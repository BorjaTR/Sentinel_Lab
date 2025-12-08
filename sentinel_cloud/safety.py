"""
Parameter Safety Scanner - Classify configs as GREEN/YELLOW/RED.

This module provides tools to assess whether parameter changes are safe
for protocol sustainability. Answers: "Can we touch this without dying?"

Pain point it solves:
    "Every parameter change is a governance war and we're basically guessing."

Usage:
    from sentinel_cloud.safety import SafetyScanner, SafetyRule

    scanner = SafetyScanner()
    results = scanner.scan_param(
        scenario="data/solana.csv",
        mapper="solana",
        param_name="fee_bps_asset0",
        values=[0, 25, 50, 75, 100],
        treasury_balance=100000
    )

    for assessment in results:
        print(f"{assessment.param_value} bps: {assessment.overall_status}")
        if assessment.overall_status == "red":
            print(f"  Failing rules: {assessment.failing_rules}")
"""

from dataclasses import dataclass, field
from typing import List, Dict, Callable, Optional, Any
from pathlib import Path

from .experiment import Config, RunResult, run_scenario
from .baseline import BaselineMetrics, BaselineAnalyzer
from .death_clock import RunwayResult, RunwayProjector
from .io import load_and_normalize


@dataclass
class SafetyRule:
    """
    A single safety check for protocol configurations.

    Attributes:
        name: Short rule name (e.g., "runway_180d")
        description: Human-readable explanation
        check: Function that takes (RunResult, RunwayResult) and returns True if passes
        severity: "info" | "warning" | "critical"

    Example:
        >>> rule = SafetyRule(
        ...     name="runway_180d",
        ...     description="Treasury runway must be > 180 days",
        ...     check=lambda run, runway: runway.baseline_runway_days is None or runway.baseline_runway_days > 180,
        ...     severity="critical"
        ... )
    """
    name: str
    description: str
    check: Callable[[RunResult, Optional[RunwayResult], Optional[BaselineMetrics]], bool]
    severity: str  # "info" | "warning" | "critical"

    def __post_init__(self):
        """Validate severity."""
        if self.severity not in ("info", "warning", "critical"):
            raise ValueError(f"severity must be info/warning/critical, got {self.severity}")


@dataclass
class SafetyAssessment:
    """
    Safety assessment for a single parameter value.

    Attributes:
        param_name: Parameter being tested (e.g., "fee_bps_asset0")
        param_value: Value being tested (e.g., 50)
        revenue: Revenue generated at this param value
        runway_days: Treasury runway in days (None = sustainable)
        passes: Dict mapping rule_name -> bool (True = passed)
        overall_status: "green" | "yellow" | "red"
        failing_rules: List of rules that failed
        run_result: Full RunResult for detailed analysis
    """
    param_name: str
    param_value: float
    revenue: float
    runway_days: Optional[float]
    passes: Dict[str, bool]
    overall_status: str  # "green" | "yellow" | "red"
    failing_rules: List[str] = field(default_factory=list)
    run_result: Optional[RunResult] = None

    def summary(self) -> str:
        """One-line summary of assessment."""
        status_emoji = {
            "green": "🟢",
            "yellow": "🟡",
            "red": "🔴"
        }
        emoji = status_emoji.get(self.overall_status, "⚪")

        runway_str = f"{self.runway_days:.0f} days" if self.runway_days else "∞"

        msg = f"{emoji} {self.param_name}={self.param_value}: ${self.revenue:,.0f}/day, runway={runway_str}"

        if self.failing_rules:
            msg += f" | ⚠️ Fails: {', '.join(self.failing_rules)}"

        return msg


class SafetyScanner:
    """
    Scan parameter ranges to classify configs as GREEN/YELLOW/RED.

    This scanner evaluates protocol configurations against safety rules
    to determine which parameter values are safe to deploy.

    Example:
        >>> scanner = SafetyScanner()
        >>> results = scanner.scan_param(
        ...     scenario="data/solana.csv",
        ...     mapper="solana",
        ...     param_name="fee_bps_asset0",
        ...     values=[0, 25, 50, 75, 100],
        ...     treasury_balance=100000
        ... )
        >>> safe_values = [r.param_value for r in results if r.overall_status == "green"]
        >>> print(f"Safe range: {min(safe_values)}-{max(safe_values)} bps")
    """

    def __init__(self, rules: Optional[List[SafetyRule]] = None):
        """
        Initialize scanner with safety rules.

        Args:
            rules: List of SafetyRule objects (uses defaults if None)
        """
        self.rules = rules or self._default_rules()

    @staticmethod
    def _default_rules() -> List[SafetyRule]:
        """
        Default safety rules for DePIN protocols.

        Returns:
            List of standard safety rules:
            - Runway > 180 days (critical)
            - Failure rate < 1% (warning)
            - No role with negative net revenue (warning)
            - Revenue > 0 (info)
        """
        rules = []

        # Rule 1: Runway safety (critical)
        def check_runway(run: RunResult, runway: Optional[RunwayResult], baseline: Optional[BaselineMetrics]) -> bool:
            if runway is None:
                return True  # No runway info available, skip check
            # None means sustainable (infinite runway) = good
            # Otherwise must be > 180 days
            return runway.optimized_runway_days is None or runway.optimized_runway_days > 180

        rules.append(SafetyRule(
            name="runway_180d",
            description="Treasury runway must be > 180 days (or sustainable)",
            check=check_runway,
            severity="critical"
        ))

        # Rule 2: Failure rate (warning)
        def check_failure_rate(run: RunResult, runway: Optional[RunwayResult], baseline: Optional[BaselineMetrics]) -> bool:
            failure_rate = run.metrics.get('failure_rate', 0.0)
            return failure_rate < 0.01  # < 1%

        rules.append(SafetyRule(
            name="failure_rate_1pct",
            description="Transaction failure rate must be < 1%",
            check=check_failure_rate,
            severity="warning"
        ))

        # Rule 3: Role economics (warning) - if role_metrics available
        def check_role_economics(run: RunResult, runway: Optional[RunwayResult], baseline: Optional[BaselineMetrics]) -> bool:
            if not run.role_metrics:
                return True  # No role metrics, skip check

            # Check that no role has negative net revenue
            for role, metrics in run.role_metrics.items():
                if metrics.get('net_revenue', 0) < 0:
                    return False
            return True

        rules.append(SafetyRule(
            name="no_negative_role_revenue",
            description="No role should have negative net revenue",
            check=check_role_economics,
            severity="warning"
        ))

        # Rule 4: Revenue generation (info)
        def check_revenue(run: RunResult, runway: Optional[RunwayResult], baseline: Optional[BaselineMetrics]) -> bool:
            revenue = run.metrics.get('rev_usdc', 0.0)
            return revenue > 0

        rules.append(SafetyRule(
            name="positive_revenue",
            description="Configuration must generate positive revenue",
            check=check_revenue,
            severity="info"
        ))

        return rules

    def assess_config(
        self,
        run_result: RunResult,
        runway_result: Optional[RunwayResult] = None,
        baseline: Optional[BaselineMetrics] = None
    ) -> SafetyAssessment:
        """
        Assess a single configuration against all safety rules.

        Args:
            run_result: Simulation result to assess
            runway_result: Optional runway projection
            baseline: Optional baseline metrics for context

        Returns:
            SafetyAssessment with pass/fail for each rule and overall status
        """
        # Extract key metrics
        revenue = run_result.metrics.get('rev_usdc', 0.0)
        runway_days = None
        if runway_result:
            runway_days = runway_result.optimized_runway_days

        # Run all checks
        passes = {}
        critical_failures = []
        warning_failures = []

        for rule in self.rules:
            try:
                passed = rule.check(run_result, runway_result, baseline)
                passes[rule.name] = passed

                if not passed:
                    if rule.severity == "critical":
                        critical_failures.append(rule.name)
                    elif rule.severity == "warning":
                        warning_failures.append(rule.name)
            except Exception as e:
                # If check fails, mark as failed
                passes[rule.name] = False
                warning_failures.append(rule.name)

        # Determine overall status
        if critical_failures:
            overall_status = "red"
            failing_rules = critical_failures + warning_failures
        elif warning_failures:
            overall_status = "yellow"
            failing_rules = warning_failures
        else:
            overall_status = "green"
            failing_rules = []

        return SafetyAssessment(
            param_name=run_result.config.name,
            param_value=run_result.config.fee_bps_asset0,
            revenue=revenue,
            runway_days=runway_days,
            passes=passes,
            overall_status=overall_status,
            failing_rules=failing_rules,
            run_result=run_result
        )

    def scan_param(
        self,
        scenario: str,
        mapper: str,
        param_name: str,
        values: List[float],
        treasury_balance: Optional[float] = None,
        baseline: Optional[BaselineMetrics] = None,
        verbose: bool = False
    ) -> List[SafetyAssessment]:
        """
        Scan parameter across multiple values and assess safety.

        Args:
            scenario: Path to transaction CSV
            mapper: Protocol mapper ('solana', 'evm', etc.)
            param_name: Parameter to scan (currently only 'fee_bps_asset0' supported)
            values: List of parameter values to test
            treasury_balance: Current treasury balance for runway projection
            baseline: Optional baseline metrics (computed if not provided)
            verbose: Print progress

        Returns:
            List of SafetyAssessment, one per value

        Example:
            >>> scanner = SafetyScanner()
            >>> results = scanner.scan_param(
            ...     "data/solana.csv",
            ...     "solana",
            ...     "fee_bps_asset0",
            ...     [0, 25, 50, 75, 100],
            ...     treasury_balance=100000
            ... )
            >>> safe = [r for r in results if r.overall_status == "green"]
        """
        if param_name != "fee_bps_asset0":
            raise ValueError(f"Only 'fee_bps_asset0' is supported for param_name, got {param_name}")

        # Compute baseline if not provided
        if baseline is None and treasury_balance is not None:
            if verbose:
                print("Computing baseline metrics...")
            txs = load_and_normalize(scenario, mapper=mapper, num_users=1024)
            analyzer = BaselineAnalyzer()
            baseline = analyzer.compute(txs)

        # Load transactions once for all runs
        if verbose:
            print(f"Loading and normalizing {scenario}...")
        txs = load_and_normalize(scenario, mapper=mapper, num_users=1024)

        # Run simulations for each value
        assessments = []
        for i, value in enumerate(values):
            if verbose:
                print(f"[{i+1}/{len(values)}] Testing {param_name}={value}...")

            # Create config
            config = Config(
                name=f"{value} bps",
                fee_bps_asset0=int(value)
            )

            # Run simulation
            run_result = run_scenario(
                scenario_path=scenario,
                mapper=mapper,
                config=config,
                verbose=False,
                transactions=txs  # Reuse loaded transactions
            )

            # Compute runway if treasury provided
            runway_result = None
            if treasury_balance is not None and baseline is not None:
                # Get optimized daily change from run metrics
                optimized_daily_change = run_result.metrics.get('daily_net_treasury_change')

                if optimized_daily_change is not None:
                    from .death_clock import RunwayInputs
                    projector = RunwayProjector()

                    inputs = RunwayInputs(
                        treasury_start_asset0=treasury_balance,
                        daily_net_change_asset0=baseline.daily_net_treasury_change or 0.0,
                        daily_net_change_asset0_optimized=optimized_daily_change
                    )
                    runway_result = projector.compute_runway(inputs)

            # Assess safety
            assessment = self.assess_config(run_result, runway_result, baseline)
            assessments.append(assessment)

            if verbose:
                print(f"  {assessment.summary()}")

        return assessments

    def get_safe_range(
        self,
        assessments: List[SafetyAssessment],
        status: str = "green"
    ) -> Optional[tuple[float, float]]:
        """
        Find the safe parameter range from assessment results.

        Args:
            assessments: List of SafetyAssessment results
            status: Status to filter by ("green", "yellow", or "red")

        Returns:
            (min_value, max_value) tuple, or None if no configs match status

        Example:
            >>> scanner = SafetyScanner()
            >>> results = scanner.scan_param(...)
            >>> safe_range = scanner.get_safe_range(results, "green")
            >>> if safe_range:
            ...     print(f"Safe range: {safe_range[0]}-{safe_range[1]} bps")
        """
        matching = [a for a in assessments if a.overall_status == status]
        if not matching:
            return None

        values = [a.param_value for a in matching]
        return (min(values), max(values))

    def summarize(self, assessments: List[SafetyAssessment]) -> str:
        """
        Generate human-readable summary of scan results.

        Args:
            assessments: List of SafetyAssessment results

        Returns:
            Multi-line summary string with safe ranges and warnings
        """
        lines = []
        lines.append("=" * 70)
        lines.append("SAFETY SCAN RESULTS")
        lines.append("=" * 70)

        # Count by status
        green = [a for a in assessments if a.overall_status == "green"]
        yellow = [a for a in assessments if a.overall_status == "yellow"]
        red = [a for a in assessments if a.overall_status == "red"]

        lines.append(f"Tested {len(assessments)} configurations:")
        lines.append(f"  🟢 Safe (Green):   {len(green)}")
        lines.append(f"  🟡 Risky (Yellow): {len(yellow)}")
        lines.append(f"  🔴 Dangerous (Red): {len(red)}")
        lines.append("")

        # Safe range
        safe_range = self.get_safe_range(assessments, "green")
        if safe_range:
            lines.append(f"🟢 SAFE RANGE: {safe_range[0]:.0f} - {safe_range[1]:.0f} bps")
        else:
            lines.append("🔴 WARNING: No configurations are fully safe!")

        # Yellow range
        yellow_range = self.get_safe_range(assessments, "yellow")
        if yellow_range:
            lines.append(f"🟡 RISKY RANGE: {yellow_range[0]:.0f} - {yellow_range[1]:.0f} bps (use with caution)")

        # Red range
        red_range = self.get_safe_range(assessments, "red")
        if red_range:
            lines.append(f"🔴 DANGEROUS RANGE: {red_range[0]:.0f} - {red_range[1]:.0f} bps (avoid)")

        lines.append("")

        # Detail each config
        lines.append("DETAILED RESULTS:")
        for assessment in assessments:
            lines.append(f"  {assessment.summary()}")

        lines.append("=" * 70)

        return "\n".join(lines)
