"""
Before/After Comparison - Compare baseline vs optimized configurations.

This module provides tools to compare actual mainnet performance (baseline)
against simulated optimized configurations to quantify improvements.

This is where the "money left on table" message comes from.
"""

from dataclasses import dataclass
from typing import Optional
from .baseline import BaselineMetrics
from .experiment import RunResult


@dataclass
class ComparisonResult:
    """
    Results of comparing baseline vs optimized configuration.

    This is the "show me the money" object - quantifies exactly how much
    better an optimized config performs vs what actually happened.
    """

    baseline: BaselineMetrics
    optimized: RunResult

    # Revenue comparison - The headline number
    baseline_revenue_asset0: float
    optimized_revenue_asset0: float
    additional_revenue_asset0: float
    pct_improvement_revenue: float

    # Failure rate comparison (if available)
    baseline_failure_rate: Optional[float] = None
    optimized_failure_rate: Optional[float] = None
    failure_delta: Optional[float] = None

    # Runway comparison (filled by Phase C - Death Clock)
    baseline_runway_days: Optional[float] = None
    optimized_runway_days: Optional[float] = None
    runway_extension_days: Optional[float] = None

    # Config details
    optimized_config_label: str = ""

    def summary(self) -> str:
        """
        Generate one-line executive summary.

        Returns:
            Human-readable summary of improvement
        """
        return (
            f"With {self.optimized_config_label}: "
            f"+${self.additional_revenue_asset0:,.0f}/day "
            f"({self.pct_improvement_revenue:+.1f}%)"
        )


class ComparisonEngine:
    """Compare baseline vs optimized configurations."""

    def compare(
        self,
        baseline: BaselineMetrics,
        optimized: RunResult,
        config_label: str = ""
    ) -> ComparisonResult:
        """
        Compare baseline metrics vs optimized simulation result.

        This is the core "before/after" logic that quantifies improvement.

        Args:
            baseline: Actual mainnet metrics (what really happened)
            optimized: Simulation result from optimized config
            config_label: Human-readable config description (e.g., "50 bps")

        Returns:
            ComparisonResult with improvement metrics

        Example:
            >>> engine = ComparisonEngine()
            >>> result = engine.compare(baseline, best_run, "50 bps")
            >>> print(result.summary())
            With 50 bps: +$1,234/day (+45.2%)
        """
        # Extract baseline revenue
        # Use fees if available, else try to estimate from volume/treasury change
        baseline_revenue = baseline.total_fees_asset0 or 0.0

        # If no fees detected, try to estimate from daily treasury change
        if baseline_revenue == 0.0 and baseline.daily_net_treasury_change:
            # If treasury is growing, use that as proxy revenue
            if baseline.daily_net_treasury_change > 0:
                # Scale to total period
                if baseline.duration_seconds:
                    days = baseline.duration_seconds / 86400.0
                    baseline_revenue = baseline.daily_net_treasury_change * days

        # Extract optimized revenue from RunResult
        # RunResult.metrics should contain 'rev_usdc' or similar
        optimized_revenue = optimized.metrics.get('rev_usdc', 0.0)

        # If not found, try alternative metric names
        if optimized_revenue == 0.0:
            optimized_revenue = optimized.metrics.get('revenue_usdc', 0.0)
        if optimized_revenue == 0.0:
            optimized_revenue = optimized.metrics.get('protocol_revenue', 0.0)

        # Compute improvement
        additional_revenue = optimized_revenue - baseline_revenue
        pct_improvement = (
            (additional_revenue / baseline_revenue * 100.0)
            if baseline_revenue > 0
            else 0.0
        )

        # Failure rate comparison (if available)
        baseline_failure_rate = baseline.failure_rate
        optimized_failure_rate = optimized.metrics.get('failure_rate')

        failure_delta = None
        if baseline_failure_rate is not None and optimized_failure_rate is not None:
            failure_delta = optimized_failure_rate - baseline_failure_rate

        return ComparisonResult(
            baseline=baseline,
            optimized=optimized,
            baseline_revenue_asset0=baseline_revenue,
            optimized_revenue_asset0=optimized_revenue,
            additional_revenue_asset0=additional_revenue,
            pct_improvement_revenue=pct_improvement,
            baseline_failure_rate=baseline_failure_rate,
            optimized_failure_rate=optimized_failure_rate,
            failure_delta=failure_delta,
            optimized_config_label=config_label,
        )

    def find_best_improvement(
        self,
        baseline: BaselineMetrics,
        runs: list[RunResult]
    ) -> ComparisonResult:
        """
        Find the configuration with the best improvement over baseline.

        Args:
            baseline: Baseline metrics
            runs: List of simulation results to compare

        Returns:
            ComparisonResult for the best configuration

        Example:
            >>> engine = ComparisonEngine()
            >>> best = engine.find_best_improvement(baseline, experiment.runs)
            >>> print(f"Best config: {best.optimized_config_label}")
        """
        if not runs:
            raise ValueError("No simulation results to compare")

        # Find run with highest revenue
        best_run = max(runs, key=lambda r: r.metrics.get('rev_usdc', 0.0))

        # Generate label from config
        config_label = best_run.config.name or f"{best_run.config.fee_bps_asset0} bps"

        return self.compare(baseline, best_run, config_label)
