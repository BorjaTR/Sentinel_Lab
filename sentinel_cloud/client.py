"""
Sentinel Cloud Client - High-level API for tokenomics testing

This module provides a simple, user-friendly interface for running
tokenomics experiments on the Sentinel hardware simulation engine.

Usage:
    from sentinel_cloud import SentinelClient

    # Initialize client
    client = SentinelClient()

    # Run single simulation
    result = client.run(
        scenario="data/solana_day_1.csv",
        fee_bps=50,
        mapper="solana"
    )
    print(f"Revenue: ${result.revenue_usdc:,}")

    # Run parameter sweep
    results = client.sweep(
        scenario="data/solana_day_1.csv",
        fee_range=(0, 200, 25),  # 0% to 2% in 0.25% steps
        mapper="solana"
    )
    results.print_summary()
"""

from typing import List, Tuple, Optional, Union
from dataclasses import dataclass
from pathlib import Path

from .experiment import (
    Config,
    RunResult,
    ExperimentResult,
    run_scenario,
    run_experiments,
    generate_fee_sweep_configs
)


@dataclass
class SimulationResult:
    """
    Simplified result object for end users.

    Wraps the internal RunResult with a cleaner interface.
    """
    config_name: str
    fee_bps: int
    revenue_usdc: float
    revenue_gpu: float
    volume_usdc: float
    volume_gpu: float
    throughput_tps: float
    lab_tps: float
    num_transactions: int
    wall_time_seconds: float
    success: bool
    error_message: Optional[str] = None

    @classmethod
    def from_run_result(cls, run_result: RunResult) -> 'SimulationResult':
        """Convert internal RunResult to user-facing SimulationResult."""
        return cls(
            config_name=run_result.config.name,
            fee_bps=run_result.config.fee_bps_asset0,
            revenue_usdc=run_result.get_metric('rev_usdc', 0),
            revenue_gpu=run_result.get_metric('rev_gpu', 0),
            volume_usdc=run_result.get_metric('vol_usdc', 0),
            volume_gpu=run_result.get_metric('vol_gpu', 0),
            throughput_tps=run_result.get_metric('engine_tps', 0),
            lab_tps=run_result.get_metric('lab_tps', 0),
            num_transactions=int(run_result.get_metric('num_tx', 0)),
            wall_time_seconds=run_result.wall_time_seconds,
            success=run_result.success,
            error_message=run_result.error_message
        )

    @property
    def metrics(self) -> dict:
        """Get all metrics as a dictionary."""
        return {
            'fee_bps': self.fee_bps,
            'revenue_usdc': self.revenue_usdc,
            'revenue_gpu': self.revenue_gpu,
            'volume_usdc': self.volume_usdc,
            'volume_gpu': self.volume_gpu,
            'engine_tps': self.throughput_tps,
            'lab_tps': self.lab_tps,
            'num_transactions': self.num_transactions,
            'wall_time_seconds': self.wall_time_seconds,
        }

    @property
    def engine_tps(self) -> float:
        """Core RTL engine throughput (theoretical max, no I/O)."""
        return self.throughput_tps

    def to_dict(self) -> dict:
        """
        Export result to stable dictionary format.

        Returns:
            Dictionary with versioned schema for JSON export
        """
        return {
            'schema_version': 1,
            'sentinel_version': '0.3.0',
            'config_name': self.config_name,
            'fee_bps': self.fee_bps,
            'success': self.success,
            'error_message': self.error_message,
            'metrics': {
                'revenue_usdc': self.revenue_usdc,
                'revenue_gpu': self.revenue_gpu,
                'volume_usdc': self.volume_usdc,
                'volume_gpu': self.volume_gpu,
                'num_transactions': self.num_transactions,
            },
            'performance': {
                'engine_tps': self.throughput_tps,
                'engine_tps_description': 'Core RTL @ 100MHz, 1 tx/cycle, no I/O/consensus',
                'lab_tps': self.lab_tps,
                'lab_tps_description': 'End-to-end including Python, Verilator, CSV I/O',
                'wall_time_seconds': self.wall_time_seconds,
            }
        }

    def __str__(self) -> str:
        """Human-readable summary."""
        if not self.success:
            return f"❌ {self.config_name}: Failed - {self.error_message}"

        return (
            f"✅ {self.config_name}\n"
            f"   Revenue:    ${self.revenue_usdc:,.0f} USDC + {self.revenue_gpu:,.0f} GPU\n"
            f"   Volume:     ${self.volume_usdc:,.0f} USDC\n"
            f"   Engine TPS: {self.throughput_tps/1e6:.2f}M tx/s (core RTL @ 100MHz, 1 tx/cycle)\n"
            f"   Lab TPS:    {self.lab_tps:,.0f} tx/s (end-to-end w/ Python + Verilator)\n"
            f"   Time:       {self.wall_time_seconds:.1f}s"
        )


class SweepResult:
    """
    Container for parameter sweep results.

    Provides comparison and analysis methods for multiple configurations.
    """
    def __init__(self, experiment_result: ExperimentResult):
        self._experiment_result = experiment_result
        self.results = [
            SimulationResult.from_run_result(run)
            for run in experiment_result.runs
        ]

    def get_successful(self) -> List[SimulationResult]:
        """Get only successful simulation results."""
        return [r for r in self.results if r.success]

    def get_optimal(self, metric: str = 'revenue_usdc') -> Optional[SimulationResult]:
        """
        Find optimal configuration by specified metric.

        Args:
            metric: Metric to optimize for (revenue_usdc, volume_usdc, lab_tps)

        Returns:
            SimulationResult with highest metric value, or None if no successful runs
        """
        successful = self.get_successful()
        if not successful:
            return None
        return max(successful, key=lambda r: getattr(r, metric))

    def get_metric_table(self, metric: str) -> List[dict]:
        """
        Get table of specific metric across all successful runs.

        Args:
            metric: Metric name (revenue_usdc, volume_usdc, lab_tps, etc.)

        Returns:
            List of dicts with config_name, fee_bps, and metric value
        """
        return [
            {
                'config_name': r.config_name,
                'fee_bps': r.fee_bps,
                metric: getattr(r, metric)
            }
            for r in self.get_successful()
        ]

    def print_summary(self):
        """Print human-readable summary table."""
        self._experiment_result.print_summary()

    def print_analysis(self):
        """
        Print opinionated fee sweep analysis with recommendations.

        Analyzes successful runs and provides actionable insights about:
        - Optimal fee configuration by revenue
        - Revenue vs volume trade-offs
        - Failure rate considerations
        - Launch recommendations
        """
        successful = self.get_successful()

        if len(successful) < 2:
            print("\nℹ️  Need at least 2 successful runs for fee sweep analysis")
            return

        print("\n" + "="*70)
        print("Fee Sweep Analysis")
        print("="*70)

        # Find optimal by revenue
        optimal = self.get_optimal('revenue_usdc')
        print(f"\n✅ Optimal Fee (by revenue): {optimal.fee_bps} bps ({optimal.fee_bps/100:.2f}%)")
        print(f"   Revenue:      ${optimal.revenue_usdc:>12,.0f} USDC")
        print(f"   Volume:       ${optimal.volume_usdc:>12,.0f} USDC")
        print(f"   Lab TPS:      {optimal.lab_tps:>12,.0f} tx/s")
        print(f"   Failure rate: {0:>12.1f}%")  # TODO: Add failure tracking

        # Revenue progression analysis
        sorted_by_fee = sorted(successful, key=lambda r: r.fee_bps)
        if len(sorted_by_fee) >= 2:
            print(f"\n📊 Revenue vs Fee:")
            for i in range(len(sorted_by_fee) - 1):
                low = sorted_by_fee[i]
                high = sorted_by_fee[i + 1]

                rev_change = high.revenue_usdc - low.revenue_usdc
                vol_change_pct = ((high.volume_usdc - low.volume_usdc) / low.volume_usdc * 100) if low.volume_usdc > 0 else 0

                print(f"   {low.fee_bps} bps → {high.fee_bps} bps:")
                print(f"   - Revenue change: ${rev_change:>12,.0f}")
                print(f"   - Volume impact:  {abs(vol_change_pct):>12.2f}% {'loss' if vol_change_pct < 0 else 'gain'}")

                # Determine if linear scaling
                expected_rev = low.revenue_usdc * (high.fee_bps / low.fee_bps) if low.fee_bps > 0 else 0
                actual_rev = high.revenue_usdc
                scaling_ratio = actual_rev / expected_rev if expected_rev > 0 else 1.0

                if 0.95 <= scaling_ratio <= 1.05:
                    print(f"   - Scaling:        Linear (revenue ∝ fee)")
                elif scaling_ratio > 1.05:
                    print(f"   - Scaling:        Super-linear (user behavior shift?)")
                else:
                    print(f"   - Scaling:        Sub-linear (volume sensitivity)")

        # Recommendation
        print(f"\n💡 Recommendation:")

        # Check if optimal is reasonable (not too aggressive)
        reasonable_threshold = 200  # 2%
        if optimal.fee_bps <= reasonable_threshold:
            print(f"   {optimal.fee_bps} bps is a strong launch candidate:")
            print(f"   - Maximizes revenue (${optimal.revenue_usdc:,.0f})")

            # Check volume impact
            if len(sorted_by_fee) >= 2:
                baseline = sorted_by_fee[0]
                vol_loss_pct = ((optimal.volume_usdc - baseline.volume_usdc) / baseline.volume_usdc * 100) if baseline.volume_usdc > 0 else 0

                if abs(vol_loss_pct) < 1.0:
                    print(f"   - Negligible volume impact ({abs(vol_loss_pct):.2f}% {'loss' if vol_loss_pct < 0 else 'change'})")
                elif abs(vol_loss_pct) < 5.0:
                    print(f"   - Acceptable volume impact ({abs(vol_loss_pct):.2f}% loss)")
                else:
                    print(f"   - ⚠️  Significant volume impact ({abs(vol_loss_pct):.2f}% loss)")

            print(f"   - Low failure rate (0.0%)")
        else:
            print(f"   {optimal.fee_bps} bps may be too aggressive for launch:")
            print(f"   - Consider testing user behavior at this fee level")
            print(f"   - Recommended starting point: 50-100 bps (0.5-1.0%)")

        # Phase 6: Treasury sustainability analysis
        optimal_run = next((r for r in self._experiment_result.runs if r.config.name == optimal.config_name), None)
        if optimal_run and optimal_run.treasury_state:
            treasury = optimal_run.treasury_state
            print(f"\n🏛️  Treasury Sustainability Check:")

            if treasury['is_sustainable']:
                print(f"   ✅ Treasury is sustainable at {optimal.fee_bps} bps")
                print(f"   - Revenue: ${treasury['revenue_rate_per_day']:,.0f}/day")
                print(f"   - Burn:    ${treasury['burn_rate_per_day']:,.0f}/day")
                print(f"   - Net:     ${treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']:+,.0f}/day")
            else:
                risk = treasury['depletion_risk']
                print(f"   {risk} Treasury depletes in {treasury.get('runway_days', 'unknown')} days")
                print(f"   - Revenue: ${treasury['revenue_rate_per_day']:,.0f}/day")
                print(f"   - Burn:    ${treasury['burn_rate_per_day']:,.0f}/day")
                print(f"   - Net:     ${treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']:+,.0f}/day")

                if '💀' in risk or '🔴' in risk:
                    print(f"   ⚠️  Action required: Increase fees, reduce emissions, or inject capital")
                elif '🟠' in risk:
                    print(f"   ⚠️  Monitor closely: Treasury trajectory is concerning")

        # Phase 6: Role economics warnings
        if optimal_run and optimal_run.role_metrics:
            warnings = []
            for role, metrics in optimal_run.role_metrics.items():
                if metrics['net_revenue'] < 0:
                    warnings.append(f"   ⚠️  {role.capitalize()}s paying more than earning (net: ${metrics['net_revenue']:,.0f})")

            if warnings:
                print(f"\n👥 Role Economics Warnings:")
                for warning in warnings:
                    print(warning)

        print("="*70 + "\n")

    def to_json(self, output_path: str):
        """Export results to JSON file with stable schema."""
        import json
        output = {
            'schema_version': 1,
            'sentinel_version': '0.3.0',
            'num_configs': len(self.results),
            'num_successful': len(self.get_successful()),
            'results': [r.to_dict() for r in self.results]
        }

        with open(output_path, 'w') as f:
            json.dump(output, f, indent=2)

    def to_dict(self) -> dict:
        """
        Export sweep results to stable dictionary format.

        Returns:
            Dictionary with versioned schema
        """
        return {
            'schema_version': 1,
            'sentinel_version': '0.3.0',
            'num_configs': len(self.results),
            'num_successful': len(self.get_successful()),
            'results': [r.to_dict() for r in self.results]
        }

    def __len__(self) -> int:
        return len(self.results)

    def __iter__(self):
        return iter(self.results)


class SentinelClient:
    """
    High-level client for Sentinel Cloud tokenomics testing.

    This is the main entry point for the SDK. It provides a simple,
    Pythonic interface for running simulations and parameter sweeps.

    Examples:
        >>> client = SentinelClient()
        >>> result = client.run("data/solana.csv", fee_bps=50)
        >>> print(f"Revenue: ${result.revenue_usdc:,}")

        >>> sweep = client.sweep("data/solana.csv", fee_range=(0, 200, 25))
        >>> optimal = sweep.get_optimal('revenue_usdc')
        >>> print(f"Optimal fee: {optimal.fee_bps} bps")
    """

    def __init__(self, verbose: bool = False):
        """
        Initialize Sentinel client.

        Args:
            verbose: Enable detailed progress output
        """
        self.verbose = verbose

    def run(
        self,
        scenario: Union[str, Path],
        fee_bps: int = 50,
        fee_bps_asset1: int = 0,
        mapper: str = "solana",
        config_name: Optional[str] = None
    ) -> SimulationResult:
        """
        Run a single simulation with specified configuration.

        Args:
            scenario: Path to transaction CSV file
            fee_bps: Fee in basis points for asset0 (default: 50 = 0.50%)
            fee_bps_asset1: Fee in basis points for asset1 (default: 0)
            mapper: Protocol mapper ('solana', 'evm', 'depin', etc.)
            config_name: Optional name for this configuration

        Returns:
            SimulationResult with metrics and analysis

        Raises:
            FileNotFoundError: If scenario file doesn't exist
            ValueError: If parameters are invalid

        Example:
            >>> client = SentinelClient()
            >>> result = client.run("data/solana.csv", fee_bps=100)
            >>> print(result)
        """
        if not Path(scenario).exists():
            raise FileNotFoundError(f"Scenario file not found: {scenario}")

        if not (0 <= fee_bps <= 10000):
            raise ValueError(f"fee_bps must be in range [0, 10000], got {fee_bps}")

        if not (0 <= fee_bps_asset1 <= 10000):
            raise ValueError(f"fee_bps_asset1 must be in range [0, 10000], got {fee_bps_asset1}")

        # Create config
        if config_name is None:
            config_name = f"{fee_bps} bps ({fee_bps/100:.2f}%)"

        config = Config(
            name=config_name,
            fee_bps_asset0=fee_bps,
            fee_bps_asset1=fee_bps_asset1
        )

        # Run simulation
        run_result = run_scenario(
            scenario_path=str(scenario),
            mapper=mapper,
            config=config,
            verbose=self.verbose
        )

        return SimulationResult.from_run_result(run_result)

    def sweep(
        self,
        scenario: Union[str, Path],
        fee_range: Optional[Tuple[int, int, int]] = None,
        fee_list: Optional[List[int]] = None,
        mapper: str = "solana"
    ) -> SweepResult:
        """
        Run parameter sweep across multiple fee configurations.

        Args:
            scenario: Path to transaction CSV file
            fee_range: Tuple of (start, end, step) in basis points
                      e.g., (0, 200, 25) = 0% to 2% in 0.25% steps
            fee_list: Explicit list of fees to test (alternative to fee_range)
            mapper: Protocol mapper ('solana', 'evm', 'depin', etc.)

        Returns:
            SweepResult with comparison table and analysis

        Raises:
            ValueError: If neither fee_range nor fee_list provided

        Example:
            >>> client = SentinelClient()
            >>> sweep = client.sweep("data/solana.csv", fee_range=(0, 200, 25))
            >>> sweep.print_summary()
            >>> sweep.print_analysis()
            >>> optimal = sweep.get_optimal('revenue_usdc')
        """
        if not Path(scenario).exists():
            raise FileNotFoundError(f"Scenario file not found: {scenario}")

        # Generate configs
        configs = []

        if fee_list is not None:
            # Explicit fee list
            for fee_bps in fee_list:
                if not (0 <= fee_bps <= 10000):
                    raise ValueError(f"Fee {fee_bps} bps is out of range [0, 10000]")
                name = f"{fee_bps} bps ({fee_bps/100:.2f}%)"
                configs.append(Config(name=name, fee_bps_asset0=fee_bps))

        elif fee_range is not None:
            # Fee range sweep
            start, end, step = fee_range
            if not (0 <= start <= 10000 and 0 <= end <= 10000):
                raise ValueError("Fee range must be within [0, 10000] bps")
            if start > end:
                raise ValueError("Fee range start must be <= end")

            configs = generate_fee_sweep_configs(
                start_bps=start,
                end_bps=end,
                step_bps=step,
                asset=0
            )

        else:
            # Default: 4-point comparison
            configs = [
                Config("No Fee (0.00%)", fee_bps_asset0=0),
                Config("Low (0.25%)", fee_bps_asset0=25),
                Config("Standard (0.50%)", fee_bps_asset0=50),
                Config("High (1.00%)", fee_bps_asset0=100),
            ]

        # Run experiments
        experiment_result = run_experiments(
            scenario_path=str(scenario),
            mapper=mapper,
            configs=configs,
            verbose=self.verbose
        )

        return SweepResult(experiment_result)

    def compare(
        self,
        scenario: Union[str, Path],
        configs: List[Tuple[str, int]],
        mapper: str = "solana"
    ) -> SweepResult:
        """
        Compare specific named configurations.

        Args:
            scenario: Path to transaction CSV file
            configs: List of (name, fee_bps) tuples
            mapper: Protocol mapper

        Returns:
            SweepResult with comparison table

        Example:
            >>> client = SentinelClient()
            >>> result = client.compare(
            ...     "data/solana.csv",
            ...     configs=[
            ...         ("Conservative", 25),
            ...         ("Aggressive", 150),
            ...         ("Experimental", 500)
            ...     ]
            ... )
            >>> result.print_summary()
        """
        config_objects = [
            Config(name=name, fee_bps_asset0=fee_bps)
            for name, fee_bps in configs
        ]

        experiment_result = run_experiments(
            scenario_path=str(scenario),
            mapper=mapper,
            configs=config_objects,
            verbose=self.verbose
        )

        return SweepResult(experiment_result)

    def compute_baseline(
        self,
        scenario: Union[str, Path],
        mapper: str = "solana"
    ) -> 'BaselineMetrics':
        """
        Compute baseline metrics from actual transaction data (no simulation).

        This analyzes real mainnet transactions to establish ground truth
        for before/after comparisons.

        Args:
            scenario: Path to transaction CSV file
            mapper: Protocol mapper ('solana', 'evm', 'depin', etc.)

        Returns:
            BaselineMetrics with actual transaction statistics

        Example:
            >>> client = SentinelClient()
            >>> baseline = client.compute_baseline("data/solana.csv")
            >>> print(f"Actual volume: ${baseline.total_volume_asset0:,.0f}")
            >>> print(f"Actual fee rate: {baseline.avg_fee_rate_asset0:.2f} bps")
        """
        from .io import load_and_normalize
        from .baseline import BaselineAnalyzer

        # Load and normalize transactions
        if not Path(scenario).exists():
            raise FileNotFoundError(f"Scenario file not found: {scenario}")

        txs = load_and_normalize(
            csv_path=str(scenario),
            mapper=mapper,
            num_users=1024,
            validate=True
        )

        # Compute baseline
        analyzer = BaselineAnalyzer()
        return analyzer.compute(txs)

    def compare_baseline_vs_config(
        self,
        baseline: 'BaselineMetrics',
        optimized_run: RunResult,
        config_label: str = "",
        treasury_balance: Optional[float] = None
    ) -> 'ComparisonResult':
        """
        Compare baseline vs a specific optimized configuration.

        This quantifies the improvement: "You're leaving $X/day on the table."

        Args:
            baseline: Baseline metrics from actual mainnet data
            optimized_run: Simulation result from optimized config
            config_label: Human-readable config label (e.g., "50 bps")
            treasury_balance: Current treasury balance for runway projection (optional)

        Returns:
            ComparisonResult with before/after metrics and optional runway projection

        Example:
            >>> client = SentinelClient()
            >>> baseline = client.compute_baseline("data/solana.csv")
            >>> sweep = client.sweep("data/solana.csv", fee_range=(0, 200, 25))
            >>> best = sweep.get_optimal('revenue_usdc')
            >>> # Get the RunResult from the experiment
            >>> best_run = sweep._experiment_result.runs[0]
            >>> comparison = client.compare_baseline_vs_config(
            ...     baseline, best_run, "50 bps", treasury_balance=100000
            ... )
            >>> print(comparison.summary())
        """
        from .comparison import ComparisonEngine

        engine = ComparisonEngine()
        return engine.compare(baseline, optimized_run, config_label, treasury_balance)

    def optimize_and_compare(
        self,
        scenario: Union[str, Path],
        mapper: str = "solana",
        fee_range: Optional[Tuple[int, int, int]] = None,
        fee_list: Optional[List[int]] = None,
        treasury_balance: Optional[float] = None
    ) -> 'ComparisonResult':
        """
        Complete optimization pipeline: baseline → sweep → compare.

        This is the high-level "show me the money" workflow.

        Args:
            scenario: Path to transaction CSV
            mapper: Protocol mapper
            fee_range: Fee sweep range (start, stop, step) in bps
            fee_list: Or explicit list of fees to test
            treasury_balance: Current treasury balance for runway projection (optional)

        Returns:
            ComparisonResult comparing baseline vs best optimized config

        Example:
            >>> client = SentinelClient()
            >>> comparison = client.optimize_and_compare(
            ...     "data/solana.csv",
            ...     fee_range=(0, 200, 25),
            ...     treasury_balance=100000
            ... )
            >>> print(comparison.summary())
            With 50 bps: +$1,234/day (+45.2%) | +147 days runway
        """
        from .comparison import ComparisonEngine

        if self.verbose:
            print("Step 1/3: Computing baseline from actual data...")

        # Step 1: Compute baseline
        baseline = self.compute_baseline(scenario, mapper)

        if self.verbose:
            print(f"  Baseline: {baseline.tx_count:,} txs, "
                  f"${baseline.total_volume_asset0:,.0f} volume")
            print("\nStep 2/3: Running fee sweep...")

        # Step 2: Run sweep
        sweep_result = self.sweep(scenario, fee_range=fee_range, fee_list=fee_list, mapper=mapper)

        if self.verbose:
            print(f"  Tested {len(sweep_result.results)} configurations")
            print("\nStep 3/3: Finding best improvement...")

        # Step 3: Find best improvement
        engine = ComparisonEngine()
        comparison = engine.find_best_improvement(
            baseline,
            sweep_result._experiment_result.runs,
            treasury_balance
        )

        if self.verbose:
            print(f"\n✅ {comparison.summary()}")

        return comparison

    def compute_runway(
        self,
        baseline: 'BaselineMetrics',
        treasury_balance: float,
        optimized_metrics: Optional[dict] = None
    ) -> 'RunwayResult':
        """
        Compute treasury runway projection from baseline metrics.

        This answers: "When do we run out of money?"

        Args:
            baseline: Baseline metrics with daily_net_treasury_change
            treasury_balance: Current treasury balance in asset0
            optimized_metrics: Optional metrics dict from optimized config

        Returns:
            RunwayResult with baseline and optional optimized runway projections

        Example:
            >>> client = SentinelClient()
            >>> baseline = client.compute_baseline("data/solana.csv")
            >>> runway = client.compute_runway(baseline, treasury_balance=100000)
            >>> if runway.baseline_runway_days:
            ...     print(f"Treasury depletes in {runway.baseline_runway_days:.0f} days")
            ...     print(f"Death date: {runway.baseline_death_date}")
            ... else:
            ...     print("Treasury is sustainable!")
        """
        from .death_clock import RunwayProjector

        projector = RunwayProjector()
        return projector.compute_from_baseline(
            baseline_metrics=baseline,
            optimized_metrics=optimized_metrics,
            treasury_balance=treasury_balance
        )

    def scan_safety(
        self,
        scenario: Union[str, Path],
        mapper: str = "solana",
        param_name: str = "fee_bps_asset0",
        values: Optional[List[float]] = None,
        treasury_balance: Optional[float] = None
    ) -> List['SafetyAssessment']:
        """
        Scan parameter values and classify as GREEN/YELLOW/RED.

        This answers: "Can we touch this parameter without dying?"

        Args:
            scenario: Path to transaction CSV
            mapper: Protocol mapper
            param_name: Parameter to scan (default: "fee_bps_asset0")
            values: List of values to test (default: [0, 25, 50, 75, 100])
            treasury_balance: Current treasury balance for runway projection

        Returns:
            List of SafetyAssessment, one per value tested

        Example:
            >>> client = SentinelClient()
            >>> results = client.scan_safety(
            ...     "data/solana.csv",
            ...     values=[0, 25, 50, 75, 100],
            ...     treasury_balance=100000
            ... )
            >>> safe = [r for r in results if r.overall_status == "green"]
            >>> print(f"Safe configs: {len(safe)}/{len(results)}")
        """
        from .safety import SafetyScanner

        if values is None:
            values = [0, 25, 50, 75, 100]

        scanner = SafetyScanner()
        return scanner.scan_param(
            scenario=str(scenario),
            mapper=mapper,
            param_name=param_name,
            values=values,
            treasury_balance=treasury_balance,
            verbose=self.verbose
        )

    def compute_unit_economics(
        self,
        scenario: Union[str, Path],
        mapper: str = "solana",
        config: Optional['Config'] = None,
        resource_name: str = "gpu_hour",
        resource_amount_field: str = "asset1_amount",
        emissions_usd_per_day: Optional[float] = None
    ) -> 'UnitEconomicsResult':
        """
        Compute unit economics (cost and margin per resource unit).

        This answers: "Are we a business or a subsidy?"

        Args:
            scenario: Path to transaction CSV
            mapper: Protocol mapper
            config: Config to simulate with (default: baseline, no fees)
            resource_name: Human-readable resource type (e.g., "gpu_hour", "gb_month")
            resource_amount_field: SentinelTx field for resource units (default: "asset1_amount")
            emissions_usd_per_day: Total emissions cost per day (optional)

        Returns:
            UnitEconomicsResult with revenue, emissions, and margin per unit

        Example:
            >>> client = SentinelClient()
            >>> result = client.compute_unit_economics(
            ...     "data/solana.csv",
            ...     resource_name="gpu_hour",
            ...     emissions_usd_per_day=5000
            ... )
            >>> print(f"Revenue: ${result.revenue_per_unit:.2f}/GPU-hour")
            >>> print(f"Margin: ${result.net_margin_per_unit:.2f}/GPU-hour")
        """
        from .io import load_and_normalize
        from .baseline import BaselineAnalyzer
        from .unit_economics import UnitEconomicsConfig, compute_unit_economics
        from .experiment import run_scenario, Config

        # Load transactions
        txs = load_and_normalize(
            csv_path=str(scenario),
            mapper=mapper,
            num_users=1024,
            validate=True
        )

        # Compute baseline
        analyzer = BaselineAnalyzer()
        baseline = analyzer.compute(txs)

        # Run simulation with config (or baseline config)
        if config is None:
            config = Config(name="baseline", fee_bps_asset0=0)

        run_result = run_scenario(
            scenario_path=str(scenario),
            mapper=mapper,
            config=config,
            verbose=False,
            transactions=txs
        )

        # Create unit economics config
        unit_econ_cfg = UnitEconomicsConfig(
            resource_name=resource_name,
            resource_amount_field=resource_amount_field
        )

        # Compute unit economics
        return compute_unit_economics(
            txs=txs,
            run=run_result,
            baseline=baseline,
            cfg=unit_econ_cfg,
            emissions_usd_per_day=emissions_usd_per_day
        )

