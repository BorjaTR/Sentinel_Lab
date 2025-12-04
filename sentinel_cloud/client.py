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

    def __str__(self) -> str:
        """Human-readable summary."""
        if not self.success:
            return f"❌ {self.config_name}: Failed - {self.error_message}"

        return (
            f"✅ {self.config_name}\n"
            f"   Revenue: ${self.revenue_usdc:,.0f} USDC + {self.revenue_gpu:,.0f} GPU\n"
            f"   Volume:  ${self.volume_usdc:,.0f} USDC\n"
            f"   TPS:     {self.lab_tps:,.0f} tx/s (lab), {self.throughput_tps/1e6:.2f}M (engine)\n"
            f"   Time:    {self.wall_time_seconds:.1f}s"
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

    def print_summary(self):
        """Print human-readable summary table."""
        self._experiment_result.print_summary()

    def print_analysis(self):
        """Print fee sweep analysis with recommendations."""
        if len(self.get_successful()) >= 2:
            self._experiment_result.summarize_fee_sweep()
        else:
            print("ℹ️  Need at least 2 successful runs for fee sweep analysis")

    def to_json(self, output_path: str):
        """Export results to JSON file."""
        self._experiment_result.to_json(output_path)

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
