"""
Experiment Engine - Parameter Sweep & Multi-Config Comparison

This module provides tools for running the same transaction scenario
with multiple configurations and comparing results.

Use cases:
- Fee optimization: "What fee maximizes revenue without killing volume?"
- Sensitivity analysis: "How does 0.1% vs 1.0% fee affect failure rates?"
- A/B testing: "Compare Protocol A fees vs Protocol B fees"

Example:
    from sentinel_cloud.experiment import run_experiments, Config

    configs = [
        Config(name="No Fee", fee_bps_asset0=0),
        Config(name="Low Fee", fee_bps_asset0=25),
        Config(name="Standard", fee_bps_asset0=50),
        Config(name="High Fee", fee_bps_asset0=100),
    ]

    result = run_experiments(
        scenario_path='data/solana_day_1.csv',
        mapper='solana',
        configs=configs
    )

    # Compare metrics across configs
    print(result.get_metric_table('revenue'))
    result.plot_revenue_vs_fee()
"""

import os
import subprocess
import time
import csv
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any
from pathlib import Path
import json


@dataclass
class Config:
    """
    Configuration for a single simulation run.

    Attributes:
        name: Human-readable config name (e.g., "No Fee", "Standard")
        fee_bps_asset0: Fee for asset0 (USDC) in basis points (0-10000)
        fee_bps_asset1: Fee for asset1 (GPU credits) in basis points (0-10000)

    Future extensions:
        - emissions_rate: Protocol emission rate
        - slashing_penalty: Validator slashing percentage
        - liquidity_params: LP pool parameters
    """
    name: str
    fee_bps_asset0: int = 50
    fee_bps_asset1: int = 0

    def __post_init__(self):
        """Validate config parameters."""
        if not (0 <= self.fee_bps_asset0 <= 10000):
            raise ValueError(f"fee_bps_asset0 must be in [0, 10000], got {self.fee_bps_asset0}")
        if not (0 <= self.fee_bps_asset1 <= 10000):
            raise ValueError(f"fee_bps_asset1 must be in [0, 10000], got {self.fee_bps_asset1}")

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON export."""
        return {
            'name': self.name,
            'fee_bps_asset0': self.fee_bps_asset0,
            'fee_bps_asset1': self.fee_bps_asset1
        }


@dataclass
class RunResult:
    """
    Result from a single simulation run.

    Contains all metrics extracted from the simulation, including:
    - Performance: TPS, latency, wall clock time
    - Economics: Revenue, volume, fees collected
    - Health: Failure rate, conservation violations

    Attributes:
        config: Configuration used for this run
        metrics: Dictionary of metric_name → value
        wall_time_seconds: Simulation wall clock time
        success: Whether simulation completed successfully
        error_message: Error message if simulation failed
    """
    config: Config
    metrics: Dict[str, float] = field(default_factory=dict)
    wall_time_seconds: float = 0.0
    success: bool = True
    error_message: str = ""

    def get_metric(self, name: str, default: float = 0.0) -> float:
        """
        Get metric value by name.

        Args:
            name: Metric name (e.g., 'revenue', 'tps_million', 'vol_usdc')
            default: Default value if metric not found

        Returns:
            float: Metric value
        """
        return self.metrics.get(name, default)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON export."""
        return {
            'config': self.config.to_dict(),
            'metrics': self.metrics,
            'wall_time_seconds': self.wall_time_seconds,
            'success': self.success,
            'error_message': self.error_message
        }


@dataclass
class ExperimentResult:
    """
    Result from a multi-config experiment.

    Aggregates results from multiple simulation runs with different configs.
    Provides comparison and visualization utilities.

    Attributes:
        runs: List of individual run results
        scenario_path: Path to transaction scenario CSV
        mapper: Protocol mapper used
        total_wall_time: Total wall clock time for all runs
    """
    runs: List[RunResult]
    scenario_path: str
    mapper: str
    total_wall_time: float = 0.0

    def get_metric_table(self, metric_name: str) -> List[Dict[str, Any]]:
        """
        Get table of metric values across all configs.

        Args:
            metric_name: Metric to extract (e.g., 'revenue', 'vol_usdc')

        Returns:
            List of dicts with 'config_name', 'fee_bps', 'metric_value'
        """
        table = []
        for run in self.runs:
            if run.success:
                table.append({
                    'config_name': run.config.name,
                    'fee_bps_asset0': run.config.fee_bps_asset0,
                    'fee_bps_asset1': run.config.fee_bps_asset1,
                    metric_name: run.get_metric(metric_name)
                })
        return table

    def get_successful_runs(self) -> List[RunResult]:
        """Get only successful runs (filter out failures)."""
        return [run for run in self.runs if run.success]

    def summary_table(self) -> List[Dict[str, Any]]:
        """
        Get summary table with key metrics for all configs.

        Returns:
            List of dicts with config name and key metrics
        """
        summary = []
        for run in self.runs:
            if run.success:
                summary.append({
                    'config': run.config.name,
                    'fee_asset0': f"{run.config.fee_bps_asset0} bps",
                    'revenue_usdc': int(run.get_metric('rev_usdc', 0)),
                    'volume_usdc': int(run.get_metric('vol_usdc', 0)),
                    'tps': f"{run.get_metric('tps_million', 0):.2f}M",
                    'wall_time': f"{run.wall_time_seconds:.1f}s"
                })
            else:
                summary.append({
                    'config': run.config.name,
                    'error': run.error_message
                })
        return summary

    def to_json(self, output_path: str):
        """
        Export experiment results to JSON file.

        Args:
            output_path: Path to output JSON file
        """
        data = {
            'scenario_path': self.scenario_path,
            'mapper': self.mapper,
            'total_wall_time': self.total_wall_time,
            'runs': [run.to_dict() for run in self.runs]
        }
        with open(output_path, 'w') as f:
            json.dump(data, f, indent=2)

    def print_summary(self):
        """Print human-readable summary to console."""
        print(f"\n{'='*70}")
        print(f"Experiment Summary: {len(self.runs)} configurations")
        print(f"Scenario: {self.scenario_path}")
        print(f"Mapper: {self.mapper}")
        print(f"Total Time: {self.total_wall_time:.1f}s")
        print(f"{'='*70}\n")

        successful = self.get_successful_runs()
        failed = len(self.runs) - len(successful)

        if failed > 0:
            print(f"⚠️  {failed} configuration(s) failed\n")

        # Print table
        print(f"{'Config':<20} {'Fee (bps)':<12} {'Revenue ($)':<15} {'Volume ($)':<15} {'TPS':<10}")
        print(f"{'-'*70}")

        for run in successful:
            revenue = int(run.get_metric('rev_usdc', 0))
            volume = int(run.get_metric('vol_usdc', 0))
            tps = run.get_metric('tps_million', 0)

            print(f"{run.config.name:<20} {run.config.fee_bps_asset0:<12} "
                  f"${revenue:>13,} ${volume:>13,} {tps:>8.2f}M")


def run_scenario(
    scenario_path: str,
    mapper: str,
    config: Config,
    verbose: bool = False
) -> RunResult:
    """
    Run single simulation with given config.

    Args:
        scenario_path: Path to transaction CSV
        mapper: Protocol mapper ('solana', 'evm', 'depin', etc.)
        config: Simulation configuration
        verbose: Print detailed output

    Returns:
        RunResult: Simulation results and metrics
    """
    from .io import load_and_normalize, convert_to_testbench_format

    if verbose:
        print(f"  Running: {config.name} (fee_asset0={config.fee_bps_asset0} bps)...")

    start_time = time.time()

    try:
        # Clean previous stats
        stats_path = "logs/sim_stats.csv"
        if os.path.exists(stats_path):
            os.remove(stats_path)

        # Clean simulation artifacts
        subprocess.run(
            ["rm", "-rf", "tb/sim_build", "tb/results.xml", "tb/__pycache__"],
            check=False,
            capture_output=True
        )

        # Prepare environment
        env = os.environ.copy()
        env["FEE_BPS_ASSET0"] = str(config.fee_bps_asset0)
        env["FEE_BPS_ASSET1"] = str(config.fee_bps_asset1)

        # Normalize transactions
        processed_file = "data/processed_batch.csv"
        transactions = load_and_normalize(
            csv_path=scenario_path,
            mapper=mapper,
            num_users=1024,
            validate=True
        )
        convert_to_testbench_format(transactions, processed_file)
        env["SCENARIO_FILE"] = os.path.abspath(processed_file)

        # Run simulation
        cmd = ["make", "-C", "tb"]
        result = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=300)

        if result.returncode != 0:
            return RunResult(
                config=config,
                wall_time_seconds=time.time() - start_time,
                success=False,
                error_message=f"Simulation failed: {result.stderr[:200]}"
            )

        # Extract metrics
        metrics = {}
        if os.path.exists(stats_path):
            with open(stats_path, 'r') as f:
                for line in f:
                    if ',' in line and line.strip() != "metric,value":
                        k, v = line.strip().split(',', 1)
                        try:
                            metrics[k] = float(v)
                        except ValueError:
                            metrics[k] = v

        wall_time = time.time() - start_time

        if verbose:
            print(f"    ✓ Completed in {wall_time:.1f}s")

        return RunResult(
            config=config,
            metrics=metrics,
            wall_time_seconds=wall_time,
            success=True
        )

    except Exception as e:
        return RunResult(
            config=config,
            wall_time_seconds=time.time() - start_time,
            success=False,
            error_message=str(e)
        )


def run_experiments(
    scenario_path: str,
    mapper: str,
    configs: List[Config],
    verbose: bool = True
) -> ExperimentResult:
    """
    Run multiple simulations with different configs and compare results.

    This is the main entry point for parameter sweeps and A/B testing.

    Args:
        scenario_path: Path to transaction CSV
        mapper: Protocol mapper ('solana', 'evm', 'depin', etc.)
        configs: List of configurations to test
        verbose: Print progress updates

    Returns:
        ExperimentResult: Aggregated results from all runs

    Example:
        configs = [
            Config("No Fee", fee_bps_asset0=0),
            Config("Low", fee_bps_asset0=25),
            Config("Standard", fee_bps_asset0=50),
            Config("High", fee_bps_asset0=100),
        ]
        result = run_experiments('data/solana_day_1.csv', 'solana', configs)
        result.print_summary()
    """
    if verbose:
        print(f"\n🧪 Starting Experiment: {len(configs)} configurations")
        print(f"   Scenario: {scenario_path}")
        print(f"   Mapper: {mapper}\n")

    experiment_start = time.time()
    runs = []

    for i, config in enumerate(configs, 1):
        if verbose:
            print(f"[{i}/{len(configs)}]", end=" ")

        run_result = run_scenario(scenario_path, mapper, config, verbose=verbose)
        runs.append(run_result)

    total_time = time.time() - experiment_start

    result = ExperimentResult(
        runs=runs,
        scenario_path=scenario_path,
        mapper=mapper,
        total_wall_time=total_time
    )

    if verbose:
        result.print_summary()

    return result


def generate_fee_sweep_configs(
    start_bps: int = 0,
    end_bps: int = 200,
    step_bps: int = 25,
    asset: int = 0
) -> List[Config]:
    """
    Generate configs for fee sweep experiment.

    Args:
        start_bps: Starting fee in basis points
        end_bps: Ending fee in basis points (inclusive)
        step_bps: Step size in basis points
        asset: Which asset to sweep (0 or 1)

    Returns:
        List[Config]: Configurations for fee sweep

    Example:
        # Test fees from 0% to 2.0% in 0.25% increments
        configs = generate_fee_sweep_configs(0, 200, 25)
        # Result: [0, 25, 50, 75, 100, 125, 150, 175, 200] bps
    """
    configs = []
    for fee_bps in range(start_bps, end_bps + 1, step_bps):
        if asset == 0:
            name = f"{fee_bps} bps ({fee_bps/100:.2f}%)"
            configs.append(Config(name=name, fee_bps_asset0=fee_bps, fee_bps_asset1=0))
        else:
            name = f"Asset1: {fee_bps} bps"
            configs.append(Config(name=name, fee_bps_asset0=0, fee_bps_asset1=fee_bps))
    return configs
