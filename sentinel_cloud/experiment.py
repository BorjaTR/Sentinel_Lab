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
    - Time-series: Transaction-level snapshots for visualization
    - Role Economics: Per-role metrics and treasury state (Phase 6)

    Attributes:
        config: Configuration used for this run
        metrics: Dictionary of metric_name → value
        wall_time_seconds: Simulation wall clock time
        success: Whether simulation completed successfully
        error_message: Error message if simulation failed
        time_series: List of time-series snapshots (tx_count, vault, success_rate, etc.)
        role_metrics: Per-role economic metrics (Phase 6)
        treasury_state: Treasury sustainability metrics (Phase 6)
    """
    config: Config
    metrics: Dict[str, float] = field(default_factory=dict)
    wall_time_seconds: float = 0.0
    success: bool = True
    error_message: str = ""
    time_series: List[Dict[str, Any]] = field(default_factory=list)
    role_metrics: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    treasury_state: Optional[Dict[str, Any]] = None
    treasury_config: Optional[Dict[str, Any]] = None  # Phase 6.5: Make assumptions explicit

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
            'error_message': self.error_message,
            'time_series': self.time_series,
            'role_metrics': self.role_metrics,
            'treasury_state': self.treasury_state,
            'treasury_config': self.treasury_config
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
        """Print human-readable summary to console with Phase 3.5 metrics."""
        print(f"\n{'='*90}")
        print(f"Experiment Summary: {len(self.runs)} configurations")
        print(f"Scenario: {self.scenario_path}")
        print(f"Mapper: {self.mapper}")
        print(f"Total Time: {self.total_wall_time:.1f}s")
        print(f"{'='*90}\n")

        successful = self.get_successful_runs()
        failed = len(self.runs) - len(successful)

        if failed > 0:
            print(f"⚠️  {failed} configuration(s) failed\n")

        # Print table with new metrics
        print(f"{'Config':<18} {'Fee':<8} {'Revenue':<12} {'Volume':<12} {'Engine TPS':<11} {'Lab TPS':<10} {'Fail%':<6}")
        print(f"{'-'*90}")

        for run in successful:
            revenue = int(run.get_metric('rev_usdc', 0))
            volume = int(run.get_metric('vol_usdc', 0))
            engine_tps = run.get_metric('engine_tps', 0) / 1_000_000  # Convert to millions
            lab_tps = run.get_metric('lab_tps', 0) / 1_000  # Convert to thousands
            failure_rate = run.get_metric('failure_rate', 0) * 100  # Convert to percentage

            print(f"{run.config.name:<18} "
                  f"{run.config.fee_bps_asset0:<3} bps "
                  f"${revenue:>10,} "
                  f"${volume:>10,} "
                  f"{engine_tps:>9.2f}M "
                  f"{lab_tps:>8.1f}K "
                  f"{failure_rate:>5.1f}%")

    def summarize_fee_sweep(self, failure_threshold: float = 0.01):
        """
        Provide human-readable interpretation of fee sweep results.

        This method analyzes the experiment results and provides:
        - Optimal fee recommendation (by revenue)
        - Revenue scaling analysis
        - Volume impact assessment
        - Failure rate warnings

        Args:
            failure_threshold: Failure rate threshold (default 1%)
        """
        successful = self.get_successful_runs()

        if len(successful) == 0:
            print("\n❌ No successful runs to analyze")
            return

        print(f"\n{'='*70}")
        print("Fee Sweep Analysis")
        print(f"{'='*70}\n")

        # Find optimal config by revenue
        optimal = max(successful, key=lambda r: r.get_metric('rev_usdc', 0))
        optimal_revenue = optimal.get_metric('rev_usdc', 0)
        optimal_volume = optimal.get_metric('vol_usdc', 0)
        optimal_failure = optimal.get_metric('failure_rate', 0)
        optimal_lab_tps = optimal.get_metric('lab_tps', 0)

        print(f"✅ Optimal Fee (by revenue): {optimal.config.fee_bps_asset0} bps ({optimal.config.fee_bps_asset0/100:.2f}%)")
        print(f"   Revenue:      ${optimal_revenue:>12,.0f}")
        print(f"   Volume:       ${optimal_volume:>12,.0f}")
        print(f"   Lab TPS:      {optimal_lab_tps:>12,.0f} tx/s")
        print(f"   Failure rate: {optimal_failure*100:>12.1f}%")

        # Revenue scaling analysis
        if len(successful) >= 2:
            sorted_by_fee = sorted(successful, key=lambda r: r.config.fee_bps_asset0)
            min_fee_run = sorted_by_fee[0]
            max_fee_run = sorted_by_fee[-1]

            min_revenue = min_fee_run.get_metric('rev_usdc', 0)
            max_revenue = max_fee_run.get_metric('rev_usdc', 0)
            min_volume = min_fee_run.get_metric('vol_usdc', 0)
            max_volume = max_fee_run.get_metric('vol_usdc', 0)

            revenue_change = max_revenue - min_revenue
            volume_loss = (min_volume - max_volume) / min_volume * 100 if min_volume > 0 else 0

            print(f"\n📊 Revenue vs Fee:")
            print(f"   {min_fee_run.config.fee_bps_asset0} bps → {max_fee_run.config.fee_bps_asset0} bps:")
            print(f"   - Revenue change: ${revenue_change:>+12,.0f}")
            print(f"   - Volume loss:    {volume_loss:>12.2f}%")

            # Linearity check
            if len(successful) >= 3:
                # Check if revenue scales linearly with fee
                revenues = [r.get_metric('rev_usdc', 0) for r in sorted_by_fee]
                fees = [r.config.fee_bps_asset0 for r in sorted_by_fee]

                # Simple linearity check: compare first-to-middle and middle-to-last
                if len(revenues) >= 3:
                    mid = len(revenues) // 2
                    slope1 = (revenues[mid] - revenues[0]) / (fees[mid] - fees[0]) if fees[mid] != fees[0] else 0
                    slope2 = (revenues[-1] - revenues[mid]) / (fees[-1] - fees[mid]) if fees[-1] != fees[mid] else 0

                    if abs(slope1 - slope2) / max(abs(slope1), abs(slope2), 1) < 0.1:  # Within 10%
                        print(f"   - Scaling:        Linear (revenue ∝ fee)")
                    else:
                        print(f"   - Scaling:        Non-linear (check volume impact)")

        # Failure rate warnings
        high_failure_runs = [r for r in successful if r.get_metric('failure_rate', 0) > failure_threshold]
        if high_failure_runs:
            print(f"\n⚠️  High Failure Rate Detected:")
            for run in high_failure_runs:
                print(f"   - {run.config.name}: {run.get_metric('failure_rate', 0)*100:.1f}% failures")

        # Recommendation
        print(f"\n💡 Recommendation:")
        if optimal_failure < failure_threshold and volume_loss < 1.0:
            print(f"   {optimal.config.fee_bps_asset0} bps is a strong launch candidate:")
            print(f"   - Maximizes revenue (${optimal_revenue:,.0f})")
            print(f"   - Negligible volume impact ({volume_loss:.2f}% loss)")
            print(f"   - Low failure rate ({optimal_failure*100:.1f}%)")
        elif optimal_failure >= failure_threshold:
            print(f"   ⚠️  Optimal fee ({optimal.config.fee_bps_asset0} bps) has high failure rate")
            print(f"   Consider lower fee to reduce failures")
        elif volume_loss >= 5.0:
            print(f"   ⚠️  High fees causing significant volume loss ({volume_loss:.2f}%)")
            print(f"   Consider {min_fee_run.config.fee_bps_asset0} bps to preserve volume")
        else:
            print(f"   {optimal.config.fee_bps_asset0} bps balances revenue and volume")

        print(f"\n{'='*70}\n")


def run_scenario(
    scenario_path: str,
    mapper: str,
    config: Config,
    verbose: bool = False,
    transactions: Optional[List] = None
) -> RunResult:
    """
    Run single simulation with given config.

    Args:
        scenario_path: Path to transaction CSV (ignored if transactions provided)
        mapper: Protocol mapper ('solana', 'evm', 'depin', etc.)
        config: Simulation configuration
        verbose: Print detailed output
        transactions: Optional pre-loaded transactions (for streaming mode)

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

        # Ensure cocotb is in PATH (critical for Streamlit/dashboard execution)
        # When running from Streamlit, the PATH may not include /usr/local/bin
        # Force inclusion of common installation paths
        required_paths = ['/usr/local/bin', '/usr/bin', '/root/.local/bin']

        if 'PATH' in env and env['PATH']:
            existing_path = env['PATH']
            # Prepend required paths to ensure they're found first
            env['PATH'] = ':'.join(required_paths) + ':' + existing_path
        else:
            # No PATH set, create one
            env['PATH'] = ':'.join(required_paths)

        # Detect cocotb makefiles path via Python (more reliable than cocotb-config binary)
        # This bypasses the need for cocotb-config to be in PATH
        cocotb_makefiles = None

        # Method 1: Try importing cocotb
        try:
            import cocotb
            detected_path = os.path.join(
                os.path.dirname(cocotb.__file__),
                'share',
                'makefiles'
            )
            # Only use detected path if it exists AND isn't a cross-platform mismatch
            # (e.g., macOS path on Linux system)
            import platform
            if os.path.exists(detected_path):
                # Check for cross-platform path issues
                if platform.system() == 'Linux' and detected_path.startswith('/Users/'):
                    # macOS path on Linux - ignore it
                    pass
                else:
                    cocotb_makefiles = detected_path
        except (ImportError, AttributeError):
            pass

        # Method 2: Try common installation paths as fallback
        if not cocotb_makefiles:
            common_paths = [
                '/usr/local/lib/python3.11/dist-packages/cocotb/share/makefiles',
                '/usr/local/lib/python3.10/dist-packages/cocotb/share/makefiles',
                '/usr/lib/python3/dist-packages/cocotb/share/makefiles',
            ]
            for path in common_paths:
                # Don't check existence - Streamlit may have restricted filesystem access
                # Just try the paths in order and use the first one
                cocotb_makefiles = path
                break

        # Last resort: use the known working path
        if not cocotb_makefiles:
            cocotb_makefiles = '/usr/local/lib/python3.11/dist-packages/cocotb/share/makefiles'

        # Verify the path and Makefile.sim exist before setting
        makefile_sim = os.path.join(cocotb_makefiles, 'Makefile.sim')
        if not os.path.exists(makefile_sim):
            # Try to find it in alternate locations
            import glob
            possible_locations = glob.glob('/usr/*/lib/python*/dist-packages/cocotb/share/makefiles/Makefile.sim')
            possible_locations += glob.glob('/root/.local/lib/python*/site-packages/cocotb/share/makefiles/Makefile.sim')
            if possible_locations:
                cocotb_makefiles = os.path.dirname(possible_locations[0])

        # Always set it - let make fail if path is actually wrong
        env["COCOTB_MAKEFILES"] = cocotb_makefiles

        env["FEE_BPS_ASSET0"] = str(config.fee_bps_asset0)
        env["FEE_BPS_ASSET1"] = str(config.fee_bps_asset1)

        # Normalize transactions (or use provided transactions for streaming)
        processed_file = "data/processed_batch.csv"
        if transactions is None:
            transactions = load_and_normalize(
                csv_path=scenario_path,
                mapper=mapper,
                num_users=1024,
                validate=True
            )
        convert_to_testbench_format(transactions, processed_file)
        env["SCENARIO_FILE"] = os.path.abspath(processed_file)

        # Run simulation
        # Find tb directory - prefer relative to package location, fall back to hardcoded path
        tb_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'tb'))

        # If that doesn't exist (shouldn't happen in normal installation), use hardcoded path
        if not os.path.exists(tb_dir):
            tb_dir = '/home/user/Sentinel_Lab/tb'

        # Final check - if still not found, try current directory
        if not os.path.exists(tb_dir):
            tb_dir = os.path.abspath('tb')

        cmd = ["make", "-C", tb_dir]

        # Ensure PATH is set in environment for subprocess
        # This handles both the make process and any shell commands it spawns
        result = subprocess.run(
            cmd,
            env=env,
            capture_output=True,
            text=True,
            timeout=300,
            shell=False  # Explicitly don't use shell to avoid PATH issues
        )

        if result.returncode != 0:
            # Enhanced error message with debugging info
            error_parts = []
            error_parts.append(f"Simulation failed (returncode={result.returncode})")
            error_parts.append(f"tb_dir: {tb_dir}")
            error_parts.append(f"tb_dir exists: {os.path.exists(tb_dir)}")

            if "cocotb-config" in result.stderr or "Makefile.sim" in result.stderr or "makefile" in result.stderr.lower():
                cocotb_path = env.get('COCOTB_MAKEFILES', 'NOT SET')
                error_parts.append(f"COCOTB_MAKEFILES: {cocotb_path}")

                # Check if the path exists from Python's perspective
                if cocotb_path != 'NOT SET':
                    makefile_exists = os.path.exists(os.path.join(cocotb_path, 'Makefile.sim'))
                    error_parts.append(f"Makefile.sim exists (from Python): {makefile_exists}")

                    # List what's actually in that directory
                    if os.path.exists(cocotb_path):
                        try:
                            files = os.listdir(cocotb_path)[:5]
                            error_parts.append(f"Files in dir: {files}")
                        except:
                            error_parts.append("Cannot list directory")

            error_parts.append(f"stderr: {result.stderr[:500]}")

            if result.stdout:
                error_parts.append(f"stdout: {result.stdout[:200]}")

            return RunResult(
                config=config,
                wall_time_seconds=time.time() - start_time,
                success=False,
                error_message=" | ".join(error_parts)
            )

        # Extract metrics from sim_stats.csv
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
        num_tx = len(transactions)

        # Add Phase 3.5 metrics
        # A. Engine TPS vs Lab TPS
        CLOCK_HZ = 100_000_000  # 100 MHz
        TX_PER_CYCLE = 1        # 1 transaction per cycle
        metrics['engine_tps'] = float(CLOCK_HZ * TX_PER_CYCLE)  # Theoretical max
        metrics['lab_tps'] = float(num_tx / wall_time) if wall_time > 0 else 0.0  # Measured throughput
        metrics['num_tx'] = float(num_tx)

        # B. Econ-native metrics
        # B.1: Failure rate (from sim_stats.csv)
        # Now parsed directly from testbench logs
        # Set default only if not found in logs
        if 'failure_rate' not in metrics:
            metrics['failure_rate'] = 0.0
        if 'success_count' not in metrics:
            metrics['success_count'] = float(num_tx)
        if 'failure_count' not in metrics:
            metrics['failure_count'] = 0.0

        # B.2: Behavioral signals from transactions
        if num_tx > 0:
            asset0_amounts = [tx.asset0_amount for tx in transactions if tx.asset0_amount > 0]
            if asset0_amounts:
                metrics['avg_amount_asset0'] = float(sum(asset0_amounts) / len(asset0_amounts))
                metrics['median_amount_asset0'] = float(sorted(asset0_amounts)[len(asset0_amounts) // 2])
                metrics['max_amount_asset0'] = float(max(asset0_amounts))
            else:
                metrics['avg_amount_asset0'] = 0.0
                metrics['median_amount_asset0'] = 0.0
                metrics['max_amount_asset0'] = 0.0
        else:
            metrics['avg_amount_asset0'] = 0.0
            metrics['median_amount_asset0'] = 0.0
            metrics['max_amount_asset0'] = 0.0

        # Load time-series data if available
        time_series = []
        time_series_path = "logs/time_series.csv"
        if os.path.exists(time_series_path):
            try:
                import csv
                with open(time_series_path, 'r') as f:
                    reader = csv.DictReader(f)
                    for row in reader:
                        time_series.append({
                            'batch': int(row['batch']),
                            'tx_count': int(row['tx_count']),
                            'time_ns': float(row['time_ns']),
                            'tps': float(row['tps']),
                            'success_rate': float(row['success_rate']),
                            'vault_usdc': int(row['vault_usdc']),
                            'vault_gpu': int(row['vault_gpu'])
                        })
            except Exception as e:
                if verbose:
                    print(f"    ⚠️  Warning: Could not load time_series.csv: {e}")

        # Phase 6: Role-based economics analysis
        role_metrics_dict = {}
        treasury_state_dict = None
        treasury_config_dict = None
        try:
            from .role_economics import RoleAnalyzer, TreasuryConfig, calculate_simulation_days

            # Calculate actual simulation duration from timestamps
            simulation_days = calculate_simulation_days(transactions)

            # Create treasury config with explicit assumptions
            treasury_config = TreasuryConfig(
                initial_balance_usdc=1_000_000.0,  # Default: 1M USDC
                simulation_days=simulation_days,
                emissions_schedule=None  # No emissions by default
            )

            # Analyze role-based economics
            analyzer = RoleAnalyzer(transactions, fee_bps=config.fee_bps_asset0)
            role_metrics = analyzer.get_role_breakdown()

            # Convert to serializable format
            role_metrics_dict = {
                role: metrics.to_dict()
                for role, metrics in role_metrics.items()
            }

            # Calculate treasury state
            treasury = analyzer.calculate_treasury_state(treasury_config)

            treasury_state_dict = {
                'balance_usdc': treasury.balance_usdc,
                'revenue_rate_per_day': treasury.revenue_rate_per_day,
                'burn_rate_per_day': treasury.burn_rate_per_day,
                'runway_days': treasury.runway_days if treasury.runway_days != float('inf') else None,
                'is_sustainable': treasury.is_sustainable,
                'depletion_risk': treasury.depletion_risk,
                'fees_collected': treasury.fees_collected,
                'emissions_sent': treasury.emissions_sent
            }

            # Store treasury config for reproducibility
            treasury_config_dict = treasury_config.to_dict()

            # Phase 6.5: Validate economics invariants
            if verbose:
                from .role_economics import validate_economics_consistency
                invariant_errors = validate_economics_consistency(
                    transactions=transactions,
                    role_metrics=role_metrics,
                    treasury_state=treasury,
                    fee_bps=config.fee_bps_asset0,
                    tolerance=0.01
                )
                if invariant_errors:
                    print(f"    ⚠️  Economics invariant violations detected:")
                    for err in invariant_errors:
                        print(f"       - {err}")

        except Exception as e:
            if verbose:
                print(f"    ⚠️  Warning: Could not calculate role economics: {e}")

        if verbose:
            print(f"    ✓ Completed in {wall_time:.1f}s")

        return RunResult(
            config=config,
            metrics=metrics,
            wall_time_seconds=wall_time,
            success=True,
            time_series=time_series,
            role_metrics=role_metrics_dict,
            treasury_state=treasury_state_dict,
            treasury_config=treasury_config_dict
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
