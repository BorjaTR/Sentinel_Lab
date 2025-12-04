"""
Dashboard I/O - Load and manage experiment results for visualization

This module provides helpers for the Streamlit dashboard to discover
and load experiment results from the file system.

Usage:
    from sentinel_cloud.dashboard_io import list_experiments, load_experiment

    # Discover available experiments
    experiments = list_experiments("experiments/")

    # Load a specific experiment
    result = load_experiment("experiments/sweep_2025_12_04.json")
"""

import json
from pathlib import Path
from typing import List, Optional
from datetime import datetime

from .experiment import ExperimentResult, RunResult, Config


def list_experiments(experiments_dir: str = "experiments") -> List[Path]:
    """
    List all experiment JSON files in a directory.

    Args:
        experiments_dir: Directory to search for experiment files

    Returns:
        List of Path objects to experiment JSON files, sorted by modification time (newest first)

    Example:
        >>> experiments = list_experiments("experiments/")
        >>> for exp in experiments:
        ...     print(exp.name)
    """
    exp_path = Path(experiments_dir)

    if not exp_path.exists():
        return []

    # Find all JSON files
    json_files = list(exp_path.glob("*.json"))

    # Sort by modification time, newest first
    json_files.sort(key=lambda p: p.stat().st_mtime, reverse=True)

    return json_files


def load_experiment(path: str) -> Optional[ExperimentResult]:
    """
    Load an experiment result from JSON file.

    Args:
        path: Path to experiment JSON file

    Returns:
        ExperimentResult object, or None if loading fails

    Example:
        >>> result = load_experiment("experiments/sweep_2025_12_04.json")
        >>> print(f"Loaded {len(result.runs)} configurations")
    """
    try:
        with open(path, 'r') as f:
            data = json.load(f)

        # Reconstruct ExperimentResult from JSON
        runs = []
        for run_data in data.get('runs', []):
            # Reconstruct Config
            config_data = run_data.get('config', {})
            config = Config(
                name=config_data.get('name', 'Unknown'),
                fee_bps_asset0=config_data.get('fee_bps_asset0', 0),
                fee_bps_asset1=config_data.get('fee_bps_asset1', 0)
            )

            # Reconstruct RunResult with only the fields it actually has
            run_result = RunResult(
                config=config,
                metrics=run_data.get('metrics', {}),
                wall_time_seconds=run_data.get('wall_time_seconds', 0.0),
                success=run_data.get('success', False),
                error_message=run_data.get('error_message', '')
            )
            runs.append(run_result)

        # Reconstruct ExperimentResult
        experiment = ExperimentResult(
            scenario_path=data.get('scenario_path', ''),
            mapper=data.get('mapper', ''),
            runs=runs
        )

        return experiment

    except Exception as e:
        print(f"Error loading experiment from {path}: {e}")
        return None


def load_multiple(paths: List[str]) -> List[ExperimentResult]:
    """
    Load multiple experiment results.

    Args:
        paths: List of paths to experiment JSON files

    Returns:
        List of ExperimentResult objects (excluding any that failed to load)

    Example:
        >>> paths = ["exp1.json", "exp2.json"]
        >>> results = load_multiple(paths)
        >>> print(f"Loaded {len(results)} experiments")
    """
    results = []
    for path in paths:
        result = load_experiment(path)
        if result is not None:
            results.append(result)
    return results


def get_experiment_metadata(path: Path) -> dict:
    """
    Extract basic metadata from an experiment without fully loading it.

    Args:
        path: Path to experiment JSON file

    Returns:
        Dictionary with metadata (name, timestamp, num_configs, scenario)

    Example:
        >>> meta = get_experiment_metadata(Path("experiments/sweep.json"))
        >>> print(meta['name'], meta['timestamp'])
    """
    try:
        with open(path, 'r') as f:
            data = json.load(f)

        # Extract key metadata
        num_runs = len(data.get('runs', []))
        scenario = Path(data.get('scenario_path', 'unknown')).name
        mapper = data.get('mapper', 'unknown')

        # Use file modification time as timestamp
        mtime = path.stat().st_mtime
        timestamp = datetime.fromtimestamp(mtime).strftime('%Y-%m-%d %H:%M:%S')

        # Create display name
        name = path.stem

        return {
            'name': name,
            'path': str(path),
            'timestamp': timestamp,
            'num_configs': num_runs,
            'scenario': scenario,
            'mapper': mapper,
            'display_name': f"{name} ({num_runs} configs, {timestamp})"
        }

    except Exception as e:
        return {
            'name': path.stem,
            'path': str(path),
            'timestamp': 'unknown',
            'num_configs': 0,
            'scenario': 'unknown',
            'mapper': 'unknown',
            'display_name': f"{path.stem} (error loading metadata)"
        }


def save_experiment(experiment: ExperimentResult, output_dir: str = "experiments",
                   filename: Optional[str] = None) -> Path:
    """
    Save an experiment result to JSON file.

    Args:
        experiment: ExperimentResult to save
        output_dir: Directory to save to
        filename: Optional custom filename (auto-generated if None)

    Returns:
        Path to saved file

    Example:
        >>> path = save_experiment(result, "experiments/")
        >>> print(f"Saved to {path}")
    """
    # Create output directory if needed
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    # Generate filename if not provided
    if filename is None:
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        scenario_name = Path(experiment.scenario_path).stem
        filename = f"sweep_{scenario_name}_{timestamp}.json"

    # Save to file
    file_path = output_path / filename
    experiment.to_json(str(file_path))

    return file_path
