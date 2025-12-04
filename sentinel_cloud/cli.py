"""
Sentinel Cloud CLI - Command-line interface for tokenomics testing

Usage:
    sentinel run data/solana.csv --fee 50
    sentinel sweep data/solana.csv --range 0 200 25
    sentinel compare data/solana.csv --configs conservative:25 aggressive:150
"""

import sys
import click
from pathlib import Path
from typing import List, Tuple

from .client import SentinelClient
from .mappers import SUPPORTED_PROTOCOLS


@click.group()
@click.version_option(version='0.3.0', prog_name='sentinel')
def cli():
    """
    Sentinel Cloud - Hardware-accelerated tokenomics wind tunnel

    Test economic parameters against real transaction data before deploying to production.
    """
    pass


@cli.command()
@click.argument('scenario', type=click.Path(exists=True))
@click.option('--fee', '-f', type=int, default=50,
              help='Fee in basis points (default: 50 = 0.50%)')
@click.option('--fee-asset1', type=int, default=0,
              help='Fee for asset1 in basis points (default: 0)')
@click.option('--mapper', '-m', type=str, default='solana',
              help='Protocol mapper (solana, evm, depin, etc.)')
@click.option('--name', '-n', type=str, default=None,
              help='Configuration name')
@click.option('--verbose', '-v', is_flag=True,
              help='Enable verbose output')
def run(scenario: str, fee: int, fee_asset1: int, mapper: str, name: str, verbose: bool):
    """
    Run a single simulation with specified configuration.

    \b
    Examples:
        sentinel run data/solana.csv --fee 50
        sentinel run data/solana.csv --fee 100 --name "High Fee"
        sentinel run data/evm.csv --fee 25 --mapper evm
    """
    # Validate inputs
    if not (0 <= fee <= 10000):
        click.echo(f"❌ Error: Fee {fee} bps is out of range [0, 10000] (0-100%)", err=True)
        click.echo(f"   Hint: 50 bps = 0.50%, 100 bps = 1.00%", err=True)
        sys.exit(1)

    if not (0 <= fee_asset1 <= 10000):
        click.echo(f"❌ Error: Fee asset1 {fee_asset1} bps is out of range [0, 10000]", err=True)
        sys.exit(1)

    if mapper not in SUPPORTED_PROTOCOLS:
        click.echo(f"❌ Error: Unknown mapper '{mapper}'", err=True)
        click.echo(f"   Supported mappers: {', '.join(sorted(SUPPORTED_PROTOCOLS.keys()))}", err=True)
        sys.exit(1)

    if not Path(scenario).exists():
        click.echo(f"❌ Error: Scenario file not found: {scenario}", err=True)
        click.echo(f"   Hint: Use an absolute path or path relative to current directory", err=True)
        sys.exit(1)

    client = SentinelClient(verbose=verbose)

    try:
        click.echo(f"🚀 Running simulation on {scenario}")
        click.echo(f"   Fee: {fee} bps ({fee/100:.2f}%), Mapper: {mapper}")

        result = client.run(
            scenario=scenario,
            fee_bps=fee,
            fee_bps_asset1=fee_asset1,
            mapper=mapper,
            config_name=name
        )

        if result.success:
            click.echo(f"\n✅ Simulation Complete!\n")
            click.echo(result)
            sys.exit(0)
        else:
            click.echo(f"\n❌ Simulation Failed")
            click.echo(f"   Error: {result.error_message}")
            sys.exit(1)

    except FileNotFoundError as e:
        click.echo(f"❌ File not found: {e}", err=True)
        sys.exit(1)
    except ValueError as e:
        click.echo(f"❌ Invalid parameter: {e}", err=True)
        sys.exit(1)
    except Exception as e:
        click.echo(f"❌ Unexpected error: {e}", err=True)
        if verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


@cli.command()
@click.argument('scenario', type=click.Path(exists=True))
@click.option('--range', '-r', 'fee_range', type=(int, int, int), default=None,
              help='Fee range as START END STEP (e.g., --range 0 200 25)')
@click.option('--fees', '-f', multiple=True, type=int,
              help='Explicit fee list (can be repeated: -f 0 -f 50 -f 100)')
@click.option('--mapper', '-m', type=str, default='solana',
              help='Protocol mapper (solana, evm, depin, etc.)')
@click.option('--export', '-e', type=click.Path(), default=None,
              help='Export results to JSON file')
@click.option('--analyze', '-a', is_flag=True, default=True,
              help='Show fee sweep analysis (default: True)')
@click.option('--verbose', '-v', is_flag=True,
              help='Enable verbose output')
def sweep(scenario: str, fee_range: Tuple[int, int, int], fees: Tuple[int, ...],
          mapper: str, export: str, analyze: bool, verbose: bool):
    """
    Run parameter sweep across multiple fee configurations.

    \b
    Examples:
        # Sweep from 0% to 2% in 0.25% steps
        sentinel sweep data/solana.csv --range 0 200 25

        # Test specific fee points
        sentinel sweep data/solana.csv -f 0 -f 50 -f 100

        # Export results to JSON
        sentinel sweep data/solana.csv --range 0 200 25 --export results.json
    """
    # Validate mapper
    if mapper not in SUPPORTED_PROTOCOLS:
        click.echo(f"❌ Error: Unknown mapper '{mapper}'", err=True)
        click.echo(f"   Supported mappers: {', '.join(sorted(SUPPORTED_PROTOCOLS.keys()))}", err=True)
        sys.exit(1)

    # Validate fee range if provided
    if fee_range:
        start, end, step = fee_range
        if not (0 <= start <= 10000 and 0 <= end <= 10000):
            click.echo(f"❌ Error: Fee range [{start}, {end}] out of bounds [0, 10000]", err=True)
            sys.exit(1)
        if start > end:
            click.echo(f"❌ Error: Invalid fee range: start ({start}) > end ({end})", err=True)
            sys.exit(1)
        if step <= 0:
            click.echo(f"❌ Error: Step size must be positive, got {step}", err=True)
            sys.exit(1)

    # Validate explicit fees if provided
    if fees:
        for fee in fees:
            if not (0 <= fee <= 10000):
                click.echo(f"❌ Error: Fee {fee} bps is out of range [0, 10000]", err=True)
                sys.exit(1)

    if not Path(scenario).exists():
        click.echo(f"❌ Error: Scenario file not found: {scenario}", err=True)
        sys.exit(1)

    client = SentinelClient(verbose=verbose)

    try:
        if fees:
            click.echo(f"🧪 Running fee sweep on {scenario}")
            click.echo(f"   Testing {len(fees)} configurations: {list(fees)} bps")
        elif fee_range:
            start, end, step = fee_range
            num_configs = len(range(start, end + 1, step))
            click.echo(f"🧪 Running fee sweep on {scenario}")
            click.echo(f"   Range: {start}-{end} bps in {step} bps steps ({num_configs} configs)")
        else:
            click.echo(f"🧪 Running default fee sweep on {scenario}")
            click.echo(f"   Testing: 0, 25, 50, 100 bps")

        sweep_result = client.sweep(
            scenario=scenario,
            fee_range=fee_range if fee_range else None,
            fee_list=list(fees) if fees else None,
            mapper=mapper
        )

        click.echo(f"\n")
        sweep_result.print_summary()

        if analyze and len(sweep_result.get_successful()) >= 2:
            sweep_result.print_analysis()

        if export:
            sweep_result.to_json(export)
            click.echo(f"\n💾 Results exported to: {export}")

        # Exit with success if all ran successfully, failure if any failed
        failed = len([r for r in sweep_result.results if not r.success])
        if failed > 0:
            click.echo(f"\n⚠️  {failed} configuration(s) failed")
            sys.exit(1)
        else:
            click.echo(f"\n✅ All {len(sweep_result)} configurations completed successfully")
            sys.exit(0)

    except Exception as e:
        click.echo(f"❌ Error: {e}", err=True)
        sys.exit(1)


@cli.command()
@click.argument('scenario', type=click.Path(exists=True))
@click.option('--config', '-c', 'configs', multiple=True, required=True,
              help='Named config as NAME:FEE (e.g., -c conservative:25 -c aggressive:150)')
@click.option('--mapper', '-m', type=str, default='solana',
              help='Protocol mapper (solana, evm, depin, etc.)')
@click.option('--export', '-e', type=click.Path(), default=None,
              help='Export results to JSON file')
@click.option('--verbose', '-v', is_flag=True,
              help='Enable verbose output')
def compare(scenario: str, configs: Tuple[str, ...], mapper: str, export: str, verbose: bool):
    """
    Compare specific named configurations.

    \b
    Examples:
        sentinel compare data/solana.csv \\
            -c conservative:25 \\
            -c moderate:50 \\
            -c aggressive:150

        sentinel compare data/solana.csv \\
            -c "Launch Config:75" \\
            -c "Stress Test:200" \\
            --export comparison.json
    """
    client = SentinelClient(verbose=verbose)

    try:
        # Parse config strings
        parsed_configs: List[Tuple[str, int]] = []
        for config_str in configs:
            if ':' not in config_str:
                click.echo(f"❌ Invalid config format: '{config_str}' (expected NAME:FEE)", err=True)
                sys.exit(1)

            name, fee_str = config_str.rsplit(':', 1)
            try:
                fee = int(fee_str)
                if not (0 <= fee <= 10000):
                    click.echo(f"❌ Fee {fee} bps out of range [0, 10000]", err=True)
                    sys.exit(1)
                parsed_configs.append((name, fee))
            except ValueError:
                click.echo(f"❌ Invalid fee value: '{fee_str}' (must be integer)", err=True)
                sys.exit(1)

        click.echo(f"🔬 Comparing {len(parsed_configs)} configurations on {scenario}")
        for name, fee in parsed_configs:
            click.echo(f"   - {name}: {fee} bps ({fee/100:.2f}%)")

        result = client.compare(
            scenario=scenario,
            configs=parsed_configs,
            mapper=mapper
        )

        click.echo(f"\n")
        result.print_summary()

        if export:
            result.to_json(export)
            click.echo(f"\n💾 Results exported to: {export}")

        # Exit with success if all ran successfully
        failed = len([r for r in result.results if not r.success])
        if failed > 0:
            click.echo(f"\n⚠️  {failed} configuration(s) failed")
            sys.exit(1)
        else:
            click.echo(f"\n✅ All {len(result)} configurations completed successfully")
            sys.exit(0)

    except Exception as e:
        click.echo(f"❌ Error: {e}", err=True)
        sys.exit(1)


def main():
    """Entry point for the CLI."""
    cli()


if __name__ == '__main__':
    main()
