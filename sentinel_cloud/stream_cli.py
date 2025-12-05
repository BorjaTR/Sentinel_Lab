"""
Streaming Mode CLI - Phase 7

Command-line interface for running Sentinel in streaming mode.

Usage:
    # Monitor CSV file with tumbling window
    python3 -m sentinel_cloud.stream_cli \
        --input data/solana_day_1.csv \
        --mapper solana \
        --window-size 1000 \
        --fee 50

    # Shadow-node mode: compare multiple fees
    python3 -m sentinel_cloud.stream_cli \
        --input data/solana_day_1.csv \
        --mapper solana \
        --shadow 25,50,100 \
        --window-size 500

    # With treasury alerts
    python3 -m sentinel_cloud.stream_cli \
        --input data/solana_day_1.csv \
        --mapper solana \
        --fee 50 \
        --alert-treasury 90 \
        --alert-failure 0.01
"""

import sys
import click
from pathlib import Path
from typing import List

from .streaming import (
    StreamProcessor,
    ShadowNode,
    TumblingWindow,
    AlertRule
)
from .experiment import Config
from .io import load_and_normalize


@click.command()
@click.option('--input', '-i', required=True, help='Input CSV file')
@click.option('--mapper', '-m', required=True, help='Protocol mapper (solana, evm, etc.)')
@click.option('--fee', '-f', type=int, default=50, help='Fee in basis points (default: 50)')
@click.option('--window-size', '-w', type=int, default=1000, help='Window size in transactions (default: 1000)')
@click.option('--shadow', help='Shadow mode: comma-separated fees (e.g., "25,50,100")')
@click.option('--alert-treasury', type=int, help='Alert if treasury runway < N days')
@click.option('--alert-failure', type=float, help='Alert if failure rate > threshold (e.g., 0.01 for 1%)')
@click.option('--alert-role', is_flag=True, help='Alert on role economic imbalances')
@click.option('--checkpoint-dir', help='Directory for checkpointing (optional)')
@click.option('--verbose', '-v', is_flag=True, help='Verbose output')
def stream(
    input: str,
    mapper: str,
    fee: int,
    window_size: int,
    shadow: str,
    alert_treasury: int,
    alert_failure: float,
    alert_role: bool,
    checkpoint_dir: str,
    verbose: bool
):
    """Run Sentinel in streaming mode."""

    click.echo(f"\n🌊 Sentinel Streaming Mode")
    click.echo(f"{'='*60}")
    click.echo(f"Input: {input}")
    click.echo(f"Mapper: {mapper}")
    click.echo(f"Window: {window_size} transactions (tumbling)")

    # Load transactions
    click.echo(f"\n📥 Loading transactions...")
    try:
        transactions = load_and_normalize(
            csv_path=input,
            mapper=mapper,
            num_users=1024,
            validate=True
        )
        click.echo(f"✅ Loaded {len(transactions)} transactions")
    except Exception as e:
        click.echo(f"❌ Error loading transactions: {e}", err=True)
        sys.exit(1)

    # Shadow mode or single processor
    if shadow:
        fees = [int(f.strip()) for f in shadow.split(',')]
        click.echo(f"\n🔀 Shadow Node Mode: {len(fees)} configs")
        for f in fees:
            click.echo(f"   - {f} bps ({f/100:.2f}%)")

        configs = [Config(f"{f} bps", fee_bps_asset0=f) for f in fees]
        shadow_node = ShadowNode(
            window=TumblingWindow(size=window_size),
            mapper=mapper,
            configs=configs,
            verbose=verbose
        )

        # Process stream
        click.echo(f"\n🔄 Processing stream...")
        window_count = 0
        for tx in transactions:
            results = shadow_node.ingest(tx)
            if results:
                window_count += 1
                click.echo(f"\n📊 Window {window_count} Results:")
                for cfg_name, result in results.items():
                    revenue = result.get_metric('rev_usdc', 0)
                    volume = result.get_metric('vol_usdc', 0)
                    failure = result.get_metric('failure_rate', 0) * 100
                    click.echo(f"   {cfg_name:>10}: Revenue ${revenue:>10,.0f}  Volume ${volume:>10,.0f}  Failures {failure:>5.2f}%")

        # Final comparison
        click.echo(f"\n{'='*60}")
        click.echo(f"Final Comparison ({window_count} windows processed):")
        comparison = shadow_node.get_comparison()
        for cfg_name, metrics in comparison.items():
            click.echo(f"\n{cfg_name}:")
            for metric, value in metrics.items():
                click.echo(f"  {metric}: {value:,.2f}")

    else:
        # Single processor mode
        click.echo(f"\nFee: {fee} bps ({fee/100:.2f}%)")

        processor = StreamProcessor(
            window=TumblingWindow(size=window_size),
            mapper=mapper,
            fee_bps=fee,
            verbose=verbose,
            checkpoint_dir=checkpoint_dir
        )

        # Add alert rules
        if alert_treasury:
            processor.add_alert(AlertRule.treasury_runway(alert_treasury))
            click.echo(f"📍 Alert: Treasury runway < {alert_treasury} days")

        if alert_failure:
            processor.add_alert(AlertRule.high_failure_rate(alert_failure))
            click.echo(f"📍 Alert: Failure rate > {alert_failure*100:.1f}%")

        if alert_role:
            processor.add_alert(AlertRule.role_imbalance())
            click.echo(f"📍 Alert: Role economic imbalances")

        # Process stream
        click.echo(f"\n🔄 Processing stream...")
        results = processor.ingest_batch(transactions)

        # Summary
        click.echo(f"\n{'='*60}")
        click.echo(f"Streaming Complete")
        click.echo(f"{'='*60}")

        stats = processor.get_stats()
        click.echo(f"Windows processed: {stats['windows_processed']}")
        click.echo(f"Transactions: {stats['transactions_ingested']}")
        click.echo(f"Alerts triggered: {stats['alerts_triggered']}")

        if results:
            last = results[-1]
            if 'result' in last:
                result = last['result']
                click.echo(f"\nFinal Window Metrics:")
                click.echo(f"  Revenue: ${result.get_metric('rev_usdc', 0):,.0f}")
                click.echo(f"  Volume: ${result.get_metric('vol_usdc', 0):,.0f}")
                click.echo(f"  Lab TPS: {result.get_metric('lab_tps', 0):,.0f}")
                click.echo(f"  Failure Rate: {result.get_metric('failure_rate', 0)*100:.2f}%")

        if checkpoint_dir:
            click.echo(f"\n💾 Checkpoints saved to: {checkpoint_dir}")

    click.echo(f"\n{'='*60}\n")


if __name__ == '__main__':
    stream()
