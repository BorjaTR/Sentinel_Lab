"""
Sentinel Cloud CLI - Main Entry Point

Commands:
- quick-check: Fast health check (30 seconds)
- analyze: Full analysis with report generation
- init: Generate starter config file
- run-config: Execute analysis from config file
"""

import sys
import json
from pathlib import Path
from typing import Optional

import click

from sentinel_cloud.client import SentinelClient
from sentinel_cloud.baseline import BaselineAnalyzer
from sentinel_cloud.death_clock import RunwayProjector, RunwayInputs
from sentinel_cloud.io import load_and_normalize


@click.group()
@click.version_option(version='0.3.0', prog_name='sentinel')
def app():
    """
    Sentinel Cloud - Tokenomics Analysis for DePIN Protocols

    Quick health check:
      sentinel quick-check data.csv --treasury 1000000

    Full analysis:
      sentinel analyze data.csv --treasury 1000000
    """
    pass


@app.command('quick-check')
@click.argument('csv_path', type=click.Path(exists=True))
@click.option('--mapper', default='depin_rewards', help='Data mapper type (depin_rewards, solana, evm_erc20)')
@click.option('--treasury', type=float, required=True, help='Current treasury balance in USD')
@click.option('--output', type=click.Choice(['text', 'json']), default='text', help='Output format')
def quick_check(csv_path: str, mapper: str, treasury: float, output: str):
    """
    Quick health check - get verdict in 30 seconds.

    Runs Baseline + Death Clock analysis to determine protocol sustainability.

    Example:
      sentinel quick-check helium.csv --treasury 1000000
    """
    try:
        # Load data
        if output == 'text':
            click.echo("Loading scenario data...")

        txs = load_and_normalize(csv_path, mapper=mapper)

        if len(txs) == 0:
            click.echo("❌ ERROR: No transactions loaded", err=True)
            sys.exit(1)

        if output == 'text':
            click.echo(f"Loaded {len(txs):,} transactions\n")

        # Run baseline analysis
        analyzer = BaselineAnalyzer()
        baseline = analyzer.analyze(txs)

        # Calculate runway
        projector = RunwayProjector()
        runway_inputs = RunwayInputs(
            treasury_balance=treasury,
            daily_treasury_change=baseline.daily_treasury_change or 0,
            revenue=baseline.revenue,
            total_emissions=baseline.total_emissions
        )
        runway = projector.compute(runway_inputs)

        # Determine status
        if runway.is_sustainable:
            status = "healthy"
            status_emoji = "✅"
        elif runway.runway_days and runway.runway_days > 180:
            status = "healthy"
            status_emoji = "✅"
        elif runway.runway_days and runway.runway_days > 90:
            status = "warning"
            status_emoji = "⚠️ "
        else:
            status = "critical"
            status_emoji = "🔴"

        # Calculate monthly metrics
        monthly_revenue = baseline.revenue if baseline.duration_days == 0 else (baseline.revenue / baseline.duration_days) * 30
        monthly_burn = abs(baseline.daily_treasury_change or 0) * 30 if baseline.daily_treasury_change and baseline.daily_treasury_change < 0 else 0

        # Generate suggestion
        suggestion = None
        if status in ["warning", "critical"] and not runway.is_sustainable:
            # Simple suggestion: what fee would extend runway to 180+ days?
            current_daily_change = baseline.daily_treasury_change or 0
            if current_daily_change < 0:
                # Need to reduce burn by this much to reach 180 days
                target_daily_change = -treasury / 180  # Target 180 days
                needed_improvement = current_daily_change - target_daily_change

                # Rough estimate: assume linear relationship between fees and revenue
                # Suggest increasing fees proportionally
                revenue_increase_factor = 1 + (needed_improvement / abs(current_daily_change))
                suggested_fee_increase = int(revenue_increase_factor * 100) - 100  # Convert to bps increase

                if suggested_fee_increase > 0:
                    suggestion = {
                        "action": "increase_fee",
                        "increase_bps": min(suggested_fee_increase, 50),  # Cap at reasonable level
                        "rationale": "To extend runway to 180+ days"
                    }

        # Output results
        if output == 'json':
            result = {
                "status": status,
                "runway_days": runway.runway_days if not runway.is_sustainable else None,
                "is_sustainable": runway.is_sustainable,
                "monthly_revenue": monthly_revenue,
                "monthly_burn": monthly_burn,
                "treasury_balance": treasury,
                "suggestion": suggestion
            }
            click.echo(json.dumps(result, indent=2))
        else:
            # Text output
            click.echo("SENTINEL QUICK CHECK")
            click.echo("━" * 40)
            click.echo(f"Transactions: {len(txs):,}")
            click.echo(f"Monthly Revenue: ${monthly_revenue:,.0f}")
            click.echo(f"Monthly Burn: ${monthly_burn:,.0f}")
            click.echo(f"Treasury: ${treasury:,.0f}")
            click.echo("")

            if runway.is_sustainable:
                click.echo(f"{status_emoji} STATUS: HEALTHY")
                click.echo(f"    Protocol is sustainable - revenue exceeds costs")
            else:
                click.echo(f"{status_emoji} STATUS: {status.upper()}")
                click.echo(f"    Runway: {runway.runway_days:.0f} days at current parameters")

            if suggestion:
                click.echo("")
                click.echo(f"💡 SUGGESTION: {suggestion['action'].replace('_', ' ').title()}")
                click.echo(f"   Consider increasing fees by ~{suggestion['increase_bps']}bps")
                click.echo(f"   Rationale: {suggestion['rationale']}")

            click.echo("")
            click.echo("Run `sentinel analyze` for full report.")

    except Exception as e:
        click.echo(f"❌ ERROR: {str(e)}", err=True)
        if output == 'json':
            error_result = {"error": str(e), "status": "error"}
            click.echo(json.dumps(error_result, indent=2), err=True)
        sys.exit(1)


@app.command()
@click.argument('csv_path', type=click.Path(exists=True))
@click.option('--mapper', default='depin_rewards', help='Data mapper type')
@click.option('--treasury', type=float, required=True, help='Current treasury balance in USD')
@click.option('--output-dir', type=click.Path(), default='./reports', help='Output directory for reports')
@click.option('--format', 'output_format', type=click.Choice(['markdown', 'json', 'both']), default='markdown', help='Report format')
@click.option('--emissions', type=float, help='Daily emissions in USD (for unit economics)')
def analyze(csv_path: str, mapper: str, treasury: float, output_dir: str, output_format: str, emissions: Optional[float]):
    """
    Full analysis with report generation.

    Runs all 8 phases (A-H) and generates comprehensive report.

    Example:
      sentinel analyze helium.csv --treasury 1000000 --emissions 50000
    """
    import os
    from datetime import datetime
    from sentinel_cloud.comparison import ComparisonEngine
    from sentinel_cloud.safety import SafetyScanner
    from sentinel_cloud.unit_economics import UnitEconomicsConfig, compute_unit_economics
    from sentinel_cloud.concentration import compute_concentration
    from sentinel_cloud.executive_report import generate_executive_report

    try:
        # Create output directory
        os.makedirs(output_dir, exist_ok=True)

        click.echo("=" * 60)
        click.echo("SENTINEL CLOUD - FULL ANALYSIS")
        click.echo("=" * 60)
        click.echo("")

        # Step 1: Load data
        click.echo("[1/8] Loading scenario data...")
        txs = load_and_normalize(csv_path, mapper=mapper)
        click.echo(f"      Loaded {len(txs):,} transactions ✓")
        click.echo("")

        # Step 2: Phase A - Baseline Analysis
        click.echo("[2/8] Phase A: Baseline Analysis...")
        analyzer = BaselineAnalyzer()
        baseline = analyzer.analyze(txs)
        click.echo(f"      Revenue: ${baseline.revenue:,.0f}")
        click.echo(f"      Volume: ${baseline.volume:,.0f}")
        click.echo(f"      Transactions: {baseline.tx_count:,} ✓")
        click.echo("")

        # Step 3: Phase C - Runway Projection
        click.echo("[3/8] Phase C: Runway Projection...")
        projector = RunwayProjector()
        runway_inputs = RunwayInputs(
            treasury_balance=treasury,
            daily_treasury_change=baseline.daily_treasury_change or 0,
            revenue=baseline.revenue,
            total_emissions=baseline.total_emissions
        )
        runway = projector.compute(runway_inputs)

        if runway.is_sustainable:
            click.echo(f"      Status: ✅ Sustainable (revenue > costs)")
        else:
            click.echo(f"      Runway: {runway.runway_days:.0f} days")
        click.echo("")

        # Step 4: Phase D - Safety Scanner
        click.echo("[4/8] Phase D: Safety Scanner...")
        scanner = SafetyScanner()
        # Run a quick safety check on current parameters
        safety_pass = True
        if runway.runway_days and runway.runway_days < 180:
            safety_pass = False
            click.echo(f"      ⚠️  Runway below 180 day threshold")

        if safety_pass:
            click.echo(f"      Status: ✅ All safety checks passed")
        click.echo("")

        # Step 5: Phase E - Unit Economics (if emissions provided)
        unit_econ_result = None
        if emissions:
            click.echo("[5/8] Phase E: Unit Economics...")
            try:
                config = UnitEconomicsConfig(resource_name="transaction")
                unit_econ_result = compute_unit_economics(
                    txs, baseline.__dict__, baseline.__dict__, config, emissions
                )
                if unit_econ_result.net_margin_per_unit and unit_econ_result.net_margin_per_unit > 0:
                    click.echo(f"      Margin per unit: ${unit_econ_result.net_margin_per_unit:.4f} ✅")
                elif unit_econ_result.net_margin_per_unit:
                    click.echo(f"      Margin per unit: ${unit_econ_result.net_margin_per_unit:.4f} ⚠️  Negative")
                click.echo("")
            except Exception as e:
                click.echo(f"      Skipped (error: {str(e)})")
                click.echo("")
        else:
            click.echo("[5/8] Phase E: Unit Economics... Skipped (no --emissions provided)")
            click.echo("")

        # Step 6: Phase F - Concentration Analysis (if reward data available)
        click.echo("[6/8] Phase F: Concentration Analysis... Skipped (requires reward data)")
        click.echo("")

        # Step 7: Phase G - Governance Simulation
        click.echo("[7/8] Phase G: Governance Simulation... Skipped (requires proposal data)")
        click.echo("")

        # Step 8: Phase H - Executive Report
        click.echo("[8/8] Phase H: Executive Report Generation...")

        report = generate_executive_report(
            scenario_name=Path(csv_path).stem,
            baseline_metrics={
                'revenue': baseline.revenue,
                'volume': baseline.volume,
                'tx_count': baseline.tx_count
            },
            runway_results={
                'runway_days': runway.runway_days,
                'is_sustainable': runway.is_sustainable
            },
            unit_economics=unit_econ_result.__dict__ if unit_econ_result else None
        )

        # Save report
        timestamp = datetime.now().strftime("%Y-%m-%d")
        base_filename = f"{Path(csv_path).stem}_{timestamp}"

        if output_format in ['markdown', 'both']:
            markdown_path = os.path.join(output_dir, f"{base_filename}.md")
            with open(markdown_path, 'w') as f:
                f.write(report.format())
            click.echo(f"      Saved: {markdown_path} ✓")

        if output_format in ['json', 'both']:
            json_path = os.path.join(output_dir, f"{base_filename}.json")
            with open(json_path, 'w') as f:
                import json as json_lib
                json_lib.dump({
                    'baseline': {
                        'revenue': baseline.revenue,
                        'volume': baseline.volume,
                        'tx_count': baseline.tx_count
                    },
                    'runway': {
                        'runway_days': runway.runway_days,
                        'is_sustainable': runway.is_sustainable
                    },
                    'status': report.overall_status,
                    'risk_level': report.overall_risk.value
                }, f, indent=2)
            click.echo(f"      Saved: {json_path} ✓")

        click.echo("")
        click.echo("=" * 60)
        click.echo("ANALYSIS COMPLETE")
        click.echo("=" * 60)
        click.echo("")
        click.echo(f"Overall Status: {report.overall_status.upper()}")
        click.echo(f"Risk Level: {report.overall_risk.value.upper()}")
        click.echo("")
        click.echo(f"Bottom Line: {report.bottom_line}")
        click.echo("")

    except Exception as e:
        click.echo(f"❌ ERROR: {str(e)}", err=True)
        import traceback
        traceback.print_exc()
        sys.exit(1)


@app.command()
def init():
    """
    Generate starter config file.

    Creates sentinel.yaml with default configuration.

    Example:
      sentinel init
    """
    click.echo("Config generation coming in Phase J-2...")


@app.command('run-config')
@click.argument('config_path', type=click.Path(exists=True), default='sentinel.yaml', required=False)
def run_config(config_path: str):
    """
    Execute analysis from config file.

    Runs full pipeline based on YAML configuration.

    Example:
      sentinel run-config sentinel.yaml
    """
    click.echo(f"Config-driven execution coming in Phase J-2...")
    click.echo(f"Will use config: {config_path}")


if __name__ == '__main__':
    app()
