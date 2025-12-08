"""
Sentinel CLI - Protocol sustainability ratings and analysis.
"""
import sys
import json
from pathlib import Path
from typing import Optional

import click

from sentinel_cloud.client import SentinelClient
from sentinel_cloud.protocol_config import ProtocolConfig
from sentinel_cloud.score import calculate_sentinel_score
from sentinel_cloud.proposal import analyze_proposal_impact, ProposalChange
from sentinel_cloud.rankings import generate_rankings, load_protocols_from_directory


@click.group()
@click.version_option(version='1.0.0', prog_name='sentinel')
def app():
    """
    Sentinel - Know your runway.

    Protocol sustainability ratings for crypto.
    """
    pass


@app.command()
@click.argument('config', type=click.Path(exists=True))
@click.option('--output', '-o', type=click.Choice(['text', 'json']), default='text', help='Output format')
@click.option('--verbose', '-v', is_flag=True, help='Show detailed breakdown')
def score(config: str, output: str, verbose: bool):
    """
    Calculate Sentinel Score for a protocol.

    Example:
        sentinel score templates/dao/sample.yaml
    """
    try:
        # Load config
        protocol = ProtocolConfig.from_yaml(config)

        # Calculate score
        result = calculate_sentinel_score(protocol)

        if output == 'json':
            click.echo(json.dumps(result.to_dict(), indent=2))
        else:
            # Text output
            click.echo("=" * 60)
            click.echo(f"SENTINEL SCORE REPORT")
            click.echo("=" * 60)
            click.echo(f"Protocol: {protocol.name}")
            click.echo(f"Type: {protocol.type.value.upper()}")
            click.echo(f"Chain: {protocol.chain}")
            click.echo()

            # Score and grade
            status_emoji = "✅" if result.status == "Healthy" else "⚠️ " if result.status == "Warning" else "🚨"
            click.echo(f"SCORE: {result.total_score}/100 (Grade: {result.grade})")
            click.echo(f"Status: {status_emoji} {result.status.upper()}")
            click.echo()

            # Breakdown
            click.echo("BREAKDOWN")
            click.echo("-" * 60)
            runway_display = f"{result.runway_months:.1f} months" if result.runway_months != float('inf') else "∞ (profitable)"
            click.echo(f"Runway:          {result.runway_score:2d}/40  ({runway_display})")

            ratio_display = f"{result.sustainability_ratio:.2f}" if result.sustainability_ratio != float('inf') else "∞"
            click.echo(f"Sustainability:  {result.sustainability_score:2d}/30  (ratio: {ratio_display})")
            click.echo(f"Diversification: {result.diversification_score:2d}/20")
            click.echo(f"Trajectory:      {result.trajectory_score:2d}/10")
            click.echo()

            # Summary
            click.echo("SUMMARY")
            click.echo("-" * 60)
            click.echo(result.summary)
            click.echo()

            # Recommendations
            if result.recommendations:
                click.echo("TOP RECOMMENDATIONS")
                click.echo("-" * 60)
                for i, rec in enumerate(result.recommendations, 1):
                    click.echo(f"{i}. {rec}")
                click.echo()

            # Metadata
            if verbose:
                click.echo("DETAILS")
                click.echo("-" * 60)
                click.echo(f"Treasury: ${protocol.treasury.balance_usd:,.0f}")
                click.echo(f"Monthly Revenue: ${protocol.monthly_revenue:,.0f}")
                click.echo(f"Monthly Costs: ${protocol.monthly_costs:,.0f}")
                click.echo(f"Monthly Net: ${protocol.monthly_net:,.0f}")
                click.echo()

            if protocol.data_sources:
                click.echo("Data sources: " + ", ".join(protocol.data_sources[:3]))
            if protocol.last_updated:
                click.echo(f"Last updated: {protocol.last_updated}")
            click.echo("=" * 60)

    except Exception as e:
        click.echo(f"Error: {str(e)}", err=True)
        raise click.Abort()


@app.command()
@click.argument('config', type=click.Path(exists=True))
def validate(config: str):
    """
    Validate a protocol config file.

    Example:
        sentinel validate my_protocol.yaml
    """
    try:
        protocol = ProtocolConfig.from_yaml(config)
        click.echo(f"✅ Config is valid!")
        click.echo(f"Protocol: {protocol.name}")
        click.echo(f"Type: {protocol.type.value}")
        click.echo(f"Treasury: ${protocol.treasury.balance_usd:,.0f}")
        click.echo(f"Revenue streams: {len(protocol.revenue_streams)}")
        click.echo(f"Cost streams: {len(protocol.cost_streams)}")
    except Exception as e:
        click.echo(f"❌ Validation failed: {str(e)}", err=True)
        raise click.Abort()


@app.command()
@click.option('--template', type=click.Choice(['dao', 'l2', 'dex']), default='dao')
def init(template: str):
    """
    Generate a template protocol config.

    Example:
        sentinel init --template dao > my_protocol.yaml
    """
    import yaml

    templates = {
        'dao': {
            'name': 'My DAO',
            'type': 'dao',
            'chain': 'ethereum',
            'treasury': {
                'total_usd_override': 10000000,
                'stables_usd_override': 2000000,
            },
            'revenue_streams': [
                {
                    'name': 'protocol_fees',
                    'monthly_usd': 500000,
                    'description': 'Protocol fee revenue',
                }
            ],
            'cost_streams': [
                {
                    'name': 'team',
                    'monthly_usd': 300000,
                    'description': 'Core team',
                },
                {
                    'name': 'grants',
                    'monthly_usd': 500000,
                    'description': 'Grants program',
                    'is_discretionary': True,
                }
            ],
            'data_sources': ['https://example.com'],
            'last_updated': '2025-01-15',
        }
    }

    template_data = templates.get(template, templates['dao'])
    click.echo(yaml.dump(template_data, default_flow_style=False, sort_keys=False))


@app.command(context_settings=dict(ignore_unknown_options=True, allow_extra_args=True))
@click.argument('config', type=click.Path(exists=True))
@click.option('--output', '-o', type=click.Choice(['text', 'json']), default='text', help='Output format')
@click.pass_context
def proposal(ctx, config: str, output: str):
    """
    Analyze impact of a governance proposal on Sentinel Score.

    Example:
        sentinel proposal arbitrum.yaml --add-cost "New Grant: 2000000"
        sentinel proposal dao.yaml --modify-cost "grants: 1500000" --add-revenue "New Product: 500000"
        sentinel proposal protocol.yaml --remove-cost "old_program"

    Options:
        --add-cost "name: amount"        Add a new cost stream
        --add-revenue "name: amount"     Add a new revenue stream
        --modify-cost "name: amount"     Modify existing cost stream
        --modify-revenue "name: amount"  Modify existing revenue stream
        --remove-cost "name"             Remove cost stream
        --remove-revenue "name"          Remove revenue stream
    """
    try:
        # Load base protocol
        protocol = ProtocolConfig.from_yaml(config)

        # Parse proposal changes from extra args
        changes = []
        i = 0
        while i < len(ctx.args):
            arg = ctx.args[i]

            if arg.startswith('--'):
                if i + 1 >= len(ctx.args):
                    click.echo(f"Error: {arg} requires a value", err=True)
                    raise click.Abort()

                value = ctx.args[i + 1]

                try:
                    if arg == '--add-cost':
                        name, amount = _parse_stream_value(value)
                        changes.append(ProposalChange(
                            action="add",
                            stream_type="cost",
                            stream_name=name,
                            new_value=amount,
                        ))
                    elif arg == '--add-revenue':
                        name, amount = _parse_stream_value(value)
                        changes.append(ProposalChange(
                            action="add",
                            stream_type="revenue",
                            stream_name=name,
                            new_value=amount,
                        ))
                    elif arg == '--modify-cost':
                        name, amount = _parse_stream_value(value)
                        changes.append(ProposalChange(
                            action="modify",
                            stream_type="cost",
                            stream_name=name,
                            new_value=amount,
                        ))
                    elif arg == '--modify-revenue':
                        name, amount = _parse_stream_value(value)
                        changes.append(ProposalChange(
                            action="modify",
                            stream_type="revenue",
                            stream_name=name,
                            new_value=amount,
                        ))
                    elif arg == '--remove-cost':
                        changes.append(ProposalChange(
                            action="remove",
                            stream_type="cost",
                            stream_name=value,
                        ))
                    elif arg == '--remove-revenue':
                        changes.append(ProposalChange(
                            action="remove",
                            stream_type="revenue",
                            stream_name=value,
                        ))
                    else:
                        click.echo(f"Error: Unknown option {arg}", err=True)
                        raise click.Abort()
                except ValueError as e:
                    click.echo(f"Error: {str(e)}", err=True)
                    raise click.Abort()

                i += 2
            else:
                i += 1

        if not changes:
            click.echo("Error: No proposal changes specified. Use --add-cost, --modify-cost, etc.", err=True)
            raise click.Abort()

        # Analyze impact
        result = analyze_proposal_impact(protocol, changes)

        if output == 'json':
            click.echo(json.dumps(result.to_dict(), indent=2))
        else:
            # Text output
            click.echo("=" * 60)
            click.echo("PROPOSAL IMPACT ANALYSIS")
            click.echo("=" * 60)
            click.echo(f"Protocol: {protocol.name}")
            click.echo()

            # Show proposed changes
            click.echo("PROPOSED CHANGES")
            click.echo("-" * 60)
            for change in changes:
                action_verb = change.action.upper()
                stream_type = change.stream_type.upper()
                if change.action in ["add", "modify"]:
                    click.echo(f"{action_verb} {stream_type}: {change.stream_name} = ${change.new_value:,.0f}/mo")
                else:
                    click.echo(f"{action_verb} {stream_type}: {change.stream_name}")
            click.echo()

            # Before/After comparison
            click.echo("SCORE IMPACT")
            click.echo("-" * 60)
            click.echo(f"Before: {result.before_score.total_score}/100 (Grade {result.before_score.grade}) - {result.before_score.status}")
            click.echo(f"After:  {result.after_score.total_score}/100 (Grade {result.after_score.grade}) - {result.after_score.status}")

            change_symbol = "+" if result.score_change >= 0 else ""
            click.echo(f"Change: {change_symbol}{result.score_change} points")
            click.echo()

            # Key metrics
            click.echo("KEY METRICS")
            click.echo("-" * 60)

            before_runway = f"{result.before_score.runway_months:.1f} months" if result.before_score.runway_months != float('inf') else "∞ (profitable)"
            after_runway = f"{result.after_score.runway_months:.1f} months" if result.after_score.runway_months != float('inf') else "∞ (profitable)"
            click.echo(f"Runway:         {before_runway} → {after_runway}")

            before_ratio = f"{result.before_score.sustainability_ratio:.2f}" if result.before_score.sustainability_ratio != float('inf') else "∞"
            after_ratio = f"{result.after_score.sustainability_ratio:.2f}" if result.after_score.sustainability_ratio != float('inf') else "∞"
            click.echo(f"Sustainability: {before_ratio} → {after_ratio}")
            click.echo()

            # Warnings
            if result.warnings:
                click.echo("⚠️  WARNINGS")
                click.echo("-" * 60)
                for warning in result.warnings:
                    click.echo(f"  {warning}")
                click.echo()

            # Recommendations
            if result.recommendations:
                click.echo("RECOMMENDATIONS")
                click.echo("-" * 60)
                for i, rec in enumerate(result.recommendations, 1):
                    click.echo(f"{i}. {rec}")
                click.echo()

            # Alternatives
            if result.alternatives:
                click.echo("ALTERNATIVES TO CONSIDER")
                click.echo("-" * 60)
                for i, alt in enumerate(result.alternatives, 1):
                    click.echo(f"{i}. {alt}")
                click.echo()

            click.echo("=" * 60)

    except Exception as e:
        click.echo(f"Error: {str(e)}", err=True)
        raise click.Abort()


def _parse_stream_value(value: str) -> tuple[str, float]:
    """Parse 'name: amount' format."""
    if ':' in value:
        parts = value.split(':', 1)
        name = parts[0].strip()
        amount = float(parts[1].strip())
        return name, amount
    else:
        raise ValueError(f"Invalid format: {value}. Expected 'name: amount'")


@app.command()
@click.argument('directory', type=click.Path(exists=True))
@click.option('--output', '-o', type=click.Choice(['text', 'json', 'html', 'markdown']), default='text', help='Output format')
@click.option('--output-file', type=click.Path(), help='Output file path')
@click.option('--title', default='Sentinel Protocol Rankings', help='Rankings title')
def rankings(directory: str, output: str, output_file: Optional[str], title: str):
    """
    Generate rankings from multiple protocol configs.

    Example:
        sentinel rankings protocols/
        sentinel rankings protocols/ --output html --output-file rankings.html
        sentinel rankings protocols/ --output markdown > rankings.md
    """
    try:
        from datetime import datetime
        from pathlib import Path

        # Load all protocols from directory
        protocols = load_protocols_from_directory(Path(directory))

        if not protocols:
            click.echo(f"Error: No protocol configs found in {directory}", err=True)
            raise click.Abort()

        # Generate rankings
        last_updated = datetime.now().strftime("%Y-%m-%d")
        ranks = generate_rankings(
            protocols,
            title=title,
            description=f"Comparing {len(protocols)} protocols",
            last_updated=last_updated,
        )

        # Output
        if output == 'json':
            content = ranks.to_json()
        elif output == 'html':
            content = ranks.to_html()
        elif output == 'markdown':
            content = ranks.to_markdown()
        else:
            # Text output
            content = []
            content.append("=" * 60)
            content.append(title.upper())
            content.append("=" * 60)
            content.append(f"Comparing {len(protocols)} protocols")
            content.append("")
            content.append(f"{'Rank':<6} {'Protocol':<20} {'Score':<10} {'Grade':<7} {'Status':<12} {'Runway':<12}")
            content.append("-" * 60)

            for p in ranks.protocols:
                runway = f"{p.score.runway_months:.0f}mo" if p.score.runway_months != float('inf') else "∞"
                status_emoji = "✅" if p.score.status == "Healthy" else "⚠️" if p.score.status == "Warning" else "🚨"

                content.append(
                    f"{p.rank:<6} {p.protocol.name:<20} {p.score.total_score:<10} "
                    f"{p.score.grade:<7} {status_emoji} {p.score.status:<10} {runway:<12}"
                )

            content.append("=" * 60)
            content = "\n".join(content)

        # Write to file or stdout
        if output_file:
            with open(output_file, 'w') as f:
                f.write(content)
            click.echo(f"Rankings written to {output_file}")
        else:
            click.echo(content)

    except Exception as e:
        click.echo(f"Error: {str(e)}", err=True)
        raise click.Abort()


if __name__ == '__main__':
    app()
