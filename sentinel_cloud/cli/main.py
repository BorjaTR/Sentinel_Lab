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
@click.argument('protocol1', type=click.Path(exists=True))
@click.argument('protocol2', type=click.Path(exists=True))
@click.option('--output', '-o', type=click.Choice(['text', 'json']), default='text', help='Output format')
def compare(protocol1: str, protocol2: str, output: str):
    """
    Compare two protocols side-by-side.

    Example:
        sentinel compare arbitrum.yaml optimism.yaml
        sentinel compare dao1.yaml dao2.yaml --output json
    """
    try:
        # Load both protocols
        p1 = ProtocolConfig.from_yaml(protocol1)
        p2 = ProtocolConfig.from_yaml(protocol2)

        # Calculate scores
        s1 = calculate_sentinel_score(p1)
        s2 = calculate_sentinel_score(p2)

        if output == 'json':
            comparison = {
                'protocol1': {
                    'name': p1.name,
                    'score': s1.to_dict(),
                    'treasury': p1.treasury.balance_usd,
                    'monthly_revenue': p1.monthly_revenue,
                    'monthly_costs': p1.monthly_costs,
                },
                'protocol2': {
                    'name': p2.name,
                    'score': s2.to_dict(),
                    'treasury': p2.treasury.balance_usd,
                    'monthly_revenue': p2.monthly_revenue,
                    'monthly_costs': p2.monthly_costs,
                },
                'differences': {
                    'score_delta': s2.total_score - s1.total_score,
                    'runway_delta': s2.runway_months - s1.runway_months if s1.runway_months != float('inf') and s2.runway_months != float('inf') else None,
                }
            }
            click.echo(json.dumps(comparison, indent=2))
        else:
            # Text comparison
            click.echo("=" * 80)
            click.echo("PROTOCOL COMPARISON")
            click.echo("=" * 80)
            click.echo()

            # Names and types
            click.echo(f"{'':20} {p1.name:^28} {p2.name:^28}")
            click.echo("-" * 80)
            click.echo(f"{'Type':20} {p1.type.value:^28} {p2.type.value:^28}")
            click.echo(f"{'Chain':20} {p1.chain:^28} {p2.chain:^28}")
            click.echo()

            # Scores
            click.echo("SENTINEL SCORES")
            click.echo("-" * 80)
            click.echo(f"{'Total Score':20} {f'{s1.total_score}/100':^28} {f'{s2.total_score}/100':^28}")
            click.echo(f"{'Grade':20} {s1.grade:^28} {s2.grade:^28}")
            click.echo(f"{'Status':20} {s1.status:^28} {s2.status:^28}")
            click.echo()

            # Component breakdown
            click.echo("COMPONENT BREAKDOWN")
            click.echo("-" * 80)
            click.echo(f"{'Runway Score':20} {f'{s1.runway_score}/40':^28} {f'{s2.runway_score}/40':^28}")
            click.echo(f"{'Sustainability':20} {f'{s1.sustainability_score}/30':^28} {f'{s2.sustainability_score}/30':^28}")
            click.echo(f"{'Diversification':20} {f'{s1.diversification_score}/20':^28} {f'{s2.diversification_score}/20':^28}")
            click.echo(f"{'Trajectory':20} {f'{s1.trajectory_score}/10':^28} {f'{s2.trajectory_score}/10':^28}")
            click.echo()

            # Key metrics
            click.echo("KEY METRICS")
            click.echo("-" * 80)

            r1 = f"{s1.runway_months:.0f}mo" if s1.runway_months != float('inf') else "∞"
            r2 = f"{s2.runway_months:.0f}mo" if s2.runway_months != float('inf') else "∞"
            click.echo(f"{'Runway':20} {r1:^28} {r2:^28}")

            ratio1 = f"{s1.sustainability_ratio:.2f}" if s1.sustainability_ratio != float('inf') else "∞"
            ratio2 = f"{s2.sustainability_ratio:.2f}" if s2.sustainability_ratio != float('inf') else "∞"
            click.echo(f"{'Sustainability':20} {ratio1:^28} {ratio2:^28}")

            t1 = f"${p1.treasury.balance_usd:,.0f}"
            t2 = f"${p2.treasury.balance_usd:,.0f}"
            click.echo(f"{'Treasury':20} {t1:^28} {t2:^28}")

            rev1 = f"${p1.monthly_revenue:,.0f}/mo"
            rev2 = f"${p2.monthly_revenue:,.0f}/mo"
            click.echo(f"{'Revenue':20} {rev1:^28} {rev2:^28}")

            cost1 = f"${p1.monthly_costs:,.0f}/mo"
            cost2 = f"${p2.monthly_costs:,.0f}/mo"
            click.echo(f"{'Costs':20} {cost1:^28} {cost2:^28}")
            click.echo()

            # Winner
            if s1.total_score > s2.total_score:
                click.echo(f"✅ {p1.name} has a stronger sustainability profile (+{s1.total_score - s2.total_score} points)")
            elif s2.total_score > s1.total_score:
                click.echo(f"✅ {p2.name} has a stronger sustainability profile (+{s2.total_score - s1.total_score} points)")
            else:
                click.echo("🤝 Both protocols have equal sustainability scores")

            click.echo("=" * 80)

    except Exception as e:
        click.echo(f"Error: {str(e)}", err=True)
        raise click.Abort()


@app.command()
@click.argument('directory', type=click.Path(exists=True))
@click.option('--output-file', '-o', type=click.Path(), required=True, help='Output CSV file path')
def export(directory: str, output_file: str):
    """
    Export scores from multiple protocols to CSV.

    Example:
        sentinel export protocols/ --output-file scores.csv
    """
    try:
        from pathlib import Path
        import csv

        # Load all protocols
        protocols = load_protocols_from_directory(Path(directory))

        if not protocols:
            click.echo(f"Error: No protocol configs found in {directory}", err=True)
            raise click.Abort()

        # Calculate scores for all
        results = []
        for protocol in protocols:
            score = calculate_sentinel_score(protocol)
            results.append({
                'name': protocol.name,
                'type': protocol.type.value,
                'chain': protocol.chain,
                'total_score': score.total_score,
                'grade': score.grade,
                'status': score.status,
                'runway_score': score.runway_score,
                'sustainability_score': score.sustainability_score,
                'diversification_score': score.diversification_score,
                'trajectory_score': score.trajectory_score,
                'runway_months': score.runway_months if score.runway_months != float('inf') else None,
                'sustainability_ratio': score.sustainability_ratio if score.sustainability_ratio != float('inf') else None,
                'treasury_usd': protocol.treasury.balance_usd,
                'monthly_revenue': protocol.monthly_revenue,
                'monthly_costs': protocol.monthly_costs,
                'monthly_net': protocol.monthly_net,
                'revenue_streams': len(protocol.revenue_streams),
                'cost_streams': len(protocol.cost_streams),
                'stables_ratio': protocol.treasury.stables_ratio,
            })

        # Sort by score
        results.sort(key=lambda x: x['total_score'], reverse=True)

        # Write CSV
        with open(output_file, 'w', newline='') as f:
            fieldnames = [
                'name', 'type', 'chain', 'total_score', 'grade', 'status',
                'runway_score', 'sustainability_score', 'diversification_score', 'trajectory_score',
                'runway_months', 'sustainability_ratio',
                'treasury_usd', 'monthly_revenue', 'monthly_costs', 'monthly_net',
                'revenue_streams', 'cost_streams', 'stables_ratio'
            ]
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(results)

        click.echo(f"✅ Exported {len(results)} protocols to {output_file}")

    except Exception as e:
        click.echo(f"Error: {str(e)}", err=True)
        raise click.Abort()


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
