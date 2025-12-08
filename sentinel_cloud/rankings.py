"""
Protocol rankings and comparisons for Sentinel.

Generate rankings tables from multiple protocol scores.
"""
from dataclasses import dataclass
from typing import Optional
from pathlib import Path
import json

from .protocol_config import ProtocolConfig
from .score import calculate_sentinel_score, SentinelScoreResult


@dataclass
class ProtocolRanking:
    """Single protocol entry in rankings."""
    protocol: ProtocolConfig
    score: SentinelScoreResult
    rank: int


@dataclass
class Rankings:
    """Rankings of multiple protocols."""
    protocols: list[ProtocolRanking]
    title: str = "Sentinel Protocol Rankings"
    description: str = "Protocol sustainability ratings"
    last_updated: str = ""

    def to_dict(self) -> dict:
        """Export rankings as dictionary."""
        return {
            'title': self.title,
            'description': self.description,
            'last_updated': self.last_updated,
            'protocols': [
                {
                    'rank': p.rank,
                    'name': p.protocol.name,
                    'type': p.protocol.type.value,
                    'chain': p.protocol.chain,
                    'score': p.score.total_score,
                    'grade': p.score.grade,
                    'status': p.score.status,
                    'runway_months': p.score.runway_months if p.score.runway_months != float('inf') else None,
                    'sustainability_ratio': p.score.sustainability_ratio if p.score.sustainability_ratio != float('inf') else None,
                    'treasury_usd': p.protocol.treasury.balance_usd,
                    'monthly_revenue': p.protocol.monthly_revenue,
                    'monthly_costs': p.protocol.monthly_costs,
                    'website': p.protocol.website,
                }
                for p in self.protocols
            ]
        }

    def to_json(self, path: Optional[str] = None) -> str:
        """Export rankings as JSON."""
        data = self.to_dict()
        json_str = json.dumps(data, indent=2)

        if path:
            with open(path, 'w') as f:
                f.write(json_str)

        return json_str

    def to_markdown(self) -> str:
        """Generate markdown table of rankings."""
        lines = [
            f"# {self.title}",
            "",
            self.description,
            "",
            "| Rank | Protocol | Type | Score | Grade | Status | Runway | Sustainability |",
            "|------|----------|------|-------|-------|--------|--------|----------------|",
        ]

        for p in self.protocols:
            runway = f"{p.score.runway_months:.0f}mo" if p.score.runway_months != float('inf') else "∞"
            sustainability = f"{p.score.sustainability_ratio:.2f}" if p.score.sustainability_ratio != float('inf') else "∞"

            status_emoji = "✅" if p.score.status == "Healthy" else "⚠️" if p.score.status == "Warning" else "🚨"

            lines.append(
                f"| {p.rank} | {p.protocol.name} | {p.protocol.type.value} | "
                f"{p.score.total_score}/100 | {p.score.grade} | {status_emoji} {p.score.status} | "
                f"{runway} | {sustainability} |"
            )

        lines.extend([
            "",
            "## Legend",
            "",
            "- **Score**: 0-100 composite score (higher is better)",
            "- **Grade**: S (90+), A (80+), B (70+), C (55+), D (40+), F (<40)",
            "- **Status**: ✅ Healthy (70+) | ⚠️ Warning (45-69) | 🚨 Critical (<45)",
            "- **Runway**: Months until treasury depletion at current burn rate",
            "- **Sustainability**: Revenue/Cost ratio (1.0 = break-even)",
            "",
        ])

        if self.last_updated:
            lines.append(f"*Last updated: {self.last_updated}*")

        return "\n".join(lines)

    def to_html(self) -> str:
        """Generate HTML rankings page."""
        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{self.title}</title>
    <style>
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}

        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            padding: 2rem;
        }}

        .container {{
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            border-radius: 12px;
            box-shadow: 0 20px 60px rgba(0,0,0,0.3);
            overflow: hidden;
        }}

        header {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 3rem 2rem;
            text-align: center;
        }}

        header h1 {{
            font-size: 2.5rem;
            margin-bottom: 0.5rem;
            font-weight: 700;
        }}

        header p {{
            font-size: 1.1rem;
            opacity: 0.9;
        }}

        .content {{
            padding: 2rem;
        }}

        table {{
            width: 100%;
            border-collapse: collapse;
            margin: 2rem 0;
        }}

        th {{
            background: #f8f9fa;
            color: #333;
            font-weight: 600;
            text-align: left;
            padding: 1rem;
            border-bottom: 2px solid #dee2e6;
        }}

        td {{
            padding: 1rem;
            border-bottom: 1px solid #e9ecef;
        }}

        tr:hover {{
            background: #f8f9fa;
        }}

        .rank {{
            font-size: 1.5rem;
            font-weight: 700;
            color: #667eea;
        }}

        .grade {{
            display: inline-block;
            padding: 0.25rem 0.75rem;
            border-radius: 4px;
            font-weight: 600;
        }}

        .grade-S {{
            background: #d4edda;
            color: #155724;
        }}

        .grade-A {{
            background: #d1ecf1;
            color: #0c5460;
        }}

        .grade-B {{
            background: #fff3cd;
            color: #856404;
        }}

        .grade-C {{
            background: #f8d7da;
            color: #721c24;
        }}

        .grade-D, .grade-F {{
            background: #f5c6cb;
            color: #721c24;
        }}

        .status-Healthy {{
            color: #28a745;
        }}

        .status-Warning {{
            color: #ffc107;
        }}

        .status-Critical {{
            color: #dc3545;
        }}

        .score {{
            font-size: 1.2rem;
            font-weight: 600;
        }}

        .badge {{
            display: inline-block;
            padding: 0.25rem 0.5rem;
            border-radius: 3px;
            font-size: 0.875rem;
            background: #e9ecef;
            color: #495057;
        }}

        footer {{
            background: #f8f9fa;
            padding: 2rem;
            text-align: center;
            color: #6c757d;
            border-top: 1px solid #dee2e6;
        }}

        .legend {{
            background: #f8f9fa;
            padding: 1.5rem;
            border-radius: 8px;
            margin: 2rem 0;
        }}

        .legend h3 {{
            margin-bottom: 1rem;
            color: #333;
        }}

        .legend ul {{
            list-style: none;
            padding-left: 1rem;
        }}

        .legend li {{
            margin: 0.5rem 0;
        }}

        @media (max-width: 768px) {{
            body {{
                padding: 1rem;
            }}

            header h1 {{
                font-size: 1.75rem;
            }}

            table {{
                font-size: 0.875rem;
            }}

            th, td {{
                padding: 0.5rem;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <header>
            <h1>{self.title}</h1>
            <p>{self.description}</p>
        </header>

        <div class="content">
            <table>
                <thead>
                    <tr>
                        <th>Rank</th>
                        <th>Protocol</th>
                        <th>Type</th>
                        <th>Score</th>
                        <th>Grade</th>
                        <th>Status</th>
                        <th>Runway</th>
                        <th>Sustainability</th>
                    </tr>
                </thead>
                <tbody>
"""

        for p in self.protocols:
            runway = f"{p.score.runway_months:.0f}mo" if p.score.runway_months != float('inf') else "∞"
            sustainability = f"{p.score.sustainability_ratio:.2f}" if p.score.sustainability_ratio != float('inf') else "∞"
            status_emoji = "✅" if p.score.status == "Healthy" else "⚠️" if p.score.status == "Warning" else "🚨"

            html += f"""                    <tr>
                        <td class="rank">{p.rank}</td>
                        <td><strong>{p.protocol.name}</strong></td>
                        <td><span class="badge">{p.protocol.type.value}</span></td>
                        <td class="score">{p.score.total_score}/100</td>
                        <td><span class="grade grade-{p.score.grade}">{p.score.grade}</span></td>
                        <td class="status-{p.score.status}">{status_emoji} {p.score.status}</td>
                        <td>{runway}</td>
                        <td>{sustainability}</td>
                    </tr>
"""

        html += """                </tbody>
            </table>

            <div class="legend">
                <h3>Legend</h3>
                <ul>
                    <li><strong>Score:</strong> 0-100 composite score (higher is better)</li>
                    <li><strong>Grade:</strong> S (90+), A (80+), B (70+), C (55+), D (40+), F (&lt;40)</li>
                    <li><strong>Status:</strong> ✅ Healthy (70+) | ⚠️ Warning (45-69) | 🚨 Critical (&lt;45)</li>
                    <li><strong>Runway:</strong> Months until treasury depletion at current burn rate</li>
                    <li><strong>Sustainability:</strong> Revenue/Cost ratio (1.0 = break-even)</li>
                </ul>
            </div>
        </div>

        <footer>
"""

        if self.last_updated:
            html += f"            <p>Last updated: {self.last_updated}</p>\n"

        html += """            <p>Generated by <strong>Sentinel</strong> - Know your runway</p>
        </footer>
    </div>
</body>
</html>
"""

        return html


def generate_rankings(
    protocols: list[ProtocolConfig],
    title: str = "Sentinel Protocol Rankings",
    description: str = "Protocol sustainability ratings",
    last_updated: str = "",
) -> Rankings:
    """
    Generate rankings from multiple protocols.

    Args:
        protocols: List of ProtocolConfig objects
        title: Rankings title
        description: Rankings description
        last_updated: Last updated date

    Returns:
        Rankings object
    """
    # Calculate scores for all protocols
    scored = []
    for protocol in protocols:
        score = calculate_sentinel_score(protocol)
        scored.append((protocol, score))

    # Sort by total score (descending)
    scored.sort(key=lambda x: x[1].total_score, reverse=True)

    # Assign ranks
    rankings = []
    for rank, (protocol, score) in enumerate(scored, start=1):
        rankings.append(ProtocolRanking(
            protocol=protocol,
            score=score,
            rank=rank,
        ))

    return Rankings(
        protocols=rankings,
        title=title,
        description=description,
        last_updated=last_updated,
    )


def load_protocols_from_directory(directory: Path) -> list[ProtocolConfig]:
    """
    Load all protocol configs from a directory.

    Args:
        directory: Directory containing YAML protocol configs

    Returns:
        List of ProtocolConfig objects
    """
    protocols = []

    if not directory.exists():
        return protocols

    for yaml_file in directory.glob("*.yaml"):
        try:
            protocol = ProtocolConfig.from_yaml(yaml_file)
            protocols.append(protocol)
        except Exception as e:
            print(f"Warning: Failed to load {yaml_file}: {e}")

    return protocols
