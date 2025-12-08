"""
Example 3: Generate Protocol Rankings

This example shows how to load multiple protocols and generate rankings
in different formats (HTML, JSON, Markdown).
"""

from pathlib import Path
from sentinel_cloud.rankings import load_protocols_from_directory, generate_rankings


def main():
    # Load all DAO protocols
    protocols = load_protocols_from_directory(Path("templates/dao"))

    print(f"Loaded {len(protocols)} protocols")
    print()

    # Generate rankings
    rankings = generate_rankings(
        protocols,
        title="Sample DAO Rankings",
        description="Comparing DAO sustainability metrics",
        last_updated="2025-01-15"
    )

    # Display text summary
    print("RANKINGS:")
    print("-" * 60)
    for p in rankings.protocols:
        status_emoji = "✅" if p.score.status == "Healthy" else "⚠️" if p.score.status == "Warning" else "🚨"
        runway = f"{p.score.runway_months:.0f}mo" if p.score.runway_months != float('inf') else "∞"
        print(f"{p.rank}. {p.protocol.name:30} {p.score.total_score:3d}/100 (Grade {p.score.grade}) {status_emoji} {runway}")
    print()

    # Export to different formats
    print("Exporting rankings...")

    # JSON export
    json_data = rankings.to_json("rankings_output.json")
    print(f"✅ JSON exported to rankings_output.json")

    # HTML export
    html = rankings.to_html()
    with open("rankings_output.html", "w") as f:
        f.write(html)
    print(f"✅ HTML exported to rankings_output.html")

    # Markdown export
    markdown = rankings.to_markdown()
    with open("rankings_output.md", "w") as f:
        f.write(markdown)
    print(f"✅ Markdown exported to rankings_output.md")

    # Display markdown preview
    print()
    print("Markdown Preview:")
    print(markdown)


if __name__ == "__main__":
    main()
