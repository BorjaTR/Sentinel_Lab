"""
Generate rankings for landing page protocols
"""

from pathlib import Path
from sentinel_cloud.rankings import load_protocols_from_directory, generate_rankings
import json

def main():
    # Load all protocols
    protocols = load_protocols_from_directory(Path("protocols/"))

    print(f"Loaded {len(protocols)} protocols")
    print()

    # Generate rankings
    rankings = generate_rankings(
        protocols,
        title="Sentinel Protocol Rankings",
        description="Protocol sustainability ratings for crypto. Know your runway.",
        last_updated="2025-01-15"
    )

    # Display rankings
    print("RANKINGS:")
    print("-" * 80)
    for p in rankings.protocols:
        status_emoji = "✅" if p.score.status == "Healthy" else "⚠️" if p.score.status == "Warning" else "🚨"
        runway = f"{p.score.runway_months:.0f}mo" if p.score.runway_months != float('inf') else "∞"
        ratio = f"{p.score.sustainability_ratio:.2f}" if p.score.sustainability_ratio != float('inf') else "∞"
        print(f"{p.rank}. {p.protocol.name:20} Score: {p.score.total_score:3d}/100 | Grade: {p.score.grade} | Status: {p.score.status:10} | Runway: {runway:8} | Ratio: {ratio}")
        print(f"   R:{p.score.runway_score}/40 S:{p.score.sustainability_score}/30 D:{p.score.diversification_score}/20 T:{p.score.trajectory_score}/10")
    print()

    # Export to JSON for landing page
    json_data = rankings.to_json("site/rankings.json")
    print(f"✅ JSON exported to site/rankings.json")

    # Display summary
    print()
    print("SUMMARY:")
    print(f"Protocols analyzed: {len(rankings.protocols)}")
    avg_score = sum(p.score.total_score for p in rankings.protocols) / len(rankings.protocols)
    print(f"Average score: {avg_score:.0f}")

    healthy = sum(1 for p in rankings.protocols if p.score.status == "Healthy")
    warning = sum(1 for p in rankings.protocols if p.score.status == "Warning")
    critical = sum(1 for p in rankings.protocols if p.score.status == "Critical")

    print(f"Healthy: {healthy} ({healthy/len(rankings.protocols)*100:.0f}%)")
    print(f"Warning: {warning} ({warning/len(rankings.protocols)*100:.0f}%)")
    print(f"Critical: {critical} ({critical/len(rankings.protocols)*100:.0f}%)")

if __name__ == "__main__":
    main()
