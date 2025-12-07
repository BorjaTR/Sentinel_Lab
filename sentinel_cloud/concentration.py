"""
Whale & Fairness Analytics - Reward concentration and distribution analysis.

This module provides tools to answer: "Are rewards insanely concentrated or somewhat fair?"
by computing distribution metrics (Gini, HHI, top-K share).

Pain point it solves:
    "Top 10 addresses get everything, but we can't quantify or explain it."

Usage:
    from sentinel_cloud.concentration import (
        compute_gini,
        compute_hhi,
        compute_concentration
    )

    rewards_by_user = {1: 1000, 2: 500, 3: 200, ...}
    metrics = compute_concentration(rewards_by_user)

    print(f"Gini coefficient: {metrics.gini:.3f}")
    print(f"Top 10 share: {metrics.top_k_share[10]:.1%}")
    if metrics.suspicious:
        print(f"⚠️ High concentration detected: {metrics.suspicion_reasons}")
"""

from dataclasses import dataclass, field
from typing import Dict, List


@dataclass
class ConcentrationMetrics:
    """
    Distribution concentration metrics for reward/resource allocation.

    Attributes:
        gini: Gini coefficient (0 = perfect equality, 1 = perfect inequality)
        hhi: Herfindahl-Hirschman Index (0 = perfect competition, 10000 = monopoly)
        top_k_share: Share of rewards for top-K users (e.g., {10: 0.72, 100: 0.93})
        suspicious: True if concentration exceeds thresholds
        suspicion_reasons: List of reasons why flagged as suspicious

    Example:
        >>> metrics = compute_concentration(rewards_by_user)
        >>> if metrics.gini > 0.8:
        ...     print("Very unequal distribution")
        >>> if metrics.top_k_share[10] > 0.5:
        ...     print("Top 10 users dominate")
    """
    gini: float
    hhi: float
    top_k_share: Dict[int, float]
    suspicious: bool
    suspicion_reasons: List[str] = field(default_factory=list)

    def summary(self) -> str:
        """
        Generate human-readable summary of concentration metrics.

        Returns:
            Multi-line summary string
        """
        lines = []
        lines.append("=" * 70)
        lines.append("WHALE & FAIRNESS ANALYSIS")
        lines.append("=" * 70)

        # Gini interpretation
        if self.gini < 0.3:
            gini_label = "Low inequality (fairly distributed)"
            gini_emoji = "✅"
        elif self.gini < 0.5:
            gini_label = "Moderate inequality"
            gini_emoji = "🟡"
        elif self.gini < 0.7:
            gini_label = "High inequality"
            gini_emoji = "🟠"
        else:
            gini_label = "Very high inequality (concentrated)"
            gini_emoji = "🔴"

        lines.append(f"\n{gini_emoji} Gini Coefficient: {self.gini:.3f} ({gini_label})")

        # HHI interpretation
        if self.hhi < 1500:
            hhi_label = "Competitive (unconcentrated)"
            hhi_emoji = "✅"
        elif self.hhi < 2500:
            hhi_label = "Moderately concentrated"
            hhi_emoji = "🟡"
        else:
            hhi_label = "Highly concentrated"
            hhi_emoji = "🔴"

        lines.append(f"{hhi_emoji} HHI Index: {self.hhi:.0f} ({hhi_label})")

        # Top-K shares
        lines.append(f"\n🐳 Top User Concentration:")
        for k in sorted(self.top_k_share.keys()):
            share = self.top_k_share[k]
            emoji = "🔴" if share > 0.7 else "🟡" if share > 0.5 else "✅"
            lines.append(f"  {emoji} Top {k:3d} users: {share:6.1%} of rewards")

        # Suspicion flags
        if self.suspicious:
            lines.append(f"\n⚠️  CONCENTRATION WARNING:")
            for reason in self.suspicion_reasons:
                lines.append(f"  - {reason}")
        else:
            lines.append(f"\n✅ Distribution appears reasonable (not flagged as suspicious)")

        lines.append("=" * 70)
        return "\n".join(lines)


def compute_gini(values: List[float]) -> float:
    """
    Compute Gini coefficient for a distribution.

    The Gini coefficient measures inequality:
    - 0.0 = perfect equality (everyone has the same)
    - 1.0 = perfect inequality (one person has everything)

    Args:
        values: List of values (e.g., rewards per user)

    Returns:
        Gini coefficient in range [0, 1]

    Example:
        >>> # Perfect equality
        >>> compute_gini([100, 100, 100])
        0.0
        >>> # Perfect inequality
        >>> compute_gini([0, 0, 1000])
        0.667
        >>> # Moderate inequality
        >>> compute_gini([10, 20, 30, 40, 50])
        0.267
    """
    if not values or len(values) == 0:
        return 0.0

    # Remove zeros and sort
    sorted_values = sorted([v for v in values if v > 0])
    n = len(sorted_values)

    if n == 0:
        return 0.0

    if n == 1:
        return 0.0  # Single value = perfect equality

    # Compute Gini using formula:
    # G = (2 * sum(i * x_i)) / (n * sum(x_i)) - (n + 1) / n
    total = sum(sorted_values)

    if total == 0:
        return 0.0

    weighted_sum = sum((i + 1) * val for i, val in enumerate(sorted_values))
    gini = (2 * weighted_sum) / (n * total) - (n + 1) / n

    return max(0.0, min(1.0, gini))  # Clamp to [0, 1]


def compute_hhi(shares: List[float]) -> float:
    """
    Compute Herfindahl-Hirschman Index (HHI) for market concentration.

    HHI measures market concentration by summing squared market shares:
    - 0 = perfect competition (infinite small players)
    - 10000 = monopoly (one player has 100%)
    - < 1500 = unconcentrated
    - 1500-2500 = moderately concentrated
    - > 2500 = highly concentrated

    Args:
        shares: List of market shares as fractions (0-1), must sum to ~1.0

    Returns:
        HHI in range [0, 10000]

    Example:
        >>> # Perfect competition (many equal players)
        >>> compute_hhi([0.1] * 10)
        1000.0
        >>> # Monopoly
        >>> compute_hhi([1.0])
        10000.0
        >>> # Duopoly
        >>> compute_hhi([0.5, 0.5])
        5000.0
    """
    if not shares or len(shares) == 0:
        return 0.0

    # Convert to percentages and square
    hhi = sum((share * 100) ** 2 for share in shares if share > 0)

    return hhi


def compute_concentration(
    rewards_by_user: Dict[int, float],
    top_k_values: List[int] = None,
    gini_threshold: float = 0.7,
    top_10_threshold: float = 0.6,
    hhi_threshold: float = 2500
) -> ConcentrationMetrics:
    """
    Compute comprehensive concentration metrics for reward distribution.

    Args:
        rewards_by_user: Mapping of user_id -> total rewards
        top_k_values: List of K values for top-K analysis (default: [1, 10, 100])
        gini_threshold: Gini above this value triggers suspicion flag (default: 0.7)
        top_10_threshold: Top-10 share above this triggers suspicion (default: 0.6)
        hhi_threshold: HHI above this triggers suspicion (default: 2500)

    Returns:
        ConcentrationMetrics with Gini, HHI, top-K shares, and suspicion flags

    Example:
        >>> rewards = {1: 1000, 2: 500, 3: 200, 4: 100, 5: 50}
        >>> metrics = compute_concentration(rewards)
        >>> print(f"Gini: {metrics.gini:.3f}")
        >>> print(f"Top 10 control {metrics.top_k_share[10]:.1%}")
        >>> if metrics.suspicious:
        ...     print("High concentration detected!")
    """
    if top_k_values is None:
        top_k_values = [1, 10, 100]

    if not rewards_by_user or len(rewards_by_user) == 0:
        # No users - return empty/zero metrics
        return ConcentrationMetrics(
            gini=0.0,
            hhi=0.0,
            top_k_share={k: 0.0 for k in top_k_values},
            suspicious=False
        )

    # Extract reward values
    values = [v for v in rewards_by_user.values() if v > 0]

    if len(values) == 0:
        return ConcentrationMetrics(
            gini=0.0,
            hhi=0.0,
            top_k_share={k: 0.0 for k in top_k_values},
            suspicious=False
        )

    # Compute Gini
    gini = compute_gini(values)

    # Compute HHI (need to convert to shares first)
    total_rewards = sum(values)
    shares = [v / total_rewards for v in values if total_rewards > 0]
    hhi = compute_hhi(shares)

    # Compute top-K shares
    sorted_values = sorted(values, reverse=True)  # Descending
    top_k_share = {}

    for k in top_k_values:
        if k >= len(sorted_values):
            # K >= total users, top-K = everyone = 100%
            top_k_share[k] = 1.0
        else:
            top_k_sum = sum(sorted_values[:k])
            top_k_share[k] = top_k_sum / total_rewards if total_rewards > 0 else 0.0

    # Check for suspicion
    suspicious = False
    suspicion_reasons = []

    if gini > gini_threshold:
        suspicious = True
        suspicion_reasons.append(f"High Gini coefficient ({gini:.3f} > {gini_threshold})")

    if 10 in top_k_share and top_k_share[10] > top_10_threshold:
        suspicious = True
        suspicion_reasons.append(f"Top 10 users control {top_k_share[10]:.1%} (> {top_10_threshold:.0%})")

    if hhi > hhi_threshold:
        suspicious = True
        suspicion_reasons.append(f"High HHI ({hhi:.0f} > {hhi_threshold})")

    return ConcentrationMetrics(
        gini=gini,
        hhi=hhi,
        top_k_share=top_k_share,
        suspicious=suspicious,
        suspicion_reasons=suspicion_reasons
    )
