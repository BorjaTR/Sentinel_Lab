"""
Unit Economics - Cost and margin per resource unit.

This module provides tools to answer: "Are we a business or a subsidy?"
by computing real cost and margin per resource unit (GPU-hour, GB, tx).

Pain point it solves:
    "What is our actual cost per GPU-hour / GB? Are we profitable per unit?"

Usage:
    from sentinel_cloud.unit_economics import (
        UnitEconomicsConfig,
        compute_unit_economics
    )

    config = UnitEconomicsConfig(
        resource_name="gpu_hour",
        resource_amount_field="asset1_amount"
    )

    result = compute_unit_economics(
        txs=txs,
        run=run_result,
        baseline=baseline,
        cfg=config,
        emissions_usd_per_day=5000
    )

    print(f"Revenue per GPU-hour: ${result.revenue_per_unit:.2f}")
    print(f"Net margin per GPU-hour: ${result.net_margin_per_unit:.2f}")
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional

from .schema import SentinelTx
from .experiment import RunResult
from .baseline import BaselineMetrics


@dataclass
class UnitEconomicsConfig:
    """
    Configuration for unit economics calculation.

    Attributes:
        resource_name: Human-readable resource type (e.g., "gpu_hour", "gb_month", "tx")
        resource_amount_field: SentinelTx field to sum for units (e.g., "asset1_amount")
        price_per_unit_override: Optional manual price per unit (overrides computed value)
        include_emissions: Whether to include emissions in margin calculation
        include_fees_only: If True, only use fees for revenue (ignore other sources)

    Example:
        >>> config = UnitEconomicsConfig(
        ...     resource_name="gpu_hour",
        ...     resource_amount_field="asset1_amount",
        ...     include_emissions=True
        ... )
    """
    resource_name: str
    resource_amount_field: str = "asset1_amount"
    price_per_unit_override: Optional[float] = None
    include_emissions: bool = True
    include_fees_only: bool = False


@dataclass
class UnitEconomicsResult:
    """
    Unit economics analysis result.

    Attributes:
        resource_name: Resource type analyzed
        total_units: Total resource units processed
        total_revenue: Total revenue generated (USD/asset0)
        revenue_per_unit: Average revenue per resource unit
        total_emissions: Total emissions cost (if available)
        emissions_per_unit: Average emissions per resource unit
        net_margin_total: Total net margin (revenue - emissions)
        net_margin_per_unit: Net margin per resource unit
        per_role: Per-role breakdown of units, revenue, emissions, margin

    Example:
        >>> print(f"Revenue: ${result.revenue_per_unit:.2f}/GPU-hour")
        >>> print(f"Margin: ${result.net_margin_per_unit:.2f}/GPU-hour")
        >>> for role, metrics in result.per_role.items():
        ...     print(f"{role}: {metrics['units']} units, ${metrics['margin']:.2f} margin")
    """
    resource_name: str

    # Totals
    total_units: float
    total_revenue: float
    revenue_per_unit: float

    # Emissions (optional)
    total_emissions: Optional[float] = None
    emissions_per_unit: Optional[float] = None

    # Net margin (optional)
    net_margin_total: Optional[float] = None
    net_margin_per_unit: Optional[float] = None

    # Per-role breakdown
    per_role: Dict[str, Dict[str, float]] = field(default_factory=dict)

    def summary(self) -> str:
        """
        Generate human-readable summary.

        Returns:
            Multi-line summary string
        """
        lines = []
        lines.append("=" * 70)
        lines.append(f"UNIT ECONOMICS: {self.resource_name}")
        lines.append("=" * 70)

        lines.append(f"\nTotal Units: {self.total_units:,.2f}")
        lines.append(f"Total Revenue: ${self.total_revenue:,.2f}")
        lines.append(f"\n💰 Revenue per {self.resource_name}: ${self.revenue_per_unit:.4f}")

        if self.emissions_per_unit is not None:
            lines.append(f"💸 Emissions per {self.resource_name}: ${self.emissions_per_unit:.4f}")

        if self.net_margin_per_unit is not None:
            margin_label = "PROFIT" if self.net_margin_per_unit > 0 else "LOSS"
            emoji = "✅" if self.net_margin_per_unit > 0 else "❌"
            lines.append(f"\n{emoji} Net Margin per {self.resource_name}: ${self.net_margin_per_unit:.4f} ({margin_label})")

        if self.per_role:
            lines.append(f"\n📊 Per-Role Breakdown:")
            for role, metrics in sorted(self.per_role.items()):
                units = metrics.get('units', 0)
                revenue = metrics.get('revenue', 0)
                margin = metrics.get('margin', 0)
                margin_emoji = "✅" if margin > 0 else "❌"

                lines.append(f"  {role:12s}: {units:10,.2f} units | "
                           f"${revenue:10,.2f} revenue | "
                           f"{margin_emoji} ${margin:10,.2f} margin")

        lines.append("=" * 70)
        return "\n".join(lines)


def compute_unit_economics(
    txs: List[SentinelTx],
    run: RunResult,
    baseline: BaselineMetrics,
    cfg: UnitEconomicsConfig,
    emissions_usd_per_day: Optional[float] = None
) -> UnitEconomicsResult:
    """
    Compute unit economics from transaction data and simulation results.

    Args:
        txs: List of SentinelTx transactions
        run: Simulation RunResult with metrics
        baseline: BaselineMetrics for context
        cfg: UnitEconomicsConfig specifying resource type and calculation method
        emissions_usd_per_day: Optional total emissions cost per day

    Returns:
        UnitEconomicsResult with per-unit revenue, emissions, and margin

    Example:
        >>> config = UnitEconomicsConfig(
        ...     resource_name="gpu_hour",
        ...     resource_amount_field="asset1_amount"
        ... )
        >>> result = compute_unit_economics(
        ...     txs=transactions,
        ...     run=run_result,
        ...     baseline=baseline_metrics,
        ...     cfg=config,
        ...     emissions_usd_per_day=5000
        ... )
        >>> print(f"Margin: ${result.net_margin_per_unit:.2f}/GPU-hour")
    """
    # Extract total resource units
    total_units = 0.0
    units_by_role: Dict[str, float] = {}

    for tx in txs:
        # Get resource amount from specified field
        if cfg.resource_amount_field == "asset0_amount":
            units = tx.asset0_amount
        elif cfg.resource_amount_field == "asset1_amount":
            units = tx.asset1_amount
        else:
            raise ValueError(f"Unsupported resource_amount_field: {cfg.resource_amount_field}")

        total_units += units

        # Track by role (use role_a as primary role)
        role = tx.role_a
        if role not in units_by_role:
            units_by_role[role] = 0
        units_by_role[role] += units

    if total_units == 0:
        # No units processed - return zero result
        return UnitEconomicsResult(
            resource_name=cfg.resource_name,
            total_units=0,
            total_revenue=0,
            revenue_per_unit=0,
            total_emissions=0 if emissions_usd_per_day is not None else None,
            emissions_per_unit=0 if emissions_usd_per_day is not None else None,
            net_margin_total=0 if emissions_usd_per_day is not None else None,
            net_margin_per_unit=0 if emissions_usd_per_day is not None else None
        )

    # Extract revenue
    if cfg.include_fees_only:
        # Only use fee-based revenue
        total_revenue = run.metrics.get('rev_usdc', 0.0)
        if total_revenue == 0:
            total_revenue = baseline.total_fees_asset0 or 0.0
    else:
        # Use all revenue sources
        total_revenue = run.metrics.get('rev_usdc', 0.0)

        # Fallback to baseline if no revenue in run
        if total_revenue == 0:
            total_revenue = baseline.total_fees_asset0 or 0.0

        # Fallback to treasury change if no fees
        if total_revenue == 0 and baseline.daily_net_treasury_change:
            if baseline.daily_net_treasury_change > 0 and baseline.duration_seconds:
                days = baseline.duration_seconds / 86400.0
                total_revenue = baseline.daily_net_treasury_change * days

    revenue_per_unit = total_revenue / total_units if total_units > 0 else 0

    # Compute emissions (if provided)
    total_emissions = None
    emissions_per_unit = None

    if cfg.include_emissions and emissions_usd_per_day is not None:
        # Spread total daily emissions over resource units
        if baseline.duration_seconds:
            days = baseline.duration_seconds / 86400.0
            total_emissions = emissions_usd_per_day * days
            emissions_per_unit = total_emissions / total_units if total_units > 0 else 0

    # Compute net margin (if emissions available)
    net_margin_total = None
    net_margin_per_unit = None

    if total_emissions is not None:
        net_margin_total = total_revenue - total_emissions
        net_margin_per_unit = net_margin_total / total_units if total_units > 0 else 0

    # Compute per-role breakdown
    per_role: Dict[str, Dict[str, float]] = {}

    for role, role_units in units_by_role.items():
        # Assume revenue and emissions are proportional to units for each role
        role_revenue = (role_units / total_units) * total_revenue if total_units > 0 else 0
        role_emissions = (role_units / total_units) * total_emissions if total_emissions is not None and total_units > 0 else None
        role_margin = role_revenue - role_emissions if role_emissions is not None else None

        per_role[role] = {
            'units': role_units,
            'revenue': role_revenue,
            'emissions': role_emissions if role_emissions is not None else 0,
            'margin': role_margin if role_margin is not None else role_revenue
        }

    return UnitEconomicsResult(
        resource_name=cfg.resource_name,
        total_units=total_units,
        total_revenue=total_revenue,
        revenue_per_unit=revenue_per_unit,
        total_emissions=total_emissions,
        emissions_per_unit=emissions_per_unit,
        net_margin_total=net_margin_total,
        net_margin_per_unit=net_margin_per_unit,
        per_role=per_role
    )
