"""
Role-Based Economics & Sustainability Analysis

This module adds role-aware economic modeling to Sentinel Cloud,
enabling protocol designers to:
- Track revenue/cost by participant type (miner, validator, client)
- Model emissions schedules and token distribution
- Detect treasury sustainability issues
- Simulate long-term protocol economics

Usage:
    from sentinel_cloud.role_economics import RoleAnalyzer, EmissionsSchedule

    # Analyze role economics from experiment results
    analyzer = RoleAnalyzer(run_result)
    role_metrics = analyzer.get_role_breakdown()

    # Check treasury sustainability
    treasury = analyzer.calculate_treasury_state(
        initial_balance=1_000_000,
        emissions_schedule=EmissionsSchedule(rate_per_tx=10.0)
    )

    if not treasury.is_sustainable:
        print(f"⚠️ Treasury depletes in {treasury.runway_days:.1f} days")
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from .schema import SentinelTx, VALID_ROLES


@dataclass
class RoleDistribution:
    """
    Defines how protocol revenue/emissions are distributed to roles.

    All values are fractions (0.0 to 1.0) and must sum to 1.0.

    Example:
        # 40% to validators, 40% to miners, 20% to treasury
        dist = RoleDistribution(validator=0.4, miner=0.4, treasury=0.2)
    """
    client: float = 0.0
    miner: float = 0.0
    validator: float = 0.0
    treasury: float = 1.0  # Default: all to treasury
    lp: float = 0.0
    storage_provider: float = 0.0
    sequencer: float = 0.0
    hotspot: float = 0.0

    def __post_init__(self):
        self.validate()

    def validate(self):
        """Ensure distribution sums to 1.0 (allow small float precision errors)."""
        total = sum([
            self.client, self.miner, self.validator, self.treasury,
            self.lp, self.storage_provider, self.sequencer, self.hotspot
        ])
        if not (0.99 <= total <= 1.01):
            raise ValueError(f"Distribution must sum to 1.0, got {total:.6f}")

    def get_share(self, role: str) -> float:
        """Get distribution share for a specific role."""
        return getattr(self, role, 0.0)


@dataclass
class EmissionsSchedule:
    """
    Protocol token emissions schedule.

    Defines how many tokens are minted and distributed to participants.

    Attributes:
        rate_per_tx: Tokens emitted per transaction
        rate_per_block: Tokens emitted per block (not used if block data unavailable)
        total_budget: Total emission budget (optional cap)
        distribution: How emissions are split among roles

    Example:
        # Emit 10 tokens per tx, split 50/50 between miners and validators
        schedule = EmissionsSchedule(
            rate_per_tx=10.0,
            distribution=RoleDistribution(miner=0.5, validator=0.5)
        )
    """
    rate_per_tx: float = 0.0
    rate_per_block: float = 0.0
    total_budget: Optional[float] = None
    distribution: RoleDistribution = field(default_factory=lambda: RoleDistribution(treasury=1.0))


@dataclass
class TreasuryState:
    """
    Treasury balance and sustainability metrics.

    Tracks protocol treasury health, including:
    - Current balance
    - Revenue rate (inflow)
    - Burn rate (outflow via emissions/rewards)
    - Runway (time until depletion)

    Attributes:
        balance_usdc: Current treasury balance in USDC
        revenue_rate_per_day: USDC inflow per day (from fees)
        burn_rate_per_day: USDC outflow per day (emissions, rewards)
        runway_days: Days until treasury depletes (if burn > revenue)
        emissions_sent: Total emissions paid out
        fees_collected: Total fees collected
    """
    balance_usdc: float
    revenue_rate_per_day: float
    burn_rate_per_day: float
    runway_days: float
    emissions_sent: float = 0.0
    fees_collected: float = 0.0

    @property
    def is_sustainable(self) -> bool:
        """Check if treasury is sustainable (revenue >= burn)."""
        return self.burn_rate_per_day <= self.revenue_rate_per_day

    @property
    def net_rate_per_day(self) -> float:
        """Net treasury growth/decline per day."""
        return self.revenue_rate_per_day - self.burn_rate_per_day

    @property
    def depletion_risk(self) -> str:
        """Human-readable risk level."""
        if self.is_sustainable:
            return "✅ Sustainable"
        elif self.runway_days > 365:
            return "🟡 Low Risk"
        elif self.runway_days > 90:
            return "🟠 Medium Risk"
        elif self.runway_days > 30:
            return "🔴 High Risk"
        else:
            return "💀 Critical"


@dataclass
class RoleMetrics:
    """
    Per-role economic metrics.

    Aggregates all economic activity for a specific participant role.

    Attributes:
        role: Role identifier (e.g., "miner", "validator", "client")
        tx_count: Number of transactions involving this role
        revenue_earned: USDC earned by this role (from fees, rewards)
        emissions_received: Tokens received via protocol emissions
        fees_paid: Fees paid by this role
        volume_usdc: Total transaction volume in USDC
        avg_tx_size: Average transaction size in USDC
    """
    role: str
    tx_count: int = 0
    revenue_earned: float = 0.0
    emissions_received: float = 0.0
    fees_paid: float = 0.0
    volume_usdc: float = 0.0

    @property
    def avg_tx_size(self) -> float:
        """Average transaction size in USDC."""
        return self.volume_usdc / self.tx_count if self.tx_count > 0 else 0.0

    @property
    def net_revenue(self) -> float:
        """Net revenue (earned - paid)."""
        return self.revenue_earned - self.fees_paid

    def to_dict(self) -> dict:
        """Convert to dictionary for export/display."""
        return {
            'role': self.role,
            'tx_count': self.tx_count,
            'revenue_earned': self.revenue_earned,
            'emissions_received': self.emissions_received,
            'fees_paid': self.fees_paid,
            'volume_usdc': self.volume_usdc,
            'avg_tx_size': self.avg_tx_size,
            'net_revenue': self.net_revenue
        }


class RoleAnalyzer:
    """
    Analyzes role-based economics from transaction data.

    Given a list of transactions, extracts role-specific metrics:
    - How much revenue each role earned
    - How much each role paid in fees
    - Transaction counts by role
    - Volume by role

    Usage:
        analyzer = RoleAnalyzer(transactions)
        role_metrics = analyzer.get_role_breakdown()

        # Check miner revenue
        miner_metrics = role_metrics['miner']
        print(f"Miners earned: ${miner_metrics.revenue_earned:,.2f}")
    """

    def __init__(self, transactions: List[SentinelTx], fee_bps: int = 0):
        """
        Initialize analyzer with transaction data.

        Args:
            transactions: List of SentinelTx objects
            fee_bps: Fee rate in basis points (for fee calculation)
        """
        self.transactions = transactions
        self.fee_bps = fee_bps
        self.fee_rate = fee_bps / 10000.0

    def get_role_breakdown(self) -> Dict[str, RoleMetrics]:
        """
        Calculate metrics for each role.

        Returns:
            Dictionary mapping role name → RoleMetrics
        """
        # Initialize metrics for all known roles
        metrics: Dict[str, RoleMetrics] = {}
        for role in VALID_ROLES:
            if role:  # Skip empty string
                metrics[role] = RoleMetrics(role=role)

        # Aggregate metrics from transactions
        for tx in self.transactions:
            # Calculate fee
            fee_usdc = tx.asset0_amount * self.fee_rate

            # Update sender (user_a) metrics
            if tx.role_a and tx.role_a in metrics:
                metrics[tx.role_a].tx_count += 1
                metrics[tx.role_a].fees_paid += fee_usdc
                metrics[tx.role_a].volume_usdc += tx.asset0_amount

            # Update receiver (user_b) metrics
            if tx.role_b and tx.role_b in metrics:
                metrics[tx.role_b].tx_count += 1
                metrics[tx.role_b].revenue_earned += tx.asset0_amount
                metrics[tx.role_b].volume_usdc += tx.asset0_amount

        # Remove roles with zero activity
        return {role: m for role, m in metrics.items() if m.tx_count > 0}

    def calculate_emissions(
        self,
        emissions_schedule: EmissionsSchedule
    ) -> Dict[str, float]:
        """
        Calculate emissions distributed to each role.

        Args:
            emissions_schedule: Emission rate and distribution

        Returns:
            Dictionary mapping role → total emissions received
        """
        total_emissions = len(self.transactions) * emissions_schedule.rate_per_tx

        # Apply budget cap if specified
        if emissions_schedule.total_budget:
            total_emissions = min(total_emissions, emissions_schedule.total_budget)

        # Distribute to roles
        distribution = {}
        for role in VALID_ROLES:
            if role:  # Skip empty string
                share = emissions_schedule.distribution.get_share(role)
                distribution[role] = total_emissions * share

        return distribution

    def calculate_treasury_state(
        self,
        initial_balance: float,
        emissions_schedule: Optional[EmissionsSchedule] = None,
        simulation_days: float = 1.0
    ) -> TreasuryState:
        """
        Calculate treasury sustainability metrics.

        Args:
            initial_balance: Starting treasury balance in USDC
            emissions_schedule: Emission schedule (if None, no emissions)
            simulation_days: Duration of simulation in days

        Returns:
            TreasuryState with sustainability metrics
        """
        # Calculate total fees collected (treasury revenue)
        total_fees = sum(tx.asset0_amount * self.fee_rate for tx in self.transactions)
        fees_per_day = total_fees / simulation_days if simulation_days > 0 else 0

        # Calculate total emissions sent (treasury burn)
        total_emissions = 0.0
        if emissions_schedule:
            total_emissions = len(self.transactions) * emissions_schedule.rate_per_tx
            if emissions_schedule.total_budget:
                total_emissions = min(total_emissions, emissions_schedule.total_budget)

        emissions_per_day = total_emissions / simulation_days if simulation_days > 0 else 0

        # Calculate runway
        net_rate = fees_per_day - emissions_per_day
        if net_rate >= 0:
            runway = float('inf')  # Sustainable
        else:
            # Days until balance reaches zero
            runway = initial_balance / abs(net_rate)

        return TreasuryState(
            balance_usdc=initial_balance + (net_rate * simulation_days),
            revenue_rate_per_day=fees_per_day,
            burn_rate_per_day=emissions_per_day,
            runway_days=runway,
            emissions_sent=total_emissions,
            fees_collected=total_fees
        )

    def detect_imbalances(
        self,
        role_metrics: Optional[Dict[str, RoleMetrics]] = None
    ) -> List[str]:
        """
        Detect economic imbalances and potential issues.

        Returns:
            List of warning messages
        """
        warnings = []

        if role_metrics is None:
            role_metrics = self.get_role_breakdown()

        # Check if any role is paying more than earning
        for role, metrics in role_metrics.items():
            if metrics.net_revenue < 0:
                warnings.append(
                    f"⚠️ {role.capitalize()}s are paying more than earning "
                    f"(net: ${metrics.net_revenue:,.2f})"
                )

        # Check if treasury is receiving zero fees
        treasury_metrics = role_metrics.get('treasury')
        if treasury_metrics and treasury_metrics.revenue_earned == 0:
            warnings.append("⚠️ Treasury receiving zero fees (unsustainable)")

        # Check for role concentration
        total_volume = sum(m.volume_usdc for m in role_metrics.values())
        for role, metrics in role_metrics.items():
            if total_volume > 0:
                share = metrics.volume_usdc / total_volume
                if share > 0.8:
                    warnings.append(
                        f"⚠️ {role.capitalize()}s dominate {share*100:.1f}% of volume "
                        f"(centralization risk)"
                    )

        return warnings


def summarize_role_economics(
    role_metrics: Dict[str, RoleMetrics],
    treasury_state: Optional[TreasuryState] = None
) -> str:
    """
    Generate human-readable summary of role economics.

    Args:
        role_metrics: Per-role metrics from RoleAnalyzer
        treasury_state: Optional treasury state

    Returns:
        Formatted summary string
    """
    lines = []
    lines.append("\n" + "="*70)
    lines.append("Role-Based Economics Summary")
    lines.append("="*70 + "\n")

    # Role breakdown
    lines.append(f"{'Role':<15} {'Txs':<8} {'Revenue':<12} {'Fees Paid':<12} {'Net':<12}")
    lines.append("-"*70)

    for role, metrics in sorted(role_metrics.items(), key=lambda x: x[1].revenue_earned, reverse=True):
        lines.append(
            f"{role.capitalize():<15} "
            f"{metrics.tx_count:<8} "
            f"${metrics.revenue_earned:>10,.0f} "
            f"${metrics.fees_paid:>10,.0f} "
            f"${metrics.net_revenue:>+10,.0f}"
        )

    # Treasury summary
    if treasury_state:
        lines.append("\n" + "="*70)
        lines.append("Treasury Sustainability")
        lines.append("="*70)
        lines.append(f"Balance:        ${treasury_state.balance_usdc:>15,.2f}")
        lines.append(f"Revenue/day:    ${treasury_state.revenue_rate_per_day:>15,.2f}")
        lines.append(f"Burn/day:       ${treasury_state.burn_rate_per_day:>15,.2f}")
        lines.append(f"Net/day:        ${treasury_state.net_rate_per_day:>+15,.2f}")

        if treasury_state.runway_days == float('inf'):
            lines.append(f"Runway:         {'♾️  Sustainable':>15}")
        else:
            lines.append(f"Runway:         {treasury_state.runway_days:>15,.1f} days")

        lines.append(f"Risk Level:     {treasury_state.depletion_risk:>15}")

    lines.append("\n" + "="*70 + "\n")

    return "\n".join(lines)
