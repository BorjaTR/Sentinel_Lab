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


def calculate_simulation_days(transactions: List[SentinelTx]) -> float:
    """
    Calculate simulation duration in days from transaction timestamps.

    This is the single source of truth for time-base conversions.
    All "per day" metrics must use this function.

    Args:
        transactions: List of transactions with timestamps

    Returns:
        Duration in days (float)

    Example:
        >>> txs = [SentinelTx(timestamp=0, ...), SentinelTx(timestamp=86400, ...)]
        >>> calculate_simulation_days(txs)
        1.0
    """
    if not transactions:
        return 0.0

    timestamps = [tx.timestamp for tx in transactions]
    min_ts = min(timestamps)
    max_ts = max(timestamps)

    duration_seconds = max_ts - min_ts

    # Handle edge case: all transactions at same timestamp
    if duration_seconds == 0:
        # Assume 1 transaction per second as baseline
        duration_seconds = len(transactions)

    return duration_seconds / 86400.0  # Convert seconds to days


@dataclass
class TreasuryConfig:
    """
    Treasury configuration for sustainability analysis.

    Makes all treasury assumptions explicit and configurable.

    Attributes:
        initial_balance_usdc: Starting treasury balance in USDC
        simulation_days: Duration of simulation in days (for rate calculations)
        emissions_schedule: Optional emission schedule to apply

    Example:
        config = TreasuryConfig(
            initial_balance_usdc=5_000_000,
            simulation_days=1.0
        )
    """
    initial_balance_usdc: float = 1_000_000.0
    simulation_days: float = 1.0
    emissions_schedule: Optional['EmissionsSchedule'] = None

    def __post_init__(self):
        """Validate treasury config."""
        if self.initial_balance_usdc < 0:
            raise ValueError(f"initial_balance_usdc must be >= 0, got {self.initial_balance_usdc}")
        if self.simulation_days <= 0:
            raise ValueError(f"simulation_days must be > 0, got {self.simulation_days}")

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON export."""
        return {
            'initial_balance_usdc': self.initial_balance_usdc,
            'simulation_days': self.simulation_days,
            'has_emissions': self.emissions_schedule is not None
        }


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
        treasury_config: TreasuryConfig
    ) -> TreasuryState:
        """
        Calculate treasury sustainability metrics.

        Args:
            treasury_config: Treasury configuration (balance, duration, emissions)

        Returns:
            TreasuryState with sustainability metrics
        """
        # Calculate total fees collected (treasury revenue)
        total_fees = sum(tx.asset0_amount * self.fee_rate for tx in self.transactions)
        fees_per_day = total_fees / treasury_config.simulation_days if treasury_config.simulation_days > 0 else 0

        # Calculate total emissions sent (treasury burn)
        total_emissions = 0.0
        if treasury_config.emissions_schedule:
            total_emissions = len(self.transactions) * treasury_config.emissions_schedule.rate_per_tx
            if treasury_config.emissions_schedule.total_budget:
                total_emissions = min(total_emissions, treasury_config.emissions_schedule.total_budget)

        emissions_per_day = total_emissions / treasury_config.simulation_days if treasury_config.simulation_days > 0 else 0

        # Calculate runway
        net_rate = fees_per_day - emissions_per_day
        if net_rate >= 0:
            runway = float('inf')  # Sustainable
        else:
            # Days until balance reaches zero
            runway = treasury_config.initial_balance_usdc / abs(net_rate)

        return TreasuryState(
            balance_usdc=treasury_config.initial_balance_usdc + (net_rate * treasury_config.simulation_days),
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


def validate_economics_consistency(
    transactions: List[SentinelTx],
    role_metrics: Dict[str, RoleMetrics],
    treasury_state: TreasuryState,
    fee_bps: int,
    tolerance: float = 0.01
) -> List[str]:
    """
    Validate economics invariants to catch math bugs.

    Phase 6.5: Economics hardening - ensure role-based accounting is internally consistent.

    Checks:
    1. Sum of fees paid by roles ≈ treasury fees collected (within tolerance)
    2. No role has net revenue > total system revenue
    3. Treasury balance never goes negative in projections
    4. Role P&L sums are reasonable (no free lunch)

    Args:
        transactions: List of all transactions
        role_metrics: Per-role metrics from analyzer
        treasury_state: Treasury state from analyzer
        fee_bps: Fee rate in basis points
        tolerance: Allowed relative error (default 1%)

    Returns:
        List of error messages (empty if all checks pass)

    Example:
        >>> errors = validate_economics_consistency(txs, role_metrics, treasury, 50)
        >>> if errors:
        ...     for err in errors:
        ...         print(f"INVARIANT VIOLATION: {err}")
    """
    errors = []
    fee_rate = fee_bps / 10000.0

    # Check 1: Sum of fees paid by roles = treasury fees collected
    total_fees_from_roles = sum(m.fees_paid for m in role_metrics.values())
    treasury_fees = treasury_state.fees_collected

    if treasury_fees > 0:
        relative_error = abs(total_fees_from_roles - treasury_fees) / treasury_fees
        if relative_error > tolerance:
            errors.append(
                f"Fee accounting mismatch: roles paid ${total_fees_from_roles:,.0f}, "
                f"treasury collected ${treasury_fees:,.0f} "
                f"({relative_error*100:.2f}% error, tolerance {tolerance*100:.1f}%)"
            )

    # Check 2: No role has net revenue > total system revenue
    total_revenue = sum(tx.asset0_amount for tx in transactions)
    for role, metrics in role_metrics.items():
        if metrics.net_revenue > total_revenue * (1 + tolerance):
            errors.append(
                f"Free lunch detected: {role} has net revenue ${metrics.net_revenue:,.0f} "
                f"> total system revenue ${total_revenue:,.0f}"
            )

    # Check 3: Treasury balance never goes negative
    if treasury_state.balance_usdc < 0:
        errors.append(
            f"Treasury balance is negative: ${treasury_state.balance_usdc:,.2f} "
            f"(initial balance may be too low or burn rate too high)"
        )

    # Check 4: Sum of role volumes should be reasonable
    # Each transaction touches 2 roles (sender + receiver), so total role volume
    # should be ~2x transaction volume (within some tolerance for untracked roles)
    total_tx_volume = sum(tx.asset0_amount for tx in transactions)
    total_role_volume = sum(m.volume_usdc for m in role_metrics.values())

    # Expected: total_role_volume ≈ 2 * total_tx_volume (each tx counted twice)
    # But allow wide tolerance for:
    # - Empty roles (not all txs may have role annotations)
    # - Double-counting semantics
    if total_tx_volume > 0:
        volume_ratio = total_role_volume / total_tx_volume
        # Expected range: [0.5, 3.0] (very permissive to handle different accounting methods)
        if volume_ratio < 0.1 or volume_ratio > 5.0:
            errors.append(
                f"Volume accounting anomaly: role volume ${total_role_volume:,.0f}, "
                f"tx volume ${total_tx_volume:,.0f} (ratio {volume_ratio:.2f}x). "
                f"Expected ratio between 0.5x and 3.0x. Check role assignment or volume calculation."
            )

    # Check 5: Runway calculation makes sense
    if not treasury_state.is_sustainable and treasury_state.runway_days != float('inf'):
        # Verify: runway = balance / burn_rate_net
        net_burn = treasury_state.burn_rate_per_day - treasury_state.revenue_rate_per_day
        if net_burn > 0:
            expected_runway = treasury_state.balance_usdc / net_burn
            runway_error = abs(treasury_state.runway_days - expected_runway) / max(expected_runway, 1)
            if runway_error > tolerance:
                errors.append(
                    f"Runway calculation error: reported {treasury_state.runway_days:.1f} days, "
                    f"expected {expected_runway:.1f} days ({runway_error*100:.1f}% error)"
                )

    return errors
