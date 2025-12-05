"""
Baseline Analysis - Compute actual mainnet metrics without simulation.

This module analyzes real transaction data to establish ground truth
for before/after comparisons.
"""

from dataclasses import dataclass
from typing import Optional, List
from .schema import SentinelTx, Opcode


@dataclass
class BaselineMetrics:
    """
    Metrics computed from actual mainnet transaction data.

    This represents the ground truth "what actually happened" for before/after
    comparison with optimized configurations.
    """

    # Transaction counts
    tx_count: int

    # Volume metrics
    total_volume_asset0: float       # e.g., total USDC volume
    total_volume_asset1: float       # e.g., total GPU credits volume

    # Fee metrics (if inferable from data)
    total_fees_asset0: Optional[float] = None
    avg_fee_rate_asset0: Optional[float] = None  # in bps

    # Time range
    start_timestamp: Optional[int] = None
    end_timestamp: Optional[int] = None
    duration_seconds: Optional[float] = None

    # Economic metrics - Treasury semantics
    # NOTE: daily_net_treasury_change is defined as:
    # "Change in protocol treasury balance in asset0 per day under baseline config"
    # Positive = treasury growing, Negative = treasury bleeding
    # Computed from: (penalties - rewards) / days
    daily_net_treasury_change: Optional[float] = None
    daily_volume_asset0: Optional[float] = None
    daily_tx_count: Optional[float] = None

    # Transaction breakdown
    transfer_count: int = 0
    swap_count: int = 0
    reward_count: int = 0
    penalty_count: int = 0

    # Failure metrics (optional - if detectable from data)
    # Some protocols/datasets expose failed transactions
    failed_tx_count: Optional[int] = None
    failure_rate: Optional[float] = None  # failed / total (0.0 to 1.0)


@dataclass
class BaselinePolicy:
    """
    Policy for protocol-specific baseline interpretation.

    Different protocols have different semantics for treasury, fees, and emissions.
    This provides hooks for customization without changing core logic.
    """
    # Treasury interpretation
    treasury_user_id: int = 0  # Which user_id represents protocol treasury
    treasury_role: str = "treasury"  # Which role represents treasury

    # Fee interpretation
    # Should PENALTY opcodes be counted as protocol fees?
    penalties_are_fees: bool = True
    # Should REWARD opcodes be counted as protocol emissions?
    rewards_are_emissions: bool = True


class BaselineAnalyzer:
    """Analyze real transaction data to compute baseline metrics."""

    def __init__(self, policy: Optional[BaselinePolicy] = None):
        """
        Initialize analyzer with optional protocol-specific policy.

        Args:
            policy: Protocol-specific interpretation rules (default: standard DePIN)
        """
        self.policy = policy or BaselinePolicy()

    def compute(self, txs: List[SentinelTx]) -> BaselineMetrics:
        """
        Compute baseline metrics from transaction list.

        Logic:
        - Aggregate volume/fees over all transactions
        - Try to infer fee rate if fee fields or vault deltas exist
        - If timestamps span >= 1 day, compute daily rates
        - Use existing TreasuryState logic if treasury semantics detected

        Args:
            txs: List of normalized transactions

        Returns:
            BaselineMetrics with all computable fields filled
        """
        if not txs:
            return BaselineMetrics(
                tx_count=0,
                total_volume_asset0=0.0,
                total_volume_asset1=0.0
            )

        # Sort by timestamp for time-based calculations
        sorted_txs = sorted(txs, key=lambda t: t.timestamp)

        # Basic counts
        tx_count = len(txs)
        transfer_count = sum(1 for tx in txs if tx.opcode == Opcode.TRANSFER)
        swap_count = sum(1 for tx in txs if tx.opcode == Opcode.SWAP)
        reward_count = sum(1 for tx in txs if tx.opcode == Opcode.REWARD)
        penalty_count = sum(1 for tx in txs if tx.opcode == Opcode.PENALTY)

        # Volume aggregation
        total_volume_asset0 = sum(tx.asset0_amount for tx in txs)
        total_volume_asset1 = sum(tx.asset1_amount for tx in txs)

        # Time range
        start_timestamp = sorted_txs[0].timestamp
        end_timestamp = sorted_txs[-1].timestamp
        duration_seconds = end_timestamp - start_timestamp if end_timestamp > start_timestamp else None

        # Daily rates
        daily_volume_asset0 = None
        daily_tx_count = None
        if duration_seconds and duration_seconds > 0:
            days = duration_seconds / 86400.0
            if days > 0:
                daily_volume_asset0 = total_volume_asset0 / days
                daily_tx_count = tx_count / days

        # Fee inference - compute from treasury flows (rewards - penalties)
        total_fees_asset0 = None
        avg_fee_rate_asset0 = None
        daily_net_treasury_change = None

        if reward_count > 0 or penalty_count > 0:
            # Net treasury change = penalties - rewards
            # (penalties flow TO treasury, rewards flow FROM treasury)
            total_rewards = sum(
                tx.asset0_amount for tx in txs
                if tx.opcode == Opcode.REWARD
            )
            total_penalties = sum(
                tx.asset0_amount for tx in txs
                if tx.opcode == Opcode.PENALTY
            )

            net_treasury_flow = total_penalties - total_rewards

            # If we have duration, compute daily rate
            if duration_seconds and duration_seconds > 0:
                days = duration_seconds / 86400.0
                if days > 0:
                    daily_net_treasury_change = net_treasury_flow / days

            # Estimate fees from penalties (if penalties represent fees)
            if total_penalties > 0:
                total_fees_asset0 = total_penalties

                # Estimate fee rate as percentage of volume
                if total_volume_asset0 > 0:
                    fee_rate_decimal = total_fees_asset0 / total_volume_asset0
                    avg_fee_rate_asset0 = fee_rate_decimal * 10000.0  # Convert to bps

        return BaselineMetrics(
            tx_count=tx_count,
            total_volume_asset0=total_volume_asset0,
            total_volume_asset1=total_volume_asset1,
            total_fees_asset0=total_fees_asset0,
            avg_fee_rate_asset0=avg_fee_rate_asset0,
            start_timestamp=start_timestamp,
            end_timestamp=end_timestamp,
            duration_seconds=duration_seconds,
            daily_net_treasury_change=daily_net_treasury_change,
            daily_volume_asset0=daily_volume_asset0,
            daily_tx_count=daily_tx_count,
            transfer_count=transfer_count,
            swap_count=swap_count,
            reward_count=reward_count,
            penalty_count=penalty_count,
        )
