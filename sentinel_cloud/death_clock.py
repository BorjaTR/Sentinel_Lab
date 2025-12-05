"""
Death Clock / Runway Projection - Treasury sustainability analysis.

This module projects protocol treasury runway under different scenarios
to answer the critical question: "When do we run out of money?"

This is where the emotional hook happens - baseline might look fine until
you see "147 days until death."
"""

from dataclasses import dataclass
from datetime import date, timedelta
from typing import Optional


@dataclass
class RunwayInputs:
    """
    Inputs for runway projection.

    All amounts in asset0 (e.g., USDC).
    """
    treasury_start_asset0: float          # Current treasury balance
    daily_net_change_asset0: float        # Daily net change (revenue - emissions)
    daily_net_change_asset0_optimized: Optional[float] = None  # For optimized config
    today: date = None

    def __post_init__(self):
        if self.today is None:
            self.today = date.today()


@dataclass
class RunwayResult:
    """
    Runway projection results.

    runway_days = None means infinite runway (sustainable)
    death_date = None means never dies (sustainable)
    """
    baseline_runway_days: Optional[float]
    baseline_death_date: Optional[date]

    optimized_runway_days: Optional[float] = None
    optimized_death_date: Optional[date] = None
    runway_extension_days: Optional[float] = None

    def is_sustainable_baseline(self) -> bool:
        """Check if baseline config is sustainable (infinite runway)."""
        return self.baseline_runway_days is None

    def is_sustainable_optimized(self) -> bool:
        """Check if optimized config is sustainable (infinite runway)."""
        return self.optimized_runway_days is None


class RunwayProjector:
    """
    Project treasury runway under different configurations.

    Simple model: linear projection with constant daily burn/earn rate.
    Future enhancement: compound growth, seasonality, etc.
    """

    def compute_runway_simple(
        self,
        treasury_balance: float,
        daily_net_change: float
    ) -> tuple[Optional[float], Optional[date]]:
        """
        Compute runway from balance and daily change.

        Args:
            treasury_balance: Current treasury size
            daily_net_change: Daily net flow (positive = growing, negative = bleeding)

        Returns:
            Tuple of (runway_days, death_date)
            Both None if sustainable (positive net change)
        """
        # If net change is positive or zero, treasury is sustainable
        if daily_net_change >= 0:
            return None, None

        # If bleeding money, compute runway
        # days_until_death = treasury / abs(daily_burn)
        runway_days = treasury_balance / abs(daily_net_change)

        # Compute death date
        death_date = date.today() + timedelta(days=int(runway_days))

        return runway_days, death_date

    def compute_runway(self, inputs: RunwayInputs) -> RunwayResult:
        """
        Compute runway for baseline and optionally optimized config.

        Args:
            inputs: Runway input parameters

        Returns:
            RunwayResult with baseline and optional optimized projections

        Example:
            >>> projector = RunwayProjector()
            >>> inputs = RunwayInputs(
            ...     treasury_start_asset0=100000,
            ...     daily_net_change_asset0=-500,  # Losing $500/day
            ...     daily_net_change_asset0_optimized=200,  # Would earn $200/day
            ... )
            >>> result = projector.compute_runway(inputs)
            >>> print(f"Baseline runway: {result.baseline_runway_days:.0f} days")
            >>> print(f"Dies on: {result.baseline_death_date}")
        """
        # Compute baseline runway
        baseline_runway, baseline_death = self.compute_runway_simple(
            inputs.treasury_start_asset0,
            inputs.daily_net_change_asset0
        )

        # Compute optimized runway (if provided)
        optimized_runway = None
        optimized_death = None
        runway_extension = None

        if inputs.daily_net_change_asset0_optimized is not None:
            optimized_runway, optimized_death = self.compute_runway_simple(
                inputs.treasury_start_asset0,
                inputs.daily_net_change_asset0_optimized
            )

            # Compute extension
            if baseline_runway is not None:
                if optimized_runway is None:
                    # Baseline dies, optimized is sustainable → infinite extension
                    runway_extension = float('inf')
                else:
                    # Both finite → compute delta
                    runway_extension = optimized_runway - baseline_runway
            else:
                # Baseline is sustainable
                if optimized_runway is not None:
                    # Optimized is worse (finite runway) → negative extension
                    runway_extension = -optimized_runway
                else:
                    # Both sustainable → no change
                    runway_extension = 0.0

        return RunwayResult(
            baseline_runway_days=baseline_runway,
            baseline_death_date=baseline_death,
            optimized_runway_days=optimized_runway,
            optimized_death_date=optimized_death,
            runway_extension_days=runway_extension,
        )

    def compute_from_baseline(
        self,
        baseline_metrics: 'BaselineMetrics',
        optimized_metrics: Optional[dict] = None,
        treasury_balance: float = None,
    ) -> RunwayResult:
        """
        Compute runway from baseline metrics (convenience wrapper).

        Args:
            baseline_metrics: BaselineMetrics from Phase A
            optimized_metrics: Optional metrics dict from optimized RunResult
            treasury_balance: Current treasury balance (required)

        Returns:
            RunwayResult

        Raises:
            ValueError: If treasury_balance not provided
        """
        if treasury_balance is None:
            raise ValueError(
                "treasury_balance required for runway projection. "
                "Protocol must provide current treasury size."
            )

        # Get baseline daily change
        daily_change_baseline = baseline_metrics.daily_net_treasury_change or 0.0

        # Get optimized daily change (if available)
        daily_change_optimized = None
        if optimized_metrics:
            # Try to infer from metrics
            # This is a simplified version - real implementation would need
            # to compute daily burn rate from optimized config
            daily_change_optimized = optimized_metrics.get('daily_net_treasury_change')

        inputs = RunwayInputs(
            treasury_start_asset0=treasury_balance,
            daily_net_change_asset0=daily_change_baseline,
            daily_net_change_asset0_optimized=daily_change_optimized,
        )

        return self.compute_runway(inputs)
