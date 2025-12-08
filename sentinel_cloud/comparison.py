"""
Before/After Comparison - Compare baseline vs optimized configurations.

This module provides tools to compare actual mainnet performance (baseline)
against simulated optimized configurations to quantify improvements.

This is where the "money left on table" message comes from.
"""

from dataclasses import dataclass
from typing import Optional
from .baseline import BaselineMetrics
from .experiment import RunResult
from .death_clock import RunwayProjector, RunwayInputs


@dataclass
class ComparisonResult:
    """
    Results of comparing baseline vs optimized configuration.

    This is the "show me the money" object - quantifies exactly how much
    better an optimized config performs vs what actually happened.

    Carries raw objects so Phase C (Death Clock) and Phase D (Safety Scanner)
    can attach additional analysis without reshuffling data.
    """

    # Raw source objects - Phase C/D/E will need these
    baseline: BaselineMetrics
    optimized_run: RunResult
    optimized_config_label: str

    # Revenue comparison - The headline numbers
    baseline_revenue_asset0: float
    optimized_revenue_asset0: float
    additional_revenue_asset0: float
    pct_improvement_revenue: float

    # Is this actually better?
    is_improvement: bool  # True if optimized >= baseline (even if both zero)

    # Failure rate comparison (if available)
    baseline_failure_rate: Optional[float] = None
    optimized_failure_rate: Optional[float] = None
    failure_delta: Optional[float] = None

    # Runway comparison (filled by Phase C - Death Clock)
    baseline_runway_days: Optional[float] = None
    optimized_runway_days: Optional[float] = None
    runway_extension_days: Optional[float] = None

    def summary(self, include_runway: bool = True) -> str:
        """
        Generate one-line executive summary.

        Args:
            include_runway: Include runway extension in summary if available

        Returns:
            Human-readable summary of improvement
        """
        # Base revenue summary
        if not self.is_improvement:
            msg = (
                f"With {self.optimized_config_label}: "
                f"${self.additional_revenue_asset0:,.0f}/day "
                f"({self.pct_improvement_revenue:+.1f}%) - WORSE than baseline"
            )
        else:
            msg = (
                f"With {self.optimized_config_label}: "
                f"+${self.additional_revenue_asset0:,.0f}/day "
                f"({self.pct_improvement_revenue:+.1f}%)"
            )

        # Add runway extension if available
        if include_runway and self.runway_extension_days is not None:
            if self.runway_extension_days == float('inf'):
                msg += " | Runway: ∞ (sustainable)"
            elif self.runway_extension_days > 0:
                msg += f" | +{self.runway_extension_days:.0f} days runway"
            elif self.runway_extension_days < 0:
                msg += f" | {self.runway_extension_days:.0f} days runway (worse)"
            # else: extension == 0, both sustainable, don't clutter message

        return msg


class ComparisonEngine:
    """Compare baseline vs optimized configurations."""

    def compare(
        self,
        baseline: BaselineMetrics,
        optimized: RunResult,
        config_label: str = "",
        treasury_balance: Optional[float] = None
    ) -> ComparisonResult:
        """
        Compare baseline metrics vs optimized simulation result.

        This is the core "before/after" logic that quantifies improvement.

        Args:
            baseline: Actual mainnet metrics (what really happened)
            optimized: Simulation result from optimized config
            config_label: Human-readable config description (e.g., "50 bps")
            treasury_balance: Current treasury balance for runway projection (optional)

        Returns:
            ComparisonResult with improvement metrics and optional runway projection

        Example:
            >>> engine = ComparisonEngine()
            >>> result = engine.compare(baseline, best_run, "50 bps", treasury_balance=100000)
            >>> print(result.summary())
            With 50 bps: +$1,234/day (+45.2%) | +147 days runway
        """
        # Extract baseline revenue
        # Use fees if available, else try to estimate from volume/treasury change
        baseline_revenue = baseline.total_fees_asset0 or 0.0

        # If no fees detected, try to estimate from daily treasury change
        if baseline_revenue == 0.0 and baseline.daily_net_treasury_change:
            # If treasury is growing, use that as proxy revenue
            if baseline.daily_net_treasury_change > 0:
                # Scale to total period
                if baseline.duration_seconds:
                    days = baseline.duration_seconds / 86400.0
                    baseline_revenue = baseline.daily_net_treasury_change * days

        # Extract optimized revenue from RunResult
        # RunResult.metrics should contain 'rev_usdc' or similar
        optimized_revenue = optimized.metrics.get('rev_usdc', 0.0)

        # If not found, try alternative metric names
        if optimized_revenue == 0.0:
            optimized_revenue = optimized.metrics.get('revenue_usdc', 0.0)
        if optimized_revenue == 0.0:
            optimized_revenue = optimized.metrics.get('protocol_revenue', 0.0)

        # Compute improvement
        additional_revenue = optimized_revenue - baseline_revenue
        pct_improvement = (
            (additional_revenue / baseline_revenue * 100.0)
            if baseline_revenue > 0
            else 0.0
        )

        # Is this actually better?
        is_improvement = optimized_revenue >= baseline_revenue

        # Failure rate comparison (if available)
        baseline_failure_rate = baseline.failure_rate
        optimized_failure_rate = optimized.metrics.get('failure_rate')

        failure_delta = None
        if baseline_failure_rate is not None and optimized_failure_rate is not None:
            failure_delta = optimized_failure_rate - baseline_failure_rate

        # Runway projection (optional - only if treasury_balance provided)
        baseline_runway_days = None
        optimized_runway_days = None
        runway_extension_days = None

        if treasury_balance is not None:
            # Get daily treasury changes
            baseline_daily_change = baseline.daily_net_treasury_change or 0.0
            optimized_daily_change = optimized.metrics.get('daily_net_treasury_change')

            if optimized_daily_change is not None:
                # Compute runway for both configs
                projector = RunwayProjector()
                inputs = RunwayInputs(
                    treasury_start_asset0=treasury_balance,
                    daily_net_change_asset0=baseline_daily_change,
                    daily_net_change_asset0_optimized=optimized_daily_change,
                )
                runway_result = projector.compute_runway(inputs)

                baseline_runway_days = runway_result.baseline_runway_days
                optimized_runway_days = runway_result.optimized_runway_days
                runway_extension_days = runway_result.runway_extension_days

        return ComparisonResult(
            baseline=baseline,
            optimized_run=optimized,
            optimized_config_label=config_label,
            baseline_revenue_asset0=baseline_revenue,
            optimized_revenue_asset0=optimized_revenue,
            additional_revenue_asset0=additional_revenue,
            pct_improvement_revenue=pct_improvement,
            is_improvement=is_improvement,
            baseline_failure_rate=baseline_failure_rate,
            optimized_failure_rate=optimized_failure_rate,
            failure_delta=failure_delta,
            baseline_runway_days=baseline_runway_days,
            optimized_runway_days=optimized_runway_days,
            runway_extension_days=runway_extension_days,
        )

    def find_best_improvement(
        self,
        baseline: BaselineMetrics,
        runs: list[RunResult],
        treasury_balance: Optional[float] = None
    ) -> ComparisonResult:
        """
        Find the configuration with the best improvement over baseline.

        Args:
            baseline: Baseline metrics
            runs: List of simulation results to compare
            treasury_balance: Current treasury balance for runway projection (optional)

        Returns:
            ComparisonResult for the best configuration

        Example:
            >>> engine = ComparisonEngine()
            >>> best = engine.find_best_improvement(baseline, experiment.runs, treasury_balance=100000)
            >>> print(f"Best config: {best.optimized_config_label}")
        """
        if not runs:
            raise ValueError("No simulation results to compare")

        # Find run with highest revenue
        best_run = max(runs, key=lambda r: r.metrics.get('rev_usdc', 0.0))

        # Generate label from config
        config_label = best_run.config.name or f"{best_run.config.fee_bps_asset0} bps"

        return self.compare(baseline, best_run, config_label, treasury_balance)
