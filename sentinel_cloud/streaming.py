"""
Streaming & Shadow-Node Mode - Phase 7

Enables continuous monitoring of live protocol economics with
real-time simulations, alerts, and shadow-node testing.

Usage:
    from sentinel_cloud.streaming import StreamProcessor, TumblingWindow, AlertRule

    # Create processor with 1000-tx tumbling window
    processor = StreamProcessor(
        window=TumblingWindow(size=1000),
        mapper='solana',
        fee_bps=50
    )

    # Add alert rules
    processor.add_alert(AlertRule.treasury_runway(threshold_days=90))
    processor.add_alert(AlertRule.role_imbalance())

    # Ingest transactions
    for tx in live_stream:
        result = processor.ingest(tx)
        if result:
            print(f"Simulation complete: {result.summary}")

    # Shadow-node mode: compare multiple fee configs
    shadow = ShadowNode(
        window=TumblingWindow(size=1000),
        mapper='solana',
        configs=[
            Config("Current", fee_bps_asset0=50),
            Config("Lower", fee_bps_asset0=25),
            Config("Higher", fee_bps_asset0=100),
        ]
    )
"""

from dataclasses import dataclass, field
from typing import List, Optional, Callable, Dict, Any
from enum import Enum
from datetime import datetime
import json
from pathlib import Path

from .schema import SentinelTx
from .experiment import Config, run_scenario, RunResult
from .role_economics import TreasuryConfig, calculate_simulation_days


class WindowStrategy(Enum):
    """Window strategy for stream processing."""
    TUMBLING = "tumbling"  # Non-overlapping fixed-size windows
    SLIDING = "sliding"    # Overlapping windows that slide on each tx
    SESSION = "session"    # Time-based session windows (gap-triggered)


@dataclass
class Window:
    """
    Base window configuration for stream processing.

    Attributes:
        strategy: Window strategy (tumbling, sliding, session)
        size: Number of transactions per window
        slide: Slide amount for sliding windows (default: size for tumbling)
        gap_seconds: Max gap between txs for session windows
    """
    strategy: WindowStrategy
    size: int = 1000
    slide: Optional[int] = None
    gap_seconds: Optional[int] = None

    def __post_init__(self):
        if self.strategy == WindowStrategy.TUMBLING and self.slide is None:
            self.slide = self.size  # Non-overlapping
        elif self.strategy == WindowStrategy.SLIDING and self.slide is None:
            self.slide = 1  # Slide by 1 transaction

        if self.size <= 0:
            raise ValueError(f"Window size must be > 0, got {self.size}")
        if self.slide and self.slide <= 0:
            raise ValueError(f"Slide must be > 0, got {self.slide}")


def TumblingWindow(size: int = 1000) -> Window:
    """Create a tumbling (non-overlapping) window."""
    return Window(strategy=WindowStrategy.TUMBLING, size=size, slide=size)


def SlidingWindow(size: int = 1000, slide: int = 100) -> Window:
    """Create a sliding (overlapping) window."""
    return Window(strategy=WindowStrategy.SLIDING, size=size, slide=slide)


def SessionWindow(gap_seconds: int = 300) -> Window:
    """Create a session window (time-based, gap-triggered)."""
    return Window(strategy=WindowStrategy.SESSION, size=0, gap_seconds=gap_seconds)


@dataclass
class AlertRule:
    """
    Alert rule for monitoring simulation results.

    Attributes:
        name: Human-readable alert name
        condition: Function that takes RunResult and returns (triggered: bool, message: str)
        severity: Alert severity (info, warning, error, critical)
    """
    name: str
    condition: Callable[[RunResult], tuple[bool, str]]
    severity: str = "warning"

    @staticmethod
    def treasury_runway(threshold_days: int = 90, severity: str = "error") -> 'AlertRule':
        """Alert if treasury runway falls below threshold."""
        def check(result: RunResult) -> tuple[bool, str]:
            if not result.treasury_state:
                return False, ""

            runway = result.treasury_state.get('runway_days')
            if runway is not None and runway < threshold_days:
                return True, f"🚨 Treasury depletes in {runway:.0f} days (< {threshold_days} day threshold)"
            return False, ""

        return AlertRule(f"Treasury Runway < {threshold_days}d", check, severity)

    @staticmethod
    def role_imbalance(severity: str = "warning") -> 'AlertRule':
        """Alert if any role has negative net revenue."""
        def check(result: RunResult) -> tuple[bool, str]:
            if not result.role_metrics:
                return False, ""

            negative_roles = [
                role for role, metrics in result.role_metrics.items()
                if metrics.get('net_revenue', 0) < 0
            ]

            if negative_roles:
                roles_str = ", ".join(negative_roles)
                return True, f"⚠️  Role imbalance: {roles_str} have negative net revenue"
            return False, ""

        return AlertRule("Role Economic Imbalance", check, severity)

    @staticmethod
    def high_failure_rate(threshold: float = 0.01, severity: str = "error") -> 'AlertRule':
        """Alert if failure rate exceeds threshold."""
        def check(result: RunResult) -> tuple[bool, str]:
            failure_rate = result.get_metric('failure_rate', 0.0)
            if failure_rate > threshold:
                return True, f"🔴 High failure rate: {failure_rate*100:.2f}% (> {threshold*100:.1f}%)"
            return False, ""

        return AlertRule(f"Failure Rate > {threshold*100:.1f}%", check, severity)

    @staticmethod
    def revenue_drop(threshold_pct: float = 20.0, severity: str = "warning") -> 'AlertRule':
        """Alert if revenue drops by more than threshold% from baseline."""
        baseline_revenue: Optional[float] = None

        def check(result: RunResult) -> tuple[bool, str]:
            nonlocal baseline_revenue
            current_revenue = result.get_metric('rev_usdc', 0.0)

            if baseline_revenue is None:
                baseline_revenue = current_revenue
                return False, ""

            if baseline_revenue > 0:
                drop_pct = (baseline_revenue - current_revenue) / baseline_revenue * 100
                if drop_pct > threshold_pct:
                    return True, f"📉 Revenue dropped {drop_pct:.1f}% from baseline (${baseline_revenue:,.0f} → ${current_revenue:,.0f})"

            return False, ""

        return AlertRule(f"Revenue Drop > {threshold_pct}%", check, severity)


@dataclass
class StreamState:
    """
    State for stream processing (for checkpointing/resume).

    Attributes:
        window_count: Number of windows processed
        tx_count: Total transactions ingested
        last_checkpoint: Timestamp of last checkpoint
        alerts_triggered: Total alerts triggered
    """
    window_count: int = 0
    tx_count: int = 0
    last_checkpoint: datetime = field(default_factory=datetime.now)
    alerts_triggered: int = 0

    def to_dict(self) -> dict:
        """Export state for checkpointing."""
        return {
            'window_count': self.window_count,
            'tx_count': self.tx_count,
            'last_checkpoint': self.last_checkpoint.isoformat(),
            'alerts_triggered': self.alerts_triggered
        }

    @classmethod
    def from_dict(cls, data: dict) -> 'StreamState':
        """Restore state from checkpoint."""
        return cls(
            window_count=data.get('window_count', 0),
            tx_count=data.get('tx_count', 0),
            last_checkpoint=datetime.fromisoformat(data.get('last_checkpoint', datetime.now().isoformat())),
            alerts_triggered=data.get('alerts_triggered', 0)
        )


class StreamProcessor:
    """
    Stream processor for continuous simulation on live data.

    Ingests transactions incrementally, maintains windowed buffers,
    triggers simulations, and emits alerts.

    Example:
        processor = StreamProcessor(
            window=TumblingWindow(size=1000),
            mapper='solana',
            fee_bps=50
        )

        processor.add_alert(AlertRule.treasury_runway(90))

        for tx in stream:
            result = processor.ingest(tx)
            if result:
                print(f"Window {result.window_id} complete")
    """

    def __init__(
        self,
        window: Window,
        mapper: str,
        fee_bps: int = 50,
        verbose: bool = False,
        checkpoint_dir: Optional[str] = None
    ):
        """
        Initialize stream processor.

        Args:
            window: Window configuration
            mapper: Protocol mapper name
            fee_bps: Fee in basis points
            verbose: Print detailed logs
            checkpoint_dir: Directory for checkpointing state
        """
        self.window = window
        self.mapper = mapper
        self.config = Config(name="Stream", fee_bps_asset0=fee_bps)
        self.verbose = verbose
        self.checkpoint_dir = Path(checkpoint_dir) if checkpoint_dir else None

        self.buffer: List[SentinelTx] = []
        self.alert_rules: List[AlertRule] = []
        self.state = StreamState()
        self.last_result: Optional[RunResult] = None

        if self.checkpoint_dir:
            self.checkpoint_dir.mkdir(parents=True, exist_ok=True)
            self._load_checkpoint()

    def add_alert(self, rule: AlertRule):
        """Add an alert rule to the processor."""
        self.alert_rules.append(rule)
        if self.verbose:
            print(f"📍 Added alert: {rule.name} [{rule.severity}]")

    def ingest(self, tx: SentinelTx) -> Optional[Dict[str, Any]]:
        """
        Ingest a single transaction.

        Returns:
            Simulation result dict if window triggered, None otherwise
        """
        self.buffer.append(tx)
        self.state.tx_count += 1

        # Check if window is complete
        if self._should_trigger_window():
            return self._process_window()

        return None

    def ingest_batch(self, transactions: List[SentinelTx]) -> List[Dict[str, Any]]:
        """
        Ingest a batch of transactions.

        Returns:
            List of simulation results for each completed window
        """
        results = []
        for tx in transactions:
            result = self.ingest(tx)
            if result:
                results.append(result)
        return results

    def _should_trigger_window(self) -> bool:
        """Check if current window should trigger a simulation."""
        if self.window.strategy == WindowStrategy.TUMBLING:
            return len(self.buffer) >= self.window.size
        elif self.window.strategy == WindowStrategy.SLIDING:
            return len(self.buffer) >= self.window.size
        elif self.window.strategy == WindowStrategy.SESSION:
            # Check time gap between last two transactions
            if len(self.buffer) >= 2:
                gap = self.buffer[-1].timestamp - self.buffer[-2].timestamp
                return gap > self.window.gap_seconds
        return False

    def _process_window(self) -> Dict[str, Any]:
        """Process current window and emit alerts."""
        window_txs = self.buffer[:self.window.size] if self.window.size > 0 else self.buffer
        self.state.window_count += 1

        if self.verbose:
            print(f"\n🔄 Processing window {self.state.window_count} ({len(window_txs)} txs)")

        # Run simulation on window
        try:
            result = run_scenario(
                scenario_path="",  # Not used when transactions provided
                mapper=self.mapper,
                config=self.config,
                verbose=False,
                transactions=window_txs  # Pass transactions directly for streaming
            )

            self.last_result = result

            # Check alert rules
            alerts = self._check_alerts(result)

            # Slide window
            self._slide_window()

            # Checkpoint periodically
            if self.state.window_count % 10 == 0 and self.checkpoint_dir:
                self._save_checkpoint()

            return {
                'window_id': self.state.window_count,
                'tx_count': len(window_txs),
                'result': result,
                'alerts': alerts
            }

        except Exception as e:
            if self.verbose:
                print(f"❌ Window processing failed: {e}")
            self._slide_window()
            return {
                'window_id': self.state.window_count,
                'tx_count': len(window_txs),
                'error': str(e)
            }

    def _check_alerts(self, result: RunResult) -> List[Dict[str, str]]:
        """Check all alert rules and emit triggered alerts."""
        alerts = []
        for rule in self.alert_rules:
            try:
                triggered, message = rule.condition(result)
                if triggered:
                    self.state.alerts_triggered += 1
                    alert = {
                        'rule': rule.name,
                        'severity': rule.severity,
                        'message': message,
                        'timestamp': datetime.now().isoformat()
                    }
                    alerts.append(alert)

                    if self.verbose:
                        print(f"  {message}")

                    # Log alert to file if checkpoint dir exists
                    if self.checkpoint_dir:
                        self._log_alert(alert)

            except Exception as e:
                if self.verbose:
                    print(f"  ⚠️  Alert check failed for '{rule.name}': {e}")

        return alerts

    def _slide_window(self):
        """Slide the window buffer."""
        if self.window.slide:
            self.buffer = self.buffer[self.window.slide:]
        else:
            self.buffer = []

    def _save_checkpoint(self):
        """Save current state to checkpoint file."""
        if not self.checkpoint_dir:
            return

        checkpoint_path = self.checkpoint_dir / "stream_state.json"
        with open(checkpoint_path, 'w') as f:
            json.dump(self.state.to_dict(), f, indent=2)

        if self.verbose:
            print(f"💾 Checkpoint saved: {checkpoint_path}")

    def _load_checkpoint(self):
        """Load state from checkpoint file."""
        if not self.checkpoint_dir:
            return

        checkpoint_path = self.checkpoint_dir / "stream_state.json"
        if checkpoint_path.exists():
            with open(checkpoint_path, 'r') as f:
                data = json.load(f)
                self.state = StreamState.from_dict(data)

            if self.verbose:
                print(f"📂 Checkpoint loaded: {self.state.window_count} windows, {self.state.tx_count} txs")

    def _log_alert(self, alert: Dict[str, str]):
        """Log alert to file."""
        if not self.checkpoint_dir:
            return

        alerts_path = self.checkpoint_dir / "alerts.jsonl"
        with open(alerts_path, 'a') as f:
            f.write(json.dumps(alert) + '\n')

    def get_stats(self) -> Dict[str, Any]:
        """Get current streaming statistics."""
        return {
            'windows_processed': self.state.window_count,
            'transactions_ingested': self.state.tx_count,
            'alerts_triggered': self.state.alerts_triggered,
            'buffer_size': len(self.buffer),
            'last_checkpoint': self.state.last_checkpoint.isoformat()
        }


class ShadowNode:
    """
    Shadow-node mode: run multiple configs in parallel on same stream.

    Simulates alternative fee structures on live data to answer:
    "What if we had used X% fees instead of Y%?"

    Example:
        shadow = ShadowNode(
            window=TumblingWindow(1000),
            mapper='solana',
            configs=[
                Config("Current", fee_bps_asset0=50),
                Config("Lower", fee_bps_asset0=25),
                Config("Higher", fee_bps_asset0=100),
            ]
        )

        for tx in stream:
            results = shadow.ingest(tx)
            if results:
                for cfg, result in results.items():
                    print(f"{cfg}: ${result.get_metric('rev_usdc'):,.0f}")
    """

    def __init__(
        self,
        window: Window,
        mapper: str,
        configs: List[Config],
        verbose: bool = False
    ):
        """
        Initialize shadow node with multiple configs.

        Args:
            window: Window configuration
            mapper: Protocol mapper
            configs: List of configurations to test in parallel
            verbose: Print detailed logs
        """
        self.processors = {
            config.name: StreamProcessor(window, mapper, config.fee_bps_asset0, verbose=False)
            for config in configs
        }
        self.verbose = verbose

    def ingest(self, tx: SentinelTx) -> Optional[Dict[str, RunResult]]:
        """
        Ingest transaction into all processors.

        Returns:
            Dict of config_name → result if any window triggered, None otherwise
        """
        results = {}
        for name, processor in self.processors.items():
            result = processor.ingest(tx)
            if result and result.get('result'):
                results[name] = result['result']

        return results if results else None

    def get_comparison(self) -> Dict[str, Dict[str, Any]]:
        """Get comparison of all configs."""
        comparison = {}
        for name, processor in self.processors.items():
            if processor.last_result:
                comparison[name] = {
                    'revenue_usdc': processor.last_result.get_metric('rev_usdc'),
                    'volume_usdc': processor.last_result.get_metric('vol_usdc'),
                    'failure_rate': processor.last_result.get_metric('failure_rate'),
                    'lab_tps': processor.last_result.get_metric('lab_tps'),
                }
        return comparison
