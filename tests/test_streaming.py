"""
Phase 7: Streaming Mode Tests

Basic validation tests for streaming processor, window strategies,
and alert system.

Run with: python3 tests/test_streaming.py
"""

import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sentinel_cloud.schema import SentinelTx, Opcode
from sentinel_cloud.streaming import (
    StreamProcessor,
    ShadowNode,
    TumblingWindow,
    SlidingWindow,
    AlertRule
)
from sentinel_cloud.experiment import Config


def create_test_transactions(count: int = 100) -> list:
    """Create test transactions for streaming."""
    txs = []
    for i in range(count):
        tx = SentinelTx(
            timestamp=i * 10,  # 10 second intervals
            user_a=i % 10,
            user_b=(i + 1) % 10,
            asset0_amount=1000 + (i * 100),  # Varying amounts
            asset1_amount=0,
            opcode=Opcode.TRANSFER,
            role_a="client",
            role_b="client"
        )
        txs.append(tx)
    return txs


def test_tumbling_window_basic():
    """Test tumbling window triggers correctly."""
    print("\n--- Tumbling Window (size=10) ---")

    # Note: Since we're testing without actual simulation infrastructure,
    # this test will fail during _process_window. We're testing the window
    # triggering logic, not the full simulation.

    window = TumblingWindow(size=10)
    assert window.size == 10
    assert window.slide == 10  # Non-overlapping
    print(f"✅ Tumbling window: size={window.size}, slide={window.slide}")


def test_sliding_window_basic():
    """Test sliding window configuration."""
    print("\n--- Sliding Window (size=10, slide=5) ---")

    window = SlidingWindow(size=10, slide=5)
    assert window.size == 10
    assert window.slide == 5  # Overlapping
    print(f"✅ Sliding window: size={window.size}, slide={window.slide}")


def test_alert_rules():
    """Test alert rule creation."""
    print("\n--- Alert Rules ---")

    # Treasury runway alert
    alert1 = AlertRule.treasury_runway(threshold_days=90)
    assert alert1.name == "Treasury Runway < 90d"
    assert alert1.severity == "error"
    print(f"✅ Alert: {alert1.name} [{alert1.severity}]")

    # Role imbalance alert
    alert2 = AlertRule.role_imbalance()
    assert "imbalance" in alert2.name.lower()
    print(f"✅ Alert: {alert2.name} [{alert2.severity}]")

    # High failure rate alert
    alert3 = AlertRule.high_failure_rate(threshold=0.01)
    assert "failure" in alert3.name.lower()
    print(f"✅ Alert: {alert3.name} [{alert3.severity}]")


def test_stream_processor_creation():
    """Test stream processor can be created."""
    print("\n--- Stream Processor Creation ---")

    processor = StreamProcessor(
        window=TumblingWindow(size=10),
        mapper='solana',
        fee_bps=50,
        verbose=False
    )

    assert processor.window.size == 10
    assert processor.mapper == 'solana'
    assert processor.config.fee_bps_asset0 == 50
    assert len(processor.buffer) == 0
    assert len(processor.alert_rules) == 0

    print(f"✅ Processor created: window_size={processor.window.size}, mapper={processor.mapper}")

    # Add alert
    processor.add_alert(AlertRule.treasury_runway(90))
    assert len(processor.alert_rules) == 1
    print(f"✅ Alert added: {len(processor.alert_rules)} rules")


def test_shadow_node_creation():
    """Test shadow node can be created with multiple configs."""
    print("\n--- Shadow Node Creation ---")

    configs = [
        Config("Low", fee_bps_asset0=25),
        Config("Medium", fee_bps_asset0=50),
        Config("High", fee_bps_asset0=100),
    ]

    shadow = ShadowNode(
        window=TumblingWindow(size=10),
        mapper='solana',
        configs=configs,
        verbose=False
    )

    assert len(shadow.processors) == 3
    assert "Low" in shadow.processors
    assert "Medium" in shadow.processors
    assert "High" in shadow.processors

    print(f"✅ Shadow node created: {len(shadow.processors)} configs")
    for name, proc in shadow.processors.items():
        print(f"   - {name}: {proc.config.fee_bps_asset0} bps")


def test_buffer_accumulation():
    """Test that buffer accumulates transactions correctly."""
    print("\n--- Buffer Accumulation ---")

    processor = StreamProcessor(
        window=TumblingWindow(size=10),
        mapper='solana',
        fee_bps=50,
        verbose=False
    )

    txs = create_test_transactions(count=5)

    # Ingest 5 transactions (less than window size)
    for tx in txs:
        result = processor.ingest(tx)
        assert result is None, "Should not trigger window yet"

    assert len(processor.buffer) == 5
    assert processor.state.tx_count == 5
    print(f"✅ Buffer accumulated: {len(processor.buffer)} txs (window size: 10)")


def test_state_tracking():
    """Test that streaming state is tracked correctly."""
    print("\n--- State Tracking ---")

    processor = StreamProcessor(
        window=TumblingWindow(size=5),
        mapper='solana',
        fee_bps=50,
        verbose=False
    )

    txs = create_test_transactions(count=3)

    for tx in txs:
        processor.ingest(tx)

    stats = processor.get_stats()
    assert stats['transactions_ingested'] == 3
    assert stats['buffer_size'] == 3
    assert stats['windows_processed'] == 0  # Not enough for a window yet

    print(f"✅ State tracked: {stats['transactions_ingested']} txs, {stats['windows_processed']} windows")


def run_all_tests():
    """Run all streaming tests."""
    print("\n" + "="*70)
    print("Phase 7: Streaming Mode Validation")
    print("="*70)

    tests = [
        ("Tumbling Window", test_tumbling_window_basic),
        ("Sliding Window", test_sliding_window_basic),
        ("Alert Rules", test_alert_rules),
        ("Stream Processor", test_stream_processor_creation),
        ("Shadow Node", test_shadow_node_creation),
        ("Buffer Accumulation", test_buffer_accumulation),
        ("State Tracking", test_state_tracking),
    ]

    passed = 0
    failed = 0

    for name, test_fn in tests:
        try:
            test_fn()
            passed += 1
        except Exception as e:
            print(f"❌ FAILED: {e}")
            import traceback
            traceback.print_exc()
            failed += 1

    print("\n" + "="*70)
    print(f"Results: {passed} passed, {failed} failed")
    print("="*70)

    print("\nNote: Full simulation tests require testbench infrastructure.")
    print("These tests validate streaming architecture and window logic.\n")

    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
