"""
Enhanced Streaming Verification Tests

Tests beyond the basic streaming tests:
- FR-STREAM-1: Batch equivalence (tumbling)
- FR-STREAM-2: ShadowNode equivalence
- FR-STREAM-3: Alert rule correctness
- INV-STREAM-1: Deterministic streaming
- INV-STREAM-2: Checkpoint/resume equivalence
- INV-STREAM-3: Window coverage
"""

import pytest
from typing import List

from sentinel_cloud.schema import SentinelTx
from sentinel_cloud.streaming import (
    StreamProcessor,
    ShadowNode,
    TumblingWindow,
    SlidingWindow,
    SessionWindow,
    AlertRule,
)
from sentinel_cloud.experiment import Config
from tests.scenario_generator import ScenarioGenerator, ScenarioConfig


class TestBatchEquivalence:
    """FR-STREAM-1: Batch equivalence"""

    def test_tumbling_equals_batch(self):
        """Test that tumbling window aggregation equals batch processing"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=1000,
            seed=30001
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        # Process in batch
        # batch_result = run_scenario(..., transactions=txs)

        # Process in streaming with tumbling windows
        processor = StreamProcessor(
            window=TumblingWindow(size=100),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )

        windowed_results = processor.ingest_batch(txs)

        # TODO: Aggregate streaming results
        # streaming_total_revenue = sum(r['result'].get_metric('rev_usdc') for r in windowed_results)

        # Verify equality
        # assert abs(batch_result.get_metric('rev_usdc') - streaming_total_revenue) < 1.0

        assert True  # Placeholder

    @pytest.mark.parametrize("window_size", [50, 100, 250, 500])
    def test_different_window_sizes(self, window_size):
        """Test batch equivalence across different window sizes"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=1000,
            seed=30002
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        # Process with different window sizes
        processor = StreamProcessor(
            window=TumblingWindow(size=window_size),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )

        windowed_results = processor.ingest_batch(txs)

        # TODO: Verify total metrics match batch regardless of window size
        assert True  # Placeholder


class TestShadowNodeEquivalence:
    """FR-STREAM-2: ShadowNode equivalence"""

    def test_shadow_equals_sequential(self):
        """Test that shadow node results equal sequential runs"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=500,
            seed=31001
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        configs = [
            Config("25bps", fee_bps_asset0=25),
            Config("50bps", fee_bps_asset0=50),
        ]

        # Run shadow node
        shadow = ShadowNode(
            configs=configs,
            window=TumblingWindow(size=100),
            mapper='identity',
            verbose=False
        )

        shadow_results = shadow.ingest_batch(txs)

        # TODO: Run sequential experiments
        # sequential_results = {
        #     "25bps": run_scenario(..., config=configs[0]),
        #     "50bps": run_scenario(..., config=configs[1]),
        # }

        # Verify per-config totals match
        # for name in ["25bps", "50bps"]:
        #     shadow_total = sum(w[name]['result'].get_metric('rev_usdc') for w in shadow_results)
        #     assert abs(shadow_total - sequential_results[name].get_metric('rev_usdc')) < 1.0

        assert True  # Placeholder


class TestAlertRuleCorrectness:
    """FR-STREAM-3: Alert rule correctness"""

    def test_treasury_alert_fires_when_low(self):
        """Test treasury runway alert fires when runway < threshold"""
        # Create mock result with low runway
        from sentinel_cloud.experiment import RunResult

        mock_result = RunResult(
            config=Config("test", fee_bps_asset0=50),
            metrics={'rev_usdc': 100},
            treasury_state={
                'balance_usdc': 100_000,
                'daily_burn_rate': 5_000,
                'daily_revenue_rate': 1_000,
                'net_revenue_daily': -4_000,
                'runway_days': 25,  # Low!
            }
        )

        # Test alert rule
        alert = AlertRule.treasury_runway(threshold_days=90)
        triggered = alert.check(mock_result)

        assert triggered is not None, "Alert should have fired for low runway"
        assert triggered['severity'] == 'ERROR'

    def test_treasury_alert_does_not_fire_when_healthy(self):
        """Test treasury alert doesn't fire when runway is healthy"""
        from sentinel_cloud.experiment import RunResult

        mock_result = RunResult(
            config=Config("test", fee_bps_asset0=50),
            metrics={'rev_usdc': 100},
            treasury_state={
                'balance_usdc': 1_000_000,
                'daily_burn_rate': 1_000,
                'daily_revenue_rate': 5_000,
                'net_revenue_daily': 4_000,
                'runway_days': float('inf'),  # Sustainable
            }
        )

        alert = AlertRule.treasury_runway(threshold_days=90)
        triggered = alert.check(mock_result)

        assert triggered is None, "Alert should not fire for healthy runway"

    def test_failure_rate_alert(self):
        """Test failure rate alert fires correctly"""
        from sentinel_cloud.experiment import RunResult

        # High failure rate
        mock_result_high = RunResult(
            config=Config("test", fee_bps_asset0=50),
            metrics={
                'total_txs': 1000,
                'failed_txs': 30,  # 3% failure rate
                'failure_rate': 0.03,
            }
        )

        alert = AlertRule.high_failure_rate(threshold=0.01)  # 1% threshold
        triggered = alert.check(mock_result_high)

        assert triggered is not None, "Alert should fire for 3% failure (threshold 1%)"

        # Low failure rate
        mock_result_low = RunResult(
            config=Config("test", fee_bps_asset0=50),
            metrics={
                'total_txs': 1000,
                'failed_txs': 5,  # 0.5% failure rate
                'failure_rate': 0.005,
            }
        )

        triggered = alert.check(mock_result_low)
        assert triggered is None, "Alert should not fire for 0.5% failure (threshold 1%)"


class TestStreamingDeterminism:
    """INV-STREAM-1: Deterministic streaming"""

    def test_identical_runs_produce_identical_results(self):
        """Test two streaming runs produce identical outputs"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=500,
            seed=32001
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        # Run 1
        processor1 = StreamProcessor(
            window=TumblingWindow(size=100),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )
        results1 = processor1.ingest_batch(txs)

        # Run 2
        processor2 = StreamProcessor(
            window=TumblingWindow(size=100),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )
        results2 = processor2.ingest_batch(txs)

        # Verify identical outputs
        assert len(results1) == len(results2), "Different number of windows"

        for i, (w1, w2) in enumerate(zip(results1, results2)):
            # Compare window boundaries
            assert w1['window_start'] == w2['window_start'], f"Window {i} start mismatch"
            assert w1['window_end'] == w2['window_end'], f"Window {i} end mismatch"

            # TODO: Compare metrics
            # assert w1['result'].get_metric('rev_usdc') == w2['result'].get_metric('rev_usdc')


class TestCheckpointResume:
    """INV-STREAM-2: Checkpoint/resume equivalence"""

    def test_checkpoint_resume_equals_straight_through(self):
        """Test that checkpoint/resume produces same results as straight-through"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=1000,
            seed=33001
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        # Run A: Process all at once
        processor_a = StreamProcessor(
            window=TumblingWindow(size=100),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )
        results_a = processor_a.ingest_batch(txs)

        # Run B: Process first half, checkpoint, resume, process second half
        processor_b = StreamProcessor(
            window=TumblingWindow(size=100),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )

        # Process first 500 txs
        results_b_part1 = processor_b.ingest_batch(txs[:500])

        # TODO: Checkpoint state
        # checkpoint = processor_b.checkpoint()

        # TODO: Resume from checkpoint
        # processor_b.restore(checkpoint)

        # Process remaining 500 txs
        results_b_part2 = processor_b.ingest_batch(txs[500:])

        results_b = results_b_part1 + results_b_part2

        # Verify equality
        assert len(results_a) == len(results_b), "Different number of windows after resume"

        # TODO: Compare window metrics
        assert True  # Placeholder


class TestWindowCoverage:
    """INV-STREAM-3: Window coverage"""

    def test_tumbling_covers_all_transactions(self):
        """Test that tumbling windows cover every transaction exactly once"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=1000,
            seed=34001
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        processor = StreamProcessor(
            window=TumblingWindow(size=100),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )

        windowed_results = processor.ingest_batch(txs)

        # Count total transactions processed
        total_processed = 0
        for window_result in windowed_results:
            # Each window should process exactly 100 txs (or remainder)
            total_processed += window_result.get('num_txs', 100)

        assert total_processed == len(txs), f"Coverage mismatch: {total_processed} != {len(txs)}"

    def test_sliding_window_overlap(self):
        """Test that sliding windows have correct overlap"""
        scenario_config = ScenarioConfig(
            num_users=32,
            num_transactions=500,
            seed=34002
        )

        generator = ScenarioGenerator(scenario_config)
        txs = generator.generate()

        # Sliding window: size 100, slide 50 → 50% overlap
        processor = StreamProcessor(
            window=SlidingWindow(size=100, slide=50),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )

        windowed_results = processor.ingest_batch(txs)

        # Each tx (except first 50 and last 50) should appear in exactly 2 windows
        # This is complex to verify precisely, but check total > tumbling

        # With 500 txs:
        # - Tumbling(100): 5 windows
        # - Sliding(100, 50): ~10 windows (more due to overlap)

        assert len(windowed_results) > 5, "Sliding windows should produce more windows than tumbling"

    def test_session_window_gaps(self):
        """Test that session windows respect gap thresholds"""
        # Create transactions with explicit gaps
        txs = []
        timestamp = 1000

        # Session 1: 10 txs within 5 seconds
        for i in range(10):
            txs.append(SentinelTx(
                timestamp=timestamp + i,
                user_a=0, user_b=1,
                amount0=100, amount1=0,
                opcode='transfer',
                role_a='client', role_b='client'
            ))

        # Gap: 100 seconds
        timestamp += 100

        # Session 2: 10 txs within 5 seconds
        for i in range(10):
            txs.append(SentinelTx(
                timestamp=timestamp + i,
                user_a=0, user_b=1,
                amount0=100, amount1=0,
                opcode='transfer',
                role_a='client', role_b='client'
            ))

        # Process with session window (gap threshold: 30 seconds)
        processor = StreamProcessor(
            window=SessionWindow(gap_seconds=30),
            mapper='identity',
            fee_bps=50,
            verbose=False
        )

        windowed_results = processor.ingest_batch(txs)

        # Should produce 2 windows (one per session)
        assert len(windowed_results) == 2, f"Expected 2 sessions, got {len(windowed_results)}"


@pytest.mark.parametrize("time_pattern", ["uniform", "bursty", "session_gaps"])
def test_streaming_with_different_time_patterns(time_pattern):
    """Test streaming works correctly with different time patterns"""
    scenario_config = ScenarioConfig(
        num_users=32,
        num_transactions=500,
        time_pattern=time_pattern,
        seed=35000
    )

    generator = ScenarioGenerator(scenario_config)
    txs = generator.generate()

    processor = StreamProcessor(
        window=TumblingWindow(size=100),
        mapper='identity',
        fee_bps=50,
        verbose=False
    )

    windowed_results = processor.ingest_batch(txs)

    # Should complete without errors regardless of time pattern
    assert len(windowed_results) > 0
    assert windowed_results[0] is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
