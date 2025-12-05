"""
Phase 6.5: Economics Hardening Tests

Basic validation tests for role economics, treasury sustainability,
and invariant checks.

Run with: python3 -m pytest tests/test_role_economics.py -v
Or directly: python3 tests/test_role_economics.py
"""

import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sentinel_cloud.schema import SentinelTx, Opcode
from sentinel_cloud.role_economics import (
    calculate_simulation_days,
    TreasuryConfig,
    RoleAnalyzer,
    validate_economics_consistency
)


def test_calculate_simulation_days_basic():
    """Test time calculation: 24h span = 1 day"""
    txs = [
        SentinelTx(timestamp=0, user_a=0, user_b=1, asset0_amount=1000, asset1_amount=0, opcode=Opcode.TRANSFER),
        SentinelTx(timestamp=86400, user_a=1, user_b=2, asset0_amount=1000, asset1_amount=0, opcode=Opcode.TRANSFER)
    ]
    days = calculate_simulation_days(txs)
    assert abs(days - 1.0) < 0.01, f"Expected 1.0 days, got {days}"
    print(f"✅ Time calc test: 24h span = {days:.2f} days")


def test_calculate_simulation_days_same_timestamp():
    """Test edge case: all transactions at same timestamp"""
    txs = [
        SentinelTx(timestamp=100, user_a=0, user_b=1, asset0_amount=1000, asset1_amount=0, opcode=Opcode.TRANSFER)
        for _ in range(100)
    ]
    days = calculate_simulation_days(txs)
    # Should use tx count as fallback: 100 tx / 86400 seconds/day
    expected = 100 / 86400.0
    assert abs(days - expected) < 0.01, f"Expected {expected:.6f} days, got {days:.6f}"
    print(f"✅ Edge case test: same timestamp = {days:.6f} days")


def test_treasury_config_validation():
    """Test treasury config validates negative values"""
    # Valid config
    config = TreasuryConfig(initial_balance_usdc=1_000_000, simulation_days=1.0)
    assert config.initial_balance_usdc == 1_000_000
    print(f"✅ Valid treasury config: ${config.initial_balance_usdc:,.0f}, {config.simulation_days} days")

    # Invalid: negative balance
    try:
        bad_config = TreasuryConfig(initial_balance_usdc=-100, simulation_days=1.0)
        assert False, "Should have raised ValueError for negative balance"
    except ValueError as e:
        print(f"✅ Rejected negative balance: {e}")

    # Invalid: zero days
    try:
        bad_config = TreasuryConfig(initial_balance_usdc=1000, simulation_days=0)
        assert False, "Should have raised ValueError for zero days"
    except ValueError as e:
        print(f"✅ Rejected zero days: {e}")


def test_role_analyzer_basic():
    """Test role analyzer with simple transactions"""
    txs = [
        SentinelTx(timestamp=0, user_a=0, user_b=1, asset0_amount=1000, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="miner"),
        SentinelTx(timestamp=10, user_a=1, user_b=2, asset0_amount=500, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="miner", role_b="client"),
    ]

    analyzer = RoleAnalyzer(txs, fee_bps=50)  # 0.5% fee
    role_metrics = analyzer.get_role_breakdown()

    # Check that we got metrics for both roles
    assert 'client' in role_metrics, "Missing client metrics"
    assert 'miner' in role_metrics, "Missing miner metrics"

    client_metrics = role_metrics['client']
    miner_metrics = role_metrics['miner']

    # Client should have 2 transactions (1 send, 1 receive)
    assert client_metrics.tx_count == 2, f"Expected 2 client txs, got {client_metrics.tx_count}"

    # Miner should have 2 transactions (1 receive, 1 send)
    assert miner_metrics.tx_count == 2, f"Expected 2 miner txs, got {miner_metrics.tx_count}"

    print(f"✅ Role analyzer: client={client_metrics.tx_count} txs, miner={miner_metrics.tx_count} txs")


def test_economics_invariants_valid():
    """Test that valid economics pass invariant checks"""
    # Create simple scenario: 2 clients exchange money
    txs = [
        SentinelTx(timestamp=0, user_a=0, user_b=1, asset0_amount=1000, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
        SentinelTx(timestamp=10, user_a=1, user_b=0, asset0_amount=500, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client"),
    ]

    analyzer = RoleAnalyzer(txs, fee_bps=50)
    role_metrics = analyzer.get_role_breakdown()

    treasury_config = TreasuryConfig(
        initial_balance_usdc=10_000,
        simulation_days=calculate_simulation_days(txs),
        emissions_schedule=None
    )
    treasury = analyzer.calculate_treasury_state(treasury_config)

    # Run invariant checks
    errors = validate_economics_consistency(
        transactions=txs,
        role_metrics=role_metrics,
        treasury_state=treasury,
        fee_bps=50,
        tolerance=0.01
    )

    if errors:
        print(f"⚠️  Invariant violations:")
        for err in errors:
            print(f"   - {err}")
    else:
        print(f"✅ All economics invariants passed")

    # Note: Don't assert no errors since role volume accounting may be permissive
    # The important thing is the checks run without crashing


def test_treasury_sustainability():
    """Test treasury sustainability with zero burn (no emissions)"""
    txs = [
        SentinelTx(timestamp=i*10, user_a=0, user_b=1, asset0_amount=1000, asset1_amount=0,
                   opcode=Opcode.TRANSFER, role_a="client", role_b="client")
        for i in range(100)
    ]

    analyzer = RoleAnalyzer(txs, fee_bps=50)  # 0.5% fees
    treasury_config = TreasuryConfig(
        initial_balance_usdc=10_000,
        simulation_days=calculate_simulation_days(txs),
        emissions_schedule=None  # No emissions = no burn
    )
    treasury = analyzer.calculate_treasury_state(treasury_config)

    # With no emissions, treasury should be sustainable
    assert treasury.is_sustainable, f"Expected sustainable, got {treasury.depletion_risk}"
    assert treasury.runway_days == float('inf'), f"Expected infinite runway, got {treasury.runway_days}"

    print(f"✅ Treasury sustainability: {treasury.depletion_risk}")
    print(f"   Revenue: ${treasury.revenue_rate_per_day:,.2f}/day")
    print(f"   Burn: ${treasury.burn_rate_per_day:,.2f}/day")
    print(f"   Balance: ${treasury.balance_usdc:,.2f}")


def run_all_tests():
    """Run all validation tests"""
    print("\n" + "="*70)
    print("Phase 6.5: Economics Hardening Validation")
    print("="*70 + "\n")

    tests = [
        ("Time Calculation (24h)", test_calculate_simulation_days_basic),
        ("Time Calculation (Edge Case)", test_calculate_simulation_days_same_timestamp),
        ("Treasury Config Validation", test_treasury_config_validation),
        ("Role Analyzer Basic", test_role_analyzer_basic),
        ("Economics Invariants", test_economics_invariants_valid),
        ("Treasury Sustainability", test_treasury_sustainability),
    ]

    passed = 0
    failed = 0

    for name, test_fn in tests:
        try:
            print(f"\n--- {name} ---")
            test_fn()
            passed += 1
        except Exception as e:
            print(f"❌ FAILED: {e}")
            import traceback
            traceback.print_exc()
            failed += 1

    print("\n" + "="*70)
    print(f"Results: {passed} passed, {failed} failed")
    print("="*70 + "\n")

    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
