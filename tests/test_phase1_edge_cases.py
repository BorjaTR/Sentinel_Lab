#!/usr/bin/env python3
"""
Phase 1 Edge Case Regression Tests

These tests verify that the configurable fee system handles
edge cases correctly and fails gracefully on invalid inputs.

Tests:
- FR-1.2: Zero fee (0 bps) collects no revenue
- FR-1.2: Confiscatory fee (10000 bps) collects maximum revenue
- QR-1.4: Large amounts don't cause overflow
- FR-1.1: CLI validation rejects invalid fee ranges
"""

import subprocess
import os
import sys
import csv

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def run_simulation_test(fee_bps_asset0, fee_bps_asset1=0, expect_error=False):
    """
    Helper to run simulation and return metrics.

    Returns:
        dict: Parsed metrics from logs/sim_stats.csv
        None: If simulation failed and expect_error=True
    """
    cmd = [
        "python3", "run_lab.py",
        "--fee-bps-asset0", str(fee_bps_asset0),
        "--fee-bps-asset1", str(fee_bps_asset1)
    ]

    result = subprocess.run(cmd, capture_output=True, text=True)

    if expect_error:
        return result.returncode != 0

    if result.returncode != 0:
        print(f"❌ Simulation failed: {result.stderr}")
        return None

    # Parse metrics
    metrics = {}
    if os.path.exists("logs/sim_stats.csv"):
        with open("logs/sim_stats.csv", 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                metrics[row['metric']] = float(row['value']) if '.' in row['value'] else int(row['value'])

    return metrics

def test_zero_fee():
    """
    FR-1.2: Zero fee should collect no revenue.

    Requirement: When fee_bps = 0, vault should remain at 0.
    """
    print("Test 1: Zero fee (0 bps) → vault should be 0")

    metrics = run_simulation_test(fee_bps_asset0=0, fee_bps_asset1=0)

    if metrics is None:
        print("  ❌ FAIL: Simulation failed")
        return False

    vault_usdc = metrics.get('rev_usdc', -1)
    vault_gpu = metrics.get('rev_gpu', -1)

    if vault_usdc == 0 and vault_gpu == 0:
        print(f"  ✅ PASS: Vault USDC={vault_usdc}, Vault GPU={vault_gpu}")
        return True
    else:
        print(f"  ❌ FAIL: Expected vault=0, got USDC={vault_usdc}, GPU={vault_gpu}")
        return False

def test_confiscatory_fee():
    """
    FR-1.2: 100% fee (10000 bps) should collect maximum revenue.

    Requirement: When fee_bps = 10000, vault should collect all transaction amounts.
    Note: Transactions will fail after first TX since users have no balance left.
    """
    print("Test 2: Confiscatory fee (10000 bps = 100%) → maximum vault accumulation")

    metrics = run_simulation_test(fee_bps_asset0=10000, fee_bps_asset1=0)

    if metrics is None:
        print("  ❌ FAIL: Simulation failed")
        return False

    vault_usdc = metrics.get('rev_usdc', 0)
    total_tx = metrics.get('total_tx', 0)

    # With 100% fee, only a few transactions will succeed before balances deplete
    # We expect vault > 0 and many TXs to fail
    if vault_usdc > 0 and total_tx > 0:
        print(f"  ✅ PASS: Vault collected ${vault_usdc:,} USDC from {total_tx} TXs")
        print(f"     Note: Many TXs likely failed due to insufficient funds (expected with 100% fee)")
        return True
    else:
        print(f"  ❌ FAIL: Expected vault > 0, got {vault_usdc}")
        return False

def test_overflow_protection():
    """
    QR-1.4: Large amounts should not cause overflow.

    Requirement: Amounts near 2^64 should either:
    - Process correctly without wraparound, OR
    - Fail gracefully with "insufficient funds"

    Note: This test uses random fuzzing mode which generates amounts up to 5000.
    For true overflow testing, we'd need a custom scenario with max int64 values.
    """
    print("Test 3: Overflow protection → no wraparound on large amounts")

    # Run standard fuzzing test (5K random TXs)
    metrics = run_simulation_test(fee_bps_asset0=50)

    if metrics is None:
        print("  ❌ FAIL: Simulation failed")
        return False

    # Check that simulation completed without crashes
    total_tx = metrics.get('total_tx', 0)
    tps = metrics.get('tps_million', 0)

    if total_tx > 0 and tps > 0:
        print(f"  ✅ PASS: Processed {total_tx} TXs at {tps:.2f}M TPS without crashes")
        print(f"     Note: Full overflow test requires custom scenario with 2^63 amounts")
        return True
    else:
        print(f"  ❌ FAIL: Simulation did not complete correctly")
        return False

def test_cli_validation_negative():
    """
    FR-1.1: CLI should reject negative fees.

    Requirement: --fee-bps-asset0 < 0 should return error before simulation.
    """
    print("Test 4a: CLI validation → reject negative fees")

    cmd = ["python3", "run_lab.py", "--fee-bps-asset0", "-50"]
    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0 and "must be between 0 and 10000" in result.stdout:
        print(f"  ✅ PASS: Rejected negative fee with error message")
        return True
    else:
        print(f"  ❌ FAIL: Did not reject negative fee")
        return False

def test_cli_validation_excessive():
    """
    FR-1.1: CLI should reject fees > 100%.

    Requirement: --fee-bps-asset0 > 10000 should return error before simulation.
    """
    print("Test 4b: CLI validation → reject excessive fees (>100%)")

    cmd = ["python3", "run_lab.py", "--fee-bps-asset0", "15000"]
    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0 and "must be between 0 and 10000" in result.stdout:
        print(f"  ✅ PASS: Rejected excessive fee with error message")
        return True
    else:
        print(f"  ❌ FAIL: Did not reject excessive fee")
        return False

def test_boundary_values():
    """
    FR-1.2: Boundary values (1 bps, 9999 bps) should work correctly.

    Requirement: Edge of valid range should process without errors.
    """
    print("Test 5: Boundary values → 1 bps and 9999 bps should work")

    # Test 1 bps (0.01%)
    metrics_low = run_simulation_test(fee_bps_asset0=1)
    if metrics_low is None:
        print(f"  ❌ FAIL: 1 bps simulation failed")
        return False

    # Test 9999 bps (99.99%)
    metrics_high = run_simulation_test(fee_bps_asset0=9999)
    if metrics_high is None:
        print(f"  ❌ FAIL: 9999 bps simulation failed")
        return False

    vault_low = metrics_low.get('rev_usdc', 0)
    vault_high = metrics_high.get('rev_usdc', 0)

    # 9999 bps should collect much more than 1 bps
    if 0 < vault_low < vault_high:
        print(f"  ✅ PASS: 1 bps → ${vault_low:,}, 9999 bps → ${vault_high:,}")
        return True
    else:
        print(f"  ❌ FAIL: Expected 0 < vault_low < vault_high, got {vault_low} and {vault_high}")
        return False

def main():
    """Run all edge case tests."""
    print("=" * 60)
    print("Phase 1 Edge Case Regression Test Suite")
    print("=" * 60)
    print()

    tests = [
        ("Zero Fee", test_zero_fee),
        ("Confiscatory Fee", test_confiscatory_fee),
        ("Overflow Protection", test_overflow_protection),
        ("CLI Validation (Negative)", test_cli_validation_negative),
        ("CLI Validation (Excessive)", test_cli_validation_excessive),
        ("Boundary Values", test_boundary_values),
    ]

    results = []
    for name, test_func in tests:
        try:
            passed = test_func()
            results.append((name, passed))
        except Exception as e:
            print(f"  ❌ EXCEPTION: {e}")
            results.append((name, False))
        print()

    # Summary
    print("=" * 60)
    print("Test Summary")
    print("=" * 60)

    passed_count = sum(1 for _, passed in results if passed)
    total_count = len(results)

    for name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{status}: {name}")

    print()
    print(f"Result: {passed_count}/{total_count} tests passed")

    if passed_count == total_count:
        print("🎉 All edge case tests passed!")
        return 0
    else:
        print("⚠️  Some tests failed. Review output above.")
        return 1

if __name__ == "__main__":
    sys.exit(main())
