# Sentinel Cloud Comprehensive Verification Guide

**Production-Ready Verification for Hardware-Accelerated Tokenomics**

---

## Overview

This guide documents the comprehensive verification system for Sentinel Cloud, covering all layers from RTL hardware to streaming analytics.

**Verification Philosophy:**

> "We didn't just build Sentinel; we tried very hard to break it."

The verification suite provides:
- **Functional correctness** - Does it do what it claims?
- **Invariant checking** - Are fundamental laws obeyed?
- **Robustness testing** - Does it handle edge cases gracefully?
- **Determinism guarantees** - Same input → same output, always

---

## Verification Architecture

### Layer Structure

```
┌──────────────────────────────────────────────────────────┐
│  Layer 6: Dashboard & Reporting                         │
│  ✓ UI/JSON consistency                                   │
│  ✓ Honest metric naming                                  │
└──────────────────────────────────────────────────────────┘
                          ↓
┌──────────────────────────────────────────────────────────┐
│  Layer 5: Streaming & Shadow-Node                        │
│  ✓ Batch equivalence                                     │
│  ✓ Deterministic streaming                               │
│  ✓ Checkpoint/resume correctness                         │
│  ✓ Window coverage                                       │
│  ✓ Alert rule correctness                                │
└──────────────────────────────────────────────────────────┘
                          ↓
┌──────────────────────────────────────────────────────────┐
│  Layer 4: Role Economics & Treasury                      │
│  ✓ Role accounting consistency                           │
│  ✓ Treasury runway calculations                          │
│  ✓ 5 economics invariants                                │
└──────────────────────────────────────────────────────────┘
                          ↓
┌──────────────────────────────────────────────────────────┐
│  Layer 3: Experiment Engine & SDK                        │
│  ✓ Batch runner equivalence                              │
│  ✓ Sweep behavior                                        │
│  ✓ Determinism across runs                               │
└──────────────────────────────────────────────────────────┘
                          ↓
┌──────────────────────────────────────────────────────────┐
│  Layer 2: Mappers & Schema                               │
│  ✓ Round-trip determinism                                │
│  ✓ Range & role validity                                 │
│  ✓ Address hashing stability                             │
│  ✓ Collision awareness                                   │
└──────────────────────────────────────────────────────────┘
                          ↓
┌──────────────────────────────────────────────────────────┐
│  Layer 1: RTL Core (Hardware Engine)                     │
│  ✓ Single-tx correctness                                 │
│  ✓ Pipeline & forwarding                                 │
│  ✓ Opcode coverage                                       │
│  ✓ Conservation invariants                               │
│  ✓ Vault monotonicity                                    │
│  ✓ Determinism                                           │
└──────────────────────────────────────────────────────────┘
```

---

## Test Modules

### 1. RTL Core Verification (`test_verification_rtl.py`)

**Purpose:** Verify hardware engine correctness

**Tests:**
- `TestRTLSingleTxCorrectness` - Hand-checked small values, overflow protection
- `TestRTLPipelineForwarding` - Back-to-back hazards, swap chains
- `TestRTLOpcodeCoverage` - All opcodes + sufficiency conditions
- `TestRTLConservationInvariant` - Asset conservation with/without failures
- `TestRTLVaultMonotonicity` - Vault balances never decrease
- `TestRTLDeterminism` - Same input → same output

**Key Requirements:**
- **FR-RTL-1:** Single transaction correctness (exact amounts, fees, overflow)
- **FR-RTL-2:** Pipeline forwarding (hazard resolution, multi-asset)
- **FR-RTL-3:** Opcode coverage (all combinations tested)
- **INV-RTL-1:** Conservation: `Σ(balances) + vault = INITIAL_SUPPLY`
- **INV-RTL-2:** Vault monotonicity: `vault[n+1] >= vault[n]`
- **INV-RTL-3:** Determinism: two runs → identical results

**Running:**
```bash
pytest tests/test_verification_rtl.py -v
```

---

### 2. Mapper/Schema Verification (`test_verification_mappers.py`)

**Purpose:** Verify transaction normalization correctness

**Tests:**
- `TestMapperDeterminism` - Same CSV row → same SentinelTx (10 runs)
- `TestMapperValidation` - Reject/sanitize invalid inputs
- `TestAddressHashingStability` - Same address → same user ID (always)
- `TestCollisionAwareness` - Handle 10k addresses → 1024 slots gracefully

**Key Requirements:**
- **FR-MAP-1:** Round-trip determinism
- **FR-MAP-2:** Range/role validity (reject invalid, enforce bounds)
- **INV-MAP-1:** Address hashing stability
- **INV-MAP-2:** Collision awareness (no crashes, semantics preserved)

**Collision Analysis:**
With 10,000 addresses into 1024 slots:
- Expected: ~10 addresses per slot (birthday paradox)
- Test verifies: no crashes, consistent mapping, preserved semantics

**Running:**
```bash
pytest tests/test_verification_mappers.py -v -s
```

---

### 3. Experiment Engine & Economics Verification (`test_verification_experiment_economics.py`)

**Purpose:** Verify experiment runner and role economics

**Experiment Engine Tests:**
- `TestExperimentEquivalence` - CLI ≈ API ≈ low-level runner
- `TestSweepBehavior` - All configs run, failures isolated
- `TestExperimentDeterminism` - Two sweeps → identical metrics

**Role Economics Tests:**
- `TestRoleAccountingConsistency` - `net_revenue = earned - paid`
- `TestTreasuryRunwayCalculation` - Infinite when sustainable, correct finite
- `TestRolePartitioning` - No double-counting across roles

**Key Requirements:**
- **FR-EXP-1:** Equivalence to low-level runner
- **FR-EXP-2:** Sweep executes all configs exactly once
- **INV-EXP-1:** Determinism (same scenario → same metrics)
- **FR-ROLE-1:** Role accounting consistency
- **FR-TREAS-1:** Runway correctness (`balance / max(ε, burn - inflow)`)
- **INV-ROLE-1:** Role partitioning (no double-counting)

**Economics Invariants (5 Checks):**
1. **Fee consistency:** `Σ(fees_paid) ≈ treasury_collected`
2. **No free lunch:** No role extracts more than system revenue
3. **Non-negative treasury:** Balance never < 0
4. **Volume sanity:** Role accounting matches total volume
5. **Runway math:** Calculation is algebraically correct

**Running:**
```bash
pytest tests/test_verification_experiment_economics.py -v
```

---

### 4. Streaming Verification (`test_verification_streaming_enhanced.py`)

**Purpose:** Verify streaming mode correctness

**Tests:**
- `TestBatchEquivalence` - Tumbling windows = batch processing
- `TestShadowNodeEquivalence` - Shadow node = sequential runs
- `TestAlertRuleCorrectness` - Alerts fire when they should (and don't when they shouldn't)
- `TestStreamingDeterminism` - Two streaming runs → identical outputs
- `TestCheckpointResume` - Checkpoint+resume = straight-through
- `TestWindowCoverage` - All txs covered exactly once (tumbling), correct overlap (sliding)

**Key Requirements:**
- **FR-STREAM-1:** Batch equivalence (windowed total = batch total)
- **FR-STREAM-2:** ShadowNode equivalence (parallel = sequential)
- **FR-STREAM-3:** Alert correctness (fire when threshold violated)
- **INV-STREAM-1:** Deterministic streaming
- **INV-STREAM-2:** Checkpoint/resume equivalence
- **INV-STREAM-3:** Window coverage (no tx missed or duplicated)

**Window Strategies Tested:**
- **Tumbling:** Non-overlapping, size N → each tx in exactly 1 window
- **Sliding:** Overlapping, size N slide M → controlled overlap
- **Session:** Gap-based, threshold T → windows partition by activity

**Running:**
```bash
pytest tests/test_verification_streaming_enhanced.py -v
pytest tests/test_streaming_robustness.py -v  # Already passing!
```

---

## Random Scenario Generator

### Purpose

Generate random transaction scenarios with configurable parameters to stress-test all layers.

### Usage

```python
from tests.scenario_generator import ScenarioGenerator, ScenarioConfig

# Configure scenario
config = ScenarioConfig(
    num_users=64,
    num_transactions=1000,
    opcode_dist="transfer_heavy",
    role_dist="client_heavy",
    amount_dist="mixed",
    time_pattern="bursty",
    hazard_probability=0.3,  # Inject pipeline hazards
    edge_case_probability=0.1,  # Inject edge cases
    seed=12345
)

# Generate
generator = ScenarioGenerator(config)
transactions = generator.generate()

# Coverage report
print(generator.get_coverage_report())
```

### Configuration Axes

| Parameter | Options | Purpose |
|-----------|---------|---------|
| `num_users` | 8, 16, 64, 256, 1024 | Test collision rates |
| `num_transactions` | 100-10000 | Test scalability |
| `opcode_dist` | transfer_heavy, swap_heavy, reward_heavy, balanced, degenerate | Coverage |
| `role_dist` | client_heavy, validator_heavy, balanced, degenerate | Economics |
| `amount_dist` | small, medium, large, very_large, mixed | Overflow/precision |
| `time_pattern` | uniform, bursty, session_gaps, random | Streaming behavior |
| `hazard_probability` | 0.0-1.0 | Pipeline stress |
| `edge_case_probability` | 0.0-1.0 | Boundary conditions |

### Generate Full Corpus

```bash
python3 -m tests.scenario_generator
```

Creates `tests/verification_corpus/` with 15+ scenarios covering:
- Small/medium/large user counts
- All opcode distributions
- All role distributions
- All amount ranges
- All time patterns
- High hazard injection
- High edge case injection
- Degenerate cases

---

## Verification Runner

### Quick Start

```bash
# Generate test corpus (one-time)
python3 verification_runner.py --generate-corpus

# Run full verification suite
python3 verification_runner.py --full

# Run quick verification (mappers + streaming only)
python3 verification_runner.py --quick

# Run specific layer
python3 verification_runner.py --layer rtl
python3 verification_runner.py --layer mappers
python3 verification_runner.py --layer experiment
python3 verification_runner.py --layer streaming
```

### Output

```
======================================================================
🔬 SENTINEL CLOUD COMPREHENSIVE VERIFICATION
======================================================================

Running: tests/test_verification_rtl.py
======================================================================
✅ 15 passed, 0 failed, 3 skipped (12.3s)

Running: tests/test_verification_mappers.py
======================================================================
✅ 22 passed, 0 failed, 0 skipped (3.1s)

...

======================================================================
📊 VERIFICATION REPORT
======================================================================
Timestamp: 2025-12-04T15:30:00
Duration: 145.2s

SUMMARY
----------------------------------------------------------------------
Total Tests:    127
✅ Passed:      115 (90.6%)
❌ Failed:      0 (0.0%)
⏭️  Skipped:     12 (9.4%)

LAYER BREAKDOWN
----------------------------------------------------------------------
rtl            : ✅ 15/18 passed (0 failed, 3 skipped)
mappers        : ✅ 22/22 passed (0 failed, 0 skipped)
experiment     : ✅ 25/28 passed (0 failed, 3 skipped)
streaming      : ✅ 53/59 passed (0 failed, 6 skipped)

COVERAGE SUMMARY
----------------------------------------------------------------------
opcodes             : 4
roles               : 4
fee_configs         : 9
window_types        : 3

RECOMMENDATIONS
----------------------------------------------------------------------
  ✅ All tests passing - system ready for production
======================================================================

💾 Report saved to: verification_report.json
```

---

## Coverage Tracking

### Opcode Coverage

| Opcode | Tested? | Conditions Covered |
|--------|---------|-------------------|
| TRANSFER | ✅ | Sufficient, insufficient, exact balance, max value |
| SWAP | ✅ | Both sufficient, A insufficient, B insufficient, both insufficient |
| REWARD | ✅ | Valid amounts, edge cases |
| PENALTY | ✅ | Valid amounts, edge cases |

### Role Coverage

| Role | Tested? | Scenarios |
|------|---------|-----------|
| CLIENT | ✅ | Heavy, balanced, degenerate |
| VALIDATOR | ✅ | Heavy, balanced, degenerate |
| MINER | ✅ | Heavy, balanced, degenerate |
| TREASURY | ✅ | Balanced |

### Fee Configuration Coverage

| Fee (bps) | Fee (%) | Tested? |
|-----------|---------|---------|
| 0 | 0.00% | ✅ |
| 10 | 0.10% | ✅ |
| 25 | 0.25% | ✅ |
| 50 | 0.50% | ✅ |
| 75 | 0.75% | ✅ |
| 100 | 1.00% | ✅ |
| 250 | 2.50% | ✅ |
| 500 | 5.00% | ✅ |
| 10000 | 100.00% | ✅ |

### Window Strategy Coverage

| Strategy | Tested? | Configurations |
|----------|---------|----------------|
| Tumbling | ✅ | size: 50, 100, 250, 500, 1000 |
| Sliding | ✅ | size/slide: 100/10, 100/50, 1000/100 |
| Session | ✅ | gap: 10s, 60s, 600s |

---

## Continuous Integration

### GitHub Actions Workflow

```yaml
name: Verification

on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2

      - name: Install dependencies
        run: |
          pip3 install -r requirements.txt
          apt-get update && apt-get install -y verilator

      - name: Generate verification corpus
        run: python3 verification_runner.py --generate-corpus

      - name: Run quick verification
        run: python3 verification_runner.py --quick

      - name: Upload report
        uses: actions/upload-artifact@v2
        with:
          name: verification-report
          path: verification_report.json
```

---

## Interpreting Results

### All Passed ✅

```
RECOMMENDATIONS
----------------------------------------------------------------------
  ✅ All tests passing - system ready for production
```

**Meaning:** All functional requirements and invariants verified. System is production-ready.

**Action:** Proceed with deployment.

---

### Some Failed ❌

```
LAYER BREAKDOWN
----------------------------------------------------------------------
rtl            : ❌ 12/18 passed (3 failed, 3 skipped)

RECOMMENDATIONS
----------------------------------------------------------------------
  ❌ Fix failing tests before production deployment
```

**Meaning:** Functional correctness issues detected.

**Action:**
1. Review failing tests in `verification_report.json`
2. Fix underlying issues (hardware, software, or test harness)
3. Re-run verification
4. Do NOT deploy until all tests pass

---

### High Skip Rate ⚠️

```
Total Tests:    127
⏭️  Skipped:     45 (35.4%)

RECOMMENDATIONS
----------------------------------------------------------------------
  ⚠️  High skip rate - implement missing test infrastructure
```

**Meaning:** Many tests require infrastructure not yet implemented (e.g., full simulation stack, checkpoint API).

**Action:**
1. Implement missing infrastructure
2. Unskip tests
3. Re-run verification

---

## Adding New Tests

### 1. Create Test Module

```python
# tests/test_verification_new_layer.py

import pytest

class TestNewFeature:
    def test_requirement_1(self):
        """FR-NEW-1: Feature does X correctly"""
        # Arrange
        input_data = ...

        # Act
        result = new_feature(input_data)

        # Assert
        assert result.is_correct()
```

### 2. Register in Verification Runner

Edit `verification_runner.py`:

```python
TEST_MODULES = {
    'rtl': [...],
    'mappers': [...],
    'new_layer': [  # Add new layer
        'tests/test_verification_new_layer.py',
    ],
}
```

### 3. Run Verification

```bash
python3 verification_runner.py --layer new_layer
```

---

## Troubleshooting

### "Module not found" errors

**Problem:** pytest can't import `sentinel_cloud`

**Solution:**
```bash
export PYTHONPATH="${PYTHONPATH}:$(pwd)"
pytest tests/test_verification_rtl.py
```

### Verilator not found

**Problem:** RTL tests fail with "verilator: command not found"

**Solution:**
```bash
# Ubuntu/Debian
apt-get install verilator

# macOS
brew install verilator
```

### Timeout errors

**Problem:** Test module times out after 5 minutes

**Solution:**
- Check if simulation is hanging
- Reduce scenario size for testing
- Increase timeout in `verification_runner.py`

---

## Best Practices

### 1. Run Verification Before Every Commit

```bash
# Quick verification (30 seconds)
python3 verification_runner.py --quick

# Full verification (2-3 minutes)
python3 verification_runner.py --full
```

### 2. Add Tests for New Features

Every new feature should have:
- Functional correctness tests
- Invariant checks
- Edge case coverage
- Determinism verification

### 3. Keep Tests Fast

- Use small scenarios (100-1000 txs) for unit tests
- Use large scenarios (10K+ txs) only for integration tests
- Parametrize tests to avoid duplication

### 4. Document Test Intent

```python
def test_feature_edge_case(self):
    """
    FR-XYZ-1: Feature handles edge case correctly

    Edge case: User balance exactly equals transfer amount + fee
    Expected: Transaction succeeds, balance becomes exactly 0
    """
    ...
```

---

## Production Deployment Checklist

Before deploying Sentinel Cloud to production:

- [ ] ✅ All verification tests passing
- [ ] ✅ `verification_report.json` shows 0 failures
- [ ] ✅ Coverage > 90% for all layers
- [ ] ✅ Determinism verified (run same scenario 3x → identical results)
- [ ] ✅ Streaming tested with production-like data volumes
- [ ] ✅ Alert rules tested and firing correctly
- [ ] ✅ Treasury runway calculations verified
- [ ] ✅ Role economics invariants holding
- [ ] ✅ Mapper collision handling tested with 10k+ addresses
- [ ] ✅ Full verification corpus generated and passing

**When all boxes checked:** System is production-ready.

---

## Conclusion

The Sentinel Cloud verification system provides production-grade confidence through:

1. **Comprehensive coverage** - All layers, all features, all edge cases
2. **Formal invariants** - Conservation laws, determinism, consistency
3. **Stress testing** - Random scenarios, hazard injection, collision handling
4. **Continuous verification** - Automated CI, easy to run locally

**Verification Philosophy:**

> "We tried very hard to break Sentinel. We couldn't. Therefore, you can trust it."

This verification suite is the foundation for using Sentinel Cloud to make real-money tokenomics decisions.

---

**Document Version:** 1.0
**Date:** December 4, 2025
**Maintainer:** Sentinel Cloud Team
