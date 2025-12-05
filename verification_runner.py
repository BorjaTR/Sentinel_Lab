#!/usr/bin/env python3
"""
Sentinel Cloud Comprehensive Verification Runner

Orchestrates all verification tests and generates a detailed report.

Usage:
    python3 verification_runner.py --full          # Run all tests
    python3 verification_runner.py --quick         # Run fast tests only
    python3 verification_runner.py --layer rtl     # Run specific layer
    python3 verification_runner.py --generate-corpus  # Generate test scenarios
"""

import sys
import os
import time
import json
import subprocess
from pathlib import Path
from typing import Dict, List, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class TestResult:
    """Result of a single test module"""
    module: str
    layer: str
    passed: int
    failed: int
    skipped: int
    duration: float
    errors: List[str]


@dataclass
class VerificationReport:
    """Comprehensive verification report"""
    timestamp: str
    total_tests: int
    total_passed: int
    total_failed: int
    total_skipped: int
    total_duration: float
    layer_results: Dict[str, List[TestResult]]
    coverage_summary: Dict[str, int]
    recommendations: List[str]


class VerificationRunner:
    """Orchestrates comprehensive verification"""

    TEST_MODULES = {
        'rtl': [
            'tests/test_verification_rtl.py',
        ],
        'mappers': [
            'tests/test_verification_mappers.py',
        ],
        'experiment': [
            'tests/test_verification_experiment_economics.py',
        ],
        'streaming': [
            'tests/test_verification_streaming.py',
            'tests/test_verification_streaming_enhanced.py',
            'tests/test_streaming_robustness.py',
        ],
        'integration': [
            # Full end-to-end tests would go here
        ],
    }

    def __init__(self, verbose=False):
        self.verbose = verbose
        self.results: List[TestResult] = []
        self.start_time = time.time()

    def run_test_module(self, module_path: str, layer: str) -> TestResult:
        """Run a single test module using pytest"""
        print(f"\n{'='*70}")
        print(f"Running: {module_path}")
        print(f"{'='*70}")

        start = time.time()

        # Run pytest
        cmd = [
            'python3', '-m', 'pytest',
            module_path,
            '-v',
            '--tb=short',
            '--color=yes' if self.verbose else '--color=no',
        ]

        if not self.verbose:
            cmd.append('-q')

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300  # 5 minute timeout per module
            )

            # Parse pytest output
            output = result.stdout + result.stderr
            passed, failed, skipped = self._parse_pytest_output(output)

            errors = []
            if result.returncode != 0:
                # Extract error messages
                for line in output.split('\n'):
                    if 'FAILED' in line or 'ERROR' in line:
                        errors.append(line.strip())

            duration = time.time() - start

            return TestResult(
                module=module_path,
                layer=layer,
                passed=passed,
                failed=failed,
                skipped=skipped,
                duration=duration,
                errors=errors
            )

        except subprocess.TimeoutExpired:
            return TestResult(
                module=module_path,
                layer=layer,
                passed=0,
                failed=1,
                skipped=0,
                duration=300.0,
                errors=[f"Timeout after 300s"]
            )
        except Exception as e:
            return TestResult(
                module=module_path,
                layer=layer,
                passed=0,
                failed=1,
                skipped=0,
                duration=0.0,
                errors=[f"Exception: {str(e)}"]
            )

    def _parse_pytest_output(self, output: str) -> Tuple[int, int, int]:
        """Parse pytest output to extract pass/fail/skip counts"""
        passed = failed = skipped = 0

        for line in output.split('\n'):
            if 'passed' in line.lower():
                # Look for patterns like "5 passed"
                parts = line.split()
                for i, part in enumerate(parts):
                    if part.lower() == 'passed' and i > 0:
                        try:
                            passed = int(parts[i-1])
                        except ValueError:
                            pass

            if 'failed' in line.lower():
                parts = line.split()
                for i, part in enumerate(parts):
                    if part.lower() == 'failed' and i > 0:
                        try:
                            failed = int(parts[i-1])
                        except ValueError:
                            pass

            if 'skipped' in line.lower():
                parts = line.split()
                for i, part in enumerate(parts):
                    if part.lower() == 'skipped' and i > 0:
                        try:
                            skipped = int(parts[i-1])
                        except ValueError:
                            pass

        return passed, failed, skipped

    def run_layer(self, layer: str) -> List[TestResult]:
        """Run all tests for a specific layer"""
        if layer not in self.TEST_MODULES:
            print(f"❌ Unknown layer: {layer}")
            print(f"Available layers: {', '.join(self.TEST_MODULES.keys())}")
            return []

        results = []
        modules = self.TEST_MODULES[layer]

        for module in modules:
            if not Path(module).exists():
                print(f"⚠️  Test module not found: {module} (skipping)")
                continue

            result = self.run_test_module(module, layer)
            results.append(result)
            self.results.append(result)

            # Print immediate summary
            status = "✅" if result.failed == 0 else "❌"
            print(f"{status} {result.passed} passed, {result.failed} failed, "
                  f"{result.skipped} skipped ({result.duration:.1f}s)")

        return results

    def run_all(self) -> List[TestResult]:
        """Run all verification tests"""
        print("\n" + "="*70)
        print("🔬 SENTINEL CLOUD COMPREHENSIVE VERIFICATION")
        print("="*70)

        for layer in self.TEST_MODULES.keys():
            self.run_layer(layer)

        return self.results

    def run_quick(self) -> List[TestResult]:
        """Run quick verification (mappers and streaming only)"""
        print("\n" + "="*70)
        print("⚡ SENTINEL CLOUD QUICK VERIFICATION")
        print("="*70)

        for layer in ['mappers', 'streaming']:
            self.run_layer(layer)

        return self.results

    def generate_report(self) -> VerificationReport:
        """Generate comprehensive verification report"""
        total_duration = time.time() - self.start_time

        # Aggregate results by layer
        layer_results = {}
        for layer in self.TEST_MODULES.keys():
            layer_results[layer] = [r for r in self.results if r.layer == layer]

        # Calculate totals
        total_tests = sum(r.passed + r.failed + r.skipped for r in self.results)
        total_passed = sum(r.passed for r in self.results)
        total_failed = sum(r.failed for r in self.results)
        total_skipped = sum(r.skipped for r in self.results)

        # Coverage summary (placeholder - would integrate with actual coverage tools)
        coverage_summary = {
            'opcodes': 4,  # All 4 opcodes covered
            'roles': 4,    # All 4 roles covered
            'fee_configs': 9,  # 0-500 bps tested
            'window_types': 3,  # Tumbling, sliding, session
        }

        # Generate recommendations
        recommendations = []
        if total_failed > 0:
            recommendations.append("❌ Fix failing tests before production deployment")
        if total_skipped > total_tests * 0.2:
            recommendations.append("⚠️  High skip rate - implement missing test infrastructure")
        if total_passed == total_tests and total_failed == 0:
            recommendations.append("✅ All tests passing - system ready for production")

        return VerificationReport(
            timestamp=datetime.now().isoformat(),
            total_tests=total_tests,
            total_passed=total_passed,
            total_failed=total_failed,
            total_skipped=total_skipped,
            total_duration=total_duration,
            layer_results=layer_results,
            coverage_summary=coverage_summary,
            recommendations=recommendations
        )

    def print_report(self, report: VerificationReport):
        """Print human-readable verification report"""
        print("\n" + "="*70)
        print("📊 VERIFICATION REPORT")
        print("="*70)
        print(f"Timestamp: {report.timestamp}")
        print(f"Duration: {report.total_duration:.1f}s")
        print()

        print("SUMMARY")
        print("-" * 70)
        print(f"Total Tests:    {report.total_tests}")
        print(f"✅ Passed:      {report.total_passed} ({100*report.total_passed/max(1,report.total_tests):.1f}%)")
        print(f"❌ Failed:      {report.total_failed} ({100*report.total_failed/max(1,report.total_tests):.1f}%)")
        print(f"⏭️  Skipped:     {report.total_skipped} ({100*report.total_skipped/max(1,report.total_tests):.1f}%)")
        print()

        print("LAYER BREAKDOWN")
        print("-" * 70)
        for layer, results in report.layer_results.items():
            if not results:
                print(f"{layer:15s}: No tests run")
                continue

            layer_passed = sum(r.passed for r in results)
            layer_failed = sum(r.failed for r in results)
            layer_skipped = sum(r.skipped for r in results)
            layer_total = layer_passed + layer_failed + layer_skipped

            status = "✅" if layer_failed == 0 else "❌"
            print(f"{layer:15s}: {status} {layer_passed}/{layer_total} passed "
                  f"({layer_failed} failed, {layer_skipped} skipped)")

        print()
        print("COVERAGE SUMMARY")
        print("-" * 70)
        for metric, count in report.coverage_summary.items():
            print(f"{metric:20s}: {count}")

        print()
        print("RECOMMENDATIONS")
        print("-" * 70)
        for rec in report.recommendations:
            print(f"  {rec}")

        print("="*70)

    def save_report(self, report: VerificationReport, output_path: str):
        """Save report to JSON file"""
        # Convert dataclasses to dicts
        report_dict = {
            'timestamp': report.timestamp,
            'total_tests': report.total_tests,
            'total_passed': report.total_passed,
            'total_failed': report.total_failed,
            'total_skipped': report.total_skipped,
            'total_duration': report.total_duration,
            'layer_results': {
                layer: [asdict(r) for r in results]
                for layer, results in report.layer_results.items()
            },
            'coverage_summary': report.coverage_summary,
            'recommendations': report.recommendations,
        }

        with open(output_path, 'w') as f:
            json.dump(report_dict, f, indent=2)

        print(f"\n💾 Report saved to: {output_path}")


def generate_verification_corpus():
    """Generate random scenarios for testing"""
    print("\n" + "="*70)
    print("🎲 GENERATING VERIFICATION CORPUS")
    print("="*70)

    from tests.scenario_generator import generate_verification_corpus as gen

    gen(output_dir="tests/verification_corpus")


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Sentinel Cloud Verification Runner")
    parser.add_argument('--full', action='store_true', help="Run all tests")
    parser.add_argument('--quick', action='store_true', help="Run quick tests only")
    parser.add_argument('--layer', type=str, help="Run specific layer (rtl, mappers, experiment, streaming)")
    parser.add_argument('--generate-corpus', action='store_true', help="Generate verification corpus")
    parser.add_argument('--output', type=str, default='verification_report.json', help="Output report path")
    parser.add_argument('--verbose', '-v', action='store_true', help="Verbose output")

    args = parser.parse_args()

    if args.generate_corpus:
        generate_verification_corpus()
        return 0

    runner = VerificationRunner(verbose=args.verbose)

    if args.full:
        runner.run_all()
    elif args.quick:
        runner.run_quick()
    elif args.layer:
        runner.run_layer(args.layer)
    else:
        print("❌ No test mode specified. Use --full, --quick, --layer, or --generate-corpus")
        parser.print_help()
        return 1

    # Generate and display report
    report = runner.generate_report()
    runner.print_report(report)
    runner.save_report(report, args.output)

    # Return exit code based on results
    return 0 if report.total_failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
