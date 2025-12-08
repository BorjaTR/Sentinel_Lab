"""
Sentinel Cloud - Config-Driven Workflow Example

Demonstrates YAML-based configuration for repeatable, team-friendly workflows.

Usage:
    python examples/04_config_workflow.py
"""

from sentinel_cloud.config import SentinelConfig, generate_default_config
from pathlib import Path

def main():
    print("="*70)
    print("Sentinel Cloud - Config-Driven Workflow Example")
    print("="*70)
    print()

    # Example 1: Generate default config
    print("Example 1: Generate Default Configuration")
    print("-" * 70)

    config = generate_default_config(
        scenario_path="data/solana_day_1.csv",
        protocol_name="MyProtocol",
        treasury_balance=5_000_000.0
    )

    # Save to file
    config.to_yaml("examples/example_config.yaml")
    print("✓ Created: examples/example_config.yaml")
    print()

    # Show config structure
    print("Configuration Preview:")
    print("-" * 70)
    print(f"Protocol: {config.protocol.name}")
    print(f"Treasury: ${config.protocol.treasury_balance:,.0f}")
    print(f"Scenario: {config.scenario.path}")
    print(f"Mapper:   {config.scenario.mapper}")
    print()
    print(f"Analysis:")
    print(f"  Fee range: {config.analysis.fee_range}")
    print(f"  Compare:   {config.analysis.compare_fee} bps")
    print(f"  Phases:    {', '.join(config.analysis.run_phases)}")
    print()
    print(f"Safety thresholds:")
    print(f"  Min runway:    {config.safety.min_runway_days} days")
    print(f"  Max fee:       {config.safety.max_fee_bps} bps")
    print(f"  Min retention: {config.safety.min_volume_retention*100}%")
    print()

    # Example 2: Load and validate config
    print("\nExample 2: Load and Validate Configuration")
    print("-" * 70)

    loaded_config = SentinelConfig.from_yaml("examples/example_config.yaml")
    warnings = loaded_config.validate_all()

    if warnings:
        print("⚠️  Warnings:")
        for warning in warnings:
            print(f"  - {warning}")
    else:
        print("✓ Configuration valid - no warnings")
    print()

    # Example 3: Customize config programmatically
    print("\nExample 3: Customize Configuration")
    print("-" * 70)

    # Create custom config
    from sentinel_cloud.config import (
        ScenarioConfig, ProtocolConfig, AnalysisConfig,
        SafetyConfig, OutputConfig, SentinelConfig
    )

    custom_config = SentinelConfig(
        version=1,
        scenario=ScenarioConfig(
            path="data/solana_day_1.csv",
            mapper="solana"
        ),
        protocol=ProtocolConfig(
            name="CustomProtocol",
            treasury_balance=10_000_000.0,
            monthly_burn=500_000.0,
            emissions_per_day=20_000.0
        ),
        analysis=AnalysisConfig(
            fee_range={"start": 0, "end": 300, "step": 50},
            compare_fee=150,
            run_phases=["baseline", "runway", "safety", "unit_economics"]
        ),
        safety=SafetyConfig(
            min_runway_days=180,      # Stricter: 6 months
            max_fee_bps=200,          # Lower max: 2%
            min_volume_retention=0.9  # Higher retention: 90%
        ),
        output=OutputConfig(
            directory="./custom_reports",
            formats=["markdown", "json"]
        )
    )

    custom_config.to_yaml("examples/custom_config.yaml")
    print("✓ Created: examples/custom_config.yaml")
    print()

    # Example 4: CLI integration
    print("\nExample 4: CLI Integration")
    print("-" * 70)
    print("You can also use configs with the CLI:")
    print()
    print("  # Generate config interactively")
    print("  $ sentinel init")
    print()
    print("  # Generate config with flags")
    print("  $ sentinel init \\")
    print("      --scenario data/solana_day_1.csv \\")
    print("      --protocol MyProtocol \\")
    print("      --treasury 5000000")
    print()
    print("  # Validate config (dry-run)")
    print("  $ sentinel run-config sentinel.yaml --dry-run")
    print()
    print("  # Run analysis from config")
    print("  $ sentinel run-config sentinel.yaml")
    print()

    # Cleanup example files
    Path("examples/example_config.yaml").unlink(missing_ok=True)
    Path("examples/custom_config.yaml").unlink(missing_ok=True)

    print("="*70)
    print("Config Workflow Examples Complete!")
    print("="*70)
    print("\nKey Takeaways:")
    print("  - YAML configs enable repeatable, team-friendly workflows")
    print("  - Version control your configs alongside code")
    print("  - Pydantic validation ensures type safety")
    print("  - Integrates with CLI for automation")
    print()


if __name__ == "__main__":
    main()
