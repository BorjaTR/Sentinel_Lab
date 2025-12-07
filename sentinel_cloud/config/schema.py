"""
Pydantic models for Sentinel Cloud YAML configuration.

Validates sentinel.yaml config files.
"""

from typing import Optional, List, Literal
from pathlib import Path
from pydantic import BaseModel, Field, validator
import yaml


class ScenarioConfig(BaseModel):
    """Scenario data configuration."""
    path: str = Field(..., description="Path to transaction data CSV file")
    mapper: str = Field(default="depin_rewards", description="Data mapper type")

    @validator('path')
    def path_must_exist(cls, v):
        """Validate that the path exists."""
        if not Path(v).exists():
            raise ValueError(f"Scenario file not found: {v}")
        return v

    @validator('mapper')
    def mapper_must_be_valid(cls, v):
        """Validate mapper type."""
        valid_mappers = ['depin_rewards', 'depin_penalty', 'solana', 'evm_erc20']
        if v not in valid_mappers:
            raise ValueError(f"Invalid mapper '{v}'. Must be one of: {', '.join(valid_mappers)}")
        return v


class ProtocolConfig(BaseModel):
    """Protocol-specific configuration."""
    name: str = Field(..., description="Protocol name")
    treasury_balance: float = Field(..., description="Current treasury balance in USD", gt=0)
    monthly_burn: Optional[float] = Field(None, description="Monthly burn rate (auto-detected if null)")
    emissions_per_day: Optional[float] = Field(None, description="Daily emissions in USD for unit economics")

    @validator('treasury_balance')
    def treasury_must_be_positive(cls, v):
        """Validate treasury balance."""
        if v <= 0:
            raise ValueError("treasury_balance must be positive")
        return v


class AnalysisConfig(BaseModel):
    """Analysis pipeline configuration."""
    fee_range: Optional[dict] = Field(
        default={'start': 0, 'end': 200, 'step': 25},
        description="Fee sweep range configuration"
    )
    compare_fee: Optional[int] = Field(None, description="Proposed fee for before/after comparison")
    run_phases: List[str] = Field(
        default=['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'],
        description="Which phases to run"
    )

    @validator('fee_range')
    def validate_fee_range(cls, v):
        """Validate fee range."""
        if v is not None:
            if 'start' not in v or 'end' not in v or 'step' not in v:
                raise ValueError("fee_range must have 'start', 'end', and 'step'")
            if v['start'] < 0 or v['end'] < v['start'] or v['step'] <= 0:
                raise ValueError("Invalid fee range values")
        return v

    @validator('run_phases')
    def validate_phases(cls, v):
        """Validate phase list."""
        valid_phases = {'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'}
        for phase in v:
            if phase not in valid_phases:
                raise ValueError(f"Invalid phase '{phase}'. Must be one of: {', '.join(valid_phases)}")
        return v


class SafetyConfig(BaseModel):
    """Safety threshold configuration."""
    min_runway_days: int = Field(default=180, description="Minimum acceptable runway in days", ge=0)
    max_fee_bps: int = Field(default=100, description="Maximum acceptable fee in basis points", ge=0)
    min_volume_retention: float = Field(default=0.7, description="Minimum volume retention ratio", ge=0, le=1)

    @validator('min_runway_days')
    def runway_reasonable(cls, v):
        """Validate runway threshold."""
        if v < 0 or v > 3650:  # Max 10 years
            raise ValueError("min_runway_days must be between 0 and 3650")
        return v


class OutputConfig(BaseModel):
    """Output configuration."""
    directory: str = Field(default="./reports", description="Output directory for reports")
    formats: List[Literal['markdown', 'json', 'pdf']] = Field(
        default=['markdown', 'json'],
        description="Output formats"
    )

    @validator('formats')
    def validate_formats(cls, v):
        """Validate output formats."""
        if not v:
            raise ValueError("At least one output format must be specified")
        valid_formats = {'markdown', 'json', 'pdf'}
        for fmt in v:
            if fmt not in valid_formats:
                raise ValueError(f"Invalid format '{fmt}'. Must be one of: {', '.join(valid_formats)}")
        return v


class SentinelConfig(BaseModel):
    """
    Root configuration model for Sentinel Cloud.

    This represents the complete sentinel.yaml structure.
    """
    version: int = Field(default=1, description="Config file version")
    scenario: ScenarioConfig = Field(..., description="Scenario data configuration")
    protocol: ProtocolConfig = Field(..., description="Protocol configuration")
    analysis: AnalysisConfig = Field(default_factory=AnalysisConfig, description="Analysis configuration")
    safety: SafetyConfig = Field(default_factory=SafetyConfig, description="Safety thresholds")
    output: OutputConfig = Field(default_factory=OutputConfig, description="Output configuration")

    @validator('version')
    def version_must_be_supported(cls, v):
        """Validate config version."""
        if v != 1:
            raise ValueError(f"Unsupported config version: {v}. Only version 1 is supported.")
        return v

    @classmethod
    def from_yaml(cls, path: str) -> 'SentinelConfig':
        """
        Load configuration from YAML file.

        Args:
            path: Path to sentinel.yaml file

        Returns:
            Validated SentinelConfig instance

        Raises:
            FileNotFoundError: If config file doesn't exist
            ValueError: If YAML is invalid or validation fails
        """
        yaml_path = Path(path)
        if not yaml_path.exists():
            raise FileNotFoundError(f"Config file not found: {path}")

        with open(yaml_path, 'r') as f:
            try:
                data = yaml.safe_load(f)
            except yaml.YAMLError as e:
                raise ValueError(f"Invalid YAML: {e}")

        if data is None:
            raise ValueError("Config file is empty")

        return cls(**data)

    def to_yaml(self, path: str) -> None:
        """
        Save configuration to YAML file.

        Args:
            path: Path to save sentinel.yaml
        """
        yaml_path = Path(path)
        yaml_path.parent.mkdir(parents=True, exist_ok=True)

        with open(yaml_path, 'w') as f:
            yaml.dump(
                self.dict(exclude_none=True),
                f,
                default_flow_style=False,
                sort_keys=False,
                indent=2
            )

    def validate_all(self) -> List[str]:
        """
        Run all validations and return list of warnings.

        Returns:
            List of warning messages (empty if all good)
        """
        warnings = []

        # Check for common issues
        if self.safety.min_runway_days < 90:
            warnings.append(f"⚠️  min_runway_days is very low ({self.safety.min_runway_days}). Consider >= 90 days.")

        if self.protocol.treasury_balance < 100000:
            warnings.append(f"⚠️  treasury_balance is very low (${self.protocol.treasury_balance:,.0f})")

        if self.analysis.compare_fee and self.analysis.compare_fee > self.safety.max_fee_bps:
            warnings.append(f"⚠️  compare_fee ({self.analysis.compare_fee}bps) exceeds max_fee_bps ({self.safety.max_fee_bps}bps)")

        return warnings


def generate_default_config(
    scenario_path: str,
    protocol_name: str,
    treasury_balance: float
) -> SentinelConfig:
    """
    Generate a default configuration with minimal inputs.

    Args:
        scenario_path: Path to transaction data
        protocol_name: Name of the protocol
        treasury_balance: Current treasury balance

    Returns:
        SentinelConfig with sensible defaults
    """
    return SentinelConfig(
        version=1,
        scenario=ScenarioConfig(
            path=scenario_path,
            mapper="depin_rewards"
        ),
        protocol=ProtocolConfig(
            name=protocol_name,
            treasury_balance=treasury_balance
        ),
        analysis=AnalysisConfig(),
        safety=SafetyConfig(),
        output=OutputConfig()
    )
