"""
Universal protocol configuration schema for Sentinel.

Supports all protocol types: DAOs, L2s, DEX, Lending, DePIN, etc.
"""
from pydantic import BaseModel, Field
from typing import Literal, Optional
from enum import Enum
from pathlib import Path
import yaml


class ProtocolType(str, Enum):
    DAO = "dao"
    L2 = "l2"
    DEX = "dex"
    LENDING = "lending"
    DEPIN = "depin"
    GAMING = "gaming"
    BRIDGE = "bridge"
    OTHER = "other"


class TokenHolding(BaseModel):
    symbol: str
    amount: float
    current_price_usd: float
    is_native: bool = False
    is_stable: bool = False

    @property
    def value_usd(self) -> float:
        return self.amount * self.current_price_usd


class Treasury(BaseModel):
    holdings: list[TokenHolding] = Field(default_factory=list)
    total_usd_override: Optional[float] = None
    stables_usd_override: Optional[float] = None

    @property
    def balance_usd(self) -> float:
        if self.total_usd_override is not None:
            return self.total_usd_override
        return sum(h.value_usd for h in self.holdings)

    @property
    def stables_usd(self) -> float:
        if self.stables_usd_override is not None:
            return self.stables_usd_override
        return sum(h.value_usd for h in self.holdings if h.is_stable)

    @property
    def native_token_usd(self) -> float:
        return sum(h.value_usd for h in self.holdings if h.is_native)

    @property
    def stables_ratio(self) -> float:
        if self.balance_usd == 0:
            return 0
        return self.stables_usd / self.balance_usd


class RevenueStream(BaseModel):
    name: str
    monthly_usd: float
    description: str = ""
    is_recurring: bool = True
    confidence: Literal["high", "medium", "low"] = "medium"


class CostStream(BaseModel):
    name: str
    monthly_usd: float
    description: str = ""
    is_fixed: bool = True
    is_discretionary: bool = False
    confidence: Literal["high", "medium", "low"] = "medium"


class Parameter(BaseModel):
    """A lever that governance can adjust."""
    name: str
    description: str = ""
    kind: Literal["revenue", "cost", "rate", "allocation"]
    current_value: float
    min_value: float
    max_value: float
    step: float
    unit: str = ""
    affects_stream: Optional[str] = None
    elasticity: Optional[float] = None


class HistoricalSnapshot(BaseModel):
    """For trajectory calculation."""
    date: str  # ISO format
    treasury_usd: float
    monthly_revenue: float
    monthly_costs: float


class ProtocolConfig(BaseModel):
    """Universal protocol configuration."""

    # Identity
    name: str
    type: ProtocolType
    chain: str = "ethereum"
    website: str = ""
    governance_forum: str = ""

    # Treasury
    treasury: Treasury

    # Flows
    revenue_streams: list[RevenueStream] = Field(default_factory=list)
    cost_streams: list[CostStream] = Field(default_factory=list)

    # Adjustable parameters
    parameters: list[Parameter] = Field(default_factory=list)

    # Historical data
    history: list[HistoricalSnapshot] = Field(default_factory=list)

    # Metadata
    data_sources: list[str] = Field(default_factory=list)
    last_updated: str = ""
    notes: str = ""

    @property
    def monthly_revenue(self) -> float:
        return sum(s.monthly_usd for s in self.revenue_streams)

    @property
    def monthly_costs(self) -> float:
        return sum(s.monthly_usd for s in self.cost_streams)

    @property
    def monthly_net(self) -> float:
        return self.monthly_revenue - self.monthly_costs

    @property
    def monthly_burn(self) -> float:
        return max(0, -self.monthly_net)

    @property
    def sustainability_ratio(self) -> float:
        if self.monthly_costs == 0:
            return float('inf')
        return self.monthly_revenue / self.monthly_costs

    @property
    def runway_months(self) -> float:
        if self.monthly_net >= 0:
            return float('inf')
        if self.monthly_burn == 0:
            return float('inf')
        return self.treasury.balance_usd / self.monthly_burn

    @property
    def is_profitable(self) -> bool:
        return self.monthly_net >= 0

    @classmethod
    def from_yaml(cls, path: str | Path) -> 'ProtocolConfig':
        """Load protocol config from YAML file."""
        with open(path, 'r') as f:
            data = yaml.safe_load(f)
        return cls(**data)

    def to_yaml(self, path: str | Path) -> None:
        """Save protocol config to YAML file."""
        data = self.model_dump(exclude_none=True)
        with open(path, 'w') as f:
            yaml.dump(data, f, default_flow_style=False, sort_keys=False)
