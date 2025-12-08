# Sentinel Score Methodology

## Overview

The **Sentinel Score** is a 0-100 composite metric that measures protocol sustainability across four key dimensions. Like a credit score, it provides an objective, standardized assessment of financial health that enables:

- **Protocol teams** to monitor sustainability
- **Governance participants** to evaluate proposals
- **Investors** to compare protocols objectively
- **Community members** to understand financial risks

## Scoring Components

### 1. Runway Score (0-40 points)

**Weight:** 40% of total score

**What it measures:** Months until treasury depletion at current burn rate

**Calculation:**
```python
if monthly_net >= 0:
    runway_months = ∞ (profitable)
else:
    runway_months = treasury_balance / abs(monthly_net)
```

**Scoring tiers:**
```
Months >= 48:  40 points (4+ years - excellent)
Months >= 36:  35 points (3 years - strong)
Months >= 24:  30 points (2 years - good)
Months >= 18:  25 points (1.5 years - adequate)
Months >= 12:  20 points (1 year - concerning)
Months >= 9:   15 points (9 months - at risk)
Months >= 6:   10 points (6 months - urgent)
Months >= 3:    5 points (3 months - critical)
Months < 3:     0 points (emergency)
```

**Rationale:**
- Runway is the most fundamental sustainability metric
- Protocols need sufficient time to adapt to market changes
- 18-24 months provides reasonable planning horizon
- Less than 6 months requires immediate action

**Examples:**
- **Profitable protocol** (revenue > costs): 40/40 points (∞ runway)
- **24-month runway**: 30/40 points
- **6-month runway**: 10/40 points
- **2-month runway**: 0/40 points

---

### 2. Sustainability Score (0-30 points)

**Weight:** 30% of total score

**What it measures:** Revenue/cost ratio

**Calculation:**
```python
if monthly_costs == 0:
    sustainability_ratio = ∞
else:
    sustainability_ratio = monthly_revenue / monthly_costs
```

**Scoring tiers:**
```
Ratio >= 1.5:  30 points (highly profitable - 50%+ margin)
Ratio >= 1.2:  27 points (profitable with margin - 20% margin)
Ratio >= 1.0:  24 points (break-even)
Ratio >= 0.8:  18 points (slight deficit - 20% shortfall)
Ratio >= 0.6:  12 points (significant deficit - 40% shortfall)
Ratio >= 0.4:   6 points (severe deficit - 60% shortfall)
Ratio < 0.4:    0 points (critical deficit)
```

**Rationale:**
- Revenue/cost ratio indicates operational efficiency
- Ratios above 1.0 mean the protocol is self-sustaining
- Ratios below 0.6 indicate fundamental business model issues
- Sustainable protocols should target 1.2+ for buffer against volatility

**Examples:**
- **$10M revenue / $6M costs** = 1.67 ratio = 30/30 points
- **$5M revenue / $5M costs** = 1.00 ratio = 24/30 points
- **$2M revenue / $5M costs** = 0.40 ratio = 6/30 points

---

### 3. Diversification Score (0-20 points)

**Weight:** 20% of total score

**What it measures:** Revenue concentration + Treasury composition

**Components:**

#### A. Revenue Concentration (0-10 points)

Uses the **Herfindahl-Hirschman Index (HHI)** to measure concentration:

```python
# Calculate market shares
shares = [stream.monthly_usd / total_revenue for stream in revenue_streams]

# Calculate HHI (sum of squared shares)
hhi = sum(share ** 2 for share in shares)
```

**Scoring:**
```
HHI >= 0.90:  0 points (monopoly - single source dominance)
HHI >= 0.70:  2 points (highly concentrated)
HHI >= 0.50:  4 points (moderately concentrated)
HHI >= 0.35:  6 points (somewhat diversified)
HHI >= 0.25:  8 points (diversified)
HHI < 0.25:  10 points (highly diversified)
```

**Examples:**
- **Single revenue source**: HHI = 1.0 = 0/10 points
- **Two equal sources** (50%/50%): HHI = 0.5 = 4/10 points
- **Three equal sources** (33%/33%/33%): HHI = 0.33 = 6/10 points
- **Five equal sources** (20% each): HHI = 0.2 = 10/10 points

#### B. Treasury Composition (0-10 points)

Measures stablecoin vs native token ratio:

```python
stables_ratio = treasury_stables_usd / treasury_total_usd
```

**Scoring:**
```
Stables >= 70%:  10 points (low risk - mostly stables)
Stables >= 50%:   8 points (balanced)
Stables >= 30%:   6 points (moderate risk)
Stables >= 15%:   4 points (high risk)
Stables >= 5%:    2 points (very high risk)
Stables < 5%:     0 points (critical risk - nearly all native token)
```

**Rationale:**
- Concentrated revenue is risky (single point of failure)
- Treasury heavily in native token creates price exposure
- Diversification provides resilience against shocks
- Stablecoins provide liquidity and reduce volatility risk

**Examples:**
- **L2 with 3 revenue sources, 20% stables**: 6 + 4 = 10/20 points
- **DEX with 1 revenue source, 5% stables**: 0 + 2 = 2/20 points
- **DAO with 4 revenue sources, 60% stables**: 8 + 8 = 16/20 points

---

### 4. Trajectory Score (0-10 points)

**Weight:** 10% of total score

**What it measures:** Historical trend (improving vs declining)

**Calculation:**
Requires at least 2 historical snapshots (current vs 3-months-ago):

```python
# Compare monthly net income
current_net = current.monthly_revenue - current.monthly_costs
previous_net = previous.monthly_revenue - previous.monthly_costs

# Calculate percentage change
net_change_pct = (current_net - previous_net) / abs(previous_net)

# Also consider runway change
runway_change = current.runway_months - previous.runway_months
```

**Scoring:**
```
Strong improvement (20%+ net increase, runway growing):      10 points
Moderate improvement (10%+ net increase or 3+mo runway):      8 points
Stable (net change within ±10%, runway stable):               6 points
Slight decline (-10% to -20% net, runway down <3mo):          4 points
Moderate decline (-20% to -40% net):                          2 points
Rapid decline (>40% net decrease):                            0 points
```

**Default:** If no historical data available, protocols receive **5 points** (neutral)

**Rationale:**
- Trajectory indicates whether issues are improving or worsening
- Declining protocols may have structural problems
- Improving protocols demonstrate adaptability
- Neutral default prevents penalizing new protocols without history

**Examples:**
- **Revenue growing, costs stable**: 10/10 points
- **Revenue flat, costs increasing slowly**: 4/10 points
- **Revenue declining 30%, costs growing**: 0/10 points

---

## Total Score Calculation

```python
total_score = (
    runway_score +          # 0-40 points
    sustainability_score +  # 0-30 points
    diversification_score + # 0-20 points
    trajectory_score        # 0-10 points
)  # Total: 0-100 points
```

## Letter Grades

| Grade | Score Range | Description |
|-------|-------------|-------------|
| **S** | 90-100 | Exceptional - Best-in-class sustainability |
| **A** | 80-89 | Excellent - Strong financial position |
| **B** | 70-79 | Good - Solid fundamentals |
| **C** | 55-69 | Fair - Some concerns |
| **D** | 40-54 | Poor - Action recommended |
| **F** | 0-39 | Failing - Immediate intervention needed |

## Status Classification

| Status | Score Range | Indicator |
|--------|-------------|-----------|
| **Healthy** | 70+ | ✅ Protocol is sustainable |
| **Warning** | 45-69 | ⚠️ Issues require attention |
| **Critical** | <45 | 🚨 Protocol at risk |

---

## Example Calculations

### Example 1: Healthy L2

**Inputs:**
- Treasury: $1B ($800M native token, $200M stables)
- Monthly revenue: $16M (sequencer fees: $12M, MEV: $3M, other: $1M)
- Monthly costs: $16M (DA: $6M, team: $3M, grants: $4M, infra: $3M)

**Calculation:**
- **Runway**: Profitable (revenue = costs) = 40/40 points
- **Sustainability**: 16/16 = 1.0 ratio = 24/30 points
- **Diversification**:
  - Revenue HHI = 0.75² + 0.19² + 0.06² = 0.60 = 4/10 points
  - Stables = 200/1000 = 20% = 4/10 points
  - Total = 8/20 points
- **Trajectory**: No history = 5/10 points (neutral)

**Total Score:** 40 + 24 + 8 + 5 = **77/100 (Grade B)** ✅ Healthy

### Example 2: Critical DAO

**Inputs:**
- Treasury: $10M ($9.5M native token, $0.5M stables)
- Monthly revenue: $50K
- Monthly costs: $2M (team: $1.5M, ops: $0.5M)

**Calculation:**
- **Runway**: 10M / 1.95M = 5.1 months = 10/40 points
- **Sustainability**: 50K/2M = 0.025 ratio = 0/30 points
- **Diversification**:
  - Revenue HHI = 1.0 (single source) = 0/10 points
  - Stables = 0.5/10 = 5% = 2/10 points
  - Total = 2/20 points
- **Trajectory**: No history = 5/10 points

**Total Score:** 10 + 0 + 2 + 5 = **17/100 (Grade F)** 🚨 Critical

---

## Interpreting Scores

### Score Ranges by Component

**Strong Performance:**
- Runway: 35-40 points (36+ months or profitable)
- Sustainability: 27-30 points (1.2+ ratio)
- Diversification: 15-20 points (3+ revenue sources, 30%+ stables)
- Trajectory: 8-10 points (improving metrics)

**Concerning Performance:**
- Runway: 0-15 points (<9 months)
- Sustainability: 0-12 points (<0.6 ratio)
- Diversification: 0-5 points (1 revenue source, <10% stables)
- Trajectory: 0-4 points (declining rapidly)

### Common Patterns

**High Score, Low Diversification (70-79):**
- Protocol is profitable but concentrated
- Risk: Single point of failure in revenue or treasury crash
- Action: Diversify revenue streams and treasury composition

**Medium Runway, Low Sustainability (40-54):**
- Large treasury but unsustainable burn
- Risk: Will eventually deplete treasury
- Action: Increase revenue or reduce costs to reach break-even

**Good Fundamentals, Declining Trajectory (55-69):**
- Currently stable but trends are negative
- Risk: Issues compounding over time
- Action: Investigate root causes of decline

---

## Limitations

### What the Score Doesn't Measure

1. **Protocol Quality**: Code quality, security, user experience
2. **Market Position**: Competitive advantages, network effects
3. **Team Quality**: Execution ability, reputation
4. **Token Economics**: Emission schedules, tokenomics design
5. **Qualitative Risks**: Regulatory, technological, market risks
6. **Growth Potential**: Total addressable market, expansion opportunities

### Data Quality Dependencies

The score is only as good as the input data:

- **Self-reported data** may be inaccurate or outdated
- **Incomplete data** (missing revenue streams, costs) skews results
- **Estimates** for monthly revenue/costs introduce uncertainty
- **Price volatility** affects native token treasury values
- **One-time events** (airdrops, hacks) can distort metrics

### Recommendation

**Use the Sentinel Score as ONE input** in a comprehensive evaluation alongside:
- On-chain data verification
- Governance activity analysis
- Community health metrics
- Technical security audits
- Market and competitive analysis

---

## Frequently Asked Questions

### Why is runway weighted highest (40%)?

Runway is the most fundamental metric - without sufficient runway, nothing else matters. A protocol can have great revenue diversification but if it runs out of money in 2 months, it's not sustainable.

### Why do profitable protocols always get 40/40 runway points?

Being profitable (revenue >= costs) means infinite theoretical runway. This is the ideal state and deserves maximum points. However, total score still depends on other factors like diversification.

### How often should protocols update their scores?

**Minimum:** Quarterly (matches historical trajectory calculation)
**Recommended:** Monthly (reflects typical governance cycles)
**Ideal:** Real-time (for protocols with automated data pipelines)

### Can a protocol with a low score recover?

Yes! The score reflects current state, not destiny. Protocols can:
- Reduce discretionary costs to extend runway
- Launch new revenue streams to improve sustainability
- Diversify treasury to reduce concentration risk
- Show improvement via trajectory component

### Why use HHI instead of simpler concentration metrics?

HHI (Herfindahl-Hirschman Index) is the standard metric in economics and antitrust analysis. It's sensitive to both the number of sources and their relative sizes, providing more nuanced measurement than simple counts.

### What if a protocol has no costs?

If monthly costs = 0, sustainability ratio = ∞ and the protocol receives 30/30 points. However, this is rare - most protocols have at least infrastructure or development costs.

### How do you handle one-time revenues or costs?

The methodology focuses on **recurring monthly flows**. One-time events should not be included in monthly revenue/costs but may affect treasury balance. Document one-time events in the protocol config notes.

---

## Version History

- **v1.0** (2025-01-15): Initial methodology release
  - Four-component scoring system
  - 0-100 scale with letter grades
  - HHI-based diversification measurement

---

## Contact

For questions about the methodology or to suggest improvements:
- GitHub Issues: [BorjaTR/Sentinel_Lab](https://github.com/BorjaTR/Sentinel_Lab/issues)
- Label: `methodology`

---

**Sentinel - Know your runway**
