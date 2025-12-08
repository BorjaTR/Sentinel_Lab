# Sentinel - Know Your Runway

![Status](https://img.shields.io/badge/Status-Active-00ff41)
![License](https://img.shields.io/badge/License-MIT-blue)
![Python](https://img.shields.io/badge/Python-3.8+-orange)

**Protocol sustainability ratings for crypto. Like Moody's, but for DAOs, L2s, and DeFi.**

```bash
$ sentinel score arbitrum.yaml

SENTINEL SCORE: 76/100 (Grade B)
Status: ✅ HEALTHY

Runway:          40/40  (infinite - profitable)
Sustainability:  27/30  (ratio: 1.20)
Diversification:  4/20  (revenue concentration risk)
Trajectory:       5/10  (neutral trend)

Summary: Healthy protocol with sustainable economics.
Recommendation: Diversify revenue streams beyond sequencer fees.
```

---

## 🎯 What is Sentinel?

**Sentinel** is a protocol sustainability rating system that helps crypto protocols answer critical questions:

- **How long can we survive** at current burn rate?
- **Is our revenue model sustainable** or are we bleeding treasury?
- **How risky is our revenue/treasury concentration?**
- **Will this governance proposal put us at risk?**

### Why It Matters

- **80% of DAOs** will run out of money in the next 24 months
- **Most protocols** have no idea when their treasury will hit zero
- **Governance votes** often pass without understanding financial impact
- **No standardized ratings** exist for protocol sustainability

Sentinel provides a **0-100 score** (like a credit score) that combines:
- **Runway** (40%): Months until treasury depletion
- **Sustainability** (30%): Revenue/cost ratio
- **Diversification** (20%): Revenue and treasury concentration
- **Trajectory** (10%): Improving or declining trend

---

## 🚀 Quick Start

### Installation

```bash
pip install -e .
```

### Basic Usage

**1. Score a protocol:**
```bash
sentinel score templates/dao/sample.yaml
```

**2. Analyze a governance proposal:**
```bash
sentinel proposal dao.yaml --add-cost "New Grant: 2000000"
# Shows before/after score impact
```

**3. Generate rankings:**
```bash
sentinel rankings protocols/ --output html --output-file rankings.html
# Compare multiple protocols side-by-side
```

**4. Validate a config:**
```bash
sentinel validate my_protocol.yaml
```

**5. Generate a template:**
```bash
sentinel init --template dao > my_protocol.yaml
```

---

## 📊 Sentinel Score System

### Score Components

| Component | Weight | What It Measures |
|-----------|--------|------------------|
| **Runway** | 40 pts | Months until treasury depletion at current burn rate |
| **Sustainability** | 30 pts | Revenue/Cost ratio (1.0 = break-even) |
| **Diversification** | 20 pts | Revenue concentration + Treasury composition |
| **Trajectory** | 10 pts | Historical trend (improving vs declining) |

### Grading Scale

| Grade | Score | Status | Meaning |
|-------|-------|--------|---------|
| **S** | 90+ | Healthy | Exceptional sustainability |
| **A** | 80-89 | Healthy | Strong financial position |
| **B** | 70-79 | Healthy | Solid fundamentals |
| **C** | 55-69 | Warning | Some concerns |
| **D** | 40-54 | Warning | Action recommended |
| **F** | <40 | Critical | Immediate intervention needed |

### Example Scores

- **Healthy DAO** (79/B): Profitable, but concentrated revenue
- **Sample DAO** (45/D): 340mo runway, but only 25% sustainability ratio
- **Critical DAO** (10/F): 5mo runway until insolvency

---

## 🛠️ Protocol Configuration

Sentinel uses **YAML configs** to define protocol economics:

```yaml
name: My Protocol
type: dao  # dao, l2, dex, lending, depin, gaming, bridge
chain: ethereum

treasury:
  holdings:
    - symbol: USDC
      amount: 10000000
      current_price_usd: 1.0
      is_stable: true
    - symbol: TOKEN
      amount: 500000000
      current_price_usd: 2.00
      is_native: true

revenue_streams:
  - name: protocol_fees
    monthly_usd: 500000
    description: Trading fees
    confidence: high

cost_streams:
  - name: team
    monthly_usd: 300000
    description: Core team
    is_discretionary: false
  - name: grants
    monthly_usd: 500000
    description: Ecosystem grants
    is_discretionary: true

data_sources:
  - https://dune.com/my_protocol
last_updated: "2025-01-15"
```

**See `templates/` for examples of different protocol types.**

---

## 📈 Features

### 1. Protocol Scoring
Calculate 0-100 sustainability score with breakdown by component.

```bash
sentinel score protocol.yaml --verbose
```

### 2. Proposal Impact Analysis
Simulate governance proposals before voting:

```bash
# Adding a new cost
sentinel proposal dao.yaml --add-cost "Marketing: 200000"

# Modifying existing costs
sentinel proposal dao.yaml --modify-cost "grants: 1500000"

# Adding revenue
sentinel proposal dao.yaml --add-revenue "New Product: 500000"

# Combined changes
sentinel proposal dao.yaml \
  --add-cost "Program: 1000000" \
  --add-revenue "Fees: 800000"
```

**Output shows:**
- Before/After score comparison
- Runway impact
- Warnings if proposal is risky
- Alternative recommendations

### 3. Protocol Rankings
Compare multiple protocols side-by-side:

```bash
# Text table
sentinel rankings protocols/

# Markdown for docs
sentinel rankings protocols/ --output markdown > rankings.md

# HTML page for sharing
sentinel rankings protocols/ --output html --output-file rankings.html

# JSON for APIs
sentinel rankings protocols/ --output json > rankings.json
```

### 4. Config Validation
Ensure your protocol config is valid:

```bash
sentinel validate protocol.yaml
```

---

## 🏆 Protocol Examples

| Protocol | Type | Score | Grade | Status | Runway |
|----------|------|-------|-------|--------|--------|
| Healthy DAO | DAO | 79 | B | ✅ Healthy | ∞ (profitable) |
| Sample L2 | L2 | 76 | B | ✅ Healthy | ∞ (profitable) |
| Sample DEX | DEX | 69 | C | ⚠️ Warning | ∞ (profitable) |
| Sample DAO | DAO | 45 | D | ⚠️ Warning | 340mo |
| Critical DAO | DAO | 10 | F | 🚨 Critical | 5mo |

**Full rankings:** Run `sentinel rankings templates/`

---

## 📁 Repository Structure

```
Sentinel_Lab/
├── sentinel_cloud/           # Core Sentinel engine
│   ├── protocol_config.py    # Universal protocol schema
│   ├── score.py              # Scoring algorithm
│   ├── proposal.py           # Proposal impact analyzer
│   ├── rankings.py           # Multi-protocol rankings
│   └── cli/
│       └── main.py           # CLI commands
├── templates/                # Example protocol configs
│   ├── dao/                  # DAO examples
│   ├── l2/                   # L2 examples
│   └── dex/                  # DEX examples
├── rtl/                      # Hardware acceleration (FPGA)
│   └── ledger_core.sv        # Exchange engine (100M TPS)
├── tb/                       # Hardware verification
└── tests/                    # Test suite
```

---

## 🎓 Use Cases

### For Protocol Teams
- **Monitor financial health** with objective metrics
- **Model governance proposals** before voting
- **Communicate sustainability** to token holders
- **Benchmark** against similar protocols

### For Investors & Analysts
- **Compare protocols** objectively across types
- **Identify risks** early (runway, concentration)
- **Track trajectory** over time
- **Due diligence** for investments

### For Governance Participants
- **Evaluate proposals** with financial impact
- **Avoid risky votes** that hurt sustainability
- **See alternatives** to maintain current runway
- **Make informed decisions** with data

---

## 🔬 Technical Architecture

Sentinel combines **software analysis** with optional **hardware acceleration**:

### Software Layer: Protocol Analysis
- **Python SDK** for protocol scoring
- **YAML configuration** for protocol definitions
- **CLI tools** for quick analysis
- **Scoring algorithms** based on financial metrics

### Hardware Layer: Exchange Simulation (Optional)
- **FPGA-accelerated** settlement engine (100M TPS)
- **Real-time simulation** of tokenomics scenarios
- **Hardware verification** via SystemVerilog
- **Mainnet replay** for accuracy testing

**The hardware layer enables high-speed parameter sweeps and stress testing.**

See [Hardware Deep Dive](#-hardware-acceleration-optional) for details.

---

## 📊 Methodology

### Runway Score (0-40 points)
```
Months >= 48:  40 points
Months >= 36:  35 points
Months >= 24:  30 points
Months >= 18:  25 points
Months >= 12:  20 points
Months >= 6:   10 points
Months < 3:     0 points
```

### Sustainability Score (0-30 points)
Based on monthly revenue / monthly costs:
```
Ratio >= 1.5:  30 points (highly profitable)
Ratio >= 1.2:  27 points (profitable with margin)
Ratio >= 1.0:  24 points (break-even)
Ratio >= 0.8:  18 points (slight deficit)
Ratio >= 0.6:  12 points (significant deficit)
Ratio < 0.4:    0 points (critical)
```

### Diversification Score (0-20 points)
- **Revenue Concentration** (0-10): Uses HHI (Herfindahl-Hirschman Index)
- **Treasury Composition** (0-10): Stablecoin vs native token ratio

### Trajectory Score (0-10 points)
Compares current vs 3-month-ago metrics:
- Improving revenue/costs: +10 points
- Stable: 5 points
- Declining: 0 points

---

## 🤝 Contributing

Current priorities:
1. **Protocol profiles** - Research and create configs for real protocols (Arbitrum, Optimism, Uniswap, Aave)
2. **Historical data** - Add trajectory tracking for major protocols
3. **Governance integration** - Pull proposals from Snapshot/Tally
4. **Public rankings page** - Deploy to GitHub Pages

See [Issues](https://github.com/BorjaTR/Sentinel_Lab/issues) for full backlog.

---

## 📚 Documentation

- **[Quick Start Guide](QUICKSTART.md)** - Get started in 5 minutes
- **[Protocol Config Schema](templates/)** - YAML configuration reference
- **[Scoring Methodology](docs/methodology.md)** - How scores are calculated
- **[CLI Reference](docs/cli.md)** - Complete command documentation

---

## 🛡️ Hardware Acceleration (Optional)

Sentinel includes an **FPGA-based settlement engine** for high-speed tokenomics simulation:

### Performance
- **99.98M TPS** throughput (1 tx/cycle @ 200MHz)
- **10ns latency** (2-stage pipeline)
- **Atomic swaps** with conservation guarantees
- **Mainnet replay** of 50K+ Solana transactions

### Architecture
```
┌─────────────────────────────────────────────┐
│  Python Analysis Layer (Sentinel Score)    │
└─────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────┐
│  Hardware Simulation (FPGA/Verilator)      │
│  - Multi-asset portfolio engine            │
│  - Parameter sweep acceleration            │
│  - Real-time stress testing                │
└─────────────────────────────────────────────┘
```

### Running Hardware Simulations

```bash
# Install hardware dependencies
pip install cocotb==1.8.1
apt-get install verilator

# Run simulation
cd tb && make

# View results
python3 run_lab.py --scenario data/solana_day_1.csv
```

**Note:** Hardware simulation is optional. All core Sentinel features work without FPGA tools.

---

## 📊 Example Output

### Sentinel Score Report
```
============================================================
SENTINEL SCORE REPORT
============================================================
Protocol: Sample L2
Type: L2
Chain: ethereum

SCORE: 76/100 (Grade: B)
Status: ✅ HEALTHY

BREAKDOWN
------------------------------------------------------------
Runway:          40/40  (∞ - profitable)
Sustainability:  27/30  (ratio: 1.20)
Diversification:  4/20  (concentration risk)
Trajectory:       5/10  (neutral)

SUMMARY
------------------------------------------------------------
Healthy protocol with sustainable economics. Minor revenue
diversification improvements possible.

TOP RECOMMENDATIONS
------------------------------------------------------------
1. Treasury is 90% native token. Consider diversifying to stables.
2. Revenue highly concentrated in sequencer fees. Explore additional sources.

Data sources: https://l2beat.com
Last updated: 2025-01-15
============================================================
```

### Proposal Impact Analysis
```
============================================================
PROPOSAL IMPACT ANALYSIS
============================================================
Protocol: Sample DAO

PROPOSED CHANGES
------------------------------------------------------------
ADD COST: New Initiative = $1,000,000/mo

SCORE IMPACT
------------------------------------------------------------
Before: 45/100 (Grade D) - Warning
After:  45/100 (Grade D) - Warning
Change: +0 points

KEY METRICS
------------------------------------------------------------
Runway:         340.0 months → 204.0 months
Sustainability: 0.25 → 0.17

⚠️  WARNINGS
------------------------------------------------------------
  ⚠️  Runway decreases by 136.0 months
  ⚠️  Sustainability ratio falls to 17%

RECOMMENDATIONS
------------------------------------------------------------
1. Consider adding $1,000,000/month in revenue to offset cost increases
2. Consider phased rollout: start with 50% funding for 3 months, then evaluate

ALTERNATIVES TO CONSIDER
------------------------------------------------------------
1. Alternative: Add 'New Initiative' at $500,000/mo (50% reduction)
2. Alternative: Pair with new revenue stream of $1,000,000/mo to maintain runway
============================================================
```

---

## 🎯 Roadmap

### Phase 1-3: Core Engine ✅ COMPLETE
- [x] Sentinel Score calculation (runway, sustainability, diversification, trajectory)
- [x] Proposal impact analyzer
- [x] Rankings system (HTML, markdown, JSON)
- [x] CLI commands (score, proposal, rankings, validate, init)
- [x] Universal protocol config schema

### Phase 4: Protocol Profiles (In Progress)
- [ ] Research and create configs for real protocols
  - [ ] Arbitrum (L2)
  - [ ] Optimism (L2)
  - [ ] Uniswap (DEX)
  - [ ] Aave (Lending)
  - [ ] Helium (DePIN)
- [ ] Validate with on-chain data
- [ ] Document data sources

### Phase 5: Public Rankings
- [ ] Deploy rankings page to GitHub Pages
- [ ] Automated updates from configs
- [ ] Methodology documentation
- [ ] Protocol submission guidelines

### Phase 6: Governance Integration
- [ ] Pull proposals from Snapshot
- [ ] Auto-analyze financial impact
- [ ] Publish impact reports
- [ ] Discord/Telegram bots

### Phase 7: Historical Tracking
- [ ] Time-series data collection
- [ ] Trajectory analysis improvements
- [ ] Trend detection
- [ ] Alerts for declining protocols

---

## 💡 Why "Sentinel"?

A **sentinel** stands guard, watching for threats. Sentinel watches protocol treasuries, alerting teams before it's too late.

**Know your runway. Protect your protocol.**

---

## 📜 License

MIT License - see [LICENSE](LICENSE) for details

---

## 🤝 Contact

- **GitHub Issues:** [BorjaTR/Sentinel_Lab](https://github.com/BorjaTR/Sentinel_Lab/issues)
- **Author:** Borja Tarazona Raga

---

**Status:** v1.0 Active | Phases 1-3 Complete
**Tagline:** Know your runway
**Mission:** Prevent DAO treasury insolvency through objective sustainability ratings
