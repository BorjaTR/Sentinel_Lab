# Sentinel Cloud - Examples

This directory contains practical examples demonstrating how to use Sentinel Cloud for protocol tokenomics analysis.

## Prerequisites

Ensure Sentinel Cloud is installed:

```bash
pip install -e .
```

## Quick Start

Start with these examples in order:

### 1. Quickstart (`01_quickstart.py`)

Basic workflow covering:
- Initialize client
- Run single simulation
- Run parameter sweep
- Find optimal configuration

```bash
python examples/01_quickstart.py
```

**Time:** ~2 minutes
**Best for:** First-time users, understanding the basics

---

### 2. Quick Health Check (`02_quick_check.py`)

Fast protocol health assessment:
- Treasury runway projection
- Health status classification
- Actionable sustainability suggestions
- JSON export for integration

```bash
python examples/02_quick_check.py
```

**Time:** <30 seconds per check
**Best for:** Monitoring, alerts, quick assessments

---

### 3. Parameter Sweeps (`03_parameter_sweep.py`)

Comprehensive fee optimization:
- Uniform fee range sweeps
- Explicit fee list testing
- Finding optimal by metric
- Saving results for dashboard

```bash
python examples/03_parameter_sweep.py
```

**Time:** ~2-5 minutes depending on sweep size
**Best for:** Fee optimization, what-if analysis

---

### 4. Config-Driven Workflow (`04_config_workflow.py`)

Team-friendly YAML configurations:
- Generate default configs
- Load and validate
- Customize programmatically
- CLI integration

```bash
python examples/04_config_workflow.py
```

**Time:** <1 minute
**Best for:** Team workflows, CI/CD, repeatability

---

## Example Outputs

### Quick Check Output
```
📊 Status: WARNING
🏦 Treasury: $10,000,000
🛣️  Runway: 🟡 WARNING: 100 days

💰 Daily Flows:
   Revenue: $      25,000/day
   Burn:    $     100,000/day
   Net:     $     -75,000/day

💡 Suggestions:
   1. Increase fees to 350 bps (+325 bps) to achieve sustainability
   2. Reduce daily emissions from $100,000 to extend runway
```

### Parameter Sweep Output
```
Config             Fee      Revenue      Volume       Engine TPS  Lab TPS    Fail%
------------------------------------------------------------------------------------
0 bps (0.00%)      0   bps $   252,343 $528,419,722    100.00M      1.6K   0.0%
25 bps (0.25%)     25  bps $   252,343 $528,419,722    100.00M      1.6K   0.0%
50 bps (0.50%)     50  bps $   252,343 $528,419,722    100.00M      1.7K   0.0%

✅ Optimal Fee (by revenue): 50 bps (0.50%)
   Revenue:      $   252,343 USDC
   Volume:       $528,419,722 USDC
```

---

## Integration Patterns

### Jupyter Notebooks

```python
from sentinel_cloud import SentinelClient

client = SentinelClient()

# Quick check for monitoring
check = client.quick_check(
    scenario="data/my_protocol.csv",
    treasury=current_treasury_balance(),
    current_fee_bps=50,
    emissions_per_day=daily_emissions()
)

if check.status.value in ['critical', 'emergency']:
    send_alert(check.suggestions)
```

### Monitoring Scripts

```python
import schedule
from sentinel_cloud import SentinelClient

def daily_health_check():
    client = SentinelClient()
    check = client.quick_check(
        scenario=fetch_latest_transactions(),
        treasury=get_treasury_balance(),
        current_fee_bps=CURRENT_FEE,
        emissions_per_day=DAILY_EMISSIONS
    )

    log_to_dashboard(check.to_dict())

    if check.runway_days and check.runway_days < 90:
        alert_team(check)

schedule.every().day.at("09:00").do(daily_health_check)
```

### CI/CD Integration

```bash
# In your CI pipeline
sentinel run-config configs/production.yaml --dry-run
sentinel quick-check data/latest.csv --treasury $TREASURY --output json > report.json
```

---

## CLI Quick Reference

All examples can also be run via CLI:

```bash
# Quick health check
sentinel quick-check data/solana_day_1.csv \
    --mapper solana \
    --treasury 1000000 \
    --output text

# Full analysis
sentinel analyze data/solana_day_1.csv \
    --mapper solana \
    --treasury 1000000 \
    --output-dir ./reports

# Config-driven
sentinel init --scenario data/solana_day_1.csv
sentinel run-config sentinel.yaml
```

---

## Next Steps

- **Dashboard:** Run `streamlit run dashboard_v3.py` for visual analysis
- **Documentation:** See main [README.md](../README.md) for architecture
- **Advanced:** Explore `sentinel_cloud/` modules for custom analysis

---

## Troubleshooting

**"No module named sentinel_cloud"**
```bash
pip install -e .
```

**"Scenario file not found"**
- Ensure paths are relative to project root
- Use absolute paths if needed

**"Simulation failed"**
- Check CSV format matches expected mapper
- Verify cocotb and verilator are installed

---

## Support

- Issues: https://github.com/anthropics/sentinel-cloud/issues
- Docs: See main README.md
- Examples: This directory!
