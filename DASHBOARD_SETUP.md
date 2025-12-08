# Sentinel Cloud Dashboard Setup

## Running on Linux Server (Recommended)

The dashboard should be run on the Linux server where all simulation tools are installed.

### Quick Start

```bash
# 1. Navigate to the project directory
cd /home/user/Sentinel_Lab

# 2. Run the dashboard
streamlit run dashboard_v3.py

# 3. Access from your browser
# The dashboard will be available at:
# http://<server-ip>:8501
```

### Remote Access

If you're connecting from your local machine:

```bash
# SSH with port forwarding
ssh -L 8501:localhost:8501 user@server-ip

# Then access the dashboard at:
# http://localhost:8501
```

## Features

- **Quick Check**: Fast protocol health assessment
- **Parameter Sweeps**: Test fee configurations (0-200 bps)
- **Experiment Comparison**: Compare multiple sweep results
- **Real-time Visualization**: Charts and metrics

## Troubleshooting

### Dashboard won't start
```bash
# Check if port 8501 is already in use
lsof -i :8501

# Kill existing streamlit process if needed
pkill -f streamlit
```

### Sweeps fail
```bash
# Verify cocotb is installed
python3 -c "import cocotb; print(cocotb.__file__)"

# Test CLI sweep first
python3 -c "from sentinel_cloud import SentinelClient; c = SentinelClient(); print(c.quick_check('data/solana_day_1.csv', treasury=1000000, mapper='solana'))"
```

## CLI Alternative

If you prefer command-line:

```bash
# Quick health check
sentinel quick-check data/solana_day_1.csv --treasury 1000000 --mapper solana

# Full analysis
sentinel analyze data/solana_day_1.csv --treasury 1000000 --mapper solana

# See all commands
sentinel --help
```
