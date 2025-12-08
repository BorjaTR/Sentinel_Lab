# Sentinel Cloud - Quick Start

## Running on Your Mac with Docker

### Prerequisites
- Install Docker Desktop: https://www.docker.com/products/docker-desktop/

### Steps

1. **Download the code**
   ```bash
   # Clone or download the repository
   git clone <repo-url>
   cd Sentinel_Lab
   ```

2. **Run with Docker Compose**
   ```bash
   docker-compose up
   ```

3. **Access the dashboard**
   - Open your browser to: http://localhost:8501
   - Click "Run Sweep" - it will work!

### What This Does
- Runs everything in a Linux container
- Installs cocotb, verilator, and all dependencies
- Mounts your data directory so you can use your own CSV files

### Stopping
```bash
docker-compose down
```

---

## Alternative: Use the CLI (No Docker Needed)

If you have the code synced to your Mac and just want quick analysis:

```bash
# Install on Mac
pip install -e .

# Quick check (doesn't require simulations)
python3 -c "
from sentinel_cloud import SentinelClient
from sentinel_cloud.baseline import BaselineAnalyzer
from sentinel_cloud.io import load_and_normalize

# Load data
txs = load_and_normalize('data/solana_day_1.csv', mapper='solana')

# Quick analysis without simulations
analyzer = BaselineAnalyzer()
result = analyzer.compute(txs)

print(f'Total Volume: ${result.total_volume_asset0:,.2f}')
print(f'Total Fees: ${result.total_fees_asset0:,.2f}')
print(f'Transactions: {result.tx_count}')
"
```

---

## For Development

If you want to run sweeps without Docker, you'd need to install:
- verilator (`brew install verilator` on Mac - may have issues)
- cocotb (`pip install cocotb`)

But Docker is the recommended way for Mac users.
