# Sentinel Protocol Rankings

This directory contains the public rankings page for Sentinel.

## Deployment to GitHub Pages

### Option 1: Deploy from `site/` directory

1. Go to repository Settings → Pages
2. Source: "Deploy from a branch"
3. Branch: `main` (or your branch)
4. Folder: `/site`
5. Save

Your rankings will be live at: `https://yourusername.github.io/Sentinel_Lab/`

### Option 2: Deploy from `docs/` directory

If you prefer the standard `/docs` folder:

```bash
# Move site contents to docs
mkdir -p docs
cp site/index.html docs/
```

Then:
1. Settings → Pages
2. Folder: `/docs`
3. Save

### Updating Rankings

To update with latest protocol data:

```bash
# Score protocols
sentinel score protocols/arbitrum.yaml
sentinel score protocols/optimism.yaml
# ... etc

# Regenerate rankings
sentinel rankings protocols/ --output html -o site/index.html

# Commit and push
git add site/index.html
git commit -m "Update protocol rankings"
git push
```

## Current Rankings

Last updated: 2024-12-08

| Rank | Protocol | Score | Grade | Status |
|------|----------|-------|-------|--------|
| 1 | Aave | 63/100 | C | Warning |
| 2 | Lido | 59/100 | C | Warning |
| 3 | Arbitrum DAO | 47/100 | D | Warning |
| 4 | Uniswap | 45/100 | D | Warning |
| 5 | Optimism | 31/100 | F | Critical |

## Findings

- **0% of protocols** are in "Healthy" status
- **80% are in "Warning"** status
- **20% are "Critical"** (Optimism: 17 months runway)
- **Average score: 49/100** (failing grade)
- **Total treasury: $6.3B** across 5 protocols

## Key Insights

1. **Optimism** - Most at risk with 17-month runway, spending $18.5M/mo on RPGF
2. **Uniswap** - Largest treasury ($4.4B) but ZERO revenue (fee switch off)
3. **Arbitrum** - 88-month runway but spending $8M/mo on incentives
4. **Aave** - Healthiest, but $4M/mo buyback program creates deficit
5. **Lido** - Nearly break-even, $2.95M revenue vs $3.9M costs
