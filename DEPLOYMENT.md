# Deployment Guide: Sentinel Public Rankings

## Quick Deploy to GitHub Pages

### Step 1: Enable GitHub Pages

1. Go to your repository on GitHub
2. Click **Settings** → **Pages** (left sidebar)
3. Under "Build and deployment":
   - **Source**: Deploy from a branch
   - **Branch**: `claude/review-repository-01GoLAkoWjYQ4PPpDLfWuCQR` (or `main` after merge)
   - **Folder**: `/site`
4. Click **Save**

Your rankings will be live at:
```
https://borjatr.github.io/Sentinel_Lab/
```

### Step 2: Verify Deployment

Wait 1-2 minutes, then visit:
```
https://borjatr.github.io/Sentinel_Lab/
```

You should see the rankings table with all 5 protocols.

### Step 3: Update README Link

Once live, update the README link from:
```markdown
📊 **[View Live Protocol Rankings →](https://borjatr.github.io/Sentinel_Lab/)** (Deploy to see)
```

To:
```markdown
📊 **[View Live Protocol Rankings →](https://borjatr.github.io/Sentinel_Lab/)**
```

---

## Updating Rankings

When protocol data changes:

```bash
# 1. Update protocol YAML files
vim protocols/arbitrum.yaml  # Update numbers

# 2. Regenerate rankings
sentinel rankings protocols/ --output html -o site/index.html

# 3. Commit and push
git add site/index.html
git commit -m "Update protocol rankings - $(date +%Y-%m-%d)"
git push

# GitHub Pages will auto-deploy in 1-2 minutes
```

---

## Adding New Protocols

```bash
# 1. Research protocol (see research template)
# 2. Create YAML config
vim protocols/new_protocol.yaml

# 3. Test it
sentinel score protocols/new_protocol.yaml

# 4. Regenerate rankings
sentinel rankings protocols/ --output html -o site/index.html

# 5. Commit and push
git add protocols/new_protocol.yaml site/index.html
git commit -m "Add [Protocol Name] to rankings"
git push
```

---

## Custom Domain (Optional)

If you want a custom domain like `sentinel-protocol.xyz`:

1. Buy domain from Namecheap, Google Domains, etc.

2. Add DNS records:
   ```
   Type: CNAME
   Host: @
   Value: borjatr.github.io
   ```

3. Create `site/CNAME` file:
   ```bash
   echo "sentinel-protocol.xyz" > site/CNAME
   git add site/CNAME
   git commit -m "Add custom domain"
   git push
   ```

4. In GitHub Settings → Pages:
   - Enter custom domain: `sentinel-protocol.xyz`
   - Check "Enforce HTTPS"

---

## Troubleshooting

### Rankings page not loading
- Check Settings → Pages shows "Your site is live at..."
- Verify `/site` folder exists in your branch
- Clear browser cache

### Rankings showing old data
- Verify you regenerated `site/index.html`
- Check git commit includes the updated file
- Wait 2-3 minutes for GitHub Pages deploy

### 404 error
- Verify branch name is correct in Settings
- Verify `/site` folder path is correct
- Check index.html exists in site/ directory

---

## Automation (Future)

To auto-update rankings daily:

### GitHub Actions Workflow

Create `.github/workflows/update-rankings.yml`:

```yaml
name: Update Protocol Rankings

on:
  schedule:
    - cron: '0 0 * * *'  # Daily at midnight UTC
  workflow_dispatch:  # Manual trigger

jobs:
  update:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Setup Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'

      - name: Install Sentinel
        run: pip install -e .

      - name: Update Rankings
        run: |
          sentinel rankings protocols/ --output html -o site/index.html

      - name: Commit Changes
        run: |
          git config user.name "GitHub Actions"
          git config user.email "actions@github.com"
          git add site/index.html
          git diff --quiet && git diff --staged --quiet || git commit -m "Auto-update rankings $(date +%Y-%m-%d)"
          git push
```

This will:
- Run daily
- Regenerate rankings
- Commit if changed
- Auto-deploy to GitHub Pages

---

## Analytics (Optional)

To track page views:

### Google Analytics

Add to `site/index.html` before `</head>`:

```html
<!-- Google Analytics -->
<script async src="https://www.googletagmanager.com/gtag/js?id=G-XXXXXXXXXX"></script>
<script>
  window.dataLayer = window.dataLayer || [];
  function gtag(){dataLayer.push(arguments);}
  gtag('js', new Date());
  gtag('config', 'G-XXXXXXXXXX');
</script>
```

### Plausible (Privacy-friendly alternative)

```html
<script defer data-domain="yourdomain.com" src="https://plausible.io/js/script.js"></script>
```

---

## SEO Optimization

To improve search ranking:

### Add Meta Tags

Update `site/index.html` `<head>`:

```html
<meta name="description" content="Sentinel Protocol Rankings - Sustainability scores for crypto protocols. Compare DAOs, L2s, and DeFi by financial health.">
<meta name="keywords" content="DAO, protocol sustainability, crypto treasury, Arbitrum, Optimism, Uniswap, Aave, Lido">

<!-- Open Graph for social sharing -->
<meta property="og:title" content="Sentinel Protocol Rankings">
<meta property="og:description" content="0% of major protocols are in healthy financial condition. See the rankings.">
<meta property="og:url" content="https://borjatr.github.io/Sentinel_Lab/">
<meta property="og:type" content="website">

<!-- Twitter Card -->
<meta name="twitter:card" content="summary_large_image">
<meta name="twitter:title" content="Sentinel Protocol Rankings">
<meta name="twitter:description" content="Protocol sustainability scores for crypto">
```

### Sitemap

Create `site/sitemap.xml`:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
  <url>
    <loc>https://borjatr.github.io/Sentinel_Lab/</loc>
    <lastmod>2024-12-08</lastmod>
    <changefreq>daily</changefreq>
    <priority>1.0</priority>
  </url>
</urlset>
```

---

## Next Steps

After deployment:

1. ✅ Verify rankings page loads
2. ✅ Share link in Twitter thread
3. ✅ Submit to relevant aggregators:
   - DefiLlama Discord
   - DAO Research Collective
   - Governance forums
4. Monitor traffic and engagement
5. Respond to feedback
6. Add more protocols based on requests

---

## Support

If you need help:
- GitHub Issues: https://github.com/BorjaTR/Sentinel_Lab/issues
- Twitter: @YourHandle

---

## Current Status

- [x] 5 real protocols configured
- [x] Rankings HTML generated
- [x] Site ready for deployment
- [ ] GitHub Pages enabled (do this now!)
- [ ] Twitter announcement posted
- [ ] Analytics added
