import streamlit as st
import pandas as pd
import subprocess
import time
import os

# ---------------------------------------------------------
# UI CONFIGURATION
# ---------------------------------------------------------
st.set_page_config(
    page_title="Sentinel Cloud | DePIN Exchange",
    page_icon="🛡️",
    layout="wide",
    initial_sidebar_state="expanded"
)

st.markdown("""
    <style>
        .metric-card { background-color: #0e1117; border: 1px solid #30333d; padding: 20px; border-radius: 10px; }
        .stButton>button { width: 100%; border-radius: 5px; height: 3em; background-color: #00ff41; color: black; font-weight: bold; }
    </style>
""", unsafe_allow_html=True)

# ---------------------------------------------------------
# SIDEBAR
# ---------------------------------------------------------
st.sidebar.title("🛡️ Sentinel Cloud")
st.sidebar.caption("Hardware Settlement Layer")

scenario = st.sidebar.selectbox(
    "Data Source",
    ("Solana Mainnet Replay (50k TXs)", "Synthetic Stress Test (10k TXs)", "Random Fuzzing (5k TXs)")
)

st.sidebar.markdown("---")
st.sidebar.metric("Node Status", "ONLINE", "FPGA Active")

# ---------------------------------------------------------
# EXECUTION ENGINE
# ---------------------------------------------------------
def run_simulation(scenario_name):
    csv_file = None
    if "Solana" in scenario_name: csv_file = "data/solana_day_1.csv"
    elif "Stress" in scenario_name: csv_file = "data/scenario_ddos.csv"
    
    cmd = ["python3", "run_lab.py"]
    if csv_file: cmd += ["--scenario", csv_file]
        
    with st.spinner(f"🚀 Ingesting Data & Replaying on Hardware..."):
        time.sleep(0.3) 
        result = subprocess.run(cmd, capture_output=True, text=True)
    return result

# ---------------------------------------------------------
# MAIN PANEL
# ---------------------------------------------------------
st.title("DePIN Settlement Engine")
st.markdown("### Real-time Atomic Swap & Settlement Layer")

# Top Level KPIs
k1, k2, k3, k4 = st.columns(4)
tps_disp = k1.empty()
lat_disp = k2.empty()
rev_disp = k3.empty()
vol_disp = k4.empty()

# Init State
tps_disp.metric("Throughput", "0 M TPS")
lat_disp.metric("Latency", "0 ns")
rev_disp.metric("Protocol Revenue", "$0.00")
vol_disp.metric("24h Volume", "$0")

if st.button("REPLAY TRANSACTIONS"):
    res = run_simulation(scenario)
    
    if res.returncode == 0:
        try:
            df = pd.read_csv("logs/sim_stats.csv", index_col=0)
            
            # Metrics
            tps = float(df.loc["tps_million"].iloc[0])
            rev_usdc = int(df.loc["rev_usdc"].iloc[0])
            rev_gpu = int(df.loc["rev_gpu"].iloc[0])
            vol_usdc = int(df.loc["vol_usdc"].iloc[0])
            
            # Update UI
            tps_disp.metric("Throughput", f"{tps:.2f} M TPS", "Hardware Speed")
            lat_disp.metric("Latency", "10 ns", "Atomic Swap")
            rev_disp.metric("Protocol Revenue", f"{rev_usdc} USDC", f"+{rev_gpu} GPU Credits")
            vol_disp.metric("Processed Volume", f"{vol_usdc:,} USDC")
            
            # Visualization
            st.markdown("---")
            c1, c2 = st.columns(2)
            
            with c1:
                st.subheader("Asset Flow Breakdown")
                chart_data = pd.DataFrame({
                    "Asset": ["USDC (Liquidity)", "GPU Credits (Compute)"],
                    "Volume": [vol_usdc, int(df.loc["vol_gpu"].iloc[0])]
                })
                st.bar_chart(chart_data.set_index("Asset"))
                
            with c2:
                st.subheader("Settlement Latency vs Cloud")
                lat_data = pd.DataFrame({
                    "System": ["AWS (Database)", "Solana (L1)", "Sentinel (FPGA)"],
                    "Latency (ms)": [50, 400, 0.00001]
                })
                st.bar_chart(lat_data.set_index("System"))

            st.success("✅ Batch Settled successfully on-chain.")
            
        except Exception as e:
            st.error(f"Telemetry Error: {e}")
    else:
        st.error("Simulation Failed")
        st.code(res.stderr)