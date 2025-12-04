"""
Sentinel Cloud Dashboard v3 - Tokenomics Lab UI

Interactive dashboard for comparing fee configurations and launching experiments.

Usage:
    streamlit run dashboard_v3.py
"""

import streamlit as st
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
from pathlib import Path
from typing import List, Optional

from sentinel_cloud import SentinelClient
from sentinel_cloud.dashboard_io import (
    list_experiments,
    load_experiment,
    get_experiment_metadata,
    save_experiment
)
from sentinel_cloud.experiment import ExperimentResult, RunResult
from sentinel_cloud.mappers import MAPPERS

# =========================================================================
# PAGE CONFIG
# =========================================================================

st.set_page_config(
    page_title="Sentinel Cloud | Tokenomics Lab",
    page_icon="🛡️",
    layout="wide",
    initial_sidebar_state="expanded"
)

# =========================================================================
# SIDEBAR
# =========================================================================

st.sidebar.title("🛡️ Sentinel Cloud")
st.sidebar.markdown("### Tokenomics Lab")

# Mode selector
mode = st.sidebar.radio(
    "View Mode",
    ["📈 Single Run Analysis", "💰 Compare Experiments"],
    index=1
)

st.sidebar.markdown("---")

# Experiment selection
st.sidebar.subheader("📂 Load Experiments")

experiments_dir = st.sidebar.text_input(
    "Experiments Directory",
    value="experiments",
    help="Directory containing experiment JSON files"
)

# List available experiments
available_experiments = list_experiments(experiments_dir)

if not available_experiments:
    st.sidebar.warning(f"No experiments found in `{experiments_dir}/`")
    st.sidebar.info("Run a sweep to generate experiments, or use the launcher below.")
    selected_experiments = []
else:
    # Get metadata for all experiments
    experiment_metadata = [get_experiment_metadata(exp) for exp in available_experiments]

    # Create selection UI
    if mode == "📈 Single Run Analysis":
        # Single select for single run mode
        selected_name = st.sidebar.selectbox(
            "Select Experiment",
            options=[meta['display_name'] for meta in experiment_metadata],
            help="Choose one experiment to analyze"
        )
        selected_experiments = [available_experiments[
            [m['display_name'] for m in experiment_metadata].index(selected_name)
        ]]
    else:
        # Multi-select for comparison mode
        selected_names = st.sidebar.multiselect(
            "Select Experiments to Compare",
            options=[meta['display_name'] for meta in experiment_metadata],
            default=[experiment_metadata[0]['display_name']] if experiment_metadata else [],
            help="Choose one or more experiments to compare"
        )
        selected_experiments = [
            available_experiments[[m['display_name'] for m in experiment_metadata].index(name)]
            for name in selected_names
        ]

st.sidebar.markdown("---")

# Sweep launcher
st.sidebar.subheader("🧪 Run New Sweep")

with st.sidebar.form("sweep_launcher"):
    scenario = st.text_input(
        "Scenario CSV",
        value="data/solana_day_1.csv",
        help="Path to transaction CSV file"
    )

    mapper = st.selectbox(
        "Protocol Mapper",
        options=sorted(MAPPERS.keys()),
        index=sorted(MAPPERS.keys()).index("solana") if "solana" in MAPPERS else 0
    )

    col1, col2, col3 = st.columns(3)
    with col1:
        fee_min = st.number_input("Min (bps)", 0, 5000, 0, step=25)
    with col2:
        fee_max = st.number_input("Max (bps)", 0, 5000, 200, step=25)
    with col3:
        fee_step = st.number_input("Step (bps)", 1, 1000, 25, step=25)

    submit = st.form_submit_button("▶️ Run Sweep", use_container_width=True)

    if submit:
        # Validate inputs
        if not Path(scenario).exists():
            st.error(f"❌ Scenario file not found: {scenario}")
        elif fee_min > fee_max:
            st.error(f"❌ Min fee ({fee_min}) > Max fee ({fee_max})")
        elif fee_step <= 0:
            st.error(f"❌ Step must be positive")
        else:
            # Run sweep
            client = SentinelClient(verbose=False)

            with st.spinner(f"🚀 Running sweep ({fee_min}-{fee_max} bps)..."):
                try:
                    sweep = client.sweep(
                        scenario=scenario,
                        fee_range=(fee_min, fee_max, fee_step),
                        mapper=mapper
                    )

                    # Save experiment
                    saved_path = save_experiment(sweep._experiment_result, experiments_dir)

                    st.success(f"✅ Sweep complete!")
                    st.info(f"💾 Saved to: `{saved_path.name}`")
                    st.rerun()

                except Exception as e:
                    st.error(f"❌ Sweep failed: {e}")

# =========================================================================
# MAIN PANEL
# =========================================================================

st.title("🛡️ Sentinel Cloud - Tokenomics Lab")
st.markdown("### Hardware-Accelerated Fee Analysis")

# Load selected experiments
if not selected_experiments:
    st.info("👈 Select an experiment from the sidebar to get started")
    st.markdown("""
    **Getting Started:**
    1. Use the **Run New Sweep** form in the sidebar to launch an experiment
    2. Or select an existing experiment from the **Load Experiments** section
    3. Compare multiple configurations to find optimal fees
    """)
    st.stop()

# Load experiment data
experiments = []
for exp_path in selected_experiments:
    exp = load_experiment(str(exp_path))
    if exp is not None:
        experiments.append(exp)

if not experiments:
    st.error("Failed to load experiments")
    st.stop()

# Display summary
primary_exp = experiments[0]
total_runs = sum(len(exp.runs) for exp in experiments)
total_tx = sum(
    int(run.get_metric('num_tx', 0))
    for exp in experiments
    for run in exp.runs
    if run.success
)

# Calculate average TPS
successful_runs = [run for exp in experiments for run in exp.runs if run.success]
if successful_runs:
    avg_engine_tps = sum(run.get_metric('engine_tps', 0) for run in successful_runs) / len(successful_runs)
    avg_lab_tps = sum(run.get_metric('lab_tps', 0) for run in successful_runs) / len(successful_runs)
else:
    avg_engine_tps = 0
    avg_lab_tps = 0

# Summary strip
col1, col2, col3, col4 = st.columns(4)
with col1:
    st.metric("Scenario", Path(primary_exp.scenario_path).stem)
with col2:
    st.metric("Mapper", primary_exp.mapper.upper())
with col3:
    st.metric("Configs Loaded", total_runs)
with col4:
    st.metric("Total TX", f"{total_tx:,}")

col1, col2 = st.columns(2)
with col1:
    st.metric(
        "Engine TPS",
        f"{avg_engine_tps/1e6:.2f}M",
        help="Core RTL @ 100MHz, 1 tx/cycle, no I/O/consensus"
    )
with col2:
    st.metric(
        "Lab TPS",
        f"{avg_lab_tps:,.0f}",
        help="End-to-end including Python, Verilator, CSV I/O"
    )

st.markdown("---")

# =========================================================================
# TABS
# =========================================================================

if mode == "📈 Single Run Analysis":
    # Single run mode - show detailed analysis of one config
    tab1 = st.tabs(["📊 Analysis"])[0]

    with tab1:
        # Config selector
        all_runs = [run for exp in experiments for run in exp.runs if run.success]

        if not all_runs:
            st.error("No successful runs to analyze")
            st.stop()

        run_names = [f"{run.config.name} ({run.config.fee_bps_asset0} bps)" for run in all_runs]
        selected_run_name = st.selectbox("Select Configuration", run_names)
        selected_run = all_runs[run_names.index(selected_run_name)]

        # Display run details
        col1, col2, col3 = st.columns(3)
        with col1:
            st.metric("Fee", f"{selected_run.config.fee_bps_asset0} bps ({selected_run.config.fee_bps_asset0/100:.2f}%)")
        with col2:
            st.metric("Revenue", f"${selected_run.get_metric('rev_usdc', 0):,.0f}")
        with col3:
            st.metric("Volume", f"${selected_run.get_metric('vol_usdc', 0):,.0f}")

        col1, col2, col3 = st.columns(3)
        with col1:
            st.metric("Engine TPS", f"{selected_run.get_metric('engine_tps', 0)/1e6:.2f}M")
        with col2:
            st.metric("Lab TPS", f"{selected_run.get_metric('lab_tps', 0):,.0f}")
        with col3:
            st.metric("Wall Time", f"{selected_run.wall_time_seconds:.1f}s")

        # Note: Time series data not yet implemented
        st.info("ℹ️  Time series charts coming in next update")

else:
    # Comparison mode - show multiple configs
    tab1, tab2, tab3, tab4 = st.tabs([
        "💰 Fee vs Revenue",
        "⚖️ Fee vs Risk",
        "📊 Config Overlay",
        "📋 Data Table"
    ])

    # Collect all successful runs
    all_runs = [run for exp in experiments for run in exp.runs if run.success]

    if not all_runs:
        st.error("No successful runs to compare")
        st.stop()

    # ===== TAB 1: Fee vs Revenue =====
    with tab1:
        st.subheader("💰 Fee vs Revenue Analysis")

        # Create dataframe
        df = pd.DataFrame([
            {
                'config': run.config.name,
                'fee_bps': run.config.fee_bps_asset0,
                'revenue_usdc': run.get_metric('rev_usdc', 0),
                'volume_usdc': run.get_metric('vol_usdc', 0),
                'lab_tps': run.get_metric('lab_tps', 0),
                'failure_rate': run.get_metric('failure_rate', 0) * 100,  # Convert to percentage
            }
            for run in all_runs
        ])

        # Revenue vs Fee scatter
        fig = px.scatter(
            df,
            x='fee_bps',
            y='revenue_usdc',
            size='volume_usdc',
            color='failure_rate',
            hover_data=['config', 'lab_tps'],
            title='Revenue vs Fee (bubble size = volume)',
            labels={
                'fee_bps': 'Fee (basis points)',
                'revenue_usdc': 'Revenue (USDC)',
                'failure_rate': 'Failure Rate (%)'
            },
            color_continuous_scale='RdYlGn_r'
        )
        st.plotly_chart(fig, use_container_width=True)

        # Line plot
        df_sorted = df.sort_values('fee_bps')
        fig = px.line(
            df_sorted,
            x='fee_bps',
            y='revenue_usdc',
            markers=True,
            title='Revenue Growth by Fee',
            labels={'fee_bps': 'Fee (basis points)', 'revenue_usdc': 'Revenue (USDC)'}
        )
        st.plotly_chart(fig, use_container_width=True)

        # Insights box
        st.markdown("### 💡 Insights")

        optimal_idx = df['revenue_usdc'].idxmax()
        optimal = df.loc[optimal_idx]

        st.info(f"""
        **Optimal Configuration:** {optimal['config']}
        - **Fee:** {optimal['fee_bps']} bps ({optimal['fee_bps']/100:.2f}%)
        - **Revenue:** ${optimal['revenue_usdc']:,.0f}
        - **Volume:** ${optimal['volume_usdc']:,.0f}
        - **Failure Rate:** {optimal['failure_rate']:.3f}%
        """)

    # ===== TAB 2: Fee vs Risk =====
    with tab2:
        st.subheader("⚖️ Fee vs Risk Analysis")

        col1, col2 = st.columns(2)

        with col1:
            # Failure rate plot
            fig = px.scatter(
                df,
                x='fee_bps',
                y='failure_rate',
                size='volume_usdc',
                hover_data=['config'],
                title='Failure Rate vs Fee',
                labels={'fee_bps': 'Fee (bps)', 'failure_rate': 'Failure Rate (%)'}
            )
            fig.add_hline(y=1.0, line_dash="dash", line_color="red",
                         annotation_text="1% threshold")
            st.plotly_chart(fig, use_container_width=True)

        with col2:
            # TPS vs Fee
            fig = px.scatter(
                df,
                x='fee_bps',
                y='lab_tps',
                size='revenue_usdc',
                hover_data=['config'],
                title='Lab TPS vs Fee',
                labels={'fee_bps': 'Fee (bps)', 'lab_tps': 'Lab TPS'}
            )
            st.plotly_chart(fig, use_container_width=True)

        # Risk assessment
        st.markdown("### 🎯 Risk Assessment")

        high_failure = df[df['failure_rate'] > 1.0]
        if not high_failure.empty:
            st.warning(f"⚠️  {len(high_failure)} configuration(s) have >1% failure rate:")
            for _, row in high_failure.iterrows():
                st.text(f"  - {row['config']}: {row['failure_rate']:.2f}%")
        else:
            st.success("✅ All configurations have <1% failure rate")

    # ===== TAB 3: Config Overlay =====
    with tab3:
        st.subheader("📊 Configuration Overlay")

        # Multi-select for configs to overlay
        config_names = [f"{run.config.name} ({run.config.fee_bps_asset0} bps)" for run in all_runs]
        selected_configs = st.multiselect(
            "Select Configurations to Overlay",
            options=config_names,
            default=config_names[:min(3, len(config_names))],
            help="Choose up to 5 configurations to compare"
        )

        if not selected_configs:
            st.info("Select at least one configuration to see overlays")
        else:
            selected_runs = [all_runs[config_names.index(name)] for name in selected_configs]

            # Note: Time series overlays not yet implemented
            st.info("ℹ️  Time series overlays coming in next update. Currently showing aggregate metrics only.")

    # ===== TAB 4: Data Table =====
    with tab4:
        st.subheader("📋 Configuration Data Table")

        # Show full data table
        display_df = df.copy()
        display_df['revenue_usdc'] = display_df['revenue_usdc'].apply(lambda x: f"${x:,.0f}")
        display_df['volume_usdc'] = display_df['volume_usdc'].apply(lambda x: f"${x:,.0f}")
        display_df['lab_tps'] = display_df['lab_tps'].apply(lambda x: f"{x:,.0f}")
        display_df['failure_rate'] = display_df['failure_rate'].apply(lambda x: f"{x:.3f}%")

        st.dataframe(
            display_df,
            use_container_width=True,
            hide_index=True
        )

        # Download button
        csv = df.to_csv(index=False)
        st.download_button(
            label="📥 Download CSV",
            data=csv,
            file_name="fee_comparison.csv",
            mime="text/csv"
        )
