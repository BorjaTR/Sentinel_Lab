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
        # Auto-select newest experiment (experiment_metadata is already sorted by time, newest first)
        default_selection = [experiment_metadata[0]['display_name']] if experiment_metadata else []

        selected_names = st.sidebar.multiselect(
            "Select Experiments to Compare",
            options=[meta['display_name'] for meta in experiment_metadata],
            default=default_selection,
            help="Choose one or more experiments to compare",
            key="experiment_selector"  # Add key for state management
        )

        # If no selection, default to newest
        if not selected_names and experiment_metadata:
            selected_names = [experiment_metadata[0]['display_name']]

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

                    # Clear experiment selector to force reload of newest experiment
                    if 'experiment_selector' in st.session_state:
                        del st.session_state['experiment_selector']

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

        # Time series charts
        st.subheader("Time Series Analysis")

        if selected_run.time_series and len(selected_run.time_series) > 0:
            import pandas as pd
            ts_df = pd.DataFrame(selected_run.time_series)

            col1, col2 = st.columns(2)

            with col1:
                # Revenue accumulation
                fig = px.line(
                    ts_df,
                    x='tx_count',
                    y='vault_usdc',
                    title='Revenue Accumulation Over Time',
                    labels={'tx_count': 'Transaction Count', 'vault_usdc': 'Revenue (USDC)'}
                )
                st.plotly_chart(fig, use_container_width=True)

            with col2:
                # Success rate
                fig = px.line(
                    ts_df,
                    x='tx_count',
                    y='success_rate',
                    title='Success Rate Over Time (%)',
                    labels={'tx_count': 'Transaction Count', 'success_rate': 'Success Rate (%)'}
                )
                fig.update_yaxes(range=[0, 100])
                st.plotly_chart(fig, use_container_width=True)
        else:
            st.info("ℹ️  No time series data available for this run (run a new sweep to generate)")

else:
    # Comparison mode - show multiple configs
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "💰 Fee vs Revenue",
        "⚖️ Fee vs Risk",
        "📊 Config Overlay",
        "📋 Data Table",
        "👥 Role Economics"
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

            # Check if any selected runs have time series data
            has_time_series = any(run.time_series and len(run.time_series) > 0 for run in selected_runs)

            if has_time_series:
                # Revenue accumulation overlay
                fig = go.Figure()
                for run in selected_runs:
                    if run.time_series and len(run.time_series) > 0:
                        ts_df = pd.DataFrame(run.time_series)
                        fig.add_trace(go.Scatter(
                            x=ts_df['tx_count'],
                            y=ts_df['vault_usdc'],
                            mode='lines',
                            name=f"{run.config.name} ({run.config.fee_bps_asset0} bps)"
                        ))

                fig.update_layout(
                    title='Revenue Accumulation Overlay',
                    xaxis_title='Transaction Count',
                    yaxis_title='Revenue (USDC)',
                    hovermode='x unified'
                )
                st.plotly_chart(fig, use_container_width=True)

                # Success rate overlay
                fig = go.Figure()
                for run in selected_runs:
                    if run.time_series and len(run.time_series) > 0:
                        ts_df = pd.DataFrame(run.time_series)
                        fig.add_trace(go.Scatter(
                            x=ts_df['tx_count'],
                            y=ts_df['success_rate'],
                            mode='lines',
                            name=f"{run.config.name} ({run.config.fee_bps_asset0} bps)"
                        ))

                fig.update_layout(
                    title='Success Rate Overlay',
                    xaxis_title='Transaction Count',
                    yaxis_title='Success Rate (%)',
                    hovermode='x unified'
                )
                fig.update_yaxes(range=[0, 100])
                st.plotly_chart(fig, use_container_width=True)
            else:
                st.info("ℹ️  No time series data available. Run a new sweep to generate time series charts.")

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

    # ===== TAB 5: Role Economics =====
    with tab5:
        st.subheader("👥 Role-Based Economics & Sustainability")

        # Check if any runs have role metrics
        runs_with_roles = [run for run in all_runs if run.role_metrics]

        if not runs_with_roles:
            st.info("""
            ℹ️  Role economics data not available for these experiments.

            **To enable role tracking:**
            1. Ensure your scenario CSV includes `role_a` and `role_b` columns
            2. Run a new sweep to generate role-aware metrics
            3. Valid roles: client, miner, validator, treasury, lp, storage_provider, sequencer, hotspot
            """)
        else:
            # Config selector for role analysis
            run_names = [f"{run.config.name} ({run.config.fee_bps_asset0} bps)" for run in runs_with_roles]
            selected_run_name = st.selectbox(
                "Select Configuration for Role Analysis",
                run_names,
                key="role_config_selector"
            )
            selected_run = runs_with_roles[run_names.index(selected_run_name)]

            # Display role metrics
            st.markdown("### 📊 Role Breakdown")

            if selected_run.role_metrics:
                # Create role metrics dataframe
                role_data = []
                for role, metrics in selected_run.role_metrics.items():
                    role_data.append({
                        'Role': role.capitalize(),
                        'Transactions': metrics['tx_count'],
                        'Revenue': metrics['revenue_earned'],
                        'Fees Paid': metrics['fees_paid'],
                        'Net': metrics['net_revenue'],
                        'Volume': metrics['volume_usdc'],
                        'Avg TX Size': metrics['avg_tx_size']
                    })

                role_df = pd.DataFrame(role_data)
                role_df = role_df.sort_values('Revenue', ascending=False)

                # Display metrics in columns
                col1, col2 = st.columns(2)

                with col1:
                    # Revenue by role
                    fig = px.bar(
                        role_df,
                        x='Role',
                        y='Revenue',
                        title='Revenue Earned by Role',
                        labels={'Revenue': 'Revenue (USDC)', 'Role': 'Participant Role'},
                        color='Revenue',
                        color_continuous_scale='Viridis'
                    )
                    st.plotly_chart(fig, use_container_width=True)

                with col2:
                    # Net revenue by role
                    fig = px.bar(
                        role_df,
                        x='Role',
                        y='Net',
                        title='Net Revenue by Role (Revenue - Fees)',
                        labels={'Net': 'Net Revenue (USDC)', 'Role': 'Participant Role'},
                        color='Net',
                        color_continuous_scale='RdYlGn'
                    )
                    fig.add_hline(y=0, line_dash="dash", line_color="gray", annotation_text="Break-even")
                    st.plotly_chart(fig, use_container_width=True)

                # Transaction volume by role
                fig = px.pie(
                    role_df,
                    values='Volume',
                    names='Role',
                    title='Transaction Volume Distribution by Role',
                    hole=0.4
                )
                st.plotly_chart(fig, use_container_width=True)

                # Role metrics table
                st.markdown("### 📋 Detailed Role Metrics")

                display_role_df = role_df.copy()
                display_role_df['Revenue'] = display_role_df['Revenue'].apply(lambda x: f"${x:,.0f}")
                display_role_df['Fees Paid'] = display_role_df['Fees Paid'].apply(lambda x: f"${x:,.0f}")
                display_role_df['Net'] = display_role_df['Net'].apply(lambda x: f"${x:+,.0f}")
                display_role_df['Volume'] = display_role_df['Volume'].apply(lambda x: f"${x:,.0f}")
                display_role_df['Avg TX Size'] = display_role_df['Avg TX Size'].apply(lambda x: f"${x:,.0f}")

                st.dataframe(display_role_df, use_container_width=True, hide_index=True)

                # Economic imbalance warnings
                st.markdown("### ⚠️  Economic Health Checks")

                warnings = []

                # Check for roles paying more than earning
                for _, row in role_df.iterrows():
                    if row['Net'] < 0:
                        warnings.append(f"🔴 **{row['Role']}s** are paying more than earning (Net: ${row['Net']:,.0f})")

                # Check for extreme concentration
                if len(role_df) > 1:
                    total_volume = role_df['Volume'].sum()
                    for _, row in role_df.iterrows():
                        if total_volume > 0:
                            share = row['Volume'] / total_volume
                            if share > 0.8:
                                warnings.append(
                                    f"🟡 **{row['Role']}s** dominate {share*100:.1f}% of volume "
                                    f"(centralization risk)"
                                )

                if warnings:
                    for warning in warnings:
                        st.warning(warning)
                else:
                    st.success("✅ No economic imbalances detected")

            # Treasury sustainability
            st.markdown("---")
            st.markdown("### 🏛️ Treasury Sustainability")

            if selected_run.treasury_state:
                treasury = selected_run.treasury_state

                # Treasury metrics
                col1, col2, col3, col4 = st.columns(4)

                with col1:
                    st.metric(
                        "Treasury Balance",
                        f"${treasury['balance_usdc']:,.0f}",
                        help="Current treasury balance in USDC"
                    )

                with col2:
                    st.metric(
                        "Revenue/Day",
                        f"${treasury['revenue_rate_per_day']:,.0f}",
                        help="Daily fee collection rate"
                    )

                with col3:
                    st.metric(
                        "Burn/Day",
                        f"${treasury['burn_rate_per_day']:,.0f}",
                        help="Daily emission/reward payout rate"
                    )

                with col4:
                    if treasury['runway_days'] is None:
                        runway_display = "♾️ Sustainable"
                        delta_color = "normal"
                    else:
                        runway_display = f"{treasury['runway_days']:.0f} days"
                        delta_color = "inverse" if treasury['runway_days'] < 90 else "normal"

                    st.metric(
                        "Runway",
                        runway_display,
                        delta=treasury['depletion_risk'],
                        delta_color=delta_color,
                        help="Days until treasury depletion (if unsustainable)"
                    )

                # Sustainability visualization
                col1, col2 = st.columns(2)

                with col1:
                    # Revenue vs burn comparison
                    comparison_df = pd.DataFrame({
                        'Type': ['Fee Revenue', 'Emissions Burn'],
                        'Amount': [
                            treasury['revenue_rate_per_day'],
                            treasury['burn_rate_per_day']
                        ]
                    })

                    fig = px.bar(
                        comparison_df,
                        x='Type',
                        y='Amount',
                        title='Daily Treasury Inflow vs Outflow',
                        labels={'Amount': 'USDC per Day'},
                        color='Type',
                        color_discrete_map={
                            'Fee Revenue': '#00CC96',
                            'Emissions Burn': '#EF553B'
                        }
                    )
                    st.plotly_chart(fig, use_container_width=True)

                with col2:
                    # Treasury balance projection
                    if treasury['runway_days'] and treasury['runway_days'] != float('inf'):
                        days = min(int(treasury['runway_days']) + 30, 365)
                    else:
                        days = 365

                    net_rate = treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']
                    projection = [treasury['balance_usdc'] + (net_rate * d) for d in range(days)]

                    proj_df = pd.DataFrame({
                        'Day': list(range(days)),
                        'Balance': projection
                    })

                    fig = px.line(
                        proj_df,
                        x='Day',
                        y='Balance',
                        title='Treasury Balance Projection',
                        labels={'Balance': 'Balance (USDC)', 'Day': 'Days from Now'}
                    )
                    fig.add_hline(y=0, line_dash="dash", line_color="red", annotation_text="Depletion")
                    st.plotly_chart(fig, use_container_width=True)

                # Treasury warnings
                st.markdown("### 💡 Sustainability Recommendations")

                if treasury['is_sustainable']:
                    st.success(f"""
                    ✅ **Treasury is sustainable**
                    - Fee revenue ({treasury['revenue_rate_per_day']:,.0f} USDC/day) exceeds emissions
                      ({treasury['burn_rate_per_day']:,.0f} USDC/day)
                    - Net accumulation: ${treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']:+,.0f}/day
                    """)
                else:
                    risk_level = treasury['depletion_risk']

                    if '💀' in risk_level:
                        st.error(f"""
                        💀 **CRITICAL: Treasury depletes in {treasury['runway_days']:.0f} days**
                        - Immediate action required
                        - Consider: Increase fees, reduce emissions, or inject capital
                        """)
                    elif '🔴' in risk_level:
                        st.error(f"""
                        🔴 **HIGH RISK: Treasury depletes in {treasury['runway_days']:.0f} days**
                        - Burn rate ({treasury['burn_rate_per_day']:,.0f} USDC/day) exceeds revenue
                          ({treasury['revenue_rate_per_day']:,.0f} USDC/day)
                        - Net drain: ${treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']:+,.0f}/day
                        - Recommend: Adjust tokenomics soon
                        """)
                    elif '🟠' in risk_level:
                        st.warning(f"""
                        🟠 **MEDIUM RISK: Treasury depletes in {treasury['runway_days']:.0f} days**
                        - Monitor closely and plan adjustments
                        - Net drain: ${treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']:+,.0f}/day
                        """)
                    else:
                        st.warning(f"""
                        🟡 **LOW RISK: Treasury depletes in {treasury['runway_days']:.0f} days**
                        - Current trajectory is unsustainable long-term
                        - Net drain: ${treasury['revenue_rate_per_day'] - treasury['burn_rate_per_day']:+,.0f}/day
                        """)
            else:
                st.info("ℹ️  Treasury state not available for this configuration")

