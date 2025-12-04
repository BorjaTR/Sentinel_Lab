`timescale 1ns/1ps

module ledger_core #(
    parameter int USER_WIDTH = 10,
    parameter int BALANCE_WIDTH = 64
)(
    input  logic clk,
    input  logic rst_n,

    // ---------------------------------------------------------
    // Config Interface - Programmable Tokenomics
    // ---------------------------------------------------------
    // Fee configuration in basis points (0-10000)
    // 0 = 0% fee, 50 = 0.50% fee, 100 = 1.00% fee, 10000 = 100% fee
    input  logic [15:0] s_fee_bps_asset0,  // USDC/money token fee
    input  logic [15:0] s_fee_bps_asset1,  // GPU/resource credit fee

    // NOTE: Fee Calculation Synthesis Considerations
    // Current implementation: fee = (amount * fee_bps) / 10000
    // - Uses integer division (synthesis-heavy on FPGA)
    // - Consumes DSP slices or significant LUT resources
    //
    // Production FPGA Optimizations:
    // 1. Pre-compute lookup table for common fee_bps values
    // 2. Use bit-shift approximations for powers-of-2 fees
    // 3. Implement fixed-point arithmetic (Q16.16 format)
    // 4. Replace divider with multiplier + right-shift
    //
    // This Verilator-friendly version prioritizes correctness
    // and bit-exact matching with Python golden model.

    // Transaction Interface
    input  logic        s_valid,
    input  logic        s_opcode,
    input  logic [USER_WIDTH-1:0] s_user_a,
    input  logic [USER_WIDTH-1:0] s_user_b,
    input  logic [BALANCE_WIDTH-1:0] s_amount_0,
    input  logic [BALANCE_WIDTH-1:0] s_amount_1,

    // Response
    output logic        m_valid,
    output logic        m_success,
    output logic [USER_WIDTH-1:0] m_user_a,
    output logic [USER_WIDTH-1:0] m_user_b,
    output logic [BALANCE_WIDTH-1:0] m_bal_a_0, m_bal_a_1,
    output logic [BALANCE_WIDTH-1:0] m_bal_b_0, m_bal_b_1,
    output logic [BALANCE_WIDTH-1:0] m_vault_usdc,
    output logic [BALANCE_WIDTH-1:0] m_vault_gpu
);

    // ---------------------------------------------------------
    // State Memory
    // ---------------------------------------------------------
    logic [2*BALANCE_WIDTH-1:0] portfolios [0:(1<<USER_WIDTH)-1];
    logic [BALANCE_WIDTH-1:0] vault_usdc;
    logic [BALANCE_WIDTH-1:0] vault_gpu;

    initial begin
        for (int i = 0; i < (1<<USER_WIDTH); i++) begin
            portfolios[i] = {64'd1000000, 64'd1000000};
        end
    end

    // ---------------------------------------------------------
    // Stage 1: READ
    // ---------------------------------------------------------
    logic p1_valid, p1_opcode;
    logic [USER_WIDTH-1:0] p1_user_a, p1_user_b;
    logic [BALANCE_WIDTH-1:0] p1_amt_0, p1_amt_1;
    logic [2*BALANCE_WIDTH-1:0] p1_data_a, p1_data_b;
    logic [15:0] p1_fee_bps_asset0, p1_fee_bps_asset1;  // Pipeline fee config

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            p1_valid <= 1'b0; p1_user_a <= '0; p1_user_b <= '0;
            p1_amt_0 <= '0; p1_amt_1 <= '0; p1_opcode <= '0;
            p1_data_a <= '0; p1_data_b <= '0;
            p1_fee_bps_asset0 <= '0; p1_fee_bps_asset1 <= '0;
        end else begin
            if (s_valid) begin
                p1_data_a <= portfolios[s_user_a];
                p1_data_b <= portfolios[s_user_b];
                p1_user_a <= s_user_a; p1_user_b <= s_user_b;
                p1_amt_0  <= s_amount_0; p1_amt_1  <= s_amount_1;
                p1_opcode <= s_opcode;   p1_valid  <= 1'b1;
                p1_fee_bps_asset0 <= s_fee_bps_asset0;
                p1_fee_bps_asset1 <= s_fee_bps_asset1;
            end else begin
                p1_valid <= 1'b0;
            end
        end
    end

    // ---------------------------------------------------------
    // Stage 2: EXECUTE
    // ---------------------------------------------------------
    logic [2*BALANCE_WIDTH-1:0] new_state_a, new_state_b;
    logic stage2_success, write_en;
    logic [BALANCE_WIDTH-1:0] eff_a_0, eff_a_1, eff_b_0, eff_b_1;
    logic [2*BALANCE_WIDTH-1:0] raw_fwd_a, raw_fwd_b;
    logic [BALANCE_WIDTH-1:0] fee_0, fee_1;

    always_comb begin
        // ---------------------------------------------------------
        // Forwarding Logic (RAW hazard mitigation)
        // ---------------------------------------------------------
        raw_fwd_a = p1_data_a;
        raw_fwd_b = p1_data_b;

        if (m_valid && m_success && (m_user_a == p1_user_a))
            raw_fwd_a = {m_bal_a_1, m_bal_a_0};
        else if (m_valid && m_success && (m_user_b == p1_user_a))
            raw_fwd_a = {m_bal_b_1, m_bal_b_0};

        if (m_valid && m_success && (m_user_a == p1_user_b))
            raw_fwd_b = {m_bal_a_1, m_bal_a_0};
        else if (m_valid && m_success && (m_user_b == p1_user_b))
            raw_fwd_b = {m_bal_b_1, m_bal_b_0};

        {eff_a_1, eff_a_0} = raw_fwd_a;
        {eff_b_1, eff_b_0} = raw_fwd_b;

        // ---------------------------------------------------------
        // Dynamic Fee Calculation
        // ---------------------------------------------------------
        // Formula: fee = (amount * fee_bps) / 10000
        // Example: amount=1000, fee_bps=50 → fee = 50000/10000 = 5 (0.50%)
        //
        // Integer division semantics (matches Python //):
        // - Truncates towards zero
        // - No rounding (12345 * 75 / 10000 = 925687 / 10000 = 92)
        fee_0 = (p1_amt_0 * p1_fee_bps_asset0) / 10000;
        fee_1 = (p1_amt_1 * p1_fee_bps_asset1) / 10000;

        // ---------------------------------------------------------
        // Transaction Execution Logic
        // ---------------------------------------------------------
        stage2_success = 1'b0;
        write_en = 1'b0;
        new_state_a = raw_fwd_a;
        new_state_b = raw_fwd_b;

        if (p1_valid) begin
            // Self-transaction (no-op)
            if (p1_user_a == p1_user_b) begin
                stage2_success = 1'b1;
            end else begin
                case (p1_opcode)
                    // Opcode 0: Transfer (A → B, USDC only)
                    1'b0: begin
                        // Check: A has enough USDC (amount + fee)
                        if (eff_a_0 >= (p1_amt_0 + fee_0)) begin
                            stage2_success = 1'b1;
                            write_en = 1'b1;
                            new_state_a = {eff_a_1, eff_a_0 - (p1_amt_0 + fee_0)};
                            new_state_b = {eff_b_1, eff_b_0 + p1_amt_0};
                        end
                    end

                    // Opcode 1: Atomic Swap (A ↔ B, bidirectional)
                    1'b1: begin
                        // Check: A has USDC, B has GPU credits
                        if (eff_a_0 >= (p1_amt_0 + fee_0) &&
                            eff_b_1 >= (p1_amt_1 + fee_1)) begin
                            stage2_success = 1'b1;
                            write_en = 1'b1;
                            // A: loses USDC+fee, gains GPU
                            new_state_a = {eff_a_1 + p1_amt_1, eff_a_0 - (p1_amt_0 + fee_0)};
                            // B: loses GPU+fee, gains USDC
                            new_state_b = {eff_b_1 - (p1_amt_1 + fee_1), eff_b_0 + p1_amt_0};
                        end
                    end
                endcase
            end
        end
    end

    // ---------------------------------------------------------
    // Stage 2: WRITE BACK
    // ---------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            m_valid <= 1'b0; m_success <= 1'b0;
            m_user_a <= '0; m_user_b <= '0;
            m_bal_a_0 <= '0; m_bal_a_1 <= '0;
            m_bal_b_0 <= '0; m_bal_b_1 <= '0;
            vault_usdc <= '0; vault_gpu  <= '0;
        end else begin
            if (write_en) begin
                // Write updated balances back to memory
                portfolios[p1_user_a] <= new_state_a;
                portfolios[p1_user_b] <= new_state_b;

                // Accumulate fees into vaults
                if (p1_opcode == 0) begin
                    // Transfer: only USDC fee
                    vault_usdc <= vault_usdc + fee_0;
                end else if (p1_opcode == 1) begin
                    // Swap: both USDC and GPU fees
                    vault_usdc <= vault_usdc + fee_0;
                    vault_gpu  <= vault_gpu  + fee_1;
                end
            end

            // Pipeline output stage
            m_valid   <= p1_valid;
            m_success <= stage2_success;
            m_user_a  <= p1_user_a;
            m_user_b  <= p1_user_b;
            {m_bal_a_1, m_bal_a_0} <= new_state_a;
            {m_bal_b_1, m_bal_b_0} <= new_state_b;
        end
    end

    // Vault outputs (combinational)
    assign m_vault_usdc = vault_usdc;
    assign m_vault_gpu  = vault_gpu;

    // ---------------------------------------------------------
    // Conservation Law Assertion (Optional for Formal Verification)
    // ---------------------------------------------------------
    // For formal tools or SVA:
    // assert property (
    //     @(posedge clk) disable iff (!rst_n)
    //     total_supply_asset0 == sum(all user asset0) + vault_usdc
    // );

endmodule
