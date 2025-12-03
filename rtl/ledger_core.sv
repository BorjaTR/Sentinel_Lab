`timescale 1ns/1ps

module ledger_core #(
    parameter int USER_WIDTH = 10,
    parameter int BALANCE_WIDTH = 64
)(
    input  logic clk,
    input  logic rst_n,

    // Input
    input  logic        s_valid,
    input  logic        s_opcode,
    input  logic [USER_WIDTH-1:0] s_user_a,
    input  logic [USER_WIDTH-1:0] s_user_b,
    input  logic [BALANCE_WIDTH-1:0] s_amount_0,
    input  logic [BALANCE_WIDTH-1:0] s_amount_1,
    
    // Output
    output logic        m_valid,
    output logic        m_success, 
    output logic [USER_WIDTH-1:0] m_user_a,
    output logic [USER_WIDTH-1:0] m_user_b,
    output logic [BALANCE_WIDTH-1:0] m_bal_a_0, 
    output logic [BALANCE_WIDTH-1:0] m_bal_a_1,
    output logic [BALANCE_WIDTH-1:0] m_bal_b_0, 
    output logic [BALANCE_WIDTH-1:0] m_bal_b_1,
    
    // NEW: Fee Vault Interface (Live Revenue Stream)
    output logic [BALANCE_WIDTH-1:0] m_vault_usdc,
    output logic [BALANCE_WIDTH-1:0] m_vault_gpu
);

    // ---------------------------------------------------------
    // State Memory
    // ---------------------------------------------------------
    logic [2*BALANCE_WIDTH-1:0] portfolios [0:(1<<USER_WIDTH)-1];
    
    // NEW: Fee Accumulators (The "Vault" Register)
    logic [BALANCE_WIDTH-1:0] vault_usdc;
    logic [BALANCE_WIDTH-1:0] vault_gpu;

    initial begin
        for (int i = 0; i < (1<<USER_WIDTH); i++) begin
            portfolios[i] = {64'd500, 64'd1000}; 
        end
    end

    // ---------------------------------------------------------
    // Stage 1: READ
    // ---------------------------------------------------------
    logic p1_valid, p1_opcode;
    logic [USER_WIDTH-1:0] p1_user_a, p1_user_b;
    logic [BALANCE_WIDTH-1:0] p1_amt_0, p1_amt_1;
    logic [2*BALANCE_WIDTH-1:0] p1_data_a, p1_data_b;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            p1_valid <= 1'b0;
            p1_user_a <= '0; p1_user_b <= '0;
            p1_amt_0 <= '0; p1_amt_1 <= '0; p1_opcode <= '0;
            p1_data_a <= '0; p1_data_b <= '0;
        end else begin
            if (s_valid) begin
                p1_data_a <= portfolios[s_user_a];
                p1_data_b <= portfolios[s_user_b];
                
                p1_user_a <= s_user_a; p1_user_b <= s_user_b;
                p1_amt_0  <= s_amount_0; p1_amt_1  <= s_amount_1;
                p1_opcode <= s_opcode;   p1_valid  <= 1'b1;
            end else begin
                p1_valid <= 1'b0;
            end
        end
    end

    // ---------------------------------------------------------
    // Stage 2: EXECUTE with FEES
    // ---------------------------------------------------------
    logic [2*BALANCE_WIDTH-1:0] new_state_a, new_state_b;
    logic stage2_success, write_en;
    
    // Internal calculations
    logic [BALANCE_WIDTH-1:0] eff_a_0, eff_a_1;
    logic [BALANCE_WIDTH-1:0] eff_b_0, eff_b_1;
    logic [2*BALANCE_WIDTH-1:0] raw_fwd_a, raw_fwd_b;
    
    // Fees
    logic [BALANCE_WIDTH-1:0] fee_0, fee_1;

    always_comb begin
        // 1. Forwarding
        raw_fwd_a = p1_data_a;
        raw_fwd_b = p1_data_b;

        if (m_valid && m_success && (m_user_a == p1_user_a)) raw_fwd_a = {m_bal_a_1, m_bal_a_0};
        else if (m_valid && m_success && (m_user_b == p1_user_a)) raw_fwd_a = {m_bal_b_1, m_bal_b_0};

        if (m_valid && m_success && (m_user_a == p1_user_b)) raw_fwd_b = {m_bal_a_1, m_bal_a_0};
        else if (m_valid && m_success && (m_user_b == p1_user_b)) raw_fwd_b = {m_bal_b_1, m_bal_b_0};

        {eff_a_1, eff_a_0} = raw_fwd_a;
        {eff_b_1, eff_b_0} = raw_fwd_b;

        // 2. Fee Calculation (Bit Shift >> 11 is approx 0.05%)
        fee_0 = p1_amt_0 >> 11; 
        fee_1 = p1_amt_1 >> 11;

        // 3. Logic
        stage2_success = 1'b0;
        write_en = 1'b0;
        new_state_a = raw_fwd_a;
        new_state_b = raw_fwd_b;

        if (p1_valid) begin
            if (p1_user_a == p1_user_b) begin
                stage2_success = 1'b1; 
            end else begin
                case (p1_opcode)
                    // Transfer USDC
                    1'b0: begin
                        // A pays Amount + Fee
                        if (eff_a_0 >= (p1_amt_0 + fee_0)) begin
                            stage2_success = 1'b1;
                            write_en = 1'b1;
                            new_state_a = {eff_a_1, eff_a_0 - (p1_amt_0 + fee_0)}; 
                            new_state_b = {eff_b_1, eff_b_0 + p1_amt_0}; 
                        end
                    end
                    // Swap
                    1'b1: begin
                        // A pays Fee on USDC, B pays Fee on GPU (Simplification)
                        if (eff_a_0 >= (p1_amt_0 + fee_0) && eff_b_1 >= (p1_amt_1 + fee_1)) begin
                            stage2_success = 1'b1;
                            write_en = 1'b1;
                            new_state_a = {eff_a_1 + p1_amt_1, eff_a_0 - (p1_amt_0 + fee_0)};
                            new_state_b = {eff_b_1 - (p1_amt_1 + fee_1), eff_b_0 + p1_amt_0};
                        end
                    end
                endcase
            end
        end
    end

    // ---------------------------------------------------------
    // Stage 2: WRITE BACK & ACCUMULATE
    // ---------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            m_valid <= 1'b0; m_success <= 1'b0;
            m_user_a <= '0; m_user_b <= '0;
            m_bal_a_0 <= '0; m_bal_a_1 <= '0;
            m_bal_b_0 <= '0; m_bal_b_1 <= '0;
            
            // Reset Vault
            vault_usdc <= '0;
            vault_gpu  <= '0;
        end else begin
            if (write_en) begin
                portfolios[p1_user_a] <= new_state_a;
                portfolios[p1_user_b] <= new_state_b;
                
                // Update Vault (Accumulator)
                if (p1_opcode == 0) begin
                    vault_usdc <= vault_usdc + fee_0;
                end else if (p1_opcode == 1) begin
                    vault_usdc <= vault_usdc + fee_0;
                    vault_gpu  <= vault_gpu  + fee_1;
                end
            end

            m_valid   <= p1_valid;
            m_success <= stage2_success;
            m_user_a  <= p1_user_a;
            m_user_b  <= p1_user_b;
            
            {m_bal_a_1, m_bal_a_0} <= new_state_a;
            {m_bal_b_1, m_bal_b_0} <= new_state_b;
        end
    end
    
    // Expose Vault for Telemetry
    assign m_vault_usdc = vault_usdc;
    assign m_vault_gpu  = vault_gpu;

endmodule
