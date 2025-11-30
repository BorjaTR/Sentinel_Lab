`timescale 1ns/1ps

module ledger_core #(
    parameter int USER_WIDTH = 10,    // 1024 Users
    parameter int BALANCE_WIDTH = 64  // 64-bit precision
)(
    input  logic clk,
    input  logic rst_n,

    // Input: Transaction Request
    input  logic        s_valid,
    input  logic [USER_WIDTH-1:0] s_payer,
    input  logic [USER_WIDTH-1:0] s_payee,
    input  logic [BALANCE_WIDTH-1:0] s_amount,
    
    // Output: Transaction Result
    output logic        m_valid,
    output logic        m_success, 
    output logic [USER_WIDTH-1:0] m_payer,
    output logic [USER_WIDTH-1:0] m_payee,
    output logic [BALANCE_WIDTH-1:0] m_bal_payer, 
    output logic [BALANCE_WIDTH-1:0] m_bal_payee
);

    // The Bank Vault (Dual-Port Block RAM)
    // Initialized to 1000 for simulation
    logic [BALANCE_WIDTH-1:0] balances [0:(1<<USER_WIDTH)-1];

    initial begin
        for (int i = 0; i < (1<<USER_WIDTH); i++) begin
            balances[i] = 64'd1000; 
        end
    end

    // ---------------------------------------------------------
    // Pipeline Stage 1: READ
    // ---------------------------------------------------------
    logic p1_valid;
    logic [USER_WIDTH-1:0] p1_payer, p1_payee;
    logic [BALANCE_WIDTH-1:0] p1_amount;
    logic [BALANCE_WIDTH-1:0] p1_bal_payer_read, p1_bal_payee_read;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            p1_valid  <= 1'b0;
            p1_payer  <= '0;
            p1_payee  <= '0;
            p1_amount <= '0;
        end else begin
            if (s_valid) begin
                // Synchronous RAM Read
                p1_bal_payer_read <= balances[s_payer];
                p1_bal_payee_read <= balances[s_payee];
                
                // Pass Metadata
                p1_payer  <= s_payer;
                p1_payee  <= s_payee;
                p1_amount <= s_amount;
                p1_valid  <= 1'b1;
            end else begin
                p1_valid <= 1'b0;
            end
        end
    end

    // ---------------------------------------------------------
    // Pipeline Stage 2: EXECUTE (Combinatorial)
    // ---------------------------------------------------------
    logic [BALANCE_WIDTH-1:0] new_bal_payer, new_bal_payee;
    logic stage2_success;
    logic write_en;

    always_comb begin
        // Defaults
        stage2_success = 1'b0;
        write_en = 1'b0;
        new_bal_payer = p1_bal_payer_read;
        new_bal_payee = p1_bal_payee_read;

        if (p1_valid) begin
            // 1. Handle Self-Transfer (No-Op)
            if (p1_payer == p1_payee) begin
                stage2_success = 1'b1;
                write_en = 1'b0; 
            end 
            // 2. Solvency Check
            else if (p1_bal_payer_read >= p1_amount) begin
                stage2_success = 1'b1;
                write_en = 1'b1;
                new_bal_payer = p1_bal_payer_read - p1_amount;
                new_bal_payee = p1_bal_payee_read + p1_amount;
            end 
            // 3. Failure (NSF)
            else begin
                stage2_success = 1'b0;
                write_en = 1'b0;
            end
        end
    end

    // ---------------------------------------------------------
    // Pipeline Stage 2: WRITE BACK (Synchronous)
    // ---------------------------------------------------------
    // NOTE: This logic contains a RAW Hazard!
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            m_valid     <= 1'b0;
            m_success   <= 1'b0;
            m_payer     <= '0;
            m_payee     <= '0;
            m_bal_payer <= '0;
            m_bal_payee <= '0;
        end else begin
            // Memory Write
            if (write_en) begin
                balances[p1_payer] <= new_bal_payer;
                balances[p1_payee] <= new_bal_payee;
            end

            // Output Drive
            m_valid     <= p1_valid;
            m_success   <= stage2_success;
            m_payer     <= p1_payer;
            m_payee     <= p1_payee;
            m_bal_payer <= new_bal_payer;
            m_bal_payee <= new_bal_payee;
        end
    end

endmodule
