//                              -*- Mode: Verilog -*-
// Filename        : RV32i_monocycle_controlpath.sv
// Description     : control path
// Author          : michel agoyan
// Created On      : Mon Aug 19 14:06:29 2024
// Last Modified By: michel agoyan
// Last Modified On: Mon Aug 19 14:06:29 2024
// Update Count    : 0
// Status          : Unknown, Use with caution!



module RV32i_controlpath (
    input logic clk_i,
    input logic resetn_i,
    input logic [31:0] instruction_i,
    input logic alu_zero_i,
    input logic alu_lt_i,

    output logic [2:0] pc_next_sel_o,
    output logic reg_we_o,
    output logic mem_we_o,
    output logic mem_re_o,
    output logic [1:0] alu_src1_o,
    output logic alu_src2_o,
    output logic [2:0] imm_gen_sel_o,
    output logic [3:0] alu_control_o,
    output logic [1:0] wb_sel_o,

    output logic [4:0] rd_add_o,

    output logic stall_o,

    output logic fetch_jump_o

);

  import RV32i_pkg::*;

  logic branch_taken_w;
  logic stall_w;

  logic [6:0] opcode_dec_w, opcode_exec_w, opcode_mem_w, opcode_wb_w;
  logic [6:0] func7_exec_w;
  logic [2:0] func3_exec_w;
  logic [9:0] func10_exec_w;
  logic [31:0] inst_dec_r, inst_exec_r, inst_mem_r, inst_wb_r;

  logic [4:0] rd_add_dec_w, rd_add_exec_w, rd_add_mem_w, rd_add_wb_w;

  logic branch_taken_r;








  logic [4:0] rs1_dec_w;



  assign rs1_dec_w = instruction_i[19:15];
  assign rs2_dec_w = instruction_i[24:20];
  assign rd_add_dec_w = instruction_i[11:7];



  
  // assign inst_dec_r =(stall_w == 1'b1) ? 32'h00000013 : instruction_i;
  assign inst_dec_r =(stall_w == 1'b1 || branch_taken_r == 1'b1) ? 32'h00000013 : instruction_i;




  assign opcode_dec_w = instruction_i[6:0];

  always_comb begin : pc_next_sel_comb
    if (branch_taken_w == 1'b1) pc_next_sel_o = SEL_PC_BRANCH;
    else begin
      case (opcode_dec_w)
        RV32I_I_INSTR_JALR: pc_next_sel_o = SEL_PC_JALR;
        RV32I_J_INSTR: pc_next_sel_o = SEL_PC_JAL;
        default: pc_next_sel_o = SEL_PC_PLUS_4;

      endcase
    end

  end

  always_comb begin : alu_src1_comb
    case (opcode_dec_w)
      RV32I_U_INSTR_LUI: alu_src1_o = SEL_OP1_IMM;
      RV32I_U_INSTR_AUIPC: alu_src1_o = SEL_OP1_PC;
      default: alu_src1_o = SEL_OP1_RS1;
    endcase

  end
  always_comb begin : alu_src2_comb
    case (opcode_dec_w)
      RV32I_I_INSTR_OPER: alu_src2_o = SEL_OP2_IMM;
      RV32I_I_INSTR_LOAD: alu_src2_o = SEL_OP2_IMM;
      RV32I_U_INSTR_AUIPC: alu_src2_o = SEL_OP2_IMM;
      RV32I_S_INSTR: alu_src2_o = SEL_OP2_IMM;
      default: alu_src2_o = SEL_OP2_RS2;
    endcase
  end

  always_comb begin : imm_gen_sel_comb
    case (opcode_dec_w)
      RV32I_I_INSTR_OPER: imm_gen_sel_o = IMM12_SIGEXTD_I;
      RV32I_I_INSTR_LOAD: imm_gen_sel_o = IMM12_SIGEXTD_I;
      RV32I_I_INSTR_JALR: imm_gen_sel_o = IMM12_SIGEXTD_I;
      RV32I_U_INSTR_LUI: imm_gen_sel_o = IMM20_UNSIGN_U;
      RV32I_U_INSTR_AUIPC: imm_gen_sel_o = IMM20_UNSIGN_U;
      RV32I_B_INSTR: imm_gen_sel_o = IMM12_SIGEXTD_SB;
      RV32I_S_INSTR: imm_gen_sel_o = IMM12_SIGEXTD_S;
      RV32I_J_INSTR: imm_gen_sel_o = IMM20_UNSIGN_UJ;
      default: imm_gen_sel_o = IMM12_SIGEXTD_I;
    endcase
  end

  always_ff @(posedge clk_i or negedge resetn_i) begin : exec_stage
    if (resetn_i == 1'b0) inst_exec_r <= 32'h0;
    else if (branch_taken_w == 1'b1) inst_exec_r <= 32'h00000013;
    else inst_exec_r <= inst_dec_r;
  end

  // always_ff @(posedge clk_i or negedge resetn_i) begin : exec_stage
  //   if (resetn_i == 1'b0) inst_exec_r <= 32'h0;
  //   else inst_exec_r <= inst_dec_r;
  //   // else inst_exec_r <= (branch_taken_w) ? 32'h00000013 : inst_dec_r;
  // end
  assign rd_add_exec_w = inst_exec_r[11:7];








  assign opcode_exec_w = inst_exec_r[6:0];
  assign func7_exec_w  = inst_exec_r[31:25];
  assign func3_exec_w  = inst_exec_r[14:12];
  assign func10_exec_w = {func7_exec_w, func3_exec_w};



  always_comb begin : alu_control_comb
    alu_control_o = ALU_X;
    case (opcode_exec_w)
      RV32I_R_INSTR: begin
        case (func10_exec_w)
          {RV32I_FUNCT7_ADD, RV32I_FUNCT3_ADD} : alu_control_o = ALU_ADD;
          {RV32I_FUNCT7_SUB, RV32I_FUNCT3_SUB} : alu_control_o = ALU_SUB;
          {RV32I_FUNCT7_XOR, RV32I_FUNCT3_XOR} : alu_control_o = ALU_XOR;
          {RV32I_FUNCT7_OR, RV32I_FUNCT3_OR} : alu_control_o = ALU_OR;
          {RV32I_FUNCT7_AND, RV32I_FUNCT3_AND} : alu_control_o = ALU_AND;
          {RV32I_FUNCT7_SLL, RV32I_FUNCT3_SLL} : alu_control_o = ALU_SLLV;
          {RV32I_FUNCT7_SRL, RV32I_FUNCT3_SR} : alu_control_o = ALU_SRLV;
          {RV32I_FUNCT7_SRA, RV32I_FUNCT3_SR} : alu_control_o = ALU_SRAV;
          default: alu_control_o = ALU_X;
        endcase
      end
      RV32I_I_INSTR_OPER: begin
        case (func3_exec_w)
          RV32I_FUNCT3_ADD: alu_control_o = ALU_ADD;
          RV32I_FUNCT3_XOR: alu_control_o = ALU_XOR;
          RV32I_FUNCT3_OR: alu_control_o = ALU_OR;
          RV32I_FUNCT3_AND: alu_control_o = ALU_AND;
          RV32I_FUNCT3_SLL: alu_control_o = ALU_SLLV;
          RV32I_FUNCT3_SR: begin
            if (func7_exec_w == RV32I_FUNCT7_SRL) alu_control_o = ALU_SRLV;
            else if (func7_exec_w == RV32I_FUNCT7_SRA) alu_control_o = ALU_SRAV;
          end
          RV32I_FUNCT3_SR: alu_control_o = ALU_SRAV;
          default: alu_control_o = ALU_X;
        endcase
      end
      RV32I_U_INSTR_LUI: alu_control_o = ALU_COPY_RS1;
      RV32I_B_INSTR: begin
        case (func3_exec_w)
          RV32I_FUNCT3_BEQ: alu_control_o = ALU_SUB;
          RV32I_FUNCT3_BNE: alu_control_o = ALU_SUB;
          RV32I_FUNCT3_BLT: alu_control_o = ALU_SLT;
          RV32I_FUNCT3_BGE: alu_control_o = ALU_SLT;
          RV32I_FUNCT3_BLTU: alu_control_o = ALU_SLTU;
          RV32I_FUNCT3_BGEU: alu_control_o = ALU_SLTU;
          default: alu_control_o = ALU_SUB;
        endcase
      end
      RV32I_U_INSTR_AUIPC: alu_control_o = ALU_ADD;
      RV32I_I_INSTR_LOAD: alu_control_o = ALU_ADD;
      RV32I_S_INSTR: alu_control_o = ALU_ADD;
      RV32I_I_INSTR_LOAD: alu_control_o = ALU_ADD;
      RV32I_I_INSTR_JALR: alu_control_o = ALU_ADD;

      default: alu_control_o = ALU_X;
    endcase
  end

  always_comb begin : branch_taken_comb
    case (opcode_exec_w)
      RV32I_B_INSTR:
      case (func3_exec_w)
        RV32I_FUNCT3_BEQ: begin
          if (alu_zero_i == 1'b1) branch_taken_w = 1'b1;
          else branch_taken_w = 1'b0;
        end
        RV32I_FUNCT3_BNE: begin
          if (alu_zero_i == 1'b0) branch_taken_w = 1'b1;
          else branch_taken_w = 1'b0;
        end
        RV32I_FUNCT3_BLT: begin
          if (alu_zero_i == 1'b0) branch_taken_w = 1'b1;
          else branch_taken_w = 1'b0;
        end
        RV32I_FUNCT3_BGE: begin
          if (alu_zero_i == 1'b1) branch_taken_w = 1'b1;
          else branch_taken_w = 1'b0;
        end
        RV32I_FUNCT3_BLTU: begin
          if (alu_zero_i == 1'b0) branch_taken_w = 1'b1;
          else branch_taken_w = 1'b0;
        end
        RV32I_FUNCT3_BGEU: begin
          if (alu_zero_i == 1'b1) branch_taken_w = 1'b1;
          else branch_taken_w = 1'b0;
        end
        default: branch_taken_w = 1'b0;
      endcase

      default: branch_taken_w = 1'b0;
    endcase

  end


  always_ff @(posedge clk_i or negedge resetn_i) begin : mem_stage
    if (resetn_i == 1'b0) inst_mem_r <= 32'h0;
    else inst_mem_r <= inst_exec_r;
  end
  assign rd_add_mem_w = inst_mem_r[11:7];







  assign opcode_mem_w = inst_mem_r[6:0];

  always_comb begin : mem_we_comb
    case (opcode_mem_w)
      RV32I_S_INSTR: mem_we_o = WE_1;
      default: mem_we_o = WE_0;
    endcase
  end

  always_comb begin : mem_re_comb
    case (opcode_mem_w)
      RV32I_I_INSTR_LOAD: mem_re_o = RE_1;
      default: mem_re_o = RE_0;
    endcase
  end


  always_ff @(posedge clk_i or negedge resetn_i) begin : wb_stage
    if (resetn_i == 1'b0) inst_wb_r <= 32'h0;
    else inst_wb_r <= inst_mem_r;
  end
  assign rd_add_wb_w = inst_wb_r[11:7];
  assign rd_add_o = rd_add_wb_w;







  assign opcode_wb_w = inst_wb_r[6:0];

  always_comb begin : reg_we_comb
    case (opcode_wb_w)
      RV32I_B_INSTR: reg_we_o = WE_0;
      RV32I_I_INSTR_JALR: reg_we_o = WE_1;
      RV32I_J_INSTR: reg_we_o = WE_1;
      default: reg_we_o = WE_1;
    endcase

  end

  always_comb begin : wb_sel_comb
    case (opcode_wb_w)
      RV32I_I_INSTR_LOAD: wb_sel_o = SEL_WB_MEM;
      RV32I_I_INSTR_JALR: wb_sel_o = SEL_WB_PC_PLUS_4;
      RV32I_J_INSTR: wb_sel_o = SEL_WB_PC_PLUS_4;
      default: wb_sel_o = SEL_WB_ALU;
    endcase

  end






  // generation du signal de stall

  // assign stall_w = 1'b0;
  logic stall_w_cond1, stall_w_cond2, stall_w_cond3, stall_w_cond4, stall_w_cond5, stall_w_cond6;
  


  // Fonction pour vérifier si rs1 est utilisé
  function bit rs1_used(input logic [6:0] opcode);
      case(opcode)
          RV32I_R_INSTR:          rs1_used = 1'b1;
          RV32I_I_INSTR_LOAD:     rs1_used = 1'b1;  
          RV32I_I_INSTR_JALR:     rs1_used = 1'b1;
          RV32I_I_INSTR_OPER:     rs1_used = 1'b1;
          RV32I_I_INSTR_FENCE:    rs1_used = 1'b1;
          RV32I_I_INSTR_ENVCSR:   rs1_used = 1'b1;
          RV32I_U_INSTR_LUI:      rs1_used = 1'b0; // 
          RV32I_U_INSTR_AUIPC:    rs1_used = 1'b0; // 
          RV32I_B_INSTR:          rs1_used = 1'b1;
          RV32I_S_INSTR:          rs1_used = 1'b1; 
          RV32I_J_INSTR:          rs1_used = 1'b0; // 
          default:                rs1_used = 1'b0;
      endcase
  endfunction

  // Fonction pour vérifier si rs2 est utilisé
  function bit rs2_used(input logic [6:0] opcode);
      case(opcode)
          RV32I_R_INSTR:          rs2_used = 1'b1;
          RV32I_I_INSTR_LOAD:     rs2_used = 1'b0; // 
          RV32I_I_INSTR_JALR:     rs2_used = 1'b0; // 
          RV32I_I_INSTR_OPER:     rs2_used = 1'b0; //
          RV32I_I_INSTR_FENCE:    rs2_used = 1'b0; //
          RV32I_I_INSTR_ENVCSR:   rs2_used = 1'b0; //
          RV32I_U_INSTR_LUI:      rs2_used = 1'b0; // 
          RV32I_U_INSTR_AUIPC:    rs2_used = 1'b0; // 
          RV32I_B_INSTR:          rs2_used = 1'b1;
          RV32I_S_INSTR:          rs2_used = 1'b1;  
          RV32I_J_INSTR:          rs2_used = 1'b0; // 
          default:                rs2_used = 1'b0; // 
      endcase
  endfunction

  // Fonction pour vérifier si rd est utilisé
  function bit uses_rd(input logic [6:0] opcode);
      case(opcode)
          RV32I_R_INSTR:          uses_rd = 1'b1;
          RV32I_I_INSTR_LOAD:     uses_rd = 1'b1;
          RV32I_I_INSTR_JALR:     uses_rd = 1'b1;
          RV32I_I_INSTR_OPER:     uses_rd = 1'b1;
          RV32I_I_INSTR_FENCE:    uses_rd = 1'b1;
          RV32I_I_INSTR_ENVCSR:   uses_rd = 1'b1;
          RV32I_U_INSTR_LUI:      uses_rd = 1'b1;
          RV32I_U_INSTR_AUIPC:    uses_rd = 1'b1;
          RV32I_B_INSTR:          uses_rd = 1'b0;
          RV32I_S_INSTR:          uses_rd = 1'b0;
          RV32I_J_INSTR:          uses_rd = 1'b0;//1'b1;
          default:                uses_rd = 1'b0;
      endcase
  endfunction

  //rd_add_exec_w != 0 car on ne peut pas ecrire dedans (vaut toujours 0)
	assign stall_w_cond1 = rs1_used(opcode_dec_w) && (uses_rd(opcode_exec_w) && rd_add_exec_w != 0 && rd_add_exec_w == rs1_dec_w);
	assign stall_w_cond2 = rs1_used(opcode_dec_w) && (uses_rd(opcode_mem_w)  && rd_add_mem_w  != 0 && rd_add_mem_w  == rs1_dec_w);
	assign stall_w_cond3 = rs1_used(opcode_dec_w) && (uses_rd(opcode_wb_w)   && rd_add_wb_w   != 0 && rd_add_wb_w   == rs1_dec_w);
	assign stall_w_cond4 = rs2_used(opcode_dec_w) && (uses_rd(opcode_exec_w) && rd_add_exec_w != 0 && rd_add_exec_w == rs2_dec_w);
	assign stall_w_cond5 = rs2_used(opcode_dec_w) && (uses_rd(opcode_mem_w)  && rd_add_mem_w  != 0 && rd_add_mem_w  == rs2_dec_w);
	assign stall_w_cond6 = rs2_used(opcode_dec_w) && (uses_rd(opcode_wb_w)   && rd_add_wb_w   != 0 && rd_add_wb_w   == rs2_dec_w);

	assign stall_w = stall_w_cond1 || stall_w_cond2 || stall_w_cond3 || stall_w_cond4 || stall_w_cond5 || stall_w_cond6 ;


  assign fetch_jump_o = (opcode_dec_w == RV32I_J_INSTR); //si on decode une instruction J on mets un nop en fin d'etage de fetch  


  assign stall_o = stall_w;


  // gestion des branch
  
  always_ff @(posedge clk_i or negedge resetn_i) begin : branch_taken_delay
    if (resetn_i == 1'b0) branch_taken_r <= 1'h0;
    else branch_taken_r <= branch_taken_w;
  end




endmodule
