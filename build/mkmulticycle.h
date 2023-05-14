/*
 * Generated by Bluespec Compiler, version 2023.01-6-g034050db (build 034050db)
 * 
<<<<<<< HEAD
<<<<<<< HEAD
 * On Fri May 12 18:18:58 EDT 2023
=======
 * On Sun May 14 03:24:55 EDT 2023
>>>>>>> 9423a9c (partial implementation of SMT, siingle red path)
=======
 * On Sun May 14 11:38:40 EDT 2023
>>>>>>> 42a381e (partial implementation SMT, passing red)
 * 
 */

/* Generation options: */
#ifndef __mkmulticycle_h__
#define __mkmulticycle_h__

#include "bluesim_types.h"
#include "bs_module.h"
#include "bluesim_primitives.h"
#include "bs_vcd.h"


/* Class declaration for the mkmulticycle module */
class MOD_mkmulticycle : public Module {
 
 /* Clock handles */
 private:
  tClock __clk_handle_0;
 
 /* Clock gate handles */
 public:
  tUInt8 *clk_gate[0];
 
 /* Instantiation parameters */
 public:
 
 /* Module state */
 public:
  MOD_Reg<tUInt64> INST_commit_id;
  MOD_Reg<tUInt64> INST_current_id;
  MOD_Reg<tUInt64> INST_dInst;
  MOD_Reg<tUInt64> INST_fresh_id;
  MOD_CReg<tUWide> INST_fromDmem_rv;
  MOD_CReg<tUWide> INST_fromImem_rv;
  MOD_CReg<tUWide> INST_fromMMIO_rv;
  MOD_Reg<tUInt32> INST_lfh;
  MOD_Reg<tUInt8> INST_mem_business;
  MOD_Reg<tUInt32> INST_pc;
  MOD_Fifo<tUInt64> INST_retired;
  MOD_Reg<tUInt32> INST_rf_0;
  MOD_Reg<tUInt32> INST_rf_1;
  MOD_Reg<tUInt32> INST_rf_10;
  MOD_Reg<tUInt32> INST_rf_11;
  MOD_Reg<tUInt32> INST_rf_12;
  MOD_Reg<tUInt32> INST_rf_13;
  MOD_Reg<tUInt32> INST_rf_14;
  MOD_Reg<tUInt32> INST_rf_15;
  MOD_Reg<tUInt32> INST_rf_16;
  MOD_Reg<tUInt32> INST_rf_17;
  MOD_Reg<tUInt32> INST_rf_18;
  MOD_Reg<tUInt32> INST_rf_19;
  MOD_Reg<tUInt32> INST_rf_2;
  MOD_Reg<tUInt32> INST_rf_20;
  MOD_Reg<tUInt32> INST_rf_21;
  MOD_Reg<tUInt32> INST_rf_22;
  MOD_Reg<tUInt32> INST_rf_23;
  MOD_Reg<tUInt32> INST_rf_24;
  MOD_Reg<tUInt32> INST_rf_25;
  MOD_Reg<tUInt32> INST_rf_26;
  MOD_Reg<tUInt32> INST_rf_27;
  MOD_Reg<tUInt32> INST_rf_28;
  MOD_Reg<tUInt32> INST_rf_29;
  MOD_Reg<tUInt32> INST_rf_3;
  MOD_Reg<tUInt32> INST_rf_30;
  MOD_Reg<tUInt32> INST_rf_31;
  MOD_Reg<tUInt32> INST_rf_4;
  MOD_Reg<tUInt32> INST_rf_5;
  MOD_Reg<tUInt32> INST_rf_6;
  MOD_Reg<tUInt32> INST_rf_7;
  MOD_Reg<tUInt32> INST_rf_8;
  MOD_Reg<tUInt32> INST_rf_9;
  MOD_Reg<tUInt32> INST_rv1;
  MOD_Reg<tUInt32> INST_rv2;
  MOD_Reg<tUInt32> INST_rvd;
  MOD_Fifo<tUInt64> INST_squashed;
  MOD_Reg<tUInt8> INST_starting;
  MOD_Reg<tUInt8> INST_state;
  MOD_CReg<tUWide> INST_toDmem_rv;
  MOD_CReg<tUWide> INST_toImem_rv;
  MOD_CReg<tUWide> INST_toMMIO_rv;
 
 /* Constructor */
 public:
  MOD_mkmulticycle(tSimStateHdl simHdl, char const *name, Module *parent);
 
 /* Symbol init methods */
 private:
  void init_symbols_0();
 
 /* Reset signal definitions */
 private:
  tUInt8 PORT_RST_N;
 
 /* Port definitions */
 public:
  tUInt8 PORT_EN_getMMIOResp;
  tUInt8 PORT_EN_getMMIOReq;
  tUInt8 PORT_EN_getDResp;
  tUInt8 PORT_EN_getDReq;
  tUInt8 PORT_EN_getIResp;
  tUInt8 PORT_EN_getIReq;
  tUWide PORT_getMMIOResp_a;
  tUWide PORT_getDResp_a;
  tUWide PORT_getIResp_a;
  tUWide PORT_getMMIOReq;
  tUWide PORT_getDReq;
  tUWide PORT_getIReq;
 
 /* Publicly accessible definitions */
 public:
  tUInt8 DEF_WILL_FIRE_getMMIOResp;
  tUInt8 DEF_WILL_FIRE_getMMIOReq;
  tUInt8 DEF_WILL_FIRE_getDResp;
  tUInt8 DEF_WILL_FIRE_getDReq;
  tUInt8 DEF_WILL_FIRE_getIResp;
  tUInt8 DEF_WILL_FIRE_getIReq;
  tUWide DEF_toMMIO_rv_port1__read____d492;
  tUWide DEF_toDmem_rv_port1__read____d488;
  tUWide DEF_toImem_rv_port1__read____d484;
  tUInt8 DEF_dInst_89_BITS_11_TO_7___d206;
  tUInt8 DEF_mem_business_57_BIT_0___d358;
  tUInt8 DEF_dInst_89_BIT_6___d190;
  tUInt32 DEF_rv1_95_PLUS_IF_dInst_89_BIT_35_96_AND_IF_dInst_ETC___d236;
  tUWide DEF_fromMMIO_rv_port1__read____d359;
  tUWide DEF_fromMMIO_rv_port0__read____d494;
  tUWide DEF_toMMIO_rv_port0__read____d242;
  tUWide DEF_fromDmem_rv_port1__read____d361;
  tUWide DEF_fromDmem_rv_port0__read____d490;
  tUWide DEF_toDmem_rv_port0__read____d245;
  tUWide DEF_fromImem_rv_port1__read____d17;
  tUWide DEF_fromImem_rv_port0__read____d486;
  tUWide DEF_toImem_rv_port0__read____d4;
  tUInt64 DEF_dInst___d189;
  tUInt32 DEF_rs1_val__h10070;
  tUInt8 DEF_mem_business___d357;
  tUInt8 DEF_starting__h4013;
  tUInt32 DEF_rv1_95_PLUS_IF_dInst_89_BIT_35_96_AND_IF_dInst_ETC___d235;
  tUInt32 DEF_x__h8347;
  tUInt8 DEF_mem_business_57_BITS_5_TO_3___d368;
  tUInt8 DEF_dInst_89_BIT_36___d365;
  tUInt8 DEF_dInst_89_BIT_35___d196;
  tUInt8 DEF_dInst_89_BIT_31___d211;
  tUInt32 DEF_imm__h8147;
  tUInt8 DEF_IF_dInst_89_BIT_35_96_THEN_dInst_89_BITS_34_TO_ETC___d198;
  tUInt8 DEF_dInst_89_BITS_11_TO_7_06_EQ_0___d367;
  tUInt8 DEF_dInst_89_BITS_4_TO_3_91_EQ_0b0___d192;
  tUInt8 DEF_dInst_89_BIT_6_90_OR_NOT_dInst_89_BITS_4_TO_3__ETC___d194;
  tUInt32 DEF_x__h8624;
  tUInt32 DEF_x__h8463;
  tUInt32 DEF_x__h8394;
 
 /* Local definitions */
 private:
  tUInt32 DEF_TASK_fopen___d2;
  tUInt32 DEF_signed_0___d14;
  tUInt64 DEF_x__h10689;
  tUInt32 DEF_lfh___d3;
  tUInt32 DEF_pc__h10072;
  tUInt8 DEF_NOT_dInst_89_BIT_6_90_53_AND_dInst_89_BITS_4_T_ETC___d254;
  tUWide DEF__16_CONCAT_pc_5_CONCAT_0___d16;
  tUWide DEF__1_CONCAT_IF_dInst_89_BIT_5_56_THEN_IF_dInst_89_ETC___d274;
  tUWide DEF__1_CONCAT_getMMIOResp_a___d493;
  tUWide DEF__1_CONCAT_getDResp_a___d489;
  tUWide DEF__1_CONCAT_getIResp_a___d485;
  tUWide DEF__0_CONCAT_DONTCARE___d22;
 
 /* Rules */
 public:
  void RL_do_tic_logging();
  void RL_fetch();
  void RL_decode();
  void RL_execute();
  void RL_writeback();
  void RL_administrative_konata_commit();
  void RL_administrative_konata_flush();
 
 /* Methods */
 public:
  tUWide METH_getIReq();
  tUInt8 METH_RDY_getIReq();
  void METH_getIResp(tUWide ARG_getIResp_a);
  tUInt8 METH_RDY_getIResp();
  tUWide METH_getDReq();
  tUInt8 METH_RDY_getDReq();
  void METH_getDResp(tUWide ARG_getDResp_a);
  tUInt8 METH_RDY_getDResp();
  tUWide METH_getMMIOReq();
  tUInt8 METH_RDY_getMMIOReq();
  void METH_getMMIOResp(tUWide ARG_getMMIOResp_a);
  tUInt8 METH_RDY_getMMIOResp();
 
 /* Reset routines */
 public:
  void reset_RST_N(tUInt8 ARG_rst_in);
 
 /* Static handles to reset routines */
 public:
 
 /* Pointers to reset fns in parent module for asserting output resets */
 private:
 
 /* Functions for the parent module to register its reset fns */
 public:
 
 /* Functions to set the elaborated clock id */
 public:
  void set_clk_0(char const *s);
 
 /* State dumping routine */
 public:
  void dump_state(unsigned int indent);
 
 /* VCD dumping routines */
 public:
  unsigned int dump_VCD_defs(unsigned int levels);
  void dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_mkmulticycle &backing);
  void vcd_defs(tVCDDumpType dt, MOD_mkmulticycle &backing);
  void vcd_prims(tVCDDumpType dt, MOD_mkmulticycle &backing);
};

#endif /* ifndef __mkmulticycle_h__ */
