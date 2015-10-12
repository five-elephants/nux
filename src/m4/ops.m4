
changequote(<:,:>)
define(<:OPCMP:>, <:
unique casez({$1.x.opcd, $1.x.xo}):>)
define(<:ENDOPCMP:>, <:endcase:>)

define(<:OP:>, <:{$1, 10'bz}:>)
define(<:OPXO:>, <:{Op_alu_xo, 1'bz, $1}:>)
define(<:OPX:>, <:{Op_alu_xo, $1}:>)
define(<:OPX2:>, <:{$1, $2}:>)
define(<:OPNVE:>, <:{Op_nve_xo, $1}:>)
define(<:OPFXV:>, <:{Op_nve_xo, $1, 1'bz}:>)

dnl ---------------------------------------------------------------------------
define(<:BRANCH_OPS:>, <:OP(Op_branch), OP(Op_bc), OPX2(Op_bclr, Xxop_bclr),
  OPX2(Op_bclr, Xxop_bcctr), OPX2(Op_bclr, Xxop_rfi), OPX2(Op_bclr, Xxop_rfci),
  OPX2(Op_bclr, Xxop_rfmci):>)
dnl ---------------------------------------------------------------------------
define(<:LOAD_IMMEDIATE_OPS:>, <:OP(Op_lwz), OP(Op_lwzu), OP(Op_lbz), OP(Op_lbzu),
  OP(Op_lhz), OP(Op_lhzu), OP(Op_lmw), OP(Op_lha), OP(Op_lhau):>)

define(<:LOAD_INDEXED_OPS:>, <:OPX(Xop_lwzx), OPX(Xop_lwzux),
  OPX(Xop_lhzx), OPX(Xop_lhzux), OPX(Xop_lbzx), OPX(Xop_lbzux),
  OPX(Xop_lhax), OPX(Xop_lhaux):>)

define(<:LOAD_ALGEBRAIC_OPS:>, <:OP(Op_lha), OPX(Xop_lhax), OP(Op_lhau), OPX(Xop_lhaux):>)

define(<:LOAD_OPS:>, <:LOAD_IMMEDIATE_OPS, LOAD_INDEXED_OPS:>) 

define(<:LOAD_UPDATE_OPS:>, <:OP(Op_lwzu), OP(Op_lbzu), OP(Op_lhzu),
  OPX(Xop_lwzux), OPX(Xop_lhzux), OPX(Xop_lbzux), OP(Op_lhau), OPX(Xop_lhaux):>)

define(<:LOAD_NOUPDATE_OPS:>, <:OP(Op_lwz), OP(Op_lbz), OP(Op_lhz), OP(Op_lmw),
	OPX(Xop_lwzx), OPX(Xop_lhzx), OPX(Xop_lbzx), OP(Op_lha), OPX(Xop_lhax):>)
dnl ---------------------------------------------------------------------------
define(<:STORE_IMMEDIATE_OPS:>, <:OP(Op_stw), OP(Op_stwu), OP(Op_sth), OP(Op_sthu),
  OP(Op_stb), OP(Op_stbu), OP(Op_stmw):>)

define(<:STORE_INDEXED_OPS:>, <:OPX(Xop_stwx), OPX(Xop_stwux), 
  OPX(Xop_stbx), OPX(Xop_stbux), OPX(Xop_sthx), OPX(Xop_sthux):>)

define(<:STORE_OPS:>, <:STORE_IMMEDIATE_OPS, STORE_INDEXED_OPS:>)

define(<:STORE_UPDATE_OPS:>,
  <:OP(Op_stwu), OP(Op_sthu), OP(Op_stbu),
  OPX(Xop_stwux), OPX(Xop_sthux), OPX(Xop_stbux):>)

define(<:STORE_NOUPDATE_OPS:>,
  <:OP(Op_stw), OP(Op_sth), OP(Op_stb),
  OPX(Xop_stwx), OPX(Xop_sthx), OPX(Xop_stbx):>)
dnl ---------------------------------------------------------------------------
define(<:LOGICAL_IMMEDIATE_OPS:>, <:OP(Op_andi), OP(Op_ori), OP(Op_oris), OP(Op_andis),
  OP(Op_xori), OP(Op_xoris):>)
define(<:LOGICAL_REG_OPS:>, <:
  OPX(Xop_and), OPX(Xop_andc), OPX(Xop_or), OPX(Xop_orc),
  OPX(Xop_xor), OPX(Xop_nand), OPX(Xop_nor), OPX(Xop_eqv):>)
define(<:LOGICAL_ONE_REG_OPS:>, <:OPX(Xop_prtyw), OPX(Xop_popcb), OPX(Xop_cntlzw), 
  OPX(Xop_extsb), OPX(Xop_extsh):>)

define(<:LOGICAL_OPS:>, <:LOGICAL_IMMEDIATE_OPS, LOGICAL_REG_OPS, LOGICAL_ONE_REG_OPS:>)
dnl ---------------------------------------------------------------------------
define(<:ROTATE_IMMEDIATE_OPS:>, <:OP(Op_rlwimi), OP(Op_rlwinm), OPX(Xop_srawi):>)
define(<:ROTATE_REG_OPS:>, <:OP(Op_rlwnm), OPX(Xop_slw), OPX(Xop_sraw), OPX(Xop_srw):>)

define(<:ROTATE_OPS:>, <:ROTATE_IMMEDIATE_OPS, ROTATE_REG_OPS:>)

define(<:ROTATE_INSERTING_OPS:>, <:OP(Op_rlwimi), OPX(Xop_srawi), OPX(Xop_sraw):>)
define(<:ROTATE_ANDING_OPS:>, <:OP(Op_rlwinm), OP(Op_rlwnm), OPX(Xop_slw), OPX(Xop_srw):>)
dnl ---------------------------------------------------------------------------
define(<:COMPARE_IMMEDIATE_OPS:>, <:OP(Op_cmpi), OP(Op_cmpli):>)

define(<:COMPARE_OPS:>, <:COMPARE_IMMEDIATE_OPS, OPX(Xop_cmp), OPX(Xop_cmpl):>)
dnl ---------------------------------------------------------------------------
define(<:TRAP_IMMEDIATE_OPS:>, <:OP(Op_twi):>)
define(<:TRAP_REG_OPS:>, <:OPX(Xop_tw):>)

define(<:TRAP_OPS:>, <:TRAP_IMMEDIATE_OPS, TRAP_REG_OPS:>)
dnl ---------------------------------------------------------------------------
define(<:MUL_IMMEDIATE_OPS:>, <:OP(Op_mulli):>)
define(<:MUL_REG_OPS:>, <:OPXO(Xop_mullw), OPXO(Xop_mulhwu), OPXO(Xop_mulhw):>)

define(<:MUL_OPS:>,
  <:MUL_IMMEDIATE_OPS, MUL_REG_OPS:>)
dnl ---------------------------------------------------------------------------
define(<:DIV_OPS:>,
  <:OPXO(Xop_divw), OPXO(Xop_divwu):>)
dnl ---------------------------------------------------------------------------
define(<:ADDSUB_IMMEDIATE_OPS:>,
  <:OP(Op_addi), OP(Op_addis), OP(Op_addic), OP(Op_addic_rec),
  OP(Op_subfic):>)

define(<:ADDSUB_REG_OPS:>,
  <:OPXO(Xop_add), OPXO(Xop_addc), OPXO(Xop_adde),
  OPXO(Xop_addme), OPXO(Xop_addze),
  OPXO(Xop_subf), OPXO(Xop_subfc), OPXO(Xop_subfe),
  OPXO(Xop_subfze), OPXO(Xop_subfme):>)

define(<:ADDSUB_OPS:>, <:ADDSUB_IMMEDIATE_OPS, ADDSUB_REG_OPS:>)
dnl ---------------------------------------------------------------------------
define(<:CR_LOGICAL_OPS:>, <:OPX2(Op_bclr, Xxop_crand), OPX2(Op_bclr, Xxop_crnand),
  OPX2(Op_bclr, Xxop_cror), OPX2(Op_bclr, Xxop_crnor), OPX2(Op_bclr, Xxop_crxor), 
  OPX2(Op_bclr, Xxop_creqv), OPX2(Op_bclr, Xxop_crorc),
  OPX2(Op_bclr, Xxop_crandc):>)
dnl ---------------------------------------------------------------------------
define(<:MOVE_WITH_CRF:>, <:OPX(Xop_mtocrf), OPX(Xop_mfocrf):>)
define(<:MOVE_WITH_SYSTEM_REG_OPS:>,
  <:OPX(Xop_mtspr), OPX(Xop_mfspr), MOVE_WITH_CRF, OPX(Xop_mfmsr), OPX(Xop_mtmsr):>)
dnl ---------------------------------------------------------------------------
define(<:DEV_CTRL_OPS:>, <:OPX(Xop_eciwx), OPX(Xop_ecowx):>)
dnl ---------------------------------------------------------------------------
define(<:VECTOR_HALFWORD_OPS:>, <:
  OPFXV(Xop_fxvmahm),
  OPFXV(Xop_fxvmahfs),
  OPFXV(Xop_fxvmatachm),
  OPFXV(Xop_fxvmatachfs),
  OPFXV(Xop_fxvmtach), 
  OPFXV(Xop_fxvmtachf),
  OPFXV(Xop_fxvmulhm),
  OPFXV(Xop_fxvmulhfs),
  OPFXV(Xop_fxvmultachm),
  OPFXV(Xop_fxvmultachfs),
  OPFXV(Xop_fxvcmph),
  OPFXV(Xop_fxvaddhm),
  OPFXV(Xop_fxvaddhfs),
  OPFXV(Xop_fxvaddtachm),
  OPFXV(Xop_fxvaddachm),
  OPFXV(Xop_fxvaddachfs),
  OPFXV(Xop_fxvaddactachm),
  OPFXV(Xop_fxvaddactachf),
  OPFXV(Xop_fxvsubhm),
  OPFXV(Xop_fxvsubhfs),
  OPFXV(Xop_fxvsplath),
  OPFXV(Xop_fxvshh)
:>)

define(<:VECTOR_BYTE_OPS:>, <:
  OPFXV(Xop_fxvmtacb),
  OPFXV(Xop_fxvmtacbf),
  OPFXV(Xop_fxvmabm),
  OPFXV(Xop_fxvmabfs),
  OPFXV(Xop_fxvmatacbm),
  OPFXV(Xop_fxvmatacbfs),
  OPFXV(Xop_fxvmulbm),
  OPFXV(Xop_fxvmulbfs),
  OPFXV(Xop_fxvmultacbm),
  OPFXV(Xop_fxvmultacbfs),
  OPFXV(Xop_fxvsubbm),
  OPFXV(Xop_fxvsubbfs),
  OPFXV(Xop_fxvaddactacb),
  OPFXV(Xop_fxvaddactacbf),
  OPFXV(Xop_fxvaddacbm),
  OPFXV(Xop_fxvaddacbfs),
  OPFXV(Xop_fxvaddtacb),
  OPFXV(Xop_fxvaddbm),
  OPFXV(Xop_fxvaddbfs),
  OPFXV(Xop_fxvcmpb),
  OPFXV(Xop_fxvsplatb),
  OPFXV(Xop_fxvshb)
:>)

define(<:VECTOR_OPS:>, <:
  OPFXV(Xop_fxvlax),
  OPFXV(Xop_fxvstax),
  OPFXV(Xop_fxvinx),
  OPFXV(Xop_fxvoutx),
  OPFXV(Xop_fxvpckbu),
  OPFXV(Xop_fxvpckbl),
  OPFXV(Xop_fxvupckbr),
  OPFXV(Xop_fxvupckbl),
  OPFXV(Xop_fxvsel),
  VECTOR_HALFWORD_OPS,
  VECTOR_BYTE_OPS
:>)

define(<:VECTOR_LOAD_OPS:>, <:OPFXV(Xop_fxvlax):>)
define(<:VECTOR_STORE_OPS:>, <:OPFXV(Xop_fxvstax):>)
dnl ---------------------------------------------------------------------------
define(<:NEVER_OPS:>, <:OP(Op_nvecmpi), OPX2(Op_nve_xo, Xop_nvem),
  OPX2(Op_nve_xo, Xop_nves), OPX2(Op_nve_xo, Xop_nvemtl):>)
dnl ---------------------------------------------------------------------------
define(<:SYNAPSE_OPS:>, <:OP(Op_syncmpi), OP(Op_syncmpi_rec),
  OPNVE(Xop_synm), OPNVE(Xop_syns), OPNVE(Xop_synmtl), OPNVE(Xop_synmtvr),
  OPNVE(Xop_synmfvr), OPNVE(Xop_synmtp), OPNVE(Xop_synmfp), OPNVE(Xop_synmvvr),
  OPNVE(Xop_synops), OPNVE(Xop_synswp):>)

define(<:SYNAPSE_DETERMINISTIC_OPS:>, <:OP(Op_syncmpi), OP(Op_syncmpi_rec),
  OPNVE(Xop_synm), OPNVE(Xop_syns), OPNVE(Xop_synmtl), OPNVE(Xop_synmtvr),
  OPNVE(Xop_synmfvr), OPNVE(Xop_synmtp), OPNVE(Xop_synmfp), OPNVE(Xop_synmvvr),
  OPNVE(Xop_synswp):>)

define(<:SYNAPSE_ND_OPS:>, <:OPNVE(Xop_synops):>)
dnl ---------------------------------------------------------------------------
dnl ---------------------------------------------------------------------------
dnl ---------------------------------------------------------------------------

dnl vim: expandtab ts=2 sw=2 softtabstop=2 smarttab:
