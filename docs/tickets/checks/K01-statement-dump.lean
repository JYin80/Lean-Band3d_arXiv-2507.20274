/-
Statement dump for the future BA-K01 ticket (dispatcher V2; supervisor 2051 G1): the hub compiles this
file on `main` and saves the output, so that the K01 check file can pin the old band statements verbatim
(`example : <old statement> := <old name>`).  #check only; never imported or merged.
-/
import RBM3D.Loop.Unique
import RBM3D.Loop.KLUnique

set_option pp.funBinderTypes true
#check @RBM.Loop.LoopIdx.two_le_length_cutGlueL
#check @RBM.Loop.LoopIdx.two_le_length_cutGlueR
#check @RBM.Loop.LoopIdx.length_cutGlueR_eq_two
#check @RBM.Loop.LoopIdx.length_cutGlueL_eq_two
#check @RBM.Loop.LoopVec
#check @RBM.Loop.LoopVec.toLoop
#check @RBM.Loop.LoopVec.exists_toLoop
#check @RBM.Loop.norm_SB_apply_le
#check @RBM.Loop.norm_mul_mul_sub_le
#check @RBM.Loop.eq_on_level
#check @RBM.Loop.isKLoop_unique
#check @RBM.Loop.exists_eq_of_length_two
#check @RBM.Loop.KLretire_twoLoopBounded
#check @RBM.Loop.kTwoFormula_of_isKLoop
#check @RBM.Loop.pureLoop_two_of_isKLoop
#check @RBM.Loop.KLK_unique
#check @RBM.Loop.KLK_translate
#check @RBM.Loop.KLK_rotate
