/-
Release check for T2188 (dispatcher V1, Mon Oct  5 07:07 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19).
UN-05 rest (GreenCorr). This file checks four things on `main`: the merged pins the targets must prove
(`UNGreenCorr`, `UNGreenCorrAll`; T2174), the merged UN ports the file builds on (Pins T2174,
OU and EigenMeasurable T2177, InjSum and PoissonSmoothing T2178), the instance data, and two Mathlib
names that the dilation step uses.  `#check`/`#print` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2188-check.lean`.
-/
import RBM3D

-- the pins (targets 1 and 2 have exactly these types)
#print RBM.Univ.UNGreenCorr
#print RBM.Univ.UNGreenCorrAll
#check (∀ {d : ℕ} (sz : RBM.Gauss.Sizes d), Filter.Tendsto (fun n => sz.size n) Filter.atTop Filter.atTop →
  ∀ M : RBM.Univ.UNModel sz, RBM.Univ.UNGreenCorr sz M : Prop)
#check (RBM.Univ.UNGreenCorrAll : Prop)

-- vocabulary of the pin (Universality/Pins, T2174)
#check @RBM.Univ.UNClaim417
#check @RBM.Univ.UNApriori
#check @RBM.Univ.InWindow
#check @RBM.Univ.UNModel
#check @RBM.Univ.ouP
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.ouTStar
#check @RBM.Univ.Nsz
#check @RBM.Univ.kPoint
#check @RBM.Univ.stieltjesN
#check @RBM.Univ.IsTestFun
#check @RBM.Univ.isTestFun_comp_smul
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.card_Idx

-- merged ports used by the source (OU, EigenMeasurable: T2177; InjSum, PoissonSmoothing: T2178)
#check @RBM.Univ.measurable_ouMat
#check @RBM.Univ.eigenvalues₀_abs_sub_le
#check @RBM.Univ.InjSum_IsTestFun
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight
#check @RBM.Univ.injSum_decomp
#check @RBM.Univ.poissonKernel
#check @RBM.Univ.poissonSmooth
#check @RBM.Univ.sum_prod_lorentz_eq
#check @RBM.Univ.sum_poissonSmooth_eq
#check @RBM.Univ.poissonSmooth_error

-- instance data (d = 3)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_tendsto
#check RBM.Univ.UNModel.band RBM.Gauss.SizesInst.sz0
#check RBM.Univ.UNModel.ba RBM.Gauss.SizesInst.sz0
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.rhoSC
#check @RBM.Univ.rhoSC_pos

-- Mathlib, for the dilation step (B)(i) and the instance
#check @MeasureTheory.Measure.integral_comp_smul
#check @tendsto_natCast_atTop_iff
