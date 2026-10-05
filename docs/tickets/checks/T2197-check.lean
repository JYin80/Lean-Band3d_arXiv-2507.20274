/-
Release check for T2197 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §20, §29, §45 O2, §57 (3), §58 (3)).
BA-C1a = BA-D1b (the T2161 probe sections 4-7 re-pinned over the law `(sz.withLam 0).seqP`) + the closure of D472
(the fine-lattice `M` and `(self_m)` with `N⁻¹ tr`).
Section 1: `#check` of every merged name the ticket cites (namespaces as on `main` 6f8b2e2).
Section 2: target 1 (D472): `BASelfFine` and the four new statements as `def … : Prop` (the library defines `BASelfFine`
with this body and states the four theorems with exactly these bodies, names without `_stmt`).
Section 3: target 2, the five PT pins, verbatim from `t/T2161:RBM3D/Probe/T2161Pins.lean` (82e72b3) `:676-727`, except that the
probe's tactic proof of `NeZero L` (`:680`, `:691`, `:701`, `:712`, `:724`; md5 of the five texts with that term put back equals the probe's) is written as a term (`NeZero L` is a `Prop`, so the two texts are definitionally equal; the library
keeps the probe text).  The structure `BAProp5to8` (`:729-734`) is not repeated here (structures are not pins of this file).
Section 4: target 4, `PrecL`, verbatim from `t/T2173:RBM3D/Probe/T2173Pins.lean` (a543154) `:1967-1968`.
Section 5: Prop-valued examples (statement shapes at concrete data, no proof obligation).
No theorem, no proof, no placeholder, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2197-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BASelf_subord
#check @RBM.BA.BAt0
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BAflowE
#check @RBM.BA.BAzztE_data
#check @RBM.BA.BAm
#check @RBM.BA.BArho
#check @RBM.BA.BAbulk
#check @RBM.BA.BAReal
#check @RBM.BA.BAdom
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAg0_le
#check @RBM.BA.BAMsigma
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
#check @RBM.BA.BATheta0
#check @RBM.BA.BAmExists
#check @RBM.BA.BAmUniqReal
#check @RBM.BA.BAWard
#check @RBM.BA.BAPropM
#check @RBM.BA.BAMB_trace_eq_sum
#check @RBM.BA.BASelf_exists
#check @RBM.BA.BASelf_unique
#check @RBM.BA.baMExists_holds
#check @RBM.BA.baMUniqReal_holds
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_real_eq_of_self
#check @RBM.BA.MFixedPointInst.wI
#check @RBM.BA.MFixedPointInst.one_lt_wI
#check @RBM.BA.MFixedPointInst.wI_norm
#check @RBM.BA.MFixedPointInst.mS
#check @RBM.BA.MFixedPointInst.zS
#check @RBM.BA.MFixedPointInst.selfS
#check @RBM.BA.MFixedPointInst.zS_im_pos
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.exists_flowPt
#check @RBM.BA.MFixedPointInst.P
-- T2013 (MD-3, 868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Loop/GLoopFlow.lean`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiV
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.PsiI_isHermitian
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Gauss.Sizes.Gt_BA
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Mres
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.etaT
-- T2006 (MD-1, 0a873f1): `RBM3D/Defs/Sizes.lean`, `RBM3D/Gauss/FineModel.lean`; `RBM3D/Gauss/Model.lean`
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.split
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
#check @RBM.Gauss.svarF
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.Sizes.SeqCoord
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqGvar
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqHflow
-- T2012 (MD-2, 9e2b00f): `RBM3D/Defs/StochDomAt.lean`
#check @RBM.StochDomAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Whp
-- T2028 (S1-07, 64bdfd3): `RBM3D/Induction/Defs.lean`
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.STmaxLoop2
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STLocalMax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STStep1Weak
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.Sizes.STStep1
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.W_ge_32
#check @RBM.Gauss.InductionDefsInst.conStInd_inst
-- T2066 (ST2-01, 86124dc): `RBM3D/Induction/Step2Defs.lean`
#check @RBM.Gauss.Sizes.STprof
#check @RBM.Gauss.Sizes.STEEk
#check @RBM.Gauss.Sizes.STInitialGT2
#check @RBM.Gauss.Sizes.STLWassmExp
-- T2127 (KL14b, b06ff9b): `RBM3D/Loop/TreeRep.lean`, `RBM3D/Loop/KLTree.lean`, `RBM3D/Propagator/Pins.lean`
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.IsKLoopS
#check @RBM.PropSpin
-- deterministic vocabulary (`RBM3D/Defs/{Params,Lattice,Semicircle,Block}.lean`), resolvent
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.Adj
#check @RBM.mE
#check @RBM.msc
#check @RBM.lemT
#check @RBM.SB
#check @RBM.isUnit_sub_smul_of_isHermitian
-- T2174 (UN-01, f8ad4b4) and T2187 (UN-01b, fdbb6f0): the UN side that BA-C1b and BA-V3 build on
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.ba
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNModelC
#check @RBM.Univ.UNKind
#check @RBM.Univ.UNOURowk
#check @RBM.Univ.UNClaimAllC
#check @RBM.Univ.un_claimAll_of_rowsk

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

namespace RBM.BA.T2197Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 2. Target 1 (D472): the fine-lattice `M` and `(self_m)` with `N⁻¹ tr` -/

/-- Target 1 (new vocabulary): `(self_m)` as the paper writes it (`1_2:626-629`), on the fine lattice:
`m = N⁻¹ tr (gΨ - z - m)⁻¹`, `Ψ = Ψ^{(B)} ⊗ I_{W^d}` (`1_2:615`, merged `PsiI`), `N = (WL)^d`, `Im m > 0`. -/
def BASelfFine (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * (Mres ((g : ℂ) • PsiI d L W) z m).trace

/-- Target 1a `BAMres_fine_kron`: `(def_G0)` (`1_2:631-633`), `M = M^{(B)} ⊗ I_{W^d}` on the fine lattice
(through the merged bridge `splitEquiv`, as `PsiI` is built from `PsiV`). -/
def BAMres_fine_kron_stmt (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    Mres ((g : ℂ) • PsiI d L W) z m =
      ((BAMB d L g z m ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) : Matrix (Vtx d L W) (Vtx d L W) ℂ)).submatrix
        (splitEquiv d L W) (splitEquiv d L W)

/-- Target 1b `BAMres_fine_apply`: the entrywise form, `M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}`. -/
def BAMres_fine_apply_stmt (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 → ∀ x y : Idx d L W,
    Mres ((g : ℂ) • PsiI d L W) z m x y =
      if (split d L W x).2 = (split d L W y).2 then BAMB d L g z m (split d L W x).1 (split d L W y).1 else 0

/-- Target 1c `BAfine_trace`: the two normalised traces agree, `N⁻¹ tr M = L^{-d} tr M^{(B)}` (D472). -/
def BAfine_trace_stmt (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * (Mres ((g : ℂ) • PsiI d L W) z m).trace =
      (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace

/-- Target 1d `BASelf_iff_fine`: the block-lattice `(self_m)` of the merged `BASelf` is the paper's, for every
`Im z ≥ 0` (real axis included), every `W ≥ 1`. -/
def BASelf_iff_fine_stmt (d L W : ℕ) [NeZero L] [NeZero W] : Prop :=
  ∀ (g : ℝ) (z m : ℂ), 0 ≤ z.im → (BASelfFine d L W g z m ↔ BASelf d L g z m)

/-! ## 3. Target 2: the PT pins of the block Anderson model (`lem_propTH` properties 5-8 for `Θ^{(σ₁,σ₂)}_t`) -/

section PTPins

variable (d : ℕ)

/-- **Property 5** `(prop:ThfadC)`: `|Θ_t(0,a)| ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}` (probe `:676-685`). -/
def BAProp5 (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Property 5, short form** `(prop:ThfadC_short)`, `σ₁ = σ₂` (probe `:687-695`). -/
def BAProp5s (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Bool, ∀ a : Zd d L,
          ‖BATheta d L g E m t σ σ 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))

/-- **Property 6** `(prop:BD1)` (probe `:697-706`). -/
def BAProp6 (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) - BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Property 7** `(prop:BD2)` (probe `:708-718`). -/
def BAProp7 (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) + BATheta d L g E m t σ₁ σ₂ 0 (a - r)
              - 2 * BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-- **Property 8** `(prop:ThfadC0)` (probe `:720-727`). -/
def BAProp8 (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

end PTPins

/-! ## 4. Target 4: `≺` at a law parameter (T2173a, DECISIONS §57 (3)) -/

/-- `≺` of the chain at an arbitrary law `μ` on the common sample space (`Prec sz` is the case `μ = seqP sz`;
the block Anderson law is `seqP (sz.withLam 0)`). -/
def PrecL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*} (ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ) : Prop :=
  StochDomAt μ sz.size ξ ζ

/-! ## 5. Statement shapes at concrete data (no proof obligation) -/

-- D472 at `(d, L, W) = (3, 4, 2)` (`N = 512`, 8 points per block)
example : Prop := BASelf_iff_fine_stmt 3 4 2
example : Prop := BAMres_fine_kron_stmt 3 4 2
example : Prop := BAMres_fine_apply_stmt 3 4 2
example : Prop := BAfine_trace_stmt 3 4 2
example : Prop := BASelfFine 3 4 2 10 Complex.I (BAm 3 4 10 Complex.I)
-- the PT pins at `Λ = 10` and the `κ` of the merged flow point `P` (`FlowPt 4 10`)
example : Prop := BAProp5 3 10 (RBM.BA.MFixedPointInst.P).m0.im
example : Prop := BAProp6 3 10 (RBM.BA.MFixedPointInst.P).m0.im (1 / 2)
-- the block Anderson law as the parameter of `≺` along the merged sequence `sz0`
example : Prop :=
  PrecL RBM.Gauss.SizesInst.sz0 (Sizes.seqP (Sizes.withLam RBM.Gauss.SizesInst.sz0 0)) (U := fun _ => Unit)
    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ))

end RBM.BA.T2197Check

end
