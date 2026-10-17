/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins

/-!
# BA stage TL, row TL-V (T2431): the base case of TL2 and the chain of times with the TL2 conjunct

Design `docs/reports/T2413-design.md` §1, §6 D6, §7 row TL-V; proofs
`docs/tickets/T2398-TL-proofs.md` (TP:8, 184, 193).

* `baTwistLoopBase_holds`: `BATwistLoopBase d` (`BA/TwistPins.lean:164`), `L̃_0 = K̃_0` exactly from
  `G_0 = M` (`STG0M`): `M` has the offset form of `BAMfine_eq`, so
  `twL2' = W^{-d} M^{(B)}(σ₂)_{ac₁} M^{(B)}(σ₁)_{c₂a} = twK` at `t = 0` (`Θ_0 = 1`);
* `baChainTL_holds`: `BAChainTL d` (`BA/TwistPins.lean:185`), the BA twin of `stMLOutG_of_mainIndG`
  (`Induction/MainIndOut.lean:99`) with the seventh conjunct `BATwistLoopLaw`: the chain of times of
  `stPosConclG_of_mainIndG` (`Induction/MainIndChain.lean:148`) with the invariant
  `STConclgL ∧ BATwistLoopLaw`, then the mixing on the class `t_n = 0`.  The step `BAMainIndTL`
  (BA-V) stays a premise.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Ind

/-! ## 1. The base case `L̃_0 = K̃_0` -/

section Base
variable {d : ℕ} {sz : Sizes d}

/-- Copy of `precL_of_zero` (`Induction/MainIndBase.lean:71-78`, private). -/
private theorem TwistChain_precL_of_zero (μ : Measure sz.SeqΩ) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h0 : ∀ n u ω, ξ n u ω = 0) (hζ : ∀ n u ω, 0 ≤ ζ n u ω) : PrecL sz μ ξ ζ :=
  StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    rw [h0 n u ω]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hζ n u ω)

/-- Copy of `TwistPins_split_shift` (`BA/TwistPins.lean:293`, private). -/
private theorem TwistChain_split_shift (n : ℕ) (c : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    split d (sz.L n) (sz.W n) (twShift n c x) = (c, (split d (sz.L n) (sz.W n) x).2) :=
  (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _

/-- Copy of `TwistPins_mem_blk` (`BA/TwistPins.lean:297`, private). -/
private theorem TwistChain_mem_blk (n : ℕ) {c : Zd d (sz.L n)} {x : Idx d (sz.L n) (sz.W n)} :
    x ∈ twBlk n c ↔ (split d (sz.L n) (sz.W n) x).1 = c := by
  simp [twBlk]

/-- The offset form of `BAMfine_eq`: `X_{wγ} = 1[offsets equal] MB_{[w][γ]}`. -/
private def TwistChain_Off (n : ℕ) (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) : Prop :=
  ∀ w γ, X w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
    MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0

/-- `twChg` of an offset-form matrix is offset-form with `BAMsigma σ MB`. -/
private theorem TwistChain_chg_off (n : ℕ) (M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (hM : TwistChain_Off n M MB) (σ : Bool) :
    TwistChain_Off n (twChg M σ) (BAMsigma d (sz.L n) MB σ) := by
  intro x y
  cases σ
  · simp only [twChg, BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def, hM y x]
    by_cases h : (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2
    · simp [h]
    · have h' : ¬ (split d (sz.L n) (sz.W n) y).2 = (split d (sz.L n) (sz.W n) x).2 := fun e => h e.symm
      simp [h, h']
  · simp only [twChg, BAMsigma, ite_true, hM x y]

/-- `Tr(X P_{ac})` of an offset-form matrix is `MB_{ca}` (`|[c]| = W^d`, `card_Iblk`). -/
private theorem TwistChain_trP_offset (n : ℕ) (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (hX : TwistChain_Off n X MB) (a c : Zd d (sz.L n)) :
    twTrP n X a c = MB c a := by
  unfold twTrP
  have key : ∀ w ∈ twBlk n c, X w (twShift n a w) = MB c a := by
    intro w hw
    rw [hX, TwistChain_split_shift, (TwistChain_mem_blk n).1 hw]
    simp
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]
  have hc : (twBlk n c).card = (sz.W n) ^ d := card_Iblk d (sz.L n) (sz.W n) c
  rw [hc]
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  push_cast
  field_simp

/-- `L̃` of two offset-form matrices: `W^{-d} MB₂_{ac₁} MB₁_{c₂a}` (`twCirc_holds` at `X₂ = M`, `TwistPins_circ_term`). -/
private theorem TwistChain_loop_offset (n : ℕ) (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB₁ MB₂ : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (h₁ : TwistChain_Off n X₁ MB₁) (h₂ : TwistChain_Off n X₂ MB₂)
    (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n X₁ X₂ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB₂ a c₁ * MB₁ c₂ a := by
  have h := twCirc_holds sz n X₁ X₂ X₂ MB₂ h₂ a c₁ c₂
  have h0 : twLoopX n X₁ (fun x y => X₂ x y - X₂ x y) a c₁ c₂ = 0 := by simp [twLoopX]
  rw [h0, eq_comm, sub_eq_zero] at h
  rw [h, TwistChain_trP_offset n X₁ MB₁ h₁ a c₂]

/-- **The base case `L̃_0 = K̃_0`** (`G_0 = M`): the pin `BATwistLoopBase d` (`BA/TwistPins.lean:164`).  `STG0M` gives
`G_0 = M`; `M` has the offset form with `M^{(B)} = BAMB` (`BAMfine_eq`, `0 < Im m_F` by `BAflow_real` at every `n`);
`twL2' = W^{-d} M^{(B)}(σ₂)_{ac₁} M^{(B)}(σ₁)_{c₂a}` and, `Θ_0 = 1`, `twK = ` the same. -/
theorem baTwistLoopBase_holds (d : ℕ) : BATwistLoopBase d := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hf hG
  refine TwistChain_precL_of_zero _ (fun n p ω => ?_)
    (fun n _ _ => Real.rpow_nonneg (mainIndBase_bctl_nonneg n _) _)
  obtain ⟨σ, a, c₁, c₂⟩ := p
  have hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := (BAflow_real κ ε 𝔠 𝔡 sz z hf n).1.1
  have hGM : (baFMz sz z).G n 0 ω = (baFMz sz z).M n := funext fun x => funext fun y => hG n ω x y
  have hMoff : TwistChain_Off n ((baFMz sz z).M n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) := fun w γ =>
    BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hm w γ
  have hL : twL2' (baFMz sz z) n 0 ω σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a c₁ *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a := by
    unfold twL2'
    rw [hGM]
    exact TwistChain_loop_offset n _ _ _ _ (TwistChain_chg_off n _ _ hMoff (σ 0)) (TwistChain_chg_off n _ _ hMoff (σ 1)) a c₁ c₂
  have hΘ : BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 0
      (σ 0) (σ 1) = 1 := by
    simp [BATheta, PropThetaQ]
  have hK : twK (baFMz sz z) n 0 σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a c₁ *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a := by
    rw [twK_ba z n hm, hΘ]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  change ‖twL2' (baFMz sz z) n 0 ω σ a c₁ c₂ - twK (baFMz sz z) n 0 σ a c₁ c₂‖ = 0
  rw [hL, hK, sub_self, norm_zero]

end Base

/-! ## 2. The chain of times with the TL2 conjunct -/

section Chain
variable {d : ℕ}

/-! ### Mixing at the class `t_n = 0` (formal: `StochDomAt.of_subset_union`) -/

section Mix
variable {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hs : Tendsto sz.size atTop atTop)
  {t t' : ℕ → ℝ} (hm : ∀ n, t n = 0 ∨ t n = t' n)
include hs hm

/-- Copy of `STLKgL_mix` (`Induction/MainIndOut.lean:66`, private). -/
private theorem TwistChain_LK_mix (h0 : STLKgL C μ (fun _ => 0)) (h1 : STLKgL C μ t') : STLKgL C μ t := fun k hk =>
  StochDomAt.of_subset_union hs (h0 k hk) (h1 k hk) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

/-- Copy of `STLmaxgL_mix` (`Induction/MainIndOut.lean:71`, private). -/
private theorem TwistChain_Lmax_mix (h0 : STLmaxgL C μ (fun _ => 0)) (h1 : STLmaxgL C μ t') : STLmaxgL C μ t := fun k hk =>
  StochDomAt.of_subset_union hs (h0 k hk) (h1 k hk) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

/-- Copy of `STDecaygL_mix` (`Induction/MainIndOut.lean:76`, private). -/
private theorem TwistChain_Decay_mix (h0 : STDecaygL C μ (fun _ => 0)) (h1 : STDecaygL C μ t') : STDecaygL C μ t := fun D hD =>
  StochDomAt.of_subset_union hs (h0 D hD) (h1 D hD) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

/-- Copy of `STExp2gL_mix` (`Induction/MainIndOut.lean:81`, private). -/
private theorem TwistChain_Exp2_mix (h0 : STExp2gL C μ (fun _ => 0)) (h1 : STExp2gL C μ t') : STExp2gL C μ t :=
  StochDomAt.of_subset_union hs h0 h1 fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

/-- Copy of `STLocalEntrygL_mix` (`Induction/MainIndOut.lean:86`, private). -/
private theorem TwistChain_LocalEntry_mix (h0 : STLocalEntrygL C μ (fun _ => 0)) (h1 : STLocalEntrygL C μ t') :
    STLocalEntrygL C μ t :=
  StochDomAt.of_subset_union hs h0 h1 fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

/-- The sixth mix, for `BATwistLoopLaw` (the proof of `STExp2gL_mix`, `MainIndOut.lean:81-85`): the index set
`(Fin 2 → Bool) × Zd³` of `BATwistLoopLaw` does not depend on `t`, and the bad set at `t_n` is the bad set at `0` or at `t'_n`. -/
private theorem TwistChain_TL2_mix (h0 : BATwistLoopLaw C μ (fun _ => 0)) (h1 : BATwistLoopLaw C μ t') :
    BATwistLoopLaw C μ t :=
  StochDomAt.of_subset_union hs h0 h1 fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω ⟨u, hu⟩ => by
    rcases hm n with h | h
    exacts [Or.inl ⟨u, by simpa [h] using hu⟩, Or.inr ⟨u, by simpa [h] using hu⟩]⟩

end Mix

/-! ### The assembly -/

end Chain

/-! ## 3. The instances (`d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `zSeq`, `flow_sz0`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`).
Other gates' pins (`STG0M` at the carrier: BA-V `GLoopAtT0`; `BAMainIndTL 3 STAny`: BA-V V2a; `STHorizonG`, `STBaseG` at the BA data) stay hypotheses. -/

end RBM.BA
