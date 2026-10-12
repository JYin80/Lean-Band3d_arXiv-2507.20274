/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.StepDecompGen
import RBM3D.Induction.GridDriftN

/-!
# The hierarchy algebra, the hierarchy identity and the grid drift over the carrier

BA-T row T5s2b (ticket T2474, targets 6-11).  Additive generic forms of
`Induction/HierAlgebra.lean`, `Induction/HierarchyN.lean` and `Induction/GridDriftN.lean` (none is
edited) over a carrier `Cm : Step2Mat sz`, on the kernel `Cm.S n` and the classes of
`Chain/StepDecompGen.lean`.

* **Algebra** (target 6): `primBilS`, `primRhsS_split`, `norm_primBilS_le` (kernel `S`, premise
  `∀ a, Σ_b ‖S a b‖ ≤ 1`); `STllPairNg`; the classes `HierDriftGen_KLoop`, `HierDriftGen_KTwo`
  (class (t): the `l = 2` coupling of `𝒦` is `Step2Gen_ThetaN`); `loopDrift_sub_K_deriv_ng`.
* **Hierarchy** (target 7): `HierarchyNg`, `hierarchyNg_of` (from T5s1's `loopGenNOf`).
* **Grid drift** (targets 8-9): `stepErrNg`, `GridDriftNg`, the classes `HierDriftGen_Expand`,
  `HierDriftGen_UStep`, `gridDriftNg_at`, `gridDriftNg`.  Besides the pinned classes they take
  the link `HierDriftGen_KLink` (`Cm.KI ∘ KLloopOf = Cm.K`): `predIncNg` reads the `K` field and
  the `𝒦`-step the `KI` field (prove report, section (a')).
* **Envelopes** (target 10): `HierDriftGen_exists_envelope`, `exists_norm_KI_le_wing`.

Band discharges of every class (`hierDriftGen_*_band`) and re-derivations of the band statements
are proved here, and compiled nonempty instances are in the last section.  Private band helpers
are reused by `open private`; the ones that read `SB`, `KLK`, `treeEqRhs`, `Ugen`, `uKer` are
copied under the stem `HierDriftGen_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private HierAlgebra_two_le_length_cutGlueL HierAlgebra_two_le_length_cutGlueR
  HierAlgebra_length_cutGlueL_lt HierAlgebra_couplingLen_eq_ksimLK from RBM3D.Induction.HierAlgebra

open private gdnTens gdnGen gdn_tens_step_le gdn_time_facts gdn_algebra gdn_loopOf_wf gdn_loopOf_length
  gdn_loopOf_eq gdn_row_UG gdn_thetaKer_eq gdn_Bctl_le gdn_Bctl_nonneg from RBM3D.Induction.GridDriftN

noncomputable section

namespace RBM.BA

open Finset MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal
open RBM.Ind (kStepC uStepC)

/-! ### 1. The polarization of `treeEqRhsS` and the coupling algebra (target 6)

Copies of `HierAlgebra.lean:41-310` with the kernel `SB d L g` replaced by an arbitrary matrix `S`
(`HierAlgebra_two_le_length_cutGlueL`, `_R`, `HierAlgebra_length_cutGlueL_lt` are `S`-free and reused by `open private`);
`norm_primBilS_le` needs the row-sum bound `Σ_b ‖S a b‖ ≤ 1` in place of `Σ_b ‖SB a b‖ = 1`. -/

section Bilinear

variable (d L : ℕ) [NeZero L] (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ)

/-- The polarization of `treeEqRhs`: the same sum with independent left and right factors
(`HA:45`, `W^2 → W^d`). -/
def primBilS (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    K (I.cutGlueL k l a) * S a b * K' (I.cutGlueR k l b)

@[simp] theorem HierDriftGen_primBilS_self (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBilS d L W S K K I = treeEqRhsS d L W S K I := rfl

theorem HierDriftGen_primBilS_add_left (K₁ K₂ K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBilS d L W S (K₁ + K₂) K' I = primBilS d L W S K₁ K' I + primBilS d L W S K₂ K' I := by
  simp only [primBilS, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem HierDriftGen_primBilS_add_right (K K₁ K₂ : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBilS d L W S K (K₁ + K₂) I = primBilS d L W S K K₁ I + primBilS d L W S K K₂ I := by
  simp only [primBilS, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem HierDriftGen_primBilS_add_add (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBilS d L W S (K + D) (K + D) I
      = primBilS d L W S K K I + primBilS d L W S K D I + primBilS d L W S D K I
        + primBilS d L W S D D I := by
  rw [HierDriftGen_primBilS_add_left, HierDriftGen_primBilS_add_right, HierDriftGen_primBilS_add_right]
  ring

/-- The loop hierarchy and the primitive equation (`pro_dyncalK`) share their quadratic term
`treeEqRhs`, so their difference (`eq_L-Keee`, `3_5:73`) has exactly three summands: the two
couplings `[𝒦 ∼ (𝓛-𝒦)]` (`DefKsimLK`, `3_5:89`) and `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` (`def_ELKLK`,
`3_5:97`) (`HA:70`). -/
theorem HierDriftGen_primRhsS_sub (Lf K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    treeEqRhsS d L W S Lf I - treeEqRhsS d L W S K I
      = primBilS d L W S K (Lf - K) I + primBilS d L W S (Lf - K) K I
        + primBilS d L W S (Lf - K) (Lf - K) I := by
  set D : LoopIdx (Zd d L) → ℂ := Lf - K with hD
  have hLf : Lf = K + D := by
    rw [hD]
    funext x
    simp
  have h1 : treeEqRhsS d L W S Lf I = primBilS d L W S (K + D) (K + D) I := by
    rw [← HierDriftGen_primBilS_self, hLf]
  rw [h1, HierDriftGen_primBilS_add_add, ← HierDriftGen_primBilS_self d L W S K I]
  ring

/-- The part of the coupling in which the *left* factor is a loop of length `lK` (`HA:85`). -/
def HierDriftGen_primBilLenS (lK : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (if (I.cutGlueL k l a).length = lK then
      K (I.cutGlueL k l a) * S a b * K' (I.cutGlueR k l b) else 0)

/-- The coupling `primBilS F G` graded by the length of the **right** factor (`HA:91`). -/
def HierDriftGen_primBilLenRS (lK : ℕ) (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (if (I.cutGlueR k l b).length = lK then
      F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b) else 0)

/-- `[𝒦 ∼ (𝓛-𝒦)]^{l_K}` (`DefKsimLK`, `3_5:89`) with `D = 𝓛 - 𝒦`: both orientations, graded by
the length `l_K` of the `𝒦` loop (`HA:98`). -/
def HierDriftGen_couplingLenS (lK : ℕ) (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  HierDriftGen_primBilLenS d L W S lK K D I + HierDriftGen_primBilLenRS d L W S lK D K I

/-- Summing the graded pieces over every possible `l_K` recovers the whole coupling
(`HA:131`). -/
theorem HierDriftGen_sum_primBilLenS (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, HierDriftGen_primBilLenS d L W S lK K K' I = primBilS d L W S K K' I := by
  simp only [HierDriftGen_primBilLenS, primBilS, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq (Finset.range N) ((I.cutGlueL k l a).length)
    (fun _ => K (I.cutGlueL k l a) * S a b * K' (I.cutGlueR k l b)),
    ite_eq_left (Finset.mem_range.mpr (lt_of_lt_of_le (HierAlgebra_length_cutGlueL_lt d L I hk hl a) hN))]

theorem HierDriftGen_sum_primBilLenRS (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, HierDriftGen_primBilLenRS d L W S lK F G I = primBilS d L W S F G I := by
  simp only [HierDriftGen_primBilLenRS, primBilS, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hlen : (I.cutGlueR k l b).length < N := by
    rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]; omega
  rw [Finset.sum_ite_eq (Finset.range N) ((I.cutGlueR k l b).length)
    (fun _ => F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b)),
    ite_eq_left (Finset.mem_range.mpr hlen)]

/-- Summing over every `l_K` gives the whole coupling:
`∑_{l_K} [𝒦 ∼ (𝓛-𝒦)]^{l_K} = primBilS K D + primBilS D K` (`HA:171`). -/
theorem HierDriftGen_sum_couplingLenS (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, HierDriftGen_couplingLenS d L W S lK K D I
      = primBilS d L W S K D I + primBilS d L W S D K I := by
  simp only [HierDriftGen_couplingLenS, Finset.sum_add_distrib]
  rw [HierDriftGen_sum_primBilLenS d L W S K D I hN, HierDriftGen_sum_primBilLenRS d L W S D K I hN]

/-- Both graded couplings vanish outside `2 ≤ lK ≤ I.length` (`HA:178`). -/
theorem HierDriftGen_couplingLenS_eq_zero_outside (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {lK : ℕ} (hlK : lK < 2 ∨ I.length < lK) :
    HierDriftGen_couplingLenS d L W S lK K D I = 0 := by
  have hzeroL : HierDriftGen_primBilLenS d L W S lK K D I = 0 := by
    unfold HierDriftGen_primBilLenS
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right]
    intro hcontra
    rcases hlK with h | h
    · have := HierAlgebra_two_le_length_cutGlueL d L I a hk.1 hl.1 hl.2
      omega
    · have := LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2
      omega
  have hzeroR : HierDriftGen_primBilLenRS d L W S lK D K I = 0 := by
    unfold HierDriftGen_primBilLenRS
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right]
    intro hcontra
    rcases hlK with h | h
    · have := HierAlgebra_two_le_length_cutGlueR d L I b hk.1 hl.1 hl.2
      omega
    · have := LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2
      omega
  rw [HierDriftGen_couplingLenS, hzeroL, hzeroR, add_zero]

/-- The split of `treeEqRhs (K + D) - treeEqRhs K` into the `l_K = 2` coupling, the `l_K ≥ 3`
couplings and the quadratic term `primBilS D D` (`eq_L-Keee` `3_5:73`, `DefKsimLK` `3_5:89`,
`def_ELKLK` `3_5:97`); the only hypothesis is `2 ≤ n` (`HA:214`). -/
theorem primRhsS_split (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    (hn : 2 ≤ I.length) :
    treeEqRhsS d L W S (K + D) I - treeEqRhsS d L W S K I
      = HierDriftGen_couplingLenS d L W S 2 K D I
        + (∑ lK ∈ Finset.Icc 3 I.length, HierDriftGen_couplingLenS d L W S lK K D I)
        + primBilS d L W S D D I := by
  have hDeq : (K + D) - K = D := by funext x; simp
  have hps := HierDriftGen_primRhsS_sub d L W S (K + D) K I
  rw [hDeq] at hps
  have hN : I.length + 2 ≤ I.length + 2 := le_rfl
  have hsum := HierDriftGen_sum_couplingLenS d L W S K D I hN
  have h2mem : (2 : ℕ) ∈ Finset.range (I.length + 2) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h2mem] at hsum
  have hsub : Finset.Icc 3 I.length ⊆ (Finset.range (I.length + 2)).erase 2 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hsum2 : ∑ lK ∈ (Finset.range (I.length + 2)).erase 2, HierDriftGen_couplingLenS d L W S lK K D I
      = ∑ lK ∈ Finset.Icc 3 I.length, HierDriftGen_couplingLenS d L W S lK K D I := by
    symm
    refine Finset.sum_subset hsub (fun x hx hnx => ?_)
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hnx
    exact HierDriftGen_couplingLenS_eq_zero_outside d L W S K D I (by omega)
  rw [hsum2] at hsum
  rw [hps, ← hsum]

/-- **`norm_primBilS_le`, `d`-dimensional form** (RBM2D `HA:252` with `W² → W^d`,
`L² → L^d = card (Zd d L)`): `primBilS F G I` is bounded by the product of separate envelopes
`BF, BG` on `F, G` at the cut sub-loop lengths `2 … I.length`, with the constant
`W^d n² L^d B_F B_G`. -/
theorem norm_primBilS_le (hS : ∀ a : Zd d L, ∑ b : Zd d L, ‖S a b‖ ≤ 1) (F G : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hI : I.WF) {BF BG : ℝ} (hBF0 : 0 ≤ BF) (hBG0 : 0 ≤ BG)
    (hBF : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ BF)
    (hBG : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ BG) :
    ‖primBilS d L W S F G I‖ ≤ (W : ℝ) ^ d * (I.length : ℝ) ^ 2 * (L : ℝ) ^ d * BF * BG := by
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ d := by positivity
  have hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖∑ a : Zd d L, ∑ b : Zd d L,
          F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b)‖
        ≤ (L : ℝ) ^ d * BF * BG := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hBFl : ∀ a : Zd d L, ‖F (I.cutGlueL k l a)‖ ≤ BF := fun a =>
      hBF _ (LoopIdx.wf_cutGlueL I a hI hk.1 hl.1 hl.2)
        (HierAlgebra_two_le_length_cutGlueL d L I a hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
    have hBGr : ∀ b : Zd d L, ‖G (I.cutGlueR k l b)‖ ≤ BG := fun b =>
      hBG _ (LoopIdx.wf_cutGlueR I b hI hk.1 hl.1 hl.2)
        (HierAlgebra_two_le_length_cutGlueR d L I b hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
    calc ‖∑ a : Zd d L, ∑ b : Zd d L,
            F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b)‖
        ≤ ∑ a : Zd d L, ∑ b : Zd d L,
            ‖F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Zd d L, ∑ b : Zd d L, BF * BG * ‖S a b‖ := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul]
          calc ‖F (I.cutGlueL k l a)‖ * ‖S a b‖ * ‖G (I.cutGlueR k l b)‖
              ≤ BF * ‖S a b‖ * BG :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hBFl a) (norm_nonneg _)) (hBGr b)
                  (norm_nonneg _) (by positivity)
            _ = BF * BG * ‖S a b‖ := by ring
      _ ≤ ∑ _a : Zd d L, BF * BG := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_of_le_one_right (mul_nonneg hBF0 hBG0) (hS a)
      _ = (L : ℝ) ^ d * BF * BG := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          ring
  calc ‖primBilS d L W S F G I‖
      ≤ (W : ℝ) ^ d * ∑ _k ∈ Icc 1 I.length, ∑ _l ∈ Ioc _k I.length, (L : ℝ) ^ d * BF * BG := by
        rw [primBilS, norm_mul, norm_pow, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) ^ d * ∑ _k ∈ Icc 1 I.length, (I.length : ℝ) * ((L : ℝ) ^ d * BF * BG) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have hle : ((I.length - k : ℕ) : ℝ) ≤ (I.length : ℝ) := by
          exact_mod_cast Nat.sub_le I.length k
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (W : ℝ) ^ d * (I.length : ℝ) ^ 2 * (L : ℝ) ^ d * BF * BG := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

end Bilinear

/-! ### 2. The carrier pair term, the classes `KLoop`, `KTwo` and the drift identity (target 6) -/

section Drift

variable {d : ℕ} {sz : Sizes d}

/-- **The pair-cut term of the loop generator over the carrier**: `STllPairN` (`HierAlgebra:~790`) with the kernel `Cm.S n`
and the loop values `STLIMg`: `treeEqRhsS (Cm.S n) (STLIMg …)`. -/
def STllPairNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (STLIMg Cm n u M) I

/-- `STllPairN` is `STllPairNg` at `bandStep2Mat` (`STllPairN_eq_treeEqRhs`, `treeEqRhs_eq_treeEqRhsS`). -/
theorem bandStep2_STllPairN (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (I : LoopIdx (Zd d (sz.L n))) :
    sz.STllPairN n (E n) u M I = STllPairNg (bandStep2Mat sz E) n u M I := rfl

/-- **Target 6, class `HierDriftGen_KLoop`**: `𝒦` of the carrier solves the convolution tree equations with the carrier
kernel `Cm.S n` on `[0, 1)` (the merged `IsKLoopS`, `Loop/KLTree.lean:828`). -/
def HierDriftGen_KLoop (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∃ M0 : LoopIdx (Zd d (sz.L n)) → ℂ,
    IsKLoopS d (sz.L n) (sz.W n) (Cm.S n) (PropSpin (Cm.m n)) M0 (Set.Ico (0 : ℝ) 1) (Cm.KI n)

/-- **Target 6, class `HierDriftGen_KTwo`** (class (t), C6): the `l = 2` coupling of `𝒦_u` is `Θ^{(k)}_{u,σ}`
(`couplingLen_two_Kval_eq_thetaOp`, `HierAlgebra.lean:620`; band discharge below). -/
def HierDriftGen_KTwo (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∀ u ∈ Set.Ico (0 : ℝ) 1, ∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ),
    2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      STksimLKMg Cm n u H 2 (KLloopOf d (sz.L n) σ a) =
        Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u H (KLloopOf d (sz.L n) σ b)) a

/-- The graded coupling with `K = 𝒦_u` and `D = 𝓛 - 𝒦` is `STksimLKMg` (`HierAlgebra_couplingLen_eq_ksimLK`). -/
theorem HierDriftGen_couplingLenS_eq_ksim (Cm : Step2Mat sz) (n : ℕ) (u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    HierDriftGen_couplingLenS d (sz.L n) (sz.W n) (Cm.S n) l (Cm.KI n u) (STLKIMg Cm n u M) I =
      STksimLKMg Cm n u M l I := by
  simp only [HierDriftGen_couplingLenS, HierDriftGen_primBilLenS, HierDriftGen_primBilLenRS, STksimLKMg,
    Finset.sum_add_distrib, mul_add]
  ring

/-- **Target 6, `loopDrift_sub_K_deriv_ng`** (`loopDrift_sub_K_deriv_n`, `HierAlgebra.lean:729`, over the carrier): the
matrix-level drift-minus-`∂_u𝒦` identity, from `KLoop` (the equation `∂_u 𝒦 = treeEqRhsS 𝒦`), `KTwo` (the `l = 2`
coupling is `Θ`) and the polarization `primRhsS_split`. -/
theorem loopDrift_sub_K_deriv_ng (Cm : Step2Mat sz) (n : ℕ) (hK : HierDriftGen_KLoop Cm n)
    (hT : HierDriftGen_KTwo Cm n) :
    ∀ u ∈ Set.Ico (0 : ℝ) 1, ∀ (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ),
      2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (STLIMg Cm n u M) (KLloopOf d (sz.L n) σ a) +
              STegtMg Cm n u M (KLloopOf d (sz.L n) σ a)) -
            deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u =
          Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u M (KLloopOf d (sz.L n) σ b)) a +
            ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n u M (KLloopOf d (sz.L n) σ a) + STegtMg Cm n u M (KLloopOf d (sz.L n) σ a) := by
  intro u hu M k hk σ a
  obtain ⟨M0, hKL⟩ := hK
  have hwf : (KLloopOf d (sz.L n) σ a).WF := by simp [KLloopOf, LoopIdx.WF]
  have hlen : (KLloopOf d (sz.L n) σ a).length = k := by simp [KLloopOf, LoopIdx.length]
  have hprim := hKL.1 u hu (KLloopOf d (sz.L n) σ a) hwf (by rw [hlen]; exact hk)
  have hderiv : deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u =
      treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n u) (KLloopOf d (sz.L n) σ a) := hprim.deriv
  have hKD : Cm.KI n u + STLKIMg Cm n u M = STLIMg Cm n u M := by
    funext x
    simp [STLKIMg]
  have hsplit := primRhsS_split d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n u) (STLKIMg Cm n u M)
    (KLloopOf d (sz.L n) σ a) (by rw [hlen]; exact hk)
  rw [hKD, hlen, HierDriftGen_couplingLenS_eq_ksim, hT u hu M k hk σ a] at hsplit
  have hsum : ∑ l ∈ Finset.Icc 3 k, HierDriftGen_couplingLenS d (sz.L n) (sz.W n) (Cm.S n) l (Cm.KI n u)
        (STLKIMg Cm n u M) (KLloopOf d (sz.L n) σ a) =
      ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (KLloopOf d (sz.L n) σ a) :=
    Finset.sum_congr rfl fun l _ => HierDriftGen_couplingLenS_eq_ksim Cm n u M l _
  have hEl : primBilS d (sz.L n) (sz.W n) (Cm.S n) (STLKIMg Cm n u M) (STLKIMg Cm n u M)
      (KLloopOf d (sz.L n) σ a) = STelklkMg Cm n u M (KLloopOf d (sz.L n) σ a) := rfl
  rw [hsum, hEl] at hsplit
  rw [hderiv]
  linear_combination hsplit

end Drift

/-! ### 3. Band discharges of `KLoop`, `KTwo` and the band drift identity (target 6) -/

section BandDrift

variable {d : ℕ}

/-- **Band discharge of `HierDriftGen_KLoop`**: `KLK_isKLoop` (`KLTreeDeriv.lean:1049`) through `IsKLoop_iff_IsKLoopS`
(`mSigma E = PropSpin (mE E)` and `SB d L g` by unfolding). -/
theorem hierDriftGen_kLoop_band (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) (n : ℕ) :
    HierDriftGen_KLoop (bandStep2Mat sz E) n :=
  ⟨_, (IsKLoop_iff_IsKLoopS d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) (Set.Ico (0 : ℝ) 1) _).1
    (KLK_isKLoop d (sz.L n) (sz.W n) (sz.lam n) (E n) (sz.three_le_L n) (sz.W_pos n) (hE n))⟩

/-- **Band discharge of `HierDriftGen_KTwo`**: `couplingLen_two_Kval_eq_thetaOp` (`HierAlgebra.lean:620`), the identity
`HierDriftGen_couplingLenS_eq_ksim` and `Step2Kern_ThetaN_band`. -/
theorem hierDriftGen_kTwo_band (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) (n : ℕ) :
    HierDriftGen_KTwo (bandStep2Mat sz E) n := by
  intro u hu H k hk σ a
  rw [← HierDriftGen_couplingLenS_eq_ksim]
  have h := RBM.Ind.couplingLen_two_Kval_eq_thetaOp d (sz.L n) (sz.W n) (sz.lam n) (sz.three_le_L n) (E n)
    (hE n).le u hu.1 hu.2 (STLKIMg (bandStep2Mat sz E) n u H) hk σ a
  have e := Step2Kern_ThetaN_band sz E n k σ u (fun v => STLKIMg (bandStep2Mat sz E) n u H (loopOf σ v))
  exact h.trans (congrFun e a).symm

/-- **Band: `loopDrift_sub_K_deriv_n`** (`HierAlgebra.lean:729`) from `loopDrift_sub_K_deriv_ng`. -/
theorem hierDriftGen_band_loopDrift (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) (n : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    (sz.STllPairN n (E n) u M (loopOf σ a) + sz.STegtM n (E n) u M (loopOf σ a)) -
        deriv (fun v : ℝ => sz.STKloop n (E n) v σ a) u =
      RBM.ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) u
          (fun b => sz.STLKIM n (E n) u M (loopOf σ b)) a +
        ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) u M l (loopOf σ a) +
        sz.STelklkM n (E n) u M (loopOf σ a) + sz.STegtM n (E n) u M (loopOf σ a) := by
  have h := loopDrift_sub_K_deriv_ng (bandStep2Mat sz E) n (hierDriftGen_kLoop_band sz E hE n)
    (hierDriftGen_kTwo_band sz E hE n) u ⟨hu0, hu1⟩ M k hk σ a
  have hfm : (bandStep2Mat sz E).toFlowFM = bandFM sz E := rfl
  rw [hfm, Step2Kern_ThetaN_band] at h
  exact h

end BandDrift

/-! ### 4. The hierarchy identity over the carrier (target 7) -/

section Hierarchy

variable {d : ℕ} {sz : Sizes d}

/-- **Target 7, `HierarchyNg`**: `HierarchyN` (`HierarchyN.lean:56`) over the carrier; the generator is T5s1's `genMatOf`
(`LoopGenN.lean:554`) at the walk coupling `g n`, the one-loop value `Cm.m n` and the energy `E n`. -/
def HierarchyNg (Cm : Step2Mat sz) (E g : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) -
            deriv (fun v : ℝ => Cm.KI n v (KLloopOf d (sz.L n) σ a)) u =
          Step2Gen_ThetaN Cm.toFlowFM n σ u (fun b => STLKIMg Cm n u M (KLloopOf d (sz.L n) σ b)) a +
            ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u M l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n u M (KLloopOf d (sz.L n) σ a) + STegtMg Cm n u M (KLloopOf d (sz.L n) σ a)

/-- **Target 7, `hierarchyNg_of`**: the hierarchy identity over the carrier, from `loopGenNOf` (T5s1) and
`loopDrift_sub_K_deriv_ng`, under `LoopForm`, the walk's variance law `Cm.S n = SB d (sz.L n) (g n)`, `KLoop`, `KTwo`. -/
theorem hierarchyNg_of (Cm : Step2Mat sz) (E g : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E)
    (hS : ∀ n, Cm.S n = SB d (sz.L n) (g n)) (hK : ∀ n, HierDriftGen_KLoop Cm n)
    (hT : ∀ n, HierDriftGen_KTwo Cm n) : HierarchyNg Cm E g := by
  intro n u hu0 hu1 M hM k hk σ a
  have hgen := RBM.Ind.loopGenNOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) (sz.three_le_L n) (hL n).1 u hu1 M hM σ a
  have hpair : RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) =
      treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (STLIMg Cm n u M) (KLloopOf d (sz.L n) σ a) +
        STegtMg Cm n u M (KLloopOf d (sz.L n) σ a) := by
    refine hgen.trans ?_
    simp only [treeEqRhsS, STegtMg, STavgErrMg, STmsigg, STLIMg, (hL n).2.2.1 u M, hS n, PropSpin]
    rfl
  rw [hpair]
  exact loopDrift_sub_K_deriv_ng Cm n (hK n) (hT n) u ⟨hu0, hu1⟩ M k hk σ a

/-- **Target 7, band re-derivation**: `HierarchyN d` (`HierarchyN.lean:56`) from `hierarchyNg_of` at `bandStep2Mat`,
`g = sz.lam`, `m = mE E`. -/
theorem hierarchyN_of_Ng (d : ℕ) : RBM.Ind.HierarchyN d := by
  intro sz n E hE u hu0 hu1 M hM k hk σ a
  have h := hierarchyNg_of (bandStep2Mat sz (fun _ => E)) (fun _ => E) sz.lam
    (stepDecompGen_loopForm_band sz (fun _ => E) (fun _ => hE)) (fun n => rfl)
    (hierDriftGen_kLoop_band sz (fun _ => E) (fun _ => hE)) (hierDriftGen_kTwo_band sz (fun _ => E) (fun _ => hE))
    n u hu0 hu1 M hM k hk σ a
  have hfm : (bandStep2Mat sz (fun _ => E)).toFlowFM = bandFM sz (fun _ => E) := rfl
  rw [hfm, Step2Kern_ThetaN_band] at h
  exact h

end Hierarchy

/-! ### 5. One step of `𝒦` over a kernel `S` and a value family `KI` (target 9)

Copies of `GridDriftN.lean:497-646` (`gdn_K_lip`, `gdn_K_step`) with `KLK d L g W E` replaced by an arbitrary family
`KI : ℝ → LoopIdx → ℂ` solving `∂_t KI_t = treeEqRhsS S KI_t` on `[0, 1)` (the content of `HierDriftGen_KLoop`), and `SB d L g` by `S` with row sums `≤ 1`. -/

section KStep

variable {d L W : ℕ} [NeZero L] {S : Matrix (Zd d L) (Zd d L) ℂ} {KI : ℝ → LoopIdx (Zd d L) → ℂ}

/-- The `𝒦` family is Lipschitz in time with constant `W^d k² L^d B²` on `[0, v]` (uses the
derivative bound `‖treeEqRhsS (𝒦_w)(J)‖ ≤ W^d k² L^d B²`, `norm_primBilS_le`; RBM1D `norm_Kgen_sub_le`,
`Gauss/Lemma514Holder.lean:269` at `c06b103`; RBM2D `gdn_K_lip`, `GDN:461`, with the `d`-dimensional
constant). -/
theorem HierDriftGen_K_lip (hS : ∀ a : Zd d L, ∑ b : Zd d L, ‖S a b‖ ≤ 1)
    (hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => KI s J) (treeEqRhsS d L W S (KI t) J) t) {v : ℝ} (hv1 : v < 1)
    {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ w ∈ Set.Icc (0 : ℝ) (v), ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KI w J‖ ≤ B)
    {J : LoopIdx (Zd d L)} (hJ : J.WF) (h2 : 2 ≤ J.length) (hk : J.length ≤ k)
    {u : ℝ} (hu : 0 ≤ u) :
    ∀ r ∈ Set.Icc u v, ‖KI r J - KI u J‖ ≤
      ((W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B ^ 2) * (r - u) := by
  have hbound : ∀ r ∈ Set.Icc u v,
      ‖treeEqRhsS d L W S (KI r) J‖ ≤ (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B ^ 2 := by
    intro r hr
    rw [← HierDriftGen_primBilS_self]
    have hr' : r ∈ Set.Icc (0 : ℝ) v := ⟨hu.trans hr.1, hr.2⟩
    have h1 := norm_primBilS_le d L W S hS (KI r) (KI r) J hJ hB0 hB0
      (fun J' hJ' h2' hk' => hB r hr' J' hJ' h2' (hk'.trans hk))
      (fun J' hJ' h2' hk' => hB r hr' J' hJ' h2' (hk'.trans hk))
    have hkk : (J.length : ℝ) ≤ k := by exact_mod_cast hk
    have hJ0 : (0 : ℝ) ≤ J.length := Nat.cast_nonneg _
    calc _ ≤ _ := h1
      _ ≤ (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B * B := by gcongr
      _ = _ := by ring
  intro r hr
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := r)
    (f := fun s => KI s J)
    (f' := fun s => treeEqRhsS d L W S (KI s) J)
    (C := (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B ^ 2)
    (fun x hx => (hder x ⟨hu.trans hx.1, lt_of_le_of_lt (hx.2.trans hr.2) hv1⟩ J hJ h2).hasDerivWithinAt)
    (fun x hx => hbound x ⟨hx.1, hx.2.le.trans hr.2⟩) r ⟨hr.1, le_rfl⟩
  exact hres

/-- **One step of `𝒦`** (RBM1D `K_step_n`, `Gauss/GridHierarchyN.lean:342` at `c06b103`; RBM2D
`gdn_K_step`, `GDN:493`, with the `d`-dimensional constants `W^d k² L^d = N k²`): for
`0 ≤ Δ ≤ 1`, `u + Δ < 1`, on the envelope `B`,
`‖𝒦_{u+Δ}(I) - 𝒦_u(I) - Δ ∂_u𝒦_u(I)‖ ≤ kStepC d L W k B Δ²`. -/
theorem HierDriftGen_K_step (hS : ∀ a : Zd d L, ∑ b : Zd d L, ‖S a b‖ ≤ 1)
    (hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => KI s J) (treeEqRhsS d L W S (KI t) J) t) {u Δ : ℝ}
    (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hv1 : u + Δ < 1) {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (u + Δ), ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KI w J‖ ≤ B) {I : LoopIdx (Zd d L)} (hI : I.WF) (h2 : 2 ≤ I.length)
    (hk : I.length = k) :
    ‖KI (u + Δ) I - KI u I -
        (Δ : ℂ) * treeEqRhsS d L W S (KI u) I‖ ≤ kStepC d L W k B * Δ ^ 2 := by
  set c : ℝ := (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d with hc
  have hc0 : 0 ≤ c := by positivity
  set D1 : ℝ := c * B ^ 2 with hD1
  have hD10 : 0 ≤ D1 := by positivity
  set C0 : ℂ := treeEqRhsS d L W S (KI u) I with hC0
  have hkI : (I.length : ℝ) = k := by exact_mod_cast hk
  -- the derivative bound
  have hbound : ∀ r ∈ Set.Ico u (u + Δ),
      ‖treeEqRhsS d L W S (KI r) I - C0‖ ≤ 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2 := by
    intro r hr
    have hr' : r ∈ Set.Icc u (u + Δ) := ⟨hr.1, hr.2.le⟩
    have hrB : r ∈ Set.Icc (0 : ℝ) (u + Δ) := ⟨hu0.trans hr.1, hr.2.le⟩
    have hδ : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖(KI r - KI u) J‖ ≤ D1 * (r - u) := by
      intro J hJ hJ2 hJk
      exact HierDriftGen_K_lip hS hder hv1 hB0 hB hJ hJ2 (hJk.trans hk.le) hu0 r hr'
    have hδ0 : 0 ≤ D1 * (r - u) := mul_nonneg hD10 (by linarith [hr.1])
    have hKu : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖KI u J‖ ≤ B := fun J hJ hJ2 hJk =>
      hB u ⟨hu0, by linarith⟩ J hJ hJ2 (hJk.trans hk.le)
    have hsub := HierDriftGen_primRhsS_sub d L W S (KI r) (KI u) I
    have e1 := norm_primBilS_le d L W S hS (KI u) (KI r - KI u)
      I hI hB0 hδ0 hKu hδ
    have e2 := norm_primBilS_le d L W S hS (KI r - KI u) (KI u)
      I hI hδ0 hB0 hδ hKu
    have e3 := norm_primBilS_le d L W S hS (KI r - KI u)
      (KI r - KI u) I hI hδ0 hδ0 hδ hδ
    rw [hkI, ← hc] at e1 e2 e3
    have hrΔ : r - u ≤ Δ := by linarith [hr.2]
    have hru : 0 ≤ r - u := by linarith [hr.1]
    have hprim : treeEqRhsS d L W S (KI r) I - C0 =
        primBilS d L W S (KI u) (KI r - KI u) I +
        primBilS d L W S (KI r - KI u) (KI u) I +
        primBilS d L W S (KI r - KI u)
          (KI r - KI u) I := hsub
    rw [hprim]
    calc _ ≤ ‖primBilS d L W S (KI u) (KI r - KI u) I +
            primBilS d L W S (KI r - KI u) (KI u) I‖ +
          ‖primBilS d L W S (KI r - KI u)
            (KI r - KI u) I‖ := norm_add_le _ _
      _ ≤ (‖primBilS d L W S (KI u) (KI r - KI u) I‖ +
            ‖primBilS d L W S (KI r - KI u) (KI u) I‖) +
          ‖primBilS d L W S (KI r - KI u)
            (KI r - KI u) I‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (c * B * (D1 * (r - u)) + c * (D1 * (r - u)) * B) + c * (D1 * (r - u)) * (D1 * (r - u)) := by
          exact add_le_add (add_le_add e1 e2) e3
      _ ≤ (c * B * (D1 * Δ) + c * (D1 * Δ) * B) + c * (D1 * Δ) * (D1 * Δ) := by gcongr
      _ = 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2 := by ring
  have hderiv : ∀ x ∈ Set.Icc u (u + Δ), HasDerivWithinAt
      (fun r : ℝ => KI r I - (r - u) • C0)
      (treeEqRhsS d L W S (KI x) I - C0) (Set.Icc u (u + Δ)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hu0.trans hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    have h1 := hder x ⟨hx0, hx1⟩ I hI h2
    have h2' : HasDerivAt (fun r : ℝ => (r - u) • C0) C0 x := by
      simpa using ((hasDerivAt_id x).sub_const u).smul_const C0
    exact (h1.sub h2').hasDerivWithinAt
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := u + Δ)
    (f := fun r : ℝ => KI r I - (r - u) • C0)
    (f' := fun x => treeEqRhsS d L W S (KI x) I - C0)
    (C := 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) hderiv hbound (u + Δ) ⟨by linarith, le_rfl⟩
  have hlhs : (KI (u + Δ) I - (u + Δ - u) • C0) - (KI u I - (u - u) • C0) =
      KI (u + Δ) I - KI u I - (Δ : ℂ) * C0 := by
    have h1 : u + Δ - u = Δ := by ring
    rw [h1, sub_self, zero_smul, sub_zero, Complex.real_smul]
    ring
  have hres' : ‖(KI (u + Δ) I - (u + Δ - u) • C0) -
      (KI u I - (u - u) • C0)‖ ≤
      (2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) * (u + Δ - u) := hres
  rw [hlhs, add_sub_cancel_left] at hres'
  refine hres'.trans ?_
  unfold kStepC
  have hΔ3 : Δ ^ 3 ≤ Δ ^ 2 := by
    calc Δ ^ 3 = Δ ^ 2 * Δ := by ring
      _ ≤ Δ ^ 2 * 1 := by gcongr
      _ = Δ ^ 2 := mul_one _
  have hcD : 0 ≤ c * D1 ^ 2 := by positivity
  calc (2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) * Δ
      = 2 * c * B * D1 * Δ ^ 2 + c * D1 ^ 2 * Δ ^ 3 := by ring
    _ ≤ 2 * c * B * D1 * Δ ^ 2 + c * D1 ^ 2 * Δ ^ 2 := by gcongr
    _ = _ := by rw [hD1, hc]; ring

end KStep

/-! ### 6. The classes `Expand`, `UStep` and the pin `GridDriftNg` (targets 8, 9) -/

section GridDef

variable {d : ℕ} {sz : Sizes d}

/-- **Target 8, `stepErrNg`**: `stepErrN` (`GridDriftN.lean:289`) with `envConst` unfolded and `etaT (E n)` read as
`C.eta n`. -/
def stepErrNg (C : FlowFM sz) (n k : ℕ) (u v Δ Bk : ℝ) : ℝ :=
  16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 * (1 + (C.eta n v)⁻¹) ^ (k + 4) *
      Δ ^ ((3 : ℝ) / 2) + kStepC d (sz.L n) (sz.W n) k Bk * Δ ^ 2 +
    uStepC k Δ v * ((C.eta n u)⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) + Bk)

/-- `stepErrN` is `stepErrNg` at `bandFM` (definitional). -/
theorem bandFM_stepErrN (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (u v Δ Bk : ℝ) :
    RBM.Ind.stepErrN d (sz.L n) (sz.W n) (E n) k u v Δ Bk = stepErrNg (bandFM sz E) n k u v Δ Bk := rfl

/-- **Target 8, `GridDriftNg`**: the pin `GridDriftN` (`GridDriftN.lean:663`) over `Step2Mat`, without the premise
`∀ n, |E n| < 2`; the error is `stepErrNg` with `Cm.eta`. -/
def GridDriftNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n j : ℕ), j < K n → ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j)
              (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (k + 4) * gridStep s t K n ^ ((3 : ℝ) / 2) +
          kStepC d (sz.L n) (sz.W n) k Bk * gridStep s t K n ^ 2 +
          uStepC k (gridStep s t K n) (gridTime s t K n (j + 1)) *
            ((Cm.eta n (gridTime s t K n j))⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk)

/-- **Target 9, class `HierDriftGen_Expand`**: one grid step of a loop observable along the carrier walk, the merged
`condExp_loop_drift` (`Path/LoopStep.lean:310`) with the generator written as `STllPairNg + STegtMg`. -/
def HierDriftGen_Expand (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : Prop :=
  0 ≤ s n → s n ≤ t n → t n < 1 → K n ≠ 0 →
  ∀ j : ℕ, j < K n → ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length →
    ∀ᵐ ω ∂(Cm.Pp),
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp
            (fun ω' => STLIMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n (j + 1) ω') I) ω -
          STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) I -
          (gridStep s t K n : ℂ) *
            (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n)
                (STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω)) I +
              STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) I)‖ ≤
        16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
          (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (I.length + 4) * gridStep s t K n ^ ((3 : ℝ) / 2)

/-- **Target 9, class `HierDriftGen_UStep`**: the row bounds of one step of the carrier kernel.  The first field is
T2471's K3 verbatim (`docs/tickets/checks/T2471-check.lean:215-216`); the second is the order-2 bound of the private
`gdn_row_UG` (`GridDriftN.lean:428`), the generator being `Step2Gen_thetaKer`. -/
def HierDriftGen_UStep (C : FlowFM sz) (n : ℕ) : Prop :=
  (∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' s t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤
      |t - s| * (1 - t)⁻¹) ∧
  (∀ (σ σ' : Bool) (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b -
        (Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b‖ ≤ Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2)

/-- **The link `𝒦 = KI ∘ KLloopOf`** (premise (e) of the ticket's "inputs used as hypotheses only"; needed by
`gridDriftNg` because `predIncNg` reads the `K` field and the `𝒦`-step the `KI` field): band `rfl`
(`STKloop = KLK ∘ KLloopOf`), BA `baStep2Mat_KI` (`BA/Step2BA.lean`). -/
def HierDriftGen_KLink (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∀ w ∈ Set.Ico (0 : ℝ) 1, ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a

/-- Band discharge of the link (definitional). -/
theorem hierDriftGen_kLink_band (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) : HierDriftGen_KLink (bandStep2Mat sz E) n :=
  fun _ _ _ _ _ => rfl

end GridDef

/-! ### 7. One step of `𝒰` over the carrier kernel (target 9) -/

section UStepGen

variable {d : ℕ} {sz : Sizes d}

/-- **One step of `𝒰`** (`gdn_Ugen_step_le`, `GridDriftN.lean:408`, in the `Step2Gen_UN` vocabulary): for `‖A‖_max ≤ M`,
`‖𝒰_{u,u+Δ,σ} A - A - Δ Θ_{u,σ} A‖ ≤ uStepC k Δ (u+Δ) M`, from the row bounds of `HierDriftGen_UStep`. -/
theorem HierDriftGen_UN_step_le (C : FlowFM sz) (n : ℕ) (hU : HierDriftGen_UStep C n) {k : ℕ}
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1)
    (A : (Fin k → Zd d (sz.L n)) → ℂ) (M : ℝ) (hA : ∀ y, ‖A y‖ ≤ M) (x : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ u (u + Δ) A x - A x - (Δ : ℂ) * Step2Gen_ThetaN C n σ u A x‖ ≤
      uStepC k Δ (u + Δ) * M := by
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  have key := gdn_tens_step_le (d := d) (L := sz.L n) (a := Δ * (1 - (u + Δ))⁻¹)
    (b := Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2) (mul_nonneg hΔ hβ1) (by positivity) k
    (fun i : Fin k => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u (u + Δ))
    (fun i : Fin k => (Δ : ℂ) • Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u)
    (fun i x' => by
      have h := hU.1 (σ i) (σ (finRotate k i)) u (u + Δ) (by linarith) hv x'
      rw [show u + Δ - u = Δ by ring, abs_of_nonneg hΔ] at h
      simpa only [Matrix.sub_apply] using h)
    (fun i x' => by
      have h := hU.2 (σ i) (σ (finRotate k i)) u Δ hu0 hΔ hv x'
      simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h) A M hA x
  have hT : gdnTens (fun i : Fin k => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u (u + Δ)) A x =
      Step2Gen_UN C n σ u (u + Δ) A x := rfl
  have hG : gdnGen (fun i : Fin k => (Δ : ℂ) • Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u) A x =
      (Δ : ℂ) * Step2Gen_ThetaN C n σ u A x := by
    unfold gdnGen Step2Gen_ThetaN
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hT, hG] at key
  refine key.trans (le_of_eq ?_)
  unfold uStepC
  ring

end UStepGen

/-! ### 8. The walk facts and the one-step theorem (target 9) -/

section GridStep

variable {d : ℕ} {sz : Sizes d}

/-- Integrability of the bounded loop observable along the shifted band walk (`gdn_integrable_loopL`,
`GridDriftN.lean:728`, with the Hermitian shift `Ψ0` and a spectral value `z`, `|Im z| ≥ η > 0`). -/
theorem HierDriftGen_integrable_loopL (P : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ)
    (Ψ0 : Matrix (Idx d (P.L n) (P.W n)) (Idx d (P.L n) (P.W n)) ℂ) (hΨ : Ψ0.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) (I : LoopIdx (Zd d (P.L n))) (hwf : I.WF) (hn : 1 ≤ I.length) :
    Integrable (fun ω : PathΩ P =>
      loopL d (P.L n) (P.W n) (blockMat d (P.L n) (P.W n) (Ψ0 + pathH P s t K n i ω)) z I) (pathP P) := by
  have hmeas : Measurable (fun ω : PathΩ P =>
      loopL d (P.L n) (P.W n) (blockMat d (P.L n) (P.W n) (Ψ0 + pathH P s t K n i ω)) z I) :=
    ((walk_measurable_loopL d (P.L n) (P.W n) z I).comp
      (walk_measurable_blockMat d (P.L n) (P.W n))).comp
      ((continuous_const.add continuous_id : Continuous fun M : Matrix (Idx d (P.L n) (P.W n))
        (Idx d (P.L n) (P.W n)) ℂ => Ψ0 + M).measurable.comp
        ((pathH_measurable_filt P s t K n i).mono ((filt P).le i) le_rfl))
  exact (memLp_top_of_bound hmeas.aestronglyMeasurable
    (η⁻¹ ^ I.a.length * (((P.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (I.a.length - 1))
    (Eventually.of_forall fun ω => RBM.Ind.norm_gloop_le_of_le_abs_im
      (show (blockMat d (P.L n) (P.W n) (Ψ0 + pathH P s t K n i ω)).IsHermitian from
        (hΨ.add (pathH_isHermitian P s t K n i ω)).submatrix _) hη hz I hwf hn)).integrable le_top

variable {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Under `LoopForm`, `0 < η_u` and `η_u ≤ |Im z_u|` (equality). -/
theorem HierDriftGen_eta_facts (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u : ℝ} (hu : u < 1) :
    0 < Cm.eta n u ∧ Cm.eta n u ≤ |(ztOf (Cm.m n) (E n) u).im| := by
  have hη : 0 < etaOf (Cm.m n) u := mul_pos (by linarith) (hL n).1
  refine ⟨by rw [(hL n).2.2.2 u]; exact hη, ?_⟩
  rw [(hL n).2.2.2 u, ztOf_im, abs_of_pos hη]

/-- Under `LoopForm`, the carrier loop `LM` is the list-indexed loop `STLIMg` at `KLloopOf`. -/
theorem HierDriftGen_LM_eq_LIM (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) : Cm.LM n u H σ a = STLIMg Cm n u H (KLloopOf d (sz.L n) σ a) := by
  rw [(hL n).2.1 u H k σ a]
  change loopM d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) _ σ a = Cm.LIM n u H _
  rw [(hL n).2.2.1 u H, loopM_eq_loopL]
  rfl

/-- Integrability of the carrier loop observable along the carrier walk. -/
theorem HierDriftGen_integrable_LIM (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {u : ℝ} (hu : u < 1) (I : LoopIdx (Zd d (sz.L n))) (hwf : I.WF)
    (hn : 1 ≤ I.length) :
    Integrable (fun ω : PathΩ sz => STLIMg Cm n u (Cm.Hpath s t K n i ω) I) Cm.Pp := by
  have hPp : Cm.Pp = pathP (sz.withLam lam') := hW.2.1
  obtain ⟨hη, hz⟩ := HierDriftGen_eta_facts hL n hu
  have e : (fun ω : PathΩ sz => STLIMg Cm n u (Cm.Hpath s t K n i ω) I) =
      fun ω => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
        (Ψ n + StepDecompGen_pathH sz lam' s t K n i ω)) (ztOf (Cm.m n) (E n) u) I := by
    funext ω
    simp only [STLIMg]
    rw [(hL n).2.2.1, StepDecompGen_Hpath_eq hW]
  rw [e, hPp]
  exact HierDriftGen_integrable_loopL (sz.withLam lam') s t K n i (Ψ n) (hW.1 n) hη hz I hwf hn

/-- The sup bound of the carrier loop observable along the carrier walk. -/
theorem HierDriftGen_norm_LIM_le (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {u : ℝ} (hu : u < 1) (ω : PathΩ sz) (I : LoopIdx (Zd d (sz.L n)))
    (hwf : I.WF) (hn : 1 ≤ I.length) :
    ‖STLIMg Cm n u (Cm.Hpath s t K n i ω) I‖ ≤
      (Cm.eta n u)⁻¹ ^ I.length * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (I.length - 1) := by
  obtain ⟨hη, hz⟩ := HierDriftGen_eta_facts hL n hu
  have hH : (Cm.Hpath s t K n i ω).IsHermitian := by
    rw [StepDecompGen_Hpath_eq hW]
    exact (hW.1 n).add (pathH_isHermitian (sz.withLam lam') s t K n i ω)
  simp only [STLIMg]
  rw [(hL n).2.2.1]
  exact RBM.Ind.norm_gloop_le_of_le_abs_im (hH.submatrix _) hη hz I hwf hn

end GridStep

section GridMain

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- **Target 9 (a), `gridDriftNg_at`**: one grid step of (`LK_SDE`), `3_5:133`, over the carrier, with the window and the
per-index classes (`Expand`, `KLoop`, `KTwo`, `UStep`, the row sums of `Cm.S n`, the link `KI ∘ KLloopOf = K`) at the size
index `n` only (DECISIONS §29 (4)); `gridDriftN_at`, `GridDriftN.lean:687`.  Proof: `P_j - Δ D_j = R₁ - R_𝒦 - R_𝒰`
(`gdn_algebra`), with `R₁` from `Expand`, `R_𝒦` from `HierDriftGen_K_step`, `R_𝒰` from `HierDriftGen_UN_step_le`, and the drift
from `loopDrift_sub_K_deriv_ng`. -/
theorem gridDriftNg_at (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hExp : HierDriftGen_Expand Cm s t K n)
    (hKL : HierDriftGen_KLoop Cm n) (hKT : HierDriftGen_KTwo Cm n) (hU : HierDriftGen_UStep Cm.toFlowFM n)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) (hKK : HierDriftGen_KLink Cm n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n)
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (Bk : ℝ) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j)
              (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (k + 4) * gridStep s t K n ^ ((3 : ℝ) / 2) +
          kStepC d (sz.L n) (sz.W n) k Bk * gridStep s t K n ^ 2 +
          uStepC k (gridStep s t K n) (gridTime s t K n (j + 1)) *
            ((Cm.eta n (gridTime s t K n j))⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk) := by
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := gdn_time_facts s t K n j hs0 hst ht1 hK hj
  have hkpos : 1 ≤ k := by omega
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hu1' : 0 ≤ gridTime s t K n (j + 1) := by rw [hvu]; linarith
  have : IsProbabilityMeasure Cm.Pp := by rw [hW.2.1]; exact isProbabilityMeasure_pathP _
  have hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => Cm.KI n s J) (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n t) J) t :=
    hKL.choose_spec.1
  have hB' : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n j + gridStep s t K n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖Cm.KI n w J‖ ≤ Bk := by
    intro w hw J hJ h2 hJk
    exact hB w (by rw [hvu]; exact hw) J hJ h2 hJk
  have hwf : ∀ {k' : ℕ} (σ' : Fin k' → Bool) (a : Fin k' → Zd d (sz.L n)), (KLloopOf d (sz.L n) σ' a).WF :=
    fun σ' a => gdn_loopOf_wf σ' a
  have hlen : ∀ {k' : ℕ} (σ' : Fin k' → Bool) (a : Fin k' → Zd d (sz.L n)), (KLloopOf d (sz.L n) σ' a).length = k' :=
    fun σ' a => gdn_loopOf_length σ' a
  have hae : ∀ a : Fin k → Zd d (sz.L n), ∀ᵐ ω ∂(Cm.Pp),
      MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' a) ω =
        MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => STLIMg Cm n (gridTime s t K n (j + 1))
          (Cm.Hpath s t K n (j + 1) ω') (KLloopOf d (sz.L n) σ a)) ω -
          Cm.KI n (gridTime s t K n (j + 1)) (KLloopOf d (sz.L n) σ a) ∧
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => STLIMg Cm n (gridTime s t K n (j + 1))
            (Cm.Hpath s t K n (j + 1) ω') (KLloopOf d (sz.L n) σ a)) ω -
          STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) -
          (gridStep s t K n : ℂ) *
            (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n)
                (STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω)) (KLloopOf d (sz.L n) σ a) +
              STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))‖ ≤
        16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
          (1 + (Cm.eta n (gridTime s t K n (j + 1)))⁻¹) ^ (k + 4) * gridStep s t K n ^ ((3 : ℝ) / 2) := by
    intro a
    have hint := HierDriftGen_integrable_LIM hL hW s t K n (j + 1) hv1 (KLloopOf d (sz.L n) σ a) (hwf σ a)
      (by rw [hlen]; exact hkpos)
    have hsub := condExp_sub hint
      (integrable_const (Cm.KI n (gridTime s t K n (j + 1)) (KLloopOf d (sz.L n) σ a))) (filt sz j)
    have hconst := condExp_const (μ := Cm.Pp) ((filt sz).le j)
      (Cm.KI n (gridTime s t K n (j + 1)) (KLloopOf d (sz.L n) σ a))
    have hexp := hExp hs0 hst ht1 hK j hj (KLloopOf d (sz.L n) σ a) (hwf σ a) (by rw [hlen]; exact hk)
    filter_upwards [hsub, hexp] with ω h1 h2
    refine ⟨?_, ?_⟩
    · have hfun : (fun ω' : PathΩ sz => AvecNg Cm s t K n (j + 1) σ ω' a) =
          (fun ω' => STLIMg Cm n (gridTime s t K n (j + 1)) (Cm.Hpath s t K n (j + 1) ω')
            (KLloopOf d (sz.L n) σ a)) -
          (fun _ => Cm.KI n (gridTime s t K n (j + 1)) (KLloopOf d (sz.L n) σ a)) := by
        funext ω'
        simp only [AvecNg, STLKMg, STLMg, Pi.sub_apply]
        rw [HierDriftGen_LM_eq_LIM hL, hKK _ ⟨hu1', hv1⟩ k σ a]
      rw [hfun, h1, Pi.sub_apply, hconst]
    · rw [hlen] at h2
      exact h2
  filter_upwards [ae_all_iff.2 hae] with ω hω a
  obtain ⟨hce, hR1⟩ := hω a
  have hAj : ∀ b : Fin k → Zd d (sz.L n), AvecNg Cm s t K n j σ ω b =
      STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b) -
        Cm.KI n (gridTime s t K n j) (KLloopOf d (sz.L n) σ b) := by
    intro b
    simp only [AvecNg, STLKMg, STLMg]
    rw [HierDriftGen_LM_eq_LIM hL, hKK _ ⟨hu0, hu1⟩ k σ b]
  have hsup : ∀ b : Fin k → Zd d (sz.L n), ‖AvecNg Cm s t K n j σ ω b‖ ≤
      (Cm.eta n (gridTime s t K n j))⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) + Bk := by
    intro b
    have h1 := HierDriftGen_norm_LIM_le hL hW s t K n j hu1 ω (KLloopOf d (sz.L n) σ b) (hwf σ b)
      (by rw [hlen]; exact hkpos)
    rw [hlen] at h1
    have h2 : ‖Cm.KI n (gridTime s t K n j) (KLloopOf d (sz.L n) σ b)‖ ≤ Bk :=
      hB _ ⟨hu0, by rw [hvu]; linarith⟩ _ (hwf σ b) (by rw [hlen]; exact hk) (by rw [hlen])
    rw [hAj]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hK' := HierDriftGen_K_step hS hder hu0 hΔ0 hΔ1 (by rw [← hvu]; exact hv1) hBk hB'
    (hwf σ a) (by rw [hlen]; exact hk) (hlen σ a)
  rw [← hvu] at hK'
  have hKd : deriv (fun x => Cm.KI n x (KLloopOf d (sz.L n) σ a)) (gridTime s t K n j) =
      treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n (gridTime s t K n j)) (KLloopOf d (sz.L n) σ a) :=
    (hder _ ⟨hu0, hu1⟩ _ (hwf σ a) (by rw [hlen]; exact hk)).deriv
  have hU' := HierDriftGen_UN_step_le Cm.toFlowFM n hU σ hu0 hΔ0 (by rw [← hvu]; exact hv1)
    (AvecNg Cm s t K n j σ ω) _ hsup a
  rw [← hvu] at hU'
  have hier := loopDrift_sub_K_deriv_ng Cm n hKL hKT (gridTime s t K n j) ⟨hu0, hu1⟩ (Cm.Hpath s t K n j ω) k hk
    σ a
  have hlk : (fun b : Fin k → Zd d (sz.L n) =>
      STLKIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b)) =
      AvecNg Cm s t K n j σ ω := funext fun b => (hAj b).symm
  rw [hlk, hKd] at hier
  have hpred : predIncNg Cm s t K n j σ ω a =
      (MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => STLIMg Cm n (gridTime s t K n (j + 1))
            (Cm.Hpath s t K n (j + 1) ω') (KLloopOf d (sz.L n) σ a)) ω -
          Cm.KI n (gridTime s t K n (j + 1)) (KLloopOf d (sz.L n) σ a)) -
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
          (AvecNg Cm s t K n j σ ω) a := by
    unfold predIncNg
    rw [hce]
  rw [hpred]
  rw [hAj a] at hU'
  have key := gdn_algebra
    (S := (∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n (gridTime s t K n j)
              (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ a) +
            STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a) +
            STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a)))
    (Gj := STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ a))
    (by rw [hier]; ring) hR1 hK' hU'
  refine key.trans (le_of_eq ?_)
  ring

/-- **Target 9 (b), `gridDriftNg`**: `gridDriftNg_at` at every size index (`gridDriftN`, `GridDriftN.lean:759`). -/
theorem gridDriftNg (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (hExp : ∀ n, HierDriftGen_Expand Cm s t K n)
    (hKL : ∀ n, HierDriftGen_KLoop Cm n) (hKT : ∀ n, HierDriftGen_KTwo Cm n)
    (hU : ∀ n, HierDriftGen_UStep Cm.toFlowFM n)
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hKK : ∀ n, HierDriftGen_KLink Cm n) : GridDriftNg Cm s t K := by
  intro hs0 hst ht1 hK n j hj k hk σ Bk hBk hB
  exact gridDriftNg_at hL hW s t K n j (hExp n) (hKL n) (hKT n) (hU n) (hS n) (hKK n) (hs0 n) (hst n) (ht1 n)
    (hK n) hj hk σ Bk hBk hB

end GridMain

/-! ### 9. The envelopes of `𝒦` (target 10) -/

section EnvelopeAbstract

/-- The abstract envelope: `KI` solving the derivative equation on `[0, 1)` is bounded on `[0, v]` for the loops of length
at most `k` (`GridDriftN_exists_envelope`, `GridDriftN.lean:950`). -/
theorem HierDriftGen_exists_envelope_of {d L W : ℕ} [NeZero L] {S : Matrix (Zd d L) (Zd d L) ℂ}
    {KI : ℝ → LoopIdx (Zd d L) → ℂ} (hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => KI s J) (treeEqRhsS d L W S (KI t) J) t) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      J.length ≤ k → ‖KI w J‖ ≤ B := by
  have h1 : ∀ ℓ : ℕ, ∀ p : (Fin ℓ → Bool) × (Fin ℓ → Zd d L), ∃ C : ℝ, 0 ≤ C ∧
      (2 ≤ ℓ → ∀ w ∈ Set.Icc (0 : ℝ) v, ‖KI w (loopOf p.1 p.2)‖ ≤ C) := by
    intro ℓ p
    by_cases hℓ : 2 ≤ ℓ
    · have hcont : ContinuousOn (fun w : ℝ => KI w (loopOf p.1 p.2)) (Set.Icc 0 v) := by
        intro w hw
        refine ContinuousAt.continuousWithinAt ?_
        have hwf : (loopOf p.1 p.2).WF := gdn_loopOf_wf p.1 p.2
        have hlen : 2 ≤ (loopOf p.1 p.2).length := by rw [gdn_loopOf_length]; exact hℓ
        exact (hder w ⟨hw.1, lt_of_le_of_lt hw.2 hv1⟩ _ hwf hlen).continuousAt
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := v)).exists_bound_of_continuousOn hcont
      exact ⟨max C 0, le_max_right _ _, fun _ w hw => (hC w hw).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hℓ⟩
  choose C hC0 hC using h1
  refine ⟨∑ ℓ ∈ Finset.range (k + 1), ∑ p : (Fin ℓ → Bool) × (Fin ℓ → Zd d L), C ℓ p,
    Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun p _ => hC0 ℓ p, ?_⟩
  intro w hw J hJ h2 hk
  have hJe := gdn_loopOf_eq J hJ
  have hb := hC J.length (fun i => J.σ.getD i false, fun i => J.a.getD i (0 : Zd d L)) h2 w hw
  simp only at hb
  rw [hJe] at hb
  refine hb.trans ?_
  have hmem : J.length ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  refine le_trans ?_ (Finset.single_le_sum (f := fun ℓ => ∑ p : (Fin ℓ → Bool) × (Fin ℓ → Zd d L),
    C ℓ p) (fun ℓ _ => Finset.sum_nonneg fun p _ => hC0 ℓ p) hmem)
  exact Finset.single_le_sum (f := fun p : (Fin J.length → Bool) × (Fin J.length → Zd d L) =>
    C J.length p) (fun p _ => hC0 _ p) (Finset.mem_univ _)

end EnvelopeAbstract

section EnvelopeCarrier

variable {d : ℕ} {sz : Sizes d}

/-- **Target 10, `HierDriftGen_exists_envelope`** (`GridDriftN_exists_envelope`, `GridDriftN.lean:950`, over the carrier):
from `KLoop` (continuity of `KI` on `[0, 1)`) and the finiteness of the loops of length `≤ k`, a deterministic envelope of
`Cm.KI n` on `[0, v]` exists. -/
theorem HierDriftGen_exists_envelope (Cm : Step2Mat sz) (n : ℕ) (hK : HierDriftGen_KLoop Cm n) {v : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v < 1) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ k → ‖Cm.KI n w J‖ ≤ B :=
  HierDriftGen_exists_envelope_of hK.choose_spec.1 hv0 hv1 k

end EnvelopeCarrier

section Envelope

variable {d : ℕ} {sz : Sizes d}

/-- The deterministic content of `STKbound` along a window: if `STKbound` holds, then eventually in
`n`, for every `w ∈ [0, v_n]`, every sign vector and label vector of length `k ≥ 1`,
`‖𝒦_w(σ, a)‖ ≤ N^τ (W^{-d} B_{w,0})^{k-1}`.  `≺` of a deterministic quantity is a deterministic
inequality (the bad event is `∅` or the whole space, and `P(bad) ≤ N^{-1} < 1`); the supremum over
`w` is taken by choosing the worst `w_n` and applying `STKbound` to the sequence `w_n`. -/
theorem HierDriftGen_Kbound_win (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hKb : STKboundgL Cm.toFlowFM μ) (hsz : sz.SizeTendsto)
    (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (k : ℕ) (hk : 1 ≤ k) (τ : ℝ)
    (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖Cm.K n w σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n w) ^ (k - 1) := by
  classical
  by_contra hcon
  have hfreq := Filter.not_eventually.1 hcon
  let bad : ℕ → Prop := fun n => ∃ w ∈ Set.Icc (0 : ℝ) (v n), ∃ (σ : Fin k → Bool)
      (a : Fin k → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n w) ^ (k - 1) < ‖Cm.K n w σ a‖
  have hbad : ∀ n, ¬ (∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ (σ : Fin k → Bool)
      (a : Fin k → Zd d (sz.L n)),
      ‖Cm.K n w σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n w) ^ (k - 1)) →
      bad n := by
    intro n hn
    by_contra hb
    exact hn fun w hw σ a => by
      by_contra hc
      exact hb ⟨w, hw, σ, a, not_le.1 hc⟩
  let w' : ℕ → ℝ := fun n => if h : bad n then Classical.choose h else 0
  have hw'mem : ∀ n, w' n ∈ Set.Icc (0 : ℝ) (v n) := by
    intro n
    by_cases h : bad n
    · have e : w' n = Classical.choose h := by simp [w', h]
      rw [e]
      exact (Classical.choose_spec h).1
    · have e : w' n = 0 := by simp [w', h]
      rw [e]
      exact ⟨le_rfl, hv0 n⟩
  have hprec := hKb w' (fun n => (hw'mem n).1) (fun n => lt_of_le_of_lt (hw'mem n).2 (hv1 n)) k hk
    τ hτ 1 one_pos
  have hsize2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (Filter.tendsto_atTop.1 hsz) 2
  obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hprec.and hsize2)).exists
  have hwn : bad n := hbad n hn1
  have hex : ∃ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (w' n)) ^ (k - 1) <
        ‖Cm.K n (w' n) σ a‖ := by
    have hspec := Classical.choose_spec hwn
    have e : w' n = Classical.choose hwn := by simp [w', hwn]
    rw [e]
    exact hspec.2
  obtain ⟨σ, a, hσa⟩ := hex
  have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
    refine (measure_univ (μ := μ)).symm.le.trans ((measure_mono ?_).trans hn2)
    intro ω _
    exact ⟨(σ, a), hσa⟩
  have h2 := ENNReal.one_le_ofReal.1 h1
  rw [Real.rpow_neg_one] at h2
  have h3 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hn3
  linarith [h3, show (2 : ℝ)⁻¹ < 1 by norm_num]

/-- **The envelope witness** (RBM2D `exists_norm_Kcal_le_win`, `GDN:792`; RBM1D
`exists_norm_Kval_le_win`, `Gauss/DriftEnvelope.lean:246` at `c06b103`).  Fixed `m` and `τ > 0`: for
a time sequence `v_n ∈ [0, 1)`, eventually in `n`, uniformly over `w ∈ [0, v_n]` and the
well-formed loops `J` of length in `[2, m]`, `‖𝒦_w(J)‖ ≤ N^τ η_{v_n}^{-m}`, `N = sz.size n = (W L)^d`.
**Form change (paper-delta candidate T2111a).**  RBM2D proves the bound from `Kbound_prec_uncond`
(`Loop/KBound`), uniformly over all `(L, W, E, u, v)` with `W² L² = N`; RBM3D has no proof of the
`≺` bound of `𝒦` (`STKbound`, `ML:Kbound`, `1_2:1056`, registered *owed*, KL7), and a single size
sequence carries it, so the statement is along the sequence `sz` with `STKbound sz E` and
`N → ∞` (`SizeTendsto`) as hypotheses.  The supremum over `w ∈ [0, v_n]` (RBM2D: over `u ≤ v`)
is kept.  `STKbound` is a `≺` statement, hence the factor `N^τ`; `W^{-d} B_{w,0} ≤ 2 η_v⁻¹` replaces
`Mt⁻¹ ≤ η_v⁻¹` (`gdn_Bctl_le`), and the `2^{m}` is absorbed by `N^{τ/2}`. -/
theorem exists_norm_KI_le_wing (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hsz : sz.SizeTendsto) (hKb : STKboundgL Cm.toFlowFM μ)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hη : ∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v)
    (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (m : ℕ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ m →
        ‖Cm.KI n w J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((Cm.eta n (v n))⁻¹) ^ m := by
  have hall : ∀ᶠ n in atTop, ∀ ℓ ∈ Finset.Icc 2 m, ∀ w ∈ Set.Icc (0 : ℝ) (v n),
      ∀ (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d (sz.L n)),
        ‖Cm.K n w σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n w) ^ (ℓ - 1) :=
    (Filter.eventually_all_finset _).2 fun ℓ hℓ =>
      HierDriftGen_Kbound_win Cm μ hKb hsz v hv0 hv1 ℓ (by have := (Finset.mem_Icc.1 hℓ).1; omega) (τ / 2)
        (half_pos hτ)
  have hpow : ∀ᶠ n in atTop, (2 : ℝ) ^ m ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) atTop atTop :=
      (tendsto_rpow_atTop (half_pos hτ)).comp hsz
    exact h1.eventually_ge_atTop _
  have hsize1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (Filter.tendsto_atTop.1 hsz) 1
  filter_upwards [hall, hpow, hsize1] with n hn hp hs1
  intro w hw J hJ h2 hJm
  have hℓ : J.length ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨h2, hJm⟩
  have hb := hn J.length hℓ w hw (fun i : Fin J.length => J.σ.getD i false)
    (fun i : Fin J.length => J.a.getD i (0 : Zd d (sz.L n)))
  have hJe := gdn_loopOf_eq J hJ
  have hb' : ‖Cm.KI n w J‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n w) ^ (J.length - 1) := by
    have e : ∀ (σ' : Fin J.length → Bool) (a' : Fin J.length → Zd d (sz.L n)),
        Cm.K n w σ' a' = Cm.KI n w (loopOf σ' a') := fun σ' a' => (hKK n w _ σ' a').symm
    rw [e, hJe] at hb
    exact hb
  have hv : v n < 1 := hv1 n
  obtain ⟨hηpos, hηle⟩ := hη n (v n) (hv0 n) hv
  have hη1 : Cm.eta n (v n) ≤ 1 := by linarith [(hv0 n)]
  have hx1 : 1 ≤ (Cm.eta n (v n))⁻¹ := (one_le_inv₀ hηpos).2 hη1
  have hBle : sz.Bctl n w ≤ 2 * (Cm.eta n (v n))⁻¹ := by
    refine (gdn_Bctl_le sz n hw.1 hw.2 hv).trans ?_
    have : (1 - v n)⁻¹ ≤ (Cm.eta n (v n))⁻¹ := inv_anti₀ hηpos hηle
    linarith
  have hB0 : 0 ≤ sz.Bctl n w := gdn_Bctl_nonneg sz n (lt_of_le_of_lt hw.2 hv)
  have hpow2 : (sz.Bctl n w) ^ (J.length - 1) ≤ (2 : ℝ) ^ m * ((Cm.eta n (v n))⁻¹) ^ m := by
    calc (sz.Bctl n w) ^ (J.length - 1) ≤ (2 * (Cm.eta n (v n))⁻¹) ^ (J.length - 1) :=
          pow_le_pow_left₀ hB0 hBle _
      _ = 2 ^ (J.length - 1) * ((Cm.eta n (v n))⁻¹) ^ (J.length - 1) := mul_pow _ _ _
      _ ≤ 2 ^ m * ((Cm.eta n (v n))⁻¹) ^ m := by
          refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
            (pow_le_pow_right₀ hx1 (by omega)) (by positivity) (by positivity)
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc ‖Cm.KI n w J‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n w) ^ (J.length - 1) := hb'
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((2 : ℝ) ^ m * ((Cm.eta n (v n))⁻¹) ^ m) :=
        mul_le_mul_of_nonneg_left hpow2 (Real.rpow_nonneg hNpos.le _)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((Cm.eta n (v n))⁻¹) ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _)
        exact mul_le_mul_of_nonneg_right hp (by positivity)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * ((Cm.eta n (v n))⁻¹) ^ m := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]
        congr 2
        ring

end Envelope

/-! ### 10. Band discharges of `Expand`, `UStep` and the band grid drift (targets 8, 9) -/

section BandGrid

variable {d : ℕ}

open scoped Matrix.Norms.Operator in
/-- `Σ_y |(uKer μ v w - 1)(x,y)| ≤ |w - v| (1 - w)⁻¹` for `‖μ‖ = 1`, `0 ≤ w < 1`, no order between `v` and `w` (copy of
the private `difRep3_sum_norm_uKer_sub_one`, `Path/DifREP3.lean:420`; `uKer_eq_one_add`, `norm_Theta_le`). -/
theorem HierDriftGen_sum_norm_uKer_sub_one {L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1)
    {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (x : Zd d L) :
    ∑ y, ‖uKer d L g μ v w x y - (1 : Matrix (Zd d L) (Zd d L) ℂ) x y‖ ≤ |w - v| * (1 - w)⁻¹ := by
  have hξ : ‖(w : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hw0 hw1 hμ
  have hu := uKer_eq_one_add (d := d) (L := L) (g := g) (s := v) hL hξ
  have hΘ := norm_Theta_le (d := d) (L := L) (g := g) hL hw0 hw1 hμ
  have hentry : ∀ y, uKer d L g μ v w x y - (1 : Matrix (Zd d L) (Zd d L) ℂ) x y =
      ((((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))) x y := by
    intro y
    rw [hu]
    simp
  simp only [hentry]
  refine (sum_norm_row_le _ x).trans ?_
  have hc : ‖((w : ℂ) - v) * μ‖ = |w - v| := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖
      ≤ ‖((w : ℂ) - v) * μ‖ * (‖SB d L g‖ * ‖Theta d L g ((w : ℂ) * μ)‖) :=
        (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ = |w - v| * ‖Theta d L g ((w : ℂ) * μ)‖ := by rw [hc, norm_SB d L g hL, one_mul]
    _ ≤ |w - v| * (1 - w)⁻¹ := mul_le_mul_of_nonneg_left hΘ (abs_nonneg _)

/-- **Band discharge of `HierDriftGen_UStep`**: first field `HierDriftGen_sum_norm_uKer_sub_one` (T2471's K3, all real `s`),
second field the private `gdn_row_UG` (`GridDriftN.lean:428`), both through `Step2Kern_uKer_band`,
`Step2Kern_thetaKer_band` and `‖m(σ) m(σ')‖ = 1` (`|E n| ≤ 2`). -/
theorem hierDriftGen_uStep_band (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) (n : ℕ) :
    HierDriftGen_UStep (bandStep2Mat sz E).toFlowFM n := by
  have hfm : (bandStep2Mat sz E).toFlowFM = bandFM sz E := rfl
  have hμ : ∀ σ σ' : Bool, ‖mSigma (E n) σ * mSigma (E n) σ'‖ = 1 := fun σ σ' => by
    rw [norm_mul, norm_mSigma (hE n).le, norm_mSigma (hE n).le, mul_one]
  refine ⟨fun σ σ' s t ht0 ht1 a => ?_, fun σ σ' u Δ hu hΔ hv a => ?_⟩
  · rw [hfm, Step2Kern_uKer_band]
    exact HierDriftGen_sum_norm_uKer_sub_one (g := sz.lam n) (sz.three_le_L n) (hμ σ σ') ht0 ht1 a
  · rw [hfm]
    simp only [Step2Kern_uKer_band, Step2Kern_thetaKer_band, gdn_thetaKer_eq]
    have h := gdn_row_UG (g := sz.lam n) (sz.three_le_L n) (hμ σ σ') hu hΔ hv a
    simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h

/-- **Band discharge of `HierDriftGen_Expand`**: the merged `condExp_loop_drift` (`Path/LoopStep.lean:310`) with the
generator `genMat` written as `STllPairN + STegtM` (`stLoopGenNForm_holds`, `LoopGenN.lean:769`). -/
theorem hierDriftGen_expand_band (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) : HierDriftGen_Expand (bandStep2Mat sz E) s t K n := by
  intro hs0 hst ht1 hK j hj I hI h2
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := gdn_time_facts s t K n j hs0 hst ht1 hK hj
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hd := condExp_loop_drift sz s t K n j (E n) (hE n) hI hs0 hst hK hj hv1
  filter_upwards [hd] with ω hω
  have hgen : genMat d (sz.L n) (sz.W n) (sz.lam n) (E n) (gridTime s t K n j) (pathH sz s t K n j ω) I =
      treeEqRhsS d (sz.L n) (sz.W n) ((bandStep2Mat sz E).S n)
          (STLIMg (bandStep2Mat sz E) n (gridTime s t K n j) ((bandStep2Mat sz E).Hpath s t K n j ω)) I +
        STegtMg (bandStep2Mat sz E) n (gridTime s t K n j) ((bandStep2Mat sz E).Hpath s t K n j ω) I := by
    have hI' := gdn_loopOf_eq I hI
    have h := RBM.Ind.stLoopGenNForm_holds d sz n (E n) (hE n) (gridTime s t K n j) hu0 hu1
      (pathH sz s t K n j ω) (pathH_isHermitian sz s t K n j ω) I.length h2
      (fun i : Fin I.length => I.σ.getD i false) (fun i : Fin I.length => I.a.getD i (0 : Zd d (sz.L n)))
    rw [hI'] at h
    exact h
  rw [hgen] at hω
  exact hω

/-- The row sums of the band kernel `SB d L g` are `1`, in particular `≤ 1` (`sum_nnnorm_SB_row`). -/
theorem hierDriftGen_SB_row (sz : Sizes d) (n : ℕ) (a : Zd d (sz.L n)) :
    ∑ b : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖ ≤ 1 := by
  have h := sum_nnnorm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) a
  have h' := congrArg (fun x : NNReal => (x : ℝ)) h
  simp at h'
  exact h'.le

/-- **Band: `GridDriftN`** (`GridDriftN.lean:663`) from `gridDriftNg` at `bandStep2Mat`: `predIncN` is `predIncNg`
(`bandStep2_predIncN`), the loops, the generator and the error are definitionally the carrier's. -/
theorem hierDriftGen_band_gridDriftN (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    RBM.Ind.GridDriftN sz E s t K := by
  intro hE hs0 hst ht1 hK n j hj k hk σ Bk hBk hB
  have hg := gridDriftNg (stepDecompGen_loopForm_band sz E hE) (stepDecompGen_walkForm_band sz E) s t K
    (fun n => hierDriftGen_expand_band sz E hE s t K n) (hierDriftGen_kLoop_band sz E hE)
    (hierDriftGen_kTwo_band sz E hE) (hierDriftGen_uStep_band sz E hE) (fun n a => hierDriftGen_SB_row sz n a)
    (hierDriftGen_kLink_band sz E)
  filter_upwards [hg hs0 hst ht1 hK n j hj k hk σ Bk hBk hB] with ω hω a
  have h := hω a
  rw [bandStep2_predIncN]
  exact h

/-- **Band: `GridDriftN_exists_envelope`** (`GridDriftN.lean:950`) from `HierDriftGen_exists_envelope_of` (the derivative
equation is `KLK_isKLoop` through `IsKLoop_iff_IsKLoopS`). -/
theorem hierDriftGen_band_exists_envelope {L W : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) (hW : 1 ≤ W)
    {E : ℝ} (hE : |E| < 2) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      J.length ≤ k → ‖KLK d L g W E w J‖ ≤ B :=
  HierDriftGen_exists_envelope_of (W := W) (S := SB d L g) (KI := fun w I => KLK d L g W E w I)
    ((IsKLoop_iff_IsKLoopS d L W g (mSigma E) (Set.Ico (0 : ℝ) 1) _).1 (KLK_isKLoop d L W g E hL hW hE)).1
    hv0 hv1 k

/-- The band spectral data: `0 < η_v ≤ 1 - v` for `|E| < 2` (`mE_im ≤ 1`). -/
theorem hierDriftGen_band_eta (E : ℝ) (hE : |E| < 2) {v : ℝ} (hv1 : v < 1) :
    0 < etaT E v ∧ etaT E v ≤ 1 - v := by
  refine ⟨etaT_pos hE hv1, ?_⟩
  have him : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  calc etaT E v = (1 - v) * (mE E).im := rfl
    _ ≤ (1 - v) * 1 := mul_le_mul_of_nonneg_left him (by linarith)
    _ = 1 - v := mul_one _

/-- **Band: `exists_norm_Kcal_le_win`** (`GridDriftN.lean:1098`) from `exists_norm_KI_le_wing` at `bandStep2Mat` and
`μ = seqP sz` (`STKbound sz E` is `STKboundgL (bandFM sz E) (seqP sz)`). -/
theorem hierDriftGen_band_exists_norm_Kcal_le_win (sz : Sizes d) (hsz : sz.SizeTendsto) (E : ℕ → ℝ)
    (hKb : sz.STKbound E) (hE : ∀ n, |E n| < 2) (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (m : ℕ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ m →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (E n) (v n))⁻¹) ^ m :=
  exists_norm_KI_le_wing (bandStep2Mat sz E) (Sizes.seqP sz) hsz hKb (fun n w k σ a => rfl)
    (fun n v hv0 hv1 => hierDriftGen_band_eta (E n) (hE n) hv1) v hv0 hv1 m τ hτ

end BandGrid

/-! ### 11. Compiled nonempty instances (`d = 3`, `sz0`; targets 6-10)

Data: the merged admissible sequence `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`, `N = 2097152`), the band carrier
`bandStep2Mat sz0 (fun _ => 0)` (`E = 0`, `m = i`), `Ψ = 0`, `lam' = sz0.lam`, the window `s ≡ 0`, `t ≡ 1/2`, `K ≡ 4`
(`Δ = 1/8`, `u_1 = 1/8`, `u_2 = 1/4`), size index `0`, loops of length `3`, `σ = (+,-,+)`, labels `(0,1,2)` (distinct blocks
of `Z_4^3`).  Every deterministic hypothesis is discharged; the pin `STKboundgL` (registered, owner K12/BA-V) stays a
hypothesis of the envelope-window example. -/

section Instances

namespace HierDriftGenCheck

open RBM.Gauss.SizesInst

private abbrev E0 : ℕ → ℝ := fun _ => 0
private abbrev s0 : ℕ → ℝ := fun _ => 0
private abbrev t0 : ℕ → ℝ := fun _ => 1 / 2
private abbrev K0 : ℕ → ℕ := fun _ => 4
private abbrev Ψ0 : ∀ n : ℕ, Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ := fun _ => 0
private abbrev Cm0 : Step2Mat sz0 := bandStep2Mat sz0 E0
private abbrev σ3 : Fin 3 → Bool := ![true, false, true]
private abbrev a3 : Fin 3 → Zd 3 (sz0.L 0) := ![0, 1, 2]

private theorem hE0 : ∀ n, |E0 n| < 2 := fun _ => by norm_num
private theorem hL0 : StepDecompGen_LoopForm Cm0 E0 := stepDecompGen_loopForm_band sz0 E0 hE0
private theorem hW0 : StepDecompGen_WalkForm Cm0 sz0.lam Ψ0 := stepDecompGen_walkForm_band sz0 E0
private theorem hst0 : s0 0 ≤ t0 0 := by norm_num
private theorem ht10 : t0 0 < 1 := by norm_num
private theorem hj0 : (0 : ℕ) < K0 0 := by norm_num

/-- The grid data are nondegenerate. -/
private theorem data : gridStep s0 t0 K0 0 = 1 / 8 ∧ gridTime s0 t0 K0 0 1 = 1 / 8 ∧
    Sizes.size sz0 0 = 2097152 ∧ 0 < (Cm0.m 0).im :=
  ⟨by norm_num [gridStep], by norm_num [gridStep, gridTime], sz0_values.2.2.1, (hL0 0).1⟩

/-- **Target 6, `norm_primBilS_le`** at the band kernel `SB`, the loop `((+,-),(0,0))`, `F = G = 1`, `B_F = B_G = 1`. -/
example :=
  norm_primBilS_le 3 (sz0.L 0) (sz0.W 0) (SB 3 (sz0.L 0) (sz0.lam 0)) (hierDriftGen_SB_row sz0 0)
    (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (⟨[true, false], [0, 0]⟩ : LoopIdx (Zd 3 (sz0.L 0))) rfl
    (zero_le_one : (0 : ℝ) ≤ 1) (zero_le_one : (0 : ℝ) ≤ 1) (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)

/-- **Target 6, `primRhsS_split`** at the band kernel and the length-`2` loop (every `K`, `D`). -/
example (K D : LoopIdx (Zd 3 (sz0.L 0)) → ℂ) :=
  primRhsS_split 3 (sz0.L 0) (sz0.W 0) (SB 3 (sz0.L 0) (sz0.lam 0)) K D
    (⟨[true, false], [0, 0]⟩ : LoopIdx (Zd 3 (sz0.L 0))) (by decide)

/-- **Target 6, `loopDrift_sub_K_deriv_ng`**: `u = 1/2`, `M = 1`, `k = 3`, `σ = (+,-,+)`, `a = (0,1,2)`. -/
example := loopDrift_sub_K_deriv_ng Cm0 0 (hierDriftGen_kLoop_band sz0 E0 hE0 0) (hierDriftGen_kTwo_band sz0 E0 hE0 0)
  (1 / 2) ⟨by norm_num, by norm_num⟩ (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) 3
  (by norm_num) σ3 a3

/-- **Target 7, `hierarchyNg_of`**: the same data. -/
example := hierarchyNg_of Cm0 E0 sz0.lam hL0 (fun _ => rfl) (hierDriftGen_kLoop_band sz0 E0 hE0)
  (hierDriftGen_kTwo_band sz0 E0 hE0) 0 (1 / 2) (by norm_num) (by norm_num)
  (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) Matrix.isHermitian_one 3 (by norm_num) σ3 a3

/-- **Targets 8-9, `gridDriftNg`**: the pin `GridDriftNg` at the band carrier and the window, every class discharged. -/
example : GridDriftNg Cm0 s0 t0 K0 :=
  gridDriftNg hL0 hW0 s0 t0 K0 (fun n => hierDriftGen_expand_band sz0 E0 hE0 s0 t0 K0 n)
    (hierDriftGen_kLoop_band sz0 E0 hE0) (hierDriftGen_kTwo_band sz0 E0 hE0) (hierDriftGen_uStep_band sz0 E0 hE0)
    (fun n a => hierDriftGen_SB_row sz0 n a) (hierDriftGen_kLink_band sz0 E0)

/-- The envelope of `𝒦` on `[0, u_1]` for loops of length `≤ 3` at the data (target 10, `HierDriftGen_exists_envelope`). -/
private theorem env3 : ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s0 t0 K0 0 1),
    ∀ J : LoopIdx (Zd 3 (sz0.L 0)), J.WF → 2 ≤ J.length → J.length ≤ 3 → ‖Cm0.KI 0 w J‖ ≤ B :=
  HierDriftGen_exists_envelope Cm0 0 (hierDriftGen_kLoop_band sz0 E0 hE0 0)
  (v := gridTime s0 t0 K0 0 1) (by norm_num [gridTime, gridStep]) (by norm_num [gridTime, gridStep]) 3

/-- **Target 9 (a), `gridDriftNg_at`** at the data, step `j = 0` (`H_0 = 0`), the envelope `B_3` from `env3`. -/
example :=
  gridDriftNg_at hL0 hW0 s0 t0 K0 0 0 (hierDriftGen_expand_band sz0 E0 hE0 s0 t0 K0 0)
    (hierDriftGen_kLoop_band sz0 E0 hE0 0) (hierDriftGen_kTwo_band sz0 E0 hE0 0)
    (hierDriftGen_uStep_band sz0 E0 hE0 0) (hierDriftGen_SB_row sz0 0) (hierDriftGen_kLink_band sz0 E0 0)
    (le_refl _) hst0 ht10 (by norm_num) hj0 (k := 3) (by norm_num) σ3 env3.choose env3.choose_spec.1
    env3.choose_spec.2

/-- Step `j = 1` (`H_1 = √Δ X_1` random), the envelope on `[0, u_2]`. -/
private theorem env3' : ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s0 t0 K0 0 2),
    ∀ J : LoopIdx (Zd 3 (sz0.L 0)), J.WF → 2 ≤ J.length → J.length ≤ 3 → ‖Cm0.KI 0 w J‖ ≤ B :=
  HierDriftGen_exists_envelope Cm0 0 (hierDriftGen_kLoop_band sz0 E0 hE0 0)
  (v := gridTime s0 t0 K0 0 2) (by norm_num [gridTime, gridStep]) (by norm_num [gridTime, gridStep]) 3

example :=
  gridDriftNg_at hL0 hW0 s0 t0 K0 0 1 (hierDriftGen_expand_band sz0 E0 hE0 s0 t0 K0 0)
    (hierDriftGen_kLoop_band sz0 E0 hE0 0) (hierDriftGen_kTwo_band sz0 E0 hE0 0)
    (hierDriftGen_uStep_band sz0 E0 hE0 0) (hierDriftGen_SB_row sz0 0) (hierDriftGen_kLink_band sz0 E0 0)
    (le_refl _) hst0 ht10 (by norm_num) (by norm_num [K0]) (k := 3) (by norm_num) σ3 env3'.choose
    env3'.choose_spec.1 env3'.choose_spec.2

/-- **Band: `GridDriftN`** at the data. -/
example := hierDriftGen_band_gridDriftN sz0 E0 s0 t0 K0

/-- **Target 10, `exists_norm_KI_le_wing`**: `STKboundgL` (registered, KL7) stays a hypothesis; `SizeTendsto` is
`sz0_tendsto`; the link is `rfl`; `0 < η_v ≤ 1 - v` is the band spectral data; `v ≡ 1/2`, `m = 3`, `τ = 1/10`. -/
example (hKb : STKboundgL Cm0.toFlowFM (Sizes.seqP sz0)) :=
  exists_norm_KI_le_wing Cm0 (Sizes.seqP sz0) sz0_tendsto hKb (fun n w k σ a => rfl)
    (fun n v hv0 hv1 => hierDriftGen_band_eta (E0 n) (hE0 n) hv1) (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun _ => by norm_num) 3 (1 / 10) (by norm_num)

end HierDriftGenCheck

end Instances

end RBM.BA

end
