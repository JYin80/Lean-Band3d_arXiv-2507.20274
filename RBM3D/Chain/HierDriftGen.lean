/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.StepDecompGen
import RBM3D.Induction.GridDriftN

/-!
# The hierarchy algebra, the hierarchy identity and the grid drift over the carrier

Generic forms of `Induction/HierAlgebra`, `Induction/HierarchyN` and `Induction/GridDriftN` over a
carrier `Cm : Step2Mat sz`, on the kernel `Cm.S n` and the classes of `Chain/StepDecompGen`.

* **Algebra**: `primBilS`, `primRhsS_split`, `norm_primBilS_le` (kernel `S`, hypothesis
  `∀ a, Σ_b ‖S a b‖ ≤ 1`); the classes `HierDriftGen_KLoop`, `HierDriftGen_KTwo` (the `l = 2` coupling
  of `𝒦` is `Step2Gen_ThetaN`); `loopDrift_sub_K_deriv_ng`.
* **Grid drift**: `stepErrNg`, `GridDriftNg`, the classes `HierDriftGen_Expand`,
  `HierDriftGen_UStep`, and `gridDriftNg_at`.  Besides these classes they take the link
  `HierDriftGen_KLink` (`Cm.KI ∘ KLloopOf = Cm.K`): `predIncNg` reads the `K` field and the
  `𝒦`-step the `KI` field.
* **Envelope**: `exists_norm_KI_le_wing`.

Private band helpers are reused by `open private`; the ones that read `SB`, `KLK`, `treeEqRhs`,
`Ugen`, `uKer` are copied.
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

/-! ### 1. The polarization of `treeEqRhsS` and the coupling algebra

Copies of the band statements of `Induction/HierAlgebra` with the kernel `SB d L g` replaced by an arbitrary matrix `S`
(`HierAlgebra_two_le_length_cutGlueL`, `HierAlgebra_two_le_length_cutGlueR`, `HierAlgebra_length_cutGlueL_lt` are `S`-free and reused by `open private`);
`norm_primBilS_le` needs the row-sum bound `Σ_b ‖S a b‖ ≤ 1` in place of `Σ_b ‖SB a b‖ = 1`. -/

section Bilinear

variable (d L : ℕ) [NeZero L] (W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ)

/-- The polarization of `treeEqRhs`: the same sum with independent left and right factors
(`W^2 → W^d`). -/
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

/-- The loop hierarchy and the primitive equation ((2.50) `pro_dyncalK`) share their quadratic term
`treeEqRhs`, so their difference ((3.8) `eq_L-Keee`) has exactly three summands: the two
couplings `[𝒦 ∼ (𝓛-𝒦)]` ((3.9) `DefKsimLK`) and `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` ((3.10) `def_ELKLK`). -/
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

/-- The part of the coupling in which the *left* factor is a loop of length `lK`. -/
def HierDriftGen_primBilLenS (lK : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (if (I.cutGlueL k l a).length = lK then
      K (I.cutGlueL k l a) * S a b * K' (I.cutGlueR k l b) else 0)

/-- The coupling `primBilS F G` graded by the length of the **right** factor. -/
def HierDriftGen_primBilLenRS (lK : ℕ) (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (if (I.cutGlueR k l b).length = lK then
      F (I.cutGlueL k l a) * S a b * G (I.cutGlueR k l b) else 0)

/-- `[𝒦 ∼ (𝓛-𝒦)]^{l_K}` ((3.9) `DefKsimLK`) with `D = 𝓛 - 𝒦`: both orientations, graded by
the length `l_K` of the `𝒦` loop. -/
def HierDriftGen_couplingLenS (lK : ℕ) (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  HierDriftGen_primBilLenS d L W S lK K D I + HierDriftGen_primBilLenRS d L W S lK D K I

/-- Summing the graded pieces over every possible `l_K` recovers the whole coupling
. -/
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
`∑_{l_K} [𝒦 ∼ (𝓛-𝒦)]^{l_K} = primBilS K D + primBilS D K`. -/
theorem HierDriftGen_sum_couplingLenS (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, HierDriftGen_couplingLenS d L W S lK K D I
      = primBilS d L W S K D I + primBilS d L W S D K I := by
  simp only [HierDriftGen_couplingLenS, Finset.sum_add_distrib]
  rw [HierDriftGen_sum_primBilLenS d L W S K D I hN, HierDriftGen_sum_primBilLenRS d L W S D K I hN]

/-- Both graded couplings vanish outside `2 ≤ lK ≤ I.length`. -/
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
couplings and the quadratic term `primBilS D D` ((3.8) `eq_L-Keee`, (3.9) `DefKsimLK`,
(3.10) `def_ELKLK`); the only hypothesis is `2 ≤ n`. -/
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

/-- **`norm_primBilS_le`, `d`-dimensional form** (as RBM2D `norm_primBilS_le` with `W² → W^d`,
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

/-! ### 2. The carrier pair term, the classes `HierDriftGen_KLoop`, `HierDriftGen_KTwo` and the drift identity -/

section Drift

variable {d : ℕ} {sz : Sizes d}

/-- **Class `HierDriftGen_KLoop`**: `𝒦` of the carrier solves the convolution tree equations with the carrier
kernel `Cm.S n` on `[0, 1)` (the existing `IsKLoopS`, `Loop/KLTree`). -/
def HierDriftGen_KLoop (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∃ M0 : LoopIdx (Zd d (sz.L n)) → ℂ,
    IsKLoopS d (sz.L n) (sz.W n) (Cm.S n) (PropSpin (Cm.m n)) M0 (Set.Ico (0 : ℝ) 1) (Cm.KI n)

/-- **Class `HierDriftGen_KTwo`**: the `l = 2` coupling of `𝒦_u` is `Θ^{(k)}_{u,σ}`
(`couplingLen_two_Kval_eq_thetaOp`, `HierAlgebra`; band discharge below). -/
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

/-- **`loopDrift_sub_K_deriv_ng`** (`loopDrift_sub_K_deriv_n`, over the carrier): the
matrix-level drift-minus-`∂_u𝒦` identity, from `HierDriftGen_KLoop` (the equation `∂_u 𝒦 = treeEqRhsS 𝒦`), `HierDriftGen_KTwo` (the `l = 2`
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

/-! ### 3. The carrier identities -/

/-! ### 4. One step of `𝒦` over a kernel `S` and a value family `KI`

Copies of `gdn_K_lip`, `gdn_K_step` (`Induction/GridDriftN`) with `KLK d L g W E` replaced by an arbitrary family
`KI : ℝ → LoopIdx → ℂ` solving `∂_t KI_t = treeEqRhsS S KI_t` on `[0, 1)` (the content of `HierDriftGen_KLoop`), and `SB d L g` by `S` with row sums `≤ 1`. -/

section KStep

variable {d L W : ℕ} [NeZero L] {S : Matrix (Zd d L) (Zd d L) ℂ} {KI : ℝ → LoopIdx (Zd d L) → ℂ}

/-- The `𝒦` family is Lipschitz in time with constant `W^d k² L^d B²` on `[0, v]` (uses the
derivative bound `‖treeEqRhsS (𝒦_w)(J)‖ ≤ W^d k² L^d B²`, `norm_primBilS_le`; as RBM1D `norm_Kgen_sub_le` and
RBM2D `gdn_K_lip`, with the `d`-dimensional constant). -/
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

/-- **One step of `𝒦`** (as RBM1D `K_step_n` and RBM2D
`gdn_K_step`, with the `d`-dimensional constants `W^d k² L^d = N k²`): for
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

/-! ### 5. The classes `HierDriftGen_Expand`, `HierDriftGen_UStep` and the statement `GridDriftNg` -/

section GridDef

variable {d : ℕ} {sz : Sizes d}

/-- **`stepErrNg`**: `stepErrN` with `envConst` unfolded and `etaT (E n)` read as `C.eta n`. -/
def stepErrNg (C : FlowFM sz) (n k : ℕ) (u v Δ Bk : ℝ) : ℝ :=
  16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 * (1 + (C.eta n v)⁻¹) ^ (k + 4) *
      Δ ^ ((3 : ℝ) / 2) + kStepC d (sz.L n) (sz.W n) k Bk * Δ ^ 2 +
    uStepC k Δ v * ((C.eta n u)⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) + Bk)

/-- `stepErrN` is `stepErrNg` at `bandFM` (definitional). -/
theorem bandFM_stepErrN (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (u v Δ Bk : ℝ) :
    RBM.Ind.stepErrN d (sz.L n) (sz.W n) (E n) k u v Δ Bk = stepErrNg (bandFM sz E) n k u v Δ Bk := rfl

/-- **`GridDriftNg`**: the statement `GridDriftN` over `Step2Mat`, without the hypothesis
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

/-- **Class `HierDriftGen_Expand`**: one grid step of a loop observable along the carrier walk (the drift of
`condExp_loop_drift`, `Path/LoopStep`), with the generator written as `treeEqRhsS` plus `STegtMg`. -/
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

/-- **Class `HierDriftGen_UStep`**: the row bounds of one step of the carrier kernel.  The first field is
the near-identity bound of `GridRepTailGen_Ker`; the second is the order-2 bound of the private
`gdn_row_UG`, the generator being `Step2Gen_thetaKer`. -/
def HierDriftGen_UStep (C : FlowFM sz) (n : ℕ) : Prop :=
  (∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' s t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤
      |t - s| * (1 - t)⁻¹) ∧
  (∀ (σ σ' : Bool) (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b -
        (Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b‖ ≤ Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2)

/-- **The link `𝒦 = KI ∘ KLloopOf`** (needed by
`gridDriftNg_at` because `predIncNg` reads the `K` field and the `𝒦`-step the `KI` field): band `rfl`
(`STKloop = KLK ∘ KLloopOf`). -/
def HierDriftGen_KLink (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∀ w ∈ Set.Ico (0 : ℝ) 1, ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a

end GridDef

/-! ### 6. One step of `𝒰` over the carrier kernel -/

section UStepGen

variable {d : ℕ} {sz : Sizes d}

/-- **One step of `𝒰`** (`gdn_Ugen_step_le`, in the `Step2Gen_UN` vocabulary): for `‖A‖_max ≤ M`,
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

/-! ### 7. The walk facts and the one-step theorem -/

section GridStep

variable {d : ℕ} {sz : Sizes d}

/-- Integrability of the bounded loop observable along the shifted band walk (`gdn_integrable_loopL`,
with the Hermitian shift `Ψ0` and a spectral value `z`, `|Im z| ≥ η > 0`). -/
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

/-- **`gridDriftNg_at`**: one grid step of the stochastic differential equation for the `(𝓛-𝒦)`-loops (Subsection 3.2, `subsec:DyLK`) over the carrier, with the window and the
per-index classes (`HierDriftGen_Expand`, `HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_UStep`, the row sums of `Cm.S n`, the link `KI ∘ KLloopOf = K`) at the size
index `n` only; band `gridDriftN_at`.  Proof: `P_j - Δ D_j = R₁ - R_𝒦 - R_𝒰`
(`gdn_algebra`), with `R₁` from `HierDriftGen_Expand`, `R_𝒦` from `HierDriftGen_K_step`, `R_𝒰` from `HierDriftGen_UN_step_le`, and the drift
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

end GridMain

/-! ### 8. The envelopes of `𝒦` -/

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

/-- **The envelope witness** (as RBM2D `exists_norm_Kcal_le_win` and RBM1D `exists_norm_Kval_le_win`).  Fixed `m` and `τ > 0`: for
a time sequence `v_n ∈ [0, 1)`, eventually in `n`, uniformly over `w ∈ [0, v_n]` and the
well-formed loops `J` of length in `[2, m]`, `‖𝒦_w(J)‖ ≤ N^τ η_{v_n}^{-m}`, `N = sz.size n = (W L)^d`.
RBM2D proves the bound from `Kbound_prec_uncond`, uniformly over all `(L, W, E, u, v)` with `W² L² = N`; here the
`≺` bound of `𝒦` (`STKboundgL`, Lemma 2.16 `ML:Kbound`) is a hypothesis along a single size
sequence `sz`, together with `N → ∞` (`SizeTendsto`).  The supremum over `w ∈ [0, v_n]` (RBM2D: over `u ≤ v`)
is kept.  `STKboundgL` is a `≺` statement, hence the factor `N^τ`; `W^{-d} B_{w,0} ≤ 2 η_v⁻¹` replaces
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

end RBM.BA

end
