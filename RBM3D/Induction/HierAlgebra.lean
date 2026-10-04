/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Path.DriftAlgebra
import RBM3D.Path.LoopStep

/-!
# The algebra behind the general-`n` hierarchy (ST2-28a, ticket T2095)

Port of RBM2D `Induction/HierAlgebra.lean` at commit `c9a24cf` (cited `HA:<line>`; 787 lines
there), renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`: `Z2 L → Zd d L`, `W^2 → W^d`,
`SB L → SB d L g`, `KLoop.primRhs → treeEqRhs`, `KLoop.Kcal → KLK`, `thetaSig → ThetaN`
(`cycProd`, `thetaKer`), `Theta_commute_SB → Theta_commute_SB_of_three_le`.  Everything is
finite-size algebra on loop indices `LoopIdx (Zd d L)`; there is no `∀ᶠ N` and no asymptotic
parameter.  Paper: arXiv:2507.20274, `pro_dyncalK`, `DefKsimLK` (`3_5:89`), `def_ELKLK`
(`3_5:97`), `DefTHUST` (`3_5:109`), `eq_L-Keee` (`3_5:73`).

* §1 (`RBM.Ind`): `primBil`, `primRhs_sub`, `primBilLen`, `primBilLenR`, `couplingLen`,
  `primRhs_split`, `norm_primBil_le` (the `d`-dimensional bound `W^d n² L^d B_F B_G`);
* §2: `couplingLen_two_Kval_eq_thetaOp`, the `l = 2` coupling of `𝒦_u` is `ThetaN`;
* §3 (`RBM.Gauss.Sizes`): the general-`n` pair term `STllPairN` and `loopDrift_sub_K_deriv_n`,
  the matrix-level drift-minus-`∂_u𝒦` identity in the merged `ST*` vocabulary of
  `Step2Defs` (`STLIM`, `STLKIM`, `STksimLKM`, `STelklkM`, `STegtM`).

Every other helper is `private` or prefixed `HierAlgebra_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open Finset Matrix RBM RBM.Loop RBM.Gauss RBM.Path

/-! ## 1. The polarization of `treeEqRhs` -/

section Bilinear

variable (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ)

/-- The polarization of `treeEqRhs`: the same sum with independent left and right factors
(`HA:45`, `W^2 → W^d`). -/
def primBil (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    K (I.cutGlueL k l a) * SB d L g a b * K' (I.cutGlueR k l b)

@[simp] theorem primBil_self (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBil d L W g K K I = treeEqRhs d L W g K I := rfl

theorem primBil_add_left (K₁ K₂ K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBil d L W g (K₁ + K₂) K' I = primBil d L W g K₁ K' I + primBil d L W g K₂ K' I := by
  simp only [primBil, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem primBil_add_right (K K₁ K₂ : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBil d L W g K (K₁ + K₂) I = primBil d L W g K K₁ I + primBil d L W g K K₂ I := by
  simp only [primBil, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem primBil_add_add (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBil d L W g (K + D) (K + D) I
      = primBil d L W g K K I + primBil d L W g K D I + primBil d L W g D K I
        + primBil d L W g D D I := by
  rw [primBil_add_left, primBil_add_right, primBil_add_right]
  ring

/-- The loop hierarchy and the primitive equation (`pro_dyncalK`) share their quadratic term
`treeEqRhs`, so their difference (`eq_L-Keee`, `3_5:73`) has exactly three summands: the two
couplings `[𝒦 ∼ (𝓛-𝒦)]` (`DefKsimLK`, `3_5:89`) and `𝓔^{((𝓛-𝒦)×(𝓛-𝒦))}` (`def_ELKLK`,
`3_5:97`) (`HA:70`). -/
theorem primRhs_sub (Lf K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    treeEqRhs d L W g Lf I - treeEqRhs d L W g K I
      = primBil d L W g K (Lf - K) I + primBil d L W g (Lf - K) K I
        + primBil d L W g (Lf - K) (Lf - K) I := by
  set D : LoopIdx (Zd d L) → ℂ := Lf - K with hD
  have hLf : Lf = K + D := by
    rw [hD]
    funext x
    simp
  have h1 : treeEqRhs d L W g Lf I = primBil d L W g (K + D) (K + D) I := by
    rw [← primBil_self, hLf]
  rw [h1, primBil_add_add, ← primBil_self d L W g K I]
  ring

/-- The part of the coupling in which the *left* factor is a loop of length `lK` (`HA:85`). -/
def primBilLen (lK : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (if (I.cutGlueL k l a).length = lK then
      K (I.cutGlueL k l a) * SB d L g a b * K' (I.cutGlueR k l b) else 0)

/-- The coupling `primBil F G` graded by the length of the **right** factor (`HA:91`). -/
def primBilLenR (lK : ℕ) (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    (if (I.cutGlueR k l b).length = lK then
      F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b) else 0)

/-- `[𝒦 ∼ (𝓛-𝒦)]^{l_K}` (`DefKsimLK`, `3_5:89`) with `D = 𝓛 - 𝒦`: both orientations, graded by
the length `l_K` of the `𝒦` loop (`HA:98`). -/
def couplingLen (lK : ℕ) (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  primBilLen d L W g lK K D I + primBilLenR d L W g lK D K I

omit [NeZero L] in
private theorem HierAlgebra_two_le_length_cutGlueL (I : LoopIdx (Zd d L)) (a : Zd d L) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) : 2 ≤ (I.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

omit [NeZero L] in
private theorem HierAlgebra_two_le_length_cutGlueR (I : LoopIdx (Zd d L)) (b : Zd d L) {k l : ℕ}
    (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) : 2 ≤ (I.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

omit [NeZero L] in
/-- Every `K`-loop occurring in the coupling has length at most `I.length + 1`. -/
private theorem HierAlgebra_length_cutGlueL_lt (I : LoopIdx (Zd d L)) {k l : ℕ}
    (hk : k ∈ Icc 1 I.length) (hl : l ∈ Ioc k I.length) (a : Zd d L) :
    (I.cutGlueL k l a).length < I.length + 2 := by
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]
  omega

/-- Summing the graded pieces over every possible `l_K` recovers the whole coupling
(`HA:131`). -/
theorem sum_primBilLen (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, primBilLen d L W g lK K K' I = primBil d L W g K K' I := by
  simp only [primBilLen, primBil, ← Finset.mul_sum]
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
    (fun _ => K (I.cutGlueL k l a) * SB d L g a b * K' (I.cutGlueR k l b)),
    ite_eq_left (Finset.mem_range.mpr (lt_of_lt_of_le (HierAlgebra_length_cutGlueL_lt d L I hk hl a) hN))]

theorem sum_primBilLenR (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, primBilLenR d L W g lK F G I = primBil d L W g F G I := by
  simp only [primBilLenR, primBil, ← Finset.mul_sum]
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
    (fun _ => F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b)),
    ite_eq_left (Finset.mem_range.mpr hlen)]

/-- Summing over every `l_K` gives the whole coupling:
`∑_{l_K} [𝒦 ∼ (𝓛-𝒦)]^{l_K} = primBil K D + primBil D K` (`HA:171`). -/
theorem sum_couplingLen (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {N : ℕ} (hN : I.length + 2 ≤ N) :
    ∑ lK ∈ Finset.range N, couplingLen d L W g lK K D I
      = primBil d L W g K D I + primBil d L W g D K I := by
  simp only [couplingLen, Finset.sum_add_distrib]
  rw [sum_primBilLen d L W g K D I hN, sum_primBilLenR d L W g D K I hN]

/-- Both graded couplings vanish outside `2 ≤ lK ≤ I.length` (`HA:178`). -/
theorem couplingLen_eq_zero_outside (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    {lK : ℕ} (hlK : lK < 2 ∨ I.length < lK) :
    couplingLen d L W g lK K D I = 0 := by
  have hzeroL : primBilLen d L W g lK K D I = 0 := by
    unfold primBilLen
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
  have hzeroR : primBilLenR d L W g lK D K I = 0 := by
    unfold primBilLenR
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
  rw [couplingLen, hzeroL, hzeroR, add_zero]

/-- The split of `treeEqRhs (K + D) - treeEqRhs K` into the `l_K = 2` coupling, the `l_K ≥ 3`
couplings and the quadratic term `primBil D D` (`eq_L-Keee` `3_5:73`, `DefKsimLK` `3_5:89`,
`def_ELKLK` `3_5:97`); the only hypothesis is `2 ≤ n` (`HA:214`). -/
theorem primRhs_split (K D : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L))
    (hn : 2 ≤ I.length) :
    treeEqRhs d L W g (K + D) I - treeEqRhs d L W g K I
      = couplingLen d L W g 2 K D I
        + (∑ lK ∈ Finset.Icc 3 I.length, couplingLen d L W g lK K D I)
        + primBil d L W g D D I := by
  have hDeq : (K + D) - K = D := by funext x; simp
  have hps := primRhs_sub d L W g (K + D) K I
  rw [hDeq] at hps
  have hN : I.length + 2 ≤ I.length + 2 := le_rfl
  have hsum := sum_couplingLen d L W g K D I hN
  have h2mem : (2 : ℕ) ∈ Finset.range (I.length + 2) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h2mem] at hsum
  have hsub : Finset.Icc 3 I.length ⊆ (Finset.range (I.length + 2)).erase 2 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hsum2 : ∑ lK ∈ (Finset.range (I.length + 2)).erase 2, couplingLen d L W g lK K D I
      = ∑ lK ∈ Finset.Icc 3 I.length, couplingLen d L W g lK K D I := by
    symm
    refine Finset.sum_subset hsub (fun x hx hnx => ?_)
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hnx
    exact couplingLen_eq_zero_outside d L W g K D I (by omega)
  rw [hsum2] at hsum
  rw [hps, ← hsum]

/-- Row sums of `‖S‖`: `∑_b ‖S_{ab}‖ = 1` (from the `NNReal` statement `sum_nnnorm_SB_row`,
`HA:243`). -/
private theorem HierAlgebra_sum_norm_SB_row (hL : 3 ≤ L) (a : Zd d L) :
    ∑ b : Zd d L, ‖SB d L g a b‖ = 1 := by
  have h := sum_nnnorm_SB_row d L g hL a
  have h' := congrArg (fun x : NNReal => (x : ℝ)) h
  simpa using h'

/-- **`norm_primBil_le`, `d`-dimensional form** (RBM2D `HA:252` with `W² → W^d`,
`L² → L^d = card (Zd d L)`): `primBil F G I` is bounded by the product of separate envelopes
`BF, BG` on `F, G` at the cut sub-loop lengths `2 … I.length`, with the constant
`W^d n² L^d B_F B_G`. -/
theorem norm_primBil_le (hL : 3 ≤ L) (F G : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hI : I.WF) {BF BG : ℝ} (hBF0 : 0 ≤ BF) (hBG0 : 0 ≤ BG)
    (hBF : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ BF)
    (hBG : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ BG) :
    ‖primBil d L W g F G I‖ ≤ (W : ℝ) ^ d * (I.length : ℝ) ^ 2 * (L : ℝ) ^ d * BF * BG := by
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ d := by positivity
  have hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖∑ a : Zd d L, ∑ b : Zd d L,
          F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b)‖
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
            F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b)‖
        ≤ ∑ a : Zd d L, ∑ b : Zd d L,
            ‖F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Zd d L, ∑ b : Zd d L, BF * BG * ‖SB d L g a b‖ := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul]
          calc ‖F (I.cutGlueL k l a)‖ * ‖SB d L g a b‖ * ‖G (I.cutGlueR k l b)‖
              ≤ BF * ‖SB d L g a b‖ * BG :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hBFl a) (norm_nonneg _)) (hBGr b)
                  (norm_nonneg _) (by positivity)
            _ = BF * BG * ‖SB d L g a b‖ := by ring
      _ = ∑ _a : Zd d L, BF * BG := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum, HierAlgebra_sum_norm_SB_row d L g hL a, mul_one]
      _ = (L : ℝ) ^ d * BF * BG := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          ring
  calc ‖primBil d L W g F G I‖
      ≤ (W : ℝ) ^ d * ∑ _k ∈ Icc 1 I.length, ∑ _l ∈ Ioc _k I.length, (L : ℝ) ^ d * BF * BG := by
        rw [primBil, norm_mul, norm_pow, Complex.norm_natCast]
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


/-! ## 2. The `l = 2` coupling is the generator `Θ^{(k)}_{u,σ}` (`DefTHUST`, `3_5:109`) -/

section Coupling2

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem HierAlgebra_take_one_drop {α : Type*} (l : List α) (d : α) {m : ℕ}
    (h : m < l.length) : (l.drop m).take 1 = [l.getD m d] := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
  rfl

private theorem HierAlgebra_take_two_drop {α : Type*} (l : List α) (d : α) {m m' : ℕ}
    (hm : m + 1 = m') (h : m' < l.length) :
    (l.drop m).take 2 = [l.getD m d, l.getD m' d] := by
  subst hm
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h]
  rfl

private theorem HierAlgebra_drop_last {α : Type*} (l : List α) (d : α) {m : ℕ}
    (h : m + 1 = l.length) : l.drop m = [l.getD m d] := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega),
    List.getD_eq_getElem _ _ (by omega)]

omit [NeZero L] in
private theorem HierAlgebra_cutGlueL_succ_eq (I : LoopIdx (Zd d L)) {k : ℕ} (hk : 1 ≤ k)
    (hk' : k + 1 ≤ I.length) (a : Zd d L) :
    I.cutGlueL k (k + 1) a = ⟨I.σ, I.a.set (k - 1) a⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hkm : k - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change I.σ.take k ++ I.σ.drop (k + 1 - 1) = I.σ
    simp
  · change I.a.take (k - 1) ++ a :: I.a.drop (k + 1 - 1) = I.a.set (k - 1) a
    rw [List.set_eq_take_cons_drop a hkm, show k + 1 - 1 = k - 1 + 1 by omega]

omit [NeZero L] in
private theorem HierAlgebra_cutGlueR_succ_eq (I : LoopIdx (Zd d L)) (hwf : I.WF) {k : ℕ}
    (hk : 1 ≤ k) (hk' : k + 1 ≤ I.length) (b : Zd d L) :
    I.cutGlueR k (k + 1) b
      = ⟨[I.σ.getD (k - 1) true, I.σ.getD k true], [I.a.getD (k - 1) 0, b]⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have h2 : k < I.σ.length := by rw [hσ]; omega
  have h1' : k - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change (I.σ.drop (k - 1)).take (k + 1 - k + 1) = _
    rw [show k + 1 - k + 1 = 2 by omega,
      HierAlgebra_take_two_drop I.σ true (by omega : k - 1 + 1 = k) h2]
  · change (I.a.drop (k - 1)).take (k + 1 - k) ++ [b] = _
    rw [show k + 1 - k = 1 by omega, HierAlgebra_take_one_drop I.a 0 h1']
    rfl

omit [NeZero L] in
private theorem HierAlgebra_cutGlueL_one_eq (I : LoopIdx (Zd d L)) (hwf : I.WF)
    (hn : 2 ≤ I.length) (a : Zd d L) :
    I.cutGlueL 1 I.length a
      = ⟨[I.σ.getD 0 true, I.σ.getD (I.length - 1) true], [a, I.a.getD (I.length - 1) 0]⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have h0 : 0 < I.σ.length := by rw [hσ]; omega
  have hm : I.length - 1 + 1 = I.σ.length := by rw [hσ]; omega
  have hm' : I.length - 1 + 1 = I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change I.σ.take 1 ++ I.σ.drop (I.length - 1) = _
    rw [HierAlgebra_drop_last I.σ true hm, show I.σ.take 1 = (I.σ.drop 0).take 1 by simp,
      HierAlgebra_take_one_drop I.σ true h0]
    rfl
  · change I.a.take 0 ++ a :: I.a.drop (I.length - 1) = _
    rw [HierAlgebra_drop_last I.a 0 hm']
    rfl

omit [NeZero L] in
private theorem HierAlgebra_cutGlueR_one_eq (I : LoopIdx (Zd d L)) (hwf : I.WF)
    (hn : 2 ≤ I.length) (b : Zd d L) :
    I.cutGlueR 1 I.length b = ⟨I.σ, I.a.set (I.length - 1) b⟩ := by
  have hlen : I.a.length = I.length := rfl
  have hσ : I.σ.length = I.length := hwf.trans hlen.symm
  have hm' : I.length - 1 < I.a.length := by rw [hlen]; omega
  refine LoopIdx.ext ?_ ?_
  · change (I.σ.drop 0).take (I.length - 1 + 1) = I.σ
    rw [List.drop_zero, show I.length - 1 + 1 = I.length by omega,
      List.take_of_length_le (by rw [hσ])]
  · change (I.a.drop 0).take (I.length - 1) ++ [b] = _
    rw [List.drop_zero, List.set_eq_take_cons_drop b hm',
      show I.length - 1 + 1 = I.length by omega,
      List.drop_eq_nil_of_le (by rw [hlen])]

section Two

variable (W : ℕ)

/-- Only the wrap-around cut `(k,l) = (1,n)` has a left chain of length 2 (`HA:397`). -/
private theorem HierAlgebra_primBilLen_two_eq (K D : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hn : 2 ≤ I.length) :
    primBilLen d L W g 2 K D I
      = (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
          K (I.cutGlueL 1 I.length a) * SB d L g a b * D (I.cutGlueR 1 I.length b) := by
  have hlenL : ∀ (k l : ℕ) (a : Zd d L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueL k l a).length = k + I.length - l + 1 :=
    fun k l a h1 h2 h3 => LoopIdx.length_cutGlueL I a h1 h2 h3
  rw [primBilLen]
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (by simp [Finset.mem_Icc]; omega)]
  · rw [Finset.sum_eq_single_of_mem I.length (by simp [Finset.mem_Ioc]; omega)]
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [ite_eq_left (by rw [hlenL 1 I.length a le_rfl (by omega) le_rfl]; omega)]
    · intro l hl hne
      rw [Finset.mem_Ioc] at hl
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [ite_eq_right (by rw [hlenL 1 l a le_rfl hl.1 hl.2]; omega)]
  · intro k hk hne
    rw [Finset.mem_Icc] at hk
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (by rw [hlenL k l a hk.1 hl.1 hl.2]; omega)]

/-- Only the adjacent cuts `(k, k+1)` have a right chain of length 2 (`HA:423`). -/
private theorem HierAlgebra_primBilLenR_two_eq (F G : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) (hn : 2 ≤ I.length) :
    primBilLenR d L W g 2 F G I
      = (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 (I.length - 1), ∑ a : Zd d L, ∑ b : Zd d L,
          F (I.cutGlueL k (k + 1) a) * SB d L g a b * G (I.cutGlueR k (k + 1) b) := by
  have hlenR : ∀ (k l : ℕ) (b : Zd d L), 1 ≤ k → k < l → l ≤ I.length →
      (I.cutGlueR k l b).length = l - k + 1 :=
    fun k l b h1 h2 h3 => LoopIdx.length_cutGlueR I b h1 h2 h3
  rw [primBilLenR]
  congr 1
  have key : ∀ k ∈ Finset.Icc 1 I.length,
      (∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        (if (I.cutGlueR k l b).length = 2 then
          F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b) else 0))
      = if k ∈ Finset.Icc 1 (I.length - 1) then
          (∑ a : Zd d L, ∑ b : Zd d L,
            F (I.cutGlueL k (k + 1) a) * SB d L g a b * G (I.cutGlueR k (k + 1) b)) else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hlt : k < I.length
    · rw [ite_eq_left (by rw [Finset.mem_Icc]; omega)]
      rw [Finset.sum_eq_single_of_mem (k + 1) (by rw [Finset.mem_Ioc]; omega)]
      · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [ite_eq_left (by rw [hlenR k (k + 1) b hk.1 (by omega) (by omega)]; omega)]
      · intro l hl hne
        rw [Finset.mem_Ioc] at hl
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right (by rw [hlenR k l b hk.1 hl.1 hl.2]; omega)]
    · have hkn : k = I.length := by omega
      subst hkn
      rw [ite_eq_right (by rw [Finset.mem_Icc]; omega), Finset.Ioc_self, Finset.sum_empty]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (by intro x hx; rw [Finset.mem_Icc] at *; omega)]

end Two

/-- Reindex `∑_{k=1}^{n}` as `∑_{k=0}^{n-1}`. -/
private theorem HierAlgebra_sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : ℕ → M) : ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- The cyclic edge weight `ξ_i = m(σ_i) m(σ_{i+1 mod n})` of a loop index (`HA:464`). -/
private def HierAlgebra_xiLoop (m : Bool → ℂ) (I : LoopIdx (Zd d L)) (i : ℕ) : ℂ :=
  m (I.σ.getD i true) * m (I.σ.getD ((i + 1) % I.length) true)

section Three

variable (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ) (K D : LoopIdx (Zd d L) → ℂ)

private theorem HierAlgebra_thetaR_term
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo d L W g m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (Zd d L)) (hwf : I.WF) {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ I.length) :
    (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        D (I.cutGlueL k (k + 1) a) * SB d L g a b * K (I.cutGlueR k (k + 1) b)
      = ∑ c : Zd d L,
          HierAlgebra_xiLoop m I (k - 1)
            * (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (k - 1)) * SB d L g)
                (I.a.getD (k - 1) 0) c
            * D ⟨I.σ, I.a.set (k - 1) c⟩ := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d hW'
  have hxi : HierAlgebra_xiLoop m I (k - 1)
      = m (I.σ.getD (k - 1) true) * m (I.σ.getD k true) := by
    rw [HierAlgebra_xiLoop, show (k - 1 + 1) % I.length = k by
      rw [show k - 1 + 1 = k by omega, Nat.mod_eq_of_lt (by omega)]]
  have hinner : ∀ b : Zd d L, K (I.cutGlueR k (k + 1) b)
      = ((W : ℂ) ^ d)⁻¹ * HierAlgebra_xiLoop m I (k - 1)
          * Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (k - 1)) (I.a.getD (k - 1) 0) b := by
    intro b
    rw [HierAlgebra_cutGlueR_succ_eq I hwf hk hk', hK, kTwo, hxi]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [HierAlgebra_cutGlueL_succ_eq I hk hk', Finset.mul_sum]
  calc ∑ b : Zd d L, (W : ℂ) ^ d * (D ⟨I.σ, I.a.set (k - 1) a⟩ * SB d L g a b
          * K (I.cutGlueR k (k + 1) b))
      = ∑ b : Zd d L, (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (k - 1))
            (I.a.getD (k - 1) 0) b
            * SB d L g b a) * (HierAlgebra_xiLoop m I (k - 1) * D ⟨I.σ, I.a.set (k - 1) a⟩) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hinner b, show SB d L g b a = SB d L g a b from
          congrFun (congrFun (SB_transpose d L g) a) b]
        field_simp
    _ = HierAlgebra_xiLoop m I (k - 1)
          * (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (k - 1)) * SB d L g)
              (I.a.getD (k - 1) 0) a
          * D ⟨I.σ, I.a.set (k - 1) a⟩ := by
        rw [← Finset.sum_mul, Matrix.mul_apply]
        ring

private theorem HierAlgebra_thetaL_term (hL : 3 ≤ L)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo d L W g m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (Zd d L)) (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1)‖ < 1) :
    (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        K (I.cutGlueL 1 I.length a) * SB d L g a b * D (I.cutGlueR 1 I.length b)
      = ∑ c : Zd d L,
          HierAlgebra_xiLoop m I (I.length - 1)
            * (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1)) * SB d L g)
                (I.a.getD (I.length - 1) 0) c
            * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d hW'
  have hxi : m (I.σ.getD 0 true) * m (I.σ.getD (I.length - 1) true)
      = HierAlgebra_xiLoop m I (I.length - 1) := by
    rw [HierAlgebra_xiLoop, show (I.length - 1 + 1) % I.length = 0 by
      rw [show I.length - 1 + 1 = I.length by omega, Nat.mod_self]]
    ring
  have hsym : ∀ p q : Zd d L, Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1)) p q
      = Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1)) q p := fun p q =>
    congrFun (congrFun (Theta_transpose_of_three_le hL hξ) q) p
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [HierAlgebra_cutGlueR_one_eq I hwf hn]
  have step : ∀ a : Zd d L,
      (W : ℂ) ^ d * (K (I.cutGlueL 1 I.length a) * SB d L g a b
          * D ⟨I.σ, I.a.set (I.length - 1) b⟩)
        = (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1))
              (I.a.getD (I.length - 1) 0) a
            * SB d L g a b)
          * (HierAlgebra_xiLoop m I (I.length - 1) * D ⟨I.σ, I.a.set (I.length - 1) b⟩) := by
    intro a
    rw [HierAlgebra_cutGlueL_one_eq I hwf hn, hK, kTwo, hxi,
      hsym a (I.a.getD (I.length - 1) 0)]
    field_simp
  rw [Finset.sum_congr rfl fun a _ => step a, ← Finset.sum_mul, Matrix.mul_apply]
  ring

private theorem HierAlgebra_couplingLen_two_eq_sum (hL : 3 ≤ L)
    (hK : ∀ σ₁ σ₂ a₁ a₂, K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = kTwo d L W g m t σ₁ σ₂ a₁ a₂)
    (I : LoopIdx (Zd d L)) (hwf : I.WF) (hn : 2 ≤ I.length)
    (hξ : ‖(t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1)‖ < 1) :
    couplingLen d L W g 2 K D I
      = ∑ i ∈ Finset.range I.length, ∑ c : Zd d L,
          HierAlgebra_xiLoop m I i
            * (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I i) * SB d L g) (I.a.getD i 0) c
            * D ⟨I.σ, I.a.set i c⟩ := by
  have hR : primBilLenR d L W g 2 D K I
      = ∑ i ∈ Finset.range (I.length - 1), ∑ c : Zd d L,
          HierAlgebra_xiLoop m I i
            * (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I i) * SB d L g) (I.a.getD i 0) c
            * D ⟨I.σ, I.a.set i c⟩ := by
    rw [HierAlgebra_primBilLenR_two_eq W D K I hn, Finset.mul_sum,
      HierAlgebra_sum_Icc_one_eq_range (I.length - 1)
        (fun k => (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
          D (I.cutGlueL k (k + 1) a) * SB d L g a b * K (I.cutGlueR k (k + 1) b))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [HierAlgebra_thetaR_term W m t K D hK I hwf (by omega : 1 ≤ i + 1) (by omega)]
    simp
  have hL2 : primBilLen d L W g 2 K D I
      = ∑ c : Zd d L,
          HierAlgebra_xiLoop m I (I.length - 1)
            * (Theta d L g ((t : ℂ) * HierAlgebra_xiLoop m I (I.length - 1)) * SB d L g)
                (I.a.getD (I.length - 1) 0) c
            * D ⟨I.σ, I.a.set (I.length - 1) c⟩ := by
    rw [HierAlgebra_primBilLen_two_eq W K D I hn,
      HierAlgebra_thetaL_term W m t K D hL hK I hwf hn hξ]
  rw [couplingLen, hR, hL2,
    show I.length = (I.length - 1) + 1 by omega, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  exact add_comm _ _

end Three

/-- `List.set` on a `List.ofFn` is `Function.update` (`HA:575`). -/
private theorem HierAlgebra_set_ofFn_eq_ofFn_update {α : Type*} {n : ℕ} (a : Fin n → α)
    (i : Fin n) (c : α) :
    (List.ofFn a).set (i : ℕ) c = List.ofFn (Function.update a i c) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.length_set, List.length_ofFn] at h1
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  by_cases hij : (i : ℕ) = j
  · subst hij
    simp [Function.update_self]
  · rw [ite_eq_right hij, Function.update_apply,
      ite_eq_right (by simp only [Fin.ext_iff]; omega)]

end Coupling2


/-- **The `l_K = 2` coupling of `𝒦_u` against any `D`, at every loop length `k ≥ 2` and every sign
vector, is `Θ^{(k)}_{u,σ}D`** (`ThetaN`, `DefTHUST` `3_5:109`; the general-`k` form of the
sentence after `def_Ustz_2`; `HA:602`).  The only hypotheses are `3 ≤ L`, `|E| ≤ 2`,
`0 ≤ u < 1`, `NeZero W`, `2 ≤ k`; `m(σ_i)` is `mSigma E (σ i)`. -/
theorem couplingLen_two_Kval_eq_thetaOp (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L)
    (E : ℝ) (hE : |E| ≤ 2) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (D : LoopIdx (Zd d L) → ℂ) {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    couplingLen d L W g 2 (KLK d L g W E u) D (loopOf σ a)
      = ThetaN d L g (fun i => mSigma E (σ i)) u (fun v => D (loopOf σ v)) a := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hwf : (loopOf σ a).WF := by
    change (List.ofFn σ).length = (List.ofFn a).length
    simp
  have hlen : (loopOf σ a).length = k' + 1 := by
    change (List.ofFn a).length = k' + 1
    simp
  have hK : ∀ s₁ s₂ (x y : Zd d L), KLK d L g W E u ⟨[s₁, s₂], [x, y]⟩
      = kTwo d L W g (mSigma E) u s₁ s₂ x y := fun s₁ s₂ x y =>
    KLK_two_eq_kTwo d L g W E u s₁ s₂ x y
  have hget : ∀ (j : ℕ) (hj : j < k' + 1), (List.ofFn σ).getD j true = σ ⟨j, hj⟩ := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  have hrot : ∀ i : Fin (k' + 1), (⟨((i : ℕ) + 1) % (k' + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k' + 1))
      = finRotate (k' + 1) i := by
    intro i
    refine Fin.ext ?_
    rw [coe_finRotate]
    split_ifs with h
    · have : (i : ℕ) = k' := by rw [h]; rfl
      simp [this]
    · have : (i : ℕ) ≠ k' := fun h' => h (Fin.ext (by simpa using h'))
      change ((i : ℕ) + 1) % (k' + 1) = (i : ℕ) + 1
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
  have hxi : ∀ i : Fin (k' + 1), HierAlgebra_xiLoop (mSigma E) (loopOf σ a) (i : ℕ)
      = cycProd (fun i => mSigma E (σ i)) i := by
    intro i
    unfold HierAlgebra_xiLoop cycProd
    change mSigma E ((List.ofFn σ).getD (i : ℕ) true)
        * mSigma E ((List.ofFn σ).getD (((i : ℕ) + 1) % (loopOf σ a).length) true) = _
    rw [hlen, hget i i.isLt, hget _ (Nat.mod_lt _ (by omega)), hrot i]
  have hξ : ‖(u : ℂ) * HierAlgebra_xiLoop (mSigma E) (loopOf σ a) ((loopOf σ a).length - 1)‖ < 1 := by
    unfold HierAlgebra_xiLoop
    exact norm_mul_mSigma_lt_one hE hu0 hu1 _ _
  rw [HierAlgebra_couplingLen_two_eq_sum W (mSigma E) u (KLK d L g W E u) D hL hK (loopOf σ a)
    hwf (by rw [hlen]; omega) hξ, hlen]
  refine (Finset.sum_range _).trans ?_
  unfold ThetaN
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  have hξ' : ‖(u : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 :=
    norm_mul_mSigma_lt_one hE hu0 hu1 (σ i) (σ (finRotate (k' + 1) i))
  have hcomm := (Theta_commute_SB_of_three_le (d := d) (g := g) hL hξ').eq
  have hget' : (List.ofFn a).getD (i : ℕ) 0 = a i := by
    rw [List.getD_eq_getElem (List.ofFn a) 0 (by rw [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]
  rw [hxi i, hcomm]
  simp only [thetaKer, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  change _ * (SB d L g * Theta d L g _) ((List.ofFn a).getD (i : ℕ) 0) c
      * D ⟨List.ofFn σ, (List.ofFn a).set (i : ℕ) c⟩ = _
  rw [hget', HierAlgebra_set_ofFn_eq_ofFn_update]
  rfl

end RBM.Ind

/-! ## 3. The drift-minus-`∂_u𝒦` identity at matrix level, in the `ST*` vocabulary -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Ind

section MatrixLevel

variable {d : ℕ} (sz : Sizes d)

/-- **The pair-cut term of the loop generator, general length** (`eq:mainStoflow`, `1_2`, drift
part): `W^d Σ_{k<l} Σ_{a,b} 𝓛(cutL^{(a)}_{k,l} I) S^{(B)}_{ab} 𝓛(cutR^{(b)}_{k,l} I)` for a fine
matrix `M` (RBM2D `llPairN`, `Induction/HierVocab.lean:539`; at length `2` it is the first term of
`LoopGenN2`).  `STllPairN = treeEqRhs` of the loop values `STLIM`. -/
def STllPairN (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      STLIM sz n E u M (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
        STLIM sz n E u M (I.cutGlueR k l' b)

theorem STllPairN_eq_treeEqRhs (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) :
    sz.STllPairN n E u M I = treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (sz.STLIM n E u M) I := rfl

end MatrixLevel

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

private theorem HierAlgebra_couplingLen_eq_ksimLK {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (l : ℕ)
    (I : LoopIdx (Zd d (sz.L n))) :
    couplingLen d (sz.L n) (sz.W n) (sz.lam n) l (KLK d (sz.L n) (sz.lam n) (sz.W n) E u)
      (sz.STLKIM n E u M) I = sz.STksimLKM n E u M l I := by
  simp only [couplingLen, primBilLen, primBilLenR, STksimLKM, Finset.sum_add_distrib, mul_add]
  ring

/-- **The general-`k` drift-minus-`∂_u𝒦` identity at matrix level** (RBM2D `HA:663`, RBM1D
`loopDrift_sub_K_deriv_n`; `d`-dimensional, in the `ST*` vocabulary).  With `𝓛 = STLIM`,
`𝒦 = KLK`, `𝓛 - 𝒦 = STLKIM`, for an arbitrary matrix `M` (no `genMat` and no Hermitian
hypothesis: the identity is algebra on the values `𝓛_M(J)`):
`(pair + 𝓔^{G̃})(I) - ∂_u𝒦_u(I) = Θ^{(k)}_{u,σ}(𝓛-𝒦) + Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{G̃}`
at `I = loopOf σ a`.  With `genMat(𝓛_I) = pair + 𝓔^{G̃}` (`STLoopGenNForm`) this is
`HierarchyN`. -/
theorem loopDrift_sub_K_deriv_n {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (hE : |E| < 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    (sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a))
        - deriv (fun v : ℝ => sz.STKloop n E v σ a) u
      = ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) u
            (fun b => sz.STLKIM n E u M (loopOf σ b)) a
          + ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a)
          + sz.STelklkM n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a) := by
  have hwf : (loopOf σ a).WF := by
    change (List.ofFn σ).length = (List.ofFn a).length
    simp
  have hlen : (loopOf σ a).length = k := by
    change (List.ofFn a).length = k
    simp
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hprim := (KLK_isKLoop d (sz.L n) (sz.W n) (sz.lam n) E (sz.three_le_L n) hW1 hE).1 u
    ⟨hu0, hu1⟩ (loopOf σ a) hwf (by rw [hlen]; exact hk)
  have hderiv : deriv (fun v : ℝ => sz.STKloop n E v σ a) u
      = treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) E u)
          (loopOf σ a) := hprim.deriv
  have hKD : KLK d (sz.L n) (sz.lam n) (sz.W n) E u + sz.STLKIM n E u M = sz.STLIM n E u M := by
    funext x
    simp [STLKIM]
  have hsplit := primRhs_split d (sz.L n) (sz.W n) (sz.lam n)
    (KLK d (sz.L n) (sz.lam n) (sz.W n) E u) (sz.STLKIM n E u M) (loopOf σ a)
    (by rw [hlen]; exact hk)
  rw [hKD, hlen,
    couplingLen_two_Kval_eq_thetaOp d (sz.L n) (sz.W n) (sz.lam n) (sz.three_le_L n) E hE.le u hu0
      hu1 (sz.STLKIM n E u M) hk σ a] at hsplit
  have hsum : ∑ l ∈ Finset.Icc 3 k, couplingLen d (sz.L n) (sz.W n) (sz.lam n) l
        (KLK d (sz.L n) (sz.lam n) (sz.W n) E u) (sz.STLKIM n E u M) (loopOf σ a)
      = ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a) :=
    Finset.sum_congr rfl fun l _ => HierAlgebra_couplingLen_eq_ksimLK sz n E u M l _
  have hEl : primBil d (sz.L n) (sz.W n) (sz.lam n) (sz.STLKIM n E u M) (sz.STLKIM n E u M)
      (loopOf σ a) = sz.STelklkM n E u M (loopOf σ a) := rfl
  rw [hsum, hEl] at hsplit
  rw [hderiv, STllPairN_eq_treeEqRhs]
  linear_combination hsplit

/-! ## 4. Compiled nonempty instances

Generic part at `d = 3`, `L = 3`, `W = 2`, `g = 1/2` (the loop `((+,-),(0,0))` of length `2` and the
alternating loop `(+,-,+)` of length `3` with labels `(0,1,2)`); the `ST*` identity at the merged
admissible sequence `sz0` (`RBM.Gauss.SizesInst.sz0`: `d = 3`, `L_0 = 4`, `W_0 = 32`,
`lam_0 = 1/64`), size index `0`, `E = 0`, `u = 1/2`, `M = 1`, loop length `k = 3`.  Every
deterministic hypothesis is discharged. -/

section Instances

/-- The loop `((+,-),((0,0,0),(0,0,0)))` of length `2` on `Z_3^3`. -/
private def HierAlgebra_I0 : LoopIdx (Zd 3 3) := ⟨[true, false], [0, 0]⟩

private theorem HierAlgebra_I0_wf : HierAlgebra_I0.WF := rfl

private theorem HierAlgebra_I0_length : HierAlgebra_I0.length = 2 := rfl

/-- `norm_primBil_le` at `d = 3`, `L = 3`, `W = 2`, `n = 2`, `F = G = 1`, `B_F = B_G = 1`: the
bound `W^d n² L^d B_F B_G = 8 · 4 · 27 = 864`. -/
theorem HierAlgebra_check_norm_primBil_le :
    ‖primBil 3 3 2 (1 / 2) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) HierAlgebra_I0‖ ≤ 864 := by
  have h := norm_primBil_le 3 3 2 (1 / 2) (le_refl 3) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
    HierAlgebra_I0 HierAlgebra_I0_wf (zero_le_one : (0 : ℝ) ≤ 1) (zero_le_one : (0 : ℝ) ≤ 1)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)
  rw [HierAlgebra_I0_length] at h
  norm_num [card_Zd] at h
  exact h

/-- The value of `primBil` at that instance is `W^d · Σ_{a,b} S_{ab} = 8 · 27 = 216`: nonzero and
below the bound `864`. -/
theorem HierAlgebra_check_primBil_value :
    primBil 3 3 2 (1 / 2) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) HierAlgebra_I0 = 216 := by
  unfold primBil
  rw [HierAlgebra_I0_length]
  have h1 : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  have h2 : (Finset.Ioc 1 2 : Finset ℕ) = {2} := by decide
  have h3 : (Finset.Ioc 2 2 : Finset ℕ) = ∅ := by decide
  rw [h1, Finset.sum_pair (by decide), h2, h3]
  simp only [one_mul, mul_one, Finset.sum_singleton, Finset.sum_empty, add_zero]
  rw [Finset.sum_congr rfl fun x _ => sum_SB_row 3 3 (1 / 2) (le_refl 3) x]
  simp
  norm_num

/-- `primRhs_split` at the length-`2` loop (every `K`, `D`). -/
theorem HierAlgebra_check_primRhs_split (K D : LoopIdx (Zd 3 3) → ℂ) :
    treeEqRhs 3 3 2 (1 / 2) (K + D) HierAlgebra_I0 - treeEqRhs 3 3 2 (1 / 2) K HierAlgebra_I0
      = couplingLen 3 3 2 (1 / 2) 2 K D HierAlgebra_I0
        + (∑ lK ∈ Finset.Icc 3 HierAlgebra_I0.length, couplingLen 3 3 2 (1 / 2) lK K D HierAlgebra_I0)
        + primBil 3 3 2 (1 / 2) D D HierAlgebra_I0 :=
  primRhs_split 3 3 2 (1 / 2) K D HierAlgebra_I0 (by rw [HierAlgebra_I0_length])

/-- `couplingLen_two_Kval_eq_thetaOp` at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `u = 1/2`,
`k = 3`, `σ = (+,-,+)`, `a = (0,1,2)`, for every `D`. -/
theorem HierAlgebra_check_couplingLen_two (D : LoopIdx (Zd 3 3) → ℂ) :
    couplingLen 3 3 2 (1 / 2) 2 (KLK 3 3 (1 / 2) 2 0 (1 / 2)) D
        (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2])
      = ThetaN 3 3 (1 / 2) (fun i => mSigma 0 (![true, false, true] i)) (1 / 2)
          (fun v => D (loopOf ![true, false, true] v)) ![(0 : Zd 3 3), 1, 2] :=
  couplingLen_two_Kval_eq_thetaOp 3 3 2 (1 / 2) (le_refl 3) 0 (by norm_num) (1 / 2)
    (by norm_num) (by norm_num) D (k := 3) (by norm_num) _ _

/-- The remaining public lemmas of §1 at the length-`2` loop (every `K`, `K'`, `D`): bilinearity,
`primRhs_sub`, the grading sums over `range 4` (`I.length + 2 = 4`) and the vanishing outside
`2 ≤ l_K ≤ I.length` (`l_K = 5`). -/
theorem HierAlgebra_check_algebra (K K' D : LoopIdx (Zd 3 3) → ℂ) :
    primBil 3 3 2 (1 / 2) (K + K') D HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) K D HierAlgebra_I0 + primBil 3 3 2 (1 / 2) K' D HierAlgebra_I0 ∧
      primBil 3 3 2 (1 / 2) D (K + K') HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) D K HierAlgebra_I0 + primBil 3 3 2 (1 / 2) D K' HierAlgebra_I0 ∧
      primBil 3 3 2 (1 / 2) (K + D) (K + D) HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) K K HierAlgebra_I0 + primBil 3 3 2 (1 / 2) K D HierAlgebra_I0
          + primBil 3 3 2 (1 / 2) D K HierAlgebra_I0 + primBil 3 3 2 (1 / 2) D D HierAlgebra_I0 ∧
      treeEqRhs 3 3 2 (1 / 2) K HierAlgebra_I0 - treeEqRhs 3 3 2 (1 / 2) D HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) D (K - D) HierAlgebra_I0
          + primBil 3 3 2 (1 / 2) (K - D) D HierAlgebra_I0
          + primBil 3 3 2 (1 / 2) (K - D) (K - D) HierAlgebra_I0 ∧
      ∑ lK ∈ Finset.range 4, primBilLen 3 3 2 (1 / 2) lK K D HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) K D HierAlgebra_I0 ∧
      ∑ lK ∈ Finset.range 4, primBilLenR 3 3 2 (1 / 2) lK K D HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) K D HierAlgebra_I0 ∧
      ∑ lK ∈ Finset.range 4, couplingLen 3 3 2 (1 / 2) lK K D HierAlgebra_I0
        = primBil 3 3 2 (1 / 2) K D HierAlgebra_I0 + primBil 3 3 2 (1 / 2) D K HierAlgebra_I0 ∧
      couplingLen 3 3 2 (1 / 2) 5 K D HierAlgebra_I0 = 0 :=
  ⟨primBil_add_left 3 3 2 (1 / 2) K K' D _, primBil_add_right 3 3 2 (1 / 2) D K K' _,
    primBil_add_add 3 3 2 (1 / 2) K D _, primRhs_sub 3 3 2 (1 / 2) K D _,
    sum_primBilLen 3 3 2 (1 / 2) K D _ (by decide), sum_primBilLenR 3 3 2 (1 / 2) K D _ (by decide),
    sum_couplingLen 3 3 2 (1 / 2) K D _ (by decide),
    couplingLen_eq_zero_outside 3 3 2 (1 / 2) K D _ (by decide)⟩

open RBM.Gauss.SizesInst in
/-- **`loopDrift_sub_K_deriv_n` at `sz0`**, `n = 0`, `E = 0`, `u = 1/2`, `M = 1`, `k = 3`,
`σ = (+,-,+)`, `a = (0,1,2)` (the labels differ in `Z_4^3`). -/
theorem HierAlgebra_check_loopDrift_sz0 :
    (sz0.STllPairN 0 0 (1 / 2)
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
        + sz0.STegtM 0 0 (1 / 2)
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]))
        - deriv (fun v : ℝ => sz0.STKloop 0 0 v ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
          (1 / 2)
      = ThetaN 3 (sz0.L 0) (sz0.lam 0) (fun i => mSigma 0 (![true, false, true] i)) (1 / 2)
            (fun b => sz0.STLKIM 0 0 (1 / 2)
              (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
              (loopOf ![true, false, true] b)) ![(0 : Zd 3 (sz0.L 0)), 1, 2]
          + ∑ l ∈ Finset.Icc 3 3, sz0.STksimLKM 0 0 (1 / 2)
              (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) l
              (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
          + sz0.STelklkM 0 0 (1 / 2)
              (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
              (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2])
          + sz0.STegtM 0 0 (1 / 2)
              (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
              (loopOf ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]) :=
  loopDrift_sub_K_deriv_n sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    (k := 3) (by norm_num) _ _

end Instances

end RBM.Ind

end

#print axioms RBM.Ind.primBil_add_add
#print axioms RBM.Ind.primRhs_sub
#print axioms RBM.Ind.sum_primBilLen
#print axioms RBM.Ind.sum_primBilLenR
#print axioms RBM.Ind.sum_couplingLen
#print axioms RBM.Ind.couplingLen_eq_zero_outside
#print axioms RBM.Ind.primRhs_split
#print axioms RBM.Ind.norm_primBil_le
#print axioms RBM.Ind.couplingLen_two_Kval_eq_thetaOp
#print axioms RBM.Ind.loopDrift_sub_K_deriv_n
