/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Data.Set.Finite.List
import RBM3D.Defs.Lattice
import RBM3D.Defs.Params
import RBM3D.Defs.Domination
import RBM3D.Loop.TreeRep

/-!
# The abstract bootstraps of the GUE phase (§7.2 of [YY_25]) on `Z_L^d` (T2202, UN-26a)

Port of the live part of `RBM2D/Universality/GUEPhase/Bootstrap.lean` at `c9a24cf` (`:1-645`
without `eq736_detDom` and `stochDom_of_forall_highProb`) to `d` dimensions.  There is no carrier
and no matrix model (class G of T2173): the random layer enters only through hypotheses.

* `SBgue d L` (`S^{(B)}_{GUE} = L^{-d}` on `Z_L^d`), `sum_SBgue_col`, `sum_SBgue_row`;
  `primBilGUE`, `primRhsGUE` (the primitive equation (7.33) with `S^{(B)} → S^{(B)}_{GUE}`,
  prefactor `W^d`), `norm_primBilGUE_le`, `norm_primRhsGUE_le` (the power counting (7.34): the
  double sum over `a, b ∈ Z_L^d` with `S_GUE = L^{-d}` costs `L^{2d} L^{-d} = L^d`, times `W^d`:
  `N = (W L)^d`).
* `continuity_argument`, `K_bootstrap` (abstract ODE bootstrap (7.35) ⟹ (7.36)), `eq736`.
* `ellT_eq_L`: (7.30) ⟹ `ℓ_{t₁} = L` for the merged `RBM.ellT` (coupling `g`, floor `1`).
* `supOn` and its scalar lemmas, `rhs745G`, `rhs746G` (the vocabulary of the `L`-bootstrap of
  UN-26b); `N` is an abstract real there, `(W L)^d` at the consumers.

All statements hold for every `d` (no `3 ≤ d`); the only `d`-dependence is `SBgue` (`L^{-d}`), the
prefactor `W^d` and the count `N = (W L)^d`.  The section `BootstrapCheck` at the end holds one
compiled nonempty instance of each target at concrete data (`d = 3`, `L = 3`, `W = 2`); `eq736` is
instanced at `K ≡ 0` and at the nonzero tight solution `K₀ / (1 - N K₀ t)` of `K' = N K²` (`n = 2`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open Matrix Finset Filter RBM.Loop

/-! ### (7.25): the variance profile -/

section Variance

variable (d L : ℕ)

/-- `S^{(B)}_{GUE}`: `(S^{(B)}_{GUE})_{ab} = L^{-d}` on `Z_L^d`. -/
def SBgue : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun _ _ => ((L : ℂ) ^ d)⁻¹

@[simp] theorem SBgue_apply (a b : Zd d L) : SBgue d L a b = ((L : ℂ) ^ d)⁻¹ := rfl

variable [NeZero L]

/-- The columns of `S^{(B)}_{GUE}` sum to `1` (`|Z_L^d| = L^d`). -/
theorem sum_SBgue_col (b : Zd d L) : ∑ a : Zd d L, SBgue d L a b = 1 := by
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  simp only [SBgue_apply, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  push_cast
  field_simp

/-- The rows of `S^{(B)}_{GUE}` sum to `1`. -/
theorem sum_SBgue_row (a : Zd d L) : ∑ b : Zd d L, SBgue d L a b = 1 := by
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  simp only [SBgue_apply, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  push_cast
  field_simp

end Variance

/-! ### The continuity argument -/

section Continuity

open Set

/-- **The continuity argument** used for (7.36) and (7.27), (7.28): finitely many continuous
quantities `f i` start strictly below the continuous thresholds `g i` at `t₁`, and whenever all
of them are below their thresholds on `[t₁, t]`, they are strictly below at `t` (the bootstrap
improvement).  Then they stay strictly below on all of `[t₁, t₀]`. -/
theorem continuity_argument {ι : Type*} {S : Set ι} (hS : S.Finite) {f g : ι → ℝ → ℝ}
    {t1 t0 : ℝ} (hf : ∀ i ∈ S, ContinuousOn (f i) (Icc t1 t0))
    (hg : ∀ i ∈ S, ContinuousOn (g i) (Icc t1 t0)) (h0 : ∀ i ∈ S, f i t1 < g i t1)
    (hstep : ∀ t ∈ Icc t1 t0, (∀ u ∈ Icc t1 t, ∀ i ∈ S, f i u ≤ g i u) →
      ∀ i ∈ S, f i t < g i t) :
    ∀ t ∈ Icc t1 t0, ∀ i ∈ S, f i t < g i t := by
  by_contra hno
  push Not at hno
  set F : Set ℝ := {t | t ∈ Icc t1 t0 ∧ ∃ i ∈ S, g i t ≤ f i t} with hFdef
  have hFeq : F = ⋃ i ∈ S, {t | t ∈ Icc t1 t0 ∧ g i t ≤ f i t} := by
    ext t
    simp only [hFdef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨ht, i, hi, h⟩; exact ⟨i, hi, ht, h⟩
    · rintro ⟨i, hi, ht, h⟩; exact ⟨ht, i, hi, h⟩
  have hFc : IsClosed F := by
    rw [hFeq]
    exact hS.isClosed_biUnion fun i hi => isClosed_Icc.isClosed_le (hg i hi) (hf i hi)
  obtain ⟨t, ht, i, hi, hti⟩ := hno
  have hFne : F.Nonempty := ⟨t, ht, i, hi, hti⟩
  have hFbdd : BddBelow F := ⟨t1, fun x hx => hx.1.1⟩
  set T := sInf F with hT
  have hTF : T ∈ F := hFc.csInf_mem hFne hFbdd
  have hT1 : t1 ≤ T := hTF.1.1
  have hTne : T ≠ t1 := by
    intro h
    obtain ⟨-, j, hj, hle⟩ := hTF
    rw [h] at hle
    exact absurd (h0 j hj) (not_lt.2 hle)
  have hT1' : t1 < T := lt_of_le_of_ne hT1 (Ne.symm hTne)
  have hbelow : ∀ u ∈ Ico t1 T, ∀ j ∈ S, f j u < g j u := by
    intro u hu j hj
    by_contra hle
    push Not at hle
    have huF : u ∈ F := ⟨⟨hu.1, (hu.2.le.trans hTF.1.2)⟩, j, hj, hle⟩
    exact absurd (csInf_le hFbdd huF) (not_le.2 hu.2)
  have hsub : Ico t1 T ⊆ Icc t1 t0 := fun u hu => ⟨hu.1, hu.2.le.trans hTF.1.2⟩
  have hcl : T ∈ closure (Ico t1 T) := by
    rw [closure_Ico hTne.symm]
    exact ⟨hT1, le_rfl⟩
  have hTle : ∀ j ∈ S, f j T ≤ g j T := by
    intro j hj
    exact ContinuousWithinAt.closure_le hcl (((hf j hj) T hTF.1).mono hsub)
      (((hg j hj) T hTF.1).mono hsub) fun y hy => (hbelow y hy j hj).le
  have hall : ∀ u ∈ Icc t1 T, ∀ j ∈ S, f j u ≤ g j u := by
    intro u hu j hj
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hTle j hj
    · exact (hbelow u ⟨hu.1, h⟩ j hj).le
  obtain ⟨hTI, j, hj, hle⟩ := hTF
  exact absurd (hstep T hTI hall j hj) (not_lt.2 hle)

end Continuity

/-! ### (7.30): the scales of the GUE phase -/

section Scales

/-- **(7.30) ⟹ `ℓ_{t₁} = L`**: `ℓ_t = L` (the merged `RBM.ellT L g t = min (max (g/√|1-t|) 1) L`) as
soon as `L² (1 - t) ≤ g²` (and `0 ≤ g`, `t < 1`: at `g < 0` the quotient is negative, at `t ≥ 1`
the absolute value `|1 - t|` is no longer `1 - t`).  RBM2D has no coupling and no floor
(hypothesis `L² (1 - t) ≤ 1`). -/
theorem ellT_eq_L {L : ℕ} {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1)
    (h : (L : ℝ) ^ 2 * (1 - t) ≤ g ^ 2) : RBM.ellT L g t = L := by
  unfold RBM.ellT
  rw [min_eq_right]
  have h1 : 0 < 1 - t := by linarith
  rw [abs_of_pos h1]
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1
  refine le_trans ?_ (le_max_left _ _)
  rw [le_div_iff₀ hs]
  have h2 : ((L : ℝ) * Real.sqrt (1 - t)) ^ 2 ≤ g ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h1.le]; exact h
  exact (pow_le_pow_iff_left₀ (by positivity) hg two_ne_zero).1 h2

end Scales

/-! ### (7.33), (7.34), (7.39), (7.40): the hierarchy with `S^{(B)} → S^{(B)}_{GUE}` -/

section Hierarchy

variable (d L : ℕ) [NeZero L]

/-- The polarized right side of the primitive equation of the GUE phase ((7.33) with independent
left and right factors): `W^d ∑_{1≤k<l≤n} ∑_{a,b} K(G^{(a),L}_{k,l}) (S^{(B)}_{GUE})_{ab}
K'(G^{(b),R}_{k,l})`, `(S^{(B)}_{GUE})_{ab} = L^{-d}`.  The merged `treeEqRhs`
(`Loop/TreeRep.lean`) with `SB ↦ SBgue`, polarized. -/
def primBilGUE (W : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
    K (I.cutGlueL k l a) * SBgue d L a b * K' (I.cutGlueR k l b)

/-- **(7.33)**: the right side of the primitive equation of the GUE phase. -/
def primRhsGUE (W : ℕ) (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  primBilGUE d L W K K I

theorem primBilGUE_add_left (W : ℕ) (K₁ K₂ K' : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBilGUE d L W (K₁ + K₂) K' I = primBilGUE d L W K₁ K' I + primBilGUE d L W K₂ K' I := by
  simp only [primBilGUE, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem primBilGUE_add_right (W : ℕ) (K K₁ K₂ : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primBilGUE d L W K (K₁ + K₂) I = primBilGUE d L W K K₁ I + primBilGUE d L W K K₂ I := by
  simp only [primBilGUE, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **The GUE-phase version of (5.12)/(5.13)**. -/
theorem primRhsGUE_sub (W : ℕ) (Lf K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    primRhsGUE d L W Lf I - primRhsGUE d L W K I
      = primBilGUE d L W K (Lf - K) I + primBilGUE d L W (Lf - K) K I
        + primBilGUE d L W (Lf - K) (Lf - K) I := by
  have hLf : Lf = K + (Lf - K) := by funext x; simp
  have h1 : primRhsGUE d L W Lf I = primBilGUE d L W (K + (Lf - K)) (K + (Lf - K)) I := by
    rw [primRhsGUE, ← hLf]
  rw [h1, primBilGUE_add_left, primBilGUE_add_right, primBilGUE_add_right, primRhsGUE]
  ring

private theorem GUEPhaseBootstrap_two_le_length_cutGlueL (I : LoopIdx (Zd d L)) (a : Zd d L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    2 ≤ (I.cutGlueL k l a).length := by
  rw [LoopIdx.length_cutGlueL I a hk hkl hl]
  omega

private theorem GUEPhaseBootstrap_two_le_length_cutGlueR (I : LoopIdx (Zd d L)) (b : Zd d L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    2 ≤ (I.cutGlueR k l b).length := by
  rw [LoopIdx.length_cutGlueR I b hk hkl hl]
  omega

private theorem GUEPhaseBootstrap_length_cutGlueL_le (I : LoopIdx (Zd d L)) (a : Zd d L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueL k l a).length ≤ I.length :=
  LoopIdx.length_cutGlueL_le I a hk hkl hl

private theorem GUEPhaseBootstrap_length_cutGlueR_le (I : LoopIdx (Zd d L)) (b : Zd d L)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) :
    (I.cutGlueR k l b).length ≤ I.length :=
  LoopIdx.length_cutGlueR_le I b hk hkl hl

/-- **The power counting behind (7.34), (7.39), (7.40)**: if `|K J| ≤ B(|J|)` and
`|K' J| ≤ B'(|J|)` for all well-formed loops `J` of length `2 ≤ |J| ≤ n = |I|`, then
`|W^d ∑_{k<l} ∑_{a,b} K(G^{L}) (S_{GUE})_{ab} K'(G^{R})| ≤ n² N ∑_{2≤j≤n} B(n-j+2) B'(j)`,
`N = (W L)^d`.  Since `S^{(B)}_{GUE}` is the constant `L^{-d}`, the double sum over
`a, b ∈ Z_L^d` costs exactly a factor `L^{2d} · L^{-d} = L^d`; with the prefactor `W^d` this is
`N = (W L)^d`. -/
theorem norm_primBilGUE_le (W : ℕ) (K K' : LoopIdx (Zd d L) → ℂ) (B B' : ℕ → ℝ)
    (I : LoopIdx (Zd d L)) (hI : I.WF)
    (hB : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ B J.length)
    (hB' : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K' J‖ ≤ B' J.length)
    (hB0 : ∀ j, 0 ≤ B j) (hB0' : ∀ j, 0 ≤ B' j) :
    ‖primBilGUE d L W K K' I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B' j := by
  set n := I.length with hn
  set Sm := ∑ j ∈ Icc 2 n, B (n - j + 2) * B' j with hSm
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0' _)
  -- one pair `(k, l)`
  have hpair : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n,
      ‖∑ a : Zd d L, ∑ b : Zd d L, K (I.cutGlueL k l a) * SBgue d L a b * K' (I.cutGlueR k l b)‖
        ≤ (L : ℝ) ^ d * Sm := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hlenL : ∀ a : Zd d L, (I.cutGlueL k l a).length = n - (l - k + 1) + 2 := by
      intro a; rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega
    have hlenR : ∀ b : Zd d L, (I.cutGlueR k l b).length = l - k + 1 := by
      intro b; rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]
    have hBL : ∀ a : Zd d L, ‖K (I.cutGlueL k l a)‖ ≤ B (n - (l - k + 1) + 2) := by
      intro a
      rw [← hlenL a]
      exact hB _ (LoopIdx.wf_cutGlueL I a hI hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_two_le_length_cutGlueL d L I a hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_length_cutGlueL_le d L I a hk.1 hl.1 hl.2)
    have hBR : ∀ b : Zd d L, ‖K' (I.cutGlueR k l b)‖ ≤ B' (l - k + 1) := by
      intro b
      rw [← hlenR b]
      exact hB' _ (LoopIdx.wf_cutGlueR I b hI hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_two_le_length_cutGlueR d L I b hk.1 hl.1 hl.2)
        (GUEPhaseBootstrap_length_cutGlueR_le d L I b hk.1 hl.1 hl.2)
    have hj : l - k + 1 ∈ Icc 2 n := by rw [Finset.mem_Icc]; omega
    have hterm : B (n - (l - k + 1) + 2) * B' (l - k + 1) ≤ Sm :=
      Finset.single_le_sum (f := fun j => B (n - j + 2) * B' j)
        (fun j _ => mul_nonneg (hB0 _) (hB0' _)) hj
    have hSB : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_natCast]
    calc _ ≤ ∑ a : Zd d L, ∑ b : Zd d L,
          ‖K (I.cutGlueL k l a) * SBgue d L a b * K' (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : Zd d L, ∑ _b : Zd d L,
          B (n - (l - k + 1) + 2) * ((L : ℝ) ^ d)⁻¹ * B' (l - k + 1) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul, SBgue_apply, hSB]
          have hLi : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ := inv_nonneg.2 hLd.le
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hBL a) hLi) (hBR b) (norm_nonneg _)
            (mul_nonneg (hB0 _) hLi)
      _ = (L : ℝ) ^ d * (B (n - (l - k + 1) + 2) * B' (l - k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ (L : ℝ) ^ d * Sm := mul_le_mul_of_nonneg_left hterm hLd.le
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ d := by positivity
  calc ‖primBilGUE d L W K K' I‖
      ≤ (W : ℝ) ^ d * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, (L : ℝ) ^ d * Sm := by
        rw [primBilGUE, norm_mul, norm_pow, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) ^ d * ∑ _k ∈ Icc 1 n, (n : ℝ) * ((L : ℝ) ^ d * Sm) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
        exact mul_le_mul_of_nonneg_right this (mul_nonneg hLd.le hSm0)
    _ = (n : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) * Sm := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

/-- **(7.34)**: `|d/dt K_{t,σ,a}| ≤ n² N ∑_{2≤k≤n} max K^{(k)} · max K^{(n-k+2)}`, with the maxima
written as bounds `B` (`N = (W L)^d`). -/
theorem norm_primRhsGUE_le (W : ℕ) (K : LoopIdx (Zd d L) → ℂ) (B : ℕ → ℝ)
    (I : LoopIdx (Zd d L)) (hI : I.WF)
    (hB : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ B J.length)
    (hB0 : ∀ j, 0 ≤ B j) :
    ‖primRhsGUE d L W K I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B j :=
  norm_primBilGUE_le d L W K K B B I hI hB hB hB0 hB0

end Hierarchy

/-! ### (7.35), (7.36): the continuity bootstrap for `K` -/

section KBootstrap

open Set

/-- `∑_{2≤j≤m} (c x^{m-j+1}) (c x^{j-1}) = (m-1) c² x^m`. -/
theorem sum_pow_mul_pow (c x : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 2 m, (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1))
      = ((m - 1 : ℕ) : ℝ) * c ^ 2 * x ^ m := by
  have hterm : ∀ j ∈ Finset.Icc 2 m,
      (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1)) = c ^ 2 * x ^ m := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have he : m - j + 2 - 1 + (j - 1) = m := by omega
    rw [show (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1))
      = c ^ 2 * (x ^ (m - j + 2 - 1) * x ^ (j - 1)) by ring, ← pow_add, he]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : m + 1 - 2 = m - 1 := by omega
  rw [this]; ring

/-- **(7.35) ⟹ (7.36), deterministic core.**  Let `k_i(t)` (`i ∈ S`, finitely many; `i` stands
for `(σ, a)` of a loop of length `|i| ∈ [2, n]`) solve `d/dt k_i = dk_i` on `[t₁, t₀]`, where the
drift obeys the power counting (7.34): whenever `|k_j(t)| ≤ B(|j|)` for all `j`,
`|dk_i(t)| ≤ C N ∑_{2≤j≤|i|} B(|i|-j+2) B(j)`.  Let `λ_t = N η_t` be positive, continuous and
non-increasing, and let (7.30) hold in the form `N (t - t₁) ≤ ε λ_t`.  If initially
`|k_i(t₁)| ≤ A λ_{t₁}^{-|i|+1}` ((7.32)) and `4 C n A ε < 1`, then
`|k_i(t)| < 2 A λ_t^{-|i|+1}` on `[t₁, t₀]` ((7.36)).  The integration of (7.34) to (7.35) is
the mean value inequality; the continuity argument is `continuity_argument`.  (The drift is named
`dk` here only to keep `d` for the dimension.) -/
theorem K_bootstrap {ι : Type*} {S : Set ι} (hS : S.Finite) (len : ι → ℕ) {n : ℕ}
    (hlen : ∀ i ∈ S, 2 ≤ len i ∧ len i ≤ n) (k dk : ℝ → ι → ℂ) {t1 t0 C N A ε : ℝ}
    (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u)
    (hlamc : ContinuousOn lam (Icc t1 t0))
    (hderiv : ∀ t ∈ Icc t1 t0, ∀ i ∈ S, HasDerivWithinAt (fun s => k s i) (dk t i) (Icc t1 t0) t)
    (hd : ∀ t ∈ Icc t1 t0, ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → (∀ j ∈ S, ‖k t j‖ ≤ B (len j)) →
      ∀ i ∈ S, ‖dk t i‖ ≤ C * N * ∑ j ∈ Finset.Icc 2 (len i), B (len i - j + 2) * B j)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hA : 0 < A)
    (hinit : ∀ i ∈ S, ‖k t1 i‖ ≤ A * (lam t1)⁻¹ ^ (len i - 1))
    (hsmall : ∀ t ∈ Icc t1 t0, N * (t - t1) ≤ ε * lam t) (hε : 4 * C * n * A * ε < 1) :
    ∀ t ∈ Icc t1 t0, ∀ i ∈ S, ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1) := by
  have ht1' : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
  have hkc : ∀ i ∈ S, ContinuousOn (fun t => ‖k t i‖) (Icc t1 t0) := fun i hi =>
    ContinuousOn.norm (f := fun s => k s i) fun t ht => (hderiv t ht i hi).continuousWithinAt
  have hgc : ∀ i ∈ S, ContinuousOn (fun t => 2 * A * (lam t)⁻¹ ^ (len i - 1)) (Icc t1 t0) :=
    fun i _ => continuousOn_const.mul
      ((hlamc.inv₀ fun t ht => (hlam t ht).ne').pow _)
  refine continuity_argument hS hkc hgc (fun i hi => ?_) (fun t ht hprev i hi => ?_)
  · have hpos : 0 < A * (lam t1)⁻¹ ^ (len i - 1) :=
      mul_pos hA (pow_pos (inv_pos.2 (hlam t1 ht1')) _)
    have := hinit i hi
    change ‖k t1 i‖ < 2 * A * (lam t1)⁻¹ ^ (len i - 1)
    linarith
  -- the improvement step at time `t`
  show ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1)
  have hlt := hlam t ht
  set x := (lam t)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hlt
  set m := len i with hm
  obtain ⟨hm2, hmn⟩ := hlen i hi
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  -- bounds on `[t₁, t]` in terms of `λ_t`
  set Bt : ℕ → ℝ := fun j => 2 * A * x ^ (j - 1) with hBt
  have hBt0 : ∀ j, 0 ≤ Bt j := fun j => by positivity
  have hkB : ∀ u ∈ Icc t1 t, ∀ j ∈ S, ‖k u j‖ ≤ Bt (len j) := by
    intro u hu j hj
    have hu0 := hsub hu
    have h1 : ‖k u j‖ ≤ 2 * A * (lam u)⁻¹ ^ (len j - 1) := hprev u hu j hj
    have hxu : (lam u)⁻¹ ≤ x := inv_anti₀ hlt (hanti u hu0 t ht hu.2)
    refine h1.trans ?_
    simp only [hBt]
    gcongr
    exact (inv_pos.2 (hlam u hu0)).le
  -- the drift bound on `[t₁, t]`
  have hdB : ∀ u ∈ Ico t1 t, ‖dk u i‖ ≤ C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) := by
    intro u hu
    have hu' : u ∈ Icc t1 t := Ico_subset_Icc_self hu
    have h := hd u (hsub hu') Bt hBt0 (fun j hj => hkB u hu' j hj) i hi
    rw [← sum_pow_mul_pow]
    exact h
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => k s i) (fun u hu => (hderiv u (hsub hu) i hi).mono hsub) hdB t ⟨ht1t, le_rfl⟩
  -- `λ_{t₁}^{-1} ≤ λ_t^{-1}`
  have hx1 : (lam t1)⁻¹ ≤ x := inv_anti₀ hlt (hanti t1 ht1' t ht ht1t)
  have hinit' : ‖k t1 i‖ ≤ A * x ^ (m - 1) := by
    refine (hinit i hi).trans ?_
    gcongr
    exact (inv_pos.2 (hlam t1 ht1')).le
  -- `C N (m-1)(2A)² x^m (t - t₁) ≤ 4 C n A² ε x^{m-1}`
  have hxm : x ^ m * lam t = x ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    rw [this, pow_succ, Nat.add_sub_cancel, mul_assoc, hx, inv_mul_cancel₀ hlt.ne', mul_one]
  have hkey : C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1)
      ≤ 4 * C * n * A * ε * (A * x ^ (m - 1)) := by
    have hm1 : ((m - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le m 1).trans hmn
    have hsm := hsmall t ht
    have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN (by linarith)
    calc C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1)
        = C * ((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m * (N * (t - t1)) := by ring
      _ ≤ C * n * (2 * A) ^ 2 * x ^ m * (ε * lam t) := by gcongr
      _ = 4 * C * n * A * ε * (A * (x ^ m * lam t)) := by ring
      _ = 4 * C * n * A * ε * (A * x ^ (m - 1)) := by rw [hxm]
  have hmvt' :
      ‖k t i‖ ≤ ‖k t1 i‖ + C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1) := by
    have := norm_sub_norm_le (k t i) (k t1 i)
    have h2 : ‖k t i - k t1 i‖ ≤ C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1) :=
      hmvt
    linarith
  have hpos : 0 < A * x ^ (m - 1) := mul_pos hA (pow_pos hx0 _)
  nlinarith

/-- Well-formed loop indices of bounded length form a finite set. -/
theorem finite_loopIdx (d L : ℕ) [NeZero L] (n : ℕ) :
    {I : LoopIdx (Zd d L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}.Finite := by
  refine (((List.finite_length_le Bool n).prod (List.finite_length_le (Zd d L) n)).image
    (fun p : List Bool × List (Zd d L) => (⟨p.1, p.2⟩ : LoopIdx (Zd d L)))).subset ?_
  rintro ⟨σ, a⟩ ⟨hWF, -, hn⟩
  simp only [LoopIdx.WF, LoopIdx.length] at hWF hn
  exact ⟨(σ, a), ⟨show σ.length ≤ n by omega, show a.length ≤ n from hn⟩, rfl⟩

/-- **(7.36)** for the primitive loops of the GUE phase: if `K_t` solves the GUE-phase
primitive equation (7.33) (`primRhsGUE`) on `[t₁, t₀]` for all loops of length `2 ≤ |I| ≤ n`,
`|K_{t₁, I}| ≤ A (N η_{t₁})^{-|I|+1}` ((7.32)), and (7.30) holds as `N (t - t₁) ≤ ε N η_t`
(`N = (W L)^d`), with `4 n³ A ε < 1`, then `|K_{t, I}| < 2 A (N η_t)^{-|I|+1}` on `[t₁, t₀]`. -/
theorem eq736 (d L W : ℕ) [NeZero L] (Kt : ℝ → LoopIdx (Zd d L) → ℂ) {n : ℕ} {t1 t0 A ε : ℝ}
    (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u)
    (hlamc : ContinuousOn lam (Icc t1 t0))
    (hK : ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n →
      HasDerivWithinAt (fun s => Kt s I) (primRhsGUE d L W (Kt t) I) (Icc t1 t0) t)
    (hA : 0 < A)
    (hinit : ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t1 I‖ ≤ A * (lam t1)⁻¹ ^ (I.length - 1))
    (hsmall : ∀ t ∈ Icc t1 t0, (((W * L) ^ d : ℕ) : ℝ) * (t - t1) ≤ ε * lam t)
    (hε : 4 * ((n : ℝ) ^ 2) * n * A * ε < 1) :
    ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t I‖ < 2 * A * (lam t)⁻¹ ^ (I.length - 1) := by
  set S := {I : LoopIdx (Zd d L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n} with hSdef
  have hS : S.Finite := finite_loopIdx d L n
  have key := K_bootstrap (S := S) hS LoopIdx.length (n := n)
    (fun I hI => ⟨hI.2.1, hI.2.2⟩) Kt (fun t I => primRhsGUE d L W (Kt t) I)
    (C := (n : ℝ) ^ 2) (N := (((W * L) ^ d : ℕ) : ℝ)) ht10 lam hlam hanti hlamc
    (fun t ht I hI => hK t ht I hI.1 hI.2.1 hI.2.2) ?_ (by positivity) (by positivity) hA
    (fun I hI => hinit I hI.1 hI.2.1 hI.2.2) hsmall hε
  · intro t ht I hWF h2 hn
    exact key t ht I ⟨hWF, h2, hn⟩
  · intro t _ B hB0 hB I hI
    have h := norm_primRhsGUE_le d L W (Kt t) B I hI.1
      (fun J hJ h2 hJI => hB J ⟨hJ, h2, hJI.trans hI.2.2⟩) hB0
    refine h.trans ?_
    have hsum : 0 ≤ ∑ j ∈ Finset.Icc 2 I.length, B (I.length - j + 2) * B j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0 _)
    have hlen : (I.length : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : (I.length : ℝ) ≤ n := by exact_mod_cast hI.2.2
      gcongr
    gcongr

/-- Well-formed loop indices of length `2 ≤ |I| ≤ n` (the `(σ, a)` of the maxima in (7.27),
(7.28), (7.36)). -/
abbrev LoopSet (d L : ℕ) (n : ℕ) : Type :=
  {I : LoopIdx (Zd d L) // I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}

/-- `4 n³ N^{τ'} N^{-τ_U} < 1` for large `N`, if `τ' < τ_U`. -/
theorem eventually_small {n : ℕ} {τ' τU : ℝ} (h : τ' < τU) :
    ∀ᶠ N : ℕ in atTop, 4 * ((n : ℝ) ^ 2) * n * (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) < 1 := by
  filter_upwards [eventually_le_rpow (8 * (n : ℝ) ^ 3 + 1) (sub_pos.2 h),
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (τU - τ') := Real.rpow_pos_of_pos hN0 _
  have he : (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) = ((N : ℝ) ^ (τU - τ'))⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; ring_nf
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  rw [mul_assoc, he, show 4 * (n : ℝ) ^ 2 * n = 4 * (n : ℝ) ^ 3 by ring, ← div_eq_mul_inv,
    div_lt_one hpos]
  linarith

end KBootstrap

/-! ### (7.45) ⟹ (7.27) and (7.46) ⟹ (7.28): the vocabulary of the `L`-bootstrap -/

section LBootstrap

open Set

/-- `sup_{u ∈ [a, b]} g(u)` (a conditionally complete supremum; only upper bounds are used). -/
def supOn (g : ℝ → ℝ) (a b : ℝ) : ℝ := ⨆ u : Icc a b, g u

theorem supOn_le {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (h : ∀ u ∈ Icc a b, g u ≤ c) :
    supOn g a b ≤ c := by
  have : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  exact ciSup_le fun u => h u u.2

/-- (7.45) with the E^{(G)} term `N L₂ L_n` (from (4.3) + (5.117), no fluctuation averaging);
`N` is the matrix size, `(W L)^d` at the consumers. -/
def rhs745G (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Lm 2 u * Lm n u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t

/-- (7.46) with the E^{(G)} term `N D₁ L_{n+1}` (the `1`-loop tracked in the bootstrap). -/
def rhs746G (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Dm 1 u * Lm (n + 1) u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) *
        Real.sqrt (Lm (2 * n) u)) t1 t

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

/-- The first line of (7.45)/(7.46) under bounds `D_j(u) ≤ c x^{j-1+e}` (`x = (Nη_t)^{-1} ≤ 1`,
`e ∈ {0, 1}`): `sup_u ∑_k ((Nη_u)^{-k+1} + D_k) D_{n-k+2} ≤ n (1 + c) c x^{n+e}`. -/
theorem supOn_line1_le {Dm : ℕ → ℝ → ℝ} {n : ℕ} {t c x : ℝ} (e : ℕ) (he : e ≤ 1)
    (ht1t : t1 ≤ t) (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x)
    (hD : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n → 0 ≤ Dm j u ∧ Dm j u ≤ c * x ^ (j - 1 + e)) :
    supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
      ≤ n * ((1 + c) * c * x ^ (n + e)) := by
  refine supOn_le ht1t fun u hu => ?_
  have hterm : ∀ k ∈ Finset.Icc 2 n, ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u
      ≤ (1 + c) * c * x ^ (n + e) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hDk0, hDk⟩ := hD u hu k hk.1 hk.2
    obtain ⟨hDn0, hDn⟩ := hD u hu (n - k + 2) (by omega) (by omega)
    have h1 : (N * η u)⁻¹ ^ (k - 1) ≤ x ^ (k - 1) := pow_le_pow_left₀ (hxu u hu).1 (hxu u hu).2 _
    have h2 : x ^ (k - 1 + e) ≤ x ^ (k - 1) := pow_le_pow_of_le_one hx0 hx1 (by omega)
    have h3 : (N * η u)⁻¹ ^ (k - 1) + Dm k u ≤ (1 + c) * x ^ (k - 1) := by nlinarith
    have hexp : k - 1 + (n - k + 2 - 1 + e) = n + e := by omega
    calc ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u
        ≤ ((1 + c) * x ^ (k - 1)) * (c * x ^ (n - k + 2 - 1 + e)) :=
          mul_le_mul h3 hDn hDn0 (by positivity)
      _ = (1 + c) * c * x ^ (n + e) := by rw [← hexp, pow_add]; ring
  calc _ ≤ ∑ _k ∈ Finset.Icc 2 n, (1 + c) * c * x ^ (n + e) := Finset.sum_le_sum hterm
    _ = ((n + 1 - 2 : ℕ) : ℝ) * ((1 + c) * c * x ^ (n + e)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ n * ((1 + c) * c * x ^ (n + e)) := by
        gcongr
        exact_mod_cast (by omega : n + 1 - 2 ≤ n)

/-- `N(t - t₁) · y ≤ ε x^{-1} y` from (7.30) in the form `t - t₁ ≤ ε η_t`, `x = (Nη_t)^{-1}`. -/
theorem mul_le_of_eq730 {t ε y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) (hsm : t - t1 ≤ ε * η t) :
    N * (t - t1) * y ≤ ε * ((N * η t)⁻¹)⁻¹ * y := by
  rw [inv_inv]
  have : N * (t - t1) ≤ ε * (N * η t) := by nlinarith
  exact mul_le_mul_of_nonneg_right this hy

/-- The martingale line: `|t - t₁|^{1/2} (N^{-1} η_t^{-2})^{1/2} = (ε (Nη_t)^{-1})^{1/2}` at most,
under (7.30) `t - t₁ ≤ ε η_t`.  (`d`-free: the GUE increment has entry variance `N^{-1}`.) -/
theorem sqrt_mul_sqrt_le {t ε : ℝ} (hN : 0 < N) (hηt : 0 < η t) (ht1t : t1 ≤ t)
    (hsm : t - t1 ≤ ε * η t) :
    Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) ≤ Real.sqrt (ε * (N * η t)⁻¹) := by
  rw [← Real.sqrt_mul (by linarith)]
  refine Real.sqrt_le_sqrt ?_
  have h0 : 0 ≤ N⁻¹ * (η t)⁻¹ ^ 2 := by positivity
  calc (t - t1) * (N⁻¹ * (η t)⁻¹ ^ 2) ≤ ε * η t * (N⁻¹ * (η t)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hsm h0
    _ = ε * (N * η t)⁻¹ := by field_simp

/-- `sup_{[a,b]} g ≥ 0` for `g ≥ 0` on `[a, b]`. -/
theorem supOn_nonneg {g : ℝ → ℝ} {a b : ℝ} (h : ∀ u ∈ Icc a b, 0 ≤ g u) : 0 ≤ supOn g a b :=
  Real.iSup_nonneg fun u => h u u.2

/-- `x^{-1} x^n = x^{n-1}` for `n ≥ 1`. -/
theorem inv_mul_pow {x : ℝ} (hx : x ≠ 0) {n : ℕ} (hn : 1 ≤ n) : x⁻¹ * x ^ n = x ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

end LBootstrap

/-! ### Domination helper -/

section Domination

/-- `N^a ≤ ρ` for large `N`, if `a < 0`, `ρ > 0`. -/
theorem eventually_rpow_le_of_neg {a ρ : ℝ} (ha : a < 0) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ ρ := by
  filter_upwards [eventually_le_rpow ρ⁻¹ (neg_pos.2 ha), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (-a) := Real.rpow_pos_of_pos hN0 _
  have e : (N : ℝ) ^ a = ((N : ℝ) ^ (-a))⁻¹ := by
    rw [← Real.rpow_neg hN0.le, neg_neg]
  rw [e]
  calc ((N : ℝ) ^ (-a))⁻¹ ≤ (ρ⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hρ) hN
    _ = ρ := inv_inv ρ

end Domination

/-! ### Compiled nonempty instances of the targets (CLAUDE.md §4 step 2) -/

namespace BootstrapCheck

open Set

/-- A concrete well-formed loop of length `3` on `Z_3^3`. -/
def loopThree : LoopIdx (Zd 3 3) :=
  ⟨[true, false, true], [fun _ => 0, fun _ => 1, fun _ => 2]⟩

theorem loopThree_WF : loopThree.WF := rfl

theorem loopThree_length : loopThree.length = 3 := rfl

theorem primBilGUE_zero_left (d L W : ℕ) [NeZero L] (K' : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) : primBilGUE d L W (fun _ => 0) K' I = 0 := by
  simp [primBilGUE]

theorem primRhsGUE_zero (d L W : ℕ) [NeZero L] (I : LoopIdx (Zd d L)) :
    primRhsGUE d L W (fun _ => 0) I = 0 :=
  primBilGUE_zero_left d L W _ I

/-- Target `sum_SBgue_col` at `d = 3`, `L = 3`, `b = 0`. -/
theorem inst_sum_SBgue_col : ∑ a : Zd 3 3, SBgue 3 3 a 0 = 1 :=
  sum_SBgue_col 3 3 0

/-- Target `sum_SBgue_row` at `d = 3`, `L = 3`, `a = 0`. -/
theorem inst_sum_SBgue_row : ∑ b : Zd 3 3, SBgue 3 3 0 b = 1 :=
  sum_SBgue_row 3 3 0

/-- Target `continuity_argument`: two constant families `f i = i`, `g i = i + 1` on `S = {1, 2}`. -/
theorem inst_continuity_argument : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ ({1, 2} : Set ℕ),
    (fun (i : ℕ) (_ : ℝ) => (i : ℝ)) i t < (fun (i : ℕ) (_ : ℝ) => (i : ℝ) + 1) i t :=
  continuity_argument (S := ({1, 2} : Set ℕ)) ((Set.finite_singleton 2).insert 1)
    (f := fun (i : ℕ) (_ : ℝ) => (i : ℝ)) (g := fun (i : ℕ) (_ : ℝ) => (i : ℝ) + 1)
    (t1 := 0) (t0 := 1) (fun _ _ => continuousOn_const) (fun _ _ => continuousOn_const)
    (fun _ _ => lt_add_one _) (fun _ _ _ _ _ => lt_add_one _)

/-- Target `K_bootstrap`: `S = {0}`, `|i| = 2`, `k ≡ 1/100`, `dk ≡ 0`, `λ ≡ 16`, `C = N = A = 1`,
`ε = 1/16`, `n = 2`. -/
theorem inst_K_bootstrap : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ ({0} : Set ℕ),
    ‖(fun (_ : ℝ) (_ : ℕ) => (1 / 100 : ℂ)) t i‖ <
      2 * (1 : ℝ) * ((fun _ : ℝ => (16 : ℝ)) t)⁻¹ ^ ((fun _ : ℕ => 2) i - 1) :=
  K_bootstrap (S := ({0} : Set ℕ)) (Set.finite_singleton 0) (fun _ => 2) (n := 2)
    (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun _ _ => (1 / 100 : ℂ)) (fun _ _ => 0)
    (t1 := 0) (t0 := 1) (C := 1) (N := 1) (A := 1) (ε := 1 / 16) zero_le_one
    (fun _ => 16) (fun _ _ => by norm_num) (fun _ _ _ _ _ => le_rfl) continuousOn_const
    (fun _ _ _ _ => hasDerivWithinAt_const _ _ _)
    (fun _ _ B hB0 _ _ _ => by
      rw [norm_zero]
      exact mul_nonneg (mul_nonneg zero_le_one zero_le_one)
        (Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0 _)))
    zero_le_one zero_le_one one_pos
    (fun _ _ => by norm_num)
    (fun t ht => by
      have h2 : t ≤ 1 := ht.2
      change (1 : ℝ) * (t - 0) ≤ 1 / 16 * 16
      linarith)
    (by norm_num)

/-- Target `norm_primBilGUE_le` at `K = K' = 0` (`d = 3`, `L = 3`, `W = 2`, `|I| = 3`,
`B = B' ≡ 1`). -/
theorem inst_norm_primBilGUE_le_zero :
    ‖primBilGUE 3 3 2 (fun _ => 0) (fun _ => 0) loopThree‖ ≤
    (loopThree.length : ℝ) ^ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 loopThree.length, (fun _ : ℕ => (1 : ℝ)) (loopThree.length - j + 2) *
        (fun _ : ℕ => (1 : ℝ)) j :=
  norm_primBilGUE_le 3 3 2 (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 1) loopThree
    loopThree_WF (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ => zero_le_one)
    (fun _ => zero_le_one)

/-- Target `norm_primBilGUE_le` at `K = K' ≡ 1` (the bound is then not trivially `0 ≤ _`:
`W^d · #{k < l} · L^{2d} · L^{-d} = 8 · 3 · 27 = 648 ≤ 3² · 216 · 2 = 3888`). -/
theorem inst_norm_primBilGUE_le_one :
    ‖primBilGUE 3 3 2 (fun _ => 1) (fun _ => 1) loopThree‖ ≤
    (loopThree.length : ℝ) ^ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 loopThree.length, (fun _ : ℕ => (1 : ℝ)) (loopThree.length - j + 2) *
        (fun _ : ℕ => (1 : ℝ)) j :=
  norm_primBilGUE_le 3 3 2 (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) loopThree
    loopThree_WF (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ => zero_le_one)
    (fun _ => zero_le_one)

/-- Target `norm_primRhsGUE_le` at `K ≡ 1`, `B ≡ 1`. -/
theorem inst_norm_primRhsGUE_le :
    ‖primRhsGUE 3 3 2 (fun _ => 1) loopThree‖ ≤
    (loopThree.length : ℝ) ^ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 loopThree.length, (fun _ : ℕ => (1 : ℝ)) (loopThree.length - j + 2) *
        (fun _ : ℕ => (1 : ℝ)) j :=
  norm_primRhsGUE_le 3 3 2 (fun _ => 1) (fun _ => 1) loopThree loopThree_WF
    (fun _ _ _ _ => by simp) (fun _ => zero_le_one)

/-- Target `eq736` at `d = 3`, `L = 3`, `W = 2`, `n = 2`, `K ≡ 0`, `t₁ = 0`, `t₀ = 1`, `A = 1`,
`ε = 1/100`, `λ ≡ 40000` (`N = (W L)^d = 216`, `N (t - t₁) ≤ 216 ≤ ε λ = 400`,
`4 n³ A ε = 0.32 < 1`). -/
theorem inst_eq736 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ I : LoopIdx (Zd 3 3), I.WF → 2 ≤ I.length →
    I.length ≤ 2 →
    ‖(fun (_ : ℝ) (_ : LoopIdx (Zd 3 3)) => (0 : ℂ)) t I‖ <
      2 * (1 : ℝ) * ((fun _ : ℝ => (40000 : ℝ)) t)⁻¹ ^ (I.length - 1) :=
  eq736 3 3 2 (fun _ _ => (0 : ℂ)) (n := 2) (t1 := 0) (t0 := 1) (A := 1) (ε := 1 / 100)
    zero_le_one (fun _ => 40000) (fun _ _ => by norm_num) (fun _ _ _ _ _ => le_rfl)
    continuousOn_const
    (fun _ _ I _ _ _ => by
      change HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) (primRhsGUE 3 3 2 (fun _ => 0) I) _ _
      rw [primRhsGUE_zero]
      exact hasDerivWithinAt_const _ _ _)
    one_pos (fun _ _ _ _ => by norm_num)
    (fun t ht => by
      have h2 : t ≤ 1 := ht.2
      change (((2 * 3) ^ 3 : ℕ) : ℝ) * (t - 0) ≤ 1 / 100 * 40000
      norm_num
      linarith)
    (by norm_num)

/-- Target `ellT_eq_L` at `L = 4`, `g = 1/2`, `t = 63/64`: `L² (1 - t) = 1/4 = g²` (equality case). -/
theorem inst_ellT_eq_L : RBM.ellT 4 (1 / 2) (63 / 64) = 4 := by
  have := ellT_eq_L (L := 4) (g := 1 / 2) (t := 63 / 64) (by norm_num) (by norm_num)
    (by norm_num)
  simpa using this

/-- Target `finite_loopIdx` at `d = 3`, `L = 3`, `n = 4`; the set contains `loopThree`. -/
theorem inst_finite_loopIdx :
    {I : LoopIdx (Zd 3 3) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ 4}.Finite ∧
      loopThree ∈ {I : LoopIdx (Zd 3 3) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ 4} :=
  ⟨finite_loopIdx 3 3 4, loopThree_WF, by rw [loopThree_length]; omega⟩

/-- Target `eventually_small` at `n = 2`, `τ' = 1/4`, `τ_U = 1/2`. -/
theorem inst_eventually_small :
    ∀ᶠ N : ℕ in atTop, 4 * (((2 : ℕ) : ℝ) ^ 2) * ((2 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) *
      (N : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
  eventually_small (n := 2) (τ' := 1 / 4) (τU := 1 / 2) (by norm_num)

/-- Target `eventually_rpow_le_of_neg` at `a = -1`, `ρ = 1/2`. -/
theorem inst_eventually_rpow_le_of_neg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 :=
  eventually_rpow_le_of_neg (by norm_num) (by norm_num)

/-- Target `sum_pow_mul_pow` at `c = 3`, `x = 2`, `m = 4`. -/
theorem inst_sum_pow_mul_pow :
    ∑ j ∈ Finset.Icc 2 4, ((3 : ℝ) * 2 ^ (4 - j + 2 - 1)) * (3 * 2 ^ (j - 1))
      = ((4 - 1 : ℕ) : ℝ) * 3 ^ 2 * 2 ^ 4 :=
  sum_pow_mul_pow 3 2 4

/-- Target `supOn_le` on `[0, 1]`. -/
theorem inst_supOn_le : supOn (fun u => u) 0 1 ≤ 1 :=
  supOn_le (by norm_num) fun _ hu => hu.2

/-- Target `supOn_nonneg` on `[0, 1]`. -/
theorem inst_supOn_nonneg : 0 ≤ supOn (fun u => u) 0 1 :=
  supOn_nonneg fun _ hu => hu.1

/-- Target `inv_mul_pow` at `x = 2`, `n = 3`. -/
theorem inst_inv_mul_pow : (2 : ℝ)⁻¹ * 2 ^ 3 = 2 ^ (3 - 1) :=
  inv_mul_pow (by norm_num) (by norm_num)

/-- Target `mul_le_of_eq730` at `N = 216`, `η ≡ 1`, `t₁ = 0`, `t = 1/2`, `ε = 1`, `y = 1`. -/
theorem inst_mul_le_of_eq730 :
    (216 : ℝ) * (1 / 2 - 0) * 1 ≤ 1 * ((216 * (fun _ : ℝ => (1 : ℝ)) (1 / 2))⁻¹)⁻¹ * 1 :=
  mul_le_of_eq730 (216 : ℝ) (fun _ : ℝ => (1 : ℝ)) 0 (t := 1 / 2) (ε := 1) (y := 1)
    (by norm_num) (by norm_num) (by norm_num)

/-- Target `sqrt_mul_sqrt_le` at `N = 216`, `η ≡ 1`, `t₁ = 0`, `t = 1/2`, `ε = 1`. -/
theorem inst_sqrt_mul_sqrt_le :
    Real.sqrt (1 / 2 - 0) * Real.sqrt ((216 : ℝ)⁻¹ * ((fun _ : ℝ => (1 : ℝ)) (1 / 2))⁻¹ ^ 2)
      ≤ Real.sqrt (1 * (216 * (fun _ : ℝ => (1 : ℝ)) (1 / 2))⁻¹) :=
  sqrt_mul_sqrt_le (216 : ℝ) (fun _ : ℝ => (1 : ℝ)) 0 (t := 1 / 2) (ε := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Target `supOn_line1_le` at `N = 216`, `η ≡ 1`, `t₁ = 0`, `t = 1`, `n = 3`, `e = 1`, `c = 1`,
`x = 1/216`, `D_j ≡ x^{j-1+1}`. -/
theorem inst_supOn_line1_le :
    supOn (fun u => ∑ k ∈ Finset.Icc 2 3,
      (((216 : ℝ) * (fun _ : ℝ => (1 : ℝ)) u)⁻¹ ^ (k - 1) +
        (fun (j : ℕ) (_ : ℝ) => ((1 / 216 : ℝ)) ^ (j - 1 + 1)) k u) *
        (fun (j : ℕ) (_ : ℝ) => ((1 / 216 : ℝ)) ^ (j - 1 + 1)) (3 - k + 2) u) 0 1
      ≤ ((3 : ℕ) : ℝ) * ((1 + 1) * 1 * (1 / 216 : ℝ) ^ (3 + 1)) :=
  supOn_line1_le (216 : ℝ) (fun _ : ℝ => (1 : ℝ)) 0
    (Dm := fun (j : ℕ) (_ : ℝ) => ((1 / 216 : ℝ)) ^ (j - 1 + 1)) (n := 3) (t := 1)
    (c := 1) (x := 1 / 216) 1 le_rfl zero_le_one zero_le_one (by norm_num) (by norm_num)
    (fun u _ => ⟨by norm_num, by norm_num⟩)
    (fun _ _ j _ _ => ⟨by positivity, by rw [one_mul]⟩)

/-- The data of the `eq736` and `ellT_eq_L` instances are nondegenerate: `N = (2·3)^3 = 216`,
`N (t - t₁) ≤ 216 ≤ ε λ = 400`, `4 n³ A ε = 0.32 < 1` at `n = 2`; `L² (1 - t) = 1/4 ≤ g² = 1/4` at
`L = 4`, `g = 1/2`, `t = 63/64`. -/
theorem inst_bounds :
    (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 - 0) ≤ 1 / 100 * 40000 ∧
      4 * ((2 : ℝ) ^ 2) * 2 * 1 * (1 / 100) < 1 ∧
      (4 : ℝ) ^ 2 * (1 - 63 / 64) ≤ (1 / 2) ^ 2 := by
  norm_num

/-- The nonzero solution of `K' = N K²` at `n = 2`: `K(t) = K₀ / (1 - N K₀ t)`, `K₀ = 1/7000`,
`N = 216`. -/
def kTight (t : ℝ) : ℝ := (1 / 7000) / (1 - 216 / 7000 * t)

theorem kTight_hasDerivAt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt kTight (216 * kTight t ^ 2) t := by
  have hne : (1 - 216 / 7000 * t) ≠ 0 := by
    have := ht.2; have := ht.1; intro h; nlinarith
  have hu : HasDerivAt (fun s : ℝ => 1 - 216 / 7000 * s) (-(216 / 7000)) t := by
    simpa using ((hasDerivAt_id t).const_mul (216 / 7000 : ℝ)).const_sub 1
  have h2 := (hu.inv hne).const_mul (1 / 7000 : ℝ)
  convert h2 using 1
  · funext s; simp [kTight, div_eq_mul_inv]
  · unfold kTight; field_simp

theorem primRhsGUE_const_len_two (c : ℂ) (I : LoopIdx (Zd 3 3)) (hI : I.length = 2) :
    primRhsGUE 3 3 2 (fun _ => c) I = 216 * c ^ 2 := by
  have hL : ((3 : ℂ) ^ 3) ≠ 0 := by norm_num
  simp only [primRhsGUE, primBilGUE, hI, SBgue_apply, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h12]
  simp
  field_simp
  ring

theorem kTight_zero : kTight 0 = 1 / 7000 := by norm_num [kTight]

/-- `K(1) = 1/6784 > K(0) = 1/7000`: the solution is nonzero and growing. -/
theorem kTight_one : kTight 1 = 1 / 6784 := by norm_num [kTight]

/-- Target `eq736` at the nonzero tight solution `K(t) = K₀ / (1 - N K₀ t)` of `K' = N K²` at
`n = 2` (`d = 3`, `L = 3`, `W = 2`, `N = 216`, `K₀ = 1/7000`, `t₁ = 0`, `t₀ = 1`, `A = 1`,
`λ ≡ 7000`, `ε = N/λ = 216/7000`, `4 n³ A ε = 0.987 < 1`; `K(1) λ = 1.032 < 2`). -/
theorem inst_eq736_tight : ∀ t ∈ Icc (0 : ℝ) 1, ∀ I : LoopIdx (Zd 3 3), I.WF → 2 ≤ I.length →
    I.length ≤ 2 →
    ‖(fun (t : ℝ) (_ : LoopIdx (Zd 3 3)) => (kTight t : ℂ)) t I‖ <
      2 * (1 : ℝ) * ((fun _ : ℝ => (7000 : ℝ)) t)⁻¹ ^ (I.length - 1) :=
  eq736 3 3 2 (fun t _ => (kTight t : ℂ)) (n := 2) (t1 := 0) (t0 := 1) (A := 1)
    (ε := 216 / 7000) zero_le_one (fun _ => 7000) (fun _ _ => by norm_num)
    (fun _ _ _ _ _ => le_rfl) continuousOn_const
    (fun t ht I _ h2 h2' => by
      have hI : I.length = 2 := le_antisymm h2' h2
      have h := (kTight_hasDerivAt ht).ofReal_comp.hasDerivWithinAt (s := Icc (0 : ℝ) 1)
      rw [primRhsGUE_const_len_two _ I hI]
      convert h using 1
      push_cast
      ring)
    one_pos
    (fun I _ h2 h2' => by
      have hI : I.length = 2 := le_antisymm h2' h2
      rw [hI]
      simp only [kTight, Complex.norm_real, Real.norm_eq_abs]
      norm_num)
    (fun t ht => by
      have h2 : t ≤ 1 := ht.2
      change (((2 * 3) ^ 3 : ℕ) : ℝ) * (t - 0) ≤ 216 / 7000 * 7000
      norm_num
      linarith)
    (by norm_num)

end BootstrapCheck

end RBM.Univ.GUEPhase

end
