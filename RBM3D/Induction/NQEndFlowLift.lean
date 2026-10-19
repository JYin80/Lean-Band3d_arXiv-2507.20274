/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins
import RBM3D.Gauss.Domination
import RBM3D.Loop.KLFinal
import RBM3D.Loop.KLTreeDeriv
import RBM3D.Loop.KBound
import RBM3D.Loop.TreeRep
import RBM3D.Loop.Unique
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The monotone envelope of a bound and the time modulus of `𝒦^{(k)}` (`d ≥ 3`)

Tools for the uniform-in-time non-alternating endpoint at the flow (the uniform statement `STNQConcl''`, from the
per-time `STNQConclPT''` of `Induction/NQEndFlow`).
Paper: Lemma 4.6 (`lem:STOeq_NQ`, bound (4.22) `am;asoiuw`, and its proof).

## What is here

* §1 the vocabulary `RBM.Ind.nqFlowSharp`: the monotone envelope
  `X♯(m,n,u) = max 1 (inf_{u' ∈ [u, t_n]} X(m,n,u'))` of a bound (`1 ≤ X♯ ≤ X`, non-decreasing
  on `u ≤ t_n`);
* §2 the time modulus of `𝒦^{(k)}`, every `k ≥ 2` (public `RBM.Gauss.Sizes.stKloop_lip`): tree
  equations `KLK_isKLoop`, the uniform crude bound `KLbound_holds`, the mean value theorem.

Every helper that is not part of the statements is `private` or prefixed `nqLift_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The vocabulary: the monotone envelope of a bound -/

/-- **The monotone envelope `X♯` of a bound**: `X♯(m,n,u) =
inf_{u' ∈ [u, t_n]} X(m,n,u')`, floored at `1` (the floor is inactive for `u ≤ t_n` when `X ≥ 1`; for `u > t_n` the
set is empty and `X♯ = 1`).  `1 ≤ X♯ ≤ X`, non-decreasing in `u ≤ t_n`. -/
noncomputable def nqFlowSharp (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  max 1 (sInf (X m n '' Set.Icc u (t n)))

end RBM.Ind

/-! ## 2. The time modulus of `𝒦^{(k)}`, every `k ≥ 2`

The tree equations (2.50) `pro_dyncalK` (`KLK_isKLoop`: `∂_t 𝒦^{(k)} = treeEqRhs`, on `t ∈ [0, 1)`) with the uniform crude
bound `KLbound_holds` (constants depending on `(d, m, κ, gmax, τ)` only, `τ = 1`) for the cut loops (lengths
`i + k - l + 1`, `l - i + 1 ∈ [2, k]`, total `k + 2`) bound the derivative by `k² C² 2^k N^{k+3} ≤ N^{2k+2}`
(eventually), and the mean value theorem on `[0, t_n]` gives the Lipschitz constant (the paper does not state a
time modulus of `𝒦^{(k)}`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Modulus

/-- A loop index of length `m` is `KLloopOf σ a` for vectors `σ`, `a`. -/
private theorem nqLift_loopOf_eq {d L : ℕ} (J : LoopIdx (Zd d L)) (hJ : J.WF) {m : ℕ} (hm : J.length = m) :
    ∃ (σ : Fin m → Bool) (a : Fin m → Zd d L), J = KLloopOf d L σ a := by
  obtain ⟨σl, al⟩ := J
  have hal : al.length = m := hm
  subst hal
  have hJ' : σl.length = al.length := hJ
  refine ⟨fun i => σl.get (Fin.cast hJ'.symm i), al.get, ?_⟩
  refine LoopIdx.ext ?_ ?_
  · change σl = List.ofFn (fun i : Fin al.length => σl.get (Fin.cast hJ'.symm i))
    apply List.ext_getElem <;> simp [hJ']
  · change al = List.ofFn al.get
    exact (List.ofFn_get al).symm

/-- **The crude bound of `𝒦^{(m)}`** (`ML:Kbound` with `τ = 1`) as a statement about loop indices, with the constant
uniform over `KLPar κ gmax`. -/
private theorem nqLift_KLK_bound {d : ℕ} (hd : 3 ≤ d) {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (J : LoopIdx (Zd d p.L)), J.WF → J.length = m →
      ‖KLK d p.L p.g p.W p.E p.t J‖ ≤
        C * (p.L : ℝ) * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (m - 1) := by
  obtain ⟨C, hC, H⟩ := KLbound_holds d m κ gmax hd hm hκ hg 1 one_pos
  refine ⟨C, hC, fun p J hJ hJm => ?_⟩
  obtain ⟨σ, a, rfl⟩ := nqLift_loopOf_eq J hJ hJm
  have h := H p σ a
  rwa [Real.rpow_one] at h

/-- **The tree-equation right side is bounded by the product bound of its cut loops**: if every loop `J` of length
`2 ≤ |J| ≤ n` has `‖K J‖ ≤ C X^{|J|-1}`, then `‖treeEqRhs K I‖ ≤ W^d n² L^{2d} C² X^n` for `|I| = n` (the two cut
loops of `(k, l)` have lengths `k + n - l + 1`, `l - k + 1 ∈ [2, n]` with `(k + n - l) + (l - k) = n`;
`|S^{(B)}_{ab}| ≤ 1`). -/
private theorem nqLift_treeEq_bound {d L W : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L)
    {K : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)} {n : ℕ} (hI : I.WF) (hn : I.length = n)
    {X C : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hK : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n → ‖K J‖ ≤ C * X ^ (J.length - 1)) :
    ‖treeEqRhs d L W g K I‖ ≤
      (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d)) * (C ^ 2 * X ^ n) := by
  have hcardZ : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_Zd]; push_cast; rfl
  have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ l ∈ Finset.Ioc k I.length, ∀ a b : Zd d L,
      ‖K (I.cutGlueL k l a) * SB d L g a b * K (I.cutGlueR k l b)‖ ≤ C ^ 2 * X ^ n := by
    intro k hk l hl a b
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hlenL := LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2
    have hlenR := LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2
    have hwL := LoopIdx.wf_cutGlueL I a hI hk.1 hl.1 hl.2
    have hwR := LoopIdx.wf_cutGlueR I b hI hk.1 hl.1 hl.2
    have h1 := hK _ hwL (by rw [hlenL]; omega) (by rw [hlenL]; omega)
    have h2 := hK _ hwR (by rw [hlenR]; omega) (by rw [hlenR]; omega)
    have hS := norm_SB_apply_le (d := d) (L := L) (g := g) hL a b
    have hX1 : 0 ≤ C * X ^ ((I.cutGlueL k l a).length - 1) := mul_nonneg hC (pow_nonneg hX _)
    have hX2 : 0 ≤ C * X ^ ((I.cutGlueR k l b).length - 1) := mul_nonneg hC (pow_nonneg hX _)
    rw [norm_mul, norm_mul]
    calc ‖K (I.cutGlueL k l a)‖ * ‖SB d L g a b‖ * ‖K (I.cutGlueR k l b)‖
        ≤ (C * X ^ ((I.cutGlueL k l a).length - 1)) * 1 *
            (C * X ^ ((I.cutGlueR k l b).length - 1)) :=
          mul_le_mul (mul_le_mul h1 hS (norm_nonneg _) hX1) h2 (norm_nonneg _) (by positivity)
      _ = C ^ 2 * X ^ n := by
          rw [hlenL, hlenR]
          have hexp : (k + I.length - l + 1 - 1) + (l - k + 1 - 1) = n := by omega
          calc C * X ^ (k + I.length - l + 1 - 1) * 1 * (C * X ^ (l - k + 1 - 1))
              = C ^ 2 * (X ^ (k + I.length - l + 1 - 1) * X ^ (l - k + 1 - 1)) := by ring
            _ = C ^ 2 * X ^ n := by rw [← pow_add, hexp]
  have hrhs : (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d)) * (C ^ 2 * X ^ n) =
      (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d) * (C ^ 2 * X ^ n)) := by ring
  rw [hrhs]
  unfold treeEqRhs
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum : ‖∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        K (I.cutGlueL k l a) * SB d L g a b * K (I.cutGlueR k l b)‖ ≤
      ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        C ^ 2 * X ^ n := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun l hl => (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hterm k hk l hl a b))))
  refine hsum.trans ?_
  have hT : 0 ≤ (L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)) := by positivity
  calc ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        C ^ 2 * X ^ n
      ≤ ∑ k ∈ Finset.Icc 1 I.length, ((n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardZ, Nat.card_Ioc]
        have hkn : ((I.length - k : ℕ) : ℝ) ≤ n := by
          rw [← hn]; exact_mod_cast Nat.sub_le _ _
        calc ((I.length - k : ℕ) : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))
            ≤ (n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n))) :=
              mul_le_mul_of_nonneg_right hkn hT
          _ = _ := rfl
    _ = (n : ℝ) * ((n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hn]
        simp
    _ = (n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d) * (C ^ 2 * X ^ n) := by ring

/-- `0 ≤ W^{-d} B_{r,0} ≤ 2 N` for `r ≤ t < 1` with `(1 - t)⁻¹ ≤ N` (`W^{-d} B_{r,0} ≤ W^{-d} 2 (1 - r)⁻¹`,
`(1 - r)⁻¹ ≤ (1 - t)⁻¹`; `cont_Bctl_eq`). -/
private theorem nqLift_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {r t : ℝ} (hrt : r ≤ t) (ht : t < 1) {N : ℝ}
    (htN : (1 - t)⁻¹ ≤ N) : sz.Bctl n r ≤ 2 * N := by
  have hr1 : r < 1 := hrt.trans_lt ht
  rw [RBM.Ind.ContinuityNet.cont_Bctl_eq sz n hr1]
  have h1t : 0 < 1 - t := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hy : (1 - r)⁻¹ ≤ N := (inv_anti₀ h1t (by linarith)).trans htN
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have e1 : (sz.lam n ^ 2 + (1 - r))⁻¹ ≤ (1 - r)⁻¹ :=
    inv_anti₀ h1r (by nlinarith [sq_nonneg (sz.lam n)])
  have e2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹ ≤ (1 - r)⁻¹ :=
    inv_anti₀ h1r (by nlinarith)
  have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
  have hsum : (sz.lam n ^ 2 + (1 - r))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹ ≤ 2 * N := by
    linarith
  have hnn : 0 ≤ (sz.lam n ^ 2 + (1 - r))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - r))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - r))⁻¹)
      ≤ 1 * (2 * N) := mul_le_mul hWi hsum hnn zero_le_one
    _ = 2 * N := one_mul _

/-- **The time modulus of `𝒦^{(k)}`, every `k ≥ 2`**: Lipschitz in time with the polynomial constant `N^{2k+2}`,
uniformly in the labels on `[0, t_n]`, for sequences
with `|E_n| ≤ 2 - κ`, `0 < lam_n ≤ gmax` and `(1 - t_n)⁻¹ ≤ N` eventually (and `N → ∞`).  `KLK_isKLoop` gives
`∂_t 𝒦^{(k)} = treeEqRhs` on `[0, 1)`; the cut loops have lengths in `[2, k]` and `KLbound_holds` (constants depending
on `(d, m, κ, gmax)` only, `τ = 1`) bounds `‖treeEqRhs‖ ≤ k² C² 2^k N^{k+3} ≤ N^{2k+2}` (eventually); then the mean value
theorem on the convex set `[0, t_n]`.  `κ` and `gmax` are fixed before `n` (so the constants do not depend on `n`). -/
theorem stKloop_lip {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hsize : sz.SizeTendsto) (E t : ℕ → ℝ) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) (ht : ∀ n, t n < 1)
    (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ‖STKloop sz n (E n) u σ a - STKloop sz n (E n) u' σ a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'| := by
  -- the constants of `ML:Kbound` (`τ = 1`) for the lengths `0 … k`
  have hC : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ (1 ≤ m → ∀ (p : KLPar κ gmax) (J : LoopIdx (Zd d p.L)), J.WF →
      J.length = m → ‖KLK d p.L p.g p.W p.E p.t J‖ ≤
        C * (p.L : ℝ) * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (m - 1)) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, hC0, hCb⟩ := nqLift_KLK_bound hd hκ hg m hm
      exact ⟨C, hC0, fun _ => hCb⟩
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose Cf hCf0 hCf using hC
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ∑ m ∈ Finset.range (k + 1), Cf m := ⟨_, rfl⟩
  have hCm_ge : ∀ m ≤ k, Cf m ≤ Cm := fun m hm => by
    rw [hCm]
    exact Finset.single_le_sum (f := Cf) (fun i _ => (hCf0 i).le) (Finset.mem_range.2 (by omega))
  have hCm0 : 0 < Cm := lt_of_lt_of_le (hCf0 0) (hCm_ge 0 (Nat.zero_le k))
  filter_upwards [hE, hlam, htN,
    hsize.eventually_ge_atTop (max 1 ((k : ℝ) * k * Cm ^ 2 * 2 ^ k))] with n hEn hlamn htNn hNn
  intro u u' hu0 hut hu'0 hu't σ a
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hNn
  have hNQ : (k : ℝ) * k * Cm ^ 2 * 2 ^ k ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hNn
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hE2 : |E n| < 2 := by linarith
  have hKL := (KLK_isKLoop d (sz.L n) (sz.W n) (sz.lam n) (E n) hL3 hW1 hE2).1
  have hIWF : (KLloopOf d (sz.L n) σ a).WF := by simp [KLloopOf, LoopIdx.WF]
  have hIlen : (KLloopOf d (sz.L n) σ a).length = k := by simp [KLloopOf, LoopIdx.length]
  -- the counting facts
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW1)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hLd1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hLdN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hsz]; nlinarith
  have hL2d : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 (by omega)
  have hcount : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) *
      ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
    have hLd0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    have h1 : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) =
        ((sz.size n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) ^ d := by rw [hsz]; ring
    rw [h1]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ 2
        ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by
          gcongr
          exact hL2d.trans hLdN
      _ = ((sz.size n : ℕ) : ℝ) ^ 3 := by ring
  -- the derivative of `𝒦^{(k)}` is bounded by `N^{2k+2}` on `[0, t_n]`
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) (t n),
      ‖treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r)
        (KLloopOf d (sz.L n) σ a)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) := by
    intro r hr
    have hr1 : r < 1 := hr.2.trans_lt (ht n)
    have hX0 : 0 ≤ sz.Bctl n r := (st_Bctl_pos sz hr1).le
    have hXle : sz.Bctl n r ≤ 2 * ((sz.size n : ℕ) : ℝ) := nqLift_Bctl_le sz n hr.2 (ht n) htNn
    have hKJ : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r J‖ ≤
          (Cm * ((sz.L n : ℕ) : ℝ)) * (sz.Bctl n r) ^ (J.length - 1) := by
      intro J hJ h2 hJk
      have h := hCf J.length (by omega)
        (⟨sz.L n, sz.W n, hL3, hW1, sz.lam n, hlamn.1, hlamn.2, E n, hEn, r, hr.1, hr1⟩ : KLPar κ gmax)
        J hJ rfl
      refine h.trans ?_
      have hL0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
      have hCle := hCm_ge J.length hJk
      have hXp : 0 ≤ (sz.Bctl n r) ^ (J.length - 1) := pow_nonneg hX0 _
      change Cf J.length * ((sz.L n : ℕ) : ℝ) * (sz.Bctl n r) ^ (J.length - 1) ≤
        (Cm * ((sz.L n : ℕ) : ℝ)) * (sz.Bctl n r) ^ (J.length - 1)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hL0) hXp
    have h1 := nqLift_treeEq_bound (W := sz.W n) (g := sz.lam n) hL3 hIWF hIlen
      (X := sz.Bctl n r) (C := Cm * ((sz.L n : ℕ) : ℝ)) (by positivity) hX0 hKJ
    have hXk : (sz.Bctl n r) ^ k ≤ (2 * ((sz.size n : ℕ) : ℝ)) ^ k := pow_le_pow_left₀ hX0 hXle k
    calc ‖treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r)
          (KLloopOf d (sz.L n) σ a)‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * k * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) *
            ((Cm * ((sz.L n : ℕ) : ℝ)) ^ 2 * (sz.Bctl n r) ^ k) := h1
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * k * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) *
            ((Cm * ((sz.L n : ℕ) : ℝ)) ^ 2 * (2 * ((sz.size n : ℕ) : ℝ)) ^ k) := by
          gcongr
      _ = ((k : ℝ) * k * Cm ^ 2 * 2 ^ k) *
            (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) *
              ((sz.L n : ℕ) : ℝ) ^ 2) * ((sz.size n : ℕ) : ℝ) ^ k := by
          rw [mul_pow, mul_pow]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) ^ k := by
          gcongr
      _ = ((sz.size n : ℕ) : ℝ) ^ (k + 4) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) := pow_le_pow_right₀ hN1 (by omega)
  -- the mean value theorem on `[0, t_n]`
  have hf : ∀ r ∈ Set.Icc (0 : ℝ) (t n),
      HasDerivWithinAt (fun r => KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r (KLloopOf d (sz.L n) σ a))
        (treeEqRhs d (sz.L n) (sz.W n) (sz.lam n) (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r)
          (KLloopOf d (sz.L n) σ a)) (Set.Icc (0 : ℝ) (t n)) r :=
    fun r hr => (hKL r ⟨hr.1, hr.2.trans_lt (ht n)⟩ (KLloopOf d (sz.L n) σ a) hIWF
      (by rw [hIlen]; exact hk)).hasDerivWithinAt
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun r => treeEqRhs d (sz.L n) (sz.W n) (sz.lam n)
      (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) r) (KLloopOf d (sz.L n) σ a))
    hf hbound (convex_Icc (0 : ℝ) (t n)) ⟨hu'0, hu't⟩ ⟨hu0, hut⟩
  rw [Real.norm_eq_abs] at hmvt
  exact hmvt

end Modulus

end RBM.Gauss.Sizes

end
