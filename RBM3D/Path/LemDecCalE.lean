/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Green.Pins
import RBM3D.Path.KellStar
import Mathlib.Analysis.PSeries

/-!
# `lem_dec_calE`, first part: the loss, the hypothesis bundle, the `LK×LK` bound (S5-05)

Ticket T2164 (S5-05, ST-4).  Port of `RBM2D/Path/LemDecCalE.lean` at commit `c9a24cf` (cited
`LemDecCalE:<line>`: `lossE2` `:53`, `E2Hyp` `:61`, `LemDecCalE_lk` `:72`, (e1)-(e10) `:85-650`,
`lemDecCalE_lk` `:375`, witness `:1190`) to `d ≥ 3`.  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem_dec_calE` `3_5:2314-2338` (the paper omits the
proof, "a special case of [YY_25, Lemma 5.7]", `3_5:2338`), `res_deccalE_lk` `3_5:2318`,
`def_ELKLK` `3_5:97`, `def_WTuD` `3_5:2297`, (`GijGEX`) `3_5:24`.

Differences from RBM2D (every one forced by `d ≥ 3` or by the premise bundle):
* the lattice is `Zd d L`, the fine lattice `Idx d L W`; the scale `M_u = W² ℓ_u² η_u` is
  `M_u = W^d (1 - u)` (`ℓ_u = 1` as `1 - u ≥ ilambda²`, `3_5:2287`; no `Im m`); `𝒯_{u,D}` is the
  merged `tailTD` of `def_WTuD` (amplitude `M_u⁻²`), the distance is `zdistInf`;
* the class-(c) set `goodSet` of RBM2D is replaced by explicit premises on the matrix `M`
  (clauses 1, 3, 4, 6 of `goodSet`, the only ones RBM2D projects): `E2Hyp` has one conjunct
  per use;
* the ball `{|z|_∞ ≤ 1}` of `Z_L^d` has `3^d` points, so the neighbour-pair count of
  (`GijGEX`) is `9^d` (RBM2D: `5 · 5 = 25`): the constants of (e7), (e8) are `9^d`, `2 · 9^d`;
* the convolution of `𝒯_{u,D}` over `Z_L^d` (RBM2D: `convTailT`, `2500`) is proved here with
  the constant `S_d = (1 + 1536 d⁴)^d ≥ Σ_{z ∈ Z_L^d} exp(-½ |z|_∞^{1/2})` (product bound
  `exp(-½ √max) ≤ Π exp(-(2d)⁻¹ √·)`, `Σ_{j ≥ 1} j⁻² ≤ 2`);
* the floor condition (C3) `L² W¹² ≤ W^{D/2}` is `L^d W^{2d} ≤ W^D`; the loss `lossE2` carries
  a `d`-dependent leading constant `(1600 d⁴)^d` that dominates `e (2 S_d + 1)`;
* the conclusion is at the single time `u` of `STLemDecCalEConcl` (RBM2D: an endpoint `v ≥ u`),
  for the `𝓔^{LK×LK}` of the model `STELKLKM`, and all `σ ∈ {±}²`; the control `J*` is a real
  `J` with `‖STLKM σ a‖ ≤ J T_{u,D}(|a₁ - a₂|)`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green

/-! ## 0. The loss, the hypothesis bundle and the pinned statement -/

/-- The explicit loss of the deterministic `lem_dec_calE` bounds (it replaces the `≺` of the paper):
`10¹² (1600 d⁴)^d K₀² Λ⁶ (1 + log(L^d W^{2d}))⁴ (1 + log W)³ exp(8 (log W)^{3/4})`.  RBM2D
(`LemDecCalE:53`) has `10¹²` and `log(L² W¹²)`; the leading constant carries `d` because the
convolution constant `e (2 S_d + 1)` of `res_deccalE_lk` grows like `(1536 d⁴)^d`. -/
def lossE2 (d L W : ℕ) (Λ K₀ : ℝ) : ℝ :=
  10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * K₀ ^ 2 * Λ ^ 6 *
    (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (2 * d))) ^ 4 *
    (1 + Real.log W) ^ 3 * Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4))

/-- The hypotheses of the deterministic `lem_dec_calE` bounds at one time `u` (regime (iii),
`1 - u ≥ ilambda²`), as numeric premises on the fine matrix `M` (`H_u`), at size index `n`,
`M_u = W^d (1 - u)`:
`3 ≤ d`, `|E| < 2`, `0 ≤ u < 1`, `0 < lam`, `lam² ≤ 1 - u`, `1 ≤ lam² W^d`, `1 ≤ Λ`, `1 ≤ K₀`,
`W ≥ e⁴`; the floor condition `L^d W^{2d} ≤ W^D` (C3); `M` Hermitian (clause 1 of `goodSet`);
(P-e6) `|G_{xy} - δ_{xy} m| ≤ Λ M_u^{-1/4}` (clause 3); (P-e7/8) `|G_{pq}|² ≤ Λ gexRHS([q],[p])` for
`p ≠ q` (clause 4, the swapped pair of `GijGEXPTSwap`); (P-e9) `|⟨G̃(σ) E_a⟩| ≤ Λ M_u⁻¹`
(clause 6, `(ℓ_u/ℓ_s)² = 1`); the control `1 ≤ J ≤ W` with `‖(𝓛-𝒦)^{(2)}_{σ,a}‖ ≤ J T_{u,D}(|a₁-a₂|)`;
the `𝒦` bound `‖𝒦_{(+,-),(a,b)}‖ ≤ K₀ M_u⁻¹`; (`Kell*`) `‖𝒦_{(+,-),(a,b)}‖ ≤ W^{-D}` for
`|a - b| ≥ ℓ*_u / 8`, `ℓ*_u = (log W)^{3/2} ℓ_u` (the shape of `KellStarEv`, `Path/KellStar.lean:54`). -/
def E2Hyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  3 ≤ d ∧ |E| < 2 ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧
    1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
    ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    M.IsHermitian ∧
    (∀ x y : Idx d (sz.L n) (sz.W n),
      ‖Gres M (zt E u) true x y - (if x = y then mE E else 0)‖ ≤
        Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ ((1 : ℝ) / 4)) ∧
    (∀ p q : Idx d (sz.L n) (sz.W n), p ≠ q →
      ‖Gres M (zt E u) true p q‖ ^ 2 ≤
        Λ * gexRHS d (sz.L n) (sz.W n) E u M (STblk sz n q) (STblk sz n p)) ∧
    (∀ (σ : Bool) (a : Zd d (sz.L n)),
      ‖avgErr d (sz.L n) (sz.W n) E u M σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
    1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STLKM sz n E u M σ a‖ ≤ J * STtailTD sz n u D a) ∧
    (∀ a b : Zd d (sz.L n),
      ‖STKloop sz n E u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
    (∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
          (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖STKloop sz n E u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **`res_deccalE_lk`** (`3_5:2318`, deterministic form): under `E2Hyp`, for every `σ ∈ {±}²` and
`a ∈ (Z_L^d)²`,
`|𝓔^{LK×LK}_{u,σ,a}| ≤ lossE2 · (1-u)⁻¹ (W^d|1-u|)⁻¹ J² · T_{u,D}(|a₁-a₂|)`: the scale of the first
conjunct of `STLemDecCalEConcl` (`Induction/Step5Pins.lean:161`). -/
def LemDecCalE_lk (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2Hyp sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STELKLKM sz n E u M σ a‖ ≤ lossE2 d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2) * STtailTD sz n u D a

/-! ## 1. Lattice facts: distance, ball counts, the sum `S_d` -/

section Lattice

private theorem lemDecCalE_zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem lemDecCalE_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem lemDecCalE_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

private theorem lemDecCalE_zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact lemDecCalE_zdistInf_add_le d L _ _

private theorem lemDecCalE_zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, lemDecCalE_zdistInf_neg]

private theorem lemDecCalE_zdist_le_zdistInf (d L : ℕ) (x : Zd d L) (i : Fin d) :
    zdist L (x i) ≤ zdistInf d L x :=
  Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)

/-- `|a₁ - a₂| ≤ |a₁ - b| + |b - a₂|` as reals. -/
private theorem lemDecCalE_zdistInf_tri_real (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    (zdistInf d L (x - w) : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + (zdistInf d L (y - w) : ℝ) := by
  exact_mod_cast lemDecCalE_zdistInf_tri d L x y w

/-- The points of `Z_L` at periodic distance `≤ m` are the images of the integers `-m, ..., m`. -/
private theorem lemDecCalE_zmod_ball_card (L : ℕ) [NeZero L] (m : ℕ) :
    (Finset.univ.filter fun y : ZMod L => zdist L y ≤ m).card ≤ 2 * m + 1 := by
  have hsub : (Finset.univ.filter fun y : ZMod L => zdist L y ≤ m) ⊆
      (Finset.Icc (-(m : ℤ)) m).image (fun k : ℤ => (k : ZMod L)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_image, Finset.mem_Icc]
    have hv : y.val < L := ZMod.val_lt y
    unfold zdist at hy
    by_cases h1 : y.val ≤ m
    · refine ⟨(y.val : ℤ), ⟨by omega, by exact_mod_cast h1⟩, ?_⟩
      simp
    · have h2 : L - y.val ≤ m := by omega
      refine ⟨-((L - y.val : ℕ) : ℤ), ⟨by omega, by omega⟩, ?_⟩
      have hle : y.val ≤ L := hv.le
      push_cast [Nat.cast_sub hle]
      simp
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp only [Int.card_Icc]
  omega

/-- (e10) (a): the ball of the periodic `L^∞` distance, `#{u : |a - u|_∞ ≤ m} ≤ (2m+1)^d`
for natural `m`. -/
theorem LemDecCalE_e10a_nat {d L : ℕ} [NeZero L] (a : Zd d L) (m : ℕ) :
    (Finset.univ.filter fun u : Zd d L => zdistInf d L (a - u) ≤ m).card ≤ (2 * m + 1) ^ d := by
  have hsub : (Finset.univ.filter fun u : Zd d L => zdistInf d L (a - u) ≤ m) ⊆
      (Fintype.piFinset fun i : Fin d =>
        (Finset.univ.filter fun y : ZMod L => zdist L y ≤ m)).image (fun z => a - z) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_image, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨a - u, fun i => ?_, by abel⟩
    exact (lemDecCalE_zdist_le_zdistInf d L (a - u) i).trans hu
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Fintype.card_piFinset]
  calc ∏ i : Fin d, (Finset.univ.filter fun y : ZMod L => zdist L y ≤ m).card
      ≤ ∏ _i : Fin d, (2 * m + 1) :=
        Finset.prod_le_prod fun i _ => lemDecCalE_zmod_ball_card L m
    _ = (2 * m + 1) ^ d := by simp

/-- (e10) (a), real radius: `#{u : |a - u|_∞ ≤ R} ≤ (2R+1)^d` for `R ≥ 0`. -/
theorem LemDecCalE_e10a {d L : ℕ} [NeZero L] (a : Zd d L) (R : ℝ) (hR : 0 ≤ R) :
    (((Finset.univ.filter fun u : Zd d L => (zdistInf d L (a - u) : ℝ) ≤ R).card : ℕ) : ℝ) ≤
      (2 * R + 1) ^ d := by
  have hsub : (Finset.univ.filter fun u : Zd d L => (zdistInf d L (a - u) : ℝ) ≤ R) ⊆
      (Finset.univ.filter fun u : Zd d L => zdistInf d L (a - u) ≤ ⌊R⌋₊) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact Nat.le_floor hu
  have h1 := (Finset.card_le_card hsub).trans (LemDecCalE_e10a_nat a ⌊R⌋₊)
  have h2 : ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * R + 1 := by
    push_cast
    have := Nat.floor_le hR
    linarith
  calc (((Finset.univ.filter fun u : Zd d L => (zdistInf d L (a - u) : ℝ) ≤ R).card : ℕ) : ℝ)
      ≤ (((2 * ⌊R⌋₊ + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ (2 * R + 1) ^ d := pow_le_pow_left₀ (by positivity) h2 d

/-- (e10) (b): the sharp ball count, `#{a' : |a' - a|_∞ ≤ 1} ≤ 3^d` (the `3^d` points of the
nearest-neighbour cube; RBM2D: `5` for the `ℓ¹` ball of `Z_L²`, `25` pairs). -/
theorem LemDecCalE_e10b {d L : ℕ} [NeZero L] (a : Zd d L) :
    ((Finset.univ.filter fun a' : Zd d L => zdistInf d L (a' - a) ≤ 1).card : ℝ) ≤ 3 ^ d := by
  have h := LemDecCalE_e10a_nat (d := d) (L := L) a 1
  have heq : (Finset.univ.filter fun a' : Zd d L => zdistInf d L (a' - a) ≤ 1) =
      (Finset.univ.filter fun u : Zd d L => zdistInf d L (a - u) ≤ 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [lemDecCalE_zdistInf_sub_comm]
  rw [heq]
  exact_mod_cast h

end Lattice

/-! ## 2. The convolution sums of `T_{u,D}` over `Z_L^d` -/

section Conv

/-- `exp(-γ √j) ≤ 24 / (γ⁴ j²)` for `j ≥ 1` (`e^y ≥ y⁴/24`). -/
private theorem lemDecCalE_exp_neg_le {γ : ℝ} (hγ : 0 < γ) {j : ℕ} (hj : 1 ≤ j) :
    Real.exp (-(γ * Real.sqrt j)) ≤ 24 / (γ ^ 4 * (j : ℝ) ^ 2) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hx : 0 ≤ γ * Real.sqrt j := by positivity
  have h := Real.pow_div_factorial_le_exp (γ * Real.sqrt j) hx 4
  have hsq : (γ * Real.sqrt j) ^ 4 = γ ^ 4 * (j : ℝ) ^ 2 := by
    rw [mul_pow]
    congr 1
    have : Real.sqrt j ^ 2 = j := Real.sq_sqrt hj0.le
    calc Real.sqrt j ^ 4 = (Real.sqrt j ^ 2) ^ 2 := by ring
      _ = (j : ℝ) ^ 2 := by rw [this]
  rw [hsq] at h
  have h24 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at h
  have hpos : 0 < γ ^ 4 * (j : ℝ) ^ 2 / 24 := by positivity
  rw [Real.exp_neg]
  calc (Real.exp (γ * Real.sqrt j))⁻¹ ≤ (γ ^ 4 * (j : ℝ) ^ 2 / 24)⁻¹ := inv_anti₀ hpos h
    _ = 24 / (γ ^ 4 * (j : ℝ) ^ 2) := by rw [inv_div]

/-- `Σ_{j=1}^{m} exp(-γ √j) ≤ 48 / γ⁴` (`Σ j⁻² ≤ 2`). -/
private theorem lemDecCalE_sum_exp_le {γ : ℝ} (hγ : 0 < γ) (m : ℕ) :
    ∑ j ∈ Finset.range m, Real.exp (-(γ * Real.sqrt ((j + 1 : ℕ) : ℝ))) ≤ 48 / γ ^ 4 := by
  have h1 : ∑ j ∈ Finset.range m, Real.exp (-(γ * Real.sqrt ((j + 1 : ℕ) : ℝ))) ≤
      ∑ j ∈ Finset.range m, (24 / γ ^ 4) * ((((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := lemDecCalE_exp_neg_le hγ (j := j + 1) (by omega)
    refine this.trans (le_of_eq ?_)
    field_simp
  have h2 : ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1)
    have heq : ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ =
        ∑ i ∈ Finset.Ioo 0 (m + 1), ((i : ℝ) ^ 2)⁻¹ := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun i : ℕ => ((i : ℝ) ^ 2)⁻¹) 0 m 1]
      congr 1
    rw [heq]
    simpa using this
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  calc 24 / γ ^ 4 * ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 24 / γ ^ 4 * 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 48 / γ ^ 4 := by ring

/-- `Σ_{y ∈ Z_L} g(y.val) = Σ_{v < L} g(v)`. -/
private theorem lemDecCalE_sum_val (L : ℕ) [NeZero L] (g : ℕ → ℝ) :
    ∑ y : ZMod L, g y.val = ∑ v ∈ Finset.range L, g v := by
  refine Finset.sum_bij (fun y _ => y.val) (fun y _ => Finset.mem_range.2 (ZMod.val_lt y))
    (fun a _ b _ h => ZMod.val_injective L h) (fun v hv => ?_) (fun y _ => rfl)
  exact ⟨(v : ZMod L), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hv)⟩

/-- The one-dimensional sum `Σ_{y ∈ Z_L} exp(-γ √|y|_L) ≤ 1 + 96/γ⁴`, uniformly in `L`. -/
private theorem lemDecCalE_sum_zdist_le (L : ℕ) [NeZero L] {γ : ℝ} (hγ : 0 < γ) :
    ∑ y : ZMod L, Real.exp (-(γ * Real.sqrt (zdist L y : ℝ))) ≤ 1 + 96 / γ ^ 4 := by
  set F : ℕ → ℝ := fun j => Real.exp (-(γ * Real.sqrt (j : ℝ))) with hF
  have hF0 : ∀ j, 0 ≤ F j := fun j => (Real.exp_pos _).le
  have hpt : ∀ y : ZMod L, Real.exp (-(γ * Real.sqrt (zdist L y : ℝ))) ≤
      F y.val + F (L - y.val) := by
    intro y
    unfold zdist
    rcases min_choice y.val (L - y.val) with h | h
    · rw [h]; simp only [hF]; linarith [hF0 (L - y.val), hF0 y.val]
    · rw [h]; simp only [hF]; linarith [hF0 (L - y.val), hF0 y.val]
  have hsum1 : ∑ y : ZMod L, F y.val ≤ 1 + 48 / γ ^ 4 := by
    rw [lemDecCalE_sum_val L F]
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by have := NeZero.pos L; omega⟩
    rw [hm, Finset.sum_range_succ']
    have h0 : F 0 = 1 := by simp [hF]
    have := lemDecCalE_sum_exp_le hγ m
    simp only [hF] at h0 ⊢
    rw [h0]
    linarith
  have hsum2 : ∑ y : ZMod L, F (L - y.val) ≤ 48 / γ ^ 4 := by
    rw [lemDecCalE_sum_val L (fun v => F (L - v))]
    have hrefl := Finset.sum_range_reflect (fun j => F (j + 1)) L
    have h3 : ∑ v ∈ Finset.range L, F (L - v) = ∑ j ∈ Finset.range L, F (j + 1) := by
      rw [← hrefl]
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.1 hj
      congr 1
      omega
    rw [h3]
    exact lemDecCalE_sum_exp_le hγ L
  calc ∑ y : ZMod L, Real.exp (-(γ * Real.sqrt (zdist L y : ℝ)))
      ≤ ∑ y : ZMod L, (F y.val + F (L - y.val)) := Finset.sum_le_sum fun y _ => hpt y
    _ = ∑ y : ZMod L, F y.val + ∑ y : ZMod L, F (L - y.val) := Finset.sum_add_distrib
    _ ≤ 1 + 96 / γ ^ 4 := by
        have : (96 : ℝ) / γ ^ 4 = 48 / γ ^ 4 + 48 / γ ^ 4 := by ring
        linarith

/-- **The lattice sum `S_d`**: `Σ_{z ∈ Z_L^d} exp(-½ √|z|_∞) ≤ (1 + 1536 d⁴)^d`, uniformly in `L`
(`exp(-½ √max_i |z_i|) ≤ Π_i exp(-(2d)⁻¹ √|z_i|)`, then the one-dimensional sum with `γ = (2d)⁻¹`). -/
theorem LemDecCalE_sum_zd_le (d L : ℕ) [NeZero L] (hd : 1 ≤ d) :
    ∑ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ))) ≤
      (1 + 1536 * (d : ℝ) ^ 4) ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set γ : ℝ := 1 / (2 * d) with hγ
  have hγ0 : 0 < γ := by positivity
  set g : ZMod L → ℝ := fun y => Real.exp (-(γ * Real.sqrt (zdist L y : ℝ))) with hg
  have hpt : ∀ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ))) ≤ ∏ i, g (z i) := by
    intro z
    simp only [hg]
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.2 ?_
    rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Finset.mul_sum]
    have hs : ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ) ≤ d * Real.sqrt (zdistInf d L z : ℝ) := by
      calc ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ)
          ≤ ∑ _i : Fin d, Real.sqrt (zdistInf d L z : ℝ) :=
            Finset.sum_le_sum fun i _ =>
              Real.sqrt_le_sqrt (by exact_mod_cast lemDecCalE_zdist_le_zdistInf d L z i)
        _ = d * Real.sqrt (zdistInf d L z : ℝ) := by simp
    calc γ * ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ)
        ≤ γ * (d * Real.sqrt (zdistInf d L z : ℝ)) := mul_le_mul_of_nonneg_left hs hγ0.le
      _ = 1 / 2 * Real.sqrt (zdistInf d L z : ℝ) := by rw [hγ]; field_simp
  have hprod : ∑ z : Zd d L, ∏ i, g (z i) = (∑ y : ZMod L, g y) ^ d := by
    have := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (ZMod L)))
      (fun _ y => g y)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    simp
  have h1d := lemDecCalE_sum_zdist_le L hγ0
  have hγ4 : 96 / γ ^ 4 = 1536 * (d : ℝ) ^ 4 := by
    rw [hγ]; field_simp; ring
  rw [hγ4] at h1d
  calc ∑ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ)))
      ≤ ∑ z : Zd d L, ∏ i, g (z i) := Finset.sum_le_sum fun z _ => hpt z
    _ = (∑ y : ZMod L, g y) ^ d := hprod
    _ ≤ (1 + 1536 * (d : ℝ) ^ 4) ^ d :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun y _ => (Real.exp_pos _).le) h1d d

/-- `√(p + q) ≤ √q + ½ √p` when `√p ≤ √q`. -/
private theorem lemDecCalE_sqrt_key {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : Real.sqrt p ≤ Real.sqrt q) :
    Real.sqrt (p + q) ≤ Real.sqrt q + 1 / 2 * Real.sqrt p := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hp
  have h2 := Real.sq_sqrt hq
  have h3 : Real.sqrt p * Real.sqrt p ≤ Real.sqrt p * Real.sqrt q :=
    mul_le_mul_of_nonneg_left hpq (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg q]

/-- The convolution of two stretched exponentials:
`exp(-√p - √q) ≤ exp(-√r) (exp(-½√p) + exp(-½√q))` for `r ≤ p + q`. -/
theorem LemDecCalE_exp_conv {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : r ≤ p + q) :
    Real.exp (-Real.sqrt p - Real.sqrt q) ≤
      Real.exp (-Real.sqrt r) *
        (Real.exp (-(1 / 2 * Real.sqrt p)) + Real.exp (-(1 / 2 * Real.sqrt q))) := by
  have hrs : Real.sqrt r ≤ Real.sqrt (p + q) := Real.sqrt_le_sqrt hr
  have hp0 := Real.sqrt_nonneg p
  have hq0 := Real.sqrt_nonneg q
  have e1 := (Real.exp_pos (-(1 / 2 * Real.sqrt p))).le
  have e2 := (Real.exp_pos (-(1 / 2 * Real.sqrt q))).le
  have e3 := (Real.exp_pos (-Real.sqrt r)).le
  rcases le_total (Real.sqrt p) (Real.sqrt q) with h | h
  · have hk := lemDecCalE_sqrt_key hp hq h
    have : -Real.sqrt p - Real.sqrt q ≤ -Real.sqrt r + -(1 / 2 * Real.sqrt p) := by linarith
    calc Real.exp (-Real.sqrt p - Real.sqrt q)
        ≤ Real.exp (-Real.sqrt r + -(1 / 2 * Real.sqrt p)) := Real.exp_le_exp.2 this
      _ = Real.exp (-Real.sqrt r) * Real.exp (-(1 / 2 * Real.sqrt p)) := Real.exp_add _ _
      _ ≤ _ := by nlinarith
  · have hk := lemDecCalE_sqrt_key hq hp h
    rw [add_comm] at hk
    have : -Real.sqrt p - Real.sqrt q ≤ -Real.sqrt r + -(1 / 2 * Real.sqrt q) := by linarith
    calc Real.exp (-Real.sqrt p - Real.sqrt q)
        ≤ Real.exp (-Real.sqrt r + -(1 / 2 * Real.sqrt q)) := Real.exp_le_exp.2 this
      _ = Real.exp (-Real.sqrt r) * Real.exp (-(1 / 2 * Real.sqrt q)) := Real.exp_add _ _
      _ ≤ _ := by nlinarith

/-- The sum of the product of two tails over `Z_L^d`:
`Σ_x T(|x - a₁|) T(|a₀ - x|) ≤ (2 S_d + 1) A T(|a₀ - a₁|)` for `T(r) = A e^{-√r} + w`, under the
floor `w L^d ≤ A` (the convolution `convTailT` of RBM2D, `2500 ℓ_u² M_u⁻²`, redone without `ℓ_u`
and `log L`). -/
theorem LemDecCalE_sum_tail_tail {d L : ℕ} [NeZero L] (hd : 1 ≤ d) {A w : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ w) (hfl : w * (L : ℝ) ^ d ≤ A) (a₀ a₁ : Zd d L) :
    ∑ x : Zd d L, (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
        (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
      (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) * A *
        (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w) := by
  set S : ℝ := (1 + 1536 * (d : ℝ) ^ 4) ^ d with hS
  set Er : ℝ := Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) with hEr
  have hEr0 : 0 ≤ Er := (Real.exp_pos _).le
  have hsum := LemDecCalE_sum_zd_le d L hd
  have hS1 : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) ≤ S := by
    have : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) =
        ∑ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ))) :=
      Fintype.sum_equiv (Equiv.subRight a₁) _ _ fun x => rfl
    rw [this]; exact hsum
  have hS2 : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ))) ≤ S := by
    have : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ))) =
        ∑ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ))) :=
      Fintype.sum_equiv (Equiv.subLeft a₀) _ _ fun x => by simp [lemDecCalE_zdistInf_sub_comm d L a₀ x]
    rw [this]; exact hsum
  have hpt : ∀ x : Zd d L, (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
        (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
      (A ^ 2 * Er + A * w) * (Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
        Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) + w ^ 2 := by
    intro x
    set p : ℝ := (zdistInf d L (x - a₁) : ℝ) with hp
    set q : ℝ := (zdistInf d L (a₀ - x) : ℝ) with hq
    have hp0 : 0 ≤ p := Nat.cast_nonneg _
    have hq0 : 0 ≤ q := Nat.cast_nonneg _
    have hr : (zdistInf d L (a₀ - a₁) : ℝ) ≤ p + q := by
      have := lemDecCalE_zdistInf_tri_real d L a₀ x a₁
      rw [hp, hq]; linarith
    have hconv := LemDecCalE_exp_conv hp0 hq0 hr
    have hep : Real.exp (-Real.sqrt p) ≤ Real.exp (-(1 / 2 * Real.sqrt p)) :=
      Real.exp_le_exp.2 (by linarith [Real.sqrt_nonneg p])
    have heq : Real.exp (-Real.sqrt p) ≤ Real.exp (-(1 / 2 * Real.sqrt p)) := hep
    have heq' : Real.exp (-Real.sqrt q) ≤ Real.exp (-(1 / 2 * Real.sqrt q)) :=
      Real.exp_le_exp.2 (by linarith [Real.sqrt_nonneg q])
    have hmul : Real.exp (-Real.sqrt p) * Real.exp (-Real.sqrt q) ≤
        Er * (Real.exp (-(1 / 2 * Real.sqrt p)) + Real.exp (-(1 / 2 * Real.sqrt q))) := by
      rw [← Real.exp_add]
      have : -Real.sqrt p + -Real.sqrt q = -Real.sqrt p - Real.sqrt q := by ring
      rw [this]; exact hconv
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    have hAw : 0 ≤ A * w := mul_nonneg hA hw
    calc (A * Real.exp (-Real.sqrt p) + w) * (A * Real.exp (-Real.sqrt q) + w)
        = A ^ 2 * (Real.exp (-Real.sqrt p) * Real.exp (-Real.sqrt q)) +
            A * w * (Real.exp (-Real.sqrt p) + Real.exp (-Real.sqrt q)) + w ^ 2 := by ring
      _ ≤ A ^ 2 * (Er * (Real.exp (-(1 / 2 * Real.sqrt p)) + Real.exp (-(1 / 2 * Real.sqrt q)))) +
            A * w * (Real.exp (-(1 / 2 * Real.sqrt p)) + Real.exp (-(1 / 2 * Real.sqrt q))) +
              w ^ 2 := by
          have := mul_le_mul_of_nonneg_left hmul hA2
          have h2 : A * w * (Real.exp (-Real.sqrt p) + Real.exp (-Real.sqrt q)) ≤
              A * w * (Real.exp (-(1 / 2 * Real.sqrt p)) + Real.exp (-(1 / 2 * Real.sqrt q))) :=
            mul_le_mul_of_nonneg_left (by linarith) hAw
          linarith
      _ = (A ^ 2 * Er + A * w) * (Real.exp (-(1 / 2 * Real.sqrt p)) +
            Real.exp (-(1 / 2 * Real.sqrt q))) + w ^ 2 := by ring
  have hsumx : ∑ x : Zd d L, (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
        (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
      (A ^ 2 * Er + A * w) * (S + S) + (L : ℝ) ^ d * w ^ 2 := by
    calc _ ≤ ∑ x : Zd d L, ((A ^ 2 * Er + A * w) *
          (Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
            Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) + w ^ 2) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = (A ^ 2 * Er + A * w) * (∑ x : Zd d L,
            Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
            ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) +
            (L : ℝ) ^ d * w ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
          simp
      _ ≤ (A ^ 2 * Er + A * w) * (S + S) + (L : ℝ) ^ d * w ^ 2 := by
          gcongr
  have hS0 : 0 ≤ S := by positivity
  have hLw : (L : ℝ) ^ d * w ^ 2 ≤ A * w := by
    have : (L : ℝ) ^ d * w ^ 2 = (w * (L : ℝ) ^ d) * w := by ring
    rw [this]
    nlinarith
  have hA2E : 0 ≤ A ^ 2 * Er := by positivity
  calc _ ≤ (A ^ 2 * Er + A * w) * (S + S) + (L : ℝ) ^ d * w ^ 2 := hsumx
    _ ≤ (A ^ 2 * Er + A * w) * (S + S) + A * w := by linarith
    _ ≤ (2 * S + 1) * A * (A * Er + w) := by nlinarith [mul_nonneg hA hw]

end Conv

/-! ## 3. The scale `M_u = W^d (1-u)` and the tail `T_{u,D}`: (e1)-(e4) -/

section Tails

/-- (e1): `W^d (M_u⁻¹)² = (1-u)⁻¹ M_u⁻¹` with `M_u = W^d |1-u|` (the prefactor of `res_deccalE_lk` is
`W^d` times the amplitude `M_u⁻²` of `T_{u,D}`; RBM2D: `W² ℓ_u² = M_u / η_u`). -/
theorem LemDecCalE_e1 (d : ℕ) {W u : ℝ} (hW : 0 < W) (hu : u < 1) :
    W ^ d * ((W ^ d * |1 - u|)⁻¹) ^ 2 = (1 - u)⁻¹ * (W ^ d * |1 - u|)⁻¹ := by
  have hx : 0 < 1 - u := by linarith
  have hWd : 0 < W ^ d := by positivity
  rw [abs_of_pos hx]
  field_simp

/-- (e1), real powers: `W^d M_u^{-a} = (1-u)⁻¹ M_u^{1-a}` for `M_u = W^d (1-u)`. -/
theorem LemDecCalE_e1_rpow (d : ℕ) {W u : ℝ} (hW : 0 < W) (hu : u < 1) (a : ℝ) :
    W ^ d * (W ^ d * (1 - u)) ^ (-a) = (1 - u)⁻¹ * (W ^ d * (1 - u)) ^ (1 - a) := by
  have hx : 0 < 1 - u := by linarith
  have hWd : 0 < W ^ d := by positivity
  have hM : 0 < W ^ d * (1 - u) := by positivity
  have h1 : (W ^ d * (1 - u)) ^ (1 - a) = (W ^ d * (1 - u)) * (W ^ d * (1 - u)) ^ (-a) := by
    rw [show (1 - a) = 1 + (-a) by ring, Real.rpow_add hM, Real.rpow_one]
  rw [h1]
  field_simp

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
private theorem lemDecCalE_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

/-- (e4) (a): `T_{u,D}` is non-increasing in its argument. -/
theorem LemDecCalE_tailT_anti {d : ℕ} {W u D x y : ℝ} (hxy : x ≤ y) :
    tailTD d W u D y ≤ tailTD d W u D x := by
  unfold tailTD
  have h1 : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have h2 : Real.exp (-Real.sqrt y) ≤ Real.exp (-Real.sqrt x) :=
    Real.exp_le_exp.2 (by linarith)
  have hA : 0 ≤ ((W ^ d * |1 - u|)⁻¹) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left h2 hA
  linarith

/-- (e4) (b): `T_{u,D}(x - c) ≤ exp(√c) T_{u,D}(x)` for `c ≥ 0`, `W ≥ 0` and every real `x`
(`√x ≤ √(x - c) + √c`).  With `c = 1` the factor is `e`. -/
theorem LemDecCalE_tailT_shift {d : ℕ} {W u D c : ℝ} (hW : 0 ≤ W) (hc : 0 ≤ c) (x : ℝ) :
    tailTD d W u D (x - c) ≤ Real.exp (Real.sqrt c) * tailTD d W u D x := by
  have hW0 : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW _
  have hkey : Real.sqrt x ≤ Real.sqrt (x - c) + Real.sqrt c := by
    have h := lemDecCalE_sqrt_add_le (x := max (x - c) 0) (y := c) (le_max_right _ _) hc
    have h1 : Real.sqrt x ≤ Real.sqrt (max (x - c) 0 + c) := by
      apply Real.sqrt_le_sqrt
      linarith [le_max_left (x - c) 0]
    have h2 : Real.sqrt (max (x - c) 0) = Real.sqrt (x - c) := by
      rcases le_total (x - c) 0 with h | h
      · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]
      · rw [max_eq_left h]
    linarith
  have hexp : Real.exp (-Real.sqrt (x - c)) ≤ Real.exp (Real.sqrt c) * Real.exp (-Real.sqrt x) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have h1 : 1 ≤ Real.exp (Real.sqrt c) := Real.one_le_exp (Real.sqrt_nonneg _)
  have hA : 0 ≤ ((W ^ d * |1 - u|)⁻¹) ^ 2 := sq_nonneg _
  unfold tailTD
  have := mul_le_mul_of_nonneg_left hexp hA
  nlinarith

/-- (e4) (c): `T_{u,D}(x - C ℓ*) ≤ exp(√C (log W)^{3/4}) T_{u,D}(x)` for `ℓ* = (log W)^{3/2}`
(`ℓ_u = 1`), `C ≥ 0`, `W ≥ 1` (the `tellStar` of RBM2D). -/
theorem LemDecCalE_e4c {d : ℕ} {W u D C : ℝ} (hW : 1 ≤ W) (hC : 0 ≤ C) (x : ℝ) :
    tailTD d W u D (x - C * Real.log W ^ ((3 : ℝ) / 2)) ≤
      Real.exp (Real.sqrt C * Real.log W ^ ((3 : ℝ) / 4)) * tailTD d W u D x := by
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have hc : 0 ≤ C * Real.log W ^ ((3 : ℝ) / 2) := mul_nonneg hC (Real.rpow_nonneg hlog _)
  have h := LemDecCalE_tailT_shift (d := d) (W := W) (u := u) (D := D) (by linarith) hc x
  have hsq : Real.sqrt (C * Real.log W ^ ((3 : ℝ) / 2)) = Real.sqrt C * Real.log W ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hlog]
    norm_num
  rw [hsq] at h
  exact h

/-- (e3) (ii): `T_{u,D}(x) ≤ T_{v,D}(x)` for `0 < W`, `u ≤ v < 1` (`M_v ≤ M_u`). -/
theorem LemDecCalE_tailT_mono_scale {d : ℕ} {W u v D x : ℝ} (hW : 0 < W) (huv : u ≤ v)
    (hv : v < 1) : tailTD d W u D x ≤ tailTD d W v D x := by
  have hu : u < 1 := huv.trans_lt hv
  have hxv : 0 < 1 - v := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hWd : 0 < W ^ d := by positivity
  have h1 : (W ^ d * |1 - u|)⁻¹ ≤ (W ^ d * |1 - v|)⁻¹ := by
    rw [abs_of_pos hxu, abs_of_pos hxv]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hWd.le)
  have h2 : ((W ^ d * |1 - u|)⁻¹) ^ 2 ≤ ((W ^ d * |1 - v|)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by rw [abs_of_pos hxu]; positivity) h1 2
  unfold tailTD
  have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-Real.sqrt x)).le
  linarith

end Tails

/-! ## 4. Unpacking `E2Hyp` and the scale facts (e2), (e3) -/

section Scales

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

private theorem lemDecCalE_W_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

/-- (e2): under `E2Hyp`, `1 ≤ M_u ≤ W^d` for `M_u = W^d (1-u)`. -/
theorem LemDecCalE_e2 (h : E2Hyp sz n E u D Λ K₀ J M) :
    1 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ∧
      ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, -⟩ := h
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (lemDecCalE_W_pos sz n) d
  refine ⟨?_, ?_⟩
  · calc (1 : ℝ) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hlamW
      _ ≤ (1 - u) * ((sz.W n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right hlamu hWd.le
      _ = ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by ring
  · nlinarith

/-- (e3) (i): under `E2Hyp`, `1 < W`, `2d < D` and `L^d ≤ W^{D - 2d}`. -/
theorem LemDecCalE_floor (h : E2Hyp sz n E u D Λ K₀ J M) :
    (1 : ℝ) < ((sz.W n : ℕ) : ℝ) ∧ 2 * (d : ℝ) < D ∧
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ (D - 2 * (d : ℝ)) := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, -⟩ := h
  have hW0 := lemDecCalE_W_pos sz n
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_lt.1 hcon)
    linarith
  have hL3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
  have hLd : (1 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    calc (1 : ℝ) < 3 := by norm_num
      _ ≤ ((sz.L n : ℕ) : ℝ) := hL3
      _ = ((sz.L n : ℕ) : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
  have hW2d : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (2 * d) := pow_pos hW0 _
  have hD : 2 * (d : ℝ) < D := by
    have h1 : ((sz.W n : ℕ) : ℝ) ^ ((2 * d : ℕ) : ℝ) < ((sz.W n : ℕ) : ℝ) ^ D := by
      rw [Real.rpow_natCast]
      calc ((sz.W n : ℕ) : ℝ) ^ (2 * d) = 1 * ((sz.W n : ℕ) : ℝ) ^ (2 * d) := (one_mul _).symm
        _ < ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) :=
            mul_lt_mul_of_pos_right hLd hW2d
        _ ≤ _ := hfloor
    have := (Real.rpow_lt_rpow_left_iff hW1).1 h1
    push_cast at this
    exact this
  refine ⟨hW1, hD, ?_⟩
  have hsub : ((sz.W n : ℕ) : ℝ) ^ (D - 2 * (d : ℝ)) =
      ((sz.W n : ℕ) : ℝ) ^ D / ((sz.W n : ℕ) : ℝ) ^ (2 * d) := by
    rw [Real.rpow_sub hW0, show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hsub, le_div_iff₀ hW2d]
  exact hfloor

/-- The floor condition in the form used by the tail sums: `W^{-D} L^d ≤ (M_u⁻¹)²`
(`W^{-D} ≤ L^{-d} W^{-2d} ≤ W^{-2d} ≤ M_u⁻²` as `M_u ≤ W^d`). -/
theorem LemDecCalE_floor_A (h : E2Hyp sz n E u D Λ K₀ J M) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ d ≤
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
  have h2 := LemDecCalE_e2 h
  obtain ⟨hW1, -⟩ := LemDecCalE_floor h
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, -⟩ := h
  have hW0 := lemDecCalE_W_pos sz n
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
    positivity
  have hW2d : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (2 * d) := pow_pos hW0 _
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ D := Real.rpow_pos_of_pos hW0 _
  have hMu : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2.1]
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
      (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ := by
    rw [Real.rpow_neg hW0.le]
    exact inv_anti₀ (by positivity) hfloor
  have h3 : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ * ((sz.L n : ℕ) : ℝ) ^ d =
      (((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ := by
    field_simp
  have h4 : (((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
    rw [pow_mul', ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hMu h2.2) 2
  calc ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ d
      ≤ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ * ((sz.L n : ℕ) : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right h1 hL0.le
    _ = (((sz.W n : ℕ) : ℝ) ^ (2 * d))⁻¹ := h3
    _ ≤ _ := h4

/-- (e3) (iii): under `E2Hyp`, `T_{u,D}(x) ≤ 2 (M_u⁻¹)²` for every real `x`
(`W^{-D} ≤ M_u⁻²` by the floor). -/
theorem LemDecCalE_tailT_le_two_inv_sq (h : E2Hyp sz n E u D Λ K₀ J M) (x : ℝ) :
    tailTD d ((sz.W n : ℕ) : ℝ) u D x ≤ 2 * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
  have hfl := LemDecCalE_floor_A h
  have hu1 : u < 1 := h.2.2.2.1
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
    exact one_le_pow₀ this
  have hW0 := lemDecCalE_W_pos sz n
  have hwn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hWD : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 :=
    (le_mul_of_one_le_right hwn hL1).trans hfl
  have hx : 0 < 1 - u := by linarith
  unfold tailTD
  rw [abs_of_pos hx]
  have hexp : Real.exp (-Real.sqrt x) ≤ 1 := by
    rw [Real.exp_le_one_iff]; simp
  have hA : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_left hexp hA
  linarith

end Scales

/-! ## 5. `lemDecCalE_lk` -/

section LK

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The loss absorbs the constant of `lemDecCalE_lk`: `e (2 S_d + 1) ≤ lossE2` under `E2Hyp`,
`S_d = (1 + 1536 d⁴)^d` (`e ≤ 3`, `2 S_d + 1 ≤ 3 S_d`, `1 + 1536 d⁴ ≤ 1600 d⁴`, `(1 + log W)³ ≥ 125`,
`K₀, Λ ≥ 1`). -/
theorem LemDecCalE_lk_const_le_lossE2 (h : E2Hyp sz n E u D Λ K₀ J M) :
    Real.exp 1 * (2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1) ≤
      lossE2 d (sz.L n) (sz.W n) Λ K₀ := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, -⟩ := h
  have hW0 := lemDecCalE_W_pos sz n
  have hL0 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_le.1 hcon).le
    linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hbase : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL0) (one_le_pow₀ hW1)
  have hA : (1 : ℝ) ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 :=
    one_le_pow₀ (by linarith [Real.log_nonneg hbase])
  have hB : (125 : ℝ) ≤ (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 := by
    have : (5 : ℝ) ≤ 1 + Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have hX : (1 : ℝ) ≤ Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    Real.one_le_exp (by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ)) ((3 : ℝ) / 4)
      linarith)
  have hP : (1 : ℝ) ≤ K₀ ^ 2 * Λ ^ 6 *
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
        Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) (one_le_pow₀ hΛ)) hA) hX
  -- the convolution constant
  set X : ℝ := (1 + 1536 * (d : ℝ) ^ 4) ^ d with hXdef
  set Y : ℝ := (1600 * (d : ℝ) ^ 4) ^ d with hYdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ d) 4])
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hXY : X ≤ Y := pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hconst : Real.exp 1 * (2 * X + 1) ≤ 9 * Y := by
    have h1 : 2 * X + 1 ≤ 3 * X := by linarith
    have h0 : 0 ≤ 2 * X + 1 := by linarith
    calc Real.exp 1 * (2 * X + 1) ≤ 3 * (3 * X) :=
          mul_le_mul he h1 h0 (by norm_num)
      _ ≤ 9 * Y := by linarith
  have hY0 : 0 ≤ Y := by positivity
  unfold lossE2
  have hrw : (10 : ℝ) ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * K₀ ^ 2 * Λ ^ 6 *
      (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
        (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 *
          Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) =
      (10 ^ 12 * Y) * (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 *
        (K₀ ^ 2 * Λ ^ 6 *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
            Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) := by
    rw [hYdef]; ring
  rw [hrw]
  have h1 : (10 : ℝ) ^ 12 * Y * 125 ≤ 10 ^ 12 * Y * (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h2 : (10 : ℝ) ^ 12 * Y * 125 * 1 ≤ 10 ^ 12 * Y * (1 + Real.log ((sz.W n : ℕ) : ℝ)) ^ 3 *
      (K₀ ^ 2 * Λ ^ 6 *
        (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
          Real.exp (8 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) :=
    mul_le_mul h1 hP (by norm_num) (by positivity)
  nlinarith

/-- `S^{(B)}_{xy} ≠ 0` forces `|x - y|_∞ ≤ 1` (`S^{(B)}` is supported on `x = y` and the
`ℓ¹`-neighbours, `sbKernel`; `|·|_∞ ≤ |·|_{ℓ¹}`). -/
private theorem lemDecCalE_SB_support (d L : ℕ) [NeZero L] (g : ℝ) {x y : Zd d L}
    (h : SB d L g x y ≠ 0) : zdistInf d L (x - y) ≤ 1 := by
  rw [SB_apply] at h
  unfold sbKernel at h
  by_cases h0 : x - y = 0
  · rw [h0, lemDecCalE_zdistInf_zero]; exact zero_le_one
  · by_cases h1 : zdistD d L (x - y) = 1
    · exact (zdistInf_le_zdistD d L _).trans h1.le
    · simp [h0, h1] at h

/-- **`lemDecCalE_lk`** (`res_deccalE_lk`, `3_5:2318`): the deterministic `𝓔^{LK×LK}` bound.
Route (RBM2D `LemDecCalE:375`, T2049 (b.3)): `|𝓔^{LK×LK}_{σ,a}| ≤ W^d Σ_{x,y} |LK_{(x,a₂)}|
|S^{(B)}_{xy}| |LK_{(a₁,y)}|`; `S^{(B)}` is supported on `|x - y|_∞ ≤ 1` with `Σ_y |S^{(B)}_{xy}| = 1`,
so the shift (e4) with `c = 1` gives the factor `e`; `LemDecCalE_sum_tail_tail` gives
`(2 S_d + 1) M_u⁻² T_{u,D}(|a₁ - a₂|)`; (e1) turns `W^d M_u⁻²` into `(1-u)⁻¹ M_u⁻¹`, and
`e (2 S_d + 1) ≤ lossE2`. -/
theorem lemDecCalE_lk (d : ℕ) : LemDecCalE_lk d := by
  intro sz n E u D Λ K₀ J M h σ a
  have hconst := LemDecCalE_lk_const_le_lossE2 h
  have hfl := LemDecCalE_floor_A h
  have h2 := LemDecCalE_e2 h
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    hJW, hLK, hK14, hK15⟩ := h
  have hW0 := lemDecCalE_W_pos sz n
  have hL3 := sz.three_le_L n
  have hx : 0 < 1 - u := by linarith
  have hJ0 : 0 ≤ J := by linarith
  -- the tail as `A e^{-√r} + w`
  have hTD : ∀ r : ℝ, tailTD d ((sz.W n : ℕ) : ℝ) u D r =
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-Real.sqrt r) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    intro r; unfold tailTD; rw [abs_of_pos hx]
  have hTT : ∀ b : Fin 2 → Zd d (sz.L n), STtailTD sz n u D b =
      tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) := fun b => rfl
  have hTnn : ∀ r : ℝ, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D r := fun r =>
    tailTD_nonneg hW0.le
  -- S1: the norm of `STELKLKM`
  have hS1 : ‖STELKLKM sz n E u M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ‖STLKM sz n E u M σ ![x, a 1]‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
          ‖STLKM sz n E u M σ ![a 0, y]‖ := by
    unfold STELKLKM
    rw [norm_mul]
    have hw : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
    rw [hw]
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul, norm_mul]
  -- S2: pointwise bound with the shift
  have hpt : ∀ x y : Zd d (sz.L n),
      ‖STLKM sz n E u M σ ![x, a 1]‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
          ‖STLKM sz n E u M σ ![a 0, y]‖ ≤
        (J ^ 2 * Real.exp 1) *
          (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)) *
          ‖SB d (sz.L n) (sz.lam n) x y‖ := by
    intro x y
    by_cases hS : SB d (sz.L n) (sz.lam n) x y = 0
    · simp [hS]
    have hxy := lemDecCalE_SB_support d (sz.L n) (sz.lam n) hS
    have hxy' : (zdistInf d (sz.L n) (y - x) : ℝ) ≤ 1 := by
      rw [lemDecCalE_zdistInf_sub_comm]; exact_mod_cast hxy
    have htri : (zdistInf d (sz.L n) (a 0 - x) : ℝ) ≤
        (zdistInf d (sz.L n) (a 0 - y) : ℝ) + (zdistInf d (sz.L n) (y - x) : ℝ) :=
      lemDecCalE_zdistInf_tri_real d (sz.L n) (a 0) y x
    have hshift : tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - y) : ℝ) ≤
        Real.exp 1 * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ) := by
      have h1 := LemDecCalE_tailT_anti (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D)
        (x := (zdistInf d (sz.L n) (a 0 - x) : ℝ) - 1) (y := (zdistInf d (sz.L n) (a 0 - y) : ℝ))
        (by linarith)
      have h2 := LemDecCalE_tailT_shift (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D)
        (c := 1) hW0.le zero_le_one (zdistInf d (sz.L n) (a 0 - x) : ℝ)
      rw [Real.sqrt_one] at h2
      exact h1.trans h2
    have hl1 := hLK σ ![x, a 1]
    have hl2 := hLK σ ![a 0, y]
    rw [hTT] at hl1 hl2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hl1 hl2
    have hT1 := hTnn (zdistInf d (sz.L n) (x - a 1) : ℝ)
    have hT2 := hTnn (zdistInf d (sz.L n) (a 0 - y) : ℝ)
    have hSn : 0 ≤ ‖SB d (sz.L n) (sz.lam n) x y‖ := norm_nonneg _
    calc ‖STLKM sz n E u M σ ![x, a 1]‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
          ‖STLKM sz n E u M σ ![a 0, y]‖
        ≤ (J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
            ‖SB d (sz.L n) (sz.lam n) x y‖ *
            (J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - y) : ℝ)) := by
          gcongr
      _ ≤ (J * tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ)) *
            ‖SB d (sz.L n) (sz.lam n) x y‖ *
            (J * (Real.exp 1 * tailTD d ((sz.W n : ℕ) : ℝ) u D
              (zdistInf d (sz.L n) (a 0 - x) : ℝ))) := by
          gcongr
      _ = (J ^ 2 * Real.exp 1) *
          (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)) *
          ‖SB d (sz.L n) (sz.lam n) x y‖ := by ring
  -- S3: sum over `y` (row sums of `|S^{(B)}|` are `1`), then over `x`
  have hS2 : ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖STLKM sz n E u M σ ![x, a 1]‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
          ‖STLKM sz n E u M σ ![a 0, y]‖ ≤
      (J ^ 2 * Real.exp 1) * ∑ x : Zd d (sz.L n),
        tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ) := by
    calc _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), (J ^ 2 * Real.exp 1) *
            (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ) *
              tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)) *
            ‖SB d (sz.L n) (sz.lam n) x y‖ :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
      _ = ∑ x : Zd d (sz.L n), (J ^ 2 * Real.exp 1) *
            (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (x - a 1) : ℝ) *
              tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - x) : ℝ)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum, sum_norm_SB_row d (sz.L n) (sz.lam n) hL3 x, mul_one]
      _ = _ := by rw [Finset.mul_sum]
  -- S4: the convolution
  have hAnn : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := sq_nonneg _
  have hwnn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hconv := LemDecCalE_sum_tail_tail (d := d) (L := sz.L n) (by omega) hAnn hwnn hfl (a 0) (a 1)
  simp only [← hTD] at hconv
  -- S5: assemble
  have hcoef : ((sz.W n : ℕ) : ℝ) ^ d * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 =
      (1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by
    have := LemDecCalE_e1 d hW0 hu1
    rw [abs_of_pos hx] at this ⊢
    exact this
  set Tr : ℝ := tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) with hTr
  have hTr0 : 0 ≤ Tr := hTnn _
  set Aq : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 with hAq
  set S : ℝ := 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 with hSdef
  have hmain : ‖STELKLKM sz n E u M σ a‖ ≤
      (Real.exp 1 * S) * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr) := by
    calc ‖STELKLKM sz n E u M σ a‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((J ^ 2 * Real.exp 1) * (S * Aq * Tr)) := by
          refine hS1.trans ?_
          gcongr
          refine hS2.trans ?_
          gcongr
      _ = (Real.exp 1 * S) * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr) := by ring
  have hpos : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr := by positivity
  have hfin : (Real.exp 1 * S) * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr) ≤
      lossE2 d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * Aq * J ^ 2 * Tr) :=
    mul_le_mul_of_nonneg_right hconst hpos
  refine hmain.trans (hfin.trans (le_of_eq ?_))
  rw [hTT a, ← hcoef]
  ring

end LK

/-! ## 6. (e5) the two-loop, and the Green function entries (e6)-(e9) -/

section Green

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- (e5), first part: `|(𝓛 - 𝒦)^{(2)}_{σ,a}| ≤ J T_{u,D}(|a₁ - a₂|)` is the premise of `E2Hyp`. -/
theorem LemDecCalE_lk_le (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) : ‖STLKM sz n E u M σ a‖ ≤ J * STtailTD sz n u D a := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    hJW, hLK, -⟩ := h
  exact hLK σ a

/-- `𝓛_{(+,-),(a,b)} = (𝓛 - 𝒦) + 𝒦` (`loopPM` is `STLM` at `(+,-)`). -/
theorem LemDecCalE_loopPM_eq (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a b : Zd d (sz.L n)) :
    loopPM d (sz.L n) (sz.W n) E u M a b =
      STLKM sz n E u M ![true, false] ![a, b] + STKloop sz n E u ![true, false] ![a, b] := by
  simp only [STLKM, STLM, loopPM]
  ring

/-- (e5), second part: under `E2Hyp`, `|𝓛_{(+,-),(a,b)}| ≤ K₀ M_u⁻¹ + 2 J (M_u⁻¹)²`
(`𝓛 = (𝓛 - 𝒦) + 𝒦`, the `𝒦` bound and (e3) (iii)). -/
theorem LemDecCalE_loopPM_le (h : E2Hyp sz n E u D Λ K₀ J M) (a b : Zd d (sz.L n)) :
    ‖loopPM d (sz.L n) (sz.W n) E u M a b‖ ≤
      K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ +
        2 * J * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
  have hT := LemDecCalE_tailT_le_two_inv_sq h ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    hJW, hLK, hK14, hK15⟩ := h
  have hJ0 : 0 ≤ J := by linarith
  have h1 := hLK ![true, false] ![a, b]
  have h2 := hK14 a b
  have h1' : ‖STLKM sz n E u M ![true, false] ![a, b]‖ ≤
      J * tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := h1
  rw [LemDecCalE_loopPM_eq]
  have h4 := norm_add_le (STLKM sz n E u M ![true, false] ![a, b])
    (STKloop sz n E u ![true, false] ![a, b])
  have h5 := mul_le_mul_of_nonneg_left hT hJ0
  linarith

/-- `G(-) = G(+)ᴴ` for Hermitian `H` (the text of the merged `ST_Gres_false`,
`Induction/Step2Iterate.lean:1198`, which is not in the import closure). -/
private theorem lemDecCalE_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- (e6), the resolvent entries minus `δ_{xy} m(σ)`: under `E2Hyp`, both signs `σ` and all fine
entries, `|G_{xy}(σ) - δ_{xy} m(σ)| ≤ Λ M_u^{-1/4}` (the premise at `σ = +`; for `σ = -` the adjoint
`G(-) = G(+)ᴴ`, `M` Hermitian). -/
theorem LemDecCalE_e6_err (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Bool)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖Gres M (zt E u) σ x y - (if x = y then mSigma E σ else 0)‖ ≤
      Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ ((1 : ℝ) / 4) := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, -⟩ := h
  cases σ
  · have hG := lemDecCalE_Gres_false hH (zt E u)
    have hent : Gres M (zt E u) false x y = star (Gres M (zt E u) true y x) := by
      have := congrFun (congrFun hG x) y
      simpa [Matrix.conjTranspose_apply] using this
    have hs : Gres M (zt E u) false x y - (if x = y then mSigma E false else 0) =
        star (Gres M (zt E u) true y x - (if y = x then mE E else 0)) := by
      rw [hent, star_sub]
      congr 1
      by_cases hxy : x = y
      · subst hxy
        simp [mSigma]
      · have : ¬ y = x := fun h => hxy h.symm
        simp [hxy, this]
    rw [hs, norm_star]
    exact h6 y x
  · simpa [mSigma] using h6 x y

/-- (e6): under `E2Hyp`, every entry satisfies `|G_{xy}(σ)| ≤ |m| + Λ M_u^{-1/4} ≤ 2Λ`
(`|m| = 1`, `norm_mSigma`, `M_u ≥ 1`). -/
theorem LemDecCalE_e6 (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖Gres M (zt E u) σ x y‖ ≤ 2 * Λ := by
  have herr := LemDecCalE_e6_err h σ x y
  have h2 := LemDecCalE_e2 h
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, -⟩ := h
  have hinv : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ ((1 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one (by positivity) (inv_le_one_of_one_le₀ h2.1) (by norm_num)
  have hm : ‖mSigma E σ‖ = 1 := norm_mSigma hE.le σ
  have hdiag : ‖(if x = y then mSigma E σ else 0 : ℂ)‖ ≤ 1 := by
    split_ifs
    · exact hm.le
    · simp
  have h1 := norm_le_norm_sub_add (Gres M (zt E u) σ x y) (if x = y then mSigma E σ else 0)
  have hΛ0 : 0 ≤ Λ := by linarith
  have : Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ ((1 : ℝ) / 4) ≤ Λ * 1 :=
    mul_le_mul_of_nonneg_left hinv hΛ0
  linarith

/-- `|q - p|_∞ ≤ |a' - q|_∞ + |a' - b'|_∞ + |b' - p|_∞`. -/
private theorem lemDecCalE_zdistInf_tri3 (d L : ℕ) [NeZero L] (q p a' b' : Zd d L) :
    zdistInf d L (q - p) ≤
      zdistInf d L (a' - q) + zdistInf d L (a' - b') + zdistInf d L (b' - p) := by
  have e : q - p = ((q - a') + (a' - b')) + (b' - p) := by abel
  have h1 := lemDecCalE_zdistInf_add_le d L (q - a' + (a' - b')) (b' - p)
  have h2 := lemDecCalE_zdistInf_add_le d L (q - a') (a' - b')
  have h3 : zdistInf d L (q - a') = zdistInf d L (a' - q) := lemDecCalE_zdistInf_sub_comm d L q a'
  rw [e]
  omega

/-- The right side of (`GijGEX`) at `(a, b)` is at most `9^d B + [|a - b|_∞ ≤ 1] W^{-d}` if
`|𝓛_{(+,-),(a',b')}| ≤ B` for the pairs with `|a' - a|_∞ ≤ 1`, `|b' - b|_∞ ≤ 1` (the cube
`|·|_∞ ≤ 1` has at most `3^d` points, so `3^d · 3^d = 9^d` pairs; RBM2D: `5 · 5 = 25`). -/
private theorem lemDecCalE_gexRHS_le_near {L W : ℕ} [NeZero L] [NeZero W] (E u B : ℝ) (hB : 0 ≤ B)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L)
    (hM : ∀ a' b' : Zd d L, zdistInf d L (a' - a) ≤ 1 → zdistInf d L (b' - b) ≤ 1 →
      ‖loopPM d L W E u M a' b'‖ ≤ B) :
    gexRHS d L W E u M a b ≤
      9 ^ d * B + (if zdistInf d L (a - b) ≤ 1 then ((W : ℝ) ^ d)⁻¹ else 0) := by
  unfold gexRHS
  have h1 : (∑ a' : Zd d L, ∑ b' : Zd d L,
      if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then ‖loopPM d L W E u M a' b'‖
      else 0) ≤ 9 ^ d * B := by
    calc (∑ a' : Zd d L, ∑ b' : Zd d L,
        if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then ‖loopPM d L W E u M a' b'‖
        else 0)
        ≤ ∑ a' : Zd d L, ∑ b' : Zd d L, (if zdistInf d L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((if zdistInf d L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
          by_cases h1 : zdistInf d L (a' - a) ≤ 1 <;> by_cases h2 : zdistInf d L (b' - b) ≤ 1
          · simpa [h1, h2] using hM a' b' h1 h2
          · simp [h1, h2]
          · simp [h1, h2]
          · simp [h1, h2]
      _ = (∑ a' : Zd d L, if zdistInf d L (a' - a) ≤ 1 then (1 : ℝ) else 0) *
            ((∑ b' : Zd d L, if zdistInf d L (b' - b) ≤ 1 then (1 : ℝ) else 0) * B) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ 3 ^ d * (3 ^ d * B) := by
          have e1 : (∑ a' : Zd d L, if zdistInf d L (a' - a) ≤ 1 then (1 : ℝ) else 0) ≤ 3 ^ d := by
            rw [Finset.sum_boole]; exact LemDecCalE_e10b a
          have e2 : (∑ b' : Zd d L, if zdistInf d L (b' - b) ≤ 1 then (1 : ℝ) else 0) ≤ 3 ^ d := by
            rw [Finset.sum_boole]; exact LemDecCalE_e10b b
          have e0 : 0 ≤ (∑ b' : Zd d L, if zdistInf d L (b' - b) ≤ 1 then (1 : ℝ) else 0) :=
            Finset.sum_nonneg fun b' _ => by split_ifs <;> norm_num
          exact mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 hB) (mul_nonneg e0 hB) (by positivity)
      _ = 9 ^ d * B := by
          rw [← mul_assoc, ← mul_pow]; norm_num
  linarith

/-- (e7) [`9^d` neighbour pairs, not `25`]: under `E2Hyp`, for fine indices `p, q` whose blocks satisfy
`|[q] - [p]|_∞ ≥ ℓ*_u/8 + 2`,
`|G_{pq}|² ≤ 9^d Λ (W^{-D} + J T_{u,D}(|[q] - [p]|_∞ - 2))`.
From the swapped (`GijGEX`) premise (`gexRHS … [q] [p]`): `gexRHS` is a sum over the `3^d · 3^d`
pairs `(a', b')` with `|a' - [q]|_∞ ≤ 1`, `|b' - [p]|_∞ ≤ 1` (and no `W^{-d}` term as
`|[q] - [p]|_∞ > 1`); each has `|a' - b'|_∞ ≥ |[q] - [p]|_∞ - 2 ≥ ℓ*_u/8`, hence `‖𝒦(a',b')‖ ≤ W^{-D}`
(`Kell*`) and `‖𝓛 - 𝒦‖ ≤ J T_{u,D}(|[q] - [p]|_∞ - 2)`. -/
theorem LemDecCalE_e7 (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Idx d (sz.L n) (sz.W n))
    (hd : (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) + 2 ≤
      (zdistInf d (sz.L n) (STblk sz n q - STblk sz n p) : ℝ)) :
    ‖Gres M (zt E u) true p q‖ ^ 2 ≤
      9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) + J *
        tailTD d ((sz.W n : ℕ) : ℝ) u D
          ((zdistInf d (sz.L n) (STblk sz n q - STblk sz n p) : ℝ) - 2)) := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    hJW, hLK, hK14, hK15⟩ := h
  have hW0 := lemDecCalE_W_pos sz n
  have hlogW : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hstar : 0 ≤ (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
      ellT (sz.L n) (sz.lam n) u) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hlogW _) ellT_nonneg)
  set r : ℝ := (zdistInf d (sz.L n) (STblk sz n q - STblk sz n p) : ℝ) with hrdef
  have hr2 : 2 ≤ r := by linarith
  have hpq : p ≠ q := by
    intro hpq
    subst hpq
    simp only [sub_self, lemDecCalE_zdistInf_zero, Nat.cast_zero] at hrdef
    linarith
  have hgex := h78 p q hpq
  set Jv := J with hJv
  have hJ0 : 0 ≤ J := by linarith
  have hB0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) + J * tailTD d ((sz.W n : ℕ) : ℝ) u D (r - 2) :=
    add_nonneg (Real.rpow_nonneg hW0.le _) (mul_nonneg hJ0 (tailTD_nonneg hW0.le))
  have hloc : ∀ a' b' : Zd d (sz.L n), zdistInf d (sz.L n) (a' - STblk sz n q) ≤ 1 →
      zdistInf d (sz.L n) (b' - STblk sz n p) ≤ 1 →
      ‖loopPM d (sz.L n) (sz.W n) E u M a' b'‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D) + J * tailTD d ((sz.W n : ℕ) : ℝ) u D (r - 2) := by
    intro a' b' h1 h2
    have htri := lemDecCalE_zdistInf_tri3 d (sz.L n) (STblk sz n q) (STblk sz n p) a' b'
    have h1' : (zdistInf d (sz.L n) (a' - STblk sz n q) : ℝ) ≤ 1 := by exact_mod_cast h1
    have h2' : (zdistInf d (sz.L n) (b' - STblk sz n p) : ℝ) ≤ 1 := by exact_mod_cast h2
    have htri' : r ≤ (zdistInf d (sz.L n) (a' - STblk sz n q) : ℝ) +
        (zdistInf d (sz.L n) (a' - b') : ℝ) + (zdistInf d (sz.L n) (b' - STblk sz n p) : ℝ) := by
      rw [hrdef]; exact_mod_cast htri
    have hfar : r - 2 ≤ (zdistInf d (sz.L n) (a' - b') : ℝ) := by linarith
    have hfar' : (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
        ellT (sz.L n) (sz.lam n) u) ≤ (zdistInf d (sz.L n) (a' - b') : ℝ) := by linarith
    have hKp := hK15 a' b' hfar'
    have hlk : ‖STLKM sz n E u M ![true, false] ![a', b']‖ ≤
        J * tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a' - b') : ℕ) : ℝ) :=
      hLK ![true, false] ![a', b']
    have hT := LemDecCalE_tailT_anti (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) hfar
    have hn := norm_add_le (STLKM sz n E u M ![true, false] ![a', b'])
      (STKloop sz n E u ![true, false] ![a', b'])
    have hJT := mul_le_mul_of_nonneg_left hT hJ0
    rw [LemDecCalE_loopPM_eq]
    linarith
  have hgex' := lemDecCalE_gexRHS_le_near (W := sz.W n) E u _ hB0 M (STblk sz n q) (STblk sz n p) hloc
  have hnear : ¬ zdistInf d (sz.L n) (STblk sz n q - STblk sz n p) ≤ 1 := by
    intro hle
    have : r ≤ 1 := by rw [hrdef]; exact_mod_cast hle
    linarith
  simp only [hnear, ite_false, add_zero] at hgex'
  have hΛ0 : 0 ≤ Λ := by linarith
  calc ‖Gres M (zt E u) true p q‖ ^ 2 ≤ Λ * gexRHS d (sz.L n) (sz.W n) E u M (STblk sz n q) (STblk sz n p) :=
        hgex
    _ ≤ Λ * (9 ^ d * (((sz.W n : ℕ) : ℝ) ^ (-D) + J * tailTD d ((sz.W n : ℕ) : ℝ) u D (r - 2))) :=
        mul_le_mul_of_nonneg_left hgex' hΛ0
    _ = 9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) + J * tailTD d ((sz.W n : ℕ) : ℝ) u D (r - 2)) := by
        ring

/-- (e8) [`9^d` neighbour pairs; constant recomputed]: under `E2Hyp`, for fine indices `p ≠ q`,
`|G_{pq}|² ≤ Λ (9^d (K₀ M_u⁻¹ + 2 J M_u⁻²) + W^{-d})`, and this is `≤ 2 · 9^d Λ K₀ M_u⁻¹ (1 + J/M_u)`
(`W^{-d} ≤ M_u⁻¹` as `M_u ≤ W^d`, `K₀ ≥ 1`; RBM2D: `25`, `50`). -/
theorem LemDecCalE_e8 (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Idx d (sz.L n) (sz.W n))
    (hpq : p ≠ q) :
    ‖Gres M (zt E u) true p q‖ ^ 2 ≤
        Λ * (9 ^ d * (K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ +
          2 * J * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ∧
      ‖Gres M (zt E u) true p q‖ ^ 2 ≤
        2 * 9 ^ d * Λ * K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ *
          (1 + J / (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))) := by
  have hloop := LemDecCalE_loopPM_le h
  have h2 := LemDecCalE_e2 h
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    hJW, hLK, hK14, hK15⟩ := h
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2.1]
  have hJ0 : 0 ≤ J := by linarith
  have hgex := h78 p q hpq
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hm0 : 0 < m := inv_pos.2 hMpos
  have hB0 : 0 ≤ K₀ * m + 2 * J * m ^ 2 := by positivity
  have hgex' := lemDecCalE_gexRHS_le_near (W := sz.W n) E u _ hB0 M (STblk sz n q) (STblk sz n p)
    (fun a' b' _ _ => hloop a' b')
  have hif : (if zdistInf d (sz.L n) (STblk sz n q - STblk sz n p) ≤ 1 then
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    split_ifs
    · exact le_rfl
    · positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hfirst : ‖Gres M (zt E u) true p q‖ ^ 2 ≤
      Λ * (9 ^ d * (K₀ * m + 2 * J * m ^ 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) :=
    hgex.trans (mul_le_mul_of_nonneg_left (hgex'.trans (by linarith)) hΛ0)
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hWm : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ m := inv_anti₀ hMpos h2.2
  have hJM : J / (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)) = J * m := by rw [hm, div_eq_mul_inv]
  rw [hJM]
  have h9d : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
  have h1 : 9 ^ d * (K₀ * m + 2 * J * m ^ 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
      2 * 9 ^ d * K₀ * m * (1 + J * m) := by
    set c : ℝ := 9 ^ d with hc
    have e1 : 0 ≤ (K₀ - 1) * m := mul_nonneg (by linarith) hm0.le
    have e2 : 0 ≤ (K₀ - 1) * (J * m ^ 2) := mul_nonneg (by linarith) (by positivity)
    have e3 : 0 ≤ K₀ * m := by positivity
    have e4 : 0 ≤ (c - 1) * (K₀ * m) := mul_nonneg (by linarith) e3
    have e5 : 0 ≤ (c - 1) * (J * m ^ 2 * K₀) := mul_nonneg (by linarith) (by positivity)
    have e6 : 0 ≤ (c - 1) * m := mul_nonneg (by linarith) hm0.le
    nlinarith
  calc Λ * (9 ^ d * (K₀ * m + 2 * J * m ^ 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
      ≤ Λ * (2 * 9 ^ d * K₀ * m * (1 + J * m)) := mul_le_mul_of_nonneg_left h1 hΛ0
    _ = 2 * 9 ^ d * Λ * K₀ * m * (1 + J * m) := by ring

/-- (e9): under `E2Hyp`, both signs `σ` and every block `a`, `|⟨G̃_u(σ) E_a⟩| ≤ Λ M_u⁻¹`
(the premise (P-e9); `(ℓ_u/ℓ_s)² = 1` in regime (iii)). -/
theorem LemDecCalE_e9 (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Bool) (a : Zd d (sz.L n)) :
    ‖avgErr d (sz.L n) (sz.W n) E u M σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, -⟩ := h
  exact h9 σ a

end Green

/-! ## 7. The nondegenerate instance: `E2Hyp` at `M = 0`, `u = 0` -/

section Witness

variable {d : ℕ}

/-- `G_0(+) = m I` at `H = 0`, `u = 0` (`z_0 = E + m`, `m (m + E) = -1`), for any finite index
(the text of the `private` `gres_zero_true` of `Green/Pins.lean`). -/
private theorem lemDecCalE_gres_zero_true {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
    (hE : |E| ≤ 2) : Gres (0 : Matrix ι ι ℂ) (zt E 0) true = mE E • (1 : Matrix ι ι ℂ) := by
  have hm := mE_mul hE
  have hzt : zt E 0 = (E : ℂ) + mE E := by simp [zt]
  have hmz : (-((E : ℂ) + mE E))⁻¹ = mE E := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 : ℂ) * hm
  have hne : (E : ℂ) + mE E ≠ 0 := by
    intro h0
    rw [add_comm, h0, mul_zero] at hm
    norm_num at hm
  rw [Gres]
  simp only [↓reduceIte]
  rw [hzt, zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hne), hmz]

/-- `G_0(σ) = m(σ) I` at `H = 0`, `u = 0`, both signs. -/
private theorem lemDecCalE_gres_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
    (hE : |E| ≤ 2) (σ : Bool) :
    Gres (0 : Matrix ι ι ℂ) (zt E 0) σ = mSigma E σ • (1 : Matrix ι ι ℂ) := by
  cases σ
  · rw [lemDecCalE_Gres_false Matrix.isHermitian_zero, lemDecCalE_gres_zero_true hE,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [mSigma]
  · simpa [mSigma] using lemDecCalE_gres_zero_true (ι := ι) hE

private theorem lemDecCalE_blockMat_zero {L W : ℕ} [NeZero L] [NeZero W] :
    blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ) = 0 := by
  ext i j; simp [blockMat]

private theorem lemDecCalE_sum_block_indicator {L W : ℕ} [NeZero L] (c : ℂ) (a : Zd d L) :
    ∑ p : Vtx d L W, (if p.1 = a then c else 0) = (W : ℂ) ^ d * c := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : Zd d L, ∑ y : Fin (W ^ d), (if (x, y).1 = a then c else 0) =
      if x = a then (W : ℂ) ^ d * c else 0 := by
    intro x
    by_cases hx : x = a
    · simp only [hx, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    · simp [hx]
  simp only [h]
  simp

/-- `tr(E_a E_b) = δ_{ab} W^{-d}`. -/
private theorem lemDecCalE_trace_Eblk_mul {L W : ℕ} [NeZero L] [NeZero W] (a b : Zd d L) :
    Matrix.trace (Eblk d L W a * Eblk d L W b) = if a = b then (((W : ℂ) ^ d)⁻¹) else 0 := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne W)
  have h : Eblk d L W a * Eblk d L W b = Matrix.diagonal (fun p : Vtx d L W =>
      (if p.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) * (if p.1 = b then ((W : ℂ) ^ d)⁻¹ else 0)) := by
    unfold Eblk
    exact Matrix.diagonal_mul_diagonal _ _
  rw [h, Matrix.trace_diagonal]
  by_cases hab : a = b
  · subst hab
    have h2 : ∀ p : Vtx d L W, (if p.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        (if p.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) =
        if p.1 = a then (((W : ℂ) ^ d)⁻¹) ^ 2 else 0 := by
      intro p; split_ifs <;> ring
    simp only [h2, lemDecCalE_sum_block_indicator, ite_true]
    field_simp
  · simp only [hab, ite_false]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases h1 : p.1 = a
    · have h3 : ¬ p.1 = b := fun h2 => hab (h1.symm.trans h2)
      simp only [h3, ite_false, mul_zero]
    · simp only [h1, ite_false, zero_mul]

/-- `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁,a₂)` for the model's `STKloop` (`KLK_two`). -/
private theorem lemDecCalE_STKloop_two (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
  have h2 : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold STKloop
  rw [h2, KLK_two]

/-- At `u = 0`: `𝒦^{(2)}_{0,σ,a} = W^{-d} m₁ m₂ δ_{a₁a₂}` (`Θ_0 = 1`). -/
private theorem lemDecCalE_STKloop_zero_time (sz : Sizes d) (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E 0 σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        (if a 0 = a 1 then 1 else 0) := by
  rw [lemDecCalE_STKloop_two]
  simp only [Complex.ofReal_zero, zero_mul]
  have : Theta d (sz.L n) (sz.lam n) 0 = 1 := by simp [Theta]
  rw [this, Matrix.one_apply]

/-- At `M = 0`, `u = 0`: `𝓛^{(2)}_{0,σ,a} = W^{-d} m₁ m₂ δ_{a₁a₂}` (`G_0(σ) = m(σ) I`,
`tr(E_a E_b) = δ_{ab} W^{-d}`). -/
private theorem lemDecCalE_STLM_zero_time (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STLM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        (if a 0 = a 1 then 1 else 0) := by
  unfold STLM loopFine loopM
  rw [lemDecCalE_blockMat_zero]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    lemDecCalE_gres_zero hE, Fin.succ_zero_eq_one]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    lemDecCalE_trace_Eblk_mul]
  split_ifs <;> ring

/-- At `M = 0`, `u = 0`: `𝓛 - 𝒦 = 0`. -/
private theorem lemDecCalE_STLKM_zero_time (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STLKM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a = 0 := by
  unfold STLKM
  rw [lemDecCalE_STLM_zero_time sz n hE, lemDecCalE_STKloop_zero_time, sub_self]

/-- **`E2Hyp` at `M = 0`, `u = 0`** (the matrix of time `0`, where `G = m I`): every conjunct
holds once the numeric premises do.  Hence a nonempty instance wherever the numbers allow. -/
theorem LemDecCalE_e2Hyp_zero (sz : Sizes d) (n : ℕ) {E D Λ K₀ J : ℝ} (hd : 3 ≤ d)
    (hE : |E| < 2) (hlam : 0 < sz.lam n) (hlam1 : sz.lam n ^ 2 ≤ 1)
    (hlamW : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hΛ : 1 ≤ Λ) (hK : 1 ≤ K₀)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hfloor : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
    E2Hyp sz n E 0 D Λ K₀ J (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
  have hW0 := lemDecCalE_W_pos sz n
  have hMu : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - 0))⁻¹ := by positivity
  have hJ0 : 0 ≤ J := by linarith
  refine ⟨hd, hE, le_rfl, by norm_num, hlam, by simpa using hlam1, hlamW, hΛ, hK, hlog, hfloor,
    Matrix.isHermitian_zero, ?_, ?_, ?_, hJ, hJW, ?_, ?_, ?_⟩
  · intro x y
    rw [lemDecCalE_gres_zero_true hE.le]
    have h0 : ‖(mE E • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) x y -
        (if x = y then mE E else 0)‖ = 0 := by
      by_cases h : x = y
      · subst h; simp
      · simp [h, Matrix.one_apply_ne h]
    rw [h0]
    positivity
  · intro p q hpq
    rw [lemDecCalE_gres_zero_true hE.le]
    have h0 : ‖(mE E • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) p q‖ ^ 2 =
        0 := by
      simp [Matrix.smul_apply, Matrix.one_apply_ne hpq]
    rw [h0]
    have := gexRHS_nonneg (d := d) (L := sz.L n) (W := sz.W n) E 0
      (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (STblk sz n q) (STblk sz n p)
    positivity
  · intro σ a
    have h0 : avgErr d (sz.L n) (sz.W n) E 0
        (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a = 0 := by
      unfold avgErr greenBlk
      rw [lemDecCalE_blockMat_zero, lemDecCalE_gres_zero hE.le]
      simp [mSigma]
    rw [h0, norm_zero]
    positivity
  · intro σ a
    rw [lemDecCalE_STLKM_zero_time sz n hE.le, norm_zero]
    have := tailTD_nonneg (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := 0) (D := D)
      (r := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) hW0.le
    exact mul_nonneg hJ0 this
  · intro a b
    rw [lemDecCalE_STKloop_zero_time]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hm : ‖mSigma E true * mSigma E false‖ = 1 := by
      rw [norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, mul_one]
    rw [norm_mul, norm_mul, hm, mul_one, norm_inv, norm_pow, Complex.norm_natCast, sub_zero,
      mul_one]
    have : ‖(if a = b then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖(if a = b then (1 : ℂ) else 0)‖
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = K₀ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ - (K₀ - 1) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by ring
      _ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
          have : 0 ≤ (K₀ - 1) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ :=
            mul_nonneg (by linarith) (by positivity)
          linarith
  · intro a b hab
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
    have hl0 : 0 < Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    have hell : 0 < ellT (sz.L n) (sz.lam n) 0 := ellT_pos hL1
    have hpos : 0 < (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
        ellT (sz.L n) (sz.lam n) 0) := by
      have := Real.rpow_pos_of_pos hl0 ((3 : ℝ) / 2)
      positivity
    have hab' : a ≠ b := by
      intro h
      subst h
      simp only [sub_self, lemDecCalE_zdistInf_zero, Nat.cast_zero] at hab
      linarith
    rw [lemDecCalE_STKloop_zero_time]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hab', ite_false, mul_zero, norm_zero]
    exact Real.rpow_nonneg hW0.le _

end Witness

/-! ## 8. The instance at `d = 3`: `E2Hyp` nonempty, and `lemDecCalE_lk` applied to it -/

section Instance

open RBM.Gauss.SizesInst

private theorem lemDecCalE_inst_values :
    (sz0.L 1 = 8) ∧ (sz0.W 1 = 1024) ∧ (sz0.lam 1 = 1 / 4096) := by
  refine ⟨rfl, rfl, ?_⟩
  norm_num [sz0]

/-- **Nondegenerate instance of `E2Hyp`** at `d = 3`: the preflight sequence `sz0` at `n = 1`
(`L = 8`, `W = 1024`, `lam = 1/4096`, `N = 2^39`), `E = 1/2`, `u = 0`, `D = 8`,
`Λ = K₀ = J = 1`, `M = 0`.  Every conjunct is discharged by numbers: `log 1024 ≥ 4`
(`e⁴ < 1024`), `L^d W^{2d} = 2^69 ≤ 2^80 = W^D`, `lam² W^d = 64 ≥ 1`. -/
theorem LemDecCalE_inst :
    E2Hyp sz0 1 (1 / 2) 0 8 1 1 1
      (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) := by
  obtain ⟨hL, hW, hlam⟩ := lemDecCalE_inst_values
  have hWc : ((sz0.W 1 : ℕ) : ℝ) = 1024 := by rw [hW]; norm_num
  have hLc : ((sz0.L 1 : ℕ) : ℝ) = 8 := by rw [hL]; norm_num
  refine LemDecCalE_e2Hyp_zero sz0 1 (by norm_num) (by norm_num [abs_of_pos]) ?_ ?_ ?_ le_rfl le_rfl
    ?_ ?_ le_rfl ?_
  · rw [hlam]; norm_num
  · rw [hlam]; norm_num
  · rw [hlam, hWc]; norm_num
  · rw [hWc]
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 4
      _ ≤ (1024 : ℝ) := by norm_num
  · rw [hWc, hLc]
    have h : ((1024 : ℝ) ^ (8 : ℝ)) = (1024 : ℝ) ^ (8 : ℕ) := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h]
    norm_num
  · rw [hWc]; norm_num

/-- **Check (ticket T2164): `lemDecCalE_lk` applied to the instance `LemDecCalE_inst`** at
`σ = (+,-)` and `a = (0, e₁)`, `e₁ = (1, 0, 0)`: the left side is `0` (`𝓛 = 𝒦` at `M = 0`), the right side
is positive. -/
example :
    ‖STELKLKM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
        ![true, false] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]‖ ≤
      lossE2 3 (sz0.L 1) (sz0.W 1) 1 1 *
        ((1 - (0 : ℝ))⁻¹ * (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ * (1 : ℝ) ^ 2) *
          STtailTD sz0 1 0 8 ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] :=
  lemDecCalE_lk 3 sz0 1 (1 / 2) 0 8 1 1 1 0 LemDecCalE_inst _ _

/-- The right side of the check is positive (so the instance is not `0 ≤ 0`): `lossE2 > 0`, the
scale `(1-u)⁻¹ (W^d|1-u|)⁻¹ = 2^{-30}` and `T_{0,8}(r) ≥ W^{-8} > 0`. -/
example : 0 < lossE2 3 (sz0.L 1) (sz0.W 1) 1 1 *
        ((1 - (0 : ℝ))⁻¹ * (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ * (1 : ℝ) ^ 2) *
          STtailTD sz0 1 0 8 ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] := by
  obtain ⟨hL, hW, hlam⟩ := lemDecCalE_inst_values
  have hWc : ((sz0.W 1 : ℕ) : ℝ) = 1024 := by rw [hW]; norm_num
  have hL3 : 3 ≤ sz0.L 1 := by rw [hL]; norm_num
  have hconst := LemDecCalE_lk_const_le_lossE2 LemDecCalE_inst
  have hloss : 0 < lossE2 3 (sz0.L 1) (sz0.W 1) 1 1 := by
    refine lt_of_lt_of_le ?_ hconst
    positivity
  have hT : 0 < STtailTD sz0 1 0 8 ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] := by
    unfold STtailTD tailTD
    have := Real.rpow_pos_of_pos (by rw [hWc]; norm_num : (0 : ℝ) < ((sz0.W 1 : ℕ) : ℝ)) (-8 : ℝ)
    have h2 : 0 ≤ ((((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹) ^ 2 *
        Real.exp (-Real.sqrt (((zdistInf 3 (sz0.L 1) (![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 0 -
          ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 1) : ℕ) : ℝ))) := by positivity
    linarith
  have hs : 0 < (1 - (0 : ℝ))⁻¹ * (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ * (1 : ℝ) ^ 2 := by
    rw [hWc]; norm_num
  positivity

end Instance

end RBM.Path
