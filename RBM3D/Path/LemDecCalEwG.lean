/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.LemDecCalE

/-!
# `lem_dec_calE`, second part: the `ℰ^{G̃,(2)}` bound `res_deccalE_wG` (S5-08)

Ticket T2172 (S5-08, ST-4).  Port of `RBM2D/Path/LemDecCalEwG.lean` at commit `c9a24cf`
(cited `wG2D:<line>`: pin `:46`, `fG` `:90`, `tri` `:145`, `norm_loop3_le_tri` `:158`,
`tri_swap` `:199`, `tri_le_of_pt` `:209`, `avg` `:232`, `tri_le_avg12` `:236`,
`tri_le_avg23` `:266`, `avg_le` `:297`, `fG_e6/e7/e8` `:339-352`, `EGt_le_pref` `:358`,
`loops_le_tri` `:412`, `facts` `:435`, `fG_near_far` `:483`, `near_sum` `:602`,
`fG_long` `:765`, `fG_sqrt` `:795`, `fG_off` `:839`, `avg_le_hyp` `:880`, `far_pt` `:921`,
`far_sum` `:1036`, `near_norm` `:1256`, `lemDecCalE_wG` `:1276`) to `d ≥ 3`; the statement of the
square-root convolution is the `d ≥ 3` form of `RBM2D/Path/TailSums.lean` `ConvSqrtTailT` `:74`
(cited `ts2D:74`); its proof follows the ticket's route (T2a)-(T2c), not RBM2D's `conv_sqrt_core`
`:590`.  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem_dec_calE` `3_5:2314-2338`,
`res_deccalE_wG` `3_5:2322-2325`, `def_WTuD` `3_5:2297`; `paper/tex/1_2_Intro_model_result.tex`:
`def_EwtG` `1_2:962`.

Differences from RBM2D (each one forced by `d ≥ 3`, by every `σ ∈ {±}²`, by the premise bundle or
by the paper's `J^{3/2}`):
* the lattice is `Zd d L`, the block-product index is `Vtx d L W` (RBM2D: `Z2 L`,
  `BlockIndex L W`), the distance is `zdistInf`; `ℓ_u = 1` (`1 - u ≥ ilambda²`), so RBM2D's
  `ρ`, `η_u`, `ℓ_u`, the endpoint `v` and `tailT` disappear: `M_u = W^d (1 - u)`,
  `𝒯_{u,D} = tailTD`, `ℓ* = (log W)^{3/2}`;
* the bundle `E2HypWG` adds to the merged `E2Hyp` the floor `(L^d W^{6d})² ≤ W^D` and the
  three-loop bound `|𝓛^{(3)}_{u,σ,a}| ≤ Λ M_u⁻²` for every `σ, a` (clause 2 of RBM2D `goodSet`
  at `k = 3`, not carried by `E2Hyp`);
* `L² W¹²` becomes `P = L^d W^{6d}`; the ball count `(2R+1)²` becomes `(2R+1)^d`
  (`LemDecCalE_e10a`); the constants `25, 50, 125, 225` become `9^d`, `2·9^d`, `5·9^d`, `9^{d+1}`;
* the square-root convolution `ts2D:74` (`30000 ℓ² M_u⁻¹`) is proved at `d ≥ 3` as
  `LemDecCalEwG_sum_sqrt_tail` with `C_sq(d) = 5 (1 + 24576 d⁴)^d`;
* RBM2D has the conclusion at `σ = (+,-)` only; here every `σ ∈ {±}²` (the prefactors
  `⟨G̃(σ₁)E_x⟩`, `⟨G̃(σ₂)E_x⟩` are bounded by (e9) for both signs, the triangle sum `tri` is
  sign-free);
* the power of `J` is the paper's `J^{3/2}` (RBM2D's pin has `J²`): `fG_off` keeps `√J`
  (RBM2D: `10 Λ K₀ J √m`, `wG2D:839`) and `far_pt` keeps `k³` (RBM2D weakens `k³ ≤ (225 Λ J)²`,
  `wG2D:1107`); `J ≤ W` is not used (RBM2D: `wG2D:695`);
* the loss is `lossE2wG = lossE2 · 1000^d (1 + log P)^{2d}`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Path

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green

/-! ## 0. The pinned vocabulary (T2172 target 1; check file section 2, verbatim) -/

/-- **The hypothesis bundle of `res_deccalE_wG`** at `d ≥ 3` (one time `u`, the fine matrix `M`): the merged
`E2Hyp` (S5-05), the floor `(L^d W^{6d})² ≤ W^D` (the `d`-form of RBM2D's `L²W¹² ≤ W^{D/2}`, `LemDecCalE.lean:63`
at `c9a24cf`; it gives the square-root convolution floor `W^{-D} L^{2d} ≤ M_u^{-2}` and a near long-edge term
without `J ≤ W`), and the three-loop bound `|𝓛^{(3)}_{u,σ,a}| ≤ Λ (W^d(1-u))^{-2}` for every `σ`, `a` (clause 2 of
RBM2D `goodSet` at `k = 3`, `GoodSet.lean:49`, used by RBM2D `LemDecCalEwG.lean:592-598`; not in `E2Hyp`; S5-09
source: `STLmaxU`). -/
def E2HypWG {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  E2Hyp sz n E u D Λ K₀ J M ∧
    (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)),
      ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2

/-- The explicit loss of `res_deccalE_wG`: the loss of `res_deccalE_lk` times
`κ_wG(d) (1 + log P)^{2d}`, `P = L^d W^{6d}`, `κ_wG(d) = 1000^d` (closed form; polylogarithmic in `N`
times `e^{O((log W)^{3/4})}`). -/
def lossE2wG (d L W : ℕ) (Λ K₀ : ℝ) : ℝ :=
  lossE2 d L W Λ K₀ * ((1000 : ℝ) ^ d * (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (6 * d))) ^ (2 * d))

/-- **`res_deccalE_wG`** (`3_5:2322-2325`), deterministic at one time `u`, every `σ ∈ {±}²`:
`|ℰ^{G̃,(2)}_{u,σ,a}| ≤ lossE2wG · (1-u)⁻¹ [1(|a₁-a₂|_∞ ≤ (log W)^{3/2}) + (W^d|1-u|)^{-1/2} J^{3/2}] T_{u,D}(|a₁-a₂|)`;
the right side after the loss is the second conjunct of `STLemDecCalEConcl` (`Step5Pins.lean:171-177`) at
`J := Jst n u D`.  The power `J^{3/2}` is the paper's (RBM2D's pin has `J²`). -/
def LemDecCalE_wG (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2HypWG sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STEGtM sz n E u M σ a‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ *
          ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
          STtailTD sz n u D a)

/-! ## 1. Lattice helpers (copies or adaptations of the private helpers of `Path/LemDecCalE`, prefix `lemDecCalEwG_`) -/

section Lattice

private theorem lemDecCalEwG_zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem lemDecCalEwG_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem lemDecCalEwG_zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

private theorem lemDecCalEwG_zdistInf_tri (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    zdistInf d L (x - w) ≤ zdistInf d L (x - y) + zdistInf d L (y - w) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact lemDecCalEwG_zdistInf_add_le d L _ _

private theorem lemDecCalEwG_zdistInf_sub_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, lemDecCalEwG_zdistInf_neg]

private theorem lemDecCalEwG_zdistInf_tri_real (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    (zdistInf d L (x - w) : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + (zdistInf d L (y - w) : ℝ) := by
  exact_mod_cast lemDecCalEwG_zdistInf_tri d L x y w

private theorem lemDecCalEwG_zdist_le_zdistInf (d L : ℕ) (x : Zd d L) (i : Fin d) :
    zdist L (x i) ≤ zdistInf d L x :=
  Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)

/-- `exp(-γ √j) ≤ 24 / (γ⁴ j²)` for `j ≥ 1` (`e^y ≥ y⁴/24`; `LemDecCalE.lean:224`). -/
private theorem lemDecCalEwG_exp_neg_le {γ : ℝ} (hγ : 0 < γ) {j : ℕ} (hj : 1 ≤ j) :
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

/-- `Σ_{j=1}^{m} exp(-γ √j) ≤ 48 / γ⁴` (`LemDecCalE.lean:244`). -/
private theorem lemDecCalEwG_sum_exp_le {γ : ℝ} (hγ : 0 < γ) (m : ℕ) :
    ∑ j ∈ Finset.range m, Real.exp (-(γ * Real.sqrt ((j + 1 : ℕ) : ℝ))) ≤ 48 / γ ^ 4 := by
  have h1 : ∑ j ∈ Finset.range m, Real.exp (-(γ * Real.sqrt ((j + 1 : ℕ) : ℝ))) ≤
      ∑ j ∈ Finset.range m, (24 / γ ^ 4) * ((((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have := lemDecCalEwG_exp_neg_le hγ (j := j + 1) (by omega)
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

private theorem lemDecCalEwG_sum_val (L : ℕ) [NeZero L] (g : ℕ → ℝ) :
    ∑ y : ZMod L, g y.val = ∑ v ∈ Finset.range L, g v := by
  refine Finset.sum_bij (fun y _ => y.val) (fun y _ => Finset.mem_range.2 (ZMod.val_lt y))
    (fun a _ b _ h => ZMod.val_injective L h) (fun v hv => ?_) (fun y _ => rfl)
  exact ⟨(v : ZMod L), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hv)⟩

/-- The one-dimensional sum `Σ_{y ∈ Z_L} exp(-γ √|y|_L) ≤ 1 + 96/γ⁴`, uniformly in `L`
(`LemDecCalE.lean:274`). -/
private theorem lemDecCalEwG_sum_zdist_le (L : ℕ) [NeZero L] {γ : ℝ} (hγ : 0 < γ) :
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
    rw [lemDecCalEwG_sum_val L F]
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by have := NeZero.pos L; omega⟩
    rw [hm, Finset.sum_range_succ']
    have h0 : F 0 = 1 := by simp [hF]
    have := lemDecCalEwG_sum_exp_le hγ m
    simp only [hF] at h0 ⊢
    rw [h0]
    linarith
  have hsum2 : ∑ y : ZMod L, F (L - y.val) ≤ 48 / γ ^ 4 := by
    rw [lemDecCalEwG_sum_val L (fun v => F (L - v))]
    have hrefl := Finset.sum_range_reflect (fun j => F (j + 1)) L
    have h3 : ∑ v ∈ Finset.range L, F (L - v) = ∑ j ∈ Finset.range L, F (j + 1) := by
      rw [← hrefl]
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.1 hj
      congr 1
      omega
    rw [h3]
    exact lemDecCalEwG_sum_exp_le hγ L
  calc ∑ y : ZMod L, Real.exp (-(γ * Real.sqrt (zdist L y : ℝ)))
      ≤ ∑ y : ZMod L, (F y.val + F (L - y.val)) := Finset.sum_le_sum fun y _ => hpt y
    _ = ∑ y : ZMod L, F y.val + ∑ y : ZMod L, F (L - y.val) := Finset.sum_add_distrib
    _ ≤ 1 + 96 / γ ^ 4 := by
        have : (96 : ℝ) / γ ^ 4 = 48 / γ ^ 4 + 48 / γ ^ 4 := by ring
        linarith

/-- **The lattice sum `S_{d,1/4}`**: `Σ_{z ∈ Z_L^d} exp(-¼ √|z|_∞) ≤ (1 + 24576 d⁴)^d`, uniformly in `L`
(the product bound of `LemDecCalE_sum_zd_le` with `γ = (4d)⁻¹`, `96 / γ⁴ = 24576 d⁴`). -/
private theorem lemDecCalEwG_sum_zd_quarter (d L : ℕ) [NeZero L] (hd : 1 ≤ d) :
    ∑ z : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L z : ℝ))) ≤
      (1 + 24576 * (d : ℝ) ^ 4) ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set γ : ℝ := 1 / (4 * d) with hγ
  have hγ0 : 0 < γ := by positivity
  set g : ZMod L → ℝ := fun y => Real.exp (-(γ * Real.sqrt (zdist L y : ℝ))) with hg
  have hpt : ∀ z : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L z : ℝ))) ≤ ∏ i, g (z i) := by
    intro z
    simp only [hg]
    rw [← Real.exp_sum]
    refine Real.exp_le_exp.2 ?_
    rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Finset.mul_sum]
    have hs : ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ) ≤ d * Real.sqrt (zdistInf d L z : ℝ) := by
      calc ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ)
          ≤ ∑ _i : Fin d, Real.sqrt (zdistInf d L z : ℝ) :=
            Finset.sum_le_sum fun i _ =>
              Real.sqrt_le_sqrt (by exact_mod_cast lemDecCalEwG_zdist_le_zdistInf d L z i)
        _ = d * Real.sqrt (zdistInf d L z : ℝ) := by simp
    calc γ * ∑ i : Fin d, Real.sqrt (zdist L (z i) : ℝ)
        ≤ γ * (d * Real.sqrt (zdistInf d L z : ℝ)) := mul_le_mul_of_nonneg_left hs hγ0.le
      _ = 1 / 4 * Real.sqrt (zdistInf d L z : ℝ) := by rw [hγ]; field_simp
  have hprod : ∑ z : Zd d L, ∏ i, g (z i) = (∑ y : ZMod L, g y) ^ d := by
    have := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (ZMod L)))
      (fun _ y => g y)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    simp
  have h1d := lemDecCalEwG_sum_zdist_le L hγ0
  have hγ4 : 96 / γ ^ 4 = 24576 * (d : ℝ) ^ 4 := by
    rw [hγ]; field_simp; ring
  rw [hγ4] at h1d
  calc ∑ z : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L z : ℝ)))
      ≤ ∑ z : Zd d L, ∏ i, g (z i) := Finset.sum_le_sum fun z _ => hpt z
    _ = (∑ y : ZMod L, g y) ^ d := hprod
    _ ≤ (1 + 24576 * (d : ℝ) ^ 4) ^ d :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun y _ => (Real.exp_pos _).le) h1d d

end Lattice

/-! ## 2. Target 2: the square-root convolution of the tail over `Z_L^d` -/

section SqrtConv

private theorem lemDecCalEwG_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := by positivity
  nlinarith

/-- (T2a) `√(A e^{-√p} + w) ≤ √A e^{-½√p} + √w`. -/
private theorem lemDecCalEwG_sqrt_tail_le {A w : ℝ} (hA : 0 ≤ A) (hw : 0 ≤ w) (p : ℝ) :
    Real.sqrt (A * Real.exp (-Real.sqrt p) + w) ≤
      Real.sqrt A * Real.exp (-(1 / 2 * Real.sqrt p)) + Real.sqrt w := by
  have h1 : Real.sqrt (A * Real.exp (-Real.sqrt p) + w) ≤
      Real.sqrt (A * Real.exp (-Real.sqrt p)) + Real.sqrt w :=
    lemDecCalEwG_sqrt_add_le (by positivity) hw
  have h2 : Real.sqrt (A * Real.exp (-Real.sqrt p)) =
      Real.sqrt A * Real.exp (-(1 / 2 * Real.sqrt p)) := by
    rw [Real.sqrt_mul hA, ← Real.exp_half]
    congr 2
    ring
  rw [h2] at h1
  exact h1

private theorem lemDecCalEwG_sqrt_quarter {p : ℝ} (hp : 0 ≤ p) :
    Real.sqrt (p / 4) = Real.sqrt p / 2 := by
  rw [Real.sqrt_div hp, show Real.sqrt 4 = 2 from by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-- (T2b) `e^{-½√p} e^{-½√q} ≤ e^{-½√r} (e^{-¼√p} + e^{-¼√q})` for `r ≤ p + q`: the merged
`LemDecCalE_exp_conv` at `(p/4, q/4, r/4)`. -/
private theorem lemDecCalEwG_exp_conv4 {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hr : r ≤ p + q) :
    Real.exp (-(1 / 2 * Real.sqrt p)) * Real.exp (-(1 / 2 * Real.sqrt q)) ≤
      Real.exp (-(1 / 2 * Real.sqrt r)) *
        (Real.exp (-(1 / 4 * Real.sqrt p)) + Real.exp (-(1 / 4 * Real.sqrt q))) := by
  have h := LemDecCalE_exp_conv (p := p / 4) (q := q / 4) (r := r / 4) (by positivity)
    (by positivity) (by linarith)
  rw [lemDecCalEwG_sqrt_quarter hp, lemDecCalEwG_sqrt_quarter hq, lemDecCalEwG_sqrt_quarter hr0] at h
  rw [← Real.exp_add]
  have e1 : -(1 / 2 * Real.sqrt p) + -(1 / 2 * Real.sqrt q) =
      -(Real.sqrt p / 2) - Real.sqrt q / 2 := by ring
  have e2 : -(1 / 2 * Real.sqrt r) = -(Real.sqrt r / 2) := by ring
  have e3 : -(1 / 4 * Real.sqrt p) = -(1 / 2 * (Real.sqrt p / 2)) := by ring
  have e4 : -(1 / 4 * Real.sqrt q) = -(1 / 2 * (Real.sqrt q / 2)) := by ring
  rw [e1, e2, e3, e4]
  exact h

/-- **Target 2** (RBM2D `ConvSqrtTailT` `ts2D:74`, at `d ≥ 3`, in the form of the merged
`LemDecCalE_sum_tail_tail`): for `w L^{2d} ≤ A`,
`Σ_x √(A e^{-√|x-a₁|} + w) · √(A e^{-√|a₀-x|} + w) ≤ C_sq(d) √A √(A e^{-√|a₀-a₁|} + w)`,
`C_sq(d) = 5 (1 + 24576 d⁴)^d`.  Route: (T2a) the tail, (T2b) `LemDecCalE_exp_conv` at the quarter
arguments, (T2c) the sums `S_{d,1/4}`, `S_{d,1/2}` and `L^d w ≤ √(A w)`. -/
theorem LemDecCalEwG_sum_sqrt_tail {d L : ℕ} [NeZero L] (hd : 1 ≤ d) {A w : ℝ} (hA : 0 ≤ A)
    (hw : 0 ≤ w) (hfl : w * (L : ℝ) ^ (2 * d) ≤ A) (a₀ a₁ : Zd d L) :
    ∑ x : Zd d L, Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
        Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
      5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * Real.sqrt A *
        Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w) := by
  set S : ℝ := (1 + 24576 * (d : ℝ) ^ 4) ^ d with hS
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hS1 : 1 ≤ S := one_le_pow₀ (by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ d) 4])
  set Er : ℝ := Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ))) with hEr
  have hEr0 : 0 ≤ Er := (Real.exp_pos _).le
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsw : 0 ≤ Real.sqrt w := Real.sqrt_nonneg w
  have hAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
  -- the lattice sums
  have hq1 : ∑ x : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) ≤ S := by
    have : ∑ x : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) =
        ∑ z : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L z : ℝ))) :=
      Fintype.sum_equiv (Equiv.subRight a₁) _ _ fun x => rfl
    rw [this]; exact lemDecCalEwG_sum_zd_quarter d L hd
  have hq2 : ∑ x : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ))) ≤ S := by
    have : ∑ x : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ))) =
        ∑ z : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L z : ℝ))) :=
      Fintype.sum_equiv (Equiv.subLeft a₀) _ _ fun x => rfl
    rw [this]; exact lemDecCalEwG_sum_zd_quarter d L hd
  have hS2le : (1 + 1536 * (d : ℝ) ^ 4) ^ d ≤ S :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ d) 4]) d
  have hh1 : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) ≤ S := by
    have : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) =
        ∑ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ))) :=
      Fintype.sum_equiv (Equiv.subRight a₁) _ _ fun x => rfl
    rw [this]; exact (LemDecCalE_sum_zd_le d L hd).trans hS2le
  have hh2 : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ))) ≤ S := by
    have : ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ))) =
        ∑ z : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L z : ℝ))) :=
      Fintype.sum_equiv (Equiv.subLeft a₀) _ _ fun x => rfl
    rw [this]; exact (LemDecCalE_sum_zd_le d L hd).trans hS2le
  -- the pointwise bound
  have hpt : ∀ x : Zd d L,
      Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
          Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
        A * Er * (Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
            Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) +
          Real.sqrt A * Real.sqrt w *
            (Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
              Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) + w := by
    intro x
    set p : ℝ := (zdistInf d L (x - a₁) : ℝ) with hp
    set q : ℝ := (zdistInf d L (a₀ - x) : ℝ) with hq
    have hp0 : 0 ≤ p := Nat.cast_nonneg _
    have hq0 : 0 ≤ q := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) ≤ (zdistInf d L (a₀ - a₁) : ℝ) := Nat.cast_nonneg _
    have hr : (zdistInf d L (a₀ - a₁) : ℝ) ≤ p + q := by
      have := lemDecCalEwG_zdistInf_tri_real d L a₀ x a₁
      rw [hp, hq]; linarith
    have hconv := lemDecCalEwG_exp_conv4 hp0 hq0 hr0 hr
    have ha := lemDecCalEwG_sqrt_tail_le hA hw p
    have hb := lemDecCalEwG_sqrt_tail_le hA hw q
    set ep := Real.exp (-(1 / 2 * Real.sqrt p)) with hep
    set eq' := Real.exp (-(1 / 2 * Real.sqrt q)) with heq
    have hep0 : 0 ≤ ep := (Real.exp_pos _).le
    have heq0 : 0 ≤ eq' := (Real.exp_pos _).le
    have hprod : Real.sqrt (A * Real.exp (-Real.sqrt p) + w) *
          Real.sqrt (A * Real.exp (-Real.sqrt q) + w) ≤
        (Real.sqrt A * ep + Real.sqrt w) * (Real.sqrt A * eq' + Real.sqrt w) :=
      mul_le_mul ha hb (Real.sqrt_nonneg _) (by positivity)
    have hexp : (Real.sqrt A * ep + Real.sqrt w) * (Real.sqrt A * eq' + Real.sqrt w) =
        A * (ep * eq') + Real.sqrt A * Real.sqrt w * (ep + eq') + (Real.sqrt w * Real.sqrt w) := by
      have h0 : (Real.sqrt A * ep + Real.sqrt w) * (Real.sqrt A * eq' + Real.sqrt w) =
          (Real.sqrt A * Real.sqrt A) * (ep * eq') + Real.sqrt A * Real.sqrt w * (ep + eq') +
            (Real.sqrt w * Real.sqrt w) := by ring
      rw [h0, hAA]
    have hww : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw
    refine hprod.trans ?_
    rw [hexp, hww]
    have := mul_le_mul_of_nonneg_left hconv hA
    nlinarith
  have hsum : ∑ x : Zd d L,
      Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (x - a₁) : ℝ)) + w) *
        Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - x) : ℝ)) + w) ≤
      A * Er * (S + S) + Real.sqrt A * Real.sqrt w * (S + S) + (L : ℝ) ^ d * w := by
    calc _ ≤ ∑ x : Zd d L, (A * Er * (Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
            Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) +
          Real.sqrt A * Real.sqrt w *
            (Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
              Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) + w) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = A * Er * (∑ x : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
              ∑ x : Zd d L, Real.exp (-(1 / 4 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) +
            Real.sqrt A * Real.sqrt w *
              (∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (x - a₁) : ℝ))) +
                ∑ x : Zd d L, Real.exp (-(1 / 2 * Real.sqrt (zdistInf d L (a₀ - x) : ℝ)))) +
            (L : ℝ) ^ d * w := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp
      _ ≤ A * Er * (S + S) + Real.sqrt A * Real.sqrt w * (S + S) + (L : ℝ) ^ d * w := by
          have e1 : 0 ≤ A * Er := by positivity
          have e2 : 0 ≤ Real.sqrt A * Real.sqrt w := by positivity
          gcongr
  -- `L^d w ≤ √A √w`
  have hLw : (L : ℝ) ^ d * w ≤ Real.sqrt A * Real.sqrt w := by
    rw [← Real.sqrt_mul hA]
    refine Real.le_sqrt_of_sq_le ?_
    have : ((L : ℝ) ^ d * w) ^ 2 = (w * (L : ℝ) ^ (2 * d)) * w := by
      rw [pow_mul']; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hfl hw
  -- the final constant
  have hfin : (3 / 2) * Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w) ≥
      Real.sqrt A * Er + Real.sqrt w := by
    set a : ℝ := Real.sqrt A * Er with ha
    set b : ℝ := Real.sqrt w with hb
    have ha0 : 0 ≤ a := by positivity
    have hsq : a ^ 2 + b ^ 2 = A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w := by
      rw [ha, hb, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hw, hEr, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring_nf
    have : (2 / 3) * (a + b) ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [sq_nonneg (a - b)]
    rw [hsq] at this
    linarith
  set Rr : ℝ := Real.sqrt (A * Real.exp (-Real.sqrt (zdistInf d L (a₀ - a₁) : ℝ)) + w) with hRr
  have hRr0 : 0 ≤ Rr := Real.sqrt_nonneg _
  calc _ ≤ A * Er * (S + S) + Real.sqrt A * Real.sqrt w * (S + S) + (L : ℝ) ^ d * w := hsum
    _ ≤ (2 * S + 1) * Real.sqrt A * (Real.sqrt A * Er + Real.sqrt w) := by
        have e1 : A * Er * (S + S) = 2 * S * Real.sqrt A * (Real.sqrt A * Er) := by
          calc A * Er * (S + S) = (Real.sqrt A * Real.sqrt A) * Er * (S + S) := by rw [hAA]
            _ = _ := by ring
        have e2 : Real.sqrt A * Real.sqrt w * (S + S) = 2 * S * Real.sqrt A * Real.sqrt w := by ring
        nlinarith [mul_nonneg hsA hsw, mul_nonneg hsA hEr0, mul_nonneg hsA (mul_nonneg hsA hEr0)]
    _ ≤ (2 * S + 1) * Real.sqrt A * ((3 / 2) * Rr) := by
        refine mul_le_mul_of_nonneg_left hfin (by positivity)
    _ ≤ 5 * S * Real.sqrt A * Rr := by
        have : 0 ≤ Real.sqrt A * Rr := by positivity
        nlinarith

end SqrtConv

/-! ## 3. Triangle sums on the block-product index (`wG2D:90-336`)

Everything here is for an arbitrary symmetric nonnegative edge bound `f` on `Vtx d L W` and a matrix `H`
on `Vtx d L W` with `‖Gres H z s p q‖ ≤ f p q` for both signs `s`. -/

section Tri

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The block weight `|E_c|_{pp} = W^{-d} 1(p.1 = c)`. -/
private def wt (c : Zd d L) (p : Vtx d L W) : ℝ := if p.1 = c then ((W : ℝ) ^ d)⁻¹ else 0

omit [NeZero L] [NeZero W] in
private theorem wt_nonneg (c : Zd d L) (p : Vtx d L W) : 0 ≤ (wt c p : ℝ) := by
  unfold wt; split_ifs <;> positivity

omit [NeZero L] [NeZero W] in
private theorem wt_le (c : Zd d L) (p : Vtx d L W) : (wt c p : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by
  unfold wt; split_ifs <;> first | exact le_rfl | positivity

private theorem sum_wt (c : Zd d L) : ∑ p : Vtx d L W, (wt c p : ℝ) = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  unfold wt
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · intro x _ hx
    simp [hx]
  · intro h; exact absurd (Finset.mem_univ c) h

/-- The triangle sum `Σ_{p ∈ c₃, q ∈ c₁, r ∈ c₂} W^{-3d} f(p,q) f(q,r) f(r,p)` (`wG2D:145`). -/
private def tri (f : Vtx d L W → Vtx d L W → ℝ) (c₁ c₂ c₃ : Zd d L) : ℝ :=
  ∑ p : Vtx d L W, ∑ q : Vtx d L W, ∑ r : Vtx d L W,
    wt c₃ p * wt c₁ q * wt c₂ r * (f p q * f q r * f r p)

omit [NeZero W] in
/-- A three-loop as a triple sum of entries (`wG2D:150`, for any signs). -/
private theorem loop3_expand (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s₁ s₂ s₃ : Bool)
    (c₁ c₂ c₃ : Zd d L) :
    loopM d L W H z ![s₁, s₂, s₃] ![c₁, c₂, c₃] =
      Matrix.trace (Gres H z s₁ * Eblk d L W c₁ * Gres H z s₂ * Eblk d L W c₂ *
        Gres H z s₃ * Eblk d L W c₃) := by
  simp [loopM, List.ofFn_succ, Matrix.mul_assoc]

/-- Every three-loop is bounded by the triangle sum (`wG2D:158`, sign-free). -/
private theorem norm_loop3_le_tri {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    {f : Vtx d L W → Vtx d L W → ℝ}
    (hf : ∀ (s : Bool) (p q : Vtx d L W), ‖Gres H z s p q‖ ≤ f p q)
    (s₁ s₂ s₃ : Bool) (c₁ c₂ c₃ : Zd d L) :
    ‖loopM d L W H z ![s₁, s₂, s₃] ![c₁, c₂, c₃]‖ ≤ tri f c₁ c₂ c₃ := by
  rw [loop3_expand]
  simp only [Eblk, Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hw : ‖(((W : ℂ) ^ d)⁻¹ : ℂ)‖ = ((W : ℝ) ^ d)⁻¹ := by simp
  have hw0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  calc _ ≤ ∑ p : Vtx d L W, ∑ r : Vtx d L W, ∑ q : Vtx d L W,
        wt c₃ p * wt c₁ q * wt c₂ r * (f p q * f q r * f r p) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        split_ifs with hp
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          split_ifs with hr
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
            split_ifs with hq
            · have h1 := hf s₁ p q
              have h2 := hf s₂ q r
              have h3 := hf s₃ r p
              have hf1 : 0 ≤ f p q := (norm_nonneg _).trans h1
              have hf2 : 0 ≤ f q r := (norm_nonneg _).trans h2
              simp only [wt, hp, hq, hr, ite_true, norm_mul, hw]
              calc ‖Gres H z s₁ p q‖ * ((W : ℝ) ^ d)⁻¹ * ‖Gres H z s₂ q r‖ *
                    ((W : ℝ) ^ d)⁻¹ * ‖Gres H z s₃ r p‖ * ((W : ℝ) ^ d)⁻¹
                  = (((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)⁻¹) *
                      (‖Gres H z s₁ p q‖ * ‖Gres H z s₂ q r‖ * ‖Gres H z s₃ r p‖) := by ring
                _ ≤ (((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)⁻¹) *
                      (f p q * f q r * f r p) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hf1) h3 (norm_nonneg _)
                        (mul_nonneg hf1 hf2)) (by positivity)
            · simp [wt, hq]
          · simp [wt, hr]
        · simp [wt, hp]
    _ = tri f c₁ c₂ c₃ := by
        unfold tri
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- The triangle sum is symmetric in its first two blocks (`wG2D:199`), for a symmetric `f`. -/
private theorem tri_swap {f : Vtx d L W → Vtx d L W → ℝ} (hs : ∀ p q, f p q = f q p)
    (c₁ c₂ c₃ : Zd d L) : tri f c₂ c₁ c₃ = tri f c₁ c₂ c₃ := by
  unfold tri
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  rw [hs p r, hs r q, hs q p]
  ring

/-- Pointwise bound on the three edges (`wG2D:209`). -/
private theorem tri_le_of_pt {f : Vtx d L W → Vtx d L W → ℝ} {c₁ c₂ c₃ : Zd d L} {B : ℝ}
    (h : ∀ p q r : Vtx d L W, p.1 = c₃ → q.1 = c₁ → r.1 = c₂ → f p q * f q r * f r p ≤ B) :
    tri f c₁ c₂ c₃ ≤ B := by
  calc tri f c₁ c₂ c₃
      ≤ ∑ p : Vtx d L W, ∑ q : Vtx d L W, ∑ r : Vtx d L W,
          wt c₃ p * (wt c₁ q * (wt c₂ r * B)) := by
        unfold tri
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
          Finset.sum_le_sum fun r _ => ?_
        by_cases hp : p.1 = c₃
        · by_cases hq : q.1 = c₁
          · by_cases hr : r.1 = c₂
            · have := mul_le_mul_of_nonneg_left (h p q r hp hq hr)
                (mul_nonneg (mul_nonneg (wt_nonneg c₃ p) (wt_nonneg c₁ q)) (wt_nonneg c₂ r))
              linarith
            · simp [wt, hr]
          · simp [wt, hq]
        · simp [wt, hp]
    _ = B := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_wt, one_mul]

/-- The average of `f` over two blocks (`wG2D:232`). -/
private def avg (f : Vtx d L W → Vtx d L W → ℝ) (c c' : Zd d L) : ℝ :=
  ∑ q : Vtx d L W, ∑ r : Vtx d L W, wt c q * (wt c' r * f q r)

/-- Two long edges bounded pointwise, the edge `c₁`–`c₂` averaged (`wG2D:236`). -/
private theorem tri_le_avg12 {f : Vtx d L W → Vtx d L W → ℝ} (hf0 : ∀ p q, 0 ≤ f p q)
    {c₁ c₂ c₃ : Zd d L} {B : ℝ}
    (h : ∀ p q r : Vtx d L W, p.1 = c₃ → q.1 = c₁ → r.1 = c₂ → f p q * f r p ≤ B) :
    tri f c₁ c₂ c₃ ≤ B * avg f c₁ c₂ := by
  calc tri f c₁ c₂ c₃
      ≤ ∑ p : Vtx d L W, ∑ q : Vtx d L W, ∑ r : Vtx d L W,
          wt c₃ p * (B * (wt c₁ q * (wt c₂ r * f q r))) := by
        unfold tri
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
          Finset.sum_le_sum fun r _ => ?_
        by_cases hp : p.1 = c₃
        · by_cases hq : q.1 = c₁
          · by_cases hr : r.1 = c₂
            · have hX : 0 ≤ wt c₃ p * wt c₁ q * wt c₂ r * f q r :=
                mul_nonneg (mul_nonneg (mul_nonneg (wt_nonneg c₃ p) (wt_nonneg c₁ q))
                  (wt_nonneg c₂ r)) (hf0 q r)
              have := mul_le_mul_of_nonneg_left (h p q r hp hq hr) hX
              calc wt c₃ p * wt c₁ q * wt c₂ r * (f p q * f q r * f r p)
                  = wt c₃ p * wt c₁ q * wt c₂ r * f q r * (f p q * f r p) := by ring
                _ ≤ wt c₃ p * wt c₁ q * wt c₂ r * f q r * B := this
                _ = wt c₃ p * (B * (wt c₁ q * (wt c₂ r * f q r))) := by ring
            · simp [wt, hr]
          · simp [wt, hq]
        · simp [wt, hp]
    _ = B * avg f c₁ c₂ := by
        unfold avg
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_wt, one_mul]

/-- Two long edges bounded pointwise, the edge `c₂`–`c₃` averaged (`wG2D:266`). -/
private theorem tri_le_avg23 {f : Vtx d L W → Vtx d L W → ℝ} (hf0 : ∀ p q, 0 ≤ f p q)
    (hs : ∀ p q, f p q = f q p) {c₁ c₂ c₃ : Zd d L} {B : ℝ}
    (h : ∀ p q r : Vtx d L W, p.1 = c₃ → q.1 = c₁ → r.1 = c₂ → f p q * f q r ≤ B) :
    tri f c₁ c₂ c₃ ≤ B * avg f c₃ c₂ := by
  calc tri f c₁ c₂ c₃
      ≤ ∑ p : Vtx d L W, ∑ q : Vtx d L W, ∑ r : Vtx d L W,
          wt c₁ q * (B * (wt c₃ p * (wt c₂ r * f p r))) := by
        unfold tri
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
          Finset.sum_le_sum fun r _ => ?_
        by_cases hp : p.1 = c₃
        · by_cases hq : q.1 = c₁
          · by_cases hr : r.1 = c₂
            · have hX : 0 ≤ wt c₃ p * wt c₁ q * wt c₂ r * f p r :=
                mul_nonneg (mul_nonneg (mul_nonneg (wt_nonneg c₃ p) (wt_nonneg c₁ q))
                  (wt_nonneg c₂ r)) (hf0 p r)
              have := mul_le_mul_of_nonneg_left (h p q r hp hq hr) hX
              rw [hs r p]
              calc wt c₃ p * wt c₁ q * wt c₂ r * (f p q * f q r * f p r)
                  = wt c₃ p * wt c₁ q * wt c₂ r * f p r * (f p q * f q r) := by ring
                _ ≤ wt c₃ p * wt c₁ q * wt c₂ r * f p r * B := this
                _ = wt c₁ q * (B * (wt c₃ p * (wt c₂ r * f p r))) := by ring
            · simp [wt, hr]
          · simp [wt, hq]
        · simp [wt, hp]
    _ = B * avg f c₃ c₂ := by
        unfold avg
        simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_wt, one_mul]

/-- The average over two blocks: the diagonal `q = r` costs `2Λ W^{-d}`, the rest `A`
(`wG2D:297`). -/
private theorem avg_le {f : Vtx d L W → Vtx d L W → ℝ} (hf0 : ∀ p q, 0 ≤ f p q) {Λ A : ℝ}
    (h6 : ∀ q r : Vtx d L W, f q r ≤ 2 * Λ)
    (h8 : ∀ q r : Vtx d L W, q ≠ r → f q r ≤ A) (hA : 0 ≤ A) (c c' : Zd d L) :
    avg f c c' ≤ 2 * Λ * ((W : ℝ) ^ d)⁻¹ + A := by
  have hin : ∀ q : Vtx d L W, ∑ r : Vtx d L W, wt c' r * f q r ≤ 2 * Λ * ((W : ℝ) ^ d)⁻¹ + A := by
    intro q
    have hΛ : 0 ≤ 2 * Λ := (hf0 q q).trans (h6 q q)
    calc ∑ r : Vtx d L W, wt c' r * f q r
        ≤ ∑ r : Vtx d L W, ((if r = q then wt c' r * (2 * Λ) else 0) + wt c' r * A) := by
          refine Finset.sum_le_sum fun r _ => ?_
          by_cases hr : r = q
          · subst hr
            simp only [ite_true]
            have := mul_le_mul_of_nonneg_left (h6 r r) (wt_nonneg c' r)
            have := mul_nonneg (wt_nonneg c' r) hA
            linarith
          · simp only [hr, ite_false, zero_add]
            exact mul_le_mul_of_nonneg_left (h8 q r (Ne.symm hr)) (wt_nonneg c' r)
      _ = wt c' q * (2 * Λ) + A := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_mul, sum_wt, one_mul]
          simp
      _ ≤ 2 * Λ * ((W : ℝ) ^ d)⁻¹ + A := by
          have := mul_le_mul_of_nonneg_right (wt_le c' q) hΛ
          linarith
  calc avg f c c' ≤ ∑ q : Vtx d L W, wt c q * (2 * Λ * ((W : ℝ) ^ d)⁻¹ + A) := by
        unfold avg
        refine Finset.sum_le_sum fun q _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hin q) (wt_nonneg c q)
    _ = 2 * Λ * ((W : ℝ) ^ d)⁻¹ + A := by
        rw [← Finset.sum_mul, sum_wt, one_mul]

end Tri

/-! ## 4. The fine entries on the block-product index: `fG`, (e6)-(e8), the prefactor (`wG2D:90-432`) -/

section Entries

section Bridge

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `G(-) = G(+)ᴴ` for Hermitian `H` (the text of the merged `ST_Gres_false`,
`Induction/Step2Iterate.lean:1198`, which is not in the import closure). -/
private theorem lemDecCalEwG_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  simp

/-- `Gres (blockMat M) z σ = (Gres M z σ)` read on the block-product index (pattern: private
`expInv_Gres_submatrix`, `Evolution/ExpInv.lean:116`). -/
private theorem lemDecCalEwG_Gres_blockMat (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (s : Bool) :
    Gres (blockMat d L W M) z s =
      (Gres M z s).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold Gres blockMat
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
      w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - w • 1).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    simp [Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]

private theorem lemDecCalEwG_greenBlk_apply (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (σ : Bool) (p q : Vtx d L W) :
    greenBlk d L W E u M σ p q =
      Gres M (zt E u) σ ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm q) := by
  unfold greenBlk
  rw [lemDecCalEwG_Gres_blockMat]
  rfl

/-- The block label of the fine index of a block-product index `p` is `p.1`. -/
private theorem lemDecCalEwG_split_symm_fst (p : Vtx d L W) :
    (split d L W ((splitEquiv d L W).symm p)).1 = p.1 := by
  have h : split d L W ((splitEquiv d L W).symm p) = p := (splitEquiv d L W).apply_symm_apply p
  rw [h]

/-- The symmetric entry bound `max(|G(+)_{pq}|, |G(+)_{qp}|)` (`wG2D:90`). -/
private def fG (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p q : Vtx d L W) : ℝ :=
  max ‖greenBlk d L W E u M true p q‖ ‖greenBlk d L W E u M true q p‖

private theorem fG_comm (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p q : Vtx d L W) :
    fG E u M p q = fG E u M q p := max_comm _ _

private theorem fG_nonneg (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p q : Vtx d L W) :
    0 ≤ fG E u M p q := le_max_of_le_left (norm_nonneg _)

private theorem fG_sq_le {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ} {p q : Vtx d L W}
    {c : ℝ} (h1 : ‖greenBlk d L W E u M true p q‖ ^ 2 ≤ c)
    (h2 : ‖greenBlk d L W E u M true q p‖ ^ 2 ≤ c) : fG E u M p q ^ 2 ≤ c := by
  unfold fG
  rcases le_total ‖greenBlk d L W E u M true p q‖ ‖greenBlk d L W E u M true q p‖ with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

/-- `|G(σ)_{pq}| ≤ fG p q` for both signs (`G(−) = G(+)ᴴ` for Hermitian `M`, `wG2D:108`). -/
private theorem norm_Gres_blockMat_le_fG {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : M.IsHermitian) (σ : Bool) (p q : Vtx d L W) :
    ‖Gres (blockMat d L W M) (zt E u) σ p q‖ ≤ fG E u M p q := by
  cases σ
  · have hHb : (blockMat d L W M).IsHermitian := hH.submatrix _
    have hG := lemDecCalEwG_Gres_false hHb (zt E u)
    have hfalse : Gres (blockMat d L W M) (zt E u) false p q =
        star (Gres (blockMat d L W M) (zt E u) true q p) := by
      have := congrFun (congrFun hG p) q
      simpa [Matrix.conjTranspose_apply] using this
    rw [hfalse, norm_star]
    exact le_max_right _ _
  · exact le_max_left _ _

end Bridge

section Sz

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- `ℓ_u = 1` for `ilambda² ≤ 1 - u` (`3_5:2287`; the text of the merged `st5_ellT_one`,
`Induction/Step5Cases.lean:84`, which is not in the import closure). -/
private theorem lemDecCalEwG_ellT_one {L : ℕ} {g u : ℝ} (hL : 1 ≤ (L : ℝ)) (hx : g ^ 2 ≤ 1 - u) :
    ellT L g u = 1 := by
  unfold ellT
  have h1 : g / Real.sqrt |1 - u| ≤ 1 := by
    rcases le_or_gt g 0 with hg | hg
    · exact (div_nonpos_of_nonpos_of_nonneg hg (Real.sqrt_nonneg _)).trans zero_le_one
    · have hx0 : 0 < 1 - u := by nlinarith [sq_pos_of_pos hg]
      rw [abs_of_pos hx0]
      have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx0
      rw [div_le_one hs]
      calc g = Real.sqrt (g ^ 2) := (Real.sqrt_sq hg.le).symm
        _ ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt hx
  rw [max_eq_right h1]
  exact min_eq_left hL

private theorem lemDecCalEwG_W_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

private theorem lemDecCalEwG_STblk_symm (p : Vtx d (sz.L n) (sz.W n)) :
    STblk sz n ((splitEquiv d (sz.L n) (sz.W n)).symm p) = p.1 :=
  lemDecCalEwG_split_symm_fst p

private theorem fG_e6 (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n)) :
    fG E u M p q ≤ 2 * Λ := by
  unfold fG
  refine max_le ?_ ?_
  · rw [lemDecCalEwG_greenBlk_apply]; exact LemDecCalE_e6 h true _ _
  · rw [lemDecCalEwG_greenBlk_apply]; exact LemDecCalE_e6 h true _ _

/-- (e7) for `fG` (`wG2D:343`): `fG² ≤ 9^d Λ (W^{-D} + J T(|p-q| - 2))` once
`|p - q|_∞ ≥ ℓ*/8 + 2` (`ℓ_u = 1`). -/
private theorem fG_e7 (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n))
    (hd : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 8 + 2 ≤
      (zdistInf d (sz.L n) (p.1 - q.1) : ℝ)) :
    fG E u M p q ^ 2 ≤ 9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) +
      J * tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (p.1 - q.1) : ℝ) - 2)) := by
  have hell : ellT (sz.L n) (sz.lam n) u = 1 := by
    obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, -⟩ := h
    exact lemDecCalEwG_ellT_one (by exact_mod_cast (sz.three_le_L n).trans' (by norm_num)) hlamu
  have hc := lemDecCalEwG_zdistInf_sub_comm d (sz.L n) p.1 q.1
  have hd' : (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
      ellT (sz.L n) (sz.lam n) u) + 2 ≤ (zdistInf d (sz.L n) (q.1 - p.1) : ℝ) := by
    rw [hell, ← hc]; linarith
  have hd'' : (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
      ellT (sz.L n) (sz.lam n) u) + 2 ≤ (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) := by
    rw [hell]; linarith
  refine fG_sq_le ?_ ?_
  · rw [lemDecCalEwG_greenBlk_apply]
    have := LemDecCalE_e7 h ((splitEquiv d (sz.L n) (sz.W n)).symm p)
      ((splitEquiv d (sz.L n) (sz.W n)).symm q)
      (by rw [lemDecCalEwG_STblk_symm, lemDecCalEwG_STblk_symm]; exact hd')
    rw [lemDecCalEwG_STblk_symm, lemDecCalEwG_STblk_symm, ← hc] at this
    exact this
  · rw [lemDecCalEwG_greenBlk_apply]
    have := LemDecCalE_e7 h ((splitEquiv d (sz.L n) (sz.W n)).symm q)
      ((splitEquiv d (sz.L n) (sz.W n)).symm p)
      (by rw [lemDecCalEwG_STblk_symm, lemDecCalEwG_STblk_symm]; exact hd'')
    rw [lemDecCalEwG_STblk_symm, lemDecCalEwG_STblk_symm] at this
    exact this

/-- (e8) for `fG` (`wG2D:352`): `fG² ≤ 2·9^d Λ K₀ M_u⁻¹ (1 + J/M_u)` for `p ≠ q`. -/
private theorem fG_e8 (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n))
    (hpq : p ≠ q) :
    fG E u M p q ^ 2 ≤ 2 * 9 ^ d * Λ * K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ *
      (1 + J / (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))) := by
  have hne : (splitEquiv d (sz.L n) (sz.W n)).symm p ≠ (splitEquiv d (sz.L n) (sz.W n)).symm q :=
    fun h' => hpq ((splitEquiv d (sz.L n) (sz.W n)).symm.injective h')
  refine fG_sq_le ?_ ?_
  · rw [lemDecCalEwG_greenBlk_apply]; exact (LemDecCalE_e8 h _ _ hne).2
  · rw [lemDecCalEwG_greenBlk_apply]; exact (LemDecCalE_e8 h _ _ (Ne.symm hne)).2

/-- `⟨G̃(σ) E_a⟩` of the model-level vocabulary is the merged `avgErr` (`tr E_a = 1`). -/
private theorem lemDecCalEwG_STavgM_eq_avgErr (σ : Bool) (x : Zd d (sz.L n)) :
    STavgM sz n E u M σ x = avgErr d (sz.L n) (sz.W n) E u M σ x := by
  unfold STavgM STLM loopFine loopM avgErr greenBlk
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul,
    trace_Eblk]
  simp [STmsig, mSigma]

/-- Prefactor (e9) (`wG2D:358`), both signs: `|ℰ^{G̃,(2)}_{σ,a}| ≤ W^d (Λ M_u⁻¹) Σ_y (|𝓛¹_y| + |𝓛²_y|)`
(the column sums of `|S^{(B)}|` are `1`). -/
private theorem EGt_le_pref (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖STEGtM sz n E u M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      (Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
      ∑ y : Zd d (sz.L n), (‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖ +
        ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖) := by
  have hL3 := sz.three_le_L n
  have hA : ∀ (σ' : Bool) (x : Zd d (sz.L n)), ‖STavgM sz n E u M σ' x‖ ≤
      Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := fun σ' x => by
    rw [lemDecCalEwG_STavgM_eq_avgErr]; exact LemDecCalE_e9 h σ' x
  have hSB : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) x y‖ = 1 := by
    intro y
    rw [← sum_norm_SB_row d (sz.L n) (sz.lam n) hL3 y]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show SB d (sz.L n) (sz.lam n) y x = SB d (sz.L n) (sz.lam n) x y from
      congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) x) y]
  set A : ℝ := Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hAdef
  set F : Zd d (sz.L n) → ℝ := fun y => ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖ +
    ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖ with hF
  unfold STEGtM
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hW2 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        (STavgM sz n E u M (σ 0) x * SB d (sz.L n) (sz.lam n) x y *
            STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
          STavgM sz n E u M (σ 1) x * SB d (sz.L n) (sz.lam n) x y *
            STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1])‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          A * (‖SB d (sz.L n) (sz.lam n) x y‖ * F y) := by
        refine mul_le_mul_of_nonneg_left ?_ hW2
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, hF]
        have h1 := hA (σ 0) x
        have h2 := hA (σ 1) x
        have hs := norm_nonneg (SB d (sz.L n) (sz.lam n) x y)
        have hl1 := norm_nonneg (STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1])
        have hl2 := norm_nonneg (STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1])
        have e1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hs hl1)
        have e2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hs hl2)
        calc ‖STavgM sz n E u M (σ 0) x‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
              ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖ +
            ‖STavgM sz n E u M (σ 1) x‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
              ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖
            = ‖STavgM sz n E u M (σ 0) x‖ * (‖SB d (sz.L n) (sz.lam n) x y‖ *
                ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖) +
              ‖STavgM sz n E u M (σ 1) x‖ * (‖SB d (sz.L n) (sz.lam n) x y‖ *
                ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖) := by ring
          _ ≤ A * (‖SB d (sz.L n) (sz.lam n) x y‖ *
                ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖) +
              A * (‖SB d (sz.L n) (sz.lam n) x y‖ *
                ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖) := add_le_add e1 e2
          _ = A * (‖SB d (sz.L n) (sz.lam n) x y‖ *
                (‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖ +
                  ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖)) := by ring
    _ = ((sz.W n : ℕ) : ℝ) ^ d * A * ∑ y : Zd d (sz.L n), F y := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Finset.sum_mul, hSB, one_mul]
        ring

end Sz

end Entries

/-! ## 5. Scale facts and the near bound (`wG2D:435-745`) -/

section Near

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- `log P ≥ 6d log W`, `P = L^d W^{6d}` (as `L ≥ 1`). -/
private theorem lemDecCalEwG_log_P_ge (sz : Sizes d) (n : ℕ) (hW1 : 1 ≤ ((sz.W n : ℕ) : ℝ)) :
    (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) ≤
      Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have h1 : Real.log (((sz.W n : ℕ) : ℝ) ^ (6 * d)) ≤
      Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
    apply Real.log_le_log (by have := lemDecCalEwG_W_pos sz n; positivity)
    have : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
    nlinarith [pow_pos (lemDecCalEwG_W_pos sz n) (6 * d)]
  rw [Real.log_pow] at h1
  push_cast at h1
  exact h1

/-- The scale facts of `E2Hyp` used below: `1 < W`, `1 ≤ M_u ≤ W^d`, `log W ≥ 4`, `ℓ* ≥ 8`. -/
private theorem facts0 (hE : E2Hyp sz n E u D Λ K₀ J M) :
    (1 : ℝ) < ((sz.W n : ℕ) : ℝ) ∧ 1 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ∧
      ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.W n : ℕ) : ℝ) ^ d ∧
      4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
      8 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨hW1, -⟩ := LemDecCalE_floor hE
  have h2 := LemDecCalE_e2 hE
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, -⟩ := hE
  have h48 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpow : (4 : ℝ) ^ ((3 : ℝ) / 2) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
  exact ⟨hW1, h2.1, h2.2, hlog, by linarith⟩

/-- The scale facts used below: those of `facts0` and `W^{-D} ≤ (P⁻¹)²` (the floor of `E2HypWG`,
`P = L^d W^{6d}`). -/
private theorem facts (h : E2HypWG sz n E u D Λ K₀ J M) :
    (1 : ℝ) < ((sz.W n : ℕ) : ℝ) ∧ 1 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ∧
      ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.W n : ℕ) : ℝ) ^ d ∧
      4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
      8 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ∧
      ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
        ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) ^ 2 := by
  obtain ⟨hE, hfl, -⟩ := h
  obtain ⟨hW1, hM1, hMW, hlog, hstar⟩ := facts0 hE
  have hW0 := lemDecCalEwG_W_pos sz n
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
  have hP : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) := by positivity
  refine ⟨hW1, hM1, hMW, hlog, hstar, ?_⟩
  rw [Real.rpow_neg hW0.le, inv_pow]
  exact inv_anti₀ (by positivity) hfl

/-- The far edge of the near case (`wG2D:483`): beyond `R = 4 (log P)²`,
`fG ≤ 5·9^d Λ J P⁻¹` ((e7), the floor, `√(R - 2) ≥ 2 log P - 1`). -/
private theorem fG_near_far (h : E2HypWG sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n))
    (hd : 4 * Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 <
      (zdistInf d (sz.L n) (p.1 - q.1) : ℝ)) :
    fG E u M p q ≤ 5 * 9 ^ d * Λ * J *
      (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hlgP := lemDecCalEwG_log_P_ge sz n hW1.le
  obtain ⟨hE, -, -⟩ := h
  have h7 := fG_e7 hE p q
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := hE
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
  set Z : ℝ := ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) with hZ
  have hZ0 : 0 < Z := by positivity
  set Lg : ℝ := Real.log Z with hLg
  set X : ℝ := Z⁻¹ with hX
  have hX0 : 0 < X := inv_pos.2 hZ0
  set x : ℝ := (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) with hx
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hLg72 : 72 ≤ Lg := by
    have h6d : (18 : ℝ) ≤ 6 * (d : ℝ) := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
      linarith
    nlinarith
  have hlogW : Real.log ((sz.W n : ℕ) : ℝ) ≤ Lg := by
    have : Real.log ((sz.W n : ℕ) : ℝ) ≤ (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) := by
      nlinarith
    linarith
  -- `ℓ*/8 + 2 ≤ 4 Lg²`
  have hstarR : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 8 + 2 ≤ 4 * Lg ^ 2 := by
    have h1 : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_two] at h1
    have h2 : Real.log ((sz.W n : ℕ) : ℝ) ^ 2 ≤ Lg ^ 2 := pow_le_pow_left₀ (by linarith) hlogW 2
    have h5 : 72 * 72 ≤ Lg ^ 2 := by
      rw [sq]; exact mul_le_mul hLg72 hLg72 (by norm_num) (by linarith)
    linarith
  have hd' : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 8 + 2 ≤ x := by linarith
  have h7' := h7 hd'
  -- the tail at `x - 2`
  have hT1 : tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2) ≤
      tailTD d ((sz.W n : ℕ) : ℝ) u D (4 * Lg ^ 2 - 2) :=
    LemDecCalE_tailT_anti (by linarith)
  have hsq : 2 * Lg - 1 ≤ Real.sqrt (4 * Lg ^ 2 - 2) := by
    rw [Real.le_sqrt (by linarith) (by nlinarith)]
    nlinarith
  have hexpZ : Real.exp (-Lg) = X := by
    rw [Real.exp_neg, hLg, Real.exp_log hZ0]
  have hexp : Real.exp (-Real.sqrt (4 * Lg ^ 2 - 2)) ≤ Real.exp 1 * X ^ 2 := by
    calc Real.exp (-Real.sqrt (4 * Lg ^ 2 - 2)) ≤ Real.exp (1 + -Lg + -Lg) :=
          Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 * X ^ 2 := by rw [Real.exp_add, Real.exp_add, hexpZ]; ring
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hM1)
  have hxu : 0 < 1 - u := by linarith
  have hT2 : tailTD d ((sz.W n : ℕ) : ℝ) u D (4 * Lg ^ 2 - 2) ≤ 4 * X ^ 2 := by
    unfold tailTD
    rw [abs_of_pos hxu]
    have h0 : 0 ≤ Real.exp (-Real.sqrt (4 * Lg ^ 2 - 2)) := (Real.exp_pos _).le
    have h1 : m ^ 2 * Real.exp (-Real.sqrt (4 * Lg ^ 2 - 2)) ≤ 1 * (Real.exp 1 * X ^ 2) :=
      mul_le_mul hm2 hexp h0 zero_le_one
    have : Real.exp 1 * X ^ 2 ≤ 3 * X ^ 2 := mul_le_mul_of_nonneg_right he3 (by positivity)
    linarith
  have hsq2 : fG E u M p q ^ 2 ≤ 5 * 9 ^ d * Λ * J * X ^ 2 := by
    have hJ0 : 0 ≤ J := by linarith
    have e1 := mul_le_mul_of_nonneg_left (hT1.trans hT2) hJ0
    have e2 : X ^ 2 ≤ J * X ^ 2 := le_mul_of_one_le_left (by positivity) hJ1
    have hΛ0 : 0 ≤ Λ := by linarith
    have h9d : (0 : ℝ) ≤ 9 ^ d := by positivity
    have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 9 ^ d * Λ)
    calc fG E u M p q ^ 2 ≤ 9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) + J * tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2)) := h7'
      _ ≤ 9 ^ d * Λ * (X ^ 2 + J * (4 * X ^ 2)) := by gcongr
      _ = 9 ^ d * Λ * X ^ 2 + 4 * (9 ^ d * Λ * (J * X ^ 2)) := by ring
      _ ≤ 9 ^ d * Λ * (J * X ^ 2) + 4 * (9 ^ d * Λ * (J * X ^ 2)) := by linarith
      _ = 5 * 9 ^ d * Λ * J * X ^ 2 := by ring
  have hc1 : 1 ≤ 5 * 9 ^ d * Λ * J := by
    have h9d : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
    have h1 : 1 ≤ 9 ^ d * (Λ * J) :=
      one_le_mul_of_one_le_of_one_le h9d (one_le_mul_of_one_le_of_one_le hΛ hJ1)
    have e : 5 * 9 ^ d * Λ * J = 5 * (9 ^ d * (Λ * J)) := by ring
    rw [e]; linarith
  have hb : 0 ≤ 5 * 9 ^ d * Λ * J * X := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ J := by linarith
    positivity
  rw [← pow_le_pow_iff_left₀ (fG_nonneg E u M p q) hb (two_ne_zero)]
  refine hsq2.trans ?_
  have : 5 * 9 ^ d * Λ * J * X ^ 2 ≤ (5 * 9 ^ d * Λ * J) ^ 2 * X ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_left hc1 (by linarith : (0 : ℝ) ≤ 5 * 9 ^ d * Λ * J)
    rw [sq]; linarith
  calc 5 * 9 ^ d * Λ * J * X ^ 2 ≤ (5 * 9 ^ d * Λ * J) ^ 2 * X ^ 2 := this
    _ = (5 * 9 ^ d * Λ * J * X) ^ 2 := by ring

/-- Both three-loops of `ℰ^{G̃,(2)}` are bounded by the triangle sum at `(a₁, y, a₂)`
(`wG2D:412`; every `σ`, the `tri` bound is sign-free). -/
private theorem loops_le_tri (hH : M.IsHermitian) (σ : Fin 2 → Bool) (a₁ a₂ y : Zd d (sz.L n)) :
    ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a₁, a₂]‖ +
        ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a₁, y, a₂]‖ ≤ 2 * tri (fG E u M) a₁ y a₂ := by
  have hf : ∀ (s : Bool) (p q : Vtx d (sz.L n) (sz.W n)),
      ‖Gres (blockMat d (sz.L n) (sz.W n) M) (zt E u) s p q‖ ≤ fG E u M p q :=
    fun s p q => norm_Gres_blockMat_le_fG hH s p q
  have h1 : ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a₁, a₂]‖ ≤ tri (fG E u M) y a₁ a₂ :=
    norm_loop3_le_tri hf (σ 0) (σ 0) (σ 1) y a₁ a₂
  have h2 : ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a₁, y, a₂]‖ ≤ tri (fG E u M) a₁ y a₂ :=
    norm_loop3_le_tri hf (σ 0) (σ 1) (σ 1) a₁ y a₂
  rw [tri_swap (fG_comm E u M) a₁ y a₂] at h1
  linarith

/-- **Near sum** (`wG2D:602`): `Σ_y (|𝓛¹_y| + |𝓛²_y|) ≤ 2·9^d Λ (log P)^{2d} M_u⁻² + 40·9^d Λ³ J W^{-6d}`
(close `y` by the three-loop clause, far `y` by `fG_near_far`; `L^d P⁻¹ = W^{-6d}`; no `J ≤ W`). -/
private theorem near_sum (h : E2HypWG sz n E u D Λ K₀ J M) (σ : Fin 2 → Bool)
    (a₁ a₂ : Zd d (sz.L n)) :
    ∑ y : Zd d (sz.L n), (‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a₁, a₂]‖ +
        ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a₁, y, a₂]‖) ≤
      2 * 9 ^ d * Λ *
          Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ (2 * d) *
          ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 +
        40 * 9 ^ d * Λ ^ 3 * J * (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hlgP := lemDecCalEwG_log_P_ge sz n hW1.le
  have hfar := fG_near_far h
  obtain ⟨hE, -, hclose⟩ := h
  have h6 := fG_e6 hE
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6', h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := hE
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
  set Z : ℝ := ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) with hZ
  have hZ0 : 0 < Z := by positivity
  set Lg : ℝ := Real.log Z with hLg
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  set X : ℝ := Z⁻¹ with hX
  set R : ℝ := 4 * Lg ^ 2 with hR
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hX0 : 0 ≤ X := (inv_pos.2 hZ0).le
  have hm0 : 0 ≤ m := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hLg72 : 72 ≤ Lg := by
    have h6d : (18 : ℝ) ≤ 6 * (d : ℝ) := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
      linarith
    nlinarith
  set F : Zd d (sz.L n) → ℝ := fun y => ‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a₁, a₂]‖ +
    ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a₁, y, a₂]‖ with hF
  set c : ℝ := 20 * 9 ^ d * Λ ^ 3 * J * X with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ y : Zd d (sz.L n), F y ≤
      (if (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ R then 2 * (Λ * m ^ 2) else 0) + 2 * c := by
    intro y
    by_cases hy : (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ R
    · simp only [hy, ↓reduceIte]
      have e1 := hclose ![σ 0, σ 0, σ 1] ![y, a₁, a₂]
      have e2 := hclose ![σ 0, σ 1, σ 1] ![a₁, y, a₂]
      simp only [hF]
      linarith
    · simp only [hy, ↓reduceIte, zero_add]
      refine (loops_le_tri hH σ a₁ a₂ y).trans ?_
      have ht : tri (fG E u M) a₁ y a₂ ≤ c := by
        refine tri_le_of_pt fun p q r hp hq hr => ?_
        have f1 := h6 p q
        have f3 := h6 r p
        have f2 : fG E u M q r ≤ 5 * 9 ^ d * Λ * J * X := by
          apply hfar q r
          rw [hq, hr]
          exact not_le.1 hy
        have n1 := fG_nonneg E u M p q
        have n2 := fG_nonneg E u M q r
        have n3 := fG_nonneg E u M r p
        calc fG E u M p q * fG E u M q r * fG E u M r p
            ≤ (2 * Λ) * (5 * 9 ^ d * Λ * J * X) * (2 * Λ) :=
              mul_le_mul (mul_le_mul f1 f2 n2 (by linarith)) f3 n3
                (mul_nonneg (by linarith) (by positivity))
          _ = c := by rw [hc]; ring
      linarith
  have hsum : ∑ y : Zd d (sz.L n), F y ≤
      ((Finset.univ.filter fun y : Zd d (sz.L n) => (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ R).card : ℝ) *
          (2 * (Λ * m ^ 2)) + ((sz.L n : ℕ) : ℝ) ^ d * (2 * c) := by
    refine (Finset.sum_le_sum fun y _ => hpt y).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp [Finset.card_univ, ZMod.card]
  -- the count
  have hcard := LemDecCalE_e10a a₁ R (by positivity)
  have hLg2 : 1 ≤ Lg ^ 2 := by nlinarith
  have hR9 : (2 * R + 1) ^ d ≤ 9 ^ d * Lg ^ (2 * d) := by
    have h1 : 2 * R + 1 ≤ 9 * Lg ^ 2 := by rw [hR]; linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 d
    calc (2 * R + 1) ^ d ≤ (9 * Lg ^ 2) ^ d := h2
      _ = 9 ^ d * Lg ^ (2 * d) := by rw [mul_pow, ← pow_mul]
  have hcardP : ((Finset.univ.filter fun y : Zd d (sz.L n) =>
      (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ R).card : ℝ) * (2 * (Λ * m ^ 2)) ≤
      2 * 9 ^ d * Λ * Lg ^ (2 * d) * m ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_right (hcard.trans hR9)
      (by positivity : (0 : ℝ) ≤ 2 * (Λ * m ^ 2))
    have e2 : 9 ^ d * Lg ^ (2 * d) * (2 * (Λ * m ^ 2)) = 2 * 9 ^ d * Λ * Lg ^ (2 * d) * m ^ 2 := by
      ring
    linarith
  have hfarP : ((sz.L n : ℕ) : ℝ) ^ d * (2 * c) =
      40 * 9 ^ d * Λ ^ 3 * J * (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ := by
    rw [hc, hX, hZ]
    have : ((sz.L n : ℕ) : ℝ) ^ d ≠ 0 := by positivity
    have : ((sz.W n : ℕ) : ℝ) ^ (6 * d) ≠ 0 := by positivity
    field_simp
    ring
  calc ∑ y : Zd d (sz.L n), F y ≤ _ := hsum
    _ ≤ 2 * 9 ^ d * Λ * Lg ^ (2 * d) * m ^ 2 +
        40 * 9 ^ d * Λ ^ 3 * J * (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ := by
        rw [← hfarP]; linarith

end Near

/-! ## 6. The far bound (`wG2D:750-1185`) -/

section Far

/-- `W^{-D} ≤ T_{u,D}(x)` (`wG2D:750`). -/
private theorem WD_le_tailTD (d : ℕ) (W u D x : ℝ) : W ^ (-D) ≤ tailTD d W u D x := by
  unfold tailTD
  have : 0 ≤ ((W ^ d * |1 - u|)⁻¹) ^ 2 * Real.exp (-Real.sqrt x) := by positivity
  linarith

/-- `T_{u,D}(x) ≤ e^{(log W)^{3/4}} T_{u,D}(dd)` for `x ≥ dd - ℓ*` (`wG2D:756`, `LemDecCalE_e4c` with
`C = 1`). -/
private theorem tail_le_Y {d : ℕ} {W u D : ℝ} (hW : 1 ≤ W) {dd x : ℝ}
    (hx : dd - Real.log W ^ ((3 : ℝ) / 2) ≤ x) :
    tailTD d W u D x ≤ Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * tailTD d W u D dd := by
  have h1 := LemDecCalE_tailT_anti (d := d) (W := W) (u := u) (D := D) hx
  have h2 := LemDecCalE_e4c (d := d) (W := W) (u := u) (D := D) (C := 1) hW zero_le_one dd
  simp only [Real.sqrt_one, one_mul] at h2
  exact h1.trans h2

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- A long edge of the far case (`wG2D:765`): `fG² ≤ 2·9^d Λ J e^Y T(dd)` if its length `x` has
`x ≥ ℓ*/8 + 2` and `x - 2 ≥ dd - ℓ*` ((e7), `tail_le_Y`). -/
private theorem fG_long (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n)) {dd x : ℝ}
    (hx : (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) = x)
    (h1 : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 8 + 2 ≤ x)
    (h2 : dd - Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ x - 2) :
    fG E u M p q ^ 2 ≤ 2 * 9 ^ d * Λ * J * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
      tailTD d ((sz.W n : ℕ) : ℝ) u D dd := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar⟩ := facts0 h
  have h7 := fG_e7 h p q (by rw [hx]; exact h1)
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := h
  rw [hx] at h7
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
  set eY := Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with heYdef
  set T := tailTD d ((sz.W n : ℕ) : ℝ) u D dd with hTdef
  have hT0 : 0 ≤ T := tailTD_nonneg hW0
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hTY := tail_le_Y (d := d) (u := u) (D := D) hW1.le h2
  have hWT := WD_le_tailTD d ((sz.W n : ℕ) : ℝ) u D dd
  have hJY : 1 ≤ J * eY := one_le_mul_of_one_le_of_one_le hJ1 heY
  have e1 : T ≤ J * eY * T := le_mul_of_one_le_left hT0 hJY
  have e2 : J * tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2) ≤ J * (eY * T) :=
    mul_le_mul_of_nonneg_left hTY (by linarith)
  have hΛ0 : 0 ≤ 9 ^ d * Λ := by positivity
  calc fG E u M p q ^ 2 ≤ 9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) +
        J * tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2)) := h7
    _ ≤ 9 ^ d * Λ * (J * eY * T + J * eY * T) := by
        apply mul_le_mul_of_nonneg_left _ hΛ0
        have : J * (eY * T) = J * eY * T := by ring
        linarith
    _ = 2 * 9 ^ d * Λ * J * eY * T := by ring

/-- An edge of length `x ≥ ℓ*/8 + 2` (`wG2D:795`): `fG ≤ √(9^{d+1} Λ J) √T(x)` ((e7), shift by `2`). -/
private theorem fG_sqrt (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n)) {x : ℝ}
    (hx : (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) = x)
    (h1 : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 8 + 2 ≤ x) :
    fG E u M p q ≤ Real.sqrt (9 ^ (d + 1) * Λ * J) *
      Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D x) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar⟩ := facts0 h
  have h7 := fG_e7 h p q (by rw [hx]; exact h1)
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := h
  rw [hx] at h7
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
  set T := tailTD d ((sz.W n : ℕ) : ℝ) u D x with hTdef
  have hT0 : 0 ≤ T := tailTD_nonneg hW0
  have hsh := LemDecCalE_tailT_shift (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D)
    hW0 (c := 2) (by norm_num) x
  have he8 : Real.exp (Real.sqrt 2) ≤ 8 := by
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]; norm_num
    have h1' : Real.exp (Real.sqrt 2) ≤ Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have h2' := Real.exp_one_lt_d9
    have h3' : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have hsh8 : tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2) ≤ 8 * T :=
    hsh.trans (mul_le_mul_of_nonneg_right he8 hT0)
  have hWT := WD_le_tailTD d ((sz.W n : ℕ) : ℝ) u D x
  have hJT : T ≤ J * T := le_mul_of_one_le_left hT0 hJ1
  have hsq : fG E u M p q ^ 2 ≤ 9 ^ (d + 1) * Λ * J * T := by
    have e2 : J * tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2) ≤ J * (8 * T) :=
      mul_le_mul_of_nonneg_left hsh8 (by linarith)
    have hΛ0 : 0 ≤ 9 ^ d * Λ := by positivity
    calc fG E u M p q ^ 2 ≤ 9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) +
          J * tailTD d ((sz.W n : ℕ) : ℝ) u D (x - 2)) := h7
      _ ≤ 9 ^ d * Λ * (J * T + J * (8 * T)) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0
          linarith
      _ = 9 ^ (d + 1) * Λ * J * T := by ring
  have hc0 : 0 ≤ 9 ^ (d + 1) * Λ * J := by
    have : 0 ≤ Λ := by linarith
    have : 0 ≤ J := by linarith
    positivity
  rw [← Real.sqrt_mul hc0, ← Real.sqrt_sq (fG_nonneg E u M p q)]
  exact Real.sqrt_le_sqrt hsq

/-- `m ≤ 1` and `m ≤ √m` for `m = M_u⁻¹`, `M_u ≥ 1`. -/
private theorem lemDecCalEwG_m_le_sqrt {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) : m ≤ Real.sqrt m := by
  rw [Real.le_sqrt hm0 hm0, sq]
  exact mul_le_of_le_one_left hm0 hm1

/-- An off-diagonal entry (`wG2D:839`, with `√J` kept: the source of `J^{3/2}` instead of `J²`):
`fG ≤ 2·3^d Λ K₀ √J √(M_u⁻¹)` ((e8)). -/
private theorem fG_off (h : E2Hyp sz n E u D Λ K₀ J M) (p q : Vtx d (sz.L n) (sz.W n)) (hpq : p ≠ q) :
    fG E u M p q ≤ 2 * 3 ^ d * Λ * K₀ * Real.sqrt J *
      Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar⟩ := facts0 h
  have h8 := fG_e8 h p q hpq
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := h
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hJM : J / (((sz.W n : ℕ) : ℝ) ^ d * (1 - u)) = J * m := by rw [hm, div_eq_mul_inv]
  rw [hJM] at h8
  have hJm : 1 + J * m ≤ 2 * J := by
    have : J * m ≤ J * 1 := mul_le_mul_of_nonneg_left hm1 (by linarith)
    linarith
  have hΛK : 1 ≤ Λ * K₀ := one_le_mul_of_one_le_of_one_le hΛ hK
  have hJ0 : 0 ≤ J := by linarith
  have hsJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ0
  have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
  have h9d : (3 : ℝ) ^ d * 3 ^ d = 9 ^ d := by rw [← mul_pow]; norm_num
  have hsq : fG E u M p q ^ 2 ≤ (2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m) ^ 2 := by
    have e0 : 0 ≤ 2 * 9 ^ d * Λ * K₀ * m := by
      have : 0 ≤ Λ := by linarith
      have : 0 ≤ K₀ := by linarith
      positivity
    have e1 := mul_le_mul_of_nonneg_left hJm e0
    have e2 : (2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m) ^ 2 =
        4 * 9 ^ d * (Λ * K₀) ^ 2 * J * m := by
      calc (2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m) ^ 2
          = 4 * ((3 : ℝ) ^ d * 3 ^ d) * (Λ * K₀) ^ 2 * Real.sqrt J ^ 2 * Real.sqrt m ^ 2 := by ring
        _ = 4 * 9 ^ d * (Λ * K₀) ^ 2 * J * m := by rw [h9d, hsJ, hsm]
    have e3 : Λ * K₀ ≤ (Λ * K₀) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by linarith) hΛK
    have e4 := mul_le_mul_of_nonneg_right e3 (by positivity : (0 : ℝ) ≤ 4 * 9 ^ d * J * m)
    rw [e2]
    calc fG E u M p q ^ 2 ≤ 2 * 9 ^ d * Λ * K₀ * m * (1 + J * m) := h8
      _ ≤ 2 * 9 ^ d * Λ * K₀ * m * (2 * J) := e1
      _ = Λ * K₀ * (4 * 9 ^ d * J * m) := by ring
      _ ≤ (Λ * K₀) ^ 2 * (4 * 9 ^ d * J * m) := e4
      _ = 4 * 9 ^ d * (Λ * K₀) ^ 2 * J * m := by ring
  have hb : 0 ≤ 2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by
    have : 0 ≤ Λ * K₀ := by linarith
    have : 0 ≤ Real.sqrt J := Real.sqrt_nonneg J
    have : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
    positivity
  exact (pow_le_pow_iff_left₀ (fG_nonneg E u M p q) hb two_ne_zero).1 hsq

/-- The block average (`wG2D:880`): `avg ≤ 4·3^d Λ K₀ √J √(M_u⁻¹)`. -/
private theorem avg_le_hyp (h : E2Hyp sz n E u D Λ K₀ J M) (c c' : Zd d (sz.L n)) :
    avg (fG E u M) c c' ≤ 4 * 3 ^ d * Λ * K₀ * Real.sqrt J *
      Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar⟩ := facts0 h
  have h6 := fG_e6 h
  have hoff := fG_off h
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6', h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := h
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hsm := lemDecCalEwG_m_le_sqrt hm0 hm1
  have hsJ1 : 1 ≤ Real.sqrt J := by
    rw [Real.le_sqrt zero_le_one (by linarith)]; linarith
  have hWm : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Real.sqrt m := (inv_anti₀ hMpos hMW).trans hsm
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have hΛK : 1 ≤ 3 ^ d * K₀ := one_le_mul_of_one_le_of_one_le h3d hK
  have hΛ0 : 0 ≤ Λ := by linarith
  have hA0 : 0 ≤ 2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by
    have : 0 ≤ Real.sqrt J := Real.sqrt_nonneg J
    have : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
    have : 0 ≤ K₀ := by linarith
    positivity
  have hav := avg_le (fG_nonneg E u M) h6 hoff hA0 c c'
  have hs0' : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have e1 : 2 * Λ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 2 * Λ * Real.sqrt m :=
    mul_le_mul_of_nonneg_left hWm (by linarith)
  have e2 : 2 * Λ * Real.sqrt m ≤ 2 * Λ * Real.sqrt m * Real.sqrt J :=
    le_mul_of_one_le_right (by positivity) hsJ1
  have e3 : 2 * Λ * Real.sqrt m * Real.sqrt J ≤
      2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by
    have : 0 ≤ Λ * Real.sqrt J * Real.sqrt m := by positivity
    nlinarith
  calc avg (fG E u M) c c' ≤ 2 * Λ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
        2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := hav
    _ ≤ 2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m +
        2 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by linarith
    _ = 4 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by ring

/-- AM–GM: `x² ≤ B`, `y² ≤ B` give `x y ≤ B`. -/
private theorem lemDecCalEwG_mul_le_of_sq_le {x y B : ℝ} (h1 : x ^ 2 ≤ B) (h2 : y ^ 2 ≤ B) :
    x * y ≤ B := by
  nlinarith [sq_nonneg (x - y)]

/-- The far case, one `y` (`wG2D:921`): `y` within `ℓ*/2` of `a₁` (edge `a₁`–`y` averaged), within `ℓ*/2`
of `a₂` (edge `y`–`a₂` averaged), or far from both (three long edges, `k³ = (9^{d+1} Λ J)^{3/2}`
kept: the source of `J^{3/2}` instead of RBM2D's `J²`, `wG2D:1107`). -/
private theorem far_pt (h : E2Hyp sz n E u D Λ K₀ J M) (a₁ a₂ y : Zd d (sz.L n))
    (hd : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)) :
    tri (fG E u M) a₁ y a₂ ≤
      (if (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 2 then
          2 * 9 ^ d * Λ * J * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) *
              (4 * 3 ^ d * Λ * K₀ * Real.sqrt J *
                Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)) else 0) +
        (if (zdistInf d (sz.L n) (a₂ - y) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 2 then
          2 * 9 ^ d * Λ * J * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
            tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) *
              (4 * 3 ^ d * Λ * K₀ * Real.sqrt J *
                Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)) else 0) +
          Real.sqrt (9 ^ (d + 1) * Λ * J) ^ 3 *
            (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)) *
              (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) *
                Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ)))) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar⟩ := facts0 h
  have hlong := fG_long h
  have hsqrt := fG_sqrt h
  have havg := avg_le_hyp h
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := h
  have hf0 : ∀ p q : Vtx d (sz.L n) (sz.W n), 0 ≤ fG E u M p q := fG_nonneg E u M
  have hfs : ∀ p q : Vtx d (sz.L n) (sz.W n), fG E u M p q = fG E u M q p := fG_comm E u M
  set ls := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hls
  set dd : ℝ := (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) with hddef
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  set eY := Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with heYdef
  have hT0 : ∀ x, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D x := fun x =>
    tailTD_nonneg (by linarith)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hK0 : 0 ≤ K₀ := by linarith
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hsm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  set B1 : ℝ := 2 * 9 ^ d * Λ * J * eY * tailTD d ((sz.W n : ℕ) : ℝ) u D dd with hB1
  have hB10 : 0 ≤ B1 := by
    have := hT0 dd
    have : 0 ≤ eY := by linarith
    positivity
  set X1 : ℝ := B1 * (4 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m) with hX1
  have hX10 : 0 ≤ X1 := by
    have : 0 ≤ 4 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by positivity
    positivity
  set k : ℝ := Real.sqrt (9 ^ (d + 1) * Λ * J) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hsT0 : ∀ y' : Zd d (sz.L n),
      0 ≤ Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y') : ℝ)) *
        Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y' - a₂) : ℝ)) :=
    fun y' => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the edge `a₂ – a₁` of length `dd`
  have hda : ∀ p q : Vtx d (sz.L n) (sz.W n), p.1 = a₂ → q.1 = a₁ →
      (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) = dd := by
    intro p q hp hq
    rw [hp, hq, lemDecCalEwG_zdistInf_sub_comm]
  have hd1 : ls / 8 + 2 ≤ dd := by linarith
  have htri := lemDecCalEwG_zdistInf_tri_real d (sz.L n) a₁ y a₂
  have hi1 : 0 ≤ (if (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ ls / 2 then X1 else 0) := by
    split_ifs <;> first | exact hX10 | exact le_rfl
  have hi2 : 0 ≤ (if (zdistInf d (sz.L n) (a₂ - y) : ℝ) ≤ ls / 2 then X1 else 0) := by
    split_ifs <;> first | exact hX10 | exact le_rfl
  by_cases hA : (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ ls / 2
  · -- `y` near `a₁`: the edge `a₁ – y` is averaged
    have hyy : (zdistInf d (sz.L n) (y - a₂) : ℝ) ≥ dd - ls / 2 := by linarith
    have ht : tri (fG E u M) a₁ y a₂ ≤ B1 * avg (fG E u M) a₁ y := by
      refine tri_le_avg12 hf0 fun p q r hp hq hr => ?_
      have e1 := hlong p q (dd := dd) (hda p q hp hq) hd1 (by linarith)
      have hx : (zdistInf d (sz.L n) (r.1 - p.1) : ℝ) = (zdistInf d (sz.L n) (y - a₂) : ℝ) := by
        rw [hr, hp]
      have e2 := hlong r p (dd := dd) hx (by linarith) (by linarith)
      exact lemDecCalEwG_mul_le_of_sq_le e1 e2
    have ha := mul_le_mul_of_nonneg_left (havg a₁ y) hB10
    simp only [hA, ↓reduceIte]
    have hk3 : 0 ≤ k ^ 3 * (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
        (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) *
          Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ)))) :=
      mul_nonneg (pow_nonneg hk0 3) (mul_nonneg (Real.sqrt_nonneg _) (hsT0 y))
    linarith
  · by_cases hB : (zdistInf d (sz.L n) (a₂ - y) : ℝ) ≤ ls / 2
    · -- `y` near `a₂`: the edge `y – a₂` is averaged
      have hB' : (zdistInf d (sz.L n) (y - a₂) : ℝ) ≤ ls / 2 := by
        rw [lemDecCalEwG_zdistInf_sub_comm]; exact hB
      have hyy : (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≥ dd - ls / 2 := by linarith
      have ht : tri (fG E u M) a₁ y a₂ ≤ B1 * avg (fG E u M) a₂ y := by
        refine tri_le_avg23 hf0 hfs fun p q r hp hq hr => ?_
        have e1 := hlong p q (dd := dd) (hda p q hp hq) hd1 (by linarith)
        have hx : (zdistInf d (sz.L n) (q.1 - r.1) : ℝ) = (zdistInf d (sz.L n) (a₁ - y) : ℝ) := by
          rw [hq, hr]
        have e2 := hlong q r (dd := dd) hx (by linarith) (by linarith)
        exact lemDecCalEwG_mul_le_of_sq_le e1 e2
      have ha := mul_le_mul_of_nonneg_left (havg a₂ y) hB10
      simp only [hA, hB, ↓reduceIte, zero_add]
      have hk3 : 0 ≤ k ^ 3 * (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
          (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) *
            Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ)))) :=
        mul_nonneg (pow_nonneg hk0 3) (mul_nonneg (Real.sqrt_nonneg _) (hsT0 y))
      linarith
    · -- `y` far from both: three long edges
      have hA' : ls / 2 < (zdistInf d (sz.L n) (a₁ - y) : ℝ) := not_le.1 hA
      have hB' : ls / 2 < (zdistInf d (sz.L n) (y - a₂) : ℝ) := by
        rw [lemDecCalEwG_zdistInf_sub_comm]; exact not_le.1 hB
      have ht : tri (fG E u M) a₁ y a₂ ≤ k ^ 3 *
          (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
            (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) *
              Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ)))) := by
        refine tri_le_of_pt fun p q r hp hq hr => ?_
        have e1 := hsqrt p q (hda p q hp hq) hd1
        have hx2 : (zdistInf d (sz.L n) (q.1 - r.1) : ℝ) = (zdistInf d (sz.L n) (a₁ - y) : ℝ) := by
          rw [hq, hr]
        have e2 := hsqrt q r hx2 (by linarith)
        have hx3 : (zdistInf d (sz.L n) (r.1 - p.1) : ℝ) = (zdistInf d (sz.L n) (y - a₂) : ℝ) := by
          rw [hr, hp]
        have e3 := hsqrt r p hx3 (by linarith)
        have n1 := hf0 p q
        have n2 := hf0 q r
        have n3 := hf0 r p
        have s1 := Real.sqrt_nonneg (tailTD d ((sz.W n : ℕ) : ℝ) u D dd)
        have s2 := Real.sqrt_nonneg
          (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ))
        have s3 := Real.sqrt_nonneg
          (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ))
        calc fG E u M p q * fG E u M q r * fG E u M r p
            ≤ (k * Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd)) *
                (k * Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D
                  (zdistInf d (sz.L n) (a₁ - y) : ℝ))) *
                (k * Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D
                  (zdistInf d (sz.L n) (y - a₂) : ℝ))) :=
              mul_le_mul (mul_le_mul e1 e2 n2 (mul_nonneg hk0 s1)) e3 n3
                (mul_nonneg (mul_nonneg hk0 s1) (mul_nonneg hk0 s2))
          _ = k ^ 3 * (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
                (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) *
                  Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D
                    (zdistInf d (sz.L n) (y - a₂) : ℝ)))) := by ring
      simp only [hA, hB, ↓reduceIte, zero_add]
      exact ht

/-- `k³ = (9^{d+1} Λ J)^{3/2} ≤ 27^{d+1} Λ² J √J` (the `J^{3/2}` of `far_pt`). -/
private theorem lemDecCalEwG_k_cube_le {Λ J : ℝ} (hΛ : 1 ≤ Λ) (hJ : 1 ≤ J) (d : ℕ) :
    Real.sqrt (9 ^ (d + 1) * Λ * J) ^ 3 ≤ 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hc0 : 0 ≤ 9 ^ (d + 1) * Λ * J := by positivity
  have hk2 : Real.sqrt (9 ^ (d + 1) * Λ * J) ^ 2 = 9 ^ (d + 1) * Λ * J := Real.sq_sqrt hc0
  have hsJ2 : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ0
  have h39 : ((3 : ℝ) ^ (d + 1)) ^ 2 = 9 ^ (d + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hkle : Real.sqrt (9 ^ (d + 1) * Λ * J) ≤ 3 ^ (d + 1) * Λ * Real.sqrt J := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (3 ^ (d + 1) * Λ * Real.sqrt J) ^ 2 = 9 ^ (d + 1) * Λ ^ 2 * J := by
      rw [mul_pow, mul_pow, h39, hsJ2]
    rw [this]
    have e0 : Λ ≤ Λ ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hΛ0 hΛ
    have h9 : (0 : ℝ) ≤ 9 ^ (d + 1) := by positivity
    have e1 := mul_le_mul_of_nonneg_left e0 (mul_nonneg h9 hJ0)
    calc 9 ^ (d + 1) * Λ * J = 9 ^ (d + 1) * J * Λ := by ring
      _ ≤ 9 ^ (d + 1) * J * Λ ^ 2 := e1
      _ = 9 ^ (d + 1) * Λ ^ 2 * J := by ring
  have h327 : (3 : ℝ) ^ (d + 1) * 9 ^ (d + 1) = 27 ^ (d + 1) := by
    rw [← mul_pow]; norm_num
  calc Real.sqrt (9 ^ (d + 1) * Λ * J) ^ 3
      = Real.sqrt (9 ^ (d + 1) * Λ * J) * Real.sqrt (9 ^ (d + 1) * Λ * J) ^ 2 := by ring
    _ ≤ (3 ^ (d + 1) * Λ * Real.sqrt J) * (9 ^ (d + 1) * Λ * J) := by
        rw [hk2]
        exact mul_le_mul_of_nonneg_right hkle (by positivity)
    _ = (3 ^ (d + 1) * 9 ^ (d + 1)) * Λ ^ 2 * J * Real.sqrt J := by ring
    _ = 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J := by rw [h327]

/-- The floor of the square-root convolution (`wG2D:1082`): `W^{-D} L^{2d} ≤ (M_u⁻¹)²`
(`W^{-D} ≤ P⁻²`, `P = L^d W^{6d}`, so `W^{-D} L^{2d} ≤ W^{-12d} ≤ W^{-2d} ≤ M_u⁻²`). -/
private theorem sqrt_floor (h : E2HypWG sz n E u D Λ K₀ J M) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ (2 * d) ≤
      ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans_lt' (by norm_num)
  have hLd : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ (2 * d) := by positivity
  have h1 : ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ (2 * d) ≤
      ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) ^ 2 *
        ((sz.L n : ℕ) : ℝ) ^ (2 * d) := mul_le_mul_of_nonneg_right hWD hLd
  have h2 : ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) ^ 2 *
      ((sz.L n : ℕ) : ℝ) ^ (2 * d) = ((((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) ^ 2 := by
    have : ((sz.L n : ℕ) : ℝ) ^ d ≠ 0 := by positivity
    have : ((sz.W n : ℕ) : ℝ) ^ (6 * d) ≠ 0 := by positivity
    rw [pow_mul' ((sz.L n : ℕ) : ℝ) 2 d]
    field_simp
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have h3 : (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hW1.le (by omega)
  have h4 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ hMpos hMW
  have h5 : (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := h3.trans h4
  calc ((sz.W n : ℕ) : ℝ) ^ (-D) * ((sz.L n : ℕ) : ℝ) ^ (2 * d)
      ≤ _ := h1
    _ = ((((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) ^ 2 := h2
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h5 2

set_option maxHeartbeats 1000000 in
-- one declaration holding the counting, the square-root convolution and the constant chain
/-- **Far sum** (`wG2D:1036`): for `|a₁ - a₂| > ℓ*`,
`Σ_y tri(a₁,y,a₂) ≤ (16·27^d Λ² K₀ e^Y (1 + log P)^{2d} + 27^{d+1} C_sq(d) Λ²) · J √J √(M_u⁻¹) T(|a₁-a₂|)`,
`C_sq(d) = 5 (1 + 24576 d⁴)^d` (`LemDecCalEwG_sum_sqrt_tail`); `J √J = J^{3/2}`. -/
private theorem far_sum (h : E2HypWG sz n E u D Λ K₀ J M) (a₁ a₂ : Zd d (sz.L n))
    (hd : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)) :
    ∑ y : Zd d (sz.L n), tri (fG E u M) a₁ y a₂ ≤
      (16 * 27 ^ d * Λ ^ 2 * K₀ * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) +
        27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2) *
        (J * Real.sqrt J * Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hlgP := lemDecCalEwG_log_P_ge sz n hW1.le
  have hfl := sqrt_floor h
  obtain ⟨hE, -, -⟩ := h
  have hptE := fun y => far_pt hE a₁ a₂ y hd
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := hE
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hxu : 0 < 1 - u := by linarith
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hLgW : Real.log ((sz.W n : ℕ) : ℝ) ≤ Lg := by
    have : Real.log ((sz.W n : ℕ) : ℝ) ≤ (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) := by
      nlinarith
    linarith
  set ls := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hls
  set dd : ℝ := (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) with hddef
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  set eY := Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with heYdef
  have hT0 : ∀ x, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D x := fun x =>
    tailTD_nonneg hW0.le
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hK0 : 0 ≤ K₀ := by linarith
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hsm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have hsJ0 : 0 ≤ Real.sqrt J := Real.sqrt_nonneg J
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  set B1 : ℝ := 2 * 9 ^ d * Λ * J * eY * tailTD d ((sz.W n : ℕ) : ℝ) u D dd with hB1
  have hB10 : 0 ≤ B1 := by
    have := hT0 dd
    have : 0 ≤ eY := by linarith
    positivity
  set X1 : ℝ := B1 * (4 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m) with hX1
  have hX10 : 0 ≤ X1 := by
    have : 0 ≤ 4 * 3 ^ d * Λ * K₀ * Real.sqrt J * Real.sqrt m := by positivity
    positivity
  set k : ℝ := Real.sqrt (9 ^ (d + 1) * Λ * J) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  set sT : Zd d (sz.L n) → ℝ := fun y =>
    Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) *
      Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ)) with hsT
  have hsT0 : ∀ y, 0 ≤ sT y := fun y => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpt : ∀ y : Zd d (sz.L n), tri (fG E u M) a₁ y a₂ ≤
      (if (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ ls / 2 then X1 else 0) +
        (if (zdistInf d (sz.L n) (a₂ - y) : ℝ) ≤ ls / 2 then X1 else 0) +
          k ^ 3 * (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) * sT y) := hptE
  -- the square-root convolution
  have hTD : ∀ r : ℝ, tailTD d ((sz.W n : ℕ) : ℝ) u D r =
      m ^ 2 * Real.exp (-Real.sqrt r) + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    intro r; unfold tailTD; rw [abs_of_pos hxu]
  have hwnn : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hconv := LemDecCalEwG_sum_sqrt_tail (d := d) (L := sz.L n) (by omega) (sq_nonneg m) hwnn
    hfl a₁ a₂
  rw [Real.sqrt_sq hm0] at hconv
  simp only [← hTD] at hconv
  have hconv' : ∑ y : Zd d (sz.L n), sT y ≤
      5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m *
        Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) := by
    have : ∑ y : Zd d (sz.L n), sT y = ∑ y : Zd d (sz.L n),
        Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (y - a₂) : ℝ)) *
          Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (a₁ - y) : ℝ)) :=
      Finset.sum_congr rfl fun y _ => mul_comm _ _
    rw [this]
    exact hconv
  -- summation
  have hsum : ∑ y : Zd d (sz.L n), tri (fG E u M) a₁ y a₂ ≤
      ((Finset.univ.filter fun y : Zd d (sz.L n) => (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ ls / 2).card : ℝ) * X1 +
        ((Finset.univ.filter fun y : Zd d (sz.L n) => (zdistInf d (sz.L n) (a₂ - y) : ℝ) ≤ ls / 2).card : ℝ) * X1 +
          k ^ 3 * (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) * ∑ y : Zd d (sz.L n), sT y) := by
    refine (Finset.sum_le_sum fun y _ => hpt y).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    exact le_rfl
  have hls0 : 0 ≤ ls := Real.rpow_nonneg (by linarith) _
  have hc1 := LemDecCalE_e10a a₁ (ls / 2) (by linarith)
  have hc2 := LemDecCalE_e10a a₂ (ls / 2) (by linarith)
  -- the count: `(ℓ* + 1)^d ≤ (1 + log P)^{2d}`
  have hlsLg : (2 * (ls / 2) + 1) ^ d ≤ (1 + Lg) ^ (2 * d) := by
    have h1 : ls ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_two] at h1
    have h2 : 2 * (ls / 2) + 1 ≤ (1 + Lg) ^ 2 := by
      nlinarith
    calc (2 * (ls / 2) + 1) ^ d ≤ ((1 + Lg) ^ 2) ^ d :=
          pow_le_pow_left₀ (by linarith) h2 d
      _ = (1 + Lg) ^ (2 * d) := by rw [← pow_mul]
  -- constants
  have hk3 : k ^ 3 ≤ 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J :=
    lemDecCalEwG_k_cube_le hΛ hJ1 d
  have hsm : m ≤ Real.sqrt m := lemDecCalEwG_m_le_sqrt hm0 hm1
  have hTd := hT0 dd
  have hsTd : Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
      Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) = tailTD d ((sz.W n : ℕ) : ℝ) u D dd :=
    Real.mul_self_sqrt hTd
  have h327d : (9 : ℝ) ^ d * 3 ^ d = 27 ^ d := by rw [← mul_pow]; norm_num
  set Q : ℝ := J * Real.sqrt J * Real.sqrt m * tailTD d ((sz.W n : ℕ) : ℝ) u D dd with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hX1Q : X1 = 8 * 27 ^ d * Λ ^ 2 * K₀ * eY * Q := by
    rw [hX1, hB1, hQ, ← h327d]; ring
  have hpart1 : ((Finset.univ.filter fun y : Zd d (sz.L n) =>
        (zdistInf d (sz.L n) (a₁ - y) : ℝ) ≤ ls / 2).card : ℝ) * X1 +
      ((Finset.univ.filter fun y : Zd d (sz.L n) =>
        (zdistInf d (sz.L n) (a₂ - y) : ℝ) ≤ ls / 2).card : ℝ) * X1 ≤
      16 * 27 ^ d * Λ ^ 2 * K₀ * eY * (1 + Lg) ^ (2 * d) * Q := by
    have e1 := mul_le_mul_of_nonneg_right (hc1.trans hlsLg) hX10
    have e2 := mul_le_mul_of_nonneg_right (hc2.trans hlsLg) hX10
    have e3 : (1 + Lg) ^ (2 * d) * X1 = 8 * 27 ^ d * Λ ^ 2 * K₀ * eY * (1 + Lg) ^ (2 * d) * Q := by
      rw [hX1Q]; ring
    linarith
  have hpart2 : k ^ 3 * (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) * ∑ y : Zd d (sz.L n), sT y) ≤
      27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2 * Q := by
    have e1 : Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) * ∑ y : Zd d (sz.L n), sT y ≤
        Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
          (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m *
            Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd)) :=
      mul_le_mul_of_nonneg_left hconv' (Real.sqrt_nonneg _)
    have e2 : Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
        (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m *
          Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd)) =
        5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m * tailTD d ((sz.W n : ℕ) : ℝ) u D dd := by
      calc _ = 5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m *
            (Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
              Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd)) := by ring
        _ = _ := by rw [hsTd]
    have e3 : 0 ≤ Real.sqrt (tailTD d ((sz.W n : ℕ) : ℝ) u D dd) * ∑ y : Zd d (sz.L n), sT y :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun y _ => hsT0 y)
    have e4 := mul_le_mul hk3 e1 e3 (by positivity)
    rw [e2] at e4
    have e5 : 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J *
        (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) ≤
        27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2 * Q := by
      have : 0 ≤ 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D dd := by positivity
      have e6 := mul_le_mul_of_nonneg_left hsm this
      calc 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J *
            (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d * m * tailTD d ((sz.W n : ℕ) : ℝ) u D dd)
          = 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) *
              tailTD d ((sz.W n : ℕ) : ℝ) u D dd * m := by ring
        _ ≤ 27 ^ (d + 1) * Λ ^ 2 * J * Real.sqrt J * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) *
              tailTD d ((sz.W n : ℕ) : ℝ) u D dd * Real.sqrt m := e6
        _ = 27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2 * Q := by rw [hQ]; ring
    linarith
  calc ∑ y : Zd d (sz.L n), tri (fG E u M) a₁ y a₂ ≤ _ := hsum
    _ ≤ 16 * 27 ^ d * Λ ^ 2 * K₀ * eY * (1 + Lg) ^ (2 * d) * Q +
        27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2 * Q := add_le_add hpart1 hpart2
    _ = _ := by ring

end Far

/-! ## 7. The loss, the normalisation, and `lemDecCalE_wG` (`wG2D:1189-1385`) -/

section Main

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

set_option maxHeartbeats 400000 in
-- the many real-number side goals of the three constant comparisons exceed the default budget
/-- The loss absorbs the three constants of the proof (`wG2D:1189`): near `2·9^d Λ² (1 + log P)^{2d} e^Y`
and `40·9^d Λ⁴ e^Y`; far `2 Λ (16·27^d Λ² K₀ e^Y (1 + log P)^{2d} + 27^{d+1} C_sq(d) Λ²)`, with
`C_sq(d) = 5 (1 + 24576 d⁴)^d`.  (`27 (1 + 24576 d⁴) ≤ 1.6·10⁶ d⁴`: the `1000^d` of `lossE2wG`.) -/
private theorem loss_ge (h : E2HypWG sz n E u D Λ K₀ J M) :
    2 * 9 ^ d * Λ ^ 2 *
        (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) *
        Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ ∧
    40 * 9 ^ d * Λ ^ 4 * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ ∧
    2 * Λ * (16 * 27 ^ d * Λ ^ 2 * K₀ * Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))) ^ (2 * d) +
        27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2) ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hlgP := lemDecCalEwG_log_P_ge sz n hW1.le
  obtain ⟨hE, -, -⟩ := h
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, -⟩ := hE
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  set lg : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hlgdef
  set Y : ℝ := lg ^ ((3 : ℝ) / 4) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hLg0 : 0 ≤ Lg := by
    have : (0 : ℝ) ≤ (6 * (d : ℝ)) * lg := by positivity
    linarith
  have hG : (1 : ℝ) ≤ (1 + Lg) ^ (2 * d) := one_le_pow₀ (by linarith)
  have hc1 : 1 ≤ Real.exp Y := Real.one_le_exp hY0
  have hcC : Real.exp Y ≤ Real.exp (8 * Y) := Real.exp_le_exp.2 (by linarith)
  have hbase : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1.le)
  have hLq : (1 : ℝ) ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 :=
    one_le_pow₀ (by linarith [Real.log_nonneg hbase])
  have hLw : (125 : ℝ) ≤ (1 + lg) ^ 3 := by
    have : (5 : ℝ) ≤ 1 + lg := by linarith
    calc (125 : ℝ) = 5 ^ 3 := by norm_num
      _ ≤ (1 + lg) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  have hK2 : 1 ≤ K₀ ^ 2 := one_le_pow₀ hK
  have hK2' : K₀ ≤ K₀ ^ 2 := le_self_pow₀ hK (by norm_num)
  have hΛ2 : Λ ^ 2 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have hΛ3 : Λ ^ 3 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have hΛ4 : Λ ^ 4 ≤ Λ ^ 6 := pow_le_pow_right₀ hΛ (by norm_num)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hK0 : 0 ≤ K₀ := by linarith
  -- the constants against `c0 = (1600 d⁴)^d 1000^d`
  set c0 : ℝ := (1600 * (d : ℝ) ^ 4) ^ d * 1000 ^ d with hc0
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hc0eq : c0 = (1600 * (d : ℝ) ^ 4 * 1000) ^ d := by rw [hc0, ← mul_pow]
  have h9c : (9 : ℝ) ^ d ≤ c0 := by
    rw [hc0eq]; exact pow_le_pow_left₀ (by norm_num) (by linarith) d
  have h27c : (27 : ℝ) ^ d ≤ c0 := by
    rw [hc0eq]; exact pow_le_pow_left₀ (by norm_num) (by linarith) d
  have hSc : (27 : ℝ) ^ d * (1 + 24576 * (d : ℝ) ^ 4) ^ d ≤ c0 := by
    rw [hc0eq, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have h1c : (0 : ℝ) ≤ c0 := by positivity
  have hloss : lossE2wG d (sz.L n) (sz.W n) Λ K₀ =
      10 ^ 12 * c0 * ((1 + Lg) ^ (2 * d) *
        (K₀ ^ 2 * Λ ^ 6 *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
          (1 + lg) ^ 3 * Real.exp (8 * Y))) := by
    unfold lossE2wG lossE2
    rw [hc0]; ring
  set R : ℝ := (1 + Lg) ^ (2 * d) *
        (K₀ ^ 2 * Λ ^ 6 *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
          (1 + lg) ^ 3 * Real.exp (8 * Y)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hQ1 : 1 ≤ K₀ ^ 2 * (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
      (1 + lg) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK2 hLq) (by linarith)
  have hexp8 : 1 ≤ Real.exp (8 * Y) := Real.one_le_exp (by linarith)
  have hΛ6 : 0 ≤ Λ ^ 6 := by positivity
  -- `R ≥ (1+Lg)^{2d} Λ⁶ e^{8Y} K₀`, in particular `R ≥ (1+Lg)^{2d} Λ⁶ e^{8Y}`
  have hRge' : (1 + Lg) ^ (2 * d) * (K₀ * (Λ ^ 6 * Real.exp (8 * Y))) ≤ R := by
    rw [hR]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : K₀ ≤ K₀ ^ 2 * (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
        (1 + lg) ^ 3 := by
      have : 1 ≤ (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
          (1 + lg) ^ 3 := one_le_mul_of_one_le_of_one_le hLq (by linarith)
      calc K₀ ≤ K₀ ^ 2 := hK2'
        _ = K₀ ^ 2 * 1 := (mul_one _).symm
        _ ≤ K₀ ^ 2 * ((1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
            (1 + lg) ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have e2 : 0 ≤ Λ ^ 6 * Real.exp (8 * Y) := by positivity
    calc K₀ * (Λ ^ 6 * Real.exp (8 * Y)) ≤ (K₀ ^ 2 * (1 + Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d))) ^ 4 *
            (1 + lg) ^ 3) * (Λ ^ 6 * Real.exp (8 * Y)) := mul_le_mul_of_nonneg_right e1 e2
      _ = _ := by ring
  have hRge : (1 + Lg) ^ (2 * d) * (Λ ^ 6 * Real.exp (8 * Y)) ≤ R := by
    refine le_trans ?_ hRge'
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_mul_of_one_le_left (by positivity) hK
  have hlossR : lossE2wG d (sz.L n) (sz.W n) Λ K₀ = 10 ^ 12 * c0 * R := hloss
  have hbig : ∀ x : ℝ, 0 ≤ x → x ≤ 10 ^ 12 → x * (c0 * R) ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
    intro x hx0 hx
    rw [hlossR]
    have : 0 ≤ c0 * R := by positivity
    calc x * (c0 * R) ≤ 10 ^ 12 * (c0 * R) := mul_le_mul_of_nonneg_right hx this
      _ = 10 ^ 12 * c0 * R := by ring
  refine ⟨?_, ?_, ?_⟩
  · -- near, first
    have e3 : Λ ^ 2 * Real.exp Y ≤ Λ ^ 6 * Real.exp (8 * Y) :=
      mul_le_mul hΛ2 hcC (Real.exp_pos _).le hΛ6
    have e4 : (1 + Lg) ^ (2 * d) * (Λ ^ 2 * Real.exp Y) ≤ R :=
      (mul_le_mul_of_nonneg_left e3 (by positivity)).trans hRge
    have e5 : 2 * 9 ^ d * Λ ^ 2 * (1 + Lg) ^ (2 * d) * Real.exp Y =
        (2 * 9 ^ d) * ((1 + Lg) ^ (2 * d) * (Λ ^ 2 * Real.exp Y)) := by ring
    rw [e5]
    calc (2 * 9 ^ d) * ((1 + Lg) ^ (2 * d) * (Λ ^ 2 * Real.exp Y)) ≤ (2 * c0) * R :=
          mul_le_mul (by linarith) e4 (by positivity) (by positivity)
      _ = 2 * (c0 * R) := by ring
      _ ≤ _ := hbig 2 (by norm_num) (by norm_num)
  · -- near, second
    have e3 : Λ ^ 4 * Real.exp Y ≤ Λ ^ 6 * Real.exp (8 * Y) :=
      mul_le_mul hΛ4 hcC (Real.exp_pos _).le hΛ6
    have e4 : Λ ^ 4 * Real.exp Y ≤ R :=
      e3.trans ((le_mul_of_one_le_left (by positivity) hG).trans hRge)
    have e5 : 40 * 9 ^ d * Λ ^ 4 * Real.exp Y = (40 * 9 ^ d) * (Λ ^ 4 * Real.exp Y) := by ring
    rw [e5]
    calc (40 * 9 ^ d) * (Λ ^ 4 * Real.exp Y) ≤ (40 * c0) * R :=
          mul_le_mul (by linarith) e4 (by positivity) (by positivity)
      _ = 40 * (c0 * R) := by ring
      _ ≤ _ := hbig 40 (by norm_num) (by norm_num)
  · -- far
    have e3 : Λ ^ 3 * Real.exp Y ≤ Λ ^ 6 * Real.exp (8 * Y) :=
      mul_le_mul hΛ3 hcC (Real.exp_pos _).le hΛ6
    have hfirst : 2 * Λ * (16 * 27 ^ d * Λ ^ 2 * K₀ * Real.exp Y * (1 + Lg) ^ (2 * d)) ≤
        (32 * 27 ^ d) * R := by
      have e1 : 2 * Λ * (16 * 27 ^ d * Λ ^ 2 * K₀ * Real.exp Y * (1 + Lg) ^ (2 * d)) =
          (32 * 27 ^ d) * ((1 + Lg) ^ (2 * d) * (K₀ * (Λ ^ 3 * Real.exp Y))) := by ring
      rw [e1]
      have e4 : (1 + Lg) ^ (2 * d) * (K₀ * (Λ ^ 3 * Real.exp Y)) ≤ R :=
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 hK0) (by positivity)).trans hRge'
      exact mul_le_mul_of_nonneg_left e4 (by positivity)
    have hsecond : 2 * Λ * (27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2) ≤
        (270 * ((27 : ℝ) ^ d * (1 + 24576 * (d : ℝ) ^ 4) ^ d)) * R := by
      have e1 : 2 * Λ * (27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2) =
          (270 * ((27 : ℝ) ^ d * (1 + 24576 * (d : ℝ) ^ 4) ^ d)) * Λ ^ 3 := by ring
      rw [e1]
      have e4 : Λ ^ 3 ≤ R := by
        calc Λ ^ 3 ≤ Λ ^ 6 := hΛ3
          _ = Λ ^ 6 * 1 := (mul_one _).symm
          _ ≤ Λ ^ 6 * Real.exp (8 * Y) := mul_le_mul_of_nonneg_left hexp8 hΛ6
          _ ≤ (1 + Lg) ^ (2 * d) * (Λ ^ 6 * Real.exp (8 * Y)) :=
              le_mul_of_one_le_left (by positivity) hG
          _ ≤ R := hRge
      exact mul_le_mul_of_nonneg_left e4 (by positivity)
    have hq1 : (32 * 27 ^ d) * R ≤ 32 * (c0 * R) := by
      calc (32 * 27 ^ d) * R = 32 * (27 ^ d * R) := by ring
        _ ≤ 32 * (c0 * R) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h27c hR0) (by norm_num)
    have hq2 : (270 * ((27 : ℝ) ^ d * (1 + 24576 * (d : ℝ) ^ 4) ^ d)) * R ≤ 270 * (c0 * R) := by
      calc (270 * ((27 : ℝ) ^ d * (1 + 24576 * (d : ℝ) ^ 4) ^ d)) * R
          = 270 * (((27 : ℝ) ^ d * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * R) := by ring
        _ ≤ 270 * (c0 * R) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSc hR0) (by norm_num)
    calc 2 * Λ * (16 * 27 ^ d * Λ ^ 2 * K₀ * Real.exp Y * (1 + Lg) ^ (2 * d) +
          27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2)
        = 2 * Λ * (16 * 27 ^ d * Λ ^ 2 * K₀ * Real.exp Y * (1 + Lg) ^ (2 * d)) +
          2 * Λ * (27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2) := by ring
      _ ≤ 32 * (c0 * R) + 270 * (c0 * R) := by
          have := hfirst.trans hq1
          have := hsecond.trans hq2
          linarith
      _ = 302 * (c0 * R) := by ring
      _ ≤ _ := hbig 302 (by norm_num) (by norm_num)

/-- The near normalisation (`wG2D:1256`): for `|a₁-a₂| ≤ ℓ*`, `M_u⁻² ≤ e^{(log W)^{3/4}} T_{u,D}(|a₁-a₂|)`
(`T(dd - ℓ*) ≥ M_u⁻²` as the square root of a non-positive number is `0`, then `LemDecCalE_e4c`). -/
private theorem near_norm {W u D : ℝ} (d : ℕ) (hW : 1 ≤ W) (hu : u < 1) {dd : ℝ}
    (hd : dd ≤ Real.log W ^ ((3 : ℝ) / 2)) :
    ((W ^ d * (1 - u))⁻¹) ^ 2 ≤
      Real.exp (Real.log W ^ ((3 : ℝ) / 4)) * tailTD d W u D dd := by
  have h := tail_le_Y (d := d) (W := W) (u := u) (D := D) hW (dd := dd)
    (x := dd - Real.log W ^ ((3 : ℝ) / 2)) le_rfl
  refine le_trans ?_ h
  have hneg : dd - Real.log W ^ ((3 : ℝ) / 2) ≤ 0 := by linarith
  have hxu : 0 < 1 - u := by linarith
  unfold tailTD
  rw [Real.sqrt_eq_zero_of_nonpos hneg, neg_zero, Real.exp_zero, mul_one, abs_of_pos hxu]
  have : 0 ≤ W ^ (-D) := Real.rpow_nonneg (by linarith) _
  linarith

/-- `W^{-6d} ≤ M_u⁻² √(M_u⁻¹)` (`W^{-6d} ≤ W^{-3d} ≤ M_u⁻³ ≤ M_u⁻² √(M_u⁻¹)`). -/
private theorem W6_le (h : E2Hyp sz n E u D Λ K₀ J M) :
    (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ ≤ ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
      Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar⟩ := facts0 h
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hsm := lemDecCalEwG_m_le_sqrt hm0 hm1
  have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ m := inv_anti₀ hMpos hMW
  have h2 : (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 := by
    rw [inv_pow, ← pow_mul]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hW1.le (by omega)
  have h3 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  calc (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ ≤ m ^ 3 := h2.trans h3
    _ = m ^ 2 * m := by ring
    _ ≤ m ^ 2 * Real.sqrt m := mul_le_mul_of_nonneg_left hsm (by positivity)

/-- `J^{3/2} = J √J` (rpow). -/
private theorem lemDecCalEwG_rpow_three_halves {J : ℝ} (hJ : 0 < J) :
    J ^ ((3 : ℝ) / 2) = J * Real.sqrt J := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hJ, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

set_option maxHeartbeats 1000000 in
-- one declaration holding the near and the far assembly with their rpow/sqrt conversions
/-- **`lemDecCalE_wG`** (`res_deccalE_wG`, `3_5:2322-2325`; `wG2D:1276`), deterministic at one time `u`,
every `σ ∈ {±}²`: the prefactor (`EGt_le_pref`); near `|a₁-a₂| ≤ ℓ*`: `near_sum` and `near_norm`; far:
`loops_le_tri` and `far_sum`; the constants are at most `lossE2wG` (`loss_ge`), and `W^d M_u⁻¹ = (1-u)⁻¹`;
`J^{3/2} = J √J`, `M_u^{-1/2} = √(M_u⁻¹)`. -/
theorem lemDecCalE_wG (d : ℕ) : LemDecCalE_wG d := by
  intro sz n E u D Λ K₀ J M h σ a
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hpref := EGt_le_pref h.1 σ a
  have hnear := near_sum h σ (a 0) (a 1)
  obtain ⟨hlossN1, hlossN2, hlossF⟩ := loss_ge h
  have hfarS := far_sum h (a 0) (a 1)
  have hW6 := W6_le h.1
  obtain ⟨hE, hfl, hl3⟩ := h
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := hE
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hxu : 0 < 1 - u := by linarith
  have hlgP := lemDecCalEwG_log_P_ge sz n hW1.le
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hJpos : 0 < J := by linarith
  have hMpos : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  rw [abs_of_pos hxu]
  set Lg : ℝ := Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) with hLg
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  set ls := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hls
  set eY := Real.exp (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with heYdef
  set Φ := lossE2wG d (sz.L n) (sz.W n) Λ K₀ with hΦ
  set dd : ℝ := (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) with hddef
  set T := tailTD d ((sz.W n : ℕ) : ℝ) u D dd with hTdef
  have hT0 : 0 ≤ T := tailTD_nonneg hW0.le
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := inv_le_one_of_one_le₀ hM1
  have hsm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have hsJ0 : 0 ≤ Real.sqrt J := Real.sqrt_nonneg J
  have hsJ1 : 1 ≤ Real.sqrt J := by
    rw [Real.le_sqrt zero_le_one hJ0]; linarith
  have heY : 1 ≤ eY := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hWm : ((sz.W n : ℕ) : ℝ) ^ d * m = (1 - u)⁻¹ := by
    rw [hm]; field_simp
  have hinvu : 0 ≤ (1 - u)⁻¹ := (inv_pos.2 hxu).le
  have hm12 : m ^ ((1 : ℝ) / 2) = Real.sqrt m := (Real.sqrt_eq_rpow m).symm
  have hJ32 := lemDecCalEwG_rpow_three_halves hJpos
  have hSTT : STtailTD sz n u D a = T := rfl
  rw [hm12, hJ32, hSTT]
  have hLg0 : 0 ≤ Lg := by
    have : (0 : ℝ) ≤ (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) := by positivity
    linarith
  have hΦ0 : 0 ≤ Φ := le_trans (by positivity) hlossN2
  have hWd0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hpre0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (Λ * m) := by positivity
  -- the prefactor: `W^d (Λ m) = Λ (1-u)⁻¹`
  have hpre : ((sz.W n : ℕ) : ℝ) ^ d * (Λ * m) = Λ * (1 - u)⁻¹ := by
    rw [← hWm]; ring
  rw [hpre] at hpref
  by_cases hdist : dd ≤ ls
  · -- near
    have hnorm := near_norm (D := D) d hW1.le hu1 hdist
    simp only [hdist, ↓reduceIte]
    set A1 : ℝ := 2 * 9 ^ d * Λ * Lg ^ (2 * d) * m ^ 2 with hA1
    set A2 : ℝ := 40 * 9 ^ d * Λ ^ 3 * J * (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ with hA2
    have e1 : ‖STEGtM sz n E u M σ a‖ ≤ Λ * (1 - u)⁻¹ * (A1 + A2) :=
      hpref.trans (mul_le_mul_of_nonneg_left hnear (by positivity))
    have hLgG : Lg ^ (2 * d) ≤ (1 + Lg) ^ (2 * d) := pow_le_pow_left₀ hLg0 (by linarith) _
    have hP0 : 0 ≤ (1 - u)⁻¹ * T := mul_nonneg hinvu hT0
    -- first part
    have e2 : Λ * (1 - u)⁻¹ * A1 ≤ Φ * ((1 - u)⁻¹ * T) := by
      have e3 : Λ * (1 - u)⁻¹ * A1 = (2 * 9 ^ d * Λ ^ 2 * Lg ^ (2 * d)) * ((1 - u)⁻¹ * m ^ 2) := by
        rw [hA1]; ring
      have e4 : (1 - u)⁻¹ * m ^ 2 ≤ (1 - u)⁻¹ * (eY * T) :=
        mul_le_mul_of_nonneg_left hnorm hinvu
      have e5 : (2 * 9 ^ d * Λ ^ 2 * Lg ^ (2 * d)) * ((1 - u)⁻¹ * m ^ 2) ≤
          (2 * 9 ^ d * Λ ^ 2 * (1 + Lg) ^ (2 * d)) * ((1 - u)⁻¹ * (eY * T)) :=
        mul_le_mul (by gcongr) e4 (by positivity) (by positivity)
      have e6 : (2 * 9 ^ d * Λ ^ 2 * (1 + Lg) ^ (2 * d)) * ((1 - u)⁻¹ * (eY * T)) =
          (2 * 9 ^ d * Λ ^ 2 * (1 + Lg) ^ (2 * d) * eY) * ((1 - u)⁻¹ * T) := by ring
      rw [e3]
      refine e5.trans (le_of_eq e6 |>.trans ?_)
      exact mul_le_mul_of_nonneg_right hlossN1 hP0
    -- second part
    have e7 : Λ * (1 - u)⁻¹ * A2 ≤ Φ * (((1 - u)⁻¹ * T) * (Real.sqrt m * (J * Real.sqrt J))) := by
      have e3 : Λ * (1 - u)⁻¹ * A2 = (40 * 9 ^ d * Λ ^ 4 * J) * ((1 - u)⁻¹ *
          (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) := by
        rw [hA2]; ring
      have e4 : (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ ≤ (eY * T) * Real.sqrt m :=
        hW6.trans (mul_le_mul_of_nonneg_right hnorm hsm0)
      have e5 : (40 * 9 ^ d * Λ ^ 4 * J) * ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹) ≤
          (40 * 9 ^ d * Λ ^ 4 * J) * ((1 - u)⁻¹ * ((eY * T) * Real.sqrt m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e4 hinvu) (by positivity)
      have e6 : (40 * 9 ^ d * Λ ^ 4 * J) * ((1 - u)⁻¹ * ((eY * T) * Real.sqrt m)) =
          (40 * 9 ^ d * Λ ^ 4 * eY) * (((1 - u)⁻¹ * T) * (Real.sqrt m * J)) := by ring
      have e8 : Real.sqrt m * J ≤ Real.sqrt m * (J * Real.sqrt J) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hJ0 hsJ1) hsm0
      have e9 : (40 * 9 ^ d * Λ ^ 4 * eY) * (((1 - u)⁻¹ * T) * (Real.sqrt m * J)) ≤
          Φ * (((1 - u)⁻¹ * T) * (Real.sqrt m * (J * Real.sqrt J))) :=
        mul_le_mul hlossN2 (mul_le_mul_of_nonneg_left e8 hP0) (by positivity) hΦ0
      rw [e3]
      exact e5.trans (le_of_eq e6 |>.trans e9)
    calc ‖STEGtM sz n E u M σ a‖ ≤ Λ * (1 - u)⁻¹ * (A1 + A2) := e1
      _ = Λ * (1 - u)⁻¹ * A1 + Λ * (1 - u)⁻¹ * A2 := by ring
      _ ≤ Φ * ((1 - u)⁻¹ * T) + Φ * (((1 - u)⁻¹ * T) * (Real.sqrt m * (J * Real.sqrt J))) :=
          add_le_add e2 e7
      _ = Φ * ((1 - u)⁻¹ * (1 + Real.sqrt m * (J * Real.sqrt J)) * T) := by ring
  · -- far
    have hd' : ls < dd := not_le.1 hdist
    simp only [hdist, ↓reduceIte]
    have hfar := hfarS hd'
    have hS2 : ∑ y : Zd d (sz.L n), (‖STLM sz n E u M ![σ 0, σ 0, σ 1] ![y, a 0, a 1]‖ +
        ‖STLM sz n E u M ![σ 0, σ 1, σ 1] ![a 0, y, a 1]‖) ≤
        2 * ∑ y : Zd d (sz.L n), tri (fG E u M) (a 0) y (a 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => loops_le_tri hH σ (a 0) (a 1) y
    set Cf : ℝ := 16 * 27 ^ d * Λ ^ 2 * K₀ * eY * (1 + Lg) ^ (2 * d) +
      27 ^ (d + 1) * (5 * (1 + 24576 * (d : ℝ) ^ 4) ^ d) * Λ ^ 2 with hCf
    have hQ0 : 0 ≤ J * Real.sqrt J * Real.sqrt m * T := by positivity
    have e1 : ‖STEGtM sz n E u M σ a‖ ≤ Λ * (1 - u)⁻¹ * (2 * (Cf * (J * Real.sqrt J * Real.sqrt m * T))) := by
      refine hpref.trans (mul_le_mul_of_nonneg_left (hS2.trans ?_) (by positivity))
      exact mul_le_mul_of_nonneg_left hfar (by norm_num)
    have e2 : Λ * (1 - u)⁻¹ * (2 * (Cf * (J * Real.sqrt J * Real.sqrt m * T))) =
        (2 * Λ * Cf) * ((1 - u)⁻¹ * (0 + Real.sqrt m * (J * Real.sqrt J)) * T) := by ring
    have hX0 : 0 ≤ (1 - u)⁻¹ * (0 + Real.sqrt m * (J * Real.sqrt J)) * T := by positivity
    have hlossF' : 2 * Λ * Cf ≤ Φ := hlossF
    calc ‖STEGtM sz n E u M σ a‖ ≤ _ := e1
      _ = _ := e2
      _ ≤ Φ * ((1 - u)⁻¹ * (0 + Real.sqrt m * (J * Real.sqrt J)) * T) :=
          mul_le_mul_of_nonneg_right hlossF' hX0

end Main

/-! ## 8. Target 4: `E2HypWG` at `M = 0`, `u = 0` -/

section Witness

variable {d : ℕ}

/-- `G_0(+) = m I` at `H = 0`, `u = 0` (the text of the `private` `lemDecCalE_gres_zero_true`,
`Path/LemDecCalE.lean:1208`). -/
private theorem lemDecCalEwG_gres_zero_true {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
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
private theorem lemDecCalEwG_gres_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
    (hE : |E| ≤ 2) (σ : Bool) :
    Gres (0 : Matrix ι ι ℂ) (zt E 0) σ = mSigma E σ • (1 : Matrix ι ι ℂ) := by
  cases σ
  · rw [lemDecCalEwG_Gres_false Matrix.isHermitian_zero, lemDecCalEwG_gres_zero_true hE,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [mSigma]
  · simpa [mSigma] using lemDecCalEwG_gres_zero_true (ι := ι) hE

private theorem lemDecCalEwG_blockMat_zero {L W : ℕ} [NeZero L] [NeZero W] :
    blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ) = 0 := by
  ext i j; simp [blockMat]

/-- `Σ_{p ∈ Vtx} 1(p.1 = a) c = W^d c`. -/
private theorem lemDecCalEwG_sum_block_indicator {L W : ℕ} [NeZero L] (c : ℝ) (a : Zd d L) :
    ∑ p : Vtx d L W, (if p.1 = a then c else 0) = (W : ℝ) ^ d * c := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : Zd d L, ∑ y : Fin (W ^ d), (if (x, y).1 = a then c else 0) =
      if x = a then (W : ℝ) ^ d * c else 0 := by
    intro x
    by_cases hx : x = a
    · simp only [hx, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    · simp [hx]
  simp only [h]
  simp

/-- `|tr(E_a E_b E_c)| ≤ W^{-2d}` (each `E` is diagonal with entries `W^{-d} 1(p.1 = ·)`). -/
private theorem lemDecCalEwG_trace_three_Eblk {L W : ℕ} [NeZero L] [NeZero W] (a b c : Zd d L) :
    ‖Matrix.trace (Eblk d L W a * (Eblk d L W b * Eblk d L W c))‖ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h : Eblk d L W a * (Eblk d L W b * Eblk d L W c) = Matrix.diagonal (fun p : Vtx d L W =>
      (if p.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        ((if p.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) * (if p.1 = c then ((W : ℂ) ^ d)⁻¹ else 0))) := by
    unfold Eblk
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  rw [h, Matrix.trace_diagonal]
  have hw0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hnorm : ∀ (x e : Zd d L), ‖(if x = e then ((W : ℂ) ^ d)⁻¹ else 0)‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
    intro x e
    split_ifs
    · simp
    · simp only [norm_zero]; exact hw0
  calc ‖∑ p : Vtx d L W, (if p.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
          ((if p.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) * (if p.1 = c then ((W : ℂ) ^ d)⁻¹ else 0))‖
      ≤ ∑ p : Vtx d L W, (if p.1 = a then (((W : ℝ) ^ d)⁻¹) ^ 3 else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        by_cases hp : p.1 = a
        · simp only [hp, ite_true]
          rw [norm_mul, norm_mul]
          have h2 : ‖(if a = b then ((W : ℂ) ^ d)⁻¹ else 0)‖ ≤ ((W : ℝ) ^ d)⁻¹ := hnorm _ _
          have h3 : ‖(if a = c then ((W : ℂ) ^ d)⁻¹ else 0)‖ ≤ ((W : ℝ) ^ d)⁻¹ := hnorm _ _
          have h0 : ‖((W : ℂ) ^ d)⁻¹‖ = ((W : ℝ) ^ d)⁻¹ := by simp
          rw [h0]
          calc ((W : ℝ) ^ d)⁻¹ * (‖(if a = b then ((W : ℂ) ^ d)⁻¹ else 0)‖ *
                ‖(if a = c then ((W : ℂ) ^ d)⁻¹ else 0)‖) ≤
              ((W : ℝ) ^ d)⁻¹ * (((W : ℝ) ^ d)⁻¹ * ((W : ℝ) ^ d)⁻¹) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (norm_nonneg _) hw0) hw0
            _ = (((W : ℝ) ^ d)⁻¹) ^ 3 := by ring
        · simp [hp]
    _ = (W : ℝ) ^ d * (((W : ℝ) ^ d)⁻¹) ^ 3 := lemDecCalEwG_sum_block_indicator _ a
    _ = (((W : ℝ) ^ d)⁻¹) ^ 2 := by
        have : (W : ℝ) ^ d ≠ 0 := by positivity
        field_simp

/-- `|𝓛^{(3)}_{0,σ,a}| ≤ W^{-2d}` at `M = 0`, `u = 0` (`G_0(σ) = m(σ) I`, `|m(σ)| = 1`). -/
private theorem lemDecCalEwG_STLM_zero_three (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)) :
    ‖STLM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a‖ ≤
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 := by
  have hexp : STLM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a =
      mSigma E (σ 0) * (mSigma E (σ 1) * (mSigma E (σ 2) *
        Matrix.trace (Eblk d (sz.L n) (sz.W n) (a 0) * (Eblk d (sz.L n) (sz.W n) (a 1) *
          Eblk d (sz.L n) (sz.W n) (a 2))))) := by
    unfold STLM loopFine loopM
    rw [lemDecCalEwG_blockMat_zero]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      lemDecCalEwG_gres_zero hE, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    ring
  rw [hexp, norm_mul, norm_mul, norm_mul, norm_mSigma hE, norm_mSigma hE, norm_mSigma hE]
  simp only [one_mul]
  exact lemDecCalEwG_trace_three_Eblk _ _ _

/-- **Target 4** (`E2HypWG` at `M = 0`, `u = 0`): the numeric premises of `LemDecCalE_e2Hyp_zero`, with
its floor replaced by `(L^d W^{6d})² ≤ W^D` (from which `L^d W^{2d} ≤ W^D` follows), give every
conjunct: the three-loop bound is `|𝓛^{(3)}| ≤ W^{-2d} ≤ Λ (W^d)^{-2}` exactly (`1 ≤ Λ`). -/
theorem LemDecCalEwG_hyp_zero (sz : Sizes d) (n : ℕ) {E D Λ K₀ J : ℝ} (hd : 3 ≤ d)
    (hE : |E| < 2) (hlam : 0 < sz.lam n) (hlam1 : sz.lam n ^ 2 ≤ 1)
    (hlamW : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hΛ : 1 ≤ Λ) (hK : 1 ≤ K₀)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hfloor : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
      ((sz.W n : ℕ) : ℝ) ^ D)
    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
    E2HypWG sz n E 0 D Λ K₀ J
      (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
  have hW0 := lemDecCalEwG_W_pos sz n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_le.1 hcon).le
    linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1)
  have hfloor' : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ D := by
    refine le_trans ?_ hfloor
    calc ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d)
        ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW1 (by omega)) (by positivity)
      _ ≤ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 :=
          le_self_pow₀ hP1 (by norm_num)
  refine ⟨LemDecCalE_e2Hyp_zero sz n hd hE hlam hlam1 hlamW hΛ hK hlog hfloor' hJ hJW, hfloor, ?_⟩
  intro σ a
  refine (lemDecCalEwG_STLM_zero_three sz n hE.le σ a).trans ?_
  have : (0 : ℝ) ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 := by positivity
  simp only [sub_zero, mul_one]
  exact le_mul_of_one_le_left this hΛ

end Witness

/-! ## 9. The instances at `d = 3`: `E2HypWG` nonempty, `lemDecCalE_wG` and `LemDecCalEwG_sum_sqrt_tail`
applied to it -/

section Instance

open RBM.Gauss.SizesInst RBM.Gauss.Step5Inst

private theorem lemDecCalEwG_inst_values :
    (sz0.L 1 = 8) ∧ (sz0.W 1 = 1024) ∧ (sz0.lam 1 = 1 / 4096) := by
  refine ⟨rfl, rfl, ?_⟩
  norm_num [sz0]

/-- **Nondegenerate instance (a) of `E2HypWG`** at `d = 3`: the preflight sequence `sz0` at `n = 1`
(`L = 8`, `W = 1024`, `lam = 1/4096`), `E = 1/2`, `u = 0`, `D = 38`, `Λ = K₀ = J = 1`, `M = 0`
(through `LemDecCalEwG_hyp_zero`).  Every numeric conjunct is discharged: `lam² W^d = 64 ≥ 1`,
`log 1024 ≥ 4` (`e⁴ < 1024`), the floor `(L^d W^{6d})² = 2^{378} ≤ 2^{380} = W^D`. -/
theorem LemDecCalEwG_inst :
    E2HypWG sz0 1 (1 / 2) 0 38 1 1 1
      (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) := by
  obtain ⟨hL, hW, hlam⟩ := lemDecCalEwG_inst_values
  have hWc : ((sz0.W 1 : ℕ) : ℝ) = 1024 := by rw [hW]; norm_num
  have hLc : ((sz0.L 1 : ℕ) : ℝ) = 8 := by rw [hL]; norm_num
  refine LemDecCalEwG_hyp_zero sz0 1 (by norm_num) (by norm_num [abs_of_pos]) ?_ ?_ ?_ le_rfl
    le_rfl ?_ ?_ le_rfl ?_
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
    have h : ((1024 : ℝ) ^ (38 : ℝ)) = (1024 : ℝ) ^ (38 : ℕ) := by
      rw [show (38 : ℝ) = ((38 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h]
    norm_num
  · rw [hWc]; norm_num

/-- **Nondegenerate instance (b) of `E2HypWG`** at `d = 3` with `L_n → ∞`: `szCL` at `n = 0`
(`L = 2·24⁵`, `W = 2²⁴`, `lam = 1`), `E = 1/2`, `u = 0`, `D = 42`, `Λ = 2`, `K₀ = J = 1`, `M = 0`.
The floor is `(L^3 W^{18})² ≈ 2^{1007.55} ≤ 2^{1008} = W^D`. -/
theorem LemDecCalEwG_inst_CL :
    E2HypWG szCL 0 (1 / 2) 0 42 2 1 1
      (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) := by
  have hlam : szCL.lam 0 = 1 := rfl
  refine LemDecCalEwG_hyp_zero szCL 0 (by norm_num) (by norm_num [abs_of_pos]) ?_ ?_ ?_
    (by norm_num) le_rfl ?_ ?_ le_rfl ?_
  · rw [hlam]; norm_num
  · rw [hlam]; norm_num
  · rw [hlam, szCL_W_real]; norm_num
  · rw [szCL_log_W]
    have := Real.log_two_gt_d9
    norm_num
    linarith
  · rw [szCL_L_real, szCL_W_real]
    have h : ((2 : ℝ) ^ (0 + 24)) ^ (42 : ℝ) = ((2 : ℝ) ^ (0 + 24)) ^ (42 : ℕ) := by
      rw [show (42 : ℝ) = ((42 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h]
    norm_num
  · rw [szCL_W_real]; norm_num

/-- The right side of `LemDecCalE_wG` is positive under `E2HypWG` (so an instance is not `0 ≤ 0`):
`lossE2wG > 0` (`lossE2 ≥ e (2 S_d + 1) > 0` and `1 + log P ≥ 1`), `(1-u)⁻¹ > 0`, the bracket is
`≥ (W^d|1-u|)^{-1/2} J^{3/2} > 0`, `T_{u,D} ≥ W^{-D} > 0`. -/
private theorem lemDecCalEwG_rhs_pos {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (h : E2HypWG sz n E u D Λ K₀ J M) (a : Fin 2 → Zd d (sz.L n)) :
    0 < lossE2wG d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ *
          ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
          STtailTD sz n u D a) := by
  obtain ⟨hW1, hM1, hMW, hlg, hstar, hWD⟩ := facts h
  have hconst := LemDecCalE_lk_const_le_lossE2 h.1
  obtain ⟨hE, -, -⟩ := h
  obtain ⟨hd3, hE', hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -, hLK, hK14, hK15⟩ := hE
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (sz.three_le_L n).trans' (by norm_num)
  have hxu : 0 < 1 - u := by linarith
  have hP1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) (one_le_pow₀ hW1.le)
  have hloss1 : 0 < lossE2 d (sz.L n) (sz.W n) Λ K₀ := by
    refine lt_of_lt_of_le ?_ hconst
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hS : (0 : ℝ) < 2 * (1 + 1536 * (d : ℝ) ^ 4) ^ d + 1 := by positivity
    exact mul_pos (Real.exp_pos 1) hS
  have hloss : 0 < lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
    unfold lossE2wG
    refine mul_pos hloss1 (mul_pos (by positivity) ?_)
    have := Real.log_nonneg hP1
    positivity
  have hT : 0 < STtailTD sz n u D a := by
    unfold STtailTD tailTD
    have := Real.rpow_pos_of_pos hW0 (-D)
    positivity
  have hbr : 0 < (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) +
      (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ) := by
    have h0 : 0 ≤ (if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) := by
      split_ifs <;> norm_num
    have hm : 0 < (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by
      rw [abs_of_pos hxu]; positivity
    have hJ : 0 < J := by linarith
    have := mul_pos (Real.rpow_pos_of_pos hm (1 / 2 : ℝ)) (Real.rpow_pos_of_pos hJ (3 / 2 : ℝ))
    linarith
  have hinv : 0 < (1 - u)⁻¹ := inv_pos.2 hxu
  exact mul_pos hloss (mul_pos (mul_pos hinv hbr) hT)

/-- **Check (ticket T2172), near branch: `lemDecCalE_wG` applied to the instance
`LemDecCalEwG_inst`** at `σ = (+,+)` and `a = (0, e₁)`, `e₁ = (1, 0, 0)`
(`|a₁ - a₂|_∞ = 1 ≤ ℓ* = (log 1024)^{3/2} ≥ 8`).  The left side is `0` (`G = m I` at `M = 0`);
the right side is positive (next `example`). -/
example :
    ‖STEGtM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
        ![true, true] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]‖ ≤
      lossE2wG 3 (sz0.L 1) (sz0.W 1) 1 1 * ((1 - (0 : ℝ))⁻¹ *
        ((if ((zdistInf 3 (sz0.L 1) (![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 0 -
              ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 1) : ℕ) : ℝ) ≤
            Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ)) *
        STtailTD sz0 1 0 38 ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]) :=
  lemDecCalE_wG 3 sz0 1 (1 / 2) 0 38 1 1 1 0 LemDecCalEwG_inst _ _

/-- The right side of the near-branch check is positive. -/
example : 0 < lossE2wG 3 (sz0.L 1) (sz0.W 1) 1 1 * ((1 - (0 : ℝ))⁻¹ *
        ((if ((zdistInf 3 (sz0.L 1) (![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 0 -
              ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 1) : ℕ) : ℝ) ≤
            Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ)) *
        STtailTD sz0 1 0 38 ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]) :=
  lemDecCalEwG_rhs_pos LemDecCalEwG_inst _

/-- **Check (ticket T2172), far branch: `lemDecCalE_wG` applied to the instance
`LemDecCalEwG_inst_CL`** at `σ = (+,-)` and `a = (0, 100 e₁)` (`100 > (24 log 2)^{3/2} ≈ 67.9`). -/
example :
    ‖STEGtM szCL 0 (1 / 2) 0
        (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ)
        ![true, false] ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100]‖ ≤
      lossE2wG 3 (szCL.L 0) (szCL.W 0) 2 1 * ((1 - (0 : ℝ))⁻¹ *
        ((if ((zdistInf 3 (szCL.L 0) (![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 0 -
              ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 1) : ℕ) : ℝ) ≤
            Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((szCL.W 0 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ)) *
        STtailTD szCL 0 0 42 ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100]) :=
  lemDecCalE_wG 3 szCL 0 (1 / 2) 0 42 2 1 1 0 LemDecCalEwG_inst_CL _ _

/-- The right side of the far-branch check is positive. -/
example : 0 < lossE2wG 3 (szCL.L 0) (szCL.W 0) 2 1 * ((1 - (0 : ℝ))⁻¹ *
        ((if ((zdistInf 3 (szCL.L 0) (![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 0 -
              ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 1) : ℕ) : ℝ) ≤
            Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((szCL.W 0 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * (1 : ℝ) ^ (3 / 2 : ℝ)) *
        STtailTD szCL 0 0 42 ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100]) :=
  lemDecCalEwG_rhs_pos LemDecCalEwG_inst_CL _

/-- On a one-coordinate point `|(c, 0, 0)|_∞ = |c|_L`. -/
private theorem lemDecCalEwG_zdistInf_single (L : ℕ) [NeZero L] (c : ZMod L) :
    zdistInf 3 L (Pi.single 0 c : Zd 3 L) = zdist L c := by
  apply le_antisymm
  · exact (zdistInf_le_zdistD 3 L _).trans (zdistD_single 0 c).le
  · have := lemDecCalEwG_zdist_le_zdistInf 3 L (Pi.single 0 c : Zd 3 L) 0
    simpa using this

/-- **The near branch is the one exercised at `LemDecCalEwG_inst`**: `a = (0, e₁)` has
`|a₁ - a₂|_∞ = 1 ≤ ℓ* = (log 1024)^{3/2}` (`ℓ* ≥ 8`). -/
example : ((zdistInf 3 (sz0.L 1) (![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 0 -
      ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 1) : ℕ) : ℝ) ≤
    Real.log ((sz0.W 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
  have h8 := (facts LemDecCalEwG_inst).2.2.2.2.1
  obtain ⟨hL, -, -⟩ := lemDecCalEwG_inst_values
  have hz : zdistInf 3 (sz0.L 1) (![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 0 -
      ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] 1) = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub]
    rw [lemDecCalEwG_zdistInf_neg, lemDecCalEwG_zdistInf_single]
    have h3 : 3 ≤ sz0.L 1 := by rw [hL]; norm_num
    exact zdist_one h3
  rw [hz]
  norm_num
  linarith

/-- **The far branch is the one exercised at `LemDecCalEwG_inst_CL`**: `a = (0, 100 e₁)` has
`|a₁ - a₂|_∞ = 100 > ℓ* = (24 log 2)^{3/2} ≈ 67.9` (`24 log 2 < 21`, `21^{3/2} < 100`). -/
example : ¬ (((zdistInf 3 (szCL.L 0) (![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 0 -
      ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 1) : ℕ) : ℝ) ≤
    Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by
  have hz : zdistInf 3 (szCL.L 0) (![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 0 -
      ![(0 : Zd 3 (szCL.L 0)), Pi.single 0 100] 1) = 100 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub]
    rw [lemDecCalEwG_zdistInf_neg, lemDecCalEwG_zdistInf_single]
    have hL : szCL.L 0 = 15925248 := by norm_num [szCL]
    unfold zdist
    have h100 : (100 : ZMod (szCL.L 0)) = ((100 : ℕ) : ZMod (szCL.L 0)) := by norm_num
    rw [h100, ZMod.val_cast_of_lt (by rw [hL]; norm_num), hL]
    norm_num
  rw [hz]
  have hlog : Real.log ((szCL.W 0 : ℕ) : ℝ) < 21 := by
    rw [szCL_log_W]
    have := Real.log_two_lt_d9
    norm_num
    linarith
  have h1 : Real.log ((szCL.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) < (21 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_lt_rpow (by rw [szCL_log_W]; have := Real.log_two_gt_d9; norm_num; linarith) hlog
      (by norm_num)
  have h2 : (21 : ℝ) ^ (3 / 2 : ℝ) < 100 := by
    rw [lemDecCalEwG_rpow_three_halves (by norm_num)]
    have : Real.sqrt 21 < 4.76 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    nlinarith
  push_cast
  linarith

/-- **Check (ticket T2172), `LemDecCalEwG_sum_sqrt_tail` at `d = 3`, `L = 8`**, `A = 2^{-60}`,
`w = 2^{-380}` (`w L^6 = 2^{-362} ≤ A`), `a₀ = 0`, `a₁ = e₁ = (1, 0, 0)`. -/
example :
    ∑ x : Zd 3 8, Real.sqrt ((2 : ℝ) ^ (-60 : ℤ) *
          Real.exp (-Real.sqrt (zdistInf 3 8 (x - Pi.single 0 1) : ℝ)) + (2 : ℝ) ^ (-380 : ℤ)) *
        Real.sqrt ((2 : ℝ) ^ (-60 : ℤ) *
          Real.exp (-Real.sqrt (zdistInf 3 8 ((0 : Zd 3 8) - x) : ℝ)) + (2 : ℝ) ^ (-380 : ℤ)) ≤
      5 * (1 + 24576 * ((3 : ℕ) : ℝ) ^ 4) ^ 3 * Real.sqrt ((2 : ℝ) ^ (-60 : ℤ)) *
        Real.sqrt ((2 : ℝ) ^ (-60 : ℤ) *
          Real.exp (-Real.sqrt (zdistInf 3 8 ((0 : Zd 3 8) - Pi.single 0 1) : ℝ)) +
            (2 : ℝ) ^ (-380 : ℤ)) :=
  LemDecCalEwG_sum_sqrt_tail (d := 3) (L := 8) (by norm_num) (A := (2 : ℝ) ^ (-60 : ℤ))
    (w := (2 : ℝ) ^ (-380 : ℤ)) (by positivity) (by positivity)
    (by
      have h : (2 : ℝ) ^ (-380 : ℤ) * ((8 : ℕ) : ℝ) ^ (2 * 3) = (2 : ℝ) ^ (-362 : ℤ) := by
        have h8 : ((8 : ℕ) : ℝ) ^ (2 * 3) = (2 : ℝ) ^ (18 : ℤ) := by norm_num
        rw [h8, ← zpow_add₀ (by norm_num)]; norm_num
      rw [h]
      exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)) 0 (Pi.single 0 1)

end Instance

end RBM.Path
