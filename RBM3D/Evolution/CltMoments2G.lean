/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltMoments2
import RBM3D.Chain.CltGen

/-!
# The CLT moment layer of Step 5 case (i) over the carrier (ticket T2479, X1b-1, targets 1-3)

Additive restatement of `Evolution/CltMoments1.lean:904-1031` (the weights) and of
`Evolution/CltMoments2.lean:78-225, 783-1208` (the vocabulary, the decomposition, the envelope, the weights, the fixed-`n`
moment bound and its eventual form) over a flow carrier `C : FlowFM sz` and a law `μ` (none of the four band files is edited).
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`, `lem;CLT`, proof `3_5:2182-2249`.  Mixed charges `σ 0 ≠ σ 1`
only (the range of `STThPropsg`); the propagator is the one of the carrier (`STThg`, one propagator, U-C4); the weights read
the propagator only through `STThPropsg` (shift, `(prop:ThfadC)`, `(prop:BD1)`), the loops through `CltRepg` and
`κ ≤ Im (C.m n)`.  No `|E| ≤ 2 - κ`, `‖m‖ = 1`, `PropSpin`, `Theta`, `seqP` in any generic statement (the
instance section, section 6, is at the band data); no coupling comparison (UBA-C1).

* **Target 1.** `cltMom1_weight_a1g`, `cltMom1_weight_a2g` (band `cltMom1_weight_a1` `:938`, `_a2` `:973`).
* **Target 2.** The vocabulary `CltMom2.Zg`, `flucg`, `offg`, `BYg`, `DomHypg`, `IsoHypg`, `rhsg` (band `:84-160`).
* **Target 3.** `cltMom2_decompg` (`:975`), `cltMom2_norm_stcltBg_le` (`:992`), `cltMom2_weightg_le` (`:1009`),
  `cltMom2_moment_fixedg` (`:1147`), `cltMom2_tail_eventuallyg` (`:1198`, from `STCltIsoConclgL`).  The loop envelope is
  `cltMom2G_LEnv`, derived from `CltRepg` and `κ ≤ Im (C.m n)` by `cltMom2G_lenv_of_rep`.

The model-free layers are reused by name: the moment engine `cltMom2_moment_le`, `cltMom2_markov`,
the comparability `cltMom2_hzu`, `meanFar_T1`.  The private band helpers `cltMom1_pow_add_one_ge`,
`cltMom2_sum_pair`, `cltMom2_eta`, `cltMom2_weight_algebra` come in by `open private`.  Ported from the
probe text `t/T2455:RBM3D/Probe/T2455Meas.lean:55-369` (X1-C5 measurement, never merged).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private cltMom1_pow_add_one_ge from RBM3D.Evolution.CltMoments1
open private cltMom2_sum_pair cltMom2_eta cltMom2_weight_algebra from RBM3D.Evolution.CltMoments2

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-! ## 1. The per-label weights from `STThPropsg` (target 1) -/

section Weights

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **Target 1a: the weight at `a₁`** (band `cltMom1_weight_a1`): from `STThPropsg` (shift, `(prop:ThfadC)`) and `meanFar_T1`,
in regime (i) `g²/L² ≤ 1 - t`: `g² |Θ_t(a, b)| ≤ C₀ (1 + 2^{d-1}) / (|a - b|_∞^{d-2} + 1)`. -/
theorem cltMom1_weight_a1g (hd : 3 ≤ d) (hTh : STThPropsg C) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n in atTop, ∀ (t : ℝ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → 0 < sz.lam n → 0 ≤ t → t < 1 →
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t → ∀ a b : Zd d (sz.L n),
        sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t a b‖ ≤
          C₀ * (1 + 2 ^ (d - 1)) / (((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ^ (d - 2) + 1) := by
  obtain ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, hC₆, hC₇, H⟩ := hTh
  refine ⟨C₅, hC₅, ?_⟩
  filter_upwards [H] with n hn t σ hσ hg ht0 ht1 hreg a b
  obtain ⟨hsh, -, hdec, -, -⟩ := hn t ht0 ht1 σ hσ
  have hT1 := meanFar_T1 hd (sz.three_le_L n) hg ht1 hreg hC₅.le hc₅
    (fun x => STThg C n (σ 0) (σ 1) t 0 x) hdec (b - a)
  rw [hsh a b]
  rw [cltMom1_zdistInf_sub_comm b a] at hT1
  set r : ℝ := ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hpow := cltMom1_pow_add_one_ge hr0 (show d - 2 ≠ 0 by omega)
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  calc sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t 0 (b - a)‖
      ≤ sz.lam n ^ 2 * ((C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2) / (r + 1) ^ (d - 2)) :=
        mul_le_mul_of_nonneg_left hT1 hg2.le
    _ = C₅ * (1 + 2 ^ (d - 1)) / (r + 1) ^ (d - 2) := by field_simp
    _ ≤ C₅ * (1 + 2 ^ (d - 1)) / (r ^ (d - 2) + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow

/-- **Target 1b: the weight at `a₂`** (band `cltMom1_weight_a2`): from `STThPropsg` (shift, `(prop:BD1)`),
for `|b₁ - b₂|_∞ ≤ w`, `2 d w ≤ ρ < |a₂ - b₁|_∞`:
`g² |Θ_t(b₂, a₂) - Θ_t(b₁, a₂)| ≤ C₀ d w / (|a₂ - b₁|_∞^{d-1} + 1)`. -/
theorem cltMom1_weight_a2g (hd : 3 ≤ d) (hTh : STThPropsg C) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n in atTop, ∀ (t : ℝ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → 0 < sz.lam n → 0 ≤ t → t < 1 →
      ∀ a₂ b₁ b₂ : Zd d (sz.L n), ∀ w ρ : ℝ, 2 * d * w ≤ ρ → ρ < ((zdistInf d (sz.L n) (a₂ - b₁) : ℕ) : ℝ) →
        ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ≤ w →
        sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t b₂ a₂ - STThg C n (σ 0) (σ 1) t b₁ a₂‖ ≤
          C₀ * d * w / (((zdistInf d (sz.L n) (a₂ - b₁) : ℕ) : ℝ) ^ (d - 1) + 1) := by
  obtain ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, hC₆, hC₇, H⟩ := hTh
  refine ⟨C₆, hC₆, ?_⟩
  filter_upwards [H] with n hn t σ hσ hg ht0 ht1 a₂ b₁ b₂ w ρ hρw ha hr
  obtain ⟨hsh, -, -, hBD, -⟩ := hn t ht0 ht1 σ hσ
  set a : Zd d (sz.L n) := a₂ - b₁ with hadef
  set r : Zd d (sz.L n) := b₁ - b₂ with hrdef
  have hsum : a + r = a₂ - b₂ := by rw [hadef, hrdef]; exact sub_add_sub_cancel a₂ b₁ b₂
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrD : (zdistD d (sz.L n) r : ℝ) ≤ d * w := by
    have h1 : ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ ((d * zdistInf d (sz.L n) r : ℕ) : ℝ) := by
      exact_mod_cast zdistD_le_mul_zdistInf d (sz.L n) r
    push_cast at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hr hd0)
  have haD : ((zdistInf d (sz.L n) a : ℕ) : ℝ) ≤ (zdistD d (sz.L n) a : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d (sz.L n) a
  have hBD' := hBD a r (by linarith)
  have e1 : STThg C n (σ 0) (σ 1) t b₂ a₂ = STThg C n (σ 0) (σ 1) t 0 (a + r) := by rw [hsh b₂ a₂, hsum]
  have e2 : STThg C n (σ 0) (σ 1) t b₁ a₂ = STThg C n (σ 0) (σ 1) t 0 a := by rw [hsh b₁ a₂]
  rw [e1, e2]
  set A : ℝ := ((zdistInf d (sz.L n) a : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hpow := cltMom1_pow_add_one_ge hA0 (show d - 1 ≠ 0 by omega)
  have hpow2 : (A + 1) ^ (d - 1) ≤ ((zdistD d (sz.L n) a : ℝ) + 1) ^ (d - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hden : 0 < sz.lam n ^ 2 + |1 - t| := by positivity
  have hfac : sz.lam n ^ 2 * (sz.lam n ^ 2 + |1 - t|)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hden]
    linarith [abs_nonneg (1 - t)]
  have hinv : (((zdistD d (sz.L n) a : ℝ) + 1) ^ (d - 1))⁻¹ ≤ 1 / (A ^ (d - 1) + 1) := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (hpow.trans hpow2)
  have hr0 : (0 : ℝ) ≤ zdistD d (sz.L n) r := Nat.cast_nonneg _
  have hw0 : 0 ≤ w := le_trans (Nat.cast_nonneg _) hr
  calc sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t 0 (a + r) - STThg C n (σ 0) (σ 1) t 0 a‖
      ≤ sz.lam n ^ 2 * (C₆ * (sz.lam n ^ 2 + |1 - t|)⁻¹ * (zdistD d (sz.L n) r : ℝ) *
          (((zdistD d (sz.L n) a : ℝ) + 1) ^ (d - 1))⁻¹) := mul_le_mul_of_nonneg_left hBD' hg2.le
    _ = C₆ * (sz.lam n ^ 2 * (sz.lam n ^ 2 + |1 - t|)⁻¹) * (zdistD d (sz.L n) r : ℝ) *
          (((zdistD d (sz.L n) a : ℝ) + 1) ^ (d - 1))⁻¹ := by ring
    _ ≤ C₆ * 1 * (d * w) * (1 / (A ^ (d - 1) + 1)) := by gcongr
    _ = C₆ * d * w / (A ^ (d - 1) + 1) := by ring

end Weights

/-! ## 2. The vocabulary over `(C, μ)` (target 2) -/

section Vocab

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The weight of a two-label index `β` in `(eq:2p_product)`** (`3_5:2218`; band `CltMom2.Z`, `CltMoments2:84`):
`g² Θ_t(a₁, β₀) · g² (Θ_t(β₁, a₂) - Θ_t(β₀, a₂))` on the region `(eq:sumregionsforb)` (`3_5:2220`), with the carrier propagator
(`= T2455Meas:55`). -/
def CltMom2.Zg (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a β : Fin 2 → Zd d (sz.L n)) : ℂ :=
  if Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (β 0 - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (β 0 - a 1) : ℕ) : ℝ) ∧
      ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s then
    (((sz.lam n ^ 2 : ℝ) : ℂ) * STThg C n (σ 0) (σ 1) t (a 0) (β 0)) *
      (((sz.lam n ^ 2 : ℝ) : ℂ) * (STThg C n (σ 0) (σ 1) t (β 1) (a 1) - STThg C n (σ 0) (σ 1) t (β 0) (a 1)))
  else 0

/-- **The window fluctuation** `Σ_β Z_β (𝗕_β - 𝔼𝗕_β)` (band `CltMom2.fluc`). -/
def CltMom2.flucg (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  ∑ β : Fin 2 → Zd d (sz.L n), CltMom2.Zg C n s t σ a β * STcltXg C μ n s σ β false ω

open Classical in
/-- **The off-window part** of `f^{far} - 𝔼 f^{far}` (band `CltMom2.off`): `𝓑 - 𝔼𝓑` with `𝓑 = 𝓛 - 𝒦` of the carrier. -/
def CltMom2.offg (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ ∈ Finset.univ.filter (fun b₂ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ)),
      STThg C n (σ 0) (σ 1) t (a 0) b₁ *
        ((C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) - ∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ) *
        (STThg C n (σ 0) (σ 1) t b₂ (a 1) - STThg C n (σ 0) (σ 1) t b₁ (a 1))

/-- **The deterministic envelope of `𝗕`**: `A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)` (band `CltMom2.BY`). -/
def CltMom2.BYg (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) : ℝ :=
  (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) *
    ((etaOf (C.m n) s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖C.K n s σ β‖)

/-- **The per-label tail of the profile-normalised `𝗕` on the window** at one `n` (band `CltMom2.DomHyp`). -/
def CltMom2.DomHypg (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (Λ' q₁ : ℝ) : Prop :=
  ∀ β : Fin 2 → Zd d (sz.L n),
    ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s →
    μ {ω | Λ' < ‖STcltBg C n s σ β ω‖ * (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤ ENNReal.ofReal q₁

/-- **The isolation bound at one `n`** (`(eq:bound_isolated)`, band `CltMom2.IsoHyp`): the inner clause of `STCltIsoConclgL`. -/
def CltMom2.IsoHypg (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (p : ℕ) (εf : ℝ) : Prop :=
  ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
    (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) →
    (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s ≤
      ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
    ‖∫ ω, ∏ k : Fin (2 * p), STcltXg C μ n s σ (b k) (decide (p ≤ k.val)) ω ∂μ‖ ≤ εf

/-- **The right side of the `2p`-th moment bound** (band `CltMom2.rhs`). -/
def CltMom2.rhsg (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (p : ℕ) (M Λ' q₁ εf : ℝ) : ℝ :=
  2 ^ (2 * p) * (Λ' ^ (2 * p) +
      (CltMom2.BYg C n s σ *
          ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)) ^ (2 * p) *
        (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) * q₁) *
    (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
      ((CltMom1.Cd d * M * Real.log ((sz.W n : ℕ) : ℝ) ^ 12) ^ (2 * p) *
        (ellT (sz.L n) (sz.lam n) s ^ 4 /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
  εf * (∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Zg C n s t σ a β‖) ^ (2 * p)

/-- The loop envelope at one `(n, u)`: the loops `𝓛^{(2)}_{u,σ,a}` of the carrier are measurable and bounded by `η_u^{-2}`
(generic `walk_measurable_Lloop`, `norm_Lloop_le`; replaces `|E| < 2`, `u < 1`). -/
def cltMom2G_LEnv (n : ℕ) (u : ℝ) : Prop := ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
  Measurable (fun ω => C.L n u σ a ω) ∧ ∀ ω, ‖C.L n u σ a ω‖ ≤ (etaOf (C.m n) u)⁻¹ ^ 2

/-- `CltRepg` and `κ ≤ Im (C.m n)` give the loop envelope for every `u < 1` (probe `lenv_of_rep`, `T2455Meas:72`). -/
theorem cltMom2G_lenv_of_rep {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1) :
    cltMom2G_LEnv C n u := by
  intro σ a
  have hη : 0 < etaOf (C.m n) u := mul_pos (sub_pos.2 hu) (lt_of_lt_of_le hκ hm)
  have hmeas : Measurable fun ω : sz.SeqΩ => H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) =>
      Sizes.seqHflow (sz.withLam g') n u ω i j :=
    Measurable.of_eval_matrix _ fun i j => measurable_const.add (Sizes.measurable_seqHflow_entry (sz.withLam g') n u i j)
  refine ⟨?_, fun ω => ?_⟩
  · rw [funext fun ω => (hrep.2.2 n u ω).2 2 σ a]
    exact (walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (C.m n) (E n) u) σ a).comp hmeas
  · rw [(hrep.2.2 n u ω).2 2 σ a]
    exact norm_loopM_le d (sz.L n) (sz.W n) (((hrep.2.1 n).add (Sizes.seqHflow_isHermitian (sz.withLam g') n u ω)).submatrix _)
      hη (by rw [ztOf_im, abs_of_pos hη]) (n := 1) σ a

end Vocab

/-! ## 3. The decomposition of `f^{far} - 𝔼 f^{far}` (target 3a) -/

section Decomp

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]

/-- The entries `𝓛 - 𝒦` of the single-time flow are integrable under the loop envelope (band `cltMom2_integrable_LK`). -/
private theorem cltMom2G_integrable_LK (n : ℕ) {s : ℝ} (hL : cltMom2G_LEnv C n s)
    (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) :
    Integrable (fun ω => C.L n s σ b ω - C.K n s σ b) μ :=
  (Integrable.of_bound (hL σ b).1.aestronglyMeasurable ((etaOf (C.m n) s)⁻¹ ^ 2)
    (Filter.Eventually.of_forall fun ω => (hL σ b).2 ω)).sub (integrable_const _)

open Classical in
/-- **The mean of `f^{far}`**: `𝔼 f^{far}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑` (`3_5:2192`; band `cltMom2_integral_fFar`). -/
private theorem cltMom2G_integral_fFar (n : ℕ) {s t : ℝ} (hL : cltMom2G_LEnv C n s)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∫ ω, STfFarg C n s t σ a ω ∂μ =
      (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
        ∑ b₂ : Zd d (sz.L n),
          STThg C n (σ 0) (σ 1) t (a 0) b₁ * (∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ) *
            (STThg C n (σ 0) (σ 1) t b₂ (a 1) - STThg C n (σ 0) (σ 1) t b₁ (a 1)) := by
  unfold STfFarg
  have hX := fun b₁ b₂ : Zd d (sz.L n) => cltMom2G_integrable_LK C μ n hL σ ![b₁, b₂]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun b₁ _ => integrable_finsetSum _
    (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _))]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [integral_finsetSum _ (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _)]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- `STcltXg … false = A^{6/5} (𝓛 - 𝒦 - 𝔼(𝓛 - 𝒦))` (band `cltMom2_stcltX_false`). -/
private theorem cltMom2G_stcltX_false (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STcltXg C μ n s σ b false ω =
      (((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) : ℝ) : ℂ) *
        ((C.L n s σ b ω - C.K n s σ b) - ∫ ω', (C.L n s σ b ω' - C.K n s σ b) ∂μ) := by
  unfold STcltXg STcltBg
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [integral_const_mul]
  ring

/-- The summand `Θ_{a₁b₁} (𝓑 - 𝔼𝓑)_{b₁b₂} (Θ_{b₂a₂} - Θ_{b₁a₂})` of `f^{far} - 𝔼 f^{far}` (`3_5:2213-2220`). -/
private def cltMom2G_T (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    (b₁ b₂ : Zd d (sz.L n)) : ℂ :=
  STThg C n (σ 0) (σ 1) t (a 0) b₁ *
    ((C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) - ∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ) *
    (STThg C n (σ 0) (σ 1) t b₂ (a 1) - STThg C n (σ 0) (σ 1) t b₁ (a 1))

open Classical in
/-- The termwise identity: the window part plus the off-window part is the full summand on the far set (band `cltMom2_term`). -/
private theorem cltMom2G_term (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hg : 0 < sz.lam n) (ω : sz.SeqΩ) (u₀ u₁ : Zd d (sz.L n)) :
    (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * (CltMom2.Zg C n s t σ a ![u₀, u₁] * STcltXg C μ n s σ ![u₀, u₁] false ω) +
      (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ)) then cltMom2G_T C μ n s t σ a ω u₀ u₁ else 0) else 0) =
      (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then cltMom2G_T C μ n s t σ a ω u₀ u₁ else 0) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hA : (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) ≠ 0 := by positivity
  by_cases hf : (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ))
  · by_cases hw : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ))
    · have hZ : CltMom2.Zg C n s t σ a ![u₀, u₁] = 0 := by
        unfold CltMom2.Zg
        split_ifs with h
        · exact absurd hw (not_lt.2 h.2.2)
        · rfl
      simp only [hZ, hf, hw, and_self, ↓reduceIte, mul_zero, zero_mul, zero_add]
    · have hw' : ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ) ≤
          Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s := not_lt.1 hw
      have hZ : CltMom2.Zg C n s t σ a ![u₀, u₁] =
          (((sz.lam n ^ 2 : ℝ) : ℂ) * STThg C n (σ 0) (σ 1) t (a 0) u₀) *
            (((sz.lam n ^ 2 : ℝ) : ℂ) * (STThg C n (σ 0) (σ 1) t u₁ (a 1) - STThg C n (σ 0) (σ 1) t u₀ (a 1))) := by
        unfold CltMom2.Zg
        split_ifs with h
        · rfl
        · exact absurd ⟨hf.1, hf.2, hw'⟩ h
      rw [hZ, cltMom2G_stcltX_false]
      simp only [hf, hw, and_self, ↓reduceIte]
      rw [cltMom2_weight_algebra (sz.lam n) _ s hg.ne' hA, mul_zero, add_zero]
      rfl
  · have hZ : CltMom2.Zg C n s t σ a ![u₀, u₁] = 0 := by
      unfold CltMom2.Zg
      split_ifs with h
      · exact absurd ⟨h.1, h.2.1⟩ hf
      · rfl
    simp only [hZ, hf, ↓reduceIte, mul_zero, zero_mul, zero_add]

open Classical in
/-- `f^{far} - 𝔼 f^{far}` as a double sum over the far set (band `cltMom2_lhs`). -/
private theorem cltMom2G_lhs (n : ℕ) {s t : ℝ} (hL : cltMom2G_LEnv C n s) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STfFarg C n s t σ a ω - ∫ ω', STfFarg C n s t σ a ω' ∂μ =
      ∑ u₀ : Zd d (sz.L n), ∑ u₁ : Zd d (sz.L n),
        (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then cltMom2G_T C μ n s t σ a ω u₀ u₁ else 0) := by
  rw [cltMom2G_integral_fFar C μ n hL σ a]
  unfold STfFarg
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  by_cases hf : (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ))
  · simp only [hf]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    simp only [and_self, ↓reduceIte]
    unfold cltMom2G_T STThg
    ring
  · simp [hf]

open Classical in
/-- `c · fluc` as a double sum: the reindexing `β = ![u₀, u₁]` (band `cltMom2_fluc_eq`). -/
private theorem cltMom2G_fluc_eq (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * CltMom2.flucg C μ n s t σ a ω =
      ∑ u₀ : Zd d (sz.L n), ∑ u₁ : Zd d (sz.L n),
        (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * (CltMom2.Zg C n s t σ a ![u₀, u₁] * STcltXg C μ n s σ ![u₀, u₁] false ω) := by
  unfold CltMom2.flucg
  have hβ : ∀ β : Fin 2 → Zd d (sz.L n), CltMom2.Zg C n s t σ a β * STcltXg C μ n s σ β false ω =
      (fun u₀ u₁ : Zd d (sz.L n) => CltMom2.Zg C n s t σ a ![u₀, u₁] * STcltXg C μ n s σ ![u₀, u₁] false ω)
        (β 0) (β 1) := fun β => by
    simp only []
    rw [← cltMom2_eta β]
  rw [Finset.sum_congr rfl fun β _ => hβ β, cltMom2_sum_pair
    (fun u₀ u₁ : Zd d (sz.L n) => CltMom2.Zg C n s t σ a ![u₀, u₁] * STcltXg C μ n s σ ![u₀, u₁] false ω),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  rw [Finset.mul_sum]

open Classical in
/-- `CltMom2.offg` as a double sum (band `cltMom2_off_eq`). -/
private theorem cltMom2G_off_eq (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    CltMom2.offg C μ n s t σ a ω =
      ∑ u₀ : Zd d (sz.L n), ∑ u₁ : Zd d (sz.L n),
        (((1 - s) ^ 2 : ℝ) : ℂ) * (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ)) then (if (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ)) then cltMom2G_T C μ n s t σ a ω u₀ u₁ else 0) else 0) := by
  unfold CltMom2.offg
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  by_cases hf : (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 0) : ℕ) : ℝ) ∧ Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - a 1) : ℕ) : ℝ))
  · simp only [hf]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    by_cases hw : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (u₀ - u₁) : ℕ) : ℝ))
    · simp only [hw, and_self, ↓reduceIte, cltMom2G_T]
    · simp [hw]
  · simp [hf]

open Classical in
/-- **Target 3a: the decomposition** `f^{far} - 𝔼 f^{far} = (1-s)²/(g⁴ A^{6/5}) · fluc + off` (`3_5:2213-2220`; band
`cltMom2_decomp`), under the loop envelope at `(n, s)`. -/
theorem cltMom2_decompg (n : ℕ) (s t : ℝ) (hL : cltMom2G_LEnv C n s) (hg : 0 < sz.lam n) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STfFarg C n s t σ a ω - ∫ ω', STfFarg C n s t σ a ω' ∂μ =
      (((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.flucg C μ n s t σ a ω + CltMom2.offg C μ n s t σ a ω := by
  rw [cltMom2G_lhs C μ n hL σ a ω, cltMom2G_off_eq C μ n s t σ a ω, cltMom2G_fluc_eq C μ n s t σ a ω,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u₁ _ => ?_
  exact (cltMom2G_term C μ n s t σ a hg ω u₀ u₁).symm

end Decomp

/-! ## 4. The deterministic inputs (target 3b, 3c) -/

section Deterministic

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **Target 3b: the envelope of `𝗕`** (band `cltMom2_norm_stcltB_le`): `|𝗕_β| ≤ A^{6/5} (η_s^{-2} + Σ_β |𝒦^{(2)}_{s,σ,β}|)`
under the loop envelope at `(n, s)`. -/
theorem cltMom2_norm_stcltBg_le (n : ℕ) {s : ℝ} (hL : cltMom2G_LEnv C n s) (σ : Fin 2 → Bool)
    (β : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ‖STcltBg C n s σ β ω‖ ≤ CltMom2.BYg C n s σ := by
  have hA : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) := by positivity
  unfold STcltBg CltMom2.BYg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hA]
  refine mul_le_mul_of_nonneg_left ?_ hA
  have h1 : ‖C.L n s σ β ω - C.K n s σ β‖ ≤ (etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ β‖ :=
    (norm_sub_le _ _).trans (add_le_add ((hL σ β).2 ω) le_rfl)
  have h2 : ‖C.K n s σ β‖ ≤ ∑ β' : Fin 2 → Zd d (sz.L n), ‖C.K n s σ β'‖ :=
    Finset.single_le_sum (f := fun β' : Fin 2 → Zd d (sz.L n) => ‖C.K n s σ β'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ β)
  linarith

/-- **Target 3c: the weights of `(eq:2p_product_pair)`** (band `cltMom2_weight_le`), eventually in `n`, from `STThPropsg`
(`(prop:ThfadC)`, `(prop:BD1)`; targets 1a, 1b): `|Z_β| (|β₀-β₁|^{d-2}+1)^{-1} ≤ u(β₀) G_w(β₀ - β₁)`, `M = C₅ (1 + 2^{d-1}) C₆ d`.
The constants are those of `STThPropsg`; no `Λ`, `κ`. -/
theorem cltMom2_weightg_le (hd : 3 ≤ d) (hTh : STThPropsg C) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, ∀ (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), σ 0 ≠ σ 1 →
      0 < sz.lam n → 0 ≤ t → t < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t →
      2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → ∀ β : Fin 2 → Zd d (sz.L n),
        ‖CltMom2.Zg C n s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
          CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s)
              (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) M (β 0) *
            CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1) := by
  obtain ⟨C₅, hC₅, H₅⟩ := cltMom1_weight_a1g C hd hTh
  obtain ⟨C₆, hC₆, H₆⟩ := cltMom1_weight_a2g C hd hTh
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hMpos : 0 < C₅ * (1 + 2 ^ (d - 1)) * C₆ * d := by positivity
  refine ⟨C₅ * (1 + 2 ^ (d - 1)) * C₆ * d, hMpos, ?_⟩
  filter_upwards [H₅, H₆] with n h5n h6n s t σ a hσ hg ht0 ht1 hreg hlw β
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
  have hd1 : (1 : ℝ) ≤ 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  have hlw1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := hd1.trans hlw
  have hw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s := by
    have : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  have hbd1 := cltMom1_scale_bd1 (d := d) hlw (show 0 ≤ ellT (sz.L n) (sz.lam n) s by linarith)
  have hnn : 0 ≤ CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s)
        (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (C₅ * (1 + 2 ^ (d - 1)) * C₆ * d) (β 0) *
      CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1) :=
    mul_nonneg (CltMom1.uw_nonneg hw0 hMpos.le _) (CltMom1.G_nonneg _ _)
  by_cases hc : Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - a 1) : ℕ) : ℝ) ∧
      ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s
  · obtain ⟨hc1, hc2, hc3⟩ := hc
    have hZ : CltMom2.Zg C n s t σ a β =
        (((sz.lam n ^ 2 : ℝ) : ℂ) * STThg C n (σ 0) (σ 1) t (a 0) (β 0)) *
          (((sz.lam n ^ 2 : ℝ) : ℂ) * (STThg C n (σ 0) (σ 1) t (β 1) (a 1) - STThg C n (σ 0) (σ 1) t (β 0) (a 1))) := by
      unfold CltMom2.Zg
      split_ifs with h
      · rfl
      · exact absurd ⟨hc1, hc2, hc3⟩ h
    have h1 := h5n t σ hσ hg ht0 ht1 hreg (a 0) (β 0)
    have hfar2 : Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (a 1 - β 0) : ℕ) : ℝ) := by
      rw [cltMom1_zdistInf_sub_comm]; exact hc2
    have h2 := h6n t σ hσ hg ht0 ht1 (a 1) (β 0) (β 1)
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s)
      (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s) hbd1 hfar2 hc3
    have hnorm : ‖CltMom2.Zg C n s t σ a β‖ =
        (sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (a 0) (β 0)‖) *
          (sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (β 1) (a 1) - STThg C n (σ 0) (σ 1) t (β 0) (a 1)‖) := by
      rw [hZ, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ sz.lam n ^ 2)]
    have hfar1 : Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (a 0 - β 0) : ℕ) : ℝ) := by
      rw [cltMom1_zdistInf_sub_comm]; exact hc1
    have hq : 0 < ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
    have hA1 : 0 < ((zdistInf d (sz.L n) (a 0 - β 0) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
    have hA2 : 0 < ((zdistInf d (sz.L n) (a 1 - β 0) : ℕ) : ℝ) ^ (d - 1) + 1 := by positivity
    have hg2 : 0 ≤ sz.lam n ^ 2 := by positivity
    simp only [CltMom1.uw, CltMom1.G, hfar1, hfar2, hc3, and_self, ↓reduceIte]
    rw [hnorm]
    calc (sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (a 0) (β 0)‖) *
          (sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (β 1) (a 1) - STThg C n (σ 0) (σ 1) t (β 0) (a 1)‖) *
          (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1))
        ≤ (C₅ * (1 + 2 ^ (d - 1)) / (((zdistInf d (sz.L n) (a 0 - β 0) : ℕ) : ℝ) ^ (d - 2) + 1)) *
          (C₆ * d * (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) /
            (((zdistInf d (sz.L n) (a 1 - β 0) : ℕ) : ℝ) ^ (d - 1) + 1)) *
          (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
      _ = _ := by ring
  · have hZ0 : CltMom2.Zg C n s t σ a β = 0 := by
      unfold CltMom2.Zg
      split_ifs with h
      · exact absurd h hc
      · rfl
    rw [hZ0, norm_zero, zero_mul]
    exact hnn

end Deterministic

/-! ## 5. The fixed-`n` moment bound and its eventual form (target 3d, 3e) -/

section Fixed

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **Target 3d: the `2p`-th moment bound `(eq:main_challenge3)` of the window fluctuation at one `n`, and Markov** (band
`cltMom2_moment_fixed`, `:1147`): `cltMom2_moment_le`, `cltMom2_markov` at `Y = STcltBg C n s σ` (measurable and bounded by the loop
envelope), `Z = CltMom2.Zg`, `w = (log W)³ ℓ_s`, `ρ = (log W)⁴ ℓ_s`; `hzu` from the pointwise weights `hW` (target 3c, constant `M₀`)
and `cltMom2_hzu` with `M = 4^d M₀`. -/
theorem cltMom2_moment_fixedg [IsProbabilityMeasure μ] (hd : 3 ≤ d) {M₀ : ℝ} (hM₀ : 0 < M₀) (n : ℕ) {s : ℝ} (t : ℝ)
    (hL : cltMom2G_LEnv C n s) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (p : ℕ) (Λ' q₁ εf : ℝ)
    (h40 : (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hq₁ : 0 ≤ q₁) (hεf : 0 ≤ εf)
    (hW : ∀ β : Fin 2 → Zd d (sz.L n),
      ‖CltMom2.Zg C n s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
        CltMom1.uw (a 0) (a 1) (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s)
            (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) M₀ (β 0) *
          CltMom1.G d (sz.L n) (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) (β 0 - β 1))
    (hdom : CltMom2.DomHypg C μ n s σ Λ' q₁) (hiso : CltMom2.IsoHypg C μ n s σ p εf) :
    ∫ ω, ‖CltMom2.flucg C μ n s t σ a ω‖ ^ (2 * p) ∂μ ≤ CltMom2.rhsg C n s t σ a p ((4 : ℝ) ^ d * M₀) Λ' q₁ εf ∧
      ∀ θ : ℝ, 0 < θ → μ {ω | θ < ‖CltMom2.flucg C μ n s t σ a ω‖} ≤
        ENNReal.ofReal (CltMom2.rhsg C n s t σ a p ((4 : ℝ) ^ d * M₀) Λ' q₁ εf / θ ^ (2 * p)) := by
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hlw1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s := by
    have : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  have hscale : 40 * (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ≤
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s := by
    have := cltMom1_scale_comparable (lw := Real.log ((sz.W n : ℕ) : ℝ)) (ℓ := ellT (sz.L n) (sz.lam n) s) (p := 1)
      (by simpa using h40) (by linarith)
    push_cast at this
    linarith
  have hz0 : ∀ β : Fin 2 → Zd d (sz.L n), 0 ≤ ‖CltMom2.Zg C n s t σ a β‖ *
      (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := fun β => by positivity
  have hzu := cltMom2_hzu d (sz.L n) (a 0) (a 1)
    (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s)
    (Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s) M₀
    (fun β => ‖CltMom2.Zg C n s t σ a β‖ * (1 / (((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)))
    (by omega) hw0 hscale hM₀.le hz0 hW
  have hYm : ∀ β : Fin 2 → Zd d (sz.L n), Measurable (STcltBg C n s σ β) := fun β =>
    measurable_const.mul ((hL σ β).1.sub measurable_const)
  have hYB : ∀ β ω, ‖STcltBg C n s σ β ω‖ ≤ CltMom2.BYg C n s σ :=
    fun β ω => cltMom2_norm_stcltBg_le C n hL σ β ω
  have hZ : ∀ β : Fin 2 → Zd d (sz.L n),
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) → CltMom2.Zg C n s t σ a β = 0 := by
    intro β hβ
    unfold CltMom2.Zg
    split_ifs with h
    · exact absurd hβ (not_lt.2 h.2.2)
    · rfl
  refine ⟨?_, fun θ hθ => ?_⟩
  · exact cltMom2_moment_le (P := μ) (Y := STcltBg C n s σ) hd p hlw1 hℓ1 (by positivity) hq₁ hεf (a 0) (a 1)
      hYm hYB (CltMom2.Zg C n s t σ a) hZ hzu hdom hiso
  · exact cltMom2_markov (P := μ) (Y := STcltBg C n s σ) hd p hlw1 hℓ1 (by positivity) hq₁ hεf (a 0) (a 1)
      hYm hYB (CltMom2.Zg C n s t σ a) hZ hzu hdom hiso θ hθ

/-- **Target 3e: the eventual form from `STCltIsoConclgL`** (band `cltMom2_tail_eventually`, `:1198`; `εf = W^{-D}`): the Markov half of
`cltMom2_moment_fixedg` with `M = 4^d M₀`, `M₀` the constant of the weights (`cltMom2_weightg_le`).  The loop envelope is derived from
`CltRepg` and `κ ≤ Im (C.m n)`; the only `∀ᶠ n` are those of `STCltIsoConclgL` and `STThPropsg`.  The input of the far step. -/
theorem cltMom2_tail_eventuallyg {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    {κ : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hrep : CltRepg C μ H₀ g' E) (hTh : STThPropsg C) {s : ℕ → ℝ}
    (hiso : STCltIsoConclgL C μ s) (t : ℕ → ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
      ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)) (Λ' q₁ θ : ℝ),
        κ ≤ (C.m n).im → 0 < sz.lam n → s n < 1 → 0 ≤ t n → t n < 1 →
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n →
        (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) → 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) →
        0 ≤ q₁ → CltMom2.DomHypg C μ n (s n) σ Λ' q₁ → 0 < θ →
        μ {ω | θ < ‖CltMom2.flucg C μ n (s n) (t n) σ a ω‖} ≤
          ENNReal.ofReal (CltMom2.rhsg C n (s n) (t n) σ a p M Λ' q₁ (((sz.W n : ℕ) : ℝ) ^ (-D)) / θ ^ (2 * p)) := by
  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
  obtain ⟨M₀, hM₀, HW⟩ := cltMom2_weightg_le C hd hTh
  refine ⟨(4 : ℝ) ^ d * M₀, by positivity, ?_⟩
  intro p hp D hD
  filter_upwards [hiso p hp D hD, HW] with n hn hWn σ hσ a Λ' q₁ θ hκm hg hs ht0 ht1 hreg h40 h2d hq₁ hdom hθ
  exact (cltMom2_moment_fixedg C μ hd hM₀ n (t n) (cltMom2G_lenv_of_rep C μ hrep hκ n hκm hs) σ a p Λ' q₁ _ h40 hq₁
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hWn (s n) (t n) σ a hσ hg ht0 ht1 hreg h2d) hdom (hn σ hσ)).2 θ hθ

end Fixed

/-! ## 6. Compiled nonempty instances (`d = 3`, band data of `Step5Inst`: `szCL`, `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL`, `tCL`)

`HCltOf` is `cltGood_hCltOf_szCL` (only the Step 2 pins `STLocalEntryUgL`, `STGdecayWgL` stay hypotheses, another gate), `STCltIsoConclgL`
is `stCltIsogL_holds` (X1a), and `STThPropsg` at the band data is the private `cltMom2G_chk_Th` (the statement of the second row's
target 7a, proved here for the instances only). -/

section Instances

open RBM.Gauss.Step5Inst

private theorem cltMom2G_chk_H
    (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
    HCltOf (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) (fun _ => 0) szCL.lam (STflowE zCL)
      (1 / 2) (1 / 10) (1 / 6) (1 / 10) 1 sCL tCL := cltGood_hCltOf_szCL hLoc hDec

/-- The band producer of `STThPropsg` (the statement of the second row's target 7a, `bandFM_STThPropsg`), proved here for the instances only
(private; `prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds` at `Λ = 𝔡⁻¹`, `c = 1/2`, `κ' = min κ (1/2)`, `bandFM_STThg`). -/
private theorem cltMom2G_chk_Th {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E : ℕ → ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ) : STThPropsg (bandFM sz E) := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hκ'0 : 0 < min κ (1 / 2) := lt_min hκ (by norm_num)
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd hΛ
  obtain ⟨C₆, hC₆, H6⟩ := prop6Diff1_holds d 𝔡⁻¹ (min κ (1 / 2)) (1 / 2) hd hΛ hκ'0 (by norm_num) (by norm_num)
  obtain ⟨C₇, hC₇, H7⟩ := prop7Diff2_holds d 𝔡⁻¹ (min κ (1 / 2)) (1 / 2) hd hΛ hκ'0 (by norm_num) (by norm_num)
  refine ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, hC₆, hC₇, ?_⟩
  filter_upwards [hWO] with n hWOn t ht0 ht1 σ hσ
  obtain ⟨hWO1, hWO2⟩ := hWOn
  have hL := sz.three_le_L n
  have hg : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hWO1
  have hEn : |E n| < 2 := by have := hE n; linarith
  have hκ' : min κ (1 / 2) ≤ (mE (E n)).im := by
    rw [mE_im]
    have hE2 : (E n) ^ 2 ≤ (2 - min κ (1 / 2)) ^ 2 := by
      have h1 := abs_le.1 (hE n)
      have h2 : min κ (1 / 2) ≤ κ := min_le_left _ _
      exact sq_le_sq' (by linarith [h1.1]) (by linarith [h1.2])
    have hκ'1 : min κ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have h4 : (2 * min κ (1 / 2)) ^ 2 ≤ 4 - (E n) ^ 2 := by nlinarith
    have h5 : 2 * min κ (1 / 2) ≤ Real.sqrt (4 - (E n) ^ 2) := by
      calc 2 * min κ (1 / 2) = Real.sqrt ((2 * min κ (1 / 2)) ^ 2) := (Real.sqrt_sq (by linarith)).symm
        _ ≤ _ := Real.sqrt_le_sqrt h4
    linarith
  have hm : ‖mE (E n)‖ = 1 := norm_mE hEn.le
  have hξ := norm_mul_mSigma_lt_one hEn.le ht0 ht1 (σ 0) (σ 1)
  have hΘ : ∀ x y, STThg (bandFM sz E) n (σ 0) (σ 1) t x y =
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) x y :=
    fun x y => congr_fun (congr_fun (bandFM_STThg sz E n (σ 0) (σ 1) t) x) y
  have hsh : ∀ x y : Zd d (sz.L n), Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) x y =
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 (y - x) := fun x y => by
    have := Theta_apply_add_right_of_three_le (d := d) (g := sz.lam n) hL hξ 0 (y - x) x
    rwa [zero_add, sub_add_cancel] at this
  have hT := fun x y => congr_fun (congr_fun (Theta_transpose_of_three_le (d := d) (L := sz.L n) (g := sz.lam n) hL hξ) x) y
  simp only [hΘ]
  refine ⟨hsh, fun x y => (hT x y).symm, ?_, ?_, ?_⟩
  · exact fun a => H5 (sz.L n) hL (sz.lam n) hg hWO2 t ht0 ht1 (mE (E n)) hm (σ 0) (σ 1) a
  · exact fun a r h => H6 (sz.L n) hL (sz.lam n) hg hWO2 t ht0 ht1 (mE (E n)) hm hκ' (σ 0) (σ 1) a r h
  · exact fun a r h => H7 (sz.L n) hL (sz.lam n) hg hWO2 t ht0 ht1 (mE (E n)) hm hκ' (σ 0) (σ 1) a r h

private theorem cltMom2G_chk_E (n : ℕ) : |STflowE zCL n| ≤ 2 - 1 / 2 := by
  have hz : 0 < (zCL n).im := by
    have := szCL_two_le_L n
    change 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ / 2
    positivity
  exact (abs_lemE_le hz).trans (by simp [zCL]; norm_num)

/-- `STThPropsg` at the band data (the closing of the examples below; target 7a of the second row proves it in general). -/
private theorem cltMom2G_chk_Th0 : STThPropsg (bandFM szCL (STflowE zCL)) :=
  cltMom2G_chk_Th szCL (1 / 2) (1 / 10) (STflowE zCL) (by norm_num) (by norm_num) (by norm_num) szCL_WO cltMom2G_chk_E

/-- Target 1a: the weight at `a₁`, at the band data. -/
example := cltMom1_weight_a1g (bandFM szCL (STflowE zCL)) (by norm_num) cltMom2G_chk_Th0

/-- Target 1b: the weight at `a₂`, at the band data. -/
example := cltMom1_weight_a2g (bandFM szCL (STflowE zCL)) (by norm_num) cltMom2G_chk_Th0

/-- The vocabulary at the band is the band vocabulary (`Zg` at `bandFM` is `CltMom2.Z`). -/
example (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a β : Fin 2 → Zd 3 (szCL.L n)) :
    CltMom2.Zg (bandFM szCL (STflowE zCL)) n s t σ a β = CltMom2.Z szCL n (STflowE zCL n) s t σ a β := by
  have h : ∀ x y, STThg (bandFM szCL (STflowE zCL)) n (σ 0) (σ 1) t x y =
      Theta 3 (szCL.L n) (szCL.lam n) ((t : ℂ) * (mSigma (STflowE zCL n) (σ 0) * mSigma (STflowE zCL n) (σ 1))) x y :=
    fun x y => congr_fun (congr_fun (bandFM_STThg szCL _ n (σ 0) (σ 1) t) x) y
  unfold CltMom2.Zg CltMom2.Z
  simp only [h]
  rfl

/-- Target 3a: the decomposition, at `n = 0`, `s = 0`, `t = tCL 0`. -/
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (szCL.L 0)) (ω : szCL.SeqΩ) :
    STfFarg (bandFM szCL (STflowE zCL)) 0 (sCL 0) (tCL 0) σ a ω -
        ∫ ω', STfFarg (bandFM szCL (STflowE zCL)) 0 (sCL 0) (tCL 0) σ a ω' ∂(Sizes.seqP szCL) =
      (((1 - sCL 0) ^ 2 / (szCL.lam 0 ^ 4 * (szCL.lam 0 ^ 2 * ((szCL.W 0 : ℕ) : ℝ) ^ 3) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.flucg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) 0 (sCL 0) (tCL 0) σ a ω +
        CltMom2.offg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) 0 (sCL 0) (tCL 0) σ a ω := by
  obtain ⟨-, hκ, -, -, -, hm, -, -, -, -, hrep, -⟩ := cltMom2G_chk_H hLoc hDec
  exact cltMom2_decompg _ _ 0 _ _ (cltMom2G_lenv_of_rep _ _ hrep hκ 0 (hm 0) (by norm_num [sCL])) (by norm_num [szCL]) σ a ω

/-- Target 3b: the envelope of `𝗕`, at `n = 0`. -/
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1)
    (σ : Fin 2 → Bool) (β : Fin 2 → Zd 3 (szCL.L 0)) (ω : szCL.SeqΩ) :
    ‖STcltBg (bandFM szCL (STflowE zCL)) 0 (sCL 0) σ β ω‖ ≤ CltMom2.BYg (bandFM szCL (STflowE zCL)) 0 (sCL 0) σ := by
  obtain ⟨-, hκ, -, -, -, hm, -, -, -, -, hrep, -⟩ := cltMom2G_chk_H hLoc hDec
  exact cltMom2_norm_stcltBg_le _ 0 (cltMom2G_lenv_of_rep _ _ hrep hκ 0 (hm 0) (by norm_num [sCL])) σ β ω

/-- Target 3c: the weights, at the band data. -/
example := cltMom2_weightg_le (bandFM szCL (STflowE zCL)) (by norm_num) cltMom2G_chk_Th0

/-- Target 3d: the moment bound at one `n ≥ 34` (`40 ≤ log W`), `p = 1`, `a = (0, 0)`, with `q₁ = 1` (the tail hypothesis `DomHypg` is
then `μ(·) ≤ 1`) and `εf = W^{-1}` from `stCltIsogL_holds`; `M₀` is the constant of the weights. -/
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1)
    (Λ' : ℝ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ n : ℕ, 34 ≤ n ∧ ∃ σ : Fin 2 → Bool, σ 0 ≠ σ 1 ∧
      ∫ ω, ‖CltMom2.flucg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) n (sCL n) (tCL n) σ (fun _ => 0) ω‖ ^ (2 * 1)
          ∂(Sizes.seqP szCL) ≤
        CltMom2.rhsg (bandFM szCL (STflowE zCL)) n (sCL n) (tCL n) σ (fun _ => 0) 1 ((4 : ℝ) ^ 3 * M₀) Λ' 1
          (((szCL.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have hH := cltMom2G_chk_H hLoc hDec
  have hiso := stCltIsogL_holds 3 _ _ _ _ _ szCL _ _ _ _ _ sCL tCL hH
  obtain ⟨-, hκ, -, -, -, hm, hs0, hst, ht1, -, hrep, -⟩ := hH
  obtain ⟨M₀, hM₀, HW⟩ := cltMom2_weightg_le (bandFM szCL (STflowE zCL)) (by norm_num) cltMom2G_chk_Th0
  obtain ⟨n, hn, hWn, hn34⟩ := ((hiso 1 le_rfl 1 one_pos).and (HW.and (Filter.eventually_ge_atTop 34))).exists
  have hlog : 40 ≤ Real.log ((szCL.W n : ℕ) : ℝ) := by
    rw [szCL_log_W]
    have h2 := Real.log_two_gt_d9
    have : (34 : ℝ) ≤ n := by exact_mod_cast hn34
    nlinarith
  have hσ : (![true, false] : Fin 2 → Bool) 0 ≠ (![true, false] : Fin 2 → Bool) 1 := by simp
  refine ⟨M₀, hM₀, n, hn34, ![true, false], hσ, ?_⟩
  refine (cltMom2_moment_fixedg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) (by norm_num) hM₀ n (tCL n)
    (cltMom2G_lenv_of_rep _ _ hrep hκ n (hm n) (by norm_num [sCL])) ![true, false] (fun _ => 0) 1 Λ' 1 _ hlog zero_le_one
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (hWn (sCL n) (tCL n) ![true, false] (fun _ => 0) hσ (by norm_num [szCL]) ((hs0 n).trans (hst n).le) (ht1 n)
      (szCL_reg5I n).1 (by push_cast; linarith))
    (fun β _ => (prob_le_one).trans (by simp)) (hn _ hσ)).1

/-- Target 3e: the eventual tail bound, at the band data (`κ = 1/2`). -/
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :=
  cltMom2_tail_eventuallyg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) (κ := 1 / 2) (by norm_num) (by norm_num)
    (cltMom2G_chk_H hLoc hDec).2.2.2.2.2.2.2.2.2.2.1 cltMom2G_chk_Th0
    (stCltIsogL_holds 3 _ _ _ _ _ szCL _ _ _ _ _ sCL tCL (cltMom2G_chk_H hLoc hDec)) tCL

#print axioms cltMom1_weight_a1g
#print axioms cltMom1_weight_a2g
#print axioms cltMom2G_lenv_of_rep
#print axioms cltMom2_decompg
#print axioms cltMom2_norm_stcltBg_le
#print axioms cltMom2_weightg_le
#print axioms cltMom2_moment_fixedg
#print axioms cltMom2_tail_eventuallyg

end Instances

end RBM.BA
