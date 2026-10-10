/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWMomentExp
import RBM3D.Graph.LWTermExpN
import RBM3D.Graph.AuxGraph2
import RBM3D.Green.GbEXP

/-!
# LW-01 (T2375): `lem:LWterm` and `lem: EWGn2_N` from the moment bounds

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:15-91` (`7_8:line`),
`paper/tex/3_5_Loop_Hierarchy.tex:380-420`.

The pins of `Graph/LWPins.lean` are proved for every `d` from the merged moment bounds
`lwMoment_holds`, `lwMomentExp_holds` by Markov's inequality and the reductions of `7_8:15-60`.

* Section 1: `lwInteg_holds` (`|f_{xy}|^p` is bounded and measurable).
* Section 2: the Markov step `LWTermHolds_prec_of_moments` (moments to `≺`, union bound over the
  index set).
* Section 3: the algebra `LWcut = W^{-2d} Σ G^{σo}_{yx} Σ_α F_α G_{xα} G_{αy}` and the pathwise
  bound of `LWE` from entry bounds (`LWTermHolds_LWE_le`), shared by both reductions.
* Section 4: the `B` side: `(eq:directG1)`, `lwReduceB_holds`, `lwterm_holds`, `lwtermB_holds`.
* Sections 5-6: the `T` side: `(eq:directG2)` with the shift `𝖳(max(r-2,0)) ≲ 𝖳(r)`,
  `(GavLGEX)` at `Ψ_t = max(W^{-d/2}, Bctl^{1/2})`, the reduction for `D ≥ 2d + 1`,
  `lwReduceT_holds`, `lwtermExpS_holds`, `lwtermExpN_holds`, `lwtermExp_holds`.
* Section 7: compiled nonempty instances at `d = 3` (merged data `sz0`, `z0`).

Copied from private merged lemmas (statements kept, names carry the stem `LWTermHolds_`):
`auxGraph2_xiSq_le` and its lattice helpers (`Graph/AuxGraph2.lean`), the row-average step of
`lwMoment_f_le` (`Graph/LWMoment.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Loop RBM.Path RBM.Graph

/-! ## 1. `LWInteg`: `|f_{xy}|^p` is bounded and measurable -/

/-- `LWInteg` closes as stated: `f_{xy}` is a finite sum of products of entries of `G_t`, `‖G_t‖ ≤ η_t⁻¹` for `t < 1`. -/
theorem lwInteg_holds : ∀ d, LWInteg d := by
  intro d sz n E t hE ht0 ht1 p x y
  have hG : ∀ a b, lwExpTerm2_BM (fun ω : sz.SeqΩ => Gt sz n E t true ω a b) := fun a b =>
    ⟨walk_measurable_Gt_apply sz n E t true a b, (etaT E t)⁻¹, fun ω => lwMoment_norm_Gt_le hE ht1 n ω a b⟩
  have hS : ∀ b, lwExpTerm2_BM (fun ω : sz.SeqΩ => STGM sz n E t ω b b) := fun b => by
    have : (fun ω : sz.SeqΩ => STGM sz n E t ω b b) = fun ω => Gt sz n E t true ω b b - mE E := by
      funext ω; simp [STGM]
    rw [this]; exact lwExpTerm2_BM_sub (hG b b) (lwExpTerm2_BM_const _)
  have hBM : lwExpTerm2_BM (fun ω : sz.SeqΩ => LWf sz n E t ω x y) := by
    unfold LWf
    refine lwExpTerm2_BM_sum _ fun α _ => ?_
    by_cases h : α = x ∨ α = y
    · simp only [h, ite_true]; exact lwExpTerm2_BM_const 0
    · simp only [h, ite_false]
      exact lwExpTerm2_BM_sum _ fun β _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_mul
        (lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (hS β)) (hG x α)) (hG α y)
  obtain ⟨hm, C, hC⟩ := hBM
  refine Integrable.of_bound ((hm.norm.pow_const p).aestronglyMeasurable) (C ^ p) (Eventually.of_forall fun ω => ?_)
  rw [norm_pow, norm_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC ω) p


/-! ## 2. The Markov step -/

/-- Markov for the `p`-th moment of a non-negative integrable variable. -/
private theorem LWTermHolds_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Ω → ℝ} (hF0 : ∀ ω, 0 ≤ F ω) {p : ℕ} (hp : p ≠ 0) (hint : Integrable (fun ω => F ω ^ p) P) {a : ℝ}
    (ha : 0 < a) : P {ω | a < F ω} ≤ ENNReal.ofReal ((∫ ω, F ω ^ p ∂P) / a ^ p) := by
  have hap : 0 < a ^ p := pow_pos ha p
  have h1 : a ^ p * P.real {ω | a ^ p ≤ F ω ^ p} ≤ ∫ ω, F ω ^ p ∂P :=
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => pow_nonneg (hF0 ω) p) hint _
  have h2 : P.real {ω | a ^ p ≤ F ω ^ p} ≤ (∫ ω, F ω ^ p ∂P) / a ^ p := by
    rw [le_div_iff₀ hap]; linarith
  calc P {ω | a < F ω} ≤ P {ω | a ^ p ≤ F ω ^ p} :=
        measure_mono fun ω hω => (pow_lt_pow_left₀ hω ha.le hp).le
    _ = ENNReal.ofReal (P.real {ω | a ^ p ≤ F ω ^ p}) := by
        rw [ofReal_measureReal]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h2

/-- **From moments to `≺`** (the Markov step of `7_8:86-91`): if for every `τ₀, D > 0` some even power `p` with
`τ₀ p ≥ D + 2` has `E F^p ≤ N (K ζ)^p` eventually (uniformly over the finite index set `V n`, of size `≤ N^C`), then
`F ≺ ζ`.  The union bound is the `StochDomAt` of the index set. -/
theorem LWTermHolds_prec_of_moments {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {V : ℕ → Type} [∀ n, Fintype (V n)]
    (F : ∀ n, V n → sz.SeqΩ → ℝ) (ζ : ∀ n, V n → ℝ) {C : ℝ}
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (hF0 : ∀ n v ω, 0 ≤ F n v ω) (hint : ∀ (p : ℕ) n v, Integrable (fun ω => F n v ω ^ p) sz.seqP)
    (hζ : ∀ᶠ n in atTop, ∀ v, 0 < ζ n v)
    (hmom : ∀ τ₀ : ℝ, 0 < τ₀ → ∀ D : ℝ, 0 < D → ∃ p : ℕ, 0 < p ∧ D + 2 ≤ τ₀ * p ∧ ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n in atTop, ∀ v, ∫ ω, F n v ω ^ p ∂sz.seqP ≤ ((sz.size n : ℕ) : ℝ) * (K * ζ n v) ^ p) :
    sz.Prec F (fun n v _ => ζ n v) := by
  refine StochDomAt.of_forall_le (sz.tendsto_size hsz) (C := C) hcard ?_
  intro τ hτ D hD
  obtain ⟨p, hp0, hpτ, K, hK, hm⟩ := hmom τ hτ D hD
  have hKp : ∀ᶠ n in atTop, K ^ p ≤ ((sz.size n : ℕ) : ℝ) := by
    exact hsz.eventually_ge_atTop (K ^ p)
  filter_upwards [hζ, hm, hKp, (sz.tendsto_size hsz).eventually (eventually_ge_atTop 1)] with n hζn hmn hKn hN1 v
  have hX1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set X : ℝ := ((sz.size n : ℕ) : ℝ) with hX
  have hX1 : (1 : ℝ) ≤ X := hX1'
  have hX0 : 0 < X := by linarith
  have hz := hζn v
  have ha : 0 < X ^ τ * ζ n v := mul_pos (Real.rpow_pos_of_pos hX0 _) hz
  have hM := LWTermHolds_markov sz.seqP (hF0 n v) hp0.ne' (hint p n v) ha
  refine hM.trans (ENNReal.ofReal_le_ofReal ?_)
  have hap : 0 < (X ^ τ * ζ n v) ^ p := pow_pos ha p
  rw [div_le_iff₀ hap]
  have e1 : (X ^ τ * ζ n v) ^ p = X ^ (τ * p) * ζ n v ^ p := by
    rw [mul_pow, ← Real.rpow_natCast (X ^ τ), ← Real.rpow_mul hX0.le]
  have h3 : X ^ (-D) * X ^ (τ * p) = X ^ (τ * p - D) := by
    rw [← Real.rpow_add hX0]; ring_nf
  have h4 : X ^ (D + 2) ≤ X ^ (τ * p) := Real.rpow_le_rpow_of_exponent_le hX1 hpτ
  have h5 : X ^ (1 : ℝ) * X ^ (D + 1) ≤ X ^ (τ * p) := by
    rw [← Real.rpow_add hX0]; refine le_trans (le_of_eq (by ring_nf)) h4
  have hz1 : 0 < ζ n v ^ p := pow_pos hz p
  calc ∫ ω, F n v ω ^ p ∂sz.seqP ≤ X * (K * ζ n v) ^ p := hmn v
    _ = X * K ^ p * ζ n v ^ p := by rw [mul_pow]; ring
    _ ≤ X * X * ζ n v ^ p := by
        gcongr
    _ ≤ X ^ (-D) * (X ^ (τ * p) * ζ n v ^ p) := by
        have h6 : X * X ≤ X ^ (-D) * X ^ (τ * p) := by
          rw [h3]
          have : X * X = X ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
          rw [this]
          exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right h6 hz1.le]
    _ = X ^ (-D) * (X ^ τ * ζ n v) ^ p := by rw [e1]
/-! ## 3. The algebra of `LWcut` through `f_{xy}` -/

section Alg

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- **`(eq:EGC)`, second line, at `σc = +`** (`7_8:9-14`): `𝓔 = W^{-2d} Σ_{x∈[a], y∈[b]} G^{σo}_{yx} Σ_α F_α G_{xα} G_{αy}`,
`F_α = Σ_β S_{αβ} Ǧ_{ββ}`, written with the block weights `w_a(x) = W^{-d} 1[x ∈ [a]]`. -/
theorem LWTermHolds_cut_true (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    LWcut sz n E t true σ ac ao ω = ∑ c, ∑ o, lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o *
      ((∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω o v * Gt sz n E t true ω v c) *
        Gt sz n E t σ ω c o) := by
  rw [lwExpTerm2_LWcut_true]
  set G := Gt sz n E t true ω with hGdef
  set Gs := Gt sz n E t σ ω with hGsdef
  set c₀ : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with hc₀
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) * c₀ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne'))
  have hS : ∀ x y, (Matrix.of fun x y => (LWS sz n x y : ℂ)) x y =
      c₀ * ((1 : ℂ) * SB d (sz.L n) (sz.lam n) (lwExpTerm2_bl d (sz.L n) (sz.W n) x)
        (lwExpTerm2_bl d (sz.L n) (sz.W n) y)) := fun x y => by
    have := lwExpTerm2_hS sz n 1 x y
    simp only [lwS, Matrix.of_apply, one_mul, Complex.ofReal_one] at this ⊢
    exact this
  have hX : ∀ v, ∑ β, (Matrix.of fun x y => (LWS sz n x y : ℂ)) v β * (G β β - mE E) =
      ∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β := fun v =>
    Finset.sum_congr rfl fun β _ => by simp [STGM, hGdef]
  have key : ∀ a₂ : Zd d (sz.L n), (∑ b, (SB d (sz.L n) (sz.lam n) a₂ b : ℂ) *
        lwExpTerm2_Xv G (mE E) (lwExpTerm2_w sz n b)) *
      lwExpTerm2_L3 G G Gs (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao) =
      ∑ c, ∑ o, ∑ v, lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o * lwExpTerm2_w sz n a₂ v *
        ((∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * (G v c * G o v * Gs c o)) := fun a₂ => by
    have h := lwExpTerm2_eval3 (lwExpTerm2_bl d (sz.L n) (sz.W n)) c₀ 1
      (fun a b => (SB d (sz.L n) (sz.lam n) a b : ℂ)) G Gs (mE E) (Matrix.of fun x y => (LWS sz n x y : ℂ)) hS
      a₂ ac ao 1
    simp only [hX, one_mul, mul_one] at h
    exact h.symm
  -- sum over `a₁` first: symmetry of `S^{(B)}`
  have hsym : ∀ a₁ a₂ : Zd d (sz.L n), (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) = SB d (sz.L n) (sz.lam n) a₂ a₁ := fun a₁ a₂ => by
    have := congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) a₁) a₂
    simpa [Matrix.transpose_apply] using this.symm
  have e1 : ∑ a₁, ∑ a₂, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (lwExpTerm2_Xv G (mE E) (lwExpTerm2_w sz n a₁) *
      lwExpTerm2_L3 G G Gs (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao)) =
      ∑ a₂, (∑ b, (SB d (sz.L n) (sz.lam n) a₂ b : ℂ) * lwExpTerm2_Xv G (mE E) (lwExpTerm2_w sz n b)) *
        lwExpTerm2_L3 G G Gs (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a₁ _ => by rw [hsym a₁ a₂]; ring
  rw [e1]
  simp only [key]
  -- the sum over the block label `a₂` of the weights
  have e2 : ∀ (c o v : Idx d (sz.L n) (sz.W n)) (Z : ℂ), ∑ a₂ : Zd d (sz.L n),
      lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o * lwExpTerm2_w sz n a₂ v * Z =
      c₀ * (lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o * Z) := fun c o v Z => by
    have := lwExpTerm2_dw_blocks (lwExpTerm2_bl d (sz.L n) (sz.W n)) c₀ v (fun _ => (1 : ℂ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ] at this
    calc _ = (∑ a₂ : Zd d (sz.L n), lwExpTerm2_w sz n a₂ v) * (lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o * Z) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a₂ _ => by ring
      _ = _ := by rw [show (∑ a₂ : Zd d (sz.L n), lwExpTerm2_w sz n a₂ v) = c₀ from this]
  rw [lwExpTerm2_sum4_rot]
  simp only [e2]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have e4 : ∑ v, c₀ * (lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o *
        ((∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * (G v c * G o v * Gs c o))) =
      c₀ * (lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o) *
        ((∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * G o v * G v c) * Gs c o) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e4]
  linear_combination (lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o *
    ((∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * G o v * G v c) * Gs c o)) * hW

/-- `F_α = Σ_β S_{αβ} Ǧ_{ββ}`: bounded by the block averages (`(eq:boundfxyGinf)`, `7_8:62-66`). -/
theorem LWTermHolds_F_le {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (ω : sz.SeqΩ) {μ : ℝ}
    (hμ : ∀ b : Zd d (sz.L n), ‖Lloop sz n E t (fun _ : Fin 1 => true) (fun _ => b) ω - mE E‖ ≤ μ)
    (α : Idx d (sz.L n) (sz.W n)) : ‖∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β‖ ≤ μ := by
  have hG : ∀ a b, Gt sz n E t true ω a b = green (sz.seqHflow n t ω) (zt E t) a b := fun a b => by
    rw [lwMoment_Gt_true_eq]
  have := lwMoment_row_le (sz.three_le_L n) (sz.lam n) (Gt sz n E t true ω) (mE E) α (μ := μ) (fun b => by
    have h := lwMoment_avgErr_sum (sz.seqHflow n t ω) (zt E t) (mE E) b
    have e : ∀ β, Gres (sz.seqHflow n t ω) (zt E t) true β β = Gt sz n E t true ω β β := fun β => by
      rw [hG]; simp [green, Gres, Matrix.nonsing_inv_eq_ringInverse]
    simp only [e] at h
    rw [← h]
    exact hμ b)
  convert this using 2
  refine Finset.sum_congr rfl fun β _ => ?_
  simp [STGM, LWS]

/-- The split `Σ_α F_α G_{xα} G_{αy} = f_{xy} + f̃_{xy}`, `f̃` the contribution of `α ∈ {x, y}` (`7_8:30-36`). -/
theorem LWTermHolds_F_split (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω x v * Gt sz n E t true ω v y =
      LWf sz n E t ω x y + ∑ α ∈ ({x, y} : Finset (Idx d (sz.L n) (sz.W n))),
        (∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω x α * Gt sz n E t true ω α y := by
  classical
  have hT : ∀ α, (∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω x α * Gt sz n E t true ω α y =
      ∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β * Gt sz n E t true ω x α * Gt sz n E t true ω α y :=
    fun α => by rw [Finset.sum_mul, Finset.sum_mul]
  have hs : ({x, y} : Finset (Idx d (sz.L n) (sz.W n))) = Finset.univ.filter (fun α => α = x ∨ α = y) := by
    ext α; simp
  unfold LWf
  rw [hs, Finset.sum_filter]
  simp only [hT]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs <;> simp

/-- `‖G^{σ}_{ij}‖ = ‖G_{ji}‖` or `‖G_{ij}‖`: the norm of an entry of `G(-)` is that of the transposed entry of `G(+)`. -/
theorem LWTermHolds_norm_Gt (E t : ℝ) (σ : Bool) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) :
    ‖Gt sz n E t σ ω i j‖ = if σ then ‖Gt sz n E t true ω i j‖ else ‖Gt sz n E t true ω j i‖ := by
  cases σ
  · rw [lwExpTerm2_Gt_false]; simp
  · simp

/-- **The pointwise bound of one term of `(eq:EGC)`** (`7_8:15-60`): with `‖G_{xx}‖ ≤ A`, `‖G_{xy}‖ ≤ γ` (`x ≠ y`),
`‖f_{xy}‖ ≤ φ`, `‖F_α‖ ≤ μ`:  `‖G^σ_{yx} (f_{xy} + f̃_{xy})‖ ≤ γ (φ + 2 μ A γ)` for `x ≠ y`, `≤ A (φ + μ A²)` for `x = y`. -/
theorem LWTermHolds_pointwise (E t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (o c : Idx d (sz.L n) (sz.W n)) {A γ φ μ : ℝ}
    (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hγ0 : 0 ≤ γ) (hA : ∀ x, ‖Gt sz n E t true ω x x‖ ≤ A)
    (hγ : o ≠ c → ‖Gt sz n E t true ω o c‖ ≤ γ ∧ ‖Gt sz n E t true ω c o‖ ≤ γ)
    (hφ : ‖LWf sz n E t ω o c‖ ≤ φ)
    (hF : ∀ α, ‖∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β‖ ≤ μ) :
    ‖(∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω o v * Gt sz n E t true ω v c) *
        Gt sz n E t σ ω c o‖ ≤
      γ * (φ + 2 * μ * A * γ) + (if o = c then A * (φ + μ * A ^ 2) else 0) := by
  classical
  rw [LWTermHolds_F_split, norm_mul]
  set G := Gt sz n E t true ω
  have hTn : ∀ α, ‖(∑ β, (LWS sz n α β : ℂ) * STGM sz n E t ω β β) * G o α * G α c‖ ≤ μ * (‖G o α‖ * ‖G α c‖) := fun α => by
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hF α) (by positivity)
  by_cases hoc : o = c
  · subst hoc
    simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton, ite_true, Finset.pair_eq_singleton]
    have h1 := hA o
    have hs : ‖Gt sz n E t σ ω o o‖ ≤ A := by rw [LWTermHolds_norm_Gt]; split_ifs <;> exact h1
    have h2 : ‖(∑ β, (LWS sz n o β : ℂ) * STGM sz n E t ω β β) * G o o * G o o‖ ≤ μ * (A * A) :=
      (hTn o).trans (mul_le_mul_of_nonneg_left (mul_le_mul h1 h1 (norm_nonneg _) hA0) hμ0)
    calc ‖LWf sz n E t ω o o + (∑ β, (LWS sz n o β : ℂ) * STGM sz n E t ω β β) * G o o * G o o‖ * ‖Gt sz n E t σ ω o o‖
        ≤ (φ + μ * (A * A)) * A := by
          refine mul_le_mul ((norm_add_le _ _).trans (add_le_add hφ h2)) hs (norm_nonneg _) (by
            have := (norm_nonneg (LWf sz n E t ω o o)).trans hφ; positivity)
      _ ≤ _ := by
          have hφ0 : 0 ≤ φ := (norm_nonneg _).trans hφ
          have : 0 ≤ γ * (φ + 2 * μ * A * γ) := by positivity
          nlinarith [this]
  · obtain ⟨hg1, hg2⟩ := hγ hoc
    have hs : ‖Gt sz n E t σ ω c o‖ ≤ γ := by rw [LWTermHolds_norm_Gt]; split_ifs <;> assumption
    rw [Finset.sum_pair hoc]
    have h2 : ‖(∑ β, (LWS sz n o β : ℂ) * STGM sz n E t ω β β) * G o o * G o c‖ ≤ μ * (A * γ) :=
      (hTn o).trans (mul_le_mul_of_nonneg_left (mul_le_mul (hA o) hg1 (norm_nonneg _) hA0) hμ0)
    have h3 : ‖(∑ β, (LWS sz n c β : ℂ) * STGM sz n E t ω β β) * G o c * G c c‖ ≤ μ * (γ * A) :=
      (hTn c).trans (mul_le_mul_of_nonneg_left (mul_le_mul hg1 (hA c) (norm_nonneg _) hγ0) hμ0)
    simp only [hoc, ite_false, add_zero]
    calc ‖LWf sz n E t ω o c + ((∑ β, (LWS sz n o β : ℂ) * STGM sz n E t ω β β) * G o o * G o c +
          (∑ β, (LWS sz n c β : ℂ) * STGM sz n E t ω β β) * G o c * G c c)‖ * ‖Gt sz n E t σ ω c o‖
        ≤ (φ + (μ * (A * γ) + μ * (γ * A))) * γ := by
          refine mul_le_mul ((norm_add_le _ _).trans (add_le_add hφ ((norm_add_le _ _).trans (add_le_add h2 h3))))
            hs (norm_nonneg _) (by
              have := (norm_nonneg (LWf sz n E t ω o c)).trans hφ; positivity)
      _ = _ := by ring

/-- The real block weight `W^{-d} 1[x ∈ [a]]` (`‖w_a(x)‖`). -/
private def LWTermHolds_r (n : ℕ) (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) : ℝ :=
  if STblk sz n x = a then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0

private theorem LWTermHolds_r_nonneg (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) : 0 ≤ LWTermHolds_r sz n a x := by
  unfold LWTermHolds_r; split_ifs <;> positivity

private theorem LWTermHolds_norm_w (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    ‖lwExpTerm2_w sz n a x‖ = LWTermHolds_r sz n a x := by
  unfold lwExpTerm2_w lwExpTerm2_dw LWTermHolds_r STblk lwExpTerm2_bl
  split_ifs <;> simp [norm_inv, Complex.norm_natCast]

private theorem LWTermHolds_r_sum (a : Zd d (sz.L n)) : ∑ x, LWTermHolds_r sz n a x = 1 := by
  have h := card_Iblk d (sz.L n) (sz.W n) a
  have h' : (Finset.univ.filter fun x : Idx d (sz.L n) (sz.W n) => STblk sz n x = a).card = (sz.W n) ^ d := h
  have hW : (((sz.W n : ℕ) : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  simp only [LWTermHolds_r, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, h']
  push_cast
  exact mul_inv_cancel₀ hW

private theorem LWTermHolds_r_mul (a b : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    LWTermHolds_r sz n a x * LWTermHolds_r sz n b x =
      if a = b then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * LWTermHolds_r sz n a x else 0 := by
  unfold LWTermHolds_r
  by_cases h : STblk sz n x = a <;> by_cases h' : STblk sz n x = b <;> by_cases hab : a = b <;> simp_all

private theorem LWTermHolds_avg {ι B : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq B] (r : B → ι → ℝ) (c₀ : ℝ)
    (ac ao : B) (hs : ∀ a, ∑ x, r a x = 1) (hm : ∀ a b x, r a x * r b x = if a = b then c₀ * r a x else 0)
    (K₁ K₂ : ℝ) :
    ∑ c, ∑ o, r ac c * r ao o * (K₁ + K₂ * (if o = c then 1 else 0)) =
      K₁ + K₂ * (c₀ * (if ac = ao then 1 else 0)) := by
  have e1 : ∀ c, ∑ o, r ac c * r ao o * (K₁ + K₂ * (if o = c then 1 else 0)) =
      r ac c * K₁ + K₂ * (r ac c * r ao c) := fun c => by
    have h1 : ∀ o, r ac c * r ao o * (K₁ + K₂ * (if o = c then 1 else 0)) =
        (r ac c * K₁) * r ao o + (K₂ * r ac c) * (if o = c then r ao o else 0) := fun o => by
      split_ifs <;> ring
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hs, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp only [e1, Finset.sum_add_distrib, hm, ← Finset.sum_mul, ← Finset.mul_sum, hs, one_mul]
  by_cases hab : ac = ao
  · subst hab; simp [← Finset.mul_sum, hs]
  · simp [hab]

/-- **The averaging step** (`(eq:recoltermwt)`, `7_8:46-52`): if `‖G^σ_{co} Σ_v F_v G_{ov} G_{vc}‖ ≤ K₁ + K₂ δ_{oc}` for all `o ∈ [a_o]`,
`c ∈ [a_c]`, then `‖LWcut(+, σ, a_c, a_o)‖ ≤ K₁ + K₂ W^{-d} 1[a_c = a_o]`. -/
theorem LWTermHolds_cut_le (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) {K₁ K₂ : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hH : ∀ o c : Idx d (sz.L n) (sz.W n), STblk sz n o = ao → STblk sz n c = ac →
      ‖(∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω o v * Gt sz n E t true ω v c) *
        Gt sz n E t σ ω c o‖ ≤ K₁ + K₂ * (if o = c then 1 else 0)) :
    ‖LWcut sz n E t true σ ac ao ω‖ ≤ K₁ + K₂ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if ac = ao then 1 else 0)) := by
  classical
  rw [LWTermHolds_cut_true]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c o, ‖lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o *
      ((∑ v, (∑ β, (LWS sz n v β : ℂ) * STGM sz n E t ω β β) * Gt sz n E t true ω o v * Gt sz n E t true ω v c) *
        Gt sz n E t σ ω c o)‖ ≤ LWTermHolds_r sz n ac c * LWTermHolds_r sz n ao o *
          (K₁ + K₂ * (if o = c then 1 else 0)) := fun c o => by
    rw [norm_mul, norm_mul, LWTermHolds_norm_w, LWTermHolds_norm_w]
    by_cases h : STblk sz n c = ac ∧ STblk sz n o = ao
    · exact mul_le_mul_of_nonneg_left (hH o c h.2 h.1) (mul_nonneg (LWTermHolds_r_nonneg sz n _ _) (LWTermHolds_r_nonneg sz n _ _))
    · have : LWTermHolds_r sz n ac c * LWTermHolds_r sz n ao o = 0 := by
        unfold LWTermHolds_r
        rcases not_and_or.1 h with h1 | h1 <;> simp [h1]
      rw [this]; simp
  refine (Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun o _ => hterm c o)).trans ?_
  exact le_of_eq (LWTermHolds_avg (LWTermHolds_r sz n) _ ac ao (LWTermHolds_r_sum sz n) (LWTermHolds_r_mul sz n) K₁ K₂)

private theorem LWTermHolds_zdistInf_neg (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem LWTermHolds_zdistInf_zero (L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem LWTermHolds_zdistInf_sub_comm (L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← neg_sub, LWTermHolds_zdistInf_neg]

/-- **The pathwise bound of `LWcut`** (`(eq:recoltermwt)`, `7_8:15-60`, both charges `σ_c`): from the entry bounds
`‖G_{xx}‖ ≤ A`, `‖G_{xy}‖ ≤ γ(|[x]-[y]|)` (`x ≠ y`), `‖f_{xy}‖ ≤ φ(|[x]-[y]|)` and the averages `‖𝓛^{(1)}_b - m‖ ≤ μ`:
`‖LWcut(σ_c, σ_o, a_c, a_o)‖ ≤ γ(r)(φ(r) + 2μAγ(r)) + W^{-d} 1[a_c = a_o] A (φ(0) + μA²)`, `r = |a_o - a_c|`. -/
theorem LWTermHolds_cutAll_le (E t : ℝ) (hE : |E| < 2) (ht : t < 1) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ)
    {A μ : ℝ} {γ φ : ℕ → ℝ} (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hγ0 : ∀ r, 0 ≤ γ r) (hφ0 : ∀ r, 0 ≤ φ r)
    (hA : ∀ x, ‖Gt sz n E t true ω x x‖ ≤ A)
    (hγ : ∀ o c, o ≠ c → ‖Gt sz n E t true ω o c‖ ≤ γ (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)))
    (hφ : ∀ o c, ‖LWf sz n E t ω o c‖ ≤ φ (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)))
    (hμ : ∀ b : Zd d (sz.L n), ‖Lloop sz n E t (fun _ : Fin 1 => true) (fun _ => b) ω - mE E‖ ≤ μ) :
    ‖LWcut sz n E t σc σo ac ao ω‖ ≤ γ (zdistInf d (sz.L n) (ao - ac)) *
        (φ (zdistInf d (sz.L n) (ao - ac)) + 2 * μ * A * γ (zdistInf d (sz.L n) (ao - ac))) +
      A * (φ 0 + μ * A ^ 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if ac = ao then 1 else 0)) := by
  classical
  have hF := LWTermHolds_F_le sz n hE ht ω hμ
  -- the case `σ_c = +`, for every pair of blocks
  have key : ∀ (σ : Bool) (ac ao : Zd d (sz.L n)), ‖LWcut sz n E t true σ ac ao ω‖ ≤
      γ (zdistInf d (sz.L n) (ao - ac)) * (φ (zdistInf d (sz.L n) (ao - ac)) +
        2 * μ * A * γ (zdistInf d (sz.L n) (ao - ac))) +
      A * (φ 0 + μ * A ^ 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if ac = ao then 1 else 0)) := fun σ ac ao => by
    refine LWTermHolds_cut_le sz n E t σ ac ao ω (by have := hγ0 (zdistInf d (sz.L n) (ao - ac)); have := hφ0 (zdistInf d (sz.L n) (ao - ac)); positivity)
      (by have := hφ0 0; positivity) ?_
    intro o c ho hc
    have hr : STblk sz n o - STblk sz n c = ao - ac := by rw [ho, hc]
    have h := LWTermHolds_pointwise sz n E t ω σ o c (A := A) (γ := γ (zdistInf d (sz.L n) (ao - ac)))
      (φ := φ (zdistInf d (sz.L n) (ao - ac))) hμ0 hA0 (hγ0 _) hA
      (fun hoc => ⟨by simpa [hr] using hγ o c hoc, by
        have := hγ c o hoc.symm
        rwa [LWTermHolds_zdistInf_sub_comm, hr] at this⟩)
      (by simpa [hr] using hφ o c) hF
    by_cases hoc : o = c
    · subst hoc
      have hac : ao = ac := by rw [← ho, ← hc]
      subst hac
      simp only [sub_self, LWTermHolds_zdistInf_zero, ite_true, mul_one] at h ⊢
      exact h
    · simpa [hoc] using h
  cases σc
  · -- conjugation: `conj LWcut(-, σ_o, a_c, a_o) = LWcut(+, -σ_o, a_o, a_c)`
    have h := key (!σo) ao ac
    rw [← lwExpTerm2_cut_conj sz n E t σo ac ao ω, Complex.norm_conj] at h
    rw [LWTermHolds_zdistInf_sub_comm (sz.L n) ac ao] at h
    have e : (if ao = ac then (1 : ℝ) else 0) = if ac = ao then 1 else 0 := by simp [eq_comm]
    rw [e] at h
    exact h
  · exact key σo ac ao

/-- **`LWE` is the sum of two `LWcut`s** (`7_8:9-10`): the pathwise bound of both terms, `r = |a₀ - a₁|`. -/
theorem LWTermHolds_LWE_le (E t : ℝ) (hE : |E| < 2) (ht : t < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ)
    {A μ : ℝ} {γ φ : ℕ → ℝ} (hμ0 : 0 ≤ μ) (hA0 : 0 ≤ A) (hγ0 : ∀ r, 0 ≤ γ r) (hφ0 : ∀ r, 0 ≤ φ r)
    (hA : ∀ x, ‖Gt sz n E t true ω x x‖ ≤ A)
    (hγ : ∀ o c, o ≠ c → ‖Gt sz n E t true ω o c‖ ≤ γ (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)))
    (hφ : ∀ o c, ‖LWf sz n E t ω o c‖ ≤ φ (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)))
    (hμ : ∀ b : Zd d (sz.L n), ‖Lloop sz n E t (fun _ : Fin 1 => true) (fun _ => b) ω - mE E‖ ≤ μ) :
    ‖LWE sz n E t σ a ω‖ ≤ 2 * (γ (zdistInf d (sz.L n) (a 0 - a 1)) *
        (φ (zdistInf d (sz.L n) (a 0 - a 1)) + 2 * μ * A * γ (zdistInf d (sz.L n) (a 0 - a 1))) +
      A * (φ 0 + μ * A ^ 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if a 1 = a 0 then 1 else 0))) := by
  have h1 := LWTermHolds_cutAll_le sz n E t hE ht (σ 1) (σ 0) (a 1) (a 0) ω hμ0 hA0 hγ0 hφ0 hA hγ hφ hμ
  have h2 := LWTermHolds_cutAll_le sz n E t hE ht (σ 0) (σ 1) (a 0) (a 1) ω hμ0 hA0 hγ0 hφ0 hA hγ hφ hμ
  rw [LWTermHolds_zdistInf_sub_comm (sz.L n) (a 1) (a 0)] at h2
  have e : (if a 0 = a 1 then (1 : ℝ) else 0) = if a 1 = a 0 then 1 else 0 := by simp [eq_comm]
  rw [e] at h2
  unfold LWE
  linarith [norm_add_le (LWcut sz n E t (σ 1) (σ 0) (a 1) (a 0) ω) (LWcut sz n E t (σ 0) (σ 1) (a 0) (a 1) ω)]

end Alg

/-! ## 4. The `B` side: the premises of the reduction -/

section BSide

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}

/-- **`(eq:directG1)` off the diagonal** (`7_8:20-23`, from `(GijGEX)`, `(LW_assm)` and `(eq:Psi)`): `|G_{xy}| ≺ Ψ_t(|[x]-[y]|)`, `x ≠ y`
(`lwGbyXi_holds` at `ρ = 1`, `R = 0`, then `claim:xi`). -/
theorem LWTermHolds_Gij_B (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    sz.Prec (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // q.1 ≠ q.2})
      (fun n q ω => ‖Gt sz n (STflowE z n) (t n) true ω q.1.1 q.1.2‖)
      (fun n q _ => Φ n ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ)) := by
  have hsz := lwMoment_size_tendsto S
  have hent := S.assm.2.2.1.1
  have h1 := lwGbyXi_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ S.assm.1 hent
    (fun _ => 1) (fun _ => 0) (fun _ => le_rfl) (fun _ => by norm_num)
  have hρ : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, (fun _ : ℕ => (1 : ℝ)) n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    fun τ hτ => ((tendsto_rpow_atTop hτ).comp hsz).eventually_ge_atTop _
  have h2 := (lwXiClaim_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ C₁ C₂ C₃ Cc Φ
    (lwMoment_psiAll S) S.assm.2.2.2.2.2 ε₀ S.assm.1 hent (fun _ => 1) (fun _ => zero_le_one) hρ).2.1
  have p1 := StochDomAt.precomp_param h1
    (fun n (v : {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // q.1 ≠ q.2}) =>
      (⟨((v.1.1, v.1.2), (STblk sz n v.1.1, STblk sz n v.1.2)), v.2, by simp [STblk], by simp [STblk]⟩ :
        {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) × (Zd d (sz.L n) × Zd d (sz.L n)) //
          q.1.1 ≠ q.1.2 ∧ (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ 0 ∧
          (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ 0}))
  have p2 := StochDomAt.precomp_param h2
    (fun n (v : {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // q.1 ≠ q.2}) =>
      (STblk sz n v.1.1, STblk sz n v.1.2))
  exact StochDomAt.trans (sz.tendsto_size hsz) p1 p2

/-- `‖G_{xx}‖ ≤ 2` w.h.p.: `‖G - M‖_max ≺ W^{-ε₀}`, `N^{𝔠 ε₀} ≤ W^{ε₀}` and `|m| = 1`. -/
theorem LWTermHolds_diag_whp (E t : ℕ → ℝ) {𝔠 ε₀ : ℝ} (h𝔠 : 0 < 𝔠) (hε₀ : 0 < ε₀) (hband : sz.Bandwidth 𝔠)
    (hE : ∀ n, |E n| ≤ 2)
    (hent : sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀))) :
    sz.Whp (fun n => {ω | ∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n (E n) (t n) true ω x x‖ ≤ 2}) := by
  have hτ : 0 < 𝔠 * ε₀ := by positivity
  refine HighProbAt.mono (Sizes.Prec.whp sz hent hτ) ?_
  filter_upwards [hband] with n hb
  intro ω hω x
  have h1 : ‖STGM sz n (E n) (t n) ω x x‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := hω (x, x)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₀) hτ.le
  rw [show 𝔠 * ε₀ / 𝔠 = ε₀ by field_simp] at h2
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ 1 := by
    calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ ε₀ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW.le _)
      _ = 1 := by rw [← Real.rpow_add hW]; simp
  have hG : Gt sz n (E n) (t n) true ω x x = STGM sz n (E n) (t n) ω x x + mE (E n) := by simp [STGM]
  rw [hG]
  calc _ ≤ ‖STGM sz n (E n) (t n) ω x x‖ + ‖mE (E n)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (h1.trans h3) (norm_mE (hE n)).le
    _ = 2 := by norm_num

/-- The arithmetic of the `B` side: `γ(φ + 2μAγ) + A(φ(0) + μA²) W^{-d} δ ≤ K X³ η⁻¹ Φ(0) Φ(r)²`. -/
private theorem LWTermHolds_arithB {X I P0 Pr Wd μ c3 c3' δ : ℝ} (hX : 1 ≤ X) (hI : 1 ≤ I) (hP0 : 0 < P0)
    (hP01 : P0 ≤ 1) (hPr : 0 < Pr) (hWd0 : 0 ≤ Wd) (hWd : Wd ≤ c3 * P0 ^ 2) (hc3 : 0 ≤ c3)
    (hc3' : 0 ≤ c3') (hμ : μ ≤ X * (c3' * P0 ^ 2)) (hδ : δ = 0 ∨ (δ = 1 ∧ Pr = P0)) :
    X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) + 2 * (X * (I * P0 * P0) + μ * 2 ^ 2) * (Wd * δ) ≤
      ((1 + 4 * c3') * (1 + 2 * c3)) * X ^ 3 * (I * P0 * Pr ^ 2) := by
  have hX0 : 0 < X := by linarith
  have hI0 : 0 < I := by linarith
  have hP0sq : P0 ^ 2 ≤ I * P0 := by nlinarith
  have hX2 : X ^ 2 ≤ X ^ 3 := by nlinarith [pow_pos hX0 2]
  have hX1 : X ≤ X ^ 3 := by nlinarith [pow_pos hX0 2]
  have hoff : X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) ≤ (1 + 4 * c3') * X ^ 3 * (I * P0 * Pr ^ 2) := by
    have h1 : 4 * μ * X ^ 2 * Pr ^ 2 ≤ 4 * c3' * X ^ 3 * (I * P0 * Pr ^ 2) := by
      have : μ ≤ X * (c3' * (I * P0)) := hμ.trans (by gcongr)
      nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 4 * X ^ 2 * Pr ^ 2)]
    have e : X * Pr * (X * (I * P0 * Pr) + 2 * μ * 2 * (X * Pr)) = X ^ 2 * (I * P0 * Pr ^ 2) + 4 * μ * X ^ 2 * Pr ^ 2 := by ring
    have e2 : (1 + 4 * c3') * X ^ 3 * (I * P0 * Pr ^ 2) = X ^ 3 * (I * P0 * Pr ^ 2) + 4 * c3' * X ^ 3 * (I * P0 * Pr ^ 2) := by ring
    rw [e, e2]
    nlinarith [mul_le_mul_of_nonneg_right hX2 (by positivity : (0:ℝ) ≤ I * P0 * Pr ^ 2)]
  have hdiag : 2 * (X * (I * P0 * P0) + μ * 2 ^ 2) * (Wd * δ) ≤ (1 + 4 * c3') * (2 * c3) * X ^ 3 * (I * P0 * Pr ^ 2) := by
    rcases hδ with h | ⟨h, hPP⟩
    · subst h
      have : 0 ≤ (1 + 4 * c3') * (2 * c3) * X ^ 3 * (I * P0 * Pr ^ 2) := by positivity
      simpa using this
    · subst h
      rw [← hPP] at hP0 hP01 hWd hμ hP0sq ⊢
      have h4 : X * (I * Pr * Pr) + μ * 2 ^ 2 ≤ (1 + 4 * c3') * X * (I * Pr ^ 2) := by
        have : 4 * μ ≤ 4 * (X * (c3' * Pr ^ 2)) := by linarith
        have h7 : Pr ^ 2 ≤ I * Pr ^ 2 := by nlinarith [sq_nonneg Pr]
        nlinarith [mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ 4 * X * c3')]
      have h5 : 2 * (X * (I * Pr * Pr) + μ * 2 ^ 2) * (Wd * 1) ≤ 2 * ((1 + 4 * c3') * X * (I * Pr ^ 2)) * (c3 * Pr ^ 2) := by
        have := mul_le_mul h4 hWd (by simpa using hWd0) (by positivity)
        nlinarith [this]
      have h6 : Pr ^ 4 ≤ Pr ^ 3 := by nlinarith [pow_pos hP0 3]
      have h8 := mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ 2 * c3 * ((1 + 4 * c3') * X * I))
      have h9 := mul_le_mul_of_nonneg_right hX1 (by positivity : (0:ℝ) ≤ (1 + 4 * c3') * (2 * c3) * (I * Pr * Pr ^ 2))
      nlinarith [h8, h9]
  have hsum : (1 + 4 * c3') * (2 * c3) * X ^ 3 * (I * P0 * Pr ^ 2) + (1 + 4 * c3') * X ^ 3 * (I * P0 * Pr ^ 2) =
      ((1 + 4 * c3') * (1 + 2 * c3)) * X ^ 3 * (I * P0 * Pr ^ 2) := by ring
  linarith

/-- **`lem:LWterm` reduces to the moment bound** (`7_8:15-91`): from `f_{xy} ≺ η_t⁻¹ Ψ_t(0) Ψ_t(|a-b|)`,
`(eq:directG1)` (`LWTermHolds_Gij_B`, `LWTermHolds_diag_whp`) and the averaged local law (`lwMoment_avg_whp`). -/
theorem lwReduceB_holds : ∀ d, LWReduceB d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ C₁ C₂ C₃ Cc Ψ Φ hassm hf
  have S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ := ⟨hd, hκ, hε, h𝔡, hflow, ht0, htT, hassm⟩
  have hsz := lwMoment_size_tendsto S
  obtain ⟨hadm, hE, htlt, -⟩ := lwMoment_flow_facts S
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => (hE n).trans (by linarith [S.hκ])
  have hsize := sz.tendsto_size hsz
  refine lwMoment_prec_of_whp sz fun τ hτ => ?_
  have hτ₁ : 0 < τ / 4 := by positivity
  have E1 := Sizes.Prec.whp sz hf hτ₁
  have E2 := Sizes.Prec.whp sz (LWTermHolds_Gij_B S) hτ₁
  have E3 := LWTermHolds_diag_whp (sz := sz) (STflowE z) t hadm.1 hassm.1 hadm.2.2.2.1 (fun n => (hE2 n).le) hassm.2.2.1.1
  have E4 := lwMoment_avg_whp S hτ₁
  refine ⟨_, HighProbAt.inter hsize (HighProbAt.inter hsize (HighProbAt.inter hsize E1 E2) E3) E4, ?_⟩
  obtain ⟨hcls1, hC3, hcls3⟩ := hassm.2.2.2.1
  have hanti := hassm.2.2.2.2.1.1
  have hK : ∀ᶠ n in atTop, 2 * ((1 + 4 * (max 1 C₃) ^ 2) * (1 + 2 * C₃ ^ 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
    ((tendsto_rpow_atTop hτ₁).comp hsz).eventually_ge_atTop _
  filter_upwards [hcls1, hcls3, lwMoment_Psi'_facts S, hK, hsize.eventually (eventually_ge_atTop 1)] with n hcl1 hcl3 hPsi hKn hN1
  intro ω hω u
  have hX1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hX1' hτ₁.le
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE2 n) (htlt n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one (hE2 n) (ht0 n) (htlt n)
  have hI : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hP0 : 0 < Φ n 0 := (hcl1 0 le_rfl).1
  have hP01 : Φ n 0 ≤ 1 := (hcl1 0 le_rfl).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith [hassm.1]))
  have hΦnn : ∀ r : ℕ, 0 < Φ n (r : ℝ) := fun r => (hcl1 r (Nat.cast_nonneg _)).1
  have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φ n 0 ^ 2 := by
    have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hWpos.le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
        Real.rpow_neg hWpos.le, Real.rpow_natCast]
    rw [← e]
    calc _ ≤ (C₃ * Φ n 0) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hWpos.le _) hcl3 2
      _ = _ := by ring
  have hΨ0 : 0 ≤ lwMoment_Psi' sz Φ n := (Real.rpow_nonneg hWpos.le _).trans hPsi.2.1
  have hΨ2 : lwMoment_Psi' sz Φ n ^ 2 ≤ (max 1 C₃) ^ 2 * Φ n 0 ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hΨ0 hPsi.2.2.2 2
  -- the pathwise bound
  have hγ : ∀ o c : Idx d (sz.L n) (sz.W n), o ≠ c → ‖Gt sz n (STflowE z n) (t n) true ω o c‖ ≤
      (fun r : ℕ => X * Φ n (r : ℝ)) (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)) := fun o c hoc =>
    hω.1.1.2 ⟨(o, c), hoc⟩
  have hφ : ∀ o c : Idx d (sz.L n) (sz.W n), ‖LWf sz n (STflowE z n) (t n) ω o c‖ ≤
      (fun r : ℕ => X * ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ))) (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)) :=
    fun o c => hω.1.1.1 (o, c)
  have hμ : ∀ b : Zd d (sz.L n), ‖Lloop sz n (STflowE z n) (t n) (fun _ : Fin 1 => true) (fun _ => b) ω - mE (STflowE z n)‖ ≤
      X * lwMoment_Psi' sz Φ n ^ 2 := hω.2
  have h := LWTermHolds_LWE_le sz n (STflowE z n) (t n) (hE2 n) (htlt n) u.1 u.2 ω (A := 2) (μ := X * lwMoment_Psi' sz Φ n ^ 2)
    (γ := fun r : ℕ => X * Φ n (r : ℝ)) (φ := fun r : ℕ => X * ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ)))
    (by positivity) (by norm_num) (fun r => by have := hΦnn r; positivity) (fun r => by have := hΦnn r; positivity)
    hω.1.2 hγ hφ hμ
  set r : ℕ := zdistInf d (sz.L n) (u.2 0 - u.2 1) with hr
  have hbd := LWTermHolds_arithB (X := X) (I := (etaT (STflowE z n) (t n))⁻¹) (P0 := Φ n 0) (Pr := Φ n (r : ℝ))
    (Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) (μ := X * lwMoment_Psi' sz Φ n ^ 2) (c3 := C₃ ^ 2) (c3' := (max 1 C₃) ^ 2)
    (δ := if u.2 1 = u.2 0 then 1 else 0) hX1 hI hP0 hP01 (hΦnn r) (by positivity) hWd (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hΨ2 (by linarith)) (by
      by_cases hh : u.2 1 = u.2 0
      · right; refine ⟨by simp [hh], ?_⟩
        rw [hr, ← hh, sub_self, LWTermHolds_zdistInf_zero]; simp
      · left; simp [hh])
  have hN : ((sz.size n : ℕ) : ℝ) ^ τ = X ^ 3 * X := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    congr 1; push_cast; ring
  have hζ : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2 := by
    have := hΦnn r; positivity
  simp only [Nat.cast_zero] at h hbd
  calc ‖LWE sz n (STflowE z n) (t n) u.1 u.2 ω‖ ≤ _ := h
    _ ≤ 2 * (((1 + 4 * (max 1 C₃) ^ 2) * (1 + 2 * C₃ ^ 2)) * X ^ 3 *
          ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2)) := by linarith [hbd]
    _ ≤ X * (X ^ 3 * ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2)) := by
        have := mul_le_mul_of_nonneg_right hKn (by positivity : (0 : ℝ) ≤ X ^ 3 * ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (r : ℝ) ^ 2))
        nlinarith [this]
    _ = _ := by rw [hN]; ring

/-- **The Markov step for `lem:LW_moment`** (`7_8:86-91`): `f_{xy} ≺ η_t⁻¹ Ψ_t(0) Ψ_t(|a-b|)` from the moment bound, `LWInteg` and
`Ψ_t(c r) ≲ Ψ_t(r)` (`(eq:Psi)`). -/
theorem LWTermHolds_fB (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ) :
    sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖)
      (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
        Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) := by
  have hsz := lwMoment_size_tendsto S
  obtain ⟨-, hE, htlt, -⟩ := lwMoment_flow_facts S
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => (hE n).trans (by linarith [S.hκ])
  refine LWTermHolds_prec_of_moments sz hsz (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖)
    (fun n q => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 *
      Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) (C := 2) ?_
    (fun n q ω => norm_nonneg _) (fun p n q => lwInteg_holds d sz n (STflowE z n) (t n) (hE2 n) (S.t0 n) (htlt n) p q.1 q.2) ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    rw [Fintype.card_prod, sz.card_Idx n, Real.rpow_two]
    push_cast; ring_nf; exact le_rfl
  · filter_upwards [S.assm.2.2.2.1.1] with n hcl q
    have h1 := (hcl 0 le_rfl).1
    have h2 := (hcl _ (Nat.cast_nonneg (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2)))).1
    have h3 : 0 < (etaT (STflowE z n) (t n))⁻¹ := inv_pos.2 (etaT_pos (hE2 n) (htlt n))
    positivity
  · intro τ₀ hτ₀ D hD
    set p₀ : ℕ := ⌈(D + 2) / τ₀⌉₊ + 1 with hp₀
    have hp2 : 2 ∣ 2 * p₀ := dvd_mul_right _ _
    obtain ⟨c, hc, H⟩ := lwMoment_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 (2 * p₀) hp2 ε₀ C₁ C₂ C₃ Cc
    have hH := H 𝔠 sz z S.flow t S.t0 S.t1 Ψ Φ S.assm
    obtain ⟨K, hK, hshift⟩ := LWPsiAll.shift sz (lwMoment_psiAll S) hc
    refine ⟨2 * p₀, by omega, ?_, K, hK, ?_⟩
    · have h1 : (D + 2) / τ₀ ≤ (⌈(D + 2) / τ₀⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : D + 2 ≤ τ₀ * (⌈(D + 2) / τ₀⌉₊ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hτ₀.le
        rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
      have hp : ((2 * p₀ : ℕ) : ℝ) = 2 * ((⌈(D + 2) / τ₀⌉₊ : ℝ) + 1) := by rw [hp₀]; push_cast; ring
      rw [hp]
      nlinarith [h2, hτ₀]
    · have h1 := (st6_prec_det_iff sz hsz _ _).1 hH 1 one_pos
      filter_upwards [h1, hshift, S.assm.2.2.2.1.1] with n hn hs hcl q
      refine (hn q).trans ?_
      rw [Real.rpow_one]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hη : 0 < (etaT (STflowE z n) (t n))⁻¹ := inv_pos.2 (etaT_pos (hE2 n) (htlt n))
      have h0 := (hcl 0 le_rfl).1
      have hr : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ) := Nat.cast_nonneg _
      have hcr : 0 < Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) :=
        (hcl _ (by positivity)).1
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))
          ≤ (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * (K * Φ n ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hs _ hr) (by positivity)
        _ = _ := by ring

/-- **`lem:LWterm`** (`3_5:385-404`, `7_8:15-91`): the reduction `lwReduceB_holds` applied to the Markov step `LWTermHolds_fB`. -/
theorem lwterm_holds : ∀ d, LWterm d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ C₁ C₂ C₃ Cc Ψ Φ hassm
  exact lwReduceB_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ C₁ C₂ C₃ Cc Ψ Φ hassm
    (LWTermHolds_fB ⟨hd, hκ, hε, h𝔡, hflow, ht0, htT, hassm⟩)

/-- **`lem:LWterm`, "in particular"** (`(LW_conclusion2)`, `3_5:393-397`): `lwterm_holds` at the B class `Φ = LWPhiB`. -/
theorem lwtermB_holds : ∀ d, LWtermB d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ c₀ C₃ K Ψ hc₀ hK hε₀ hwin hinit hcls hL2
  have h := lwterm_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ ((2 : ℝ) ^ d) (d : ℝ) C₃
    (fun C => Real.sqrt ((C + 1) ^ (d - 2))) Ψ (LWPhiB sz c₀ K t)
    ⟨hε₀, hwin, hinit, hcls, LWPhiB_psiRel sz (by omega) c₀ K t, hL2⟩
  refine lwN_prec_mono (sz.tendsto_size (lwMoment_size_tendsto
    (S := (⟨hd, hκ, hε, h𝔡, hflow, ht0, htT, ⟨hε₀, hwin, hinit, hcls, LWPhiB_psiRel sz (by omega) c₀ K t, hL2⟩⟩ :
      LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ ((2 : ℝ) ^ d) (d : ℝ) C₃ (fun C => Real.sqrt ((C + 1) ^ (d - 2))) Ψ (LWPhiB sz c₀ K t)))))
    (c := 1) ?_ h
  refine Eventually.of_forall fun n => ?_
  rintro ⟨σ, a⟩ ω
  have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0 := by unfold Bparam; positivity
  have e1 : LWPhiB sz c₀ K t n 0 = (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0) ^ (1 / 2 : ℝ) := by
    simp [LWPhiB]
  have e2 : LWPhiB sz c₀ K t n ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ 2 = ((sz.W n : ℕ) : ℝ) ^ (-c₀) *
      Bparam d (sz.L n) (sz.lam n) (t n) (min (zdistInf d (sz.L n) (a 0 - a 1)) (K n)) := by
    unfold LWPhiB
    rw [Nat.floor_natCast, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
    unfold Bparam; positivity
  rw [e1, e2, one_mul]
  exact ⟨by
    have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) (min (zdistInf d (sz.L n) (a 0 - a 1)) (K n)) := by
      unfold Bparam; positivity
    have h3 : 0 < (etaT (STflowE z n) (t n))⁻¹ := inv_pos.2 (etaT_pos (by
      have := (lwMoment_flow_facts (S := (⟨hd, hκ, hε, h𝔡, hflow, ht0, htT, ⟨hε₀, hwin, hinit, hcls, LWPhiB_psiRel sz (by omega) c₀ K t, hL2⟩⟩ :
        LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ ((2 : ℝ) ^ d) (d : ℝ) C₃ (fun C => Real.sqrt ((C + 1) ^ (d - 2))) Ψ (LWPhiB sz c₀ K t)))).2.1 n
      linarith) (by
      have := (lwMoment_flow_facts (S := (⟨hd, hκ, hε, h𝔡, hflow, ht0, htT, ⟨hε₀, hwin, hinit, hcls, LWPhiB_psiRel sz (by omega) c₀ K t, hL2⟩⟩ :
        LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ ((2 : ℝ) ^ d) (d : ℝ) C₃ (fun C => Real.sqrt ((C + 1) ^ (d - 2))) Ψ (LWPhiB sz c₀ K t)))).2.2.1 n
      exact this))
    positivity, le_rfl⟩

end BSide

/-! ## 5. The `T` side: deterministic facts -/

section TFacts

open Real

private theorem LWTermHolds_zdistInf_add_le (L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  exact (zdist_add_le L (x i) (y i)).trans (add_le_add
    (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
    (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i)))

private theorem LWTermHolds_zdistInf_tri_real (d L : ℕ) [NeZero L] (x y w : Zd d L) :
    (zdistInf d L (x - w) : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + (zdistInf d L (y - w) : ℝ) := by
  have : x - w = (x - y) + (y - w) := by abel
  rw [this]; exact_mod_cast LWTermHolds_zdistInf_add_le L _ _

private theorem LWTermHolds_pair_sum (g : (Fin 2 → Bool) → ℝ) :
    ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), g σ =
      g ![true, false] + g ![false, true] := by
  rw [Finset.sum_pair]
  intro h
  have := congrFun h 0
  simp at this

private theorem LWTermHolds_card_ball {d L : ℕ} [NeZero L] (c : Zd d L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (((Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ).card : ℕ) : ℝ) ≤
      (2 * ρ + 1) ^ d := by
  have := RBM.Ind.DecayLoopB_card_ball (L := L) c hρ
  have e : (Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ) =
      Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ ρ := by
    refine Finset.filter_congr fun b _ => ?_
    rw [LWTermHolds_zdistInf_sub_comm]
  rw [e]; exact this

/-- **`ξ([a₁],[a₂])² ≲ Φ(|a₁ - a₂|)²` from `(LW_assm)` and `(eq:Psi)`** (copy of the private `auxGraph2_xiSq_le`, `Graph/AuxGraph2.lean:828`):
if every `‖𝓛^{(2)}_{(s,!s),(b₁,b₂)}‖ ≤ B Φ(|b₁ - b₂|)²`, `Φ(m) ≤ K Φ(ℓ)` for `ℓ ≤ 2ρ + m` and
`W^{-d} ≤ C₃² Φ(0)²`, then `ξ² ≤ (2 (2ρ+1)^{2d} B + C₃²) K² Φ(|a₁ - a₂|)²`. -/
private theorem LWTermHolds_xiSq_le {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (Φn : ℝ → ℝ) (hρ : 0 ≤ ρ n) {B K C₃ : ℝ} (hB : 0 ≤ B)
    (hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖Lloop sz n (E n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
        B * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2)
    (hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r)
    (hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φn m ≤ K * Φn ℓ)
    (hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φn 0 ^ 2) (a₁ a₂ : Zd d (sz.L n)) :
    lwXiSq sz E t ρ n a₁ a₂ ω ≤
      (2 * (2 * ρ n + 1) ^ (2 * d) * B + C₃ ^ 2) * K ^ 2 *
        Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 := by
  classical
  set ℓ : ℝ := ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  set Q : ℝ := K ^ 2 * Φn ℓ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hterm : ∀ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∀ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * B * Q := by
    intro b₁ hb₁ b₂ hb₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
    set m : ℝ := ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have t1 := LWTermHolds_zdistInf_tri_real d (sz.L n) a₁ b₁ a₂
    have t2 := LWTermHolds_zdistInf_tri_real d (sz.L n) b₁ b₂ a₂
    have h1 : (zdistInf d (sz.L n) (a₁ - b₁) : ℝ) ≤ ρ n := by
      rw [LWTermHolds_zdistInf_sub_comm (sz.L n)]; exact hb₁
    have h2 : (zdistInf d (sz.L n) (b₂ - a₂) : ℝ) ≤ ρ n := hb₂
    have hlm : ℓ ≤ 2 * ρ n + m := by
      have := LWTermHolds_zdistInf_tri_real d (sz.L n) a₁ b₁ a₂
      have t3 := LWTermHolds_zdistInf_tri_real d (sz.L n) b₁ b₂ a₂
      rw [hℓ, hm]
      linarith
    have hΦ : Φn m ≤ K * Φn ℓ := hcmp ℓ m hℓ0 hm0 hlm
    have hsq : Φn m ^ 2 ≤ Q := by
      rw [hQ, ← mul_pow]
      exact pow_le_pow_left₀ (hΦnn m hm0) hΦ 2
    rw [LWTermHolds_pair_sum]
    have e1 := hloop true b₁ b₂
    have e2 := hloop false b₁ b₂
    have e3 : B * Φn m ^ 2 ≤ B * Q := mul_le_mul_of_nonneg_left hsq hB
    simp only [Bool.not_true, Bool.not_false] at e1 e2
    linarith
  have hfirst : ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
        ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
    calc _ ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
          ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
            2 * B * Q :=
          Finset.sum_le_sum fun b₁ hb₁ => Finset.sum_le_sum fun b₂ hb₂ => hterm b₁ hb₁ b₂ hb₂
      _ = (((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
          ((((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
            (2 * B * Q)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ρ n + 1) ^ d * ((2 * ρ n + 1) ^ d * (2 * B * Q)) := by
          have c1 := LWTermHolds_card_ball (d := d) a₁ hρ
          have c2 := LWTermHolds_card_ball (d := d) a₂ hρ
          have hBQ : 0 ≤ 2 * B * Q := by positivity
          exact mul_le_mul c1 (mul_le_mul_of_nonneg_right c2 hBQ) (by positivity) (by positivity)
      _ = 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
          rw [show 2 * d = d + d from two_mul d, pow_add]; ring
  have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) ≤ C₃ ^ 2 * Q := by
    split_ifs with hc
    · have : Φn 0 ≤ K * Φn ℓ := hcmp ℓ 0 hℓ0 le_rfl (by rw [hℓ]; linarith)
      have h0 : 0 ≤ Φn 0 := hΦnn 0 le_rfl
      have : Φn 0 ^ 2 ≤ Q := by
        rw [hQ, ← mul_pow]; exact pow_le_pow_left₀ h0 this 2
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 ≤ C₃ ^ 2 * Φn 0 ^ 2 := by rw [mul_one]; exact hW
        _ ≤ C₃ ^ 2 * Q := mul_le_mul_of_nonneg_left this (by positivity)
    · rw [mul_zero]; positivity
  unfold lwXiSq
  calc _ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q + C₃ ^ 2 * Q := add_le_add hfirst hsecond
    _ = _ := by rw [hQ]; ring



private theorem LWTermHolds_sfT_shift {d L : ℕ} {W g t : ℝ} (hℓ : 1 ≤ ellT L g t) {u : ℝ} (hu : 0 ≤ u) :
    sfT d L W g t (max (u - 2) 0) ≤ (Real.sqrt (3 ^ (d - 2)) * Real.exp (Real.sqrt 2 / 2)) * sfT d L W g t u := by
  set u' : ℝ := max (u - 2) 0 with hu'def
  have hu'0 : 0 ≤ u' := le_max_right _ _
  have hu'2 : u ≤ u' + 2 := by
    rcases le_total (u - 2) 0 with h | h
    · rw [hu'def, max_eq_right h]; linarith
    · rw [hu'def, max_eq_left h]; linarith
  have h3 : u + 1 ≤ 3 * (u' + 1) := by
    rcases le_total (u - 2) 0 with h | h
    · rw [hu'def, max_eq_right h]; linarith
    · rw [hu'def, max_eq_left h]; linarith
  set k := d - 2
  have hp : ((u' + 1) ^ k)⁻¹ ≤ 3 ^ k * ((u + 1) ^ k)⁻¹ := by
    have h1 : (u + 1) ^ k ≤ (3 * (u' + 1)) ^ k := pow_le_pow_left₀ (by linarith) h3 k
    have h2 : ((3 * (u' + 1)) ^ k)⁻¹ ≤ ((u + 1) ^ k)⁻¹ := inv_anti₀ (by positivity) h1
    have e : ((u' + 1) ^ k)⁻¹ = 3 ^ k * ((3 * (u' + 1)) ^ k)⁻¹ := by
      rw [mul_pow]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsq : √(((u' + 1) ^ k)⁻¹) ≤ √(3 ^ k) * √(((u + 1) ^ k)⁻¹) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hp
  have hexp : exp (-(1 / 2) * √(u' / ellT L g t)) ≤ exp (√2 / 2) * exp (-(1 / 2) * √(u / ellT L g t)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hℓ0 : 0 < ellT L g t := by linarith
    have h1 : u / ellT L g t ≤ u' / ellT L g t + 2 := by
      have : u / ellT L g t ≤ (u' + 2) / ellT L g t := div_le_div_of_nonneg_right hu'2 hℓ0.le
      rw [add_div] at this
      have h2 : 2 / ellT L g t ≤ 2 := by
        rw [div_le_iff₀ hℓ0]; nlinarith
      linarith
    have h2 : √(u / ellT L g t) ≤ √(u' / ellT L g t) + √2 :=
      (Real.sqrt_le_sqrt h1).trans (sqrt_add_le_add_sqrt (by positivity) (by norm_num))
    linarith
  unfold sfT
  have hA : 0 ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) := by positivity
  calc √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * √(((u' + 1) ^ k)⁻¹) * exp (-(1 / 2) * √(u' / ellT L g t))
      ≤ √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) * (√(3 ^ k) * √(((u + 1) ^ k)⁻¹)) *
        (exp (√2 / 2) * exp (-(1 / 2) * √(u / ellT L g t))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq hA) hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private theorem LWTermHolds_sfT_sq_le {d L : ℕ} {W g t : ℝ} (hW : 0 < W) {r : ℝ} (hr : 0 ≤ r) :
    sfT d L W g t r ^ 2 ≤ (W ^ d)⁻¹ * (g ^ 2 + |1 - t|)⁻¹ := by
  unfold sfT
  have h1 : 0 ≤ (W ^ d)⁻¹ := by positivity
  have h2 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have h3 : 0 ≤ (((r + 1) ^ (d - 2))⁻¹) := by positivity
  have h3' : (((r + 1) ^ (d - 2))⁻¹) ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have h4 : exp (-(1 / 2) * √(r / ellT L g t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := Real.sqrt_nonneg (r / ellT L g t); linarith)
  have h5 : exp (-(1 / 2) * √(r / ellT L g t)) ^ 2 ≤ 1 := by
    have := Real.exp_pos (-(1 / 2) * √(r / ellT L g t))
    nlinarith
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt h3]
  have : 0 ≤ (W ^ d)⁻¹ * (g ^ 2 + |1 - t|)⁻¹ := mul_nonneg h1 h2
  calc (W ^ d)⁻¹ * (g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹ * exp (-(1 / 2) * √(r / ellT L g t)) ^ 2
      ≤ (W ^ d)⁻¹ * (g ^ 2 + |1 - t|)⁻¹ * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3' this) h5 (by positivity) (by positivity)
    _ = _ := by ring

private theorem LWTermHolds_sfT_zero_sq {d L : ℕ} {W g t : ℝ} (hW : 0 < W) :
    sfT d L W g t 0 ^ 2 = (W ^ d)⁻¹ * (g ^ 2 + |1 - t|)⁻¹ := by
  rw [sfT_zero, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

private theorem LWTermHolds_A_ge {g t Λ : ℝ} (hg : g ≤ Λ) (hg0 : 0 ≤ g) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 + Λ ^ 2)⁻¹ ≤ (g ^ 2 + |1 - t|)⁻¹ := by
  have h1 : |1 - t| ≤ 1 := by rw [abs_of_pos (by linarith)]; linarith
  have h2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg0 hg 2
  have hpos : 0 < g ^ 2 + |1 - t| := by
    have : 0 < |1 - t| := abs_pos.2 (by linarith)
    positivity
  exact inv_anti₀ hpos (by linarith)

private theorem LWTermHolds_tail_cmp {d L : ℕ} {W g t ℓ D : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) (hW : 0 < W)
    (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hℓ0 : 0 ≤ ℓ) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ L) :
    (1 / 2) * (sfT d L W g t (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) ≤ (W ^ d)⁻¹ * tailW d L g t ℓ W D r ∧
      (W ^ d)⁻¹ * tailW d L g t ℓ W D r ≤
        (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) := by
  have hm : min r (min ℓ L) = min r ℓ := by
    rw [min_left_comm, min_eq_left hrL, min_comm]
  have hmm : min ℓ L ≤ L := min_le_right _ _
  have h := tailW_regime1_bounds (d := d) (L := L) (W := W) (g := g) (t := t) (ℓ := min ℓ L) (D := D) hd hL ht hW hgt
    (le_min hℓ0 (by linarith)) hmm hr
  have e : tailW d L g t ℓ W D r = tailW d L g t (min ℓ L) W D r := by
    unfold tailW; rw [hm]
  rw [e]
  rwa [hm] at h


/-- The arithmetic of the `T` side: `γ(φ + 2μAγ) + A(φ(0) + μA²) W^{-d} δ ≤ K Γ² X Z`. -/
private theorem LWTermHolds_arithT {X Γ u b s s0 w w₂ Wd μ cB cs Z Z0 δ : ℝ}
    (hX : 1 ≤ X) (hΓ : 1 ≤ Γ) (hu : 0 < u) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hbu : b ≤ u)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hw : 0 ≤ w) (hw₂ : 0 ≤ w₂) (hWd : 0 ≤ Wd)
    (hWd1 : Wd ≤ 1) (hμ0 : 0 ≤ μ) (hcB : 0 ≤ cB) (hcs : 0 ≤ cs) (hμ : μ ≤ X * (cB * (b * b)))
    (hwu : w ≤ u ^ 2 * Wd) (hwu' : w ≤ u) (hw₂w : w₂ ≤ Wd * w) (hcs' : Wd ≤ cs * s0 ^ 2)
    (hZ : u * (s ^ 2 + Wd * w) ≤ 2 * Z) (hZ0 : u * s0 ^ 2 ≤ 2 * Z0)
    (hδ : δ = 0 ∨ (δ = 1 ∧ Z0 = Z ∧ s0 = s)) :
    Γ * (s + w₂) * (X * (u * s + w) + 2 * μ * 2 * (Γ * (s + w₂))) +
        2 * (X * (u * s0 + w) + μ * 2 ^ 2) * (Wd * δ) ≤
      (6 + 16 * cB + 2 * (4 + 8 * cB) * cs) * Γ ^ 2 * X * Z := by
  have hX0 : 0 < X := by linarith
  have hZ0' : 0 ≤ Z := by
    have := mul_nonneg hu.le (add_nonneg (sq_nonneg s) (mul_nonneg hWd hw)); linarith
  have hWdw : Wd * w ≤ w := mul_le_of_le_one_left hw hWd1
  have hus : u * s ≤ u := mul_le_of_le_one_right hu.le hs1
  -- `s w ≤ u s² + u Wd w`
  have hsw : s * w ≤ u * s ^ 2 + u * Wd * w := by
    have h1 : u * (2 * (s * w)) ≤ u * (u * s ^ 2 + u * Wd * w) := by
      have h2 : w * w ≤ w * (u ^ 2 * Wd) := mul_le_mul_of_nonneg_left hwu hw
      nlinarith [sq_nonneg (u * s - w)]
    have h3 : 2 * (s * w) ≤ u * s ^ 2 + u * Wd * w := le_of_mul_le_mul_left h1 hu
    nlinarith [mul_nonneg hs hw]
  have e1 : w₂ * (u * s) ≤ u * (Wd * w) := by
    calc w₂ * (u * s) ≤ w₂ * u := mul_le_mul_of_nonneg_left hus hw₂
      _ ≤ (Wd * w) * u := mul_le_mul_of_nonneg_right hw₂w hu.le
      _ = _ := by ring
  have e2 : w₂ * w ≤ u * (Wd * w) := by
    calc w₂ * w ≤ (Wd * w) * w := mul_le_mul_of_nonneg_right hw₂w hw
      _ ≤ (Wd * w) * u := mul_le_mul_of_nonneg_left hwu' (mul_nonneg hWd hw)
      _ = _ := by ring
  have hterm1 : Γ * (s + w₂) * (X * (u * s + w)) ≤ 6 * Γ * X * Z := by
    have h4 : u * s ^ 2 + s * w + w₂ * (u * s) + w₂ * w ≤ 3 * (u * (s ^ 2 + Wd * w)) := by
      nlinarith [hsw, e1, e2, mul_nonneg hu.le (sq_nonneg s)]
    calc Γ * (s + w₂) * (X * (u * s + w)) = Γ * X * (u * s ^ 2 + s * w + w₂ * (u * s) + w₂ * w) := by ring
      _ ≤ Γ * X * (3 * (2 * Z)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hbb : b * b ≤ b := mul_le_of_le_one_right hb hb1
  have hb2 : b * b ≤ u := hbb.trans hbu
  have hterm2 : Γ * (s + w₂) * (2 * μ * 2 * (Γ * (s + w₂))) ≤ 16 * cB * Γ ^ 2 * X * Z := by
    have h1 : (s + w₂) ^ 2 ≤ 2 * (s ^ 2 + w₂ ^ 2) := by nlinarith [sq_nonneg (s - w₂)]
    have h2 : b * b * (s ^ 2 + w₂ ^ 2) ≤ 2 * Z := by
      have a1 : b * b * s ^ 2 ≤ u * s ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg s)
      have a2 : b * b * w₂ ^ 2 ≤ u * (Wd * w) := by
        have hbb1 : b * b ≤ 1 := hbb.trans hb1
        have hw2 : w₂ ^ 2 ≤ (Wd * w) * (Wd * w) := by nlinarith [mul_nonneg hw₂ hw₂]
        calc b * b * w₂ ^ 2 ≤ 1 * w₂ ^ 2 := mul_le_mul_of_nonneg_right hbb1 (sq_nonneg w₂)
          _ ≤ (Wd * w) * (Wd * w) := by linarith
          _ ≤ (Wd * w) * u := mul_le_mul_of_nonneg_left (hWdw.trans hwu') (mul_nonneg hWd hw)
          _ = _ := by ring
      nlinarith [a1, a2]
    have h3 : μ * (s + w₂) ^ 2 ≤ 4 * (X * cB * Z) := by
      calc μ * (s + w₂) ^ 2 ≤ (X * (cB * (b * b))) * (2 * (s ^ 2 + w₂ ^ 2)) :=
            mul_le_mul hμ h1 (sq_nonneg _) (by positivity)
        _ = 2 * (X * cB) * (b * b * (s ^ 2 + w₂ ^ 2)) := by ring
        _ ≤ 2 * (X * cB) * (2 * Z) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 4 * (X * cB * Z) := by ring
    calc Γ * (s + w₂) * (2 * μ * 2 * (Γ * (s + w₂))) = 4 * Γ ^ 2 * (μ * (s + w₂) ^ 2) := by ring
      _ ≤ 4 * Γ ^ 2 * (4 * (X * cB * Z)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hterm3 : 2 * (X * (u * s0 + w) + μ * 2 ^ 2) * (Wd * δ) ≤ 2 * (4 + 8 * cB) * cs * X * Z := by
    rcases hδ with h | ⟨h, hZZ, hss⟩
    · rw [h]
      have : 0 ≤ 2 * (4 + 8 * cB) * cs * X * Z := by positivity
      simpa using this
    · rw [h, hss]
      rw [hss] at hcs' hZ0
      rw [hZZ] at hZ0
      have hUW : u * Wd ≤ 2 * cs * Z := by
        calc u * Wd ≤ u * (cs * s ^ 2) := mul_le_mul_of_nonneg_left hcs' hu.le
          _ = cs * (u * s ^ 2) := by ring
          _ ≤ cs * (2 * Z) := mul_le_mul_of_nonneg_left hZ0 hcs
          _ = 2 * cs * Z := by ring
      have c1 : u * s * Wd ≤ u * Wd := mul_le_mul_of_nonneg_right hus hWd
      have c2 : w * Wd ≤ u * Wd := mul_le_mul_of_nonneg_right hwu' hWd
      have c3 : μ * Wd ≤ X * cB * (u * Wd) := by
        calc μ * Wd ≤ (X * (cB * (b * b))) * Wd := mul_le_mul_of_nonneg_right hμ hWd
          _ = X * cB * ((b * b) * Wd) := by ring
          _ ≤ X * cB * (u * Wd) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb2 hWd) (by positivity)
      calc 2 * (X * (u * s + w) + μ * 2 ^ 2) * (Wd * 1)
          = 2 * X * (u * s * Wd) + 2 * X * (w * Wd) + 8 * (μ * Wd) := by ring
        _ ≤ 2 * X * (u * Wd) + 2 * X * (u * Wd) + 8 * (X * cB * (u * Wd)) := by
            have := mul_le_mul_of_nonneg_left c1 (by positivity : (0:ℝ) ≤ 2 * X)
            have := mul_le_mul_of_nonneg_left c2 (by positivity : (0:ℝ) ≤ 2 * X)
            linarith
        _ = (4 * X + 8 * X * cB) * (u * Wd) := by ring
        _ ≤ (4 * X + 8 * X * cB) * (2 * cs * Z) := mul_le_mul_of_nonneg_left hUW (by positivity)
        _ = _ := by ring
  have hΓ2 : Γ ≤ Γ ^ 2 := by
    calc Γ = Γ * 1 := (mul_one Γ).symm
      _ ≤ Γ * Γ := mul_le_mul_of_nonneg_left hΓ (by linarith)
      _ = Γ ^ 2 := (sq Γ).symm
  have hΓ3 : 1 ≤ Γ ^ 2 := one_le_pow₀ hΓ
  have hXZ : 0 ≤ X * Z := mul_nonneg hX0.le hZ0'
  have k1 : 6 * Γ * X * Z ≤ 6 * Γ ^ 2 * X * Z := by
    have := mul_le_mul_of_nonneg_right hΓ2 hXZ
    linarith
  have k2 : 2 * (4 + 8 * cB) * cs * X * Z ≤ 2 * (4 + 8 * cB) * cs * Γ ^ 2 * X * Z := by
    have := mul_le_mul_of_nonneg_right hΓ3 (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (4 + 8 * cB) * cs) hXZ)
    linarith
  have k3 : 16 * cB * Γ ^ 2 * X * Z = 16 * cB * Γ ^ 2 * X * Z := rfl
  calc _ ≤ 6 * Γ * X * Z + 16 * cB * Γ ^ 2 * X * Z + 2 * (4 + 8 * cB) * cs * X * Z := by linarith
    _ ≤ 6 * Γ ^ 2 * X * Z + 16 * cB * Γ ^ 2 * X * Z + 2 * (4 + 8 * cB) * cs * Γ ^ 2 * X * Z := by linarith
    _ = _ := by ring

end TFacts

/-! ## 6. The `T` side: the entry and loop events -/

section TSide

/-- **`(eq:directG2)`** (`7_8:24-30`): off the diagonal, w.h.p. `|G_{xy}| ≲ N^{2τ₁} (𝖳_t(|[x]-[y]| ∧ ℓ) + w₂)`, `w₂ = (W^{d+D₂})^{-1/2}`,
on the sizes with `1 - t > ĝ²/L²`: `lwGbyXi_holds` (`(GijGEX)`), the loop events of `(LW_assm_exp)`, the comparison `W^{-d} 𝒯̃ ≲ 𝖳² + W^{-d-D₂}`
(`tailW_regime1_bounds`) and the shift `𝖳(max(r-2,0)) ≲ 𝖳(r)` (`LWTermHolds_sfT_shift`) inside `LWTermHolds_xiSq_le`. -/
theorem LWTermHolds_Gij_T {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ)
    {D₂ : ℝ} (hD₂ : 0 < D₂) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    ∃ Cξ : ℝ, 1 ≤ Cξ ∧ sz.Whp (fun n => {ω | sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n →
      ∀ o c : Idx d (sz.L n) (sz.W n), o ≠ c → ‖Gt sz n (STflowE z n) (t n) true ω o c‖ ≤
        Cξ * ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) * (sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
          (min ((zdistInf d (sz.L n) (STblk sz n o - STblk sz n c) : ℕ) : ℝ) (ℓ n)) +
          Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D₂)))}) := by
  obtain ⟨hadm, hE, htlt, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize := sz.tendsto_size hsz
  obtain ⟨hε₀, -, hinit, hℓ0, -, hloopE⟩ := hA
  set Λ : ℝ := 𝔡⁻¹ with hΛ
  set Ks : ℝ := Real.sqrt (3 ^ (d - 2)) * Real.exp (Real.sqrt 2 / 2) with hKs
  have hKs1 : 1 ≤ Ks := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (3 ^ (d - 2)) := by
      rw [Real.one_le_sqrt]; exact one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.exp (Real.sqrt 2 / 2) := Real.one_le_exp (by positivity)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  set ct : ℝ := 1 + 2 ^ (d - 1) with hct
  have hct1 : (1 : ℝ) ≤ ct := by rw [hct]; linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := d - 1)]
  set Cξ : ℝ := (2 * 3 ^ (2 * d) * ct + (1 + Λ ^ 2)) * Ks ^ 2 with hCξ
  have hCξ1 : 1 ≤ Cξ := by
    have h1 : (1 : ℝ) ≤ 2 * 3 ^ (2 * d) * ct + (1 + Λ ^ 2) := by
      have : (0 : ℝ) ≤ 2 * 3 ^ (2 * d) * ct := by positivity
      nlinarith [sq_nonneg Λ]
    have h2 : (1 : ℝ) ≤ Ks ^ 2 := one_le_pow₀ hKs1
    exact one_le_mul_of_one_le_of_one_le h1 h2
  refine ⟨Cξ, hCξ1, ?_⟩
  have hent := hinit.1
  have Ea := Sizes.Prec.whp sz (lwGbyXi_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hent
    (fun _ => 1) (fun _ => 0) (fun _ => le_rfl) (fun _ => by norm_num)) hτ₁
  have Eb := Sizes.Prec.whp sz (hloopE D₂ hD₂) hτ₁
  refine HighProbAt.mono (HighProbAt.inter hsize Ea Eb) ?_
  filter_upwards [hflow.1.2.2.2.2, hsize.eventually (eventually_ge_atTop 1)] with n hWO hN1 ω hω hP o c hoc
  obtain ⟨hωa, hωb⟩ := hω
  have hX1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ τ₁ with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hX1' hτ₁.le
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  have hg0 : 0 ≤ sz.lam n := (Real.rpow_pos_of_pos hW0 _).le.trans hWO.1
  have hg : sz.lam n ≤ Λ := hWO.2
  have hℓn := hℓ0 n
  have hℓt : 1 ≤ ellT (sz.L n) (sz.lam n) (t n) := one_le_ellT hL1
  set w₂ : ℝ := Real.sqrt ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D₂)) with hw₂def
  have hw₂0 : 0 ≤ w₂ := Real.sqrt_nonneg _
  have hw₂sq : w₂ ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D₂) :=
    Real.sq_sqrt (mul_nonneg (by positivity) (Real.rpow_nonneg hW0.le _))
  set Φn : ℝ → ℝ := fun r => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) (min r (ℓ n)) + w₂ with hΦn
  have hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r := fun r _ => add_nonneg (sfT_nonneg _) hw₂0
  -- the comparison `Φn(m) ≤ K Φn(ℓ')` for `ℓ' ≤ 2 + m`
  have hcmp : ∀ ℓ' m : ℝ, 0 ≤ ℓ' → 0 ≤ m → ℓ' ≤ 2 * (fun _ : ℕ => (1 : ℝ)) n + m → Φn m ≤ Ks * Φn ℓ' := by
    intro ℓ' m hℓ' hm hlm
    have hu0 : 0 ≤ min ℓ' (ℓ n) := le_min hℓ' hℓn
    have h1 : min ℓ' (ℓ n) ≤ min m (ℓ n) + 2 := by
      have : min ℓ' (ℓ n) ≤ min (m + 2) (ℓ n + 2) := min_le_min (by linarith) (by linarith)
      exact this.trans_eq (min_add_add_right m (ℓ n) 2)
    have h2 : max (min ℓ' (ℓ n) - 2) 0 ≤ min m (ℓ n) := max_le (by linarith) (le_min hm hℓn)
    have h3 := sfT_antitone (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
      (le_max_right _ _) h2
    have h4 := LWTermHolds_sfT_shift (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n) hℓt hu0
    simp only [hΦn]
    nlinarith [sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n) (min ℓ' (ℓ n)), hKs1]
  -- `W^{-d} ≤ (1 + Λ²) Φn(0)²`
  have hΦ0 : sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) 0 ≤ Φn 0 := by
    simp only [hΦn, min_eq_left hℓn]; linarith
  have hWd0 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (Real.sqrt (1 + Λ ^ 2)) ^ 2 * Φn 0 ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    have h1 := LWTermHolds_sfT_zero_sq (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hW0
    have h2 := LWTermHolds_A_ge hg hg0 (ht0 n) (htlt n)
    have h3 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 + Λ ^ 2)⁻¹ ≤ sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) 0 ^ 2 := by
      rw [h1]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (1 + Λ ^ 2) * sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) 0 ^ 2 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + Λ ^ 2)
      rwa [show (1 + Λ ^ 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 + Λ ^ 2)⁻¹) = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ by
        field_simp] at this
    exact h4.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sfT_nonneg _) hΦ0 2) (by positivity))
  -- the loop bound
  have hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖Lloop sz n (STflowE z n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
        (X * ct) * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2 := fun s b₁ b₂ => by
    refine (hωb (s, b₁, b₂)).trans ?_
    have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrL : ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast lwMoment_zdistInf_le (sz.L n) (b₁ - b₂)
    have hc := (LWTermHolds_tail_cmp (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n) (ℓ := ℓ n)
      (D := D₂) (by omega) hL1 (htlt n) hW0 hP.le hℓn hr0 hrL).2
    have hs0 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
      (min ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) (ℓ n))
    have hsq : sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) (min ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) (ℓ n)) ^ 2 +
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D₂) ≤ Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2 := by
      rw [← hw₂sq]; simp only [hΦn]; nlinarith [mul_nonneg hs0 hw₂0]
    calc X * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D₂
          ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ))
        ≤ X * (ct * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hsq (by positivity))) (by positivity)
      _ = _ := by ring
  have hxi := LWTermHolds_xiSq_le sz (STflowE z) t (fun _ => 1) n ω Φn (by norm_num) (B := X * ct) (K := Ks)
    (C₃ := Real.sqrt (1 + Λ ^ 2)) (by positivity) hloop hΦnn hcmp hWd0 (STblk sz n o) (STblk sz n c)
  have hG := hωa ⟨((o, c), (STblk sz n o, STblk sz n c)), hoc, by simp [STblk], by simp [STblk]⟩
  simp only at hG
  set r : ℝ := ((zdistInf d (sz.L n) (STblk sz n o - STblk sz n c) : ℕ) : ℝ) with hr
  have hΦr : 0 ≤ Φn r := hΦnn r (Nat.cast_nonneg _)
  have hCX : 1 ≤ Cξ * X := one_le_mul_of_one_le_of_one_le hCξ1 hX1
  have hxi2 : lwXiSq sz (STflowE z) t (fun _ => 1) n (STblk sz n o) (STblk sz n c) ω ≤ (Cξ * X * Φn r) ^ 2 := by
    refine hxi.trans ?_
    have h1 : (2 * (2 * (1 : ℝ) + 1) ^ (2 * d) * (X * ct) + Real.sqrt (1 + Λ ^ 2) ^ 2) * Ks ^ 2 ≤ Cξ * X := by
      rw [Real.sq_sqrt (by positivity), hCξ]
      have : (2 * (2 * (1 : ℝ) + 1) ^ (2 * d) * (X * ct) + (1 + Λ ^ 2)) ≤ (2 * 3 ^ (2 * d) * ct + (1 + Λ ^ 2)) * X := by
        have h1X : (1 + Λ ^ 2) ≤ (1 + Λ ^ 2) * X := le_mul_of_one_le_right (by positivity) hX1
        have e1 : (2 * (2 * (1 : ℝ) + 1) ^ (2 * d) * (X * ct) + (1 + Λ ^ 2)) = 2 * 3 ^ (2 * d) * ct * X + (1 + Λ ^ 2) := by
          norm_num; ring
        have e2 : (2 * 3 ^ (2 * d) * ct + (1 + Λ ^ 2)) * X = 2 * 3 ^ (2 * d) * ct * X + (1 + Λ ^ 2) * X := by ring
        rw [e1, e2]; linarith
      calc _ ≤ ((2 * 3 ^ (2 * d) * ct + (1 + Λ ^ 2)) * X) * Ks ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
    calc _ ≤ Cξ * X * Φn r ^ 2 := by
          have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Φn r)); linarith
      _ ≤ (Cξ * X) ^ 2 * Φn r ^ 2 := mul_le_mul_of_nonneg_right (le_self_pow₀ hCX two_ne_zero) (sq_nonneg _)
      _ = _ := by ring
  have hvar : lwXiVar sz (STflowE z) t (fun _ => 1) n (STblk sz n o) (STblk sz n c) ω ≤ Cξ * X * Φn r :=
    Real.sqrt_le_iff.2 ⟨by positivity, hxi2⟩
  calc ‖Gt sz n (STflowE z n) (t n) true ω o c‖ ≤ X * lwXiVar sz (STflowE z) t (fun _ => 1) n (STblk sz n o) (STblk sz n c) ω := hG
    _ ≤ X * (Cξ * X * Φn r) := mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = Cξ * ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) * Φn r := by
        rw [show ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) = X * X by
          rw [hXdef, ← Real.rpow_add (by linarith)]; ring_nf]
        ring

/-- **`(GavLGEX)` at `Ψ_t = max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})`** (`7_8:62-66`, `(eq:recolterm2)`): `max_a |𝓛^{(1)}_{+,a} - m| ≤ N^{τ₁} Ψ_t²` w.h.p.;
`(initialGT2)` is `LWInit.1` (from `ε₀` down to `ε₁ ≤ ε₀`), the loop bound `max 𝓛^{(2)} ≺ Ψ_t²` is `(LW_assm_exp)` at `D = 1` (`wT(r) ≤ wT(0)`),
the window is `Bctl ≤ N^{-c}` (`lwN_Bctl_le`). -/
theorem LWTermHolds_avg_T {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ)
    {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    sz.Whp (fun n => {ω | ∀ a : Zd d (sz.L n),
      ‖Lloop sz n (STflowE z n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (STflowE z n)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2}) := by
  obtain ⟨hadm, hE, htlt, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize := sz.tendsto_size hsz
  obtain ⟨hε₀, -, hinit, hℓ0, -, hloopE⟩ := hA
  have h𝔠 : 0 < 𝔠 := hadm.1
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (min ε₀ ((d : ℝ) * c / 2)) ((d : ℝ) / 2) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min (lt_min hε₀ (by positivity)) (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₁b : 2 * ε₁ ≤ (d : ℝ) * c := by
    have : ε₁ ≤ (d : ℝ) * c / 2 := by rw [hε₁def]; exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hε₁c : ε₁ ≤ (d : ℝ) / 2 := by rw [hε₁def]; exact min_le_right _ _
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  -- the control parameter `Ψ_t` and its window
  have hup : ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
    filter_upwards [lwN_Bctl_le sz hκ hε h𝔡 hflow htT] with n hn
    have h1 := hn (t n) (ht0 n) le_rfl
    rw [← hcdef] at h1
    have h2 := lwN_size_rpow_neg_le sz n hc.le
    have h3 : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) :=
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
    exact (h1.trans h2).trans h3
  have hwin := LWWindow_max_Bctl sz hε₁c t hup
  have hent' : sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) := by
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  -- `max 𝓛^{(2)} ≺ Ψ_t²` from `(LW_assm_exp)` at `D = 1`
  have hmax : sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (STflowE z n) (t n) ω)
      (fun n _ _ => (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2) := by
    apply lwMoment_prec_of_whp
    intro τ hτ
    refine ⟨_, Sizes.Prec.whp sz (hloopE 1 one_pos) hτ, ?_⟩
    refine Eventually.of_forall fun n => ?_
    intro ω hω u
    unfold STmaxLoop2
    refine Finset.sup'_le _ _ fun q _ => ?_
    refine (hω (false, q.1, q.2)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) ≤
        tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 0 :=
      tailW_antitone (hℓ0 n) le_rfl hr0
    have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2 := by
      have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hWpos n).le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
          Real.rpow_neg (hWpos n).le, Real.rpow_natCast]
      rw [← e]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (hWpos n).le _) (le_max_left _ _) 2
    have hB : sz.Bctl n (t n) ≤ (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2 := by
      have hB0 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
      calc sz.Bctl n (t n) = Real.sqrt (sz.Bctl n (t n)) ^ 2 := (Real.sq_sqrt hB0).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
    have hT0 : tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 0 =
        max (Bparam d (sz.L n) (sz.lam n) (t n) 0) (((sz.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
      unfold tailW; rw [min_eq_left (hℓ0 n), tailT_zero]
    have hWn : ((sz.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hW1 n) (by norm_num)
    have hWd0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 0 :=
          mul_le_mul_of_nonneg_left h1 hWd0
      _ = max ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) 0)
            ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
          rw [hT0]; exact mul_max_of_nonneg _ _ hWd0
      _ ≤ _ := max_le hB (by
          calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left hWn hWd0
            _ ≤ _ := by rw [mul_one]; exact hWd)
  have hGav := (RBM.Green.stGbEXP_holds hd).2.2 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₁ hε₁pos
  exact Sizes.Prec.whp sz (hGav _ (hwin.mono fun n hn => hn.1) (hwin.mono fun n hn => hn.2) hent' hmax) hτ₁

set_option maxHeartbeats 1600000 in
-- one long pathwise estimate: eight events, thirty size facts and the arithmetic lemma in one proof
/-- **The `T`-side reduction** for `D ≥ 2d + 1` (`7_8:20-58`, `(eq:recolterm2)`, `(eq:recoltermwt2)`): from `f_{xy} ≺ η_t⁻¹ B^{1/2} 𝖳_t(|a-b|∧ℓ) + W^{-D}`,
`(eq:directG2)` (`LWTermHolds_Gij_T`, `D₂ = d + 2D`), `LWTermHolds_diag_whp` and `LWTermHolds_avg_T`, on the sizes with `1 - t > ĝ²/L²`.  The restriction `D ≥ 2d + 1` is where
the cross term `W^{-D} 𝖳` is absorbed (paper-delta candidate `T2375c`). -/
theorem LWTermHolds_reduceT_core {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ)
    {D : ℝ} (hD : 2 * (d : ℝ) + 1 ≤ D)
    (hf : sz.Prec (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖)
      (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
          (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))) :
    sz.Prec (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) := by
  obtain ⟨hadm, hE, htlt, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => (hE n).trans (by linarith)
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize := sz.tendsto_size hsz
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hband := hadm.2.2.2.1
  have hD0 : 0 < D := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  refine lwMoment_prec_of_whp sz fun τ hτ => ?_
  have hτ₁ : 0 < τ / 6 := by positivity
  obtain ⟨Cξ, hCξ1, EG⟩ := LWTermHolds_Gij_T hd hκ hε h𝔡 sz hflow ht0 htT hA (D₂ := (d : ℝ) + 2 * D) (by positivity) hτ₁
  have E1 := Sizes.Prec.whp sz hf hτ₁
  have E3 := LWTermHolds_diag_whp (sz := sz) (STflowE z) t h𝔠 hA.1 hband (fun n => (hE2 n).le) hA.2.2.1.1
  have E4 := LWTermHolds_avg_T hd hκ hε h𝔡 sz hflow ht0 htT hA hτ₁
  refine ⟨_, HighProbAt.inter hsize (HighProbAt.inter hsize (HighProbAt.inter hsize E1 EG) E3) E4, ?_⟩
  set Λ : ℝ := 𝔡⁻¹ with hΛ
  set K0 : ℝ := 6 + 16 * (1 + Λ ^ 2) + 2 * (4 + 8 * (1 + Λ ^ 2)) * (1 + Λ ^ 2) with hK0
  have hK0pos : 0 ≤ K0 := by positivity
  have hK : ∀ᶠ n in atTop, 2 * K0 * Cξ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 6) :=
    ((tendsto_rpow_atTop hτ₁).comp hsz).eventually_ge_atTop _
  have hWbig : ∀ᶠ n in atTop, 1 + Λ ^ 2 ≤ ((sz.W n : ℕ) : ℝ) := by
    filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (1 + Λ ^ 2)] with n hb hn
    exact hn.trans hb
  filter_upwards [hflow.1.2.2.2.2, lwN_Bctl_le sz hκ hε h𝔡 hflow htT, hK, hWbig,
    hsize.eventually (eventually_ge_atTop 1)] with n hWO hBc hKn hWn hN1
  rintro ω ⟨⟨⟨hω1, hωG⟩, hω3⟩, hω4⟩ ⟨⟨σ, a⟩, hP⟩
  have hX1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 6) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hX1' hτ₁.le
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  have hg0 : 0 ≤ sz.lam n := (Real.rpow_pos_of_pos hW0 _).le.trans hWO.1
  have hg : sz.lam n ≤ Λ := hWO.2
  have hℓn := hA.2.2.2.1 n
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE2 n) (htlt n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one (hE2 n) (ht0 n) (htlt n)
  have hI : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  -- `B_{t,0}` and `Bctl`
  have hAge := LWTermHolds_A_ge hg hg0 (ht0 n) (htlt n)
  have hBpar : (sz.lam n ^ 2 + |1 - t n|)⁻¹ ≤ Bparam d (sz.L n) (sz.lam n) (t n) 0 := by
    unfold Bparam; simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    have : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - t n|)⁻¹ := by positivity
    linarith
  set Wd : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  have hWd1 : Wd ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have hBctl : sz.Bctl n (t n) = Wd * Bparam d (sz.L n) (sz.lam n) (t n) 0 := rfl
  have hBlow : Wd ≤ (1 + Λ ^ 2) * sz.Bctl n (t n) := by
    have h1 : Wd * (1 + Λ ^ 2)⁻¹ ≤ sz.Bctl n (t n) := by
      rw [hBctl]; exact mul_le_mul_of_nonneg_left (hAge.trans hBpar) hWd0.le
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + Λ ^ 2)
    rwa [show (1 + Λ ^ 2) * (Wd * (1 + Λ ^ 2)⁻¹) = Wd by field_simp] at this
  have hB0 : 0 < sz.Bctl n (t n) := by
    have : 0 < Wd * (1 + Λ ^ 2)⁻¹ := by positivity
    rw [hBctl]; exact lt_of_lt_of_le this (mul_le_mul_of_nonneg_left (hAge.trans hBpar) hWd0.le)
  have hB1 : sz.Bctl n (t n) ≤ 1 := by
    have h1 := hBc (t n) (ht0 n) le_rfl
    refine h1.trans (Real.rpow_le_one_of_one_le_of_nonpos hX1' (by
      have : 0 < min (2 * 𝔡 * 𝔠) ε := lt_min (by positivity) hε
      linarith))
  set b : ℝ := Real.sqrt (sz.Bctl n (t n)) with hbdef
  have hb0 : 0 < b := Real.sqrt_pos.2 hB0
  have hbb : b * b = sz.Bctl n (t n) := Real.mul_self_sqrt hB0.le
  have hb1 : b ≤ 1 := by rw [hbdef, Real.sqrt_le_one]; exact hB1
  set u : ℝ := (etaT (STflowE z n) (t n))⁻¹ * b with hudef
  have hu0 : 0 < u := by positivity
  have hbu : b ≤ u := le_mul_of_one_le_left hb0.le hI
  have e12 : (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) = b := by rw [hbdef, Real.sqrt_eq_rpow]
  -- the sizes of `w = W^{-D}` and `w₂`
  have hWdr : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) = Wd := by rw [hWd, Real.rpow_neg hW0.le, Real.rpow_natCast]
  set w : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-D) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hW0 _
  have hwW : (1 + Λ ^ 2) * w ≤ Wd ^ 2 := by
    have h1 : w ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * (d : ℝ) + 1)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(2 * (d : ℝ) + 1)) = Wd ^ 2 * (((sz.W n : ℕ) : ℝ))⁻¹ := by
      rw [show -(2 * (d : ℝ) + 1) = -(d : ℝ) + -(d : ℝ) + -1 by ring, Real.rpow_add hW0, Real.rpow_add hW0, hWdr,
        Real.rpow_neg_one]
      ring
    have h3 : (1 + Λ ^ 2) * (((sz.W n : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hW0]; exact hWn
    calc (1 + Λ ^ 2) * w ≤ (1 + Λ ^ 2) * (Wd ^ 2 * (((sz.W n : ℕ) : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity)
      _ = Wd ^ 2 * ((1 + Λ ^ 2) * (((sz.W n : ℕ) : ℝ))⁻¹) := by ring
      _ ≤ Wd ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := mul_one _
  have hwb : w ≤ b := by
    have h1 : w ≤ Wd / (1 + Λ ^ 2) := by
      rw [le_div_iff₀ (by positivity), mul_comm]; nlinarith [hwW, hWd1, hWd0]
    have h2 : Wd / (1 + Λ ^ 2) ≤ sz.Bctl n (t n) := by
      rw [div_le_iff₀ (by positivity), mul_comm]; exact hBlow
    exact (h1.trans h2).trans (by rw [← hbb]; exact mul_le_of_le_one_right hb0.le hb1)
  have hwu : w ≤ u ^ 2 * Wd := by
    have h1 : Wd ^ 2 / (1 + Λ ^ 2) ≥ w := by rw [ge_iff_le, le_div_iff₀ (by positivity), mul_comm]; exact hwW
    have h2 : Wd / (1 + Λ ^ 2) ≤ u ^ 2 := by
      calc Wd / (1 + Λ ^ 2) ≤ sz.Bctl n (t n) := by
            rw [div_le_iff₀ (by positivity), mul_comm]; exact hBlow
        _ = b * b := hbb.symm
        _ ≤ u * u := mul_le_mul hbu hbu hb0.le hu0.le
        _ = u ^ 2 := (sq u).symm
    calc w ≤ Wd ^ 2 / (1 + Λ ^ 2) := h1
      _ = (Wd / (1 + Λ ^ 2)) * Wd := by ring
      _ ≤ u ^ 2 * Wd := mul_le_mul_of_nonneg_right h2 hWd0.le
  have hwu' : w ≤ u := hwb.trans hbu
  have hw₂ : Real.sqrt (Wd * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) + 2 * D))) = Wd * w := by
    have : Wd * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) + 2 * D)) = (Wd * w) ^ 2 := by
      rw [show -((d : ℝ) + 2 * D) = -(d : ℝ) + (-D) + (-D) by ring, Real.rpow_add hW0, Real.rpow_add hW0, hWdr, hwdef]
      ring
    rw [this]; exact Real.sqrt_sq (by positivity)
  -- the profile `𝖳` and the target `Z`
  set sf : ℕ → ℝ := fun r => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) with hsf
  have hsf0 : ∀ r, 0 ≤ sf r := fun r => sfT_nonneg _
  have hsf1 : ∀ r, sf r ≤ 1 := fun r => by
    have h1 := LWTermHolds_sfT_sq_le (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hW0 (le_min (Nat.cast_nonneg r) hℓn)
    have h2 : Wd * (sz.lam n ^ 2 + |1 - t n|)⁻¹ ≤ sz.Bctl n (t n) := by
      rw [hBctl]; exact mul_le_mul_of_nonneg_left hBpar hWd0.le
    exact (pow_le_one_iff_of_nonneg (hsf0 r) two_ne_zero).1 (h1.trans (h2.trans hB1))
  have hs0sq : Wd ≤ (1 + Λ ^ 2) * sf 0 ^ 2 := by
    have h1 := LWTermHolds_sfT_zero_sq (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hW0
    have h3 : Wd * (1 + Λ ^ 2)⁻¹ ≤ sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) 0 ^ 2 := by
      rw [h1]; exact mul_le_mul_of_nonneg_left hAge hWd0.le
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + Λ ^ 2)
    rw [show (1 + Λ ^ 2) * (Wd * (1 + Λ ^ 2)⁻¹) = Wd by field_simp] at this
    simpa [hsf, min_eq_left hℓn] using this
  set Z : ℕ → ℝ := fun r => u * (Wd * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D (r : ℝ)) with hZdef
  have hZ : ∀ r : ℕ, (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) → u * (sf r ^ 2 + Wd * w) ≤ 2 * Z r := fun r hrL => by
    have hc := (LWTermHolds_tail_cmp (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n) (ℓ := ℓ n)
      (D := D) (by omega) hL1 (htlt n) hW0 hP.le hℓn (Nat.cast_nonneg r) hrL).1
    have := mul_le_mul_of_nonneg_left hc hu0.le
    simp only [hZdef, hsf]
    nlinarith [this]
  -- the pathwise bound
  have hGx : ∀ x, ‖Gt sz n (STflowE z n) (t n) true ω x x‖ ≤ 2 := hω3
  have hγ : ∀ o c : Idx d (sz.L n) (sz.W n), o ≠ c → ‖Gt sz n (STflowE z n) (t n) true ω o c‖ ≤
      (fun r : ℕ => (Cξ * X ^ 2) * (sf r + Wd * w)) (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)) := fun o c hoc => by
    have h := hωG hP o c hoc
    have e : ((sz.size n : ℕ) : ℝ) ^ (2 * (τ / 6)) = X ^ 2 := by
      rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
    rw [e, hw₂] at h
    exact h
  have hφ : ∀ o c : Idx d (sz.L n) (sz.W n), ‖LWf sz n (STflowE z n) (t n) ω o c‖ ≤
      (fun r : ℕ => X * (u * sf r + w)) (zdistInf d (sz.L n) (STblk sz n o - STblk sz n c)) := fun o c => by
    have h := hω1 ⟨(o, c), hP⟩
    simp only at h
    rw [e12] at h
    exact h
  set Ψt : ℝ := max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) b with hΨt
  have hΨsq : Ψt ^ 2 ≤ (1 + Λ ^ 2) * (b * b) := by
    have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = Wd := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring, hWdr]
    rw [hbb]
    rcases le_total (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) b with h | h
    · rw [hΨt, max_eq_right h, ← hbb]
      have : 0 ≤ b * b := mul_nonneg hb0.le hb0.le
      nlinarith [sq_nonneg Λ]
    · rw [hΨt, max_eq_left h, e]
      exact hBlow
  have hμ : ∀ a : Zd d (sz.L n), ‖Lloop sz n (STflowE z n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (STflowE z n)‖ ≤
      X * Ψt ^ 2 := hω4
  have h := LWTermHolds_LWE_le sz n (STflowE z n) (t n) (hE2 n) (htlt n) σ a ω (A := 2) (μ := X * Ψt ^ 2)
    (γ := fun r : ℕ => (Cξ * X ^ 2) * (sf r + Wd * w)) (φ := fun r : ℕ => X * (u * sf r + w))
    (by positivity) (by norm_num) (fun r => by have := hsf0 r; positivity) (fun r => by have := hsf0 r; positivity)
    hGx hγ hφ hμ
  set r : ℕ := zdistInf d (sz.L n) (a 0 - a 1) with hr
  have hrL : (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast lwMoment_zdistInf_le (sz.L n) (a 0 - a 1)
  have hZr := hZ r hrL
  have hZ0 := hZ 0 (by simp)
  have hZnn : 0 ≤ Z r := by
    have := mul_nonneg hu0.le (add_nonneg (sq_nonneg (sf r)) (mul_nonneg hWd0.le hw0.le)); linarith
  have hμb : X * Ψt ^ 2 ≤ X * ((1 + Λ ^ 2) * (b * b)) := mul_le_mul_of_nonneg_left hΨsq (by linarith)
  have hbd := LWTermHolds_arithT (X := X) (Γ := Cξ * X ^ 2) (u := u) (b := b) (s := sf r) (s0 := sf 0) (w := w)
    (w₂ := Wd * w) (Wd := Wd) (μ := X * Ψt ^ 2) (cB := 1 + Λ ^ 2) (cs := 1 + Λ ^ 2) (Z := Z r) (Z0 := Z 0)
    (δ := if a 1 = a 0 then 1 else 0) hX1 (one_le_mul_of_one_le_of_one_le hCξ1 (one_le_pow₀ hX1)) hu0 hb0.le hb1 hbu
    (hsf0 r) (hsf1 r) hw0.le (by positivity) hWd0.le hWd1 (by positivity) (by positivity) (by positivity) hμb hwu hwu'
    le_rfl hs0sq hZr (by nlinarith [mul_nonneg hu0.le (mul_nonneg hWd0.le hw0.le)]) (by
      by_cases hh : a 1 = a 0
      · right
        have hr0 : r = 0 := by rw [hr, ← hh, sub_self, LWTermHolds_zdistInf_zero]
        exact ⟨by simp [hh], by rw [hr0], by rw [hr0]⟩
      · left; simp [hh])
  have hN : ((sz.size n : ℕ) : ℝ) ^ τ = X ^ 6 := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  have hKX : 2 * K0 * Cξ ^ 2 ≤ X := hKn
  have e13 : (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
      (Wd * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D (r : ℝ)) = Z r := by
    rw [e12]
  change ‖LWE sz n (STflowE z n) (t n) σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ *
    (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
      ((sz.W n : ℕ) : ℝ) D (r : ℝ)))
  rw [e13, hN]
  calc ‖LWE sz n (STflowE z n) (t n) σ a ω‖ ≤ _ := h
    _ ≤ 2 * (K0 * (Cξ * X ^ 2) ^ 2 * X * Z r) := by
        have : K0 = 6 + 16 * (1 + Λ ^ 2) + 2 * (4 + 8 * (1 + Λ ^ 2)) * (1 + Λ ^ 2) := hK0
        rw [this]
        linarith [hbd]
    _ = (2 * K0 * Cξ ^ 2) * (X ^ 5 * Z r) := by ring
    _ ≤ X * (X ^ 5 * Z r) := mul_le_mul_of_nonneg_right hKX (by positivity)
    _ = X ^ 6 * Z r := by ring

/-- **The Markov step for `lem:LW_moment_exp`** (`7_8:86-91`): `f_{xy} ≺ η_t⁻¹ B^{1/2} 𝖳_t(|a-b|∧ℓ) + W^{-D}` on the sizes with `1 - t > ĝ²/L²`, from
`lwMomentExp_holds` at `D' = pD` (`a^p + (W^{-D})^p ≤ (a + W^{-D})^p`) and `LWInteg`. -/
theorem LWTermHolds_fT {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ)
    {D : ℝ} (hD : 0 < D) :
    sz.Prec (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖)
      (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
          (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨hadm, hE, htlt, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => (hE n).trans (by linarith)
  have hsz : sz.SizeTendsto := hadm.2.2.1
  refine LWTermHolds_prec_of_moments sz hsz (V := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
    (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖)
    (fun n q => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
      sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D)) (C := 2) ?_ (fun n q ω => norm_nonneg _)
    (fun p n q => lwInteg_holds d sz n (STflowE z n) (t n) (hE2 n) (ht0 n) (htlt n) p q.1.1 q.1.2) ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    refine (Nat.cast_le.2 (Fintype.card_subtype_le _)).trans ?_
    rw [Fintype.card_prod, sz.card_Idx n, Real.rpow_two]
    push_cast; ring_nf; exact le_rfl
  · refine Eventually.of_forall fun n q => ?_
    have h1 : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos (Nat.cast_pos.2 (sz.W_pos n)) _
    have h2 : 0 < (etaT (STflowE z n) (t n))⁻¹ := inv_pos.2 (etaT_pos (hE2 n) (htlt n))
    have h3 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
    have h4 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
      (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))
    positivity
  · intro τ₀ hτ₀ D' hD'
    set p₀ : ℕ := ⌈(D' + 2) / τ₀⌉₊ + 1 with hp₀
    have hp2 : 2 ∣ 2 * p₀ := dvd_mul_right _ _
    have hpD : 0 < ((2 * p₀ : ℕ) : ℝ) * D := mul_pos (by positivity) hD
    have hH := lwMomentExp_holds d hd κ ε 𝔡 hκ hε h𝔡 (2 * p₀) hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA _ hpD
    refine ⟨2 * p₀, by omega, ?_, 1, one_pos, ?_⟩
    · have h1 : (D' + 2) / τ₀ ≤ (⌈(D' + 2) / τ₀⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : D' + 2 ≤ τ₀ * (⌈(D' + 2) / τ₀⌉₊ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hτ₀.le
        rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
      have hp : ((2 * p₀ : ℕ) : ℝ) = 2 * ((⌈(D' + 2) / τ₀⌉₊ : ℝ) + 1) := by rw [hp₀]; push_cast; ring
      rw [hp]
      nlinarith [h2, hτ₀]
    · have h1 := (st6_prec_det_iff sz hsz _ _).1 hH 1 one_pos
      filter_upwards [h1] with n hn q
      refine (hn q).trans ?_
      rw [Real.rpow_one]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
      have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
      have h2 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (htlt n))).le
      have h3 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
      have h4 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
        (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))
      have e : ((sz.W n : ℕ) : ℝ) ^ (-(((2 * p₀ : ℕ) : ℝ) * D)) = (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ (2 * p₀) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
      rw [e, one_mul]
      exact pow_add_pow_le (by positivity) hw (by omega)

/-- **`lem: EWGn2_N` on the sizes with `1 - t > ĝ²/L²`, for every `D > 0`**: the reduction at `D' = max(D, 2d + 1)` (the premise at `D'` is `LWTermHolds_fT`), then
`wT_{D'} ≤ wT_D`. -/
theorem LWTermHolds_concT {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (sz : Sizes d) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ lemT (z n)) {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ)
    {D : ℝ} (hD : 0 < D) :
    sz.Prec (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖)
      (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) := by
  obtain ⟨hadm, hE, htlt, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => (hE n).trans (by linarith)
  have hsize := sz.tendsto_size hadm.2.2.1
  have hD'0 : 0 < max D (2 * (d : ℝ) + 1) := lt_max_of_lt_left hD
  have h1 := LWTermHolds_reduceT_core hd hκ hε h𝔡 sz hflow ht0 htT hA (le_max_right _ _)
    (LWTermHolds_fT hd hκ hε h𝔡 sz hflow ht0 htT hA hD'0)
  refine lwN_prec_mono hsize (c := 1) ?_ h1
  refine Eventually.of_forall fun n => ?_
  rintro ⟨⟨σ, a⟩, hP⟩ ω
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have h2 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (htlt n))).le
  have h3 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
  have h4 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have h5 : 0 ≤ tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) :=
    (tailW_pos hW0 _).le
  have hle : tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) (max D (2 * (d : ℝ) + 1)) ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := by
    unfold tailW
    exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [le_max_left D (2 * (d : ℝ) + 1)]))
  refine ⟨by positivity, ?_⟩
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle h4) (mul_nonneg h2 (Real.rpow_nonneg h3 _))

/-- **`lem: EWGn2_N`, reduction to the moment bound, regime `1 - t > ĝ²/L²`** (`7_8:20-58`): for `D ≥ 2d + 1` from the premise by `LWTermHolds_reduceT_core`; for
`D < 2d + 1` the premise at `D` is too weak (the cross term `W^{-D} 𝖳` of `(eq:recoltermwt2)` needs `D ≥ 2d + 1`) and the premise at `2d + 1` comes from
`lwMomentExp_holds` (`LWTermHolds_concT`; paper-delta candidate `T2375c`). -/
theorem lwReduceT_holds : ∀ d, LWReduceT d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD hf
  by_cases hD2 : 2 * (d : ℝ) + 1 ≤ D
  · exact LWTermHolds_reduceT_core hd hκ hε h𝔡 sz hflow ht0 htT hA hD2 hf
  · exact LWTermHolds_concT hd hκ hε h𝔡 sz hflow ht0 htT hA hD

/-- **`lem: EWGn2_N`, regime `1 - t > ĝ²/L²`** from `lwMomentExp_holds` + Markov (`LWTermHolds_fT`) + `lwReduceT_holds`. -/
theorem lwtermExpS_holds : ∀ d, LWtermExpS d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  exact lwReduceT_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
    (LWTermHolds_fT hd hκ hε h𝔡 sz hflow ht0 htT hA hD)

/-- **`lem: EWGn2_N`, regime `1 - t ≤ ĝ²/L²`**: `lwtermExpN_of_LWterm` at `lwterm_holds`. -/
theorem lwtermExpN_holds : ∀ d, LWtermExpN d := fun d => lwtermExpN_of_LWterm d (lwterm_holds d)

/-- **`lem: EWGn2_N`** (`3_5:406-415`): the union of the two index sets (`1 - t > ĝ²/L²` and `1 - t ≤ ĝ²/L²`). -/
theorem lwtermExp_holds : ∀ d, LWtermExp d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  have hS := lwtermExpS_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  have hN := lwtermExpN_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  refine StochDomAt.of_subset_union (sz.tendsto_size hflow.1.2.2.1) hS hN fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  by_cases hP : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n
  · exact Or.inl ⟨⟨u, hP⟩, hu⟩
  · exact Or.inr ⟨⟨u, not_lt.1 hP⟩, hu⟩

end TSide

end RBM.Gauss.Sizes

/-! ## 7. Compiled nonempty instances at `d = 3`

The merged data of `Graph/LWPins.lean` (`sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`;
`z0`, `flow_z0`; `t ≡ 1/16` (`tInst`, regime `1 - t > ĝ²/L²` for every `n`: `strict_all`), the flow end `t = lemT z_n` (`tEnd`); `ε₀ = 1/20`,
`Ψ0 = Φ0 ≡ W^{-1}`, `(C₁, C₂, C₃, Cc) = (2, 2, 1, 1)`, `ℓ = ℓ_t`), and the B class of `LWPsiInst` (`c₀ = 3`, `K = L`, `ε₀ = 1/5`).  Every deterministic
hypothesis of each theorem is discharged; the stochastic premises `LWInit`, `LWLoop2`, `LWLoopExp` of the LW pins stay hypotheses (other gates' pins). -/

namespace RBM.Gauss.LWTermHoldsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst Filter

/-- `|E_n| < 2` and `t_n < 1` along the preflight flow. -/
theorem LWTermHolds_flow_facts : (∀ n, |STflowE z0 n| < 2) ∧ ∀ n, tInst n < 1 := by
  obtain ⟨-, hE, ht, -⟩ := RBM.Green.v3_premises_of_stFlow sz0 (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 tInst_range.2
  exact ⟨fun n => (hE n).trans (by norm_num), ht⟩

/-- `lwInteg_holds` at `sz0`, `n = 0`, `p = 2`: `|f_{xy}|²` is integrable. -/
example (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    MeasureTheory.Integrable (fun ω => ‖LWf sz0 0 (STflowE z0 0) (tInst 0) ω x y‖ ^ 2) sz0.seqP :=
  lwInteg_holds 3 sz0 0 (STflowE z0 0) (tInst 0) (LWTermHolds_flow_facts.1 0) (tInst_range.1 0) (LWTermHolds_flow_facts.2 0) 2 x y

/-- `lwReduceB_holds` at the data, the `f`-premise being the Markov step `LWTermHolds_fB`. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :=
  lwReduceB_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) 2 2 1 (fun _ => 1) Ψ0 Φ0 (assm_of hI hL)
    (LWTermHolds_fB ⟨le_rfl, by norm_num, by norm_num, by norm_num, flow_z0, tInst_range.1, tInst_range.2, assm_of hI hL⟩)

/-- `lwterm_holds` (`lem:LWterm`) at the data. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :=
  inst_LWterm (lwterm_holds 3) hI hL

/-- `lwtermB_holds` (`lem:LWterm`, "in particular") at the B class `c₀ = 3`, `K = L`, `ε₀ = 1/5`. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 5) (fun n =>
      max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (Real.sqrt (sz0.Bctl n (tInst n)))))
    (hL : LWLoop2 sz0 (STflowE z0) tInst (LWPhiB sz0 3 (fun n => sz0.L n) tInst)) :=
  lwtermB_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 5) 3 (Real.sqrt (1 + 1 ^ 2)) (fun n => sz0.L n) _ (by norm_num) (fun n => le_rfl)
    (by norm_num) LWPsiInst.inst_window_tInst hI LWPsiInst.inst_class_tInst hL

/-- `lwReduceT_holds` (the premise `LWTermHolds_fT`) at `D = 7 ≥ 2d + 1` (the premise branch) and `D = 5 < 2d + 1` (the branch through `LWTermHolds_concT`). -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) :=
  lwReduceT_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) 7 (by norm_num)
    (LWTermHolds_fT le_rfl (by norm_num) (by norm_num) (by norm_num) sz0 flow_z0 tInst_range.1 tInst_range.2 (assmExp_of hI hL)
      (by norm_num : (0 : ℝ) < 7))

example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) :=
  lwReduceT_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) 5 (by norm_num)
    (LWTermHolds_fT le_rfl (by norm_num) (by norm_num) (by norm_num) sz0 flow_z0 tInst_range.1 tInst_range.2 (assmExp_of hI hL)
      (by norm_num : (0 : ℝ) < 5))

/-- `lwtermExpS_holds` at `t ≡ 1/16`, where the regime `1 - t > ĝ²/L²` is the whole index set (`strict_all`). -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) :=
  lwtermExpS_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) 5 (by norm_num)

/-- `lwtermExpN_holds` at the flow end `t = lemT z_n` (`inst_LWtermExpN`); the index set `1 - t ≤ ĝ²/L²` is nonempty for `n ≥ 6000`
(`LWTermHolds_N_regime_tEnd` below). -/
example (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) :=
  inst_LWtermExpN (lwtermExpN_holds 3) hI hL 5 (by norm_num)

/-- `lwtermExp_holds` (`lem: EWGn2_N`): at `t ≡ 1/16` and at the flow end `t = lemT z_n`. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) :=
  inst_LWtermExp (lwtermExp_holds 3) hI hL 5 (by norm_num)

example (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) :=
  inst_LWtermExp_endT (lwtermExp_holds 3) hI hL 5 (by norm_num)

/-- The deterministic steps at concrete numbers.  Markov (`τ₀ = 1/10`, `D = 5`): the even power `p = 2 p₀`, `p₀ = ⌈(D+2)/τ₀⌉ + 1 = 71`, has
`D + 2 ≤ τ₀ p` (`7 ≤ 14.2`); `Ψ_t(c r) ≲ Ψ_t(r)` (`c = 1/2`): `LWPsiAll.shift` at the class of the data; the regime split at `n = 0`, `t = 1/16`:
`ĝ²/L² = 2^{-16} < 15/16`, and at `t = 1 - 10^{-6}`: `1 - t = 10^{-6} ≤ 2^{-16}`. -/
example : (⌈((5 : ℝ) + 2) / (1 / 10)⌉₊ + 1 : ℕ) = 71 ∧ (5 : ℝ) + 2 ≤ (1 / 10) * ((2 * 71 : ℕ) : ℝ) := by
  refine ⟨?_, by norm_num⟩
  have : ⌈((5 : ℝ) + 2) / (1 / 10)⌉₊ = 70 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  omega

example : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ0 n (1 / 2 * r) ≤ K * Φ0 n r :=
  LWPsiAll.shift sz0 psiAll0 (by norm_num)

example : sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 < 1 - 1 / 16 ∧
    1 - (1 - 1 / 10 ^ 6 : ℝ) ≤ sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by
  have hl : sz0.lam 0 = 1 / 64 := by simp [sz0]; norm_num
  have hL : ((sz0.L 0 : ℕ) : ℝ) = 4 := by simp [sz0]
  rw [hl, hL]; norm_num

/-! ### Both regimes of `lem: EWGn2_N` at concrete data

`t ≡ 1/16` is in the regime `1 - t > ĝ²/L²` for every `n` (`strict_all`); the flow end `t = lemT z_n` is in the regime `1 - t ≤ ĝ²/L²` for `n ≥ 6000`
(compiled below from `lemma28_quant`); the sequence that alternates the two exercises the union in `lwtermExp_holds`. -/

/-- `N_n = 2^{21} (n+1)^{18}` and `ĝ²/L² = 2^{-16}(n+1)^{-14}` for `sz0`. -/
theorem LWTermHolds_sz0_size_real (n : ℕ) : ((sz0.size n : ℕ) : ℝ) = 2 ^ 21 * ((n : ℝ) + 1) ^ 18 := by
  simp only [Sizes.size, sz0]
  push_cast
  ring

theorem LWTermHolds_sz0_ratio (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 = (2 : ℝ) ^ (-16 : ℤ) * ((n : ℝ) + 1) ^ (-14 : ℤ) := by
  simp only [sz0]
  push_cast
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp
  ring

/-- `54 N^{-4/5} ≤ ĝ²/L²` for `n ≥ 6000`. -/
theorem LWTermHolds_sz0_eta_le (n : ℕ) (hn : 6000 ≤ n) :
    54 * ((sz0.size n : ℕ) : ℝ) ^ (-(4 / 5 : ℝ)) ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by
  rw [LWTermHolds_sz0_ratio, LWTermHolds_sz0_size_real]
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx : (6000 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast (by omega : 6000 ≤ n + 1)
  have hx0 : 0 < x := by linarith
  have hN0 : (0 : ℝ) < 2 ^ 21 * x ^ 18 := by positivity
  set y : ℝ := (2 ^ 21 * x ^ 18) ^ (-(4 / 5 : ℝ)) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hN0 _
  have hy5 : y ^ 5 = ((2 : ℝ) ^ 21 * x ^ 18) ^ (-4 : ℤ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, show -(4 / 5 : ℝ) * ((5 : ℕ) : ℝ) = ((-4 : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast]
  have hz : (0 : ℝ) < (2 : ℝ) ^ (-16 : ℤ) * x ^ (-14 : ℤ) := by positivity
  rw [← pow_le_pow_iff_left₀ (by positivity) hz.le (by norm_num : (5 : ℕ) ≠ 0), mul_pow, hy5]
  have h54 : (54 : ℝ) ^ 5 ≤ 16 * x ^ 2 := by nlinarith
  have key : (54 : ℝ) ^ 5 * ((2 : ℝ) ^ 16 * x ^ 14) ^ 5 ≤ ((2 : ℝ) ^ 21 * x ^ 18) ^ 4 := by
    calc (54 : ℝ) ^ 5 * ((2 : ℝ) ^ 16 * x ^ 14) ^ 5 = (54 : ℝ) ^ 5 * (2 ^ 80 * x ^ 70) := by ring
      _ ≤ (16 * x ^ 2) * (2 ^ 80 * x ^ 70) := by gcongr
      _ = ((2 : ℝ) ^ 21 * x ^ 18) ^ 4 := by ring
  simp only [_root_.zpow_neg, zpow_ofNat]
  have e2 : (((2 : ℝ) ^ 16)⁻¹ * (x ^ 14)⁻¹) ^ 5 = ((((2 : ℝ) ^ 16) * x ^ 14) ^ 5)⁻¹ := by
    rw [← mul_inv, inv_pow]
  rw [e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **The flow end is in the regime `1 - t ≤ ĝ²/L²` for `n ≥ 6000`** (`lemma28_quant`: `η_{t₀} ≤ 16 Im z_n`, `Im m ≥ 3/10` at `|E| ≤ 19/10`,
so `1 - t₀ ≤ 54 N^{-4/5} ≤ ĝ²/L²`). -/
theorem LWTermHolds_N_regime_tEnd (n : ℕ) (hn : 6000 ≤ n) :
    1 - tEnd n ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by
  have hz := z0_im_pos n
  obtain ⟨hE, -, -, h4⟩ := lemma28_quant (z := z0 n) (κ := 1 / 10) (by norm_num) hz (z0_im_le_one n) (z0_locDomain n).1
  rw [zt_im] at h4
  have hE' := abs_le.mp hE
  have hm : (3 / 10 : ℝ) ≤ (mE (lemE (z0 n))).im := by
    rw [mE_im]
    have : (6 / 10 : ℝ) ≤ Real.sqrt (4 - lemE (z0 n) ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [hE'.1, hE'.2]
    linarith
  have h0 : 0 ≤ 1 - lemT (z0 n) := sub_nonneg.2 (lemT_lt_one hz).le
  have h1 := mul_le_mul_of_nonneg_left hm h0
  have h2 : 1 - lemT (z0 n) ≤ 54 * (z0 n).im := by
    have : (1 - lemT (z0 n)) * (3 / 10) ≤ 16 * (z0 n).im := by
      refine h1.trans (h4.trans (le_of_eq (by norm_num)))
    nlinarith [hz]
  exact h2.trans (LWTermHolds_sz0_eta_le n hn)

/-- `t_n = 1/16` for even `n`, `t_n = lemT z_n` for odd `n`: both regimes of `lem: EWGn2_N` occur. -/
def LWTermHolds_tMix : ℕ → ℝ := fun n => if Even n then tInst n else tEnd n

theorem LWTermHolds_tMix_range : (∀ n, 0 ≤ LWTermHolds_tMix n) ∧ ∀ n, LWTermHolds_tMix n ≤ lemT (z0 n) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · by_cases h : Even n
    · simp only [LWTermHolds_tMix, h, ite_true, tInst]; norm_num
    · simp only [LWTermHolds_tMix, h, ite_false, tEnd]; exact (lemT_pos (z0_im_pos n)).le
  · by_cases h : Even n
    · simp only [LWTermHolds_tMix, h, ite_true, tInst]; exact sixteenth_le_lemT n
    · simp only [LWTermHolds_tMix, h, ite_false, tEnd]; exact le_rfl


/-- The union of the two regimes at the alternating time sequence: the index set `1 - t > ĝ²/L²` contains every even `n`, the index set
`1 - t ≤ ĝ²/L²` every odd `n ≥ 6000` (both nonempty), and `lwtermExp_holds` is applied at this sequence. -/
example : sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 < 1 - LWTermHolds_tMix 0 ∧
    1 - LWTermHolds_tMix 6001 ≤ sz0.lam 6001 ^ 2 / ((sz0.L 6001 : ℕ) : ℝ) ^ 2 := by
  refine ⟨?_, ?_⟩
  · simpa [LWTermHolds_tMix] using strict_all 0
  · have h : ¬ Even 6001 := by decide
    simpa [LWTermHolds_tMix, h, tEnd] using LWTermHolds_N_regime_tEnd 6001 (by norm_num)

example (hI : LWInit sz0 (STflowE z0) LWTermHolds_tMix (1 / 20) Ψ0)
    (hL : LWLoopExp sz0 (STflowE z0) LWTermHolds_tMix (ℓT LWTermHolds_tMix)) :=
  lwtermExp_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    LWTermHolds_tMix LWTermHolds_tMix_range.1 LWTermHolds_tMix_range.2 (1 / 20) Ψ0 (ℓT LWTermHolds_tMix)
    (assmExpT_of LWTermHolds_tMix hI hL) 5 (by norm_num)

end RBM.Gauss.LWTermHoldsInst
