/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.KDecay
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.Step5Kit
import RBM3D.Loop.KLTree
import RBM3D.Loop.Primitive
import RBM3D.Loop.GLoopFlow
import RBM3D.Defs.Tail
import RBM3D.Gauss.DominationAt

/-!
# S6-06 (T2222, ST-5): `(eq:Exp(L-K)1)`, the proof of the pin `STExpLKLKHi`

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:56-66` (`(eq:Exp(L-K)1)`):
`𝔼ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a} ≺ (W^{-d}B_{u,0})^{11/5} Σ_b B_{u,|a₁-b|} e^{-(|a₁-b|/ℓ_u)^{1/2}}`
`≲ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}`, uniformly in `u ∈ [s,t]`.  Port of the pattern of RBM2D
`Evolution/MLExpDrift.lean` at `c9a24cf` (`MLExpDrift_norm_sbSum_le` `:141`, `_env_X` `:610`,
`_first_moment` `:717`) to `d ≥ 3`; the `d = 2` window `(2R+1)²` and the `η⁻¹M⁻³` arithmetic are
not ported: the merged lattice sum `KDecay_sum_tailT_le` replaces them.

Route.  `ℰ = W^d Σ_{x,y} (𝓛-𝒦)_{σ,(x,a₂)} S_{xy} (𝓛-𝒦)_{σ,(a₁,y)}`.  Off the union `S_n` of the
failure events of `STLKU … 2` (the factor `(x,a₂)`: `≤ N^{τ'} B²`) and `STGdecayW … 0` (the factor
`(a₁,y)`: `≤ N^{τ'}(B^{1/5} W^{-d}B_{u,|a₁-y|} e^{-(|a₁-y|/ℓ_u)^{1/2}} + W^{-D})`), with
`Σ_x |S_{xy}| = 1` (`expLK_window_le`) and the lattice sum (`expLK_latticeSum`),
`|ℰ| ≤ N^{2τ'} ((C_∞(d) + 1) (1-u)⁻¹ B^{11/5})`; `D = 2/𝔠` makes `W^{-D} ≤ N^{-2}` and `B ≥ N⁻¹`
absorbs the zero-mode part (`expLK_det_core`).  The expectation is `𝔼|ℰ| ≤ c + Env P(S_n)` outside
the failure event, with the polynomial envelope `Env ≤ N^6` (`expLK_env`, `expLK_env_poly`).
Both inputs are uniform in `u ∈ [s,t]` (`Prec` over `TimeIcc`, the union inside `P`): no grid lift.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Deterministic steps (one matrix, one size) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The window sum** (RBM2D `MLExpDrift_norm_sbSum_le` `MLExpDrift.lean:141`, without the window `R`):
`‖ℰ^{LK×LK}‖ ≤ W^d M Σ_y f(y)` if the first factor is at most `M` and the second at most the profile
`f(y)`: `Σ_x |S_{xy}| = 1` (`SB_transpose`, `sum_norm_SB_row`, `3 ≤ L`). -/
theorem expLK_window_le {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (M : ℝ) (f : Zd d (sz.L n) → ℝ)
    (hM : ∀ x, ‖sz.STLKM n E u H σ ![x, a 1]‖ ≤ M)
    (hf : ∀ y, ‖sz.STLKM n E u H σ ![a 0, y]‖ ≤ f y) :
    ‖sz.STELKLKM n E u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * M * ∑ y : Zd d (sz.L n), f y := by
  have hL3 := sz.three_le_L n
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) x y‖ = 1 := by
    intro y
    rw [← sum_norm_SB_row d (sz.L n) (sz.lam n) hL3 y]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := congrFun (congrFun (SB_transpose d (sz.L n) (sz.lam n)) y) x
    rw [Matrix.transpose_apply] at h
    rw [h]
  have key : ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      sz.STLKM n E u H σ ![x, a 1] * SB d (sz.L n) (sz.lam n) x y * sz.STLKM n E u H σ ![a 0, y]‖ ≤
      M * ∑ y, f y := by
    calc _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          ‖sz.STLKM n E u H σ ![x, a 1] * SB d (sz.L n) (sz.lam n) x y * sz.STLKM n E u H σ ![a 0, y]‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
      _ ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), M * (‖SB d (sz.L n) (sz.lam n) x y‖ * f y) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => by
            rw [norm_mul, norm_mul]
            calc ‖sz.STLKM n E u H σ ![x, a 1]‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
                  ‖sz.STLKM n E u H σ ![a 0, y]‖
                = ‖SB d (sz.L n) (sz.lam n) x y‖ *
                  (‖sz.STLKM n E u H σ ![x, a 1]‖ * ‖sz.STLKM n E u H σ ![a 0, y]‖) := by ring
              _ ≤ ‖SB d (sz.L n) (sz.lam n) x y‖ * (M * f y) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul (hM x) (hf y) (norm_nonneg _) hM0)
                    (norm_nonneg _)
              _ = M * (‖SB d (sz.L n) (sz.lam n) x y‖ * f y) := by ring
      _ = M * ∑ y, f y := by
          rw [Finset.sum_comm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum, ← Finset.sum_mul, hcol y, one_mul]
  unfold Sizes.STELKLKM
  rw [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- **The lattice sum of `6:61`**, in the form of the right side of `STGdecayW` (`W^d · STWB = Bparam`):
`W^d Σ_y W^{-d} B_{u,|a-y|} e^{-(|a-y|/ℓ_u)^{1/2}} ≤ C_∞(d) (1-u)⁻¹` (the merged `KDecay_sum_tailT_le` after
`y ↦ a - y`, `BparamR_natCast`, `√x = x^{1/2}`). -/
theorem expLK_latticeSum {d : ℕ} (sz : Sizes d) (hd : 2 ≤ d) (n : ℕ) {u : ℝ} (hlam : 0 ≤ sz.lam n)
    (hu : u < 1) (a : Zd d (sz.L n)) :
    ((sz.W n : ℕ) : ℝ) ^ d * ∑ y : Zd d (sz.L n),
        sz.STWB n u (zdistInf d (sz.L n) (a - y)) *
          Real.exp (-(((zdistInf d (sz.L n) (a - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤
      KDecay_tailC d / (1 - u) := by
  have hW : ((sz.W n : ℕ) : ℝ) ^ d ≠ 0 := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have h1 : ∀ y : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ d *
      (sz.STWB n u (zdistInf d (sz.L n) (a - y)) *
        Real.exp (-(((zdistInf d (sz.L n) (a - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) =
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - y) : ℝ) := by
    intro y
    unfold Sizes.STWB tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
    field_simp
  rw [Finset.mul_sum]
  calc ∑ y : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ d *
        (sz.STWB n u (zdistInf d (sz.L n) (a - y)) *
          Real.exp (-(((zdistInf d (sz.L n) (a - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)))
      = ∑ y : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a - y) : ℝ) :=
        Finset.sum_congr rfl fun y _ => h1 y
    _ = ∑ b : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) b : ℝ) :=
        Fintype.sum_equiv (Equiv.subLeft a) _ _ fun y => rfl
    _ ≤ KDecay_tailC d / (1 - u) := KDecay_sum_tailT_le hd hlam hu

/-- `‖𝒦^{(2)}_{u,σ,a}‖ ≤ (1-u)⁻¹` (`KLK_two_eq_kTwo`, `norm_kTwo_le`, `norm_mSigma`, `W ≥ 1`). -/
private theorem expLK_norm_Kloop_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖sz.STKloop n E u σ a‖ ≤ (1 - u)⁻¹ := by
  have hL3 := sz.three_le_L n
  have h : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold Sizes.STKloop
  rw [h, KLK_two_eq_kTwo]
  refine (norm_kTwo_le hL3 (norm_mSigma hE.le _) (norm_mSigma hE.le _) hu0 hu1 _ _).trans ?_
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  calc ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ * (1 - u)⁻¹ ≤ 1 * (1 - u)⁻¹ := mul_le_mul_of_nonneg_right hW this
    _ = (1 - u)⁻¹ := one_mul _

/-- **The envelope** (RBM2D `MLExpDrift_env_X` `MLExpDrift.lean:610`): `|ℰ^{LK×LK}| ≤ W^d L^d (η_u⁻² + (1-u)⁻¹)²`
for every sample: `‖𝓛^{(2)}‖ ≤ η_u⁻²` (`norm_Lloop_le`), `‖𝒦^{(2)}‖ ≤ (1-u)⁻¹`, the window sum with
`M = f = η_u⁻² + (1-u)⁻¹` and `Σ_y 1 = L^d`. -/
theorem expLK_env {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖sz.STELKLK n E u σ a ω‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * ((etaT E u)⁻¹ ^ 2 + (1 - u)⁻¹) ^ 2 := by
  set c : ℝ := (etaT E u)⁻¹ ^ 2 + (1 - u)⁻¹ with hc
  have hbd : ∀ b : Fin 2 → Zd d (sz.L n), ‖sz.STLKM n E u (sz.seqHflow n u ω) σ b‖ ≤ c := by
    intro b
    have e : sz.STLKM n E u (sz.seqHflow n u ω) σ b = sz.Lloop n E u σ b ω - sz.STKloop n E u σ b := rfl
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (sz.norm_Lloop_le n hE hu1 (k := 1) σ b ω)
      (expLK_norm_Kloop_le sz n hE hu0 hu1 σ b))
  have h := expLK_window_le sz n E u (sz.seqHflow n u ω) σ a c (fun _ => c) (fun x => hbd _) (fun y => hbd _)
  have hsum : ∑ _y : Zd d (sz.L n), c = ((sz.L n : ℕ) : ℝ) ^ d * c := by
    rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    push_cast; ring
  rw [hsum] at h
  unfold Sizes.STELKLK
  calc _ ≤ _ := h
    _ = _ := by ring

end RBM.Gauss.Sizes

/-! ## 2. Along the sequence: the floor, the polynomial envelope -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The floor** (`d ≥ 3`; RBM2D `scaleM ≤ N`): `N⁻¹ ≤ W^{-d} B_{u,0}` for `0 ≤ u < 1`: the first term of `B` is
`≥ 0` and `W^{-d} (L^d (1-u))⁻¹ ≥ (W L)^{-d}`. -/
private theorem expLK_Bctl_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u := by
  have h1 : 0 < 1 - u := by linarith
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsize : ((sz.size n : ℕ) : ℝ)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow, mul_inv]
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    calc ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.L n : ℕ) : ℝ) ^ d * 1 := by
          gcongr; linarith
      _ = ((sz.L n : ℕ) : ℝ) ^ d := mul_one _
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1, hsize]
  have h4 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h4.trans ?_
  rw [mul_add]
  have h5 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
      ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by positivity
  linarith

/-- `η_u⁻¹ ≤ N` along the flow for `u ≤ lemT z`, eventually: `1 - u ≥ 1 - lemT z ≥ Im z/(1+|z|) ≥ N^{-1+ε}/4`
(`ST_one_sub_lemT`, `‖z‖ ≤ 3`), `Im m ≥ √(2κ)/2` (`st6_mE_im_ge`), and `N^ε ≥ 8/√(2κ)`. -/
private theorem expLK_eta_inv_le {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z n) → (etaT (STflowE z n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hz.1.2.2.1
  set c0 : ℝ := Real.sqrt (2 * κ) / 2 with hc0def
  have hc0 : 0 < c0 := by positivity
  have hev := ((tendsto_rpow_atTop hε).comp hsz).eventually (eventually_ge_atTop (4 / c0))
  filter_upwards [hev] with n hn u hu
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  obtain ⟨hre, him1, him2⟩ := hz.2 n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) him1
  have hzn : ‖z n‖ ≤ 3 := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z n)
    rw [abs_of_pos him] at h1
    linarith
  have h1 := ST_one_sub_lemT him
  have hlow : N ^ (-1 + ε) / 4 ≤ 1 - lemT (z n) := by
    refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by norm_num) (by linarith [norm_nonneg (z n)])]
    nlinarith [Real.rpow_pos_of_pos hNpos (-1 + ε), norm_nonneg (z n)]
  have h1u : N ^ (-1 + ε) / 4 ≤ 1 - u := by linarith
  have hIm : c0 ≤ (mE (STflowE z n)).im := st6_mE_im_ge hκ (st6_flowE_le sz hz n)
  set a : ℝ := N ^ (1 - ε) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hNa : N ^ (-1 + ε) = a⁻¹ := by
    rw [ha, ← Real.rpow_neg hNpos.le]; congr 1; ring
  have hNab : a * N ^ ε = N := by
    rw [ha, ← Real.rpow_add hNpos]
    simp
  have hηlow : a⁻¹ / 4 * c0 ≤ etaT (STflowE z n) u := by
    unfold etaT
    rw [hNa] at h1u
    exact mul_le_mul h1u hIm hc0.le (by linarith [inv_pos.2 hapos])
  have hpos : 0 < a⁻¹ / 4 * c0 := by positivity
  calc (etaT (STflowE z n) u)⁻¹ ≤ (a⁻¹ / 4 * c0)⁻¹ := inv_anti₀ hpos hηlow
    _ = a * (4 / c0) := by field_simp
    _ ≤ a * N ^ ε := by gcongr; exact hn
    _ = N := hNab

/-- **The envelope is polynomial** on the flow, at the right end `t ≤ lemT z`:
`W^d L^d (η_t⁻² + (1-t)⁻¹)² ≤ N^6` eventually (`η_t⁻¹ ≤ N`, `(1-t)⁻¹ ≤ η_t⁻¹` since `Im m ≤ 1`,
`W^d L^d = N`, `4N⁵ ≤ N⁶`). -/
theorem expLK_env_poly {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
        ((etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ) := by
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hz.1.2.2.1
  filter_upwards [expLK_eta_inv_le sz hκ hε hz, hsz.eventually (eventually_ge_atTop 4)] with n hη hN4
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have ht1 : t n < 1 := st5_t_lt_one sz hz ht n
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz n
  have hepos : 0 < etaT (STflowE z n) (t n) := etaT_pos hE2 ht1
  have hx : (etaT (STflowE z n) (t n))⁻¹ ≤ N := hη (t n) (ht n)
  have hIm1 : (mE (STflowE z n)).im ≤ 1 := by
    have := Complex.im_le_norm (mE (STflowE z n))
    rwa [norm_mE hE2.le] at this
  have hle : etaT (STflowE z n) (t n) ≤ 1 - t n := by
    unfold etaT
    have h0 : 0 < 1 - t n := by linarith
    calc (1 - t n) * (mE (STflowE z n)).im ≤ (1 - t n) * 1 := by gcongr
      _ = 1 - t n := mul_one _
  have hy : (1 - t n)⁻¹ ≤ N := (inv_anti₀ hepos hle).trans hx
  have hx0 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 hepos).le
  have hy0 : 0 ≤ (1 - t n)⁻¹ := inv_nonneg.2 (by linarith)
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsq : (etaT (STflowE z n) (t n))⁻¹ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hsum : (etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹ ≤ 2 * N ^ 2 := by nlinarith
  have hsum0 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹ := by positivity
  have hsq2 : ((etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ (2 * N ^ 2) ^ 2 :=
    pow_le_pow_left₀ hsum0 hsum 2
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = N := by
    rw [hNdef]; simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  rw [hWL]
  have h6 : N ^ (6 : ℝ) = N ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h6]
  calc N * ((etaT (STflowE z n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ N * (2 * N ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq2 (by linarith)
    _ = 4 * N ^ 5 := by ring
    _ ≤ N ^ 6 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ N) 5]

end RBM.Gauss.Sizes

/-! ## 3. The decay step: `ℰ^{LK×LK} ≺ (1-u)⁻¹ (W^{-d}B_{u,0})^{11/5}` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The deterministic core of `expLK_prec`: outside the failure events, `|ℰ| ≤ N^{2τ'} (C_∞(d) + 1) (1-u)⁻¹ B^{11/5}`
(window sum, lattice sum, `W^{-D} ≤ N^{-2}`, `B ≥ N⁻¹`: the zero-mode part `N B² W^{-D} ≤ B^{11/5}`). -/
private theorem expLK_det_core {d : ℕ} (sz : Sizes d) (hd : 2 ≤ d) (n : ℕ) {E u τ' D : ℝ}
    (hlam : 0 ≤ sz.lam n) (hu0 : 0 ≤ u) (hu1 : u < 1) (hN : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hWD : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ))
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (h1 : ∀ x : Zd d (sz.L n), ‖sz.STLKM n E u H σ ![x, a 1]‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ' * sz.Bctl n u ^ 2)
    (h2 : ∀ y : Zd d (sz.L n), ‖sz.STLKM n E u H σ ![a 0, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' *
        (sz.Bctl n u ^ (1 / 5 : ℝ) * sz.STWB n u (zdistInf d (sz.L n) (a 0 - y)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D))) :
    ‖sz.STELKLKM n E u H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.size n : ℕ) : ℝ) ^ τ' *
      (KDecay_tailC d + 1) * ((1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set X : ℝ := N ^ τ' with hX
  set B : ℝ := sz.Bctl n u with hB
  set Wd : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hWd
  set Ld : ℝ := ((sz.L n : ℕ) : ℝ) ^ d with hLd
  set P : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-D) with hP
  set Bq : ℝ := B ^ (1 / 5 : ℝ) with hBq
  set g : Zd d (sz.L n) → ℝ := fun y => sz.STWB n u (zdistInf d (sz.L n) (a 0 - y)) *
    Real.exp (-(((zdistInf d (sz.L n) (a 0 - y) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) with hg
  have hBpos : 0 < B := STBctl_pos sz n hu1
  have hBN : N⁻¹ ≤ B := expLK_Bctl_ge sz n hu0 hu1
  have hNpos : 0 < N := by linarith
  have hWL : Wd * Ld = N := by
    rw [hNdef, hWd, hLd]; simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
  have hf : ∀ y, ‖sz.STLKM n E u H σ ![a 0, y]‖ ≤ X * (Bq * g y + P) := by
    intro y
    refine (h2 y).trans (le_of_eq ?_)
    simp only [hg, mul_assoc]
  have hwin := expLK_window_le sz n E u H σ a (X * B ^ 2) (fun y => X * (Bq * g y + P)) h1 hf
  have hsumf : ∑ y : Zd d (sz.L n), X * (Bq * g y + P) = X * (Bq * (∑ y, g y) + Ld * P) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      card_Zd, nsmul_eq_mul]
    push_cast; rw [hLd]
  rw [hsumf] at hwin
  have hlat : Wd * ∑ y, g y ≤ KDecay_tailC d / (1 - u) := expLK_latticeSum sz hd n hlam hu1 (a 0)
  have hB2 : B ^ 2 * Bq = B ^ (11 / 5 : ℝ) := by
    rw [hBq, ← Real.rpow_natCast B 2, ← Real.rpow_add hBpos]; norm_num
  have hmain : Wd * (X * B ^ 2) * (X * (Bq * (∑ y, g y) + Ld * P)) =
      X * X * (B ^ 2 * Bq * (Wd * ∑ y, g y) + B ^ 2 * (Wd * Ld) * P) := by ring
  rw [hWL, hB2] at hmain
  -- the zero-mode part
  have hNinv : N⁻¹ ≤ Bq := by
    have h0 : 0 < N⁻¹ := inv_pos.2 hNpos
    have h1' : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
    have ha : N⁻¹ ^ (1 : ℝ) ≤ N⁻¹ ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h0 h1' (by norm_num)
    rw [Real.rpow_one] at ha
    exact ha.trans (Real.rpow_le_rpow h0.le hBN (by norm_num))
  have hPN : N * P ≤ N⁻¹ := by
    have h2' : P ≤ (N ^ 2)⁻¹ := by
      refine hWD.trans (le_of_eq ?_)
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNpos.le, Real.rpow_natCast]
    calc N * P ≤ N * (N ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2' hNpos.le
      _ = N⁻¹ := by field_simp
  have hzero : B ^ 2 * N * P ≤ B ^ (11 / 5 : ℝ) := by
    calc B ^ 2 * N * P = B ^ 2 * (N * P) := by ring
      _ ≤ B ^ 2 * N⁻¹ := mul_le_mul_of_nonneg_left hPN (by positivity)
      _ ≤ B ^ 2 * Bq := mul_le_mul_of_nonneg_left hNinv (by positivity)
      _ = B ^ (11 / 5 : ℝ) := hB2
  have hB115 : 0 ≤ B ^ (11 / 5 : ℝ) := Real.rpow_nonneg hBpos.le _
  have hu' : 0 < 1 - u := by linarith
  have hone : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hu').2 (by linarith)
  have hX0 : 0 ≤ X := Real.rpow_nonneg hNpos.le _
  have hmid : B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) + B ^ 2 * N * P ≤
      (KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ)) := by
    have hl : B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) ≤ B ^ (11 / 5 : ℝ) * (KDecay_tailC d / (1 - u)) :=
      mul_le_mul_of_nonneg_left hlat hB115
    have hz2 : B ^ 2 * N * P ≤ (1 - u)⁻¹ * B ^ (11 / 5 : ℝ) := by
      calc B ^ 2 * N * P ≤ B ^ (11 / 5 : ℝ) := hzero
        _ = 1 * B ^ (11 / 5 : ℝ) := (one_mul _).symm
        _ ≤ (1 - u)⁻¹ * B ^ (11 / 5 : ℝ) := mul_le_mul_of_nonneg_right hone hB115
    calc B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) + B ^ 2 * N * P
        ≤ B ^ (11 / 5 : ℝ) * (KDecay_tailC d / (1 - u)) + (1 - u)⁻¹ * B ^ (11 / 5 : ℝ) := add_le_add hl hz2
      _ = (KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ)) := by
          rw [div_eq_mul_inv]; ring
  calc ‖sz.STELKLKM n E u H σ a‖ ≤ Wd * (X * B ^ 2) * (X * (Bq * (∑ y, g y) + Ld * P)) := by
        have := hwin
        simpa only [mul_assoc] using this
    _ = X * X * (B ^ (11 / 5 : ℝ) * (Wd * ∑ y, g y) + B ^ 2 * N * P) := hmain
    _ ≤ X * X * ((KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmid (mul_nonneg hX0 hX0)
    _ = X * X * (KDecay_tailC d + 1) * ((1 - u)⁻¹ * B ^ (11 / 5 : ℝ)) := by ring

/-- **The decay step** (`6:58-61`, `(eq:Exp(L-K)1)` before the expectation): `ℰ^{LK×LK}_{u,σ,a} ≺ (1-u)⁻¹
(W^{-d}B_{u,0})^{11/5}` uniformly in `u ∈ [s,t]`.  On the complement of the two failure events of `STLKU` (`k = 2`, the
factor `(x,a₂)`) and `STGdecayW … 0` (the factor `(a₁,y)`, at `D = 2/𝔠`) every bound holds for every index at once
(`badSetAt` is the union over the index), so `expLK_det_core` applies; `StochDomAt.of_subset_union` with
`τ' = τ/3`.  No grid lift: both inputs are uniform in `u` (DECISIONS §64 (4)). -/
theorem expLK_prec {d : ℕ} (sz : Sizes d) (hd : 2 ≤ d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto)
    (hband : sz.Bandwidth 𝔠) (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) {E s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (ht1 : ∀ n, t n < 1) (hLKU : STLKU sz E s t) (hGd : STGdecayW sz E s t 0) :
    sz.Prec (U := STIdx2 sz s t)
      (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) := by
  have hsize := tendsto_size sz hsz
  have hD : (0 : ℝ) < 2 / 𝔠 := by positivity
  refine StochDomAt.of_subset_union hsize (hLKU 2 (by norm_num)) (hGd (2 / 𝔠) hD) ?_
  intro τ hτ
  refine ⟨τ / 3, by positivity, ?_⟩
  have hτ3 : 0 < τ / 3 := by positivity
  have hC : ∀ᶠ n in atTop, KDecay_tailC d + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) :=
    ((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop (KDecay_tailC d + 1))
  filter_upwards [hlam, hband, hC, hsz.eventually (eventually_ge_atTop 1)] with n hl hb hCn hN1 ω hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  -- the two good events, at every index
  have hg1 : ∀ p : STIdx2 sz s t n,
      ‖sz.Lloop n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - sz.STKloop n (E n) (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * sz.Bctl n (p.1 : ℝ) ^ 2 := by
    intro p
    by_contra hc
    exact hn1 ⟨p, lt_of_not_ge hc⟩
  have hg2 : ∀ p : STIdx2 sz s t n,
      ‖sz.Lloop n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - sz.STKloop n (E n) (p.1 : ℝ) p.2.1 p.2.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
          (((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) * sz.Bctl n (p.1 : ℝ) ^ (1 / 5 : ℝ) *
            sz.STWB n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
              ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-(2 / 𝔠))) := by
    intro p
    by_contra hc
    exact hn2 ⟨p, lt_of_not_ge hc⟩
  -- `W^{-D} ≤ N^{-2}` from the bandwidth
  have hWD : ((sz.W n : ℕ) : ℝ) ^ (-(2 / 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-2 : ℝ) := by
    have h1 : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hNpos _
    have h2 := Real.rpow_le_rpow_of_nonpos h1 hb (by linarith : -(2 / 𝔠) ≤ 0)
    refine h2.trans (le_of_eq ?_)
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    field_simp
  -- the target index
  obtain ⟨p, hp⟩ := hω
  obtain ⟨⟨u, hu⟩, σ, a⟩ := p
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 n)
  have key := expLK_det_core sz hd n (E := E n) (τ' := τ / 3) (D := 2 / 𝔠) hl hu0 hu1 hN hWD
    (sz.seqHflow n u ω) σ a (fun x => hg1 (⟨u, hu⟩, σ, ![x, a 1])) (fun y => by
      have h := hg2 (⟨u, hu⟩, σ, ![a 0, y])
      simp only [Real.rpow_zero, one_mul] at h
      exact h)
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := Real.rpow_nonneg hNpos.le _
  have hR0 : 0 ≤ (1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ) :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (Real.rpow_nonneg (STBctl_pos sz n hu1).le _)
  have hXXX : ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
      (KDecay_tailC d + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
    calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
          ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := mul_le_mul_of_nonneg_left hCn (mul_nonneg hX0 hX0)
      _ = ((sz.size n : ℕ) : ℝ) ^ τ := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
  have hle : ‖sz.STELKLK n (E n) u σ a ω‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ)) :=
    key.trans (mul_le_mul_of_nonneg_right hXXX hR0)
  exact absurd hp (not_lt.2 hle)


/-! ## 4. `≺ → 𝔼`: the first moment outside the failure event -/

/-- **The first moment outside a small event** (RBM2D `MLExpDrift_first_moment` `MLExpDrift.lean:717`): `‖f‖ ≤ c` off `S`
and `‖f‖ ≤ B` everywhere give `𝔼‖f‖ ≤ c + B P(S)`, with no measurability of `f` or `S` (only the integrability of the
right side is used, `integral_mono_of_nonneg`). -/
private theorem expLK_first_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℂ} {S : Set Ω} {c B : ℝ} (hc : 0 ≤ c) (hB : ∀ ω, ‖f ω‖ ≤ B)
    (hin : ∀ ω, ω ∉ S → ‖f ω‖ ≤ c) : ∫ ω, ‖f ω‖ ∂P ≤ c + B * (P S).toReal := by
  classical
  set S' : Set Ω := toMeasurable P S with hS'
  have hmeas : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS : P S' = P S := measure_toMeasurable S
  have hpt : ∀ ω, ‖f ω‖ ≤ c + B * S'.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω]
      have := hB ω
      linarith
    · rw [Set.indicator_of_notMem hω]
      have := hin ω (fun h => hω (subset_toMeasurable P S h))
      linarith
  have hint : Integrable (fun ω => c + B * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const c).add (Integrable.const_mul ((integrable_const (1 : ℝ)).indicator hmeas) B)
  calc ∫ ω, ‖f ω‖ ∂P ≤ ∫ ω, (c + B * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = c + B * (P S).toReal := by
        rw [integral_add (integrable_const c) (Integrable.const_mul
          ((integrable_const (1 : ℝ)).indicator hmeas) B), integral_const,
          integral_const_mul, integral_indicator_const _ hmeas]
        simp [measureReal_def, hPS]


/-- **`≺ → 𝔼`** for `ℰ^{LK×LK}` (`(eq:Exp(L-K)1)` after the expectation): from the `≺` of `‖ℰ‖` against `R = (1-u)⁻¹ B^{11/5}`
(`expLK_prec`) and a polynomial envelope at the right end `t`: `𝔼|ℰ| ≤ N^{τ/2} R + Env P(S_n)`, `Env ≤ N^{Kenv}`,
`P(S_n) ≤ N^{-(|Kenv|+3)}`, and the floor `R ≥ N^{-11/5}`; the deterministic `Prec` through `st6_prec_det_iff`. -/
theorem expLK_expect {d : ℕ} (sz : Sizes d) {E s t : ℕ → ℝ} {Kenv : ℝ} (hsz : sz.SizeTendsto)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (henv : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
        ((etaT (E n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hprec : sz.Prec (U := STIdx2 sz s t)
        (fun n p ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))) :
    STExpLKLKHiConcl sz E s t := by
  unfold STExpLKLKHiConcl
  refine (st6_prec_det_iff sz hsz (fun n (p : STIdx2 sz s t n) => ‖sz.STExpELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hDp : 0 < |Kenv| + 3 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hprec (τ / 2) hτ2 (|Kenv| + 3) hDp, henv, hC, hsz.eventually (eventually_ge_atTop 1)]
    with n hP hEnv hN2 hN1
  rintro ⟨⟨u, hu⟩, σ, a⟩
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hu0 : 0 ≤ u := (hs0 n).trans hu.1
  have hut : u ≤ t n := hu.2
  have hu1 : u < 1 := hut.trans_lt (ht1 n)
  have h1t : 0 < 1 - t n := by linarith [ht1 n]
  have h1u : 0 < 1 - u := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set R : ℝ := (1 - u)⁻¹ * sz.Bctl n u ^ (11 / 5 : ℝ) with hR
  have hBpos : 0 < sz.Bctl n u := STBctl_pos sz n hu1
  -- the floor `R ≥ N^{-11/5}`
  have hone : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ h1u).2 (by linarith)
  have hfloor : N ^ (-(11 / 5 : ℝ)) ≤ R := by
    have hBN : N⁻¹ ≤ sz.Bctl n u := expLK_Bctl_ge sz n hu0 hu1
    have h1 : N ^ (-(11 / 5 : ℝ)) = (N⁻¹) ^ (11 / 5 : ℝ) := by
      rw [Real.rpow_neg hNpos.le, Real.inv_rpow hNpos.le]
    rw [h1]
    calc (N⁻¹) ^ (11 / 5 : ℝ) ≤ sz.Bctl n u ^ (11 / 5 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hNpos.le) hBN (by norm_num)
      _ = 1 * sz.Bctl n u ^ (11 / 5 : ℝ) := (one_mul _).symm
      _ ≤ R := mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hBpos.le _)
  have hR0 : 0 ≤ R := (Real.rpow_nonneg hNpos.le _).trans hfloor
  -- the failure event
  set S : Set sz.SeqΩ := badSetAt sz.size
    (fun n (p : STIdx2 sz s t n) ω => ‖sz.STELKLK n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
    (fun n (p : STIdx2 sz s t n) _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) (τ / 2) n with hS
  have hPS : (sz.seqP S).toReal ≤ N ^ (-(|Kenv| + 3)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hP
  -- envelope at `u ≤ t`
  have hEnvu : ∀ ω, ‖sz.STELKLK n (E n) u σ a ω‖ ≤ N ^ Kenv := by
    intro ω
    refine (expLK_env sz n (hE n) hu0 hu1 σ a ω).trans (le_trans ?_ hEnv)
    have hm : 0 < (mE (E n)).im := mE_im_pos (hE n)
    have hηt : 0 < etaT (E n) (t n) := etaT_pos (hE n) (ht1 n)
    have hηle : etaT (E n) (t n) ≤ etaT (E n) u := by
      unfold etaT
      exact mul_le_mul_of_nonneg_right (by linarith) hm.le
    have hηinv : (etaT (E n) u)⁻¹ ≤ (etaT (E n) (t n))⁻¹ := inv_anti₀ hηt hηle
    have hinv : (1 - u)⁻¹ ≤ (1 - t n)⁻¹ := inv_anti₀ h1t (by linarith)
    have hηu0 : 0 ≤ (etaT (E n) u)⁻¹ := inv_nonneg.2 (etaT_pos (hE n) hu1).le
    have hsq : (etaT (E n) u)⁻¹ ^ 2 ≤ (etaT (E n) (t n))⁻¹ ^ 2 := pow_le_pow_left₀ hηu0 hηinv 2
    have h0 : 0 ≤ (etaT (E n) u)⁻¹ ^ 2 + (1 - u)⁻¹ := by positivity
    have hle : ((etaT (E n) u)⁻¹ ^ 2 + (1 - u)⁻¹) ^ 2 ≤ ((etaT (E n) (t n))⁻¹ ^ 2 + (1 - t n)⁻¹) ^ 2 :=
      pow_le_pow_left₀ h0 (add_le_add hsq hinv) 2
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  -- off `S`
  have hin : ∀ ω, ω ∉ S → ‖sz.STELKLK n (E n) u σ a ω‖ ≤ N ^ (τ / 2) * R := by
    intro ω hω
    by_contra hc
    exact hω ⟨(⟨u, hu⟩, σ, a), lt_of_not_ge hc⟩
  have hfm := expLK_first_moment (P := sz.seqP) (f := fun ω => sz.STELKLK n (E n) u σ a ω) (S := S)
    (c := N ^ (τ / 2) * R) (B := N ^ Kenv) (mul_nonneg (Real.rpow_nonneg hNpos.le _) hR0) hEnvu hin
  -- the tail
  have htail : N ^ Kenv * (sz.seqP S).toReal ≤ R := by
    calc N ^ Kenv * (sz.seqP S).toReal ≤ N ^ Kenv * N ^ (-(|Kenv| + 3)) :=
          mul_le_mul_of_nonneg_left hPS (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (Kenv + -(|Kenv| + 3)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (-(11 / 5 : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          have := le_abs_self Kenv
          linarith
      _ ≤ R := hfloor
  have hexp : sz.STExpELKLK n (E n) u σ a = ∫ ω, sz.STELKLK n (E n) u σ a ω ∂(sz.seqP) := rfl
  have hX2 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc ‖sz.STExpELKLK n (E n) u σ a‖ ≤ ∫ ω, ‖sz.STELKLK n (E n) u σ a ω‖ ∂(sz.seqP) := by
        rw [hexp]; exact norm_integral_le_integral_norm _
    _ ≤ N ^ (τ / 2) * R + N ^ Kenv * (sz.seqP S).toReal := hfm
    _ ≤ N ^ (τ / 2) * R + R := add_le_add le_rfl htail
    _ ≤ N ^ (τ / 2) * R + N ^ (τ / 2) * R := by
        have : R ≤ N ^ (τ / 2) * R := by nlinarith
        linarith
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * R) := by
        have h3 : 0 ≤ N ^ (τ / 2) * R := mul_nonneg hX2 hR0
        linarith [mul_le_mul_of_nonneg_right hN2 h3]
    _ = N ^ τ * R := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring


/-! ## 5. The conclusion from the premises it uses, and the pin -/

/-- `(eq:Exp(L-K)1)` from the premises it uses (`STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STLKU`, `STGdecayW … 0`):
`expLK_prec`, then `expLK_expect` with `Kenv = 6` (`expLK_env_poly`).  The window `STDriftHi` and the other
premises of `STIngR6` are not used: the bound holds for every `u < 1`. -/
theorem STExpLKLKHiConcl_of_LKU {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hLKU : STLKU sz (STflowE z) s t)
    (hGd : STGdecayW sz (STflowE z) s t 0) : STExpLKLKHiConcl sz (STflowE z) s t := by
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow htT
  have hE : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hflow
  have hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n := (st6_lam_pos sz hflow.1.2.2.2.2).mono fun n h => h.le
  have hprec := expLK_prec sz (by omega) hflow.1.1 hflow.1.2.2.1 hflow.1.2.2.2.1 hlam hs0 ht1 hLKU hGd
  exact expLK_expect sz hflow.1.2.2.1 hE hs0 ht1 (expLK_env_poly sz hκ hε hflow htT) hprec

/-- **`(eq:Exp(L-K)1)`** (`6:58-62`): the merged pin `STExpLKLKHi` (`Step6Pins.lean:301`, unchanged), proved with
`𝔠_d = 1/100`.  Premises used: `STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STLKU`, `STGdecayW … 0`; unused: `s < t`, `STDriftHi`,
`STLK`, `STDecay`, `STExp2` at `s`, `STConStInd`, `STStep2Core`, `STLmaxU`. -/
theorem stExpLKLKHi_holds (d : ℕ) : STExpLKLKHi d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hHi hLK hDec hExp hcon hS2 hLmax hLKU hGd
  exact STExpLKLKHiConcl_of_LKU sz hd hκ hε hflow hs0 htT hLKU hGd

end RBM.Gauss.Sizes

/-! ## 6. Instances (nonempty, nondegenerate data of the merged Step-6 instances) -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path RBM.Loop Filter

/-- `(eq:Exp(L-K)1)` at the data of regime (i) (`szB`, `zB`, `[7/8, 15/16]`). -/
theorem inst_expLKLK_I_holds :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_expLKLK_I (stExpLKLKHi_holds 3)

/-- The same at the data of regime (ii) (`[15/16, 31/32]`). -/
theorem inst_expLKLK_II_holds :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expLKLK_II (stExpLKLKHi_holds 3)

/-- The same at the data of regime (iii) (`sz0`, `z0`, `sInst`, `tInst`). -/
theorem inst_expLKLK_III_holds :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst :=
  inst_expLKLK_III (stExpLKLKHi_holds 3)

/-- The regime (iii) skeleton with `hLK := stExpLKLKHi_holds 3`: what remains are the other gates' pins. -/
theorem inst_skeleton6III_LK :
    LWtermEXP 3 → STExpDuhamelZ 3 → STExpIntIII 3 →
      InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  fun hLW hDu hInt => inst_skeleton6III (stExpLKLKHi_holds 3) hLW hDu hInt

/-- `expLK_latticeSum` at `sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`), `u = 1/2`, `a = 0`. -/
theorem inst_expLK_latticeSum :
    ((sz0.W 0 : ℕ) : ℝ) ^ 3 * ∑ y : Zd 3 (sz0.L 0),
        sz0.STWB 0 (1 / 2) (zdistInf 3 (sz0.L 0) ((0 : Zd 3 (sz0.L 0)) - y)) *
          Real.exp (-(((zdistInf 3 (sz0.L 0) ((0 : Zd 3 (sz0.L 0)) - y) : ℕ) : ℝ) /
            ellT (sz0.L 0) (sz0.lam 0) (1 / 2)) ^ (1 / 2 : ℝ)) ≤
      KDecay_tailC 3 / (1 - 1 / 2) :=
  expLK_latticeSum sz0 (by norm_num) 0 (by rw [sz0_values.2.2.2]; norm_num) (by norm_num) 0

/-- `expLK_env` at `sz0`, `n = 0`, `E = u = 1/2`, `σ = (+,-)`, `a = (0,0)`. -/
theorem inst_expLK_env :
    ∀ ω : sz0.SeqΩ,
      ‖sz0.STELKLK 0 (1 / 2) (1 / 2) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0] ω‖ ≤
        ((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.L 0 : ℕ) : ℝ) ^ 3 *
          ((etaT (1 / 2) (1 / 2))⁻¹ ^ 2 + (1 - (1 / 2 : ℝ))⁻¹) ^ 2 :=
  fun ω => expLK_env sz0 0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num)
    (by norm_num) ![true, false] ![0, 0] ω

/-- `expLK_window_le` at `sz0`, `n = 0`, `E = u = 1/2`, the model matrix `H = seqHflow` at a sample, with the
nondegenerate choices `M = Σ_x |(𝓛-𝒦)_{(x,0)}|`, `f(y) = |(𝓛-𝒦)_{(0,y)}|`. -/
theorem inst_expLK_window (ω : sz0.SeqΩ) :
    ‖sz0.STELKLKM 0 (1 / 2) (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) ![true, false] ![(0 : Zd 3 (sz0.L 0)), 0]‖ ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ 3 *
        (∑ x : Zd 3 (sz0.L 0), ‖sz0.STLKM 0 (1 / 2) (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) ![true, false] ![x, 0]‖) *
        ∑ y : Zd 3 (sz0.L 0), ‖sz0.STLKM 0 (1 / 2) (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) ![true, false] ![0, y]‖ :=
  expLK_window_le sz0 0 (1 / 2) (1 / 2) _ ![true, false] ![0, 0] _ _
    (fun x => Finset.single_le_sum (f := fun x : Zd 3 (sz0.L 0) =>
      ‖sz0.STLKM 0 (1 / 2) (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) ![true, false] ![x, 0]‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ x)) (fun _ => le_rfl)

/-- `expLK_env_poly` along `sz0`, `z0`, with `t = tInst` (`1/16 ≤ lemT z_n`). -/
theorem inst_expLK_env_poly :
    ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ 3 * ((sz0.L n : ℕ) : ℝ) ^ 3 *
        ((etaT (STflowE z0 n) (tInst n))⁻¹ ^ 2 + (1 - tInst n)⁻¹) ^ 2 ≤ ((sz0.size n : ℕ) : ℝ) ^ (6 : ℝ) :=
  expLK_env_poly sz0 (by norm_num) (by norm_num) flow_z0 (t := tInst) fun n => sixteenth_le_lemT n

/-- `expLK_prec` at `sz0`, `z0`, `sInst`, `tInst`: the Steps 4 and 5 inputs stay hypotheses. -/
theorem inst_expLK_prec (hLKU : STLKU sz0 (STflowE z0) sInst tInst)
    (hGd : STGdecayW sz0 (STflowE z0) sInst tInst 0) :
    sz0.Prec (U := STIdx2 sz0 sInst tInst)
      (fun n p ω => ‖sz0.STELKLK n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz0.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ)) :=
  expLK_prec sz0 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 6) sz0_tendsto sz0_bandwidth
    ((st6_lam_pos sz0 sz0_WO).mono fun n h => h.le) (fun n => by simp [sInst]) (fun n => by norm_num [tInst])
    hLKU hGd

/-- `expLK_expect` at `sz0`, `z0`, `sInst`, `tInst` with `Kenv = 6`: the `≺` input stays a hypothesis. -/
theorem inst_expLK_expect
    (hprec : sz0.Prec (U := STIdx2 sz0 sInst tInst)
      (fun n p ω => ‖sz0.STELKLK n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz0.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))) :
    STExpLKLKHiConcl sz0 (STflowE z0) sInst tInst :=
  expLK_expect sz0 sz0_tendsto (st6_flowE_lt_two sz0 (by norm_num) flow_z0) (fun n => by simp [sInst])
    (fun n => by norm_num [tInst]) inst_expLK_env_poly hprec

/-- `STExpLKLKHiConcl_of_LKU` at `sz0`, `z0`, `sInst`, `tInst`: the Steps 4 and 5 inputs stay hypotheses. -/
theorem inst_expLKLK_of_LKU (hLKU : STLKU sz0 (STflowE z0) sInst tInst)
    (hGd : STGdecayW sz0 (STflowE z0) sInst tInst 0) :
    STExpLKLKHiConcl sz0 (STflowE z0) sInst tInst :=
  STExpLKLKHiConcl_of_LKU sz0 (by norm_num) (by norm_num) (by norm_num) flow_z0 (fun n => by simp [sInst])
    (fun n => sixteenth_le_lemT n) hLKU hGd

end RBM.Gauss.Step6Inst
