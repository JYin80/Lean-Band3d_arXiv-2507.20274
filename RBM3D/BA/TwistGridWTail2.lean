/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGridWTail

/-!
# The `Ũ`-weighted martingale tail, part 2

Clause (iv) of the grid martingale statement `BATwistGridMartAt` (statement `BATwistGridWTail`, `BA/TwistGrid2`); the first part is `BA/TwistGridWTail`.  The analogue of `Path/DifREP3` at one kernel slot:
the vocabulary of the coarse level (`TwistGridWTail2_kap`, `TwistGridWTail2_zeta`, `TwistGridWTail2_yinc`, `TwistGridWTail2_aSeq`, `TwistGridWTail2_qv`, `TwistGridWTail2_vSeq`, `TwistGridWTail2_eSeq`), the first-chaos tail by the peeling `difRep2_peel`, the pathwise inclusion
from the coarse grid to the sums of `BATwistGridWTail`, the numerical budgets, the tail at one size index, and `baTwistGridWTail_holds` (every `d`).
The coarse grid is `v_p = s + p (t − s)/P`, `P = ⌈N^{C'}⌉`, `C' = D + 14`; the fine grid exponent is `CK = 3D + 40`.

Every statement is for every `d` (no `3 ≤ d`).  Every helper is `private` or carries the stem `TwistGridWTail2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Ind

/-! ## 1. The coarse-level vocabulary and its elementary facts

For a coarse time `vp` and a label `a`, `kap j = Ũ_{u_j,vp}(a, ·)` if `u_j ≤ vp` and `0` otherwise (a deterministic switch); `zeta_j` is `stepZCN` of the family
at the kernel `kap j`, `yinc_j = Σ_b kap j b ξ_{j+1}(b) − zeta_j`; `aSeq_j = 1[u_j ≤ vp] Δ ‖twEEUM_{u_j,vp}(H_j)(a,a)‖`; `qv_j = Re Σ κ κ̄ twEEM_{u_{j+1}}(H_j)`,
`vSeq_j = max (0, Δ qv_j)`; `eSeq_j = Δ S² · N · 24 η⁻⁷ Δ` (the shift of `twEEM` from `u_j` to `u_{j+1}`, `|z' − z| ≤ Δ`). -/

section Vocab

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)

def TwistGridWTail2_kap (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) : Zd d (sz.L n) → ℂ :=
  fun b => if gridTime s t K n j ≤ vp then twU sz lam0 E n σ (gridTime s t K n j) vp a b else 0

def TwistGridWTail2_zeta (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℂ :=
  stepZCN (sz.withLam 0) s t K n j (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j)
    (fun _ a' => TwistGridWTail2_kap sz lam0 E s t K n σ vp a j a') 0 ω

def TwistGridWTail2_yinc (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℂ :=
  TwistGridWTail_yinc sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_kap sz lam0 E s t K n σ vp a) j ω

def TwistGridWTail2_aSeq (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  if gridTime s t K n j ≤ vp then
    gridStep s t K n * ‖twEEUM sz lam0 E n (gridTime s t K n j) vp ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂‖
  else 0

def TwistGridWTail2_qv (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  (∑ b, ∑ b', TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b * (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b') *
    twEEM sz lam0 E n (gridTime s t K n (j + 1)) ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ b b' c₁ c₂).re

def TwistGridWTail2_vSeq (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) : ℝ :=
  max 0 (gridStep s t K n * TwistGridWTail2_qv sz lam0 E s t K n σ c₁ c₂ vp a j ω)

/-- The deterministic shift slack `e_j = Δ · S² · N · 24 η⁻⁷ Δ` (`|twEEM_{u_{j+1}} − twEEM_{u_j}| ≤ 24 N η⁻⁷ |z_{j+1} − z_j|`, `|z_{j+1} − z_j| ≤ Δ`). -/
def TwistGridWTail2_eSeq (S η : ℝ) (j : ℕ) : ℝ :=
  gridStep s t K n * (S ^ 2 * (((sz.size n : ℕ) : ℝ) * (24 * η⁻¹ ^ 7 * gridStep s t K n)))

end Vocab

section Basic

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)

/-- `Σ_b |kap_j(b)| ≤ 16 N` when `(1 − vp)⁻¹ ≤ 16 N` (`Σ_b |Ũ_{u_j,vp}(a,b)| ≤ (1 − u_j)/(1 − vp) ≤ (1 − vp)⁻¹`). -/
theorem TwistGridWTail2_kap_sum_le {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    {vp R : ℝ} (hvp1 : vp < 1) (hR : (1 - vp)⁻¹ ≤ R) (hR0 : 0 ≤ R) (a : Zd d (sz.L n)) (j : ℕ) :
    ∑ b, ‖TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b‖ ≤ R := by
  unfold TwistGridWTail2_kap
  by_cases h : gridTime s t K n j ≤ vp
  · simp only [h, ↓reduceIte]
    refine (TwistGridWTail_sum_norm_twU_le sz lam0 E n hr σ (TwistGridWTail_gridTime_nonneg hs0 hst j) h hvp1 a).trans ?_
    have h1w : 0 < 1 - vp := by linarith
    have : (1 - gridTime s t K n j) / (1 - vp) ≤ (1 - vp)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.2 h1w.le) (by linarith [TwistGridWTail_gridTime_nonneg (K := K) hs0 hst j])
    linarith
  · simp only [h, ↓reduceIte, norm_zero, Finset.sum_const_zero]
    exact hR0

theorem TwistGridWTail2_aSeq_nonneg (hst : s n ≤ t n) (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) :
    0 ≤ TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω := by
  unfold TwistGridWTail2_aSeq
  split_ifs
  · exact mul_nonneg (ST_gridStep_nonneg s t K n hst) (norm_nonneg _)
  · exact le_rfl

theorem TwistGridWTail2_vSeq_nonneg (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) (ω : PathΩ (sz.withLam 0)) :
    0 ≤ TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω := le_max_left _ _

theorem TwistGridWTail2_eSeq_nonneg (hst : s n ≤ t n) {S η : ℝ} (hη0 : 0 < η) (j : ℕ) :
    0 ≤ TwistGridWTail2_eSeq sz s t K n S η j := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold TwistGridWTail2_eSeq
  positivity

/-- `‖Σ_{x,y} P_x P'_y T_{xy}‖ ≤ (Σ|P|)(Σ|P'|) M` for `|T_{xy}| ≤ M` (copy of the private `difRep3_norm_double_sum_le`, `Path/DifREP3`). -/
theorem TwistGridWTail2_norm_double_sum_le {X : Type*} [Fintype X] (P P' : X → ℂ) (T : X → X → ℂ) {R R' M : ℝ} (hM : 0 ≤ M)
    (hP : ∑ x, ‖P x‖ ≤ R) (hP' : ∑ x, ‖P' x‖ ≤ R') (hT : ∀ x y, ‖T x y‖ ≤ M) :
    ‖∑ x, ∑ y, P x * P' y * T x y‖ ≤ R * R' * M := by
  calc ‖∑ x, ∑ y, P x * P' y * T x y‖ ≤ ∑ x, ∑ y, ‖P x‖ * ‖P' y‖ * M := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_))
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hT x y) (by positivity)
    _ = (∑ x, ‖P x‖) * (∑ y, ‖P' y‖) * M := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
    _ ≤ R * R' * M := by
        have h1 : 0 ≤ ∑ x, ‖P x‖ := Finset.sum_nonneg fun x _ => norm_nonneg _
        have h2 : 0 ≤ ∑ y, ‖P' y‖ := Finset.sum_nonneg fun x _ => norm_nonneg _
        have h3 : 0 ≤ R := h1.trans hP
        gcongr

/-- `twEEUM` is the quadratic form `Σ κ_b conj κ_{b'} twEEM(b,b')` with `κ = Ũ^{(σ)}_{v,w}(a,·)` (the conjugation identity `Ũ^{(σ̄)} = conj Ũ^{(σ)}`). -/
theorem TwistGridWTail2_twEEUM_eq {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (v : ℝ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a c₁ c₂ : Zd d (sz.L n)) :
    twEEUM sz lam0 E n v w H σ a c₁ c₂ = ∑ b, ∑ b', twU sz lam0 E n σ v w a b * (starRingEnd ℂ) (twU sz lam0 E n σ v w a b') *
      twEEM sz lam0 E n v H σ b b' c₁ c₂ := by
  unfold twEEUM
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [TwistGridWTail_twU_conj sz lam0 E n hr σ v hw0 hw1 a b']

/-- **Crude bound of the weighted quadratic variation**: `|twEEUM_{u,w}(H)| ≤ R² · N (2 η⁻³)²` for `0 ≤ u ≤ w < 1`, `(1 − w)⁻¹ ≤ R`, `η ≤ η_u`. -/
theorem TwistGridWTail2_norm_twEEUM_le {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u w R : ℝ} (hu : 0 ≤ u) (huw : u ≤ w)
    (hw1 : w < 1) (hR : (1 - w)⁻¹ ≤ R) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (a c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEUM sz lam0 E n u w H σ a c₁ c₂‖ ≤ (R * R) * (((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3))) := by
  have h1w : 0 < 1 - w := by linarith
  have hrow : ∀ σ' : Fin 2 → Bool, ∑ b, ‖twU sz lam0 E n σ' u w a b‖ ≤ R := fun σ' => by
    refine (TwistGridWTail_sum_norm_twU_le sz lam0 E n hr σ' hu huw hw1 a).trans ?_
    have : (1 - u) / (1 - w) ≤ (1 - w)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.2 h1w.le) (by linarith)
    linarith
  unfold twEEUM
  exact TwistGridWTail2_norm_double_sum_le _ _ _ (by positivity) (hrow σ) (hrow fun i => !σ i)
    fun b b' => TwistGridWTail_twEEM_norm_le lam0 E n u hH hη0 hη σ b b' c₁ c₂

open scoped Matrix.Norms.Operator in
/-- **The proxy transfer in the endpoint**: `|twEEUM_{u,w₂} − twEEUM_{u,w₁}| ≤ 2 R³ (w₂ − w₁) · N (2 η⁻³)²` for `0 ≤ u ≤ w₁ ≤ w₂ < 1`,
`(1 − w_i)⁻¹ ≤ R` (kernel difference `TwistGridWTail_norm_twU_sub_le`, double sums). -/
theorem TwistGridWTail2_norm_twEEUM_sub_le {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {u w₁ w₂ R : ℝ} (hu : 0 ≤ u)
    (huw : u ≤ w₁) (hw12 : w₁ ≤ w₂) (hw2 : w₂ < 1) (hR₁ : (1 - w₁)⁻¹ ≤ R) (hR₂ : (1 - w₂)⁻¹ ≤ R)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ etaOf (BAmF sz lam0 E n) u) (a c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEUM sz lam0 E n u w₂ H σ a c₁ c₂ - twEEUM sz lam0 E n u w₁ H σ a c₁ c₂‖ ≤
      2 * (((w₂ - w₁) * (R * R)) * R) * (((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3))) := by
  have hw1 : w₁ < 1 := hw12.trans_lt hw2
  have hw10 : 0 ≤ w₁ := hu.trans huw
  have hw20 : 0 ≤ w₂ := hw10.trans hw12
  have h1w1 : 0 < 1 - w₁ := by linarith
  have h1w2 : 0 < 1 - w₂ := by linarith
  have hR0 : 0 ≤ R := (inv_nonneg.2 h1w1.le).trans hR₁
  set M : ℝ := ((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3)) with hM
  have hM0 : 0 ≤ M := by positivity
  set θ : ℝ := (w₂ - w₁) * (R * R) with hθ
  have hθ0 : 0 ≤ θ := mul_nonneg (by linarith) (by positivity)
  have hrow : ∀ (σ' : Fin 2 → Bool) {w : ℝ}, u ≤ w → w < 1 → (1 - w)⁻¹ ≤ R → ∑ b, ‖twU sz lam0 E n σ' u w a b‖ ≤ R := by
    intro σ' w huw' hw1' hRw
    have h1w : 0 < 1 - w := by linarith
    refine (TwistGridWTail_sum_norm_twU_le sz lam0 E n hr σ' hu huw' hw1' a).trans ?_
    have : (1 - u) / (1 - w) ≤ (1 - w)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.2 h1w.le) (by linarith)
    linarith
  have hdiff : ∀ σ' : Fin 2 → Bool, ∑ b, ‖twU sz lam0 E n σ' u w₂ a b - twU sz lam0 E n σ' u w₁ a b‖ ≤ θ := by
    intro σ'
    have h := TwistGridWTail_norm_twU_sub_le sz lam0 E n hr σ' hu huw hw12 hw2
    have hrow' : ∑ b, ‖twU sz lam0 E n σ' u w₂ a b - twU sz lam0 E n σ' u w₁ a b‖ ≤
        ‖twU sz lam0 E n σ' u w₂ - twU sz lam0 E n σ' u w₁‖ := by
      simpa only [Matrix.sub_apply] using sum_norm_row_le (twU sz lam0 E n σ' u w₂ - twU sz lam0 E n σ' u w₁) a
    refine hrow'.trans (h.trans ?_)
    have hA : (1 - w₂)⁻¹ ≤ R := hR₂
    have hB : (1 - u) / (1 - w₁) ≤ R := by
      have : (1 - u) / (1 - w₁) ≤ (1 - w₁)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_nonneg.2 h1w1.le) (by linarith)
      linarith
    have e1 : (w₂ - w₁) * (1 - w₂)⁻¹ ≤ (w₂ - w₁) * R := mul_le_mul_of_nonneg_left hA (by linarith)
    have e2 := mul_le_mul e1 hB (div_nonneg (by linarith) h1w1.le) (mul_nonneg (by linarith) hR0)
    refine e2.trans (le_of_eq ?_)
    rw [hθ]; ring
  have hT : ∀ b b', ‖twEEM sz lam0 E n u H σ b b' c₁ c₂‖ ≤ M := fun b b' =>
    TwistGridWTail_twEEM_norm_le lam0 E n u hH hη0 hη σ b b' c₁ c₂
  set P₂ : Zd d (sz.L n) → ℂ := fun b => twU sz lam0 E n σ u w₂ a b with hP₂
  set P₁ : Zd d (sz.L n) → ℂ := fun b => twU sz lam0 E n σ u w₁ a b with hP₁
  set Q₂ : Zd d (sz.L n) → ℂ := fun b => twU sz lam0 E n (fun i => !σ i) u w₂ a b with hQ₂
  set Q₁ : Zd d (sz.L n) → ℂ := fun b => twU sz lam0 E n (fun i => !σ i) u w₁ a b with hQ₁
  have hsplit : twEEUM sz lam0 E n u w₂ H σ a c₁ c₂ - twEEUM sz lam0 E n u w₁ H σ a c₁ c₂ =
      ∑ b, ∑ b', (P₂ b - P₁ b) * Q₂ b' * twEEM sz lam0 E n u H σ b b' c₁ c₂ +
        ∑ b, ∑ b', P₁ b * (Q₂ b' - Q₁ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂ := by
    unfold twEEUM
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [hP₂, hP₁, hQ₂, hQ₁]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := TwistGridWTail2_norm_double_sum_le (fun b => P₂ b - P₁ b) Q₂ (fun b b' => twEEM sz lam0 E n u H σ b b' c₁ c₂) hM0
    (hdiff σ) (hrow (fun i => !σ i) (huw.trans hw12) hw2 hR₂) hT
  have h2 := TwistGridWTail2_norm_double_sum_le P₁ (fun b => Q₂ b - Q₁ b) (fun b b' => twEEM sz lam0 E n u H σ b b' c₁ c₂) hM0
    (hrow σ huw hw1 hR₁) (hdiff fun i => !σ i) hT
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [hθ]; ring

/-- `‖z_{u'} − z_u‖ ≤ (u' − u) ‖m‖` for `u ≤ u'` (`z_u = E + (1 − u) m`). -/
theorem TwistGridWTail2_norm_zt_sub_le (m : ℂ) (Eu : ℝ) {u u' : ℝ} (huu : u ≤ u') : ‖ztOf m Eu u' - ztOf m Eu u‖ ≤ (u' - u) * ‖m‖ := by
  have e : ztOf m Eu u' - ztOf m Eu u = -(((u' - u : ℝ) : ℂ) * m) := by unfold ztOf; push_cast; ring
  rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

/-- **The proxy is dominated by `a_j + e_j`** (`c = 1`): the switched weights give `Σ κ κ̄ twEEM_{u_j} = twEEUM_{u_j,vp}` (conjugation identity) and the shift
`u_j → u_{j+1}` costs `S² · N · 24 η⁻⁷ Δ` (`TwistGridWTail_twEEM_sub_le`, `|z_{j+1} − z_j| ≤ Δ‖m‖ ≤ Δ`). -/
theorem TwistGridWTail2_vSeq_le {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hm : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) {η : ℝ} (hη0 : 0 < η) (hη : ∀ u : ℝ, u ≤ t n → η ≤ etaOf (BAmF sz lam0 E n) u)
    (c₁ c₂ : Zd d (sz.L n)) {j : ℕ} (hj : j + 1 ≤ K n) {vp : ℝ} (hvp0 : 0 ≤ vp) (hvp1 : vp < 1) {S : ℝ} (hS0 : 0 ≤ S)
    (a : Zd d (sz.L n)) (hS : ∀ j, ∑ b, ‖TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b‖ ≤ S) (ω : PathΩ (sz.withLam 0)) :
    TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω ≤
      TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω + TwistGridWTail2_eSeq sz s t K n S η j := by
  have hK : K n ≠ 0 := by omega
  have hu1 : gridTime s t K n (j + 1) ≤ t n := TwistGridWTail_gridTime_le hst hK hj
  have huj : gridTime s t K n j ≤ t n := TwistGridWTail_gridTime_le hst hK (by omega)
  have hsucc := TwistGridWTail_gridTime_succ s t K n j
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hH : ((baStep2Mat sz lam0 E).Hpath s t K n j ω).IsHermitian :=
    TwistGridWTail_Hm_herm sz lam0 n (pathH_isHermitian (sz.withLam 0) s t K n j ω)
  have ha0 := TwistGridWTail2_aSeq_nonneg sz lam0 E s t K n σ hst c₁ c₂ vp a j ω
  have he0 := TwistGridWTail2_eSeq_nonneg sz s t K n hst (S := S) hη0 j
  unfold TwistGridWTail2_vSeq
  refine max_le (add_nonneg ha0 he0) ?_
  by_cases h : gridTime s t K n j ≤ vp
  · have hkap : ∀ b, TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b = twU sz lam0 E n σ (gridTime s t K n j) vp a b := by
      intro b; simp only [TwistGridWTail2_kap, h, ↓reduceIte]
    set H := (baStep2Mat sz lam0 E).Hpath s t K n j ω with hHdef
    have hE0 := TwistGridWTail2_twEEUM_eq sz lam0 E n σ hr (gridTime s t K n j) hvp0 hvp1 H a c₁ c₂
    have hshift : ∀ b b', ‖twEEM sz lam0 E n (gridTime s t K n (j + 1)) H σ b b' c₁ c₂ - twEEM sz lam0 E n (gridTime s t K n j) H σ b b' c₁ c₂‖ ≤
        ((sz.size n : ℕ) : ℝ) * (24 * (η⁻¹) ^ 7 * gridStep s t K n) := by
      intro b b'
      refine (TwistGridWTail_twEEM_sub_le lam0 E n (gridTime s t K n j) (gridTime s t K n (j + 1)) hH hη0 (hη _ huj) (hη _ hu1) σ b b' c₁ c₂).trans ?_
      have hz := TwistGridWTail2_norm_zt_sub_le (BAmF sz lam0 E n) (E n) (u := gridTime s t K n j) (u' := gridTime s t K n (j + 1)) (by rw [hsucc]; linarith)
      have hz' : ‖ztOf (BAmF sz lam0 E n) (E n) (gridTime s t K n (j + 1)) - ztOf (BAmF sz lam0 E n) (E n) (gridTime s t K n j)‖ ≤ gridStep s t K n := by
        refine hz.trans ?_
        rw [hsucc]
        nlinarith [norm_nonneg (BAmF sz lam0 E n)]
      have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
      have h7 : 0 ≤ 24 * (η⁻¹) ^ 7 := by positivity
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' h7) hN
    set X₁ := ∑ b, ∑ b', TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b * (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b') *
      twEEM sz lam0 E n (gridTime s t K n (j + 1)) H σ b b' c₁ c₂ with hX₁
    have hX : X₁ = twEEUM sz lam0 E n (gridTime s t K n j) vp H σ a c₁ c₂ +
        ∑ b, ∑ b', TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b * (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b') *
          (twEEM sz lam0 E n (gridTime s t K n (j + 1)) H σ b b' c₁ c₂ - twEEM sz lam0 E n (gridTime s t K n j) H σ b b' c₁ c₂) := by
      rw [hE0, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [hkap]
      ring
    have hdiff : ‖∑ b, ∑ b', TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b * (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b') *
          (twEEM sz lam0 E n (gridTime s t K n (j + 1)) H σ b b' c₁ c₂ - twEEM sz lam0 E n (gridTime s t K n j) H σ b b' c₁ c₂)‖ ≤
        S * S * (((sz.size n : ℕ) : ℝ) * (24 * (η⁻¹) ^ 7 * gridStep s t K n)) := by
      refine TwistGridWTail2_norm_double_sum_le _ (fun b' => (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b')) _
        (by positivity) (hS j) (by simpa only [Complex.norm_conj] using hS j) hshift
    have hqv : TwistGridWTail2_qv sz lam0 E s t K n σ c₁ c₂ vp a j ω ≤
        ‖twEEUM sz lam0 E n (gridTime s t K n j) vp H σ a c₁ c₂‖ + S * S * (((sz.size n : ℕ) : ℝ) * (24 * (η⁻¹) ^ 7 * gridStep s t K n)) := by
      unfold TwistGridWTail2_qv
      change X₁.re ≤ _
      rw [hX]
      exact (Complex.re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add le_rfl hdiff))
    unfold TwistGridWTail2_aSeq TwistGridWTail2_eSeq
    simp only [h, ↓reduceIte]
    calc gridStep s t K n * TwistGridWTail2_qv sz lam0 E s t K n σ c₁ c₂ vp a j ω
        ≤ gridStep s t K n * (‖twEEUM sz lam0 E n (gridTime s t K n j) vp H σ a c₁ c₂‖ +
          S * S * (((sz.size n : ℕ) : ℝ) * (24 * (η⁻¹) ^ 7 * gridStep s t K n))) := mul_le_mul_of_nonneg_left hqv hΔ
      _ = _ := by ring
  · have hk : ∀ b, TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b = 0 := fun b => by simp only [TwistGridWTail2_kap, h, ↓reduceIte]
    have hq : TwistGridWTail2_qv sz lam0 E s t K n σ c₁ c₂ vp a j ω = 0 := by
      unfold TwistGridWTail2_qv
      simp only [hk, zero_mul, Finset.sum_const_zero, Complex.zero_re]
    rw [hq, mul_zero]
    exact add_nonneg ha0 he0

/-! ### Measurability of the proxies in the matrix -/

theorem TwistGridWTail2_chg_measurable (u : ℝ) (σ' : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twChg (twGM sz lam0 E n u H) σ' x y) := by
  cases σ'
  · simp only [twChg, twGM, Bool.false_eq_true, ite_false]
    exact Complex.continuous_conj.measurable.comp (walk_measurable_Gres_apply _ true y x)
  · simp only [twChg, twGM, ite_true]
    exact walk_measurable_Gres_apply _ true x y

theorem TwistGridWTail2_twEEM_measurable (u : ℝ) (b b' c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twEEM sz lam0 E n u H σ b b' c₁ c₂) := by
  have hder : ∀ (b'' : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)), Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      twDerM sz lam0 E n u H σ b'' c₁ c₂ x y) := by
    intro b'' x y
    simp only [TwistGridWTail_twDerM_eq, TwistGridWTail_der]
    have hc := fun σ'' x' y' => TwistGridWTail2_chg_measurable sz lam0 E n u σ'' x' y'
    refine (measurable_const.mul (Measurable.add (Finset.measurable_sum _ fun z _ => Finset.measurable_sum _ fun w _ => ?_)
      (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun z _ => ?_)))
    · exact ((hc _ _ _).mul (hc _ _ _)).mul (hc _ _ _)
    · exact ((hc _ _ _).mul (hc _ _ _)).mul (hc _ _ _)
  unfold twEEM
  exact Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
    measurable_const.mul ((hder b x y).mul (Complex.continuous_conj.measurable.comp (hder b' x y)))

theorem TwistGridWTail2_twEEUM_measurable (v w : ℝ) (a c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twEEUM sz lam0 E n v w H σ a c₁ c₂) := by
  unfold twEEUM
  exact Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ =>
    measurable_const.mul (TwistGridWTail2_twEEM_measurable sz lam0 E n σ v b b' c₁ c₂)

theorem TwistGridWTail2_Hpath_measurable (j : ℕ) :
    Measurable[filt (sz.withLam 0) j] (fun ω : PathΩ (sz.withLam 0) => (baStep2Mat sz lam0 E).Hpath s t K n j ω) := by
  exact (TwistGridWTail_Hm_measurable sz lam0 n).comp (pathH_measurable_filt (sz.withLam 0) s t K n j)

theorem TwistGridWTail2_aSeq_sm (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) :
    StronglyMeasurable[filt (sz.withLam 0) j] (TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j) := by
  by_cases h : gridTime s t K n j ≤ vp
  · have e : TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j = fun ω => gridStep s t K n *
        ‖twEEUM sz lam0 E n (gridTime s t K n j) vp ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂‖ :=
      funext fun ω => by simp only [TwistGridWTail2_aSeq, h, ↓reduceIte]
    rw [e]
    exact (((TwistGridWTail2_twEEUM_measurable sz lam0 E n σ _ vp a c₁ c₂).comp
      (TwistGridWTail2_Hpath_measurable sz lam0 E s t K n j)).stronglyMeasurable.norm).const_mul _
  · have e : TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j = fun _ => 0 :=
      funext fun ω => by simp only [TwistGridWTail2_aSeq, h, ↓reduceIte]
    rw [e]
    exact stronglyMeasurable_const

theorem TwistGridWTail2_vSeq_sm (c₁ c₂ : Zd d (sz.L n)) (vp : ℝ) (a : Zd d (sz.L n)) (j : ℕ) :
    StronglyMeasurable[filt (sz.withLam 0) j] (TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j) := by
  have hf : Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (∑ b, ∑ b', TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b * (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b') *
        twEEM sz lam0 E n (gridTime s t K n (j + 1)) H σ b b' c₁ c₂).re) :=
    Complex.measurable_re.comp (Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun b' _ =>
      measurable_const.mul (TwistGridWTail2_twEEM_measurable sz lam0 E n σ _ b b' c₁ c₂))
  have hqv : Measurable[filt (sz.withLam 0) j] (TwistGridWTail2_qv sz lam0 E s t K n σ c₁ c₂ vp a j) :=
    hf.comp (TwistGridWTail2_Hpath_measurable sz lam0 E s t K n j)
  exact (measurable_const.max (hqv.const_mul _)).stronglyMeasurable

/-! ### The conditional mgf of the first-chaos increment at the coarse level -/

open scoped Matrix.Norms.L2Operator in
/-- **The mgf facts of `Re ζ_j`, `Im ζ_j` with the proxy `v_j`** (`TwistGridWTail_condMGF_generic` at the weights `kap j`; `exp` is monotone, `v_j = max (0, Δ qv_j)`). -/
theorem TwistGridWTail2_zeta_mgf (hs0 : 0 ≤ s n) (hst : s n ≤ t n) {η : ℝ} (hη0 : 0 < η) (hη : ∀ u : ℝ, u ≤ t n → η ≤ etaOf (BAmF sz lam0 E n) u)
    (c₁ c₂ : Zd d (sz.L n)) {j : ℕ} (hj : j + 1 ≤ K n) (vp : ℝ) {S : ℝ} (hS0 : 0 ≤ S) (a : Zd d (sz.L n))
    (hS : ∀ j, ∑ b, ‖TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b‖ ≤ S) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * (TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω).re)) (pathP (sz.withLam 0)) ∧
    Integrable (fun ω => Real.exp (r * (TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω).im)) (pathP (sz.withLam 0)) ∧
    (pathP (sz.withLam 0))[fun ω => Real.exp (r * (TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω).re) | filt (sz.withLam 0) j] ≤ᵐ[pathP (sz.withLam 0)]
      (fun ω => Real.exp (r ^ 2 * TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω / 2)) ∧
    (pathP (sz.withLam 0))[fun ω => Real.exp (r * (TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω).im) | filt (sz.withLam 0) j] ≤ᵐ[pathP (sz.withLam 0)]
      (fun ω => Real.exp (r ^ 2 * TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω / 2)) := by
  set szz : Sizes d := sz.withLam 0 with hszz
  have hK : K n ≠ 0 := by omega
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hu1 : gridTime s t K n (j + 1) ≤ t n := TwistGridWTail_gridTime_le hst hK hj
  have hηj := hη _ hu1
  have hΦ : ∀ b, HermTestFun szz n (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j b) := fun b =>
    TwistGridWTail_hermTestFun sz lam0 E n _ σ c₁ c₂ b hη0 hηj
  have hC₂ : ∀ b (M y : Matrix (Idx d (szz.L n) (szz.W n)) (Idx d (szz.L n) (szz.W n)) ℂ), M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j b)) M y y‖ ≤ (6 * η⁻¹ ^ 4) * ‖y‖ ^ 2 :=
    fun b M y hM hy => TwistGridWTail_Phi_second sz lam0 E n _ σ c₁ c₂ b hη0 hηj hM hy
  set U : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun _ a' => TwistGridWTail2_kap sz lam0 E s t K n σ vp a j a' with hU
  set qv : PathΩ szz → ℝ := TwistGridWTail2_qv sz lam0 E s t K n σ c₁ c₂ vp a j with hqvdef
  have hvar := fun ω : PathΩ szz => TwistGridWTail_linTrVar_le_QV sz lam0 E n _ σ c₁ c₂ hη0 hηj (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j)
    (pathH_isHermitian szz s t K n j ω)
  have hbound : ∀ ω, qv ω ≤ S * S * (((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3))) := by
    intro ω
    have hH := TwistGridWTail_Hm_herm sz lam0 n (pathH_isHermitian szz s t K n j ω)
    have h := TwistGridWTail2_norm_double_sum_le (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j)
      (fun b' => (starRingEnd ℂ) (TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b'))
      (fun b b' => twEEM sz lam0 E n (gridTime s t K n (j + 1)) (TwistGridWTail_Hm sz lam0 n (pathH szz s t K n j ω)) σ b b' c₁ c₂)
      (M := ((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3))) (by positivity) (hS j) (by simpa only [Complex.norm_conj] using hS j)
      fun b b' => TwistGridWTail_twEEM_norm_le lam0 E n _ hH hη0 hηj σ b b' c₁ c₂
    exact (Complex.re_le_norm _).trans h
  have hmgf := TwistGridWTail_condMGF_generic (sz := szz) s t K n j hΦ hC₂ hΔ U 0
    (c0 := gridStep s t K n * (S * S * (((sz.size n : ℕ) : ℝ) * (2 * (η⁻¹) ^ 3 * (2 * (η⁻¹) ^ 3))))) (by positivity) qv
    (fun ω => (hvar ω).1) (fun ω => (hvar ω).2) (fun ω => mul_le_mul_of_nonneg_left (hbound ω) hΔ) r
  have hre : ∀ ω, (TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω).re = stepZCN_re szz s t K n j (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j) U 0 ω := by
    intro ω
    simp [TwistGridWTail2_zeta, stepZCN, hU]
    rfl
  have him : ∀ ω, (TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω).im = stepZCN_im szz s t K n j (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j) U 0 ω := by
    intro ω
    simp [TwistGridWTail2_zeta, stepZCN, hU]
    rfl
  simp only [hre, him]
  have hle : ∀ ω : PathΩ szz, r ^ 2 * (gridStep s t K n * qv ω) / 2 ≤ r ^ 2 * TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω / 2 := by
    intro ω
    unfold TwistGridWTail2_vSeq
    have := le_max_right 0 (gridStep s t K n * qv ω)
    have h0 : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith
  obtain ⟨h1, h2, h3, h4⟩ := hmgf
  exact ⟨h1, h2, h3.trans (Eventually.of_forall fun ω => Real.exp_le_exp.2 (hle ω)),
    h4.trans (Eventually.of_forall fun ω => Real.exp_le_exp.2 (hle ω))⟩

open scoped Matrix.Norms.L2Operator in
/-- `ζ_j` is `filt (j+1)`-measurable (`TwistGridWTail_measurable_stepZCN`). -/
theorem TwistGridWTail2_zeta_measurable (hs0 : 0 ≤ s n) (hst : s n ≤ t n) {η : ℝ} (hη0 : 0 < η)
    (hη : ∀ u : ℝ, u ≤ t n → η ≤ etaOf (BAmF sz lam0 E n) u) (c₁ c₂ : Zd d (sz.L n)) {j : ℕ} (hj : j + 1 ≤ K n) (vp : ℝ) (a : Zd d (sz.L n)) :
    Measurable[filt (sz.withLam 0) (j + 1)] (fun ω => TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω) := by
  set szz : Sizes d := sz.withLam 0 with hszz
  have hK : K n ≠ 0 := by omega
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hu1 : gridTime s t K n (j + 1) ≤ t n := TwistGridWTail_gridTime_le hst hK hj
  have hηj := hη _ hu1
  have hΦ : ∀ b, HermTestFun szz n (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j b) := fun b =>
    TwistGridWTail_hermTestFun sz lam0 E n _ σ c₁ c₂ b hη0 hηj
  have hC₂ : ∀ b (M y : Matrix (Idx d (szz.L n) (szz.W n)) (Idx d (szz.L n) (szz.W n)) ℂ), M.IsHermitian → y.IsHermitian →
      ‖fderiv ℝ (fderiv ℝ (TwistGridWTail_fam sz lam0 E s t K n σ c₁ c₂ j b)) M y y‖ ≤ (6 * η⁻¹ ^ 4) * ‖y‖ ^ 2 :=
    fun b M y hM hy => TwistGridWTail_Phi_second sz lam0 E n _ σ c₁ c₂ b hη0 hηj hM hy
  set U : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun _ a' => TwistGridWTail2_kap sz lam0 E s t K n σ vp a j a' with hU
  have hIntRe := integrable_stepZCN_re_of_hermTestFun szz s t K n j hΦ hC₂ hΔ U 0
  have hIntIm := integrable_stepZCN_im_of_hermTestFun szz s t K n j hΦ hC₂ hΔ U 0
  obtain ⟨-, hAm, -, -⟩ := stepDecompCN szz s t K n j hΦ hC₂ hΔ U 0 hIntRe hIntIm
  exact TwistGridWTail_measurable_stepZCN s t K n j _ U 0 hAm

/-- **The `Z` part of the tail**, through the peeling lemma `difRep2_peel` (`ζ_j`, `a_j`, `v_j`, `e_j`, `c = 1`). -/
theorem TwistGridWTail2_Z_tail {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hm : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) {η : ℝ} (hη0 : 0 < η) (hη : ∀ u : ℝ, u ≤ t n → η ≤ etaOf (BAmF sz lam0 E n) u)
    (c₁ c₂ : Zd d (sz.L n)) {vp : ℝ} (hvp0 : 0 ≤ vp) (hvp1 : vp < 1) {S : ℝ} (hS0 : 0 ≤ S) (a : Zd d (sz.L n))
    (hS : ∀ j, ∑ b, ‖TwistGridWTail2_kap sz lam0 E s t K n σ vp a j b‖ ≤ S) (Lmax : ℕ) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hesum : ∑ j ∈ Finset.range (K n), TwistGridWTail2_eSeq sz s t K n S η j ≤ δ)
    (haL : ∀ ω, ∑ j ∈ Finset.range (K n), TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω ≤ 2 ^ Lmax * δ) :
    (pathP (sz.withLam 0)).real {ω | ∃ k, k ≤ K n ∧
        ρ * (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω + δ) ^ (1 / 2 : ℝ) <
          ‖∑ j ∈ Finset.range k, TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω‖} ≤
      ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) := by
  exact difRep2_peel (pathP (sz.withLam 0)) (filt (sz.withLam 0)) (fun j ω => TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a j ω)
    (fun j => TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j) (fun j => TwistGridWTail2_vSeq sz lam0 E s t K n σ c₁ c₂ vp a j)
    (fun j => TwistGridWTail2_eSeq sz s t K n S η j) (K n) Lmax 1 δ ρ one_pos hδ hρ
    (fun j hj => (Complex.measurable_re.comp (TwistGridWTail2_zeta_measurable sz lam0 E s t K n σ hs0 hst hη0 hη c₁ c₂ hj vp a)).stronglyMeasurable)
    (fun j hj => (Complex.measurable_im.comp (TwistGridWTail2_zeta_measurable sz lam0 E s t K n σ hs0 hst hη0 hη c₁ c₂ hj vp a)).stronglyMeasurable)
    (fun j _ => TwistGridWTail2_aSeq_sm sz lam0 E s t K n σ c₁ c₂ vp a j) (fun j _ => TwistGridWTail2_vSeq_sm sz lam0 E s t K n σ c₁ c₂ vp a j)
    (fun j _ ω => TwistGridWTail2_aSeq_nonneg sz lam0 E s t K n σ hst c₁ c₂ vp a j ω)
    (fun j _ ω => TwistGridWTail2_vSeq_nonneg sz lam0 E s t K n σ c₁ c₂ vp a j ω)
    (fun j _ => TwistGridWTail2_eSeq_nonneg sz s t K n hst hη0 j)
    (fun j hj ω => by rw [one_mul]; exact TwistGridWTail2_vSeq_le sz lam0 E s t K n σ hr hm hs0 hst hη0 hη c₁ c₂ hj hvp0 hvp1 hS0 a hS ω)
    hesum haL
    (fun j hj r => (TwistGridWTail2_zeta_mgf sz lam0 E s t K n σ hs0 hst hη0 hη c₁ c₂ hj vp hS0 a hS r).1)
    (fun j hj r => (TwistGridWTail2_zeta_mgf sz lam0 E s t K n σ hs0 hst hη0 hη c₁ c₂ hj vp hS0 a hS r).2.1)
    (fun j hj r => (TwistGridWTail2_zeta_mgf sz lam0 E s t K n σ hs0 hst hη0 hη c₁ c₂ hj vp hS0 a hS r).2.2.1)
    (fun j hj r => (TwistGridWTail2_zeta_mgf sz lam0 E s t K n σ hs0 hst hη0 hη c₁ c₂ hj vp hS0 a hS r).2.2.2)

end Basic

/-! ## 2. The coarse time grid `v_p = s + p (t − s)/P` and the numerical constants (copies of `Path/DifREP3`) -/

section Coarse

def TwistGridWTail2_vc (s t : ℝ) (P p : ℕ) : ℝ := s + (p : ℝ) * ((t - s) / P)

theorem TwistGridWTail2_vc_ge {s t : ℝ} (hst : s ≤ t) (P p : ℕ) : s ≤ TwistGridWTail2_vc s t P p := by
  unfold TwistGridWTail2_vc
  have : 0 ≤ (p : ℝ) * ((t - s) / P) := mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (Nat.cast_nonneg _))
  linarith

theorem TwistGridWTail2_vc_le {s t : ℝ} (hst : s ≤ t) {P : ℕ} (hP : 1 ≤ P) {p : ℕ} (hp : p ≤ P) : TwistGridWTail2_vc s t P p ≤ t := by
  unfold TwistGridWTail2_vc
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hp' : (p : ℝ) ≤ P := by exact_mod_cast hp
  have : (p : ℝ) * ((t - s) / P) ≤ (P : ℝ) * ((t - s) / P) := mul_le_mul_of_nonneg_right hp' (div_nonneg (by linarith) hP0.le)
  have h2 : (P : ℝ) * ((t - s) / P) = t - s := by field_simp
  linarith

/-- **The coarse index of a fine index**: for `k ≤ K`, `p = ⌈k P/K⌉` satisfies `p ≤ P`, `u_k ≤ v_p` and `v_p − u_k ≤ (t − s)/P`. -/
theorem TwistGridWTail2_coarse (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n) (hK : K n ≠ 0) {P : ℕ} (hP : 1 ≤ P) {k : ℕ} (hk : k ≤ K n) :
    ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ≤ P ∧ gridTime s t K n k ≤ TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ∧
      TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ - gridTime s t K n k ≤ (t n - s n) / P := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hK0 : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  set x : ℝ := ((k : ℝ) * P) / (K n : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxP : x ≤ P := by
    rw [hx, div_le_iff₀ hK0]
    have : (k : ℝ) ≤ K n := by exact_mod_cast hk
    nlinarith
  have hc : 0 ≤ (t n - s n) / P := div_nonneg (by linarith) hP0.le
  have hxc : x * ((t n - s n) / P) = (k : ℝ) * ((t n - s n) / K n) := by rw [hx]; field_simp
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  refine ⟨Nat.ceil_le.2 hxP, ?_, ?_⟩
  · unfold TwistGridWTail2_vc gridTime gridStep
    have := mul_le_mul_of_nonneg_right h1 hc
    linarith
  · unfold TwistGridWTail2_vc gridTime gridStep
    have := mul_le_mul_of_nonneg_right h2.le hc
    nlinarith

/-- `M_ee = N (2 (16 N)³)²`, the crude bound of `twEEM` at `η⁻¹ = 16 N` (`TwistGridWTail_twEEM_norm_le`). -/
def TwistGridWTail2_Mee (N : ℝ) : ℝ := N * (2 * (16 * N) ^ 3 * (2 * (16 * N) ^ 3))

/-- `V_Q = (16 N)² M_ee`, the crude bound of `twEEUM` (`TwistGridWTail2_norm_twEEUM_le`). -/
def TwistGridWTail2_VQ (N : ℝ) : ℝ := ((16 * N) * (16 * N)) * TwistGridWTail2_Mee N

/-- The constant of the proxy transfer: `|twEEUM_{u,w₂} − twEEUM_{u,w₁}| ≤ c₃ (w₂ − w₁)`, `c₃ = 2 (16 N)³ M_ee`. -/
def TwistGridWTail2_c3 (N : ℝ) : ℝ := 2 * ((16 * N) * (16 * N) * (16 * N)) * TwistGridWTail2_Mee N

/-- `P_Y = 768 (S · 6 η⁻⁴)² N⁸` at `S = 16 N`, `η⁻¹ = 16 N`: the second-moment constant of the weighted `Y` increments. -/
def TwistGridWTail2_PY (N : ℝ) : ℝ := 768 * ((16 * N) * (6 * (16 * N) ^ 4)) ^ 2 * N ^ 8

end Coarse

/-! ## 3. The pathwise inclusion: from the coarse level to the sums of `BATwistGridWTail` -/

section Pathwise

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)

theorem TwistGridWTail2_inv_eta {N : ℝ} (hN : 0 < N) : (1 / (16 * N))⁻¹ = 16 * N := by
  rw [one_div, inv_inv]

/-- The threshold increment is at most `Δ V_Q` (`η = 1/(16N)`, `(1 − vp)⁻¹ ≤ 16 N`). -/
theorem TwistGridWTail2_aSeq_le {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u) (c₁ c₂ : Zd d (sz.L n)) {j : ℕ} (hj : j ≤ K n)
    (hK : K n ≠ 0) {vp : ℝ} (hvp1 : vp < 1) (hvp16 : (1 - vp)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ)) (a : Zd d (sz.L n)) (ω : PathΩ (sz.withLam 0)) :
    TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω ≤ gridStep s t K n * TwistGridWTail2_VQ ((sz.size n : ℕ) : ℝ) := by
  have hΔ := ST_gridStep_nonneg s t K n hst
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hVQ0 : 0 ≤ TwistGridWTail2_VQ ((sz.size n : ℕ) : ℝ) := by unfold TwistGridWTail2_VQ TwistGridWTail2_Mee; positivity
  unfold TwistGridWTail2_aSeq
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ hΔ
    have hH : ((baStep2Mat sz lam0 E).Hpath s t K n j ω).IsHermitian :=
      TwistGridWTail_Hm_herm sz lam0 n (pathH_isHermitian (sz.withLam 0) s t K n j ω)
    have hu := TwistGridWTail_gridTime_le hst hK hj
    have h1 := TwistGridWTail2_norm_twEEUM_le sz lam0 E n σ hr (TwistGridWTail_gridTime_nonneg hs0 hst j) h hvp1 hvp16 hH (by positivity)
      (hη _ hu) a c₁ c₂
    rw [TwistGridWTail2_inv_eta hN0] at h1
    exact h1.trans (le_of_eq (by unfold TwistGridWTail2_VQ TwistGridWTail2_Mee; ring))
  · exact mul_nonneg hΔ hVQ0

open scoped Matrix.Norms.Operator in
/-- **The pathwise inclusion**: at the coarse level `v_p`, `p = ⌈k P/K⌉`, if the first-chaos sums `Σ_{j<k} ζ^{p,a'}_j` obey the peeled bound and the second-order sums
`Σ_{j<k} y^{p,a'}_j` are at most `x_Y = ρ √δ`, for every label `a'`, then the sum `X_k = (Σ_{j<k} Ũ_{u_j,u_k} ξ_{j+1})_a` is at most
`ρ (A_k + N^{-D})^{1/2} + 2 x_Y`: the exact transfer `X_k = (Ũ_{v_p,u_k} W_k)_a` (`BAuKer_comp`), the kernel transfer `‖Ũ_{v_p,u_k} − 1‖ ≤ (v_p − u_k)(1 − u_k)⁻¹`
and the proxy transfer `TwistGridWTail2_norm_twEEUM_sub_le`. -/
theorem TwistGridWTail2_pathwise {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (ht1 : t n < 1) (hK : K n ≠ 0) (c₁ c₂ a : Zd d (sz.L n))
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u)
    (hR16 : ∀ u : ℝ, u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    {P : ℕ} (hP1 : 1 ≤ P) {ρ₁ : ℝ} (hPρ : 1 / (P : ℝ) ≤ ρ₁) (D : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hf2 : TwistGridWTail2_c3 ((sz.size n : ℕ) : ℝ) * ρ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hf1 : (16 * ((sz.size n : ℕ) : ℝ) * ρ₁) * (ρ * Real.sqrt (TwistGridWTail2_VQ ((sz.size n : ℕ) : ℝ) + ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) +
        ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ≤ ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2))
    (ω : PathΩ (sz.withLam 0)) {k : ℕ} (hk : k ≤ K n)
    (hZg : ∀ a' : Zd d (sz.L n), ‖∑ j ∈ Finset.range k, TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂
          (TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂
          (TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω + ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) ^ (1 / 2 : ℝ))
    (hYg : ∀ a' : Zd d (sz.L n), ‖∑ j ∈ Finset.range k, TwistGridWTail2_yinc sz lam0 E s t K n σ c₁ c₂
          (TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) :
    ‖(∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n k) *ᵥ
        (fun b => twMart sz lam0 E s t K n σ b c₁ c₂ (j + 1) ω - twMart sz lam0 E s t K n σ b c₁ c₂ j ω)) a‖ ≤
      ρ * (∑ j ∈ Finset.range k, gridStep s t K n * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) +
        2 * (ρ * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  set p : ℕ := ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ with hp
  set vp : ℝ := TwistGridWTail2_vc (s n) (t n) P p with hvp
  set uk : ℝ := gridTime s t K n k with huk
  obtain ⟨hpP, hukvp, hvpuk⟩ := TwistGridWTail2_coarse s t K n hst hK hP1 hk
  have hvp_t : vp ≤ t n := TwistGridWTail2_vc_le hst hP1 hpP
  have huk0 : 0 ≤ uk := TwistGridWTail_gridTime_nonneg hs0 hst k
  have hvp0 : 0 ≤ vp := huk0.trans hukvp
  have hvp1 : vp < 1 := hvp_t.trans_lt ht1
  have hukt : uk ≤ t n := TwistGridWTail_gridTime_le hst hK hk
  have huk1 : uk < 1 := hukt.trans_lt ht1
  have hts : t n - s n ≤ 1 := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
  have hvpuk' : vp - uk ≤ ρ₁ := hvpuk.trans ((div_le_div_of_nonneg_right hts hP0.le).trans hPρ)
  have hvp16 : (1 - vp)⁻¹ ≤ 16 * N := hR16 vp hvp_t
  have huk16 : (1 - uk)⁻¹ ≤ 16 * N := hR16 uk hukt
  have hρ₁ : 0 ≤ ρ₁ := (div_nonneg zero_le_one hP0.le).trans hPρ
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := N ^ (-D) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  set xY : ℝ := ρ * Real.sqrt δ with hxY
  -- Step 1: the exact transfer
  set ξ : ℕ → Zd d (sz.L n) → ℂ := fun j b => twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b with hξ
  have hdiffξ : ∀ j, (fun b => twMart sz lam0 E s t K n σ b c₁ c₂ (j + 1) ω - twMart sz lam0 E s t K n σ b c₁ c₂ j ω) = ξ j := by
    intro j; funext b
    simp only [twMart, Finset.sum_range_succ, add_sub_cancel_left, hξ]
  simp only [hdiffξ]
  set W : Zd d (sz.L n) → ℂ := ∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) vp *ᵥ ξ j with hWdef
  have hT : ∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) uk *ᵥ ξ j = twU sz lam0 E n σ vp uk *ᵥ W := by
    rw [hWdef, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_mulVec]
    congr 1
    exact (BAuKer_comp hr hvp0 hvp1 huk0 huk1 (σ 0) (σ 1)).symm
  rw [hT]
  -- Step 2: the label sums
  have hW : ∀ a' : Zd d (sz.L n), W a' = ∑ j ∈ Finset.range k, TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a' j ω +
      ∑ j ∈ Finset.range k, TwistGridWTail2_yinc sz lam0 E s t K n σ c₁ c₂ vp a' j ω := by
    intro a'
    rw [hWdef, Finset.sum_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.1 hj
    have hon : gridTime s t K n j ≤ vp := (TwistGridWTail_gridTime_mono hst hjk.le).trans hukvp
    have hkap : ∀ b, TwistGridWTail2_kap sz lam0 E s t K n σ vp a' j b = twU sz lam0 E n σ (gridTime s t K n j) vp a' b := by
      intro b; simp only [TwistGridWTail2_kap, hon, ↓reduceIte]
    have hzy : TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a' j ω + TwistGridWTail2_yinc sz lam0 E s t K n σ c₁ c₂ vp a' j ω =
        ∑ b, TwistGridWTail2_kap sz lam0 E s t K n σ vp a' j b * twMartInc sz lam0 E s t K n σ c₁ c₂ j ω b := by
      unfold TwistGridWTail2_yinc TwistGridWTail_yinc TwistGridWTail2_zeta
      ring
    rw [hzy]
    simp only [hkap, Matrix.mulVec, dotProduct, hξ]
  -- Step 3: the crude bound on `W`
  have hVQ0 : 0 ≤ TwistGridWTail2_VQ N := by unfold TwistGridWTail2_VQ TwistGridWTail2_Mee; positivity
  have hkΔ : (k : ℝ) * Δ ≤ 1 := ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk : (k : ℝ) ≤ K n) hΔ)).trans hKΔ
  have haSum : ∀ a' : Zd d (sz.L n), ∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a' j ω ≤ TwistGridWTail2_VQ N := by
    intro a'
    have hterm : ∀ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a' j ω ≤ Δ * TwistGridWTail2_VQ N := fun j hj =>
      TwistGridWTail2_aSeq_le sz lam0 E s t K n σ hr hs0 hst hη c₁ c₂ ((Finset.mem_range.1 hj).le.trans hk) hK hvp1 hvp16 a' ω
    calc ∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a' j ω ≤ ∑ j ∈ Finset.range k, Δ * TwistGridWTail2_VQ N :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Δ * TwistGridWTail2_VQ N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * TwistGridWTail2_VQ N := mul_le_mul_of_nonneg_right hkΔ hVQ0
      _ = TwistGridWTail2_VQ N := one_mul _
  have haSum0 : ∀ a' : Zd d (sz.L n), 0 ≤ ∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a' j ω := fun a' =>
    Finset.sum_nonneg fun j _ => TwistGridWTail2_aSeq_nonneg sz lam0 E s t K n σ hst c₁ c₂ vp a' j ω
  have hZ' : ∀ a' : Zd d (sz.L n), ‖∑ j ∈ Finset.range k, TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ vp a' j ω‖ ≤
      ρ * Real.sqrt (TwistGridWTail2_VQ N + δ) := by
    intro a'
    refine (hZg a').trans (mul_le_mul_of_nonneg_left ?_ hρ)
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by linarith [haSum a'])
  have hWa : ∀ a' : Zd d (sz.L n), ‖W a'‖ ≤ ρ * Real.sqrt (TwistGridWTail2_VQ N + δ) + xY := by
    intro a'
    rw [hW a']
    exact (norm_add_le _ _).trans (add_le_add (hZ' a') (hYg a'))
  have hWmax0 : 0 ≤ ρ * Real.sqrt (TwistGridWTail2_VQ N + δ) + xY := by positivity
  -- Step 4: the kernel transfer
  have herr : ‖(twU sz lam0 E n σ vp uk *ᵥ W) a - W a‖ ≤ ρ * Real.sqrt δ := by
    have hmv : (twU sz lam0 E n σ vp uk *ᵥ W) a - W a = ((twU sz lam0 E n σ vp uk - 1) *ᵥ W) a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
    rw [hmv]
    have hU := TwistGridWTail_norm_twU_sub_one_le sz lam0 E n hr σ vp huk0 huk1
    have hε : |uk - vp| * (1 - uk)⁻¹ ≤ 16 * N * ρ₁ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      calc (vp - uk) * (1 - uk)⁻¹ ≤ ρ₁ * (16 * N) := mul_le_mul hvpuk' huk16 (inv_nonneg.2 (by linarith)) hρ₁
        _ = 16 * N * ρ₁ := by ring
    have hrow : ∑ b, ‖(twU sz lam0 E n σ vp uk - 1) a b‖ ≤ ‖twU sz lam0 E n σ vp uk - 1‖ := sum_norm_row_le _ a
    calc ‖((twU sz lam0 E n σ vp uk - 1) *ᵥ W) a‖ = ‖∑ b, (twU sz lam0 E n σ vp uk - 1) a b * W b‖ := rfl
      _ ≤ ∑ b, ‖(twU sz lam0 E n σ vp uk - 1) a b‖ * (ρ * Real.sqrt (TwistGridWTail2_VQ N + δ) + xY) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hWa b) (norm_nonneg _)
      _ = (∑ b, ‖(twU sz lam0 E n σ vp uk - 1) a b‖) * (ρ * Real.sqrt (TwistGridWTail2_VQ N + δ) + xY) := by rw [Finset.sum_mul]
      _ ≤ (16 * N * ρ₁) * (ρ * Real.sqrt (TwistGridWTail2_VQ N + δ) + xY) :=
          mul_le_mul_of_nonneg_right (hrow.trans (hU.trans hε)) hWmax0
      _ ≤ ρ * Real.sqrt δ := hf1
  -- Step 5: the proxy transfer
  have hc3 : 0 ≤ TwistGridWTail2_c3 N := by unfold TwistGridWTail2_c3 TwistGridWTail2_Mee; positivity
  have hAk : ∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω ≤
      ∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + N ^ (-D) / 4 := by
    have hterm : ∀ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω ≤
        Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + Δ * (TwistGridWTail2_c3 N * ρ₁) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.1 hj
      have hon : gridTime s t K n j ≤ vp := (TwistGridWTail_gridTime_mono hst hjk.le).trans hukvp
      have hju : gridTime s t K n j ≤ uk := TwistGridWTail_gridTime_mono hst hjk.le
      have hjt : gridTime s t K n j ≤ t n := TwistGridWTail_gridTime_le hst hK (hjk.le.trans hk)
      have hH : ((baStep2Mat sz lam0 E).Hpath s t K n j ω).IsHermitian :=
        TwistGridWTail_Hm_herm sz lam0 n (pathH_isHermitian (sz.withLam 0) s t K n j ω)
      have hsub := TwistGridWTail2_norm_twEEUM_sub_le sz lam0 E n σ hr (TwistGridWTail_gridTime_nonneg hs0 hst j) hju hukvp hvp1 huk16 hvp16
        hH (by positivity) (hη _ hjt) a c₁ c₂
      rw [TwistGridWTail2_inv_eta hN0] at hsub
      have hsub' : ‖twEEUM sz lam0 E n (gridTime s t K n j) vp ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂ -
          twEEUM sz lam0 E n (gridTime s t K n j) uk ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂‖ ≤ TwistGridWTail2_c3 N * (vp - uk) := by
        refine hsub.trans (le_of_eq ?_)
        unfold TwistGridWTail2_c3 TwistGridWTail2_Mee
        ring
      have h1 : ‖twEEUM sz lam0 E n (gridTime s t K n j) vp ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂‖ ≤
          ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + TwistGridWTail2_c3 N * ρ₁ := by
        have h0 := norm_sub_norm_le (twEEUM sz lam0 E n (gridTime s t K n j) vp ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂)
          (twEEUM sz lam0 E n (gridTime s t K n j) uk ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂)
        have h2 : TwistGridWTail2_c3 N * (vp - uk) ≤ TwistGridWTail2_c3 N * ρ₁ := mul_le_mul_of_nonneg_left hvpuk' hc3
        have e : twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω = twEEUM sz lam0 E n (gridTime s t K n j) uk ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂ := rfl
        rw [e]
        linarith
      unfold TwistGridWTail2_aSeq
      simp only [hon, ↓reduceIte]
      calc Δ * ‖twEEUM sz lam0 E n (gridTime s t K n j) vp ((baStep2Mat sz lam0 E).Hpath s t K n j ω) σ a c₁ c₂‖
          ≤ Δ * (‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + TwistGridWTail2_c3 N * ρ₁) := mul_le_mul_of_nonneg_left h1 hΔ
        _ = _ := by ring
    calc ∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω
        ≤ ∑ j ∈ Finset.range k, (Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + Δ * (TwistGridWTail2_c3 N * ρ₁)) := Finset.sum_le_sum hterm
      _ = ∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + (k : ℝ) * (Δ * (TwistGridWTail2_c3 N * ρ₁)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + N ^ (-D) / 4 := by
          have hc3ρ : 0 ≤ TwistGridWTail2_c3 N * ρ₁ := mul_nonneg hc3 hρ₁
          have : (k : ℝ) * (Δ * (TwistGridWTail2_c3 N * ρ₁)) = ((k : ℝ) * Δ) * (TwistGridWTail2_c3 N * ρ₁) := by ring
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_right hkΔ hc3ρ, hf2]
  -- the conclusion
  set Ak : ℝ := ∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ with hAkdef
  have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
  have hT1 : (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω + δ) ^ (1 / 2 : ℝ) ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by linarith [haSum0 a]) (by linarith [hAk]) (by norm_num)
  have hT2 : Real.sqrt δ ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hδ0.le (by linarith) (by norm_num)
  have hWa' : ‖W a‖ ≤ ρ * (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω + δ) ^ (1 / 2 : ℝ) + xY := by
    rw [hW a]
    exact (norm_add_le _ _).trans (add_le_add (hZg a) (hYg a))
  calc ‖(twU sz lam0 E n σ vp uk *ᵥ W) a‖ = ‖W a + ((twU sz lam0 E n σ vp uk *ᵥ W) a - W a)‖ := by congr 1; ring
    _ ≤ ‖W a‖ + ‖(twU sz lam0 E n σ vp uk *ᵥ W) a - W a‖ := norm_add_le _ _
    _ ≤ (ρ * (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ vp a j ω + δ) ^ (1 / 2 : ℝ) + xY) + ρ * Real.sqrt δ :=
        add_le_add hWa' herr
    _ ≤ (ρ * (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) + ρ * Real.sqrt δ) + ρ * Real.sqrt δ := by
        have := mul_le_mul_of_nonneg_left hT1 hρ
        linarith
    _ = ρ * (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) + 2 * (ρ * Real.sqrt δ) := by ring

/-- The number of labels `|Z_L^d| = L^d` is at most `N` (`L^d ≤ W^d L^d = N`). -/
theorem TwistGridWTail2_card_label_le : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have hcard : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by simp [Zd, ZMod.card]
  rw [hcard]
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hL0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
    rw [this]; push_cast; ring
  push_cast
  rw [hsize]
  nlinarith

end Pathwise

/-! ## 4. The tail at one size index -/

section Core

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- **The tail at one size index**: given the numerical budgets (`hshift`, `hf2`, `hf1`, `hY`, `hZ`), `η_u ≥ 1/(16 N)`, `(1 − u)⁻¹ ≤ 16 N` for `u ≤ t`, the event of `BATwistGridWTail` at the label
`(σ, a, c₁, c₂)` is contained in the union over the coarse levels `p ≤ P` and the labels `a'` of the bad events of the `Z` part (peeling, `TwistGridWTail2_Z_tail`) and of the `Y` part
(Doob, `TwistGridWTail_Y_tail`), by `TwistGridWTail2_pathwise`. -/
theorem TwistGridWTail2_core {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hm : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u)
    (hR16 : ∀ u : ℝ, u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    {P : ℕ} (hP1 : 1 ≤ P) {ρ₁ : ℝ} (hPρ : 1 / (P : ℝ) ≤ ρ₁) (hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1)
    (hshift : (16 * ((sz.size n : ℕ) : ℝ)) ^ 2 * (((sz.size n : ℕ) : ℝ) * (24 * (16 * ((sz.size n : ℕ) : ℝ)) ^ 7)) * gridStep s t K n ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (hf2 : TwistGridWTail2_c3 ((sz.size n : ℕ) : ℝ) * ρ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hf1 : (16 * ((sz.size n : ℕ) : ℝ) * ρ₁) * (((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (TwistGridWTail2_VQ ((sz.size n : ℕ) : ℝ) +
        ((sz.size n : ℕ) : ℝ) ^ (-D) / 2) + ((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2))
    (hY : ((P : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) * (4 * (gridStep s t K n * TwistGridWTail2_PY ((sz.size n : ℕ) : ℝ)) /
        (((sz.size n : ℕ) : ℝ) ^ ε' / 4 * Real.sqrt (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 4)
    (hZ : ((P : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) * (((⌈TwistGridWTail2_VQ ((sz.size n : ℕ) : ℝ) / (((sz.size n : ℕ) : ℝ) ^ (-D) / 2)⌉₊ : ℝ) + 1) *
        (4 * Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 4) ^ 2 / (16 * (1 : ℝ))))) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) / 2)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    (pathP (sz.withLam 0)) {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖(∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n k) *ᵥ
          (fun b => twMart sz lam0 E s t K n σ b c₁ c₂ (j + 1) ω - twMart sz lam0 E s t K n σ b c₁ c₂ j ω)) a‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set szz : Sizes d := sz.withLam 0 with hszz
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hND : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  set δ : ℝ := N ^ (-D) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hNε : 1 ≤ N ^ ε' := Real.one_le_rpow hN1 hε'.le
  set ρ : ℝ := N ^ ε' / 4 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ : 0 ≤ ρ := hρ0.le
  set VQ : ℝ := TwistGridWTail2_VQ N with hVQ
  have hVQ0 : 0 ≤ VQ := by rw [hVQ]; unfold TwistGridWTail2_VQ TwistGridWTail2_Mee; positivity
  set Lmax : ℕ := ⌈VQ / δ⌉₊ with hLmax
  set xY : ℝ := ρ * Real.sqrt δ with hxY
  have hxY0 : 0 < xY := mul_pos hρ0 (Real.sqrt_pos.2 hδ0)
  set PY : ℝ := TwistGridWTail2_PY N with hPY
  have hPY0 : 0 ≤ PY := by rw [hPY]; unfold TwistGridWTail2_PY; positivity
  have hη0 : 0 < 1 / (16 * N) := by positivity
  -- the coarse levels
  have hvp0 : ∀ p : ℕ, 0 ≤ TwistGridWTail2_vc (s n) (t n) P p := fun p => hs0.trans (TwistGridWTail2_vc_ge hst P p)
  have hvpt : ∀ p : ℕ, p ≤ P → TwistGridWTail2_vc (s n) (t n) P p ≤ t n := fun p hp => TwistGridWTail2_vc_le hst hP1 hp
  have hvp1 : ∀ p : ℕ, p ≤ P → TwistGridWTail2_vc (s n) (t n) P p < 1 := fun p hp => (hvpt p hp).trans_lt ht1
  have hvp16 : ∀ p : ℕ, p ≤ P → (1 - TwistGridWTail2_vc (s n) (t n) P p)⁻¹ ≤ 16 * N := fun p hp => hR16 _ (hvpt p hp)
  have hS : ∀ p : ℕ, p ≤ P → ∀ (a' : Zd d (sz.L n)) (j : ℕ), ∑ b, ‖TwistGridWTail2_kap sz lam0 E s t K n σ (TwistGridWTail2_vc (s n) (t n) P p) a' j b‖ ≤ 16 * N :=
    fun p hp a' j => TwistGridWTail2_kap_sum_le sz lam0 E s t K n σ hr hs0 hst (hvp1 p hp) (hvp16 p hp) (by positivity) a' j
  -- the shift budget
  have hesum : ∑ j ∈ Finset.range (K n), TwistGridWTail2_eSeq sz s t K n (16 * N) (1 / (16 * N)) j ≤ δ := by
    unfold TwistGridWTail2_eSeq
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, TwistGridWTail2_inv_eta hN0]
    have hc : 0 ≤ (16 * N) ^ 2 * (N * (24 * (16 * N) ^ 7)) := by positivity
    calc (K n : ℝ) * (Δ * ((16 * N) ^ 2 * (N * (24 * (16 * N) ^ 7 * Δ)))) =
        ((K n : ℝ) * Δ) * ((16 * N) ^ 2 * (N * (24 * (16 * N) ^ 7)) * Δ) := by ring
      _ ≤ 1 * ((16 * N) ^ 2 * (N * (24 * (16 * N) ^ 7)) * Δ) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ ≤ δ := by rw [one_mul]; exact hshift
  -- the threshold sums
  have haL : ∀ p : ℕ, p ≤ P → ∀ (a' : Zd d (sz.L n)) (ω : PathΩ szz),
      ∑ j ∈ Finset.range (K n), TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_vc (s n) (t n) P p) a' j ω ≤ 2 ^ Lmax * δ := by
    intro p hp a' ω
    have hterm : ∀ j ∈ Finset.range (K n), TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_vc (s n) (t n) P p) a' j ω ≤ Δ * VQ := fun j hj =>
      TwistGridWTail2_aSeq_le sz lam0 E s t K n σ hr hs0 hst hη c₁ c₂ (Finset.mem_range.1 hj).le hK (hvp1 p hp) (hvp16 p hp) a' ω
    have hVL : VQ ≤ (Lmax : ℝ) * δ := (div_le_iff₀ hδ0).1 (Nat.le_ceil _)
    have hL2 : (Lmax : ℝ) < 2 ^ Lmax := by exact_mod_cast Nat.lt_two_pow_self
    calc ∑ j ∈ Finset.range (K n), TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_vc (s n) (t n) P p) a' j ω
        ≤ ∑ j ∈ Finset.range (K n), Δ * VQ := Finset.sum_le_sum hterm
      _ = (K n : ℝ) * Δ * VQ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1 * VQ := mul_le_mul_of_nonneg_right hKΔ hVQ0
      _ = VQ := one_mul _
      _ ≤ (Lmax : ℝ) * δ := hVL
      _ ≤ 2 ^ Lmax * δ := mul_le_mul_of_nonneg_right hL2.le hδ0.le
  -- the bad events
  set EZ : ℕ → Zd d (sz.L n) → Set (PathΩ szz) := fun p a' =>
    {ω | ∃ k, k ≤ K n ∧ ρ * (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_vc (s n) (t n) P p) a' j ω + δ) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_vc (s n) (t n) P p) a' j ω‖} with hEZ
  set EY : ℕ → Zd d (sz.L n) → Set (PathΩ szz) := fun p a' =>
    {ω | ∃ k, k ≤ K n ∧ xY ≤ ‖∑ j ∈ Finset.range k, TwistGridWTail2_yinc sz lam0 E s t K n σ c₁ c₂ (TwistGridWTail2_vc (s n) (t n) P p) a' j ω‖} with hEY
  have hZbad : ∀ p : ℕ, p ≤ P → ∀ a' : Zd d (sz.L n), (pathP szz).real (EZ p a') ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) :=
    fun p hp a' => TwistGridWTail2_Z_tail sz lam0 E s t K n σ hr hm hs0 hst hη0 hη c₁ c₂ (hvp0 p) (hvp1 p hp) (by positivity) a' (hS p hp a') Lmax hδ0 hρ
      hesum (haL p hp a')
  have hYbad : ∀ p : ℕ, p ≤ P → ∀ a' : Zd d (sz.L n), (pathP szz).real (EY p a') ≤ 4 * (Δ * PY) / xY ^ 2 := by
    intro p hp a'
    have h := TwistGridWTail_Y_tail sz lam0 E s t K n σ c₁ c₂ hs0 hst hη0 hη (TwistGridWTail2_kap sz lam0 E s t K n σ (TwistGridWTail2_vc (s n) (t n) P p) a')
      (S := 16 * N) (by positivity) (hS p hp a') (P := PY) (by rw [TwistGridWTail2_inv_eta hN0, hPY]; unfold TwistGridWTail2_PY; exact le_refl _) hxY0
    refine h.trans ?_
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have : (K n : ℝ) * (Δ ^ 2 * PY) = ((K n : ℝ) * Δ) * (Δ * PY) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hKΔ (mul_nonneg hΔ hPY0)
    linarith
  -- the pathwise inclusion
  have hincl : {ω : PathΩ szz | ∃ k, k ≤ K n ∧
      N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖(∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n k) *ᵥ
          (fun b => twMart sz lam0 E s t K n σ b c₁ c₂ (j + 1) ω - twMart sz lam0 E s t K n σ b c₁ c₂ j ω)) a‖} ⊆
      ⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Zd d (sz.L n))), (EZ p a' ∪ EY p a') := by
    intro ω hω
    obtain ⟨k, hk, hlt⟩ := hω
    by_contra hnot
    have hgood : ∀ p ∈ Finset.range (P + 1), ∀ a' : Zd d (sz.L n), ω ∉ EZ p a' ∧ ω ∉ EY p a' := by
      intro p hp a'
      by_contra hcon
      apply hnot
      simp only [Set.mem_iUnion]
      refine ⟨p, hp, a', Finset.mem_univ _, ?_⟩
      by_cases h1 : ω ∈ EZ p a'
      · exact Or.inl h1
      · exact Or.inr (by_contra fun h2 => hcon ⟨h1, h2⟩)
    obtain ⟨hpP, -, -⟩ := TwistGridWTail2_coarse s t K n hst hK hP1 hk
    have hmem : ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊ ∈ Finset.range (P + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hpP)
    have hZg : ∀ a' : Zd d (sz.L n), ‖∑ j ∈ Finset.range k, TwistGridWTail2_zeta sz lam0 E s t K n σ c₁ c₂
          (TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤
        ρ * (∑ j ∈ Finset.range k, TwistGridWTail2_aSeq sz lam0 E s t K n σ c₁ c₂
          (TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω + δ) ^ (1 / 2 : ℝ) := by
      intro a'
      by_contra hcon
      exact (hgood _ hmem a').1 ⟨k, hk, not_le.1 hcon⟩
    have hYg : ∀ a' : Zd d (sz.L n), ‖∑ j ∈ Finset.range k, TwistGridWTail2_yinc sz lam0 E s t K n σ c₁ c₂
          (TwistGridWTail2_vc (s n) (t n) P ⌈((k : ℝ) * P) / (K n : ℝ)⌉₊) a' j ω‖ ≤ ρ * Real.sqrt δ := by
      intro a'
      by_contra hcon
      exact (hgood _ hmem a').2 ⟨k, hk, (not_le.1 hcon).le⟩
    have hpw := TwistGridWTail2_pathwise sz lam0 E s t K n σ hr hs0 hst ht1 hK c₁ c₂ a hη hR16 hP1 hPρ D hρ hKΔ hf2 hf1 ω hk hZg hYg
    set Ak : ℝ := ∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ with hAkdef
    have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg hΔ (norm_nonneg _)
    have hT0 : 0 ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hsq : Real.sqrt δ ≤ (Ak + N ^ (-D)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hδ0.le (by linarith) (by norm_num)
    have hρ4 : N ^ ε' = 4 * ρ := by rw [hρdef]; ring
    rw [hρ4] at hlt
    nlinarith [mul_le_mul_of_nonneg_left hsq hρ]
  -- the measure
  have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := TwistGridWTail2_card_label_le sz n
  have hbound : (pathP szz).real (⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Zd d (sz.L n))), (EZ p a' ∪ EY p a')) ≤ N ^ (-D) := by
    calc (pathP szz).real (⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Zd d (sz.L n))), (EZ p a' ∪ EY p a'))
        ≤ ∑ p ∈ Finset.range (P + 1), (pathP szz).real (⋃ a' ∈ (Finset.univ : Finset (Zd d (sz.L n))), (EZ p a' ∪ EY p a')) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ p ∈ Finset.range (P + 1), ∑ a' : Zd d (sz.L n), (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) + 4 * (Δ * PY) / xY ^ 2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpP : p ≤ P := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
          refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
          exact (measureReal_union_le _ _).trans (add_le_add (hZbad p hpP a') (hYbad p hpP a'))
      _ = ((P : ℝ) + 1) * (Fintype.card (Zd d (sz.L n)) : ℝ) *
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) + 4 * (Δ * PY) / xY ^ 2) := by
          simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((P : ℝ) + 1) * N *
          (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) + 4 * (Δ * PY) / xY ^ 2) := by
          have h0 : (0 : ℝ) ≤ ((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ)))) + 4 * (Δ * PY) / xY ^ 2 := by positivity
          have hP0 : (0 : ℝ) ≤ (P : ℝ) + 1 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hP0) h0
      _ = ((P : ℝ) + 1) * N * (((Lmax : ℝ) + 1) * (4 * Real.exp (-ρ ^ 2 / (16 * (1 : ℝ))))) + ((P : ℝ) + 1) * N * (4 * (Δ * PY) / xY ^ 2) := by ring
      _ ≤ N ^ (-D) / 2 + N ^ (-D) / 4 := add_le_add hZ hY
      _ ≤ N ^ (-D) := by linarith
  calc (pathP szz) {ω | ∃ k, k ≤ K n ∧
        N ^ ε' * (∑ j ∈ Finset.range k, Δ * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + N ^ (-D)) ^ (1 / 2 : ℝ) <
          ‖(∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n k) *ᵥ
            (fun b => twMart sz lam0 E s t K n σ b c₁ c₂ (j + 1) ω - twMart sz lam0 E s t K n σ b c₁ c₂ j ω)) a‖}
      ≤ (pathP szz) (⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Zd d (sz.L n))), (EZ p a' ∪ EY p a')) := measure_mono hincl
    _ = ENNReal.ofReal ((pathP szz).real (⋃ p ∈ Finset.range (P + 1), ⋃ a' ∈ (Finset.univ : Finset (Zd d (sz.L n))), (EZ p a' ∪ EY p a'))) := by
        rw [ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hbound

end Core


/-! ## 5. The numerical budgets (pure real arithmetic)

`N ≥ 1`, `ND = N^D ≥ 1`, `N^{-D} = ND⁻¹`; the coarse grid is `P = ⌈N^{14} ND⌉` (`C' = D + 14`), the fine grid has `Δ N^{40} ND³ ≤ 1` (`CK = 3D + 40`).  The closed forms
`V_Q = 2³⁴ N⁹`, `c₃ = 2³⁹ N¹⁰`, `P_Y = 27648 · 2⁴⁰ N¹⁸`; all deterministic budgets hold for `N ≥ 2⁷⁰`, the `Z` budget is the eventual inequality of
`TwistGridWTail2_eventually_Z`. -/

section Budgets

theorem TwistGridWTail2_VQ_eq (N : ℝ) : TwistGridWTail2_VQ N = 2 ^ 34 * N ^ 9 := by
  unfold TwistGridWTail2_VQ TwistGridWTail2_Mee; ring

theorem TwistGridWTail2_c3_eq (N : ℝ) : TwistGridWTail2_c3 N = 2 ^ 39 * N ^ 10 := by
  unfold TwistGridWTail2_c3 TwistGridWTail2_Mee; ring

theorem TwistGridWTail2_PY_eq (N : ℝ) : TwistGridWTail2_PY N = 27648 * 2 ^ 40 * N ^ 18 := by
  unfold TwistGridWTail2_PY; ring

/-- The shift budget. -/
theorem TwistGridWTail2_budget_shift {N ND Δ : ℝ} (hN : (2 : ℝ) ^ 70 ≤ N) (hND : 1 ≤ ND) (hΔ0 : 0 ≤ Δ) (hΔ : Δ * (N ^ 40 * ND ^ 3) ≤ 1) :
    (16 * N) ^ 2 * (N * (24 * (16 * N) ^ 7)) * Δ ≤ ND⁻¹ / 2 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hND0 : 0 < ND := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : (16 * N) ^ 2 * (N * (24 * (16 * N) ^ 7)) * Δ = 1649267441664 * (N ^ 10 * Δ) := by ring
  rw [h1, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hND0]
  have h2 : 2 * 1649267441664 ≤ N ^ 30 * ND ^ 2 := by
    have : (2 : ℝ) * 1649267441664 ≤ N := le_trans (by norm_num) hN
    calc (2 : ℝ) * 1649267441664 ≤ N := this
      _ ≤ N ^ 30 := le_self_pow₀ hN1 (by norm_num)
      _ ≤ N ^ 30 * ND ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hND)
  calc 1649267441664 * (N ^ 10 * Δ) * 2 * ND = (2 * 1649267441664) * (N ^ 10 * ND * Δ) := by ring
    _ ≤ (N ^ 30 * ND ^ 2) * (N ^ 10 * ND * Δ) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = Δ * (N ^ 40 * ND ^ 3) := by ring
    _ ≤ 1 := hΔ

/-- The proxy-transfer budget (`C' = D + 14`): `c₃ (N^{14} ND)⁻¹ ≤ ND⁻¹/4`. -/
theorem TwistGridWTail2_budget_f2 {N ND : ℝ} (hN : (2 : ℝ) ^ 70 ≤ N) (hND : 1 ≤ ND) :
    TwistGridWTail2_c3 N * (N ^ 14 * ND)⁻¹ ≤ ND⁻¹ / 4 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  rw [TwistGridWTail2_c3_eq]
  have hX : 0 < N ^ 14 * ND := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ hX]
  have h1 : ND⁻¹ / 4 * (N ^ 14 * ND) = N ^ 14 / 4 := by field_simp
  rw [h1]
  have h4 : (2 : ℝ) ^ 41 ≤ N ^ 4 := by
    calc (2 : ℝ) ^ 41 ≤ 2 ^ 70 := by norm_num
      _ ≤ N := hN
      _ ≤ N ^ 4 := le_self_pow₀ hN1 (by norm_num)
  have h2 : N ^ 14 = N ^ 10 * N ^ 4 := by ring
  rw [h2]
  have hpos : 0 < N ^ 10 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 hpos.le]

/-- The arithmetic of the kernel-transfer budget: `A (√(V + δ) + √δ) ≤ √δ` from `A ≤ 1/4`, `A V ≤ δ/4`, `δ ≤ 1 ≤ V` (copy of `difRep3_f1_arith`, `Path/DifREP3`). -/
theorem TwistGridWTail2_f1_arith {A V δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hV : 1 ≤ V) (hA0 : 0 ≤ A) (hA : A ≤ 1 / 4) (hAV : A * V ≤ δ / 4) :
    A * (Real.sqrt (V + δ) + Real.sqrt δ) ≤ Real.sqrt δ := by
  have h1 : δ ≤ Real.sqrt δ := by
    rw [Real.le_sqrt hδ0.le hδ0.le]; nlinarith
  have h2 : Real.sqrt (V + δ) ≤ V + δ := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h3 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hA0, mul_le_mul_of_nonneg_right hA hδ0.le, mul_le_mul_of_nonneg_right hA h3]

/-- The kernel-transfer budget (`ρ` cancels, so the exponents are `ε'`-free). -/
theorem TwistGridWTail2_budget_f1 {N ND : ℝ} (hN : (2 : ℝ) ^ 70 ≤ N) (hND : 1 ≤ ND) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (16 * N * (N ^ 14 * ND)⁻¹) * (ρ * Real.sqrt (TwistGridWTail2_VQ N + ND⁻¹ / 2) + ρ * Real.sqrt (ND⁻¹ / 2)) ≤ ρ * Real.sqrt (ND⁻¹ / 2) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  have hX : 0 < N ^ 14 * ND := by positivity
  have hVQ1 : 1 ≤ TwistGridWTail2_VQ N := by
    rw [TwistGridWTail2_VQ_eq]
    have : (1 : ℝ) ≤ N ^ 9 := one_le_pow₀ hN1
    nlinarith [show (1 : ℝ) ≤ 2 ^ 34 by norm_num]
  have hA0 : 0 ≤ 16 * N * (N ^ 14 * ND)⁻¹ := by positivity
  have hN13 : (64 : ℝ) ≤ N ^ 13 := by
    calc (64 : ℝ) ≤ 2 ^ 70 := by norm_num
      _ ≤ N := hN
      _ ≤ N ^ 13 := le_self_pow₀ hN1 (by norm_num)
  have hA : 16 * N * (N ^ 14 * ND)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hX]
    have : N ^ 14 = N * N ^ 13 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hN13 hN0.le, show (1 : ℝ) ≤ ND from hND, mul_nonneg hN0.le (pow_nonneg hN0.le 13)]
  have h4 : (2 : ℝ) ^ 41 ≤ N ^ 4 := by
    calc (2 : ℝ) ^ 41 ≤ 2 ^ 70 := by norm_num
      _ ≤ N := hN
      _ ≤ N ^ 4 := le_self_pow₀ hN1 (by norm_num)
  have hAV : 16 * N * (N ^ 14 * ND)⁻¹ * TwistGridWTail2_VQ N ≤ ND⁻¹ / 2 / 4 := by
    rw [TwistGridWTail2_VQ_eq]
    have e : 16 * N * (N ^ 14 * ND)⁻¹ * (2 ^ 34 * N ^ 9) = (2 ^ 38 * N ^ 10) / (N ^ 14 * ND) := by field_simp; ring
    rw [e, div_le_iff₀ hX]
    have h1 : ND⁻¹ / 2 / 4 * (N ^ 14 * ND) = N ^ 14 / 8 := by field_simp; norm_num
    rw [h1]
    have h2 : N ^ 14 = N ^ 10 * N ^ 4 := by ring
    rw [h2]
    have hpos : 0 < N ^ 10 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 hpos.le]
  have hδ1 : ND⁻¹ / 2 ≤ 1 := by
    have : ND⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hND
    linarith
  have hδ0 : 0 < ND⁻¹ / 2 := by positivity
  have h := TwistGridWTail2_f1_arith hδ0 hδ1 hVQ1 hA0 hA hAV
  calc (16 * N * (N ^ 14 * ND)⁻¹) * (ρ * Real.sqrt (TwistGridWTail2_VQ N + ND⁻¹ / 2) + ρ * Real.sqrt (ND⁻¹ / 2))
      = ρ * ((16 * N * (N ^ 14 * ND)⁻¹) * (Real.sqrt (TwistGridWTail2_VQ N + ND⁻¹ / 2) + Real.sqrt (ND⁻¹ / 2))) := by ring
    _ ≤ ρ * Real.sqrt (ND⁻¹ / 2) := mul_le_mul_of_nonneg_left h hρ

/-- The `Y` budget (`CK = 3D + 40`): `(P+1) N 4 Δ P_Y/(ρ √δ)² ≤ ND⁻¹/4`, `ρ ≥ 1/4`, `P + 1 ≤ 3 N^{14} ND`. -/
theorem TwistGridWTail2_budget_Y {N ND Δ Pp ρ : ℝ} (hN : (2 : ℝ) ^ 70 ≤ N) (hND : 1 ≤ ND) (hΔ0 : 0 ≤ Δ) (hΔ : Δ * (N ^ 40 * ND ^ 3) ≤ 1)
    (hPp0 : 0 ≤ Pp) (hPp : Pp + 1 ≤ 3 * (N ^ 14 * ND)) (hρ : 1 / 4 ≤ ρ) :
    (Pp + 1) * N * (4 * (Δ * TwistGridWTail2_PY N) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2) ≤ ND⁻¹ / 4 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  have hδ0 : 0 < ND⁻¹ / 2 := by positivity
  have hsq : (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 = ρ ^ 2 * (ND⁻¹ / 2) := by rw [mul_pow, Real.sq_sqrt hδ0.le]
  have hρ2 : 1 / 16 ≤ ρ ^ 2 := by nlinarith
  have hden0 : 0 < (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 := by
    rw [hsq]; have : 0 < ρ := by linarith
    positivity
  have hden : 1 / (32 * ND) ≤ (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 := by
    rw [hsq]
    calc 1 / (32 * ND) = 1 / 16 * (ND⁻¹ / 2) := by field_simp; norm_num
      _ ≤ ρ ^ 2 * (ND⁻¹ / 2) := mul_le_mul_of_nonneg_right hρ2 hδ0.le
  have hPY : TwistGridWTail2_PY N = 27648 * 2 ^ 40 * N ^ 18 := TwistGridWTail2_PY_eq N
  have h1 : 4 * (Δ * TwistGridWTail2_PY N) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 ≤ 128 * (Δ * TwistGridWTail2_PY N) * ND := by
    rw [div_le_iff₀ hden0]
    have hpy0 : 0 ≤ Δ * TwistGridWTail2_PY N := mul_nonneg hΔ0 (by rw [hPY]; positivity)
    calc 4 * (Δ * TwistGridWTail2_PY N) = 128 * (Δ * TwistGridWTail2_PY N) * ND * (1 / (32 * ND)) := by field_simp; ring
      _ ≤ 128 * (Δ * TwistGridWTail2_PY N) * ND * (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2 := mul_le_mul_of_nonneg_left hden (by positivity)
  have hN0' : 0 ≤ N := hN0.le
  calc (Pp + 1) * N * (4 * (Δ * TwistGridWTail2_PY N) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2)
      ≤ (3 * (N ^ 14 * ND)) * N * (128 * (Δ * TwistGridWTail2_PY N) * ND) := by
        have h0 : 0 ≤ 128 * (Δ * TwistGridWTail2_PY N) * ND := by rw [hPY]; positivity
        calc (Pp + 1) * N * (4 * (Δ * TwistGridWTail2_PY N) / (ρ * Real.sqrt (ND⁻¹ / 2)) ^ 2)
            ≤ (Pp + 1) * N * (128 * (Δ * TwistGridWTail2_PY N) * ND) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (3 * (N ^ 14 * ND)) * N * (128 * (Δ * TwistGridWTail2_PY N) * ND) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPp hN0') h0
    _ = 384 * (27648 * 2 ^ 40) * (Δ * (N ^ 33 * ND ^ 2)) := by rw [hPY]; ring
    _ ≤ ND⁻¹ / 4 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), ← one_div, le_div_iff₀ hND0]
        have h2 : 1536 * (27648 * 2 ^ 40 : ℝ) ≤ N ^ 7 := by
          calc 1536 * (27648 * 2 ^ 40 : ℝ) ≤ 2 ^ 70 := by norm_num
            _ ≤ N := hN
            _ ≤ N ^ 7 := le_self_pow₀ hN1 (by norm_num)
        calc 384 * (27648 * 2 ^ 40 : ℝ) * (Δ * (N ^ 33 * ND ^ 2)) * 4 * ND = (1536 * (27648 * 2 ^ 40 : ℝ)) * (Δ * (N ^ 33 * ND ^ 3)) := by ring
          _ ≤ N ^ 7 * (Δ * (N ^ 33 * ND ^ 3)) := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = Δ * (N ^ 40 * ND ^ 3) := by ring
          _ ≤ 1 := hΔ

/-- The `Z` budget, arithmetic: from `P + 1 ≤ 3 N^{14} ND`, `L + 1 ≤ 2 V_Q ND + 2` and `24 (2³⁵ + 2) N^{24} ND³ E ≤ 1`,
`(P+1) N (L+1) 4 E ≤ ND⁻¹/2`. -/
theorem TwistGridWTail2_budget_Z {N ND Ex Pp Lc : ℝ} (hN : 1 ≤ N) (hND : 1 ≤ ND) (hE0 : 0 ≤ Ex) (hPp0 : 0 ≤ Pp) (hPp : Pp + 1 ≤ 3 * (N ^ 14 * ND))
    (hLc0 : 0 ≤ Lc) (hLc : Lc + 1 ≤ 2 * TwistGridWTail2_VQ N * ND + 2) (hZ : 24 * (2 ^ 35 + 2) * (N ^ 24 * ND ^ 3) * Ex ≤ 1) :
    (Pp + 1) * N * ((Lc + 1) * (4 * Ex)) ≤ ND⁻¹ / 2 := by
  have hN0 : 0 < N := by linarith
  have hND0 : 0 < ND := by linarith
  have hNp1 : 1 ≤ N ^ 9 * ND := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) hND
  have hL2 : Lc + 1 ≤ (2 ^ 35 + 2) * (N ^ 9 * ND) := by
    refine hLc.trans ?_
    rw [TwistGridWTail2_VQ_eq]
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ N ^ 9 * ND)]
  have hLc1 : 0 ≤ Lc + 1 := by linarith
  calc (Pp + 1) * N * ((Lc + 1) * (4 * Ex)) ≤ (3 * (N ^ 14 * ND)) * N * (((2 ^ 35 + 2) * (N ^ 9 * ND)) * (4 * Ex)) := by gcongr
    _ = 12 * (2 ^ 35 + 2) * (N ^ 24 * ND ^ 2) * Ex := by ring
    _ ≤ ND⁻¹ / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← one_div, le_div_iff₀ hND0]
        calc 12 * (2 ^ 35 + 2) * (N ^ 24 * ND ^ 2) * Ex * 2 * ND = 24 * (2 ^ 35 + 2) * (N ^ 24 * ND ^ 3) * Ex := by ring
          _ ≤ 1 := hZ

end Budgets

/-! ## 6. The asymptotics and the tail at one size index -/

section Asymptotics

/-- A polynomial against a stretched exponential: `N^s e^{-b N^c} → 0` (copy of the private `difRep3_tendsto_rpow_exp`, `Path/DifREP3`). -/
theorem TwistGridWTail2_tendsto_rpow_exp (s b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun N : ℝ => N ^ s * Real.exp (-b * N ^ c)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / c) b hb
  have h2 : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have h3 := h1.comp h2
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  simp only [Function.comp]
  rw [← Real.rpow_mul hN]
  congr 2
  field_simp

/-- **The `Z` budget holds for large `N`**: `24 (2³⁵ + 2) N^{24} (N^D)³ exp (−(N^{ε'}/4)²/16) ≤ 1` eventually (a polynomial against a stretched exponential;
the only place `ε'` enters). -/
theorem TwistGridWTail2_eventually_Z (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε') :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ 24 * (2 ^ 35 + 2) * (N ^ 24 * (N ^ D) ^ 3) * Real.exp (-(N ^ ε' / 4) ^ 2 / (16 * (1 : ℝ))) ≤ 1 := by
  set c₄ : ℝ := 24 * (2 ^ 35 + 2) with hc₄
  have hc₄0 : 0 < c₄ := by rw [hc₄]; positivity
  set q : ℝ := ((24 : ℕ) : ℝ) + D * 3 with hq
  have hlim := TwistGridWTail2_tendsto_rpow_exp q (1 / 256) (2 * ε') (by positivity) (by positivity)
  have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c₄))
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  refine ⟨hN1, ?_⟩
  have hN0 : 0 < N := by linarith
  have h1 : N ^ 24 * (N ^ D) ^ 3 = N ^ q := by
    rw [hq, Real.rpow_add hN0, Real.rpow_natCast, Real.rpow_mul hN0.le]
    norm_num
  have h2 : -(N ^ ε' / 4) ^ 2 / (16 * (1 : ℝ)) = -(1 / 256) * N ^ (2 * ε') := by
    have : (N ^ ε') ^ 2 = N ^ (2 * ε') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    field_simp
    ring
  rw [h1, h2]
  have hlt : N ^ q * Real.exp (-(1 / 256) * N ^ (2 * ε')) < 1 / c₄ := hN
  calc c₄ * N ^ q * Real.exp (-(1 / 256) * N ^ (2 * ε')) = c₄ * (N ^ q * Real.exp (-(1 / 256) * N ^ (2 * ε'))) := by ring
    _ ≤ c₄ * (1 / c₄) := mul_le_mul_of_nonneg_left hlt.le hc₄0.le
    _ = 1 := by field_simp

/-- `N^{3D + 40} = N^{40} (N^D)³` (`CK = 3D + 40`). -/
theorem TwistGridWTail2_rpow_CK {N : ℝ} (hN : 0 < N) (D : ℝ) : N ^ (3 * D + 40) = N ^ 40 * (N ^ D) ^ 3 := by
  have h1 : (3 * D + 40) = ((40 : ℕ) : ℝ) + D * 3 := by push_cast; ring
  rw [h1, Real.rpow_add hN, Real.rpow_natCast, Real.rpow_mul hN.le]
  norm_num

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- **The tail at one size index**: given `η_u ≥ 1/(16 N)` and `(1 − u)⁻¹ ≤ 16 N` for `u ≤ t`, `K ≥ N^{3D + 40}`, `N ≥ 2⁷⁰` and the `Z` budget, the event of `BATwistGridWTail` at the label
`(σ, a, c₁, c₂)` has probability at most `N^{-D}`, with the coarse grid `P = ⌈N^{14} N^D⌉` (`C' = D + 14`). -/
theorem TwistGridWTail2_tail_at {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hm : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (D ε' : ℝ) (hD : 0 < D) (hε' : 0 < ε')
    (hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz lam0 E n) u)
    (hR16 : ∀ u : ℝ, u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ))
    (hKN : ((sz.size n : ℕ) : ℝ) ^ (3 * D + 40) ≤ K n) (hbig : (2 : ℝ) ^ 70 ≤ ((sz.size n : ℕ) : ℝ))
    (hZ : 24 * (2 ^ 35 + 2) * (((sz.size n : ℕ) : ℝ) ^ 24 * (((sz.size n : ℕ) : ℝ) ^ D) ^ 3) *
        Real.exp (-(((sz.size n : ℕ) : ℝ) ^ ε' / 4) ^ 2 / (16 * (1 : ℝ))) ≤ 1)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    (pathP (sz.withLam 0)) {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n * ‖twEEUk sz lam0 E s t K n σ a c₁ c₂ j k ω‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
        ‖(∑ j ∈ Finset.range k, twU sz lam0 E n σ (gridTime s t K n j) (gridTime s t K n k) *ᵥ
          (fun b => twMart sz lam0 E s t K n σ b c₁ c₂ (j + 1) ω - twMart sz lam0 E s t K n σ b c₁ c₂ j ω)) a‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set Δ := gridStep s t K n with hΔdef
  have hΔ0 : 0 ≤ Δ := ST_gridStep_nonneg s t K n hst
  have hKΔ : (K n : ℝ) * Δ ≤ 1 := by
    rw [hΔdef, TwistGridWTail_K_mul_step s t K n hK]; linarith [hs0, ht1]
  set ND : ℝ := N ^ D with hNDdef
  have hND1 : 1 ≤ ND := Real.one_le_rpow hN1 hD.le
  have hND0 : 0 < ND := by linarith
  have hNmD : N ^ (-D) = ND⁻¹ := Real.rpow_neg hN0.le D
  have hΔN : Δ * (N ^ 40 * ND ^ 3) ≤ 1 := by
    have h1 : N ^ (3 * D + 40) = N ^ 40 * ND ^ 3 := TwistGridWTail2_rpow_CK hN0 D
    calc Δ * (N ^ 40 * ND ^ 3) = Δ * N ^ (3 * D + 40) := by rw [h1]
      _ ≤ Δ * K n := mul_le_mul_of_nonneg_left hKN hΔ0
      _ = (K n : ℝ) * Δ := mul_comm _ _
      _ ≤ 1 := hKΔ
  -- the coarse grid
  set X : ℝ := N ^ 14 * ND with hXdef
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) hND1
  have hX0 : 0 < X := by linarith
  set P : ℕ := ⌈X⌉₊ with hPdef
  have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hX0))
  have hXP : X ≤ (P : ℝ) := Nat.le_ceil X
  have hP3 : (P : ℝ) + 1 ≤ 3 * X := by
    have := Nat.ceil_lt_add_one hX0.le
    linarith
  have hPρ : 1 / (P : ℝ) ≤ X⁻¹ := by
    rw [← one_div]; exact one_div_le_one_div_of_le hX0 hXP
  have hρ0 : 0 ≤ N ^ ε' / 4 := by positivity
  have hρ14 : 1 / 4 ≤ N ^ ε' / 4 := by
    have := Real.one_le_rpow hN1 hε'.le
    linarith
  refine TwistGridWTail2_core sz lam0 E s t K n hr hm hs0 hst ht1 hK D ε' hD hε' hη hR16 hP1 hPρ hKΔ ?_ ?_ ?_ ?_ ?_ σ a c₁ c₂
  · rw [hNmD]; exact TwistGridWTail2_budget_shift hbig hND1 hΔ0 hΔN
  · rw [hNmD]; exact TwistGridWTail2_budget_f2 hbig hND1
  · rw [hNmD]; exact TwistGridWTail2_budget_f1 hbig hND1 _ hρ0
  · rw [hNmD]
    exact TwistGridWTail2_budget_Y hbig hND1 hΔ0 hΔN (Nat.cast_nonneg _) hP3 hρ14
  · rw [hNmD]
    have hVQ0 : 0 ≤ TwistGridWTail2_VQ N := by unfold TwistGridWTail2_VQ TwistGridWTail2_Mee; positivity
    have hceil : ((⌈TwistGridWTail2_VQ N / (ND⁻¹ / 2)⌉₊ : ℕ) : ℝ) + 1 ≤ 2 * TwistGridWTail2_VQ N * ND + 2 := by
      have h0 : 0 ≤ TwistGridWTail2_VQ N / (ND⁻¹ / 2) := by positivity
      have := Nat.ceil_lt_add_one h0
      have e : TwistGridWTail2_VQ N / (ND⁻¹ / 2) = 2 * TwistGridWTail2_VQ N * ND := by field_simp
      linarith
    exact TwistGridWTail2_budget_Z hN1 hND1 (Real.exp_pos _).le (Nat.cast_nonneg _) hP3 (Nat.cast_nonneg _) hceil hZ

end Asymptotics

/-! ## 7. `baTwistGridWTail_holds` -/

/-- `baTwistGridWTail_holds`: clause (iv) of `BATwistGridMartAt`, the `Ũ`-weighted martingale tail with the weighted quadratic variation `twEEUk`, uniform in `k ≤ K`
(`BATwistGridWTail`, `BA/TwistGrid2`), for every `d` (no `3 ≤ d`).  The grid exponent is `CK = 3 D + 40` (the coarse time grid `P = ⌈N^{C'}⌉`, `C' = D + 14`; both depend on `D`
only, not on `ε'`, `κ`, `ε`).  Proof outline (the analogue of `gridRepWTailQN_holds`, `Path/DifREP3`, at one kernel slot): a coarse time grid `v_0 < … < v_P` of `[s, t]` independent of `K`; for each
`(p, a')` the sums `Σ_{j<k} Ũ_{u_j,v_p} Z_j` (peeling `difRep2_peel`) and `Σ_{j<k} Ũ_{u_j,v_p} Y_j` (Doob, `j`-dependent weights) are martingales in `k`; the exact transfer
`Σ_{j<k} Ũ_{u_j,u_k} ξ_{j+1} = Ũ_{v_p,u_k} W^p_k` (`BAuKer_comp`) and the kernel and proxy transfers end the proof (`TwistGridWTail2_pathwise`, `TwistGridWTail2_core`). -/
theorem baTwistGridWTail_holds (d : ℕ) : BATwistGridWTail d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨3 * D + 40, by positivity, ?_⟩
  intro K hK0 hKN ε' hε'
  have hsize : sz.SizeTendsto := hz.1.2.2.1
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hz
  have hm : ∀ n, ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 := fun n =>
    BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) (hr n).1
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hz n)
  have hbig : ∀ᶠ n in atTop, (2 : ℝ) ^ 70 ≤ ((sz.size n : ℕ) : ℝ) := hsize.eventually (eventually_ge_atTop _)
  have hZev := hsize.eventually (TwistGridWTail2_eventually_Z D ε' hD hε')
  have hεev : ∀ᶠ n in atTop, 1 / (8 * κ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    hsize.eventually ((tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (1 / (8 * κ))))
  filter_upwards [hKN, hbig, hZev, hεev] with n hKNn hbign hZn hεn
  intro i
  obtain ⟨hN1, hZn⟩ := hZn
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη : ∀ u : ℝ, u ≤ t n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u := by
    intro u hu
    have h1 : (z n).im / 2 ≤ 1 - u := (EMn2BA_one_sub_T0 hκ sz hz n).trans (by linarith [htT n])
    have h2 : κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := (EMn2BA_mF_data sz hz n).1
    have h3 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hz.2 n).2.1
    have h0 : 0 ≤ (z n).im / 2 := by linarith [EMn2BA_zim_pos sz hz n]
    unfold etaOf
    have h4 : (z n).im / 2 * κ ≤ (1 - u) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im :=
      mul_le_mul h1 h2 hκ.le (by linarith)
    have h5 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) = (((sz.size n : ℕ) : ℝ))⁻¹ * ((sz.size n : ℕ) : ℝ) ^ ε := by
      rw [Real.rpow_add hN0, Real.rpow_neg_one]
    have h6 : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ (z n).im / 2 * κ := by
      have h7 : (((sz.size n : ℕ) : ℝ))⁻¹ * (1 / (8 * κ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
        rw [h5]; exact mul_le_mul_of_nonneg_left hεn (inv_nonneg.2 hN0.le)
      have h8 : (((sz.size n : ℕ) : ℝ))⁻¹ * (1 / (8 * κ)) ≤ (z n).im := h7.trans h3
      calc 1 / (16 * ((sz.size n : ℕ) : ℝ)) = (((sz.size n : ℕ) : ℝ))⁻¹ * (1 / (8 * κ)) / 2 * κ := by field_simp; norm_num
        _ ≤ (z n).im / 2 * κ := by gcongr
    exact h6.trans h4
  have hR16 : ∀ u : ℝ, u ≤ t n → (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) := by
    intro u hu
    have hmim : (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1 := (EMn2BA_mF_data sz hz n).2
    have h1 : (z n).im / 2 ≤ 1 - u := (EMn2BA_one_sub_T0 hκ sz hz n).trans (by linarith [htT n])
    have h1u : 0 < 1 - u := by linarith [EMn2BA_zim_pos sz hz n]
    have h2 : etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u ≤ 1 - u := by
      unfold etaOf
      nlinarith
    have h3 : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ 1 - u := (hη u hu).trans h2
    calc (1 - u)⁻¹ ≤ (1 / (16 * ((sz.size n : ℕ) : ℝ)))⁻¹ := inv_anti₀ (by positivity) h3
      _ = 16 * ((sz.size n : ℕ) : ℝ) := TwistGridWTail2_inv_eta hN0
  exact TwistGridWTail2_tail_at sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n (hr n) (hm n) (hs n) (hst n) (ht1 n) (hK0 n) D ε' hD hε' hη hR16
    hKNn hbign hZn i.1 i.2.1 i.2.2.1 i.2.2.2

end RBM.BA
