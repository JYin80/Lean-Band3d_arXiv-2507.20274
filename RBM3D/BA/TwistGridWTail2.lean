/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGridWTail

/-!
# BA stage TL, row TL2a4 (T2439), part 2: the `Ũ`-weighted martingale tail (clause (iv) of 4 (b))

Second file of `docs/tickets/T2439.md` (the first is `RBM3D/BA/TwistGridWTail.lean`).  Twin of `Path/DifREP3.lean` §6-§10 (`:1088-2390`) at one kernel slot:
the vocabulary of the coarse level (`kap`, `zeta`, `yinc`, `aSeq`, `qv`, `vSeq`, `eSeq`), the first-chaos tail by the peeling `difRep2_peel`, the pathwise inclusion
from the coarse grid to the pin's sums, the numerical budgets, the tail at one size index, the target `baTwistGridWTail_holds` (every `d`) and its compiled instance
at `d = 3`, `sz0`, `zSeq`, `flow_sz0`.  The coarse grid is `v_p = s + p (t − s)/P`, `P = ⌈N^{C'}⌉`, `C' = D + 14`; the fine grid exponent is `CK = 3D + 40`.

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

/-- `‖Σ_{x,y} P_x P'_y T_{xy}‖ ≤ (Σ|P|)(Σ|P'|) M` for `|T_{xy}| ≤ M` (copy of the private `difRep3_norm_double_sum_le`, `Path/DifREP3.lean:316`). -/
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

/-! ## 2. The coarse time grid `v_p = s + p (t − s)/P` and the numerical constants (copies of `Path/DifREP3.lean:786-834`) -/

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

/-! ## 3. The pathwise inclusion: from the coarse level to the pin's sums -/

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
`Σ_{j<k} y^{p,a'}_j` are at most `x_Y = ρ √δ`, for every label `a'`, then the pin's sum `X_k = (Σ_{j<k} Ũ_{u_j,u_k} ξ_{j+1})_a` is at most
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

end Pathwise

end RBM.BA
