/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QDriftA
import RBM3D.Induction.QopDecay
import RBM3D.Induction.B45
import RBM3D.Induction.NQGood1
import RBM3D.Induction.Step2Core
import RBM3D.Kernel.PropT
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.B45Gen

/-!
# The decay class of the alternating drift, `d ≥ 3`

Paper: (4.35) `int_K-L+Q`, Claim 4.9 (`lem_+Q`), (4.59) `y27kasdfg`, (4.61) `A4`, (4.60) `A5`, (4.62)
`eq:alternatecase2`.  The argument is that of RBM2D (`hDcls` at `d = 2`: the drift class at `u_j` moved
to the index `j + 1` by `ellT_mono`).

The drift `dFlowQN = 𝒬_u(ℬ₁ + ℬ₂ + ℬ₃) + ℬ₄ + ℬ₅` of `Induction/QDriftA` is in the class `altClsQN`
of `goodSetN_A0clsQN` (radius `ε'`, `δD = 4 W^{-D'}`):

* `drift13_fastDecay`: the block `ℬ₁ + ℬ₂ + ℬ₃` decays at a `GoodSetN` matrix (the far-label clause of
  the drift);
* `altB4N_fastDecay`: `ℬ₄ = Θ(𝒜 - 𝒬𝒜) - (Θ𝒜 - 𝒬Θ𝒜)` decays at every radius and depth from the
  crude sup of `𝒜 = (𝓛-𝒦)_{u,σ}(H)` alone (`stQop_sub_fastDecay`, `QopDecay_ThetaN_fastDecay`);
* `altB5N_fastDecay_moll`: `ℬ₅ = -(𝒫𝒜)_{a₁} ∂_uϑ` decays at every radius and depth for the explicit
  mollifier (`QopDecay_deriv_fastDecay`);
* `dFlowQN_clsQN`: `dFlowQN ∈ altClsQN … ε' Dc uu i (4 W^{-D'})` at a matrix;
* `alt_hDclsQN`: the field `hDcls` of `GridAssemblyHypN` along the walk at the explicit mollifier.

All statements are deterministic and level-free, per matrix or per grid time; `Γ Λ Φ` occur only
inside `GoodSetN` memberships.  Every helper that is not part of the statements is `private` or
prefixed `QDriftB_`.

The generic twins over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`, `open RBM.BA`):
`drift13_fastDecayg`, `altB4Ng_fastDecay` (with the private `QDriftB_ThetaNg_fastDecay`: the decay of the
one-index kernel from `Step5KerGen_ThDecay` at the kernel coupling `gK`, crossed to the size level by the
comparison of couplings), `altB5Ng_fastDecay_moll`, `dFlowQNg_clsQNg`, `alt_hDclsQNg`.
-/

open private qdec_growth qdec_far_dist from RBM3D.Induction.QopDecay
open private Step5KerGen_cmp_pos Step5KerGen_tailT_cross from RBM3D.Chain.Step5KerGen

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ## 1. Helpers from `QDriftA` -/

/-- A pair of indices realising `R ≤ diam_∞ b` gives the `ℓ¹` window `R ≤ zdistD (b i - b j)`.  As
the private `QDriftA_window_of_diamInf`. -/
private theorem QDriftB_window_of_diamInf {d L k : ℕ} (hk : 1 ≤ k) {R : ℝ} (b : Fin k → Zd d L)
    (hb : R ≤ (STdiamInf b : ℝ)) : ∃ i j : Fin k, R ≤ (zdistD d L (b i - b j) : ℝ) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
    Finset.univ_nonempty (fun p : Fin k × Fin k => zdistInf d L (b p.1 - b p.2))
  refine ⟨p.1, p.2, hb.trans ?_⟩
  have h1 : STdiamInf b = zdistInf d L (b p.1 - b p.2) := hp
  rw [h1]
  exact_mod_cast zdistInf_le_zdistD d L _

/-- The specification of `QDriftA_W0`.  As the private `QDriftA_W0_spec`; it unfolds `QDriftA_W0`. -/
private theorem QDriftB_W0_spec (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε' : 0 < ε') :
    1 < QDriftA_W0 d m K C c C₀ ε' D' ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, QDriftA_W0 d m K C c C₀ ε' D' ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' A →
        ∀ a : Fin (m + 1) → Zd d L, (∃ i j, W ^ ε' * ellT L g t ≤ (zdistD d L (a i - a j) : ℝ)) →
          ‖STQop (d := d) ϑ t A a‖ ≤ 2 * W ^ (-D') := by
  have h : 0 < C ∧ 0 < c ∧ 0 < ε' := ⟨hC, hc, hε'⟩
  have hdef : QDriftA_W0 d m K C c C₀ ε' D' =
      Classical.choose (Qop_fastDecay d m K C c C₀ ε' D' h.1 h.2.1 h.2.2) := by
    unfold QDriftA_W0; rw [dite_eq_left_of_eq_true (eq_true h)]
  rw [hdef]
  exact Classical.choose_spec (Qop_fastDecay d m K C c C₀ ε' D' h.1 h.2.1 h.2.2)

/-! ## 2. Crude-sup bookkeeping (private) -/

/-- `‖𝒫𝒜‖_∞ ≤ ((2^d)^m + (L^d)^m) ‖𝒜‖_∞` (`B45_Psum_le` at `R = 0`, `Y = F`). -/
private theorem QDriftB_Psum_crude {d L m : ℕ} [NeZero L] (A : (Fin (m + 1) → Zd d L) → ℂ) {Y : ℝ}
    (hY : ∀ b, ‖A b‖ ≤ Y) (a₁ : Zd d L) :
    ‖STPsum (d := d) A a₁‖ ≤ (((2 : ℝ) ^ d) ^ m + ((L : ℝ) ^ d) ^ m) * Y := by
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY (fun _ => 0))
  have h := B45_Psum_le (d := d) (L := L) (m := m) A a₁ (R := 0) (Y := Y) (F := Y) le_rfl hY hY0
    (fun b _ _ => hY b)
  rw [show (2 * (0 : ℝ) + 2) = 2 by norm_num] at h
  linarith

/-- The mollifier is bounded by its constant `C`: `ℓ_t ≥ 1` and `Σ_{i ≥ 2} |a_i - a_1| ≥ 0`. -/
private theorem QDriftB_mollifier_norm_le {d L m : ℕ} [NeZero L] {g C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hϑ : STMollifierProps (d := d) g C c ϑ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Fin (m + 1) → Zd d L) : ‖ϑ t a‖ ≤ C := by
  have h := hϑ.2.1 t ht0 ht1 a
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hL1
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le zero_lt_one hℓ1
  set S : ℝ := ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have h1 : (((ellT L g t) ^ d)⁻¹) ^ m ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (pow_nonneg hℓ0.le _)) (inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1))
  have h2 : Real.exp (-c * S / ellT L g t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hℓ0.le
  have h3 : 0 ≤ (((ellT L g t) ^ d)⁻¹) ^ m := pow_nonneg (inv_nonneg.2 (pow_nonneg hℓ0.le _)) _
  calc ‖ϑ t a‖ ≤ C * (((ellT L g t) ^ d)⁻¹) ^ m * Real.exp (-c * S / ellT L g t) := h
    _ ≤ C * 1 * 1 := by gcongr
    _ = C := by ring

/-- `(2^d)^m + (L^d)^m` absorbed: for `L^d ≤ W^K`, `C (2^{dm} + 1) ≤ W` we get
`C · ((2^d)^m + (L^d)^m) ≤ W · W^{K m}` (and `W^{K m} ≥ 1`). -/
private theorem QDriftB_absorb {d L m : ℕ} {W K C : ℝ} (hC : 0 ≤ C) (hW : 1 < W) (hL1 : 1 ≤ L)
    (hLK : (L : ℝ) ^ d ≤ W ^ K) (hCW : C * (((2 : ℝ) ^ d) ^ m + 1) ≤ W) :
    1 ≤ W ^ (K * m) ∧ C * (((2 : ℝ) ^ d) ^ m + ((L : ℝ) ^ d) ^ m) ≤ W * W ^ (K * m) := by
  have hW0 : 0 < W := by linarith
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLd : ((L : ℝ) ^ d) ^ m ≤ W ^ (K * m) := by
    calc ((L : ℝ) ^ d) ^ m ≤ (W ^ K) ^ m := pow_le_pow_left₀ (by positivity) hLK m
      _ = W ^ (K * m) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hWp1 : 1 ≤ W ^ (K * m) :=
    (one_le_pow₀ (one_le_pow₀ hL1' : (1 : ℝ) ≤ (L : ℝ) ^ d)).trans hLd
  refine ⟨hWp1, ?_⟩
  have h2 : 0 ≤ ((2 : ℝ) ^ d) ^ m := by positivity
  have hmul : C * (((2 : ℝ) ^ d) ^ m) ≤ C * (((2 : ℝ) ^ d) ^ m) * W ^ (K * m) :=
    le_mul_of_one_le_right (mul_nonneg hC h2) hWp1
  calc C * (((2 : ℝ) ^ d) ^ m + ((L : ℝ) ^ d) ^ m)
      ≤ C * (((2 : ℝ) ^ d) ^ m + W ^ (K * m)) := by gcongr
    _ ≤ C * (((2 : ℝ) ^ d) ^ m + 1) * W ^ (K * m) := by nlinarith
    _ ≤ W * W ^ (K * m) := mul_le_mul_of_nonneg_right hCW (by positivity)

/-- `2 W^{-(D+1)} ≤ W^{-D}` for `W ≥ 2`. -/
private theorem QDriftB_two_mul_rpow_le {W D : ℝ} (hW : 2 ≤ W) :
    W ^ (-(D + 1)) + W ^ (-(D + 1)) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have h : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hW0, Real.rpow_neg_one]
  have h1 : 2 * W⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hW0]; linarith
  have h2 : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  rw [h]
  nlinarith

/-! ## 3. The block `ℬ₁ + ℬ₂ + ℬ₃` decays at a good matrix -/

/-- **`drift13_fastDecay`**: the `ℬ₁ + ℬ₂ + ℬ₃` block `driftTensorN` decays in the `ℓ¹`
window of radius `ε'` at a `GoodSetN` matrix: the far-label clause of `GoodSetN` (`driftTensorN_far_of_goodSet`,
the `L^∞` window `ℓ_u W^{τ'}`) and `fastDecay_of_diamInf` (`d W^{τ'} ≤ W^{ε'}`).  No threshold. -/
theorem drift13_fastDecay :
    ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {m n : ℕ} {E u Γ Λ Φ τ' ε' D' : ℝ}
      {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (σ : Fin (m + 1) → Bool),
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      H ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D' →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
        (fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b) := by
  intro d sz hd m n E u Γ Λ Φ τ' ε' D' H σ hdW hH
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  exact fastDecay_of_diamInf (by omega) hL1 hdW le_rfl
    (fun b hb => driftTensorN_far_of_goodSet sz hH σ b hb)

/-! ## 4. `ℬ₄` decays at every radius and depth from the crude sup alone -/

/-- **`altB4N_fastDecay`**: `ℬ₄ = Θ(𝒜 - 𝒬𝒜) - (Θ𝒜 - 𝒬Θ𝒜)` (`QopAlgebra_ThetaN_sub`,
`STQop`), `𝒜 = (𝓛-𝒦)_{u,σ}(H)`.  `𝒜 - 𝒬𝒜 = (𝒫𝒜)ϑ` and `Θ𝒜 - 𝒬Θ𝒜` decay at `(ε'/2, D'+K+2)` resp.
`(ε', D'+1)` by `stQop_sub_fastDecay` (crude sups `W^{C₀+Km+1}` resp. `W^{C₀+K+1}`: `B45_Psum_le`,
`B45_norm_ThetaN_le`), `Θ` maps the first to `(ε', D'+1)` (`QopDecay_ThetaN_fastDecay`), and
`2 W^{-(D'+1)} ≤ W^{-D'}`. -/
theorem altB4N_fastDecay :
    ∀ (d m : ℕ) (Λg K C c C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < C → 0 < c → 0 < ε' →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ)
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool),
        |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        STMollifierProps (d := d) (sz.lam n) C c ϑ →
        ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4N sz n E u ϑ σ H) := by
  intro d m Λg K C c C₀ ε' D' hd hΛg hC hc hε'
  have hε2 : 0 < ε' / 2 := by positivity
  obtain ⟨Wa, hWa, Ha⟩ := stQop_sub_fastDecay d m K C c C₀ (ε' / 2) (D' + K + 2) hC hc hε2
  obtain ⟨Wb, hWb, Hb⟩ := stQop_sub_fastDecay d m K C c (C₀ + K + 1) ε' (D' + 1) hC hc hε'
  obtain ⟨Wc, hWc, Hc⟩ := QopDecay_ThetaN_fastDecay d (m + 1) hd Λg K (C₀ + K * m + 1) (ε' / 2)
    (D' + K + 2) hΛg hε2
  refine ⟨max (max Wa Wb) (max Wc (max (C * (((2 : ℝ) ^ d) ^ m + 1)) (max ((m : ℝ) + 1) 2))),
    lt_of_lt_of_le hWa ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro sz n E u H ϑ σ hE hlam hlamΛ hW hLK hu0 hu1 hK hϑ hA a ha
  have hWa' : Wa ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hW
  have hWb' : Wb ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hW
  have hWc' : Wc ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWC : C * (((2 : ℝ) ^ d) ^ m + 1) ≤ ((sz.W n : ℕ) : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hWm : (m : ℝ) + 1 ≤ ((sz.W n : ℕ) : ℝ) :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : 1 < W := by linarith
  have hW0 : 0 < W := by linarith
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hL1 : 1 ≤ sz.L n := by omega
  set A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b => sz.STLKM n E u H σ b with hAdef
  set μs : Fin (m + 1) → ℂ := fun i => mSigma E (σ i) with hμsdef
  have hμ : ∀ i, ‖μs i‖ = 1 := fun i => norm_mSigma hE (σ i)
  have hAb : ∀ b, ‖A b‖ ≤ W ^ C₀ := fun b => (norm_le_pi_norm A b).trans hA
  -- the crude sup of `A - 𝒬A`
  obtain ⟨hWp1, habs⟩ := QDriftB_absorb (d := d) (m := m) (K := K) hC.le hW1 hL1 hLK hWC
  have hAQ : ‖A - STQop (d := d) ϑ u A‖ ≤ W ^ (C₀ + K * m + 1) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
    have e : (A - STQop (d := d) ϑ u A) b = STPsum (d := d) A (b 0) * ϑ u b := by simp [STQop]
    rw [e, norm_mul]
    have h1 := QDriftB_Psum_crude (d := d) A hAb (b 0)
    have h2 := QDriftB_mollifier_norm_le hC.le hc.le hϑ hu0 hu1 b
    have hC0 : 0 ≤ ‖STPsum (d := d) A (b 0)‖ := norm_nonneg _
    have hW0C : (0 : ℝ) ≤ W ^ C₀ := by positivity
    calc ‖STPsum (d := d) A (b 0)‖ * ‖ϑ u b‖
        ≤ ((((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m) * W ^ C₀) * C :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = W ^ C₀ * (C * (((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m)) := by ring
      _ ≤ W ^ C₀ * (W * W ^ (K * m)) := mul_le_mul_of_nonneg_left habs hW0C
      _ = W ^ (C₀ + K * m + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring
  -- the crude sup of `ΘA`
  have hΘA : ‖ThetaN d (sz.L n) (sz.lam n) μs u A‖ ≤ W ^ (C₀ + K + 1) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
    have h := B45_norm_ThetaN_le (d := d) (L := sz.L n) (sz.lam n) hL3 hμ hu0 hu1 (A := A)
      (M := W ^ C₀) hAb b
    have hm : (((m + 1 : ℕ) : ℝ)) ≤ W := by push_cast; exact hWm
    calc ‖ThetaN d (sz.L n) (sz.lam n) μs u A b‖ ≤ ((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * W ^ C₀ := h
      _ ≤ W * W ^ K * W ^ C₀ := by gcongr
      _ = W ^ (C₀ + K + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring
  -- the three decays
  have hd1 : EKFastDecay (sz.lam n) u W (ε' / 2) (D' + K + 2) (A - STQop (d := d) ϑ u A) :=
    Ha (sz.L n) hL3 (sz.lam n) hlam W hWa' hLK ϑ hϑ u hu0 hu1 A hA
  have hd2 : EKFastDecay (sz.lam n) u W (2 * (ε' / 2)) (D' + K + 2 - (K + 1))
      (ThetaN d (sz.L n) (sz.lam n) μs u (A - STQop (d := d) ϑ u A)) :=
    Hc (sz.L n) hL3 (sz.lam n) hlam hlamΛ W hWc' hLK u hu0 hu1 hK μs hμ _ hAQ hd1
  have hd3 : EKFastDecay (sz.lam n) u W ε' (D' + 1)
      (ThetaN d (sz.L n) (sz.lam n) μs u A - STQop (d := d) ϑ u (ThetaN d (sz.L n) (sz.lam n) μs u A)) :=
    Hb (sz.L n) hL3 (sz.lam n) hlam W hWb' hLK ϑ hϑ u hu0 hu1 _ hΘA
  rw [show 2 * (ε' / 2) = ε' by ring, show D' + K + 2 - (K + 1) = D' + 1 by ring] at hd2
  have b1 := hd2 a ha
  have b2 := hd3 a ha
  -- the identity `ℬ₄ = Θ(𝒜 - 𝒬𝒜) - (Θ𝒜 - 𝒬Θ𝒜)`
  have hsub : ThetaN d (sz.L n) (sz.lam n) μs u (A - STQop (d := d) ϑ u A) a =
      ThetaN d (sz.L n) (sz.lam n) μs u A a -
        ThetaN d (sz.L n) (sz.lam n) μs u (STQop (d := d) ϑ u A) a :=
    QopAlgebra_ThetaN_sub (d := d) (L := sz.L n) (m := m) (sz.lam n) μs u A
      (STQop (d := d) ϑ u A) a
  have e : altB4N sz n E u ϑ σ H a =
      ThetaN d (sz.L n) (sz.lam n) μs u (A - STQop (d := d) ϑ u A) a -
        (ThetaN d (sz.L n) (sz.lam n) μs u A -
          STQop (d := d) ϑ u (ThetaN d (sz.L n) (sz.lam n) μs u A)) a := by
    rw [hsub, Pi.sub_apply]
    unfold altB4N
    ring
  rw [e]
  calc ‖ThetaN d (sz.L n) (sz.lam n) μs u (A - STQop (d := d) ϑ u A) a -
        (ThetaN d (sz.L n) (sz.lam n) μs u A -
          STQop (d := d) ϑ u (ThetaN d (sz.L n) (sz.lam n) μs u A)) a‖
      ≤ ‖ThetaN d (sz.L n) (sz.lam n) μs u (A - STQop (d := d) ϑ u A) a‖ +
        ‖(ThetaN d (sz.L n) (sz.lam n) μs u A -
          STQop (d := d) ϑ u (ThetaN d (sz.L n) (sz.lam n) μs u A)) a‖ := norm_sub_le _ _
    _ ≤ W ^ (-(D' + 1)) + W ^ (-(D' + 1)) := add_le_add b1 b2
    _ ≤ W ^ (-D') := QDriftB_two_mul_rpow_le hW2

/-! ## 5. `ℬ₅` decays at every radius and depth for the explicit mollifier -/

/-- **`altB5N_fastDecay_moll`**: `ℬ₅ = (-𝒫𝒜)_{a₁} ∂_uϑ_{u,a}` for `ϑ = QopAlgebra_mollifier`
is `QopDecay_deriv_fastDecay` with `B = -𝒫𝒜`, `‖𝒫𝒜‖ ≤ ((2^d)^m + (L^d)^m) W^{C₀} ≤ W^{C₀+Km+1}`
(`B45_Psum_le`).  `STMollifierProps` has no decay of `∂_uϑ` (clause 4 is the size only), so the
explicit mollifier is used. -/
theorem altB5N_fastDecay_moll :
    ∀ (d m : ℕ) (K C₀ ε' D' : ℝ), 0 < ε' →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ)
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1) → Bool),
        0 < sz.lam n → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
          (altB5N sz n E u (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ H) := by
  intro d m K C₀ ε' D' hε'
  obtain ⟨Wd, hWd, Hd⟩ := QopDecay_deriv_fastDecay d m K (C₀ + K * m + 1) ε' D' hε'
  refine ⟨max Wd (((2 : ℝ) ^ d) ^ m + 1), lt_of_lt_of_le hWd (le_max_left _ _), ?_⟩
  intro sz n E u H σ hlam hW hLK hu0 hu1 hK hA
  have hWd' : Wd ≤ ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hW
  have hWC : (1 : ℝ) * (((2 : ℝ) ^ d) ^ m + 1) ≤ ((sz.W n : ℕ) : ℝ) := by
    rw [one_mul]; exact (le_max_right _ _).trans hW
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : 1 < W := lt_of_lt_of_le hWd hWd'
  have hW0 : 0 < W := by linarith
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  obtain ⟨hWp1, habs⟩ := QDriftB_absorb (d := d) (m := m) (K := K) (C := 1) zero_le_one hW1
    (by omega) hLK hWC
  set A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b => sz.STLKM n E u H σ b with hAdef
  have hAb : ∀ b, ‖A b‖ ≤ W ^ C₀ := fun b => (norm_le_pi_norm A b).trans hA
  have hB : ‖fun a₁ : Zd d (sz.L n) => -STPsum (d := d) A a₁‖ ≤ W ^ (C₀ + K * m + 1) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a₁ => ?_
    rw [norm_neg]
    have h1 := QDriftB_Psum_crude (d := d) A hAb a₁
    have hW0C : (0 : ℝ) ≤ W ^ C₀ := by positivity
    calc ‖STPsum (d := d) A a₁‖
        ≤ (((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m) * W ^ C₀ := h1
      _ = W ^ C₀ * (1 * (((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m)) := by ring
      _ ≤ W ^ C₀ * (W * W ^ (K * m)) := mul_le_mul_of_nonneg_left habs hW0C
      _ = W ^ (C₀ + K * m + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring
  have e : altB5N sz n E u (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ H =
      fun a : Fin (m + 1) → Zd d (sz.L n) =>
        (fun a₁ : Zd d (sz.L n) => -STPsum (d := d) A a₁) (a 0) *
          deriv (fun τ => QopAlgebra_mollifier d (sz.L n) m (sz.lam n) τ a) u := by
    funext a
    exact (neg_mul _ _).symm
  rw [e]
  exact Hd (sz.L n) hL3 (sz.lam n) hlam W hWd' u hu0 hu1 hK _ hB

/-! ## 6. The drift class at a matrix -/

/-- **`dFlowQN_clsQN`**: `dFlowQN … u … H ∈ altClsQN … ε' Dc uu i (4 W^{-D'})` whenever
`ℓ_u ≤ ℓ_{uu i}` (the index shift of `hDcls`).  Sum-zero by `dFlowQN_sumZero`; on the `L^∞` window
`ℓ_{uu i} W^{ε'}` the `ℓ¹` window `W^{ε'} ℓ_u` is attained by a pair (`QDriftB_window_of_diamInf`);
`|𝒬_u(ℬ₁₋₃)| ≤ 2 W^{-D'}` (`drift13_fastDecay`, `QDriftB_W0_spec`), `|ℬ₄|, |ℬ₅| ≤ W^{-D'}` (hypotheses,
supplied by `altB4N_fastDecay` and `altB5N_fastDecay_moll`). -/
theorem dFlowQN_clsQN :
    ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ (m : ℕ) (K C c C₀ ε' D' : ℝ), 0 < C → 0 < c → 0 < ε' →
      ∀ {n : ℕ} {E u Γ Λ Φ τ' Dc : ℝ} {uu : ℕ → ℝ} {i : ℕ},
      QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ) →
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
      |E| ≤ 2 → 0 < sz.lam n → 0 ≤ u → u < 1 →
      ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) (uu i) →
      ∀ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ},
      H ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D' →
      ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), STMollifierProps (d := d) (sz.lam n) C c ϑ →
      (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) →
      ∀ (σ : Fin (m + 1) → Bool),
      ‖fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4N sz n E u ϑ σ H) →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB5N sz n E u ϑ σ H) →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc uu i
        (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (dFlowQN sz n E u ϑ σ H) := by
  intro d sz hd m K C c C₀ ε' D' hC hc hε' n E u Γ Λ Φ τ' Dc uu i hW hLK hdW hDD hE hlam hu0 hu1 hℓ
    H hH ϑ hϑ hdiff σ hcrude hB4 hB5
  obtain ⟨hW₀, Hq⟩ := QDriftB_W0_spec d m K C c C₀ ε' D' hC hc hε'
  have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
  have hfast := drift13_fastDecay sz hd σ hdW hH
  refine ⟨(dFlowQN_sumZero sz n E u ϑ σ H hE hu0 hu1 hϑ.1 hdiff).2.2.2.2, hDD, fun b hb => ?_⟩
  have hb' : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ (STdiamInf b : ℝ) :=
    (mul_le_mul_of_nonneg_right hℓ (Real.rpow_nonneg hW0.le _)).trans hb
  obtain ⟨i', j', hij⟩ := QDriftB_window_of_diamInf (by omega) b
    (R := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) u) (by rw [mul_comm]; exact hb')
  have hq := Hq (sz.L n) (sz.three_le_L n) (sz.lam n) hlam ((sz.W n : ℕ) : ℝ) hW hLK ϑ hϑ u hu0 hu1
    (fun b => driftTensorN sz n E u H σ b) hcrude hfast b ⟨i', j', hij⟩
  have h4 := hB4 b ⟨i', j', hij⟩
  have h5 := hB5 b ⟨i', j', hij⟩
  unfold dFlowQN
  calc _ ≤ ‖STQop (d := d) ϑ u (fun b => driftTensorN sz n E u H σ b) b‖ +
        ‖altB4N sz n E u ϑ σ H b‖ + ‖altB5N sz n E u ϑ σ H b‖ := norm_add₃_le
    _ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') + ((sz.W n : ℕ) : ℝ) ^ (-D') + ((sz.W n : ℕ) : ℝ) ^ (-D') :=
        add_le_add (add_le_add hq h4) h5
    _ = 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') := by ring

/-! ## 7. The field `hDcls` of `GridAssemblyHypN` along the walk -/

/-- **`alt_hDclsQN`**: the field `hDcls` of `GridAssemblyHypN` for
the alternating chain at the explicit mollifier: `Cls = altClsQN … ε' Dc (gridTime s v Kg n)`,
`δD = 4 W^{-D'}`, `Dr j ω = dGridQN … j ω`, on `{j < Kg n, j < τ ω}`.  `dGridQN_eq_dFlowQN`; `dFlowQN_clsQN` at
`u = u_j`, `uu = gridTime s v Kg n`, `i = j + 1` (`ℓ_{u_j} ≤ ℓ_{u_{j+1}}`: `ellT_mono`, `ST_gridTime_mono`,
`ST_gridTime_mem`); `altB4N_fastDecay`, `altB5N_fastDecay_moll` at `u = u_j` (`(1 - u_j)⁻¹ ≤ (1 - v_n)⁻¹ ≤ W^K`); the mollifier facts
`QopAlgebra_mollifier_props` (`C = (1 + 40dm) 6^{dm}`, `c = 1/2`) and
`QopAlgebra_mollifier_differentiableAt`. -/
theorem alt_hDclsQN :
    ∀ (d m : ℕ) (Λg K C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1) → Bool) (E s v : ℕ → ℝ)
        (Kg : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ),
        |E n| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ s n → s n ≤ v n → v n < 1 → (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
        4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈
          sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1) (Γ n) (Λ n) (Φ n) τ' D') →
        (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
          ‖fun b : Fin (m + 1) → Zd d (sz.L n) =>
            sz.STLKM n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ C₀) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
          ‖fun b : Fin (m + 1) → Zd d (sz.L n) =>
            driftTensorN sz n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ C₀) →
        ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
          altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1)
            (4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
            (dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) := by
  intro d m Λg K C₀ ε' D' hd hΛg hε'
  have hCm0 : (0 : ℝ) < (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) := by positivity
  obtain ⟨W₃, hW₃, H₃⟩ := altB4N_fastDecay d m Λg K ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
    (1 / 2) C₀ ε' D' hd hΛg hCm0 (by norm_num) hε'
  obtain ⟨W₄, hW₄, H₄⟩ := altB5N_fastDecay_moll d m K C₀ ε' D' hε'
  refine ⟨max (QDriftA_W0 d m K ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) (1 / 2) C₀ ε' D')
    (max W₃ W₄), lt_of_lt_of_le (QDriftA_W0_gt_one d m K _ (1 / 2) C₀ ε' D' hCm0 (by norm_num) hε')
      (le_max_left _ _), ?_⟩
  intro sz n σ E s v Kg Γ Λ Φ τ' Dc τ hE hlam hlamΛ hW hLK hs0 hsv hv1 hKv hdW hDD hτG hAcr hDcr ω j hj hjτ
  have hW0' : QDriftA_W0 d m K ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) (1 / 2) C₀ ε' D' ≤
      ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hW
  have hW3' : W₃ ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hW4' : W₄ ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  rw [dGridQN_eq_dFlowQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω]
  have hKne : Kg n ≠ 0 := by omega
  have hmem := ST_gridTime_mem s v Kg n j hsv hKne hj.le
  have hmem1 := ST_gridTime_mem s v Kg n (j + 1) hsv hKne hj
  have hmono := ST_gridTime_mono s v Kg n hsv (Nat.le_succ j)
  have hu0 : 0 ≤ gridTime s v Kg n j := hs0.trans hmem.1
  have hu1 : gridTime s v Kg n j < 1 := lt_of_le_of_lt hmem.2 hv1
  have hℓ : ellT (sz.L n) (sz.lam n) (gridTime s v Kg n j) ≤
      ellT (sz.L n) (sz.lam n) (gridTime s v Kg n (j + 1)) :=
    ellT_mono hlam.le hmono (lt_of_le_of_lt hmem1.2 hv1)
  have hKj : (1 - gridTime s v Kg n j)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K :=
    (inv_anti₀ (by linarith) (by linarith [hmem.2])).trans hKv
  have hϑ := QopAlgebra_mollifier_props d (sz.L n) m (sz.three_le_L n) hlam
  have hdiff := fun a => QopAlgebra_mollifier_differentiableAt d (sz.L n) m (sz.three_le_L n) hlam hu1 a
  have hA := hAcr ω j hj hjτ
  exact dFlowQN_clsQN sz hd m K _ (1 / 2) C₀ ε' D' hCm0 (by norm_num) hε' (n := n) (E := E n)
    (Γ := Γ n) (Λ := Λ n) (Φ := Φ n) (τ' := τ') (Dc := Dc) (u := gridTime s v Kg n j)
    (uu := gridTime s v Kg n) (i := j + 1) hW0' hLK hdW hDD hE hlam hu0 hu1 hℓ (hτG ω j hjτ)
    (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) hϑ hdiff σ (hDcr ω j hj hjτ)
    (H₃ sz n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω)
      (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ hE hlam hlamΛ hW3' hLK hu0 hu1 hKj hϑ hA)
    (H₄ sz n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ hlam hW4' hLK hu0 hu1 hKj hA)


/-! ## 3g.-7g. The generic twins over a carrier -/

/-! ## 3g. The `ℬ₁ + ℬ₂ + ℬ₃` block decays at a good matrix (over a carrier) -/

section DriftBG

variable {d : ℕ} {sz : Sizes d}

/-- **`drift13_fastDecayg`** (band `drift13_fastDecay`): the far-label clause of `GoodSetNg` (`driftTensorNg_far_of_goodSetNg`) and `fastDecay_of_diamInf`. -/
theorem drift13_fastDecayg (Cm : Step2Mat sz) (hd : 3 ≤ d) {m n : ℕ} {u Γ Λ Φ τ' ε' D' : ℝ}
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (σ : Fin (m + 1) → Bool)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hH : GoodSetNg Cm n u (m + 1) Γ Λ Φ τ' D' H) :
    EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
      (fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorNg Cm n u H σ b) := by
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  exact fastDecay_of_diamInf (by omega) hL1 hdW le_rfl
    (fun b hb => driftTensorNg_far_of_goodSetNg hH σ b hb)


end DriftBG

section ThetaG

variable {d : ℕ}


/-- `B_{u,r} ≤ 2 (1 - u)⁻¹` at a real argument (band `qdec_Bparam_le`). -/
private theorem QDriftB_BparamR_le {L : ℕ} (g u : ℝ) (hL : 1 ≤ L) (hu : u < 1) {r : ℝ} (hr : 0 ≤ r) :
    BparamR d L g u r ≤ 2 * (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have habs : |1 - u| = 1 - u := abs_of_pos h1u
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold BparamR
  rw [habs]
  have a1 : (g ^ 2 + (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1u (by nlinarith [sq_nonneg g])
  have a2 : ((r + 1) ^ (d - 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have a3 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
    inv_anti₀ h1u (by nlinarith [one_le_pow₀ (n := d) hL1])
  have a4 : 0 ≤ (g ^ 2 + (1 - u))⁻¹ := inv_nonneg.2 (by nlinarith [sq_nonneg g])
  have a5 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := inv_nonneg.2 (by positivity)
  calc (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹
      ≤ (1 - u)⁻¹ * 1 + (1 - u)⁻¹ := by gcongr
    _ = 2 * (1 - u)⁻¹ := by ring

/-- **`Θ^{(k)}_u` over a carrier maps a decaying tensor to a decaying tensor** (band `QopDecay_ThetaN_fastDecay`): the class
`Step5KerGen_ThDecay C gK Λ C₆` of the one-index kernel at the kernel coupling `gK`, the comparison of couplings (`tailT^{gK} ≤ A tailT^{lam}`,
`Step5KerGen_tailT_cross`), the row sums `C₆/(1-u)`; a `(u, ε, D)`-decaying tensor of size `≤ W^{C₀}` is mapped to a `(u, 2ε, D - (K + 1))`-decaying
tensor at the size level `sz.lam`, for `W ≥ W₀(d, k, Λ, C₆, A, K, C₀, ε, D)`, `L^d ≤ W^K`, `(1 - u)⁻¹ ≤ W^K`. -/
private theorem QDriftB_ThetaNg_fastDecay (d k : ℕ) (hd : 0 < d) (C₆ A K C₀ ε D : ℝ) (hC₆ : 0 ≤ C₆) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (Λ : ℝ) (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (n : ℕ), Step5KerGen_ThDecay C gK Λ C₆ →
      (∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) → 0 < gK n → gK n ≤ Λ →
      ∀ W : ℝ, W₀ ≤ W → ((sz.L n : ℕ) : ℝ) ^ d ≤ W ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ W ^ K → ∀ σ : Fin k → Bool,
      ∀ 𝒜 : (Fin k → Zd d (sz.L n)) → ℂ, ‖𝒜‖ ≤ W ^ C₀ → EKFastDecay (sz.lam n) u W ε D 𝒜 →
        EKFastDecay (sz.lam n) u W (2 * ε) (D - (K + 1)) (Step2Gen_ThetaN C n σ u 𝒜) := by
  set Cc : ℝ := 2 * C₆ * A + 1 with hCc
  have hCc0 : 0 < Cc := by have : 0 ≤ 2 * C₆ * A := by positivity
                           linarith
  obtain ⟨W₁, hW₁, hgrow⟩ := qdec_growth (C := 2 * ((k : ℝ) + 1) * Cc) (c := 1 / (d : ℝ)) (ε' := ε)
    (p := K + C₀ + D - 1) (by positivity) (by have : (0 : ℝ) < d := by exact_mod_cast hd
                                              positivity) hε
  refine ⟨max W₁ (max ((2 : ℝ) ^ (1 / ε)) (2 * (k : ℝ) * (C₆ + 1))), lt_of_lt_of_le hW₁ (le_max_left _ _), ?_⟩
  intro Λ sz C gK n hdec hcmp hg hgΛ W hW hLW u hu0 hu1 hKu σ 𝒜 hAn hAd a ⟨j, j', hjk⟩
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans hW
  have hW2ε : (2 : ℝ) ^ (1 / ε) ≤ W := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWk : 2 * (k : ℝ) * (C₆ + 1) ≤ W := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hW1 : 1 < W := lt_of_lt_of_le hW₁ hWW₁
  have hW0 : 0 < W := by linarith
  have hWε : 2 ≤ W ^ ε := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
      _ ≤ W ^ ε := Real.rpow_le_rpow (by positivity) hW2ε hε.le
  have hWε2 : W ^ (2 * ε) = W ^ ε * W ^ ε := by rw [two_mul, Real.rpow_add hW0]
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  set ℓ := ellT (sz.L n) (sz.lam n) u with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set x := 1 / (d : ℝ) * W ^ ε / 2 with hx
  have hr : 2 * (W ^ ε * ℓ) ≤ W ^ (2 * ε) * ℓ := by
    rw [hWε2]
    nlinarith [mul_nonneg (sub_nonneg.2 hWε) (mul_nonneg (by linarith : (0 : ℝ) ≤ W ^ ε) hℓ0.le)]
  obtain ⟨hlam0, hgl⟩ := Step5KerGen_cmp_pos (hcmp n) hg
  have hcr : ∀ (σ₁ σ₂ : Bool) (b b' : Zd d (sz.L n)),
      ‖Step2Gen_thetaKer C n σ₁ σ₂ u b b'‖ ≤
        2 * C₆ * A * (1 - u)⁻¹ * Real.exp (-Real.sqrt (((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ) / ℓ)) := by
    intro σ₁ σ₂ b b'
    obtain ⟨hθ, -⟩ := hdec n hg hgΛ σ₁ σ₂ u hu0 hu1
    have hcross := Step5KerGen_tailT_cross (d := d) (L := sz.L n) (t := u)
      (r := ((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ)) hL1 hg hgl (hcmp n).2.2 hA hu1 (Nat.cast_nonneg _)
    have hB := QDriftB_BparamR_le (d := d) (L := sz.L n) (sz.lam n) u (by have := sz.three_le_L n; omega) hu1
      (r := ((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ)) (Nat.cast_nonneg _)
    have hE0 : 0 ≤ Real.exp (-Real.sqrt (((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ) / ℓ)) := (Real.exp_pos _).le
    refine (hθ b b').trans ?_
    calc C₆ * tailT d (sz.L n) (gK n) u ((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ)
        ≤ C₆ * (A * tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcross hC₆
      _ ≤ C₆ * (A * (2 * (1 - u)⁻¹ * Real.exp (-Real.sqrt (((zdistInf d (sz.L n) (b' - b) : ℕ) : ℝ) / ℓ)))) := by
          unfold tailT
          gcongr
      _ = _ := by ring
  have hpar : ∀ i : Fin k, ‖∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b *
      𝒜 (Function.update a i b)‖ ≤ C₆ * W ^ K * W ^ (-D) + W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x)) := by
    intro i
    have hconst : 0 ≤ Cc * W ^ K * W ^ C₀ * Real.exp (-x) := by positivity
    have hpt : ∀ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b * 𝒜 (Function.update a i b)‖ ≤
        ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖ * W ^ (-D) + Cc * W ^ K * W ^ C₀ * Real.exp (-x) := by
      intro b
      rw [norm_mul]
      by_cases hnear : ∃ p q : Fin k,
          W ^ ε * ℓ ≤ (zdistD d (sz.L n) (Function.update a i b p - Function.update a i b q) : ℝ)
      · have h1 : ‖𝒜 (Function.update a i b)‖ ≤ W ^ (-D) := hAd _ hnear
        have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b))
        linarith
      · push Not at hnear
        have hdist := qdec_far_dist a b i j j' hr hjk hnear
        have hinf : (zdistD d (sz.L n) (b - a i) : ℝ) ≤ d * ((zdistInf d (sz.L n) (b - a i) : ℕ) : ℝ) := by
          exact_mod_cast zdistD_le_mul_zdistInf d (sz.L n) (b - a i)
        have hxs : x ≤ Real.sqrt (((zdistInf d (sz.L n) (b - a i) : ℕ) : ℝ) / ℓ) := by
          refine Real.le_sqrt_of_sq_le ?_
          have hrinf : W ^ (2 * ε) * ℓ / 2 / d ≤ ((zdistInf d (sz.L n) (b - a i) : ℕ) : ℝ) := by
            rw [div_le_iff₀ hd0]
            nlinarith
          have h2 : W ^ (2 * ε) / 2 / d ≤ ((zdistInf d (sz.L n) (b - a i) : ℕ) : ℝ) / ℓ := by
            rw [le_div_iff₀ hℓ0]
            calc W ^ (2 * ε) / 2 / d * ℓ = W ^ (2 * ε) * ℓ / 2 / d := by ring
              _ ≤ _ := hrinf
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
          have hWp : 0 ≤ W ^ ε := Real.rpow_nonneg hW0.le _
          have e1 : x ^ 2 = (W ^ ε) ^ 2 / (4 * (d : ℝ) ^ 2) := by
            rw [hx]; field_simp; ring
          have e2 : W ^ (2 * ε) / 2 / d = (W ^ ε) ^ 2 / (2 * (d : ℝ)) := by
            rw [hWε2]; field_simp
          have e3 : (W ^ ε) ^ 2 / (4 * (d : ℝ) ^ 2) ≤ (W ^ ε) ^ 2 / (2 * (d : ℝ)) := by
            apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
            nlinarith
          calc x ^ 2 = (W ^ ε) ^ 2 / (4 * (d : ℝ) ^ 2) := e1
            _ ≤ (W ^ ε) ^ 2 / (2 * (d : ℝ)) := e3
            _ = W ^ (2 * ε) / 2 / d := e2.symm
            _ ≤ _ := h2
        have hexp : Real.exp (-Real.sqrt (((zdistInf d (sz.L n) (b - a i) : ℕ) : ℝ) / ℓ)) ≤ Real.exp (-x) :=
          Real.exp_le_exp.2 (neg_le_neg hxs)
        have hKb := hcr (σ i) (σ (finRotate k i)) (a i) b
        have hK1 : ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖ ≤ Cc * W ^ K * Real.exp (-x) := by
          refine hKb.trans ?_
          have hu' : (1 - u)⁻¹ ≤ W ^ K := hKu
          have h2CA : 2 * C₆ * A ≤ Cc := by linarith
          have h0 : 0 ≤ 2 * C₆ * A := by positivity
          exact mul_le_mul (mul_le_mul h2CA hu' (inv_nonneg.2 (by linarith)) hCc0.le) hexp (Real.exp_pos _).le
            (by positivity)
        have hA1 : ‖𝒜 (Function.update a i b)‖ ≤ W ^ C₀ := (norm_le_pi_norm 𝒜 _).trans hAn
        have h3 := mul_le_mul hK1 hA1 (norm_nonneg _) (by positivity)
        have h4 : 0 ≤ ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖ * W ^ (-D) := by positivity
        calc _ ≤ Cc * W ^ K * Real.exp (-x) * W ^ C₀ := h3
          _ = Cc * W ^ K * W ^ C₀ * Real.exp (-x) := by ring
          _ ≤ _ := by linarith
    obtain ⟨-, hrowC⟩ := hdec n hg hgΛ (σ i) (σ (finRotate k i)) u hu0 hu1
    calc ‖∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b * 𝒜 (Function.update a i b)‖
        ≤ ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b * 𝒜 (Function.update a i b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ b : Zd d (sz.L n), (‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖ * W ^ (-D) +
            Cc * W ^ K * W ^ C₀ * Real.exp (-x)) := Finset.sum_le_sum fun b _ => hpt b
      _ = (∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖) * W ^ (-D) +
            (((sz.L n : ℕ) : ℝ) ^ d) * (Cc * W ^ K * W ^ C₀ * Real.exp (-x)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast; ring
      _ ≤ C₆ * W ^ K * W ^ (-D) + W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x)) := by
          have h1 : ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖ ≤ C₆ * W ^ K :=
            hrowC (a i) |>.trans (by
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_left hKu hC₆)
          gcongr
  simp only [Step2Gen_ThetaN]
  refine (norm_sum_le _ _).trans ?_
  have hQ0 : 0 ≤ W ^ K * W ^ (-D) := by positivity
  set Z := W ^ (-(D - (K + 1))) with hZ
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hW0 _
  have hZe : Z = W * (W ^ K * W ^ (-D)) := by
    rw [hZ, show -(D - (K + 1)) = 1 + K + -D by ring, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
    ring
  have hT1 : (k : ℝ) * (C₆ * W ^ K * W ^ (-D)) ≤ Z / 2 := by
    rw [hZe]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hkc' : (k : ℝ) * C₆ ≤ (k : ℝ) * (C₆ + 1) := mul_le_mul_of_nonneg_left (by linarith) hk0
    have hkc : (k : ℝ) * C₆ ≤ W / 2 := by linarith [hWk]
    calc (k : ℝ) * (C₆ * W ^ K * W ^ (-D)) = ((k : ℝ) * C₆) * (W ^ K * W ^ (-D)) := by ring
      _ ≤ (W / 2) * (W ^ K * W ^ (-D)) := mul_le_mul_of_nonneg_right hkc hQ0
      _ = W * (W ^ K * W ^ (-D)) / 2 := by ring
  have hpow : W ^ K * W ^ K * W ^ C₀ = W ^ (K + C₀ + D - 1) * Z := by
    have h1 : W ^ K * W ^ K * W ^ C₀ = W ^ (K + K + C₀) := by rw [Real.rpow_add hW0, Real.rpow_add hW0]
    have h2 : W ^ (K + C₀ + D - 1) * Z = W ^ (K + C₀ + D - 1 + -(D - (K + 1))) := by
      rw [hZ, Real.rpow_add hW0]
    rw [h1, h2]; congr 1; ring
  have hg1 := hgrow W hWW₁
  set q := Cc * W ^ (K + C₀ + D - 1) * Real.exp (-x) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : 2 * ((k : ℝ) + 1) * q ≤ 1 := by
    calc 2 * ((k : ℝ) + 1) * q = (2 * ((k : ℝ) + 1) * Cc * W ^ (K + C₀ + D - 1)) * Real.exp (-x) := by
          rw [hq]; ring
      _ ≤ Real.exp x * Real.exp (-x) := mul_le_mul_of_nonneg_right hg1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hT2 : (k : ℝ) * (W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x))) ≤ Z / 2 := by
    have e : W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x)) = Z * q := by
      calc W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x)) = Cc * (W ^ K * W ^ K * W ^ C₀) * Real.exp (-x) := by ring
        _ = Cc * (W ^ (K + C₀ + D - 1) * Z) * Real.exp (-x) := by rw [hpow]
        _ = Z * q := by rw [hq]; ring
    rw [e]
    have hn1 : (k : ℝ) * q ≤ ((k : ℝ) + 1) * q := mul_le_mul_of_nonneg_right (by linarith) hq0
    have hnq : (k : ℝ) * q ≤ 1 / 2 := by linarith only [hn1, hq1]
    calc (k : ℝ) * (Z * q) = Z * ((k : ℝ) * q) := by ring
      _ ≤ Z * (1 / 2) := mul_le_mul_of_nonneg_left hnq hZ0.le
      _ = Z / 2 := by ring
  calc ∑ i : Fin k, ‖∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b * 𝒜 (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (C₆ * W ^ K * W ^ (-D) + W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x))) :=
        Finset.sum_le_sum fun i _ => hpar i
    _ = (k : ℝ) * (C₆ * W ^ K * W ^ (-D)) + (k : ℝ) * (W ^ K * (Cc * W ^ K * W ^ C₀ * Real.exp (-x))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ Z := by linarith

end ThetaG


/-! ## 4g. `ℬ₄` decays at every radius and depth from the crude sup alone (over a carrier) -/

section B4G

/-- **`altB4Ng_fastDecay`** (band `altB4N_fastDecay`): `ℬ₄ = Θ(𝒜 - 𝒬𝒜) - (Θ𝒜 - 𝒬Θ𝒜)` decays at the size level `sz.lam` at every radius and
depth from the crude sup of `𝒜 = (𝓛-𝒦)_{u,σ}(H)` alone.  The kernel of `Θ` is `Step2Gen_thetaKer` with the class `Step5KerGen_ThDecay Cm.toFlowFM gK Λg C₆`
(`C₆` before the carrier), the comparison of couplings (`gK² ≤ lam² ≤ A gK²`) crosses the tail to `sz.lam` (`QDriftB_ThetaNg_fastDecay`). -/
theorem altB4Ng_fastDecay :
    ∀ (d m : ℕ) (Λg K C c C₀ ε' D' C₆ A : ℝ), 3 ≤ d → 0 < Λg → 0 < C → 0 < c → 0 < ε' → 0 ≤ C₆ → 1 ≤ A →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (Cm : Step2Mat sz) (gK : ℕ → ℝ) (n : ℕ) (u : ℝ)
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool),
        Step5KerGen_ThDecay Cm.toFlowFM gK Λg C₆ →
        (∀ m', 0 ≤ gK m' * sz.lam m' ∧ gK m' ^ 2 ≤ sz.lam m' ^ 2 ∧ sz.lam m' ^ 2 ≤ A * gK m' ^ 2) →
        0 < gK n → gK n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        STMollifierProps (d := d) (sz.lam n) C c ϑ →
        ‖fun b : Fin (m + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4Ng Cm n u ϑ σ H) := by
  intro d m Λg K C c C₀ ε' D' C₆ A hd hΛg hC hc hε' hC₆ hA
  have hε2 : 0 < ε' / 2 := by positivity
  obtain ⟨Wa, hWa, Ha⟩ := stQop_sub_fastDecay d m K C c C₀ (ε' / 2) (D' + K + 2) hC hc hε2
  obtain ⟨Wb, hWb, Hb⟩ := stQop_sub_fastDecay d m K C c (C₀ + K + 1) ε' (D' + 1) hC hc hε'
  obtain ⟨Wc, hWc, Hc⟩ := QDriftB_ThetaNg_fastDecay d (m + 1) (by omega) C₆ A K (C₀ + K * m + 1) (ε' / 2)
    (D' + K + 2) hC₆ hA hε2
  refine ⟨max (max Wa Wb) (max Wc (max (C * (((2 : ℝ) ^ d) ^ m + 1)) (max (((m : ℝ) + 1) * (C₆ + 1)) 2))),
    lt_of_lt_of_le hWa ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro sz Cm gK n u H ϑ σ hdec hcmp hg hgΛ hW hLK hu0 hu1 hK hϑ hAn a ha
  have hWa' : Wa ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hW
  have hWb' : Wb ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hW
  have hWc' : Wc ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hWC : C * (((2 : ℝ) ^ d) ^ m + 1) ≤ ((sz.W n : ℕ) : ℝ) :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hWm : ((m : ℝ) + 1) * (C₆ + 1) ≤ ((sz.W n : ℕ) : ℝ) :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  have hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hW
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : 1 < W := by linarith
  have hW0 : 0 < W := by linarith
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hL1 : 1 ≤ sz.L n := by omega
  have hlam : 0 < sz.lam n := (Step5KerGen_cmp_pos (hcmp n) hg).1
  set Aa : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b => STLKMg Cm n u H σ b with hAadef
  have hAb : ∀ b, ‖Aa b‖ ≤ W ^ C₀ := fun b => (norm_le_pi_norm Aa b).trans hAn
  have hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ C₆ / (1 - t) :=
    fun σ σ' t ht0 ht1 a => (hdec n hg hgΛ σ σ' t ht0 ht1).2 a
  obtain ⟨hWp1, habs⟩ := QDriftB_absorb (d := d) (m := m) (K := K) hC.le hW1 hL1 hLK hWC
  have hAQ : ‖Aa - STQop (d := d) ϑ u Aa‖ ≤ W ^ (C₀ + K * m + 1) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
    have e : (Aa - STQop (d := d) ϑ u Aa) b = STPsum (d := d) Aa (b 0) * ϑ u b := by simp [STQop]
    rw [e, norm_mul]
    have h1 := QDriftB_Psum_crude (d := d) Aa hAb (b 0)
    have h2 := QDriftB_mollifier_norm_le hC.le hc.le hϑ hu0 hu1 b
    have hC0 : 0 ≤ ‖STPsum (d := d) Aa (b 0)‖ := norm_nonneg _
    have hW0C : (0 : ℝ) ≤ W ^ C₀ := by positivity
    calc ‖STPsum (d := d) Aa (b 0)‖ * ‖ϑ u b‖
        ≤ ((((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m) * W ^ C₀) * C :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = W ^ C₀ * (C * (((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m)) := by ring
      _ ≤ W ^ C₀ * (W * W ^ (K * m)) := mul_le_mul_of_nonneg_left habs hW0C
      _ = W ^ (C₀ + K * m + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring
  have hΘA : ‖Step2Gen_ThetaN Cm.toFlowFM n σ u Aa‖ ≤ W ^ (C₀ + K + 1) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
    have h := B45_norm_ThetaN_leg Cm.toFlowFM n hrow σ hu0 hu1 (A := Aa) (M := W ^ C₀) hAb b
    have hm : (((m + 1 : ℕ) : ℝ)) * C₆ ≤ W := by
      push_cast
      have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      have : ((m : ℝ) + 1) * C₆ ≤ ((m : ℝ) + 1) * (C₆ + 1) := mul_le_mul_of_nonneg_left (by linarith) hm0
      linarith
    have hinv : (1 - u)⁻¹ ≤ W ^ K := hK
    calc ‖Step2Gen_ThetaN Cm.toFlowFM n σ u Aa b‖ ≤ ((m + 1 : ℕ) : ℝ) * (C₆ / (1 - u)) * W ^ C₀ := h
      _ = (((m + 1 : ℕ) : ℝ) * C₆) * (1 - u)⁻¹ * W ^ C₀ := by rw [div_eq_mul_inv]; ring
      _ ≤ W * W ^ K * W ^ C₀ := by gcongr
      _ = W ^ (C₀ + K + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring
  have hd1 : EKFastDecay (sz.lam n) u W (ε' / 2) (D' + K + 2) (Aa - STQop (d := d) ϑ u Aa) :=
    Ha (sz.L n) hL3 (sz.lam n) hlam W hWa' hLK ϑ hϑ u hu0 hu1 Aa hAn
  have hd2 : EKFastDecay (sz.lam n) u W (2 * (ε' / 2)) (D' + K + 2 - (K + 1))
      (Step2Gen_ThetaN Cm.toFlowFM n σ u (Aa - STQop (d := d) ϑ u Aa)) :=
    Hc Λg sz Cm.toFlowFM gK n hdec hcmp hg hgΛ W hWc' hLK u hu0 hu1 hK σ _ hAQ hd1
  have hd3 : EKFastDecay (sz.lam n) u W ε' (D' + 1)
      (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa - STQop (d := d) ϑ u (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa)) :=
    Hb (sz.L n) hL3 (sz.lam n) hlam W hWb' hLK ϑ hϑ u hu0 hu1 _ hΘA
  rw [show 2 * (ε' / 2) = ε' by ring, show D' + K + 2 - (K + 1) = D' + 1 by ring] at hd2
  have b1 := hd2 a ha
  have b2 := hd3 a ha
  have hsub : Step2Gen_ThetaN Cm.toFlowFM n σ u (Aa - STQop (d := d) ϑ u Aa) a =
      Step2Gen_ThetaN Cm.toFlowFM n σ u Aa a -
        Step2Gen_ThetaN Cm.toFlowFM n σ u (STQop (d := d) ϑ u Aa) a :=
    QopAlgebra_ThetaN_subg Cm.toFlowFM n σ u Aa (STQop (d := d) ϑ u Aa) a
  have e : altB4Ng Cm n u ϑ σ H a =
      Step2Gen_ThetaN Cm.toFlowFM n σ u (Aa - STQop (d := d) ϑ u Aa) a -
        (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa -
          STQop (d := d) ϑ u (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa)) a := by
    rw [hsub, Pi.sub_apply]
    unfold altB4Ng
    ring
  rw [e]
  calc ‖Step2Gen_ThetaN Cm.toFlowFM n σ u (Aa - STQop (d := d) ϑ u Aa) a -
        (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa -
          STQop (d := d) ϑ u (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa)) a‖
      ≤ ‖Step2Gen_ThetaN Cm.toFlowFM n σ u (Aa - STQop (d := d) ϑ u Aa) a‖ +
        ‖(Step2Gen_ThetaN Cm.toFlowFM n σ u Aa -
          STQop (d := d) ϑ u (Step2Gen_ThetaN Cm.toFlowFM n σ u Aa)) a‖ := norm_sub_le _ _
    _ ≤ W ^ (-(D' + 1)) + W ^ (-(D' + 1)) := add_le_add b1 b2
    _ ≤ W ^ (-D') := QDriftB_two_mul_rpow_le hW2

end B4G

/-- **Band concluder with head `Step5KerGen_ThDecay`**: the premise of `altB4Ng_fastDecay` and `alt_hDclsQNg` holds at the band flow
`bandFM sz E` (`|E n| ≤ 2`) with the constant `C₆ = C₆(d, Λ)` of `step5KerGen_thDecay_band`, at `gK = sz.lam`. -/
theorem qDriftB_thDecay_band_concl (d : ℕ) (hd : 3 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2) :
    Step5KerGen_ThDecay (bandFM sz E) sz.lam Λ (Classical.choose (step5KerGen_thDecay_band d Λ hd hΛ)) :=
  (Classical.choose_spec (step5KerGen_thDecay_band d Λ hd hΛ)).2 sz E hE

/-! ## 5g. `ℬ₅` decays at every radius and depth for the explicit mollifier (over a carrier) -/

section B5G

/-- **`altB5Ng_fastDecay_moll`** (band `altB5N_fastDecay_moll`): the size level `sz.lam` only; the carrier enters through `STLKMg`. -/
theorem altB5Ng_fastDecay_moll :
    ∀ (d m : ℕ) (K C₀ ε' D' : ℝ), 0 < ε' →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (Cm : Step2Mat sz) (n : ℕ) (u : ℝ)
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1) → Bool),
        0 < sz.lam n → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        ‖fun b : Fin (m + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
          (altB5Ng Cm n u (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ H) := by
  intro d m K C₀ ε' D' hε'
  obtain ⟨Wd, hWd, Hd⟩ := QopDecay_deriv_fastDecay d m K (C₀ + K * m + 1) ε' D' hε'
  refine ⟨max Wd (((2 : ℝ) ^ d) ^ m + 1), lt_of_lt_of_le hWd (le_max_left _ _), ?_⟩
  intro sz Cm n u H σ hlam hW hLK hu0 hu1 hK hAn
  have hWd' : Wd ≤ ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hW
  have hWC : (1 : ℝ) * (((2 : ℝ) ^ d) ^ m + 1) ≤ ((sz.W n : ℕ) : ℝ) := by
    rw [one_mul]; exact (le_max_right _ _).trans hW
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW1 : 1 < W := lt_of_lt_of_le hWd hWd'
  have hW0 : 0 < W := by linarith
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  obtain ⟨hWp1, habs⟩ := QDriftB_absorb (d := d) (m := m) (K := K) (C := 1) zero_le_one hW1
    (by omega) hLK hWC
  set Aa : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b => STLKMg Cm n u H σ b with hAadef
  have hAb : ∀ b, ‖Aa b‖ ≤ W ^ C₀ := fun b => (norm_le_pi_norm Aa b).trans hAn
  have hB : ‖fun a₁ : Zd d (sz.L n) => -STPsum (d := d) Aa a₁‖ ≤ W ^ (C₀ + K * m + 1) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a₁ => ?_
    rw [norm_neg]
    have h1 := QDriftB_Psum_crude (d := d) Aa hAb a₁
    have hW0C : (0 : ℝ) ≤ W ^ C₀ := by positivity
    calc ‖STPsum (d := d) Aa a₁‖
        ≤ (((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m) * W ^ C₀ := h1
      _ = W ^ C₀ * (1 * (((2 : ℝ) ^ d) ^ m + (((sz.L n : ℕ) : ℝ) ^ d) ^ m)) := by ring
      _ ≤ W ^ C₀ * (W * W ^ (K * m)) := mul_le_mul_of_nonneg_left habs hW0C
      _ = W ^ (C₀ + K * m + 1) := by
          rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring
  have e : altB5Ng Cm n u (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ H =
      fun a : Fin (m + 1) → Zd d (sz.L n) =>
        (fun a₁ : Zd d (sz.L n) => -STPsum (d := d) Aa a₁) (a 0) *
          deriv (fun τ => QopAlgebra_mollifier d (sz.L n) m (sz.lam n) τ a) u := by
    funext a
    exact (neg_mul _ _).symm
  rw [e]
  exact Hd (sz.L n) hL3 (sz.lam n) hlam W hWd' u hu0 hu1 hK _ hB

end B5G


/-! ## 6g. The drift class at a matrix, and the field `hDcls` along the walk (over a carrier) -/

section ClsG

/-- **`dFlowQNg_clsQNg`** (band `dFlowQN_clsQN`): `dFlowQNg … u … H ∈ altClsQN … ε' Dc uu i (4 W^{-D'})` whenever `ℓ_u ≤ ℓ_{uu i}`.  The kernel class
`ZeroModeGen_KerSums` (the sum-zero of the drift) is used in place of `|E| ≤ 2`; the good set is `GoodSetNg`. -/
theorem dFlowQNg_clsQNg :
    ∀ {d : ℕ} (sz : Sizes d) (Cm : Step2Mat sz), 3 ≤ d → ∀ (m : ℕ) (K C c C₀ ε' D' : ℝ), 0 < C → 0 < c → 0 < ε' →
      ∀ {n : ℕ} {u Γ Λ Φ τ' Dc : ℝ} {uu : ℕ → ℝ} {i : ℕ},
      ZeroModeGen_KerSums Cm.toFlowFM n →
      QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ) →
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
      0 < sz.lam n → 0 ≤ u → u < 1 →
      ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) (uu i) →
      ∀ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ},
      GoodSetNg Cm n u (m + 1) Γ Λ Φ τ' D' H →
      ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), STMollifierProps (d := d) (sz.lam n) C c ϑ →
      (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) →
      ∀ (σ : Fin (m + 1) → Bool),
      ‖fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorNg Cm n u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4Ng Cm n u ϑ σ H) →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB5Ng Cm n u ϑ σ H) →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc uu i
        (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (dFlowQNg Cm n u ϑ σ H) := by
  intro d sz Cm hd m K C c C₀ ε' D' hC hc hε' n u Γ Λ Φ τ' Dc uu i hKS hW hLK hdW hDD hlam hu0 hu1 hℓ
    H hH ϑ hϑ hdiff σ hcrude hB4 hB5
  obtain ⟨hW₀, Hq⟩ := QDriftB_W0_spec d m K C c C₀ ε' D' hC hc hε'
  have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
  have hfast := drift13_fastDecayg Cm hd σ hdW hH
  refine ⟨(dFlowQNg_sumZero Cm n hKS u ϑ σ H hϑ.1 hdiff).2.2.2.2, hDD, fun b hb => ?_⟩
  have hb' : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ (STdiamInf b : ℝ) :=
    (mul_le_mul_of_nonneg_right hℓ (Real.rpow_nonneg hW0.le _)).trans hb
  obtain ⟨i', j', hij⟩ := QDriftB_window_of_diamInf (by omega) b
    (R := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) u) (by rw [mul_comm]; exact hb')
  have hq := Hq (sz.L n) (sz.three_le_L n) (sz.lam n) hlam ((sz.W n : ℕ) : ℝ) hW hLK ϑ hϑ u hu0 hu1
    (fun b => driftTensorNg Cm n u H σ b) hcrude hfast b ⟨i', j', hij⟩
  have h4 := hB4 b ⟨i', j', hij⟩
  have h5 := hB5 b ⟨i', j', hij⟩
  unfold dFlowQNg
  calc _ ≤ ‖STQop (d := d) ϑ u (fun b => driftTensorNg Cm n u H σ b) b‖ +
        ‖altB4Ng Cm n u ϑ σ H b‖ + ‖altB5Ng Cm n u ϑ σ H b‖ := norm_add₃_le
    _ ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') + ((sz.W n : ℕ) : ℝ) ^ (-D') + ((sz.W n : ℕ) : ℝ) ^ (-D') :=
        add_le_add (add_le_add hq h4) h5
    _ = 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') := by ring


/-- **`alt_hDclsQNg`** (band `alt_hDclsQN`): the field `hDcls` of `GridAssemblyHypNg` for the alternating chain at the explicit mollifier over a carrier:
`Cls = altClsQN … ε' Dc (gridTime s v Kg n)`, `δD = 4 W^{-D'}`, `Dr j ω = dGridQNg … j ω`, on `{j < Kg n, j < τ ω}`.  The kernel enters through
`ZeroModeGen_KerSums` (sum-zero of the drift) and `Step5KerGen_ThDecay` at `gK` with the comparison of couplings (`C₆`, `A` before the carrier). -/
theorem alt_hDclsQNg :
    ∀ (d m : ℕ) (Λg K C₀ ε' D' C₆ A : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' → 0 ≤ C₆ → 1 ≤ A →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (Cm : Step2Mat sz) (gK : ℕ → ℝ) (n : ℕ) (σ : Fin (m + 1) → Bool)
        (s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ),
        ZeroModeGen_KerSums Cm.toFlowFM n → Step5KerGen_ThDecay Cm.toFlowFM gK Λg C₆ →
        (∀ m', 0 ≤ gK m' * sz.lam m' ∧ gK m' ^ 2 ≤ sz.lam m' ^ 2 ∧ sz.lam m' ^ 2 ≤ A * gK m' ^ 2) →
        0 < gK n → gK n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ s n → s n ≤ v n → v n < 1 → (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
        4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → GoodSetNg Cm n (gridTime s v Kg n j) (m + 1)
          (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v Kg n j ω)) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
          ‖fun b : Fin (m + 1) → Zd d (sz.L n) =>
            STLKMg Cm n (gridTime s v Kg n j) (Cm.Hpath s v Kg n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
          ‖fun b : Fin (m + 1) → Zd d (sz.L n) =>
            driftTensorNg Cm n (gridTime s v Kg n j) (Cm.Hpath s v Kg n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) →
        ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
          altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1)
            (4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
            (dGridQNg Cm s v Kg n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) := by
  intro d m Λg K C₀ ε' D' C₆ A hd hΛg hε' hC₆ hA
  have hCm0 : (0 : ℝ) < (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) := by positivity
  obtain ⟨W₃, hW₃, H₃⟩ := altB4Ng_fastDecay d m Λg K ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
    (1 / 2) C₀ ε' D' C₆ A hd hΛg hCm0 (by norm_num) hε' hC₆ hA
  obtain ⟨W₄, hW₄, H₄⟩ := altB5Ng_fastDecay_moll d m K C₀ ε' D' hε'
  refine ⟨max (QDriftA_W0 d m K ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) (1 / 2) C₀ ε' D')
    (max W₃ W₄), lt_of_lt_of_le (QDriftA_W0_gt_one d m K _ (1 / 2) C₀ ε' D' hCm0 (by norm_num) hε')
      (le_max_left _ _), ?_⟩
  intro sz Cm gK n σ s v Kg Γ Λ Φ τ' Dc τ hKS hdec hcmp hg hgΛ hW hLK hs0 hsv hv1 hKv hdW hDD hτG hAcr hDcr ω j hj hjτ
  have hW0' : QDriftA_W0 d m K ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) (1 / 2) C₀ ε' D' ≤
      ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hW
  have hW3' : W₃ ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hW
  have hW4' : W₄ ≤ ((sz.W n : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hW
  have hlam : 0 < sz.lam n := (Step5KerGen_cmp_pos (hcmp n) hg).1
  rw [dGridQNg_eq_dFlowQNg Cm s v Kg n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω]
  have hKne : Kg n ≠ 0 := by omega
  have hmem := ST_gridTime_mem s v Kg n j hsv hKne hj.le
  have hmem1 := ST_gridTime_mem s v Kg n (j + 1) hsv hKne hj
  have hmono := ST_gridTime_mono s v Kg n hsv (Nat.le_succ j)
  have hu0 : 0 ≤ gridTime s v Kg n j := hs0.trans hmem.1
  have hu1 : gridTime s v Kg n j < 1 := lt_of_le_of_lt hmem.2 hv1
  have hℓ : ellT (sz.L n) (sz.lam n) (gridTime s v Kg n j) ≤
      ellT (sz.L n) (sz.lam n) (gridTime s v Kg n (j + 1)) :=
    ellT_mono hlam.le hmono (lt_of_le_of_lt hmem1.2 hv1)
  have hKj : (1 - gridTime s v Kg n j)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K :=
    (inv_anti₀ (by linarith) (by linarith [hmem.2])).trans hKv
  have hϑ := QopAlgebra_mollifier_props d (sz.L n) m (sz.three_le_L n) hlam
  have hdiff := fun a => QopAlgebra_mollifier_differentiableAt d (sz.L n) m (sz.three_le_L n) hlam hu1 a
  have hA' := hAcr ω j hj hjτ
  exact dFlowQNg_clsQNg sz Cm hd m K _ (1 / 2) C₀ ε' D' hCm0 (by norm_num) hε' (n := n)
    (Γ := Γ n) (Λ := Λ n) (Φ := Φ n) (τ' := τ') (Dc := Dc) (u := gridTime s v Kg n j)
    (uu := gridTime s v Kg n) (i := j + 1) hKS hW0' hLK hdW hDD hlam hu0 hu1 hℓ (hτG ω j hjτ)
    (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) hϑ hdiff σ (hDcr ω j hj hjτ)
    (H₃ sz Cm gK n (gridTime s v Kg n j) (Cm.Hpath s v Kg n j ω)
      (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ hdec hcmp hg hgΛ hW3' hLK hu0 hu1 hKj hϑ hA')
    (H₄ sz Cm n (gridTime s v Kg n j) (Cm.Hpath s v Kg n j ω) σ hlam hW4' hLK hu0 hu1 hKj hA')

end ClsG

end RBM.Ind

end
