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

/-!
# S3-15b (ticket T2263): the decay class of the alternating drift, `d ≥ 3`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: `int_K-L+Q` (`3_5:1337-1346`), `lem_+Q`
(`3_5:1284-1289`), `(A4)`, `(A5)` (`3_5:1692-1706`), `(eq:alternatecase2)` (`3_5:1711-1714`).
Pattern (not a port): RBM2D `Induction/AltEnd.lean:254-264` at `c9a24cf` (`hDcls` at `d = 2`:
the drift class at `u_j` moved to the index `j + 1` by `ellT_mono`).

The drift `dFlowQN = 𝒬_u(ℬ₁ + ℬ₂ + ℬ₃) + ℬ₄ + ℬ₅` of `Induction/QDriftA` is in the class `altClsQN`
of the merged `goodSetN_A0clsQN` (radius `ε'`, `δD = 4 W^{-D'}`):

* `drift13_fastDecay`: the block `ℬ₁ + ℬ₂ + ℬ₃` decays at a `GoodSetN` matrix (clause (Vb));
* `altB4N_fastDecay`: `ℬ₄ = Θ(𝒜 - 𝒬𝒜) - (Θ𝒜 - 𝒬Θ𝒜)` decays at every radius and depth from the
  crude sup of `𝒜 = (𝓛-𝒦)_{u,σ}(H)` alone (`stQop_sub_fastDecay`, `QopDecay_ThetaN_fastDecay`);
* `altB5N_fastDecay_moll`: `ℬ₅ = -(𝒫𝒜)_{a₁} ∂_uϑ` decays at every radius and depth for the explicit
  mollifier (`QopDecay_deriv_fastDecay`);
* `dFlowQN_clsQN`: `dFlowQN ∈ altClsQN … ε' Dc uu i (4 W^{-D'})` at a matrix;
* `alt_hDclsQN`: the field `hDcls` of `GridAssemblyHypN` along the walk at the explicit mollifier.

All statements are deterministic and level-free, per matrix or per grid time; `Γ Λ Φ` occur only
inside `GoodSetN` memberships.  Every unpinned helper is `private` or prefixed `QDriftB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. Copies of the private helpers of `QDriftA` (ticket target 1) -/

/-- A pair of indices realising `R ≤ diam_∞ b` gives the `ℓ¹` window `R ≤ zdistD (b i - b j)`.  A copy of
the private `QDriftA_window_of_diamInf` (`QDriftA.lean:389`, ticket T2250, `88ee6fd`). -/
private theorem QDriftB_window_of_diamInf {d L k : ℕ} (hk : 1 ≤ k) {R : ℝ} (b : Fin k → Zd d L)
    (hb : R ≤ (STdiamInf b : ℝ)) : ∃ i j : Fin k, R ≤ (zdistD d L (b i - b j) : ℝ) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
    Finset.univ_nonempty (fun p : Fin k × Fin k => zdistInf d L (b p.1 - b p.2))
  refine ⟨p.1, p.2, hb.trans ?_⟩
  have h1 : STdiamInf b = zdistInf d L (b p.1 - b p.2) := hp
  rw [h1]
  exact_mod_cast zdistInf_le_zdistD d L _

/-- The spec of `QDriftA_W0`.  A copy of the private `QDriftA_W0_spec` (`QDriftA.lean:409`, ticket T2250,
`88ee6fd`); it unfolds the merged `QDriftA_W0`. -/
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

/-! ## 3. Target 2: the block `ℬ₁ + ℬ₂ + ℬ₃` decays at a good matrix -/

/-- **Target 2** (`T2263_drift13_fastDecay`): the `ℬ₁ + ℬ₂ + ℬ₃` block `driftTensorN` decays in the `ℓ¹`
window of radius `ε'` at a `GoodSetN` matrix: clause (Vb) of `GoodSetN` (`driftTensorN_far_of_goodSet`,
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

/-! ## 4. Target 3: `ℬ₄` decays at every radius and depth from the crude sup alone -/

/-- **Target 3** (`T2263_altB4N_fastDecay`): `ℬ₄ = Θ(𝒜 - 𝒬𝒜) - (Θ𝒜 - 𝒬Θ𝒜)` (`QopAlgebra_ThetaN_sub`,
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

/-! ## 5. Target 4: `ℬ₅` decays at every radius and depth for the explicit mollifier -/

/-- **Target 4** (`T2263_altB5N_fastDecay_moll`): `ℬ₅ = (-𝒫𝒜)_{a₁} ∂_uϑ_{u,a}` for `ϑ = QopAlgebra_mollifier`
is `QopDecay_deriv_fastDecay` with `B = -𝒫𝒜`, `‖𝒫𝒜‖ ≤ ((2^d)^m + (L^d)^m) W^{C₀} ≤ W^{C₀+Km+1}`
(`B45_Psum_le`).  The merged `STMollifierProps` has no decay of `∂_uϑ` (clause 4 is the size only), so the
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

/-! ## 6. Target 5: the drift class at a matrix -/

/-- **Target 5** (`T2263_dFlowQN_clsQN`): `dFlowQN … u … H ∈ altClsQN … ε' Dc uu i (4 W^{-D'})` whenever
`ℓ_u ≤ ℓ_{uu i}` (the index shift of `hDcls`).  Sum-zero by `dFlowQN_sumZero`; on the `L^∞` window
`ℓ_{uu i} W^{ε'}` the `ℓ¹` window `W^{ε'} ℓ_u` is attained by a pair (`QDriftB_window_of_diamInf`);
`|𝒬_u(ℬ₁₋₃)| ≤ 2 W^{-D'}` (`drift13_fastDecay`, `QDriftB_W0_spec`), `|ℬ₄|, |ℬ₅| ≤ W^{-D'}` (hypotheses;
targets 3 and 4). -/
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

/-! ## 7. Target 6: the field `hDcls` of `GridAssemblyHypN` along the walk -/

/-- **Target 6** (`T2263_alt_hDclsQN`): the field `hDcls` of `GridAssemblyHypN` (`GridAssemblyN.lean:209`) for
the alternating chain at the explicit mollifier: `Cls = altClsQN … ε' Dc (gridTime s v Kg n)`,
`δD = 4 W^{-D'}`, `Dr j ω = dGridQN … j ω`, on `{j < Kg n, j < τ ω}`.  `dGridQN_eq_dFlowQN`; target 5 at
`u = u_j`, `uu = gridTime s v Kg n`, `i = j + 1` (`ℓ_{u_j} ≤ ℓ_{u_{j+1}}`: `ellT_mono`, `ST_gridTime_mono`,
`ST_gridTime_mem`); targets 3, 4 at `u = u_j` (`(1 - u_j)⁻¹ ≤ (1 - v_n)⁻¹ ≤ W^K`); the mollifier facts
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

/-! ## 8. Compiled nonempty instances (namespace `QDriftBInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) and the
T2250 data (`QDriftAInst`, `QDriftA.lean:649-1335`): `m = 3` (`k = 4`), `K = 2`, the explicit mollifier
`QopAlgebra_mollifier` (`C = (1 + 40·9)·6^9`, `c = 1/2`), `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `E = 0`, `u = 0`,
`H = 0 ∈ GoodSetN` at the levels `(Γ, Λ, Φ) = (4, 100, 1)`, at an `n` with `W_n` above the thresholds of the
targets.  The first part of the namespace copies the private numeric helpers of `QDriftAInst` (ticket T2250,
`88ee6fd`, `QDriftA.lean:715-806, 808-857, 864-869, 891-892, 1150-1209`, without `mE_zero_im_ge`). -/

namespace QDriftBInst

open RBM.Gauss.SizesInst RBM.Ind.GridDriftNCheck

private theorem rpow_pow5 {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y ^ 5) ^ r = y ^ (5 * r) := by
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]; norm_num

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem etaT_zero_zero : etaT 0 0 = 1 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

private theorem etaT_zero_half : etaT 0 (1 / 2) = 1 / 2 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧
      ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem lam_pos_n (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

private theorem L_ge_four (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  have h := (sz0_facts n).2.1
  have := Nat.cast_nonneg (α := ℝ) n
  rw [h]; linarith

/-- All the numeric hypotheses of the instances at `n` with `x = 2(n+1) ≥ 10`. -/
private theorem numeric (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    1 < ((sz0.W n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    Real.log ((sz0.L n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) ∧
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    (3 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ∧ (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
  obtain ⟨hW, hL, hlam⟩ := sz0_facts n
  set x : ℝ := 2 * ((n : ℝ) + 1) with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxW : ((sz0.W n : ℕ) : ℝ) = x ^ 5 := hW
  have h7 : (10 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
    rw [hxW]
    have : (10 : ℝ) ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    linarith
  have hW15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hs3 : (3 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  have hW110 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  refine ⟨by rw [hxW]; nlinarith [pow_le_pow_left₀ (by norm_num) hx 5], ?_, ?_, ?_, ?_, ?_, hW2⟩
  · rw [hW15]; linarith
  · rw [hW15, hL, Real.log_mul (by norm_num) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x by linarith)
    have h2 := Real.log_two_lt_d9
    linarith
  · rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * 2 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hL]
    have h10 : x ^ 10 = x ^ 3 * x ^ 7 := by ring
    have h8 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h7 (pow_nonneg hx0 3)]
  · rw [hW15, hW110]
    push_cast
    nlinarith
  · rw [hW110]; exact hs3

/-- `ℓ_0 = 1` for `g ≤ 1`. -/
private theorem ellT_zero_eq (L : ℕ) (hL : 1 ≤ L) {g : ℝ} (hg : g ≤ 1) : ellT L g 0 = 1 := by
  unfold ellT
  rw [sub_zero, abs_one, Real.sqrt_one, div_one, max_eq_right hg]
  exact min_eq_left (by exact_mod_cast hL)

private theorem ellT_sz0 (n : ℕ) : ellT (sz0.L n) (sz0.lam n) 0 = 1 :=
  ellT_zero_eq _ (by have := sz0.three_le_L n; omega) (lam_le_one n)

/-- The coordinate `x = L/2 = 2(n+1)` is at distance `2(n+1)` from `0` on `Z_{4(n+1)}`. -/
private theorem zdist_far (n : ℕ) :
    zdist (sz0.L n) (((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) = 2 * (n + 1) := by
  have hL : sz0.L n = 4 * (n + 1) := rfl
  have hv : (((2 * (n + 1) : ℕ) : ZMod (sz0.L n))).val = 2 * (n + 1) := by
    rw [ZMod.val_natCast, hL]
    exact Nat.mod_eq_of_lt (by omega)
  unfold zdist
  rw [hv, hL]
  omega

/-- The far point `(x, x, x)`. -/
private def farv (n : ℕ) : Zd 3 (sz0.L n) := fun _ => (((2 * (n + 1) : ℕ) : ZMod (sz0.L n)))

private theorem zdistD_farv (n : ℕ) : zdistD 3 (sz0.L n) (farv n) = 3 * (2 * (n + 1)) := by
  unfold zdistD farv
  simp only [zdist_far, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem zdistInf_farv (n : ℕ) : zdistInf 3 (sz0.L n) (farv n) = 2 * (n + 1) := by
  unfold zdistInf farv
  simp only [zdist_far]
  rw [Finset.sup_const (Finset.univ_nonempty)]

/-- The far tuple `(0, x⃗, 0, 0)`. -/
private def farb (n : ℕ) : Fin (3 + 1) → Zd 3 (sz0.L n) := ![0, farv n, 0, 0]

/-- The `ℓ¹` window is attained: a tuple of `ℓ¹`-spread `3x ≥ x ≥ w ℓ_0`. -/
private theorem window_l1 (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j,
      w * ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ) := by
  refine ⟨farb n, 1, 0, ?_⟩
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistD_farv, ellT_sz0]
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The `L^∞` window is attained: `diam_∞ (farb n) ≥ x ≥ ℓ_0 w`. -/
private theorem window_linf (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * w ≤ (STdiamInf b : ℝ) := by
  refine ⟨farb n, ?_⟩
  have h := Finset.le_sup (f := fun q : Fin (3 + 1) × Fin (3 + 1) =>
      zdistInf 3 (sz0.L n) (farb n q.1 - farb n q.2)) (Finset.mem_univ ((1 : Fin (3 + 1)), (0 : Fin (3 + 1))))
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistInf_farv] at h
  have h2 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf (farb n) : ℝ) := by exact_mod_cast h
  rw [ellT_sz0]
  push_cast at h2
  linarith

/-- `W^{x} ≤ x'` for `x ≤ 1/5`: the exponents of the instances are at most `1/5`, and `W^{1/5} = x`. -/
private theorem W_rpow_fifth (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := by
  have hx0 : 0 ≤ 2 * ((n : ℝ) + 1) := by linarith
  rw [(sz0_facts n).1, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]


/-- The constants of the mollifier of `QopAlgebra_mollifier_props` at `d = 3`, `m = 3`. -/
private noncomputable abbrev Cmol3 : ℝ := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)

/-- `0 ∈ GoodSetN` at `E = 0`, `u = 0`, `k = 4` with the levels `(Γ, Λ, Φ) = (4, 100, 1)`
(`Γ² Λ = 1600 ≥ 4 · 2^8`), every `τ'`, `D'`. -/
private theorem zero_mem_inst (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 τ' D' := by
  refine zero_mem_goodSetN_of_levels sz0 n (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  have h1 : (1 + sz0.lam n ^ 2) ≤ 2 := by nlinarith [sq_nonneg (sz0.lam n), lam_pos_n n]
  have h2 : (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 2 ^ (2 * (3 + 1)) :=
    pow_le_pow_left₀ (by positivity) h1 _
  push_cast
  calc 4 * (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 4 * 2 ^ (2 * (3 + 1)) := by gcongr
    _ ≤ 4 * (4 * 100) := by norm_num

/-- **The crude sup** `‖(𝓛-𝒦)_{0,σ}(0)‖ ≤ W^7` at `E = 0`, `u = 0`, `M = 0`, `k = 4`, from the eventual bound of
`exists_norm_Kcal_le_win` on `𝒦` and `norm_loopFine_crudeN` (`≤ 1 + 16 N ≤ 1 + 16 W^6`, `N = (W L)^3 ≤ W^6`,
`W ≥ 17`). -/
private theorem crude_sup (n : ℕ) (hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ))
    (hn1 : ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 4 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4)
    (σ : Fin (3 + 1) → Bool) :
    ‖fun a => sz0.STLKM n 0 0 0 σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have e : sz0.STLKM n 0 0 0 σ a =
      loopFine 3 (sz0.L n) (sz0.W n) (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n))
        (Idx 3 (sz0.L n) (sz0.W n)) ℂ) (zt 0 0) σ a - sz0.STKloop n 0 0 σ a := rfl
  rw [e]
  have h1 := norm_loopFine_crudeN sz0 n (E := 0) (by norm_num) Matrix.isHermitian_zero (u := 0)
    (by norm_num) (ℓ := 4) (by norm_num) σ a
  rw [etaT_zero_zero, inv_one, one_pow] at h1
  have hJ : sz0.STKloop n 0 0 σ a = KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) 0 (loopOf σ a) := rfl
  have h2 := hn1 0 ⟨le_rfl, by norm_num⟩ (loopOf σ a) (by simp [LoopIdx.WF, loopOf])
    (by simp [LoopIdx.length, loopOf]) (by simp [LoopIdx.length, loopOf])
  have hη : etaT (E0 n) 0 = 1 := etaT_zero_zero
  have hη' : etaT (E0 n) (1 / 2) = 1 / 2 := etaT_zero_half
  simp only [hη', Real.rpow_one] at h2
  have hsize : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by exact_mod_cast sz0_size_le_W_pow n
  rw [hJ]
  have h3 : ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) 0 (loopOf σ a)‖ ≤
      16 * ((sz0.W n : ℕ) : ℝ) ^ 6 := by
    refine h2.trans ?_
    have : ((1 / 2 : ℝ)⁻¹) ^ 4 = 16 := by norm_num
    rw [this]
    nlinarith [hsize]
  have h4 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4]
  have h5 : (17 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ 6 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    have : ((sz0.W n : ℕ) : ℝ) ^ 7 = ((sz0.W n : ℕ) : ℝ) ^ 6 * ((sz0.W n : ℕ) : ℝ) := by ring
    rw [this]
    nlinarith [pow_pos hWpos 6]
  have h6 : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := one_le_pow₀ (by linarith)
  calc _ ≤ ‖loopFine 3 (sz0.L n) (sz0.W n) (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n))
        (Idx 3 (sz0.L n) (sz0.W n)) ℂ) (zt 0 0) σ a‖ +
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) 0 (loopOf σ a)‖ := norm_sub_le _ _
    _ ≤ 1 + 16 * ((sz0.W n : ℕ) : ℝ) ^ 6 := add_le_add h1 h3
    _ ≤ _ := by linarith

/-- `ℓ_t = 1` for `0 ≤ t ≤ 1/2` and `g ≤ 1/2` (so `g/√|1-t| ≤ 2g ≤ 1`). -/
private theorem ellT_eq_one {L : ℕ} (hL : 1 ≤ L) {g t : ℝ} (hg : g ≤ 1 / 2) (hg0 : 0 ≤ g) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) : ellT L g t = 1 := by
  unfold ellT
  have h1 : (1 / 2 : ℝ) ≤ |1 - t| := by rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : (1 / 2 : ℝ) ≤ Real.sqrt |1 - t| := by
    refine (Real.le_sqrt' (by norm_num)).2 ?_
    nlinarith
  have h3 : g / Real.sqrt |1 - t| ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  rw [max_eq_right h3]
  exact min_eq_left (by exact_mod_cast hL)

/-- The crude sup of the block `ℬ₁ + ℬ₂ + ℬ₃` at `H = 0`, `E = 0`, `u = 0`, `k = 4`: from `0 ∈ GoodSetN` with the
levels `(4, 100, 1)`, `driftTensorN_norm_le_of_goodSet` gives `‖Dr‖ ≤ 4·4·(B^4/η)·(3 + 4·4) = 304 B^4`,
`η = 1`, `B = W^{-3} B_{0,0} ≤ 2`, so `‖Dr‖ ≤ 4864 ≤ 17^7 ≤ W^7`. -/
private theorem crude_block (n : ℕ) (hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) (σ : Fin (3 + 1) → Bool) :
    ‖fun a => driftTensorN sz0 n 0 0 (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)
        σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  have hL4 := L_ge_four n
  have hBpar0 : 0 ≤ Bparam 3 (sz0.L n) (sz0.lam n) 0 0 := by unfold Bparam; positivity
  have hBpar : Bparam 3 (sz0.L n) (sz0.lam n) 0 0 ≤ 2 := by
    unfold Bparam
    have h1 : ((sz0.lam n) ^ 2 + |1 - (0 : ℝ)|)⁻¹ ≤ 1 := by
      rw [sub_zero, abs_one]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (sz0.lam n)])
    have h3 : (((sz0.L n : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ≤ 1 := by
      rw [sub_zero, abs_one, mul_one]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    have h2 : (((((0 : ℕ) : ℝ)) + 1) ^ (3 - 2)) ⁻¹ = 1 := by norm_num
    rw [h2, mul_one]
    linarith
  have hW3 : ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hB0 : 0 ≤ sz0.Bctl n 0 := by unfold Sizes.Bctl; positivity
  have hB : sz0.Bctl n 0 ≤ 2 := by
    unfold Sizes.Bctl
    calc ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) * Bparam 3 (sz0.L n) (sz0.lam n) 0 0
        ≤ 1 * 2 := mul_le_mul hW3 hBpar hBpar0 zero_le_one
      _ = 2 := by norm_num
  have hB4 : (sz0.Bctl n 0) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hB0 hB 4
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun a => ?_
  have h := driftTensorN_norm_le_of_goodSet sz0 (n := n) (E := 0) (u := 0) (Γ := 4) (Λ := 100) (Φ := 1)
    (τ' := 1 / 10) (D' := 3) (k := 4) (by norm_num) (zero_mem_inst n (lam_le_one n) _ _) σ a
  rw [etaT_zero_zero] at h
  have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h7]
  have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hW17 7
  refine h.trans ?_
  push_cast
  nlinarith [hB4, h17]

/-- A large `n`: `max W₁ 17 ≤ x = 2(n+1)`, and the crude sup `‖(𝓛-𝒦)_{0,σ}(0)‖ ≤ W^7` for every `σ` (the proof
of `QDriftAInst.goodSetN_A0clsQN_instance`, `QDriftA.lean:1229-1261`, with the proved `stKbound_holds`). -/
private theorem inst_data (W₁ : ℝ) :
    ∃ n : ℕ, max W₁ 17 ≤ 2 * ((n : ℝ) + 1) ∧ ∀ σ : Fin (3 + 1) → Bool,
      ‖fun a => sz0.STLKM n 0 0 0 σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  have hKev := exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 4 1 one_pos
  obtain ⟨n, hn1, hn2⟩ := (hKev.and (Filter.eventually_ge_atTop ⌈max W₁ 17⌉₊)).exists
  have hn : max W₁ 17 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  have hx : max W₁ 17 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hxW : 2 * ((n : ℝ) + 1) ≤ ((sz0.W n : ℕ) : ℝ) := by
    rw [(sz0_facts n).1]
    exact le_self_pow₀ (by linarith) (by norm_num)
  exact ⟨n, hx, fun σ => crude_sup n (hx17.trans hxW) hn1 σ⟩

/-- `x = 2(n+1) ≤ W_n` and `W_n ≥ 17`, from `max W₁ 17 ≤ x`. -/
private theorem x_le_W (n : ℕ) (hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1)) :
    2 * ((n : ℝ) + 1) ≤ ((sz0.W n : ℕ) : ℝ) := by
  rw [(sz0_facts n).1]
  exact le_self_pow₀ (by linarith) (by norm_num)

/-- `4 W^{-6} ≤ W^{-3}` for `W ≥ 4` (`D' = 6`, `Dc = 3`). -/
private theorem hDD_inst {W : ℝ} (hW : 4 ≤ W) : 4 * W ^ (-(6 : ℝ)) ≤ W ^ (-(3 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have h : W ^ (-(6 : ℝ)) = W ^ (-(3 : ℝ)) * W ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hW0]; norm_num
  have h3 : W ^ (-(3 : ℝ)) ≤ 4⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hW 3])
  have h2 : 0 ≤ W ^ (-(3 : ℝ)) := Real.rpow_nonneg hW0.le _
  rw [h]
  nlinarith

/-! ### The instances -/

/-- **Instance of target 2** (`drift13_fastDecay`): `d = 3`, `m = 3` (`k = 4`), `E = 0`, `u = 0`, `H = 0 ∈ GoodSetN`
at the levels `(Γ, Λ, Φ) = (4, 100, 1)`, `τ' = 1/10`, `D' = 6`, `ε' = 1/5`, `n = 9` (`x = 20`: `3 W^{1/10} ≤ W^{1/5}`),
every `σ`: the block decays in the `ℓ¹` window, which is attained by a tuple (not vacuous). -/
theorem drift13_fastDecay_instance :
    ∃ n : ℕ,
      (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
        sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) 6 ∧
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j,
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤
          (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧
      ∀ σ : Fin (3 + 1) → Bool,
        EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 6
          (fun b : Fin (3 + 1) → Zd 3 (sz0.L n) =>
            driftTensorN sz0 n 0 0 (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)
              σ b) := by
  have hx10 : (10 : ℝ) ≤ 2 * (((9 : ℕ) : ℝ) + 1) := by norm_num
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 9 hx10
  refine ⟨9, zero_mem_inst 9 (lam_le_one 9) _ _, window_l1 9 (W_rpow_fifth 9 hx10).le, fun σ => ?_⟩
  exact drift13_fastDecay sz0 (le_refl 3) (m := 3) (n := 9) (E := 0) (u := 0) (Γ := 4) (Λ := 100) (Φ := 1)
    (τ' := 1 / 10) (ε' := 1 / 5) (D' := 6) σ hdW (zero_mem_inst 9 (lam_le_one 9) _ _)

/-- **Instance of target 3** (`altB4N_fastDecay`): `d = 3`, `m = 3`, `Λ_g = 1`, `K = 2`, the explicit mollifier
(`C = (1 + 40·9)·6^9`, `c = 1/2`), `C₀ = 7`, `ε' = 1/5`, `D' = 6`, `E = 0`, `u = 0`, `H = 0`, every `σ`, at an `n`
with `W_n ≥ W₀`; the crude sup `‖(𝓛-𝒦)_{0,σ}(0)‖ ≤ W^7` is derived (no hypothesis is left open). -/
theorem altB4N_fastDecay_instance :
    ∃ n : ℕ,
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j,
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤
          (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧
      ∀ σ : Fin (3 + 1) → Bool,
        EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 6
          (altB4N sz0 n 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ
            (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)) := by
  obtain ⟨W₀, hW₀, H⟩ := altB4N_fastDecay 3 3 1 2 Cmol3 (1 / 2) 7 (1 / 5) 6 (le_refl 3) one_pos
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨n, hx, hcr⟩ := inst_data W₀
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans (x_le_W n hx17)
  refine ⟨n, window_l1 n (W_rpow_fifth n hx10).le, fun σ => ?_⟩
  exact H sz0 n 0 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ (by norm_num) (lam_pos_n n)
    (lam_le_one n) hW0W hLK le_rfl (by norm_num)
    (by rw [sub_zero, inv_one]; exact Real.one_le_rpow hW.le (by norm_num))
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) (hcr σ)

/-- **Instance of target 4** (`altB5N_fastDecay_moll`): the same data. -/
theorem altB5N_fastDecay_moll_instance :
    ∃ n : ℕ,
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j,
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤
          (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧
      ∀ σ : Fin (3 + 1) → Bool,
        EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 6
          (altB5N sz0 n 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ
            (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)) := by
  obtain ⟨W₀, hW₀, H⟩ := altB5N_fastDecay_moll 3 3 2 7 (1 / 5) 6 (by norm_num)
  obtain ⟨n, hx, hcr⟩ := inst_data W₀
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans (x_le_W n hx17)
  refine ⟨n, window_l1 n (W_rpow_fifth n hx10).le, fun σ => ?_⟩
  exact H sz0 n 0 0 0 σ (lam_pos_n n) hW0W hLK le_rfl (by norm_num)
    (by rw [sub_zero, inv_one]; exact Real.one_le_rpow hW.le (by norm_num)) (hcr σ)

/-- **Instance of target 5** (`dFlowQN_clsQN`): `d = 3`, `m = 3`, `K = 2`, the explicit mollifier, `C₀ = 7`,
`ε' = 1/5`, `τ' = 1/10`, `D' = 6`, `Dc = 3`, `E = 0`, `u = 0`, `uu ≡ 0`, `i = 1`, `H = 0 ∈ GoodSetN` at the
levels `(4, 100, 1)`, every `σ` (alternating and not), at an `n` with `W_n ≥ W₀`: every hypothesis is discharged
(the two crude sups from `stKbound_holds`/`norm_loopFine_crudeN` and from `driftTensorN_norm_le_of_goodSet`; the
decays of `ℬ₄`, `ℬ₅` from targets 3 and 4).  The `L^∞` window `ℓ_0 W^{ε'}` is attained by a tuple. -/
theorem dFlowQN_clsQN_instance :
    ∃ n : ℕ,
      (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
        sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) 6 ∧
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
      ∀ σ : Fin (3 + 1) → Bool,
        altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (fun _ => 0) 1
          (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
          (dFlowQN sz0 n 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ
            (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)) := by
  obtain ⟨W₃, hW₃, H₃⟩ := altB4N_fastDecay 3 3 1 2 Cmol3 (1 / 2) 7 (1 / 5) 6 (le_refl 3) one_pos
    (by positivity) (by norm_num) (by norm_num)
  obtain ⟨W₄, hW₄, H₄⟩ := altB5N_fastDecay_moll 3 3 2 7 (1 / 5) 6 (by norm_num)
  set WQ : ℝ := QDriftA_W0 3 3 2 Cmol3 (1 / 2) 7 (1 / 5) 6 with hWQ
  obtain ⟨n, hx, hcr⟩ := inst_data (max WQ (max W₃ W₄))
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hWQ' : WQ ≤ ((sz0.W n : ℕ) : ℝ) :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans hx).trans hxW
  have hW3' : W₃ ≤ ((sz0.W n : ℕ) : ℝ) :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx).trans hxW
  have hW4' : W₄ ≤ ((sz0.W n : ℕ) : ℝ) :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx).trans hxW
  have hWx : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := W_rpow_fifth n hx10
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hϑ := QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)
  have hone : (1 - (0 : ℝ))⁻¹ ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [sub_zero, inv_one]; exact Real.one_le_rpow hW.le (by norm_num)
  refine ⟨n, zero_mem_inst n (lam_le_one n) _ _, ?_, fun σ => ?_⟩
  · obtain ⟨b, hb⟩ := window_linf n (w := ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ)) hWx.le
    exact ⟨b, hb⟩
  · exact dFlowQN_clsQN sz0 (le_refl 3) 3 2 Cmol3 (1 / 2) 7 (1 / 5) 6 (by positivity) (by norm_num)
      (by norm_num) (n := n) (E := 0) (u := 0) (Γ := 4) (Λ := 100) (Φ := 1) (τ' := 1 / 10) (Dc := 3)
      (uu := fun _ => 0) (i := 1) hWQ' hLK hdW (hDD_inst (by linarith)) (by norm_num) (lam_pos_n n) le_rfl
      (by norm_num) le_rfl (zero_mem_inst n (lam_le_one n) _ _)
      (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) hϑ
      (fun a => QopAlgebra_mollifier_differentiableAt 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)
        (by norm_num) a) σ (crude_block n hW17 σ)
      (H₃ sz0 n 0 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ (by norm_num) (lam_pos_n n)
        (lam_le_one n) hW3' hLK le_rfl (by norm_num) hone hϑ (hcr σ))
      (H₄ sz0 n 0 0 0 σ (lam_pos_n n) hW4' hLK le_rfl (by norm_num) hone (hcr σ))

/-- **Instance of target 6** (`alt_hDclsQN`) on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4` (so `H_0 = 0`,
`u_0 = 0`, `u_1 = 1/8`), the stopping time `τ ≡ 1` (`0 < τ`, and `H_0 ∈ GoodSetN` for `j < τ`), levels `(4, 100, 1)`,
the explicit mollifier, `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 6`, `Dc = 3`, `Λ_g = 1`, `K = 2`, every `σ` (no
hypothesis on `σ`) and every path `ω`, at `j = 0`: the drift `dGridQN … 0 ω` is in the class `altClsQN … (0 + 1)` with
`δD = 4 W^{-6}`; every hypothesis is discharged.  The `L^∞` window `ℓ_{u_1} W^{ε'}` is attained by a tuple. -/
theorem alt_hDclsQN_instance :
    ∃ n : ℕ,
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n)
        (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (0 + 1)) *
          ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
      ∀ (σ : Fin (3 + 1) → Bool) (ω : PathΩ sz0),
        altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3
          (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n) (0 + 1)
          (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
          (dGridQN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n
            (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ 0 ω) := by
  obtain ⟨W₀, hW₀, H⟩ := alt_hDclsQN 3 3 1 2 7 (1 / 5) 6 (le_refl 3) one_pos (by norm_num)
  obtain ⟨n, hx, hcr⟩ := inst_data W₀
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hWx : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := W_rpow_fifth n hx10
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hlam1 := lam_le_one n
  have hg12 : sz0.lam n ≤ 1 / 2 := by
    have h : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := (sz0_facts n).2.2
    rw [h]
    have h6 : (10 : ℝ) ^ 6 ≤ (2 * ((n : ℝ) + 1)) ^ 6 := pow_le_pow_left₀ (by norm_num) hx10 6
    calc ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ ((10 : ℝ) ^ 6)⁻¹ := inv_anti₀ (by norm_num) h6
      _ ≤ 1 / 2 := by norm_num
  have hu1 : gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (0 + 1) = 1 / 8 := by
    simp only [gridTime, gridStep]
    norm_num
  refine ⟨n, ?_, fun σ ω => ?_⟩
  · rw [hu1, ellT_eq_one (by have := sz0.three_le_L n; omega) hg12 (lam_pos_n n).le (by norm_num)
      (by norm_num), one_mul, hWx]
    obtain ⟨b, hb⟩ := window_linf n (w := ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ)) hWx.le
    rw [ellT_sz0, one_mul, hWx] at hb
    exact ⟨b, hb⟩
  · have hp0 := azumaProxy_pathH_zero_of_s_zero sz0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n
      rfl ω
    refine H sz0 n σ (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (1 / 10) 3 (fun _ => 1) (by norm_num) (lam_pos_n n)
      hlam1 hW0W hLK le_rfl (by norm_num) (by norm_num)
      (by
        show (1 - (1 / 2 : ℝ))⁻¹ ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ)
        have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
        rw [h2, Real.rpow_two]
        nlinarith)
      hdW (hDD_inst (by linarith)) ?_ ?_ ?_ ω 0 (by norm_num) (by norm_num)
    · intro ω' j hj
      have hj0 : j = 0 := by
        have : j < 1 := hj
        omega
      subst hj0
      rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ n rfl ω', ST_gridTime_zero]
      exact zero_mem_inst n hlam1 _ _
    · intro ω' j hj hjτ
      have hj0 : j = 0 := by
        have : j < 1 := hjτ
        omega
      subst hj0
      rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ n rfl ω', ST_gridTime_zero]
      exact hcr σ
    · intro ω' j hj hjτ
      have hj0 : j = 0 := by
        have : j < 1 := hjτ
        omega
      subst hj0
      rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ n rfl ω', ST_gridTime_zero]
      exact crude_block n hW17 σ

end QDriftBInst

end RBM.Ind

end
