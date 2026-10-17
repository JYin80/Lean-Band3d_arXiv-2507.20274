/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.GridRepTailGen
import RBM3D.Induction.NQGood1

/-!
# The non-alternating good-set inputs, first half, over the carrier (U3s2a, file 1; ticket T2491)

Generic forms of `Induction/NQGood1.lean` (not edited) over a carrier `Cm : Step2Mat sz` and the kernel `Step2Gen_UN`
of T8b, namespace `RBM.BA`, no `BA/*` import.  Paper: arXiv:2507.20274, `lem:STOeq_NQ` (`3_5:1136`, proof `3_5:1152`),
`(sum_res_2_NAL)` of `lem:sum_decay` (`3_5:1632`).

* **Target 1 (D1)** `NQGoodGen_KerNAL`, `NQGoodGen_KerNALFam`: the deterministic `(sum_res_2_NAL)` (EK-6) for the carrier kernel at the kernel
  coupling `gK`, with an explicit constant `Ck` (the band constant `nqGood1C` is a `Classical.choose`); band discharges
  `nqGoodGen_kerNAL_band_at`, `nqGoodGen_kerNAL_band` (`Ck = nqGood1C d k 𝔡⁻¹ (min κ (4/5))`).  BA: `baEKSumDecayNAL_holds`
  at `gK = BAflowLam0` (U3-BA).
* **Target 2** `driftTensorNg` with `driftTensorNg_norm_le_of_goodSetNg`, `driftTensorNg_far_of_goodSetNg`; `hker_of_case1Ng`
  (band `hker_of_case1N`, `NQGood1:310`): D1 at `gK` and the comparison R1 (`gK² ≤ lam² ≤ A gK²`, UBA-C1) give the bound with the weight at
  `sz.lam`; the QV majorant `qvFormNg_le_of_goodSetNg` (band `NQGood1:551`; `qvFormNg` is `Re STeeUMg`, so no conjugation is
  needed; the row sums are the K2 of `GridRepTailGen_Ker`).
* **Target 3** the shift layer `u_j → u_{j+1}` (band `NQGood1:578-1053`) under `StepDecompGen_LoopForm` and `‖Cm.m n‖ ≤ 1` (D3):
  `etaT_inv_shiftNg_le`, `loopFine_shiftNg_le`, `STXiLMg_shiftNg_le`, `goodSetNg_dec_shiftNg`, the crude envelopes, `eeShiftErrNg`,
  `norm_STeeMg_shiftNg_le`.  `loopShiftErrN`, `norm_loopL_zshiftN_le`, `loopMax_zshiftN_le`, `nqGood1_ellT_mono` are model-free and
  used by name.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1 (D1): the kernel class of `hker` -/

/-- **D1, `NQGoodGen_KerNAL`**: the deterministic `(sum_res_2_NAL)` (EK-6) for the carrier kernel `Step2Gen_UN C` at the kernel
coupling `gK`, index `n`, explicit constant `Ck` (band `hker_of_case1N`'s input `ekSumDecayNAL_holds`, `NQGood1.lean:310`; BA
`BAEKSumDecayNAL`, `BA/EKPins.lean:113`). -/
def NQGoodGen_KerNAL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (Ck : ℝ) (n : ℕ) : Prop :=
  1 < ((sz.W n : ℕ) : ℝ) →
  ∀ ε D : ℝ, 0 < ε → ε < 1 → 1 < D → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 →
      (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ σ : Fin k → Bool, (∃ i, σ i = σ (finRotate k i)) →
      ∀ A : (Fin k → Zd d (sz.L n)) → ℂ, EKFastDecay (gK n) s ((sz.W n : ℕ) : ℝ) ε D A →
        ‖Step2Gen_UN C n σ s t A‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((gK n ^ 2 + |1 - s|) / (gK n ^ 2 + |1 - t|)) ^ (k - 1) * ‖A‖ +
            ((sz.W n : ℕ) : ℝ) ^ (-D + Ck)

/-- **D1, the family form** (guarded; `∃ Ck` after `(k, κ, ε, 𝔡)` and before `(sz, z)`: U5S-C3, no F1 case). Band `gK = sz.lam`; BA
`gK = BAflowLam0 sz z` (U3-BA (a), from `baEKSumDecayNAL_holds`). -/
def NQGoodGen_KerNALFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Ck : ℝ, 0 < Ck ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, NQGoodGen_KerNAL (mk sz z) (gK sz z) k Ck n

section D1Band

open RBM.Ind

/-- D1 at one index, band: `Step2Gen_UN (bandFM sz E)` is `Ugen` (`bandStep2_Ugen`); the class is `ekSumDecayNAL_holds` with the
band constant `nqGood1C` (`NQGood1:261`). -/
theorem nqGoodGen_kerNAL_band_at {d k : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) {Λ κ' : ℝ} (hΛ : 0 < Λ)
    (hκ' : 0 < κ') (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ) (hE : |E n| ≤ 2) (hκm : κ' ≤ (mE (E n)).im) :
    NQGoodGen_KerNAL (bandFM sz E) sz.lam k (nqGood1C d k Λ κ') n := by
  intro hW ε D hε0 hε1 hD hWε s t hs hst ht hWt σ hσ A hA
  have hCdef : nqGood1C d k Λ κ' = Classical.choose (ekSumDecayNAL_holds d k Λ κ' (prop5Decay_holds d Λ)
      (prop5Short_holds d Λ κ') hd hk hΛ hκ') := by
    unfold nqGood1C; rw [dite_eq_left_of_eq_true (eq_true ⟨hd, hk, hΛ, hκ'⟩)]
  obtain ⟨-, hEK⟩ := Classical.choose_spec (ekSumDecayNAL_holds d k Λ κ' (prop5Decay_holds d Λ)
    (prop5Short_holds d Λ κ') hd hk hΛ hκ')
  rw [hCdef, ← bandStep2_Ugen]
  exact hEK (sz.L n) (sz.three_le_L n) (sz.lam n) hg hgΛ _ ε D hW hε0 hε1 hD hWε s t hs hst ht hWt (mE (E n)) (norm_mE hE) hκm σ hσ A hA

end D1Band


/-! ## 2. Target 2: the drift tensor and its compositions with `GoodSetNg` -/

section Drift

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- The drift tensor of the stopped hierarchy at a grid time (band `driftTensorN`, `NQGood1:95`; the sum of `GridDriftNg`'s inline
form): `Σ_{l=3}^k STksimLKMg_l + STelklkMg + STegtMg`. -/
def driftTensorNg (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l (loopOf σ a) + STelklkMg Cm n u H (loopOf σ a) + STegtMg Cm n u H (loopOf σ a)

variable {Cm}

/-- **The drift far decay on the good set** (band `driftTensorN_far_of_goodSet`, `NQGood1:133`; clause (Va)): `‖Dr(σ,a)‖ ≤ W^{-D'}`
when `ℓ_u W^{τ'} ≤ diam_∞ a`. -/
theorem driftTensorNg_far_of_goodSetNg {n : ℕ} {u Γ Λ Φ τ' D' : ℝ} {k : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : GoodSetNg Cm n u k Γ Λ Φ τ' D' M) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (hfar : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)) :
    ‖driftTensorNg Cm n u M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  obtain ⟨-, -, -, -, -, -, -, hVa, -⟩ := hM
  have h := hVa σ a hfar
  unfold driftTensorNg
  exact (norm_add₃_le).trans h

end Drift

/-! ## 3. Target 2: `hker_of_case1Ng`, D1 at `gK` and the comparison R1 -/

section Hker

/-- **`hker` in the non-alternating case over a carrier** (band `hker_of_case1N`, `NQGood1:310`; UBA-C1): `hKer` is D1 at the kernel
coupling `gK` and the constant `Ck`, `hcmp` the comparison R1 (`gK² ≤ lam² ≤ A gK²`), `Cv ≥ Ck` the constant of the vocabulary with
`A^{k-1} ≤ W^{(Cv-Ck)ε}` and `d √A W^{τ'} ≤ W^ε` (the two crossings where R1 enters, besides the kernel window, which is read off `hcmp`
inline, and the ratio and `ℓ` comparisons `step34Gen_ratio_pow_le`, `step34Gen_ellT_ge`).  Band: `gK = lam`, `A = 1`, `Cv = Ck`, where `hdW`, `hAk` are the band's `hdW` and
`1 ≤ W^0`.  The bound has the weight at `sz.lam`. -/
theorem hker_of_case1Ng {d k : ℕ} {sz : Sizes d} (C : FlowFM sz) {gK : ℕ → ℝ} {A Ck Cv : ℝ} (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : NQGoodGen_KerNAL C gK k Ck n) (hCv : Ck ≤ Cv) {ε τ' D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hD : 1 < D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s))
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (X : (Fin k → Zd d (sz.L n)) → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hδD : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) (hXM : ∀ b, ‖X b‖ ≤ M)
    (hXcls : ∀ b : Fin k → Zd d (sz.L n), ellT (sz.L n) (sz.lam n) s * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ)
    (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ s t X a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1) * M +
      ((sz.W n : ℕ) : ℝ) ^ Cv * δ := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have hL2 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := pow_pos (by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)) 2
  have ht1 : t < 1 := by
    rcases div_pos_iff.1 (lt_of_lt_of_le (inv_pos.2 hW0) hWt) with ⟨h, -⟩ | ⟨h, -⟩
    · linarith
    · linarith [div_nonneg (sq_nonneg (sz.lam n)) hL2.le]
  have hwin : t ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    linarith [div_le_div_of_nonneg_right (hcmp n).2.1 hL2.le]
  have hX : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr hXM
  have hrat := step34Gen_ratio_pow_le hcmp hA n (v := s) ht1 (k - 1)
  have hell := step34Gen_ellT_ge hcmp hA n s
  have hfast : ∀ D'', δ ≤ W ^ (-D'') → EKFastDecay (gK n) s W ε D'' X := by
    intro D'' hD'' a' ⟨i, j, hij⟩
    refine (hXcls a' ?_).trans hD''
    have hdist : (zdistD d (sz.L n) (a' i - a' j) : ℝ) ≤ d * (STdiamInf a' : ℝ) := by
      have h3 : zdistInf d (sz.L n) (a' i - a' j) ≤ STdiamInf a' :=
        Finset.le_sup (f := fun p : Fin k × Fin k => zdistInf d (sz.L n) (a' p.1 - a' p.2)) (Finset.mem_univ (i, j))
      exact_mod_cast (zdistD_le_mul_zdistInf d (sz.L n) (a' i - a' j)).trans (Nat.mul_le_mul_left d h3)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hE0 : 0 ≤ ellT (sz.L n) (gK n) s := le_min (le_trans zero_le_one (le_max_right _ _)) (Nat.cast_nonneg _)
    refine le_of_mul_le_mul_left (a := (d : ℝ)) ?_ hd0
    calc (d : ℝ) * (ellT (sz.L n) (sz.lam n) s * W ^ τ')
        ≤ (d : ℝ) * (Real.sqrt A * ellT (sz.L n) (gK n) s * W ^ τ') :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hell (Real.rpow_nonneg hW0.le _)) hd0.le
      _ = ellT (sz.L n) (gK n) s * ((d : ℝ) * Real.sqrt A * W ^ τ') := by ring
      _ ≤ ellT (sz.L n) (gK n) s * W ^ ε := mul_le_mul_of_nonneg_left hdW hE0
      _ = W ^ ε * ellT (sz.L n) (gK n) s := mul_comm _ _
      _ ≤ _ := hij
      _ ≤ _ := hdist
  have hat : ∀ D'' : ℝ, 1 < D'' → δ ≤ W ^ (-D'') → ‖Step2Gen_UN C n σ s t X a‖ ≤
      W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1) * M + W ^ (-D'' + Cv) := by
    intro D'' hD'' hδ''
    have h := hKer hW ε D'' hε0 hε1 hD'' hWε s t hs hst hwin hWt σ hσ X (hfast D'' hδ'')
    have e0 : W ^ (Ck * ε) * W ^ ((Cv - Ck) * ε) = W ^ (Cv * ε) := by rw [← Real.rpow_add hW0]; ring_nf
    have e1 : W ^ (Ck * ε) * ((gK n ^ 2 + |1 - s|) / (gK n ^ 2 + |1 - t|)) ^ (k - 1) * ‖X‖ ≤
        W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1) * M := by
      calc _ ≤ W ^ (Ck * ε) * (A ^ (k - 1) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1)) * M := by gcongr
        _ ≤ W ^ (Ck * ε) * (W ^ ((Cv - Ck) * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1)) * M := by gcongr
        _ = _ := by rw [← e0]; ring
    have e2 : W ^ (-D'' + Ck) ≤ W ^ (-D'' + Cv) := Real.rpow_le_rpow_of_exponent_le hW.le (by linarith)
    exact (norm_le_pi_norm (Step2Gen_UN C n σ s t X) a).trans (h.trans (by linarith))
  rcases hδ.eq_or_lt with h0 | hpos
  · subst h0
    rw [mul_zero, add_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hD1 : 1 < max 2 (Cv - Real.logb W η) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h1 := hat _ hD1 (Real.rpow_nonneg hW0.le _)
    have h2 : W ^ (-max 2 (Cv - Real.logb W η) + Cv) ≤ η :=
      calc _ ≤ W ^ (Real.logb W η) := Real.rpow_le_rpow_of_exponent_le hW.le (by linarith [le_max_right 2 (Cv - Real.logb W η)])
        _ = η := Real.rpow_logb hW0 hW.ne' hη
    linarith
  · have hWD : W ^ (-(-Real.logb W δ)) = δ := by rw [neg_neg]; exact Real.rpow_logb hW0 hW.ne' hpos
    have hDle : D ≤ -Real.logb W δ := by linarith [(Real.logb_le_iff_le_rpow hW hpos).2 hδD]
    have h1 := hat (-Real.logb W δ) (by linarith) hWD.symm.le
    rw [Real.rpow_add hW0, hWD] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring

end Hker


/-! ## 4. Target 2: the quadratic-variation majorant of `qvFormNg` on the good set -/

section QVBound

theorem NQGood1Gen_t_lt_one {d : ℕ} {sz : Sizes d} {n : ℕ} {s t : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ))
    (ht : t ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s)) : t < 1 := by
  have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL2 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := pow_pos (by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)) 2
  rcases div_pos_iff.1 (lt_of_lt_of_le (inv_pos.2 hW0) hWt) with ⟨h, -⟩ | ⟨h, -⟩
  · linarith
  · linarith [div_nonneg (sq_nonneg (sz.lam n)) hL2.le]

/-- The row-sum bound of `Step2Gen_UN` from K2 of `GridRepTailGen_Ker` (band `norm_UN_apply_le`, `Kernel/Evolution:131`):
`‖(𝒰_{v,w,σ} X)_a‖ ≤ ((1-v)/(1-w))^k M` for `0 ≤ v ≤ w < 1`, `‖X b‖ ≤ M`. -/
private theorem NQGood1Gen_norm_UN_row {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {k : ℕ}
    (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    {X : (Fin k → Zd d (sz.L n)) → ℂ} {M : ℝ} (hM : 0 ≤ M) (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ v w X a‖ ≤ ((1 - v) / (1 - w)) ^ k * M := by
  set Kk : Fin k → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := fun i =>
    Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w with hKk
  have hrow : ∀ i, ∑ c, ‖Kk i (a i) c‖ ≤ (1 - v) / (1 - w) := fun i => hK.2.1 _ _ v w hv0 hvw hw1 (a i)
  calc ‖Step2Gen_UN C n σ v w X a‖
      ≤ ∑ b : Fin k → Zd d (sz.L n), ‖(∏ i, Kk i (a i) (b i)) * X b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin k → Zd d (sz.L n), (∏ i, ‖Kk i (a i) (b i)‖) * M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hX b) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (∏ i, ∑ c, ‖Kk i (a i) c‖) * M := by
        rw [← Finset.sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ ((1 - v) / (1 - w)) ^ k * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        calc ∏ i, ∑ c, ‖Kk i (a i) c‖ ≤ ∏ _i : Fin k, ((1 - v) / (1 - w)) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _) fun i _ => hrow i
          _ = ((1 - v) / (1 - w)) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `STeeUMg` is `𝒰_σ` applied to `b ↦ (𝒰_σ̄ ∘ T_{b,·})(a)` (band `nqGood1_UgenPairN_eq_Ugen`). -/
private theorem NQGood1Gen_STeeUMg_eq {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (v w : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    STeeUMg Cm n v w H σ a =
      Step2Gen_UN Cm.toFlowFM n σ v w (fun b => Step2Gen_UN Cm.toFlowFM n (fun i => !σ i) v w (fun b' => STeeMg Cm n v H σ b b') a) a := by
  unfold STeeUMg Step2Gen_UN
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

/-- **The pair kernel on a tensor with a sup bound and far decay** (band `nqGood1_ugenPairN_le_of_bounds`, `NQGood1:431`, by two uses
of `hker_of_case1Ng`): for non-alternating `σ`, `D > k + 1`, `‖T b b'‖ ≤ Mee`, `‖T b b'‖ ≤ δ ≤ W^{-D}` beyond `ℓ_s W^{τ'}` in
`diam_∞ (b, b')`: `‖(𝒰_σ ⊗ 𝒰_σ̄) ∘ T (a,a)‖ ≤ κ₁ (κ₁ Mee + W^{Cv} δ) + W^{Cv} (W^k δ)`, `κ₁ = W^{Cv ε} r^{k-1}`. -/
theorem NQGood1Gen_pair_le {d k : ℕ} {sz : Sizes d} (C : FlowFM sz) {gK : ℕ → ℝ} {A Ck Cv : ℝ} (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : NQGoodGen_KerNAL C gK k Ck n) (hRow : GridRepTailGen_Ker C n) (hCv : Ck ≤ Cv) {ε τ' D : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hD : (k : ℝ) + 1 < D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t) / (1 - s))
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (T : (Fin k → Zd d (sz.L n)) → (Fin k → Zd d (sz.L n)) → ℂ) {Mee δ : ℝ} (hδ : 0 ≤ δ)
    (hδD : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) (hT : ∀ b b', ‖T b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin k → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) s * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖T b b'‖ ≤ δ)
    (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ s t (fun b => Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a) a‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1)) *
          ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1)) * Mee +
            ((sz.W n : ℕ) : ℝ) ^ Cv * δ) +
        ((sz.W n : ℕ) : ℝ) ^ Cv * (((sz.W n : ℕ) : ℝ) ^ k * δ) := by
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have hD1 : 1 < D := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have ht1 : t < 1 := NQGood1Gen_t_lt_one hW ht hWt
  have hMee0 : 0 ≤ Mee := (norm_nonneg _).trans (hT (fun _ => 0) (fun _ => 0))
  set κ1 : ℝ := W ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1) with hκ1
  have hκ10 : 0 ≤ κ1 := mul_nonneg (Real.rpow_nonneg hW0.le _) (by positivity)
  have hWC0 : 0 ≤ W ^ Cv := Real.rpow_nonneg hW0.le _
  have hσb : ∃ i, (fun i => !σ i) i = (fun i => !σ i) (finRotate k i) := by
    obtain ⟨i, hi⟩ := hσ
    exact ⟨i, by simp only [hi]⟩
  have hstage1 : ∀ b : Fin k → Zd d (sz.L n),
      ‖Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ κ1 * Mee + W ^ Cv * δ := by
    intro b
    exact hker_of_case1Ng C hd hcmp hA hKer hCv hW hε0 hε1 hWε hdW hAk hD1 hs hst ht hWt hσb (fun b' => T b b') hMee0 hδ hδD
      (fun b' => hT b b') (fun b' hfar => hTfar b b' (hfar.trans (by
        exact_mod_cast (show STdiamInf b' ≤ STdiamInf (Fin.append b b') from Finset.sup_le fun p _ => by
          have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) => zdistInf d (sz.L n) (Fin.append b b' q.1 - Fin.append b b' q.2))
            (Finset.mem_univ (Fin.natAdd k p.1, Fin.natAdd k p.2))
          rw [Fin.append_right, Fin.append_right] at h
          exact h)))) a
  have hP : (1 - s) / (1 - t) ≤ W := by
    have h1 : ((1 - t) / (1 - s))⁻¹ ≤ W := inv_le_of_inv_le₀ hW0 hWt
    rwa [inv_div] at h1
  have hP0 : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  have hstage1far : ∀ b : Fin k → Zd d (sz.L n), ellT (sz.L n) (sz.lam n) s * W ^ τ' ≤ (STdiamInf b : ℝ) →
      ‖Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a‖ ≤ W ^ k * δ := by
    intro b hfar
    have h1 := NQGood1Gen_norm_UN_row hRow (fun i => !σ i) hs hst ht1 hδ
      (fun b' => hTfar b b' (hfar.trans (by
        exact_mod_cast (show STdiamInf b ≤ STdiamInf (Fin.append b b') from Finset.sup_le fun p _ => by
          have h := Finset.le_sup (f := fun q : Fin (k + k) × Fin (k + k) => zdistInf d (sz.L n) (Fin.append b b' q.1 - Fin.append b b' q.2))
            (Finset.mem_univ (Fin.castAdd k p.1, Fin.castAdd k p.2))
          rw [Fin.append_left, Fin.append_left] at h
          exact h)))) a
    calc _ ≤ ((1 - s) / (1 - t)) ^ k * δ := h1
      _ ≤ W ^ k * δ := by gcongr
  have hδ2 : W ^ k * δ ≤ W ^ (-(D - k)) := by
    calc W ^ k * δ ≤ W ^ k * W ^ (-D) := by gcongr
      _ = W ^ (-(D - k)) := by rw [← Real.rpow_natCast, ← Real.rpow_add hW0]; congr 1; ring
  have hstage2 := hker_of_case1Ng C hd hcmp hA hKer hCv hW hε0 hε1 hWε hdW hAk (D := D - k) (by linarith) hs hst ht hWt hσ
    (fun b => Step2Gen_UN C n (fun i => !σ i) s t (fun b' => T b b') a) (M := κ1 * Mee + W ^ Cv * δ) (δ := W ^ k * δ)
    (add_nonneg (mul_nonneg hκ10 hMee0) (mul_nonneg hWC0 hδ)) (mul_nonneg (pow_nonneg hW0.le _) hδ) hδ2 hstage1 hstage1far a
  calc _ ≤ _ := hstage2
    _ = _ := by ring

variable {d k : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) {gK : ℕ → ℝ} {A Ck Cv : ℝ}

/-- **The quadratic-variation majorant from bounds on `𝓔⊗𝓔`** (band `nqGood1_qvFormN_le_of_bounds`, `NQGood1:515`): `qvFormNg` is
the real part of `STeeUMg`, a `Step2Gen_UN`-pair applied to `STeeMg`.  The time of the matrix need not be `v`: the shift
`u_j → u_{j+1}` enters through `Mee`, `δ`. -/
theorem NQGood1Gen_qvFormNg_le_of_bounds (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n) (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : Ck ≤ Cv) {ε τ' D : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hD : (k : ℝ) + 1 < D) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w)
    (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - v))
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {Mee δ : ℝ}
    (hδ : 0 ≤ δ) (hδD : δ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hT : ∀ b b' : Fin k → Zd d (sz.L n), ‖STeeMg Cm n v M σ b b'‖ ≤ Mee)
    (hTfar : ∀ b b' : Fin k → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖STeeMg Cm n v M σ b b'‖ ≤ δ)
    (a : Fin k → Zd d (sz.L n)) :
    qvFormNg Cm n v w σ M a ≤
      (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
          ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) * Mee +
            ((sz.W n : ℕ) : ℝ) ^ Cv * δ) +
        ((sz.W n : ℕ) : ℝ) ^ Cv * (((sz.W n : ℕ) : ℝ) ^ k * δ) := by
  unfold qvFormNg
  rw [NQGood1Gen_STeeUMg_eq]
  exact (Complex.re_le_norm _).trans
    (NQGood1Gen_pair_le Cm.toFlowFM hd hcmp hA hKer hRow hCv hW hε0 hε1 hWε hdW hAk hD hv0 hvw hwL hWt hσ _ hδ hδD hT hTfar a)

end QVBound


/-! ## 5. Target 3: the good-set shift `u_j → u_{j+1}` under `StepDecompGen_LoopForm` and `‖Cm.m n‖ ≤ 1` (D3) -/

section Shift

open scoped Matrix.Norms.L2Operator
open RBM.Ind (loopShiftErrN norm_loopL_zshiftN_le nqGood1_ellT_mono nqGood1_loopShiftErrN_nonneg norm_gloop_le_of_le_abs_im eeLoop_WF length_eeLoop)

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ}

/-- `η_u = (1 - u) Im m` of the carrier (`LoopForm`). -/
theorem NQGood1Gen_eta_eq (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) :
    Cm.eta n u = (1 - u) * (Cm.m n).im := (hL n).2.2.2 u

theorem NQGood1Gen_im_le_one {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1) : (Cm.m n).im ≤ 1 :=
  (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hm)

theorem NQGood1Gen_eta_pos (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u : ℝ} (hu : u < 1) : 0 < Cm.eta n u := by
  rw [NQGood1Gen_eta_eq hL]; exact mul_pos (by linarith) (hL n).1

/-- `η_{u'} ≤ η_u` for `u ≤ u'` (the carrier form of `etaT_le_of_le`). -/
theorem NQGood1Gen_eta_anti (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u u' : ℝ} (hu : u ≤ u') :
    Cm.eta n u' ≤ Cm.eta n u := by
  rw [NQGood1Gen_eta_eq hL, NQGood1Gen_eta_eq hL]; nlinarith [(hL n).1]

theorem NQGood1Gen_eta_le_one (hL : StepDecompGen_LoopForm Cm E) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) :
    Cm.eta n u ≤ 1 := by
  rw [NQGood1Gen_eta_eq hL]; nlinarith [(hL n).1, NQGood1Gen_im_le_one hm]

/-- `|Im z_u| = η_u` for `u < 1`, `z_u = ztOf (Cm.m n) (E n) u`. -/
theorem NQGood1Gen_abs_zt_im (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u : ℝ} (hu : u < 1) :
    |(ztOf (Cm.m n) (E n) u).im| = Cm.eta n u := by
  rw [ztOf_im, ← (hL n).2.2.2 u, abs_of_pos (NQGood1Gen_eta_pos hL n hu)]

/-- `|z_{u'} - z_u| ≤ |u' - u|` (`‖m‖ ≤ 1`). -/
theorem NQGood1Gen_norm_zt_sub {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1) (u u' : ℝ) :
    ‖ztOf (Cm.m n) (E n) u' - ztOf (Cm.m n) (E n) u‖ ≤ |u' - u| := by
  have h : ztOf (Cm.m n) (E n) u' - ztOf (Cm.m n) (E n) u = ((u - u' : ℝ) : ℂ) * Cm.m n := by
    simp only [ztOf]; push_cast; ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_of_le_one_right (abs_nonneg _) hm

/-- **Crude loop bound** (band `norm_loopFine_crudeN`, `NQGood1:916`): `|𝓛_{u,σ,a}(M)| ≤ η_u^{-ℓ}` for Hermitian `M`, `ℓ ≥ 1`. -/
theorem norm_loopFine_crudeNg (hL : StepDecompGen_LoopForm Cm E) {n : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u : ℝ} (hu1 : u < 1) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d (sz.L n)) :
    ‖Cm.LM n u M σ a‖ ≤ (Cm.eta n u)⁻¹ ^ ℓ := by
  have hη := NQGood1Gen_eta_pos hL n hu1
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  have hwf : (loopOf σ a).σ.length = (loopOf σ a).a.length := by simp [loopOf]
  have hlen : (loopOf σ a).a.length = ℓ := by simp [loopOf]
  have h := norm_gloop_le_of_le_abs_im hMb hη (le_of_eq (NQGood1Gen_abs_zt_im hL n hu1).symm) (loopOf σ a) hwf (by rw [hlen]; exact hℓ)
  rw [hlen] at h
  rw [congrFun (StepDecompGen_LM_eq hL n u σ a) M]
  refine h.trans ?_
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWi : (((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹) ^ (ℓ - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have h0 : 0 ≤ (Cm.eta n u)⁻¹ ^ ℓ := by positivity
  calc (Cm.eta n u)⁻¹ ^ ℓ * (((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹) ^ (ℓ - 1) ≤ (Cm.eta n u)⁻¹ ^ ℓ * 1 := mul_le_mul_of_nonneg_left hWi h0
    _ = _ := mul_one _

/-- **The crude `(𝓛-𝒦)` envelope** (band `STmaxLKM_crudeN`, `NQGood1:941`): for Hermitian `M`, `0 ≤ u < 1` and `‖𝒦^{(m)}_{u,σ,a}‖ ≤ M_K`
for the loops of length `m ≤ n'`, `max|𝓛 - 𝒦| ≤ η_u^{-n'} + M_K`. -/
theorem STmaxLKMg_crudeNg (hL : StepDecompGen_LoopForm Cm E) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {n' m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n') {MK : ℝ} (hK : ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), ‖Cm.K n u σ a‖ ≤ MK) :
    STmaxLKMg Cm n u m M ≤ (Cm.eta n u)⁻¹ ^ n' + MK := by
  have hη := NQGood1Gen_eta_pos hL n hu1
  have hη1 : 1 ≤ (Cm.eta n u)⁻¹ := (one_le_inv₀ hη).mpr (NQGood1Gen_eta_le_one hL hm hu0)
  unfold STmaxLKMg
  refine Finset.sup'_le _ _ fun p _ => ?_
  have h1 := norm_loopFine_crudeNg hL hM hu1 hm1 p.1 p.2
  have h2 : (Cm.eta n u)⁻¹ ^ m ≤ (Cm.eta n u)⁻¹ ^ n' := pow_le_pow_right₀ hη1 hmn
  have h3 := hK p.1 p.2
  calc _ ≤ ‖Cm.LM n u M p.1 p.2‖ + ‖Cm.K n u p.1 p.2‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- **Crude bound on `Ξ̂^{(𝓛-𝒦)}_m(M)`** (band `STXiLKM_crudeN`, `NQGood1:959`): for `1 ≤ m ≤ n'` and `B_u ≤ 1`,
`Ξ̂^{(𝓛-𝒦)}_m ≤ 1 + (η_u^{-n'} + M_K) / B_u^{n'}`. -/
theorem STXiLKMg_crudeNg (hL : StepDecompGen_LoopForm Cm E) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hB1 : sz.Bctl n u ≤ 1) {n' m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n') {MK : ℝ}
    (hK : ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), ‖Cm.K n u σ a‖ ≤ MK) :
    STXiLKMg Cm n u m M ≤ 1 + ((Cm.eta n u)⁻¹ ^ n' + MK) / (sz.Bctl n u) ^ n' := by
  have hB : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu1
  have h1 := STmaxLKMg_crudeNg hL hm hM hu0 hu1 hm1 hmn hK
  have h0 : 0 ≤ STmaxLKMg Cm n u m M :=
    Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))) (norm_nonneg _)
  have hpow : (sz.Bctl n u) ^ n' ≤ (sz.Bctl n u) ^ m := pow_le_pow_of_le_one hB.le hB1 hmn
  unfold STXiLKMg
  have h2 : STmaxLKMg Cm n u m M / (sz.Bctl n u) ^ m ≤ STmaxLKMg Cm n u m M / (sz.Bctl n u) ^ n' :=
    div_le_div_of_nonneg_left h0 (pow_pos hB _) hpow
  have h3 : STmaxLKMg Cm n u m M / (sz.Bctl n u) ^ n' ≤ ((Cm.eta n u)⁻¹ ^ n' + MK) / (sz.Bctl n u) ^ n' :=
    div_le_div_of_nonneg_right h1 (pow_pos hB _).le
  linarith

/-- The shift error of the pair form at loop length `2k+2` (band `eeShiftErrN`, `NQGood1:982`):
`W^d · k · L^d · (2k+2) η_{u'}^{-(2k+3)} (W^{-d})^{2k+1} (u'-u)`, `η_{u'} = Cm.eta n u'` (`Σ_{b,b'} |S_{bb'}| ≤ L^d`). -/
def eeShiftErrNg (Cm : Step2Mat sz) (n k : ℕ) (u u' : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d) * ((k : ℝ) * ((((sz.L n : ℕ) : ℝ) ^ d) * loopShiftErrN d (sz.W n) (Cm.eta n u') (2 * k + 2) (u' - u)))

/-- **The shift of the pair form** (band `norm_STeeM_shiftN_le`, `NQGood1:996`): `|(𝓔⊗𝓔)_{u'} - (𝓔⊗𝓔)_u| ≤ eeShiftErrNg` for Hermitian `M`;
`hS` is the row-sum bound `Σ_b ‖S_{ab}‖ ≤ 1` of the carrier (`SEforLnGen_Facts`; the band has `Σ_b ‖SB a b‖ = 1`). -/
theorem norm_STeeMg_shiftNg_le (hL : StepDecompGen_LoopForm Cm E) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u u' : ℝ} (huu' : u ≤ u')
    (hu'1 : u' < 1) {k : ℕ} (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) :
    ‖STeeMg Cm n u' M σ a a' - STeeMg Cm n u M σ a a'‖ ≤ eeShiftErrNg Cm n k u u' := by
  have hW2 : ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
  have hδ0 : 0 ≤ loopShiftErrN d (sz.W n) (Cm.eta n u') (2 * k + 2) (u' - u) :=
    nqGood1_loopShiftErrN_nonneg (NQGood1Gen_eta_pos hL n hu'1).le (by linarith : 0 ≤ u' - u) d (sz.W n) (2 * k + 2)
  have hMb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hM.submatrix _
  have hη := NQGood1Gen_eta_pos hL n hu'1
  have hz : Cm.eta n u' ≤ |(ztOf (Cm.m n) (E n) u).im| := by
    rw [NQGood1Gen_abs_zt_im hL n (huu'.trans_lt hu'1)]; exact NQGood1Gen_eta_anti hL n huu'
  have hz' : Cm.eta n u' ≤ |(ztOf (Cm.m n) (E n) u').im| := by rw [NQGood1Gen_abs_zt_im hL n hu'1]
  have hS2 : ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), ‖Cm.S n b b'‖ ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    refine (Finset.sum_le_sum fun b _ => hS b).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := by simp [Zd, ZMod.card]
    rw [this]; push_cast; rfl
  unfold STeeMg
  rw [← mul_sub, norm_mul, hW2]
  have key : ‖∑ k' ∈ Finset.Icc 1 k, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        Cm.S n b b' * STLIMg Cm n u' M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') -
      ∑ k' ∈ Finset.Icc 1 k, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
        Cm.S n b b' * STLIMg Cm n u M (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b')‖ ≤
      (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d * loopShiftErrN d (sz.W n) (Cm.eta n u') (2 * k + 2) (u' - u)) := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k' ∈ Finset.Icc 1 k, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
          ‖Cm.S n b b'‖ * loopShiftErrN d (sz.W n) (Cm.eta n u') (2 * k + 2) (u' - u) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
          simp only [Finset.mem_Icc] at hk'
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
          rw [← mul_sub, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hwf := eeLoop_WF (List.ofFn σ) (List.ofFn a) (List.ofFn a') hk'.1 (by simpa using hk'.2) (by simp) (by simp) b b'
          have hlenE : (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b').a.length = 2 * k + 2 := by
            have := length_eeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') (k := k') (by simp; omega) (by simp) b b'
            simpa [LoopIdx.length] using this
          have h1 := norm_loopL_zshiftN_le hMb hη hz hz' (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k' b b') hwf
            (by rw [hlenE]; omega)
          rw [hlenE] at h1
          have hzt := NQGood1Gen_norm_zt_sub (E := E) hm u u'
          rw [abs_of_nonneg (by linarith)] at hzt
          have h2 : ((2 * k + 2 : ℕ) : ℝ) * ((Cm.eta n u')⁻¹ ^ (2 * k + 2 + 1) * (((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1)) *
              ‖ztOf (Cm.m n) (E n) u' - ztOf (Cm.m n) (E n) u‖) ≤ loopShiftErrN d (sz.W n) (Cm.eta n u') (2 * k + 2) (u' - u) := by
            unfold loopShiftErrN
            have : 0 ≤ (Cm.eta n u')⁻¹ := inv_nonneg.2 hη.le
            push_cast
            gcongr
          unfold STLIMg
          rw [(hL n).2.2.1 u' M _, (hL n).2.2.1 u M _]
          exact h1.trans h2
      _ ≤ (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d * loopShiftErrN d (sz.W n) (Cm.eta n u') (2 * k + 2) (u' - u)) := by
          simp only [← Finset.sum_mul, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS2 hδ0) (Nat.cast_nonneg k)
  unfold eeShiftErrNg
  exact mul_le_mul_of_nonneg_left key (by positivity)

end Shift


/-! ## 6. Compiled nonempty instances (`d = 3`, band carrier `bandStep2Mat sz0 Einst`, `n = 0`)

Data of the band instances `NQGood1Inst` (reused by name, private facts by `open private`): `sz0` (`L = 4`, `W = 32`, `lam = 1/64`),
`E ≡ 1/2`, grid `u_0 = 0`, `u_1 = 1/128`, `k = 3`, `σ = (+,-,+)` (non-alternating), levels `(Γ, Λ, Φ) = (4, 3, 1)`, `τ' = 1/5`, `D' = 6`,
`ε = 4/5`, `Λ_g = 10`, `κ' = 1/2`; `H_0 = 0 ∈ GoodSetNg` (`zero_mem_goodSetN_inst`, the bridge is `Iff.rfl`); the far label vector
`aFar` has `diam_∞ = 2 ≥ ℓ_0 W^{τ'}`.  The comparison is R1 with `A = 1`, `gK = lam`, `Cv = Ck = nqGood1C 3 3 10 (1/2)`.  D1 is also
instantiated at the flow `(szB, zB)` of `Induction/Step34Pins`. -/

/-! ### Target 3: the shift lemmas, one step `u_0 = 0 → u_1 = 1/128` -/

end RBM.BA

end
