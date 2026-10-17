/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQGood1Gen
import RBM3D.Chain.StepDecompGen
import RBM3D.Induction.NQGood2

/-!
# The non-alternating good-set inputs, second half, over the carrier (U3s2a, file 2; ticket T2491)

Generic forms of `Induction/NQGood2.lean` (not edited) over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: arXiv:2507.20274, `lem:STOeq_NQ` (`3_5:1136`, proof `3_5:1152`), (5.93) (`3_5:1158`).

* **Target 4** the vocabulary with an explicit constant `Ck` (the band constant `nqGood1C` is a `Classical.choose`): `kappaNonAltNg`,
  `epsNonAltNg`, `dDriftNonAltNg`, `qvBdNonAltNg`, `cQVNonAltNg`, with their band bridges (`rfl` at `Ck = nqGood1C d k Λg κ'`) and
  (5.93) `kappaNonAltNg_mul_Bctl_pow_le`.  `nonAltClsN` and `nqGood2_ratio_mul_Bctl_le` are model-free and used by name.
* **Target 5** the fields of `GridAssemblyHypNg` (`GridAssemblyGen.lean:221-391`): `nonAlt_hkerNg` (D1 at `gK` and R1 through
  `hker_of_case1Ng`), `goodSetNg_A0clsNg`, `nonAlt_hA0clsNg`, `nonAlt_hdriftNg`, `goodSetNg_driftClsNg`, `nonAlt_hDclsNg`,
  `nonAlt_hκ0Ng`, `nonAlt_hε0Ng`, `nonAlt_hdDrift0Ng`.
* **Target 6** `qvBdNonAltNg_pos`, `qvFormNg_le_of_goodSetNg_shift`, `hQ_nonAltNg` (the `hQ` of `azumaProxy_subG_goodExitg`,
  `AzumaProxyGen.lean:237-238`, with `Q = cQVNonAltNg`), `subGaussStop_nonAltNg`, `cQVNonAltNg_sum_pos`, and the band re-derivation
  `hQ_nonAltN_of_Ng` of the merged `hQ_nonAltN` (`NQGood2:519`).  Closes T2473c-audit O1 (`hQ` open at `Cm0`) by the instance of
  `subGaussStop_nonAltNg`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private nqGood2_pow_aux nqGood2_gridTime_le nqGood2_gridTime_nonneg from RBM3D.Induction.NQGood2

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nonAltClsN nqGood2_ratio_mul_Bctl_le nqGood1C nqGood1_ellT_mono)

/-! ## 1. Target 4: the vocabulary with an explicit constant `Ck`, (5.93) -/

section Vocab

variable {d : ℕ} {sz : Sizes d}

/-- **The kernel weight `κ_{i,m}`** (band `kappaNonAltN`, `NQGood2:86`): the coefficient of `M` in `hker_of_case1Ng`,
`W^{Ck ε} ((g²+|1-u_i|)/(g²+|1-u_m|))^{k-1}`. -/
def kappaNonAltNg (k : ℕ) (Ck g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
  W ^ (Ck * ε) * ((g ^ 2 + |1 - u i|) / (g ^ 2 + |1 - u m|)) ^ (k - 1)

/-- **The additive decay-error weight `ε_{i,m}`** (band `epsNonAltN`): the coefficient of `δ`, the constant `W^{Ck}`. -/
def epsNonAltNg (Ck W : ℝ) (_i _m : ℕ) : ℝ :=
  W ^ Ck

/-- **The variance majorant** (band `qvBdNonAltN`, `NQGood2:102`): the right side of `NQGood1Gen_qvFormNg_le_of_bounds` at `(v, w) = (u, w)`
with `Mee = Γ(ΓΛ)B_u^{2k}/η_u + W^{-D''}` and `δ = W^{-D''}`. -/
def qvBdNonAltNg (Cm : Step2Mat sz) (n k : ℕ) (Ck ε Γ Λ D'' u w : ℝ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
    ((((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) *
      (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / Cm.eta n u) + ((sz.W n : ℕ) : ℝ) ^ (-D'')) +
      ((sz.W n : ℕ) : ℝ) ^ Ck * ((sz.W n : ℕ) : ℝ) ^ (-D'')) +
    ((sz.W n : ℕ) : ℝ) ^ Ck * (((sz.W n : ℕ) : ℝ) ^ k * ((sz.W n : ℕ) : ℝ) ^ (-D''))

/-- **The sub-Gaussian proxy of the `j`-th propagated increment towards `u_m`** (band `cQVNonAltN`): `Δ · k · qvBdNonAltNg(u_{j+1}, u_m)`. -/
def cQVNonAltNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Ck ε : ℝ) (Γ Λ : ℕ → ℝ) (D'' : ℝ) (m : ℕ)
    (_a : Fin k → Zd d (sz.L n)) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * qvBdNonAltNg Cm n k Ck ε (Γ n) (Λ n) D'' (gridTime s v K n (j + 1)) (gridTime s v K n m))).toNNReal

private theorem NQGood2Gen_kappa_nonneg (k : ℕ) (Ck g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ) (i m : ℕ) :
    0 ≤ kappaNonAltNg k Ck g W ε u i m :=
  mul_nonneg (Real.rpow_nonneg hW _) (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

/-- **(5.93), the sharp kernel on the initial datum** (band `kappaNonAltN_mul_Bctl_pow_le`, `NQGood2:188`): for `u_i ≤ u_m < 1` and `0 ≤ W`,
`κ_{i,m} B_{u_i}^k ≤ W^{Ck ε} B_{u_m}^k`. -/
theorem kappaNonAltNg_mul_Bctl_pow_le (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) {W : ℝ} (hW : 0 ≤ W) (u : ℕ → ℝ)
    {i m : ℕ} (him : u i ≤ u m) (hm1 : u m < 1) :
    kappaNonAltNg k Ck (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤ W ^ (Ck * ε) * (sz.Bctl n (u m)) ^ k := by
  have hi1 : u i < 1 := him.trans_lt hm1
  have hBu : 0 < sz.Bctl n (u i) := Sizes.STBctl_pos sz n hi1
  have hBle : sz.Bctl n (u i) ≤ sz.Bctl n (u m) := Sizes.STBctl_mono sz n him hm1
  have hr0 : 0 ≤ (sz.lam n ^ 2 + |1 - u i|) / (sz.lam n ^ 2 + |1 - u m|) := div_nonneg (by positivity) (by positivity)
  have hrB := nqGood2_ratio_mul_Bctl_le sz n him hm1
  have hWC : 0 ≤ W ^ (Ck * ε) := Real.rpow_nonneg hW _
  unfold kappaNonAltNg
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (nqGood2_pow_aux hr0 hBu.le hBle hrB k) hWC

/-- **(5.93), the sharp kernel on the drift** (band `kappaNonAltN_succ_mul_Bctl_pow_le`, `NQGood2:206`): for `u_j ≤ u_{j+1} ≤ u_m < 1`,
`κ_{j+1,m} B_{u_j}^k ≤ W^{Ck ε} B_{u_m}^k`. -/
theorem kappaNonAltNg_succ_mul_Bctl_pow_le (sz : Sizes d) (n k : ℕ) (Ck ε : ℝ) {W : ℝ} (hW : 0 ≤ W) (u : ℕ → ℝ) (j m : ℕ)
    (hjj : u j ≤ u (j + 1)) (hj1m : u (j + 1) ≤ u m) (hm1 : u m < 1) :
    kappaNonAltNg k Ck (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k ≤ W ^ (Ck * ε) * (sz.Bctl n (u m)) ^ k := by
  have hj1 : u (j + 1) < 1 := hj1m.trans_lt hm1
  have hBle : sz.Bctl n (u j) ≤ sz.Bctl n (u (j + 1)) := Sizes.STBctl_mono sz n hjj hj1
  have hBj : 0 < sz.Bctl n (u j) := Sizes.STBctl_pos sz n (hjj.trans_lt hj1)
  have hκ := NQGood2Gen_kappa_nonneg k Ck (sz.lam n) W ε hW u (j + 1) m
  calc kappaNonAltNg k Ck (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k
      ≤ kappaNonAltNg k Ck (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u (j + 1))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBj.le hBle k) hκ
    _ ≤ _ := kappaNonAltNg_mul_Bctl_pow_le sz n k Ck ε hW u hj1m hm1

end Vocab


/-! ## 2. Target 5: the fields of `GridAssemblyHypNg` -/

section Fields

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz}

/-- **The field `hker` for non-alternating `σ`** (band `nonAlt_hkerN`, `NQGood2:252`): `hker_of_case1Ng` in the shape of the field of
`GridAssemblyHypNg`, `Cls = nonAltClsN`, `κ = kappaNonAltNg`, `εK = epsNonAltNg`.  D1 at `gK` (`hKer`) and R1 (`hcmp`, `hdW`, `hAk`) as in
`hker_of_case1Ng`; the grid `u` is nonnegative and monotone on `[0, K]`, `u_K ≤ 1 - lam²/L²`, `W⁻¹ ≤ (1-u_K)/(1-u_0)`. -/
theorem nonAlt_hkerNg {k : ℕ} (C : FlowFM sz) {gK : ℕ → ℝ} {A Ck Cv : ℝ} (hd : 0 < d)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A) {n : ℕ}
    (hKer : NQGoodGen_KerNAL C gK k Ck n) (hCv : Ck ≤ Cv) {ε τ' Dc : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hDc : 1 < Dc)
    {K : ℕ} {u : ℕ → ℝ} (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m)
    (huK : u K ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - u K) / (1 - u 0))
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ → (∀ b, ‖X b‖ ≤ M) →
      nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i δ X → ∀ a : Fin k → Zd d (sz.L n),
      ‖Step2Gen_UN C n σ (u i) (u m) X a‖ ≤
        kappaNonAltNg k Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m * M + epsNonAltNg Cv ((sz.W n : ℕ) : ℝ) i m * δ := by
  intro i m him hmK X M δ hM hδ hXM hcls a
  obtain ⟨hδD, hXcls⟩ := hcls
  have hiK : i ≤ K := him.trans hmK
  have hmK' : u m ≤ u K := hmono m K hmK le_rfl
  have hi0 : u 0 ≤ u i := hmono 0 i (Nat.zero_le _) hiK
  have hK1 : u K < 1 := NQGood1Gen_t_lt_one hW huK hWt
  have hwin : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - u m) / (1 - u i) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith [hmono i K hiK le_rfl]) (by linarith)
  exact hker_of_case1Ng C hd hcmp hA hKer hCv hW hε0 hε1 hWε hdW hAk hDc (hu0 i hiK) (hmono i m him hmK) (hmK'.trans huK) hwin hσ
    X hM hδ hδD hXM hXcls a

/-- **The field `hA0cls`**, matrix level (band `goodSetN_A0clsN`, `NQGood2:284`): for `M ∈ GoodSetNg … u_i`, `1 ≤ k` and `Dc ≤ D'`, the tensor
`a ↦ (𝓛-𝒦)_{u_i,σ,a}(M)` is in the class `nonAltClsN … i` with `δ = W^{-D'}` (clause (Dec) at length `k ≤ 2k+2`). -/
theorem goodSetNg_A0clsNg {n k : ℕ} (hk : 1 ≤ k) {Γ Λ Φ τ' D' Dc : ℝ} (hDc : Dc ≤ D') (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) {u : ℕ → ℝ} {i : ℕ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : GoodSetNg Cm n (u i) k Γ Λ Φ τ' D' M) (σ : Fin k → Bool) :
    nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i (((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun a => STLKMg Cm n (u i) M σ a) := by
  refine ⟨Real.rpow_le_rpow_of_exponent_le hW (by linarith), fun b hfar => ?_⟩
  obtain ⟨-, -, hDec, -⟩ := hM
  have h := hDec k hk (by omega) σ b hfar
  have e : STLKMg Cm n (u i) M σ b = Cm.LM n (u i) M σ b - Cm.K n (u i) σ b := rfl
  change ‖STLKMg Cm n (u i) M σ b‖ ≤ _
  rw [e]
  have h0 : 0 ≤ ‖Cm.LM n (u i) M σ b‖ := norm_nonneg _
  linarith

/-- **The field `hA0cls` on the event `{H_0 ∈ GoodSetNg(u_0)}`** (band `nonAlt_hA0clsN`, `NQGood2:303`). -/
theorem nonAlt_hA0clsNg {n k : ℕ} (hk : 1 ≤ k) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (σ : Fin k → Bool)
    (s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' Dc : ℝ) (hDc : Dc ≤ D') (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n j ω)) :
    ∀ ω, 0 < τ ω → nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc (gridTime s v K n) 0
      (((sz.W n : ℕ) : ℝ) ^ (-D')) (AvecNg Cm s v K n 0 σ ω) :=
  fun ω hω => goodSetNg_A0clsNg hk hDc hW (hτG ω 0 hω) σ

/-- **The field `hDcls`**, matrix level (band `goodSetN_driftClsN`, `NQGood2:329`): the drift tensor at `u_i` of `M ∈ GoodSetNg … u_i` is in the
class `nonAltClsN … i'` of radius `ℓ_{u_{i'}} W^{τ'}`, `δ = W^{-D'}`, for `u_i ≤ u_{i'} < 1` (clause (Va) at `u_i`). -/
theorem goodSetNg_driftClsNg {n k : ℕ} {Γ Λ Φ τ' D' Dc : ℝ} (hDc : Dc ≤ D') (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) {u : ℕ → ℝ} {i i' : ℕ}
    (hii' : u i ≤ u i') (hi'1 : u i' < 1) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : GoodSetNg Cm n (u i) k Γ Λ Φ τ' D' M) (σ : Fin k → Bool) :
    nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i' (((sz.W n : ℕ) : ℝ) ^ (-D'))
      (driftTensorNg Cm n (u i) M σ) := by
  refine ⟨Real.rpow_le_rpow_of_exponent_le hW (by linarith), fun b hfar => ?_⟩
  have hWτ : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg (by linarith) _
  have hrad : ellT (sz.L n) (sz.lam n) (u i) ≤ ellT (sz.L n) (sz.lam n) (u i') := nqGood1_ellT_mono _ _ hii' hi'1
  exact driftTensorNg_far_of_goodSetNg hM σ b ((mul_le_mul_of_nonneg_right hrad hWτ).trans hfar)

/-- **The field `hDcls` on the event** (band `nonAlt_hDclsN`, `NQGood2:344`): the drift tensor at `(u_j, H_j)` is in the class at index `j + 1`. -/
theorem nonAlt_hDclsNg {n k : ℕ} (s v : ℕ → ℝ) (K : ℕ → ℕ) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' Dc : ℝ) (hDc : Dc ≤ D') (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n j ω)) :
    ∀ ω j, j < K n → j < τ ω →
      nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc (gridTime s v K n) (j + 1) (((sz.W n : ℕ) : ℝ) ^ (-D'))
        (driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ) := by
  intro ω j hjK hjτ
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) := ST_gridTime_mono s v K n hsv (Nat.le_succ j)
  have hu1 : gridTime s v K n (j + 1) < 1 := (nqGood2_gridTime_le hsv (show j + 1 ≤ K n by omega)).trans_lt hv1
  exact goodSetNg_driftClsNg hDc hW hjj hu1 (hτG ω j hjτ) σ

/-- The non-negativity field `hκ0` (band `nonAlt_hκ0N`): `κ_{i,m} = W^{Ck ε} r^{k-1} ≥ 0`. -/
theorem nonAlt_hκ0Ng (k : ℕ) (Ck g W ε : ℝ) (hW : 0 ≤ W) (K : ℕ) (u : ℕ → ℝ) :
    ∀ i m, i ≤ m → m ≤ K → 0 ≤ kappaNonAltNg k Ck g W ε u i m :=
  fun i m _ _ => NQGood2Gen_kappa_nonneg k Ck g W ε hW u i m

/-- The non-negativity field `hε0` (band `nonAlt_hε0N`): `ε_{i,m} = W^{Ck} ≥ 0`. -/
theorem nonAlt_hε0Ng (Ck W : ℝ) (hW : 0 ≤ W) (K : ℕ) : ∀ i m, i ≤ m → m ≤ K → 0 ≤ epsNonAltNg Ck W i m :=
  fun i m _ _ => Real.rpow_nonneg hW _

end Fields

/-! ## 3. Target 6: the quadratic-variation constant, `hQ_nonAltNg` -/

section QVConst

variable {d k : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `0 < qvBdNonAltNg` (band `qvBdNonAltN_pos`, `NQGood2:401`): the last term `W^{Ck} W^k W^{-D''}` is positive and the others are nonnegative
(`η_u = (1-u) Im m ≥ 0` for `u ≤ 1`, from `LoopForm`).  No energy condition is needed. -/
theorem qvBdNonAltNg_pos {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {Ck ε Γ Λ D'' u w : ℝ} (hΛ : 0 ≤ Λ) (hu1 : u ≤ 1) :
    0 < qvBdNonAltNg Cm n k Ck ε Γ Λ D'' u w := by
  have hWp : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hη : 0 ≤ Cm.eta n u := by
    rw [NQGood1Gen_eta_eq hL]; exact mul_nonneg (by linarith) (hL n).1.le
  have hG : 0 ≤ Γ * (Γ * Λ) := by
    have : Γ * (Γ * Λ) = Γ ^ 2 * Λ := by ring
    rw [this]; exact mul_nonneg (sq_nonneg _) hΛ
  have hB2 : 0 ≤ (sz.Bctl n u) ^ (2 * k) := (even_two_mul k).pow_nonneg _
  have hmain := mul_nonneg hG (div_nonneg hB2 hη)
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_pos_of_pos hWp _
  have hWC : 0 < ((sz.W n : ℕ) : ℝ) ^ Ck := Real.rpow_pos_of_pos hWp _
  have hκ1 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Ck * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1) :=
    mul_nonneg (Real.rpow_nonneg hWp.le _) (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)
  unfold qvBdNonAltNg
  exact add_pos_of_nonneg_of_pos (mul_nonneg hκ1 (add_nonneg (mul_nonneg hκ1 (add_nonneg hmain hWD.le)) (mul_nonneg hWC.le hWD.le)))
    (mul_pos hWC (mul_pos (pow_pos hWp k) hWD))

variable {Cm} {E gK : ℕ → ℝ} {A Ck Cv : ℝ}

/-- **The variance majorant of `AzumaSubGNg` after the spectral-time shift `u → u'`** (band `qvFormN_le_of_goodSetN_shiftN`, `NQGood2:435`): for
`M ∈ GoodSetNg(u)` (levels `Γ, Λ, Φ`, decay `τ', D'`), `0 ≤ u ≤ u' ≤ w ≤ 1 - lam²/L²`, `W⁻¹ ≤ (1-w)/(1-u')`, non-alternating `σ`, `k + 1 < D''` and
the shift hypothesis `W^{-D'} + eeShiftErrNg(u, u') ≤ W^{-D''}`: `qvFormNg_{u',w}(M)(a) ≤ qvBdNonAltNg(u', w)`.  `LoopForm` and `‖Cm.m n‖ ≤ 1`
(D3) replace `|E| < 2`; the row sums `hS` of `Cm.S` enter through `norm_STeeMg_shiftNg_le`; D1 and R1 enter through
`NQGood1Gen_qvFormNg_le_of_bounds`. -/
theorem qvFormNg_le_of_goodSetNg_shift (hd : 0 < d) (hL : StepDecompGen_LoopForm Cm E) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A)
    (hKer : NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n) (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : Ck ≤ Cv) {ε τ' D' D'' : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hD'' : (k : ℝ) + 1 < D'')
    {u u' w : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'w : u' ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - u')) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i))
    {Γ Λ Φ : ℝ} (hΛ : 0 ≤ Λ) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : GoodSetNg Cm n u k Γ Λ Φ τ' D' M)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrNg Cm n k u u' ≤ ((sz.W n : ℕ) : ℝ) ^ (-D''))
    (a : Fin k → Zd d (sz.L n)) :
    qvFormNg Cm n u' w σ M a ≤ qvBdNonAltNg Cm n k Cv ε Γ Λ D'' u' w := by
  have hMh : M.IsHermitian := hM.1
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := hM
  have hw1 : w < 1 := NQGood1Gen_t_lt_one hW hwL hWt
  have hu'1 : u' < 1 := hu'w.trans_lt hw1
  have hu1 : u < 1 := huu'.trans_lt hu'1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWD'' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hW0.le _
  have hWD' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hWτ : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  have hηu' := NQGood1Gen_eta_pos hL n hu'1
  have hηle : Cm.eta n u' ≤ Cm.eta n u := NQGood1Gen_eta_anti hL n huu'
  have hBu : 0 < sz.Bctl n u := Sizes.STBctl_pos sz n hu1
  have hBu' : 0 < sz.Bctl n u' := Sizes.STBctl_pos sz n hu'1
  have hBle : sz.Bctl n u ≤ sz.Bctl n u' := Sizes.STBctl_mono sz n huu' hu'1
  have hG : 0 ≤ Γ * (Γ * Λ) := by
    have : Γ * (Γ * Λ) = Γ ^ 2 * Λ := by ring
    rw [this]; exact mul_nonneg (sq_nonneg _) hΛ
  have hmono : Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / Cm.eta n u) ≤ Γ * (Γ * Λ) * ((sz.Bctl n u') ^ (2 * k) / Cm.eta n u') :=
    mul_le_mul_of_nonneg_left (div_le_div₀ (pow_nonneg hBu'.le _) (pow_le_pow_left₀ hBu.le hBle _) hηu' hηle) hG
  have hLK : ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) u' := nqGood1_ellT_mono _ _ huu' hu'1
  have htri : ∀ b b' : Fin k → Zd d (sz.L n), ‖STeeMg Cm n u' M σ b b'‖ ≤ ‖STeeMg Cm n u M σ b b'‖ + eeShiftErrNg Cm n k u u' := by
    intro b b'
    have h3 : ‖STeeMg Cm n u' M σ b b'‖ ≤ ‖STeeMg Cm n u M σ b b'‖ + ‖STeeMg Cm n u' M σ b b' - STeeMg Cm n u M σ b b'‖ := by
      have := norm_add_le (STeeMg Cm n u M σ b b') (STeeMg Cm n u' M σ b b' - STeeMg Cm n u M σ b b')
      rwa [add_sub_cancel] at this
    linarith [norm_STeeMg_shiftNg_le hL hm hS hMh huu' hu'1 σ b b']
  have hT : ∀ b b' : Fin k → Zd d (sz.L n), ‖STeeMg Cm n u' M σ b b'‖ ≤
      Γ * (Γ * Λ) * ((sz.Bctl n u') ^ (2 * k) / Cm.eta n u') + ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
    intro b b'
    have h1 := hD4 σ b b'
    have h2 := htri b b'
    linarith
  have hTfar : ∀ b b' : Fin k → Zd d (sz.L n), ellT (sz.L n) (sz.lam n) u' * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) →
      ‖STeeMg Cm n u' M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
    intro b b' hfar
    have h1 := hVb σ b b' ((mul_le_mul_of_nonneg_right hLK hWτ).trans hfar)
    have h2 := htri b b'
    linarith
  have key := NQGood1Gen_qvFormNg_le_of_bounds Cm hd hcmp hA hKer hRow hCv hW hε0 hε1 hWε hdW hAk hD'' (hu0.trans huu') hu'w hwL hWt hσ M
    (Mee := Γ * (Γ * Λ) * ((sz.Bctl n u') ^ (2 * k) / Cm.eta n u') + ((sz.W n : ℕ) : ℝ) ^ (-D'')) (δ := ((sz.W n : ℕ) : ℝ) ^ (-D''))
    hWD'' le_rfl hT hTfar a
  unfold qvBdNonAltNg
  exact key

/-- **The majorant `hQ` of `azumaProxy_subG_goodExitg` on the good set** (band `hQ_nonAltN`, `NQGood2:519`; the conclusion is the `hQ` of
`AzumaProxyGen.lean:237-238` at the proxy `Q = cQVNonAltNg`, `T2491_HQg`): for `M ∈ GoodSetNg(u_j)` Hermitian,
`Δ · (k · qvFormNg_{u_{j+1},u_m}(M)) ≤ cQVNonAltNg`, under the shift hypothesis `W^{-D'} + eeShiftErrNg(u_j, u_{j+1}) ≤ W^{-D''}`.  All hypotheses
are at the fixed `n`; the window `W⁻¹ ≤ (1-v_n)/(1-s_n)` and `v_n ≤ 1 - lam²/L²` give those of the shifted majorant for every `u_j ≤ u_{j+1} ≤ u_m`
on the grid. -/
theorem hQ_nonAltNg (hd : 0 < d) (hL : StepDecompGen_LoopForm Cm E) {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcmp : ∀ m, 0 ≤ gK m * sz.lam m ∧ gK m ^ 2 ≤ sz.lam m ^ 2 ∧ sz.lam m ^ 2 ≤ A * gK m ^ 2) (hA : 1 ≤ A)
    (hKer : NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n) (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : Ck ≤ Cv)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) {ε τ' D' D'' : ℝ}
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (k - 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - Ck) * ε)) (hD'' : (k : ℝ) + 1 < D'')
    {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (Γ Λ Φ : ℕ → ℝ) (hΛ : 0 ≤ Λ n) (m : ℕ) (hmK : m ≤ K n)
    (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrNg Cm n k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    ∀ M, GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' M → M.IsHermitian →
      gridStep s v K n * ((k : ℝ) * qvFormNg Cm n (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤
        (cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j : ℝ) := by
  intro M hM _
  have hΔ : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hu0 : 0 ≤ gridTime s v K n j := nqGood2_gridTime_nonneg hs0 hsv j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) := ST_gridTime_mono s v K n hsv (Nat.le_succ j)
  have hj1m : gridTime s v K n (j + 1) ≤ gridTime s v K n m := ST_gridTime_mono s v K n hsv (by omega)
  have hmv : gridTime s v K n m ≤ v n := nqGood2_gridTime_le hsv hmK
  have hs1 : s n ≤ gridTime s v K n (j + 1) := by
    have h := ST_gridTime_mono s v K n hsv (Nat.zero_le (j + 1))
    rwa [ST_gridTime_zero] at h
  have hj1v : gridTime s v K n (j + 1) ≤ v n := hj1m.trans hmv
  have hwin : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - gridTime s v K n m) / (1 - gridTime s v K n (j + 1)) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have hq := qvFormNg_le_of_goodSetNg_shift hd hL hm hS hcmp hA hKer hRow hCv hW hε0 hε1 hWε hdW hAk hD'' hu0 hjj hj1m (hmv.trans hwL)
    hwin hσ hΛ hM hδ a
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) hΔ

/-- **The field `hc_pos`** (band `cQVNonAltN_sum_pos`, `NQGood2:589`): `Σ_{j<m} c_j > 0` for `Δ > 0`, i.e. `s_n < v_n`, `K_n ≠ 0`
(`η_u ≥ 0` from `LoopForm`). -/
theorem cQVNonAltNg_sum_pos {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (Ck ε : ℝ) (hk : 1 ≤ k)
    (hsv : s n < v n) (hv1 : v n < 1) (hK : K n ≠ 0) (Γ Λ : ℕ → ℝ) (hΛ : 0 ≤ Λ n) (D'' : ℝ) :
    ∀ m, 1 ≤ m → m ≤ K n → ∀ a : Fin k → Zd d (sz.L n), 0 < ∑ j ∈ Finset.range m, (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' m a j : ℝ) := by
  intro m hm1 hmK a
  have hΔ : 0 < gridStep s v K n := div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hK)
  have hterm : ∀ j ∈ Finset.range m, 0 ≤ (cQVNonAltNg Cm s v K n k Ck ε Γ Λ D'' m a j : ℝ) := fun j _ => NNReal.coe_nonneg _
  have h0 : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm h0)
  have hu1 : gridTime s v K n (0 + 1) ≤ 1 := (nqGood2_gridTime_le hsv.le (show 0 + 1 ≤ K n by omega)).trans hv1.le
  have hpos := qvBdNonAltNg_pos Cm hL n (k := k) (Ck := Ck) (ε := ε) (Γ := Γ n) (D'' := D'') (u := gridTime s v K n (0 + 1))
    (w := gridTime s v K n m) hΛ hu1
  unfold cQVNonAltNg
  rw [Real.coe_toNNReal _ (mul_pos hΔ (mul_pos (by exact_mod_cast hk) hpos)).le]
  exact mul_pos hΔ (mul_pos (by exact_mod_cast hk) hpos)

end QVConst


/-! ## 4. The band re-derivation of `hQ_nonAltN` -/

/-! ## 5. Compiled nonempty instances (`d = 3`, band carrier `bandStep2Mat sz0 Einst`, `n = 0`)

Data of the band instances `NQGood2Inst` (public facts by name, private ones by `open private`): `sz0` (`L = 4`, `W = 32`, `lam = 1/64`), `E ≡ 1/2`, the
grid `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4` (`Δ = 1/128`, `u_j = j/128`), `k = 3`, `σ = (+,-,+)` (non-alternating), levels `(Γ, Λ, Φ) = (4, 3, 1)`,
`τ' = 1/5`, `D' = Dc = 6`, `D'' = 5`, `ε = 4/5`; the constant `Ck = Cv = nqGood1C 3 3 10 (1/2)` stays abstract (R1 with `A = 1`, `gK = lam`).
`H_0 = 0 ∈ GoodSetNg` at `u_0` (`zero_mem_goodSetN_inst_grid`, bridge `bandStep2_GoodSetN`); the exit time is `goodExitTauNg`, positive at every
sample.  The shift hypothesis is the band fact `delta_shift_ok`.  The pin `AzumaSubGNg` is the theorem `azumaSubGNg`; nothing is left open. -/

/-! ### Target 4: the vocabulary and (5.93) -/

/-! ### Target 5: the fields -/

/-! ### Target 6: the quadratic-variation constant -/

end RBM.BA

end
