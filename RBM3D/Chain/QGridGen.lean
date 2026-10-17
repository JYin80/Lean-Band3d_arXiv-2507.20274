/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QGridA
import RBM3D.Chain.HierDriftGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.NQGood1Gen

/-!
# The `𝒬`-grid layer of `int_K-L+Q` over the flow carrier (BA-U row U1s2a, file 1, ticket T2497)

Generic forms of `Induction/QGridA.lean` (not edited) over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: `3_5:1300-1346` (`int_K-L+Q`), `3_5:1204` (`Def:QtPt`).

* **Vocabulary** (target 1): `aTrueQNg`, `dGridQNg`, `aFrozQNg`, `martIncQNg`, `rGridQNg`, `lkEnvNg`, `driftEnvNg`, `qErrQNg`
  (`qStepErrN` is reused); the kernel is `Step2Gen_UN/ThetaN`, the law is `Cm.Pp`, the drift is `GridDriftNg`'s.
* **Kernel step** (target 2, private): the generator row bound `‖Θ_{u,σ} A‖ ≤ k (1-u)⁻¹ ‖A‖` from `HierDriftGen_UStep` at `Δ → 0`;
  one step of `𝒰` is `HierDriftGen_UN_step_le`.
* **Algebra** (targets 3-4, private): `QGridGen_qstep_algebra`, the drift envelope (`η ≤ 1` from `NQGood1Gen_eta_le_one`, inline `‖m‖ ≤ 1`).
* `QGridGen_condExp_aTrueQNg` (target 5), `gridDriftQNg_of`, `gridDriftQNg` (target 6), `stoppedDuhamelQNg` (target 7), instances (target 9).

Private band helpers that mention no band object are reused by `open private … from RBM3D.Induction.QGridA`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private QGridA_row_mul QGridA_Psum_add QGridA_Psum_mul QGridA_norm_Psum_le QGridA_norm_six_le QGridA_time_facts
  QGridA_loopOf_wf QGridA_loopOf_length QGridA_norm_ite_le QGridA_length_cutGlue QGridA_wf_cutGlue
  QGridA_vartheta_sup QGridA_vartheta_lip QGridA_gridTime_nonneg QGridA_gridTime_lt_one from RBM3D.Induction.QGridA

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal
open RBM.Ind (kStepC uStepC qStepErrN QGridA_Taylor2 QGridA_mollifier_taylor2)

/-! ## 1. The vocabulary (target 1) -/

section Vocab

/-- **`aTrueQNg`** (band `aTrueQN`, `QGridA:1263`): `A^Q_j = 𝒬_{u_j} A_j` with `AvecNg`. -/
def aTrueQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n j) (AvecNg Cm s t K n j σ ω)

/-- **`dGridQNg`** (band `dGridQN`, `QGridA:1274`): `𝒬_u D + ℬ₄ + ℬ₅` with the drift of `GridDriftNg` and the kernel
`Step2Gen_ThetaN`. -/
def dGridQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ (gridTime s t K n j)
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1),
            STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l (KLloopOf d (sz.L n) σ b) +
          STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b) +
          STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b)) a +
      (STQop (d := d) ϑ (gridTime s t K n j)
          (Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n j) (AvecNg Cm s t K n j σ ω)) a -
        Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n j)
          (STQop (d := d) ϑ (gridTime s t K n j) (AvecNg Cm s t K n j σ ω)) a) -
      STPsum (d := d) (AvecNg Cm s t K n j σ ω) (a 0) * deriv (fun τ => ϑ τ a) (gridTime s t K n j)

/-- **`aFrozQNg`** (band `aFrozQN`, `QGridA:1292`). -/
def aFrozQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (τ : PathΩ sz → ℕ) (j : ℕ)
    (ω : PathΩ sz) : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j)
    (aTrueQNg Cm s t K n ϑ σ (min j (τ ω)) ω)

/-- **`martIncQNg`** (band `martIncQN`, `QGridA:1299`); the law of the walk is `Cm.Pp`. -/
def martIncQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => aTrueQNg Cm s t K n ϑ σ (j + 1) ω a -
    MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω

/-- **`rGridQNg`** (band `rGridQN`, `QGridA:1307`): the one-step remainder, named as a difference. -/
def rGridQNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω -
    Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (aTrueQNg Cm s t K n ϑ σ j ω) a -
    (gridStep s t K n : ℂ) * dGridQNg Cm s t K n ϑ σ j ω a

/-- **`lkEnvNg`** (band `lkEnvN`, `QGridA:1319`): `etaT E u` read as `Cf.eta n u` (as `stepErrNg`). -/
def lkEnvNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n k : ℕ) (u Bk : ℝ) : ℝ :=
  (Cf.eta n u)⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk

/-- **`driftEnvNg`** (band `driftEnvN`, `QGridA:1326`). -/
def driftEnvNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n k : ℕ) (u Bk : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d *
    ((k : ℝ) * (2 * (k : ℝ) ^ 2 * (((Cf.eta n u)⁻¹ ^ k + Bk) * Bk)) +
      (k : ℝ) ^ 2 * (((Cf.eta n u)⁻¹ ^ k + Bk) * ((Cf.eta n u)⁻¹ ^ k + Bk)) +
      (k : ℝ) * (((Cf.eta n u)⁻¹ + 1) * (Cf.eta n u)⁻¹ ^ (k + 1)))

/-- **`qErrQNg`** (band `qErrQN`, `QGridA:1349`): the model-free `qStepErrN` at the three generic envelopes. -/
def qErrQNg {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (C C₂ Bk : ℝ)
    (j : ℕ) : ℝ :=
  qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
    (lkEnvNg Cf n (m + 1) (gridTime s t K n j) Bk)
    (driftEnvNg Cf n (m + 1) (gridTime s t K n j) Bk)
    (stepErrNg Cf n (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n) Bk)

end Vocab

/-! ## 2. The kernel step (target 2, private)

The generator row bound: `HierDriftGen_UStep` (a) and (b) give, for every `0 < Δ < 1 - u`,
`Δ Σ_b ‖θ_u(a,b)‖ ≤ Δ (1-u-Δ)⁻¹ + Δ² (1-u-Δ)⁻²`; let `Δ → 0⁺`. -/

section KernelStep

variable {d : ℕ} {sz : Sizes d}

/-- Row sums of the generator kernel `Step2Gen_thetaKer` are at most `(1-u)⁻¹` for `0 ≤ u < 1`. -/
private theorem QGridGen_row_thetaKer_le {C : FlowFM sz} {n : ℕ} (hU : HierDriftGen_UStep C n) (σ σ' : Bool)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Zd d (sz.L n)) :
    ∑ b, ‖Step2Gen_thetaKer C n σ σ' u a b‖ ≤ (1 - u)⁻¹ := by
  have hpos : 0 < 1 - u := by linarith
  set g : ℝ → ℝ := fun Δ => (1 - (u + Δ))⁻¹ + Δ * ((1 - (u + Δ))⁻¹) ^ 2 with hg
  have key : ∀ Δ : ℝ, 0 < Δ → Δ < 1 - u → ∑ b, ‖Step2Gen_thetaKer C n σ σ' u a b‖ ≤ g Δ := by
    intro Δ hΔ hΔ1
    have h1 := hU.1 σ σ' u (u + Δ) (by linarith) (by linarith) a
    have h2 := hU.2 σ σ' u Δ hu0 hΔ.le (by linarith) a
    rw [show u + Δ - u = Δ by ring, abs_of_pos hΔ] at h1
    have hb : ∀ b, Δ * ‖Step2Gen_thetaKer C n σ σ' u a b‖ ≤
        ‖Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ +
        ‖Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b -
          (Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b‖ := by
      intro b
      have e : (Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b =
          (Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b) -
          (Step2Gen_uKer C n σ σ' u (u + Δ) a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b -
            (Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b) := by ring
      have h0 : Δ * ‖Step2Gen_thetaKer C n σ σ' u a b‖ = ‖(Δ : ℂ) * Step2Gen_thetaKer C n σ σ' u a b‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ.le]
      rw [h0]
      exact le_of_eq_of_le (congrArg norm e) (norm_sub_le _ _)
    have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hb b
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have h3 : Δ * ∑ b, ‖Step2Gen_thetaKer C n σ σ' u a b‖ ≤ Δ * g Δ := by
      refine hsum.trans ?_
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      simp only [hg]; ring
    exact le_of_mul_le_mul_left h3 hΔ
  have hcont : ContinuousAt g 0 := by
    have h0 : (1 - (u + 0)) ≠ 0 := by rw [add_zero]; exact hpos.ne'
    simp only [hg]
    fun_prop (disch := exact h0)
  have hlim : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ Δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∑ b, ‖Step2Gen_thetaKer C n σ σ' u a b‖ ≤ g Δ := by
    filter_upwards [Ioo_mem_nhdsGT hpos] with Δ hΔ
    exact key Δ hΔ.1 hΔ.2
  have := ge_of_tendsto hlim hev
  simpa [hg] using this

/-- **The generator row bound** `‖Θ_{u,σ} A‖_max ≤ k (1-u)⁻¹ ‖A‖_max` (band `QGridA_norm_ThetaN_le`, `QGridA:1408`). -/
private theorem QGridGen_norm_ThetaN_le {C : FlowFM sz} {n : ℕ} (hU : HierDriftGen_UStep C n) {k : ℕ}
    (σ : Fin k → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {A : (Fin k → Zd d (sz.L n)) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_ThetaN C n σ u A a‖ ≤ (k : ℝ) * (1 - u)⁻¹ * M := by
  unfold Step2Gen_ThetaN
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin k, ‖∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b *
          A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (1 - u)⁻¹ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact QGridA_row_mul (P := Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u)
          (fun x => QGridGen_row_thetaKer_le hU _ _ hu0 hu1 x) (a i) (fun c => hA _)
    _ = (k : ℝ) * (1 - u)⁻¹ * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end KernelStep

/-! ## 3. The deterministic `𝒬` algebra of one step (target 3, private) -/

section QAlgebra

variable {d : ℕ} {sz : Sizes d}

/-- **The deterministic core of the one-step `𝒬`-identity** over the carrier (band `QGridA_qstep_algebra`, `QGridA:1447`): if
`c = 𝒰_{u,u+Δ} X + Δ D + e` with `‖e‖ ≤ S` and the mollifier satisfies `‖ϑ‖ ≤ C` at `u`, `u+Δ`, the Lipschitz bound and the
second-order Taylor bound between `u` and `u+Δ`, then `𝒬_{u+Δ} c - 𝒰_{u,u+Δ}(𝒬_u X) = Δ (𝒬_u D + [𝒬_u, Θ_{u,σ}] X - 𝒫X ∂_uϑ_u) + R`,
`‖R‖ ≤ qStepErrN`.  The kernel is `Step2Gen_UN/ThetaN` of the carrier; the row bounds are the class `HierDriftGen_UStep`. -/
private theorem QGridGen_qstep_algebra {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (n : ℕ)
    (hU : HierDriftGen_UStep Cf n) {m : ℕ} (hm : 1 ≤ m)
    (σ : Fin (m + 1) → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ) (hut1 : u + Δ < 1)
    {ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ} {C C₂ : ℝ}
    (hϑu : ∀ a, ‖ϑ u a‖ ≤ C) (hϑv : ∀ a, ‖ϑ (u + Δ) a‖ ≤ C)
    (hlip : ∀ a, ‖ϑ (u + Δ) a - ϑ u a‖ ≤ C * (1 - (u + Δ))⁻¹ * Δ)
    (htay : ∀ a, ‖ϑ (u + Δ) a - ϑ u a - (Δ : ℂ) * deriv (fun τ => ϑ τ a) u‖ ≤
      C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2)
    {X D c : (Fin (m + 1) → Zd d (sz.L n)) → ℂ} {Mk Dm S : ℝ} (hX : ∀ b, ‖X b‖ ≤ Mk)
    (hD : ∀ b, ‖D b‖ ≤ Dm)
    (hc : ∀ b, ‖c b - Step2Gen_UN Cf n σ u (u + Δ) X b - (Δ : ℂ) * D b‖ ≤ S)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    ‖STQop (d := d) ϑ (u + Δ) c a - Step2Gen_UN Cf n σ u (u + Δ) (STQop (d := d) ϑ u X) a -
        (Δ : ℂ) * (STQop (d := d) ϑ u D a +
          (STQop (d := d) ϑ u (Step2Gen_ThetaN Cf n σ u X) a -
            Step2Gen_ThetaN Cf n σ u (STQop (d := d) ϑ u X) a) -
          STPsum (d := d) X (a 0) * deriv (fun τ => ϑ τ a) u)‖ ≤
      qStepErrN d (sz.L n) m C C₂ u Δ Mk Dm S := by
  have hu1 : u < 1 := by linarith
  have hv0 : 0 ≤ u + Δ := by linarith
  have hMk0 : 0 ≤ Mk := (norm_nonneg _).trans (hX a)
  have hDm0 : 0 ≤ Dm := (norm_nonneg _).trans (hD a)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hc a)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hϑu a)
  set Lp : ℝ := (((sz.L n : ℕ) : ℝ) ^ d) ^ m with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  set Ust : ℝ := uStepC (m + 1) Δ (u + Δ) with hUst
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβ
  have hβ0 : 0 ≤ β := inv_nonneg.mpr (by linarith)
  have hβu : (1 - u)⁻¹ ≤ β := inv_anti₀ (by linarith) (by linarith)
  have hβu0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr (by linarith)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  -- the objects
  set Y : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b => STPsum (d := d) X (b 0) * ϑ u b with hY
  set e : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
    fun b => c b - Step2Gen_UN Cf n σ u (u + Δ) X b - (Δ : ℂ) * D b with he
  set εX : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b =>
    Step2Gen_UN Cf n σ u (u + Δ) X b - X b -
      (Δ : ℂ) * Step2Gen_ThetaN Cf n σ u X b with hεX
  set εY : (Fin (m + 1) → Zd d (sz.L n)) → ℂ := fun b =>
    Step2Gen_UN Cf n σ u (u + Δ) Y b - Y b -
      (Δ : ℂ) * Step2Gen_ThetaN Cf n σ u Y b with hεY
  have hUst0 : 0 ≤ Ust := by
    unfold Ust uStepC
    have hx0 : 0 ≤ Δ * (1 - (u + Δ))⁻¹ := mul_nonneg hΔ0 hβ0
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - (u + Δ))⁻¹ by linarith) (m + 1)
    have e1 : 0 ≤ ((m + 1 : ℕ) : ℝ) * Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by positivity
    nlinarith [hb]
  have hεXb : ∀ b, ‖εX b‖ ≤ Ust * Mk := fun b =>
    HierDriftGen_UN_step_le Cf n hU σ hu0 hΔ0 hut1 X Mk hX b
  have hYb : ∀ b, ‖Y b‖ ≤ Lp * Mk * C := fun b => by
    simp only [hY]
    rw [norm_mul]
    exact mul_le_mul (QGridA_norm_Psum_le hX _) (hϑu b) (norm_nonneg _) (by positivity)
  have hεYb : ∀ b, ‖εY b‖ ≤ Ust * (Lp * Mk * C) := fun b =>
    HierDriftGen_UN_step_le Cf n hU σ hu0 hΔ0 hut1 Y (Lp * Mk * C) hYb b
  have heb : ∀ b, ‖e b‖ ≤ S := hc
  -- the `STPsum` identities
  have h4 : STPsum (d := d) (Step2Gen_UN Cf n σ u (u + Δ) X) (a 0) = STPsum (d := d) X (a 0) +
      (Δ : ℂ) * STPsum (d := d) (Step2Gen_ThetaN Cf n σ u X) (a 0) +
        STPsum (d := d) εX (a 0) := by
    have h1 : (fun b => Step2Gen_UN Cf n σ u (u + Δ) X b) =
        fun b => (X b + (Δ : ℂ) * Step2Gen_ThetaN Cf n σ u X b) + εX b := by
      funext b; simp only [hεX]; ring
    calc STPsum (d := d) (Step2Gen_UN Cf n σ u (u + Δ) X) (a 0)
        = STPsum (d := d) (fun b => (X b + (Δ : ℂ) * Step2Gen_ThetaN Cf n σ u X b) + εX b) (a 0) := by
          rw [← h1]
      _ = _ := by
          rw [QGridA_Psum_add, QGridA_Psum_add, QGridA_Psum_mul]
  have h3 : STPsum (d := d) c (a 0) = STPsum (d := d) e (a 0) +
      STPsum (d := d) (Step2Gen_UN Cf n σ u (u + Δ) X) (a 0) + (Δ : ℂ) * STPsum (d := d) D (a 0) := by
    have h1 : (fun b => c b) = fun b => (e b + Step2Gen_UN Cf n σ u (u + Δ) X b) + (Δ : ℂ) * D b := by
      funext b; simp only [he]; ring
    calc STPsum (d := d) c (a 0)
        = STPsum (d := d) (fun b => (e b + Step2Gen_UN Cf n σ u (u + Δ) X b) + (Δ : ℂ) * D b) (a 0) := by
          rw [← h1]
      _ = _ := by
          rw [QGridA_Psum_add, QGridA_Psum_add, QGridA_Psum_mul]
  have hQX : STQop (d := d) ϑ u X = fun b => X b - Y b := rfl
  have h5 : Step2Gen_UN Cf n σ u (u + Δ) (STQop (d := d) ϑ u X) a =
      Step2Gen_UN Cf n σ u (u + Δ) X a - Step2Gen_UN Cf n σ u (u + Δ) Y a := by
    rw [hQX]; exact QopAlgebra_UN_subg Cf n σ u (u + Δ) X Y a
  have h6 : Step2Gen_ThetaN Cf n σ u (STQop (d := d) ϑ u X) a =
      Step2Gen_ThetaN Cf n σ u X a -
        Step2Gen_ThetaN Cf n σ u Y a := by
    rw [hQX]; exact QopAlgebra_ThetaN_subg Cf n σ u X Y a
  -- the exact identity
  have key : STQop (d := d) ϑ (u + Δ) c a -
      Step2Gen_UN Cf n σ u (u + Δ) (STQop (d := d) ϑ u X) a -
      (Δ : ℂ) * (STQop (d := d) ϑ u D a +
        (STQop (d := d) ϑ u (Step2Gen_ThetaN Cf n σ u X) a -
          Step2Gen_ThetaN Cf n σ u (STQop (d := d) ϑ u X) a) -
        STPsum (d := d) X (a 0) * deriv (fun τ => ϑ τ a) u) =
      (e a - STPsum (d := d) e (a 0) * ϑ (u + Δ) a) +
        (Δ : ℂ) * STPsum (d := d) D (a 0) * (ϑ u a - ϑ (u + Δ) a) +
        STPsum (d := d) X (a 0) * (ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u) +
        (Δ : ℂ) * STPsum (d := d) (Step2Gen_ThetaN Cf n σ u X) (a 0) *
          (ϑ u a - ϑ (u + Δ) a) +
        εY a - STPsum (d := d) εX (a 0) * ϑ (u + Δ) a := by
    rw [h5, h6]
    simp only [STQop]
    have hYa : Y a = STPsum (d := d) X (a 0) * ϑ u a := rfl
    have hea : e a = c a - Step2Gen_UN Cf n σ u (u + Δ) X a - (Δ : ℂ) * D a := rfl
    have hεYa : εY a = Step2Gen_UN Cf n σ u (u + Δ) Y a - Y a -
        (Δ : ℂ) * Step2Gen_ThetaN Cf n σ u Y a := rfl
    linear_combination (-1 : ℂ) * hea + (-1 : ℂ) * hεYa + (1 : ℂ) * hYa +
      (-(ϑ (u + Δ) a)) * h3 + (-(ϑ (u + Δ) a)) * h4
  rw [key]
  -- the bounds on `ϑ`
  have hVd : ‖ϑ u a - ϑ (u + Δ) a‖ ≤ C * β * Δ := by
    rw [norm_sub_rev]; exact hlip a
  have hτB : ‖ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u‖ ≤
      C₂ * β ^ 2 * Δ ^ 2 := by
    have e' : ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u =
        -(ϑ (u + Δ) a - ϑ u a - (Δ : ℂ) * deriv (fun τ => ϑ τ a) u) := by ring
    rw [e', norm_neg]
    exact htay a
  have hPe : ‖STPsum (d := d) e (a 0)‖ ≤ Lp * S := QGridA_norm_Psum_le heb _
  have hPD : ‖STPsum (d := d) D (a 0)‖ ≤ Lp * Dm := QGridA_norm_Psum_le hD _
  have hPX : ‖STPsum (d := d) X (a 0)‖ ≤ Lp * Mk := QGridA_norm_Psum_le hX _
  have hΘX : ∀ b, ‖Step2Gen_ThetaN Cf n σ u X b‖ ≤ ((m + 1 : ℕ) : ℝ) * β * Mk :=
    fun b =>
      (QGridGen_norm_ThetaN_le hU σ hu0 hu1 hX b).trans (by
        have h0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * Mk := by positivity
        calc ((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk = (((m + 1 : ℕ) : ℝ) * Mk) * (1 - u)⁻¹ := by ring
          _ ≤ (((m + 1 : ℕ) : ℝ) * Mk) * β := mul_le_mul_of_nonneg_left hβu h0
          _ = ((m + 1 : ℕ) : ℝ) * β * Mk := by ring)
  have hPΘ : ‖STPsum (d := d) (Step2Gen_ThetaN Cf n σ u X) (a 0)‖ ≤
      Lp * (((m + 1 : ℕ) : ℝ) * β * Mk) := QGridA_norm_Psum_le hΘX _
  have hPεX : ‖STPsum (d := d) εX (a 0)‖ ≤ Lp * (Ust * Mk) := QGridA_norm_Psum_le hεXb _
  have hϑva := hϑv a
  have hVd0 : 0 ≤ C * β * Δ := by positivity
  have t1 : ‖e a - STPsum (d := d) e (a 0) * ϑ (u + Δ) a‖ ≤ (1 + C * Lp) * S := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖STPsum (d := d) e (a 0)‖ * ‖ϑ (u + Δ) a‖ ≤ (Lp * S) * C :=
      mul_le_mul hPe hϑva (norm_nonneg _) (by positivity)
    have := heb a
    nlinarith
  have t2 : ‖(Δ : ℂ) * STPsum (d := d) D (a 0) * (ϑ u a - ϑ (u + Δ) a)‖ ≤
      Δ * (Lp * Dm) * (C * β * Δ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPD hΔ0) hVd (norm_nonneg _) (by positivity)
  have t3 : ‖STPsum (d := d) X (a 0) *
      (ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u)‖ ≤
      Lp * Mk * (C₂ * β ^ 2 * Δ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hPX hτB (norm_nonneg _) (by positivity)
  have t4 : ‖(Δ : ℂ) * STPsum (d := d) (Step2Gen_ThetaN Cf n σ u X) (a 0) *
      (ϑ u a - ϑ (u + Δ) a)‖ ≤
      Δ * (Lp * (((m + 1 : ℕ) : ℝ) * β * Mk)) * (C * β * Δ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPΘ hΔ0) hVd (norm_nonneg _) (by positivity)
  have t5 : ‖εY a‖ ≤ Ust * (Lp * Mk * C) := hεYb a
  have t6 : ‖STPsum (d := d) εX (a 0) * ϑ (u + Δ) a‖ ≤ Lp * (Ust * Mk) * C := by
    rw [norm_mul]
    exact mul_le_mul hPεX hϑva (norm_nonneg _) (by positivity)
  refine (QGridA_norm_six_le _ _ _ _ _ _).trans ?_
  unfold qStepErrN
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at t4
  linarith [t1, t2, t3, t4, t5, t6]

end QAlgebra

/-! ## 4. The deterministic envelope of the drift (target 4, private)

With `η = η_u`, `B_F = η^{-k} + Bk`: `|𝓛-𝒦| ≤ B_F` on the loops of length `2..k`, `|𝓛| ≤ η^{-(k+1)}` on the loops of length
`k+1`, `|avgErr| ≤ η⁻¹ + 1`.  The inputs are `StepDecompGen_LoopForm`, the inline `‖m‖ ≤ 1` (`η ≤ 1` by `NQGood1Gen_eta_le_one`) and the
row sums `Σ_b ‖S_ab‖ ≤ 1` of the carrier kernel (the band has `= 1`). -/

/-- Well-formedness and length of the cyclic loop `KLloopOf` (band `QGridA_loopOf_wf`, `_length`; `KLloopOf` is the band `loopOf`). -/
private theorem QGridGen_KL_wf {d L k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) : (KLloopOf d L σ a).WF :=
  QGridA_loopOf_wf σ a

private theorem QGridGen_KL_length {d L k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    (KLloopOf d L σ a).length = k := QGridA_loopOf_length σ a

section DriftEnv

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E : ℕ → ℝ}

/-- `|𝓛_{u,I}| ≤ η^{-|I|} (W^{-d})^{|I|-1}` for a Hermitian fine matrix `H` (copy of `HierDriftGen_norm_LIM_le` at any `H`). -/
private theorem QGridGen_norm_LIM_le (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u : ℝ} (hu : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    (I : LoopIdx (Zd d (sz.L n))) (hwf : I.WF) (hn : 1 ≤ I.length) :
    ‖STLIMg Cm n u H I‖ ≤ (Cm.eta n u)⁻¹ ^ I.length * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (I.length - 1) := by
  obtain ⟨hη, hz⟩ := HierDriftGen_eta_facts hL n hu
  simp only [STLIMg]
  rw [(hL n).2.2.1]
  exact RBM.Ind.norm_gloop_le_of_le_abs_im (hH.submatrix _) hη hz I hwf hn

/-- `|𝓛_{u,J}| ≤ η^{-K'}` for a well-formed loop `J` of length `1 ≤ |J| ≤ K'` (band `QGridA_norm_STLIM_le`). -/
private theorem QGridGen_norm_STLIM_le (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (hm : ‖Cm.m n‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) {J : LoopIdx (Zd d (sz.L n))} (hJ : J.WF) {K' : ℕ} (h1 : 1 ≤ J.length)
    (hK' : J.length ≤ K') : ‖STLIMg Cm n u H J‖ ≤ (Cm.eta n u)⁻¹ ^ K' := by
  have hη : 0 < Cm.eta n u := (HierDriftGen_eta_facts hL n hu1).1
  have h := QGridGen_norm_LIM_le hL n hu1 hH J hJ h1
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (J.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have hone : 1 ≤ (Cm.eta n u)⁻¹ := (one_le_inv₀ hη).2 (NQGood1Gen_eta_le_one hL hm hu0)
  calc ‖STLIMg Cm n u H J‖ ≤ (Cm.eta n u)⁻¹ ^ J.length * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (J.length - 1) := h
    _ ≤ (Cm.eta n u)⁻¹ ^ J.length * 1 := mul_le_mul_of_nonneg_left hWi (by positivity)
    _ = (Cm.eta n u)⁻¹ ^ J.length := mul_one _
    _ ≤ (Cm.eta n u)⁻¹ ^ K' := pow_le_pow_right₀ hone hK'

/-- `|avgErr| ≤ η⁻¹ + 1` (`|𝓛_{(σ),(a)}| ≤ η⁻¹`, `‖m(σ)‖ ≤ 1`; band `QGridA_norm_avgErr_le`). -/
private theorem QGridGen_norm_avgErr_le (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (hm : ‖Cm.m n‖ ≤ 1) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (s : Bool) (a : Zd d (sz.L n)) :
    ‖STavgErrMg Cm n u H s a‖ ≤ (Cm.eta n u)⁻¹ + 1 := by
  unfold STavgErrMg
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have h := QGridGen_norm_STLIM_le hL n hm hu0 hu1 hH (J := ⟨[s], [a]⟩) (K' := 1)
      (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length])
    simpa using h
  · unfold STmsigg
    split_ifs
    · exact hm
    · rw [Complex.norm_conj]; exact hm

/-- The graded cut coupling `[𝒦∼(𝓛-𝒦)]^l` is a sum of two `primBilS`s with the `𝒦` restricted to the loops of length `l`
(band `QGridA_ksimLK_eq`). -/
private theorem QGridGen_ksimLK_eq (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    STksimLKMg Cm n u H l I =
      primBilS d (sz.L n) (sz.W n) (Cm.S n) (STLKIMg Cm n u H)
          (fun J => if J.length = l then Cm.KI n u J else 0) I +
        primBilS d (sz.L n) (sz.W n) (Cm.S n)
          (fun J => if J.length = l then Cm.KI n u J else 0) (STLKIMg Cm n u H) I := by
  unfold STksimLKMg primBilS
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]

private theorem QGridGen_norm_ksimLK_le (n : ℕ) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {I : LoopIdx (Zd d (sz.L n))} (hI : I.WF) (l : ℕ) {BF Bk : ℝ} (hBF0 : 0 ≤ BF) (hBk0 : 0 ≤ Bk)
    (hF : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖STLKIMg Cm n u H J‖ ≤ BF)
    (hK : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖Cm.KI n u J‖ ≤ Bk) :
    ‖STksimLKMg Cm n u H l I‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * (I.length : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk) := by
  rw [QGridGen_ksimLK_eq]
  refine (norm_add_le _ _).trans ?_
  have hKl : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖(fun J : LoopIdx (Zd d (sz.L n)) => if J.length = l then Cm.KI n u J else 0) J‖ ≤ Bk :=
    fun J h1 h2 h3 => (QGridA_norm_ite_le _ _).trans (hK J h1 h2 h3)
  have h1 := norm_primBilS_le d (sz.L n) (sz.W n) (Cm.S n) hS (STLKIMg Cm n u H)
    (fun J => if J.length = l then Cm.KI n u J else 0) I hI hBF0 hBk0 hF hKl
  have h2 := norm_primBilS_le d (sz.L n) (sz.W n) (Cm.S n) hS
    (fun J => if J.length = l then Cm.KI n u J else 0) (STLKIMg Cm n u H) I hI hBk0 hBF0 hKl hF
  linarith [h1, h2]

private theorem QGridGen_norm_elklk_le (n : ℕ) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {I : LoopIdx (Zd d (sz.L n))} (hI : I.WF) {BF : ℝ} (hBF0 : 0 ≤ BF)
    (hF : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖STLKIMg Cm n u H J‖ ≤ BF) :
    ‖STelklkMg Cm n u H I‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (I.length : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * BF :=
  norm_primBilS_le d (sz.L n) (sz.W n) (Cm.S n) hS (STLKIMg Cm n u H) (STLKIMg Cm n u H) I hI hBF0 hBF0 hF hF

/-- `‖𝓔^{(G̃)}‖ ≤ W^d k L^d (η⁻¹ + 1) η^{-(k+1)}` (one row of `S` per cut; band `QGridA_norm_egtN_le`). -/
private theorem QGridGen_norm_egt_le (hL : StepDecompGen_LoopForm Cm E)
    (n : ℕ) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hm : ‖Cm.m n‖ ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {I : LoopIdx (Zd d (sz.L n))} (hI : I.WF) {k : ℕ} (hk : I.length = k) :
    ‖STegtMg Cm n u H I‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
        (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)))) := by
  unfold STegtMg
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  have hη : 0 < Cm.eta n u := (HierDriftGen_eta_facts hL n hu1).1
  have hη0 : 0 ≤ (Cm.eta n u)⁻¹ := inv_nonneg.2 hη.le
  have hone : ∀ k' ∈ Finset.Icc 1 I.length,
      ‖∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), STavgErrMg Cm n u H (I.σ.getD (k' - 1) false) a *
        Cm.S n a b * STLIMg Cm n u H (I.cutGlue k' b)‖ ≤
      ((sz.L n : ℕ) : ℝ) ^ d * (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) := by
    intro k' hk'
    rw [Finset.mem_Icc] at hk'
    have hBG : ∀ b : Zd d (sz.L n), ‖STLIMg Cm n u H (I.cutGlue k' b)‖ ≤ (Cm.eta n u)⁻¹ ^ (k + 1) := by
      intro b
      have hJ := QGridA_wf_cutGlue hI b hk'.1 hk'.2
      have hlen := QGridA_length_cutGlue I b hk'.2
      exact QGridGen_norm_STLIM_le hL n hm hu0 hu1 hH hJ (by omega) (by omega)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a : Zd d (sz.L n), ‖∑ b : Zd d (sz.L n), STavgErrMg Cm n u H (I.σ.getD (k' - 1) false) a *
          Cm.S n a b * STLIMg Cm n u H (I.cutGlue k' b)‖
        ≤ ∑ _a : Zd d (sz.L n), (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine (norm_sum_le _ _).trans ?_
          calc ∑ b : Zd d (sz.L n), ‖STavgErrMg Cm n u H (I.σ.getD (k' - 1) false) a *
                Cm.S n a b * STLIMg Cm n u H (I.cutGlue k' b)‖
              ≤ ∑ b : Zd d (sz.L n), (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) *
                  ‖Cm.S n a b‖ := by
                refine Finset.sum_le_sum fun b _ => ?_
                rw [norm_mul, norm_mul]
                have h1 := QGridGen_norm_avgErr_le hL n hm hu0 hu1 hH (I.σ.getD (k' - 1) false) a
                have h2 := hBG b
                calc ‖STavgErrMg Cm n u H (I.σ.getD (k' - 1) false) a‖ *
                      ‖Cm.S n a b‖ * ‖STLIMg Cm n u H (I.cutGlue k' b)‖
                    ≤ ((Cm.eta n u)⁻¹ + 1) * ‖Cm.S n a b‖ * (Cm.eta n u)⁻¹ ^ (k + 1) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
                        (norm_nonneg _) (by positivity)
                  _ = (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) * ‖Cm.S n a b‖ := by ring
            _ = (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) * ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ := by
                rw [Finset.mul_sum]
            _ ≤ (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) * 1 :=
                mul_le_mul_of_nonneg_left (hS a) (by positivity)
            _ = (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) := mul_one _
      _ = ((sz.L n : ℕ) : ℝ) ^ d * (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          ring
  calc ∑ k' ∈ Finset.Icc 1 I.length,
        ‖∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), STavgErrMg Cm n u H (I.σ.getD (k' - 1) false) a *
          Cm.S n a b * STLIMg Cm n u H (I.cutGlue k' b)‖
      ≤ ∑ _k' ∈ Finset.Icc 1 I.length,
          ((sz.L n : ℕ) : ℝ) ^ d * (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)) :=
        Finset.sum_le_sum hone
    _ = (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d * (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hk]
        simp

/-- **The drift envelope** (band `QGridA_norm_drift_le`, `QGridA:1811`): for every Hermitian grid state `H`, every sign vector and
label, with the `𝒦` envelope `Bk` at the time `u`, `|Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}| ≤ driftEnvNg`. -/
private theorem QGridGen_norm_drift_le (hL : StepDecompGen_LoopForm Cm E)
    (n : ℕ) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hm : ‖Cm.m n‖ ≤ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k → ‖Cm.KI n u J‖ ≤ Bk)
    (a : Fin k → Zd d (sz.L n)) :
    ‖∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l (KLloopOf d (sz.L n) σ a) +
        STelklkMg Cm n u H (KLloopOf d (sz.L n) σ a) + STegtMg Cm n u H (KLloopOf d (sz.L n) σ a)‖ ≤
      driftEnvNg Cm.toFlowFM n k u Bk := by
  have hI : (KLloopOf d (sz.L n) σ a).WF := QGridGen_KL_wf σ a
  have hlen : (KLloopOf d (sz.L n) σ a).length = k := QGridGen_KL_length σ a
  have hη : 0 < Cm.eta n u := (HierDriftGen_eta_facts hL n hu1).1
  have hη0 : 0 ≤ (Cm.eta n u)⁻¹ := inv_nonneg.2 hη.le
  set BF : ℝ := (Cm.eta n u)⁻¹ ^ k + Bk with hBF
  have hBF0 : 0 ≤ BF := by positivity
  have hF : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ (KLloopOf d (sz.L n) σ a).length →
      ‖STLKIMg Cm n u H J‖ ≤ BF := by
    intro J hJ h2 hJk
    rw [hlen] at hJk
    unfold STLKIMg
    exact (norm_sub_le _ _).trans (add_le_add
      (QGridGen_norm_STLIM_le hL n hm hu0 hu1 hH hJ (by omega) hJk) (hBk J hJ h2 hJk))
  have hK : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ (KLloopOf d (sz.L n) σ a).length →
      ‖Cm.KI n u J‖ ≤ Bk := fun J hJ h2 hJk => hBk J hJ h2 (hlen ▸ hJk)
  have h1 : ‖∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l (KLloopOf d (sz.L n) σ a)‖ ≤
      (k : ℝ) * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l ∈ Finset.Icc 3 k, ‖STksimLKMg Cm n u H l (KLloopOf d (sz.L n) σ a)‖
        ≤ ∑ _l ∈ Finset.Icc 3 k,
            (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) :=
          Finset.sum_le_sum fun l _ => by
            have := QGridGen_norm_ksimLK_le n hS u H hI l hBF0 hBk0 hF hK
            rwa [hlen] at this
      _ = ((Finset.Icc 3 k).card : ℝ) *
            (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : k + 1 - 3 ≤ k)
  have h2 : ‖STelklkMg Cm n u H (KLloopOf d (sz.L n) σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * BF := by
    have := QGridGen_norm_elklk_le n hS u H hI hBF0 hF
    rwa [hlen] at this
  have h3 := QGridGen_norm_egt_le hL n hS hm hu0 hu1 hH hI hlen
  calc _ ≤ ‖∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l (KLloopOf d (sz.L n) σ a)‖ +
        ‖STelklkMg Cm n u H (KLloopOf d (sz.L n) σ a)‖ + ‖STegtMg Cm n u H (KLloopOf d (sz.L n) σ a)‖ :=
        norm_add₃_le
    _ ≤ (k : ℝ) * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) +
        ((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * BF +
        ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
          (((Cm.eta n u)⁻¹ + 1) * (Cm.eta n u)⁻¹ ^ (k + 1)))) := by linarith [h1, h2, h3]
    _ = driftEnvNg Cm.toFlowFM n k u Bk := by
        unfold driftEnvNg
        rw [hBF]
        ring

end DriftEnv

/-! ## 5. Integrability and `𝔼[·| F_j]` of the `𝒬`-process (targets 3, 5) -/

section CondExp

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- Every label of `A_i = (𝓛 - 𝒦)_{u_i,σ}` along the carrier walk is integrable (band `QGridA_integrable_AvecN`):
`HierDriftGen_integrable_LIM` (the walk is Hermitian by `WalkForm`, `|Im z| = η > 0` by `LoopForm`), minus the constant `𝒦`. -/
private theorem QGridGen_integrable_AvecNg (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (hKK : HierDriftGen_KLink Cm n) (hi0 : 0 ≤ gridTime s t K n i)
    (hi1 : gridTime s t K n i < 1) {k : ℕ} (σ : Fin k → Bool) (hk : 1 ≤ k) (b : Fin k → Zd d (sz.L n)) :
    Integrable (fun ω : PathΩ sz => AvecNg Cm s t K n i σ ω b) Cm.Pp := by
  have : IsProbabilityMeasure Cm.Pp := by rw [hW.2.1]; exact isProbabilityMeasure_pathP _
  have hint := HierDriftGen_integrable_LIM hL hW s t K n i hi1 (KLloopOf d (sz.L n) σ b) (QGridGen_KL_wf σ b)
    (by rw [QGridGen_KL_length]; exact hk)
  have h2 := hint.sub (integrable_const (Cm.KI n (gridTime s t K n i) (KLloopOf d (sz.L n) σ b)))
  refine h2.congr (Eventually.of_forall fun ω => ?_)
  simp only [AvecNg, STLKMg, STLMg, Pi.sub_apply]
  rw [HierDriftGen_LM_eq_LIM hL, hKK _ ⟨hi0, hi1⟩ k σ b]

/-- **Target 5, `QGridGen_condExp_aTrueQNg`** (band `QGridA_condExp_aTrueQN`, `QGridA:1906`): `𝔼[·| F_j]` commutes with
`𝒬_{u_{j+1}}`, a.e., label by label: `𝔼[A^Q_{j+1}(a) | F_j] = (𝒬_{u_{j+1}} c)(a)`, `c_b = 𝔼[A_{j+1}(b) | F_j]`. -/
theorem QGridGen_condExp_aTrueQNg (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hKK : HierDriftGen_KLink Cm n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∀ᵐ ω ∂(Cm.Pp), MeasureTheory.condExp (filt sz j) Cm.Pp
        (fun ω' => aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω =
      STQop (d := d) ϑ (gridTime s t K n (j + 1))
        (fun b => MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b) ω) a := by
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := QGridA_time_facts s t K n j hs0 hst ht1 hK hj
  have hv0 : 0 ≤ gridTime s t K n (j + 1) := by rw [hvu]; linarith
  have : IsProbabilityMeasure Cm.Pp := by rw [hW.2.1]; exact isProbabilityMeasure_pathP _
  have hk1 : 1 ≤ m + 1 := by omega
  have hInt := QGridGen_integrable_AvecNg hL hW s t K n (j + 1) hKK hv0 hv1 σ hk1
  set F : Finset (Fin (m + 1) → Zd d (sz.L n)) :=
    Finset.univ.filter (fun b : Fin (m + 1) → Zd d (sz.L n) => b 0 = a 0) with hF
  have hfun : (fun ω' => aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) =
      (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' a) -
        ϑ (gridTime s t K n (j + 1)) a •
          ∑ b ∈ F, (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b) := by
    funext ω'
    simp only [aTrueQNg, STQop, STPsum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    ring
  have hsumInt : Integrable (∑ b ∈ F, (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b)) Cm.Pp :=
    integrable_finsetSum' F fun b _ => hInt b
  rw [hfun]
  filter_upwards [condExp_sub (hInt a)
      (hsumInt.smul (ϑ (gridTime s t K n (j + 1)) a)) (filt sz j),
    condExp_smul (ϑ (gridTime s t K n (j + 1)) a)
      (∑ b ∈ F, (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b)) (filt sz j),
    condExp_finsetSum (fun b _ => hInt b) (filt sz j)] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Finset.sum_apply, smul_eq_mul]
  simp only [STQop, STPsum]
  ring

end CondExp

/-! ## 6. The one-step identity of `int_K-L+Q` (target 6) -/

section GridDriftQ

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
  {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- **`gridDriftQNg_of`** (band `QGridA_gridDriftQN_of`, `QGridA:2007`): the one-step identity of `int_K-L+Q` for every `ϑ` with
`STMollifierProps (sz.lam n) C c ϑ`, differentiable on `[0, 1)` and satisfying the second-order Taylor bound.  One index `n`, one
step `j`: the per-index classes of T5s2 (`Expand`, `KLoop`, `KTwo`, `UStep`, the row sums, the link) and the inline `‖m‖ ≤ 1`. -/
theorem gridDriftQNg_of (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool) (Bk : ℝ)
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hExp : HierDriftGen_Expand Cm s t K n) (hKL : HierDriftGen_KLoop Cm n) (hKT : HierDriftGen_KTwo Cm n)
    (hU : HierDriftGen_UStep Cm.toFlowFM n) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hKK : HierDriftGen_KLink Cm n) (hm1 : ‖Cm.m n‖ ≤ 1)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) (hm : 1 ≤ m) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 1 → ‖Cm.KI n w J‖ ≤ Bk)
    {C c C₂ : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hdiff : ∀ τ : ℝ, 0 ≤ τ → τ < 1 → ∀ a, DifferentiableAt ℝ (fun τ' => ϑ τ' a) τ)
    (hTay : QGridA_Taylor2 C₂ ϑ) :
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin (m + 1) → Zd d (sz.L n),
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => aTrueQNg Cm s t K n ϑ σ (j + 1) ω' a) ω -
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
            (aTrueQNg Cm s t K n ϑ σ j ω) a -
          (gridStep s t K n : ℂ) * dGridQNg Cm s t K n ϑ σ j ω a‖ ≤
        qErrQNg Cm.toFlowFM s t K n m C C₂ Bk j := by
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := QGridA_time_facts s t K n j hs0 hst ht1 hK hj
  have hkpos : 1 ≤ m + 1 := by omega
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hT := gridDriftNg_at hL hW s t K n j hExp hKL hKT hU hS hKK hs0 hst ht1 hK hj (k := m + 1) (by omega) σ Bk
    hBk hB
  have hlin' := ae_all_iff.2 fun a =>
    QGridGen_condExp_aTrueQNg hL hW s t K n j hKK hs0 hst ht1 hK hj ϑ σ a
  have hBk' : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ m + 1 →
      ‖Cm.KI n (gridTime s t K n j) J‖ ≤ Bk :=
    fun J hJ h2 hJk => hB _ ⟨hu0, by rw [hvu]; linarith⟩ J hJ h2 hJk
  have hL1 : 1 ≤ sz.L n := by have := sz.three_le_L n; omega
  have hϑu : ∀ a, ‖ϑ (gridTime s t K n j) a‖ ≤ C := fun a =>
    QGridA_vartheta_sup hL1 hC hc hϑ hu0 hu1 a
  have hϑv : ∀ a, ‖ϑ (gridTime s t K n j + gridStep s t K n) a‖ ≤ C := fun a =>
    QGridA_vartheta_sup hL1 hC hc hϑ (by linarith) (by rw [← hvu]; exact hv1) a
  have hlip := fun a => QGridA_vartheta_lip hL1 hC hϑ hdiff hu0 hΔ0 (by rw [← hvu]; exact hv1) a
  have htay := fun a => hTay _ _ hu0 hΔ0 (by rw [← hvu]; exact hv1) a
  filter_upwards [hT, hlin'] with ω hTω hlinω a
  have hH : (Cm.Hpath s t K n j ω).IsHermitian := by
    rw [StepDecompGen_Hpath_eq hW]
    exact (hW.1 n).add (pathH_isHermitian (sz.withLam lam') s t K n j ω)
  have hAj : ∀ b : Fin (m + 1) → Zd d (sz.L n), AvecNg Cm s t K n j σ ω b =
      STLIMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b) -
        Cm.KI n (gridTime s t K n j) (KLloopOf d (sz.L n) σ b) := by
    intro b
    simp only [AvecNg, STLKMg, STLMg]
    rw [HierDriftGen_LM_eq_LIM hL, hKK _ ⟨hu0, hu1⟩ (m + 1) σ b]
  -- the sup bound on `A_j`
  have hX : ∀ b : Fin (m + 1) → Zd d (sz.L n), ‖AvecNg Cm s t K n j σ ω b‖ ≤
      lkEnvNg Cm.toFlowFM n (m + 1) (gridTime s t K n j) Bk := by
    intro b
    have h1 := HierDriftGen_norm_LIM_le hL hW s t K n j hu1 ω (KLloopOf d (sz.L n) σ b) (QGridGen_KL_wf σ b)
      (by rw [QGridGen_KL_length]; exact hkpos)
    rw [QGridGen_KL_length] at h1
    have h2 := hBk' (KLloopOf d (sz.L n) σ b) (QGridGen_KL_wf σ b)
      (by rw [QGridGen_KL_length]; omega) (by rw [QGridGen_KL_length])
    rw [hAj]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  -- the sup bound on the drift
  have hD : ∀ b : Fin (m + 1) → Zd d (sz.L n),
      ‖∑ l ∈ Finset.Icc 3 (m + 1), STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l
            (KLloopOf d (sz.L n) σ b) +
          STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b) +
          STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b)‖ ≤
        driftEnvNg Cm.toFlowFM n (m + 1) (gridTime s t K n j) Bk := fun b =>
    QGridGen_norm_drift_le hL n hS hm1 hu0 hu1 hH σ hBk hBk' b
  -- the merged one-step bound in the shape of the algebra lemma
  have hc' : ∀ b : Fin (m + 1) → Zd d (sz.L n),
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp (fun ω' => AvecNg Cm s t K n (j + 1) σ ω' b) ω -
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n j + gridStep s t K n)
            (AvecNg Cm s t K n j σ ω) b -
          (gridStep s t K n : ℂ) *
            (∑ l ∈ Finset.Icc 3 (m + 1), STksimLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) l
                (KLloopOf d (sz.L n) σ b) +
              STelklkMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b) +
              STegtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) (KLloopOf d (sz.L n) σ b))‖ ≤
        stepErrNg Cm.toFlowFM n (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n) Bk := by
    intro b
    rw [← hvu]
    have := hTω b
    simp only [predIncNg] at this
    exact this
  have hmain := QGridGen_qstep_algebra Cm.toFlowFM n hU hm σ hu0 hΔ0
    (by rw [← hvu]; exact hv1) hϑu hϑv hlip htay hX hD hc' a
  rw [← hvu] at hmain
  rw [hlinω a]
  exact hmain

/-- **`gridDriftQNg`** (band `gridDriftQN`, `QGridA:2114`): `gridDriftQNg_of` for the merged mollifier
`QopAlgebra_mollifier d L m (sz.lam n)` (`C = (1 + 40 d m) 6^{d m}`, `c = 1/2`, `C₂ = 1000 (1 + d m)²`): one index `n`, one step `j`;
size level `sz.lam n`, `0 < sz.lam n`. -/
theorem gridDriftQNg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool) (Bk : ℝ)
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ)
    (hExp : HierDriftGen_Expand Cm s t K n) (hKL : HierDriftGen_KLoop Cm n) (hKT : HierDriftGen_KTwo Cm n)
    (hU : HierDriftGen_UStep Cm.toFlowFM n) (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hKK : HierDriftGen_KLink Cm n) (hm1 : ‖Cm.m n‖ ≤ 1) (hlam : 0 < sz.lam n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) (hm : 1 ≤ m) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 1 → ‖Cm.KI n w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(Cm.Pp), ∀ a : Fin (m + 1) → Zd d (sz.L n),
      ‖MeasureTheory.condExp (filt sz j) Cm.Pp
            (fun ω' => aTrueQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ (j + 1) ω' a) ω -
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n j) (gridTime s t K n (j + 1))
            (aTrueQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) a -
          (gridStep s t K n : ℂ) *
            dGridQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω a‖ ≤
        qErrQNg Cm.toFlowFM s t K n m ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
          (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) Bk j :=
  gridDriftQNg_of s t K n j σ Bk hL hW hExp hKL hKT hU hS hKK hm1 hs0 hst ht1 hK hj hm hBk hB (by positivity)
    (by norm_num) (QopAlgebra_mollifier d (sz.L n) m (sz.lam n))
    (QopAlgebra_mollifier_props d (sz.L n) m (sz.three_le_L n) hlam)
    (fun τ _ hτ a => QopAlgebra_mollifier_differentiableAt d (sz.L n) m (sz.three_le_L n) hlam hτ a)
    (QGridA_mollifier_taylor2 d (sz.L n) m (sz.three_le_L n) hlam)

end GridDriftQ

/-! ## 7. The stopped Duhamel expansion of the frozen `𝒬`-process (target 7) -/

section StoppedDuhamelQ

variable {d : ℕ} {sz : Sizes d}

/-- **`stoppedDuhamelQNg`** (band `stoppedDuhamelQN`, `QGridA:2168`): the pathwise stopped Duhamel expansion of `aFrozQNg`, for every
mollifier family `ϑ`, every stopping index `τ` and every grid index `j ≤ K n`; one index `n`, the semigroup class
`Step2Gen_USemigroup` replaces `|E n| < 2`:
`A^{Q,frz}_j = 𝒰_{u_0,u_j} A^Q_0 + Σ_{i<j∧τ} 𝒰_{u_{i+1},u_j}(Δ dGridQNg_i + ξ^Q_{i+1} + R^Q_i)`. -/
theorem stoppedDuhamelQNg (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hS : Step2Gen_USemigroup Cm.toFlowFM n)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j ≤ K n) :
    aFrozQNg Cm s t K n ϑ σ τ j ω =
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n j) (aTrueQNg Cm s t K n ϑ σ 0 ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n j)
            ((gridStep s t K n : ℂ) • dGridQNg Cm s t K n ϑ σ i ω + martIncQNg Cm s t K n ϑ σ i ω +
              rGridQNg Cm s t K n ϑ σ i ω) := by
  have hmin : min j (τ ω) ≤ K n := (min_le_left _ _).trans hj
  have hu0 : ∀ i, 0 ≤ gridTime s t K n i := QGridA_gridTime_nonneg s t K n hs0 hst
  have hu1 : ∀ i ≤ K n, gridTime s t K n i < 1 := fun i hi => QGridA_gridTime_lt_one s t K n hst hK ht1 hi
  have htele := Step2Gen_UN_duhamel_telescope Cm.toFlowFM n hS σ
    (gridTime s t K n) (min j (τ ω)) (fun i _ => hu0 i) (fun i hi => hu1 i (hi.trans hmin))
    (fun i => aTrueQNg Cm s t K n ϑ σ i ω)
  have hinc : ∀ i, aTrueQNg Cm s t K n ϑ σ (i + 1) ω -
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n i) (gridTime s t K n (i + 1))
        (aTrueQNg Cm s t K n ϑ σ i ω) =
      (gridStep s t K n : ℂ) • dGridQNg Cm s t K n ϑ σ i ω +
        martIncQNg Cm s t K n ϑ σ i ω + rGridQNg Cm s t K n ϑ σ i ω := by
    intro i
    funext a
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, martIncQNg, rGridQNg]
    ring
  simp only [hinc] at htele
  unfold aFrozQNg
  refine (congrArg (Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j)) htele).trans ?_
  rw [Step2Gen_UN_add]
  have hcomp : ∀ (i : ℕ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ),
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j)
        (Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n i) (gridTime s t K n (min j (τ ω))) A) =
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n i) (gridTime s t K n j) A := fun i A =>
    Step2Gen_UN_comp Cm.toFlowFM n hS σ (hu0 _) (hu1 _ hmin) (hu0 _) (hu1 _ hj) A
  have hsum := map_sum
    (Step2Gen_UNHom Cm.toFlowFM n σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j))
    (fun i => Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
      ((gridStep s t K n : ℂ) • dGridQNg Cm s t K n ϑ σ i ω +
        martIncQNg Cm s t K n ϑ σ i ω + rGridQNg Cm s t K n ϑ σ i ω))
    (Finset.range (min j (τ ω)))
  refine congrArg₂ (· + ·) (hcomp 0 _) ?_
  refine hsum.trans (Finset.sum_congr rfl fun i _ => hcomp (i + 1) _)

end StoppedDuhamelQ

/-! ## 8. Band bridges -/

section Bridges

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {m : ℕ}
  (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (ω : PathΩ sz)

/-- The band envelope `qErrQN` is `qErrQNg` at `bandFM` (definitional, as `bandFM_stepErrN`). -/
theorem QGridGen_bandFM_qErrQN (m' : ℕ) (C C₂ Bk : ℝ) :
    RBM.Ind.qErrQN sz E s t K n m' C C₂ Bk j = qErrQNg (bandFM sz E) s t K n m' C C₂ Bk j := rfl

end Bridges

/-! ## 9. Compiled nonempty instances (target 9)

Data of the band instances `QGridACheck` re-declared under the stem: `d = 3`, the merged `sz0` (`L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`),
the band carrier `bandStep2Mat sz0 E0` (`E0 ≡ 0`, `m = i`, `‖m‖ = 1`), `Ψ = 0`, `lam' = sz0.lam`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`
(`Δ = 1/10`), size index `0`, `m = 3` (tensors of `4` indices), `σ = (+,-,+,-)`, the merged mollifier `QopAlgebra_mollifier 3 4 3 (1/64)`.
Every deterministic hypothesis is discharged (the classes by the band discharges of `HierDriftGen`, the envelope by
`HierDriftGen_exists_envelope`); nothing is left as a hypothesis. -/

end RBM.BA

end
