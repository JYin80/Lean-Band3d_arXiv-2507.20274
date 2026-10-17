/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QEndGrid
import RBM3D.Chain.QGridGen2
import RBM3D.Chain.NQBudgetGen
import RBM3D.Chain.GridAssemblyGen
import RBM3D.Chain.NQEndLinGen

/-!
# The alternating grid endpoint over the carrier (U3s3b, ticket T2498)

Generic form of `Induction/QEndGrid.lean` (`altGridEndQN'`, not edited) over a carrier
`Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: arXiv:2507.20274, `lem:STOeq_Qt`, the alternating case `(eq:alternatecase1)`
`3_5:1676-1714`.  Composition, no new mathematics: the merged `assembledNg` at the alternating
exit time `altExitTauNg`, the vocabulary and the C1-C5 lemmas of `Induction/QEndA` (row a), the
`𝒬`-remainder `qErrQNg` and `sum_weighted_qErrQNg_le` (T2497), the level split, the Y-moment
constant (the `lam` patch of the band, kept: `yMomentsQUnifNg` asks the mollifier properties at
every `n`), the collapsed window and the union bound over the alternating `σ`.

* the model-free private helpers of `QEndGrid` (§0-§5: asymptotics, the grid, the level
  arithmetic, the exponent bookkeeping `altGrid_arith'`) and the carrier lemmas of `NQEndLinGen`
  (§2-§4: `η_v⁻¹ ≤ N`, the shift hypothesis, the collapsed window) are used by `open private`;
  no band `def` is edited;
* `QEndGridGen_assembly` (per alternating sign vector) and **`altGridEndQNg`** (the endpoint;
  exponents `ε₁ τ' D' C_K` after the carrier);
* compiled instances at the band carrier `bandStep2Mat sz0 Einst`
  (namespace `RBM.BA.QEndGridGenCheck`).

Constants (as the band, `C₄` replaced by the vocabulary constant `Cv ≥ C4`): `Λg = 𝔡⁻¹`,
`KL = 1/𝔠`, `C₁ = (1 + 40 d(m+1)) 6^{d(m+1)}`, `C_n`, `ε₀' = min ε₀ 1`, `e₂ = ε₀'/2`,
`ε = min (e₂/(8 max(Cv, C_n))) (1/2)`, `ε' = ε/2`, `τ' = min (ε/4) (e₂/(40 d (m+1)))`,
`ε₁ = εq = e₂/40`, `τ_N = e₂/8`, `D'' = 2C_n + 2 + 2Cv + k + (4k+1)/𝔠`, `D' = D'' + 2`,
`D_c = D'' + 1`, `C_K = D₁ + 2 C_P^* + 8k + 20 + D''`, `C₀ = (8k+8)/𝔠` (`k = m + 2`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private altGrid_ev_rpow_le altGrid_one_le_size altGrid_size_cast altGrid_W_le_size altGrid_ev_W_rpow_ge altGrid_step_le
  altGrid_K_mul_step altGrid_hΔη altGrid_gridTime_nonneg altGrid_gridTime_le altGrid_rangeCond_mono altGrid_ev_union
  altGrid_mol altGrid_mol_eq altGrid_mol_props altGrid_Bctl_le altGrid_hMee_bound altGrid_dDrift_bound altGrid_big_case
  altGrid_Dt_absorb altGrid_final_arith altGrid_C1 altGrid_C2 altGrid_Wpow_le altGrid_Npow_le_Wpow altGrid_ev_hlog
  altGrid_fin_arith altGrid_arith' altGrid_small altGrid_pow_succ_le altGrid_uStepC_nonneg from RBM3D.Induction.QEndGrid

open private altEnd_kappag_nonneg altEnd_stepErrNg_nonneg from RBM3D.Induction.QEndA

open private B45_norm_colsum from RBM3D.Induction.B45

open private NQEndLinGen_ev_hη NQEndLinGen_ev_hδ NQEndLinGen_Hpath_collapse NQEndLinGen_eta_win from RBM3D.Chain.NQEndLinGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (uStepC qStepErrN altYSetNg altExitTauNg mem_of_lt_altExitTauNg altExitMeasNg gridDriftQNg_envelope_ev assembledRHSAltQNg_qErr_le
  subGaussStop_altQNg alt_hkerGridQNg alt_hdriftGridQNg alt_hA0clsGridQNg alt_hDclsGridQNg altEnd_driftSupg altEnd_hexpg
  altEnd_stronglyMeasurable_zVecQNg altEnd_aFroz_eq_aTrueg altEnd_unQg QProxyG_KerEK4 zVecQNg yVecQNg yMomentsQUnifNg qProxyCn qProxyCQ
  qProxyW0 qProxyCn_pos QDriftA_W0 kappaAltQNg epsAltQNg altClsQN cQVAltQNg dDriftAltLinQNg qvBdAltQNg assembledRHSAltQNg budgetAltQNg
  altBudgetNumQNg altBudgetNumQNg_eventually dDriftAltLinQNg_nonneg dDriftAltLinQNg_le_shape altBudgetExpQN altBudgetExpQN_of_choice qProxy4C qProxy4C_pos qProxyG_kerEK4_band_at)

/-! ## 1. Helpers over a carrier -/

section Helpers

variable {d : ℕ} {sz : Sizes d}

/-- **The R1 guard (g)** at one index: from `0 ≤ g·l`, `g² ≤ l² ≤ A g²` and `0 < l ≤ Λg` the kernel coupling is in the window, `0 < g ≤ Λg`. -/
private theorem QEndGridGen_gK_win {g l A Λg : ℝ} (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hl : 0 < l) (hlΛ : l ≤ Λg) :
    0 < g ∧ g ≤ Λg := by
  obtain ⟨h1, h2, h3⟩ := h
  have hg0 : 0 ≤ g := by
    by_contra hneg
    have hneg := lt_of_not_ge hneg
    nlinarith
  have hgpos : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at h3
      nlinarith
  refine ⟨hgpos, ?_⟩
  have : g ≤ l := by
    by_contra hlt
    have hlt := lt_of_not_ge hlt
    nlinarith
  linarith

/-- The per-`u` facts on `[0, v]` over a carrier (band `altGrid_u_facts`): `η_u⁻¹ ≤ η_v⁻¹ ≤ N`, `B_u ≤ 2 (1-v)⁻¹ ≤ 2 N`. -/
private theorem QEndGridGen_u_facts (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {v u : ℝ}
    (hv1 : v < 1) (hu0 : 0 ≤ u) (huv : u ≤ v) (hη : (Cm.eta n v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hNv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v) :
    0 < Cm.eta n u ∧ (Cm.eta n u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ 0 < sz.Bctl n u ∧ sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  refine ⟨NQGood1Gen_eta_pos hL n hu1, ?_, STBctl_pos sz n hu1, ?_⟩
  · exact (inv_anti₀ (NQGood1Gen_eta_pos hL n hv1) (NQGood1Gen_eta_anti hL n huv)).trans hη
  · have h1 := altGrid_Bctl_le sz n hu0 huv hv1
    have h2 : (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (inv_pos.2 hN0) hNv
      rwa [inv_inv] at this
    linarith

/-- `N⁻¹ ≤ 1 - v` from `η_v⁻¹ ≤ N` and `η_v ≤ 1 - v` (band `altGrid_Nv`). -/
private theorem QEndGridGen_Nv (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    {v N : ℝ} (hv1 : v < 1) (hN0 : 0 < N) (hη : (Cm.eta n v)⁻¹ ≤ N) : N⁻¹ ≤ 1 - v := by
  have h1v : 0 < 1 - v := by linarith
  have hle : Cm.eta n v ≤ 1 - v := by
    rw [NQGood1Gen_eta_eq hL]
    exact mul_le_of_le_one_right h1v.le (NQGood1Gen_im_le_one hm)
  have h2 : (1 - v)⁻¹ ≤ N := (inv_anti₀ (NQGood1Gen_eta_pos hL n hv1) hle).trans hη
  exact (inv_le_comm₀ h1v hN0).1 h2

/-- **The crude sup at length `k` on the good walk over a carrier, in `N`-exponents** (band `altGrid_crude_N`; deterministic, fixed `n`): for Hermitian `H` and
`u ∈ [0, v]`, `‖(𝓛-𝒦)^{(k)}_{u,σ}(H)‖_∞ ≤ N^{k+2}`, from `STmaxLKMg_crudeNg` with the `𝒦` envelope `M_K = N η_v^{-k}` (the wing bound `exists_norm_KI_le_wing` at
`τ = 1`, the link `hKK`), `η_u⁻¹ ≤ η_v⁻¹ ≤ N`, `N ≥ 2`. -/
private theorem QEndGridGen_crude_N (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (hm : ‖Cm.m n‖ ≤ 1)
    {v : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hKI : ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖Cm.KI n w J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((Cm.eta n v)⁻¹) ^ k)
    (hKK : ∀ (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hv1 : v < 1) (hη : (Cm.eta n v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hN2 : 2 ≤ ((sz.size n : ℕ) : ℝ)) {u : ℝ} (hu0 : 0 ≤ u)
    (huv : u ≤ v) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) (σ : Fin k → Bool) :
    ‖fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n u H σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (k + 2) := by
  have hu1 : u < 1 := huv.trans_lt hv1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hηv := NQGood1Gen_eta_pos hL n hv1
  have hηu : (Cm.eta n u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    (inv_anti₀ hηv (NQGood1Gen_eta_anti hL n huv)).trans hη
  have hηv0 : 0 ≤ (Cm.eta n v)⁻¹ := inv_nonneg.2 hηv.le
  have hηu0 : 0 ≤ (Cm.eta n u)⁻¹ := inv_nonneg.2 (NQGood1Gen_eta_pos hL n hu1).le
  have hK : ∀ (σ' : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖Cm.K n u σ' a‖ ≤ ((sz.size n : ℕ) : ℝ) * ((Cm.eta n v)⁻¹) ^ k := by
    intro σ' a
    rw [← hKK u k σ' a]
    have h2 := hKI u ⟨hu0, huv⟩ (loopOf σ' a) (by simp [LoopIdx.WF, loopOf])
      (by simpa [LoopIdx.length, loopOf] using hk) (by simp [LoopIdx.length, loopOf])
    rwa [Real.rpow_one] at h2
  have hmax := STmaxLKMg_crudeNg hL hm hH hu0 hu1 (n' := k) (m := k) (by omega) le_rfl hK
  have hbd : (Cm.eta n u)⁻¹ ^ k + ((sz.size n : ℕ) : ℝ) * ((Cm.eta n v)⁻¹) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ (k + 2) := by
    have h1 : (Cm.eta n u)⁻¹ ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hηu0 hηu k
    have h2 : ((Cm.eta n v)⁻¹) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hηv0 hη k
    have h3 : ((sz.size n : ℕ) : ℝ) * ((Cm.eta n v)⁻¹) ^ k ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left h2 hN0.le
    have hNk : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ k := by positivity
    have h4 : (1 : ℝ) + ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by nlinarith
    calc (Cm.eta n u)⁻¹ ^ k + ((sz.size n : ℕ) : ℝ) * ((Cm.eta n v)⁻¹) ^ k
        ≤ ((sz.size n : ℕ) : ℝ) ^ k + ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k := by linarith
      _ = (1 + ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ k := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ k := mul_le_mul_of_nonneg_right h4 hNk
      _ = ((sz.size n : ℕ) : ℝ) ^ (k + 2) := by rw [← pow_add]; ring_nf
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b => ?_
  refine le_trans ?_ (hmax.trans hbd)
  exact Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖Cm.LM n u H p.1 p.2 - Cm.K n u p.1 p.2‖)
    (Finset.mem_univ (σ, b))

/-- **The `𝒬`-remainder `qErrQNg` is nonnegative** (the field `hstepErr0`; band `altGrid_qErrQN_nonneg`): every term of `qStepErrN` is a product of
nonnegative factors (`stepErrNg ≥ 0`, `uStepC ≥ 0`, `lkEnvNg`, `driftEnvNg ≥ 0`, `(1 - (u + Δ))⁻¹ ≥ 0`). -/
private theorem QEndGridGen_qErrQNg_nonneg {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n j m : ℕ)
    {s t : ℕ → ℝ} {K : ℕ → ℕ} {C C₂ Bk : ℝ} (hu : gridTime s t K n j < 1) (hu' : gridTime s t K n (j + 1) < 1)
    (hΔ : 0 ≤ gridStep s t K n) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hBk : 0 ≤ Bk) :
    0 ≤ qErrQNg Cm.toFlowFM s t K n m C C₂ Bk j := by
  have hη : 0 < Cm.eta n (gridTime s t K n j) := NQGood1Gen_eta_pos hL n hu
  have hη' : 0 < Cm.eta n (gridTime s t K n (j + 1)) := NQGood1Gen_eta_pos hL n hu'
  have hη0 : 0 ≤ (Cm.eta n (gridTime s t K n j))⁻¹ := inv_nonneg.2 hη.le
  have hsucc : gridTime s t K n j + gridStep s t K n = gridTime s t K n (j + 1) := by
    unfold gridTime; push_cast; ring
  have hβ : 0 ≤ (1 - (gridTime s t K n j + gridStep s t K n))⁻¹ := by
    rw [hsucc]; exact inv_nonneg.2 (by linarith)
  have hS : 0 ≤ stepErrNg Cm.toFlowFM n (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1)) (gridStep s t K n) Bk :=
    altEnd_stepErrNg_nonneg Cm.toFlowFM n _ hη hη' hu' hΔ hBk
  have hUst : 0 ≤ uStepC (m + 1) (gridStep s t K n) (gridTime s t K n j + gridStep s t K n) := by
    refine altGrid_uStepC_nonneg _ hΔ ?_
    rw [hsucc]; exact hu'
  have hMk : 0 ≤ lkEnvNg Cm.toFlowFM n (m + 1) (gridTime s t K n j) Bk := by
    unfold lkEnvNg; positivity
  have hDm : 0 ≤ driftEnvNg Cm.toFlowFM n (m + 1) (gridTime s t K n j) Bk := by
    unfold driftEnvNg; positivity
  unfold qErrQNg qStepErrN
  positivity

/-- **The uniform `Y` moments for all signs with one `C_P`, with the `lam` patch** (band `altGrid_yMomentsMax`): the maximum over the `2^k` sign vectors of the
constants of `yMomentsQUnifNg` at the patched mollifier family `altGrid_mol` (the explicit mollifier if `0 < lam n`, the delta family otherwise, so that the
mollifier properties hold at every `n`) serves every sign; the conclusion is for the explicit mollifier on the eventual set `0 < lam n`. -/
private theorem QEndGridGen_yMomentsMax {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
    {κm τR : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) {s v : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) (hsize : sz.SizeTendsto) (hrange : sz.RangeCond τR v) (m : ℕ) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin (m + 1 + 1) → Bool,
      ∀ᶠ n : ℕ in atTop, 0 < sz.lam n → ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
          YMomentBoundsNg Cm σ (gridTime s v K n) τ (K n)
            (fun j ω => yVecQNg Cm s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  choose CP hCP0 hCPev using fun σ : Fin (m + 1 + 1) → Bool =>
    yMomentsQUnifNg hL hW hRow κm τR s v hspec hs0 hsv hv1 hsize hrange (m + 1)
      ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
      (fun n => altGrid_mol sz m n) hC0 (by norm_num) (fun n => altGrid_mol_props sz m n) σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn hlam
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  refine ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), fun τ hτm => ?_⟩
  have h := hτ τ hτm
  rw [altGrid_mol_eq sz m n hlam] at h
  exact h

end Helpers

/-! ## 2. The assembly at the alternating exit time, for one sign vector

Band `altGrid_assembly'` (`QEndGrid:1117`).  The merged `assembledNg` at `τ = altExitTauNg` (exit from `GoodSetNg ∩ GoodLinNg ∩ altYSetNg`, levels `Γ = N^{ε₁}`,
`Yl = N^{ε₁} X`) for the `𝒬`-process `aTrueQNg` with the kernel class `altClsQN` (`κ = kappaAltQNg` at the vocabulary constant `Cv ≥ C4`, `εK = epsAltQNg`, class
exponent `ε'`, radius level `Dc`), the linear drift level `dDriftAltLinQNg`, the sub-Gaussian proxy `cQVAltQNg` (`subGaussStop_altQNg`), the `Y` moments of `yVecQNg`
and the `qErrQNg` remainder (D2, `gridDriftQNg_envelope_ev`); then the bridge C1b (`assembledRHSAltQNg_qErr_le`) turns the remainder sum into `assembledRHSAltQNg +
N^{-D_t}`.  The kernel class is D1 (`hKer`, constant `C4`, at the kernel coupling `gK`) and the comparison R1 (`hcmp`, `hA`, `hdW2`, `hAk`, `C4 ≤ Cv`); the spectral
levels of `ℬ₄ + ℬ₅` are the fields of `B45Gen_Facts` at the carrier (`hward`, `hker`, `hrow`, `hcol`, `K₆`, `κm`) and the `Θ`-decay is `Step5KerGen_ThDecay` (`hTh`). -/

section Assembly

variable {d : ℕ} {sz : Sizes d}

private theorem QEndGridGen_assembly (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm K₆ C₆ : ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ) (hd : 3 ≤ d)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hGD : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ HierDriftGen_Expand Cm s v K n ∧ HierDriftGen_KLoop Cm n ∧
      HierDriftGen_KTwo Cm n ∧ HierDriftGen_UStep Cm.toFlowFM n)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0)
    (Λ Φc Φ₁ Φ₂ Φ₃ X : ℕ → ℝ) (hΛ : ∀ n, 0 ≤ Λ n) (hΦ₁ : ∀ n, 0 ≤ Φ₁ n) (hΦ₂ : ∀ n, 0 ≤ Φ₂ n)
    (hΦ₃ : ∀ n, 0 ≤ Φ₃ n) (hX : ∀ n, 1 ≤ X n)
    {A C4 Cv Λg KL ε ε' τ' τN D' D'' Dc ε₁ εq τK D_Y D_t D₁ C_P C_K C₀ : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) (hCv : C4 ≤ Cv)
    (hTh : Step5KerGen_ThDecay Cm.toFlowFM gK Λg C₆) (hC₆ : 0 ≤ C₆)
    (hΛg : 0 < Λg) (hKL : 0 < KL)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hε'0 : 0 < ε') (hε'1 : ε' < 1) (hε'ε : ε' ≤ ε) (hτ' : 0 ≤ τ') (hε₁0 : 0 ≤ ε₁)
    (hε₁1 : ε₁ ≤ 1) (hD'1 : 1 < D') (hDc : 1 < Dc) (hC₀ : 0 ≤ C₀) (hεq : 0 < εq) (hτK : 0 < τK)
    (hCK0 : 0 ≤ C_K) (hDt0 : 0 ≤ D_t)
    (hCK : D₁ + 4 * D_Y + ((m + 1 + 1 : ℕ) : ℝ) + 2 * C_P + 8 ≤ C_K)
    (hD : ((m + 1 : ℕ) : ℝ) + 2 + qProxyCQ d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) < D'' + 1)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin (m + 1 + 1) → Bool, ∀ᶠ n : ℕ in atTop, 0 < sz.lam n → ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsNg Cm σ (gridTime s v K n) τ (K n)
          (fun j ω => yVecQNg Cm s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    (hW4 : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ))
    (hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hWε' : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hlog : ∀ᶠ n : ℕ in atTop, Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hNW : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW1 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hdW2 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : ∀ᶠ n : ℕ in atTop, A ^ (m + 1 + 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε))
    (hKer : ∀ᶠ n : ℕ in atTop, QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) KL C4 n)
    (hDD : ∀ᶠ n : ℕ in atTop, 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrNg Cm n (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)))
    (hW0a : ∀ᶠ n : ℕ in atTop,
      qProxyW0 d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) C₀ ε' (D'' + 1) ≤ ((sz.W n : ℕ) : ℝ))
    (hW0b : ∀ᶠ n : ℕ in atTop,
      QDriftA_W0 d (m + 1) KL (altGrid_C1 d m) (1 / 2) C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
    (hWbig : ∀ T : ℝ, ∀ᶠ n : ℕ in atTop, T ≤ ((sz.W n : ℕ) : ℝ))
    (hη : ∀ᶠ n : ℕ in atTop, (Cm.eta n (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hνt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁)
    (hFv : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹)
    (hMΛ : ∀ᶠ n : ℕ in atTop, ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * altGrid_C1 d m *
      (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
    (S : ℕ → Prop)
    (hMee : ∀ᶠ n : ℕ in atTop, S n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ ε₁ * Λ n) *
        ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / Cm.eta n u) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hDr : ∀ᶠ n : ℕ in atTop, S n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      dDriftLinNg Cm n u (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ≤
        ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hCr : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ σ : Fin (m + 1 + 1) → Bool,
          ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hsum : ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s v K n p)⁻¹) ^ (m + 1 + 1) *
          qErrQNg Cm.toFlowFM s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
            (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)) :
    ∀ᶠ n : ℕ in atTop, S n → ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 → s n < v n →
      ∃ G : Set (PathΩ sz), Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetNg Cm n (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
            ‖aTrueQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ (K n) ω a‖ ≤
              assembledRHSAltQNg Cm s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε
                (fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁) Λ
                (fun j => dDriftAltLinQNg Cm n (gridTime s v K n j) m (((sz.size n : ℕ) : ℝ) ^ ε₁)
                  (Φ₁ n) (Φ₂ n) (Φ₃ n) (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
                (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b =>
                  ‖aTrueQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b‖) a +
                ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  classical
  have : IsProbabilityMeasure Cm.Pp := by rw [hW'.2.1]; exact isProbabilityMeasure_pathP _
  have hC₁ : 0 < altGrid_C1 d m := by unfold altGrid_C1; positivity
  have hC₂0 : 0 ≤ altGrid_C2 d m := by unfold altGrid_C2; positivity
  have hk2 : 2 ≤ m + 1 + 1 := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hκ0 : 0 < κm := hspec.1
  obtain ⟨W₀, hW₀1, HDcls⟩ := alt_hDclsGridQNg d m Λg KL C₀ ε' D' C₆ A hd hΛg hε'0 hC₆ hA
  have hA' := assembledNg Cm hsize (m + 1 + 1) εq hεq D_Y D₁ C_P C_K hCK0 hCK
  have hη' := NQEndLinGen_eta_win hL hm
  have hEnv : ∀ σ : Fin (m + 1 + 1) → Bool, ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n →
      ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖rGridQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω a‖ ≤
        qErrQNg Cm.toFlowFM s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
          (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j :=
    fun σ => gridDriftQNg_envelope_ev d sz Cm E lam' Ψ μ m τK hτK s v K hsize hKb hL hW' hS hKK hm hη' hs0 hsv hv1 hK0
      hGD σ
  have hQV : QVPropagatedNg Cm lam' := qvPropagatedNg Cm E lam' hL hSeq
  have hSub : AzumaSubGNg Cm lam' s v K := azumaSubGNg Cm hW' s v K
  filter_upwards [hA', hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hlam, hWt, hW4,
    hWε, hWε', hlog, hNW, hdW1, hdW2, hDD, hδ, hW0a, hW0b, hWbig W₀, hη, hνt, hFv, hMΛ, hMee, hDr, hCr,
    hsum, hKer, hAk] with n hAn hKNn hKUn hYn hEnvn hlamn hWtn hW4n hWεn hWε'n hlogn hNWn hdW1n hdW2n hDDn hδn hW0an
    hW0bn hW₀n hηn hνtn hFvn hMΛn hMeen hDrn hCrn hsumn hKern hAkn
  intro hSn σ hσ hsvn
  obtain ⟨hg, hgΛ⟩ := hlamn
  obtain ⟨hgK0, hgKΛ⟩ := QEndGridGen_gK_win (hcmp n) hg hgΛ
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ hg
  have hMeen := hMeen hSn
  have hDrn := hDrn hSn
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := altGrid_step_le sz hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := altGrid_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ => altGrid_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi =>
    (altGrid_gridTime_le (hsv n) hKn hi).trans_lt (hv1 n)
  have huv : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi => altGrid_gridTime_le (hsv n) hKn hi
  have hmono : ∀ i m', i ≤ m' → m' ≤ K n → gridTime s v K n i ≤ gridTime s v K n m' :=
    fun i m' him _ => ST_gridTime_mono s v K n (hsv n) him
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNvn : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n := QEndGridGen_Nv Cm hL (hm n) (hv1 n) hN0 hηn
  have hLKn : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL := by
    refine le_trans ?_ hNWn
    have h1 := altGrid_size_cast sz n
    have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1.le
    have h3 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    calc ((sz.L n : ℕ) : ℝ) ^ d = 1 * ((sz.L n : ℕ) : ℝ) ^ d := (one_mul _).symm
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := mul_le_mul_of_nonneg_right h2 h3
      _ = ((sz.size n : ℕ) : ℝ) := h1
  have hKv : (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ KL := by
    refine le_trans ?_ hNWn
    have := inv_anti₀ (inv_pos.2 hN0) hNvn
    rwa [inv_inv] at this
  have hdW0 : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' := hdW1n
  have hεε : Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
    refine le_trans ?_ hdW2n
    have h0 : 0 ≤ Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hW0.le _)
    calc Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' = 1 * (Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε') := (one_mul _).symm
      _ ≤ (d : ℝ) * (Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε') := mul_le_mul_of_nonneg_right hd1 h0
      _ = (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' := by ring
  have hDD2 : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) := by
    have := Real.rpow_nonneg hW0.le (-D')
    linarith
  have hν1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁0
  have hνN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
    calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
      _ = _ := Real.rpow_one _
  have hSemi : Step2Gen_USemigroup Cm.toFlowFM n := (hRow n).1
  have hKLink : HierDriftGen_KLink Cm n := fun w _ k σ a => hKK n w k σ a
  -- the data of the assembly
  set ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ :=
    QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n) with hϑ
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set Γ : ℕ → ℝ := fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ with hΓ
  set Yl : ℕ → ℝ := fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ * X n with hYl
  set τ : PathΩ sz → ℕ := altExitTauNg Cm s v K (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n with hτdef
  have hτmeas : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω} :=
    altExitMeasNg hL hW' s v K n (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D'
  have hmem : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → Cm.Hpath s v K n j ω ∈
      {H | GoodSetNg Cm n (u j) (m + 1 + 1) (Γ n) (Λ n) (Φc n) τ' D' H} ∩
        GoodLinNg Cm n (u j) (m + 1 + 1) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
          altYSetNg Cm n (u j) (m + 1 + 1 - 1) (Yl n) :=
    fun ω j hj => mem_of_lt_altExitTauNg hj
  have hcrude : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → j ≤ K n →
      ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        STLKMg Cm n (u j) (Cm.Hpath s v K n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ :=
    fun ω j hj hjK => hCrn (u j) (hu0 j hjK) (huv j hjK) _ (hmem ω j hj).1.1.1 σ
  have hAcr : ∀ (ω : PathΩ sz) (j : ℕ), j < K n → j < τ ω →
      ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        STLKMg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ :=
    fun ω j hjK hjτ => hcrude ω j hjτ hjK.le
  have hDcr : ∀ (ω : PathΩ sz) (j : ℕ), j < K n → j < τ ω →
      ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ :=
    fun ω j hjK hjτ => altEnd_driftSupg Cm n hk2 (hmem ω j hjτ).1.2
      (hDrn (u j) (hu0 j hjK.le) (huv j hjK.le)) σ
  have hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (fun ω => zVecQNg Cm s v K n j ϑ σ ω) :=
    fun j => altEnd_stronglyMeasurable_zVecQNg Cm hL hW' s v K n j ϑ σ
  have hsubG : ∀ m' ≤ K n, ∀ (a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ), j < m' →
      SubGaussStopNg Cm σ u τ (fun j ω => zVecQNg Cm s v K n j ϑ σ ω) m' a j
        (cQVAltQNg Cm s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j) := by
    intro m' hm' a j hj
    have hj1 : j + 1 ≤ K n := by omega
    exact subGaussStop_altQNg (m := m) (Cm := Cm) hd Λg KL hΛg hKL hSub hL hW' hQV hs0 hsv hv1 n (hm n) (hS n) hcmp hA hKern
      (hRow n) hCv (hwL n) hWtn hg hgΛ (ε := ε) (ε₁ := ε') (τ' := τ') (C₀ := C₀) (D' := D') (D'' := D'') hW2 hε0 hε1 hWεn
      hlogn hε'0 hε'1 hWε'n hεε hLKn hdW0 hAkn hC₀ hD hW0an (σ := σ) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl m' hm' a j hj
      (hMeen _ (hu0 _ hj1) (huv _ hj1)) (hδn j (by omega))
  have hbundle : GridAssemblyHypNg Cm σ u τ Δ (K n)
      (altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u)
      (fun ω => aTrueQNg Cm s v K n ϑ σ 0 ω) (fun m' ω => aFrozQNg Cm s v K n ϑ σ τ m' ω)
      (fun j ω => dGridQNg Cm s v K n ϑ σ j ω) (fun j ω => zVecQNg Cm s v K n j ϑ σ ω)
      (fun j ω => yVecQNg Cm s v K n j ϑ σ ω) (fun j ω => rGridQNg Cm s v K n ϑ σ j ω)
      (kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u)
      (epsAltQNg Cv ((sz.W n : ℕ) : ℝ)) (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun j _ => dDriftAltLinQNg Cm n (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
        (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
      (fun _ _ => 4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
      (fun m' a j => cQVAltQNg Cm s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j)
      (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2)
      (fun j => qErrQNg Cm.toFlowFM s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
        (Cm.eta n (u (j + 1)))⁻¹ ^ (m + 1 + 1)) j) := {
    hKer := hRow n
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := altEnd_hexpg Cm hL hW' s v K n hKLink hSemi (hs0 n) (hsv n) (hv1 n) hKn ϑ σ τ
    hκ0 := fun i m' _ _ => altEnd_kappag_nonneg (m + 1 + 1) Cv (sz.lam n) _ ε hW0.le u i m'
    hε0 := fun i m' _ _ => Real.rpow_nonneg hW0.le _
    hker := alt_hkerGridQNg hd Cm hcmp hA s v K n hKern hCv (hs0 n) (hsv n) hKn hW1 hε0 hε1 hWεn hlogn hLKn hdW2n hAkn hDc
      (hwL n) hWtn σ
    hδ0 := by positivity
    hA0cls := alt_hA0clsGridQNg hd m KL C₀ ε' D' hε'0 Cm σ s v K Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' Dc hW0bn hLKn hdW1n hDD2 hg (hs0 n)
      ((hsv n).trans_lt (hv1 n)) (fun ω hω => hcrude ω 0 hω (Nat.zero_le _))
    hdDrift0 := fun ω j hj => dDriftAltLinQNg_nonneg Cm hL n (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) _ ε' D' τN
      (X n) (hu1 j hj.le) (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) (by linarith [hX n])
    hδD0 := fun _ _ _ => by positivity
    hdrift := fun ω j hjK hjτ b => alt_hdriftGridQNg hd m Λg KL hΛg hKL Cm hL n hκ0 (hspec.2.1 n) (hm n) hward (hker n) hK₆
      (hrow n) (hcol n) σ s v K Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl hg hgΛ (hs0 n) (hsv n) (hv1 n) hNvn hW1 hτ' hε'0 hε'1 hD'1 hWε'n hLKn hdW1n
      hν1 (hX n) hνtn hνN hFvn hMΛn le_rfl hσ ω j hjK hjτ b
    hDcls := fun ω j hjK hjτ => HDcls sz Cm gK n σ s v K Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' Dc (hker n) hTh hcmp hgK0 hgKΛ hW₀n hLKn (hs0 n)
      (hsv n) (hv1 n) hKv hdW1n hDDn hAcr hDcr ω j hjK hjτ
    hc_pos := fun m' hm1 hmK a => by
      have hΔpos : 0 < Δ := div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hKn)
      have hterm : ∀ j ∈ Finset.range m',
          0 < (cQVAltQNg Cm s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j : ℝ) := by
        intro j hj
        have hj1 : j + 1 ≤ K n := by have := Finset.mem_range.1 hj; omega
        have hη'' := NQGood1Gen_eta_pos hL n (hu1 (j + 1) hj1)
        have hB' := STBctl_pos sz n (hu1 (j + 1) hj1)
        have hΛ' := hΛ n
        have hΓ' : 0 ≤ Γ n := Real.rpow_nonneg hN0.le _
        unfold cQVAltQNg
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        have hq : 0 < qvBdAltQNg Cm n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε (Γ n) (Λ n) D'' (u (j + 1)) (u m') := by
          unfold qvBdAltQNg
          positivity
        positivity
      exact Finset.sum_pos hterm ⟨0, Finset.mem_range.2 (by omega)⟩
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := hYP τ hτmeas
    hstepErr0 := fun j hj => QEndGridGen_qErrQNg_nonneg hL n j (m + 1) (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0 hC₁.le hC₂0
      (by
        have := NQGood1Gen_eta_pos hL n (hu1 (j + 1) hj)
        positivity)
    hR := (hEnvn σ).mono fun ω hω j hj _ b => hω j hj b }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) σ u τ Δ
    (altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u)
    (fun ω => aTrueQNg Cm s v K n ϑ σ 0 ω) (fun m' ω => aFrozQNg Cm s v K n ϑ σ τ m' ω)
    (fun j ω => dGridQNg Cm s v K n ϑ σ j ω) (fun j ω => zVecQNg Cm s v K n j ϑ σ ω)
    (fun j ω => yVecQNg Cm s v K n j ϑ σ ω) (fun j ω => rGridQNg Cm s v K n ϑ σ j ω)
    (kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u)
    (epsAltQNg Cv ((sz.W n : ℕ) : ℝ)) (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun j _ => dDriftAltLinQNg Cm n (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
      (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
    (fun _ _ => 4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (fun m' a j => cQVAltQNg Cm s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε Γ Λ D'' m' a j)
    (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2)
    (fun j => qErrQNg Cm.toFlowFM s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ τK *
      (Cm.eta n (u (j + 1)))⁻¹ ^ (m + 1 + 1)) j) P hK1 hKUn hΔ hKΔ hP0 hPle (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauNg_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hAeq : aFrozQNg Cm s v K n ϑ σ τ (K n) ω = aTrueQNg Cm s v K n ϑ σ (K n) ω :=
    altEnd_aFroz_eq_aTrueg Cm s v K n hSemi (hs0 n) (hsv n) (hv1 n) hKn ϑ σ τ ω (by rw [hτeq])
  have hb' : ‖aFrozQNg Cm s v K n ϑ σ τ (K n) ω a‖ ≤ _ := hb
  rw [hAeq] at hb'
  have hC1b := assembledRHSAltQNg_qErr_le Cm hL s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε Γ Λ
    (fun j => dDriftAltLinQNg Cm n (u j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
      (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
    (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D'' D_Y τK εq
    (Finset.univ.sup' Finset.univ_nonempty fun b => ‖aTrueQNg Cm s v K n ϑ σ 0 ω b‖)
    (Finset.univ.sup' Finset.univ_nonempty fun b => ‖aTrueQNg Cm s v K n ϑ σ 0 ω b‖) D_t
    (altGrid_C1 d m) (altGrid_C2 d m) a (hs0 n) (hsv n) (hv1 n) hKn hτK.le le_rfl (hsumn (K n) le_rfl)
  exact hb'.trans hC1b

end Assembly

/-! ## 3. Target 10: the alternating grid endpoint `altGridEndQNg`

Band `altGridEndQN'` (`QEndGrid:2176`, `lem:STOeq_Qt`, `(eq:alternatecase1)` `3_5:1676-1714`).  For every `m` (tensors of `m + 2 ≥ 2` indices), D1 constant `C4`
(`QProxyG_KerEK4` at `KL = 1/𝔠` and the kernel coupling `gK`, eventually), vocabulary constant `Cv ≥ C4` (`Cv > C4` unless the comparison constant `A` of R1 is `1`),
levels `Λ ≥ 0` (`≥ 1` eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, `X ≥ 1`, end time `v ∈ [s, t]`, final loss `ε₀ > 0` and failure exponent `D₁ > 0` there are exponents `ε₁, τ', D', C_K`
(after the carrier, as `nqGridEndLinNg`) such that for every crude level `Φc` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`, eventually there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`,
on which: if the carrier walk is in `GoodSetNg(N^{ε₁}, Λ, Φc, τ', D') ∩ GoodLinNg(N^{ε₁}, Φ₁, Φ₂, Φ₃) ∩ altYSetNg(N^{ε₁} X)` at every `j ≤ K_n` and the initial `𝒬`-loops satisfy
`|𝒬_s (𝓛-𝒦)_{s,σ,a}| ≤ N^{ε₁} B_s^{m+2}`, then `|(𝓛-𝒦)_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃ + X) B_v^{m+2}` for every alternating `σ` and label `a`.
`|E n| ≤ 2 - κ` is `DecayGen_Spec` and `‖Cm.m n‖ ≤ 1`; `STKbound` is the pin `STKboundgL`; the drift enters per index (the classes `Expand`, `KLoop`, `KTwo`, `UStep`
eventually, the link `hKK`, the row sums); the spectral levels of `ℬ₄ + ℬ₅` are the fields of `B45Gen_Facts` at the carrier; `Step5KerGen_ThDecay` is `hTh`; R1 is
`hcmp`, `hA`; the guard (g) `0 < lam n → 0 < gK n ≤ lam n` is derived from `hcmp` at the indices of the window `0 < lam n ≤ 𝔡⁻¹` (`hWO`). -/

section Endpoint

variable {d : ℕ} {sz : Sizes d}

theorem altGridEndQNg (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm 𝔠 τ 𝔡 A C₆ K₆ : ℝ} (s t : ℕ → ℝ) (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτ : 0 < τ) (h𝔡 : 0 < 𝔡)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n)
    (hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n) (hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n)
    (hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hTh : Step5KerGen_ThDecay Cm.toFlowFM gK 𝔡⁻¹ C₆) (hC₆ : 0 ≤ C₆)
    (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τ t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) :
    ∀ m : ℕ, ∀ C4 Cv : ℝ, 0 < C4 → C4 ≤ Cv → (C4 < Cv ∨ A = 1) →
      (∀ᶠ n : ℕ in atTop, QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) (1 / 𝔠) C4 n) →
    ∀ Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) → (∀ n, 1 ≤ X n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetNg Cm n (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                  (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                    STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
                  (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
  intro m C4 Cv hC4 hCv hAk0 hKer Λ Φ₁ Φ₂ Φ₃ X hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ hX v hsv hvt ε₀ hε₀ D₁ hD₁
  classical
  have hd1 : 1 ≤ d := by omega
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hv0 : ∀ n, 0 ≤ v n := fun n => (hs0 n).trans (hsv n)
  have him1 : ∀ n, (Cm.m n).im ≤ 1 := fun n => NQGood1Gen_im_le_one (hm n)
  have hk2 : 2 ≤ m + 1 + 1 := by omega
  have hκ0 : 0 < κm := hspec.1
  -- the window `0 < lam n ≤ Λg = 𝔡⁻¹`, `KL = 1/𝔠`
  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
  obtain ⟨KL, hKLdef⟩ : ∃ KL : ℝ, KL = 1 / 𝔠 := ⟨_, rfl⟩
  have hΛg : 0 < Λg := by rw [hΛgdef]; exact inv_pos.2 h𝔡
  have hKLpos : 0 < KL := by rw [hKLdef]; positivity
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg := by
    rw [hΛgdef]
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  rw [← hΛgdef] at hTh
  rw [← hKLdef] at hKer
  -- the range exponent of the end time, the `Y`-moment constant (one for all signs, before the grid)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : sz.RangeCond (min τ 1) v := altGrid_rangeCond_mono sz (min_le_left _ _) hvt hrange
  obtain ⟨Cmax, hCmax0, hYmax⟩ := QEndGridGen_yMomentsMax hL hW' hRow hspec hs0 hsv hv1 hsize hrangeV m
  -- the numerical constants, in the fixed order of the docstring
  have hC₁ : 0 < altGrid_C1 d m := by unfold altGrid_C1; positivity
  have hC₂0 : 0 ≤ altGrid_C2 d m := by unfold altGrid_C2; positivity
  have hCv0 : 0 < Cv := lt_of_lt_of_le hC4 hCv
  have hCn : 0 < qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) :=
    qProxyCn_pos hd (m + 1) hΛg hKLpos hC₁ (by norm_num)
  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
  have he0 : 0 < e0 := by rw [he0def]; exact lt_min hε₀ one_pos
  have he01 : e0 ≤ 1 := by rw [he0def]; exact min_le_right _ _
  have he0le : e0 ≤ ε₀ := by rw [he0def]; exact min_le_left _ _
  obtain ⟨e2, he2def⟩ : ∃ e2 : ℝ, e2 = e0 / 2 := ⟨_, rfl⟩
  have he2 : 0 < e2 := by rw [he2def]; positivity
  have he2le : e2 ≤ 1 := by rw [he2def]; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (e2 / (8 * max Cv
      (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)))) (1 / 2) := ⟨_, rfl⟩
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = ε / 2 := ⟨_, rfl⟩
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = min (ε / 4) (e2 / (40 * ((d : ℝ) * ((m : ℝ) + 1)))) := ⟨_, rfl⟩
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = e2 / 40 := ⟨_, rfl⟩
  obtain ⟨τN, hτNdef⟩ : ∃ τN : ℝ, τN = e2 / 8 := ⟨_, rfl⟩
  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = 2 * qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) + 2 +
      2 * Cv + ((m + 1 + 1 : ℕ) : ℝ) + (4 * ((m + 1 + 1 : ℕ) : ℝ) + 1) / 𝔠 := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : ℝ, D' = D'' + 2 := ⟨_, rfl⟩
  obtain ⟨Dc, hDcdef⟩ : ∃ Dc : ℝ, Dc = D'' + 1 := ⟨_, rfl⟩
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ, C_K = D₁ + 2 * Cmax + 8 * ((m + 1 + 1 : ℕ) : ℝ) + 20 + D'' :=
    ⟨_, rfl⟩
  obtain ⟨hε0, hε1, hε'0, hε'1, hε'ε, hτ'0, hτ'ε, hτ'dm, hε₁0, hε₁1, hε₁e2, hτNe2, h2ε₁τN, hD''0, hD'1, hDc1, hCK0, hCK1,
    hCKa, hCKb, hCKθ, hD, hFv, hexp⟩ := altGrid_arith' d m (C₄ := Cv)
    (Cn := qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) hd h𝔠 hCv0 hCn he2 he2le hD₁ hCmax0 hεdef
    hε'def hτ'def hε₁def hτNdef hD''def hD'def hDcdef hCKdef
  refine ⟨ε₁, τ', D', C_K, hε₁0, hτ'0, by linarith [hD'1], hCK0, ?_⟩
  intro Φc K hK0 hKN hKU
  -- the eventual regime facts
  have hη := NQEndLinGen_ev_hη Cm hspec him1 hsize hτR hrangeV
  have hη' := NQEndLinGen_eta_win hL hm
  have hN2ev : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hsize.eventually_ge_atTop 2
  have hWbig : ∀ T : ℝ, ∀ᶠ n : ℕ in atTop, T ≤ ((sz.W n : ℕ) : ℝ) := fun T => by
    filter_upwards [altGrid_ev_W_rpow_ge sz hsize h𝔠 hband one_pos T] with n hn
    rwa [Real.rpow_one] at hn
  have hWε : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
    altGrid_ev_W_rpow_ge sz hsize h𝔠 hband hε0 4
  have hWε' : ∀ᶠ n : ℕ in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' :=
    altGrid_ev_W_rpow_ge sz hsize h𝔠 hband hε'0 4
  have hlog := altGrid_ev_hlog sz hd1 hsize h𝔠 hband hε0
  have hNW : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ KL := by
    filter_upwards [hband] with n hn
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hn (τ := 1) zero_le_one
    rwa [Real.rpow_one, ← hKLdef] at this
  have hdW1 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' := by
    filter_upwards [altGrid_ev_W_rpow_ge sz hsize h𝔠 hband (show 0 < ε / 4 by linarith [hε0])
      (d : ℝ)] with n hn
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by linarith
    calc (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 4) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1 hτ'ε) (by positivity)
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 4) * ((sz.W n : ℕ) : ℝ) ^ (ε / 4) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
      _ = ((sz.W n : ℕ) : ℝ) ^ ε' := by
          rw [← Real.rpow_add' hW0 (by linarith [hε0]), hε'def]; congr 1; ring
  have hdW2 : ∀ᶠ n : ℕ in atTop, (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
    filter_upwards [altGrid_ev_W_rpow_ge sz hsize h𝔠 hband (show 0 < ε / 2 by linarith [hε0])
      ((d : ℝ) * Real.sqrt A)] with n hn
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' = (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) := by
          rw [hε'def]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hW0 _)
      _ = ((sz.W n : ℕ) : ℝ) ^ ε := by
          rw [← Real.rpow_add' hW0 (by linarith [hε0])]; congr 1; ring
  have hAk : ∀ᶠ n : ℕ in atTop, A ^ (m + 1 + 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε) := by
    rcases hAk0 with hlt | hA1
    · have hpos : 0 < (Cv - C4) * ε := mul_pos (sub_pos.2 hlt) hε0
      exact altGrid_ev_W_rpow_ge sz hsize h𝔠 hband hpos (A ^ (m + 1 + 1))
    · filter_upwards [hWbig 1] with n hn
      rw [hA1, one_pow]
      exact Real.one_le_rpow hn (mul_nonneg (sub_nonneg.2 hCv) hε0.le)
  have hDD : ∀ᶠ n : ℕ in atTop, 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) := by
    filter_upwards [hWbig 4] with n hn
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have e : ((sz.W n : ℕ) : ℝ) ^ (-Dc) = ((sz.W n : ℕ) : ℝ) ^ (-D') * ((sz.W n : ℕ) : ℝ) := by
      rw [show -Dc = -D' + 1 by rw [hDcdef, hD'def]; ring, Real.rpow_add hW0, Real.rpow_one]
    rw [e]
    have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
    calc 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') = ((sz.W n : ℕ) : ℝ) ^ (-D') * 4 := by ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') * ((sz.W n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hn this
  have hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrNg Cm n (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    filter_upwards [NQEndLinGen_ev_hδ Cm hspec him1 hd1 hsize h𝔠 hband (m + 1 + 1) (D'' := D'' + 1) (C_K := C_K) hs0
      hsv hv1 hK0 hη (by linarith [hD''0]) hCKb hKN] with n hn j hj
    have h := hn j hj
    rwa [show -(D'' + 1 + 1) = -D' by rw [hD'def]; ring] at h
  have hνt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := by
    refine Eventually.of_forall fun n => ?_
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_W_le_size sz hd1 n
    have hτ0 := hτ'0.le
    calc (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m)
        = ((sz.W n : ℕ) : ℝ) ^ (τ' * ((d : ℝ) * m)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; push_cast; ring_nf
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' * ((d : ℝ) * m)) :=
          Real.rpow_le_rpow hW0 hWN (by positivity)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_le_rpow_of_exponent_le hN1 hτ'dm
  have hFv' : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-D') ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
    filter_upwards [hband] with n hbn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 := altGrid_Wpow_le hN0 hbn (show -D' ≤ 0 by linarith [hD'1])
    have h2 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-D')) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * (m : ℝ) + 4)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hFv])
    have h3 : ((sz.size n : ℕ) : ℝ) ^ (-(2 * (m : ℝ) + 4)) = (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
      rw [Real.rpow_neg hN0.le, show (2 * (m : ℝ) + 4) = ((2 * m + 4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have h4 : (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ :=
      le_mul_of_one_le_left (inv_nonneg.2 (by positivity)) (Real.one_le_rpow hN1 hε₁0.le)
    exact h1.trans (h2.trans (h3.le.trans h4))
  have hMΛ : ∀ᶠ n : ℕ in atTop, ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * altGrid_C1 d m *
      (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN := by
    filter_upwards [hsize.eventually (altGrid_ev_rpow_le (a := 2 * ε₁) (b := τN) h2ε₁τN
      (((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * altGrid_C1 d m))),
      hsize.eventually_ge_atTop 1] with n hn hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have e : (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (2 * ε₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
    calc ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * altGrid_C1 d m *
          (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2)
        = (((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * altGrid_C1 d m)) *
          ((sz.size n : ℕ) : ℝ) ^ (2 * ε₁) := by rw [e]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τN := hn
  have hε₀e2 : 0 < ε₀ - e2 := by rw [he2def]; linarith
  have hfin : ∀ᶠ n : ℕ in atTop, 3 / 2 * ((sz.size n : ℕ) : ℝ) ^ e2 + ((sz.size n : ℕ) : ℝ) ^ τN ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ := by
    filter_upwards [hsize.eventually (altGrid_ev_rpow_le (a := 0) (b := ε₀ - e2) hε₀e2 3),
      hsize.eventually_ge_atTop 1] with n hn hN1
    rw [Real.rpow_zero, mul_one] at hn
    exact altGrid_fin_arith hN1 hτNe2 hn
  have hun := altGrid_ev_union sz hsize (m + 1 + 1) D₁
  have hKcal := exists_norm_KI_le_wing Cm μ hsize hKb hKK hη' v hv0 hv1 (m + 1 + 1) 1 one_pos
  have hθ0 : 0 ≤ 1 - min τ 1 := by linarith
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  obtain ⟨hC1, hC2, hC3, hC1', hC2', hC3'⟩ := hCKθ (1 - min τ 1) hθ0 hθ1
  have hC4' : 1 - min τ 1 < C_K := by linarith [hCK1]
  have hlogR := nqBudget_merged_inputsg Cm (κm := κm) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := ((m + 1 + 1 : ℕ) : ℝ) + 1) (s := s) (v := v) (K := K) (m + 1 + 1) hspec him1 hτR hτR1
    one_pos (by positivity) hk2 hsize hs0 hsv hv1 hK0 hrangeV hC1 hC2 hC3 hC4' hKN
  have hsumE := sum_weighted_qErrQNg_le d sz Cm (κm := κm) (τ' := min τ 1) (τK := 1) (C_K := C_K)
    (D_t := ((m + 1 + 1 : ℕ) : ℝ) + 1) (C := altGrid_C1 d m) (C₂ := altGrid_C2 d m) (s := s)
    (t := v) (K := K) (m + 1) hC₁.le hC₂0 hspec him1 hτR hτR1 one_pos (by positivity) (by omega) hsize hs0 hsv
    hv1 hK0 hrangeV hC1' hC2' hC3' hC4' hKN
  have hbudNum := altBudgetNumQNg_eventually Cm m Cv Λg KL (altGrid_C1 d m) (1 / 2) 𝔠 ε ε' τN D' D''
    (((m + 1 + 1 : ℕ) : ℝ) + 1) (((m + 1 + 1 : ℕ) : ℝ) + 1) ε₁ e2 ε₁ (-(2 * ((m + 1 + 1 : ℕ) : ℝ) + 1)) κm
    hd1 hsize hband hκ0 (Eventually.of_forall fun n => hspec.2.1 n) hlam hexp
  have hWt' : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n) := by
    filter_upwards [hWt] with n hn
    refine hn.trans ?_
    have h1 : 0 < 1 - s n := by linarith [hst n, ht1 n]
    exact div_le_div_of_nonneg_right (by linarith [hvt n]) h1.le
  have hwL : ∀ n, v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := fun n => by
    have := hcase n
    linarith [hvt n]
  have hGD : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ HierDriftGen_Expand Cm s v K n ∧ HierDriftGen_KLoop Cm n ∧
      HierDriftGen_KTwo Cm n ∧ HierDriftGen_UStep Cm.toFlowFM n := by
    filter_upwards [hlam, hExp, hKL, hKT, hU] with n h0 h1 h2 h3 h4
    exact ⟨h0.1, h1 s v K, h2, h3, h4⟩
  -- the level split: on the small levels the three quantities of the assembly are `≤ W^{C₀}`
  have hCr : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ σ : Fin (m + 1 + 1) → Bool,
          ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) := by
    filter_upwards [hη, hN2ev, hKcal, hband] with n hηn hN2n hKcaln hbn
    intro u hu0 huv H hH σ
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    exact (QEndGridGen_crude_N Cm hL n (hm n) hk2 hKcaln (fun w k σ a => hKK n w k σ a) (hv1 n) hηn hN2n hu0 huv hH
      σ).trans (altGrid_Npow_le_Wpow h𝔠 hN1 hbn (a := m + 1 + 1 + 2) (c := 8 * (m + 1 + 1) + 8) (by omega))
  have hMee : ∀ᶠ n : ℕ in atTop, altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ ε₁ * Λ n) *
        ((sz.Bctl n u) ^ (2 * (m + 1 + 1)) / Cm.eta n u) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) := by
    filter_upwards [hη, hN2ev, hband, hWbig 1] with n hηn hN2n hbn hW1n
    intro hSn u hu0 huv
    unfold altGrid_small at hSn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hNvn := QEndGridGen_Nv Cm hL (hm n) (hv1 n) hN0 hηn
    obtain ⟨hηu0, hηu, hBu0, hBu⟩ := QEndGridGen_u_facts Cm hL n (hv1 n) hu0 huv hηn hNvn
    have hΛh : 0 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 n) _
    have hΛs : Λ n ^ ((1 : ℝ) / 2) < ((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2) := by
      linarith only [hSn, hΦ₁ n, hΦ₂ n, hΦ₃ n, hX n]
    have hΛle : Λ n ≤ ((sz.size n : ℕ) : ℝ) ^ (4 * (m + 1 + 1) + 4) := by
      have e : Λ n = (Λ n ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hΛ0 n)]; norm_num
      calc Λ n = (Λ n ^ ((1 : ℝ) / 2)) ^ 2 := e
        _ ≤ (((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2)) ^ 2 := pow_le_pow_left₀ hΛh hΛs.le 2
        _ = ((sz.size n : ℕ) : ℝ) ^ (4 * (m + 1 + 1) + 4) := by rw [← pow_mul]; ring_nf
    have hΓ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
    have hΓN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
      calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
        _ = _ := Real.rpow_one _
    have h1 := altGrid_hMee_bound (m + 1 + 1) hN2n hΓ0 hΓN (hΛ0 n) hΛle hBu0.le hBu hηu0 hηu
    have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1n (by linarith [hD''0])
    have h3 := altGrid_pow_succ_le hN2n (8 * (m + 1 + 1) + 7)
    have h4 := altGrid_Npow_le_Wpow h𝔠 hN1 hbn (a := 8 * (m + 1 + 1) + 7 + 1) (c := 8 * (m + 1 + 1) + 8)
      le_rfl
    calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (8 * (m + 1 + 1) + 7) + 1 := by linarith only [h1, h2]
      _ ≤ _ := h3.trans h4
  have hDr : ∀ᶠ n : ℕ in atTop, altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m n → ∀ u : ℝ, 0 ≤ u → u ≤ v n →
      dDriftLinNg Cm n u (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n) ≤
        ((sz.W n : ℕ) : ℝ) ^ (((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) := by
    filter_upwards [hη, hN2ev, hband] with n hηn hN2n hbn
    intro hSn u hu0 huv
    unfold altGrid_small at hSn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hNvn := QEndGridGen_Nv Cm hL (hm n) (hv1 n) hN0 hηn
    obtain ⟨hηu0, hηu, hBu0, hBu⟩ := QEndGridGen_u_facts Cm hL n (hv1 n) hu0 huv hηn hNvn
    have hΛh : 0 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 n) _
    have hΓ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
    have hΓN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
      calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
        _ = _ := Real.rpow_one _
    have h1 := altGrid_dDrift_bound (k := m + 1 + 1) hk2 hN2n hΓ0 hΓN (hΦ₁ n) (hΦ₂ n) (hΦ₃ n)
      (by linarith only [hSn, hΛh, hΦ₂ n, hΦ₃ n, hX n]) (by linarith only [hSn, hΛh, hΦ₁ n, hΦ₃ n, hX n])
      (by linarith only [hSn, hΛh, hΦ₁ n, hΦ₂ n, hX n]) hBu0.le hBu hηu0 hηu
    have h4 := altGrid_Npow_le_Wpow h𝔠 hN1 hbn (a := 8 * (m + 1 + 1) + 7) (c := 8 * (m + 1 + 1) + 8)
      (by omega)
    exact h1.trans h4
  have hsum : ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s v K n p)⁻¹) ^ (m + 1 + 1) *
          qErrQNg Cm.toFlowFM s v K n (m + 1) (altGrid_C1 d m) (altGrid_C2 d m) (((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) *
            (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-(((m + 1 + 1 : ℕ) : ℝ) + 1)) := hsumE
  have hAsm := QEndGridGen_assembly Cm μ m hd hL hW' hspec hm hSeq hS hRow hKK hKb hGD hward hker hK₆ hrow hcol hsize hs0 hsv
    hv1 hK0 Λ Φc Φ₁ Φ₂ Φ₃ X hΛ0 hΦ₁ hΦ₂ hΦ₃ hX (Λg := Λg) (KL := KL) (ε := ε) (ε' := ε') (τ' := τ') (τN := τN)
    (D' := D') (D'' := D'') (Dc := Dc) (ε₁ := ε₁) (εq := ε₁) (τK := 1) (D_Y := ((m + 1 + 1 : ℕ) : ℝ) + 1)
    (D_t := ((m + 1 + 1 : ℕ) : ℝ) + 1) (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K)
    (C₀ := ((8 * (m + 1 + 1) + 8 : ℕ) : ℝ) / 𝔠) hcmp hA hCv hTh hC₆ hΛg hKLpos hε0 hε1 hε'0 hε'1 hε'ε
    hτ'0.le hε₁0.le hε₁1 hD'1 hDc1 (by positivity) hε₁0 one_pos hCK0
    (by positivity) hCKa hD hKN hKU (hYmax K hK0) hwL hWt' hlam (hWbig 4) hWε hWε' hlog hNW hdW1 hdW2 hAk hKer hDD
    hδ (hWbig _) (hWbig _) hWbig hη hνt hFv' hMΛ (altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m) hMee hDr hCr hsum
  filter_upwards [hAsm, hη, hlogR, hbudNum, hΛ1, hun, hKN, hKcal, hfin, hN2ev, hlam, hWbig 4, hνt, hFv', hMΛ]
    with n hAsmn hηn hlogRn hbudn hΛ1n hunn hKNn hKcaln hfinn hN2n hlamn hW4n hνtn hFvn hMΛn
  obtain ⟨hg, hgΛ⟩ := hlamn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altGrid_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hKn : K n ≠ 0 := hK0 n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNvn : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n := QEndGridGen_Nv Cm hL (hm n) (hv1 n) hN0 hηn
  have hBv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.Bctl n (v n) :=
    RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n (hv0 n) (hv1 n)
  have hBv0 : 0 < sz.Bctl n (v n) := STBctl_pos sz n (hv1 n)
  have hBk0 : 0 ≤ (sz.Bctl n (v n)) ^ (m + 1 + 1) := pow_nonneg hBv0.le _
  have hΛh1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ1n (by norm_num)
  have h𝔏1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n := by
    linarith only [hΛh1, hΦ₁ n, hΦ₂ n, hΦ₃ n, hX n]
  have h𝔏0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n := by linarith only [h𝔏1]
  have hν1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁0.le
  have hνN : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) := by
    calc ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
      _ = _ := Real.rpow_one _
  have hϑ : STMollifierProps (d := d) (sz.lam n) (altGrid_C1 d m) (1 / 2)
      (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) :=
    QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hg
  by_cases hbig : ((sz.size n : ℕ) : ℝ) ^ (2 * (m + 1 + 1) + 2) ≤
      Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n
  · -- the big levels: the conclusion follows from the level-free crude bound
    refine ⟨Set.univ, ?_, fun ω _ hgood _ σ hσ a => ?_⟩
    · rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · have hH : (Cm.Hpath s v K n (K n) ω).IsHermitian := (hgood (K n) le_rfl).1.1.1
      have hcr := QEndGridGen_crude_N Cm hL n (hm n) hk2 hKcaln (fun w k σ a => hKK n w k σ a) (hv1 n) hηn hN2n (hv0 n)
        le_rfl hH σ
      exact (norm_le_pi_norm (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b) a).trans
        (hcr.trans (altGrid_big_case (m + 1 + 1) hN1 hε₀.le hBv hbig))
  · have hS : altGrid_small sz Λ Φ₁ Φ₂ Φ₃ X m n := not_le.1 hbig
    by_cases hsvn : s n = v n
    · -- the collapsed window `v_n = s_n`: `G = univ`; de-`𝒬` at `u = s_n = v_n`
      refine ⟨Set.univ, ?_, fun ω _ hgood hinit σ hσ a => ?_⟩
      · rw [Set.compl_univ]
        simp only [measureReal_empty]
        exact Real.rpow_nonneg hN0.le _
      · rw [NQEndLinGen_Hpath_collapse hW' hsvn (K n) ω, ← hsvn]
        have hg0 := hgood 0 (Nat.zero_le _)
        rw [ST_gridTime_zero s v K n] at hg0
        have hs1 : s n < 1 := by rw [hsvn]; exact hv1 n
        have hNs : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - s n := by rw [hsvn]; exact hNvn
        have hunQ := altEnd_unQg hd m Cm hL n hκ0 (hspec.2.1 n) (hm n) hward (hker n) hK₆ (hrow n) (hcol n)
          (H := Cm.Hpath s v K n 0 ω) σ (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (hs0 n)
          hs1 hg hNs hW1 hτ'0.le hν1 (hX n) hνtn hνN hFvn hC₁ (by norm_num) hMΛn hϑ hg0.1.1 hg0.2 hσ a
        have hinit' := hinit σ hσ a
        have hBks0 : 0 ≤ (sz.Bctl n (s n)) ^ (m + 1 + 1) :=
          pow_nonneg (STBctl_pos sz n hs1).le _
        have hN12 : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ e2 :=
          Real.rpow_le_rpow_of_exponent_le hN1 hε₁e2
        have hR : ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) ≤
            ((sz.size n : ℕ) : ℝ) ^ e2 * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
              (sz.Bctl n (s n)) ^ (m + 1 + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hBks0
          exact hN12.trans (le_mul_of_one_le_right (Real.rpow_nonneg hN0.le _) h𝔏1)
        have hDt0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ e2 * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
            (sz.Bctl n (s n)) ^ (m + 1 + 1) / 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) h𝔏0) hBks0) (by norm_num)
        refine altGrid_final_arith (Q := ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n))
          (s n) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
            STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) a‖)
          (R := ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) (Dt := 0)
          (A := ((sz.size n : ℕ) : ℝ) ^ τN) hBks0 (by linarith only [h𝔏1, hΛh1, hΦ₁ n, hΦ₂ n, hΦ₃ n])
          h𝔏0 (Real.rpow_nonneg hN0.le _) hunQ (by linarith only [hinit']) hR hDt0 hfinn
    · -- the non-collapsed window: one event per alternating sign vector
      have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
      have hAsmσ := fun σ : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} =>
        hAsmn hS σ.1 σ.2 hlt
      choose Gs hGsP hGsb using hAsmσ
      refine ⟨⋂ σ, Gs σ, ?_, ?_⟩
      · -- the union bound over the `≤ 2^k` sign vectors
        have hcompl : (⋂ σ, Gs σ)ᶜ = ⋃ σ, (Gs σ)ᶜ := by rw [Set.compl_iInter]
        rw [hcompl]
        calc Cm.Pp.real (⋃ σ, (Gs σ)ᶜ) ≤ ∑ σ, Cm.Pp.real (Gs σ)ᶜ :=
              measureReal_iUnion_fintype_le _
          _ ≤ ∑ _σ : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0},
                ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := Finset.sum_le_sum fun σ _ => hGsP σ
          _ = (Fintype.card {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} : ℝ) *
                ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
          _ ≤ (2 : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hN0.le _)
              have h1 := Fintype.card_subtype_le
                (fun σ : Fin (m + 1 + 1) → Bool => σ (Fin.last (m + 1)) = !σ 0)
              have h2 : Fintype.card (Fin (m + 1 + 1) → Bool) = 2 ^ (m + 1 + 1) := by simp
              rw [h2] at h1
              exact_mod_cast h1
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := hunn
      · intro ω hω hgood hinit σ hσ a
        have hωσ : ω ∈ Gs ⟨σ, hσ⟩ := Set.mem_iInter.1 hω ⟨σ, hσ⟩
        have hb := hGsb ⟨σ, hσ⟩ ω hωσ hgood a
        have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b =>
            ‖aTrueQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b‖) ≤
            ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1) := by
          refine Finset.sup'_le _ _ fun b _ => ?_
          have h := hinit σ hσ b
          have h0 : AvecNg Cm s v K n 0 σ ω =
              fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b := by
            funext b
            simp only [AvecNg, ST_gridTime_zero]
          have e : aTrueQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b =
              STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                  STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) b := by
            simp only [aTrueQNg, ST_gridTime_zero, h0]
          rw [e]
          exact h
        obtain ⟨ha1, ha2, ha3, he0', he1, he2', he3, he4⟩ := hbudn
        have hη0 : 0 ≤ (Cm.eta n (v n))⁻¹ := inv_nonneg.2 (NQGood1Gen_eta_pos hL n (hv1 n)).le
        have hΔη := altGrid_hΔη sz (C_K := C_K) (η := Cm.eta n (v n)) hCK1 hKNn hvs hη0 hηn
        have hdd : ∀ j < K n, dDriftAltLinQNg Cm n (gridTime s v K n j) m
            (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n)
            (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n) ≤
            (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) * ε') *
              (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
                ((sz.size n : ℕ) : ℝ) ^ τN) * (Φ₁ n + Φ₂ n + Φ₃ n + X n) *
              ((sz.Bctl n (gridTime s v K n j)) ^ (m + 1 + 1) / Cm.eta n (gridTime s v K n j)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) := by
          intro j hj
          have hj1 : j ≤ K n := hj.le
          exact dDriftAltLinQNg_le_shape Cm hL n (gridTime s v K n j) m _ (Φ₁ n) (Φ₂ n) (Φ₃ n) _ ε' D' τN
            (X n) ((altGrid_gridTime_le (hsv n) hKn hj1).trans_lt (hv1 n)) (hΦ₁ n) (hΦ₂ n) (hΦ₃ n)
            (by linarith only [hX n])
        have hbud := budgetAltQNg Cm hL s v K n m Cv Λg KL (altGrid_C1 d m) (1 / 2) ε
          (fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁) Λ
          (fun j => dDriftAltLinQNg Cm n (gridTime s v K n j) m (((sz.size n : ℕ) : ℝ) ^ ε₁)
            (Φ₁ n) (Φ₂ n) (Φ₃ n) (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)) ε' D' τN (X n))
          (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2) * ε') *
              (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
                ((sz.size n : ℕ) : ℝ) ^ τN)
          (Φ₁ n + Φ₂ n + Φ₃ n + X n)
          (((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL (altGrid_C1 d m) (1 / 2)))
          (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D''
          (((m + 1 + 1 : ℕ) : ℝ) + 1) (((m + 1 + 1 : ℕ) : ℝ) + 1) 1 ε₁ e2 ε₁
          (Finset.univ.sup' Finset.univ_nonempty fun b =>
            ‖aTrueQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω b‖) a
          hε₁0.le (hm n) (hs0 n) (hsv n) (hv1 n) hKn hηn hΔη rfl hΛ1n (by positivity)
          (by linarith only [hΦ₁ n, hΦ₂ n, hΦ₃ n, hX n]) (by positivity) (by positivity) (by positivity)
          hdd hlogRn.1 hX0 hlogRn.2 ha1 ha2 ha3 he0' he1 he2' he3 he4
        have hdt := altGrid_Dt_absorb (m + 1 + 1) hN2n he2.le hBv h𝔏1
        have hunQ := altEnd_unQg hd m Cm hL n hκ0 (hspec.2.1 n) (hm n) hward (hker n) hK₆ (hrow n) (hcol n)
          (H := Cm.Hpath s v K n (K n) ω) σ (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (hv0 n) (hv1 n)
          hg hNvn hW1 hτ'0.le hν1 (hX n) hνtn hνN hFvn hC₁ (by norm_num) hMΛn hϑ
          (by have := (hgood (K n) le_rfl).1.1; rwa [gridTime_last s v K n hKn] at this)
          (by have := (hgood (K n) le_rfl).2; rwa [gridTime_last s v K n hKn] at this) hσ a
        have h0K : AvecNg Cm s v K n (K n) σ ω =
            fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
              STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b := by
          funext b
          simp only [AvecNg, gridTime_last s v K n hKn]
        have e : aTrueQNg Cm s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ (K n) ω a =
            STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (v n)
              (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b) a := by
          simp only [aTrueQNg, gridTime_last s v K n hKn, h0K]
        rw [e] at hb
        have e𝔏 : Λ n ^ ((1 : ℝ) / 2) + (Φ₁ n + Φ₂ n + Φ₃ n + X n) =
            Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n := by ring
        rw [e𝔏] at hbud
        refine altGrid_final_arith (Q := ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n))
          (v n) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
            STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b) a‖) hBk0
          (by linarith only [h𝔏1, hΛh1, hΦ₁ n, hΦ₂ n, hΦ₃ n]) h𝔏0 (Real.rpow_nonneg hN0.le _) hunQ hb hbud
          ?_ hfinn
        exact hdt

end Endpoint

/-! ## 4. Compiled nonempty instances (`d = 3`, band carrier `bandStep2Mat sz0 Einst`)

Data of the band instances `NQEndLinInst` (`Induction/NQEndLin.lean:1277-1592`, public facts by name; the data of `NQEndLinGenCheck`): `sz0` (`n = 0`: `L = 4`,
`W = 32`, `N = 2^21`, `lam = 1/64`), `E = Einst ≡ 1/2`, `κ = 1` (`κ' = κi = min κ (4/5)`), `s = sInst ≡ 0`, `t = tInst ≡ 1/16`, `v = vg ≡ 1/32` (`Δ > 0` on every grid
`KC C_K`), `τ = 1/2`, `𝔠 = 1/6`, `𝔡 = 1/10`, `m ≥ 0` arbitrary (tensors of `m + 2 ≥ 2` indices), levels `Λ = 3`, `Φ₁ = Φ₃ = 1`, `Φ₂ = 12`, `X = 1`, `ε₀ = 1/10`, `D₁ = 1`.
The D1 constant is `C4 = qProxy4C 3 (m + 2) 10 κi (1/𝔠)` (abstract, `> 0`); `A = 1`, `Cv = C4`.  Every hypothesis is discharged (`STKboundgL` by `stKbound_holds`; the drift classes,
the kernel class, `LoopForm`, `WalkForm`, the spectral data, the Ward and kernel-sum data, `Step5KerGen_ThDecay` by the band lemmas); the good-walk and initial hypotheses stay in the
conclusion. -/

end RBM.BA

end
