/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QBudgetB
import RBM3D.Induction.QGridB
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.NQGood2
import RBM3D.Induction.GridAssemblyN

/-!
# Vocabulary, the `hY` event at length `n_ - 1`, and the compositions for the alternating endpoint

Paper: Lemma 4.10 (`lem:STOeq_Qt`), the alternating case in Subsection 4.5 `subsec:support` ((4.59)
`y27kasdfg`, (4.61) `A4`, (4.60) `A5`), (4.32) `normQA`.

* §0 vocabulary `altYSetN`, `altExitTauN`;
* §1 `measurableAltYSetN`, `mem_of_lt_altExitTauN`, `altExitMeasN`;
* §2 `altYGridN`: the `hY` event at length `l` on the grid at the level `N^ε X`;
* §3 the `𝒬`-remainder envelope `gridDriftQN_envelope'` and the bridge `assembledRHSAltQN_qErr_le`;
* §4 the variance proxy after the spectral-time shift: `hQ_altQN`, `subGaussStop_altQN`;
* §5 the kernel field on the grid: `alt_hkerGridQN`;
* §6 the drift and class fields on the exit family: `alt_hdriftGridQN`, `alt_hA0clsGridQN`,
  `alt_hDclsGridQN`, and the crude-sup derivation `altEnd_driftSup`;
* §7 the identity, measurability, terminal value and de-`𝒬`: `altEnd_hexp`,
  `altEnd_stronglyMeasurable_zVecQN`, `altEnd_aFroz_eq_aTrue`, `altEnd_unQ`.

The generic twins over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`, `open RBM.BA`, no `BA/*`
import), after §7: `altYSetNg`, `altExitTauNg` (§0g), `measurableAltYSetNg`, `mem_of_lt_altExitTauNg`,
`altExitMeasNg` (§1g), `altYGridNg` (§2g), `gridDriftQNg_envelope_ev` and
`assembledRHSAltQNg_qErr_le` (§3g), `hQ_altQNg`, `subGaussStop_altQNg` (§4g: `QProxyG_KerEK4` at the
kernel coupling `gK`, the comparison of couplings, two radii `ε₁ ≤ ε`), `alt_hkerGridQNg` (§5g),
`alt_hdriftGridQNg`, `alt_hA0clsGridQNg`, `alt_hDclsGridQNg`, `altEnd_driftSupg` (§6g),
`altEnd_hexpg`, `altEnd_stronglyMeasurable_zVecQNg`, `altEnd_aFroz_eq_aTrueg`, `altEnd_unQg` (§7g).
`LoopForm` and the inline `‖Cm.m n‖ ≤ 1` are used in place of `|E n| < 2`; the spectral levels of
`ℬ₄ + ℬ₅` are the fields of `B45Gen_Facts`.

Helpers are `private` or prefixed `altEnd_`.
-/

open private GridGoodGen_precL_whp from RBM3D.Chain.GridGoodGen
open private gridGood_gridTime_mem from RBM3D.Induction.GridGoodN

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ## 0. Vocabulary -/

/-- **The `hY` set at length `l`**: the fine matrices whose `(𝓛-𝒦)^{(l)}` loops are at most
`Y · B_u^l` at every sign vector and label (the `hY` premise of `altB45N_levelM`, `alt_hdriftLinQN` at `ν X := Y`). -/
def altYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | ∀ (σ' : Fin l → Bool) (a' : Fin l → Zd d (sz.L n)),
    ‖sz.STLKM n E u H σ' a'‖ ≤ Y * sz.Bctl n u ^ l}

/-- **The alternating exit time**: `nqLinExitTauN` with the `hY` set at length `k - 1` added
(`GoodSetN` at the crude level `Φc`, `GoodLinN` at the linear levels, `altYSetN` at the level `Yl`). -/
noncomputable def altExitTauN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetN sz n (E n) (gridTime s v K n j) (k - 1) (Yl n))

/-! ## 1. Measurability and the exit family -/

section Meas

private theorem altEnd_measurableSet_forall {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {p : ι → α → Prop} (h : ∀ i, MeasurableSet {x | p i x}) :
    MeasurableSet {x | ∀ i, p i x} := by
  have e : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter h

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem altEnd_meas_loopFine (E u : ℝ) {j : ℕ} (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopFine d (sz.L n) (sz.W n) H (zt E u) σ a :=
  walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a

/-- **`measurableAltYSetN`**: `altYSetN` is a measurable set of matrices (a finite intersection over the
labels of sublevel sets of the measurable norms of the loop observables). -/
theorem measurableAltYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) :
    MeasurableSet (altYSetN sz n E u l Y) := by
  unfold altYSetN
  refine altEnd_measurableSet_forall fun σ' => altEnd_measurableSet_forall fun a' => ?_
  exact measurableSet_le (((altEnd_meas_loopFine sz n E u σ' a').sub_const _).norm) measurable_const

end Meas

/-- **`mem_of_lt_altExitTauN`**: strictly before the exit, the grid state is in `GoodSetN ∩ GoodLinN ∩ altYSetN`
(`mem_of_lt_gridExitTauN`). -/
theorem mem_of_lt_altExitTauN {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ}
    {Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ} {τ' D' : ℝ} {n : ℕ} {ω : PathΩ sz} {j : ℕ}
    (h : j < altExitTauN sz E s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω) :
    pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetN sz n (E n) (gridTime s v K n j) (k - 1) (Yl n) :=
  mem_of_lt_gridExitTauN h

/-- **`altExitMeasN`**: `{j < altExitTauN}` is `filt j`-measurable (`gridExitTauN_measurableSet` with
`measurableGoodSetN`, `measurableGoodLinN`, `measurableAltYSetN`). -/
theorem altExitMeasN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < altExitTauN sz E s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω} :=
  gridExitTauN_measurableSet (fun j =>
    ((measurableGoodSetN d sz n _ _ _ _ _ _ _ _).inter
      (measurableGoodLinN sz n _ _ _ _ _ _ _)).inter (measurableAltYSetN sz n _ _ _ _)) j

/-! ## 2. The `hY` event on the grid (`altYGridN`) -/

section Grid

/-- Clause `STXiLKM ≤ Z` read as an entry bound: `‖(𝓛-𝒦)^{(j)}_{σ,a}(H)‖ ≤ (Z - 1) B^j` (as in `QLevelsB`). -/
private theorem altEnd_norm_STLKM_le_of_XiLKM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (j : ℕ) {Z : ℝ}
    (hB : 0 < sz.Bctl n u) (h : sz.STXiLKM n E u j H ≤ Z) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) : ‖sz.STLKM n E u H σ a‖ ≤ (Z - 1) * sz.Bctl n u ^ j := by
  have hBj : 0 < sz.Bctl n u ^ j := pow_pos hB j
  unfold STXiLKM at h
  have h1 : ‖sz.STLKM n E u H σ a‖ ≤ STmaxLKM sz n E u j H :=
    Finset.le_sup' (fun p : (Fin j → Bool) × (Fin j → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖)
      (Finset.mem_univ (σ, a))
  have h2 : STmaxLKM sz n E u j H / sz.Bctl n u ^ j ≤ Z - 1 := by linarith
  rw [div_le_iff₀ hBj] at h2
  exact h1.trans h2

private theorem altEnd_measurable_pathH {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j

private theorem altEnd_measurable_seqHflow {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) :
    Measurable (sz.seqHflow n u) :=
  Measurable.of_eval_matrix _ fun i j => measurable_seqHflow_entry sz n u i j

/-- **The transfer and the union bound** (as the private `gridGood_grid`, and
`nqLin_grid`, with `altYSetN`): if w.h.p. `seqHflow n u ω ∈ altYSetN … u` for every
`u ∈ [s_n,v_n]`, then w.h.p. the grid walk `pathH … j` is in `altYSetN` at every `j ≤ K n`. -/
private theorem altEnd_yGrid {d : ℕ} (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hK : ∀ n, K n ≠ 0) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) {l : ℕ} {Y : ℕ → ℝ}
    (hW : Whp sz (fun n => {ω | ∀ u : TimeIcc s v n, sz.seqHflow n (u : ℝ) ω ∈
      altYSetN sz n (E n) (u : ℝ) l (Y n)})) :
    HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
      pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l (Y n)}) := by
  have hgrid : ∀ n j, j ≤ K n →
      pathP sz {ω | pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l (Y n)}ᶜ ≤
      sz.seqP {ω | ∀ u : TimeIcc s v n, sz.seqHflow n (u : ℝ) ω ∈
        altYSetN sz n (E n) (u : ℝ) l (Y n)}ᶜ := by
    intro n j hj
    have hmem := ST_gridTime_mem s v K n j (hsv n) (hK n) hj
    have hG := (measurableAltYSetN sz n (E n) (gridTime s v K n j) l (Y n)).compl
    have h1 := Measure.map_apply (μ := pathP sz) (altEnd_measurable_pathH sz s v K n j) hG
    have h2 := Measure.map_apply (μ := sz.seqP)
      (altEnd_measurable_seqHflow sz n (gridTime s v K n j)) hG
    have h3 := map_pathH_eq sz s v K n j (hs0 n) (hsv n) (hK n)
    have e1 : {ω | pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l (Y n)}ᶜ =
        pathH sz s v K n j ⁻¹' (altYSetN sz n (E n) (gridTime s v K n j) l (Y n))ᶜ := by
      ext ω; simp
    rw [e1, ← h1, h3, h2]
    refine measure_mono ?_
    intro ω hω hall
    exact hω (hall ⟨gridTime s v K n j, hmem⟩)
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hI := highProbAt_iInter (pathP sz) sz.size (K := fun n => Fin (K n + 1))
    (Ξ := fun n j => {ω | pathH sz s v K n j.1 ω ∈
      altYSetN sz n (E n) (gridTime s v K n j.1) l (Y n)}) (C := max C 0)
    (le_max_right _ _)
    (by
      filter_upwards [hC] with n hn
      rw [Fintype.card_fin]
      exact hn.trans (Real.rpow_le_rpow_of_exponent_le (hN1 n) (le_max_left _ _)))
    (fun D hD => (hW D hD).mono fun n hn j =>
      (hgrid n j.1 (Nat.lt_succ_iff.1 j.2)).trans hn)
  refine hI.mono (Eventually.of_forall fun n ω hω j hj => ?_)
  exact Set.mem_iInter.1 hω ⟨j, Nat.lt_succ_of_le hj⟩

end Grid

/-- **`altYGridN`**: from
the deterministic bound `Ξ̂^{(𝓛-𝒦)}_l ≺ X` uniformly on `[s_n, v_n]`, with high probability the grid walk is in
`altYSetN` at the level `N^ε X` at every grid time `j ≤ K n` (`Prec.whp` at the exponent `ε`; `STXiLKM ≤ Z` gives
`‖(𝓛-𝒦)^{(l)}‖ ≤ (Z-1)B^l ≤ Z B^l`; `map_pathH_eq` at each `j`; `highProbAt_iInter`, `K n + 1 ≤ N^C`).  It is used
with `l = n_ - 1`. -/
theorem altYGridN :
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (l : ℕ) (X : ℕ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) → (∀ n, K n ≠ 0) → (∀ n, 1 ≤ X n) →
    Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLK sz n (E n) (u : ℝ) l ω) (fun n _ _ => X n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l
          (((sz.size n : ℕ) : ℝ) ^ ε * X n)}) := by
  intro d sz E s v K l X hs0 hsv hv1 hK hX hP C hC ε hε
  have hW : Whp sz (fun n => {ω | ∀ u : TimeIcc s v n, sz.seqHflow n (u : ℝ) ω ∈
      altYSetN sz n (E n) (u : ℝ) l (((sz.size n : ℕ) : ℝ) ^ ε * X n)}) := by
    refine (hP.whp sz hε).mono (Eventually.of_forall fun n ω hω u => ?_)
    have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
    have hB : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz hu1
    have hBl : 0 ≤ sz.Bctl n (u : ℝ) ^ l := (pow_pos hB l).le
    intro σ' a'
    have h : sz.STXiLKM n (E n) (u : ℝ) l (sz.seqHflow n (u : ℝ) ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * X n := hω u
    refine (altEnd_norm_STLKM_le_of_XiLKM sz n (E n) (u : ℝ) _ l hB h σ' a').trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hBl
  exact altEnd_yGrid sz hs0 hsv hK hC hW

/-! ## 3. The `𝒬`-remainder envelope and the bridge to `assembledRHSAltQN` -/

section C1

private theorem altEnd_gridStep_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n) :
    0 ≤ gridStep s v K n :=
  div_nonneg (sub_nonneg.2 hsv) (Nat.cast_nonneg _)

private theorem altEnd_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (j : ℕ) : 0 ≤ gridTime s v K n j := by
  have hΔ := altEnd_gridStep_nonneg (s := s) (v := v) (K := K) hsv
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem altEnd_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

private theorem altEnd_gridTime_lt_one {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) (hv1 : v n < 1) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i < 1 :=
  (altEnd_gridTime_le hsv hK hi).trans_lt hv1

/-- **`gridDriftQN_envelope'`**: the `𝒬`-remainder `rGridQN` along the grid is bounded by `qErrQN` at the
envelope `N^{τ_K} η_{u_{j+1}}^{-(m+2)}`, a.e., eventually in `n`, for every grid step `j < K n` and label
(tensors of `m + 2 ≥ 2` indices, `m : ℕ` arbitrary; the call to `gridDriftQN` is at the mollifier index
`m + 1 ≥ 1`). -/
theorem gridDriftQN_envelope' {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ)
    (τK : ℝ) (hτK : 0 < τK) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : sz.STKbound E) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n)
    (σ : Fin (m + 1 + 1) → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n → ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖rGridQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω a‖ ≤
        qErrQN sz E s v K n (m + 1) ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)))
          (1000 * (1 + ((d * (m + 1) : ℕ) : ℝ)) ^ 2)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j := by
  classical
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hv1' : ∀ n j, j < K n → gridTime s v K n (j + 1) < 1 := fun n j hj =>
    altEnd_gridTime_lt_one (hsv n) (hK0 n) (hv1 n) (show j + 1 ≤ K n by omega)
  -- the deterministic envelope statement at the grid step `j`
  let P : ℕ → ℕ → Prop := fun n j => ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s v K n (j + 1)),
    ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ m + 1 + 1 →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)
  have hP : ∀ᶠ n in atTop, ∀ j, j < K n → P n j := by
    by_contra hcon
    have hfreq := Filter.not_eventually.1 hcon
    let bad : ℕ → Prop := fun n => ∃ j, j < K n ∧ ¬ P n j
    have hbad : ∀ n, ¬ (∀ j, j < K n → P n j) → bad n := by
      intro n hn
      by_contra hb
      exact hn fun j hj => by
        by_contra hc
        exact hb ⟨j, hj, hc⟩
    let w₀ : ℕ → ℝ := fun n =>
      if h : bad n then gridTime s v K n (Classical.choose h + 1) else 0
    have hvmem : ∀ n, 0 ≤ w₀ n ∧ w₀ n < 1 := by
      intro n
      by_cases h : bad n
      · have e : w₀ n = gridTime s v K n (Classical.choose h + 1) := by simp [w₀, h]
        rw [e]
        exact ⟨altEnd_gridTime_nonneg (hs0 n) (hsv n) _, hv1' n _ (Classical.choose_spec h).1⟩
      · have e : w₀ n = 0 := by simp [w₀, h]
        rw [e]
        exact ⟨le_rfl, one_pos⟩
    have hwin := exists_norm_Kcal_le_win sz hsize E hKb hE2 w₀ (fun n => (hvmem n).1)
      (fun n => (hvmem n).2) (m + 1 + 1) τK hτK
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hwin).exists
    have hbn : bad n := hbad n hn1
    obtain ⟨hjlt, hnP⟩ := Classical.choose_spec hbn
    have e : w₀ n = gridTime s v K n (Classical.choose hbn + 1) := by simp [w₀, hbn]
    apply hnP
    intro w hw J hJ h2 hJk
    have hb := hn2 w (by rw [e]; exact hw) J hJ h2 hJk
    rw [e] at hb
    exact hb
  filter_upwards [hP, hlam] with n hn hlamn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hη : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos (hE2 n) (hv1' n j hj)
    have hBk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη.le) _)
    have h := gridDriftQN sz E s v K n j (hE2 n) (hs0 n) (hsv n) (hv1 n) (hK0 n) hj hlamn (m := m + 1)
      (by omega) σ _ hBk (hn j hj)
    exact h.mono fun ω hω _ a => hω a
  · exact Eventually.of_forall fun ω h => absurd h hj

/-- `kappaAltQN` is nonnegative. -/
private theorem altEnd_kappa_nonneg (d k : ℕ) (Λg κ' KL g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ)
    (i m : ℕ) : 0 ≤ kappaAltQN d k Λg κ' KL g W ε u i m := by
  unfold kappaAltQN
  exact mul_nonneg (Real.rpow_nonneg hW _)
    (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

/-- The step error of `gridDriftN` is nonnegative (as the private `nqEnd_stepErrN_nonneg`). -/
private theorem altEnd_stepErrN_nonneg {d L W : ℕ} {E u v Δ Bk : ℝ} {k : ℕ} (hE : |E| < 2)
    (hu1 : u < 1) (hv1 : v < 1) (hΔ : 0 ≤ Δ) (hBk : 0 ≤ Bk) : 0 ≤ stepErrN d L W E k u v Δ Bk := by
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hv : 0 < 1 - v := by linarith
  have hηi : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hη.le
  have h1 : 0 ≤ envConst d L W E k v * Δ ^ ((3 : ℝ) / 2) := by
    unfold envConst
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hΔ _)
  have h2 : 0 ≤ kStepC d L W k Bk * Δ ^ 2 := by
    unfold kStepC; positivity
  have h3 : 0 ≤ uStepC k Δ v := by
    unfold uStepC
    have hx : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ (inv_nonneg.2 hv.le)
    have hb : 1 + (k : ℝ) * (Δ * (1 - v)⁻¹) ≤ (1 + Δ * (1 - v)⁻¹) ^ k := by
      have := one_add_mul_le_pow (a := Δ * (1 - v)⁻¹) (by linarith : (-2 : ℝ) ≤ Δ * (1 - v)⁻¹) k
      simpa using this
    have hk : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
    nlinarith
  have h4 : 0 ≤ (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk := by
    have : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
    positivity
  unfold stepErrN
  have := mul_nonneg h3 h4
  linarith

/-- **`assembledRHSAltQN_qErr_le`** (the bridge).  The right side of
`AssembledN` at the target `m = K n` for the alternating chain (`κ = kappaAltQN`,
`εK = epsAltQN`, `c = cQVAltQN`, `k = m + 2`, `u = gridTime`), with the remainder `stepErr := qErrQN` (the `𝒬`-process
remainder of `gridDriftQN_envelope'`) and an initial supremum `Xs ≤ X0`, is at most `assembledRHSAltQN` (whose last term
is the non-alternating `stepErrN`) plus `N^{-D_t}`, once the weighted `qErrQN` sum is at
most `N^{-D_t}` (`sum_weighted_qErrQN_le` at `m ↦ m + 1`).  The five common terms are identical and
`stepErrN ≥ 0`. -/
theorem assembledRHSAltQN_qErr_le {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (Λg κ' KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (δ0 δD D'' D_Y τK εq Xs X0 D_t C₁ C₂ : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n))
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hτK : 0 ≤ τK)
    (hX : Xs ≤ X0)
    (hsum : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        qErrQN sz E s v K n (m + 1) C₁ C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t)) :
    kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * Xs +
      epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 +
      gridStep s v K n * ∑ j ∈ Finset.range (K n),
        (kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
            dd j +
          epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) +
      ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
        (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' (K n) a j : ℝ)) +
      ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
      ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        qErrQN sz E s v K n (m + 1) C₁ C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
          (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
    assembledRHSAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ dd δ0 δD D'' D_Y τK εq X0 a +
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  have hKu : gridTime s v K n (K n) = v n := gridTime_last s v K n hK
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => altEnd_gridTime_lt_one hsv hK hv1 hi
  have hΔ := altEnd_gridStep_nonneg (s := s) (v := v) (K := K) hsv
  have hWn : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk := altEnd_kappa_nonneg d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hWn
    (gridTime s v K n) 0 (K n)
  have hX' : kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * Xs ≤
      kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 :=
    mul_le_mul_of_nonneg_left hX hk
  have hw : 0 ≤ (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) := by
    rw [hKu]
    have : 0 ≤ (1 - v n)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  have hS : 0 ≤ ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
      stepErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg hw ?_
    have hj' := Finset.mem_range.1 hj
    have hη : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hE (hu1 (j + 1) hj')
    exact altEnd_stepErrN_nonneg hE (hu1 j hj'.le) (hu1 (j + 1) hj') hΔ
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη.le) _))
  unfold assembledRHSAltQN
  linarith

end C1

/-! ## 4. The variance proxy after the spectral-time shift, and `SubGaussStopN` -/

section C2

/-- The two `W`-power facts behind the shift `D ↦ D'' + 1` of `hQ_altQN`: `W^{2C_nε}·W^{-(D''+1)} ≤ W^{-(D''+1)+C_Q}` and
`2·W^{-(D''+1)+C_Q} ≤ W^{-D''+C_Q}` (`C_Q = 2C_n + 2`, `0 < C_n`, `ε < 1`, `2 ≤ W`). -/
private theorem altEnd_shift_rpow {W Cn ε D : ℝ} (hW : 2 ≤ W) (hCn : 0 < Cn) (hε : ε < 1) :
    W ^ (2 * Cn * ε) * W ^ (-(D + 1)) ≤ W ^ (-(D + 1) + (2 * Cn + 2)) ∧
      2 * W ^ (-(D + 1) + (2 * Cn + 2)) ≤ W ^ (-D + (2 * Cn + 2)) := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  refine ⟨?_, ?_⟩
  · rw [← Real.rpow_add hW0]
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    nlinarith
  · have hyx : W ^ (-D + (2 * Cn + 2)) = W ^ (-(D + 1) + (2 * Cn + 2)) * W := by
      rw [← Real.rpow_add_one hW0.ne']
      congr 1; ring
    have hx0 : 0 ≤ W ^ (-(D + 1) + (2 * Cn + 2)) := Real.rpow_nonneg hW0.le _
    rw [hyx]
    nlinarith

/-- The monotone arithmetic of `hQ_altQN`: replacing `x ↦ y` and `P(G + z) + x ↦ PG + y` in the closed form of
`qvFormQN_le_of_bounds`. -/
private theorem altEnd_qv_arith {κ4 A B P G x y z : ℝ} (hκ4 : 0 ≤ κ4) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hPz : P * z ≤ x) (h2x : 2 * x ≤ y) (hx0 : 0 ≤ x) :
    κ4 * (κ4 * (P * (G + z) + x) + A * x) + A * (B * x) ≤
      κ4 * (κ4 * (P * G + y) + A * y) + A * (B * y) := by
  have hin : P * (G + z) + x ≤ P * G + y := by rw [mul_add]; linarith
  have hxy : x ≤ y := by linarith
  gcongr

/-- **`hQ_altQN`** (RBM2D `hQ_alt`; the pattern of `hQ_nonAltN`; fixed `n`): for `M ∈ GoodSetN n E u_j (m+2) Γ Λ Φc τ' D'` Hermitian and every `σ`, the proxy
`Δ · ((m+2) · qvFormQN_{u_{j+1},u_p}(M)(a))` of the `j`-th propagated `𝒬`-increment towards `u_p` is at most
`cQVAltQN … D'' p a j`.  Proof: the bound on `STeeM` and the far-label decay of `(ℰ⊗ℰ)^M` in `GoodSetN` at `u_j` are moved to `u_{j+1}` by
`norm_STeeM_shiftN_le`, `B_{u_j} ≤ B_{u_{j+1}}`, `η_{u_j}⁻¹ ≤ η_{u_{j+1}}⁻¹`, `ℓ_{u_j} ≤ ℓ_{u_{j+1}}`, then
`qvFormQN_le_of_bounds` at `m ↦ m + 1`, `v := u_{j+1}`, `w := u_p`, `D := D'' + 1`,
`M_ee = Γ(ΓΛ)B_{u_{j+1}}^{2k}/η_{u_{j+1}} + W^{-(D''+1)}`.  The shift hypothesis is
`W^{-D'} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-(D''+1)}` together with `2 ≤ W` (the
literal `≤ W^{-D''}` does not give `qvBdAltQN … D''`, because `qvBdAltQN` has no `W^{2C_nε - D}` term; the extra
`+1` pays the factor `2`). -/
theorem hQ_altQN {d m : ℕ} (Λg κ' KL C c : ℝ) (hd : 3 ≤ d) (hΛg : 0 < Λg) (hκ' : 0 < κ')
    (hKL : 0 < KL) (hC : 0 < C) (hc : 0 < c) (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' C₀ D' D'' : ℝ}
    (hW : 2 ≤ ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hC₀ : 0 ≤ C₀)
    (hD : ((m + 1 : ℕ) : ℝ) + 2 + qProxyCQ d (m + 1) Λg KL C c < D'' + 1)
    (hW₀ : qProxyW0 d (m + 1) Λg KL C c C₀ ε (D'' + 1) ≤ ((sz.W n : ℕ) : ℝ))
    {ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ}
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    {σ : Fin (m + 1 + 1) → Bool} (Γ Λ Φc : ℕ → ℝ) (p : ℕ) (hp : p ≤ K n)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p)
    (hMee : Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        etaT (E n) (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1)
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1))) :
    ∀ M ∈ sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (Γ n) (Λ n) (Φc n) τ' D',
      M.IsHermitian → gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) *
        qvFormQN sz n ϑ (E n) (gridTime s v K n (j + 1)) (gridTime s v K n p) σ M a) ≤
        (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' p a j : ℝ) := by
  intro M hM hMh
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := hM
  have hΔ : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hu0 : 0 ≤ gridTime s v K n j := altEnd_gridTime_nonneg hs0 hsv j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    ST_gridTime_mono s v K n hsv (Nat.le_succ j)
  have hj1p : gridTime s v K n (j + 1) ≤ gridTime s v K n p :=
    ST_gridTime_mono s v K n hsv (by omega)
  have hK : K n ≠ 0 := by omega
  have hpv : gridTime s v K n p ≤ v n := altEnd_gridTime_le hsv hK hp
  have hj1v : gridTime s v K n (j + 1) ≤ v n := hj1p.trans hpv
  have hs1 : s n ≤ gridTime s v K n (j + 1) := by
    have h := ST_gridTime_mono s v K n hsv (Nat.zero_le (j + 1))
    rwa [ST_gridTime_zero] at h
  have hwin : (((sz.W n : ℕ) : ℝ))⁻¹ ≤
      (1 - gridTime s v K n p) / (1 - gridTime s v K n (j + 1)) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have hL3 := sz.three_le_L n
  have hLpos : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hgL : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have hu'1 : gridTime s v K n (j + 1) < 1 := by linarith
  have hu1 : gridTime s v K n j < 1 := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWτ : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  have hWD'' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := Real.rpow_nonneg hW0.le _
  have hWD' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hηu := etaT_pos hE hu1
  have hηu' := etaT_pos hE hu'1
  have hηle : etaT (E n) (gridTime s v K n (j + 1)) ≤ etaT (E n) (gridTime s v K n j) :=
    RBM.Green.etaT_le_of_le hE hjj
  have hBu : 0 < sz.Bctl n (gridTime s v K n j) := STBctl_pos sz n hu1
  have hBu' : 0 < sz.Bctl n (gridTime s v K n (j + 1)) := STBctl_pos sz n hu'1
  have hBle : sz.Bctl n (gridTime s v K n j) ≤ sz.Bctl n (gridTime s v K n (j + 1)) :=
    STBctl_mono sz n hjj hu'1
  have hmono : ∀ G : ℝ, 0 ≤ G →
      G * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * (m + 1 + 1)) / etaT (E n) (gridTime s v K n j)) ≤
      G * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        etaT (E n) (gridTime s v K n (j + 1))) := fun G hG0 =>
    mul_le_mul_of_nonneg_left (div_le_div₀ (pow_nonneg hBu'.le _)
      (pow_le_pow_left₀ hBu.le hBle _) hηu' hηle) hG0
  have hLK' : ellT (sz.L n) (sz.lam n) (gridTime s v K n j) ≤
      ellT (sz.L n) (sz.lam n) (gridTime s v K n (j + 1)) := nqGood1_ellT_mono _ _ hjj hu'1
  have hshift := fun b b' => norm_STeeM_shiftN_le sz n hE hMh hjj hu'1 σ b b'
  have htri : ∀ b b' : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b'‖ ≤
        ‖sz.STeeM n (E n) (gridTime s v K n j) M σ b b'‖ +
          eeShiftErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j)
            (gridTime s v K n (j + 1)) := by
    intro b b'
    have h3 : ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b'‖ ≤
        ‖sz.STeeM n (E n) (gridTime s v K n j) M σ b b'‖ +
          ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b' -
            sz.STeeM n (E n) (gridTime s v K n j) M σ b b'‖ := by
      have := norm_add_le (sz.STeeM n (E n) (gridTime s v K n j) M σ b b')
        (sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b' -
          sz.STeeM n (E n) (gridTime s v K n j) M σ b b')
      rwa [add_sub_cancel] at this
    linarith only [h3, hshift b b']
  have hD4' : ∀ b b', ‖sz.STeeM n (E n) (gridTime s v K n j) M σ b b'‖ ≤
      Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * (m + 1 + 1)) /
        etaT (E n) (gridTime s v K n j)) := fun b b' => hD4 σ b b'
    -- `G ≥ 0` is forced by the bound on `STeeM` (a norm is nonnegative and the quotient is positive)
  have hGnn : 0 ≤ Γ n * (Γ n * Λ n) := by
    have h0 := (norm_nonneg _).trans (hD4' (fun _ => 0) (fun _ => 0))
    have hq : 0 < (sz.Bctl n (gridTime s v K n j)) ^ (2 * (m + 1 + 1)) /
        etaT (E n) (gridTime s v K n j) := div_pos (pow_pos hBu _) hηu
    exact nonneg_of_mul_nonneg_left h0 hq
  have hT : ∀ b b' : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b'‖ ≤
        Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
          etaT (E n) (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    intro b b'
    have h1 := hD4' b b'
    have h2 := htri b b'
    have h3 := hmono _ hGnn
    linarith only [h1, h2, h3, hδ, hWD']
  have hTfar : ∀ b b' : Fin (m + 1 + 1) → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) (gridTime s v K n (j + 1)) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
          (STdiamInf (Fin.append b b') : ℝ) →
        ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    intro b b' hfar
    have hfar' : ellT (sz.L n) (sz.lam n) (gridTime s v K n j) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
        (STdiamInf (Fin.append b b') : ℝ) := (mul_le_mul_of_nonneg_right hLK' hWτ).trans hfar
    have h1 := hVb σ b b' hfar'
    have h2 := htri b b'
    linarith only [h1, h2, hδ]
  have key := qvFormQN_le_of_bounds (m := m + 1) hd (by omega) Λg κ' KL C c hΛg hκ' hKL hC hc sz n hg hgΛ
    hW1 hε0 hε1 hWε hlog hLK hdW hC₀ hD hW₀ hϑ (hu0.trans hjj) hj1p (hpv.trans hwL) hwin hE.le hκm M
    hMee hT hTfar a
  have hCn : 0 < qProxyCn d (m + 1) Λg KL C c := qProxyCn_pos hd (m + 1) hΛg hKL hC hc
  have hCQ : qProxyCQ d (m + 1) Λg KL C c = 2 * qProxyCn d (m + 1) Λg KL C c + 2 := rfl
  have hq : qvFormQN sz n ϑ (E n) (gridTime s v K n (j + 1)) (gridTime s v K n p) σ M a ≤
      qvBdAltQN sz n (E n) m Λg κ' KL C c ε (Γ n) (Λ n) D'' (gridTime s v K n (j + 1))
        (gridTime s v K n p) := by
    refine key.trans ?_
    unfold qvBdAltQN
    obtain ⟨hPz, h2x⟩ := altEnd_shift_rpow (D := D'') (ε := ε) hW hCn hε1
    have hx0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1) + qProxyCQ d (m + 1) Λg KL C c) :=
      Real.rpow_nonneg hW0.le _
    rw [hCQ] at hx0 ⊢
    refine altEnd_qv_arith (by positivity) (by positivity) (by positivity) hPz h2x hx0
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) hΔ

/-- **`subGaussStop_altQN`** (RBM2D `subGaussStop_alt`; pattern
`subGaussStop_linN`): `azumaSubGQ_gridExitN` at the alternating exit
family of `altExitTauN` (the family `GoodSetN ∩ GoodLinN ∩ altYSetN`; measurable by the ingredients of `altExitMeasN`) and the
`hQ` premise from `hQ_altQN` on the `GoodSetN` component: sub-Gaussianity of the stopped propagated first-chaos part
`zVecQN` (mollifier `QopAlgebra_mollifier … (m+1)`, constants `C = (1 + 40 d(m+1)) 6^{d(m+1)}`, `c = 1/2`) with the
explicit proxy `cQVAltQN`.  Hypotheses as `hQ_altQN`. -/
theorem subGaussStop_altQN {d m : ℕ} (Λg κ' KL : ℝ) (hd : 3 ≤ d) (hΛg : 0 < Λg) (hκ' : 0 < κ')
    (hKL : 0 < KL) (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' C₀ D' D'' : ℝ}
    (hW : 2 ≤ ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hC₀ : 0 ≤ C₀)
    (hD : ((m + 1 : ℕ) : ℝ) + 2 + qProxyCQ d (m + 1) Λg KL
        ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2) < D'' + 1)
    (hW₀ : qProxyW0 d (m + 1) Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
      C₀ ε (D'' + 1) ≤ ((sz.W n : ℕ) : ℝ))
    {σ : Fin (m + 1 + 1) → Bool} (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (p : ℕ) (hp : p ≤ K n)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p)
    (hMee : Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        etaT (E n) (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1)
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1))) :
    SubGaussStopN sz (E n) σ (gridTime s v K n)
      (altExitTauN sz E s v K (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n)
      (fun j ω => zVecQN sz E s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω) p a j
      (cQVAltQN sz E s v K n m Λg κ' KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
        ε Γ Λ D'' p a j) := by
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  have hϑ := QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hg
  exact azumaSubGQ_gridExitN sz hE hs0 hsv hv1 n (m + 1) (by omega)
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ
    (fun j => sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (Γ n) (Λ n) (Φc n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) (m + 1 + 1) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetN sz n (E n) (gridTime s v K n j) (m + 1) (Yl n))
    (fun j => ((measurableGoodSetN d sz n _ _ _ _ _ _ _ _).inter
      (measurableGoodLinN sz n _ _ _ _ _ _ _)).inter (measurableAltYSetN sz n _ _ _ _))
    p hp a j hj _
    (fun M hM hMh => hQ_altQN Λg κ' KL _ (1 / 2) hd hΛg hκ' hKL hC0 (by norm_num) sz E s v K n (hE n) (hs0 n)
      (hsv n) (hv1 n) hwL hWt hκm hg hgΛ hW hε0 hε1 hWε hlog hLK hdW hC₀ hD hW₀ hϑ Γ Λ Φc p hp a j hj
      hMee hδ M hM.1.1 hMh)

end C2

/-! ## 5. The kernel field on the grid -/

section C3

/-- **`alt_hkerGridQN`** (RBM2D `altQ_hker_shift`, reduced; the field `hker` of
`GridAssemblyHypN`): `alt_hkerQN` at the grid `u = gridTime s v K n`, `Kg = K n`
(`0 ≤ u_i` from `s n ≥ 0`, monotone `ST_gridTime_mono`, `u_{K n} = v n` `gridTime_last`), with the regime premises
explicit (case (i) only here: `v n ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-v_n)/(1-s_n)`).  `Cls = altClsQN … ε' Dc` (the class radius
exponent `ε'` of `alt_hA0clsQN`, `alt_hDclsQN`), `κ = kappaAltQN`, `εK = epsAltQN` (tensors of `m + 2` indices). -/
theorem alt_hkerGridQN {d m : ℕ} (Λg κ' KL : ℝ) (hd : 3 ≤ d) (hΛg : 0 < Λg) (hκ' : 0 < κ') (hKL : 0 < KL)
    (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hK : K n ≠ 0)
    (hE : |E n| ≤ 2) (hκm : κ' ≤ (mE (E n)).im) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg)
    {ε ε' Dc : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hDc : 1 < Dc)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (σ : Fin (m + 1 + 1) → Bool) :
    ∀ i m', i ≤ m' → m' ≤ K n → ∀ (X : (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v K n) i δ X →
      ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n i) (gridTime s v K n m') X a‖ ≤
          kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) i m' * M +
            epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) i m' * δ := by
  have hKu : gridTime s v K n (K n) = v n := gridTime_last s v K n hK
  have h0u : gridTime s v K n 0 = s n := ST_gridTime_zero s v K n
  exact alt_hkerQN Λg κ' KL hd (by omega) hΛg hκ' hKL (sz.three_le_L n) hg hgΛ hW hε0 hε1 hWε hlog hLK hdW
    hDc (Kg := K n) (u := gridTime s v K n) (fun i _ => altEnd_gridTime_nonneg hs0 hsv i)
    (fun i m' him _ => ST_gridTime_mono s v K n hsv him) (by rw [hKu]; exact hwL)
    (by rw [hKu, h0u]; exact hWt) hE hκm σ

end C3

/-! ## 6. The drift and class fields on the alternating exit family -/

section C4

/-- **`alt_hdriftGridQN`** (the field `hdrift` of `GridAssemblyHypN`): `alt_hdriftLinQN` with `τ := altExitTauN`; the premise `hτG` is components 1 and 2 of
`mem_of_lt_altExitTauN` and the premise `hY` is component 3 at the level `Yl n ≤ ν X`
(`altYSetN` at length `k - 1 = m + 1`; used with `Yl n = N^{ε₁} X n`). -/
theorem alt_hdriftGridQN :
  ∀ (d m : ℕ) (Λg KL : ℝ), 3 ≤ d → 0 < Λg → 0 < KL →
    ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
      (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (κ τ' ε' D' ν X τN : ℝ),
      0 < κ → |E n| ≤ 2 - κ → 0 < sz.lam n → sz.lam n ≤ Λg →
      0 ≤ s n → s n ≤ v n → v n < 1 → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n →
      1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' →
      4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      1 ≤ ν → 1 ≤ X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) →
      ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ →
      (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) *
          ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) * ν ^ 2) ≤
        ((sz.size n : ℕ) : ℝ) ^ τN →
      Yl n ≤ ν * X →
      σ (Fin.last (m + 1)) = !σ 0 →
      ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n →
        j < altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
        ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n),
          ‖dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω b‖ ≤
            dDriftAltLinQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
              (qProxyCn d (m + 1) Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2))
              ε' D' τN X := by
  intro d m Λg KL hd hΛg hKL sz n σ E s v Kg Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl κ τ' ε' D' ν X τN hκ hE hlam hlamΛ hs0 hsv hv1
    hNv hW hτ' hε hε1 hD h4 hLW hdW hν hX hνt hνN hFv hMΛ hYl hσ ω j hjK hjτ b
  have hKne : Kg n ≠ 0 := by omega
  have hu1 : gridTime s v Kg n j < 1 := altEnd_gridTime_lt_one hsv hKne hv1 hjK.le
  have hB : 0 ≤ sz.Bctl n (gridTime s v Kg n j) ^ (m + 1) := (pow_pos (STBctl_pos sz n hu1) _).le
  refine alt_hdriftLinQN d m Λg KL hd hΛg hKL sz n σ E s v Kg Γ Λ Φc Φ₁ Φ₂ Φ₃ κ τ' ε' D' ν X τN
    (altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n) hκ hE hlam hlamΛ hs0 hsv hv1 hNv hW hτ'
    hε hε1 hD h4 hLW hdW hν hX hνt hνN hFv hMΛ hσ (fun ω' j' hj' => (mem_of_lt_altExitTauN hj').1)
    (fun ω' j' hj' σ' a' => ?_) ω j hjK hjτ b
  have hjK' : j' < Kg n := hj'.trans_le (gridExitTauN_le ω')
  have hu1' : gridTime s v Kg n j' < 1 := altEnd_gridTime_lt_one hsv hKne hv1 hjK'.le
  have hB' : 0 ≤ sz.Bctl n (gridTime s v Kg n j') ^ (m + 1) := (pow_pos (STBctl_pos sz n hu1') _).le
  have h : ‖sz.STLKM n (E n) (gridTime s v Kg n j') (pathH sz s v Kg n j' ω') σ' a'‖ ≤
      Yl n * sz.Bctl n (gridTime s v Kg n j') ^ (m + 1) := (mem_of_lt_altExitTauN hj').2 σ' a'
  exact h.trans (mul_le_mul_of_nonneg_right hYl hB')

/-- **`alt_hA0clsGridQN`** (the field `hA0cls` of `GridAssemblyHypN`): `alt_hA0clsQN`
(tensors of `m + 2` indices) with `τ := altExitTauN`: `hτG` is component 1 of
`mem_of_lt_altExitTauN` (`k = m + 1 + 1`, crude level `Φc`), and the crude sup `‖A_0‖ ≤ W^{C₀}` is an explicit premise
(a bound on `‖(𝓛-𝒦)^{(m+2)}(H_0)‖` at length `k`, which no clause of `GoodSetN` gives).
The class exponent is `ε'` (`d W^{τ'} ≤ W^{ε'}`), the radius level `Dc ≤ D' - 1`. -/
theorem alt_hA0clsGridQN {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (m : ℕ) (K C₀ ε' D' : ℝ) (hε' : 0 < ε')
    {n : ℕ} (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' Dc : ℝ)
    (hW : QDriftA_W0 d (m + 1) K ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2) C₀ ε' D' ≤
      ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hlam : 0 < sz.lam n) (hs0 : 0 ≤ s n) (hs1 : s n < 1)
    (hcrude : ∀ ω, 0 < altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
      ‖AvecN sz E s v Kg n 0 σ ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    ∀ ω, 0 < altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) 0
        (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
        (aTrueQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω) :=
  alt_hA0clsQN sz hd (m + 1) K _ (1 / 2) C₀ ε' D' (by positivity) (by norm_num) hε' σ E s v Kg Γ Λ Φc τ' Dc
    (altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n)
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hW hLK hdW hDD hlam hs0 hs1
    (QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hlam)
    (fun ω' j' hj' => (mem_of_lt_altExitTauN hj').1.1) hcrude

/-- **`alt_hDclsGridQN`** (the field `hDcls` of `GridAssemblyHypN`): `alt_hDclsQN`
(tensors of `m + 2` indices, the existential `W₀` of its statement) with
`τ := altExitTauN`: `hτG` is component 1 of `mem_of_lt_altExitTauN`; the crude sups `hAcr`
(`‖(𝓛-𝒦)^{(m+2)}(H_j)‖ ≤ W^{C₀}`) and `hDcr` (`‖driftTensorN‖ ≤ W^{C₀}`) are explicit premises
(the second is derived from the exit family by `altEnd_driftSup`). -/
theorem alt_hDclsGridQN :
  ∀ (d m : ℕ) (Λg K C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ)
      (Kg : ℕ → ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' Dc : ℝ),
      |E n| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      0 ≤ s n → s n ≤ v n → v n < 1 → (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
      (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
        ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
          sz.STLKM n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ C₀) →
      (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
        ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
          driftTensorN sz n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ C₀) →
      ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n →
        j < altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
        altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1)
          (4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
          (dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω) := by
  intro d m Λg K C₀ ε' D' hd hΛg hε'
  obtain ⟨W₀, hW₀, H⟩ := alt_hDclsQN d (m + 1) Λg K C₀ ε' D' hd hΛg hε'
  refine ⟨W₀, hW₀, ?_⟩
  intro sz n σ E s v Kg Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' Dc hE hlam hlamΛ hW hLK hs0 hsv hv1 hKv hdW hDD hAcr hDcr
  exact H sz n σ E s v Kg Γ Λ Φc τ' Dc (altExitTauN sz E s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n)
    hE hlam hlamΛ hW hLK hs0 hsv hv1 hKv hdW hDD (fun ω' j' hj' => (mem_of_lt_altExitTauN hj').1.1)
    hAcr hDcr

/-- **The crude sup of the drift tensor from the exit family** (deterministic):
`GoodLinN` (component 2) gives `‖driftTensorN‖ ≤ dDriftLinN` (`driftTensorN_norm_le_of_goodLin`), so a bound
`dDriftLinN ≤ W^{C₀}` gives the `hDcr` premise of `alt_hDclsGridQN`. -/
theorem altEnd_driftSup {d : ℕ} (sz : Sizes d) (n : ℕ) {E u Γ Φ₁ Φ₂ Φ₃ C₀ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H ∈ GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃)
    (hW : dDriftLinN sz n E u k Γ Φ₁ Φ₂ Φ₃ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (σ : Fin k → Bool) :
    ‖fun b : Fin k → Zd d (sz.L n) => driftTensorN sz n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hWpos.le C₀)).2 fun b =>
    (driftTensorN_norm_le_of_goodLin sz hk hH σ b).trans hW

end C4

/-! ## 7. The identity, measurability, terminal value, de-`𝒬` -/

section C5

/-- **`altEnd_hexp`** (RBM2D `altEnd_identity`; literally the field `hexp` of
`GridAssemblyHypN` at `A := aFrozQN`, `A0 := aTrueQN … 0`, `Dr := dGridQN`, `Z := zVecQN`, `Y := yVecQN`,
`R := rGridQN`): for every stopping index `τ` and target `m' ≤ K n`, a.e.,
`A^{Q,frz}_{m'} = 𝒰_{u_0,u_{m'}} A^Q_0 + Σ_{j < m' ∧ τ} 𝒰_{u_{j+1},u_{m'}}(Δ dGridQN_j + zVecQN_j + yVecQN_j + rGridQN_j)`
(`stoppedDuhamelQN` with `martIncQN_ae_eq` at every `j < K n`). -/
theorem altEnd_hexp {d m : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool)
    (τ : PathΩ sz → ℕ) :
    ∀ m' ≤ K n, ∀ᵐ ω ∂(pathP sz),
      aFrozQN sz E s v K n ϑ σ τ m' ω =
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n 0) (gridTime s v K n m')
            (aTrueQN sz E s v K n ϑ σ 0 ω) +
          ∑ j ∈ Finset.range (min m' (τ ω)),
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n m')
              ((gridStep s v K n : ℂ) • dGridQN sz E s v K n ϑ σ j ω + zVecQN sz E s v K n j ϑ σ ω +
                yVecQN sz E s v K n j ϑ σ ω + rGridQN sz E s v K n ϑ σ j ω) := by
  intro m' hm'
  have hmart : ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n →
      martIncQN sz E s v K n ϑ σ j ω = zVecQN sz E s v K n j ϑ σ ω + yVecQN sz E s v K n j ϑ σ ω := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hj : j < K n
    · have hj1 : gridTime s v K n (j + 1) < 1 := altEnd_gridTime_lt_one hsv hK hv1 (by omega)
      have h := ae_all_iff.2 fun a => martIncQN_ae_eq sz E s v K n j hE hj1 ϑ σ a
      exact h.mono fun ω hω _ => funext hω
    · exact Eventually.of_forall fun ω h => absurd h hj
  filter_upwards [hmart] with ω hω
  rw [stoppedDuhamelQN sz E s v K n hE hs0 hsv hv1 hK ϑ σ τ m' ω hm']
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < K n := (Finset.mem_range.1 hj).trans_le ((min_le_left _ _).trans hm')
  rw [hω j hj', ← add_assoc ((gridStep s v K n : ℂ) • dGridQN sz E s v K n ϑ σ j ω)]

/-- **`altEnd_stronglyMeasurable_zVecQN`**: `zVecQN … j` is `filt sz (j + 1)`-strongly measurable
(`gridAsm_stronglyMeasurable_ZvecN` composed with the continuous linear `STQop ϑ u_{j+1}` on the finite-dimensional
space of tensors). -/
theorem altEnd_stronglyMeasurable_zVecQN {d m : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => zVecQN sz E s v K n j ϑ σ ω) := by
  have hZ := gridAsm_stronglyMeasurable_ZvecN sz E s v K n j σ
  have hcont : Continuous (STQop (d := d) ϑ (gridTime s v K n (j + 1)) :
      ((Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) := by
    refine continuous_pi fun a => ?_
    unfold STQop STPsum
    exact (continuous_apply a).sub ((continuous_finsetSum _ fun b _ => continuous_apply b).mul
      continuous_const)
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.comp _ _ _ (filt sz (j + 1)) _ _ _ _ hcont.measurable hZ.measurable

/-- **`altEnd_aFroz_eq_aTrue`**: on `{K n ≤ τ ω}` the stopped `𝒬`-process (`aFrozQN`) at the last grid index is the true
one (`min (K n) (τ ω) = K n`, `𝒰_{u,u} = id`: `GridDuhamelN_Ugen_self`). -/
theorem altEnd_aFroz_eq_aTrue {d m : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| ≤ 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool)
    (τ : PathΩ sz → ℕ) (ω : PathΩ sz) (hτ : K n ≤ τ ω) :
    aFrozQN sz E s v K n ϑ σ τ (K n) ω = aTrueQN sz E s v K n ϑ σ (K n) ω := by
  unfold aFrozQN
  rw [min_eq_left hτ]
  exact GridDuhamelN_Ugen_self (sz.three_le_L n) hE σ (altEnd_gridTime_nonneg hs0 hsv _)
    (altEnd_gridTime_lt_one hsv hK hv1 le_rfl) _

/-- **`altEnd_unQ`** (de-`𝒬` at the end, per matrix; RBM2D `altEnd_unQ`): for alternating `σ`, under the
hypotheses of `altB45N_levelM` (`QLevelsA.lean`; `GoodSetN` at a free crude level gives Hermitian and the decay clause; `hY` the
length-`m + 1` level at `u`; the mollifier `ϑ` with `STMollifierProps`),
`‖(𝓛-𝒦)_{u,σ}(H)_a‖ ≤ ‖𝒬_u(𝓛-𝒦)_{u,σ}(H)_a‖ + N^{τ_N} B_u^{m+2} X`
(`STQop` unfolded, the first conjunct of `altB45N_levelM`, `norm_add_le`).  It is applied at `u = v_n`,
`H = H_{K n}` (the `altYSetN` component and the decay clause at `j = K n`, `u_{K n} = v_n`). -/
theorem altEnd_unQ {d : ℕ} (hd : 3 ≤ d) (m : ℕ) (sz : Sizes d) (n : ℕ)
    (E u κ Γc Λc Φc τ' D' ν X τN C c : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hlam : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hτ' : 0 ≤ τ')
    (hν : 1 ≤ ν) (hX : 1 ≤ X) (hνt : (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν)
    (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹)
    (hC : 0 < C) (hc : 0 < c)
    (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * C * ν ^ 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ τN)
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hG : H ∈ sz.GoodSetN n E u (m + 1 + 1) Γc Λc Φc τ' D')
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖sz.STLKM n E u H σ a‖ ≤
      ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a‖ +
        ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hωf : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW.le hτ'
  have hHerm : H.IsHermitian := hG.1
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
        ‖sz.STLKM n E u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := fun σ' a' hfar =>
    goodSetN_LKM_far d sz n E u (m + 1 + 1) Γc Λc Φc τ' D' H hG (m + 1) (by omega) (by omega) σ' a' hfar
  have hexp : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine (hϑ.2.1 u hu0 hu1 a).trans ?_
    have hl : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos (by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hex : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ)) / ellT (sz.L n) (sz.lam n) u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hc.le hS]) hl.le
    have hC0 : 0 ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) := by positivity
    calc _ ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hex hC0
      _ = _ := by rw [mul_one]
  have hB45 := altB45N_levelM d (by omega) sz n E u κ hκ hE hu0 hu1 hlam hNu H hHerm m (2 / Real.sqrt κ) ν X
    (((sz.W n : ℕ) : ℝ) ^ τ') (((sz.W n : ℕ) : ℝ) ^ (-D')) C τN rfl hν hX hωf hνt hνN hFv
    (Real.rpow_nonneg hWpos.le _) hC.le hMΛ hY hF ϑ hexp (fun a => hϑ.2.2.2 u hu0 hu1 a) σ hσ a
  have e : sz.STLKM n E u H σ a =
      STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a +
        STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
          ϑ u a := by
    unfold STQop; ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hB45.1)

end C5
/-! ## 0g. The vocabulary over a carrier -/

section VocabG

variable {d : ℕ} {sz : Sizes d}

/-- **The `hY` set at length `l` over a carrier** (band `altYSetN`): the fine matrices whose `(𝓛-𝒦)^{(l)}` loops are at most `Y · B_u^l` at every sign vector and label
(`STLKMg Cm n u H`). -/
def altYSetNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (l : ℕ) (Y : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | ∀ (σ' : Fin l → Bool) (a' : Fin l → Zd d (sz.L n)), ‖STLKMg Cm n u H σ' a'‖ ≤ Y * sz.Bctl n u ^ l}

/-- **The alternating exit time over a carrier** (band `altExitTauN`): `nqLinExitTauNg` (`Chain/NQLinGen`) with the `hY` set at length `k - 1` added (`GoodSetNg` at the
crude level `Φc`, `GoodLinNg` at the linear levels, `altYSetNg` at the level `Yl`). -/
noncomputable def altExitTauNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauNg Cm s v K n (fun j =>
    {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' H} ∩
      GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetNg Cm n (gridTime s v K n j) (k - 1) (Yl n))

end VocabG

/-! ## 1g. Measurability and the exit family over a carrier -/

section MeasG

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz}

/-- `altYSetNg` is a measurable set of matrices under `LoopForm` (band `measurableAltYSetN`). -/
theorem measurableAltYSetNg {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) (l : ℕ) (Y : ℝ) :
    MeasurableSet (altYSetNg Cm n u l Y) := by
  have hLM := (GridGoodGen_meas_of_loopForm hL n u).1
  unfold altYSetNg
  refine altEnd_measurableSet_forall fun σ' => altEnd_measurableSet_forall fun a' => ?_
  exact measurableSet_le (((hLM l σ' a').sub_const _).norm) measurable_const

/-- Strictly before the exit, the grid state is in `GoodSetNg ∩ GoodLinNg ∩ altYSetNg` (band `mem_of_lt_altExitTauN`). -/
theorem mem_of_lt_altExitTauNg {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ}
    {Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ} {τ' D' : ℝ} {n : ℕ} {ω : PathΩ sz} {j : ℕ}
    (h : j < altExitTauNg Cm s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω) :
    Cm.Hpath s v K n j ω ∈ {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' H} ∩
      GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetNg Cm n (gridTime s v K n j) (k - 1) (Yl n) :=
  mem_of_lt_gridExitTauNg h

/-- `{j < altExitTauNg}` is `filt j`-measurable (band `altExitMeasN`): `gridExitTauNg_measurableSet` under `StepDecompGen_WalkForm`, with `measurableGoodSetNg`, `measurableGoodLinNg`,
`measurableAltYSetNg` under `LoopForm`. -/
theorem altExitMeasNg {E lam' : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < altExitTauNg Cm s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω} :=
  gridExitTauNg_measurableSet hW (fun j =>
    ((measurableGoodSetNg hL n _ k _ _ _ _ _).inter (measurableGoodLinNg hL n _ _ _ _ _ _)).inter
      (measurableAltYSetNg hL n _ _ _)) j

end MeasG

/-! ## 2g. The `hY` event on the grid over a carrier (`altYGridNg`) -/

section GridG

variable {d : ℕ} {sz : Sizes d}

/-- Clause `STXiLKMg ≤ Z` read as an entry bound: `‖(𝓛-𝒦)^{(j)}_{σ,a}(H)‖ ≤ (Z - 1) B^j` (band `altEnd_norm_STLKM_le_of_XiLKM`). -/
private theorem altEnd_norm_STLKMg_le_of_XiLKM (Cm : Step2Mat sz) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (j : ℕ) {Z : ℝ}
    (hB : 0 < sz.Bctl n u) (h : STXiLKMg Cm n u j H ≤ Z) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) : ‖STLKMg Cm n u H σ a‖ ≤ (Z - 1) * sz.Bctl n u ^ j := by
  have hBj : 0 < sz.Bctl n u ^ j := pow_pos hB j
  unfold STXiLKMg at h
  have h1 : ‖STLKMg Cm n u H σ a‖ ≤ STmaxLKMg Cm n u j H :=
    Finset.le_sup' (fun p : (Fin j → Bool) × (Fin j → Zd d (sz.L n)) => ‖Cm.LM n u H p.1 p.2 - Cm.K n u p.1 p.2‖)
      (Finset.mem_univ (σ, a))
  have h2 : STmaxLKMg Cm n u j H / sz.Bctl n u ^ j ≤ Z - 1 := by linarith
  rw [div_le_iff₀ hBj] at h2
  exact h1.trans h2

/-- **The transfer and the union bound** (band `altEnd_yGrid`; the proof of `NQLinGen_grid` with `altYSetNg`): if with high probability `Hf n u ω ∈ altYSetNg … u` for every
`u ∈ [s_n,v_n]`, then with high probability the carrier walk `Cm.Hpath … j` is in `altYSetNg` at every grid index `j ≤ K n`. -/
private theorem altEnd_yGridg {Cm : Step2Mat sz} {E : ℕ → ℝ} {μ : Measure sz.SeqΩ}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hLaw : Step2EventsGen_Law Cm μ Hf) {s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hK : ∀ n, K n ≠ 0) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) {l : ℕ} {Y : ℕ → ℝ}
    (hW : HighProbAt μ sz.size (fun n => {ω | ∀ u : TimeIcc s v n, Hf n (u : ℝ) ω ∈
      altYSetNg Cm n (u : ℝ) l (Y n)})) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
      Cm.Hpath s v K n j ω ∈ altYSetNg Cm n (gridTime s v K n j) l (Y n)}) := by
  have hgrid : ∀ n j, j ≤ K n →
      Cm.Pp {ω | Cm.Hpath s v K n j ω ∈ altYSetNg Cm n (gridTime s v K n j) l (Y n)}ᶜ ≤
      μ {ω | ∀ u : TimeIcc s v n, Hf n (u : ℝ) ω ∈ altYSetNg Cm n (u : ℝ) l (Y n)}ᶜ := by
    intro n j hj
    have hmem := gridGood_gridTime_mem hsv (fun n => le_rfl) hK n j hj
    have hG := (measurableAltYSetNg hL n (gridTime s v K n j) l (Y n)).compl
    have e1 : {ω | Cm.Hpath s v K n j ω ∈ altYSetNg Cm n (gridTime s v K n j) l (Y n)}ᶜ =
        {ω | Cm.Hpath s v K n j ω ∈ (altYSetNg Cm n (gridTime s v K n j) l (Y n))ᶜ} := by
      ext ω; simp
    rw [e1, hLaw s v K n j (hs0 n) (hsv n) (hK n) _ hG]
    refine measure_mono ?_
    intro ω hω hall
    exact hω (hall ⟨gridTime s v K n j, hmem⟩)
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hI := highProbAt_iInter Cm.Pp sz.size (K := fun n => Fin (K n + 1))
    (Ξ := fun n j => {ω | Cm.Hpath s v K n j.1 ω ∈ altYSetNg Cm n (gridTime s v K n j.1) l (Y n)}) (C := max C 0)
    (le_max_right _ _)
    (by
      filter_upwards [hC] with n hn
      rw [Fintype.card_fin]
      exact hn.trans (Real.rpow_le_rpow_of_exponent_le (hN1 n) (le_max_left _ _)))
    (fun D hD => (hW D hD).mono fun n hn j =>
      (hgrid n j.1 (Nat.lt_succ_iff.1 j.2)).trans hn)
  refine hI.mono (Eventually.of_forall fun n ω hω j hj => ?_)
  exact Set.mem_iInter.1 hω ⟨j, Nat.lt_succ_of_le hj⟩

/-- **`altYGridNg`** (band `altYGridN`): from the bound `Ξ̂^{(𝓛-𝒦)}_l ≺ X` uniformly on `[s_n, v_n]` at the law `μ` of the flow
matrix `Hf` (`LoopForm`, `Step34Gen_LCompat`, the law `Step2EventsGen_Law`), with high probability the carrier walk is in `altYSetNg` at the level `N^ε X` at every grid time `j ≤ K n`
(`GridGoodGen_precL_whp` at the exponent `ε`; `STXiLKMg ≤ Z` gives `‖(𝓛-𝒦)^{(l)}‖ ≤ (Z-1)B^l ≤ Z B^l`; `K n + 1 ≤ N^C`). -/
theorem altYGridNg {E : ℕ → ℝ} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hL : StepDecompGen_LoopForm Cm E) (hC : Step34Gen_LCompat Cm Hf) (hLaw : Step2EventsGen_Law Cm μ Hf)
    (s v : ℕ → ℝ) (K : ℕ → ℕ) (l : ℕ) (X : ℕ → ℝ)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK : ∀ n, K n ≠ 0)
    (hP : PrecL sz μ (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) l ω) (fun n _ _ => X n))
    {C : ℝ} (hCK : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) {ε : ℝ} (hε : 0 < ε) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
      Cm.Hpath s v K n j ω ∈ altYSetNg Cm n (gridTime s v K n j) l (((sz.size n : ℕ) : ℝ) ^ ε * X n)}) := by
  have hW : HighProbAt μ sz.size (fun n => {ω | ∀ u : TimeIcc s v n, Hf n (u : ℝ) ω ∈
      altYSetNg Cm n (u : ℝ) l (((sz.size n : ℕ) : ℝ) ^ ε * X n)}) := by
    refine (GridGoodGen_precL_whp hP hε).mono (Eventually.of_forall fun n ω hω u => ?_)
    have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
    have hB : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz hu1
    have hBl : 0 ≤ sz.Bctl n (u : ℝ) ^ l := (pow_pos hB l).le
    intro σ' a'
    have h : STXiLKMg Cm n (u : ℝ) l (Hf n (u : ℝ) ω) ≤ ((sz.size n : ℕ) : ℝ) ^ ε * X n := by
      rw [STXiLKMg_Hf (fun n u k σ a ω => GridGoodGen_LM_eq_L hL hC n u σ a ω)]
      exact hω u
    refine (altEnd_norm_STLKMg_le_of_XiLKM Cm n (u : ℝ) _ l hB h σ' a').trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hBl
  exact altEnd_yGridg hL hLaw hs0 hsv hK hCK hW

end GridG

/-! ## 3g. The `𝒬`-remainder envelope and the bridge to `assembledRHSAltQNg` -/

section C1G

/-- **`gridDriftQNg_envelope_ev`** (band `gridDriftQN_envelope'`): `gridDriftQNg` (`Chain/QGridGen`) at `m ↦ m + 1` with its
drift premise per index under `∀ᶠ n` (`0 < sz.lam n` and the classes `HierDriftGen_Expand`, `HierDriftGen_KLoop`, `HierDriftGen_KTwo`, `HierDriftGen_UStep`), `hS`, the all-`w` link, `‖m‖ ≤ 1`, `hη` for every `n`, and the wing envelope
`exists_norm_KI_le_wing` (under `STKboundgL`): eventually in `n`, a.e., for every grid step `j < K n` and label, the `𝒬`-remainder `rGridQNg` (tensors of `m + 2` indices,
mollifier at `m + 1`) is at most `qErrQNg` at the envelope `N^{τ_K} η_{u_{j+1}}^{-(m+2)}` of `𝒦` on `[0, u_{j+1}]`. -/
theorem gridDriftQNg_envelope_ev :
  ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) (E lam' : ℕ → ℝ)
    (Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (m : ℕ) (τK : ℝ), 0 < τK → ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ), sz.SizeTendsto → STKboundgL Cm.toFlowFM μ →
    StepDecompGen_LoopForm Cm E → StepDecompGen_WalkForm Cm lam' Ψ →
    (∀ n (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) →
    (∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a) → (∀ n, ‖Cm.m n‖ ≤ 1) →
    (∀ (n : ℕ) (v : ℝ), 0 ≤ v → v < 1 → 0 < Cm.eta n v ∧ Cm.eta n v ≤ 1 - v) →
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    (∀ᶠ n in atTop, 0 < sz.lam n ∧ HierDriftGen_Expand Cm s t K n ∧ HierDriftGen_KLoop Cm n ∧ HierDriftGen_KTwo Cm n ∧
      HierDriftGen_UStep Cm.toFlowFM n) →
    ∀ σ : Fin (m + 1 + 1) → Bool, ∀ᶠ n in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n → ∀ a,
      ‖rGridQNg Cm s t K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω a‖ ≤
        qErrQNg Cm.toFlowFM s t K n (m + 1) ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)))
          (1000 * (1 + ((d * (m + 1) : ℕ) : ℝ)) ^ 2)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j := by
  intro d sz Cm E lam' Ψ μ _ m τK hτK s t K hsize hKb hL hW hS hKK hm hη hs0 hst ht1 hK hev σ
  classical
  have hv1' : ∀ n j, j < K n → gridTime s t K n (j + 1) < 1 := fun n j hj =>
    altEnd_gridTime_lt_one (hst n) (hK n) (ht1 n) (show j + 1 ≤ K n by omega)
  -- the deterministic envelope statement at the grid step `j`
  let P : ℕ → ℕ → Prop := fun n j => ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)),
    ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ m + 1 + 1 →
      ‖Cm.KI n w J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1 + 1)
  have hP : ∀ᶠ n in atTop, ∀ j, j < K n → P n j := by
    by_contra hcon
    have hfreq := Filter.not_eventually.1 hcon
    let bad : ℕ → Prop := fun n => ∃ j, j < K n ∧ ¬ P n j
    have hbad : ∀ n, ¬ (∀ j, j < K n → P n j) → bad n := by
      intro n hn
      by_contra hb
      exact hn fun j hj => by
        by_contra hc
        exact hb ⟨j, hj, hc⟩
    let w₀ : ℕ → ℝ := fun n =>
      if h : bad n then gridTime s t K n (Classical.choose h + 1) else 0
    have hvmem : ∀ n, 0 ≤ w₀ n ∧ w₀ n < 1 := by
      intro n
      by_cases h : bad n
      · have e : w₀ n = gridTime s t K n (Classical.choose h + 1) := by simp [w₀, h]
        rw [e]
        exact ⟨altEnd_gridTime_nonneg (hs0 n) (hst n) _, hv1' n _ (Classical.choose_spec h).1⟩
      · have e : w₀ n = 0 := by simp [w₀, h]
        rw [e]
        exact ⟨le_rfl, one_pos⟩
    have hwin := exists_norm_KI_le_wing Cm μ hsize hKb hKK hη w₀ (fun n => (hvmem n).1)
      (fun n => (hvmem n).2) (m + 1 + 1) τK hτK
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hwin).exists
    have hbn : bad n := hbad n hn1
    obtain ⟨hjlt, hnP⟩ := Classical.choose_spec hbn
    have e : w₀ n = gridTime s t K n (Classical.choose hbn + 1) := by simp [w₀, hbn]
    apply hnP
    intro w hw J hJ h2 hJk
    have hb := hn2 w (by rw [e]; exact hw) J hJ h2 hJk
    rw [e] at hb
    exact hb
  filter_upwards [hP, hev] with n hn hevn
  obtain ⟨hlamn, hExp, hKL, hKT, hU⟩ := hevn
  refine ae_all_iff.2 fun j => ?_
  by_cases hj : j < K n
  · have hη' : 0 < Cm.eta n (gridTime s t K n (j + 1)) :=
      (hη n _ (altEnd_gridTime_nonneg (hs0 n) (hst n) _) (hv1' n j hj)).1
    have hBk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1 + 1) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη'.le) _)
    have h := gridDriftQNg s t K n j σ _ hL hW hExp hKL hKT hU (hS n) (fun w _ k σ' a => hKK n w k σ' a) (hm n) hlamn
      (hs0 n) (hst n) (ht1 n) (hK n) hj (by omega) hBk (hn j hj)
    exact h.mono fun ω hω _ a => hω a
  · exact Eventually.of_forall fun ω h => absurd h hj

end C1G

section C1bG

variable {d : ℕ} {sz : Sizes d}

/-- `kappaAltQNg` is nonnegative (as in `QBudgetA`). -/
private theorem altEnd_kappag_nonneg (k : ℕ) (Cv g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ) (i m : ℕ) :
    0 ≤ kappaAltQNg k Cv g W ε u i m := by
  unfold kappaAltQNg
  exact mul_nonneg (Real.rpow_nonneg hW _)
    (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

/-- The step error `stepErrNg` is nonnegative (the carrier form of the band step error, with `envConst` unfolded in `stepErrNg`; `0 < η_u`, `0 < η_v`). -/
private theorem altEnd_stepErrNg_nonneg (C : FlowFM sz) (n k : ℕ) {u v Δ Bk : ℝ} (hηu : 0 < C.eta n u)
    (hηv : 0 < C.eta n v) (hv1 : v < 1) (hΔ : 0 ≤ Δ) (hBk : 0 ≤ Bk) : 0 ≤ stepErrNg C n k u v Δ Bk := by
  have hv : 0 < 1 - v := by linarith
  have hηi : 0 ≤ (C.eta n v)⁻¹ := inv_nonneg.2 hηv.le
  have h1 : 0 ≤ 16 * ((k : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 * (1 + (C.eta n v)⁻¹) ^ (k + 4) *
      Δ ^ ((3 : ℝ) / 2) := by
    have := Real.rpow_nonneg hΔ ((3 : ℝ) / 2)
    positivity
  have h2 : 0 ≤ kStepC d (sz.L n) (sz.W n) k Bk * Δ ^ 2 := by
    unfold kStepC; positivity
  have h3 : 0 ≤ uStepC k Δ v := by
    unfold uStepC
    have hx : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ (inv_nonneg.2 hv.le)
    have hb : 1 + (k : ℝ) * (Δ * (1 - v)⁻¹) ≤ (1 + Δ * (1 - v)⁻¹) ^ k := by
      have := one_add_mul_le_pow (a := Δ * (1 - v)⁻¹) (by linarith : (-2 : ℝ) ≤ Δ * (1 - v)⁻¹) k
      simpa using this
    have hk : 0 ≤ (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 := by positivity
    nlinarith
  have h4 : 0 ≤ (C.eta n u)⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) + Bk := by
    have : 0 ≤ (C.eta n u)⁻¹ := inv_nonneg.2 hηu.le
    positivity
  unfold stepErrNg
  have := mul_nonneg h3 h4
  linarith

/-- **`assembledRHSAltQNg_qErr_le`** (band `assembledRHSAltQN_qErr_le`): the right side of `AssembledNg` at the target `m = K n` for the alternating chain
(`κ = kappaAltQNg`, `εK = epsAltQNg`, `c = cQVAltQNg`, `k = m + 2`, `u = gridTime`), with the remainder `stepErr := qErrQNg` (the `𝒬`-process remainder of `gridDriftQNg_envelope_ev`) and
an initial supremum `Xs ≤ X0`, is at most `assembledRHSAltQNg` (whose last term is the non-alternating `stepErrNg`) plus `N^{-D_t}`, once the weighted `qErrQNg` sum is at most `N^{-D_t}`
(`sum_weighted_qErrQNg_le` at `m ↦ m + 1`).  The five common terms are identical and `stepErrNg ≥ 0`. -/
theorem assembledRHSAltQNg_qErr_le {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (s v : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ) (Cv Λg KL C c ε : ℝ) (Γ Λ : ℕ → ℝ) (dd : ℕ → ℝ) (δ0 δD D'' D_Y τK εq Xs X0 D_t C₁ C₂ : ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n))
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hτK : 0 ≤ τK)
    (hX : Xs ≤ X0)
    (hsum : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        qErrQNg Cm.toFlowFM s v K n (m + 1) C₁ C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
          (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t)) :
    kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * Xs +
      epsAltQNg Cv ((sz.W n : ℕ) : ℝ) 0 (K n) * δ0 +
      gridStep s v K n * ∑ j ∈ Finset.range (K n),
        (kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) *
            dd j +
          epsAltQNg Cv ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * δD) +
      ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
        (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' (K n) a j : ℝ)) +
      ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
      ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        qErrQNg Cm.toFlowFM s v K n (m + 1) C₁ C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
          (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤
    assembledRHSAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ dd δ0 δD D'' D_Y τK εq X0 a +
      ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  have hKu : gridTime s v K n (K n) = v n := gridTime_last s v K n hK
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => altEnd_gridTime_lt_one hsv hK hv1 hi
  have hΔ := altEnd_gridStep_nonneg (s := s) (v := v) (K := K) hsv
  have hWn : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk := altEnd_kappag_nonneg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε hWn
    (gridTime s v K n) 0 (K n)
  have hX' : kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * Xs ≤
      kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 :=
    mul_le_mul_of_nonneg_left hX hk
  have hw : 0 ≤ (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) := by
    rw [hKu]
    have : 0 ≤ (1 - v n)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  have hS : 0 ≤ ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
      stepErrNg Cm.toFlowFM n (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg hw ?_
    have hj' := Finset.mem_range.1 hj
    have hη : 0 < Cm.eta n (gridTime s v K n (j + 1)) := NQGood1Gen_eta_pos hL n (hu1 (j + 1) hj')
    exact altEnd_stepErrNg_nonneg Cm.toFlowFM n _ (NQGood1Gen_eta_pos hL n (hu1 j hj'.le)) hη (hu1 (j + 1) hj') hΔ
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (inv_nonneg.2 hη.le) _))
  unfold assembledRHSAltQNg
  linarith

end C1bG

/-! ## 4g. The variance proxy after the spectral-time shift, and `SubGaussStopNg` -/

section C2G

variable {d : ℕ} {sz : Sizes d}

/-- **`hQ_altQNg`** (band `hQ_altQN`; RBM2D `hQ_alt`; the pattern of `hQ_nonAltNg`; fixed `n`): for `M ∈ GoodSetNg n u_j (m+2) Γ Λ Φc τ' D'` Hermitian and every `σ`, the proxy
`Δ · ((m+2) · qvFormQNg_{u_{j+1},u_p}(M)(a))` of the `j`-th propagated `𝒬`-increment towards `u_p` is at most `cQVAltQNg … D'' p a j`.  Proof: the bound on `STeeM` and the far-label decay of `(ℰ⊗ℰ)^M` in `GoodSetNg` at `u_j` are moved
to `u_{j+1}` by `norm_STeeMg_shiftNg_le`, `B_{u_j} ≤ B_{u_{j+1}}`, `η_{u_j}⁻¹ ≤ η_{u_{j+1}}⁻¹` (`NQGood1Gen_eta_anti`), `ℓ_{u_j} ≤ ℓ_{u_{j+1}}`, then `qvFormQNg_le_of_bounds` (`QProxy`) at
`m ↦ m + 1`, `v := u_{j+1}`, `w := u_p`, `D := D'' + 1`, `M_ee = Γ(ΓΛ)B_{u_{j+1}}^{2k}/η_{u_{j+1}} + W^{-(D''+1)}`.  `QProxyG_KerEK4` enters through `hKer` at the kernel coupling `gK` and the comparison of couplings
(`hcmp`, `hA`, `hεε`, `hAk`, `C4 ≤ Cv`); the two radii `ε₁ ≤ ε` of `qvFormQNg_le_of_bounds` are tied by `√A W^{ε₁} ≤ W^ε`.  The shift hypothesis is
`W^{-D'} + eeShiftErrNg(u_j, u_{j+1}) ≤ W^{-(D''+1)}` together with `2 ≤ W`. -/
theorem hQ_altQNg {m : ℕ} (hd : 3 ≤ d) (Λg KL C c : ℝ) (hΛg : 0 < Λg) (hKL : 0 < KL) (hC : 0 < C) (hc : 0 < c)
    {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) {gK : ℕ → ℝ} {A C4 Cv : ℝ}
    {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcmp : ∀ n', 0 ≤ gK n' * sz.lam n' ∧ gK n' ^ 2 ≤ sz.lam n' ^ 2 ∧ sz.lam n' ^ 2 ≤ A * gK n' ^ 2) (hA : 1 ≤ A)
    (hKer : QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) KL C4 n) (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : C4 ≤ Cv)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε ε₁ τ' C₀ D' D'' : ℝ}
    (hW : 2 ≤ ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hε₁0 : 0 < ε₁) (hε₁1 : ε₁ < 1) (hWε₁ : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁)
    (hεε : Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁)
    (hAk : A ^ (m + 1 + 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) (hC₀ : 0 ≤ C₀)
    (hD : ((m + 1 : ℕ) : ℝ) + 2 + qProxyCQ d (m + 1) Λg KL C c < D'' + 1)
    (hW₀ : qProxyW0 d (m + 1) Λg KL C c C₀ ε₁ (D'' + 1) ≤ ((sz.W n : ℕ) : ℝ))
    {ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ}
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    {σ : Fin (m + 1 + 1) → Bool} (Γ Λ Φc : ℕ → ℝ) (p : ℕ) (hp : p ≤ K n)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p)
    (hMee : Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        Cm.eta n (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrNg Cm n (m + 1 + 1)
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1))) :
    ∀ M, GoodSetNg Cm n (gridTime s v K n j) (m + 1 + 1) (Γ n) (Λ n) (Φc n) τ' D' M →
      M.IsHermitian → gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) *
        qvFormQNg Cm n ϑ (gridTime s v K n (j + 1)) (gridTime s v K n p) σ M a) ≤
        (cQVAltQNg Cm s v K n m Cv Λg KL C c ε Γ Λ D'' p a j : ℝ) := by
  intro M hM hMh
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := hM
  have hΔ : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hu0 : 0 ≤ gridTime s v K n j := altEnd_gridTime_nonneg hs0 hsv j
  have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) :=
    ST_gridTime_mono s v K n hsv (Nat.le_succ j)
  have hj1p : gridTime s v K n (j + 1) ≤ gridTime s v K n p :=
    ST_gridTime_mono s v K n hsv (by omega)
  have hK : K n ≠ 0 := by omega
  have hpv : gridTime s v K n p ≤ v n := altEnd_gridTime_le hsv hK hp
  have hj1v : gridTime s v K n (j + 1) ≤ v n := hj1p.trans hpv
  have hs1 : s n ≤ gridTime s v K n (j + 1) := by
    have h := ST_gridTime_mono s v K n hsv (Nat.zero_le (j + 1))
    rwa [ST_gridTime_zero] at h
  have hwin : (((sz.W n : ℕ) : ℝ))⁻¹ ≤
      (1 - gridTime s v K n p) / (1 - gridTime s v K n (j + 1)) := by
    refine hWt.trans ?_
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have hL3 := sz.three_le_L n
  have hLpos : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < sz.L n)
  have hgL : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have hu'1 : gridTime s v K n (j + 1) < 1 := by linarith
  have hu1 : gridTime s v K n j < 1 := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWτ : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.rpow_nonneg hW0.le _
  have hWD'' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := Real.rpow_nonneg hW0.le _
  have hWD' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hηu := NQGood1Gen_eta_pos hL n hu1
  have hηu' := NQGood1Gen_eta_pos hL n hu'1
  have hηle : Cm.eta n (gridTime s v K n (j + 1)) ≤ Cm.eta n (gridTime s v K n j) :=
    NQGood1Gen_eta_anti hL n hjj
  have hBu : 0 < sz.Bctl n (gridTime s v K n j) := STBctl_pos sz n hu1
  have hBu' : 0 < sz.Bctl n (gridTime s v K n (j + 1)) := STBctl_pos sz n hu'1
  have hBle : sz.Bctl n (gridTime s v K n j) ≤ sz.Bctl n (gridTime s v K n (j + 1)) :=
    STBctl_mono sz n hjj hu'1
  have hmono : ∀ G : ℝ, 0 ≤ G →
      G * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * (m + 1 + 1)) / Cm.eta n (gridTime s v K n j)) ≤
      G * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        Cm.eta n (gridTime s v K n (j + 1))) := fun G hG0 =>
    mul_le_mul_of_nonneg_left (div_le_div₀ (pow_nonneg hBu'.le _)
      (pow_le_pow_left₀ hBu.le hBle _) hηu' hηle) hG0
  have hLK' : ellT (sz.L n) (sz.lam n) (gridTime s v K n j) ≤
      ellT (sz.L n) (sz.lam n) (gridTime s v K n (j + 1)) := nqGood1_ellT_mono _ _ hjj hu'1
  have hshift := fun b b' => norm_STeeMg_shiftNg_le hL hm hS hMh hjj hu'1 σ b b'
  have htri : ∀ b b' : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b'‖ ≤
        ‖STeeMg Cm n (gridTime s v K n j) M σ b b'‖ +
          eeShiftErrNg Cm n (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1)) := by
    intro b b'
    have h3 : ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b'‖ ≤
        ‖STeeMg Cm n (gridTime s v K n j) M σ b b'‖ +
          ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b' -
            STeeMg Cm n (gridTime s v K n j) M σ b b'‖ := by
      have := norm_add_le (STeeMg Cm n (gridTime s v K n j) M σ b b')
        (STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b' -
          STeeMg Cm n (gridTime s v K n j) M σ b b')
      rwa [add_sub_cancel] at this
    linarith only [h3, hshift b b']
  have hD4' : ∀ b b', ‖STeeMg Cm n (gridTime s v K n j) M σ b b'‖ ≤
      Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * (m + 1 + 1)) /
        Cm.eta n (gridTime s v K n j)) := fun b b' => hD4 σ b b'
    -- `G ≥ 0` is forced by the bound on `STeeM` (a norm is nonnegative and the quotient is positive)
  have hGnn : 0 ≤ Γ n * (Γ n * Λ n) := by
    have h0 := (norm_nonneg _).trans (hD4' (fun _ => 0) (fun _ => 0))
    have hq : 0 < (sz.Bctl n (gridTime s v K n j)) ^ (2 * (m + 1 + 1)) /
        Cm.eta n (gridTime s v K n j) := div_pos (pow_pos hBu _) hηu
    exact nonneg_of_mul_nonneg_left h0 hq
  have hT : ∀ b b' : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b'‖ ≤
        Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
          Cm.eta n (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    intro b b'
    have h1 := hD4' b b'
    have h2 := htri b b'
    have h3 := hmono _ hGnn
    linarith only [h1, h2, h3, hδ, hWD']
  have hTfar : ∀ b b' : Fin (m + 1 + 1) → Zd d (sz.L n),
      ellT (sz.L n) (sz.lam n) (gridTime s v K n (j + 1)) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
          (STdiamInf (Fin.append b b') : ℝ) →
        ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    intro b b' hfar
    have hfar' : ellT (sz.L n) (sz.lam n) (gridTime s v K n j) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
        (STdiamInf (Fin.append b b') : ℝ) := (mul_le_mul_of_nonneg_right hLK' hWτ).trans hfar
    have h1 := hVb σ b b' hfar'
    have h2 := htri b b'
    linarith only [h1, h2, hδ]
  have key := qvFormQNg_le_of_bounds (m := m + 1) hd (by omega) Λg KL C c hΛg hKL hC hc Cm hcmp hA hg hgΛ hKer hRow hCv
    hW1 hε0 hε1 hWε hlog hε₁0 hε₁1 hWε₁ hεε hLK hdW hAk hC₀ hD hW₀ hϑ (hu0.trans hjj) hj1p (hpv.trans hwL) hwin M
    hMee hT hTfar a
  have hCn : 0 < qProxyCn d (m + 1) Λg KL C c := qProxyCn_pos hd (m + 1) hΛg hKL hC hc
  have hCQ : qProxyCQ d (m + 1) Λg KL C c = 2 * qProxyCn d (m + 1) Λg KL C c + 2 := rfl
  have hε₁ε : ε₁ ≤ ε := by
    have h1 : ((sz.W n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.W n : ℕ) : ℝ) ^ ε := by
      refine le_trans ?_ hεε
      have hs : 1 ≤ Real.sqrt A := by
        rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hA
      exact le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _) hs
    exact (Real.rpow_le_rpow_left_iff hW1).1 h1
  have hq : qvFormQNg Cm n ϑ (gridTime s v K n (j + 1)) (gridTime s v K n p) σ M a ≤
      qvBdAltQNg Cm n m Cv Λg KL C c ε (Γ n) (Λ n) D'' (gridTime s v K n (j + 1))
        (gridTime s v K n p) := by
    refine key.trans ?_
    unfold qvBdAltQNg
    obtain ⟨hPz, h2x⟩ := altEnd_shift_rpow (D := D'') (ε := ε) hW hCn hε1
    have hx0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1) + qProxyCQ d (m + 1) Λg KL C c) :=
      Real.rpow_nonneg hW0.le _
    have hP1 : ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε₁) ≤
        ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) :=
      Real.rpow_le_rpow_of_exponent_le hW1.le (mul_le_mul_of_nonneg_left hε₁ε (by positivity))
    have hGz : 0 ≤ Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        Cm.eta n (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) :=
      add_nonneg (mul_nonneg hGnn (div_nonneg (pow_nonneg hBu'.le _) hηu'.le)) hWD''
    have hmono2 : ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε₁) *
          (Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
            Cm.eta n (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1))) ≤
        ((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d (m + 1) Λg KL C c * ε) *
          (Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
            Cm.eta n (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1))) :=
      mul_le_mul_of_nonneg_right hP1 hGz
    rw [hCQ] at hx0 ⊢
    refine le_trans ?_ (altEnd_qv_arith (by positivity) (by positivity) (by positivity) hPz h2x hx0)
    gcongr
  refine le_trans ?_ (Real.le_coe_toNNReal _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)) hΔ

/-- **`subGaussStop_altQNg`** (band `subGaussStop_altQN`; RBM2D `subGaussStop_alt`; pattern `subGaussStop_linNg`): the `azumaSubGQ_gridExitNg` (`QProxy`) at the alternating exit family of
`altExitTauNg` (the family `GoodSetNg ∩ GoodLinNg ∩ altYSetNg`, measurable by the ingredients of `altExitMeasNg`) and the `hQ` premise from `hQ_altQNg` on the `GoodSetNg` component:
sub-Gaussianity of the stopped propagated first-chaos part `zVecQNg` (mollifier `QopAlgebra_mollifier … (m+1)`, constants `C = (1 + 40 d(m+1)) 6^{d(m+1)}`, `c = 1/2`) with the explicit
proxy `cQVAltQNg`.  Hypotheses as `hQ_altQNg`, plus `AzumaSubGNg`, `QVPropagatedNg`, the loop and walk forms of the carrier. -/
theorem subGaussStop_altQNg {m : ℕ} {Cm : Step2Mat sz} [IsProbabilityMeasure Cm.Pp] {g lam' s v : ℕ → ℝ} {K : ℕ → ℕ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hd : 3 ≤ d) (Λg KL : ℝ)
    (hΛg : 0 < Λg) (hKL : 0 < KL) {E : ℕ → ℝ} (hAz : AzumaSubGNg Cm g s v K) (hL : StepDecompGen_LoopForm Cm E)
    (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hQV : QVPropagatedNg Cm g) {gK : ℕ → ℝ} {A C4 Cv : ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ) (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcmp : ∀ n', 0 ≤ gK n' * sz.lam n' ∧ gK n' ^ 2 ≤ sz.lam n' ^ 2 ∧ sz.lam n' ^ 2 ≤ A * gK n' ^ 2) (hA : 1 ≤ A)
    (hKer : QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) KL C4 n) (hRow : GridRepTailGen_Ker Cm.toFlowFM n) (hCv : C4 ≤ Cv)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n))
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε ε₁ τ' C₀ D' D'' : ℝ}
    (hW : 2 ≤ ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hε₁0 : 0 < ε₁) (hε₁1 : ε₁ < 1) (hWε₁ : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁)
    (hεε : Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε₁)
    (hAk : A ^ (m + 1 + 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) (hC₀ : 0 ≤ C₀)
    (hD : ((m + 1 : ℕ) : ℝ) + 2 + qProxyCQ d (m + 1) Λg KL
        ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2) < D'' + 1)
    (hW₀ : qProxyW0 d (m + 1) Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
      C₀ ε₁ (D'' + 1) ≤ ((sz.W n : ℕ) : ℝ))
    {σ : Fin (m + 1 + 1) → Bool} (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (p : ℕ) (hp : p ≤ K n)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) (j : ℕ) (hj : j < p)
    (hMee : Γ n * (Γ n * Λ n) * ((sz.Bctl n (gridTime s v K n (j + 1))) ^ (2 * (m + 1 + 1)) /
        Cm.eta n (gridTime s v K n (j + 1))) + ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ C₀)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrNg Cm n (m + 1 + 1)
      (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1))) :
    SubGaussStopNg Cm σ (gridTime s v K n)
      (altExitTauNg Cm s v K (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n)
      (fun j ω => zVecQNg Cm s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω) p a j
      (cQVAltQNg Cm s v K n m Cv Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
        ε Γ Λ D'' p a j) := by
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  have hϑ := QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hg
  exact azumaSubGQ_gridExitNg hAz hL hW' hQV hs0 hsv hv1 n (m + 1) hRow (by omega)
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ
    (fun j => {H | GoodSetNg Cm n (gridTime s v K n j) (m + 1 + 1) (Γ n) (Λ n) (Φc n) τ' D' H} ∩
      GoodLinNg Cm n (gridTime s v K n j) (m + 1 + 1) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetNg Cm n (gridTime s v K n j) (m + 1) (Yl n))
    (fun j => ((measurableGoodSetNg hL n _ _ _ _ _ _ _).inter (measurableGoodLinNg hL n _ _ _ _ _ _)).inter
      (measurableAltYSetNg hL n _ _ _))
    p hp a j hj _
    (fun M hM hMh => hQ_altQNg hd Λg KL _ (1 / 2) hΛg hKL hC0 (by norm_num) Cm hL hm hS hcmp hA hKer hRow hCv (hs0 n) (hsv n)
      (hv1 n) hwL hWt hg hgΛ hW hε0 hε1 hWε hlog hε₁0 hε₁1 hWε₁ hεε hLK hdW hAk hC₀ hD hW₀ hϑ Γ Λ Φc p hp a j hj hMee hδ M
      hM.1.1 hMh)

end C2G

/-! ## 5g. The kernel field on the grid over a carrier -/

section C3G

variable {d : ℕ} {sz : Sizes d}

/-- **`alt_hkerGridQNg`** (band `alt_hkerGridQN`; the field `hker` of `GridAssemblyHypNg`): `alt_hkerQNg` (`QDriftA`) at the grid `u = gridTime s v K n`, `Kg = K n`
(`0 ≤ u_i` from `s n ≥ 0`, monotone `ST_gridTime_mono`, `u_{K n} = v n` `gridTime_last`), with the regime premises explicit (case (i) only here: `v n ≤ 1 - g²/L²`,
`W⁻¹ ≤ (1-v_n)/(1-s_n)`).  `QProxyG_KerEK4` at the kernel coupling `gK`, the comparison of couplings (`hcmp`, `hA`, `hdW`, `hAk`, `C4 ≤ Cv`); `Cls = altClsQN … ε' Dc`,
`κ = kappaAltQNg`, `εK = epsAltQNg` (tensors of `m + 2` indices). -/
theorem alt_hkerGridQNg {m : ℕ} (hd : 3 ≤ d) (Cm : Step2Mat sz) {gK : ℕ → ℝ} {A C4 Cv KL : ℝ}
    (hcmp : ∀ n', 0 ≤ gK n' * sz.lam n' ∧ gK n' ^ 2 ≤ sz.lam n' ^ 2 ∧ sz.lam n' ^ 2 ≤ A * gK n' ^ 2) (hA : 1 ≤ A)
    (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hKer : QProxyG_KerEK4 Cm.toFlowFM gK (m + 1 + 1) KL C4 n) (hCv : C4 ≤ Cv)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hK : K n ≠ 0)
    {ε ε' Dc : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * Real.sqrt A * ((sz.W n : ℕ) : ℝ) ^ ε' ≤ ((sz.W n : ℕ) : ℝ) ^ ε)
    (hAk : A ^ (m + 1 + 1) ≤ ((sz.W n : ℕ) : ℝ) ^ ((Cv - C4) * ε)) (hDc : 1 < Dc)
    (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (σ : Fin (m + 1 + 1) → Bool) :
    ∀ i m', i ≤ m' → m' ≤ K n → ∀ (X : (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v K n) i δ X →
      ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖Step2Gen_UN Cm.toFlowFM n σ (gridTime s v K n i) (gridTime s v K n m') X a‖ ≤
          kappaAltQNg (m + 1 + 1) Cv (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) i m' * M +
            epsAltQNg Cv ((sz.W n : ℕ) : ℝ) i m' * δ := by
  have hKu : gridTime s v K n (K n) = v n := gridTime_last s v K n hK
  have h0u : gridTime s v K n 0 = s n := ST_gridTime_zero s v K n
  exact alt_hkerQNg Cm.toFlowFM (by omega) hcmp hA hKer hCv hW hLK hε0 hε1 hWε hlog hdW hAk hDc
    (Kg := K n) (u := gridTime s v K n) (fun i _ => altEnd_gridTime_nonneg hs0 hsv i)
    (fun i m' him _ => ST_gridTime_mono s v K n hsv him) (by rw [hKu]; exact hwL)
    (by rw [hKu, h0u]; exact hWt) σ

end C3G

/-! ## 6g. The drift and class fields on the alternating exit family over a carrier -/

section C4G

variable {d : ℕ} {sz : Sizes d}

/-- **`alt_hdriftGridQNg`** (band `alt_hdriftGridQN`; the field `hdrift` of `GridAssemblyHypNg`): `alt_hdriftLinQNg` with `τ := altExitTauNg`; the premise `hτG` is components 1 and 2 of
`mem_of_lt_altExitTauNg` and the premise `hY` is component 3 at the level `Yl n ≤ ν X` (`altYSetNg` at length `k - 1 = m + 1`; used with `Yl n = N^{ε₁} X n`).  The spectral
levels are the fields of `B45Gen_Facts` at `n` (`κm`, `K₆`, `hward`, `hker`, `hrow`, `hcol`), `Γ = κm⁻¹`. -/
theorem alt_hdriftGridQNg {E : ℕ → ℝ} (hd : 3 ≤ d) (m : ℕ) (Λg KL : ℝ) (hΛg : 0 < Λg) (hKL : 0 < KL)
    (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {κm K₆ : ℝ} (hκm : 0 < κm) (hmn : κm ≤ (Cm.m n).im)
    (hm : ‖Cm.m n‖ ≤ 1) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (σ : Fin (m + 1 + 1) → Bool) (s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ)
    {τ' ε' D' ν X τN : ℝ} (hlam : 0 < sz.lam n) (hlamΛ : sz.lam n ≤ Λg) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n)
    (hv1 : v n < 1) (hNv : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n)
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hτ' : 0 ≤ τ') (hε : 0 < ε') (hε1 : ε' < 1) (hD : 1 < D')
    (h4 : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε') (hLW : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hν : 1 ≤ ν) (hX : 1 ≤ X) (hνt : (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹)
    (hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ *
        ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
    (hYl : Yl n ≤ ν * X) (hσ : σ (Fin.last (m + 1)) = !σ 0) :
    ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n →
      j < altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
      ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖dGridQNg Cm s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω b‖ ≤
          dDriftAltLinQNg Cm n (gridTime s v Kg n j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
            (qProxyCn d (m + 1) Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2))
            ε' D' τN X := by
  intro ω j hjK hjτ b
  have hKne : Kg n ≠ 0 := by omega
  have hu1 : gridTime s v Kg n j < 1 := altEnd_gridTime_lt_one hsv hKne hv1 hjK.le
  refine alt_hdriftLinQNg hd m Λg KL hΛg hKL Cm hL n hκm hmn hm hward hker hK₆ hrow hcol σ s v Kg Γ Λ Φc Φ₁ Φ₂ Φ₃
    (altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n) hlam hlamΛ hs0 hsv hv1 hNv hW hτ' hε hε1 hD h4 hLW hdW hν hX hνt
    hνN hFv hMΛ hσ (fun ω' j' hj' => (mem_of_lt_altExitTauNg hj').1) (fun ω' j' hj' σ' a' => ?_) ω j hjK hjτ b
  have hjK' : j' < Kg n := hj'.trans_le (gridExitTauNg_le ω')
  have hu1' : gridTime s v Kg n j' < 1 := altEnd_gridTime_lt_one hsv hKne hv1 hjK'.le
  have hB' : 0 ≤ sz.Bctl n (gridTime s v Kg n j') ^ (m + 1) := (pow_pos (STBctl_pos sz n hu1') _).le
  have h : ‖STLKMg Cm n (gridTime s v Kg n j') (Cm.Hpath s v Kg n j' ω') σ' a'‖ ≤
      Yl n * sz.Bctl n (gridTime s v Kg n j') ^ (m + 1) := (mem_of_lt_altExitTauNg hj').2 σ' a'
  exact h.trans (mul_le_mul_of_nonneg_right hYl hB')

/-- **`alt_hA0clsGridQNg`** (band `alt_hA0clsGridQN`; the field `hA0cls` of `GridAssemblyHypNg`): `alt_hA0clsQNg` (`QDriftA`, tensors of `m + 2` indices) with
`τ := altExitTauNg`: `hτG` is component 1 of `mem_of_lt_altExitTauNg` (`k = m + 1 + 1`, crude level `Φc`), and the crude sup `‖A_0‖ ≤ W^{C₀}` is an explicit premise (a bound on
`‖(𝓛-𝒦)^{(m+2)}(H_0)‖` at length `k`, which no clause of `GoodSetNg` gives).  The class exponent is `ε'` (`d W^{τ'} ≤ W^{ε'}`), the radius level `Dc ≤ D' - 1`. -/
theorem alt_hA0clsGridQNg (hd : 3 ≤ d) (m : ℕ) (K C₀ ε' D' : ℝ) (hε' : 0 < ε') (Cm : Step2Mat sz)
    {n : ℕ} (σ : Fin (m + 1 + 1) → Bool) (s v : ℕ → ℝ) (Kg : ℕ → ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' Dc : ℝ)
    (hW : QDriftA_W0 d (m + 1) K ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2) C₀ ε' D' ≤
      ((sz.W n : ℕ) : ℝ))
    (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
    (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
    (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
    (hlam : 0 < sz.lam n) (hs0 : 0 ≤ s n) (hs1 : s n < 1)
    (hcrude : ∀ ω, 0 < altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
      ‖AvecNg Cm s v Kg n 0 σ ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    ∀ ω, 0 < altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) 0
        (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
        (aTrueQNg Cm s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω) :=
  alt_hA0clsQNg Cm hd (m + 1) K _ (1 / 2) C₀ ε' D' (by positivity) (by norm_num) hε' σ s v Kg Γ Λ Φc τ' Dc
    (altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n)
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hW hLK hdW hDD hlam hs0 hs1
    (QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hlam)
    (fun ω' j' hj' => (mem_of_lt_altExitTauNg hj').1.1) hcrude

/-- **`alt_hDclsGridQNg`** (band `alt_hDclsGridQN`; the field `hDcls` of `GridAssemblyHypNg`): `alt_hDclsQNg` (`QDriftB`, tensors of `m + 2` indices, the existential `W₀` of the
generic statement) with `τ := altExitTauNg`: `hτG` is component 1 of `mem_of_lt_altExitTauNg`; the crude sups `hAcr` (`‖(𝓛-𝒦)^{(m+2)}(H_j)‖ ≤ W^{C₀}`) and `hDcr`
(`‖driftTensorNg‖ ≤ W^{C₀}`) are explicit premises (the second is derived from the exit family by `altEnd_driftSupg`).  The kernel enters through `ZeroModeGen_KerSums` and
`Step5KerGen_ThDecay` at `gK` with the comparison of couplings (`C₆`, `A` before the carrier). -/
theorem alt_hDclsGridQNg :
    ∀ (d m : ℕ) (Λg K C₀ ε' D' C₆ A : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' → 0 ≤ C₆ → 1 ≤ A →
      ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (Cm : Step2Mat sz) (gK : ℕ → ℝ) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool)
        (s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' Dc : ℝ),
        ZeroModeGen_KerSums Cm.toFlowFM n → Step5KerGen_ThDecay Cm.toFlowFM gK Λg C₆ →
        (∀ m', 0 ≤ gK m' * sz.lam m' ∧ gK m' ^ 2 ≤ sz.lam m' ^ 2 ∧ sz.lam m' ^ 2 ≤ A * gK m' ^ 2) →
        0 < gK n → gK n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
        ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        0 ≤ s n → s n ≤ v n → v n < 1 → (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
        4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n →
          j < altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
          ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
            STLKMg Cm n (gridTime s v Kg n j) (Cm.Hpath s v Kg n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) →
        (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n →
          j < altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
          ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
            driftTensorNg Cm n (gridTime s v Kg n j) (Cm.Hpath s v Kg n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) →
        ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n →
          j < altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω →
          altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1)
            (4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
            (dGridQNg Cm s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω) := by
  intro d m Λg K C₀ ε' D' C₆ A hd hΛg hε' hC₆ hA
  obtain ⟨W₀, hW₀, H⟩ := alt_hDclsQNg d (m + 1) Λg K C₀ ε' D' C₆ A hd hΛg hε' hC₆ hA
  refine ⟨W₀, hW₀, ?_⟩
  intro sz Cm gK n σ s v Kg Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' Dc hKS hTh hcmp hg hgΛ hW hLK hs0 hsv hv1 hKv hdW hDD hAcr hDcr
  exact H sz Cm gK n σ s v Kg Γ Λ Φc τ' Dc (altExitTauNg Cm s v Kg (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n)
    hKS hTh hcmp hg hgΛ hW hLK hs0 hsv hv1 hKv hdW hDD (fun ω' j' hj' => (mem_of_lt_altExitTauNg hj').1.1) hAcr hDcr

/-- **The crude sup of the drift tensor from the exit family** (deterministic; band `altEnd_driftSup`): `GoodLinNg` (component 2) gives
`‖driftTensorNg‖ ≤ dDriftLinNg` (`driftTensorNg_norm_le_of_goodLin`), so a bound `dDriftLinNg ≤ W^{C₀}` gives the `hDcr` premise of `alt_hDclsGridQNg`. -/
theorem altEnd_driftSupg (Cm : Step2Mat sz) (n : ℕ) {u Γ Φ₁ Φ₂ Φ₃ C₀ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H ∈ GoodLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃)
    (hW : dDriftLinNg Cm n u k Γ Φ₁ Φ₂ Φ₃ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (σ : Fin k → Bool) :
    ‖fun b : Fin k → Zd d (sz.L n) => driftTensorNg Cm n u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hWpos.le C₀)).2 fun b =>
    (driftTensorNg_norm_le_of_goodLin hk hH σ b).trans hW

end C4G

/-! ## 7g. The identity, measurability, terminal value, de-`𝒬` over a carrier -/

section C5G

variable {d : ℕ} {sz : Sizes d}

/-- **`altEnd_hexpg`** (band `altEnd_hexp`; RBM2D `altEnd_identity`; literally the field `hexp` of `GridAssemblyHypNg` at `A := aFrozQNg`, `A0 := aTrueQNg … 0`, `Dr := dGridQNg`,
`Z := zVecQNg`, `Y := yVecQNg`, `R := rGridQNg`): for every stopping index `τ` and target `m' ≤ K n`, a.e., `A^{Q,frz}_{m'} = 𝒰_{u_0,u_{m'}} A^Q_0 +
Σ_{j < m' ∧ τ} 𝒰_{u_{j+1},u_{m'}}(Δ dGridQNg_j + zVecQNg_j + yVecQNg_j + rGridQNg_j)` (`stoppedDuhamelQNg` with `martIncQNg_ae_eq` at every `j < K n`; the semigroup law
`Step2Gen_USemigroup` and the link `HierDriftGen_KLink` replace `|E n| < 2`). -/
theorem altEnd_hexpg {m : ℕ} {E lam' : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s v : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (hKL : HierDriftGen_KLink Cm n) (hS : Step2Gen_USemigroup Cm.toFlowFM n)
    (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool)
    (τ : PathΩ sz → ℕ) :
    ∀ m' ≤ K n, ∀ᵐ ω ∂(Cm.Pp),
      aFrozQNg Cm s v K n ϑ σ τ m' ω =
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s v K n 0) (gridTime s v K n m')
            (aTrueQNg Cm s v K n ϑ σ 0 ω) +
          ∑ j ∈ Finset.range (min m' (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s v K n (j + 1)) (gridTime s v K n m')
              ((gridStep s v K n : ℂ) • dGridQNg Cm s v K n ϑ σ j ω + zVecQNg Cm s v K n j ϑ σ ω +
                yVecQNg Cm s v K n j ϑ σ ω + rGridQNg Cm s v K n ϑ σ j ω) := by
  intro m' hm'
  have hmart : ∀ᵐ ω ∂(Cm.Pp), ∀ j, j < K n →
      martIncQNg Cm s v K n ϑ σ j ω = zVecQNg Cm s v K n j ϑ σ ω + yVecQNg Cm s v K n j ϑ σ ω := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hj : j < K n
    · have h := ae_all_iff.2 fun a => martIncQNg_ae_eq hL hW s v K n j hKL hs0 hsv hv1 hK hj ϑ σ a
      exact h.mono fun ω hω _ => funext hω
    · exact Eventually.of_forall fun ω h => absurd h hj
  filter_upwards [hmart] with ω hω
  rw [stoppedDuhamelQNg Cm s v K n ϑ σ τ m' ω hS hs0 hsv hv1 hK hm']
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < K n := (Finset.mem_range.1 hj).trans_le ((min_le_left _ _).trans hm')
  rw [hω j hj', ← add_assoc ((gridStep s v K n : ℂ) • dGridQNg Cm s v K n ϑ σ j ω)]

/-- **`altEnd_stronglyMeasurable_zVecQNg`** (band `altEnd_stronglyMeasurable_zVecQN`): `zVecQNg … j` is `filt sz (j + 1)`-strongly measurable
(`GridAssemblyGen_stronglyMeasurable_ZvecNg` composed with the continuous linear `STQop ϑ u_{j+1}` on the finite-dimensional space of tensors). -/
theorem altEnd_stronglyMeasurable_zVecQNg {m : ℕ} {E lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s v : ℕ → ℝ)
    (K : ℕ → ℕ) (n j : ℕ)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => zVecQNg Cm s v K n j ϑ σ ω) := by
  have hZ := GridAssemblyGen_stronglyMeasurable_ZvecNg hL hW s v K n j σ
  have hcont : Continuous (STQop (d := d) ϑ (gridTime s v K n (j + 1)) :
      ((Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) := by
    refine continuous_pi fun a => ?_
    unfold STQop STPsum
    exact (continuous_apply a).sub ((continuous_finsetSum _ fun b _ => continuous_apply b).mul
      continuous_const)
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.comp _ _ _ (filt sz (j + 1)) _ _ _ _ hcont.measurable hZ.measurable

/-- **`altEnd_aFroz_eq_aTrueg`** (band `altEnd_aFroz_eq_aTrue`): on `{K n ≤ τ ω}` the stopped `𝒬`-process (`aFrozQN`) at the last grid index is the true one
(`min (K n) (τ ω) = K n`, `𝒰_{u,u} = id`: `Step2Gen_UN_self` under the semigroup law). -/
theorem altEnd_aFroz_eq_aTrueg {m : ℕ} (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hS : Step2Gen_USemigroup Cm.toFlowFM n) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool)
    (τ : PathΩ sz → ℕ) (ω : PathΩ sz) (hτ : K n ≤ τ ω) :
    aFrozQNg Cm s v K n ϑ σ τ (K n) ω = aTrueQNg Cm s v K n ϑ σ (K n) ω := by
  unfold aFrozQNg
  rw [min_eq_left hτ]
  exact Step2Gen_UN_self Cm.toFlowFM n hS σ (altEnd_gridTime_nonneg hs0 hsv _)
    (altEnd_gridTime_lt_one hsv hK hv1 le_rfl) _

/-- **`altEnd_unQg`** (band `altEnd_unQ`; de-`𝒬` at the end, per matrix; RBM2D `altEnd_unQ`): for alternating `σ`, under the hypotheses of `altB45Ng_levelM` (`GoodSetNg` at a free
crude level gives Hermitian and the decay clause; `hY` the length-`m + 1` level at `u`; the mollifier `ϑ` with `STMollifierProps`),
`‖(𝓛-𝒦)_{u,σ}(H)_a‖ ≤ ‖𝒬_u(𝓛-𝒦)_{u,σ}(H)_a‖ + N^{τ_N} B_u^{m+2} X` (`STQop` unfolded, the first conjunct of `altB45Ng_levelM`, `norm_add_le`).  It is applied at `u = v_n`,
`H = H_{K n}` (the `altYSetNg` component and the decay clause at `j = K n`, `u_{K n} = v_n`).  The spectral levels are the fields of `B45Gen_Facts` (`κm`, `K₆`, `hward`, `hker`, `hrow`, `hcol`),
`Γ = κm⁻¹`. -/
theorem altEnd_unQg {E : ℕ → ℝ} (hd : 3 ≤ d) (m : ℕ) (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (n : ℕ)
    {κm K₆ : ℝ} (hκm : 0 < κm) (hmn : κm ≤ (Cm.m n).im) (hm : ‖Cm.m n‖ ≤ 1)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {u Γc Λc Φc τ' D' ν X τN C c : ℝ}
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hlam : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hτ' : 0 ≤ τ')
    (hν : 1 ≤ ν) (hX : 1 ≤ X) (hνt : (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν)
    (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹)
    (hC : 0 < C) (hc : 0 < c)
    (hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * κm⁻¹ * C * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hG : GoodSetNg Cm n u (m + 1 + 1) Γc Λc Φc τ' D' H)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKMg Cm n u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖STLKMg Cm n u H σ a‖ ≤
      ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) a‖ +
        ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hωf : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW.le hτ'
  have hHerm : H.IsHermitian := hG.1
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
        ‖STLKMg Cm n u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := fun σ' a' hfar =>
    goodSetNg_LKM_far d sz Cm n u (m + 1 + 1) Γc Λc Φc τ' D' H hG (m + 1) (by omega) (by omega) σ' a' hfar
  have hexp : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine (hϑ.2.1 u hu0 hu1 a).trans ?_
    have hl : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos (by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hex : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ)) / ellT (sz.L n) (sz.lam n) u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hc.le hS]) hl.le
    have hC0 : 0 ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) := by positivity
    calc _ ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hex hC0
      _ = _ := by rw [mul_one]
  have hB45 := altB45Ng_levelM (by omega) Cm hL n hκm hmn (NQGood1Gen_im_le_one hm) (NQGood1Gen_eta_eq hL n) hward hker hK₆
    hrow hcol hu0 hu1 hlam hNu hHerm (m := m) (Γ := κm⁻¹) (ν := ν) (X := X) (ωf := ((sz.W n : ℕ) : ℝ) ^ τ')
    (Fv := ((sz.W n : ℕ) : ℝ) ^ (-D')) (Λ := C) (τ := τN) rfl hν hX hωf hνt hνN hFv
    (Real.rpow_nonneg hWpos.le _) hC.le hMΛ hY hF ϑ hexp (fun a => hϑ.2.2.2 u hu0 hu1 a) σ hσ a
  have e : STLKMg Cm n u H σ a =
      STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) a +
        STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) (a 0) *
          ϑ u a := by
    unfold STQop; ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hB45.1)

end C5G

end RBM.Ind

end
