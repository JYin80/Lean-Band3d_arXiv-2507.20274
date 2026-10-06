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
# S3-18a1 (ticket T2294): vocabulary, the `hY` event at length `n_ - 1`, and the compositions C1-C5

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem:STOeq_Qt`
`3_5:1362-1378`, the alternating case `3_5:1676-1714` (`(y27kasdfg)`, `(A4)`, `(A5)`
`3_5:1692-1706`), `(normQA)` `3_5:1284-1289`.

* §0 vocabulary `altYSetN`, `altExitTauN` (check file `docs/tickets/checks/T2294-check.lean` §2,
  verbatim);
* §1 `measurableAltYSetN`, `mem_of_lt_altExitTauN`, `altExitMeasN`;
* §2 `altYGridN` (pin `T2294_altYGridN`): the `hY` event at length `l` on the grid at the level
  `N^ε X`;
* §3 C1 `gridDriftQN_envelope`, `assembledRHSAltQN_qErr_le`;
* §4 C2 `hQ_altQN`, `subGaussStop_altQN`;
* §5 C3 `alt_hkerGridQN`;
* §6 C4 `alt_hdriftGridQN`, `alt_hA0clsGridQN`, `alt_hDclsGridQN`, and the two crude-sup derivations
  `altEnd_crudeSup`, `altEnd_driftSup`;
* §7 C5 `altEnd_hexp`, `altEnd_stronglyMeasurable_zVecQN`, `altEnd_aFroz_eq_aTrue`, `altEnd_unQ`,
  `altEnd_yMomentsMax`;
* §8 compiled nonempty instances (namespace `RBM.Ind.QEndAInst`), with the fixed-`n` shift estimate
  `altEnd_shift_fixed` (copy of the body of `nqEnd_ev_hδ`).

Unpinned helpers are `private` or prefixed `altEnd_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 0. Vocabulary (copied verbatim from the check file §2) -/

/-- **The `hY` set at length `l`** (supervisor 1102 O1): the fine matrices whose `(𝓛-𝒦)^{(l)}` loops are at most
`Y · B_u^l` at every sign vector and label (the `hY` premise of `altB45N_levelM`, `alt_hdriftLinQN` at `ν X := Y`). -/
def altYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | ∀ (σ' : Fin l → Bool) (a' : Fin l → Zd d (sz.L n)),
    ‖sz.STLKM n E u H σ' a'‖ ≤ Y * sz.Bctl n u ^ l}

/-- **The alternating exit time**: `nqLinExitTauN` (`NQLin.lean:716`) with the `hY` set at length `k - 1` added
(`GoodSetN` at the crude level `Φc`, `GoodLinN` at the linear levels, `altYSetN` at the level `Yl`). -/
noncomputable def altExitTauN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetN sz n (E n) (gridTime s v K n j) (k - 1) (Yl n))

/-! ## 1. Targets 1: measurability and the exit family -/

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

/-- **Target `measurableAltYSetN`**: `altYSetN` is a measurable set of matrices (a finite intersection over the
labels of sublevel sets of the measurable norms of the loop observables). -/
theorem measurableAltYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) :
    MeasurableSet (altYSetN sz n E u l Y) := by
  unfold altYSetN
  refine altEnd_measurableSet_forall fun σ' => altEnd_measurableSet_forall fun a' => ?_
  exact measurableSet_le (((altEnd_meas_loopFine sz n E u σ' a').sub_const _).norm) measurable_const

end Meas

/-- **Target `mem_of_lt_altExitTauN`**: strictly before the exit, the grid state is in `GoodSetN ∩ GoodLinN ∩ altYSetN`
(`mem_of_lt_gridExitTauN`). -/
theorem mem_of_lt_altExitTauN {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ}
    {Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ} {τ' D' : ℝ} {n : ℕ} {ω : PathΩ sz} {j : ℕ}
    (h : j < altExitTauN sz E s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω) :
    pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetN sz n (E n) (gridTime s v K n j) (k - 1) (Yl n) :=
  mem_of_lt_gridExitTauN h

/-- **Target `altExitMeasN`**: `{j < altExitTauN}` is `filt j`-measurable (`gridExitTauN_measurableSet` with
`measurableGoodSetN`, `measurableGoodLinN`, `measurableAltYSetN`). -/
theorem altExitMeasN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < altExitTauN sz E s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω} :=
  gridExitTauN_measurableSet (fun j =>
    ((measurableGoodSetN d sz n _ _ _ _ _ _ _ _).inter
      (measurableGoodLinN sz n _ _ _ _ _ _ _)).inter (measurableAltYSetN sz n _ _ _ _)) j

/-! ## 2. Target 2: the `hY` event on the grid (`altYGridN`) -/

section Grid

/-- Clause `STXiLKM ≤ Z` read as an entry bound: `‖(𝓛-𝒦)^{(j)}_{σ,a}(H)‖ ≤ (Z - 1) B^j` (copy of the private
`QLevelsB_norm_STLKM_le_of_XiLKM`, `QLevelsB.lean:62`). -/
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

/-- **The transfer and the union bound** (copy of the private `gridGood_grid`, `GridGoodN.lean:879`, and
`nqLin_grid`, `NQLin.lean:541`, with `altYSetN`): if w.h.p. `seqHflow n u ω ∈ altYSetN … u` for every
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

/-- **Target 2, `altYGridN`** (pin `T2294_altYGridN`, check file §2; supervisor 1102 O1, DECISIONS §95 (3)): from
the deterministic control `Ξ̂^{(𝓛-𝒦)}_l ≺ X` uniformly on `[s_n, v_n]`, with high probability the grid walk is in
`altYSetN` at the level `N^ε X` at every grid time `j ≤ K n` (`Prec.whp` at the exponent `ε`; `STXiLKM ≤ Z` gives
`‖(𝓛-𝒦)^{(l)}‖ ≤ (Z-1)B^l ≤ Z B^l`; `map_pathH_eq` at each `j`; `highProbAt_iInter`, `K n + 1 ≤ N^C`).  S3-18b
calls it with `l = n_ - 1`. -/
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

/-! ## 3. C1: the `𝒬`-remainder envelope and the bridge to `assembledRHSAltQN` -/

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

/-- **Target C1a, `gridDriftQN_envelope`** (RBM2D `gridDriftQN_envelope`, `AltEndCompose.lean:315` at `c9a24cf`; the
pattern of `gridDriftN_envelope`, `GridEnvelopeN.lean:111`): under the owed pin `STKbound E` (premise), eventually in
`n`, a.e., for every grid step `j < K n` and label, the `𝒬`-remainder `rGridQN` (tensors of `m + 2` indices, mollifier
at `m + 1`) is at most `qErrQN` at the envelope `N^{τ_K} η_{u_{j+1}}^{-(m+2)}` of `𝒦` on `[0, u_{j+1}]`
(`exists_norm_Kcal_le_win`, with `gridDriftQN` at `m ↦ m + 1` per `j`). -/
theorem gridDriftQN_envelope {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m)
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

/-- `kappaAltQN` is nonnegative (copy of the private `QBudgetA_kappa_nonneg`, `QBudgetA.lean:125`). -/
private theorem altEnd_kappa_nonneg (d k : ℕ) (Λg κ' KL g W ε : ℝ) (hW : 0 ≤ W) (u : ℕ → ℝ)
    (i m : ℕ) : 0 ≤ kappaAltQN d k Λg κ' KL g W ε u i m := by
  unfold kappaAltQN
  exact mul_nonneg (Real.rpow_nonneg hW _)
    (pow_nonneg (div_nonneg (by positivity) (by positivity)) _)

/-- The step error of `gridDriftN` is nonnegative (copy of the private `nqEnd_stepErrN_nonneg`,
`NQEndLin.lean:736`). -/
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

/-- **Target C1b, `assembledRHSAltQN_qErr_le`** (the bridge; ticket Design (c), finding).  The right side of the merged
`AssembledN` (`GridAssemblyN.lean:249-255`) at the target `m = K n` for the alternating chain (`κ = kappaAltQN`,
`εK = epsAltQN`, `c = cQVAltQN`, `k = m + 2`, `u = gridTime`), with the remainder `stepErr := qErrQN` (the `𝒬`-process
remainder of `gridDriftQN_envelope`) and an initial supremum `Xs ≤ X0`, is at most `assembledRHSAltQN` (whose last term
is the non-alternating `stepErrN`, `QBudgetA.lean:117-121`) plus `N^{-D_t}`, once the weighted `qErrQN` sum is at
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

/-! ## 4. C2: the variance proxy after the spectral-time shift, and `SubGaussStopN` -/

section C2

/-- The two `W`-power facts behind the shift `D ↦ D'' + 1` of C2: `W^{2C_nε}·W^{-(D''+1)} ≤ W^{-(D''+1)+C_Q}` and
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

/-- The monotone arithmetic of C2: replacing `x ↦ y` and `P(G + z) + x ↦ PG + y` in the closed form of
`qvFormQN_le_of_bounds`. -/
private theorem altEnd_qv_arith {κ4 A B P G x y z : ℝ} (hκ4 : 0 ≤ κ4) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hPz : P * z ≤ x) (h2x : 2 * x ≤ y) (hx0 : 0 ≤ x) :
    κ4 * (κ4 * (P * (G + z) + x) + A * x) + A * (B * x) ≤
      κ4 * (κ4 * (P * G + y) + A * y) + A * (B * y) := by
  have hin : P * (G + z) + x ≤ P * G + y := by rw [mul_add]; linarith
  have hxy : x ≤ y := by linarith
  gcongr

/-- **Target C2a, `hQ_altQN`** (RBM2D (C2) `hQ_alt`, `AltEndCompose.lean:422-571`; the pattern of `hQ_nonAltN`,
`NQGood2.lean:519`; fixed `n`): for `M ∈ GoodSetN n E u_j (m+2) Γ Λ Φc τ' D'` Hermitian and every `σ`, the proxy
`Δ · ((m+2) · qvFormQN_{u_{j+1},u_p}(M)(a))` of the `j`-th propagated `𝒬`-increment towards `u_p` is at most
`cQVAltQN … D'' p a j`.  Route: (D4) and (Vb) of `GoodSetN` at `u_j` are moved to `u_{j+1}` by
`norm_STeeM_shiftN_le`, `B_{u_j} ≤ B_{u_{j+1}}`, `η_{u_j}⁻¹ ≤ η_{u_{j+1}}⁻¹`, `ℓ_{u_j} ≤ ℓ_{u_{j+1}}`, then
`qvFormQN_le_of_bounds` (`QProxy.lean:1102`) at `m ↦ m + 1`, `v := u_{j+1}`, `w := u_p`, `D := D'' + 1`,
`M_ee = Γ(ΓΛ)B_{u_{j+1}}^{2k}/η_{u_{j+1}} + W^{-(D''+1)}`.  The shift hypothesis is
`W^{-D'} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-(D''+1)}` together with `2 ≤ W` (paper-delta candidate `T2294c`: the
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
  -- `G ≥ 0` is forced by (D4) (a norm is nonnegative and the quotient is positive)
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

/-- **Target C2b, `subGaussStop_altQN`** (RBM2D `subGaussStop_alt`, `AltEndCompose.lean:540-571`; pattern
`subGaussStop_linN`, `NQLin.lean:786`): the merged `azumaSubGQ_gridExitN` (`QProxy.lean:409`) at the alternating exit
family of `altExitTauN` (the family `GoodSetN ∩ GoodLinN ∩ altYSetN`; measurable by `altExitMeasN`'s ingredients) and the
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

/-! ## 5. C3: the kernel field on the grid -/

section C3

/-- **Target C3, `alt_hkerGridQN`** (RBM2D `altQ_hker_shift`, `AltEndCompose.lean:380-420`, reduced; the field `hker` of
`GridAssemblyHypN`): `alt_hkerQN` (`QDriftA.lean:353`) at the grid `u = gridTime s v K n`, `Kg = K n`
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

/-! ## 6. C4: the drift and class fields on the alternating exit family -/

section C4

/-- **Target C4a, `alt_hdriftGridQN`** (the field `hdrift` of `GridAssemblyHypN`): `alt_hdriftLinQN`
(`QBudgetB.lean:209`) with `τ := altExitTauN`; the premise `hτG` is components 1 and 2 of
`mem_of_lt_altExitTauN` and the premise `hY` is component 3 at the level `Yl n ≤ ν X`
(`altYSetN` at length `k - 1 = m + 1`; S3-18a2 takes `Yl n = N^{ε₁} X n`). -/
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

/-- **Target C4b, `alt_hA0clsGridQN`** (the field `hA0cls` of `GridAssemblyHypN`): `alt_hA0clsQN`
(`QDriftA.lean:473`, tensors of `m + 2` indices) with `τ := altExitTauN`: `hτG` is component 1 of
`mem_of_lt_altExitTauN` (`k = m + 1 + 1`, crude level `Φc`), and the crude sup `‖A_0‖ ≤ W^{C₀}` is an explicit premise
(a bound on `‖(𝓛-𝒦)^{(m+2)}(H_0)‖` at length `k`, which no clause of `GoodSetN` gives; see `altEnd_crudeSup`).
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

/-- **Target C4c, `alt_hDclsGridQN`** (the field `hDcls` of `GridAssemblyHypN`): `alt_hDclsQN`
(`QDriftB.lean:379`, tensors of `m + 2` indices, the existential `W₀` of the merged statement) with
`τ := altExitTauN`: `hτG` is component 1 of `mem_of_lt_altExitTauN`; the crude sups `hAcr`
(`‖(𝓛-𝒦)^{(m+2)}(H_j)‖ ≤ W^{C₀}`) and `hDcr` (`‖driftTensorN‖ ≤ W^{C₀}`) are explicit premises (preflight finding F1;
derivations from the exit family are `altEnd_crudeSup`, `altEnd_driftSup`). -/
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

/-- **The crude sup at length `k` from the exit family** (preflight finding F1; deterministic): for `H` Hermitian
(component 1 of `GoodSetN`), a bound `‖𝒦^{(k)}_{u,σ,a}‖ ≤ M_K` and `η_u^{-k} + M_K ≤ W^{C₀}`, `‖(𝓛-𝒦)^{(k)}_{u,σ}(H)‖ ≤ W^{C₀}`
in the sup norm (`STmaxLKM_crudeN`, `NQGood1.lean:927`, `crudeLKM_of_level`): the form of the `hcrude`, `hAcr` premises
of C4b, C4c. -/
theorem altEnd_crudeSup {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian) {k : ℕ}
    (hk : 1 ≤ k) {MK C₀ : ℝ}
    (hK : ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), ‖sz.STKloop n E u σ a‖ ≤ MK)
    (hη : (etaT E u)⁻¹ ^ k + MK ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (σ : Fin k → Bool) :
    ‖fun b : Fin k → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ := by
  have hmax := STmaxLKM_crudeN sz n hE hH hu0 hu1 (n' := k) (m := k) hk le_rfl hK
  refine crudeLKM_of_level d sz n E u H k σ _ C₀ (fun b => ?_) hη
  refine le_trans ?_ hmax
  exact Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖)
      (Finset.mem_univ (σ, b))

/-- **The crude sup of the drift tensor from the exit family** (preflight finding F1; deterministic):
`GoodLinN` (component 2) gives `‖driftTensorN‖ ≤ dDriftLinN` (`driftTensorN_norm_le_of_goodLin`), so a bound
`dDriftLinN ≤ W^{C₀}` gives the `hDcr` premise of C4c. -/
theorem altEnd_driftSup {d : ℕ} (sz : Sizes d) (n : ℕ) {E u Γ Φ₁ Φ₂ Φ₃ C₀ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H ∈ GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃)
    (hW : dDriftLinN sz n E u k Γ Φ₁ Φ₂ Φ₃ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (σ : Fin k → Bool) :
    ‖fun b : Fin k → Zd d (sz.L n) => driftTensorN sz n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hWpos.le C₀)).2 fun b =>
    (driftTensorN_norm_le_of_goodLin sz hk hH σ b).trans hW

end C4

/-! ## 7. C5: the identity, measurability, terminal value, de-`𝒬`, `Y` moments -/

section C5

/-- **Target C5a, `altEnd_hexp`** (RBM2D `altEnd_identity`, `AltEndCompose.lean:580`; literally the field `hexp` of
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

/-- **Target C5b, `altEnd_stronglyMeasurable_zVecQN`**: `zVecQN … j` is `filt sz (j + 1)`-strongly measurable
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

/-- **Target C5c, `altEnd_aFroz_eq_aTrue`**: on `{K n ≤ τ ω}` the frozen `𝒬`-process at the last grid index is the true
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

/-- **Target C5d, `altEnd_unQ`** (de-`𝒬` at the end, per matrix; RBM2D `altEnd_unQ`): for alternating `σ`, under the
hypotheses of `altB45N_levelM` (`QLevelsA.lean:376`; `GoodSetN` at a free crude level gives Hermitian and (Dec); `hY` the
length-`m + 1` level at `u`; the mollifier `ϑ` with `STMollifierProps`),
`‖(𝓛-𝒦)_{u,σ}(H)_a‖ ≤ ‖𝒬_u(𝓛-𝒦)_{u,σ}(H)_a‖ + N^{τ_N} B_u^{m+2} X`
(`STQop` unfolded, the first conjunct of `altB45N_levelM`, `norm_add_le`).  S3-18a2 applies it at `u = v_n`,
`H = H_{K n}` (the `altYSetN` component and (Dec) at `j = K n`, `u_{K n} = v_n`). -/
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

/-- **Target C5e, `altEnd_yMomentsMax`** (RBM2D `AltEndCompose` `yMomentsMax`; copy of the private `nqEnd_yMomentsMax`,
`NQEndLin.lean:1028`, over `yMomentsQUnifN`, `QProxy.lean:1468`): one `C_P` for all `σ : Fin (m + 2) → Bool`, chosen
before the grid `K`, such that eventually the `Y` moments of `yVecQN` (mollifier `QopAlgebra_mollifier … (m+1)`)
hold with `v_j = Δ² P`, `w_j = Δ⁴ P²` for every measurable stopping family.  The premise `∀ n, 0 < sz.lam n` is that of the
merged `yMomentsQUnifN` (`∀ n, STMollifierProps … (ϑ n)`; paper-delta candidate `T2294d`). -/
theorem altEnd_yMomentsMax {d : ℕ} (sz : Sizes d) {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hsize : sz.SizeTendsto) (hrange : sz.RangeCond τR v) (hlam : ∀ n, 0 < sz.lam n) (m : ℕ) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → ∀ σ : Fin (m + 1 + 1) → Bool,
      ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
        ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
          YMomentBoundsN sz (E n) σ (gridTime s v K n) τ (K n)
            (fun j ω => yVecQN sz E s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω)
            (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2) := by
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  choose CP hCP0 hCPev using fun σ : Fin (m + 1 + 1) → Bool =>
    yMomentsQUnifN sz κ τR E s v hκ hE hs0 hsv hv1 hsize hrange (m + 1)
      ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)
      (fun n => QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hC0 (by norm_num)
      (fun n => QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) (hlam n)) σ
  refine ⟨Finset.univ.sup' Finset.univ_nonempty CP,
    (hCP0 (fun _ => true)).trans (Finset.le_sup' CP (Finset.mem_univ _)), fun K hK0 σ => ?_⟩
  filter_upwards [hCPev σ K hK0] with n hn
  obtain ⟨P, hP0, hPle, hτ⟩ := hn
  exact ⟨P, hP0, hPle.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n)
    (Finset.le_sup' CP (Finset.mem_univ σ))), hτ⟩

end C5

/-! ## 8. Compiled nonempty instances (namespace `QEndAInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) at the data of
`QBudgetBInst`/`QDriftBInst`: `n = 4` (`L = 20`, `W = 10^5`, `N = (W L)^3 = 8·10^18`) for the fixed-`n` instances, `m = 2`
(tensors of `k = 4` indices), `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4` (`Δ = 1/8`), the alternating `σ = (+,-,+,-)`, the
explicit mollifier `QopAlgebra_mollifier … (m+1)`; and a large `n` (`W_n` above the abstract thresholds `qProxyW0`,
`QDriftA_W0`, taken from `exists_nat_ge`/`inst_data`) where an abstract constant enters.  The numeric helpers are copies of
the private ones of `QDriftBInst` (`QDriftB.lean:451-754`) and `QBudgetBInst` (`QBudgetB.lean:880-935`). -/

namespace QEndAInst

open RBM.Gauss.SizesInst RBM.Ind.GridDriftNCheck RBM.Ind.GridEnvelopeNCheck RBM.Ind.QGridBCheck

private theorem rpow_pow5 {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y ^ 5) ^ r = y ^ (5 * r) := by
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]; norm_num

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
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

/-- The `𝒦` envelope on `[0, 1/2]` at `n` (`exists_norm_Kcal_le_win` for the `STKbound E0` proved by `stKbound_holds`),
for the loops of length `≤ 4`, together with a large `n` (`max W₁ 17 ≤ x = 2(n+1)`). -/
private theorem inst_data2 (W₁ : ℝ) :
    ∃ n : ℕ, max W₁ 17 ≤ 2 * ((n : ℝ) + 1) ∧
      ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
        2 ≤ J.length → J.length ≤ 4 →
          ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4 := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  have hKev := exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 4 1 one_pos
  obtain ⟨n, hn1, hn2⟩ := (hKev.and (Filter.eventually_ge_atTop ⌈max W₁ 17⌉₊)).exists
  have hn : max W₁ 17 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  exact ⟨n, by have := Nat.cast_nonneg (α := ℝ) n; linarith, hn1⟩

/-- **The crude sup at length 4 from the exit family** at a grid time `u ∈ [0, 1/2]` and `E = 0`: for Hermitian `H`,
`‖(𝓛-𝒦)^{(4)}_{u,σ}(H)‖ ≤ W^7` (`altEnd_crudeSup` with `M_K = 16 N`, from the `𝒦` envelope; `N ≤ W^6`, `W ≥ 17`). -/
private theorem crude_u (n : ℕ) (hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ))
    (hn1 : ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 4 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    {H : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin (3 + 1) → Bool) :
    ‖fun a => sz0.STLKM n 0 u H σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  have hsize : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by
    exact_mod_cast sz0_size_le_W_pow n
  have hK : ∀ (σ' : Fin 4 → Bool) (a : Fin 4 → Zd 3 (sz0.L n)),
      ‖sz0.STKloop n 0 u σ' a‖ ≤ ((sz0.size n : ℕ) : ℝ) * 16 := by
    intro σ' a
    have hJ : sz0.STKloop n 0 u σ' a = KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) u (loopOf σ' a) := rfl
    rw [hJ]
    have h2 := hn1 u ⟨hu0, hu⟩ (loopOf σ' a) (by simp [LoopIdx.WF, loopOf])
      (by simp [LoopIdx.length, loopOf]) (by simp [LoopIdx.length, loopOf])
    have hη' : etaT (E0 n) (1 / 2) = 1 / 2 := etaT_zero_half
    simp only [hη', Real.rpow_one] at h2
    refine h2.trans (le_of_eq ?_)
    norm_num
  have hη1 : (etaT 0 u)⁻¹ ^ 4 ≤ 16 := by
    have h : (1 / 2 : ℝ) ≤ etaT 0 u := by
      unfold etaT; rw [mE_zero_im]; linarith
    have h' : (etaT 0 u)⁻¹ ≤ 2 := by
      calc (etaT 0 u)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h
        _ = 2 := by norm_num
    calc (etaT 0 u)⁻¹ ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (inv_nonneg.2 (by linarith)) h' 4
      _ = 16 := by norm_num
  have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h6 : (16 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by
    have h1 : (17 : ℝ) ^ 6 ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hW17 6
    have h2 : (16 : ℝ) ≤ 17 ^ 6 := by norm_num
    linarith
  have h5 : (17 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ 6 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    have : ((sz0.W n : ℕ) : ℝ) ^ 7 = ((sz0.W n : ℕ) : ℝ) ^ 6 * ((sz0.W n : ℕ) : ℝ) := by ring
    rw [this]
    nlinarith [pow_pos hWpos 6]
  have hu1 : u < 1 := by linarith
  have hη : (etaT 0 u)⁻¹ ^ 4 + ((sz0.size n : ℕ) : ℝ) * 16 ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
    rw [h7]
    linarith [hη1, hsize, h5, h6]
  exact altEnd_crudeSup sz0 n (E := 0) (by norm_num) hu0 hu1 hH (by norm_num) (MK := ((sz0.size n : ℕ) : ℝ) * 16)
    (C₀ := 7) hK hη σ

/-- `0 < gridExitTauN` when the grid walk starts in `G 0` and the grid is not empty (`K n > 0`): the first hit is not
at `0` (`hittingBtwn_mem_set_of_hittingBtwn_lt`). -/
private theorem zero_lt_exitTau {d : ℕ} {sz : Sizes d} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)} {ω : PathΩ sz}
    (hK : 0 < K n) (h0 : pathH sz s v K n 0 ω ∈ G 0) : 0 < gridExitTauN sz s v K n G ω := by
  by_contra hne
  have h0' : gridExitTauN sz s v K n G ω = 0 := Nat.eq_zero_of_not_pos hne
  have hlt : gridExitTauN sz s v K n G ω < K n := by omega
  have hmem : (1 / 2 : ℝ) ≤ (G (gridExitTauN sz s v K n G ω))ᶜ.indicator (fun _ => (1 : ℝ))
      (pathH sz s v K n (gridExitTauN sz s v K n G ω) ω) :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  rw [h0', Set.indicator_of_notMem (show pathH sz s v K n 0 ω ∉ (G 0)ᶜ from fun hc => hc h0)] at hmem
  norm_num at hmem



private abbrev H0 : Matrix (Idx 3 (sz0.L 4) (sz0.W 4)) (Idx 3 (sz0.L 4) (sz0.W 4)) ℂ := 0

private theorem hx4 : (10 : ℝ) ≤ 2 * (((4 : ℕ) : ℝ) + 1) := by norm_num

private theorem W4 : ((sz0.W 4 : ℕ) : ℝ) = 100000 := by
  rw [(sz0_facts 4).1]; norm_num

private theorem N4 : ((sz0.size 4 : ℕ) : ℝ) = 8000000000000000000 := by
  have : sz0.size 4 = 8000000000000000000 := by norm_num [Sizes.size, sz0]
  exact_mod_cast this

private theorem W10_4 : ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt 10 := by
  rw [(sz0_facts 4).1, rpow_pow5 (by positivity), show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  norm_num

private theorem sqrt10_pow6 : (Real.sqrt 10) ^ (3 * 2) = 1000 := by
  rw [show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The alternating sign pattern of the instances. -/
private abbrev σalt : Fin (2 + 1 + 1) → Bool := ![true, false, true, false]

private theorem σalt_last : σalt (Fin.last (2 + 1)) = !σalt 0 := by decide

private theorem hFv4 : ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤
    ((sz0.W 4 : ℕ) : ℝ) * (((sz0.size 4 : ℕ) : ℝ) ^ (2 * 2 + 4))⁻¹ := by
  rw [W4, N4, Real.rpow_neg (by norm_num), show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem hMΛ4 : (2 * ((2 : ℕ) : ℝ) + 5) * (3 * 4 ^ (3 * 2) * (2 / Real.sqrt 1) * Cmol3 *
    ((sz0.W 4 : ℕ) : ℝ) ^ 2) ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [W4, N4, Real.rpow_two, Real.sqrt_one]
  norm_num

private theorem hNu4 : (((sz0.size 4 : ℕ) : ℝ))⁻¹ ≤ 1 - 0 := by
  rw [N4]; norm_num

/-- `0 ∈ GoodLinN` at the levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, kΓΦ², 1)`, `k = 4` (`goodSetN_subset_goodLinN`). -/
private theorem zero_mem_lin (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      GoodLinN sz0 n 0 0 (3 + 1) 4 1 (((3 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 :=
  goodSetN_subset_goodLinN sz0 n 0 0 (3 + 1) 4 100 1 τ' D' (zero_mem_inst n hlam1 τ' D')

/-- The levels `Φ₂ = kΓΦ² = 16` of the `GoodLinN` set of the instances. -/
private noncomputable abbrev Φ2v : ℝ := ((3 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2

/-- `0` is in the three sets of the exit family at `u = 0` (`GoodSetN` at `(4, 100, 1)`, `GoodLinN` at `(4, 1, 16, 1)`,
`altYSetN` at length `3` and level `4`), for every `n`, `τ'`, `D'`. -/
private theorem zero_mem_G0 (n : ℕ) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (2 + 1 + 1) 4 100 1 τ' D' ∩ GoodLinN sz0 n 0 0 (2 + 1 + 1) 4 1 Φ2v 1 ∩
        altYSetN sz0 n 0 0 (2 + 1 + 1 - 1) 4 := by
  refine ⟨⟨zero_mem_inst n (lam_le_one n) τ' D', zero_mem_lin n (lam_le_one n) τ' D'⟩, fun σ' a' => ?_⟩
  have h := (goodSetN_LKM_le 3 sz0 n 0 0 (2 + 1 + 1) 4 100 1 τ' D' 0
    (zero_mem_inst n (lam_le_one n) τ' D') (by norm_num) (2 + 1) (by omega) (by omega)).2 σ' a'
  simpa using h

/-- The premise `hY` of targets 1-2 at the data: `‖(𝓛-𝒦)^{(j)}‖ ≤ ν X B^{m+1}` with `ν = W`, `X = 1`, `j = m + 1 = 3`
(`goodSetN_LKM_le`, `4 ≤ W`). -/
private theorem hY4 : ∀ (σ' : Fin (2 + 1) → Bool) (a' : Fin (2 + 1) → Zd 3 (sz0.L 4)),
    ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ ((sz0.W 4 : ℕ) : ℝ) * 1 * sz0.Bctl 4 0 ^ (2 + 1) := by
  intro σ' a'
  have h := (goodSetN_LKM_le 3 sz0 4 0 0 (2 + 1 + 1) 4 100 1 (1 / 10) 40 H0
    (zero_mem_inst 4 (lam_le_one 4) _ _) (by norm_num) (2 + 1) (by omega) (by omega)).2 σ' a'
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (pow_pos (STBctl_pos sz0 4 (by norm_num)) _).le)
  rw [W4]; norm_num



/-! ### The shift hypothesis `hδ` of C2 at a fixed `n` (copies of the private helpers of `NQEndLin.lean`, `:127-152`,
`:459-482`, `:533-552`, and of the body of `nqEnd_ev_hδ`, `:558-647`; ticket T2199) -/

section ShiftFixed

variable {d : ℕ} (sz : Sizes d)

private theorem altEnd_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n


/-- `W^d L^d = N` (the private `gridEnv_size_cast` of `GridEnvelopeN`). -/
private theorem altEnd_size_cast (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- **Crude `W ≤ N`** (`W ≤ W^d ≤ (W L)^d = N`, `d ≥ 1`): the bound for the positive powers of `W`. -/
private theorem altEnd_W_le_size (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ (sz.W n) ^ d := Nat.le_self_pow (by omega) _
  have h2 : (sz.W n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
  exact_mod_cast h1.trans h2

/-- `Δ ≤ N^{-C_K}` on a grid with `N^{C_K} ≤ K n` and `v - s ≤ 1` (RBM2D `NonAltEnd_step_le`,
`NonAltEnd:652`). -/
private theorem altEnd_step_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ}
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (altEnd_one_le_size sz n)
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hK0 : (0 : ℝ) < K n := lt_of_lt_of_le hpos hK
  unfold gridStep
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc v n - s n ≤ 1 := hvs
    _ = (((sz.size n : ℕ) : ℝ) ^ C_K)⁻¹ * ((sz.size n : ℕ) : ℝ) ^ C_K :=
        (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ (((sz.size n : ℕ) : ℝ) ^ C_K)⁻¹ * (K n : ℝ) :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- The one-step increment of the grid times is `Δ`. -/
private theorem altEnd_gridTime_succ_sub (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- The shift error with `η_{u'}⁻¹ ≤ B`: `eeShiftErrN ≤ W^d k L^d (2k+2) B^{2k+3} (u' - u)`
(RBM2D `NonAltEnd_eeShiftErr_le`, `NonAltEnd:694`, with `W^d`, `L^d`). -/
private theorem altEnd_eeShiftErrN_le {d L W : ℕ} (hW : 1 ≤ W) {E : ℝ} (k : ℕ) {u u' B : ℝ}
    (hη0 : 0 ≤ (etaT E u')⁻¹) (hB : (etaT E u')⁻¹ ≤ B) (hΔ : 0 ≤ u' - u) :
    eeShiftErrN d L W E k u u' ≤
      (W : ℝ) ^ d * ((k : ℝ) * ((L : ℝ) ^ d * (((2 * k + 2 : ℕ) : ℝ) *
        (B ^ (2 * k + 2 + 1) * (u' - u))))) := by
  unfold eeShiftErrN loopShiftErrN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWi : (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW1))
  have hWi0 : 0 ≤ (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) := by positivity
  have h1 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) ≤ B ^ (2 * k + 2 + 1) := pow_le_pow_left₀ hη0 hB _
  have h2 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) * (u' - u) ≤
      B ^ (2 * k + 2 + 1) * (u' - u) := by
    calc _ ≤ (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * 1 * (u' - u) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWi (by positivity)) hΔ
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right h1 hΔ
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  gcongr


/-- (`hδ`, fixed `n`) `W^{-(D''+1)} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-D''}` for every `j < K n`, given `N^{C_K} ≤ K n`,
`C_K ≥ D'' + 2k + 5`, `2 ≤ W`, `N ≥ 2k(2k+2)`, `η_{v_n}⁻¹ ≤ N` (the body of `nqEnd_ev_hδ`, `NQEndLin.lean:558`, after its
`filter_upwards`). -/
private theorem altEnd_shift_fixed (hd : 1 ≤ d) (k : ℕ) {D'' C_K : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n : ℕ)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0) (hηn : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hD'' : 0 ≤ D'')
    (hCK : D'' + 2 * (k : ℝ) + 5 ≤ C_K) (hKNn : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ))
    (hNA : 2 * ((k : ℝ) * ((2 * k + 2 : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ)) :
    ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
  set A : ℝ := (k : ℝ) * ((2 * k + 2 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  intro j hj
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altEnd_W_le_size sz hd n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := altEnd_step_le sz hKNn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu'v : gridTime s v K n (j + 1) ≤ v n := by
    have h := ST_gridTime_mono s v K n (hsv n) (show j + 1 ≤ K n by omega)
    rwa [gridTime_last s v K n (hK0 n)] at h
  have hdiff := altEnd_gridTime_succ_sub s v K n j
  have hEn := hE n
  have hηv : 0 < etaT (E n) (v n) := etaT_pos hEn (hv1 n)
  have hη' : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hEn (hu'v.trans_lt (hv1 n))
  have hηle : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    refine le_trans (inv_anti₀ hηv ?_) hηn
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hEn).le
  have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ := inv_nonneg.2 hη'.le
  have hee := altEnd_eeShiftErrN_le (d := d) (L := sz.L n) (W := sz.W n) (sz.W_pos n) k
    (E := E n) (u := gridTime s v K n j) (u' := gridTime s v K n (j + 1)) hη0 hηle
    (by rw [hdiff]; exact hΔ0)
  rw [hdiff] at hee
  have hsz := altEnd_size_cast sz n
  have hpow : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
      ((sz.size n : ℕ) : ℝ) ^ (-C_K) = ((sz.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + 4) - C_K) := by
    have e1 : ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) =
        ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [e1]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) *
          ((sz.size n : ℕ) : ℝ) ^ (-C_K)
        = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) *
          ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by rw [Real.rpow_one]
      _ = ((sz.size n : ℕ) : ℝ) ^ (1 + (2 * (k : ℝ) + 3) + (-C_K)) := by
          rw [Real.rpow_add hN0 (1 + (2 * (k : ℝ) + 3)) (-C_K), Real.rpow_add hN0 (1 : ℝ)]
      _ = _ := by congr 1; ring
  have hmain : eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    refine hee.trans ?_
    have e : ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
        (((2 * k + 2 : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n)))) =
        (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * A *
          (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n) := by rw [hA]; ring
    rw [e, hsz]
    calc ((sz.size n : ℕ) : ℝ) * A * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n)
        ≤ ((sz.size n : ℕ) : ℝ) * A * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
            ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by gcongr
      _ = A * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
            ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by ring
      _ = A * ((sz.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + 4) - C_K) := by rw [hpow]
      _ ≤ A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hA0
  have hN2 : A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have h0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hN0.le _
    have h2A : A * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hN0]; linarith
    calc A * (((sz.size n : ℕ) : ℝ) ^ (-D'') * ((sz.size n : ℕ) : ℝ)⁻¹)
        = ((sz.size n : ℕ) : ℝ) ^ (-D'') * (A * ((sz.size n : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') * (1 / 2) := mul_le_mul_of_nonneg_left h2A h0
      _ = ((sz.size n : ℕ) : ℝ) ^ (-D'') / 2 := by ring
  have hWD : ((sz.size n : ℕ) : ℝ) ^ (-D'') ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
    Real.rpow_le_rpow_of_nonpos hWpos hWN (by linarith)
  have hWm1 : ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hpos : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hWpos.le _
    have : ((sz.W n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hW2
    calc ((sz.W n : ℕ) : ℝ) ^ (-D'') * ((sz.W n : ℕ) : ℝ)⁻¹
        ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') * (1 / 2) := mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  linarith

end ShiftFixed

/-! ### Instances 1, 2, 7: the `hY` set, the `hY` event on the grid, the pinned statement -/

/-- **Instance 1** (`altYSetN`, `measurableAltYSetN`): the zero matrix (the walk start `H_0 = 0` at `s ≡ 0`) is in
`altYSetN` at length `m + 1 = 3`, level `ν X = W·1` (`goodSetN_LKM_le`), and the set is measurable. -/
theorem altYSetN_instance :
    (0 : Matrix (Idx 3 (sz0.L 4) (sz0.W 4)) (Idx 3 (sz0.L 4) (sz0.W 4)) ℂ) ∈
      altYSetN sz0 4 0 0 (2 + 1) (((sz0.W 4 : ℕ) : ℝ) * 1) ∧
    MeasurableSet (altYSetN sz0 4 0 0 (2 + 1) (((sz0.W 4 : ℕ) : ℝ) * 1)) :=
  ⟨fun σ' a' => hY4 σ' a', measurableAltYSetN sz0 4 0 0 (2 + 1) _⟩

/-- **Instance 2** (`altYGridN`) at `sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `l = 3`, `X ≡ 1`, `C = 1`
(`K + 1 = 5 ≤ N`, from `sz0_tendsto`), `ε = 1/10`.  The premise `Prec (Ξ̂^{(𝓛-𝒦)}_3 ≺ 1)` on `[s_n, v_n]` is the owed
`STLKU`-type gate (`Step34Pins.lean:184`) and stays a hypothesis; the conclusion is unfolded at one `n` (failure
probability of the grid event at most `N^{-1}`). -/
theorem altYGridN_instance
    (hP : Prec sz0 (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n)
      (fun n u ω => STXiLK sz0 n ((fun _ => (0 : ℝ)) n) (u : ℝ) 3 ω) (fun n _ _ => (fun _ => (1 : ℝ)) n)) :
    ∃ n : ℕ, pathP sz0 {ω | ∀ j ≤ 4, pathH sz0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j ω ∈
        altYSetN sz0 n 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j) 3
          (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1)}ᶜ ≤
      ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have h := altYGridN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 3
    (fun _ => (1 : ℝ)) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl) hP 1
    (by
      filter_upwards [sz0_tendsto.eventually_ge_atTop 5] with n hn
      rw [Real.rpow_one]
      exact_mod_cast hn)
    (1 / 10) (by norm_num)
  obtain ⟨n, hn⟩ := (h 1 one_pos).exists
  exact ⟨n, hn⟩

/-- **Instance 7**: the pinned statement `T2294_altYGridN` (check file §2, copied verbatim) is proved by `altYGridN`. -/
private def T2294_altYGridN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (l : ℕ) (X : ℕ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) → (∀ n, K n ≠ 0) → (∀ n, 1 ≤ X n) →
    Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLK sz n (E n) (u : ℝ) l ω) (fun n _ _ => X n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l
          (((sz.size n : ℕ) : ℝ) ^ ε * X n)})

example : T2294_altYGridN := @altYGridN


/-! ### Instance 3: the `𝒬`-remainder envelope and the bridge -/

private abbrev sg0 : ℕ → ℝ := fun _ => 0

private abbrev vg2 : ℕ → ℝ := fun _ => 1 / 2

/-- **Instance of C1a** (`gridDriftQN_envelope`) at `sz0` (`SizeTendsto` by `sz0_tendsto`; `STKbound E0` by the proved
`stKbound_holds`), `m = 2` (`k = 4`), `κ = 1`, `τ_K = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, the alternating `σ`: there
is an `n` where, a.e. in the walk, every grid step `j < 4` and label has `‖rGridQN‖ ≤ qErrQN` at the envelope
`N η_{u_{j+1}}^{-4}`. -/
theorem gridDriftQN_envelope_instance :
    ∃ n : ℕ, ∀ᵐ ω ∂(pathP sz0), ∀ j, j < 4 → ∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
      ‖rGridQN sz0 E0 sg0 vg2 (fun _ => 4) n (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt j ω a‖ ≤
        qErrQN sz0 E0 sg0 vg2 (fun _ => 4) n (2 + 1) ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
          (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2)
          (((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * (etaT (E0 n) (gridTime sg0 vg2 (fun _ => 4) n (j + 1)))⁻¹ ^
            (2 + 1 + 1)) j := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  exact (gridDriftQN_envelope sz0 1 one_pos 2 (by norm_num) 1 one_pos sz0_tendsto hKb
    (fun _ => by norm_num [E0]) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (Filter.Eventually.of_forall lam_pos_n) σalt).exists

/-- The kernel weight of the instance of C1b (`k = 4` indices, `Λ_g = κ' = K_L = 1`, `ε = 1/10`, grid `K n = N_n^{31}`). -/
private noncomputable abbrev kapI (n i m' : ℕ) : ℝ :=
  kappaAltQN 3 (2 + 1 + 1) 1 1 1 (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 10) (gridTime sg0 vg2 Kc31 n) i m'

/-- The additive decay weight of the instance of C1b. -/
private noncomputable abbrev epsI (n i m' : ℕ) : ℝ :=
  epsAltQN 3 (2 + 1 + 1) 1 1 1 ((sz0.W n : ℕ) : ℝ) i m'

/-- **Instance of C1b** (`assembledRHSAltQN_qErr_le`) at `sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K n = N_n^{31}` (`Kc31`),
`m = 2` (`k = 4`), `D_t = 1`, `τ_K = 1/2`, the mollifier constants `C₁ = (1 + 40·9)6^9`, `C₂ = 1000(1 + 9)²`: the weighted
`qErrQN` sum is at most `N^{-1}` by the merged `sum_weighted_qErrQN_instance` (`QGridB.lean:723`); the five common terms
are at the real values `Λ_g = κ' = K_L = C = 1`, `c = 1/2`, `ε = ε_q = 1/10`, `Γ = Λ = dd ≡ 1`, `δ0 = δD = D'' = D_Y = 1`,
`X_s = 1 ≤ X_0 = 2`, every label `a`: the left side (the `AssembledN` right side with `stepErr := qErrQN`) is at most
`assembledRHSAltQN … + N^{-1}`. -/
theorem assembledRHSAltQN_qErr_le_instance :
    ∃ n : ℕ, ∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
      kapI n 0 (Kc31 n) * 1 + epsI n 0 (Kc31 n) * 1 +
        gridStep sg0 vg2 Kc31 n * ∑ j ∈ Finset.range (Kc31 n), (kapI n (j + 1) (Kc31 n) * 1 + epsI n (j + 1) (Kc31 n) * 1) +
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Real.sqrt (∑ j ∈ Finset.range (Kc31 n),
          (cQVAltQN sz0 E1 sg0 vg2 Kc31 n 2 1 1 1 1 (1 / 2) (1 / 10) (fun _ => 1) (fun _ => 1) 1 (Kc31 n) a j : ℝ)) +
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) +
        ∑ j ∈ Finset.range (Kc31 n), (1 + (1 - gridTime sg0 vg2 Kc31 n (Kc31 n))⁻¹) ^ (2 + 1 + 1) *
          qErrQN sz0 E1 sg0 vg2 Kc31 n (2 + 1) ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
            (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2) (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime sg0 vg2 Kc31 n (j + 1)))⁻¹ ^ (2 + 1 + 1)) j ≤
      assembledRHSAltQN sz0 E1 sg0 vg2 Kc31 n 2 1 1 1 1 (1 / 2) (1 / 10) (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 1 1 1
        (1 / 2) (1 / 10) 2 a + ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨n, hn⟩ := (sum_weighted_qErrQN_instance.and (Filter.eventually_ge_atTop 0)).exists
  refine ⟨n, fun a => ?_⟩
  exact assembledRHSAltQN_qErr_le sz0 E1 sg0 vg2 Kc31 n 2 1 1 1 1 (1 / 2) (1 / 10) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) 1 1 1 1 (1 / 2) (1 / 10) 1 2 1 ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
    (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2) a (by norm_num [E1]) (by norm_num [sg0]) (by norm_num [sg0, vg2])
    (by norm_num [vg2]) (Kc31_ne_zero n) (by norm_num) (by norm_num) (by convert hn.1 (Kc31 n) le_rfl using 3)

/-! ### Instance 4: the variance proxy after the shift (C2) and `SubGaussStopN` -/

/-- The mollifier constant `C = (1 + 40·9) 6^9` of `QopAlgebra_mollifier … 3` (`d = 3`, `m + 1 = 3`). -/
private noncomputable abbrev Cm2 : ℝ := (1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1))

/-- `B_u ≤ 4` for `0 ≤ u ≤ 1/2` at `sz0` (`W ≥ 1`, `L ≥ 4`, `g ≤ 1`; the pattern of `crude_block`). -/
private theorem Bctl_le_four (n : ℕ) (hW : 1 ≤ ((sz0.W n : ℕ) : ℝ)) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    sz0.Bctl n u ≤ 4 := by
  have hL4 := L_ge_four n
  have hlam := lam_pos_n n
  have hx : (1 / 2 : ℝ) ≤ |1 - u| := by rw [abs_of_nonneg (by linarith)]; linarith
  have h1 : ((sz0.lam n) ^ 2 + |1 - u|)⁻¹ ≤ 2 := by
    have h : (1 / 2 : ℝ) ≤ (sz0.lam n) ^ 2 + |1 - u| := by nlinarith [sq_nonneg (sz0.lam n)]
    calc _ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h
      _ = 2 := by norm_num
  have h3 : (((sz0.L n : ℕ) : ℝ) ^ 3 * |1 - u|)⁻¹ ≤ 1 := by
    have hL3 : (64 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hL4 3]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hBpar0 : 0 ≤ Bparam 3 (sz0.L n) (sz0.lam n) u 0 := by unfold Bparam; positivity
  have hBpar : Bparam 3 (sz0.L n) (sz0.lam n) u 0 ≤ 3 := by
    unfold Bparam
    have h2 : (((((0 : ℕ) : ℝ)) + 1) ^ (3 - 2))⁻¹ = 1 := by norm_num
    rw [h2, mul_one]
    linarith
  have hW3 : ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  unfold Sizes.Bctl
  calc ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) * Bparam 3 (sz0.L n) (sz0.lam n) u 0 ≤ 1 * 3 :=
        mul_le_mul hW3 hBpar hBpar0 zero_le_one
    _ ≤ 4 := by norm_num

private theorem etaT_zero (u : ℝ) : etaT 0 u = 1 - u := by
  unfold etaT
  rw [mE_zero_im, mul_one]

/-- `v ≡ 1/2 ≤ 1 - g²/L²` at `sz0` (`g ≤ 1`, `L ≥ 4`). -/
private theorem hwL_gen (n : ℕ) : vg2 n ≤ 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by
  have hl1 := lam_le_one n
  have hl0 := lam_pos_n n
  have hL4 := L_ge_four n
  have : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  norm_num [vg2]
  linarith

/-- `W⁻¹ ≤ (1 - v)/(1 - s) = 1/2` for `W ≥ 2`. -/
private theorem hWt_gen (n : ℕ) (hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) :
    (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - vg2 n) / (1 - sg0 n) := by
  norm_num [vg2, sg0]
  exact (inv_anti₀ (by norm_num) hW2 : _).trans_eq (by norm_num)

/-- **Instances of C2 and of `subGaussStop_altQN`** at `sz0` (`d = 3`), `m = 2` (`k = 4`), `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`,
`σ` alternating, `M = 0 ∈ GoodSetN` at the levels `(Γ, Λ, Φc) = (4, 100, 1)` (`GoodLinN` at `(4, 1, 16, 1)`), `Λ_g = κ' = 1`,
`K_L = 2`, `C = (1 + 40·9)6^9`, `c = 1/2`, `ε = 1/5`, `τ' = 1/10`, `C₀ = 7`, and the abstract constant `C_Q = qProxyCQ`
(`D'' = 5 + C_Q`, `D' = D'' + 2`, `W_n ≥ qProxyW0 …`).  The shift hypothesis is discharged by the fixed-`n` form of
`nqEnd_ev_hδ` on the grid `K n = ⌈N^{D'' + 14}⌉` (so `Δ ≤ N^{-(D''+14)}`; the window `[0, 1/2]` is not collapsed).  At
`j = 0 < p = 1`: the proxy `Δ · (4 · qvFormQN_{u_1,u_1}(0)(a)) ≤ cQVAltQN`, and `SubGaussStopN` of the stopped propagated
first-chaos part for the exit family `altExitTauN`. -/
theorem hQ_altQN_subGaussStop_altQN_instance :
    ∃ (K : ℕ → ℕ) (n : ℕ), K n ≠ 0 ∧ 0 < gridStep sg0 vg2 K n ∧
      (∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
        gridStep sg0 vg2 K n * (((2 + 1 + 1 : ℕ) : ℝ) * qvFormQN sz0 n
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) 0 (gridTime sg0 vg2 K n (0 + 1))
          (gridTime sg0 vg2 K n 1) σalt
          (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) a) ≤
        (cQVAltQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K n 2 1 1 2 Cm2 (1 / 2) (1 / 5) (fun _ => 4) (fun _ => 100)
          (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2)) 1 a 0 : ℝ)) ∧
      (∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
        SubGaussStopN sz0 ((fun _ => (0 : ℝ)) n) σalt (gridTime sg0 vg2 K n)
          (altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K (2 + 1 + 1) (fun _ => 4) (fun _ => 100) (fun _ => 1)
            (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10)
            (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) + 1 + 1) n)
          (fun j ω => zVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K n j
            (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt ω) 1 a 0
          (cQVAltQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K n 2 1 1 2 Cm2 (1 / 2) (1 / 5) (fun _ => 4) (fun _ => 100)
            (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2)) 1 a 0)) := by
  set CQ : ℝ := qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) with hCQdef
  have hCQ0 : 0 < CQ := qProxyCQ_pos (by norm_num) _ one_pos two_pos (by positivity) (by norm_num)
  set D'' : ℝ := 5 + CQ with hD''def
  set W₀ : ℝ := qProxyW0 3 (2 + 1) 1 2 Cm2 (1 / 2) 7 (1 / 5) (D'' + 1) with hW₀def
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max W₀ 100) 17)
  have hx : max (max W₀ 100) 17 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx100 : (100 : ℝ) ≤ 2 * ((n : ℝ) + 1) := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := (((le_max_left _ _).trans (le_max_left _ _)).trans hx).trans hxW
  have hW100 : (100 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx100.trans hxW
  have hWN : ((sz0.W n : ℕ) : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := altEnd_W_le_size sz0 (by norm_num) n
  have hN100 : (100 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := hW100.trans hWN
  have hN0 : ∀ m : ℕ, (0 : ℝ) < ((sz0.size m : ℕ) : ℝ) := fun m =>
    lt_of_lt_of_le one_pos (by exact_mod_cast sz0.one_le_size m)
  set CK : ℝ := D'' + 14 with hCK
  set Kf : ℕ → ℕ := fun m => ⌈((sz0.size m : ℕ) : ℝ) ^ CK⌉₊ with hKf
  have hK0 : ∀ m, Kf m ≠ 0 := fun m =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (hN0 m) _)).ne'
  have hKNn : ((sz0.size n : ℕ) : ℝ) ^ CK ≤ (Kf n : ℝ) := Nat.le_ceil _
  have hKpos : 1 ≤ Kf n := Nat.one_le_iff_ne_zero.2 (hK0 n)
  have hΔ : 0 < gridStep sg0 vg2 Kf n := by
    unfold gridStep
    exact div_pos (by norm_num [sg0, vg2]) (by exact_mod_cast Nat.pos_of_ne_zero (hK0 n))
  have hEn : ∀ m, |(fun _ : ℕ => (0 : ℝ)) m| < 2 := fun _ => by norm_num
  have hs0 : ∀ m, 0 ≤ sg0 m := fun _ => le_rfl
  have hsv : ∀ m, sg0 m ≤ vg2 m := fun _ => by norm_num [sg0, vg2]
  have hv1 : ∀ m, vg2 m < 1 := fun _ => by norm_num [vg2]
  have hηn : (etaT ((fun _ : ℕ => (0 : ℝ)) n) (vg2 n))⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) := by
    change (etaT 0 (1 / 2))⁻¹ ≤ _
    rw [etaT_zero_half, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
    linarith
  have hNA : 2 * (((4 : ℕ) : ℝ) * ((2 * 4 + 2 : ℕ) : ℝ)) ≤ ((sz0.size n : ℕ) : ℝ) := by
    have h80 : (80 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by linarith
    have e : 2 * (((4 : ℕ) : ℝ) * ((2 * 4 + 2 : ℕ) : ℝ)) = 80 := by norm_num
    rw [e]; exact h80
  have hCKle : D'' + 1 + 2 * ((4 : ℕ) : ℝ) + 5 ≤ CK := by rw [hCK]; push_cast; linarith
  have hδall := altEnd_shift_fixed sz0 (by norm_num) 4 (D'' := D'' + 1) (C_K := CK) (E := fun _ => (0 : ℝ))
    (s := sg0) (v := vg2) (K := Kf) n hEn hs0 hsv hv1 hK0 hηn (by linarith) hCKle hKNn hW2 hNA
  have hδ0 := hδall 0 (Nat.pos_of_ne_zero (hK0 n))
  -- the bound on the sup of `𝓔 ⊗ 𝓔` at `u_1`
  have hmem := ST_gridTime_mem sg0 vg2 Kf n 1 (by norm_num [sg0, vg2]) (hK0 n) hKpos
  have hu1 : gridTime sg0 vg2 Kf n (0 + 1) ≤ 1 / 2 := by simpa [vg2] using hmem.2
  have hu10 : 0 ≤ gridTime sg0 vg2 Kf n (0 + 1) := by simpa [sg0] using hmem.1
  have hB4 := Bctl_le_four n (by linarith) hu10 hu1
  have hB0 : 0 ≤ sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1)) := (STBctl_pos sz0 n (by linarith)).le
  have hη2 : (1 / 2 : ℝ) ≤ etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) := by
    change (1 / 2 : ℝ) ≤ etaT 0 _
    rw [etaT_zero]; linarith
  have hMee : (fun _ : ℕ => (4 : ℝ)) n * ((fun _ : ℕ => (4 : ℝ)) n * (fun _ : ℕ => (100 : ℝ)) n) *
      ((sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1))) +
        ((sz0.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
    have h1 : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) ≤ 4 ^ (2 * (2 + 1 + 1)) :=
      pow_le_pow_left₀ hB0 hB4 _
    have h2 : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) ≤ 4 ^ (2 * (2 + 1 + 1)) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hη2
    have h3 : ((sz0.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
    have h2' : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) ≤ 131072 :=
      h2.trans (by norm_num)
    have h17' : (410338673 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      have : (17 : ℝ) ^ 7 = 410338673 := by norm_num
      linarith
    rw [h7]
    have h4 := mul_le_mul_of_nonneg_left h2' (by norm_num : (0 : ℝ) ≤ 4 * (4 * 100))
    change 4 * (4 * 100) * _ + _ ≤ _
    linarith
  have hwL := hwL_gen n
  have hWt := hWt_gen n hW2
  have hκm : (1 : ℝ) ≤ (mE ((fun _ : ℕ => (0 : ℝ)) n)).im := by
    change (1 : ℝ) ≤ (mE 0).im
    rw [mE_zero_im]
  have hϑ := QopAlgebra_mollifier_props 3 (sz0.L n) (2 + 1) (sz0.three_le_L n) (lam_pos_n n)
  have hD : ((2 + 1 : ℕ) : ℝ) + 2 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) < D'' + 1 := by
    rw [hD''def, ← hCQdef]; push_cast; linarith
  have hHerm : (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ).IsHermitian :=
    Matrix.isHermitian_zero
  have hzero : (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n 0) (2 + 1 + 1)
        ((fun _ : ℕ => (4 : ℝ)) n) ((fun _ : ℕ => (100 : ℝ)) n) ((fun _ : ℕ => (1 : ℝ)) n) (1 / 10)
        (D'' + 1 + 1) := by
    rw [ST_gridTime_zero]
    exact zero_mem_inst n (lam_le_one n) (1 / 10) (D'' + 1 + 1)
  clear_value Kf CK W₀ D'' CQ
  refine ⟨Kf, n, hK0 n, hΔ, fun a => ?_, fun a => ?_⟩
  · exact hQ_altQN (m := 2) 1 1 2 Cm2 (1 / 2) (by norm_num) one_pos one_pos two_pos (by positivity)
      (by norm_num) sz0 (fun _ => (0 : ℝ)) sg0 vg2 Kf n (hEn n) (hs0 n) (hsv n) (hv1 n) hwL hWt hκm
      (lam_pos_n n) (lam_le_one n) (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 7) (D' := D'' + 1 + 1) (D'' := D'')
      (by linarith) (by norm_num) (by norm_num) hWε hlog hLK hdW (by norm_num) hD (hW₀def.symm.trans_le hW0W)
      hϑ (σ := σalt) (fun _ => 4) (fun _ => 100) (fun _ => 1) 1 (Nat.one_le_iff_ne_zero.2 (hK0 n)) a 0
      (by norm_num) hMee hδ0 0 hzero hHerm
  · exact subGaussStop_altQN (m := 2) 1 1 2 (by norm_num) one_pos one_pos two_pos sz0 (E := fun _ => (0 : ℝ))
      (s := sg0) (v := vg2) (K := Kf) hEn hs0 hsv hv1 n hwL hWt hκm (lam_pos_n n) (lam_le_one n)
      (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 7) (D' := D'' + 1 + 1) (D'' := D'') (by linarith) (by norm_num)
      (by norm_num) hWε hlog hLK hdW (by norm_num) hD (hW₀def.symm.trans_le hW0W) (σ := σalt)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1)
      (fun _ => 4) 1 (Nat.one_le_iff_ne_zero.2 (hK0 n)) a 0 (by norm_num) hMee hδ0

/-! ### Instance 5: the kernel field (C3) and the drift/class fields (C4) -/

/-- **Instance of C3** (`alt_hkerGridQN`) at `n = 4`, `m = 2`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `Λ_g = κ' = 1`,
`K_L = 2`, `ε = 1/5`, `ε' = 1/10`, `D_c = 2`, the alternating `σ`, at `i = 0`, `m' = 1` and the zero tensor in the class:
every deterministic hypothesis (regime `v ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-v)/(1-s)`, the window `4 ≤ W^ε`, `log L ≤ W^ε`,
`L^3 ≤ W^{K_L}`, `d W^{ε'} ≤ W^ε`) is discharged. -/
theorem alt_hkerGridQN_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖Ugen 3 (sz0.L 4) (sz0.lam 4) ((fun _ : ℕ => (0 : ℝ)) 4) σalt (gridTime sg0 vg2 (fun _ => 4) 4 0)
        (gridTime sg0 vg2 (fun _ => 4) 4 1) (fun _ => 0) a‖ ≤
      kappaAltQN 3 (2 + 1 + 1) 1 1 2 (sz0.lam 4) ((sz0.W 4 : ℕ) : ℝ) (1 / 5)
          (gridTime sg0 vg2 (fun _ => 4) 4) 0 1 * 0 +
        epsAltQN 3 (2 + 1 + 1) 1 1 2 ((sz0.W 4 : ℕ) : ℝ) 0 1 * 0 := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  have hW2' : (2 : ℝ) ≤ ((sz0.W 4 : ℕ) : ℝ) := by rw [W4]; norm_num
  have hκm : (1 : ℝ) ≤ (mE ((fun _ : ℕ => (0 : ℝ)) 4)).im := by
    change (1 : ℝ) ≤ (mE 0).im
    rw [mE_zero_im]
  refine alt_hkerGridQN (m := 2) 1 1 2 (by norm_num) one_pos one_pos two_pos sz0 (fun _ => (0 : ℝ)) sg0 vg2
    (fun _ => 4) 4 le_rfl (by norm_num [sg0, vg2]) (by norm_num) (by norm_num) hκm (lam_pos_n 4) (lam_le_one 4)
    (ε := 1 / 5) (ε' := 1 / 10) (Dc := 2) hW (by norm_num) (by norm_num) hWε hlog hLK hdW (by norm_num)
    (hwL_gen 4) (hWt_gen 4 hW2') σalt 0 1 (by norm_num) (by norm_num) (fun _ => 0) 0 0 le_rfl le_rfl
    (fun _ => by simp) ⟨fun _ _ _ => by simp, by positivity, fun _ _ => by simp⟩ a

/-- **Instance of C4a** (`alt_hdriftGridQN`) on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `n = 4`, `m = 2`,
the alternating `σ`, levels `(Γ, Λ, Φc) = (4, 100, 1)`, `(Φ₁, Φ₂, Φ₃) = (1, 16, 1)`, `Y_l = 4`, the exit time
`altExitTauN` (`0 < τ ω` for every `ω`: `H_0 = 0` is in the three sets, `zero_lt_exitTau`), every path `ω`, `j = 0` and every
label: the three components of `mem_of_lt_altExitTauN` supply `hτG` and `hY`. -/
theorem alt_hdriftGridQN_instance :
    ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)),
      0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω ∧
      ‖dGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω b‖ ≤
        dDriftAltLinQN sz0 4 0 (gridTime sg0 vg2 (fun _ => 4) 4 0) 2 4 1 Φ2v 1
          (qProxyCn 3 (2 + 1) 1 2 Cm2 (1 / 2)) (1 / 5) 40 2 1 := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  intro ω b
  have hpos : 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4)
      (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω := by
    refine zero_lt_exitTau (by norm_num) ?_
    rw [azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ 4 rfl ω, ST_gridTime_zero]
    exact zero_mem_G0 4 (1 / 10) 40
  refine ⟨hpos, alt_hdriftGridQN 3 2 1 2 (le_refl 3) one_pos (by norm_num) sz0 4 σalt (fun _ => (0 : ℝ)) sg0 vg2
    (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4)
    1 (1 / 10) (1 / 5) 40 (((sz0.W 4 : ℕ) : ℝ)) 1 2 one_pos (by norm_num) (lam_pos_n 4) (lam_le_one 4) le_rfl
    (by norm_num) (by norm_num) (by rw [N4]; norm_num) hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hWε hLK hdW (by linarith) le_rfl (by rw [W10_4, sqrt10_pow6, W4]; norm_num)
    (by rw [W4, N4]; norm_num) hFv4 (by rw [W4, N4, Real.rpow_two, Real.sqrt_one]; norm_num)
    (by rw [W4]; norm_num) σalt_last ω 0 (by norm_num) hpos b⟩

/-- **Instance of C4b** (`alt_hA0clsGridQN`): `m = 2`, `K_L = 2`, `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 6`, `D_c = 3`,
the exit family at `(Γ, Λ, Φc, Φ₁, Φ₂, Φ₃, Y_l) = (4, 100, 1, 1, 16, 1, 4)`, at an `n` with `W_n ≥ W₀`; for every path
`ω`, `0 < τ ω` and the initial `𝒬`-process is in the class `altClsQN … 0` with `δ_0 = 2 W^{-6}`; the crude sup of the
premise is derived from the Hermitian component and the `𝒦` envelope (`altEnd_crudeSup`, `crude_u`). -/
theorem alt_hA0clsGridQN_instance :
    ∃ n : ℕ, ∀ ω : PathΩ sz0,
      0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω ∧
      altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime sg0 vg2 (fun _ => 4) n) 0
        (2 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (aTrueQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) n
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt 0 ω) := by
  set WQ : ℝ := QDriftA_W0 3 (2 + 1) 2 Cm2 (1 / 2) 7 (1 / 5) 6 with hWQ
  obtain ⟨n, hx, hn1⟩ := inst_data2 WQ
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hWQ' : WQ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  refine ⟨n, fun ω => ?_⟩
  have hpos : 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4)
      (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω := by
    refine zero_lt_exitTau (by norm_num) ?_
    rw [azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ n rfl ω, ST_gridTime_zero]
    exact zero_mem_G0 n (1 / 10) 6
  refine ⟨hpos, alt_hA0clsGridQN sz0 (le_refl 3) 2 2 7 (1 / 5) 6 (by norm_num) σalt (fun _ => (0 : ℝ)) sg0 vg2
    (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4)
    (1 / 10) 3 hWQ' hLK hdW ?_ (lam_pos_n n) le_rfl (by norm_num) ?_ ω hpos⟩
  · have h6 := hDD_inst (show (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) by linarith)
    have h0 : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (by linarith) _
    linarith
  · intro ω' hω'
    have hH := (mem_of_lt_altExitTauN hω').1.1.1
    have hu0 : 0 ≤ gridTime sg0 vg2 (fun _ => 4) n 0 := by rw [ST_gridTime_zero]
    have hu : gridTime sg0 vg2 (fun _ => 4) n 0 ≤ 1 / 2 := by rw [ST_gridTime_zero]; norm_num [sg0]
    exact crude_u n hW17 hn1 hu0 hu hH σalt

/-- **Instance of C4c** (`alt_hDclsGridQN`): the data of C4b with `D' = 6`, `D_c = 3`; for every path `ω` and every
`j < 4` with `j < altExitTauN ω`, the drift `dGridQN … j ω` is in the class `altClsQN … (j + 1)` with `δ_D = 4 W^{-6}`.  The
two crude sups of the premises are derived for every grid time from the exit-family membership (`altEnd_crudeSup` with the
`𝒦` envelope, and `altEnd_driftSup` with `dDriftLinN ≤ 4^2·(4^4·2)·19 ≤ W^7`). -/
theorem alt_hDclsGridQN_instance :
    ∃ n : ℕ, (∀ ω : PathΩ sz0,
      0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω) ∧
      ∀ (ω : PathΩ sz0) (j : ℕ), j < 4 →
        j < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
          (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω →
        altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime sg0 vg2 (fun _ => 4) n) (j + 1)
          (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
          (dGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) n
            (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt j ω) := by
  obtain ⟨W₀, hW₀, H⟩ := alt_hDclsGridQN 3 2 1 2 7 (1 / 5) 6 (le_refl 3) one_pos (by norm_num)
  obtain ⟨n, hx, hn1⟩ := inst_data2 W₀
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hpos : ∀ ω : PathΩ sz0, 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n
      ω := fun ω => by
    refine zero_lt_exitTau (by norm_num) ?_
    rw [azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ n rfl ω, ST_gridTime_zero]
    exact zero_mem_G0 n (1 / 10) 6
  refine ⟨n, hpos, fun ω j hj hjτ => ?_⟩
  have hu0 : ∀ i, 0 ≤ gridTime sg0 vg2 (fun _ => 4) n i := fun i =>
    altEnd_gridTime_nonneg (le_rfl : (0 : ℝ) ≤ sg0 n) (by norm_num [sg0, vg2]) i
  have hu : ∀ i ≤ 4, gridTime sg0 vg2 (fun _ => 4) n i ≤ 1 / 2 := fun i hi => by
    have := altEnd_gridTime_le (s := sg0) (v := vg2) (K := fun _ => 4) (n := n) (by norm_num [sg0, vg2])
      (by norm_num) hi
    simpa [vg2] using this
  refine H sz0 n σalt (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 3 (by norm_num) (lam_pos_n n) (lam_le_one n)
    hW0W hLK le_rfl (by norm_num [sg0, vg2]) (by norm_num [vg2])
    (by
      change (1 - (1 / 2 : ℝ))⁻¹ ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ)
      have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
      rw [h2, Real.rpow_two]
      nlinarith)
    hdW (hDD_inst (by linarith)) ?_ ?_ ω j hj hjτ
  · intro ω' j' hj' hjτ'
    exact crude_u n hW17 hn1 (hu0 j') (hu j' (by omega)) (mem_of_lt_altExitTauN hjτ').1.1.1 σalt
  · intro ω' j' hj' hjτ'
    have hB4 := Bctl_le_four n (by linarith) (hu0 j') (hu j' (by omega))
    have hB0 : 0 ≤ sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j') :=
      (STBctl_pos sz0 n (by have := hu j' (by omega); linarith)).le
    have hη2 : (1 / 2 : ℝ) ≤ etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 (fun _ => 4) n j') := by
      change (1 / 2 : ℝ) ≤ etaT 0 _
      rw [etaT_zero]; have := hu j' (by omega); linarith
    have h1 : (sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) ≤ 4 ^ (2 + 1 + 1) :=
      pow_le_pow_left₀ hB0 hB4 _
    have h2 : (sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 (fun _ => 4) n j') ≤ 4 ^ (2 + 1 + 1) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hη2
    have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hW17 7
    have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    refine altEnd_driftSup sz0 n (by norm_num) (mem_of_lt_altExitTauN hjτ').1.2 ?_ σalt
    unfold dDriftLinN
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 4 * 4)
    have h4 : (17 : ℝ) ^ 7 = 410338673 := by norm_num
    rw [h7]
    change (4 : ℝ) * 4 * (_ / _) * ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) ≤ _
    have e : ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) = 19 := by
      unfold Φ2v; norm_num
    rw [e]
    have h5 : (4 : ℝ) * 4 * ((sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 (fun _ => 4) n j')) ≤ 4 * 4 * (4 ^ (2 + 1 + 1) / (1 / 2)) := h3
    norm_num at h5
    nlinarith

/-! ### Instance 6: the identity, measurability, terminal value, de-`𝒬` and the `Y` moments (C5), and `altExitMeasN` -/

/-- **Instance of `altExitMeasN`** at the data of C4a: `{0 < altExitTauN}` is `filt 0`-measurable. -/
theorem altExitMeasN_instance :
    MeasurableSet[filt sz0 0] {ω | 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω} :=
  altExitMeasN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 (2 + 1 + 1) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 0

/-- **Instance of C5a** (`altEnd_hexp`) at `n = 4`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, the explicit mollifier, the
alternating `σ` and the stopping index `τ ≡ 1`: for every target `m' ≤ 4`, a.e., the frozen `𝒬`-process is the Duhamel
expansion (the field `hexp` of `GridAssemblyHypN`). -/
theorem altEnd_hexp_instance :
    ∀ m' ≤ 4, ∀ᵐ ω ∂(pathP sz0),
      aFrozQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt (fun _ => 1) m' ω =
        Ugen 3 (sz0.L 4) (sz0.lam 4) ((fun _ : ℕ => (0 : ℝ)) 4) σalt (gridTime sg0 vg2 (fun _ => 4) 4 0)
            (gridTime sg0 vg2 (fun _ => 4) 4 m')
            (aTrueQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
              (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω) +
          ∑ j ∈ Finset.range (min m' ((fun _ : PathΩ sz0 => 1) ω)),
            Ugen 3 (sz0.L 4) (sz0.lam 4) ((fun _ : ℕ => (0 : ℝ)) 4) σalt (gridTime sg0 vg2 (fun _ => 4) 4 (j + 1))
              (gridTime sg0 vg2 (fun _ => 4) 4 m')
              ((gridStep sg0 vg2 (fun _ => 4) 4 : ℂ) • dGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt j ω +
                zVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 j
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω +
                yVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 j
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω +
                rGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt j ω) :=
  altEnd_hexp sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 (by norm_num) le_rfl (by norm_num [sg0, vg2])
    (by norm_num [vg2]) (by norm_num) _ σalt (fun _ => 1)

/-- **Instance of C5b** (`altEnd_stronglyMeasurable_zVecQN`) at the same data, `j = 0`. -/
theorem altEnd_stronglyMeasurable_zVecQN_instance :
    StronglyMeasurable[filt sz0 (0 + 1)] (fun ω => zVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 0
      (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω) :=
  altEnd_stronglyMeasurable_zVecQN sz0 _ _ _ _ 4 0 _ σalt

/-- **Instance of C5c** (`altEnd_aFroz_eq_aTrue`) at the same data and `τ ≡ 4 = K n`: for every path, the frozen and the
true `𝒬`-processes agree at the last grid index. -/
theorem altEnd_aFroz_eq_aTrue_instance (ω : PathΩ sz0) :
    aFrozQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
        (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt (fun _ => 4) 4 ω =
      aTrueQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
        (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 4 ω :=
  altEnd_aFroz_eq_aTrue sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 (by norm_num) le_rfl
    (by norm_num [sg0, vg2]) (by norm_num [vg2]) (by norm_num) _ σalt (fun _ => 4) ω le_rfl

/-- **Instance of C5d** (`altEnd_unQ`) at `n = 4`, `m = 2`, `E = 0`, `u = 0`, `H = 0 ∈ GoodSetN` at `(4, 100, 1)`, `κ = 1`,
`τ' = 1/10`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, the explicit mollifier, the alternating `σ` and every label:
`‖(𝓛-𝒦)_{0,σ}(0)_a‖ ≤ ‖𝒬_0(𝓛-𝒦)_{0,σ}(0)_a‖ + N² B_0^{4}`.  The level `hY` is the one of `goodSetN_LKM_le`. -/
theorem altEnd_unQ_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖sz0.STLKM 4 0 0 H0 σalt a‖ ≤
      ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) 0
          (fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4) => sz0.STLKM 4 0 0 H0 σalt b) a‖ +
        ((sz0.size 4 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 4 0 ^ (2 + 2) * 1) := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  exact altEnd_unQ (le_refl 3) 2 sz0 4 0 0 1 4 100 1 (1 / 10) 40 (((sz0.W 4 : ℕ) : ℝ)) 1 2 Cm2 (1 / 2) H0 σalt
    (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) one_pos (by norm_num) le_rfl (by norm_num)
    (lam_pos_n 4) hNu4 hW (by norm_num) (by rw [W4]; norm_num) le_rfl
    (by rw [W10_4, sqrt10_pow6, W4]; norm_num) (by rw [W4, N4]; norm_num) hFv4 (by positivity)
    (by norm_num) hMΛ4 (QopAlgebra_mollifier_props 3 (sz0.L 4) (2 + 1) (sz0.three_le_L 4) (lam_pos_n 4))
    (zero_mem_inst 4 (lam_le_one 4) _ _) hY4 σalt_last a

/-- **Instance of C5e** (`altEnd_yMomentsMax`) at `sz0` (`SizeTendsto` by `sz0_tendsto`, `RangeCond (1/2) v` by
`rangeCond_half`, `0 < lam n` for every `n`), `m = 2`, `κ = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, the grid `K ≡ 4`, the
alternating `σ`: one `C_P` and, at some `n`, a level `P ≤ N^{C_P}` for which the `Y` moments of `yVecQN` hold for the
stopping index `τ ≡ 1` (`YMomentBoundsN` with `v_j = Δ² P`, `w_j = Δ⁴ P²`). -/
theorem altEnd_yMomentsMax_instance :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      YMomentBoundsN sz0 ((fun _ : ℕ => (0 : ℝ)) n) σalt (gridTime sg0 vg2 (fun _ => 4) n) (fun _ => 1) 4
        (fun j ω => yVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) n j
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt ω)
        (fun _ => gridStep sg0 vg2 (fun _ => 4) n ^ 2 * P) (fun _ => gridStep sg0 vg2 (fun _ => 4) n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, H⟩ := altEnd_yMomentsMax sz0 (κ := 1) (τR := 1 / 2) (E := fun _ => (0 : ℝ)) (s := sg0) (v := vg2)
    one_pos (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [sg0, vg2]) (fun _ => by norm_num [vg2])
    sz0_tendsto rangeCond_half lam_pos_n 2
  refine ⟨C_P, hC, ?_⟩
  obtain ⟨n, P, hP0, hPle, hτ⟩ := (H (fun _ => 4) (fun _ => by norm_num) σalt).exists
  exact ⟨n, P, hP0, hPle, hτ (fun _ => 1) (fun j => MeasurableSet.const _)⟩

end QEndAInst

end RBM.Ind

end

#print axioms RBM.Ind.altYSetN
#print axioms RBM.Ind.altExitTauN
#print axioms RBM.Ind.measurableAltYSetN
#print axioms RBM.Ind.mem_of_lt_altExitTauN
#print axioms RBM.Ind.altExitMeasN
#print axioms RBM.Ind.altYGridN
#print axioms RBM.Ind.gridDriftQN_envelope
#print axioms RBM.Ind.assembledRHSAltQN_qErr_le
#print axioms RBM.Ind.hQ_altQN
#print axioms RBM.Ind.subGaussStop_altQN
#print axioms RBM.Ind.alt_hkerGridQN
#print axioms RBM.Ind.alt_hdriftGridQN
#print axioms RBM.Ind.alt_hA0clsGridQN
#print axioms RBM.Ind.alt_hDclsGridQN
#print axioms RBM.Ind.altEnd_crudeSup
#print axioms RBM.Ind.altEnd_driftSup
#print axioms RBM.Ind.altEnd_hexp
#print axioms RBM.Ind.altEnd_stronglyMeasurable_zVecQN
#print axioms RBM.Ind.altEnd_aFroz_eq_aTrue
#print axioms RBM.Ind.altEnd_unQ
#print axioms RBM.Ind.altEnd_yMomentsMax
#print axioms RBM.Ind.QEndAInst.altYSetN_instance
#print axioms RBM.Ind.QEndAInst.altYGridN_instance
#print axioms RBM.Ind.QEndAInst.gridDriftQN_envelope_instance
#print axioms RBM.Ind.QEndAInst.assembledRHSAltQN_qErr_le_instance
#print axioms RBM.Ind.QEndAInst.hQ_altQN_subGaussStop_altQN_instance
#print axioms RBM.Ind.QEndAInst.alt_hkerGridQN_instance
#print axioms RBM.Ind.QEndAInst.alt_hdriftGridQN_instance
#print axioms RBM.Ind.QEndAInst.alt_hA0clsGridQN_instance
#print axioms RBM.Ind.QEndAInst.alt_hDclsGridQN_instance
#print axioms RBM.Ind.QEndAInst.altExitMeasN_instance
#print axioms RBM.Ind.QEndAInst.altEnd_hexp_instance
#print axioms RBM.Ind.QEndAInst.altEnd_stronglyMeasurable_zVecQN_instance
#print axioms RBM.Ind.QEndAInst.altEnd_aFroz_eq_aTrue_instance
#print axioms RBM.Ind.QEndAInst.altEnd_unQ_instance
#print axioms RBM.Ind.QEndAInst.altEnd_yMomentsMax_instance
