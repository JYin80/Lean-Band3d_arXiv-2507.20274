/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.DecayGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.Step2EventsGen
import RBM3D.Induction.GridGoodN

/-!
# The good set of the grid walk over the carrier

Generic forms of `Induction/GridGoodN` over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no
`BA/*` import:

* the matrix-level bounds `STmaxLMg`, `STmaxLKMg`, `STXiLKMg` with the lemmas `STmaxLKMg_Hf`,
  `STXiLKMg_Hf` to `STmaxLKg`, `STXiLKg` at the flow matrix (under the loop compatibility, derived from
  `StepDecompGen_LoopForm` and `Step34Gen_LCompat`);
* the good set `GoodSetNg`;
* the exit times `gridExitTauNg` and their lemmas, the matrix-level measurability `MeasurableGoodSetNg` /
  `measurableGoodSetNg` (from `StepDecompGen_LoopForm`);
* the statements `GridGoodNConclg`, `GridGoodNgL`, with the private core of the proof (the uniform good
  event and the grid transfer) and the public theorem `gridGoodNgL_of` (family form).  Its hypotheses are
  `StepDecompGen_LoopForm`, `Step2EventsGen_Law`, `Step34Gen_LCompat`, `DecayGen_Spec`, `Admissible`, the
  `≺` inputs, and, for the Hermitian clause of `GoodSetNg`, `StepDecompGen_WalkForm`.

Private band helpers are reused by `open private ... from RBM3D.Induction.GridGoodN`; the ones that read
`zt`, `STKloop`, `seqHflow` are copied.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private gridGood_firstHit_eq_of_below gridGood_measurableSet_forall gridGood_measurableSet_imp
  gridGood_whp_and gridGood_whp_forall_mem gridGood_sqrt_mul_le gridGood_pow_absorb gridGood_nat_mul_pow_le
  gridGood_mul_bound gridGood_D4_arith gridGood_D2_arith gridGood_far_exists gridGood_gridTime_mem
  from RBM3D.Induction.GridGoodN

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The matrix-level bounds -/

section Vocab

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- `max_{σ,a} |𝓛^{(k)}_{v,σ,a}(H)|` for a fine matrix `H` (band `STmaxLM`; `loopFine H (zt E v)` is `Cm.LM n v H`). -/
def STmaxLMg (n : ℕ) (v : ℝ) (k : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖Cm.LM n v H p.1 p.2‖)

/-- `max_{σ,a} |(𝓛 - 𝒦)^{(k)}_{v,σ,a}(H)|` (band `STmaxLKM`; `STKloop` is `Cm.K`). -/
def STmaxLKMg (n : ℕ) (v : ℝ) (k : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖Cm.LM n v H p.1 p.2 - Cm.K n v p.1 p.2‖)

/-- `Ξ̂^{(𝓛-𝒦)}_{v,k}(H)` (band `STXiLKM`). -/
def STXiLKMg (n : ℕ) (v : ℝ) (k : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  1 + STmaxLKMg Cm n v k H / (sz.Bctl n v) ^ k

variable {Cm}
  {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The LM compat: under `LoopForm` and `Step34Gen_LCompat`, the loop of the carrier at the flow matrix is the sample loop `Cm.L`
(`loopM_eq_loopL`; `KLloopOf σ a` is `loopOf σ a`). -/
theorem GridGoodGen_LM_eq_L {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (hC : Step34Gen_LCompat Cm Hf) (n : ℕ) (u : ℝ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Cm.LM n u (Hf n u ω) σ a = Cm.L n u σ a ω := by
  rw [hC n u σ a ω, (hL n).2.1 u _ k σ a, (hL n).2.2.1 u _ (KLloopOf d (sz.L n) σ a)]
  unfold loopFine
  exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a

/-- `STmaxLKMg` at the flow matrix is `STmaxLKg`. -/
theorem STmaxLKMg_Hf (hLM : ∀ (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ),
      Cm.LM n u (Hf n u ω) σ a = Cm.L n u σ a ω) (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    STmaxLKMg Cm n v k (Hf n v ω) = STmaxLKg Cm.toFlowFM n v k ω := by
  unfold STmaxLKMg STmaxLKg
  simp only [hLM]

/-- `STXiLKMg` at the flow matrix is `STXiLKg` (band `gridGood_STXiLKM_seqHflow`). -/
theorem STXiLKMg_Hf (hLM : ∀ (n : ℕ) (u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ),
      Cm.LM n u (Hf n u ω) σ a = Cm.L n u σ a ω) (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    STXiLKMg Cm n v k (Hf n v ω) = STXiLKg Cm.toFlowFM n v k ω := by
  unfold STXiLKMg STXiLKg
  rw [STmaxLKMg_Hf hLM]

end Vocab

/-! ## 2. The good set -/

section GoodSet

variable {d : ℕ} {sz : Sizes d}

/-- **`GoodSetNg`** (band `GoodSetN`): the good set of the grid walk at the
spectral time `u`, for the loop length `k`, over a carrier: `loopFine H (zt E u)` is `Cm.LM n u H`, `STKloop` is `Cm.K`, `etaT E u`
is `Cm.eta n u`; `ellT (sz.L n) (sz.lam n) u` and `sz.Bctl` stay (size level). -/
def GoodSetNg (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H.IsHermitian ∧
    (∀ m : ℕ, 1 ≤ m → m < k →
      1 + Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
          (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cm.LM n u H p.1 p.2 - Cm.K n u p.1 p.2‖) /
        (sz.Bctl n u) ^ m ≤ Γ * Φ) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖Cm.LM n u H σ a‖ + ‖Cm.LM n u H σ a - Cm.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKMg Cm n u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkMg Cm n u H (loopOf σ a)‖ ≤ Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtMg Cm n u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ‖STeeMg Cm n u H σ a a'‖ ≤ Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l (loopOf σ a)‖ +
          ‖STelklkMg Cm n u H (loopOf σ a)‖ + ‖STegtMg Cm n u H (loopOf σ a)‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append a a') : ℝ) →
        ‖STeeMg Cm n u H σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'))

end GoodSet

/-! ## 3. The exit times and measurability -/

section ExitTime

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)

/-- **`gridExitTauNg`** (band `gridExitTauN`): the exit time of the carrier walk `Cm.Hpath` from a family `G`
of matrix sets: the first `j ≤ K n` with `H_j ∉ G j`, and `K n` if there is none. -/
def gridExitTauNg (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) : PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) => (G j)ᶜ.indicator (fun _ => (1 : ℝ)) (Cm.Hpath s v K n j ω)) (1 / 2) (K n)

variable {Cm} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
  {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}

/-- `gridExitTauNg ≤ K n`. -/
theorem gridExitTauNg_le (ω : PathΩ sz) : gridExitTauNg Cm s v K n G ω ≤ K n :=
  firstHit_le _ _ _ ω

/-- Strictly before the exit, the carrier walk is in `G`. -/
theorem mem_of_lt_gridExitTauNg {ω : PathΩ sz} {j : ℕ} (h : j < gridExitTauNg Cm s v K n G ω) :
    Cm.Hpath s v K n j ω ∈ G j := by
  have h1 := lt_firstHit_imp _ _ _ h
  by_contra hmem
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h1
  norm_num at h1

/-- If the carrier walk stays in `G` up to `K n`, the exit time is `K n`. -/
theorem gridExitTauNg_eq_of_forall_mem {ω : PathΩ sz} (hgood : ∀ j ≤ K n, Cm.Hpath s v K n j ω ∈ G j) :
    gridExitTauNg Cm s v K n G ω = K n := by
  refine gridGood_firstHit_eq_of_below _ _ _ fun j hj => ?_
  have hnot : Cm.Hpath s v K n j ω ∉ (G j)ᶜ := fun hc => hc (hgood j hj)
  rw [Set.indicator_of_notMem hnot]
  norm_num

/-- Under `StepDecompGen_WalkForm` the carrier walk is adapted to the coordinate filtration (`pathH_measurable_filt`). -/
theorem GridGoodGen_Hpath_measurable_filt {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (j : ℕ) :
    Measurable[filt sz j] (fun ω : PathΩ sz => Cm.Hpath s v K n j ω) := by
  have hT : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Ψ n + H :=
    Measurable.of_eval_matrix _ fun i j => measurable_const.add ((measurable_pi_apply j).comp (measurable_pi_apply i))
  have h1 : (fun ω : PathΩ sz => Cm.Hpath s v K n j ω) = fun ω : PathΩ sz => Ψ n + StepDecompGen_pathH sz lam' s v K n j ω :=
    funext fun ω => hW.2.2 s v K n j ω
  rw [h1]
  exact hT.comp (pathH_measurable_filt (sz.withLam lam') s v K n j)

/-- `{j < gridExitTauNg}` is `filt sz j`-measurable when every `G j` is measurable and the walk has the property `StepDecompGen_WalkForm`. -/
theorem gridExitTauNg_measurableSet {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hW : StepDecompGen_WalkForm Cm lam' Ψ) (hG : ∀ j, MeasurableSet (G j)) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < gridExitTauNg Cm s v K n G ω} :=
  lt_firstHit_measurableSet (ℱ := filt sz)
    (fun j (ω : PathΩ sz) => (G j)ᶜ.indicator (fun _ => (1 : ℝ)) (Cm.Hpath s v K n j ω)) (1 / 2) (K n)
    (fun j => ((measurable_const.indicator (hG j).compl).comp (GridGoodGen_Hpath_measurable_filt hW j))) j

end ExitTime

section MeasurableProof

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {n : ℕ} {u : ℝ}

/-- **`MeasurableGoodSetNg`** (band `MeasurableGoodSetN`, per carrier): `GoodSetNg` is a measurable set of
matrices, for every index, time, loop length, levels and exponents. -/
def MeasurableGoodSetNg (Cm : Step2Mat sz) : Prop :=
  ∀ (n : ℕ) (u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ), MeasurableSet {H | GoodSetNg Cm n u k Γ Λ Φ τ' D' H}

private theorem GridGoodGen_meas_LKIM
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STLKIMg Cm n u H I :=
  (hLIM I).sub_const _

private theorem GridGoodGen_meas_STmaxLKMg
    (hLM : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Cm.LM n u H σ a) (k : ℕ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STmaxLKMg Cm n u k H := by
  have h : (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STmaxLKMg Cm n u k H) =
      Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖Cm.LM n u H p.1 p.2 - Cm.K n u p.1 p.2‖) := by
    funext H
    rw [Finset.sup'_apply (C := fun _ => ℝ)]
    rfl
  rw [h]
  exact Finset.measurable_sup' _ fun p _ => ((hLM k p.1 p.2).sub_const _).norm

private theorem GridGoodGen_meas_STXiLKMg
    (hLM : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Cm.LM n u H σ a) (m : ℕ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STXiLKMg Cm n u m H := by
  unfold STXiLKMg
  exact measurable_const.add ((GridGoodGen_meas_STmaxLKMg hLM m).div_const _)

private theorem GridGoodGen_meas_STksimLKMg
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STksimLKMg Cm n u H l I := by
  unfold STksimLKMg
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (MeasurableSet.const _)
      (((GridGoodGen_meas_LKIM hLIM _).mul_const _).mul_const _) measurable_const
  · exact Measurable.ite (MeasurableSet.const _)
      ((measurable_const.mul_const _).mul (GridGoodGen_meas_LKIM hLIM _)) measurable_const

private theorem GridGoodGen_meas_STksimLKMg_sum
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) (k : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l I :=
  Finset.measurable_sum _ fun l _ => GridGoodGen_meas_STksimLKMg hLIM l I

private theorem GridGoodGen_meas_STelklkMg
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STelklkMg Cm n u H I := by
  unfold STelklkMg
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((GridGoodGen_meas_LKIM hLIM _).mul_const _).mul (GridGoodGen_meas_LKIM hLIM _)

private theorem GridGoodGen_meas_STavgErrMg
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) (σ : Bool) (a : Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STavgErrMg Cm n u H σ a := by
  unfold STavgErrMg
  exact (hLIM _).sub_const _

private theorem GridGoodGen_meas_STegtMg
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STegtMg Cm n u H I := by
  unfold STegtMg
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((GridGoodGen_meas_STavgErrMg hLIM _ a).mul_const _).mul (hLIM _)

private theorem GridGoodGen_meas_STeeMg
    (hLIM : ∀ I : LoopIdx (Zd d (sz.L n)), Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      Cm.LIM n u H I) {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => STeeMg Cm n u H σ a a' := by
  unfold STeeMg
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun b _ => Finset.measurable_sum _ fun b' _ => ?_)
  exact measurable_const.mul (hLIM _)

/-- **The measurability of `Cm.LM`, `Cm.LIM` in the matrix follows from `StepDecompGen_LoopForm`** (no separate compatibility). -/
theorem GridGoodGen_meas_of_loopForm {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (u : ℝ) :
    (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Cm.LM n u H σ a) ∧
    ∀ I : LoopIdx (Zd d (sz.L n)),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => Cm.LIM n u H I := by
  refine ⟨fun k σ a => ?_, fun I => ?_⟩
  · simp only [(hL n).2.1 u _ k σ a]
    exact walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (Cm.m n) (E n) u) σ a
  · simp only [(hL n).2.2.1 u _ I]
    exact (walk_measurable_loopL d (sz.L n) (sz.W n) (ztOf (Cm.m n) (E n) u) I).comp
      (walk_measurable_blockMat d (sz.L n) (sz.W n))

/-- **`measurableGoodSetNg`** (band `measurableGoodSetN`): `GoodSetNg` is a measurable set of matrices
under `StepDecompGen_LoopForm` (a finite conjunction, over finitely many labels, of inequalities between measurable functions of `H` and the
closed set `H.IsHermitian`). -/
theorem measurableGoodSetNg {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) : MeasurableGoodSetNg Cm := by
  intro n u k Γ Λ Φ τ' D'
  obtain ⟨hLM, hLIM⟩ := GridGoodGen_meas_of_loopForm hL n u
  have hH : MeasurableSet
      {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | H.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  unfold GoodSetNg
  simp only [Set.ofPred_and]
  refine hH.inter (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ ?_)))))))
  · exact gridGood_measurableSet_forall fun m => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ =>
        measurableSet_le (GridGoodGen_meas_STXiLKMg hLM m) measurable_const
  · exact gridGood_measurableSet_forall fun j => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ => gridGood_measurableSet_forall fun σ =>
        gridGood_measurableSet_forall fun a => gridGood_measurableSet_imp fun _ =>
          measurableSet_le (((hLM j σ a).norm).add ((hLM j σ a).sub_const _).norm) measurable_const
  · exact gridGood_measurableSet_forall fun l => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ => gridGood_measurableSet_forall fun σ =>
        gridGood_measurableSet_forall fun a =>
          measurableSet_le (GridGoodGen_meas_STksimLKMg hLIM l (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      measurableSet_le (GridGoodGen_meas_STelklkMg hLIM (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      measurableSet_le (GridGoodGen_meas_STegtMg hLIM (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      gridGood_measurableSet_forall fun a' =>
        measurableSet_le (GridGoodGen_meas_STeeMg hLIM σ a a').norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      gridGood_measurableSet_imp fun _ =>
        measurableSet_le (((GridGoodGen_meas_STksimLKMg_sum hLIM k (loopOf σ a)).norm.add
          (GridGoodGen_meas_STelklkMg hLIM (loopOf σ a)).norm).add
            (GridGoodGen_meas_STegtMg hLIM (loopOf σ a)).norm) measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      gridGood_measurableSet_forall fun a' => gridGood_measurableSet_imp fun _ =>
        measurableSet_le (GridGoodGen_meas_STeeMg hLIM σ a a').norm measurable_const

end MeasurableProof

/-! ## 4. The statement `GridGoodNgL` over a carrier -/

section Pin

variable {d : ℕ} {sz : Sizes d}

/-- **The conclusion `GridGoodNConclg`** (band `GridGoodNConcl`) over `(Cm, μ)`:
`Prec sz` is `PrecL sz μ`, `STXiL`/`STXiLK` are `STXiLg`/`STXiLKg`, `pathP`/`pathH` are `Cm.Pp`/`Cm.Hpath`, `GoodSetN` is
`GoodSetNg`. -/
def GridGoodNConclg (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 1 ≤ Λ n) → (∀ n, 1 ≤ Φ n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      PrecL sz μ (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    ∀ q : ℕ, 1 ≤ q →
    PrecL sz μ (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) (2 * k - 1) ω *
        (STXiLg Cm.toFlowFM n (u : ℝ) (4 * q) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (q : ℝ))))
      (fun n _ _ => Λ n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
      HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
        GoodSetNg Cm n (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'
          (Cm.Hpath s v K n j ω)})

end Pin

/-- **The statement `GridGoodNgL`** (band `GridGoodN`): `STIngRgL d STAny` over a carrier family
`(law, Flow, mkM, T0)` (`mkM` valued in `Step2Mat`) with the conclusion `GridGoodNConclg`. -/
def GridGoodNgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STAny law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => GridGoodNConclg (mkM sz z) (law sz) s t)

/-! ## 4a. The uniform good event and the grid transfer (private core)

The proofs below are the ports of `gridGood_whp_uniform` and `gridGood_grid`.  They are private; the public theorem `gridGoodNgL_of` of §4b
uses them.  The Hermitian clause of `GoodSetNg` is not derived from `StepDecompGen_LoopForm`, `Step2EventsGen_Law`,
`Step34Gen_LCompat` or the `≺` inputs (none of them mentions a Hermitian matrix), so the uniform event is
stated for the Hermitian flow matrices, `H.IsHermitian → GoodSetNg … H`, and the grid transfer takes the
walk to be `Cm.Pp`-a.s. Hermitian as a hypothesis; §4b gets that hypothesis from `StepDecompGen_WalkForm`. -/

section Core

variable {d : ℕ} {sz : Sizes d}

/-- `ξ ≺ ζ` at the law `μ` gives the event of high probability `{∀ u, ξ ≤ N^τ ζ}` (band `Prec.whp`). -/
private theorem GridGoodGen_precL_whp {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt μ sz.size (fun n => {ω | ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (le_of_eq ?_) hn
  congr 1
  ext ω
  simp [badSetAt]

private theorem GridGoodGen_one_le_STXiLg (C : FlowFM sz) {n : ℕ} {v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiLg C n v k ω := by
  unfold STXiLg STmaxLg
  have h0 : 0 ≤ Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
      (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n v p.1 p.2 ω‖) :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖C.L n v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

private theorem GridGoodGen_one_le_STXiLKg (C : FlowFM sz) {n : ℕ} {v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiLKg C n v k ω := by
  unfold STXiLKg STmaxLKg
  have h0 : 0 ≤ Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
      (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n v p.1 p.2 ω - C.K n v p.1 p.2‖) :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖C.L n v p.1 p.2 ω - C.K n v p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB k).le
  linarith

/-- **The uniform good event** (band `gridGood_whp_uniform`): from the hypotheses of `GridGoodNConclg`, the four `lem:SEforLn`
estimates `STSEforLnConclgL`, the loop decay `STDecayLoopUgL` and the four `ℰ`-term label decays, with high probability
`Hf n u ω ∈ GoodSetNg … u` for every `u ∈ [s_n,t_n]` at once, for the Hermitian flow matrices (the Hermitian clause is not read). -/
private theorem GridGoodGen_whp_uniform {Cm : Step2Mat sz} {E : ℕ → ℝ} {μ : Measure sz.SeqΩ}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hC : Step34Gen_LCompat Cm Hf) {κm 𝔠 𝔡 : ℝ}
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1)
    (hSE : STSEforLnConclgL Cm Hf μ s t) (hU : STDecayLoopUgL Cm.toFlowFM μ s t)
    {k : ℕ} (hk : 2 ≤ k)
    (hEK : ∀ σ : Fin k → Bool,
      STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
        STegtg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
      (∀ l : ℕ, STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
        STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
        STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
      STEKDecaygL μ s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
        STeeg Cm Hf n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    {Λ Φ : ℕ → ℝ} (hΦ : ∀ n, 1 ≤ Φ n)
    (hX : ∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      PrecL sz μ (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φ n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φ n))
    {q : ℕ} (hq : 1 ≤ q)
    (hQ : PrecL sz μ (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) (2 * k - 1) ω *
        (STXiLg Cm.toFlowFM n (u : ℝ) (4 * q) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (q : ℝ))))
      (fun n _ _ => Λ n))
    {ε : ℝ} (hε : 0 < ε) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    HighProbAt μ sz.size (fun n => {ω | ∀ u : TimeIcc s t n, (Hf n (u : ℝ) ω).IsHermitian →
      GoodSetNg Cm n (u : ℝ) k (((sz.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D' (Hf n (u : ℝ) ω)}) := by
  obtain ⟨h𝔠, h𝔡, hN, hBw, hWO⟩ := id hA
  have hsz : Tendsto sz.size atTop atTop := tendsto_size sz hN
  have hLM := GridGoodGen_LM_eq_L hL hC
  -- positivity of the scales on the window
  have hpos : ∀ n (u : TimeIcc s t n), 0 < sz.Bctl n (u : ℝ) ∧ 0 < Cm.eta n (u : ℝ) := by
    intro n u
    have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (ht1 n)
    refine ⟨st_Bctl_pos sz hu1, ?_⟩
    rw [hspec.2.2 n]
    exact mul_pos (by linarith) (hspec.1.trans_le (hspec.2.1 n))
  -- the w.h.p. events
  have wY := gridGood_whp_forall_mem hsz (Finset.Icc 1 k) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact GridGoodGen_precL_whp (hY m hm.1 hm.2) hε)
  have wX := gridGood_whp_forall_mem hsz (Finset.Icc 1 (k + 1)) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact GridGoodGen_precL_whp (hX m hm.1 hm.2) hε)
  have wQ := GridGoodGen_precL_whp hQ hε
  have wDec := gridGood_whp_forall_mem hsz (Finset.Icc 1 (2 * k + 2)) (fun j hj => by
    rw [Finset.mem_Icc] at hj
    exact GridGoodGen_precL_whp (hU j hj.1 τ' (D' + 1) hτ' (by linarith)) h𝔠)
  have hSE' := hSE k hk
  have wD3 := GridGoodGen_precL_whp hSE'.1 hε
  have wD1 := gridGood_whp_forall_mem hsz (Finset.Icc 3 k) (fun l hl => by
    rw [Finset.mem_Icc] at hl
    exact GridGoodGen_precL_whp (hSE'.2.1 l hl.1 hl.2) hε)
  have wD2 := GridGoodGen_precL_whp hSE'.2.2.1 hε
  have wD4 := GridGoodGen_precL_whp (hSE'.2.2.2 q hq) hε
  have wEgt := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    (hEK σ).1 τ' (D' + 1) hτ' (by linarith))
  have wKs := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    gridGood_whp_forall_mem hsz (Finset.Icc 3 k) (fun l _ =>
      (hEK σ).2.1 l τ' (D' + 1) hτ' (by linarith)))
  have wEl := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    (hEK σ).2.2.1 τ' (D' + 1) hτ' (by linarith))
  have wEe := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    (hEK σ).2.2.2 τ' D' hτ' hD')
  have wAll := gridGood_whp_and hsz wY (gridGood_whp_and hsz wX (gridGood_whp_and hsz wQ
    (gridGood_whp_and hsz wDec (gridGood_whp_and hsz wD1 (gridGood_whp_and hsz wD2
    (gridGood_whp_and hsz wD3 (gridGood_whp_and hsz wD4 (gridGood_whp_and hsz wEgt
    (gridGood_whp_and hsz wKs (gridGood_whp_and hsz wEl wEe))))))))))
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hBw h1
  refine wAll.mono ?_
  filter_upwards [hB1, hBw, hWt.eventually_ge_atTop (k : ℝ)] with n hB1n hbwn hWk
  intro ω hω u hherm
  obtain ⟨hY', hX', hQ', hDec', hD1', hD2', hD3', hD4', hEgt', hKs', hEl', hEe'⟩ := hω
  have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (ht1 n)
  obtain ⟨hBpos, hηpos⟩ := hpos n u
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hΓ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hΓ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε := by linarith
  have hBk : 0 ≤ (sz.Bctl n (u : ℝ)) ^ k / Cm.eta n (u : ℝ) := by positivity
  have hB6 : (sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) ≤ 1 :=
    Real.rpow_le_one hBpos.le (hB1n (u : ℝ) u.2.2) (by norm_num)
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hYb : ∀ m, 1 ≤ m → m ≤ k →
      0 ≤ STXiLKg Cm.toFlowFM n (u : ℝ) m ω ∧
        STXiLKg Cm.toFlowFM n (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Φ n := fun m h1 h2 =>
    ⟨(zero_le_one.trans (GridGoodGen_one_le_STXiLKg Cm.toFlowFM m ω hBpos)),
      hY' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  have hXb : ∀ m, 1 ≤ m → m ≤ k + 1 →
      0 ≤ STXiLg Cm.toFlowFM n (u : ℝ) m ω ∧
        STXiLg Cm.toFlowFM n (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Φ n := fun m h1 h2 =>
    ⟨(zero_le_one.trans (GridGoodGen_one_le_STXiLg Cm.toFlowFM m ω hBpos)),
      hX' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  unfold GoodSetNg
  refine ⟨hherm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·  -- the bound on `𝓛 - 𝒦` at the lengths `m < k`
    intro m h1 h2
    have h := hYb m h1 h2.le
    have h' := h.2
    rw [← STXiLKMg_Hf hLM n (u : ℝ) m ω] at h'
    exact h'
  ·  -- the decay of the loops with far labels
    intro j hj1 hj2 σ a hfar
    have h := hDec' j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) ((u, σ, a) : TimeIcc s t n × (Fin j → Bool) ×
      (Fin j → Zd d (sz.L n)))
    simp only [hfar, ↓reduceIte, mul_one] at h
    rw [hLM n (u : ℝ) σ a ω]
    exact h.trans (gridGood_pow_absorb hWpos hbwn)
  ·  -- the bound on `STksimLKMg`
    intro l hl3 hlk σ a
    have h := hD1' l (Finset.mem_Icc.2 ⟨hl3, hlk⟩) ((u, σ, a) : TimeIcc s t n × (Fin k → Bool) ×
      (Fin k → Zd d (sz.L n)))
    exact gridGood_mul_bound hΓ0 hBk h (hYb (k - l + 2) (by omega) (by omega)).2
  ·  -- the bound on `STelklkMg`
    intro σ a
    have h := hD2' ((u, σ, a) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    exact gridGood_D2_arith hk (Y := fun m => STXiLKg Cm.toFlowFM n (u : ℝ) m ω)
      (X := fun m => STXiLg Cm.toFlowFM n (u : ℝ) m ω) hΓ1 (hΦ n) hBk hB6
      (Real.rpow_nonneg hBpos.le _) hYb hXb h
  ·  -- the bound on `STegtMg`
    intro σ a
    have h := hD3' ((u, σ, a) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    have hi : 1 ≤ (STn12E k).1 ∧ (STn12E k).1 ≤ k + 1 ∧ 1 ≤ (STn12E k).2 ∧
        (STn12E k).2 ≤ k + 1 := by
      unfold STn12E
      split_ifs with h2 <;> simp only <;> omega
    have hx1 := hXb _ hi.1 hi.2.1
    have hx2 := hXb _ hi.2.2.1 hi.2.2.2
    exact gridGood_mul_bound hΓ0 hBk h (gridGood_sqrt_mul_le hx1.1 hx2.1 hx1.2 hx2.2)
  ·  -- the bound on `STeeMg`
    intro σ a a'
    have h := hD4' ((u, σ, a, a') : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) ×
      (Fin k → Zd d (sz.L n)))
    have hQu := hQ' u
    exact gridGood_D4_arith hBpos (zero_le_one.trans (GridGoodGen_one_le_STXiLg Cm.toFlowFM (4 * q) ω hBpos))
      hΓ0 hηpos h hQu
  ·  -- the decay of the sum of the three `ℰ`-terms at far labels
    intro σ a hfar
    have hfar' : ((sz.W n : ℕ) : ℝ) ^ τ' * ellT (sz.L n) (sz.lam n) (u : ℝ) ≤ (STdiamInf a : ℝ) := by
      rwa [mul_comm]
    obtain ⟨i, j, hij⟩ := gridGood_far_exists (by omega : 1 ≤ k) a hfar'
    have e1 := hEgt' σ (Finset.mem_univ σ) u a ⟨i, j, hij⟩
    have e3 := hEl' σ (Finset.mem_univ σ) u a ⟨i, j, hij⟩
    have e2 : ∀ l ∈ Finset.Icc 3 k, ‖STksimLKg Cm Hf n (u : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := fun l hl => hKs' σ (Finset.mem_univ σ) l hl u a ⟨i, j, hij⟩
    have hsum : ‖∑ l ∈ Finset.Icc 3 k, STksimLKg Cm Hf n (u : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
        ((Finset.Icc 3 k).card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_card_nsmul _ _ _ e2
      simpa [nsmul_eq_mul] using this
    have hcard : ((Finset.Icc 3 k).card : ℝ) + 2 ≤ k := by
      have : (Finset.Icc 3 k).card + 2 ≤ k := by rw [Nat.card_Icc]; omega
      exact_mod_cast this
    have hδ0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hWpos.le _
    calc _ ≤ ((Finset.Icc 3 k).card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) +
          ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) + ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := by
          exact add_le_add (add_le_add hsum e3) e1
      _ = (((Finset.Icc 3 k).card : ℝ) + 2) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := by ring
      _ ≤ (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := mul_le_mul_of_nonneg_right hcard hδ0
      _ ≤ _ := gridGood_nat_mul_pow_le hWpos hWk
  ·  -- the decay of `STeeMg` at far labels
    intro σ a a' hfar
    have hfar' : ((sz.W n : ℕ) : ℝ) ^ τ' * ellT (sz.L n) (sz.lam n) (u : ℝ) ≤
        (STdiamInf (Fin.append a a') : ℝ) := by rwa [mul_comm]
    obtain ⟨i, j, hij⟩ := gridGood_far_exists (by omega : 1 ≤ k + k) (Fin.append a a') hfar'
    have e := hEe' σ (Finset.mem_univ σ) u (Fin.append a a') ⟨i, j, hij⟩
    have e1 : (fun i : Fin k => (Fin.append a a' : Fin (k + k) → Zd d (sz.L n)) (Fin.castAdd k i)) = a :=
      funext (Fin.append_left a a')
    have e2 : (fun i : Fin k => (Fin.append a a' : Fin (k + k) → Zd d (sz.L n)) (Fin.natAdd k i)) = a' :=
      funext (Fin.append_right a a')
    beta_reduce at e
    rw [e1, e2] at e
    exact e

/-- **The transfer and the union bound** (band `gridGood_grid`): if with high probability `Hf n u ω ∈ GoodSetNg … u` (for the Hermitian
`Hf n u ω`) for every `u ∈ [s_n,t_n]`, then with high probability the carrier walk `Cm.Hpath … j` is in `GoodSetNg` at every grid index
`j ≤ K n` (the law `Step2EventsGen_Law` at each `j`, then `highProbAt_iInter` over `j ≤ K n`, `K n + 1 ≤ N^C`), provided the walk is
`Cm.Pp`-a.s. Hermitian. -/
private theorem GridGoodGen_grid {Cm : Step2Mat sz} {E : ℕ → ℝ} {μ : Measure sz.SeqΩ}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hL : StepDecompGen_LoopForm Cm E) (hLaw : Step2EventsGen_Law Cm μ Hf) (hsize : Tendsto sz.size atTop atTop)
    {s t v : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n)
    (hK : ∀ n, K n ≠ 0) {C : ℝ} (hC : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    {k : ℕ} {Γ Λ Φ : ℕ → ℝ} {τ' D' : ℝ}
    (hHerm : ∀ n j, ∀ᵐ ω ∂Cm.Pp, (Cm.Hpath s v K n j ω).IsHermitian)
    (hW : HighProbAt μ sz.size (fun n => {ω | ∀ u : TimeIcc s t n, (Hf n (u : ℝ) ω).IsHermitian →
      GoodSetNg Cm n (u : ℝ) k (Γ n) (Λ n) (Φ n) τ' D' (Hf n (u : ℝ) ω)})) :
    HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
      GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n j ω)}) := by
  have hSmeas : ∀ n j, MeasurableSet
      {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        H.IsHermitian → GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} := by
    intro n j
    have hH : MeasurableSet
        {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | H.IsHermitian} :=
      (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
    have e : {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        H.IsHermitian → GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} =
        {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | H.IsHermitian}ᶜ ∪
          {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} := by
      ext H
      simp [imp_iff_not_or]
    rw [e]
    exact hH.compl.union (measurableGoodSetNg hL n _ k _ _ _ _ _)
  have hgrid : ∀ n j, j ≤ K n →
      Cm.Pp {ω | Cm.Hpath s v K n j ω ∈ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        H.IsHermitian → GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H}ᶜ} ≤
      μ {ω | ∀ u : TimeIcc s t n, (Hf n (u : ℝ) ω).IsHermitian →
        GoodSetNg Cm n (u : ℝ) k (Γ n) (Λ n) (Φ n) τ' D' (Hf n (u : ℝ) ω)}ᶜ := by
    intro n j hj
    have hmem := gridGood_gridTime_mem hsv hvt hK n j hj
    rw [hLaw s v K n j (hs0 n) (hsv n) (hK n) _ (hSmeas n j).compl]
    refine measure_mono ?_
    intro ω hω hall
    exact hω (hall ⟨gridTime s v K n j, hmem⟩)
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hI := highProbAt_iInter Cm.Pp sz.size (K := fun n => Fin (K n + 1))
    (Ξ := fun n j => {ω | Cm.Hpath s v K n j.1 ω ∈ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      H.IsHermitian → GoodSetNg Cm n (gridTime s v K n j.1) k (Γ n) (Λ n) (Φ n) τ' D' H}}) (C := max C 0)
    (le_max_right _ _)
    (by
      filter_upwards [hC] with n hn
      rw [Fintype.card_fin]
      exact hn.trans (Real.rpow_le_rpow_of_exponent_le (hN1 n) (le_max_left _ _)))
    (fun D hD => (hW D hD).mono fun n hn j =>
      (hgrid n j.1 (Nat.lt_succ_iff.1 j.2)).trans hn)
  have hHE : HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n, (Cm.Hpath s v K n j ω).IsHermitian}) := by
    intro D hD
    refine Eventually.of_forall fun n => ?_
    have h : ∀ᵐ ω ∂Cm.Pp, ∀ j ≤ K n, (Cm.Hpath s v K n j ω).IsHermitian := by
      rw [ae_all_iff]
      intro j
      by_cases hj : j ≤ K n
      · filter_upwards [hHerm n j] with ω hω _ using hω
      · exact Eventually.of_forall fun ω h => absurd h hj
    have h0 := ae_iff.1 h
    have : Cm.Pp {ω | ∀ j ≤ K n, (Cm.Hpath s v K n j ω).IsHermitian}ᶜ = 0 := h0
    rw [this]
    exact zero_le
  refine (HighProbAt.inter hsize hI hHE).mono (Eventually.of_forall fun n ω hω j hj => ?_)
  have h1 := Set.mem_iInter.1 hω.1 ⟨j, Nat.lt_succ_of_le hj⟩
  exact h1 (hω.2 j hj)

end Core

/-! ## 4b. The public theorem

Hypotheses: `StepDecompGen_LoopForm Cm E`, `StepDecompGen_WalkForm Cm lam' Ψ` (it
gives the Hermitian clause of `GoodSetNg`, `Cm.Hpath = Ψ + pathH (sz.withLam lam')`), `Step2EventsGen_Law Cm μ Hf` (the law of the
grid state), `Step34Gen_LCompat Cm Hf`, `DecayGen_Spec`, `Admissible`, the window `0 ≤ s ≤ t < 1`, `B ≤ 1` on it, and the `≺` inputs
`STSEforLnConclgL`, `STDecayLoopUgL`, the four `ℰ`-term decays as `STEKDecaygL`.  Only `η > 0` on the window is read (through `DecayGen_Spec`). -/

section Public

variable {d : ℕ} {sz : Sizes d}

/-- **`gridGoodNgL_of`** (band `gridGoodN_holds` as a statement): the family form `GridGoodNgL d law Flow mkM T0`.
The `≺` inputs are `STSEforLngL` (the statement `lem:SEforLn` over the family), the loop decay from `stDecayLoopUgL_of_step2` (the `STGdecayWgL`
inside `STStep2ConclgL`), `DecayGen_WardPair`, `STKcalDecaygL` and the `ℰ`-term decays; the carrier facts are per flow (`Step2EventsGen_Flow`
for `Admissible` and `T0 < 1`, `StepDecompGen_LoopForm`, `StepDecompGen_WalkForm`, `Step2EventsGen_Law`, `Step34Gen_LCompat`, a spectral `κm`).  `B ≤ 1` on the window
is derived from `STConStInd`. -/
theorem gridGoodNgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (lam' : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)))) :
    GridGoodNgL d law Flow mkM T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := hSE hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hcon hStep2
  have hSE' := H 𝔠 sz z hflow s t hs hst ht hR hKb hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  have hU : STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t :=
    stDecayLoopUgL_of_step2 hd sz (mkM sz z).toFlowFM (law sz) κm 𝔠 𝔡 s t Cd hspec hA hs ht1 (hWard sz z)
      (hKcal sz κ ε 𝔠 𝔡 z hκ hflow) hStep2.2.2
  have hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1 := by
    filter_upwards [hcon] with n hn u hu
    have hBt : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
    have hlt : sz.Bctl n (t n) < 1 := by
      by_contra hge
      have h1 : (1 : ℝ) ≤ sz.Bctl n (t n) := not_lt.1 hge
      have h2 : (1 : ℝ) ≤ (sz.Bctl n (t n)) ^ 𝔠d := Real.one_le_rpow h1 h𝔠d0.le
      linarith [hn.1, hn.2]
    exact (STBctl_mono sz n hu (ht1 n)).trans hlt.le
  intro v hsv hvt K hK k hk Λ Φ hΛ hΦ hX hY q hq hQ C hC' ε₁ hε₁ τ' hτ' D' hD'
  have hU' := GridGoodGen_whp_uniform (hL sz κ ε 𝔠 𝔡 z hκ hflow) (hC sz z) hspec hA hs (fun n => (hst n).le) ht1 hB1
    hSE' hU hk (hEK sz κ ε 𝔠 𝔡 z hκ hflow s t hs (fun n => (hst n).le) ht1 hU k hk) hΦ hX hY hq hQ hε₁ hτ' hD'
  exact GridGoodGen_grid (hL sz κ ε 𝔠 𝔡 z hκ hflow) (hLaw sz z) (tendsto_size sz hA.2.2.1) hs hsv hvt hK hC'
    (fun n j => Eventually.of_forall fun ω => by
      rw [StepDecompGen_Hpath_eq (hW sz κ ε 𝔠 𝔡 z hκ hflow)]
      exact ((hW sz κ ε 𝔠 𝔡 z hκ hflow).1 n).add
        (pathH_isHermitian (sz.withLam (lam' sz z)) s v K n j ω)) hU'

end Public

end RBM.BA

end
