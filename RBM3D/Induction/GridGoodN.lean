/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.SEforLn2
import RBM3D.Induction.DecayLoopB
import RBM3D.Induction.StepDecompN
import RBM3D.Path.Walk
import RBM3D.Path.Stop

/-!
# The good set of the grid walk at loop length `k`, its exit time, its measurability, and the
# high-probability event `GridGoodN` (`d ≥ 3`)

Ticket T2146 (ST2-32, stochastic layer ST-2, the hub of the general-`n` grid walk).  Rewrite, not a
port, of `RBM2D/Induction/GridGoodN.lean` at `c9a24cf` (sections 1, 2, 5: `GoodSetN` :81,
`gridExitTauN` :123, `goodExitTauN`, `MeasurableGoodSetN`, `GoodExitMeasN`, `GridGoodN` :207,
`measurableGoodSetN` :532-1000).  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`
(`3_5:line`): `lem:SEforLn` (`3_5:1017-1065`), `Def_decay`, `lem_decayLoop` (`3_5:1115-1126`),
`def:XiL`, `def:XIL-K` (`3_5:1010-1012`).

## What is here (namespace `RBM.Gauss.Sizes` unless stated)

* §1 the matrix-level controls `STmaxLM`, `STmaxLKM`, `STXiLM`, `STXiLKM` (the merged `STmaxL`,
  `STmaxLK`, `STXiL`, `STXiLK` evaluated at a fine matrix `H`; the `gridGood_*_seqHflow` are `rfl`);
* §2 the pin `GoodSetN` (Hermitian; `Ξ̂^{(𝓛-𝒦)}_m ≤ ΓΦ`, `m < k`; far decay of `𝓛`, `𝓛-𝒦`; the four
  `ℰ` terms of `lem:SEforLn` at the levels of its four conjuncts; far decay of the `ℰ` terms);
* §3 (namespace `RBM.Path`) the exit times `gridExitTauN`, `goodExitTauN` and their four lemmas;
* §4 measurability: `MeasurableGoodSetN`, `GoodExitMeasN`, `measurableGoodSetN`, `goodExitMeasN`;
* §5 the pin `GridGoodN` (and `GridGoodNConcl`), proved as `gridGoodN_holds` from
  `stSEforLn_holds`, `stDecayLoopU_of_step2`, `stEtermDecay` and `map_pathH_eq`;
* §6 the levels `hX`, `hY`, `hQ` of `GridGoodNConcl` at `Φ ≡ 1` from `STLmaxU`, `STLKU`
  (private lemmas for §7);
* §7 the compiled nonempty instances at `d = 3` on the merged flow instance `sz0`.

Every helper that the ticket does not pin is `private` or prefixed `gridGood_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The matrix-level controls `Ξ̂` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- `max_{σ,a} |𝓛^{(k)}_{v,σ,a}(H)|` for a fine matrix `H` (the merged `STmaxL` is the case
`H = seqHflow sz n v ω`, `gridGood_STmaxLM_seqHflow`). -/
def STmaxLM (n : ℕ) (E v : ℝ) (k : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E v) p.1 p.2‖)

/-- `max_{σ,a} |(𝓛 - 𝒦)^{(k)}_{v,σ,a}(H)|` for a fine matrix `H`. -/
def STmaxLKM (n : ℕ) (E v : ℝ) (k : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E v) p.1 p.2 - STKloop sz n E v p.1 p.2‖)

/-- **`Ξ̂^{(𝓛)}_{v,k}(H)`** of `(def:XiL)` (`3_5:1010`) at a fine matrix `H`:
`1 + max_{σ,a} |𝓛^{(k)}_{v,σ,a}(H)| / (W^{-d}B_{v,0})^{k-1}`. -/
def STXiLM (n : ℕ) (E v : ℝ) (k : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  1 + STmaxLM sz n E v k H / (sz.Bctl n v) ^ (k - 1)

/-- **`Ξ̂^{(𝓛-𝒦)}_{v,k}(H)`** of `(def:XIL-K)` (`3_5:1012`) at a fine matrix `H`:
`1 + max_{σ,a} |(𝓛-𝒦)^{(k)}_{v,σ,a}(H)| / (W^{-d}B_{v,0})^k`. -/
def STXiLKM (n : ℕ) (E v : ℝ) (k : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  1 + STmaxLKM sz n E v k H / (sz.Bctl n v) ^ k

theorem gridGood_STmaxLM_seqHflow (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    STmaxLM sz n E v k (sz.seqHflow n v ω) = STmaxL sz n E v k ω := rfl

theorem gridGood_STmaxLKM_seqHflow (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    STmaxLKM sz n E v k (sz.seqHflow n v ω) = STmaxLK sz n E v k ω := rfl

theorem gridGood_STXiLM_seqHflow (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    STXiLM sz n E v k (sz.seqHflow n v ω) = STXiL sz n E v k ω := rfl

theorem gridGood_STXiLKM_seqHflow (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    STXiLKM sz n E v k (sz.seqHflow n v ω) = STXiLK sz n E v k ω := rfl

end Vocab

/-! ## 2. The good set -/

section GoodSet

variable {d : ℕ} (sz : Sizes d)

/-- **Pin (`GoodSetN`)**: the good set of the grid walk at the spectral time `u`, for the loop length
`k` (the paper's `n` of `lem:SEforLn`), the loss `Γ` (the caller takes `Γ = N^ε`), the deterministic
levels `Λ Φ` of the controls `Ξ̂` and the decay exponents `τ' D'`.  A set of fine matrices `H`
(`Matrix (Idx d L W) _ ℂ`, the grid state `H_u`), with `B = W^{-d}B_{u,0}` (`sz.Bctl`),
`η = etaT E u`, `ℓ_u = ellT`:
* Hermitian;
* (G2) `Ξ̂^{(𝓛-𝒦)}_m(H) ≤ ΓΦ` for `1 ≤ m < k`;
* (Dec) `(|𝓛^{(j)}| + |(𝓛-𝒦)^{(j)}|)(H) ≤ W^{-D'}` for `1 ≤ j ≤ 2k+2` at the labels with
  `ℓ_u W^{τ'} ≤ diam_∞ a` (`STdiamInf`; the form of `STDecayLoopU`, `lem_decayLoop`, `3_5:1126`);
* (D1)-(D4) the four `ℰ` terms of `lem:SEforLn` (`3_5:1017-1065`) at the matrix level (`STksimLKM`
  for `3 ≤ l ≤ k`, `STelklkM`, `STegtM`, `STeeM`) bounded by
  `Γ(ΓΦ) B^k/η`, `Γ k (ΓΦ)² B^k/η`, `Γ(ΓΦ) B^k/η`, `Γ(ΓΛ) B^{2k}/η`;
* (Va), (Vb) the label decay of the `ℰ` terms: `‖Σ_l 𝒦^{(l)}∼(𝓛-𝒦) + ℰ^{(𝓛-𝒦)×(𝓛-𝒦)} + ℰ^{G̃}‖ ≤ W^{-D'}`
  and `‖(ℰ⊗ℰ)^M‖ ≤ W^{-D'}` when two labels are `ℓ_u W^{τ'}` apart.
RBM2D `GoodSetN` (`GridGoodN.lean:81` at `c9a24cf`) has also (G1) `Ξ^{(𝓛)}_{2k+2} ≤ ΓΛ`, (G3) the
products `Ξ_mΞ_{k-m+2}M⁻¹ ≤ ΓΦ` and (G4) `Ξ^{(𝓛)}_{k+1} ≤ ΓΦ`: no `d ≥ 3` consumer uses them (the
levels of `lem:SEforLn` are (D1)-(D4) with the `Ξ̂` of the hypotheses of `GridGoodNConcl`), so they
are not clauses here (paper-delta candidate `T2146a`). -/
def GoodSetN (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | H.IsHermitian ∧
    (∀ m : ℕ, 1 ≤ m → m < k → STXiLKM sz n E u m H ≤ Γ * Φ) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a‖ +
          ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a - STKloop sz n E u σ a‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKM sz n E u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkM sz n E u H (loopOf σ a)‖ ≤
        Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtM sz n E u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ‖STeeM sz n E u H σ a a'‖ ≤ Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖∑ l ∈ Finset.Icc 3 k, STksimLKM sz n E u H l (loopOf σ a)‖ +
          ‖STelklkM sz n E u H (loopOf σ a)‖ + ‖STegtM sz n E u H (loopOf σ a)‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append a a') : ℝ) →
        ‖STeeM sz n E u H σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'))}

end GoodSet

end RBM.Gauss.Sizes

/-! ## 3. The exit times -/

namespace RBM.Path

open RBM RBM.Gauss RBM.Gauss.Sizes

section ExitTime

variable {d : ℕ} (sz : Sizes d)

/-- **Pin (`gridExitTauN`)**: the exit time of an arbitrary family `G` of matrix sets (one per grid
index) from the grid walk: the first `j ≤ K n` with `H_j ∉ G j`, and `K n` if there is none
(`firstHit` of the indicator of the complement at the level `1/2`).  RBM2D `gridExitTauN`
(`GridGoodN.lean:123` at `c9a24cf`). -/
def gridExitTauN (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :
    PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) =>
    (G j)ᶜ.indicator (fun _ => (1 : ℝ)) (pathH sz s v K n j ω)) (1 / 2) (K n)

/-- **Pin (`goodExitTauN`)**: the exit time of the grid walk from `GoodSetN`. -/
def goodExitTauN (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ)
    (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')

variable {sz} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
  {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}

/-- If `J` stays strictly below `θ` up to the horizon `K`, `firstHit J θ K` does not fire (RBM2D
`Path/Bootstrap.lean:78` at `c9a24cf`, `firstHit_eq_of_below`). -/
private theorem gridGood_firstHit_eq_of_below {Ω' : Type*} (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ)
    {ω : Ω'} (h : ∀ j ≤ K, J j ω < θ) : firstHit J θ K ω = K := by
  by_contra hne
  have hlt : firstHit J θ K ω < K := lt_of_le_of_ne (firstHit_le J θ K ω) hne
  have hmem : θ ≤ J (firstHit J θ K ω) ω :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  exact absurd (h _ hlt.le) (not_lt.2 hmem)

/-- `gridExitTauN ≤ K n`. -/
theorem gridExitTauN_le (ω : PathΩ sz) : gridExitTauN sz s v K n G ω ≤ K n :=
  firstHit_le _ _ _ ω

/-- Strictly before the exit, the grid state is in `G`. -/
theorem mem_of_lt_gridExitTauN {ω : PathΩ sz} {j : ℕ} (h : j < gridExitTauN sz s v K n G ω) :
    pathH sz s v K n j ω ∈ G j := by
  have h1 := lt_firstHit_imp _ _ _ h
  by_contra hmem
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h1
  norm_num at h1

/-- If the grid state stays in `G` up to `K n`, the exit time is `K n`. -/
theorem gridExitTauN_eq_of_forall_mem {ω : PathΩ sz}
    (hgood : ∀ j ≤ K n, pathH sz s v K n j ω ∈ G j) : gridExitTauN sz s v K n G ω = K n := by
  refine gridGood_firstHit_eq_of_below _ _ _ fun j hj => ?_
  have hnot : pathH sz s v K n j ω ∉ (G j)ᶜ := fun hc => hc (hgood j hj)
  rw [Set.indicator_of_notMem hnot]
  norm_num

/-- `{j < gridExitTauN}` is `filt sz j`-measurable when every `G j` is measurable. -/
theorem gridExitTauN_measurableSet (hG : ∀ j, MeasurableSet (G j)) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < gridExitTauN sz s v K n G ω} :=
  lt_firstHit_grid_measurableSet sz s v K n
    (F := fun j M => (G j)ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (fun j => measurable_const.indicator (hG j).compl) (1 / 2) (K n) j

end ExitTime

end RBM.Path

/-! ## 4. Measurability -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **Pin (matrix-level measurability of `GoodSetN`)**: for every size data, index, energy, time,
loop length, levels and exponents, `GoodSetN` is a measurable set of matrices (no hypothesis). -/
def MeasurableGoodSetN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ),
    MeasurableSet (sz.GoodSetN n E u k Γ Λ Φ τ' D')

section MeasurableProof

private theorem gridGood_measurableSet_forall {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {p : ι → α → Prop} (h : ∀ i, MeasurableSet {x | p i x}) :
    MeasurableSet {x | ∀ i, p i x} := by
  have e : {x | ∀ i, p i x} = ⋂ i, {x | p i x} := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter h

private theorem gridGood_measurableSet_imp {α : Type*} [MeasurableSpace α] {p : Prop}
    {q : α → Prop} (h : p → MeasurableSet {x | q x}) : MeasurableSet {x | p → q x} := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp [hp]

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem gridGood_meas_STLIM (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLIM sz n E τ H I :=
  (walk_measurable_loopL d (sz.L n) (sz.W n) (zt E τ) I).comp
    (walk_measurable_blockMat d (sz.L n) (sz.W n))

private theorem gridGood_meas_STLKIM (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLKIM sz n E τ H I :=
  (gridGood_meas_STLIM sz n E τ I).sub_const _

private theorem gridGood_meas_loopFine (E u : ℝ) {j : ℕ} (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopFine d (sz.L n) (sz.W n) H (zt E u) σ a :=
  walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a

private theorem gridGood_meas_STmaxLM (E u : ℝ) (k : ℕ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STmaxLM sz n E u k H := by
  have h : (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STmaxLM sz n E u k H) = Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2‖) := by
    funext H
    rw [Finset.sup'_apply (C := fun _ => ℝ)]
    rfl
  rw [h]
  exact Finset.measurable_sup' _ fun p _ => (gridGood_meas_loopFine sz n E u p.1 p.2).norm

private theorem gridGood_meas_STmaxLKM (E u : ℝ) (k : ℕ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STmaxLKM sz n E u k H := by
  have h : (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STmaxLKM sz n E u k H) = Finset.univ.sup' Finset.univ_nonempty
      (fun (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖) := by
    funext H
    rw [Finset.sup'_apply (C := fun _ => ℝ)]
    rfl
  rw [h]
  exact Finset.measurable_sup' _ fun p _ =>
    ((gridGood_meas_loopFine sz n E u p.1 p.2).sub_const _).norm

private theorem gridGood_meas_STXiLKM (E u : ℝ) (m : ℕ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STXiLKM sz n E u m H := by
  unfold STXiLKM
  exact measurable_const.add ((gridGood_meas_STmaxLKM sz n E u m).div_const _)

private theorem gridGood_meas_STksimLKM (E u : ℝ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STksimLKM sz n E u H l I := by
  unfold STksimLKM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  refine Measurable.add ?_ ?_
  · exact Measurable.ite (MeasurableSet.const _)
      (((gridGood_meas_STLKIM sz n E u _).mul_const _).mul_const _) measurable_const
  · exact Measurable.ite (MeasurableSet.const _)
      ((measurable_const.mul_const _).mul (gridGood_meas_STLKIM sz n E u _)) measurable_const

private theorem gridGood_meas_STksimLKM_sum (E u : ℝ) (k : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ∑ l ∈ Finset.Icc 3 k, STksimLKM sz n E u H l I :=
  Finset.measurable_sum _ fun l _ => gridGood_meas_STksimLKM sz n E u l I

private theorem gridGood_meas_STelklkM (E u : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STelklkM sz n E u H I := by
  unfold STelklkM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun l' _ => Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((gridGood_meas_STLKIM sz n E u _).mul_const _).mul (gridGood_meas_STLKIM sz n E u _)

private theorem gridGood_meas_STavgErrM (E u : ℝ) (σ : Bool) (a : Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STavgErrM sz n E u H σ a := by
  unfold STavgErrM
  exact (gridGood_meas_STLIM sz n E u _).sub_const _

private theorem gridGood_meas_STegtM (E u : ℝ) (I : LoopIdx (Zd d (sz.L n))) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STegtM sz n E u H I := by
  unfold STegtM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun a _ => Finset.measurable_sum _ fun b _ => ?_)
  exact ((gridGood_meas_STavgErrM sz n E u _ a).mul_const _).mul (gridGood_meas_STLIM sz n E u _)

private theorem gridGood_meas_STeeM (E u : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a a' : Fin m → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STeeM sz n E u H σ a a' := by
  unfold STeeM
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun b _ => Finset.measurable_sum _ fun b' _ => ?_)
  exact measurable_const.mul (gridGood_meas_STLIM sz n E u _)

end MeasurableProof

/-- **Target `measurableGoodSetN`**: `GoodSetN` is a measurable set of matrices, for every
`sz n E u k Γ Λ Φ τ' D'` (no hypothesis): a finite conjunction, over finitely many labels, of
inequalities between measurable functions of `H` (norms of the loop observables) and the closed
set `H.IsHermitian`.  Template: RBM2D `measurableGoodSetN` (`GridGoodN.lean:532` at `c9a24cf`). -/
theorem measurableGoodSetN (d : ℕ) : MeasurableGoodSetN d := by
  intro sz n E u k Γ Λ Φ τ' D'
  have hH : MeasurableSet
      {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | H.IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet
  unfold GoodSetN
  simp only [Set.ofPred_and]
  refine hH.inter (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ ?_)))))))
  · exact gridGood_measurableSet_forall fun m => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ =>
        measurableSet_le (gridGood_meas_STXiLKM sz n E u m) measurable_const
  · exact gridGood_measurableSet_forall fun j => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ => gridGood_measurableSet_forall fun σ =>
        gridGood_measurableSet_forall fun a => gridGood_measurableSet_imp fun _ =>
          measurableSet_le (((gridGood_meas_loopFine sz n E u σ a).norm).add
            ((gridGood_meas_loopFine sz n E u σ a).sub_const _).norm) measurable_const
  · exact gridGood_measurableSet_forall fun l => gridGood_measurableSet_imp fun _ =>
      gridGood_measurableSet_imp fun _ => gridGood_measurableSet_forall fun σ =>
        gridGood_measurableSet_forall fun a =>
          measurableSet_le (gridGood_meas_STksimLKM sz n E u l (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      measurableSet_le (gridGood_meas_STelklkM sz n E u (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      measurableSet_le (gridGood_meas_STegtM sz n E u (loopOf σ a)).norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      gridGood_measurableSet_forall fun a' =>
        measurableSet_le (gridGood_meas_STeeM sz n E u σ a a').norm measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      gridGood_measurableSet_imp fun _ =>
        measurableSet_le (((gridGood_meas_STksimLKM_sum sz n E u k (loopOf σ a)).norm.add
          (gridGood_meas_STelklkM sz n E u (loopOf σ a)).norm).add
            (gridGood_meas_STegtM sz n E u (loopOf σ a)).norm) measurable_const
  · exact gridGood_measurableSet_forall fun σ => gridGood_measurableSet_forall fun a =>
      gridGood_measurableSet_forall fun a' => gridGood_measurableSet_imp fun _ =>
        measurableSet_le (gridGood_meas_STeeM sz n E u σ a a').norm measurable_const

end RBM.Gauss.Sizes

namespace RBM.Path

open RBM RBM.Gauss RBM.Gauss.Sizes

section ExitMeasurable

variable {d : ℕ} (sz : Sizes d)

/-- **Pin (measurability of `{j < goodExitTauN}`, the form `StoppedAzumaN` takes)**: for every
size index `n`, loop length `k`, levels and exponents, `{j < goodExitTauN}` is `filt sz j`-measurable. -/
def GoodExitMeasN (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ),
    MeasurableSet[filt sz j] {ω | j < goodExitTauN sz E s v K k Γ Λ Φ τ' D' n ω}

/-- The matrix-level measurability gives the exit-time measurability pin. -/
private theorem goodExitMeasN_of_measurable {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ}
    (hM : MeasurableGoodSetN d) : GoodExitMeasN sz E s v K :=
  fun n k Γ Λ Φ τ' D' j =>
    gridExitTauN_measurableSet (fun j => hM sz n _ _ _ _ _ _ _ _) j

/-- **Target `goodExitMeasN`**: `{j < goodExitTauN}` is `filt sz j`-measurable (from
`measurableGoodSetN` and `goodExitMeasN_of_measurable`), no hypothesis. -/
theorem goodExitMeasN (E s v : ℕ → ℝ) (K : ℕ → ℕ) : GoodExitMeasN sz E s v K :=
  goodExitMeasN_of_measurable sz (measurableGoodSetN d)

end ExitMeasurable

end RBM.Path

/-! ## 5. `GridGoodN`: the grid walk stays in the good set with high probability

The grid state `H_j` has the law of the single-time flow `seqHflow` at the grid time `u_j` (`map_pathH_eq`),
and `GoodSetN` is measurable; so the failure probability of the event at the grid index `j` is at most
that of the event "`seqHflow sz n u ω ∈ GoodSetN … u` for every `u ∈ [s_n,t_n]`", which is a finite
conjunction of `≺` statements uniform in `u` (the hypotheses `hX`, `hY`, `hQ` of `GridGoodNConcl`,
`stSEforLn_holds`, `stDecayLoopU_of_step2`, `stEtermDecay`).  Then `highProbAt_iInter` over `j ≤ K n`. -/

section Helpers

open RBM.Gauss

/-- A finite family of `w.h.p.` events holds simultaneously `w.h.p.` (`HighProbAt.biInter` with the
constant count `Nat.card ι ≤ size l` eventually). -/
private theorem gridGood_whp_iInter {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {ι : Type*} [Finite ι] {Ξ : ι → ℕ → Set Ω}
    (h : ∀ i, HighProbAt P size (Ξ i)) : HighProbAt P size (fun n => ⋂ i, Ξ i n) := by
  have := Fintype.ofFinite ι
  refine HighProbAt.biInter (K := fun _ => ι) (C := 1) zero_le_one ?_ ?_
  · filter_upwards [hsize.eventually (eventually_ge_atTop (Fintype.card ι))] with l hl
    rw [Real.rpow_one]
    exact_mod_cast hl
  · intro D hD
    have : ∀ᶠ l in atTop, ∀ i, P (Ξ i l)ᶜ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) :=
      Filter.eventually_all.2 fun i => h i D hD
    exact this.mono fun l hl i => hl i

/-- A `Finset`-indexed family of `w.h.p.` events holds simultaneously `w.h.p.` -/
private theorem gridGood_whp_forall_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {ι : Type*} (S : Finset ι)
    {p : ι → ℕ → Ω → Prop} (h : ∀ i ∈ S, HighProbAt P size (fun n => {ω | p i n ω})) :
    HighProbAt P size (fun n => {ω | ∀ i ∈ S, p i n ω}) := by
  have := gridGood_whp_iInter hsize (ι := ↥S) (Ξ := fun i n => {ω | p i.1 n ω})
    (fun i => h i.1 i.2)
  refine this.mono (Eventually.of_forall fun n ω hω i hi => ?_)
  have := Set.mem_iInter.1 hω ⟨i, hi⟩
  exact this

/-- Two `w.h.p.` events hold simultaneously `w.h.p.` (set-builder form). -/
private theorem gridGood_whp_and {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {p q : ℕ → Ω → Prop}
    (hp : HighProbAt P size (fun n => {ω | p n ω})) (hq : HighProbAt P size (fun n => {ω | q n ω})) :
    HighProbAt P size (fun n => {ω | p n ω ∧ q n ω}) :=
  HighProbAt.inter hsize hp hq

/-- `√(x₁ x₂) ≤ c` when `0 ≤ x₁, x₂ ≤ c`. -/
private theorem gridGood_sqrt_mul_le {x₁ x₂ c : ℝ} (h1 : 0 ≤ x₁) (h2 : 0 ≤ x₂) (hc1 : x₁ ≤ c)
    (hc2 : x₂ ≤ c) : (x₁ * x₂) ^ (1 / 2 : ℝ) ≤ c := by
  have hc : 0 ≤ c := h1.trans hc1
  rw [← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_iff.mpr ⟨hc, ?_⟩
  nlinarith

end Helpers

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section GridGood

variable {d : ℕ}

/-- **The conclusion of the pin `GridGoodN`** at `(sz, E, s, t)`: for every `v ∈ [s,t]`, every grid size
`K` (`K n ≠ 0`, `K n + 1 ≤ N^C`), every loop length `k ≥ 2`, every pair of deterministic levels `Λ, Φ ≥ 1`
of the controls `Ξ̂` (hypotheses `hX`: `Ξ̂^{(𝓛)}_m ≺ Φ`, `m ≤ k+1`; `hY`: `Ξ̂^{(𝓛-𝒦)}_m ≺ Φ`, `m ≤ k`; `hQ`:
`Ξ̂^{(𝓛)}_{2k-1} (Ξ̂^{(𝓛)}_{4q}/B)^{1/(2q)} ≺ Λ` for one `q ≥ 1`, all uniform in `u ∈ [s_n,t_n]`),
and every `ε, τ', D' > 0`: with high probability the grid walk `H_j` stays in `GoodSetN` at every
`j ≤ K n` (the union bound over the `K n + 1 ≤ N^C` grid times).  RBM2D `GridGoodN`
(`GridGoodN.lean:207` at `c9a24cf`).  The RBM2D hypotheses are replaced as follows (all inside the context of
`STIngR`, see `GridGoodN`): `MainIndHyp` by `STFlow`, `STConStInd`, `0 ≤ s < t ≤ lemT z`, `STLK s`; `KboundConcl` by
`STKbound`, `STKward`; `KcalDecay` by the decay of `𝒦` inside `stEtermDecay` (`inst_stKcalDecay_admissible`);
`GbEXPHypV3`, `Step2LocalPT` by `STLocalEntryU` and `Step2DecayPT` by `STGdecayW` (both in `STStep2Concl`);
`DecayLoopPT` by `STDecayLoopU` (`stDecayLoopU_of_step2`); `PT` by `Prec` over `TimeIcc s t n` (the union over `u`
inside `P`, DECISIONS §39); `M_u = scaleM` by `(W^{-d}B_{u,0})⁻¹ = (sz.Bctl n u)⁻¹`; `N = (WL)^d = sz.size n`. -/
def GridGoodNConcl (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 1 ≤ Λ n) → (∀ n, 1 ≤ Φ n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    ∀ q : ℕ, 1 ≤ q →
    Prec sz (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) (2 * k - 1) ω *
        (STXiL sz n (E n) (u : ℝ) (4 * q) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (q : ℝ))))
      (fun n _ _ => Λ n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k
          (((sz.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'})

/-- **Pin (`GridGoodN`)**: the Step 3-4 ingredient shape (`STIngR`: `3 ≤ d`, the constants `κ ε 𝔡 C_d`, then
`𝔠_d`, the flow, `0 ≤ s < t ≤ lemT z`, `STKbound`, `STKward`, `STLK s`, `STConStInd`, `STStep2Concl`) with the
conclusion `GridGoodNConcl`. -/
def GridGoodN (d : ℕ) : Prop := STIngR d STAny (fun sz E s t => GridGoodNConcl sz E s t)

end GridGood

end RBM.Gauss.Sizes

/-! ### The deterministic arithmetic of the clauses -/

section Arith

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- `W^{-D'} ≥ N^𝔠 W^{-(D'+1)}` when `N^𝔠 ≤ W` (absorption of the loss `N^𝔠` into one power of `W`). -/
private theorem gridGood_pow_absorb {a W D : ℝ} (hW : 0 < W) (ha : a ≤ W) :
    a * W ^ (-(D + 1)) ≤ W ^ (-D) := by
  have h : W ^ (-D) = W * W ^ (-(D + 1)) := by
    have := Real.rpow_add hW 1 (-(D + 1))
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  rw [h]
  exact mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hW.le _)

/-- `k W^{-(D+1)} ≤ W^{-D}` when `k ≤ W`. -/
private theorem gridGood_nat_mul_pow_le {k : ℕ} {W D : ℝ} (hW : 0 < W) (hk : (k : ℝ) ≤ W) :
    (k : ℝ) * W ^ (-(D + 1)) ≤ W ^ (-D) :=
  gridGood_pow_absorb hW hk

/-- `x ≤ Γ (Bk Y)` and `Y ≤ c` give `x ≤ Γ c Bk` (the shape of the clauses (D1), (D3)). -/
private theorem gridGood_mul_bound {x Γ Bk Y c : ℝ} (hΓ : 0 ≤ Γ) (hBk : 0 ≤ Bk)
    (hx : x ≤ Γ * (Bk * Y)) (hY : Y ≤ c) : x ≤ Γ * c * Bk := by
  calc x ≤ Γ * (Bk * Y) := hx
    _ ≤ Γ * (Bk * c) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hBk) hΓ
    _ = Γ * c * Bk := by ring

/-- The clause (D4): `B^{2k - 1/(2q)} η⁻¹ X₁ X₂^{1/(2q)} = B^{2k} η⁻¹ X₁ (X₂/B)^{1/(2q)}`. -/
private theorem gridGood_D4_arith {B η Γ L X₁ X₂ x : ℝ} {k q : ℕ} (hB : 0 < B) (hX₂ : 0 ≤ X₂)
    (hΓ : 0 ≤ Γ) (hη : 0 < η)
    (hx : x ≤ Γ * (B ^ ((2 * (k : ℝ)) - 1 / (2 * (q : ℝ))) / η * (X₁ * X₂ ^ (1 / (2 * (q : ℝ))))))
    (hQ : X₁ * (X₂ / B) ^ (1 / (2 * (q : ℝ))) ≤ Γ * L) :
    x ≤ Γ * (Γ * L) * (B ^ (2 * k) / η) := by
  have hr : B ^ ((2 * (k : ℝ)) - 1 / (2 * (q : ℝ))) * X₂ ^ (1 / (2 * (q : ℝ))) =
      B ^ (2 * k) * (X₂ / B) ^ (1 / (2 * (q : ℝ))) := by
    rw [Real.div_rpow hX₂ hB.le, Real.rpow_sub hB, ← Real.rpow_natCast B (2 * k)]
    push_cast
    field_simp
  have hBη : 0 ≤ B ^ (2 * k) / η := by positivity
  calc x ≤ Γ * (B ^ ((2 * (k : ℝ)) - 1 / (2 * (q : ℝ))) / η * (X₁ * X₂ ^ (1 / (2 * (q : ℝ))))) := hx
    _ = Γ * ((B ^ ((2 * (k : ℝ)) - 1 / (2 * (q : ℝ))) * X₂ ^ (1 / (2 * (q : ℝ)))) * X₁ / η) := by
        ring
    _ = Γ * ((B ^ (2 * k) * (X₂ / B) ^ (1 / (2 * (q : ℝ)))) * X₁ / η) := by rw [hr]
    _ = Γ * (B ^ (2 * k) / η * (X₁ * (X₂ / B) ^ (1 / (2 * (q : ℝ))))) := by ring
    _ ≤ Γ * (B ^ (2 * k) / η * (Γ * L)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hBη) hΓ
    _ = Γ * (Γ * L) * (B ^ (2 * k) / η) := by ring

/-- The clause (D2): the sum over `n'` has at most `k - 2` terms, each `≤ c²`, plus `B^{1/6} Y_k ≤ c ≤ c²`. -/
private theorem gridGood_D2_arith {k : ℕ} (hk : 2 ≤ k) {Γ Φ Bk B6 x : ℝ} {Y X : ℕ → ℝ}
    (hΓ : 1 ≤ Γ) (hΦ : 1 ≤ Φ) (hBk : 0 ≤ Bk) (hB6 : B6 ≤ 1) (hB6' : 0 ≤ B6)
    (hY : ∀ m, 1 ≤ m → m ≤ k → 0 ≤ Y m ∧ Y m ≤ Γ * Φ)
    (hX : ∀ m, 1 ≤ m → m ≤ k + 1 → 0 ≤ X m ∧ X m ≤ Γ * Φ)
    (hx : x ≤ Γ * (Bk * (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
        Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) + B6 * Y k))) :
    x ≤ Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * Bk := by
  have hc : 1 ≤ Γ * Φ := by nlinarith
  have hc0 : 0 ≤ Γ * Φ := by linarith
  have hterm : ∀ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) ≤ (Γ * Φ) * (Γ * Φ) := by
    intro n' hn'
    rw [Finset.mem_Icc] at hn'
    have hn2 : 2 ≤ n' := by omega
    have hy := hY (k + 2 - n') (by omega) (by omega)
    have hi : 1 ≤ (STn12 n').1 ∧ (STn12 n').1 ≤ k + 1 ∧ 1 ≤ (STn12 n').2 ∧ (STn12 n').2 ≤ k + 1 := by
      unfold STn12
      split_ifs with h2 <;> simp only <;> omega
    have hx1 := hX _ hi.1 hi.2.1
    have hx2 := hX _ hi.2.2.1 hi.2.2.2
    have hsq := gridGood_sqrt_mul_le hx1.1 hx2.1 hx1.2 hx2.2
    exact mul_le_mul hy.2 hsq (Real.rpow_nonneg (mul_nonneg hx1.1 hx2.1) _) hc0
  have hsum : ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) ≤
      ((Finset.Icc ((k + 1) / 2 + 1) (k - 1)).card : ℝ) * ((Γ * Φ) * (Γ * Φ)) := by
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    simpa [nsmul_eq_mul] using this
  have hcard : (Finset.Icc ((k + 1) / 2 + 1) (k - 1)).card + 1 ≤ k := by
    rw [Nat.card_Icc]; omega
  have hcard' : ((Finset.Icc ((k + 1) / 2 + 1) (k - 1)).card : ℝ) + 1 ≤ k := by
    exact_mod_cast hcard
  have hYk := hY k (by omega) le_rfl
  have hlast : B6 * Y k ≤ (Γ * Φ) * (Γ * Φ) := by
    calc B6 * Y k ≤ 1 * (Γ * Φ) := mul_le_mul hB6 hYk.2 hYk.1 zero_le_one
      _ ≤ (Γ * Φ) * (Γ * Φ) := by nlinarith
  have htot : ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
        Y (k + 2 - n') * (X (STn12 n').1 * X (STn12 n').2) ^ (1 / 2 : ℝ) + B6 * Y k ≤
      (k : ℝ) * (Γ * Φ) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (Γ * Φ) * (Γ * Φ) := by positivity
    nlinarith
  calc x ≤ Γ * (Bk * _) := hx
    _ ≤ Γ * (Bk * ((k : ℝ) * (Γ * Φ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htot hBk) (by linarith)
    _ = Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * Bk := by ring

/-- A far label vector has a far pair in the `ℓ¹` distance of `EKFastDecay`: `R ≤ diam_∞ a` gives
`i, j` with `R ≤ |a_i - a_j|_{ℓ¹}`. -/
private theorem gridGood_far_exists {d L k : ℕ} (hk : 1 ≤ k) (a : Fin k → Zd d L) {R : ℝ}
    (h : R ≤ (STdiamInf a : ℝ)) :
    ∃ i j, R ≤ (zdistD d L (a i - a j) : ℝ) := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k × Fin k))
    Finset.univ_nonempty (fun p : Fin k × Fin k => zdistInf d L (a p.1 - a p.2))
  refine ⟨p.1, p.2, h.trans ?_⟩
  have h1 : (STdiamInf a : ℝ) = (zdistInf d L (a p.1 - a p.2) : ℝ) := by
    unfold STdiamInf; exact_mod_cast hp
  rw [h1]
  exact_mod_cast zdistInf_le_zdistD d L _

end Arith

/-! ### The uniform event: `seqHflow n u ω ∈ GoodSetN` for every `u ∈ [s_n,t_n]`, w.h.p. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Uniform

variable {d : ℕ}

private theorem gridGood_one_le_STXiL (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiL sz n E v k ω := by
  unfold STXiL
  have h0 : 0 ≤ STmaxL sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

private theorem gridGood_one_le_STXiLK (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiLK sz n E v k ω := by
  unfold STXiLK
  have h0 : 0 ≤ STmaxLK sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω - STKloop sz n E v p.1 p.2‖)
      (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB k).le
  linarith

/-- **The uniform good event**: from the hypotheses of `GridGoodNConcl` and the three `lem:SEforLn`,
`lem_decayLoop`, label-decay inputs, with high probability `seqHflow n u ω ∈ GoodSetN … u` for every
`u ∈ [s_n,t_n]` at once. -/
private theorem gridGood_whp_uniform (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 : ℝ} {E s t : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1)
    (hSE : STSEforLnConcl sz E s t) (hU : STDecayLoopU sz E s t)
    {k : ℕ} (hk : 2 ≤ k) {Λ Φ : ℕ → ℝ} (hΦ : ∀ n, 1 ≤ Φ n)
    (hX : ∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω) (fun n _ _ => Φ n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n _ _ => Φ n))
    {q : ℕ} (hq : 1 ≤ q)
    (hQ : Prec sz (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) (2 * k - 1) ω *
        (STXiL sz n (E n) (u : ℝ) (4 * q) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (q : ℝ))))
      (fun n _ _ => Λ n))
    {ε : ℝ} (hε : 0 < ε) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    Whp sz (fun n => {ω | ∀ u : TimeIcc s t n, sz.seqHflow n (u : ℝ) ω ∈
      sz.GoodSetN n (E n) (u : ℝ) k (((sz.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'}) := by
  obtain ⟨h𝔠, h𝔡, hN, hBw, hWO⟩ := id hA
  have hsz : Tendsto sz.size atTop atTop := tendsto_size sz hN
  -- positivity of the scales on the window
  have hpos : ∀ n (u : TimeIcc s t n), 0 < sz.Bctl n (u : ℝ) ∧ 0 < etaT (E n) (u : ℝ) := by
    intro n u
    have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (ht1 n)
    refine ⟨st_Bctl_pos sz hu1, etaT_pos ?_ hu1⟩
    have := hE n
    linarith
  -- the w.h.p. events
  have wY := gridGood_whp_forall_mem hsz (Finset.Icc 1 k) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact (hY m hm.1 hm.2).whp sz hε)
  have wX := gridGood_whp_forall_mem hsz (Finset.Icc 1 (k + 1)) (fun m hm => by
    rw [Finset.mem_Icc] at hm
    exact (hX m hm.1 hm.2).whp sz hε)
  have wQ := hQ.whp sz hε
  have wDec := gridGood_whp_forall_mem hsz (Finset.Icc 1 (2 * k + 2)) (fun j hj => by
    rw [Finset.mem_Icc] at hj
    exact (hU j hj.1 τ' hτ' (D' + 1) (by linarith)).whp sz h𝔠)
  have hSE' := hSE k hk
  have wD3 := hSE'.1.whp sz hε
  have wD1 := gridGood_whp_forall_mem hsz (Finset.Icc 3 k) (fun l hl => by
    rw [Finset.mem_Icc] at hl
    exact (hSE'.2.1 l hl.1 hl.2).whp sz hε)
  have wD2 := hSE'.2.2.1.whp sz hε
  have wD4 := (hSE'.2.2.2 q hq).whp sz hε
  have EK := fun σ => stEtermDecay hd sz hκ hE hA hs0 hst ht1 hU k hk σ
  have wEgt := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    (EK σ).1 τ' (D' + 1) hτ' (by linarith))
  have wKs := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    gridGood_whp_forall_mem hsz (Finset.Icc 3 k) (fun l _ =>
      (EK σ).2.1 l τ' (D' + 1) hτ' (by linarith)))
  have wEl := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    (EK σ).2.2.1 τ' (D' + 1) hτ' (by linarith))
  have wEe := gridGood_whp_forall_mem hsz (Finset.univ : Finset (Fin k → Bool)) (fun σ _ =>
    (EK σ).2.2.2 τ' D' hτ' hD')
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
  intro ω hω u
  obtain ⟨hY', hX', hQ', hDec', hD1', hD2', hD3', hD4', hEgt', hKs', hEl', hEe'⟩ := hω
  have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (ht1 n)
  obtain ⟨hBpos, hηpos⟩ := hpos n u
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hΓ1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hΓ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε := by linarith
  have hBk : 0 ≤ (sz.Bctl n (u : ℝ)) ^ k / etaT (E n) (u : ℝ) := by positivity
  have hB6 : (sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) ≤ 1 :=
    Real.rpow_le_one hBpos.le (hB1n (u : ℝ) u.2.2) (by norm_num)
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hYb : ∀ m, 1 ≤ m → m ≤ k →
      0 ≤ STXiLK sz n (E n) (u : ℝ) m ω ∧
        STXiLK sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Φ n := fun m h1 h2 =>
    ⟨(zero_le_one.trans (gridGood_one_le_STXiLK sz m ω hBpos)),
      hY' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  have hXb : ∀ m, 1 ≤ m → m ≤ k + 1 →
      0 ≤ STXiL sz n (E n) (u : ℝ) m ω ∧
        STXiL sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ ε * Φ n := fun m h1 h2 =>
    ⟨(zero_le_one.trans (gridGood_one_le_STXiL sz m ω hBpos)),
      hX' m (Finset.mem_Icc.2 ⟨h1, h2⟩) u⟩
  rw [GoodSetN, Set.mem_ofPred_eq]
  refine ⟨sz.seqHflow_isHermitian n (u : ℝ) ω, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (G2)
    intro m h1 h2
    exact hY' m (Finset.mem_Icc.2 ⟨h1, h2.le⟩) u
  · -- (Dec)
    intro j hj1 hj2 σ a hfar
    have h := hDec' j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) ((u, σ, a) : TimeIcc s t n × (Fin j → Bool) ×
      (Fin j → Zd d (sz.L n)))
    simp only [hfar, ↓reduceIte, mul_one] at h
    exact h.trans (gridGood_pow_absorb hWpos hbwn)
  · -- (D1)
    intro l hl3 hlk σ a
    have h := hD1' l (Finset.mem_Icc.2 ⟨hl3, hlk⟩) ((u, σ, a) : TimeIcc s t n × (Fin k → Bool) ×
      (Fin k → Zd d (sz.L n)))
    exact gridGood_mul_bound hΓ0 hBk h (hYb (k - l + 2) (by omega) (by omega)).2
  · -- (D2)
    intro σ a
    have h := hD2' ((u, σ, a) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    exact gridGood_D2_arith hk (Y := fun m => STXiLK sz n (E n) (u : ℝ) m ω)
      (X := fun m => STXiL sz n (E n) (u : ℝ) m ω) hΓ1 (hΦ n) hBk hB6
      (Real.rpow_nonneg hBpos.le _) hYb hXb h
  · -- (D3)
    intro σ a
    have h := hD3' ((u, σ, a) : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    have hi : 1 ≤ (STn12E k).1 ∧ (STn12E k).1 ≤ k + 1 ∧ 1 ≤ (STn12E k).2 ∧
        (STn12E k).2 ≤ k + 1 := by
      unfold STn12E
      split_ifs with h2 <;> simp only <;> omega
    have hx1 := hXb _ hi.1 hi.2.1
    have hx2 := hXb _ hi.2.2.1 hi.2.2.2
    exact gridGood_mul_bound hΓ0 hBk h (gridGood_sqrt_mul_le hx1.1 hx2.1 hx1.2 hx2.2)
  · -- (D4)
    intro σ a a'
    have h := hD4' ((u, σ, a, a') : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) ×
      (Fin k → Zd d (sz.L n)))
    have hQu := hQ' u
    exact gridGood_D4_arith hBpos (zero_le_one.trans (gridGood_one_le_STXiL sz (4 * q) ω hBpos))
      hΓ0 hηpos h hQu
  · -- (Va)
    intro σ a hfar
    have hfar' : ((sz.W n : ℕ) : ℝ) ^ τ' * ellT (sz.L n) (sz.lam n) (u : ℝ) ≤ (STdiamInf a : ℝ) := by
      rwa [mul_comm]
    obtain ⟨i, j, hij⟩ := gridGood_far_exists (by omega : 1 ≤ k) a hfar'
    have hδ : ∀ {x : ℝ}, x ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) → x ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
      fun h => h
    have e1 := hEgt' σ (Finset.mem_univ σ) u a ⟨i, j, hij⟩
    have e3 := hEl' σ (Finset.mem_univ σ) u a ⟨i, j, hij⟩
    have e2 : ∀ l ∈ Finset.Icc 3 k, ‖sz.STksimLK n (E n) (u : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := fun l hl => hKs' σ (Finset.mem_univ σ) l hl u a ⟨i, j, hij⟩
    have hsum : ‖∑ l ∈ Finset.Icc 3 k, sz.STksimLK n (E n) (u : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
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
  · -- (Vb)
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

end Uniform

/-! ### The grid: transfer to the single-time flow and the union bound over `j ≤ K n` -/

section Grid

variable {d : ℕ}

private theorem gridGood_gridTime_mem {s v t : ℕ → ℝ} {K : ℕ → ℕ} (hsv : ∀ n, s n ≤ v n)
    (hvt : ∀ n, v n ≤ t n) (hK : ∀ n, K n ≠ 0) (n j : ℕ) (hj : j ≤ K n) :
    gridTime s v K n j ∈ Set.Icc (s n) (t n) := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero (hK n)
  have hstep : 0 ≤ gridStep s v K n := div_nonneg (by linarith [hsv n]) hKpos.le
  have hjK : (j : ℝ) ≤ K n := by exact_mod_cast hj
  unfold gridTime
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hstep]
  · have h1 : (j : ℝ) * gridStep s v K n ≤ (K n : ℝ) * gridStep s v K n :=
      mul_le_mul_of_nonneg_right hjK hstep
    have hK' : (K n : ℝ) * gridStep s v K n = v n - s n := by
      unfold gridStep; field_simp
    linarith [hvt n]

private theorem gridGood_measurable_pathH (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j

private theorem gridGood_measurable_seqHflow (sz : Sizes d) (n : ℕ) (u : ℝ) :
    Measurable (sz.seqHflow n u) :=
  Measurable.of_eval_matrix _ fun i j => measurable_seqHflow_entry sz n u i j

/-- **The transfer and the union bound**: if with high probability `seqHflow n u ω ∈ GoodSetN … u` for
every `u ∈ [s_n,t_n]`, then with high probability the grid walk `pathH … j` is in `GoodSetN` at every
grid index `j ≤ K n` (`map_pathH_eq` at each `j`, then `highProbAt_iInter` over `j ≤ K n`,
`K n + 1 ≤ N^C`). -/
private theorem gridGood_grid (sz : Sizes d) {E s t v : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n)
    (hsv : ∀ n, s n ≤ v n) (hvt : ∀ n, v n ≤ t n) (hK : ∀ n, K n ≠ 0) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) {k : ℕ}
    {Γ Λ Φ : ℕ → ℝ} {τ' D' : ℝ}
    (hW : Whp sz (fun n => {ω | ∀ u : TimeIcc s t n, sz.seqHflow n (u : ℝ) ω ∈
      sz.GoodSetN n (E n) (u : ℝ) k (Γ n) (Λ n) (Φ n) τ' D'})) :
    HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
      pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D'}) := by
  have hmeas := measurableGoodSetN d
  have hgrid : ∀ n j, j ≤ K n →
      pathP sz {ω | pathH sz s v K n j ω ∈
        sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D'}ᶜ ≤
      sz.seqP {ω | ∀ u : TimeIcc s t n, sz.seqHflow n (u : ℝ) ω ∈
        sz.GoodSetN n (E n) (u : ℝ) k (Γ n) (Λ n) (Φ n) τ' D'}ᶜ := by
    intro n j hj
    have hmem := gridGood_gridTime_mem hsv hvt hK n j hj
    have hG := (hmeas sz n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D').compl
    have h1 := Measure.map_apply (μ := pathP sz) (gridGood_measurable_pathH sz s v K n j) hG
    have h2 := Measure.map_apply (μ := sz.seqP)
      (gridGood_measurable_seqHflow sz n (gridTime s v K n j)) hG
    have h3 := map_pathH_eq sz s v K n j (hs0 n) (hsv n) (hK n)
    have e1 : {ω | pathH sz s v K n j ω ∈
        sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D'}ᶜ =
        pathH sz s v K n j ⁻¹' (sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')ᶜ := by
      ext ω; simp
    rw [e1, ← h1, h3, h2]
    refine measure_mono ?_
    intro ω hω hall
    exact hω (hall ⟨gridTime s v K n j, hmem⟩)
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hI := highProbAt_iInter (pathP sz) sz.size (K := fun n => Fin (K n + 1))
    (Ξ := fun n j => {ω | pathH sz s v K n j.1 ω ∈
      sz.GoodSetN n (E n) (gridTime s v K n j.1) k (Γ n) (Λ n) (Φ n) τ' D'}) (C := max C 0)
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

/-- **`gridGoodN_holds`: the pin `GridGoodN` is a theorem for every `d ≥ 3`.**  `𝔠_d` is that of
`stSEforLn_holds` (`lem:SEforLn`, `Step34Pins.lean:456`); the four conjuncts of `STSEforLnConcl` give the
levels of (D1)-(D4), `stDecayLoopU_of_step2` the far decay of the loops (Dec), `stEtermDecay` the far
decay of the `ℰ` terms (Va), (Vb), the hypotheses `hX`, `hY`, `hQ` the levels of `Ξ̂`; `(con_st_ind)`
with `STBctl_mono` gives `B ≤ 1` on `[s_n,t_n]` (used by `B^{1/6} ≤ 1` in (D2)); then
`gridGood_grid`.  The other premises of the pin (`STKbound`, `STKward`, `STLK s`) are not used. -/
theorem gridGoodN_holds (d : ℕ) : GridGoodN d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d0, h𝔠d1, H⟩ := stSEforLn_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h𝔠d0, h𝔠d1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hSE := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hU : STDecayLoopU sz (STflowE z) s t :=
    stDecayLoopU_of_step2 hd sz hκ hε hflow hs (fun n => (hst n).le) ht Cd hStep2.2.2
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n =>
    (abs_lemE_le (him n)).trans (hflow.2 n).1
  have hB1 : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1 := by
    filter_upwards [hcon] with n hn u hu
    have hBt : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
    have hlt : sz.Bctl n (t n) < 1 := by
      by_contra hge
      have h1 : (1 : ℝ) ≤ sz.Bctl n (t n) := not_lt.1 hge
      have h2 : (1 : ℝ) ≤ (sz.Bctl n (t n)) ^ 𝔠d := Real.one_le_rpow h1 h𝔠d0.le
      linarith [hn.1, hn.2]
    exact (STBctl_mono sz n hu (ht1 n)).trans hlt.le
  intro v hsv hvt K hK0 k hk Λ Φ hΛ hΦ hX hY q hq hQ C hC ε₁ hε₁ τ' hτ' D' hD'
  have hW := gridGood_whp_uniform hd sz hκ hE hflow.1 hs (fun n => (hst n).le) ht1 hB1 hSE hU hk
    hΦ hX hY hq hQ hε₁ hτ' hD'
  exact gridGood_grid sz hs hsv hvt hK0 hC hW

end RBM.Gauss.Sizes

/-! ## 6. The hypotheses `hX`, `hY`, `hQ` at `Φ ≡ 1`: they follow from `STLmaxU`, `STLKU`

The levels of `GridGoodNConcl` are satisfiable: at `Φ ≡ 1` the statements `Ξ̂^{(𝓛)}_m ≺ 1`, `Ξ̂^{(𝓛-𝒦)}_m ≺ 1`
are `(Eq:LGxb)`, `(Eq:L-KGt-flow)` (the conclusions `STLmaxU`, `STLKU` of Steps 3-4, `1 + a/b ≺ 1`), and `hQ`
holds with `Λ_n = max 1 (W^{-d}B_{s_n,0})^{-1/(2q)}` (`B_{u,0}` is non-decreasing in `u`, `STBctl_mono`).
The four lemmas are used by the instance of `gridGoodN_holds` (section 7); the other gates' pins `STLmaxU`,
`STLKU` stay hypotheses there. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section LevelsOne

variable {d : ℕ}

/-- `Prec` from its `w.h.p.` form for every exponent (`Prec.whp` converse). -/
private theorem gridGood_prec_of_whp (sz : Sizes d) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : ∀ τ : ℝ, 0 < τ → Whp sz (fun n => {ω | ∀ u : U n,
      ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω})) : Prec sz ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (le_of_eq ?_) hn
  congr 1
  ext ω
  simp [badSetAt]

private theorem gridGood_one_add_le {a : ℝ} (ha : 2 ≤ a) : 1 + a ≤ a * a := by nlinarith

/-- `Ξ̂^{(𝓛)}_m ≺ 1` on the window from `STLmaxU`. -/
private theorem gridGood_prec_XiL_one (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hL : STLmaxU sz E s t) {m : ℕ} (hm : 1 ≤ m) :
    Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine gridGood_prec_of_whp sz fun τ hτ => ?_
  have hw := (hL m hm).whp sz (half_pos hτ)
  refine hw.mono ?_
  filter_upwards [((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop 2] with n hN2 ω hω u
  have hBpos : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz ((u.2.2).trans_lt (ht1 n))
  have hpb : 0 < (sz.Bctl n (u : ℝ)) ^ (m - 1) := pow_pos hBpos _
  have hmax : STmaxL sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (u : ℝ)) ^ (m - 1) :=
    Finset.sup'_le _ _ fun p _ => hω (u, p)
  have hdiv : STmaxL sz n (E n) (u : ℝ) m ω / (sz.Bctl n (u : ℝ)) ^ (m - 1) ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [div_le_iff₀ hpb]; exact hmax
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' hN0 (by linarith)]; ring_nf
  calc STXiL sz n (E n) (u : ℝ) m ω = 1 + STmaxL sz n (E n) (u : ℝ) m ω /
        (sz.Bctl n (u : ℝ)) ^ (m - 1) := rfl
    _ ≤ 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
    _ ≤ _ := gridGood_one_add_le hN2
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * 1 := by rw [hsq, mul_one]

/-- `Ξ̂^{(𝓛-𝒦)}_m ≺ 1` on the window from `STLKU`. -/
private theorem gridGood_prec_XiLK_one (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hL : STLKU sz E s t) {m : ℕ} (hm : 1 ≤ m) :
    Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine gridGood_prec_of_whp sz fun τ hτ => ?_
  have hw := (hL m hm).whp sz (half_pos hτ)
  refine hw.mono ?_
  filter_upwards [((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop 2] with n hN2 ω hω u
  have hBpos : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz ((u.2.2).trans_lt (ht1 n))
  have hpb : 0 < (sz.Bctl n (u : ℝ)) ^ m := pow_pos hBpos _
  have hmax : STmaxLK sz n (E n) (u : ℝ) m ω ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      (sz.Bctl n (u : ℝ)) ^ m :=
    Finset.sup'_le _ _ fun p _ => hω (u, p)
  have hdiv : STmaxLK sz n (E n) (u : ℝ) m ω / (sz.Bctl n (u : ℝ)) ^ m ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [div_le_iff₀ hpb]; exact hmax
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' hN0 (by linarith)]; ring_nf
  calc STXiLK sz n (E n) (u : ℝ) m ω = 1 + STmaxLK sz n (E n) (u : ℝ) m ω /
        (sz.Bctl n (u : ℝ)) ^ m := rfl
    _ ≤ 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
    _ ≤ _ := gridGood_one_add_le hN2
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * 1 := by rw [hsq, mul_one]

/-- `hQ` at `Φ ≡ 1`: `Ξ̂_{a} (Ξ̂_{b}/B)^{r} ≺ max 1 B_s^{-r}` for `0 ≤ r ≤ 1` from `Ξ̂_a ≺ 1`, `Ξ̂_b ≺ 1`
(`B_{u,0}` is non-decreasing in `u`). -/
private theorem gridGood_prec_Q_one (sz : Sizes d) (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ}
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) {a b : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiL sz n (E n) (u : ℝ) a ω)
      (fun _ _ _ => (1 : ℝ)))
    (hb : Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiL sz n (E n) (u : ℝ) b ω)
      (fun _ _ _ => (1 : ℝ))) :
    Prec sz (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) a ω *
        (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ r)
      (fun n _ _ => max 1 ((sz.Bctl n (s n)) ^ (-r))) := by
  refine gridGood_prec_of_whp sz fun τ hτ => ?_
  have hw := gridGood_whp_and (tendsto_size sz hsz) (ha.whp sz (half_pos hτ)) (hb.whp sz (half_pos hτ))
  refine hw.mono ?_
  filter_upwards with n ω ⟨hωa, hωb⟩ u
  have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (ht1 n)
  have hBu : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz ((hst n).trans_lt (ht1 n))
  have hBsu : sz.Bctl n (s n) ≤ sz.Bctl n (u : ℝ) := STBctl_mono sz n u.2.1 hu1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hXa := hωa u
  have hXb := hωb u
  rw [mul_one] at hXa hXb
  have hXb0 : 0 ≤ STXiL sz n (E n) (u : ℝ) b ω :=
    zero_le_one.trans (gridGood_one_le_STXiL sz b ω hBu)
  have hXa0 : 0 ≤ STXiL sz n (E n) (u : ℝ) a ω :=
    zero_le_one.trans (gridGood_one_le_STXiL sz a ω hBu)
  set Nh : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hNh
  have hNh1 : 1 ≤ Nh := Real.one_le_rpow hN1 (half_pos hτ).le
  have h1 : (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ r ≤ (Nh / sz.Bctl n (u : ℝ)) ^ r :=
    Real.rpow_le_rpow (div_nonneg hXb0 hBu.le) (div_le_div_of_nonneg_right hXb hBu.le) hr0
  have h2 : (Nh / sz.Bctl n (u : ℝ)) ^ r = Nh ^ r * (sz.Bctl n (u : ℝ)) ^ (-r) := by
    rw [Real.div_rpow (by linarith) hBu.le, Real.rpow_neg hBu.le, div_eq_mul_inv]
  have h3 : (sz.Bctl n (u : ℝ)) ^ (-r) ≤ (sz.Bctl n (s n)) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos hBs hBsu (by linarith)
  have h4 : Nh ^ r ≤ Nh := by
    calc Nh ^ r ≤ Nh ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNh1 hr1
      _ = Nh := Real.rpow_one _
  have hΛ : (sz.Bctl n (s n)) ^ (-r) ≤ max 1 ((sz.Bctl n (s n)) ^ (-r)) := le_max_right _ _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ = Nh * Nh := by
    rw [hNh, ← Real.rpow_add hN0]; ring_nf
  have hΛ0 : 0 ≤ max 1 ((sz.Bctl n (s n)) ^ (-r)) := zero_le_one.trans (le_max_left _ _)
  have hB0 : 0 ≤ (sz.Bctl n (u : ℝ)) ^ (-r) := Real.rpow_nonneg hBu.le _
  calc STXiL sz n (E n) (u : ℝ) a ω * (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ r
      ≤ Nh * (Nh ^ r * (sz.Bctl n (u : ℝ)) ^ (-r)) := by
        rw [← h2]
        exact mul_le_mul hXa h1 (Real.rpow_nonneg (div_nonneg hXb0 hBu.le) _) (by linarith)
    _ ≤ Nh * (Nh * max 1 ((sz.Bctl n (s n)) ^ (-r))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact mul_le_mul h4 (h3.trans hΛ) hB0 (by linarith)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * max 1 ((sz.Bctl n (s n)) ^ (-r)) := by rw [hsq]; ring

end LevelsOne

end RBM.Gauss.Sizes

/-! ## 7. Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; at `n = 0`:
`L = 4`, `W = 32`, `N = 2097152`), the flow `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, the window
`s ≡ 0`, `t ≡ 1/16` (`1/16 ≤ lemT z0`, `(con_st_ind)` from `sz0_con`), the grid end `v ≡ 1/32`, the grid size
`K ≡ 4` (`Δ = 1/128`, `u_j = j/128`, `j ≤ 4`, `K + 1 = 5 ≤ N^1`), `C_d = 1`.
* `measurableGoodSetN`, `goodExitMeasN`: applied at `sz0`, `n = 0`, `E = 1/2`, `k = 2`, `Γ = 4`, `Λ = 3`, `Φ = 1`,
  `τ' = 1/2`, `D' = 1` and at the exit time of the grid walk.
* `gridGoodN_holds`: applied through `inst_ing` (the merged shape of the instances of `STIngR`), at `k = 2`, `q = 5`,
  `ε = 1/10`, `τ' = 1/2`, `D' = 1`, `Φ ≡ 1`, `Λ_n = max 1 (W^{-d}B_{0,0})^{-1/10}`.  The hypotheses of `STIngR`
  that are other gates' outputs stay hypotheses of the example (`STKbound`, `STKward`, `STLK`, `STStep2Concl`) and so do
  the Step 3-4 conclusions `STLmaxU`, `STLKU`; the levels `hX`, `hY`, `hQ` are *discharged* from them
  (`gridGood_prec_XiL_one`, `gridGood_prec_XiLK_one`, `gridGood_prec_Q_one`), `Λ_n ≥ 1`, `Φ ≥ 1`, `0 ≤ s ≤ v ≤ t`,
  `K ≠ 0`, `K + 1 ≤ N^C` are proved at the data.  Then the good event is eventually nonempty
  (`HighProbAt.nonempty`): for large `n` there is a sample of the grid walk that is in the good set at every grid time. -/

namespace RBM.Gauss.GridGoodNInst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step34Inst

/-- The grid end `v ≡ 1/32`. -/
def vg : ℕ → ℝ := fun _ => 1 / 32

/-- The grid size `K ≡ 4`. -/
def Kg : ℕ → ℕ := fun _ => 4

/-- The grid is nondegenerate: `Δ = 1/128 > 0`, `u_0 = 0`, `u_1 = 1/128`, `u_4 = 1/32 ≤ 1/16`. -/
theorem grid_data : gridStep sInst vg Kg 0 = 1 / 128 ∧ gridTime sInst vg Kg 0 0 = 0 ∧
    gridTime sInst vg Kg 0 1 = 1 / 128 ∧ gridTime sInst vg Kg 0 4 = 1 / 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gridStep, gridTime, sInst, vg, Kg]

/-- The nondegenerate size data: `d = 3`, `L = 4`, `W = 32`, `N = 2097152`, `K + 1 = 5`. -/
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ Kg 0 + 1 = 5 :=
  ⟨sz0_values.1, sz0_values.2.1, sz0_values.2.2.1, rfl⟩

/-- **`measurableGoodSetN` at `sz0`**: `d = 3`, `n = 0`, `E = 1/2`, `u = 1/32`, `k = 2`, `Γ = 4`, `Λ = 3`, `Φ = 1`,
`τ' = 1/2`, `D' = 1`. -/
example : MeasurableSet (sz0.GoodSetN 0 (1 / 2) (1 / 32) 2 4 3 1 (1 / 2) 1) :=
  measurableGoodSetN 3 sz0 0 (1 / 2) (1 / 32) 2 4 3 1 (1 / 2) 1

/-- **`goodExitMeasN` at `sz0`**: for every `j`, `{j < goodExitTauN}` is `filt sz0 j`-measurable (grid
`(s, v, K) = (0, 1/32, 4)`, `k = 2`, levels `(4, 3, 1)`, `τ' = 1/2`, `D' = 1`, `n = 0`). -/
example (j : ℕ) : MeasurableSet[filt sz0 j] {ω | j < goodExitTauN sz0 (fun _ => 1 / 2) sInst vg Kg 2
    (fun _ => 4) (fun _ => 3) (fun _ => 1) (1 / 2) 1 0 ω} :=
  goodExitMeasN sz0 (fun _ => 1 / 2) sInst vg Kg 0 2 (fun _ => 4) (fun _ => 3) (fun _ => 1) (1 / 2) 1 j

example : GoodExitMeasN sz0 (fun _ => 1 / 2) sInst vg Kg := goodExitMeasN sz0 _ _ _ _

/-- The exit time lemmas at the instance: the exit time is `≤ K 0 = 4`, and it is `4` when the grid state is in
the good set at every `j ≤ 4`. -/
example (ω : PathΩ sz0) : goodExitTauN sz0 (fun _ => 1 / 2) sInst vg Kg 2 (fun _ => 4) (fun _ => 3)
    (fun _ => 1) (1 / 2) 1 0 ω ≤ 4 :=
  gridExitTauN_le ω

example (ω : PathΩ sz0)
    (h : ∀ j ≤ Kg 0, pathH sz0 sInst vg Kg 0 j ω ∈ sz0.GoodSetN 0 (1 / 2) (gridTime sInst vg Kg 0 j) 2 4 3 1
      (1 / 2) 1) :
    goodExitTauN sz0 (fun _ => 1 / 2) sInst vg Kg 2 (fun _ => 4) (fun _ => 3) (fun _ => 1) (1 / 2) 1 0 ω = 4 :=
  gridExitTauN_eq_of_forall_mem h

example (ω : PathΩ sz0) (j : ℕ)
    (h : j < goodExitTauN sz0 (fun _ => 1 / 2) sInst vg Kg 2 (fun _ => 4) (fun _ => 3) (fun _ => 1)
      (1 / 2) 1 0 ω) :
    pathH sz0 sInst vg Kg 0 j ω ∈ sz0.GoodSetN 0 (1 / 2) (gridTime sInst vg Kg 0 j) 2 4 3 1 (1 / 2) 1 :=
  mem_of_lt_gridExitTauN h

theorem tInst_lt_one : ∀ n, tInst n < 1 := fun n => by simp only [tInst]; norm_num

/-- **`gridGoodN_holds` at `sz0`** (`k = 2`, `q = 5`, `K ≡ 4`, `v ≡ 1/32`, `ε = 1/10`, `τ' = 1/2`, `D' = 1`,
`Φ ≡ 1`, `Λ_n = max 1 (W^{-d}B_{0,0})^{-1/10}`): with high probability the grid walk stays in `GoodSetN`
at every `j ≤ 4`.  The hypotheses `STKbound`, `STKward`, `STLK`, `STStep2Concl` of `STIngR` and the Step 3-4
conclusions `STLmaxU`, `STLKU` (other gates' pins) are hypotheses; everything else is discharged. -/
theorem gridGood_instance (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :
    HighProbAt (pathP sz0) sz0.size (fun n => {ω | ∀ j ≤ Kg n,
      pathH sz0 sInst vg Kg n j ω ∈ sz0.GoodSetN n (STflowE z0 n) (gridTime sInst vg Kg n j) k
        (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ))
        (max 1 ((sz0.Bctl n (sInst n)) ^ (-(1 / (2 * ((5 : ℕ) : ℝ))))))
        1 (1 / 2) 1}) := by
  obtain ⟨𝔠d, -, -, hG⟩ := inst_ing STAny (fun sz E s t => GridGoodNConcl sz E s t) (gridGoodN_holds 3)
    sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht trivial sz0_con 1 one_pos
  have hGG := hG hKb hKw hLK hStep2
  have hst : ∀ n, sInst n ≤ tInst n := fun n => (sz0_hst n).le
  have hXone : ∀ m : ℕ, 1 ≤ m →
      Prec sz0 (U := fun n => TimeIcc sInst tInst n)
        (fun n u ω => STXiL sz0 n (STflowE z0 n) (u : ℝ) m ω) (fun _ _ _ => (1 : ℝ)) :=
    fun m hm => gridGood_prec_XiL_one sz0 sz0_tendsto hst tInst_lt_one hL hm
  refine hGG vg (fun n => by simp only [sInst, vg]; norm_num) (fun n => by simp only [tInst, vg]; norm_num)
    Kg (fun n => by simp [Kg]) k hk (fun n => max 1 ((sz0.Bctl n (sInst n)) ^ (-(1 / (2 * ((5 : ℕ) : ℝ))))))
    (fun _ => 1) (fun n => le_max_left _ _) (fun _ => le_rfl)
    (fun m hm1 _ => hXone m hm1)
    (fun m hm1 _ => gridGood_prec_XiLK_one sz0 sz0_tendsto hst tInst_lt_one hLKU hm1) 5 (by norm_num)
    (gridGood_prec_Q_one sz0 sz0_tendsto hst tInst_lt_one (by positivity)
      (by norm_num) (hXone (2 * k - 1) (by omega)) (hXone (4 * 5) (by norm_num)))
    1 ?_ (1 / 10) (by norm_num) (1 / 2) (by norm_num) 1 one_pos
  filter_upwards [sz0_tendsto.eventually_ge_atTop (5 : ℝ)] with n hn
  rw [Real.rpow_one]
  simpa [Kg] using hn

/-- The good event of the instance is eventually nonempty: for large `n` some sample of the grid walk is in
`GoodSetN` at every grid time `j ≤ 4` (so the good set is nonempty at each grid time). -/
theorem gridGood_instance_nonempty (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0))
    (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :
    ∀ᶠ n in atTop, ∃ ω : PathΩ sz0, ∀ j ≤ Kg n,
      pathH sz0 sInst vg Kg n j ω ∈ sz0.GoodSetN n (STflowE z0 n) (gridTime sInst vg Kg n j) k
        (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ))
        (max 1 ((sz0.Bctl n (sInst n)) ^ (-(1 / (2 * ((5 : ℕ) : ℝ))))))
        1 (1 / 2) 1 :=
  (gridGood_instance k hk hKb hKw hLK hStep2 hL hLKU).nonempty (tendsto_size sz0 sz0_tendsto)
    (measure_univ) |>.mono fun n hn => hn

/-- The instance at the minimal loop length `k = 2` (no `l ∈ [3,k]`, empty sum over `n'`) and at `k = 4` (`l ∈ {3,4}`,
`n' = 3`): the clauses (D1), (D2) are not vacuous at `k = 4`. -/
example : Finset.Icc 3 2 = ∅ ∧ Finset.Icc ((2 + 1) / 2 + 1) (2 - 1) = ∅ ∧ Finset.Icc 3 4 = {3, 4} ∧
    Finset.Icc ((4 + 1) / 2 + 1) (4 - 1) = {3} := by decide

example (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :=
  gridGood_instance 2 le_rfl hKb hKw hLK hStep2 hL hLKU

example (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :=
  gridGood_instance 4 (by norm_num) hKb hKw hLK hStep2 hL hLKU

end RBM.Gauss.GridGoodNInst

end

#print axioms RBM.Gauss.Sizes.gridGood_STmaxLM_seqHflow
#print axioms RBM.Gauss.Sizes.gridGood_STmaxLKM_seqHflow
#print axioms RBM.Gauss.Sizes.gridGood_STXiLM_seqHflow
#print axioms RBM.Gauss.Sizes.gridGood_STXiLKM_seqHflow
#print axioms RBM.Path.gridExitTauN_le
#print axioms RBM.Path.mem_of_lt_gridExitTauN
#print axioms RBM.Path.gridExitTauN_eq_of_forall_mem
#print axioms RBM.Path.gridExitTauN_measurableSet
#print axioms RBM.Gauss.Sizes.measurableGoodSetN
#print axioms RBM.Path.goodExitMeasN
#print axioms RBM.Gauss.Sizes.gridGoodN_holds
#print axioms RBM.Gauss.GridGoodNInst.grid_data
#print axioms RBM.Gauss.GridGoodNInst.tInst_lt_one
#print axioms RBM.Gauss.GridGoodNInst.gridGood_instance
#print axioms RBM.Gauss.GridGoodNInst.gridGood_instance_nonempty
