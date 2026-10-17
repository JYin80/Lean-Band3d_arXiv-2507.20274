/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.DecayGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Induction.SEforLn2

/-!
# `lem:SEforLn` over the flow carrier (BA-U row U2, ticket T2480, U2a)

Additive generic form of `Induction/SEforLn1.lean` and `Induction/SEforLn2.lean` (none edited): the four estimates of the
`ℰ`-terms of `lem:SEforLn` (`3_5:1017-1046`) and the ingredient pin `STSEforLngL` (`Chain/Step34Gen.lean:404`), over a flow
matrix `Cm : Step2Mat sz`, a flow matrix family `Hf` and a probability law `μ`.

* **The class `SEforLnGen_Facts`** (target 3, `T2480_SEforLnFacts`) collects the carrier facts that replace the band objects:
  the loop form at `ztOf` (in place of `|E| < 2`, `zt E`, `etaT E`; the contraction inequality `stContractM_holds` then
  applies), a Hermitian flow matrix, the two compatibility facts of U3s1, the one Ward text of U1s1 (the rotation of `𝒦`), the
  row and column sums and the support of `S` (in place of `SB`), `Im m ≤ 1` (in place of `norm_mE`) and the one-loop value
  `𝒦^{(1)}_σ = m_σ` (in place of `KLK_one`).  `seforLnGen_facts_band` discharges it at `(STFlow, bandStep2Mat ∘ STflowE, seqHflow)`.
* **Parts (1)-(4)** `stSEforLn_part1g` ... `stSEforLn_part4g` and `stSEforLnConclgL_of` (target 4), the pin
  `stSEforLngL_of` (target 5, every regime `R`: the proof reads none).
* Private helpers of the band files are reused by `open private` (precedent `Chain/DecayGen.lean:45-47`); the ones that mention a
  band object are restated under the stem `SEforLnGen_`.  The `ℰ`-term decays (target 6) are in `Chain/SEforLnGen2.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private SEforLn1_exists_ofFn SEforLn1_loopL_rotate_iter SEforLn1_loopOf_eq SEforLn1_cut_rotate SEforLn1_n12
  SEforLn1_n12_sum SEforLn1_R_le SEforLn1_arith1 SEforLn1_of_subset SEforLn1_sum_pairs SEforLn1_arith2 from RBM3D.Induction.SEforLn1
open private SEforLn2_Bctl_ge_inv SEforLn2_WD SEforLn2_conU SEforLn2_n12 SEforLn2_n12_sum SEforLn2_arith_long
  SEforLn2_arith_two SEforLn2_final SEforLn2_eeLoop SEforLn2_arith4 SEforLn2_R_le SEforLn2_sum_pairs from RBM3D.Induction.SEforLn2
open private DecayLoopB_SB_eq_zero from RBM3D.Induction.DecayLoopB

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 3: the class `SEforLnGen_Facts` -/

/-- **Target 3, class `SEforLnGen_Facts`** (`T2480_SEforLnFacts`): the carrier facts of a flow family `(Flow, mkM, Hf)` that replace
the band objects of `SEforLn1/2` and `DecayLoopB` §9: the loop form at `ztOf` (in place of `|E| < 2`, `zt E`, `etaT E`; the
contraction inequality `stContractM_holds` then applies), a Hermitian flow matrix, the two compatibility facts of U3s1, the one Ward
text of U1s1 (the rotation of `𝒦`), the row and column sums and the support of `S` (in place of `SB`), `Im m ≤ 1` (in place of
`norm_mE`) and the one-loop value `𝒦^{(1)}_σ = m_σ` (in place of `KLK_one`; the first conjunct of T2478's `OneLoop` text). -/
def SEforLnGen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    (∃ E : ℕ → ℝ, StepDecompGen_LoopForm (mkM sz z) E) ∧
    (∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf sz z n τ ω).IsHermitian) ∧
    Step34Gen_LCompat (mkM sz z) (Hf sz z) ∧ Step34Gen_KCompat (mkM sz z) ∧
    ZeroModeGen_WardCls sz (mkM sz z).toFlowFM ∧
    (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1) ∧
    (∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1) ∧
    (∀ (n : ℕ) (a b : Zd d (sz.L n)), (mkM sz z).S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) ∧
    (∀ n : ℕ, ((mkM sz z).m n).im ≤ 1) ∧
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      (mkM sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg (mkM sz z) n σ

/-! ## 2. The facts at hand, rotation and the contraction inequality over a carrier -/

section Core

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
  (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- The carrier facts of target 3 read by the deterministic cores (private bundle of the explicit hypotheses of the public
parts; `E` is the energy of `StepDecompGen_LoopForm`). -/
private structure SEforLnGen_Hyp {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (E : ℕ → ℝ) : Prop where
  loop : StepDecompGen_LoopForm Cm E
  herm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian
  lc : Step34Gen_LCompat Cm Hf
  kc : Step34Gen_KCompat Cm
  ward : ZeroModeGen_WardCls sz Cm.toFlowFM
  row : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1
  col : ∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1

variable {Cm Hf}

/-- `η_τ > 0` for `τ < 1`, from `0 < Im m` and `η_τ = (1 - τ) Im m` (the loop form). -/
private theorem SEforLnGen_eta_pos {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ < 1) :
    0 < Cm.eta n τ := by
  rw [(hC.loop n).2.2.2 τ]
  exact mul_pos (by linarith) (hC.loop n).1

private theorem SEforLnGen_LI_eq {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ)
    (I : LoopIdx (Zd d (sz.L n))) :
    STLIg Cm Hf n τ ω I =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hf n τ ω)) (ztOf (Cm.m n) (E n) τ) I :=
  (hC.loop n).2.2.1 τ (Hf n τ ω) I

/-- Rotation of a family on list indices from the rotation by one step. -/
private theorem SEforLnGen_rotate_of_fam {α : Type*} {T : LoopIdx α → ℂ}
    (h : ∀ (s : Bool) (b : α) (σ : List Bool) (a : List α), σ.length = a.length →
      T ⟨s :: σ, b :: a⟩ = T ⟨σ ++ [s], a ++ [b]⟩) :
    ∀ (j : ℕ) (σ : List Bool) (a : List α), σ.length = a.length → T ⟨σ.rotate j, a.rotate j⟩ = T ⟨σ, a⟩ := by
  intro j
  induction j with
  | zero => intro σ a _; simp
  | succ j ih =>
    intro σ a hlen
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at hlen
      | cons b a =>
        have h' : σ.length = a.length := by simpa using hlen
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (h s b σ a h').symm

/-- `𝓛` of the carrier is invariant under rotation (`SEforLn1_STLI_rotate`; trace cyclicity through the loop form). -/
private theorem SEforLnGen_LI_rotate {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (j : ℕ)
    (σ : List Bool) (a : List (Zd d (sz.L n))) (h : σ.length = a.length) :
    STLIg Cm Hf n τ ω ⟨σ.rotate j, a.rotate j⟩ = STLIg Cm Hf n τ ω ⟨σ, a⟩ := by
  rw [SEforLnGen_LI_eq hC, SEforLnGen_LI_eq hC]
  exact SEforLn1_loopL_rotate_iter j σ a h

/-- `𝒦` of the carrier is invariant under rotation (`SEforLn1_STKI_rotate`): `𝒦_I` is the `TK` of `ZeroModeGen_WardCls`
(through `Step34Gen_KCompat`), a Ward family. -/
private theorem SEforLnGen_KI_rotate {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) (j : ℕ) (σ : List Bool) (a : List (Zd d (sz.L n))) (h : σ.length = a.length) :
    STKIg Cm n τ ⟨σ.rotate j, a.rotate j⟩ = STKIg Cm n τ ⟨σ, a⟩ := by
  obtain ⟨TL, TK, hTL, hTK, hfL, hfK⟩ := hC.ward n τ h0 h1 ω
  have hKI : ∀ (σ : List Bool) (a : List (Zd d (sz.L n))), σ.length = a.length →
      Cm.KI n τ ⟨σ, a⟩ = TK ⟨σ, a⟩ := by
    intro σ a h
    obtain ⟨f, hf⟩ := SEforLn1_exists_ofFn σ (rfl : σ.length = σ.length)
    obtain ⟨g, hg⟩ := SEforLn1_exists_ofFn a h.symm
    have e : (⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))) = KLloopOf d (sz.L n) f g := by
      simp [KLloopOf, hf, hg]
    rw [e, ← hC.kc n τ f g]
    exact hTK _ f g
  have hlen : (σ.rotate j).length = (a.rotate j).length := by simp [h]
  unfold STKIg
  rw [hKI _ _ hlen, hKI _ _ h]
  exact SEforLnGen_rotate_of_fam hfK.1 j σ a h

/-- `max_{σ,a} |𝓛^{(k)}|` of the carrier is the `max` of `Contract_maxLoopM` at the flow matrix and the spectral value. -/
private theorem SEforLnGen_maxL_eq {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (k : ℕ) :
    Contract_maxLoopM d (sz.L n) (sz.W n) (Hf n τ ω) (ztOf (Cm.m n) (E n) τ) k =
      STmaxLg Cm.toFlowFM n τ k ω := by
  unfold Contract_maxLoopM STmaxLg
  refine Finset.sup'_congr _ rfl fun p _ => ?_
  have h1 : Cm.toFlowFM.L n τ p.1 p.2 ω = STLIg Cm Hf n τ ω (loopOf p.1 p.2) := hC.lc n τ p.1 p.2 ω
  rw [h1, SEforLnGen_LI_eq hC]
  change ‖loopM d (sz.L n) (sz.W n) _ _ p.1 p.2‖ = ‖loopL d (sz.L n) (sz.W n) _ _ (loopOf p.1 p.2)‖
  rw [loopM_eq_loopL]

/-- `(𝓛 - 𝒦)` of a `loopOf` index (`SEforLn1_STLKI_eq`). -/
private theorem SEforLnGen_STLKI_eq {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLKIg Cm Hf n τ ω (loopOf σ a) = Cm.toFlowFM.L n τ σ a ω - Cm.toFlowFM.K n τ σ a := by
  have h1 : Cm.toFlowFM.L n τ σ a ω = STLIg Cm Hf n τ ω (loopOf σ a) := hC.lc n τ σ a ω
  have h2 : Cm.toFlowFM.K n τ σ a = STKIg Cm n τ (loopOf σ a) := hC.kc n τ σ a
  rw [h1, h2]
  rfl


private theorem SEforLnGen_hz {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ < 1) :
    0 < (ztOf (Cm.m n) (E n) τ).im := by
  rw [ztOf_im, ← (hC.loop n).2.2.2 τ]
  exact SEforLnGen_eta_pos hC n hτ

/-- **The first contraction inequality** (`(yi2oslxj2)`, `stContractM_holds`) at the flow matrix `Hf n τ ω` and the spectral
value `ztOf (Cm.m n) (E n) τ`: for a loop of length `m` and `1 ≤ k ≤ m - 1`,
`Σ_x |𝓛(σ, (a, x))| ≤ (W^d η_τ)⁻¹ (max|𝓛^{(2k-1)}| max|𝓛^{(2m-2k-1)}|)^{1/2}`. -/
private theorem SEforLnGen_contract1 {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ < 1)
    (ω : sz.SeqΩ) {m k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), ‖STLIg Cm Hf n τ ω ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω * STmaxLg Cm.toFlowFM n τ (2 * m - 2 * k - 1) ω) ^ (1 / 2 : ℝ) := by
  have h := (stContractM_holds d (sz.L n) (sz.W n) (Hf n τ ω) (ztOf (Cm.m n) (E n) τ) (hC.herm n τ ω)
    (SEforLnGen_hz hC n hτ)).1 m k hk hkm σ a
  rw [ztOf_im, ← (hC.loop n).2.2.2 τ, SEforLnGen_maxL_eq hC, SEforLnGen_maxL_eq hC] at h
  simpa only [SEforLnGen_LI_eq hC] using h

/-- **The second contraction inequality** (`(u2jzooi-2)`, `stContractM_holds`) at the flow matrix and spectral value. -/
private theorem SEforLnGen_contract2 {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ < 1)
    (ω : sz.SeqΩ) {m k l p : ℕ} (j : Fin (m - 1)) (C : ℝ) (hm : 4 ≤ m) (hp : 1 ≤ p) (hk : 1 ≤ k) (hkj : k < j.val + 1)
    (hjl : j.val + 1 < l) (hlm : l + 1 ≤ m) (hC0 : 0 ≤ C) (𝒜 : Zd d (sz.L n) → Finset (Zd d (sz.L n)))
    (hcard : ∀ x, ((𝒜 x).card : ℝ) ≤ C) (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), ∑ y ∈ 𝒜 x,
        ‖STLIg Cm Hf n τ ω ⟨List.ofFn σ, List.ofFn (Function.update a j y) ++ [x]⟩‖ ≤
      C * (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω * STmaxLg Cm.toFlowFM n τ (2 * m - 2 * l - 1) ω) ^ (1 / 2 : ℝ) *
        STmaxLg Cm.toFlowFM n τ (2 * (l - k) * p) ω ^ (1 / (2 * (p : ℝ))) := by
  have h := (stContractM_holds d (sz.L n) (sz.W n) (Hf n τ ω) (ztOf (Cm.m n) (E n) τ) (hC.herm n τ ω)
    (SEforLnGen_hz hC n hτ)).2 m k l p j C hm hp hk hkj hjl hlm hC0 𝒜 hcard σ a
  rw [ztOf_im, ← (hC.loop n).2.2.2 τ, SEforLnGen_maxL_eq hC, SEforLnGen_maxL_eq hC, SEforLnGen_maxL_eq hC] at h
  simpa only [SEforLnGen_LI_eq hC] using h

/-! ### Nonnegativity and the normalised controls -/

variable (C : FlowFM sz)

private theorem SEforLnGen_maxL_nonneg (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : 0 ≤ STmaxLg C n v k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖C.L n v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

private theorem SEforLnGen_maxLK_nonneg (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : 0 ≤ STmaxLKg C n v k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖C.L n v p.1 p.2 ω - C.K n v p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

private theorem SEforLnGen_maxL_le (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    STmaxLg C n u m ω ≤ sz.Bctl n u ^ (m - 1) * STXiLg C n u m ω := by
  unfold STXiLg
  have h0 := SEforLnGen_maxL_nonneg C n u m ω
  have hp : 0 < sz.Bctl n u ^ (m - 1) := pow_pos hB _
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne']
  linarith [hp.le]

private theorem SEforLnGen_maxLK_le (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    STmaxLKg C n u m ω ≤ sz.Bctl n u ^ m * STXiLKg C n u m ω := by
  unfold STXiLKg
  have h0 := SEforLnGen_maxLK_nonneg C n u m ω
  have hp : 0 < sz.Bctl n u ^ m := pow_pos hB _
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne']
  linarith [hp.le]

private theorem SEforLnGen_one_le_XiL (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    1 ≤ STXiLg C n u m ω := by
  unfold STXiLg
  have := SEforLnGen_maxL_nonneg C n u m ω
  have : 0 ≤ STmaxLg C n u m ω / sz.Bctl n u ^ (m - 1) := by positivity
  linarith

private theorem SEforLnGen_one_le_XiLK (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    1 ≤ STXiLKg C n u m ω := by
  unfold STXiLKg
  have := SEforLnGen_maxLK_nonneg C n u m ω
  have : 0 ≤ STmaxLKg C n u m ω / sz.Bctl n u ^ m := by positivity
  linarith

/-- Every well-formed loop of length `m` is bounded by `max_{σ,a} |(𝓛-𝒦)^{(m)}|` (`SEforLn1_norm_STLKI_le`). -/
private theorem SEforLnGen_norm_STLKI_le {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ)
    (J : LoopIdx (Zd d (sz.L n))) (hJ : J.WF) : ‖STLKIg Cm Hf n τ ω J‖ ≤ STmaxLKg Cm.toFlowFM n τ J.length ω := by
  have hJ' := SEforLn1_loopOf_eq J hJ
  conv_lhs => rw [← hJ']
  rw [SEforLnGen_STLKI_eq hC]
  exact Finset.le_sup' (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Zd d (sz.L n)) =>
    ‖Cm.toFlowFM.L n τ p.1 p.2 ω - Cm.toFlowFM.K n τ p.1 p.2‖)
    (Finset.mem_univ ((fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2)),
      (fun i : Fin J.a.length => J.a[i.1])))

/-! ## 3. Part (1): `(bEwGn)` -/

/-- `Σ_{a,b} F(a) |S_{ab}| G(b) ≤ (sup F) Σ_b G(b)` (column sums of `S` at most `1`); `SEforLn1_sum_glue_left`. -/
private theorem SEforLnGen_sum_glue_left {L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hcol : ∀ b, ∑ a, ‖S a b‖ ≤ 1) (F G : Zd d L → ℝ) {M : ℝ} (hM : 0 ≤ M) (hF : ∀ a, F a ≤ M) (hG : ∀ b, 0 ≤ G b) :
    ∑ a : Zd d L, ∑ b : Zd d L, F a * ‖S a b‖ * G b ≤ M * ∑ b : Zd d L, G b := by
  calc ∑ a : Zd d L, ∑ b : Zd d L, F a * ‖S a b‖ * G b
      ≤ ∑ a : Zd d L, ∑ b : Zd d L, M * (‖S a b‖ * G b) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF a) (norm_nonneg _)) (hG b)
    _ = M * ∑ b : Zd d L, (∑ a : Zd d L, ‖S a b‖) * G b := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ M * ∑ b : Zd d L, G b := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) hM
        exact (mul_le_mul_of_nonneg_right (hcol b) (hG b)).trans_eq (one_mul _)

/-- `Σ_{a,b} F(a) |S_{ab}| G(b) ≤ (sup G) Σ_a F(a)` (row sums of `S` at most `1`); `SEforLn1_sum_glue_right`. -/
private theorem SEforLnGen_sum_glue_right {L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hrow : ∀ a, ∑ b, ‖S a b‖ ≤ 1) (F G : Zd d L → ℝ) {M : ℝ} (hM : 0 ≤ M) (hG : ∀ b, G b ≤ M) (hF : ∀ a, 0 ≤ F a) :
    ∑ a : Zd d L, ∑ b : Zd d L, F a * ‖S a b‖ * G b ≤ M * ∑ a : Zd d L, F a := by
  calc ∑ a : Zd d L, ∑ b : Zd d L, F a * ‖S a b‖ * G b
      ≤ ∑ a : Zd d L, ∑ b : Zd d L, M * (F a * ‖S a b‖) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [mul_comm M]
        exact mul_le_mul_of_nonneg_left (hG b) (mul_nonneg (hF a) (norm_nonneg _))
    _ = M * ∑ a : Zd d L, F a * ∑ b : Zd d L, ‖S a b‖ := by
        simp only [← Finset.mul_sum]
    _ ≤ M * ∑ a : Zd d L, F a := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) hM
        exact (mul_le_mul_of_nonneg_left (hrow a) (hF a)).trans_eq (mul_one _)

/-- `tr(G̃(σ) E_a) = (𝓛-𝒦)^{(1)}_{σ,a}` once the one-loop value `𝒦^{(1)}_σ = m_σ` holds at `(n, u)` (`SEforLn1_avgErr_eq`). -/
private theorem SEforLnGen_avgErr_eq {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ)
    (hone : ∀ (σ : Bool) (a : Zd d (sz.L n)), Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (σ : Bool) (a : Zd d (sz.L n)) :
    STavgErrg Cm Hf n u ω σ a =
      Cm.toFlowFM.L n u (fun _ : Fin 1 => σ) (fun _ => a) ω - Cm.toFlowFM.K n u (fun _ : Fin 1 => σ) (fun _ => a) := by
  have h1 : Cm.toFlowFM.L n u (fun _ : Fin 1 => σ) (fun _ => a) ω = STLIg Cm Hf n u ω ⟨[σ], [a]⟩ := by
    rw [hC.lc n u (fun _ : Fin 1 => σ) (fun _ => a) ω]
    simp [STLIg, STLIMg, KLloopOf]
  have h2 : Cm.toFlowFM.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ := hone σ a
  rw [h1, h2]
  rfl

/-- **The contraction of the glued label**: `Σ_b |𝓛(cutGlue_j^{(b)} I)| ≤ (W^d η)⁻¹ (max|𝓛^{(n₁)}| max|𝓛^{(n₂)}|)^{1/2}` for a loop of
length `k ≥ 1` and the edge `1 ≤ j ≤ k` (`SEforLn1_sum_cutGlue`). -/
private theorem SEforLnGen_sum_cutGlue {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ < 1)
    (ω : sz.SeqΩ) {k : ℕ} (hk : 1 ≤ k) (σ : List Bool) (a : List (Zd d (sz.L n)))
    (hσ : σ.length = k) (ha : a.length = k) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∑ b : Zd d (sz.L n), ‖STLIg Cm Hf n τ ω ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlue j b)‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (STn12E k).1 ω * STmaxLg Cm.toFlowFM n τ (STn12E k).2 ω) ^ (1 / 2 : ℝ) := by
  obtain ⟨σ₁, hσ₁⟩ := SEforLn1_exists_ofFn (σ.drop (j - 1) ++ σ.take j) (m := k + 1)
    (by simp [hσ]; omega)
  obtain ⟨a₁, ha₁⟩ := SEforLn1_exists_ofFn (a.drop (j - 1) ++ a.take (j - 1)) (m := k + 1 - 1)
    (by simp [ha]; omega)
  have hc := SEforLnGen_contract1 hC n hτ ω (m := k + 1) (k := (k + 1) / 2) (by omega) (by omega) σ₁ a₁
  obtain ⟨e1, e2⟩ := SEforLn1_n12 k hk
  rw [e1, e2] at hc
  refine le_trans (le_of_eq ?_) hc
  refine Finset.sum_congr rfl fun b _ => ?_
  have hrot := SEforLn1_cut_rotate σ a b (j := j) (p := j - 1) (by omega) (by omega) hj1
  have hlen : (σ.take j ++ σ.drop (j - 1)).length = (a.take (j - 1) ++ b :: a.drop (j - 1)).length := by
    simp [hσ, ha]; omega
  have := SEforLnGen_LI_rotate hC n τ ω j _ _ hlen
  rw [hrot] at this
  change ‖STLIg Cm Hf n τ ω ⟨σ.take j ++ σ.drop (j - 1), a.take (j - 1) ++ b :: a.drop (j - 1)⟩‖ = _
  rw [← this, hσ₁, ha₁]

/-- **`ℰ^{G̃,(k)}` of a loop by the contraction inequality** (`3_5:1048-1053`; `SEforLn1_det_egt`). -/
private theorem SEforLnGen_det_egt {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ < 1)
    (ω : sz.SeqΩ) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) {δ : ℝ}
    (hδ : ∀ s x, ‖STavgErrg Cm Hf n τ ω s x‖ ≤ δ) :
    ‖STegtg Cm Hf n τ ω ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
      k * δ * (Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (STn12E k).1 ω * STmaxLg Cm.toFlowFM n τ (STn12E k).2 ω) ^ (1 / 2 : ℝ) := by
  have hη : 0 < Cm.eta n τ := SEforLnGen_eta_pos hC n hτ
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set R : ℝ := (STmaxLg Cm.toFlowFM n τ (STn12E k).1 ω * STmaxLg Cm.toFlowFM n τ (STn12E k).2 ω) ^ (1 / 2 : ℝ)
    with hR
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ true 0)
  have hC' : ∀ j ∈ Finset.Icc 1 k,
      ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ‖STavgErrg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).σ.getD (j - 1) false) x‖ *
          ‖Cm.S n x y‖ *
          ‖STLIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlue j y)‖ ≤
        δ * ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * R) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine (SEforLnGen_sum_glue_left (Cm.S n) (hC.col n) _ _ hδ0 (fun x => hδ _ x) (fun y => norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (SEforLnGen_sum_cutGlue hC n hτ ω hk (List.ofFn σ) (List.ofFn a) (by simp) (by simp) hj.1 hj.2) hδ0
  unfold STegtg STegtMg
  have hlen : (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).length = k := by
    simp [LoopIdx.length]
  rw [norm_mul, hlen, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ j ∈ Finset.Icc 1 k, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        STavgErrMg Cm n τ (Hf n τ ω) ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).σ.getD (j - 1) false) x *
          Cm.S n x y *
          STLIMg Cm n τ (Hf n τ ω) ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlue j y)‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ j ∈ Finset.Icc 1 k,
          (δ * ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * R)) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)) hW.le
        refine (norm_sum_le _ _).trans ?_
        refine le_trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => le_of_eq ?_)) (hC' j hj)
        rw [norm_mul, norm_mul]
        rfl
    _ = k * δ * (Cm.eta n τ)⁻¹ * R := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp


/-- The core of part (1), for the carrier facts and times `0 ≤ s ≤ t < 1` (`SEforLn1_part1_core`). -/
private theorem SEforLnGen_part1_core {E s t : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (μ : Measure sz.SeqΩ)
    (hN : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hAvg : STAvgUgL Cm.toFlowFM μ s t) (k : ℕ) (hk : 2 ≤ k) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegtg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).1 ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).2 ω) ^
          (1 / 2 : ℝ)) := by
  have hsize := Sizes.tendsto_size sz hN
  unfold STAvgUgL PrecL at hAvg
  unfold PrecL
  refine SEforLn1_of_subset hAvg (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  filter_upwards [hsize.eventually (eventually_le_rpow (k : ℝ) (half_pos hτ)), hone] with n hkN hone_n
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < Cm.eta n (p.1 : ℝ) := SEforLnGen_eta_pos hC n hu1
  have hNa : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hδ : ∀ σ x, ‖STavgErrg Cm Hf n (p.1 : ℝ) ω σ x‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (p.1 : ℝ) := by
    intro σ x
    rw [SEforLnGen_avgErr_eq hC n _ ω (hone_n _ hu0 hu1) σ x]
    have := hno (p.1, (fun _ : Fin 1 => σ), (fun _ => x))
    simpa using this
  have hd1 := SEforLnGen_det_egt hC n hu1 ω (by omega) p.2.1 p.2.2 hδ
  have hRle := SEforLn1_R_le (k := k) hB (SEforLnGen_maxL_nonneg Cm.toFlowFM n (p.1 : ℝ) _ ω)
    (SEforLnGen_maxL_nonneg Cm.toFlowFM n (p.1 : ℝ) _ ω)
    (SEforLnGen_maxL_le Cm.toFlowFM n (p.1 : ℝ) ω _ hB) (SEforLnGen_maxL_le Cm.toFlowFM n (p.1 : ℝ) ω _ hB)
    (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n (p.1 : ℝ) ω _ hB))
    (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n (p.1 : ℝ) ω _ hB))
    (SEforLn1_n12_sum k hk)
  have hR0 : 0 ≤ (STmaxLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).1 ω *
      STmaxLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (SEforLnGen_maxL_nonneg Cm.toFlowFM n _ _ ω)
      (SEforLnGen_maxL_nonneg Cm.toFlowFM n _ _ ω)) _
  have hY0 : 0 ≤ (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).1 ω *
      STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n _ ω _ hB))
      (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n _ ω _ hB))) _
  have hfin := SEforLn1_arith1 (kk := (k : ℝ)) (a := ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (B := sz.Bctl n (p.1 : ℝ)) (η := Cm.eta n (p.1 : ℝ)) (k := k) (by omega)
    (Nat.cast_nonneg _) hkN hB.le hη hR0 hY0 hNa hRle
  rw [UnifDetDom.rpow_half_mul_rpow_half _ hτ] at hfin
  have hd2 : ‖STegtg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).1 ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).2 ω) ^
          (1 / 2 : ℝ)) := hd1.trans hfin
  exact absurd hp (not_lt.2 hd2)


/-! ## 4. Part (2): `(eq:KsimL-K)` -/

/-- The `𝒦`-piece `cutGlueR` of length `l` has its summed label last: the Ward bound applies directly (`SEforLn1_sum_cutGlueR_K`). -/
private theorem SEforLnGen_sum_cutGlueR_K (n : ℕ) {τ : ℝ} {l : ℕ} {Kw : ℝ}
    (hKw : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw)
    {m : ℕ} (σ : List Bool) (a : List (Zd d (sz.L n))) (hσ : σ.length = m) (ha : a.length = m)
    {k l' : ℕ} (hk : 1 ≤ k) (hkl : k < l') (hl' : l' ≤ m) (hl : l' - k + 1 = l) :
    ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR k l' x)‖ ≤ Kw := by
  obtain ⟨σ₁, hσ₁⟩ := SEforLn1_exists_ofFn ((σ.drop (k - 1)).take (l' - k + 1)) (m := l)
    (by simp [hσ]; omega)
  obtain ⟨a₁, ha₁⟩ := SEforLn1_exists_ofFn ((a.drop (k - 1)).take (l' - k)) (m := l - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hKw σ₁ a₁)
  simp only [LoopIdx.cutGlueR, hσ₁, ha₁]

/-- The `𝒦`-piece `cutGlueL` of length `l`: its summed label is rotated to the last position (the Ward family of
`ZeroModeGen_WardCls`), then the Ward bound applies (`SEforLn1_sum_cutGlueL_K`). -/
private theorem SEforLnGen_sum_cutGlueL_K {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h0 : 0 ≤ τ)
    (h1 : τ < 1) (ω : sz.SeqΩ) {l : ℕ} {Kw : ℝ}
    (hKw : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw)
    {m : ℕ} (σ : List Bool) (a : List (Zd d (sz.L n))) (hσ : σ.length = m) (ha : a.length = m)
    {k l' : ℕ} (hk : 1 ≤ k) (hkl : k < l') (hl' : l' ≤ m) (hl : k + m - l' + 1 = l) :
    ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL k l' x)‖ ≤ Kw := by
  obtain ⟨σ₂, hσ₂⟩ := SEforLn1_exists_ofFn (σ.drop (l' - 1) ++ σ.take k) (m := l)
    (by simp [hσ]; omega)
  obtain ⟨a₂, ha₂⟩ := SEforLn1_exists_ofFn (a.drop (l' - 1) ++ a.take (k - 1)) (m := l - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hKw σ₂ a₂)
  have hrot := SEforLn1_cut_rotate σ a x (j := k) (p := l' - 1) (by omega) (by omega) hk
  have hlen : (σ.take k ++ σ.drop (l' - 1)).length = (a.take (k - 1) ++ x :: a.drop (l' - 1)).length := by
    simp [hσ, ha]; omega
  have := SEforLnGen_KI_rotate hC n h0 h1 ω k _ _ hlen
  rw [hrot] at this
  change ‖STKIg Cm n τ ⟨σ.take k ++ σ.drop (l' - 1), a.take (k - 1) ++ x :: a.drop (l' - 1)⟩‖ = _
  rw [← this, hσ₂, ha₂]

/-- **`[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(m)}` by the Ward bound** (`3_5:1054-1061`; `SEforLn1_det_ksim`). -/
private theorem SEforLnGen_det_ksim {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {m l : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {Kw : ℝ}
    (hKw : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw) :
    ‖STksimLKg Cm Hf n τ ω l ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) ^ 2 * (2 * (STmaxLKg Cm.toFlowFM n τ (m + 2 - l) ω * Kw))) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hlen : I.length = m := by simp [hI, LoopIdx.length]
  have hσl : (List.ofFn σ).length = m := by simp
  have hal : (List.ofFn a).length = m := by simp
  set M := STmaxLKg Cm.toFlowFM n τ (m + 2 - l) ω with hM
  have hM0 : 0 ≤ M := SEforLnGen_maxLK_nonneg Cm.toFlowFM n τ _ ω
  have hKw0 : 0 ≤ Kw := (Finset.sum_nonneg fun x _ => norm_nonneg _).trans (hKw (fun _ => true) (fun _ => 0))
  have hMK : 0 ≤ M * Kw := mul_nonneg hM0 hKw0
  unfold STksimLKg STksimLKMg
  rw [norm_mul, hlen, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  refine mul_le_mul_of_nonneg_left ?_ hW.le
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine SEforLn1_sum_pairs m _ (by positivity) fun k hk l' hl' => ?_
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl'
  have hlenR : ∀ y, (I.cutGlueR k l' y).length = l' - k + 1 := fun y =>
    LoopIdx.length_cutGlueR I y hk.1 hl'.1 (hlen ▸ hl'.2)
  have hlenL : ∀ x, (I.cutGlueL k l' x).length = k + m - l' + 1 := fun x => by
    rw [LoopIdx.length_cutGlueL I x hk.1 hl'.1 (hlen ▸ hl'.2), hlen]
  have hwfL : ∀ x, (I.cutGlueL k l' x).WF := fun x => LoopIdx.wf_cutGlueL I x hIwf hk.1 hl'.1 (hlen ▸ hl'.2)
  have hwfR : ∀ y, (I.cutGlueR k l' y).WF := fun y => LoopIdx.wf_cutGlueR I y hIwf hk.1 hl'.1 (hlen ▸ hl'.2)
  have hS1 : ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖(if (I.cutGlueR k l' y).length = l then
          STLKIg Cm Hf n τ ω (I.cutGlueL k l' x) * Cm.S n x y * STKIg Cm n τ (I.cutGlueR k l' y)
        else 0)‖ ≤ M * Kw := by
    by_cases hc : l' - k + 1 = l
    · have hc' : ∀ y, (I.cutGlueR k l' y).length = l := fun y => (hlenR y).trans hc
      simp only [hc', ite_true, norm_mul]
      refine (SEforLnGen_sum_glue_left (Cm.S n) (hC.col n) (fun x => ‖STLKIg Cm Hf n τ ω (I.cutGlueL k l' x)‖)
        (fun y => ‖STKIg Cm n τ (I.cutGlueR k l' y)‖) (M := M) hM0 (fun x => ?_)
        (fun y => norm_nonneg _)).trans ?_
      · refine (SEforLnGen_norm_STLKI_le hC n τ ω _ (hwfL x)).trans (le_of_eq ?_)
        rw [hM, hlenL x]; congr 1; omega
      · exact mul_le_mul_of_nonneg_left
          (SEforLnGen_sum_cutGlueR_K n hKw (List.ofFn σ) (List.ofFn a) hσl hal hk.1 hl'.1 hl'.2 hc) hM0
    · have hc' : ∀ y, ¬ ((I.cutGlueR k l' y).length = l) := fun y h => hc ((hlenR y).symm.trans h)
      simp only [hc', ite_false, norm_zero, Finset.sum_const_zero]
      exact hMK
  have hS2 : ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖(if (I.cutGlueL k l' x).length = l then
          STKIg Cm n τ (I.cutGlueL k l' x) * Cm.S n x y * STLKIg Cm Hf n τ ω (I.cutGlueR k l' y)
        else 0)‖ ≤ M * Kw := by
    by_cases hc : k + m - l' + 1 = l
    · have hc' : ∀ x, (I.cutGlueL k l' x).length = l := fun x => (hlenL x).trans hc
      simp only [hc', ite_true, norm_mul]
      refine (SEforLnGen_sum_glue_right (Cm.S n) (hC.row n) (fun x => ‖STKIg Cm n τ (I.cutGlueL k l' x)‖)
        (fun y => ‖STLKIg Cm Hf n τ ω (I.cutGlueR k l' y)‖) (M := M) hM0 (fun y => ?_)
        (fun x => norm_nonneg _)).trans ?_
      · refine (SEforLnGen_norm_STLKI_le hC n τ ω _ (hwfR y)).trans (le_of_eq ?_)
        rw [hM, hlenR y]; congr 1; omega
      · exact mul_le_mul_of_nonneg_left
          (SEforLnGen_sum_cutGlueL_K hC n h0 h1 ω hKw (List.ofFn σ) (List.ofFn a) hσl hal hk.1 hl'.1 hl'.2 hc) hM0
    · have hc' : ∀ x, ¬ ((I.cutGlueL k l' x).length = l) := fun x h => hc ((hlenL x).symm.trans h)
      simp only [hc', ite_false, norm_zero, Finset.sum_const_zero]
      exact hMK
  calc ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ((if (I.cutGlueR k l' y).length = l then
            STLKIg Cm Hf n τ ω (I.cutGlueL k l' x) * Cm.S n x y * STKIg Cm n τ (I.cutGlueR k l' y)
          else 0) +
         (if (I.cutGlueL k l' x).length = l then
            STKIg Cm n τ (I.cutGlueL k l' x) * Cm.S n x y * STLKIg Cm Hf n τ ω (I.cutGlueR k l' y)
          else 0))‖
      ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          (‖(if (I.cutGlueR k l' y).length = l then
            STLKIg Cm Hf n τ ω (I.cutGlueL k l' x) * Cm.S n x y * STKIg Cm n τ (I.cutGlueR k l' y)
          else 0)‖ +
          ‖(if (I.cutGlueL k l' x).length = l then
            STKIg Cm n τ (I.cutGlueL k l' x) * Cm.S n x y * STLKIg Cm Hf n τ ω (I.cutGlueR k l' y)
          else 0)‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => norm_add_le _ _))
    _ ≤ M * Kw + M * Kw := by
        simp only [Finset.sum_add_distrib]
        exact add_le_add hS1 hS2
    _ = 2 * (M * Kw) := by ring

/-- The core of part (2) from the uniform `𝒦`-loop Ward bound `(wardineq_K)` at every length `≥ 2` (`SEforLn1_part2_core`). -/
private theorem SEforLnGen_part2_core {E s t : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (μ : Measure sz.SeqΩ)
    (hN : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hKw : ∀ l : ℕ, 2 ≤ l →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖STKIg Cm n (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)))
    (k : ℕ) (l : ℕ) (hl3 : 3 ≤ l) (hlk : l ≤ k) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STksimLKg Cm Hf n (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k - l + 2) ω) := by
  have hsize := Sizes.tendsto_size sz hN
  have hK := hKw l (by omega)
  unfold PrecL at hK ⊢
  refine SEforLn1_of_subset hK (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  filter_upwards [hsize.eventually (eventually_le_rpow (2 * (k : ℝ) ^ 2) (half_pos hτ))] with n hkN
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < Cm.eta n (p.1 : ℝ) := SEforLnGen_eta_pos hC n hu1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hNa : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKw' : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n (p.1 : ℝ) ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)) :=
    fun σ' a' => hno (p.1, σ', a')
  have hd1 := SEforLnGen_det_ksim hC n hu0 hu1 ω p.2.1 p.2.2 hKw'
  have hM := SEforLnGen_maxLK_le Cm.toFlowFM n (p.1 : ℝ) ω (k + 2 - l) hB
  have hfin := SEforLn1_arith2 (k := k) (l := l) (K := (k : ℝ) ^ 2)
    (a := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (B := sz.Bctl n (p.1 : ℝ)) (η := Cm.eta n (p.1 : ℝ))
    (M := STmaxLKg Cm.toFlowFM n (p.1 : ℝ) (k + 2 - l) ω)
    (Ξ := STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k + 2 - l) ω) (by omega) (by omega) hW (by linarith) hNa hB hη
    (SEforLnGen_maxLK_nonneg Cm.toFlowFM n _ _ ω) (by simpa using hM)
    (zero_le_one.trans (SEforLnGen_one_le_XiLK Cm.toFlowFM n _ ω _ hB))
  rw [UnifDetDom.rpow_half_mul_rpow_half _ hτ, show k + 2 - l = k - l + 2 by omega] at hfin
  rw [show k + 2 - l = k - l + 2 by omega] at hd1
  exact absurd hp (not_lt.2 (hd1.trans hfin))


/-- `η_τ ≤ 1 - τ` for `τ < 1` from `Im m ≤ 1` (`hηle` of `SEforLn2_sumTwo_pt`). -/
private theorem SEforLnGen_eta_le {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (him : ∀ n, (Cm.m n).im ≤ 1) (n : ℕ) {τ : ℝ}
    (hτ : τ < 1) : Cm.eta n τ ≤ 1 - τ := by
  rw [(hC.loop n).2.2.2 τ]
  have h1 := him n
  have h2 := (hC.loop n).1
  unfold etaOf
  nlinarith

/-! ## 5. Part (3): `(eq:L-KsimL-K)` -/

/-- A `PrecL` of a deterministic family is an eventual deterministic bound (each failure event is `∅` or the whole space and
`μ univ = 1 > N^{-1}` for `N ≥ 2`; `SEforLn2_det_of_prec`). -/
private theorem SEforLnGen_det_of_prec (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (hN : sz.SizeTendsto)
    {U : ℕ → Type*} (f g : ∀ n, U n → ℝ)
    (h : PrecL sz μ (U := U) (fun n u _ => f n u) (fun n u _ => g n u)) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ u, f n u ≤ ((sz.size n : ℕ) : ℝ) ^ τ * g n u := by
  have hsz := Sizes.tendsto_size sz hN
  unfold PrecL at h
  filter_upwards [h τ hτ 1 one_pos, hsz.eventually_ge_atTop 2] with n hn hn2 u
  by_contra hlt
  push Not at hlt
  have hset : badSetAt sz.size (fun n u (_ : sz.SeqΩ) => f n u) (fun n u (_ : sz.SeqΩ) => g n u) τ n =
      Set.univ := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨u, hlt⟩
  rw [hset, measure_univ] at hn
  have hN2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn2
  have hlt1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) < 1 := by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  exact absurd hn (not_le.2 (ENNReal.ofReal_lt_one.2 hlt1))

/-- **`(eq:sumtwoloop)`, second `≺`, pointwise in `(n, u)`** (a copy of the proof of `stSumTwoLoop` at a time
`u` with `(con_st_ind)` in the form of `SEforLn2_conU`): `((1-s)/(1-u))^{C_d} B^{1/5} Σ_{a₂} 𝒯_u(|a₁-a₂|) ≤
C_∞(d) B^{1/6} η_u⁻¹`. -/
private theorem SEforLnGen_sumTwo_pt (hd : 2 ≤ d) (n : ℕ) {𝔠d Cd s' u η : ℝ} (h𝔠 : 0 < 𝔠d) (hCd : 0 ≤ Cd)
    (hcc : 𝔠d * Cd ≤ 1 / 30) (hs : 0 < 1 - s') (hu1 : u < 1)
    (hB : (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s')) (hB1 : sz.Bctl n u ≤ 1) (hηpos : 0 < η) (hηle : η ≤ 1 - u)
    (hl : 0 ≤ sz.lam n) (a₁ : Zd d (sz.L n)) :
    ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd d (sz.L n),
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤
      KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * η⁻¹ := by
  have hBpos : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hu : 0 < 1 - u := by linarith
  have hρle : (1 - s') / (1 - u) ≤ (sz.Bctl n u) ^ (-𝔠d) := by
    rw [Real.rpow_neg hBpos.le, ← inv_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hBpos _) hB
  have hρ0 : 0 ≤ (1 - s') / (1 - u) := by positivity
  have h3 : ((1 - s') / (1 - u)) ^ Cd ≤ (sz.Bctl n u) ^ (-(𝔠d * Cd)) := by
    calc ((1 - s') / (1 - u)) ^ Cd ≤ ((sz.Bctl n u) ^ (-𝔠d)) ^ Cd :=
          Real.rpow_le_rpow hρ0 hρle hCd
      _ = (sz.Bctl n u) ^ (-(𝔠d * Cd)) := by
          rw [← Real.rpow_mul hBpos.le]; congr 1; ring
  have h4 : ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤
      (sz.Bctl n u) ^ (1 / 6 : ℝ) := by
    calc ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ)
        ≤ (sz.Bctl n u) ^ (-(𝔠d * Cd)) * (sz.Bctl n u) ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hBpos.le _)
      _ = (sz.Bctl n u) ^ (-(𝔠d * Cd) + 1 / 5) := (Real.rpow_add hBpos _ _).symm
      _ ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hBpos hB1 (by linarith)
  have h5 : ∑ a₂ : Zd d (sz.L n),
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) =
      ∑ a : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) a : ℝ) :=
    Equiv.sum_comp (Equiv.subLeft a₁)
      (fun a : Zd d (sz.L n) => tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) a : ℝ))
  have h6 := KDecay_sum_tailT_le (L := sz.L n) hd hl hu1
  have h7 : 0 ≤ ∑ a₂ : Zd d (sz.L n),
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) :=
    Finset.sum_nonneg fun a _ => tailT_nonneg (Nat.cast_nonneg _)
  have hη : (1 - u)⁻¹ ≤ η⁻¹ := inv_anti₀ hηpos hηle
  have hC1 : 1 ≤ KDecay_tailC d := KDecay_one_le_tailC (by omega)
  calc ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd d (sz.L n),
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)
      ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * (KDecay_tailC d / (1 - u)) :=
        mul_le_mul h4 (h5 ▸ h6) h7 (Real.rpow_nonneg hBpos.le _)
    _ = KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹ := by ring
    _ ≤ KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * η⁻¹ := by
        refine mul_le_mul_of_nonneg_left hη ?_
        have := Real.rpow_nonneg hBpos.le (1 / 6 : ℝ)
        positivity


/-- **`(eq:sumtwoloop)`, deterministic part**: if the 2-loop estimate of `STGdecayW` holds at the labels
with the loss `δ` and the exponent `D_w`, with `N W^{-D_w} ≤ B`, then, under `(con_st_ind)` at `u` (in the form
of `SEforLn2_conU`),
`Σ_{a₂} |(𝓛-𝒦)^{(2)}_{u,σ,(a₁,a₂)}| ≤ δ (C_∞(d) + 1) B^{1/6} (W^d η_u)⁻¹`. -/
private theorem SEforLnGen_sum2 {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (him : ∀ n, (Cm.m n).im ≤ 1) (hd : 2 ≤ d)
    (n : ℕ) {𝔠d Cd s' u δ Dw : ℝ} (h𝔠 : 0 < 𝔠d)
    (hCd : 0 ≤ Cd) (hcc : 𝔠d * Cd ≤ 1 / 30) (hs : 0 < 1 - s') (h0 : 0 ≤ u) (hu1 : u < 1)
    (hB : (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s')) (hB1 : sz.Bctl n u ≤ 1)
    (hl : 0 ≤ sz.lam n) (hδ : 0 ≤ δ)
    (hWD : ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ sz.Bctl n u) (ω : sz.SeqΩ)
    (hno : ∀ (σ' : Fin 2 → Bool) (a2 : Fin 2 → Zd d (sz.L n)),
      ‖Cm.toFlowFM.L n u σ' a2 ω - Cm.toFlowFM.K n u σ' a2‖ ≤
        δ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a2 0 - a2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a2 0 - a2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^
            (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw))) :
    ∀ (σ' : Fin 2 → Bool) (a' : Fin (2 - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STLKIg Cm Hf n u ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        δ * (KDecay_tailC d + 1) * (sz.Bctl n u) ^ (1 / 6 : ℝ) *
          ((((sz.W n : ℕ) : ℝ) ^ d) * Cm.eta n u)⁻¹ := by
  intro σ' a'
  obtain ⟨c, rfl⟩ : ∃ c : Zd d (sz.L n), a' = fun _ => c :=
    ⟨a' ⟨0, by norm_num⟩, funext fun i => congrArg a' (Fin.ext (by have := i.2; simp only at this ⊢; omega))⟩
  have hBpos : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hη : 0 < Cm.eta n u := SEforLnGen_eta_pos hC n hu1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hηle1u : Cm.eta n u ≤ 1 - u := SEforLnGen_eta_le hC him n hu1
  have hηle : Cm.eta n u ≤ 1 := hηle1u.trans (by linarith)
  have hη1 : 1 ≤ (Cm.eta n u)⁻¹ := one_le_inv₀ hη |>.2 hηle
  -- the pointwise bound
  have hpt : ∀ x : Zd d (sz.L n),
      ‖STLKIg Cm Hf n u ω ⟨List.ofFn σ', List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x]⟩‖ ≤
        δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
    intro x
    have hlist : (List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x] : List (Zd d (sz.L n))) =
        List.ofFn (![c, x] : Fin 2 → Zd d (sz.L n)) := by
      simp [List.ofFn_succ]
    have h1 : STLKIg Cm Hf n u ω ⟨List.ofFn σ', List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x]⟩ =
        Cm.toFlowFM.L n u σ' ![c, x] ω - Cm.toFlowFM.K n u σ' ![c, x] := by
      rw [hlist]; exact SEforLnGen_STLKI_eq hC n u ω σ' ![c, x]
    rw [h1]
    have h2 := hno σ' ![c, x]
    have e0 : (![c, x] : Fin 2 → Zd d (sz.L n)) 0 = c := rfl
    have e1 : (![c, x] : Fin 2 → Zd d (sz.L n)) 1 = x := rfl
    rw [e0, e1] at h2
    refine h2.trans (le_of_eq ?_)
    congr 1
    unfold STWB tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
    ring
  calc ∑ x : Zd d (sz.L n), ‖STLKIg Cm Hf n u ω ⟨List.ofFn σ', List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x]⟩‖
      ≤ ∑ x : Zd d (sz.L n), δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd *
          (sz.Bctl n u) ^ (1 / 5 : ℝ) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := Finset.sum_le_sum fun x _ => hpt x
    _ = δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          ∑ x : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) +
          (((sz.L n : ℕ) : ℝ) ^ d) * ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (Cm.eta n u)⁻¹) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (Cm.eta n u)⁻¹) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hδ
        · exact mul_le_mul_of_nonneg_left
            (SEforLnGen_sumTwo_pt hd n h𝔠 hCd hcc hs hu1 hB hB1 hη hηle1u hl c) (by positivity)
        · have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
            simp [Sizes.size, mul_pow]
          have h1 : (((sz.L n : ℕ) : ℝ) ^ d) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) =
              (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
            rw [hsize]; field_simp
          have h2 : sz.Bctl n u ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) := by
            have := Real.rpow_le_rpow_of_exponent_ge hBpos hB1 (by norm_num : (1 / 6 : ℝ) ≤ 1)
            simpa using this
          have h3 : (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * (Cm.eta n u)⁻¹ :=
            le_mul_of_one_le_right (Real.rpow_nonneg hBpos.le _) hη1
          rw [h1, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hWD.trans (h2.trans h3)) (by positivity)
    _ = δ * (KDecay_tailC d + 1) * (sz.Bctl n u) ^ (1 / 6 : ℝ) *
          ((((sz.W n : ℕ) : ℝ) ^ d) * Cm.eta n u)⁻¹ := by
        rw [mul_inv]; ring

/-! ## 4. The two pieces of a cut: sums over the glued label -/

/-- The glued label of a loop of length `m` is summed with the bound `Q`: for every charge vector and every
list of the other `m - 1` labels, `Σ_x |(𝓛-𝒦)^{(m)}_{σ,(a', x)}| ≤ Q`. -/
private def SEforLnGen_SumOK (Cm : Step2Mat sz) (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (m : ℕ) (Q : ℝ) : Prop :=
  ∀ (σ' : Fin m → Bool) (a' : Fin (m - 1) → Zd d (sz.L n)),
    ∑ x : Zd d (sz.L n), ‖STLKIg Cm Hf n τ ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Q

/-- The piece `cutGlueR` has its glued label last. -/
private theorem SEforLnGen_sumR (n : ℕ) {τ : ℝ} {ω : sz.SeqΩ} {r : ℕ} {Q : ℝ}
    (hQ : SEforLnGen_SumOK Cm Hf n τ ω r Q) {m : ℕ} (σ : List Bool) (a : List (Zd d (sz.L n)))
    (hσ : σ.length = m) (ha : a.length = m) {j l' : ℕ} (hj : 1 ≤ j) (hjl : j < l') (hl' : l' ≤ m)
    (hr : l' - j + 1 = r) :
    ∑ y : Zd d (sz.L n), ‖STLKIg Cm Hf n τ ω ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤ Q := by
  obtain ⟨σ₁, hσ₁⟩ := SEforLn1_exists_ofFn ((σ.drop (j - 1)).take (l' - j + 1)) (m := r)
    (by simp [hσ]; omega)
  obtain ⟨a₁, ha₁⟩ := SEforLn1_exists_ofFn ((a.drop (j - 1)).take (l' - j)) (m := r - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hQ σ₁ a₁)
  simp only [LoopIdx.cutGlueR, hσ₁, ha₁]

/-- The piece `cutGlueL`: its glued label is rotated to the last position (trace cyclicity for `𝓛`,
`KLK_rotate` for `𝒦`). -/
private theorem SEforLnGen_sumL {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Set.Ico (0 : ℝ) 1)
    {ω : sz.SeqΩ} {ℓ : ℕ} {Q : ℝ} (hQ : SEforLnGen_SumOK Cm Hf n τ ω ℓ Q) {m : ℕ} (σ : List Bool)
    (a : List (Zd d (sz.L n))) (hσ : σ.length = m) (ha : a.length = m) {j l' : ℕ} (hj : 1 ≤ j)
    (hjl : j < l') (hl' : l' ≤ m) (hl : j + m - l' + 1 = ℓ) :
    ∑ x : Zd d (sz.L n), ‖STLKIg Cm Hf n τ ω ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ ≤ Q := by
  obtain ⟨σ₂, hσ₂⟩ := SEforLn1_exists_ofFn (σ.drop (l' - 1) ++ σ.take j) (m := ℓ)
    (by simp [hσ]; omega)
  obtain ⟨a₂, ha₂⟩ := SEforLn1_exists_ofFn (a.drop (l' - 1) ++ a.take (j - 1)) (m := ℓ - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hQ σ₂ a₂)
  have hrot := SEforLn1_cut_rotate σ a x (j := j) (p := l' - 1) (by omega) (by omega) hj
  have hlen : (σ.take j ++ σ.drop (l' - 1)).length = (a.take (j - 1) ++ x :: a.drop (l' - 1)).length := by
    simp [hσ, ha]; omega
  have hL := SEforLnGen_LI_rotate hC n τ ω j _ _ hlen
  have hK := SEforLnGen_KI_rotate hC n hτ.1 hτ.2 ω j _ _ hlen
  rw [hrot] at hL hK
  change ‖STLKIg Cm Hf n τ ω ⟨σ.take j ++ σ.drop (l' - 1), a.take (j - 1) ++ x :: a.drop (l' - 1)⟩‖ = _
  have e : ∀ I, STLKIg Cm Hf n τ ω I = STLIg Cm Hf n τ ω I - STKIg Cm n τ I := fun I => rfl
  rw [e, e, ← hL, ← hK, hσ₂, ha₂]

/-- The two pieces of a cut have lengths `j + k - l' + 1` and `l' - j + 1`; a bound of the max of one by the
`Σ` of the other. -/
private theorem SEforLnGen_pair_left {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) {j l' : ℕ} (hj : 1 ≤ j) (hjl : j < l') (hl' : l' ≤ k) {Q : ℝ}
    (hQ : ∑ y : Zd d (sz.L n), ‖STLKIg Cm Hf n τ ω
        ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤ Q) :
    ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖STLKIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ *
        ‖Cm.S n x y‖ *
        ‖STLKIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤
      STmaxLKg Cm.toFlowFM n τ (j + k - l' + 1) ω * Q := by
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hlen : I.length = k := by simp [hI, LoopIdx.length]
  have hlenL : ∀ x, (I.cutGlueL j l' x).length = j + k - l' + 1 := fun x => by
    rw [LoopIdx.length_cutGlueL I x hj hjl (hlen ▸ hl'), hlen]
  have hwfL : ∀ x, (I.cutGlueL j l' x).WF := fun x => LoopIdx.wf_cutGlueL I x hIwf hj hjl (hlen ▸ hl')
  have hM0 := SEforLnGen_maxLK_nonneg Cm.toFlowFM n τ (j + k - l' + 1) ω
  refine (SEforLnGen_sum_glue_left (Cm.S n) (hC.col n) (fun x => ‖STLKIg Cm Hf n τ ω (I.cutGlueL j l' x)‖)
    (fun y => ‖STLKIg Cm Hf n τ ω (I.cutGlueR j l' y)‖) (M := STmaxLKg Cm.toFlowFM n τ (j + k - l' + 1) ω) hM0
    (fun x => ?_) (fun y => norm_nonneg _)).trans ?_
  · refine (SEforLnGen_norm_STLKI_le hC n τ ω _ (hwfL x)).trans (le_of_eq ?_)
    rw [hlenL x]
  · exact mul_le_mul_of_nonneg_left hQ hM0

private theorem SEforLnGen_pair_right {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) {j l' : ℕ} (hj : 1 ≤ j) (hjl : j < l') (hl' : l' ≤ k) {Q : ℝ}
    (hQ : ∑ x : Zd d (sz.L n), ‖STLKIg Cm Hf n τ ω
        ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ ≤ Q) :
    ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖STLKIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ *
        ‖Cm.S n x y‖ *
        ‖STLKIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤
      STmaxLKg Cm.toFlowFM n τ (l' - j + 1) ω * Q := by
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hlen : I.length = k := by simp [hI, LoopIdx.length]
  have hlenR : ∀ y, (I.cutGlueR j l' y).length = l' - j + 1 := fun y =>
    LoopIdx.length_cutGlueR I y hj hjl (hlen ▸ hl')
  have hwfR : ∀ y, (I.cutGlueR j l' y).WF := fun y => LoopIdx.wf_cutGlueR I y hIwf hj hjl (hlen ▸ hl')
  have hM0 := SEforLnGen_maxLK_nonneg Cm.toFlowFM n τ (l' - j + 1) ω
  refine (SEforLnGen_sum_glue_right (Cm.S n) (hC.row n) (fun x => ‖STLKIg Cm Hf n τ ω (I.cutGlueL j l' x)‖)
    (fun y => ‖STLKIg Cm Hf n τ ω (I.cutGlueR j l' y)‖) (M := STmaxLKg Cm.toFlowFM n τ (l' - j + 1) ω) hM0
    (fun y => ?_) (fun x => norm_nonneg _)).trans ?_
  · refine (SEforLnGen_norm_STLKI_le hC n τ ω _ (hwfR y)).trans (le_of_eq ?_)
    rw [hlenR y]
  · exact mul_le_mul_of_nonneg_left hQ hM0

/-! ## 5. The sums of the longer piece: contraction for `𝓛`, Ward for `𝒦`, and the exponent counts -/

/-- `(2⌊m/2⌋ - 1, 2m - 2⌊m/2⌋ - 1) = STn12 m`: the lengths of `(yi2oslxj2)` at the index `⌊m/2⌋`
(the paper's `⌈m/2⌉` gives the same pair up to order). -/
private theorem SEforLn2_n12 (m : ℕ) (hm : 2 ≤ m) :
    2 * (m / 2) - 1 = (STn12 m).1 ∧ 2 * m - 2 * (m / 2) - 1 = (STn12 m).2 := by
  unfold STn12
  split_ifs with h <;> simp only <;> omega

private theorem SEforLn2_n12_sum (m : ℕ) (hm : 3 ≤ m) :
    ((STn12 m).1 - 1) + ((STn12 m).2 - 1) = 2 * ((m - 1) - 1) := by
  unfold STn12
  split_ifs with h <;> simp only <;> omega

/-- **The contraction of the glued label** (`(yi2oslxj2)` at `⌊m/2⌋`, `3_5:1078-1082`): for a loop of length
`m ≥ 2` with the glued label last, `Σ_x |𝓛| ≤ (W^d η)⁻¹ (max|𝓛^{(m₁)}| max|𝓛^{(m₂)}|)^{1/2}`, `(m₁, m₂) = STn12 m`. -/
private theorem SEforLnGen_sumContract {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {m : ℕ} (hm : 2 ≤ m) (σ' : Fin m → Bool) (a' : Fin (m - 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), ‖STLIg Cm Hf n τ ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (STn12 m).1 ω * STmaxLg Cm.toFlowFM n τ (STn12 m).2 ω) ^ (1 / 2 : ℝ) := by
  have hc := SEforLnGen_contract1 hC n h1 ω (m := m) (k := m / 2) (by omega) (by omega) σ' a'
  obtain ⟨e1, e2⟩ := SEforLn2_n12 m hm
  rw [e1, e2] at hc
  exact hc

/-- The `𝓛 - 𝒦` sum of a loop of length `m ≥ 2` with the glued label last: contraction plus the Ward bound
`Kw` of the `𝒦`-loop. -/
private theorem SEforLnGen_sumLK {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {m : ℕ} (hm : 2 ≤ m) {Kw : ℝ}
    (hKw : ∀ (σ' : Fin m → Bool) (a' : Fin (m - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw) :
    SEforLnGen_SumOK Cm Hf n τ ω m
      ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (STn12 m).1 ω * STmaxLg Cm.toFlowFM n τ (STn12 m).2 ω) ^ (1 / 2 : ℝ) + Kw) := by
  intro σ' a'
  refine le_trans (Finset.sum_le_sum fun x _ => norm_sub_le (STLIg Cm Hf n τ ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩)
    (STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩)) ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add (SEforLnGen_sumContract hC n h0 h1 ω hm σ' a') (hKw σ' a')


private theorem SEforLnGen_long {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h1 : τ < 1) (ω : sz.SeqΩ) {k n' : ℕ}
    (hn' : n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1)) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((sz.W n : ℕ) : ℝ) ^ d * (STmaxLKg Cm.toFlowFM n τ (k + 2 - n') ω *
      ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (STn12 n').1 ω * STmaxLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
        δ * ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * (sz.Bctl n τ) ^ (n' - 2)))) ≤
      2 * δ * ((sz.Bctl n τ) ^ k / Cm.eta n τ *
        (STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
          (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ))) := by
  rw [Finset.mem_Icc] at hn'
  have hn3 : 3 ≤ n' := by omega
  have hB : 0 < sz.Bctl n τ := st_Bctl_pos sz h1
  have hη : 0 < Cm.eta n τ := SEforLnGen_eta_pos hC n h1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hX1 := SEforLnGen_one_le_XiL Cm.toFlowFM n τ ω (STn12 n').1 hB
  have hX2 := SEforLnGen_one_le_XiL Cm.toFlowFM n τ ω (STn12 n').2 hB
  have hY : 1 ≤ (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hX1 hX2) (by norm_num)
  have hRR := SEforLn2_R_le (k := n' - 1) hB (SEforLnGen_maxL_nonneg Cm.toFlowFM n τ _ ω)
    (SEforLnGen_maxL_nonneg Cm.toFlowFM n τ _ ω) (SEforLnGen_maxL_le Cm.toFlowFM n τ ω _ hB)
    (SEforLnGen_maxL_le Cm.toFlowFM n τ ω _ hB) (by linarith) (by linarith) (SEforLn2_n12_sum n' hn3)
  rw [show n' - 1 - 1 = n' - 2 by omega] at hRR
  exact SEforLn2_arith_long hWd hB hη hδ (SEforLnGen_maxLK_nonneg Cm.toFlowFM n τ _ ω)
    (SEforLnGen_maxLK_le Cm.toFlowFM n τ ω _ hB) (by linarith [SEforLnGen_one_le_XiLK Cm.toFlowFM n τ ω (k + 2 - n') hB]) hY
    (Real.rpow_nonneg (mul_nonneg (SEforLnGen_maxL_nonneg Cm.toFlowFM n τ _ ω)
      (SEforLnGen_maxL_nonneg Cm.toFlowFM n τ _ ω)) _) hRR (by omega)

/-- **The deterministic core of part (3)** (`3_5:1063-1086`): for every sample, a time `u = τ ∈ [0,1)`, the loop form,
if the 2-loop sum is bounded (`hS2`: `Σ_{a₂} |(𝓛-𝒦)^{(2)}| ≤ δ C_s B^{1/6} (W^d η)⁻¹`, `(eq:sumtwoloop)`) and the `𝒦`-loop
Ward bound holds with the loss `δ` (`hKw`), then `‖ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}‖ ≤ k² (C_s+2) δ B^k η⁻¹ (Σ_{n'} ... + B^{1/6} Ξ̂^{𝓛-𝒦}_k)`. -/
private theorem SEforLnGen_det3 {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (ω : sz.SeqΩ)
    {k : ℕ} (hk : 2 ≤ k) {δ Cs : ℝ} (hδ : 1 ≤ δ) (hCs : 0 ≤ Cs)
    (hS2 : SEforLnGen_SumOK Cm Hf n τ ω 2
      (δ * Cs * (sz.Bctl n τ) ^ (1 / 6 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d) * Cm.eta n τ)⁻¹))
    (hKw : ∀ l : ℕ, 3 ≤ l → l + 1 ≤ k → ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        δ * ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * (sz.Bctl n τ) ^ (l - 2)))
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖STelklkg Cm Hf n τ ω ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
      (k : ℝ) ^ 2 * ((Cs + 2) * δ) *
        ((sz.Bctl n τ) ^ k / Cm.eta n τ *
          (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
              STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
                (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
            (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n τ k ω)) := by
  have hτ : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨h0, h1⟩
  have hB : 0 < sz.Bctl n τ := st_Bctl_pos sz h1
  have hη : 0 < Cm.eta n τ := SEforLnGen_eta_pos hC n h1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hB6 : 0 ≤ (sz.Bctl n τ) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hB.le _
  have hXk := SEforLnGen_one_le_XiLK Cm.toFlowFM n τ ω k hB
  set T : ℝ := ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
    STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
      (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) with hT
  have hA0 : ∀ n' : ℕ, 0 ≤ STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
      (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) := fun n' =>
    mul_nonneg (zero_le_one.trans (SEforLnGen_one_le_XiLK Cm.toFlowFM n τ ω _ hB))
      (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n τ ω _ hB))
        (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n τ ω _ hB))) _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n' _ => hA0 n'
  set Zb : ℝ := (sz.Bctl n τ) ^ k / Cm.eta n τ * (T + (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n τ k ω) with hZ
  have hBkη : 0 ≤ (sz.Bctl n τ) ^ k / Cm.eta n τ := by positivity
  have hZ0 : 0 ≤ Zb := mul_nonneg hBkη (add_nonneg hT0 (mul_nonneg hB6 (by linarith)))
  have hCδ : 0 ≤ (Cs + 2) * δ := mul_nonneg (by linarith) (by linarith)
  set Q2 : ℝ := δ * Cs * (sz.Bctl n τ) ^ (1 / 6 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d) * Cm.eta n τ)⁻¹ with hQ2
  -- the pieces with a 2-loop summed
  have htwo : ∀ MK : ℝ, 0 ≤ MK → MK ≤ (sz.Bctl n τ) ^ k * STXiLKg Cm.toFlowFM n τ k ω →
      ((sz.W n : ℕ) : ℝ) ^ d * (MK * (δ * Cs * (sz.Bctl n τ) ^ (1 / 6 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d) * Cm.eta n τ)⁻¹)) ≤ (Cs + 2) * δ * Zb := by
    intro MK hMK0 hMK
    refine (SEforLn2_arith_two hWd hη (by linarith) hCs hB6 hMK hMK0).trans ?_
    have h1 : (sz.Bctl n τ) ^ k / Cm.eta n τ * ((sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n τ k ω) ≤ Zb := by
      rw [hZ]; exact mul_le_mul_of_nonneg_left (by linarith) hBkη
    have h2 : 0 ≤ (sz.Bctl n τ) ^ k / Cm.eta n τ * ((sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n τ k ω) :=
      mul_nonneg hBkη (mul_nonneg hB6 (by linarith))
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ) h2]
  -- the sum bound of a longer piece
  set Qm : ℕ → ℝ := fun m => (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
      (STmaxLg Cm.toFlowFM n τ (STn12 m).1 ω * STmaxLg Cm.toFlowFM n τ (STn12 m).2 ω) ^ (1 / 2 : ℝ) +
      δ * ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * (sz.Bctl n τ) ^ (m - 2)) with hQm
  have hQmOK : ∀ m : ℕ, 3 ≤ m → m + 1 ≤ k → SEforLnGen_SumOK Cm Hf n τ ω m (Qm m) := fun m hm3 hmk =>
    SEforLnGen_sumLK hC n h0 h1 ω (by omega) (Kw := δ * ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
      (sz.Bctl n τ) ^ (m - 2))) (hKw m hm3 hmk)
  have hlong : ∀ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      ((sz.W n : ℕ) : ℝ) ^ d * (STmaxLKg Cm.toFlowFM n τ (k + 2 - n') ω * Qm n') ≤ (Cs + 2) * δ * Zb := by
    intro n' hn'
    refine (SEforLnGen_long hC n h1 ω hn' hδ).trans ?_
    have hsingle : STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
        (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) ≤ T :=
      Finset.single_le_sum (f := fun n' => STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
        (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ))
        (fun i _ => hA0 i) hn'
    have h1' : (sz.Bctl n τ) ^ k / Cm.eta n τ * (STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
        (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ)) ≤ Zb := by
      rw [hZ]
      refine mul_le_mul_of_nonneg_left ?_ hBkη
      have : 0 ≤ (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n τ k ω := mul_nonneg hB6 (by linarith)
      linarith
    have h2 : 0 ≤ (sz.Bctl n τ) ^ k / Cm.eta n τ * (STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
        (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ)) :=
      mul_nonneg hBkη (hA0 n')
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ) h2]
  have hdiv : ∀ x X : ℝ, ((sz.W n : ℕ) : ℝ) ^ d * x ≤ X → x ≤ X * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    intro x X h
    rw [← div_eq_mul_inv, le_div_iff₀ hWd]
    linarith [mul_comm x (((sz.W n : ℕ) : ℝ) ^ d)]
  have hσl : (List.ofFn σ).length = k := by simp
  have hal : (List.ofFn a).length = k := by simp
  -- the bound of one pair of cut edges
  have hpair : ∀ j ∈ Finset.Icc 1 k, ∀ l' ∈ Finset.Ioc j k,
      ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ‖STLKIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ *
          ‖Cm.S n x y‖ *
          ‖STLKIg Cm Hf n τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤
        (Cs + 2) * δ * Zb * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    intro j hj l' hl'
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ioc] at hl'
    by_cases hr2 : l' - j + 1 = 2
    · -- the `cutGlueR` piece is a 2-loop, the other has length `k`
      have hQ' : SEforLnGen_SumOK Cm Hf n τ ω (l' - j + 1) Q2 := by rw [hr2]; exact hS2
      have hQR := SEforLnGen_sumR n hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
      refine (SEforLnGen_pair_left hC n τ ω σ a hj.1 hl'.1 hl'.2 hQR).trans ?_
      rw [show j + k - l' + 1 = k by omega]
      exact hdiv _ _ (htwo _ (SEforLnGen_maxLK_nonneg Cm.toFlowFM n τ k ω) (SEforLnGen_maxLK_le Cm.toFlowFM n τ ω k hB))
    · by_cases hl2 : j + k - l' + 1 = 2
      · -- the `cutGlueL` piece is a 2-loop, the other has length `k`
        have hQ' : SEforLnGen_SumOK Cm Hf n τ ω (j + k - l' + 1) Q2 := by rw [hl2]; exact hS2
        have hQL := SEforLnGen_sumL hC n hτ hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
        refine (SEforLnGen_pair_right hC n τ ω σ a hj.1 hl'.1 hl'.2 hQL).trans ?_
        rw [show l' - j + 1 = k by omega]
        exact hdiv _ _ (htwo _ (SEforLnGen_maxLK_nonneg Cm.toFlowFM n τ k ω) (SEforLnGen_maxLK_le Cm.toFlowFM n τ ω k hB))
      · by_cases hlr : l' - j + 1 ≤ j + k - l' + 1
        · -- the longer piece is `cutGlueL`, of length `n' = j + k - l' + 1`
          have hn' : j + k - l' + 1 ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1) := by
            rw [Finset.mem_Icc]; omega
          have hQ' := hQmOK (j + k - l' + 1) (by omega) (by omega)
          have hQL := SEforLnGen_sumL hC n hτ hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
          refine (SEforLnGen_pair_right hC n τ ω σ a hj.1 hl'.1 hl'.2 hQL).trans ?_
          rw [show l' - j + 1 = k + 2 - (j + k - l' + 1) by omega]
          exact hdiv _ _ (hlong _ hn')
        · -- the longer piece is `cutGlueR`, of length `n' = l' - j + 1`
          have hn' : l' - j + 1 ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1) := by
            rw [Finset.mem_Icc]; omega
          have hQ' := hQmOK (l' - j + 1) (by omega) (by omega)
          have hQR := SEforLnGen_sumR n hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
          refine (SEforLnGen_pair_left hC n τ ω σ a hj.1 hl'.1 hl'.2 hQR).trans ?_
          rw [show j + k - l' + 1 = k + 2 - (l' - j + 1) by omega]
          exact hdiv _ _ (hlong _ hn')
  -- the sum over the cut edges
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hlen : I.length = k := by simp [hI, LoopIdx.length]
  unfold STelklkg STelklkMg
  rw [norm_mul, hlen, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  have hsum : ‖∑ j ∈ Finset.Icc 1 k, ∑ l' ∈ Finset.Ioc j k, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      STLKIg Cm Hf n τ ω (I.cutGlueL j l' x) * Cm.S n x y *
        STLKIg Cm Hf n τ ω (I.cutGlueR j l' y)‖ ≤
      (k : ℝ) ^ 2 * ((Cs + 2) * δ * Zb * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _) ?_
    refine SEforLn2_sum_pairs k (fun j l' => ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      STLKIg Cm Hf n τ ω (I.cutGlueL j l' x) * Cm.S n x y *
        STLKIg Cm Hf n τ ω (I.cutGlueR j l' y)‖)
      (mul_nonneg (mul_nonneg hCδ hZ0) (inv_nonneg.2 hWd.le)) fun j hj l' hl' => ?_
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => le_of_eq ?_)) (hpair j hj l' hl'))
    rw [norm_mul, norm_mul]
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ j ∈ Finset.Icc 1 k, ∑ l' ∈ Finset.Ioc j k, ∑ x : Zd d (sz.L n),
        ∑ y : Zd d (sz.L n), STLKIg Cm Hf n τ ω (I.cutGlueL j l' x) * Cm.S n x y *
          STLKIg Cm Hf n τ ω (I.cutGlueR j l' y)‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) ^ 2 * ((Cs + 2) * δ * Zb * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum hWd.le
    _ = (k : ℝ) ^ 2 * ((Cs + 2) * δ) * Zb := by field_simp

private theorem SEforLnGen_Z_nonneg {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h1 : τ < 1) (ω : sz.SeqΩ) (k : ℕ) :
    0 ≤ (sz.Bctl n τ) ^ k / Cm.eta n τ *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLKg Cm.toFlowFM n τ (k + 2 - n') ω *
              (STXiLg Cm.toFlowFM n τ (STn12 n').1 ω * STXiLg Cm.toFlowFM n τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n τ k ω) := by
  have hB : 0 < sz.Bctl n τ := st_Bctl_pos sz h1
  have hη : 0 < Cm.eta n τ := SEforLnGen_eta_pos hC n h1
  refine mul_nonneg (div_nonneg (pow_nonneg hB.le _) hη.le) (add_nonneg (Finset.sum_nonneg fun n' _ => ?_)
    (mul_nonneg (Real.rpow_nonneg hB.le _) (zero_le_one.trans (SEforLnGen_one_le_XiLK Cm.toFlowFM n τ ω _ hB))))
  exact mul_nonneg (zero_le_one.trans (SEforLnGen_one_le_XiLK Cm.toFlowFM n τ ω _ hB))
    (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n τ ω _ hB))
      (zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n τ ω _ hB))) _)

/-- The core of part (3), for an abstract energy sequence `E` with `|E n| < 2` and times `0 ≤ s ≤ t < 1`, from
the uniform 2-`G`-loop estimate `STGdecayW` (the only `ω`-dependent input), the uniform `𝒦`-loop Ward bound
`(wardineq_K)` (a `Prec` of a deterministic family), `(con_st_ind)` with `𝔠_d C_d ≤ 1/30`, and `W ≥ N^𝔠`. -/
private theorem SEforLnGen_part3_core {E s t : ℕ → ℝ} {Cd 𝔠d 𝔠 : ℝ} (hC : SEforLnGen_Hyp Cm Hf E)
    (him : ∀ n, (Cm.m n).im ≤ 1) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (hd : 2 ≤ d) (hN : sz.SizeTendsto)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) (hCd : 0 ≤ Cd)
    (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30) (hcon : sz.STConStInd 𝔠d s t) (hG : STGdecayWgL Cm.toFlowFM μ s t Cd)
    (hKw : ∀ l : ℕ, 2 ≤ l →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖STKIg Cm n (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (p.1 : ℝ))⁻¹ *
          (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)))
    (k : ℕ) (hk : 2 ≤ k) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklkg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k + 2 - n') ω *
              (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').1 ω *
                STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n (p.1 : ℝ) k ω)) := by
  have hsize := Sizes.tendsto_size sz hN
  have hG' := hG (2 / 𝔠) (by positivity)
  unfold PrecL at hG' ⊢
  refine SEforLn1_of_subset hG' (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  have hKwdet : ∀ᶠ n in atTop, ∀ l ∈ Finset.Icc 2 k, ∀ (u : TimeIcc s t n) (σ' : Fin l → Bool)
      (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n (u : ℝ) ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (u : ℝ))⁻¹ * (sz.Bctl n (u : ℝ)) ^ (l - 2)) := by
    rw [Filter.eventually_all_finset]
    intro l hl
    have := SEforLnGen_det_of_prec μ hN
      (fun n (p : TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n))) =>
        ∑ x : Zd d (sz.L n), ‖STKIg Cm n (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
      (fun n p => (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2))
      (hKw l (Finset.mem_Icc.1 hl).1) (half_pos hτ)
    filter_upwards [this] with n hn u σ' a' using hn (u, σ', a')
  filter_upwards [hsize.eventually (eventually_le_rpow ((k : ℝ) ^ 2 * (KDecay_tailC d + 1 + 2))
    (half_pos hτ)), hcon, hlam, hband, hKwdet] with n hCN hcon_n hlam_n hband_n hKw_n
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < Cm.eta n (p.1 : ℝ) := SEforLnGen_eta_pos hC n hu1
  obtain ⟨hs', hB1, hBc⟩ := SEforLn2_conU sz n h𝔠d hcon_n p.1.2.2 (ht1 n)
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) (half_pos hτ).le
  have hWD := (SEforLn2_WD sz n h𝔠 hband_n).trans (SEforLn2_Bctl_ge_inv sz n hu0 hu1)
  have hS2 := SEforLnGen_sum2 hC him hd n h𝔠d hCd hcc hs' hu0 hu1 hBc hB1 hlam_n (by linarith) hWD ω
    (fun σ' a2 => hno (p.1, σ', a2))
  have hKw3 : ∀ l : ℕ, 3 ≤ l → l + 1 ≤ k → ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKIg Cm n (p.1 : ℝ) ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)) :=
    fun l hl3 hlk σ' a' => hKw_n l (Finset.mem_Icc.2 ⟨by omega, by omega⟩) p.1 σ' a'
  have hdet := SEforLnGen_det3 hC n hu0 hu1 ω hk hN1
    (Cs := KDecay_tailC d + 1) (by linarith [KDecay_one_le_tailC (d := d) (by omega)]) hS2 hKw3 p.2.1 p.2.2
  have hZ0 := SEforLnGen_Z_nonneg hC n hu1 ω k
  have hδ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
  have hfin : ‖STelklkg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k + 2 - n') ω *
              (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').1 ω *
                STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n (p.1 : ℝ) k ω)) := by
    refine SEforLn2_final hdet ?_ hZ0 (UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ)
    nlinarith [hCN, hδ0]
  exact absurd hp (not_lt.2 hfin)


/-! ## 6. Part (4): `(eq:MG_nloop)` -/

/-- `𝒜(x) = {y : |x - y|_∞ ≤ 1}`, the support of the row `S_{x ·}` (target 3, support field). -/
private def SEforLnGen_nbhd {L : ℕ} [NeZero L] (x : Zd d L) : Finset (Zd d L) :=
  Finset.univ.filter fun y => zdistInf d L (x - y) ≤ 1

private theorem SEforLnGen_nbhd_card {L : ℕ} [NeZero L] (x : Zd d L) :
    ((SEforLnGen_nbhd x).card : ℝ) ≤ (3 : ℝ) ^ d := by
  have h := RBM.Ind.DecayLoopB_card_ball x (R := 1) zero_le_one
  have hfl : (Finset.univ.filter fun u : Zd d L => (zdistInf d L (x - u) : ℝ) ≤ 1) = SEforLnGen_nbhd x := by
    ext u
    simp [SEforLnGen_nbhd]
  rw [hfl] at h
  norm_num at h
  exact h

/-- `|S_{xy}| ≤ 1` (a single term of the row sum). -/
private theorem SEforLnGen_S_le_one {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) (x y : Zd d (sz.L n)) :
    ‖Cm.S n x y‖ ≤ 1 :=
  (Finset.single_le_sum (f := fun y => ‖Cm.S n x y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)).trans (hC.row n x)

/-- `Σ_y |S_{xy} f(y)| ≤ Σ_{y ∈ 𝒜(x)} |f(y)|` (support and `|S| ≤ 1`; `SEforLn2_SB_sum`). -/
private theorem SEforLnGen_SB_sum {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E)
    (hsupp : ∀ (n : ℕ) (x y : Zd d (sz.L n)), Cm.S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) (n : ℕ)
    (x : Zd d (sz.L n)) (f : Zd d (sz.L n) → ℂ) :
    ∑ y : Zd d (sz.L n), ‖Cm.S n x y * f y‖ ≤ ∑ y ∈ SEforLnGen_nbhd x, ‖f y‖ := by
  calc ∑ y : Zd d (sz.L n), ‖Cm.S n x y * f y‖
      = ∑ y ∈ SEforLnGen_nbhd x, ‖Cm.S n x y * f y‖ :=
        (Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => by
          have : Cm.S n x y = 0 := by
            by_contra h0
            exact hy (by simpa [SEforLnGen_nbhd] using hsupp n x y h0)
          rw [this]; simp)).symm
    _ ≤ ∑ y ∈ SEforLnGen_nbhd x, ‖f y‖ :=
        Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (SEforLnGen_S_le_one hC n x y)

/-- **The contraction of the `(2k+2)`-loop** (`(u2jzooi-2)` with `k`, `j = k + 1`, `l = k + 2`, `p = q`,
`𝒜 b = {b' : |b - b'|_∞ ≤ 1}`, `3_5:1088-1093`): for the cut edge `j`,
`Σ_b Σ_{b' ∈ 𝒜 b} |𝓛(STeeLoop j b b')| ≤ 3^d (W^d η)⁻¹ (max|𝓛^{(2k-1)}| max|𝓛^{(2k-1)}|)^{1/2}
(max|𝓛^{(4q)}|)^{1/(2q)}`. -/
private theorem SEforLnGen_eeSum {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E) (n : ℕ) {τ : ℝ} (h1 : τ < 1) (ω : sz.SeqΩ)
    {k : ℕ} (hk : 1 ≤ k) {q : ℕ} (hq : 1 ≤ q) (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x : Zd d (sz.L n), ∑ y ∈ SEforLnGen_nbhd x,
        ‖STLIg Cm Hf n τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y)‖ ≤
      (3 : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ *
        (STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω * STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω) ^ (1 / 2 : ℝ) *
        STmaxLg Cm.toFlowFM n τ (4 * q) ω ^ (1 / (2 * (q : ℝ))) := by
  obtain ⟨σ'', a₀, hloop⟩ := SEforLn2_eeLoop σ a a' hj1 hjk (0 : Zd d (sz.L n))
  have hc := SEforLnGen_contract2 hC n h1 ω (m := 2 * k + 2) (k := k) (l := k + 2) (p := q) ⟨k, by omega⟩
    ((3 : ℝ) ^ d) (by omega) hq hk (by simp) (by simp) (by omega) (by positivity)
    (SEforLnGen_nbhd (L := sz.L n)) (fun x => SEforLnGen_nbhd_card x) σ'' a₀
  rw [show 2 * (2 * k + 2) - 2 * (k + 2) - 1 = 2 * k - 1 by omega, show k + 2 - k = 2 by omega,
    show 2 * 2 * q = 4 * q by omega] at hc
  refine le_trans (le_of_eq ?_) hc
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hloop x y]

/-- **The deterministic core of part (4)**: `‖(ℰ⊗ℰ)^{M,(k)}‖ ≤ k 3^d η⁻¹ (max|𝓛^{(2k-1)}|²)^{1/2}
(max|𝓛^{(4q)}|)^{1/(2q)}` for every sample, `u ∈ [0,1)`, the loop form: the sum over the `k` cut edges of
`(defEOTE)`, `|S^{(B)}| ≤ 1` supported on `𝒜`. -/
private theorem SEforLnGen_det4 {E : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E)
    (hsupp : ∀ (n : ℕ) (x y : Zd d (sz.L n)), Cm.S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1) (n : ℕ) {τ : ℝ} (h1 : τ < 1) (ω : sz.SeqΩ)
    {k : ℕ} (hk : 1 ≤ k) {q : ℕ} (hq : 1 ≤ q) (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) :
    ‖STeeg Cm Hf n τ ω σ a a'‖ ≤
      (k : ℝ) * ((3 : ℝ) ^ d * ((Cm.eta n τ)⁻¹ *
        ((STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω * STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω) ^ (1 / 2 : ℝ) *
          STmaxLg Cm.toFlowFM n τ (4 * q) ω ^ (1 / (2 * (q : ℝ)))))) := by
  have hη : 0 < Cm.eta n τ := SEforLnGen_eta_pos hC n h1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  unfold STeeg STeeMg
  rw [norm_mul, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  set Rr : ℝ := (STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω * STmaxLg Cm.toFlowFM n τ (2 * k - 1) ω) ^ (1 / 2 : ℝ) *
    STmaxLg Cm.toFlowFM n τ (4 * q) ω ^ (1 / (2 * (q : ℝ))) with hRr
  have hone : ∀ j ∈ Finset.Icc 1 k,
      ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), Cm.S n x y *
          STLIg Cm Hf n τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y)‖ ≤
        (3 : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * Rr := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _)) ?_
    refine le_trans (Finset.sum_le_sum fun x _ => SEforLnGen_SB_sum hC hsupp n x
      (fun y => STLIg Cm Hf n τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y))) ?_
    have := SEforLnGen_eeSum hC n h1 ω hk hq σ a a' hj.1 hj.2
    rw [hRr, ← mul_assoc]
    exact this
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ j ∈ Finset.Icc 1 k, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        Cm.S n x y *
          STLIg Cm Hf n τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y)‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ j ∈ Finset.Icc 1 k,
          ((3 : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n τ)⁻¹ * Rr) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)) hWd.le
        exact hone j hj
    _ = (k : ℝ) * ((3 : ℝ) ^ d * ((Cm.eta n τ)⁻¹ * Rr)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp

private theorem SEforLnGen_part4_core {E s t : ℕ → ℝ} (hC : SEforLnGen_Hyp Cm Hf E)
    (hsupp : ∀ (n : ℕ) (x y : Zd d (sz.L n)), Cm.S n x y ≠ 0 → zdistInf d (sz.L n) (x - y) ≤ 1)
    (μ : Measure sz.SeqΩ) (hN : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (k : ℕ) (hk : 2 ≤ k) (q : ℕ) (hq : 1 ≤ q) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STeeg Cm Hf n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / Cm.eta n (p.1 : ℝ) *
        (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^
          (1 / (2 * (q : ℝ))))) := by
  have hsize := Sizes.tendsto_size sz hN
  unfold PrecL
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  filter_upwards [hsize.eventually (eventually_le_rpow ((k : ℝ) * (3 : ℝ) ^ d) hτ)] with n hn
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro p
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < Cm.eta n (p.1 : ℝ) := SEforLnGen_eta_pos hC n hu1
  have hdet := SEforLnGen_det4 hC hsupp n hu1 ω (by omega) hq p.2.1 p.2.2.1 p.2.2.2
  have hX1 := zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n (p.1 : ℝ) ω (2 * k - 1) hB)
  have hX2 := zero_le_one.trans (SEforLnGen_one_le_XiL Cm.toFlowFM n (p.1 : ℝ) ω (4 * q) hB)
  have hR := SEforLn2_arith4 (k := k) (q := q) (by omega) hq hB
    (SEforLnGen_maxL_nonneg Cm.toFlowFM n _ _ ω) (SEforLnGen_maxL_nonneg Cm.toFlowFM n _ _ ω) hX1 hX2
    (SEforLnGen_maxL_le Cm.toFlowFM n (p.1 : ℝ) ω _ hB) (SEforLnGen_maxL_le Cm.toFlowFM n (p.1 : ℝ) ω _ hB)
  have hZ0 : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / Cm.eta n (p.1 : ℝ) *
      (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^
        (1 / (2 * (q : ℝ)))) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hB.le _) hη.le)
      (mul_nonneg hX1 (Real.rpow_nonneg hX2 _))
  have hη' : 0 ≤ (Cm.eta n (p.1 : ℝ))⁻¹ := inv_nonneg.2 hη.le
  calc ‖STeeg Cm Hf n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖
      ≤ (k : ℝ) * ((3 : ℝ) ^ d * ((Cm.eta n (p.1 : ℝ))⁻¹ *
        ((STmaxLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STmaxLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω) ^
            (1 / 2 : ℝ) * STmaxLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ)))))) := hdet
    _ ≤ (k : ℝ) * ((3 : ℝ) ^ d * ((Cm.eta n (p.1 : ℝ))⁻¹ *
        ((sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) *
          (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR hη')
          (by positivity)) (by positivity)
    _ = (k : ℝ) * (3 : ℝ) ^ d *
        ((sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / Cm.eta n (p.1 : ℝ) *
          (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))) := by
        field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / Cm.eta n (p.1 : ℝ) *
          (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))) := mul_le_mul_of_nonneg_right hn hZ0


/-! ## 7. The uniform `𝒦`-loop Ward bound in the list-indexed form -/

/-- `STKIg` at the label vector of `STKwardgL` (`Carrier_ofFn_ext`). -/
private theorem SEforLnGen_KI_snoc (hK : Step34Gen_KCompat Cm) {l : ℕ} (hl : 1 ≤ l) (n : ℕ) (τ : ℝ)
    (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)) (x : Zd d (sz.L n)) :
    STKIg Cm n τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩ =
      Cm.K n τ σ' (fun i : Fin l => if h : (i : ℕ) < l - 1 then a' ⟨i, h⟩ else x) := by
  rw [hK n τ σ' _]
  unfold STKIg KLloopOf
  rw [Carrier_ofFn_ext hl a' x]

/-- Target 1 (`stKward_timeIccgL`) read on the list-indexed `𝒦`. -/
private theorem SEforLnGen_kward_timeIcc (hK : Step34Gen_KCompat Cm) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hN : sz.SizeTendsto) (hKw : STKwardgL Cm.toFlowFM μ) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (l : ℕ) (hl : 2 ≤ l) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n)))
      (fun n p _ => ∑ x : Zd d (sz.L n),
        ‖STKIg Cm n (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
      (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * Cm.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)) := by
  have h := stKward_timeIccgL sz Cm.toFlowFM μ hN hKw s t hs0 hst ht1 l hl
  simp only [SEforLnGen_KI_snoc hK (show 1 ≤ l by omega)]
  exact h

end Core



/-! ## 8. Parts (1)-(4), the conclusion `STSEforLnConclgL` and the pin -/

section Parts

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
  (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
  (μ : Measure sz.SeqΩ)

/-- **Part (1) of `lem:SEforLn`, `(bEwGn)`** (`3_5:1017-1027`, proof `3_5:1047-1053`; band `stSEforLn_part1`, `SEforLn1:466`) over a
carrier: from the uniform averaged local law `STAvgUgL` (`(Gt_avgbound_flow)`, an output of Step 2) and the contraction inequality,
for every `k ≥ 2`, `max_{σ,a} |ℰ^{G̃,(k)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^k η_u⁻¹ (Ξ̂^{𝓛}_{u,n₁} Ξ̂^{𝓛}_{u,n₂})^{1/2}`, `(n₁, n₂) = STn12E k`,
uniformly in `u ∈ [s_n, t_n]`.  The conclusion is the first conjunct of `STSEforLnConclgL Cm Hf μ s t` at `k`. -/
theorem stSEforLn_part1g (E s t : ℕ → ℝ) (hN : sz.SizeTendsto) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcol : ∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hAvg : STAvgUgL Cm.toFlowFM μ s t) (k : ℕ) (hk : 2 ≤ k) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegtg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).1 ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).2 ω) ^
          (1 / 2 : ℝ)) :=
  SEforLnGen_part1_core ⟨hloop, hherm, hL, hK, hward, hrow, hcol⟩ μ hN hs0 ht1 hone hAvg k hk

/-- **Part (2) of `lem:SEforLn`, `(eq:KsimL-K)`** (`3_5:1028-1034`, proof `3_5:1054-1061`; band `stSEforLn_part2`, `SEforLn1:702`) over a
carrier: for every `k ≥ 2` and `3 ≤ l ≤ k`, `max_{σ,a} |[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^k η_u⁻¹ Ξ̂^{𝓛-𝒦}_{u,k-l+2}`,
uniformly in `u ∈ [s_n, t_n]`.  The input is `lem_wardineq_K` (`STKwardgL`, per time sequence; target 1 makes it uniform in time).
The conclusion is the second conjunct of `STSEforLnConclgL Cm Hf μ s t` at `k`. -/
theorem stSEforLn_part2g [IsProbabilityMeasure μ] (E s t : ℕ → ℝ) (hN : sz.SizeTendsto)
    (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcol : ∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hKw : STKwardgL Cm.toFlowFM μ) (k : ℕ) :
    ∀ l : ℕ, 3 ≤ l → l ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STksimLKg Cm Hf n (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) * STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k - l + 2) ω) :=
  fun l hl3 hlk => SEforLnGen_part2_core ⟨hloop, hherm, hL, hK, hward, hrow, hcol⟩ μ hN hs0 ht1
    (fun l' hl' => SEforLnGen_kward_timeIcc hK μ hN hKw s t hs0 hst ht1 l' hl') k l hl3 hlk

/-- **Part (3) of `lem:SEforLn`, `(eq:L-KsimL-K)`** (`3_5:1035-1041`, proof `3_5:1063-1086`; band `stSEforLn_part3`, `SEforLn2:1007`) over a
carrier: from the uniform 2-`G`-loop estimate `STGdecayWgL` (`(Eq:Gdecay_w)`, an output of Step 2), `(con_st_ind)` with `𝔠_d C_d ≤ 1/30`
(`(eq:sumtwoloop)`), the uniform `𝒦`-loop Ward bound (target 1) and the contraction inequality, for every `k ≥ 2`,
`max_{σ,a} |ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^k η_u⁻¹ (Σ_{n'=⌈k/2⌉+1}^{k-1} Ξ̂^{𝓛-𝒦}_{u,k+2-n'} (Ξ̂^{𝓛}_{u,n'₁} Ξ̂^{𝓛}_{u,n'₂})^{1/2}
+ (W^{-d}B_{u,0})^{1/6} Ξ̂^{𝓛-𝒦}_{u,k})`, uniformly in `u ∈ [s_n, t_n]`.  The conclusion is the third conjunct of `STSEforLnConclgL` at `k`. -/
theorem stSEforLn_part3g [IsProbabilityMeasure μ] (hd : 3 ≤ d) (𝔠 𝔡 Cd 𝔠d : ℝ) (E s t : ℕ → ℝ) (hA : sz.Admissible 𝔠 𝔡)
    (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcol : ∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (him : ∀ n : ℕ, (Cm.m n).im ≤ 1) (hCd : 0 < Cd) (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcon : sz.STConStInd 𝔠d s t)
    (hKw : STKwardgL Cm.toFlowFM μ) (hG : STGdecayWgL Cm.toFlowFM μ s t Cd) (k : ℕ) (hk : 2 ≤ k) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklkg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k + 2 - n') ω *
              (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').1 ω *
                STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n (p.1 : ℝ) k ω)) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n := by
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact (Real.rpow_pos_of_pos hW _).le.trans hn.1
  exact SEforLnGen_part3_core ⟨hloop, hherm, hL, hK, hward, hrow, hcol⟩ him μ (by omega) hN hs0 ht1 hlam h𝔠 hB hCd.le
    h𝔠d hcc hcon hG (fun l' hl' => SEforLnGen_kward_timeIcc hK μ hN hKw s t hs0 (fun n => (hst n).le) ht1 l' hl') k hk

/-- **Part (4) of `lem:SEforLn`, `(eq:MG_nloop)`** (`3_5:1042-1046`, proof `3_5:1088-1093`; band `stSEforLn_part4`, `SEforLn2:1264`) over a
carrier: for every `k ≥ 2` and `q ≥ 1`, `max_{σ,a,a'} |(ℰ⊗ℰ)^{M,(k)}_{u,σ,a,a'}| ≺ (W^{-d}B_{u,0})^{2k-1/(2q)} η_u⁻¹ Ξ̂^{𝓛}_{u,2k-1}
(Ξ̂^{𝓛}_{u,4q})^{1/(2q)}`, uniformly in `u ∈ [s_n, t_n]`.  The input is the second inequality of the contraction (`(u2jzooi-2)`) and the
finite range of `S` (`zdistInf (a - b) ≤ 1`, at most `3^d` neighbours); no stochastic hypothesis.  The conclusion is the fourth conjunct
of `STSEforLnConclgL` at `k`. -/
theorem stSEforLn_part4g (E s t : ℕ → ℝ) (hN : sz.SizeTendsto) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcol : ∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (k : ℕ) (hk : 2 ≤ k) :
    ∀ q : ℕ, 1 ≤ q →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STeeg Cm Hf n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / Cm.eta n (p.1 : ℝ) *
          (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))) :=
  fun q hq => SEforLnGen_part4_core ⟨hloop, hherm, hL, hK, hward, hrow, hcol⟩ hsupp μ hN hs0 ht1 k hk q hq

end Parts

/-- **Target 4, `stSEforLnConclgL_of`** (conclusion binding `T2480_SEforLnConclOf`; band `stSEforLn_holds`, `SEforLn2:1287`, parts
(1)-(4) assembled): the four estimates of `lem:SEforLn` over one carrier `(Cm, Hf, μ)`, from the carrier facts of target 3 (here as
separate hypotheses), `(con_st_ind)` with `𝔠_d C_d ≤ 1/30`, `lem_wardineq_K` (`STKwardgL`) and the Step 2 outputs `STStep2ConclgL`
(`STAvgUgL`, `STGdecayWgL`).  The hypothesis list is the shape of the check file's `T2480_SEforLnConclOf` plus the support field of
`SEforLnGen_Facts` (`hsupp`, needed by part (4): the second contraction inequality sums over a bounded neighbourhood). -/
theorem stSEforLnConclgL_of {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 Cd 𝔠d : ℝ) (E s t : ℕ → ℝ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hcol : ∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (him : ∀ n : ℕ, (Cm.m n).im ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hCd : 0 < Cd) (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcon : sz.STConStInd 𝔠d s t)
    (hKw : STKwardgL Cm.toFlowFM μ) (hStep2 : STStep2ConclgL Cm.toFlowFM μ s t Cd) :
    STSEforLnConclgL Cm Hf μ s t := by
  intro k hk
  exact ⟨stSEforLn_part1g Cm Hf μ E s t hA.2.2.1 hloop hherm hL hK hward hrow hcol hone hs0 ht1 hStep2.2.1 k hk,
    stSEforLn_part2g Cm Hf μ E s t hA.2.2.1 hloop hherm hL hK hward hrow hcol hs0 (fun n => (hst n).le) ht1 hKw k,
    stSEforLn_part3g Cm Hf μ hd 𝔠 𝔡 Cd 𝔠d E s t hA hloop hherm hL hK hward hrow hcol him hCd h𝔠d hcc hs0 hst ht1 hcon hKw
      hStep2.2.2 k hk,
    stSEforLn_part4g Cm Hf μ E s t hA.2.2.1 hloop hherm hL hK hward hrow hcol hsupp hs0 ht1 k hk⟩

/-- **Target 5, the pin `stSEforLngL_of`** (conclusion binding `T2480_SEforLngLOf`; band `stSEforLn_holds` through `bandFM_STSEforLn`,
`Chain/Step34Gen.lean:460`): `lem:SEforLn` as an ingredient pin over a carrier family `(law, Flow, mkM, Hf, T0)`, for every regime `R`
(the proof reads none: `STIngRgL` takes `R sz s t` only as a hypothesis).  Inputs: probability laws, the flow facts of U4s1
(`Step5CasesGen_FlowFacts`: admissible sizes, `T0 < 1`, `κm ≤ Im m`, `η = (1 - t) Im m`) and the carrier facts `SEforLnGen_Facts`;
`𝔠_d = min (1/100) (1/(30 C_d))` as in `stSEforLn_holds`. -/
theorem stSEforLngL_of (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hlaw : ∀ sz : Sizes d, IsProbabilityMeasure (law sz))
    (hflow : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0)
    (hfacts : SEforLnGen_Facts d Flow mkM Hf) : STSEforLngL d R law Flow mkM Hf T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have h𝔠d : 0 < min (1 / 100 : ℝ) (1 / (30 * Cd)) := lt_min (by norm_num) (by positivity)
  refine ⟨min (1 / 100) (1 / (30 * Cd)), h𝔠d, min_le_left _ _, ?_⟩
  intro 𝔠 sz z hFlow s t hs hst ht _ _ hKw _ hcon hStep2
  have := hlaw sz
  obtain ⟨κm, hκm, hF⟩ := hflow κ hκ
  obtain ⟨hA, hT, hmκ, hη⟩ := hF sz ε 𝔠 𝔡 z hFlow
  obtain ⟨⟨E, hloop⟩, hherm, hL, hK, hward, hrow, hcol, hsupp, him, hone⟩ := hfacts sz κ ε 𝔠 𝔡 z hκ hFlow
  have hcc : min (1 / 100 : ℝ) (1 / (30 * Cd)) * Cd ≤ 1 / 30 :=
    calc min (1 / 100 : ℝ) (1 / (30 * Cd)) * Cd ≤ 1 / (30 * Cd) * Cd :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hCd.le
      _ = 1 / 30 := by field_simp
  exact stSEforLnConclgL_of hd sz (mkM sz z) (Hf sz z) (law sz) κm 𝔠 𝔡 Cd _ E s t ⟨hκm, hmκ, hη⟩ hA hloop hherm hL hK
    hward hrow hcol hsupp him hone hCd h𝔠d hcc hs hst (fun n => (ht n).trans_lt (hT n)) hcon hKw hStep2



/-! ## 9. Band re-derivations of parts (1)-(4) and of the pin -/

end RBM.BA

/-! ## 10. Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the flow
`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, the window `s ≡ 0`, `t ≡ 1/16` (`1/16 ≤ lemT z0`), `C_d = 4`, `𝔠_d = 1/120`
(`𝔠_d C_d = 1/30`), the carrier `bandStep2Mat sz0 (STflowE z0)`, the flow matrix `seqHflow sz0` and the law `seqP sz0`.  The class
`SEforLnGen_Facts` and the pin `stSEforLngL_of` are applied with no stochastic hypothesis; `stSEforLnConclgL_of` keeps the Step 2 output
`STStep2ConclgL` (`STAvgUgL`, `STGdecayWgL`: another gate's pin) as a hypothesis, every deterministic premise (`3 ≤ d`, admissibility,
the ten carrier facts, `κm`, `0 < C_d`, `0 < 𝔠_d`, `𝔠_d C_d ≤ 1/30`, the window, `(con_st_ind)`, `lem_wardineq_K`) is discharged. -/
