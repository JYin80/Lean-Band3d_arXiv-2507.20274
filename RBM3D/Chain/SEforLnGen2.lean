/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.SEforLnGen

/-!
# The label decay of the four `ℰ`-terms over the flow carrier

Generic form of `Induction/DecayLoopB` (`stEtermDecay`): for a flow matrix `Cm : Step2Mat sz`, a flow
matrix family `Hf` and a probability law `μ`, the four `ℰ`-terms of `lem:SEforLn` (`STegtg`,
`STksimLKg`, `STelklkg`, `STeeg`) have the label decay `STEKDecaygL` ((4.52) `deccA0` w.h.p., at
`sz.lam`): `stEtermDecaygL_egt`, `stEtermDecaygL_ksim`, `stEtermDecaygL_elklk`,
`stEtermDecaygL_ee` and the bundle `stEtermDecaygL`.

* **Inputs.** `STDecayLoopUgL` (`lem_decayLoop`), `STKcalDecaygL` (the far decay of `𝒦`; band `STKcalDecay`), `STKboundgL` (through `stKbound_timeIccgL`), `DecayGen_Spec`, `Admissible`,
  the loop form, `Step34Gen_LCompat`, `Step34Gen_KCompat`, the row sums and the support of `S` (the
  class `SEforLnGen_Facts`).
* **Band objects replaced.** `SB` by the carrier kernel `Cm.S` (row sums `≤ 1` and support
  `|a - b|_∞ ≤ 1` instead of `DecayLoopB_sum_sum_norm_SB`, `DecayLoopB_SB_eq_zero`), `etaT`, `zt` by
  `Cm.eta`, `ztOf`, and `Im m ≥ √κ/2` by the constant `κm` of `DecayGen_Spec` (`Γ = 1 + κm⁻¹`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private DecayLoopB_norm_ite_le DecayLoopB_sum_pairs DecayLoopB_length_loopOf DecayLoopB_WF_loopOf DecayLoopB_mem_loopOf
  DecayLoopB_mem_eeLoop DecayLoopB_arith DecayLoopB_far_facts DecayLoopB_one_sub_u DecayLoopB_STWB_le
  DecayLoopB_STWB_nonneg DecayLoopB_diam_le_KLmaxDist DecayLoopB_size_eq DecayLoopB_SB_eq_zero from RBM3D.Induction.DecayLoopB

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (LoopDecay DecayLoopB_loopDecay_of DecayLoopB_bound_of mem_cutGlue_of_mem DecayLoopB_length_cutGlue
  DecayLoopB_wf_cutGlue far_cutGlueL_or_far_cutGlueR length_eeLoop eeLoop_WF mem_eeLoop_left mem_eeLoop_right
  norm_gloop_le_of_le_abs_im)

section Target6

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
  (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-! ## 1. The facts at hand and the normalisations -/

/-- The carrier facts read by the label decay (private bundle of the explicit hypotheses of the public results). -/
private structure SEforLnGen2_Hyp {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (E : ℕ → ℝ) : Prop where
  loop : StepDecompGen_LoopForm Cm E
  herm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian
  lc : Step34Gen_LCompat Cm Hf
  kc : Step34Gen_KCompat Cm
  row : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1
  supp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1

variable {Cm Hf}

private theorem SEforLnGen2_LI_eq {E : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLIg Cm Hf n τ ω (loopOf σ a) = Cm.toFlowFM.L n τ σ a ω := (hC.lc n τ σ a ω).symm

private theorem SEforLnGen2_KI_eq {E : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STKIg Cm n τ (loopOf σ a) = Cm.toFlowFM.K n τ σ a := (hC.kc n τ σ a).symm

private theorem SEforLnGen2_LKI_eq {E : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    STLKIg Cm Hf n τ ω (loopOf σ a) = Cm.toFlowFM.L n τ σ a ω - Cm.toFlowFM.K n τ σ a := by
  rw [← SEforLnGen2_LI_eq hC, ← SEforLnGen2_KI_eq hC]
  rfl

/-- `⟨(G_u(σ) - m(σ)) E_a⟩ = (𝓛 - 𝒦)_{u,(σ),(a)}` once the one-loop value holds (`DecayLoopB_avgErr_eq`). -/
private theorem SEforLnGen2_avgErr_eq {E : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) {n : ℕ} {τ : ℝ} {ω : sz.SeqΩ}
    (hone : ∀ (σ : Bool) (a : Zd d (sz.L n)), Cm.K n τ (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (σ : Bool) (a : Zd d (sz.L n)) :
    STavgErrg Cm Hf n τ ω σ a = STLKIg Cm Hf n τ ω ⟨[σ], [a]⟩ := by
  have h : STKIg Cm n τ ⟨[σ], [a]⟩ = STmsigg Cm n σ := by
    rw [← hone σ a, ← SEforLnGen2_KI_eq hC n τ (fun _ : Fin 1 => σ) (fun _ => a)]
    rfl
  change STLIg Cm Hf n τ ω ⟨[σ], [a]⟩ - STmsigg Cm n σ = STLIg Cm Hf n τ ω ⟨[σ], [a]⟩ - STKIg Cm n τ ⟨[σ], [a]⟩
  rw [h]

private theorem SEforLnGen2_norm_W_pow (n : ℕ) : ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by
  simp

/-- `Σ_{a,b} |S_{ab}| ≤ L^d` (row sums at most `1`; `DecayLoopB_sum_sum_norm_SB`). -/
private theorem SEforLnGen2_sum_sum_norm_le {L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hrow : ∀ a, ∑ b, ‖S a b‖ ≤ 1) : ∑ a : Zd d L, ∑ b : Zd d L, ‖S a b‖ ≤ (L : ℝ) ^ d := by
  calc ∑ a : Zd d L, ∑ b : Zd d L, ‖S a b‖ ≤ ∑ a : Zd d L, (1 : ℝ) := Finset.sum_le_sum fun a _ => hrow a
    _ = (L : ℝ) ^ d := by simp [Finset.card_univ]

/-! ## 2. One cut of a far loop -/

/-- **One cut of a far loop, pointwise** (`DecayLoopB_norm_mul_le_of_far_aux`): on the support `|a - b|_∞ ≤ 1` of `S`, one factor of a
cut of a far loop is small. -/
private theorem SEforLnGen2_norm_mul_le_of_far_aux {L : ℕ} [NeZero L] {F G : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay d L I.length R δF F) (hGd : LoopDecay d L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ))
    {a b : Zd d L} (hab : zdistInf d L (a - b) ≤ 1) :
    ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ δF * MG + MF * δG := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF a)
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG b)
  rcases far_cutGlueL_or_far_cutGlueR I hk hkl hx hy hxy hab with
    ⟨x', hx', y', hy', h⟩ | ⟨x', hx', y', hy', h⟩
  · have h1 := hFd _ (LoopIdx.wf_cutGlueL I a hI hk hkl hl)
      (LoopIdx.length_cutGlueL_le I a hk hkl hl) x' hx' y' hy' h
    have h2 := hG b
    have : ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ δF * MG :=
      mul_le_mul h1 h2 (norm_nonneg _) hδF
    nlinarith [mul_nonneg hMF hδG]
  · have h1 := hGd _ (LoopIdx.wf_cutGlueR I b hI hk hkl hl)
      (LoopIdx.length_cutGlueR_le I b hk hkl hl) x' hx' y' hy' h
    have h2 := hF a
    have : ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ MF * δG :=
      mul_le_mul h2 h1 (norm_nonneg _) hMF
    nlinarith [mul_nonneg hδF hMG]

/-- **One cut of a far loop, summed norms** (`DecayLoopB_sum_norm_glue_le_of_far`): `Σ_{a,b} ‖F(L_a)‖ ‖S_{ab}‖ ‖G(R_b)‖ ≤
L^d (δ_F M_G + M_F δ_G)` for a cut of a loop with two labels at distance `≥ 2R + 1` (row sums of `S` at most `1`, support `≤ 1`). -/
private theorem SEforLnGen2_sum_norm_glue_le_of_far {L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hrow : ∀ a, ∑ b, ‖S a b‖ ≤ 1) (hsupp : ∀ a b, S a b ≠ 0 → zdistInf d L (a - b) ≤ 1)
    {F G : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay d L I.length R δF F) (hGd : LoopDecay d L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ)) :
    ∑ a : Zd d L, ∑ b : Zd d L, ‖F (I.cutGlueL k l a)‖ * ‖S a b‖ *
        ‖G (I.cutGlueR k l b)‖ ≤ (L : ℝ) ^ d * (δF * MG + MF * δG) := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF 0)
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG 0)
  calc ∑ a : Zd d L, ∑ b : Zd d L, ‖F (I.cutGlueL k l a)‖ * ‖S a b‖ * ‖G (I.cutGlueR k l b)‖
      ≤ ∑ a : Zd d L, ∑ b : Zd d L, ‖S a b‖ * (δF * MG + MF * δG) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        by_cases hab : S a b = 0
        · rw [hab]; simp
        · have := SEforLnGen2_norm_mul_le_of_far_aux hI hk hkl hl hδF hδG hFd hGd hF hG hx hy hxy (hsupp a b hab)
          calc ‖F (I.cutGlueL k l a)‖ * ‖S a b‖ * ‖G (I.cutGlueR k l b)‖
              = ‖S a b‖ * (‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖) := by ring
            _ ≤ ‖S a b‖ * (δF * MG + MF * δG) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = (∑ a : Zd d L, ∑ b : Zd d L, ‖S a b‖) * (δF * MG + MF * δG) := by
        simp only [← Finset.sum_mul]
    _ ≤ (L : ℝ) ^ d * (δF * MG + MF * δG) :=
        mul_le_mul_of_nonneg_right (SEforLnGen2_sum_sum_norm_le S hrow)
          (add_nonneg (mul_nonneg hδF hMG) (mul_nonneg hMF hδG))


/-- One cut of a far loop, both orientations of `[𝒦 ∼ (𝓛 - 𝒦)]` (or `(𝓛-𝒦) × (𝓛-𝒦)`). -/
private theorem SEforLnGen2_cut {L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℂ)
    (hrow : ∀ a, ∑ b, ‖S a b‖ ≤ 1) (hsupp : ∀ a b, S a b ≠ 0 → zdistInf d L (a - b) ≤ 1)
    {F G : LoopIdx (Zd d L) → ℂ} {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hFb : ∀ J : LoopIdx (Zd d L), J.WF → 1 ≤ J.length → J.length ≤ m → ‖F J‖ ≤ B)
    (hGb : ∀ J : LoopIdx (Zd d L), J.WF → 1 ≤ J.length → J.length ≤ m → ‖G J‖ ≤ B)
    (hFd : LoopDecay d L m R δ F) (hGd : LoopDecay d L m R δ G)
    (σ : Fin m → Bool) (a : Fin m → Zd d L) {i j : Fin m}
    (hfar : 2 * R + 1 ≤ (zdistInf d L (a i - a j) : ℝ)) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ m) :
    ∑ x : Zd d L, ∑ y : Zd d L, ‖F ((loopOf σ a).cutGlueL k l x)‖ * ‖S x y‖ *
        ‖G ((loopOf σ a).cutGlueR k l y)‖ ≤ (L : ℝ) ^ d * (δ * B + B * δ) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hI : I.WF := DecayLoopB_WF_loopOf σ a
  have hl' : l ≤ I.length := hlen ▸ hl
  refine SEforLnGen2_sum_norm_glue_le_of_far S hrow hsupp hI hk hkl hl' hδ hδ
    (LoopDecay.mono hFd (le_of_eq hlen) le_rfl le_rfl)
    (LoopDecay.mono hGd (le_of_eq hlen) le_rfl le_rfl) (fun x => ?_) (fun y => ?_)
    (DecayLoopB_mem_loopOf σ a i) (DecayLoopB_mem_loopOf σ a j) hfar
  · refine hFb _ (LoopIdx.wf_cutGlueL I x hI hk hkl hl') ?_
      ((LoopIdx.length_cutGlueL_le I x hk hkl hl').trans_eq hlen)
    rw [LoopIdx.length_cutGlueL I x hk hkl hl']; omega
  · refine hGb _ (LoopIdx.wf_cutGlueR I y hI hk hkl hl') ?_
      ((LoopIdx.length_cutGlueR_le I y hk hkl hl').trans_eq hlen)
    rw [LoopIdx.length_cutGlueR I y hk hkl hl']; omega

/-! ## 3. Deterministic bounds on the four `ℰ`-terms of a loop with two far labels -/

variable {n : ℕ} {τ : ℝ} {ω : sz.SeqΩ}

/-- **`[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(m)}` of a loop with two far labels**: with `δ`-decay and the crude bound
`B` of `𝓛-𝒦` and `𝒦` on all loops of length `≤ m`, `‖ksimLK_l‖ ≤ W^d m² L^d 4 δ B`. -/
private theorem SEforLnGen2_det_ksimLK (hrow : ∀ a, ∑ b, ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ a b, Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ m →
      ‖STLKIg Cm Hf n τ ω J‖ ≤ B)
    (hKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ m →
      ‖STKIg Cm n τ J‖ ≤ B)
    (hdLK : LoopDecay d (sz.L n) m R δ (STLKIg Cm Hf n τ ω))
    (hdK : LoopDecay d (sz.L n) m R δ (STKIg Cm n τ))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {i j : Fin m}
    (hfar : 2 * R + 1 ≤ (zdistInf d (sz.L n) (a i - a j) : ℝ)) (l : ℕ) :
    ‖STksimLKg Cm Hf n τ ω l (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) ^ 2 * ((((sz.L n : ℕ) : ℝ)) ^ d * (4 * (δ * B)))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hB : 0 ≤ B := (norm_nonneg _).trans
    (hLKb ⟨[true], [0]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
      (by have := i.2; simp [LoopIdx.length]; omega))
  unfold STksimLKg STksimLKMg
  rw [norm_mul, SEforLnGen2_norm_W_pow, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine DecayLoopB_sum_pairs m _ (by positivity) fun k hk l' hl' => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  have h1 := SEforLnGen2_cut (Cm.S n) hrow hsupp hδ hLKb hKb hdLK hdK σ a hfar hk.1 hl'.1 hl'.2
  have h2 := SEforLnGen2_cut (Cm.S n) hrow hsupp hδ hKb hLKb hdK hdLK σ a hfar hk.1 hl'.1 hl'.2
  calc ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ((if (I.cutGlueR k l' y).length = l then
            STLKIg Cm Hf n τ ω (I.cutGlueL k l' x) * Cm.S n x y *
              STKIg Cm n τ (I.cutGlueR k l' y)
          else 0) +
         (if (I.cutGlueL k l' x).length = l then
            STKIg Cm n τ (I.cutGlueL k l' x) * Cm.S n x y *
              STLKIg Cm Hf n τ ω (I.cutGlueR k l' y)
          else 0))‖
      ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          (‖STLKIg Cm Hf n τ ω (I.cutGlueL k l' x)‖ * ‖Cm.S n x y‖ *
              ‖STKIg Cm n τ (I.cutGlueR k l' y)‖ +
            ‖STKIg Cm n τ (I.cutGlueL k l' x)‖ * ‖Cm.S n x y‖ *
              ‖STLKIg Cm Hf n τ ω (I.cutGlueR k l' y)‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => ?_))
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (DecayLoopB_norm_ite_le _ _).trans ?_; rw [norm_mul, norm_mul]
        · refine (DecayLoopB_norm_ite_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ (((sz.L n : ℕ) : ℝ)) ^ d * (δ * B + B * δ) + (((sz.L n : ℕ) : ℝ)) ^ d * (δ * B + B * δ) := by
        simp only [Finset.sum_add_distrib]
        exact add_le_add h1 h2
    _ = (((sz.L n : ℕ) : ℝ)) ^ d * (4 * (δ * B)) := by ring

/-- **`ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}` of a loop with two far labels**: `‖elklk‖ ≤ W^d m² L^d (δB + Bδ)`. -/
private theorem SEforLnGen2_det_elklk (hrow : ∀ a, ∑ b, ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ a b, Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ m →
      ‖STLKIg Cm Hf n τ ω J‖ ≤ B)
    (hdLK : LoopDecay d (sz.L n) m R δ (STLKIg Cm Hf n τ ω))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {i j : Fin m}
    (hfar : 2 * R + 1 ≤ (zdistInf d (sz.L n) (a i - a j) : ℝ)) :
    ‖STelklkg Cm Hf n τ ω (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) ^ 2 * ((((sz.L n : ℕ) : ℝ)) ^ d * (δ * B + B * δ))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hB : 0 ≤ B := (norm_nonneg _).trans
    (hLKb ⟨[true], [0]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
      (by have := i.2; simp [LoopIdx.length]; omega))
  unfold STelklkg STelklkMg
  rw [norm_mul, SEforLnGen2_norm_W_pow, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine DecayLoopB_sum_pairs m _ (by positivity) fun k hk l' hl' => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  refine le_trans ?_ (SEforLnGen2_cut (Cm.S n) hrow hsupp hδ hLKb hLKb hdLK hdLK σ a hfar hk.1 hl'.1 hl'.2)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun y _ => ?_))
  rw [norm_mul, norm_mul]
  exact le_rfl

/-- **`ℰ^{G̃}` of a loop with two far labels**: `‖egt‖ ≤ W^d m L^d B δ` (`B` bounds `|G̃|`, `δ` is
the decay of `𝓛` on loops of length `≤ m + 1`). -/
private theorem SEforLnGen2_det_egt (hrow : ∀ a, ∑ b, ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ a b, Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (havg : ∀ s a, ‖STavgErrg Cm Hf n τ ω s a‖ ≤ B)
    (hdLL : LoopDecay d (sz.L n) (m + 1) R δ (STLIg Cm Hf n τ ω))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {i j : Fin m}
    (hfar : R ≤ (zdistInf d (sz.L n) (a i - a j) : ℝ)) :
    ‖STegtg Cm Hf n τ ω (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * (B * δ))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hI : I.WF := DecayLoopB_WF_loopOf σ a
  unfold STegtg STegtMg
  rw [norm_mul, SEforLnGen2_norm_W_pow, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 m, ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        STavgErrg Cm Hf n τ ω (I.σ.getD (k - 1) false) x * Cm.S n x y *
          STLIg Cm Hf n τ ω (I.cutGlue k y)‖
      ≤ ∑ k ∈ Finset.Icc 1 m, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          ‖Cm.S n x y‖ * (B * δ) := by
        refine Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => ?_))
        simp only [Finset.mem_Icc] at hk
        have hkI : k ≤ I.length := hlen ▸ hk.2
        have hd : ‖STLIg Cm Hf n τ ω (I.cutGlue k y)‖ ≤ δ := by
          refine hdLL _ (DecayLoopB_wf_cutGlue I y hk.1 hkI hI) ?_ (a i)
            (mem_cutGlue_of_mem I y k (DecayLoopB_mem_loopOf σ a i)) (a j)
            (mem_cutGlue_of_mem I y k (DecayLoopB_mem_loopOf σ a j)) hfar
          rw [DecayLoopB_length_cutGlue I y hk.1 hkI hI, hlen]
        rw [norm_mul, norm_mul]
        calc ‖STavgErrg Cm Hf n τ ω (I.σ.getD (k - 1) false) x‖ * ‖Cm.S n x y‖ *
              ‖STLIg Cm Hf n τ ω (I.cutGlue k y)‖
            = ‖Cm.S n x y‖ * (‖STavgErrg Cm Hf n τ ω (I.σ.getD (k - 1) false) x‖ *
                ‖STLIg Cm Hf n τ ω (I.cutGlue k y)‖) := by ring
          _ ≤ ‖Cm.S n x y‖ * (B * δ) := mul_le_mul_of_nonneg_left
              (mul_le_mul (havg _ _) hd (norm_nonneg _) hB) (norm_nonneg _)
    _ ≤ (m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * (B * δ)) := by
        simp only [← Finset.sum_mul, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have h2 := mul_le_mul_of_nonneg_right (SEforLnGen2_sum_sum_norm_le (Cm.S n) hrow) (mul_nonneg hB hδ)
        nlinarith [mul_le_mul_of_nonneg_left h2 hm0]

/-- **`(ℰ⊗ℰ)^M` of a pair of label vectors with two far labels**: `‖ee‖ ≤ m W^d L^d δ`. -/
private theorem SEforLnGen2_det_ee (hrow : ∀ a, ∑ b, ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ a b, Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) {m : ℕ} {R δ : ℝ} (hδ : 0 ≤ δ)
    (hdLL : LoopDecay d (sz.L n) (2 * m + 2) R δ (STLIg Cm Hf n τ ω))
    (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) {i j : Fin (m + m)}
    (hfar : R ≤ (zdistInf d (sz.L n) (Fin.append a a' i - Fin.append a a' j) : ℝ)) :
    ‖STeeg Cm Hf n τ ω σ a a'‖ ≤
      (m : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ)) ^ d) * δ := by
  unfold STeeg STeeMg
  rw [norm_mul, SEforLnGen2_norm_W_pow]
  have key : ‖∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
      Cm.S n b b' *
        STLIg Cm Hf n τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤
      (m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * δ) := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
          ‖Cm.S n b b'‖ * δ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b' _ => ?_)))
          simp only [Finset.mem_Icc] at hk
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine hdLL _ (eeLoop_WF _ _ _ hk.1 (by simpa using hk.2) (by simp) (by simp) b b') ?_
            _ (DecayLoopB_mem_eeLoop σ a a' k b b' i) _ (DecayLoopB_mem_eeLoop σ a a' k b b' j) hfar
          rw [length_eeLoop _ _ _ (by simp; omega) (by simp) b b']
          simp
      _ ≤ (m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * δ) := by
          simp only [← Finset.sum_mul, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have h2 := mul_le_mul_of_nonneg_right (SEforLnGen2_sum_sum_norm_le (Cm.S n) hrow) hδ
          nlinarith [mul_le_mul_of_nonneg_left h2 hm0]
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖_‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * δ)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (m : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ)) ^ d) * δ := by ring



/-! ## 4. The good event and the decay of `𝒦` -/

/-- `ξ ≺ ζ` gives the event holding with high probability `{∀ u, ξ ≤ N^τ ζ}` at a law `μ` (`Prec.whp`). -/
private theorem SEforLnGen2_prec_whp (μ : Measure sz.SeqΩ) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt μ sz.size (fun n => {ω | ∀ u, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (le_of_eq ?_) hn
  congr 1
  ext ω
  simp [badSetAt]

/-- **The good event of the label decay** at size `n` (loop lengths `1 … K`, the scale `ℓ_u W^{τ'}`, the decay level `W^{-D''}`):
for every `u ∈ [s_n,t_n]`, charges and labels, `(|𝓛| + |𝓛-𝒦|)` is at most `N W^{-D''}` when `ℓ_u W^{τ'} ≤ diam_∞ a`, and
`|𝒦| ≤ N (W^{-d}B_{u,0})^{m-1}` (`DecayLoopB_Good`). -/
private def SEforLnGen2_Good (C : FlowFM sz) (s t : ℕ → ℝ) (K : ℕ) (τ' D'' : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∀ m ∈ Finset.Icc 1 K, ∀ (v : TimeIcc s t n) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)),
    ((‖C.L n (v : ℝ) σ a ω‖ + ‖C.L n (v : ℝ) σ a ω - C.K n (v : ℝ) σ a‖) *
      (if ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)
        then 1 else 0) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) ∧
    ‖C.K n (v : ℝ) σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n (v : ℝ)) ^ (m - 1)

/-- **The good event holds with high probability** (`DecayLoopB_whp_good`): the intersection over the `K` loop lengths of `STDecayLoopUgL`
(at `τ', D''`) and of `stKbound_timeIccgL` (both at the exponent `τ = 1`). -/
private theorem SEforLnGen2_whp_good (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] {C : FlowFM sz} {𝔠 𝔡 : ℝ}
    {s t : ℕ → ℝ} (hA : sz.Admissible 𝔠 𝔡) (hKb : STKboundgL C μ)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hU : STDecayLoopUgL C μ s t) (K : ℕ) {τ' D'' : ℝ} (hτ' : 0 < τ') (hD'' : 0 < D'') :
    HighProbAt μ sz.size (fun n => {ω | SEforLnGen2_Good C s t K τ' D'' n ω}) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hN
  have hΞ : ∀ m : ↥(Finset.Icc 1 K), HighProbAt μ sz.size (fun n =>
      {ω | ∀ u : TimeIcc s t n × (Fin m.1 → Bool) × (Fin m.1 → Zd d (sz.L n)),
          (‖C.L n (u.1 : ℝ) u.2.1 u.2.2 ω‖ +
            ‖C.L n (u.1 : ℝ) u.2.1 u.2.2 ω - C.K n (u.1 : ℝ) u.2.1 u.2.2‖) *
          (if ellT (sz.L n) (sz.lam n) (u.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf u.2.2 : ℝ)
            then 1 else 0) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')} ∩
      {ω | ∀ u : TimeIcc s t n × (Fin m.1 → Bool) × (Fin m.1 → Zd d (sz.L n)),
          ‖C.K n (u.1 : ℝ) u.2.1 u.2.2‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n (u.1 : ℝ)) ^ (m.1 - 1)}) := by
    intro m
    have hm1 : 1 ≤ m.1 := (Finset.mem_Icc.1 m.2).1
    refine HighProbAt.inter hsize ?_ ?_
    · exact SEforLnGen2_prec_whp μ (hU m.1 hm1 τ' D'' hτ' hD'') (τ := 1) one_pos
    · exact SEforLnGen2_prec_whp μ (stKbound_timeIccgL sz C μ hN hKb s t hs0 hst ht1 m.1 hm1) (τ := 1) one_pos
  have hbi := HighProbAt.biInter (P := μ) (size := sz.size)
    (K := fun _ => ↥(Finset.Icc 1 K)) (C := 1) zero_le_one
    (by
      filter_upwards [hN.eventually_ge_atTop (K : ℝ)] with n hn
      rw [Real.rpow_one, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel]
      exact hn)
    (fun D hD => Filter.eventually_all.2 fun m => hΞ m D hD)
  refine HighProbAt.mono hbi (Eventually.of_forall fun n ω hω => ?_)
  intro m hm v σ a
  have := Set.mem_iInter.1 hω ⟨m, hm⟩
  exact ⟨this.1 (v, σ, a), this.2 (v, σ, a)⟩

/-- **The `𝒦` decay bundle** at size `n`: `STKcalDecaygL` for every loop length `1 … K`, at the exponents `(τ, D)` (`DecayLoopB_KDec`). -/
private def SEforLnGen2_KDec (C : FlowFM sz) (K : ℕ) (τ D : ℝ) (n : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 K, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)),
    ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ ≤ (KLmaxDist d (sz.L n) a : ℝ) →
      ‖C.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

private theorem SEforLnGen2_KDec_ev {C : FlowFM sz} (hKcal : STKcalDecaygL C) (K : ℕ) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ n in atTop, SEforLnGen2_KDec C K τ D n := by
  unfold SEforLnGen2_KDec
  rw [Filter.eventually_all_finset]
  intro j hj
  exact hKcal j (Finset.mem_Icc.1 hj).1 τ D hτ hD


private theorem SEforLnGen2_LKI_def {n : ℕ} {τ : ℝ} {ω : sz.SeqΩ} (J : LoopIdx (Zd d (sz.L n))) :
    STLKIg Cm Hf n τ ω J = STLIg Cm Hf n τ ω J - STKIg Cm n τ J := rfl

/-- `𝓛_I` is the loop at the spectral value `ztOf (Cm.m n) (E n) τ` (the loop form). -/
private theorem SEforLnGen2_LI_eq' {E : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) {n : ℕ} {τ : ℝ} {ω : sz.SeqΩ}
    {J : LoopIdx (Zd d (sz.L n))} :
    ‖STLIg Cm Hf n τ ω J‖ =
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hf n τ ω)) (ztOf (Cm.m n) (E n) τ) J‖ := by
  rw [show STLIg Cm Hf n τ ω J = _ from (hC.loop n).2.2.1 τ (Hf n τ ω) J]


/-- **The context at `(n, u, ω)` for a far label vector** (`ℓ_u < L`): from the good event and the
decay of `𝒦` (`DecayLoopB_KDec`), `𝓛`, `𝓛-𝒦`, `𝒦` have `(R, δ)` decay on loops of length `≤ K`
(`R = ℓ_u W^{τ'}`, `δ = N W^{-D''}`) and `𝓛`, `𝒦` are `≤ B_c = (2ΓN)^K` there (`η_u^{-1} ≤ ΓN` and
`W^{-d}B_{u,0} ≤ 2`, both from `ℓ_u < L`, i.e. `1 - u ≥ N⁻¹`). -/
private theorem SEforLnGen2_ctx {E s t : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) {κm 𝔡 : ℝ} (hκm : 0 < κm)
    (hmκ : ∀ n, κm ≤ (Cm.m n).im) (hη_eq : ∀ (n : ℕ) (t : ℝ), Cm.eta n t = (1 - t) * (Cm.m n).im)
    (hd : 3 ≤ d) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (h𝔡 : 0 < 𝔡)
    {K : ℕ} {τ' D'' : ℝ} {n : ℕ} (v : TimeIcc s t n) (ω : sz.SeqΩ)
    (hwo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹)
    (hKd : SEforLnGen2_KDec Cm.toFlowFM K τ' D'' n) (hG : SEforLnGen2_Good Cm.toFlowFM s t K τ' D'' n ω)
    (hℓL : ellT (sz.L n) (sz.lam n) (v : ℝ) < ((sz.L n : ℕ) : ℝ))
    {R δ Bc : ℝ} (hR : R = ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ')
    (hδ : δ = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))
    (hBc : Bc = (2 * (1 + κm⁻¹) * ((sz.size n : ℕ) : ℝ)) ^ K) :
    LoopDecay d (sz.L n) K R δ (STLIg Cm Hf n (v : ℝ) ω) ∧
    LoopDecay d (sz.L n) K R δ (STLKIg Cm Hf n (v : ℝ) ω) ∧
    LoopDecay d (sz.L n) K R δ (STKIg Cm n (v : ℝ)) ∧
    (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ K →
      ‖STLIg Cm Hf n (v : ℝ) ω J‖ ≤ Bc) ∧
    (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ K →
      ‖STKIg Cm n (v : ℝ) J‖ ≤ Bc) := by
  have hu0 : 0 ≤ (v : ℝ) := (hs0 n).trans v.2.1
  have hu1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 n)
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (v : ℝ) :=
    DecayLoopB_one_sub_u (by omega) hL3 hW1 hlam0 hgW hu1 hℓL
  have hv : 0 < 1 - (v : ℝ) := by linarith
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - (v : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hNu hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 1 + κm⁻¹ := ⟨_, rfl⟩
  have hκi : 0 < κm⁻¹ := inv_pos.2 hκm
  have hΓ1 : 1 ≤ Γ := by rw [hΓ]; linarith
  rw [← hΓ] at hBc
  have hμ : κm ≤ (Cm.m n).im := hmκ n
  have hηeq : Cm.eta n (v : ℝ) = (1 - (v : ℝ)) * (Cm.m n).im := hη_eq n _
  have hη : 0 < Cm.eta n (v : ℝ) := by
    rw [hηeq]; exact mul_pos hv (lt_of_lt_of_le hκm hμ)
  have hηΓ : (Cm.eta n (v : ℝ))⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (1 - (v : ℝ)) * κm ≤ Cm.eta n (v : ℝ) := by
      rw [hηeq]; exact mul_le_mul_of_nonneg_left hμ hv.le
    have h2 : (Cm.eta n (v : ℝ))⁻¹ ≤ ((1 - (v : ℝ)) * κm)⁻¹ := inv_anti₀ (by positivity) h1
    have h3 : ((1 - (v : ℝ)) * κm)⁻¹ = κm⁻¹ * (1 - (v : ℝ))⁻¹ := by rw [mul_inv]; ring
    have h4 : (1 - (v : ℝ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    have h5 : κm⁻¹ ≤ Γ := by rw [hΓ]; linarith
    calc (Cm.eta n (v : ℝ))⁻¹ ≤ ((1 - (v : ℝ)) * κm)⁻¹ := h2
      _ = κm⁻¹ * (1 - (v : ℝ))⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := mul_le_mul h5 h4 (inv_nonneg.2 hv.le) (by linarith)
  have hBctl : sz.Bctl n (v : ℝ) ≤ 2 := DecayLoopB_STWB_le sz n 0 hu1 hg1 hN1u
  have hBctl0 : 0 ≤ sz.Bctl n (v : ℝ) := DecayLoopB_STWB_nonneg sz n _ 0
  have hΘ : 2 ≤ 2 * Γ * ((sz.size n : ℕ) : ℝ) := by nlinarith
  have hWD0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hWpos.le _
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hN1
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- decay of `𝓛` and `𝓛 - 𝒦`
  have hgood : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)),
      R ≤ (STdiamInf a : ℝ) →
      ‖Cm.toFlowFM.L n (v : ℝ) σ a ω‖ + ‖Cm.toFlowFM.L n (v : ℝ) σ a ω - Cm.toFlowFM.K n (v : ℝ) σ a‖ ≤ δ := by
    intro m hm σ a hRa
    have h := (hG m hm v σ a).1
    have hRa' : ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) := by
      rw [← hR]; exact hRa
    simp only [hRa', ↓reduceIte, mul_one] at h
    rw [hδ]; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine DecayLoopB_loopDecay_of _ fun m hm σ a hRa => ?_
    rw [SEforLnGen2_LI_eq hC]
    have := hgood m hm σ a hRa
    linarith [norm_nonneg (Cm.toFlowFM.L n (v : ℝ) σ a ω - Cm.toFlowFM.K n (v : ℝ) σ a)]
  · refine DecayLoopB_loopDecay_of _ fun m hm σ a hRa => ?_
    rw [SEforLnGen2_LKI_eq hC]
    have := hgood m hm σ a hRa
    linarith [norm_nonneg (Cm.toFlowFM.L n (v : ℝ) σ a ω)]
  · refine DecayLoopB_loopDecay_of _ fun m hm σ a hRa => ?_
    rw [SEforLnGen2_KI_eq hC]
    have hKm := hKd m hm (v : ℝ) hu0 hu1 σ a (by
      rw [← hR]; exact hRa.trans (by exact_mod_cast DecayLoopB_diam_le_KLmaxDist a))
    have : ‖Cm.toFlowFM.K n (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := hKm
    rw [hδ]
    calc ‖Cm.toFlowFM.K n (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := this
      _ = 1 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hN1' hWD0
  · -- `‖𝓛_u(J)‖ ≤ η_u^{-|J|} ≤ (ΓN)^{|J|} ≤ B_c`
    intro J hJ hJ1 hJK
    have hHh : (blockMat d (sz.L n) (sz.W n) (Hf n (v : ℝ) ω)).IsHermitian :=
      (hC.herm n (v : ℝ) ω).submatrix _
    have hzim : Cm.eta n (v : ℝ) ≤ |(ztOf (Cm.m n) (E n) (v : ℝ)).im| := by
      rw [ztOf_im, ← (hC.loop n).2.2.2 (v : ℝ), abs_of_pos hη]
    have hg := norm_gloop_le_of_le_abs_im (z := ztOf (Cm.m n) (E n) (v : ℝ)) (W := sz.W n) hHh hη hzim J hJ hJ1
    have hWinv : (((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ (J.a.length - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW1r))
    have hΓN1 : 1 ≤ Γ * ((sz.size n : ℕ) : ℝ) := by nlinarith
    rw [SEforLnGen2_LI_eq' hC]
    rw [hBc]
    calc ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hf n (v : ℝ) ω))
          (ztOf (Cm.m n) (E n) (v : ℝ)) J‖
        ≤ (Cm.eta n (v : ℝ))⁻¹ ^ J.a.length * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (J.a.length - 1) := hg
      _ ≤ (Γ * ((sz.size n : ℕ) : ℝ)) ^ J.a.length * 1 := by
          refine mul_le_mul (pow_le_pow_left₀ (inv_nonneg.2 hη.le) hηΓ _) hWinv (by positivity)
            (by positivity)
      _ ≤ (Γ * ((sz.size n : ℕ) : ℝ)) ^ K := by
          rw [mul_one]; exact pow_le_pow_right₀ hΓN1 hJK
      _ ≤ (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ K := by
          refine pow_le_pow_left₀ (by positivity) ?_ K
          nlinarith
  · -- `‖𝒦_u(J)‖ ≤ N (W^{-d}B_{u,0})^{|J|-1} ≤ N 2^{|J|-1} ≤ B_c`
    refine DecayLoopB_bound_of _ (K := K) fun m hm σ a => ?_
    rw [SEforLnGen2_KI_eq hC]
    have hm' := Finset.mem_Icc.1 hm
    have h := (hG m hm v σ a).2
    rw [Real.rpow_one] at h
    rw [hBc]
    have hΘ1 : (1 : ℝ) ≤ 2 * Γ * ((sz.size n : ℕ) : ℝ) := by linarith
    calc ‖Cm.toFlowFM.K n (v : ℝ) σ a‖
        ≤ ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (v : ℝ)) ^ (m - 1) := h
      _ ≤ ((sz.size n : ℕ) : ℝ) * 2 ^ (m - 1) := by gcongr
      _ ≤ (2 * Γ * ((sz.size n : ℕ) : ℝ)) * (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ (m - 1) := by
          refine mul_le_mul (by nlinarith) (pow_le_pow_left₀ (by norm_num) hΘ _) (by positivity)
            (by positivity)
      _ = (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ m := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ K := pow_le_pow_right₀ hΘ1 hm'.2


/-- **The four label-decay statements at once, with high probability.**  Parameters: `τ' = ε/2`,
`D'' = D + 1 + (2k+4)/𝔠`.  On the good event (`DecayLoopB_Good`, `K = 2k+2`) and eventually in `n`,
for every `u ∈ [s_n,t_n]`, every charge vector and every far label vector, the four `ℰ`-terms are
`≤ W^{-D}`:  `4 k² N (δ B') ≤ W^{-D}` with `δ = N W^{-D''}`, `B' = 2 (2ΓN)^{2k+2}`
(`DecayLoopB_arith`). -/
private theorem SEforLnGen2_master {E s t : ℕ → ℝ} (hC : SEforLnGen2_Hyp Cm Hf E) (μ : Measure sz.SeqΩ)
    [IsProbabilityMeasure μ] {κm 𝔠 𝔡 : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) (hd : 3 ≤ d) (hA : sz.Admissible 𝔠 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hKb : STKboundgL Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t)
    {k : ℕ} (hk : 2 ≤ k) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    HighProbAt μ sz.size (fun n => {ω | ∀ v : TimeIcc s t n,
      (∀ σ : Fin k → Bool, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun a : Fin k → Zd d (sz.L n) =>
          STegtg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      (∀ (σ : Fin k → Bool) (l : ℕ), EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun a : Fin k → Zd d (sz.L n) =>
          STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      (∀ σ : Fin k → Bool, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun a : Fin k → Zd d (sz.L n) =>
          STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      (∀ σ : Fin k → Bool, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun b : Fin (k + k) → Zd d (sz.L n) =>
          STeeg Cm Hf n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i))
            (fun i => b (Fin.natAdd k i))))}) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  obtain ⟨hκm, hmκ, hη_eq⟩ := hspec
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 1 + κm⁻¹ := ⟨_, rfl⟩
  obtain ⟨D'', hD''⟩ : ∃ D'' : ℝ, D'' = D + 1 + ((2 * k + 4 : ℕ) : ℝ) / 𝔠 := ⟨_, rfl⟩
  have hD''0 : 0 < D'' := by rw [hD'']; positivity
  have hτ' : 0 < ε / 2 := half_pos hε
  have hW := SEforLnGen2_whp_good μ hA hKb hs0 hst ht1 hU (2 * k + 2) hτ' hD''0
  refine HighProbAt.mono hW ?_
  have hκi : 0 < κm⁻¹ := inv_pos.2 hκm
  have hΓ1 : 1 ≤ Γ := by rw [hΓ]; linarith
  have hΓ0 : 0 ≤ Γ := by linarith
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hB h1
  have e1 : ∀ᶠ n in atTop, 3 * (d : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop hτ').comp hWtend).eventually_ge_atTop _
  have e2 := SEforLnGen2_KDec_ev hKcal (2 * k + 2) hτ' hD''0
  have e3 : ∀ᶠ n in atTop, 8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2) ≤ ((sz.W n : ℕ) : ℝ) :=
    hWtend.eventually_ge_atTop _
  filter_upwards [e1, e2, e3, hB, hWO, hone] with n he1 he2 he3 hbw hwo hone_n
  intro ω hω v
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hX : ((sz.W n : ℕ) : ℝ) ^ ε = ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hWpos]; ring_nf
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (v : ℝ) := one_le_ellT hL1r
  -- the explicit constants
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
    ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
    ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ,
      Bc = (2 * (1 + κm⁻¹) * ((sz.size n : ℕ) : ℝ)) ^ (2 * k + 2) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hBc1 : 1 ≤ Bc := by
    rw [hBc, ← hΓ]
    exact one_le_pow₀ (by nlinarith)
  -- the package at a far label vector
  have hpkg : ∀ x : Zd d (sz.L n),
      ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) (v : ℝ) ≤ (zdistD d (sz.L n) x : ℝ) →
      2 * R + 1 ≤ (zdistInf d (sz.L n) x : ℝ) ∧
      LoopDecay d (sz.L n) (2 * k + 2) R δ (STLIg Cm Hf n (v : ℝ) ω) ∧
      LoopDecay d (sz.L n) (2 * k + 2) R δ (STLKIg Cm Hf n (v : ℝ) ω) ∧
      LoopDecay d (sz.L n) (2 * k + 2) R δ (STKIg Cm n (v : ℝ)) ∧
      (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ 2 * k + 2 →
        ‖STLIg Cm Hf n (v : ℝ) ω J‖ ≤ Bc) ∧
      (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ 2 * k + 2 →
        ‖STKIg Cm n (v : ℝ) J‖ ≤ Bc) := by
    intro x hx
    have hff := DecayLoopB_far_facts (by omega : 1 ≤ d) hℓ1 he1 x (by rw [← hX]; exact hx) hL3
    refine ⟨by rw [hR]; exact hff.1, ?_⟩
    exact SEforLnGen2_ctx hC hκm hmκ hη_eq hd hs0 ht1 h𝔡 v ω hwo he2 hω hff.2 hR hδ hBc
  -- the final count
  have hfin : 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
      (δ * (2 * Bc)))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have := DecayLoopB_arith (N := ((sz.size n : ℕ) : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (Γ := Γ)
      (𝔠 := 𝔠) (D := D) (D'' := D'') (k := k) hN1 hΓ0 hWpos h𝔠 hbw he3 hD''
    have hNe := DecayLoopB_size_eq sz n
    have hprod : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc))) =
        ((sz.size n : ℕ) : ℝ) * (δ * (2 * Bc)) := by rw [← mul_assoc, ← hNe]
    rw [hprod, hδ, hBc, ← hΓ]
    calc _ = 4 * (k : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) *
          ((((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) *
            (2 * (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ (2 * k + 2))) := by ring
      _ ≤ _ := this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hMv0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc))) := by
    have : 0 ≤ Bc := by linarith
    positivity
  have hB'1 : 1 ≤ 2 * Bc := by linarith
  have hk4 : (k : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  have hk24 : 2 * (k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ℰ^{G̃}`
    intro σ a ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (a i - a j) hij
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have havg : ∀ (s' : Bool) (a' : Zd d (sz.L n)),
        ‖STavgErrg Cm Hf n (v : ℝ) ω s' a'‖ ≤ 2 * Bc := by
      intro s' a'
      rw [SEforLnGen2_avgErr_eq hC (hone_n _ ((hs0 n).trans v.2.1) (v.2.2.trans_lt (ht1 n)))]
      have hJ : (⟨[s'], [a']⟩ : LoopIdx (Zd d (sz.L n))).WF := by simp [LoopIdx.WF]
      have hl1 : (⟨[s'], [a']⟩ : LoopIdx (Zd d (sz.L n))).length = 1 := by simp [LoopIdx.length]
      have h1 := hLb _ hJ (by omega) (by omega)
      have h2 := hKb _ hJ (by omega) (by omega)
      rw [SEforLnGen2_LKI_def]
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hdet := SEforLnGen2_det_egt (Cm := Cm) (Hf := Hf) (n := n) (τ := (v : ℝ)) (ω := ω)
      (hC.row n) (hC.supp n) (R := R) (δ := δ) (B := 2 * Bc) hδ0 (by linarith) havg
      (LoopDecay.mono hdLL (by omega) le_rfl le_rfl) σ a (i := i) (j := j) (by linarith)
    refine hdet.trans ?_
    calc _ = (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc)))) := by
          ring
      _ ≤ 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := mul_le_mul_of_nonneg_right hk4 hMv0
      _ ≤ _ := hfin
  · -- `[𝒦^{(l)} ∼ (𝓛-𝒦)]`
    intro σ l a ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (a i - a j) hij
    have hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
        ‖STLKIg Cm Hf n (v : ℝ) ω J‖ ≤ 2 * Bc := by
      intro J hJ h1 h2
      have a1 := hLb J hJ h1 (by omega)
      have a2 := hKb J hJ h1 (by omega)
      rw [SEforLnGen2_LKI_def]
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hdet := SEforLnGen2_det_ksimLK (Cm := Cm) (Hf := Hf) (n := n) (τ := (v : ℝ)) (ω := ω)
      (hC.row n) (hC.supp n) (R := R) (δ := δ) (B := 2 * Bc) hδ0 hLKb
      (fun J hJ h1 h2 => (hKb J hJ h1 (by omega)).trans (by linarith))
      (LoopDecay.mono hdLK (by omega) le_rfl le_rfl) (LoopDecay.mono hdK (by omega) le_rfl le_rfl)
      σ a (i := i) (j := j) hfar l
    refine hdet.trans ?_
    calc _ = 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := by ring
      _ ≤ _ := hfin
  · -- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}`
    intro σ a ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (a i - a j) hij
    have hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
        ‖STLKIg Cm Hf n (v : ℝ) ω J‖ ≤ 2 * Bc := by
      intro J hJ h1 h2
      have a1 := hLb J hJ h1 (by omega)
      have a2 := hKb J hJ h1 (by omega)
      rw [SEforLnGen2_LKI_def]
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hdet := SEforLnGen2_det_elklk (Cm := Cm) (Hf := Hf) (n := n) (τ := (v : ℝ)) (ω := ω)
      (hC.row n) (hC.supp n) (R := R) (δ := δ) (B := 2 * Bc) hδ0 hLKb
      (LoopDecay.mono hdLK (by omega) le_rfl le_rfl) σ a (i := i) (j := j) hfar
    refine hdet.trans ?_
    calc _ = 2 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := by ring
      _ ≤ 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := mul_le_mul_of_nonneg_right hk24 hMv0
      _ ≤ _ := hfin
  · -- `(ℰ⊗ℰ)^M`
    intro σ b ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (b i - b j) hij
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have hb : Fin.append (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)) = b :=
      Fin.append_castAdd_natAdd
    have hdet := SEforLnGen2_det_ee (Cm := Cm) (Hf := Hf) (n := n) (τ := (v : ℝ)) (ω := ω)
      (hC.row n) (hC.supp n) (R := R) (δ := δ) hδ0 hdLL σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))
      (i := i) (j := j) (by rw [hb]; linarith)
    refine hdet.trans ?_
    calc _ = (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * δ := by ring
      _ ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc)))) := by
          have h1 : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ ≤
              ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc))) := by
            have h0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by positivity
            calc ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ
                = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ * 1 := (mul_one _).symm
              _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ * (2 * Bc) :=
                  mul_le_mul_of_nonneg_left hB'1 (by positivity)
              _ = _ := by ring
          calc (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * δ
              = (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ) := by ring
            _ ≤ (k : ℝ) * _ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := mul_le_mul_of_nonneg_right hk4 hMv0
      _ ≤ _ := hfin

end Target6

/-! ## 5. The label decay of the four `ℰ`-terms -/

section Public

variable {d : ℕ}

/-- **`stEtermDecaygL_egt`** (conclusion head `STEKDecaygL`; band `stEtermDecay`, first conjunct):
the label decay of `ℰ^{G̃,(k)}` ((4.52) `deccA0` w.h.p., uniformly in `v ∈ [s_n,t_n]`), `k ≥ 2`, from `lem_decayLoop` (`STDecayLoopUgL`), the
far decay of `𝒦` (`STKcalDecaygL`), Lemma 2.16 (`ML:Kbound`, `STKboundgL`) and the carrier facts.  The hypothesis list includes the one-loop value of
`SEforLnGen_Facts` (`hone`: it links `STmsigg` to `𝒦^{(1)}`, which the bound of `tr(G̃(σ) E_a)` needs). -/
theorem stEtermDecaygL_egt (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 : ℝ) (E s t : ℕ → ℝ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hKb : STKboundgL Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t)
    (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) :
    STEKDecaygL μ s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) => STegtg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) :=
  fun ε D hε hD => HighProbAt.mono
    (SEforLnGen2_master ⟨hloop, hherm, hL, hK, hrow, hsupp⟩ μ hspec hd hA hs0 hst ht1 hone hKb hKcal hU hk hε hD)
    (Eventually.of_forall fun n ω hω v => (hω v).1 σ)

/-- **`stEtermDecaygL_ksim`**: the label decay of `[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)}` (second conjunct of `stEtermDecay`), every `l`. -/
theorem stEtermDecaygL_ksim (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 : ℝ) (E s t : ℕ → ℝ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hKb : STKboundgL Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t)
    (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) (l : ℕ) :
    STEKDecaygL μ s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) => STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩) :=
  fun ε D hε hD => HighProbAt.mono
    (SEforLnGen2_master ⟨hloop, hherm, hL, hK, hrow, hsupp⟩ μ hspec hd hA hs0 hst ht1 hone hKb hKcal hU hk hε hD)
    (Eventually.of_forall fun n ω hω v => (hω v).2.1 σ l)

/-- **`stEtermDecaygL_elklk`**: the label decay of `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}` (third conjunct of `stEtermDecay`). -/
theorem stEtermDecaygL_elklk (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 : ℝ) (E s t : ℕ → ℝ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hKb : STKboundgL Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t)
    (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) :
    STEKDecaygL μ s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) => STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) :=
  fun ε D hε hD => HighProbAt.mono
    (SEforLnGen2_master ⟨hloop, hherm, hL, hK, hrow, hsupp⟩ μ hspec hd hA hs0 hst ht1 hone hKb hKcal hU hk hε hD)
    (Eventually.of_forall fun n ω hω v => (hω v).2.2.1 σ)

/-- **`stEtermDecaygL_ee`**: the label decay of `(ℰ⊗ℰ)^{M,(k)}` as a tensor of the `2k` labels `(a, a')` (fourth conjunct of
`stEtermDecay`). -/
theorem stEtermDecaygL_ee (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 : ℝ) (E s t : ℕ → ℝ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hKb : STKboundgL Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t)
    (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) :
    STEKDecaygL μ s t (m := k + k)
      (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
        STeeg Cm Hf n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))) :=
  fun ε D hε hD => HighProbAt.mono
    (SEforLnGen2_master ⟨hloop, hherm, hL, hK, hrow, hsupp⟩ μ hspec hd hA hs0 hst ht1 hone hKb hKcal hU hk hε hD)
    (Eventually.of_forall fun n ω hω v => (hω v).2.2.2 σ)

/-- **The bundle `stEtermDecaygL`** (band `stEtermDecay`): the four
label decays at once, for every `k ≥ 2` and charge vector `σ`. -/
theorem stEtermDecaygL (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡 : ℝ) (E s t : ℕ → ℝ)
    (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E)
    (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm)
    (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1)
    (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ)
    (hKb : STKboundgL Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t) :
    ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
      STEKDecaygL μ s t (m := k)
          (fun n v ω (a : Fin k → Zd d (sz.L n)) => STegtg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL μ s t (m := k)
          (fun n v ω (a : Fin k → Zd d (sz.L n)) => STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL μ s t (m := k)
          (fun n v ω (a : Fin k → Zd d (sz.L n)) => STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL μ s t (m := k + k)
          (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
            STeeg Cm Hf n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))) :=
  fun k hk σ =>
    ⟨stEtermDecaygL_egt hd sz Cm Hf μ κm 𝔠 𝔡 E s t hspec hA hloop hherm hs0 hst ht1 hL hK hrow hsupp hone hKb hKcal hU k hk σ,
     fun l => stEtermDecaygL_ksim hd sz Cm Hf μ κm 𝔠 𝔡 E s t hspec hA hloop hherm hs0 hst ht1 hL hK hrow hsupp hone hKb hKcal hU k hk σ l,
     stEtermDecaygL_elklk hd sz Cm Hf μ κm 𝔠 𝔡 E s t hspec hA hloop hherm hs0 hst ht1 hL hK hrow hsupp hone hKb hKcal hU k hk σ,
     stEtermDecaygL_ee hd sz Cm Hf μ κm 𝔠 𝔡 E s t hspec hA hloop hherm hs0 hst ht1 hL hK hrow hsupp hone hKb hKcal hU k hk σ⟩

end Public

end RBM.BA
