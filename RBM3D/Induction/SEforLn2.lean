/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.SEforLn1
import RBM3D.Induction.ScaleFacts

/-!
# S3-09 (ticket T2139): `lem:SEforLn`, parts (3) and (4), and the pin `STSEforLn`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: `lem:SEforLn` (`3_5:1035-1046`), proof
`3_5:1063-1093`: `(eq:sumtwoloop)`, `(eq:sumtwoloop2)`, `(yi2oslxj2)`, `(u2jzooi-2)`,
`(wardineq_K)`, `(def:XiL)`, `(def:XIL-K)`.

* `stSEforLn_part3`: `‖ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}‖ ≺ B^k η⁻¹ (Σ_{n'=⌈k/2⌉+1}^{k-1} Ξ̂^{𝓛-𝒦}_{k+2-n'}
  (Ξ̂^{𝓛}_{n'₁} Ξ̂^{𝓛}_{n'₂})^{1/2} + B^{1/6} Ξ̂^{𝓛-𝒦}_k)`: the third conjunct of `STSEforLnConcl`
  (`Step34Pins.lean:363`), uniformly in `u ∈ [s,t]` and the labels.  The stochastic input is the
  uniform 2-`G`-loop estimate `STGdecayW` (the third conjunct of `STStep2Concl`); the `𝒦`-loop Ward
  bound is the deterministic `stKward_timeIcc`; the contraction inequality is `stContract_holds`.
* `stSEforLn_part4`: `‖(ℰ⊗ℰ)^{M,(k)}‖ ≺ B^{2k-1/(2q)} η⁻¹ Ξ̂^{𝓛}_{2k-1} (Ξ̂^{𝓛}_{4q})^{1/(2q)}`,
  every `q ≥ 1`: the fourth conjunct; deterministic (the second inequality of `stContract_holds`).
* `stSEforLn_holds d : STSEforLn d`: the assembly with the parts (1), (2) of `SEforLn1.lean`,
  `𝔠_d = min (1/100) (1/(30 C_d))`.

The deterministic cores (§1-§5, §9) are bounds for every sample `ω` and every time `u ∈ [0,1)`,
`|E| < 2`; the `≺` is assembled in §7 and §9 by the inclusion of the bad events.  The private
helpers of `SEforLn1.lean` that are needed again are copied with the prefix `SEforLn2_`; every
helper that the ticket does not pin is `private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Lists, rotation (copies of `SEforLn1_*`) -/

private theorem SEforLn2_exists_ofFn {α : Type*} (l : List α) {m : ℕ} (h : l.length = m) :
    ∃ f : Fin m → α, List.ofFn f = l := by
  subst h
  exact ⟨l.get, List.ofFn_get l⟩

section Rot

variable {d L W : ℕ} [NeZero L]

private theorem SEforLn2_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I
      = Matrix.trace (((I.σ.zip I.a).map fun p => Gres H z p.1 * Eblk d L W p.2).prod) := by
  have hfold : ∀ l : List (Bool × Zd d L),
      l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1
        = (l.map fun p => Gres H z p.1 * Eblk d L W p.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  unfold loopL
  rw [hfold]

private theorem SEforLn2_loopL_rotate (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool)
    (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [SEforLn2_loopL_eq_prod, SEforLn2_loopL_eq_prod]
  simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
  rw [List.zip_append h]
  simp only [List.map_append, List.prod_append, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

private theorem SEforLn2_loopL_rotate_iter {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} :
    ∀ (j : ℕ) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      loopL d L W H z ⟨σ.rotate j, a.rotate j⟩ = loopL d L W H z ⟨σ, a⟩ := by
  intro j
  induction j with
  | zero => intro σ a _; simp
  | succ j ih =>
    intro σ a h
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at h
      | cons b a =>
        have h' : σ.length = a.length := by simpa using h
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (SEforLn2_loopL_rotate H z s b σ a h').symm

end Rot

variable {d : ℕ} (sz : Sizes d)

private theorem SEforLn2_STLI_rotate (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (j : ℕ) (σ : List Bool)
    (a : List (Zd d (sz.L n))) (h : σ.length = a.length) :
    sz.STLI n E τ ω ⟨σ.rotate j, a.rotate j⟩ = sz.STLI n E τ ω ⟨σ, a⟩ :=
  SEforLn2_loopL_rotate_iter j σ a h

private theorem SEforLn2_STKI_rotate (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (hτ : τ ∈ Set.Ico (0 : ℝ) 1)
    (j : ℕ) (σ : List Bool) (a : List (Zd d (sz.L n))) (h : σ.length = a.length) :
    sz.STKI n E τ ⟨σ.rotate j, a.rotate j⟩ = sz.STKI n E τ ⟨σ, a⟩ := by
  induction j generalizing σ a with
  | zero => simp
  | succ j ih =>
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at h
      | cons b a =>
        have h' : σ.length = a.length := by simpa using h
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) E (sz.three_le_L n)
          (Nat.one_le_iff_ne_zero.2 (sz.W_pos n).ne') hE τ hτ s b σ a h').symm

private theorem SEforLn2_loopOf_eq {α : Type*} (J : LoopIdx α) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

private theorem SEforLn2_STLKI_eq (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    sz.STLKI n E τ ω (loopOf σ a) = Lloop sz n E τ σ a ω - STKloop sz n E τ σ a := by
  unfold STLKI STKI STKloop STLI
  rw [← loopM_eq_loopL]; rfl

private theorem SEforLn2_STmaxL_nonneg (n : ℕ) (E t : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    0 ≤ STmaxL sz n E t k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖Lloop sz n E t p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

private theorem SEforLn2_STmaxLK_nonneg (n : ℕ) (E t : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    0 ≤ STmaxLK sz n E t k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖Lloop sz n E t p.1 p.2 ω - STKloop sz n E t p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

/-- Every well-formed loop of length `m` is bounded by `max_{σ,a} |(𝓛-𝒦)^{(m)}|`. -/
private theorem SEforLn2_norm_STLKI_le (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (J : LoopIdx (Zd d (sz.L n)))
    (hJ : J.WF) : ‖sz.STLKI n E τ ω J‖ ≤ STmaxLK sz n E τ J.length ω := by
  have hJ' := SEforLn2_loopOf_eq J hJ
  conv_lhs => rw [← hJ']
  rw [SEforLn2_STLKI_eq]
  exact Finset.le_sup' (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Zd d (sz.L n)) =>
    ‖Lloop sz n E τ p.1 p.2 ω - STKloop sz n E τ p.1 p.2‖)
    (Finset.mem_univ ((fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2)),
      (fun i : Fin J.a.length => J.a[i.1])))

private theorem SEforLn2_cut_rotate {α : Type*} (σ : List Bool) (a : List α) (b : α) {j p : ℕ}
    (hσ : j ≤ σ.length) (ha : j - 1 ≤ a.length) (hj1 : 1 ≤ j) :
    (⟨(σ.take j ++ σ.drop p).rotate j, (a.take (j - 1) ++ b :: a.drop p).rotate j⟩ : LoopIdx α) =
      ⟨σ.drop p ++ σ.take j, (a.drop p ++ a.take (j - 1)) ++ [b]⟩ := by
  have h1 : (σ.take j).length = j := by simp; omega
  have h2 : (a.take (j - 1) ++ [b]).length = j := by simp; omega
  have h3 : a.take (j - 1) ++ b :: a.drop p = (a.take (j - 1) ++ [b]) ++ a.drop p := by
    simp
  refine LoopIdx.ext ?_ ?_
  · change (σ.take j ++ σ.drop p).rotate j = _
    rw [List.rotate_eq_drop_append_take (by simp; omega), List.drop_left' h1, List.take_left' h1]
  · change (a.take (j - 1) ++ b :: a.drop p).rotate j = _
    rw [List.rotate_eq_drop_append_take (by simp; omega), h3, List.drop_left' h2, List.take_left' h2]
    simp

private theorem SEforLn2_sum_norm_SB_col (n : ℕ) (b : Zd d (sz.L n)) :
    ∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖ = 1 := by
  have hsym : ∀ x y : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) y x = SB d (sz.L n) (sz.lam n) x y :=
    fun x y => congrFun (congrFun (SB_isSymm d (sz.L n) (sz.lam n)) x) y
  calc ∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖
      = ∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) b a‖ :=
        Finset.sum_congr rfl fun a _ => by rw [hsym a b]
    _ = 1 := sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) b

/-- `Σ_{a,b} F(a) |S_{ab}| G(b) ≤ (sup F) Σ_b G(b)` (column sums of `S`). -/
private theorem SEforLn2_sum_glue_left (n : ℕ) (F G : Zd d (sz.L n) → ℝ) {M : ℝ}
    (hF : ∀ a, F a ≤ M) (hG : ∀ b, 0 ≤ G b) :
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), F a * ‖SB d (sz.L n) (sz.lam n) a b‖ * G b ≤
      M * ∑ b : Zd d (sz.L n), G b := by
  calc ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), F a * ‖SB d (sz.L n) (sz.lam n) a b‖ * G b
      ≤ ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), M * (‖SB d (sz.L n) (sz.lam n) a b‖ * G b) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF a) (norm_nonneg _)) (hG b)
    _ = M * ∑ b : Zd d (sz.L n), (∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖) * G b := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by simp only [SEforLn2_sum_norm_SB_col sz n, one_mul]

/-- `Σ_{a,b} F(a) |S_{ab}| G(b) ≤ (sup G) Σ_a F(a)` (row sums of `S`). -/
private theorem SEforLn2_sum_glue_right (n : ℕ) (F G : Zd d (sz.L n) → ℝ) {M : ℝ}
    (hG : ∀ b, G b ≤ M) (hF : ∀ a, 0 ≤ F a) :
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), F a * ‖SB d (sz.L n) (sz.lam n) a b‖ * G b ≤
      M * ∑ a : Zd d (sz.L n), F a := by
  calc ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), F a * ‖SB d (sz.L n) (sz.lam n) a b‖ * G b
      ≤ ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), M * (F a * ‖SB d (sz.L n) (sz.lam n) a b‖) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [mul_comm M]
        exact mul_le_mul_of_nonneg_left (hG b) (mul_nonneg (hF a) (norm_nonneg _))
    _ = M * ∑ a : Zd d (sz.L n), F a * ∑ b : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖ := by
        simp only [← Finset.mul_sum]
    _ = _ := by simp only [sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n), mul_one]

private theorem SEforLn2_maxL_le (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    STmaxL sz n E u m ω ≤ sz.Bctl n u ^ (m - 1) * STXiL sz n E u m ω := by
  unfold STXiL
  have h0 := SEforLn2_STmaxL_nonneg sz n E u m ω
  have hp : 0 < sz.Bctl n u ^ (m - 1) := pow_pos hB _
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne']
  linarith [hp.le]

private theorem SEforLn2_maxLK_le (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    STmaxLK sz n E u m ω ≤ sz.Bctl n u ^ m * STXiLK sz n E u m ω := by
  unfold STXiLK
  have h0 := SEforLn2_STmaxLK_nonneg sz n E u m ω
  have hp : 0 < sz.Bctl n u ^ m := pow_pos hB _
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne']
  linarith [hp.le]

private theorem SEforLn2_one_le_XiL (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    1 ≤ STXiL sz n E u m ω := by
  unfold STXiL
  have := SEforLn2_STmaxL_nonneg sz n E u m ω
  have : 0 ≤ STmaxL sz n E u m ω / sz.Bctl n u ^ (m - 1) := by positivity
  linarith

private theorem SEforLn2_one_le_XiLK (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    1 ≤ STXiLK sz n E u m ω := by
  unfold STXiLK
  have := SEforLn2_STmaxLK_nonneg sz n E u m ω
  have : 0 ≤ STmaxLK sz n E u m ω / sz.Bctl n u ^ m := by positivity
  linarith

/-- `(M₁ M₂)^{1/2} ≤ B^{k-1} (Ξ₁ Ξ₂)^{1/2}` when `(n₁-1) + (n₂-1) = 2 (k-1)`. -/
private theorem SEforLn2_R_le {B M1 M2 Ξ1 Ξ2 : ℝ} {n1 n2 k : ℕ} (hB : 0 < B) (hM1 : 0 ≤ M1)
    (hM2 : 0 ≤ M2) (h1 : M1 ≤ B ^ (n1 - 1) * Ξ1) (h2 : M2 ≤ B ^ (n2 - 1) * Ξ2) (hΞ1 : 0 ≤ Ξ1)
    (hΞ2 : 0 ≤ Ξ2) (hsum : (n1 - 1) + (n2 - 1) = 2 * (k - 1)) :
    (M1 * M2) ^ (1 / 2 : ℝ) ≤ B ^ (k - 1) * (Ξ1 * Ξ2) ^ (1 / 2 : ℝ) := by
  have hp1 : 0 ≤ B ^ (n1 - 1) := by positivity
  have hp2 : 0 ≤ B ^ (n2 - 1) := by positivity
  have h3 : M1 * M2 ≤ (B ^ (k - 1)) ^ 2 * (Ξ1 * Ξ2) := by
    calc M1 * M2 ≤ (B ^ (n1 - 1) * Ξ1) * (B ^ (n2 - 1) * Ξ2) :=
          mul_le_mul h1 h2 hM2 (mul_nonneg hp1 hΞ1)
      _ = B ^ ((n1 - 1) + (n2 - 1)) * (Ξ1 * Ξ2) := by rw [pow_add]; ring
      _ = (B ^ (k - 1)) ^ 2 * (Ξ1 * Ξ2) := by rw [hsum]; ring
  calc (M1 * M2) ^ (1 / 2 : ℝ) ≤ ((B ^ (k - 1)) ^ 2 * (Ξ1 * Ξ2)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (mul_nonneg hM1 hM2) h3 (by norm_num)
    _ = B ^ (k - 1) * (Ξ1 * Ξ2) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (mul_nonneg hΞ1 hΞ2), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (by positivity)]

/-- `StochDomAt.of_subset` with a different parameter family for the source (the failure event of the
target is contained in the failure event of the source). -/
private theorem SEforLn2_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U₁ U : ℕ → Type*} {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

/-! ## 2. Scale facts and the deterministic form of a `Prec` of a deterministic family -/

/-- `N⁻¹ ≤ W^{-d} B_{u,0}` for `0 ≤ u < 1` (the zero-mode term of `(eq_B_param)`). -/
private theorem SEforLn2_Bctl_ge_inv (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hx : 0 < 1 - u := by linarith
  rw [abs_of_pos hx]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  rw [hsize, mul_inv]
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_of_le_one_right (by positivity) (by linarith))
  have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hW0 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
        mul_le_mul_of_nonneg_left h1 hW0
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hW0
        linarith

/-- The absorption of the `W^{-D}` term: `N W^{-2/𝔠} ≤ N⁻¹` from `W ≥ N^𝔠` (`(Main_DEL_COND)`). -/
private theorem SEforLn2_WD (n : ℕ) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) :
    ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(2 / 𝔠)) ≤ (((sz.size n : ℕ) : ℝ))⁻¹ := by
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h1 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (2 / 𝔠) = ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 / 𝔠) := by
    rw [← h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hb (by positivity)
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]; norm_num
  rw [h3] at h2
  rw [Real.rpow_neg hW.le]
  have h4 : (((sz.W n : ℕ) : ℝ) ^ (2 / 𝔠))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) h2
  calc ((sz.size n : ℕ) : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (2 / 𝔠))⁻¹
      ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h4 hN0.le
    _ = (((sz.size n : ℕ) : ℝ))⁻¹ := by field_simp

/-- A `Prec` of a deterministic family is an eventual deterministic bound (each failure event is `∅` or the
whole space, and `P(univ) = 1 > N^{-1}` for `N ≥ 2`). -/
private theorem SEforLn2_det_of_prec (hN : sz.SizeTendsto) {U : ℕ → Type*} (f g : ∀ n, U n → ℝ)
    (h : sz.Prec (U := U) (fun n u _ => f n u) (fun n u _ => g n u)) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ u, f n u ≤ ((sz.size n : ℕ) : ℝ) ^ τ * g n u := by
  have hsz := tendsto_size sz hN
  unfold Prec at h
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

/-- `(con_st_ind)` at an intermediate time `u ∈ [s, t]` from `(s, t)`: `B_u^{𝔠_d} ≤ (1-u)/(1-s)`, `B_u ≤ 1`
(the pair `(s,u)` itself need not satisfy `(1-u)/(1-s) < 1`: at `u = s` the ratio is `1`). -/
private theorem SEforLn2_conU (n : ℕ) {𝔠d s' t' u : ℝ} (h𝔠 : 0 < 𝔠d)
    (hcon : (sz.Bctl n t') ^ 𝔠d ≤ (1 - t') / (1 - s') ∧ (1 - t') / (1 - s') < 1) (hut : u ≤ t')
    (ht1 : t' < 1) :
    0 < 1 - s' ∧ sz.Bctl n u ≤ 1 ∧ (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s') := by
  obtain ⟨hB, hρ⟩ := hcon
  have hBpos : 0 < sz.Bctl n t' := st_Bctl_pos sz ht1
  have hu : 0 < 1 - t' := by linarith
  have hr0 : 0 < (1 - t') / (1 - s') := lt_of_lt_of_le (Real.rpow_pos_of_pos hBpos _) hB
  have hs : 0 < 1 - s' := by
    by_contra h
    push Not at h
    have := div_nonpos_of_nonneg_of_nonpos hu.le h
    linarith
  have hB1 : sz.Bctl n t' < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ (sz.Bctl n t') ^ 𝔠d := Real.one_le_rpow h h𝔠.le
    linarith
  have hmono : sz.Bctl n u ≤ sz.Bctl n t' := STBctl_mono sz n hut ht1
  refine ⟨hs, hmono.trans hB1.le, ?_⟩
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz (hut.trans_lt ht1)
  calc (sz.Bctl n u) ^ 𝔠d ≤ (sz.Bctl n t') ^ 𝔠d := Real.rpow_le_rpow hBu.le hmono h𝔠.le
    _ ≤ (1 - t') / (1 - s') := hB
    _ ≤ (1 - u) / (1 - s') := div_le_div_of_nonneg_right (by linarith) hs.le

/-- **`(eq:sumtwoloop)`, second `≺`, pointwise in `(n, u)`** (a copy of the proof of `stSumTwoLoop` at a time
`u` with `(con_st_ind)` in the form of `SEforLn2_conU`): `((1-s)/(1-u))^{C_d} B^{1/5} Σ_{a₂} 𝒯_u(|a₁-a₂|) ≤
C_∞(d) B^{1/6} η_u⁻¹`. -/
private theorem SEforLn2_sumTwo_pt (hd : 2 ≤ d) (n : ℕ) {𝔠d Cd s' u E : ℝ} (h𝔠 : 0 < 𝔠d) (hCd : 0 ≤ Cd)
    (hcc : 𝔠d * Cd ≤ 1 / 30) (hs : 0 < 1 - s') (hu1 : u < 1)
    (hB : (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s')) (hB1 : sz.Bctl n u ≤ 1) (hEn : |E| < 2)
    (hl : 0 ≤ sz.lam n) (a₁ : Zd d (sz.L n)) :
    ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd d (sz.L n),
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤
      KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (etaT E u)⁻¹ := by
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
  have himpos : 0 < (mE E).im := mE_im_pos hEn
  have himle : (mE E).im ≤ 1 := by
    have := Complex.im_le_norm (mE E)
    rwa [norm_mE hEn.le] at this
  have hηpos : 0 < etaT E u := mul_pos hu himpos
  have hηle : etaT E u ≤ 1 - u := by
    unfold etaT
    nlinarith
  have hη : (1 - u)⁻¹ ≤ (etaT E u)⁻¹ := inv_anti₀ hηpos hηle
  have hC1 : 1 ≤ KDecay_tailC d := KDecay_one_le_tailC (by omega)
  calc ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd d (sz.L n),
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)
      ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * (KDecay_tailC d / (1 - u)) :=
        mul_le_mul h4 (h5 ▸ h6) h7 (Real.rpow_nonneg hBpos.le _)
    _ = KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹ := by ring
    _ ≤ KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (etaT E u)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hη ?_
        have := Real.rpow_nonneg hBpos.le (1 / 6 : ℝ)
        positivity

/-! ## 3. The 2-loop sum of `(eq:sumtwoloop)` from the uniform 2-`G`-loop estimate -/

/-- **`(eq:sumtwoloop)`, deterministic part**: if the 2-loop estimate of `STGdecayW` holds at the labels
with the loss `δ` and the exponent `D_w`, with `N W^{-D_w} ≤ B`, then, under `(con_st_ind)` at `u` (in the form
of `SEforLn2_conU`),
`Σ_{a₂} |(𝓛-𝒦)^{(2)}_{u,σ,(a₁,a₂)}| ≤ δ (C_∞(d) + 1) B^{1/6} (W^d η_u)⁻¹`. -/
private theorem SEforLn2_sum2 (hd : 2 ≤ d) (n : ℕ) {𝔠d Cd s' u E δ Dw : ℝ} (h𝔠 : 0 < 𝔠d)
    (hCd : 0 ≤ Cd) (hcc : 𝔠d * Cd ≤ 1 / 30) (hs : 0 < 1 - s') (h0 : 0 ≤ u) (hu1 : u < 1)
    (hB : (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s')) (hB1 : sz.Bctl n u ≤ 1) (hEn : |E| < 2)
    (hl : 0 ≤ sz.lam n) (hδ : 0 ≤ δ)
    (hWD : ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ sz.Bctl n u) (ω : sz.SeqΩ)
    (hno : ∀ (σ' : Fin 2 → Bool) (a2 : Fin 2 → Zd d (sz.L n)),
      ‖Lloop sz n E u σ' a2 ω - STKloop sz n E u σ' a2‖ ≤
        δ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a2 0 - a2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a2 0 - a2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^
            (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw))) :
    ∀ (σ' : Fin 2 → Bool) (a' : Fin (2 - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STLKI n E u ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        δ * (KDecay_tailC d + 1) * (sz.Bctl n u) ^ (1 / 6 : ℝ) *
          ((((sz.W n : ℕ) : ℝ) ^ d) * etaT E u)⁻¹ := by
  intro σ' a'
  obtain ⟨c, rfl⟩ : ∃ c : Zd d (sz.L n), a' = fun _ => c :=
    ⟨a' ⟨0, by norm_num⟩, funext fun i => congrArg a' (Fin.ext (by have := i.2; simp only at this ⊢; omega))⟩
  have hBpos : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hη : 0 < etaT E u := etaT_pos hEn hu1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hηle : etaT E u ≤ 1 := by
    have himle : (mE E).im ≤ 1 := by
      have := Complex.im_le_norm (mE E)
      rwa [norm_mE hEn.le] at this
    have himpos : 0 < (mE E).im := mE_im_pos hEn
    unfold etaT
    nlinarith
  have hη1 : 1 ≤ (etaT E u)⁻¹ := one_le_inv₀ hη |>.2 hηle
  -- the pointwise bound
  have hpt : ∀ x : Zd d (sz.L n),
      ‖sz.STLKI n E u ω ⟨List.ofFn σ', List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x]⟩‖ ≤
        δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
    intro x
    have hlist : (List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x] : List (Zd d (sz.L n))) =
        List.ofFn (![c, x] : Fin 2 → Zd d (sz.L n)) := by
      simp [List.ofFn_succ]
    have h1 : sz.STLKI n E u ω ⟨List.ofFn σ', List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x]⟩ =
        Lloop sz n E u σ' ![c, x] ω - STKloop sz n E u σ' ![c, x] := by
      rw [hlist, ← SEforLn2_STLKI_eq]; rfl
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
  calc ∑ x : Zd d (sz.L n), ‖sz.STLKI n E u ω ⟨List.ofFn σ', List.ofFn (fun _ : Fin (2 - 1) => c) ++ [x]⟩‖
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
    _ ≤ δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (etaT E u)⁻¹) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (etaT E u)⁻¹) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hδ
        · exact mul_le_mul_of_nonneg_left
            (SEforLn2_sumTwo_pt sz hd n h𝔠 hCd hcc hs hu1 hB hB1 hEn hl c) (by positivity)
        · have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
            simp [Sizes.size, mul_pow]
          have h1 : (((sz.L n : ℕ) : ℝ) ^ d) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) =
              (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
            rw [hsize]; field_simp
          have h2 : sz.Bctl n u ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) := by
            have := Real.rpow_le_rpow_of_exponent_ge hBpos hB1 (by norm_num : (1 / 6 : ℝ) ≤ 1)
            simpa using this
          have h3 : (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * (etaT E u)⁻¹ :=
            le_mul_of_one_le_right (Real.rpow_nonneg hBpos.le _) hη1
          rw [h1, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hWD.trans (h2.trans h3)) (by positivity)
    _ = δ * (KDecay_tailC d + 1) * (sz.Bctl n u) ^ (1 / 6 : ℝ) *
          ((((sz.W n : ℕ) : ℝ) ^ d) * etaT E u)⁻¹ := by
        rw [mul_inv]; ring

/-! ## 4. The two pieces of a cut: sums over the glued label -/

/-- The glued label of a loop of length `m` is summed with the bound `Q`: for every charge vector and every
list of the other `m - 1` labels, `Σ_x |(𝓛-𝒦)^{(m)}_{σ,(a', x)}| ≤ Q`. -/
private def SEforLn2_SumOK (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (m : ℕ) (Q : ℝ) : Prop :=
  ∀ (σ' : Fin m → Bool) (a' : Fin (m - 1) → Zd d (sz.L n)),
    ∑ x : Zd d (sz.L n), ‖sz.STLKI n E τ ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Q

/-- The piece `cutGlueR` has its glued label last. -/
private theorem SEforLn2_sumR (n : ℕ) {E τ : ℝ} {ω : sz.SeqΩ} {r : ℕ} {Q : ℝ}
    (hQ : SEforLn2_SumOK sz n E τ ω r Q) {m : ℕ} (σ : List Bool) (a : List (Zd d (sz.L n)))
    (hσ : σ.length = m) (ha : a.length = m) {j l' : ℕ} (hj : 1 ≤ j) (hjl : j < l') (hl' : l' ≤ m)
    (hr : l' - j + 1 = r) :
    ∑ y : Zd d (sz.L n), ‖sz.STLKI n E τ ω ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤ Q := by
  obtain ⟨σ₁, hσ₁⟩ := SEforLn2_exists_ofFn ((σ.drop (j - 1)).take (l' - j + 1)) (m := r)
    (by simp [hσ]; omega)
  obtain ⟨a₁, ha₁⟩ := SEforLn2_exists_ofFn ((a.drop (j - 1)).take (l' - j)) (m := r - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hQ σ₁ a₁)
  simp only [LoopIdx.cutGlueR, hσ₁, ha₁]

/-- The piece `cutGlueL`: its glued label is rotated to the last position (trace cyclicity for `𝓛`,
`KLK_rotate` for `𝒦`). -/
private theorem SEforLn2_sumL (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (hτ : τ ∈ Set.Ico (0 : ℝ) 1)
    {ω : sz.SeqΩ} {ℓ : ℕ} {Q : ℝ} (hQ : SEforLn2_SumOK sz n E τ ω ℓ Q) {m : ℕ} (σ : List Bool)
    (a : List (Zd d (sz.L n))) (hσ : σ.length = m) (ha : a.length = m) {j l' : ℕ} (hj : 1 ≤ j)
    (hjl : j < l') (hl' : l' ≤ m) (hl : j + m - l' + 1 = ℓ) :
    ∑ x : Zd d (sz.L n), ‖sz.STLKI n E τ ω ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ ≤ Q := by
  obtain ⟨σ₂, hσ₂⟩ := SEforLn2_exists_ofFn (σ.drop (l' - 1) ++ σ.take j) (m := ℓ)
    (by simp [hσ]; omega)
  obtain ⟨a₂, ha₂⟩ := SEforLn2_exists_ofFn (a.drop (l' - 1) ++ a.take (j - 1)) (m := ℓ - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hQ σ₂ a₂)
  have hrot := SEforLn2_cut_rotate σ a x (j := j) (p := l' - 1) (by omega) (by omega) hj
  have hlen : (σ.take j ++ σ.drop (l' - 1)).length = (a.take (j - 1) ++ x :: a.drop (l' - 1)).length := by
    simp [hσ, ha]; omega
  have hL := SEforLn2_STLI_rotate sz n E τ ω j _ _ hlen
  have hK := SEforLn2_STKI_rotate sz n hE hτ j _ _ hlen
  rw [hrot] at hL hK
  change ‖sz.STLKI n E τ ω ⟨σ.take j ++ σ.drop (l' - 1), a.take (j - 1) ++ x :: a.drop (l' - 1)⟩‖ = _
  unfold STLKI
  rw [← hL, ← hK, hσ₂, ha₂]

/-- The two pieces of a cut have lengths `j + k - l' + 1` and `l' - j + 1`; a bound of the max of one by the
`Σ` of the other. -/
private theorem SEforLn2_pair_left (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) {j l' : ℕ} (hj : 1 ≤ j) (hjl : j < l') (hl' : l' ≤ k) {Q : ℝ}
    (hQ : ∑ y : Zd d (sz.L n), ‖sz.STLKI n E τ ω
        ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤ Q) :
    ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖sz.STLKI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ *
        ‖SB d (sz.L n) (sz.lam n) x y‖ *
        ‖sz.STLKI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤
      STmaxLK sz n E τ (j + k - l' + 1) ω * Q := by
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hlen : I.length = k := by simp [hI, LoopIdx.length]
  have hlenL : ∀ x, (I.cutGlueL j l' x).length = j + k - l' + 1 := fun x => by
    rw [LoopIdx.length_cutGlueL I x hj hjl (hlen ▸ hl'), hlen]
  have hwfL : ∀ x, (I.cutGlueL j l' x).WF := fun x => LoopIdx.wf_cutGlueL I x hIwf hj hjl (hlen ▸ hl')
  have hM0 := SEforLn2_STmaxLK_nonneg sz n E τ (j + k - l' + 1) ω
  refine (SEforLn2_sum_glue_left sz n (fun x => ‖sz.STLKI n E τ ω (I.cutGlueL j l' x)‖)
    (fun y => ‖sz.STLKI n E τ ω (I.cutGlueR j l' y)‖) (M := STmaxLK sz n E τ (j + k - l' + 1) ω)
    (fun x => ?_) (fun y => norm_nonneg _)).trans ?_
  · refine (SEforLn2_norm_STLKI_le sz n E τ ω _ (hwfL x)).trans (le_of_eq ?_)
    rw [hlenL x]
  · exact mul_le_mul_of_nonneg_left hQ hM0

private theorem SEforLn2_pair_right (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) {j l' : ℕ} (hj : 1 ≤ j) (hjl : j < l') (hl' : l' ≤ k) {Q : ℝ}
    (hQ : ∑ x : Zd d (sz.L n), ‖sz.STLKI n E τ ω
        ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ ≤ Q) :
    ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖sz.STLKI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ *
        ‖SB d (sz.L n) (sz.lam n) x y‖ *
        ‖sz.STLKI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤
      STmaxLK sz n E τ (l' - j + 1) ω * Q := by
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hlen : I.length = k := by simp [hI, LoopIdx.length]
  have hlenR : ∀ y, (I.cutGlueR j l' y).length = l' - j + 1 := fun y =>
    LoopIdx.length_cutGlueR I y hj hjl (hlen ▸ hl')
  have hwfR : ∀ y, (I.cutGlueR j l' y).WF := fun y => LoopIdx.wf_cutGlueR I y hIwf hj hjl (hlen ▸ hl')
  have hM0 := SEforLn2_STmaxLK_nonneg sz n E τ (l' - j + 1) ω
  refine (SEforLn2_sum_glue_right sz n (fun x => ‖sz.STLKI n E τ ω (I.cutGlueL j l' x)‖)
    (fun y => ‖sz.STLKI n E τ ω (I.cutGlueR j l' y)‖) (M := STmaxLK sz n E τ (l' - j + 1) ω)
    (fun y => ?_) (fun x => norm_nonneg _)).trans ?_
  · refine (SEforLn2_norm_STLKI_le sz n E τ ω _ (hwfR y)).trans (le_of_eq ?_)
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
private theorem SEforLn2_sumContract (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {m : ℕ} (hm : 2 ≤ m) (σ' : Fin m → Bool) (a' : Fin (m - 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), ‖sz.STLI n E τ ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
        (STmaxL sz n E τ (STn12 m).1 ω * STmaxL sz n E τ (STn12 m).2 ω) ^ (1 / 2 : ℝ) := by
  have hc := (stContract_holds d sz n E τ hE h0 h1 ω).1 m (m / 2) (by omega) (by omega) σ' a'
  obtain ⟨e1, e2⟩ := SEforLn2_n12 m hm
  rw [e1, e2] at hc
  exact hc

/-- The `𝓛 - 𝒦` sum of a loop of length `m ≥ 2` with the glued label last: contraction plus the Ward bound
`Kw` of the `𝒦`-loop. -/
private theorem SEforLn2_sumLK (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {m : ℕ} (hm : 2 ≤ m) {Kw : ℝ}
    (hKw : ∀ (σ' : Fin m → Bool) (a' : Fin (m - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw) :
    SEforLn2_SumOK sz n E τ ω m
      ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
        (STmaxL sz n E τ (STn12 m).1 ω * STmaxL sz n E τ (STn12 m).2 ω) ^ (1 / 2 : ℝ) + Kw) := by
  intro σ' a'
  refine le_trans (Finset.sum_le_sum fun x _ => norm_sub_le (sz.STLI n E τ ω ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩)
    (sz.STKI n E τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩)) ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add (SEforLn2_sumContract sz n hE h0 h1 ω hm σ' a') (hKw σ' a')

/-- Exponent count for a pair with the longer piece `n'` summed (`3_5:1079-1086`):
`W^d · max|(𝓛-𝒦)^{(m')}| · ((W^dη)⁻¹ (R + δ B^{n'-2})) ≤ 2 δ (B^k/η) Ξ^{𝓛-𝒦}_{m'} Y`, `m' + n' - 2 = k`,
`R ≤ B^{n'-2} Y`, `Y ≥ 1`, `δ ≥ 1`. -/
private theorem SEforLn2_arith_long {Wd B η δ MK Ξ Y RR : ℝ} {k m' n' : ℕ} (hWd : 0 < Wd) (hB : 0 < B)
    (hη : 0 < η) (hδ : 1 ≤ δ) (hMK0 : 0 ≤ MK) (hMK : MK ≤ B ^ m' * Ξ) (hΞ : 0 ≤ Ξ) (hY : 1 ≤ Y)
    (hRR0 : 0 ≤ RR) (hRR : RR ≤ B ^ (n' - 2) * Y) (hk : m' + (n' - 2) = k) :
    Wd * (MK * ((Wd * η)⁻¹ * RR + δ * ((Wd * η)⁻¹ * B ^ (n' - 2)))) ≤
      2 * δ * (B ^ k / η * (Ξ * Y)) := by
  have hBk : B ^ k = B ^ m' * B ^ (n' - 2) := by rw [← pow_add, hk]
  have hp : 0 < B ^ (n' - 2) := pow_pos hB _
  have hη' : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hsum : RR + δ * B ^ (n' - 2) ≤ B ^ (n' - 2) * (2 * δ * Y) := by
    have h1 : δ * B ^ (n' - 2) ≤ B ^ (n' - 2) * (δ * Y) := by
      have : δ ≤ δ * Y := le_mul_of_one_le_right (by linarith) hY
      nlinarith [hp]
    have h2 : B ^ (n' - 2) * Y ≤ B ^ (n' - 2) * (δ * Y) := by
      have : Y ≤ δ * Y := le_mul_of_one_le_left (by linarith) hδ
      exact mul_le_mul_of_nonneg_left this hp.le
    nlinarith [hp]
  have hlhs : Wd * (MK * ((Wd * η)⁻¹ * RR + δ * ((Wd * η)⁻¹ * B ^ (n' - 2)))) =
      η⁻¹ * (MK * (RR + δ * B ^ (n' - 2))) := by
    field_simp
  rw [hlhs]
  calc η⁻¹ * (MK * (RR + δ * B ^ (n' - 2)))
      ≤ η⁻¹ * ((B ^ m' * Ξ) * (B ^ (n' - 2) * (2 * δ * Y))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hMK hsum (by positivity) (by positivity)) hη'
    _ = 2 * δ * (B ^ k / η * (Ξ * Y)) := by rw [hBk]; field_simp

/-- Exponent count for a pair with a 2-loop piece summed (`(eq:sumtwoloop)`):
`W^d · max|(𝓛-𝒦)^{(k)}| · (δ C_s B^{1/6} (W^dη)⁻¹) ≤ δ C_s (B^k/η) (B^{1/6} Ξ^{𝓛-𝒦}_k)`. -/
private theorem SEforLn2_arith_two {Wd B η δ Cs MK Ξ B6 : ℝ} {k : ℕ} (hWd : 0 < Wd) (hη : 0 < η)
    (hδ : 0 ≤ δ) (hCs : 0 ≤ Cs) (hB6 : 0 ≤ B6) (hMK : MK ≤ B ^ k * Ξ) (hMK0 : 0 ≤ MK) :
    Wd * (MK * (δ * Cs * B6 * (Wd * η)⁻¹)) ≤ δ * Cs * (B ^ k / η * (B6 * Ξ)) := by
  have hη' : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hlhs : Wd * (MK * (δ * Cs * B6 * (Wd * η)⁻¹)) = (δ * Cs * B6) * η⁻¹ * MK := by
    field_simp
  rw [hlhs]
  calc (δ * Cs * B6) * η⁻¹ * MK ≤ (δ * Cs * B6) * η⁻¹ * (B ^ k * Ξ) :=
        mul_le_mul_of_nonneg_left hMK (by positivity)
    _ = δ * Cs * (B ^ k / η * (B6 * Ξ)) := by field_simp

/-! ## 6. Part (3): the deterministic core -/

/-- `Σ_{1 ≤ j < l' ≤ m} f(j, l') ≤ m² T`. -/
private theorem SEforLn2_sum_pairs (m : ℕ) (f : ℕ → ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ k ∈ Finset.Icc 1 m, ∀ l ∈ Finset.Ioc k m, f k l ≤ T) :
    ∑ k ∈ Finset.Icc 1 m, ∑ l ∈ Finset.Ioc k m, f k l ≤ (m : ℝ) ^ 2 * T := by
  calc ∑ k ∈ Finset.Icc 1 m, ∑ l ∈ Finset.Ioc k m, f k l
      ≤ ∑ k ∈ Finset.Icc 1 m, ∑ l ∈ Finset.Ioc k m, T :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hf k hk l hl
    _ ≤ ∑ k ∈ Finset.Icc 1 m, (m : ℝ) * T := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le m k
    _ = (m : ℝ) ^ 2 * T := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

/-- A pair with the longer piece `n' ∈ [⌈k/2⌉+1, k-1]` summed: the exponent count of `(eq:sumtwoloop2)`,
first term (`3_5:1079-1086`). -/
private theorem SEforLn2_long (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h1 : τ < 1) (ω : sz.SeqΩ) {k n' : ℕ}
    (hn' : n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1)) {δ : ℝ} (hδ : 1 ≤ δ) :
    ((sz.W n : ℕ) : ℝ) ^ d * (STmaxLK sz n E τ (k + 2 - n') ω *
      ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
        (STmaxL sz n E τ (STn12 n').1 ω * STmaxL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
        δ * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * (sz.Bctl n τ) ^ (n' - 2)))) ≤
      2 * δ * ((sz.Bctl n τ) ^ k / etaT E τ *
        (STXiLK sz n E τ (k + 2 - n') ω *
          (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ))) := by
  rw [Finset.mem_Icc] at hn'
  have hn3 : 3 ≤ n' := by omega
  have hB : 0 < sz.Bctl n τ := st_Bctl_pos sz h1
  have hη : 0 < etaT E τ := etaT_pos hE h1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hX1 := SEforLn2_one_le_XiL sz n E τ ω (STn12 n').1 hB
  have hX2 := SEforLn2_one_le_XiL sz n E τ ω (STn12 n').2 hB
  have hY : 1 ≤ (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hX1 hX2) (by norm_num)
  have hRR := SEforLn2_R_le (k := n' - 1) hB (SEforLn2_STmaxL_nonneg sz n E τ _ ω)
    (SEforLn2_STmaxL_nonneg sz n E τ _ ω) (SEforLn2_maxL_le sz n E τ ω _ hB)
    (SEforLn2_maxL_le sz n E τ ω _ hB) (by linarith) (by linarith) (SEforLn2_n12_sum n' hn3)
  rw [show n' - 1 - 1 = n' - 2 by omega] at hRR
  exact SEforLn2_arith_long hWd hB hη hδ (SEforLn2_STmaxLK_nonneg sz n E τ _ ω)
    (SEforLn2_maxLK_le sz n E τ ω _ hB) (by linarith [SEforLn2_one_le_XiLK sz n E τ ω (k + 2 - n') hB]) hY
    (Real.rpow_nonneg (mul_nonneg (SEforLn2_STmaxL_nonneg sz n E τ _ ω)
      (SEforLn2_STmaxL_nonneg sz n E τ _ ω)) _) hRR (by omega)

/-- **The deterministic core of part (3)** (`3_5:1063-1086`): for every sample, a time `u = τ ∈ [0,1)`, `|E| < 2`,
if the 2-loop sum is bounded (`hS2`: `Σ_{a₂} |(𝓛-𝒦)^{(2)}| ≤ δ C_s B^{1/6} (W^d η)⁻¹`, `(eq:sumtwoloop)`) and the `𝒦`-loop
Ward bound holds with the loss `δ` (`hKw`), then `‖ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}‖ ≤ k² (C_s+2) δ B^k η⁻¹ (Σ_{n'} ... + B^{1/6} Ξ̂^{𝓛-𝒦}_k)`. -/
private theorem SEforLn2_det3 (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1) (ω : sz.SeqΩ)
    {k : ℕ} (hk : 2 ≤ k) {δ Cs : ℝ} (hδ : 1 ≤ δ) (hCs : 0 ≤ Cs)
    (hS2 : SEforLn2_SumOK sz n E τ ω 2
      (δ * Cs * (sz.Bctl n τ) ^ (1 / 6 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d) * etaT E τ)⁻¹))
    (hKw : ∀ l : ℕ, 3 ≤ l → l + 1 ≤ k → ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        δ * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * (sz.Bctl n τ) ^ (l - 2)))
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖sz.STelklk n E τ ω ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
      (k : ℝ) ^ 2 * ((Cs + 2) * δ) *
        ((sz.Bctl n τ) ^ k / etaT E τ *
          (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
              STXiLK sz n E τ (k + 2 - n') ω *
                (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
            (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLK sz n E τ k ω)) := by
  have hτ : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨h0, h1⟩
  have hB : 0 < sz.Bctl n τ := st_Bctl_pos sz h1
  have hη : 0 < etaT E τ := etaT_pos hE h1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hB6 : 0 ≤ (sz.Bctl n τ) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hB.le _
  have hXk := SEforLn2_one_le_XiLK sz n E τ ω k hB
  set T : ℝ := ∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
    STXiLK sz n E τ (k + 2 - n') ω *
      (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) with hT
  have hA0 : ∀ n' : ℕ, 0 ≤ STXiLK sz n E τ (k + 2 - n') ω *
      (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) := fun n' =>
    mul_nonneg (zero_le_one.trans (SEforLn2_one_le_XiLK sz n E τ ω _ hB))
      (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (SEforLn2_one_le_XiL sz n E τ ω _ hB))
        (zero_le_one.trans (SEforLn2_one_le_XiL sz n E τ ω _ hB))) _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n' _ => hA0 n'
  set Zb : ℝ := (sz.Bctl n τ) ^ k / etaT E τ * (T + (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLK sz n E τ k ω) with hZ
  have hBkη : 0 ≤ (sz.Bctl n τ) ^ k / etaT E τ := by positivity
  have hZ0 : 0 ≤ Zb := mul_nonneg hBkη (add_nonneg hT0 (mul_nonneg hB6 (by linarith)))
  have hCδ : 0 ≤ (Cs + 2) * δ := mul_nonneg (by linarith) (by linarith)
  set Q2 : ℝ := δ * Cs * (sz.Bctl n τ) ^ (1 / 6 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d) * etaT E τ)⁻¹ with hQ2
  -- the pieces with a 2-loop summed
  have htwo : ∀ MK : ℝ, 0 ≤ MK → MK ≤ (sz.Bctl n τ) ^ k * STXiLK sz n E τ k ω →
      ((sz.W n : ℕ) : ℝ) ^ d * (MK * (δ * Cs * (sz.Bctl n τ) ^ (1 / 6 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d) * etaT E τ)⁻¹)) ≤ (Cs + 2) * δ * Zb := by
    intro MK hMK0 hMK
    refine (SEforLn2_arith_two hWd hη (by linarith) hCs hB6 hMK hMK0).trans ?_
    have h1 : (sz.Bctl n τ) ^ k / etaT E τ * ((sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLK sz n E τ k ω) ≤ Zb := by
      rw [hZ]; exact mul_le_mul_of_nonneg_left (by linarith) hBkη
    have h2 : 0 ≤ (sz.Bctl n τ) ^ k / etaT E τ * ((sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLK sz n E τ k ω) :=
      mul_nonneg hBkη (mul_nonneg hB6 (by linarith))
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ) h2]
  -- the sum bound of a longer piece
  set Qm : ℕ → ℝ := fun m => (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
      (STmaxL sz n E τ (STn12 m).1 ω * STmaxL sz n E τ (STn12 m).2 ω) ^ (1 / 2 : ℝ) +
      δ * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * (sz.Bctl n τ) ^ (m - 2)) with hQm
  have hQmOK : ∀ m : ℕ, 3 ≤ m → m + 1 ≤ k → SEforLn2_SumOK sz n E τ ω m (Qm m) := fun m hm3 hmk =>
    SEforLn2_sumLK sz n hE h0 h1 ω (by omega) (Kw := δ * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
      (sz.Bctl n τ) ^ (m - 2))) (hKw m hm3 hmk)
  have hlong : ∀ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      ((sz.W n : ℕ) : ℝ) ^ d * (STmaxLK sz n E τ (k + 2 - n') ω * Qm n') ≤ (Cs + 2) * δ * Zb := by
    intro n' hn'
    refine (SEforLn2_long sz n hE h1 ω hn' hδ).trans ?_
    have hsingle : STXiLK sz n E τ (k + 2 - n') ω *
        (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) ≤ T :=
      Finset.single_le_sum (f := fun n' => STXiLK sz n E τ (k + 2 - n') ω *
        (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ))
        (fun i _ => hA0 i) hn'
    have h1' : (sz.Bctl n τ) ^ k / etaT E τ * (STXiLK sz n E τ (k + 2 - n') ω *
        (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ)) ≤ Zb := by
      rw [hZ]
      refine mul_le_mul_of_nonneg_left ?_ hBkη
      have : 0 ≤ (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLK sz n E τ k ω := mul_nonneg hB6 (by linarith)
      linarith
    have h2 : 0 ≤ (sz.Bctl n τ) ^ k / etaT E τ * (STXiLK sz n E τ (k + 2 - n') ω *
        (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ)) :=
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
        ‖sz.STLKI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL j l' x)‖ *
          ‖SB d (sz.L n) (sz.lam n) x y‖ *
          ‖sz.STLKI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR j l' y)‖ ≤
        (Cs + 2) * δ * Zb * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    intro j hj l' hl'
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ioc] at hl'
    by_cases hr2 : l' - j + 1 = 2
    · -- the `cutGlueR` piece is a 2-loop, the other has length `k`
      have hQ' : SEforLn2_SumOK sz n E τ ω (l' - j + 1) Q2 := by rw [hr2]; exact hS2
      have hQR := SEforLn2_sumR sz n hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
      refine (SEforLn2_pair_left sz n E τ ω σ a hj.1 hl'.1 hl'.2 hQR).trans ?_
      rw [show j + k - l' + 1 = k by omega]
      exact hdiv _ _ (htwo _ (SEforLn2_STmaxLK_nonneg sz n E τ k ω) (SEforLn2_maxLK_le sz n E τ ω k hB))
    · by_cases hl2 : j + k - l' + 1 = 2
      · -- the `cutGlueL` piece is a 2-loop, the other has length `k`
        have hQ' : SEforLn2_SumOK sz n E τ ω (j + k - l' + 1) Q2 := by rw [hl2]; exact hS2
        have hQL := SEforLn2_sumL sz n hE hτ hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
        refine (SEforLn2_pair_right sz n E τ ω σ a hj.1 hl'.1 hl'.2 hQL).trans ?_
        rw [show l' - j + 1 = k by omega]
        exact hdiv _ _ (htwo _ (SEforLn2_STmaxLK_nonneg sz n E τ k ω) (SEforLn2_maxLK_le sz n E τ ω k hB))
      · by_cases hlr : l' - j + 1 ≤ j + k - l' + 1
        · -- the longer piece is `cutGlueL`, of length `n' = j + k - l' + 1`
          have hn' : j + k - l' + 1 ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1) := by
            rw [Finset.mem_Icc]; omega
          have hQ' := hQmOK (j + k - l' + 1) (by omega) (by omega)
          have hQL := SEforLn2_sumL sz n hE hτ hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
          refine (SEforLn2_pair_right sz n E τ ω σ a hj.1 hl'.1 hl'.2 hQL).trans ?_
          rw [show l' - j + 1 = k + 2 - (j + k - l' + 1) by omega]
          exact hdiv _ _ (hlong _ hn')
        · -- the longer piece is `cutGlueR`, of length `n' = l' - j + 1`
          have hn' : l' - j + 1 ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1) := by
            rw [Finset.mem_Icc]; omega
          have hQ' := hQmOK (l' - j + 1) (by omega) (by omega)
          have hQR := SEforLn2_sumR sz n hQ' (List.ofFn σ) (List.ofFn a) hσl hal hj.1 hl'.1 hl'.2 rfl
          refine (SEforLn2_pair_left sz n E τ ω σ a hj.1 hl'.1 hl'.2 hQR).trans ?_
          rw [show j + k - l' + 1 = k + 2 - (l' - j + 1) by omega]
          exact hdiv _ _ (hlong _ hn')
  -- the sum over the cut edges
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hlen : I.length = k := by simp [hI, LoopIdx.length]
  unfold STelklk
  rw [norm_mul, hlen, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  have hsum : ‖∑ j ∈ Finset.Icc 1 k, ∑ l' ∈ Finset.Ioc j k, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      sz.STLKI n E τ ω (I.cutGlueL j l' x) * SB d (sz.L n) (sz.lam n) x y *
        sz.STLKI n E τ ω (I.cutGlueR j l' y)‖ ≤
      (k : ℝ) ^ 2 * ((Cs + 2) * δ * Zb * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _) ?_
    refine SEforLn2_sum_pairs k (fun j l' => ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      sz.STLKI n E τ ω (I.cutGlueL j l' x) * SB d (sz.L n) (sz.lam n) x y *
        sz.STLKI n E τ ω (I.cutGlueR j l' y)‖)
      (mul_nonneg (mul_nonneg hCδ hZ0) (inv_nonneg.2 hWd.le)) fun j hj l' hl' => ?_
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => le_of_eq ?_)) (hpair j hj l' hl'))
    rw [norm_mul, norm_mul]
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ j ∈ Finset.Icc 1 k, ∑ l' ∈ Finset.Ioc j k, ∑ x : Zd d (sz.L n),
        ∑ y : Zd d (sz.L n), sz.STLKI n E τ ω (I.cutGlueL j l' x) * SB d (sz.L n) (sz.lam n) x y *
          sz.STLKI n E τ ω (I.cutGlueR j l' y)‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) ^ 2 * ((Cs + 2) * δ * Zb * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum hWd.le
    _ = (k : ℝ) ^ 2 * ((Cs + 2) * δ) * Zb := by field_simp

/-! ## 7. Part (3): the `≺` -/

private theorem SEforLn2_Z_nonneg (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h1 : τ < 1) (ω : sz.SeqΩ) (k : ℕ) :
    0 ≤ (sz.Bctl n τ) ^ k / etaT E τ *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLK sz n E τ (k + 2 - n') ω *
              (STXiL sz n E τ (STn12 n').1 ω * STXiL sz n E τ (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n τ) ^ (1 / 6 : ℝ) * STXiLK sz n E τ k ω) := by
  have hB : 0 < sz.Bctl n τ := st_Bctl_pos sz h1
  have hη : 0 < etaT E τ := etaT_pos hE h1
  refine mul_nonneg (div_nonneg (pow_nonneg hB.le _) hη.le) (add_nonneg (Finset.sum_nonneg fun n' _ => ?_)
    (mul_nonneg (Real.rpow_nonneg hB.le _) (zero_le_one.trans (SEforLn2_one_le_XiLK sz n E τ ω _ hB))))
  exact mul_nonneg (zero_le_one.trans (SEforLn2_one_le_XiLK sz n E τ ω _ hB))
    (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (SEforLn2_one_le_XiL sz n E τ ω _ hB))
      (zero_le_one.trans (SEforLn2_one_le_XiL sz n E τ ω _ hB))) _)

private theorem SEforLn2_final {ξ c δ Z Nτ : ℝ} (hdet : ξ ≤ c * Z) (hc : c ≤ δ * δ) (hZ : 0 ≤ Z)
    (h : δ * δ = Nτ) : ξ ≤ Nτ * Z := by
  rw [← h]
  exact hdet.trans (mul_le_mul_of_nonneg_right hc hZ)

/-- The core of part (3), for an abstract energy sequence `E` with `|E n| < 2` and times `0 ≤ s ≤ t < 1`, from
the uniform 2-`G`-loop estimate `STGdecayW` (the only `ω`-dependent input), the uniform `𝒦`-loop Ward bound
`(wardineq_K)` (a `Prec` of a deterministic family), `(con_st_ind)` with `𝔠_d C_d ≤ 1/30`, and `W ≥ N^𝔠`. -/
private theorem SEforLn2_part3_core {E s t : ℕ → ℝ} {Cd 𝔠d 𝔠 : ℝ} (hd : 2 ≤ d) (hN : sz.SizeTendsto)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) (hCd : 0 ≤ Cd)
    (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30) (hcon : sz.STConStInd 𝔠d s t) (hG : STGdecayW sz E s t Cd)
    (hKw : ∀ l : ℕ, 2 ≤ l →
      Prec sz (U := fun n => TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖STKI sz n (E n) (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ *
          (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)))
    (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklk sz n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLK sz n (E n) (p.1 : ℝ) (k + 2 - n') ω *
              (STXiL sz n (E n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz n (E n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz n (E n) (p.1 : ℝ) k ω)) := by
  have hsize := tendsto_size sz hN
  have hG' := hG (2 / 𝔠) (by positivity)
  unfold Prec at hG' ⊢
  refine SEforLn2_of_subset hG' (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  have hKwdet : ∀ᶠ n in atTop, ∀ l ∈ Finset.Icc 2 k, ∀ (u : TimeIcc s t n) (σ' : Fin l → Bool)
      (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STKI sz n (E n) (u : ℝ) ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (u : ℝ))⁻¹ * (sz.Bctl n (u : ℝ)) ^ (l - 2)) := by
    rw [Filter.eventually_all_finset]
    intro l hl
    have := SEforLn2_det_of_prec sz hN
      (fun n (p : TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n))) =>
        ∑ x : Zd d (sz.L n), ‖STKI sz n (E n) (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
      (fun n p => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2))
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
  have hη : 0 < etaT (E n) (p.1 : ℝ) := etaT_pos (hE n) hu1
  obtain ⟨hs', hB1, hBc⟩ := SEforLn2_conU sz n h𝔠d hcon_n p.1.2.2 (ht1 n)
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) (half_pos hτ).le
  have hWD := (SEforLn2_WD sz n h𝔠 hband_n).trans (SEforLn2_Bctl_ge_inv sz n hu0 hu1)
  have hS2 := SEforLn2_sum2 sz hd n h𝔠d hCd hcc hs' hu0 hu1 hBc hB1 (hE n) hlam_n (by linarith) hWD ω
    (fun σ' a2 => hno (p.1, σ', a2))
  have hKw3 : ∀ l : ℕ, 3 ≤ l → l + 1 ≤ k → ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n (E n) (p.1 : ℝ) ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)) :=
    fun l hl3 hlk σ' a' => hKw_n l (Finset.mem_Icc.2 ⟨by omega, by omega⟩) p.1 σ' a'
  have hdet := SEforLn2_det3 sz n (hE n) hu0 hu1 ω hk hN1
    (Cs := KDecay_tailC d + 1) (by linarith [KDecay_one_le_tailC (d := d) (by omega)]) hS2 hKw3 p.2.1 p.2.2
  have hZ0 := SEforLn2_Z_nonneg sz n (hE n) hu1 ω k
  have hδ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
  have hfin : ‖STelklk sz n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLK sz n (E n) (p.1 : ℝ) (k + 2 - n') ω *
              (STXiL sz n (E n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz n (E n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz n (E n) (p.1 : ℝ) k ω)) := by
    refine SEforLn2_final hdet ?_ hZ0 (UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ)
    nlinarith [hCN, hδ0]
  exact absurd hp (not_lt.2 hfin)

/-! ## 8. Part (3): the public statement -/

private theorem SEforLn2_flow_im {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1

/-- **Part (3) of `lem:SEforLn`, `(eq:L-KsimL-K)`** (`3_5:1035-1041`, proof `3_5:1063-1086`): along the flow
`STFlow` with `0 ≤ s < t ≤ lemT z`, from the uniform 2-`G`-loop estimate `STGdecayW` (`(Eq:Gdecay_w)`, the third
input of `STStep2Concl`), `(con_st_ind)` with `𝔠_d C_d ≤ 1/30` (`(eq:sumtwoloop)`), the uniform `𝒦`-loop Ward bound
(`stKward_timeIcc`) and the contraction inequality (`stContract_holds`): for every `k ≥ 2`,
`max_{σ,a} |ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^k η_u⁻¹ (Σ_{n'=⌈k/2⌉+1}^{k-1} Ξ̂^{𝓛-𝒦}_{u,k+2-n'}
(Ξ̂^{𝓛}_{u,n'₁} Ξ̂^{𝓛}_{u,n'₂})^{1/2} + (W^{-d}B_{u,0})^{1/6} Ξ̂^{𝓛-𝒦}_{u,k})`, `(n'₁, n'₂) = STn12 n'`, uniformly in
`u ∈ [s_n, t_n]`.  The conclusion is the third conjunct of `STSEforLnConcl sz (STflowE z) s t` at `k`. -/
theorem stSEforLn_part3 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 Cd 𝔠d : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hCd : 0 < Cd) (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30) (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hcon : STConStInd sz 𝔠d s t) (hG : STGdecayW sz (STflowE z) s t Cd) (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklk sz n (STflowE z n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (STflowE z n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLK sz n (STflowE z n) (p.1 : ℝ) (k + 2 - n') ω *
              (STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz n (STflowE z n) (p.1 : ℝ) k ω)) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hflow.1
  have him := SEforLn2_flow_im sz hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hE' : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => (abs_lemE_le (him n)).trans (hflow.2 n).1
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hn.1, hn.2⟩
  exact SEforLn2_part3_core sz (by omega) hN (fun n => abs_lemE_lt_two (him n)) hs ht1
    (hlam.mono fun n hn => hn.1.le) h𝔠 hB hCd.le h𝔠d hcc hcon hG
    (fun l hl => stKward_timeIcc sz hd hκ (inv_pos.2 h𝔡) hN (Eventually.of_forall hE') hlam hs
      (fun n => (hst n).le) ht1 l hl) k hk

/-! ## 9. Part (4): `(eq:MG_nloop)` -/

private theorem SEforLn2_ofFn_update {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) (y : α) :
    List.ofFn (Function.update f i y) = (List.ofFn f).set i.1 y := by
  refine List.ext_getElem (by simp) (fun j h1 h2 => ?_)
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply]
  by_cases hj : (⟨j, by simpa using h1⟩ : Fin m) = i
  · have : i.1 = j := by rw [← hj]
    simp [hj, this]
  · have : ¬ i.1 = j := fun h => hj (Fin.ext h.symm)
    simp [hj, this]

/-- The `(2k+2)`-loop `STeeLoop` in the form of `(u2jzooi-2)`: the label `b'` is the entry at position `k`
(`0`-based) of the labels before the last one `b`, i.e. `List.ofFn (Function.update a₀ ⟨k, _⟩ b') ++ [b]`. -/
private theorem SEforLn2_eeLoop {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a a' : Fin k → α) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (x0 : α) :
    ∃ (σ'' : Fin (2 * k + 2) → Bool) (a₀ : Fin (2 * k + 2 - 1) → α), ∀ x y : α,
      STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y =
        ⟨List.ofFn σ'', List.ofFn (Function.update a₀ ⟨k, by omega⟩ y) ++ [x]⟩ := by
  set P : List α := (List.ofFn a).drop (j - 1) ++ (List.ofFn a).take (j - 1) with hP
  set R : List α := ((List.ofFn a').take (j - 1)).reverse ++ ((List.ofFn a').drop (j - 1)).reverse with hR
  have hPl : P.length = k := by simp [hP]; omega
  have hRl : R.length = k := by simp [hR]; omega
  obtain ⟨σ'', hσ''⟩ := SEforLn2_exists_ofFn
    ((STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x0 x0).σ) (m := 2 * k + 2)
    (by simp [STeeLoop]; omega)
  obtain ⟨a₀, ha₀⟩ := SEforLn2_exists_ofFn (P ++ x0 :: R) (m := 2 * k + 2 - 1) (by simp [hPl, hRl]; omega)
  refine ⟨σ'', a₀, fun x y => ?_⟩
  have hset : List.ofFn (Function.update a₀ ⟨k, by omega⟩ y) = P ++ y :: R := by
    rw [SEforLn2_ofFn_update, ha₀, List.set_append_right k y (by omega), hPl]
    simp
  rw [hset, hσ'']
  simp only [STeeLoop, hP, hR, List.append_assoc]
  simp

/-- `𝒜(x) = {y : |x - y|_D ≤ 1}`, the support of the row `S^{(B)}_{x ·}` (`Block.lean:38`). -/
private def SEforLn2_nbhd (n : ℕ) (x : Zd d (sz.L n)) : Finset (Zd d (sz.L n)) :=
  Finset.univ.filter fun y => zdistD d (sz.L n) (x - y) ≤ 1

private theorem SEforLn2_nbhd_card (n : ℕ) (x : Zd d (sz.L n)) :
    ((SEforLn2_nbhd sz n x).card : ℝ) ≤ 2 * (d : ℝ) + 1 := by
  have hsub : SEforLn2_nbhd sz n x ⊆ insert x (Finset.univ.filter fun y => Adj d (sz.L n) x y) := by
    intro y hy
    simp only [SEforLn2_nbhd, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.mem_insert]
    by_cases h0 : zdistD d (sz.L n) (x - y) = 0
    · left
      exact (sub_eq_zero.1 ((zdistD_eq_zero_iff d (sz.L n)).1 h0)).symm
    · right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change zdistD d (sz.L n) (x - y) = 1
      omega
  have h := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  rw [card_adj d (sz.L n) (sz.three_le_L n) x] at h
  have h' : (SEforLn2_nbhd sz n x).card ≤ 2 * d + 1 := by omega
  exact_mod_cast h'

private theorem SEforLn2_SB_zero (n : ℕ) (x y : Zd d (sz.L n)) (h : y ∉ SEforLn2_nbhd sz n x) :
    SB d (sz.L n) (sz.lam n) x y = 0 := by
  simp only [SEforLn2_nbhd, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at h
  rw [SB_apply, sbKernel]
  have h0 : x - y ≠ 0 := by
    intro h0
    rw [h0, zdistD_zero] at h
    omega
  have h1 : zdistD d (sz.L n) (x - y) ≠ 1 := by omega
  simp [h0, h1]

private theorem SEforLn2_SB_le_one (n : ℕ) (x y : Zd d (sz.L n)) : ‖SB d (sz.L n) (sz.lam n) x y‖ ≤ 1 :=
  (Finset.single_le_sum (f := fun y => ‖SB d (sz.L n) (sz.lam n) x y‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)).trans (sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) x).le

private theorem SEforLn2_SB_sum (n : ℕ) (x : Zd d (sz.L n)) (f : Zd d (sz.L n) → ℂ) :
    ∑ y : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) x y * f y‖ ≤ ∑ y ∈ SEforLn2_nbhd sz n x, ‖f y‖ := by
  calc ∑ y : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) x y * f y‖
      = ∑ y ∈ SEforLn2_nbhd sz n x, ‖SB d (sz.L n) (sz.lam n) x y * f y‖ :=
        (Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => by
          rw [SEforLn2_SB_zero sz n x y hy]; simp)).symm
    _ ≤ ∑ y ∈ SEforLn2_nbhd sz n x, ‖f y‖ :=
        Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (SEforLn2_SB_le_one sz n x y)

/-- **The contraction of the `(2k+2)`-loop** (`(u2jzooi-2)` with `k`, `j = k + 1`, `l = k + 2`, `p = q`,
`𝒜 b = {b' : |b - b'|_D ≤ 1}`, `3_5:1088-1093`): for the cut edge `j`,
`Σ_b Σ_{b' ∈ 𝒜 b} |𝓛(STeeLoop j b b')| ≤ (2d+1) (W^d η)⁻¹ (max|𝓛^{(2k-1)}| max|𝓛^{(2k-1)}|)^{1/2}
(max|𝓛^{(4q)}|)^{1/(2q)}`. -/
private theorem SEforLn2_eeSum (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1) (ω : sz.SeqΩ)
    {k : ℕ} (hk : 1 ≤ k) {q : ℕ} (hq : 1 ≤ q) (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∑ x : Zd d (sz.L n), ∑ y ∈ SEforLn2_nbhd sz n x,
        ‖sz.STLI n E τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y)‖ ≤
      (2 * (d : ℝ) + 1) * (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
        (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * k - 1) ω) ^ (1 / 2 : ℝ) *
        STmaxL sz n E τ (4 * q) ω ^ (1 / (2 * (q : ℝ))) := by
  obtain ⟨σ'', a₀, hloop⟩ := SEforLn2_eeLoop σ a a' hj1 hjk (0 : Zd d (sz.L n))
  have hc := (stContract_holds d sz n E τ hE h0 h1 ω).2 (2 * k + 2) k (k + 2) q ⟨k, by omega⟩
    (2 * (d : ℝ) + 1) (by omega) hq hk (by simp) (by simp) (by omega) (by positivity)
    (SEforLn2_nbhd sz n) (fun x => SEforLn2_nbhd_card sz n x) σ'' a₀
  rw [show 2 * (2 * k + 2) - 2 * (k + 2) - 1 = 2 * k - 1 by omega, show k + 2 - k = 2 by omega,
    show 2 * 2 * q = 4 * q by omega] at hc
  refine le_trans (le_of_eq ?_) hc
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hloop x y]

/-- **The deterministic core of part (4)**: `‖(ℰ⊗ℰ)^{M,(k)}‖ ≤ k (2d+1) η⁻¹ (max|𝓛^{(2k-1)}|²)^{1/2}
(max|𝓛^{(4q)}|)^{1/(2q)}` for every sample, `u ∈ [0,1)`, `|E| < 2`: the sum over the `k` cut edges of
`(defEOTE)`, `|S^{(B)}| ≤ 1` supported on `𝒜`. -/
private theorem SEforLn2_det4 (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1) (ω : sz.SeqΩ)
    {k : ℕ} (hk : 1 ≤ k) {q : ℕ} (hq : 1 ≤ q) (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) :
    ‖sz.STee n E τ ω σ a a'‖ ≤
      (k : ℝ) * ((2 * (d : ℝ) + 1) * ((etaT E τ)⁻¹ *
        ((STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * k - 1) ω) ^ (1 / 2 : ℝ) *
          STmaxL sz n E τ (4 * q) ω ^ (1 / (2 * (q : ℝ)))))) := by
  have hη : 0 < etaT E τ := etaT_pos hE h1
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  unfold STee
  rw [norm_mul, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  set Rr : ℝ := (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * k - 1) ω) ^ (1 / 2 : ℝ) *
    STmaxL sz n E τ (4 * q) ω ^ (1 / (2 * (q : ℝ))) with hRr
  have hone : ∀ j ∈ Finset.Icc 1 k,
      ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) x y *
          sz.STLI n E τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y)‖ ≤
        (2 * (d : ℝ) + 1) * (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * Rr := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _)) ?_
    refine le_trans (Finset.sum_le_sum fun x _ => SEforLn2_SB_sum sz n x
      (fun y => sz.STLI n E τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y))) ?_
    have := SEforLn2_eeSum sz n hE h0 h1 ω hk hq σ a a' hj.1 hj.2
    rw [hRr, ← mul_assoc]
    exact this
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ j ∈ Finset.Icc 1 k, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        SB d (sz.L n) (sz.lam n) x y *
          sz.STLI n E τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') j x y)‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ j ∈ Finset.Icc 1 k,
          ((2 * (d : ℝ) + 1) * (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * Rr) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)) hWd.le
        exact hone j hj
    _ = (k : ℝ) * ((2 * (d : ℝ) + 1) * ((etaT E τ)⁻¹ * Rr)) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp

/-- The exponent count of part (4): `M₁ ≤ B^{2k-2} Ξ₁`, `M₂ ≤ B^{4q-1} Ξ₂` give
`(M₁ M₁)^{1/2} M₂^{1/(2q)} ≤ B^{2k - 1/(2q)} Ξ₁ Ξ₂^{1/(2q)}` (`(def:XiL)`, `3_5:1093`). -/
private theorem SEforLn2_arith4 {B M1 M2 Ξ1 Ξ2 : ℝ} {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) (hB : 0 < B)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hΞ1 : 0 ≤ Ξ1) (hΞ2 : 0 ≤ Ξ2)
    (h1 : M1 ≤ B ^ (2 * k - 1 - 1) * Ξ1) (h2 : M2 ≤ B ^ (4 * q - 1) * Ξ2) :
    (M1 * M1) ^ (1 / 2 : ℝ) * M2 ^ (1 / (2 * (q : ℝ))) ≤
      B ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) * (Ξ1 * Ξ2 ^ (1 / (2 * (q : ℝ)))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hs : (M1 * M1) ^ (1 / 2 : ℝ) = M1 := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_mul_self hM1
  have h3 : M2 ^ (1 / (2 * (q : ℝ))) ≤ (B ^ (4 * q - 1) * Ξ2) ^ (1 / (2 * (q : ℝ))) :=
    Real.rpow_le_rpow hM2 h2 he
  rw [Real.mul_rpow (by positivity) hΞ2, ← Real.rpow_natCast, ← Real.rpow_mul hB.le] at h3
  have hexp : ((2 * k - 1 - 1 : ℕ) : ℝ) + ((4 * q - 1 : ℕ) : ℝ) * (1 / (2 * (q : ℝ))) =
      (2 * k : ℝ) - 1 / (2 * (q : ℝ)) := by
    have e1 : ((2 * k - 1 - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 2 := by
      rw [show 2 * k - 1 - 1 = 2 * k - 2 by omega, Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : ((4 * q - 1 : ℕ) : ℝ) = 4 * (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2]; field_simp; ring
  rw [hs]
  calc M1 * M2 ^ (1 / (2 * (q : ℝ)))
      ≤ (B ^ (2 * k - 1 - 1) * Ξ1) *
          (B ^ (((4 * q - 1 : ℕ) : ℝ) * (1 / (2 * (q : ℝ)))) * Ξ2 ^ (1 / (2 * (q : ℝ)))) :=
        mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = B ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) * (Ξ1 * Ξ2 ^ (1 / (2 * (q : ℝ)))) := by
        rw [← hexp, Real.rpow_add hB, Real.rpow_natCast]; ring

/-- The core of part (4): deterministic, for an abstract energy sequence `E` with `|E n| < 2` and times
`0 ≤ s ≤ t < 1`. -/
private theorem SEforLn2_part4_core {E s t : ℕ → ℝ} (hN : sz.SizeTendsto) (hE : ∀ n, |E n| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (k : ℕ) (hk : 2 ≤ k) (q : ℕ) (hq : 1 ≤ q) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STee sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / etaT (E n) (p.1 : ℝ) *
        (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1 : ℝ) (4 * q) ω ^
          (1 / (2 * (q : ℝ))))) := by
  have hsize := tendsto_size sz hN
  unfold Prec
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  filter_upwards [hsize.eventually (eventually_le_rpow ((k : ℝ) * (2 * (d : ℝ) + 1)) hτ)] with n hn
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro p
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < etaT (E n) (p.1 : ℝ) := etaT_pos (hE n) hu1
  have hdet := SEforLn2_det4 sz n (hE n) hu0 hu1 ω (by omega) hq p.2.1 p.2.2.1 p.2.2.2
  have hX1 := zero_le_one.trans (SEforLn2_one_le_XiL sz n (E n) (p.1 : ℝ) ω (2 * k - 1) hB)
  have hX2 := zero_le_one.trans (SEforLn2_one_le_XiL sz n (E n) (p.1 : ℝ) ω (4 * q) hB)
  have hR := SEforLn2_arith4 (k := k) (q := q) (by omega) hq hB
    (SEforLn2_STmaxL_nonneg sz n _ _ _ ω) (SEforLn2_STmaxL_nonneg sz n _ _ _ ω) hX1 hX2
    (SEforLn2_maxL_le sz n (E n) (p.1 : ℝ) ω _ hB) (SEforLn2_maxL_le sz n (E n) (p.1 : ℝ) ω _ hB)
  have hZ0 : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / etaT (E n) (p.1 : ℝ) *
      (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1 : ℝ) (4 * q) ω ^
        (1 / (2 * (q : ℝ)))) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg hB.le _) hη.le)
      (mul_nonneg hX1 (Real.rpow_nonneg hX2 _))
  have hη' : 0 ≤ (etaT (E n) (p.1 : ℝ))⁻¹ := inv_nonneg.2 hη.le
  calc ‖STee sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖
      ≤ (k : ℝ) * ((2 * (d : ℝ) + 1) * ((etaT (E n) (p.1 : ℝ))⁻¹ *
        ((STmaxL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STmaxL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω) ^
            (1 / 2 : ℝ) * STmaxL sz n (E n) (p.1 : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ)))))) := hdet
    _ ≤ (k : ℝ) * ((2 * (d : ℝ) + 1) * ((etaT (E n) (p.1 : ℝ))⁻¹ *
        ((sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) *
          (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR hη')
          (by positivity)) (by positivity)
    _ = (k : ℝ) * (2 * (d : ℝ) + 1) *
        ((sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / etaT (E n) (p.1 : ℝ) *
          (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))) := by
        field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        ((sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / etaT (E n) (p.1 : ℝ) *
          (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1 : ℝ) (4 * q) ω ^
            (1 / (2 * (q : ℝ))))) := mul_le_mul_of_nonneg_right hn hZ0

/-- **Part (4) of `lem:SEforLn`, `(eq:MG_nloop)`** (`3_5:1042-1046`, proof `3_5:1088-1093`): along the flow
`STFlow` with `0 ≤ s`, `t ≤ lemT z`, for every `k ≥ 2` and `q ≥ 1`,
`max_{σ,a,a'} |(ℰ⊗ℰ)^{M,(k)}_{u,σ,a,a'}| ≺ (W^{-d}B_{u,0})^{2k-1/(2q)} η_u⁻¹ Ξ̂^{𝓛}_{u,2k-1} (Ξ̂^{𝓛}_{u,4q})^{1/(2q)}`,
uniformly in `u ∈ [s_n, t_n]`.  The input is the second inequality of the contraction `stContract_holds`
(`(u2jzooi-2)` with `m = 2k+2`, `l = k + 2`, `p = q`), a deterministic inequality; no stochastic hypothesis.  The
conclusion is the fourth conjunct of `STSEforLnConcl sz (STflowE z) s t` at `k`. -/
theorem stSEforLn_part4 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n)) (k : ℕ) (hk : 2 ≤ k) :
    ∀ q : ℕ, 1 ≤ q →
      Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) ×
          (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STee sz n (STflowE z n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) /
            etaT (STflowE z n) (p.1 : ℝ) *
          (STXiL sz n (STflowE z n) (p.1 : ℝ) (2 * k - 1) ω *
            STXiL sz n (STflowE z n) (p.1 : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ))))) := by
  intro q hq
  have him := SEforLn2_flow_im sz hflow
  exact SEforLn2_part4_core sz hflow.1.2.2.1 (fun n => abs_lemE_lt_two (him n)) hs
    (fun n => (ht n).trans_lt (lemT_lt_one (him n))) k hk q hq

/-! ## 10. The pin `STSEforLn` -/

/-- **`lem:SEforLn`** (`3_5:1017-1046`), the four estimates of the `ℰ` terms, for every `d ≥ 3`
(`STSEforLn d`, `Step34Pins.lean:456`): `𝔠_d = min (1/100) (1/(30 C_d))` (as in `stSumTwoLoop_exists`; `𝔠_d C_d ≤ 1/30`
is what `(eq:sumtwoloop)` needs; parts (1), (2), (4) hold for every `𝔠_d`), then the four parts:
`stSEforLn_part1` (`STAvgU`, the second input of `STStep2Concl`), `stSEforLn_part2` (no stochastic input),
`stSEforLn_part3` (`STGdecayW`, the third input of `STStep2Concl`), `stSEforLn_part4` (no stochastic input).  The
other hypotheses of the pin (`STKbound`, `STKward`, `STLK s`, the regime `STAny`) are not used. -/
theorem stSEforLn_holds (d : ℕ) : STSEforLn d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have h𝔠d : 0 < min (1 / 100 : ℝ) (1 / (30 * Cd)) := lt_min (by norm_num) (by positivity)
  refine ⟨min (1 / 100) (1 / (30 * Cd)), h𝔠d, min_le_left _ _, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht _ _ _ _ hcon hStep2 k hk
  have hcc : min (1 / 100 : ℝ) (1 / (30 * Cd)) * Cd ≤ 1 / 30 :=
    calc min (1 / 100 : ℝ) (1 / (30 * Cd)) * Cd ≤ 1 / (30 * Cd) * Cd :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hCd.le
      _ = 1 / 30 := by field_simp
  exact ⟨stSEforLn_part1 sz hflow hs ht hStep2.2.1 k hk, stSEforLn_part2 hd sz hκ hflow hs hst ht k,
    stSEforLn_part3 hd sz hκ hCd h𝔠d hcc hflow hs hst ht hcon hStep2.2.2 k hk,
    stSEforLn_part4 sz hflow hs ht k hk⟩

end RBM.Gauss.Sizes

/-! ## 11. Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the flow
`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, `s ≡ 0`, `t ≡ 1/16` (`1/16 ≤ lemT z0`): a nondegenerate window
`[0, 1/16]`, nonempty index sets, `C_d = 4`, `𝔠_d = 1/120` (`𝔠_d C_d = 1/30`, `(con_st_ind)` from `sz0_con`).  Part (3) at
`k = 2` (sum over `n'` empty) and `k = 4` (`n' = 3`, `STn12 3 = (1, 3)`); part (4) at `(k, q) = (2, 1)` and `(4, 2)`.
The uniform 2-`G`-loop estimate `STGdecayW` of part (3) is the output of another gate (Step 2) and stays a
hypothesis of the examples; every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s`, `s < t`, `t ≤ lemT z`,
`0 < κ`, `0 < C_d`, `0 < 𝔠_d`, `𝔠_d C_d ≤ 1/30`, `(con_st_ind)`) is discharged.  Part (4) has no stochastic hypothesis. -/

namespace RBM.Gauss.SEforLn2Inst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step34Inst

/-- The index set of the instances is nonempty at every size index (window point `0 ∈ [0, 1/16]`, charges `(+, +)`,
labels `0`). -/
example (n : ℕ) :
    Nonempty (TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) × (Fin 2 → Zd 3 (sz0.L n))) :=
  ⟨⟨0, by simp [sInst, tInst]⟩, fun _ => true, fun _ => 0, fun _ => 0⟩

/-- The ranges of `n'` and the indices `(n'₁, n'₂)` of part (3). -/
example : Finset.Icc ((2 + 1) / 2 + 1) (2 - 1) = ∅ := by decide
example : Finset.Icc ((4 + 1) / 2 + 1) (4 - 1) = {3} := by decide
example : STn12 3 = (1, 3) := by decide

/-- **`stSEforLn_part3` at `k = 2`** (the sum over `n'` is empty: `B²/η · B^{1/6} Ξ̂^{𝓛-𝒦}_2`). -/
example (hG : STGdecayW sz0 (STflowE z0) sInst tInst 4) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STelklk sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 2 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((2 + 1) / 2 + 1) (2 - 1),
            STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) (2 + 2 - n') ω *
              (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 2 ω)) :=
  stSEforLn_part3 (by norm_num) sz0 (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (Cd := 4)
    (𝔠d := 1 / 120) (by norm_num) (by norm_num) (by norm_num) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht
    (sz0_con (1 / 120) (by norm_num)) hG 2 le_rfl

/-- **`stSEforLn_part3` at `k = 4`** (`n' = 3`: `B⁴/η (Ξ̂^{𝓛-𝒦}_3 (Ξ̂^{𝓛}_1 Ξ̂^{𝓛}_3)^{1/2} + B^{1/6} Ξ̂^{𝓛-𝒦}_4)`). -/
example (hG : STGdecayW sz0 (STflowE z0) sInst tInst 4) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 4 → Bool) × (Fin 4 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STelklk sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 4 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((4 + 1) / 2 + 1) (4 - 1),
            STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) (4 + 2 - n') ω *
              (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').1 ω *
                STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 4 ω)) :=
  stSEforLn_part3 (by norm_num) sz0 (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (Cd := 4)
    (𝔠d := 1 / 120) (by norm_num) (by norm_num) (by norm_num) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht
    (sz0_con (1 / 120) (by norm_num)) hG 4 (by norm_num)

/-- **`stSEforLn_part4` at `(k, q) = (2, 1)`**: `B^{4 - 1/2}/η · Ξ̂^{𝓛}_3 (Ξ̂^{𝓛}_4)^{1/2}`; no stochastic hypothesis. -/
example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) ×
        (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STee sz0 n (STflowE z0 n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ ((2 * ((2 : ℕ) : ℝ)) - 1 / (2 * ((1 : ℕ) : ℝ))) /
          etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (2 * 2 - 1) ω *
          STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (4 * 1) ω ^ (1 / (2 * ((1 : ℕ) : ℝ))))) :=
  stSEforLn_part4 sz0 flow_z0 sz0_hs0 sz0_ht 2 le_rfl 1 le_rfl

/-- **`stSEforLn_part4` at `(k, q) = (4, 2)`**: `B^{8 - 1/4}/η · Ξ̂^{𝓛}_7 (Ξ̂^{𝓛}_8)^{1/4}`. -/
example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 4 → Bool) × (Fin 4 → Zd 3 (sz0.L n)) ×
        (Fin 4 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STee sz0 n (STflowE z0 n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ ((2 * ((4 : ℕ) : ℝ)) - 1 / (2 * ((2 : ℕ) : ℝ))) /
          etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (2 * 4 - 1) ω *
          STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) (4 * 2) ω ^ (1 / (2 * ((2 : ℕ) : ℝ))))) :=
  stSEforLn_part4 sz0 flow_z0 sz0_hs0 sz0_ht 4 (by norm_num) 2 (by norm_num)

/-- **`stSEforLn_holds` at `d = 3`**: the pin `STSEforLn 3`, nonempty by construction (a theorem); and its merged
instance `Step34Inst.inst_SEforLn` at `(sz0, z0, 0, 1/16)`, `C_d = 4`. -/
example : STSEforLn 3 := stSEforLn_holds 3

example : InstIngConcl (fun sz E s t => STSEforLnConcl sz E s t) sz0 z0 sInst tInst 4 :=
  inst_SEforLn (stSEforLn_holds 3) 4 (by norm_num)

/-! ### The interface with `STSEforLnConcl`

The four conclusions are the four conjuncts of `STSEforLnConcl sz (STflowE z) s t` at `k`, definitionally. -/

example {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 Cd 𝔠d : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hCd : 0 < Cd)
    (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hcon : STConStInd sz 𝔠d s t) (hG : STGdecayW sz (STflowE z) s t Cd)
    (hconcl : STSEforLnConcl sz (STflowE z) s t) (k : ℕ) (hk : 2 ≤ k) :
    stSEforLn_part3 hd sz hκ hCd h𝔠d hcc hflow hs hst ht hcon hG k hk = (hconcl k hk).2.2.1 := rfl

example {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n)) (hconcl : STSEforLnConcl sz (STflowE z) s t)
    (k : ℕ) (hk : 2 ≤ k) :
    stSEforLn_part4 sz hflow hs ht k hk = (hconcl k hk).2.2.2 := rfl

end RBM.Gauss.SEforLn2Inst
