/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Contract
import RBM3D.Induction.KDecay
import RBM3D.Induction.DecayLoopB

/-!
# S3-08 (ticket T2137): `lem:SEforLn`, parts (1) and (2)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: `lem:SEforLn` (`3_5:1017-1034`),
proof `3_5:1047-1062`, `(bEwGn)`, `(eq:KsimL-K)`, `(yi2oslxj2)`, `(Gt_avgbound_flow)`,
`(wardineq_K)`.  The reference (older paper version) is RBM2D `Induction/BcalE.lean` at
`c9a24cf`, conjuncts (i)-(ii), whose window decomposition is replaced here by the contraction
inequality (`stContract_holds`) and the `𝒦`-loop Ward bound (`stKward_timeIcc`).

* `stSEforLn_part1`: `‖ℰ^{G̃,(k)}‖ ≺ B^k η⁻¹ (Ξ̂^{𝓛}_{n₁} Ξ̂^{𝓛}_{n₂})^{1/2}`,
  `(n₁, n₂) = STn12E k`, uniformly in `u ∈ [s,t]` and the labels: the first conjunct of
  `STSEforLnConcl` (`Step34Pins.lean:363`), from the uniform averaged local law `STAvgU` and
  the contraction inequality.
* `stSEforLn_part2`: `‖[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)}‖ ≺ B^k η⁻¹ Ξ̂^{𝓛-𝒦}_{k-l+2}`, `3 ≤ l ≤ k`: the
  second conjunct, from the uniform `𝒦`-loop Ward bound `stKward_timeIcc` (no hypothesis beyond
  the flow).

The deterministic core (§1-§3, §5) is a bound for every sample `ω` and every time `τ ∈ [0,1)`,
`|E| < 2`; the `≺` is assembled in §4 and §6 by the inclusion of the bad events.  Every helper
that the ticket does not pin is `private` with the prefix `SEforLn1_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Lists, rotation of `𝓛` and `𝒦` -/

private theorem SEforLn1_exists_ofFn {α : Type*} (l : List α) {m : ℕ} (h : l.length = m) :
    ∃ f : Fin m → α, List.ofFn f = l := by
  subst h
  exact ⟨l.get, List.ofFn_get l⟩

section Rot

variable {d L W : ℕ} [NeZero L]

private theorem SEforLn1_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
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

/-- Cyclic invariance of `𝓛`: moving the first edge to the end (trace cyclicity). -/
private theorem SEforLn1_loopL_rotate (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool)
    (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [SEforLn1_loopL_eq_prod, SEforLn1_loopL_eq_prod]
  simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
  rw [List.zip_append h]
  simp only [List.map_append, List.prod_append, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

/-- Rotating a loop by `j` positions does not change `𝓛`. -/
private theorem SEforLn1_loopL_rotate_iter {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} :
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
        exact (SEforLn1_loopL_rotate H z s b σ a h').symm

end Rot

variable {d : ℕ} (sz : Sizes d)

/-- `𝓛` of the pins (`STLI`) is invariant under rotation. -/
private theorem SEforLn1_STLI_rotate (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (j : ℕ) (σ : List Bool)
    (a : List (Zd d (sz.L n))) (h : σ.length = a.length) :
    sz.STLI n E τ ω ⟨σ.rotate j, a.rotate j⟩ = sz.STLI n E τ ω ⟨σ, a⟩ :=
  SEforLn1_loopL_rotate_iter j σ a h

/-- `𝒦` of the pins (`STKI`) is invariant under rotation (`KLK_rotate`, iterated). -/
private theorem SEforLn1_STKI_rotate (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (hτ : τ ∈ Set.Ico (0 : ℝ) 1)
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

/-- A well-formed loop is `loopOf` of its entries. -/
private theorem SEforLn1_loopOf_eq {α : Type*} (J : LoopIdx α) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- `(𝓛-𝒦)` of a `loopOf` index. -/
private theorem SEforLn1_STLKI_eq (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    sz.STLKI n E τ ω (loopOf σ a) = Lloop sz n E τ σ a ω - STKloop sz n E τ σ a := by
  unfold STLKI STKI STKloop STLI
  rw [← loopM_eq_loopL]; rfl

private theorem SEforLn1_STmaxL_nonneg (n : ℕ) (E t : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    0 ≤ STmaxL sz n E t k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖Lloop sz n E t p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

private theorem SEforLn1_STmaxLK_nonneg (n : ℕ) (E t : ℝ) (k : ℕ) (ω : sz.SeqΩ) :
    0 ≤ STmaxLK sz n E t k ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
    ‖Lloop sz n E t p.1 p.2 ω - STKloop sz n E t p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => 0))))

/-- Every well-formed loop of length `m` is bounded by `max_{σ,a} |(𝓛-𝒦)^{(m)}|`. -/
private theorem SEforLn1_norm_STLKI_le (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (J : LoopIdx (Zd d (sz.L n)))
    (hJ : J.WF) : ‖sz.STLKI n E τ ω J‖ ≤ STmaxLK sz n E τ J.length ω := by
  have hJ' := SEforLn1_loopOf_eq J hJ
  conv_lhs => rw [← hJ']
  rw [SEforLn1_STLKI_eq]
  exact Finset.le_sup' (fun p : (Fin J.a.length → Bool) × (Fin J.a.length → Zd d (sz.L n)) =>
    ‖Lloop sz n E τ p.1 p.2 ω - STKloop sz n E τ p.1 p.2‖)
    (Finset.mem_univ ((fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2)),
      (fun i : Fin J.a.length => J.a[i.1])))

/-- `tr(G̃(σ) E_a) = (𝓛-𝒦)^{(1)}_{σ,a}` as a `loopOf` loop. -/
private theorem SEforLn1_avgErr_eq (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a : Zd d (sz.L n)) :
    sz.STavgErr n E τ ω σ a =
      Lloop sz n E τ (fun _ : Fin 1 => σ) (fun _ => a) ω -
        STKloop sz n E τ (fun _ : Fin 1 => σ) (fun _ => a) := by
  have h1 : sz.STavgErr n E τ ω σ a = sz.STLKI n E τ ω ⟨[σ], [a]⟩ := by
    unfold STavgErr STLKI STKI
    rw [KLK_one]
  rw [h1]
  have h2 : (⟨[σ], [a]⟩ : LoopIdx (Zd d (sz.L n))) = loopOf (fun _ : Fin 1 => σ) (fun _ => a) := by
    simp [loopOf]
  rw [h2, SEforLn1_STLKI_eq]


/-! ## 2. The cut `cutGlue`: contraction of the glued label (part 1) -/

private theorem SEforLn1_cut_rotate {α : Type*} (σ : List Bool) (a : List α) (b : α) {j p : ℕ}
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

/-- The column sums of `S^{(B)}`: `Σ_a |S_{ab}| = 1`. -/
private theorem SEforLn1_sum_norm_SB_col (n : ℕ) (b : Zd d (sz.L n)) :
    ∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖ = 1 := by
  have hsym : ∀ x y : Zd d (sz.L n), SB d (sz.L n) (sz.lam n) y x = SB d (sz.L n) (sz.lam n) x y :=
    fun x y => congrFun (congrFun (SB_isSymm d (sz.L n) (sz.lam n)) x) y
  calc ∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) a b‖
      = ∑ a : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) b a‖ :=
        Finset.sum_congr rfl fun a _ => by rw [hsym a b]
    _ = 1 := sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) b

/-- `Σ_{a,b} F(a) |S_{ab}| G(b) ≤ (sup F) Σ_b G(b)` (column sums of `S`). -/
private theorem SEforLn1_sum_glue_left (n : ℕ) (F G : Zd d (sz.L n) → ℝ) {M : ℝ}
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
    _ = _ := by simp only [SEforLn1_sum_norm_SB_col sz n, one_mul]

/-- `Σ_{a,b} F(a) |S_{ab}| G(b) ≤ (sup G) Σ_a F(a)` (row sums of `S`). -/
private theorem SEforLn1_sum_glue_right (n : ℕ) (F G : Zd d (sz.L n) → ℝ) {M : ℝ}
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

/-- `(n₁, n₂) = STn12E k` is the pair of lengths of the contraction inequality for the `(k+1)`-loop cut
at `⌈k/2⌉ = (k+1)/2`: `(2⌈k/2⌉ - 1, 2(k+1) - 2⌈k/2⌉ - 1)`. -/
private theorem SEforLn1_n12 (k : ℕ) (hk : 1 ≤ k) :
    2 * ((k + 1) / 2) - 1 = (STn12E k).1 ∧ 2 * (k + 1) - 2 * ((k + 1) / 2) - 1 = (STn12E k).2 := by
  unfold STn12E
  split_ifs with h <;> simp only <;> omega

/-- **The contraction of the glued label**: `Σ_b |𝓛(cutGlue_j^{(b)} I)| ≤ (W^d η)⁻¹ (max|𝓛^{(n₁)}| max|𝓛^{(n₂)}|)^{1/2}`
for a loop of length `k ≥ 1` and the edge `1 ≤ j ≤ k` (`(yi2oslxj2)` with `k' = ⌈k/2⌉`, after rotating the new
label to the last position). -/
private theorem SEforLn1_sum_cutGlue (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {k : ℕ} (hk : 1 ≤ k) (σ : List Bool) (a : List (Zd d (sz.L n)))
    (hσ : σ.length = k) (ha : a.length = k) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∑ b : Zd d (sz.L n), ‖sz.STLI n E τ ω ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlue j b)‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
        (STmaxL sz n E τ (STn12E k).1 ω * STmaxL sz n E τ (STn12E k).2 ω) ^ (1 / 2 : ℝ) := by
  obtain ⟨σ₁, hσ₁⟩ := SEforLn1_exists_ofFn (σ.drop (j - 1) ++ σ.take j) (m := k + 1)
    (by simp [hσ]; omega)
  obtain ⟨a₁, ha₁⟩ := SEforLn1_exists_ofFn (a.drop (j - 1) ++ a.take (j - 1)) (m := k + 1 - 1)
    (by simp [ha]; omega)
  have hc := (stContract_holds d sz n E τ hE h0 h1 ω).1 (k + 1) ((k + 1) / 2) (by omega) (by omega)
    σ₁ a₁
  obtain ⟨e1, e2⟩ := SEforLn1_n12 k hk
  rw [e1, e2] at hc
  refine le_trans (le_of_eq ?_) hc
  refine Finset.sum_congr rfl fun b _ => ?_
  have hrot := SEforLn1_cut_rotate σ a b (j := j) (p := j - 1) (by omega) (by omega) hj1
  have hlen : (σ.take j ++ σ.drop (j - 1)).length = (a.take (j - 1) ++ b :: a.drop (j - 1)).length := by
    simp [hσ, ha]; omega
  have := SEforLn1_STLI_rotate sz n E τ ω j _ _ hlen
  rw [hrot] at this
  change ‖sz.STLI n E τ ω ⟨σ.take j ++ σ.drop (j - 1), a.take (j - 1) ++ b :: a.drop (j - 1)⟩‖ = _
  rw [← this, hσ₁, ha₁]

/-- **`ℰ^{G̃,(k)}` of a loop by the contraction inequality** (`3_5:1048-1053`): if `|tr(G̃(σ) E_a)| ≤ δ` for all
`σ`, `a`, then `‖ℰ^{G̃,(k)}‖ ≤ k δ η⁻¹ (max|𝓛^{(n₁)}| max|𝓛^{(n₂)}|)^{1/2}`: the sum over the cut edge `j`, the
column sums of `S^{(B)}`, and `Σ_b |𝓛(cutGlue_j^{(b)})|` by `SEforLn1_sum_cutGlue`. -/
private theorem SEforLn1_det_egt (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (h0 : 0 ≤ τ) (h1 : τ < 1)
    (ω : sz.SeqΩ) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) {δ : ℝ}
    (hδ : ∀ s x, ‖sz.STavgErr n E τ ω s x‖ ≤ δ) :
    ‖sz.STegt n E τ ω ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
      k * δ * (etaT E τ)⁻¹ *
        (STmaxL sz n E τ (STn12E k).1 ω * STmaxL sz n E τ (STn12E k).2 ω) ^ (1 / 2 : ℝ) := by
  have hη : 0 < etaT E τ := etaT_pos hE h1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set R : ℝ := (STmaxL sz n E τ (STn12E k).1 ω * STmaxL sz n E τ (STn12E k).2 ω) ^ (1 / 2 : ℝ) with hR
  have hC : ∀ j ∈ Finset.Icc 1 k,
      ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ‖sz.STavgErr n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).σ.getD (j - 1) false) x‖ *
          ‖SB d (sz.L n) (sz.lam n) x y‖ *
          ‖sz.STLI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlue j y)‖ ≤
        δ * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * R) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine (SEforLn1_sum_glue_left sz n _ _ (fun x => hδ _ x) (fun y => norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (SEforLn1_sum_cutGlue sz n hE h0 h1 ω hk (List.ofFn σ) (List.ofFn a) (by simp) (by simp) hj.1 hj.2)
      ((norm_nonneg _).trans (hδ true 0))
  unfold STegt
  have hlen : (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).length = k := by
    simp [LoopIdx.length]
  rw [norm_mul, hlen, show ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d by simp]
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ j ∈ Finset.Icc 1 k, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        sz.STavgErr n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).σ.getD (j - 1) false) x *
          SB d (sz.L n) (sz.lam n) x y *
          sz.STLI n E τ ω ((⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (Zd d (sz.L n))).cutGlue j y)‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ j ∈ Finset.Icc 1 k,
          (δ * ((((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * R)) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)) hW.le
        refine (norm_sum_le _ _).trans ?_
        refine le_trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => le_of_eq ?_)) (hC j hj)
        rw [norm_mul, norm_mul]
    _ = k * δ * (etaT E τ)⁻¹ * R := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp

/-! ## 3. The controls `Ξ̂` and the arithmetic of the exponents -/

private theorem SEforLn1_maxL_le (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    STmaxL sz n E u m ω ≤ sz.Bctl n u ^ (m - 1) * STXiL sz n E u m ω := by
  unfold STXiL
  have h0 := SEforLn1_STmaxL_nonneg sz n E u m ω
  have hp : 0 < sz.Bctl n u ^ (m - 1) := pow_pos hB _
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne']
  linarith [hp.le]

private theorem SEforLn1_maxLK_le (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    STmaxLK sz n E u m ω ≤ sz.Bctl n u ^ m * STXiLK sz n E u m ω := by
  unfold STXiLK
  have h0 := SEforLn1_STmaxLK_nonneg sz n E u m ω
  have hp : 0 < sz.Bctl n u ^ m := pow_pos hB _
  rw [mul_add, mul_one, mul_div_cancel₀ _ hp.ne']
  linarith [hp.le]

private theorem SEforLn1_XiL_nonneg (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    0 ≤ STXiL sz n E u m ω := by
  unfold STXiL
  have := SEforLn1_STmaxL_nonneg sz n E u m ω
  have : 0 ≤ STmaxL sz n E u m ω / sz.Bctl n u ^ (m - 1) := by positivity
  linarith

private theorem SEforLn1_XiLK_nonneg (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (m : ℕ) (hB : 0 < sz.Bctl n u) :
    0 ≤ STXiLK sz n E u m ω := by
  unfold STXiLK
  have := SEforLn1_STmaxLK_nonneg sz n E u m ω
  have : 0 ≤ STmaxLK sz n E u m ω / sz.Bctl n u ^ m := by positivity
  linarith

private theorem SEforLn1_n12_sum (k : ℕ) (hk : 2 ≤ k) :
    ((STn12E k).1 - 1) + ((STn12E k).2 - 1) = 2 * (k - 1) := by
  unfold STn12E
  split_ifs with h <;> simp only <;> omega

/-- `(max|𝓛^{(n₁)}| max|𝓛^{(n₂)}|)^{1/2} ≤ B^{k-1} (Ξ̂_{n₁} Ξ̂_{n₂})^{1/2}`, `n₁ + n₂ = 2k`. -/
private theorem SEforLn1_R_le {B M1 M2 Ξ1 Ξ2 : ℝ} {n1 n2 k : ℕ} (hB : 0 < B) (hM1 : 0 ≤ M1)
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

/-- The exponent count of part (1): `k (a B) η⁻¹ R ≤ a² (B^k/η) X^{1/2}` for `k ≤ a`, `R ≤ B^{k-1} X^{1/2}`. -/
private theorem SEforLn1_arith1 {kk a B η R Y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkk : 0 ≤ kk) (hka : kk ≤ a) (hB : 0 ≤ B)
    (hη : 0 < η) (hR0 : 0 ≤ R) (hY : 0 ≤ Y) (ha : 0 ≤ a) (hR : R ≤ B ^ (k - 1) * Y) :
    kk * (a * B) * η⁻¹ * R ≤ a * a * (B ^ k / η * Y) := by
  have hBk : B ^ k = B * B ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hη' : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  calc kk * (a * B) * η⁻¹ * R ≤ a * (a * B) * η⁻¹ * (B ^ (k - 1) * Y) := by
        gcongr
    _ = a * a * (B ^ k / η * Y) := by rw [hBk]; field_simp

/-! ## 4. Part (1): `(bEwGn)` -/

/-- `StochDomAt.of_subset` with a different parameter family for the source (the failure event of the
target is contained in the failure event of the source). -/
private theorem SEforLn1_of_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U₁ U : ℕ → Type*} {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

/-- The core of part (1), for an abstract energy sequence `E` with `|E n| < 2` and times `0 ≤ s ≤ t < 1`. -/
private theorem SEforLn1_part1_core {E s t : ℕ → ℝ} (hN : sz.SizeTendsto) (hE : ∀ n, |E n| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hAvg : STAvgU sz E s t) (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegt sz n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        (STXiL sz n (E n) (p.1 : ℝ) (STn12E k).1 ω * STXiL sz n (E n) (p.1 : ℝ) (STn12E k).2 ω) ^
          (1 / 2 : ℝ)) := by
  have hsize := tendsto_size sz hN
  unfold STAvgU Prec at hAvg
  unfold Prec
  refine SEforLn1_of_subset hAvg (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  filter_upwards [hsize.eventually (eventually_le_rpow (k : ℝ) (half_pos hτ))] with n hkN
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < etaT (E n) (p.1 : ℝ) := etaT_pos (hE n) hu1
  have hNa : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hδ : ∀ σ x, ‖sz.STavgErr n (E n) (p.1 : ℝ) ω σ x‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * sz.Bctl n (p.1 : ℝ) := by
    intro σ x
    rw [SEforLn1_avgErr_eq]
    have := hno (p.1, (fun _ : Fin 1 => σ), (fun _ => x))
    simpa using this
  have hd1 := SEforLn1_det_egt sz n (hE n) hu0 hu1 ω (by omega) p.2.1 p.2.2 hδ
  obtain ⟨hn1, hn2⟩ : 1 ≤ (STn12E k).1 ∧ 1 ≤ (STn12E k).2 := by
    unfold STn12E; split_ifs <;> simp only <;> omega
  have hRle := SEforLn1_R_le (k := k) hB (SEforLn1_STmaxL_nonneg sz n (E n) (p.1 : ℝ) _ ω)
    (SEforLn1_STmaxL_nonneg sz n (E n) (p.1 : ℝ) _ ω)
    (SEforLn1_maxL_le sz n (E n) (p.1 : ℝ) ω _ hB) (SEforLn1_maxL_le sz n (E n) (p.1 : ℝ) ω _ hB)
    (SEforLn1_XiL_nonneg sz n (E n) (p.1 : ℝ) ω _ hB) (SEforLn1_XiL_nonneg sz n (E n) (p.1 : ℝ) ω _ hB)
    (SEforLn1_n12_sum k hk)
  have hR0 : 0 ≤ (STmaxL sz n (E n) (p.1 : ℝ) (STn12E k).1 ω *
      STmaxL sz n (E n) (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (SEforLn1_STmaxL_nonneg sz n _ _ _ ω)
      (SEforLn1_STmaxL_nonneg sz n _ _ _ ω)) _
  have hY0 : 0 ≤ (STXiL sz n (E n) (p.1 : ℝ) (STn12E k).1 ω *
      STXiL sz n (E n) (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (SEforLn1_XiL_nonneg sz n _ _ ω _ hB)
      (SEforLn1_XiL_nonneg sz n _ _ ω _ hB)) _
  have hfin := SEforLn1_arith1 (kk := (k : ℝ)) (a := ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (B := sz.Bctl n (p.1 : ℝ)) (η := etaT (E n) (p.1 : ℝ)) (k := k) (by omega)
    (Nat.cast_nonneg _) hkN hB.le hη hR0 hY0 hNa hRle
  rw [UnifDetDom.rpow_half_mul_rpow_half _ hτ] at hfin
  have hd2 : ‖sz.STegt n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        (STXiL sz n (E n) (p.1 : ℝ) (STn12E k).1 ω * STXiL sz n (E n) (p.1 : ℝ) (STn12E k).2 ω) ^
          (1 / 2 : ℝ)) := hd1.trans hfin
  exact absurd hp (not_lt.2 hd2)

/-- The flow has `Im z_n > 0`. -/
private theorem SEforLn1_flow_im {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1

/-- **Part (1) of `lem:SEforLn`, `(bEwGn)`** (`3_5:1017-1027`, proof `3_5:1047-1053`): along the flow `STFlow` with
`0 ≤ s < t ≤ lemT z`, from the uniform averaged local law `STAvgU` (`(Gt_avgbound_flow)`, a conclusion of Step 2:
the third input of `STStep2Concl`), for every `k ≥ 2`,
`max_{σ,a} |ℰ^{G̃,(k)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^k η_u⁻¹ (Ξ̂^{𝓛}_{u,n₁} Ξ̂^{𝓛}_{u,n₂})^{1/2}`,
`(n₁, n₂) = STn12E k`, uniformly in `u ∈ [s_n, t_n]`.  The conclusion is the first conjunct of
`STSEforLnConcl sz (STflowE z) s t` at `k`. -/
theorem stSEforLn_part1 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hAvg : STAvgU sz (STflowE z) s t) (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegt sz n (STflowE z n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (STflowE z n) (p.1 : ℝ) *
        (STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12E k).1 ω *
          STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ)) :=
  SEforLn1_part1_core sz hflow.1.2.2.1 (fun n => abs_lemE_lt_two (SEforLn1_flow_im sz hflow n)) hs
    (fun n => (ht n).trans_lt (lemT_lt_one (SEforLn1_flow_im sz hflow n))) hAvg k hk

/-! ## 5. The cuts `cutGlueL`, `cutGlueR` of part (2) -/

/-- `Σ_{1 ≤ k < l' ≤ m} f(k, l') ≤ m² T`. -/
private theorem SEforLn1_sum_pairs (m : ℕ) (f : ℕ → ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
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

private theorem SEforLn1_norm_ite (p : Prop) [Decidable p] (x : ℂ) :
    ‖(if p then x else 0)‖ = if p then ‖x‖ else 0 := by
  split_ifs <;> simp

/-- The `𝒦`-piece `cutGlueR` of length `l` has its summed label last: the Ward bound applies directly. -/
private theorem SEforLn1_sum_cutGlueR_K (n : ℕ) {E τ : ℝ} {l : ℕ} {Kw : ℝ}
    (hKw : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw)
    {m : ℕ} (σ : List Bool) (a : List (Zd d (sz.L n))) (hσ : σ.length = m) (ha : a.length = m)
    {k l' : ℕ} (hk : 1 ≤ k) (hkl : k < l') (hl' : l' ≤ m) (hl : l' - k + 1 = l) :
    ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueR k l' x)‖ ≤ Kw := by
  obtain ⟨σ₁, hσ₁⟩ := SEforLn1_exists_ofFn ((σ.drop (k - 1)).take (l' - k + 1)) (m := l)
    (by simp [hσ]; omega)
  obtain ⟨a₁, ha₁⟩ := SEforLn1_exists_ofFn ((a.drop (k - 1)).take (l' - k)) (m := l - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hKw σ₁ a₁)
  simp only [LoopIdx.cutGlueR, hσ₁, ha₁]

/-- The `𝒦`-piece `cutGlueL` of length `l`: its summed label is rotated to the last position
(`KLK_rotate`), then the Ward bound applies. -/
private theorem SEforLn1_sum_cutGlueL_K (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (hτ : τ ∈ Set.Ico (0 : ℝ) 1)
    {l : ℕ} {Kw : ℝ}
    (hKw : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw)
    {m : ℕ} (σ : List Bool) (a : List (Zd d (sz.L n))) (hσ : σ.length = m) (ha : a.length = m)
    {k l' : ℕ} (hk : 1 ≤ k) (hkl : k < l') (hl' : l' ≤ m) (hl : k + m - l' + 1 = l) :
    ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ((⟨σ, a⟩ : LoopIdx (Zd d (sz.L n))).cutGlueL k l' x)‖ ≤ Kw := by
  obtain ⟨σ₂, hσ₂⟩ := SEforLn1_exists_ofFn (σ.drop (l' - 1) ++ σ.take k) (m := l)
    (by simp [hσ]; omega)
  obtain ⟨a₂, ha₂⟩ := SEforLn1_exists_ofFn (a.drop (l' - 1) ++ a.take (k - 1)) (m := l - 1)
    (by simp [ha]; omega)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) (hKw σ₂ a₂)
  have hrot := SEforLn1_cut_rotate σ a x (j := k) (p := l' - 1) (by omega) (by omega) hk
  have hlen : (σ.take k ++ σ.drop (l' - 1)).length = (a.take (k - 1) ++ x :: a.drop (l' - 1)).length := by
    simp [hσ, ha]; omega
  have := SEforLn1_STKI_rotate sz n hE hτ k _ _ hlen
  rw [hrot] at this
  change ‖sz.STKI n E τ ⟨σ.take k ++ σ.drop (l' - 1), a.take (k - 1) ++ x :: a.drop (l' - 1)⟩‖ = _
  rw [← this, hσ₂, ha₂]

/-- **`[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(m)}` by the Ward bound** (`3_5:1054-1061`): if `Σ_{a_l} |𝒦^{(l)}_{σ,a}| ≤ Kw` for all
`σ`, `a`, then `‖[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(m)}‖ ≤ W^d · m² · 2 · max|(𝓛-𝒦)^{(m-l+2)}| · Kw`: for each pair of cut edges
`k < l'` the two pieces have lengths summing to `m + 2`; the `𝒦`-piece is summed over its glued label
(column or row sums of `S^{(B)}`). -/
private theorem SEforLn1_det_ksim (n : ℕ) {E τ : ℝ} (hE : |E| < 2) (hτ : τ ∈ Set.Ico (0 : ℝ) 1)
    (ω : sz.SeqΩ) {m l : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {Kw : ℝ}
    (hKw : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n E τ ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤ Kw) :
    ‖sz.STksimLK n E τ ω l ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) ^ 2 * (2 * (STmaxLK sz n E τ (m + 2 - l) ω * Kw))) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set I : LoopIdx (Zd d (sz.L n)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hlen : I.length = m := by simp [hI, LoopIdx.length]
  have hσl : (List.ofFn σ).length = m := by simp
  have hal : (List.ofFn a).length = m := by simp
  set M := STmaxLK sz n E τ (m + 2 - l) ω with hM
  have hM0 : 0 ≤ M := SEforLn1_STmaxLK_nonneg sz n E τ _ ω
  have hKw0 : 0 ≤ Kw := (Finset.sum_nonneg fun x _ => norm_nonneg _).trans (hKw (fun _ => true) (fun _ => 0))
  have hMK : 0 ≤ M * Kw := mul_nonneg hM0 hKw0
  unfold STksimLK
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
          sz.STLKI n E τ ω (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
            sz.STKI n E τ (I.cutGlueR k l' y)
        else 0)‖ ≤ M * Kw := by
    by_cases hc : l' - k + 1 = l
    · have hc' : ∀ y, (I.cutGlueR k l' y).length = l := fun y => (hlenR y).trans hc
      simp only [hc', ite_true, norm_mul]
      refine (SEforLn1_sum_glue_left sz n (fun x => ‖sz.STLKI n E τ ω (I.cutGlueL k l' x)‖)
        (fun y => ‖sz.STKI n E τ (I.cutGlueR k l' y)‖) (M := M) (fun x => ?_)
        (fun y => norm_nonneg _)).trans ?_
      · refine (SEforLn1_norm_STLKI_le sz n E τ ω _ (hwfL x)).trans (le_of_eq ?_)
        rw [hM, hlenL x]; congr 1; omega
      · exact mul_le_mul_of_nonneg_left
          (SEforLn1_sum_cutGlueR_K sz n hKw (List.ofFn σ) (List.ofFn a) hσl hal hk.1 hl'.1 hl'.2 hc) hM0
    · have hc' : ∀ y, ¬ ((I.cutGlueR k l' y).length = l) := fun y h => hc ((hlenR y).symm.trans h)
      simp only [hc', ite_false, norm_zero, Finset.sum_const_zero]
      exact hMK
  have hS2 : ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
      ‖(if (I.cutGlueL k l' x).length = l then
          sz.STKI n E τ (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
            sz.STLKI n E τ ω (I.cutGlueR k l' y)
        else 0)‖ ≤ M * Kw := by
    by_cases hc : k + m - l' + 1 = l
    · have hc' : ∀ x, (I.cutGlueL k l' x).length = l := fun x => (hlenL x).trans hc
      simp only [hc', ite_true, norm_mul]
      refine (SEforLn1_sum_glue_right sz n (fun x => ‖sz.STKI n E τ (I.cutGlueL k l' x)‖)
        (fun y => ‖sz.STLKI n E τ ω (I.cutGlueR k l' y)‖) (M := M) (fun y => ?_)
        (fun x => norm_nonneg _)).trans ?_
      · refine (SEforLn1_norm_STLKI_le sz n E τ ω _ (hwfR y)).trans (le_of_eq ?_)
        rw [hM, hlenR y]; congr 1; omega
      · exact mul_le_mul_of_nonneg_left
          (SEforLn1_sum_cutGlueL_K sz n hE hτ hKw (List.ofFn σ) (List.ofFn a) hσl hal hk.1 hl'.1 hl'.2 hc) hM0
    · have hc' : ∀ x, ¬ ((I.cutGlueL k l' x).length = l) := fun x h => hc ((hlenL x).symm.trans h)
      simp only [hc', ite_false, norm_zero, Finset.sum_const_zero]
      exact hMK
  calc ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ((if (I.cutGlueR k l' y).length = l then
            sz.STLKI n E τ ω (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
              sz.STKI n E τ (I.cutGlueR k l' y)
          else 0) +
         (if (I.cutGlueL k l' x).length = l then
            sz.STKI n E τ (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
              sz.STLKI n E τ ω (I.cutGlueR k l' y)
          else 0))‖
      ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          (‖(if (I.cutGlueR k l' y).length = l then
            sz.STLKI n E τ ω (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
              sz.STKI n E τ (I.cutGlueR k l' y)
          else 0)‖ +
          ‖(if (I.cutGlueL k l' x).length = l then
            sz.STKI n E τ (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
              sz.STLKI n E τ ω (I.cutGlueR k l' y)
          else 0)‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => norm_add_le _ _))
    _ ≤ M * Kw + M * Kw := by
        simp only [Finset.sum_add_distrib]
        exact add_le_add hS1 hS2
    _ = 2 * (M * Kw) := by ring

/-! ## 6. Part (2): `(eq:KsimL-K)` -/

/-- The exponent count of part (2): `W (K (2 (M (a ((W η)⁻¹ B^{l-2}))))) ≤ a² (B^k/η) Ξ` for `2K ≤ a`,
`M ≤ B^{k+2-l} Ξ`, `2 ≤ l ≤ k + 2`. -/
private theorem SEforLn1_arith2 {W K a B η M Ξ : ℝ} {k l : ℕ} (hl : 2 ≤ l) (hlk : l ≤ k + 2)
    (hW : 0 < W) (hK : 2 * K ≤ a) (ha : 0 ≤ a) (hB : 0 < B) (hη : 0 < η) (hM0 : 0 ≤ M)
    (hM : M ≤ B ^ (k + 2 - l) * Ξ) (hΞ : 0 ≤ Ξ) :
    W * (K * (2 * (M * (a * ((W * η)⁻¹ * B ^ (l - 2)))))) ≤ a * a * (B ^ k / η * Ξ) := by
  have hBk : B ^ k = B ^ (k + 2 - l) * B ^ (l - 2) := by
    rw [← pow_add]; congr 1; omega
  have hη' : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
  have hBp : 0 ≤ B ^ (l - 2) := by positivity
  calc W * (K * (2 * (M * (a * ((W * η)⁻¹ * B ^ (l - 2))))))
      = (2 * K) * a * η⁻¹ * (M * B ^ (l - 2)) := by field_simp
    _ ≤ a * a * η⁻¹ * ((B ^ (k + 2 - l) * Ξ) * B ^ (l - 2)) := by
        gcongr
    _ = a * a * (B ^ k / η * Ξ) := by rw [hBk]; field_simp

/-- The core of part (2), for an abstract energy sequence `E` with `|E n| < 2`, `0 ≤ s ≤ t < 1`, from the
uniform `𝒦`-loop Ward bound `(wardineq_K)` at every length `≥ 2`. -/
private theorem SEforLn1_part2_core {E s t : ℕ → ℝ} (hN : sz.SizeTendsto) (hE : ∀ n, |E n| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hKw : ∀ l : ℕ, 2 ≤ l →
      Prec sz (U := fun n => TimeIcc s t n × (Fin l → Bool) × (Fin (l - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖STKI sz n (E n) (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ *
          (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)))
    (k : ℕ) (l : ℕ) (hl3 : 3 ≤ l) (hlk : l ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STksimLK sz n (E n) (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        STXiLK sz n (E n) (p.1 : ℝ) (k - l + 2) ω) := by
  have hsize := tendsto_size sz hN
  have hK := hKw l (by omega)
  unfold Prec at hK ⊢
  refine SEforLn1_of_subset hK (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  filter_upwards [hsize.eventually (eventually_le_rpow (2 * (k : ℝ) ^ 2) (half_pos hτ))] with n hkN
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 n).trans p.1.2.1
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 n)
  have hB : 0 < sz.Bctl n (p.1 : ℝ) := st_Bctl_pos sz hu1
  have hη : 0 < etaT (E n) (p.1 : ℝ) := etaT_pos (hE n) hu1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hNa : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKw' : ∀ (σ' : Fin l → Bool) (a' : Fin (l - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖sz.STKI n (E n) (p.1 : ℝ) ⟨List.ofFn σ', List.ofFn a' ++ [x]⟩‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (l - 2)) :=
    fun σ' a' => hno (p.1, σ', a')
  have hd1 := SEforLn1_det_ksim sz n (hE n) ⟨hu0, hu1⟩ ω p.2.1 p.2.2 hKw'
  have hM := SEforLn1_maxLK_le sz n (E n) (p.1 : ℝ) ω (k + 2 - l) hB
  have hfin := SEforLn1_arith2 (k := k) (l := l) (K := (k : ℝ) ^ 2)
    (a := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (B := sz.Bctl n (p.1 : ℝ)) (η := etaT (E n) (p.1 : ℝ))
    (M := STmaxLK sz n (E n) (p.1 : ℝ) (k + 2 - l) ω)
    (Ξ := STXiLK sz n (E n) (p.1 : ℝ) (k + 2 - l) ω) (by omega) (by omega) hW (by linarith) hNa hB hη
    (SEforLn1_STmaxLK_nonneg sz n _ _ _ ω) (by simpa using hM) (SEforLn1_XiLK_nonneg sz n _ _ ω _ hB)
  rw [UnifDetDom.rpow_half_mul_rpow_half _ hτ, show k + 2 - l = k - l + 2 by omega] at hfin
  rw [show k + 2 - l = k - l + 2 by omega] at hd1
  exact absurd hp (not_lt.2 (hd1.trans hfin))

/-- **Part (2) of `lem:SEforLn`, `(eq:KsimL-K)`** (`3_5:1028-1034`, proof `3_5:1054-1061`): along the flow `STFlow`
with `0 ≤ s < t ≤ lemT z`, for every `k ≥ 2` and `3 ≤ l ≤ k`,
`max_{σ,a} |[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})^k η_u⁻¹ Ξ̂^{𝓛-𝒦}_{u,k-l+2}`, uniformly in
`u ∈ [s_n, t_n]`.  The input is the uniform `𝒦`-loop Ward bound `(wardineq_K)`, `stKward_timeIcc`, which
needs no hypothesis beyond the flow (`3 ≤ d`, `0 < κ`).  The conclusion is the second conjunct of
`STSEforLnConcl sz (STflowE z) s t` at `k`. -/
theorem stSEforLn_part2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (k : ℕ) :
    ∀ l : ℕ, 3 ≤ l → l ≤ k →
      Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STksimLK sz n (STflowE z n) (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (STflowE z n) (p.1 : ℝ) *
          STXiLK sz n (STflowE z n) (p.1 : ℝ) (k - l + 2) ω) := by
  intro l hl3 hlk
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hflow.1
  have him := SEforLn1_flow_im sz hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hE' : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => (abs_lemE_le (him n)).trans (hflow.2 n).1
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hn.1, hn.2⟩
  exact SEforLn1_part2_core sz hN (fun n => abs_lemE_lt_two (him n)) hs ht1
    (fun l hl => stKward_timeIcc sz hd hκ (inv_pos.2 h𝔡) hN (Eventually.of_forall hE') hlam hs
      (fun n => (hst n).le) ht1 l hl) k l hl3 hlk

end RBM.Gauss.Sizes

/-! ## 7. Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, so `N = (WL)^3` is
astronomically large but every window is a genuine one), the flow `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6)
(1/10) z0`, `s ≡ 0`, `t ≡ 1/16` (`1/16 ≤ lemT z0`): the window `[0, 1/16]` is a nondegenerate interval, the index
set `TimeIcc × (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n))` is nonempty, `k = 2` and `k = 3` (part (1)),
`(k, l) = (3, 3)` and `(4, 3)` (part (2)).  The uniform averaged local law `STAvgU` of part (1) is the output of
another gate (Step 2) and stays a hypothesis of the examples; every deterministic hypothesis (`3 ≤ d`, the flow,
`0 ≤ s`, `t ≤ lemT z`, `3 ≤ l ≤ k`, `0 < κ`) is discharged.  Part (2) has no stochastic hypothesis. -/

namespace RBM.Gauss.SEforLn1Inst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step34Inst

/-- The index set of the instances is nonempty at every size index: window point `0 ∈ [0, 1/16]`, charges
`(+, +, +)`, labels `0`. -/
example (n : ℕ) :
    Nonempty (TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n))) :=
  ⟨⟨0, by simp [sInst, tInst]⟩, fun _ => true, fun _ => 0⟩

/-- The indices `(n₁, n₂)` of `lem:SEforLn` (1) at `k = 2` and `k = 3`. -/
example : STn12E 2 = (1, 3) := by decide
example : STn12E 3 = (3, 3) := by decide

/-- **`stSEforLn_part1` at `k = 2`**, `(n₁, n₂) = (1, 3)`. -/
example (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STegt sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 2 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 1 ω * STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω) ^
          (1 / 2 : ℝ)) :=
  stSEforLn_part1 sz0 flow_z0 sz0_hs0 sz0_ht hAvg 2 le_rfl

/-- **`stSEforLn_part1` at `k = 3`**, `(n₁, n₂) = (3, 3)`. -/
example (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STegt sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 3 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω * STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω) ^
          (1 / 2 : ℝ)) :=
  stSEforLn_part1 sz0 flow_z0 sz0_hs0 sz0_ht hAvg 3 (by norm_num)

/-- **`stSEforLn_part2` at `(k, l) = (3, 3)`**: `Ξ̂^{𝓛-𝒦}_{2}`; no stochastic hypothesis. -/
example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STksimLK sz0 n (STflowE z0 n) (p.1 : ℝ) ω 3 ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 3 / etaT (STflowE z0 n) (p.1 : ℝ) *
        STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 2 ω) :=
  stSEforLn_part2 (by norm_num) sz0 (κ := 1 / 10) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht 3 3
    le_rfl le_rfl

/-- **`stSEforLn_part2` at `(k, l) = (4, 3)`**: `Ξ̂^{𝓛-𝒦}_{3}`. -/
example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 4 → Bool) × (Fin 4 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STksimLK sz0 n (STflowE z0 n) (p.1 : ℝ) ω 3 ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 4 / etaT (STflowE z0 n) (p.1 : ℝ) *
        STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω) :=
  stSEforLn_part2 (by norm_num) sz0 (κ := 1 / 10) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht 4 3
    le_rfl (by norm_num)

/-! ### The interface with `STSEforLnConcl`

The conclusions of the two theorems are, up to definitional unfolding, the first two conjuncts of
`STSEforLnConcl sz (STflowE z) s t` at `k`, so that S3-09 can assemble
`fun k hk => ⟨stSEforLn_part1 .., stSEforLn_part2 .., part3, part4⟩`. -/

example {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hAvg : STAvgU sz (STflowE z) s t) (hconcl : STSEforLnConcl sz (STflowE z) s t) (k : ℕ)
    (hk : 2 ≤ k) :
    stSEforLn_part1 sz hflow hs ht hAvg k hk = (hconcl k hk).1 := rfl

example {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (hconcl : STSEforLnConcl sz (STflowE z) s t) (k : ℕ)
    (hk : 2 ≤ k) :
    stSEforLn_part2 hd sz hκ hflow hs hst ht k = (hconcl k hk).2.1 := rfl

end RBM.Gauss.SEforLn1Inst
