/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.LemDecCalE
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.Split

/-!
# `lem_dec_calE`, third part, first half: the `𝓔 ⊗ 𝓔` bound, cut bounds (S5-06)

Ticket T2171 (S5-06, ST-4).  Port of `RBM2D/Path/LemDecCalEdif.lean` at commit `c9a24cf`
(cited `LemDecCalEdif:<line>`: pin `:52`, §1 Generic `:65-347`, §2 Facts `:349-500`,
§3 Loops `:502-521`, §4 Near `:523-692`, §5 Far `:694-1000`, `EE_le` `:1010`) to `d ≥ 3`.
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `res_deccalE_dif`
`3_5:2327-2334`, `defEOTE` `3_5:176`, `def_diffakn_k` `3_5:187`; the paper omits the proof
("a special case of [YY_25, Lemma 5.7]", `3_5:2338`).

Contents (namespace `RBM.Path`).  Vocabulary: `E2HypDif` (the merged `E2Hyp`, the floor
`(L^d W^{6d})² ≤ W^D`, the four- and six-loop bounds), `lossE2dif`, and the pinned statement
`LemDecCalE_dif` (proved by S5-07, `Path/LemDecCalEdif2`).  Bounds: `LemDecCalEdif_STeeM_le`
(the two cuts of `(ℰ⊗ℰ)^{M,(2)}`, every `σ`, every `a'`), `LemDecCalEdif_cut_near`,
`LemDecCalEdif_cut_far` (one cut six-loop, every `σ₀, σ₁`), `LemDecCalEdif_hyp_zero`
(`E2HypDif` at `M = 0`, `u = 0`), and the instances.

Differences from RBM2D (each forced by `d ≥ 3`, by `σ`, or by the premise bundle):
* the cut loop is `tr(A E₁ C E₂ A E₃ Aᴴ E₄ Cᴴ E₅ Aᴴ E₆)`, `A = G(σ₀)`, `C = G(σ₁)`, on `Vtx d L W`
  (RBM2D: `loopAB`, `σ₁ = σ̄₀` only); the glue `Aᴴ E₆ A` is Hermitian, the middle factor
  `C E₂ A E₃ Aᴴ E₄ Cᴴ` is bounded pointwise only; the edge pairs `(C, Cᴴ)`, `(A, Aᴴ)`, `(Aᴴ, A)`
  are AM-GM'd with (e7), which holds for both signs;
* `v = u` and `ℓ_u = 1` (`ilambda² ≤ 1 - u`): `ρ`, `η_u`, `tail_uv`, the shift `edge_u → edge_v`
  disappear; `ℓ*_u = (log W)^{3/2}`, the tail is the merged `tailTD`, the distance `zdistInf`;
* `L² W¹²` becomes `P = L^d W^{6d}` (floor `P² ≤ W^D`, in `E2HypDif`; `ℓ** = 4 (log P)²`); the
  constants of (e7) are `c_e = 2 · 9^d` (RBM2D `50`), the long-edge constant `3^{d+1}` (RBM2D
  `200`), `c_near = 32 · 3^{d+1}`;
* the four- and six-loop bounds are premises of `E2HypDif` (RBM2D: clause 2 of `goodSet`); the
  six-loop clause is used for `|A₁ - B|_∞ ≤ ℓ**`, the four-loop clause
  (`√(Λ M_u⁻³) ≤ Λ M_u^{-3/2}`) in the Cauchy-Schwarz step; the conjunct `J ≤ W` of `E2Hyp` is
  not used (it is inherited by `E2HypDif` only);
* the block resolvent entries are the fine entries read through `splitEquiv.symm`
  (`lemDecCalEdif_Gres_blockMat`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Path

open Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Green

/-! ## 0. Vocabulary: the bundle, the loss and the pinned statement -/

/-- **The hypothesis bundle of `res_deccalE_dif`** at `d ≥ 3` (one time `u`, the fine matrix `M`): the merged
`E2Hyp` (S5-05), the floor `(L^d W^{6d})² ≤ W^D` (the `d`-form of RBM2D's `L²W¹² ≤ W^{D/2}`, `LemDecCalE.lean:63`
at `c9a24cf`, with `W^{6d}` so that the near long-edge term needs no `J ≤ W`), and the four- and six-loop bounds
`|𝓛^{(k)}_{u,σ,a}| ≤ Λ (W^d(1-u))^{-(k-1)}` for every `σ`, `a` (clause 2 of RBM2D `goodSet` at `k = 4, 6`,
`GoodSet.lean:49`, used by RBM2D `LemDecCalEdif.lean:639, 708`; not in `E2Hyp`; S5-09 source: `STLmaxU`). -/
def E2HypDif {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  E2Hyp sz n E u D Λ K₀ J M ∧
    (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)),
      ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
    ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)),
      ‖STLM sz n E u M σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5

/-- The explicit loss of `lemDecCalE_dif`: the loss of `res_deccalE_lk` times
`729^d (1 + log(L^d W^{6d}))^{2d}` (the constant chain of the near and far parts is in the report). -/
def lossE2dif (d L W : ℕ) (Λ K₀ : ℝ) : ℝ :=
  lossE2 d L W Λ K₀ * ((729 : ℝ) ^ d * (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (6 * d))) ^ (2 * d))

/-- **`res_deccalE_dif`** (`3_5:2327-2334`), deterministic at one time `u`, every `σ ∈ {±}²`: for
`|a_i - a'_i|_∞ ≤ (log W)^{3/2}`,
`|(ℰ⊗ℰ)^{M,(2)}_{u,σ,a,a'}| ≤ lossE2dif · (1-u)⁻¹ [1(|a₁-a₂|_∞ ≤ 4(log W)^{3/2}) + (W^d|1-u|)^{-1/2} J³] T_{u,D}(|a₁-a₂|)²`;
the right side after the loss is the third conjunct of `STLemDecCalEConcl` (`Step5Pins.lean:178-186`) at
`J := Jst n u D`.  Proved by S5-07 (`Path/LemDecCalEdif2`). -/
def LemDecCalE_dif (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2HypDif sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (a i - a' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E u M σ a a'‖ ≤ lossE2dif d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ *
          ((if ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
                4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) *
          STtailTD sz n u D a ^ 2)

/-! ## 1. Generic algebra of the cut six-loop on the block-product index -/

section Generic

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The weight of `E_c` at `p`: `W^{-d}` on the block `c`, `0` elsewhere. -/
private def lemDecCalEdif_wt (c : Zd d L) (p : Vtx d L W) : ℝ :=
  if p.1 = c then ((W : ℝ) ^ d)⁻¹ else 0

private theorem lemDecCalEdif_wt_nonneg (c : Zd d L) (p : Vtx d L W) :
    0 ≤ lemDecCalEdif_wt c p := by
  unfold lemDecCalEdif_wt; split_ifs <;> positivity

private theorem lemDecCalEdif_Eblk_eq_diag (c : Zd d L) :
    Eblk d L W c = diagonal (fun p : Vtx d L W => ((lemDecCalEdif_wt c p : ℝ) : ℂ)) := by
  unfold Eblk
  congr 1
  funext p
  unfold lemDecCalEdif_wt
  split_ifs <;> simp

private theorem lemDecCalEdif_sum_wt (c : Zd d L) :
    ∑ p : Vtx d L W, lemDecCalEdif_wt c p = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp only [lemDecCalEdif_wt, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  · intro b _ hb
    simp [lemDecCalEdif_wt, hb]
  · simp

private theorem lemDecCalEdif_path2 (P H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (c : Zd d L)
    (p q : Vtx d L W) {t β : ℝ} (ht : 0 ≤ t)
    (h : ∀ y : Vtx d L W, y.1 = c → ‖P p y‖ * ‖H y q‖ * t ≤ β) :
    ‖(P * Eblk d L W c * H) p q‖ * t ≤ β := by
  rw [lemDecCalEdif_Eblk_eq_diag, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  have h1 : ‖∑ y, P p y * ((lemDecCalEdif_wt c y : ℝ) : ℂ) * H y q‖ ≤
      ∑ y, lemDecCalEdif_wt c y * (‖P p y‖ * ‖H y q‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (lemDecCalEdif_wt_nonneg c y)]
    nlinarith [norm_nonneg (P p y), norm_nonneg (H y q), lemDecCalEdif_wt_nonneg c y]
  calc ‖∑ y, P p y * ((lemDecCalEdif_wt c y : ℝ) : ℂ) * H y q‖ * t
      ≤ (∑ y, lemDecCalEdif_wt c y * (‖P p y‖ * ‖H y q‖)) * t :=
        mul_le_mul_of_nonneg_right h1 ht
    _ = ∑ y, lemDecCalEdif_wt c y * (‖P p y‖ * ‖H y q‖ * t) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun y _ => by ring
    _ ≤ ∑ y, lemDecCalEdif_wt c y * β := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases hy : y.1 = c
        · exact mul_le_mul_of_nonneg_left (h y hy) (lemDecCalEdif_wt_nonneg c y)
        · simp [lemDecCalEdif_wt, hy]
    _ = β := by rw [← Finset.sum_mul, lemDecCalEdif_sum_wt, one_mul]

/-- The cut six-loop `tr(A E₁ C E₂ A E₃ A' E₄ C' E₅ A' E₆)` (the `loopL` bracketing); at
`A = G(σ₀)`, `C = G(σ₁)`, `A' = G(σ̄₀)`, `C' = G(σ̄₁)` it is `𝓛⁶_{σ₀σ₁}`. -/
private def lemDecCalEdif_loop6 (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Zd d L) : ℂ :=
  trace (A * Eblk d L W c1 * (C * Eblk d L W c2 * (A * Eblk d L W c3 * (A' * Eblk d L W c4 *
    (C' * Eblk d L W c5 * (A' * Eblk d L W c6 * 1))))))

/-- The four-loop `tr(A E₁ A' E₆ A E₅ A' E₆)`. -/
private def lemDecCalEdif_loop4 (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ) (c1 c6 c5 : Zd d L) : ℂ :=
  trace (A * Eblk d L W c1 * (A' * Eblk d L W c6 * (A * Eblk d L W c5 * (A' * Eblk d L W c6 * 1))))

/-- Cyclic rotation of the six-loop by three steps. -/
private theorem lemDecCalEdif_loop6_rot (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Zd d L) :
    lemDecCalEdif_loop6 A C A' C' c1 c2 c3 c4 c5 c6 =
      lemDecCalEdif_loop6 A' C' A C c4 c5 c6 c1 c2 c3 := by
  unfold lemDecCalEdif_loop6
  simp only [Matrix.mul_one]
  rw [show A * Eblk d L W c1 * (C * Eblk d L W c2 * (A * Eblk d L W c3 *
      (A' * Eblk d L W c4 * (C' * Eblk d L W c5 * (A' * Eblk d L W c6))))) =
      (A * Eblk d L W c1 * C * Eblk d L W c2 * A * Eblk d L W c3) *
        (A' * Eblk d L W c4 * C' * Eblk d L W c5 * A' * Eblk d L W c6) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The middle factor `C E₂ A E₃ A' E₄ C'` (edges `c₁ → c₂ → c₃ → c₄ → c₅`). -/
private def lemDecCalEdif_mid (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c2 c3 c4 : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  C * Eblk d L W c2 * A * Eblk d L W c3 * A' * Eblk d L W c4 * C'

/-- The glue `X = A' E₆ A` (edges `c₅ → c₆ → c₁`). -/
private def lemDecCalEdif_glue (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ) (c6 : Zd d L) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  A' * Eblk d L W c6 * A

private theorem lemDecCalEdif_loop6_eq_sum (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Zd d L) :
    lemDecCalEdif_loop6 A C A' C' c1 c2 c3 c4 c5 c6 = ∑ p, ∑ q,
      ((lemDecCalEdif_wt c1 p : ℝ) : ℂ) * lemDecCalEdif_mid A C A' C' c2 c3 c4 p q *
        ((lemDecCalEdif_wt c5 q : ℝ) : ℂ) * lemDecCalEdif_glue A A' c6 q p := by
  have h : lemDecCalEdif_loop6 A C A' C' c1 c2 c3 c4 c5 c6 =
      trace ((Eblk d L W c1 * lemDecCalEdif_mid A C A' C' c2 c3 c4 * Eblk d L W c5) *
        lemDecCalEdif_glue A A' c6) := by
    unfold lemDecCalEdif_loop6 lemDecCalEdif_mid lemDecCalEdif_glue
    simp only [Matrix.mul_one]
    rw [show A * Eblk d L W c1 * (C * Eblk d L W c2 * (A * Eblk d L W c3 *
        (A' * Eblk d L W c4 * (C' * Eblk d L W c5 * (A' * Eblk d L W c6))))) =
        A * (Eblk d L W c1 * C * Eblk d L W c2 * A * Eblk d L W c3 * A' * Eblk d L W c4 * C' *
          Eblk d L W c5 * A' * Eblk d L W c6) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lemDecCalEdif_Eblk_eq_diag, lemDecCalEdif_Eblk_eq_diag, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

private theorem lemDecCalEdif_loop4_eq_sum (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c6 c5 : Zd d L) :
    lemDecCalEdif_loop4 A A' c1 c6 c5 = ∑ p, ∑ q,
      ((lemDecCalEdif_wt c1 p : ℝ) : ℂ) * lemDecCalEdif_glue A A' c6 p q *
        ((lemDecCalEdif_wt c5 q : ℝ) : ℂ) * lemDecCalEdif_glue A A' c6 q p := by
  have h : lemDecCalEdif_loop4 A A' c1 c6 c5 =
      trace ((Eblk d L W c1 * lemDecCalEdif_glue A A' c6 * Eblk d L W c5) *
        lemDecCalEdif_glue A A' c6) := by
    unfold lemDecCalEdif_loop4 lemDecCalEdif_glue
    simp only [Matrix.mul_one]
    rw [show A * Eblk d L W c1 * (A' * Eblk d L W c6 * (A * Eblk d L W c5 *
        (A' * Eblk d L W c6))) =
        A * (Eblk d L W c1 * A' * Eblk d L W c6 * A * Eblk d L W c5 * A' * Eblk d L W c6) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lemDecCalEdif_Eblk_eq_diag, lemDecCalEdif_Eblk_eq_diag, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

/-- Path bound for the middle factor. -/
private theorem lemDecCalEdif_mid_le (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c2 c3 c4 c5 : Zd d L) {α : ℝ}
    (h : ∀ x1 x2 x3 x4 x5 : Vtx d L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖C x1 x2‖ * ‖A x2 x3‖ * ‖A' x3 x4‖ * ‖C' x4 x5‖ ≤ α)
    (p q : Vtx d L W) (hp : p.1 = c1) (hq : q.1 = c5) :
    ‖lemDecCalEdif_mid A C A' C' c2 c3 c4 p q‖ ≤ α := by
  have h3 : ∀ y3 y4 : Vtx d L W, y3.1 = c3 → y4.1 = c4 →
      ‖(C * Eblk d L W c2 * A) p y3‖ * (‖A' y3 y4‖ * ‖C' y4 q‖) ≤ α := fun y3 y4 hy3 hy4 =>
    lemDecCalEdif_path2 C A c2 p y3 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun y2 hy2 => by
      have := h p y2 y3 y4 q hp hy2 hy3 hy4 hq
      calc ‖C p y2‖ * ‖A y2 y3‖ * (‖A' y3 y4‖ * ‖C' y4 q‖)
          = ‖C p y2‖ * ‖A y2 y3‖ * ‖A' y3 y4‖ * ‖C' y4 q‖ := by ring
        _ ≤ α := this)
  have h4 : ∀ y4 : Vtx d L W, y4.1 = c4 →
      ‖(C * Eblk d L W c2 * A * Eblk d L W c3 * A') p y4‖ * ‖C' y4 q‖ ≤ α := fun y4 hy4 =>
    lemDecCalEdif_path2 (C * Eblk d L W c2 * A) A' c3 p y4 (norm_nonneg _) (fun y3 hy3 => by
      have := h3 y3 y4 hy3 hy4
      calc ‖(C * Eblk d L W c2 * A) p y3‖ * ‖A' y3 y4‖ * ‖C' y4 q‖
          = ‖(C * Eblk d L W c2 * A) p y3‖ * (‖A' y3 y4‖ * ‖C' y4 q‖) := by ring
        _ ≤ α := this)
  have := lemDecCalEdif_path2 (C * Eblk d L W c2 * A * Eblk d L W c3 * A') C' c4 p q (t := 1)
    zero_le_one (fun y4 hy4 => by rw [mul_one]; exact h4 y4 hy4)
  simpa [lemDecCalEdif_mid] using this

/-- Pointwise bound for the glue. -/
private theorem lemDecCalEdif_glue_le (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c5 c6 c1 : Zd d L) {β : ℝ}
    (h : ∀ x5 x6 x1 : Vtx d L W, x5.1 = c5 → x6.1 = c6 → x1.1 = c1 →
      ‖A' x5 x6‖ * ‖A x6 x1‖ ≤ β)
    (q p : Vtx d L W) (hq : q.1 = c5) (hp : p.1 = c1) :
    ‖lemDecCalEdif_glue A A' c6 q p‖ ≤ β := by
  have := lemDecCalEdif_path2 A' A c6 q p (t := 1) zero_le_one (fun y hy => by
    rw [mul_one]; exact h q y p hq hy hp)
  simpa [lemDecCalEdif_glue] using this

/-- The first reduction: `‖loop‖ ≤ α Σ_{p,q} w₁(p) w₅(q) ‖X_{qp}‖`. -/
private theorem lemDecCalEdif_loop6_le_glue (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Zd d L) {α : ℝ}
    (h : ∀ x1 x2 x3 x4 x5 : Vtx d L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖C x1 x2‖ * ‖A x2 x3‖ * ‖A' x3 x4‖ * ‖C' x4 x5‖ ≤ α) :
    ‖lemDecCalEdif_loop6 A C A' C' c1 c2 c3 c4 c5 c6‖ ≤
      α * ∑ p, ∑ q, lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q *
        ‖lemDecCalEdif_glue A A' c6 q p‖ := by
  rw [lemDecCalEdif_loop6_eq_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (lemDecCalEdif_wt_nonneg c1 p),
    Real.norm_of_nonneg (lemDecCalEdif_wt_nonneg c5 q)]
  have hw1 := lemDecCalEdif_wt_nonneg (W := W) c1 p
  have hw5 := lemDecCalEdif_wt_nonneg (W := W) c5 q
  have hX := norm_nonneg (lemDecCalEdif_glue A A' c6 q p)
  by_cases hp : p.1 = c1
  · by_cases hq : q.1 = c5
    · have hm := lemDecCalEdif_mid_le A C A' C' c1 c2 c3 c4 c5 h p q hp hq
      have : lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q *
          ‖lemDecCalEdif_glue A A' c6 q p‖ * ‖lemDecCalEdif_mid A C A' C' c2 c3 c4 p q‖ ≤
          lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q * ‖lemDecCalEdif_glue A A' c6 q p‖ * α :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      nlinarith
    · simp [lemDecCalEdif_wt, hq]
  · simp [lemDecCalEdif_wt, hp]

/-- Weighted Cauchy–Schwarz: `(Σ w f)² ≤ Σ w f²` for weights `w ≥ 0` of total mass `1`. -/
private theorem lemDecCalEdif_wcs {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : (∑ i, w i * f i) ^ 2 ≤ ∑ i, w i * f i ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)
  have e1 : ∀ i, Real.sqrt (w i) * (Real.sqrt (w i) * f i) = w i * f i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw i)
  have e3 : ∀ i, (Real.sqrt (w i) * f i) ^ 2 = w i * f i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i)]
  simp only [e1, e2, e3, h1, one_mul] at this
  exact this

/-- Total mass of the product weight. -/
private theorem lemDecCalEdif_sum_wt_wt (c1 c5 : Zd d L) :
    ∑ p : Vtx d L W, ∑ q : Vtx d L W, lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q = 1 := by
  simp only [← Finset.mul_sum, lemDecCalEdif_sum_wt, mul_one]

/-- The glue of a Hermitian pair is Hermitian. -/
private theorem lemDecCalEdif_glue_herm (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ) (hAA : Aᴴ = A')
    (c6 : Zd d L) (p q : Vtx d L W) :
    lemDecCalEdif_glue A A' c6 p q = star (lemDecCalEdif_glue A A' c6 q p) := by
  have hBA : A'ᴴ = A := by rw [← hAA, Matrix.conjTranspose_conjTranspose]
  have hE : (Eblk d L W c6)ᴴ = Eblk d L W c6 := by
    rw [lemDecCalEdif_Eblk_eq_diag, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    simp
  have hX : (lemDecCalEdif_glue A A' c6)ᴴ = lemDecCalEdif_glue A A' c6 := by
    unfold lemDecCalEdif_glue
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hE, hAA, hBA, Matrix.mul_assoc]
  have := congrFun (congrFun hX p) q
  rw [Matrix.conjTranspose_apply] at this
  exact this.symm

/-- The four-loop is the weighted `ℓ²` mass of the glue. -/
private theorem lemDecCalEdif_loop4_eq (A A' : Matrix (Vtx d L W) (Vtx d L W) ℂ) (hAA : Aᴴ = A')
    (c1 c6 c5 : Zd d L) :
    lemDecCalEdif_loop4 A A' c1 c6 c5 =
      ((∑ p, ∑ q, lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q *
        ‖lemDecCalEdif_glue A A' c6 q p‖ ^ 2 : ℝ) : ℂ) := by
  rw [lemDecCalEdif_loop4_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [lemDecCalEdif_glue_herm A A' hAA c6 p q]
  have : star (lemDecCalEdif_glue A A' c6 q p) * lemDecCalEdif_glue A A' c6 q p =
      ((‖lemDecCalEdif_glue A A' c6 q p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  calc ((lemDecCalEdif_wt c1 p : ℝ) : ℂ) * star (lemDecCalEdif_glue A A' c6 q p) *
        ((lemDecCalEdif_wt c5 q : ℝ) : ℂ) * lemDecCalEdif_glue A A' c6 q p
      = ((lemDecCalEdif_wt c1 p : ℝ) : ℂ) * ((lemDecCalEdif_wt c5 q : ℝ) : ℂ) *
          (star (lemDecCalEdif_glue A A' c6 q p) * lemDecCalEdif_glue A A' c6 q p) := by ring
    _ = _ := by rw [this]; push_cast; ring

/-- **Glue at `c₆` with Cauchy–Schwarz**: for `Aᴴ = A'`, `‖loop‖ ≤ α √‖tr(A E₁ A' E₆ A E₅ A' E₆)‖`. -/
private theorem lemDecCalEdif_loop6_le_cs (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (hAA : Aᴴ = A') (c1 c2 c3 c4 c5 c6 : Zd d L) {α : ℝ} (hα0 : 0 ≤ α)
    (h : ∀ x1 x2 x3 x4 x5 : Vtx d L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖C x1 x2‖ * ‖A x2 x3‖ * ‖A' x3 x4‖ * ‖C' x4 x5‖ ≤ α) :
    ‖lemDecCalEdif_loop6 A C A' C' c1 c2 c3 c4 c5 c6‖ ≤
      α * Real.sqrt ‖lemDecCalEdif_loop4 A A' c1 c6 c5‖ := by
  refine (lemDecCalEdif_loop6_le_glue A C A' C' c1 c2 c3 c4 c5 c6 h).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hα0
  set S2 : ℝ := ∑ p, ∑ q, lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q *
    ‖lemDecCalEdif_glue A A' c6 q p‖ ^ 2 with hS2
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (lemDecCalEdif_wt_nonneg c1 p) (lemDecCalEdif_wt_nonneg c5 q))
      (sq_nonneg _)
  have h4 : ‖lemDecCalEdif_loop4 A A' c1 c6 c5‖ = S2 := by
    rw [lemDecCalEdif_loop4_eq A A' hAA, Complex.norm_real, Real.norm_of_nonneg hS20]
  rw [h4]
  have hcs := lemDecCalEdif_wcs (ι := Vtx d L W × Vtx d L W)
    (fun x => lemDecCalEdif_wt c1 x.1 * lemDecCalEdif_wt c5 x.2)
    (fun x => ‖lemDecCalEdif_glue A A' c6 x.2 x.1‖)
    (fun x => mul_nonneg (lemDecCalEdif_wt_nonneg c1 x.1) (lemDecCalEdif_wt_nonneg c5 x.2))
    (by rw [Fintype.sum_prod_type]; exact lemDecCalEdif_sum_wt_wt c1 c5)
  rw [Fintype.sum_prod_type (fun x : Vtx d L W × Vtx d L W =>
      lemDecCalEdif_wt c1 x.1 * lemDecCalEdif_wt c5 x.2 * ‖lemDecCalEdif_glue A A' c6 x.2 x.1‖),
    Fintype.sum_prod_type (fun x : Vtx d L W × Vtx d L W =>
      lemDecCalEdif_wt c1 x.1 * lemDecCalEdif_wt c5 x.2 *
        ‖lemDecCalEdif_glue A A' c6 x.2 x.1‖ ^ 2)] at hcs
  apply Real.le_sqrt_of_sq_le
  rw [hS2]
  exact hcs

/-- **Pointwise glue**: `‖loop‖ ≤ α β`. -/
private theorem lemDecCalEdif_loop6_le_pt (A C A' C' : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (c1 c2 c3 c4 c5 c6 : Zd d L) {α β : ℝ} (hα0 : 0 ≤ α)
    (h : ∀ x1 x2 x3 x4 x5 : Vtx d L W, x1.1 = c1 → x2.1 = c2 → x3.1 = c3 → x4.1 = c4 →
      x5.1 = c5 → ‖C x1 x2‖ * ‖A x2 x3‖ * ‖A' x3 x4‖ * ‖C' x4 x5‖ ≤ α)
    (hβ : ∀ x5 x6 x1 : Vtx d L W, x5.1 = c5 → x6.1 = c6 → x1.1 = c1 →
      ‖A' x5 x6‖ * ‖A x6 x1‖ ≤ β) :
    ‖lemDecCalEdif_loop6 A C A' C' c1 c2 c3 c4 c5 c6‖ ≤ α * β := by
  refine (lemDecCalEdif_loop6_le_glue A C A' C' c1 c2 c3 c4 c5 c6 h).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hα0
  calc ∑ p, ∑ q, lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q *
        ‖lemDecCalEdif_glue A A' c6 q p‖
      ≤ ∑ p : Vtx d L W, ∑ q : Vtx d L W, lemDecCalEdif_wt c1 p * lemDecCalEdif_wt c5 q * β := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        by_cases hp : p.1 = c1
        · by_cases hq : q.1 = c5
          · exact mul_le_mul_of_nonneg_left (lemDecCalEdif_glue_le A A' c5 c6 c1 hβ q p hq hp)
              (mul_nonneg (lemDecCalEdif_wt_nonneg c1 p) (lemDecCalEdif_wt_nonneg c5 q))
          · simp [lemDecCalEdif_wt, hq]
        · simp [lemDecCalEdif_wt, hp]
    _ = β := by simp only [← Finset.sum_mul, lemDecCalEdif_sum_wt_wt, one_mul]

end Generic

/-! ## 2. Bridges: the loops of `STLM` as `lemDecCalEdif_loop6/4`, entries on `Vtx`, `ℓ_u = 1` -/

section Bridge

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The cut six-loop `𝓛⁶_{σ₀σ₁}(c₁, …, c₆)` of `STLM` is `lemDecCalEdif_loop6` of the four block
resolvents (RBM2D `gloop6_eq` `:509`, now for every `σ₀, σ₁`). -/
private theorem lemDecCalEdif_STLM6 (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ0 σ1 : Bool)
    (c1 c2 c3 c4 c5 c6 : Zd d (sz.L n)) :
    STLM sz n E u M ![σ0, σ1, σ0, !σ0, !σ1, !σ0] ![c1, c2, c3, c4, c5, c6] =
      lemDecCalEdif_loop6 (greenBlk d (sz.L n) (sz.W n) E u M σ0)
        (greenBlk d (sz.L n) (sz.W n) E u M σ1) (greenBlk d (sz.L n) (sz.W n) E u M (!σ0))
        (greenBlk d (sz.L n) (sz.W n) E u M (!σ1)) c1 c2 c3 c4 c5 c6 := by
  simp [STLM, loopFine, loopM, lemDecCalEdif_loop6, greenBlk, List.ofFn_succ]

private theorem lemDecCalEdif_STLM4 (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (τ : Bool)
    (c1 c6 c5 : Zd d (sz.L n)) :
    STLM sz n E u M ![τ, !τ, τ, !τ] ![c1, c6, c5, c6] =
      lemDecCalEdif_loop4 (greenBlk d (sz.L n) (sz.W n) E u M τ)
        (greenBlk d (sz.L n) (sz.W n) E u M (!τ)) c1 c6 c5 := by
  simp [STLM, loopFine, loopM, lemDecCalEdif_loop4, greenBlk, List.ofFn_succ]

/-- `G(σ)ᴴ = G(σ̄)` for the block resolvent of a Hermitian `M`. -/
private theorem lemDecCalEdif_greenBlk_herm (hH : M.IsHermitian) (σ : Bool) :
    (greenBlk d (sz.L n) (sz.W n) E u M σ)ᴴ = greenBlk d (sz.L n) (sz.W n) E u M (!σ) := by
  have hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hH.submatrix _
  have hG := ST_Gres_false hHb (zt E u)
  cases σ
  · simp only [greenBlk, Bool.not_false]
    rw [hG, Matrix.conjTranspose_conjTranspose]
  · simp only [greenBlk, Bool.not_true]
    rw [hG]

/-- `Gres (blockMat M) z σ = (Gres M z σ)` read on `Vtx` through `splitEquiv.symm` (the text of the
`private` `expInv_Gres_submatrix`, `Evolution/ExpInv.lean:116`, with `inv_submatrix_equiv`). -/
private theorem lemDecCalEdif_Gres_blockMat {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (s : Bool) :
    Gres (blockMat d L W M) z s =
      (Gres M z s).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold Gres
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - w • 1).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    simp [blockMat, Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]

private theorem lemDecCalEdif_greenBlk_apply (p q : Vtx d (sz.L n) (sz.W n)) (σ : Bool) :
    greenBlk d (sz.L n) (sz.W n) E u M σ p q =
      Gres M (zt E u) σ ((splitEquiv d (sz.L n) (sz.W n)).symm p)
        ((splitEquiv d (sz.L n) (sz.W n)).symm q) := by
  unfold greenBlk
  rw [lemDecCalEdif_Gres_blockMat]
  rfl

/-- The block of `splitEquiv.symm p` is `p.1`. -/
private theorem lemDecCalEdif_STblk_symm (sz : Sizes d) (n : ℕ) (p : Vtx d (sz.L n) (sz.W n)) :
    STblk sz n ((splitEquiv d (sz.L n) (sz.W n)).symm p) = p.1 := by
  unfold STblk
  have h2 : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm p) = p :=
    (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply p
  rw [h2]

/-- `ℓ_u = 1` from `ilambda² ≤ 1 - u` (the merged `B45_ellT_eq_one` is `private`). -/
private theorem lemDecCalEdif_ellT_eq_one {L : ℕ} {g u : ℝ} (hL : 1 ≤ L) (hu : u < 1)
    (hgu : g ^ 2 ≤ 1 - u) : ellT L g u = 1 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hx : 0 < 1 - u := by linarith
  have hs : g ≤ Real.sqrt (1 - u) := Real.le_sqrt_of_sq_le hgu
  have hs0 : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 hx
  have h : g / Real.sqrt (1 - u) ≤ 1 := by rw [div_le_one hs0]; exact hs
  unfold ellT
  rw [abs_of_pos hx, max_eq_right h]
  exact min_eq_left hLr

private theorem lemDecCalEdif_ell (h : E2Hyp sz n E u D Λ K₀ J M) :
    ellT (sz.L n) (sz.lam n) u = 1 := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, -⟩ := h
  exact lemDecCalEdif_ellT_eq_one (by have := sz.three_le_L n; omega) hu1 hlamu

private theorem lemDecCalEdif_W_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
  exact_mod_cast sz.W_pos n

private theorem lemDecCalEdif_L_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 0 < sz.L n)

private theorem lemDecCalEdif_L_one (sz : Sizes d) (n : ℕ) : 1 ≤ sz.L n := by
  have := sz.three_le_L n; omega

private theorem lemDecCalEdif_W_one (sz : Sizes d) (n : ℕ) : 1 ≤ sz.W n := sz.W_pos n

/-- Basic numeric consequences of `E2Hyp`. -/
private theorem lemDecCalEdif_basic (h : E2Hyp sz n E u D Λ K₀ J M) :
    0 ≤ u ∧ u < 1 ∧ 1 ≤ Λ ∧ 1 ≤ J ∧ 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ M.IsHermitian := by
  obtain ⟨hd3, hE, hu0, hu1, hlam, hlamu, hlamW, hΛ, hK, hlog, hfloor, hH, h6, h78, h9, hJ1,
    -⟩ := h
  exact ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩

private theorem lemDecCalEdif_zd_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

/-- Symmetry of the `L^∞` distance. -/
private theorem lemDecCalEdif_zd_comm (d L : ℕ) [NeZero L] (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, lemDecCalEdif_zd_neg]

private theorem lemDecCalEdif_zd_tri (d L : ℕ) [NeZero L] (a b c : Zd d L) :
    (zdistInf d L (a - c) : ℝ) ≤ (zdistInf d L (a - b) : ℝ) + (zdistInf d L (b - c) : ℝ) := by
  have h : a - c = (a - b) + (b - c) := by abel
  have h2 : zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
    rw [h]
    unfold zdistInf
    refine Finset.sup_le fun i _ => ?_
    exact (zdist_add_le L ((a - b) i) ((b - c) i)).trans (add_le_add
      (Finset.le_sup (f := fun j => zdist L ((a - b) j)) (Finset.mem_univ i))
      (Finset.le_sup (f := fun j => zdist L ((b - c) j)) (Finset.mem_univ i)))
  exact_mod_cast h2

/-- (e7) for either sign, in the vertex form with the distance `|p.1 - q.1|_∞`, with the additive
`W^{-D}` folded (`W^{-D} ≤ T_{u,D}`, `J ≥ 1`) and the constant `c_e = 2 · 9^d`
(RBM2D `edge_u` `:427`: `50 = 2 · 25`). -/
private theorem lemDecCalEdif_edge (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Bool)
    (p q : Vtx d (sz.L n) (sz.W n))
    (hd : (1 / 8 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 2 ≤
      (zdistInf d (sz.L n) (p.1 - q.1) : ℝ)) :
    ‖greenBlk d (sz.L n) (sz.W n) E u M σ p q‖ ^ 2 ≤
      2 * 9 ^ d * Λ * J * tailTD d ((sz.W n : ℕ) : ℝ) u D
        ((zdistInf d (sz.L n) (p.1 - q.1) : ℝ) - 2) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h
  have hW0 := lemDecCalEdif_W_pos sz n
  have hell := lemDecCalEdif_ell h
  set r : ℝ := (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) with hr
  set T : ℝ := tailTD d ((sz.W n : ℕ) : ℝ) u D (r - 2) with hT
  have hT' : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ T := by
    have h1 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) ^ 2 * Real.exp (-Real.sqrt (r - 2)) :=
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    simp only [hT, tailTD]
    linarith
  have hT0 : 0 ≤ T := le_trans (Real.rpow_nonneg hW0.le _) hT'
  have key : ∀ x : ℝ, x ≤ 9 ^ d * Λ * (((sz.W n : ℕ) : ℝ) ^ (-D) + J * T) →
      x ≤ 2 * 9 ^ d * Λ * J * T := by
    intro x hx
    have h1 : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ J * T := hT'.trans (le_mul_of_one_le_left hT0 hJ1)
    have h9 : (0 : ℝ) ≤ 9 ^ d * Λ := by positivity
    nlinarith
  have hd' : (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
      ellT (sz.L n) (sz.lam n) u) + 2 ≤ r := by rw [hell]; linarith
  have hd'' : (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
      ellT (sz.L n) (sz.lam n) u) + 2 ≤
      (zdistInf d (sz.L n) (q.1 - p.1) : ℝ) := by
    rw [lemDecCalEdif_zd_comm] at hr; rw [hr] at hd'; exact hd'
  cases σ
  · -- `G(-)_{pq} = conj G(+)_{qp}`
    have hent : greenBlk d (sz.L n) (sz.W n) E u M false p q =
        star (greenBlk d (sz.L n) (sz.W n) E u M true q p) := by
      have hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian := hH.submatrix _
      have := congrFun (congrFun (ST_Gres_false hHb (zt E u)) p) q
      simpa [greenBlk, Matrix.conjTranspose_apply] using this
    rw [hent, norm_star, lemDecCalEdif_greenBlk_apply]
    have he := LemDecCalE_e7 h ((splitEquiv d (sz.L n) (sz.W n)).symm q)
      ((splitEquiv d (sz.L n) (sz.W n)).symm p)
      (by rw [lemDecCalEdif_STblk_symm, lemDecCalEdif_STblk_symm]; exact hd')
    rw [lemDecCalEdif_STblk_symm, lemDecCalEdif_STblk_symm] at he
    exact key _ he
  · rw [lemDecCalEdif_greenBlk_apply]
    have he := LemDecCalE_e7 h ((splitEquiv d (sz.L n) (sz.W n)).symm p)
      ((splitEquiv d (sz.L n) (sz.W n)).symm q)
      (by rw [lemDecCalEdif_STblk_symm, lemDecCalEdif_STblk_symm]; exact hd'')
    rw [lemDecCalEdif_STblk_symm, lemDecCalEdif_STblk_symm, ← lemDecCalEdif_zd_comm] at he
    exact key _ he

end Bridge

/-! ## 3. The near part: the split radius `ℓ** = 4 (log(L^d W^{6d}))²` -/

section Near

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- `log(L^d W^{6d}) ≥ 6 d log W` (RBM2D `logP_ge` `:534`). -/
private theorem lemDecCalEdif_logP_ge (sz : Sizes d) (n : ℕ) :
    (6 * (d : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) ≤
      Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
  have hL0 := lemDecCalEdif_L_pos sz n
  have hW0 := lemDecCalEdif_W_pos sz n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast lemDecCalEdif_L_one sz n
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h1 : 0 ≤ (d : ℝ) * Real.log ((sz.L n : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hL1)
  push_cast
  linarith

/-- `W^{-D} ≤ ((L^d W^{6d})²)⁻¹` from the floor (RBM2D `wD_le` `:545`). -/
private theorem lemDecCalEdif_wD_le (h : E2HypDif sz n E u D Λ K₀ J M) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
      ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2)⁻¹ := by
  have hfloor := h.2.1
  have hW0 := lemDecCalEdif_W_pos sz n
  have hL0 := lemDecCalEdif_L_pos sz n
  rw [Real.rpow_neg hW0.le]
  exact inv_anti₀ (by positivity) hfloor

/-- `log P ≥ 72` for `P = L^d W^{6d}` (`d ≥ 3`, `log W ≥ 4`). -/
private theorem lemDecCalEdif_logP_ge72 (h : E2Hyp sz n E u D Λ K₀ J M) :
    72 ≤ Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast h.1
  have := lemDecCalEdif_logP_ge sz n
  nlinarith

/-- The tail at the split radius: `T_{u,D}(ℓ** - 2) ≤ 4 P⁻²`, and `ℓ*/8 + 2 ≤ ℓ**`
(RBM2D `tail_Rss` `:560`; `ℓ_u = 1`). -/
private theorem lemDecCalEdif_tail_Rss (h : E2HypDif sz n E u D Λ K₀ J M) :
    tailTD d ((sz.W n : ℕ) : ℝ) u D
        (4 * Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 - 2) ≤
      4 * ((((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2)⁻¹ ∧
    (1 / 8 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 2 ≤
      4 * Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h.1
  have h2 := LemDecCalE_e2 h.1
  have hlp := lemDecCalEdif_logP_ge72 h.1
  have hW0 := lemDecCalEdif_W_pos sz n
  have hL0 := lemDecCalEdif_L_pos sz n
  have hWD := lemDecCalEdif_wD_le h
  set P : ℝ := ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) with hPdef
  have hP0 : 0 < P := by positivity
  set Lg : ℝ := Real.log P with hLg
  have hLg1 : 1 ≤ Lg := by linarith
  refine ⟨?_, ?_⟩
  · have hq : (2 * Lg - 1) ^ 2 ≤ 4 * Lg ^ 2 - 2 := by nlinarith
    have hs : 2 * Lg - 1 ≤ Real.sqrt (4 * Lg ^ 2 - 2) := Real.le_sqrt_of_sq_le hq
    have he : Real.exp (-Real.sqrt (4 * Lg ^ 2 - 2)) ≤ Real.exp 1 * (P ^ 2)⁻¹ := by
      have hP2 : P ^ 2 = Real.exp (2 * Lg) := by
        rw [show 2 * Lg = Lg + Lg by ring, Real.exp_add, hLg, Real.exp_log hP0]; ring
      rw [hP2, ← Real.exp_neg, ← Real.exp_add, Real.exp_le_exp]
      linarith
    have hM : ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) ^ 2 ≤ 1 := by
      rw [abs_of_pos (by linarith)]
      have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := h2.1
      have h3 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      have h4 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
        have : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith
        positivity
      nlinarith
    have he3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hPi : 0 ≤ (P ^ 2)⁻¹ := by positivity
    unfold tailTD
    have hexp0 := (Real.exp_pos (-Real.sqrt (4 * Lg ^ 2 - 2))).le
    calc ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹) ^ 2 * Real.exp (-Real.sqrt (4 * Lg ^ 2 - 2)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D)
        ≤ 1 * (Real.exp 1 * (P ^ 2)⁻¹) + (P ^ 2)⁻¹ := by gcongr
      _ ≤ 4 * (P ^ 2)⁻¹ := by nlinarith
  · have hlogW : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
    have h32 : Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := Real.log ((sz.W n : ℕ) : ℝ)) (by linarith)
        (show (3 : ℝ) / 2 ≤ ((2 : ℕ) : ℝ) by norm_num)
      rwa [Real.rpow_natCast] at this
    have hlogW' := lemDecCalEdif_logP_ge sz n
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by have := h.1.1; omega : 1 ≤ d)
    have hLg2 : Real.log ((sz.W n : ℕ) : ℝ) ^ 2 ≤ Lg ^ 2 :=
      pow_le_pow_left₀ hlogW (by nlinarith) 2
    nlinarith

/-- The block resolvent entries are bounded by `2Λ` (`LemDecCalE_e6`). -/
private theorem lemDecCalEdif_entry_le (h : E2Hyp sz n E u D Λ K₀ J M) (τ : Bool)
    (x y : Vtx d (sz.L n) (sz.W n)) :
    ‖greenBlk d (sz.L n) (sz.W n) E u M τ x y‖ ≤ 2 * Λ := by
  rw [lemDecCalEdif_greenBlk_apply]
  exact LemDecCalE_e6 h τ _ _

/-- **Near cut bound** (RBM2D `cut_near` `:615`) for the cut pattern `(A₁, A₂, B', A₂', A₁', B)` and
every `σ₀, σ₁`: if `|A₁ - B|_∞ ≤ ℓ**` the six-loop is `≤ Λ M_u⁻⁵` (the six-loop clause of `E2HypDif`);
otherwise the edge `B → A₁` is long and `‖loop‖ ≤ (2Λ)⁴ · 2Λ · 3^{d+1} Λ J P⁻¹`
(`(e7)` with `T(ℓ** - 2) ≤ 4 P⁻²`, `W^{-D} ≤ P⁻²`). -/
theorem LemDecCalEdif_cut_near (h : E2HypDif sz n E u D Λ K₀ J M) (σ₀ σ₁ : Bool)
    (A₁ A₂ A₁' A₂' B B' : Zd d (sz.L n)) :
    ‖STLM sz n E u M ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![A₁, A₂, B', A₂', A₁', B]‖ ≤
      Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5 *
          (if (zdistInf d (sz.L n) (A₁ - B) : ℝ) ≤
              4 * Real.log (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2
            then 1 else 0) +
        32 * 3 ^ (d + 1) * Λ ^ 6 * J *
          (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d))⁻¹ := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h.1
  have hW0 := lemDecCalEdif_W_pos sz n
  have hL0 := lemDecCalEdif_L_pos sz n
  obtain ⟨hT, hR⟩ := lemDecCalEdif_tail_Rss h
  have h2 := LemDecCalE_e2 h.1
  set P : ℝ := ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) with hPdef
  have hP0 : 0 < P := by positivity
  have hMu : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    have : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2.1]
    positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hsecond : 0 ≤ 32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹ := by positivity
  split_ifs with hn
  · have hk := h.2.2.2 ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![A₁, A₂, B', A₂', A₁', B]
    linarith
  · have hlong : ∀ x6 x1 : Vtx d (sz.L n) (sz.W n), x6.1 = B → x1.1 = A₁ →
        ‖greenBlk d (sz.L n) (sz.W n) E u M σ₀ x6 x1‖ ≤ 3 ^ (d + 1) * Λ * J * P⁻¹ := by
      intro x6 x1 h6 h1
      have hd : 4 * Real.log P ^ 2 < (zdistInf d (sz.L n) (x6.1 - x1.1) : ℝ) := by
        rw [h6, h1, lemDecCalEdif_zd_comm]; exact lt_of_not_ge hn
      have he := lemDecCalEdif_edge h.1 σ₀ x6 x1 (by linarith)
      have ht := LemDecCalE_tailT_anti (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D)
        (x := 4 * Real.log P ^ 2 - 2) (y := (zdistInf d (sz.L n) (x6.1 - x1.1) : ℝ) - 2)
        (by linarith)
      have hc : 0 ≤ 2 * 9 ^ d * Λ * J := by positivity
      have hΛJ : 1 ≤ Λ * J := by nlinarith
      have hsq : ‖greenBlk d (sz.L n) (sz.W n) E u M σ₀ x6 x1‖ ^ 2 ≤
          (3 ^ (d + 1) * Λ * J * P⁻¹) ^ 2 := by
        calc ‖greenBlk d (sz.L n) (sz.W n) E u M σ₀ x6 x1‖ ^ 2
            ≤ 2 * 9 ^ d * Λ * J * (4 * (P ^ 2)⁻¹) :=
              he.trans (mul_le_mul_of_nonneg_left (ht.trans hT) hc)
          _ ≤ (3 ^ (d + 1) * Λ * J * P⁻¹) ^ 2 := by
              have e3 : ((3 : ℝ) ^ (d + 1)) ^ 2 = 9 * 9 ^ d := by
                rw [← pow_mul, mul_comm, pow_mul]; norm_num; ring
              have hPi : 0 ≤ (P ^ 2)⁻¹ := by positivity
              have e : (3 ^ (d + 1) * Λ * J * P⁻¹) ^ 2 = (9 * 9 ^ d) * (Λ * J) ^ 2 * (P ^ 2)⁻¹ := by
                rw [show (3 ^ (d + 1) * Λ * J * P⁻¹) = (3 ^ (d + 1)) * (Λ * J) * P⁻¹ by ring,
                  mul_pow, mul_pow, inv_pow, e3]
              rw [e]
              have h9 : (0 : ℝ) ≤ 9 ^ d * (P ^ 2)⁻¹ := by positivity
              nlinarith [mul_nonneg h9 (sub_nonneg.2 hΛJ), mul_nonneg h9 (mul_nonneg
                (sub_nonneg.2 hΛJ) (sub_nonneg.2 hΛJ))]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    have hle := lemDecCalEdif_entry_le h.1
    have hα : ∀ x1 x2 x3 x4 x5 : Vtx d (sz.L n) (sz.W n), x1.1 = A₁ → x2.1 = A₂ → x3.1 = B' →
        x4.1 = A₂' → x5.1 = A₁' →
        ‖greenBlk d (sz.L n) (sz.W n) E u M σ₁ x1 x2‖ *
          ‖greenBlk d (sz.L n) (sz.W n) E u M σ₀ x2 x3‖ *
          ‖greenBlk d (sz.L n) (sz.W n) E u M (!σ₀) x3 x4‖ *
          ‖greenBlk d (sz.L n) (sz.W n) E u M (!σ₁) x4 x5‖ ≤ (2 * Λ) ^ 4 := by
      intro x1 x2 x3 x4 x5 _ _ _ _ _
      have h1 := hle σ₁ x1 x2
      have h2 := hle σ₀ x2 x3
      have h3 := hle (!σ₀) x3 x4
      have h4 := hle (!σ₁) x4 x5
      calc _ ≤ (2 * Λ) * (2 * Λ) * (2 * Λ) * (2 * Λ) := by gcongr
        _ = (2 * Λ) ^ 4 := by ring
    have hβ : ∀ x5 x6 x1 : Vtx d (sz.L n) (sz.W n), x5.1 = A₁' → x6.1 = B → x1.1 = A₁ →
        ‖greenBlk d (sz.L n) (sz.W n) E u M (!σ₀) x5 x6‖ *
          ‖greenBlk d (sz.L n) (sz.W n) E u M σ₀ x6 x1‖ ≤
          2 * Λ * (3 ^ (d + 1) * Λ * J * P⁻¹) := by
      intro x5 x6 x1 _ h6 h1
      exact mul_le_mul (hle _ _ _) (hlong x6 x1 h6 h1) (norm_nonneg _) (by positivity)
    rw [lemDecCalEdif_STLM6]
    have := lemDecCalEdif_loop6_le_pt _ _ _ _ A₁ A₂ B' A₂' A₁' B (by positivity) hα hβ
    calc _ ≤ (2 * Λ) ^ 4 * (2 * Λ * (3 ^ (d + 1) * Λ * J * P⁻¹)) := this
      _ = 32 * 3 ^ (d + 1) * Λ ^ 6 * J * P⁻¹ := by ring
      _ ≤ _ := by linarith

end Near

/-! ## 4. The far part: the glue at `B` or at `B'` and Cauchy–Schwarz with the four-loop -/

section Far

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E u D Λ K₀ J : ℝ}
  {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- The combined shift: `T_{u,D}(y) ≤ e² e^{2Y} T_{u,D}(x)` for `y ≥ x - 4 - 4ℓ*`, `Y = (log W)^{3/4}`
(RBM2D `shiftS` `:455`, at `v = u`, `ℓ_u = 1`). -/
private theorem lemDecCalEdif_shift (sz : Sizes d) (n : ℕ) (u D : ℝ) {x y : ℝ}
    (hy : x - 4 - 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ y) :
    tailTD d ((sz.W n : ℕ) : ℝ) u D y ≤
      Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
        tailTD d ((sz.W n : ℕ) : ℝ) u D x := by
  have hW0 := lemDecCalEdif_W_pos sz n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast lemDecCalEdif_W_one sz n
  have h1 : tailTD d ((sz.W n : ℕ) : ℝ) u D y ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D
      ((x - 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) - 4) :=
    LemDecCalE_tailT_anti (by linarith)
  have h2 := LemDecCalE_tailT_shift (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) (c := 4)
    hW0.le (by norm_num) (x - 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
  have h3 := LemDecCalE_e4c (d := d) (W := ((sz.W n : ℕ) : ℝ)) (u := u) (D := D) (C := 4) hW1
    (by norm_num) x
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4] at h2 h3
  have he : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
  calc tailTD d ((sz.W n : ℕ) : ℝ) u D y
      ≤ Real.exp 2 * tailTD d ((sz.W n : ℕ) : ℝ) u D
          (x - 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := h1.trans h2
    _ ≤ Real.exp 2 * (Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D x) := mul_le_mul_of_nonneg_left h3 he
    _ = _ := by ring

/-- AM–GM for two norms with a common squared bound. -/
private theorem lemDecCalEdif_pair_le {a b K : ℝ} (ha : a ^ 2 ≤ K) (hb : b ^ 2 ≤ K) :
    a * b ≤ K := by
  nlinarith [sq_nonneg (a - b)]

private theorem lemDecCalEdif_quad_le {a b c e P1 P2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (h25 : a * e ≤ P1) (h34 : b * c ≤ P2) : a * b * c * e ≤ P1 * P2 := by
  have h1 : a * b * c * e = (a * e) * (b * c) := by ring
  rw [h1]
  exact mul_le_mul h25 h34 (by positivity) ((mul_nonneg ha he).trans h25)

/-- The four-loop of the Cauchy–Schwarz step: `√‖𝓛_{(τ,τ̄,τ,τ̄)}‖ ≤ Λ M_u^{-3/2}`
(the four-loop clause of `E2HypDif`, `Λ ≥ 1`; RBM2D `sqrt_loop4_le` `:702`). -/
private theorem lemDecCalEdif_sqrt_loop4 (h : E2HypDif sz n E u D Λ K₀ J M) (τ : Bool)
    (c1 c6 c5 : Zd d (sz.L n)) :
    Real.sqrt ‖lemDecCalEdif_loop4 (greenBlk d (sz.L n) (sz.W n) E u M τ)
        (greenBlk d (sz.L n) (sz.W n) E u M (!τ)) c1 c6 c5‖ ≤
      Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ ((3 : ℝ) / 2) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h.1
  have hk := h.2.2.1 ![τ, !τ, τ, !τ] ![c1, c6, c5, c6]
  rw [lemDecCalEdif_STLM4] at hk
  have h2 := LemDecCalE_e2 h.1
  set m : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ with hm
  have hm0 : 0 ≤ m := by
    have : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2.1]
    positivity
  have hsq : (m ^ ((3 : ℝ) / 2)) ^ 2 = m ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0,
      show ((3 : ℝ) / 2 * ((2 : ℕ) : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ‖lemDecCalEdif_loop4 (greenBlk d (sz.L n) (sz.W n) E u M τ)
        (greenBlk d (sz.L n) (sz.W n) E u M (!τ)) c1 c6 c5‖
      ≤ Λ * m ^ 3 := hk
    _ ≤ Λ ^ 2 * m ^ 3 := by
        have : Λ ≤ Λ ^ 2 := by nlinarith
        have h0 : 0 ≤ m ^ 3 := by positivity
        nlinarith
    _ = (Λ * m ^ ((3 : ℝ) / 2)) ^ 2 := by rw [mul_pow, hsq]

/-- (e7) at the scale `u` with slack `2 + 4ℓ*` in the distance, for either sign and a block
resolvent entry (RBM2D `edge_v` `:475`, at `v = u`): `|G_{pq}|² ≤ c_e Λ J · e² e^{2Y} T(x)`,
`c_e = 2 · 9^d`. -/
private theorem lemDecCalEdif_edge_shift (h : E2Hyp sz n E u D Λ K₀ J M) (σ : Bool)
    (p q : Vtx d (sz.L n) (sz.W n)) (x : ℝ)
    (hd : (1 / 8 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 2 ≤
      (zdistInf d (sz.L n) (p.1 - q.1) : ℝ))
    (hx : x - 2 - 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      (zdistInf d (sz.L n) (p.1 - q.1) : ℝ)) :
    ‖greenBlk d (sz.L n) (sz.W n) E u M σ p q‖ ^ 2 ≤
      2 * 9 ^ d * Λ * J *
        (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D x := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h
  have h1 := lemDecCalEdif_edge h σ p q hd
  have h3 := lemDecCalEdif_shift sz n u D (x := x)
    (y := (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) - 2) (by linarith)
  have hc : 0 ≤ 2 * 9 ^ d * Λ * J := by positivity
  calc ‖greenBlk d (sz.L n) (sz.W n) E u M σ p q‖ ^ 2
      ≤ 2 * 9 ^ d * Λ * J * tailTD d ((sz.W n : ℕ) : ℝ) u D
          ((zdistInf d (sz.L n) (p.1 - q.1) : ℝ) - 2) := h1
    _ ≤ 2 * 9 ^ d * Λ * J * (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D x) := mul_le_mul_of_nonneg_left h3 hc
    _ = _ := by ring

/-- **Far cut bound** (RBM2D `cut_far` `:746`; `L6G6X`, `GGTLJ4G`) for the cut pattern
`(A₁, A₂, B', A₂', A₁', B)` with signs `(σ₀, σ₁, σ₀, σ̄₀, σ̄₁, σ̄₀)`, at `|A₁ - A₂|_∞ > 4ℓ*`.
Case (1) `|A₁ - B| ≤ |B - A₂|`: glue `A' E_B A` at `B`; case (2): glue at `B'` on the loop rotated by
three.  In (1a)/(2a) (`B` within `ℓ* + 1` of a label) Cauchy–Schwarz with the four-loop clause;
otherwise pointwise (e7) bounds.  `c_e = 2 · 9^d`, `S = e² e^{2Y}`, `Y = (log W)^{3/4}`. -/
theorem LemDecCalEdif_cut_far (h : E2HypDif sz n E u D Λ K₀ J M) (σ₀ σ₁ : Bool)
    (A₁ A₂ A₁' A₂' B B' : Zd d (sz.L n))
    (h1 : (zdistInf d (sz.L n) (A₁ - A₁') : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (h2 : (zdistInf d (sz.L n) (A₂ - A₂') : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (hB : (zdistInf d (sz.L n) (B - B') : ℝ) ≤ 1)
    (hd : 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) <
      (zdistInf d (sz.L n) (A₁ - A₂) : ℝ)) :
    ‖STLM sz n E u M ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![A₁, A₂, B', A₂', A₁', B]‖ ≤
      (2 * 9 ^ d * Λ * J) ^ 2 *
          (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (A₁ - A₂) : ℝ) ^ 2 *
          (Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ ((3 : ℝ) / 2)) *
          ((if (zdistInf d (sz.L n) (A₁ - B) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤
                Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) + 1 then 1 else 0)) +
        (2 * 9 ^ d * Λ * J) ^ 3 *
          (Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ^ 3 *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (A₁ - A₂) : ℝ) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (A₁ - B) : ℝ) *
          tailTD d ((sz.W n : ℕ) : ℝ) u D (zdistInf d (sz.L n) (B - A₂) : ℝ) := by
  obtain ⟨hu0, hu1, hΛ, hJ1, hlog, hH⟩ := lemDecCalEdif_basic h.1
  have hW0 := lemDecCalEdif_W_pos sz n
  have hlogW : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by linarith
  have hls : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
    have h1' : Real.log ((sz.W n : ℕ) : ℝ) ^ (1 : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at h1'
    linarith
  rw [lemDecCalEdif_STLM6]
  -- abbreviations
  set ls := Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hls_def
  set S := Real.exp 2 * Real.exp (2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) with hS
  set κ := 2 * 9 ^ d * Λ * J with hκ
  set R4 := Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ ((3 : ℝ) / 2) with hR4
  set GA := greenBlk d (sz.L n) (sz.W n) E u M with hGA
  have hS1 : 1 ≤ S := by
    have a := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    have b := Real.one_le_exp (show (0 : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) by
      have := Real.rpow_nonneg hlogW ((3 : ℝ) / 4)
      linarith)
    nlinarith
  have hκ0 : 0 ≤ κ := by positivity
  have hR40 : 0 ≤ R4 := by
    have h2' := LemDecCalE_e2 h.1
    have : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
      have : 0 < ((sz.W n : ℕ) : ℝ) ^ d * (1 - u) := by linarith [h2'.1]
      positivity
    positivity
  have hT0 : ∀ x : ℝ, 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) u D x := fun x => tailTD_nonneg hW0.le
  -- the edge bound
  have edge : ∀ (τ : Bool) (p q : Vtx d (sz.L n) (sz.W n)) (x : ℝ),
      ls / 8 + 2 ≤ (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) →
      x - 2 - 4 * ls ≤ (zdistInf d (sz.L n) (p.1 - q.1) : ℝ) →
      ‖GA τ p q‖ ^ 2 ≤ κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D x :=
    fun τ p q x ha hb => lemDecCalEdif_edge_shift h.1 τ p q x (by linarith) hb
  have shift : ∀ x y : ℝ, x - 4 - 4 * ls ≤ y →
      tailTD d ((sz.W n : ℕ) : ℝ) u D y ≤ S * tailTD d ((sz.W n : ℕ) : ℝ) u D x :=
    fun x y hxy => lemDecCalEdif_shift sz n u D hxy
  -- distances
  set dd := (zdistInf d (sz.L n) (A₁ - A₂) : ℝ) with hdd
  set bA1 := (zdistInf d (sz.L n) (A₁ - B) : ℝ) with hbA1
  set bA2 := (zdistInf d (sz.L n) (B - A₂) : ℝ) with hbA2
  have zc : ∀ a b : Zd d (sz.L n), (zdistInf d (sz.L n) (a - b) : ℝ) =
      (zdistInf d (sz.L n) (b - a) : ℝ) := fun a b => by rw [lemDecCalEdif_zd_comm d (sz.L n) a b]
  have c1 : (zdistInf d (sz.L n) (B - A₁) : ℝ) = bA1 := by rw [hbA1, zc]
  have c2 : (zdistInf d (sz.L n) (A₂ - B) : ℝ) = bA2 := by rw [hbA2, zc]
  have c3 := zc A₁' A₂'
  have c4 := zc A₂' A₂
  have c5 := zc B' A₂
  have c6 := zc B' B
  have c7 := zc A₂' B'
  have c8 := zc B A₂'
  have t1 := lemDecCalEdif_zd_tri d (sz.L n) A₁ A₁' A₂
  have t2 := lemDecCalEdif_zd_tri d (sz.L n) A₁' A₂' A₂
  have t3 := lemDecCalEdif_zd_tri d (sz.L n) B B' A₂
  have t4 := lemDecCalEdif_zd_tri d (sz.L n) B' A₂' A₂
  have t5 := lemDecCalEdif_zd_tri d (sz.L n) A₁ A₁' B
  have t6 := lemDecCalEdif_zd_tri d (sz.L n) A₁ B A₂
  have t7 := lemDecCalEdif_zd_tri d (sz.L n) A₂ A₂' B
  have t8 := lemDecCalEdif_zd_tri d (sz.L n) A₂ B' B
  have t9 := lemDecCalEdif_zd_tri d (sz.L n) A₂' B' B
  have t10 := lemDecCalEdif_zd_tri d (sz.L n) B B' A₂'
  have hd5 : dd - 2 * ls ≤ (zdistInf d (sz.L n) (A₂' - A₁') : ℝ) := by linarith
  -- the pair of long edges `C: A₁ → A₂`, `C': A₂' → A₁'` (both signs)
  have pair25 : ∀ (τ : Bool) (x1 x2 x4 x5 : Vtx d (sz.L n) (sz.W n)), x1.1 = A₁ → x2.1 = A₂ →
      x4.1 = A₂' → x5.1 = A₁' →
      ‖GA τ x1 x2‖ * ‖GA (!τ) x4 x5‖ ≤ κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd := by
    intro τ x1 x2 x4 x5 e1 e2 e4 e5
    refine lemDecCalEdif_pair_le (edge τ x1 x2 dd (by rw [e1, e2]; linarith)
      (by rw [e1, e2]; linarith))
      (edge (!τ) x4 x5 dd (by rw [e4, e5]; linarith) (by rw [e4, e5]; linarith))
  have hGherm : ∀ τ : Bool, (GA τ)ᴴ = GA (!τ) := fun τ => lemDecCalEdif_greenBlk_herm hH τ
  by_cases hcase : bA1 ≤ bA2
  · -- case (1): glue at `B`
    have hb2 : dd / 2 ≤ bA2 := by linarith
    have pair34 : ∀ x2 x3 x4 : Vtx d (sz.L n) (sz.W n), x2.1 = A₂ → x3.1 = B' → x4.1 = A₂' →
        ‖GA σ₀ x2 x3‖ * ‖GA (!σ₀) x3 x4‖ ≤ κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2 := by
      intro x2 x3 x4 e2 e3 e4
      refine lemDecCalEdif_pair_le (edge σ₀ x2 x3 bA2 (by rw [e2, e3]; linarith)
        (by rw [e2, e3]; linarith))
        (edge (!σ₀) x3 x4 bA2 (by rw [e3, e4]; linarith) (by rw [e3, e4]; linarith))
    have hα : ∀ x1 x2 x3 x4 x5 : Vtx d (sz.L n) (sz.W n), x1.1 = A₁ → x2.1 = A₂ → x3.1 = B' →
        x4.1 = A₂' → x5.1 = A₁' →
        ‖GA σ₁ x1 x2‖ * ‖GA σ₀ x2 x3‖ * ‖GA (!σ₀) x3 x4‖ * ‖GA (!σ₁) x4 x5‖ ≤
          (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
            (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2) := by
      intro x1 x2 x3 x4 x5 e1 e2 e3 e4 e5
      exact lemDecCalEdif_quad_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        (pair25 σ₁ x1 x2 x4 x5 e1 e2 e4 e5) (pair34 x2 x3 x4 e2 e3 e4)
    have hα0 : 0 ≤ (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
        (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2) := by
      have := hT0 dd; have := hT0 bA2; positivity
    by_cases hA : bA1 ≤ ls + 1 ∨ (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1
    · -- (1a)
      have hbA2' : dd - 4 - 4 * ls ≤ bA2 := by rcases hA with hA | hA <;> linarith
      have hsh := shift dd bA2 hbA2'
      have hcs := lemDecCalEdif_loop6_le_cs _ _ _ _ (hGherm σ₀) A₁ A₂ B' A₂' A₁' B hα0 hα
      have h4 := lemDecCalEdif_sqrt_loop4 h σ₀ A₁ B A₁'
      have hind : 1 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
          (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
        rcases hA with hA | hA
        · simp only [hA, ite_true]; split_ifs <;> norm_num
        · simp only [hA, ite_true]; split_ifs <;> norm_num
      have hsec : 0 ≤ κ ^ 3 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd *
          tailTD d ((sz.W n : ℕ) : ℝ) u D bA1 * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2 := by
        have := hT0 dd; have := hT0 bA1; have := hT0 bA2; positivity
      have hTd := hT0 dd
      calc ‖lemDecCalEdif_loop6 (GA σ₀) (GA σ₁) (GA (!σ₀)) (GA (!σ₁)) A₁ A₂ B' A₂' A₁' B‖
          ≤ (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
              (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2) *
              Real.sqrt ‖lemDecCalEdif_loop4 (GA σ₀) (GA (!σ₀)) A₁ B A₁'‖ := hcs
        _ ≤ (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
              (κ * S * (S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd)) * R4 := by
            apply mul_le_mul _ h4 (Real.sqrt_nonneg _) (by positivity)
            gcongr
        _ = κ ^ 2 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd ^ 2 * R4 * 1 := by ring
        _ ≤ κ ^ 2 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd ^ 2 * R4 *
            ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
              (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hind (by positivity)
        _ ≤ _ := by linarith
    · -- (1b)
      push Not at hA
      obtain ⟨hA1, hA1'⟩ := hA
      have hβ : ∀ x5 x6 x1 : Vtx d (sz.L n) (sz.W n), x5.1 = A₁' → x6.1 = B → x1.1 = A₁ →
          ‖GA (!σ₀) x5 x6‖ * ‖GA σ₀ x6 x1‖ ≤
            κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1 := by
        intro x5 x6 x1 e5 e6 e1
        refine lemDecCalEdif_pair_le (edge (!σ₀) x5 x6 bA1 (by rw [e5, e6]; linarith)
          (by rw [e5, e6]; linarith))
          (edge σ₀ x6 x1 bA1 (by rw [e6, e1]; linarith) (by rw [e6, e1]; linarith))
      have hpt := lemDecCalEdif_loop6_le_pt _ _ _ _ A₁ A₂ B' A₂' A₁' B hα0 hα hβ
      have hfirst : 0 ≤ κ ^ 2 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd ^ 2 * R4 *
          ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0)) := by
        have := hT0 dd
        have hi : 0 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
          split_ifs <;> norm_num
        positivity
      have heq : (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
          (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2) *
          (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1) =
          κ ^ 3 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd *
            tailTD d ((sz.W n : ℕ) : ℝ) u D bA1 * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2 := by ring
      linarith
  · -- case (2): glue at `B'`, on the loop rotated by three
    push Not at hcase
    have hb1 : dd / 2 < bA1 := by linarith
    rw [lemDecCalEdif_loop6_rot]
    have pair34' : ∀ x2 x3 x4 : Vtx d (sz.L n) (sz.W n), x2.1 = A₁' → x3.1 = B → x4.1 = A₁ →
        ‖GA (!σ₀) x2 x3‖ * ‖GA σ₀ x3 x4‖ ≤ κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1 := by
      intro x2 x3 x4 e2 e3 e4
      refine lemDecCalEdif_pair_le (edge (!σ₀) x2 x3 bA1 (by rw [e2, e3]; linarith)
        (by rw [e2, e3]; linarith))
        (edge σ₀ x3 x4 bA1 (by rw [e3, e4]; linarith) (by rw [e3, e4]; linarith))
    have hα : ∀ x1 x2 x3 x4 x5 : Vtx d (sz.L n) (sz.W n), x1.1 = A₂' → x2.1 = A₁' → x3.1 = B →
        x4.1 = A₁ → x5.1 = A₂ →
        ‖GA (!σ₁) x1 x2‖ * ‖GA (!σ₀) x2 x3‖ * ‖GA σ₀ x3 x4‖ * ‖GA σ₁ x4 x5‖ ≤
          (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
            (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1) := by
      intro x1 x2 x3 x4 x5 e1 e2 e3 e4 e5
      have p25 := pair25 σ₁ x4 x5 x1 x2 e4 e5 e1 e2
      have p25' : ‖GA (!σ₁) x1 x2‖ * ‖GA σ₁ x4 x5‖ ≤
          κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd := by rw [mul_comm]; exact p25
      exact lemDecCalEdif_quad_le (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
        p25' (pair34' x2 x3 x4 e2 e3 e4)
    have hα0 : 0 ≤ (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
        (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1) := by
      have := hT0 dd; have := hT0 bA1; positivity
    by_cases hA : bA2 ≤ ls + 1 ∨ (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1
    · -- (2a)
      have hbA1' : dd - 4 - 4 * ls ≤ bA1 := by rcases hA with hA | hA <;> linarith
      have hsh := shift dd bA1 hbA1'
      have hherm : (GA (!σ₀))ᴴ = GA σ₀ := by rw [hGherm, Bool.not_not]
      have hcs := lemDecCalEdif_loop6_le_cs _ _ _ _ hherm A₂' A₁' B A₁ A₂ B' hα0 hα
      have h4 := lemDecCalEdif_sqrt_loop4 h (!σ₀) A₂' B' A₂
      rw [Bool.not_not] at h4
      have hind : 1 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
          (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
          (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
        rcases hA with hA | hA
        · have : (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 := by linarith
          simp only [this, ite_true]; split_ifs <;> norm_num
        · simp only [hA, ite_true]; split_ifs <;> norm_num
      have hsec : 0 ≤ κ ^ 3 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd *
          tailTD d ((sz.W n : ℕ) : ℝ) u D bA1 * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2 := by
        have := hT0 dd; have := hT0 bA1; have := hT0 bA2; positivity
      have hTd := hT0 dd
      calc ‖lemDecCalEdif_loop6 (GA (!σ₀)) (GA (!σ₁)) (GA σ₀) (GA σ₁) A₂' A₁' B A₁ A₂ B'‖
          ≤ (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
              (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1) *
              Real.sqrt ‖lemDecCalEdif_loop4 (GA (!σ₀)) (GA σ₀) A₂' B' A₂‖ := hcs
        _ ≤ (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
              (κ * S * (S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd)) * R4 := by
            apply mul_le_mul _ h4 (Real.sqrt_nonneg _) (by positivity)
            gcongr
        _ = κ ^ 2 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd ^ 2 * R4 * 1 := by ring
        _ ≤ κ ^ 2 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd ^ 2 * R4 *
            ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
              (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
              (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0)) :=
            mul_le_mul_of_nonneg_left hind (by positivity)
        _ ≤ _ := by linarith
    · -- (2b)
      push Not at hA
      obtain ⟨hA2, hA2'⟩ := hA
      have hβ : ∀ x5 x6 x1 : Vtx d (sz.L n) (sz.W n), x5.1 = A₂ → x6.1 = B' → x1.1 = A₂' →
          ‖GA σ₀ x5 x6‖ * ‖GA (!σ₀) x6 x1‖ ≤
            κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2 := by
        intro x5 x6 x1 e5 e6 e1
        refine lemDecCalEdif_pair_le (edge σ₀ x5 x6 bA2 (by rw [e5, e6]; linarith)
          (by rw [e5, e6]; linarith))
          (edge (!σ₀) x6 x1 bA2 (by rw [e6, e1]; linarith) (by rw [e6, e1]; linarith))
      have hpt := lemDecCalEdif_loop6_le_pt _ _ _ _ A₂' A₁' B A₁ A₂ B' hα0 hα hβ
      have hfirst : 0 ≤ κ ^ 2 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd ^ 2 * R4 *
          ((if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0)) := by
        have := hT0 dd
        have hi : 0 ≤ (if bA1 ≤ ls + 1 then (1 : ℝ) else 0) +
            (if (zdistInf d (sz.L n) (A₁' - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂ - B) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf d (sz.L n) (A₂' - B) : ℝ) ≤ ls + 1 then 1 else 0) := by
          split_ifs <;> norm_num
        positivity
      have heq : (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D dd) *
          (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA1) *
          (κ * S * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2) =
          κ ^ 3 * S ^ 3 * tailTD d ((sz.W n : ℕ) : ℝ) u D dd *
            tailTD d ((sz.W n : ℕ) : ℝ) u D bA1 * tailTD d ((sz.W n : ℕ) : ℝ) u D bA2 := by ring
      linarith

end Far

/-! ## 5. The bridge from `(ℰ⊗ℰ)^{M,(2)}` to its two cut six-loops -/

section Cuts

variable {d : ℕ}

/-- **`EE_le`** (RBM2D `EE_le` `:1010`), for every `σ ∈ {±}²` and every `a'` (no hypothesis):
`|(ℰ⊗ℰ)^{M,(2)}_{σ,a,a'}| ≤ W^d Σ_{b,b'} |S^{(B)}_{bb'}| (|𝓛⁶_{σ₀σ₁}(a₀, a₁, b', a'₁, a'₀, b)| +
|𝓛⁶_{σ₁σ₀}(a₁, a₀, b', a'₀, a'₁, b)|)`: the cuts `k = 1, 2` of `STeeLoop` (at `a' = a` they are
`STeeLoop_one`, `STeeLoop_two`) read as `𝓛⁶` through `STLM_eq_STLIM`. -/
theorem LemDecCalEdif_STeeM_le (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a a' : Fin 2 → Zd d (sz.L n)) :
    ‖STeeM sz n E u M σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
      ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), ‖SB d (sz.L n) (sz.lam n) b b'‖ *
        (‖STLM sz n E u M ![σ 0, σ 1, σ 0, !σ 0, !σ 1, !σ 0] ![a 0, a 1, b', a' 1, a' 0, b]‖ +
          ‖STLM sz n E u M ![σ 1, σ 0, σ 1, !σ 1, !σ 0, !σ 1] ![a 1, a 0, b', a' 0, a' 1, b]‖) := by
  have e1 : ∀ b b' : Zd d (sz.L n),
      STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') 1 b b' =
        KLloopOf d (sz.L n) ![σ 0, σ 1, σ 0, !σ 0, !σ 1, !σ 0] ![a 0, a 1, b', a' 1, a' 0, b] := by
    intro b b'
    simp [STeeLoop, KLloopOf, List.ofFn_succ]
  have e2 : ∀ b b' : Zd d (sz.L n),
      STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') 2 b b' =
        KLloopOf d (sz.L n) ![σ 1, σ 0, σ 1, !σ 1, !σ 0, !σ 1] ![a 1, a 0, b', a' 0, a' 1, b] := by
    intro b b'
    simp [STeeLoop, KLloopOf, List.ofFn_succ]
  unfold STeeM
  have h12 : Finset.Icc 1 2 = {1, 2} := by decide
  rw [h12, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  simp only [e1, e2, ← STLM_eq_STLIM]
  have hw : ‖((sz.W n : ℕ) : ℂ) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by simp
  rw [norm_mul, hw]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
  rw [← mul_add, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

end Cuts

/-! ## 6. `E2HypDif` at `M = 0`, `u = 0` -/

section Zero

variable {d : ℕ}

/-- `G_0(+) = m I` at `H = 0`, `u = 0` (`z_0 = E + m`, `m (m + E) = -1`), for any finite index
(the text of the `private` `lemDecCalE_gres_zero_true`, `Path/LemDecCalE.lean:1208`). -/
private theorem lemDecCalEdif_gres_zero_true {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
    (hE : |E| ≤ 2) : Gres (0 : Matrix ι ι ℂ) (zt E 0) true = mE E • (1 : Matrix ι ι ℂ) := by
  have hm := mE_mul hE
  have hzt : zt E 0 = (E : ℂ) + mE E := by simp [zt]
  have hmz : (-((E : ℂ) + mE E))⁻¹ = mE E := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 : ℂ) * hm
  have hne : (E : ℂ) + mE E ≠ 0 := by
    intro h0
    rw [add_comm, h0, mul_zero] at hm
    norm_num at hm
  rw [Gres]
  simp only [↓reduceIte]
  rw [hzt, zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hne), hmz]

/-- `G_0(σ) = m(σ) I` at `H = 0`, `u = 0`, both signs. -/
private theorem lemDecCalEdif_gres_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ}
    (hE : |E| ≤ 2) (σ : Bool) :
    Gres (0 : Matrix ι ι ℂ) (zt E 0) σ = mSigma E σ • (1 : Matrix ι ι ℂ) := by
  cases σ
  · rw [ST_Gres_false Matrix.isHermitian_zero, lemDecCalEdif_gres_zero_true hE,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [mSigma]
  · simpa [mSigma] using lemDecCalEdif_gres_zero_true (ι := ι) hE

private theorem lemDecCalEdif_blockMat_zero {L W : ℕ} [NeZero L] [NeZero W] :
    blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ) = 0 := by
  ext i j; simp [blockMat]

/-- The product of `c_i · 1 · E_{a_i}` is diagonal. -/
private theorem lemDecCalEdif_prod_diag {L W : ℕ} [NeZero L] :
    ∀ {k : ℕ} (c : Fin k → ℂ) (a : Fin k → Zd d L),
      (List.ofFn fun i : Fin k =>
        (c i • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Eblk d L W (a i)).prod =
      diagonal fun x : Vtx d L W =>
        ∏ i : Fin k, (c i * if x.1 = a i then ((W : ℂ) ^ d)⁻¹ else 0)
  | 0, c, a => by simp
  | k + 1, c, a => by
      rw [List.ofFn_succ, List.prod_cons,
        lemDecCalEdif_prod_diag (fun i => c i.succ) (fun i => a i.succ)]
      have h0 : (c 0 • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Eblk d L W (a 0) =
          diagonal (fun x : Vtx d L W => c 0 * if x.1 = a 0 then ((W : ℂ) ^ d)⁻¹ else 0) := by
        rw [Matrix.smul_mul, Matrix.one_mul]
        unfold Eblk
        rw [← Matrix.diagonal_smul]
        rfl
      rw [h0, Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      rw [Fin.prod_univ_succ]

/-- `|tr ∏_i (c_i E_{a_i})| ≤ W^{-d(k-1)}` for `|c_i| = 1`, `k ≥ 1`. -/
private theorem lemDecCalEdif_norm_trace_diag {L W : ℕ} [NeZero L] [NeZero W] {k : ℕ}
    (c : Fin (k + 1) → ℂ) (hc : ∀ i, ‖c i‖ = 1) (a : Fin (k + 1) → Zd d L) :
    ‖trace (diagonal fun x : Vtx d L W =>
        ∏ i : Fin (k + 1), (c i * if x.1 = a i then ((W : ℂ) ^ d)⁻¹ else 0))‖ ≤
      (((W : ℝ) ^ d)⁻¹) ^ k := by
  rw [Matrix.trace_diagonal]
  have hWd : (0 : ℝ) < ((W : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hnorm : ∀ (x : Vtx d L W) (i : Fin (k + 1)),
      ‖c i * if x.1 = a i then ((W : ℂ) ^ d)⁻¹ else 0‖ = lemDecCalEdif_wt (a i) x := by
    intro x i
    rw [norm_mul, hc i, one_mul]
    unfold lemDecCalEdif_wt
    split_ifs <;> simp
  have hle : ∀ (x : Vtx d L W) (i : Fin (k + 1)), lemDecCalEdif_wt (a i) x ≤ ((W : ℝ) ^ d)⁻¹ := by
    intro x i
    unfold lemDecCalEdif_wt
    split_ifs
    · exact le_rfl
    · exact hWd.le
  calc ‖∑ x : Vtx d L W, ∏ i : Fin (k + 1), (c i * if x.1 = a i then ((W : ℂ) ^ d)⁻¹ else 0)‖
      ≤ ∑ x : Vtx d L W, ‖∏ i : Fin (k + 1), (c i * if x.1 = a i then ((W : ℂ) ^ d)⁻¹ else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x : Vtx d L W, lemDecCalEdif_wt (a 0) x * (((W : ℝ) ^ d)⁻¹) ^ k := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_prod, Fin.prod_univ_succ]
        simp only [hnorm]
        refine mul_le_mul_of_nonneg_left ?_ (lemDecCalEdif_wt_nonneg _ _)
        calc ∏ i : Fin k, lemDecCalEdif_wt (a i.succ) x
            ≤ ∏ _i : Fin k, ((W : ℝ) ^ d)⁻¹ :=
              Finset.prod_le_prod₀ (fun i _ => lemDecCalEdif_wt_nonneg _ _) (fun i _ => hle x _)
          _ = (((W : ℝ) ^ d)⁻¹) ^ k := by simp
    _ = (((W : ℝ) ^ d)⁻¹) ^ k := by rw [← Finset.sum_mul, lemDecCalEdif_sum_wt, one_mul]

/-- At `M = 0`, `u = 0`: `|𝓛^{(k+1)}_{0,σ,a}| ≤ W^{-dk}` (`G_0(σ) = m(σ) I`, `|m| = 1`,
`|tr ∏ E_{a_i}| ≤ W^{-dk}`). -/
private theorem lemDecCalEdif_STLM_zero_time (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    ‖STLM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ a‖ ≤
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ k := by
  unfold STLM loopFine loopM
  rw [lemDecCalEdif_blockMat_zero]
  have hf : (fun i : Fin (k + 1) =>
      Gres (0 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (zt E 0) (σ i) *
        Eblk d (sz.L n) (sz.W n) (a i)) = fun i =>
      (mSigma E (σ i) • (1 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ)) *
        Eblk d (sz.L n) (sz.W n) (a i) := by
    funext i
    rw [lemDecCalEdif_gres_zero hE]
  rw [hf, lemDecCalEdif_prod_diag (fun i => mSigma E (σ i)) a]
  exact lemDecCalEdif_norm_trace_diag _ (fun i => norm_mSigma hE _) a

private theorem lemDecCalEdif_sum_block_indicator {L W : ℕ} [NeZero L] (c : ℂ) (a : Zd d L) :
    ∑ p : Vtx d L W, (if p.1 = a then c else 0) = (W : ℂ) ^ d * c := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : Zd d L, ∑ y : Fin (W ^ d), (if (x, y).1 = a then c else 0) =
      if x = a then (W : ℂ) ^ d * c else 0 := by
    intro x
    by_cases hx : x = a
    · simp only [hx, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    · simp [hx]
  simp only [h]
  simp

/-- At `M = 0`, `u = 0`, all labels equal: `|𝓛^{(k+1)}_{0,σ,(c,…,c)}| = W^{-dk}` exactly. -/
private theorem lemDecCalEdif_STLM_zero_const (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (c : Zd d (sz.L n)) :
    ‖STLM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) σ
        (fun _ => c)‖ = ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ k := by
  unfold STLM loopFine loopM
  rw [lemDecCalEdif_blockMat_zero]
  have hf : (fun i : Fin (k + 1) =>
      Gres (0 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (zt E 0) (σ i) *
        Eblk d (sz.L n) (sz.W n) c) = fun i =>
      (mSigma E (σ i) • (1 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ)) *
        Eblk d (sz.L n) (sz.W n) c := by
    funext i
    rw [lemDecCalEdif_gres_zero hE]
  rw [hf, lemDecCalEdif_prod_diag (fun i => mSigma E (σ i)) (fun _ => c), Matrix.trace_diagonal]
  have h1 : ∀ x : Vtx d (sz.L n) (sz.W n),
      ∏ i : Fin (k + 1), (mSigma E (σ i) *
        if x.1 = c then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0) =
      (∏ i, mSigma E (σ i)) *
        (if x.1 = c then ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ (k + 1) else 0) := by
    intro x
    rw [Finset.prod_mul_distrib]
    congr 1
    by_cases hx : x.1 = c <;> simp [hx]
  simp only [h1, ← Finset.mul_sum]
  rw [lemDecCalEdif_sum_block_indicator, norm_mul]
  have hm : ‖∏ i, mSigma E (σ i)‖ = 1 := by
    rw [norm_prod]; exact Finset.prod_eq_one fun i _ => norm_mSigma hE _
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (sz.W_pos n).ne')
  rw [hm, one_mul]
  have e : ((sz.W n : ℕ) : ℂ) ^ d * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ (k + 1) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ k := by
    rw [pow_succ]; field_simp
  rw [e, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]

/-- **`E2HypDif` at `M = 0`, `u = 0`** (the matrix of time `0`, where `G = m I`): every conjunct
holds once the numeric premises do (those of `LemDecCalE_e2Hyp_zero`, with the floor
`(L^d W^{6d})² ≤ W^D`; `L^d W^{2d} ≤ W^D` follows).  The loop clauses hold exactly at `Λ ≥ 1`. -/
theorem LemDecCalEdif_hyp_zero (sz : Sizes d) (n : ℕ) {E D Λ K₀ J : ℝ} (hd : 3 ≤ d)
    (hE : |E| < 2) (hlam : 0 < sz.lam n) (hlam1 : sz.lam n ^ 2 ≤ 1)
    (hlamW : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hΛ : 1 ≤ Λ) (hK : 1 ≤ K₀)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hfloor : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
      ((sz.W n : ℕ) : ℝ) ^ D)
    (hJ : 1 ≤ J) (hJW : J ≤ ((sz.W n : ℕ) : ℝ)) :
    E2HypDif sz n E 0 D Λ K₀ J
      (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
  have hW0 := lemDecCalEdif_W_pos sz n
  have hL0 := lemDecCalEdif_L_pos sz n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast lemDecCalEdif_L_one sz n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast lemDecCalEdif_W_one sz n
  have hfloor2 : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ D := by
    refine le_trans ?_ hfloor
    have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
    have hWd : ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
      pow_le_pow_right₀ hW1 (by omega)
    have hW6 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d) := one_le_pow₀ hW1
    calc ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d)
        ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
          mul_le_mul_of_nonneg_left hWd (by positivity)
      _ ≤ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) *
            (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) := by
          have : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d) :=
            one_le_mul_of_one_le_of_one_le hLd hW6
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d)
            (by positivity : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d))]
      _ = _ := by ring
  refine ⟨LemDecCalE_e2Hyp_zero sz n hd hE hlam hlam1 hlamW hΛ hK hlog hfloor2 hJ hJW, hfloor,
    ?_, ?_⟩
  · intro σ a
    have h := lemDecCalEdif_STLM_zero_time sz n hE.le (k := 3) σ a
    have hpos : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 3 := by positivity
    calc _ ≤ _ := h
      _ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - 0))⁻¹) ^ 3 := by
          rw [sub_zero, mul_one]
          nlinarith
  · intro σ a
    have h := lemDecCalEdif_STLM_zero_time sz n hE.le (k := 5) σ a
    have hpos : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 5 := by positivity
    calc _ ≤ _ := h
      _ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - 0))⁻¹) ^ 5 := by
          rw [sub_zero, mul_one]
          nlinarith

end Zero

/-! ## 7. Nondegenerate instances at `d = 3` -/

section Instance

open RBM.Gauss.SizesInst RBM.Gauss.Step5Inst

private theorem lemDecCalEdif_inst_values :
    (sz0.L 1 = 8) ∧ (sz0.W 1 = 1024) ∧ (sz0.lam 1 = 1 / 4096) := by
  refine ⟨rfl, rfl, ?_⟩
  norm_num [sz0]

/-- **Instance (a)**: `E2HypDif` at `d = 3`, the preflight sequence `sz0` at `n = 1`
(`L = 8`, `W = 1024`, `lam = 1/4096`), `E = 1/2`, `u = 0`, `D = 38`, `Λ = K₀ = J = 1`, `M = 0`
(`L^d W^{6d})² = 2^{378} ≤ 2^{380} = W^D`). -/
theorem LemDecCalEdif_inst_a :
    E2HypDif sz0 1 (1 / 2) 0 38 1 1 1
      (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) := by
  obtain ⟨hL, hW, hlam⟩ := lemDecCalEdif_inst_values
  have hWc : ((sz0.W 1 : ℕ) : ℝ) = 1024 := by rw [hW]; norm_num
  have hLc : ((sz0.L 1 : ℕ) : ℝ) = 8 := by rw [hL]; norm_num
  refine LemDecCalEdif_hyp_zero sz0 1 (by norm_num) (by norm_num [abs_of_pos]) ?_ ?_ ?_ le_rfl
    le_rfl ?_ ?_ le_rfl ?_
  · rw [hlam]; norm_num
  · rw [hlam]; norm_num
  · rw [hlam, hWc]; norm_num
  · rw [hWc]
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 4
      _ ≤ (1024 : ℝ) := by norm_num
  · rw [hWc, hLc]
    have h : ((1024 : ℝ) ^ (38 : ℝ)) = (1024 : ℝ) ^ (38 : ℕ) := by
      rw [show (38 : ℝ) = ((38 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h]
    norm_num
  · rw [hWc]; norm_num

/-- **Instance (b)**: `E2HypDif` for the sequence `szCL` with `L_n → ∞` (`L = 2 · 24⁵`, `W = 2^24`,
`lam = 1`) at `n = 0`, `E = 1/2`, `u = 0`, `D = 42`, `Λ = K₀ = J = 1`, `M = 0`
(`(L^d W^{6d})² ≈ 2^{1007.55} ≤ 2^{1008} = W^D`). -/
theorem LemDecCalEdif_inst_b :
    E2HypDif szCL 0 (1 / 2) 0 42 1 1 1
      (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ) := by
  have hWc := szCL_W_real 0
  have hLc := szCL_L_real 0
  have hlam : szCL.lam 0 = 1 := rfl
  refine LemDecCalEdif_hyp_zero szCL 0 (by norm_num) (by norm_num [abs_of_pos]) ?_ ?_ ?_ le_rfl
    le_rfl ?_ ?_ le_rfl ?_
  · rw [hlam]; norm_num
  · rw [hlam]; norm_num
  · rw [hlam, hWc]; norm_num
  · rw [szCL_log_W]
    have := Real.log_two_gt_d9
    norm_num
    linarith
  · rw [hWc, hLc]
    have h : (((2 : ℝ) ^ (0 + 24)) ^ (42 : ℝ)) = ((2 : ℝ) ^ (0 + 24)) ^ (42 : ℕ) := by
      rw [show (42 : ℝ) = ((42 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h]
    norm_num
  · rw [hWc]; norm_num

/-- **Check (c)**: `LemDecCalEdif_STeeM_le` at the instance (a) data (`d = 3`, `L = 8`, `W = 1024`),
`σ = (+,+)`, `a = a' = (0, e₁)`, `e₁ = (1, 0, 0)`; the theorem has no hypothesis. -/
example :
    ‖STeeM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true]
        ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]‖ ≤
      ((sz0.W 1 : ℕ) : ℝ) ^ 3 *
        ∑ b : Zd 3 (sz0.L 1), ∑ b' : Zd 3 (sz0.L 1), ‖SB 3 (sz0.L 1) (sz0.lam 1) b b'‖ *
          (‖STLM sz0 1 (1 / 2) 0
              (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
              ![true, true, true, !true, !true, !true]
              ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1, b', Pi.single 0 1, 0, b]‖ +
            ‖STLM sz0 1 (1 / 2) 0
              (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
              ![true, true, true, !true, !true, !true]
              ![(Pi.single 0 1 : Zd 3 (sz0.L 1)), 0, b', 0, Pi.single 0 1, b]‖) :=
  LemDecCalEdif_STeeM_le sz0 1 (1 / 2) 0 _ ![true, true]
    ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]

/-- **Check (c′)**: `LemDecCalEdif_STeeM_le` at the instance (a) data with `a = a' = (0, 0)`, `σ = (+,+)`:
the bound holds with the right side `R` of the theorem, and `R > 0` (at `M = 0` the term `b = b' = 0` of the sum
is `|S^{(B)}_{00}| · 2 W^{-15}`: the six-loop with all labels equal is `W^{-5d}` exactly). -/
example :
    let R : ℝ := ((sz0.W 1 : ℕ) : ℝ) ^ 3 *
        ∑ b : Zd 3 (sz0.L 1), ∑ b' : Zd 3 (sz0.L 1), ‖SB 3 (sz0.L 1) (sz0.lam 1) b b'‖ *
          (‖STLM sz0 1 (1 / 2) 0
              (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
              ![true, true, true, !true, !true, !true]
              ![(0 : Zd 3 (sz0.L 1)), 0, b', 0, 0, b]‖ +
            ‖STLM sz0 1 (1 / 2) 0
              (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
              ![true, true, true, !true, !true, !true]
              ![(0 : Zd 3 (sz0.L 1)), 0, b', 0, 0, b]‖)
    0 < R ∧
    ‖STeeM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) ![true, true]
        ![(0 : Zd 3 (sz0.L 1)), 0] ![(0 : Zd 3 (sz0.L 1)), 0]‖ ≤ R := by
  intro R
  refine ⟨?_, LemDecCalEdif_STeeM_le sz0 1 (1 / 2) 0 _ ![true, true]
    ![(0 : Zd 3 (sz0.L 1)), 0] ![(0 : Zd 3 (sz0.L 1)), 0]⟩
  obtain ⟨hL, hW, hlam⟩ := lemDecCalEdif_inst_values
  have hWc : ((sz0.W 1 : ℕ) : ℝ) = 1024 := by rw [hW]; norm_num
  have hX : ‖STLM sz0 1 (1 / 2) 0
      (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
      ![true, true, true, !true, !true, !true]
      ![(0 : Zd 3 (sz0.L 1)), 0, 0, 0, 0, 0]‖ = ((((sz0.W 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ 5 := by
    have h := lemDecCalEdif_STLM_zero_const sz0 1 (E := 1 / 2) (by norm_num [abs_of_pos])
      (k := 5) ![true, true, true, !true, !true, !true] (0 : Zd 3 (sz0.L 1))
    have e : (fun _ : Fin 6 => (0 : Zd 3 (sz0.L 1))) = ![(0 : Zd 3 (sz0.L 1)), 0, 0, 0, 0, 0] := by
      funext i; fin_cases i <;> rfl
    rw [e] at h
    exact h
  have hSB : 0 < ‖SB 3 (sz0.L 1) (sz0.lam 1) 0 0‖ := by
    rw [SB_apply, sub_self]
    unfold sbKernel
    simp only [ite_true]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    positivity
  have hW0 : (0 : ℝ) < ((sz0.W 1 : ℕ) : ℝ) := by rw [hWc]; norm_num
  simp only [R]
  have hnn : ∀ b b' : Zd 3 (sz0.L 1), 0 ≤ ‖SB 3 (sz0.L 1) (sz0.lam 1) b b'‖ *
      (‖STLM sz0 1 (1 / 2) 0
          (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
          ![true, true, true, !true, !true, !true]
          ![(0 : Zd 3 (sz0.L 1)), 0, b', 0, 0, b]‖ +
        ‖STLM sz0 1 (1 / 2) 0
          (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
          ![true, true, true, !true, !true, !true]
          ![(0 : Zd 3 (sz0.L 1)), 0, b', 0, 0, b]‖) := fun b b' =>
    mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine mul_pos (pow_pos hW0 3) (Finset.sum_pos' (fun b _ => Finset.sum_nonneg fun b' _ => hnn b b')
    ⟨0, Finset.mem_univ _, Finset.sum_pos' (fun b' _ => hnn 0 b') ⟨0, Finset.mem_univ _, ?_⟩⟩)
  rw [hX]
  have hXp : 0 < ((((sz0.W 1 : ℕ) : ℝ) ^ 3)⁻¹) ^ 5 := pow_pos (inv_pos.2 (pow_pos hW0 3)) 5
  exact mul_pos hSB (add_pos hXp hXp)

/-- **Check (d)**: `LemDecCalEdif_cut_near` at the instance (a), the same-sign loop `σ₀ = σ₁ = +`
(RBM2D has only `σ = (+,-)`), labels `A₁ = A₁' = B = B' = 0`, `A₂ = A₂' = e₁`. -/
example :
    ‖STLM sz0 1 (1 / 2) 0
        (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
        ![true, true, true, !true, !true, !true]
        ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1, 0, Pi.single 0 1, 0, 0]‖ ≤
      1 * ((((sz0.W 1 : ℕ) : ℝ) ^ 3 * (1 - 0))⁻¹) ^ 5 *
          (if (zdistInf 3 (sz0.L 1) ((0 : Zd 3 (sz0.L 1)) - 0) : ℝ) ≤
              4 * Real.log (((sz0.L 1 : ℕ) : ℝ) ^ 3 * ((sz0.W 1 : ℕ) : ℝ) ^ (6 * 3)) ^ 2
            then 1 else 0) +
        32 * 3 ^ (3 + 1) * 1 ^ 6 * 1 *
          (((sz0.L 1 : ℕ) : ℝ) ^ 3 * ((sz0.W 1 : ℕ) : ℝ) ^ (6 * 3))⁻¹ :=
  LemDecCalEdif_cut_near LemDecCalEdif_inst_a true true 0 (Pi.single 0 1) 0 (Pi.single 0 1) 0 0

/-- The periodic `L^∞` distance of `e = 300 · e₁` to `0` in `Z_L³`, `L = 2 · 24⁵`. -/
private theorem lemDecCalEdif_inst_dist :
    zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - Pi.single 0 300) = 300 := by
  unfold zdistInf
  decide

private theorem lemDecCalEdif_inst_dist' :
    zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) = 0 := by
  unfold zdistInf
  decide

private theorem lemDecCalEdif_inst_dist'' :
    zdistInf 3 (szCL.L 0) (Pi.single 0 300 - (0 : Zd 3 (szCL.L 0))) = 300 := by
  unfold zdistInf
  decide

/-- `4 (log W)^{3/2} < 300` for `W = 2^24`. -/
private theorem lemDecCalEdif_inst_ell : 4 * Real.log ((szCL.W 0 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < 300 := by
  rw [szCL_log_W]
  have h2 := Real.log_two_lt_d9
  have h2' := Real.log_two_gt_d9
  set x : ℝ := ((0 : ℕ) : ℝ) + 24 with hx
  set y : ℝ := x * Real.log 2 with hy
  have hy0 : 0 < y := by rw [hy, hx]; norm_num; positivity
  have hy1 : y < 16.64 := by rw [hy, hx]; norm_num; linarith
  have h32 : y ^ ((3 : ℝ) / 2) = y * Real.sqrt y := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h32]
  have hs : Real.sqrt y < 4.08 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have := Real.sqrt_nonneg y
  nlinarith

/-- **Check (e)**: `LemDecCalEdif_cut_far` at the instance (b) (`L_n = 2 · 24⁵ → ∞` sequence,
`W = 2^24`), `σ₀ = +`, `σ₁ = -`, `A₁ = A₁' = B = B' = 0`, `A₂ = A₂' = 300 e₁`
(`|A₁ - A₂|_∞ = 300 > 4 (24 log 2)^{3/2} ≈ 271.4`; the far hypotheses cannot hold at `L = 8`):
the bound holds with the right side `R` of the theorem, and `R > 0`. -/
example :
    let W : ℝ := ((szCL.W 0 : ℕ) : ℝ)
    let T : ℝ → ℝ := tailTD 3 W 0 42
    let S : ℝ := Real.exp 2 * Real.exp (2 * Real.log W ^ ((3 : ℝ) / 4))
    let ls : ℝ := Real.log W ^ ((3 : ℝ) / 2)
    let e : Zd 3 (szCL.L 0) := Pi.single 0 300
    let R : ℝ := (2 * 9 ^ 3 * 1 * 1) ^ 2 * S ^ 3 *
          T (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - e) : ℝ) ^ 2 *
          (1 * ((W ^ 3 * (1 - 0))⁻¹) ^ ((3 : ℝ) / 2)) *
          ((if (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf 3 (szCL.L 0) (e - 0) : ℝ) ≤ ls + 1 then 1 else 0) +
            (if (zdistInf 3 (szCL.L 0) (e - 0) : ℝ) ≤ ls + 1 then 1 else 0)) +
        (2 * 9 ^ 3 * 1 * 1) ^ 3 * S ^ 3 *
          T (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - e) : ℝ) *
          T (zdistInf 3 (szCL.L 0) ((0 : Zd 3 (szCL.L 0)) - 0) : ℝ) *
          T (zdistInf 3 (szCL.L 0) (0 - e) : ℝ)
    0 < R ∧
    ‖STLM szCL 0 (1 / 2) 0
        (0 : Matrix (Idx 3 (szCL.L 0) (szCL.W 0)) (Idx 3 (szCL.L 0) (szCL.W 0)) ℂ)
        ![true, false, true, !true, !false, !true]
        ![(0 : Zd 3 (szCL.L 0)), e, 0, e, 0, 0]‖ ≤ R := by
  intro W T S ls e R
  have hWc := szCL_W_real 0
  refine ⟨?_, LemDecCalEdif_cut_far LemDecCalEdif_inst_b true false (0 : Zd 3 (szCL.L 0))
    (Pi.single 0 300) 0 (Pi.single 0 300) 0 0 ?_ ?_ ?_ ?_⟩
  · have hW : W = 2 ^ (0 + 24) := hWc
    simp only [R, T, S, ls, W, hW]
    refine add_pos_of_nonneg_of_pos (by positivity) ?_
    unfold tailTD
    positivity
  · rw [lemDecCalEdif_inst_dist']
    exact_mod_cast Real.rpow_nonneg (by have := szCL_one_le_log_W 0; linarith) _
  · rw [sub_self, show zdistInf 3 (szCL.L 0) (0 : Zd 3 (szCL.L 0)) = 0 from by
      unfold zdistInf; decide]
    exact_mod_cast Real.rpow_nonneg (by have := szCL_one_le_log_W 0; linarith) _
  · rw [lemDecCalEdif_inst_dist']
    norm_num
  · rw [lemDecCalEdif_inst_dist]
    exact_mod_cast lemDecCalEdif_inst_ell

end Instance

end RBM.Path

end
