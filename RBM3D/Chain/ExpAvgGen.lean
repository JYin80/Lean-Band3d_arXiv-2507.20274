/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.ExpAvg
import RBM3D.Chain.CltGen
import RBM3D.Evolution.XiPins

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# `lem:improve_exp_aver` over the carrier (BA-V row V1s1, ticket T2502 row c, targets 14-16)

Additive restatement of `Induction/ExpAvg.lean` (not edited) at a carrier `C : FlowFM sz` whose loops are those of the Hermitian matrix
`H₀ n + √u X` at `ztOf (C.m n) (E n) u` (`CltRepg`).  Paper: arXiv:2507.20274, `6:12-21` ("the same as [YY_25, Lemma 5.15]"),
`(res_ELK_n=1)`; the scalar-`M` proof of the paper is extended to a matrix `M` by W1 (iii), (iv) (Amend 1, `T2502ca`).

* **Fixed size, Stein** (target 14): `ExpAvgGen_stein_trace` (the Stein identity at `H₀ + √u X`, `H₀ ≠ 0`, for a trace `tr(P X G Q)`), the
  self-consistent identity `x = u M^{(++)} S x + R` of `x_a = 𝔼 𝓛^{(1)}_{u,+,a} - m` (`ExpAvgGen_selfcons`), Ward identity of `M`
  (`ExpAvgGen_ward`) and the invertibility of `1 - u M^{(++)} S` (`ExpAvgGen_isUnit_one_sub`, Levy-Desplanques).
* **Sequence part** (target 15): the relative-envelope bridge `≺ ⇒ moments` (`ExpAvgGen_moment`), the envelope of the loops and of `t_{aq}`.
* **Target 16**: `stImproveCoregL_of` (16a: the per-time core `STImproveCoregL`), `stImproveExpAvergL_of` (16b), `stExpAvgUgL_of_core` (16c), and the band
  discharge of the family texts (`ExpAvgGen_band_W1fam`, `ExpAvgGen_band_W1iiiOfLW`), `stImproveExpAver_of_gL` (band `stImproveExpAver_holds` through 16b).

Premises of 16a/16b beyond the shapes `T2502_Target16a/b`: the family flow facts `Step5CasesGen_FlowFacts` (`hFF`, ticket table row 3: `Admissible`, `T0 < 1`, `κm ≤ Im m`).
New public defs (Amend 1, item 3): the W1 vocabulary `ExpAvgGen_W1i`, `_W1ii`, `_tM`, `_MB`, `_W1iii`, `_W1iv`, `_W1fam`, `_W1iiiOfLW` and `STImproveCoregL`.
Every other helper is `private` or prefixed `ExpAvgGen_`.
-/

open private expAvg_integral_slice expAvg_integrable_of_cont_bdd expAvg_integrable_coord_smul expAvg_norm_trace_mul3_le
  from RBM3D.Induction.ExpAvg

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The public texts (Amend 1: `T2502_*` of `docs/tickets/checks/T2502-amend-1-check.lean`, name map `T2502_X ↦ ExpAvgGen_X`) -/

section Texts

variable {d : ℕ} {sz : Sizes d}

/-- **W1 (i)′**: (a) the variance kernel of the carrier is the block profile `SB d (L n) (g' n)`; (b) `(H₀ - E - m) M = 1`; (c) the block average of
`M` is `C.m n`. -/
def ExpAvgGen_W1i (C : FlowFM sz) (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (g' E : ℕ → ℝ) (n : ℕ) : Prop :=
  C.S n = SB d (sz.L n) (g' n) ∧
  (H₀ n - ((E n : ℂ) + C.m n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Matrix.of (fun x y => C.M n x y) = 1 ∧
  ∀ a : Zd d (sz.L n), (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, C.M n x x = C.m n

/-- **W1 (ii)′**: the same-charge row bound of the carrier kernel, eventual in `n`. -/
def ExpAvgGen_W1ii (C : FlowFM sz) (Cs : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ (σ : Bool) (s t : ℝ), 0 ≤ s → s ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b : Zd d (sz.L n), ‖Step2Gen_uKer C n σ σ s t a b‖ ≤ Cs

/-- The `M`-weighted block trace `t_{aq} = tr(E_a M P_q G_u)`. -/
def ExpAvgGen_tM (C : FlowFM sz) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (a q : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) q, C.M n x y * C.G n u ω y x

/-- The block entry `M^{(B)}_{aq} = M_{(a,0),(q,0)}`. -/
def ExpAvgGen_MB (C : FlowFM sz) (n : ℕ) (a q : Zd d (sz.L n)) : ℂ :=
  C.M n ((splitEquiv d (sz.L n) (sz.W n)).symm (a, 0)) ((splitEquiv d (sz.L n) (sz.W n)).symm (q, 0))

/-- **W1 (iii)**, per time: `|t_{aq} - M^{(++)}_{aq}| ≺ |M^{(B)}_{aq}| W^{-d}B_{τ,0}`.  Band: `δ_{aq} m (ḡ_a - m)` and `LWAvgLawgL`; BA: `TwistPins_circ_term`
(`BA/TwistPins:439`) and TL1 `BATwistAvgLaw` (`BA/TwistPins:91`), owner of the bridge V1-BA. -/
def ExpAvgGen_W1iii (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖ExpAvgGen_tM C n (τ n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖)
    (fun n p _ => ‖ExpAvgGen_MB C n p.1 p.2‖ * sz.Bctl n (τ n))

/-- **W1 (iv)**: `ℓ¹` row bound of `M^{(B)}`, eventual.  Band `CM = 1`; BA: `CltFlowBA_MB_decay` (`BA/CltFlowBA:221`) summed, made public by V1-BA. -/
def ExpAvgGen_W1iv (C : FlowFM sz) (CM : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ a : Zd d (sz.L n), ∑ q, ‖ExpAvgGen_MB C n a q‖ ≤ CM

end Texts

/-- **Family rows 9 + 14 merged, with (iv)**: `Cs`, `CM` after `(κ, ε, 𝔡)`, before `(𝔠, sz, z)`; one witness `(H₀, g', E)` per flow. -/
def ExpAvgGen_W1fam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ Cs CM : ℝ, 0 < Cs ∧ 0 < CM ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ (∀ n, ExpAvgGen_W1i (mk sz z) H₀ g' E n) ∧
          ExpAvgGen_W1ii (mk sz z) Cs ∧ ExpAvgGen_W1iv (mk sz z) CM

/-- **The per-time core** (target 16a): `lem:improve_exp_aver` at a matrix carrier; the Stein remainder is controlled by W1 (iii) at the same time
`u` (band `STImproveExpAvergL` plus the premise `ExpAvgGen_W1iii`). -/
def STImproveCoregL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ T0 sz z n) →
        LWAvgLawgL (mk sz z) (law sz) u → STLKgL (mk sz z) (law sz) u → ExpAvgGen_W1iii (mk sz z) (law sz) u →
          STExpAvgAtgL (mk sz z) (law sz) u

/-! ## 2. Transport between the fine lattice and the block-product index -/

section Transport

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem ExpAvgGen_blockMat_mul (A B : Matrix (Idx d L W) (Idx d L W) ℂ) :
    blockMat d L W (A * B) = blockMat d L W A * blockMat d L W B :=
  (Matrix.submatrix_mul_equiv A B _ (splitEquiv d L W).symm _).symm

private theorem ExpAvgGen_blockMat_sub_smul (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    blockMat d L W H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      blockMat d L W (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) := by
  ext p q
  simp [blockMat, Matrix.one_apply]

/-- `G(blockMat H) = blockMat (G H)`. -/
private theorem ExpAvgGen_Gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) :
    Gres (blockMat d L W H) z true = blockMat d L W (Gres H z true) := by
  unfold Gres
  simp only [ite_true]
  rw [ExpAvgGen_blockMat_sub_smul, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
  exact Matrix.inv_submatrix_equiv _ _ _

private theorem ExpAvgGen_trace_Eblk (A : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L) :
    Matrix.trace (blockMat d L W A * Eblk d L W a) = ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, A x x := by
  unfold Eblk
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  rw [← (splitEquiv d L W).sum_comp, Iblk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [blockMat, splitEquiv, Equiv.ofBijective_apply, mul_comm]

private theorem ExpAvgGen_sum_Eblk :
    ∑ q : Zd d L, Eblk d L W q = ((W : ℂ) ^ d)⁻¹ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  ext v w
  simp only [Eblk, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

/-- `W^d tr(G E_a M E_p) = W^{-d} Σ_{x∈[a]} Σ_{y∈[p]} M_{xy} G_{yx}`, the block trace `t_{ap}`. -/
private theorem ExpAvgGen_trace_four (G Mf : Matrix (Idx d L W) (Idx d L W) ℂ) (a p : Zd d L) :
    ((W : ℂ) ^ d) * Matrix.trace (blockMat d L W G * Eblk d L W a * blockMat d L W Mf * Eblk d L W p) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * G y x := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  have key : ∀ v : Vtx d L W, (blockMat d L W G * Eblk d L W a * blockMat d L W Mf * Eblk d L W p) v v =
      (∑ w, blockMat d L W G v w * (if w.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) * blockMat d L W Mf w v) *
        (if v.1 = p then ((W : ℂ) ^ d)⁻¹ else 0) := by
    intro v
    unfold Eblk
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  have e1 : ∀ y : Idx d L W, (∑ w, blockMat d L W G (splitEquiv d L W y) w * (if w.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        blockMat d L W Mf w (splitEquiv d L W y)) =
      ∑ x : Idx d L W, G y x * (if (split d L W x).1 = a then ((W : ℂ) ^ d)⁻¹ else 0) * Mf x y := by
    intro y
    rw [← (splitEquiv d L W).sum_comp]
    simp [blockMat, splitEquiv, Equiv.ofBijective_apply]
  simp only [Matrix.trace, Matrix.diag_apply, key]
  rw [← (splitEquiv d L W).sum_comp]
  simp only [e1, Iblk, Finset.sum_filter]
  have e2 : ∀ y : Idx d L W, ((splitEquiv d L W y).1 = p) ↔ ((split d L W y).1 = p) := fun y => by
    simp [splitEquiv, Equiv.ofBijective_apply]
  simp only [e2]
  have hite : ∀ (c : Prop) [Decidable c] (f : Idx d L W → ℂ), (if c then ∑ x, f x else 0) = ∑ x, if c then f x else 0 :=
    fun c _ f => by split_ifs <;> simp
  simp only [Finset.mul_sum, Finset.sum_mul, ite_mul, mul_ite, zero_mul, mul_zero, hite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hx : (split d L W x).1 = a <;> by_cases hy : (split d L W y).1 = p <;> simp [hx, hy]
  all_goals field_simp

end Transport

/-! ## 3. The Stein identity at `H₀ + √u X` (`H₀ ≠ 0`) for a trace `tr(P X G Q)` -/

section Stein

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem ExpAvgGen_Hb_herm {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) (u : ℝ) (ω : Ω d L W) :
    (H₀b + HflowBlock d L W u ω).IsHermitian :=
  hH.add (HflowBlock_isHermitian d L W u ω)

private theorem ExpAvgGen_G_cont {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W u ω) z true :=
  continuous_green_of_isHermitian (continuous_const.add (continuous_HflowBlock_sample d L W u)) (ExpAvgGen_Hb_herm hH u) hz

private theorem ExpAvgGen_G_norm {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Ω d L W) : ‖Gres (H₀b + HflowBlock d L W u ω) z true‖ ≤ |z.im|⁻¹ :=
  norm_Gsig_le_inv_eta (ExpAvgGen_Hb_herm hH u ω) (abs_pos.mpr hz) le_rfl true

/-- `‖tr(G K)‖ ≤ (L W)^d ‖G‖ ‖K‖`. -/
private theorem ExpAvgGen_trG_bdd (G K : Matrix (Vtx d L W) (Vtx d L W) ℂ) {r : ℝ} (hr : ‖G‖ ≤ r) :
    ‖Matrix.trace (G * K)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (r * ‖K‖) := by
  have h := norm_matrix_trace_le_card_mul (G * K)
  rw [card_BlockIndex] at h
  exact h.trans (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))) (Nat.cast_nonneg _))

/-- `‖tr(A M C)‖ ≤ (L W)^d ‖A‖ s ‖C‖` for `‖M‖ ≤ s`. -/
private theorem ExpAvgGen_trace3_le (A M C : Matrix (Vtx d L W) (Vtx d L W) ℂ) {s : ℝ} (hs : ‖M‖ ≤ s) :
    ‖Matrix.trace (A * M * C)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (‖A‖ * s * ‖C‖) :=
  (expAvg_norm_trace_mul3_le L W A M C).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) (norm_nonneg _)) (Nat.cast_nonneg _))

/-- `‖G X G‖ ≤ r ‖X‖ r` for `‖G‖ ≤ r`. -/
private theorem ExpAvgGen_norm_GXG (G X : Matrix (Vtx d L W) (Vtx d L W) ℂ) {r : ℝ} (hr : ‖G‖ ≤ r) : ‖G * X * G‖ ≤ r * ‖X‖ * r :=
  (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))) hr (norm_nonneg _)
    ((norm_nonneg _).trans hr |>.trans' le_rfl |> fun h => mul_nonneg h (norm_nonneg _)))

/-- One-coordinate Stein identity for `tr(P B_c G Q)`, `G = (H₀ + √u X - z)⁻¹` (`H₀ = 0`, `P = 1`, `Q = E_a`: `expAvg_stein_coord`). -/
private theorem ExpAvgGen_stein_coord (g : ℝ) {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) (c : CoordF d L W) :
    ∫ ω : Ω d L W, ω c • Matrix.trace (P * coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W u ω) z true * Q) ∂(PF d L W g) =
      (gvarF d L W g c : ℝ) • ∫ ω : Ω d L W, Matrix.trace (P * coordinateBlock d L W c *
        (-(Gres (H₀b + HflowBlock d L W u ω) z true * (Real.sqrt u • coordinateBlock d L W c) *
          Gres (H₀b + HflowBlock d L W u ω) z true)) * Q) ∂(PF d L W g) := by
  set B := coordinateBlock d L W c with hB
  let f : Ω d L W → ℂ := fun ω => Matrix.trace (P * B * Gres (H₀b + HflowBlock d L W u ω) z true * Q)
  let f' : Ω d L W → ℂ := fun ω => Matrix.trace (P * B * (-(Gres (H₀b + HflowBlock d L W u ω) z true *
    (Real.sqrt u • B) * Gres (H₀b + HflowBlock d L W u ω) z true)) * Q)
  have hGc := ExpAvgGen_G_cont hH u hz
  have hgc : Continuous f := (continuous_matrixTrace d L W).comp ((continuous_const.mul hGc).mul continuous_const)
  have hg'c : Continuous f' :=
    (continuous_matrixTrace d L W).comp ((continuous_const.mul (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const)
  have hderiv : ∀ ω : Ω d L W, HasDerivAt (fun t : ℝ => f (Function.update ω c t)) (f' ω) (ω c) := by
    intro ω
    set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h1 := hasDerivAt_green_moving (H := fun t : ℝ => H₀b + HflowBlock d L W u (Function.update ω c t)) (z := fun _ => z)
      ((hasDerivAt_HflowBlock_update d L W u ω c).const_add H₀b) (hasDerivAt_const (ω c) z)
      (by simpa only [Function.update_eq_self] using ExpAvgGen_Hb_herm hH u ω) hz
    have h2 := ((hasDerivAt_const (ω c) (P * B)).mul h1).mul_const Q
    have h3 := T.hasFDerivAt.comp_hasDerivAt (ω c) h2
    refine h3.congr_deriv ?_
    simp only [hT, f', zero_mul, zero_add, Function.update_eq_self, zero_smul, sub_zero, ← hB]
  have hgb : ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C :=
    ⟨(((L * W) ^ d : ℕ) : ℝ) * (‖P * B‖ * |z.im|⁻¹ * ‖Q‖), fun ω => ExpAvgGen_trace3_le _ _ _ (ExpAvgGen_G_norm hH u hz ω)⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖f' ω‖ ≤ C := by
    refine ⟨(((L * W) ^ d : ℕ) : ℝ) * (‖P * B‖ * ((|z.im|⁻¹ * ‖Real.sqrt u • B‖ * |z.im|⁻¹)) * ‖Q‖), fun ω => ?_⟩
    have hM : ‖-(Gres (H₀b + HflowBlock d L W u ω) z true * (Real.sqrt u • B) * Gres (H₀b + HflowBlock d L W u ω) z true)‖ ≤
        |z.im|⁻¹ * ‖Real.sqrt u • B‖ * |z.im|⁻¹ := by
      rw [norm_neg]
      exact ExpAvgGen_norm_GXG _ _ (ExpAvgGen_G_norm hH u hz ω)
    exact ExpAvgGen_trace3_le _ _ _ hM
  exact GaussianProduct.stein (gvarF d L W g) c f f' hgc hg'c hderiv hgb hg'b

/-- Pointwise contraction: `Σ_c 𝕍_c tr(P B_c (-(G √u B_c G)) Q) = -√u W^d Σ_{p,q} tr(G Q P E_p) S_{pq} tr(G E_q)` (`sum_coordinateBlock_trace_pair`). -/
private theorem ExpAvgGen_contract (g u : ℝ) (G P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) * Matrix.trace (P * coordinateBlock d L W c *
      (-(G * (Real.sqrt u • coordinateBlock d L W c) * G)) * Q) =
      -(Real.sqrt u : ℂ) * (((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, Matrix.trace (G * Q * P * Eblk d L W p) * SB d L g p q *
          Matrix.trace (G * Eblk d L W q)) := by
  have hterm : ∀ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) * Matrix.trace (P * coordinateBlock d L W c *
      (-(G * (Real.sqrt u • coordinateBlock d L W c) * G)) * Q) =
      -(Real.sqrt u : ℂ) * (((gvarF d L W g c : ℝ) : ℂ) * Matrix.trace (G * Q * P * coordinateBlock d L W c * G * coordinateBlock d L W c)) := by
    intro c
    set B := coordinateBlock d L W c
    have h1 : P * B * (-(G * (Real.sqrt u • B) * G)) * Q = -(Real.sqrt u • ((P * B * G * B) * (G * Q))) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have h2 : Matrix.trace ((P * B * G * B) * (G * Q)) = Matrix.trace (G * Q * P * B * G * B) := by
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_neg, Matrix.trace_smul, h2, Complex.real_smul]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_coordinateBlock_trace_pair d L W g (G * Q * P) G]

/-- `tr(P X G Q) = Σ_c ω_c tr(P B_c G Q)`. -/
private theorem ExpAvgGen_trace_expand (P Q G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (ω : Ω d L W) :
    Matrix.trace (P * blockMat d L W (Xmat d L W ω) * G * Q) =
      ∑ c : CoordF d L W, ω c • Matrix.trace (P * coordinateBlock d L W c * G * Q) := by
  rw [Xblock_eq_sum_coordinates]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

/-- Integrability of the integrands of the Stein identity for a continuous `G` with `‖G‖ ≤ r`. -/
private theorem ExpAvgGen_stein_int (g u r : ℝ) {G : Ω d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ} (hGc : Continuous G)
    (hGn : ∀ ω, ‖G ω‖ ≤ r) (P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    (∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => ω c • Matrix.trace (P * coordinateBlock d L W c * G ω * Q)) (PF d L W g)) ∧
    (∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => Matrix.trace (P * coordinateBlock d L W c *
      (-(G ω * (Real.sqrt u • coordinateBlock d L W c) * G ω)) * Q)) (PF d L W g)) ∧
    (∀ p : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p)) (PF d L W g)) ∧
    (∀ q : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Eblk d L W q)) (PF d L W g)) ∧
    (∀ p q : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p) *
      Matrix.trace (G ω * Eblk d L W q)) (PF d L W g)) := by
  have hc1 : ∀ p : Zd d L, Continuous fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p) := fun p =>
    (continuous_matrixTrace d L W).comp (((hGc.mul continuous_const).mul continuous_const).mul continuous_const)
  have hc2 : ∀ q : Zd d L, Continuous fun ω : Ω d L W => Matrix.trace (G ω * Eblk d L W q) := fun q =>
    (continuous_matrixTrace d L W).comp (hGc.mul continuous_const)
  have hb1 : ∀ (p : Zd d L) (ω : Ω d L W), ‖Matrix.trace (G ω * Q * P * Eblk d L W p)‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * (r * ‖Q * P * Eblk d L W p‖) := by
    intro p ω
    have e : G ω * Q * P * Eblk d L W p = G ω * (Q * P * Eblk d L W p) := by simp only [Matrix.mul_assoc]
    rw [e]
    exact ExpAvgGen_trG_bdd _ _ (hGn ω)
  have hb2 : ∀ (q : Zd d L) (ω : Ω d L W), ‖Matrix.trace (G ω * Eblk d L W q)‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (r * ‖Eblk d L W q‖) :=
    fun q ω => ExpAvgGen_trG_bdd _ _ (hGn ω)
  refine ⟨fun c => ?_, fun c => ?_, fun p => ?_, fun q => ?_, fun p q => ?_⟩
  · refine expAvg_integrable_coord_smul L W g c _ ((continuous_matrixTrace d L W).comp ((continuous_const.mul hGc).mul continuous_const)).measurable
      (C := (((L * W) ^ d : ℕ) : ℝ) * (‖P * coordinateBlock d L W c‖ * r * ‖Q‖)) fun ω => ?_
    exact ExpAvgGen_trace3_le _ _ _ (hGn ω)
  · refine expAvg_integrable_of_cont_bdd L W g ((continuous_matrixTrace d L W).comp ((continuous_const.mul
      (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const))
      (C := (((L * W) ^ d : ℕ) : ℝ) * (‖P * coordinateBlock d L W c‖ * ((r * ‖Real.sqrt u • coordinateBlock d L W c‖ * r)) * ‖Q‖))
      fun ω => ?_
    have hM : ‖-(G ω * (Real.sqrt u • coordinateBlock d L W c) * G ω)‖ ≤ r * ‖Real.sqrt u • coordinateBlock d L W c‖ * r := by
      rw [norm_neg]
      exact ExpAvgGen_norm_GXG _ _ (hGn ω)
    exact ExpAvgGen_trace3_le _ _ _ hM
  · exact expAvg_integrable_of_cont_bdd L W g (hc1 p) (hb1 p)
  · exact expAvg_integrable_of_cont_bdd L W g (hc2 q) (hb2 q)
  · refine expAvg_integrable_of_cont_bdd L W g ((hc1 p).mul (hc2 q))
      (C := ((((L * W) ^ d : ℕ) : ℝ) * (r * ‖Q * P * Eblk d L W p‖)) * ((((L * W) ^ d : ℕ) : ℝ) * (r * ‖Eblk d L W q‖))) fun ω => ?_
    have hr0 : 0 ≤ r := (norm_nonneg _).trans (hGn ω)
    have hA : 0 ≤ (((L * W) ^ d : ℕ) : ℝ) * (r * ‖Q * P * Eblk d L W p‖) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
    show ‖Matrix.trace (G ω * Q * P * Eblk d L W p) * Matrix.trace (G ω * Eblk d L W q)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hb1 p ω) (hb2 q ω) (norm_nonneg _) hA

/-- **The Stein identity** at `H₀ + √u X` (`H₀ ≠ 0`; band `expAvg_stein` is `H₀ = 0`, `P = 1`, `Q = E_a`):
`𝔼 tr(P X G Q) = -√u W^d Σ_{p,q} 𝔼[tr(G Q P E_p) S_{pq} tr(G E_q)]`, `G = (H₀ + √u X - z)⁻¹`. -/
private theorem ExpAvgGen_stein_trace (g : ℝ) {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∫ ω : Ω d L W, Matrix.trace (P * blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W u ω) z true * Q) ∂(PF d L W g) =
      -(Real.sqrt u : ℂ) * (((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, ∫ ω : Ω d L W,
        Matrix.trace (Gres (H₀b + HflowBlock d L W u ω) z true * Q * P * Eblk d L W p) * SB d L g p q *
          Matrix.trace (Gres (H₀b + HflowBlock d L W u ω) z true * Eblk d L W q) ∂(PF d L W g)) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Ω d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ, ∀ ω, G ω = Gres (H₀b + HflowBlock d L W u ω) z true :=
    ⟨_, fun _ => rfl⟩
  have hGc : Continuous G := (funext hG : G = fun ω => Gres (H₀b + HflowBlock d L W u ω) z true) ▸ ExpAvgGen_G_cont hH u hz
  have hGn : ∀ ω, ‖G ω‖ ≤ |z.im|⁻¹ := fun ω => (hG ω) ▸ ExpAvgGen_G_norm hH u hz ω
  simp only [← hG]
  obtain ⟨hI1, hI2, -, -, hF0⟩ := ExpAvgGen_stein_int (L := L) (W := W) g u _ hGc hGn P Q
  have hF : ∀ p q : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p) * SB d L g p q *
      Matrix.trace (G ω * Eblk d L W q)) (PF d L W g) := fun p q => by
    have := (hF0 p q).const_mul (SB d L g p q)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [mul_left_comm (SB d L g p q), mul_comm (SB d L g p q)]
    ring
  simp_rw [ExpAvgGen_trace_expand]
  rw [integral_finsetSum _ (fun c _ => hI1 c)]
  have hst : ∀ c : CoordF d L W, ∫ ω : Ω d L W, ω c • Matrix.trace (P * coordinateBlock d L W c * G ω * Q) ∂(PF d L W g) =
      ∫ ω : Ω d L W, ((gvarF d L W g c : ℝ) : ℂ) * Matrix.trace (P * coordinateBlock d L W c *
        (-(G ω * (Real.sqrt u • coordinateBlock d L W c) * G ω)) * Q) ∂(PF d L W g) := by
    intro c
    have := ExpAvgGen_stein_coord g hH u hz P Q c
    simp only [← hG] at this
    rw [this, integral_const_mul, Complex.real_smul]
  simp_rw [hst]
  rw [← integral_finsetSum _ (fun c _ => (hI2 c).const_mul _)]
  simp_rw [ExpAvgGen_contract]
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hF p q))]
  exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun p _ => integral_finsetSum _ (fun q _ => hF p q)))

private theorem ExpAvgGen_HflowBlock_eq (u : ℝ) (ω : Ω d L W) :
    HflowBlock d L W u ω = (Real.sqrt u : ℂ) • blockMat d L W (Xmat d L W ω) := by
  ext i j
  simp [HflowBlock, blockMat, Hflow]

private theorem ExpAvgGen_blockMat_Hflow (H₀ : Matrix (Idx d L W) (Idx d L W) ℂ) (u : ℝ) (ω : Ω d L W) :
    blockMat d L W (H₀ + Hflow d L W u ω) = blockMat d L W H₀ + HflowBlock d L W u ω := by
  ext i j
  simp [HflowBlock, blockMat]

/-- The resolvent identity `G = M - M (u m + √u X) G` (`G = (H₀ + √u X - z)⁻¹`, `(H₀ - z - u m) M = 1`, `z + u m = E + m`). -/
private theorem ExpAvgGen_resolvent_id {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {u : ℝ} {z m : ℂ}
    (hz : z.im ≠ 0) (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1) (ω : Ω d L W) :
    Gres (H₀b + HflowBlock d L W u ω) z true = Mb - Mb * (((u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) +
      (Real.sqrt u : ℂ) • blockMat d L W (Xmat d L W ω)) * Gres (H₀b + HflowBlock d L W u ω) z true := by
  set T : Matrix (Vtx d L W) (Vtx d L W) ℂ := H₀b + HflowBlock d L W u ω - z • 1 with hT
  have hTu : IsUnit T := isUnit_sub_smul_of_isHermitian (ExpAvgGen_Hb_herm hH u ω) hz
  have hG : Gres (H₀b + HflowBlock d L W u ω) z true = Ring.inverse T := by simp [Gres, hT]
  have hTG : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel T hTu
  have hM' : Mb * (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) = 1 := mul_eq_one_comm.mp hM
  have hTdec : T = (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) +
      (((u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) + (Real.sqrt u : ℂ) • blockMat d L W (Xmat d L W ω)) := by
    rw [hT, ExpAvgGen_HflowBlock_eq]
    module
  have h1 : Mb * T * Ring.inverse T = Mb := by rw [Matrix.mul_assoc, hTG, Matrix.mul_one]
  have h2 : Mb * T = 1 + Mb * (((u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) + (Real.sqrt u : ℂ) • blockMat d L W (Xmat d L W ω)) := by
    rw [hTdec, Matrix.mul_add, hM']
  rw [h2, Matrix.add_mul, Matrix.one_mul] at h1
  rw [hG]
  exact eq_sub_of_add_eq h1

/-- **The self-consistent identity before the translation** (Vtx level): `𝔼 tr(G E_a) = tr(M E_a) - u m 𝔼 tr(M G E_a)
+ u W^d Σ_{p,q} 𝔼[tr(G E_a M E_p) S_{pq} tr(G E_q)]`. -/
private theorem ExpAvgGen_sid1 (g : ℝ) {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {u : ℝ} (hu : 0 ≤ u)
    {z m : ℂ} (hz : z.im ≠ 0) (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1) (a : Zd d L) :
    ∫ ω : Ω d L W, Matrix.trace (Gres (H₀b + HflowBlock d L W u ω) z true * Eblk d L W a) ∂(PF d L W g) =
      Matrix.trace (Mb * Eblk d L W a) - ((u : ℂ) * m) * ∫ ω : Ω d L W, Matrix.trace (Mb * Gres (H₀b + HflowBlock d L W u ω) z true *
        Eblk d L W a) ∂(PF d L W g) +
      (u : ℂ) * (((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, ∫ ω : Ω d L W,
        Matrix.trace (Gres (H₀b + HflowBlock d L W u ω) z true * Eblk d L W a * Mb * Eblk d L W p) * SB d L g p q *
          Matrix.trace (Gres (H₀b + HflowBlock d L W u ω) z true * Eblk d L W q) ∂(PF d L W g)) := by
  classical
  have hst := ExpAvgGen_stein_trace g hH u hz Mb (Eblk d L W a)
  obtain ⟨G, hG⟩ : ∃ G : Ω d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ, ∀ ω, G ω = Gres (H₀b + HflowBlock d L W u ω) z true :=
    ⟨_, fun _ => rfl⟩
  have hGc : Continuous G := (funext hG : G = fun ω => Gres (H₀b + HflowBlock d L W u ω) z true) ▸ ExpAvgGen_G_cont hH u hz
  have hGn : ∀ ω, ‖G ω‖ ≤ |z.im|⁻¹ := fun ω => (hG ω) ▸ ExpAvgGen_G_norm hH u hz ω
  simp only [← hG] at hst ⊢
  obtain ⟨hI1, -, -, -, -⟩ := ExpAvgGen_stein_int (L := L) (W := W) g u _ hGc hGn Mb (Eblk d L W a)
  have hpt : ∀ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a) = Matrix.trace (Mb * Eblk d L W a) -
      ((u : ℂ) * m) * Matrix.trace (Mb * G ω * Eblk d L W a) -
      (Real.sqrt u : ℂ) * Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a) := by
    intro ω
    have h := ExpAvgGen_resolvent_id (Mb := Mb) hH hz hM ω
    rw [← hG] at h
    have h2 : G ω * Eblk d L W a = Mb * Eblk d L W a - (((u : ℂ) * m) • (Mb * G ω * Eblk d L W a) +
        (Real.sqrt u : ℂ) • (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)) := by
      conv_lhs => rw [h]
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [h2, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hi1 : Integrable (fun ω : Ω d L W => Matrix.trace (Mb * G ω * Eblk d L W a)) (PF d L W g) :=
    expAvg_integrable_of_cont_bdd L W g ((continuous_matrixTrace d L W).comp ((continuous_const.mul hGc).mul continuous_const))
      (C := (((L * W) ^ d : ℕ) : ℝ) * (‖Mb‖ * |z.im|⁻¹ * ‖Eblk d L W a‖)) fun ω => ExpAvgGen_trace3_le _ _ _ (hGn ω)
  have hi2 : Integrable (fun ω : Ω d L W => Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)) (PF d L W g) := by
    have : (fun ω : Ω d L W => Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)) =
        fun ω => ∑ c : CoordF d L W, ω c • Matrix.trace (Mb * coordinateBlock d L W c * G ω * Eblk d L W a) :=
      funext fun ω => ExpAvgGen_trace_expand _ _ _ ω
    rw [this]
    exact integrable_finsetSum _ fun c _ => hI1 c
  have i1 : Integrable (fun ω : Ω d L W => Matrix.trace (Mb * Eblk d L W a) - ((u : ℂ) * m) * Matrix.trace (Mb * G ω * Eblk d L W a))
      (PF d L W g) := (integrable_const _).sub (hi1.const_mul _)
  have i2 : Integrable (fun ω : Ω d L W => (Real.sqrt u : ℂ) *
      Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)) (PF d L W g) := hi2.const_mul _
  have i3 : Integrable (fun ω : Ω d L W => ((u : ℂ) * m) * Matrix.trace (Mb * G ω * Eblk d L W a)) (PF d L W g) := hi1.const_mul _
  simp_rw [hpt]
  rw [integral_sub i1 i2, integral_sub (integrable_const _) i3, integral_const_mul, integral_const_mul, integral_const, hst]
  have hsq : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
  have h1 : (PF d L W g).real Set.univ = 1 := by simp [Measure.real]
  simp only [h1, Complex.real_smul, Complex.ofReal_one, one_mul]
  linear_combination ((((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
    SB d L g p q * Matrix.trace (G ω * Eblk d L W q) ∂(PF d L W g))) * hsq

private theorem ExpAvgGen_blockMat_one : blockMat d L W (1 : Matrix (Idx d L W) (Idx d L W) ℂ) = 1 :=
  Matrix.submatrix_one_equiv _

/-- **The fixed-size self-consistent identity** (fine lattice; `x_a = 𝔼 g_a - m`, `g_q = W^{-d} Σ_{x∈[q]} G_{xx}`, `t_{ap} = W^{-d} Σ_{x∈[a]} Σ_{y∈[p]} M_{xy} G_{yx}`):
`x_a = u Σ_{p,q} S_{pq} 𝔼[t_{ap} (g_q - m)]` for `(H₀ - z - u m) M = 1`, `tr(M E_a) = m`, `G = (H₀ + √u X - z)⁻¹` (band: `expAvg_selfcons`, `M = m`). -/
private theorem ExpAvgGen_selfcons_fixed (g : ℝ) (hL : 3 ≤ L) {H₀ Mf : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H₀.IsHermitian) {u : ℝ}
    (hu : 0 ≤ u) {z m : ℂ} (hz : z.im ≠ 0) (hM : (H₀ - (z + (u : ℂ) * m) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * Mf = 1)
    (hm : ∀ a : Zd d L, ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, Mf x x = m) (a : Zd d L) :
    (∫ ω : Ω d L W, ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, Gres (H₀ + Hflow d L W u ω) z true x x ∂(PF d L W g)) - m =
      (u : ℂ) * ∑ p : Zd d L, ∑ q : Zd d L, SB d L g p q * ∫ ω : Ω d L W,
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gres (H₀ + Hflow d L W u ω) z true y x) *
          (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gres (H₀ + Hflow d L W u ω) z true x x - m) ∂(PF d L W g) := by
  classical
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  obtain ⟨Gf, hGf⟩ : ∃ Gf : Ω d L W → Matrix (Idx d L W) (Idx d L W) ℂ, ∀ ω, Gf ω = Gres (H₀ + Hflow d L W u ω) z true :=
    ⟨_, fun _ => rfl⟩
  simp only [← hGf]
  have hHb : (blockMat d L W H₀).IsHermitian := hH.submatrix _
  have hMb : (blockMat d L W H₀ - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * blockMat d L W Mf = 1 := by
    rw [ExpAvgGen_blockMat_sub_smul, ← ExpAvgGen_blockMat_mul, hM, ExpAvgGen_blockMat_one]
  have hGb : ∀ ω, Gres (blockMat d L W H₀ + HflowBlock d L W u ω) z true = blockMat d L W (Gf ω) := by
    intro ω
    rw [hGf, ← ExpAvgGen_blockMat_Hflow, ExpAvgGen_Gres_blockMat]
  have hs := ExpAvgGen_sid1 g hHb hu hz hMb a
  simp only [hGb] at hs
  -- the integrability facts
  have hGc : Continuous fun ω : Ω d L W => blockMat d L W (Gf ω) :=
    (funext hGb : (fun ω : Ω d L W => Gres (blockMat d L W H₀ + HflowBlock d L W u ω) z true) = _) ▸ ExpAvgGen_G_cont hHb u hz
  have hGn : ∀ ω, ‖blockMat d L W (Gf ω)‖ ≤ |z.im|⁻¹ := fun ω => (hGb ω) ▸ ExpAvgGen_G_norm hHb u hz ω
  obtain ⟨-, -, hIp, hIq, hIpq⟩ := ExpAvgGen_stein_int (L := L) (W := W) g u _ hGc hGn (blockMat d L W Mf) (Eblk d L W a)
  -- the translation of the traces
  have e1 : ∀ (ω : Ω d L W) (q : Zd d L), Matrix.trace (blockMat d L W (Gf ω) * Eblk d L W q) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x := fun ω q => ExpAvgGen_trace_Eblk _ q
  have e2 : Matrix.trace (blockMat d L W Mf * Eblk d L W a) = m := by rw [ExpAvgGen_trace_Eblk, hm]
  have e4 : ∀ (ω : Ω d L W) (p : Zd d L), Matrix.trace (blockMat d L W (Gf ω) * Eblk d L W a * blockMat d L W Mf * Eblk d L W p) =
      ((W : ℂ) ^ d)⁻¹ * (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) := by
    intro ω p
    have := ExpAvgGen_trace_four (Gf ω) Mf a p
    rw [← this]
    field_simp
  have e3 : ∀ ω : Ω d L W, Matrix.trace (blockMat d L W Mf * blockMat d L W (Gf ω) * Eblk d L W a) =
      ∑ q : Zd d L, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mf x y * Gf ω y x) := by
    intro ω
    have hid : ((W : ℂ) ^ d) • ∑ q : Zd d L, Eblk d L W q = (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
      rw [ExpAvgGen_sum_Eblk, smul_smul, mul_inv_cancel₀ hW, one_smul]
    have h1 : Matrix.trace (blockMat d L W Mf * blockMat d L W (Gf ω) * Eblk d L W a) =
        Matrix.trace (blockMat d L W (Gf ω) * Eblk d L W a * blockMat d L W Mf) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [h1]
    calc Matrix.trace (blockMat d L W (Gf ω) * Eblk d L W a * blockMat d L W Mf)
        = Matrix.trace (blockMat d L W (Gf ω) * Eblk d L W a * blockMat d L W Mf * (((W : ℂ) ^ d) • ∑ q : Zd d L, Eblk d L W q)) := by
          rw [hid, Matrix.mul_one]
      _ = ∑ q : Zd d L, ((W : ℂ) ^ d) * Matrix.trace (blockMat d L W (Gf ω) * Eblk d L W a * blockMat d L W Mf * Eblk d L W q) := by
          rw [Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, Finset.mul_sum]
      _ = _ := Finset.sum_congr rfl fun q _ => by rw [e4]; field_simp
  simp only [e1, e2, e3, e4] at hs
  -- integrability of `t` and `t g`
  have hit : ∀ p : Zd d L, Integrable (fun ω : Ω d L W => ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x)
      (PF d L W g) := by
    intro p
    refine ((hIp p).const_mul ((W : ℂ) ^ d)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [e4]
    exact mul_inv_cancel_left₀ hW _
  have hitg : ∀ p q : Zd d L, Integrable (fun ω : Ω d L W => (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
      (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x)) (PF d L W g) := by
    intro p q
    refine ((hIpq p q).const_mul ((W : ℂ) ^ d)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [e1, e4]
    field_simp
  have hitq : ∀ q : Zd d L, Integrable (fun ω : Ω d L W => ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) (PF d L W g) := by
    intro q
    exact (hIq q).congr (Filter.Eventually.of_forall fun ω => e1 ω q)
  have h1 : (PF d L W g).real Set.univ = 1 := by simp [Measure.real]
  -- the integrals
  have hint1 : ∫ ω : Ω d L W, ∑ q : Zd d L, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mf x y * Gf ω y x) ∂(PF d L W g) =
      ∑ q : Zd d L, ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mf x y * Gf ω y x) ∂(PF d L W g) :=
    integral_finsetSum _ fun q _ => hit q
  have hint2 : ∀ p q : Zd d L, ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
      (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x - m) ∂(PF d L W g) =
      (∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g)) -
      m * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) ∂(PF d L W g) := by
    intro p q
    have e : ∀ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x - m) =
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
          (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) -
        m * (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) := fun ω => by ring
    simp only [e]
    rw [integral_sub (hitg p q) ((hit p).const_mul m), integral_const_mul]
  have hint3 : ∀ p q : Zd d L, ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x)) *
      SB d L g p q * (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g) =
      (((W : ℂ) ^ d)⁻¹ * SB d L g p q) * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g) := by
    intro p q
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  simp only [hint1, hint3, hint2] at hs ⊢
  have hS : ∀ p : Zd d L, ∑ q : Zd d L, SB d L g p q = 1 := fun p => sum_SB_row d L g hL p
  have hR : ∀ p : Zd d L, ∑ q : Zd d L, SB d L g p q * ((∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g)) -
      m * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) ∂(PF d L W g)) =
      (∑ q : Zd d L, SB d L g p q * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g)) -
        m * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) ∂(PF d L W g) := by
    intro p
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_mul, hS p, one_mul]
  simp only [hR, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hs]
  have e5 : ∀ p q : Zd d L, ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹ * SB d L g p q *
      ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g)) =
      SB d L g p q * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g) := fun p q => by
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]
  have hA : ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, (((W : ℂ) ^ d)⁻¹ * SB d L g p q *
      ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g)) =
      ∑ p : Zd d L, ∑ q : Zd d L, SB d L g p q * ∫ ω : Ω d L W, (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W p, Mf x y * Gf ω y x) *
        (((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W q, Gf ω x x) ∂(PF d L W g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => e5 p q
  rw [hA]
  ring


end Stein

/-! ## 4. The Ward identity of `M`, `‖M^{(++)}‖_∞ ≤ 1` and the invertibility of `1 - u M^{(++)} S` -/

section Ward

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Ward identity** of `M = (H₀ - w)⁻¹`: `Im M_xx = Im w Σ_y |M_xy|² = Im w Σ_y |M_yx|²` (from `(H₀ - w) M = 1` and `H₀ = H₀ᴴ` only). -/
private theorem ExpAvgGen_ward {H₀ M : Matrix ι ι ℂ} (hH : H₀.IsHermitian) {w : ℂ} (hM : (H₀ - w • (1 : Matrix ι ι ℂ)) * M = 1) (x : ι) :
    (M x x).im = w.im * ∑ y, ‖M x y‖ ^ 2 ∧ (M x x).im = w.im * ∑ y, ‖M y x‖ ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix ι ι ℂ, A = H₀ - w • (1 : Matrix ι ι ℂ) := ⟨_, rfl⟩
  rw [← hA] at hM
  have hMA : M * A = 1 := mul_eq_one_comm.mp hM
  have hAh : Aᴴ = H₀ - (starRingEnd ℂ w) • (1 : Matrix ι ι ℂ) := by
    rw [hA, Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have hdiff : Aᴴ - A = (w - starRingEnd ℂ w) • (1 : Matrix ι ι ℂ) := by rw [hAh, hA]; module
  have h1 : Mᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hM, Matrix.conjTranspose_one]
  have h2 : Aᴴ * Mᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hMA, Matrix.conjTranspose_one]
  have hform1 : M - Mᴴ = (w - starRingEnd ℂ w) • (Mᴴ * M) := by
    calc M - Mᴴ = Mᴴ * Aᴴ * M - Mᴴ * (A * M) := by rw [h1, hM, Matrix.one_mul, Matrix.mul_one]
      _ = Mᴴ * (Aᴴ - A) * M := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = _ := by rw [hdiff]; simp [Matrix.mul_smul, Matrix.smul_mul]
  have hform2 : M - Mᴴ = (w - starRingEnd ℂ w) • (M * Mᴴ) := by
    calc M - Mᴴ = M * (Aᴴ * Mᴴ) - M * A * Mᴴ := by rw [h2, hMA, Matrix.mul_one, Matrix.one_mul]
      _ = M * (Aᴴ - A) * Mᴴ := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = _ := by rw [hdiff]; simp [Matrix.mul_smul, Matrix.smul_mul]
  have hw : w - starRingEnd ℂ w = (2 * w.im : ℝ) * Complex.I := Complex.sub_conj w
  have hent : ∀ (N : Matrix ι ι ℂ), M - Mᴴ = (w - starRingEnd ℂ w) • N → ∀ r : ℝ, (N x x).re = r → (N x x).im = 0 →
      (M x x).im = w.im * r := by
    intro N hN r hr hi
    have := congrArg (fun K : Matrix ι ι ℂ => (K x x).im) hN
    simp only [Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_im, Complex.star_def, Complex.conj_im,
      hw, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hr, hi] at this
    linarith
  have hsq : ∀ f : ι → ℂ, (∑ y, star (f y) * f y).re = ∑ y, ‖f y‖ ^ 2 ∧ (∑ y, star (f y) * f y).im = 0 := fun f => by
    refine ⟨?_, ?_⟩ <;> simp [Complex.re_sum, Complex.im_sum, Complex.conj_mul', ← Complex.ofReal_pow]
  refine ⟨hent (M * Mᴴ) hform2 _ ?_ ?_, hent (Mᴴ * M) hform1 _ ?_ ?_⟩
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simpa [mul_comm] using (hsq fun y => M x y).1
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [mul_comm]
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact (hsq fun y => M y x).1
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact (hsq fun y => M y x).2

/-- Levy-Desplanques: `‖Y‖_∞ ≤ 1` and `0 ≤ u < 1` give `1 - u Y` invertible. -/
private theorem ExpAvgGen_isUnit_one_sub (Y : Matrix ι ι ℂ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hY : ∀ a, ∑ b, ‖Y a b‖ ≤ 1) :
    IsUnit (1 - (u : ℂ) • Y) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have h1 : ∑ j ∈ Finset.univ.erase k, ‖(1 - (u : ℂ) • Y) k j‖ = u * ∑ j ∈ Finset.univ.erase k, ‖Y k j‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : k ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    simp [Matrix.sub_apply, Matrix.one_apply, hjk, Complex.norm_real, abs_of_nonneg hu0]
  have h2 : 1 - u * ‖Y k k‖ ≤ ‖(1 - (u : ℂ) • Y) k k‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((u : ℂ) * Y k k)
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, norm_one, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hu0] at this ⊢
    exact this
  have h3 : ∑ j ∈ Finset.univ.erase k, ‖Y k j‖ = ∑ j, ‖Y k j‖ - ‖Y k k‖ := Finset.sum_erase_eq_sub (Finset.mem_univ k)
  have h4 := hY k
  rw [h1, h3]
  nlinarith [norm_nonneg (Y k k)]

/-- `x = u X x + R` with `‖R‖_∞ ≤ K`, `1 - u X` invertible and the row sums of its inverse `≤ Cs` give `‖x‖_∞ ≤ Cs K`. -/
private theorem ExpAvgGen_solve {X : Matrix ι ι ℂ} {u : ℝ} (hU : IsUnit (1 - (u : ℂ) • X)) {x R : ι → ℂ}
    (h : ∀ a, x a = (u : ℂ) * ∑ b, X a b * x b + R a) {K Cs : ℝ} (hR : ∀ a, ‖R a‖ ≤ K)
    (hrow : ∀ a, ∑ b, ‖Ring.inverse (1 - (u : ℂ) • X) a b‖ ≤ Cs) (a : ι) : ‖x a‖ ≤ Cs * K := by
  have hy : R = (1 - (u : ℂ) • X) *ᵥ x := by
    funext c
    have hm : ((1 - (u : ℂ) • X) *ᵥ x) c = x c - (u : ℂ) * ∑ b, X c b * x b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      simp [Matrix.mulVec, dotProduct]
    rw [hm]
    linear_combination (-1 : ℂ) * h c
  have hx : Ring.inverse (1 - (u : ℂ) • X) *ᵥ R = x := by
    rw [hy, Matrix.mulVec_mulVec, Ring.inverse_mul_cancel _ hU, Matrix.one_mulVec]
  have hK : 0 ≤ K := (norm_nonneg _).trans (hR a)
  rw [← hx]
  calc ‖(Ring.inverse (1 - (u : ℂ) • X) *ᵥ R) a‖ = ‖∑ b, Ring.inverse (1 - (u : ℂ) • X) a b * R b‖ := rfl
    _ ≤ ∑ b, ‖Ring.inverse (1 - (u : ℂ) • X) a b‖ * K := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hR b) (norm_nonneg _)
    _ = (∑ b, ‖Ring.inverse (1 - (u : ℂ) • X) a b‖) * K := by rw [Finset.sum_mul]
    _ ≤ Cs * K := mul_le_mul_of_nonneg_right (hrow a) hK

end Ward

section Mss

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **`‖M^{(++)}‖_∞ ≤ 1`** from the Ward identity and the block average `= m`, `Im m = Im w`:
`Σ_q |M^{(++)}_{aq}| ≤ W^{-d} Σ_{x∈[a]} Σ_y |M_{yx}| |M_{xy}| ≤ W^{-d} Σ_{x∈[a]} Im M_xx / Im w = 1`. -/
private theorem ExpAvgGen_Mss_row {H₀ Mf : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H₀.IsHermitian) {w m : ℂ}
    (hM : (H₀ - w • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * Mf = 1) (hmim : m.im = w.im) (hb : 0 < w.im)
    (hm : ∀ a : Zd d L, ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, Mf x x = m) (a : Zd d L) :
    ∑ q : Zd d L, ‖((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mf y x * Mf x y‖ ≤ 1 := by
  classical
  have hWc : (((W : ℝ) ^ d)⁻¹ : ℝ) = ‖((W : ℂ) ^ d)⁻¹‖ := by simp
  set c : ℝ := ((W : ℝ) ^ d)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hward := fun x => ExpAvgGen_ward hH hM x
  have hA : ∀ q : Zd d L, ‖((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mf y x * Mf x y‖ ≤
      c * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, ‖Mf y x‖ * ‖Mf x y‖ := by
    intro q
    rw [norm_mul, ← hWc]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)) hc0
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul]
  have hB : ∑ q : Zd d L, c * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, ‖Mf y x‖ * ‖Mf x y‖ =
      c * ∑ x ∈ Iblk d L W a, ∑ y, ‖Mf y x‖ * ‖Mf x y‖ := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Finset.sum_fiberwise (Finset.univ : Finset (Idx d L W)) (fun y => (split d L W y).1) (fun y => ‖Mf y x‖ * ‖Mf x y‖)
  have hC : ∀ x : Idx d L W, ∑ y, ‖Mf y x‖ * ‖Mf x y‖ ≤ (Mf x x).im / w.im := by
    intro x
    have h1 : ∑ y, ‖Mf y x‖ * ‖Mf x y‖ ≤ ∑ y, (‖Mf y x‖ ^ 2 + ‖Mf x y‖ ^ 2) / 2 :=
      Finset.sum_le_sum fun y _ => by nlinarith [sq_nonneg (‖Mf y x‖ - ‖Mf x y‖)]
    rw [← Finset.sum_div, Finset.sum_add_distrib] at h1
    rw [le_div_iff₀ hb]
    have e1 := (hward x).1
    have e2 := (hward x).2
    nlinarith
  have hD : c * ∑ x ∈ Iblk d L W a, (Mf x x).im = m.im := by
    have := congrArg Complex.im (hm a)
    rw [← this]
    have e : ((W : ℂ) ^ d)⁻¹ = ((c : ℝ) : ℂ) := by simp [hc]
    rw [e, Complex.im_ofReal_mul, Complex.im_sum]
  calc ∑ q : Zd d L, ‖((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, Mf y x * Mf x y‖
      ≤ ∑ q : Zd d L, c * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W q, ‖Mf y x‖ * ‖Mf x y‖ := Finset.sum_le_sum fun q _ => hA q
    _ = c * ∑ x ∈ Iblk d L W a, ∑ y, ‖Mf y x‖ * ‖Mf x y‖ := hB
    _ ≤ c * ∑ x ∈ Iblk d L W a, (Mf x x).im / w.im := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hC x) hc0
    _ = 1 := by
        rw [← Finset.sum_div, ← mul_div_assoc, hD, hmim, div_self hb.ne']


/-- `|M_xy| ≤ (Im w)⁻¹` for `M = (H₀ - w)⁻¹` (Ward identity). -/
private theorem ExpAvgGen_M_entry {ι : Type*} [Fintype ι] [DecidableEq ι] {H₀ Mf : Matrix ι ι ℂ} (hH : H₀.IsHermitian) {w : ℂ}
    (hb : 0 < w.im) (hM : (H₀ - w • (1 : Matrix ι ι ℂ)) * Mf = 1) (x y : ι) : ‖Mf x y‖ ≤ (w.im)⁻¹ := by
  have e := (ExpAvgGen_ward hH hM x).1
  have hsum : ∀ y, ‖Mf x y‖ ^ 2 ≤ ∑ y, ‖Mf x y‖ ^ 2 := fun y =>
    Finset.single_le_sum (f := fun y => ‖Mf x y‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have him : (Mf x x).im ≤ ‖Mf x x‖ := Complex.im_le_norm _
  have hS : ∑ y, ‖Mf x y‖ ^ 2 ≤ ‖Mf x x‖ / w.im := by
    rw [le_div_iff₀ hb, mul_comm]
    nlinarith
  have ht : ‖Mf x x‖ ≤ (w.im)⁻¹ := by
    have h1 : ‖Mf x x‖ ^ 2 ≤ ‖Mf x x‖ / w.im := (hsum x).trans hS
    rcases (norm_nonneg (Mf x x)).eq_or_lt with h | h
    · rw [← h]; exact inv_nonneg.2 hb.le
    · rw [pow_two, le_div_iff₀ hb] at h1
      rw [← one_div, le_div_iff₀ hb]
      have h3 : ‖Mf x x‖ * (‖Mf x x‖ * w.im) ≤ ‖Mf x x‖ * 1 := by nlinarith
      nlinarith [(mul_le_mul_iff_of_pos_left h).1 h3]
  have h2 : ‖Mf x y‖ ^ 2 ≤ ((w.im)⁻¹) ^ 2 := by
    calc ‖Mf x y‖ ^ 2 ≤ ‖Mf x x‖ / w.im := (hsum y).trans hS
      _ ≤ (w.im)⁻¹ / w.im := by gcongr
      _ = ((w.im)⁻¹) ^ 2 := by field_simp
  exact le_of_sq_le_sq h2 (inv_nonneg.2 hb.le)

end Mss

/-! ## 5. The carrier: loops and `t_{aq}` as functions of the Gaussian sample -/

section Carrier

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
  {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}

private theorem ExpAvgGen_Gf_cont {L W : ℕ} [NeZero L] [NeZero W] {H₀ : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H₀.IsHermitian) (u : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (x y : Idx d L W) : Continuous fun ω : Ω d L W => Gres (H₀ + Hflow d L W u ω) z true x y :=
  (continuous_apply y).comp ((continuous_apply x).comp (continuous_green_of_isHermitian (continuous_const.add (continuous_Hflow d L W u))
    (fun ω => hH.add (Hflow_isHermitian d L W u ω)) hz))

/-- `C.L` at `k = 1`, `σ = +`: `W^{-d} Σ_{x∈[q]} G_xx` of the fine matrix `H₀ + √u X` (`CltRepg`). -/
private theorem ExpAvgGen_L_eq (hR : CltRepg C μ H₀ g' E) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (q : Zd d (sz.L n)) :
    C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) q,
      Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ((sz.withLam g').slice n ω)) (ztOf (C.m n) (E n) u) true x x) := by
  rw [(hR.2.2 n u ω).2]
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [show (Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j) =
    Hflow d (sz.L n) (sz.W n) u ((sz.withLam g').slice n ω) from rfl, ExpAvgGen_Gres_blockMat, ExpAvgGen_trace_Eblk]

private theorem ExpAvgGen_tM_eq (hR : CltRepg C μ H₀ g' E) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (a q : Zd d (sz.L n)) :
    ExpAvgGen_tM C n u ω a q = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) q,
      C.M n x y * Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ((sz.withLam g').slice n ω)) (ztOf (C.m n) (E n) u) true y x := by
  unfold ExpAvgGen_tM
  simp only [(hR.2.2 n u ω).1]
  rfl

/-- The loop is a continuous function of the sample slice: measurable on the sequence space. -/
private theorem ExpAvgGen_L_meas (hR : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hz : (ztOf (C.m n) (E n) u).im ≠ 0) (q : Zd d (sz.L n)) :
    Measurable fun ω : sz.SeqΩ => C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω := by
  have hc : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) q,
      Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true x x) :=
    continuous_const.mul (continuous_finsetSum _ fun x _ => ExpAvgGen_Gf_cont (hR.2.1 n) u hz x x)
  simp only [ExpAvgGen_L_eq hR n u _ q]
  exact hc.measurable.comp ((sz.withLam g').measurable_slice n)

private theorem ExpAvgGen_tM_meas (hR : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hz : (ztOf (C.m n) (E n) u).im ≠ 0) (a q : Zd d (sz.L n)) :
    Measurable fun ω : sz.SeqΩ => ExpAvgGen_tM C n u ω a q := by
  have hc : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
      ∑ y ∈ Iblk d (sz.L n) (sz.W n) q, C.M n x y * Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true y x :=
    continuous_const.mul (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      continuous_const.mul (ExpAvgGen_Gf_cont (hR.2.1 n) u hz y x))
  simp only [ExpAvgGen_tM_eq hR n u _ a q]
  exact hc.measurable.comp ((sz.withLam g').measurable_slice n)

private theorem ExpAvgGen_int_slice (hR : CltRepg C μ H₀ g' E) (n : ℕ) {F : Ω d (sz.L n) (sz.W n) → ℂ} (hF : Continuous F) :
    ∫ ω, F ((sz.withLam g').slice n ω) ∂μ = ∫ ω', F ω' ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
  rw [hR.1]
  exact expAvg_integral_slice (sz.withLam g') n F hF.aestronglyMeasurable

/-- `ztOf m E u` has imaginary part `(1 - u) Im m`. -/
private theorem ExpAvgGen_zim {m : ℂ} (hm : 0 < m.im) (E : ℝ) {u : ℝ} (hu : u < 1) : 0 < (ztOf m E u).im := by
  rw [ztOf_im]
  exact mul_pos (by linarith) hm

/-- **The self-consistent identity at the carrier**: `𝔼 𝓛^{(1)}_{u,+,a} - m = u Σ_{p,q} S_{pq} 𝔼[t_{ap} (𝓛^{(1)}_{u,+,q} - m)]` (band `expAvg_selfcons`, `M = m`). -/
private theorem ExpAvgGen_selfcons (hR : CltRepg C μ H₀ g' E) (n : ℕ) (hW1 : ExpAvgGen_W1i C H₀ g' E n) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (him : 0 < (C.m n).im) (a : Zd d (sz.L n)) :
    (∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω ∂μ) - C.m n =
      (u : ℂ) * ∑ p : Zd d (sz.L n), ∑ q : Zd d (sz.L n), C.S n p q * ∫ ω, ExpAvgGen_tM C n u ω a p *
        (C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω - C.m n) ∂μ := by
  have hz := (ExpAvgGen_zim him (E n) hu1).ne'
  have hzim : (ztOf (C.m n) (E n) u).im ≠ 0 := hz
  have hM : (H₀ n - (ztOf (C.m n) (E n) u + (u : ℂ) * C.m n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) *
      Matrix.of (fun x y => C.M n x y) = 1 := by
    have e : ztOf (C.m n) (E n) u + (u : ℂ) * C.m n = (E n : ℂ) + C.m n := by simp only [ztOf]; ring
    rw [e]
    exact hW1.2.1
  have hfix := ExpAvgGen_selfcons_fixed (g' n) (sz.three_le_L n) (hR.2.1 n) hu0 hzim hM (fun a' => by simpa using hW1.2.2 a') a
  have eL : ∀ (q : Zd d (sz.L n)) (ω : sz.SeqΩ), C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) q,
        Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ((sz.withLam g').slice n ω)) (ztOf (C.m n) (E n) u) true x x :=
    fun q ω => ExpAvgGen_L_eq hR n u ω q
  have eT : ∀ (a q : Zd d (sz.L n)) (ω : sz.SeqΩ), ExpAvgGen_tM C n u ω a q =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) q,
        (Matrix.of (fun x y => C.M n x y)) x y * Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ((sz.withLam g').slice n ω))
          (ztOf (C.m n) (E n) u) true y x :=
    fun a q ω => ExpAvgGen_tM_eq hR n u ω a q
  have cG : ∀ x y : Idx d (sz.L n) (sz.W n), Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
      Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true x y := fun x y => ExpAvgGen_Gf_cont (hR.2.1 n) u hzim x y
  have cg : ∀ q : Zd d (sz.L n), Continuous fun ω' : Ω d (sz.L n) (sz.W n) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) q,
      Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true x x := fun q =>
    continuous_const.mul (continuous_finsetSum _ fun x _ => cG x x)
  have ct : ∀ a q : Zd d (sz.L n), Continuous fun ω' : Ω d (sz.L n) (sz.W n) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
      ∑ y ∈ Iblk d (sz.L n) (sz.W n) q, (Matrix.of (fun x y => C.M n x y)) x y *
        Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true y x := fun a q =>
    continuous_const.mul (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => continuous_const.mul (cG y x))
  have h1 : (∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω ∂μ) = ∫ ω' : Ω d (sz.L n) (sz.W n),
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
        Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true x x ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
    simp only [eL a]
    exact ExpAvgGen_int_slice hR n (cg a)
  have h2 : ∀ p q : Zd d (sz.L n), (∫ ω, ExpAvgGen_tM C n u ω a p * (C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω - C.m n) ∂μ) =
      ∫ ω' : Ω d (sz.L n) (sz.W n), ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p,
        (Matrix.of (fun x y => C.M n x y)) x y * Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true y x) *
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) q,
          Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ω') (ztOf (C.m n) (E n) u) true x x - C.m n) ∂(PF d (sz.L n) (sz.W n) (g' n)) := by
    intro p q
    simp only [eL q, eT a p]
    exact ExpAvgGen_int_slice hR n ((ct a p).mul ((cg q).sub continuous_const))
  rw [h1]
  simp only [h2, hW1.1]
  exact hfix

private theorem ExpAvgGen_prob (hR : CltRepg C μ H₀ g' E) : IsProbabilityMeasure μ := by
  rw [hR.1]
  exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')

/-- Average of `W^d` terms bounded by `B`. -/
private theorem ExpAvgGen_avg_le {ι : Type*} (W : ℕ) [NeZero W] (S : Finset ι) (hS : S.card = W ^ d) {f : ι → ℂ} {B : ℝ}
    (hB : ∀ x ∈ S, ‖f x‖ ≤ B) : ‖(((W : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ S, f x‖ ≤ B := by
  have hW : (0 : ℝ) < ((W : ℕ) : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)) d
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have h1 : ‖∑ x ∈ S, f x‖ ≤ ((W : ℕ) : ℝ) ^ d * B := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hB).trans ?_)
    rw [Finset.sum_const, hS, nsmul_eq_mul]
    push_cast
    exact le_rfl
  calc (((W : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ x ∈ S, f x‖ ≤ (((W : ℕ) : ℝ) ^ d)⁻¹ * (((W : ℕ) : ℝ) ^ d * B) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hW.le)
    _ = B := by field_simp

/-- The fine resolvent entries are bounded by `1/|Im z|`. -/
private theorem ExpAvgGen_Gf_le {L W : ℕ} [NeZero L] [NeZero W] {H₀ : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H₀.IsHermitian) (u : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (ω : Ω d L W) (x y : Idx d L W) : ‖Gres (H₀ + Hflow d L W u ω) z true x y‖ ≤ |z.im|⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (norm_Gsig_le_inv_eta (hH.add (Hflow_isHermitian d L W u ω)) (abs_pos.mpr hz) le_rfl true)

/-- `‖𝓛^{(1)}_{u,+,q}‖ ≤ η_u⁻¹`. -/
private theorem ExpAvgGen_L_le (hR : CltRepg C μ H₀ g' E) (n : ℕ) {u : ℝ} (hz : (ztOf (C.m n) (E n) u).im ≠ 0) (ω : sz.SeqΩ)
    (q : Zd d (sz.L n)) : ‖C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω‖ ≤ |(ztOf (C.m n) (E n) u).im|⁻¹ := by
  rw [ExpAvgGen_L_eq hR n u ω q]
  exact ExpAvgGen_avg_le (sz.W n) _ (card_Iblk d (sz.L n) (sz.W n) q) fun x _ => ExpAvgGen_Gf_le (hR.2.1 n) u hz _ x x

/-- `‖t_{aq}‖ ≤ W^d (Im w)⁻¹ η_u⁻¹`, `w = E + m`. -/
private theorem ExpAvgGen_tM_le (hR : CltRepg C μ H₀ g' E) (n : ℕ) (hW1 : ExpAvgGen_W1i C H₀ g' E n) {u : ℝ} (hu1 : u < 1)
    (him : 0 < (C.m n).im) (ω : sz.SeqΩ) (a q : Zd d (sz.L n)) :
    ‖ExpAvgGen_tM C n u ω a q‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((C.m n).im)⁻¹ * |(ztOf (C.m n) (E n) u).im|⁻¹) := by
  have hz := (ExpAvgGen_zim him (E n) hu1).ne'
  have hb : 0 < ((E n : ℂ) + C.m n).im := by simpa using him
  rw [ExpAvgGen_tM_eq hR n u ω a q]
  refine ExpAvgGen_avg_le (sz.W n) _ (card_Iblk d (sz.L n) (sz.W n) a) fun x _ => ?_
  have hsum : ‖∑ y ∈ Iblk d (sz.L n) (sz.W n) q, C.M n x y * Gres (H₀ n + Hflow d (sz.L n) (sz.W n) u ((sz.withLam g').slice n ω))
      (ztOf (C.m n) (E n) u) true y x‖ ≤ ((Iblk d (sz.L n) (sz.W n) q).card : ℝ) * (((C.m n).im)⁻¹ * |(ztOf (C.m n) (E n) u).im|⁻¹) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun y _ => ?_).trans (by rw [Finset.sum_const, nsmul_eq_mul]))
    rw [norm_mul]
    exact mul_le_mul (by simpa using ExpAvgGen_M_entry (hR.2.1 n) hb hW1.2.1 x y) (ExpAvgGen_Gf_le (hR.2.1 n) u hz _ y x)
      (norm_nonneg _) (inv_nonneg.2 him.le)
  rw [card_Iblk] at hsum
  simpa using hsum

end Carrier

/-! ## 6. The deterministic core at one size index -/

section Core

variable {Ω' ι : Type*} [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι] {P : Measure Ω'}

/-- Cauchy-Schwarz in the form `∫ f h ≤ α β` for `∫ f² ≤ α²`, `∫ h² ≤ β²` (AM-GM with the weight `β/α`). -/
private theorem ExpAvgGen_cs {f h : Ω' → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hh0 : ∀ ω, 0 ≤ h ω) (hf2 : Integrable (fun ω => f ω ^ 2) P)
    (hh2 : Integrable (fun ω => h ω ^ 2) P) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hfα : ∫ ω, f ω ^ 2 ∂P ≤ α ^ 2)
    (hhβ : ∫ ω, h ω ^ 2 ∂P ≤ β ^ 2) : ∫ ω, f ω * h ω ∂P ≤ α * β := by
  have hg : Integrable (fun ω => (β / α * f ω ^ 2 + α / β * h ω ^ 2) / 2) P := ((hf2.const_mul _).add (hh2.const_mul _)).div_const _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => mul_nonneg (hf0 ω) (hh0 ω)) hg
    (Filter.Eventually.of_forall fun ω => ?_)).trans ?_
  · have key : β / α * f ω ^ 2 + α / β * h ω ^ 2 - 2 * (f ω * h ω) = (β * f ω - α * h ω) ^ 2 / (α * β) := by
      field_simp
      ring
    have : 0 ≤ (β * f ω - α * h ω) ^ 2 / (α * β) := by positivity
    linarith
  · rw [integral_div, integral_add (hf2.const_mul _) (hh2.const_mul _), integral_const_mul, integral_const_mul]
    have e1 : β / α * ∫ ω, f ω ^ 2 ∂P ≤ β / α * α ^ 2 := mul_le_mul_of_nonneg_left hfα (by positivity)
    have e2 : α / β * ∫ ω, h ω ^ 2 ∂P ≤ α / β * β ^ 2 := mul_le_mul_of_nonneg_left hhβ (by positivity)
    have e3 : β / α * α ^ 2 + α / β * β ^ 2 = 2 * (α * β) := by field_simp; ring
    linarith

/-- **The deterministic core** (abstract): the self-consistent identity `x = u M S x + R`, the second-moment bounds `α`, `β` of `𝓛 - m`, `t - M^{(++)}`
and the invertibility of `1 - u M^{(++)} S` with the row bound `Cs` of its inverse give `|x_a| ≤ Cs u α Bs`. -/
private theorem ExpAvgGen_core_abs [IsProbabilityMeasure P] {Lf : ι → Ω' → ℂ} {Tf : ι → ι → Ω' → ℂ} {m : ℂ} {Ms S : Matrix ι ι ℂ} {u : ℝ}
    {BL BT BM : ℝ} (hLm : ∀ q, Measurable (Lf q)) (hLb : ∀ q ω, ‖Lf q ω‖ ≤ BL) (hTm : ∀ a p, Measurable (Tf a p))
    (hTb : ∀ a p ω, ‖Tf a p ω‖ ≤ BT) (hMs : ∀ a p, ‖Ms a p‖ ≤ BM) (hS : ∀ p, ∑ q, ‖S p q‖ = 1)
    (hid : ∀ a, (∫ ω, Lf a ω ∂P) - m = (u : ℂ) * ∑ p, ∑ q, S p q * ∫ ω, Tf a p ω * (Lf q ω - m) ∂P)
    (hU : IsUnit (1 - (u : ℂ) • (Ms * S))) {Cs : ℝ} (hCs : ∀ a, ∑ b, ‖Ring.inverse (1 - (u : ℂ) • (Ms * S)) a b‖ ≤ Cs)
    {α : ℝ} (hα : 0 < α) (hL2 : ∀ q, ∫ ω, ‖Lf q ω - m‖ ^ 2 ∂P ≤ α ^ 2)
    {β : ι → ι → ℝ} (hβ : ∀ a p, 0 < β a p) (hT2 : ∀ a p, ∫ ω, ‖Tf a p ω - Ms a p‖ ^ 2 ∂P ≤ β a p ^ 2)
    {Bs : ℝ} (hBs : ∀ a, ∑ p, β a p ≤ Bs) (hu0 : 0 ≤ u) (a : ι) :
    ‖(∫ ω, Lf a ω ∂P) - m‖ ≤ Cs * (u * α * Bs) := by
  have hint1 : ∀ q, Integrable (Lf q) P := fun q => Integrable.of_bound (hLm q).aestronglyMeasurable BL (Filter.Eventually.of_forall (hLb q))
  have hxq : ∀ q, ∫ ω, (Lf q ω - m) ∂P = (∫ ω, Lf q ω ∂P) - m := fun q => by
    rw [integral_sub (hint1 q) (integrable_const m), integral_const]
    simp
  have hfm : ∀ q, ∀ ω, ‖Lf q ω - m‖ ≤ BL + ‖m‖ := fun q ω => (norm_sub_le _ _).trans (add_le_add (hLb q ω) le_rfl)
  have hhm : ∀ a p, ∀ ω, ‖Tf a p ω - Ms a p‖ ≤ BT + BM := fun a p ω => (norm_sub_le _ _).trans (add_le_add (hTb a p ω) (hMs a p))
  have hint2 : ∀ a p q, Integrable (fun ω => (Tf a p ω - Ms a p) * (Lf q ω - m)) P := fun a p q =>
    Integrable.of_bound (((hTm a p).sub_const _).mul ((hLm q).sub_const _)).aestronglyMeasurable ((BT + BM) * (BL + ‖m‖))
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_mul]
        exact mul_le_mul (hhm a p ω) (hfm q ω) (norm_nonneg _) ((norm_nonneg _).trans (hhm a p ω)))
  have hsplit : ∀ a p q, ∫ ω, Tf a p ω * (Lf q ω - m) ∂P =
      (∫ ω, (Tf a p ω - Ms a p) * (Lf q ω - m) ∂P) + Ms a p * ((∫ ω, Lf q ω ∂P) - m) := by
    intro a p q
    have e : ∀ ω, Tf a p ω * (Lf q ω - m) = (Tf a p ω - Ms a p) * (Lf q ω - m) + Ms a p * (Lf q ω - m) := fun ω => by ring
    have i3 : Integrable (fun ω => Ms a p * (Lf q ω - m)) P := ((hint1 q).sub (integrable_const m)).const_mul _
    simp only [e]
    rw [integral_add (hint2 a p q) i3, integral_const_mul, hxq]
  set J : ι → ι → ι → ℂ := fun a p q => ∫ ω, (Tf a p ω - Ms a p) * (Lf q ω - m) ∂P with hJ
  set R : ι → ℂ := fun a => (u : ℂ) * ∑ p, ∑ q, S p q * J a p q with hRdef
  have hx : ∀ a, (∫ ω, Lf a ω ∂P) - m = (u : ℂ) * ∑ b, (Ms * S) a b * ((∫ ω, Lf b ω ∂P) - m) + R a := by
    intro a
    rw [hid a]
    simp only [hsplit, hRdef, hJ, mul_add, Finset.sum_add_distrib]
    have e : ∑ b, (Ms * S) a b * ((∫ ω, Lf b ω ∂P) - m) =
        ∑ p, ∑ q, S p q * (Ms a p * ((∫ ω, Lf q ω ∂P) - m)) := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => by ring
    rw [e]
    ring
  have hJb : ∀ a p q, ‖J a p q‖ ≤ α * β a p := by
    intro a p q
    refine (norm_integral_le_integral_norm _).trans ?_
    have h1 : ∫ ω, ‖(Tf a p ω - Ms a p) * (Lf q ω - m)‖ ∂P = ∫ ω, ‖Lf q ω - m‖ * ‖Tf a p ω - Ms a p‖ ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [norm_mul, mul_comm]
    rw [h1]
    refine ExpAvgGen_cs (fun ω => norm_nonneg _) (fun ω => norm_nonneg _) ?_ ?_ hα (hβ a p) (hL2 q) (hT2 a p)
    · exact Integrable.of_bound ((((hLm q).sub_const _).norm.pow_const 2).aestronglyMeasurable) ((BL + ‖m‖) ^ 2)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hfm q ω) 2)
    · exact Integrable.of_bound ((((hTm a p).sub_const _).norm.pow_const 2).aestronglyMeasurable) ((BT + BM) ^ 2)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hhm a p ω) 2)
  have hRb : ∀ a, ‖R a‖ ≤ u * α * Bs := by
    intro a
    have hua : 0 ≤ u * α := mul_nonneg hu0 hα.le
    calc ‖R a‖ = u * ‖∑ p, ∑ q, S p q * J a p q‖ := by rw [hRdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      _ ≤ u * ∑ p, ∑ q, ‖S p q‖ * (α * β a p) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun q _ => ?_))) hu0
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hJb a p q) (norm_nonneg _)
      _ = u * ∑ p, α * β a p := by
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_mul, hS p, one_mul]
      _ = (u * α) * ∑ p, β a p := by rw [← Finset.mul_sum, mul_assoc]
      _ ≤ (u * α) * Bs := mul_le_mul_of_nonneg_left (hBs a) hua
  exact ExpAvgGen_solve hU hx hRb hCs a

end Core

section CoreCarrier

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
  {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}

/-- `Σ_q |M^{(++)}_{aq}| ≤ 1` at the carrier (`ExpAvgGen_Mss_row`). -/
private theorem ExpAvgGen_Mss_row_C (hR : CltRepg C μ H₀ g' E) (n : ℕ) (hW1 : ExpAvgGen_W1i C H₀ g' E n) (him : 0 < (C.m n).im)
    (a : Zd d (sz.L n)) : ∑ q, ‖Step2Kern_Mss C n true true a q‖ ≤ 1 := by
  have := ExpAvgGen_Mss_row (Mf := Matrix.of (fun x y => C.M n x y)) (hR.2.1 n) (w := (E n : ℂ) + C.m n) (m := C.m n) hW1.2.1
    (by simp) (by simpa using him) (fun a' => by simpa using hW1.2.2 a') a
  simpa [Step2Kern_Mss, Step2Kern_Msig] using this

/-- **The deterministic core at the carrier**: moment bounds `α`, `β` and the row bound `Cs` give `|𝔼 𝓛 - m| ≤ Cs u α Bs`. -/
private theorem ExpAvgGen_core (hR : CltRepg C μ H₀ g' E) (n : ℕ) (hW1 : ExpAvgGen_W1i C H₀ g' E n) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (him : 0 < (C.m n).im) {Cs : ℝ} (hCs : ∀ a, ∑ b, ‖Step2Gen_uKer C n true true 0 u a b‖ ≤ Cs)
    {α : ℝ} (hα : 0 < α) (hL2 : ∀ q, ∫ ω, ‖C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω - C.m n‖ ^ 2 ∂μ ≤ α ^ 2)
    {β : Zd d (sz.L n) → Zd d (sz.L n) → ℝ} (hβ : ∀ a p, 0 < β a p)
    (hT2 : ∀ a p, ∫ ω, ‖ExpAvgGen_tM C n u ω a p - Step2Kern_Mss C n true true a p‖ ^ 2 ∂μ ≤ β a p ^ 2)
    {Bs : ℝ} (hBs : ∀ a, ∑ p, β a p ≤ Bs) (a : Zd d (sz.L n)) :
    ‖(∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω ∂μ) - C.m n‖ ≤ Cs * (u * α * Bs) := by
  have := ExpAvgGen_prob hR
  have hz := (ExpAvgGen_zim him (E n) hu1).ne'
  have hS : ∀ p, ∑ q, ‖C.S n p q‖ = 1 := fun p => by
    rw [hW1.1]
    exact sum_norm_SB_row d (sz.L n) (g' n) (sz.three_le_L n) p
  have hMss : ∀ a p, ‖Step2Kern_Mss C n true true a p‖ ≤ 1 := fun a p =>
    (Finset.single_le_sum (f := fun q => ‖Step2Kern_Mss C n true true a q‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ p)).trans
      (ExpAvgGen_Mss_row_C hR n hW1 him a)
  have hrow : ∀ a, ∑ b, ‖(Step2Kern_Mss C n true true * C.S n) a b‖ ≤ 1 := by
    intro a
    calc ∑ b, ‖(Step2Kern_Mss C n true true * C.S n) a b‖ ≤ ∑ b, ∑ p, ‖Step2Kern_Mss C n true true a p‖ * ‖C.S n p b‖ :=
          Finset.sum_le_sum fun b _ => by
            rw [Matrix.mul_apply]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => (norm_mul _ _).le)
      _ = ∑ p, ‖Step2Kern_Mss C n true true a p‖ * ∑ b, ‖C.S n p b‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
      _ ≤ 1 := by
          simp only [hS, mul_one]
          exact ExpAvgGen_Mss_row_C hR n hW1 him a
  have hU := ExpAvgGen_isUnit_one_sub _ hu0 hu1 hrow
  have hker : Step2Gen_uKer C n true true 0 u = Ring.inverse (1 - (u : ℂ) • (Step2Kern_Mss C n true true * C.S n)) := by
    simp [Step2Gen_uKer, Step2Gen_Theta]
  exact ExpAvgGen_core_abs (BL := |(ztOf (C.m n) (E n) u).im|⁻¹)
    (BT := ((sz.W n : ℕ) : ℝ) ^ d * (((C.m n).im)⁻¹ * |(ztOf (C.m n) (E n) u).im|⁻¹)) (BM := 1)
    (fun q => ExpAvgGen_L_meas hR n hz q) (fun q ω => ExpAvgGen_L_le hR n hz ω q) (fun a p => ExpAvgGen_tM_meas hR n hz a p)
    (fun a p ω => ExpAvgGen_tM_le hR n hW1 hu1 him ω a p) hMss hS (fun a => ExpAvgGen_selfcons hR n hW1 hu0 hu1 him a) hU
    (by rw [← hker]; exact hCs) hα hL2 hβ hT2 hBs hu0 a

end CoreCarrier

/-! ## 7. The sequence part: the relative-envelope bridge `≺ ⇒ second moments` -/

section Sequence

/-- **Reverse bridge with an envelope relative to the control** (new; the merged `momentDomAt_of_stochDomAt_of_nonneg` needs `Y ≤ N^K`):
`Y ≺ ζ` and `Y ≤ K₀ N^K ζ` give `𝔼 Y² ≤ C N^ε ζ²` (apply the merged bridge to `Y/ζ ≺ 1`). -/
private theorem ExpAvgGen_moment {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P] {size : ℕ → ℕ}
    (hsize : Tendsto size atTop atTop) {U : ℕ → Type*} {Y : ∀ n, U n → Ω' → ℝ} {ζ : ∀ n, U n → ℝ}
    (hY0 : ∀ n u ω, 0 ≤ Y n u ω) (hmeas : ∀ n u, Measurable (Y n u)) (hζ : ∀ n u, 0 < ζ n u) {K0 K : ℝ} (hK0 : 0 ≤ K0) (hK : 0 ≤ K)
    (henv : ∀ n u ω, Y n u ω ≤ K0 * (size n : ℝ) ^ K * ζ n u) (hdom : StochDomAt P size Y (fun n u _ => ζ n u)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ u, ∫ ω, Y n u ω ^ 2 ∂P ≤ C * ((size n : ℝ) ^ ε * ζ n u ^ 2) := by
  have hsz' : ∀ᶠ n in atTop, K0 ≤ (size n : ℝ) := (tendsto_natCast_atTop_atTop.comp hsize).eventually_ge_atTop K0
  have hdom' : StochDomAt P size (fun n u ω => Y n u ω / ζ n u) (fun _ _ _ => (1 : ℝ)) := by
    refine StochDomAt.of_subset hdom fun τ hτ => ⟨τ, hτ, Filter.Eventually.of_forall fun n ω ⟨u, hu⟩ => ⟨u, ?_⟩⟩
    rw [mul_one, lt_div_iff₀ (hζ n u)] at hu
    exact hu
  have hmom := momentDomAt_of_stochDomAt_of_nonneg size hsize (Y := fun n u ω => Y n u ω / ζ n u) (Φ := fun _ _ => (1 : ℝ))
    (Env := fun n => K0 * (size n : ℝ) ^ K) (Kenv := K + 1) (B := 0) (fun n u ω => div_nonneg (hY0 n u ω) (hζ n u).le)
    (fun n u => (hmeas n u).div_const _) (fun _ _ => one_pos) le_rfl
    (Filter.Eventually.of_forall fun n u => by simp) (fun n => mul_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by linarith)
    (fun n u ω => by
      rw [div_le_iff₀ (hζ n u)]
      exact henv n u ω)
    (by
      filter_upwards [hsz', hsize.eventually (eventually_ge_atTop 1)] with n hn h1
      have h1' : (0 : ℝ) < (size n : ℝ) := by exact_mod_cast h1
      rw [Real.rpow_add_one h1'.ne', mul_comm]
      exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg h1'.le _))
    hdom'
  intro ε hε
  obtain ⟨C, hC, h⟩ := hmom ε hε 1
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with n hn u
  have h1 := hn u
  simp only [Nat.cast_one, mul_one, one_pow, pow_one] at h1
  have e : ∀ ω, Y n u ω ^ 2 = ζ n u ^ 2 * |Y n u ω / ζ n u| ^ 2 := fun ω => by
    rw [sq_abs, div_pow]
    field_simp [(hζ n u).ne']
  simp only [e]
  rw [integral_const_mul]
  calc ζ n u ^ 2 * ∫ ω, |Y n u ω / ζ n u| ^ 2 ∂P ≤ ζ n u ^ 2 * (C * (size n : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = C * ((size n : ℝ) ^ ε * ζ n u ^ 2) := by ring

end Sequence

section Envelope

open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
  {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}

/-- **The floor** `(N (1 - u))⁻¹ ≤ W^{-d} B_{u,0}` (the second term of `Bctl`; band `expAvg_Bctl_ge` keeps `N⁻¹`). -/
private theorem ExpAvgGen_Bctl_floor (sz : Sizes d) (n : ℕ) {u : ℝ} (hu1 : u < 1) :
    (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ sz.Bctl n u := by
  have h1 : 0 < 1 - u := by linarith
  have hsize : ((sz.size n : ℕ) : ℝ) * (1 - u) = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u)) := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
    ring
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1, hsize, mul_inv]
  have h5 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) := by
    have : 0 < sz.lam n ^ 2 + (1 - u) := by positivity
    positivity
  rw [mul_add]
  linarith

private theorem ExpAvgGen_size_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

private theorem ExpAvgGen_Wd_le (sz : Sizes d) (n : ℕ) : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)
  exact_mod_cast Nat.pow_le_pow_left h1 d

/-- `(1 - u)⁻¹ ≤ N B` and `1 ≤ N B`. -/
private theorem ExpAvgGen_inv_le (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u := by
  have hN := ExpAvgGen_size_pos sz n
  have h1 : 0 < 1 - u := by linarith
  have h2 : (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u := by
    have := mul_le_mul_of_nonneg_left (ExpAvgGen_Bctl_floor sz n hu1) hN.le
    rwa [mul_inv, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
  exact ⟨h2, le_trans (one_le_inv_iff₀.2 ⟨h1, by linarith⟩) h2⟩

/-- **The envelopes along the flow** (`κm ≤ Im m`): `‖𝓛^{(1)} - m‖ ≤ (2/κm) N B` and `‖t - M^{(++)}‖ ≤ (κm⁻² + 1) N² B`. -/
private theorem ExpAvgGen_envelope (hR : CltRepg C μ H₀ g' E) (n : ℕ) (hW1 : ExpAvgGen_W1i C H₀ g' E n) {κm u : ℝ} (hκm : 0 < κm)
    (him : κm ≤ (C.m n).im) (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ) (a q : Zd d (sz.L n)) :
    ‖C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω - C.m n‖ ≤ (2 / κm) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) ∧
    ‖ExpAvgGen_tM C n u ω a q - Step2Kern_Mss C n true true a q‖ ≤
      (κm⁻¹ ^ 2 + 1) * (((sz.size n : ℕ) : ℝ) ^ 2 * sz.Bctl n u) := by
  have hb : 0 < (C.m n).im := hκm.trans_le him
  have hz := (ExpAvgGen_zim hb (E n) hu1).ne'
  have hη : |(ztOf (C.m n) (E n) u).im|⁻¹ ≤ κm⁻¹ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) := by
    rw [ztOf_im, etaOf, abs_of_pos (mul_pos (by linarith) hb), mul_inv, mul_comm]
    exact mul_le_mul (inv_anti₀ hκm him |>.trans le_rfl) (ExpAvgGen_inv_le sz n hu0 hu1).1 (inv_nonneg.2 (by linarith)) (inv_nonneg.2 hκm.le)
  have hNB := ExpAvgGen_inv_le sz n hu0 hu1
  have hN := ExpAvgGen_size_pos sz n
  have hm : ‖C.m n‖ ≤ κm⁻¹ := by
    have := ExpAvgGen_avg_le (sz.W n) (Iblk d (sz.L n) (sz.W n) 0) (card_Iblk d (sz.L n) (sz.W n) 0)
      (f := fun x => C.M n x x) (B := ((E n : ℂ) + C.m n).im⁻¹) fun x _ => by
        simpa using ExpAvgGen_M_entry (hR.2.1 n) (w := (E n : ℂ) + C.m n) (by simpa using hb) hW1.2.1 x x
    rw [hW1.2.2 0] at this
    simpa using this.trans (inv_anti₀ hκm (by simpa using him))
  have hmN : κm⁻¹ ≤ κm⁻¹ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) := le_mul_of_one_le_right (inv_nonneg.2 hκm.le) hNB.2
  refine ⟨?_, ?_⟩
  · calc ‖C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω - C.m n‖ ≤ ‖C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω‖ + ‖C.m n‖ := norm_sub_le _ _
      _ ≤ κm⁻¹ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) + κm⁻¹ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) :=
          add_le_add ((ExpAvgGen_L_le hR n hz ω q).trans hη) (hm.trans hmN)
      _ = (2 / κm) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) := by ring
  · have h1 := ExpAvgGen_tM_le hR n hW1 hu1 hb ω a q
    have h2 : ‖Step2Kern_Mss C n true true a q‖ ≤ 1 :=
      (Finset.single_le_sum (f := fun q' => ‖Step2Kern_Mss C n true true a q'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ q)).trans
        (ExpAvgGen_Mss_row_C hR n hW1 hb a)
    have hbinv : ((C.m n).im)⁻¹ ≤ κm⁻¹ := inv_anti₀ hκm him
    have h3 : ((sz.W n : ℕ) : ℝ) ^ d * (((C.m n).im)⁻¹ * |(ztOf (C.m n) (E n) u).im|⁻¹) ≤
        ((sz.size n : ℕ) : ℝ) * (κm⁻¹ * (κm⁻¹ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u))) :=
      mul_le_mul (ExpAvgGen_Wd_le sz n) (mul_le_mul hbinv hη (by positivity) (inv_nonneg.2 hκm.le)) (by positivity) hN.le
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have h4 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u) := by
      nlinarith [hNB.2]
    calc ‖ExpAvgGen_tM C n u ω a q - Step2Kern_Mss C n true true a q‖ ≤ ‖ExpAvgGen_tM C n u ω a q‖ + ‖Step2Kern_Mss C n true true a q‖ := norm_sub_le _ _
      _ ≤ ((sz.size n : ℕ) : ℝ) * (κm⁻¹ * (κm⁻¹ * (((sz.size n : ℕ) : ℝ) * sz.Bctl n u))) + 1 := add_le_add (h1.trans h3) h2
      _ ≤ (κm⁻¹ ^ 2 + 1) * (((sz.size n : ℕ) : ℝ) ^ 2 * sz.Bctl n u) := by
          have hB : 0 ≤ sz.Bctl n u := (ExpAvgGen_Bctl_floor sz n hu1).trans' (by positivity)
          nlinarith [mul_nonneg hB (sq_nonneg κm⁻¹), mul_nonneg hB hN.le]

end Envelope

section Step

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {μ : Measure sz.SeqΩ}
  {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}

/-- `𝓛^{(1)}_{u,-,a} = conj 𝓛^{(1)}_{u,+,a}` (`G(-) = G(+)^*`; band `ST_Lloop_one_false`). -/
private theorem ExpAvgGen_L_false (hR : CltRepg C μ H₀ g' E) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)) :
    C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω = (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω) := by
  have hH : (blockMat d (sz.L n) (sz.W n) (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)).IsHermitian :=
    ((hR.2.1 n).add ((sz.withLam g').seqHflow_isHermitian n u ω)).submatrix _
  rw [(hR.2.2 n u ω).2, (hR.2.2 n u ω).2]
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [ST_Gres_false hH]
  have hm : ∀ A : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ, Aᴴ * Eblk d (sz.L n) (sz.W n) a = (Eblk d (sz.L n) (sz.W n) a * A)ᴴ := fun A => by
    rw [Matrix.conjTranspose_mul, ST_Eblk_herm]
  rw [hm, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rfl

private theorem ExpAvgGen_card_Zd (L : ℕ) [NeZero L] : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
  simp [Zd, ZMod.card]

/-- **The per-index estimate** of 16a: all eventual quantities are hypotheses; the conclusion is `|𝔼 𝓛 - m| ≤ N^{3ε} B²`. -/
private theorem ExpAvgGen_step (hR : CltRepg C μ H₀ g' E) (n : ℕ) (hW1 : ExpAvgGen_W1i C H₀ g' E n) {u κm Cs CM ε C₁ C₂ : ℝ} (hκm : 0 < κm)
    (him : κm ≤ (C.m n).im) (hu0 : 0 ≤ u) (hu1 : u < 1) (hCs : ∀ a, ∑ b, ‖Step2Gen_uKer C n true true 0 u a b‖ ≤ Cs)
    (hCs0 : 0 ≤ Cs) (hCM : ∀ a, ∑ q, ‖ExpAvgGen_MB C n a q‖ ≤ CM) (hCM0 : 0 ≤ CM) (hε : 0 ≤ ε) (hC₁ : C₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε)
    (hC₂ : C₂ ≤ ((sz.size n : ℕ) : ℝ) ^ ε) (hCC : Cs * (CM + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ ε)
    (h1 : ∀ q, ∫ ω, ‖C.L n u (fun _ : Fin 1 => true) (fun _ => q) ω - C.m n‖ ^ 2 ∂μ ≤ C₁ * (((sz.size n : ℕ) : ℝ) ^ ε * sz.Bctl n u ^ 2))
    (h2 : ∀ a p, ∫ ω, ‖ExpAvgGen_tM C n u ω a p - Step2Kern_Mss C n true true a p‖ ^ 2 ∂μ ≤
      C₂ * (((sz.size n : ℕ) : ℝ) ^ ε * ((‖ExpAvgGen_MB C n a p‖ + (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹) * sz.Bctl n u) ^ 2)) (a : Zd d (sz.L n)) :
    ‖(∫ ω, C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω ∂μ) - C.m n‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (3 * ε) * sz.Bctl n u ^ 2 := by
  have hb : 0 < (C.m n).im := hκm.trans_le him
  have hBpos : 0 < sz.Bctl n u := STBctl_pos sz n hu1
  have hN := ExpAvgGen_size_pos sz n
  have hNε : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε := Real.rpow_nonneg hN.le _
  have hNε' : 0 < ((sz.size n : ℕ) : ℝ) ^ ε := Real.rpow_pos_of_pos hN _
  have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h1 : sz.L n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_left _ (sz.W_pos n)
    exact_mod_cast Nat.pow_le_pow_left h1 d
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set B : ℝ := sz.Bctl n u with hBdef
  have hζ : ∀ a p, 0 < (‖ExpAvgGen_MB C n a p‖ + (N ^ 2)⁻¹) * B := fun a p => mul_pos (by positivity) hBpos
  have hcore := ExpAvgGen_core hR n hW1 hu0 hu1 (hκm.trans_le him) hCs (α := N ^ ε * B) (by positivity)
    (fun q => (h1 q).trans (by
      calc C₁ * (N ^ ε * B ^ 2) ≤ N ^ ε * (N ^ ε * B ^ 2) := mul_le_mul_of_nonneg_right hC₁ (by positivity)
        _ = (N ^ ε * B) ^ 2 := by ring))
    (β := fun a p => N ^ ε * ((‖ExpAvgGen_MB C n a p‖ + (N ^ 2)⁻¹) * B)) (fun a p => mul_pos hNε' (hζ a p))
    (fun a p => (h2 a p).trans (by
      calc C₂ * (N ^ ε * ((‖ExpAvgGen_MB C n a p‖ + (N ^ 2)⁻¹) * B) ^ 2) ≤ N ^ ε * (N ^ ε * ((‖ExpAvgGen_MB C n a p‖ + (N ^ 2)⁻¹) * B) ^ 2) :=
            mul_le_mul_of_nonneg_right hC₂ (by positivity)
        _ = (N ^ ε * ((‖ExpAvgGen_MB C n a p‖ + (N ^ 2)⁻¹) * B)) ^ 2 := by ring))
    (Bs := N ^ ε * ((CM + 1) * B)) (fun a' => by
      have hsum : ∑ p, N ^ ε * ((‖ExpAvgGen_MB C n a' p‖ + (N ^ 2)⁻¹) * B) =
          N ^ ε * (B * (∑ p, ‖ExpAvgGen_MB C n a' p‖ + (Fintype.card (Zd d (sz.L n)) : ℝ) * (N ^ 2)⁻¹)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_congr rfl fun p _ => mul_comm (‖ExpAvgGen_MB C n a' p‖ + (N ^ 2)⁻¹) B, ← Finset.mul_sum, Finset.sum_add_distrib]
        simp
      rw [hsum]
      refine mul_le_mul_of_nonneg_left ?_ hNε
      rw [mul_comm (CM + 1) B]
      refine mul_le_mul_of_nonneg_left ?_ hBpos.le
      have hcard : (Fintype.card (Zd d (sz.L n)) : ℝ) ≤ N := by
        rw [ExpAvgGen_card_Zd]
        exact hLd
      have hN1 : (1 : ℝ) ≤ N := hN1'
      have h3 : (Fintype.card (Zd d (sz.L n)) : ℝ) * (N ^ 2)⁻¹ ≤ 1 := by
        calc (Fintype.card (Zd d (sz.L n)) : ℝ) * (N ^ 2)⁻¹ ≤ N * (N ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = N⁻¹ := by field_simp
          _ ≤ 1 := inv_le_one_of_one_le₀ hN1
      linarith [hCM a']) a
  refine hcore.trans ?_
  have hu1' : u ≤ 1 := hu1.le
  calc Cs * (u * (N ^ ε * B) * (N ^ ε * ((CM + 1) * B))) ≤ Cs * (1 * (N ^ ε * B) * (N ^ ε * ((CM + 1) * B))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu1' (by positivity)) (by positivity)) hCs0
    _ = (Cs * (CM + 1)) * (N ^ ε * N ^ ε) * B ^ 2 := by ring
    _ ≤ N ^ ε * (N ^ ε * N ^ ε) * B ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hCC le_rfl (by positivity) hNε) (by positivity)
    _ = N ^ (3 * ε) * B ^ 2 := by
        rw [show 3 * ε = ε + (ε + ε) by ring, Real.rpow_add hN, Real.rpow_add hN]


/-- A larger control dominates as well. -/
private theorem ExpAvgGen_dom_mono {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {size : ℕ → ℕ} {U : ℕ → Type*}
    {ξ : ∀ n, U n → Ω' → ℝ} {ζ ζ' : ∀ n, U n → ℝ} (hle : ∀ n u, ζ n u ≤ ζ' n u) (h : StochDomAt P size ξ (fun n u _ => ζ n u)) :
    StochDomAt P size ξ (fun n u _ => ζ' n u) :=
  StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Filter.Eventually.of_forall fun n ω ⟨u, hu⟩ =>
    ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩⟩

/-- The second moments of `𝓛^{(1)} - m` from `LWAvgLawgL` (the relative-envelope bridge with `‖𝓛 - m‖ ≤ (2/κm) N B`). -/
private theorem ExpAvgGen_mom1 (hR : CltRepg C μ H₀ g' E) (hW1 : ∀ n, ExpAvgGen_W1i C H₀ g' E n) {κm : ℝ} (hκm : 0 < κm)
    (him : ∀ n, κm ≤ (C.m n).im) {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hsize : Tendsto sz.size atTop atTop)
    (hLW : LWAvgLawgL C μ u) : ∀ ε' : ℝ, 0 < ε' → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ n in atTop, ∀ a : Zd d (sz.L n),
      ∫ ω, ‖C.L n (u n) (fun _ : Fin 1 => true) (fun _ => a) ω - C.m n‖ ^ 2 ∂μ ≤ C₁ * (((sz.size n : ℕ) : ℝ) ^ ε' * sz.Bctl n (u n) ^ 2) := by
  have := ExpAvgGen_prob hR
  have hz : ∀ n, (ztOf (C.m n) (E n) (u n)).im ≠ 0 := fun n => (ExpAvgGen_zim (hκm.trans_le (him n)) (E n) (hu1 n)).ne'
  exact ExpAvgGen_moment (P := μ) hsize (U := fun n => Zd d (sz.L n))
    (Y := fun n a ω => ‖C.L n (u n) (fun _ : Fin 1 => true) (fun _ => a) ω - C.m n‖) (ζ := fun n _ => sz.Bctl n (u n))
    (fun n a ω => norm_nonneg _) (fun n a => ((ExpAvgGen_L_meas hR n (hz n) a).sub_const _).norm) (fun n a => STBctl_pos sz n (hu1 n))
    (K0 := 2 / κm) (K := 1) (by positivity) zero_le_one
    (fun n a ω => by
      rw [Real.rpow_one, mul_assoc]
      exact (ExpAvgGen_envelope hR n (hW1 n) hκm (him n) (hu0 n) (hu1 n) ω 0 a).1)
    hLW

/-- The second moments of `t - M^{(++)}` from W1 (iii) (control `(‖M^{(B)}‖ + N^{-2}) B`, envelope `(κm⁻² + 1) N² B ≤ (κm⁻² + 1) N⁴ (N^{-2} B)`). -/
private theorem ExpAvgGen_mom2 (hR : CltRepg C μ H₀ g' E) (hW1 : ∀ n, ExpAvgGen_W1i C H₀ g' E n) {κm : ℝ} (hκm : 0 < κm)
    (him : ∀ n, κm ≤ (C.m n).im) {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n < 1) (hsize : Tendsto sz.size atTop atTop)
    (hiii : ExpAvgGen_W1iii C μ u) : ∀ ε' : ℝ, 0 < ε' → ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ᶠ n in atTop, ∀ p : Zd d (sz.L n) × Zd d (sz.L n),
      ∫ ω, ‖ExpAvgGen_tM C n (u n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖ ^ 2 ∂μ ≤
        C₂ * (((sz.size n : ℕ) : ℝ) ^ ε' * ((‖ExpAvgGen_MB C n p.1 p.2‖ + (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹) * sz.Bctl n (u n)) ^ 2) := by
  have := ExpAvgGen_prob hR
  have hz : ∀ n, (ztOf (C.m n) (E n) (u n)).im ≠ 0 := fun n => (ExpAvgGen_zim (hκm.trans_le (him n)) (E n) (hu1 n)).ne'
  have hBpos : ∀ n, 0 < sz.Bctl n (u n) := fun n => STBctl_pos sz n (hu1 n)
  have hNpos : ∀ n, (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := fun n => ExpAvgGen_size_pos sz n
  have hle : ∀ (n : ℕ) (p : Zd d (sz.L n) × Zd d (sz.L n)), ‖ExpAvgGen_MB C n p.1 p.2‖ * sz.Bctl n (u n) ≤
      (‖ExpAvgGen_MB C n p.1 p.2‖ + (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹) * sz.Bctl n (u n) := fun n p =>
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (inv_nonneg.2 (sq_nonneg _))) (hBpos n).le
  have hiii' : StochDomAt μ sz.size (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖ExpAvgGen_tM C n (u n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖)
      (fun n p _ => ‖ExpAvgGen_MB C n p.1 p.2‖ * sz.Bctl n (u n)) := hiii
  have hdom2 := ExpAvgGen_dom_mono hle hiii'
  have henv : ∀ (n : ℕ) (p : Zd d (sz.L n) × Zd d (sz.L n)) (ω : sz.SeqΩ),
      ‖ExpAvgGen_tM C n (u n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖ ≤ (κm⁻¹ ^ 2 + 1) * ((sz.size n : ℝ) ^ (4 : ℝ)) *
        ((‖ExpAvgGen_MB C n p.1 p.2‖ + (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹) * sz.Bctl n (u n)) := by
    intro n p ω
    have h := (ExpAvgGen_envelope hR n (hW1 n) hκm (him n) (hu0 n) (hu1 n) ω p.1 p.2).2
    have hN := hNpos n
    have hB := hBpos n
    refine h.trans ?_
    rw [show ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 4 by norm_num, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : ((sz.size n : ℕ) : ℝ) ^ 2 * sz.Bctl n (u n) = ((sz.size n : ℕ) : ℝ) ^ 4 * ((((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ * sz.Bctl n (u n)) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) hB.le
  have hmeas : ∀ (n : ℕ) (p : Zd d (sz.L n) × Zd d (sz.L n)), Measurable fun ω : sz.SeqΩ =>
      ‖ExpAvgGen_tM C n (u n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖ := fun n p =>
    ((ExpAvgGen_tM_meas hR n (hz n) p.1 p.2).sub_const _).norm
  have hζ : ∀ (n : ℕ) (p : Zd d (sz.L n) × Zd d (sz.L n)),
      0 < (‖ExpAvgGen_MB C n p.1 p.2‖ + (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹) * sz.Bctl n (u n) := fun n p =>
    mul_pos (add_pos_of_nonneg_of_pos (norm_nonneg _) (inv_pos.2 (pow_pos (hNpos n) 2))) (hBpos n)
  exact ExpAvgGen_moment (P := μ) hsize (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (Y := fun n p ω => ‖ExpAvgGen_tM C n (u n) ω p.1 p.2 - Step2Kern_Mss C n true true p.1 p.2‖)
    (ζ := fun n p => (‖ExpAvgGen_MB C n p.1 p.2‖ + (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹) * sz.Bctl n (u n))
    (fun n p ω => norm_nonneg _) hmeas hζ (K0 := κm⁻¹ ^ 2 + 1) (K := 4) (by positivity) (by norm_num) henv hdom2

end Step

/-! ## 8. Targets 16a, 16b, 16c -/

/-- **Target 16a** (`stImproveCoregL_of`): `lem:improve_exp_aver` over the carrier tuple, per time, from the family texts rows 9 + 14 (with (iv)) and the
flow facts (row 3 of the family table).  Stein at `H₀ + √u X` and `M`, inversion by `Step2Gen_uKer C n + +` (W1 (ii)), the remainder by W1 (iii), (iv)
and the second moments of `LWAvgLawgL`; the premise `STLKgL` is unused, as in the band. -/
theorem stImproveCoregL_of {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} (hFF : Step5CasesGen_FlowFacts d Flow mk T0) :
    ExpAvgGen_W1fam d law Flow mk → STImproveCoregL d law Flow mk T0 := by
  intro hW1 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 huT hLW _hLK hiii
  obtain ⟨Cs, CM, hCs0, hCM0, hfam⟩ := hW1 hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨H₀, g', E, hR, hW1i, hW1ii, hW1iv⟩ := hfam 𝔠 sz z hflow
  obtain ⟨κm, hκm, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, himm, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hsz
  have hu1 : ∀ n, u n < 1 := fun n => (huT n).trans_lt (hT0 n)
  have hμ : IsProbabilityMeasure (law sz) := ExpAvgGen_prob hR
  have hM1 := ExpAvgGen_mom1 hR hW1i hκm himm hu0 hu1 hsize hLW
  have hM2 := ExpAvgGen_mom2 hR hW1i hκm himm hu0 hu1 hsize hiii
  unfold STExpAvgAtgL
  rw [st6_prec_det_iffg sz (law sz) hμ hsz]
  intro τ hτ
  have hε3 : 0 < τ / 3 := by positivity
  obtain ⟨C₁, hC₁, h1ev⟩ := hM1 (τ / 3) hε3
  obtain ⟨C₂, hC₂, h2ev⟩ := hM2 (τ / 3) hε3
  have hbig := ((tendsto_rpow_atTop hε3).comp hsz).eventually (eventually_ge_atTop (max (max C₁ C₂) (Cs * (CM + 1))))
  filter_upwards [h1ev, h2ev, hW1ii, hW1iv, hbig] with n h1 h2 h3 h4 hb
  intro v
  have hmain : ∀ a : Zd d (sz.L n), ‖(∫ ω, (mk sz z).L n (u n) (fun _ : Fin 1 => true) (fun _ => a) ω ∂(law sz)) - (mk sz z).m n‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n (u n) ^ 2 := by
    intro a
    have := ExpAvgGen_step hR n (hW1i n) hκm (himm n) (hu0 n) (hu1 n)
      (fun a' => h3 true 0 (u n) le_rfl (hu0 n) (hu1 n) a') hCs0.le (fun a' => h4 a') hCM0.le hε3.le
      ((le_max_left _ _).trans ((le_max_left _ _).trans hb)) ((le_max_right _ _).trans ((le_max_left _ _).trans hb)) ((le_max_right _ _).trans hb)
      h1 (fun a' p => h2 (a', p)) a
    rwa [show 3 * (τ / 3) = τ by ring] at this
  obtain ⟨σ, a⟩ := v
  cases σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp_rw [ExpAvgGen_L_false hR n (u n) _ a]
    rw [integral_conj, ← map_sub, Complex.norm_conj]
    exact hmain a
  · simpa using hmain a

/-! ## 9. The band discharge of the family texts (`bandFM`, `H₀ = 0`, `g' = sz.lam`) and the band pin through 16b -/

/-! ## 10. Compiled nonempty instances at `d = 3`, the band tuple `(sz0, z0)`, `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`, `u ≡ 1/16`

Every deterministic premise is discharged (`3 ≤ 3`, `0 < 1/10`, `flow_z0`, `0 ≤ 1/16 ≤ lemT`, the band texts); the stochastic pins `LWAvgLawgL`,
`STLKgL`, `ExpAvgGen_W1iii` (16a) and `STStep2CoregL`, `STLKUgL` (16c) stay hypotheses of the examples. -/

end RBM.BA
