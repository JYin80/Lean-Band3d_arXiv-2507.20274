/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.LoopGenN
import RBM3D.Induction.HierAlgebra
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.Split
import RBM3D.Path.LoopStep
import RBM3D.Path.UBounds
import RBM3D.Path.Stop

/-!
# One grid step of (`LK_SDE`) for general `n` and all `σ` (`d ≥ 3`)

Ticket T2111 (ST2-29, second file).  Port of `RBM2D/Induction/GridDriftN.lean` at commit `c9a24cf`
(cited `GDN:<line>`; 911 lines there).  Paper: arXiv:2507.20274, `3_5` (`LK_SDE`, `3_5:133`),
`def_Ustz`, `def_Ustz_2`, `pro_dyncalK`.

## Main results (namespace `RBM.Ind`)

* `kStepC`, `uStepC`, `stepErrN` : the explicit one-step error; `GridDriftN sz E s t K` : the pin
  (RBM2D `Induction/HierVocab.lean:421, 427, 432, 440`, defined here with the vocabulary of the
  merged files).
* `gridDriftN_at` : one grid step of (`LK_SDE`), with hypotheses only at the size index `n`
  (DECISIONS §29 (4), T2104c); `gridDriftN : GridDriftN sz E s t K`.
* `GridDriftN_exists_envelope` : a deterministic envelope `B_k` of `𝒦` on `[0, v]` exists for every
  `0 ≤ v < 1` (continuity of `𝒦` on `[0, 1)` and finiteness of the loops of length `≤ k`).
* `exists_norm_Kcal_le_win` : the envelope witness `‖𝒦_w(J)‖ ≤ N^τ η_v^{-m}` for `w ∈ [0, v_n]`,
  eventually in `n`, from the owed pin `STKbound` (paper-delta candidate T2111a, see below).

## Route and `d ≥ 3` changes (CLAUDE.md §5.2)

Proof of `gridDriftN_at`: `P_j - Δ D_j = R₁ - R_𝒦 - R_𝒰` (`gdn_algebra`), with `R₁` from the merged
`condExp_loop_drift` (`envConst d L W E k v Δ^{3/2}`, `envConst = 16 (k+3)^4 N^4 (1+η_v⁻¹)^{k+4}`,
`N = (W L)^d`), `R_𝒦` from `gdn_K_step` and `R_𝒰` from `gdn_Ugen_step_le`; the drift `D_j` is
supplied by `hierarchyN_holds` (T2103).  The `d`-dependent constants:

* `𝒦` step: `c = W^d k² L^d = N k²` (`norm_primBil_le`, `HierAlgebra.lean:254`, the bound
  `W^d n² L^d B_F B_G`), `kStepC = 2 c B (c B²) + c (c B²)²`;
* `𝒰` step: `uStepC k Δ v` is dimension-free (`k`, `Δ`, `v` only); the row bounds use
  `‖S^{(B)}‖ = 1` (`norm_SB`, `3 ≤ L`) and the propagator bounds, copied from the private helpers of
  `Path/UBounds.lean` (`sum_norm_row_le_opNorm`, `norm_Theta_le_of_lt`,
  `sum_norm_thetaGenMat_row_le`, `sum_norm_thetaGenMat_diff_row_le`) as private `gdn_` helpers;
* `stepErrN`: the sup bound on `A_j` is `η⁻ᵏ (W^{-d})^{k-1} + B_k` (`norm_gloop_le_of_le_abs_im`).

Vocabulary changes (DECISIONS §29, D185, D204): `thetaSig → ThetaN`, `Ugen d L g E σ v w` without
`[NeZero k]` (so `GridDriftN` drops RBM2D's `[NeZero k]`, stronger, T2111a), `KLoop.Kcal → KLK`,
`KLoop.primRhs → treeEqRhs`, `ksimLK/elklkN/egtN → STksimLKM/STelklkM/STegtM` at `H = pathH`,
`hierarchyN → hierarchyN_holds`.  The import cuts (portmap P.4): `Path/GoodEvent` is replaced by the
merged `walk_measurable_loopL`, `walk_measurable_blockMat`, `pathH_measurable_filt` (as T2104 in
`Path/DuhamelTail`); `Path/ScalesBridge` by the direct bound `Bctl ≤ 2 η_v⁻¹` (`gdn_Bctl_le`);
`Loop/KBound` (`Kbound_prec_uncond`) has no RBM3D counterpart and is replaced by the owed pin
`STKbound` (`Induction/Defs.lean`).

Every unpinned helper is `private` and carries the prefix `gdn_` or `GridDriftN_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The abstract `k`-slot tensor step -/

section TensorStep

variable {d L : ℕ} [NeZero L]

/-- `(⊗_i U_i) A` at `x`: `Σ_y (Π_i U_i(x_i, y_i)) A(y)`. -/
private def gdnTens {k : ℕ} (U : Fin k → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin k → Zd d L) → ℂ)
    (x : Fin k → Zd d L) : ℂ :=
  ∑ y : Fin k → Zd d L, (∏ i, U i (x i) (y i)) * A y

/-- `(Σ_i (1 ⊗ ⋯ ⊗ G_i ⊗ ⋯ ⊗ 1)) A` at `x`. -/
private def gdnGen {k : ℕ} (G : Fin k → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin k → Zd d L) → ℂ)
    (x : Fin k → Zd d L) : ℂ :=
  ∑ i : Fin k, ∑ c : Zd d L, G i (x i) c * A (Function.update x i c)

private theorem gdnTens_zero (U : Fin 0 → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin 0 → Zd d L) → ℂ)
    (x : Fin 0 → Zd d L) : gdnTens U A x = A x := by
  unfold gdnTens
  rw [Finset.sum_eq_single x (fun y _ hy => absurd (Subsingleton.elim y x) hy)
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem gdnGen_zero (G : Fin 0 → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin 0 → Zd d L) → ℂ)
    (x : Fin 0 → Zd d L) : gdnGen G A x = 0 := by
  simp [gdnGen]

private theorem gdnTens_succ {k : ℕ} (U : Fin (k + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin (k + 1) → Zd d L) → ℂ) (x : Fin (k + 1) → Zd d L) :
    gdnTens U A x = ∑ y0 : Zd d L, U 0 (x 0) y0 *
      gdnTens (fun i : Fin k => U i.succ) (fun y' => A (Fin.cons y0 y')) (Fin.tail x) := by
  unfold gdnTens
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Zd d L)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail, mul_assoc]

private theorem gdnGen_succ {k : ℕ} (G : Fin (k + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin (k + 1) → Zd d L) → ℂ) (x : Fin (k + 1) → Zd d L) :
    gdnGen G A x = ∑ c : Zd d L, G 0 (x 0) c * A (Fin.cons c (Fin.tail x)) +
      gdnGen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x) := by
  unfold gdnGen
  rw [Fin.sum_univ_succ]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Fin.cons_self_tail x, Fin.update_cons_zero]
    simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Fin.cons_self_tail x, ← Fin.cons_update]
    simp [Fin.tail]

/-- Row sums of `P` are `≤ r`, `f` is bounded by `m`: `‖Σ_c P x c f c‖ ≤ r m`. -/
private theorem gdn_row_mul {P : Matrix (Zd d L) (Zd d L) ℂ} {r m : ℝ}
    (hP : ∀ x : Zd d L, ∑ c : Zd d L, ‖P x c‖ ≤ r) (x : Zd d L) {f : Zd d L → ℂ}
    (hf : ∀ c, ‖f c‖ ≤ m) : ‖∑ c : Zd d L, P x c * f c‖ ≤ r * m := by
  have hm : 0 ≤ m := (norm_nonneg _).trans (hf x)
  calc ‖∑ c : Zd d L, P x c * f c‖ ≤ ∑ c : Zd d L, ‖P x c * f c‖ := norm_sum_le _ _
    _ = ∑ c : Zd d L, ‖P x c‖ * ‖f c‖ := by simp only [norm_mul]
    _ ≤ ∑ c : Zd d L, ‖P x c‖ * m :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hf c) (norm_nonneg _)
    _ = (∑ c : Zd d L, ‖P x c‖) * m := (Finset.sum_mul _ _ _).symm
    _ ≤ r * m := mul_le_mul_of_nonneg_right (hP x) hm

/-- Rows of `P = 1 + e` with `e` having row sums `≤ a` have row sums `≤ 1 + a`. -/
private theorem gdn_row_one_add {e : Matrix (Zd d L) (Zd d L) ℂ} {a : ℝ}
    (he : ∀ x : Zd d L, ∑ c : Zd d L, ‖e x c‖ ≤ a) (x : Zd d L) :
    ∑ c : Zd d L, ‖(1 + e) x c‖ ≤ 1 + a := by
  calc ∑ c : Zd d L, ‖(1 + e) x c‖ ≤ ∑ c : Zd d L, (‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x c‖ + ‖e x c‖) :=
        Finset.sum_le_sum fun c _ => by rw [Matrix.add_apply]; exact norm_add_le _ _
    _ = ∑ c : Zd d L, ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x c‖ + ∑ c : Zd d L, ‖e x c‖ :=
        Finset.sum_add_distrib
    _ ≤ 1 + a := by
        gcongr
        · simp [Matrix.one_apply, apply_ite (norm : ℂ → ℝ), Finset.sum_ite_eq]
        · exact he x

/-- `Σ_c (1 + e) x c f c = f x + Σ_c e x c f c`. -/
private theorem gdn_one_add_mul (e : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) (f : Zd d L → ℂ) :
    ∑ c : Zd d L, (1 + e) x c * f c = f x + ∑ c : Zd d L, e x c * f c := by
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

/-- The first-order tensor bound: `‖(⊗U_i) A - A‖ ≤ ((1+a)^k - 1) M`. -/
private theorem gdn_tens_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ (k : ℕ) (U : Fin k → Matrix (Zd d L) (Zd d L) ℂ),
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1) x c‖ ≤ a) →
      ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖gdnTens U A x - A x‖ ≤ ((1 + a) ^ k - 1) * M := by
  intro k
  induction k with
  | zero =>
      intro U _ A M _ x
      rw [gdnTens_zero]
      simp
  | succ k ih =>
      intro U hU A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      have hpow : 1 ≤ (1 + a) ^ k := one_le_pow₀ (by linarith)
      set e : Matrix (Zd d L) (Zd d L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      have hrow : ∀ x' : Zd d L, ∑ c : Zd d L, ‖U 0 x' c‖ ≤ 1 + a := by
        intro x'; rw [hU0]; exact gdn_row_one_add (fun x'' => hU 0 x'') x'
      set T : Zd d L → ℂ := fun y0 => gdnTens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Zd d L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        ih (fun i => U i.succ) (fun i x' => hU i.succ x') (fun y' => A (Fin.cons y0 y')) M
          (fun y' => hA _) (Fin.tail x)
      have hsplit : gdnTens U A x - A x =
          ∑ c : Zd d L, U 0 (x 0) c * (T c - Y c) + ∑ c : Zd d L, e (x 0) c * Y c := by
        rw [gdnTens_succ, hAx]
        have h1 : ∑ c : Zd d L, U 0 (x 0) c * T c =
            ∑ c : Zd d L, U 0 (x 0) c * (T c - Y c) + ∑ c : Zd d L, U 0 (x 0) c * Y c := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Zd d L, U 0 (x 0) c * Y c = Y (x 0) + ∑ c : Zd d L, e (x 0) c * Y c := by
          rw [hU0]; exact gdn_one_add_mul e (x 0) Y
        rw [h1, h2]
        ring
      rw [hsplit]
      have hb1 : ‖∑ c : Zd d L, U 0 (x 0) c * (T c - Y c)‖ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) :=
        gdn_row_mul hrow (x 0) hTY
      have hb2 : ‖∑ c : Zd d L, e (x 0) c * Y c‖ ≤ a * M :=
        gdn_row_mul (fun x' => hU 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖∑ c : Zd d L, U 0 (x 0) c * (T c - Y c)‖ + ‖∑ c : Zd d L, e (x 0) c * Y c‖ :=
            norm_add_le _ _
        _ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) + a * M := add_le_add hb1 hb2
        _ = ((1 + a) ^ (k + 1) - 1) * M := by ring

/-- The second-order tensor bound: with `‖(U_i - 1)‖_rows ≤ a`, `‖(U_i - 1 - G_i)‖_rows ≤ b`,
`‖(⊗U_i) A - A - (Σ_i G_i) A‖ ≤ (k b + (1+a)^k - 1 - k a) M`. -/
private theorem gdn_tens_step_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ (k : ℕ) (U G : Fin k → Matrix (Zd d L) (Zd d L) ℂ),
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1) x c‖ ≤ a) →
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1 - G i) x c‖ ≤ b) →
      ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖gdnTens U A x - A x - gdnGen G A x‖ ≤ ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M := by
  intro k
  induction k with
  | zero =>
      intro U G _ _ A M _ x
      rw [gdnTens_zero, gdnGen_zero]
      simp
  | succ k ih =>
      intro U G hU hG A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      set e : Matrix (Zd d L) (Zd d L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      set T : Zd d L → ℂ := fun y0 => gdnTens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Zd d L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        gdn_tens_sub_le ha k (fun i => U i.succ) (fun i x' => hU i.succ x')
          (fun y' => A (Fin.cons y0 y')) M (fun y' => hA _) (Fin.tail x)
      have hIH : ‖T (x 0) - Y (x 0) - gdnGen (fun i : Fin k => G i.succ)
          (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x)‖ ≤
          ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M :=
        ih (fun i => U i.succ) (fun i => G i.succ) (fun i x' => hU i.succ x')
          (fun i x' => hG i.succ x') (fun y' => A (Fin.cons (x 0) y')) M (fun y' => hA _)
          (Fin.tail x)
      set g' : ℂ := gdnGen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y'))
        (Fin.tail x) with hg'
      have hsplit : gdnTens U A x - A x - gdnGen G A x =
          (T (x 0) - Y (x 0) - g') + ∑ c : Zd d L, e (x 0) c * (T c - Y c) +
            ∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c := by
        rw [gdnTens_succ, gdnGen_succ, hAx]
        have h1 : ∑ c : Zd d L, U 0 (x 0) c * T c =
            T (x 0) + ∑ c : Zd d L, e (x 0) c * (T c - Y c) + ∑ c : Zd d L, e (x 0) c * Y c := by
          rw [hU0, gdn_one_add_mul, add_assoc, ← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c =
            ∑ c : Zd d L, e (x 0) c * Y c - ∑ c : Zd d L, G 0 (x 0) c * Y c := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [he, Matrix.sub_apply, Matrix.sub_apply]
          ring
        rw [h1, h2]
        simp only [hT, hY, hg']
        ring
      rw [hsplit]
      have hb2 : ‖∑ c : Zd d L, e (x 0) c * (T c - Y c)‖ ≤ a * (((1 + a) ^ k - 1) * M) :=
        gdn_row_mul (fun x' => hU 0 x') (x 0) hTY
      have hb3 : ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ ≤ b * M :=
        gdn_row_mul (fun x' => hG 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖T (x 0) - Y (x 0) - g' + ∑ c : Zd d L, e (x 0) c * (T c - Y c)‖ +
            ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ := norm_add_le _ _
        _ ≤ (‖T (x 0) - Y (x 0) - g'‖ + ‖∑ c : Zd d L, e (x 0) c * (T c - Y c)‖) +
            ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M + a * (((1 + a) ^ k - 1) * M)) +
            b * M := by gcongr
        _ = (((k + 1 : ℕ) : ℝ) * b + ((1 + a) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * a)) * M := by
            push_cast; ring

end TensorStep

/-! ## 1b. The explicit one-step error (the pin vocabulary) -/

/-- The `d`-dimensional remainder of one step of `𝒦` (RBM1D `K_step_n`; RBM2D `kStepC`,
`Induction/HierVocab.lean:421`, with `W² → W^d`, `L² → L^d`): `c = W^d k² L^d = N k²`,
`kStepC = 2 c B (c B²) + c (c B²)²`. -/
def kStepC (d L W k : ℕ) (Bk : ℝ) : ℝ :=
  2 * (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * Bk *
      ((W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * Bk ^ 2) +
    (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d *
      ((W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * Bk ^ 2) ^ 2

/-- The remainder factor of one step of `𝒰` (RBM1D `Uker_step_n`, dimension-free; RBM2D `uStepC`,
`HierVocab.lean:427`). -/
def uStepC (k : ℕ) (Δ v : ℝ) : ℝ :=
  (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 + ((1 + Δ * (1 - v)⁻¹) ^ k - 1 - (k : ℝ) * Δ * (1 - v)⁻¹)

/-- The explicit one-step error: `envConst Δ^{3/2}` (merged `condExp_loop_drift`) plus the `𝒦` and
`𝒰` second-order remainders, with `‖A_j‖_max ≤ η_{u_j}^{-k} (W^{-d})^{k-1} + B_k` (RBM2D `stepErrN`,
`HierVocab.lean:432`, with `((W⁻¹)^2)^(k-1) → ((W^d)⁻¹)^(k-1)`). -/
def stepErrN (d L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ Bk : ℝ) : ℝ :=
  envConst d L W E k v * Δ ^ ((3 : ℝ) / 2) + kStepC d L W k Bk * Δ ^ 2 +
    uStepC k Δ v * ((etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk)

/-! ## 2. One step of `𝒰` in the `Ugen` vocabulary -/

section UStep

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm (copied from the private
`sum_norm_row_le_opNorm` of `Path/UBounds.lean`). -/
private theorem gdn_sum_norm_row_le_opNorm (M : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) :
    ∑ c : Zd d L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Zd d L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Zd d L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Zd d L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- `‖Θ_z‖ ≤ (1 - ‖z‖)⁻¹` for complex `z`, `‖z‖ < 1` (copied from the private
`norm_Theta_le_of_lt` of `Path/UBounds.lean`; merged `norm_Theta_le` at `z = ‖z‖ · (z/‖z‖)`). -/
private theorem gdn_norm_Theta_le_of_lt (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Theta d L g z‖ ≤ (1 - ‖z‖)⁻¹ := by
  by_cases h0 : z = 0
  · subst h0
    have := norm_Theta_le (d := d) (L := L) (g := g) hL (t := 0) le_rfl zero_lt_one (m := 1)
      (by simp)
    simpa using this
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hm : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm]; exact div_self hn.ne'
    have h := norm_Theta_le (d := d) (L := L) (g := g) hL (t := ‖z‖) hn.le hz hm
    have e : ((‖z‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) = z := by
      have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rwa [e] at h

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}` (copied from the private
`sum_norm_thetaGenMat_row_le` of `Path/UBounds.lean`; port of RBM1D `row_bound_edge`). -/
private theorem gdn_row_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ =
      ‖ξ‖ * ‖(SB d L g * Theta d L g ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((gdn_sum_norm_row_le_opNorm _ x).trans ?_) (norm_nonneg _)
  calc ‖SB d L g * Theta d L g ((s : ℂ) * ξ)‖ ≤ ‖SB d L g‖ * ‖Theta d L g ((s : ℂ) * ξ)‖ :=
      norm_mul_le _ _
    _ = ‖Theta d L g ((s : ℂ) * ξ)‖ := by rw [norm_SB d L g hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := gdn_norm_Theta_le_of_lt hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u` (copied from the
private `sum_norm_thetaGenMat_diff_row_le` of `Path/UBounds.lean`; resolvent identity
`Theta_sub_Theta`). -/
private theorem gdn_row_thetaGenMat_diff (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hu : ‖(u : ℂ) * ξ‖ < 1) (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ ≤
      Δ * ‖ξ‖ ^ 2 * ((1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹) := by
  have hTsub := Theta_sub_Theta d L g (norm_SB d L g hL) (ξ := (u : ℂ) * ξ)
    (ζ := ((u + Δ : ℝ) : ℂ) * ξ) hu hd
  have hcast : ((u + Δ : ℝ) : ℂ) * ξ - (u : ℂ) * ξ = ((Δ : ℝ) : ℂ) * ξ := by
    push_cast; ring
  rw [hcast] at hTsub
  have hM : thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u =
      (((Δ : ℝ) : ℂ) * ξ ^ 2) •
        (SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
          Theta d L g ((u : ℂ) * ξ))) := by
    unfold thetaGenMat
    rw [← smul_sub, ← Matrix.mul_sub, hTsub, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  have hnormeq : ∀ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ =
      Δ * ‖ξ‖ ^ 2 * ‖(SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
        Theta d L g ((u : ℂ) * ξ))) x c‖ := by
    intro c
    rw [hM, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hΔ, norm_pow]
  simp_rw [hnormeq]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((gdn_sum_norm_row_le_opNorm _ x).trans ?_) (by positivity)
  calc ‖SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g * Theta d L g ((u : ℂ) * ξ))‖
      ≤ ‖SB d L g‖ * ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
          Theta d L g ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ = ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g * Theta d L g ((u : ℂ) * ξ)‖ := by
        rw [norm_SB d L g hL, one_mul]
    _ ≤ ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g‖ * ‖Theta d L g ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ ≤ (‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖SB d L g‖) * ‖Theta d L g ((u : ℂ) * ξ)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖Theta d L g ((u : ℂ) * ξ)‖ := by
        rw [norm_SB d L g hL, mul_one]
    _ ≤ (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ * (1 - ‖(u : ℂ) * ξ‖)⁻¹ :=
        mul_le_mul (gdn_norm_Theta_le_of_lt hL hd) (gdn_norm_Theta_le_of_lt hL hu)
          (norm_nonneg _) (inv_nonneg.mpr (by linarith))

/-- `‖(w : ℂ) ξ‖ = w` for `‖ξ‖ = 1`, `0 ≤ w`. -/
private theorem gdn_norm_real_mul {ξ : ℂ} (hξ : ‖ξ‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    ‖(w : ℂ) * ξ‖ = w := by
  rw [norm_mul, hξ, mul_one, Complex.norm_of_nonneg hw]

/-- `(1 - vξS)Θ_{wξ} = 1 + (w - v) ξ S Θ_{wξ}`, i.e. `𝒰_{u,u+Δ} - 1 = Δ · (generator at u+Δ)`
(`def_Ustz_2`, `3_5`). -/
private theorem gdn_ukerMat_sub_one (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ}
    (hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1) :
    uKer d L g ξ u (u + Δ) - 1 = (Δ : ℂ) • thetaGenMat d L g ξ (u + Δ) := by
  have h1 : (1 : Matrix (Zd d L) (Zd d L) ℂ) - ((u : ℂ) * ξ) • SB d L g =
      (1 - (((u + Δ : ℝ) : ℂ) * ξ) • SB d L g) + ((Δ : ℂ) * ξ) • SB d L g := by
    push_cast
    module
  unfold uKer thetaGenMat
  rw [h1, add_mul, mul_Theta d L g (norm_SB d L g hL) hd, Matrix.smul_mul, add_sub_cancel_left,
    smul_smul]

/-- Row sums of `𝒰_{u,u+Δ} - 1` are `≤ Δ (1-(u+Δ))⁻¹` for `‖ξ‖ = 1`. -/
private theorem gdn_row_U (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(uKer d L g ξ u (u + Δ) - 1) x c‖ ≤ Δ * (1 - (u + Δ))⁻¹ := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [gdn_norm_real_mul hξ (by linarith)]; exact hv
  rw [gdn_ukerMat_sub_one hL hd]
  have hentry : ∀ c : Zd d L, ‖((Δ : ℂ) • thetaGenMat d L g ξ (u + Δ)) x c‖ =
      Δ * ‖thetaGenMat d L g ξ (u + Δ) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  have := gdn_row_thetaGenMat (g := g) hL hd x
  rwa [hξ, gdn_norm_real_mul hξ (by linarith), one_mul] at this

/-- Row sums of `𝒰_{u,u+Δ} - 1 - Δ (generator at u)` are `≤ Δ² (1-(u+Δ))⁻²` for `‖ξ‖ = 1`. -/
private theorem gdn_row_UG (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(uKer d L g ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat d L g ξ u) x c‖ ≤
      Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [gdn_norm_real_mul hξ (by linarith)]; exact hv
  have hu : ‖(u : ℂ) * ξ‖ < 1 := by
    rw [gdn_norm_real_mul hξ hu0]; linarith
  have hM : uKer d L g ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat d L g ξ u =
      (Δ : ℂ) • (thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) := by
    rw [gdn_ukerMat_sub_one hL hd, smul_sub]
  rw [hM]
  have hentry : ∀ c : Zd d L, ‖((Δ : ℂ) • (thetaGenMat d L g ξ (u + Δ) -
      thetaGenMat d L g ξ u)) x c‖ =
      Δ * ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  have h1 := gdn_row_thetaGenMat_diff (g := g) hL hΔ hu hd x
  rw [hξ, gdn_norm_real_mul hξ (by linarith), gdn_norm_real_mul hξ hu0] at h1
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβu : (1 - u)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hβ0 (by linarith)
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  calc Δ * ∑ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖
      ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹)) :=
        mul_le_mul_of_nonneg_left h1 hΔ
    _ ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - (u + Δ))⁻¹)) := by gcongr
    _ = Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by ring

/-- The generator kernel of `ThetaN` is `thetaGenMat`: `(μ S) Θ_{tμ} = μ (S Θ_{tμ})`. -/
private theorem gdn_thetaKer_eq (μ : ℂ) (t : ℝ) :
    thetaKer d L g μ t = thetaGenMat d L g μ t := by
  unfold thetaKer thetaGenMat
  rw [Matrix.smul_mul]

/-- **One step of `𝒰`** (RBM1D `Uker_step_n`, `Gauss/GridHierarchyN.lean:698` at `c06b103`;
RBM2D `gdn_Ugen_step_le`, `GDN:408`, in the `Ugen`/`ThetaN` vocabulary): for `‖A‖_max ≤ M`,
`‖𝒰_{u,u+Δ,σ} A - A - Δ ϴ_{u,σ} A‖ ≤ uStepC k Δ (u+Δ) M`. -/
private theorem gdn_Ugen_step_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1)
    (A : (Fin k → Zd d L) → ℂ) (M : ℝ) (hA : ∀ y, ‖A y‖ ≤ M) (x : Fin k → Zd d L) :
    ‖Ugen d L g E σ u (u + Δ) A x - A x -
        (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x‖ ≤
      uStepC k Δ (u + Δ) * M := by
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  have hedge : ∀ i : Fin k, ‖cycProd (fun i => mSigma E (σ i)) i‖ = 1 := fun i =>
    norm_cycProd (fun i => norm_mSigma hE (σ i)) i
  have key := gdn_tens_step_le (d := d) (L := L) (a := Δ * (1 - (u + Δ))⁻¹)
    (b := Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2) (mul_nonneg hΔ hβ1) (by positivity) k
    (fun i : Fin k => uKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (u + Δ))
    (fun i : Fin k => (Δ : ℂ) • thetaGenMat d L g (cycProd (fun i => mSigma E (σ i)) i) u)
    (fun i x' => gdn_row_U hL (hedge i) hu0 hΔ hv x')
    (fun i x' => gdn_row_UG hL (hedge i) hu0 hΔ hv x') A M hA x
  have hT : gdnTens (fun i : Fin k =>
      uKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (u + Δ)) A x =
      Ugen d L g E σ u (u + Δ) A x := rfl
  have hG : gdnGen (fun i : Fin k =>
      (Δ : ℂ) • thetaGenMat d L g (cycProd (fun i => mSigma E (σ i)) i) u) A x =
      (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x := by
    unfold gdnGen ThetaN
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, gdn_thetaKer_eq]
    ring
  rw [hT, hG] at key
  refine key.trans (le_of_eq ?_)
  unfold uStepC
  ring

end UStep

/-! ## 3. One step of `𝒦` -/

section KStep

variable {d L W : ℕ} [NeZero L] {g : ℝ}

/-- Bound `‖𝒦_w(J)‖ ≤ B` on `[0, v]` for the loops of length at most `k`. -/
private def GdnEnv (d L W : ℕ) [NeZero L] (g E : ℝ) (k : ℕ) (v B : ℝ) : Prop :=
  ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ k →
    ‖KLK d L g W E w J‖ ≤ B

/-- `∂_t 𝒦_t(J) = treeEqRhs (𝒦_t)(J)` (`KLK_isKLoop`, the equation `pro_dyncalK`). -/
private theorem gdn_hasDeriv (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {J : LoopIdx (Zd d L)} (hJ : J.WF) (h2 : 2 ≤ J.length) :
    HasDerivAt (fun s => KLK d L g W E s J) (treeEqRhs d L W g (KLK d L g W E t) J) t :=
  (KLK_isKLoop d L W g E hL hW hE).1 t ⟨ht0, ht1⟩ J hJ h2

/-- The `𝒦` family is Lipschitz in time with constant `W^d k² L^d B²` on `[0, v]` (uses the
derivative bound `‖treeEqRhs (𝒦_w)(J)‖ ≤ W^d k² L^d B²`, `norm_primBil_le`; RBM1D `norm_Kgen_sub_le`,
`Gauss/Lemma514Holder.lean:269` at `c06b103`; RBM2D `gdn_K_lip`, `GDN:461`, with the `d`-dimensional
constant). -/
private theorem gdn_K_lip (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {v : ℝ} (hv1 : v < 1)
    {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B) (hB : GdnEnv d L W g E k v B)
    {J : LoopIdx (Zd d L)} (hJ : J.WF) (h2 : 2 ≤ J.length) (hk : J.length ≤ k)
    {u : ℝ} (hu : 0 ≤ u) :
    ∀ r ∈ Set.Icc u v, ‖KLK d L g W E r J - KLK d L g W E u J‖ ≤
      ((W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B ^ 2) * (r - u) := by
  have hbound : ∀ r ∈ Set.Icc u v,
      ‖treeEqRhs d L W g (KLK d L g W E r) J‖ ≤ (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B ^ 2 := by
    intro r hr
    rw [← primBil_self]
    have hr' : r ∈ Set.Icc (0 : ℝ) v := ⟨hu.trans hr.1, hr.2⟩
    have h1 := norm_primBil_le d L W g hL (KLK d L g W E r) (KLK d L g W E r) J hJ hB0 hB0
      (fun J' hJ' h2' hk' => hB r hr' J' hJ' h2' (hk'.trans hk))
      (fun J' hJ' h2' hk' => hB r hr' J' hJ' h2' (hk'.trans hk))
    have hkk : (J.length : ℝ) ≤ k := by exact_mod_cast hk
    have hJ0 : (0 : ℝ) ≤ J.length := Nat.cast_nonneg _
    calc _ ≤ _ := h1
      _ ≤ (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B * B := by gcongr
      _ = _ := by ring
  intro r hr
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := r)
    (f := fun s => KLK d L g W E s J)
    (f' := fun s => treeEqRhs d L W g (KLK d L g W E s) J)
    (C := (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d * B ^ 2)
    (fun x hx => (gdn_hasDeriv hL hW hE (hu.trans hx.1) (lt_of_le_of_lt (hx.2.trans hr.2) hv1) hJ
      h2).hasDerivWithinAt)
    (fun x hx => hbound x ⟨hx.1, hx.2.le.trans hr.2⟩) r ⟨hr.1, le_rfl⟩
  exact hres

/-- **One step of `𝒦`** (RBM1D `K_step_n`, `Gauss/GridHierarchyN.lean:342` at `c06b103`; RBM2D
`gdn_K_step`, `GDN:493`, with the `d`-dimensional constants `W^d k² L^d = N k²`): for
`0 ≤ Δ ≤ 1`, `u + Δ < 1`, on the envelope `B`,
`‖𝒦_{u+Δ}(I) - 𝒦_u(I) - Δ ∂_u𝒦_u(I)‖ ≤ kStepC d L W k B Δ²`. -/
private theorem gdn_K_step (hL : 3 ≤ L) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {u Δ : ℝ}
    (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hv1 : u + Δ < 1) {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : GdnEnv d L W g E k (u + Δ) B) {I : LoopIdx (Zd d L)} (hI : I.WF) (h2 : 2 ≤ I.length)
    (hk : I.length = k) :
    ‖KLK d L g W E (u + Δ) I - KLK d L g W E u I -
        (Δ : ℂ) * treeEqRhs d L W g (KLK d L g W E u) I‖ ≤ kStepC d L W k B * Δ ^ 2 := by
  set c : ℝ := (W : ℝ) ^ d * (k : ℝ) ^ 2 * (L : ℝ) ^ d with hc
  have hc0 : 0 ≤ c := by positivity
  set D1 : ℝ := c * B ^ 2 with hD1
  have hD10 : 0 ≤ D1 := by positivity
  set C0 : ℂ := treeEqRhs d L W g (KLK d L g W E u) I with hC0
  have hkI : (I.length : ℝ) = k := by exact_mod_cast hk
  -- the derivative bound
  have hbound : ∀ r ∈ Set.Ico u (u + Δ),
      ‖treeEqRhs d L W g (KLK d L g W E r) I - C0‖ ≤ 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2 := by
    intro r hr
    have hr' : r ∈ Set.Icc u (u + Δ) := ⟨hr.1, hr.2.le⟩
    have hrB : r ∈ Set.Icc (0 : ℝ) (u + Δ) := ⟨hu0.trans hr.1, hr.2.le⟩
    have hδ : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖(KLK d L g W E r - KLK d L g W E u) J‖ ≤ D1 * (r - u) := by
      intro J hJ hJ2 hJk
      exact gdn_K_lip hL hW hE hv1 hB0 hB hJ hJ2 (hJk.trans hk.le) hu0 r hr'
    have hδ0 : 0 ≤ D1 * (r - u) := mul_nonneg hD10 (by linarith [hr.1])
    have hKu : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
        ‖KLK d L g W E u J‖ ≤ B := fun J hJ hJ2 hJk =>
      hB u ⟨hu0, by linarith⟩ J hJ hJ2 (hJk.trans hk.le)
    have hsub := primRhs_sub d L W g (KLK d L g W E r) (KLK d L g W E u) I
    have e1 := norm_primBil_le d L W g hL (KLK d L g W E u) (KLK d L g W E r - KLK d L g W E u)
      I hI hB0 hδ0 hKu hδ
    have e2 := norm_primBil_le d L W g hL (KLK d L g W E r - KLK d L g W E u) (KLK d L g W E u)
      I hI hδ0 hB0 hδ hKu
    have e3 := norm_primBil_le d L W g hL (KLK d L g W E r - KLK d L g W E u)
      (KLK d L g W E r - KLK d L g W E u) I hI hδ0 hδ0 hδ hδ
    rw [hkI, ← hc] at e1 e2 e3
    have hrΔ : r - u ≤ Δ := by linarith [hr.2]
    have hru : 0 ≤ r - u := by linarith [hr.1]
    have hprim : treeEqRhs d L W g (KLK d L g W E r) I - C0 =
        primBil d L W g (KLK d L g W E u) (KLK d L g W E r - KLK d L g W E u) I +
        primBil d L W g (KLK d L g W E r - KLK d L g W E u) (KLK d L g W E u) I +
        primBil d L W g (KLK d L g W E r - KLK d L g W E u)
          (KLK d L g W E r - KLK d L g W E u) I := hsub
    rw [hprim]
    calc _ ≤ ‖primBil d L W g (KLK d L g W E u) (KLK d L g W E r - KLK d L g W E u) I +
            primBil d L W g (KLK d L g W E r - KLK d L g W E u) (KLK d L g W E u) I‖ +
          ‖primBil d L W g (KLK d L g W E r - KLK d L g W E u)
            (KLK d L g W E r - KLK d L g W E u) I‖ := norm_add_le _ _
      _ ≤ (‖primBil d L W g (KLK d L g W E u) (KLK d L g W E r - KLK d L g W E u) I‖ +
            ‖primBil d L W g (KLK d L g W E r - KLK d L g W E u) (KLK d L g W E u) I‖) +
          ‖primBil d L W g (KLK d L g W E r - KLK d L g W E u)
            (KLK d L g W E r - KLK d L g W E u) I‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (c * B * (D1 * (r - u)) + c * (D1 * (r - u)) * B) + c * (D1 * (r - u)) * (D1 * (r - u)) := by
          exact add_le_add (add_le_add e1 e2) e3
      _ ≤ (c * B * (D1 * Δ) + c * (D1 * Δ) * B) + c * (D1 * Δ) * (D1 * Δ) := by gcongr
      _ = 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2 := by ring
  have hderiv : ∀ x ∈ Set.Icc u (u + Δ), HasDerivWithinAt
      (fun r : ℝ => KLK d L g W E r I - (r - u) • C0)
      (treeEqRhs d L W g (KLK d L g W E x) I - C0) (Set.Icc u (u + Δ)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hu0.trans hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hv1
    have h1 := gdn_hasDeriv (g := g) (W := W) hL hW hE hx0 hx1 hI h2
    have h2' : HasDerivAt (fun r : ℝ => (r - u) • C0) C0 x := by
      simpa using ((hasDerivAt_id x).sub_const u).smul_const C0
    exact (h1.sub h2').hasDerivWithinAt
  have hres := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := u + Δ)
    (f := fun r : ℝ => KLK d L g W E r I - (r - u) • C0)
    (f' := fun x => treeEqRhs d L W g (KLK d L g W E x) I - C0)
    (C := 2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) hderiv hbound (u + Δ) ⟨by linarith, le_rfl⟩
  have hlhs : (KLK d L g W E (u + Δ) I - (u + Δ - u) • C0) - (KLK d L g W E u I - (u - u) • C0) =
      KLK d L g W E (u + Δ) I - KLK d L g W E u I - (Δ : ℂ) * C0 := by
    have h1 : u + Δ - u = Δ := by ring
    rw [h1, sub_self, zero_smul, sub_zero, Complex.real_smul]
    ring
  have hres' : ‖(KLK d L g W E (u + Δ) I - (u + Δ - u) • C0) -
      (KLK d L g W E u I - (u - u) • C0)‖ ≤
      (2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) * (u + Δ - u) := hres
  rw [hlhs, add_sub_cancel_left] at hres'
  refine hres'.trans ?_
  unfold kStepC
  have hΔ3 : Δ ^ 3 ≤ Δ ^ 2 := by
    calc Δ ^ 3 = Δ ^ 2 * Δ := by ring
      _ ≤ Δ ^ 2 * 1 := by gcongr
      _ = Δ ^ 2 := mul_one _
  have hcD : 0 ≤ c * D1 ^ 2 := by positivity
  calc (2 * c * B * D1 * Δ + c * D1 ^ 2 * Δ ^ 2) * Δ
      = 2 * c * B * D1 * Δ ^ 2 + c * D1 ^ 2 * Δ ^ 3 := by ring
    _ ≤ 2 * c * B * D1 * Δ ^ 2 + c * D1 ^ 2 * Δ ^ 2 := by gcongr
    _ = _ := by rw [hD1, hc]; ring

end KStep

/-! ## 4. The pin `GridDriftN` and the assembly -/

section Assembly

variable {d : ℕ} (sz : Sizes d)

/-- **Pin `GridDriftN` (one grid step of `LK_SDE`, `3_5:133`, general `n`, all `σ`)** (RBM2D
`Induction/HierVocab.lean:440`, vocabulary of the merged files): a.e., the predictable part
`P_j = 𝔼[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A_j` is `Δ` times the non-linear drift
`Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{(G̃)}` at `u_j`, up to the deterministic `stepErrN`, given a
deterministic envelope `B_k` of `𝒦` on `[0, u_{j+1}]`.  RBM1D `discrete_hierarchy_step_n`.
Differences from RBM2D: `Z2 → Zd d`, `Kcal → KLK`, `ksimLK/elklkN/egtN → STksimLKM/STelklkM/STegtM`
at `H = pathH` (`Induction/Step2Defs.lean`), `stepErrN` with `W^d`; `[NeZero k]` dropped (T2111a).
The `∀ n` hypotheses are the pin's (DECISIONS §29 (4)); `gridDriftN_at` needs them only at `n`. -/
def GridDriftN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n j : ℕ), j < K n → ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncN sz E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))‖
        ≤ stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n) Bk

private theorem gdn_loopOf_wf {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem gdn_loopOf_length {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- The grid-time facts used by `gridDriftN_at`: `Δ ≥ 0`, `u_j ≥ 0`, `u_{j+1} = u_j + Δ`,
`u_{j+1} < 1`, `Δ ≤ 1` (`GDN:598`). -/
private theorem gdn_time_facts (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n) :
    0 ≤ gridStep s t K n ∧ 0 ≤ gridTime s t K n j ∧
      gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n ∧
      gridTime s t K n (j + 1) < 1 ∧ gridStep s t K n ≤ 1 := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) hKpos.le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hu : 0 ≤ gridTime s t K n j := add_nonneg hs0 (mul_nonneg hj0 hΔ)
  have hsucc : gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
    unfold gridTime; push_cast; ring
  have hKΔ : (K n : ℝ) * gridStep s t K n = t n - s n := by
    unfold gridStep; field_simp
  have hle : gridTime s t K n (j + 1) ≤ t n := by
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ K n := by exact_mod_cast Nat.succ_le_of_lt hj
    calc gridTime s t K n (j + 1) = s n + ((j + 1 : ℕ) : ℝ) * gridStep s t K n := rfl
      _ ≤ s n + (K n : ℝ) * gridStep s t K n := by gcongr
      _ = t n := by rw [hKΔ]; ring
  have hv1 : gridTime s t K n (j + 1) < 1 := lt_of_le_of_lt hle ht1
  exact ⟨hΔ, hu, hsucc, hv1, by linarith⟩

/-- `A_i = (𝓛 - 𝒦)_{u_i,σ}` along the walk is the loop of the block matrix minus `𝒦`. -/
private theorem gdn_AvecN_eq (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (ω : PathΩ sz) (a : Fin k → Zd d (sz.L n)) :
    AvecN sz E s t K n i σ ω a =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n i ω))
          (zt (E n) (gridTime s t K n i)) (loopOf σ a) -
        KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n i) (loopOf σ a) := by
  change sz.STLM n (E n) (gridTime s t K n i) (pathH sz s t K n i ω) σ a -
      sz.STKloop n (E n) (gridTime s t K n i) σ a = _
  unfold Sizes.STLM
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- `(𝓛 - 𝒦)_{u,I}` at `I = loopOf σ b` is `STLKM` (copy of the private `HierarchyN_STLKIM_loopOf`
of `Induction/HierarchyN.lean`). -/
private theorem gdn_STLKIM_loopOf (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) :
    sz.STLKIM n E u H (loopOf σ b) = sz.STLKM n E u H σ b := by
  unfold Sizes.STLKIM Sizes.STLKM
  have h : sz.STLIM n E u H (loopOf σ b) = sz.STLM n E u H σ b :=
    (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ b).symm
  rw [h]
  rfl

/-- Integrability of the bounded loop observable along the walk (RBM2D `gdn_integrable_gloop`,
`GDN:620`; measurability by the merged `walk_measurable_loopL`, `walk_measurable_blockMat`,
`pathH_measurable_filt` instead of `GoodEvent_measurable_gloop`). -/
private theorem gdn_integrable_loopL (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {E : ℝ}
    (hE : |E| < 2) {w : ℝ} (hw : w < 1) (I : LoopIdx (Zd d (sz.L n))) (hwf : I.WF)
    (hn : 1 ≤ I.length) :
    Integrable (fun ω : PathΩ sz =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n i ω)) (zt E w) I)
      (pathP sz) := by
  have hη : 0 < etaT E w := etaT_pos hE hw
  have hz : etaT E w ≤ |(zt E w).im| := by
    rw [zt_im, abs_of_pos (mul_pos (sub_pos.2 hw) (mE_im_pos hE))]
    exact le_rfl
  have hmeas : Measurable (fun ω : PathΩ sz =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n i ω)) (zt E w) I) :=
    ((walk_measurable_loopL d (sz.L n) (sz.W n) (zt E w) I).comp
      (walk_measurable_blockMat d (sz.L n) (sz.W n))).comp
      ((pathH_measurable_filt sz s t K n i).mono ((filt sz).le i) le_rfl)
  exact (memLp_top_of_bound hmeas.aestronglyMeasurable
    ((etaT E w)⁻¹ ^ I.a.length * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (I.a.length - 1))
    (Eventually.of_forall fun ω => norm_gloop_le_of_le_abs_im
      (show (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n i ω)).IsHermitian from
        (pathH_isHermitian sz s t K n i ω).submatrix _) hη hz I hwf hn)).integrable le_top

/-- The exact algebra `P_j - Δ D_j = R₁ - R_𝒦 - R_𝒰` (`GDN:640`). -/
private theorem gdn_algebra {g1 Gj gen K1 K0 Kd U θ S : ℂ} {Δ : ℝ} {eR eK eU : ℝ}
    (hier : gen - Kd = θ + S) (hR : ‖g1 - Gj - (Δ : ℂ) * gen‖ ≤ eR)
    (hK : ‖K1 - K0 - (Δ : ℂ) * Kd‖ ≤ eK) (hU : ‖U - (Gj - K0) - (Δ : ℂ) * θ‖ ≤ eU) :
    ‖(g1 - K1 - U) - (Δ : ℂ) * S‖ ≤ eR + eK + eU := by
  have hid : (g1 - K1 - U) - (Δ : ℂ) * S =
      (g1 - Gj - (Δ : ℂ) * gen) - (K1 - K0 - (Δ : ℂ) * Kd) - (U - (Gj - K0) - (Δ : ℂ) * θ) := by
    linear_combination (Δ : ℂ) * hier
  rw [hid]
  calc _ ≤ ‖(g1 - Gj - (Δ : ℂ) * gen) - (K1 - K0 - (Δ : ℂ) * Kd)‖ +
        ‖U - (Gj - K0) - (Δ : ℂ) * θ‖ := norm_sub_le _ _
    _ ≤ (‖g1 - Gj - (Δ : ℂ) * gen‖ + ‖K1 - K0 - (Δ : ℂ) * Kd‖) +
        ‖U - (Gj - K0) - (Δ : ℂ) * θ‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ eR + eK + eU := by gcongr

/-- **One grid step of (`LK_SDE`), at one size index** (DECISIONS §29 (4), T2104c): the pin
`GridDriftN` with the hypotheses `|E n| < 2`, `0 ≤ s n ≤ t n < 1`, `K n ≠ 0` only at the index `n`.
RBM1D `discrete_hierarchy_step_n`, `Gauss/GridHierarchyN.lean:999` at `c06b103`; RBM2D `gridDriftN`,
`GDN:656`. -/
theorem gridDriftN_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n)
    {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (Bk : ℝ) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ k →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncN sz E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))‖
        ≤ stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n) Bk := by
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := gdn_time_facts s t K n j hs0 hst ht1 hK hj
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hkpos : 1 ≤ k := by omega
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hB' : GdnEnv d (sz.L n) (sz.W n) (sz.lam n) (E n) k
      (gridTime s t K n j + gridStep s t K n) Bk := by
    intro w hw J hJ h2 hJk
    exact hB w (by rw [hvu]; exact hw) J hJ h2 hJk
  -- the a.e. facts for a fixed label vector
  have hae : ∀ a : Fin k → Zd d (sz.L n), ∀ᵐ ω ∂(pathP sz),
      (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' a | filt sz j] ω =
        (pathP sz)[fun ω' => loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
            (zt (E n) (gridTime s t K n (j + 1))) (loopOf σ a) | filt sz j] ω -
          KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ a) ∧
      ‖(pathP sz)[fun ω' => loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
            (zt (E n) (gridTime s t K n (j + 1))) (loopOf σ a) | filt sz j] ω -
          loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
            (zt (E n) (gridTime s t K n j)) (loopOf σ a) -
          (gridStep s t K n : ℂ) * genMat d (sz.L n) (sz.W n) (sz.lam n) (E n)
            (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a)‖ ≤
        envConst d (sz.L n) (sz.W n) (E n) k (gridTime s t K n (j + 1)) *
          gridStep s t K n ^ ((3 : ℝ) / 2) := by
    intro a
    have hint := gdn_integrable_loopL sz s t K n (j + 1) hE hv1 (loopOf σ a)
      (gdn_loopOf_wf σ a) (by rw [gdn_loopOf_length]; exact hkpos)
    have hsub := condExp_sub hint
      (integrable_const (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n (j + 1))
        (loopOf σ a))) (filt sz j)
    have hconst := condExp_const (μ := pathP sz) ((filt sz).le j)
      (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ a))
    have hdrift := condExp_loop_drift sz s t K n j (E n) hE (gdn_loopOf_wf σ a) hs0 hst hK hj hv1
    filter_upwards [hsub, hdrift] with ω h1 h2
    refine ⟨?_, ?_⟩
    · have hfun : (fun ω' : PathΩ sz => AvecN sz E s t K n (j + 1) σ ω' a) =
          (fun ω' => loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
            (zt (E n) (gridTime s t K n (j + 1))) (loopOf σ a)) -
          (fun _ => KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n (j + 1))
            (loopOf σ a)) := by
        funext ω'
        exact gdn_AvecN_eq sz E s t K n (j + 1) σ ω' a
      rw [hfun, h1, Pi.sub_apply, hconst]
    · rw [gdn_loopOf_length] at h2
      exact h2
  filter_upwards [ae_all_iff.2 hae] with ω hω a
  obtain ⟨hce, hR1⟩ := hω a
  have hη : 0 < etaT (E n) (gridTime s t K n j) := etaT_pos hE hu1
  have hz : etaT (E n) (gridTime s t K n j) ≤ |(zt (E n) (gridTime s t K n j)).im| := by
    rw [zt_im, abs_of_pos (mul_pos (sub_pos.2 hu1) (mE_im_pos hE))]
    exact le_rfl
  -- the sup bound on `A_j`
  have hsup : ∀ b : Fin k → Zd d (sz.L n), ‖AvecN sz E s t K n j σ ω b‖ ≤
      (etaT (E n) (gridTime s t K n j))⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) + Bk := by
    intro b
    have hHb : (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω)).IsHermitian :=
      (pathH_isHermitian sz s t K n j ω).submatrix _
    have h1 := norm_gloop_le_of_le_abs_im hHb hη hz (loopOf σ b) (gdn_loopOf_wf σ b)
      (by rw [show (loopOf σ b).a.length = k from gdn_loopOf_length σ b]; exact hkpos)
    rw [show (loopOf σ b).a.length = k from gdn_loopOf_length σ b] at h1
    have h2 : ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j) (loopOf σ b)‖ ≤ Bk :=
      hB _ ⟨hu0, by rw [hvu]; linarith⟩ (loopOf σ b) (gdn_loopOf_wf σ b)
        (by rw [gdn_loopOf_length]; exact hk) (by rw [gdn_loopOf_length])
    rw [gdn_AvecN_eq]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
  -- the three remainders
  have hK' := gdn_K_step hL3 hW1 hE hu0 hΔ0 hΔ1 (by rw [← hvu]; exact hv1) hBk hB'
    (gdn_loopOf_wf σ a) (by rw [gdn_loopOf_length]; exact hk) (gdn_loopOf_length σ a)
  rw [← hvu] at hK'
  have hKd : deriv (fun x => KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) x (loopOf σ a))
      (gridTime s t K n j) =
      treeEqRhs d (sz.L n) (sz.W n) (sz.lam n)
        (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j)) (loopOf σ a) :=
    (gdn_hasDeriv hL3 hW1 hE hu0 hu1 (gdn_loopOf_wf σ a)
      (by rw [gdn_loopOf_length]; exact hk)).deriv
  have hU' := gdn_Ugen_step_le (g := sz.lam n) hL3 hE.le σ hu0 hΔ0 (by rw [← hvu]; exact hv1)
    (AvecN sz E s t K n j σ ω) _ hsup a
  rw [← hvu] at hU'
  have hier := hierarchyN_holds d sz n (E n) hE (gridTime s t K n j) hu0 hu1
    (pathH sz s t K n j ω) (pathH_isHermitian sz s t K n j ω) k hk σ a
  have hlk : (fun b : Fin k → Zd d (sz.L n) =>
      sz.STLKIM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b)) =
      AvecN sz E s t K n j σ ω := by
    funext b
    exact gdn_STLKIM_loopOf sz n _ _ _ σ b
  have hKd' : deriv (fun v : ℝ => sz.STKloop n (E n) v σ a) (gridTime s t K n j) =
      treeEqRhs d (sz.L n) (sz.W n) (sz.lam n)
        (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j)) (loopOf σ a) := hKd
  rw [hlk, hKd'] at hier
  have hpred : predIncN sz E s t K n j σ ω a =
      ((pathP sz)[fun ω' => loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
            (zt (E n) (gridTime s t K n (j + 1))) (loopOf σ a) | filt sz j] ω -
          KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n (j + 1)) (loopOf σ a)) -
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
          (AvecN sz E s t K n j σ ω) a := by
    unfold predIncN
    rw [hce]
  rw [hpred]
  have hU'' : ‖Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
        (AvecN sz E s t K n j σ ω) a -
      (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
          (zt (E n) (gridTime s t K n j)) (loopOf σ a) -
        KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j) (loopOf σ a)) -
      (gridStep s t K n : ℂ) * ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i))
        (gridTime s t K n j) (AvecN sz E s t K n j σ ω) a‖ ≤
      uStepC k (gridStep s t K n) (gridTime s t K n (j + 1)) *
        ((etaT (E n) (gridTime s t K n j))⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) + Bk) := by
    rw [← gdn_AvecN_eq sz E s t K n j σ ω a]
    exact hU'
  have key := gdn_algebra
    (S := (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a)))
    (Gj := loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
      (zt (E n) (gridTime s t K n j)) (loopOf σ a))
    (by rw [hier]; ring) hR1 hK' hU''
  refine key.trans (le_of_eq ?_)
  unfold stepErrN
  ring

/-- **Pin `GridDriftN`** (`LK_SDE`, `3_5:133`, the drift part): `gridDriftN_at` at every size
index. -/
theorem gridDriftN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : GridDriftN sz E s t K := by
  intro hE hs0 hst ht1 hK n j hj k hk σ Bk hBk hB
  exact gridDriftN_at sz E s t K n j (hE n) (hs0 n) (hst n) (ht1 n) (hK n) hj hk σ Bk hBk hB

end Assembly

/-! ## 5. The envelope of `𝒦` -/

section Envelope

/-- `List.ofFn (fun i : Fin n => l.getD i d) = l` when `l.length = n` (`GDN:771`). -/
private theorem gdn_ofFn_getD {α : Type*} (l : List α) (d : α) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i d) = l := by
  subst h
  refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
  simp

/-- A well-formed loop is `loopOf` of its own signs and labels (`GDN:778`). -/
private theorem gdn_loopOf_eq {d L : ℕ} [NeZero L] (J : LoopIdx (Zd d L)) (hJ : J.WF) :
    loopOf (fun i : Fin J.length => J.σ.getD i false)
      (fun i : Fin J.length => J.a.getD i (0 : Zd d L)) = J := by
  obtain ⟨σ', a'⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [loopOf, LoopIdx.length]
  rw [gdn_ofFn_getD σ' false a'.length hJ, gdn_ofFn_getD a' 0 a'.length rfl]

/-- **A deterministic envelope of `𝒦` exists.**  For `|E| < 2`, `0 ≤ v < 1` and every `k`, there is
`B ≥ 0` with `‖𝒦_w(J)‖ ≤ B` for all `w ∈ [0, v]` and all well-formed loops `J` of length in
`[2, k]`: `w ↦ 𝒦_w(J)` is continuous on `[0, 1)` (it is differentiable there, `KLK_isKLoop`), and
there are finitely many loops of length `≤ k` over `Zd d L`.  (No analogue in RBM2D: its envelope
witness `exists_norm_Kcal_le_win` is asymptotic.)  It discharges the envelope hypothesis of
`gridDriftN` at a concrete size index. -/
theorem GridDriftN_exists_envelope {d L W : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) (hW : 1 ≤ W)
    {E : ℝ} (hE : |E| < 2) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      J.length ≤ k → ‖KLK d L g W E w J‖ ≤ B := by
  have h1 : ∀ ℓ : ℕ, ∀ p : (Fin ℓ → Bool) × (Fin ℓ → Zd d L), ∃ C : ℝ, 0 ≤ C ∧
      (2 ≤ ℓ → ∀ w ∈ Set.Icc (0 : ℝ) v, ‖KLK d L g W E w (loopOf p.1 p.2)‖ ≤ C) := by
    intro ℓ p
    by_cases hℓ : 2 ≤ ℓ
    · have hcont : ContinuousOn (fun w : ℝ => KLK d L g W E w (loopOf p.1 p.2)) (Set.Icc 0 v) := by
        intro w hw
        refine ContinuousAt.continuousWithinAt ?_
        have hwf : (loopOf p.1 p.2).WF := gdn_loopOf_wf p.1 p.2
        have hlen : 2 ≤ (loopOf p.1 p.2).length := by rw [gdn_loopOf_length]; exact hℓ
        exact (gdn_hasDeriv (g := g) (W := W) hL hW hE hw.1 (lt_of_le_of_lt hw.2 hv1) hwf
          hlen).continuousAt
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := v)).exists_bound_of_continuousOn hcont
      exact ⟨max C 0, le_max_right _ _, fun _ w hw => (hC w hw).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hℓ⟩
  choose C hC0 hC using h1
  refine ⟨∑ ℓ ∈ Finset.range (k + 1), ∑ p : (Fin ℓ → Bool) × (Fin ℓ → Zd d L), C ℓ p,
    Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun p _ => hC0 ℓ p, ?_⟩
  intro w hw J hJ h2 hk
  have hJe := gdn_loopOf_eq J hJ
  have hb := hC J.length (fun i => J.σ.getD i false, fun i => J.a.getD i (0 : Zd d L)) h2 w hw
  simp only at hb
  rw [hJe] at hb
  refine hb.trans ?_
  have hmem : J.length ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  refine le_trans ?_ (Finset.single_le_sum (f := fun ℓ => ∑ p : (Fin ℓ → Bool) × (Fin ℓ → Zd d L),
    C ℓ p) (fun ℓ _ => Finset.sum_nonneg fun p _ => hC0 ℓ p) hmem)
  exact Finset.single_le_sum (f := fun p : (Fin J.length → Bool) × (Fin J.length → Zd d L) =>
    C J.length p) (fun p _ => hC0 _ p) (Finset.mem_univ _)

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{w,0} ≤ 2 (1 - v)⁻¹` for `0 ≤ w ≤ v < 1` (replaces RBM2D's `kloop_Mt_eq` chain of
`Path/ScalesBridge`): `B_{w,0} = (g² + 1 - w)⁻¹ + (L^d (1 - w))⁻¹ ≤ 2 (1 - w)⁻¹`. -/
private theorem gdn_Bctl_le (n : ℕ) {w v : ℝ} (hw0 : 0 ≤ w) (hwv : w ≤ v) (hv1 : v < 1) :
    sz.Bctl n w ≤ 2 * (1 - v)⁻¹ := by
  have hw1 : 0 < 1 - w := by linarith
  have hv : 0 < 1 - v := by linarith
  have hwv' : (1 - w)⁻¹ ≤ (1 - v)⁻¹ := inv_anti₀ hv (by linarith)
  have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
    exact one_le_pow₀ this
  have hLd : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    exact one_le_pow₀ this
  have habs : |1 - w| = 1 - w := abs_of_pos hw1
  have hB : Bparam d (sz.L n) (sz.lam n) w 0 ≤ 2 * (1 - v)⁻¹ := by
    unfold Bparam
    rw [habs]
    have e1 : (sz.lam n ^ 2 + (1 - w))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (1 - w)⁻¹ := by
      have : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
      rw [this, mul_one]
      exact inv_anti₀ hw1 (by nlinarith [sq_nonneg (sz.lam n)])
    have e2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - w))⁻¹ ≤ (1 - w)⁻¹ := by
      refine inv_anti₀ hw1 ?_
      nlinarith
    linarith
  have hB0 : 0 ≤ Bparam d (sz.L n) (sz.lam n) w 0 := by
    unfold Bparam
    rw [habs]
    positivity
  unfold Sizes.Bctl
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) w 0
      ≤ 1 * Bparam d (sz.L n) (sz.lam n) w 0 :=
        mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hWd) hB0
    _ ≤ 2 * (1 - v)⁻¹ := by rw [one_mul]; exact hB

/-- The deterministic content of `STKbound` along a window: if `STKbound` holds, then eventually in
`n`, for every `w ∈ [0, v_n]`, every sign vector and label vector of length `k ≥ 1`,
`‖𝒦_w(σ, a)‖ ≤ N^τ (W^{-d} B_{w,0})^{k-1}`.  `≺` of a deterministic quantity is a deterministic
inequality (the bad event is `∅` or the whole space, and `P(bad) ≤ N^{-1} < 1`); the supremum over
`w` is taken by choosing the worst `w_n` and applying `STKbound` to the sequence `w_n`. -/
private theorem gdn_STKbound_win {E : ℕ → ℝ} (hKb : sz.STKbound E) (hsz : sz.SizeTendsto)
    (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (k : ℕ) (hk : 1 ≤ k) (τ : ℝ)
    (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖sz.STKloop n (E n) w σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n w) ^ (k - 1) := by
  classical
  by_contra hcon
  have hfreq := Filter.not_eventually.1 hcon
  let bad : ℕ → Prop := fun n => ∃ w ∈ Set.Icc (0 : ℝ) (v n), ∃ (σ : Fin k → Bool)
      (a : Fin k → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n w) ^ (k - 1) < ‖sz.STKloop n (E n) w σ a‖
  have hbad : ∀ n, ¬ (∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ (σ : Fin k → Bool)
      (a : Fin k → Zd d (sz.L n)),
      ‖sz.STKloop n (E n) w σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n w) ^ (k - 1)) →
      bad n := by
    intro n hn
    by_contra hb
    exact hn fun w hw σ a => by
      by_contra hc
      exact hb ⟨w, hw, σ, a, not_le.1 hc⟩
  let w' : ℕ → ℝ := fun n => if h : bad n then Classical.choose h else 0
  have hw'mem : ∀ n, w' n ∈ Set.Icc (0 : ℝ) (v n) := by
    intro n
    by_cases h : bad n
    · have e : w' n = Classical.choose h := by simp [w', h]
      rw [e]
      exact (Classical.choose_spec h).1
    · have e : w' n = 0 := by simp [w', h]
      rw [e]
      exact ⟨le_rfl, hv0 n⟩
  have hprec := hKb w' (fun n => (hw'mem n).1) (fun n => lt_of_le_of_lt (hw'mem n).2 (hv1 n)) k hk
    τ hτ 1 one_pos
  have hsize2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (Filter.tendsto_atTop.1 hsz) 2
  obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hprec.and hsize2)).exists
  have hwn : bad n := hbad n hn1
  have hex : ∃ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (w' n)) ^ (k - 1) <
        ‖sz.STKloop n (E n) (w' n) σ a‖ := by
    have hspec := Classical.choose_spec hwn
    have e : w' n = Classical.choose hwn := by simp [w', hwn]
    rw [e]
    exact hspec.2
  obtain ⟨σ, a, hσa⟩ := hex
  have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
    refine (measure_univ (μ := Sizes.seqP sz)).symm.le.trans ((measure_mono ?_).trans hn2)
    intro ω _
    exact ⟨(σ, a), hσa⟩
  have h2 := ENNReal.one_le_ofReal.1 h1
  rw [Real.rpow_neg_one] at h2
  have h3 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hn3
  linarith [h3, show (2 : ℝ)⁻¹ < 1 by norm_num]

/-- `W^{-d} B_{w,0} ≥ 0` for `w < 1`. -/
private theorem gdn_Bctl_nonneg (n : ℕ) {w : ℝ} (hw1 : w < 1) : 0 ≤ sz.Bctl n w := by
  have hw : 0 < 1 - w := by linarith
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hw]
  positivity

/-- **The envelope witness** (RBM2D `exists_norm_Kcal_le_win`, `GDN:792`; RBM1D
`exists_norm_Kval_le_win`, `Gauss/DriftEnvelope.lean:246` at `c06b103`).  Fixed `m` and `τ > 0`: for
a time sequence `v_n ∈ [0, 1)`, eventually in `n`, uniformly over `w ∈ [0, v_n]` and the
well-formed loops `J` of length in `[2, m]`, `‖𝒦_w(J)‖ ≤ N^τ η_{v_n}^{-m}`, `N = sz.size n = (W L)^d`.
**Form change (paper-delta candidate T2111a).**  RBM2D proves the bound from `Kbound_prec_uncond`
(`Loop/KBound`), uniformly over all `(L, W, E, u, v)` with `W² L² = N`; RBM3D has no proof of the
`≺` bound of `𝒦` (`STKbound`, `ML:Kbound`, `1_2:1056`, registered *owed*, KL7), and a single size
sequence carries it, so the statement is along the sequence `sz` with `STKbound sz E` and
`N → ∞` (`SizeTendsto`) as hypotheses.  The supremum over `w ∈ [0, v_n]` (RBM2D: over `u ≤ v`)
is kept.  `STKbound` is a `≺` statement, hence the factor `N^τ`; `W^{-d} B_{w,0} ≤ 2 η_v⁻¹` replaces
`Mt⁻¹ ≤ η_v⁻¹` (`gdn_Bctl_le`), and the `2^{m}` is absorbed by `N^{τ/2}`. -/
theorem exists_norm_Kcal_le_win (hsz : sz.SizeTendsto) (E : ℕ → ℝ) (hKb : sz.STKbound E)
    (hE : ∀ n, |E n| < 2) (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (m : ℕ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ m →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (E n) (v n))⁻¹) ^ m := by
  have hall : ∀ᶠ n in atTop, ∀ ℓ ∈ Finset.Icc 2 m, ∀ w ∈ Set.Icc (0 : ℝ) (v n),
      ∀ (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d (sz.L n)),
        ‖sz.STKloop n (E n) w σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n w) ^ (ℓ - 1) :=
    (Filter.eventually_all_finset _).2 fun ℓ hℓ =>
      gdn_STKbound_win sz hKb hsz v hv0 hv1 ℓ (by have := (Finset.mem_Icc.1 hℓ).1; omega) (τ / 2)
        (half_pos hτ)
  have hpow : ∀ᶠ n in atTop, (2 : ℝ) ^ m ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) atTop atTop :=
      (tendsto_rpow_atTop (half_pos hτ)).comp hsz
    exact h1.eventually_ge_atTop _
  have hsize1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (Filter.tendsto_atTop.1 hsz) 1
  filter_upwards [hall, hpow, hsize1] with n hn hp hs1
  intro w hw J hJ h2 hJm
  have hℓ : J.length ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨h2, hJm⟩
  have hb := hn J.length hℓ w hw (fun i : Fin J.length => J.σ.getD i false)
    (fun i : Fin J.length => J.a.getD i (0 : Zd d (sz.L n)))
  have hJe := gdn_loopOf_eq J hJ
  have hb' : ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n w) ^ (J.length - 1) := by
    have e : ∀ (σ' : Fin J.length → Bool) (a' : Fin J.length → Zd d (sz.L n)),
        sz.STKloop n (E n) w σ' a' = KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w (loopOf σ' a') :=
      fun _ _ => rfl
    rw [e, hJe] at hb
    exact hb
  have hv : v n < 1 := hv1 n
  have hηpos : 0 < etaT (E n) (v n) := etaT_pos (hE n) hv
  have hηle : etaT (E n) (v n) ≤ 1 - v n := by
    have him : (mE (E n)).im ≤ 1 := by
      rw [mE_im]
      have : Real.sqrt (4 - E n ^ 2) ≤ 2 :=
        Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg (E n)]⟩
      linarith
    have him0 : 0 ≤ (mE (E n)).im := (mE_im_pos (hE n)).le
    calc etaT (E n) (v n) = (1 - v n) * (mE (E n)).im := rfl
      _ ≤ (1 - v n) * 1 := mul_le_mul_of_nonneg_left him (by linarith)
      _ = 1 - v n := mul_one _
  have hη1 : etaT (E n) (v n) ≤ 1 := by linarith [(hv0 n)]
  have hx1 : 1 ≤ (etaT (E n) (v n))⁻¹ := (one_le_inv₀ hηpos).2 hη1
  have hBle : sz.Bctl n w ≤ 2 * (etaT (E n) (v n))⁻¹ := by
    refine (gdn_Bctl_le sz n hw.1 hw.2 hv).trans ?_
    have : (1 - v n)⁻¹ ≤ (etaT (E n) (v n))⁻¹ := inv_anti₀ hηpos hηle
    linarith
  have hB0 : 0 ≤ sz.Bctl n w := gdn_Bctl_nonneg sz n (lt_of_le_of_lt hw.2 hv)
  have hpow2 : (sz.Bctl n w) ^ (J.length - 1) ≤ (2 : ℝ) ^ m * ((etaT (E n) (v n))⁻¹) ^ m := by
    calc (sz.Bctl n w) ^ (J.length - 1) ≤ (2 * (etaT (E n) (v n))⁻¹) ^ (J.length - 1) :=
          pow_le_pow_left₀ hB0 hBle _
      _ = 2 ^ (J.length - 1) * ((etaT (E n) (v n))⁻¹) ^ (J.length - 1) := mul_pow _ _ _
      _ ≤ 2 ^ m * ((etaT (E n) (v n))⁻¹) ^ m := by
          refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
            (pow_le_pow_right₀ hx1 (by omega)) (by positivity) (by positivity)
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  calc ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (sz.Bctl n w) ^ (J.length - 1) := hb'
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((2 : ℝ) ^ m * ((etaT (E n) (v n))⁻¹) ^ m) :=
        mul_le_mul_of_nonneg_left hpow2 (Real.rpow_nonneg hNpos.le _)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          ((etaT (E n) (v n))⁻¹) ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _)
        exact mul_le_mul_of_nonneg_right hp (by positivity)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (E n) (v n))⁻¹) ^ m := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]
        congr 2
        ring

end Envelope


/-! ## 6. Compiled nonempty instances at the admissible sequence `sz0`

`RBM.Gauss.SizesInst.sz0` (`RBM3D/Defs/Sizes.lean`): `d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`,
`size 0 = 2097152`.  Grid data `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4` (`Δ = 1/10`, `u_0 = 1/10`,
`u_1 = 1/5`), energy `E ≡ 0`, size index `n = 0`, step `j = 0 < 4`, loop length `k = 3`,
`σ = (+,-,+)`.  `gridDriftN`: every deterministic hypothesis is discharged, the envelope `B_3` is
supplied by `GridDriftN_exists_envelope`.  `exists_norm_Kcal_le_win`: the owed pin `STKbound sz0 E`
(registered, `RBM3D/Test/Axioms.lean`; proved by KL7) stays a hypothesis of the example; `SizeTendsto`
is `sz0_tendsto`, the other hypotheses are discharged. -/

namespace GridDriftNCheck

open RBM.Gauss.SizesInst

/-- `E ≡ 0`. -/
abbrev E0 : ℕ → ℝ := fun _ => 0
/-- `s ≡ 1/10`. -/
abbrev s0 : ℕ → ℝ := fun _ => 1 / 10
/-- `t ≡ 1/2`. -/
abbrev t0 : ℕ → ℝ := fun _ => 1 / 2
/-- `K ≡ 4`. -/
abbrev K0 : ℕ → ℕ := fun _ => 4

/-- The grid data are nondegenerate: `Δ = 1/10`, `u_0 = 1/10`, `u_1 = 1/5 < 1`. -/
theorem data : gridStep s0 t0 K0 0 = 1 / 10 ∧ gridTime s0 t0 K0 0 0 = 1 / 10 ∧
    gridTime s0 t0 K0 0 (0 + 1) = 1 / 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [gridStep, gridTime]

/-- **`gridDriftN` at `sz0`**, `k = 3`, `σ = (+,-,+)`, `j = 0`: one grid step of `LK_SDE` for the
size sequence `sz0` and every label `a ∈ (Z_4^3)^3`, with a deterministic envelope `B_3 ≥ 0` of
`𝒦` on `[0, u_1]` (it exists: `GridDriftN_exists_envelope`).  No hypothesis is left open. -/
theorem gridDriftN_instance :
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ᵐ ω ∂(pathP sz0), ∀ a : Fin 3 → Zd 3 (sz0.L 0),
      ‖predIncN sz0 E0 s0 t0 K0 0 0 ![true, false, true] ω a - (gridStep s0 t0 K0 0 : ℂ) *
          (∑ l ∈ Finset.Icc 3 3, sz0.STksimLKM 0 (E0 0) (gridTime s0 t0 K0 0 0)
              (pathH sz0 s0 t0 K0 0 0 ω) l (loopOf ![true, false, true] a) +
            sz0.STelklkM 0 (E0 0) (gridTime s0 t0 K0 0 0) (pathH sz0 s0 t0 K0 0 0 ω)
              (loopOf ![true, false, true] a) +
            sz0.STegtM 0 (E0 0) (gridTime s0 t0 K0 0 0) (pathH sz0 s0 t0 K0 0 0 ω)
              (loopOf ![true, false, true] a))‖
        ≤ stepErrN 3 (sz0.L 0) (sz0.W 0) (E0 0) 3 (gridTime s0 t0 K0 0 0)
            (gridTime s0 t0 K0 0 (0 + 1)) (gridStep s0 t0 K0 0) Bk := by
  obtain ⟨_, _, _, hv1, _⟩ := gdn_time_facts s0 t0 K0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Bk, hB0, hB⟩ := GridDriftN_exists_envelope (d := 3) (L := sz0.L 0) (W := sz0.W 0)
    (g := sz0.lam 0) (sz0.three_le_L 0) (sz0.W_pos 0) (E := E0 0) (by norm_num)
    (v := gridTime s0 t0 K0 0 (0 + 1)) (by rw [data.2.2]; norm_num) hv1 3
  exact ⟨Bk, hB0, gridDriftN sz0 E0 s0 t0 K0 (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) 0 0 (by norm_num) 3
    (by norm_num) ![true, false, true] Bk hB0 hB⟩

/-- **The envelope `B_3` exists at `sz0`** (`GridDriftN_exists_envelope`, `n = 0`, `v = u_1 = 1/5`,
`k = 3`): a finite `B ≥ 0` with `‖𝒦_w(J)‖ ≤ B` on `[0, 1/5]` for the loops of length `2` and `3`. -/
theorem envelope_instance :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) (1 / 5), ∀ J : LoopIdx (Zd 3 (sz0.L 0)), J.WF →
      2 ≤ J.length → J.length ≤ 3 → ‖KLK 3 (sz0.L 0) (sz0.lam 0) (sz0.W 0) 0 w J‖ ≤ B :=
  GridDriftN_exists_envelope (d := 3) (L := sz0.L 0) (W := sz0.W 0) (g := sz0.lam 0)
    (sz0.three_le_L 0) (sz0.W_pos 0) (E := 0) (by norm_num) (v := 1 / 5) (by norm_num)
    (by norm_num) 3

/-- **`exists_norm_Kcal_le_win` at `sz0`**, `E ≡ 0`, `v ≡ 1/2`, `m = 3`, `τ = 1`: eventually in `n`,
`‖𝒦_w(J)‖ ≤ N η_{1/2}^{-3}` for `w ∈ [0, 1/2]` and the well-formed loops of length `2` and `3`.  The
owed pin `STKbound sz0 E0` is the hypothesis; `SizeTendsto` is `sz0_tendsto`. -/
theorem exists_norm_Kcal_le_win_instance (hKb : sz0.STKbound E0) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 3 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) (1 / 2))⁻¹) ^ 3 :=
  exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) 3 1 one_pos

end GridDriftNCheck

end RBM.Ind

end

#print axioms RBM.Ind.kStepC
#print axioms RBM.Ind.uStepC
#print axioms RBM.Ind.stepErrN
#print axioms RBM.Ind.GridDriftN
#print axioms RBM.Ind.gridDriftN_at
#print axioms RBM.Ind.gridDriftN
#print axioms RBM.Ind.GridDriftN_exists_envelope
#print axioms RBM.Ind.exists_norm_Kcal_le_win
#print axioms RBM.Ind.GridDriftNCheck.data
#print axioms RBM.Ind.GridDriftNCheck.gridDriftN_instance
#print axioms RBM.Ind.GridDriftNCheck.envelope_instance
#print axioms RBM.Ind.GridDriftNCheck.exists_norm_Kcal_le_win_instance
