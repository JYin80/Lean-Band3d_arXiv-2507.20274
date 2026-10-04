/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.GridDriftN
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.HierAlgebra
import RBM3D.Induction.Step34Pins

/-!
# The `𝒬`-hierarchy on the grid (`d ≥ 3`)

Ticket T2132 (S3-13a).  Paper: arXiv:2507.20274, `3_5` (`Def:QtPt` `3_5:1204`, `zjuii1`-`zjuii2`
`3_5:1300-1330`, `int_K-L+Q` `3_5:1337-1346`).  Port of RBM2D `Induction/AltGridQ.lean` at
commit `c9a24cf` (sections 1-9 and 11; cited `AltGridQ:<line>`), with `Z2 L ↦ Zd d L`,
`W² ↦ W^d`, `L² ↦ L^d`, tensors of `m + 1` indices (`Fin (m+1)`, no `[NeZero k]`), the merged
`STQop`, `STPsum`, `ThetaN`, `Ugen`, `AvecN`, `martIncN`, and an abstract mollifier family `ϑ`
(RBM2D's `Θ`-product `ϑ` is not admissible at `d ≥ 3`, docstring of `STMollifierProps`).

## Main results (namespace `RBM.Ind`)

* **Definitions** (target 1): `aTrueQN` (`A^Q_j = 𝒬_{u_j} A_j`), `dGridQN` (the drift
  `𝒬_u D + ℬ₄ + ℬ₅`), `aFrozQN`, `martIncQN`, `rGridQN`, `lkEnvN`, `driftEnvN`, `qStepErrN`,
  `qErrQN`.
* **`gridDriftQN`** (target 2): a.e., for every label,
  `‖𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1}} A^Q_j - Δ dGridQN_j‖ ≤ qErrQN_j`, for the merged
  mollifier `QopAlgebra_mollifier`; `QGridA_gridDriftQN_of` is the same for any `ϑ` with
  `STMollifierProps`, differentiable on `[0,1)`, and the Taylor bound `QGridA_Taylor2 C₂ ϑ` as
  a hypothesis.
* **`stoppedDuhamelQN`** (target 3): the pathwise stopped Duhamel expansion of `aFrozQN`
  (any `ϑ`).
* `QGridA_Taylor2`, `QGridA_mollifier_taylor2`: the time regularity of `ϑ` (below).

Not here: RBM2D's section 10 (`sum_weighted_qErrQN_le`, the summed envelope), which needs
`sum_weighted_stepErrN_le` of ST2-31 (S3-13b).

## The sign of `ℬ₅`

The paper writes `ℬ₅(u) := -[𝒫∘(𝓛-𝒦)_{u,σ}]_{a₁} ∂_uϑ` (`3_5:1345`, last term of `zjuii1`
`3_5:1315`), with the minus sign inside `ℬ₅`; `QopAlgebra_Qop_hasDerivAt` has
`-(𝒫𝒜)_{a₁} ∂_tϑ`.  `dGridQN` carries `ℬ₅` with this sign
(`- STPsum X (a 0) * deriv (fun τ => ϑ τ a) u`).  RBM2D's paper-delta #122 corrects a `+`
printed in the `d = 2` paper; the `d ≥ 3` paper prints `-`, so there is no sign delta here.

## Time regularity of `ϑ` (route (b) of the ticket)

The one-step remainder contains `𝒫X (ϑ_u - ϑ_v + Δ ∂_uϑ_u)` (term `T1` of
`QGridA_qstep_algebra`), which needs a second-order Taylor bound of `t ↦ ϑ_t`:
`‖ϑ_v - ϑ_u - Δ ∂_uϑ_u‖ ≤ C₂ (1-v)⁻² Δ²`.  `STMollifierProps` gives only the sup bound,
differentiability and `|∂_tϑ| ≤ C (1-t)⁻¹ (ℓ_t^d)^{-m}`.  With the first-order bound alone
(mean-value theorem) the bound of `T1` is `Lp Mk 2 C β Δ` per step (`Lp = (L^d)^m`,
`β = (1-v)⁻¹`), which sums over the `K` grid steps to `Lp Mk 2 C β (t-s)`, independent of `K`,
so it cannot be absorbed by `N^{-D_t}` as `K` grows; with the Taylor bound the bound of `T1`
is `Lp Mk C₂ β² Δ²`.  Hence `QGridA_Taylor2 C₂ ϑ` is a hypothesis of the general theorem, and
`QGridA_mollifier_taylor2` proves it for the merged mollifier with `C₂ = 1000 (1 + d m)²`
(second `t`-derivative of `exp(-u_t S)/z(u_t)^{dm}` through `u_t = y_t⁻¹ + L⁻¹`, with
`u z₂ ≤ 40 z`, `u² z₃ ≤ 160 z`, `z ≥ 1`; sections 4a-4d).  No change of `STMollifierProps`
is needed.  The error terms are then `S = stepErrN = O(Δ^{3/2})` and `O(Δ²)` with
polynomial-in-`N` prefactors `(1 + C (L^d)^m)` (S3-13b sums them).

## Conventions

All helpers are `private` with the prefix `QGridA_`; copies of private helpers of the merged
`GridDriftN.lean` (`gdn_*`) and of `QopAlgebra.lean` (`qa*`) carry that prefix too.  Hypotheses
are at the size index `n` only (DECISIONS §29 (4)).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The abstract `k`-slot tensor step -/

section TensorStep

variable {d L : ℕ} [NeZero L]

/-- `(⊗_i U_i) A` at `x`: `Σ_y (Π_i U_i(x_i, y_i)) A(y)`. -/
private def QGridA_Tens {k : ℕ} (U : Fin k → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin k → Zd d L) → ℂ)
    (x : Fin k → Zd d L) : ℂ :=
  ∑ y : Fin k → Zd d L, (∏ i, U i (x i) (y i)) * A y

/-- `(Σ_i (1 ⊗ ⋯ ⊗ G_i ⊗ ⋯ ⊗ 1)) A` at `x`. -/
private def QGridA_Gen {k : ℕ} (G : Fin k → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin k → Zd d L) → ℂ)
    (x : Fin k → Zd d L) : ℂ :=
  ∑ i : Fin k, ∑ c : Zd d L, G i (x i) c * A (Function.update x i c)

private theorem QGridA_Tens_zero (U : Fin 0 → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin 0 → Zd d L) → ℂ)
    (x : Fin 0 → Zd d L) : QGridA_Tens U A x = A x := by
  unfold QGridA_Tens
  rw [Finset.sum_eq_single x (fun y _ hy => absurd (Subsingleton.elim y x) hy)
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem QGridA_Gen_zero (G : Fin 0 → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin 0 → Zd d L) → ℂ)
    (x : Fin 0 → Zd d L) : QGridA_Gen G A x = 0 := by
  simp [QGridA_Gen]

private theorem QGridA_Tens_succ {k : ℕ} (U : Fin (k + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin (k + 1) → Zd d L) → ℂ) (x : Fin (k + 1) → Zd d L) :
    QGridA_Tens U A x = ∑ y0 : Zd d L, U 0 (x 0) y0 *
      QGridA_Tens (fun i : Fin k => U i.succ) (fun y' => A (Fin.cons y0 y')) (Fin.tail x) := by
  unfold QGridA_Tens
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Zd d L)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail, mul_assoc]

private theorem QGridA_Gen_succ {k : ℕ} (G : Fin (k + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin (k + 1) → Zd d L) → ℂ) (x : Fin (k + 1) → Zd d L) :
    QGridA_Gen G A x = ∑ c : Zd d L, G 0 (x 0) c * A (Fin.cons c (Fin.tail x)) +
      QGridA_Gen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x) := by
  unfold QGridA_Gen
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
private theorem QGridA_row_mul {P : Matrix (Zd d L) (Zd d L) ℂ} {r m : ℝ}
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
private theorem QGridA_row_one_add {e : Matrix (Zd d L) (Zd d L) ℂ} {a : ℝ}
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
private theorem QGridA_one_add_mul (e : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) (f : Zd d L → ℂ) :
    ∑ c : Zd d L, (1 + e) x c * f c = f x + ∑ c : Zd d L, e x c * f c := by
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

/-- The first-order tensor bound: `‖(⊗U_i) A - A‖ ≤ ((1+a)^k - 1) M`. -/
private theorem QGridA_tens_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ (k : ℕ) (U : Fin k → Matrix (Zd d L) (Zd d L) ℂ),
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1) x c‖ ≤ a) →
      ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖QGridA_Tens U A x - A x‖ ≤ ((1 + a) ^ k - 1) * M := by
  intro k
  induction k with
  | zero =>
      intro U _ A M _ x
      rw [QGridA_Tens_zero]
      simp
  | succ k ih =>
      intro U hU A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      have hpow : 1 ≤ (1 + a) ^ k := one_le_pow₀ (by linarith)
      set e : Matrix (Zd d L) (Zd d L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      have hrow : ∀ x' : Zd d L, ∑ c : Zd d L, ‖U 0 x' c‖ ≤ 1 + a := by
        intro x'; rw [hU0]; exact QGridA_row_one_add (fun x'' => hU 0 x'') x'
      set T : Zd d L → ℂ := fun y0 => QGridA_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Zd d L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        ih (fun i => U i.succ) (fun i x' => hU i.succ x') (fun y' => A (Fin.cons y0 y')) M
          (fun y' => hA _) (Fin.tail x)
      have hsplit : QGridA_Tens U A x - A x =
          ∑ c : Zd d L, U 0 (x 0) c * (T c - Y c) + ∑ c : Zd d L, e (x 0) c * Y c := by
        rw [QGridA_Tens_succ, hAx]
        have h1 : ∑ c : Zd d L, U 0 (x 0) c * T c =
            ∑ c : Zd d L, U 0 (x 0) c * (T c - Y c) + ∑ c : Zd d L, U 0 (x 0) c * Y c := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Zd d L, U 0 (x 0) c * Y c = Y (x 0) + ∑ c : Zd d L, e (x 0) c * Y c := by
          rw [hU0]; exact QGridA_one_add_mul e (x 0) Y
        rw [h1, h2]
        ring
      rw [hsplit]
      have hb1 : ‖∑ c : Zd d L, U 0 (x 0) c * (T c - Y c)‖ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) :=
        QGridA_row_mul hrow (x 0) hTY
      have hb2 : ‖∑ c : Zd d L, e (x 0) c * Y c‖ ≤ a * M :=
        QGridA_row_mul (fun x' => hU 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖∑ c : Zd d L, U 0 (x 0) c * (T c - Y c)‖ + ‖∑ c : Zd d L, e (x 0) c * Y c‖ :=
            norm_add_le _ _
        _ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) + a * M := add_le_add hb1 hb2
        _ = ((1 + a) ^ (k + 1) - 1) * M := by ring

/-- The second-order tensor bound: with `‖(U_i - 1)‖_rows ≤ a`, `‖(U_i - 1 - G_i)‖_rows ≤ b`,
`‖(⊗U_i) A - A - (Σ_i G_i) A‖ ≤ (k b + (1+a)^k - 1 - k a) M`. -/
private theorem QGridA_tens_step_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ (k : ℕ) (U G : Fin k → Matrix (Zd d L) (Zd d L) ℂ),
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1) x c‖ ≤ a) →
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1 - G i) x c‖ ≤ b) →
      ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖QGridA_Tens U A x - A x - QGridA_Gen G A x‖ ≤ ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M := by
  intro k
  induction k with
  | zero =>
      intro U G _ _ A M _ x
      rw [QGridA_Tens_zero, QGridA_Gen_zero]
      simp
  | succ k ih =>
      intro U G hU hG A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      set e : Matrix (Zd d L) (Zd d L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      set T : Zd d L → ℂ := fun y0 => QGridA_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Zd d L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        QGridA_tens_sub_le ha k (fun i => U i.succ) (fun i x' => hU i.succ x')
          (fun y' => A (Fin.cons y0 y')) M (fun y' => hA _) (Fin.tail x)
      have hIH : ‖T (x 0) - Y (x 0) - QGridA_Gen (fun i : Fin k => G i.succ)
          (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x)‖ ≤
          ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M :=
        ih (fun i => U i.succ) (fun i => G i.succ) (fun i x' => hU i.succ x')
          (fun i x' => hG i.succ x') (fun y' => A (Fin.cons (x 0) y')) M (fun y' => hA _)
          (Fin.tail x)
      set g' : ℂ := QGridA_Gen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y'))
        (Fin.tail x) with hg'
      have hsplit : QGridA_Tens U A x - A x - QGridA_Gen G A x =
          (T (x 0) - Y (x 0) - g') + ∑ c : Zd d L, e (x 0) c * (T c - Y c) +
            ∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c := by
        rw [QGridA_Tens_succ, QGridA_Gen_succ, hAx]
        have h1 : ∑ c : Zd d L, U 0 (x 0) c * T c =
            T (x 0) + ∑ c : Zd d L, e (x 0) c * (T c - Y c) + ∑ c : Zd d L, e (x 0) c * Y c := by
          rw [hU0, QGridA_one_add_mul, add_assoc, ← Finset.sum_add_distrib]
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
        QGridA_row_mul (fun x' => hU 0 x') (x 0) hTY
      have hb3 : ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ ≤ b * M :=
        QGridA_row_mul (fun x' => hG 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖T (x 0) - Y (x 0) - g' + ∑ c : Zd d L, e (x 0) c * (T c - Y c)‖ +
            ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ := norm_add_le _ _
        _ ≤ (‖T (x 0) - Y (x 0) - g'‖ + ‖∑ c : Zd d L, e (x 0) c * (T c - Y c)‖) +
            ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M + a * (((1 + a) ^ k - 1) * M)) +
            b * M := by gcongr
        _ = (((k + 1 : ℕ) : ℝ) * b + ((1 + a) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * a)) * M := by
            push_cast; ring

end TensorStep

section UStep

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- A row `ℓ¹` norm is at most the `ℓ^∞` operator norm (copied from the private
`sum_norm_row_le_opNorm` of `Path/UBounds.lean`). -/
private theorem QGridA_sum_norm_row_le_opNorm (M : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) :
    ∑ c : Zd d L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Zd d L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Zd d L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Zd d L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- `‖Θ_z‖ ≤ (1 - ‖z‖)⁻¹` for complex `z`, `‖z‖ < 1` (copied from the private
`norm_Theta_le_of_lt` of `Path/UBounds.lean`; merged `norm_Theta_le` at `z = ‖z‖ · (z/‖z‖)`). -/
private theorem QGridA_norm_Theta_le_of_lt (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) :
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
private theorem QGridA_row_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ =
      ‖ξ‖ * ‖(SB d L g * Theta d L g ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((QGridA_sum_norm_row_le_opNorm _ x).trans ?_) (norm_nonneg _)
  calc ‖SB d L g * Theta d L g ((s : ℂ) * ξ)‖ ≤ ‖SB d L g‖ * ‖Theta d L g ((s : ℂ) * ξ)‖ :=
      norm_mul_le _ _
    _ = ‖Theta d L g ((s : ℂ) * ξ)‖ := by rw [norm_SB d L g hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := QGridA_norm_Theta_le_of_lt hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u` (copied from the
private `sum_norm_thetaGenMat_diff_row_le` of `Path/UBounds.lean`; resolvent identity
`Theta_sub_Theta`). -/
private theorem QGridA_row_thetaGenMat_diff (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
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
  refine mul_le_mul_of_nonneg_left ((QGridA_sum_norm_row_le_opNorm _ x).trans ?_) (by positivity)
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
        mul_le_mul (QGridA_norm_Theta_le_of_lt hL hd) (QGridA_norm_Theta_le_of_lt hL hu)
          (norm_nonneg _) (inv_nonneg.mpr (by linarith))

/-- `‖(w : ℂ) ξ‖ = w` for `‖ξ‖ = 1`, `0 ≤ w`. -/
private theorem QGridA_norm_real_mul {ξ : ℂ} (hξ : ‖ξ‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    ‖(w : ℂ) * ξ‖ = w := by
  rw [norm_mul, hξ, mul_one, Complex.norm_of_nonneg hw]

/-- `(1 - vξS)Θ_{wξ} = 1 + (w - v) ξ S Θ_{wξ}`, i.e. `𝒰_{u,u+Δ} - 1 = Δ · (generator at u+Δ)`
(`def_Ustz_2`, `3_5`). -/
private theorem QGridA_ukerMat_sub_one (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ}
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
private theorem QGridA_row_U (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(uKer d L g ξ u (u + Δ) - 1) x c‖ ≤ Δ * (1 - (u + Δ))⁻¹ := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [QGridA_norm_real_mul hξ (by linarith)]; exact hv
  rw [QGridA_ukerMat_sub_one hL hd]
  have hentry : ∀ c : Zd d L, ‖((Δ : ℂ) • thetaGenMat d L g ξ (u + Δ)) x c‖ =
      Δ * ‖thetaGenMat d L g ξ (u + Δ) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  have := QGridA_row_thetaGenMat (g := g) hL hd x
  rwa [hξ, QGridA_norm_real_mul hξ (by linarith), one_mul] at this

/-- Row sums of `𝒰_{u,u+Δ} - 1 - Δ (generator at u)` are `≤ Δ² (1-(u+Δ))⁻²` for `‖ξ‖ = 1`. -/
private theorem QGridA_row_UG (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(uKer d L g ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat d L g ξ u) x c‖ ≤
      Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [QGridA_norm_real_mul hξ (by linarith)]; exact hv
  have hu : ‖(u : ℂ) * ξ‖ < 1 := by
    rw [QGridA_norm_real_mul hξ hu0]; linarith
  have hM : uKer d L g ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat d L g ξ u =
      (Δ : ℂ) • (thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) := by
    rw [QGridA_ukerMat_sub_one hL hd, smul_sub]
  rw [hM]
  have hentry : ∀ c : Zd d L, ‖((Δ : ℂ) • (thetaGenMat d L g ξ (u + Δ) -
      thetaGenMat d L g ξ u)) x c‖ =
      Δ * ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  have h1 := QGridA_row_thetaGenMat_diff (g := g) hL hΔ hu hd x
  rw [hξ, QGridA_norm_real_mul hξ (by linarith), QGridA_norm_real_mul hξ hu0] at h1
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβu : (1 - u)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hβ0 (by linarith)
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  calc Δ * ∑ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖
      ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹)) :=
        mul_le_mul_of_nonneg_left h1 hΔ
    _ ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - (u + Δ))⁻¹)) := by gcongr
    _ = Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by ring

/-- The generator kernel of `ThetaN` is `thetaGenMat`: `(μ S) Θ_{tμ} = μ (S Θ_{tμ})`. -/
private theorem QGridA_thetaKer_eq (μ : ℂ) (t : ℝ) :
    thetaKer d L g μ t = thetaGenMat d L g μ t := by
  unfold thetaKer thetaGenMat
  rw [Matrix.smul_mul]

/-- **One step of `𝒰`** (RBM1D `Uker_step_n`, `Gauss/GridHierarchyN.lean:698` at `c06b103`;
copy of the private `gdn_Ugen_step_le` of `GridDriftN.lean`, in the `Ugen`/`ThetaN` vocabulary): for `‖A‖_max ≤ M`,
`‖𝒰_{u,u+Δ,σ} A - A - Δ ϴ_{u,σ} A‖ ≤ uStepC k Δ (u+Δ) M`. -/
private theorem QGridA_Ugen_step_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1)
    (A : (Fin k → Zd d L) → ℂ) (M : ℝ) (hA : ∀ y, ‖A y‖ ≤ M) (x : Fin k → Zd d L) :
    ‖Ugen d L g E σ u (u + Δ) A x - A x -
        (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x‖ ≤
      uStepC k Δ (u + Δ) * M := by
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  have hedge : ∀ i : Fin k, ‖cycProd (fun i => mSigma E (σ i)) i‖ = 1 := fun i =>
    norm_cycProd (fun i => norm_mSigma hE (σ i)) i
  have key := QGridA_tens_step_le (d := d) (L := L) (a := Δ * (1 - (u + Δ))⁻¹)
    (b := Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2) (mul_nonneg hΔ hβ1) (by positivity) k
    (fun i : Fin k => uKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (u + Δ))
    (fun i : Fin k => (Δ : ℂ) • thetaGenMat d L g (cycProd (fun i => mSigma E (σ i)) i) u)
    (fun i x' => QGridA_row_U hL (hedge i) hu0 hΔ hv x')
    (fun i x' => QGridA_row_UG hL (hedge i) hu0 hΔ hv x') A M hA x
  have hT : QGridA_Tens (fun i : Fin k =>
      uKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (u + Δ)) A x =
      Ugen d L g E σ u (u + Δ) A x := rfl
  have hG : QGridA_Gen (fun i : Fin k =>
      (Δ : ℂ) • thetaGenMat d L g (cycProd (fun i => mSigma E (σ i)) i) u) A x =
      (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x := by
    unfold QGridA_Gen ThetaN
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, QGridA_thetaKer_eq]
    ring
  rw [hT, hG] at key
  refine key.trans (le_of_eq ?_)
  unfold uStepC
  ring

end UStep

/-! ## 3. Grid-time facts and integrability (copies of the private `gdn_*` helpers of `GridDriftN.lean`) -/

section GridFacts

variable {d : ℕ} (sz : Sizes d)

private theorem QGridA_loopOf_wf {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem QGridA_loopOf_length {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- The grid-time facts used by `gridDriftN_at`: `Δ ≥ 0`, `u_j ≥ 0`, `u_{j+1} = u_j + Δ`,
`u_{j+1} < 1`, `Δ ≤ 1` (copy of the private `gdn_time_facts`). -/
private theorem QGridA_time_facts (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hs0 : 0 ≤ s n)
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



/-- Integrability of the bounded loop observable along the walk (copy of the private
`gdn_integrable_loopL`; measurability by the merged `walk_measurable_loopL`, `walk_measurable_blockMat`,
`pathH_measurable_filt` instead of `GoodEvent_measurable_gloop`). -/
private theorem QGridA_integrable_loopL (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {E : ℝ}
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


end GridFacts

/-! ## 4a. The one-dimensional masses `z`, `z₂`, `z₃` -/

section Mollifier

private theorem QGridA_sum_zmod_val {L : ℕ} [NeZero L] (F : ℕ → ℝ) :
    ∑ y : ZMod L, F y.val = ∑ k ∈ Finset.range L, F k :=
  Finset.sum_bij (fun y _ => y.val) (fun y _ => Finset.mem_range.2 (ZMod.val_lt y))
    (fun _ _ _ _ h => ZMod.val_injective L h)
    (fun k hk => ⟨(k : ZMod L), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.1 hk)⟩)
    (fun _ _ => rfl)

/-- `z(u) = Σ_{y ∈ ℤ_L} exp(-u |y|)` (copy of the private `qaZ1` of `QopAlgebra.lean`). -/
private def QGridA_Z1 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, Real.exp (-u * (zdist L y : ℝ))

/-- `z₂(u) = Σ_y |y| exp(-u |y|)` (copy of `qaZ2`). -/
private def QGridA_Z2 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, (zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ))

/-- `z₃(u) = Σ_y |y|² exp(-u |y|)`. -/
private def QGridA_Z3 (L : ℕ) [NeZero L] (u : ℝ) : ℝ :=
  ∑ y : ZMod L, (zdist L y : ℝ) ^ 2 * Real.exp (-u * (zdist L y : ℝ))

private theorem QGridA_Z1_ge_one {L : ℕ} [NeZero L] (u : ℝ) : 1 ≤ QGridA_Z1 L u := by
  have h := Finset.single_le_sum (f := fun y : ZMod L => Real.exp (-u * (zdist L y : ℝ)))
    (fun y _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : ZMod L))
  unfold QGridA_Z1
  simpa [zdist_zero] using h

private theorem QGridA_Z1_pos {L : ℕ} [NeZero L] (u : ℝ) : 0 < QGridA_Z1 L u :=
  lt_of_lt_of_le zero_lt_one (QGridA_Z1_ge_one u)

private theorem QGridA_Z2_nonneg {L : ℕ} [NeZero L] (u : ℝ) : 0 ≤ QGridA_Z2 L u :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem QGridA_Z3_nonneg {L : ℕ} [NeZero L] (u : ℝ) : 0 ≤ QGridA_Z3 L u :=
  Finset.sum_nonneg fun _ _ => by positivity

private theorem QGridA_Z1_eq_range {L : ℕ} [NeZero L] (u : ℝ) :
    QGridA_Z1 L u = ∑ k ∈ Finset.range L, Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)) :=
  QGridA_sum_zmod_val (fun k => Real.exp (-u * ((min k (L - k) : ℕ) : ℝ)))

/-- Lower bound for the one-dimensional mass: `z(u) ≥ (e u)⁻¹` when `L⁻¹ < u` (copy of `qaZ1_ge`). -/
private theorem QGridA_Z1_ge {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u) :
    (Real.exp 1)⁻¹ * u⁻¹ ≤ QGridA_Z1 L u := by
  set k := ⌊u⁻¹⌋₊ with hk
  have hk1 : (k : ℝ) ≤ u⁻¹ := Nat.floor_le (by positivity)
  have hk2 : u⁻¹ < k + 1 := Nat.lt_floor_add_one _
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hkL : k + 1 ≤ L := by
    have h1 : (k : ℝ) < L := lt_of_le_of_lt hk1 ((inv_lt_comm₀ hu hL0).2 huL)
    exact_mod_cast h1
  rw [QGridA_Z1_eq_range]
  calc (Real.exp 1)⁻¹ * u⁻¹ ≤ ((k : ℝ) + 1) * (Real.exp 1)⁻¹ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hk2.le (inv_nonneg.2 (Real.exp_pos 1).le)
    _ = ∑ _j ∈ Finset.range (k + 1), (Real.exp 1)⁻¹ := by simp
    _ ≤ ∑ j ∈ Finset.range (k + 1), Real.exp (-u * ((min j (L - j) : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have h1 : ((min j (L - j) : ℕ) : ℝ) ≤ k := by
          exact_mod_cast (min_le_left _ _).trans hj'
        have h2 : u * ((min j (L - j) : ℕ) : ℝ) ≤ 1 := by
          calc u * ((min j (L - j) : ℕ) : ℝ) ≤ u * u⁻¹ := mul_le_mul_of_nonneg_left (h1.trans hk1) hu.le
            _ = 1 := mul_inv_cancel₀ hu.ne'
        rw [← Real.exp_neg]
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ ∑ j ∈ Finset.range L, Real.exp (-u * ((min j (L - j) : ℕ) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hkL)
          (fun _ _ _ => (Real.exp_pos _).le)

/-- Upper bound for the one-dimensional mass: `z(v) ≤ 2 (1 - e^{-v})⁻¹` (the shape of `qaZ2_le`). -/
private theorem QGridA_Z1_le {L : ℕ} [NeZero L] {v : ℝ} (hv : 0 < v) :
    QGridA_Z1 L v ≤ 2 * (1 - Real.exp (-v))⁻¹ := by
  set f : ℕ → ℝ := fun j => Real.exp (-v * j) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => (Real.exp_pos _).le
  have hS : HasSum f (1 - Real.exp (-v))⁻¹ := by
    have hr : Real.exp (-v) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have h := hasSum_geometric_of_lt_one (Real.exp_pos _).le hr
    convert h using 2 with j
    rw [← Real.exp_nat_mul]
    simp only [hf]; congr 1; ring
  have hT : ∀ n, ∑ k ∈ Finset.range n, f k ≤ (1 - Real.exp (-v))⁻¹ :=
    fun n => sum_le_hasSum _ (fun j _ => hf0 j) hS
  rw [QGridA_Z1_eq_range]
  have h1 : ∑ k ∈ Finset.range L, Real.exp (-v * ((min k (L - k) : ℕ) : ℝ))
      ≤ ∑ k ∈ Finset.range L, (f k + f (L - k)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    change f (min k (L - k)) ≤ f k + f (L - k)
    rcases min_choice k (L - k) with h | h <;> rw [h]
    · linarith [hf0 (L - k)]
    · linarith [hf0 k]
  have h2 : ∑ k ∈ Finset.range L, f (L - k) = ∑ j ∈ Finset.range L, f (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => f (j + 1)) L]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    congr 1; omega
  have h3 : ∑ j ∈ Finset.range L, f (j + 1) ≤ (1 - Real.exp (-v))⁻¹ := by
    have := Finset.sum_range_succ' f L
    have h4 := hT (L + 1)
    have h5 : 0 ≤ f 0 := hf0 0
    linarith
  rw [Finset.sum_add_distrib, h2] at h1
  linarith [hT L]

/-- `x e^{-x} ≤ 2 e^{-x/2}` and `x² e^{-x} ≤ 8 e^{-x/2}` for `x ≥ 0`. -/
private theorem QGridA_xexp (x : ℝ) (hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) ∧ x ^ 2 * Real.exp (-x) ≤ 8 * Real.exp (-(x / 2)) := by
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ x / 2 by positivity)
  have he : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (-(x / 2))
  have hmul : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 : x ≤ 2 * Real.exp (x / 2) := by nlinarith [sq_nonneg (x / 2)]
  have h2 : x ^ 2 ≤ 8 * Real.exp (x / 2) := by nlinarith [sq_nonneg (x / 2)]
  constructor
  · calc x * Real.exp (-x) = (x * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) := by rw [he]; ring
      _ ≤ ((2 * Real.exp (x / 2)) * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) := by gcongr
      _ = 2 * (Real.exp (x / 2) * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) := by ring
      _ = 2 * Real.exp (-(x / 2)) := by rw [hmul]; ring
  · calc x ^ 2 * Real.exp (-x) = (x ^ 2 * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) := by rw [he]; ring
      _ ≤ ((8 * Real.exp (x / 2)) * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) := by gcongr
      _ = 8 * (Real.exp (x / 2) * Real.exp (-(x / 2))) * Real.exp (-(x / 2)) := by ring
      _ = 8 * Real.exp (-(x / 2)) := by rw [hmul]; ring

private theorem QGridA_Z2_le_half {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) :
    u * QGridA_Z2 L u ≤ 2 * QGridA_Z1 L (u / 2) := by
  unfold QGridA_Z2 QGridA_Z1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := (QGridA_xexp (u * (zdist L y : ℝ)) (by positivity)).1
  have e1 : u * ((zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ)))
      = (u * (zdist L y : ℝ)) * Real.exp (-(u * (zdist L y : ℝ))) := by ring_nf
  have e2 : -(u * (zdist L y : ℝ) / 2) = -(u / 2) * (zdist L y : ℝ) := by ring
  rw [e1]
  rw [e2] at h
  exact h

private theorem QGridA_Z3_le_half {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) :
    u ^ 2 * QGridA_Z3 L u ≤ 8 * QGridA_Z1 L (u / 2) := by
  unfold QGridA_Z3 QGridA_Z1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := (QGridA_xexp (u * (zdist L y : ℝ)) (by positivity)).2
  have e1 : u ^ 2 * ((zdist L y : ℝ) ^ 2 * Real.exp (-u * (zdist L y : ℝ)))
      = (u * (zdist L y : ℝ)) ^ 2 * Real.exp (-(u * (zdist L y : ℝ))) := by ring_nf
  have e2 : -(u * (zdist L y : ℝ) / 2) = -(u / 2) * (zdist L y : ℝ) := by ring
  rw [e1]
  rw [e2] at h
  exact h

/-- `z(u/2) ≤ 20 z(u)` for `L⁻¹ < u ≤ 4/3`. -/
private theorem QGridA_Z1_half_le {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u)
    (hu4 : u ≤ 4 / 3) : QGridA_Z1 L (u / 2) ≤ 20 * QGridA_Z1 L u := by
  have hv : 0 < u / 2 := by positivity
  have h1 := QGridA_Z1_le (L := L) hv
  have hz1 := QGridA_Z1_ge hu huL
  have he : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  -- `(1 - e^{-v})⁻¹ ≤ (1 + v)/v`
  have hr1 : Real.exp (-(u / 2)) ≤ (1 + u / 2)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp (u / 2)])
  have hgap : (u / 2) / (1 + u / 2) ≤ 1 - Real.exp (-(u / 2)) := by
    have : 1 - (1 + u / 2)⁻¹ = (u / 2) / (1 + u / 2) := by field_simp; ring
    linarith
  have hgap0 : 0 < (u / 2) / (1 + u / 2) := by positivity
  have h2 : (1 - Real.exp (-(u / 2)))⁻¹ ≤ ((u / 2) / (1 + u / 2))⁻¹ := inv_anti₀ hgap0 hgap
  have h3 : ((u / 2) / (1 + u / 2))⁻¹ = 1 + 2 / u := by field_simp; ring
  have h4 : 1 + 2 / u ≤ (10 / 3) * u⁻¹ := by
    have : (1 : ℝ) ≤ (4 / 3) * u⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hu]; linarith
    have e : 2 / u = 2 * u⁻¹ := by rw [div_eq_mul_inv]
    rw [e]; linarith
  have h5 : u⁻¹ ≤ Real.exp 1 * QGridA_Z1 L u := by
    have := mul_le_mul_of_nonneg_left hz1 he0.le
    rw [← mul_assoc, mul_inv_cancel₀ he0.ne', one_mul] at this
    exact this
  have hz0 := QGridA_Z1_pos (L := L) u
  calc QGridA_Z1 L (u / 2) ≤ 2 * (1 - Real.exp (-(u / 2)))⁻¹ := h1
    _ ≤ 2 * ((10 / 3) * u⁻¹) := by gcongr; exact h2.trans (h3 ▸ h4)
    _ ≤ 2 * ((10 / 3) * (Real.exp 1 * QGridA_Z1 L u)) := by gcongr
    _ ≤ 20 * QGridA_Z1 L u := by nlinarith

/-! ## 4b. The scale `u_t = y_t⁻¹ + L⁻¹` and its first two derivatives -/

/-- `y_t = 1 + g (1 - t)^{-1/2}` (copy of `qaY`). -/
private def QGridA_Y (g t : ℝ) : ℝ := 1 + g / Real.sqrt (1 - t)

/-- `u_t = y_t⁻¹ + L⁻¹` (copy of `qaU`). -/
private def QGridA_U (L : ℕ) (g t : ℝ) : ℝ := (QGridA_Y g t)⁻¹ + (L : ℝ)⁻¹

private theorem QGridA_Y_gt {g t : ℝ} (hg : 0 < g) (ht : t < 1) : 1 < QGridA_Y g t := by
  have h : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  unfold QGridA_Y; have := div_pos hg h; linarith

private theorem QGridA_U_pos {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    0 < QGridA_U L g t := by
  have h1 : 0 < QGridA_Y g t := lt_trans zero_lt_one (QGridA_Y_gt hg ht)
  have h2 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold QGridA_U; positivity

private theorem QGridA_U_gt {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    (L : ℝ)⁻¹ < QGridA_U L g t := by
  have h1 : 0 < QGridA_Y g t := lt_trans zero_lt_one (QGridA_Y_gt hg ht)
  unfold QGridA_U; have := inv_pos.2 h1; linarith

private theorem QGridA_U_le {L : ℕ} (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    QGridA_U L g t ≤ 4 / 3 := by
  have h1 : (QGridA_Y g t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (QGridA_Y_gt hg ht).le
  have h3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 : (L : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h3
  unfold QGridA_U; linarith

private theorem QGridA_Yinv_le_U (L : ℕ) (g t : ℝ) : (QGridA_Y g t)⁻¹ ≤ QGridA_U L g t := by
  unfold QGridA_U; have := inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) L); linarith

/-- `q_t = g (1 - t)^{-1/2}` has derivative `q / (2 (1 - t))`. -/
private theorem QGridA_hasDerivAt_q {g t : ℝ} (ht : t < 1) :
    HasDerivAt (fun s : ℝ => g / Real.sqrt (1 - s)) (g / Real.sqrt (1 - t) / (2 * (1 - t))) t := by
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 - s)) (-1 / (2 * Real.sqrt (1 - t))) t :=
    h1.sqrt h1t.ne'
  have h3 := (hasDerivAt_const t g).fun_div h2 hr.ne'
  have hr2 : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  refine h3.congr_deriv ?_
  set r := Real.sqrt (1 - t) with hrdef
  rw [← hr2]
  field_simp
  ring

/-- `u_t' = -(q/(2(1-t)))/y²`. -/
private def QGridA_Up (g t : ℝ) : ℝ :=
  -(g / Real.sqrt (1 - t) / (2 * (1 - t))) / (1 + g / Real.sqrt (1 - t)) ^ 2

/-- `u_t'' = -q (3 + q) / (4 (1-t)² y³)`. -/
private def QGridA_Upp (g t : ℝ) : ℝ :=
  -(g / Real.sqrt (1 - t) * (3 + g / Real.sqrt (1 - t))) /
    (4 * (1 - t) ^ 2 * (1 + g / Real.sqrt (1 - t)) ^ 3)

private theorem QGridA_hasDerivAt_U (L : ℕ) {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    HasDerivAt (QGridA_U L g) (QGridA_Up g t) t := by
  have h1t : 0 < 1 - t := by linarith
  have hq := QGridA_hasDerivAt_q (g := g) ht
  have hy : HasDerivAt (fun s => 1 + g / Real.sqrt (1 - s)) (g / Real.sqrt (1 - t) / (2 * (1 - t))) t :=
    hq.const_add 1
  have hy0 : 1 + g / Real.sqrt (1 - t) ≠ 0 := by
    have : 0 < g / Real.sqrt (1 - t) := div_pos hg (Real.sqrt_pos.2 h1t)
    linarith
  have h := (hy.fun_inv hy0).add_const ((L : ℝ)⁻¹)
  refine h.congr_deriv ?_
  unfold QGridA_Up
  ring

private theorem QGridA_hasDerivAt_Up {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    HasDerivAt (fun s => QGridA_Up g s) (QGridA_Upp g t) t := by
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have hq := QGridA_hasDerivAt_q (g := g) ht
  have hy : HasDerivAt (fun s : ℝ => 1 + g / Real.sqrt (1 - s))
      (g / Real.sqrt (1 - t) / (2 * (1 - t))) t := hq.const_add 1
  have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun s : ℝ => 2 * (1 - s)) (2 * (-1)) t := h1.const_mul 2
  have hA := hq.fun_div h2 (by positivity)
  have hy0 : 1 + g / Real.sqrt (1 - t) ≠ 0 := by
    have : 0 < g / Real.sqrt (1 - t) := div_pos hg hr
    linarith
  have hY2 := hy.fun_pow 2
  have hN : HasDerivAt (fun s : ℝ => -(g / Real.sqrt (1 - s) / (2 * (1 - s))))
      (-((g / Real.sqrt (1 - t) / (2 * (1 - t)) * (2 * (1 - t)) - g / Real.sqrt (1 - t) * (2 * -1)) /
        (2 * (1 - t)) ^ 2)) t := hA.neg
  have hD := hN.fun_div hY2 (pow_ne_zero 2 hy0)
  refine hD.congr_deriv ?_
  unfold QGridA_Upp
  have hq0 : 0 < g / Real.sqrt (1 - t) := div_pos hg hr
  set q := g / Real.sqrt (1 - t) with hqdef
  set w := 1 - t with hw
  have hw0 : w ≠ 0 := h1t.ne'
  have hyq : 1 + q ≠ 0 := hy0
  norm_num
  field_simp
  ring

/-- `|u_t'| ≤ u_t / (2 (1 - t))`. -/
private theorem QGridA_Up_le {L : ℕ} {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    |QGridA_Up g t| ≤ QGridA_U L g t / (2 * (1 - t)) := by
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  set q := g / Real.sqrt (1 - t) with hq
  have hq0 : 0 < q := div_pos hg hr
  have hy0 : 0 < 1 + q := by linarith
  have hUle := QGridA_Yinv_le_U L g t
  have hYdef : QGridA_Y g t = 1 + q := rfl
  rw [hYdef] at hUle
  unfold QGridA_Up
  rw [← hq]
  have habs : |-(q / (2 * (1 - t))) / (1 + q) ^ 2| = q / (2 * (1 - t)) / (1 + q) ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs]
  calc q / (2 * (1 - t)) / (1 + q) ^ 2 = (q / (1 + q) ^ 2) / (2 * (1 - t)) := by ring
    _ ≤ (1 + q)⁻¹ / (2 * (1 - t)) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ (by positivity)]
        calc q ≤ 1 + q := by linarith
          _ = (1 + q)⁻¹ * (1 + q) ^ 2 := by field_simp
    _ ≤ QGridA_U L g t / (2 * (1 - t)) := div_le_div_of_nonneg_right hUle (by positivity)

/-- `|u_t''| ≤ (3/4) u_t / (1 - t)²`. -/
private theorem QGridA_Upp_le {L : ℕ} {g t : ℝ} (hg : 0 < g) (ht : t < 1) :
    |QGridA_Upp g t| ≤ (3 / 4) * QGridA_U L g t / (1 - t) ^ 2 := by
  have h1t : 0 < 1 - t := by linarith
  have hr : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  set q := g / Real.sqrt (1 - t) with hq
  have hq0 : 0 < q := div_pos hg hr
  have hy0 : 0 < 1 + q := by linarith
  have hUle := QGridA_Yinv_le_U L g t
  have hYdef : QGridA_Y g t = 1 + q := rfl
  rw [hYdef] at hUle
  unfold QGridA_Upp
  rw [← hq]
  have habs : |-(q * (3 + q)) / (4 * (1 - t) ^ 2 * (1 + q) ^ 3)|
      = q * (3 + q) / (4 * (1 - t) ^ 2 * (1 + q) ^ 3) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [habs]
  have key : q * (3 + q) / (4 * (1 - t) ^ 2 * (1 + q) ^ 3) ≤ (3 / 4) * (1 + q)⁻¹ / (1 - t) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : q * (3 + q) ≤ 3 * (1 + q) ^ 2 := by nlinarith [sq_nonneg q]
    have h2 : (3 / 4 : ℝ) * (1 + q)⁻¹ * (4 * (1 - t) ^ 2 * (1 + q) ^ 3)
        = 3 * (1 + q) ^ 2 * (1 - t) ^ 2 := by field_simp
    rw [h2]
    have : 0 ≤ (1 - t) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 this]
  refine key.trans ?_
  rw [mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact div_le_div_of_nonneg_right hUle (by positivity)
/-! ## 4c. `Φ(u) = exp(-u S) / z(u)^n` and its first two derivatives in `u` -/

private theorem QGridA_Z1_hasDerivAt (L : ℕ) [NeZero L] (u : ℝ) :
    HasDerivAt (QGridA_Z1 L) (-QGridA_Z2 L u) u := by
  have h : ∀ y ∈ (Finset.univ : Finset (ZMod L)),
      HasDerivAt (fun v : ℝ => Real.exp (-v * (zdist L y : ℝ)))
        (-((zdist L y : ℝ) * Real.exp (-u * (zdist L y : ℝ)))) u := by
    intro y _
    have h1 : HasDerivAt (fun v : ℝ => -v * (zdist L y : ℝ)) (-(zdist L y : ℝ)) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const (zdist L y : ℝ))
    have h2 := h1.exp
    convert h2 using 1; ring
  have h3 := HasDerivAt.fun_sum h
  unfold QGridA_Z1 QGridA_Z2
  rw [Finset.sum_neg_distrib] at h3
  exact h3

private theorem QGridA_Z2_hasDerivAt (L : ℕ) [NeZero L] (u : ℝ) :
    HasDerivAt (QGridA_Z2 L) (-QGridA_Z3 L u) u := by
  have h : ∀ y ∈ (Finset.univ : Finset (ZMod L)),
      HasDerivAt (fun v : ℝ => (zdist L y : ℝ) * Real.exp (-v * (zdist L y : ℝ)))
        (-((zdist L y : ℝ) ^ 2 * Real.exp (-u * (zdist L y : ℝ)))) u := by
    intro y _
    have h1 : HasDerivAt (fun v : ℝ => -v * (zdist L y : ℝ)) (-(zdist L y : ℝ)) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const (zdist L y : ℝ))
    have h2 := h1.exp.const_mul (zdist L y : ℝ)
    convert h2 using 1; ring
  have h3 := HasDerivAt.fun_sum h
  unfold QGridA_Z2 QGridA_Z3
  rw [Finset.sum_neg_distrib] at h3
  exact h3

/-- `Φ(u) = exp(-u S) / z(u)^n`. -/
private def QGridA_phi (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-u * S) / (QGridA_Z1 L u) ^ n

/-- `Φ'(u) = Φ(u) (-S + n z₂/z)`. -/
private def QGridA_dphi (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-u * S) / (QGridA_Z1 L u) ^ n * (-S + n * QGridA_Z2 L u / QGridA_Z1 L u)

/-- `Φ''(u) = Φ(u) ((-S + n z₂/z)² + n (z₂²/z² - z₃/z))`. -/
private def QGridA_ddphi (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-u * S) / (QGridA_Z1 L u) ^ n *
    ((-S + n * QGridA_Z2 L u / QGridA_Z1 L u) ^ 2 +
      n * ((QGridA_Z2 L u / QGridA_Z1 L u) ^ 2 - QGridA_Z3 L u / QGridA_Z1 L u))

private theorem QGridA_phi_hasDerivAt (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (QGridA_phi L S n) (QGridA_dphi L S n u) u := by
  have hz : 0 < QGridA_Z1 L u := QGridA_Z1_pos u
  have h1 : HasDerivAt (fun v : ℝ => Real.exp (-v * S)) (Real.exp (-u * S) * (-S)) u := by
    have h0 : HasDerivAt (fun v : ℝ => -v * S) (-S) u := by
      simpa using ((hasDerivAt_id u).neg.mul_const S)
    exact h0.exp
  have h2 : HasDerivAt (fun v : ℝ => (QGridA_Z1 L v) ^ n)
      ((n : ℝ) * (QGridA_Z1 L u) ^ (n - 1) * (-QGridA_Z2 L u)) u :=
    (QGridA_Z1_hasDerivAt L u).fun_pow n
  have h3 := h1.fun_div h2 (pow_pos hz n).ne'
  refine h3.congr_deriv ?_
  unfold QGridA_dphi
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

private theorem QGridA_dphi_hasDerivAt (L : ℕ) [NeZero L] (S : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (QGridA_dphi L S n) (QGridA_ddphi L S n u) u := by
  have hz : 0 < QGridA_Z1 L u := QGridA_Z1_pos u
  have hφ := QGridA_phi_hasDerivAt L S n u
  have hZ2 := QGridA_Z2_hasDerivAt L u
  have hZ1 := QGridA_Z1_hasDerivAt L u
  have hh : HasDerivAt (fun v : ℝ => -S + (n : ℝ) * QGridA_Z2 L v / QGridA_Z1 L v)
      (((n : ℝ) * (-QGridA_Z3 L u) * QGridA_Z1 L u - (n : ℝ) * QGridA_Z2 L u * (-QGridA_Z2 L u)) /
        QGridA_Z1 L u ^ 2) u := by
    have h1 := (hZ2.const_mul (n : ℝ)).fun_div hZ1 hz.ne'
    exact h1.const_add (-S)
  have hprod := hφ.mul hh
  refine hprod.congr_deriv ?_
  unfold QGridA_dphi QGridA_ddphi QGridA_phi
  field_simp
  ring

/-- `|Φ'(u)| u ≤ (1 + 40 n) / z^n` given `u z₂ ≤ 40 z` (copy of `qa_core`). -/
private theorem QGridA_core1 {u S z z₂ : ℝ} (n : ℕ) (hu : 0 < u) (hS : 0 ≤ S) (hz : 0 < z)
    (hz₂ : 0 ≤ z₂) (h : u * z₂ ≤ 40 * z) :
    |Real.exp (-u * S) / z ^ n * (-S + n * z₂ / z)| * u ≤ (1 + 40 * (n : ℝ)) / z ^ n := by
  have he0 : 0 < Real.exp (-u * S) := Real.exp_pos _
  have he : Real.exp (-u * S) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hx : u * S * Real.exp (-u * S) ≤ 1 := by
    have h1 : u * S ≤ Real.exp (u * S) := by linarith [Real.add_one_le_exp (u * S)]
    calc u * S * Real.exp (-u * S) ≤ Real.exp (u * S) * Real.exp (-u * S) :=
          mul_le_mul_of_nonneg_right h1 he0.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hzn : 0 < z ^ n := pow_pos hz n
  have hnz : 0 ≤ (n : ℝ) * z₂ / z := div_nonneg (mul_nonneg n.cast_nonneg hz₂) hz.le
  have habs : |-S + n * z₂ / z| ≤ S + n * z₂ / z := by
    rw [abs_le]; constructor <;> linarith
  have huz : u * z₂ / z ≤ 40 := by rw [div_le_iff₀ hz]; exact h
  rw [abs_mul, abs_of_pos (div_pos he0 hzn)]
  calc Real.exp (-u * S) / z ^ n * |-S + n * z₂ / z| * u
      ≤ Real.exp (-u * S) / z ^ n * (S + n * z₂ / z) * u := by gcongr
    _ = (u * S * Real.exp (-u * S) + (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S)) / z ^ n := by
        field_simp
    _ ≤ (1 + 40 * (n : ℝ)) / z ^ n := by
        refine div_le_div_of_nonneg_right ?_ hzn.le
        have h1 : (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S) ≤ (n : ℝ) * 40 := by
          calc (n : ℝ) * (u * z₂ / z) * Real.exp (-u * S) ≤ (n : ℝ) * (u * z₂ / z) * 1 :=
                mul_le_mul_of_nonneg_left he (mul_nonneg n.cast_nonneg (by positivity))
            _ ≤ (n : ℝ) * 40 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left huz n.cast_nonneg
        linarith

/-- `|Φ''(u)| u² ≤ (4 + 3200 n² + 1760 n) / z^n` given `u z₂ ≤ 40 z`, `u² z₃ ≤ 160 z`. -/
private theorem QGridA_core2 {u S z z₂ z₃ : ℝ} (n : ℕ) (hu : 0 < u) (hS : 0 ≤ S) (hz : 0 < z)
    (hz₂ : 0 ≤ z₂) (hz₃ : 0 ≤ z₃) (h2 : u * z₂ ≤ 40 * z) (h3 : u ^ 2 * z₃ ≤ 160 * z) :
    |Real.exp (-u * S) / z ^ n * ((-S + n * z₂ / z) ^ 2 + n * ((z₂ / z) ^ 2 - z₃ / z))| * u ^ 2 ≤
      (4 + 3200 * (n : ℝ) ^ 2 + 1760 * n) / z ^ n := by
  set E := Real.exp (-u * S) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hzn : 0 < z ^ n := pow_pos hz n
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  set m₁ := z₂ / z with hm1def
  set m₃ := z₃ / z with hm3def
  have hm1 : 0 ≤ m₁ := div_nonneg hz₂ hz.le
  have hm3 : 0 ≤ m₃ := div_nonneg hz₃ hz.le
  have hum1 : u * m₁ ≤ 40 := by
    rw [hm1def, ← mul_div_assoc, div_le_iff₀ hz]; exact h2
  have hum3 : u ^ 2 * m₃ ≤ 160 := by
    rw [hm3def, ← mul_div_assoc, div_le_iff₀ hz]; exact h3
  have hx2 : u ^ 2 * S ^ 2 * E ≤ 2 := by
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u * S by positivity)
    have hmul : Real.exp (u * S) * E = 1 := by
      rw [hEdef, ← Real.exp_add]; simp
    have h1 : (u * S) ^ 2 ≤ 2 * Real.exp (u * S) := by nlinarith [sq_nonneg (u * S)]
    calc u ^ 2 * S ^ 2 * E = (u * S) ^ 2 * E := by ring
      _ ≤ (2 * Real.exp (u * S)) * E := mul_le_mul_of_nonneg_right h1 hE0.le
      _ = 2 := by rw [mul_assoc, hmul]; ring
  have habsB : |(-S + n * m₁) ^ 2 + n * (m₁ ^ 2 - m₃)| ≤
      2 * S ^ 2 + 2 * (n : ℝ) ^ 2 * m₁ ^ 2 + n * m₁ ^ 2 + n * m₃ := by
    have h1 : (-S + n * m₁) ^ 2 ≤ 2 * S ^ 2 + 2 * (n : ℝ) ^ 2 * m₁ ^ 2 := by
      nlinarith [sq_nonneg (S + n * m₁)]
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (-S + n * m₁), mul_nonneg hn0 hm3, mul_nonneg hn0 (sq_nonneg m₁),
        sq_nonneg S, mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg m₁)]
    · nlinarith [mul_nonneg hn0 hm3, mul_nonneg hn0 (sq_nonneg m₁)]
  rw [show (n : ℝ) * z₂ / z = n * m₁ by rw [hm1def]; ring]
  rw [abs_mul, abs_of_pos (div_pos hE0 hzn)]
  have hfin : (2 * S ^ 2 + 2 * (n : ℝ) ^ 2 * m₁ ^ 2 + n * m₁ ^ 2 + n * m₃) * u ^ 2 * E ≤
      4 + 3200 * (n : ℝ) ^ 2 + 1760 * n := by
    have e1 : (2 * S ^ 2 + 2 * (n : ℝ) ^ 2 * m₁ ^ 2 + n * m₁ ^ 2 + n * m₃) * u ^ 2 * E
        = 2 * (u ^ 2 * S ^ 2 * E) + (2 * (n : ℝ) ^ 2 + n) * (u * m₁) ^ 2 * E + n * (u ^ 2 * m₃) * E := by
      ring
    rw [e1]
    have t2 : (2 * (n : ℝ) ^ 2 + n) * (u * m₁) ^ 2 * E ≤ (2 * (n : ℝ) ^ 2 + n) * 1600 := by
      have h40 : (u * m₁) ^ 2 ≤ 1600 := by nlinarith [mul_nonneg hu.le hm1]
      have hc : 0 ≤ 2 * (n : ℝ) ^ 2 + n := by positivity
      calc (2 * (n : ℝ) ^ 2 + n) * (u * m₁) ^ 2 * E ≤ (2 * (n : ℝ) ^ 2 + n) * (u * m₁) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ ≤ (2 * (n : ℝ) ^ 2 + n) * 1600 := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left h40 hc
    have t3 : (n : ℝ) * (u ^ 2 * m₃) * E ≤ n * 160 := by
      calc (n : ℝ) * (u ^ 2 * m₃) * E ≤ (n : ℝ) * (u ^ 2 * m₃) * 1 :=
            mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ ≤ n * 160 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hum3 hn0
    nlinarith
  calc E / z ^ n * |(-S + n * m₁) ^ 2 + n * (m₁ ^ 2 - m₃)| * u ^ 2
      ≤ E / z ^ n * (2 * S ^ 2 + 2 * (n : ℝ) ^ 2 * m₁ ^ 2 + n * m₁ ^ 2 + n * m₃) * u ^ 2 := by
        gcongr
    _ = ((2 * S ^ 2 + 2 * (n : ℝ) ^ 2 * m₁ ^ 2 + n * m₁ ^ 2 + n * m₃) * u ^ 2 * E) / z ^ n := by
        ring
    _ ≤ (4 + 3200 * (n : ℝ) ^ 2 + 1760 * n) / z ^ n :=
        div_le_div_of_nonneg_right hfin hzn.le
/-! ## 4d. The second-order Taylor bound of `t ↦ Φ(u_t)` -/

/-- A real second-order Taylor bound by two mean-value steps: if `ψ' = D` and `D' ` are
derivatives on `[u, v]` and `|D'| ≤ M` there, then `|ψ v - ψ u - (v - u) D u| ≤ M (v - u)²`. -/
private theorem QGridA_taylor_real {ψ D D' : ℝ → ℝ} {u v M : ℝ} (huv : u ≤ v)
    (hψ : ∀ τ ∈ Set.Icc u v, HasDerivAt ψ (D τ) τ)
    (hD : ∀ τ ∈ Set.Icc u v, HasDerivAt D (D' τ) τ)
    (hM : ∀ τ ∈ Set.Icc u v, |D' τ| ≤ M) :
    |ψ v - ψ u - (v - u) * D u| ≤ M * (v - u) ^ 2 := by
  have h1 : ∀ τ ∈ Set.Icc u v, |D τ - D u| ≤ M * (τ - u) := by
    intro τ hτ
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := D) (f' := D') (a := u) (b := τ) (C := M)
      (fun x hx => (hD x ⟨hx.1, hx.2.trans hτ.2⟩).hasDerivWithinAt)
      (fun x hx => by simpa using hM x ⟨hx.1, hx.2.le.trans hτ.2⟩) τ ⟨hτ.1, le_rfl⟩
    simpa using this
  have hG : ∀ τ ∈ Set.Icc u v,
      HasDerivWithinAt (fun τ => ψ τ - (τ - u) * D u) (D τ - D u) (Set.Icc u v) τ := by
    intro τ hτ
    have h2 : HasDerivAt (fun τ => ψ τ - (τ - u) * D u) (D τ - 1 * D u) τ :=
      (hψ τ hτ).sub (((hasDerivAt_id τ).sub_const u).mul_const (D u))
    simpa using h2.hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico u v, ‖D x - D u‖ ≤ M * (v - u) := by
    intro x hx
    have hx' : x ∈ Set.Icc u v := ⟨hx.1, hx.2.le⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx')
    rw [Real.norm_eq_abs]
    calc |D x - D u| ≤ M * (x - u) := h1 x hx'
      _ ≤ M * (v - u) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hM0
  have := norm_image_sub_le_of_norm_deriv_le_segment' hG hb v ⟨huv, le_rfl⟩
  rw [Real.norm_eq_abs] at this
  have e : ψ v - (v - u) * D u - (ψ u - (u - u) * D u) = ψ v - ψ u - (v - u) * D u := by ring
  rw [e] at this
  calc _ ≤ M * (v - u) * (v - u) := this
    _ = M * (v - u) ^ 2 := by ring

/-- `ψ(t) = Φ(u_t)`'s first derivative `D(t) = Φ'(u_t) u_t'`. -/
private def QGridA_D (L : ℕ) [NeZero L] (g S : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  QGridA_dphi L S n (QGridA_U L g t) * QGridA_Up g t

/-- Its derivative `D'(t) = Φ''(u_t) u_t'² + Φ'(u_t) u_t''`. -/
private def QGridA_D' (L : ℕ) [NeZero L] (g S : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  QGridA_ddphi L S n (QGridA_U L g t) * QGridA_Up g t * QGridA_Up g t +
    QGridA_dphi L S n (QGridA_U L g t) * QGridA_Upp g t

private theorem QGridA_hasDerivAt_psi {L : ℕ} [NeZero L] {g : ℝ} (hg : 0 < g) {t : ℝ} (ht : t < 1)
    (S : ℝ) (n : ℕ) :
    HasDerivAt (fun τ => QGridA_phi L S n (QGridA_U L g τ)) (QGridA_D L g S n t) t :=
  (QGridA_phi_hasDerivAt L S n (QGridA_U L g t)).comp t (QGridA_hasDerivAt_U L hg ht)

private theorem QGridA_hasDerivAt_D {L : ℕ} [NeZero L] {g : ℝ} (hg : 0 < g) {t : ℝ} (ht : t < 1)
    (S : ℝ) (n : ℕ) :
    HasDerivAt (fun τ => QGridA_D L g S n τ) (QGridA_D' L g S n t) t :=
  ((QGridA_dphi_hasDerivAt L S n (QGridA_U L g t)).comp t (QGridA_hasDerivAt_U L hg ht)).mul
    (QGridA_hasDerivAt_Up hg ht)

/-- The moment bounds `u z₂ ≤ 40 z`, `u² z₃ ≤ 160 z` for `L⁻¹ < u ≤ 4/3`. -/
private theorem QGridA_moments {L : ℕ} [NeZero L] {u : ℝ} (hu : 0 < u) (huL : (L : ℝ)⁻¹ < u)
    (hu4 : u ≤ 4 / 3) :
    u * QGridA_Z2 L u ≤ 40 * QGridA_Z1 L u ∧ u ^ 2 * QGridA_Z3 L u ≤ 160 * QGridA_Z1 L u := by
  have h := QGridA_Z1_half_le hu huL hu4
  exact ⟨by linarith [QGridA_Z2_le_half (L := L) hu], by linarith [QGridA_Z3_le_half (L := L) hu]⟩

/-- **The bound of `D'`**: `|D'(t)| ≤ 1000 (1 + n)² (1 - t)⁻²` for `t < 1`. -/
private theorem QGridA_D'_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g t : ℝ} (hg : 0 < g) (ht : t < 1)
    {S : ℝ} (hS : 0 ≤ S) (n : ℕ) :
    |QGridA_D' L g S n t| ≤ 1000 * (1 + (n : ℝ)) ^ 2 / (1 - t) ^ 2 := by
  have h1t : 0 < 1 - t := by linarith
  set u := QGridA_U L g t with hudef
  have hu : 0 < u := QGridA_U_pos hg ht
  have huL : (L : ℝ)⁻¹ < u := QGridA_U_gt hg ht
  have hu4 : u ≤ 4 / 3 := QGridA_U_le hL hg ht
  obtain ⟨hm2, hm3⟩ := QGridA_moments (L := L) hu huL hu4
  have hz := QGridA_Z1_pos (L := L) u
  have hz1 : (1 : ℝ) ≤ (QGridA_Z1 L u) ^ n := one_le_pow₀ (QGridA_Z1_ge_one u)
  have hc1 := QGridA_core1 (z := QGridA_Z1 L u) n hu hS hz (QGridA_Z2_nonneg u) hm2
  have hc2 := QGridA_core2 (z := QGridA_Z1 L u) n hu hS hz (QGridA_Z2_nonneg u) (QGridA_Z3_nonneg u) hm2 hm3
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hd1 : |QGridA_dphi L S n u| * u ≤ 1 + 40 * (n : ℝ) := by
    refine hc1.trans ?_
    exact div_le_self (by positivity) hz1
  have hd2 : |QGridA_ddphi L S n u| * u ^ 2 ≤ 4 + 3200 * (n : ℝ) ^ 2 + 1760 * n := by
    refine hc2.trans ?_
    exact div_le_self (by positivity) hz1
  have hUp := QGridA_Up_le (L := L) hg ht
  have hUpp := QGridA_Upp_le (L := L) hg ht
  rw [← hudef] at hUp hUpp
  have hUp0 := abs_nonneg (QGridA_Up g t)
  have hUp2 : |QGridA_Up g t| * |QGridA_Up g t| ≤ u ^ 2 / (4 * (1 - t) ^ 2) := by
    calc |QGridA_Up g t| * |QGridA_Up g t| ≤ (u / (2 * (1 - t))) * (u / (2 * (1 - t))) :=
          mul_le_mul hUp hUp hUp0 (by positivity)
      _ = u ^ 2 / (4 * (1 - t) ^ 2) := by field_simp; ring
  unfold QGridA_D'
  have hdd0 := abs_nonneg (QGridA_ddphi L S n u)
  have hd0 := abs_nonneg (QGridA_dphi L S n u)
  calc |QGridA_ddphi L S n u * QGridA_Up g t * QGridA_Up g t + QGridA_dphi L S n u * QGridA_Upp g t|
      ≤ |QGridA_ddphi L S n u| * (|QGridA_Up g t| * |QGridA_Up g t|) +
          |QGridA_dphi L S n u| * |QGridA_Upp g t| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, mul_assoc]
    _ ≤ |QGridA_ddphi L S n u| * (u ^ 2 / (4 * (1 - t) ^ 2)) +
          |QGridA_dphi L S n u| * ((3 / 4) * u / (1 - t) ^ 2) := by
        gcongr
    _ = ((|QGridA_ddphi L S n u| * u ^ 2) / 4 + (3 / 4) * (|QGridA_dphi L S n u| * u)) / (1 - t) ^ 2 := by
        field_simp
    _ ≤ (((4 + 3200 * (n : ℝ) ^ 2 + 1760 * n) / 4 + (3 / 4) * (1 + 40 * (n : ℝ)))) / (1 - t) ^ 2 := by
        gcongr
    _ ≤ 1000 * (1 + (n : ℝ)) ^ 2 / (1 - t) ^ 2 := by
        gcongr
        nlinarith [sq_nonneg (n : ℝ)]

/-- **The second-order Taylor bound of `t ↦ Φ(u_t)`**: for `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1`,
`|ψ(u+Δ) - ψ(u) - Δ ψ'(u)| ≤ 1000 (1+n)² (1-(u+Δ))⁻² Δ²`. -/
private theorem QGridA_psi_taylor {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) {S : ℝ}
    (hS : 0 ≤ S) (n : ℕ) {u Δ : ℝ} (hu : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) :
    |QGridA_phi L S n (QGridA_U L g (u + Δ)) - QGridA_phi L S n (QGridA_U L g u) -
        Δ * QGridA_D L g S n u| ≤ 1000 * (1 + (n : ℝ)) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2 := by
  have hvu : u ≤ u + Δ := by linarith
  have key := QGridA_taylor_real (ψ := fun τ => QGridA_phi L S n (QGridA_U L g τ))
    (D := fun τ => QGridA_D L g S n τ) (D' := fun τ => QGridA_D' L g S n τ)
    (M := 1000 * (1 + (n : ℝ)) ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2) hvu
    (fun τ hτ => QGridA_hasDerivAt_psi hg (lt_of_le_of_lt hτ.2 hv) S n)
    (fun τ hτ => QGridA_hasDerivAt_D hg (lt_of_le_of_lt hτ.2 hv) S n)
    (fun τ hτ => by
      have hτ1 : τ < 1 := lt_of_le_of_lt hτ.2 hv
      refine (QGridA_D'_le hL hg hτ1 hS n).trans ?_
      have hpos : 0 < 1 - (u + Δ) := by linarith
      have h1 : (1 - (u + Δ)) ≤ 1 - τ := by linarith [hτ.2]
      have : ((1 - (u + Δ))⁻¹) ^ 2 = 1 / (1 - (u + Δ)) ^ 2 := by rw [inv_pow, one_div]
      rw [this, ← mul_div_assoc, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hpos.le h1 2))
  have e : u + Δ - u = Δ := by ring
  simp only [e] at key
  exact key


/-- `S(a) = Σ_{i ≥ 2} |a_i - a₁|` (copy of the private `qaS`). -/
private def QGridA_S {d L m : ℕ} [NeZero L] (a : Fin (m + 1) → Zd d L) : ℝ :=
  ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)

private theorem QGridA_S_nonneg {d L m : ℕ} [NeZero L] (a : Fin (m + 1) → Zd d L) : 0 ≤ QGridA_S a :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The merged mollifier is `Φ_a(u_t)` (`QopAlgebra_mollifier` unfolds to the private `qaPhi ∘ qaU`). -/
private theorem QGridA_mollifier_eq (d L m : ℕ) [NeZero L] (g t : ℝ) (a : Fin (m + 1) → Zd d L) :
    QopAlgebra_mollifier d L m g t a =
      ((QGridA_phi L (QGridA_S a) (d * m) (QGridA_U L g t) : ℝ) : ℂ) := rfl

/-- **The second-order Taylor hypothesis** on a mollifier family `ϑ` (T2132; paper-delta candidate
`T2132b`): for `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1`, every label `a`,
`‖ϑ_{u+Δ,a} - ϑ_{u,a} - Δ ∂_uϑ_{u,a}‖ ≤ C₂ (1-(u+Δ))⁻² Δ²`.  It is not a clause of
`STMollifierProps` (which has the sup bound, differentiability and `|∂_tϑ| ≤ C (1-t)⁻¹ (ℓ^d)^{-m}`);
`QGridA_mollifier_taylor2` proves it for the merged mollifier `QopAlgebra_mollifier`. -/
def QGridA_Taylor2 {d m L : ℕ} [NeZero L] (C₂ : ℝ)
    (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) : Prop :=
  ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ a : Fin (m + 1) → Zd d L,
    ‖ϑ (u + Δ) a - ϑ u a - (Δ : ℂ) * deriv (fun τ => ϑ τ a) u‖ ≤
      C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2

/-- **The Taylor hypothesis holds for the merged mollifier** with `C₂ = 1000 (1 + d m)²`, for every
`g > 0` and `L ≥ 3` (the second `t`-derivative of `exp(-u_t S) / z(u_t)^{dm}`:
`Φ'' u² ≤ (4 + 3200 n² + 1760 n) z^{-n}`, `|u'| ≤ u/(2(1-t))`, `|u''| ≤ (3/4) u/(1-t)²`, `z ≥ 1`). -/
theorem QGridA_mollifier_taylor2 (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) :
    QGridA_Taylor2 (d := d) (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) (QopAlgebra_mollifier d L m g) := by
  intro u Δ hu hΔ hv a
  have hu1 : u < 1 := by linarith
  have hd := QGridA_hasDerivAt_psi (L := L) hg hu1 (QGridA_S a) (d * m)
  have hdc : HasDerivAt (fun τ => QopAlgebra_mollifier d L m g τ a)
      ((QGridA_D L g (QGridA_S a) (d * m) u : ℝ) : ℂ) u := hd.ofReal_comp
  rw [hdc.deriv]
  have hT := QGridA_psi_taylor hL hg (QGridA_S_nonneg a) (d * m) hu hΔ hv
  have e : QopAlgebra_mollifier d L m g (u + Δ) a - QopAlgebra_mollifier d L m g u a -
      (Δ : ℂ) * ((QGridA_D L g (QGridA_S a) (d * m) u : ℝ) : ℂ) =
      ((QGridA_phi L (QGridA_S a) (d * m) (QGridA_U L g (u + Δ)) -
        QGridA_phi L (QGridA_S a) (d * m) (QGridA_U L g u) -
        Δ * QGridA_D L g (QGridA_S a) (d * m) u : ℝ) : ℂ) := by
    rw [QGridA_mollifier_eq, QGridA_mollifier_eq]
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact hT

end Mollifier

/-! ## 5. The definitions (target 1) -/

section Defs

variable {d : ℕ} (sz : Sizes d)

/-- **`A^Q_j = 𝒬_{u_j} A_j`** (RBM2D `aTrueQN`, `AltGridQ:923`), with `A_j = (𝓛-𝒦)_{u_j,σ}(H_j)` the
merged `AvecN` and `(𝒬_t 𝒜)_a = 𝒜_a - (𝒫𝒜)_{a₁} ϑ_{t,a}` the merged `STQop` for the mollifier family `ϑ`
(tensors of `m + 1` indices; `ϑ` an explicit parameter). -/
def aTrueQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  STQop (d := d) ϑ (gridTime s t K n j) (AvecN sz E s t K n j σ ω)

/-- **The drift of `int_K-L+Q`** (`3_5:1337-1346`) at the grid time `u = u_j`:
`𝒬_u` of the merged `GridDriftN` drift `Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{G̃}`, plus
`ℬ₄ = [𝒬_u, Θ^{(m+1)}_{u,σ}](𝓛-𝒦)_{u,σ}` and `ℬ₅ = -[𝒫∘(𝓛-𝒦)_{u,σ}] ∂_uϑ` with the paper's sign
(`3_5:1345`): the minus sign is inside `ℬ₅`, so the drift is `𝒬_u D + ℬ₄ + ℬ₅` and the last Lean term
is `- STPsum X (a 0) * deriv (fun τ => ϑ τ a) u` (the `-(𝒫𝒜)_{a₁} ∂_tϑ` of
`QopAlgebra_Qop_hasDerivAt`). -/
def dGridQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ (gridTime s t K n j)
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ b) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b)) a +
      (STQop (d := d) ϑ (gridTime s t K n j)
          (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) (gridTime s t K n j)
            (AvecN sz E s t K n j σ ω)) a -
        ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) (gridTime s t K n j)
          (STQop (d := d) ϑ (gridTime s t K n j) (AvecN sz E s t K n j σ ω)) a) -
      STPsum (d := d) (AvecN sz E s t K n j σ ω) (a 0) * deriv (fun τ => ϑ τ a) (gridTime s t K n j)

/-- **The frozen `𝒬`-process**: the process stopped at `τ` and then propagated by the kernel,
`A^{Q,frz}_j = 𝒰_{u_{j∧τ},u_j,σ} A^Q_{j∧τ}` (RBM2D `aFrozQN`). -/
def aFrozQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j)
    (aTrueQN sz E s t K n ϑ σ (min j (τ ω)) ω)

/-- The martingale increment `ξ^Q_{j+1} = A^Q_{j+1} - 𝔼[A^Q_{j+1} | F_j]` (RBM2D `martIncQN`). -/
def martIncQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => aTrueQN sz E s t K n ϑ σ (j + 1) ω a -
    (pathP sz)[fun ω' => aTrueQN sz E s t K n ϑ σ (j + 1) ω' a | filt sz j] ω

/-- The exact one-step remainder of the `𝒬`-process, named by subtraction (RBM2D `rGridQN`):
`R^Q_j = 𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A^Q_j - Δ dGridQN_j`. -/
def rGridQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => (pathP sz)[fun ω' => aTrueQN sz E s t K n ϑ σ (j + 1) ω' a | filt sz j] ω -
    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (aTrueQN sz E s t K n ϑ σ j ω) a -
    (gridStep s t K n : ℂ) * dGridQN sz E s t K n ϑ σ j ω a

end Defs

/-- The deterministic sup bound on `A_j = (𝓛-𝒦)_{u,σ}` at loop length `k` (`|𝓛| ≤ η^{-k} (W^{-d})^{k-1}`
plus the `𝒦` envelope `Bk`): the bracket of the merged `stepErrN` (RBM2D `lkEnvN`). -/
def lkEnvN (d W : ℕ) (E : ℝ) (k : ℕ) (u Bk : ℝ) : ℝ :=
  (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk

/-- The explicit crude envelope of the drift `Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{LK×LK} + 𝓔^{G̃}` at loop length
`k` (RBM2D `driftEnvN` with `W² L² → W^d L^d`): with `B_F = η^{-k} + Bk` a bound of `|𝓛-𝒦|` on the
loops of length `2..k` (`Bk` the `𝒦` envelope),
`W^d L^d (k · 2k² B_F Bk + k² B_F² + k (η⁻¹ + 1) η^{-(k+1)})` (`norm_primBil_le`). -/
def driftEnvN (d L W : ℕ) (E : ℝ) (k : ℕ) (u Bk : ℝ) : ℝ :=
  (W : ℝ) ^ d * (L : ℝ) ^ d *
    ((k : ℝ) * (2 * (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * Bk)) +
      (k : ℝ) ^ 2 * (((etaT E u)⁻¹ ^ k + Bk) * ((etaT E u)⁻¹ ^ k + Bk)) +
      (k : ℝ) * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))

/-- **The explicit one-step remainder of the `𝒬` identity** (RBM2D `qStepErrN`, `AltGridQ:986`), for
tensors of `m + 1` indices, `Lp = (L^d)^m` the number of terms of `𝒫`, `β = (1-(u+Δ))⁻¹`,
`C`, `C₂` the sup/Lipschitz and second-order Taylor constants of the mollifier (`‖ϑ‖ ≤ C`,
`‖ϑ_v-ϑ_u‖ ≤ CβΔ`, `‖ϑ_v-ϑ_u-Δϑ̇_u‖ ≤ C₂β²Δ²`):
`(1 + C Lp) S + Δ Lp Dm (CβΔ) + 2 C Lp Ust Mk + Lp Mk (C₂β²Δ²) + Δ Lp ((m+1) β Mk) (CβΔ)`,
`S` the merged `stepErrN` bound, `Mk`, `Dm` the sup bounds of `A_j` and of the drift,
`Ust = uStepC (m+1) Δ (u+Δ)`. -/
def qStepErrN (d L m : ℕ) (C C₂ u Δ Mk Dm S : ℝ) : ℝ :=
  (1 + C * ((L : ℝ) ^ d) ^ m) * S +
    (Δ * (((L : ℝ) ^ d) ^ m * Dm) * (C * (1 - (u + Δ))⁻¹ * Δ) +
      2 * (C * (((L : ℝ) ^ d) ^ m * (uStepC (m + 1) Δ (u + Δ) * Mk))) +
      ((L : ℝ) ^ d) ^ m * Mk * (C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) +
      Δ * (((L : ℝ) ^ d) ^ m * (((m : ℝ) + 1) * (1 - (u + Δ))⁻¹ * Mk)) *
        (C * (1 - (u + Δ))⁻¹ * Δ))

/-- **The explicit one-step remainder of the grid step `j` of `int_K-L+Q`** (RBM2D `qErrQN`), in terms
of the merged `stepErrN`, `Bk` the `𝒦` envelope on `[0, u_{j+1}]`. -/
def qErrQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (C C₂ Bk : ℝ) (j : ℕ) : ℝ :=
  qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
    (lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk)
    (driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk)
    (stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1))
      (gridStep s t K n) Bk)

/-! ## 6. The deterministic `𝒬` algebra of one step -/

section QAlgebra

variable {d L m : ℕ} [NeZero L]

private theorem QGridA_Psum_add (A B : (Fin (m + 1) → Zd d L) → ℂ) (x : Zd d L) :
    STPsum (d := d) (fun b => A b + B b) x = STPsum (d := d) A x + STPsum (d := d) B x := by
  simp only [STPsum, Finset.sum_add_distrib]

private theorem QGridA_Psum_mul (c : ℂ) (A : (Fin (m + 1) → Zd d L) → ℂ) (x : Zd d L) :
    STPsum (d := d) (fun b => c * A b) x = c * STPsum (d := d) A x := by
  simp only [STPsum, Finset.mul_sum]

/-- The number of `a ∈ (ℤ_L^d)^{m+1}` with `a₀ = x` is `(L^d)^m` (RBM2D `SumZeroQ_card_filter`). -/
private theorem QGridA_card_filter (x : Zd d L) :
    (((Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = x)).card : ℕ) : ℝ) =
      ((L : ℝ) ^ d) ^ m := by
  have h : (Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = x)).card =
      Fintype.card (Fin m → Zd d L) := by
    rw [← Finset.card_univ (α := Fin m → Zd d L)]
    refine Finset.card_bij' (fun a _ => Fin.tail a) (fun y _ => Fin.cons x y) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro y _; simp
    · intro a ha
      have ha0 : a 0 = x := (Finset.mem_filter.1 ha).2
      rw [← ha0]; exact Fin.cons_self_tail a
    · intro y _; simp
  rw [h, Fintype.card_fun, Fintype.card_fin, card_Zd]
  push_cast
  rfl

/-- Crude counting bound `‖𝒫𝒜‖ ≤ (L^d)^m max‖𝒜‖` (RBM2D `AltGridQ_norm_Psum_le`). -/
private theorem QGridA_norm_Psum_le {A : (Fin (m + 1) → Zd d L) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (x : Zd d L) :
    ‖STPsum (d := d) A x‖ ≤ ((L : ℝ) ^ d) ^ m * M := by
  unfold STPsum
  refine (norm_sum_le _ _).trans ?_
  have h := Finset.sum_le_card_nsmul (Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = x))
    (fun a => ‖A a‖) M (fun a _ => hA a)
  rw [nsmul_eq_mul, QGridA_card_filter x] at h
  exact h

private theorem QGridA_Ugen_sub {g : ℝ} (E : ℝ) (σ : Fin (m + 1) → Bool) (v w : ℝ)
    (A B : (Fin (m + 1) → Zd d L) → ℂ) (a : Fin (m + 1) → Zd d L) :
    Ugen d L g E σ v w (fun b => A b - B b) a =
      Ugen d L g E σ v w A a - Ugen d L g E σ v w B a :=
  QopAlgebra_UN_sub g (fun i => mSigma E (σ i)) v w A B a

/-- `‖Θ_{u,σ} 𝒜‖_max ≤ k (1-u)⁻¹ ‖𝒜‖_max` (row sums of the generator `ξ S Θ_{uξ}`; RBM2D
`AltGridQ_norm_thetaSig_le`). -/
private theorem QGridA_norm_ThetaN_le {g : ℝ} (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {A : (Fin k → Zd d L) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (a : Fin k → Zd d L) :
    ‖ThetaN d L g (fun i => mSigma E (σ i)) u A a‖ ≤ (k : ℝ) * (1 - u)⁻¹ * M := by
  unfold ThetaN
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin k, ‖∑ b : Zd d L, thetaKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (a i) b *
          A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, (1 - u)⁻¹ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hξ : ‖cycProd (fun i => mSigma E (σ i)) i‖ = 1 :=
          norm_cycProd (fun i => norm_mSigma hE (σ i)) i
        have hsξ : ‖(u : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 := by
          rw [QGridA_norm_real_mul hξ hu0]; exact hu1
        exact QGridA_row_mul
          (P := thetaKer d L g (cycProd (fun i => mSigma E (σ i)) i) u)
          (fun x => by
            rw [QGridA_thetaKer_eq]
            have := QGridA_row_thetaGenMat (g := g) hL hsξ x
            rwa [hξ, QGridA_norm_real_mul hξ hu0, one_mul] at this) (a i) (fun c => hA _)
    _ = (k : ℝ) * (1 - u)⁻¹ * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private theorem QGridA_norm_six_le (T1 T2 T3 T4 T5 T6 : ℂ) :
    ‖T1 + T2 + T3 + T4 + T5 - T6‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by
  calc _ ≤ ‖T1 + T2 + T3 + T4 + T5‖ + ‖T6‖ := norm_sub_le _ _
    _ ≤ ‖T1 + T2 + T3 + T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖T1 + T2 + T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖T1 + T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by gcongr; exact norm_add_le _ _

/-- **The deterministic core of the one-step `𝒬`-identity** (RBM2D `AltGridQ_qstep_algebra`,
`AltGridQ:1072`; RBM1D `Qstep_algebra`): if `c = 𝒰_{u,u+Δ} X + Δ D + e` with `‖e‖ ≤ S` (the conclusion
of the merged `gridDriftN`) and the mollifier satisfies `‖ϑ‖ ≤ C` at `u`, `u+Δ`, the Lipschitz bound
and the second-order Taylor bound between `u` and `u+Δ`, then
`𝒬_{u+Δ} c - 𝒰_{u,u+Δ}(𝒬_u X) = Δ (𝒬_u D + [𝒬_u, Θ_{u,σ}] X - 𝒫X ∂_uϑ_u) + R`, `‖R‖ ≤ qStepErrN`.
Exact identity:
`R = (e - 𝒫e ϑ_v) + Δ 𝒫D (ϑ_u-ϑ_v) + 𝒫X (ϑ_u-ϑ_v+Δϑ̇_u) + Δ 𝒫(ΘX)(ϑ_u-ϑ_v) + R_U(𝒫Xϑ_u) - 𝒫(R_U X) ϑ_v`,
`R_U = 𝒰 - 1 - Δ Θ`. -/
private theorem QGridA_qstep_algebra {g : ℝ} (hL : 3 ≤ L) (hm : 1 ≤ m) {E : ℝ} (hE : |E| ≤ 2)
    (σ : Fin (m + 1) → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ) (hut1 : u + Δ < 1)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} {C C₂ : ℝ}
    (hϑu : ∀ a, ‖ϑ u a‖ ≤ C) (hϑv : ∀ a, ‖ϑ (u + Δ) a‖ ≤ C)
    (hlip : ∀ a, ‖ϑ (u + Δ) a - ϑ u a‖ ≤ C * (1 - (u + Δ))⁻¹ * Δ)
    (htay : ∀ a, ‖ϑ (u + Δ) a - ϑ u a - (Δ : ℂ) * deriv (fun τ => ϑ τ a) u‖ ≤
      C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2)
    {X D c : (Fin (m + 1) → Zd d L) → ℂ} {Mk Dm S : ℝ} (hX : ∀ b, ‖X b‖ ≤ Mk)
    (hD : ∀ b, ‖D b‖ ≤ Dm)
    (hc : ∀ b, ‖c b - Ugen d L g E σ u (u + Δ) X b - (Δ : ℂ) * D b‖ ≤ S)
    (a : Fin (m + 1) → Zd d L) :
    ‖STQop (d := d) ϑ (u + Δ) c a - Ugen d L g E σ u (u + Δ) (STQop (d := d) ϑ u X) a -
        (Δ : ℂ) * (STQop (d := d) ϑ u D a +
          (STQop (d := d) ϑ u (ThetaN d L g (fun i => mSigma E (σ i)) u X) a -
            ThetaN d L g (fun i => mSigma E (σ i)) u (STQop (d := d) ϑ u X) a) -
          STPsum (d := d) X (a 0) * deriv (fun τ => ϑ τ a) u)‖ ≤
      qStepErrN d L m C C₂ u Δ Mk Dm S := by
  have hu1 : u < 1 := by linarith
  have hv0 : 0 ≤ u + Δ := by linarith
  have hMk0 : 0 ≤ Mk := (norm_nonneg _).trans (hX a)
  have hDm0 : 0 ≤ Dm := (norm_nonneg _).trans (hD a)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hc a)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hϑu a)
  set Lp : ℝ := ((L : ℝ) ^ d) ^ m with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  set Ust : ℝ := uStepC (m + 1) Δ (u + Δ) with hUst
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβ
  have hβ0 : 0 ≤ β := inv_nonneg.mpr (by linarith)
  have hβu : (1 - u)⁻¹ ≤ β := inv_anti₀ (by linarith) (by linarith)
  have hβu0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr (by linarith)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  -- the objects
  set Y : (Fin (m + 1) → Zd d L) → ℂ := fun b => STPsum (d := d) X (b 0) * ϑ u b with hY
  set e : (Fin (m + 1) → Zd d L) → ℂ :=
    fun b => c b - Ugen d L g E σ u (u + Δ) X b - (Δ : ℂ) * D b with he
  set εX : (Fin (m + 1) → Zd d L) → ℂ := fun b =>
    Ugen d L g E σ u (u + Δ) X b - X b -
      (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u X b with hεX
  set εY : (Fin (m + 1) → Zd d L) → ℂ := fun b =>
    Ugen d L g E σ u (u + Δ) Y b - Y b -
      (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u Y b with hεY
  have hUst0 : 0 ≤ Ust := by
    unfold Ust uStepC
    have hx0 : 0 ≤ Δ * (1 - (u + Δ))⁻¹ := mul_nonneg hΔ0 hβ0
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - (u + Δ))⁻¹ by linarith) (m + 1)
    have e1 : 0 ≤ ((m + 1 : ℕ) : ℝ) * Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by positivity
    nlinarith [hb]
  have hεXb : ∀ b, ‖εX b‖ ≤ Ust * Mk := fun b =>
    QGridA_Ugen_step_le (g := g) hL hE σ hu0 hΔ0 hut1 X Mk hX b
  have hYb : ∀ b, ‖Y b‖ ≤ Lp * Mk * C := fun b => by
    simp only [hY]
    rw [norm_mul]
    exact mul_le_mul (QGridA_norm_Psum_le hX _) (hϑu b) (norm_nonneg _) (by positivity)
  have hεYb : ∀ b, ‖εY b‖ ≤ Ust * (Lp * Mk * C) := fun b =>
    QGridA_Ugen_step_le (g := g) hL hE σ hu0 hΔ0 hut1 Y (Lp * Mk * C) hYb b
  have heb : ∀ b, ‖e b‖ ≤ S := hc
  -- the `STPsum` identities
  have h4 : STPsum (d := d) (Ugen d L g E σ u (u + Δ) X) (a 0) = STPsum (d := d) X (a 0) +
      (Δ : ℂ) * STPsum (d := d) (ThetaN d L g (fun i => mSigma E (σ i)) u X) (a 0) +
        STPsum (d := d) εX (a 0) := by
    have h1 : (fun b => Ugen d L g E σ u (u + Δ) X b) =
        fun b => (X b + (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u X b) + εX b := by
      funext b; simp only [hεX]; ring
    calc STPsum (d := d) (Ugen d L g E σ u (u + Δ) X) (a 0)
        = STPsum (d := d) (fun b => (X b + (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u X b) + εX b) (a 0) := by
          rw [← h1]
      _ = _ := by
          rw [QGridA_Psum_add, QGridA_Psum_add, QGridA_Psum_mul]
  have h3 : STPsum (d := d) c (a 0) = STPsum (d := d) e (a 0) +
      STPsum (d := d) (Ugen d L g E σ u (u + Δ) X) (a 0) + (Δ : ℂ) * STPsum (d := d) D (a 0) := by
    have h1 : (fun b => c b) = fun b => (e b + Ugen d L g E σ u (u + Δ) X b) + (Δ : ℂ) * D b := by
      funext b; simp only [he]; ring
    calc STPsum (d := d) c (a 0)
        = STPsum (d := d) (fun b => (e b + Ugen d L g E σ u (u + Δ) X b) + (Δ : ℂ) * D b) (a 0) := by
          rw [← h1]
      _ = _ := by
          rw [QGridA_Psum_add, QGridA_Psum_add, QGridA_Psum_mul]
  have hQX : STQop (d := d) ϑ u X = fun b => X b - Y b := rfl
  have h5 : Ugen d L g E σ u (u + Δ) (STQop (d := d) ϑ u X) a =
      Ugen d L g E σ u (u + Δ) X a - Ugen d L g E σ u (u + Δ) Y a := by
    rw [hQX]; exact QGridA_Ugen_sub E σ u (u + Δ) X Y a
  have h6 : ThetaN d L g (fun i => mSigma E (σ i)) u (STQop (d := d) ϑ u X) a =
      ThetaN d L g (fun i => mSigma E (σ i)) u X a -
        ThetaN d L g (fun i => mSigma E (σ i)) u Y a := by
    rw [hQX]; exact QopAlgebra_ThetaN_sub g (fun i => mSigma E (σ i)) u X Y a
  -- the exact identity
  have key : STQop (d := d) ϑ (u + Δ) c a -
      Ugen d L g E σ u (u + Δ) (STQop (d := d) ϑ u X) a -
      (Δ : ℂ) * (STQop (d := d) ϑ u D a +
        (STQop (d := d) ϑ u (ThetaN d L g (fun i => mSigma E (σ i)) u X) a -
          ThetaN d L g (fun i => mSigma E (σ i)) u (STQop (d := d) ϑ u X) a) -
        STPsum (d := d) X (a 0) * deriv (fun τ => ϑ τ a) u) =
      (e a - STPsum (d := d) e (a 0) * ϑ (u + Δ) a) +
        (Δ : ℂ) * STPsum (d := d) D (a 0) * (ϑ u a - ϑ (u + Δ) a) +
        STPsum (d := d) X (a 0) * (ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u) +
        (Δ : ℂ) * STPsum (d := d) (ThetaN d L g (fun i => mSigma E (σ i)) u X) (a 0) *
          (ϑ u a - ϑ (u + Δ) a) +
        εY a - STPsum (d := d) εX (a 0) * ϑ (u + Δ) a := by
    rw [h5, h6]
    simp only [STQop]
    have hYa : Y a = STPsum (d := d) X (a 0) * ϑ u a := rfl
    have hea : e a = c a - Ugen d L g E σ u (u + Δ) X a - (Δ : ℂ) * D a := rfl
    have hεYa : εY a = Ugen d L g E σ u (u + Δ) Y a - Y a -
        (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u Y a := rfl
    linear_combination (-1 : ℂ) * hea + (-1 : ℂ) * hεYa + (1 : ℂ) * hYa +
      (-(ϑ (u + Δ) a)) * h3 + (-(ϑ (u + Δ) a)) * h4
  rw [key]
  -- the bounds on `ϑ`
  have hVd : ‖ϑ u a - ϑ (u + Δ) a‖ ≤ C * β * Δ := by
    rw [norm_sub_rev]; exact hlip a
  have hτB : ‖ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u‖ ≤
      C₂ * β ^ 2 * Δ ^ 2 := by
    have e' : ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u =
        -(ϑ (u + Δ) a - ϑ u a - (Δ : ℂ) * deriv (fun τ => ϑ τ a) u) := by ring
    rw [e', norm_neg]
    exact htay a
  have hPe : ‖STPsum (d := d) e (a 0)‖ ≤ Lp * S := QGridA_norm_Psum_le heb _
  have hPD : ‖STPsum (d := d) D (a 0)‖ ≤ Lp * Dm := QGridA_norm_Psum_le hD _
  have hPX : ‖STPsum (d := d) X (a 0)‖ ≤ Lp * Mk := QGridA_norm_Psum_le hX _
  have hΘX : ∀ b, ‖ThetaN d L g (fun i => mSigma E (σ i)) u X b‖ ≤ ((m + 1 : ℕ) : ℝ) * β * Mk :=
    fun b =>
      (QGridA_norm_ThetaN_le (g := g) hL hE σ hu0 hu1 hX b).trans (by
        have h0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * Mk := by positivity
        calc ((m + 1 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk = (((m + 1 : ℕ) : ℝ) * Mk) * (1 - u)⁻¹ := by ring
          _ ≤ (((m + 1 : ℕ) : ℝ) * Mk) * β := mul_le_mul_of_nonneg_left hβu h0
          _ = ((m + 1 : ℕ) : ℝ) * β * Mk := by ring)
  have hPΘ : ‖STPsum (d := d) (ThetaN d L g (fun i => mSigma E (σ i)) u X) (a 0)‖ ≤
      Lp * (((m + 1 : ℕ) : ℝ) * β * Mk) := QGridA_norm_Psum_le hΘX _
  have hPεX : ‖STPsum (d := d) εX (a 0)‖ ≤ Lp * (Ust * Mk) := QGridA_norm_Psum_le hεXb _
  have hϑva := hϑv a
  have hVd0 : 0 ≤ C * β * Δ := by positivity
  have t1 : ‖e a - STPsum (d := d) e (a 0) * ϑ (u + Δ) a‖ ≤ (1 + C * Lp) * S := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖STPsum (d := d) e (a 0)‖ * ‖ϑ (u + Δ) a‖ ≤ (Lp * S) * C :=
      mul_le_mul hPe hϑva (norm_nonneg _) (by positivity)
    have := heb a
    nlinarith
  have t2 : ‖(Δ : ℂ) * STPsum (d := d) D (a 0) * (ϑ u a - ϑ (u + Δ) a)‖ ≤
      Δ * (Lp * Dm) * (C * β * Δ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPD hΔ0) hVd (norm_nonneg _) (by positivity)
  have t3 : ‖STPsum (d := d) X (a 0) *
      (ϑ u a - ϑ (u + Δ) a + (Δ : ℂ) * deriv (fun τ => ϑ τ a) u)‖ ≤
      Lp * Mk * (C₂ * β ^ 2 * Δ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hPX hτB (norm_nonneg _) (by positivity)
  have t4 : ‖(Δ : ℂ) * STPsum (d := d) (ThetaN d L g (fun i => mSigma E (σ i)) u X) (a 0) *
      (ϑ u a - ϑ (u + Δ) a)‖ ≤
      Δ * (Lp * (((m + 1 : ℕ) : ℝ) * β * Mk)) * (C * β * Δ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPΘ hΔ0) hVd (norm_nonneg _) (by positivity)
  have t5 : ‖εY a‖ ≤ Ust * (Lp * Mk * C) := hεYb a
  have t6 : ‖STPsum (d := d) εX (a 0) * ϑ (u + Δ) a‖ ≤ Lp * (Ust * Mk) * C := by
    rw [norm_mul]
    exact mul_le_mul hPεX hϑva (norm_nonneg _) (by positivity)
  refine (QGridA_norm_six_le _ _ _ _ _ _).trans ?_
  unfold qStepErrN
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at t4
  linarith [t1, t2, t3, t4, t5, t6]

end QAlgebra

/-! ## 7. The deterministic envelope of the drift (RBM2D `AltGridQ_norm_drift_le`, counted with `W^d L^d`)

With `η = η_u`, `B_F = η^{-k} + Bk`: `|𝓛-𝒦| ≤ B_F` on the loops of length `2..k` (`Bk` the `𝒦`
envelope), `|𝓛| ≤ η^{-(k+1)}` on the loops of length `k+1`, `|avgErr| ≤ η⁻¹ + 1`.  The drift
`Σ_{l≥3}[𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}` is bounded by counting (`norm_primBil_le` for the two
cut couplings, one row of `S` for `𝓔^{(G̃)}`). -/

section DriftEnv

variable {d : ℕ} (sz : Sizes d)

private theorem QGridA_eta_le_one {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) : etaT E u ≤ 1 := by
  have hsq : Real.sqrt (4 - E ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have him : (mE E).im ≤ 1 := by rw [mE_im]; linarith
  have hIm : 0 ≤ (mE E).im := (mE_im_pos hE).le
  calc etaT E u = (1 - u) * (mE E).im := rfl
    _ ≤ 1 * 1 := mul_le_mul (by linarith) him hIm (by norm_num)
    _ = 1 := one_mul 1

/-- `|𝓛_{u,J}| ≤ η^{-K'}` for a well-formed loop `J` of length `1 ≤ |J| ≤ K'`. -/
private theorem QGridA_norm_STLIM_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian) {J : LoopIdx (Zd d (sz.L n))} (hJ : J.WF)
    {K' : ℕ} (h1 : 1 ≤ J.length) (hK' : J.length ≤ K') :
    ‖sz.STLIM n E u M J‖ ≤ (etaT E u)⁻¹ ^ K' := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hz : etaT E u ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_pos (mul_pos (sub_pos.2 hu1) (mE_im_pos hE))]
    exact le_rfl
  have h := norm_gloop_le_of_le_abs_im hHb hη hz J hJ h1
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d :=
    one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (J.a.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have hone : 1 ≤ (etaT E u)⁻¹ := (one_le_inv₀ hη).2 (QGridA_eta_le_one hE hu0)
  calc ‖sz.STLIM n E u M J‖ ≤ (etaT E u)⁻¹ ^ J.a.length * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (J.a.length - 1) := h
    _ ≤ (etaT E u)⁻¹ ^ J.a.length * 1 := mul_le_mul_of_nonneg_left hWi (by positivity)
    _ = (etaT E u)⁻¹ ^ J.a.length := mul_one _
    _ ≤ (etaT E u)⁻¹ ^ K' := pow_le_pow_right₀ hone hK'

/-- `|avgErr| ≤ η⁻¹ + 1` (`|𝓛_{(σ),(a)}| ≤ η⁻¹`, `|m| = 1`). -/
private theorem QGridA_norm_avgErr_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian) (s : Bool) (a : Zd d (sz.L n)) :
    ‖sz.STavgErrM n E u M s a‖ ≤ (etaT E u)⁻¹ + 1 := by
  unfold Sizes.STavgErrM
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have h := QGridA_norm_STLIM_le sz n hE hu0 hu1 hHb (J := ⟨[s], [a]⟩) (K' := 1)
      (by simp [LoopIdx.WF]) (by simp [LoopIdx.length]) (by simp [LoopIdx.length])
    simpa using h
  · rw [norm_mSigma hE.le]

/-- `∑_b ‖S_{ab}‖ = 1` (copy of the private `HierAlgebra_sum_norm_SB_row`). -/
private theorem QGridA_sum_norm_SB_row {L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) (a : Zd d L) :
    ∑ b : Zd d L, ‖SB d L g a b‖ = 1 := by
  have h := sum_nnnorm_SB_row d L g hL a
  have h' := congrArg (fun x : NNReal => (x : ℝ)) h
  simpa using h'

private theorem QGridA_norm_ite_le (p : Prop) [Decidable p] (x : ℂ) :
    ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

/-- The graded cut coupling `[𝒦∼(𝓛-𝒦)]^l` is a sum of two `primBil`s with the `𝒦` restricted to the
loops of length `l` (RBM2D `AltGridQ_ksimLK_eq`). -/
private theorem QGridA_ksimLK_eq (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (l : ℕ)
    (I : LoopIdx (Zd d (sz.L n))) :
    sz.STksimLKM n E u M l I =
      primBil d (sz.L n) (sz.W n) (sz.lam n) (sz.STLKIM n E u M)
          (fun J => if J.length = l then KLK d (sz.L n) (sz.lam n) (sz.W n) E u J else 0) I +
        primBil d (sz.L n) (sz.W n) (sz.lam n)
          (fun J => if J.length = l then KLK d (sz.L n) (sz.lam n) (sz.W n) E u J else 0)
          (sz.STLKIM n E u M) I := by
  unfold Sizes.STksimLKM primBil
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]

private theorem QGridA_norm_ksimLK_le (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {I : LoopIdx (Zd d (sz.L n))}
    (hI : I.WF) (l : ℕ) {BF Bk : ℝ} (hBF0 : 0 ≤ BF) (hBk0 : 0 ≤ Bk)
    (hF : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖sz.STLKIM n E u M J‖ ≤ BF)
    (hK : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E u J‖ ≤ Bk) :
    ‖sz.STksimLKM n E u M l I‖ ≤
      2 * (((sz.W n : ℕ) : ℝ) ^ d * (I.length : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk) := by
  rw [QGridA_ksimLK_eq]
  refine (norm_add_le _ _).trans ?_
  have hKl : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖(fun J : LoopIdx (Zd d (sz.L n)) =>
          if J.length = l then KLK d (sz.L n) (sz.lam n) (sz.W n) E u J else 0) J‖ ≤ Bk :=
    fun J h1 h2 h3 => (QGridA_norm_ite_le _ _).trans (hK J h1 h2 h3)
  have h1 := norm_primBil_le d (sz.L n) (sz.W n) (sz.lam n) (sz.three_le_L n) (sz.STLKIM n E u M)
    (fun J => if J.length = l then KLK d (sz.L n) (sz.lam n) (sz.W n) E u J else 0) I hI hBF0 hBk0
    hF hKl
  have h2 := norm_primBil_le d (sz.L n) (sz.W n) (sz.lam n) (sz.three_le_L n)
    (fun J => if J.length = l then KLK d (sz.L n) (sz.lam n) (sz.W n) E u J else 0)
    (sz.STLKIM n E u M) I hI hBk0 hBF0 hKl hF
  linarith [h1, h2]

private theorem QGridA_norm_elklkN_le (n : ℕ) (E u : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {I : LoopIdx (Zd d (sz.L n))}
    (hI : I.WF) {BF : ℝ} (hBF0 : 0 ≤ BF)
    (hF : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖sz.STLKIM n E u M J‖ ≤ BF) :
    ‖sz.STelklkM n E u M I‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (I.length : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * BF :=
  norm_primBil_le d (sz.L n) (sz.W n) (sz.lam n) (sz.three_le_L n) (sz.STLKIM n E u M)
    (sz.STLKIM n E u M) I hI hBF0 hBF0 hF hF

/-- The operation `cutGlue` adds exactly one Green edge (copy of the private `OneStep_length_cutGlue`). -/
private theorem QGridA_length_cutGlue {α : Type*} (I : LoopIdx α) (b : α) {k : ℕ}
    (hk : k ≤ I.length) : (I.cutGlue k b).length = I.length + 1 := by
  simp only [LoopIdx.length, LoopIdx.cutGlue, List.length_append, List.length_take,
    List.length_cons, List.length_drop] at hk ⊢
  omega

/-- A valid one-based cut preserves well-formedness (copy of the private `OneStep_wf_cutGlue`). -/
private theorem QGridA_wf_cutGlue {α : Type*} {I : LoopIdx α} (hI : I.WF) (b : α) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ I.length) : (I.cutGlue k b).WF := by
  simp only [LoopIdx.WF, LoopIdx.length, LoopIdx.cutGlue, List.length_append,
    List.length_take, List.length_cons, List.length_drop] at hI hk ⊢
  omega

/-- `‖𝓔^{(G̃)}‖ ≤ W^d k L^d (η⁻¹ + 1) η^{-(k+1)}` (one row of `S` per cut). -/
private theorem QGridA_norm_egtN_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian) {I : LoopIdx (Zd d (sz.L n))}
    (hI : I.WF) {k : ℕ} (hk : I.length = k) :
    ‖sz.STegtM n E u M I‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
        (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))) := by
  unfold Sizes.STegtM
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hη0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη.le
  have hone : ∀ k' ∈ Finset.Icc 1 I.length,
      ‖∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), sz.STavgErrM n E u M (I.σ.getD (k' - 1) false) a *
        SB d (sz.L n) (sz.lam n) a b * sz.STLIM n E u M (I.cutGlue k' b)‖ ≤
      ((sz.L n : ℕ) : ℝ) ^ d * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
    intro k' hk'
    rw [Finset.mem_Icc] at hk'
    have hBG : ∀ b : Zd d (sz.L n), ‖sz.STLIM n E u M (I.cutGlue k' b)‖ ≤ (etaT E u)⁻¹ ^ (k + 1) := by
      intro b
      have hJ := QGridA_wf_cutGlue hI b hk'.1 hk'.2
      have hlen := QGridA_length_cutGlue I b hk'.2
      exact QGridA_norm_STLIM_le sz n hE hu0 hu1 hHb hJ (by omega) (by omega)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a : Zd d (sz.L n), ‖∑ b : Zd d (sz.L n), sz.STavgErrM n E u M (I.σ.getD (k' - 1) false) a *
          SB d (sz.L n) (sz.lam n) a b * sz.STLIM n E u M (I.cutGlue k' b)‖
        ≤ ∑ _a : Zd d (sz.L n), (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine (norm_sum_le _ _).trans ?_
          calc ∑ b : Zd d (sz.L n), ‖sz.STavgErrM n E u M (I.σ.getD (k' - 1) false) a *
                SB d (sz.L n) (sz.lam n) a b * sz.STLIM n E u M (I.cutGlue k' b)‖
              ≤ ∑ b : Zd d (sz.L n), (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) *
                  ‖SB d (sz.L n) (sz.lam n) a b‖ := by
                refine Finset.sum_le_sum fun b _ => ?_
                rw [norm_mul, norm_mul]
                have h1 := QGridA_norm_avgErr_le sz n hE hu0 hu1 hHb (I.σ.getD (k' - 1) false) a
                have h2 := hBG b
                calc ‖sz.STavgErrM n E u M (I.σ.getD (k' - 1) false) a‖ *
                      ‖SB d (sz.L n) (sz.lam n) a b‖ * ‖sz.STLIM n E u M (I.cutGlue k' b)‖
                    ≤ ((etaT E u)⁻¹ + 1) * ‖SB d (sz.L n) (sz.lam n) a b‖ * (etaT E u)⁻¹ ^ (k + 1) :=
                      mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
                        (norm_nonneg _) (by positivity)
                  _ = (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) *
                        ‖SB d (sz.L n) (sz.lam n) a b‖ := by ring
            _ = (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
                rw [← Finset.mul_sum, QGridA_sum_norm_SB_row (sz.lam n) (sz.three_le_L n) a, mul_one]
      _ = ((sz.L n : ℕ) : ℝ) ^ d * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          ring
  calc ∑ k' ∈ Finset.Icc 1 I.length,
        ‖∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), sz.STavgErrM n E u M (I.σ.getD (k' - 1) false) a *
          SB d (sz.L n) (sz.lam n) a b * sz.STLIM n E u M (I.cutGlue k' b)‖
      ≤ ∑ _k' ∈ Finset.Icc 1 I.length,
          ((sz.L n : ℕ) : ℝ) ^ d * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)) :=
        Finset.sum_le_sum hone
    _ = (k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d * (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hk]
        simp

/-- **The drift envelope**: for every Hermitian grid state `M`, every sign vector and label, with the
`𝒦` envelope `Bk` at the time `u`,
`|Σ_{l=3}^k [𝒦∼(𝓛-𝒦)]^l + 𝓔^{(𝓛-𝒦)×(𝓛-𝒦)} + 𝓔^{(G̃)}| ≤ driftEnvN`. -/
private theorem QGridA_norm_drift_le (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hHb : (blockMat d (sz.L n) (sz.W n) M).IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E u J‖ ≤ Bk) (a : Fin k → Zd d (sz.L n)) :
    ‖∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a) +
        sz.STelklkM n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)‖ ≤
      driftEnvN d (sz.L n) (sz.W n) E k u Bk := by
  have hI : (loopOf σ a).WF := QGridA_loopOf_wf σ a
  have hlen : (loopOf σ a).length = k := QGridA_loopOf_length σ a
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hη0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη.le
  set BF : ℝ := (etaT E u)⁻¹ ^ k + Bk with hBF
  have hBF0 : 0 ≤ BF := by positivity
  have hF : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ a).length →
      ‖sz.STLKIM n E u M J‖ ≤ BF := by
    intro J hJ h2 hJk
    rw [hlen] at hJk
    unfold Sizes.STLKIM
    exact (norm_sub_le _ _).trans (add_le_add
      (QGridA_norm_STLIM_le sz n hE hu0 hu1 hHb hJ (by omega) hJk) (hBk J hJ h2 hJk))
  have hK : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ (loopOf σ a).length →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E u J‖ ≤ Bk := fun J hJ h2 hJk =>
    hBk J hJ h2 (hlen ▸ hJk)
  have h1 : ‖∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a)‖ ≤
      (k : ℝ) * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l ∈ Finset.Icc 3 k, ‖sz.STksimLKM n E u M l (loopOf σ a)‖
        ≤ ∑ _l ∈ Finset.Icc 3 k,
            (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) :=
          Finset.sum_le_sum fun l _ => by
            have := QGridA_norm_ksimLK_le sz n E u M hI l hBF0 hBk0 hF hK
            rwa [hlen] at this
      _ = ((Finset.Icc 3 k).card : ℝ) *
            (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : k + 1 - 3 ≤ k)
  have h2 : ‖sz.STelklkM n E u M (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * BF := by
    have := QGridA_norm_elklkN_le sz n E u M hI hBF0 hF
    rwa [hlen] at this
  have h3 := QGridA_norm_egtN_le sz n hE hu0 hu1 hHb hI hlen
  calc _ ≤ ‖∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u M l (loopOf σ a)‖ +
        ‖sz.STelklkM n E u M (loopOf σ a)‖ + ‖sz.STegtM n E u M (loopOf σ a)‖ := norm_add₃_le
    _ ≤ (k : ℝ) * (2 * (((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * Bk)) +
        ((sz.W n : ℕ) : ℝ) ^ d * (k : ℝ) ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d * BF * BF +
        ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
          (((etaT E u)⁻¹ + 1) * (etaT E u)⁻¹ ^ (k + 1)))) := by linarith [h1, h2, h3]
    _ = driftEnvN d (sz.L n) (sz.W n) E k u Bk := by
        unfold driftEnvN
        rw [hBF]
        ring

end DriftEnv

/-! ## 8. Target 2: the one-step identity of `int_K-L+Q` on the grid -/

section GridDriftQ

variable {d : ℕ} (sz : Sizes d)

/-- `A_i = (𝓛 - 𝒦)_{u_i,σ}` along the walk is the loop of the block matrix minus `𝒦` (copy of the
private `gdn_AvecN_eq` of `GridDriftN.lean`). -/
private theorem QGridA_AvecN_eq (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {k : ℕ}
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

/-- Every label of `A_i` is integrable (`𝓛` is bounded by `η^{-k}`, `𝒦` is deterministic). -/
private theorem QGridA_integrable_AvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ)
    (hE : |E n| < 2) (hi : gridTime s t K n i < 1) {k : ℕ} (σ : Fin k → Bool) (hk : 1 ≤ k)
    (b : Fin k → Zd d (sz.L n)) :
    Integrable (fun ω : PathΩ sz => AvecN sz E s t K n i σ ω b) (pathP sz) := by
  have h := QGridA_integrable_loopL sz s t K n i hE hi (loopOf σ b) (QGridA_loopOf_wf σ b)
    (by rw [QGridA_loopOf_length]; exact hk)
  have h2 := h.sub (integrable_const
    (KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n i) (loopOf σ b)))
  refine h2.congr (Eventually.of_forall fun ω => ?_)
  exact (QGridA_AvecN_eq sz E s t K n i σ ω b).symm

/-- **`𝔼[·| F_j]` commutes with `𝒬_{u_{j+1}}`** (a.e., label by label): the `𝒬`-process satisfies
`𝔼[A^Q_{j+1}(a) | F_j] = (𝒬_{u_{j+1}} c)(a)`, `c_b = 𝔼[A_{j+1}(b) | F_j]` (RBM2D
`AltGridQ_condExp_aTrueQN`, `AltGridQ:1499`). -/
theorem QGridA_condExp_aTrueQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hj1 : gridTime s t K n (j + 1) < 1) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d (sz.L n)) :
    ∀ᵐ ω ∂(pathP sz), (pathP sz)[fun ω' => aTrueQN sz E s t K n ϑ σ (j + 1) ω' a | filt sz j] ω =
      STQop (d := d) ϑ (gridTime s t K n (j + 1))
        (fun b => (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' b | filt sz j] ω) a := by
  have hk1 : 1 ≤ m + 1 := by omega
  have hInt := QGridA_integrable_AvecN sz E s t K n (j + 1) hE hj1 σ hk1
  set F : Finset (Fin (m + 1) → Zd d (sz.L n)) :=
    Finset.univ.filter (fun b : Fin (m + 1) → Zd d (sz.L n) => b 0 = a 0) with hF
  have hfun : (fun ω' => aTrueQN sz E s t K n ϑ σ (j + 1) ω' a) =
      (fun ω' => AvecN sz E s t K n (j + 1) σ ω' a) -
        ϑ (gridTime s t K n (j + 1)) a •
          ∑ b ∈ F, (fun ω' => AvecN sz E s t K n (j + 1) σ ω' b) := by
    funext ω'
    simp only [aTrueQN, STQop, STPsum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    ring
  have hsumInt : Integrable (∑ b ∈ F, (fun ω' => AvecN sz E s t K n (j + 1) σ ω' b))
      (pathP sz) := integrable_finsetSum' F fun b _ => hInt b
  rw [hfun]
  filter_upwards [condExp_sub (hInt a)
      (hsumInt.smul (ϑ (gridTime s t K n (j + 1)) a)) (filt sz j),
    condExp_smul (ϑ (gridTime s t K n (j + 1)) a)
      (∑ b ∈ F, (fun ω' => AvecN sz E s t K n (j + 1) σ ω' b)) (filt sz j),
    condExp_finsetSum (fun b _ => hInt b) (filt sz j)] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Finset.sum_apply, smul_eq_mul]
  simp only [STQop, STPsum]
  ring

end GridDriftQ

section GridDriftQ2

variable {d : ℕ} (sz : Sizes d)

/-- From `STMollifierProps`: `‖ϑ_t‖ ≤ C` on `[0, 1)` (`ℓ_t ≥ 1`, `c ≥ 0`, `C ≥ 0`). -/
private theorem QGridA_vartheta_sup {m L : ℕ} [NeZero L] (hL : 1 ≤ L) {g C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 ≤ c) {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ}
    (hϑ : STMollifierProps (d := d) g C c ϑ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Fin (m + 1) → Zd d L) : ‖ϑ t a‖ ≤ C := by
  have h := hϑ.2.1 t ht0 ht1 a
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT (by exact_mod_cast hL)
  have hℓ0 : 0 < ellT L g t := lt_of_lt_of_le zero_lt_one hℓ1
  have h1 : (((ellT L g t) ^ d)⁻¹) ^ m ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (by positivity)) (inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1))
  have h2 : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
      (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have hs : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have : 0 ≤ c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) :=
      mul_nonneg hc hs
    rw [neg_mul]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ0.le
  refine h.trans ?_
  calc C * (((ellT L g t) ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
        (zdistD d L (a i - a 0) : ℝ)) / ellT L g t) ≤ C * 1 * 1 := by
        gcongr
    _ = C := by ring

/-- From `STMollifierProps` and differentiability: the Lipschitz bound
`‖ϑ_{u+Δ} - ϑ_u‖ ≤ C (1-(u+Δ))⁻¹ Δ` (mean-value theorem on `[u, u+Δ]`). -/
private theorem QGridA_vartheta_lip {m L : ℕ} [NeZero L] (hL : 1 ≤ L) {g C c : ℝ} (hC : 0 ≤ C)
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hϑ : STMollifierProps (d := d) g C c ϑ)
    (hdiff : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a, DifferentiableAt ℝ (fun τ => ϑ τ a) t)
    {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (a : Fin (m + 1) → Zd d L) :
    ‖ϑ (u + Δ) a - ϑ u a‖ ≤ C * (1 - (u + Δ))⁻¹ * Δ := by
  have hpos : 0 < 1 - (u + Δ) := by linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun τ => ϑ τ a)
    (f' := fun τ => deriv (fun τ => ϑ τ a) τ) (a := u) (b := u + Δ) (C := C * (1 - (u + Δ))⁻¹)
    (fun x hx => (hdiff x (hu0.trans hx.1) (lt_of_le_of_lt hx.2 hv) a).hasDerivAt.hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 ≤ x := hu0.trans hx.1
      have hx1 : x < 1 := by linarith [hx.2]
      have h := hϑ.2.2.2 x hx0 hx1 a
      have hℓ : 1 ≤ ellT L g x := one_le_ellT (by exact_mod_cast hL)
      have h1 : (((ellT L g x) ^ d)⁻¹) ^ m ≤ 1 :=
        pow_le_one₀ (inv_nonneg.2 (by positivity)) (inv_le_one_of_one_le₀ (one_le_pow₀ hℓ))
      have h2 : (1 - x)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hpos (by linarith [hx.2])
      refine h.trans ?_
      calc C * (1 - x)⁻¹ * (((ellT L g x) ^ d)⁻¹) ^ m ≤ C * (1 - x)⁻¹ * 1 := by gcongr
        _ ≤ C * (1 - (u + Δ))⁻¹ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 hC)
    (u + Δ) ⟨by linarith, le_rfl⟩
  simpa using key

end GridDriftQ2

section GridDriftQ3

variable {d : ℕ} (sz : Sizes d)

/-- **`gridDriftQN` for a general mollifier family** (the engine of the target): the one-step
identity of `int_K-L+Q` for every `ϑ` with `STMollifierProps (sz.lam n) C c ϑ`, differentiable on
`[0, 1)` and satisfying the second-order Taylor bound `QGridA_Taylor2 C₂` (the part of the
time regularity of `ϑ` that `STMollifierProps` does not give; paper-delta candidate `T2132b`).  A.e.,
for every label,
`‖𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1}} A^Q_j - Δ dGridQN_j‖ ≤ qErrQN_j`.
Proof: the merged `gridDriftN_at` gives `c = 𝒰 X + Δ D + e`, `‖e‖ ≤ stepErrN`; conditional
expectation commutes with `𝒬_{u_{j+1}}`; the deterministic identity `QGridA_qstep_algebra`
finishes.  RBM2D `gridDriftQN` (`AltGridQ:1536`). -/
theorem QGridA_gridDriftQN_of {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n)
    {m : ℕ} (hm : 1 ≤ m) (σ : Fin (m + 1) → Bool) (Bk : ℝ) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 1 →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤ Bk)
    {C c C₂ : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (hdiff : ∀ τ : ℝ, 0 ≤ τ → τ < 1 → ∀ a, DifferentiableAt ℝ (fun τ' => ϑ τ' a) τ)
    (hTay : QGridA_Taylor2 C₂ ϑ) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin (m + 1) → Zd d (sz.L n),
      ‖(pathP sz)[fun ω' => aTrueQN sz E s t K n ϑ σ (j + 1) ω' a | filt sz j] ω -
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
            (aTrueQN sz E s t K n ϑ σ j ω) a -
          (gridStep s t K n : ℂ) * dGridQN sz E s t K n ϑ σ j ω a‖ ≤
        qErrQN sz E s t K n m C C₂ Bk j := by
  obtain ⟨hΔ0, hu0, hvu, hv1, hΔ1⟩ := QGridA_time_facts s t K n j hs0 hst ht1 hK hj
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hkpos : 1 ≤ m + 1 := by omega
  have hu1 : gridTime s t K n j < 1 := by linarith
  have hT := gridDriftN_at sz E s t K n j hE hs0 hst ht1 hK hj (k := m + 1) (by omega) σ Bk hBk hB
  have hlin' := ae_all_iff.2 fun a =>
    QGridA_condExp_aTrueQN sz E s t K n j hE hv1 ϑ σ a
  have hη : 0 < etaT (E n) (gridTime s t K n j) := etaT_pos hE hu1
  have hz : etaT (E n) (gridTime s t K n j) ≤ |(zt (E n) (gridTime s t K n j)).im| := by
    rw [zt_im, abs_of_pos (mul_pos (sub_pos.2 hu1) (mE_im_pos hE))]
    exact le_rfl
  have hBk' : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ m + 1 →
      ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j) J‖ ≤ Bk :=
    fun J hJ h2 hJk => hB _ ⟨hu0, by rw [hvu]; linarith⟩ J hJ h2 hJk
  -- the mollifier facts at `u_j`, `u_{j+1}`
  have hL1 : 1 ≤ sz.L n := by omega
  have hϑu : ∀ a, ‖ϑ (gridTime s t K n j) a‖ ≤ C := fun a =>
    QGridA_vartheta_sup hL1 hC hc hϑ hu0 hu1 a
  have hϑv : ∀ a, ‖ϑ (gridTime s t K n j + gridStep s t K n) a‖ ≤ C := fun a =>
    QGridA_vartheta_sup hL1 hC hc hϑ (by linarith) (by rw [← hvu]; exact hv1) a
  have hlip := fun a => QGridA_vartheta_lip hL1 hC hϑ hdiff hu0 hΔ0 (by rw [← hvu]; exact hv1) a
  have htay := fun a => hTay _ _ hu0 hΔ0 (by rw [← hvu]; exact hv1) a
  filter_upwards [hT, hlin'] with ω hTω hlinω a
  have hHb : (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω)).IsHermitian :=
    (pathH_isHermitian sz s t K n j ω).submatrix _
  -- the sup bound on `A_j`
  have hX : ∀ b : Fin (m + 1) → Zd d (sz.L n), ‖AvecN sz E s t K n j σ ω b‖ ≤
      lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk := by
    intro b
    have hlen : (loopOf σ b).a.length = m + 1 := by simp [loopOf]
    have h1 := norm_gloop_le_of_le_abs_im hHb hη hz (loopOf σ b) (QGridA_loopOf_wf σ b)
      (by rw [hlen]; exact hkpos)
    rw [hlen] at h1
    have h2 := hBk' (loopOf σ b) (QGridA_loopOf_wf σ b)
      (by rw [QGridA_loopOf_length]; omega)
      (by rw [QGridA_loopOf_length])
    rw [QGridA_AvecN_eq]
    calc ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
            (zt (E n) (gridTime s t K n j)) (loopOf σ b) -
          KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j) (loopOf σ b)‖
        ≤ ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
            (zt (E n) (gridTime s t K n j)) (loopOf σ b)‖ +
          ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) (gridTime s t K n j) (loopOf σ b)‖ :=
          norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h2
  -- the sup bound on the drift
  have hD : ∀ b : Fin (m + 1) → Zd d (sz.L n),
      ‖∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n (E n) (gridTime s t K n j)
            (pathH sz s t K n j ω) l (loopOf σ b) +
          sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b) +
          sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b)‖ ≤
        driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk := fun b =>
    QGridA_norm_drift_le sz n hE hu0 hu1 hHb σ hBk hBk' b
  -- the merged one-step bound in the shape of the algebra lemma
  have hc' : ∀ b : Fin (m + 1) → Zd d (sz.L n),
      ‖(pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' b | filt sz j] ω -
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j)
            (gridTime s t K n j + gridStep s t K n) (AvecN sz E s t K n j σ ω) b -
          (gridStep s t K n : ℂ) *
            (∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n (E n) (gridTime s t K n j)
                (pathH sz s t K n j ω) l (loopOf σ b) +
              sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b) +
              sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b))‖ ≤
        stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n) Bk := by
    intro b
    rw [← hvu]
    have := hTω b
    simpa [predIncN] using this
  have hmain := QGridA_qstep_algebra (g := sz.lam n) hL3 hm (hE |>.le) σ hu0 hΔ0
    (by rw [← hvu]; exact hv1) hϑu hϑv hlip htay hX hD hc' a
  rw [← hvu] at hmain
  rw [hlinω a]
  exact hmain

end GridDriftQ3

section Targets

variable {d : ℕ} (sz : Sizes d)

/-- **Target 2 (`gridDriftQN`)**: the `𝒬`-analogue of the merged `gridDriftN_at` for the merged
mollifier `QopAlgebra_mollifier d L m (sz.lam n)` (`Σ_{a₂..a_n} ϑ = 1`, `‖ϑ‖ ≤ C`, `‖∂_tϑ‖ ≤ C (1-t)⁻¹`,
`C = (1 + 40 d m) 6^{d m}`, `c = 1/2`: `QopAlgebra_mollifier_props`) and the second-order Taylor
bound `C₂ = 1000 (1 + d m)²` (`QGridA_mollifier_taylor2`): a.e., for every label,
`‖𝔼[A^Q_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A^Q_j - Δ dGridQN_j‖ ≤ qErrQN_j`.
The hypotheses are those of `gridDriftN_at` (DECISIONS §29 (4): at the size index `n` only; the
envelope `B_k` of `𝒦` on `[0, u_{j+1}]` is a hypothesis as there) plus `0 < sz.lam n` (`g > 0` of the
mollifier).  `m + 1 ≥ 2` indices.  Time regularity of `ϑ`: route (b) of the ticket
(`QGridA_gridDriftQN_of` is the version for any `ϑ` with the Taylor bound as a hypothesis). -/
theorem gridDriftQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n)
    (hlam : 0 < sz.lam n) {m : ℕ} (hm : 1 ≤ m) (σ : Fin (m + 1) → Bool) (Bk : ℝ) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 1 →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin (m + 1) → Zd d (sz.L n),
      ‖(pathP sz)[fun ω' => aTrueQN sz E s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n))
            σ (j + 1) ω' a | filt sz j] ω -
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
            (aTrueQN sz E s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) a -
          (gridStep s t K n : ℂ) *
            dGridQN sz E s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω a‖ ≤
        qErrQN sz E s t K n m ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
          (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) Bk j :=
  QGridA_gridDriftQN_of sz E s t K n j hE hs0 hst ht1 hK hj hm σ Bk hBk hB (by positivity)
    (by norm_num) (QopAlgebra_mollifier d (sz.L n) m (sz.lam n))
    (QopAlgebra_mollifier_props d (sz.L n) m (sz.three_le_L n) hlam)
    (fun τ _ hτ a => QopAlgebra_mollifier_differentiableAt d (sz.L n) m (sz.three_le_L n) hlam hτ a)
    (QGridA_mollifier_taylor2 d (sz.L n) m (sz.three_le_L n) hlam)

end Targets

/-! ## 9. Target 3: the stopped Duhamel expansion of the frozen `𝒬`-process -/

section StoppedDuhamelQ

variable {d : ℕ} (sz : Sizes d)

private theorem QGridA_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

private theorem QGridA_gridTime_lt_one (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    (hK : K n ≠ 0) (ht1 : t n < 1) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j < 1 := by
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  have h : gridTime s t K n j ≤ gridTime s t K n (K n) := by
    unfold gridTime
    have : (j : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hj
    nlinarith
  rw [gridTime_last s t K n hK] at h
  linarith

/-- **Target 3 (`stoppedDuhamelQN`)**: the `𝒬`-analogue of the merged `stoppedDuhamelN_at` for the frozen
process `aFrozQN`, pathwise, for every mollifier family `ϑ`, every stopping index
`τ : PathΩ sz → ℕ` and every grid index `j ≤ K n` (hypotheses at the size index `n` only,
DECISIONS §29 (4)):
`A^{Q,frz}_j = 𝒰_{u_0,u_j} A^Q_0 + Σ_{i<j∧τ} 𝒰_{u_{i+1},u_j}(Δ dGridQN_i + ξ^Q_{i+1} + R^Q_i)`.
The remainder `R^Q_i = rGridQN` is named by subtraction; `gridDriftQN` bounds it a.e. by `qErrQN`.
The telescope is the merged `GridDuhamelN_Ugen_duhamel_telescope`. RBM2D `stoppedDuhamelQN`
(`AltGridQ:1627`). -/
theorem stoppedDuhamelQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hj : j ≤ K n) :
    aFrozQN sz E s t K n ϑ σ τ j ω =
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n j)
          (aTrueQN sz E s t K n ϑ σ 0 ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1)) (gridTime s t K n j)
            ((gridStep s t K n : ℂ) • dGridQN sz E s t K n ϑ σ i ω +
              martIncQN sz E s t K n ϑ σ i ω + rGridQN sz E s t K n ϑ σ i ω) := by
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hmin : min j (τ ω) ≤ K n := (min_le_left _ _).trans hj
  have hu0 : ∀ i, 0 ≤ gridTime s t K n i := QGridA_gridTime_nonneg s t K n hs0 hst
  have hu1 : ∀ i ≤ K n, gridTime s t K n i < 1 := fun i hi =>
    QGridA_gridTime_lt_one s t K n hst hK ht1 hi
  have htele := GridDuhamelN_Ugen_duhamel_telescope (g := sz.lam n) hL3 hE.le σ
    (gridTime s t K n) (min j (τ ω)) (fun i _ => hu0 i) (fun i hi => hu1 i (hi.trans hmin))
    (fun i => aTrueQN sz E s t K n ϑ σ i ω)
  have hinc : ∀ i, aTrueQN sz E s t K n ϑ σ (i + 1) ω -
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n i) (gridTime s t K n (i + 1))
        (aTrueQN sz E s t K n ϑ σ i ω) =
      (gridStep s t K n : ℂ) • dGridQN sz E s t K n ϑ σ i ω +
        martIncQN sz E s t K n ϑ σ i ω + rGridQN sz E s t K n ϑ σ i ω := by
    intro i
    funext a
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, martIncQN, rGridQN]
    ring
  simp only [hinc] at htele
  unfold aFrozQN
  refine (congrArg (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (min j (τ ω)))
    (gridTime s t K n j)) htele).trans ?_
  rw [GridDuhamelN_Ugen_add]
  have hcomp : ∀ (i : ℕ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ),
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (min j (τ ω))) (gridTime s t K n j)
        (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n i)
          (gridTime s t K n (min j (τ ω))) A) =
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n i) (gridTime s t K n j) A := fun i A =>
    GridDuhamelN_Ugen_comp (g := sz.lam n) hL3 hE.le σ (hu0 _) (hu1 _ hmin) (hu0 _) (hu1 _ hj) A
  have hsum := map_sum
    (GridDuhamelN_UgenHom d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (min j (τ ω)))
      (gridTime s t K n j))
    (fun i => Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
      (gridTime s t K n (min j (τ ω)))
      ((gridStep s t K n : ℂ) • dGridQN sz E s t K n ϑ σ i ω +
        martIncQN sz E s t K n ϑ σ i ω + rGridQN sz E s t K n ϑ σ i ω))
    (Finset.range (min j (τ ω)))
  refine congrArg₂ (· + ·) (hcomp 0 _) ?_
  refine hsum.trans (Finset.sum_congr rfl fun i _ => hcomp (i + 1) _)

end StoppedDuhamelQ

/-! ## 11. Compiled nonempty instances

The merged admissible sequence `RBM.Gauss.SizesInst.sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`,
`lam_0 = 1/64`) and the grid data of `GridDriftNCheck`: `E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`
(`Δ = 1/10`, `u_0 = 1/10`, `u_1 = 1/5`), size index `n = 0`, `k = 4 = m + 1` (`m = 3`) and the
alternating sign vector `σ = (+,-,+,-)`; the mollifier is the merged `QopAlgebra_mollifier 3 4 3 (1/64)`.
Every deterministic hypothesis is discharged: `|E| < 2`, `0 ≤ s ≤ t < 1`, `K ≠ 0`, `j < K`, `0 < lam`,
the envelope `B_4` of `𝒦` on `[0, u_1]` (`GridDriftN_exists_envelope`); nothing is left as a
hypothesis (no external input is used). -/

namespace QGridACheck

open RBM.Gauss.SizesInst RBM.Ind.GridDriftNCheck

/-- The alternating sign vector `(+,-,+,-)`. -/
def sigma4 : Fin (3 + 1) → Bool := ![true, false, true, false]

/-- The sign vector is alternating (`σ_{i+1} ≠ σ_i` cyclically), so the `𝒬`-hierarchy is the relevant one. -/
theorem sigma4_alternating : STAlternating sigma4 := by
  unfold STAlternating sigma4
  decide

/-- The mollifier family at `sz0`, `n = 0`, `m = 3`: `QopAlgebra_mollifier 3 (L_0) 3 (lam_0)`. -/
abbrev moll : ℝ → (Fin (3 + 1) → Zd 3 (sz0.L 0)) → ℂ :=
  QopAlgebra_mollifier 3 (sz0.L 0) 3 (sz0.lam 0)

theorem lam_pos : 0 < sz0.lam 0 := by rw [sz0_values.2.2.2]; norm_num

/-- **Instance of `gridDriftQN`** (target 2) at `sz0`, `k = 4`, `σ = (+,-,+,-)`, `j = 0 < 4`: for the
merged mollifier and a finite envelope `B_4 ≥ 0` of `𝒦` on `[0, u_1]` (it exists), a.e. in the
walk, every label `a ∈ ((ℤ_4)^3)^4` satisfies the one-step bound by `qErrQN`
(`C = (1 + 40·9) 6^9`, `C₂ = 1000 (1 + 9)²`). -/
theorem gridDriftQN_instance :
    STAlternating sigma4 ∧
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ᵐ ω ∂(pathP sz0), ∀ a : Fin (3 + 1) → Zd 3 (sz0.L 0),
      ‖(pathP sz0)[fun ω' => aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 (0 + 1) ω' a | filt sz0 0] ω -
          Ugen 3 (sz0.L 0) (sz0.lam 0) (E0 0) sigma4 (gridTime s0 t0 K0 0 0)
            (gridTime s0 t0 K0 0 (0 + 1)) (aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω) a -
          (gridStep s0 t0 K0 0 : ℂ) * dGridQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω a‖ ≤
        qErrQN sz0 E0 s0 t0 K0 0 3 ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3))
          (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2) Bk 0 := by
  obtain ⟨_, _, _, hv1, _⟩ := QGridA_time_facts s0 t0 K0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Bk, hB0, hB⟩ := GridDriftN_exists_envelope (d := 3) (L := sz0.L 0) (W := sz0.W 0)
    (g := sz0.lam 0) (sz0.three_le_L 0) (sz0.W_pos 0) (E := E0 0) (by norm_num)
    (v := gridTime s0 t0 K0 0 (0 + 1)) (by rw [data.2.2]; norm_num) hv1 (3 + 1)
  exact ⟨sigma4_alternating, Bk, hB0, gridDriftQN sz0 E0 s0 t0 K0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) lam_pos (m := 3) (by norm_num) sigma4 Bk
    hB0 hB⟩

/-- **Instance of `stoppedDuhamelQN`** (target 3) at the same data with the stopping index `τ ≡ 3` and
the grid index `j = 4 = K 0` (so `j ∧ τ = 3`: three genuine Duhamel steps), for every path. -/
theorem stoppedDuhamelQN_instance (ω : PathΩ sz0) :
    STAlternating sigma4 ∧
    aFrozQN sz0 E0 s0 t0 K0 0 moll sigma4 (fun _ => 3) 4 ω =
      Ugen 3 (sz0.L 0) (sz0.lam 0) (E0 0) sigma4 (gridTime s0 t0 K0 0 0) (gridTime s0 t0 K0 0 4)
          (aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (E0 0) sigma4 (gridTime s0 t0 K0 0 (i + 1))
            (gridTime s0 t0 K0 0 4)
            ((gridStep s0 t0 K0 0 : ℂ) • dGridQN sz0 E0 s0 t0 K0 0 moll sigma4 i ω +
              martIncQN sz0 E0 s0 t0 K0 0 moll sigma4 i ω +
              rGridQN sz0 E0 s0 t0 K0 0 moll sigma4 i ω) :=
  ⟨sigma4_alternating, stoppedDuhamelQN sz0 E0 s0 t0 K0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) moll sigma4 (fun _ => 3) 4 ω (by norm_num)⟩

/-- **Instance of `QGridA_mollifier_taylor2`** at `d = 3`, `L = 4`, `m = 3`, `g = 1/64`. -/
theorem taylor2_instance :
    QGridA_Taylor2 (d := 3) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2) moll :=
  QGridA_mollifier_taylor2 3 (sz0.L 0) 3 (sz0.three_le_L 0) lam_pos

end QGridACheck


end RBM.Ind

end

#print axioms RBM.Ind.aTrueQN
#print axioms RBM.Ind.dGridQN
#print axioms RBM.Ind.aFrozQN
#print axioms RBM.Ind.martIncQN
#print axioms RBM.Ind.rGridQN
#print axioms RBM.Ind.lkEnvN
#print axioms RBM.Ind.driftEnvN
#print axioms RBM.Ind.qStepErrN
#print axioms RBM.Ind.qErrQN
#print axioms RBM.Ind.QGridA_Taylor2
#print axioms RBM.Ind.QGridA_mollifier_taylor2
#print axioms RBM.Ind.QGridA_condExp_aTrueQN
#print axioms RBM.Ind.QGridA_gridDriftQN_of
#print axioms RBM.Ind.gridDriftQN
#print axioms RBM.Ind.stoppedDuhamelQN
#print axioms RBM.Ind.QGridACheck.sigma4
#print axioms RBM.Ind.QGridACheck.sigma4_alternating
#print axioms RBM.Ind.QGridACheck.lam_pos
#print axioms RBM.Ind.QGridACheck.gridDriftQN_instance
#print axioms RBM.Ind.QGridACheck.stoppedDuhamelQN_instance
#print axioms RBM.Ind.QGridACheck.taylor2_instance
