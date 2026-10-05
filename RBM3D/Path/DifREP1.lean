/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.Split
import RBM3D.Loop.KLFinal
import RBM3D.Green.CondDom

/-!
# `STGridRepN`, part 1: the canonical split, the remainder bound, the assembly (`d ≥ 3`)

Ticket T2168 (ST2-12, stochastic layer ST-2).  Paper: arXiv:2507.20274, `3_5`: `(int_K-L_ST)`
(`3_5:136`), the drift `(eq_L-Keee)` (`3_5:73-104`), `DefTHUST`, `Sol_CalL`, `lem:DIfREP`
(`3_5:218-240`, for the tails' shape only).  No RBM2D or RBM1D counterpart of the pin exists (RBM2D
`c9a24cf` has no `STGridRepN`); the file copies, with the prefix `difRep_`, the private helpers of
the merged `Induction/GridDriftN` (T2111, `14137ce`) and `Induction/GridEnvelopeN` (T2153,
`a438a51`), themselves ports of RBM2D `Induction/GridDriftN.lean` and `Induction/GridEnvelopeN.lean`
at `c9a24cf` (`GDN:58-253, 257-439`; `GEN:161-282`).

## Main results (namespace `RBM.Ind`)

* §1 the vocabulary `difRepMartN` (`Mart`), `difRepRemN` (`Rem`), `GridRepRemNAt` (clauses (i)-(ii)
  of `STGridRepNAt` for them), `GridRepTailNAt` (clause (iii)) and `GridRepWTailNAt` (clause (iv)).
* §2 `difRep_identity` (the split is a pathwise identity, for every `k`) and `difRepMartN_succ_sub`.
* §3 the interface lemmas of ST2-13: `difRep_Ugen_step_le` (one step of `𝒰`, the public copy of
  `gdn_Ugen_step_le`), `difRep_flow_bounds` (the flow bulk, `t₀ < 1`, `η_u` between `N^{-1+ε}/16`
  and `1 - u`).
* §4 `gridRepRemN_holds`: `‖Rem_k‖ ≤ N^{m+9} Δ^{1/2}` for all `k ≤ K`, `C₀ = m + 9`, `CK = 8m + 20`.
* §5 the assembly `stGridRepNAt_of_parts`, `stGridRepN_of_tails`, `stGridMartAt_of_parts2`,
  `stGridMart_of_tail`.
* §6 compiled nonempty instances at `d = 3`.

`3 ≤ d` enters only through `stKbound_of_flow` (`Loop/KLFinal.lean:302`, DECISIONS §36), hence
only in `gridRepRemN_holds`, `stGridRepN_of_tails`, `stGridMart_of_tail`.

Every unpinned helper is `private` with the prefix `difRep_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The vocabulary -/

/-- **The martingale part** `Mart_k = Σ_{j<k} ξ_{j+1}`, `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]` (the merged
`martIncN`), of the grid observable `A_j = (𝓛 - 𝒦)^{(m)}_{u_j,σ,a}(H_j)` at the label pair `i = (σ, a)`; the
type is that of `Mart` in `STGridRepNAt`. -/
def difRepMartN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k, martIncN sz E s t K n j i.1 ω i.2

/-- **The remainder** `Rem_k = Σ_{j<k} (𝔼[A_{j+1} | F_j] - A_j - Δ Drift_j)`, `Drift_j` the merged general-`n`
drift `STgDriftN` (`(eq_L-Keee)`, `3_5:73`) at `(u_j, H_j)`; the type is that of `Rem` in `STGridRepNAt`. -/
def difRepRemN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
    (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ∑ j ∈ Finset.range k,
    ((pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) i.1 ω' i.2 | filt sz j] ω -
      AvecN sz E s t K n j i.1 ω i.2 -
      ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (E n) i.1 i.2 j ω)

/-- **Clauses (i)-(ii) of `STGridRepNAt d m C₀`** (`Step2Defs.lean:817`) for `Mart = difRepMartN`,
`Rem = difRepRemN`, with their own grid exponent: the decomposition, and `‖Rem_k‖ ≤ N^{C₀} Δ^{1/2}` a.e.,
for all `k ≤ K` at once, eventually in `n`. -/
def GridRepRemNAt (d m : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))), ∀ᵐ ω ∂(pathP sz),
              ∀ k, k ≤ K n →
                STgAN sz s t K n (STflowE z n) i.1 i.2 k ω =
                  STgAN sz s t K n (STflowE z n) i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftN sz s t K n (STflowE z n) i.1 i.2 j ω +
                    difRepRemN sz (STflowE z) s t K n i k ω +
                    difRepMartN sz (STflowE z) s t K n i k ω) ∧
            (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                ‖difRepRemN sz (STflowE z) s t K n i k ω‖ ≤
                  ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n))

/-- **Clause (iii) of `STGridRepNAt`** (`(aaswtghh)` with Azuma + Doob, `3_5:220`) for `Mart = difRepMartN`:
the plain martingale tail, for all `k ≤ K` at once.  Owed to ST2-13. -/
def GridRepTailNAt (d m : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              pathP sz {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeM sz n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                        i.1 i.2 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                  ‖difRepMartN sz (STflowE z) s t K n i k ω‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **Clause (iv) of `STGridRepNAt`** (`(alu9_STime)` with Azuma + Doob, `3_5:229`) for `Mart = difRepMartN`:
the `𝒰`-weighted martingale tail, for all `k ≤ K` at once.  Owed to ST2-13. -/
def GridRepWTailNAt (d m : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              pathP sz {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeUM sz n (STflowE z n) (gridTime s t K n j) (gridTime s t K n k)
                        (pathH sz s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                        (1 / 2 : ℝ) <
                  ‖∑ j ∈ Finset.range k,
                    UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i'))
                      (gridTime s t K n j) (gridTime s t K n k)
                      (fun b => difRepMartN sz (STflowE z) s t K n (i.1, b) (j + 1) ω -
                        difRepMartN sz (STflowE z) s t K n (i.1, b) j ω) i.2‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-! ## 2. The identity -/

/-- Target 2, `difRep_identity`: the split is an identity, pathwise, for every `k` and `ω`. -/
theorem difRep_identity :
    ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
      (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (k : ℕ) (ω : PathΩ sz),
      STgAN sz s t K n (E n) i.1 i.2 k ω =
        STgAN sz s t K n (E n) i.1 i.2 0 ω +
          ((gridStep s t K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDriftN sz s t K n (E n) i.1 i.2 j ω +
          difRepRemN sz E s t K n i k ω + difRepMartN sz E s t K n i k ω := by
  intro d sz E s t K m n i k ω
  have hA : ∀ j, STgAN sz s t K n (E n) i.1 i.2 j ω = AvecN sz E s t K n j i.1 ω i.2 :=
    fun j => (STLKM_eq_STLKIM sz n (E n) _ _ i.1 i.2).symm
  induction k with
  | zero => simp [difRepRemN, difRepMartN]
  | succ k ih =>
      have hstep : STgAN sz s t K n (E n) i.1 i.2 (k + 1) ω - STgAN sz s t K n (E n) i.1 i.2 k ω =
          ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (E n) i.1 i.2 k ω +
            ((pathP sz)[fun ω' => AvecN sz E s t K n (k + 1) i.1 ω' i.2 | filt sz k] ω -
              AvecN sz E s t K n k i.1 ω i.2 -
              ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (E n) i.1 i.2 k ω) +
            martIncN sz E s t K n k i.1 ω i.2 := by
        rw [hA, hA]
        simp only [martIncN]
        ring
      rw [difRepRemN, difRepMartN, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      rw [difRepRemN, difRepMartN] at ih
      linear_combination ih + hstep

/-- Target 2, `difRepMartN_succ_sub`: the increments of `difRepMartN` are the merged `martIncN`. -/
theorem difRepMartN_succ_sub :
    ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) {m : ℕ} (n : ℕ)
      (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) (j : ℕ) (ω : PathΩ sz),
      difRepMartN sz E s t K n i (j + 1) ω - difRepMartN sz E s t K n i j ω =
        martIncN sz E s t K n j i.1 ω i.2 := by
  intro d sz E s t K m n i j ω
  rw [difRepMartN, difRepMartN, Finset.sum_range_succ]
  ring

/-! ## 3. Interface lemmas for ST2-13

Copies (renamed to the prefix `difRep_`) of the private helpers of the merged `Induction/GridDriftN.lean`
(T2111, `14137ce`): lines 73-268 (`difRep_Tens`, `difRep_Gen`, the row lemmas, `difRep_tens_step_le`) and 295-502
(`difRep_sum_norm_row_le_opNorm` ... `difRep_Ugen_step_aux`), ports of RBM2D `Induction/GridDriftN.lean:58-253, 257-439`
at `c9a24cf` (`difRep_tens_step_le` `:189`, `difRep_Ugen_step_aux` `:408`). -/

section TensorStep

variable {d L : ℕ} [NeZero L]

/-- `(⊗_i U_i) A` at `x`: `Σ_y (Π_i U_i(x_i, y_i)) A(y)`. -/
private def difRep_Tens {k : ℕ} (U : Fin k → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin k → Zd d L) → ℂ)
    (x : Fin k → Zd d L) : ℂ :=
  ∑ y : Fin k → Zd d L, (∏ i, U i (x i) (y i)) * A y

/-- `(Σ_i (1 ⊗ ⋯ ⊗ G_i ⊗ ⋯ ⊗ 1)) A` at `x`. -/
private def difRep_Gen {k : ℕ} (G : Fin k → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin k → Zd d L) → ℂ)
    (x : Fin k → Zd d L) : ℂ :=
  ∑ i : Fin k, ∑ c : Zd d L, G i (x i) c * A (Function.update x i c)

private theorem difRep_Tens_zero (U : Fin 0 → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin 0 → Zd d L) → ℂ)
    (x : Fin 0 → Zd d L) : difRep_Tens U A x = A x := by
  unfold difRep_Tens
  rw [Finset.sum_eq_single x (fun y _ hy => absurd (Subsingleton.elim y x) hy)
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

private theorem difRep_Gen_zero (G : Fin 0 → Matrix (Zd d L) (Zd d L) ℂ) (A : (Fin 0 → Zd d L) → ℂ)
    (x : Fin 0 → Zd d L) : difRep_Gen G A x = 0 := by
  simp [difRep_Gen]

private theorem difRep_Tens_succ {k : ℕ} (U : Fin (k + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin (k + 1) → Zd d L) → ℂ) (x : Fin (k + 1) → Zd d L) :
    difRep_Tens U A x = ∑ y0 : Zd d L, U 0 (x 0) y0 *
      difRep_Tens (fun i : Fin k => U i.succ) (fun y' => A (Fin.cons y0 y')) (Fin.tail x) := by
  unfold difRep_Tens
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Zd d L)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail, mul_assoc]

private theorem difRep_Gen_succ {k : ℕ} (G : Fin (k + 1) → Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin (k + 1) → Zd d L) → ℂ) (x : Fin (k + 1) → Zd d L) :
    difRep_Gen G A x = ∑ c : Zd d L, G 0 (x 0) c * A (Fin.cons c (Fin.tail x)) +
      difRep_Gen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x) := by
  unfold difRep_Gen
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
private theorem difRep_row_mul {P : Matrix (Zd d L) (Zd d L) ℂ} {r m : ℝ}
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
private theorem difRep_row_one_add {e : Matrix (Zd d L) (Zd d L) ℂ} {a : ℝ}
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
private theorem difRep_one_add_mul (e : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) (f : Zd d L → ℂ) :
    ∑ c : Zd d L, (1 + e) x c * f c = f x + ∑ c : Zd d L, e x c * f c := by
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

/-- The first-order tensor bound: `‖(⊗U_i) A - A‖ ≤ ((1+a)^k - 1) M`. -/
private theorem difRep_tens_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ (k : ℕ) (U : Fin k → Matrix (Zd d L) (Zd d L) ℂ),
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1) x c‖ ≤ a) →
      ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖difRep_Tens U A x - A x‖ ≤ ((1 + a) ^ k - 1) * M := by
  intro k
  induction k with
  | zero =>
      intro U _ A M _ x
      rw [difRep_Tens_zero]
      simp
  | succ k ih =>
      intro U hU A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      have hpow : 1 ≤ (1 + a) ^ k := one_le_pow₀ (by linarith)
      set e : Matrix (Zd d L) (Zd d L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      have hrow : ∀ x' : Zd d L, ∑ c : Zd d L, ‖U 0 x' c‖ ≤ 1 + a := by
        intro x'; rw [hU0]; exact difRep_row_one_add (fun x'' => hU 0 x'') x'
      set T : Zd d L → ℂ := fun y0 => difRep_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Zd d L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        ih (fun i => U i.succ) (fun i x' => hU i.succ x') (fun y' => A (Fin.cons y0 y')) M
          (fun y' => hA _) (Fin.tail x)
      have hsplit : difRep_Tens U A x - A x =
          ∑ c : Zd d L, U 0 (x 0) c * (T c - Y c) + ∑ c : Zd d L, e (x 0) c * Y c := by
        rw [difRep_Tens_succ, hAx]
        have h1 : ∑ c : Zd d L, U 0 (x 0) c * T c =
            ∑ c : Zd d L, U 0 (x 0) c * (T c - Y c) + ∑ c : Zd d L, U 0 (x 0) c * Y c := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
        have h2 : ∑ c : Zd d L, U 0 (x 0) c * Y c = Y (x 0) + ∑ c : Zd d L, e (x 0) c * Y c := by
          rw [hU0]; exact difRep_one_add_mul e (x 0) Y
        rw [h1, h2]
        ring
      rw [hsplit]
      have hb1 : ‖∑ c : Zd d L, U 0 (x 0) c * (T c - Y c)‖ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) :=
        difRep_row_mul hrow (x 0) hTY
      have hb2 : ‖∑ c : Zd d L, e (x 0) c * Y c‖ ≤ a * M :=
        difRep_row_mul (fun x' => hU 0 x') (x 0) (fun c => hA _)
      calc _ ≤ ‖∑ c : Zd d L, U 0 (x 0) c * (T c - Y c)‖ + ‖∑ c : Zd d L, e (x 0) c * Y c‖ :=
            norm_add_le _ _
        _ ≤ (1 + a) * (((1 + a) ^ k - 1) * M) + a * M := add_le_add hb1 hb2
        _ = ((1 + a) ^ (k + 1) - 1) * M := by ring

/-- The second-order tensor bound: with `‖(U_i - 1)‖_rows ≤ a`, `‖(U_i - 1 - G_i)‖_rows ≤ b`,
`‖(⊗U_i) A - A - (Σ_i G_i) A‖ ≤ (k b + (1+a)^k - 1 - k a) M`. -/
private theorem difRep_tens_step_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ (k : ℕ) (U G : Fin k → Matrix (Zd d L) (Zd d L) ℂ),
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1) x c‖ ≤ a) →
      (∀ i x, ∑ c : Zd d L, ‖(U i - 1 - G i) x c‖ ≤ b) →
      ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) → ∀ x,
        ‖difRep_Tens U A x - A x - difRep_Gen G A x‖ ≤ ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M := by
  intro k
  induction k with
  | zero =>
      intro U G _ _ A M _ x
      rw [difRep_Tens_zero, difRep_Gen_zero]
      simp
  | succ k ih =>
      intro U G hU hG A M hA x
      have hM : 0 ≤ M := (norm_nonneg _).trans (hA x)
      set e : Matrix (Zd d L) (Zd d L) ℂ := U 0 - 1 with he
      have hU0 : U 0 = 1 + e := by rw [he]; abel
      set T : Zd d L → ℂ := fun y0 => difRep_Tens (fun i : Fin k => U i.succ)
        (fun y' => A (Fin.cons y0 y')) (Fin.tail x) with hT
      set Y : Zd d L → ℂ := fun y0 => A (Fin.cons y0 (Fin.tail x)) with hY
      have hAx : A x = Y (x 0) := by simp [hY]
      have hTY : ∀ y0, ‖T y0 - Y y0‖ ≤ ((1 + a) ^ k - 1) * M := fun y0 =>
        difRep_tens_sub_le ha k (fun i => U i.succ) (fun i x' => hU i.succ x')
          (fun y' => A (Fin.cons y0 y')) M (fun y' => hA _) (Fin.tail x)
      have hIH : ‖T (x 0) - Y (x 0) - difRep_Gen (fun i : Fin k => G i.succ)
          (fun y' => A (Fin.cons (x 0) y')) (Fin.tail x)‖ ≤
          ((k : ℝ) * b + ((1 + a) ^ k - 1 - k * a)) * M :=
        ih (fun i => U i.succ) (fun i => G i.succ) (fun i x' => hU i.succ x')
          (fun i x' => hG i.succ x') (fun y' => A (Fin.cons (x 0) y')) M (fun y' => hA _)
          (Fin.tail x)
      set g' : ℂ := difRep_Gen (fun i : Fin k => G i.succ) (fun y' => A (Fin.cons (x 0) y'))
        (Fin.tail x) with hg'
      have hsplit : difRep_Tens U A x - A x - difRep_Gen G A x =
          (T (x 0) - Y (x 0) - g') + ∑ c : Zd d L, e (x 0) c * (T c - Y c) +
            ∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c := by
        rw [difRep_Tens_succ, difRep_Gen_succ, hAx]
        have h1 : ∑ c : Zd d L, U 0 (x 0) c * T c =
            T (x 0) + ∑ c : Zd d L, e (x 0) c * (T c - Y c) + ∑ c : Zd d L, e (x 0) c * Y c := by
          rw [hU0, difRep_one_add_mul, add_assoc, ← Finset.sum_add_distrib]
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
        difRep_row_mul (fun x' => hU 0 x') (x 0) hTY
      have hb3 : ‖∑ c : Zd d L, (U 0 - 1 - G 0) (x 0) c * Y c‖ ≤ b * M :=
        difRep_row_mul (fun x' => hG 0 x') (x 0) (fun c => hA _)
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
private theorem difRep_sum_norm_row_le_opNorm (M : Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L) :
    ∑ c : Zd d L, ‖M x c‖ ≤ ‖M‖ := by
  have h : ∑ c : Zd d L, ‖M x c‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j : Zd d L, ‖M i j‖₊) (Finset.mem_univ x)
  have h' : ((∑ c : Zd d L, ‖M x c‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa using h'

/-- `‖Θ_z‖ ≤ (1 - ‖z‖)⁻¹` for complex `z`, `‖z‖ < 1` (copied from the private
`norm_Theta_le_of_lt` of `Path/UBounds.lean`; merged `norm_Theta_le` at `z = ‖z‖ · (z/‖z‖)`). -/
private theorem difRep_norm_Theta_le_of_lt (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) :
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
private theorem difRep_row_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} {s : ℝ}
    (hsξ : ‖(s : ℂ) * ξ‖ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ ≤ ‖ξ‖ * (1 - ‖(s : ℂ) * ξ‖)⁻¹ := by
  have hentry : ∀ c : Zd d L, ‖thetaGenMat d L g ξ s x c‖ =
      ‖ξ‖ * ‖(SB d L g * Theta d L g ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((difRep_sum_norm_row_le_opNorm _ x).trans ?_) (norm_nonneg _)
  calc ‖SB d L g * Theta d L g ((s : ℂ) * ξ)‖ ≤ ‖SB d L g‖ * ‖Theta d L g ((s : ℂ) * ξ)‖ :=
      norm_mul_le _ _
    _ = ‖Theta d L g ((s : ℂ) * ξ)‖ := by rw [norm_SB d L g hL, one_mul]
    _ ≤ (1 - ‖(s : ℂ) * ξ‖)⁻¹ := difRep_norm_Theta_le_of_lt hL hsξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u` (copied from the
private `sum_norm_thetaGenMat_diff_row_le` of `Path/UBounds.lean`; resolvent identity
`Theta_sub_Theta`). -/
private theorem difRep_row_thetaGenMat_diff (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ} (hΔ : 0 ≤ Δ)
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
  refine mul_le_mul_of_nonneg_left ((difRep_sum_norm_row_le_opNorm _ x).trans ?_) (by positivity)
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
        mul_le_mul (difRep_norm_Theta_le_of_lt hL hd) (difRep_norm_Theta_le_of_lt hL hu)
          (norm_nonneg _) (inv_nonneg.mpr (by linarith))

/-- `‖(w : ℂ) ξ‖ = w` for `‖ξ‖ = 1`, `0 ≤ w`. -/
private theorem difRep_norm_real_mul {ξ : ℂ} (hξ : ‖ξ‖ = 1) {w : ℝ} (hw : 0 ≤ w) :
    ‖(w : ℂ) * ξ‖ = w := by
  rw [norm_mul, hξ, mul_one, Complex.norm_of_nonneg hw]

/-- `(1 - vξS)Θ_{wξ} = 1 + (w - v) ξ S Θ_{wξ}`, i.e. `𝒰_{u,u+Δ} - 1 = Δ · (generator at u+Δ)`
(`def_Ustz_2`, `3_5`). -/
private theorem difRep_ukerMat_sub_one (hL : 3 ≤ L) {ξ : ℂ} {u Δ : ℝ}
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
private theorem difRep_row_U (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(uKer d L g ξ u (u + Δ) - 1) x c‖ ≤ Δ * (1 - (u + Δ))⁻¹ := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [difRep_norm_real_mul hξ (by linarith)]; exact hv
  rw [difRep_ukerMat_sub_one hL hd]
  have hentry : ∀ c : Zd d L, ‖((Δ : ℂ) • thetaGenMat d L g ξ (u + Δ)) x c‖ =
      Δ * ‖thetaGenMat d L g ξ (u + Δ) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hΔ
  have := difRep_row_thetaGenMat (g := g) hL hd x
  rwa [hξ, difRep_norm_real_mul hξ (by linarith), one_mul] at this

/-- Row sums of `𝒰_{u,u+Δ} - 1 - Δ (generator at u)` are `≤ Δ² (1-(u+Δ))⁻²` for `‖ξ‖ = 1`. -/
private theorem difRep_row_UG (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ} (hu0 : 0 ≤ u)
    (hΔ : 0 ≤ Δ) (hv : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(uKer d L g ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat d L g ξ u) x c‖ ≤
      Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by
  have hd : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := by
    rw [difRep_norm_real_mul hξ (by linarith)]; exact hv
  have hu : ‖(u : ℂ) * ξ‖ < 1 := by
    rw [difRep_norm_real_mul hξ hu0]; linarith
  have hM : uKer d L g ξ u (u + Δ) - 1 - (Δ : ℂ) • thetaGenMat d L g ξ u =
      (Δ : ℂ) • (thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) := by
    rw [difRep_ukerMat_sub_one hL hd, smul_sub]
  rw [hM]
  have hentry : ∀ c : Zd d L, ‖((Δ : ℂ) • (thetaGenMat d L g ξ (u + Δ) -
      thetaGenMat d L g ξ u)) x c‖ =
      Δ * ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖ := by
    intro c
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ]
  simp_rw [hentry]
  rw [← Finset.mul_sum]
  have h1 := difRep_row_thetaGenMat_diff (g := g) hL hΔ hu hd x
  rw [hξ, difRep_norm_real_mul hξ (by linarith), difRep_norm_real_mul hξ hu0] at h1
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβu : (1 - u)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hβ0 (by linarith)
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  calc Δ * ∑ c : Zd d L, ‖(thetaGenMat d L g ξ (u + Δ) - thetaGenMat d L g ξ u) x c‖
      ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹)) :=
        mul_le_mul_of_nonneg_left h1 hΔ
    _ ≤ Δ * (Δ * 1 ^ 2 * ((1 - (u + Δ))⁻¹ * (1 - (u + Δ))⁻¹)) := by gcongr
    _ = Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2 := by ring

/-- The generator kernel of `ThetaN` is `thetaGenMat`: `(μ S) Θ_{tμ} = μ (S Θ_{tμ})`. -/
private theorem difRep_thetaKer_eq (μ : ℂ) (t : ℝ) :
    thetaKer d L g μ t = thetaGenMat d L g μ t := by
  unfold thetaKer thetaGenMat
  rw [Matrix.smul_mul]

/-- **One step of `𝒰`** (RBM1D `Uker_step_n`, `Gauss/GridHierarchyN.lean:698` at `c06b103`;
RBM2D `gdn_Ugen_step_le`, `GDN:408`, in the `Ugen`/`ThetaN` vocabulary): for `‖A‖_max ≤ M`,
`‖𝒰_{u,u+Δ,σ} A - A - Δ ϴ_{u,σ} A‖ ≤ uStepC k Δ (u+Δ) M`. -/
private theorem difRep_Ugen_step_aux (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hv : u + Δ < 1)
    (A : (Fin k → Zd d L) → ℂ) (M : ℝ) (hA : ∀ y, ‖A y‖ ≤ M) (x : Fin k → Zd d L) :
    ‖Ugen d L g E σ u (u + Δ) A x - A x -
        (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x‖ ≤
      uStepC k Δ (u + Δ) * M := by
  have hβ0 : 0 < 1 - (u + Δ) := by linarith
  have hβ1 : 0 ≤ (1 - (u + Δ))⁻¹ := inv_nonneg.mpr hβ0.le
  have hedge : ∀ i : Fin k, ‖cycProd (fun i => mSigma E (σ i)) i‖ = 1 := fun i =>
    norm_cycProd (fun i => norm_mSigma hE (σ i)) i
  have key := difRep_tens_step_le (d := d) (L := L) (a := Δ * (1 - (u + Δ))⁻¹)
    (b := Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2) (mul_nonneg hΔ hβ1) (by positivity) k
    (fun i : Fin k => uKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (u + Δ))
    (fun i : Fin k => (Δ : ℂ) • thetaGenMat d L g (cycProd (fun i => mSigma E (σ i)) i) u)
    (fun i x' => difRep_row_U hL (hedge i) hu0 hΔ hv x')
    (fun i x' => difRep_row_UG hL (hedge i) hu0 hΔ hv x') A M hA x
  have hT : difRep_Tens (fun i : Fin k =>
      uKer d L g (cycProd (fun i => mSigma E (σ i)) i) u (u + Δ)) A x =
      Ugen d L g E σ u (u + Δ) A x := rfl
  have hG : difRep_Gen (fun i : Fin k =>
      (Δ : ℂ) • thetaGenMat d L g (cycProd (fun i => mSigma E (σ i)) i) u) A x =
      (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x := by
    unfold difRep_Gen ThetaN
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, difRep_thetaKer_eq]
    ring
  rw [hT, hG] at key
  refine key.trans (le_of_eq ?_)
  unfold uStepC
  ring

end UStep

/-- Target 3, `difRep_Ugen_step_le`: one step of `𝒰` (the statement of the private `gdn_Ugen_step_le`,
`GridDriftN.lean:468`, made public). -/
theorem difRep_Ugen_step_le :
    ∀ (d L : ℕ) [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 → ∀ {k : ℕ} (σ : Fin k → Bool) {u Δ : ℝ},
      0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ (A : (Fin k → Zd d L) → ℂ) (M : ℝ), (∀ y, ‖A y‖ ≤ M) →
        ∀ x : Fin k → Zd d L,
          ‖Ugen d L g E σ u (u + Δ) A x - A x -
              (Δ : ℂ) * ThetaN d L g (fun i => mSigma E (σ i)) u A x‖ ≤
            uStepC k Δ (u + Δ) * M := by
  intro d L _ g hL E hE k σ u Δ hu0 hΔ hv A M hA x
  exact difRep_Ugen_step_aux hL hE σ hu0 hΔ hv A M hA x

/-- Target 3, `difRep_flow_bounds`: the flow energy is in the bulk, `t₀ < 1`, and below `t₀` the
spectral height is `≥ N^{-1+ε}/16` and `≤ 1 - u` (Lemma 2.8, `(2.40)`). -/
theorem difRep_flow_bounds :
    ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ {z : ℕ → ℂ}, STFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) {u : ℝ}, u ≤ lemT (z n) →
        |STflowE z n| ≤ 2 - κ ∧ lemT (z n) < 1 ∧
          ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 ≤ etaT (STflowE z n) u ∧
          etaT (STflowE z n) u ≤ 1 - u := by
  intro d sz κ ε 𝔠 𝔡 hκ z hz n u hu
  have h := hz.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h.2.1
  obtain ⟨hE, -, hz16, -⟩ := lemma28_quant hκ him h.2.2 h.1
  have hT1 : lemT (z n) < 1 := lemT_lt_one him
  have hE2 : |STflowE z n| < 2 := by
    have : |STflowE z n| ≤ 2 - κ := hE
    linarith
  refine ⟨hE, hT1, ?_, ?_⟩
  · have h1 : etaT (STflowE z n) (lemT (z n)) ≤ etaT (STflowE z n) u :=
      Green.etaT_le_of_le hE2 hu
    have h2 : etaT (STflowE z n) (lemT (z n)) = (zt (lemE (z n)) (lemT (z n))).im :=
      etaT_eq_zt_im
    calc ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 ≤ (z n).im / 16 := by linarith [h.2.1]
      _ = (1 / 16 : ℝ) * (z n).im := by ring
      _ ≤ (zt (lemE (z n)) (lemT (z n))).im := hz16
      _ = etaT (STflowE z n) (lemT (z n)) := h2.symm
      _ ≤ etaT (STflowE z n) u := h1
  · have hu1 : 0 ≤ 1 - u := by linarith
    have hm : (mE (STflowE z n)).im ≤ 1 := by
      have h3 := Complex.im_le_norm (mE (STflowE z n))
      rwa [norm_mE hE2.le] at h3
    calc etaT (STflowE z n) u = (1 - u) * (mE (STflowE z n)).im := rfl
      _ ≤ (1 - u) * 1 := mul_le_mul_of_nonneg_left hm hu1
      _ = 1 - u := mul_one _

/-! ## 4. The remainder

Copies (renamed to the prefix `difRep_`) of `difRep_binom_rem` and `difRep_stepErr_le` of the merged
`Induction/GridEnvelopeN.lean:240-362` (T2153, `a438a51`), ports of RBM2D `Induction/GridEnvelopeN.lean:161-282`
(`GridEnvelopeN_binom_rem` `:161`, `GridEnvelopeN_stepErr_le` `:187`) at `c9a24cf`. -/

/-- `(1 + x)^k - 1 - k x ≤ k 2^k x²` for `0 ≤ x ≤ 1` (induction: `f_{k+1} = (1+x) f_k + k x²`). -/
private theorem difRep_binom_rem (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k - 1 - (k : ℝ) * x ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (1 + x) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * x =
        (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) + (k : ℝ) * x ^ 2 := by
      push_cast; ring
    rw [e]
    have hk2 : (k : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have hpk : (0 : ℝ) ≤ 2 ^ k := by positivity
    have h1 : (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) ≤
        (1 + x) * ((k : ℝ) * 2 ^ k * x ^ 2) := mul_le_mul_of_nonneg_left ih (by linarith)
    have hb : 0 ≤ (k : ℝ) * 2 ^ k * x ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_right hx1 hb
    have h3 := mul_le_mul_of_nonneg_right hk2 hx2
    have h4 := mul_nonneg hpk hx2
    push_cast
    rw [pow_succ (2 : ℝ) k]
    nlinarith [h1, h2, h3, h4]

/-- **The uniform one-step bound** (rows A, B, C): with `N = W^d L^d`, `H ≥ 1` a bound of
`(1 - v)^{-1}`, `H / c` a bound of `η_u^{-1}, η_v^{-1}`, `Y ≥ 1` (`= N^{τ_K}`) and `Δ H ≤ 1`, the
step error at `B_k = Y η_v^{-k}` is at most `Z₁ Δ^{3/2} + Z₂₃ Δ²`.  RBM2D `GridEnvelopeN_stepErr_le`
(`GEN:187`) with `W² L² = N ↦ W^d L^d = N`. -/
private theorem difRep_stepErr_le (d L W : ℕ) (E : ℝ) (k : ℕ) (u v Δ N H Y c : ℝ)
    (hN1 : 1 ≤ N) (hWL : (W : ℝ) ^ d * (L : ℝ) ^ d = N) (hW : (1 : ℝ) ≤ W)
    (hH : 1 ≤ H) (hY : 1 ≤ Y) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hΔ0 : 0 ≤ Δ) (hΔH : Δ * H ≤ 1)
    (hηu0 : 0 < etaT E u) (hηv0 : 0 < etaT E v)
    (hηu : (etaT E u)⁻¹ ≤ H / c) (hηv : (etaT E v)⁻¹ ≤ H / c)
    (hv1 : 0 < 1 - v) (hv : (1 - v)⁻¹ ≤ H) :
    stepErrN d L W E k u v Δ (Y * (etaT E v)⁻¹ ^ k) ≤
      16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) +
        ((2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * (Y * (H / c) ^ k) ^ 4 +
          2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * (Y * (H / c) ^ k)) * Δ ^ 2 := by
  unfold stepErrN
  set B := Y * (H / c) ^ k with hB
  have hHc : 1 ≤ H / c := by rw [le_div_iff₀ hc0]; linarith
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hY (one_le_pow₀ hHc)
  have hηu' : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu0.le
  have hηv' : 0 ≤ (etaT E v)⁻¹ := inv_nonneg.2 hηv0.le
  have hBk0 : 0 ≤ Y * (etaT E v)⁻¹ ^ k := mul_nonneg (by linarith) (pow_nonneg hηv' _)
  have hBk : Y * (etaT E v)⁻¹ ^ k ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηv' hηv k)
    (by linarith)
  set Bk := Y * (etaT E v)⁻¹ ^ k with hBkdef
  -- term A
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hcast : ((((W * L) ^ d : ℕ)) : ℝ) = N := by
    push_cast; rw [← hWL]; ring
  have hone : 1 + (etaT E v)⁻¹ ≤ (1 + 1 / c) * H := by
    have : (etaT E v)⁻¹ ≤ H / c := hηv
    have h2 : H / c = (1 / c) * H := by ring
    linarith
  have hA : envConst d L W E k v ≤ 16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) := by
    unfold envConst
    rw [hcast]
    have hbase : 0 ≤ 1 + (etaT E v)⁻¹ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hone _) (by positivity)
  have hA' : envConst d L W E k v * Δ ^ ((3 : ℝ) / 2) ≤
      16 * ((k : ℝ) + 3) ^ 4 * N ^ 4 * ((1 + 1 / c) * H) ^ (k + 4) * Δ ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hΔ0 _)
  -- term B
  have hk : kStepC d L W k Bk = 2 * (k : ℝ) ^ 4 * N ^ 2 * Bk ^ 3 + (k : ℝ) ^ 6 * N ^ 3 * Bk ^ 4 := by
    unfold kStepC
    rw [← hWL]; ring
  have hN23 : N ^ 2 ≤ N ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
  have hB3 : Bk ^ 3 ≤ B ^ 4 :=
    (pow_le_pow_left₀ hBk0 hBk 3).trans (pow_le_pow_right₀ hB1 (by norm_num))
  have hB4 : Bk ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hBk0 hBk 4
  have hkB : kStepC d L W k Bk ≤ (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * B ^ 4 := by
    rw [hk]
    have hk4 : (0 : ℝ) ≤ (k : ℝ) ^ 4 := by positivity
    have hk6 : (0 : ℝ) ≤ (k : ℝ) ^ 6 := by positivity
    have e1 : 2 * (k : ℝ) ^ 4 * N ^ 2 * Bk ^ 3 ≤ 2 * (k : ℝ) ^ 4 * N ^ 3 * B ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hN23 (by positivity)) hB3 (by positivity)
        (by positivity)
    have e2 : (k : ℝ) ^ 6 * N ^ 3 * Bk ^ 4 ≤ (k : ℝ) ^ 6 * N ^ 3 * B ^ 4 :=
      mul_le_mul_of_nonneg_left hB4 (by positivity)
    linarith [e1, e2]
  have hB' : kStepC d L W k Bk * Δ ^ 2 ≤
      (2 * (k : ℝ) ^ 4 + (k : ℝ) ^ 6) * N ^ 3 * B ^ 4 * Δ ^ 2 :=
    mul_le_mul_of_nonneg_right hkB (sq_nonneg Δ)
  -- term C
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 (inv_nonneg.2 hv1.le)
  have hxH : Δ * (1 - v)⁻¹ ≤ Δ * H := mul_le_mul_of_nonneg_left hv hΔ0
  have hx1 : Δ * (1 - v)⁻¹ ≤ 1 := hxH.trans hΔH
  have hrem := difRep_binom_rem (Δ * (1 - v)⁻¹) hx0 hx1 k
  have hx2 : (Δ * (1 - v)⁻¹) ^ 2 ≤ Δ ^ 2 * H ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxH 2 |>.trans (by rw [mul_pow])
  have hiv2 : (1 - v)⁻¹ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hv1.le) hv 2
  have hU : uStepC k Δ v ≤ ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2 := by
    unfold uStepC
    have e1 : (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 ≤ (k : ℝ) * Δ ^ 2 * H ^ 2 :=
      mul_le_mul_of_nonneg_left hiv2 (by positivity)
    have e2 : (k : ℝ) * 2 ^ k * (Δ * (1 - v)⁻¹) ^ 2 ≤ (k : ℝ) * 2 ^ k * (Δ ^ 2 * H ^ 2) :=
      mul_le_mul_of_nonneg_left hx2 (by positivity)
    linarith [hrem, e1, e2]
  have hWd0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := inv_nonneg.2 (by positivity)
  have hbr0 : 0 ≤ (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk :=
    add_nonneg (mul_nonneg (pow_nonneg hηu' _) (pow_nonneg hWd0 _)) hBk0
  have hW1 : (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ 1 :=
    pow_le_one₀ hWd0 (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have hbr : (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk ≤ 2 * B := by
    have e1 : (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ B := by
      calc (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) ≤ (etaT E u)⁻¹ ^ k * 1 :=
            mul_le_mul_of_nonneg_left hW1 (pow_nonneg hηu' _)
        _ = (etaT E u)⁻¹ ^ k := mul_one _
        _ ≤ (H / c) ^ k := pow_le_pow_left₀ hηu' hηu k
        _ ≤ Y * (H / c) ^ k := by
          exact le_mul_of_one_le_left (by positivity) hY
    linarith
  have hC : uStepC k Δ v * ((etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk) ≤
      2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * B * Δ ^ 2 := by
    calc uStepC k Δ v * ((etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk)
        ≤ (((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2) * (2 * B) :=
          mul_le_mul hU hbr hbr0 (by positivity)
      _ = 2 * ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * B * Δ ^ 2 := by ring
  linarith [hA', hB', hC]

private theorem difRep_gridStep_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem difRep_gridTime_le {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hst : s n ≤ t n)
    (hK0 : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  have hΔ := difRep_gridStep_nonneg (s := s) (t := t) (K := K) hst
  have hj' : (j : ℝ) ≤ (K n : ℝ) := by exact_mod_cast hj
  have h := mul_le_mul_of_nonneg_right hj' hΔ
  have hlast := gridTime_last s t K n hK0
  unfold gridTime at hlast ⊢
  nlinarith

/-- `Z₁ = 16 (m+3)^4 N^4 (32 N)^{m+4}`: the coefficient of `Δ^{3/2}` (`c = 1`, `H = 16 N`). -/
private def difRep_Z1 (m : ℕ) (N : ℝ) : ℝ := 16 * ((m : ℝ) + 3) ^ 4 * N ^ 4 * (32 * N) ^ (m + 4)

/-- `Z₂`: the coefficient of `Δ²` (`B = N (16 N)^m`, `Y = N`, `H = 16 N`). -/
private def difRep_Z2 (m : ℕ) (N : ℝ) : ℝ :=
  (2 * (m : ℝ) ^ 4 + (m : ℝ) ^ 6) * N ^ 3 * (N * (16 * N) ^ m) ^ 4 +
    2 * ((m : ℝ) + (m : ℝ) * 2 ^ m) * (16 * N) ^ 2 * (N * (16 * N) ^ m)

private theorem difRep_Z1_nonneg (m : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ difRep_Z1 m N := by
  unfold difRep_Z1; positivity

private theorem difRep_Z2_nonneg (m : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ difRep_Z2 m N := by
  unfold difRep_Z2; positivity

/-- `uStepC k Δ v ≤ (k + k 2^k) H² Δ²` for `Δ H ≤ 1`, `(1 - v)⁻¹ ≤ H` (the `hU` block of
`difRep_stepErr_le`). -/
private theorem difRep_uStepC_le (k : ℕ) (Δ v H : ℝ) (hΔ0 : 0 ≤ Δ) (hΔH : Δ * H ≤ 1)
    (hv1 : 0 < 1 - v) (hv : (1 - v)⁻¹ ≤ H) :
    uStepC k Δ v ≤ ((k : ℝ) + (k : ℝ) * 2 ^ k) * H ^ 2 * Δ ^ 2 := by
  have hx0 : 0 ≤ Δ * (1 - v)⁻¹ := mul_nonneg hΔ0 (inv_nonneg.2 hv1.le)
  have hxH : Δ * (1 - v)⁻¹ ≤ Δ * H := mul_le_mul_of_nonneg_left hv hΔ0
  have hx1 : Δ * (1 - v)⁻¹ ≤ 1 := hxH.trans hΔH
  have hrem := difRep_binom_rem (Δ * (1 - v)⁻¹) hx0 hx1 k
  have hx2 : (Δ * (1 - v)⁻¹) ^ 2 ≤ Δ ^ 2 * H ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx0 hxH 2 |>.trans (by rw [mul_pow])
  have hiv2 : (1 - v)⁻¹ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hv1.le) hv 2
  unfold uStepC
  have e1 : (k : ℝ) * Δ ^ 2 * (1 - v)⁻¹ ^ 2 ≤ (k : ℝ) * Δ ^ 2 * H ^ 2 :=
    mul_le_mul_of_nonneg_left hiv2 (by positivity)
  have e2 : (k : ℝ) * 2 ^ k * (Δ * (1 - v)⁻¹) ^ 2 ≤ (k : ℝ) * 2 ^ k * (Δ ^ 2 * H ^ 2) :=
    mul_le_mul_of_nonneg_left hx2 (by positivity)
  linarith [hrem, e1, e2]

/-- **The per-step arithmetic**: the step error of `gridDriftN_envelope` at `B_k = N η_v^{-m}` plus the
`𝒰`-step remainder at `M = η_u^{-m} (W^{-d})^{m-1} + N η_t^{-m}` is `≤ Z₁ Δ^{3/2} + 2 Z₂ Δ²`
(`c = 1`, `H = 16 N`, `Y = N`). -/
private theorem difRep_step_arith (d L W : ℕ) (E : ℝ) (m : ℕ) (u v t Δ N : ℝ)
    (hN1 : 1 ≤ N) (hWL : (W : ℝ) ^ d * (L : ℝ) ^ d = N) (hW : (1 : ℝ) ≤ W)
    (hΔ0 : 0 ≤ Δ) (hΔH : Δ * (16 * N) ≤ 1)
    (hηu0 : 0 < etaT E u) (hηv0 : 0 < etaT E v) (hηt0 : 0 < etaT E t)
    (hηu : (etaT E u)⁻¹ ≤ 16 * N) (hηv : (etaT E v)⁻¹ ≤ 16 * N) (hηt : (etaT E t)⁻¹ ≤ 16 * N)
    (hv1 : 0 < 1 - v) (hv : (1 - v)⁻¹ ≤ 16 * N) :
    stepErrN d L W E m u v Δ (N * (etaT E v)⁻¹ ^ m) +
        uStepC m Δ v * ((etaT E u)⁻¹ ^ m * (((W : ℝ) ^ d)⁻¹) ^ (m - 1) + N * (etaT E t)⁻¹ ^ m) ≤
      difRep_Z1 m N * Δ ^ ((3 : ℝ) / 2) + 2 * difRep_Z2 m N * Δ ^ 2 := by
  have hH1 : (1 : ℝ) ≤ 16 * N := by linarith
  have h1 := difRep_stepErr_le d L W E m u v Δ N (16 * N) N 1 hN1 hWL hW hH1 hN1 one_pos le_rfl
    hΔ0 hΔH hηu0 hηv0 (by rwa [div_one]) (by rwa [div_one]) hv1 hv
  have e32 : (1 + 1 / (1 : ℝ)) * (16 * N) = 32 * N := by ring
  rw [e32, div_one] at h1
  have hU := difRep_uStepC_le m Δ v (16 * N) hΔ0 hΔH hv1 hv
  have hηu' : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 hηu0.le
  have hηt' : 0 ≤ (etaT E t)⁻¹ := inv_nonneg.2 hηt0.le
  have hB1 : 1 ≤ N * (16 * N) ^ m := one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hH1)
  have hWd0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := inv_nonneg.2 (by positivity)
  have hW1 : (((W : ℝ) ^ d)⁻¹) ^ (m - 1) ≤ 1 :=
    pow_le_one₀ hWd0 (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have hbr0 : 0 ≤ (etaT E u)⁻¹ ^ m * (((W : ℝ) ^ d)⁻¹) ^ (m - 1) + N * (etaT E t)⁻¹ ^ m :=
    add_nonneg (mul_nonneg (pow_nonneg hηu' _) (pow_nonneg hWd0 _))
      (mul_nonneg (by linarith) (pow_nonneg hηt' _))
  have hbr : (etaT E u)⁻¹ ^ m * (((W : ℝ) ^ d)⁻¹) ^ (m - 1) + N * (etaT E t)⁻¹ ^ m ≤
      2 * (N * (16 * N) ^ m) := by
    have e1 : (etaT E u)⁻¹ ^ m * (((W : ℝ) ^ d)⁻¹) ^ (m - 1) ≤ N * (16 * N) ^ m := by
      calc (etaT E u)⁻¹ ^ m * (((W : ℝ) ^ d)⁻¹) ^ (m - 1) ≤ (etaT E u)⁻¹ ^ m * 1 :=
            mul_le_mul_of_nonneg_left hW1 (pow_nonneg hηu' _)
        _ = (etaT E u)⁻¹ ^ m := mul_one _
        _ ≤ (16 * N) ^ m := pow_le_pow_left₀ hηu' hηu m
        _ ≤ N * (16 * N) ^ m := le_mul_of_one_le_left (by positivity) hN1
    have e2 : N * (etaT E t)⁻¹ ^ m ≤ N * (16 * N) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hηt' hηt m) (by linarith)
    linarith
  have hC : uStepC m Δ v * ((etaT E u)⁻¹ ^ m * (((W : ℝ) ^ d)⁻¹) ^ (m - 1) + N * (etaT E t)⁻¹ ^ m) ≤
      2 * ((m : ℝ) + (m : ℝ) * 2 ^ m) * (16 * N) ^ 2 * (N * (16 * N) ^ m) * Δ ^ 2 := by
    calc _ ≤ (((m : ℝ) + (m : ℝ) * 2 ^ m) * (16 * N) ^ 2 * Δ ^ 2) * (2 * (N * (16 * N) ^ m)) :=
          mul_le_mul hU hbr hbr0 (by positivity)
      _ = _ := by ring
  have hN0 : 0 ≤ N := by linarith
  have hTB : 0 ≤ (2 * (m : ℝ) ^ 4 + (m : ℝ) ^ 6) * N ^ 3 * (N * (16 * N) ^ m) ^ 4 * Δ ^ 2 := by
    positivity
  unfold difRep_Z1 difRep_Z2
  linarith [h1, hC, hTB]


section Remainder

variable {d : ℕ} (sz : Sizes d)

private theorem difRep_loopOf_wf {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem difRep_loopOf_length {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) :
    (loopOf σ a).length = k := by
  simp [loopOf, LoopIdx.length]

/-- `A_i = (𝓛 - 𝒦)_{u_i,σ}` along the walk is the loop of the block matrix minus `𝒦` (copy of the
private `gdn_AvecN_eq` of `Induction/GridDriftN.lean:709`). -/
private theorem difRep_AvecN_eq (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {k : ℕ}
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

/-- `‖𝓛_{u,σ,y}(H)‖ ≤ η_u^{-k} (W^{-d})^{k-1}` for the walk matrix (`(5.2)`). -/
private theorem difRep_norm_loopL_le (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) {E w : ℝ} (hE : |E| < 2)
    (hw : w < 1) (ω : PathΩ sz) {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (y : Fin k → Zd d (sz.L n)) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n i ω)) (zt E w)
        (loopOf σ y)‖ ≤
      (etaT E w)⁻¹ ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) := by
  have hη : 0 < etaT E w := etaT_pos hE hw
  have hz : etaT E w ≤ |(zt E w).im| := by
    rw [zt_im, abs_of_pos (mul_pos (sub_pos.2 hw) (mE_im_pos hE))]
    exact le_rfl
  have hl : (loopOf σ y).a.length = k := by simp [loopOf]
  have h := norm_gloop_le_of_le_abs_im
    (show (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n i ω)).IsHermitian from
      (pathH_isHermitian sz s t K n i ω).submatrix _) hη hz (loopOf σ y)
    (difRep_loopOf_wf σ y) (by rw [hl]; exact hk)
  rwa [hl] at h

private theorem difRep_size_cast (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

private theorem difRep_gridTime_nonneg {s t : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  have hΔ := difRep_gridStep_nonneg (s := s) (t := t) (K := K) hst
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

private theorem difRep_gridTime_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s t K n (j + 1) = gridTime s t K n j + gridStep s t K n := by
  unfold gridTime; push_cast; ring

private theorem difRep_K_mul_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    (K n : ℝ) * gridStep s t K n = t n - s n := by
  have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold gridStep
  field_simp

/-- For `u ≤ t₀`: `η_u > 0`, `η_u^{-1} ≤ 16 N`, `0 < 1 - u` and `(1 - u)^{-1} ≤ 16 N`. -/
private theorem difRep_eta_bounds {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu : u ≤ lemT (z n)) :
    0 < etaT (STflowE z n) u ∧ (etaT (STflowE z n) u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) ∧
      0 < 1 - u ∧ (1 - u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) := by
  obtain ⟨hE, hT1, hlow, hup⟩ := difRep_flow_bounds sz hκ hz n hu
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hpow : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have hη : ((sz.size n : ℕ) : ℝ)⁻¹ / 16 ≤ etaT (STflowE z n) u := by
    have := div_le_div_of_nonneg_right hpow (by norm_num : (0 : ℝ) ≤ 16)
    exact this.trans hlow
  have hηpos : 0 < etaT (STflowE z n) u :=
    lt_of_lt_of_le (div_pos (inv_pos.2 hN0) (by norm_num)) hη
  have hinv : (etaT (STflowE z n) u)⁻¹ ≤ 16 * ((sz.size n : ℕ) : ℝ) := by
    have h1 := inv_anti₀ (div_pos (inv_pos.2 hN0) (by norm_num)) hη
    have e : (((sz.size n : ℕ) : ℝ)⁻¹ / 16)⁻¹ = 16 * ((sz.size n : ℕ) : ℝ) := by
      field_simp
    rwa [e] at h1
  have h1u : 0 < 1 - u := lt_of_lt_of_le hηpos hup
  exact ⟨hηpos, hinv, h1u, (inv_anti₀ hηpos hup).trans hinv⟩

end Remainder

section RemainderStep

variable {d : ℕ} (sz : Sizes d)

/-- **One grid step of the remainder** (deterministic): given the a.e. step error of
`gridDriftN_envelope` at `(σ, ω)` and the `𝒦` envelope `‖𝒦_w‖ ≤ N η_{t}^{-m}` on `[0, t_n]`, the
summand `r_j = 𝔼[A_{j+1} | F_j] - A_j - Δ Drift_j` of `difRepRemN` has `‖r_j‖ ≤ Z₁ Δ^{3/2} + 2 Z₂ Δ²`:
`r_j = [predIncN_j - Δ S_j] + [𝒰_{u_j,u_{j+1},σ} A_j - A_j - Δ Θ_{u_j,σ} A_j]` (`S_j` the non-`Θ`
part of `STgDriftN`), the first bracket by `hω`, the second by `difRep_Ugen_step_le`. -/
private theorem difRep_step_le {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ lemT (z n)) (hK0 : ∀ n, K n ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) (n : ℕ)
    (hΔH : gridStep s t K n * (16 * ((sz.size n : ℕ) : ℝ)) ≤ 1)
    (hKw : ∀ w ∈ Set.Icc (0 : ℝ) (t n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length →
      J.length ≤ m →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (STflowE z n) w J‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (etaT (STflowE z n) (t n))⁻¹ ^ m)
    (σ : Fin m → Bool) (ω : PathΩ sz)
    (hω : ∀ j, j < K n → ∀ a : Fin m → Zd d (sz.L n),
      ‖predIncN sz (STflowE z) s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 m, sz.STksimLKM n (STflowE z n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))‖ ≤
        stepErrN d (sz.L n) (sz.W n) (STflowE z n) m (gridTime s t K n j)
          (gridTime s t K n (j + 1)) (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) *
            (etaT (STflowE z n) (gridTime s t K n (j + 1)))⁻¹ ^ m))
    (j : ℕ) (hj : j < K n) (a : Fin m → Zd d (sz.L n)) :
    ‖(pathP sz)[fun ω' => AvecN sz (STflowE z) s t K n (j + 1) σ ω' a | filt sz j] ω -
        AvecN sz (STflowE z) s t K n j σ ω a -
        ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (STflowE z n) σ a j ω‖ ≤
      difRep_Z1 m ((sz.size n : ℕ) : ℝ) * gridStep s t K n ^ ((3 : ℝ) / 2) +
        2 * difRep_Z2 m ((sz.size n : ℕ) : ℝ) * gridStep s t K n ^ 2 := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW : (1 : ℝ) ≤ sz.W n := by exact_mod_cast sz.W_pos n
  have hΔ0 := difRep_gridStep_nonneg (s := s) (t := t) (K := K) (hst n)
  have hu0 := difRep_gridTime_nonneg (K := K) (hs0 n) (hst n) j
  have hvsucc := difRep_gridTime_succ s t K n j
  have huj : gridTime s t K n j ≤ t n := difRep_gridTime_le (hst n) (hK0 n) hj.le
  have hvj : gridTime s t K n (j + 1) ≤ t n := difRep_gridTime_le (hst n) (hK0 n) hj
  obtain ⟨hE, hT1, -, -⟩ := difRep_flow_bounds sz hκ hz n (htT n)
  have hE2 : |STflowE z n| < 2 := by
    have : |STflowE z n| ≤ 2 - κ := hE
    linarith
  have hv1 : gridTime s t K n (j + 1) < 1 := lt_of_le_of_lt (hvj.trans (htT n)) hT1
  obtain ⟨hηu0, hηu, -, -⟩ := difRep_eta_bounds sz hκ hε hz n (huj.trans (htT n))
  obtain ⟨hηv0, hηv, hv0, hv⟩ := difRep_eta_bounds sz hκ hε hz n (hvj.trans (htT n))
  obtain ⟨hηt0, hηt, -, -⟩ := difRep_eta_bounds sz hκ hε hz n (htT n)
  have hu1 : gridTime s t K n j < 1 := by linarith [hvsucc, hΔ0, hv1]
  -- the sup bound of `A_j`
  have hA : ∀ y : Fin m → Zd d (sz.L n),
      ‖AvecN sz (STflowE z) s t K n j σ ω y‖ ≤
        (etaT (STflowE z n) (gridTime s t K n j))⁻¹ ^ m * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (m - 1) +
          ((sz.size n : ℕ) : ℝ) * (etaT (STflowE z n) (t n))⁻¹ ^ m := by
    intro y
    rw [difRep_AvecN_eq]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact difRep_norm_loopL_le sz s t K n j hE2 hu1 ω (by omega) σ y
    · have h := hKw (gridTime s t K n j) ⟨hu0, huj⟩ (loopOf σ y) (difRep_loopOf_wf σ y)
        (by rw [difRep_loopOf_length]; exact hm) (by rw [difRep_loopOf_length])
      rwa [Real.rpow_one] at h
  -- the `𝒰` step
  have hU := difRep_Ugen_step_le d (sz.L n) (sz.lam n) (sz.three_le_L n) hE2.le σ hu0 hΔ0
    (by rw [← hvsucc]; exact hv1) (AvecN sz (STflowE z) s t K n j σ ω) _ hA a
  rw [← hvsucc] at hU
  -- the identity `r_j = [P_j - Δ S_j] + [𝒰 A_j - A_j - Δ Θ A_j]`
  have hfun : (fun a' => sz.STLKIM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
      (KLloopOf d (sz.L n) σ a')) = AvecN sz (STflowE z) s t K n j σ ω :=
    funext fun a' => (STLKM_eq_STLKIM sz n _ _ _ σ a').symm
  have hdec : (pathP sz)[fun ω' => AvecN sz (STflowE z) s t K n (j + 1) σ ω' a | filt sz j] ω -
        AvecN sz (STflowE z) s t K n j σ ω a -
        ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (STflowE z n) σ a j ω =
      (predIncN sz (STflowE z) s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 m, sz.STksimLKM n (STflowE z n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))) +
        (Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ (gridTime s t K n j)
            (gridTime s t K n (j + 1)) (AvecN sz (STflowE z) s t K n j σ ω) a -
          AvecN sz (STflowE z) s t K n j σ ω a -
          (gridStep s t K n : ℂ) * ThetaN d (sz.L n) (sz.lam n)
            (fun i => mSigma (STflowE z n) (σ i)) (gridTime s t K n j)
            (AvecN sz (STflowE z) s t K n j σ ω) a) := by
    unfold STgDriftN predIncN
    rw [hfun]
    simp only [show KLloopOf d (sz.L n) σ a = loopOf σ a from rfl]
    ring
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  have h1 := hω j hj a
  have hN := difRep_step_arith d (sz.L n) (sz.W n) (STflowE z n) m (gridTime s t K n j)
    (gridTime s t K n (j + 1)) (t n) (gridStep s t K n) ((sz.size n : ℕ) : ℝ) hN1
    (difRep_size_cast sz n) hW hΔ0 hΔH hηu0 hηv0 hηt0 hηu hηv hηt hv0 hv
  rw [Real.rpow_one] at h1
  exact (add_le_add h1 hU).trans hN

end RemainderStep

/-- `c₁ = 16 (m+3)^4 32^{m+4}`: `Z₁ = c₁ N^{m+8}`. -/
private def difRep_c1 (m : ℕ) : ℝ := 16 * ((m : ℝ) + 3) ^ 4 * 32 ^ (m + 4)

/-- `c₂ = (2m⁴+m⁶) 16^{4m} + 2(m + m 2^m) 16^{m+2}`: `Z₂ ≤ c₂ N^{4m+7}`. -/
private def difRep_c2 (m : ℕ) : ℝ :=
  (2 * (m : ℝ) ^ 4 + (m : ℝ) ^ 6) * 16 ^ (4 * m) + 2 * ((m : ℝ) + (m : ℝ) * 2 ^ m) * 16 ^ (m + 2)

private theorem difRep_Z1_eq (m : ℕ) (N : ℝ) : difRep_Z1 m N = difRep_c1 m * N ^ (m + 8) := by
  unfold difRep_Z1 difRep_c1
  ring

private theorem difRep_Z2_le (m : ℕ) {N : ℝ} (hN1 : 1 ≤ N) :
    difRep_Z2 m N ≤ difRep_c2 m * N ^ (4 * m + 7) := by
  have h1 : (2 * (m : ℝ) ^ 4 + (m : ℝ) ^ 6) * N ^ 3 * (N * (16 * N) ^ m) ^ 4 =
      (2 * (m : ℝ) ^ 4 + (m : ℝ) ^ 6) * 16 ^ (4 * m) * N ^ (4 * m + 7) := by ring
  have h2 : 2 * ((m : ℝ) + (m : ℝ) * 2 ^ m) * (16 * N) ^ 2 * (N * (16 * N) ^ m) =
      2 * ((m : ℝ) + (m : ℝ) * 2 ^ m) * 16 ^ (m + 2) * N ^ (m + 3) := by ring
  have h3 : N ^ (m + 3) ≤ N ^ (4 * m + 7) := pow_le_pow_right₀ hN1 (by omega)
  have hc : 0 ≤ 2 * ((m : ℝ) + (m : ℝ) * 2 ^ m) * 16 ^ (m + 2) := by positivity
  unfold difRep_Z2 difRep_c2
  rw [h1, h2]
  nlinarith [mul_le_mul_of_nonneg_left h3 hc]

private theorem difRep_c1_nonneg (m : ℕ) : 0 ≤ difRep_c1 m := by unfold difRep_c1; positivity

private theorem difRep_c2_nonneg (m : ℕ) : 0 ≤ difRep_c2 m := by unfold difRep_c2; positivity

private theorem difRep_rpow_three_halves {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hΔ (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- **The summation arithmetic of the remainder**: for `k ≤ K`, `K Δ ≤ 1`, `Δ N^{8m+20} ≤ 1` and `N`
large (`N ≥ c₁ + 1`, `N ≥ 2 c₂`), `k (Z₁ Δ^{3/2} + 2 Z₂ Δ²) ≤ N^{m+9} Δ^{1/2}`. -/
private theorem difRep_rem_arith (m : ℕ) (N Δ : ℝ) (K k : ℕ) (hk : k ≤ K) (hN1 : 1 ≤ N)
    (hΔ0 : 0 ≤ Δ) (hKΔ : (K : ℝ) * Δ ≤ 1) (hΔN : Δ * N ^ (8 * m + 20) ≤ 1)
    (hN₁ : difRep_c1 m + 1 ≤ N) (hN₂ : 2 * difRep_c2 m ≤ N) :
    (k : ℝ) * (difRep_Z1 m N * Δ ^ ((3 : ℝ) / 2) + 2 * difRep_Z2 m N * Δ ^ 2) ≤
      N ^ (m + 9) * Real.sqrt Δ := by
  set r := Real.sqrt Δ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = Δ := Real.mul_self_sqrt hΔ0
  have hN0 : 0 < N := by linarith
  have hc1 := difRep_c1_nonneg m
  have hc2 := difRep_c2_nonneg m
  -- `r N^{4m+10} ≤ 1`
  have hrP : r * N ^ (4 * m + 10) ≤ 1 := by
    have h1 : (r * N ^ (4 * m + 10)) ^ 2 ≤ 1 := by
      have e : (r * N ^ (4 * m + 10)) ^ 2 = Δ * N ^ (8 * m + 20) := by
        rw [mul_pow, sq r, hrr, ← pow_mul]
        ring_nf
      rw [e]; exact hΔN
    exact (pow_le_one_iff_of_nonneg (by positivity) (by norm_num)).1 h1
  have hZ1 : difRep_Z1 m N = difRep_c1 m * N ^ (m + 8) := difRep_Z1_eq m N
  have hZ2 := difRep_Z2_le m hN1
  have hZ20 := difRep_Z2_nonneg m hN0.le
  have hZ10 := difRep_Z1_nonneg m hN0.le
  -- `2 Z₂ r ≤ 1`
  have h2Z : 2 * difRep_Z2 m N * r ≤ 1 := by
    have hN3 : 0 < N ^ 3 := by positivity
    have hNN3 : N ≤ N ^ 3 := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    have h1 : 2 * difRep_Z2 m N * r * N ^ 3 ≤ 2 * difRep_c2 m * (r * N ^ (4 * m + 10)) := by
      have e : 2 * difRep_c2 m * N ^ (4 * m + 7) * r * N ^ 3 =
          2 * difRep_c2 m * (r * N ^ (4 * m + 10)) := by ring
      rw [← e]
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hZ2 (by norm_num : (0 : ℝ) ≤ 2)) hr0
      have := mul_le_mul_of_nonneg_right this hN3.le
      nlinarith [this]
    have h2 : 2 * difRep_c2 m * (r * N ^ (4 * m + 10)) ≤ 2 * difRep_c2 m := by
      calc 2 * difRep_c2 m * (r * N ^ (4 * m + 10)) ≤ 2 * difRep_c2 m * 1 :=
            mul_le_mul_of_nonneg_left hrP (by positivity)
        _ = 2 * difRep_c2 m := mul_one _
    have h3 : 2 * difRep_Z2 m N * r * N ^ 3 ≤ 1 * N ^ 3 := by linarith
    exact le_of_mul_le_mul_right h3 hN3
  -- `Z₁ + 2 Z₂ r ≤ N^{m+9}`
  have hbig : difRep_Z1 m N + 2 * difRep_Z2 m N * r ≤ N ^ (m + 9) := by
    have hp : 1 ≤ N ^ (m + 8) := one_le_pow₀ hN1
    calc difRep_Z1 m N + 2 * difRep_Z2 m N * r ≤ difRep_c1 m * N ^ (m + 8) + 1 := by
          rw [hZ1]; linarith
      _ ≤ (difRep_c1 m + 1) * N ^ (m + 8) := by nlinarith
      _ ≤ N * N ^ (m + 8) := mul_le_mul_of_nonneg_right hN₁ (by positivity)
      _ = N ^ (m + 9) := by ring
  -- the sum over `k ≤ K` steps
  have hΔ32 := difRep_rpow_three_halves hΔ0
  rw [hΔ32]
  have hbr : 0 ≤ difRep_Z1 m N * (Δ * r) + 2 * difRep_Z2 m N * Δ ^ 2 := by positivity
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk
  calc (k : ℝ) * (difRep_Z1 m N * (Δ * r) + 2 * difRep_Z2 m N * Δ ^ 2)
      ≤ (K : ℝ) * (difRep_Z1 m N * (Δ * r) + 2 * difRep_Z2 m N * Δ ^ 2) :=
        mul_le_mul_of_nonneg_right hkK hbr
    _ = ((K : ℝ) * Δ) * (difRep_Z1 m N * r + 2 * difRep_Z2 m N * Δ) := by ring
    _ ≤ 1 * (difRep_Z1 m N * r + 2 * difRep_Z2 m N * Δ) :=
        mul_le_mul_of_nonneg_right hKΔ (by positivity)
    _ = r * (difRep_Z1 m N + 2 * difRep_Z2 m N * r) := by rw [← hrr]; ring
    _ ≤ r * N ^ (m + 9) := mul_le_mul_of_nonneg_left hbig hr0
    _ = N ^ (m + 9) * r := mul_comm _ _

/-- Target 4, `gridRepRemN_holds`: clauses (i)-(ii) with `C₀ = m + 9`, for `3 ≤ d` (DECISIONS §36).
`CK = 8m + 20`; route: `gridDriftN_envelope` (`τ_K = 1`, `hKb := stKbound_of_flow`) and
`exists_norm_Kcal_le_win` give the per-step bound `‖r_j‖ ≤ Z₁ Δ^{3/2} + 2 Z₂ Δ²`
(`difRep_step_le`), summed over `j < k ≤ K` (`difRep_rem_arith`). -/
theorem gridRepRemN_holds :
    ∀ d : ℕ, 3 ≤ d → ∀ m : ℕ, 2 ≤ m → GridRepRemNAt d m ((m : ℝ) + 9) := by
  intro d hd m hm κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  refine ⟨((8 * m + 20 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  intro K hK0 hKN
  refine ⟨?_, ?_⟩
  · intro n i
    exact ae_of_all _ fun ω k _ => difRep_identity sz (STflowE z) s t K n i k ω
  · have hfl : ∀ n, |STflowE z n| ≤ 2 - κ ∧ lemT (z n) < 1 := fun n =>
      let h := difRep_flow_bounds sz hκ hz n (htT n)
      ⟨h.1, h.2.1⟩
    have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n => (hfl n).1
    have hE2 : ∀ n, |STflowE z n| < 2 := fun n => by linarith [hE n]
    have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hfl n).2
    have hsize : sz.SizeTendsto := hz.1.2.2.1
    have hKb : sz.STKbound (STflowE z) := stKbound_of_flow sz hd hκ hz
    have hEnv : ∀ᶠ n in atTop, ∀ σ : Fin m → Bool, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n →
        ∀ a : Fin m → Zd d (sz.L n),
          ‖predIncN sz (STflowE z) s t K n j σ ω a - (gridStep s t K n : ℂ) *
              (∑ l ∈ Finset.Icc 3 m, sz.STksimLKM n (STflowE z n) (gridTime s t K n j)
                  (pathH sz s t K n j ω) l (loopOf σ a) +
                sz.STelklkM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                  (loopOf σ a) +
                sz.STegtM n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                  (loopOf σ a))‖ ≤
            stepErrN d (sz.L n) (sz.W n) (STflowE z n) m (gridTime s t K n j)
              (gridTime s t K n (j + 1)) (gridStep s t K n)
              (((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) *
                (etaT (STflowE z n) (gridTime s t K n (j + 1)))⁻¹ ^ m) :=
      Filter.eventually_all.2 fun σ =>
        gridDriftN_envelope sz κ hκ m hm 1 one_pos hsize hKb hE hs hst ht1 hK0 σ
    have hKw := exists_norm_Kcal_le_win sz hsize (STflowE z) hKb hE2 t
      (fun n => (hs n).trans (hst n)) ht1 m 1 one_pos
    have hbig := (hsize.eventually_ge_atTop (max 16 (max (difRep_c1 m + 1) (2 * difRep_c2 m))))
    filter_upwards [hEnv, hKw, hbig, hKN] with n hEnvn hKwn hbign hKNn
    intro i
    have hN16 : (16 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hbign
    have hN₁ : difRep_c1 m + 1 ≤ ((sz.size n : ℕ) : ℝ) :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hbign
    have hN₂ : 2 * difRep_c2 m ≤ ((sz.size n : ℕ) : ℝ) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hbign
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hΔ0 := difRep_gridStep_nonneg (s := s) (t := t) (K := K) (hst n)
    have hKΔ : (K n : ℝ) * gridStep s t K n ≤ 1 := by
      rw [difRep_K_mul_step s t K n (hK0 n)]
      linarith [hs n, ht1 n]
    have hKNn' : ((sz.size n : ℕ) : ℝ) ^ (8 * m + 20) ≤ K n := by
      have := hKNn
      rwa [Real.rpow_natCast] at this
    have hΔN : gridStep s t K n * ((sz.size n : ℕ) : ℝ) ^ (8 * m + 20) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hKNn' hΔ0).trans (by rw [mul_comm]; exact hKΔ)
    have hΔH : gridStep s t K n * (16 * ((sz.size n : ℕ) : ℝ)) ≤ 1 := by
      have h16 : 16 * ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (8 * m + 20) := by
        calc 16 * ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right hN16 (by linarith)
          _ = ((sz.size n : ℕ) : ℝ) ^ 2 := (sq _).symm
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ (8 * m + 20) := pow_le_pow_right₀ hN1 (by omega)
      exact (mul_le_mul_of_nonneg_left h16 hΔ0).trans hΔN
    filter_upwards [hEnvn i.1] with ω hω k hk
    have hstep := fun j (hj : j < K n) => difRep_step_le sz hκ hε hz hs hst htT hK0 hm n hΔH hKwn
      i.1 ω hω j hj i.2
    have hcast : ((sz.size n : ℕ) : ℝ) ^ ((m : ℝ) + 9) = ((sz.size n : ℕ) : ℝ) ^ (m + 9) := by
      rw [show ((m : ℝ) + 9) = ((m + 9 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hcast]
    calc ‖difRepRemN sz (STflowE z) s t K n i k ω‖
        ≤ ∑ j ∈ Finset.range k, ‖(pathP sz)[fun ω' => AvecN sz (STflowE z) s t K n (j + 1) i.1 ω' i.2 |
              filt sz j] ω - AvecN sz (STflowE z) s t K n j i.1 ω i.2 -
              ((gridStep s t K n : ℝ) : ℂ) * STgDriftN sz s t K n (STflowE z n) i.1 i.2 j ω‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range k, (difRep_Z1 m ((sz.size n : ℕ) : ℝ) * gridStep s t K n ^ ((3 : ℝ) / 2) +
            2 * difRep_Z2 m ((sz.size n : ℕ) : ℝ) * gridStep s t K n ^ 2) :=
          Finset.sum_le_sum fun j hj =>
            hstep j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)
      _ = (k : ℝ) * (difRep_Z1 m ((sz.size n : ℕ) : ℝ) * gridStep s t K n ^ ((3 : ℝ) / 2) +
            2 * difRep_Z2 m ((sz.size n : ℕ) : ℝ) * gridStep s t K n ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (m + 9) * Real.sqrt (gridStep s t K n) :=
          difRep_rem_arith m _ _ (K n) k hk hN1 hΔ0 hKΔ hΔN hN₁ hN₂

/-! ## 5. The assembly -/

/-- Target 5, `stGridRepNAt_of_parts`: the four clauses assemble to the pin at one loop length
(`CK := max CK_rem (max CK_tail CK_wtail)`; `N ≥ 1` gives `N^{CK_i} ≤ N^{CK}`). -/
theorem stGridRepNAt_of_parts :
    ∀ (d m : ℕ) (C₀ : ℝ), 0 ≤ C₀ → GridRepRemNAt d m C₀ → GridRepTailNAt d m →
      GridRepWTailNAt d m → STGridRepNAt d m C₀ := by
  intro d m C₀ _ hRem hTail hWTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKr, hCKr, hr⟩ := hRem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  obtain ⟨CKt, hCKt, ht⟩ := hTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKw, hCKw, hw⟩ := hWTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨max CKr (max CKt CKw), le_max_of_le_left hCKr, fun K hK0 hKN => ?_⟩
  have hmono : ∀ C : ℝ, C ≤ max CKr (max CKt CKw) → ∀ n : ℕ,
      ((sz.size n : ℕ) : ℝ) ^ (max CKr (max CKt CKw)) ≤ K n → ((sz.size n : ℕ) : ℝ) ^ C ≤ K n :=
    fun C hC n hn =>
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n) hC).trans hn
  have hKr : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKr ≤ K n :=
    hKN.mono fun n hn => hmono _ (le_max_left _ _) n hn
  have hKt : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKt ≤ K n :=
    hKN.mono fun n hn => hmono _ ((le_max_left _ _).trans (le_max_right _ _)) n hn
  have hKw : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKw ≤ K n :=
    hKN.mono fun n hn => hmono _ ((le_max_right _ _).trans (le_max_right _ _)) n hn
  obtain ⟨hid, hrem⟩ := hr K hK0 hKr
  exact ⟨fun n i k ω => difRepMartN sz (STflowE z) s t K n i k ω,
    fun n i k ω => difRepRemN sz (STflowE z) s t K n i k ω, hid, hrem,
    fun ε' hε' => ht K hK0 hKt ε' hε', fun ε' hε' => hw K hK0 hKw ε' hε'⟩

/-- Target 5, `stGridRepN_of_tails`: the pin `STGridRepN` from the two owed tails. -/
theorem stGridRepN_of_tails :
    ∀ d : ℕ, 3 ≤ d → (∀ m : ℕ, 2 ≤ m → GridRepTailNAt d m) →
      (∀ m : ℕ, 2 ≤ m → GridRepWTailNAt d m) → STGridRepN d := by
  intro d hd hT hW m hm
  exact ⟨(m : ℝ) + 9, by positivity,
    stGridRepNAt_of_parts d m _ (by positivity) (gridRepRemN_holds d hd m hm) (hT m hm) (hW m hm)⟩

/-- Target 5, `stGridMartAt_of_parts2`: the loop-length-`2` pin needs only clauses (i)-(iii)
(the vocabulary of loop length `2` by `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN`, `STEEM_eq_STeeM`, as in
`ST_gridMart_of_repN`). -/
theorem stGridMartAt_of_parts2 :
    ∀ (d : ℕ) (C₀ : ℝ), 0 ≤ C₀ → GridRepRemNAt d 2 C₀ → GridRepTailNAt d 2 →
      STGridMartAt d C₀ := by
  intro d C₀ _ hRem hTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  obtain ⟨CKr, hCKr, hr⟩ := hRem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT
  obtain ⟨CKt, hCKt, ht⟩ := hTail κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz s t hs hst htT D hD
  refine ⟨max CKr CKt, le_max_of_le_left hCKr, fun K hK0 hKN => ?_⟩
  have hmono : ∀ C : ℝ, C ≤ max CKr CKt → ∀ n : ℕ,
      ((sz.size n : ℕ) : ℝ) ^ (max CKr CKt) ≤ K n → ((sz.size n : ℕ) : ℝ) ^ C ≤ K n :=
    fun C hC n hn =>
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz.one_le_size n) hC).trans hn
  have hKr : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKr ≤ K n :=
    hKN.mono fun n hn => hmono _ (le_max_left _ _) n hn
  have hKt : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CKt ≤ K n :=
    hKN.mono fun n hn => hmono _ (le_max_right _ _) n hn
  obtain ⟨hid, hrem⟩ := hr K hK0 hKr
  refine ⟨fun n i k ω => difRepMartN sz (STflowE z) s t K n i k ω,
    fun n i k ω => difRepRemN sz (STflowE z) s t K n i k ω, ?_, hrem, ?_⟩
  · intro n i
    filter_upwards [hid n i] with ω hω k hk
    simp only [STgA_eq_STgAN, STgDrift_eq_STgDriftN]
    exact hω k hk
  · intro ε' hε'
    filter_upwards [ht K hK0 hKt ε' hε'] with n hn i
    simp only [STEEM_eq_STeeM]
    exact hn i

/-- Target 5, `stGridMart_of_tail`: the pin `STGridMart` from the plain tail at `m = 2` alone. -/
theorem stGridMart_of_tail :
    ∀ d : ℕ, 3 ≤ d → GridRepTailNAt d 2 → STGridMart d := by
  intro d hd hT
  exact ⟨((2 : ℕ) : ℝ) + 9, by positivity,
    stGridMartAt_of_parts2 d _ (by positivity) (gridRepRemN_holds d hd 2 le_rfl) hT⟩

/-! ## 6. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `sz0` (`d = 3`, `L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`,
`N_0 = 2097152`) and the flow block of `Induction/Defs.lean` (`z0 = 1/2 + i N^{-4/5}`, `flow_z0` with
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ 0`, `t ≡ 1/16 ≤ lemT z0`).  The grid of §6.1 is `K ≡ 4`, so
`Δ = 1/64`.  Every deterministic hypothesis is discharged; what stays a hypothesis of an instance is
`GridRepTailNAt`, `GridRepWTailNAt` (the pins owed to ST2-13) and the other pins of the Step 2 chain. -/

end RBM.Ind

namespace RBM.Ind.DifREP1Inst

open MeasureTheory Filter RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
  RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step2DefsInst

theorem hs0 : ∀ n, 0 ≤ sInst n := fun _ => le_rfl

theorem hst : ∀ n, sInst n ≤ tInst n := fun n => by simp only [sInst, tInst]; norm_num

theorem htT : ∀ n, tInst n ≤ lemT (z0 n) := fun n => sixteenth_le_lemT n

/-- The instance grid is nondegenerate: `K ≡ 4` on `[0, 1/16]` has `Δ = 1/64`. -/
theorem gridStep_inst : gridStep sInst tInst (fun _ => 4) 0 = 1 / 64 := by
  norm_num [gridStep, sInst, tInst]

/-- The loop `(+,-,+)` of length `3` at the origin label. -/
def σ3 : Fin 3 → Bool := ![true, false, true]

/-- A point of the path space. -/
def ω0 : PathΩ sz0 := fun _ _ => 0

/-- **`difRep_identity` at the data** (`m = 3`, `K ≡ 4`, `n = 0`, `σ = (+,-,+)`, `a ≡ 0`, `k = 3`): the
split `A_3 = A_0 + Δ Σ_{j<3} Drift_j + Rem_3 + Mart_3` for every `ω`. -/
theorem inst_difRep_identity (ω : PathΩ sz0) :
    STgAN sz0 sInst tInst (fun _ => 4) 0 (STflowE z0 0) σ3 (fun _ => 0) 3 ω =
      STgAN sz0 sInst tInst (fun _ => 4) 0 (STflowE z0 0) σ3 (fun _ => 0) 0 ω +
        ((gridStep sInst tInst (fun _ => 4) 0 : ℝ) : ℂ) *
          ∑ j ∈ Finset.range 3,
            STgDriftN sz0 sInst tInst (fun _ => 4) 0 (STflowE z0 0) σ3 (fun _ => 0) j ω +
        difRepRemN sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 (σ3, fun _ => 0) 3 ω +
        difRepMartN sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 (σ3, fun _ => 0) 3 ω :=
  difRep_identity sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 (σ3, fun _ => 0) 3 ω

/-- **`difRepMartN_succ_sub` at the data** (`j = 2`). -/
theorem inst_difRepMartN_succ_sub (ω : PathΩ sz0) :
    difRepMartN sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 (σ3, fun _ => 0) 3 ω -
        difRepMartN sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 (σ3, fun _ => 0) 2 ω =
      martIncN sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 2 σ3 ω (fun _ => 0) :=
  difRepMartN_succ_sub sz0 (STflowE z0) sInst tInst (fun _ => 4) 0 (σ3, fun _ => 0) 2 ω

/-- the two instances at the concrete point `ω0` -/
example := inst_difRep_identity ω0
example := inst_difRepMartN_succ_sub ω0

/-- **`difRep_Ugen_step_le` at the data** (`L = 4`, `g = 1/64`, `E = 1/2`, `k = 3`, `σ = (+,-,+)`,
`u = 0`, `Δ = 1/128`, `A ≡ 1`, `M = 1`). -/
theorem inst_difRep_Ugen_step_le (x : Fin 3 → Zd 3 4) :
    ‖Ugen 3 4 (1 / 64) (1 / 2) σ3 0 (0 + 1 / 128) (fun _ => (1 : ℂ)) x - 1 -
        (((1 / 128 : ℝ)) : ℂ) * ThetaN 3 4 (1 / 64) (fun i => mSigma (1 / 2) (σ3 i)) 0
          (fun _ => (1 : ℂ)) x‖ ≤ uStepC 3 (1 / 128) (0 + 1 / 128) * 1 :=
  difRep_Ugen_step_le 3 4 (1 / 64) (by norm_num) (E := 1 / 2) (by norm_num) σ3 (u := 0)
    (Δ := 1 / 128) le_rfl (by norm_num) (by norm_num) (fun _ => (1 : ℂ)) 1
    (fun y => by simp) x

/-- **`difRep_flow_bounds` at the data** (`κ = 1/10`, `n = 0`, `u = 1/16 ≤ lemT (z0 0)`). -/
theorem inst_difRep_flow_bounds :
    |STflowE z0 0| ≤ 2 - 1 / 10 ∧ lemT (z0 0) < 1 ∧
      ((sz0.size 0 : ℕ) : ℝ) ^ (-1 + 1 / 10 : ℝ) / 16 ≤ etaT (STflowE z0 0) (1 / 16) ∧
      etaT (STflowE z0 0) (1 / 16) ≤ 1 - 1 / 16 :=
  difRep_flow_bounds sz0 (κ := 1 / 10) (by norm_num) flow_z0 0 (u := 1 / 16)
    (sixteenth_le_lemT 0)

/-- **`gridRepRemN_holds` at the flow data**, every loop length `m ≥ 2`: the grid exponent `CK` it
returns, the grid `K_n = ⌈N^{CK}⌉ + 1`, the decomposition a.e. for every `k ≤ K_n` (clause (i)) and the
remainder bound `‖Rem_k‖ ≤ N^{m+9} Δ^{1/2}` eventually (clause (ii)). -/
theorem inst_gridRepRemN (m : ℕ) (hm : 2 ≤ m) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd 3 (sz0.L n))), ∀ᵐ ω ∂(pathP sz0),
        ∀ k, k ≤ K n →
          STgAN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 k ω =
            STgAN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 0 ω +
              ((gridStep sInst tInst K n : ℝ) : ℂ) *
                ∑ j ∈ Finset.range k, STgDriftN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω +
              difRepRemN sz0 (STflowE z0) sInst tInst K n i k ω +
              difRepMartN sz0 (STflowE z0) sInst tInst K n i k ω) ∧
      (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd 3 (sz0.L n)),
        ∀ᵐ ω ∂(pathP sz0), ∀ k, k ≤ K n →
          ‖difRepRemN sz0 (STflowE z0) sInst tInst K n i k ω‖ ≤
            ((sz0.size n : ℕ) : ℝ) ^ ((m : ℝ) + 9) * Real.sqrt (gridStep sInst tInst K n)) := by
  obtain ⟨CK, hCK, h⟩ := gridRepRemN_holds 3 (by norm_num) m hm (1 / 10) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 ≠ 0 := fun n => Nat.succ_ne_zero _
  have hKN : ∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ ((⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 : ℕ) : ℝ) :=
    Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
  exact ⟨CK, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1, hK0, hKN,
    h (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) hK0 hKN⟩

/-- `gridRepRemN_holds` at `m = 2` and `m = 3` on the flow data. -/
example := inst_gridRepRemN 2 le_rfl
example := inst_gridRepRemN 3 (by norm_num)

/-- **`stGridRepNAt_of_parts` at the data** (`d = 3`, `m = 3`, `C₀ = 3 + 9`): the clauses (i)-(ii)
are `gridRepRemN_holds`; the two tails are the pins owed to ST2-13. -/
example (hT : GridRepTailNAt 3 3) (hW : GridRepWTailNAt 3 3) :
    STGridRepNAt 3 3 (((3 : ℕ) : ℝ) + 9) :=
  stGridRepNAt_of_parts 3 3 _ (by positivity) (gridRepRemN_holds 3 (by norm_num) 3 (by norm_num))
    hT hW

/-- **`stGridRepN_of_tails` at `d = 3`**: the pin `STGridRepN 3` from the two owed tails. -/
example (hT : ∀ m : ℕ, 2 ≤ m → GridRepTailNAt 3 m) (hW : ∀ m : ℕ, 2 ≤ m → GridRepWTailNAt 3 m) :
    STGridRepN 3 :=
  stGridRepN_of_tails 3 (by norm_num) hT hW

/-- **`stGridMartAt_of_parts2` at the data** (`d = 3`, `C₀ = 2 + 9`): loop length `2`, clauses (i)-(iii). -/
example (hT : GridRepTailNAt 3 2) : STGridMartAt 3 (((2 : ℕ) : ℝ) + 9) :=
  stGridMartAt_of_parts2 3 _ (by positivity) (gridRepRemN_holds 3 (by norm_num) 2 le_rfl) hT

/-- **`stGridMart_of_tail` at `d = 3`**: the pin `STGridMart 3` from the plain tail at `m = 2` alone. -/
example (hT : GridRepTailNAt 3 2) : STGridMart 3 := stGridMart_of_tail 3 (by norm_num) hT

/-- **`STStep2 3` through `ST_step2_of_pinsN'`** with the two owed tails and the other pins of the
chain as hypotheses (DECISIONS §36 (iii)). -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hT : ∀ m : ℕ, 2 ≤ m → GridRepTailNAt 3 m) (hW : ∀ m : ℕ, 2 ≤ m → GridRepWTailNAt 3 m)
    (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) : STStep2 3 :=
  ST_step2_of_pinsN' hNew hLWT hEMe (stGridRepN_of_tails 3 (by norm_num) hT hW) hOpt hClos

/-- **`STStep2 3` through `ST_step2_of_pins'`**: the loop-length-`2` pin `STGridMart` from the plain tail
alone, the other pins of the chain as hypotheses. -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hT : GridRepTailNAt 3 2)
    (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) : STStep2 3 :=
  ST_step2_of_pins' hNew hLWT hEMe (stGridMart_of_tail 3 (by norm_num) hT) hOpt hClos

/-- **The conclusion of `STStep2` at the data**: the chain with the two owed tails compiles to the
statement at `(sz0, z0, 0, 1/16)`. -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hT : ∀ m : ℕ, 2 ≤ m → GridRepTailNAt 3 m) (hW : ∀ m : ℕ, 2 ≤ m → GridRepWTailNAt 3 m)
    (hOpt : STOptL2 3) (hClos : STLocalAvgOfL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_of_pinsN' hNew hLWT hEMe (stGridRepN_of_tails 3 (by norm_num) hT hW) hOpt
    hClos)

end RBM.Ind.DifREP1Inst

end
