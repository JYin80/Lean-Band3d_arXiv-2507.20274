/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Batteries.Tactic.OpenPrivate
import RBM3D.Loop.KLInduct

/-!
# The `K`-loop layer, KL12: Ward's inequality for `𝒦`-loops, `lem_wardineq_K`, `(wardineq_K)`

Ticket T2122 (`paper/tex/A_deterministic_estimates.tex:809-827`, the proof of `lem_wardineq_K`;
statement `3_5_Loop_Hierarchy.tex:1001-1005`), `d ≥ 3`.  Names are in `RBM.Loop`.

Pinned names: `KLwardIneqAt`, `KLwardIneqPin` (verbatim from `docs/tickets/checks/T2122-check.lean`,
i.e. `64b58eb:RBM3D/Probe/T2004Pins.lean:786-798`) and their proof `KLwardIneqPin_holds`.  The
statement of `(eq:K-pi-bound_partial)` is `KLWardIneq_KpiAt`, proved by `KLWardIneq_KpiAt_holds`
(strong induction with `KLWardIneq_Kpi_step`).  Every other public declaration carries the file-stem
prefix `KLWardIneq`, every other helper is `private`.  The only hypothesis of the proved pins is
`KLPT d κ gmax`; the new `Prop` `KLWardIneq_KpiAt` is concluded by `KLWardIneq_KpiAt_holds`, so
`Test/Axioms.lean` needs no new line.

* §1 the pins.
* §2 `η_t ≤ 1 - t` and `(1 - t)⁻¹ ≤ η_t⁻¹` (`0 < Im m^{(E)} ≤ 1` for `|E| < 2`).
* §3 the layer `π = ∅` with the last label summed (`KLWardIneq_Kpi_empty_bound`): the last leaf is
  long, or short.
* §4 the cut `KLKpi_cut` keeps the summed last label in the outer polygon.
* §5 the induction step, `KLWardIneq_KpiAt_holds`, the case `n = 2` (`KLWardIneq_At_two`), the case
  `n ≥ 3` from the layers (`KLWardIneq_At_of_Kpi`), the pin `KLwardIneqPin_holds`.
* §6 the compiled instances at `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`.

**The induction.**  Notation: `n = m + 1` polygon vertices, the summed label is the label of
the last vertex `v = Fin.last m`, `a[x] = Function.update a v x`, `K^{(π)} = KLKpi`.  Strong
induction on `m ≥ 2` for `P(m) := ∑_x |K^{(π)}(σ, a[x])| ≤ C L^τ η_t⁻¹ B_{t,0}^{n-2}`.  At `n`,
given `P(m'')` for `2 ≤ m'' < m`:

(L) `π = ∅`, `σ_v ≠ σ_{v+1}` (the leaf of `v` is the long `Θ_t^{(+,-)}`).  `K^{(∅)}(a[x]) =
∑_b Θ(x, b) X_b`, `X_b = ∑_{δ_v = b} Σ^{(∅)}(δ) ∏_{i ≠ v} Θ_i(a_i, δ_i)`; the column sums of `Θ` are
`≤ (1-t)⁻¹ ≤ η_t⁻¹` (`(eq:THETAinftinf)`), and `∑_b |X_b| ≺ B^{n-2}` is `KLindStepPin_holds`
(`(eq:ind-step-bound)`, the estimate with the cancellation inside the sum over the slice).
(S) `π = ∅`, `σ_v = σ_{v+1}` (the leaf of `v` is short).  The paper's displayed line
`A_deterministic_estimates.tex:816-818` writes `Θ^{(+,-)}_{t,a_n b_n}` and does not cover it;
`KLindStepAt` needs a long root and `KLindStep_nonAlt_noloss` a second short leaf.  Here:
`∑_x |Θ^{(s,s)}(x, b)| ≤ S` (property 5', `KLedge_l1`), `|Σ^{(∅)}(δ)| ≤ C_m e^{-c_m max|δ_i - δ_j|}`
(`KLmolecule_holds`), the leaves other than `v` and `0` are `≤ C_d B` pointwise (`KLedge_sup`), the
leaf at `0` is summed (`∑_y |Θ(a_0, y)| ≤ (1-t)⁻¹`) and `∑_{δ_0 = y} e^{-c max|δ_i - δ_j|} ≤
expC^{n-1}`.  So `∑_x |K^{(∅)}| ≤ S C_m (C_d B)^{n-2} expC^{n-1} (1-t)⁻¹`, with no cancellation and
no loss `L^τ`.
(C) `π ≠ ∅`: `K^{(π)} = 0` if no tree has the long edges `π`; otherwise cut at an innermost long
edge `J = (i, j)` (`KLKpi_cut`).  Since `j ≤ n - 1`, the last vertex is not the glue vertex `i`,
and the labels of the inner polygon below its root do not see `a_{n-1}`: `A(u)` does not depend
on `x`, and the outer labels are `a_out(w)[x]` (`KLWardIneq_aOut_update`).  Then
`∑_x |K^{(π)}| ≤ |t| (∑_u |A(u)|) sup_w ∑_x |K^{(π'')}(w, x)|` (`∑_w |S^{(B)}_{uw}| = 1`),
`∑_u |A| ≺ B^{k-2}` (`KLindStepPin_holds` at `k = j - i + 1 ∈ [3, n-1]`, loss `L^{τ/2}`) and
`sup_w ∑_x |K^{(π'')}| ≺ η_t⁻¹ B^{n''-2}` (`P(m'')` at `τ/2`, `n'' = n - (j - i) + 1 ∈ [3, n-1]`).
`(k-2) + (n''-2) = n - 2`, `L^{τ/2} L^{τ/2} = L^τ`, and `η_t⁻¹` occurs exactly once.

Then `(wardineq_K)`: `n = 2` is `KLK_two` (every `σ`, also `(s, s)`, which `KLward_two` does not
cover); `n ≥ 3` is `(eq_K-Kpi)` (`KLK_eq_sum_Kpi`): `W^{-d(n-1)}` times the sum over the
`2^{|diagonals n|}` layers, and `(W^{-d})^{n-1} η_t⁻¹ B^{n-2} = (W^d η_t)⁻¹ (W^{-d} B)^{n-2}`.  The
constant depends on `d, n, κ, gmax, τ` only, never on `L, W, g, t, E`: the pins are uniform in
`t ∈ [0,1)`, and the regimes `1 - t ≷ g², g²/L², g²/L^d` are absorbed in `B_{t,0}` (DECISIONS §29).

**Differences from the paper.**  (i) The paper inducts on the number of molecules for the
generalised `K̃^{(π)}` (leaves `Θ̃ ∈ {Θ, tSΘ}`); here, as in `KLInduct.lean`, on the number of
polygon vertices for the standard `K^{(π)}`.  (ii) The case (S) is proved here.
(iii) `(eq:K-pi-bound_partial)` is stated for `n ≥ 3`: `(eq_K-Kpi)` and `K^{(π)}` are for `n ≥ 3`
(`KLgen` uses `kTwo` at length `2`); `n = 2` is `KLWardIneq_At_two`.  (iv) The loss is `L^τ` with
`τ > 0` arbitrary, as in the pin.

Reused from the merged files: `KLKpi_cut`, `KLInduct_aIn`, `KLInduct_aOut`, `KLindStepPin_holds`,
`KLmolecule_holds`, `KLedge_sup`, `KLedge_l1`, `KLone_le_rpow`, `KLK_eq_sum_Kpi`,
`KLKpi_eq_sum_SigmaPi`, `KLK_two`, `sum_norm_Theta_row_le`, `sum_norm_SB_row`, and (public since
ticket T2127, `private` when this file was written) `sigmaIn`, `sigmaOut`.  Copied, because they
were `private` in merged files when this file was written: `KLMolecule_sum_slice` (still private)
and `KLMolecule_sum_exp_maxDist` (`KLMolecule.lean:688`, `:722`), `exists_innermost` and
`Flong_subset_diagonals` (`KLSumZeroWard.lean:577`, `:594`; the last three are public since T2127).
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The pins (verbatim: `docs/tickets/checks/T2122-check.lean`) -/

/-- **Pin `lem_wardineq_K`, `(wardineq_K)`** (consumer: `lem:SEforLn`): for `n ≥ 2`,
`max_σ ∑_{a_n} |𝒦^{(n)}_{t,σ,a}| ≺ (W^d η_t)⁻¹ (W^{-d} B_{t,0})^{n-2}`. -/
def KLwardIneqAt (d n : ℕ) (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (a : Fin (n - 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLK d p.L p.g p.W p.E p.t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
      ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d) * Gauss.etaT p.E p.t)⁻¹
          * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 2)

def KLwardIneqPin : Prop :=
  ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLwardIneqAt d n κ gmax

/-! ## 2. Scalar facts -/

section Scalar

/-- `η_t ≤ 1 - t` (`0 < Im m ≤ 1`). -/
private theorem KLWardIneq_etaT_le {E t : ℝ} (ht : t ≤ 1) :
    Gauss.etaT E t ≤ 1 - t := by
  have him : (mE E).im ≤ 1 := by
    rw [mE_im, div_le_one (by norm_num)]
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
  have h1 : 0 ≤ 1 - t := by linarith
  calc Gauss.etaT E t = (1 - t) * (mE E).im := rfl
    _ ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left him h1
    _ = 1 - t := mul_one _

/-- `η_t > 0` in the bulk. -/
private theorem KLWardIneq_etaT_pos {E t κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht : t < 1) :
    0 < Gauss.etaT E t :=
  Gauss.etaT_pos (by linarith) ht

/-- `(1 - t)⁻¹ ≤ η_t⁻¹`. -/
private theorem KLWardIneq_inv_le {E t κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht : t < 1) :
    (1 - t)⁻¹ ≤ (Gauss.etaT E t)⁻¹ :=
  inv_anti₀ (KLWardIneq_etaT_pos hκ hE ht) (KLWardIneq_etaT_le ht.le)

end Scalar

/-! ## 3. The layer `π = ∅` with the last label summed -/

section Empty

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- Column sums of a symmetric kernel equal row sums. -/
private theorem KLWardIneq_col_eq_row (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (b : Zd d L) :
    ∑ x : Zd d L, ‖Theta d L g ξ x b‖ = ∑ x : Zd d L, ‖Theta d L g ξ b x‖ := by
  refine Finset.sum_congr rfl fun x _ => ?_
  have := congrFun (congrFun (Theta_transpose_of_three_le (d := d) (g := g) hL hξ) x) b
  rw [Matrix.transpose_apply] at this
  rw [this]

/-- `(eq:THETAinftinf)`: the column sums of every leaf `Θ^{(s,s')}_t` are `≤ (1-t)⁻¹`. -/
private theorem KLWardIneq_col_thetaEdge_le (hL : 3 ≤ L) {E t : ℝ} (hE : |E| ≤ 2) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (s s' : Bool) (b : Zd d L) :
    ∑ x : Zd d L, ‖thetaEdge d L g (mSigma E) t s s' x b‖ ≤ (1 - t)⁻¹ := by
  unfold thetaEdge
  have hμ : ‖mSigma E s * mSigma E s'‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
  have hξ := norm_mul_mSigma_lt_one hE ht0 ht1 s s'
  rw [KLWardIneq_col_eq_row hL hξ]
  exact sum_norm_Theta_row_le hL ht0 ht1 hμ b

/-- **`K^{(∅)}` with the last label `x`**: `K^{(∅)}(σ, a[x]) = ∑_b Θ^{(σ_v,σ_{v+1})}(x, b) X_b`,
`v = Fin.last m`, `X_b = ∑_{δ_v = b} Σ^{(∅)}(δ) ∏_{i ≠ v} Θ^{(σ_i,σ_{i+1})}(a_i, δ_i)`. -/
private theorem KLWardIneq_Kempty_slice (m' : Bool → ℂ) (t : ℝ) {m : ℕ} (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d L) (x : Zd d L) :
    KLKpi d L g m' t σ (Function.update a (Fin.last m) x) ∅
      = ∑ b : Zd d L, thetaEdge d L g m' t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b *
          ∑ δ ∈ Finset.univ.filter (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            KLSigmaPi d L g m' t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge d L g m' t (σ i) (σ (i + 1)) (a i) (δ i) := by
  rw [KLKpi_eq_sum_SigmaPi,
    ← Finset.sum_fiberwise Finset.univ (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  have hb : δ (Fin.last m) = b := (Finset.mem_filter.1 hδ).2
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (Fin.last m)), hb]
  have hprod : ∏ i ∈ Finset.univ.erase (Fin.last m),
      thetaEdge d L g m' t (σ i) (σ (i + 1)) (Function.update a (Fin.last m) x i) (δ i)
      = ∏ i ∈ Finset.univ.erase (Fin.last m), thetaEdge d L g m' t (σ i) (σ (i + 1)) (a i) (δ i) :=
    Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hprod, Function.update_self]
  ring

/-- If the column sums of the last leaf are `≤ Λ`, then `∑_x |K^{(∅)}(σ, a[x])| ≤ Λ ∑_b |X_b|`. -/
private theorem KLWardIneq_sum_Kempty_le (m' : Bool → ℂ) (t : ℝ) {m : ℕ} (σ : Fin (m + 1) → Bool)
    (a : Fin (m + 1) → Zd d L) {Λ : ℝ}
    (hΛ : ∀ b : Zd d L,
      ∑ x : Zd d L, ‖thetaEdge d L g m' t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b‖ ≤ Λ) :
    ∑ x : Zd d L, ‖KLKpi d L g m' t σ (Function.update a (Fin.last m) x) ∅‖
      ≤ Λ * ∑ b : Zd d L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            KLSigmaPi d L g m' t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge d L g m' t (σ i) (σ (i + 1)) (a i) (δ i)‖ := by
  simp only [KLWardIneq_Kempty_slice]
  set X : Zd d L → ℝ := fun b => ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            KLSigmaPi d L g m' t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge d L g m' t (σ i) (σ (i + 1)) (a i) (δ i)‖ with hX
  calc ∑ x : Zd d L, ‖∑ b : Zd d L, thetaEdge d L g m' t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b *
          ∑ δ ∈ Finset.univ.filter (fun δ : Fin (m + 1) → Zd d L => δ (Fin.last m) = b),
            KLSigmaPi d L g m' t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge d L g m' t (σ i) (σ (i + 1)) (a i) (δ i)‖
      ≤ ∑ x : Zd d L, ∑ b : Zd d L,
          ‖thetaEdge d L g m' t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b‖ * X b := by
        refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [norm_mul]
    _ = ∑ b : Zd d L, (∑ x : Zd d L,
          ‖thetaEdge d L g m' t (σ (Fin.last m)) (σ (Fin.last m + 1)) x b‖) * X b := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ ∑ b : Zd d L, Λ * X b :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hΛ b) (norm_nonneg _)
    _ = Λ * ∑ b : Zd d L, X b := by rw [Finset.mul_sum]

end Empty

section Short

variable {n : ℕ} [NeZero n] {d L : ℕ} [NeZero L]

/-- A sum over the slice `δ_0 = x` of a product of one-point functions (copy of the private
`KLMolecule_sum_slice`, `KLMolecule.lean:688`). -/
private theorem KLWardIneq_sum_slice (x : Zd d L) (f : Zd d L → ℝ) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd d L => δ 0 = x), ∏ i : Fin n, f (δ i)
      = f x * (∑ y, f y) ^ (n - 1) := by
  classical
  have hS : univ.filter (fun δ : Fin n → Zd d L => δ 0 = x)
      = Fintype.piFinset (fun i : Fin n => if i = 0 then ({x} : Finset (Zd d L)) else univ) := by
    ext δ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = 0
      · simp [hi, h]
      · simp [hi]
    · intro h
      have := h 0
      simpa using this
  have h := Finset.prod_univ_sum
    (fun i : Fin n => if i = 0 then ({x} : Finset (Zd d L)) else univ) (fun _ y => f y)
  rw [hS, ← h]
  have hfac : ∀ i : Fin n,
      ∑ y ∈ (if i = 0 then ({x} : Finset (Zd d L)) else univ), f y
        = if i = 0 then f x else ∑ y, f y := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  simp only [hfac]
  rw [← mul_prod_erase univ _ (mem_univ (0 : Fin n))]
  have h0 : (if (0 : Fin n) = 0 then f x else ∑ y, f y) = f x := by simp
  have h1 : ∀ i ∈ univ.erase (0 : Fin n),
      (if i = 0 then f x else ∑ y, f y) = ∑ y, f y := fun i hi => by
    simp [ne_of_mem_erase hi]
  rw [h0, prod_congr rfl h1, prod_const, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]

/-- `∑_{δ_0 = x} e^{-c max|δ_i - δ_j|} ≤ expC(c/n)^{n-1}` (copy of the private
`KLMolecule_sum_exp_maxDist`, `KLMolecule.lean:722`). -/
private theorem KLWardIneq_sum_exp_maxDist (k : ℕ) {c : ℝ} (hc : 0 < c) (x : Zd (k + 2) L) :
    ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x),
        Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ (expC k (c / n)) ^ (n - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcn : 0 < c / n := by positivity
  set f : Zd (k + 2) L → ℝ := fun y => Real.exp (-(c / n * (zdistD (k + 2) L (x - y) : ℝ)))
    with hf
  have hterm : ∀ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x),
      Real.exp (-(c * (KLmaxDist (k + 2) L δ : ℝ))) ≤ ∏ i : Fin n, f (δ i) := by
    intro δ hδ
    have hδ0 : δ 0 = x := (mem_filter.1 hδ).2
    simp only [hf, ← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hle : ∀ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ) ≤ KLmaxDist (k + 2) L δ := by
      intro i
      have : zdistD (k + 2) L (δ 0 - δ i) ≤ KLmaxDist (k + 2) L δ :=
        Finset.le_sup (f := fun q : Fin n × Fin n => zdistD (k + 2) L (δ q.1 - δ q.2))
          (mem_univ ((0 : Fin n), i))
      rw [hδ0] at this
      exact_mod_cast this
    have hsum : ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)
        ≤ n * (KLmaxDist (k + 2) L δ : ℝ) := by
      calc _ ≤ ∑ _i : Fin n, (KLmaxDist (k + 2) L δ : ℝ) := sum_le_sum fun i _ => hle i
        _ = n * (KLmaxDist (k + 2) L δ : ℝ) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ i : Fin n, -(c / n * (zdistD (k + 2) L (x - δ i) : ℝ))
        = -(c / n * ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)) := by
      rw [mul_sum, sum_neg_distrib]
    rw [h1]
    have h2 : c / n * ∑ i : Fin n, (zdistD (k + 2) L (x - δ i) : ℝ)
        ≤ c * (KLmaxDist (k + 2) L δ : ℝ) := by
      calc _ ≤ c / n * (n * (KLmaxDist (k + 2) L δ : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum hcn.le
        _ = c * (KLmaxDist (k + 2) L δ : ℝ) := by field_simp
    linarith
  have hfx : f x = 1 := by simp [hf]
  have hfs : ∑ y, f y ≤ expC k (c / n) := sum_exp_decay_centre k hcn x
  have hf0 : 0 ≤ ∑ y, f y := sum_nonneg fun _ _ => (Real.exp_pos _).le
  calc _ ≤ ∑ δ ∈ univ.filter (fun δ : Fin n → Zd (k + 2) L => δ 0 = x), ∏ i : Fin n, f (δ i) :=
        sum_le_sum hterm
    _ = f x * (∑ y, f y) ^ (n - 1) := KLWardIneq_sum_slice x f
    _ ≤ 1 * (expC k (c / n)) ^ (n - 1) := by
        rw [hfx]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf0 hfs _) zero_le_one
    _ = _ := one_mul _

end Short

section ShortLast

/-- **The absolute-value bound for a short last leaf** (case (S); the paper's displayed `π = ∅` bound
writes the last leaf as `Θ^{(+,-)}`): `∑_δ |Σ^{(∅)}(δ) ∏_{i ≠ v} Θ^{(σ_i,σ_{i+1})}(a_i, δ_i)| ≲
(1-t)⁻¹ B^{n-2}` for every `σ`.
`|Σ^{(∅)}(δ)| ≤ C_m e^{-c_m max|δ_i - δ_j|}` (`KLmolecule_holds`); all leaves but two are `≤ C_d B`
pointwise (`KLedge_sup`), the leaf at the vertex `0` is summed (`∑_y |Θ(a_0, y)| ≤ (1-t)⁻¹`), the
vertex `v` is free (its leaf is not in the product).  No cancellation and no loss `L^τ` is used. -/
private theorem KLWardIneq_abs_sum_le (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d p.L),
      ∑ δ : Fin (m + 1) → Zd d p.L, ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
          ∏ i ∈ Finset.univ.erase (Fin.last m),
            thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (1 - p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cm, hCm, cm, hcm, hmol⟩ :=
    KLmolecule_holds (k + 2) (m + 1) κ gmax hd (by omega) hκ hg hPT.short
  obtain ⟨Cd, hCd, hsup⟩ := KLedge_sup hPT
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hcn : 0 < cm / ((m + 1 : ℕ) : ℝ) := by positivity
  have hEC : 0 < expC k (cm / ((m + 1 : ℕ) : ℝ)) := by unfold expC; positivity
  refine ⟨Cm * Cd ^ (m - 1) * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m, by positivity, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  set v : Fin (m + 1) := Fin.last m with hv
  set B0 := Bparam (k + 2) p.L p.g p.t 0 with hB0def
  have hB0 : 0 ≤ B0 := KLIndStepA_Bparam_nonneg _ _
  have hv0 : (0 : Fin (m + 1)) ∈ Finset.univ.erase v := by
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro h
    have := congrArg Fin.val h
    simp [hv] at this
    omega
  have hcard : ((Finset.univ.erase v).erase (0 : Fin (m + 1))).card = m - 1 := by
    rw [Finset.card_erase_of_mem hv0, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hμ : ∀ s s' : Bool, ‖mSigma p.E s * mSigma p.E s'‖ = 1 := fun s s' => by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, mul_one]
  have hleaf : ∀ (i : Fin (m + 1)) (y z : Zd (k + 2) p.L),
      ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) y z‖ ≤ Cd * B0 := fun i y z =>
    hsup p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 _ (hμ (σ i) (σ (i + 1))) y z
  set e1 : (Fin (m + 1) → Zd (k + 2) p.L) → ℝ := fun δ =>
    Real.exp (-(cm * (KLmaxDist (k + 2) p.L δ : ℝ))) with he1
  set T0 : Zd (k + 2) p.L → ℝ := fun y =>
    ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ 0) (σ (0 + 1)) (a 0) y‖ with hT0
  have hpt : ∀ δ : Fin (m + 1) → Zd (k + 2) p.L,
      ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
          ∏ i ∈ Finset.univ.erase v,
            thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (Cm * (Cd * B0) ^ (m - 1)) * (e1 δ * T0 (δ 0)) := by
    intro δ
    rw [norm_mul, norm_prod, ← Finset.mul_prod_erase (Finset.univ.erase v) _ hv0]
    have h1 := hmol p σ δ
    have h3 : ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
        ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (Cd * B0) ^ (m - 1) := by
      calc _ ≤ ∏ _i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)), (Cd * B0) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => hleaf i (a i) (δ i)
        _ = (Cd * B0) ^ (m - 1) := by rw [Finset.prod_const, hcard]
    have h4 : 0 ≤ ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
        ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    have h5 : 0 ≤ T0 (δ 0) := norm_nonneg _
    have h6 : ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ 0) (σ (0 + 1)) (a 0) (δ 0)‖ *
          ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
            ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ T0 (δ 0) * (Cd * B0) ^ (m - 1) := mul_le_mul le_rfl h3 h4 h5
    have h7 : 0 ≤ Cm * e1 δ := by positivity
    calc ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖ *
          (‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ 0) (σ (0 + 1)) (a 0) (δ 0)‖ *
            ∏ i ∈ (Finset.univ.erase v).erase (0 : Fin (m + 1)),
              ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖)
        ≤ (Cm * e1 δ) * (T0 (δ 0) * (Cd * B0) ^ (m - 1)) :=
          mul_le_mul h1 h6 (mul_nonneg (norm_nonneg _) h4) h7
      _ = (Cm * (Cd * B0) ^ (m - 1)) * (e1 δ * T0 (δ 0)) := by ring
  have hsum : ∑ δ : Fin (m + 1) → Zd (k + 2) p.L, e1 δ * T0 (δ 0)
      ≤ (1 - p.t)⁻¹ * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
    calc ∑ δ : Fin (m + 1) → Zd (k + 2) p.L, e1 δ * T0 (δ 0)
        = ∑ y : Zd (k + 2) p.L, ∑ δ ∈ univ.filter (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ 0 = y),
            e1 δ * T0 (δ 0) :=
          (Finset.sum_fiberwise univ (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ 0)
            (fun δ => e1 δ * T0 (δ 0))).symm
      _ = ∑ y : Zd (k + 2) p.L, T0 y *
            ∑ δ ∈ univ.filter (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ 0 = y), e1 δ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun δ hδ => ?_
          have hδ0 : δ 0 = y := (Finset.mem_filter.1 hδ).2
          simp only [hδ0]
          ring
      _ ≤ ∑ y : Zd (k + 2) p.L, T0 y * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
          refine Finset.sum_le_sum fun y _ => ?_
          exact mul_le_mul_of_nonneg_left (KLWardIneq_sum_exp_maxDist (n := m + 1) k hcm y)
            (norm_nonneg _)
      _ = (∑ y : Zd (k + 2) p.L, T0 y) * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
          rw [Finset.sum_mul]
      _ ≤ (1 - p.t)⁻¹ * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simp only [hT0, thetaEdge]
          exact sum_norm_Theta_row_le p.hL p.ht0 p.ht1 (hμ (σ 0) (σ (0 + 1))) (a 0)
  have hP0 : 0 ≤ Cm * (Cd * B0) ^ (m - 1) := by positivity
  calc ∑ δ : Fin (m + 1) → Zd (k + 2) p.L,
        ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
          ∏ i ∈ Finset.univ.erase v,
            thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
      ≤ ∑ δ : Fin (m + 1) → Zd (k + 2) p.L, (Cm * (Cd * B0) ^ (m - 1)) * (e1 δ * T0 (δ 0)) :=
        Finset.sum_le_sum fun δ _ => hpt δ
    _ = (Cm * (Cd * B0) ^ (m - 1)) * ∑ δ : Fin (m + 1) → Zd (k + 2) p.L, e1 δ * T0 (δ 0) := by
        rw [Finset.mul_sum]
    _ ≤ (Cm * (Cd * B0) ^ (m - 1)) *
          ((1 - p.t)⁻¹ * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m) :=
        mul_le_mul_of_nonneg_left hsum hP0
    _ = Cm * Cd ^ (m - 1) * (expC k (cm / ((m + 1 : ℕ) : ℝ))) ^ m * (1 - p.t)⁻¹ * B0 ^ (m - 1) := by
        rw [mul_pow]; ring

end ShortLast

section EmptyBound

/-- **The layer `π = ∅` with the last label summed** (`n = m + 1 ≥ 3`, case `π = ∅` of the proof of
`lem_wardineq_K`): `∑_x |K^{(∅)}(σ, a[x])| ≺ η_t⁻¹ B_{t,0}^{n-2}`, every `σ`.  Long last leaf
(`σ_v ≠ σ_{v+1}`): the column sums of `Θ_t^{(+,-)}` are `≤ (1-t)⁻¹` (`(eq:THETAinftinf)`) and the root
sum is `KLindStepPin_holds` (`(eq:ind-step-bound)`, with its cancellation), loss `L^τ`.  Short last
leaf: the paper's displayed line does not cover it; `∑_x |Θ^{(s,s)}(x, b)| ≤ S` (property 5') and the
absolute bound `KLWardIneq_abs_sum_le`, no loss. -/
theorem KLWardIneq_Kpi_empty_bound (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d p.L),
      ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) ∅‖
        ≤ C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cl, hCl, hind⟩ := KLindStepPin_holds (k + 2) (m + 1) κ gmax hd (by omega) hκ hg hPT τ hτ
  obtain ⟨Cs, hCs, habs⟩ := KLWardIneq_abs_sum_le (k + 2) m κ gmax hd hm hκ hg hPT
  obtain ⟨S, hS0, hS⟩ := KLedge_l1 hκ hPT.short
  refine ⟨Cl + S * Cs, by positivity, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hB0 : 0 ≤ Bparam (k + 2) p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  have hBm : 0 ≤ (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := pow_nonneg hB0 _
  have hL1 := KLone_le_rpow p.hL hτ
  have hLτ0 : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hη := KLWardIneq_inv_le hκ p.hE p.ht1
  have hη0 : 0 < (Gauss.etaT p.E p.t)⁻¹ := inv_pos.2 (KLWardIneq_etaT_pos hκ p.hE p.ht1)
  have h1t : 0 < (1 - p.t)⁻¹ := inv_pos.2 (by linarith [p.ht1])
  by_cases hl : σ (Fin.last m) = σ (Fin.last m + 1)
  · -- a short last leaf
    have hcol : ∀ b : Zd (k + 2) p.L,
        ∑ x : Zd (k + 2) p.L, ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ (Fin.last m))
          (σ (Fin.last m + 1)) x b‖ ≤ S := by
      intro b
      rw [← hl]
      have hξ := norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 (σ (Fin.last m)) (σ (Fin.last m))
      unfold thetaEdge
      rw [KLWardIneq_col_eq_row p.hL hξ]
      exact hS p.L p.hL p.g p.hg0 p.hg1 p.E p.hE (σ (Fin.last m)) p.t p.ht0 p.ht1 b
    refine (KLWardIneq_sum_Kempty_le (mSigma p.E) p.t σ a hcol).trans ?_
    have hX : ∑ b : Zd (k + 2) p.L, ‖∑ δ ∈ Finset.univ.filter
        (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ (Fin.last m) = b),
          KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ Finset.univ.erase (Fin.last m),
              thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ Cs * (1 - p.t)⁻¹ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by
      refine le_trans ?_ (habs p σ a)
      calc _ ≤ ∑ b : Zd (k + 2) p.L, ∑ δ ∈ Finset.univ.filter
            (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ (Fin.last m) = b),
            ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖ :=
            Finset.sum_le_sum fun b _ => norm_sum_le _ _
        _ = _ := Finset.sum_fiberwise Finset.univ
            (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ (Fin.last m))
            (fun δ => ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖)
    calc S * ∑ b : Zd (k + 2) p.L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ (Fin.last m) = b),
            KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ S * (Cs * (1 - p.t)⁻¹ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left hX hS0.le
      _ ≤ S * (Cs * (Gauss.etaT p.E p.t)⁻¹ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1)) := by
          gcongr
      _ = (S * Cs) * 1 * (Gauss.etaT p.E p.t)⁻¹ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by
          ring
      _ ≤ (S * Cs) * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹
            * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by
          gcongr
      _ ≤ (Cl + S * Cs) * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹
            * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by
          have : 0 ≤ Cl * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹
              * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by positivity
          nlinarith [this]
  · -- a long last leaf
    refine (KLWardIneq_sum_Kempty_le (mSigma p.E) p.t σ a
      (fun b => KLWardIneq_col_thetaEdge_le p.hL hE2 p.ht0 p.ht1 _ _ b)).trans ?_
    have hroot := hind p σ (Fin.last m) hl a
    have e : m + 1 - 2 = m - 1 := by omega
    rw [e] at hroot
    calc (1 - p.t)⁻¹ * ∑ b : Zd (k + 2) p.L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (m + 1) → Zd (k + 2) p.L => δ (Fin.last m) = b),
            KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last m),
                thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ (1 - p.t)⁻¹ * (Cl * (p.L : ℝ) ^ τ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left hroot h1t.le
      _ ≤ (Gauss.etaT p.E p.t)⁻¹ * (Cl * (p.L : ℝ) ^ τ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1)) :=
          mul_le_mul_of_nonneg_right hη (by positivity)
      _ = Cl * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by
          ring
      _ ≤ (Cl + S * Cs) * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹
            * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by
          have : 0 ≤ S * Cs * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹
              * (Bparam (k + 2) p.L p.g p.t 0) ^ (m - 1) := by positivity
          nlinarith [this]

end EmptyBound

/-! ## 4. The cut with the last label summed -/

section CutLabels

variable {d L : ℕ}

/-- The inner labels at the non-root vertices do not see the last vertex `v = n - 1` of the polygon
(`i + k < j ≤ n - 1` for `k` below the root). -/
private theorem KLWardIneq_aIn_update {m : ℕ} (J : Fin (m + 1) × Fin (m + 1))
    (hJ : J.1.val < J.2.val) (a : Fin (m + 1) → Zd d L) (x : Zd d L)
    (i : Fin (KLwIn J + 1)) (hi : i ≠ Fin.last (KLwIn J)) :
    KLInduct_aIn J (Function.update a (Fin.last m) x) i = KLInduct_aIn J a i := by
  unfold KLInduct_aIn
  apply Function.update_of_ne
  intro h
  have h1 := congrArg Fin.val h
  have h2 : i.val < KLwIn J := by
    have := i.isLt
    rcases Nat.lt_or_ge i.val (KLwIn J) with h | h
    · exact h
    · exact absurd (Fin.ext (by simp [Fin.val_last]; omega)) hi
  have h3 := J.2.isLt
  simp only [KLwIn, Fin.val_last] at h1 h2
  omega

/-- The last vertex of the polygon is the last vertex of the outer polygon (it is not the glue vertex
`i < j ≤ n - 1`), with the same label: `a_out(a[x], w) = a_out(a, w)[x]`. -/
private theorem KLWardIneq_aOut_update {m : ℕ} (J : Fin (m + 1) × Fin (m + 1))
    (hJ : J.1.val < J.2.val) (a : Fin (m + 1) → Zd d L) (w x : Zd d L) :
    KLInduct_aOut J (Function.update a (Fin.last m) x) w
      = Function.update (KLInduct_aOut J a w) (Fin.last (m + 1 - KLwIn J)) x := by
  have h3 := J.2.isLt
  have hw1 : 1 ≤ KLwIn J := by simp only [KLwIn]; omega
  funext k
  by_cases hk : k = Fin.last (m + 1 - KLwIn J)
  · subst hk
    have hne : Fin.last (m + 1 - KLwIn J) ≠ KLglueV J := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, KLglueV] at this
      simp only [KLwIn] at this hw1
      omega
    unfold KLInduct_aOut
    rw [Function.update_of_ne hne, Function.update_self]
    have hcol : KLunCol J (m + 1 - KLwIn J) = m := by
      have hnot : ¬ (m + 1 - KLwIn J ≤ J.1.val) := by simp only [KLwIn]; omega
      unfold KLunCol
      simp only [hnot, ↓reduceIte]
      simp only [KLwIn]
      omega
    have : (⟨min (KLunCol J (Fin.last (m + 1 - KLwIn J)).val) (m + 1 - 1), by omega⟩ : Fin (m + 1))
        = Fin.last m := by
      apply Fin.ext
      simp only [Fin.val_last, hcol]
      omega
    rw [this, Function.update_self]
  · rw [Function.update_of_ne hk]
    unfold KLInduct_aOut
    by_cases hg : k = KLglueV J
    · subst hg
      simp
    · rw [Function.update_of_ne hg, Function.update_of_ne hg]
      apply Function.update_of_ne
      intro h
      have h1 := congrArg Fin.val h
      have h2 : k.val < m + 1 - KLwIn J := by
        have := k.isLt
        have hk' : k.val ≠ m + 1 - KLwIn J := fun h' => hk (Fin.ext (by simp [Fin.val_last]; omega))
        omega
      simp only [KLunCol, KLwIn] at h1 h2 hw1
      split_ifs at h1 <;> simp at h1 <;> omega

end CutLabels

/-! ## 5. The induction step: `(eq:K-pi-bound_partial)` for all `π` -/

section Step

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `∑_x |∑_{u,w} ξ A(u) S^{(B)}_{uw} K(w, x)| ≤ |ξ| (∑_u |A(u)|) M` when `∑_x |K(w, x)| ≤ M` for every
`w` (`∑_w |S^{(B)}_{uw}| = 1`): the summed last label stays in the outer factor. -/
private theorem KLWardIneq_norm_cut_sum_le (hL : 3 ≤ L) (ξ : ℂ) (A : Zd d L → ℂ)
    (K : Zd d L → Zd d L → ℂ) {M : ℝ} (hK : ∀ w, ∑ x, ‖K w x‖ ≤ M) :
    ∑ x : Zd d L, ‖∑ u : Zd d L, ∑ w : Zd d L, ξ * A u * SB d L g u w * K w x‖
      ≤ ‖ξ‖ * (∑ u : Zd d L, ‖A u‖) * M := by
  have hM : 0 ≤ M := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hK 0)
  calc ∑ x, ‖∑ u, ∑ w, ξ * A u * SB d L g u w * K w x‖
      ≤ ∑ x, ∑ u, ∑ w, ‖ξ‖ * ‖A u‖ * ‖SB d L g u w‖ * ‖K w x‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun u _ => ?_
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [norm_mul]
    _ = ∑ u, ∑ w, ‖ξ‖ * ‖A u‖ * ‖SB d L g u w‖ * ∑ x, ‖K w x‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ u, ∑ w, ‖ξ‖ * ‖A u‖ * ‖SB d L g u w‖ * M := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun w _ => ?_
        exact mul_le_mul_of_nonneg_left (hK w) (by positivity)
    _ = ‖ξ‖ * (∑ u, ‖A u‖) * M := by
        have hrow : ∀ u, ∑ w, ‖ξ‖ * ‖A u‖ * ‖SB d L g u w‖ * M = ‖ξ‖ * ‖A u‖ * M := fun u => by
          rw [← Finset.sum_mul, ← Finset.mul_sum, sum_norm_SB_row d L g hL u, mul_one]
        simp_rw [hrow]
        rw [Finset.mul_sum, Finset.sum_mul]

omit [NeZero L] in
/-- An innermost edge of `π`: no other edge of `π` inside its arc (copy of the private
`exists_innermost`, `KLSumZeroWard.lean:577`). -/
private theorem KLWardIneq_exists_innermost {n : ℕ} {π : Finset (Fin n × Fin n)}
    (hπ : π ⊆ diagonals n) (hne : π.Nonempty) :
    ∃ J ∈ π, ∀ e ∈ π, KLArcLe e J → e = J := by
  obtain ⟨J, hJ, hmin⟩ := π.exists_min_image KLarcWidth hne
  refine ⟨J, hJ, fun e he heJ => ?_⟩
  have hJd : IsDiag n J.1 J.2 := (Finset.mem_filter.1 (hπ hJ)).2
  have hed : IsDiag n e.1 e.2 := (Finset.mem_filter.1 (hπ he)).2
  have hw := hmin e he
  obtain ⟨h1, h2⟩ := heJ
  have hJ12 := hJd.1
  have he12 := hed.1
  simp only [KLarcWidth] at hw
  rw [Fin.le_def] at h1 h2
  rw [Fin.lt_def] at hJ12 he12
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero L] in
/-- The long edges of a tree are diagonals (copy of the private `Flong_subset_diagonals`). -/
private theorem KLWardIneq_Flong_subset_diagonals {n : ℕ} {F₀ : Finset (Fin n × Fin n)}
    (hF₀ : F₀ ∈ TSP n) (σ : Fin n → Bool) : KLFlong F₀ σ ⊆ diagonals n :=
  (Finset.filter_subset _ _).trans (Finset.mem_powerset.1 (Finset.mem_filter.1 hF₀).1)

/-- **`(eq:K-pi-bound_partial)` at the polygon with `n = m + 1` vertices** (the statement proved by
`KLWardIneq_Kpi_step`, `KLWardIneq_KpiAt_holds`): the sum over the last label `a_n = x`,
`∑_x |K^{(π)}(t,σ,a[x])| ≺ η_t⁻¹ B_{t,0}^{n-2}`, every `σ`, every `π`.  `n`, `κ`, `gmax` and `τ` are
fixed before the constant, which does not depend on `L`, `W`, `g`, `E`, `t`, `σ`, `π`, `a`. -/
def KLWardIneq_KpiAt (d m : ℕ) (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin (m + 1) → Bool)
    (π : Finset (Fin (m + 1) × Fin (m + 1))) (a : Fin (m + 1) → Zd d p.L),
    ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) π‖
      ≤ C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1)

/-- **The induction step** (strong induction on the number `n = m + 1` of polygon vertices, as
`KLKpi_step`): the bound at `n ≥ 3` follows from the bound at every `3 ≤ n'' < n`.  The layer `π = ∅`
is `KLWardIneq_Kpi_empty_bound`; a layer `π ≠ ∅` is cut at an innermost long edge (`KLKpi_cut`): the
inner polygon `k = j - i + 1 ∈ [3, n-1]` has root sum `≺ B^{k-2}` (`KLindStepPin_holds`, `L^{τ/2}`), the
summed last label `x` is the last label of the outer polygon (`n'' = n - (j - i) + 1 ∈ [3, n-1]`),
whose bound is `L^{τ/2} η_t⁻¹ B^{n''-2}`; `(k-2) + (n''-2) = n - 2`, `L^{τ/2} L^{τ/2} = L^τ`, and
`η_t⁻¹` appears exactly once. -/
theorem KLWardIneq_Kpi_step (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax)
    (hout : ∀ m'' : ℕ, 2 ≤ m'' → m'' < m → KLWardIneq_KpiAt d m'' κ gmax) :
    KLWardIneq_KpiAt d m κ gmax := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨C₀, hC₀, H₀⟩ := KLWardIneq_Kpi_empty_bound d m κ gmax hd hm hκ hg hPT τ hτ
  -- the inner constants (at `τ/2`) and the outer constants (at `τ/2`), one per width
  have hin : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (3 ≤ k → ∀ [NeZero k], ∀ (p : KLPar κ gmax)
      (σ : Fin k → Bool) (r : Fin k), σ r ≠ σ (r + 1) → ∀ a : Fin k → Zd d p.L,
        ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin k → Zd d p.L => δ r = b),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase r,
                thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
          ≤ C * (p.L : ℝ) ^ (τ / 2) * (Bparam d p.L p.g p.t 0) ^ (k - 2)) := by
    intro k
    by_cases hk : 3 ≤ k
    · have : NeZero k := ⟨by omega⟩
      obtain ⟨C, hC, H⟩ := KLindStepPin_holds d k κ gmax hd hk hκ hg hPT (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ => H⟩
    · exact ⟨1, one_pos, fun hk' => absurd hk' hk⟩
  have hout' : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (2 ≤ k → k < m → ∀ (p : KLPar κ gmax)
      (σ : Fin (k + 1) → Bool) (π : Finset (Fin (k + 1) × Fin (k + 1)))
      (a : Fin (k + 1) → Zd d p.L),
        ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last k) x) π‖
          ≤ C * (p.L : ℝ) ^ (τ / 2) * (Gauss.etaT p.E p.t)⁻¹
            * (Bparam d p.L p.g p.t 0) ^ (k - 1)) := by
    intro k
    by_cases hk : 2 ≤ k ∧ k < m
    · obtain ⟨C, hC, H⟩ := hout k hk.1 hk.2 (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ => H⟩
    · exact ⟨1, one_pos, fun h2 hlt => absurd ⟨h2, hlt⟩ hk⟩
  choose Ci hCi0 hCi using hin
  choose Co hCo0 hCo using hout'
  have hsum0 : 0 ≤ ∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le
  refine ⟨C₀ + ∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w), by positivity, ?_⟩
  intro p σ π a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hB0 : 0 ≤ Bparam d p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBm : 0 ≤ (Bparam d p.L p.g p.t 0) ^ (m - 1) := pow_nonneg hB0 _
  have hηpos : 0 < Gauss.etaT p.E p.t := KLWardIneq_etaT_pos hκ p.hE p.ht1
  have hη0 : 0 < (Gauss.etaT p.E p.t)⁻¹ := inv_pos.2 hηpos
  have hRHS : 0 ≤ (C₀ + ∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w)) * (p.L : ℝ) ^ τ
      * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1) := by positivity
  by_cases hπ0 : π = ∅
  · -- the layer `π = ∅`
    subst hπ0
    refine (H₀ p σ a).trans ?_
    have : 0 ≤ (∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w)) * (p.L : ℝ) ^ τ
        * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1) := by positivity
    nlinarith [this]
  rcases (KLTSPlong (m + 1) σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · -- no tree has the long edges `π`
    have hz : ∀ x : Zd d p.L,
        KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) π = 0 := fun x => by
      simp only [KLKpi, hemp, Finset.sum_empty, mul_zero]
    simp only [hz, norm_zero, Finset.sum_const_zero]
    exact hRHS
  obtain ⟨hF₀T, hπ⟩ := Finset.mem_filter.1 hF₀
  have hsub : π ⊆ diagonals (m + 1) := by
    rw [← hπ]; exact KLWardIneq_Flong_subset_diagonals hF₀T σ
  obtain ⟨J, hJ, hinner⟩ :=
    KLWardIneq_exists_innermost hsub (Finset.nonempty_iff_ne_empty.2 hπ0)
  have hJd : IsDiag (m + 1) J.1 J.2 := (Finset.mem_filter.1 (hsub hJ)).2
  have hJlong : σ J.1 ≠ σ J.2 := by
    have hJ' : J ∈ KLFlong F₀ σ := by rw [hπ]; exact hJ
    exact (Finset.mem_filter.1 hJ').2
  obtain ⟨hJ12, hJadj, hJwhole⟩ := hJd
  rw [Fin.lt_def] at hJ12
  have hJ2n := J.2.isLt
  have hw2 : 2 ≤ KLwIn J := by simp only [KLwIn]; omega
  have hwn : KLwIn J + 2 ≤ m + 1 := by
    simp only [KLwIn]
    by_cases h0 : J.1.val = 0
    · have : J.2.val ≠ m + 1 - 1 := fun h => hJwhole ⟨h0, h⟩
      omega
    · omega
  have hm' : ∀ s s' : Bool, ‖(p.t : ℂ) * (mSigma p.E s * mSigma p.E s')‖ < 1 := fun s s' =>
    norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 s s'
  -- the inner root sum, independent of the last label
  set A : Zd d p.L → ℂ := fun u => ∑ δ ∈ Finset.univ.filter
      (fun δ : Fin (KLwIn J + 1) → Zd d p.L => δ (Fin.last (KLwIn J)) = u),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t (sigmaIn σ J) ∅ δ *
          ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            thetaEdge d p.L p.g (mSigma p.E) p.t (sigmaIn σ J i) (sigmaIn σ J (i + 1))
              (KLInduct_aIn J a i) (δ i) with hAdef
  have hcut : ∀ x : Zd d p.L,
      KLKpi d p.L p.g (mSigma p.E) p.t σ (Function.update a (Fin.last m) x) π
        = ∑ u : Zd d p.L, ∑ w : Zd d p.L, (p.t : ℂ) * A u * SB d p.L p.g u w *
            KLKpi d p.L p.g (mSigma p.E) p.t (sigmaOut σ J)
              (Function.update (KLInduct_aOut J a w) (Fin.last (m + 1 - KLwIn J)) x)
              ((π.erase J).image (KLshiftOut J)) := by
    intro x
    rw [KLKpi_cut d p.L p.g p.hL hn (mSigma p.E) p.t hm' σ hF₀T hπ hJ hinner
      (Function.update a (Fin.last m) x)]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [KLWardIneq_aOut_update J hJ12 a w x]
    have hAx : (∑ δ ∈ Finset.univ.filter
        (fun δ : Fin (KLwIn J + 1) → Zd d p.L => δ (Fin.last (KLwIn J)) = u),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t (sigmaIn σ J) ∅ δ *
            ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
              thetaEdge d p.L p.g (mSigma p.E) p.t (sigmaIn σ J i) (sigmaIn σ J (i + 1))
                (KLInduct_aIn J (Function.update a (Fin.last m) x) i) (δ i)) = A u := by
      refine Finset.sum_congr rfl fun δ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [KLWardIneq_aIn_update J hJ12 a x i (Finset.ne_of_mem_erase hi)]
    rw [hAx]
  have hB : ∀ w : Zd d p.L, ∑ x : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t (sigmaOut σ J)
      (Function.update (KLInduct_aOut J a w) (Fin.last (m + 1 - KLwIn J)) x)
      ((π.erase J).image (KLshiftOut J))‖
        ≤ Co (m + 1 - KLwIn J) * (p.L : ℝ) ^ (τ / 2) * (Gauss.etaT p.E p.t)⁻¹ *
          (Bparam d p.L p.g p.t 0) ^ (m + 1 - KLwIn J - 1) := fun w =>
    hCo (m + 1 - KLwIn J) (by omega) (by omega) p (sigmaOut σ J) _ (KLInduct_aOut J a w)
  have hroot : sigmaIn σ J (Fin.last (KLwIn J)) ≠ sigmaIn σ J (Fin.last (KLwIn J) + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last (KLwIn J)) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last]
      congr 1
      ext
      simp only [KLwIn]
      omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]
      congr 1
      ext
      simp only
      omega
    rw [e1, e2]
    exact Ne.symm hJlong
  have hA : ∑ u : Zd d p.L, ‖A u‖
      ≤ Ci (KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) * (Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2) :=
    hCi (KLwIn J + 1) (by omega) p (sigmaIn σ J) (Fin.last (KLwIn J)) hroot (KLInduct_aIn J a)
  have hξ : ‖((p.t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg p.ht0]; exact p.ht1.le
  simp only [hcut]
  refine (KLWardIneq_norm_cut_sum_le p.hL _ _ _ hB).trans ?_
  have hM0 : 0 ≤ Co (m + 1 - KLwIn J) * (p.L : ℝ) ^ (τ / 2) * (Gauss.etaT p.E p.t)⁻¹ *
      (Bparam d p.L p.g p.t 0) ^ (m + 1 - KLwIn J - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hCo0 _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      hη0.le) (pow_nonneg hB0 _)
  have hsumA : 0 ≤ ∑ u : Zd d p.L, ‖A u‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpow : (Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2) *
      (Bparam d p.L p.g p.t 0) ^ (m + 1 - KLwIn J - 1) = (Bparam d p.L p.g p.t 0) ^ (m - 1) := by
    rw [← pow_add]; congr 1; omega
  have hLL : (p.L : ℝ) ^ (τ / 2) * (p.L : ℝ) ^ (τ / 2) = (p.L : ℝ) ^ τ := by
    rw [← Real.rpow_add (by exact_mod_cast (by have := p.hL; omega : 0 < p.L)), add_halves]
  have hterm : Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)
      ≤ ∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w) :=
    Finset.single_le_sum (f := fun w => Ci (w + 1) * Co (m + 1 - w))
      (fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le) (Finset.mem_range.2 (by omega))
  calc ‖((p.t : ℝ) : ℂ)‖ * (∑ u : Zd d p.L, ‖A u‖) *
        (Co (m + 1 - KLwIn J) * (p.L : ℝ) ^ (τ / 2) * (Gauss.etaT p.E p.t)⁻¹ *
          (Bparam d p.L p.g p.t 0) ^ (m + 1 - KLwIn J - 1))
      ≤ 1 * (Ci (KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) *
            (Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2)) *
          (Co (m + 1 - KLwIn J) * (p.L : ℝ) ^ (τ / 2) * (Gauss.etaT p.E p.t)⁻¹ *
            (Bparam d p.L p.g p.t 0) ^ (m + 1 - KLwIn J - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hξ hA hsumA zero_le_one) hM0
    _ = (Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)) *
          ((p.L : ℝ) ^ (τ / 2) * (p.L : ℝ) ^ (τ / 2)) * (Gauss.etaT p.E p.t)⁻¹ *
          ((Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2) *
            (Bparam d p.L p.g p.t 0) ^ (m + 1 - KLwIn J - 1)) := by ring
    _ = (Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)) * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ *
          (Bparam d p.L p.g p.t 0) ^ (m - 1) := by rw [hLL, hpow]
    _ ≤ (C₀ + ∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w)) * (p.L : ℝ) ^ τ *
          (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1) := by
        have h1 : Ci (KLwIn J + 1) * Co (m + 1 - KLwIn J)
            ≤ C₀ + ∑ w ∈ range (m + 1), Ci (w + 1) * Co (m + 1 - w) := by linarith
        gcongr

/-- **`(eq:K-pi-bound_partial)` is proved** for every `n = m + 1 ≥ 3`, every `π`: strong induction on `m`
with `KLWardIneq_Kpi_step`; the only hypothesis is the local propagator shapes `KLPT d κ gmax`. -/
theorem KLWardIneq_KpiAt_holds (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLWardIneq_KpiAt d m κ gmax := by
  have key : ∀ m : ℕ, 2 ≤ m → KLWardIneq_KpiAt d m κ gmax := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      exact KLWardIneq_Kpi_step d m κ gmax hd hm hκ hg hPT (fun m'' h2 hlt => ih m'' hlt h2)
  exact key m hm

/-- **`(wardineq_K)` at `n = 2`**: `∑_x |𝒦^{(2)}(σ, (a₁, x))| = W^{-d} ∑_x |Θ_{t m₁ m₂}(a₁, x)| ≤
W^{-d} (1-t)⁻¹ ≤ (W^d η_t)⁻¹`, every `σ` (`KLK_two`; `KLward_two` is the equality for `σ = (s, -s)`). -/
theorem KLWardIneq_At_two (d : ℕ) {κ gmax : ℝ} (hκ : 0 < κ) : KLwardIneqAt d 2 κ gmax := by
  intro τ hτ
  refine ⟨1, one_pos, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hμ : ‖mSigma p.E (σ 0) * mSigma p.E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, mul_one]
  have hloop : ∀ x : Zd d p.L,
      (⟨List.ofFn σ, List.ofFn a ++ [x]⟩ : LoopIdx (Zd d p.L)) = ⟨[σ 0, σ 1], [a 0, x]⟩ := by
    intro x
    simp [List.ofFn_succ]
  simp only [hloop, KLK_two, norm_mul, hμ, mul_one, norm_inv, norm_pow, Complex.norm_natCast]
  have hW0 : 0 ≤ ((p.W : ℝ) ^ d)⁻¹ := by positivity
  have hrow : ∑ x : Zd d p.L,
      ‖Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 0) * mSigma p.E (σ 1))) (a 0) x‖
        ≤ (1 - p.t)⁻¹ := sum_norm_Theta_row_le p.hL p.ht0 p.ht1 hμ (a 0)
  have hη := KLWardIneq_inv_le hκ p.hE p.ht1
  have hηpos := KLWardIneq_etaT_pos hκ p.hE p.ht1
  have hL1 := KLone_le_rpow p.hL hτ
  rw [← Finset.mul_sum]
  change ((p.W : ℝ) ^ d)⁻¹ * _ ≤ 1 * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d) * Gauss.etaT p.E p.t)⁻¹ *
    (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (2 - 2)
  rw [show (2 : ℕ) - 2 = 0 from rfl, pow_zero, mul_one, one_mul, mul_inv]
  calc ((p.W : ℝ) ^ d)⁻¹ * ∑ x : Zd d p.L,
        ‖Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 0) * mSigma p.E (σ 1))) (a 0) x‖
      ≤ ((p.W : ℝ) ^ d)⁻¹ * (Gauss.etaT p.E p.t)⁻¹ :=
        mul_le_mul_of_nonneg_left (hrow.trans hη) hW0
    _ = 1 * (((p.W : ℝ) ^ d)⁻¹ * (Gauss.etaT p.E p.t)⁻¹) := (one_mul _).symm
    _ ≤ (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d)⁻¹ * (Gauss.etaT p.E p.t)⁻¹) :=
        mul_le_mul_of_nonneg_right hL1 (by positivity)

/-- **`(wardineq_K)` for `n = m + 1 ≥ 3`, from the layers**: `(eq_K-Kpi)` (`KLK_eq_sum_Kpi`) gives the
prefactor `W^{-d(n-1)}`, the same for every `π`, times the sum over the `2^{|diagonals n|}` layers, each
`∑_x |K^{(π)}| ≺ η_t⁻¹ B^{n-2}` (`KLWardIneq_KpiAt_holds`): `(W^d)^{-(n-1)} η_t⁻¹ B^{n-2} =
(W^d η_t)⁻¹ (W^{-d} B)^{n-2}`. -/
theorem KLWardIneq_At_of_Kpi (d m : ℕ) (κ gmax : ℝ) (hd : 3 ≤ d) (hm : 2 ≤ m) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLwardIneqAt d (m + 1) κ gmax := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := KLWardIneq_KpiAt_holds d m κ gmax hd hm hκ hg hPT τ hτ
  refine ⟨2 ^ (diagonals (m + 1)).card * C, by positivity, ?_⟩
  intro p σ a
  have hB0 : 0 ≤ Bparam d p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW0 : 0 ≤ ((p.W : ℝ) ^ d)⁻¹ := by positivity
  have hηpos := KLWardIneq_etaT_pos hκ p.hE p.ht1
  have hloop : ∀ x : Zd d p.L,
      (⟨List.ofFn σ, List.ofFn a ++ [x]⟩ : LoopIdx (Zd d p.L))
        = KLloopOf d p.L σ (Fin.snoc (α := fun _ => Zd d p.L) a x) := by
    intro x
    simp only [KLloopOf]
    congr 1
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  have hterm : ∀ x : Zd d p.L,
      ‖KLK d p.L p.g p.W p.E p.t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
        ≤ ((p.W : ℝ) ^ d)⁻¹ ^ m * ∑ π ∈ (diagonals (m + 1)).powerset,
            ‖KLKpi d p.L p.g (mSigma p.E) p.t σ
              (Function.update (Fin.snoc (α := fun _ => Zd d p.L) a 0) (Fin.last m) x) π‖ := by
    intro x
    rw [hloop, KLK_eq_sum_Kpi d p.L p.g p.W p.E p.t (by omega) σ _, norm_mul, norm_pow, norm_inv,
      norm_pow, Complex.norm_natCast, Nat.add_sub_cancel, Fin.update_snoc_last]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hW0 _)
  calc ∑ x : Zd d p.L, ‖KLK d p.L p.g p.W p.E p.t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
      ≤ ∑ x : Zd d p.L, ((p.W : ℝ) ^ d)⁻¹ ^ m * ∑ π ∈ (diagonals (m + 1)).powerset,
            ‖KLKpi d p.L p.g (mSigma p.E) p.t σ
              (Function.update (Fin.snoc (α := fun _ => Zd d p.L) a 0) (Fin.last m) x) π‖ :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = ((p.W : ℝ) ^ d)⁻¹ ^ m * ∑ π ∈ (diagonals (m + 1)).powerset, ∑ x : Zd d p.L,
            ‖KLKpi d p.L p.g (mSigma p.E) p.t σ
              (Function.update (Fin.snoc (α := fun _ => Zd d p.L) a 0) (Fin.last m) x) π‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((p.W : ℝ) ^ d)⁻¹ ^ m * ∑ _π ∈ (diagonals (m + 1)).powerset,
            C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π _ => H p σ π _) (pow_nonneg hW0 _)
    _ = ((p.W : ℝ) ^ d)⁻¹ ^ m * (2 ^ (diagonals (m + 1)).card *
            (C * (p.L : ℝ) ^ τ * (Gauss.etaT p.E p.t)⁻¹ * (Bparam d p.L p.g p.t 0) ^ (m - 1))) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        ring
    _ = 2 ^ (diagonals (m + 1)).card * C * (p.L : ℝ) ^ τ *
          (((p.W : ℝ) ^ d) * Gauss.etaT p.E p.t)⁻¹ *
          (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (m + 1 - 2) := by
        have e : m + 1 - 2 = m - 1 := by omega
        have hpow : ((p.W : ℝ) ^ d)⁻¹ ^ m = ((p.W : ℝ) ^ d)⁻¹ ^ (m - 1) * ((p.W : ℝ) ^ d)⁻¹ := by
          rw [← pow_succ]; congr 1; omega
        rw [e, mul_inv, mul_pow, hpow]
        ring

/-- **The pin `lem_wardineq_K`, `(wardineq_K)`, is proved**: `max_σ ∑_{a_n} |𝒦^{(n)}_{t,σ,a}| ≺
(W^d η_t)⁻¹ (W^{-d} B_{t,0})^{n-2}` for every `n ≥ 2`, uniformly in `t ∈ [0,1)`, conditional only on the
local propagator shapes `KLPT d κ gmax`: `n = 2` by `KLWardIneq_At_two` (`KLK_two`), `n ≥ 3` by
`KLWardIneq_At_of_Kpi` (`(eq_K-Kpi)` and the induction of `KLWardIneq_KpiAt_holds`). -/
theorem KLwardIneqPin_holds : KLwardIneqPin := by
  intro d n κ gmax hd hn hκ hg hPT
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
  · exact KLWardIneq_At_two d hκ
  · exact KLWardIneq_At_of_Kpi d m κ gmax hd hm hκ hg hPT

end Step

/-! ## 6. The compiled instances: `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`

The parameter point is `KLinstPar` of `KLTree.lean` (`κ = gmax = 1`, `η_t = 1/10`, `B_{t,0} = 514/175`);
`KLPT 3 1 1` (the shapes of `lem_propTH`, another gate's pin) stays a hypothesis of the examples, every
other hypothesis is discharged at the data.  Charges `(+,-,+)` (`n = 3`: the last leaf is short, case (S)),
`(+,+,-,-)` (`n = 4`: the last leaf is long, case (L); both diagonals are long, case (C)), spread labels in
`Z_5^3`; the last label is summed. -/

section Instances

/-- Target 3, `KLwardIneqPin_holds` at `n = 2, 3, 4`: `∑_x |𝒦^{(n)}(σ, (a, x))| ≤ C L^τ (W^d η_t)⁻¹
(W^{-d} B_{t,0})^{n-2}` at `σ = (+,-)`, `(+,-,+)`, `(+,+,-,-)` with spread labels. -/
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn ![true, false], List.ofFn ![KLinsta 0] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn KLinstσ, List.ofFn ![KLinsta 0, KLinsta 1] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn KLInduct_instσ,
            List.ofFn ![KLInduct_insta 0, KLInduct_insta 1, KLInduct_insta 2] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLwardIneqPin_holds 3 2 1 1 (by norm_num) (by norm_num) one_pos one_pos
      hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar ![true, false] ![KLinsta 0]⟩
  · obtain ⟨C, hC, H⟩ := KLwardIneqPin_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos
      hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLinstσ ![KLinsta 0, KLinsta 1]⟩
  · obtain ⟨C, hC, H⟩ := KLwardIneqPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos
      hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLInduct_instσ
      ![KLInduct_insta 0, KLInduct_insta 1, KLInduct_insta 2]⟩

/-- Target 2, `(eq:K-pi-bound_partial)` (`KLWardIneq_KpiAt_holds`) at `n = 4` and the three layers
`π = ∅`, `π = {(0,2)}`, `π = {(1,3)}` of `σ = (+,+,-,-)`, and at `n = 3` (`π = ∅`, the only layer of the
triangle): one constant serves the layers of one `n`.  `KLPT 3 1 1` is the only hypothesis left. -/
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      (∑ x : Zd 3 5, ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ
            (Function.update KLInduct_insta (Fin.last 3) x) ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Gauss.etaT 0 (9 / 10))⁻¹ *
          (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1)) ∧
      (∑ x : Zd 3 5, ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ
            (Function.update KLInduct_insta (Fin.last 3) x) {((0 : Fin 4), (2 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Gauss.etaT 0 (9 / 10))⁻¹ *
          (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1)) ∧
      (∑ x : Zd 3 5, ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ
            (Function.update KLInduct_insta (Fin.last 3) x) {((1 : Fin 4), (3 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Gauss.etaT 0 (9 / 10))⁻¹ *
          (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ
            (Function.update KLinsta (Fin.last 2) x) ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Gauss.etaT 0 (9 / 10))⁻¹ *
          (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 1)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLWardIneq_KpiAt_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos
      one_pos hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLInduct_instσ ∅ KLInduct_insta,
      H KLinstPar KLInduct_instσ {((0 : Fin 4), (2 : Fin 4))} KLInduct_insta,
      H KLinstPar KLInduct_instσ {((1 : Fin 4), (3 : Fin 4))} KLInduct_insta⟩
  · obtain ⟨C, hC, H⟩ := KLWardIneq_KpiAt_holds 3 2 1 1 (by norm_num) (by norm_num) one_pos
      one_pos hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLinstσ ∅ KLinsta⟩

/-- Target 2, `KLWardIneq_Kpi_step` (and `KLWardIneq_Kpi_empty_bound` for the layer `π = ∅`) at `n = 4`:
the induction hypothesis at `n'' = 3` is the proved `KLWardIneq_KpiAt_holds`, so `KLPT 3 1 1` is the only
hypothesis left. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ
            (Function.update KLInduct_insta (Fin.last 3) x) {((0 : Fin 4), (2 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Gauss.etaT 0 (9 / 10))⁻¹ *
          (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1) := by
  obtain ⟨C, hC, H⟩ := KLWardIneq_Kpi_step 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    (fun m'' h2 hlt => KLWardIneq_KpiAt_holds 3 m'' 1 1 (by norm_num) h2 one_pos one_pos hPT)
    1 one_pos
  exact ⟨C, hC, H KLinstPar KLInduct_instσ {((0 : Fin 4), (2 : Fin 4))} KLInduct_insta⟩

example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ
            (Function.update KLInduct_insta (Fin.last 3) x) ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Gauss.etaT 0 (9 / 10))⁻¹ *
          (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1) := by
  obtain ⟨C, hC, H⟩ := KLWardIneq_Kpi_empty_bound 3 3 1 1 (by norm_num) (by norm_num) one_pos
    one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar KLInduct_instσ KLInduct_insta⟩

/-- The pin `KLwardIneqAt` is nonempty at `n = 3` and `n = 4` (the shape `∀ τ, ∃ C, …` with `τ = 1`). -/
example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
  ⟨KLwardIneqPin_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT,
    KLwardIneqPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT⟩

/-- `KLWardIneq_At_two` and `KLWardIneq_At_of_Kpi` directly: `n = 2` with equal charges `(+,+)` (the case
`KLward_two` does not cover; no hypothesis is left), and `KLwardIneqAt` at `n = 3`, `n = 4` from the layers. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn ![true, true], List.ofFn ![KLinsta 0] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 2) := by
  obtain ⟨C, hC, H⟩ := KLWardIneq_At_two 3 (κ := 1) (gmax := 1) one_pos 1 one_pos
  exact ⟨C, hC, H KLinstPar ![true, true] ![KLinsta 0]⟩

example (hPT : KLPT 3 1 1) : KLwardIneqAt 3 3 1 1 ∧ KLwardIneqAt 3 4 1 1 :=
  ⟨KLWardIneq_At_of_Kpi 3 2 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT,
    KLWardIneq_At_of_Kpi 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT⟩

end Instances

end RBM.Loop
