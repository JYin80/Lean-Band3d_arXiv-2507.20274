/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Instances.Matrix
import RBM3D.Gauss.DominationAt
import RBM3D.Gauss.FineModel
import RBM3D.Gauss.LinearForm
import RBM3D.Green.EntryCore

/-!
# Row independence of the Gaussian entries; the row LDE as a high-probability bound

Ticket T2038 (S1-11).  Port of `RBM2D/Green/RowIndep.lean` at commit `c9a24cf` (lines 56-1418: the
file up to its private `Checks` section, lines 1420-1659; the `#print axioms` lines are not ported)
to the fine lattice `Z_{WL}^d`.  The file is itself a port of `RBM1D/Gauss/RowIndep.lean`
(RBM1D `86573b9`).  The paper (arXiv:2507.20274) does not state this file as a lemma:
`paper/tex/3_5_Loop_Hierarchy.tex:37` says that the estimates of `lem_GbEXP` (Lemma 4.1 of
`[YY_25]` for `d = 1`) are dimension-independent and use "standard arguments based on resolvent
identities and large deviation estimates".  The row large-deviation events `LDERow` of
`Green/EntryCore.lean` are those large deviation estimates, and their high-probability bound is
the content here.

The mathematics: `G^{(i)}`, the resolvent with row and column `i` removed, and every coefficient
`C` that reads only the coordinates off row `i`, are independent of the Gaussian entries
`H_{ik}`, `k ≠ i`, that multiply them.  Conditionally on the off-row block the row sum
`∑_{k≠i} H_{ik} C_k` is a centred circular complex Gaussian of variance
`V = u ∑_{k≠i} S_{ik} ‖C_k‖²`, so `E (‖·‖²/V)^p = p! ≤ 2 (2p-1)!!`; Markov and a union over an index
set of size `≤ N^{Ccard}`, `N = (W L)^d`, give `‖∑ H_{ik} C_k‖² ≤ N^{2τ} V` with probability
`≥ 1 - N^{-D}`.  No exponent of the argument depends on `d`; the dimension enters only through the
index type `Idx d L W`, the cardinality `N = (W L)^d` (`Sizes.card_Idx`), and the variance profile
`svarF d L W g`, which carries the coupling `g = sz.lam n`.

## Main statements

* `AgreeOffRow`, `Xentry_congr_of_ne`, `Hflow_submatrix_congr`: the minor reads only off-row
  coordinates.
* `rowSet`, `indepFun_rowSet`, `rowCoord`, `Xentry_eq_rowCoord`, `offRowCoord`,
  `Hflow_submatrix_congr_offRowCoord`, `row_sum_congr`: the row block `{(i,k,b), (k,i,b)}` is
  independent of the off-row block, and the row sum reads only the two.
* `integral_norm_row_sum_pow_le`: frozen coefficients,
  `E‖∑_{k≠i} H_{ik} c_k‖^{2p} ≤ 2 (2p-1)!! (u ∑_{k≠i} S_{ik} ‖c_k‖²)^p`.
* `integral_norm_rowSum_pow_le`, `integral_norm_rowSum_norm_pow_le'`: coefficients reading only the
  off-row block (conditionally Gaussian row sum), and the normalised form with constant bound.
* `minorCol`, `minorRowConj`, `ldeRowLHS_eq`, `rowVarSum_eq`: the minor-resolvent columns and the
  alignment with `ldeRowLHS`, `ldeRowRHS` of `Green/EntryCore.lean`.
* `stochDom_rowSum_general`, `highProb_norm_rowSum_sq_le`: the row LDE as `StochDomAt` and
  `HighProbAt` along a size sequence with `N → ∞`.

* T2389 (BA-G2): `RowIndep_minorColD`, `RowIndep_minorRowConjD` and their measurability, off-row determination
  and alignment lemmas (`RowIndep_*`) for the resolvent of `D + X`, `D` a deterministic matrix (the block
  Anderson hopping `g₀ Ψ`): the section "The shifted minor resolvent".  The band declarations are unchanged.

## Renaming (RBM2D `c9a24cf` → here; `docs/tickets/ST1-COMMON.md` item 2)

R1 `d : Sizes` → `sz : Sizes d` (the dimension `d` is the implicit parameter of `Sizes d`);
R2 `Idx L W` → `Idx d L W`; R3 the cardinality `d.size n = (W L)^2` → `sz.size n = (W L)^d`
(`Sizes.card_Idx`); R4 `Coord`, `svar` → `CoordF`, `svarF d L W (sz.lam n)`.  The probability layer
is the merged MD layer: `Sizes.seqP`, `Sizes.seqHflow`, `LinearForm.{linVar, map_lin, glue, …}`,
`stochDomAt_of_momentDomAt`, `StochDomAt`, `HighProbAt`.  The Gaussian-moment helpers are private
copies, as in RBM2D; the double factorial is `RowIndep_dfac`.

## Differences from RBM2D (residual, after the renaming)

* the variance in `rowVarSum` and the statements is `svarF d L W (sz.lam n)`, which carries the
  coupling (RBM2D's fixed five-point profile `svar L W` has none);
* the private `one_le_size` of RBM2D is the merged `Sizes.one_le_size`; the `Z2` unfolding in
  `card_LdeIdx_le` is `Sizes.card_Idx`;
* `gvar_offDiag` of RBM2D (public) is a private copy `rowIndep_gvarF_offDiag` (the merged
  `fineModel_gvarF_offDiag` is private to `FineModel.lean`);
* the private `Checks` section of RBM2D (`checkSizes`, `green_diag_ne_zero`, `check_*`, `growSizes`)
  is replaced by the instances `RBM.Green.RowIndepInst.*` at `SizesInst.sz0` at the end of this
  file; the RBM1D check
  `greenMinor_congr_of_offRow` is not ported (it is private, and its hypotheses `green_diag_ne_zero`
  need `im_green_apply_self`, which is not merged).
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory RBM.Gauss RBM.Gauss.LinearForm
open scoped NNReal ENNReal

/-! ### Gaussian moments (private ports of RBM1D `Gauss/Moments.lean` lines 27-115 and
`Gauss/LinearForm.lean` lines 118-176, commit `86573b9`) -/

section Moments

/-- Every polynomial is integrable against a real Gaussian. -/
private theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Transfer integrability from the Gaussian measure to the density form used by
`RBM.integral_mul_gaussianReal`. -/
private theorem integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

/-- **The Stein recursion for the even moments**: `E[X^{2p+2}] = (2p+1) v E[X^{2p}]`. -/
private theorem integral_pow_gaussianReal_succ (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p + 2) ∂(gaussianReal 0 v)
      = (2 * p + 1) * (v : ℝ) * ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, integral_dirac, integral_dirac]
    simp
  have hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * p + 1))
      ((2 * p + 1 : ℕ) * x ^ (2 * p)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * p + 1) x
  have h1 : Integrable fun x : ℝ =>
      x ^ (2 * p + 1) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) := by
    have := integrable_mul_gaussianPDFReal hv
      (g := fun x : ℝ => -((v : ℝ)⁻¹) * x ^ (2 * p + 2))
      (((integrable_pow_gaussianReal v (2 * p + 2)).const_mul _))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    field_simp
    ring
  have h2 : Integrable fun x : ℝ =>
      ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv
      ((integrable_pow_gaussianReal v (2 * p)).const_mul _)
  have h3 : Integrable fun x : ℝ => x ^ (2 * p + 1) * gaussianPDFReal 0 v x :=
    integrable_mul_gaussianPDFReal hv (integrable_pow_gaussianReal v (2 * p + 1))
  have h := integral_mul_gaussianReal hv hf h1 h2 h3
  rw [show (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x : ℝ => x ^ (2 * p + 2) from by
    funext x; ring] at h
  rw [h, integral_const_mul]
  push_cast
  ring

/-- **The even moments of a centred real Gaussian**: `E[X^{2p}] = (2p-1)!!·v^p`, with the
double factorial written as `∏_{i<p} (2i+1)`. -/
private theorem integral_pow_gaussianReal (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v)
      = (∏ i ∈ Finset.range p, (2 * (i : ℝ) + 1)) * (v : ℝ) ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 2 from by ring, integral_pow_gaussianReal_succ, ih,
      Finset.prod_range_succ]
    ring

/-- The double factorial `(2p-1)!! = ∏_{i<p} (2i+1)`, the `2p`-th moment of a standard
Gaussian.  (RBM1D `Gauss/Moments.lean` `dfac`; public because it occurs in the statements of the
moment bounds below.) -/
noncomputable def RowIndep_dfac (p : ℕ) : ℝ := ∏ i ∈ Finset.range p, (2 * (i : ℝ) + 1)

@[simp] theorem RowIndep_dfac_zero : RowIndep_dfac 0 = 1 := by simp [RowIndep_dfac]

theorem RowIndep_dfac_succ (p : ℕ) :
    RowIndep_dfac (p + 1) = (2 * (p : ℝ) + 1) * RowIndep_dfac p := by
  rw [RowIndep_dfac, RowIndep_dfac, Finset.prod_range_succ, mul_comm]

private theorem integral_pow_gaussianReal' (v : ℝ≥0) (p : ℕ) :
    ∫ x : ℝ, x ^ (2 * p) ∂(gaussianReal 0 v) = RowIndep_dfac p * (v : ℝ) ^ p :=
  integral_pow_gaussianReal v p

section MomentBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} {X : ι → Ω → ℝ} {v : ι → ℝ≥0}

/-- All even moments of a linear form exist. -/
private theorem integrable_pow_lin (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P)
    (a : ι → ℝ) (s : Finset ι) (p : ℕ) :
    Integrable (fun ω => (∑ i ∈ s, a i * X i ω) ^ (2 * p)) P := by
  classical
  have hm := measurable_lin hmeas a s
  have h := integrable_pow_gaussianReal (linVar v a s) (2 * p)
  rw [← map_lin hmeas hlaw hindep a s] at h
  exact (integrable_map_measure ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
    hm.aemeasurable).1 h

/-- **The even moments of a linear form**: `E[(∑ a_i X_i)^{2p}] = (2p-1)!! (∑ a_i² v_i)^p`. -/
private theorem integral_pow_lin (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P)
    (a : ι → ℝ) (s : Finset ι) (p : ℕ) :
    ∫ ω, (∑ i ∈ s, a i * X i ω) ^ (2 * p) ∂P = RowIndep_dfac p * (linVar v a s : ℝ) ^ p := by
  classical
  have hm := measurable_lin hmeas a s
  have h := integral_map (μ := P) (φ := fun ω => ∑ i ∈ s, a i * X i ω)
    (f := fun y : ℝ => y ^ (2 * p)) hm.aemeasurable
    ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
  rw [map_lin hmeas hlaw hindep a s] at h
  rw [← h, integral_pow_gaussianReal']

/-- **The moment bound for the modulus of a complex linear form.**  If `Y = ∑ a_i X_i` and
`Y' = ∑ b_i X_i` are the real and imaginary parts, then
`E[(Y² + Y'²)^p] ≤ 2^p (2p-1)!! (V_a^p + V_b^p)`; in the circular case `V_a = V_b = σ²/2` this
is `E‖Z‖^{2p} ≤ (2p-1)!! σ^{2p}`. -/
private theorem integral_sq_add_sq_pow_le (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P)
    (a b : ι → ℝ) (s : Finset ι) (p : ℕ) :
    ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ 2 ^ p * (RowIndep_dfac p * ((linVar v a s : ℝ) ^ p + (linVar v b s : ℝ) ^ p)) := by
  classical
  have hia := integrable_pow_lin hmeas hlaw hindep a s p
  have hib := integrable_pow_lin hmeas hlaw hindep b s p
  have hpt : ∀ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p
      ≤ 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p) + (∑ i ∈ s, b i * X i ω) ^ (2 * p)) := by
    intro ω
    set x := (∑ i ∈ s, a i * X i ω) ^ 2 with hx
    set y := (∑ i ∈ s, b i * X i ω) ^ 2 with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hmax : x + y ≤ 2 * max x y := by
      rcases le_total x y with h | h
      · simp [max_eq_right h]; linarith
      · simp [max_eq_left h]; linarith
    have h1 : (x + y) ^ p ≤ (2 * max x y) ^ p :=
      pow_le_pow_left₀ (by positivity) hmax p
    have h2 : (2 * max x y) ^ p = 2 ^ p * max x y ^ p := by rw [mul_pow]
    have h3 : max x y ^ p ≤ x ^ p + y ^ p := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]
        have : (0 : ℝ) ≤ x ^ p := by positivity
        linarith
      · rw [max_eq_left h]
        have : (0 : ℝ) ≤ y ^ p := by positivity
        linarith
    have hxp : x ^ p = (∑ i ∈ s, a i * X i ω) ^ (2 * p) := by
      rw [hx, ← pow_mul]
    have hyp : y ^ p = (∑ i ∈ s, b i * X i ω) ^ (2 * p) := by
      rw [hy, ← pow_mul]
    calc (x + y) ^ p ≤ 2 ^ p * max x y ^ p := by rw [← h2]; exact h1
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          exact mul_le_mul_of_nonneg_left h3 this
      _ = _ := by rw [hxp, hyp]
  have hint : Integrable (fun ω => 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
      + (∑ i ∈ s, b i * X i ω) ^ (2 * p))) P := (hia.add hib).const_mul _
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hint
    (Filter.Eventually.of_forall hpt)
  calc ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ ∫ ω, 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
          + (∑ i ∈ s, b i * X i ω) ^ (2 * p)) ∂P := hle
    _ = 2 ^ p * (RowIndep_dfac p * ((linVar v a s : ℝ) ^ p + (linVar v b s : ℝ) ^ p)) := by
        rw [integral_const_mul, integral_add hia hib, integral_pow_lin hmeas hlaw hindep,
          integral_pow_lin hmeas hlaw hindep]
        ring


end MomentBound

end Moments

/-! ### Measurability of the matrix inverse (private port of RBM1D `Defs/MatrixMeasurable.lean`
lines 25-48, commit `86573b9`) -/

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A`. -/
private theorem measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ} (hM : Measurable M)
    (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

/-- The entrywise form: from measurability of every entry of `A`, every entry of `A⁻¹` is
measurable. -/
private theorem measurable_inv_entries {A : Θ → Matrix ν ν ℂ}
    (hA : ∀ k l, Measurable fun ω => A ω k l) (k l : ν) :
    Measurable fun ω => (A ω)⁻¹ k l :=
  measurable_matrix_inv_apply (Measurable.of_eval fun a => Measurable.of_eval fun b => hA a b) k l

end MatrixMeasurable

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- The slice of a common sample point, evaluated at a coordinate. -/
private theorem slice_apply (ω : Sizes.SeqΩ sz) (c : CoordF d (sz.L n) (sz.W n)) :
    Sizes.slice sz n ω c = ω ⟨n, c⟩ := rfl

/-- The entries of the common-space flow. -/
private theorem seqHflow_apply (u : ℝ) (ω : Sizes.SeqΩ sz) (i j : Idx d (sz.L n) (sz.W n)) :
    Sizes.seqHflow sz n u ω i j
      = (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) i j := rfl


/-- Two sample points **agree off row `i`** when every coordinate at size `n` whose index pair
avoids `i` carries the same value. -/
def AgreeOffRow {d : ℕ} (sz : Sizes d) (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) (ω ω' : Sizes.SeqΩ sz) : Prop :=
  ∀ (k l : Idx d (sz.L n) (sz.W n)) (b : Bool), k ≠ i → l ≠ i → ω ⟨n, k, l, b⟩ = ω' ⟨n, k, l, b⟩

/-- The entries of `X` away from row and column `i` only read coordinates that avoid `i`. -/
theorem Xentry_congr_of_ne {i : Idx d (sz.L n) (sz.W n)} {ω ω' : Sizes.SeqΩ sz}
    (h : AgreeOffRow sz n i ω ω')
    {k l : Idx d (sz.L n) (sz.W n)} (hk : k ≠ i) (hl : l ≠ i) :
    Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) k l
      = Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω') k l := by
  unfold Xentry
  simp only [slice_apply]
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` at `i` only reads coordinates that avoid `i`. -/
theorem Hflow_submatrix_congr (u : ℝ) {i : Idx d (sz.L n) (sz.W n)} {ω ω' : Sizes.SeqΩ sz}
    (h : AgreeOffRow sz n i ω ω') :
    (Sizes.seqHflow sz n u ω).submatrix (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      = (Sizes.seqHflow sz n u ω').submatrix (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _) := by
  ext k l
  simp only [Matrix.submatrix_apply, seqHflow_apply]
  rw [Xentry_congr_of_ne h k.2 l.2]

/-! ### The coordinates of row `i` -/

open Finset

/-- The coordinates of row `i` at size `n`: those whose index pair contains `i`. -/
def rowSet {d : ℕ} (sz : Sizes d) (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) : Finset (Sizes.SeqCoord sz) :=
  (univ : Finset (Idx d (sz.L n) (sz.W n) × Bool)).image
      (fun p => (⟨n, i, p.1, p.2⟩ : Sizes.SeqCoord sz)) ∪
    (univ : Finset (Idx d (sz.L n) (sz.W n) × Bool)).image
      (fun p => (⟨n, p.1, i, p.2⟩ : Sizes.SeqCoord sz))

@[simp] theorem mem_rowSet {i k l : Idx d (sz.L n) (sz.W n)} {b : Bool} :
    (⟨n, k, l, b⟩ : Sizes.SeqCoord sz) ∈ rowSet sz n i ↔ (k = i ∨ l = i) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      injection hp with h1 h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inl h2.1.symm
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      injection hp with h1 h2
      simp only [Prod.mk.injEq] at h2
      exact Or.inr h2.2.1.symm
  · rintro (rfl | rfl)
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨(l, b), Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨(k, b), Finset.mem_univ _, rfl⟩)

/-- **The row block is independent of any disjoint block of coordinates.** -/
theorem indepFun_rowSet (i : Idx d (sz.L n) (sz.W n)) (T : Finset (Sizes.SeqCoord sz))
    (hT : Disjoint (rowSet sz n i) T) :
    IndepFun (fun (ω : Sizes.SeqΩ sz) (c : rowSet sz n i) => ω c)
      (fun (ω : Sizes.SeqΩ sz) (c : T) => ω c) (Sizes.seqP sz) :=
  (iIndepFun_coord sz).indepFun_finset _ _ hT fun c => measurable_pi_apply c

/-! ### The row as a family indexed by `(column, real/imaginary)` -/

/-- The coordinate carrying the real (`b = true`) or imaginary (`b = false`) part of the entry
`X_{ik}`, for `k ≠ i`. -/
noncomputable def rowCoord {d : ℕ} (sz : Sizes d) (n : ℕ) (i k : Idx d (sz.L n) (sz.W n)) (b : Bool) :
    Sizes.SeqCoord sz :=
  if idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k then ⟨n, i, k, b⟩ else ⟨n, k, i, b⟩

/-- The sign with which the imaginary coordinate enters `X_{ik}`. -/
noncomputable def rowSign {d : ℕ} (sz : Sizes d) (n : ℕ) (i k : Idx d (sz.L n) (sz.W n)) : ℝ :=
  if idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k then 1 else -1

theorem rowCoord_mem_rowSet (i k : Idx d (sz.L n) (sz.W n)) (b : Bool) :
    rowCoord sz n i k b ∈ rowSet sz n i := by
  unfold rowCoord
  split_ifs with h
  · exact mem_rowSet.2 (Or.inl rfl)
  · exact mem_rowSet.2 (Or.inr rfl)

/-- **The entry `X_{ik}` in terms of the two row coordinates.**  For `k ≠ i` it is
`ω(real) + ε i ω(imag)` with `ε = ±1`. -/
theorem Xentry_eq_rowCoord {i k : Idx d (sz.L n) (sz.W n)} (hik : i ≠ k) (ω : Sizes.SeqΩ sz) :
    Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) i k = (ω (rowCoord sz n i k true) : ℂ)
      + (rowSign sz n i k : ℂ) * Complex.I * (ω (rowCoord sz n i k false) : ℂ) := by
  have hkey : idxKey d (sz.L n) (sz.W n) i ≠ idxKey d (sz.L n) (sz.W n) k := fun h =>
    hik (idxKey_injective d (sz.L n) (sz.W n) h)
  unfold Xentry rowCoord rowSign
  simp only [slice_apply]
  rcases lt_or_gt_of_ne hkey with h | h
  · simp only [h, ↓reduceIte]
    push_cast
    ring
  · have h' : ¬ idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k := by omega
    simp only [h', ↓reduceIte, h]
    push_cast
    ring

/-- The row coordinates are distinct: `(k, b) ↦ rowCoord i k b` is injective away from `i`. -/
theorem rowCoord_injOn {i : Idx d (sz.L n) (sz.W n)} {k l : Idx d (sz.L n) (sz.W n)} {b c : Bool}
    (hk : k ≠ i) (hl : l ≠ i)
    (h : rowCoord sz n i k b = rowCoord sz n i l c) : k = l ∧ b = c := by
  unfold rowCoord at h
  have hk' := hk
  have hl' := hl
  split_ifs at h with h1 h2 h2 <;> injection h with h3 h4 <;>
    simp only [Prod.mk.injEq] at h4 <;>
    first
      | exact ⟨h4.2.1, h4.2.2⟩
      | exact ⟨h4.1, h4.2.2⟩
      | (exfalso; simp_all)

/-! ### The row sum as a pair of real linear forms -/

/-- The index set of the row: a column `k ≠ i` together with a real/imaginary flag. -/
abbrev RowIdx {d : ℕ} (sz : Sizes d) (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) : Type :=
    {k : Idx d (sz.L n) (sz.W n) // k ≠ i} × Bool

/-- The Gaussian coordinates of the row, indexed by `RowIdx`. -/
noncomputable def rowVar {d : ℕ} (sz : Sizes d) (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) (q : RowIdx sz n i)
    (ω : Sizes.SeqΩ sz) : ℝ :=
  ω (rowCoord sz n i q.1.1 q.2)

/-- The coefficients of the real part of `∑_{k ≠ i} H_{ik} c_k`. -/
noncomputable def rowRe {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
    (c : Idx d (sz.L n) (sz.W n) → ℂ)
    (q : RowIdx sz n i) : ℝ :=
  if q.2 then Real.sqrt u * (c q.1.1).re
  else -(Real.sqrt u * rowSign sz n i q.1.1 * (c q.1.1).im)

/-- The coefficients of the imaginary part of `∑_{k ≠ i} H_{ik} c_k`. -/
noncomputable def rowIm {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
    (c : Idx d (sz.L n) (sz.W n) → ℂ)
    (q : RowIdx sz n i) : ℝ :=
  if q.2 then Real.sqrt u * (c q.1.1).im
  else Real.sqrt u * rowSign sz n i q.1.1 * (c q.1.1).re

/-- **The row sum, real part**: a real linear form in the row coordinates. -/
theorem re_row_sum (u : ℝ) (i : Idx d (sz.L n) (sz.W n)) (c : Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) :
    (∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * c k.1).re
      = ∑ q : RowIdx sz n i, rowRe sz n u i c q * rowVar sz n i q ω := by
  rw [Complex.re_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [seqHflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]
  simp only [Fintype.sum_bool, rowRe, rowVar, rowSign, ↓reduceIte]
  by_cases h : idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k.1 <;>
    simp [h, Complex.add_re, Complex.mul_re] <;> ring

/-- **The row sum, imaginary part**. -/
theorem im_row_sum (u : ℝ) (i : Idx d (sz.L n) (sz.W n)) (c : Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) :
    (∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * c k.1).im
      = ∑ q : RowIdx sz n i, rowIm sz n u i c q * rowVar sz n i q ω := by
  rw [Complex.im_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [seqHflow_apply, Xentry_eq_rowCoord (Ne.symm k.2) ω]
  simp only [Fintype.sum_bool, rowIm, rowVar, rowSign, ↓reduceIte]
  by_cases h : idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k.1 <;>
    simp [h, Complex.add_im, Complex.mul_im] <;> ring

/-! ### The moment bound for a row sum with frozen coefficients -/

theorem rowCoord_inj (i : Idx d (sz.L n) (sz.W n)) :
    Function.Injective fun q : RowIdx sz n i => rowCoord sz n i q.1.1 q.2 := by
  rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
  obtain ⟨h1, h2⟩ := rowCoord_injOn hk hl h
  subst h1
  subst h2
  rfl

/-- The row coordinates form an independent family. -/
theorem iIndepFun_rowVar (i : Idx d (sz.L n) (sz.W n)) :
    ProbabilityTheory.iIndepFun (rowVar sz n i) (Sizes.seqP sz) :=
  ProbabilityTheory.iIndepFun.precomp
    (g := fun q : RowIdx sz n i => rowCoord sz n i q.1.1 q.2) (rowCoord_inj i) (iIndepFun_coord sz)

theorem measurable_rowVar (i : Idx d (sz.L n) (sz.W n)) (q : RowIdx sz n i) :
    Measurable (rowVar sz n i q) := measurable_pi_apply _

theorem map_rowVar (i : Idx d (sz.L n) (sz.W n)) (q : RowIdx sz n i) :
    (Sizes.seqP sz).map (rowVar sz n i q)
      = gaussianReal 0 (Sizes.seqGvar sz (rowCoord sz n i q.1.1 q.2)) :=
  Sizes.seqP_map_eval sz _

/-- Off the diagonal the coordinate variance is `S_ik / 2`.  (Helper: `RBM2D/Gauss/Model.lean:121`,
`gvar_offDiag`; the merged copy `fineModel_gvarF_offDiag` is private to `FineModel.lean`.) -/
private theorem rowIndep_gvarF_offDiag (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]
    (i j : Idx d L W) (b : Bool) (hij : i ≠ j) :
    (gvarF d L W g (i, j, b) : ℝ) = svarF d L W g i j / 2 := by
  change (if i = j then svarF d L W g i j else svarF d L W g i j / 2) = _
  simp [hij]

/-- Off the diagonal the coordinate variance is `S_ik / 2`, in either order of the index pair. -/
theorem gvar_rowCoord {i k : Idx d (sz.L n) (sz.W n)} (hk : k ≠ i) (b : Bool) :
    (Sizes.seqGvar sz (rowCoord sz n i k b) : ℝ) = svarF d (sz.L n) (sz.W n) (sz.lam n) i k / 2 := by
  have key : ∀ a c : Idx d (sz.L n) (sz.W n), a ≠ c →
      (Sizes.seqGvar sz ⟨n, a, c, b⟩ : ℝ) = svarF d (sz.L n) (sz.W n) (sz.lam n) a c / 2 := fun a c hac =>
    rowIndep_gvarF_offDiag d (sz.L n) (sz.W n) (sz.lam n) a c b hac
  unfold rowCoord
  split_ifs with h
  · exact key i k (Ne.symm hk)
  · rw [key k i hk, svarF_comm]

/-- The variance of the real part of the row sum: `(u/2) ∑_k S_{ik} |c_k|²`. -/
theorem linVar_rowRe {u : ℝ} (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) (c : Idx d (sz.L n) (sz.W n) → ℂ) :
    ((linVar (fun q : RowIdx sz n i => Sizes.seqGvar sz (rowCoord sz n i q.1.1 q.2))
        (rowRe sz n u i c) Finset.univ : ℝ≥0) : ℝ)
      = u / 2 * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
          svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖c k.1‖ ^ 2 := by
  unfold linVar
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [rowRe, rowSign, ↓reduceIte, gvar_rowCoord k.2]
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hnorm : ‖c k.1‖ ^ 2 = (c k.1).re ^ 2 + (c k.1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases h : idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k.1 <;>
    simp [h, hnorm, mul_pow, hsq] <;> ring

/-- The variance of the imaginary part is the same. -/
theorem linVar_rowIm {u : ℝ} (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) (c : Idx d (sz.L n) (sz.W n) → ℂ) :
    ((linVar (fun q : RowIdx sz n i => Sizes.seqGvar sz (rowCoord sz n i q.1.1 q.2))
        (rowIm sz n u i c) Finset.univ : ℝ≥0) : ℝ)
      = u / 2 * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
          svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖c k.1‖ ^ 2 := by
  unfold linVar
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [rowIm, rowSign, ↓reduceIte, gvar_rowCoord k.2]
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  have hnorm : ‖c k.1‖ ^ 2 = (c k.1).re ^ 2 + (c k.1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_cases h : idxKey d (sz.L n) (sz.W n) i < idxKey d (sz.L n) (sz.W n) k.1 <;>
    simp [h, hnorm, mul_pow, hsq] <;> ring

/-- **The moment bound for a row sum with frozen coefficients**:
`E‖∑_{k ≠ i} H_{ik} c_k‖^{2p} ≤ 2 (2p-1)!! (u ∑_k S_{ik} |c_k|²)^p`. -/
theorem integral_norm_row_sum_pow_le {u : ℝ} (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n))
    (c : Idx d (sz.L n) (sz.W n) → ℂ) (p : ℕ) :
    ∫ ω, ‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
        Sizes.seqHflow sz n u ω i k.1 * c k.1‖ ^ (2 * p) ∂(Sizes.seqP sz)
      ≤ 2 * (RowIndep_dfac p *
        (u * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
          svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖c k.1‖ ^ 2) ^ p) := by
  set V : ℝ := u / 2 * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
    svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖c k.1‖ ^ 2 with hV
  have hpt : ∀ ω : Sizes.SeqΩ sz, ‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
        Sizes.seqHflow sz n u ω i k.1 * c k.1‖ ^ (2 * p)
      = ((∑ q : RowIdx sz n i, rowRe sz n u i c q * rowVar sz n i q ω) ^ 2
        + (∑ q : RowIdx sz n i, rowIm sz n u i c q * rowVar sz n i q ω) ^ 2) ^ p := by
    intro ω
    rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← re_row_sum, ← im_row_sum]
    ring_nf
  simp_rw [hpt]
  have hbound := integral_sq_add_sq_pow_le (P := Sizes.seqP sz)
    (measurable_rowVar (sz := sz) (n := n) i)
    (map_rowVar (sz := sz) (n := n) i) (iIndepFun_rowVar (sz := sz) (n := n) i)
    (rowRe sz n u i c) (rowIm sz n u i c) Finset.univ p
  rw [linVar_rowRe hu, linVar_rowIm hu] at hbound
  refine hbound.trans (le_of_eq ?_)
  simp only [mul_pow, div_pow]
  field_simp
  ring

/-! ### The two concrete finite blocks -/

/-- The coordinates of slice `n` (all of them: RBM2D has no unused-coordinate bookkeeping, and the
finite block only has to contain the coordinates that `H` at size `n` reads and to be disjoint
from `rowSet`). -/
def relCoord {d : ℕ} (sz : Sizes d) (n : ℕ) : Finset (Sizes.SeqCoord sz) :=
  (Finset.univ : Finset (CoordF d (sz.L n) (sz.W n))).image (fun c => (⟨n, c⟩ : Sizes.SeqCoord sz))

/-- The relevant coordinates outside row `i`. -/
def offRowCoord {d : ℕ} (sz : Sizes d) (n : ℕ) (i : Idx d (sz.L n) (sz.W n)) : Finset (Sizes.SeqCoord sz) :=
  relCoord sz n \ rowSet sz n i

theorem disjoint_rowSet_offRowCoord (i : Idx d (sz.L n) (sz.W n)) :
    Disjoint (rowSet sz n i) (offRowCoord sz n i) := by
  rw [Finset.disjoint_right]
  intro c hc
  exact (Finset.mem_sdiff.1 hc).2

/-- A coordinate of slice `n` whose index pair avoids `i` lies in the off-row block. -/
private theorem mem_offRowCoord {i k l : Idx d (sz.L n) (sz.W n)} (b : Bool) (hk : k ≠ i)
    (hl : l ≠ i) : (⟨n, k, l, b⟩ : Sizes.SeqCoord sz) ∈ offRowCoord sz n i := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact Finset.mem_image.2 ⟨(k, l, b), Finset.mem_univ _, rfl⟩
  · rw [mem_rowSet]
    rintro (h | h)
    · exact hk h
    · exact hl h

/-- **The minor matrix reads only the off-row block.**  Two sample points agreeing on
`offRowCoord` have the same `H^{(i)}`. -/
theorem Hflow_submatrix_congr_offRowCoord (u : ℝ) {i : Idx d (sz.L n) (sz.W n)}
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    (Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      = (Sizes.seqHflow sz n u ω').submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _) :=
  Hflow_submatrix_congr u fun _ _ b hk hl => h _ (mem_offRowCoord b hk hl)

/-- The row entries `H_{ik}`, `k ≠ i`, read only the row block. -/
theorem Hflow_row_congr (u : ℝ) {i : Idx d (sz.L n) (sz.W n)} {ω ω' : Sizes.SeqΩ sz}
    (h : ∀ c ∈ rowSet sz n i, ω c = ω' c) {k : Idx d (sz.L n) (sz.W n)} (hk : k ≠ i) :
    Sizes.seqHflow sz n u ω i k = Sizes.seqHflow sz n u ω' i k := by
  rw [seqHflow_apply, seqHflow_apply, Xentry_eq_rowCoord (Ne.symm hk) ω,
    Xentry_eq_rowCoord (Ne.symm hk) ω', h _ (rowCoord_mem_rowSet i k true),
    h _ (rowCoord_mem_rowSet i k false)]

/-- The row sum with coefficients reading only the off-row block, as a function of the two
blocks. -/
theorem row_sum_congr (u : ℝ) {i : Idx d (sz.L n) (sz.W n)} (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω')
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ rowSet sz n i ∪ offRowCoord sz n i, ω c = ω' c) :
    (∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * C ω k.1)
      = ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω' i k.1 * C ω' k.1 := by
  have hrow : ∀ c ∈ rowSet sz n i, ω c = ω' c := fun c hc =>
    h c (Finset.mem_union_left _ hc)
  have hoff : ∀ c ∈ offRowCoord sz n i, ω c = ω' c := fun c hc =>
    h c (Finset.mem_union_right _ hc)
  rw [hC ω ω' hoff]
  exact Finset.sum_congr rfl fun k _ => by rw [Hflow_row_congr u hrow k.2]

/-! ### The conditional moment bound: random coefficients -/

variable {u : ℝ} {i : Idx d (sz.L n) (sz.W n)} {p : ℕ}

/-- Abbreviation for the row sum with coefficients `C`. -/
noncomputable def rowSum {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
    (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * C ω k.1

/-- The (random) variance of the row sum. -/
noncomputable def rowVarSum {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
    (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) : ℝ :=
  u * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖C ω k.1‖ ^ 2

/-- **The row LDE moment bound.**  If the coefficients read only the off-row block, then
`E‖∑_{k ≠ i} H_{ik} C_k‖^{2p} ≤ 2 (2p-1)!! · E[(u ∑_k S_{ik} |C_k|²)^p]`: conditionally on the
off-row block the row sum is a centred complex Gaussian of variance `u ∑_k S_{ik}|C_k|²`, so the
frozen bound `integral_norm_row_sum_pow_le` applies fibrewise. -/
theorem integral_norm_rowSum_pow_le (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω')
    (hint : Integrable (fun ω => ‖rowSum sz n u i C ω‖ ^ (2 * p)) (Sizes.seqP sz))
    (hint' : Integrable (fun ω => rowVarSum sz n u i C ω ^ p) (Sizes.seqP sz)) :
    ∫ ω, ‖rowSum sz n u i C ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      ≤ 2 * (RowIndep_dfac p * ∫ ω, rowVarSum sz n u i C ω ^ p ∂(Sizes.seqP sz)) := by
  classical
  set S := rowSet sz n i with hS
  set T := offRowCoord sz n i with hT
  set U : Sizes.SeqΩ sz → ({c // c ∈ S} → ℝ) := fun ω c => ω c.1 with hU
  set V : Sizes.SeqΩ sz → ({c // c ∈ T} → ℝ) := fun ω c => ω c.1 with hV
  have hUmeas : Measurable U := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hVmeas : Measurable V := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hindep : IndepFun U V (Sizes.seqP sz) := indepFun_rowSet i T (disjoint_rowSet_offRowCoord i)
  have hdisj := disjoint_rowSet_offRowCoord (sz := sz) (n := n) i
  -- the coefficients read only the second block, so they may be read off `V` alone
  have hCy : ∀ ω : Sizes.SeqΩ sz, C ω = C (glue S T (0, V ω)) := by
    intro ω
    refine hC _ _ fun c hc => ?_
    have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
    simp [glue, hcS, hc, hV]
  -- the row sum is a function of the two blocks
  have hrow : ∀ ω : Sizes.SeqΩ sz, rowSum sz n u i C ω = rowSum sz n u i C (glue S T (U ω, V ω)) := by
    intro ω
    refine row_sum_congr u C hC fun c hc => ?_
    exact (glue_agree S T ω hc).symm
  set F : ({c // c ∈ S} → ℝ) × ({c // c ∈ T} → ℝ) → ℝ :=
    fun q => ‖rowSum sz n u i C (glue S T q)‖ ^ (2 * p) with hF
  set G : ({c // c ∈ T} → ℝ) → ℝ :=
    fun y => 2 * (RowIndep_dfac p * rowVarSum sz n u i C (glue S T (0, y)) ^ p) with hG
  -- measurability of the glued quantities
  have hglue := measurable_glue (ι := Sizes.SeqCoord sz) S T
  have hFmeas : Measurable F := by
    refine (Measurable.pow_const ?_ _)
    refine Measurable.norm ?_
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((Sizes.measurable_seqHflow_entry sz n u i k.1).comp hglue).mul
      (((measurable_pi_apply k.1).comp hCmeas).comp hglue)
  have hGmeas : Measurable G := by
    refine (measurable_const.mul ((measurable_const.mul (Measurable.pow_const ?_ _))))
    refine (measurable_const.mul ?_)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact measurable_const.mul
      ((((measurable_pi_apply k.1).comp hCmeas).comp (hglue.comp (measurable_const.prodMk
        measurable_id))).norm.pow_const _)
  -- transport the two integrability hypotheses
  have hpair : (Sizes.seqP sz).map (fun ω => (U ω, V ω))
      = ((Sizes.seqP sz).map U).prod ((Sizes.seqP sz).map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUmeas.aemeasurable hVmeas.aemeasurable).1 hindep
  have hFint : Integrable F (((Sizes.seqP sz).map U).prod ((Sizes.seqP sz).map V)) := by
    rw [← hpair]
    refine (integrable_map_measure hFmeas.aestronglyMeasurable
      (hUmeas.prodMk hVmeas).aemeasurable).2 ?_
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF, Function.comp]
    rw [← hrow]
  have hGint : Integrable G ((Sizes.seqP sz).map V) := by
    refine (integrable_map_measure hGmeas.aestronglyMeasurable hVmeas.aemeasurable).2 ?_
    refine ((hint'.const_mul (RowIndep_dfac p)).const_mul 2).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hG, Function.comp, rowVarSum]
    rw [← hCy]
  -- the fibrewise (conditional) bound
  have hinner : ∀ y : {c // c ∈ T} → ℝ, (∫ x, F (x, y) ∂((Sizes.seqP sz).map U)) ≤ G y := by
    intro y
    have hmap := integral_map (μ := Sizes.seqP sz) (φ := U) (f := fun x => F (x, y))
      hUmeas.aemeasurable (hFmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    rw [hmap]
    have hval : ∀ ω : Sizes.SeqΩ sz, F (U ω, y)
        = ‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 *
            C (glue S T (0, y)) k.1‖ ^ (2 * p) := by
      intro ω
      simp only [hF, rowSum]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      have hHe : Sizes.seqHflow sz n u (glue S T (U ω, y)) i k.1 = Sizes.seqHflow sz n u ω i k.1 := by
        refine Hflow_row_congr u (fun c hc => ?_) k.2
        have hcS : c ∈ S := hc
        simp [glue, hcS, hU]
      have hCe : C (glue S T (U ω, y)) k.1 = C (glue S T (0, y)) k.1 := by
        have : C (glue S T (U ω, y)) = C (glue S T (0, y)) := by
          refine hC _ _ fun c hc => ?_
          have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
          simp [glue, hcS, hc]
        rw [this]
      rw [hHe, hCe]
    simp only [hval]
    exact (integral_norm_row_sum_pow_le hu i (C (glue S T (0, y))) p).trans (le_of_eq (by
      simp only [hG, rowVarSum]))
  -- assemble
  have hmain := integral_indep_pair_le hUmeas hVmeas hindep hFint hGint
    (Filter.Eventually.of_forall hinner)
  have hL : ∫ ω, ‖rowSum sz n u i C ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      = ∫ ω, F (U ω, V ω) ∂(Sizes.seqP sz) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF]
    rw [← hrow]
  have hR : ∫ y, G y ∂((Sizes.seqP sz).map V)
      = 2 * (RowIndep_dfac p * ∫ ω, rowVarSum sz n u i C ω ^ p ∂(Sizes.seqP sz)) := by
    rw [integral_map hVmeas.aemeasurable hGmeas.aestronglyMeasurable]
    simp only [hG, rowVarSum]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [← hCy]
  rw [hL, ← hR]
  exact hmain

/-- The coefficients normalised by the (random) standard deviation of the row sum. -/
noncomputable def rowCoeffNorm {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
    (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) (k : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if 0 < rowVarSum sz n u i C ω then C ω k / (Real.sqrt (rowVarSum sz n u i C ω) : ℂ) else 0

theorem rowVarSum_nonneg (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) :
    0 ≤ rowVarSum sz n u i C ω := by
  refine mul_nonneg hu (Finset.sum_nonneg fun k _ => ?_)
  exact mul_nonneg (svarF_nonneg _ _ _ _ _ _) (by positivity)

/-- **The normalised row sum has variance `1`** wherever the variance is positive. -/
theorem rowVarSum_rowCoeffNorm (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (ω : Sizes.SeqΩ sz) :
    rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω
      = if 0 < rowVarSum sz n u i C ω then 1 else 0 := by
  have hV0 := rowVarSum_nonneg (i := i) hu C ω
  by_cases h : 0 < rowVarSum sz n u i C ω
  · have hs : (0 : ℝ) < Real.sqrt (rowVarSum sz n u i C ω) := Real.sqrt_pos.2 h
    have hsq : Real.sqrt (rowVarSum sz n u i C ω) ^ 2 = rowVarSum sz n u i C ω := Real.sq_sqrt hV0
    have hcoef : ∀ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, ‖rowCoeffNorm sz n u i C ω k.1‖ ^ 2
        = ‖C ω k.1‖ ^ 2 / rowVarSum sz n u i C ω := by
      intro k
      simp only [rowCoeffNorm, h, ↓reduceIte, norm_div, div_pow, Complex.norm_real,
        Real.norm_of_nonneg hs.le, hsq]
    simp only [h, ↓reduceIte]
    have hne : rowVarSum sz n u i C ω ≠ 0 := ne_of_gt h
    have hcalc : rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω
        = rowVarSum sz n u i C ω / rowVarSum sz n u i C ω := by
      conv_lhs => unfold rowVarSum
      simp only [hcoef]
      rw [Finset.sum_congr rfl fun k _ => (mul_div_assoc (svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1)
        (‖C ω k.1‖ ^ 2) (rowVarSum sz n u i C ω)).symm, ← Finset.sum_div, ← mul_div_assoc]
      rfl
    rw [hcalc, div_self hne]
  · simp only [h, ↓reduceIte]
    have hzero : ∀ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, rowCoeffNorm sz n u i C ω k.1 = 0 := by
      intro k
      simp [rowCoeffNorm, h]
    unfold rowVarSum
    simp [hzero]

/-- The normalised coefficients still read only the off-row block. -/
theorem rowCoeffNorm_congr (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω')
    (ω ω' : Sizes.SeqΩ sz) (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    rowCoeffNorm sz n u i C ω = rowCoeffNorm sz n u i C ω' := by
  have hCe := hC ω ω' h
  funext k
  simp only [rowCoeffNorm, rowVarSum, hCe]
  rfl

theorem measurable_rowVarSum (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ) (hCmeas : Measurable C) :
    Measurable (rowVarSum sz n u i C) := by
  unfold rowVarSum
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
  exact measurable_const.mul ((((measurable_pi_apply k.1).comp hCmeas).norm).pow_const 2)

theorem measurable_rowCoeffNorm (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : Measurable C) :
    Measurable (rowCoeffNorm sz n u i C) := by
  refine Measurable.of_eval fun k => ?_
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_rowVarSum C hCmeas)) ?_
    measurable_const
  refine ((measurable_pi_apply k).comp hCmeas).div ?_
  exact Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (measurable_rowVarSum C hCmeas))

/-- **The row LDE, ratio form.**  Normalising by the conditional standard deviation gives a
*constant* moment bound: `E[(‖∑_{k≠i} H_{ik} C_k‖² / (u ∑_k S_{ik}|C_k|²))^p] ≤ 2 (2p-1)!!`.
This is the `MomentDom` input (with `Φ = 1`) that `stochDom_of_momentDom` turns into `≺`. -/
theorem integral_norm_rowSum_norm_pow_le (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω')
    (hint : Integrable
      (fun ω => ‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p)) (Sizes.seqP sz)) :
    ∫ ω, ‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      ≤ 2 * RowIndep_dfac p := by
  have hvar := rowVarSum_rowCoeffNorm (sz := sz) (n := n) (u := u) (i := i) hu C
  have hmeas' : Measurable (fun ω => rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω ^ p) :=
    (measurable_rowVarSum _ (measurable_rowCoeffNorm C hCmeas)).pow_const p
  have hbdd : ∀ ω : Sizes.SeqΩ sz, ‖rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω ^ p‖ ≤ 1 := by
    intro ω
    rw [hvar ω]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · by_cases h : 0 < rowVarSum sz n u i C ω <;> simp [h]
    · by_cases h : 0 < rowVarSum sz n u i C ω <;> simp [h, zero_pow hp.ne']
  have hint' : Integrable (fun ω => rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω ^ p)
      (Sizes.seqP sz) :=
    (integrable_const (1 : ℝ)).mono' hmeas'.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hmain := integral_norm_rowSum_pow_le (sz := sz) (n := n) (u := u) (i := i) (p := p) hu
    (rowCoeffNorm sz n u i C) (measurable_rowCoeffNorm C hCmeas)
    (fun ω ω' h => rowCoeffNorm_congr C hC ω ω' h) hint hint'
  refine hmain.trans ?_
  have hle : ∫ ω, rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω ^ p ∂(Sizes.seqP sz) ≤ 1 := by
    calc ∫ ω, rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω ^ p ∂(Sizes.seqP sz)
        ≤ ∫ _ω : Sizes.SeqΩ sz, (1 : ℝ) ∂(Sizes.seqP sz) := by
          refine integral_mono hint' (integrable_const 1) fun ω => ?_
          have := hbdd ω
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = 1 := by simp
  have hd : 0 ≤ RowIndep_dfac p := by
    unfold RowIndep_dfac
    positivity
  nlinarith [hle, hd]

/-! ### Measurability of the minor resolvent -/

/-- The `j`-th column of the minor resolvent `(H^{(i)} - z)^{-1}`, as coefficients indexed by
all of `Idx d (sz.L n) (sz.W n)` (zero at `i`). -/
noncomputable def minorCol {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (i : Idx d (sz.L n) (sz.W n))
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) (ω : Sizes.SeqΩ sz) (k : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if h : k ≠ i then
    (((Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ i}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ i} ℂ))⁻¹) ⟨k, h⟩ j
  else 0

/-- **The minor resolvent column reads only the off-row block.** -/
theorem minorCol_congr (u : ℝ) (z : ℂ) {i : Idx d (sz.L n) (sz.W n)}
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i})
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    minorCol sz n u z i j ω = minorCol sz n u z i j ω' := by
  funext k
  unfold minorCol
  rw [Hflow_submatrix_congr_offRowCoord u h]

theorem measurable_minorCol (u : ℝ) (z : ℂ) (i : Idx d (sz.L n) (sz.W n))
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    Measurable (minorCol sz n u z i j) := by
  refine Measurable.of_eval fun k => ?_
  unfold minorCol
  split
  · exact measurable_inv_entries
      (A := fun ω : Sizes.SeqΩ sz => (Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ i} {a : Idx d (sz.L n) (sz.W n) // a ≠ i} ℂ))
      (fun a b => (Sizes.measurable_seqHflow_entry sz n u a.1 b.1).sub measurable_const) _ _
  · exact measurable_const

/-! ### The row LDE for the Gaussian model -/

/-! ### Alignment with the LDE of `Green/EntryCore.lean` -/

variable {z : ℂ}

/-- Where the resolvent exists, the coefficients `minorCol` are the entries of `G^{(i)}`. -/
theorem minorCol_eq_greenMinor (u : ℝ) {i : Idx d (sz.L n) (sz.W n)}
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow sz n u ω) z i i ≠ 0) {k : Idx d (sz.L n) (sz.W n)} (hk : k ≠ i) :
    minorCol sz n u z i j ω k = greenMinor (green (Sizes.seqHflow sz n u ω) z) i k j.1 := by
  unfold minorCol
  simp only [ne_eq, hk, not_false_eq_true, ↓reduceDIte]
  rw [inv_minor_resolvent hdet i hGii]
  rfl

/-- **The left-hand side of the row LDE** is the row sum with the minor resolvent column. -/
theorem ldeRowLHS_eq (u : ℝ) {i : Idx d (sz.L n) (sz.W n)} (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i})
    {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow sz n u ω) z i i ≠ 0) :
    ldeRowLHS (Sizes.seqHflow sz n u ω) (green (Sizes.seqHflow sz n u ω) z) i j.1
      = ‖rowSum sz n u i (minorCol sz n u z i j) ω‖ ^ 2 := by
  unfold ldeRowLHS rowSum
  congr 2
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

/-- **The right-hand side of the row LDE** is the variance of that row sum, up to the factor
`u`. -/
theorem rowVarSum_eq (u : ℝ) {i : Idx d (sz.L n) (sz.W n)} (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i})
    {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow sz n u ω) z i i ≠ 0) :
    rowVarSum sz n u i (minorCol sz n u z i j) ω
      = u * ldeRowRHS (svarF d (sz.L n) (sz.W n) (sz.lam n)) (green (Sizes.seqHflow sz n u ω) z) i j.1 := by
  unfold rowVarSum ldeRowRHS
  congr 1
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

/-! ### The frozen bound in `ℝ≥0∞` form -/

theorem measurable_row_sum (u : ℝ) (i : Idx d (sz.L n) (sz.W n)) (c : Idx d (sz.L n) (sz.W n) → ℂ) :
    Measurable fun ω : Sizes.SeqΩ sz =>
      ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * c k.1 :=
  Finset.measurable_sum _ fun k _ =>
    (Sizes.measurable_seqHflow_entry sz n u i k.1).mul measurable_const

/-- All even moments of a frozen row sum exist. -/
theorem integrable_norm_row_sum_pow (u : ℝ) (i : Idx d (sz.L n) (sz.W n))
    (c : Idx d (sz.L n) (sz.W n) → ℂ) (p : ℕ) :
    Integrable (fun ω : Sizes.SeqΩ sz =>
      ‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * c k.1‖ ^ (2 * p))
        (Sizes.seqP sz) := by
  have hre := integrable_pow_lin (P := Sizes.seqP sz) (measurable_rowVar (sz := sz) (n := n) i)
    (map_rowVar (sz := sz) (n := n) i) (iIndepFun_rowVar (sz := sz) (n := n) i)
    (rowRe sz n u i c) Finset.univ p
  have him := integrable_pow_lin (P := Sizes.seqP sz) (measurable_rowVar (sz := sz) (n := n) i)
    (map_rowVar (sz := sz) (n := n) i) (iIndepFun_rowVar (sz := sz) (n := n) i)
    (rowIm sz n u i c) Finset.univ p
  refine ((hre.add him).const_mul ((2 : ℝ) ^ p)).mono'
    (((measurable_row_sum u i c).norm).pow_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  set x := (∑ q : RowIdx sz n i, rowRe sz n u i c q * rowVar sz n i q ω) with hx
  set y := (∑ q : RowIdx sz n i, rowIm sz n u i c q * rowVar sz n i q ω) with hy
  have hz : ‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
        Sizes.seqHflow sz n u ω i k.1 * c k.1‖ ^ (2 * p)
      = (x ^ 2 + y ^ 2) ^ p := by
    rw [pow_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hx, hy, ← re_row_sum,
      ← im_row_sum]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hz]
  have hxy : (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
    have hx0 : (0 : ℝ) ≤ x ^ 2 := by positivity
    have hy0 : (0 : ℝ) ≤ y ^ 2 := by positivity
    have h1 : (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rcases le_total (x ^ 2) (y ^ 2) with h | h
      · simp [max_eq_right h]; linarith
      · simp [max_eq_left h]; linarith
    have h2 : max (x ^ 2) (y ^ 2) ^ p ≤ x ^ (2 * p) + y ^ (2 * p) := by
      rw [pow_mul, pow_mul]
      rcases le_total (x ^ 2) (y ^ 2) with h | h
      · rw [max_eq_right h]
        have : (0 : ℝ) ≤ (x ^ 2) ^ p := by positivity
        linarith
      · rw [max_eq_left h]
        have : (0 : ℝ) ≤ (y ^ 2) ^ p := by positivity
        linarith
    calc (x ^ 2 + y ^ 2) ^ p ≤ (2 * max (x ^ 2) (y ^ 2)) ^ p := h1
      _ = 2 ^ p * max (x ^ 2) (y ^ 2) ^ p := by rw [mul_pow]
      _ ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          exact mul_le_mul_of_nonneg_left h2 this
  calc (x ^ 2 + y ^ 2) ^ p ≤ 2 ^ p * (x ^ (2 * p) + y ^ (2 * p)) := hxy
    _ = _ := by simp only [Pi.add_apply, hx, hy]

/-- The frozen bound, in `ℝ≥0∞` form. -/
theorem lintegral_norm_row_sum_pow_le {u : ℝ} (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n))
    (c : Idx d (sz.L n) (sz.W n) → ℂ) (p : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
        Sizes.seqHflow sz n u ω i k.1 * c k.1‖ ^ (2 * p)) ∂(Sizes.seqP sz)
      ≤ ENNReal.ofReal (2 * (RowIndep_dfac p *
        (u * ∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
          svarF d (sz.L n) (sz.W n) (sz.lam n) i k.1 * ‖c k.1‖ ^ 2) ^ p)) := by
  have hint := integrable_norm_row_sum_pow u i c p
  have hnn : 0 ≤ᵐ[Sizes.seqP sz] fun ω : Sizes.SeqΩ sz =>
      ‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i}, Sizes.seqHflow sz n u ω i k.1 * c k.1‖ ^ (2 * p) :=
    Filter.Eventually.of_forall fun ω => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.ofReal_le_ofReal (integral_norm_row_sum_pow_le hu i c p)

/-! ### The row LDE without integrability hypotheses -/

/-- **Tonelli assembly, constant-bound form.**  If the coefficients `D` read only the off-row
block and their (random) variance obeys a uniform bound after the frozen estimate, then
`∫⁻ ‖Z‖^{2p}` obeys that bound — with no integrability hypothesis. -/
theorem lintegral_norm_rowSum_pow_le_of_const (hu : 0 ≤ u)
    (D : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ) (hDmeas : Measurable D)
    (hDC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → D ω = D ω') {c : ℝ≥0∞}
    (hb : ∀ ω : Sizes.SeqΩ sz,
      ENNReal.ofReal (2 * (RowIndep_dfac p * rowVarSum sz n u i D ω ^ p)) ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (‖rowSum sz n u i D ω‖ ^ (2 * p)) ∂(Sizes.seqP sz) ≤ c := by
  classical
  set S := rowSet sz n i with hS
  set T := offRowCoord sz n i with hT
  set U : Sizes.SeqΩ sz → ({c // c ∈ S} → ℝ) := fun ω c => ω c.1 with hU
  set V : Sizes.SeqΩ sz → ({c // c ∈ T} → ℝ) := fun ω c => ω c.1 with hV
  have hUmeas : Measurable U := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hVmeas : Measurable V := Measurable.of_eval fun c => measurable_pi_apply c.1
  have hindep : IndepFun U V (Sizes.seqP sz) := indepFun_rowSet i T (disjoint_rowSet_offRowCoord i)
  have hdisj := disjoint_rowSet_offRowCoord (sz := sz) (n := n) i
  set F : ({c // c ∈ S} → ℝ) × ({c // c ∈ T} → ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (‖rowSum sz n u i D (glue S T q)‖ ^ (2 * p)) with hF
  have hglue := measurable_glue (ι := Sizes.SeqCoord sz) S T
  have hFmeas : Measurable F := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) _)
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((Sizes.measurable_seqHflow_entry sz n u i k.1).comp hglue).mul
      (((measurable_pi_apply k.1).comp hDmeas).comp hglue)
  have hrow : ∀ ω : Sizes.SeqΩ sz, rowSum sz n u i D ω = rowSum sz n u i D (glue S T (U ω, V ω)) := by
    intro ω
    refine row_sum_congr u D hDC fun c hc => ?_
    exact (glue_agree S T ω hc).symm
  have hinner : ∀ y : {c // c ∈ T} → ℝ, (∫⁻ x, F (x, y) ∂((Sizes.seqP sz).map U)) ≤ c := by
    intro y
    have hFy : Measurable fun x : {c // c ∈ S} → ℝ => F (x, y) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_map hFy hUmeas]
    have hval : ∀ ω : Sizes.SeqΩ sz, F (U ω, y)
        = ENNReal.ofReal (‖∑ k : {k : Idx d (sz.L n) (sz.W n) // k ≠ i},
            Sizes.seqHflow sz n u ω i k.1 * D (glue S T (0, y)) k.1‖ ^ (2 * p)) := by
      intro ω
      simp only [hF, rowSum]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      have hHe : Sizes.seqHflow sz n u (glue S T (U ω, y)) i k.1 = Sizes.seqHflow sz n u ω i k.1 := by
        refine Hflow_row_congr u (fun c hc => ?_) k.2
        have hcS : c ∈ S := hc
        simp [glue, hcS, hU]
      have hDe : D (glue S T (U ω, y)) k.1 = D (glue S T (0, y)) k.1 := by
        have : D (glue S T (U ω, y)) = D (glue S T (0, y)) := by
          refine hDC _ _ fun c hc => ?_
          have hcS : c ∉ S := Finset.disjoint_right.1 hdisj hc
          simp [glue, hcS, hc]
        rw [this]
      rw [hHe, hDe]
    simp only [hval]
    exact (lintegral_norm_row_sum_pow_le hu i (D (glue S T (0, y))) p).trans
      (hb (glue S T (0, y)))
  have hmain := lintegral_indep_pair_le hUmeas hVmeas hindep hFmeas hinner
  calc ∫⁻ ω, ENNReal.ofReal (‖rowSum sz n u i D ω‖ ^ (2 * p)) ∂(Sizes.seqP sz)
      = ∫⁻ ω, F (U ω, V ω) ∂(Sizes.seqP sz) := by
        refine lintegral_congr fun ω => ?_
        simp only [hF]
        rw [← hrow]
    _ ≤ c := hmain

/-- **The row LDE, `ℝ≥0∞` form, no side conditions.**  Conditionally on the off-row block the
normalised row sum is a centred complex Gaussian of variance `≤ 1`. -/
theorem lintegral_norm_rowSum_norm_pow_le (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω') :
    ∫⁻ ω, ENNReal.ofReal (‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p)) ∂(Sizes.seqP sz)
      ≤ ENNReal.ofReal (2 * RowIndep_dfac p) := by
  refine lintegral_norm_rowSum_pow_le_of_const hu (rowCoeffNorm sz n u i C)
    (measurable_rowCoeffNorm C hCmeas) (fun ω ω' h => rowCoeffNorm_congr C hC ω ω' h)
    (fun ω => ENNReal.ofReal_le_ofReal ?_)
  have hvar := rowVarSum_rowCoeffNorm (sz := sz) (n := n) (u := u) (i := i) hu C ω
  have hd0 : (0 : ℝ) ≤ RowIndep_dfac p := by unfold RowIndep_dfac; positivity
  have hle : rowVarSum sz n u i (rowCoeffNorm sz n u i C) ω ^ p ≤ 1 := by
    rw [hvar]
    by_cases h : 0 < rowVarSum sz n u i C ω
    · simp [h]
    · rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [h]
      · simp [h, zero_pow hp.ne']
  nlinarith [hle, hd0]

/-- Integrability of the normalised row sum, from the finiteness of the `ℝ≥0∞` bound. -/
theorem integrable_norm_rowSum_norm_pow (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω') :
    Integrable (fun ω => ‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p)) (Sizes.seqP sz) := by
  have hmeas : Measurable fun ω : Sizes.SeqΩ sz =>
      ‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p) := by
    unfold rowSum
    refine (Measurable.norm ?_).pow_const _
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (Sizes.measurable_seqHflow_entry sz n u i k.1).mul
      ((measurable_pi_apply k.1).comp (measurable_rowCoeffNorm C hCmeas))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnn : ∀ ω : Sizes.SeqΩ sz, ‖‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p)‖ₑ
      = ENNReal.ofReal (‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p)) :=
    fun ω => Real.enorm_eq_ofReal (by positivity)
  simp only [hnn]
  exact lt_of_le_of_lt (lintegral_norm_rowSum_norm_pow_le hu C hCmeas hC) ENNReal.ofReal_lt_top

/-- **The row LDE, Bochner form, no side conditions**: `E‖Z/√V‖^{2p} ≤ 2 (2p-1)!!`. -/
theorem integral_norm_rowSum_norm_pow_le' (hu : 0 ≤ u) (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω') :
    ∫ ω, ‖rowSum sz n u i (rowCoeffNorm sz n u i C) ω‖ ^ (2 * p) ∂(Sizes.seqP sz)
      ≤ 2 * RowIndep_dfac p :=
  integral_norm_rowSum_norm_pow_le hu C hCmeas hC
    (integrable_norm_rowSum_norm_pow hu C hCmeas hC)

/-! ### The row LDE as stochastic domination -/

/-- The index set of the row LDE: a row `i` and a column `j ≠ i`. -/
abbrev LdeIdx {d : ℕ} (sz : Sizes d) (n : ℕ) : Type := Σ i : Idx d (sz.L n) (sz.W n),
    {a : Idx d (sz.L n) (sz.W n) // a ≠ i}

/-- The index set of the row LDE has at most `(size n)²` elements, for every `n`
(RBM1D `card_LdeIdx_le`, which needs `Dims.dim`; here `Fintype.card (Idx d L W) = size n` is
`Sizes.card_Idx`, so the `Z2` unfolding of RBM2D is not needed). -/
theorem card_LdeIdx_le (n : ℕ) :
    (Fintype.card (LdeIdx sz n) : ℝ) ≤ (sz.size n : ℝ) * (sz.size n : ℝ) := by
  have hcard : Fintype.card (Idx d (sz.L n) (sz.W n)) = sz.size n := Sizes.card_Idx sz n
  have : Fintype.card (LdeIdx sz n)
      ≤ Fintype.card (Idx d (sz.L n) (sz.W n)) * Fintype.card (Idx d (sz.L n) (sz.W n)) := by
    calc Fintype.card (LdeIdx sz n)
        = ∑ i : Idx d (sz.L n) (sz.W n), Fintype.card {a : Idx d (sz.L n) (sz.W n) // a ≠ i} :=
          Fintype.card_sigma
      _ ≤ ∑ _i : Idx d (sz.L n) (sz.W n), Fintype.card (Idx d (sz.L n) (sz.W n)) :=
          Finset.sum_le_sum fun i _ => Fintype.card_subtype_le _
      _ = Fintype.card (Idx d (sz.L n) (sz.W n)) * Fintype.card (Idx d (sz.L n) (sz.W n)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hcard] at this
  exact_mod_cast this

/-- The index set of the row LDE is polynomially large: `#LdeIdx ≤ (size n)²`. -/
theorem eventually_card_LdeIdx_le {d : ℕ} (sz : Sizes d) :
    ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (LdeIdx sz n) : ℝ) ≤ (sz.size n : ℝ) ^ (2 : ℝ) := by
  refine Filter.Eventually.of_forall fun n => ?_
  refine (card_LdeIdx_le n).trans (le_of_eq ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- **Stochastic domination for any row sum with off-row coefficients, with the time in the
index set.**  Given a family of times `tim n q ≥ 0`, rows `row n q` and coefficients `C n q`
that read only the corresponding off-row block, the normalised row sums are `≺ 1` along the
admissible size sequence `sz.size`, uniformly over a polynomially large index set.

The hypothesis `hsize` is needed (and is not automatic for `Sizes`): for constant sizes the
scale `N = size n` stays bounded and the domination would ask for probabilities `≤ N^{-D}` for
every `D`. -/
theorem stochDom_rowSum_generalTime (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
    (tim : ∀ n, U n → ℝ) (htim : ∀ n q, 0 ≤ tim n q)
    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω') :
    StochDomAt (Sizes.seqP sz) sz.size
      (fun n q ω =>
        ‖rowSum sz n (tim n q) (row n q)
          (rowCoeffNorm sz n (tim n q) (row n q) (C n q)) ω‖)
      (fun _ _ _ => 1) := by
  refine stochDomAt_of_momentDomAt sz.size hsize hcard (Φ := fun _ _ => (1 : ℝ))
    (fun _ _ => zero_lt_one) ?_ ?_
  · intro p n q
    have := integrable_norm_rowSum_norm_pow (sz := sz) (n := n) (u := tim n q) (i := row n q)
      (p := p) (htim n q) (C n q) (hCmeas n q) (fun ω ω' h => hC n q ω ω' h)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [abs_norm]
  · intro ε hε p
    have hd0 : (0 : ℝ) ≤ RowIndep_dfac p := by unfold RowIndep_dfac; positivity
    refine ⟨2 * RowIndep_dfac p + 1, by linarith, ?_⟩
    refine Filter.Eventually.of_forall fun n q => ?_
    have hn1 : (1 : ℝ) ≤ (sz.size n : ℝ) := by exact_mod_cast Sizes.one_le_size sz n
    have hbound := integral_norm_rowSum_norm_pow_le' (sz := sz) (n := n) (u := tim n q)
      (i := row n q) (p := p) (htim n q) (C n q) (hCmeas n q) (fun ω ω' h => hC n q ω ω' h)
    have habs : ∫ ω, |‖rowSum sz n (tim n q) (row n q)
          (rowCoeffNorm sz n (tim n q) (row n q) (C n q)) ω‖| ^ (2 * p) ∂(Sizes.seqP sz)
        = ∫ ω, ‖rowSum sz n (tim n q) (row n q)
            (rowCoeffNorm sz n (tim n q) (row n q) (C n q)) ω‖ ^ (2 * p) ∂(Sizes.seqP sz) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [abs_norm]
    rw [habs]
    have hpow : (1 : ℝ) ≤ (sz.size n : ℝ) ^ (ε * p) := Real.one_le_rpow hn1 (by positivity)
    have : (2 * RowIndep_dfac p)
        ≤ (2 * RowIndep_dfac p + 1) * ((sz.size n : ℝ) ^ (ε * p) * 1 ^ (2 * p)) := by
      rw [one_pow, mul_one]
      nlinarith [hpow, hd0]
    linarith [hbound, this]

/-- The single-time case of `stochDom_rowSum_generalTime`.  Both the row LDE and (by
Hermitian symmetry) the column LDE are instances. -/
theorem stochDom_rowSum_general (hu : 0 ≤ u)
    (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω') :
    StochDomAt (Sizes.seqP sz) sz.size
      (fun n q ω =>
        ‖rowSum sz n u (row n q) (rowCoeffNorm sz n u (row n q) (C n q)) ω‖)
      (fun _ _ _ => 1) :=
  stochDom_rowSum_generalTime hsize hcard (fun _ _ => u) (fun _ _ => hu) row C hCmeas hC

/-! ### The column LDE, by Hermitian symmetry -/

/-- The conjugate of the `k`-th row of the minor resolvent `(H^{(j)} - z)^{-1}`, as coefficients
indexed by all of `Idx d (sz.L n) (sz.W n)` (zero at `j`).  By Hermitian symmetry the column sum of
the paper is the conjugate of the row sum with these coefficients. -/
noncomputable def minorRowConj {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (j : Idx d (sz.L n) (sz.W n))
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) (ω : Sizes.SeqΩ sz) (l : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if h : l ≠ j then
    (starRingEnd ℂ) ((((Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ j} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ j} → _)
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ j}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ j} ℂ))⁻¹) k ⟨l, h⟩)
  else 0

theorem minorRowConj_congr (u : ℝ) (z : ℂ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j})
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ offRowCoord sz n j, ω c = ω' c) :
    minorRowConj sz n u z j k ω = minorRowConj sz n u z j k ω' := by
  funext l
  unfold minorRowConj
  rw [Hflow_submatrix_congr_offRowCoord u h]

theorem measurable_minorRowConj (u : ℝ) (z : ℂ) (j : Idx d (sz.L n) (sz.W n))
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) : Measurable (minorRowConj sz n u z j k) := by
  refine Measurable.of_eval fun l => ?_
  unfold minorRowConj
  split
  · refine Complex.continuous_conj.measurable.comp ?_
    exact measurable_inv_entries
      (A := fun ω : Sizes.SeqΩ sz => (Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ j} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ j} → _)
        - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ j} {a : Idx d (sz.L n) (sz.W n) // a ≠ j} ℂ))
      (fun a b => (Sizes.measurable_seqHflow_entry sz n u a.1 b.1).sub measurable_const) _ _
  · exact measurable_const

/-! ### The shifted minor resolvent (T2389, BA-G2)

The block Anderson flow is `H = D + X` with `D = g₀ Ψ` deterministic and `X` the Gaussian part
(`seqHflow` of `sz.withLam 0`).  The coefficients below are the entries of the minor of `D + X`;
`D` is a constant, so the proofs are those of `minorCol`, `minorRowConj` above (`D = 0` is the band).
The band declarations stay as they are; the row of `X` is still `seqHflow`. -/

/-- The `j`-th column of the minor resolvent of `D + X`, as coefficients on all of `Idx` (zero at `i`). -/
noncomputable def RowIndep_minorColD {d : ℕ} (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z : ℂ)
    (i : Idx d (sz.L n) (sz.W n)) (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) (ω : Sizes.SeqΩ sz)
    (k : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if h : k ≠ i then
    (((D + Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ i}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ i} ℂ))⁻¹) ⟨k, h⟩ j
  else 0

/-- The conjugate of the `k`-th row of the minor resolvent of `D + X` (the column sum of the paper is
the conjugate of a row sum with these coefficients). -/
noncomputable def RowIndep_minorRowConjD {d : ℕ} (sz : Sizes d) (n : ℕ)
    (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (u : ℝ) (z : ℂ)
    (j : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) (ω : Sizes.SeqΩ sz)
    (l : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if h : l ≠ j then
    (starRingEnd ℂ) ((((D + Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ j} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ j} → _)
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ j}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ j} ℂ))⁻¹) k ⟨l, h⟩)
  else 0

section Shift

variable (D : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

private theorem RowIndep_submatrix_add (A B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (i : Idx d (sz.L n) (sz.W n)) :
    (A + B).submatrix (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      = A.submatrix (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
          (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        + B.submatrix (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
          (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _) := rfl

/-- The minor of `D + X` reads only the off-row block of `X`. -/
theorem RowIndep_submatrix_shift_congr (u : ℝ) {i : Idx d (sz.L n) (sz.W n)}
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    (D + Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
      = (D + Sizes.seqHflow sz n u ω').submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _) := by
  rw [RowIndep_submatrix_add, RowIndep_submatrix_add, Hflow_submatrix_congr_offRowCoord u h]

theorem RowIndep_minorColD_congr (u : ℝ) (z : ℂ) {i : Idx d (sz.L n) (sz.W n)}
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i})
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ offRowCoord sz n i, ω c = ω' c) :
    RowIndep_minorColD sz n D u z i j ω = RowIndep_minorColD sz n D u z i j ω' := by
  funext k
  unfold RowIndep_minorColD
  rw [RowIndep_submatrix_shift_congr D u h]

theorem RowIndep_minorRowConjD_congr (u : ℝ) (z : ℂ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j})
    {ω ω' : Sizes.SeqΩ sz} (h : ∀ c ∈ offRowCoord sz n j, ω c = ω' c) :
    RowIndep_minorRowConjD sz n D u z j k ω = RowIndep_minorRowConjD sz n D u z j k ω' := by
  funext l
  unfold RowIndep_minorRowConjD
  rw [RowIndep_submatrix_shift_congr D u h]

/-- Every entry of `(D + X)^{(i)} - z` is measurable in `ω`. -/
private theorem RowIndep_measurable_shift_entry (u : ℝ) (z : ℂ) (i : Idx d (sz.L n) (sz.W n))
    (a b : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    Measurable fun ω : Sizes.SeqΩ sz => ((D + Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ i} → _)
        - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ i}
          {a : Idx d (sz.L n) (sz.W n) // a ≠ i} ℂ)) a b := by
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.add_apply]
  exact (measurable_const.add (Sizes.measurable_seqHflow_entry sz n u a.1 b.1)).sub measurable_const

theorem RowIndep_measurable_minorColD (u : ℝ) (z : ℂ) (i : Idx d (sz.L n) (sz.W n))
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    Measurable (RowIndep_minorColD sz n D u z i j) := by
  refine Measurable.of_eval fun k => ?_
  unfold RowIndep_minorColD
  split
  · exact measurable_inv_entries (RowIndep_measurable_shift_entry D u z i) _ _
  · exact measurable_const

theorem RowIndep_measurable_minorRowConjD (u : ℝ) (z : ℂ) (j : Idx d (sz.L n) (sz.W n))
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) :
    Measurable (RowIndep_minorRowConjD sz n D u z j k) := by
  refine Measurable.of_eval fun l => ?_
  unfold RowIndep_minorRowConjD
  split
  · exact Complex.continuous_conj.measurable.comp
      (measurable_inv_entries (RowIndep_measurable_shift_entry D u z j) _ _)
  · exact measurable_const


/-- Where the resolvent of `D + X` exists, `minorColD` is the entries of its minor `G^{(i)}`. -/
theorem RowIndep_minorColD_eq_greenMinor (u : ℝ) {i : Idx d (sz.L n) (sz.W n)}
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (D + Sizes.seqHflow sz n u ω) z i i ≠ 0) {k : Idx d (sz.L n) (sz.W n)}
    (hk : k ≠ i) :
    RowIndep_minorColD sz n D u z i j ω k
      = greenMinor (green (D + Sizes.seqHflow sz n u ω) z) i k j.1 := by
  unfold RowIndep_minorColD
  simp only [ne_eq, hk, not_false_eq_true, ↓reduceDIte]
  rw [inv_minor_resolvent hdet i hGii]
  rfl

/-- Where the resolvent of `D + X` exists, `minorRowConjD` is the conjugated entries of `G^{(j)}`. -/
theorem RowIndep_minorRowConjD_eq_greenMinor (u : ℝ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGjj : green (D + Sizes.seqHflow sz n u ω) z j j ≠ 0) {l : Idx d (sz.L n) (sz.W n)}
    (hl : l ≠ j) :
    RowIndep_minorRowConjD sz n D u z j k ω l
      = (starRingEnd ℂ) (greenMinor (green (D + Sizes.seqHflow sz n u ω) z) j k.1 l) := by
  unfold RowIndep_minorRowConjD
  rw [dite_eq_left_of_eq_true (by simpa using hl), inv_minor_resolvent hdet j hGjj]
  rfl

/-- **The left-hand side of the row LDE** (row of `X`, resolvent of `D + X`) is the row sum with the
minor column of `D + X`. -/
theorem RowIndep_ldeRowLHS_eqD (u : ℝ) {i : Idx d (sz.L n) (sz.W n)}
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (D + Sizes.seqHflow sz n u ω) z i i ≠ 0) :
    ldeRowLHS (Sizes.seqHflow sz n u ω) (green (D + Sizes.seqHflow sz n u ω) z) i j.1
      = ‖rowSum sz n u i (RowIndep_minorColD sz n D u z i j) ω‖ ^ 2 := by
  unfold ldeRowLHS rowSum
  congr 2
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [RowIndep_minorColD_eq_greenMinor D u j hdet hGii k.2]

/-- The variance of that row sum is `u` times the right-hand side of the row LDE. -/
theorem RowIndep_rowVarSum_eqD (u : ℝ) {i : Idx d (sz.L n) (sz.W n)}
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (D + Sizes.seqHflow sz n u ω) z i i ≠ 0) :
    rowVarSum sz n u i (RowIndep_minorColD sz n D u z i j) ω
      = u * ldeRowRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
          (green (D + Sizes.seqHflow sz n u ω) z) i j.1 := by
  unfold rowVarSum ldeRowRHS
  congr 1
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [RowIndep_minorColD_eq_greenMinor D u j hdet hGii k.2]

/-- **The left-hand side of the column LDE** is the conjugate of the row sum with the conjugated minor row. -/
theorem RowIndep_ldeColLHS_eqD (u : ℝ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGjj : green (D + Sizes.seqHflow sz n u ω) z j j ≠ 0) :
    ldeColLHS (Sizes.seqHflow sz n u ω) (green (D + Sizes.seqHflow sz n u ω) z) k.1 j
      = ‖rowSum sz n u j (RowIndep_minorRowConjD sz n D u z j k) ω‖ ^ 2 := by
  have key : rowSum sz n u j (RowIndep_minorRowConjD sz n D u z j k) ω
      = (starRingEnd ℂ) (∑ l ∈ Finset.univ.erase j,
          greenMinor (green (D + Sizes.seqHflow sz n u ω) z) j k.1 l
            * Sizes.seqHflow sz n u ω l j) := by
    unfold rowSum
    rw [map_sum, Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
      (fun l => by simp [Finset.mem_erase]) _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [RowIndep_minorRowConjD_eq_greenMinor D u k hdet hGjj l.2, map_mul,
      show (starRingEnd ℂ) (Sizes.seqHflow sz n u ω l.1 j) = Sizes.seqHflow sz n u ω j l.1 from
        (Sizes.seqHflow_isHermitian sz n u ω).apply j l.1]
    ring
  rw [key, Complex.norm_conj, ldeColLHS]

/-- The variance of the conjugated row sum is `u` times the right-hand side of the column LDE. -/
theorem RowIndep_rowVarSum_minorRowConjD_eq (u : ℝ) {j : Idx d (sz.L n) (sz.W n)}
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) {ω : Sizes.SeqΩ sz}
    (hdet : IsUnit (D + Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGjj : green (D + Sizes.seqHflow sz n u ω) z j j ≠ 0) :
    rowVarSum sz n u j (RowIndep_minorRowConjD sz n D u z j k) ω
      = u * ldeColRHS (svarF d (sz.L n) (sz.W n) (sz.lam n))
          (green (D + Sizes.seqHflow sz n u ω) z) k.1 j := by
  unfold rowVarSum ldeColRHS
  congr 1
  rw [Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
    (fun l => by simp [Finset.mem_erase]) _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [RowIndep_minorRowConjD_eq_greenMinor D u k hdet hGjj l.2, Complex.norm_conj,
    svarF_comm d (sz.L n) (sz.W n) (sz.lam n) j l.1]
  ring

/-- **The band is the shift `D = 0`:** the shifted minor column of `0 + X` is the band minor column. -/
theorem RowIndep_minorColD_zero (u : ℝ) (z : ℂ) (i : Idx d (sz.L n) (sz.W n))
    (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i}) :
    RowIndep_minorColD sz n 0 u z i j = minorCol sz n u z i j := by
  funext ω k
  simp only [RowIndep_minorColD, minorCol, zero_add]

/-- The same for the conjugated minor rows. -/
theorem RowIndep_minorRowConjD_zero (u : ℝ) (z : ℂ) (j : Idx d (sz.L n) (sz.W n))
    (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ j}) :
    RowIndep_minorRowConjD sz n 0 u z j k = minorRowConj sz n u z j k := by
  funext ω l
  simp only [RowIndep_minorRowConjD, minorRowConj, zero_add]

end Shift

/-- **The band row identity `ldeRowLHS_eq` is the corollary at `D = 0`** of `RowIndep_ldeRowLHS_eqD`. -/
example (u : ℝ) {i : Idx d (sz.L n) (sz.W n)} (j : {a : Idx d (sz.L n) (sz.W n) // a ≠ i})
    {ω : Sizes.SeqΩ sz} {z : ℂ}
    (hdet : IsUnit (Sizes.seqHflow sz n u ω - z • (1 : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGii : green (Sizes.seqHflow sz n u ω) z i i ≠ 0) :
    ldeRowLHS (Sizes.seqHflow sz n u ω) (green (Sizes.seqHflow sz n u ω) z) i j.1
      = ‖rowSum sz n u i (minorCol sz n u z i j) ω‖ ^ 2 := by
  have h0 : ∀ ω' : Sizes.SeqΩ sz, (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      + Sizes.seqHflow sz n u ω' = Sizes.seqHflow sz n u ω' := fun ω' => zero_add _
  have h := RowIndep_ldeRowLHS_eqD (z := z) (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    u j (ω := ω) (by rw [h0]; exact hdet) (by rw [h0]; exact hGii)
  rw [h0, RowIndep_minorColD_zero] at h
  exact h

/-- **The degenerate case.**  Where the conditional variance vanishes, so does the row sum,
almost surely: freezing the coefficients to `0` off that event gives a family whose variance is
identically `0`, hence whose second moment vanishes. -/
theorem rowSum_ae_eq_zero_of_varSum_eq_zero (hu : 0 ≤ u)
    (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ) (hCmeas : Measurable C)
    (hC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → C ω = C ω') :
    ∀ᵐ ω ∂(Sizes.seqP sz), rowVarSum sz n u i C ω = 0 → rowSum sz n u i C ω = 0 := by
  classical
  set D : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ :=
    fun ω k => if rowVarSum sz n u i C ω = 0 then C ω k else 0 with hD
  have hVmeas : Measurable (rowVarSum sz n u i C) := measurable_rowVarSum C hCmeas
  have hDmeas : Measurable D := by
    refine Measurable.of_eval fun k => ?_
    exact Measurable.ite (measurableSet_eq_fun hVmeas measurable_const)
      ((measurable_pi_apply k).comp hCmeas) measurable_const
  have hDC : ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ offRowCoord sz n i, ω c = ω' c) → D ω = D ω' := by
    intro ω ω' h
    have hCe := hC ω ω' h
    funext k
    simp only [hD, rowVarSum, hCe]
    rfl
  have hDvar : ∀ ω : Sizes.SeqΩ sz, rowVarSum sz n u i D ω = 0 := by
    intro ω
    by_cases h : rowVarSum sz n u i C ω = 0
    · have : D ω = C ω := by funext k; simp [hD, h]
      simp only [rowVarSum] at h ⊢
      rw [this]
      exact h
    · have : D ω = fun _ => (0 : ℂ) := by funext k; simp [hD, h]
      simp [rowVarSum, this]
  -- the second moment of the frozen family vanishes
  have hzero : ∫⁻ ω, ENNReal.ofReal (‖rowSum sz n u i D ω‖ ^ (2 * 1)) ∂(Sizes.seqP sz) = 0 := by
    refine le_antisymm ?_ (zero_le)
    refine lintegral_norm_rowSum_pow_le_of_const hu D hDmeas hDC fun ω => ?_
    simp [hDvar ω]
  have hae : ∀ᵐ ω ∂(Sizes.seqP sz), ENNReal.ofReal (‖rowSum sz n u i D ω‖ ^ (2 * 1)) = 0 := by
    rw [lintegral_eq_zero_iff'] at hzero
    · exact hzero
    · refine (ENNReal.measurable_ofReal.comp
        (Measurable.pow_const (Measurable.norm ?_) _)).aemeasurable
      unfold rowSum
      exact Finset.measurable_sum _ fun k _ =>
        (Sizes.measurable_seqHflow_entry sz n u i k.1).mul ((measurable_pi_apply k.1).comp hDmeas)
  filter_upwards [hae] with ω hω hV
  have hDC' : D ω = C ω := by funext k; simp [hD, hV]
  have : ‖rowSum sz n u i D ω‖ ^ (2 * 1) = 0 := by
    have := ENNReal.ofReal_eq_zero.1 hω
    have hnn : (0 : ℝ) ≤ ‖rowSum sz n u i D ω‖ ^ (2 * 1) := by positivity
    linarith
  have hnorm : ‖rowSum sz n u i D ω‖ = 0 := by
    have hp : ‖rowSum sz n u i D ω‖ ^ (2 * 1) = ‖rowSum sz n u i D ω‖ ^ 2 := by norm_num
    rw [hp, pow_eq_zero_iff (by norm_num)] at this
    exact this
  have : rowSum sz n u i D ω = 0 := by simpa using hnorm
  rwa [show rowSum sz n u i D ω = rowSum sz n u i C ω by
    unfold rowSum; simp only [hDC']] at this

/-- Normalising the coefficients divides the row sum by the conditional standard deviation. -/
theorem rowSum_rowCoeffNorm (C : Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ) {ω : Sizes.SeqΩ sz}
    (hV : 0 < rowVarSum sz n u i C ω) :
    rowSum sz n u i (rowCoeffNorm sz n u i C) ω
      = ((Real.sqrt (rowVarSum sz n u i C ω) : ℂ))⁻¹ * rowSum sz n u i C ω := by
  unfold rowSum rowCoeffNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hV, ↓reduceIte]
  field_simp

/-- **The row LDE as a high-probability inequality.**  For every `τ > 0`, with overwhelming
probability (measured against `sz.size n`) every pair `(x, j)` satisfies
`‖∑_{k ≠ x} H_{xk} C_{k}‖² ≤ (size n)^{2τ} · u ∑_k S_{xk}|C_k|²`. -/
theorem highProb_norm_rowSum_sq_le (hu : 0 ≤ u)
    (hsize : Filter.Tendsto sz.size Filter.atTop Filter.atTop)
    {U : ℕ → Type*} [∀ n, Fintype (U n)] {Ccard : ℝ}
    (hcard : ∀ᶠ n : ℕ in Filter.atTop, (Fintype.card (U n) : ℝ) ≤ (sz.size n : ℝ) ^ Ccard)
    (row : ∀ n, U n → Idx d (sz.L n) (sz.W n))
    (C : ∀ n, U n → Sizes.SeqΩ sz → Idx d (sz.L n) (sz.W n) → ℂ)
    (hCmeas : ∀ n q, Measurable (C n q))
    (hC : ∀ n q (ω ω' : Sizes.SeqΩ sz),
      (∀ c ∈ offRowCoord sz n (row n q), ω c = ω' c) → C n q ω = C n q ω')
    {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω | ∀ q : U n,
      ‖rowSum sz n u (row n q) (C n q) ω‖ ^ 2
        ≤ (sz.size n : ℝ) ^ (2 * τ) * rowVarSum sz n u (row n q) (C n q) ω}) := by
  classical
  -- the normalised sums are `≺ 1`
  have hgood := stochDom_rowSum_general (sz := sz) (u := u) hu hsize hcard row C hCmeas hC
  -- the degenerate fibres are negligible
  have hnull : ∀ n : ℕ, (Sizes.seqP sz) {ω | ¬ ∀ q : U n,
      rowVarSum sz n u (row n q) (C n q) ω = 0 → rowSum sz n u (row n q) (C n q) ω = 0} = 0 := by
    intro n
    have hae : ∀ᵐ ω ∂(Sizes.seqP sz), ∀ q : U n,
        rowVarSum sz n u (row n q) (C n q) ω = 0 → rowSum sz n u (row n q) (C n q) ω = 0 := by
      rw [MeasureTheory.ae_all_iff]
      intro q
      exact rowSum_ae_eq_zero_of_varSum_eq_zero hu (C n q) (hCmeas n q) (hC n q)
    simpa [MeasureTheory.ae_iff] using hae
  intro D hD
  filter_upwards [hgood τ hτ D hD] with n hn
  have hpos : (0 : ℝ) < (sz.size n : ℝ) := by exact_mod_cast Sizes.one_le_size sz n
  -- outside the bad event and the degenerate null set, the inequality holds
  have hsub : ({ω | ∀ q : U n,
      ‖rowSum sz n u (row n q) (C n q) ω‖ ^ 2
        ≤ (sz.size n : ℝ) ^ (2 * τ) * rowVarSum sz n u (row n q) (C n q) ω}ᶜ : Set (Sizes.SeqΩ sz))
      ⊆ badSetAt sz.size (fun n q ω =>
          ‖rowSum sz n u (row n q) (rowCoeffNorm sz n u (row n q) (C n q)) ω‖)
          (fun _ _ _ => (1 : ℝ)) τ n
        ∪ {ω | ¬ ∀ q : U n,
          rowVarSum sz n u (row n q) (C n q) ω = 0 → rowSum sz n u (row n q) (C n q) ω = 0} := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : ∀ q : U n, ‖rowSum sz n u (row n q) (rowCoeffNorm sz n u (row n q) (C n q)) ω‖
        ≤ (sz.size n : ℝ) ^ τ * 1 := fun q => by
      by_contra hq
      exact h1 ⟨q, not_le.1 hq⟩
    have h2' : ∀ q : U n, rowVarSum sz n u (row n q) (C n q) ω = 0 →
        rowSum sz n u (row n q) (C n q) ω = 0 := by
      by_contra hq
      exact h2 hq
    apply hω
    intro q
    have hV0 : 0 ≤ rowVarSum sz n u (row n q) (C n q) ω := rowVarSum_nonneg hu (C n q) ω
    rcases eq_or_lt_of_le hV0 with hV | hV
    · rw [← hV, h2' q hV.symm]
      simp
    · have hs : (0 : ℝ) < Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω) := Real.sqrt_pos.2 hV
      have hnorm := h1' q
      rw [rowSum_rowCoeffNorm (C n q) hV, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs.le, mul_one] at hnorm
      have hle : ‖rowSum sz n u (row n q) (C n q) ω‖
          ≤ (sz.size n : ℝ) ^ τ * Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω) := by
        rw [inv_mul_le_iff₀ hs] at hnorm
        linarith [hnorm]
      have hnn : (0 : ℝ) ≤ ‖rowSum sz n u (row n q) (C n q) ω‖ := norm_nonneg _
      have hrhs : (0 : ℝ) ≤ (sz.size n : ℝ) ^ τ
          * Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω) := by
        have : (0 : ℝ) ≤ (sz.size n : ℝ) ^ τ := Real.rpow_nonneg (by positivity) τ
        positivity
      have hsq := mul_le_mul hle hle hnn hrhs
      have hsqrt : Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω) *
          Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω)
          = rowVarSum sz n u (row n q) (C n q) ω := Real.mul_self_sqrt hV0
      have hNpow : (sz.size n : ℝ) ^ τ * (sz.size n : ℝ) ^ τ = (sz.size n : ℝ) ^ (2 * τ) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      calc ‖rowSum sz n u (row n q) (C n q) ω‖ ^ 2
          = ‖rowSum sz n u (row n q) (C n q) ω‖ * ‖rowSum sz n u (row n q) (C n q) ω‖ := by ring
        _ ≤ ((sz.size n : ℝ) ^ τ * Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω)) *
            ((sz.size n : ℝ) ^ τ * Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω)) := hsq
        _ = ((sz.size n : ℝ) ^ τ * (sz.size n : ℝ) ^ τ) *
            (Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω) *
              Real.sqrt (rowVarSum sz n u (row n q) (C n q) ω)) := by ring
        _ = (sz.size n : ℝ) ^ (2 * τ) * rowVarSum sz n u (row n q) (C n q) ω := by
            rw [hNpow, hsqrt]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull n, add_zero]
  exact hn


end RBM.Green

namespace RBM.Green.RowIndepInst

/-! ### Compiled nonempty instances at the preflight sequence `sz0` (`d = 3`)

`SizesInst.sz0` (`RBM3D/Defs/Sizes.lean:259`): `L n = 4 (n + 1)`, `W n = (2 (n + 1))^5`,
`lam n = (2 (n + 1))^{-6}`, `N = (W L)^3 = 2097152` at `n = 0`.  Every deterministic hypothesis of
the theorems below is discharged: `hsize` (`sz0_tendsto`), the cardinality bound `#LdeIdx ≤ N²`
(`eventually_card_LdeIdx_le`, `Ccard = 2`), measurability and off-row determination of the
coefficients `minorCol` (the minor-resolvent columns, the application of the paper's row LDE).
There is no external hypothesis. -/

open RBM.Gauss RBM.Gauss.SizesInst RBM.Green
open scoped NNReal ENNReal

/-- `sz0.size` tends to infinity in `ℕ` (`sz0_tendsto` is the real-valued form). -/
private theorem sz0_size_tendsto : Filter.Tendsto sz0.size Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_iff.1 sz0_tendsto

/-- The index set of the row LDE is nonempty at every `n`: rows `0` and a second point, so the
instances below are not over an empty index set. -/
theorem LdeIdx_nonempty_sz0 (n : ℕ) : Nonempty (LdeIdx sz0 n) := by
  have : Fact (1 < sz0.W n * sz0.L n) :=
    ⟨by have := sz0.three_le_L n; have := sz0.W_pos n; nlinarith⟩
  refine ⟨⟨0, ⟨Function.update 0 0 1, fun h => ?_⟩⟩⟩
  have h0 := congrFun h 0
  simp at h0

/-- **Instance of `highProb_norm_rowSum_sq_le`** at `sz0`, `u = 1`, `τ = 1/10`, `Ccard = 2`: the
row LDE for the minor-resolvent columns `C n q = minorCol sz0 n 1 z q.1 q.2`, indexed by all
`(row, column)` pairs `LdeIdx sz0 n` (`#LdeIdx ≤ N²`), at the spectral parameter `z`. -/
theorem highProb_norm_rowSum_sq_le_sz0 (z : ℂ) :
    HighProbAt (Sizes.seqP sz0) sz0.size (fun n => {ω | ∀ q : LdeIdx sz0 n,
      ‖rowSum sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2) ω‖ ^ 2
        ≤ (sz0.size n : ℝ) ^ (2 * (1 / 10 : ℝ)) *
          rowVarSum sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2) ω}) :=
  highProb_norm_rowSum_sq_le (U := fun n => LdeIdx sz0 n) (Ccard := 2) zero_le_one
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ q => q.1)
    (fun n q => minorCol sz0 n 1 z q.1 q.2) (fun _ q => measurable_minorCol 1 z q.1 q.2)
    (fun _ q _ _ h => minorCol_congr 1 z q.2 h) (by norm_num)

/-- **Instance of `stochDom_rowSum_general`** at `sz0`, `u = 1`: the normalised row sums of the
minor-resolvent columns are `≺ 1` at the scale `N = sz0.size`, uniformly over `LdeIdx sz0 n`. -/
theorem stochDom_rowSum_general_sz0 (z : ℂ) :
    StochDomAt (Sizes.seqP sz0) sz0.size
      (fun n (q : LdeIdx sz0 n) ω =>
        ‖rowSum sz0 n 1 q.1 (rowCoeffNorm sz0 n 1 q.1 (minorCol sz0 n 1 z q.1 q.2)) ω‖)
      (fun _ _ _ => 1) :=
  stochDom_rowSum_general (U := fun n => LdeIdx sz0 n) (Ccard := 2) zero_le_one
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ q => q.1)
    (fun n q => minorCol sz0 n 1 z q.1 q.2) (fun _ q => measurable_minorCol 1 z q.1 q.2)
    (fun _ q _ _ h => minorCol_congr 1 z q.2 h)

/-- **Instance of `stochDom_rowSum_generalTime`** at `sz0` with a time depending on the index,
`tim n q = 1/2`. -/
theorem stochDom_rowSum_generalTime_sz0 (z : ℂ) :
    StochDomAt (Sizes.seqP sz0) sz0.size
      (fun n (q : LdeIdx sz0 n) ω =>
        ‖rowSum sz0 n (1 / 2) q.1 (rowCoeffNorm sz0 n (1 / 2) q.1 (minorCol sz0 n (1 / 2) z q.1 q.2)) ω‖)
      (fun _ _ _ => 1) :=
  stochDom_rowSum_generalTime (U := fun n => LdeIdx sz0 n) (Ccard := 2)
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ _ => 1 / 2) (fun _ _ => by norm_num)
    (fun _ q => q.1) (fun n q => minorCol sz0 n (1 / 2) z q.1 q.2)
    (fun _ q => measurable_minorCol (1 / 2) z q.1 q.2)
    (fun _ q _ _ h => minorCol_congr (1 / 2) z q.2 h)

/-- A nonzero Hermitian shift for the instances of the `D`-versions (T2389): `D = (1/2) I` at `sz0`. -/
private noncomputable def shiftD (n : ℕ) :
    Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)

/-- **Instance of the shifted minor columns** at `sz0`, `u = 1/2`, `D = (1/2) I`: the normalised row sums with the
coefficients `RowIndep_minorColD` (measurable, reading only the off-row block) are `≺ 1`, uniformly over `LdeIdx sz0 n`. -/
theorem RowIndep_stochDom_rowSum_generalTime_shift_sz0 (z : ℂ) :
    StochDomAt (Sizes.seqP sz0) sz0.size
      (fun n (q : LdeIdx sz0 n) ω =>
        ‖rowSum sz0 n (1 / 2) q.1
          (rowCoeffNorm sz0 n (1 / 2) q.1 (RowIndep_minorColD sz0 n (shiftD n) (1 / 2) z q.1 q.2)) ω‖)
      (fun _ _ _ => 1) :=
  stochDom_rowSum_generalTime (U := fun n => LdeIdx sz0 n) (Ccard := 2)
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ _ => 1 / 2) (fun _ _ => by norm_num)
    (fun _ q => q.1) (fun n q => RowIndep_minorColD sz0 n (shiftD n) (1 / 2) z q.1 q.2)
    (fun n q => RowIndep_measurable_minorColD (shiftD n) (1 / 2) z q.1 q.2)
    (fun n q _ _ h => RowIndep_minorColD_congr (shiftD n) (1 / 2) z q.2 h)

/-- The same for the conjugated minor rows `RowIndep_minorRowConjD` (the column LDE). -/
example (z : ℂ) :
    StochDomAt (Sizes.seqP sz0) sz0.size
      (fun n (q : LdeIdx sz0 n) ω =>
        ‖rowSum sz0 n (1 / 2) q.1
          (rowCoeffNorm sz0 n (1 / 2) q.1 (RowIndep_minorRowConjD sz0 n (shiftD n) (1 / 2) z q.1 q.2)) ω‖)
      (fun _ _ _ => 1) :=
  stochDom_rowSum_generalTime (U := fun n => LdeIdx sz0 n) (Ccard := 2)
    sz0_size_tendsto (eventually_card_LdeIdx_le sz0) (fun _ _ => 1 / 2) (fun _ _ => by norm_num)
    (fun _ q => q.1) (fun n q => RowIndep_minorRowConjD sz0 n (shiftD n) (1 / 2) z q.1 q.2)
    (fun n q => RowIndep_measurable_minorRowConjD (shiftD n) (1 / 2) z q.1 q.2)
    (fun n q _ _ h => RowIndep_minorRowConjD_congr (shiftD n) (1 / 2) z q.2 h)

/-- Each row of the variance profile sums to `1` (`3 ≤ L`): `∑_k S_{xk} = ∑_b S^{(B)}_{ab} = 1`
(`sum_sbKernelR`, `Defs/Block.lean:93`; the bridge `splitEquiv`). -/
private theorem sum_svarF_row (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (x : Idx d L W) : ∑ k : Idx d L W, svarF d L W g x k = 1 := by
  have h1 : ∑ k : Idx d L W, svarF d L W g x k
      = ∑ p : Vtx d L W, ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W x).1 p.1 :=
    Fintype.sum_equiv (splitEquiv d L W) _ _ fun k => rfl
  have h2 : ∑ b, SBR d L g (split d L W x).1 b = 1 := by
    rw [← sum_sbKernelR d L g hL]
    exact Fintype.sum_equiv (Equiv.subLeft (split d L W x).1) _ _ fun b => by simp [SBR]
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  calc ∑ a : Zd d L, ((W : ℝ) ^ d) * (((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W x).1 a)
      = ∑ a : Zd d L, SBR d L g (split d L W x).1 a :=
        Finset.sum_congr rfl fun a _ => by rw [← mul_assoc, mul_inv_cancel₀ hW, one_mul]
    _ = 1 := h2

/-- **Instance of `integral_norm_row_sum_pow_le`** (frozen coefficients) at `sz0`, `n = 0`
(`N = 2097152`), row `x = 0`, `u = 1`, `c ≡ 1`, `p = 2`: `E‖∑_{k≠x} H_{xk}‖⁴ ≤ 2 · 3 · S²` with
`S = ∑_{k≠x} S_{xk} = 1 - W^{-d} (1 + 2 d g²)⁻¹ ≤ 1`, hence `E‖∑_{k≠x} H_{xk}‖⁴ ≤ 6`. -/
theorem integral_norm_row_sum_pow_le_sz0 :
    ∫ ω, ‖∑ k : {k : Idx 3 (sz0.L 0) (sz0.W 0) // k ≠ 0},
        Sizes.seqHflow sz0 0 1 ω 0 k.1‖ ^ (2 * 2) ∂(Sizes.seqP sz0) ≤ 6 := by
  have hd : RowIndep_dfac 2 = 3 := by
    simp [RowIndep_dfac, Finset.prod_range_succ]
    norm_num
  have h := integral_norm_row_sum_pow_le (sz := sz0) (n := 0) (u := 1) zero_le_one
    (0 : Idx 3 _ _) (fun _ => (1 : ℂ)) 2
  have hS : ∑ k : {k : Idx 3 (sz0.L 0) (sz0.W 0) // k ≠ 0},
      svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 k.1 ≤ 1 := by
    rw [sum_subtype_ne (0 : Idx 3 (sz0.L 0) (sz0.W 0))
      (fun k => svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 k),
      sum_svarF_row 3 _ _ _ (sz0.three_le_L 0)]
    linarith [svarF_nonneg 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 0]
  have hS0 : 0 ≤ ∑ k : {k : Idx 3 (sz0.L 0) (sz0.W 0) // k ≠ 0},
      svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 k.1 :=
    Finset.sum_nonneg fun k _ => svarF_nonneg _ _ _ _ _ _
  simp only [norm_one, one_pow, mul_one, one_mul, hd] at h
  refine h.trans ?_
  nlinarith [hS, hS0]

/-- **Row independence is not vacuous** (`AgreeOffRow`, `Hflow_submatrix_congr`): for any two
distinct points `x ≠ y` of the lattice there are sample points that agree on every coordinate off
row `x` and whose flows at time `1` differ in the entry `H_{xy}`. -/
private theorem exists_agreeOffRow_ne {d : ℕ} {sz : Sizes d} {n : ℕ}
    {x y : Idx d (sz.L n) (sz.W n)} (hxy : x ≠ y) :
    ∃ ω ω' : Sizes.SeqΩ sz, AgreeOffRow sz n x ω ω' ∧
      Sizes.seqHflow sz n 1 ω ≠ Sizes.seqHflow sz n 1 ω' := by
  classical
  refine ⟨0, Function.update 0 (rowCoord sz n x y true) 1, ?_, ?_⟩
  · intro k l b hk hl
    have hc : (⟨n, k, l, b⟩ : Sizes.SeqCoord sz) ≠ rowCoord sz n x y true := fun hcc => by
      have h' : rowCoord sz n x y true ∈ rowSet sz n x := rowCoord_mem_rowSet x y true
      rw [← hcc, mem_rowSet] at h'
      rcases h' with h | h
      · exact hk h
      · exact hl h
    simp [Function.update_of_ne hc]
  · intro hEq
    have h1 := congrFun (congrFun hEq x) y
    rw [seqHflow_apply, seqHflow_apply, Xentry_eq_rowCoord hxy, Xentry_eq_rowCoord hxy] at h1
    have hf : rowCoord sz n x y false ≠ rowCoord sz n x y true := fun hcc => by
      have := rowCoord_injOn (sz := sz) (n := n) (i := x) (k := y) (l := y)
        (b := false) (c := true) (Ne.symm hxy) (Ne.symm hxy) hcc
      simp at this
    simp [Function.update_self, Function.update_of_ne hf] at h1

/-- The instance of the previous check at `sz0`, `n = 0` (`N = 2097152`), `x = 0`, `y = (1,1,1)`. -/
theorem exists_agreeOffRow_ne_sz0 :
    ∃ ω ω' : Sizes.SeqΩ sz0, AgreeOffRow sz0 0 (0 : Idx 3 (sz0.L 0) (sz0.W 0)) ω ω' ∧
    Sizes.seqHflow sz0 0 1 ω ≠ Sizes.seqHflow sz0 0 1 ω' := by
  have : Fact (1 < sz0.W 0 * sz0.L 0) :=
    ⟨by have := sz0.three_le_L 0; have := sz0.W_pos 0; nlinarith⟩
  exact exists_agreeOffRow_ne (sz := sz0) (n := 0) (x := 0) (y := fun _ => 1)
    fun h => zero_ne_one (α := ZMod (sz0.W 0 * sz0.L 0)) (congrFun h 0)

end RBM.Green.RowIndepInst
