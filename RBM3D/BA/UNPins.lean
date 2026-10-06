/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.FlowPins
import RBM3D.Universality.PinsC2
import RBM3D.Endpoints
import RBM3D.Defs.Neighbours
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `RBM3D.BA.UNPins` (BA-C1b): the UN-side block Anderson pins

Ticket T2241 (BA-C1b, second half of the portmap row BA-C1; the split note is
`docs/tickets/T2197.md:28-30`).  Port of the compiled design probe `RBM3D/Probe/T2173Pins.lean`
(branch `t/T2173`, `a543154`; never merged) under the merged substitutions S1-S6 of T2187
(`RBM3D/Universality/PinsK.lean:21-26`), the merged non-centred `ouMat` (probe `ouMatNC`), and the
re-routings R1-R5 of the ticket (the C form is the C″ form of T2213):

* R1 `UNDens ↦ UNDens'` (`UNDensBARow'`); R2 `UNTrLocalInit ↦ UNTrLocalInit'`
  (`UNTrLocalInitBARow'`);
* R3 `baBUniv_of_rows` consumes `UNCoreC''` and supplies `UNMeanBound` by `unMeanBound_ba`;
* R4 the `(Meq:QUE2)` half of `BAEnd_QUEL` is the merged `RBM.Endpoints.que2BadMat`;
* R5 `inst_UNStep1GoodC` is replaced by `inst_step1GoodC''_ba` over the proved `step1GoodC''`.

No refuted pin (`UNStep1Good`, `UNInfty1Row`, `UNStep1GoodC`, `UNCoreC`, `UNTrLocalInit`,
`UNStep1GoodC'`, `UNCoreC'`) occurs in a statement or hypothesis of this file.  Every block
Anderson law is `Sizes.seqP (sz.withLam 0)` (`UNModel.ba`, DECISIONS §57 (3), paper-delta T2173a).

Sections: 1 the model `UNModelC.ba` and the kind `UNKind.ba`; 2 the consumed inputs, the four BA
rows and `un_claimAll_of_rowsBA`; 3 the input rows of the core and `unMeanBound_ba`; 4 the end pins
`BAEnd_QUEL`, `BAEnd_BUnivL` and the assembly `baBUniv_of_rows`; 5 the centred flow; 6 the `λ = 0`
extremes; 7 the bad event of one block; 8 compiled nonempty instances (class sequences
`RBM.BA.UNPinsInst`, UN instances `RBM.Univ.BAInst`).

Not here (ticket T2241): the BA event forms `BAGbEXPii/ij/av` (DECISIONS §72 (4)); any proof of an
owed row; the drift and the generator identity (UN-15); `BAEnd_locSC`, `BAEnd_decol`, `BAkPoint`,
`BAeigs`, `BAgueP`, `BArhoSC`, `BAunivConclL*` (replaced by merged vocabulary).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open scoped NNReal ENNReal Kronecker

namespace RBM.Univ

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. The model `UNModelC.ba` and the kind `UNKind.ba` -/

/-- **The block Anderson model with its mean** (`(eq:H_blocka)`, `1_2:611-616`): the merged `UNModel.ba` (law
`Sizes.seqP (sz.withLam 0)`, matrix `Sizes.seqHBA sz`) and the deterministic mean `E H = λ Ψ` that the centred OU flow
holds fixed (probe `UNModel.ba` with its field `mean`, `:146-160`, under S1). -/
def UNModelC.ba {d : ℕ} (sz : Sizes d) : UNModelC sz :=
  { UNModel.ba sz with
    mean := fun n => (sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n)
    mean_herm := fun n => by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
        show star (sz.lam n : ℂ) = (sz.lam n : ℂ) from Complex.conj_ofReal _] }

/-- What `UNModelC.ba` is: the underlying model is the merged `UNModel.ba sz` and the mean is `λ_n Ψ` (`rfl` facts). -/
theorem UNModelC.ba_spec :
    ∀ {d : ℕ} (sz : Sizes d), (UNModelC.ba sz).toUNModel = UNModel.ba sz ∧
      ∀ n : ℕ, (UNModelC.ba sz).mean n = (sz.lam n : ℂ) • PsiI d (sz.L n) (sz.W n) :=
  fun _ => ⟨rfl, fun _ => rfl⟩

/-- The underlying model of `UNModelC.ba sz` is the merged `UNModel.ba sz` (`rfl`). -/
theorem UNModelC.ba_toUNModel {d : ℕ} (sz : Sizes d) : (UNModelC.ba sz).toUNModel = UNModel.ba sz := rfl

/-- **The block Anderson kind**: `UNModelC.ba`, profile coupling `0` (`S^{(B)}(0) = I`, `1_2:606`), bulk
`ρ_N(E) ≥ κ` (`BAbulk`, DECISIONS §51), `m = m(·, λ)` of `(self_m)` (`BAm`); probe `UNKind.ba`, `:2262-2266`,
under S1, S6. -/
def UNKind.ba (d : ℕ) : UNKind d where
  M := UNModelC.ba
  lamV := fun _ _ => 0
  bulk := fun sz κ E n => BAbulk d (sz.L n) (sz.lam n) κ E
  mdet := fun sz n => BAm d (sz.L n) (sz.lam n)

/-- The model of the block Anderson kind is `UNModelC.ba` (the analogue of the merged `unPinsK_band_M`, `rfl`). -/
theorem UNKind.ba_M {d : ℕ} (sz : Sizes d) : (UNKind.ba d).M sz = UNModelC.ba sz := rfl

/-! ## 2. The consumed inputs, the four BA rows and `un_claimAll_of_rowsBA` -/

section Consumed

/-- **Consumed: `(Meq:QUE)` of the block Anderson model at `t = 0`** (`UNQuek` at `UNKind.ba`; T2161 `BAEnd_QUE` with
the law `seqP (sz.withLam 0)`).  Registry class: **owed** (BA-M3, through `UNQueBA_of_BAEnd_QUEL`). -/
def UNQueBA : Prop := UNQuek (fun d => UNKind.ba d)

/-- **Consumed: `(G_bound_ave)` of the block Anderson model** (`UNLocAvgk` at `UNKind.ba`).  Registry class: **owed**
(BA-M1; T2161 `BAEnd_locSC` with the law `seqP (sz.withLam 0)`, T2173a). -/
def UNLocAvgBA : Prop := UNLocAvgk (fun d => UNKind.ba d)

/-- **Consumed from BA-V3: the flow outputs `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` of the block Anderson flow** at
every time sequence `0 ≤ t_n ≤ t₀_n` (`(eq:t0E0_BA)`, `7_8:1798`): the conclusions of `lem:main_ind_BA` over the carrier
`baFMz` **under the law `seqP (sz.withLam 0)`** (probe `:2414-2419`, verbatim; it reads only the merged T2197 names).
Shape of the band `UNMLOut` with `STFlow ↦ BAFlow`, `lemT ↦ BAflowT0`, `STLK ↦ STLKgL …`.  Registry class: **owed**
(BA-V3, from `BAMainInd` through `BAFamZ_main`). -/
def UNMLOutBA (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
        STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STExp2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
        STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

end Consumed

section Rows

/-- `UNOURowBA`: the `𝐇_t` claims of the **centred** block Anderson flow from `UNMLOutBA`, `UNLocAvgBA`, `UNQueBA`
(`UNOURowk` at `UNKind.ba`).  Registry class: **owed** (the model-generic UN rows at `K = UNKind.ba`). -/
def UNOURowBA : Prop :=
  UNOURowk (fun d => UNKind.ba d) (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA

/-- `UNEMCTE2RowBA`: the weighted `(EMCTE2)` of the block Anderson kind (`UNEMCTE2Rowk` at `UNKind.ba`).  Registry
class: **owed** (the model-generic UN rows). -/
def UNEMCTE2RowBA : Prop := UNEMCTE2Rowk (fun d => UNKind.ba d)

/-- `UNJakUywRowBA`: `(jaklsdufowe)`, `(uywy7723r3rf)` of the block Anderson kind (`UNJakUywRowk` at `UNKind.ba`).
Registry class: **owed** (the model-generic UN rows). -/
def UNJakUywRowBA : Prop := UNJakUywRowk (fun d => UNKind.ba d) UNLocAvgBA

/-- `UNClaimRowBA`: the arithmetic row from `(EMCTE2)`, `(jaklsdufowe)`, `(uywy7723r3rf)` to `(417)` (`UNClaimRowk` at
`UNKind.ba`).  Registry class: **owed** (the model-generic UN rows). -/
def UNClaimRowBA : Prop := UNClaimRowk (fun d => UNKind.ba d)

/-- **The Claim `(417)` of the block Anderson model from the BA rows**: for every admissible `sz`, `κ > 0` and every
`E` that is eventually in the ρ-bulk `{ρ_N ≥ κ}`, `UNClaimAllC sz (UNModelC.ba sz) E` (the centred OU flow of
`H = V + ilambda Ψ`); the input of `UNCoreC''` for the block Anderson model (DECISIONS §48 (i); probe
`un_claimAll_of_rowsBA`, `:2496-2501`, under S5). -/
theorem un_claimAll_of_rowsBA (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA)
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → UNClaimAllC sz (UNModelC.ba sz) E :=
  un_claimAll_of_rowsk (fun d => UNKind.ba d) rC rE rJ rO hML hLoc hQ

end Rows

/-! ## 3. The input rows of the core and the mean bound -/

section BAInputs

/-- **BA row (density)**: the regularity data of `UNDens'` for `m = m(·, λ_n)`, `ρ_N = π⁻¹ Im m(E + i0)`, and the bulk
stability of the window (DECISIONS §51): there is `δ₀ > 0` (depending on `κ`, `E`) such that for `δ ≤ δ₀` the window
`|x - E| ≤ δ` stays in the `κ/2`-bulk (probe `UNDensBARow`, `:2588-2593`, with `UNDens ↦ UNDens'`, R1).  The uniform
modulus of `(z, λ) ↦ m(z, λ)` is not among the T2161 pins.  Registry class: **owed** (BA-C2, through
`unDens'_freeConvST`). -/
def UNDensBARow' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        UNDens' (fun n => BAm d (sz.L n) (sz.lam n)) E (fun n => BArho d (sz.L n) (sz.lam n) E) δ ∧
          ∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x

/-- **BA row (tracial law of `H`)**: `UNTrLocal` of the block Anderson model at `m(·, λ_n)` from `(G_bound_ave)` (the
average over the `L^d` blocks of the block averages; probe `UNTrLocalBARow`, `:2597-2601`, under S4).  Registry class:
**owed** (BA-N1). -/
def UNTrLocalBARow : Prop :=
  UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocal sz (UNModelC.ba sz).toUNModel (fun n => BAm d (sz.L n) (sz.lam n)) E δ

/-- **BA row (initial-data local law)**: `UNTrLocalInit'` of the block Anderson model at `m(·, λ_n)` (probe
`UNTrLocalInitBARow`, `:2606-2610`, with `UNTrLocalInit ↦ UNTrLocalInit'`, R2).  Route (supervisor 1955 B2): the initial
matrix is `ouInit = e^{-t*/2} (V + λ̂ Ψ)`, the block Anderson matrix at the coupling `λ̂ = λ e^{t*/2}`, i.e. the model
at `sz.withLam (lamHat sz (ouTStar sz τs))`, admissible at `(𝔠, 𝔡/2)` by `admissible_lamHat`; the local law at `λ̂` and
the shift `|a⁻¹ m(z/a; λ̂) - m(z; λ)| ≤ C t*` are absorbed by the tolerance `W^τ (Bctl + t*)`.  Registry class:
**owed** (BA-N1, with the BA-D8 coupling Lipschitz bound). -/
def UNTrLocalInitBARow' : Prop :=
  UNLocAvgBA → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ δ : ℝ, 0 < δ →
      (∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) →
        UNTrLocalInit' sz (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E δ

/-- **BA row (norm bound)**: `(2.3)` of [32] for `H = V + ilambda Ψ`: `‖H‖ ≤ ‖V‖ + ilambda ‖Ψ‖`, `‖Ψ‖ ≤ 2d`,
`ilambda ≤ 𝔡⁻¹`, `‖V‖ ≤ N` with probability `≥ 1 - N^{-D}` (Gaussian tails); probe `UNNormBARow`, `:2614-2616`,
under S4.  Registry class: **owed** (BA-N1). -/
def UNNormBARow : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz (UNModelC.ba sz).toUNModel CV₀

end BAInputs

section MeanBound

/-- **Weyl-type bound by the maximal absolute row sum** (the argument of the private `FlowPins_eig_le`,
`FlowPins.lean:734-780`, at a general Hermitian matrix; re-proved, not imported): if every row of `A` has
`∑ j ‖A i j‖ ≤ R`, every eigenvalue of `A` has modulus `≤ R` (take an index of maximal `‖v i‖` in an eigenvector). -/
private theorem UNPins_eig_le_rowsum {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {R : ℝ} (hR : ∀ i, ∑ j, ‖A i j‖ ≤ R) (j : ι) : |hA.eigenvalues j| ≤ R := by
  classical
  have : Nonempty ι := ⟨j⟩
  set v : ι → ℂ := ⇑(hA.eigenvectorBasis j) with hv
  have hvne : ∃ k, v k ≠ 0 := by
    have h0 := (hA.eigenvectorBasis.orthonormal).ne_zero j
    by_contra hno
    push Not at hno
    apply h0
    ext k
    exact hno k
  have heq : A *ᵥ v = ((hA.eigenvalues j : ℝ) : ℂ) • v := hA.mulVec_eigenvectorBasis j
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => ‖v k‖)
  obtain ⟨k0, hk0⟩ := hvne
  have hvi : v i ≠ 0 := by
    intro h
    apply hk0
    have := hi k0
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrow := congrFun heq i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  have hnorm : ‖((hA.eigenvalues j : ℝ) : ℂ)‖ * ‖v i‖ ≤ R * ‖v i‖ := by
    calc ‖((hA.eigenvalues j : ℝ) : ℂ)‖ * ‖v i‖ = ‖((hA.eigenvalues j : ℝ) : ℂ) * v i‖ := (norm_mul _ _).symm
      _ = ‖∑ b, A i b * v b‖ := by rw [hrow]
      _ ≤ ∑ b, ‖A i b * v b‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖A i b‖ * ‖v i‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hi b) (norm_nonneg _)
      _ = (∑ b, ‖A i b‖) * ‖v i‖ := by rw [Finset.sum_mul]
      _ ≤ R * ‖v i‖ := mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _)
  have hpos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
  have := le_of_mul_le_mul_right hnorm hpos
  simpa using this

/-- The row sum of `Ψ` on the fine lattice: `∑_y |Ψ_{xy}| = 2d` for `L ≥ 3` (one nonzero offset per neighbouring block,
`Ψ = Ψ^{(B)} ⊗ I_{W^d}` through `splitEquiv`; `RBM.card_adj`). -/
private theorem UNPins_psiI_rowsum (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (x : Idx d L W) :
    ∑ y, ‖PsiI d L W x y‖ = 2 * d := by
  classical
  have h1 : ∀ y, ‖PsiI d L W x y‖ =
      ‖PsiV d L W (splitEquiv d L W x) (splitEquiv d L W y)‖ := fun y => rfl
  simp_rw [h1]
  rw [Equiv.sum_comp (splitEquiv d L W) (fun v => ‖PsiV d L W (splitEquiv d L W x) v‖)]
  obtain ⟨a, p⟩ := splitEquiv d L W x
  rw [Fintype.sum_prod_type]
  have h2 : ∀ (b : Zd d L), ∑ q : Fin (W ^ d), ‖PsiV d L W (a, p) (b, q)‖ = ‖PsiB d L a b‖ := by
    intro b
    simp only [PsiV, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
    simp [apply_ite norm, eq_comm]
  simp_rw [h2]
  have h3 : ∀ b : Zd d L, ‖PsiB d L a b‖ = if Adj d L a b then (1 : ℝ) else 0 := by
    intro b
    simp only [PsiB, Matrix.of_apply]
    by_cases h : Adj d L a b <;> simp [h]
  simp_rw [h3]
  rw [Finset.sum_boole]
  exact_mod_cast RBM.card_adj d L hL a

/-- `1 ≤ N` at every size index. -/
private theorem UNPins_one_le_Nsz {d : ℕ} (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  have h1 : 1 ≤ sz.size n := by
    simp only [Sizes.size]
    have := sz.three_le_L n
    have := sz.W_pos n
    exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by omega))
  exact_mod_cast h1

/-- The norm bound is monotone in the exponent: `UNNormBound sz M a → a ≤ b → UNNormBound sz M b`
(`1 ≤ N`, `Real.rpow_le_rpow_of_exponent_le`, `measure_mono`). -/
private theorem UNPins_normBound_mono {d : ℕ} {sz : Sizes d} {M : UNModel sz} {a b : ℝ}
    (h : UNNormBound sz M a) (hab : a ≤ b) : UNNormBound sz M b := by
  intro D hD
  filter_upwards [h D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨i, hi⟩
  exact ⟨i, lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le (UNPins_one_le_Nsz sz n) hab) hi⟩

/-- **`UNMeanBound` of the block Anderson mean** (new proof, ticket R3; supervisor 1955 B2: `‖λΨ‖ ≤ 2d 𝔡⁻¹ ≤ N^{CV₀}`
eventually for `CV₀ > 0`): the eigenvalues of `λ_n Ψ` on the fine lattice are `≤ 2d |λ_n|` in modulus (maximal row sum,
`UNPins_eig_le_rowsum`, `UNPins_psiI_rowsum`), `λ_n ≤ 𝔡⁻¹` eventually (`(eq:WO)`), and `2d 𝔡⁻¹ ≤ N^{CV₀}` eventually
(`N → ∞`).  Registry class: **structural** (a condition on the deterministic mean). -/
theorem unMeanBound_ba {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (CV₀ : ℝ) (hCV : 0 < CV₀) :
    UNMeanBound sz (UNModelC.ba sz) CV₀ := by
  obtain ⟨h𝔠, h𝔡, hT, hB, hW⟩ := hA
  have hlim : Tendsto (fun n => Nsz sz n ^ CV₀) atTop atTop := (tendsto_rpow_atTop hCV).comp hT
  filter_upwards [hW, hlim.eventually_ge_atTop (2 * (d : ℝ) * 𝔡⁻¹)] with n hn hN i
  obtain ⟨h1, h2⟩ := hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hl0 : 0 ≤ sz.lam n := le_trans (Real.rpow_nonneg hW0.le _) h1
  have hrow : ∀ x, ∑ y, ‖(UNModelC.ba sz).mean n x y‖ ≤ 2 * (d : ℝ) * 𝔡⁻¹ := by
    intro x
    have e : ∀ y, ‖(UNModelC.ba sz).mean n x y‖ = sz.lam n * ‖PsiI d (sz.L n) (sz.W n) x y‖ := by
      intro y
      change ‖((sz.lam n : ℝ) : ℂ) * PsiI d (sz.L n) (sz.W n) x y‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
    simp_rw [e]
    rw [← Finset.mul_sum, UNPins_psiI_rowsum d (sz.L n) (sz.W n) (sz.three_le_L n) x]
    calc sz.lam n * (2 * (d : ℝ)) ≤ 𝔡⁻¹ * (2 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * (d : ℝ) * 𝔡⁻¹ := by ring
  exact (UNPins_eig_le_rowsum ((UNModelC.ba sz).mean_herm n) hrow i).trans hN

end MeanBound

end RBM.Univ

/-! ## 4. The end pins and the assembly `baBUniv_of_rows` -/

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ

/-- **`(Meq:QUE)` and `(Meq:QUE2)` for the block Anderson matrix `sz.seqHBA` under the law `μ`** (`1_2:411-420`; T2161
`BAqueConcl`, `:1592-1605`, with the law as a parameter, T2173a): for energies in the ρ-bulk `{ρ_N ≥ κ}`, the failure
event of the first half is the merged `queBadMat` (per block `a`), of the second half the merged
`RBM.Endpoints.que2BadMat` (per nonempty block set `A`, T2001f), the bound the merged `queBound` (R4: no `BA…` copy of
the QUE vocabulary). -/
def BAqueConclL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (𝔡 κ ε₀ c τ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ E : ℝ, BAbulk d (sz.L n) (sz.lam n) κ E →
    (∀ a : Zd d (sz.L n),
      μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqHBA n ω)} ≤
        queBound (sz.W n) 𝔡 ε₀ c τ) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      μ {ω | RBM.Endpoints.que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqHBA n ω)} ≤
        queBound (sz.W n) 𝔡 ε₀ c τ)

/-- **Pin `MR:QUE` for block Anderson** (`MR:decol_BA` third bullet, `1_2:655`; T2161 `BAEnd_QUE`, `:1602-1605`, with the
law corrected: the law of `H = V + ilambda Ψ` is `seqP (sz.withLam 0)`, T2173a; `2 - κ ↦ e_λ - κ` read as
`ρ_N(E) ≥ κ`, DECISIONS §51).  Registry class: **owed** (BA-M3). -/
def BAEnd_QUEL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      BAqueConclL sz (Sizes.seqP (sz.withLam 0)) 𝔡 κ ε₀ c τ

/-- **Pin `Thm: B_Univ` for block Anderson** (`1_2:452-460`, `MR:decol_BA` third bullet `1_2:655`), in the dilated form
`UNUnivDilAt` of DECISIONS §11 at the density `ρ_N(E) = π⁻¹ Im m(E + i0)` of `(self_m)` (`BArho`), for the model
`UNModel.ba sz` (law `seqP (sz.withLam 0)`), `E` eventually in the ρ-bulk, `|E'| < 2`, `k ≥ 1`, `𝒪 ∈ C_c^∞(ℝ^k)`
(no `BAkPoint`, `BAeigs`, `BAgueP`, `BArhoSC`, `BAunivConclL`: not ported).  Concluded by `baBUniv_of_rows`, so not
registered as owed. -/
def BAEnd_BUnivL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ E' : ℝ, |E'| < 2 →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        UNUnivDilAt sz (UNModel.ba sz) (fun n => BArho d (sz.L n) (sz.lam n) E) E E' k O

end RBM.BA

namespace RBM.Univ

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-- **The consumed `(Meq:QUE)` of the block Anderson model is the first half of `BAEnd_QUEL`**: the ticket BA-M3 that
proves `BAEnd_QUEL` delivers `UNQueBA` (probe `UNQueBA_of_BAEnd_QUEL`, `:3256-3258`: `.mono`, first conjunct). -/
theorem UNQueBA_of_BAEnd_QUEL (h : ∀ d : ℕ, BAEnd_QUEL d) : UNQueBA := by
  intro d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6
  exact (h d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6).mono fun n hn E hE a => (hn E hE).1 a

/-- **The block Anderson `Thm: B_Univ` from the rows** (BA analogue of T2162 `un_bUniv_of_rows`; probe
`baBUniv_of_rows`, `:3283-3295`, through `UNCoreC''`, ticket R3): for every admissible `sz`, `κ > 0`, every `E`
eventually in the ρ-bulk, every `|E'| < 2`, `k ≥ 1` and `𝒪 ∈ C_c^∞(ℝ^k)`, the dilated universality of DECISIONS §11 from
`UNCoreC''`, the external `UNL32`, the internal `UNGUELocal`, `UNGreenCorrAllC`, the BA rows and the consumed inputs.
The norm bound `UNNormBound` at `CV₀` of the row `UNNormBARow` is used at `CV₀ + 1` together with the proved
`unMeanBound_ba`.  (The `d`-quantifier of `BAEnd_BUnivL` is the dimension of the theorem.) -/
theorem baBUniv_of_rows (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC)
    (rD : UNDensBARow') (rT0 : UNTrLocalBARow) (rT : UNTrLocalInitBARow') (rN : UNNormBARow)
    (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA)
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) (d : ℕ) : BAEnd_BUnivL d := by
  intro hd 𝔠 𝔡 sz hA k hk κ hκ E hE E' hE' O hO
  obtain ⟨δ₀, hδ₀, hδ⟩ := rD d hd 𝔠 𝔡 sz hA κ hκ E hE
  obtain ⟨hDens, hbulk⟩ := hδ δ₀ hδ₀ le_rfl
  have hCl := un_claimAll_of_rowsBA rC rE rJ rO hML hLoc hQ d hd 𝔠 𝔡 sz hA κ hκ E hE
  obtain ⟨CV₀, hCV, hN⟩ := rN d hd 𝔠 𝔡 sz hA
  exact hcore h32 hGL hGC d hd 𝔠 𝔡 sz hA (UNModelC.ba sz) (fun n => BAm d (sz.L n) (sz.lam n)) E
    (fun n => BArho d (sz.L n) (sz.lam n) E) δ₀ hDens
    (rT0 hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ₀ hδ₀ hbulk) (rT hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ₀ hδ₀ hbulk)
    ⟨CV₀ + 1, by linarith, UNPins_normBound_mono hN (by linarith), unMeanBound_ba sz hA _ (by linarith)⟩ hCl
    E' hE' k hk O hO

end RBM.Univ

namespace RBM.Univ

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 5. The centred flow

The centred block Anderson matrix at time `s_n` is the merged non-centred OU matrix of the model at the coupling
`λ̂_n = λ_n e^{s_n/2}` (`ouMatC_ba_eq_ouMat`), which is admissible at `(𝔠, 𝔡/2)` (`admissible_lamHat`); and the
centred flow minus the mean `λΨ` is the band OU matrix of `sz.withLam 0` (`ouMatC_ba_eq_band_add`).  Not ported
(ticket): the drift `drift_entry`, `drift_not_absorbable`, `un_shift_absorb` (UN-15; no consumer under
`UNTrLocalInit'`), and the bridges `ouMat_eq_ouMatNC_add`, `ouMat_band` (merged as `ouMatC_eq_ouMat_add`,
`ouMatC_toC`). -/

section Centred

variable {d : ℕ}

/-- The coupling `λ̂_n = λ_n e^{s_n/2}` (probe `lamHat`, `:2702`, verbatim). -/
def lamHat (sz : Sizes d) (s : ℕ → ℝ) : ℕ → ℝ := fun n => sz.lam n * Real.exp (s n / 2)

/-- **The centred block Anderson matrix at time `s_n` is the non-centred OU matrix of the block Anderson model at the
coupling `λ̂_n = λ_n e^{s_n/2}`**, pointwise on the carrier (the Gaussian part `V` of `sz.withLam 0` is the same, and
`e^{-s/2} (λ e^{s/2} Ψ) = λ Ψ`); probe `ouMat_ba_eq_ouMatNC`, `:2709-2735`, under S1, S2 and `ouMatNC ↦ ouMat`. -/
theorem ouMatC_ba_eq_ouMat (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC (UNModelC.ba sz) n (s n) ω = ouMat (UNModel.ba (sz.withLam (lamHat sz s))) n (s n) ω := by
  have hsc : ((Real.exp (-(s n) / 2) : ℝ) : ℂ) * ((lamHat sz s n : ℝ) : ℂ) = ((sz.lam n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    unfold lamHat
    rw [mul_comm (sz.lam n), ← mul_assoc, ← Real.exp_add]
    have : -(s n) / 2 + s n / 2 = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  have e1 : (Real.exp (-(s n) / 2)) • (((lamHat sz s n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) =
      ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
    rw [← Complex.coe_smul (Real.exp _), smul_smul, hsc]
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      V = Matrix.of fun (i j : Idx d (sz.L n) (sz.W n)) => (sz.withLam 0).seqXmat n ω.1 i j := ⟨_, rfl⟩
  have hH0 : (UNModelC.ba sz).H n ω.1 = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V := by
    rw [hV]; rfl
  have hH : (UNModel.ba (sz.withLam (lamHat sz s))).H n ω.1 =
      ((lamHat sz s n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V := by
    rw [hV]; rfl
  have hm : (UNModelC.ba sz).mean n = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := rfl
  unfold ouMatC ouMat
  rw [hm, hH0, hH, add_sub_cancel_left]
  change ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + Real.exp (-(s n) / 2) • V +
      Real.sqrt (1 - Real.exp (-(s n))) • Xmat d (sz.L n) (sz.W n) ω.2 =
    Real.exp (-(s n) / 2) • (((lamHat sz s n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V) +
      Real.sqrt (1 - Real.exp (-(s n))) • Xmat d (sz.L n) (sz.W n) ω.2
  rw [smul_add, e1]

/-- Both models have the same carrier law: `ouP` does not see the coupling of `sz` (`seqP (sz.withLam 0)`); probe
`ouP_ba_withLam`, `:2738-2739`, under S3. -/
theorem ouP_ba_withLam (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ) :
    ouP (UNModelC.ba sz).toUNModel n = ouP (UNModel.ba (sz.withLam g)) n := rfl

/-- **Translation identity of the centred flow**: `𝐇_t^{BA} - λΨ` is the band OU matrix `ouMat (UNModel.band ·) n t`
of `sz.withLam 0` (the block Anderson Gaussian part `V`, `S^{(B)}(0) = I`).  Every Gaussian-carrier fact of the OU flow
is therefore the band fact at `sz.withLam 0`, translated by the constant `λΨ`; probe `ouMat_ba_eq_band_add`,
`:2746-2765`, under S1, S2. -/
theorem ouMatC_ba_eq_band_add (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC (UNModelC.ba sz) n t ω - ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) =
      ouMat (UNModel.band (sz.withLam 0)) n t ω := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      V = Matrix.of fun (i j : Idx d (sz.L n) (sz.W n)) => (sz.withLam 0).seqXmat n ω.1 i j := ⟨_, rfl⟩
  have hH0 : (UNModelC.ba sz).H n ω.1 = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V := by
    rw [hV]; rfl
  have hm : (UNModelC.ba sz).mean n = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := rfl
  have hb : (UNModel.band (sz.withLam 0)).H n ω.1 = V := by rw [hV]; rfl
  unfold ouMatC ouMat
  rw [hm, hH0, hb]
  change ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) +
        Real.exp (-t / 2) • (((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V -
          ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) +
      Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2 -
      ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) =
    Real.exp (-t / 2) • V + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
  rw [add_sub_cancel_left, add_assoc, add_sub_cancel_left]

/-- The block Anderson OU carrier is the band OU carrier of `sz.withLam 0` (both are `seqP (sz.withLam 0) ⊗ GUE`);
probe `ouP_ba_eq_band`, `:2768-2769`, under S3. -/
theorem ouP_ba_eq_band (sz : Sizes d) (n : ℕ) :
    ouP (UNModelC.ba sz).toUNModel n = ouP (UNModel.band (sz.withLam 0)) n := rfl

/-- The DBM initial matrix of the block Anderson model is the rescaled block Anderson matrix at the coupling
`λ̂_n = λ_n e^{s_n/2}`: `A = e^{-s/2} (V + λ̂ Ψ)` (probe `ouInit_ba`, `:2778-2802`, under S1). -/
theorem ouInit_ba (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) (ω : Sizes.SeqΩ sz) :
    ouInit (UNModelC.ba sz) n (s n) ω =
      Real.exp (-(s n) / 2) • (UNModel.ba (sz.withLam (lamHat sz s))).H n ω := by
  have hsc : ((Real.exp (-(s n) / 2) : ℝ) : ℂ) * ((lamHat sz s n : ℝ) : ℂ) = ((sz.lam n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    unfold lamHat
    rw [mul_comm (sz.lam n), ← mul_assoc, ← Real.exp_add]
    have : -(s n) / 2 + s n / 2 = 0 := by ring
    rw [this, Real.exp_zero, one_mul]
  have e1 : (Real.exp (-(s n) / 2)) • (((lamHat sz s n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) =
      ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
    rw [← Complex.coe_smul (Real.exp _), smul_smul, hsc]
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      V = Matrix.of fun (i j : Idx d (sz.L n) (sz.W n)) => (sz.withLam 0).seqXmat n ω i j := ⟨_, rfl⟩
  have hH0 : (UNModelC.ba sz).H n ω = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V := by
    rw [hV]; rfl
  have hH : (UNModel.ba (sz.withLam (lamHat sz s))).H n ω =
      ((lamHat sz s n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V := by
    rw [hV]; rfl
  have hm : (UNModelC.ba sz).mean n = ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := rfl
  unfold ouInit
  rw [hm, hH0, hH, add_sub_cancel_left]
  change ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + Real.exp (-(s n) / 2) • V =
    Real.exp (-(s n) / 2) • (((lamHat sz s n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + V)
  rw [smul_add, e1]

/-- **The shifted coupling is admissible**: if `sz` is admissible at `(𝔠, 𝔡)` and `0 ≤ s_n ≤ 1`, then
`sz.withLam λ̂` is admissible at `(𝔠, 𝔡/2)`: `(eq:WO)` with `𝔡/2` holds since `λ̂ ≥ λ ≥ W^{-d/2+𝔡} ≥ W^{-d/2+𝔡/2}` and
`λ̂ ≤ e^{1/2} λ ≤ 2 𝔡⁻¹ = (𝔡/2)⁻¹` (`s_n = t*_n = N^{-1+τ_U} ≤ 1`); probe `admissible_lamHat`, `:2807-2829`,
verbatim. -/
theorem admissible_lamHat {sz : Sizes d} {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hs1 : ∀ n, s n ≤ 1) : (sz.withLam (lamHat sz s)).Admissible 𝔠 (𝔡 / 2) := by
  obtain ⟨h𝔠, h𝔡, hT, hB, hW⟩ := hA
  refine ⟨h𝔠, by linarith, hT, hB, ?_⟩
  filter_upwards [hW] with n hn
  obtain ⟨h1, h2⟩ := hn
  have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
  have hexp1 : 1 ≤ Real.exp (s n / 2) := Real.one_le_exp (by linarith [hs0 n])
  have hexp2 : Real.exp (s n / 2) ≤ 2 := by
    have hle : Real.exp (s n / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [hs1 n])
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (1 / 2)
    nlinarith
  have hlam0 : 0 ≤ sz.lam n := le_trans (by positivity) h1
  refine ⟨?_, ?_⟩
  · calc (sz.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡 / 2) ≤ (sz.W n : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ ≤ sz.lam n := h1
      _ ≤ sz.lam n * Real.exp (s n / 2) := le_mul_of_one_le_right hlam0 hexp1
  · calc sz.lam n * Real.exp (s n / 2) ≤ 𝔡⁻¹ * 2 := mul_le_mul h2 hexp2 (by positivity) (by positivity)
      _ = (𝔡 / 2)⁻¹ := by field_simp

/-! ## 6. The extreme input `λ = 0`: no mean, `S^{(B)}(0) = I`, the block Anderson model is the band model of
`sz.withLam 0` -/

/-- At `λ = 0` the block Anderson matrix is the band matrix of `sz.withLam 0` (probe `ba_zero_H`, `:2833-2836`,
under S1). -/
theorem ba_zero_H {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (n : ℕ) (ω : Sizes.SeqΩ sz) :
    (UNModelC.ba sz).H n ω = (UNModel.band (sz.withLam 0)).H n ω := by
  ext i j
  simp [UNModelC.ba, UNModel.ba, UNModel.band, Sizes.seqHBA, h n]

/-- At `λ = 0` the mean of the block Anderson model is the mean `0` of the band model of `sz.withLam 0` (probe
`ba_zero_mean`, `:2838-2841`, under S1, S6). -/
theorem ba_zero_mean {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (n : ℕ) :
    (UNModelC.ba sz).mean n = ((UNModel.band (sz.withLam 0)).toC).mean n := by
  simp [UNModelC.ba, UNModel.toC, h n]
  rfl

/-- At `λ = 0` the centred block Anderson OU matrix is the band OU matrix of `sz.withLam 0` (same law
`seqP (sz.withLam 0)`: `ouP` is the same, `rfl`); probe `ouMat_ba_zero`, `:2845-2849`, under S1, S2, S6. -/
theorem ouMatC_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMatC (UNModelC.ba sz) n t ω = ouMatC (UNModel.band (sz.withLam 0)).toC n t ω := by
  unfold ouMatC
  rw [ba_zero_H h, ba_zero_mean h]
  rfl

/-- At `λ = 0` the weighted `(EMCTE2)` of the block Anderson kind is that of the band kind of `sz.withLam 0` (probe
`UNEMCTE2k_ba_zero`, `:2851-2857`). -/
theorem UNEMCTE2k_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) :
    UNEMCTE2k (UNKind.ba d) sz E nf τU Cn ↔ UNEMCTE2k (UNKind.band d) (sz.withLam 0) E nf τU Cn := by
  have key : ∀ n t ω, ouMatC (UNModelC.ba sz) n t ω = ouMatC (UNModel.band (sz.withLam 0)).toC n t ω :=
    fun n t ω => ouMatC_ba_zero h n t ω
  unfold UNEMCTE2k
  simp only [UNKind.ba, UNKind.band, key]
  rfl

/-- At `λ = 0` `(jaklsdufowe)` of the block Anderson kind is that of the band kind of `sz.withLam 0` (probe
`UNJakk_ba_zero`, `:2859-2865`). -/
theorem UNJakk_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) :
    UNJakk (UNKind.ba d) sz E nf τU C c' ↔ UNJakk (UNKind.band d) (sz.withLam 0) E nf τU C c' := by
  have key : ∀ n t ω, ouMatC (UNModelC.ba sz) n t ω = ouMatC (UNModel.band (sz.withLam 0)).toC n t ω :=
    fun n t ω => ouMatC_ba_zero h n t ω
  unfold UNJakk
  simp only [UNKind.ba, UNKind.band, key]
  rfl

/-- At `λ = 0` `(uywy7723r3rf)` of the block Anderson kind is that of the band kind of `sz.withLam 0` (probe
`UNUywk_ba_zero`, `:2867-2873`). -/
theorem UNUywk_ba_zero {sz : Sizes d} (h : ∀ n, sz.lam n = 0) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) :
    UNUywk (UNKind.ba d) sz E nf τU C c' ↔ UNUywk (UNKind.band d) (sz.withLam 0) E nf τU C c' := by
  have key : ∀ n t ω, ouMatC (UNModelC.ba sz) n t ω = ouMatC (UNModel.band (sz.withLam 0)).toC n t ω :=
    fun n t ω => ouMatC_ba_zero h n t ω
  unfold UNUywk
  simp only [UNKind.ba, UNKind.band, key]
  rfl

end Centred

end RBM.Univ

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes

/-- At `λ = 0`, `(self_m)` is the semicircle equation: `msc z` is a solution (`BASelf d L 0 z (msc z)`), so the block
Anderson deterministic layer reduces to the band one (the bulk forms then agree: `ρ_N = ρ_sc`); probe `BASelf_msc`,
`:2879-2901`, moved to the namespace of `BASelf`. -/
theorem BASelf_msc (d L : ℕ) [NeZero L] {z : ℂ} (hz : 0 < z.im) : BASelf d L 0 z (msc z) := by
  refine ⟨msc_im_pos hz, ?_⟩
  have hne : z + msc z ≠ 0 := by
    intro h0
    have := msc_mul z
    rw [add_comm, h0, mul_zero] at this
    norm_num at this
  have hc : -(z + msc z) ≠ 0 := neg_ne_zero.mpr hne
  have hmsc : msc z = (-(z + msc z))⁻¹ := by
    have h := msc_mul z
    exact eq_inv_of_mul_eq_one_left (by linear_combination (-1 : ℂ) * h)
  have hM : BAMB d L 0 z (msc z) = (-(z + msc z))⁻¹ • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    unfold BAMB Mres
    have h0 : (((0 : ℝ) : ℂ) • PsiB d L) = 0 := by simp
    rw [h0, zero_sub, ← neg_smul, ← Matrix.nonsing_inv_eq_ringInverse]
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hL : ((L ^ d : ℕ) : ℂ) ≠ 0 := by
    have : (L ^ d : ℕ) ≠ 0 := pow_ne_zero _ (NeZero.ne L)
    exact_mod_cast this
  rw [hM, Matrix.trace_smul, Matrix.trace_one, BAcard_Zd, smul_eq_mul]
  rw [← hmsc.symm.symm]
  field_simp

end RBM.BA

/-! ## 7. The bad event `𝓑(y)` for the block Anderson model: one block

`UNBadY lamV 𝔡 E y M` uses the profile coupling `lamV` only in `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}`, `S = S^{(B)}(lamV)`;
the QUE window of the conclusion carries the other coupling `lamQ` (`ilambda`).  For the band model they coincide
(merged `unBadY_subset`); for block Anderson `lamV = 0`, `S^{(B)}(0) = I`: `M_{y,α}` is the QUE quantity of the single
block `[a(y)]` (`unBadYBA_subset`) and `ℙ(𝓑(y)) ≤ p` with no factor `2d + 1` (`unBadYBA_measure_le`; the merged
`unBadY_measure_le` has `(2d+1) p`).  The exponent `c' = 𝔠𝔡/30` is unchanged (the factor is absorbed by `W^{τ/2}` in both
cases).  Probe `:2958-3071`, verbatim. -/

namespace RBM.Univ

open RBM RBM.Gauss RBM.Gauss.Sizes

section BadY2

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **`𝓑(y) ⊆` the union of the block QUE bad events over the support of `S^{(B)}(lamV)`** with two couplings (T2162
`unBadY_subset`, `:1204-1284`, proof verbatim with `lam` split into `lamV` (weights) and `lamQ` (QUE window)). -/
theorem unBadY_subset' (hL : 3 ≤ L) {lamV lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (y : Idx d L W)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : UNBadY d L W lamV 𝔡 E y M) :
    ∃ b : Zd d L, SBR d L lamV b (split d L W y).1 ≠ 0 ∧
      queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E b M := by
  obtain ⟨μ, ψ, hb, α, hα, hθ⟩ := h
  have hW0 : (0 : ℝ) < (W : ℝ) := lt_of_lt_of_le one_pos hW
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
    have : 0 < (W * L) ^ d := pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
      (Nat.pos_of_ne_zero (NeZero.ne L))) _
    exact_mod_cast this
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  -- the unit vector `ψ α`
  have hnorm : ∑ x, ‖ψ α x‖ ^ 2 = 1 := by
    have h1 := hb.1 α α
    simp only [ite_true, dotProduct] at h1
    have h2 : ∑ x, ((‖ψ α x‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      change ((‖ψ α x‖ ^ 2 : ℝ) : ℂ) = star (ψ α x) * ψ α x
      rw [Complex.star_def, Complex.conj_mul']
      push_cast; ring
    exact_mod_cast h2
  set a := (split d L W y).1 with ha
  set N : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hNdef
  set S : Zd d L → ℝ := fun b => ∑ x ∈ Iblk d L W b, ‖ψ α x‖ ^ 2 with hS
  set u : Zd d L → ℝ := fun b => N / (W : ℝ) ^ d * S b - 1 with hu
  have hrow : ∑ b : Zd d L, SBR d L lamV b a = 1 := by
    simp_rw [SBR_comm _ a]
    exact sum_SBR_row hL a
  have hwnn : ∀ b, 0 ≤ SBR d L lamV b a := fun b => sbKernelR_nonneg d L lamV _
  have hM := unMy_eq hL lamV (ψ α) hnorm y
  have hθ' : (W : ℝ) ^ (-(𝔡 / 6)) ≤ |∑ b, SBR d L lamV b a * u b| := by rw [← hM]; exact hθ
  by_contra hcon
  push Not at hcon
  -- every block of positive weight has `|u b| < θ`
  have hlt : ∀ b, SBR d L lamV b a ≠ 0 → |u b| < (W : ℝ) ^ (-(𝔡 / 6)) := by
    intro b hb0
    by_contra hge
    push Not at hge
    refine hcon b hb0 ⟨μ, ψ, hb, α, α, ?_, ?_, ?_⟩
    · have := un_window_sub (d := d) hW hN h𝔡 hlam
      exact hα.trans this
    · have := un_window_sub (d := d) hW hN h𝔡 hlam
      exact hα.trans this
    · -- the block quantity
      have hSb : (∑ x ∈ Iblk d L W b, star (ψ α x) * ψ α x) = ((S b : ℝ) : ℂ) := by
        rw [hS]; push_cast
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.star_def, Complex.conj_mul']
      simp only [ite_true, mul_one]
      rw [hSb]
      have : ((S b : ℝ) : ℂ) - (W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ) =
          (((S b - (W : ℝ) ^ d / N) : ℝ) : ℂ) := by
        rw [hNdef]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
      have hrel : S b - (W : ℝ) ^ d / N = (W : ℝ) ^ d / N * u b := by
        rw [hu]; field_simp
      rw [hrel, abs_mul, abs_of_pos (by positivity : 0 < (W : ℝ) ^ d / N)]
      have hWc : (W : ℝ) ^ ((d : ℝ) - 𝔡 / 6) = (W : ℝ) ^ d * (W : ℝ) ^ (-(𝔡 / 6)) := by
        rw [sub_eq_add_neg, Real.rpow_add hW0, Real.rpow_natCast]
      rw [hWc]
      calc (W : ℝ) ^ d * (W : ℝ) ^ (-(𝔡 / 6)) / N
          = (W : ℝ) ^ d / N * (W : ℝ) ^ (-(𝔡 / 6)) := by ring
        _ ≤ (W : ℝ) ^ d / N * |u b| := by gcongr
  -- contradiction with `θ ≤ |∑ w u|`
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, SBR d L lamV b₀ a ≠ 0 := by
    by_contra h0; push Not at h0
    simp [h0] at hrow
  have hsum : ∑ b, SBR d L lamV b a * |u b| < ∑ b, SBR d L lamV b a * (W : ℝ) ^ (-(𝔡 / 6)) := by
    refine Finset.sum_lt_sum (fun b _ => ?_) ⟨b₀, Finset.mem_univ _, ?_⟩
    · by_cases hz : SBR d L lamV b a = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hlt b hz).le (hwnn b)
    · exact mul_lt_mul_of_pos_left (hlt b₀ hb₀) (lt_of_le_of_ne (hwnn b₀) (Ne.symm hb₀))
  have habs : |∑ b, SBR d L lamV b a * u b| ≤ ∑ b, SBR d L lamV b a * |u b| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [abs_mul, abs_of_nonneg (hwnn b)]
  rw [← Finset.sum_mul, hrow, one_mul] at hsum
  linarith

/-- At `lamV = 0`, `S^{(B)}(0) = I`: the weight `SBR 0 b a` is nonzero only at `b = a`. -/
theorem SBR_zero_ne {b a : Zd d L} (h : SBR d L 0 b a ≠ 0) : b = a := by
  by_contra hne
  apply h
  have h1 : b - a ≠ 0 := sub_ne_zero.mpr hne
  simp [SBR, sbKernelR, h1]

/-- **The block Anderson bad event is a single-block QUE bad event** (`lamV = 0`): `𝓑(y) ⊆ {QUE bad at the block of y}`. -/
theorem unBadYBA_subset (hL : 3 ≤ L) {lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (y : Idx d L W)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : UNBadY d L W 0 𝔡 E y M) :
    queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E (split d L W y).1 M := by
  obtain ⟨b, hb, hq⟩ := unBadY_subset' hL hW h𝔡 hlam y M h
  rwa [SBR_zero_ne hb] at hq

/-- **`ℙ(𝓑(y)) ≤ p`** for block Anderson: if `(Meq:QUE)` holds with bound `p` at every block for the random matrix `Mf`,
then `𝓑(y)` has probability `≤ p` (T2162 `unBadY_measure_le` has `(2d+1) p`). -/
theorem unBadYBA_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (hL : 3 ≤ L)
    {lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (y : Idx d L W)
    (Mf : Ω → Matrix (Idx d L W) (Idx d L W) ℂ) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, μ {ω | queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} ≤ p) :
    μ {ω | UNBadY d L W 0 𝔡 E y (Mf ω)} ≤ p :=
  (measure_mono fun ω hω => unBadYBA_subset hL hW h𝔡 hlam y (Mf ω) hω).trans (hp _)

end BadY2

end RBM.Univ

/-! ## 8. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

(a) `RBM.BA.UNPinsInst`: the class sequences (probe T2173 `:2114-2219` = T2161 `:2434-2545`, minus `Thm27At`,
`inst_cls_Thm27*`, `inst_cls_gaps/odd/interval`, which need T2161's glue pin `BAThm27`; the flow point is the merged
`MFixedPointInst.FlowPt`, the uniqueness pin `BAmUniqReal 3` is the proved `baMUniqReal_holds 3`).
(b) `RBM.Univ.BAInst`: the UN instances at the class sequence `(L, g) = (4, 3/10)` (constant `L = 4`, constant coupling
`g₀ = (fp 4 _).g0 ≤ 3/10`, `W_n = (2(n+1))^5`, admissible at `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_* > 0`, the energy
`E_* = (fp 4 _).E` in the ρ-bulk) and along `sz0` with the flow points `zSeq`.  Every deterministic hypothesis
(admissibility, `κ > 0`, bulk membership, `τ > 0`, the window, the flow setting) is discharged; the pins of other
gates (the rows, the consumed inputs, `UNCoreC''`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`) are hypotheses of the
instances.  Dropped from the probe: `inst_UNStep1GoodC` (refuted pin, R5), `inst_shift_absorb`,
`inst_drift_not_absorbable`, `inst_drift_ne_zero` (drift: UN-15), `inst_que_exponent_ba`, `inst_que_params_ba`,
`inst_cprime_ba`, `inst_claim_exponent_ba` (identical to the merged `UNInst` ones), `svarF_ne_zero_profile`,
`seqGvar_ne_withLam_zero` (merged in `FlowPinsInst`), `unMy_single_self_zero`. -/

namespace RBM.BA.UNPinsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA.MFixedPointInst

/-- A chosen flow point (probe `fp`, `:2114`, over the merged `MFixedPointInst.FlowPt`). -/
noncomputable def fp (L : ℕ) [NeZero L] {g : ℝ} (hg : 0 < g) : FlowPt L g := (exists_flowPt L hg).some

/-- The flow point has `κ_* = Im m₀ > 0` (probe `fp_kappa_pos`, `:2116`). -/
theorem fp_kappa_pos (L : ℕ) [NeZero L] {g : ℝ} (hg : 0 < g) : 0 < (fp L hg).m0.im := (fp L hg).real.1.1

/-- The class sequence: constant `L ≥ 3`, `W_n = (2(n+1))⁵`, constant coupling `g₀` (probe `clsSz`, `:2135`). -/
def clsSz (L : ℕ) (hL : 3 ≤ L) (g0 : ℝ) : Sizes 3 where
  L := fun _ => L
  W := fun n => (2 * (n + 1)) ^ 5
  lam := fun _ => g0
  three_le_L := fun _ => hL
  W_pos := fun n => by positivity

/-- `L ≤ W_n` for `n ≥ L` along the class sequence. -/
theorem clsSz_L_le_W (L : ℕ) (hL : 3 ≤ L) (g0 : ℝ) (n : ℕ) (hn : L ≤ n) :
    (clsSz L hL g0).L n ≤ (clsSz L hL g0).W n := by
  have h2 : 2 * (n + 1) ≤ (2 * (n + 1)) ^ 5 := Nat.le_self_pow (by norm_num) _
  change L ≤ (2 * (n + 1)) ^ 5
  omega

/-- `N_n → ∞` along the class sequence. -/
theorem clsSz_tendsto (L : ℕ) (hL : 3 ≤ L) (g0 : ℝ) : (clsSz L hL g0).SizeTendsto := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have h1 : 2 * (n + 1) ≤ (2 * (n + 1)) ^ 5 := Nat.le_self_pow (by norm_num) _
  have h2 : (2 * (n + 1)) ^ 5 ≤ (2 * (n + 1)) ^ 5 * L := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : (2 * (n + 1)) ^ 5 * L ≤ ((2 * (n + 1)) ^ 5 * L) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h4 : n ≤ (clsSz L hL g0).size n := by
    change n ≤ ((2 * (n + 1)) ^ 5 * L) ^ 3
    omega
  exact_mod_cast h4

/-- `(Main_DEL_COND)` along the class sequence at `𝔠 = 1/6`. -/
theorem clsSz_bandwidth (L : ℕ) (hL : 3 ≤ L) (g0 : ℝ) : (clsSz L hL g0).Bandwidth (1 / 6) := by
  rw [Sizes.Bandwidth, Filter.eventually_atTop]
  refine ⟨L, fun n hn => ?_⟩
  have hle := clsSz_L_le_W L hL g0 n hn
  have h : (clsSz L hL g0).size n ≤ ((clsSz L hL g0).W n) ^ 6 := by
    calc (clsSz L hL g0).size n = ((clsSz L hL g0).W n * (clsSz L hL g0).L n) ^ 3 := rfl
      _ = ((clsSz L hL g0).W n) ^ 3 * ((clsSz L hL g0).L n) ^ 3 := by rw [mul_pow]
      _ ≤ ((clsSz L hL g0).W n) ^ 3 * ((clsSz L hL g0).W n) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 3)
      _ = ((clsSz L hL g0).W n) ^ 6 := by ring
  have h' : (((clsSz L hL g0).size n : ℕ) : ℝ) ≤ (((clsSz L hL g0).W n : ℕ) : ℝ) ^ 6 := by exact_mod_cast h
  calc (((clsSz L hL g0).size n : ℕ) : ℝ) ^ (1 / 6 : ℝ)
      ≤ ((((clsSz L hL g0).W n : ℕ) : ℝ) ^ 6) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h' (by norm_num)
    _ = (((clsSz L hL g0).W n : ℕ) : ℝ) := by
        rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)

/-- `(eq:WO)` along the class sequence at `𝔡 = 1/10` for `0 < g₀ ≤ 10`. -/
theorem clsSz_WO (L : ℕ) (hL : 3 ≤ L) {g0 : ℝ} (h0 : 0 < g0) (h10 : g0 ≤ 10) :
    (clsSz L hL g0).WO (1 / 10) := by
  rw [Sizes.WO, Filter.eventually_atTop]
  refine ⟨⌈g0⁻¹⌉₊, fun n hn => ?_⟩
  have hx0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hnR : g0⁻¹ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hW : (((clsSz L hL g0).W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [clsSz]
  have hexp : (-((3 : ℕ) : ℝ) / 2 + 1 / 10 : ℝ) = -(7 / 5) := by norm_num
  have hpow : ((2 * ((n : ℝ) + 1)) ^ 5) ^ (-(7 / 5) : ℝ) = ((2 * ((n : ℝ) + 1)) ^ 7)⁻¹ := by
    rw [← Real.rpow_natCast (2 * ((n : ℝ) + 1)) 5, ← Real.rpow_mul hx0.le,
      show ((5 : ℕ) : ℝ) * (-(7 / 5)) = -((7 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_natCast]
  refine ⟨?_, ?_⟩
  · rw [hW, hexp, hpow]
    calc ((2 * ((n : ℝ) + 1)) ^ 7)⁻¹ ≤ (2 * ((n : ℝ) + 1))⁻¹ :=
          inv_anti₀ hx0 (le_self_pow₀ hx1 (by norm_num))
      _ ≤ (g0⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr h0) (by linarith)
      _ = g0 := inv_inv g0
  · change g0 ≤ (1 / 10 : ℝ)⁻¹
    norm_num
    exact h10

/-- The class sequence is admissible at `(𝔠, 𝔡) = (1/6, 1/10)` for every `0 < g₀ ≤ 10`. -/
theorem clsSz_admissible (L : ℕ) (hL : 3 ≤ L) {g0 : ℝ} (h0 : 0 < g0) (h10 : g0 ≤ 10) :
    (clsSz L hL g0).Admissible (1 / 6) (1 / 10) :=
  ⟨by norm_num, by norm_num, clsSz_tendsto L hL g0, clsSz_bandwidth L hL g0, clsSz_WO L hL h0 h10⟩

/-- The class sequence of `(L, g)`: constant coupling `g₀ = √t₀ g` of the flow point (probe `clsS`, `:2205`). -/
noncomputable abbrev clsS (L : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) : Sizes 3 :=
  clsSz L hL (fp L hg).g0

/-- The bulk threshold `κ_* = Im m₀ / π` of the class (probe `clsκ`, `:2209`). -/
noncomputable abbrev clsκ (L : ℕ) [NeZero L] {g : ℝ} (hg : 0 < g) : ℝ := (fp L hg).m0.im / Real.pi

/-- `κ_* > 0`. -/
theorem clsκ_pos (L : ℕ) [NeZero L] {g : ℝ} (hg : 0 < g) : 0 < clsκ L hg :=
  div_pos (fp_kappa_pos L hg) Real.pi_pos

/-- *Compiled non-vacuity of the ρ-form*: `E_*` is in the bulk `B_{κ_*}` of the class `(L, g₀)`; the uniqueness pin
`BAmUniqReal 3` of the probe is the proved `baMUniqReal_holds 3` (probe `cls_bulk`, `:2215-2221`, without `huniq`). -/
theorem cls_bulk (L : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) :
    BAbulk 3 L (fp L hg).g0 (clsκ L hg) (fp L hg).E := by
  rw [BAbulk_iff (clsκ_pos L hg)
    (fun m m' hm hm' => baMUniqReal_holds 3 L hL (fp L hg).g0 (fp L hg).g0_pos (fp L hg).E m m' hm hm')]
  refine ⟨(fp L hg).m0, (fp L hg).real.1, le_of_eq ?_⟩
  unfold clsκ
  field_simp

end RBM.BA.UNPinsInst

namespace RBM.Univ.BAInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.BA.UNPinsInst RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.Univ

/-- `0 < 3/10` (the coupling parameter `g` of the class `(L, g) = (4, 3/10)`). -/
private theorem UNPins_hg_3_10 : (0 : ℝ) < 3 / 10 := by norm_num

/-- `3/10 ≤ 10` (so that the class sequence is admissible: `g₀ ≤ g ≤ 10`). -/
private theorem UNPins_hg10 : (3 / 10 : ℝ) ≤ 10 := by norm_num

/-- The class sequence `(L, g) = (4, 3/10)` and its data (probe `S0`, `:3428`). -/
noncomputable abbrev S0 : Sizes 3 := clsS 4 (by norm_num) UNPins_hg_3_10

/-- The class sequence is admissible at `(𝔠, 𝔡) = (1/6, 1/10)`. -/
theorem S0_adm : S0.Admissible (1 / 6) (1 / 10) :=
  clsSz_admissible 4 (by norm_num) (fp 4 UNPins_hg_3_10).g0_pos ((fp 4 UNPins_hg_3_10).g0_le.trans UNPins_hg10)

/-- `E_*` is in the ρ-bulk `{ρ_N ≥ κ_*}` of the class sequence at every `n` (no uniqueness hypothesis). -/
theorem S0_bulk :
    ∀ᶠ n in atTop, BAbulk 3 (S0.L n) (S0.lam n) (clsκ 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E :=
  Eventually.of_forall fun _ => cls_bulk 4 (by norm_num) UNPins_hg_3_10

/-! ### The five Claim pins of the block Anderson kind, applied at the class sequence -/

/-- `UNOUQUEk` of the block Anderson kind at the class sequence, read at `κ_*`, `E_*`, `τ_Q = 1/300`. -/
theorem inst_UNOUQUEk {τU : ℝ} (h : UNOUQUEk (UNKind.ba 3) S0 (1 / 10) τU) :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar S0 τU n → ∀ a : Zd 3 (S0.L n),
      ouP (UNModelC.ba S0).toUNModel n
          {ω | queBadMat 3 (S0.L n) (S0.W n) (S0.lam n) ((1 / 10) / 3) ((1 / 10) / 6) (fp 4 UNPins_hg_3_10).E a
            (ouMatC (UNModelC.ba S0) n t ω)} ≤
        queBound (S0.W n) (1 / 10) ((1 / 10) / 3) ((1 / 10) / 6) (1 / 300) :=
  (h (clsκ 4 UNPins_hg_3_10) (1 / 300) (clsκ_pos 4 UNPins_hg_3_10) (by norm_num)).mono fun n hn t h0 h1 a =>
    hn t h0 h1 (fp 4 UNPins_hg_3_10).E (cls_bulk 4 (by norm_num) UNPins_hg_3_10) a

/-- `UNOUDiagk` of the block Anderson kind at the class sequence (`κ_*`, `ε = 1/10`, `D = 1`). -/
theorem inst_UNOUDiagk {τU : ℝ} (h : UNOUDiagk (UNKind.ba 3) S0 τU) :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar S0 τU n →
      ouP (UNModelC.ba S0).toUNModel n {ω | ∃ x : Idx 3 (S0.L n) (S0.W n),
          Nsz S0 n ^ (1 / 10 : ℝ) <
            ‖Gres (ouMatC (UNModelC.ba S0) n t ω)
                (((fp 4 UNPins_hg_3_10).E : ℂ) + ((Nsz S0 n ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) true x x‖} ≤
        ENNReal.ofReal (Nsz S0 n ^ (-(1 : ℝ))) :=
  (h (clsκ 4 UNPins_hg_3_10) (1 / 10) 1 (clsκ_pos 4 UNPins_hg_3_10) (by norm_num) (by norm_num)).mono
    fun n hn t h0 h1 => hn t h0 h1 (fp 4 UNPins_hg_3_10).E (cls_bulk 4 (by norm_num) UNPins_hg_3_10)

/-- The window point `z = E_* + i N⁻¹` (`n_f = 1`). -/
def zpt (n : ℕ) : Fin 1 → ℂ := fun _ => ⟨(fp 4 UNPins_hg_3_10).E, (Nsz S0 n)⁻¹⟩

/-- `(EMCTE2)` weights: `UNEMCTE2k` at `n_f = 1` and the window point `zpt n`: every hypothesis but the bounds `B` on
the expectations of the kernels (the owed content of the row) holds; `0 ≤ B` is satisfiable and the window is nonempty
(`UNKInst.inWindow_nonempty`). -/
theorem inst_UNEMCTE2k {τU Cn : ℝ} (hτ : 0 ≤ τU)
    (h : UNEMCTE2k (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10).E 1 τU Cn) :
    ∀ᶠ n in atTop, ∀ B : ℝ, 0 ≤ B →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar S0 τU n → ∀ u : Fin 1,
        ∫ ω, (∏ j ∈ Finset.univ.erase u, (stieltjesN (ouMatC (UNModelC.ba S0) n s ω) (zpt n j)).im) *
          L1t 3 (S0.L n) (S0.W n) 0 (ouMatC (UNModelC.ba S0) n s ω) (zpt n u)
          ∂(ouP (UNModelC.ba S0).toUNModel n) ≤ B) →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar S0 τU n → ∀ u v : Fin 1, u ≠ v →
        ∫ ω, (∏ k ∈ (Finset.univ.erase u).erase v, (stieltjesN (ouMatC (UNModelC.ba S0) n s ω) (zpt n k)).im) *
          L2t 3 (S0.L n) (S0.W n) 0 (ouMatC (UNModelC.ba S0) n s ω) (zpt n u) (zpt n v)
          ∂(ouP (UNModelC.ba S0).toUNModel n) ≤ B) →
      ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar S0 τU n →
        |(∫ ω, ∏ i, (stieltjesN (ouMatC (UNModelC.ba S0) n t ω) (zpt n i)).im ∂(ouP (UNModelC.ba S0).toUNModel n)) -
          ∫ ω, ∏ i, (stieltjesN (ouMatC (UNModelC.ba S0) n (ouTStar S0 τU n) ω) (zpt n i)).im
            ∂(ouP (UNModelC.ba S0).toUNModel n)| ≤
          Nsz S0 n ^ (1 : ℝ) * Nsz S0 n ^ (-1 + Cn * τU) * B := by
  filter_upwards [h 1 1 one_pos one_pos] with n hn B hB h1 h2 t h0 h3
  exact hn (zpt n) (fun _ => UNKInst.inWindow_nonempty S0 _ _ _ n zero_le_one hτ) B hB h1 h2 t h0 h3

/-- Two window points (`n_f = 2`). -/
def zpt2 (n : ℕ) : Fin 2 → ℂ := fun _ => ⟨(fp 4 UNPins_hg_3_10).E, (Nsz S0 n)⁻¹⟩

/-- `UNJakk` of the block Anderson kind at the class sequence, `n_f = 1`, the window point `zpt n`. -/
theorem inst_UNJakk {τU C c' : ℝ} (hτ : 0 ≤ τU)
    (h : UNJakk (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10).E 1 τU C c') :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar S0 τU n →
      ∀ (s : Finset (Fin 1)) (i : Fin 1) (y : Idx 3 (S0.L n) (S0.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ j ∈ s, (stieltjesN (ouMatC (UNModelC.ba S0) n t ω) (zpt n j)).im) *
          ‖∑ x, (Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt n i) b₁ *
              Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt n i) b₁) x x *
            scirc 3 (S0.L n) (S0.W n) 0 x y *
              Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt n i) b₂ y y‖
          ∂(ouP (UNModelC.ba S0).toUNModel n) ≤
          Nsz S0 n ^ (1 : ℝ) * Nsz S0 n ^ (1 - c' + C * τU) := by
  filter_upwards [h 1 1 one_pos one_pos] with n hn t h0 h1 s i y b₁ b₂
  exact hn (zpt n) (fun _ => UNKInst.inWindow_nonempty S0 _ _ _ n zero_le_one hτ) t h0 h1 s i y b₁ b₂

/-- `UNUywk` of the block Anderson kind at the class sequence, `n_f = 2`, the window points `zpt2 n`. -/
theorem inst_UNUywk {τU C c' : ℝ} (hτ : 0 ≤ τU)
    (h : UNUywk (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10).E 2 τU C c') :
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar S0 τU n →
      ∀ (s : Finset (Fin 2)) (i j : Fin 2), i ≠ j → ∀ (y : Idx 3 (S0.L n) (S0.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ k ∈ s, (stieltjesN (ouMatC (UNModelC.ba S0) n t ω) (zpt2 n k)).im) *
          ‖∑ x, (Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt2 n i) b₁ *
              Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt2 n i) b₁) x y *
            scirc 3 (S0.L n) (S0.W n) 0 x y *
              (Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt2 n j) b₂ *
                Gres (ouMatC (UNModelC.ba S0) n t ω) (zpt2 n j) b₂) y x‖
          ∂(ouP (UNModelC.ba S0).toUNModel n) ≤
          Nsz S0 n ^ (1 : ℝ) * Nsz S0 n ^ (2 - c' + C * τU) := by
  filter_upwards [h 1 1 one_pos one_pos] with n hn t h0 h1 s i j hij y b₁ b₂
  exact hn (zpt2 n) (fun _ => UNKInst.inWindow_nonempty S0 _ _ _ n zero_le_one hτ) t h0 h1 s i j hij y b₁ b₂

/-! ### The consumed inputs at the class sequence -/

/-- `UNQueBA` at the class sequence, `κ_*`, `E_*`, `(ε₀, c, τ) = (1/30, 1/60, 1/100)`. -/
theorem inst_UNQueBA (h : UNQueBA) :
    ∀ᶠ n in atTop, ∀ a : Zd 3 (S0.L n),
      (UNModelC.ba S0).μ {ω | queBadMat 3 (S0.L n) (S0.W n) (S0.lam n) (1 / 30) (1 / 60)
          (fp 4 UNPins_hg_3_10).E a ((UNModelC.ba S0).H n ω)} ≤
        queBound (S0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 100) :=
  (h 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10) (1 / 30) (1 / 60)
    (1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mono
    fun n hn a => hn (fp 4 UNPins_hg_3_10).E (cls_bulk 4 (by norm_num) UNPins_hg_3_10) a

/-- The domain of `(G_bound_ave)` is nonempty at every `n`: `z = E_* + i` is in the bulk, `N^{-1+ε} ≤ 1 ≤ 1`. -/
theorem inst_locAvg_domain {ε : ℝ} (hε : ε ≤ 1) (n : ℕ) :
    ∃ z : ℂ, (UNKind.ba 3).bulk S0 (clsκ 4 UNPins_hg_3_10) z.re n ∧
      ((S0.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 := by
  refine ⟨⟨(fp 4 UNPins_hg_3_10).E, 1⟩, cls_bulk 4 (by norm_num) UNPins_hg_3_10, ?_, le_rfl⟩
  have hN : (1 : ℝ) ≤ (((S0.size n : ℕ)) : ℝ) := by
    have h1 : 1 ≤ S0.size n :=
      Nat.one_le_pow _ _ (Nat.mul_pos (S0.W_pos n) (show 0 < S0.L n by have := S0.three_le_L n; omega))
    exact_mod_cast h1
  exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- `UNLocAvgBA` at the class sequence (`κ_*`, `ε = τ = 1/10`, `D = 1`). -/
theorem inst_UNLocAvgBA (h : UNLocAvgBA) :
    ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
        ((UNKind.ba 3).bulk S0 (clsκ 4 UNPins_hg_3_10) z.re n ∧
            ((S0.size n : ℕ) : ℝ) ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 1) ∧
          ∃ a : Zd 3 (S0.L n), ((S0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * S0.Bctl n (1 - z.im) <
            ‖(((S0.W n : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (S0.L n) (S0.W n) a,
                Gres ((UNModelC.ba S0).H n ω) z true x x - BAm 3 (S0.L n) (S0.lam n) z‖} ≤
      ENNReal.ofReal (Nsz S0 n ^ (-(1 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10) (1 / 10) (1 / 10) 1 (clsκ_pos 4 UNPins_hg_3_10)
    (by norm_num) (by norm_num) (by norm_num)

/-- `UNMLOutBA 3` along `sz0` at the flow points `zSeq` (`BAFlow` holds, `t₀ ≥ 2/3`), time `t = 0`: the five estimates
of `lem:main_ind_BA` over the carrier `baFMz sz0 zSeq` under the law `seqP (sz0.withLam 0)`; the hypothesis is the
owed pin `UNMLOutBA 3` only (`BAmExists 3` is discharged by `baMExists_holds`, inside `flow_sz0`). -/
theorem inst_UNMLOutBA (h : UNMLOutBA 3) :
    STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) ∧
      STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) ∧
      STDecaygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) ∧
      STExp2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) ∧
      STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) :=
  h (by norm_num) (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq flow_sz0
    (fun _ => 0) (fun _ => le_rfl) (fun n => le_trans (by norm_num) (t0_sz0 n))

/-! ### The rows at the class sequence -/

/-- `UNOURowBA` applied at the class sequence. -/
theorem inst_UNOURowBA (rO : UNOURowBA) (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNOUQUEk (UNKind.ba 3) S0 (1 / 10) τU ∧ UNOUDiagk (UNKind.ba 3) S0 τU :=
  rO hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm

/-- `UNEMCTE2RowBA` applied at the class sequence, `κ_*`, `E_*`, `n_f = 1`. -/
theorem inst_UNEMCTE2RowBA (rE : UNEMCTE2RowBA) :
    ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNEMCTE2k (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10).E 1 τU Cn :=
  rE 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10)
    (fp 4 UNPins_hg_3_10).E S0_bulk 1

/-- `UNJakUywRowBA` applied at the class sequence, `κ_*`, `E_*`, `n_f = 2`; the `𝐇_t` claims it reads are the output
`rO hML hLoc hQ` of the row `UNOURowBA` (so the only hypotheses are registered pins). -/
theorem inst_UNJakUywRowBA (rJ : UNJakUywRowBA) (rO : UNOURowBA) (hML : ∀ d : ℕ, UNMLOutBA d)
    (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNJakk (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10).E 2 τU C (1 / 6 * (1 / 10) / 30) ∧
        UNUywk (UNKind.ba 3) S0 (fp 4 UNPins_hg_3_10).E 2 τU C (1 / 6 * (1 / 10) / 30) :=
  rJ hLoc (rO hML hLoc hQ) 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10)
    (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk 2

/-- **Target `un_claimAll_of_rowsBA` at the class sequence: `UNClaimAllC sz (UNModelC.ba sz) E_*` from the BA rows**,
every deterministic hypothesis discharged (admissibility, `κ_* > 0`, `E_*` in the ρ-bulk); the rows and the consumed
inputs are the hypotheses.  The model is the block Anderson model `H = V + λ Ψ` with the centred OU flow. -/
theorem inst_claimAll_ba (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA)
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    UNClaimAllC S0 (UNModelC.ba S0) (fp 4 UNPins_hg_3_10).E :=
  un_claimAll_of_rowsBA rC rE rJ rO hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10)
    (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk

/-- **The block Anderson form of `Thm: B_Univ` (DECISIONS §11) at the class sequence from the BA rows**
(`baBUniv_of_rows` at `S0`, `k = 1`, `𝒪 = UNInst.bump`, `E' = 0`): `UNCoreC''` applied to `UNModelC.ba S0` with
`m n = m(·, λ_n)`, `ρ_n = ρ_N(E_*)`; `UNDens'`, `UNTrLocal`, `UNTrLocalInit'`, `UNNormBound` come from the BA rows
`UNDensBARow'`, `UNTrLocalBARow`, `UNTrLocalInitBARow'`, `UNNormBARow`, `UNMeanBound` from `unMeanBound_ba`, and
`UNClaimAllC` from `un_claimAll_of_rowsBA`.  Hypotheses: the pins of the other gates. -/
theorem inst_univ_ba (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC)
    (rD : UNDensBARow') (rT0 : UNTrLocalBARow) (rT : UNTrLocalInitBARow') (rN : UNNormBARow)
    (rC : UNClaimRowBA) (rE : UNEMCTE2RowBA) (rJ : UNJakUywRowBA) (rO : UNOURowBA)
    (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    UNUnivDilAt S0 (UNModel.ba S0) (fun n => BArho 3 (S0.L n) (S0.lam n) (fp 4 UNPins_hg_3_10).E)
      (fp 4 UNPins_hg_3_10).E 0 1 (UNInst.bump : (Fin 1 → ℝ) → ℝ) :=
  baBUniv_of_rows hcore h32 hGL hGC rD rT0 rT rN rC rE rJ rO hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1
    le_rfl (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk 0 (by norm_num)
    UNInst.bump UNInst.bump_testFun

/-! ### The centred flow at the class sequence -/

/-- The shifted coupling of the class sequence at `τ_s = 1/100` (`t*_n = N^{-1+τ_s} ≤ 1`) is admissible at
`(1/6, 1/20)` (`admissible_lamHat`; preflight (iv)). -/
theorem inst_admissible_lamHat :
    (S0.withLam (lamHat S0 (ouTStar S0 (1 / 100)))).Admissible (1 / 6) (1 / 20) := by
  have hN : ∀ n, (1 : ℝ) ≤ (((S0.size n : ℕ)) : ℝ) := fun n => by
    have h1 : 1 ≤ S0.size n :=
      Nat.one_le_pow _ _ (Nat.mul_pos (S0.W_pos n) (show 0 < S0.L n by have := S0.three_le_L n; omega))
    exact_mod_cast h1
  have h := admissible_lamHat S0_adm (ouTStar S0 (1 / 100))
    (fun n => Real.rpow_nonneg (by linarith [hN n]) _)
    (fun n => Real.rpow_le_one_of_one_le_of_nonpos (hN n) (by norm_num))
  have e : (1 / 20 : ℝ) = (1 / 10) / 2 := by norm_num
  rw [e]
  exact h

/-- **Target `ouMatC_ba_eq_ouMat` at the class sequence**, `s = ouTStar S0 (1/100)`: the centred block Anderson matrix at
`t*_n` is the non-centred OU matrix of the model at the coupling `λ̂_n`, and `λ̂_n ≠ λ_n` (`t*_n > 0`, `λ_n > 0`: the
shifted model is a different one). -/
theorem inst_ouMatC_ba_eq_ouMat (n : ℕ) (ω : Sizes.SeqΩ S0 × Ω 3 (S0.L n) (S0.W n)) :
    ouMatC (UNModelC.ba S0) n (ouTStar S0 (1 / 100) n) ω =
        ouMat (UNModel.ba (S0.withLam (lamHat S0 (ouTStar S0 (1 / 100))))) n (ouTStar S0 (1 / 100) n) ω ∧
      lamHat S0 (ouTStar S0 (1 / 100)) n ≠ S0.lam n := by
  refine ⟨ouMatC_ba_eq_ouMat S0 (ouTStar S0 (1 / 100)) n ω, ?_⟩
  have hN : (1 : ℝ) ≤ (((S0.size n : ℕ)) : ℝ) := by
    have h1 : 1 ≤ S0.size n :=
      Nat.one_le_pow _ _ (Nat.mul_pos (S0.W_pos n) (show 0 < S0.L n by have := S0.three_le_L n; omega))
    exact_mod_cast h1
  have hpos : 0 < ouTStar S0 (1 / 100) n := Real.rpow_pos_of_pos (by linarith) _
  have hlam : 0 < S0.lam n := (fp 4 UNPins_hg_3_10).g0_pos
  have hexp : 1 < Real.exp (ouTStar S0 (1 / 100) n / 2) := Real.one_lt_exp_iff.mpr (by linarith)
  intro h
  change S0.lam n * Real.exp (ouTStar S0 (1 / 100) n / 2) = S0.lam n at h
  nlinarith

/-! ### The mean bound and the step 1 at the class sequence -/

/-- **`unMeanBound_ba` at the class sequence**: `UNMeanBound S0 (UNModelC.ba S0) (1/2)`, no hypothesis (`n₀ = 0` in the
preflight: `2d 𝔡⁻¹ = 60 ≤ N_0^{1/2} = 1448`; the proof is the eventual statement). -/
theorem inst_unMeanBound_ba : UNMeanBound S0 (UNModelC.ba S0) (1 / 2) :=
  unMeanBound_ba S0 S0_adm (1 / 2) (by norm_num)

/-- **`step1GoodC''` at the class sequence, from the BA rows** (`τ_s = 1/100 ≤ 𝔠𝔡 = 1/60`, `D = 1`): the conclusion of
`UNStep1GoodC''` at `S0`, `UNModelC.ba S0`, `m = BAm`, `ρ = BArho`, `E = E_*`.  The norm bound of the row `UNNormBARow`
is used at `CV₀ + 1` together with the proved `unMeanBound_ba` (so the regularity exponent is `CV₀ + 1 + 1`).
Hypotheses: `rD`, `rT`, `rN`, `hLoc` only (R5: replaces the probe's `inst_UNStep1GoodC`). -/
theorem inst_step1GoodC''_ba (rD : UNDensBARow') (rT : UNTrLocalInitBARow') (rN : UNNormBARow)
    (hLoc : UNLocAvgBA) :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      (UNModelC.ba S0).μ {ω | ¬ (IsRegular32 (vOUC S0 (UNModelC.ba S0) n (1 / 100) (fp 4 UNPins_hg_3_10).E ω)
            (Nsz S0 n ^ (-1 + (1 / 100 : ℝ) / 4))
            (Nsz S0 n ^ (-(min ((1 / 100 : ℝ) / 4) ((1 - 1 / 100) / 3)))) c C
            ((rN 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm).choose + 1 + 1) ∧
          ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC S0 (UNModelC.ba S0) n (1 / 100) (fp 4 UNPins_hg_3_10).E ω)
              (1 - Real.exp (-(ouTStar S0 (1 / 100) n))) mfc ∧
            ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
              |ρ' - BArho 3 (S0.L n) (S0.lam n) (fp 4 UNPins_hg_3_10).E| ≤
                Nsz S0 n ^ (-(3 * (1 / 100 : ℝ) / 8)))} ≤
        ENNReal.ofReal (Nsz S0 n ^ (-(1 : ℝ))) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := rD 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10)
    (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk
  obtain ⟨hDens, hbulk⟩ := hδ δ₀ hδ₀ le_rfl
  have hN := rN 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm
  have hpos : 0 < hN.choose + 1 := by linarith [hN.choose_spec.1]
  exact step1GoodC'' 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (UNModelC.ba S0)
    (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 UNPins_hg_3_10).E
    (fun n => BArho 3 (S0.L n) (S0.lam n) (fp 4 UNPins_hg_3_10).E) δ₀ hDens
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10)
      (fp 4 UNPins_hg_3_10).E S0_bulk δ₀ hδ₀ hbulk)
    (hN.choose + 1) hpos.le (UNPins_normBound_mono hN.choose_spec.2 (by linarith))
    (unMeanBound_ba S0 S0_adm _ hpos) (1 / 100) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### The bad event at `d = 3`: one block -/

/-- **A nondegenerate bad event for block Anderson** (`lamV = 0`): the zero matrix on `Idx 3 4 32` with the standard
basis: `|M_{y,y}| = L^d - 1 = 63 ≥ 1 ≥ W^{-𝔡/6}` (probe `badYBA_zero`, `:3705-3712`, with the merged
`UNInst.unMy_single_self` at `lam = 0`). -/
theorem badYBA_zero : UNBadY 3 4 32 0 (1 / 10) 0 (0 : Idx 3 4 32) 0 := by
  refine ⟨fun _ => 0, fun k => Pi.single k 1, UNInst.isOrthoEigenbasis_zero, 0, ?_, ?_⟩
  · simp only [sub_self, abs_zero]; positivity
  · rw [UNInst.unMy_single_self]
    have h1 : ((32 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    refine h1.trans ?_
    norm_num

/-- **`unBadYBA_subset` at the instance**: the QUE bad event at the single block of `y` (`lamQ = 1/64`, `(eq:WO)`
holds; probe `inst_badYBA_subset`, `:3715-3719`). -/
theorem inst_badYBA_subset :
    queBadMat 3 4 32 (1 / 64) (1 / 10 / 3) (1 / 10 / 6) 0 ((split 3 4 32 (0 : Idx 3 4 32)).1)
      (0 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ) :=
  unBadYBA_subset (d := 3) (L := 4) (W := 32) (by norm_num) (by norm_num) (by norm_num)
    (by rw [Nat.cast_ofNat, UNInst.pow32]; norm_num) _ _ badYBA_zero

/-- **`ℙ(𝓑(y)) ≤ p` at the instance** (law `δ_*`, `p = 1`): no factor `2d + 1` (probe `inst_badYBA_measure`,
`:3722-3725`). -/
theorem inst_badYBA_measure : (Measure.dirac ()) {_ω : Unit | UNBadY 3 4 32 0 (1 / 10) 0 (0 : Idx 3 4 32)
      (0 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ)} ≤ 1 :=
  unBadYBA_measure_le (d := 3) (L := 4) (W := 32) (lamQ := 1 / 64) (Measure.dirac ()) (by norm_num) (by norm_num)
    (by norm_num) (by rw [Nat.cast_ofNat, UNInst.pow32]; norm_num) _ (fun _ => 0) 1 (fun b => prob_le_one)

/-- `Ψ` has an entry `1` between the block `0` and a neighbouring block `e₁` at `(L, d) = (4, 3)` (probe
`PsiI_entry_one`, `:3735-3738`). -/
theorem PsiI_entry_one (W : ℕ) [NeZero W] : ∃ i j : Idx 3 4 W, PsiI 3 4 W i j = 1 := by
  refine ⟨(splitEquiv 3 4 W).symm (0, 0), (splitEquiv 3 4 W).symm (![1, 0, 0], 0), ?_⟩
  have h : Adj 3 4 0 ![1, 0, 0] := by unfold Adj; decide
  simp [PsiI, PsiV, PsiB, h, Matrix.kroneckerMap_apply]

/-- The mean `λ Ψ` of the block Anderson model has a nonzero entry at the class sequence (`λ = g₀ > 0`, two
neighbouring blocks; probe `inst_ba_mean_ne_zero`, `:3742-3748`). -/
theorem inst_ba_mean_ne_zero (n : ℕ) :
    ∃ i j : Idx 3 (S0.L n) (S0.W n), (UNModelC.ba S0).mean n i j ≠ 0 := by
  obtain ⟨i, j, hij⟩ := PsiI_entry_one (S0.W n)
  refine ⟨i, j, ?_⟩
  have h4 : ((UNModelC.ba S0).mean n i j) = ((S0.lam n : ℝ) : ℂ) * PsiI 3 4 (S0.W n) i j := rfl
  rw [h4, hij, mul_one]
  exact Complex.ofReal_ne_zero.mpr (fp 4 UNPins_hg_3_10).g0_pos.ne'

/-- The `(eq:WO)` window of `𝓑(y)` for block Anderson at `d = 3`, `W = 32`, `N = 2097152` (`lamQ = ilambda` enters the
window, not the weights): `W^{-d/2+𝔡} ≤ lamQ`; probe `inst_window_sub_ba`, `:3788-3791`. -/
theorem inst_window_sub_ba (lam : ℝ) (h1 : (32 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10) ≤ lam) :
    (2097152 : ℝ)⁻¹ * (32 : ℝ) ^ ((1 / 10 : ℝ) / 3) ≤
      (32 : ℝ) ^ (-((1 / 10 : ℝ) / 3)) * (lam * (32 : ℝ) ^ (((3 : ℕ) : ℝ) / 2) / 2097152) :=
  un_window_sub (d := 3) (by norm_num) (by norm_num) (by norm_num) h1

/-- **The OU claim at `t = 0` is the consumed QUE** (class sequence, `κ_*`, `E_*`, `τ_Q = 1/300`): `UNOUQUEk` at `t = 0`
from `UNQueBA` (`UNOUQUEk_zero_of_UNQuek`). -/
theorem inst_UNOUQUEk_zero (hQ : UNQueBA) :
    ∀ᶠ n in atTop, ∀ a : Zd 3 (S0.L n),
      ouP (UNModelC.ba S0).toUNModel n
          {ω | queBadMat 3 (S0.L n) (S0.W n) (S0.lam n) ((1 / 10) / 3) ((1 / 10) / 6)
            (fp 4 UNPins_hg_3_10).E a (ouMatC (UNModelC.ba S0) n 0 ω)} ≤
        queBound (S0.W n) (1 / 10) ((1 / 10) / 3) ((1 / 10) / 6) (1 / 300) :=
  (UNOUQUEk_zero_of_UNQuek (fun d => UNKind.ba d) hQ (le_refl 3) S0_adm (clsκ 4 UNPins_hg_3_10) (1 / 300)
    (clsκ_pos 4 UNPins_hg_3_10) (by norm_num)).mono fun n hn a =>
    hn (fp 4 UNPins_hg_3_10).E (cls_bulk 4 (by norm_num) UNPins_hg_3_10) a

/-! ### The remaining targets at concrete data -/

/-- `UNModelC.ba_spec`, `UNKind.ba_M` at the class sequence: the model is `UNModel.ba S0`, the mean is `λ_n Ψ`, and it is
nonzero (`inst_ba_mean_ne_zero`: the instance is not the band model). -/
theorem inst_UNModelC_ba_spec (n : ℕ) :
    (UNModelC.ba S0).toUNModel = UNModel.ba S0 ∧
      (UNModelC.ba S0).mean n = (S0.lam n : ℂ) • PsiI 3 (S0.L n) (S0.W n) ∧
      (UNKind.ba 3).M S0 = UNModelC.ba S0 ∧
      ∃ i j : Idx 3 (S0.L n) (S0.W n), (UNModelC.ba S0).mean n i j ≠ 0 :=
  ⟨(UNModelC.ba_spec S0).1, (UNModelC.ba_spec S0).2 n, UNKind.ba_M S0, inst_ba_mean_ne_zero n⟩

/-- **`BAEnd_QUEL` at the class sequence, both halves at `E_*`**: for `(ε₀, c, τ) = (1/30, 1/60, 1/100)` at `𝔡 = 1/10`
(`0 < ε₀ < 𝔡/2`, `0 < c < ε₀`, `c < 𝔡/5`), eventually, `(Meq:QUE)` at every block `a` and `(Meq:QUE2)` at every
nonempty block set `A`, under the law `seqP (S0.withLam 0)`; the hypothesis is the owed pin `BAEnd_QUEL 3` only. -/
theorem inst_BAEnd_QUEL (h : BAEnd_QUEL 3) :
    ∀ᶠ n in atTop, (∀ a : Zd 3 (S0.L n),
        Sizes.seqP (S0.withLam 0) {ω | queBadMat 3 (S0.L n) (S0.W n) (S0.lam n) (1 / 30) (1 / 60)
            (fp 4 UNPins_hg_3_10).E a (S0.seqHBA n ω)} ≤ queBound (S0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 100)) ∧
      (∀ A : Finset (Zd 3 (S0.L n)), A.Nonempty →
        Sizes.seqP (S0.withLam 0) {ω | RBM.Endpoints.que2BadMat 3 (S0.L n) (S0.W n) (S0.lam n) (1 / 30) (1 / 60)
            (fp 4 UNPins_hg_3_10).E A (S0.seqHBA n ω)} ≤ queBound (S0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 100)) :=
  ((h le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10) (1 / 30) (1 / 60)
    (1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).and
    S0_bulk).mono fun n hn => hn.1 _ hn.2

/-- **`UNQueBA_of_BAEnd_QUEL` at the class sequence**: the QUE input of the OU rows at `E_*` from the end pin
`BAEnd_QUEL` (the hypothesis, owed by BA-M3). -/
theorem inst_UNQueBA_of_BAEnd_QUEL (h : ∀ d : ℕ, BAEnd_QUEL d) :
    ∀ᶠ n in atTop, ∀ a : Zd 3 (S0.L n),
      (UNModelC.ba S0).μ {ω | queBadMat 3 (S0.L n) (S0.W n) (S0.lam n) (1 / 30) (1 / 60)
          (fp 4 UNPins_hg_3_10).E a ((UNModelC.ba S0).H n ω)} ≤
        queBound (S0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 100) :=
  inst_UNQueBA (UNQueBA_of_BAEnd_QUEL h)

/-- **The carrier facts at the class sequence**: `ouP` of the block Anderson model is that of the model at any coupling
and the band carrier of `S0.withLam 0` (`ouP_ba_withLam`, `ouP_ba_eq_band`). -/
theorem inst_ouP_ba (n : ℕ) (g : ℕ → ℝ) :
    ouP (UNModelC.ba S0).toUNModel n = ouP (UNModel.ba (S0.withLam g)) n ∧
      ouP (UNModelC.ba S0).toUNModel n = ouP (UNModel.band (S0.withLam 0)) n :=
  ⟨ouP_ba_withLam S0 g n, ouP_ba_eq_band S0 n⟩

/-- **The translation identity at the class sequence** (`ouMatC_ba_eq_band_add`): the centred block Anderson flow minus
the mean `λ_n Ψ` is the band flow of `S0.withLam 0`, and the mean is nonzero. -/
theorem inst_ouMatC_ba_eq_band_add (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ S0 × Ω 3 (S0.L n) (S0.W n)) :
    ouMatC (UNModelC.ba S0) n t ω - ((S0.lam n : ℝ) : ℂ) • PsiI 3 (S0.L n) (S0.W n) =
        ouMat (UNModel.band (S0.withLam 0)) n t ω ∧
      ∃ i j : Idx 3 (S0.L n) (S0.W n), ((S0.lam n : ℝ) : ℂ) • PsiI 3 (S0.L n) (S0.W n) i j ≠ 0 :=
  ⟨ouMatC_ba_eq_band_add S0 n t ω, inst_ba_mean_ne_zero n⟩

/-- **The initial matrix at the class sequence** (`ouInit_ba`, `s = ouTStar S0 (1/100)`): `ouInit` is the rescaled block
Anderson matrix at the coupling `λ̂_n`. -/
theorem inst_ouInit_ba (n : ℕ) (ω : Sizes.SeqΩ S0) :
    ouInit (UNModelC.ba S0) n (ouTStar S0 (1 / 100) n) ω =
      Real.exp (-(ouTStar S0 (1 / 100) n) / 2) •
        (UNModel.ba (S0.withLam (lamHat S0 (ouTStar S0 (1 / 100))))).H n ω :=
  ouInit_ba S0 (ouTStar S0 (1 / 100)) n ω

/-- **The `λ = 0` extremes at the sizes `S0.withLam 0`** (`λ_n = 0`): the block Anderson matrix, mean and centred OU
matrix are those of the band model of the same sizes (`ba_zero_H`, `ba_zero_mean`, `ouMatC_ba_zero`). -/
theorem inst_ba_zero (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ (S0.withLam 0) × Ω 3 ((S0.withLam 0).L n) ((S0.withLam 0).W n)) :
    (UNModelC.ba (S0.withLam 0)).H n ω.1 = (UNModel.band ((S0.withLam 0).withLam 0)).H n ω.1 ∧
      (UNModelC.ba (S0.withLam 0)).mean n = ((UNModel.band ((S0.withLam 0).withLam 0)).toC).mean n ∧
      ouMatC (UNModelC.ba (S0.withLam 0)) n t ω =
        ouMatC (UNModel.band ((S0.withLam 0).withLam 0)).toC n t ω :=
  ⟨ba_zero_H (sz := S0.withLam 0) (fun _ => rfl) n ω.1, ba_zero_mean (sz := S0.withLam 0) (fun _ => rfl) n,
    ouMatC_ba_zero (sz := S0.withLam 0) (fun _ => rfl) n t ω⟩

/-- **The `λ = 0` pins at the sizes `S0.withLam 0`**: `(EMCTE2)`, `(jaklsdufowe)`, `(uywy7723r3rf)` of the block Anderson
kind are those of the band kind (`UNEMCTE2k_ba_zero`, `UNJakk_ba_zero`, `UNUywk_ba_zero`) at `E = E_*`, `n_f = 1`,
`τ_U = 1/100`. -/
theorem inst_ba_zero_pins :
    (UNEMCTE2k (UNKind.ba 3) (S0.withLam 0) (fp 4 UNPins_hg_3_10).E 1 (1 / 100) 1 ↔
        UNEMCTE2k (UNKind.band 3) ((S0.withLam 0).withLam 0) (fp 4 UNPins_hg_3_10).E 1 (1 / 100) 1) ∧
      (UNJakk (UNKind.ba 3) (S0.withLam 0) (fp 4 UNPins_hg_3_10).E 1 (1 / 100) 1 (1 / 1800) ↔
        UNJakk (UNKind.band 3) ((S0.withLam 0).withLam 0) (fp 4 UNPins_hg_3_10).E 1 (1 / 100) 1 (1 / 1800)) ∧
      (UNUywk (UNKind.ba 3) (S0.withLam 0) (fp 4 UNPins_hg_3_10).E 1 (1 / 100) 1 (1 / 1800) ↔
        UNUywk (UNKind.band 3) ((S0.withLam 0).withLam 0) (fp 4 UNPins_hg_3_10).E 1 (1 / 100) 1 (1 / 1800)) :=
  ⟨UNEMCTE2k_ba_zero (sz := S0.withLam 0) (fun _ => rfl) _ _ _ _,
    UNJakk_ba_zero (sz := S0.withLam 0) (fun _ => rfl) _ _ _ _ _,
    UNUywk_ba_zero (sz := S0.withLam 0) (fun _ => rfl) _ _ _ _ _⟩

/-- **`BASelf_msc` at `(d, L) = (3, 4)`, `z = i`**: `msc i` solves `(self_m)` at `λ = 0`. -/
theorem inst_BASelf_msc : BASelf 3 4 0 Complex.I (msc Complex.I) :=
  BASelf_msc 3 4 (by simp)

/-- **`unBadY_subset'` at the instance** (two couplings: weights `lamV = 1/64`, window `lamQ = 1/64`; the merged
`UNInst.badY_zero`): some block `b` of positive weight has the QUE bad event. -/
theorem inst_unBadY_subset' :
    ∃ b : Zd 3 4, SBR 3 4 (1 / 64) b (split 3 4 32 (0 : Idx 3 4 32)).1 ≠ 0 ∧
      queBadMat 3 4 32 (1 / 64) (1 / 10 / 3) (1 / 10 / 6) 0 b (0 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ) :=
  unBadY_subset' (d := 3) (L := 4) (W := 32) (lamV := 1 / 64) (lamQ := 1 / 64) (by norm_num) (by norm_num)
    (by norm_num) (by rw [Nat.cast_ofNat, UNInst.pow32]; norm_num) _ _ UNInst.badY_zero

/-- **`SBR_zero_ne` at `(d, L) = (3, 4)`**: at `lamV = 0` the weight `S^{(B)}(0) = I` is nonzero on the diagonal and
only there. -/
theorem inst_SBR_zero_ne :
    SBR 3 4 0 (0 : Zd 3 4) 0 ≠ 0 ∧ ∀ b : Zd 3 4, SBR 3 4 0 b 0 ≠ 0 → b = 0 := by
  refine ⟨?_, fun b hb => SBR_zero_ne hb⟩
  simp [SBR, sbKernelR]

end RBM.Univ.BAInst
