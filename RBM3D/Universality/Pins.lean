/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Sizes
import RBM3D.Defs.StochDomAt
import RBM3D.Gauss.BlockAnderson
import RBM3D.Induction.Defs
import RBM3D.Propagator.Gap
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Statements for bulk universality (Theorem 2.4 `Thm: B_Univ`) at `d ≥ 3`

Paper: arXiv:2507.20274, Theorem 2.4 `Thm: B_Univ` with its conclusion (2.20) `eq:universality`, its proof
(which adapts the proof of [DYYY25, Theorem 2.6], itself adapted from [YY_25, Theorem 2.6]), and the
quantum unique ergodicity estimate (2.18) `Meq:QUE` that enters it.  The statements below are the two-dimensional
ones of [DYYY25] read at `d ≥ 3`, with `N = (W L)^d`.

Namespace `RBM.Univ`.  The names of the model-level statements carry the prefix `UN`.  Each of them is a `Prop`
that is either a result of the paper in the form in which the comparison argument uses it, or a step of the proof
of Theorem 2.4; theorems that need such a statement take it as a hypothesis.  The one external input is
`UNL32`, Theorem 2.2 of Landon–Sosoe–Yau (arXiv:1609.09011v4).

Contents: the vocabulary and the abstract model; the endpoint `UNBUniv` and its dilated form; the external input
`UNL32` and the limit computation of its arithmetic hypotheses; the statements taken from the local law, the
density and quantum unique ergodicity; the local law and density of the model; the claim on the Ornstein–Uhlenbeck
(OU) path and the Green-function comparison; the band-model chain (the claims on `𝐇_t`, (2.21), (2.22), (2.23) of
[DYYY25]); the composition `un_claimAll_of_rows`; the exponent computations; the bad event `𝓑(y)` and its
probability.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ## Vocabulary -/

section Vocab

/-- `(μ, ψ)` is an orthonormal eigenbasis of `H`: the vectors `ψ k` are orthonormal and `H ψ k = μ k ψ k`. -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k

/-- GUE coordinate variances at dimension `N = (W L)^d`: `1/N` on the diagonal and `1/(2N)` for each
real coordinate off the diagonal, so `E|h_ij|² = 1/N`. -/
def gueVar (d L W : ℕ) (c : CoordF d L W) : ℝ≥0 :=
  if c.1 = c.2.1 then ((((W * L) ^ d : ℕ) : ℝ≥0))⁻¹ else ((2 * ((W * L) ^ d : ℕ) : ℝ≥0))⁻¹

/-- The GUE law on the coordinate space `Ω d L W`: `Xmat d L W` under it is an `N × N` GUE matrix with
`E|h_ij|² = 1/N`, `N = (W L)^d` (the law of `𝐇_∞` in the proof of Theorem 2.4, as in [DYYY25, Theorem 2.6]). -/
def gueP (d L W : ℕ) [NeZero L] [NeZero W] : Measure (Ω d L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueVar d L W c)

instance isProbabilityMeasure_gueP (d L W : ℕ) [NeZero L] [NeZero W] :
    IsProbabilityMeasure (gueP d L W) := by
  unfold gueP; infer_instance

/-- The symmetric `k`-point functional `N^k (N-k)!/N! Σ_{i₁,…,i_k distinct} 𝒪(N(λ_{i₁}-E), …)`: its
expectation is `∫ 𝒪(α) p^{(k)}(E + α/N) dα`, where `p^{(k)}` is the `k`-point function defined before
Theorem 2.4, normalized to integrate to `1`. -/
def kPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
    ∑ f : Fin k ↪ ι, O (fun j => (Fintype.card ι : ℝ) * (lam (f j) - E))

/-- `ρ_sc(E) = (2π)⁻¹ √(4 - E²)`, the semicircle density; it equals `π⁻¹ Im mE E` (`RBM.mE`). -/
def rhoSC (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / (2 * Real.pi)

/-- `m(z) = N⁻¹ tr (M - z)⁻¹` for a matrix `M` on a finite index set (`Gres` is the resolvent). -/
def stieltjesN {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * (Gres M z true).trace

/-- A test function: `𝒪 ∈ C_c^∞(ℝ^k)` (smoothness index `∞`, not `ω`). -/
def IsTestFun {k : ℕ} (O : (Fin k → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O

end Vocab

/-! ### The abstract model: a measure on the common sample space and a matrix family

The band model and the block Anderson model (`RBM3D/Gauss/BlockAnderson.lean`) are both a measurable
family of Hermitian matrices on `Sizes.SeqΩ sz`.  The statements below are formulated for such a model, so that
both models can use them, with the data `m`, `ρ_N` of (2.32) `self_m` in the block Anderson case. -/

/-- A random-matrix model along a size sequence. -/
structure UNModel {d : ℕ} (sz : Sizes d) where
  /-- the law -/
  μ : Measure (Sizes.SeqΩ sz)
  prob : IsProbabilityMeasure μ
  /-- the matrix at size `n` -/
  H : ∀ n : ℕ, Sizes.SeqΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
  herm : ∀ n ω, (H n ω).IsHermitian
  meas : ∀ n (i j : Idx d (sz.L n) (sz.W n)), Measurable fun ω => H n ω i j

attribute [instance] UNModel.prob

/-- The band model (2.4) `bandcw0`: law `seqP sz`, matrix `seqXmat sz n`. -/
def UNModel.band {d : ℕ} (sz : Sizes d) : UNModel sz where
  μ := Sizes.seqP sz
  prob := inferInstance
  H := Sizes.seqXmat sz
  herm := Sizes.seqXmat_isHermitian sz
  meas := fun n i j => (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (measurable_slice sz n)

/-- The block Anderson model (2.30) `eq:H_blocka`: `H = V + ilambda Ψ` with `V` the model of
`sz.withLam 0` (`Sizes.seqHBA`). -/
def UNModel.ba {d : ℕ} (sz : Sizes d) : UNModel sz where
  μ := Sizes.seqP (sz.withLam 0)
  prob := Sizes.isProbabilityMeasure_seqP (sz.withLam 0)
  H := Sizes.seqHBA sz
  herm := Sizes.seqHBA_isHermitian sz
  meas := fun n i j => by
    have h : Measurable fun ω : Sizes.SeqΩ sz =>
        (Sizes.seqXmat (sz.withLam 0) n ω) i j :=
      (measurable_Xentry d _ _ i j).comp (measurable_slice (sz.withLam 0) n)
    simpa [Sizes.seqHBA] using h.const_add _

section OU

variable {d : ℕ} {sz : Sizes d}

/-- The OU time `t* = N^{-1+τ_U}` at size `n` (the time of the proof of Theorem 2.4, as in
[DYYY25, Theorem 2.6]). -/
def ouTStar (sz : Sizes d) (τU : ℝ) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ) ^ (-1 + τU)

/-- The OU carrier at size `n`: the model and an independent GUE. -/
def ouP (M : UNModel sz) (n : ℕ) : Measure (Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :=
  M.μ.prod (gueP d (sz.L n) (sz.W n))

/-- The OU marginal `𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'`, `H'` an independent GUE
(`E|h'_ij|² = 1/N`). -/
def ouMat (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Real.exp (-t / 2) • M.H n ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2

theorem ouMat_isHermitian (M : UNModel sz) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : (ouMat M n t ω).IsHermitian :=
  ((M.herm n ω.1).smul (IsSelfAdjoint.all _)).add
    ((Xmat_isHermitian d _ _ ω.2).smul (IsSelfAdjoint.all _))

/-- `𝐇_0 = H`. -/
theorem ouMat_zero (M : UNModel sz) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat M n 0 ω = M.H n ω.1 := by
  simp [ouMat]

end OU

/-! ## The endpoint `Thm: B_Univ` and its dilated form -/

section Endpoint

/-- **`UNBUniv`: Theorem 2.4 `Thm: B_Univ`, (2.20) `eq:universality`**, band model.
The constants `(d, 𝔠, 𝔡)` come before the sequence `sz` (which carries `ilambda` as the sequence `sz.lam`);
`Admissible` is `W ≥ N^𝔠`, (2.10) `eq:WO`, `N → ∞`, `0 < 𝔠, 𝔡` (`Defs/Sizes.lean`); `k ≥ 1` is fixed,
`|E| ≤ 2 - κ`, `𝒪 ∈ C_c^∞(ℝ^k)`; the `N^{-1}` scale is the one of `kPoint`. -/
def UNBUniv : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        Tendsto (fun n =>
          (∫ ω, kPoint k O E (Sizes.seqXmat_isHermitian sz n ω).eigenvalues ∂(Sizes.seqP sz)) -
          (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))))
          atTop (𝓝 0)

variable {d : ℕ} {sz : Sizes d}

/-- **The dilated universality statement** at the density sequence `ρ` and the GUE energy `E'`: in the
normalisation `α = ρ β`,
`∫ 𝒪(α)[ρ_n^{-k} p_H^{(k)}(E + α/(Nρ_n)) - ρ_sc(E')^{-k} p_GUE^{(k)}(E' + α/(Nρ_sc(E')))] dα → 0`
is `E kPoint k 𝒪(ρ_n ·) E (λ(H)) - E kPoint k 𝒪(ρ_sc(E') ·) E' (λ(GUE)) → 0`.  The band model
is `ρ_n = ρ_sc(E)`, `E' = E` (`unBUniv_diff_eq`); the block Anderson model has `ρ_n = ρ_N(E)`. -/
def UNUnivDilAt (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
    (∫ ω, kPoint k (fun α => O (rhoSC E' • α)) E' (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
      ∂(gueP d (sz.L n) (sz.W n)))) atTop (𝓝 0)

theorem rhoSC_pos {E : ℝ} (hE : |E| < 2) : 0 < rhoSC E := by
  have h : E ^ 2 < 4 := by
    have := abs_lt.mp hE
    nlinarith [this.1, this.2]
  unfold rhoSC
  exact div_pos (Real.sqrt_pos.2 (by linarith)) (by positivity)

/-- The band model is the dilated statement at `ρ_n = ρ_sc(E)`, `E' = E`: the dilation of the test
function is undone by the substitution `𝒪' = 𝒪(ρ_sc(E)⁻¹ ·)` (the test functions are a vector space
closed under nonzero dilation, `isTestFun_comp_smul`). -/
theorem unBUniv_diff_eq (M : UNModel sz) {E : ℝ} (hE : |E| < 2) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (n : ℕ) :
    (∫ ω, kPoint k (fun α => (fun β => O ((rhoSC E)⁻¹ • β)) (rhoSC E • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
      (∫ ω, kPoint k (fun α => (fun β => O ((rhoSC E)⁻¹ • β)) (rhoSC E • α)) E
        (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) =
    (∫ ω, kPoint k O E (M.herm n ω).eigenvalues ∂M.μ) -
      (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
        ∂(gueP d (sz.L n) (sz.W n))) := by
  have hρ : rhoSC E ≠ 0 := (rhoSC_pos hE).ne'
  have : (fun α : Fin k → ℝ => (fun β => O ((rhoSC E)⁻¹ • β)) (rhoSC E • α)) = O := by
    funext α; simp [smul_smul, inv_mul_cancel₀ hρ]
  rw [this]

theorem isTestFun_comp_smul {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) {r : ℝ} (hr : r ≠ 0) :
    IsTestFun (fun β => O (r • β)) :=
  ⟨hO.1.comp (contDiff_const_smul r),
    hO.2.comp_isClosedEmbedding (Homeomorph.smulOfNeZero r hr).isClosedEmbedding⟩

end Endpoint

/-! ## The external input `UNL32` and its limit computation -/

section L32

/-- `m_V(z) = N⁻¹ ∑_i (v_i - z)⁻¹` ([LSY, (2.2)]). -/
def mV {ι : Type*} [Fintype ι] (v : ι → ℝ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹

/-- [LSY, Definition 2.1]: `V = diag v` is `(g, G)`-regular, [LSY, (2.2) and (2.3)]. -/
def IsRegular32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (g G c C CV : ℝ) : Prop :=
  (∀ E η : ℝ, |E| ≤ G → g ≤ η → η ≤ 10 →
      c ≤ (mV v ⟨E, η⟩).im ∧ (mV v ⟨E, η⟩).im ≤ C) ∧
    ∀ i, |v i| ≤ (Fintype.card ι : ℝ) ^ CV

/-- [LSY, (2.5)]: `m` solves the free-convolution equation on the upper half plane, `Im m > 0`. -/
def IsFreeConv32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧
    m z = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹

/-- [LSY, (2.1)] with GOE replaced by GUE: `V + √t H'`, `H' = Xmat` under `gueP` (`E|h'_ij|² = 1/N`). -/
def dbmMat (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ) (t : ℝ) (ω : Ω d L W) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt t • Xmat d L W ω

theorem dbmMat_isHermitian (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ) (t : ℝ)
    (ω : Ω d L W) : (dbmMat d L W v t ω).IsHermitian :=
  (Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).add
    ((Xmat_isHermitian d L W ω).smul (IsSelfAdjoint.all _))

/-- **`UNL32`: Theorem 2.2 of Landon–Sosoe–Yau [LSY] (*Fixed energy universality of Dyson Brownian
motion*, Adv. Math. 346 (2019); arXiv:1609.09011v4), complex Hermitian (GUE) version, unit density.**  This is the
one external input.  The statement follows the text of v4: its (2.9) carries the factors `ρ_fc^{-k}`,
`ρ_sc^{-k}`, and the Remark after Theorem 2.2 covers the complex Hermitian case.
* Hypotheses: [LSY, Definition 2.1] `((2.2), (2.3))`, `(2.5)–(2.6)`, `(2.8)`, `|E| ≤ qG`, eventually along a
  size sequence with `size n → ∞`; the matrix is `diag v + √t · GUE_N`, `N = (W L)^d`.  The hypotheses
  involve only the size `N` (not `d`, `W`, `L`); `d` enters through the carrier `Idx d L W` of the
  `N × N` matrix.
* Conclusion: (2.9) of v4 with the factors `ρ_fc^{-k}`, `ρ_sc^{-k}`, by `α = ρβ` the test function
  dilated by each side's own density, in the eigenvalue-sum form `kPoint`; the rate `C N^{-κ}` is
  weakened to `→ 0`.
* `size n → ∞` is a hypothesis (for a constant sequence the conclusion would equate two finite-`N`
  quantities).  The limit computation of the arithmetic hypotheses at the `d ≥ 3` parameters is
  `un_L32_arith`.
It is used once, in the comparison of `𝐇_{t*}` with the GUE in the proof of Theorem 2.4
(the argument of [DYYY25, Theorem 2.6]). -/
def UNL32 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ n, Idx d (sz.L n) (sz.W n) → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ n in atTop,
      ((sz.size n : ℕ) : ℝ) ^ δ / ((sz.size n : ℕ) : ℝ) ≤ g n ∧
      g n ≤ ((sz.size n : ℕ) : ℝ) ^ (-δ) ∧ G n ≤ ((sz.size n : ℕ) : ℝ) ^ (-δ) ∧
      g n * ((sz.size n : ℕ) : ℝ) ^ σ ≤ t n ∧ t n ≤ ((sz.size n : ℕ) : ℝ) ^ (-σ) * G n ^ 2 ∧
      |E n| ≤ q * G n ∧
      IsRegular32 (v n) (g n) (G n) c C CV ∧ IsFreeConv32 (v n) (t n) (m n) ∧
      Tendsto (fun η : ℝ => (m n ⟨E n, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
      Tendsto (fun n =>
        (∫ ω, kPoint k (fun α => O (ρ n • α)) (E n)
            (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (t n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        (∫ ω, kPoint k (fun α => O (rhoSC (E n) • α)) (E n)
            (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
        atTop (𝓝 0)

/-- **The limit computation of the arithmetic hypotheses of `UNL32`** at the OU time
`t = 1 - e^{-N^{-1+τ}}` (`t* = N^{-1+τ_U}`, `τ = τ_s`): with
`g = N^{-1+τ/4}`, `G = N^{-σ}`, `δ = σ = min(τ/4, (1-τ)/3)`, `q = 1/2`, `E = 0`, the six hypotheses
`N^σ/N ≤ g`, `g ≤ N^{-σ}`, `G ≤ N^{-σ}`, `g N^σ ≤ t`, `t ≤ N^{-σ} G²`, `|E| ≤ qG` hold as soon as
`N ≥ 1` and `N^{τ/2} ≥ 2` (i.e. `N ≥ 2^{2/τ}`).  They involve only `N` and `τ`: nothing here depends on
`d`, `W`, `L`, `ilambda`. -/
theorem un_L32_arith {N τ : ℝ} (hN : 1 ≤ N) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hN2 : 2 ≤ N ^ (τ / 2)) :
    let σ := min (τ / 4) ((1 - τ) / 3)
    let g := N ^ (-1 + τ / 4)
    let G := N ^ (-σ)
    let t := 1 - Real.exp (-(N ^ (-1 + τ)))
    N ^ σ / N ≤ g ∧ g ≤ N ^ (-σ) ∧ G ≤ N ^ (-σ) ∧ g * N ^ σ ≤ t ∧ t ≤ N ^ (-σ) * G ^ 2 ∧
      |(0 : ℝ)| ≤ (1 / 2) * G := by
  intro σ g G t
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hσ1 : σ ≤ τ / 4 := min_le_left _ _
  have hσ2 : σ ≤ (1 - τ) / 3 := min_le_right _ _
  have hσ0 : 0 < σ := lt_min (by linarith) (by linarith)
  have hx0 : 0 ≤ N ^ (-1 + τ) := Real.rpow_nonneg hN0.le _
  have hx1 : N ^ (-1 + τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hmono : ∀ {a b : ℝ}, a ≤ b → N ^ a ≤ N ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hN h
  refine ⟨?_, ?_, le_rfl, ?_, ?_, by simp only [abs_zero]; positivity⟩
  · have : N ^ σ / N = N ^ (σ - 1) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
    rw [this]
    exact hmono (by linarith)
  · exact hmono (by linarith)
  · -- `g N^σ ≤ N^{-1+τ/2} ≤ N^{-1+τ}/2 ≤ t`
    have hgσ : g * N ^ σ ≤ N ^ (-1 + τ / 2) := by
      have : g * N ^ σ = N ^ (-1 + τ / 4 + σ) := by
        rw [← Real.rpow_add hN0]
      rw [this]
      exact hmono (by linarith)
    have hsplit : N ^ (-1 + τ) = N ^ (-1 + τ / 2) * N ^ (τ / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have ht : N ^ (-1 + τ) / 2 ≤ t := by
      change N ^ (-1 + τ) / 2 ≤ 1 - Real.exp (-(N ^ (-1 + τ)))
      set x := N ^ (-1 + τ) with hx
      have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
      have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      have h3 : Real.exp (-x) * (x + 1) ≤ 1 := by
        calc Real.exp (-x) * (x + 1) ≤ Real.exp (-x) * Real.exp x :=
              mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
          _ = 1 := h2
      nlinarith [Real.exp_pos (-x)]
    calc g * N ^ σ ≤ N ^ (-1 + τ / 2) := hgσ
      _ ≤ N ^ (-1 + τ / 2) * N ^ (τ / 2) / 2 := by
          have : 0 < N ^ (-1 + τ / 2) := Real.rpow_pos_of_pos hN0 _
          nlinarith
      _ = N ^ (-1 + τ) / 2 := by rw [hsplit]
      _ ≤ t := ht
  · have htle : t ≤ N ^ (-1 + τ) := by
      change 1 - Real.exp (-(N ^ (-1 + τ))) ≤ N ^ (-1 + τ)
      have := Real.add_one_le_exp (-(N ^ (-1 + τ)))
      linarith
    have hG2 : G ^ 2 = N ^ (-σ * 2) := by
      change (N ^ (-σ)) ^ 2 = N ^ (-σ * 2)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    rw [hG2, ← Real.rpow_add hN0]
    exact htle.trans (hmono (by linarith))

end L32

/-! ## The model-level statements -/

section Pins

variable {d : ℕ}

/-- The one scale `N = (W L)^d = sz.size n` as a real number. -/
abbrev Nsz (sz : Sizes d) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ)

/-! ### Statements taken from the local law, the density and quantum unique ergodicity -/

/-- `𝓘_E(ε₀) = {x : |x - E| ≤ W^{-ε₀} (ilambda W^{d/2} / N)}` of (2.17) `eq:defIE`.  The footnote after
Theorem 2.1 (`MR:decol`) replaces `ilambda` by `ilambda ∧ 1`; only the lower bound
`W^{-ε₀}(lam ∧ 1) W^{d/2} ≥ W^{2𝔡/3}` is used here (`un_window_sub`), which holds for both readings. -/
def queWindow (d L W : ℕ) (lam ε₀ E x : ℝ) : Prop :=
  |x - E| ≤ (W : ℝ) ^ (-ε₀) * (lam * (W : ℝ) ^ ((d : ℝ) / 2) / (((W * L) ^ d : ℕ) : ℝ))

/-- The probability bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}` of (2.18) `Meq:QUE`. -/
def queBound (W : ℕ) (𝔡 ε₀ c τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((W : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ))

/-- The failure event of (2.18) `Meq:QUE` at the block `a` for an arbitrary Hermitian
matrix `M` on the fine lattice: some orthonormal eigenbasis has `i, j` in the window `𝓘_E(ε₀)` with
`|∑_{x∈[a]} conj ψ_i(x) ψ_j(x) - (W^d/N) δ_ij| ≥ W^{d-c}/N`. -/
def queBadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (a : Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ i j, queWindow d L W lam ε₀ E (μ i) ∧ queWindow d L W lam ε₀ E (μ j) ∧
      (W : ℝ) ^ ((d : ℝ) - c) / (((W * L) ^ d : ℕ) : ℝ) ≤
        ‖(∑ x ∈ Iblk d L W a, star (ψ i x) * ψ j x) -
            ((W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ)) * (if i = j then 1 else 0)‖

/-- **`UNQueBand`: (2.18) `Meq:QUE`** (Theorem 2.3 `MR:QUE`), band model, for the parameters
`ε₀ ∈ (0, 𝔡/2)`, `0 < c < ε₀ ∧ 𝔡/5`, any `τ > 0`, eventually, uniformly in `|E| ≤ 2 - κ` and the block `a`.
(The statement (2.19) `Meq:QUE2` is not used.) -/
def UNQueBand : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
        Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (Sizes.seqXmat sz n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- **`UNLocAvgBand`: (2.15) `G_bound_ave`**, the averaged local law on a block, band model, with the
intersection over `z` inside the probability: `|W^{-d} ∑_{x∈[a]} G_xx(z) - m(z)| ≤ W^τ B_{η,0}` for every block,
`W^{-d}B_{η,0} = sz.Bctl n (1-η)` ((2.13) `eq:calBetaK` at `K = 0`), `m = msc`.  (The entrywise
estimate (2.14) `G_bound` is not used.) -/
def UNLocAvgBand : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ∃ z : ℂ, sz.locDomain κ ε n z ∧ ∃ a : Zd d (sz.L n),
          ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (Sizes.seqXmat sz n ω) z true x x - msc z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNMLOut`: the `G`-loop outputs along `z`-sequences** (Lemma 2.21 `ML:GLoop`, Lemma 2.22 `ML:GLoop_expec`,
Lemma 2.23 `ML:GtLocal`, "fix any `z ∈ 𝐃_{κ,ε}` ... uniformly in `t ∈ [0, t₀]`"): the conclusions
of `STMainInd` at every time sequence `0 ≤ t_n ≤ lemT z_n`:
`STLK`, `STLmax`, `STDecay`, `STExp2`, `STLocalEntry`. -/
def UNMLOut (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
        STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t

/-! ### The local law and the density -/

/-- **The tracial local law of a model at the Stieltjes transforms `m n`**, in a window `|Re z - E| ≤ δ`
around the energy: with probability `≥ 1 - N^{-D}`, simultaneously for all `z` with
`N^{-1+ε} ≤ Im z ≤ 1`, `|m_N(z) - m_n(z)| ≤ W^τ B_{η,0}`, `W^{-d}B_{η,0} = sz.Bctl n (1-η)`
((2.13) `eq:calBetaK`).  For the band model `m n = msc`, a consequence of `UNLocAvgBand` (average over the `L^d`
blocks; `δ ≤ κ/2`); for the block Anderson model `m n = m(z, λ_n)` of (2.32) `self_m`. -/
def UNTrLocal (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) < ‖stieltjesN (M.H n ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **The regularity of the density used by the comparison**: near `E`, in the window `|x - E| ≤ δ`, `0 < η ≤ 10`,
`c ≤ Im m_n(x + iη) ≤ C` (the bounds (2.2) of [LSY, Definition 2.1] for the free-convolution input), `x ↦ Im m_n(x+iη)`
is `Lp`-Lipschitz uniformly in `η` (so `ρ_n` is `Lp`-Lipschitz and the free convolution with a
semicircle of variance `t* ≪ 1` has density within `O(t*)` of `ρ_n`), and `ρ_n = π⁻¹ Im m_n(E + i0)`.
For the band model `m n = msc`, `ρ_n = ρ_sc(E)`; the block Anderson model has `ρ_n = ρ_N(E)`.  This is a
condition on the deterministic data `m`. -/
def UNDens (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ c C Lp : ℝ, 0 < c ∧ 0 < C ∧ 0 < Lp ∧ ∀ᶠ n in atTop,
    (∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 →
      c ≤ (m n ⟨x, η⟩).im ∧ (m n ⟨x, η⟩).im ≤ C) ∧
    (∀ x y η : ℝ, |x - E| ≤ δ → |y - E| ≤ δ → 0 < η → η ≤ 10 →
      |(m n ⟨x, η⟩).im - (m n ⟨y, η⟩).im| ≤ Lp * |x - y|) ∧
    Tendsto (fun η : ℝ => (m n ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))

/-- **Polynomial bound on the spectrum of the model** ((2.3) of [LSY, Definition 2.1], `‖V‖ ≤ N^{C_V}`):
for every `D > 0`, eventually, with probability `≥ 1 - N^{-D}` all eigenvalues of `H` are `≤ N^{CV₀}` in modulus.
It cannot be derived from `UNTrLocal`: a deterministic diagonal model with the semicircle quantiles plus one
eigenvalue `N^{10}` has the local law and the regularity of the density but violates (2.3).
For the band model `CV₀ = 3` (`unNormBandRow`: from the Gaussian entry tails every entry is at most `2N`, so
`|λ| ≤ N³`); for the block Anderson
model `‖V‖ + ilambda ‖Ψ‖`. -/
def UNNormBound (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-! ### The weak GUE local law -/

/-- **`UNGUELocal`**: a weak averaged bulk local law of the `N × N` GUE, `N = (W L)^d`:
`|m_N(z) - m_sc(z)| ≤ N^τ (N Im z)^{-1/2}` for `N^{-1+τ} ≤ Im z ≤ 10`, `|Re z| ≤ 2 - κ`, union over `z`
inside the probability.  It is not stated in the paper; it is needed to move the GUE statistics from energy `0`
(where [LSY] compares) to `E'`.  It is dimension-free (only `N`). -/
def UNGUELocal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    gueP d (sz.L n) (sz.W n) {ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
        Nsz sz n ^ τ / Real.sqrt (Nsz sz n * z.im) <
          ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-! ### The claim (2.20) of [DYYY25], the comparison, the two limits -/

/-- The spectral window of the Claim of [DYYY25, (2.20)]: `|E_j - E| ≤ C₀/N`,
`N^{-1-τ_U} ≤ η_j ≤ N^{-1+τ_U}`. -/
def InWindow (sz : Sizes d) (E C₀ τU : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  |z.re - E| ≤ C₀ / Nsz sz n ∧ Nsz sz n ^ (-1 - τU) ≤ z.im ∧ z.im ≤ Nsz sz n ^ (-1 + τU)

/-- **`UNClaim417`**: the Claim [DYYY25, (2.20)] for the OU path of a model: for `nf` factors,
`sup_{0≤t≤t*} |E ∏ Im m_t(z_i) - E ∏ Im m_{t*}(z_i)| ≤ N^{-c' + C_n τ_U}`, eventually, for every `C₀`.
`c'`, `C_n` are parameters (`c' = 𝔠𝔡/30` in the application). -/
def UNClaim417 (sz : Sizes d) (M : UNModel sz) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ, (∀ i, InWindow sz E C₀ τU n (z i)) →
    ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      |(∫ ω, ∏ i, (stieltjesN (ouMat M n t ω) (z i)).im ∂(ouP M n)) -
        ∫ ω, ∏ i, (stieltjesN (ouMat M n (ouTStar sz τU n) ω) (z i)).im ∂(ouP M n)| ≤
        Nsz sz n ^ (-c' + Cn * τU)

/-- `UNClaim417` for all `n_f`, for all small `τ_U`, at one exponent `c' > 0`. -/
def UNClaimAll (sz : Sizes d) (M : UNModel sz) (E : ℝ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNClaim417 sz M E nf τU c' Cn

/-- The a priori bound at the level spacing: `E (Im m_0(E + i/N))^p ≤ N^ε`
eventually. -/
def UNApriori (sz : Sizes d) (M : UNModel sz) (E : ℝ) : Prop :=
  ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∫ ω, (stieltjesN (ouMat M n 0 ω) ((E : ℂ) + ((Nsz sz n)⁻¹ : ℂ) * Complex.I)).im ^ p ∂(ouP M n) ≤
      Nsz sz n ^ ε

/-- **`UNGreenCorr`**: the Green-function-to-correlation comparison used in the proof of Theorem 2.4
("Theorem 15.3 in Erdős–Yau (*A dynamical approach to random matrix theory*), Proposition 4.17 in Xu–Yang–Yau–Yin
(Ann. Probab. 2024), (2.23) in [YY_25]").  If the Claim holds for all
`n_f ≤ k` at `τ_U ≤ τ₀` and the a priori bound holds, the `k`-point functionals of `𝐇_0` and `𝐇_{t*}`
have the same limit, for the test function dilated by any sequence `r_n ∈ [a, b] ⊂ (0, ∞)` (eventually).
The dilation is a sequence `r_n`, since the band model needs `r_n ≡ ρ_sc(E)` and the block Anderson model has
`r_n = ρ_N(E)` varying; the smoothing argument is uniform over a `C^∞`-bounded family of test functions.
The threshold `τ₀` depends on `E, k, c', C_n` only. -/
def UNGreenCorr (sz : Sizes d) (M : UNModel sz) : Prop :=
  ∀ (E : ℝ) (k : ℕ) (c' : ℝ), 0 < c' → ∀ Cn : ℕ → ℝ, ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → (∀ nf ≤ k, UNClaim417 sz M E nf τU c' (Cn nf)) → UNApriori sz M E →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → ∀ (r : ℕ → ℝ) (a b : ℝ), 0 < a → (∀ᶠ n in atTop, a ≤ r n ∧ r n ≤ b) →
        Tendsto (fun n =>
          (∫ ω, kPoint k (fun α => O (r n • α)) E (ouMat_isHermitian M n 0 ω).eigenvalues ∂(ouP M n)) -
          (∫ ω, kPoint k (fun α => O (r n • α)) E
              (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)))
          atTop (𝓝 0)

/-- `UNGreenCorr` for every model along every size sequence with `size n → ∞`. -/
def UNGreenCorrAll : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
    ∀ M : UNModel sz, UNGreenCorr sz M

/-- **The comparison of `𝐇_{t*}` with the GUE** [DYYY25, proof of Theorem 2.6] at `τ_U`: the `𝐇_{t*}` functional,
dilated by `ρ_n`, against the GUE functional at energy `E'` dilated by `ρ_sc(E')`. -/
def UNInfty1 (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E
        (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)) -
    (∫ ω, kPoint k (fun α => O (rhoSC E' • α)) E'
        (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
    atTop (𝓝 0)

/-- **The comparison of `H = 𝐇_0` with `𝐇_{t*}`** [DYYY25, proof of Theorem 2.6] at `τ_U`: both functionals dilated by
`ρ_n`. -/
def UNUnivMain (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E
        (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)))
    atTop (𝓝 0)

/-- The shifted, rescaled diagonal of the free-convolution step: `v_i = e^{-t*/2} λ_i(H) - E₀`, `t* = N^{-1+τ_s}`. -/
def vOU (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ sz) :
    Idx d (sz.L n) (sz.W n) → ℝ :=
  fun i => Real.exp (-(ouTStar sz τs n) / 2) * (M.herm n ω).eigenvalues i - E₀

/-- **`UNStep1Good`**: the regularity event of the free-convolution step (comparison of `𝐇_{t*}` with the GUE):
with probability `≥ 1 - N^{-D}` the shifted diagonal
`v = e^{-t*/2} λ(H) - E` is `(g, G)`-regular with `g = N^{-1+τ_s/4}`, `G = N^{-min(τ_s/4,(1-τ_s)/3)}`,
`CV = CV₀ + 1` (from `UNNormBound sz M CV₀`: `|v_i| ≤ N^{CV₀} + |E| ≤ N^{CV₀+1}`), and the free convolution with a
semicircle of variance `1 - e^{-t*}` has a density at `0` within `N^{-3τ_s/8}` of `ρ_n`.  The range of `τ_s` is
`τ_s ≤ 𝔠𝔡`: the local-law floor is `W^{-d}(lam² + η)^{-1} ≤ W^{-2𝔡} ≤ N^{-2𝔠𝔡}` (`un_Bctl_le`, `un_step1_floor`).
The constants `c, C` are produced from those of `UNDens`.  The hypotheses `UNDens` and `UNTrLocal` observe `m_n` only
for `0 < η ≤ 10` and `N^{-1+ε} ≤ Im z ≤ 1` respectively: replacing `m_n` by `m_n + (i/2) 1{Im z < N^{-2}}` keeps both
and moves `ρ_n` by `1/(2π)`, so the conclusion needs the box hypotheses of `UNDens'` (`UNStep1Good'`). -/
def UNStep1Good : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

end Pins

/-! ## The band-model chain: the `𝐇_t` claims, (2.21), (2.22), (2.23) of [DYYY25]

These are specific to the band model (Gaussian, mean `0`, variance profile `S`): the generator identity of
the OU flow of [DYYY25, (2.21)] has a first-order drift term for a model with a nonzero mean `ilambda Ψ` (block
Anderson).  The band model produces the Claim [DYYY25, (2.20)] from the statements of this section
(`un_claimAll_of_rows`). -/

section Band

variable {d : ℕ}

/-- `S°_{xy} = S_{xy} - N⁻¹`, `S_xy = svarF` ((2.5) `eq:variancematrix`). -/
def scirc (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (x y : Idx d L W) : ℂ :=
  ((svarF d L W lam x y : ℝ) : ℂ) - ((((W * L) ^ d : ℕ) : ℂ))⁻¹

/-- `L_{1,t}(z)` of [DYYY25, proof of Theorem 2.6] at the matrix `M = 𝐇_t`; `G ∈ {R, R^*}` is `Gres M z b`
(`Gres M z false = (M - z̄)⁻¹ = R^*` for Hermitian `M`). -/
def L1t (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool,
    ‖((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ a, ∑ b,
      (Gres M z b₁ * Gres M z b₁) a a * scirc d L W lam a b * Gres M z b₂ b b‖

/-- `L_{2,t}(z₁, z₂)` of [DYYY25, proof of Theorem 2.6] at the matrix `M = 𝐇_t`. -/
def L2t (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z₁ z₂ : ℂ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool,
    ‖(((((W * L) ^ d : ℕ) : ℂ))⁻¹) ^ 2 * ∑ a, ∑ b,
      (Gres M z₁ b₁ * Gres M z₁ b₁) a b * scirc d L W lam a b *
        (Gres M z₂ b₂ * Gres M z₂ b₂) b a‖

/-- **`UNOUQUE`: the first `𝐇_t` claim** (as in [DYYY25]: "details identical to Section 7.2 of
[YY_25]"): (2.18) `Meq:QUE` holds for `𝐇_t`, uniformly in `t ∈ [0, t*]`,
`t* = N^{-1+τ_U}`, at the parameters `ε₀ = 𝔡/3`, `c = 𝔡/6` of the proof of Theorem 2.4, for every `τ > 0`: the failure
probability is `≤ W^{-(2ε₀)∧(2𝔡/5)+2c+τ} = W^{-𝔡/15+τ}` (`un_que_exponent`).  (2.19) `Meq:QUE2` for `𝐇_t`
is not used. -/
def UNOUQUE (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ τQ : ℝ, 0 < κ → 0 < τQ → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
      ouP (UNModel.band sz) n
          {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a
            (ouMat (UNModel.band sz) n t ω)} ≤
        queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ

/-- **`UNOUDiag`: the second `𝐇_t` claim** (as in [DYYY25]): for `t ∈ [0, t*]`, `|E| ≤ 2 - κ`,
`η = N^{-1+2τ_U}`: `max_x |(𝐑_t(E + iη))_{xx}| ≺ 1`, union over `x` inside `P`.  Delocalization of `𝐇_t`
(`|ψ_α(x)|² ≤ η Im 𝐑_xx`, (2.16) `eq:ukx`). -/
def UNOUDiag (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ ε D : ℝ, 0 < κ → 0 < ε → 0 < D → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, |E| ≤ 2 - κ →
      ouP (UNModel.band sz) n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
          Nsz sz n ^ ε <
            ‖Gres (ouMat (UNModel.band sz) n t ω)
                ((E : ℂ) + ((Nsz sz n ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) true x x‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- The two `𝐇_t` claims for all small `τ_U` (as in [DYYY25]: "for `τ_U > 0` sufficiently small"). -/
def UNOUClaims : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUE sz 𝔡 τU ∧ UNOUDiag sz τU

/-- **`UNEMCTE2`** ([DYYY25, (2.21)]: "argue as in Step 3 of the proof of Theorem 2.6 in [YY_25]"),
in the weighted form of [YY_25]: the left side of the Claim [DYYY25, (2.20)] is `≤ N^ε N^{-1+C_nτ_U}` times a bound `B` on
`E[(∏_{j≠u} Im m_s(z_j)) L_{1,s}(z_u)]` (all `u`) and on `E[(∏_{k∉{u,v}} Im m_s(z_k)) L_{2,s}(z_u,z_v)]`
(`u ≠ v`), `s ∈ [0, t*]`; `0 ≤ B` is needed (`n_f = 0`; see `un_emcte2_zero`).
The generator identity is exact for a centred Gaussian model: band only. -/
def UNEMCTE2 (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ B : ℝ, 0 ≤ B →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar sz τU n → ∀ u : Fin nf,
        ∫ ω, (∏ j ∈ Finset.univ.erase u,
            (stieltjesN (ouMat (UNModel.band sz) n s ω) (z j)).im) *
          L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z u)
          ∂(ouP (UNModel.band sz) n) ≤ B) →
      (∀ s : ℝ, 0 ≤ s → s ≤ ouTStar sz τU n → ∀ u v : Fin nf, u ≠ v →
        ∫ ω, (∏ k ∈ (Finset.univ.erase u).erase v,
            (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
          L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z u) (z v)
          ∂(ouP (UNModel.band sz) n) ≤ B) →
      ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
        |(∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im ∂(ouP (UNModel.band sz) n)) -
          ∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n (ouTStar sz τU n) ω) (z i)).im
            ∂(ouP (UNModel.band sz) n)| ≤
          Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) * B

/-- **`UNJak`: [DYYY25, (2.22)]** (this paper names "the proofs of equations (2.22) and (2.23)" of [DYYY25] in the proof
of Theorem 2.4): with the
exponent `c'` (value `𝔠𝔡/30` at `d ≥ 3`), the slack `N^ε` and a weight
`∏_{j∈s} Im m_t(z_j)` for every `s`, `max_i max_y E[(∏_{j∈s} Im m_t(z_j)) |∑_x (G₁²(z_i))_{xx} S°_{xy}
(G₂(z_i))_{yy}|] ≤ N^{ε} N^{1-c'+Cτ_U}`, `t ∈ [0,t*]`.  The proof splits on the bad event `𝓑(y)`
(`UNBadY`). -/
def UNJak (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      ∀ (s : Finset (Fin nf)) (i : Fin nf) (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ j ∈ s, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z j)).im) *
          ‖∑ x, (Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁ *
              Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁) x x *
            scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
              Gres (ouMat (UNModel.band sz) n t ω) (z i) b₂ y y‖
          ∂(ouP (UNModel.band sz) n) ≤
          Nsz sz n ^ ε * Nsz sz n ^ (1 - c' + C * τU)

/-- **`UNUyw`: [DYYY25, (2.23)]**: the same as `UNJak` with `N^{2-c'+Cτ_U}`
and the pair `i ≠ j`. -/
def UNUyw (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
  ∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ,
    (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      ∀ (s : Finset (Fin nf)) (i j : Fin nf), i ≠ j → ∀ (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool),
        ∫ ω, (∏ k ∈ s, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z k)).im) *
          ‖∑ x, (Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁ *
              Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁) x y *
            scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
              (Gres (ouMat (UNModel.band sz) n t ω) (z j) b₂ *
                Gres (ouMat (UNModel.band sz) n t ω) (z j) b₂) y x‖
          ∂(ouP (UNModel.band sz) n) ≤
          Nsz sz n ^ ε * Nsz sz n ^ (2 - c' + C * τU)

end Band

/-! ## The comparison statement `UNUnivMainRow` -/

section Rows

/-- **`UNUnivMainRow`**: the comparison of `H = 𝐇_0` with `𝐇_{t*}` from the Claim [DYYY25, (2.20)], the local law and
density (a priori bound `UNApriori`) and `UNGreenCorrAll`, for every `τ_U ∈ (0, τ₀]`, `τ₀` independent of `O`. -/
def UNUnivMainRow : Prop :=
  UNGreenCorrAll →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → UNClaimAll sz M E →
          ∀ k : ℕ, ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
            ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivMain sz M ρ E k O τU

end Rows

/-! ### The band-model statements, and `UNBUniv` from them -/

section BandRows

/-- **`UNOURow`**: the `𝐇_t` claims from the `G`-loop outputs, (2.15) `G_bound_ave` and (2.18) `Meq:QUE` at `t = 0`
(as in [DYYY25]: "treating `𝐇_t` as a perturbation of `𝐇_0`; the details are identical to Section 7.2 of
[YY_25]"; this is the random layer of the GUE phase, with `UNOUQUE` at the
parameters `ε₀ = 𝔡/3`, `c = 𝔡/6`). -/
def UNOURow : Prop := (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNOUClaims

/-- **`UNEMCTE2Row`**: the weighted [DYYY25, (2.21)] from the OU generator identity alone. -/
def UNEMCTE2Row : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2 sz E nf τU Cn

/-- **`UNJakUywRow`**: the weighted [DYYY25, (2.22)] and [DYYY25, (2.23)] at `c' = 𝔠𝔡/30` from the local law and
the `𝐇_t` claims (`UNBadY`, `unBadY_measure_le`). -/
def UNJakUywRow : Prop :=
  UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJak sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)

/-- **`UNClaimRow`** (arithmetic): [DYYY25, (2.21)] with [DYYY25, (2.22)], [DYYY25, (2.23)], all weighted, give
the Claim [DYYY25, (2.20)] at `c' = 𝔠𝔡/30`, `C_n' = C_n + C + 1` (`UNJak` at `s = univ.erase u` bounds the `L₁` term,
`UNUyw` at `s = (univ.erase u).erase v` the `L₂` term). -/
def UNClaimRow : Prop :=
  (∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNEMCTE2 sz E nf τU Cn ∧ UNJak sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)) →
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E

/-- **`UNDensBandRow`** (deterministic): the density regularity `UNDens` of the semicircle,
`m n = msc`, `ρ_n = ρ_sc(E)`, in a window `δ ≤ κ/2` inside the bulk (Stieltjes bounds, Lipschitz in `x`,
the limit `η ↓ 0`; compare `freeConvST_zero_eq_msc`: continuity of `m_sc` up to the real axis). -/
def UNDensBandRow : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∃ δ : ℝ, δ ≤ κ / 2 ∧ UNDens (fun _ => msc) E (fun _ => rhoSC E) δ

/-- **`UNNormBandRow`**: the band model satisfies `UNNormBound` for some `CV₀ ≥ 0` (every entry has variance
`S_xy ≤ 1`; `unNormBandRow` proves it with `CV₀ = 3`: with probability `≥ 1 - N^{-D}` every entry is at most `2N`,
so `|λ| ≤ N³`). -/
def UNNormBandRow : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz (UNModel.band sz) CV₀

/-- **`UNTrLocalBandRow`**: the tracial local law from the block-averaged (2.15) `G_bound_ave`
(`N⁻¹ Tr G - m = L^{-d} ∑_a (W^{-d} ∑_{x∈[a]} G_xx - m)`, with the intersection over `z` inside the probability). -/
def UNTrLocalBandRow : Prop :=
  UNLocAvgBand → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ δ : ℝ, 0 < δ → δ ≤ κ / 2 →
      UNTrLocal sz (UNModel.band sz) (fun _ => msc) E δ

/-- **The `𝐇_t` claims and [DYYY25, (2.21)], [DYYY25, (2.22)], [DYYY25, (2.23)] give the Claim [DYYY25, (2.20)]** for the band
model from `UNMLOut`, `UNLocAvgBand`, `UNQueBand`. -/
theorem un_claimAll_of_rows (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E := by
  have hOU := rO hML hLoc hQ
  apply rC
  intro d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨Cn, τ₁, hτ₁, h1⟩ := rE d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  obtain ⟨C, τ₂, hτ₂, h2⟩ := rJ hLoc hOU d hd 𝔠 𝔡 sz hA κ hκ E hE nf
  refine ⟨Cn, C, min τ₁ τ₂, lt_min hτ₁ hτ₂, fun τU h0 hle => ?_⟩
  have hJU := h2 τU h0 (hle.trans (min_le_right _ _))
  exact ⟨h1 τU h0 (hle.trans (min_le_left _ _)), hJU.1, hJU.2⟩

end BandRows

/-! ## The exponents of the proof of Theorem 2.4 and the limit computations at `d ≥ 3`

Every lemma is a deterministic inequality between the parameters `𝔠, 𝔡, N, W, ilambda, τ`. -/

section Arith

/-- **The QUE exponent of the proof of Theorem 2.4**: `(2ε₀)∧(2𝔡/5) = 2𝔡/5` and `-(2𝔡/5) + 2c = -𝔡/15` at `ε₀ = 𝔡/3`,
`c = 𝔡/6` (`ℙ(𝓑) ≤ W^{-𝔡/15+τ}`). -/
theorem un_que_exponent {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) :
    -(min (2 * (𝔡 / 3)) (2 * 𝔡 / 5)) + 2 * (𝔡 / 6) = -(𝔡 / 15) := by
  rw [min_eq_right (by linarith)]; ring

/-- **The `𝓑(y)`-window lies in `𝓘_E(𝔡/3)`** (`|λ_α - E| ≤ N^{-1}W^{𝔡/3}` against
`𝓘_E(ε₀)`, `ε₀ = 𝔡/3`, (2.17) `eq:defIE`): from (2.10) `eq:WO`, `ilambda ≥ W^{-d/2+𝔡}`, `W ≥ 1`, the half-width
`W^{-𝔡/3}(lam W^{d/2}/N)` is at least `W^{2𝔡/3}/N ≥ W^{𝔡/3}/N`.  Holds for every `lam ≥ W^{-d/2+𝔡}`
(in particular at both ends of (2.10) `eq:WO`), and for `lam ∧ 1` (footnote after Theorem 2.1) since `W^{-d/2+𝔡} ≤ 1`. -/
theorem un_window_sub {d : ℕ} {W N lam 𝔡 : ℝ} (hW : 1 ≤ W) (hN : 0 < N) (h𝔡 : 0 < 𝔡)
    (hlam : W ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) :
    N⁻¹ * W ^ (𝔡 / 3) ≤ W ^ (-(𝔡 / 3)) * (lam * W ^ ((d : ℝ) / 2) / N) := by
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW
  have h1 : W ^ (-(𝔡 / 3)) * (W ^ (-(d : ℝ) / 2 + 𝔡) * W ^ ((d : ℝ) / 2)) = W ^ (2 * 𝔡 / 3) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
  have h2 : W ^ (𝔡 / 3) ≤ W ^ (2 * 𝔡 / 3) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have h3 : W ^ (-(𝔡 / 3)) * (W ^ (-(d : ℝ) / 2 + 𝔡) * W ^ ((d : ℝ) / 2)) ≤
      W ^ (-(𝔡 / 3)) * (lam * W ^ ((d : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlam (by positivity)) (by positivity)
  calc N⁻¹ * W ^ (𝔡 / 3) ≤ N⁻¹ * W ^ (2 * 𝔡 / 3) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (W ^ (-(𝔡 / 3)) * (W ^ (-(d : ℝ) / 2 + 𝔡) * W ^ ((d : ℝ) / 2))) / N := by
        rw [h1]; ring
    _ ≤ (W ^ (-(𝔡 / 3)) * (lam * W ^ ((d : ℝ) / 2))) / N := by
        gcongr
    _ = W ^ (-(𝔡 / 3)) * (lam * W ^ ((d : ℝ) / 2) / N) := by ring

/-- `W ≥ N^𝔠` converts a `W`-power into an `N`-power: `W^{-x} ≤ N^{-𝔠x}` for `x ≥ 0` (this is where
(2.9) `Main_DEL_COND` enters, besides `W → ∞`). -/
theorem un_W_neg_le {W N 𝔠 x : ℝ} (hN : 0 < N) (hW : 0 < W) (hx : 0 ≤ x) (hb : N ^ 𝔠 ≤ W) :
    W ^ (-x) ≤ N ^ (-(𝔠 * x)) := by
  have h1 : N ^ (𝔠 * x) ≤ W ^ x := by
    rw [Real.rpow_mul hN.le]; exact Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hb hx
  rw [Real.rpow_neg hW.le, Real.rpow_neg hN.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN _) h1

/-- **`Bctl` at the energy scale `η`**: `W^{-d}B_{1-η,0} ≤ W^{-2𝔡}`-floor `+ (Nη)⁻¹` ((2.13) `eq:calBetaK` at
`K = 0` and (2.10) `eq:WO`: `A = W^{2𝔡} ≤ lam² W^d`).  This is the local-law precision of `UNTrLocal`; its floor
`W^{-2𝔡} ≤ N^{-2𝔠𝔡}` (`un_W_neg_le`) is what limits `τ_s ≤ 𝔠𝔡` in `UNStep1Good`. -/
theorem un_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {η A : ℝ} (hη : 0 < η) (hA : 0 < A)
    (hlam : A ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) :
    sz.Bctl n (1 - η) ≤ A⁻¹ + (Nsz sz n * η)⁻¹ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hl2 : 0 < sz.lam n ^ 2 := by
    by_contra h
    have h0 : sz.lam n ^ 2 ≤ 0 := not_lt.mp h
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0 hWd.le
    linarith
  have habs : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  have hN : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Nsz Sizes.size
    push_cast; rw [mul_pow]
  unfold Sizes.Bctl Bparam
  rw [habs]
  have e1 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [e1, inv_one, mul_one, mul_add]
  have t1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + η)⁻¹ ≤ A⁻¹ := by
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + η)⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ := by
          gcongr; linarith
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [mul_comm, mul_inv]
      _ ≤ A⁻¹ := inv_anti₀ hA hlam
  have t2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ = (Nsz sz n * η)⁻¹ := by
    rw [hN, ← mul_inv, mul_assoc]
  rw [t2]
  linarith

/-- **The floor of the local law against the precision `N^{-15τ_s/16}` of the strip**: for `τ_s ≤ 𝔠𝔡`, `𝔠 < 1`,
`W ≥ N^𝔠 ≥ 1`, the floor term times the loss
`W^{τ_s/8}` is `≤ N^{-15τ_s/16}`.  At `d ≥ 3` the floor is `W^{-2𝔡} ≤ N^{-2𝔠𝔡}`: the range of the free
convolution step is `τ_s ≤ 𝔠𝔡` (for `W = N^𝔠` the inequality holds exactly for `τ_s ≤ 32𝔠𝔡/(15+2𝔠)`, so `τ_s ≤ 𝔠𝔡` is not the sharp range). -/
theorem un_step1_floor {W N 𝔠 𝔡 τs : ℝ} (hN : 1 ≤ N) (hW : 1 ≤ W) (_h𝔠 : 0 < 𝔠) (h𝔠1 : 𝔠 < 1)
    (h𝔡 : 0 < 𝔡) (hτ : 0 < τs) (hτ𝔠 : τs ≤ 𝔠 * 𝔡) (hb : N ^ 𝔠 ≤ W) :
    W ^ (τs / 8) * W ^ (-(2 * 𝔡)) ≤ N ^ (-(15 * τs / 16)) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW
  have hx : 0 ≤ 2 * 𝔡 - τs / 8 := by nlinarith
  have h1 : W ^ (τs / 8) * W ^ (-(2 * 𝔡)) = W ^ (-(2 * 𝔡 - τs / 8)) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  rw [h1]
  refine (un_W_neg_le hN0 hW0 hx hb).trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
  nlinarith

/-- **`𝔠 d < 1`**: `W ≥ N^𝔠` with `N = (WL)^d`, `L ≥ 3`, `W ≥ 1` forces `d𝔠 < 1` (the range `𝔠 ∈ (0, 1/d)`
of the exponent table; the constraint is `L ≤ W^{1/(d𝔠)-1}`). -/
theorem un_dc_lt_one {d L W : ℕ} (_hd : 1 ≤ d) (hL : 3 ≤ L) (hW : 1 ≤ W) {𝔠 : ℝ} (_h𝔠 : 0 < 𝔠)
    (hb : (((W * L) ^ d : ℕ) : ℝ) ^ 𝔠 ≤ (W : ℝ)) : (d : ℝ) * 𝔠 < 1 := by
  by_contra hcon
  have h1 : (1 : ℝ) ≤ (d : ℝ) * 𝔠 := not_lt.mp hcon
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hWL : (1 : ℝ) ≤ (W : ℝ) * L := by nlinarith
  have hN : (((W * L) ^ d : ℕ) : ℝ) ^ 𝔠 = ((W : ℝ) * L) ^ ((d : ℝ) * 𝔠) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [hN] at hb
  have h2 : (W : ℝ) * L ≤ ((W : ℝ) * L) ^ ((d : ℝ) * 𝔠) := by
    calc (W : ℝ) * L = ((W : ℝ) * L) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hWL h1
  nlinarith

end Arith

/-! ## The bad event `𝓑(y)` of the proof of Theorem 2.4 and its probability (the `d ≥ 3` step of (2.22), (2.23) of [DYYY25])

[DYYY25] defines `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}` below its eigenvector representation of the left side of (2.22);
this paper cites it ("`M_{y,α}` is defined below equation (2.24) of [DYYY25]").  For `d ≥ 3` the profile `S^{(B)}(ilambda)` has the weights
`(1 + 2d lam²)⁻¹ (δ_{ab} + lam² 1_{a∼b})` on `2d + 1` blocks ((2.5) `eq:variancematrix`), not the equal weights `1/5` of
the two-dimensional case; the definition below is the one of [DYYY25] read with the `d ≥ 3` `S`.
`unBadY_subset` proves that a weighted average of block QUE quantities
exceeds `θ` only if one block quantity does: the union bound is over the support of the weights, `≤ 2d + 1`
blocks (`unBadY_card_le`). -/

section BadY

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `M_{y,α}` for a vector `ψ = ψ_α`: `N ∑_x |ψ(x)|² S°_{xy}`, `S°_{xy} = S_xy - N⁻¹` (real). -/
def unMy (lam : ℝ) (ψ : Idx d L W → ℂ) (y : Idx d L W) : ℝ :=
  (((W * L) ^ d : ℕ) : ℝ) *
    ∑ x, ‖ψ x‖ ^ 2 * (svarF d L W lam x y - ((((W * L) ^ d : ℕ) : ℝ))⁻¹)

/-- **The bad event `𝓑(y)`**: there is an eigenvector `ψ_α` of `M` with
`|λ_α - E| ≤ N^{-1} W^{𝔡/3}` and `|M_{y,α}| ≥ W^{-𝔡/6}`.  It is used by `UNJak` and `UNUyw`: the eigenvector representation
of [DYYY25] is split on `𝓑` and `𝓑ᶜ`. -/
def UNBadY (lam 𝔡 E : ℝ) (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ), IsOrthoEigenbasis M μ ψ ∧
    ∃ α, |μ α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
      (W : ℝ) ^ (-(𝔡 / 6)) ≤ |unMy d L W lam (ψ α) y|

variable {d L W}

/-- `M_{y,α}` is the `S^{(B)}`-weighted average of the block QUE quantities
`(N/W^d)(∑_{x∈[b]} |ψ(x)|² - W^d/N)` (the identity behind the eigenvector representation of [DYYY25]), for a unit vector. -/
theorem unMy_eq (hL : 3 ≤ L) (lam : ℝ) (ψ : Idx d L W → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1)
    (y : Idx d L W) :
    unMy d L W lam ψ y = ∑ b : Zd d L, SBR d L lam b (split d L W y).1 *
      ((((W * L) ^ d : ℕ) : ℝ) / (W : ℝ) ^ d * (∑ x ∈ Iblk d L W b, ‖ψ x‖ ^ 2) - 1) := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
    have : 0 < (W * L) ^ d := pow_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne W))
      (Nat.pos_of_ne_zero (NeZero.ne L))) _
    exact_mod_cast this
  set N : ℝ := (((W * L) ^ d : ℕ) : ℝ) with hNdef
  set a := (split d L W y).1 with ha
  have hrow : ∑ b : Zd d L, SBR d L lam b a = 1 := by
    simp_rw [SBR_comm _ a]
    exact sum_SBR_row hL a
  -- group the sum over `x` by the block of `x`
  have hgroup : ∑ x, ‖ψ x‖ ^ 2 * svarF d L W lam x y =
      ((W : ℝ) ^ d)⁻¹ * ∑ b : Zd d L, SBR d L lam b a * ∑ x ∈ Iblk d L W b, ‖ψ x‖ ^ 2 := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x => (split d L W x).1)
      (fun x => ‖ψ x‖ ^ 2 * svarF d L W lam x y), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxb : (split d L W x).1 = b := (Finset.mem_filter.mp hx).2
    simp only [svarF, ← ha, hxb]
    ring
  unfold unMy
  have h1 : ∑ x, ‖ψ x‖ ^ 2 * N⁻¹ = N⁻¹ := by rw [← Finset.sum_mul, hψ, one_mul]
  have e1 : ∑ x, ‖ψ x‖ ^ 2 * (svarF d L W lam x y - N⁻¹) =
      ∑ x, ‖ψ x‖ ^ 2 * svarF d L W lam x y - N⁻¹ := by
    have : ∀ x, ‖ψ x‖ ^ 2 * (svarF d L W lam x y - N⁻¹) =
        ‖ψ x‖ ^ 2 * svarF d L W lam x y - ‖ψ x‖ ^ 2 * N⁻¹ := fun x => mul_sub _ _ _
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_sub_distrib, h1]
  have e2 : ∑ b : Zd d L, SBR d L lam b a *
        (N / (W : ℝ) ^ d * (∑ x ∈ Iblk d L W b, ‖ψ x‖ ^ 2) - 1) =
      N / (W : ℝ) ^ d * ∑ b : Zd d L, SBR d L lam b a * ∑ x ∈ Iblk d L W b, ‖ψ x‖ ^ 2 - 1 := by
    have : ∀ b : Zd d L, SBR d L lam b a * (N / (W : ℝ) ^ d * (∑ x ∈ Iblk d L W b, ‖ψ x‖ ^ 2) - 1) =
        N / (W : ℝ) ^ d * (SBR d L lam b a * ∑ x ∈ Iblk d L W b, ‖ψ x‖ ^ 2) - SBR d L lam b a := by
      intro b; ring
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, hrow, ← Finset.mul_sum]
  rw [e1, hgroup, e2]
  field_simp
  rw [hNdef]

/-- **`𝓑(y)` is contained in the union of the block QUE bad events over the support of the weights**
(the proof of Theorem 2.4: "applying (2.18) `Meq:QUE` with `ε₀ = 𝔡/3` and `c = 𝔡/6`"): a weighted average, with weights
`SBR b a ≥ 0` summing to `1`, of the numbers `u_b = (N/W^d) |∑_{x∈[b]} |ψ|² - W^d/N|`-type quantities has
modulus `≥ W^{-𝔡/6}` only if some `u_b` with positive weight has; and the window of `𝓑(y)` is inside
`𝓘_E(𝔡/3)` (`un_window_sub`, needs (2.10) `eq:WO`). -/
theorem unBadY_subset (hL : 3 ≤ L) {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (y : Idx d L W)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (h : UNBadY d L W lam 𝔡 E y M) :
    ∃ b : Zd d L, SBR d L lam b (split d L W y).1 ≠ 0 ∧
      queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b M := by
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
  have hrow : ∑ b : Zd d L, SBR d L lam b a = 1 := by
    simp_rw [SBR_comm _ a]
    exact sum_SBR_row hL a
  have hwnn : ∀ b, 0 ≤ SBR d L lam b a := fun b => sbKernelR_nonneg d L lam _
  have hM := unMy_eq hL lam (ψ α) hnorm y
  have hθ' : (W : ℝ) ^ (-(𝔡 / 6)) ≤ |∑ b, SBR d L lam b a * u b| := by rw [← hM]; exact hθ
  by_contra hcon
  push Not at hcon
  -- every block of positive weight has `|u b| < θ`
  have hlt : ∀ b, SBR d L lam b a ≠ 0 → |u b| < (W : ℝ) ^ (-(𝔡 / 6)) := by
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
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, SBR d L lam b₀ a ≠ 0 := by
    by_contra h0; push Not at h0
    simp [h0] at hrow
  have hsum : ∑ b, SBR d L lam b a * |u b| < ∑ b, SBR d L lam b a * (W : ℝ) ^ (-(𝔡 / 6)) := by
    refine Finset.sum_lt_sum (fun b _ => ?_) ⟨b₀, Finset.mem_univ _, ?_⟩
    · by_cases hz : SBR d L lam b a = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hlt b hz).le (hwnn b)
    · exact mul_lt_mul_of_pos_left (hlt b₀ hb₀) (lt_of_le_of_ne (hwnn b₀) (Ne.symm hb₀))
  have habs : |∑ b, SBR d L lam b a * u b| ≤ ∑ b, SBR d L lam b a * |u b| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [abs_mul, abs_of_nonneg (hwnn b)]
  rw [← Finset.sum_mul, hrow, one_mul] at hsum
  linarith

end BadY

/-! ### 5c. The union bound: `2d + 1` blocks -/

section BadYProb

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The weights `SBR b a` of the block average `M_{y,α}` are supported on `b - a ∈ {0} ∪ {|x| = 1}`, which
has `2d + 1` points for `L ≥ 3` ((2.5) `eq:variancematrix`; `flucVanish_card_sbSupport` is the same count). -/
theorem unBadY_card_le (hL : 3 ≤ L) (lam : ℝ) (a : Zd d L) :
    (Finset.univ.filter fun b : Zd d L => SBR d L lam b a ≠ 0).card ≤ 2 * d + 1 := by
  classical
  have hT : (insert (0 : Zd d L) (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1)).card
      ≤ 2 * d + 1 := by
    refine (Finset.card_insert_le _ _).trans ?_
    rw [card_nbhd d L hL]
  refine le_trans (Finset.card_le_card_of_injOn (fun b => b - a) ?_ ?_) hT
  · intro b hb
    have hb' : SBR d L lam b a ≠ 0 := (Finset.mem_filter.mp hb).2
    simp only [SBR, Matrix.of_apply, sbKernelR] at hb'
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_filter]
    by_contra hcon
    push Not at hcon
    apply hb'
    simp [hcon.1, hcon.2 (Finset.mem_univ _)]
  · intro b₁ _ b₂ _ h
    exact sub_left_injective h

/-- **`ℙ(𝓑(y)) ≤ (2d+1) · p`**: if (2.18) `Meq:QUE` at `(ε₀, c) = (𝔡/3, 𝔡/6)` holds with bound `p` at every
block for the random matrix `Mf`, then the bad event `𝓑(y)` has probability `≤ (2d+1) p`.  The constant
`2d + 1` is absorbed in `W^τ` by the users of this bound, giving `W^{-𝔡/15+τ}` of the paper. -/
theorem unBadY_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (hL : 3 ≤ L)
    {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (y : Idx d L W)
    (Mf : Ω → Matrix (Idx d L W) (Idx d L W) ℂ) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, μ {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} ≤ p) :
    μ {ω | UNBadY d L W lam 𝔡 E y (Mf ω)} ≤ ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
  classical
  set a := (split d L W y).1 with ha
  set s := Finset.univ.filter fun b : Zd d L => SBR d L lam b a ≠ 0 with hs
  have hsub : {ω | UNBadY d L W lam 𝔡 E y (Mf ω)} ⊆
      ⋃ b ∈ s, {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} := by
    intro ω hω
    obtain ⟨b, hb0, hb⟩ := unBadY_subset hL hW h𝔡 hlam y (Mf ω) hω
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩) hb
  calc μ {ω | UNBadY d L W lam 𝔡 E y (Mf ω)}
      ≤ μ (⋃ b ∈ s, {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Mf ω)}) := measure_mono hsub
    _ ≤ ∑ b ∈ s, μ {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _b ∈ s, p := Finset.sum_le_sum fun b _ => hp b
    _ = (s.card : ℝ≥0∞) * p := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
        gcongr
        exact_mod_cast unBadY_card_le hL lam a

end BadYProb

/-! ## Examples: a test function and the statement `UNEMCTE2` at `n_f = 0` -/

namespace UNInst

open RBM.Gauss.SizesInst

/-- A smooth bump on `Fin 1 → ℝ`, `1` on `‖x‖ ≤ 1`, supported in `‖x‖ < 2`: a nonconstant test function. -/
def bump : ContDiffBump (0 : Fin 1 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bump_testFun : IsTestFun (bump : (Fin 1 → ℝ) → ℝ) :=
  ⟨bump.contDiff, bump.hasCompactSupport⟩

/-- `UNEMCTE2` at `n_f = 0` holds (both products are `1`); `0 ≤ B` is needed: without it the statement would claim
`0 ≤ N^ε N^{…} B` for every `B`, which is false. -/

theorem un_emcte2_zero {d : ℕ} (sz : Sizes d) (E τU Cn : ℝ) : UNEMCTE2 sz E 0 τU Cn := by
  intro C₀ ε _ _
  refine Eventually.of_forall fun n z _ B hB _ _ t _ _ => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero]
  have : 0 ≤ Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) := by positivity
  exact mul_nonneg this hB

end UNInst

end RBM.Univ
