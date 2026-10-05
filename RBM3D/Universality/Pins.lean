/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.Sizes
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.SemicircleIntegral
import RBM3D.Gauss.BlockAnderson
import RBM3D.Induction.Defs
import RBM3D.Propagator.Gap
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# `RBM3D.Universality.Pins` (UN-01): the pins of bulk universality `Thm: B_Univ` at `d ≥ 3`

Promotion of the UN-D1 design probe of ticket T2162 (`RBM3D/Probe/T2162Pins.lean` at `73b451c`) to
the library (ticket T2174; statements unchanged).  Paper:
arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`): `Thm: B_Univ`
`1_2:444-460`, its proof `1_2:566-581`, `(Meq:QUE)` `1_2:407-419`.  RBM2D sources are cited as
`RBM2D/<file>:<line>` at commit `c9a24cf` (read-only; every statement below is a port that was
re-checked against this paper).

Namespace `RBM.Univ`; ported vocabulary keeps the RBM2D name, every pin is prefixed `UN`.
Registry class (DECISIONS §16, §20) of each pin is in its docstring: **borrowed** (only `UNL32`),
**owed** (a result of the paper that other tickets prove), **structural** (a condition on data
that deterministic lemmas take as a hypothesis).

Sections: 1 vocabulary and the abstract model; 2 the endpoint `UNBUniv` and its dilated form;
3 the external input `UNL32` and its limit computation; 4 the internal pins (local law, density,
the `𝐇_t` claims, Claim `(417)`, `(jaklsdufowe)`, `(uywy7723r3rf)`, the comparison);
5 the bad event `𝓑(y)` and the exponents of `1_2:570-578`; 6 the rows and the composition
theorems; 7 compiled nonempty instances at `d = 3` and extreme inputs.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

/-! ## 1. Vocabulary -/

section Vocab

/-- `(μ, ψ)` is an orthonormal eigenbasis of `H`.  `RBM2D/Endpoints.lean:56` (`IsOrthoEigenbasis`). -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k

/-- GUE coordinate variances at dimension `N = (W L)^d`: `1/N` on the diagonal and `1/(2N)` for each
real coordinate off the diagonal, so `E|h_ij|² = 1/N`.  `RBM2D/Endpoints.lean:190` (`gueVar`),
`(W L)^2` becomes `(W L)^d`. -/
def gueVar (d L W : ℕ) (c : CoordF d L W) : ℝ≥0 :=
  if c.1 = c.2.1 then ((((W * L) ^ d : ℕ) : ℝ≥0))⁻¹ else ((2 * ((W * L) ^ d : ℕ) : ℝ≥0))⁻¹

/-- The GUE law on the coordinate space `Ω d L W`: `Xmat d L W` under it is an `N × N` GUE matrix with
`E|h_ij|² = 1/N`, `N = (W L)^d` (the law of `𝐇_∞`, `1_2:566-581` as in `[DYYY25]` Thm 2.6).
`RBM2D/Endpoints.lean:196` (`gueP`). -/
def gueP (d L W : ℕ) [NeZero L] [NeZero W] : Measure (Ω d L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueVar d L W c)

instance isProbabilityMeasure_gueP (d L W : ℕ) [NeZero L] [NeZero W] :
    IsProbabilityMeasure (gueP d L W) := by
  unfold gueP; infer_instance

/-- The symmetric `k`-point functional `N^k (N-k)!/N! Σ_{i₁,…,i_k distinct} 𝒪(N(λ_{i₁}-E), …)`: its
expectation is `∫ 𝒪(α) p^{(k)}(E + α/N) dα` (`p^{(k)}` of `1_2:446-449` integrates to `1`; paper-delta
T2001h).  `RBM2D/Endpoints.lean:202` (`kPoint`). -/
def kPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
    ∑ f : Fin k ↪ ι, O (fun j => (Fintype.card ι : ℝ) * (lam (f j) - E))

/-- `ρ_sc(E) = (2π)⁻¹ √(4 - E²)`; `π⁻¹ Im mE E` (`RBM.mE`, `Defs/Semicircle.lean:38`).
`RBM2D/Universality/Pins.lean:139` (`rhoSC`). -/
def rhoSC (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / (2 * Real.pi)

/-- `m(z) = N⁻¹ tr (M - z)⁻¹` for a matrix `M` on a finite index set (`Gres`, `Loop/GLoopFlow.lean:74`,
is the resolvent).  `RBM2D/Universality/Pins.lean:72` (`stieltjesN`). -/
def stieltjesN {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * (Gres M z true).trace

/-- A test function: `𝒪 ∈ C_c^∞(ℝ^k)` (smoothness index `∞`, not `ω`). -/
def IsTestFun {k : ℕ} (O : (Fin k → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O ∧ HasCompactSupport O

end Vocab

/-! ### The abstract model: a measure on the common sample space and a matrix family

The band model and the block Anderson model (`RBM3D/Gauss/BlockAnderson.lean`) are both a measurable
family of Hermitian matrices on `Sizes.SeqΩ sz`; the core pin `UNCore` is stated for such a model, so
that BA-D1 consumes it with the data `m`, `ρ_N` of `(self_m)`.  (T2162 interface decision, report 4.) -/

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

/-- The band model of `(bandcw0)`: law `seqP sz`, matrix `seqXmat sz n`. -/
def UNModel.band {d : ℕ} (sz : Sizes d) : UNModel sz where
  μ := Sizes.seqP sz
  prob := inferInstance
  H := Sizes.seqXmat sz
  herm := Sizes.seqXmat_isHermitian sz
  meas := fun n i j => (measurable_Xentry d (sz.L n) (sz.W n) i j).comp (measurable_slice sz n)

/-- The block Anderson model `(eq:H_blocka)`: `H = V + ilambda Ψ` with `V` the model of
`sz.withLam 0` (`Sizes.seqHBA`, `Gauss/BlockAnderson.lean:96`). -/
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

/-- The OU time `t* = N^{-1+τ_U}` at size `n` (`1_2:566-581` as `[DYYY25]` Thm 2.6; RBM2D paper `1-2:341`).
`RBM2D/Universality/Pins.lean:109` (`ouTStar`). -/
def ouTStar (sz : Sizes d) (τU : ℝ) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ) ^ (-1 + τU)

/-- The OU carrier at size `n`: the model and an independent GUE.  `RBM2D/Universality/Pins.lean:53`. -/
def ouP (M : UNModel sz) (n : ℕ) : Measure (Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :=
  M.μ.prod (gueP d (sz.L n) (sz.W n))

/-- The OU marginal `𝐇_t = e^{-t/2} H + √(1 - e^{-t}) H'`, `H'` an independent GUE
(`E|h'_ij|² = 1/N`).  `RBM2D/Universality/Pins.lean:59` (`ouMat`). -/
def ouMat (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Real.exp (-t / 2) • M.H n ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2

theorem ouMat_isHermitian (M : UNModel sz) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : (ouMat M n t ω).IsHermitian :=
  ((M.herm n ω.1).smul (IsSelfAdjoint.all _)).add
    ((Xmat_isHermitian d _ _ ω.2).smul (IsSelfAdjoint.all _))

/-- `𝐇_0 = H` (RBM2D paper `1-2:339`). -/
theorem ouMat_zero (M : UNModel sz) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat M n 0 ω = M.H n ω.1 := by
  simp [ouMat]

end OU

/-! ## 2. The endpoint `Thm: B_Univ` and its dilated form -/

section Endpoint

/-- **Pin `UNBUniv` = `Thm: B_Univ`, `(eq:universality)`** (`1_2:444-460`), band model, in the form to
freeze (consumer: the MA freeze `RBM3D/Endpoints.lean`; compare `T2001_BUniv`,
`bd95cc9:RBM3D/Probe/T2001Endpoints.lean:230-238`, and RBM2D `BUniv`, `RBM2D/Endpoints.lean:209`).
Constants `(d, 𝔠, 𝔡)` before the sequence `sz` (which carries `ilambda` as the sequence `sz.lam`);
`Admissible` is `W ≥ N^𝔠`, `(eq:WO)`, `N → ∞`, `0 < 𝔠, 𝔡` (`Defs/Sizes.lean`); `k ≥ 1` fixed,
`|E| ≤ 2 - κ`, `𝒪 ∈ C_c^∞(ℝ^k)`; the `N^{-1}` scale is the one of `kPoint`.  Registry class: **owed**
(the paper's Theorem 2.4, proved by the UN tickets from `UNL32`). Consumer (RBM2D `c9a24cf`): `Main/BUnivHolds.lean:32` (`bUniv_holds`) and the MA freeze `RBM3D/Endpoints.lean`. -/
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

/-- **The dilated universality statement** at the density sequence `ρ` and the GUE energy `E'`
(DECISIONS §11): in the normalisation `α = ρ β`,
`∫ 𝒪(α)[ρ_n^{-k} p_H^{(k)}(E + α/(Nρ_n)) - ρ_sc(E')^{-k} p_GUE^{(k)}(E' + α/(Nρ_sc(E')))] dα → 0`
is `E kPoint k 𝒪(ρ_n ·) E (λ(H)) - E kPoint k 𝒪(ρ_sc(E') ·) E' (λ(GUE)) → 0`
(the change of variables is the one of `L32`, `RBM2D/Universality/Pins.lean:170-174`).  The band model
is `ρ_n = ρ_sc(E)`, `E' = E` (`unBUniv_diff_eq`); the block Anderson model has `ρ_n = ρ_N(E)`. Consumer (RBM2D `c9a24cf`): `Universality/GUETranslation.lean:827` (conclusion of `L32`); here `UNCore`, `un_bUniv_of_rows`. -/
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

/-! ## 3. The external input `UNL32` ([32] Thm 2.2, DECISIONS §5) and its limit computation -/

section L32

/-- `m_V(z) = N⁻¹ ∑_i (v_i - z)⁻¹` ([32] (2.2)).  `RBM2D/Universality/Pins.lean:114`. -/
def mV {ι : Type*} [Fintype ι] (v : ι → ℝ) (z : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z)⁻¹

/-- [32] Definition 2.1: `V = diag v` is `(g, G)`-regular, (2.2) and (2.3).
`RBM2D/Universality/Pins.lean:118`. -/
def IsRegular32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (g G c C CV : ℝ) : Prop :=
  (∀ E η : ℝ, |E| ≤ G → g ≤ η → η ≤ 10 →
      c ≤ (mV v ⟨E, η⟩).im ∧ (mV v ⟨E, η⟩).im ≤ C) ∧
    ∀ i, |v i| ≤ (Fintype.card ι : ℝ) ^ CV

/-- [32] (2.5): `m` solves the free-convolution equation on the upper half plane, `Im m > 0`.
`RBM2D/Universality/Pins.lean:124`. -/
def IsFreeConv32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧
    m z = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹

/-- [32] (2.1) with GOE → GUE: `V + √t H'`, `H' = Xmat` under `gueP` (`E|h'_ij|² = 1/N`).
`RBM2D/Universality/Pins.lean:129`. -/
def dbmMat (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ) (t : ℝ) (ω : Ω d L W) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.diagonal (fun i => (v i : ℂ)) + Real.sqrt t • Xmat d L W ω

theorem dbmMat_isHermitian (d L W : ℕ) [NeZero L] [NeZero W] (v : Idx d L W → ℝ) (t : ℝ)
    (ω : Ω d L W) : (dbmMat d L W v t ω).IsHermitian :=
  (Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).add
    ((Xmat_isHermitian d L W ω).smul (IsSelfAdjoint.all _))

/-- **Pin `UNL32`: [32] (`LANDON20191137`, Landon–Sosoe–Yau) Theorem 2.2, complex Hermitian (GUE)
version, unit density**, as stated in arXiv:1609.09011v4 (latest version at the time of T2162, `arxiv.org/abs/1609.09011` of 2026-10-04; premises and conclusion re-checked against the v4 text, report b.3; its (2.9) carries the factors `ρ_fc^{-k}`,
`ρ_sc^{-k}` that earlier versions omitted: RBM1D paper-delta T1654a; the Remark after Theorem 2.2
covers the complex Hermitian case; DECISIONS §5).  Used once, at `(1infyuniv)`; the proof step is
`1_2:566-581` as `[DYYY25]` Thm 2.6.
* Premises: [32] Def 2.1 `((2.2), (2.3))`, `(2.5)–(2.6)`, `(2.8)`, `|E| ≤ qG`, eventually along a
  size sequence with `size n → ∞`; the matrix is `diag v + √t · GUE_N`, `N = (W L)^d`.  The premises
  involve only the size `N` (not `d`, `W`, `L`); `d` enters through the carrier `Idx d L W` of the
  `N × N` matrix.
* Conclusion: (2.9) of v4 with the factors `ρ_fc^{-k}`, `ρ_sc^{-k}`, by `α = ρβ` the test function
  dilated by each side's own density, in the eigenvalue-sum form `kPoint`; the rate `C N^{-κ}` is
  weakened to `→ 0`.
* `size n → ∞` is a hypothesis (for a constant sequence the conclusion would equate two finite-`N`
  quantities).  The limit computation of the premises at the `d ≥ 3` parameters is
  `un_L32_arith` (arithmetic premises) and the pin `UNStep1Good` (regularity premises).
Port of `RBM2D/Universality/Pins.lean:156` (`L32`), `Sizes` → `Sizes d`, `3 ≤ d`.
Registry class: **borrowed** (the one external input, DECISIONS §5). Consumer (RBM2D `c9a24cf`): `Universality/GUETranslation.lean:827`. -/
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

/-- **The limit computation of the arithmetic premises of `UNL32`** at the OU time
`t = 1 - e^{-N^{-1+τ}}` of `1_2:566-581` (`t* = N^{-1+τ_U}`, `τ = τ_s`): with
`g = N^{-1+τ/4}`, `G = N^{-σ}`, `δ = σ = min(τ/4, (1-τ)/3)`, `q = 1/2`, `E = 0`, the six premises
`N^σ/N ≤ g`, `g ≤ N^{-σ}`, `G ≤ N^{-σ}`, `g N^σ ≤ t`, `t ≤ N^{-σ} G²`, `|E| ≤ qG` hold as soon as
`N ≥ 1` and `N^{τ/2} ≥ 2` (i.e. `N ≥ 2^{2/τ}`).  They involve only `N` and `τ`: nothing here depends on
`d`, `W`, `L`, `ilambda` (RBM2D `Universality/GUETranslation.lean:827`: same data at `d = 2`). -/
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

/-! ## 4. The internal pins -/

section Pins

variable {d : ℕ}

/-- The one scale `N = (W L)^d = sz.size n` as a real number (`1_2:263`). -/
abbrev Nsz (sz : Sizes d) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ)

/-! ### 4.1 The consumed inputs: the shapes UN takes from MA and ST -/

/-- `𝓘_E(ε₀) = {x : |x - E| ≤ W^{-ε₀} (ilambda W^{d/2} / N)}` of `(eq:defIE)` (`1_2:409`); the footnote
`1_2:372` replaces `ilambda` by `ilambda ∧ 1`: only the lower bound `W^{-ε₀}(lam ∧ 1) W^{d/2} ≥ W^{2𝔡/3}`
is used here (`un_window_sub`), which holds for both readings.  `T2001_QUE` (`queWindow`,
`bd95cc9:RBM3D/Probe/T2001Endpoints.lean:170`) is this definition on `Vtx`. -/
def queWindow (d L W : ℕ) (lam ε₀ E x : ℝ) : Prop :=
  |x - E| ≤ (W : ℝ) ^ (-ε₀) * (lam * (W : ℝ) ^ ((d : ℝ) / 2) / (((W * L) ^ d : ℕ) : ℝ))

/-- The probability bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}` of `(Meq:QUE)` (`1_2:416`). -/
def queBound (W : ℕ) (𝔡 ε₀ c τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((W : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ))

/-- The failure event of `(Meq:QUE)` (`1_2:414-416`) at the block `a` for an arbitrary Hermitian
matrix `M` on the fine lattice: some orthonormal eigenbasis has `i, j` in the window `𝓘_E(ε₀)` with
`|∑_{x∈[a]} conj ψ_i(x) ψ_j(x) - (W^d/N) δ_ij| ≥ W^{d-c}/N`.  `T2001_QUE` (`QueBad`, `bd95cc9:RBM3D/Probe/T2001Endpoints.lean:175`) on `Idx`
instead of `Vtx`; RBM2D `queBadMat` (`Universality/Pins.lean:79`) is the `d = 2` form with the older
QUE of `[DYYY25]`. -/
def queBadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (a : Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ i j, queWindow d L W lam ε₀ E (μ i) ∧ queWindow d L W lam ε₀ E (μ j) ∧
      (W : ℝ) ^ ((d : ℝ) - c) / (((W * L) ^ d : ℕ) : ℝ) ≤
        ‖(∑ x ∈ Iblk d L W a, star (ψ i x) * ψ j x) -
            ((W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ)) * (if i = j then 1 else 0)‖

/-- **Consumed from MA: `(Meq:QUE)`** (`1_2:407-417`, `MR:QUE`), band model, for the parameters
`ε₀ ∈ (0, 𝔡/2)`, `0 < c < ε₀ ∧ 𝔡/5`, any `τ > 0`, eventually, uniformly in `|E| ≤ 2 - κ` and the block `a`
(first half of `T2001_QUE`, `bd95cc9:RBM3D/Probe/T2001Endpoints.lean:195`; `(Meq:QUE2)` is not consumed).  Producer: "MA pin to be frozen" (the
endpoint `MR:QUE`).  Registry class: **owed** (MA). Consumer (RBM2D `c9a24cf`): `Universality/Jak.lean:732` (`measure_bad_le_of_queBadMat`, through `OUQUE`); `OURow` itself does not use it (`ZeroModeProfile.lean:712`). -/
def UNQueBand : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
        Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (Sizes.seqXmat sz n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- **Consumed from MA: `(G_bound_ave)`** (`1_2:391-399`): `∩_z` inside the probability (T2001b),
`|W^{-d} ∑_{x∈[a]} G_xx(z) - m(z)| ≤ W^τ B_{η,0}` for every block, `W^{-d}B_{η,0} = sz.Bctl n (1-η)`
(`Defs/Sizes.lean:214`, `(eq:calBetaK)` at `K = 0`), `m = msc` (`msc_eq_integral`).  (The entrywise half
`(G_bound)` is not consumed.)  Producer: "MA pin to be frozen" (`T2001_locSC` second half, `LocBad2`, `bd95cc9:RBM3D/Probe/T2001Endpoints.lean:147-166`).
Registry class: **owed** (MA). Consumer (RBM2D `c9a24cf`): `Universality/Step1RegularityA.lean:304, 809` (`Step1RegularityA_tracial_le`). -/
def UNLocAvgBand : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ∃ z : ℂ, sz.locDomain κ ε n z ∧ ∃ a : Zd d (sz.L n),
          ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
            ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
                Gres (Sizes.seqXmat sz n ω) z true x x - msc z‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **Consumed from ST-6/MA: the `G`-loop outputs along `z`-sequences** (`ML:GLoop`, `ML:GLoop_expec`,
`ML:GtLocal`, `1_2:1193-1226`, "fix any `z ∈ 𝐃_{κ,ε}` ... uniformly in `t ∈ [0, t₀]`"): the conclusions
of the merged `STMainInd` (`Induction/Defs.lean:294`) at every time sequence `0 ≤ t_n ≤ lemT z_n`:
`STLK`, `STLmax`, `STDecay`, `STExp2`, `STLocalEntry`.  RBM2D counterpart: `P7Out`, `P7ExpOut`
(`Universality/Pins.lean:238, 250`: all bulk energy sequences with `1 - t ≥ N^{-1+τ}`; the bridge
`(E', t) ↔ (z, t ≤ lemT z)` is `RBM2D/Universality/GUEPhase/RandomLayerA.lean`, `RandomLayer_lem28`).
Producer: "MA/ST-6 pin to be frozen".  Registry class: **owed** (ST-6). Consumer (RBM2D `c9a24cf`): `Universality/GUEPhase/RandomLayerA.lean:738`, `GUEPhase/Eq729B.lean:1613`. -/
def UNMLOut (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
        STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t

/-! ### 4.2 The local law and the density: the data of the core -/

/-- **Tracial local law of a model at the Stieltjes transforms `m n`**, in a window `|Re z - E| ≤ δ`
around the energy: with probability `≥ 1 - N^{-D}`, simultaneously for all `z` with
`N^{-1+ε} ≤ Im z ≤ 1`, `|m_N(z) - m_n(z)| ≤ W^τ B_{η,0}`, `W^{-d}B_{η,0} = sz.Bctl n (1-η)`
(`(eq:calBetaK)`).  Band model: `m n = msc`, a consequence of `UNLocAvgBand` (average over the `L^d`
blocks; `δ ≤ κ/2`); BA model: BA-D1 supplies it with `m(z, λ_n)` of `(self_m)`.  RBM2D:
`Step1RegularityA.lean`, `Step1LocalEvent` (`:748`), there with a grid and `Meta`.  Registry class:
**owed** (MA/BA). Consumer (RBM2D `c9a24cf`): `Universality/Step1RegularityB.lean:339`. -/
def UNTrLocal (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) < ‖stieltjesN (M.H n ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **The regularity of the density used by the comparison** (DECISIONS §11: "lower bound of
`ρ_N(E)`, regularity of `E ↦ ρ_N(E)`"): near `E`, in the window `|x - E| ≤ δ`, `0 < η ≤ 10`,
`c ≤ Im m_n(x + iη) ≤ C` (the bounds (2.2) of [32] Def 2.1 for the free-convolution input), `x ↦ Im m_n(x+iη)`
is `Lp`-Lipschitz uniformly in `η` (so `ρ_n` is `Lp`-Lipschitz and the free convolution with a
semicircle of variance `t* ≪ 1` has density within `O(t*)` of `ρ_n`), and `ρ_n = π⁻¹ Im m_n(E + i0)`.
Band model: `m n = msc`, `ρ_n = ρ_sc(E)`: proved at `E = 0`, `δ = 1/2` (`un_dens_msc_zero`), the density-level
facts are `un_rhoSC_lower`, `un_rhoSC_lip`; every bulk `E` is the row `UNDensBandRow`.  BA: BA-D1 (the bulk
condition of `T2001d/l` is this hypothesis).
Registry class: **structural** (a condition on the deterministic data `m`). Consumer (RBM2D `c9a24cf`): `Universality/Step1RegularityB.lean:228, 470` (`Step1RegularityB_msc_im_ge`). -/
def UNDens (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ c C Lp : ℝ, 0 < c ∧ 0 < C ∧ 0 < Lp ∧ ∀ᶠ n in atTop,
    (∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 →
      c ≤ (m n ⟨x, η⟩).im ∧ (m n ⟨x, η⟩).im ≤ C) ∧
    (∀ x y η : ℝ, |x - E| ≤ δ → |y - E| ≤ δ → 0 < η → η ≤ 10 →
      |(m n ⟨x, η⟩).im - (m n ⟨y, η⟩).im| ≤ Lp * |x - y|) ∧
    Tendsto (fun η : ℝ => (m n ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))

/-- **Polynomial bound on the spectrum of the model** (`(2.3)` of [32] Def 2.1, `‖V‖ ≤ N^{C_V}`):
for every `D > 0`, eventually, with probability `≥ 1 - N^{-D}` all eigenvalues of `H` are `≤ N^{CV₀}` in modulus.
It cannot be derived from `UNTrLocal`: a deterministic diagonal model with the semicircle quantiles plus one
eigenvalue `N^{10}` has the local law and the regularity of the density but violates `(2.3)` (T2162 extreme-input
finding; not compiled).  Band model: `CV₀ = 1` from the Gaussian entry tails `|h_xy| ≤ 1` (RBM2D
`Step1RegularityA.lean`, entry event; `|λ| ≤ N`); block Anderson: `‖V‖ + ilambda ‖Ψ‖`.
Registry class: **owed** (band: UN-10; BA: BA-D1). Consumer (RBM2D `c9a24cf`): `Universality/Step1RegularityB.lean:483, 637` (`Step1RegularityB_eigenvalue_le`). -/
def UNNormBound (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-! ### 4.3 The weak GUE local law (internal) -/

/-- **Pin `UNGUELocal`**: a weak averaged bulk local law of the `N × N` GUE, `N = (W L)^d`:
`|m_N(z) - m_sc(z)| ≤ N^τ (N Im z)^{-1/2}` for `N^{-1+τ} ≤ Im z ≤ 10`, `|Re z| ≤ 2 - κ`, union over `z`
inside the probability.  Not in the paper (RBM2D `Pins.lean:184`: the RBM2D paper cites only `MR:locSC` and [32] there; `1_2:566-581` cites neither);
needed to move the GUE statistics from energy `0` (where [32] compares) to `E'` (RBM1D
`gue_translation'`; RBM2D `Pins.lean:179-197`, paper-delta T2162b).  Dimension-free (only `N`).
Registry class: **owed** (UN: RBM2D `GUELocalSchur`, `GUELocalBootstrap`). Consumer (RBM2D `c9a24cf`): `Universality/GUETranslation.lean:60`. -/
def UNGUELocal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    gueP d (sz.L n) (sz.W n) {ω | ∃ z : ℂ, |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10 ∧
        Nsz sz n ^ τ / Real.sqrt (Nsz sz n * z.im) <
          ‖stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z - msc z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-! ### 4.4 The claim `(417)`, the comparison, the two limits -/

/-- The spectral window of the Claim (RBM2D paper `1-2:352`): `|E_j - E| ≤ C₀/N`,
`N^{-1-τ_U} ≤ η_j ≤ N^{-1+τ_U}`.  `RBM2D/Universality/Pins.lean:259`. -/
def InWindow (sz : Sizes d) (E C₀ τU : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  |z.re - E| ≤ C₀ / Nsz sz n ∧ Nsz sz n ^ (-1 - τU) ≤ z.im ∧ z.im ≤ Nsz sz n ^ (-1 + τU)

/-- **Pin `UNClaim417`**: the Claim `(417)` (RBM2D paper `1-2:352-356`) for the OU path of a model: for `nf` factors,
`sup_{0≤t≤t*} |E ∏ Im m_t(z_i) - E ∏ Im m_{t*}(z_i)| ≤ N^{-c' + C_n τ_U}`, eventually, for every `C₀`.
`c'`, `C_n` are parameters (`c' = 𝔠𝔡/30` at the design point of target 3; RBM2D `𝔠/36`).
RBM2D `Universality/Pins.lean:267` (`Claim417`).  Registry class: **owed** (UN band; BA-D1 for BA). Consumer (RBM2D `c9a24cf`): `Universality/GreenCorr.lean:644`. -/
def UNClaim417 (sz : Sizes d) (M : UNModel sz) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∀ᶠ n in atTop, ∀ z : Fin nf → ℂ, (∀ i, InWindow sz E C₀ τU n (z i)) →
    ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
      |(∫ ω, ∏ i, (stieltjesN (ouMat M n t ω) (z i)).im ∂(ouP M n)) -
        ∫ ω, ∏ i, (stieltjesN (ouMat M n (ouTStar sz τU n) ω) (z i)).im ∂(ouP M n)| ≤
        Nsz sz n ^ (-c' + Cn * τU)

/-- `Claim417` for all `n_f`, for all small `τ_U`, at one exponent `c' > 0`. -/
def UNClaimAll (sz : Sizes d) (M : UNModel sz) (E : ℝ) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
    ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNClaim417 sz M E nf τU c' Cn

/-- The a priori bound at the level spacing (RBM1D `AprioriImM`): `E (Im m_0(E + i/N))^p ≤ N^ε`
eventually.  `RBM2D/Universality/Pins.lean:348`. Consumer (RBM2D `c9a24cf`): `Universality/GreenCorr.lean:693`. -/
def UNApriori (sz : Sizes d) (M : UNModel sz) (E : ℝ) : Prop :=
  ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∫ ω, (stieltjesN (ouMat M n 0 ω) ((E : ℂ) + ((Nsz sz n)⁻¹ : ℂ) * Complex.I)).im ^ p ∂(ouP M n) ≤
      Nsz sz n ^ ε

/-- **Pin `UNGreenCorr`**: the Green-function-to-correlation comparison (`1_2:566-581`: "Theorem 15.3 in
[25], Prop. 4.17 in [45], (2.23) in [YY_25]"; internal, DECISIONS §5).  If `(417)` holds for all
`n_f ≤ k` at `τ_U ≤ τ₀` and the a priori bound holds, the `k`-point functionals of `𝐇_0` and `𝐇_{t*}`
have the same limit, for the test function dilated by any sequence `r_n ∈ [a, b] ⊂ (0, ∞)` (eventually, DECISIONS §29 (4))
(T2162 interface decision: the band model needs `r_n ≡ ρ_sc(E)`, the block Anderson model has `r_n = ρ_N(E)`
varying; the smoothing proof of RBM1D `GreenCorrComparison.lean` is uniform over a `C^∞`-bounded family;
`r ≡ 1` is RBM2D `GreenCorr`, `Universality/Pins.lean:359`).  `τ₀` depends on `E, k, c', C_n` only.
Registry class: **owed** (UN, model-independent). Consumer (RBM2D `c9a24cf`): `Universality/UnivMain.lean:449, 514`. -/
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

/-- **`(1infyuniv)`** (RBM2D paper `1-2:344`) at `τ_U`: the `𝐇_{t*}` functional, dilated by `ρ_n`, against the
GUE functional at energy `E'` dilated by `ρ_sc(E')`.  RBM2D `Pins.lean:375` (`Infty1`). Consumer (RBM2D `c9a24cf`): `Universality/GUETranslation.lean:1151` (`Infty1Row`). -/
def UNInfty1 (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E
        (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)) -
    (∫ ω, kPoint k (fun α => O (rhoSC E' • α)) E'
        (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
    atTop (𝓝 0)

/-- **`(univ-main)`** (RBM2D paper `1-2:345`) at `τ_U`: the model `H = 𝐇_0` against `𝐇_{t*}`, both dilated by
`ρ_n`.  RBM2D `Pins.lean:386` (`UnivMain`). Consumer (RBM2D `c9a24cf`): `Universality/UnivMain.lean:449` (`univMainRow`). -/
def UNUnivMain (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E
        (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)))
    atTop (𝓝 0)

/-- The shifted, rescaled diagonal of Step 1: `v_i = e^{-t*/2} λ_i(H) - E₀`, `t* = N^{-1+τ_s}`.
`RBM2D/Universality/Step1RegularityB.lean:55` (`vOU`). -/
def vOU (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ sz) :
    Idx d (sz.L n) (sz.W n) → ℝ :=
  fun i => Real.exp (-(ouTStar sz τs n) / 2) * (M.herm n ω).eigenvalues i - E₀

/-- **Pin `UNStep1Good`**: the regularity event of Step 1 (`(1infyuniv)`, RBM2D paper `1-2:344`; RBM2D
`Step1RegularityB.lean:817` `step1Good_highProb`): with probability `≥ 1 - N^{-D}` the shifted diagonal
`v = e^{-t*/2} λ(H) - E` is `(g, G)`-regular with `g = N^{-1+τ_s/4}`, `G = N^{-min(τ_s/4,(1-τ_s)/3)}`,
`CV = CV₀ + 1` (from `UNNormBound sz M CV₀`: `|v_i| ≤ N^{CV₀} + |E| ≤ N^{CV₀+1}`; RBM2D `CV = 2`), and the free convolution with a semicircle of variance `1 - e^{-t*}` has a density at `0`
within `N^{-3τ_s/8}` of `ρ_n`.  **The range of `τ_s` is `τ_s ≤ 𝔠𝔡`** (RBM2D `τ_s ≤ 𝔠`): the local-law
floor is `W^{-d}(lam² + η)^{-1} ≤ W^{-2𝔡} ≤ N^{-2𝔠𝔡}` (`un_Bctl_le`, `un_step1_floor`).  The constants
`c, C` are produced from those of `UNDens`.  Registry class: **owed** (UN). Consumer (RBM2D `c9a24cf`): `Universality/Step1Band.lean:1037`. -/
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

/-! ## 4b. The band-model chain: the `𝐇_t` claims, `(EMCTE2)`, `(jaklsdufowe)`, `(uywy7723r3rf)`

These are specific to the band model (Gaussian, mean `0`, variance profile `S`): the generator identity of
the OU flow of `(EMCTE2)` has a first-order drift term for a model with a nonzero mean `ilambda Ψ` (block
Anderson), which BA-D1 must treat; the core `UNCore` therefore takes `UNClaimAll` (the Claim `(417)`) as its
input, and the band model produces it from the pins of this section (`un_claimAll_of_rows`). -/

section Band

variable {d : ℕ}

/-- `S°_{xy} = S_{xy} - N⁻¹` (RBM2D paper `1-2:372`), `S_xy = svarF` (`(eq:variancematrix)`).
`RBM2D/Universality/Pins.lean:87` (`Scirc`). -/
def scirc (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (x y : Idx d L W) : ℂ :=
  ((svarF d L W lam x y : ℝ) : ℂ) - ((((W * L) ^ d : ℕ) : ℂ))⁻¹

/-- `L_{1,t}(z)` of the RBM2D paper `1-2:371-376` at the matrix `M = 𝐇_t`; `G ∈ {R, R^*}` is `Gres M z b`
(`Gres M z false = (M - z̄)⁻¹ = R^*` for Hermitian `M`).  `RBM2D/Universality/Pins.lean:94`. -/
def L1t (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool,
    ‖((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ a, ∑ b,
      (Gres M z b₁ * Gres M z b₁) a a * scirc d L W lam a b * Gres M z b₂ b b‖

/-- `L_{2,t}(z₁, z₂)` of the RBM2D paper `1-2:371-376` at the matrix `M = 𝐇_t`.  `RBM2D/Universality/Pins.lean:100`. -/
def L2t (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z₁ z₂ : ℂ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool,
    ‖(((((W * L) ^ d : ℕ) : ℂ))⁻¹) ^ 2 * ∑ a, ∑ b,
      (Gres M z₁ b₁ * Gres M z₁ b₁) a b * scirc d L W lam a b *
        (Gres M z₂ b₂ * Gres M z₂ b₂) b a‖

/-- **Pin `UNOUQUE`: the first `𝐇_t` claim** (RBM2D paper `1-2:362`, "details identical to Section 7.2 of
[YY_25]"; paper-delta T2162b): `(Meq:QUE)` holds for `𝐇_t`, uniformly in `t ∈ [0, t*]`,
`t* = N^{-1+τ_U}`, at the parameters `ε₀ = 𝔡/3`, `c = 𝔡/6` of `1_2:575-577`, for every `τ > 0`: the failure
probability is `≤ W^{-(2ε₀)∧(2𝔡/5)+2c+τ} = W^{-𝔡/15+τ}` (`un_que_exponent`).  `(Meq:QUE2)` for `𝐇_t`
has no consumer.  RBM2D `OUQUE` (`Universality/Pins.lean:206`: `τ = 𝔠/3`, bound `N^{-τ/6}`).
Registry class: **owed** (UN, `QUEFlow`/GUE phase). Consumer (RBM2D `c9a24cf`): `Universality/Jak.lean:904` (`jakRow`). -/
def UNOUQUE (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ τQ : ℝ, 0 < κ → 0 < τQ → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
      ouP (UNModel.band sz) n
          {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a
            (ouMat (UNModel.band sz) n t ω)} ≤
        queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ

/-- **Pin `UNOUDiag`: the second `𝐇_t` claim** (RBM2D paper `1-2:362`): for `t ∈ [0, t*]`, `|E| ≤ 2 - κ`,
`η = N^{-1+2τ_U}`: `max_x |(𝐑_t(E + iη))_{xx}| ≺ 1`, union over `x` inside `P`.  Delocalization of `𝐇_t`
(`|ψ_α(x)|² ≤ η Im 𝐑_xx`, `(eq:ukx)`).  RBM2D `OUDiag` (`Pins.lean:218`).  Registry class: **owed**. Consumer (RBM2D `c9a24cf`): `Universality/Jak.lean:904` (`jakRow`). -/
def UNOUDiag (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ ε D : ℝ, 0 < κ → 0 < ε → 0 < D → ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
    ∀ E : ℝ, |E| ≤ 2 - κ →
      ouP (UNModel.band sz) n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
          Nsz sz n ^ ε <
            ‖Gres (ouMat (UNModel.band sz) n t ω)
                ((E : ℂ) + ((Nsz sz n ^ (-1 + 2 * τU) : ℝ) : ℂ) * Complex.I) true x x‖} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))

/-- The two `𝐇_t` claims for all small `τ_U` (RBM2D paper `1-2:362`: "for `τ_U > 0` sufficiently small").
RBM2D `OUClaims` (`Pins.lean:229`). Consumer (RBM2D `c9a24cf`): `Universality/Jak.lean:904` (`jakRow`). -/
def UNOUClaims : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUE sz 𝔡 τU ∧ UNOUDiag sz τU

/-- **Pin `UNEMCTE2`** (RBM2D paper `1-2:364-369`: "argue as in Step 3 of the proof of Theorem 2.6 in [YY_25]"),
in the weighted form of RBM1D `eq225`: the left side of `(417)` is `≤ N^ε N^{-1+C_nτ_U}` times a bound `B` on
`E[(∏_{j≠u} Im m_s(z_j)) L_{1,s}(z_u)]` (all `u`) and on `E[(∏_{k∉{u,v}} Im m_s(z_k)) L_{2,s}(z_u,z_v)]`
(`u ≠ v`), `s ∈ [0, t*]`; `0 ≤ B` is needed (`n_f = 0`: RBM2D report extreme input E5; `un_emcte2_zero`).
The generator identity is exact for a centred Gaussian model: band only.  RBM2D `EMCTE2`
(`Pins.lean:288`).  Registry class: **owed** (UN: `OUGenerator`, `OUHessian`, `OUContraction`, `EMCTE2`). Consumer (RBM2D `c9a24cf`): `Universality/UnivMain.lean:362` (`UnivMain_claim417_of`). -/
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

/-- **Pin `UNJak`: `(jaklsdufowe)`, the `(2.22)` analogue** (RBM2D paper `1-2:381`; this paper `1_2:569` names "the proofs of equations (2.22) and (2.23)" of `[DYYY25]`): with the
exponent `c'` (design value `𝔠𝔡/30` at `d ≥ 3`, target 3), the slack `N^ε` and a weight
`∏_{j∈s} Im m_t(z_j)` for every `s`, `max_i max_y E[(∏_{j∈s} Im m_t(z_j)) |∑_x (G₁²(z_i))_{xx} S°_{xy}
(G₂(z_i))_{yy}|] ≤ N^{ε} N^{1-c'+Cτ_U}`, `t ∈ [0,t*]`.  The proof splits on the bad event `𝓑(y)` of
section 5 (`UNBadY`).  RBM2D `Jak` (`Pins.lean:313`).  Registry class: **owed** (UN:
`JakSpectral`, `JakKernel`, `Jak`). Consumer (RBM2D `c9a24cf`): `Universality/UnivMain.lean:362`. -/
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

/-- **Pin `UNUyw`: `(uywy7723r3rf)`, the `(2.23)` analogue** (RBM2D paper `1-2:382`): the same with `N^{2-c'+Cτ_U}`
and the pair `i ≠ j`.  RBM2D `Uyw` (`Pins.lean:331`).  Registry class: **owed**. Consumer (RBM2D `c9a24cf`): `Universality/UnivMain.lean:362`. -/
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

/-! ## 6. The rows and the composition theorems -/

section Rows

/-- **Row `UNInfty1Row`**: `(1infyuniv)` for every `τ_U ∈ (0, τ₁]`, `τ₁` depending on `𝔠, 𝔡, k, E, E', O`,
from `UNL32`, the weak GUE local law, the density and the local law of the model (conditioning on `H`, GUE
unitary invariance, `UNStep1Good`, dilation `ρ_fc → ρ_n` by Lipschitz dependence, GUE translation from
energy `0` to `E'`).  RBM2D `Infty1Row` (`Pins.lean:438`, amended there for `τ_s ≤ 𝔠`).  Registry class:
**owed** (UN: `Step1Cond`, `Step1Band`, `Step1Regularity*`, `GUEInvariance`, `GUETranslation`,
`FreeConv*`, `GUELocal*`). Consumer (RBM2D `c9a24cf`): `Main/BUniv.lean:42` (`bUniv_of_rows`, `Pins.lean:526`). -/
def UNInfty1Row : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          ∀ E' : ℝ, |E'| < 2 →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E E' k O τU

/-- **Row `UNUnivMainRow`**: `(univ-main)` from the Claim `(417)`, the local law and density (a priori bound
`UNApriori`) and `UNGreenCorrAll`, for every `τ_U ∈ (0, τ₀]`, `τ₀` independent of `O`.  RBM2D
`UnivMainRow` (`Pins.lean:454`).  Registry class: **owed** (UN: `Apriori`, `UnivMain`). Consumer (RBM2D `c9a24cf`): `Main/BUniv.lean:42` (`bUniv_of_rows`, `Pins.lean:526`). -/
def UNUnivMainRow : Prop :=
  UNGreenCorrAll →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → UNClaimAll sz M E →
          ∀ k : ℕ, ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
            ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → UNUnivMain sz M ρ E k O τU

/-- **The core pin `UNCore` (target 2(b)): universality from inputs**, for an abstract model and an abstract
density.  Inputs: the external `UNL32`; the internal `UNGUELocal` and `UNGreenCorrAll`; for the model, the
tracial local law `UNTrLocal` at `m n` near `E`, the regularity of the density `UNDens` (positive lower
bound, Lipschitz), the polynomial norm bound `UNNormBound` (`(2.3)` of [32]), and the Claim `(417)` `UNClaimAll` for its OU path.  Conclusion: the dilated universality
`UNUnivDilAt` for every GUE energy `|E'| < 2` and every `𝒪 ∈ C_c^∞(ℝ^k)`, `k ≥ 1` (DECISIONS §11).  Band
(`m = msc`, `ρ = ρ_sc(E)`) and block Anderson (`m = m(·, λ_n)`, `ρ = ρ_N(E)`, bulk condition = `UNDens`) both
consume it.  Registry class: **owed** (UN). Consumer (RBM2D `c9a24cf`): `Pins.lean:497` (`bUnivOfInputs_of_rows`) and BA-D1. -/
def UNCore : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAll →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
          UNClaimAll sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M ρ E E' k O

/-- **The two limits compose** (RBM2D paper `1-2:341-345`: `(univ-main)` and `(1infyuniv)` at the same `t*`):
`UNInfty1Row` and `UNUnivMainRow` give `UNCore` (`τ_U := min τ₀ τ₁`).  RBM2D `bUnivOfInputs_of_rows`
(`Pins.lean:497`). -/
theorem un_core_of_rows (h1 : UNInfty1Row) (h2 : UNUnivMainRow) : UNCore := by
  intro h32 hGL hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hN hC E' hE' k _ O hO
  obtain ⟨τ₀, hτ₀, hU⟩ := h2 hGC d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hC k
  obtain ⟨τ₁, hτ₁, hI⟩ := h1 h32 hGL d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT hN E' hE' k O hO
  have hpos : 0 < min τ₀ τ₁ := lt_min hτ₀ hτ₁
  have h3 := (hU _ hpos (min_le_left _ _) O hO).add (hI _ hpos (min_le_right _ _))
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

end Rows

/-! ### 6b. The band-model rows, and `UNBUniv` from the rows -/

section BandRows

/-- **Row `UNOURow`**: the `𝐇_t` claims from the `G`-loop outputs, `(G_bound_ave)` and `(Meq:QUE)` at `t = 0`
(RBM2D paper `1-2:362`: "treating `𝐇_t` as a perturbation of `𝐇_0`; the details are identical to Section 7.2 of
[YY_25]"; the GUE-phase random layer, RBM2D `GUEPhase/*`, `ZeroModeProfile`, `QUEFlow`, `UNOUQUE` at the
parameters `ε₀ = 𝔡/3`, `c = 𝔡/6`).  RBM2D `OURow` (`Pins.lean:493`).  Registry class: **owed**
(UN: the 25 files `GUEPhase/*`, `ZeroModeProfile`, `QUEFlow`). -/
def UNOURow : Prop := (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNOUClaims

/-- **Row `UNEMCTE2Row`**: the weighted `(EMCTE2)` from the OU generator identity alone (RBM1D `eq225`).
RBM2D `EMCTE2Row` (`Pins.lean:475`).  Registry class: **owed**. -/
def UNEMCTE2Row : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2 sz E nf τU Cn

/-- **Row `UNJakUywRow`**: the weighted `(jaklsdufowe)`, `(uywy7723r3rf)` at `c' = 𝔠𝔡/30` from the local law and
the `𝐇_t` claims (`UNBadY`, `unBadY_measure_le`).  RBM2D `JakUywRow` (`Pins.lean:483`, `c' = 𝔠/36`).
Registry class: **owed**. -/
def UNJakUywRow : Prop :=
  UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJak sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)

/-- **Row `UNClaimRow`** (arithmetic): `(EMCTE2)` with `(jaklsdufowe)`, `(uywy7723r3rf)`, all weighted, give
`(417)` at `c' = 𝔠𝔡/30`, `C_n' = C_n + C + 1` (`Jak` at `s = univ.erase u` bounds the `L₁` term, `Uyw` at
`s = (univ.erase u).erase v` the `L₂` term).  RBM2D `ClaimRow` (`Pins.lean:466`).  Registry class: **owed**
(UN: `UnivMain`). -/
def UNClaimRow : Prop :=
  (∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNEMCTE2 sz E nf τU Cn ∧ UNJak sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)) →
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E

/-- **Row `UNDensBandRow`** (deterministic): the density regularity `UNDens` of the semicircle,
`m n = msc`, `ρ_n = ρ_sc(E)`, in a window `δ ≤ κ/2` inside the bulk (Stieltjes bounds, Lipschitz in `x`,
the limit `η ↓ 0`; RBM2D `Step1RegularityB_msc_im_ge`, `FreeConvStability` "continuity of `m_sc` up to the
real axis").  Registry class: **owed** (UN, deterministic). -/
def UNDensBandRow : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
    ∃ δ : ℝ, δ ≤ κ / 2 ∧ UNDens (fun _ => msc) E (fun _ => rhoSC E) δ

/-- **Row `UNNormBandRow`**: the band model satisfies `UNNormBound` with `CV₀ = 1` (every entry has variance
`S_xy ≤ 1`, so `|h_xy| ≤ 1` for all `x, y` with probability `≥ 1 - N^{-D}` and `|λ| ≤ N`).  RBM2D
`Step1RegularityA.lean` (entry event), `Step1RegularityB.lean` (`Step1RegularityB_eigenvalue_le`).
Registry class: **owed** (UN-10). -/
def UNNormBandRow : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz (UNModel.band sz) CV₀

/-- **Row `UNTrLocalBandRow`**: the tracial local law from the block-averaged `(G_bound_ave)`
(`N⁻¹ Tr G - m = L^{-d} ∑_a (W^{-d} ∑_{x∈[a]} G_xx - m)`).  RBM2D `Step1RegularityA` (`:1-60`,
`Step1RegularityA_tracial_le`; there with a grid, here `∩_z` is inside the probability, T2001b).
Registry class: **owed** (UN). -/
def UNTrLocalBandRow : Prop :=
  UNLocAvgBand → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ δ : ℝ, 0 < δ → δ ≤ κ / 2 →
      UNTrLocal sz (UNModel.band sz) (fun _ => msc) E δ

/-- **The `𝐇_t` claims, `(EMCTE2)`, `(jaklsdufowe)`, `(uywy7723r3rf)` give the Claim `(417)`** for the band
model from `UNMLOut`, `UNLocAvgBand`, `UNQueBand` (RBM2D `claimAll_of_rows`, `Pins.lean:510`). -/
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

/-- **Target 5: `Thm: B_Univ` (band, `UNBUniv`) from the UN pins and the consumed inputs.**  The leaves that
remain hypotheses are the external `UNL32`; the consumed MA/ST-6 inputs `UNMLOut`, `UNLocAvgBand`,
`UNQueBand`; the internal pins `UNGUELocal`, `UNGreenCorrAll`; and the rows.  The band model is the dilated
statement at `ρ_n = ρ_sc(E)`, `E' = E` (`unBUniv_diff_eq`).  RBM2D `bUniv_of_rows` (`Pins.lean:526`). -/
theorem un_bUniv_of_rows (rI : UNInfty1Row) (rU : UNUnivMainRow) (rC : UNClaimRow)
    (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow)
    (rT : UNTrLocalBandRow) (rN : UNNormBandRow) :
    UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll →
      UNBUniv := by
  intro h32 hML hLoc hQ hGL hGC d hd 𝔠 𝔡 sz hA k hk κ hκ E hE O hO
  have hE2 : |E| < 2 := by linarith
  obtain ⟨δ, hδκ, hDens⟩ := rD κ hκ E hE
  have hTr := rT hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ hDens.1 hδκ
  have hCl := un_claimAll_of_rows rC rE rJ rO hML hLoc hQ d hd 𝔠 𝔡 sz hA κ hκ E hE
  have hO' : IsTestFun (fun β => O ((rhoSC E)⁻¹ • β)) :=
    isTestFun_comp_smul hO (inv_ne_zero (rhoSC_pos hE2).ne')
  have hcore := un_core_of_rows rI rU h32 hGL hGC d hd 𝔠 𝔡 sz hA (UNModel.band sz)
    (fun _ => msc) E (fun _ => rhoSC E) δ hDens hTr (rN d hd 𝔠 𝔡 sz hA) hCl E hE2 k hk _ hO'
  refine hcore.congr fun n => ?_
  exact unBUniv_diff_eq (UNModel.band sz) hE2 k O n

end BandRows

/-! ## 5. The exponents of `1_2:570-578` and the limit computations at `d ≥ 3` (target 3)

Every lemma is a compiled version of a row of the exponent table of the report: a deterministic inequality
between the parameters `𝔠, 𝔡, N, W, ilambda, τ`.  They are used by the UN rows, not by the pins. -/

section Arith

/-- **The QUE exponent of `1_2:577`**: `(2ε₀)∧(2𝔡/5) = 2𝔡/5` and `-(2𝔡/5) + 2c = -𝔡/15` at `ε₀ = 𝔡/3`,
`c = 𝔡/6` (`ℙ(𝓑) ≤ W^{-𝔡/15+τ}`). -/
theorem un_que_exponent {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) :
    -(min (2 * (𝔡 / 3)) (2 * 𝔡 / 5)) + 2 * (𝔡 / 6) = -(𝔡 / 15) := by
  rw [min_eq_right (by linarith)]; ring

/-- The parameters `ε₀ = 𝔡/3`, `c = 𝔡/6` satisfy the constraints of `(Meq:QUE)` (`1_2:407-410`):
`ε₀ ∈ (0, 𝔡/2)`, `0 < c < ε₀ ∧ 𝔡/5`; the slacks are `𝔡/6` and `𝔡/30`. -/
theorem un_que_params {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) :
    0 < 𝔡 / 3 ∧ 𝔡 / 3 < 𝔡 / 2 ∧ 0 < 𝔡 / 6 ∧ 𝔡 / 6 < 𝔡 / 3 ∧ 𝔡 / 6 < 𝔡 / 5 :=
  ⟨by positivity, by linarith, by positivity, by linarith, by linarith⟩

/-- **The `𝓑(y)`-window lies in `𝓘_E(𝔡/3)`** (`1_2:575`: `|λ_α - E| ≤ N^{-1}W^{𝔡/3}` against
`𝓘_E(ε₀)`, `ε₀ = 𝔡/3`, `(eq:defIE)`): from `(eq:WO)`, `ilambda ≥ W^{-d/2+𝔡}`, `W ≥ 1`, the half-width
`W^{-𝔡/3}(lam W^{d/2}/N)` is at least `W^{2𝔡/3}/N ≥ W^{𝔡/3}/N`.  Holds for every `lam ≥ W^{-d/2+𝔡}`
(in particular at both ends of `(eq:WO)`), and for `lam ∧ 1` (footnote `1_2:372`) since `W^{-d/2+𝔡} ≤ 1`. -/
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

/-- `W ≥ N^𝔠` converts a `W`-power into an `N`-power: `W^{-x} ≤ N^{-𝔠x}` for `x ≥ 0` (the place of
the chain where `(Main_DEL_COND)` enters, besides `W → ∞`). -/
theorem un_W_neg_le {W N 𝔠 x : ℝ} (hN : 0 < N) (hW : 0 < W) (hx : 0 ≤ x) (hb : N ^ 𝔠 ≤ W) :
    W ^ (-x) ≤ N ^ (-(𝔠 * x)) := by
  have h1 : N ^ (𝔠 * x) ≤ W ^ x := by
    rw [Real.rpow_mul hN.le]; exact Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hb hx
  rw [Real.rpow_neg hW.le, Real.rpow_neg hN.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN _) h1

/-- **The design exponent `c'` of `(jaklsdufowe)`/`(uywy7723r3rf)` at `d ≥ 3`** (target 3): the good-event
factor is `θ = W^{-𝔡/6} ≤ N^{-𝔠𝔡/6}` and the bad event has `ℙ(𝓑) ≤ W^{-𝔡/15+τ_Q} ≤ N^{-𝔠(𝔡/15-τ_Q)}`;
at `τ_Q = 𝔡/30` the minimum of the two exponents is `𝔠𝔡/30` and it is `ℙ(𝓑)` that binds (RBM2D `𝔠/36`:
there `θ` binds, `Jak.lean:831`). -/
theorem un_cprime {𝔠 𝔡 : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) :
    min (𝔠 * 𝔡 / 6) (𝔠 * (𝔡 / 15 - 𝔡 / 30)) = 𝔠 * 𝔡 / 30 := by
  have : 0 < 𝔠 * 𝔡 := mul_pos h𝔠 h𝔡
  rw [min_eq_right (by nlinarith)]; ring

/-- The exponent of the right side of `(417)` is negative: `τ_U ≤ c'/(2(C_n+1))` gives `-c' + C_n τ_U ≤
-c'/2`.  At the design point `(𝔠, 𝔡) = (1/6, 1/10)`, `c' = 1/1800`, `C_n' = 21` (`n_f = 1`: `C_n = 1`,
`C = 19`, `+1`), `τ_U ≤ 1/79200` (RBM2D: `GreenCorr.lean:46-48`, `UnivMain.lean:355-363`). -/
theorem un_claim_exponent {c' Cn τ : ℝ} (hc : 0 < c') (hCn : 0 ≤ Cn) (hτ : τ ≤ c' / (2 * (Cn + 1))) :
    -c' + Cn * τ ≤ -(c' / 2) := by
  have hCn1 : 0 < Cn + 1 := by linarith
  have h1 : Cn * τ ≤ Cn * (c' / (2 * (Cn + 1))) := mul_le_mul_of_nonneg_left hτ hCn
  have h2 : Cn * (c' / (2 * (Cn + 1))) ≤ c' / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- **`Bctl` at the energy scale `η`**: `W^{-d}B_{1-η,0} ≤ W^{-2𝔡}`-floor `+ (Nη)⁻¹` (`(eq:calBetaK)` at
`K = 0` and `(eq:WO)`: `A = W^{2𝔡} ≤ lam² W^d`).  This is the local-law precision of `UNTrLocal`; its floor
`W^{-2𝔡} ≤ N^{-2𝔠𝔡}` (`un_W_neg_le`) is what limits `τ_s ≤ 𝔠𝔡` in `UNStep1Good` (RBM2D `Meta ≥ min(W², Nη)`,
`Step1RegularityB.lean:23`: floor `W^{-2}`, `τ_s ≤ 𝔠`). -/
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

/-- **The floor of the local law against the precision `N^{-15τ_s/16}` of the strip** (Step 1,
`Step1RegularityB.lean:36-37`): for `τ_s ≤ 𝔠𝔡`, `𝔠 < 1`, `W ≥ N^𝔠 ≥ 1`, the floor term times the loss
`W^{τ_s/8}` is `≤ N^{-15τ_s/16}`.  At `d ≥ 3` the floor is `W^{-2𝔡} ≤ N^{-2𝔠𝔡}`: the range of the free
convolution step is `τ_s ≤ 𝔠𝔡` (for `W = N^𝔠` the inequality holds exactly for `τ_s ≤ 32𝔠𝔡/(15+2𝔠)`, so `τ_s ≤ 𝔠𝔡` is not the sharp range; paper-delta candidate T2174a, docstring only), RBM2D `τ_s ≤ 𝔠`. -/
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
of the exponent table; the ticket's `L ∈ {W^{1/𝔠-1}}` is the `d = 1` form, here `L ≤ W^{1/(d𝔠)-1}`). -/
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

/-- **`𝔡 < d/2`**: for `W ≥ 1`, `(eq:WO)` `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` forces `𝔡 < d/2` (`𝔡 ≥ d/2` gives
`1 ≤ W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹ ≤ 2/d < 1`).  This is why `ε₀ = 𝔡/3 < 𝔡/2 < d/4` is always an allowed
exponent of `(Meq:QUE)`. -/
theorem un_d_lt_half {d : ℕ} (hd : 3 ≤ d) {W lam 𝔡 : ℝ} (hW : 1 ≤ W) (_h𝔡 : 0 < 𝔡)
    (h1 : W ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (h2 : lam ≤ 𝔡⁻¹) : 𝔡 < (d : ℝ) / 2 := by
  by_contra hcon
  have h3 : (d : ℝ) / 2 ≤ 𝔡 := not_lt.mp hcon
  have h4 : 1 ≤ W ^ (-(d : ℝ) / 2 + 𝔡) :=
    Real.one_le_rpow hW (show (0 : ℝ) ≤ -(d : ℝ) / 2 + 𝔡 by linarith)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have h5 : 𝔡⁻¹ ≤ ((d : ℝ) / 2)⁻¹ := inv_anti₀ hd0 h3
  have h6 : ((d : ℝ) / 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  linarith

/-- **The window of `𝓑(y)` in the `N`-scale** (target 3, `1_2:575`: `N^{-1} W^{𝔡/3}`; RBM2D `N^{-1+𝔠/6}`):
`N^{-1+𝔠𝔡/3} ≤ N^{-1}W^{𝔡/3} ≤ N^{-1+𝔡/(3d)}` from `W ≥ N^𝔠` and `W^d ≤ N`; the exponent `-1+𝔡/(3d) < 0`, so
the window is `o(1)` and the bulk stays a bulk, and `-1+𝔠𝔡/3 > -1` so it contains `≫ N^{-1}` many levels. -/
theorem un_window_N_scale {W N 𝔠 𝔡 : ℝ} {d : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) (hW : 0 < W) (h𝔡 : 0 < 𝔡)
    (hb : N ^ 𝔠 ≤ W) (hWd : W ^ d ≤ N) :
    N ^ (-1 + 𝔠 * 𝔡 / 3) ≤ N⁻¹ * W ^ (𝔡 / 3) ∧ N⁻¹ * W ^ (𝔡 / 3) ≤ N ^ (-1 + 𝔡 / (3 * d)) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · have : N ^ (𝔠 * 𝔡 / 3) ≤ W ^ (𝔡 / 3) := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hb (by positivity : 0 ≤ 𝔡 / 3)
      rwa [← Real.rpow_mul hN0.le, show 𝔠 * (𝔡 / 3) = 𝔠 * 𝔡 / 3 by ring] at h
    rw [Real.rpow_add hN0, Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · have : W ^ (𝔡 / 3) ≤ N ^ (𝔡 / (3 * d)) := by
      have h := Real.rpow_le_rpow (by positivity) hWd (by positivity : 0 ≤ 𝔡 / (3 * d))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hW.le,
        show (d : ℝ) * (𝔡 / (3 * d)) = 𝔡 / 3 by field_simp] at h
    rw [Real.rpow_add hN0, Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **The density of the semicircle on the bulk** (limit check of `UNDens` at `ρ = ρ_sc`, DECISIONS §11):
`ρ_sc(E) ≥ √(4κ - κ²)/(2π)` for `|E| ≤ 2 - κ`, with equality at the edge `|E| = 2 - κ`. -/
theorem un_rhoSC_lower {κ E : ℝ} (_hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    Real.sqrt (4 * κ - κ ^ 2) / (2 * Real.pi) ≤ rhoSC E := by
  unfold rhoSC
  have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have := abs_le.mp hE
    nlinarith [this.1, this.2]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by nlinarith)) (by positivity)

theorem un_rhoSC_edge {κ : ℝ} : rhoSC (2 - κ) = Real.sqrt (4 * κ - κ ^ 2) / (2 * Real.pi) := by
  unfold rhoSC; congr 2; ring

/-- **`ρ_sc` is Lipschitz on the bulk**: for `|x|, |y| ≤ 2 - κ`, `0 < κ`:
`|ρ_sc(x) - ρ_sc(y)| ≤ |x - y| / (π √(4κ - κ²))`. -/
theorem un_rhoSC_lip {κ x y : ℝ} (hκ : 0 < κ) (hx : |x| ≤ 2 - κ) (hy : |y| ≤ 2 - κ) :
    |rhoSC x - rhoSC y| ≤ |x - y| / (Real.pi * Real.sqrt (4 * κ - κ ^ 2)) := by
  have hκ2 : κ ≤ 2 := by
    have := abs_nonneg x; linarith
  have h4 : 0 < 4 * κ - κ ^ 2 := by nlinarith
  set s := Real.sqrt (4 * κ - κ ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 h4
  have hax : 4 * κ - κ ^ 2 ≤ 4 - x ^ 2 := by
    have := abs_le.mp hx; nlinarith [this.1, this.2]
  have hay : 4 * κ - κ ^ 2 ≤ 4 - y ^ 2 := by
    have := abs_le.mp hy; nlinarith [this.1, this.2]
  have hsx : s ≤ Real.sqrt (4 - x ^ 2) := Real.sqrt_le_sqrt hax
  have hsy : s ≤ Real.sqrt (4 - y ^ 2) := Real.sqrt_le_sqrt hay
  have hsxy : 0 < Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2) := by linarith
  have hkey : (Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)) *
      (Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2)) = (y - x) * (y + x) := by
    have e1 := Real.sq_sqrt (show 0 ≤ 4 - x ^ 2 by linarith)
    have e2 := Real.sq_sqrt (show 0 ≤ 4 - y ^ 2 by linarith)
    nlinarith
  have hxy : |y + x| ≤ 4 := by
    have := abs_le.mp hx; have := abs_le.mp hy
    rw [abs_le]; constructor <;> linarith
  have hdiff : |Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)| ≤ 2 * |x - y| / s := by
    rw [le_div_iff₀ hs0]
    have habs : |Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)| *
        (Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2)) = |y - x| * |y + x| := by
      calc |Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)| *
            (Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2))
          = |Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)| *
              |Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2)| := by rw [abs_of_pos hsxy]
        _ = |(Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)) *
              (Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2))| := (abs_mul _ _).symm
        _ = |(y - x) * (y + x)| := by rw [hkey]
        _ = |y - x| * |y + x| := abs_mul _ _
    have h2 : 2 * s ≤ Real.sqrt (4 - x ^ 2) + Real.sqrt (4 - y ^ 2) := by linarith
    have h3 : |y - x| * |y + x| ≤ 4 * |x - y| := by
      rw [abs_sub_comm y x]
      exact mul_le_mul_of_nonneg_left hxy (abs_nonneg _) |>.trans (by nlinarith [abs_nonneg (x - y)])
    nlinarith [abs_nonneg (Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)), abs_nonneg (x - y)]
  unfold rhoSC
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc |Real.sqrt (4 - x ^ 2) - Real.sqrt (4 - y ^ 2)| / (2 * Real.pi)
      ≤ (2 * |x - y| / s) / (2 * Real.pi) := by gcongr
    _ = |x - y| / (Real.pi * s) := by field_simp

end Arith

/-! ## 5b. The bad event `𝓑(y)` of `1_2:570-577` and its probability (the `d ≥ 3` step of `(2.22)`, `(2.23)`)

`[DYYY25]` defines `M_{y,α} = N ∑_x |ψ_α(x)|² S°_{xy}` (below `(yw982823)`, RBM2D paper `1-2:391`, which is `(2.24)` of `[DYYY25]` in `1_2:570`); this paper does not (`1_2:570`: "`M_{y,α}`
is defined below equation (2.24) of [DYYY25]").  For `d ≥ 3` the profile `S^{(B)}(ilambda)` has the weights
`(1 + 2d lam²)⁻¹ (δ_{ab} + lam² 1_{a∼b})` on `2d + 1` blocks (`1_2:303-306`), not the equal weights `1/5` of
RBM2D (`JakSpectral.lean:182-196`); the definition below is the one of `[DYYY25]` read with the `d ≥ 3` `S`
(paper-delta candidate T2162a).  `unBadY_subset` proves that a weighted average of block QUE quantities
exceeds `θ` only if one block quantity does: the union bound is over the support of the weights, `≤ 2d + 1`
blocks (`unBadY_card_le`). -/

section BadY

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `M_{y,α}` for a vector `ψ = ψ_α`: `N ∑_x |ψ(x)|² S°_{xy}`, `S°_{xy} = S_xy - N⁻¹` (real). -/
def unMy (lam : ℝ) (ψ : Idx d L W → ℂ) (y : Idx d L W) : ℝ :=
  (((W * L) ^ d : ℕ) : ℝ) *
    ∑ x, ‖ψ x‖ ^ 2 * (svarF d L W lam x y - ((((W * L) ^ d : ℕ) : ℝ))⁻¹)

/-- **The bad event `𝓑(y)`** (`1_2:570-575`): there is an eigenvector `ψ_α` of `M` with
`|λ_α - E| ≤ N^{-1} W^{𝔡/3}` and `|M_{y,α}| ≥ W^{-𝔡/6}`.  Consumers: `UNJak`, `UNUyw` (the split of
`(yw982823)` on `𝓑` and `𝓑ᶜ`). -/
def UNBadY (lam 𝔡 E : ℝ) (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ), IsOrthoEigenbasis M μ ψ ∧
    ∃ α, |μ α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
      (W : ℝ) ^ (-(𝔡 / 6)) ≤ |unMy d L W lam (ψ α) y|

variable {d L W}

/-- `M_{y,α}` is the `S^{(B)}`-weighted average of the block QUE quantities
`(N/W^d)(∑_{x∈[b]} |ψ(x)|² - W^d/N)` (the identity behind `(yw982823)` of `[DYYY25]`), for a unit vector. -/
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
(`1_2:575-577`: "applying `(Meq:QUE)` with `ε₀ = 𝔡/3` and `c = 𝔡/6`"): a weighted average, with weights
`SBR b a ≥ 0` summing to `1`, of the numbers `u_b = (N/W^d) |∑_{x∈[b]} |ψ|² - W^d/N|`-type quantities has
modulus `≥ W^{-𝔡/6}` only if some `u_b` with positive weight has; and the window of `𝓑(y)` is inside
`𝓘_E(𝔡/3)` (`un_window_sub`, needs `(eq:WO)`). -/
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
has `2d + 1` points for `L ≥ 3` (`1_2:303-306`; RBM2D `card_sbSupport = 5`; merged
`flucVanish_card_sbSupport`, `Green/FlucVanish.lean:1079`, is the same count). -/
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

/-- **`ℙ(𝓑(y)) ≤ (2d+1) · p`** (`1_2:577`): if `(Meq:QUE)` at `(ε₀, c) = (𝔡/3, 𝔡/6)` holds with bound `p` at every
block for the random matrix `Mf`, then the bad event `𝓑(y)` has probability `≤ (2d+1) p`.  The constant
`2d + 1` is absorbed in `W^τ` (`un_const_absorb`), giving `W^{-𝔡/15+τ}` of the paper. -/
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

/-- The constant `2d + 1` is absorbed by `W^{τ/2}` once `W^{τ/2} ≥ 2d + 1` (eventually, `W → ∞`):
`(2d+1) W^{-𝔡/15+τ/2} ≤ W^{-𝔡/15+τ}`, i.e. `ℙ(𝓑) ≤ W^{-𝔡/15+τ}` as in `1_2:577`. -/
theorem un_const_absorb {W x τ : ℝ} {d : ℕ} (hW : 1 ≤ W) (_hτ : 0 < τ)
    (h : (2 * d + 1 : ℝ) ≤ W ^ (τ / 2)) :
    (2 * d + 1 : ℝ) * W ^ (-x + τ / 2) ≤ W ^ (-x + τ) := by
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW
  have : W ^ (-x + τ) = W ^ (τ / 2) * W ^ (-x + τ / 2) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hW0.le _)

end BadYProb

/-! ## 5d. The density hypothesis `UNDens` is satisfiable at `ρ = ρ_sc`: `m = msc`, `E = 0` (limit check)

The Stieltjes bounds `c ≤ Im m ≤ C` on `|x| ≤ 1/2`, `0 < η ≤ 10`, the Lipschitz regularity in `x`, and the
limit `Im m(iη)/π → ρ_sc(0)` are proved from the quadratic equation `m (m + z) = -1` (`msc_mul`, `:118`),
`‖m‖ < 1` (`norm_msc_lt_one`, `:152`) and `Im m > 0` (`msc_im_pos`, `:123`) of `Defs/Semicircle.lean`, with
`c = 9/100`, `C = 1`, `Lp = 10000/81`.  (The row `UNDensBandRow` asks the same for every bulk `E`.) -/

section DensBand

private theorem un_msc_eqs {z : ℂ} :
    (msc z).re * ((msc z).re + z.re) - (msc z).im * ((msc z).im + z.im) = -1 ∧
    (msc z).re * ((msc z).im + z.im) + (msc z).im * ((msc z).re + z.re) = 0 := by
  have h := msc_mul z
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Lower bound of `Im msc` near the real axis in the bulk window**: `|Re z| ≤ 1/2`, `0 < Im z ≤ 10`
give `Im msc z ≥ 9/100` (from `1 = b² + bη - a² - ax ≤ b² + bη + x²/4`). -/
theorem un_msc_im_ge {z : ℂ} (hz : 0 < z.im) (hz10 : z.im ≤ 10) (hx : |z.re| ≤ 1 / 2) :
    9 / 100 ≤ (msc z).im := by
  obtain ⟨h1, _⟩ := un_msc_eqs (z := z)
  have hb : 0 < (msc z).im := msc_im_pos hz
  have hx2 : z.re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hx
    nlinarith [this.1, this.2]
  by_contra hlt
  push Not at hlt
  set a := (msc z).re
  set b := (msc z).im
  have e1 : 1 = b ^ 2 + b * z.im - a ^ 2 - a * z.re := by nlinarith
  have e2 : -a ^ 2 - a * z.re ≤ z.re ^ 2 / 4 := by nlinarith [sq_nonneg (a + z.re / 2)]
  have e3 : b * z.im ≤ 9 / 100 * 10 := by nlinarith
  nlinarith

/-- **Lipschitz dependence of `msc` on `z` where `Im msc ≥ 9/100`**: from `(m₁ - m₂)(1 - m₁m₂) = (z₁ - z₂) m₁ m₂`
and `Re(1 - m₁m₂) ≥ Im m₁ Im m₂ ≥ (9/100)²`, `‖m_i‖ < 1`. -/
theorem un_msc_lip {z₁ z₂ : ℂ} (h1 : 0 < z₁.im) (h2 : 0 < z₂.im) (hb1 : 9 / 100 ≤ (msc z₁).im)
    (hb2 : 9 / 100 ≤ (msc z₂).im) : ‖msc z₁ - msc z₂‖ ≤ (10000 / 81) * ‖z₁ - z₂‖ := by
  set m₁ := msc z₁
  set m₂ := msc z₂
  have e1 : m₁ ^ 2 + z₁ * m₁ + 1 = 0 := by have := msc_mul z₁; linear_combination this
  have e2 : m₂ ^ 2 + z₂ * m₂ + 1 = 0 := by have := msc_mul z₂; linear_combination this
  have key : (m₁ - m₂) * (1 - m₁ * m₂) = (z₁ - z₂) * (m₁ * m₂) := by
    linear_combination (-m₂) * e1 + m₁ * e2
  have hn1 : ‖m₁‖ < 1 := norm_msc_lt_one h1
  have hn2 : ‖m₂‖ < 1 := norm_msc_lt_one h2
  have ha1 : |m₁.re| ≤ 1 := (Complex.abs_re_le_norm m₁).trans hn1.le
  have ha2 : |m₂.re| ≤ 1 := (Complex.abs_re_le_norm m₂).trans hn2.le
  have hre : (81 : ℝ) / 10000 ≤ (1 - m₁ * m₂).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re]
    have : |m₁.re * m₂.re| ≤ 1 := by
      rw [abs_mul]; calc |m₁.re| * |m₂.re| ≤ 1 * 1 := mul_le_mul ha1 ha2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h3 : m₁.re * m₂.re ≤ 1 := (le_abs_self _).trans this
    nlinarith [mul_le_mul hb1 hb2 (by norm_num) (by linarith)]
  have hnorm : (81 : ℝ) / 10000 ≤ ‖1 - m₁ * m₂‖ := hre.trans ((Complex.re_le_norm _))
  have hprod : ‖m₁ - m₂‖ * ‖1 - m₁ * m₂‖ = ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) := by
    rw [← norm_mul, key, norm_mul, norm_mul]
  have hle : ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) ≤ ‖z₁ - z₂‖ := by
    have : ‖m₁‖ * ‖m₂‖ ≤ 1 := by
      calc ‖m₁‖ * ‖m₂‖ ≤ 1 * 1 := mul_le_mul hn1.le hn2.le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) ≤ ‖z₁ - z₂‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖z₁ - z₂‖ := mul_one _
  have h4 : ‖m₁ - m₂‖ * (81 / 10000) ≤ ‖z₁ - z₂‖ := by
    calc ‖m₁ - m₂‖ * (81 / 10000) ≤ ‖m₁ - m₂‖ * ‖1 - m₁ * m₂‖ :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖z₁ - z₂‖ * (‖m₁‖ * ‖m₂‖) := hprod
      _ ≤ ‖z₁ - z₂‖ := hle
  linarith

/-- On the imaginary axis `msc(iη) = i (√(η²+4) - η)/2`. -/
theorem un_msc_imag_axis {η : ℝ} (hη : 0 < η) :
    (msc ⟨0, η⟩).im = (Real.sqrt (η ^ 2 + 4) - η) / 2 := by
  have hz : 0 < (⟨0, η⟩ : ℂ).im := hη
  obtain ⟨h1, h2⟩ := un_msc_eqs (z := (⟨0, η⟩ : ℂ))
  have hb : 0 < (msc ⟨0, η⟩).im := msc_im_pos hz
  simp only [] at h1 h2
  set a := (msc (⟨0, η⟩ : ℂ)).re
  set b := (msc (⟨0, η⟩ : ℂ)).im
  have ha : a = 0 := by
    have : a * (2 * b + η) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  rw [ha] at h1
  have hbb : b ^ 2 + b * η = 1 := by nlinarith
  have hsq : η ^ 2 + 4 = (2 * b + η) ^ 2 := by nlinarith
  have : Real.sqrt (η ^ 2 + 4) = 2 * b + η := by
    rw [hsq, Real.sqrt_sq (by linarith)]
  rw [this]; ring

/-- **`UNDens` at the semicircle, `E = 0`, `δ = 1/2`**: `m n = msc`, `ρ_n = ρ_sc(0) = 1/π`:
`9/100 ≤ Im msc ≤ 1` on `|x| ≤ 1/2`, `0 < η ≤ 10`; `Im msc(·+iη)` is `10000/81`-Lipschitz there; and
`Im msc(iη)/π → 1/π = ρ_sc(0)` as `η ↓ 0`.  The non-vacuity of the density hypothesis of `UNCore` at `ρ_sc`. -/
theorem un_dens_msc_zero : UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) := by
  refine ⟨by norm_num, 9 / 100, 1, 10000 / 81, by norm_num, by norm_num, by norm_num,
    Eventually.of_forall fun n => ⟨?_, ?_, ?_⟩⟩
  · intro x η hx hη hη10
    have hx' : |(⟨x, η⟩ : ℂ).re| ≤ 1 / 2 := by simpa using hx
    refine ⟨un_msc_im_ge hη hη10 hx', ?_⟩
    exact (Complex.im_le_norm _).trans (norm_msc_lt_one hη).le
  · intro x y η hx hy hη hη10
    have hx' : |(⟨x, η⟩ : ℂ).re| ≤ 1 / 2 := by simpa using hx
    have hy' : |(⟨y, η⟩ : ℂ).re| ≤ 1 / 2 := by simpa using hy
    have hl := un_msc_lip (z₁ := ⟨x, η⟩) (z₂ := ⟨y, η⟩) hη hη (un_msc_im_ge hη hη10 hx')
      (un_msc_im_ge hη hη10 hy')
    have hnz : ‖(⟨x, η⟩ : ℂ) - ⟨y, η⟩‖ = |x - y| := by
      have : ((⟨x, η⟩ : ℂ) - ⟨y, η⟩) = ((x - y : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    calc |(msc ⟨x, η⟩).im - (msc ⟨y, η⟩).im| = |((msc ⟨x, η⟩) - (msc ⟨y, η⟩)).im| := by simp
      _ ≤ ‖msc ⟨x, η⟩ - msc ⟨y, η⟩‖ := Complex.abs_im_le_norm _
      _ ≤ (10000 / 81) * ‖(⟨x, η⟩ : ℂ) - ⟨y, η⟩‖ := hl
      _ = 10000 / 81 * |x - y| := by rw [hnz]
  · have hcont : Continuous fun η : ℝ => ((Real.sqrt (η ^ 2 + 4) - η) / 2) / Real.pi := by fun_prop
    have h0 : ((Real.sqrt ((0 : ℝ) ^ 2 + 4) - 0) / 2) / Real.pi = rhoSC 0 := by
      unfold rhoSC
      norm_num
      ring_nf
    have ht : Tendsto (fun η : ℝ => ((Real.sqrt (η ^ 2 + 4) - η) / 2) / Real.pi) (𝓝[>] 0)
        (𝓝 (rhoSC 0)) := by
      rw [← h0]
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [un_msc_imag_axis hη]

end DensBand

/-! ## 7. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2) and extreme inputs

The data: `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`,
`W = 32`, `lam = 1/64`, `N = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `k = 1`, `E = 0`, `𝒪 = ` the bump
function (`bump 0 = 1`, `bump = 0` outside `‖x‖ < 2`).  Hypotheses that are pins of other gates (MA, ST-6) or of
the UN proof tickets stay hypotheses of the examples; every deterministic hypothesis is discharged. -/

namespace UNInst

open RBM.Gauss.SizesInst

/-- A smooth bump on `Fin 1 → ℝ`, `1` on `‖x‖ ≤ 1`, supported in `‖x‖ < 2`: a nonconstant test function. -/
def bump : ContDiffBump (0 : Fin 1 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bump_testFun : IsTestFun (bump : (Fin 1 → ℝ) → ℝ) :=
  ⟨bump.contDiff, bump.hasCompactSupport⟩

theorem bump_nondegenerate :
    (bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ (bump : (Fin 1 → ℝ) → ℝ) (fun _ => 3) = 0 := by
  refine ⟨bump.one_of_mem_closedBall (by simp [bump]), bump.zero_of_le_dist ?_⟩
  simp only [bump, dist_zero_right]
  have : ‖(fun _ : Fin 1 => (3 : ℝ))‖ = 3 := by
    rw [pi_norm_const]; norm_num
  rw [this]; norm_num

/-! ### 7.1 The shared hypotheses -/

/-- `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`: the instance sequence is admissible (merged). -/
theorem sz0_adm : sz0.Admissible (1 / 6) (1 / 10) := sz0_admissible

/-- `𝔠 d < 1` at the instance (`3 · 1/6 = 1/2 < 1`) and `𝔡 < d/2` (`1/10 < 3/2`): the two ranges of the
exponent table, from the instance's own `W ≥ N^𝔠` (`n = 0`) and `(eq:WO)`. -/
theorem inst_dc_lt_one : (3 : ℝ) * (1 / 6) < 1 :=
  un_dc_lt_one (d := 3) (L := 4) (W := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := sz0_bandwidth_at 0
      have e : sz0.size 0 = ((32 * 4) ^ 3 : ℕ) := by norm_num [Sizes.size, sz0]
      rw [e] at h
      have e2 : sz0.W 0 = 32 := rfl
      rw [e2] at h
      simpa using h)

theorem inst_d_lt_half : (1 / 10 : ℝ) < (3 : ℝ) / 2 :=
  un_d_lt_half (d := 3) (W := 32) (lam := 1 / 64) (𝔡 := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have : ((32 : ℝ)) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10) = 1 / 128 := by
        have h32 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
        rw [h32, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        have : ((5 : ℕ) : ℝ) * (-((3 : ℕ) : ℝ) / 2 + 1 / 10) = -7 := by norm_num
        rw [this, Real.rpow_neg (by norm_num)]
        norm_num
      rw [this]; norm_num)
    (by norm_num)

/-! ### 7.2 The limit computation of `UNL32` at the instance and at extreme `τ` -/

theorem two_le_rpow_quarter {N : ℝ} (h : 16 ≤ N) : 2 ≤ N ^ (1 / 4 : ℝ) := by
  have h2 : ((2 : ℝ) ^ (4 : ℕ)) ^ ((4 : ℕ)⁻¹ : ℝ) = 2 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  calc (2 : ℝ) = ((2 : ℝ) ^ (4 : ℕ)) ^ ((4 : ℕ)⁻¹ : ℝ) := h2.symm
    _ ≤ N ^ ((4 : ℕ)⁻¹ : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by rw [show ((2 : ℝ) ^ (4 : ℕ)) = 16 by norm_num]; exact h)
          (by norm_num)
    _ = N ^ (1 / 4 : ℝ) := by norm_num

/-- `un_L32_arith` at `N = sz0.size 0 = 2097152`, `τ = 1/2` (`τ_s` at the extreme of `(0, 1)`): all six
premises of `UNL32`. -/
theorem inst_L32_arith_half :
    let N : ℝ := 2097152
    let σ := min ((1 / 2 : ℝ) / 4) ((1 - 1 / 2) / 3)
    let g := N ^ (-1 + (1 / 2 : ℝ) / 4)
    let G := N ^ (-σ)
    let t := 1 - Real.exp (-(N ^ (-1 + (1 / 2 : ℝ))))
    N ^ σ / N ≤ g ∧ g ≤ N ^ (-σ) ∧ G ≤ N ^ (-σ) ∧ g * N ^ σ ≤ t ∧ t ≤ N ^ (-σ) * G ^ 2 ∧
      |(0 : ℝ)| ≤ (1 / 2) * G :=
  un_L32_arith (N := 2097152) (τ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by
      have := two_le_rpow_quarter (N := 2097152) (by norm_num)
      norm_num at this ⊢
      exact this)

/-- `un_L32_arith` at a small `τ = 1/8` and `N = 2^{16}`: `N^{τ/2} = 2^{1} = 2`, the threshold is attained
(`N = 2^{2/τ}` exactly): the arithmetic is sharp at the stated threshold. -/
theorem inst_L32_arith_sharp :
    let N : ℝ := 65536
    let σ := min ((1 / 8 : ℝ) / 4) ((1 - 1 / 8) / 3)
    let g := N ^ (-1 + (1 / 8 : ℝ) / 4)
    let G := N ^ (-σ)
    let t := 1 - Real.exp (-(N ^ (-1 + (1 / 8 : ℝ))))
    N ^ σ / N ≤ g ∧ g ≤ N ^ (-σ) ∧ G ≤ N ^ (-σ) ∧ g * N ^ σ ≤ t ∧ t ≤ N ^ (-σ) * G ^ 2 ∧
      |(0 : ℝ)| ≤ (1 / 2) * G :=
  un_L32_arith (N := 65536) (τ := 1 / 8) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h : (65536 : ℝ) = (2 : ℝ) ^ (16 : ℕ) := by norm_num
      rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : ((16 : ℕ) : ℝ) * ((1 / 8 : ℝ) / 2) = 1 := by norm_num
      rw [this, Real.rpow_one])

/-! ### 7.3 The exponent lemmas at the instance -/

/-- `ε₀ = 𝔡/3`, `c = 𝔡/6`, exponent `-𝔡/15`: at `𝔡 = 1/10`, `-1/150`. -/
theorem inst_que_exponent : -(min (2 * ((1 / 10 : ℝ) / 3)) (2 * (1 / 10 : ℝ) / 5)) + 2 * ((1 / 10 : ℝ) / 6) = -((1 / 10 : ℝ) / 15) :=
  un_que_exponent (by norm_num)

theorem inst_que_params : 0 < (1 / 10 : ℝ) / 3 ∧ (1 / 10 : ℝ) / 3 < (1 / 10 : ℝ) / 2 ∧ 0 < (1 / 10 : ℝ) / 6 ∧
    (1 / 10 : ℝ) / 6 < (1 / 10 : ℝ) / 3 ∧ (1 / 10 : ℝ) / 6 < (1 / 10 : ℝ) / 5 :=
  un_que_params (by norm_num)

/-- `c' = 𝔠𝔡/30 = 1/1800` at `(𝔠, 𝔡) = (1/6, 1/10)`: `ℙ(𝓑)` binds (`1/1800 < 𝔠𝔡/6 = 1/360`). -/
theorem inst_cprime : min ((1 / 6 : ℝ) * (1 / 10) / 6) ((1 / 6 : ℝ) * ((1 / 10) / 15 - (1 / 10) / 30)) =
    (1 / 6 : ℝ) * (1 / 10) / 30 := un_cprime (by norm_num) (by norm_num)

/-- `τ_U ≤ 1/79200` at `c' = 1/1800`, `C_n' = 21`: the exponent of `(417)` is `≤ -c'/2`. -/
theorem inst_claim_exponent : -(1 / 1800 : ℝ) + 21 * (1 / 79200) ≤ -((1 / 1800 : ℝ) / 2) :=
  un_claim_exponent (by norm_num) (by norm_num) (by norm_num)

/-- The window of `𝓑(y)` lies in `𝓘_E(𝔡/3)` at the instance, at the lower edge of `(eq:WO)`
`lam = W^{-d/2+𝔡} = 1/128` and at `lam = 1/64` (the instance's own coupling). -/
theorem pow32 : ((32 : ℝ)) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10) = 1 / 128 := by
  have h32 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
  rw [h32, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : ((5 : ℕ) : ℝ) * (-((3 : ℕ) : ℝ) / 2 + 1 / 10) = -7 := by norm_num
  rw [this, Real.rpow_neg (by norm_num)]
  norm_num

theorem inst_window_sub_lower_edge : (2097152 : ℝ)⁻¹ * (32 : ℝ) ^ ((1 / 10 : ℝ) / 3) ≤
    (32 : ℝ) ^ (-((1 / 10 : ℝ) / 3)) * ((1 / 128) * (32 : ℝ) ^ (((3 : ℕ) : ℝ) / 2) / 2097152) :=
  un_window_sub (d := 3) (by norm_num) (by norm_num) (by norm_num) (by rw [pow32])

theorem inst_window_sub_inst : (2097152 : ℝ)⁻¹ * (32 : ℝ) ^ ((1 / 10 : ℝ) / 3) ≤
    (32 : ℝ) ^ (-((1 / 10 : ℝ) / 3)) * ((1 / 64) * (32 : ℝ) ^ (((3 : ℕ) : ℝ) / 2) / 2097152) :=
  un_window_sub (d := 3) (by norm_num) (by norm_num) (by norm_num) (by rw [pow32]; norm_num)

/-- At the upper edge `lam = 𝔡⁻¹ = 10` of `(eq:WO)` (extreme input): the window is larger, the inclusion holds. -/
theorem inst_window_sub_upper_edge : (2097152 : ℝ)⁻¹ * (32 : ℝ) ^ ((1 / 10 : ℝ) / 3) ≤
    (32 : ℝ) ^ (-((1 / 10 : ℝ) / 3)) * ((10 : ℝ) * (32 : ℝ) ^ (((3 : ℕ) : ℝ) / 2) / 2097152) :=
  un_window_sub (d := 3) (by norm_num) (by norm_num) (by norm_num) (by rw [pow32]; norm_num)

/-- `W^{-x} ≤ N^{-𝔠x}` at the instance (`W = 32`, `N = 2097152 = 32^{21/5}`, `𝔠 = 1/6`, `x = 1/5`). -/
theorem inst_W_neg_le : (32 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (2097152 : ℝ) ^ (-((1 / 6 : ℝ) * (1 / 5))) :=
  un_W_neg_le (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := sz0_bandwidth_at 0
      have e : sz0.size 0 = 2097152 := sz0_values.2.2.1
      have e2 : sz0.W 0 = 32 := rfl
      rw [e, e2] at h
      simpa using h)

/-- The floor of Step 1 at the instance, `τ_s = 𝔠𝔡 = 1/60` (the extreme of the range `τ_s ≤ 𝔠𝔡`). -/
theorem inst_step1_floor : (32 : ℝ) ^ ((1 / 60 : ℝ) / 8) * (32 : ℝ) ^ (-(2 * (1 / 10 : ℝ))) ≤
    (2097152 : ℝ) ^ (-(15 * (1 / 60 : ℝ) / 16)) :=
  un_step1_floor (N := 2097152) (W := 32) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (τs := 1 / 60)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by
      have h := sz0_bandwidth_at 0
      have e : sz0.size 0 = 2097152 := sz0_values.2.2.1
      have e2 : sz0.W 0 = 32 := rfl
      rw [e, e2] at h
      simpa using h)

/-- The window in the `N`-scale at the instance: `N^{-1+𝔠𝔡/3} ≤ N^{-1}W^{𝔡/3} ≤ N^{-1+𝔡/(3d)}`. -/
theorem inst_window_N_scale : (2097152 : ℝ) ^ (-1 + (1 / 6 : ℝ) * (1 / 10) / 3) ≤ (2097152 : ℝ)⁻¹ * (32 : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
    (2097152 : ℝ)⁻¹ * (32 : ℝ) ^ ((1 / 10 : ℝ) / 3) ≤ (2097152 : ℝ) ^ (-1 + (1 / 10 : ℝ) / (3 * ((3 : ℕ) : ℝ))) :=
  un_window_N_scale (d := 3) (N := 2097152) (W := 32) (𝔠 := 1 / 6) (𝔡 := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h := sz0_bandwidth_at 0
      have e : sz0.size 0 = 2097152 := sz0_values.2.2.1
      have e2 : sz0.W 0 = 32 := rfl
      rw [e, e2] at h
      simpa using h)
    (by norm_num)

/-- The local-law precision at the instance: `W^{-d}B_{1-η,0} ≤ W^{-2𝔡} + (Nη)⁻¹`, `W^{2𝔡} = 2 ≤ lam² W^d = 8`. -/
theorem inst_Bctl_le : sz0.Bctl 0 (1 - 1 / 100) ≤ (2 : ℝ)⁻¹ + (((sz0.size 0 : ℕ) : ℝ) * (1 / 100))⁻¹ :=
  un_Bctl_le sz0 0 (A := 2) (by norm_num) (by norm_num)
    (by
      have h := sz0_values
      rw [Sizes.size] at *
      simp only [sz0] at *
      norm_num)

/-- The constant `2d + 1 = 7` is absorbed by `W^{τ/2}` once `W^{τ/2} ≥ 7`: at `W = 2^{200}`, `τ = 1/10`
(an asymptotic statement: not instantiable at the instance's own `W = 32`, where `32^{1/20} < 7`). -/
theorem inst_const_absorb : (2 * 3 + 1 : ℝ) * ((2 : ℝ) ^ (200 : ℝ)) ^ (-(1 / 150 : ℝ) + (1 / 10 : ℝ) / 2) ≤
    ((2 : ℝ) ^ (200 : ℝ)) ^ (-(1 / 150 : ℝ) + 1 / 10) :=
  un_const_absorb (d := 3) (by norm_num) (by norm_num)
    (by
      have : ((2 : ℝ) ^ (200 : ℝ)) ^ ((1 / 10 : ℝ) / 2) = (2 : ℝ) ^ (10 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]; norm_num
      rw [this]; norm_num)

/-! ### 7.4 The density: `ρ_sc` on the bulk, extreme `|E| = 2 - κ` -/

theorem inst_rhoSC_lower : Real.sqrt (4 * (1 / 10 : ℝ) - (1 / 10) ^ 2) / (2 * Real.pi) ≤ rhoSC 0 :=
  un_rhoSC_lower (by norm_num) (by norm_num)

/-- At the edge `|E| = 2 - κ` the lower bound is an equality. -/
theorem inst_rhoSC_edge : rhoSC (2 - 1 / 10) = Real.sqrt (4 * (1 / 10 : ℝ) - (1 / 10) ^ 2) / (2 * Real.pi) :=
  un_rhoSC_edge

theorem inst_rhoSC_lip : |rhoSC 0 - rhoSC (19 / 10)| ≤ |(0 : ℝ) - 19 / 10| / (Real.pi * Real.sqrt (4 * (1 / 10 : ℝ) - (1 / 10) ^ 2)) :=
  un_rhoSC_lip (by norm_num) (by norm_num) (by norm_num)

/-- `UNDens` at `ρ_sc`, `E = 0` (proved in 5d). -/
theorem inst_dens_msc : UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) := un_dens_msc_zero

/-! ### 7.5 The `d ≥ 3` step of `(2.22)`, `(2.23)`: `𝓑(y)` at `(d, L, W) = (3, 4, 32)` -/

/-- `M_{y,y}` of the standard basis vector `e_y`: `N (S_yy - N⁻¹)`. -/
theorem unMy_single_self (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (y : Idx d L W) :
    unMy d L W lam (Pi.single y 1) y =
      (((W * L) ^ d : ℕ) : ℝ) * (((W : ℝ) ^ d)⁻¹ * (1 + 2 * (d : ℝ) * lam ^ 2)⁻¹ -
        ((((W * L) ^ d : ℕ) : ℝ))⁻¹) := by
  unfold unMy
  rw [Finset.sum_eq_single y]
  · simp [svarF_diag]
  · intro x _ hx
    simp [hx]
  · intro h; exact absurd (Finset.mem_univ y) h

/-- The standard basis is an orthonormal eigenbasis of the zero matrix. -/
theorem isOrthoEigenbasis_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsOrthoEigenbasis (0 : Matrix ι ι ℂ) (fun _ => 0) (fun k => Pi.single k 1) := by
  refine ⟨fun k k' => ?_, fun k => ?_⟩
  · simp [Pi.single_apply, eq_comm]
  · rw [Matrix.zero_mulVec]; simp

/-- **A nondegenerate bad event**: the zero matrix on `Idx 3 4 32` (`n = 0` of `sz0`) with eigenbasis the
standard basis has `𝓑(y)` for `y = 0`, `E = 0`: `|M_{y,y}| = L^d/(1+2d lam²) - 1 ≈ 62.9 ≥ 1 ≥ W^{-𝔡/6}`. -/
theorem badY_zero : UNBadY 3 4 32 (1 / 64) (1 / 10) 0 (0 : Idx 3 4 32) 0 := by
  refine ⟨fun _ => 0, fun k => Pi.single k 1, isOrthoEigenbasis_zero, 0, ?_, ?_⟩
  · simp only [sub_self, abs_zero]; positivity
  · rw [unMy_single_self]
    have h1 : ((32 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    refine h1.trans ?_
    norm_num

/-- **`unBadY_subset` at the instance** (all deterministic hypotheses discharged: `3 ≤ L`, `W ≥ 1`, `𝔡 > 0`,
`(eq:WO)` `lam ≥ W^{-d/2+𝔡}`): some block `b` in the support of the weights has the QUE bad event. -/
theorem inst_badY_subset : ∃ b : Zd 3 4, SBR 3 4 (1 / 64) b (split 3 4 32 (0 : Idx 3 4 32)).1 ≠ 0 ∧
    queBadMat 3 4 32 (1 / 64) (1 / 10 / 3) (1 / 10 / 6) 0 b (0 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ) :=
  unBadY_subset (d := 3) (L := 4) (W := 32) (by norm_num) (by norm_num) (by norm_num)
    (by rw [Nat.cast_ofNat, pow32]; norm_num) _ _ badY_zero

/-- **`unBadY_measure_le` at the instance**: the law `δ_*` on a point with the zero matrix: every block bad
event has probability `1`, `p = 1`, so `ℙ(𝓑(y)) ≤ (2d+1) · 1 = 7`; the bound is not sharp here (the point of
the instance is that every hypothesis is discharged and the event is nonempty, `badY_zero`). -/
theorem inst_badY_measure : (Measure.dirac ()) {_ω : Unit | UNBadY 3 4 32 (1 / 64) (1 / 10) 0 (0 : Idx 3 4 32)
      (0 : Matrix (Idx 3 4 32) (Idx 3 4 32) ℂ)} ≤ ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1 :=
  unBadY_measure_le (d := 3) (L := 4) (W := 32) (Measure.dirac ()) (by norm_num) (by norm_num)
    (by norm_num) (by rw [Nat.cast_ofNat, pow32]; norm_num) _ (fun _ => 0) 1
    (fun b => prob_le_one)

/-- The support of the weights has at most `2d + 1 = 7` blocks (here: for `lam = 1/64`, `L = 4`). -/
theorem inst_badY_card (a : Zd 3 4) : (Finset.univ.filter fun b : Zd 3 4 => SBR 3 4 (1 / 64) b a ≠ 0).card ≤ 2 * 3 + 1 :=
  unBadY_card_le (by norm_num) _ a


/-! ### 7.6 The skeleton: `Thm: B_Univ` (band) and the block Anderson form from `UNCore` (target 5) -/

/-- **Target 5(a): `Thm: B_Univ` for the band model at the instance** (`sz0`, `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`,
`k = 1`, `κ = 1/10`, `E = 0`, `𝒪 = bump`) from the UN pins and the consumed inputs: every deterministic hypothesis is
discharged; the hypotheses are the external `UNL32`, the consumed `UNMLOut`, `UNLocAvgBand`, `UNQueBand`
(MA/ST-6 pins to be frozen), the internal `UNGUELocal`, `UNGreenCorrAll` and the rows of the UN proof tickets. -/
theorem inst_bUniv_band (rI : UNInfty1Row) (rU : UNUnivMainRow) (rC : UNClaimRow) (rE : UNEMCTE2Row)
    (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow) (rT : UNTrLocalBandRow)
    (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand)
    (hQ : UNQueBand) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0) :=
  un_bUniv_of_rows rI rU rC rE rJ rO rD rT rN h32 hML hLoc hQ hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0
    sz0_adm 1 le_rfl (1 / 10) (by norm_num) 0 (by norm_num) bump bump_testFun

/-- **Target 5(a'): the core at `ρ = ρ_sc`, `E = 0`, `E' = 0`** for the band model: `UNDens` at `msc` is discharged
(`un_dens_msc_zero`, so the hypothesis set of `UNCore` is nonempty at `ρ = ρ_sc`); the remaining hypotheses are the
local law `UNTrLocal` and the Claim `(417)` of the model (MA and UN rows) and the external/internal pins. -/
theorem inst_core_band (hcore : UNCore) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll)
    (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.band sz0) 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  hcore h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens_msc_zero hT hN hC 0 (by norm_num) 1 le_rfl bump bump_testFun

/-- **Target 5(b): the block Anderson form of DECISIONS §11 from `UNCore`**: the model `UNModel.ba sz0`
(`H = V + ilambda Ψ`, law `seqP (sz0.withLam 0)`), the data `m n = m(·, λ_n)` of `(self_m)`, the density
`ρ_N(E) = π⁻¹ Im m_n(E + i0)` and the bulk condition (= `UNDens`) are supplied by BA-D1 and stay hypotheses; the
conclusion is the dilated universality `ρ_N(E)^{-k} p_H^{(k)}(E + α/(Nρ_N(E)))` against GUE at an arbitrary
`|E'| < 2` with density `ρ_sc(E')`. -/
theorem inst_core_ba (hcore : UNCore) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll)
    (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (hD : UNDens m E ρ δ)
    (hT : UNTrLocal sz0 (UNModel.ba sz0) m E δ)
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.ba sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.ba sz0) E) (E' : ℝ) (hE' : |E'| < 2) :
    UNUnivDilAt sz0 (UNModel.ba sz0) ρ E E' 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  hcore h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.ba sz0) m E ρ δ hD hT hN hC E' hE' 1
    le_rfl bump bump_testFun

/-- Target 5(c): the Claim `(417)` for the band model from the four band rows, at the instance (`κ = 1/10`,
`E = 0`). -/
theorem inst_claimAll_band (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNClaimAll sz0 (UNModel.band sz0) 0 :=
  un_claimAll_of_rows rC rE rJ rO hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (1 / 10)
    (by norm_num) 0 (by norm_num)

/-! ### 7.7 Extreme inputs -/

/-- `k = 0`: `kPoint 0 O E λ = O 0` (no injection needed): the statement is vacuous, which is why the pins have
`1 ≤ k` (RBM2D `PinsCheck.kPoint_zero`, `Pins.lean:569`). -/
theorem kPoint_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (O : (Fin 0 → ℝ) → ℝ) (E : ℝ)
    (lam : ι → ℝ) : kPoint 0 O E lam = O 0 := by
  simp only [kPoint, pow_zero, Nat.descFactorial_zero, Nat.cast_one, div_one, one_mul]
  rw [Fintype.sum_unique]
  exact congrArg O (Subsingleton.elim _ _)

/-- `k > N`: no injection `Fin k ↪ ι`, `kPoint = 0` (RBM2D `PinsCheck.kPoint_eq_zero_of_card_lt`, `:560`). -/
theorem kPoint_eq_zero_of_card_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) (hk : Fintype.card ι < k) :
    kPoint k O E lam = 0 := by
  have hemp : IsEmpty (Fin k ↪ ι) :=
    ⟨fun f => absurd (Fintype.card_le_of_embedding f) (by simpa using hk.not_ge)⟩
  simp [kPoint]

/-- At `k = 0` the dilated statement is trivially true, for every model, density and energies. -/
theorem unUnivDilAt_zero {d : ℕ} (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ)
    (O : (Fin 0 → ℝ) → ℝ) : UNUnivDilAt sz M ρ E E' 0 O := by
  unfold UNUnivDilAt
  have h : ∀ n, ((∫ ω, kPoint 0 (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
      ∫ ω, kPoint 0 (fun α => O (rhoSC E' • α)) E'
        (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) = 0 := by
    intro n
    simp [kPoint_zero]
  simp_rw [h]
  exact tendsto_const_nhds

/-- `(EMCTE2)` at `n_f = 0` holds (both products are `1`); `0 ≤ B` is needed: without it the pin would claim
`0 ≤ N^ε N^{…} B` for every `B`, which is false (RBM2D report extreme input E5, `Pins.lean:577-608`). -/
theorem un_emcte2_zero {d : ℕ} (sz : Sizes d) (E τU Cn : ℝ) : UNEMCTE2 sz E 0 τU Cn := by
  intro C₀ ε _ _
  refine Eventually.of_forall fun n z _ B hB _ _ t _ _ => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero]
  have : 0 ≤ Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) := by positivity
  exact mul_nonneg this hB

/-- `Claim417` at `n_f = 0` holds (RBM2D extreme input E6). -/
theorem un_claim417_zero {d : ℕ} (sz : Sizes d) (M : UNModel sz) (E τU c' Cn : ℝ) :
    UNClaim417 sz M E 0 τU c' Cn := by
  intro C₀ _
  refine Eventually.of_forall fun n z _ t _ _ => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero]
  positivity

/-- `Uyw` at `n_f = 1` holds (no pair `i ≠ j`; RBM2D extreme input E7). -/
theorem un_uyw_one {d : ℕ} (sz : Sizes d) (E τU C c' : ℝ) : UNUyw sz E 1 τU C c' := by
  intro C₀ ε _ _
  exact Eventually.of_forall fun n z _ t _ _ s i j hij y b₁ b₂ =>
    absurd (Subsingleton.elim i j) hij


/-- The negative check behind `un_emcte2_zero`: the `n_f = 0` instance of `UNEMCTE2` **without** `0 ≤ B` is
false for every size sequence (take `B = -1`); the hypotheses on the `L₁`, `L₂` kernels are empty at `n_f = 0`
and are dropped.  RBM2D `PinsCheck.not_emcte2_zero_noB` (`Pins.lean:585`). -/
theorem un_not_emcte2_zero_noB {d : ℕ} (sz : Sizes d) (E τU Cn : ℝ) :
    ¬ (∀ C₀ ε : ℝ, 0 < C₀ → 0 < ε → ∀ᶠ n in atTop, ∀ z : Fin 0 → ℂ,
      (∀ i, InWindow sz E C₀ τU n (z i)) → ∀ B : ℝ,
        ∀ t : ℝ, 0 ≤ t → t ≤ ouTStar sz τU n →
          |(∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im
              ∂(ouP (UNModel.band sz) n)) -
            ∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n (ouTStar sz τU n) ω) (z i)).im
              ∂(ouP (UNModel.band sz) n)| ≤
            Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) * B) := by
  intro h
  obtain ⟨n, hn⟩ := (h 1 1 one_pos one_pos).exists
  have ht : (0 : ℝ) ≤ ouTStar sz τU n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have key := hn Fin.elim0 (fun i => i.elim0) (-1) 0 le_rfl ht
  simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero] at key
  have hN : (0 : ℝ) < Nsz sz n := by
    have : 0 < sz.size n := by
      simp only [Sizes.size]
      have := sz.three_le_L n
      have := sz.W_pos n
      positivity
    exact_mod_cast this
  have h1 := Real.rpow_pos_of_pos hN 1
  have h2 := Real.rpow_pos_of_pos hN (-1 + Cn * τU)
  nlinarith [mul_pos h1 h2]


/-- **`un_core_of_rows` at the instance**: the two limit rows give the core, which is then applied at
`sz0`, `E = 0`, `E' = 0`, `ρ = ρ_sc(0)`, `𝒪 = bump` (the density hypothesis is discharged by `un_dens_msc_zero`). -/
theorem inst_core_of_rows (rI : UNInfty1Row) (rU : UNUnivMainRow) (h32 : UNL32) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAll) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.band sz0) 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
  un_core_of_rows rI rU h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0)
    (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) un_dens_msc_zero hT hN hC 0 (by norm_num) 1 le_rfl
    bump bump_testFun


end UNInst

end RBM.Univ
