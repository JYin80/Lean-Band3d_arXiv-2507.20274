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

end BadYProb

/-! ## 5d. The density hypothesis `UNDens` is satisfiable at `ρ = ρ_sc`: `m = msc`, `E = 0` (limit check)

The Stieltjes bounds `c ≤ Im m ≤ C` on `|x| ≤ 1/2`, `0 < η ≤ 10`, the Lipschitz regularity in `x`, and the
limit `Im m(iη)/π → ρ_sc(0)` are proved from the quadratic equation `m (m + z) = -1` (`msc_mul`, `:118`),
`‖m‖ < 1` (`norm_msc_lt_one`, `:152`) and `Im m > 0` (`msc_im_pos`, `:123`) of `Defs/Semicircle.lean`, with
`c = 9/100`, `C = 1`, `Lp = 10000/81`.  (The row `UNDensBandRow` asks the same for every bulk `E`.) -/

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

/-! ### 7.1 The shared hypotheses -/

/-! ### 7.2 The limit computation of `UNL32` at the instance and at extreme `τ` -/

/-! ### 7.3 The exponent lemmas at the instance -/

/-! ### 7.4 The density: `ρ_sc` on the bulk, extreme `|E| = 2 - κ` -/

/-! ### 7.5 The `d ≥ 3` step of `(2.22)`, `(2.23)`: `𝓑(y)` at `(d, L, W) = (3, 4, 32)` -/

/-! ### 7.6 The skeleton: `Thm: B_Univ` (band) and the block Anderson form from `UNCore` (target 5) -/

/-! ### 7.7 Extreme inputs -/

/-- `(EMCTE2)` at `n_f = 0` holds (both products are `1`); `0 ≤ B` is needed: without it the pin would claim
`0 ≤ N^ε N^{…} B` for every `B`, which is false (RBM2D report extreme input E5, `Pins.lean:577-608`). -/
theorem un_emcte2_zero {d : ℕ} (sz : Sizes d) (E τU Cn : ℝ) : UNEMCTE2 sz E 0 τU Cn := by
  intro C₀ ε _ _
  refine Eventually.of_forall fun n z _ B hB _ _ t _ _ => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero]
  have : 0 ≤ Nsz sz n ^ ε * Nsz sz n ^ (-1 + Cn * τU) := by positivity
  exact mul_nonneg this hB

end UNInst

end RBM.Univ
