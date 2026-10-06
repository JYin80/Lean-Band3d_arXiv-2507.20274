/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Endpoints
import RBM3D.Propagator.Prop6Hold
import RBM3D.Propagator.Pins
import RBM3D.Green.EntryCore
import RBM3D.Induction.ContinuityNet

/-!
# MA-05a: the carrier side of `QUE` from `QDiff` (spectral bound, trace algebra, core, events)

Ticket T2240 (MA-05a of the T2192 assembly split).  MA-05 measured against its components is about
1580 lines, above the 1500-line limit, so it splits at the carrier-free boundary (DECISIONS §9,
T2192 portmap `:426`).  Everything here is at one fixed `(sz, n, z)`: no `∀ᶠ n`, no union over a
grid.  MA-05b (`Main/QUEFromQDiff`) holds the scale `η_Q`, the `d = 3` exponent chain, `MAQUE` and
`QUE_of_QDiff`.

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`), the outline of
the proof of Theorem 2.3 (`MR:QUE`).  Port of RBM2D `RBM2D/Main/QUEFromQDiff.lean` at `c9a24cf`
(read-only), `:38-812`, to general `d` on the band carrier (`Zd d L`, `Idx d L W`, `avg2`,
`profPM`/`profPP`): `Z2 L` becomes `Zd d L`, `L²` becomes `L^d`, `W²` becomes `W^d`, `Epaper`
becomes `queBlk`, `trGEGE` becomes `avg2` of the entries of `Gn = (H - z)⁻¹`.

* `(ssfa2)` (`1_2:524-530`): `normSq_le_trace`, `|ψ_k^* B ψ_{k'}|² ≤ 4η² Re tr(Im G B Im G B)`
  for `k, k'` in the window `|μ - E| ≤ η` and Hermitian `B`, at `z = E + iη`.
* `(que0)`, `(ssfa2_deter)` (`1_2:531-537`): `queX_core`, `E X_c ≤ 4 (K + ε)` for
  `X_c = Re tr(Im G B_c Im G B_c)`, `B_c = ∑_u (c_u - L^{-d}) E_u`, from the expectation half of
  `QDiff` (error `ε`) and the row differences `K` of the profiles (`∑ β = 0`, `∑ |β| ≤ 2`, the
  four-term formula of `Im G = (G - G†)/(2i)`).
* `thetaDiff` (`1_2:534-537`, `max |Θ_ab - Θ_ab'| ≺ ilambda^{-2}`): `MAThetaDiff`, the `d ≥ 3`
  replacement of RBM2D's `d = 2` Fourier bound `QUEFromQDiff_profile_diff` (`:465`, with
  `log L`): no `log L` here.  Copied verbatim from the compiled probe
  `RBM3D/Probe/T2192Pins.lean` at `97d958e` (branch `t/T2192`, never merged), `:665-772` and
  `:2439-2446`; the probe namespace `RBM.Probe.T2192` becomes `RBM.Endpoints`, its `Inst`
  becomes `RBM.Endpoints.Inst`.
* `queBad_sub`, `que2Bad_sub`: the events `(Meq:QUE)`, `(Meq:QUE2)` are inside
  `{W^{-2c} ≤ 4N²η² X_c}` for `c = δ_a`, `c = 1_A/|A|`, when the window `𝓘_E(ε₀)` lies in
  `[E - η, E + η]`.  `queMarkov`: Markov's inequality.
* Instances (CLAUDE.md §4 step 2): `inst_thetaDiff`, `inst_queBad_sub` (named, as pinned) and
  anonymous `example`s for `que2Bad_sub`, `normSq_le_trace`, `queMarkov`, `queX_core` at concrete
  data (`sz0`, `n = 0`, `d = 3`; `queX_core` keeps the expectation half of `QDiff` as a hypothesis).
* Consumers: MA-05b only (`QUE_of_QDiff`).  Paper deltas D500 (`N₀` uniform over `𝐃_{κ,ε}`),
  D503 (`a, b` inside), D504 (explicit form) are unchanged.  Registry
  (`RBM3D/Test/Axioms.lean`): no new line.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Endpoints

/-! ## 1. The `Θ`-differences `MAThetaDiff`, `thetaDiff` (verbatim from the probe) -/

/-! ### (e) The `Θ`-differences of the QUE deduction (`1_2:536-537`): present on `main`, not missing -/

section ThetaDiff

open scoped Matrix.Norms.Operator

/-- **Pin `MAThetaDiff`** (`1_2:534-537`, `max_{σ,σ',a,b,b'} |Θ^{(σσ')}_{ab} - Θ^{(σσ')}_{ab'}| ≺ ilambda^{-2}`):
at every `z ∈ 𝐃_{κ,·}` (`0 < Im z ≤ 1`, `|Re z| ≤ 2 - κ`) and every `0 < g ≤ 𝔡⁻¹`, for `Θ^{(+,-)}` (`ξ = |m|²`) and
`Θ^{(+,+)}` (`ξ = m²`), with a constant `C(d, 𝔡, κ)`: deterministic, no `≺`, **no `log L`** (RBM2D
`norm_Theta_sub_le_log` is the `d = 2` form, `QUEFromQDiff_profile_diff`, `RBM2D/Main/QUEFromQDiff.lean:465`).
Proved below from the merged `prop5to8_holds` (`Propagator/Prop6Hold.lean:433`, no hypothesis),
`Theta_apply_add_right` (`Propagator/Basic.lean:154`) and `Theta0_apply` (`Propagator/Basic.lean:229`). -/
def MAThetaDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b - Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b'‖ ≤
            C * (g ^ 2)⁻¹ ∧
        ‖Theta d L g (msc z ^ 2) a b - Theta d L g (msc z ^ 2) a b'‖ ≤ C * (g ^ 2)⁻¹

/-- Row `0` reduction: `Θ_{ab} - Θ_{ab'} = Θ̊_{0,b-a} - Θ̊_{0,b'-a}` (translation invariance, the zero mode is a
constant matrix). -/
private theorem theta_diff_of_row (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {B : ℝ}
    (hB : ∀ x : Zd d L, ‖Theta0 d L g ξ 0 x‖ ≤ B) (a b b' : Zd d L) :
    ‖Theta d L g ξ a b - Theta d L g ξ a b'‖ ≤ 2 * B := by
  have hS : ‖SB d L g‖ = 1 := norm_SB d L g hL
  have hrow : ∀ x : Zd d L, Theta d L g ξ a x = Theta d L g ξ 0 (x - a) := by
    intro x
    have h := Theta_apply_add_right d L g hS hξ 0 (x - a) a
    simpa using h
  rw [hrow b, hrow b']
  have h0 : Theta d L g ξ 0 (b - a) - Theta d L g ξ 0 (b' - a) =
      Theta0 d L g ξ 0 (b - a) - Theta0 d L g ξ 0 (b' - a) := by
    rw [Theta0_apply, Theta0_apply]; ring
  rw [h0]
  calc ‖Theta0 d L g ξ 0 (b - a) - Theta0 d L g ξ 0 (b' - a)‖
      ≤ ‖Theta0 d L g ξ 0 (b - a)‖ + ‖Theta0 d L g ξ 0 (b' - a)‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hB _) (hB _)
    _ = 2 * B := by ring

theorem thetaDiff : MAThetaDiff := by
  intro d hd 𝔡 κ h𝔡 hκ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine ⟨1, one_pos, fun L hL g hg hgΛ z hz hz1 hre => ?_⟩
    exfalso
    have := abs_nonneg z.re
    linarith
  have hκ' : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  obtain ⟨C₈, hC₈, H⟩ := prop5to8_holds d 𝔡⁻¹ (Real.sqrt (κ * (4 - κ)) / 2) (1 / 2) |>.zeroMode hd
    (inv_pos.2 h𝔡) hκ'
  refine ⟨2 * C₈, by positivity, fun L hL g hg hgΛ z hz hz1 hre a b b' => ?_⟩
  have : NeZero L := ⟨by omega⟩
  have hE := (lemma28_quant hκ hz hz1 hre).1
  have hE2 : |lemE z| ≤ 2 := (abs_lemE_lt_two hz).le
  have hm1 : ‖mE (lemE z)‖ = 1 := norm_mE hE2
  have hmi : Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE (lemE z)).im := by
    rw [mE_im]
    have h1 := abs_le.1 hE
    have : κ * (4 - κ) ≤ 4 - lemE z ^ 2 := by nlinarith [h1.1, h1.2]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt this) (by norm_num)
  have ht0 : 0 ≤ lemT z := (lemT_pos hz).le
  have ht1 : lemT z < 1 := lemT_lt_one hz
  have hmn : 0 < ‖msc z‖ := norm_msc_pos hz
  have hmn1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hB : ∀ (σ₁ σ₂ : Bool) (x : Zd d L),
      ‖Theta0 d L g ((lemT z : ℂ) * (PropSpin (mE (lemE z)) σ₁ * PropSpin (mE (lemE z)) σ₂)) 0 x‖ ≤
        C₈ * (g ^ 2)⁻¹ := by
    intro σ₁ σ₂ x
    refine (H L hL g hg hgΛ (lemT z) ht0 ht1 (mE (lemE z)) hm1 hmi σ₁ σ₂ x).trans ?_
    have h1 : (g ^ 2 + |1 - lemT z|)⁻¹ ≤ (g ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by have := abs_nonneg (1 - lemT z); linarith)
    have h2 : ((((zdistD d L x : ℝ)) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0 : ℝ) ≤ zdistD d L x := Nat.cast_nonneg _; linarith))
    have h3 : 0 ≤ (g ^ 2 + |1 - lemT z|)⁻¹ := by positivity
    calc C₈ * (g ^ 2 + |1 - lemT z|)⁻¹ * ((((zdistD d L x : ℝ)) + 1) ^ (d - 2))⁻¹
        ≤ C₈ * (g ^ 2)⁻¹ * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₈.le) h2 (by positivity) (by positivity)
      _ = C₈ * (g ^ 2)⁻¹ := mul_one _
  have hξ1 : (lemT z : ℂ) * (PropSpin (mE (lemE z)) true * PropSpin (mE (lemE z)) false) =
      (((‖msc z‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [PropSpin, ite_true, Bool.false_eq_true, ite_false]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hm1]
    simp [lemT]
  have hξ2 : (lemT z : ℂ) * (PropSpin (mE (lemE z)) true * PropSpin (mE (lemE z)) true) = msc z ^ 2 := by
    simp only [PropSpin, ite_true]
    rw [mE_lemE hz]
    have hne : ((‖msc z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmn.ne'
    simp only [lemT]
    push_cast
    field_simp
  have hn1 : ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have hn2 : ‖msc z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith
  refine ⟨?_, ?_⟩
  · have h := theta_diff_of_row d L hL g hn1 (B := C₈ * (g ^ 2)⁻¹)
      (fun x => by rw [← hξ1]; exact hB true false x) a b b'
    linarith
  · have h := theta_diff_of_row d L hL g hn2 (B := C₈ * (g ^ 2)⁻¹)
      (fun x => by rw [← hξ2]; exact hB true true x) a b b'
    linarith

end ThetaDiff

/-! ## 2. Vocabulary: `Im G`, `E_a`, `B_c`, `X_c` -/

/-- `Im G = (G - G†)/(2i)` (RBM2D `QUEFromQDiff_imG`, `QUEFromQDiff.lean:44`). -/
noncomputable def queImG {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Matrix ι ι ℂ :=
  ((2 : ℂ) * Complex.I)⁻¹ • (RBM.green H z - (RBM.green H z)ᴴ)

/-- `E_a = W^{-d} 1_{[a]}` (diagonal; RBM2D `Epaper`). -/
noncomputable def queBlk (d L W : ℕ) [NeZero L] [NeZero W] (a : Zd d L) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.diagonal fun x => if x ∈ Iblk d L W a then (((W : ℂ) ^ d)⁻¹) else 0

/-- `B_c = ∑_u (c_u - L^{-d}) E_u` (RBM2D `QUEFromQDiff_B`, `:345`, `L²` → `L^d`). -/
noncomputable def queObs (d L W : ℕ) [NeZero L] [NeZero W] (c : Zd d L → ℝ) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  ∑ u, (((c u - ((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) • queBlk d L W u

/-- `X_c(ω) = Re tr(Im G B_c Im G B_c)` at `H = seqXmat n ω` (RBM2D `QUEFromQDiff_X`, `:510`). -/
noncomputable def queX {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (c : Zd d (sz.L n) → ℝ) (ω : sz.SeqΩ) : ℝ :=
  (Matrix.trace (queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c *
    queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c)).re

/-! ## 3. Spectral: `(ssfa2)`, trace algebra, the core, the events -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℂ} {μ : ι → ℝ} {ψ : ι → ι → ℂ}

/-- The matrix of eigenvector columns. -/
private def queCore_U (ψ : ι → ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun y l => ψ l y

private theorem queCore_UU (hψ : IsOrthoEigenbasis H μ ψ) :
    star (queCore_U ψ) * queCore_U ψ = 1 := by
  ext k k'
  have h := hψ.1 k k'
  simp only [dotProduct, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, queCore_U, Matrix.of_apply,
    Matrix.one_apply]
  exact h

private theorem queCore_green_eq (hψ : IsOrthoEigenbasis H μ ψ) {z : ℂ}
    (hz : ∀ l, (μ l : ℂ) ≠ z) :
    green H z = queCore_U ψ * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) *
      star (queCore_U ψ) := by
  set U := queCore_U ψ with hU
  have hUU : star U * U = 1 := queCore_UU hψ
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have hHU : H * U = U * diagonal (fun l => (μ l : ℂ)) := by
    ext y l
    have h := congrFun (hψ.2 l) y
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hU, queCore_U, Matrix.of_apply]
    rw [h, mul_comm]
  have hsub : (H - z • 1) * U = U * diagonal (fun l => (μ l : ℂ) - z) := by
    rw [Matrix.sub_mul, hHU, Matrix.smul_mul, Matrix.one_mul, ← diagonal_sub,
      Matrix.mul_sub, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  apply Matrix.inv_eq_right_inv
  calc (H - z • 1) * (U * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U)
      = ((H - z • 1) * U) * diagonal (fun l => ((μ l : ℂ) - z)⁻¹) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (diagonal (fun l => (μ l : ℂ) - z)
          * diagonal (fun l => ((μ l : ℂ) - z)⁻¹)) * star U := by
        rw [hsub]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        have hd : (fun l => ((μ l : ℂ) - z) * ((μ l : ℂ) - z)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [diagonal_mul_diagonal, hd, diagonal_one, Matrix.mul_one, hUU']

/-- The resolvent weight `w_l = η / ((μ_l - E)² + η²)`. -/
private noncomputable def queCore_w (μ : ι → ℝ) (E η : ℝ) (l : ι) : ℝ :=
  η / ((μ l - E) ^ 2 + η ^ 2)

/-- `Im G(E + iη) = U diag(w) U*` for any orthonormal eigenbasis. -/
private theorem queCore_imG_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) :
    queImG H (E + η * Complex.I) = queCore_U ψ *
      diagonal (fun l => ((queCore_w μ E η l : ℝ) : ℂ)) * star (queCore_U ψ) := by
  set z : ℂ := E + η * Complex.I with hzdef
  have hz : ∀ l, (μ l : ℂ) ≠ z := by
    intro l h
    have := congrArg Complex.im h
    simp [hzdef] at this
    exact hη this.symm
  set U := queCore_U ψ with hU
  set d : ι → ℂ := fun l => ((μ l : ℂ) - z)⁻¹ with hd
  have hG := queCore_green_eq hψ hz
  rw [← hd] at hG
  have hGH : (green H z)ᴴ = U * diagonal (star d) * star U := by
    rw [hG, conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose,
      Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdiag : diagonal (fun l => ((queCore_w μ E η l : ℝ) : ℂ)) =
      ((2 : ℂ) * Complex.I)⁻¹ • (diagonal d - diagonal (star d)) := by
    rw [diagonal_sub, ← diagonal_smul]
    congr 1
    funext l
    simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, RCLike.star_def]
    rw [Complex.sub_conj]
    have hn : Complex.normSq ((μ l : ℂ) - z) = (μ l - E) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]
      simp [hzdef]
      ring
    have him : ((μ l : ℂ) - z).im = -η := by simp [hzdef]
    have hdim : (d l).im = queCore_w μ E η l := by
      simp only [hd, Complex.inv_im, hn, him, queCore_w]
      ring
    rw [hdim]
    have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    field_simp
    push_cast
    ring
  unfold queImG
  rw [hGH, hG, hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
/-- The entry `(U* B U)_{lm} = ψ_l^* B ψ_m`. -/
private theorem queCore_C_apply (B : Matrix ι ι ℂ) (l m : ι) :
    (star (queCore_U ψ) * B * queCore_U ψ) l m = star (ψ l) ⬝ᵥ (B *ᵥ ψ m) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, queCore_U,
    Matrix.star_apply, Matrix.of_apply, Pi.star_apply]

/-- For Hermitian `B`: `tr(Im G B Im G B) = ∑_{l,m} w_l w_m |ψ_l^* B ψ_m|²`. -/
private theorem queCore_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B) =
      ∑ l, ∑ m, ((queCore_w μ E η l * queCore_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) : ℝ) : ℂ) := by
  rw [queCore_imG_eq hψ E hη]
  set U := queCore_U ψ with hU
  set D : Matrix ι ι ℂ := diagonal (fun l => ((queCore_w μ E η l : ℝ) : ℂ)) with hD
  set C : Matrix ι ι ℂ := star U * B * U with hC
  have hCH : Cᴴ = C := by
    rw [hC, conjTranspose_mul, conjTranspose_mul, hB, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  have htr : trace (U * D * star U * B * (U * D * star U) * B) = trace (D * C * D * C) := by
    have h1 : U * D * star U * B * (U * D * star U) * B =
        U * (D * star U * B * U * D * star U * B) := by simp only [Matrix.mul_assoc]
    rw [h1, trace_mul_comm, hC]
    simp only [Matrix.mul_assoc]
  rw [htr, trace]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hml : C m l = star (C l m) := by
    have h := congrFun (congrFun hCH m) l
    rw [conjTranspose_apply] at h
    exact h.symm
  rw [hml, hD, mul_diagonal, diagonal_mul, ← queCore_C_apply B l m]
  rw [RCLike.star_def]
  have := Complex.mul_conj (C l m)
  push_cast
  linear_combination (((queCore_w μ E η l : ℝ) : ℂ) *
    ((queCore_w μ E η m : ℝ) : ℂ)) * this

private theorem queCore_re_trace_eq (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : η ≠ 0) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    (trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B)).re =
      ∑ l, ∑ m, queCore_w μ E η l * queCore_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
  rw [queCore_trace_eq hψ E hη B hB, Complex.re_sum]
  simp only [Complex.re_sum, Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] in
private theorem queCore_w_nonneg (μ : ι → ℝ) (E : ℝ) {η : ℝ} (hη : 0 ≤ η) (l : ι) :
    0 ≤ queCore_w μ E η l := by
  unfold queCore_w
  positivity

/-- `Re tr(Im G B Im G B) ≥ 0` for Hermitian `B`. -/
private theorem queCore_re_trace_nonneg (hψ : IsOrthoEigenbasis H μ ψ) (E : ℝ) {η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
    0 ≤ (trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B)).re := by
  rw [queCore_re_trace_eq hψ E hη.ne' B hB]
  refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => ?_
  have := queCore_w_nonneg μ E hη.le l
  have := queCore_w_nonneg μ E hη.le m
  have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
  positivity

/-- **Pointwise domination.** If `|μ_k - E| ≤ η` and `|μ_{k'} - E| ≤ η`, then
`|ψ_k^* B ψ_{k'}|² ≤ 4 η² Re tr(Im G B Im G B)`. -/
private theorem queCore_normSq_le (hψ : IsOrthoEigenbasis H μ ψ) {E η : ℝ}
    (hη : 0 < η) (B : Matrix ι ι ℂ) (hB : Bᴴ = B) {k k' : ι}
    (hk : |μ k - E| ≤ η) (hk' : |μ k' - E| ≤ η) :
    Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      4 * η ^ 2 * (trace (queImG H (E + η * Complex.I) * B *
        queImG H (E + η * Complex.I) * B)).re := by
  rw [queCore_re_trace_eq hψ E hη.ne' B hB]
  have hterm : ∀ l ∈ Finset.univ, ∀ m ∈ Finset.univ, 0 ≤ queCore_w μ E η l *
      queCore_w μ E η m * Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) := by
    intro l _ m _
    have := queCore_w_nonneg μ E hη.le l
    have := queCore_w_nonneg μ E hη.le m
    have := Complex.normSq_nonneg (star (ψ l) ⬝ᵥ (B *ᵥ ψ m))
    positivity
  have hsingle : queCore_w μ E η k * queCore_w μ E η k' *
      Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      ∑ l, ∑ m, queCore_w μ E η l * queCore_w μ E η m *
        Complex.normSq (star (ψ l) ⬝ᵥ (B *ᵥ ψ m)) :=
    le_trans (Finset.single_le_sum (hterm k (Finset.mem_univ k)) (Finset.mem_univ k'))
      (Finset.single_le_sum (fun l hl => Finset.sum_nonneg (hterm l hl))
        (Finset.mem_univ k))
  have hw : ∀ j, |μ j - E| ≤ η → 1 / (2 * η) ≤ queCore_w μ E η j := by
    intro j hj
    unfold queCore_w
    have hsq : (μ j - E) ^ 2 ≤ η ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hj 2
    have hden : 0 < (μ j - E) ^ 2 + η ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith
  have hwk := hw k hk
  have hwk' := hw k' hk'
  set c := Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) with hc
  have hc0 : 0 ≤ c := Complex.normSq_nonneg _
  have h2η : 0 < 2 * η := by positivity
  have hprod : 1 / (2 * η) * (1 / (2 * η)) ≤
      queCore_w μ E η k * queCore_w μ E η k' :=
    mul_le_mul hwk hwk' (by positivity) (queCore_w_nonneg μ E hη.le k)
  have hkey : c = 4 * η ^ 2 * (1 / (2 * η) * (1 / (2 * η)) * c) := by
    field_simp
    ring
  calc c = 4 * η ^ 2 * (1 / (2 * η) * (1 / (2 * η)) * c) := hkey
    _ ≤ 4 * η ^ 2 * (queCore_w μ E η k * queCore_w μ E η k' * c) := by
        gcongr
    _ ≤ _ := by gcongr

/-- Every Hermitian matrix has an orthonormal eigenbasis in the sense of
`IsOrthoEigenbasis` (Mathlib's `eigenvectorBasis`). -/
private theorem queCore_exists_basis (hH : H.IsHermitian) :
    ∃ (μ : ι → ℝ) (ψ : ι → ι → ℂ), IsOrthoEigenbasis H μ ψ := by
  refine ⟨hH.eigenvalues, fun k => ⇑(hH.eigenvectorBasis k), ?_, fun k => ?_⟩
  · intro k k'
    have h := orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal k k'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  · rw [hH.mulVec_eigenvectorBasis k]
    ext x
    simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

end Spectral

/-- `(ssfa2)` (`1_2:524-530`; RBM2D `QUEFromQDiff_normSq_le`, `:204`): for eigenvalues within `η` of `E`,
`|ψ_k^* B ψ_{k'}|² ≤ 4η² Re tr(Im G B Im G B)` at `z = E + iη`, any Hermitian `B`. -/
theorem normSq_le_trace {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (μ : ι → ℝ)
    (ψ : ι → ι → ℂ) (hψ : IsOrthoEigenbasis H μ ψ) (E η : ℝ) (hη : 0 < η) (B : Matrix ι ι ℂ)
    (hB : Bᴴ = B) (k k' : ι) (hk : |μ k - E| ≤ η) (hk' : |μ k' - E| ≤ η) :
    Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
      4 * η ^ 2 * (Matrix.trace (queImG H ((E : ℂ) + (η : ℂ) * Complex.I) * B *
        queImG H ((E : ℂ) + (η : ℂ) * Complex.I) * B)).re :=
  queCore_normSq_le hψ hη B hB hk hk'

section TraceAlgebra

variable {ι : Type*} [Fintype ι]

/-- `tr(Im G E_u Im G E_v) = -¼ (tr(G E_u G E_v) + conj tr(G E_u G E_v) - tr(G E_u G† E_v)
- tr(G E_v G† E_u))` for Hermitian `E_u, E_v`. -/
private theorem queCore_trace_imG (G Eu Ev : Matrix ι ι ℂ) (hEu : Euᴴ = Eu)
    (hEv : Evᴴ = Ev) :
    trace ((((2 : ℂ) * Complex.I)⁻¹ • (G - Gᴴ)) * Eu * (((2 : ℂ) * Complex.I)⁻¹ • (G - Gᴴ)) *
        Ev) =
      -(1 / 4 : ℂ) * (trace (G * Eu * G * Ev) + conj (trace (G * Eu * G * Ev)) -
        trace (G * Eu * Gᴴ * Ev) - trace (G * Ev * Gᴴ * Eu)) := by
  have h1 : trace (Gᴴ * Eu * G * Ev) = trace (G * Ev * Gᴴ * Eu) := by
    have : Gᴴ * Eu * G * Ev = (Gᴴ * Eu) * (G * Ev) := by simp only [Matrix.mul_assoc]
    rw [this, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : trace (Gᴴ * Eu * Gᴴ * Ev) = conj (trace (G * Eu * G * Ev)) := by
    rw [← RCLike.star_def, ← trace_conjTranspose]
    simp only [conjTranspose_mul, hEu, hEv]
    have : Gᴴ * Eu * Gᴴ * Ev = (Gᴴ * Eu * Gᴴ) * Ev := rfl
    rw [this, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hc : ((2 : ℂ) * Complex.I)⁻¹ * ((2 : ℂ) * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
    rw [← mul_inv, show (2 : ℂ) * Complex.I * (2 * Complex.I) = -4 by
      ring_nf; rw [Complex.I_sq]; ring]
    norm_num
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, Matrix.sub_mul,
    Matrix.mul_sub, trace_sub, smul_eq_mul]
  rw [h1, h2]
  linear_combination (trace (G * Eu * G * Ev) - trace (G * Ev * Gᴴ * Eu) -
    trace (G * Eu * Gᴴ * Ev) + conj (trace (G * Eu * G * Ev))) * hc

/-- Bilinear expansion of `tr(M B M B')` for `B = ∑ β_u E_u`, `B' = ∑ β'_v E_v`. -/
private theorem queCore_trace_sum {κ : Type*} [Fintype κ] (M : Matrix ι ι ℂ)
    (E : κ → Matrix ι ι ℂ) (β : κ → ℂ) :
    trace (M * (∑ u, β u • E u) * M * (∑ v, β v • E v)) =
      ∑ u, ∑ v, β u * β v * trace (M * E u * M * E v) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sum,
    trace_smul, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- `|∑_{u,v} β_u β_v g_{uv}| ≤ (∑|β|)² M` when `|g_{uv}| ≤ M`. -/
private theorem queCore_norm_dbl_le {κ : Type*} [Fintype κ] (β : κ → ℝ)
    (g : κ → κ → ℂ) {M : ℝ} (hg : ∀ u v, ‖g u v‖ ≤ M) :
    ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * g u v‖ ≤ (∑ u, |β u|) ^ 2 * M := by
  calc ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * g u v‖
      ≤ ∑ u, ∑ v, ‖((β u : ℂ) * (β v : ℂ)) * g u v‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => norm_sum_le _ _)
    _ ≤ ∑ u, ∑ v, |β u| * |β v| * M := by
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hg u v) (by positivity)
    _ = (∑ u, |β u|) ^ 2 * M := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-- `|∑_{u,v} β_u β_v h_{uv}| ≤ (∑|β|)² (ε + K)` when `∑ β = 0`, `|h_{uv} - P_{uv}| ≤ ε` and the
profile `P` varies along each row by at most `K` (row differences `P(u,v) - P(u,u)`). -/
private theorem queCore_norm_double_sum_le {κ : Type*} [Fintype κ] (β : κ → ℝ)
    (hβ0 : ∑ u, β u = 0) (h P : κ → κ → ℂ) {ε K : ℝ}
    (hε : ∀ u v, ‖h u v - P u v‖ ≤ ε) (hK : ∀ u v v', ‖P u v - P u v'‖ ≤ K) :
    ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * h u v‖ ≤ (∑ u, |β u|) ^ 2 * (ε + K) := by
  have hz : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * P u u = 0 := by
    have h0 : (∑ v, (β v : ℂ)) = 0 := by exact_mod_cast hβ0
    have e : ∀ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * P u u = (β u : ℂ) * P u u * ∑ v, (β v : ℂ) := by
      intro u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    simp only [e, h0, mul_zero, Finset.sum_const_zero]
  have hsplit : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * h u v =
      ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (h u v - P u v) +
      ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (P u v - P u u) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hz]
    ring
  rw [hsplit]
  calc _ ≤ ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (h u v - P u v)‖ +
        ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * (P u v - P u u)‖ := norm_add_le _ _
    _ ≤ (∑ u, |β u|) ^ 2 * ε + (∑ u, |β u|) ^ 2 * K :=
        add_le_add (queCore_norm_dbl_le β _ hε) (queCore_norm_dbl_le β _ fun u v => hK u v u)
    _ = _ := by ring

end TraceAlgebra

/-! ### The observable `B_c = ∑_u (c_u - L^{-d}) E_u` -/

section Observable

variable (d L W : ℕ) [NeZero L] [NeZero W]

private theorem queCore_blk_conjTranspose (a : Zd d L) : (queBlk d L W a)ᴴ = queBlk d L W a := by
  unfold queBlk
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  by_cases h : x ∈ Iblk d L W a <;> simp [h]

private theorem queCore_sum_blk :
    ∑ u, queBlk d L W u = ((W : ℂ) ^ d)⁻¹ • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  ext x y
  simp only [queBlk, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, Iblk, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul, mul_one]
    rw [Finset.sum_ite_eq]
    simp
  · simp [hxy]

private theorem queCore_obs_herm (c : Zd d L → ℝ) : (queObs d L W c)ᴴ = queObs d L W c := by
  unfold queObs
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [conjTranspose_smul, queCore_blk_conjTranspose, RCLike.star_def, Complex.conj_ofReal]

private theorem queCore_obs_eq (c : Zd d L → ℝ) :
    queObs d L W c = ∑ u, ((c u : ℝ) : ℂ) • queBlk d L W u -
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  unfold queObs
  simp only [Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.smul_sum, queCore_sum_blk, smul_smul]
  congr 1
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  push_cast
  field_simp
  ring

private theorem queCore_card : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
  simp [Zd, ZMod.card]

private theorem queCore_sum_beta (c : Zd d L → ℝ) (hc1 : ∑ u, c u = 1) :
    ∑ u, (c u - ((L : ℝ) ^ d)⁻¹) = 0 := by
  rw [Finset.sum_sub_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    queCore_card]
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  field_simp
  ring

private theorem queCore_sum_abs_beta (c : Zd d L → ℝ) (hc0 : ∀ u, 0 ≤ c u)
    (hc1 : ∑ u, c u = 1) :
    ∑ u, |c u - ((L : ℝ) ^ d)⁻¹| ≤ 2 := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  calc ∑ u, |c u - ((L : ℝ) ^ d)⁻¹| ≤ ∑ u, (c u + ((L : ℝ) ^ d)⁻¹) := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [abs_le]
        have := hc0 u
        have : 0 ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
        constructor <;> linarith
    _ = 2 := by
        rw [Finset.sum_add_distrib, hc1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          queCore_card]
        field_simp
        ring

end Observable

/-! ### Traces of the block insertions, integrability -/

section Integr

variable {d : ℕ}

private theorem queCore_trace_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (G H : Matrix ι ι ℂ)
    (e f : ι → ℂ) :
    Matrix.trace (G * Matrix.diagonal e * H * Matrix.diagonal f) =
      ∑ i, ∑ j, G i j * e j * H j i * f i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal]

/-- `tr(G E_u H E_v) = W^{-2d} ∑_{i∈[v], j∈[u]} G_{ij} H_{ji}`. -/
private theorem queCore_trace_blk (L W : ℕ) [NeZero L] [NeZero W]
    (G H : Matrix (Idx d L W) (Idx d L W) ℂ) (u v : Zd d L) :
    Matrix.trace (G * queBlk d L W u * H * queBlk d L W v) =
      ∑ i ∈ Iblk d L W v, ∑ j ∈ Iblk d L W u,
        ((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * (G i j * H j i) := by
  unfold queBlk
  rw [queCore_trace_diag]
  have key : ∀ i, ∑ j, G i j * (if j ∈ Iblk d L W u then ((W : ℂ) ^ d)⁻¹ else 0) * H j i *
      (if i ∈ Iblk d L W v then ((W : ℂ) ^ d)⁻¹ else 0) =
      if i ∈ Iblk d L W v then ∑ j ∈ Iblk d L W u,
        ((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * (G i j * H j i) else 0 := by
    intro i
    by_cases hi : i ∈ Iblk d L W v
    · simp only [hi, ↓reduceIte]
      calc _ = ∑ j, (if j ∈ Iblk d L W u then
            ((W : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹ * (G i j * H j i) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : j ∈ Iblk d L W u
            · simp only [hj, ↓reduceIte]; ring
            · simp [hj]
        _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
    · simp [hi]
  simp only [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- `tr(G E_u G E_v) = W^{-2d} ∑_{x∈[u], y∈[v]} G_{xy} G_{yx}`. -/
private theorem queCore_trace_GG (L W : ℕ) [NeZero L] [NeZero W]
    (G : Matrix (Idx d L W) (Idx d L W) ℂ) (u v : Zd d L) :
    Matrix.trace (G * queBlk d L W u * G * queBlk d L W v) =
      ((((W : ℂ) ^ d) ^ 2)⁻¹) * ∑ x ∈ Iblk d L W u, ∑ y ∈ Iblk d L W v, G x y * G y x := by
  rw [queCore_trace_blk, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `tr(G E_u G† E_v) = W^{-2d} ∑_{x∈[v], y∈[u]} |G_{xy}|²`. -/
private theorem queCore_trace_GGstar (L W : ℕ) [NeZero L] [NeZero W]
    (G : Matrix (Idx d L W) (Idx d L W) ℂ) (u v : Zd d L) :
    Matrix.trace (G * queBlk d L W u * Gᴴ * queBlk d L W v) =
      ((((W : ℂ) ^ d) ^ 2)⁻¹) * ∑ x ∈ Iblk d L W v, ∑ y ∈ Iblk d L W u,
        ((‖G x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [queCore_trace_blk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 : G x y * star (G x y) = ((‖G x y‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [Matrix.conjTranspose_apply, ← h1]
  ring

variable (sz : Sizes d) (n : ℕ)

private theorem queCore_norm_avg2_le (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    {C : ℝ} (hF : ∀ x y, ‖F x y‖ ≤ C) (a b : Zd d (sz.L n)) : ‖avg2 sz n F a b‖ ≤ C := by
  unfold avg2
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  rw [norm_mul, norm_inv, norm_pow, norm_pow, Complex.norm_natCast]
  have hS : ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * C) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ x ∈ Iblk d (sz.L n) (sz.W n) a,
        ‖∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * C := by
      intro x _
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ C fun y _ => hF x y).trans ?_
      rw [card_Iblk, nsmul_eq_mul]
      push_cast
      rfl
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [card_Iblk, nsmul_eq_mul]
    push_cast
    rfl
  calc ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ * ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) a,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y‖
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d) ^ 2)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * C)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C := by field_simp

private theorem queCore_meas_Gn {z : ℂ} (hz : z.im ≠ 0) (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω => sz.Gn n z ω x y := by
  have hc : Continuous fun s : Ω d (sz.L n) (sz.W n) => Gres (Xmat d (sz.L n) (sz.W n) s) z true :=
    continuous_green_of_isHermitian (continuous_Xmat d _ _)
      (fun s => Xmat_isHermitian d _ _ s) hz
  exact (hc.matrix_elem x y).measurable.comp (measurable_slice sz n)

open scoped Matrix.Norms.L2Operator in
private theorem queCore_norm_Gn_le {z : ℂ} (hz : z.im ≠ 0) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : ‖sz.Gn n z ω x y‖ ≤ |z.im|⁻¹ :=
  (norm_matrix_entry_le_opNorm _ x y).trans
    (norm_Gsig_le_inv_eta (seqXmat_isHermitian sz n ω) (abs_pos.mpr hz) le_rfl true)

private theorem queCore_meas_avg2 {z : ℂ}
    (F : sz.SeqΩ → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (hF : ∀ x y, Measurable fun ω => F ω x y) (a b : Zd d (sz.L n)) :
    Measurable fun ω => avg2 sz n (F ω) a b := by
  unfold avg2
  exact (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => hF x y).const_mul _

private theorem queCore_Tp_integrable {z : ℂ} (hz : z.im ≠ 0) (a b : Zd d (sz.L n)) :
    Integrable (fun ω => avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b)
      (Sizes.seqP sz) := by
  refine Integrable.of_bound (C := (|z.im|⁻¹) * (|z.im|⁻¹)) ?_ (ae_of_all _ fun ω => ?_)
  · exact (queCore_meas_avg2 sz n (z := z) _
      (fun x y => (queCore_meas_Gn sz n hz x y).mul (queCore_meas_Gn sz n hz y x)) a b).aestronglyMeasurable
  · refine queCore_norm_avg2_le sz n _ (fun x y => ?_) a b
    rw [norm_mul]
    exact mul_le_mul (queCore_norm_Gn_le sz n hz ω x y) (queCore_norm_Gn_le sz n hz ω y x)
      (norm_nonneg _) (by positivity)

private theorem queCore_Tm_integrable {z : ℂ} (hz : z.im ≠ 0) (a b : Zd d (sz.L n)) :
    Integrable (fun ω => avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b)
      (Sizes.seqP sz) := by
  refine Integrable.of_bound (C := (|z.im|⁻¹) ^ 2) ?_ (ae_of_all _ fun ω => ?_)
  · exact (queCore_meas_avg2 sz n (z := z) _
      (fun x y => Complex.measurable_ofReal.comp
        ((queCore_meas_Gn sz n hz x y).norm.pow_const 2)) a b).aestronglyMeasurable
  · refine queCore_norm_avg2_le sz n _ (fun x y => ?_) a b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (queCore_norm_Gn_le sz n hz ω x y) 2

end Integr

/-! ### The core: expectation of `Re tr(Im G B_c Im G B_c)` -/

section Core

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The complex four-term combination of the two block averages `T₊`, `T₋`. -/
private noncomputable def queCore_F (z : ℂ) (ω : sz.SeqΩ) (u v : Zd d (sz.L n)) : ℂ :=
  -(1 / 4 : ℂ) * (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v +
    conj (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v) -
    avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) v u -
    avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) u v)

private theorem queCore_trace_eq_sum (z : ℂ) (c : Zd d (sz.L n) → ℝ) (ω : sz.SeqΩ) :
    Matrix.trace (queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c *
      queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c) =
      ∑ u, ∑ v, ((((c u - ((sz.L n : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) *
        (((c v - ((sz.L n : ℝ) ^ d)⁻¹ : ℝ)) : ℂ)) * queCore_F sz n z ω u v := by
  unfold queObs
  rw [queCore_trace_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  unfold queImG
  rw [queCore_trace_imG _ _ _ (queCore_blk_conjTranspose _ _ _ u) (queCore_blk_conjTranspose _ _ _ v)]
  have hG : RBM.green (sz.seqXmat n ω) z = sz.Gn n z ω :=
    (RBM.Ind.ContinuityNet.cont_Gres_true_eq_green _ _).symm
  rw [hG]
  simp only [queCore_trace_GG, queCore_trace_GGstar]
  rfl

private theorem queCore_F_integrable {z : ℂ} (hz : z.im ≠ 0) (u v : Zd d (sz.L n)) :
    Integrable (fun ω => queCore_F sz n z ω u v) (Sizes.seqP sz) := by
  have hT := queCore_Tp_integrable sz n hz u v
  have hF := queCore_Tm_integrable sz n hz u v
  have hF' := queCore_Tm_integrable sz n hz v u
  have hTc : Integrable (fun ω => conj (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v))
      (Sizes.seqP sz) := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  exact (((hT.add hTc).sub hF').sub hF).const_mul _

private theorem queCore_integral_F {z : ℂ} (hz : z.im ≠ 0) (u v : Zd d (sz.L n)) :
    ∫ ω, queCore_F sz n z ω u v ∂(Sizes.seqP sz) =
      -(1 / 4 : ℂ) * ((∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v ∂(Sizes.seqP sz)) +
        conj (∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v ∂(Sizes.seqP sz)) -
        (∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) v u ∂(Sizes.seqP sz)) -
        (∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) u v ∂(Sizes.seqP sz))) := by
  have hT := queCore_Tp_integrable sz n hz u v
  have hF := queCore_Tm_integrable sz n hz u v
  have hF' := queCore_Tm_integrable sz n hz v u
  have hTc : Integrable (fun ω => conj (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v))
      (Sizes.seqP sz) := by
    have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hT
    simpa using this
  have h0 : Integrable (fun ω => avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v +
      conj (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v)) (Sizes.seqP sz) :=
    hT.add hTc
  have h1 : Integrable (fun ω => avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v +
      conj (avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v) -
      avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) v u) (Sizes.seqP sz) := h0.sub hF'
  unfold queCore_F
  rw [integral_const_mul, integral_sub h1 hF, integral_sub h0 hF', integral_add hT hTc,
    integral_conj]

private theorem queCore_four_sum {κ : Type*} [Fintype κ] (b : κ → ℂ) (A B C D : κ → κ → ℂ) :
    ∑ u, ∑ v, (b u * b v) * (-(1 / 4 : ℂ) * (A u v + B u v - C u v - D u v)) =
      -(1 / 4 : ℂ) * ((∑ u, ∑ v, (b u * b v) * A u v) + (∑ u, ∑ v, (b u * b v) * B u v) -
        (∑ u, ∑ v, (b u * b v) * C u v) - (∑ u, ∑ v, (b u * b v) * D u v)) := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

/-- **The core** (`(que0)`, `1_2:531-537`; RBM2D `QUEFromQDiff_core`, `:564`): if the expectation half of
`QDiff` holds at `z` with error `ε` and the profiles vary along rows by at most `K`, then for every
probability vector `c` on the blocks, `X_c ≥ 0`, `X_c` is integrable and `E X_c ≤ 4 (K + ε)`. -/
theorem queX_core {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (hz0 : 0 < z.im) (ε K : ℝ)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
          profPM sz n z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n z a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n),
      ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ K ∧ ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ K)
    (c : Zd d (sz.L n) → ℝ) (hc0 : ∀ u, 0 ≤ c u) (hc1 : ∑ u, c u = 1) :
    Integrable (queX sz n z c) (Sizes.seqP sz) ∧ (∀ ω, 0 ≤ queX sz n z c ω) ∧
      ∫ ω, queX sz n z c ω ∂(Sizes.seqP sz) ≤ 4 * (K + ε) := by
  have hz : z.im ≠ 0 := hz0.ne'
  set β : Zd d (sz.L n) → ℝ := fun u => c u - ((sz.L n : ℝ) ^ d)⁻¹ with hβ
  set Xc : sz.SeqΩ → ℂ := fun ω =>
    Matrix.trace (queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c *
      queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c) with hXc
  have hXc_eq : Xc = fun ω => ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
      queCore_F sz n z ω u v :=
    funext fun ω => queCore_trace_eq_sum sz n z c ω
  have hXc_int : Integrable Xc (Sizes.seqP sz) := by
    rw [hXc_eq]
    refine integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => ?_
    exact (queCore_F_integrable sz n hz u v).const_mul _
  have hX : queX sz n z c = fun ω => (Xc ω).re := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]; exact hXc_int.re
  · intro ω
    obtain ⟨μ, ψ, hψ⟩ := queCore_exists_basis (seqXmat_isHermitian sz n ω)
    have hzeq : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im z).symm
    have h := queCore_re_trace_nonneg hψ z.re hz0 (queObs d (sz.L n) (sz.W n) c)
      (queCore_obs_herm _ _ _ c)
    rw [← hzeq] at h
    exact h
  · have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hQ 0 0).1
    have hint : ∫ ω, Xc ω ∂(Sizes.seqP sz) = ∑ u, ∑ v, (((β u : ℝ) : ℂ) * ((β v : ℝ) : ℂ)) *
        ∫ ω, queCore_F sz n z ω u v ∂(Sizes.seqP sz) := by
      rw [hXc_eq, integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ =>
        (queCore_F_integrable sz n hz u v).const_mul _]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum _ fun v _ => (queCore_F_integrable sz n hz u v).const_mul _]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul]
    set Ip : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun u v =>
      ∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) u v ∂(Sizes.seqP sz) with hIp
    set Im' : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun u v =>
      ∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) u v ∂(Sizes.seqP sz) with hIm
    have hβ0 : ∑ u, β u = 0 := queCore_sum_beta d (sz.L n) c hc1
    have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 0 0).1
    have hSp : ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v‖ ≤ (∑ u, |β u|) ^ 2 * (ε + K) :=
      queCore_norm_double_sum_le β hβ0 Ip (profPP sz n z) (fun u v => (hQ u v).2)
        (fun u v v' => (hK u v v').2)
    have hSm : ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v‖ ≤ (∑ u, |β u|) ^ 2 * (ε + K) :=
      queCore_norm_double_sum_le β hβ0 Im' (profPM sz n z) (fun u v => (hQ u v).1)
        (fun u v v' => (hK u v v').1)
    have hsum2 : (∑ u, |β u|) ^ 2 ≤ 4 := by
      have h := queCore_sum_abs_beta d (sz.L n) c hc0 hc1
      have h0 : 0 ≤ ∑ u, |β u| := Finset.sum_nonneg fun u _ => abs_nonneg _
      nlinarith
    -- the swap `u ↔ v` of the second block average
    have hswap : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' v u =
        ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
    have hconj : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * conj (Ip u v) =
        conj (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) := by
      simp only [map_sum, map_mul, Complex.conj_ofReal]
    have hmain : ∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * ∫ ω, queCore_F sz n z ω u v ∂(Sizes.seqP sz) =
        -(1 / 4 : ℂ) * ((∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) +
          conj (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v)) := by
      have h1 : ∀ u v, ∫ ω, queCore_F sz n z ω u v ∂(Sizes.seqP sz) =
          -(1 / 4 : ℂ) * (Ip u v + conj (Ip u v) - Im' v u - Im' u v) :=
        fun u v => queCore_integral_F sz n hz u v
      simp only [h1]
      rw [queCore_four_sum (fun u => (β u : ℂ)) Ip (fun u v => conj (Ip u v)) (fun u v => Im' v u)
        Im', hconj, hswap]
    rw [hX]
    have hre : (∫ ω, (Xc ω).re ∂(Sizes.seqP sz)) = (∫ ω, Xc ω ∂(Sizes.seqP sz)).re :=
      integral_re hXc_int
    change (∫ ω, (Xc ω).re ∂(Sizes.seqP sz)) ≤ _
    rw [hre]
    calc (∫ ω, Xc ω ∂(Sizes.seqP sz)).re ≤ ‖∫ ω, Xc ω ∂(Sizes.seqP sz)‖ := Complex.re_le_norm _
      _ = ‖-(1 / 4 : ℂ) * ((∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) +
          conj (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v) -
          (∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v))‖ := by rw [hint, hmain]
      _ ≤ (1 / 4) * (‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v‖ +
          ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Ip u v‖ +
          ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v‖ +
          ‖∑ u, ∑ v, ((β u : ℂ) * (β v : ℂ)) * Im' u v‖) := by
        rw [norm_mul]
        have h4 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
        rw [h4]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add le_rfl ?_)) le_rfl)) le_rfl
        rw [RCLike.norm_conj]
      _ ≤ (1 / 4) * (4 * ((∑ u, |β u|) ^ 2 * (ε + K))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        linarith
      _ ≤ 4 * (K + ε) := by
        have : (∑ u, |β u|) ^ 2 * (ε + K) ≤ 4 * (ε + K) :=
          mul_le_mul_of_nonneg_right hsum2 (by linarith)
        nlinarith

end Core

/-! ### The failure events are dominated by `4 N² η² X_c` -/

section Events

private theorem queCore_blk_cross (d L W : ℕ) [NeZero L] [NeZero W] (ψ φ : Idx d L W → ℂ)
    (u : Zd d L) :
    star ψ ⬝ᵥ (queBlk d L W u *ᵥ φ) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W u, star (ψ x) * φ x := by
  unfold queBlk
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have key : ∀ x, star (ψ x) * ((if x ∈ Iblk d L W u then ((W : ℂ) ^ d)⁻¹ else 0) * φ x) =
      if x ∈ Iblk d L W u then ((W : ℂ) ^ d)⁻¹ * (star (ψ x) * φ x) else 0 := by
    intro x
    by_cases h : x ∈ Iblk d L W u
    · simp only [h, ↓reduceIte]; ring
    · simp [h]
  simp only [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

private theorem queCore_quad_blk (d L W : ℕ) [NeZero L] [NeZero W] (ψ : Idx d L W → ℂ)
    (u : Zd d L) :
    star ψ ⬝ᵥ (queBlk d L W u *ᵥ ψ) =
      ((((W : ℝ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W u, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [queCore_blk_cross]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

private theorem queCore_sub_of_normSq {W N η X c : ℝ} (hW : 0 < W) (hN : 0 < N) (Z : ℂ)
    (hZ : (W ^ c)⁻¹ / N ≤ ‖Z‖) (hdom : Complex.normSq Z ≤ 4 * η ^ 2 * X) :
    W ^ (-(2 * c)) ≤ 4 * N ^ 2 * η ^ 2 * X := by
  have hWc : 0 < W ^ c := Real.rpow_pos_of_pos hW c
  have h1 : W ^ (-(2 * c)) = ((W ^ c)⁻¹) ^ 2 := by
    rw [Real.rpow_neg hW.le, show 2 * c = c * 2 by ring, Real.rpow_mul hW.le, Real.rpow_two,
      inv_pow]
  have h2 : (W ^ c)⁻¹ ≤ ‖Z‖ * N := (div_le_iff₀ hN).1 hZ
  have h3 : ((W ^ c)⁻¹) ^ 2 ≤ (‖Z‖ * N) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [h1]
  calc ((W ^ c)⁻¹) ^ 2 ≤ (‖Z‖ * N) ^ 2 := h3
    _ = N ^ 2 * Complex.normSq Z := by rw [mul_pow, Complex.sq_norm]; ring
    _ ≤ N ^ 2 * (4 * η ^ 2 * X) := mul_le_mul_of_nonneg_left hdom (by positivity)
    _ = _ := by ring

private theorem queCore_rpow_sub {W : ℝ} (hW : 0 < W) (d : ℕ) (c : ℝ) :
    W ^ ((d : ℝ) - c) = W ^ d * (W ^ c)⁻¹ := by
  rw [Real.rpow_sub hW, Real.rpow_natCast, div_eq_mul_inv]

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- `(Meq:QUE)` event `⊆ {W^{-2c} ≤ 4N²η² X_{δ_a}}` (RBM2D `QUEFromQDiff_queBad_sub`, `:671`), when the
window `𝓘_E(ε₀)` lies in `[E - η, E + η]`. -/
theorem queBad_sub {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E η : ℝ) (hη : 0 < η)
    (hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η)
    (a : Zd d (sz.L n)) :
    {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ⊆
      {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        4 * Nsz sz n ^ 2 * η ^ 2 *
          queX sz n ((E : ℂ) + (η : ℂ) * Complex.I) (fun u => if u = a then 1 else 0) ω} := by
  intro ω hω
  obtain ⟨μ, ψ, hψ, i, j, hi, hj, hbad⟩ := hω
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hNeq : ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) = Nsz sz n := rfl
  have hBeq : queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0) =
      queBlk d (sz.L n) (sz.W n) a -
        ((((sz.W n * sz.L n) ^ d : ℕ) : ℂ))⁻¹ • (1 : Matrix (Idx d (sz.L n) (sz.W n))
          (Idx d (sz.L n) (sz.W n)) ℂ) := by
    rw [queCore_obs_eq]
    congr 1
    simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hdom := normSq_le_trace (sz.seqXmat n ω) μ ψ hψ E η hη
    (queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0)) (queCore_obs_herm _ _ _ _) i j
    (hwin _ hi) (hwin _ hj)
  have hWc : ((sz.W n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have hNc : ((((sz.W n * sz.L n) ^ d : ℕ) : ℂ)) ≠ 0 := by
    have : ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) ≠ 0 := by rw [hNeq]; exact hN.ne'
    exact_mod_cast this
  have hZ : star (ψ i) ⬝ᵥ (queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0) *ᵥ ψ j) =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ((∑ x ∈ Iblk d (sz.L n) (sz.W n) a, star (ψ i x) * ψ j x) -
        (((sz.W n : ℕ) : ℂ) ^ d / (((sz.W n * sz.L n) ^ d : ℕ) : ℂ)) *
          (if i = j then 1 else 0)) := by
    rw [hBeq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, queCore_blk_cross, hψ.1 i j, smul_eq_mul]
    field_simp
  have hnorm : (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n ≤
      ‖star (ψ i) ⬝ᵥ (queObs d (sz.L n) (sz.W n) (fun u => if u = a then 1 else 0) *ᵥ ψ j)‖ := by
    rw [hZ, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have h1 := hbad
    rw [queCore_rpow_sub hW, hNeq] at h1
    calc (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  exact queCore_sub_of_normSq hW hN _ hnorm hdom

/-- `(Meq:QUE2)` event `⊆ {W^{-2c} ≤ 4N²η² X_{1_A/|A|}}` (RBM2D `QUEFromQDiff_que2Bad_sub`, `:704`). -/
theorem que2Bad_sub {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E η : ℝ) (hη : 0 < η)
    (hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η)
    (A : Finset (Zd d (sz.L n))) (hA : A.Nonempty) :
    {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ⊆
      {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        4 * Nsz sz n ^ 2 * η ^ 2 *
          queX sz n ((E : ℂ) + (η : ℂ) * Complex.I)
            (fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0) ω} := by
  intro ω hω
  obtain ⟨μ, ψ, hψ, k, hk, hbad⟩ := hω
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hNeq : ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) = Nsz sz n := rfl
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  set cA : Zd d (sz.L n) → ℝ := fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0 with hcA
  have hdom := normSq_le_trace (sz.seqXmat n ω) μ ψ hψ E η hη
    (queObs d (sz.L n) (sz.W n) cA) (queCore_obs_herm _ _ _ _) k k (hwin _ hk) (hwin _ hk)
  set S : Zd d (sz.L n) → ℝ := fun u => ∑ x ∈ Iblk d (sz.L n) (sz.W n) u, ‖ψ k x‖ ^ 2 with hS
  set r : ℝ := (A.card : ℝ)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ a ∈ A, S a - (Nsz sz n)⁻¹ with hr
  have hunit : star (ψ k) ⬝ᵥ ψ k = 1 := by rw [hψ.1 k k]; simp
  have hC : star (ψ k) ⬝ᵥ (queObs d (sz.L n) (sz.W n) cA *ᵥ ψ k) = (r : ℂ) := by
    rw [queCore_obs_eq, Matrix.sub_mulVec, Matrix.sum_mulVec, dotProduct_sub, dotProduct_sum,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hunit]
    simp only [Matrix.smul_mulVec, dotProduct_smul, queCore_quad_blk, smul_eq_mul]
    have hsum : ∑ u, ((cA u : ℝ) : ℂ) * ((((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹ * S u : ℝ) : ℂ) =
        (((A.card : ℝ)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ a ∈ A, S a : ℝ) : ℂ) := by
      have h1 : ∀ u, ((cA u : ℝ) : ℂ) * ((((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹ * S u : ℝ) : ℂ) =
          if u ∈ A then (((A.card : ℝ)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * S u) : ℝ) : ℂ) else 0 := by
        intro u
        by_cases hu : u ∈ A
        · simp only [hcA, hu, ↓reduceIte]
          push_cast
          ring
        · simp [hcA, hu]
      simp only [h1]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [hsum, hr]
    have : ((((sz.W n * sz.L n) ^ d : ℕ) : ℂ))⁻¹ = (((Nsz sz n)⁻¹ : ℝ) : ℂ) := by
      rw [← hNeq]; push_cast; rfl
    rw [this]
    push_cast
    ring
  rw [hC] at hdom
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hid : (∑ a ∈ A, S a) - ((sz.W n : ℕ) : ℝ) ^ d / Nsz sz n * (A.card : ℝ) =
      (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * r := by
    rw [hr]
    field_simp
  have hbad' := hbad
  rw [queCore_rpow_sub hW, hNeq] at hbad'
  have hbad'' : (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ * (A.card : ℝ) / Nsz sz n) ≤
      (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * |r| := by
    have h2 : |A.sum S - ((sz.W n : ℕ) : ℝ) ^ d / Nsz sz n * (A.card : ℝ)| =
        (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * |r| := by
      rw [show A.sum S = ∑ a ∈ A, S a from rfl, hid, abs_mul, abs_of_pos (by positivity)]
    rw [← h2]
    exact hbad'
  have hnorm : (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n ≤ ‖(r : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine le_of_mul_le_mul_left (a := (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d) ?_ (by positivity)
    calc (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * ((((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n)
        = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ * (A.card : ℝ) / Nsz sz n := by ring
      _ ≤ _ := hbad''
  exact queCore_sub_of_normSq hW hN _ hnorm hdom

end Events

/-! ### Markov -/

/-- Markov (RBM2D `QUEFromQDiff_markov`, `:798`). -/
theorem queMarkov {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω) {s T : ℝ} (hs : 0 < s)
    (hT : ∫ ω, f ω ∂P ≤ T) (S : Set Ω) (hS : S ⊆ {ω | s ≤ f ω}) :
    P S ≤ ENNReal.ofReal (T / s) := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hf s
  have hreal : P.real {ω | s ≤ f ω} ≤ T / s := by
    rw [le_div_iff₀ hs, mul_comm]
    exact h.trans hT
  calc P S ≤ P {ω | s ≤ f ω} := measure_mono hS
    _ = ENNReal.ofReal (P.real {ω | s ≤ f ω}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (T / s) := ENNReal.ofReal_le_ofReal hreal


/-! ## 4. Compiled nonempty instances at `d = 3` on `SizesInst.sz0` (CLAUDE.md §4 step 2)

Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `κ = 𝔡 = 1/10`, `z = zI = 1/2 + i N^{-4/5}`.
`inst_thetaDiff`: `thetaDiff` at `(d, 𝔡, κ) = (3, 1/10, 1/10)`, `L = 4`, `g = 1/64`.  `inst_queBad_sub`:
`queBad_sub` at `ε₀ = 1/30`, `c = 1/60`, `E = 0`, `η = 1`; the window hypothesis is discharged:
`32^{-1/30} · (1/64) · 32^{3/2} / 2097152 ≤ 1`. -/

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- `thetaDiff` at `d = 3`, `L = 4`, `ilambda = 1/64 ≤ 𝔡⁻¹ = 10`, `z = zI`, both `Θ^{(+,-)}` and `Θ^{(+,+)}`. -/
theorem inst_thetaDiff : ∃ C : ℝ, 0 < C ∧ ∀ b b' : Zd 3 4,
    ‖Theta 3 4 (1 / 64) (((‖msc zI‖ ^ 2 : ℝ)) : ℂ) 0 b - Theta 3 4 (1 / 64) (((‖msc zI‖ ^ 2 : ℝ)) : ℂ) 0 b'‖ ≤
        C * ((1 / 64 : ℝ) ^ 2)⁻¹ ∧
      ‖Theta 3 4 (1 / 64) (msc zI ^ 2) 0 b - Theta 3 4 (1 / 64) (msc zI ^ 2) 0 b'‖ ≤ C * ((1 / 64 : ℝ) ^ 2)⁻¹ := by
  obtain ⟨C, hC, H⟩ := thetaDiff 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  exact ⟨C, hC, fun b b' => H 4 (by norm_num) (1 / 64) (by norm_num) (by norm_num) zI zI_im_pos zI_im_le zI_re_le 0 b b'⟩

/-- The window `𝓘_0(1/30)` at `sz0`, `n = 0` lies in `[-1, 1]`: `32^{-1/30} · (1/64) · 32^{3/2} / 2097152 ≤ 1`. -/
private theorem queCore_inst_window :
    ∀ x : ℝ, queWindow 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) 0 x → |x - 0| ≤ 1 := by
  intro x hx
  unfold queWindow at hx
  obtain ⟨hL, hW, -, hlam⟩ := sz0_values
  rw [hL, hW, hlam] at hx
  refine hx.trans ?_
  have h1 : ((32 : ℕ) : ℝ) ^ (-(1 / 30 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h2 : ((32 : ℕ) : ℝ) ^ (((3 : ℕ) : ℝ) / 2) ≤ ((32 : ℕ) : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h3 : ((32 : ℕ) : ℝ) ^ (2 : ℝ) = 1024 := by
    rw [Real.rpow_two]; norm_num
  rw [h3] at h2
  have h4 : (0 : ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1 / 30 : ℝ)) := by positivity
  have h5 : (0 : ℝ) ≤ ((32 : ℕ) : ℝ) ^ (((3 : ℕ) : ℝ) / 2) := by positivity
  calc ((32 : ℕ) : ℝ) ^ (-(1 / 30 : ℝ)) * ((1 / 64 : ℝ) * ((32 : ℕ) : ℝ) ^ (((3 : ℕ) : ℝ) / 2) /
        ((((32 * 4) ^ 3 : ℕ)) : ℝ))
      ≤ 1 * ((1 / 64 : ℝ) * 1024 / ((((32 * 4) ^ 3 : ℕ)) : ℝ)) := by
        refine mul_le_mul h1 ?_ (by positivity) (by norm_num)
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ 1 := by norm_num

/-- **`queBad_sub` at the instance** (`sz0`, `n = 0`, `ε₀ = 1/30`, `c = 1/60`, `E = 0`, `η = 1`): the event
`(Meq:QUE)` at the block `a` is inside `{W^{-2c} ≤ 4 N² η² X_{δ_a}}`; the window hypothesis is discharged. -/
theorem inst_queBad_sub : ∀ a : Zd 3 (sz0.L 0),
    {ω | queBadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 a (sz0.seqXmat 0 ω)} ⊆
      {ω | ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))) ≤
        4 * Nsz sz0 0 ^ 2 * (1 : ℝ) ^ 2 *
          queX sz0 0 (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)
            (fun u => if u = a then 1 else 0) ω} :=
  fun a => queBad_sub sz0 0 (1 / 30) (1 / 60) 0 1 one_pos queCore_inst_window a

/-! ### Instances of the remaining targets (anonymous `example`s) -/

/-- `que2Bad_sub` at the instance, `A = {0}`. -/
example := que2Bad_sub sz0 0 (1 / 30) (1 / 60) 0 1 one_pos queCore_inst_window ({0} : Finset (Zd 3 (sz0.L 0)))
  (Finset.singleton_nonempty _)

/-- `normSq_le_trace` on `Fin 2`: `H = diag(1/2, -1/2)`, `E = 0`, `η = 1`, `B = σ_x`, `k = 0`, `k' = 1`. -/
example :
    Complex.normSq (star ((fun k : Fin 2 => (Pi.single k 1 : Fin 2 → ℂ)) 0) ⬝ᵥ
        ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (fun k : Fin 2 => (Pi.single k 1 : Fin 2 → ℂ)) 1)) ≤
      4 * (1 : ℝ) ^ 2 *
        (Matrix.trace (queImG (Matrix.diagonal (fun k : Fin 2 => if k = 0 then (1 / 2 : ℂ) else -(1 / 2))) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) *
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
          queImG (Matrix.diagonal (fun k : Fin 2 => if k = 0 then (1 / 2 : ℂ) else -(1 / 2))) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) *
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))).re := by
  refine normSq_le_trace (Matrix.diagonal (fun k : Fin 2 => if k = 0 then (1 / 2 : ℂ) else -(1 / 2)))
    (fun k => if k = 0 then 1 / 2 else -(1 / 2)) (fun k => Pi.single k 1) ?_ 0 1 one_pos
    (!![0, 1; 1, 0]) ?_ 0 1 ?_ ?_
  · refine ⟨fun k k' => ?_, fun k => ?_⟩
    · simp [Pi.single_apply, eq_comm]
    · ext x
      by_cases hx : x = k <;> fin_cases k <;> fin_cases x <;> simp [Matrix.mulVec_diagonal]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · norm_num
  · norm_num


/-- `queMarkov` on `Fin 2` with `P = (1/2) count`, `f i = i`, `s = 1`, `T = 1/2`, `S = {1}`. -/
example : ((2 : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin 2))) {1} ≤ ENNReal.ofReal ((1 / 2 : ℝ) / 1) := by
  have : IsProbabilityMeasure ((2 : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin 2))) :=
    ⟨by simp [Measure.count_apply, ENNReal.inv_mul_cancel]⟩
  refine queMarkov ((2 : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin 2))) (fun i => ((i : ℕ) : ℝ))
    (Integrable.of_finite) (fun i => Nat.cast_nonneg _) one_pos ?_ {1} ?_
  · rw [integral_smul_measure, integral_count]
    simp [Fin.sum_univ_two]
  · intro i hi
    simp at hi
    simp [hi]

/-- `queX_core` at `sz0`, `n = 0`, `z = zI`, `c = δ_0`.  `hQ` is the expectation half of `QDiff` at `zI` with error `ε`
(the pin of another gate, kept as a hypothesis); the row-difference hypothesis is discharged from `thetaDiff`,
with `K = C (ilambda²)⁻¹ / W^d`, `‖msc zI‖ < 1`. -/
example (ε : ℝ)
    (hQ : ∀ a b : Zd 3 (sz0.L 0),
      ‖(∫ ω, avg2 sz0 0 (fun x y => ((‖sz0.Gn 0 zI ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
          profPM sz0 0 zI a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz0 0 (fun x y => sz0.Gn 0 zI ω x y * sz0.Gn 0 zI ω y x) a b ∂(Sizes.seqP sz0)) -
          profPP sz0 0 zI a b‖ ≤ ε) :
    ∃ K : ℝ, Integrable (queX sz0 0 zI (fun u => if u = 0 then 1 else 0)) (Sizes.seqP sz0) ∧
      (∀ ω, 0 ≤ queX sz0 0 zI (fun u => if u = 0 then 1 else 0) ω) ∧
      ∫ ω, queX sz0 0 zI (fun u => if u = 0 then 1 else 0) ω ∂(Sizes.seqP sz0) ≤ 4 * (K + ε) := by
  obtain ⟨C, hC, H⟩ := thetaDiff 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  have hlam : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have hW : (0 : ℝ) < ((sz0.W 0 : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos 0
  have hm1 : ‖msc zI‖ < 1 := norm_msc_lt_one zI_im_pos
  have hm0 : 0 ≤ ‖msc zI‖ := norm_nonneg _
  have key : ∀ (ξ Θ1 Θ2 : ℂ), ‖ξ‖ ≤ 1 →
      ‖ξ * Θ1 / (((sz0.W 0 : ℕ) : ℂ) ^ 3) - ξ * Θ2 / (((sz0.W 0 : ℕ) : ℂ) ^ 3)‖ ≤
        ‖Θ1 - Θ2‖ / (((sz0.W 0 : ℕ) : ℝ) ^ 3) := by
    intro ξ Θ1 Θ2 hξ
    rw [← sub_div, ← mul_sub, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    calc ‖ξ‖ * ‖Θ1 - Θ2‖ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 ≤ 1 * ‖Θ1 - Θ2‖ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 := by
          gcongr
      _ = _ := by rw [one_mul]
  refine ⟨C * ((sz0.lam 0 ^ 2)⁻¹) / ((sz0.W 0 : ℕ) : ℝ) ^ 3, queX_core sz0 0 zI zI_im_pos ε _ hQ ?_
    (fun u => if u = 0 then 1 else 0) (fun u => by split_ifs <;> norm_num) (by simp)⟩
  intro a b b'
  have hT := H (sz0.L 0) (sz0.three_le_L 0) (sz0.lam 0) (by rw [hlam]; norm_num) (by rw [hlam]; norm_num)
    zI zI_im_pos zI_im_le zI_re_le a b b'
  refine ⟨(key _ _ _ ?_).trans (div_le_div_of_nonneg_right hT.1 (by positivity)),
    (key _ _ _ ?_).trans (div_le_div_of_nonneg_right hT.2 (by positivity))⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  · rw [norm_pow]
    nlinarith

end Inst


end RBM.Endpoints

end
