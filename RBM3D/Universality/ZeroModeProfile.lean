/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.OU
import RBM3D.Endpoints
import RBM3D.Propagator.Prop6Hold
import RBM3D.Green.IBP
import RBM3D.Path.Walk
import RBM3D.Induction.Split

/-!
# UN-51a: the zero-mode profile `S̃ = (1 - ζ) S + ζ N⁻¹ J` and the §7.2 layer interface (T2276)

Port of `RBM2D/Universality/ZeroModeProfile.lean` (`c9a24cf`, 1269 lines) to `d ≥ 3`.
Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex:524-543` (QUE scale),
`(prop:ThfadC0)` (property 8 of `lem_propTH`); RBM2D paper (arXiv:2503.07606) `1-2:330-422` for the
flow `𝐇_t` ("details identical to Section 7.2 of [YY_25]").

Contents.
* §1 the profile `S̃` on `Idx d L W` (row sums, `S̃ = S̃^(B) ⊗ S_W`, the OU variance family
  `ouVar d L W lam t` is the coordinate family of `S̃` at `ζ = 1 - e^{-t}`).
* §2 `S̃^(B)` and `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹` on `Z_L^d`: `Θ̃ = Θ_T + α J` (`ThetaTilde_eq`) and the
  `d ≥ 3` oscillation bound `norm_ThetaTilde_sub_le` (constant `C(d, 𝔡, κ)`, uniform in `L`, `ζ`,
  no `log L`), proved from `prop5to8_holds` as the merged `thetaDiff` (`Main/QUECore.lean:105`,
  copied privately); the row differences `profTilde_rowDiff` of the profiles.
* §3 the layer constants `ouTauMax`, `ouEtaLL`, `ouEtaQ`.
* §4 the profiles `profPMTilde`, `profPPTilde` and the pins `UNOULL`, `UNOUEq747`, `UNG1Row`,
  `UNG2bRow` (definitions only).
* §5 `ouDiag_of_ouLL` (Markov and a union bound inside `ouP`) and §6 the assembly `ouRow_of_pins`.
* §7 compiled instances (`RBM.Univ.ZeroModeProfileInst`).

Replaced at `d ≥ 3` (not a port): the `d = 2` oscillation bound `90 (1 + log L)`, the entry bound
`S̃ ≤ (5 W²)⁻¹`, the "no flat profile" lemma, `OULL`/`OUEq747`/`G1Row`/`G2bRow` (the `(7.47)` form
`W^δ Meta^{-3}` becomes `QDiff`'s expectation half at `η_Q = etaQ sz n (𝔡/3)`), `ouTauMax`.
Helpers that are not pinned by the ticket are `private` or carry the prefix `ZeroModeProfile_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ

open MeasureTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
open scoped NNReal ENNReal

/-! ## §1 The profile `S̃ = (1 - ζ) S + ζ N⁻¹ J` on `Idx d L W` -/

/-- The OU time change `ζ(t) = 1 - e^{-t}` (RBM2D `ouZeta`, `ZeroModeProfile.lean:53`;
`E|h_{xy}|² = e^{-t} S_{xy} + (1 - e^{-t}) N⁻¹` for `𝐇_t`). -/
def ouZeta (t : ℝ) : ℝ := 1 - Real.exp (-t)

/-- `S̃_{xy} = (1 - ζ) S_{xy} + ζ N⁻¹`, `S = svarF d L W lam`, `N = (W L)^d`. -/
def Stilde (d L W : ℕ) [NeZero L] [NeZero W] (lam ζ : ℝ) (i j : Idx d L W) : ℝ :=
  (1 - ζ) * svarF d L W lam i j + ζ / (((W * L) ^ d : ℕ) : ℝ)

/-- The all-ones matrix `J` on `Z_L^d`. -/
def Jmat (d L : ℕ) : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun _ _ => 1

/-- `S̃^(B) = (1 - ζ) S^(B)(lam) + (ζ / L^d) J`. -/
def SBtilde (d L : ℕ) (lam ζ : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((((1 - ζ : ℝ)) : ℂ)) • SB d L lam + ((ζ : ℂ) / (L : ℂ) ^ d) • Jmat d L

/-- `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹` (`Ring.inverse`, as the merged `RBM.Theta`). -/
def ThetaTilde (d L : ℕ) [NeZero L] (lam ζ : ℝ) (ξ : ℂ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - ξ • SBtilde d L lam ζ)

/-- The two spectral parameters of the profiles: `m²` (`σ = true`), `|m|²` (`σ = false`). -/
def xiQ (z : ℂ) (σ : Bool) : ℂ :=
  if σ then msc z ^ 2 else (((‖msc z‖ ^ 2 : ℝ)) : ℂ)

/-- Design value of the layer's `τ_U` bound at `d ≥ 3` (T2276b): `min(𝔠/12, 𝔠𝔡/12, 1/100)`. -/
def ouTauMax (𝔠 𝔡 : ℝ) : ℝ := min (min (𝔠 / 12) (𝔠 * 𝔡 / 12)) (1 / 100)

/-- The scale of `UNOUDiag`/`UNOULL`: `η = N^{-1+2τ_U}` (token-equal to `Pins.lean:654`). -/
def ouEtaLL {d : ℕ} (sz : Sizes d) (τU : ℝ) (n : ℕ) : ℝ := Nsz sz n ^ (-1 + 2 * τU)

/-- The QUE scale of `UNOUQUE` (`ε₀ = 𝔡/3`): `η_Q = W^{-𝔡/3} lam W^{d/2} / N` (= `etaQ sz n (𝔡/3)`). -/
def ouEtaQ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ) (n : ℕ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n)

/-- `profPM` with `Θ` replaced by `Θ̃` at `ζ`. -/
def profPMTilde {d : ℕ} (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaTilde d (sz.L n) (sz.lam n) ζ (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b /
    ((sz.W n : ℕ) : ℂ) ^ d

/-- `profPP` with `Θ` replaced by `Θ̃` at `ζ`. -/
def profPPTilde {d : ℕ} (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaTilde d (sz.L n) (sz.lam n) ζ (msc z ^ 2) a b / ((sz.W n : ℕ) : ℂ) ^ d

/-- **`UNOULL`**: per-sequence moment form of the weak local law for `𝐇_t` at `η = N^{-1+2τ_U}`. -/
def UNOULL {d : ℕ} (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ δ : ℝ, 0 < δ → ∀ p : ℕ,
      ∀ᶠ n in atTop, ∀ x : Idx d (sz.L n) (sz.W n),
        ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω)
            ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
          ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ

/-- **`UNOUEq747`**: the expectation half of `(eq:diffu1)`/`(eq:diffu2)` (`QDiff`, `Endpoints.lean:197-210`) for
`𝐇_t` at the QUE scale `z_n = E_n + i η_Q`, with `Θ̃` at `ζ(t_n)`, per sequence. -/
def UNOUEq747 {d : ℕ} (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ →
      ∀ᶠ n in atTop, ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMat (UNModel.band sz) n (t n) ω)
              ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPMTilde sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
        ‖(∫ ω, avg2 sz n (fun x y =>
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPPTilde sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)

/-- **Row `UNG1Row`** (UN-51, `RandomLayerB` `g1Row`): the two layer pins from the inputs of `UNOURow`. -/
def UNG1Row : Prop :=
  (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOULL sz τU ∧ UNOUEq747 sz 𝔡 τU

/-- **Row `UNG2bRow`** (UN-52, `QUEFlow` `g2bRow`): `UNOUQUE` for `𝐇_t` from `UNOUEq747`. -/
def UNG2bRow : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUEq747 sz 𝔡 τU → UNOUQUE sz 𝔡 τU

/-! ### ζ -/

theorem ZeroModeProfile_ouZeta_zero : ouZeta 0 = 0 := by simp [ouZeta]

theorem ZeroModeProfile_ouZeta_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ouZeta t := by
  unfold ouZeta
  have := Real.exp_le_one_iff.2 (neg_nonpos.2 ht)
  linarith

theorem ZeroModeProfile_ouZeta_le_one (t : ℝ) : ouZeta t ≤ 1 := by
  unfold ouZeta
  have := (Real.exp_pos (-t)).le
  linarith

/-- `ζ(t) ≤ t` (RBM1D `frl_ouZeta_le`). -/
theorem ZeroModeProfile_ouZeta_le (t : ℝ) : ouZeta t ≤ t := by
  unfold ouZeta
  have := Real.add_one_le_exp (-t)
  linarith

/-! ### Profile identities -/

theorem Stilde_zero (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (i j : Idx d L W) :
    Stilde d L W lam 0 i j = svarF d L W lam i j := by
  simp [Stilde]

theorem sum_Stilde_row (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (hL : 3 ≤ L) (ζ : ℝ)
    (i : Idx d L W) : ∑ j, Stilde d L W lam ζ i j = 1 := by
  unfold Stilde
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Green.IBP_sum_svarF_row lam hL i, Finset.sum_const,
    Finset.card_univ, RBM.Gauss.card_Idx, nsmul_eq_mul]
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  field_simp
  ring

theorem ouVar_eq_Stilde (d L W : ℕ) [NeZero L] [NeZero W] (lam t : ℝ) (ht : 0 ≤ t)
    (c : CoordF d L W) :
    (ouVar d L W lam t c : ℝ) =
      if c.1 = c.2.1 then Stilde d L W lam (ouZeta t) c.1 c.2.1
      else Stilde d L W lam (ouZeta t) c.1 c.2.1 / 2 := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  unfold ouVar
  simp only [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
    Real.coe_toNNReal _ (sub_nonneg.2 he)]
  have hg : (gvarF d L W lam c : ℝ) = if c.1 = c.2.1 then svarF d L W lam c.1 c.2.1
      else svarF d L W lam c.1 c.2.1 / 2 := rfl
  unfold gueVar
  by_cases hc : c.1 = c.2.1
  · simp only [hc, ite_true, hg, Stilde, ouZeta, NNReal.coe_inv, NNReal.coe_natCast]
    ring_nf
  · simp only [hc, ite_false, hg, Stilde, ouZeta, NNReal.coe_inv, NNReal.coe_mul,
      NNReal.coe_natCast, NNReal.coe_ofNat]
    field_simp
    ring_nf

theorem Stilde_eq_SBtilde_mul (d L W : ℕ) [NeZero L] [NeZero W] (lam ζ : ℝ) (i j : Idx d L W) :
    (Stilde d L W lam ζ i j : ℂ) =
      SBtilde d L lam ζ (split d L W i).1 (split d L W j).1 * (((W : ℂ) ^ d)⁻¹) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have h1 : ((svarF d L W lam i j : ℝ) : ℂ) = SB d L lam (split d L W i).1 (split d L W j).1 *
      (((W : ℂ) ^ d)⁻¹) := by
    simp only [svarF, SB_eq_map_SBR, Matrix.map_apply]
    push_cast
    ring
  unfold Stilde SBtilde Jmat
  push_cast
  rw [h1]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  field_simp
  simp only [mul_pow]
  ring

/-! ## §2 The zero-mode profile on `Z_L^d` and `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹` -/

section ThetaTilde

variable (d L : ℕ) [NeZero L]

private theorem ZeroModeProfile_SBtilde_zero (lam : ℝ) : SBtilde d L lam 0 = SB d L lam := by
  simp [SBtilde]

/-- Extreme input `ζ = 0`: `Θ̃ = Θ`. -/
theorem ThetaTilde_zero (lam : ℝ) (ξ : ℂ) : ThetaTilde d L lam 0 ξ = Theta d L lam ξ := by
  simp [ThetaTilde, Theta, ZeroModeProfile_SBtilde_zero]

private theorem ZeroModeProfile_SB_mul_Jmat (lam : ℝ) (hL : 3 ≤ L) :
    SB d L lam * Jmat d L = Jmat d L := by
  ext a b
  simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, mul_one]
  exact sum_SB_row d L lam hL a

private theorem ZeroModeProfile_Jmat_mul_SB (lam : ℝ) (hL : 3 ≤ L) :
    Jmat d L * SB d L lam = Jmat d L := by
  ext a b
  simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, one_mul]
  rw [← sum_SB_row d L lam hL b]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := congrFun (congrFun (SB_transpose d L lam) b) k
  simpa [Matrix.transpose_apply] using this

private theorem ZeroModeProfile_Jmat_mul_Jmat : Jmat d L * Jmat d L = ((L : ℂ) ^ d) • Jmat d L := by
  ext a b
  simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, mul_one, Finset.sum_const,
    Finset.card_univ, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [show Fintype.card (Zd d L) = L ^ d by simp [Zd, ZMod.card]]
  push_cast
  ring

/-- Left inverses are two-sided and unique for `Ring.inverse` (finite matrices). -/
private theorem ZeroModeProfile_ringInverse_eq_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : B * A = 1) : Ring.inverse A = B := by
  have h2 : A * B = 1 := mul_eq_one_comm.mp h
  have hu : IsUnit A := ⟨⟨A, B, h2, h⟩, rfl⟩
  calc Ring.inverse A = (B * A) * Ring.inverse A := by rw [h, one_mul]
    _ = B * (A * Ring.inverse A) := by rw [mul_assoc]
    _ = B := by rw [Ring.mul_inverse_cancel _ hu, mul_one]

private theorem ZeroModeProfile_one_sub_smul_SB_mul_Jmat (lam : ℝ) (hL : 3 ≤ L) (T : ℂ) :
    (1 - T • SB d L lam) * Jmat d L = (1 - T) • Jmat d L := by
  rw [sub_mul, one_mul, Matrix.smul_mul, ZeroModeProfile_SB_mul_Jmat d L lam hL, sub_smul, one_smul]

private theorem ZeroModeProfile_Jmat_mul_one_sub_smul_SB (lam : ℝ) (hL : 3 ≤ L) (T : ℂ) :
    Jmat d L * (1 - T • SB d L lam) = (1 - T) • Jmat d L := by
  rw [mul_sub, mul_one, Matrix.mul_smul, ZeroModeProfile_Jmat_mul_SB d L lam hL, sub_smul, one_smul]

/-- `Θ_T J = (1 - T)⁻¹ J`: the constant vector is the zero mode of `Θ_T`. -/
private theorem ZeroModeProfile_Theta_mul_Jmat (lam : ℝ) (hL : 3 ≤ L) {T : ℂ} (hT : ‖T‖ < 1) :
    Theta d L lam T * Jmat d L = (1 - T)⁻¹ • Jmat d L := by
  have h1T : (1 : ℂ) - T ≠ 0 := one_sub_ne_zero hT
  have h : Theta d L lam T * ((1 - T • SB d L lam) * Jmat d L) =
      Theta d L lam T * ((1 - T) • Jmat d L) := by
    rw [ZeroModeProfile_one_sub_smul_SB_mul_Jmat d L lam hL]
  rw [← mul_assoc, Theta_mul d L lam (norm_SB d L lam hL) hT, one_mul, Matrix.mul_smul] at h
  calc Theta d L lam T * Jmat d L = (1 - T)⁻¹ • ((1 - T) • (Theta d L lam T * Jmat d L)) := by
        rw [smul_smul, inv_mul_cancel₀ h1T, one_smul]
    _ = (1 - T)⁻¹ • Jmat d L := by rw [← h]

/-- **The zero-mode identity** (RBM2D `ThetaTilde_eq` `:339`, RBM1D `Propagator/ZeroMode.lean:113`, with `L² → L^d`):
for `T = ξ (1 - ζ)`, `Θ̃_ξ = Θ_T + α J`, `α = ξ ζ / (L^d (1 - T)(1 - ξ))`. -/
theorem ThetaTilde_eq (lam : ℝ) (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {ζ : ℝ} (h0 : 0 ≤ ζ)
    (h1 : ζ ≤ 1) :
    ThetaTilde d L lam ζ ξ = Theta d L lam (ξ * (1 - (ζ : ℂ))) +
      (ξ * ζ / ((L : ℂ) ^ d * (1 - ξ * (1 - (ζ : ℂ))) * (1 - ξ))) • Jmat d L := by
  have hTn : ‖ξ * (1 - (ζ : ℂ))‖ < 1 := by
    have hz : ‖(1 - (ζ : ℂ))‖ ≤ 1 := by
      have : (1 - (ζ : ℂ)) = ((1 - ζ : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    calc ‖ξ * (1 - (ζ : ℂ))‖ = ‖ξ‖ * ‖(1 - (ζ : ℂ))‖ := norm_mul _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ < 1 := by linarith
  generalize hT : ξ * (1 - (ζ : ℂ)) = T at hTn ⊢
  have h1T : (1 : ℂ) - T ≠ 0 := one_sub_ne_zero hTn
  have h1ξ : (1 : ℂ) - ξ ≠ 0 := one_sub_ne_zero hξ
  have hL2 : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hX : 1 - ξ • SBtilde d L lam ζ =
      (1 - T • SB d L lam) - (ξ * ((ζ : ℂ) / (L : ℂ) ^ d)) • Jmat d L := by
    unfold SBtilde
    rw [smul_add, smul_smul, smul_smul]
    have e1 : ξ * (((1 - ζ : ℝ) : ℂ)) = T := by rw [← hT]; push_cast; ring
    rw [e1]
    abel
  have hs : ((ξ * ζ / ((L : ℂ) ^ d * (1 - T) * (1 - ξ)))) * (1 - T)
      - (ξ * ((ζ : ℂ) / (L : ℂ) ^ d)) * (1 - T)⁻¹
      - (ξ * ζ / ((L : ℂ) ^ d * (1 - T) * (1 - ξ))) * (ξ * ((ζ : ℂ) / (L : ℂ) ^ d)) *
        (L : ℂ) ^ d = 0 := by
    rw [← hT]
    have h1T' : (1 : ℂ) - ξ * (1 - (ζ : ℂ)) ≠ 0 := by rw [hT]; exact h1T
    field_simp
    ring
  have key : (Theta d L lam T + (ξ * ζ / ((L : ℂ) ^ d * (1 - T) * (1 - ξ))) • Jmat d L) *
      (1 - ξ • SBtilde d L lam ζ) = 1 := by
    rw [hX]
    set α : ℂ := ξ * ζ / ((L : ℂ) ^ d * (1 - T) * (1 - ξ)) with hα
    set c : ℂ := ξ * ((ζ : ℂ) / (L : ℂ) ^ d) with hc
    have hΘA := Theta_mul d L lam (norm_SB d L lam hL) hTn
    have hΘJ := ZeroModeProfile_Theta_mul_Jmat d L lam hL hTn
    have hJA := ZeroModeProfile_Jmat_mul_one_sub_smul_SB d L lam hL T
    have hJJ := ZeroModeProfile_Jmat_mul_Jmat d L
    generalize (1 - T • SB d L lam) = A at hΘA hJA ⊢
    calc (Theta d L lam T + α • Jmat d L) * (A - c • Jmat d L)
        = Theta d L lam T * A - c • (Theta d L lam T * Jmat d L)
          + α • (Jmat d L * A) - (α * c) • (Jmat d L * Jmat d L) := by
          simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          module
      _ = 1 - c • ((1 - T)⁻¹ • Jmat d L) + α • ((1 - T) • Jmat d L)
          - (α * c) • (((L : ℂ) ^ d) • Jmat d L) := by
          rw [hΘA, hΘJ, hJA, hJJ]
      _ = 1 + (α * (1 - T) - c * (1 - T)⁻¹ - α * c * (L : ℂ) ^ d) • Jmat d L := by
          module
      _ = 1 := by rw [hs, zero_smul, add_zero]
  exact ZeroModeProfile_ringInverse_eq_of_mul_eq_one key

end ThetaTilde

/-! ### The `d ≥ 3` oscillation bound of `Θ̃` (target 2.4) -/

section Oscillation

open scoped Matrix.Norms.Operator

/-- Oscillation of `Θ_T` from a bound `B` on `Θ̊_T(0, ·)`: `αJ` and the zero mode cancel
(translation invariance `Theta_apply_add_right`, `Theta0_apply`; copy of the private
`theta_diff_of_row` of `Main/QUECore.lean:87`). -/
private theorem ZeroModeProfile_osc_of_bound (d L : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {T : ℂ}
    (hT : ‖T‖ < 1) {B : ℝ} (hB : ∀ x : Zd d L, ‖Theta0 d L g T 0 x‖ ≤ B) (u v : Zd d L) :
    ‖Theta d L g T u v - Theta d L g T 0 0‖ ≤ 2 * B := by
  have hS : ‖SB d L g‖ = 1 := norm_SB d L g hL
  have hrow : Theta d L g T u v = Theta d L g T 0 (v - u) := by
    have h := Theta_apply_add_right d L g hS hT 0 (v - u) u
    simpa using h
  rw [hrow]
  have h0 : Theta d L g T 0 (v - u) - Theta d L g T 0 0 =
      Theta0 d L g T 0 (v - u) - Theta0 d L g T 0 0 := by
    rw [Theta0_apply, Theta0_apply]; ring
  rw [h0]
  calc ‖Theta0 d L g T 0 (v - u) - Theta0 d L g T 0 0‖
      ≤ ‖Theta0 d L g T 0 (v - u)‖ + ‖Theta0 d L g T 0 0‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hB _) (hB _)
    _ = 2 * B := by ring

/-- **The `d ≥ 3` oscillation bound of `Θ̃`** (replaces RBM2D `norm_ThetaTilde_sub_le`, `90 (1 + log L)`):
uniform in `L`, `ζ ∈ [0,1]`, `z` in the bulk, constant `C(d, 𝔡, κ)`, no `log L`.  The constant matrix `α J`
of `ThetaTilde_eq` cancels, and `Θ_T`, `T = ξ (1 - ζ) = t' · m(σ₁) m(σ₂)`, `t' = (1 - ζ) lemT z ∈ [0,1)`,
is bounded by property 8 (`prop5to8_holds`) as in the merged `thetaDiff` (`Main/QUECore.lean:105`). -/
theorem norm_ThetaTilde_sub_le :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
        ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
          ∀ (σ : Bool) (u v : Zd d L),
            ‖ThetaTilde d L lam ζ (xiQ z σ) u v - ThetaTilde d L lam ζ (xiQ z σ) 0 0‖ ≤
              C * (lam ^ 2)⁻¹ := by
  intro d hd 𝔡 κ h𝔡 hκ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine ⟨1, one_pos, fun L _ hL lam hlam hlamΛ z hz hz1 hre => ?_⟩
    exfalso
    have := abs_nonneg z.re
    linarith
  have hκ' : 0 < Real.sqrt (κ * (4 - κ)) / 2 := by
    have : 0 < κ * (4 - κ) := mul_pos hκ (by linarith)
    positivity
  obtain ⟨C₈, hC₈, H⟩ := prop5to8_holds d 𝔡⁻¹ (Real.sqrt (κ * (4 - κ)) / 2) (1 / 2) |>.zeroMode hd
    (inv_pos.2 h𝔡) hκ'
  refine ⟨2 * C₈, by positivity, fun L _ hL lam hlam hlamΛ z hz hz1 hre ζ hζ0 hζ1 σ u v => ?_⟩
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
  have hu0 : 0 ≤ 1 - ζ := by linarith
  have ht'0 : 0 ≤ (1 - ζ) * lemT z := mul_nonneg hu0 ht0
  have ht'1 : (1 - ζ) * lemT z < 1 := by nlinarith
  have hB : ∀ (σ₁ σ₂ : Bool) (x : Zd d L),
      ‖Theta0 d L lam (((((1 - ζ) * lemT z : ℝ)) : ℂ) *
        (PropSpin (mE (lemE z)) σ₁ * PropSpin (mE (lemE z)) σ₂)) 0 x‖ ≤ C₈ * (lam ^ 2)⁻¹ := by
    intro σ₁ σ₂ x
    refine (H L hL lam hlam hlamΛ ((1 - ζ) * lemT z) ht'0 ht'1 (mE (lemE z)) hm1 hmi σ₁ σ₂ x).trans ?_
    have h1 : (lam ^ 2 + |1 - (1 - ζ) * lemT z|)⁻¹ ≤ (lam ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by have := abs_nonneg (1 - (1 - ζ) * lemT z); linarith)
    have h2 : ((((zdistD d L x : ℝ)) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0 : ℝ) ≤ zdistD d L x := Nat.cast_nonneg _; linarith))
    have h3 : 0 ≤ (lam ^ 2 + |1 - (1 - ζ) * lemT z|)⁻¹ := by positivity
    calc C₈ * (lam ^ 2 + |1 - (1 - ζ) * lemT z|)⁻¹ * ((((zdistD d L x : ℝ)) + 1) ^ (d - 2))⁻¹
        ≤ C₈ * (lam ^ 2)⁻¹ * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₈.le) h2 (by positivity) (by positivity)
      _ = C₈ * (lam ^ 2)⁻¹ := mul_one _
  have hξ1 : (((((1 - ζ) * lemT z : ℝ)) : ℂ) *
      (PropSpin (mE (lemE z)) true * PropSpin (mE (lemE z)) false)) =
      (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * (1 - (ζ : ℂ)) := by
    simp only [PropSpin, ite_true, Bool.false_eq_true, ite_false]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hm1]
    simp [lemT]
    ring
  have hξ2 : (((((1 - ζ) * lemT z : ℝ)) : ℂ) *
      (PropSpin (mE (lemE z)) true * PropSpin (mE (lemE z)) true)) = msc z ^ 2 * (1 - (ζ : ℂ)) := by
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
  have hz1' : ‖(1 - (ζ : ℂ))‖ ≤ 1 := by
    have : (1 - (ζ : ℂ)) = ((1 - ζ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    linarith
  have hTn : ∀ {ξ : ℂ}, ‖ξ‖ < 1 → ‖ξ * (1 - (ζ : ℂ))‖ < 1 := fun {ξ} hξ =>
    calc ‖ξ * (1 - (ζ : ℂ))‖ = ‖ξ‖ * ‖(1 - (ζ : ℂ))‖ := norm_mul _ _
      _ ≤ ‖ξ‖ * 1 := by gcongr
      _ < 1 := by linarith
  have key : ∀ {ξ : ℂ}, ‖ξ‖ < 1 →
      (∀ x : Zd d L, ‖Theta0 d L lam (ξ * (1 - (ζ : ℂ))) 0 x‖ ≤ C₈ * (lam ^ 2)⁻¹) →
      ‖ThetaTilde d L lam ζ ξ u v - ThetaTilde d L lam ζ ξ 0 0‖ ≤ 2 * (C₈ * (lam ^ 2)⁻¹) := by
    intro ξ hξ hBξ
    rw [ThetaTilde_eq d L lam hL hξ hζ0 hζ1]
    simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, Matrix.of_apply, smul_eq_mul, mul_one]
    have := ZeroModeProfile_osc_of_bound d L hL lam (hTn hξ) hBξ u v
    convert this using 2
    ring
  have hfin : ‖ThetaTilde d L lam ζ (xiQ z σ) u v - ThetaTilde d L lam ζ (xiQ z σ) 0 0‖ ≤
      2 * (C₈ * (lam ^ 2)⁻¹) := by
    cases σ
    · simp only [xiQ, Bool.false_eq_true, ite_false]
      exact key hn1 (fun x => by rw [← hξ1]; exact hB true false x)
    · simp only [xiQ, ite_true]
      exact key hn2 (fun x => by rw [← hξ2]; exact hB true true x)
  calc _ ≤ 2 * (C₈ * (lam ^ 2)⁻¹) := hfin
    _ = 2 * C₈ * (lam ^ 2)⁻¹ := by ring

end Oscillation

/-! ### Row differences of the `Θ̃` profiles (target 2.5) and `ζ = 0` -/

/-- **Consumer form** (UN-52, as `queRowDiff`): row differences of the `Θ̃` profiles,
`‖profP·Tilde a b - profP·Tilde a b'‖ ≤ C lam⁻² W^{-d}` (2.4 with `‖ξ‖ ≤ 1`). -/
theorem profTilde_rowDiff :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
      ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
        ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
          ∀ a b b' : Zd d (sz.L n),
            ‖profPMTilde sz n ζ z a b - profPMTilde sz n ζ z a b'‖ ≤
                C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
            ‖profPPTilde sz n ζ z a b - profPPTilde sz n ζ z a b'‖ ≤
                C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
  intro d hd 𝔡 κ h𝔡 hκ
  obtain ⟨C, hC, H⟩ := norm_ThetaTilde_sub_le d hd 𝔡 κ h𝔡 hκ
  refine ⟨2 * C, by positivity, fun sz n hlam hlamΛ z hz hz1 hre ζ hζ0 hζ1 a b b' => ?_⟩
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have := sz.W_pos n
    positivity
  have hmn1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hmn : 0 ≤ ‖msc z‖ := norm_nonneg _
  have hdiff : ∀ σ : Bool,
      ‖ThetaTilde d (sz.L n) (sz.lam n) ζ (xiQ z σ) a b -
          ThetaTilde d (sz.L n) (sz.lam n) ζ (xiQ z σ) a b'‖ ≤ 2 * C * (sz.lam n ^ 2)⁻¹ := by
    intro σ
    have h1 := H (sz.L n) (sz.three_le_L n) (sz.lam n) hlam hlamΛ z hz hz1 hre ζ hζ0 hζ1 σ a b
    have h2 := H (sz.L n) (sz.three_le_L n) (sz.lam n) hlam hlamΛ z hz hz1 hre ζ hζ0 hζ1 σ a b'
    calc _ = ‖(ThetaTilde d (sz.L n) (sz.lam n) ζ (xiQ z σ) a b -
              ThetaTilde d (sz.L n) (sz.lam n) ζ (xiQ z σ) 0 0) -
            (ThetaTilde d (sz.L n) (sz.lam n) ζ (xiQ z σ) a b' -
              ThetaTilde d (sz.L n) (sz.lam n) ζ (xiQ z σ) 0 0)‖ := by congr 1; ring
      _ ≤ _ := (norm_sub_le _ _).trans (by linarith)
  have hWc : ‖((sz.W n : ℕ) : ℂ) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [norm_pow, Complex.norm_natCast]
  have hnorm : ∀ (ξ : ℂ), ‖ξ‖ ≤ 1 → ∀ θ θ' : ℂ, ‖θ - θ'‖ ≤ 2 * C * (sz.lam n ^ 2)⁻¹ →
      ‖ξ * θ / ((sz.W n : ℕ) : ℂ) ^ d - ξ * θ' / ((sz.W n : ℕ) : ℂ) ^ d‖ ≤
        2 * C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
    intro ξ hξ θ θ' hθ
    have : ξ * θ / ((sz.W n : ℕ) : ℂ) ^ d - ξ * θ' / ((sz.W n : ℕ) : ℂ) ^ d =
        ξ * (θ - θ') / ((sz.W n : ℕ) : ℂ) ^ d := by ring
    rw [this, norm_div, norm_mul, hWc]
    apply div_le_div_of_nonneg_right _ hW.le
    calc ‖ξ‖ * ‖θ - θ'‖ ≤ 1 * (2 * C * (sz.lam n ^ 2)⁻¹) :=
          mul_le_mul hξ hθ (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine ⟨?_, ?_⟩
  · have hξ : ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
    have := hnorm _ hξ _ _ (hdiff false)
    simpa only [profPMTilde, xiQ, Bool.false_eq_true, ite_false] using this
  · have hξ : ‖msc z ^ 2‖ ≤ 1 := by
      rw [norm_pow]; nlinarith
    have := hnorm _ hξ _ _ (hdiff true)
    simpa only [profPPTilde, xiQ, ite_true] using this

/-- Extreme input `ζ = 0`: the profiles with `Θ̃` are the merged `profPM`, `profPP`. -/
theorem profPMTilde_zero {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) :
    profPMTilde sz n 0 z a b = profPM sz n z a b ∧ profPPTilde sz n 0 z a b = profPP sz n z a b := by
  refine ⟨?_, ?_⟩
  · simp only [profPMTilde, profPM, ThetaPM, ThetaTilde_zero]
  · simp only [profPPTilde, profPP, ThetaPP, ThetaTilde_zero]

/-! ## §3 The `τ_U` constraint of the layer -/

theorem ouTauMax_pos {𝔠 𝔡 : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) : 0 < ouTauMax 𝔠 𝔡 := by
  unfold ouTauMax
  exact lt_min (lt_min (by linarith) (by positivity)) (by norm_num)

/-- The design value's slack (`d ≥ 3`): `12 τ_U ≤ 𝔠`, `12 τ_U ≤ 𝔠 𝔡`, `τ_U < 𝔠 𝔡` and
`(3/2) τ_U ≤ 𝔠𝔡/8 < 2𝔠𝔡/3` (the QUE scale `η_Q ≥ N^{-1+2𝔠𝔡/3}`, `UNOUEq747`). -/
theorem ouTauMax_slack {𝔠 𝔡 τU : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (h : τU ≤ ouTauMax 𝔠 𝔡) :
    12 * τU ≤ 𝔠 ∧ 12 * τU ≤ 𝔠 * 𝔡 ∧ τU < 𝔠 * 𝔡 ∧ 3 * τU / 2 < 2 * (𝔠 * 𝔡) / 3 := by
  have h1 : τU ≤ 𝔠 / 12 := h.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : τU ≤ 𝔠 * 𝔡 / 12 := h.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : 0 < 𝔠 * 𝔡 := mul_pos h𝔠 h𝔡
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## §5 Sequence uniformization and `ouDiag_of_ouLL` -/

/-- Uniformization over admissible parameter sequences (RBM1D `eventually_forall_mem_of_forall_seq`,
`Flow/OUCommonFlow.lean:85`; RBM2D `ZeroModeProfile.lean:550`; pure filter combinatorics). -/
private theorem ZeroModeProfile_eventually_forall_mem_of_forall_seq' {α : Type*} {T : ℕ → Set α}
    (hT : ∀ n, (T n).Nonempty) {P : ℕ → α → Prop}
    (h : ∀ s : ℕ → α, (∀ n, s n ∈ T n) → ∀ᶠ n in atTop, P n (s n)) :
    ∀ᶠ n in atTop, ∀ a ∈ T n, P n a := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, ∃ a, a ∈ T n ∧ ¬ P n a := by
    refine hcon.mono ?_
    intro n hn
    push Not at hn
    exact hn
  set g : ℕ → α := fun n =>
    if hn : ∃ a, a ∈ T n ∧ ¬ P n a then hn.choose else (hT n).choose with hg
  have hgmem : ∀ n, g n ∈ T n := by
    intro n
    by_cases hn : ∃ a, a ∈ T n ∧ ¬ P n a
    · simp only [hg, hn, dite_true]
      exact hn.choose_spec.1
    · simp only [hg, hn, dite_false]
      exact (hT n).choose_spec
  have hbad : ∀ n, (∃ a, a ∈ T n ∧ ¬ P n a) → ¬ P n (g n) := by
    intro n hn
    have hgn : g n = hn.choose := by simp only [hg, hn, dite_true]
    rw [hgn]
    exact hn.choose_spec.2
  have heven : ∀ᶠ n in atTop, P n (g n) := h g hgmem
  obtain ⟨n, hn1, hn2⟩ := (hcon'.and_eventually heven).exists
  exact hbad n hn1 hn2

section DiagMarkov

variable {d : ℕ} {sz : Sizes d}

open scoped Matrix.Norms.L2Operator in
private theorem ZeroModeProfile_norm_entry_le (M : UNModel sz) (n : ℕ) (t : ℝ)
    (ω : SeqΩ sz × Ω d (sz.L n) (sz.W n)) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖Gres (ouMat M n t ω) z true x y‖ ≤ η⁻¹ :=
  (RBM.Ind.norm_apply_le_l2_opNorm _ x y).trans
    (norm_Gsig_le_inv_eta (ouMat_isHermitian M n t ω) hη hz true)

/-- Markov for one diagonal entry: if `E ‖G_{xx}‖^{2p} ≤ N^δ` then
`P(‖G_{xx}‖ > N^ε) ≤ N^{δ - 2pε}` (RBM2D `ouLL_markov`, `ZeroModeProfile.lean:584`). -/
private theorem ZeroModeProfile_markov (n : ℕ) (t : ℝ) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : z.im = η)
    (x : Idx d (sz.L n) (sz.W n)) (p : ℕ) {N ε δ : ℝ} (hN : 1 ≤ N)
    (hmom : ∫ ω, ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖ ^ (2 * p)
      ∂(ouP (UNModel.band sz) n) ≤ N ^ δ) :
    ouP (UNModel.band sz) n {ω | N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖} ≤
      ENNReal.ofReal (N ^ (δ - 2 * p * ε)) := by
  have hN0 : 0 < N := by linarith
  set μ := ouP (UNModel.band sz) n with hμ
  set f : SeqΩ sz × Ω d (sz.L n) (sz.W n) → ℝ :=
    fun ω => ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖ ^ (2 * p) with hf
  have hfm : Measurable f :=
    (((walk_measurable_Gres_apply z true x x).comp (measurable_ouMat (UNModel.band sz) n t)).norm).pow_const
      (2 * p)
  have hfi : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ((η⁻¹) ^ (2 * p)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (ZeroModeProfile_norm_entry_le (UNModel.band sz) n t ω hη (by rw [hz]; exact le_abs_self _) x x) _
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (ae_of_all _ fun ω => by positivity) hfi (N ^ (2 * p * ε))
  have hsub : {ω | N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖} ⊆
      {ω | N ^ (2 * p * ε) ≤ f ω} := by
    intro ω hω
    have h1 : (N ^ ε) ^ (2 * p) ≤ ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖ ^ (2 * p) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) (le_of_lt hω) _
    have h2 : (N ^ ε) ^ (2 * p) = N ^ (2 * p * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    change N ^ (2 * p * ε) ≤ ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖ ^ (2 * p)
    rw [← h2]
    exact h1
  have hreal : μ.real {ω | N ^ (2 * p * ε) ≤ f ω} ≤ N ^ (δ - 2 * p * ε) := by
    have hpos : 0 < N ^ (2 * p * ε) := Real.rpow_pos_of_pos hN0 _
    have h3 : N ^ (2 * p * ε) * μ.real {ω | N ^ (2 * p * ε) ≤ f ω} ≤ N ^ δ := hM.trans hmom
    rw [Real.rpow_sub hN0, le_div_iff₀ hpos]
    linarith
  calc μ {ω | N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω) z true x x‖}
      ≤ μ {ω | N ^ (2 * p * ε) ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | N ^ (2 * p * ε) ≤ f ω}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (N ^ (δ - 2 * p * ε)) := ENNReal.ofReal_le_ofReal hreal

end DiagMarkov

/-- **`UNOUDiag` from the per-sequence moment pin `UNOULL`.**  Uniformization over `(t, E)`
(`ZeroModeProfile_eventually_forall_mem_of_forall_seq'`), Markov for `E ‖G_{xx}‖^{2p} ≤ N^ε` with
`2pε ≥ 1 + ε + D`, and the union bound over the `N` indices `x` inside `ouP`
(RBM2D `ouDiag_of_ouLL`, `ZeroModeProfile.lean:630`). -/
theorem ouDiag_of_ouLL :
    ∀ {d : ℕ} {sz : Sizes d} {τU : ℝ}, UNOULL sz τU → UNOUDiag sz τU := by
  intro d sz τU h κ ε D hκ hε hD
  by_cases hκ2 : 2 < κ
  · refine Eventually.of_forall fun n t _ _ E hE => ?_
    exfalso
    have := abs_nonneg E
    linarith
  push Not at hκ2
  obtain ⟨p, hp⟩ : ∃ p : ℕ, 1 + ε + D ≤ 2 * (p : ℝ) * ε := by
    refine ⟨⌈(1 + ε + D) / (2 * ε)⌉₊, ?_⟩
    have := Nat.le_ceil ((1 + ε + D) / (2 * ε))
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hT : ∀ n, ({a : ℝ × ℝ | 0 ≤ a.1 ∧ a.1 ≤ ouTStar sz τU n ∧ |a.2| ≤ 2 - κ}).Nonempty := by
    intro n
    refine ⟨(0, 0), le_rfl, Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    simp only [abs_zero]
    linarith
  have key := ZeroModeProfile_eventually_forall_mem_of_forall_seq'
    (P := fun n (a : ℝ × ℝ) => ∀ x : Idx d (sz.L n) (sz.W n),
      ∫ ω, ‖Gres (ouMat (UNModel.band sz) n a.1 ω)
          ((a.2 : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
        ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ ε) hT
    (fun s hs => h κ hκ (fun n => (s n).2) (fun n => (hs n).2.2) (fun n => (s n).1)
      (fun n => ⟨(hs n).1, (hs n).2.1⟩) ε hε p)
  filter_upwards [key] with n hn t ht0 ht E hE
  have hsz : 1 ≤ Nsz sz n := by
    have : 1 ≤ sz.size n := by
      have h1 := sz.three_le_L n
      have h2 := sz.W_pos n
      simp only [Sizes.size]
      exact Nat.one_le_pow _ _ (Nat.mul_pos h2 (by omega))
    exact_mod_cast this
  set N : ℝ := Nsz sz n with hN
  have hN0 : 0 < N := by linarith
  have hη : 0 < ouEtaLL sz τU n := Real.rpow_pos_of_pos hN0 _
  have hmom := hn (t, E) ⟨ht0, ht, hE⟩
  have hbd : ∀ x : Idx d (sz.L n) (sz.W n),
      ouP (UNModel.band sz) n {ω | N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω)
        ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} ≤
      ENNReal.ofReal (N ^ (ε - 2 * p * ε)) := fun x =>
    ZeroModeProfile_markov n t hη (by simp) x p hsz (hmom x)
  have hset : {ω | ∃ x : Idx d (sz.L n) (sz.W n), N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω)
      ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} =
      ⋃ x : Idx d (sz.L n) (sz.W n), {ω | N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω)
        ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} := by
    ext ω; simp
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [Sizes.card_Idx]
  change ouP (UNModel.band sz) n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
      N ^ ε < ‖Gres (ouMat (UNModel.band sz) n t ω)
        ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} ≤ ENNReal.ofReal (N ^ (-D))
  rw [hset]
  calc ouP (UNModel.band sz) n (⋃ x : Idx d (sz.L n) (sz.W n), {ω | N ^ ε <
        ‖Gres (ouMat (UNModel.band sz) n t ω)
          ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖})
      ≤ ∑ x : Idx d (sz.L n) (sz.W n), ouP (UNModel.band sz) n {ω | N ^ ε <
        ‖Gres (ouMat (UNModel.band sz) n t ω)
          ((E : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _x : Idx d (sz.L n) (sz.W n), ENNReal.ofReal (N ^ (ε - 2 * p * ε)) :=
        Finset.sum_le_sum fun x _ => hbd x
    _ = ENNReal.ofReal (N * N ^ (ε - 2 * p * ε)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul hN0.le]
        congr 1
        rw [← hcard]
        exact (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (N ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        calc N * N ^ (ε - 2 * p * ε) = N ^ (1 + (ε - 2 * p * ε)) := by
              rw [Real.rpow_add hN0, Real.rpow_one]
          _ ≤ N ^ (-D) := Real.rpow_le_rpow_of_exponent_le hsz (by linarith)

/-! ## §6 The assembly -/

/-- **The assembly** (RBM2D `ouRow_of_pins`, `ZeroModeProfile.lean:715`): the rows `UNG1Row`, `UNG2bRow` give
`UNOURow` with `τ₀ = ouTauMax 𝔠 𝔡`; the `UNOUDiag` half is `ouDiag_of_ouLL`. -/
theorem ouRow_of_pins : UNG1Row → UNG2bRow → UNOURow := by
  intro r1 r2b hML hLoc hQ d hd 𝔠 𝔡 sz hA
  refine ⟨ouTauMax 𝔠 𝔡, ouTauMax_pos hA.1 hA.2.1, fun τU hτ hle => ?_⟩
  have h1 := r1 hML hLoc hQ d hd 𝔠 𝔡 sz hA τU hτ hle
  exact ⟨r2b d hd 𝔠 𝔡 sz hA τU hτ hle h1.2, ouDiag_of_ouLL h1.1⟩

/-! ## §7 Compiled instances (`d = 3`, `L = 4`, `W = 2`, `lam = 1/2`; the owed pins stay hypotheses) -/

namespace ZeroModeProfileInst

open RBM.Gauss.SizesInst

/-- Row sums of `S̃` at `d = 3`, `L = 4`, `W = 2`, `lam = 1/2`, `ζ = ζ(1) = 1 - e^{-1}`. -/
theorem inst_sum_Stilde_row (i : Idx 3 4 2) : ∑ j, Stilde 3 4 2 (1 / 2) (ouZeta 1) i j = 1 :=
  sum_Stilde_row 3 4 2 (1 / 2) (by norm_num) (ouZeta 1) i

/-- The OU variance is the coordinate family of `S̃` at `t = 1` (a diagonal coordinate). -/
theorem inst_ouVar_eq_Stilde (i : Idx 3 4 2) :
    (ouVar 3 4 2 (1 / 2) 1 (i, i, true) : ℝ) = Stilde 3 4 2 (1 / 2) (ouZeta 1) i i := by
  have h := ouVar_eq_Stilde 3 4 2 (1 / 2) 1 zero_le_one (i, i, true)
  simpa using h

/-- The zero-mode identity at `ξ = 1/2`, `ζ = 1/100`. -/
theorem inst_ThetaTilde_eq :
    ThetaTilde 3 4 (1 / 2) (1 / 100) (1 / 2 : ℂ) =
      Theta 3 4 (1 / 2) ((1 / 2 : ℂ) * (1 - (((1 / 100 : ℝ)) : ℂ))) +
        ((1 / 2 : ℂ) * ((1 / 100 : ℝ) : ℂ) /
          ((4 : ℂ) ^ 3 * (1 - (1 / 2 : ℂ) * (1 - (((1 / 100 : ℝ)) : ℂ))) * (1 - (1 / 2 : ℂ)))) •
          Jmat 3 4 := by
  have h := ThetaTilde_eq 3 4 (1 / 2) (by norm_num) (ξ := (1 / 2 : ℂ)) (by norm_num)
    (ζ := 1 / 100) (by norm_num) (by norm_num)
  simpa using h

/-- Target 2.4 at `d = 3`, `𝔡 = κ = 1/10`: the constant `C` is obtained and applied at `L = 4`,
`lam = 1/2`, `z = 1/2 + i/2`, `ζ = 1/2`, both `σ`, `u = 0`, `v = (1, 0, 0)`. -/
theorem inst_norm_ThetaTilde_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ σ : Bool,
    ‖ThetaTilde 3 4 (1 / 2) (1 / 2) (xiQ ((1 / 2 : ℂ) + Complex.I / 2) σ) 0 (fun i => if i = 0 then 1 else 0) -
      ThetaTilde 3 4 (1 / 2) (1 / 2) (xiQ ((1 / 2 : ℂ) + Complex.I / 2) σ) 0 0‖ ≤
        C * ((1 / 2 : ℝ) ^ 2)⁻¹ := by
  obtain ⟨C, hC, H⟩ := norm_ThetaTilde_sub_le 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun σ => ?_⟩
  refine H 4 (by norm_num) (1 / 2) (by norm_num) (by norm_num) ((1 / 2 : ℂ) + Complex.I / 2)
    (by norm_num) (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num) σ 0 _

/-- Target 2.5 along the preflight sequence `sz0`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`). -/
theorem inst_profTilde_rowDiff : ∃ C : ℝ, 0 < C ∧ ∀ a b b' : Zd 3 (sz0.L 0),
    ‖profPMTilde sz0 0 (1 / 2) ((1 / 2 : ℂ) + Complex.I / 2) a b -
        profPMTilde sz0 0 (1 / 2) ((1 / 2 : ℂ) + Complex.I / 2) a b'‖ ≤
      C * (sz0.lam 0 ^ 2)⁻¹ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 := by
  obtain ⟨C, hC, H⟩ := profTilde_rowDiff 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun a b b' => (H sz0 0 ?_ ?_ ((1 / 2 : ℂ) + Complex.I / 2) (by norm_num)
    (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num) a b b').1⟩
  · simp [sz0]
  · norm_num [sz0]

/-- `ζ = 0` at `sz0`. -/
theorem inst_profPMTilde_zero (a b : Zd 3 (sz0.L 0)) (z : ℂ) :
    profPMTilde sz0 0 0 z a b = profPM sz0 0 z a b ∧ profPPTilde sz0 0 0 z a b = profPP sz0 0 z a b :=
  profPMTilde_zero sz0 0 z a b

/-- `ouTauMax (1/6) (1/10) = 1/720`. -/
theorem inst_ouTauMax : ouTauMax (1 / 6) (1 / 10) = 1 / 720 := by
  unfold ouTauMax
  norm_num [min_def]

/-- The chosen `τ_U = 1/1000` is below `ouTauMax` and its slack inequalities hold. -/
theorem inst_ouTauMax_slack :
    12 * (1 / 1000 : ℝ) ≤ 1 / 6 ∧ 12 * (1 / 1000 : ℝ) ≤ 1 / 6 * (1 / 10) ∧
      (1 / 1000 : ℝ) < 1 / 6 * (1 / 10) ∧ 3 * (1 / 1000 : ℝ) / 2 < 2 * (1 / 6 * (1 / 10)) / 3 :=
  ouTauMax_slack (by norm_num) (by norm_num) (by rw [inst_ouTauMax]; norm_num)

/-- `ouDiag_of_ouLL` at `sz0`, `τ_U = 1/1000`: the pin `UNOULL` (another gate's) stays a hypothesis. -/
theorem inst_ouDiag : UNOULL sz0 (1 / 1000) → UNOUDiag sz0 (1 / 1000) :=
  ouDiag_of_ouLL

/-- `UNG1Row` at `sz0` (admissible at `𝔠 = 1/6`, `𝔡 = 1/10`), `τ_U = 1/1000 ≤ ouTauMax`. -/
theorem inst_g1 (r1 : UNG1Row) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULL sz0 (1 / 1000) ∧ UNOUEq747 sz0 (1 / 10) (1 / 1000) :=
  r1 hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (by rw [inst_ouTauMax]; norm_num)

/-- `ouRow_of_pins` applied (the rows `UNG1Row`, `UNG2bRow` are other gates' pins). -/
theorem inst_ouRow (r1 : UNG1Row) (r2b : UNG2bRow) : UNOURow :=
  ouRow_of_pins r1 r2b

end ZeroModeProfileInst

end RBM.Univ
