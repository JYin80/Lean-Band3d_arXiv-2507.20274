/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.RandomLayerBGBA
import RBM3D.BA.Prop6Path
import RBM3D.BA.KBase
import RBM3D.BA.KTreeRep
import RBM3D.BA.KInduct
import RBM3D.BA.EMn2BA
import RBM3D.BA.EKNonzero
import RBM3D.Universality.GUEPhase.KPrim
import RBM3D.Universality.OUInterfaceK

/-!
# BA-C3 row a: the BA OU profile, row differences, the BA `thetaDiff`, the BA GUE-phase 2-loop

Ticket T2515 (row a; DECISIONS §337; design gate D1 signed by `docs/reports/T2515-1a-audit.md`).
New BA leaf: no merged file is edited.  The band twins are `Universality/ZeroModeProfile.lean`
(`ThetaTilde_eq:281`, `norm_ThetaTilde_sub_le:367`, `profTilde_rowDiff:469`) and
`Universality/GUEPhase/KPrim.lean` (`kTwoGUE:68`, `hasDerivAt_kTwoGUE:150`,
`lemT_mul_kTwoGUE_pm_eq_profPMTilde:275`, `KPrim_exists_upto:523`, `gueK_exists:749`); the private
ODE machinery of `KPrim` (8 private lemmas) and private lemmas of `ZeroModeProfile` (2) and
`EKNonzero` (3) are read by `open private`.

Nothing here reads a V output (`BAMLOutTL`, `BAMainIndFamTL`, `UNMLOutBA`, `BA/MainInd*`,
`BA/TwistPins`, `BA/Step6*`).  Property 8 enters through the merged lossless `baProp8_holds`
(`BA/Prop6Path.lean:1009`, `BAProp8`: no `W^τ`, no `≺`) at the flow point
`(λ₀, E, m₀) = (√t₀ λ, BAflowE, m/√t₀)` of `BAzztE_data`.  The BA matrix
`Q = M^{(+,σ)}(z) = t₀ Q₀` has constant row and column sums `r = t₀ r₀`, `|r₀| ≤ 1` (Ward), so
`Θ̃_ζ Q` differs from `Θ_{1-ζ} Q` by a constant matrix.

* §1 `UNOUProfile.ba d` and `UNOUProfile.ba_spec` (target 1): `pm`, `pp` are
  `W^{-d} (Θ̃_ζ M^{(+,σ)})_{ab}`, `Θ̃_ζ = (1 - M^{(+,σ)}(z) S̃_ζ)⁻¹`,
  `S̃_ζ = SBtilde d L 0 ζ = (1-ζ) 1 + (ζ/L^d) J` (`SB d L 0 = 1`).
* §2 `baThetaTransfer` (`Θ_s` at `z` is `BATheta` at the flow point, time `s t₀`) and `baT0Cmp`
  (`cT ≤ t₀`) (target 2).
* §3 the zero mode: Sherman-Morrison for a matrix with constant row and column sums
  (`GUEKPrim_SM`), `baThetaTilde_eq` (`Θ̃_ζ = Θ_{(1-ζ)t₀} + β J` at real data).
* §4 the lossless oscillation (`GUEKPrim_osc_core`), the row differences of `Θ_s Q` for all
  `s ∈ [0,1]` (`GUEKPrim_rowdiff`: `s ≥ 1/2` through `s Θ_s Q = Θ_s - 1`; `s < 1/2` through
  `‖Θ_s‖_{∞→∞} ≤ 2`).
* §5 `baThetaTilde_osc` (target 3), `baThetaDiff`, `baOUProfRowk_holds`, `baProfComp`,
  `UNOUProfile.ba_zero` (targets 4-6).
* §6 `kTwoGUEBA`, `kTwoGUELoopBA`, `kTwoGUEBA_self`, `kTwoGUEBA_eq_ThetaTilde`,
  `hasDerivAt_kTwoGUELoopBA` ((7.33) at `n = 2`; the row and column sums of `Θ_{t₁} Q₀` are
  `r₀ (1 - t₁ r₀)⁻¹`), §7 `gueK_existsBA` (the induction of `KPrim_exists_upto` over a start
  family `K0` and a 2-loop family `K2`), §8 the bridges `kTwoGUEBA_bridge`, `_pm`, `_pp`
  (target 7); §9 compiled nonempty instances (target 8).

Helpers that are not pinned by the ticket are `private` with the stem `GUEKPrim_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

open private ZeroModeProfile_Jmat_mul_Jmat ZeroModeProfile_ringInverse_eq_of_mul_eq_one from
  RBM3D.Universality.ZeroModeProfile
open private EKNonzero_row_sum EKNonzero_col_sum EKNonzero_norm_Q_le from RBM3D.BA.EKNonzero

noncomputable section

/-! ## 1. The BA OU profile (target 1) -/

namespace RBM.Univ

open RBM RBM.Gauss RBM.BA

/-- **The BA OU profile** (D1 (iii)): `pm sz n ζ z a b = W^{-d} (Θ̃_ζ M^{(+,-)})_{ab}` and
`pp sz n ζ z a b = W^{-d} (Θ̃_ζ M^{(+,+)})_{ab}`, `Θ̃_ζ = (1 - M^{(+,σ)} S̃_ζ)⁻¹`, `S̃_ζ = SBtilde d L 0 ζ`,
`M = BAMB d L λ z (BAm d L λ z)`, `λ = sz.lam n`; it reads `sz` at the index only. -/
def UNOUProfile.ba (d : ℕ) : UNOUProfile (UNKind.ba d) where
  pm sz n ζ z a b :=
    (Ring.inverse (1 - BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false *
        SBtilde d (sz.L n) 0 ζ) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false) a b /
        ((sz.W n : ℕ) : ℂ) ^ d
  pp sz n ζ z a b :=
    (Ring.inverse (1 - BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true *
        SBtilde d (sz.L n) 0 ζ) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true) a b /
        ((sz.W n : ℕ) : ℂ) ^ d

/-- **Target 1**: the profile text of D1 (iii) (`T2515_ProfSpec d (UNOUProfile.ba d)`), by `rfl`. -/
theorem UNOUProfile.ba_spec (d : ℕ) :
    ∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)),
      (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false;
        (UNOUProfile.ba d).pm sz n ζ z a b =
          (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧
      (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true;
        (UNOUProfile.ba d).pp sz n ζ z a b =
          (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl⟩

end RBM.Univ

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Univ RBM.Univ.GUEPhase

/-! ## 2. The transfer to the flow point and the comparison `cT ≤ t₀` (target 2) -/

/-- `M^{(σ₁,σ₂)}(z) = t₀ M^{(σ₁,σ₂)}(λ₀, E, m₀)` (`BAzztE_data` conj. 5; `BAMss` of a real multiple is its square). -/
private theorem GUEKPrim_Mss_flow {d L : ℕ} [NeZero L] (lam : ℝ) {z : ℂ} (hz : 0 < z.im) (σ₁ σ₂ : Bool) :
    BAMss d L (BAMB d L lam z (BAm d L lam z)) σ₁ σ₂ = ((BAt0 z (BAm d L lam z) : ℝ) : ℂ) •
      BAMss d L (BAMB d L (Real.sqrt (BAt0 z (BAm d L lam z)) * lam) (BAflowE z (BAm d L lam z) : ℂ)
        (BAm d L lam z / (Real.sqrt (BAt0 z (BAm d L lam z)) : ℂ))) σ₁ σ₂ := by
  obtain ⟨ht0, -, -, -, hMB⟩ := BAzztE_data d L lam hz (BAm_self d L lam z hz)
  have hs : ∀ (c : ℝ) (M : Matrix (Zd d L) (Zd d L) ℂ), BAMss d L ((c : ℂ) • M) σ₁ σ₂ =
      ((c ^ 2 : ℝ) : ℂ) • BAMss d L M σ₁ σ₂ := fun c M => by
    ext a b
    cases σ₁ <;> cases σ₂ <;> simp [BAMss, BAMsigma, Matrix.conjTranspose_apply] <;> ring
  rw [← hMB, hs, Real.sq_sqrt ht0.le]

/-- **Target 2 (transfer, O9 core)**: at `Im z > 0`, `Θ_s` at `z` is `BATheta` at the flow point
`(λ₀, E, m₀) = (√t₀ λ, BAflowE z m, m/√t₀)` at time `s t₀` (`BAzztE_data` conj. 5; `BAMss` of a real multiple). -/
theorem baThetaTransfer :
    ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ), 0 < z.im → ∀ (s : ℝ) (σ₁ σ₂ : Bool),
      let m := BAm d L lam z; let t0 := BAt0 z m;
      PropThetaQ (BAMss d L (BAMB d L lam z m) σ₁ σ₂) s =
        BATheta d L (Real.sqrt t0 * lam) (BAflowE z m) (m / (Real.sqrt t0 : ℂ)) (s * t0) σ₁ σ₂ := by
  intro d L _ lam z hz s σ₁ σ₂ m t0
  unfold BATheta PropThetaQ
  rw [GUEKPrim_Mss_flow lam hz, smul_smul]
  push_cast
  rfl

/-- **Target 2 (UBA-C1 comparison)**: `cT = κ'/(κ'+1) ≤ t₀`, `κ' = (πκ)^5/2048` (the `cT` of `ba_flowG`), i.e.
`cT λ² ≤ λ₀² ≤ λ²`. -/
theorem baT0Cmp :
    ∀ κ : ℝ, 0 < κ → ∃ cT : ℝ, 0 < cT ∧ ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ),
      BAbulk d L lam κ z.re → 0 < z.im → z.im ≤ 1 → cT ≤ BAt0 z (BAm d L lam z) := by
  intro κ hκ
  have hk : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  refine ⟨(Real.pi * κ) ^ 5 / 2048 / ((Real.pi * κ) ^ 5 / 2048 + 1), by positivity, ?_⟩
  intro d L _ lam z hb h0 h1
  have hm := ba_dom_of_bulk d L lam κ hκ hb h0 h1
  change _ ≤ (BAm d L lam z).im / ((BAm d L lam z).im + z.im)
  rw [div_le_div_iff₀ (by linarith) (by linarith [lt_of_lt_of_le hk hm])]
  nlinarith [mul_le_mul_of_nonneg_left h1 hk.le]

/-! ## 3. The zero mode: `Θ̃_ζ = Θ_{1-ζ} + β J` for a matrix `Q` with constant row and column sums `r` -/

section Generic

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `‖X‖ < 1` (the `∞→∞` norm) makes `1 - X` a unit. -/
private theorem GUEKPrim_isUnit {X : Matrix (Zd d L) (Zd d L) ℂ} (hX : ‖X‖ < 1) : IsUnit (1 - X) :=
  ⟨Units.oneSub X hX, Units.val_oneSub X hX⟩

/-- The resolvent bound `‖(1 - X)⁻¹‖ ≤ (1 - ‖X‖)⁻¹` (`Θ = 1 + Θ X`). -/
private theorem GUEKPrim_inv_norm {X : Matrix (Zd d L) (Zd d L) ℂ} (hX : ‖X‖ < 1) :
    ‖Ring.inverse (1 - X)‖ ≤ (1 - ‖X‖)⁻¹ := by
  have h1 : Ring.inverse (1 - X) * (1 - X) = 1 := Ring.inverse_mul_cancel _ (GUEKPrim_isUnit hX)
  have h2 : Ring.inverse (1 - X) = 1 + Ring.inverse (1 - X) * X := by
    rw [mul_sub, mul_one] at h1
    exact (sub_eq_iff_eq_add.mp h1)
  have h3 : ‖Ring.inverse (1 - X)‖ ≤ 1 + ‖Ring.inverse (1 - X)‖ * ‖X‖ := by
    calc ‖Ring.inverse (1 - X)‖ = ‖1 + Ring.inverse (1 - X) * X‖ := by rw [← h2]
      _ ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖ + ‖Ring.inverse (1 - X) * X‖ := norm_add_le _ _
      _ ≤ 1 + ‖Ring.inverse (1 - X)‖ * ‖X‖ := by
          rw [norm_one]; exact add_le_add_right (norm_mul_le (Ring.inverse (1 - X)) X) _
  have h4 : 0 < 1 - ‖X‖ := by linarith
  rw [inv_eq_one_div, le_div_iff₀ h4]
  nlinarith

/-- An entry is bounded by the `∞→∞` norm. -/
private theorem GUEKPrim_entry_le (A : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) : ‖A a b‖ ≤ ‖A‖ := by
  have h1 : ‖A a b‖₊ ≤ ∑ j, ‖A a j‖₊ := Finset.single_le_sum (f := fun j => ‖A a j‖₊) (fun _ _ => zero_le)
    (Finset.mem_univ b)
  have h2 : ∑ j, ‖A a j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ a)
  exact_mod_cast h1.trans h2

/-- `t Θ_t Q = Θ_t - 1` (`Θ_t (1 - t Q) = 1`). -/
private theorem GUEKPrim_tThQ {Q : Matrix (Zd d L) (Zd d L) ℂ} {t : ℝ} (hU : IsUnit (1 - (t : ℂ) • Q)) :
    (t : ℂ) • (PropThetaQ Q t * Q) = PropThetaQ Q t - 1 := by
  have h : PropThetaQ Q t * (1 - (t : ℂ) • Q) = 1 := Ring.inverse_mul_cancel _ hU
  rw [mul_sub, mul_one, Matrix.mul_smul] at h
  exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp h).symm

/-- `Θ_s J = J Θ_s = (1 - s r)⁻¹ J`: the constant vector is the zero mode of `Θ_s` when `Q J = J Q = r J`. -/
private theorem GUEKPrim_ThJ {Q : Matrix (Zd d L) (Zd d L) ℂ} {r : ℂ} {s : ℝ} (hQJ : Q * Jmat d L = r • Jmat d L)
    (hJQ : Jmat d L * Q = r • Jmat d L) (hU : IsUnit (1 - (s : ℂ) • Q)) (hsr : 1 - (s : ℂ) * r ≠ 0) :
    PropThetaQ Q s * Jmat d L = (1 - (s : ℂ) * r)⁻¹ • Jmat d L ∧
      Jmat d L * PropThetaQ Q s = (1 - (s : ℂ) * r)⁻¹ • Jmat d L := by
  have hΘA : PropThetaQ Q s * (1 - (s : ℂ) • Q) = 1 := Ring.inverse_mul_cancel _ hU
  have hAΘ : (1 - (s : ℂ) • Q) * PropThetaQ Q s = 1 := Ring.mul_inverse_cancel _ hU
  have hAJ : (1 - (s : ℂ) • Q) * Jmat d L = (1 - (s : ℂ) * r) • Jmat d L := by
    rw [sub_mul, one_mul, Matrix.smul_mul, hQJ, smul_smul, sub_smul, one_smul]
  have hJA : Jmat d L * (1 - (s : ℂ) • Q) = (1 - (s : ℂ) * r) • Jmat d L := by
    rw [mul_sub, mul_one, Matrix.mul_smul, hJQ, smul_smul, sub_smul, one_smul]
  constructor
  · calc PropThetaQ Q s * Jmat d L
        = (1 - (s : ℂ) * r)⁻¹ • ((1 - (s : ℂ) * r) • (PropThetaQ Q s * Jmat d L)) := by
          rw [smul_smul, inv_mul_cancel₀ hsr, one_smul]
      _ = (1 - (s : ℂ) * r)⁻¹ • (PropThetaQ Q s * ((1 - (s : ℂ) * r) • Jmat d L)) := by rw [Matrix.mul_smul]
      _ = (1 - (s : ℂ) * r)⁻¹ • (PropThetaQ Q s * ((1 - (s : ℂ) • Q) * Jmat d L)) := by rw [hAJ]
      _ = (1 - (s : ℂ) * r)⁻¹ • Jmat d L := by rw [← mul_assoc, hΘA, one_mul]
  · calc Jmat d L * PropThetaQ Q s
        = (1 - (s : ℂ) * r)⁻¹ • ((1 - (s : ℂ) * r) • (Jmat d L * PropThetaQ Q s)) := by
          rw [smul_smul, inv_mul_cancel₀ hsr, one_smul]
      _ = (1 - (s : ℂ) * r)⁻¹ • (((1 - (s : ℂ) * r) • Jmat d L) * PropThetaQ Q s) := by rw [Matrix.smul_mul]
      _ = (1 - (s : ℂ) * r)⁻¹ • ((Jmat d L * (1 - (s : ℂ) • Q)) * PropThetaQ Q s) := by rw [hJA]
      _ = (1 - (s : ℂ) * r)⁻¹ • Jmat d L := by rw [mul_assoc, hAΘ, mul_one]

/-- **Sherman-Morrison with the constant row and column sums `r` of `Q`** (twin of `ThetaTilde_eq`,
`ZeroModeProfile.lean:281`, with `ξ S^{(B)}` replaced by `Q`, `S^{(B)}(0) = 1`): for `s = 1 - ζ`,
`(1 - Q S̃_ζ)⁻¹ = Θ_s + ζ r/(L^d (1 - r)(1 - s r)) J`. -/
private theorem GUEKPrim_SM {Q : Matrix (Zd d L) (Zd d L) ℂ} {r : ℂ} (hQJ : Q * Jmat d L = r • Jmat d L)
    (hJQ : Jmat d L * Q = r • Jmat d L) {ζ : ℝ} (hU : IsUnit (1 - ((1 - ζ : ℝ) : ℂ) • Q)) (h1r : 1 - r ≠ 0)
    (hsr : 1 - ((1 - ζ : ℝ) : ℂ) * r ≠ 0) :
    Ring.inverse (1 - Q * SBtilde d L 0 ζ) = PropThetaQ Q (1 - ζ) +
      ((ζ : ℂ) * r / ((L : ℂ) ^ d * (1 - r) * (1 - ((1 - ζ : ℝ) : ℂ) * r))) • Jmat d L := by
  have hL : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))
  set s : ℂ := ((1 - ζ : ℝ) : ℂ) with hs
  have hsζ : s + (ζ : ℂ) = 1 := by rw [hs]; push_cast; ring
  have hSB : SBtilde d L 0 ζ = s • (1 : Matrix (Zd d L) (Zd d L) ℂ) + ((ζ : ℂ) / (L : ℂ) ^ d) • Jmat d L := by
    unfold SBtilde
    rw [EMn2BA_SB_zero]
  have hQS : Q * SBtilde d L 0 ζ = s • Q + ((ζ : ℂ) * r / (L : ℂ) ^ d) • Jmat d L := by
    rw [hSB, mul_add, Matrix.mul_smul, mul_one, Matrix.mul_smul, hQJ, smul_smul]
    congr 2
    ring
  have hX : 1 - Q * SBtilde d L 0 ζ = (1 - s • Q) - ((ζ : ℂ) * r / (L : ℂ) ^ d) • Jmat d L := by
    rw [hQS]; abel
  set Θ := PropThetaQ Q (1 - ζ) with hΘ
  set A := 1 - s • Q with hA
  have hΘA : Θ * A = 1 := Ring.inverse_mul_cancel _ hU
  have hJA : Jmat d L * A = (1 - s * r) • Jmat d L := by
    rw [hA, mul_sub, mul_one, Matrix.mul_smul, hJQ, smul_smul, sub_smul, one_smul]
  have hΘJ : Θ * Jmat d L = (1 - s * r)⁻¹ • Jmat d L := (GUEKPrim_ThJ hQJ hJQ hU hsr).1
  have hJJ := ZeroModeProfile_Jmat_mul_Jmat d L
  set α : ℂ := (ζ : ℂ) * r / ((L : ℂ) ^ d * (1 - r) * (1 - s * r)) with hα
  set c : ℂ := (ζ : ℂ) * r / (L : ℂ) ^ d with hc
  have hcoef : α * (1 - s * r) - c * (1 - s * r)⁻¹ - α * c * (L : ℂ) ^ d = 0 := by
    rw [hα, hc]
    have hζ : (ζ : ℂ) = 1 - s := by linear_combination hsζ
    rw [hζ]
    field_simp
    ring
  have key : (Θ + α • Jmat d L) * ((1 - s • Q) - c • Jmat d L) = 1 := by
    rw [← hA]
    generalize hAA : A = A' at hΘA hJA ⊢
    calc (Θ + α • Jmat d L) * (A' - c • Jmat d L)
        = Θ * A' - c • (Θ * Jmat d L) + α • (Jmat d L * A') - (α * c) • (Jmat d L * Jmat d L) := by
          simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          module
      _ = 1 - c • ((1 - s * r)⁻¹ • Jmat d L) + α • ((1 - s * r) • Jmat d L)
          - (α * c) • (((L : ℂ) ^ d) • Jmat d L) := by rw [hΘA, hΘJ, hJA, hJJ]
      _ = 1 + (α * (1 - s * r) - c * (1 - s * r)⁻¹ - α * c * (L : ℂ) ^ d) • Jmat d L := by
          module
      _ = 1 := by rw [hcoef, zero_smul, add_zero]
  rw [hX]
  exact ZeroModeProfile_ringInverse_eq_of_mul_eq_one key

/-- A translation-invariant `Q` has constant row and column sums `r = ∑_c Q_{0c}`: `Q J = J Q = r J`. -/
private theorem GUEKPrim_QJ {Q : Matrix (Zd d L) (Zd d L) ℂ} (hT : ∀ a b r : Zd d L, Q (a + r) (b + r) = Q a b) :
    Q * Jmat d L = (∑ c, Q 0 c) • Jmat d L ∧ Jmat d L * Q = (∑ c, Q 0 c) • Jmat d L := by
  constructor
  · ext a b
    simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, mul_one, Matrix.smul_apply, smul_eq_mul]
    exact EKNonzero_row_sum hT a
  · ext a b
    simp only [Matrix.mul_apply, Jmat, Matrix.of_apply, one_mul, mul_one, Matrix.smul_apply, smul_eq_mul]
    exact EKNonzero_col_sum hT b

/-- The row sum `r₀ = ∑_c Q₀_{0c}` of `Q₀ = M^{(σ₁σ₂)}` at real data is at most `1` in modulus
(`|Q₀_{ab}| = BAK_{ab}`, unit row sums). -/
private theorem GUEKPrim_r0_norm {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) :
    ‖∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c‖ ≤ 1 := by
  refine (norm_sum_le _ _).trans ?_
  simp only [BAMss_norm_eq_BAK]
  exact (BAK_row_sum d L g E m hr.1 0).le

/-- `‖t r₀‖ < 1` for `0 ≤ t < 1`. -/
private theorem GUEKPrim_tr_norm {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : ‖(t : ℂ) * ∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  calc t * ‖∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c‖ ≤ t * 1 :=
        mul_le_mul_of_nonneg_left (GUEKPrim_r0_norm hr σ₁ σ₂) ht0
    _ < 1 := by linarith

/-- **The BA zero-mode identity** (twin of `ThetaTilde_eq`): for the real data `(g, E, m)`, `t₀ ∈ [0,1)` and
`ζ ∈ [0,1]`, `Θ̃_ζ = (1 - t₀ Q₀ S̃_ζ)⁻¹ = Θ_{(1-ζ) t₀}(Q₀) + β J`, `Q₀ = M^{(σ₁σ₂)}`, `r₀ = ∑_c Q₀_{0c}`,
`β = gueShift d L r₀ ((1-ζ) t₀) t₀ = ζ t₀ r₀ / (L^d (1 - t₀ r₀)(1 - (1-ζ) t₀ r₀))`. -/
theorem baThetaTilde_eq {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t0 : ℝ} (ht0 : 0 ≤ t0) (ht1 : t0 < 1)
    {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (σ₁ σ₂ : Bool) :
    Ring.inverse (1 - ((t0 : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * SBtilde d L 0 ζ) =
      BATheta d L g E m ((1 - ζ) * t0) σ₁ σ₂ +
        gueShift d L (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) ((1 - ζ) * t0) t0 • Jmat d L := by
  have hs0 : 0 ≤ (1 - ζ) * t0 := mul_nonneg (by linarith) ht0
  have hs1 : (1 - ζ) * t0 < 1 := by nlinarith
  obtain ⟨hQJ, hJQ⟩ := GUEKPrim_QJ (d := d) (L := L)
    (fun a b r => EKNonzero_Mss_shift (d := d) (L := L) g E m σ₁ σ₂ a b r)
  set Q₀ := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ with hQ₀
  set r₀ := ∑ c, Q₀ 0 c with hr₀
  have e : ((1 - ζ : ℝ) : ℂ) • ((t0 : ℂ) • Q₀) = (((1 - ζ) * t0 : ℝ) : ℂ) • Q₀ := by
    rw [smul_smul, ← Complex.ofReal_mul]
  have hU : IsUnit (1 - ((1 - ζ : ℝ) : ℂ) • ((t0 : ℂ) • Q₀)) := by
    rw [e]; exact BATheta_isUnit d L g κ E m hr ((1 - ζ) * t0) hs0 hs1 σ₁ σ₂
  have hn1 : 1 - (t0 : ℂ) * r₀ ≠ 0 := by
    have : ‖(t0 : ℂ) * r₀‖ < 1 := GUEKPrim_tr_norm hr σ₁ σ₂ ht0 ht1
    intro h
    have h' : (t0 : ℂ) * r₀ = 1 := by linear_combination -h
    rw [h', norm_one] at this
    exact lt_irrefl _ this
  have hn2 : 1 - ((1 - ζ : ℝ) : ℂ) * ((t0 : ℂ) * r₀) ≠ 0 := by
    have : ‖(((1 - ζ) * t0 : ℝ) : ℂ) * r₀‖ < 1 := GUEKPrim_tr_norm hr σ₁ σ₂ hs0 hs1
    intro h
    have h' : (((1 - ζ) * t0 : ℝ) : ℂ) * r₀ = 1 := by
      push_cast at h ⊢; linear_combination -h
    rw [h', norm_one] at this
    exact lt_irrefl _ this
  have hQJ' : ((t0 : ℂ) • Q₀) * Jmat d L = ((t0 : ℂ) * r₀) • Jmat d L := by
    rw [Matrix.smul_mul, hQJ, smul_smul]
  have hJQ' : Jmat d L * ((t0 : ℂ) • Q₀) = ((t0 : ℂ) * r₀) • Jmat d L := by
    rw [Matrix.mul_smul, hJQ, smul_smul]
  have hSM := GUEKPrim_SM hQJ' hJQ' hU hn1 hn2
  rw [hSM]
  have eΘ : PropThetaQ ((t0 : ℂ) • Q₀) (1 - ζ) = BATheta d L g E m ((1 - ζ) * t0) σ₁ σ₂ := by
    unfold PropThetaQ BATheta
    rw [e]
    rfl
  rw [eΘ]
  congr 2
  unfold gueShift
  push_cast
  rw [hr₀]
  field_simp
  ring

end Generic

/-! ## 4. The profile at complex `z`: structure, the lossless oscillation (O9), row differences -/

section Profile

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `M^{(+,σ)}(z)` of the profile text. -/
private abbrev GUEKPrim_Q (d L : ℕ) [NeZero L] (lam : ℝ) (z : ℂ) (σ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ

/-- The flow point of `z`: `0 < t₀ < 1` and `(√t₀ λ, Im m, E, m/√t₀)` are real data (`BAdom_real` at `κ = Im m`; no
bulk is used). -/
private theorem GUEKPrim_flow (lam : ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < BAt0 z (BAm d L lam z) ∧ BAt0 z (BAm d L lam z) < 1 ∧
      BAReal d L (Real.sqrt (BAt0 z (BAm d L lam z)) * lam) (BAm d L lam z).im (BAflowE z (BAm d L lam z))
        (BAm d L lam z / (Real.sqrt (BAt0 z (BAm d L lam z)) : ℂ)) := by
  have hm := BAm_self d L lam z hz
  exact ⟨BAt0_pos hz hm.1, BAt0_lt_one hz hm.1, BAdom_real hz hm le_rfl⟩

/-- **Structure at complex `z`, `s ∈ [0,1]`**: `1 - s Q` is a unit, `s Θ_s Q = Θ_s - 1`, and for `s ≤ 1/2` the
entries of `Θ_s Q` are bounded by `2` (`‖Q‖_{∞→∞} ≤ t₀ < 1`, `‖Θ_s‖ ≤ (1 - s t₀)⁻¹ ≤ 2`). -/
private theorem GUEKPrim_struct (lam : ℝ) {z : ℂ} (hz : 0 < z.im) (σ : Bool) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsUnit (1 - (s : ℂ) • GUEKPrim_Q d L lam z σ) ∧
      (s : ℂ) • (PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) =
        PropThetaQ (GUEKPrim_Q d L lam z σ) s - 1 ∧
      (s ≤ 1 / 2 → ∀ a b, ‖(PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) a b‖ ≤ 2) := by
  obtain ⟨ht0, ht1, hreal⟩ := GUEKPrim_flow (d := d) (L := L) lam hz
  set t0 := BAt0 z (BAm d L lam z) with ht0def
  have hQ := GUEKPrim_Mss_flow (d := d) (L := L) lam hz true σ
  have hQ₀ := EKNonzero_norm_Q_le hreal true σ
  have hQn : ‖GUEKPrim_Q d L lam z σ‖ ≤ t0 := by
    change ‖BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ‖ ≤ t0
    rw [hQ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    calc t0 * _ ≤ t0 * 1 := mul_le_mul_of_nonneg_left hQ₀ ht0.le
      _ = t0 := mul_one _
  have hsQ : ‖(s : ℂ) • GUEKPrim_Q d L lam z σ‖ ≤ s * t0 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left hQn hs0
  have hst : s * t0 < 1 := by nlinarith
  have hlt : ‖(s : ℂ) • GUEKPrim_Q d L lam z σ‖ < 1 := lt_of_le_of_lt hsQ hst
  have hU : IsUnit (1 - (s : ℂ) • GUEKPrim_Q d L lam z σ) := GUEKPrim_isUnit hlt
  refine ⟨hU, GUEKPrim_tThQ hU, fun hs12 a b => ?_⟩
  have hsQ2 : ‖(s : ℂ) • GUEKPrim_Q d L lam z σ‖ ≤ 1 / 2 := hsQ.trans (by nlinarith)
  have hΘ : ‖PropThetaQ (GUEKPrim_Q d L lam z σ) s‖ ≤ 2 := by
    refine (GUEKPrim_inv_norm hlt).trans ?_
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  calc ‖(PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) a b‖
      ≤ ‖PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ‖ := GUEKPrim_entry_le _ a b
    _ ≤ ‖PropThetaQ (GUEKPrim_Q d L lam z σ) s‖ * ‖GUEKPrim_Q d L lam z σ‖ := norm_mul_le _ _
    _ ≤ 2 * 1 := mul_le_mul hΘ (hQn.trans ht1.le) (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

/-- Row-0 reduction: `Θ_{ab} - Θ_{a'b'} = Θ̊_{0,b-a} - Θ̊_{0,b'-a'}` (`baP8_BATheta_shift`; the zero mode is constant). -/
private theorem GUEKPrim_diff (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) {B : ℝ}
    (hB : ∀ x, ‖BATheta0 d L g E m t σ₁ σ₂ 0 x‖ ≤ B) (a b a' b' : Zd d L) :
    ‖BATheta d L g E m t σ₁ σ₂ a b - BATheta d L g E m t σ₁ σ₂ a' b'‖ ≤ 2 * B := by
  have hsh : ∀ a b, BATheta d L g E m t σ₁ σ₂ a b = BATheta d L g E m t σ₁ σ₂ 0 (b - a) := fun a b => by
    simpa using baP8_BATheta_shift g E m t σ₁ σ₂ 0 (b - a) a
  have h0 : ∀ x y, BATheta d L g E m t σ₁ σ₂ 0 x - BATheta d L g E m t σ₁ σ₂ 0 y =
      BATheta0 d L g E m t σ₁ σ₂ 0 x - BATheta0 d L g E m t σ₁ σ₂ 0 y := fun x y => by simp [BATheta0]
  rw [hsh a b, hsh a' b', h0]
  calc _ ≤ ‖BATheta0 d L g E m t σ₁ σ₂ 0 (b - a)‖ + ‖BATheta0 d L g E m t σ₁ σ₂ 0 (b' - a')‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hB _) (hB _)
    _ = 2 * B := by ring

/-- **The lossless oscillation of `Θ_s` at the flow point (O9)**, every `s ∈ [0,1]`: `C = 2 C₈ / cT`, `C₈ = C₈(d, 𝔡⁻¹, κ')`
of `baProp8_holds` at `κ' = (πκ)^5/2048`, `(g₀² + |1 - s t₀|)⁻¹ ≤ (cT λ²)⁻¹`; no `W^τ`, no `≺`. -/
private theorem GUEKPrim_osc_core (d : ℕ) (hd : 3 ≤ d) (𝔡 κ : ℝ) (h𝔡 : 0 < 𝔡) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d L lam κ z.re → ∀ (σ : Bool) (s : ℝ), 0 ≤ s → s ≤ 1 →
        ∀ a b a' b' : Zd d L, ‖PropThetaQ (GUEKPrim_Q d L lam z σ) s a b -
          PropThetaQ (GUEKPrim_Q d L lam z σ) s a' b'‖ ≤ C * (lam ^ 2)⁻¹ := by
  have hκ' : 0 < (Real.pi * κ) ^ 5 / 2048 := by positivity
  obtain ⟨C₈, hC₈, H⟩ := baProp8_holds d 𝔡⁻¹ ((Real.pi * κ) ^ 5 / 2048) hd (inv_pos.2 h𝔡) hκ'
  obtain ⟨cT, hcT, hcmp⟩ := baT0Cmp κ hκ
  refine ⟨2 * C₈ / cT, by positivity, fun L _ hL lam hlam hlamΛ z hz hz1 hb σ s hs0 hs1 a b a' b' => ?_⟩
  have hm := BAm_self d L lam z hz
  have hreal := BAdom_real hz hm (ba_dom_of_bulk d L lam κ hκ hb hz hz1)
  have hc := hcmp d L lam z hb hz hz1
  have ht0 := BAt0_pos hz hm.1
  have ht1 := BAt0_lt_one hz hm.1
  set t0 := BAt0 z (BAm d L lam z) with ht0def
  have hg0 : 0 < Real.sqrt t0 * lam := mul_pos (Real.sqrt_pos.2 ht0) hlam
  have hΘ := baThetaTransfer d L lam z hz s true σ
  have hst0 : 0 ≤ s * t0 := by positivity
  have hst1 : s * t0 < 1 := by nlinarith
  have hbound : ∀ x : Zd d L, ‖BATheta0 d L (Real.sqrt t0 * lam) (BAflowE z (BAm d L lam z))
      (BAm d L lam z / (Real.sqrt t0 : ℂ)) (s * t0) true σ 0 x‖ ≤ C₈ * (cT * lam ^ 2)⁻¹ := by
    intro x
    refine (H L hL _ hg0 ((BAg0_le hlam.le hz hm.1).trans hlamΛ) _ _ hreal (s * t0) hst0 hst1 true σ x).trans ?_
    have h1 : ((Real.sqrt t0 * lam) ^ 2 + |1 - s * t0|)⁻¹ ≤ (cT * lam ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by
        rw [mul_pow, Real.sq_sqrt ht0.le]
        nlinarith [abs_nonneg (1 - s * t0), mul_le_mul_of_nonneg_right hc (sq_nonneg lam)])
    have h2 : (((zdistD d L x : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by have : (0 : ℝ) ≤ zdistD d L x := Nat.cast_nonneg _; linarith))
    calc _ ≤ C₈ * (cT * lam ^ 2)⁻¹ * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₈.le) h2 (by positivity) (by positivity)
      _ = _ := mul_one _
  change ‖PropThetaQ (BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ) s a b -
    PropThetaQ (BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ) s a' b'‖ ≤ _
  rw [hΘ]
  refine (GUEKPrim_diff _ _ _ _ true σ hbound a b a' b').trans (le_of_eq ?_)
  field_simp

/-- **Row differences of `Θ_s Q`, every `s ∈ [0,1]`**: `C = 4 C₈/cT + 4 𝔡⁻²`.  For `s ≥ 1/2`: `Θ_s Q = (Θ_s - 1)/s`,
`s⁻¹ ≤ 2`, the oscillation `GUEKPrim_osc_core`, `|δ_{ab} - δ_{ab'}| ≤ 1 ≤ 𝔡⁻² λ⁻²`; for `s < 1/2`: the entries of `Θ_s Q` are
at most `2` (`GUEKPrim_struct`) and `4 ≤ 4 𝔡⁻² λ⁻²`. -/
private theorem GUEKPrim_rowdiff (d : ℕ) (hd : 3 ≤ d) (𝔡 κ : ℝ) (h𝔡 : 0 < 𝔡) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d L lam κ z.re → ∀ (σ : Bool) (s : ℝ), 0 ≤ s → s ≤ 1 →
        ∀ a b b' : Zd d L, ‖(PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) a b -
          (PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) a b'‖ ≤ C * (lam ^ 2)⁻¹ := by
  obtain ⟨C, hC, H⟩ := GUEKPrim_osc_core d hd 𝔡 κ h𝔡 hκ
  refine ⟨2 * C + 4 * 𝔡⁻¹ ^ 2, by positivity, fun L _ hL lam hlam hlamΛ z hz hz1 hb σ s hs0 hs1 a b b' => ?_⟩
  obtain ⟨hU, hΘQ, hbd⟩ := GUEKPrim_struct (d := d) (L := L) lam hz σ hs0 hs1
  have h2 : 1 ≤ 𝔡⁻¹ ^ 2 * (lam ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_pow]; exact one_le_pow₀ ((one_le_div hlam).2 hlamΛ)
  have hC0 : 0 ≤ C * (lam ^ 2)⁻¹ := by positivity
  rcases le_or_gt (1 / 2) s with hs | hs
  · have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (by linarith : s ≠ 0)
    have e : ∀ x y : Zd d L, (PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) x y =
        (s : ℂ)⁻¹ * (PropThetaQ (GUEKPrim_Q d L lam z σ) s x y - (1 : Matrix (Zd d L) (Zd d L) ℂ) x y) := by
      intro x y
      have := congrFun (congrFun hΘQ x) y
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this
      rw [← this]; field_simp
    have h1 : ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a b - (1 : Matrix (Zd d L) (Zd d L) ℂ) a b'‖ ≤ 1 := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    have hsi : ‖(s : ℂ)⁻¹‖ ≤ 2 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      calc s⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) hs
        _ = 2 := by norm_num
    have hosc := H L hL lam hlam hlamΛ z hz hz1 hb σ s hs0 hs1 a b a b'
    rw [e a b, e a b', ← mul_sub, norm_mul]
    have hin : ‖PropThetaQ (GUEKPrim_Q d L lam z σ) s a b - (1 : Matrix (Zd d L) (Zd d L) ℂ) a b -
        (PropThetaQ (GUEKPrim_Q d L lam z σ) s a b' - (1 : Matrix (Zd d L) (Zd d L) ℂ) a b')‖ ≤
        C * (lam ^ 2)⁻¹ + 1 := by
      calc _ = ‖(PropThetaQ (GUEKPrim_Q d L lam z σ) s a b - PropThetaQ (GUEKPrim_Q d L lam z σ) s a b') -
            ((1 : Matrix (Zd d L) (Zd d L) ℂ) a b - (1 : Matrix (Zd d L) (Zd d L) ℂ) a b')‖ := by congr 1; ring
        _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hosc h1)
    calc ‖(s : ℂ)⁻¹‖ * _ ≤ 2 * (C * (lam ^ 2)⁻¹ + 1) :=
          mul_le_mul hsi hin (norm_nonneg _) (by norm_num)
      _ ≤ (2 * C + 4 * 𝔡⁻¹ ^ 2) * (lam ^ 2)⁻¹ := by nlinarith [inv_nonneg.2 (sq_nonneg lam)]
  · have hb1 := hbd hs.le a b
    have hb2 := hbd hs.le a b'
    calc _ ≤ ‖(PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) a b‖ +
          ‖(PropThetaQ (GUEKPrim_Q d L lam z σ) s * GUEKPrim_Q d L lam z σ) a b'‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := add_le_add hb1 hb2
      _ ≤ (2 * C + 4 * 𝔡⁻¹ ^ 2) * (lam ^ 2)⁻¹ := by nlinarith [inv_nonneg.2 (sq_nonneg lam)]

/-- The zero-mode form of the profile matrix at complex `z`: `Θ̃_ζ = Θ_{1-ζ} + β J` and `J Q = ρ J` for some `β ρ`
(`baThetaTilde_eq` at the flow point, `Q = t₀ Q₀`, the transfer `baThetaTransfer`). -/
private theorem GUEKPrim_tilde (lam : ℝ) {z : ℂ} (hz : 0 < z.im) (σ : Bool) {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) :
    ∃ β ρ : ℂ, Ring.inverse (1 - GUEKPrim_Q d L lam z σ * SBtilde d L 0 ζ) =
        PropThetaQ (GUEKPrim_Q d L lam z σ) (1 - ζ) + β • Jmat d L ∧
      Jmat d L * GUEKPrim_Q d L lam z σ = ρ • Jmat d L := by
  obtain ⟨ht0, ht1, hreal⟩ := GUEKPrim_flow (d := d) (L := L) lam hz
  set t0 := BAt0 z (BAm d L lam z) with ht0def
  set Q₀ := BAMss d L (BAMB d L (Real.sqrt t0 * lam) (BAflowE z (BAm d L lam z) : ℂ)
    (BAm d L lam z / (Real.sqrt t0 : ℂ))) true σ with hQ₀
  have hQ : GUEKPrim_Q d L lam z σ = (t0 : ℂ) • Q₀ := GUEKPrim_Mss_flow (d := d) (L := L) lam hz true σ
  have hSM := baThetaTilde_eq hreal ht0.le ht1 h0 h1 true σ
  have hΘ : PropThetaQ (GUEKPrim_Q d L lam z σ) (1 - ζ) =
      BATheta d L (Real.sqrt t0 * lam) (BAflowE z (BAm d L lam z)) (BAm d L lam z / (Real.sqrt t0 : ℂ))
        ((1 - ζ) * t0) true σ := baThetaTransfer d L lam z hz (1 - ζ) true σ
  obtain ⟨-, hJQ⟩ := GUEKPrim_QJ (d := d) (L := L) (Q := Q₀)
    (fun a b r => EKNonzero_Mss_shift (d := d) (L := L) _ _ _ true σ a b r)
  refine ⟨gueShift d L (∑ c, Q₀ 0 c) ((1 - ζ) * t0) t0, (t0 : ℂ) * ∑ c, Q₀ 0 c, ?_, ?_⟩
  · rw [hΘ, hQ]
    exact hSM
  · rw [hQ, Matrix.mul_smul, hJQ, smul_smul]

/-- Row differences of the profile matrix `Θ̃_ζ Q` are those of `Θ_{1-ζ} Q` (`β J Q` is a constant matrix). -/
private theorem GUEKPrim_prof_diff (lam : ℝ) {z : ℂ} (hz : 0 < z.im) (σ : Bool) {ζ : ℝ} (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1)
    (a b b' : Zd d L) :
    (Ring.inverse (1 - GUEKPrim_Q d L lam z σ * SBtilde d L 0 ζ) * GUEKPrim_Q d L lam z σ) a b -
        (Ring.inverse (1 - GUEKPrim_Q d L lam z σ * SBtilde d L 0 ζ) * GUEKPrim_Q d L lam z σ) a b' =
      (PropThetaQ (GUEKPrim_Q d L lam z σ) (1 - ζ) * GUEKPrim_Q d L lam z σ) a b -
        (PropThetaQ (GUEKPrim_Q d L lam z σ) (1 - ζ) * GUEKPrim_Q d L lam z σ) a b' := by
  obtain ⟨β, ρ, hΘ, hJQ⟩ := GUEKPrim_tilde (d := d) (L := L) lam hz σ h0 h1
  rw [hΘ, add_mul, Matrix.smul_mul, hJQ, smul_smul]
  simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, Matrix.of_apply, smul_eq_mul, mul_one]
  ring

end Profile

/-! ## 5. Targets 3-6 -/

/-- **Target 3 (O9, lossless oscillation of `Θ̃^{BA}_ζ`)**: twin of `norm_ThetaTilde_sub_le`
(`ZeroModeProfile.lean:367`): `C = 2 C₈ / cT` with `C₈ = C₈(d, 𝔡⁻¹, κ')` of `baProp8_holds` at `κ' = (πκ)^5/2048`
and `cT = κ'/(κ'+1)`, uniform in `L`, `ζ ∈ [0,1]`, `z`; no `W^{τ'}`.  The `β J` part of `baThetaTilde_eq` cancels. -/
theorem baThetaTilde_osc :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
        ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d L lam κ z.re → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
          ∀ (σ : Bool) (u v : Zd d L),
            let Q := BAMss d L (BAMB d L lam z (BAm d L lam z)) true σ;
            ‖Ring.inverse (1 - Q * SBtilde d L 0 ζ) u v - Ring.inverse (1 - Q * SBtilde d L 0 ζ) 0 0‖ ≤
              C * (lam ^ 2)⁻¹ := by
  intro d hd 𝔡 κ h𝔡 hκ
  obtain ⟨C, hC, H⟩ := GUEKPrim_osc_core d hd 𝔡 κ h𝔡 hκ
  refine ⟨C, hC, fun L _ hL lam hlam hlamΛ z hz hz1 hb ζ hζ0 hζ1 σ u v => ?_⟩
  obtain ⟨β, ρ, hΘ, -⟩ := GUEKPrim_tilde (d := d) (L := L) lam hz σ hζ0 hζ1
  intro Q
  have h := H L hL lam hlam hlamΛ z hz hz1 hb σ (1 - ζ) (by linarith) (by linarith) u v 0 0
  change ‖Ring.inverse (1 - GUEKPrim_Q d L lam z σ * SBtilde d L 0 ζ) u v -
    Ring.inverse (1 - GUEKPrim_Q d L lam z σ * SBtilde d L 0 ζ) 0 0‖ ≤ _
  rw [hΘ]
  simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, Matrix.of_apply, smul_eq_mul, mul_one]
  convert h using 2
  ring

/-- **Target 6 (the BA `thetaDiff` at `ζ = 0`, Q4 (c))**, in the consumer form of `queRowDiff`
(`Main/QUEFromQDiff.lean:244`) on the end profile `(Θ M)^{(+,σ)}/W^d` (`= BAprof sz n z true σ`, T2449 probe `:164`):
lossless, `C = C(d, 𝔡, κ)` (`GUEKPrim_rowdiff` at `s = 1`: property 8 at the flow point), no `W^τ`. -/
theorem baThetaDiff :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
      ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
        ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re →
          ∀ (σ : Bool) (a b b' : Zd d (sz.L n)),
            let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ;
            ‖(PropThetaQ Q 1 * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d - (PropThetaQ Q 1 * Q) a b' / ((sz.W n : ℕ) : ℂ) ^ d‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
  intro d hd 𝔡 κ h𝔡 hκ
  obtain ⟨C, hC, H⟩ := GUEKPrim_rowdiff d hd 𝔡 κ h𝔡 hκ
  refine ⟨C, hC, fun sz n hl hl1 z hz hz1 hb σ a b b' => ?_⟩
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
  have hWc : ‖((sz.W n : ℕ) : ℂ) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by rw [norm_pow, Complex.norm_natCast]
  intro Q
  rw [← sub_div, norm_div, hWc]
  exact div_le_div_of_nonneg_right (H (sz.L n) (sz.three_le_L n) (sz.lam n) hl hl1 z hz hz1 hb σ 1 zero_le_one le_rfl
    a b b') hW.le

/-- **Target 4**: `UNOUProfRowk` (`OUInterfaceK:56`, read by name, merged text at exact type) at the BA profile:
lossless (O9), `C = C(d, 𝔡, κ)` before `sz`, uniformly in `ζ ∈ [0,1]` (consumer: N2, `ouRowk_of_pins`, premise `hprof`).
The proof is `GUEKPrim_prof_diff` (the zero mode `β J Q` is constant) and `GUEKPrim_rowdiff` with `s = 1 - ζ`. -/
theorem baOUProfRowk_holds : ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (UNKind.ba d) (UNOUProfile.ba d) := by
  intro d hd 𝔡 κ h𝔡 hκ
  obtain ⟨C, hC, H⟩ := GUEKPrim_rowdiff d hd 𝔡 κ h𝔡 hκ
  refine ⟨C, hC, fun sz n hl hl1 z hz hz1 hb ζ hζ0 hζ1 a b b' => ?_⟩
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
  have hWc : ‖((sz.W n : ℕ) : ℂ) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by rw [norm_pow, Complex.norm_natCast]
  have key : ∀ σ : Bool, ‖(Ring.inverse (1 - GUEKPrim_Q d (sz.L n) (sz.lam n) z σ * SBtilde d (sz.L n) 0 ζ) *
        GUEKPrim_Q d (sz.L n) (sz.lam n) z σ) a b / ((sz.W n : ℕ) : ℂ) ^ d -
      (Ring.inverse (1 - GUEKPrim_Q d (sz.L n) (sz.lam n) z σ * SBtilde d (sz.L n) 0 ζ) *
        GUEKPrim_Q d (sz.L n) (sz.lam n) z σ) a b' / ((sz.W n : ℕ) : ℂ) ^ d‖ ≤
        C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
    intro σ
    rw [← sub_div, norm_div, hWc, GUEKPrim_prof_diff (d := d) (L := sz.L n) (sz.lam n) hz σ hζ0 hζ1 a b b']
    exact div_le_div_of_nonneg_right
      (H (sz.L n) (sz.three_le_L n) (sz.lam n) hl hl1 z hz hz1 hb σ (1 - ζ) (by linarith) (by linarith) a b b') hW.le
  exact ⟨key false, key true⟩

/-- **Target 5**: the profile half of `RBG_Comp` at BA: `RBG_ProfComp (UNKind.ba d) (UNOUProfile.ba d)` (`rfl`: the
profile reads `sz.L n`, `sz.lam n`, `sz.W n` at the index only; as `RandomLayerBG_profComp_band`).  Consumer: N2
(`RandomLayerBGBA_comp d (baProfComp d)` → `g1Rowk_of_inputsG`). -/
theorem baProfComp (d : ℕ) : RBG_ProfComp (UNKind.ba d) (UNOUProfile.ba d) :=
  fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩

/-- **Target 6 (the `ζ = 0` bridge)**: at `ζ = 0` the profile is the end profile of `BAEnd_QDiffL` (`BAprof sz n z true σ`,
T2449 probe `:164`, `(PropThetaQ Q 1 * Q)_{ab}/W^d`): `T2515_ProfZero`, for every profile `P` with the text of D1 (iii). -/
theorem _root_.RBM.Univ.UNOUProfile.ba_zero (d : ℕ) :
    ∀ P : UNOUProfile (UNKind.ba d),
      (∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)),
        (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false;
          P.pm sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧
        (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true;
          P.pp sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)) →
      ∀ (sz : Sizes d) (n : ℕ) (z : ℂ) (σ : Bool) (a b : Zd d (sz.L n)),
        (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ;
          (if σ then P.pp sz n 0 z a b else P.pm sz n 0 z a b) = (PropThetaQ Q 1 * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) := by
  intro P hP sz n z σ a b
  have h0 : ∀ Q : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ,
      Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 0) = PropThetaQ Q 1 := fun Q => by
    simp [SBtilde, EMn2BA_SB_zero, PropThetaQ]
  cases σ
  · simp only [Bool.false_eq_true, ite_false]; rw [(hP sz n 0 z a b).1, h0]
  · simp only [ite_true]; rw [(hP sz n 0 z a b).2, h0]

/-! ## 6. The BA GUE-phase 2-loop primitive (target 7) -/

/-- **The 2-loop primitive of the GUE phase at BA** (twin of `kTwoGUE`, `KPrim.lean:68`, at the flow point `(g, E, m)`):
`K_{t,σ,(a,b)} = W^{-d} ((Θ_{t₁}(Q₀) + β_r(t) J) Q₀)_{ab}`, `Q₀ = M^{(σ₁,σ₂)}`, `r = ∑_c Q₀_{0c}` (the row sum),
`β_r = gueShift d L r t₁ t`.  At `t = t₁` this is the 2-loop `W^{-d} Θ_{t₁} M^{(σσ')}` of `baKsolve`
(`kTwoGUEBA_self`); it solves (7.33) at `n = 2` (`hasDerivAt_kTwoGUELoopBA`) and is `W^{-d} Θ̃_ζ Q₀` at `t₀` for
`t₁ = (1 - ζ) t₀` (`kTwoGUEBA_eq_ThetaTilde`). -/
def kTwoGUEBA (d L : ℕ) [NeZero L] (W : ℕ) (g E : ℝ) (m : ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) : ℂ :=
  let Q₀ := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂
  ((W : ℂ) ^ d)⁻¹ * ((BATheta d L g E m t1 σ₁ σ₂ + gueShift d L (∑ c, Q₀ 0 c) t1 t • Jmat d L) * Q₀) a b

/-- `kTwoGUEBA` on loop indices (`0` off the 2-loops; band twin `kTwoGUELoop`, `KPrim.lean:75`). -/
def kTwoGUELoopBA (d L : ℕ) [NeZero L] (W : ℕ) (g E : ℝ) (m : ℂ) (t1 t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwoGUEBA d L W g E m t1 t σ₁ σ₂ a₁ a₂
  | _, _ => 0

/-- At `t = t₁` the BA GUE-phase 2-loop primitive is the 2-loop `W^{-d} (Θ_{t₁} M^{(σσ')})_{ab}` of `baKsolve`
(`BAKsolve`, `BA/KSolve.lean:58`): `K` is continuous across the switch of the flow at `t₁`. -/
theorem kTwoGUEBA_self (d L : ℕ) [NeZero L] (W : ℕ) (g E : ℝ) (m : ℂ) (t1 : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    kTwoGUEBA d L W g E m t1 t1 σ₁ σ₂ a b =
      ((W : ℂ) ^ d)⁻¹ * (BATheta d L g E m t1 σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b := by
  simp [kTwoGUEBA, gueShift]

section TwoLoop

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- **(7.25) and the zero mode at BA**: at `t₀`, with `t₁ = (1 - ζ) t₀`, the 2-loop primitive of the GUE phase is
`W^{-d} (Θ̃_ζ Q₀)_{ab}`, `Θ̃_ζ = (1 - t₀ Q₀ S̃_ζ)⁻¹` (`baThetaTilde_eq`; twin of `kTwoGUE_eq_ThetaTilde`). -/
theorem kTwoGUEBA_eq_ThetaTilde (d L W : ℕ) [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m)
    {t0 ζ : ℝ} (ht0 : 0 ≤ t0) (ht1 : t0 < 1) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    kTwoGUEBA d L W g E m ((1 - ζ) * t0) t0 σ₁ σ₂ a b =
      ((W : ℂ) ^ d)⁻¹ * (Ring.inverse (1 - ((t0 : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) *
        SBtilde d L 0 ζ) * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b := by
  rw [baThetaTilde_eq hr ht0 ht1 h0 h1 σ₁ σ₂]
  rfl

/-- `kTwoGUEBA` through the row sum `μ` of `Q₀`: `W^{-d} ((Θ_{t₁} Q₀)_{ab} + μ β_μ(t))` (`J Q₀ = μ J`). -/
private theorem GUEKPrim_kTwo_eq (W : ℕ) (g E : ℝ) (m : ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    kTwoGUEBA d L W g E m t1 t σ₁ σ₂ a b = ((W : ℂ) ^ d)⁻¹ *
      ((BATheta d L g E m t1 σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b +
        (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) *
          gueShift d L (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) t1 t) := by
  obtain ⟨-, hJQ⟩ := GUEKPrim_QJ (d := d) (L := L) (Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)
    (fun a b r => EKNonzero_Mss_shift (d := d) (L := L) g E m σ₁ σ₂ a b r)
  simp only [kTwoGUEBA]
  rw [add_mul, Matrix.smul_mul, hJQ, smul_smul]
  simp only [Matrix.add_apply, Matrix.smul_apply, Jmat, Matrix.of_apply, smul_eq_mul, mul_one]
  ring

/-- **The derivative of the closed form, abstract data**: `Q₀` with `Q₀ J = J Q₀ = μ J`, `Θ` with
`Θ J = J Θ = (1 - t₁ μ)⁻¹ J`; `K_s(a,b) = W^{-d} ((Θ Q₀)_{ab} + μ β_μ(s))`, `β_μ = gueShift d L μ t₁`.  Row and
column sums of `Θ Q₀` are `μ (1 - t₁ μ)⁻¹`; the scalar identity is the merged `kTwoGUE_deriv_identity`. -/
private theorem GUEKPrim_deriv_abs (d L W : ℕ) [NeZero L] [NeZero W] (Q₀ Θ : Matrix (Zd d L) (Zd d L) ℂ) (μ : ℂ)
    {t1 t : ℝ} (hQJ : Q₀ * Jmat d L = μ • Jmat d L) (hJQ : Jmat d L * Q₀ = μ • Jmat d L)
    (hΘJ : Θ * Jmat d L = (1 - (t1 : ℂ) * μ)⁻¹ • Jmat d L) (hJΘ : Jmat d L * Θ = (1 - (t1 : ℂ) * μ)⁻¹ • Jmat d L)
    (hp0 : 1 - (t1 : ℂ) * μ ≠ 0) (hq0 : (1 : ℂ) - (t : ℂ) * μ ≠ 0) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s : ℝ => ((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) a₁ a₂ + μ * gueShift d L μ t1 s))
      ((W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        (((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) a₁ a + μ * gueShift d L μ t1 t)) * SBgue d L a b *
          (((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) b a₂ + μ * gueShift d L μ t1 t))) t := by
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have hLd0 : (L : ℂ) ^ d ≠ 0 := pow_ne_zero d hL0
  set p : ℂ := 1 - (t1 : ℂ) * μ with hp
  have hrow : ∀ a : Zd d L, ∑ b : Zd d L, (Θ * Q₀) a b = μ * p⁻¹ := by
    intro a
    have h1 : (Θ * Q₀) * Jmat d L = (μ * p⁻¹) • Jmat d L := by
      rw [mul_assoc, hQJ, Matrix.mul_smul, hΘJ, smul_smul, mul_comm]
    have := congrFun (congrFun h1 a) 0
    simpa [Matrix.mul_apply, Jmat] using this
  have hcol : ∀ b : Zd d L, ∑ a : Zd d L, (Θ * Q₀) a b = μ * p⁻¹ := by
    intro b
    have h1 : Jmat d L * (Θ * Q₀) = (μ * p⁻¹) • Jmat d L := by
      rw [← mul_assoc, hJΘ, Matrix.smul_mul, hJQ, smul_smul, mul_comm]
    have := congrFun (congrFun h1 0) b
    simpa [Matrix.mul_apply, Jmat] using this
  set Θab := (Θ * Q₀) a₁ a₂ with hΘab
  have hf : HasDerivAt (fun w : ℂ => (w - t1) * μ) μ (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).sub_const (t1 : ℂ)).mul_const μ
  have hg : HasDerivAt (fun w : ℂ => (L : ℂ) ^ d * p * (1 - w * μ)) ((L : ℂ) ^ d * p * -μ) (t : ℂ) := by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const μ).const_sub 1).const_mul ((L : ℂ) ^ d * p)
  have hgt : (L : ℂ) ^ d * p * (1 - (t : ℂ) * μ) ≠ 0 := mul_ne_zero (mul_ne_zero hLd0 hp0) hq0
  have hdiv := hf.div hg hgt
  have hG := (((hdiv.const_mul μ).const_add Θab).const_mul (((W : ℂ) ^ d)⁻¹)).comp_ofReal
  have hfun : (fun s : ℝ => ((W : ℂ) ^ d)⁻¹ * (Θab + μ * gueShift d L μ t1 s)) =
      fun s : ℝ => ((W : ℂ) ^ d)⁻¹ * (Θab + μ * (((s : ℂ) - t1) * μ / ((L : ℂ) ^ d * p * (1 - (s : ℂ) * μ)))) := by
    funext s
    simp only [gueShift, hp]
  rw [hfun]
  refine hG.congr_deriv ?_
  set β := gueShift d L μ t1 t with hβ
  have hsum : (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
      (((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) a₁ a + μ * β)) * SBgue d L a b * (((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) b a₂ + μ * β))
      = ((W : ℂ) ^ d)⁻¹ * μ ^ 2 * ((L : ℂ) ^ d)⁻¹ * ((p⁻¹ + (L : ℂ) ^ d * β) * (p⁻¹ + (L : ℂ) ^ d * β)) := by
    simp only [SBgue_apply]
    have e : ∀ a b : Zd d L, ((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) a₁ a + μ * β) * ((L : ℂ) ^ d)⁻¹ *
        (((W : ℂ) ^ d)⁻¹ * ((Θ * Q₀) b a₂ + μ * β))
        = (((W : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹ * ((W : ℂ) ^ d)⁻¹) *
          (((Θ * Q₀) a₁ a + μ * β) * ((Θ * Q₀) b a₂ + μ * β)) := by
      intro a b; ring
    simp only [e, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [Finset.sum_add_distrib, hrow, hcol, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hsum, hβ, gueShift]
  have hid := kTwoGUE_deriv_identity d ((W : ℂ)) μ p (1 - (t : ℂ) * μ) ((t : ℂ) - t1) (L : ℂ)
    (by rw [hp]; ring) hp0 hq0 hL0
  rw [← mul_assoc] at hid
  exact hid.symm ▸ by ring

/-- **(7.33) at `n = 2`**: the closed form `kTwoGUEBA` solves the primitive equation of the GUE phase,
`d/dt K_{t,σ,(a₁,a₂)} = W^d ∑_{a,b} K_{t,σ,(a₁,a)} (S^{(B)}_{GUE})_{ab} K_{t,σ,(b,a₂)}`, for `0 ≤ t₁ ≤ t < 1` at real
data (twin of `hasDerivAt_kTwoGUE`, `KPrim.lean:150`: row and column sums of `Θ_{t₁} Q₀` are `μ (1 - t₁ μ)⁻¹`). -/
private theorem GUEKPrim_hasDerivAt_kTwo (d L W : ℕ) [NeZero L] [NeZero W] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m)
    {t1 t : ℝ} (ht1 : 0 ≤ t1) (ht1t : t1 ≤ t) (ht : t < 1) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => kTwoGUEBA d L W g E m t1 s σ₁ σ₂ a₁ a₂)
      ((W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        kTwoGUEBA d L W g E m t1 t σ₁ σ₂ a₁ a * SBgue d L a b * kTwoGUEBA d L W g E m t1 t σ₁ σ₂ b a₂) t := by
  obtain ⟨hQJ, hJQ⟩ := GUEKPrim_QJ (d := d) (L := L) (Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)
    (fun a b r => EKNonzero_Mss_shift (d := d) (L := L) g E m σ₁ σ₂ a b r)
  have ht10 : t1 < 1 := by linarith
  have hp0 : 1 - (t1 : ℂ) * (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) ≠ 0 := by
    have := GUEKPrim_tr_norm hr σ₁ σ₂ ht1 ht10
    intro h
    have h' : (t1 : ℂ) * (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) = 1 := by linear_combination -h
    rw [h', norm_one] at this
    exact lt_irrefl _ this
  have hq0 : (1 : ℂ) - (t : ℂ) * (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) ≠ 0 := by
    have := GUEKPrim_tr_norm hr σ₁ σ₂ (ht1.trans ht1t) ht
    intro h
    have h' : (t : ℂ) * (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) = 1 := by linear_combination -h
    rw [h', norm_one] at this
    exact lt_irrefl _ this
  have hU : IsUnit (1 - (t1 : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) :=
    BATheta_isUnit d L g κ E m hr t1 ht1 ht10 σ₁ σ₂
  obtain ⟨hΘJ, hJΘ⟩ := GUEKPrim_ThJ hQJ hJQ hU hp0
  have key := GUEKPrim_deriv_abs d L W (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)
    (BATheta d L g E m t1 σ₁ σ₂) (∑ c, BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ 0 c) hQJ hJQ hΘJ hJΘ hp0 hq0 a₁ a₂
  simp only [GUEKPrim_kTwo_eq]
  exact key

/-- (7.33) at `n = 2` in cut-and-glue form: `kTwoGUEBA`, as a function of the loop index, satisfies
`d/dt K_{t,I} = primRhsGUE (K_t) I` for every 2-loop `I`, `0 ≤ t₁ ≤ t < 1`, real data `BAReal d L g κ E m` (twin of
`hasDerivAt_kTwoGUELoop`, `KPrim.lean:209`; `T2515_KDerivBA` of the probe). -/
theorem hasDerivAt_kTwoGUELoopBA (d : ℕ) :
    ∀ (L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t1 t : ℝ, 0 ≤ t1 → t1 ≤ t →
      t < 1 → ∀ (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L),
        HasDerivAt (fun s => kTwoGUELoopBA d L W g E m t1 s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
          (primRhsGUE d L W (kTwoGUELoopBA d L W g E m t1 t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  intro L _ W _ g κ E m hr t1 t ht1 ht1t ht σ₁ σ₂ a₁ a₂
  rw [primRhsGUE_two]
  exact GUEKPrim_hasDerivAt_kTwo d L W hr ht1 ht1t ht σ₁ σ₂ a₁ a₂

end TwoLoop

/-! ## 7. The primitive loops of the GUE phase at BA: existence on `[t₁, t₀]` -/

section Loops

open private KPrim_ode_global KPrim_eq_two KPrim_primRhsGUE_congr KPrim_primRhsGUE_len_one
  KPrim_two_le_length_cutGlueL KPrim_two_le_length_cutGlueR KPrim_length_cutGlueL_le KPrim_length_cutGlueR_le from
  RBM3D.Universality.GUEPhase.KPrim

/-- Existence of the BA GUE-phase primitive loops up to length `n ≥ 2` by induction on `n` (twin of
`KPrim_exists_upto`, `KPrim.lean:523`, with the start `KLgen (mSigma E) t₁` replaced by a family `K0` and the
closed-form 2-loops `kTwoGUELoop` by a family `K2` of solutions of (7.33) at `n = 2`).  The induction step is the
merged one: for `n ≥ 2` the loops of length `n + 1` solve an ODE on the finite-dimensional space of functions on the
slice `{WF, length = n + 1}`, affine in the unknowns with coefficients from the shorter loops (Lipschitz). -/
private theorem GUEKPrim_exists_upto (d L W : ℕ) [NeZero L] [NeZero W] (K0 : LoopIdx (Zd d L) → ℂ)
    (K2 : ℝ → LoopIdx (Zd d L) → ℂ) {t1 t0 : ℝ} (ht10 : t1 ≤ t0)
    (h2start : ∀ (σ₁ σ₂ : Bool) (a b : Zd d L), K2 t1 ⟨[σ₁, σ₂], [a, b]⟩ = K0 ⟨[σ₁, σ₂], [a, b]⟩)
    (h2deriv : ∀ t ∈ Set.Icc t1 t0, ∀ (σ₁ σ₂ : Bool) (a b : Zd d L),
      HasDerivWithinAt (fun s => K2 s ⟨[σ₁, σ₂], [a, b]⟩) (primRhsGUE d L W (K2 t) ⟨[σ₁, σ₂], [a, b]⟩)
        (Set.Icc t1 t0) t)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
      (∀ J : LoopIdx (Zd d L), J.WF → 1 ≤ J.length → J.length ≤ n → K t1 J = K0 J) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ J : LoopIdx (Zd d L), J.WF → 1 ≤ J.length → J.length ≤ n →
        HasDerivWithinAt (fun s => K s J) (primRhsGUE d L W (K t) J) (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
        K t ⟨[σ₁, σ₂], [a, b]⟩ = K2 t ⟨[σ₁, σ₂], [a, b]⟩) := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- lengths `1` (constant) and `2` (the family `K2`)
    set K : ℝ → LoopIdx (Zd d L) → ℂ := fun t J => if J.length = 1 then K0 J else K2 t J with hKdef
    have hK2 : ∀ t (J : LoopIdx (Zd d L)), 2 ≤ J.length → K t J = K2 t J := by
      intro t J h
      exact ite_eq_right (by omega)
    refine ⟨K, fun J hJ h1 h2 => ?_, fun t ht J hJ h1 h2 => ?_, fun t ht σ₁ σ₂ a b => ?_⟩
    · rcases Nat.lt_or_ge J.length 2 with h | h
      · exact ite_eq_left (by omega)
      · obtain ⟨σ₁, σ₂, a, b, rfl⟩ := KPrim_eq_two hJ (by omega)
        rw [hK2 t1 _ h]
        exact h2start σ₁ σ₂ a b
    · rcases Nat.lt_or_ge J.length 2 with h | h
      · have hl : J.length = 1 := by omega
        have e : (fun s => K s J) = fun _ => K0 J := funext fun s => ite_eq_left hl
        rw [e, KPrim_primRhsGUE_len_one d L W _ hl]
        exact hasDerivWithinAt_const _ _ _
      · obtain ⟨σ₁, σ₂, a, b, rfl⟩ := KPrim_eq_two hJ (by omega)
        have e : (fun s => K s ⟨[σ₁, σ₂], [a, b]⟩) = fun s => K2 s ⟨[σ₁, σ₂], [a, b]⟩ :=
          funext fun s => hK2 s _ h
        rw [e, KPrim_primRhsGUE_congr d L W hJ (K' := K2 t) (fun J' _ hJ' _ => hK2 t J' hJ')]
        exact h2deriv t ht σ₁ σ₂ a b
    · rw [hK2 t _ (le_refl 2)]
  | succ n hn ih =>
    obtain ⟨Kp, hq1, hq2, hq3⟩ := ih
    -- the unknown slice: well-formed loops of length `n + 1`
    have hSfin : {J : LoopIdx (Zd d L) | J.WF ∧ J.length = n + 1}.Finite :=
      (finite_loopIdx d L (n + 1)).subset fun J hJ => by
        obtain ⟨h1, h2⟩ := hJ
        exact ⟨h1, by omega, h2.le⟩
    set S := hSfin.toFinset with hSdef
    have hmemS : ∀ J, J ∈ S ↔ J.WF ∧ J.length = n + 1 := fun J => hSfin.mem_toFinset
    -- the shorter lengths are continuous, hence bounded, on `[t₁, t₀]`
    have hcontK : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n →
        ContinuousOn (fun t => Kp t J) (Set.Icc t1 t0) := fun J hJ h2 hn' t ht =>
      (hq2 t ht J hJ (by omega) hn').continuousWithinAt
    have hTfin := finite_loopIdx d L n
    set T := hTfin.toFinset
    obtain ⟨M', hM'⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun t (J : T) => Kp t J.1) (s := Set.Icc t1 t0) (continuousOn_pi.2 fun J => by
        have hJ := hTfin.mem_toFinset.1 J.2
        exact hcontK J.1 hJ.1 hJ.2.1 hJ.2.2)
    set M := max M' 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hM : ∀ t ∈ Set.Icc t1 t0, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
        J.length ≤ n → ‖Kp t J‖ ≤ M := by
      intro t ht J hJ h2 hn'
      have hJT : J ∈ T := hTfin.mem_toFinset.2 ⟨hJ, h2, hn'⟩
      exact (norm_le_pi_norm (fun J : T => Kp t J.1) ⟨J, hJT⟩).trans
        ((hM' t ht).trans (le_max_left _ _))
    -- the vector field of the linear ODE for the length-`(n+1)` slice
    let gv : ℝ → (S → ℂ) → LoopIdx (Zd d L) → ℂ := fun t y J =>
      if h : J ∈ S then y ⟨J, h⟩ else Kp t J
    let f : ℝ → (S → ℂ) → (S → ℂ) := fun t y I => primRhsGUE d L W (gv t y) I.1
    have hgS : ∀ t y (J : LoopIdx (Zd d L)) (h : J ∈ S), gv t y J = y ⟨J, h⟩ :=
      fun t y J h => dite_eq_left h
    have hgN : ∀ t y (J : LoopIdx (Zd d L)), J ∉ S → gv t y J = Kp t J :=
      fun t y J h => dite_eq_right h
    have hnotS : ∀ J : LoopIdx (Zd d L), J.WF → J.length ≤ n + 1 → J ∉ S → J.length ≤ n := by
      intro J hJ hl hS
      by_contra hc
      exact hS ((hmemS J).2 ⟨hJ, by omega⟩)
    -- continuity in `t`
    have hcont : ∀ y, ContinuousOn (fun t => f t y) (Set.Icc t1 t0) := by
      intro y
      refine continuousOn_pi.2 fun I => ?_
      have hI := (hmemS I.1).1 I.2
      have hg : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n + 1 →
          ContinuousOn (fun t => gv t y J) (Set.Icc t1 t0) := by
        intro J hJ h2 hl
        by_cases hS : J ∈ S
        · simp only [hgS _ _ _ hS]
          exact continuousOn_const
        · simp only [hgN _ _ _ hS]
          exact hcontK J hJ h2 (hnotS J hJ hl hS)
      change ContinuousOn (fun t => (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.1.length,
        ∑ l ∈ Finset.Ioc k I.1.length, ∑ a : Zd d L, ∑ b : Zd d L,
          gv t y (I.1.cutGlueL k l a) * SBgue d L a b * gv t y (I.1.cutGlueR k l b))
        (Set.Icc t1 t0)
      refine continuousOn_const.mul (continuousOn_finsetSum _ fun k hk =>
        continuousOn_finsetSum _ fun l hl => continuousOn_finsetSum _ fun a _ =>
          continuousOn_finsetSum _ fun b _ => ?_)
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Ioc] at hl
      exact ((hg _ (LoopIdx.wf_cutGlueL I.1 a hI.1 hk.1 hl.1 hl.2)
        (KPrim_two_le_length_cutGlueL I.1 a hk.1 hl.1 hl.2)
        ((KPrim_length_cutGlueL_le I.1 a hk.1 hl.1 hl.2).trans hI.2.le)).mul
          continuousOn_const).mul
        (hg _ (LoopIdx.wf_cutGlueR I.1 b hI.1 hk.1 hl.1 hl.2)
        (KPrim_two_le_length_cutGlueR I.1 b hk.1 hl.1 hl.2)
        ((KPrim_length_cutGlueR_le I.1 b hk.1 hl.1 hl.2).trans hI.2.le))
    -- the uniform Lipschitz bound: at most one cut factor has length `n + 1`
    set c0 : ℝ := ((L : ℝ) ^ d)⁻¹ * M with hc0
    have hc00 : 0 ≤ c0 := by positivity
    set C : ℝ := (W : ℝ) ^ d * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
      ∑ a : Zd d L, ∑ b : Zd d L, c0 with hCdef
    have hC0 : 0 ≤ C := by positivity
    set CN : NNReal := ⟨C, hC0⟩ with hCNdef
    have hCN : (CN : ℝ) = C := rfl
    have hlip : ∀ t ∈ Set.Icc t1 t0, LipschitzWith CN (f t) := by
      intro t ht
      refine LipschitzWith.of_dist_le_mul fun y y' => ?_
      rw [dist_eq_norm, dist_eq_norm, hCN]
      set δ := ‖y - y'‖ with hδ
      have hδ0 : 0 ≤ δ := norm_nonneg _
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun I => ?_
      have hI := (hmemS I.1).1 I.2
      have hterm : ∀ k ∈ Finset.Icc 1 (n + 1), ∀ l ∈ Finset.Ioc k (n + 1), ∀ a b : Zd d L,
          ‖gv t y (I.1.cutGlueL k l a) * SBgue d L a b * gv t y (I.1.cutGlueR k l b) -
            gv t y' (I.1.cutGlueL k l a) * SBgue d L a b * gv t y' (I.1.cutGlueR k l b)‖
            ≤ c0 * δ := by
        intro k hk l hl a b
        rw [Finset.mem_Icc] at hk
        rw [Finset.mem_Ioc] at hl
        have hl2 : l ≤ I.1.length := hI.2 ▸ hl.2
        have hsum := LoopIdx.length_cutGlueL_add_length_cutGlueR I.1 a hk.1 hl.1 hl2
        have hLR : (I.1.cutGlueR k l b).length = (I.1.cutGlueR k l a).length := by
          rw [LoopIdx.length_cutGlueR I.1 b hk.1 hl.1 hl2,
            LoopIdx.length_cutGlueR I.1 a hk.1 hl.1 hl2]
        have hWL := LoopIdx.wf_cutGlueL I.1 a hI.1 hk.1 hl.1 hl2
        have hWR := LoopIdx.wf_cutGlueR I.1 b hI.1 hk.1 hl.1 hl2
        have h2L := KPrim_two_le_length_cutGlueL I.1 a hk.1 hl.1 hl2
        have h2R := KPrim_two_le_length_cutGlueR I.1 b hk.1 hl.1 hl2
        have hleL := (KPrim_length_cutGlueL_le I.1 a hk.1 hl.1 hl2).trans hI.2.le
        have hleR := (KPrim_length_cutGlueR_le I.1 b hk.1 hl.1 hl2).trans hI.2.le
        have hSB : ‖SBgue d L a b‖ = ((L : ℝ) ^ d)⁻¹ := by
          rw [SBgue_apply, norm_inv, norm_pow, Complex.norm_natCast]
        have hcoord : ∀ (J : LoopIdx (Zd d L)) (h : J ∈ S), ‖y ⟨J, h⟩ - y' ⟨J, h⟩‖ ≤ δ :=
          fun J h => norm_le_pi_norm (y - y') ⟨J, h⟩
        have hL0 : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
        by_cases hSL : I.1.cutGlueL k l a ∈ S <;> by_cases hSR : I.1.cutGlueR k l b ∈ S
        · exfalso
          have h1 := ((hmemS _).1 hSL).2
          have h2 := ((hmemS _).1 hSR).2
          omega
        · rw [hgS _ _ _ hSL, hgS _ _ _ hSL, hgN _ _ _ hSR, hgN _ _ _ hSR,
            show ∀ u v s w : ℂ, u * s * w - v * s * w = (u - v) * s * w from
              fun u v s w => by ring, norm_mul, norm_mul, hSB]
          have hKb := hM t ht _ hWR h2R (hnotS _ hWR hleR hSR)
          calc ‖y ⟨_, hSL⟩ - y' ⟨_, hSL⟩‖ * ((L : ℝ) ^ d)⁻¹ * ‖Kp t (I.1.cutGlueR k l b)‖
              ≤ δ * ((L : ℝ) ^ d)⁻¹ * M := by gcongr; exact hcoord _ hSL
            _ = c0 * δ := by rw [hc0]; ring
        · rw [hgN _ _ _ hSL, hgN _ _ _ hSL, hgS _ _ _ hSR, hgS _ _ _ hSR,
            show ∀ u v s w : ℂ, w * s * u - w * s * v = w * s * (u - v) from
              fun u v s w => by ring, norm_mul, norm_mul, hSB]
          have hKb := hM t ht _ hWL h2L (hnotS _ hWL hleL hSL)
          calc ‖Kp t (I.1.cutGlueL k l a)‖ * ((L : ℝ) ^ d)⁻¹ * ‖y ⟨_, hSR⟩ - y' ⟨_, hSR⟩‖
              ≤ M * ((L : ℝ) ^ d)⁻¹ * δ := by gcongr; exact hcoord _ hSR
            _ = c0 * δ := by rw [hc0]; ring
        · rw [hgN _ _ _ hSL, hgN _ _ _ hSL, hgN _ _ _ hSR, hgN _ _ _ hSR, sub_self, norm_zero]
          positivity
      have hIlen : I.1.length = n + 1 := hI.2
      calc ‖(f t y - f t y') I‖
          = ‖(W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : Zd d L, ∑ b : Zd d L,
              (gv t y (I.1.cutGlueL k l a) * SBgue d L a b * gv t y (I.1.cutGlueR k l b) -
                gv t y' (I.1.cutGlueL k l a) * SBgue d L a b *
                  gv t y' (I.1.cutGlueR k l b))‖ := by
            simp only [Pi.sub_apply, f, primRhsGUE, primBilGUE, hIlen,
              ← mul_sub, ← Finset.sum_sub_distrib]
        _ = (W : ℝ) ^ d * ‖∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : Zd d L, ∑ b : Zd d L,
              (gv t y (I.1.cutGlueL k l a) * SBgue d L a b * gv t y (I.1.cutGlueR k l b) -
                gv t y' (I.1.cutGlueL k l a) * SBgue d L a b *
                  gv t y' (I.1.cutGlueR k l b))‖ := by
            rw [norm_mul, norm_pow, Complex.norm_natCast]
        _ ≤ (W : ℝ) ^ d * ∑ k ∈ Finset.Icc 1 (n + 1), ∑ l ∈ Finset.Ioc k (n + 1),
              ∑ a : Zd d L, ∑ b : Zd d L, c0 * δ := by
            gcongr
            exact norm_sum_le_of_le _ fun k hk => norm_sum_le_of_le _ fun l hl =>
              norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ => hterm k hk l hl a b
        _ = C * δ := by
            simp only [hCdef, mul_assoc, Finset.sum_mul]
    -- global existence for the length-`(n+1)` slice
    obtain ⟨α, hα0, hα⟩ := KPrim_ode_global f ht10 CN hlip hcont
      (fun I : S => K0 I.1)
    refine ⟨fun t J => gv t (α t) J, fun J hJ h1 hl => ?_, fun t ht J hJ h1 hl => ?_,
      fun t ht σ₁ σ₂ a b => ?_⟩
    · by_cases hS : J ∈ S
      · simp only [hgS _ _ _ hS, hα0]
      · simp only [hgN _ _ _ hS]
        exact hq1 J hJ h1 (hnotS J hJ hl hS)
    · by_cases hS : J ∈ S
      · have e : (fun s => gv s (α s) J) = fun s => α s ⟨J, hS⟩ := funext fun s => hgS _ _ _ hS
        rw [e]
        exact hasDerivWithinAt_pi.1 (hα t ht) ⟨J, hS⟩
      · have hJn := hnotS J hJ hl hS
        have e : (fun s => gv s (α s) J) = fun s => Kp s J := funext fun s => hgN _ _ _ hS
        rw [e, KPrim_primRhsGUE_congr d L W hJ (K' := Kp t) fun J' hJ' _ hl' =>
          hgN _ _ _ fun hS' => by have := ((hmemS J').1 hS').2; omega]
        exact hq2 t ht J hJ h1 hJn
    · have hS : (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Zd d L)) ∉ S := fun hS' => by
        have := ((hmemS _).1 hS').2
        simp only [LoopIdx.length, List.length_cons, List.length_nil] at this
        omega
      simp only [hgN _ _ _ hS]
      exact hq3 t ht σ₁ σ₂ a b

/-- **(7.33)**: the BA GUE-phase primitive loops exist on `[t₁, t₀]` for every length `≤ n₀`, start from the BA `𝒦`-loops
`BAKsol` (the family of `baKsolve`, `(Kn2sol)`: `W^{-d} Θ_{t₁} M^{(σσ')}` at the 2-loops) at `t₁`, and their `2`-loops are
`kTwoGUEBA` (twin of `gueK_exists`, `KPrim.lean:749`).  `t₁ ≤ t₀ < 1`, real data `BAReal d L g κ E m`, `0 < g`, `0 < κ`. -/
theorem gueK_existsBA (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (hL : 3 ≤ L) {g κ E : ℝ} {m : ℂ} (hg : 0 < g)
    (hκ : 0 < κ) (hr : BAReal d L g κ E m) {t1 t0 : ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n0 : ℕ) :
    ∃ Kt : ℝ → LoopIdx (Zd d L) → ℂ,
      (∀ I, Kt t1 I = BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t1 I) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length → I.length ≤ n0 →
        HasDerivWithinAt (fun s => Kt s I) (primRhsGUE d L W (Kt t) I) (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
        Kt t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEBA d L W g E m t1 t σ₁ σ₂ a b) := by
  classical
  have h2start : ∀ (σ₁ σ₂ : Bool) (a b : Zd d L), kTwoGUELoopBA d L W g E m t1 t1 ⟨[σ₁, σ₂], [a, b]⟩ =
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t1 ⟨[σ₁, σ₂], [a, b]⟩ := by
    intro σ₁ σ₂ a b
    have h := baKsol_two d hκ hg hL W hr (t := t1) ⟨ht1, by linarith⟩ ![σ₁, σ₂] ![a, b]
    have hloop : KLloopOf d L ![σ₁, σ₂] ![a, b] = ⟨[σ₁, σ₂], [a, b]⟩ := by simp [KLloopOf, List.ofFn_succ]
    rw [hloop] at h
    rw [h]
    simp only [kTwoGUELoopBA]
    exact kTwoGUEBA_self d L W g E m t1 σ₁ σ₂ a b
  have h2deriv : ∀ t ∈ Set.Icc t1 t0, ∀ (σ₁ σ₂ : Bool) (a b : Zd d L),
      HasDerivWithinAt (fun s => kTwoGUELoopBA d L W g E m t1 s ⟨[σ₁, σ₂], [a, b]⟩)
        (primRhsGUE d L W (kTwoGUELoopBA d L W g E m t1 t) ⟨[σ₁, σ₂], [a, b]⟩) (Set.Icc t1 t0) t :=
    fun t ht σ₁ σ₂ a b =>
      (hasDerivAt_kTwoGUELoopBA d L W g κ E m hr t1 t ht1 ht.1 (lt_of_le_of_lt ht.2 ht0) σ₁ σ₂ a b).hasDerivWithinAt
  obtain ⟨K, hK1, hK2, hK3⟩ := GUEKPrim_exists_upto d L W
    (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t1) (kTwoGUELoopBA d L W g E m t1) ht10
    h2start h2deriv (max n0 2) (le_max_right _ _)
  set N := max n0 2 with hN
  refine ⟨fun t I => if I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N then K t I
    else BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t1 I, fun I => ?_,
    fun t ht I hI h1 hl => ?_, fun t ht σ₁ σ₂ a b => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hK1 I h.1 h.2.1 h.2.2
    · rfl
  · have hIN : I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N := ⟨hI, h1, hl.trans (le_max_left _ _)⟩
    have e : (fun s => (fun t I => if I.WF ∧ 1 ≤ I.length ∧ I.length ≤ N then K t I
        else BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t1 I) s I) = fun s => K s I :=
      funext fun s => ite_eq_left hIN
    rw [e, KPrim_primRhsGUE_congr d L W hI (K' := K t) fun J hJ h2 hJl =>
      ite_eq_left ⟨hJ, by omega, hJl.trans hIN.2.2⟩]
    exact hK2 t ht I hI h1 hIN.2.2
  · have h2 : (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Zd d L)).WF ∧
        1 ≤ (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Zd d L)).length ∧
        (⟨[σ₁, σ₂], [a, b]⟩ : LoopIdx (Zd d L)).length ≤ N :=
      ⟨rfl, by simp [LoopIdx.length], by simp [LoopIdx.length, hN]⟩
    dsimp only
    rw [ite_eq_left h2]
    exact hK3 t ht σ₁ σ₂ a b

end Loops

/-! ## 8. The bridges to the OU profile (target 7) -/

/-- **Bridge to the BA OU profile**: `t₀ K^{(σ₁σ₂)}` of the GUE phase at the flow point `(√t₀ λ, E, m/√t₀)` of `z` and
`t₁ = (1 - ζ) t₀` is the profile `W^{-d} (Θ̃_ζ M^{(+,σ)})_{ab}` of the text of D1 (iii): `pm` for `σ = -`, `pp` for
`σ = +` (twin of `lemT_mul_kTwoGUE_pm_eq_profPMTilde`, `KPrim.lean:275`; `T2515_KBridgeBA` at `0 ≤ ζ ≤ 1`). -/
theorem kTwoGUEBA_bridge (d : ℕ) :
    ∀ P : UNOUProfile (UNKind.ba d),
      (∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)),
        (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true false;
          P.pm sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d) ∧
        (let Q := BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true true;
          P.pp sz n ζ z a b = (Ring.inverse (1 - Q * SBtilde d (sz.L n) 0 ζ) * Q) a b / ((sz.W n : ℕ) : ℂ) ^ d)) →
      ∀ (sz : Sizes d) (n : ℕ) (ζ : ℝ), (0 ≤ ζ ∧ ζ ≤ 1) →
        ∀ (z : ℂ), 0 < z.im → ∀ a b : Zd d (sz.L n),
          let m := BAm d (sz.L n) (sz.lam n) z; let t0 := BAt0 z m;
          (t0 : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt t0 * sz.lam n) (BAflowE z m) (m / (Real.sqrt t0 : ℂ))
              ((1 - ζ) * t0) t0 true false a b = P.pm sz n ζ z a b ∧
          (t0 : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt t0 * sz.lam n) (BAflowE z m) (m / (Real.sqrt t0 : ℂ))
              ((1 - ζ) * t0) t0 true true a b = P.pp sz n ζ z a b := by
  intro P hP sz n ζ hζ z hz a b m t0
  obtain ⟨ht0, ht1, hreal⟩ := GUEKPrim_flow (d := d) (L := sz.L n) (sz.lam n) hz
  have key : ∀ σ : Bool, (t0 : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt t0 * sz.lam n) (BAflowE z m)
      (m / (Real.sqrt t0 : ℂ)) ((1 - ζ) * t0) t0 true σ a b =
      (Ring.inverse (1 - GUEKPrim_Q d (sz.L n) (sz.lam n) z σ * SBtilde d (sz.L n) 0 ζ) *
        GUEKPrim_Q d (sz.L n) (sz.lam n) z σ) a b / ((sz.W n : ℕ) : ℂ) ^ d := by
    intro σ
    rw [kTwoGUEBA_eq_ThetaTilde d (sz.L n) (sz.W n) hreal ht0.le ht1 hζ.1 hζ.2 true σ a b]
    have hQ : GUEKPrim_Q d (sz.L n) (sz.lam n) z σ = (t0 : ℂ) • BAMss d (sz.L n) (BAMB d (sz.L n)
        (Real.sqrt t0 * sz.lam n) (BAflowE z m : ℂ) (m / (Real.sqrt t0 : ℂ))) true σ :=
      GUEKPrim_Mss_flow (d := d) (L := sz.L n) (sz.lam n) hz true σ
    rw [hQ, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  exact ⟨(key false).trans (hP sz n ζ z a b).1.symm, (key true).trans (hP sz n ζ z a b).2.symm⟩

/-- `t₀ K^{(+,-)}` at the flow point is `(UNOUProfile.ba d).pm` (`0 ≤ ζ ≤ 1`, `Im z > 0`). -/
theorem kTwoGUEBA_bridge_pm {d : ℕ} (sz : Sizes d) (n : ℕ) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) {z : ℂ}
    (hz : 0 < z.im) (a b : Zd d (sz.L n)) :
    (BAt0 z (BAm d (sz.L n) (sz.lam n) z) : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n)
        (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) * sz.lam n) (BAflowE z (BAm d (sz.L n) (sz.lam n) z))
        (BAm d (sz.L n) (sz.lam n) z / (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) : ℂ))
        ((1 - ζ) * BAt0 z (BAm d (sz.L n) (sz.lam n) z)) (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) true false a b =
      (UNOUProfile.ba d).pm sz n ζ z a b :=
  (kTwoGUEBA_bridge d (UNOUProfile.ba d) (UNOUProfile.ba_spec d) sz n ζ ⟨hζ0, hζ1⟩ z hz a b).1

/-- `t₀ K^{(+,+)}` at the flow point is `(UNOUProfile.ba d).pp` (`0 ≤ ζ ≤ 1`, `Im z > 0`). -/
theorem kTwoGUEBA_bridge_pp {d : ℕ} (sz : Sizes d) (n : ℕ) {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) {z : ℂ}
    (hz : 0 < z.im) (a b : Zd d (sz.L n)) :
    (BAt0 z (BAm d (sz.L n) (sz.lam n) z) : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n)
        (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) * sz.lam n) (BAflowE z (BAm d (sz.L n) (sz.lam n) z))
        (BAm d (sz.L n) (sz.lam n) z / (Real.sqrt (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) : ℂ))
        ((1 - ζ) * BAt0 z (BAm d (sz.L n) (sz.lam n) z)) (BAt0 z (BAm d (sz.L n) (sz.lam n) z)) true true a b =
      (UNOUProfile.ba d).pp sz n ζ z a b :=
  (kTwoGUEBA_bridge d (UNOUProfile.ba d) (UNOUProfile.ba_spec d) sz n ζ ⟨hζ0, hζ1⟩ z hz a b).2

/-! ## 9. Compiled nonempty instances (target 8)

`d = 3`.  Profile-level data: `S0 = clsS 4 (g = 3/10)` (`BA/UNPins.lean:884`: `L = 4`, `W₀ = 32`, `λ = (fp 4 _).g0 ∈ (0, 3/10]`),
`n = 0`, `κ_* = Im m₀/π` (`clsκ`), `E_*` in the bulk (`cls_bulk`), `z = E_* + i/2` (`0 < Im z ≤ 1`), `𝔡 = 1/10`,
`ζ ∈ {0, 1/2, 1}`.  Flow-point data: the merged `MFixedPointInst.P` (`(L, g) = (4, 10)`, `P.real : BAReal 3 4 P.g0 (Im m₀)
P.E P.m₀`) and `fp 4 _` (`S0`).  Every deterministic hypothesis is discharged; `UNG1Rowk` and `UNG2bRowk` (N2's, C5's inputs)
stay hypotheses of the `ouRowk_of_pins` example only. -/

namespace GUEKPrimInst

open RBM.Univ.BAInst RBM.BA.UNPinsInst RBM.BA.MFixedPointInst

private theorem hg : (0 : ℝ) < 3 / 10 := by norm_num

/-- The point `z = E_* + i/2` of the class `S0`. -/
def zS0 : ℂ := ⟨(fp 4 hg).E, 1 / 2⟩

private theorem S0_win : 0 < S0.lam 0 ∧ S0.lam 0 ≤ (1 / 10 : ℝ)⁻¹ :=
  ⟨(fp 4 hg).g0_pos, by
    change (fp 4 hg).g0 ≤ (1 / 10 : ℝ)⁻¹
    have := (fp 4 hg).g0_le
    norm_num
    linarith⟩

private theorem fp_im_pos : 0 < ((fp 4 hg).m0).im := (fp 4 hg).real.1.1

/-- Target 1 at `S0`, `n = 0`, `ζ = 1/2`, `z = E_* + i/2`, `a = b = 0`. -/
example := UNOUProfile.ba_spec 3 S0 0 (1 / 2) zS0 0 0

/-- Target 2 (transfer) at `S0` and at the merged point `(L, g) = (4, 10)`, `s = 1/2`, charges `(+,-)`. -/
example := baThetaTransfer 3 4 (S0.lam 0) zS0 (by norm_num [zS0]) (1 / 2) true false

example := baThetaTransfer 3 4 10 (zS 4 10) (zS_im_pos 4 10) (1 / 2) true false

/-- Target 2 (comparison) at `κ_*`, `E_*`. -/
example := (baT0Cmp (clsκ 4 hg) (clsκ_pos 4 hg)).imp fun cT h =>
  And.intro h.1 (h.2 3 4 (S0.lam 0) zS0 (cls_bulk 4 (by norm_num) hg) (by norm_num [zS0]) (by norm_num [zS0]))

/-- Target 3 (zero-mode identity) at the merged flow point `P`, `t₀ = 1/2`, `ζ ∈ {0, 1/2, 1}`, charges `(+,-)`, `(+,+)`. -/
example := baThetaTilde_eq (MFixedPointInst.P).real (t0 := 1 / 2) (by norm_num) (by norm_num) (ζ := 0) le_rfl
  zero_le_one true false

example := baThetaTilde_eq (MFixedPointInst.P).real (t0 := 1 / 2) (by norm_num) (by norm_num) (ζ := 1 / 2)
  (by norm_num) (by norm_num) true true

example := baThetaTilde_eq (MFixedPointInst.P).real (t0 := 1 / 2) (by norm_num) (by norm_num) (ζ := 1) zero_le_one
  le_rfl true false

/-- Target 3 (oscillation, lossless) at `S0`, `n = 0`, `z = E_* + i/2`, `𝔡 = 1/10`, `ζ ∈ {0, 1/2, 1}`. -/
example := (baThetaTilde_osc 3 le_rfl (1 / 10) (clsκ 4 hg) (by norm_num) (clsκ_pos 4 hg)).imp fun C h =>
  And.intro h.1 fun σ u v =>
    And.intro (h.2 4 (by norm_num) (S0.lam 0) S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) 0 le_rfl zero_le_one σ u v)
    (And.intro (h.2 4 (by norm_num) (S0.lam 0) S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) (1 / 2) (by norm_num) (by norm_num) σ u v)
     (h.2 4 (by norm_num) (S0.lam 0) S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) 1 zero_le_one le_rfl σ u v))

/-- Target 6 (`baThetaDiff`) at `S0`, `n = 0`, `z = E_* + i/2`. -/
example := (baThetaDiff 3 le_rfl (1 / 10) (clsκ 4 hg) (by norm_num) (clsκ_pos 4 hg)).imp fun C h =>
  And.intro h.1 fun σ a b b' => h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
    (cls_bulk 4 (by norm_num) hg) σ a b b'

/-- Target 4 (`baOUProfRowk_holds`) at `S0`, `n = 0`, `z = E_* + i/2`, `ζ ∈ {0, 1/2, 1}`. -/
example := (baOUProfRowk_holds 3 le_rfl (1 / 10) (clsκ 4 hg) (by norm_num) (clsκ_pos 4 hg)).imp fun C h =>
  And.intro h.1 fun a b b' =>
    And.intro (h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) 0 le_rfl zero_le_one a b b')
    (And.intro (h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) (1 / 2) (by norm_num) (by norm_num) a b b')
     (h.2 S0 0 S0_win.1 S0_win.2 zS0 (by norm_num [zS0]) (by norm_num [zS0])
      (cls_bulk 4 (by norm_num) hg) 1 zero_le_one le_rfl a b b'))

/-- Target 4 as the premise `hprof` of `ouRowk_of_pins` (N2): the BA kind with the BA profile; `UNG1Rowk` and `UNG2bRowk`
are the other gates' pins. -/
example {ML Loc Que : Prop} (h1 : UNG1Rowk (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) ML Loc Que)
    (h2 : UNG2bRowk (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d)) :
    UNOURowk (fun d => UNKind.ba d) ML Loc Que :=
  ouRowk_of_pins (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (fun d hd => baOUProfRowk_holds d hd) h1 h2

/-- Target 5 (`baProfComp`) through `RandomLayerBGBA_comp`, and at `S0` with `φ = (2 * ·)`. -/
example : RBG_Comp (UNKind.ba 3) (UNOUProfile.ba 3) := RandomLayerBGBA_comp 3 (baProfComp 3)

example (j : ℕ) := RandomLayerBGBA_comp 3 (baProfComp 3) S0 (2 * ·) (fun a b h => by change 2 * a < 2 * b; omega) j

example := baProfComp 3 S0 (2 * ·) 1 (1 / 2) zS0 (0 : Zd 3 4) 0

/-- Target 6 (`UNOUProfile.ba_zero`, the `ζ = 0` bridge) at `S0`, `n = 0`, `z = E_* + i/2`, charge `(+,-)`. -/
example := UNOUProfile.ba_zero 3 (UNOUProfile.ba 3) (UNOUProfile.ba_spec 3) S0 0 zS0 false 0 0

/-- Target 7 at the merged flow point `P`: `kTwoGUEBA_self`, `kTwoGUEBA_eq_ThetaTilde` (`t₀ = 1/2`, `ζ = 1/2`). -/
example := kTwoGUEBA_self 3 4 2 (MFixedPointInst.P).g0 (MFixedPointInst.P).E (MFixedPointInst.P).m0 (1 / 2) true false 0 0

example := kTwoGUEBA_eq_ThetaTilde 3 4 2 (MFixedPointInst.P).real (t0 := 1 / 2) (ζ := 1 / 2) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) true false 0 0

/-- Target 7, (7.33) at `n = 2` in cut-and-glue form on `[1/4, 1/2]` at `P`, `W = 2`, both charge pairs. -/
example := hasDerivAt_kTwoGUELoopBA 3 4 2 (MFixedPointInst.P).g0 ((MFixedPointInst.P).m0).im (MFixedPointInst.P).E
  (MFixedPointInst.P).m0 (MFixedPointInst.P).real (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) true false 0 1

example := hasDerivAt_kTwoGUELoopBA 3 4 2 (MFixedPointInst.P).g0 ((MFixedPointInst.P).m0).im (MFixedPointInst.P).E
  (MFixedPointInst.P).m0 (MFixedPointInst.P).real (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) true true 0 1

/-- Target 7, the bridges to `pm`/`pp` at `S0`, `n = 0`, `z = E_* + i/2`, `ζ = 1/2`. -/
example := kTwoGUEBA_bridge_pm S0 0 (ζ := 1 / 2) (by norm_num) (by norm_num) (z := zS0) (by norm_num [zS0]) 0 0

example := kTwoGUEBA_bridge_pp S0 0 (ζ := 1 / 2) (by norm_num) (by norm_num) (z := zS0) (by norm_num [zS0]) 0 0

example := kTwoGUEBA_bridge 3 (UNOUProfile.ba 3) (UNOUProfile.ba_spec 3) S0 0 0 ⟨le_rfl, zero_le_one⟩ zS0
  (by norm_num [zS0]) 0 0

/-- Target 7, `gueK_existsBA` at the data of `S0`, `n = 0` (`L = 4`, `W = 32`, `g = λ`, `(κ, E, m) = (Im m₀, E_*, m₀)` of the
flow point `fp 4 _`), start `t₁ = 1/4`, end `t₀ = 1/2`, all lengths `≤ 4`. -/
example := gueK_existsBA 3 4 32 (by norm_num) (g := (fp 4 hg).g0) (κ := ((fp 4 hg).m0).im) (E := (fp 4 hg).E)
  (m := (fp 4 hg).m0) (fp 4 hg).g0_pos fp_im_pos (fp 4 hg).real (t1 := 1 / 4) (t0 := 1 / 2) (by norm_num)
  (by norm_num) (by norm_num) 4

end GUEKPrimInst

end RBM.BA

end
