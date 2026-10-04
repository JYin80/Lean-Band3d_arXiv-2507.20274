/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.KDecay
import RBM3D.Induction.NewKLK
import RBM3D.Induction.GridDuhamelN

/-!
# S5-02 (ST-4): the Step 5 kit

`Prec` comparisons, the assembly, case (i) from its pins, case (iv) proved.

Moved from the T2134 design probe (`7b2b789`, `RBM3D/Probe/T2134Pins.lean`, never merged),
lines `477-1039` (section 7 up to the heading `### Case (iii)`, which is S5-03) without
`st5_reg5I_mid` (public in `Induction/Step5Pins.lean`), and the instances of probe `1819-1855`
and `inst_skeletonI` (`2255-2261`); the instance namespace `RBM.Gauss.T2134Inst` is
`RBM.Gauss.Step5Inst`.
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (Step 5 is `3_5:1935-2383`).
Registry (DECISIONS §16, §20, §40): `STStep5IV` is proved here (`stStep5IV_holds`);
`STStep5I` stays owed.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 7. The skeletons: Step 5 from its ingredients (compiled)

The `Prec` calculus used below is the merged `StochDomAt` (`Defs/StochDomAt.lean` §9); every deterministic comparison is a
theorem of this section (`st5_*`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `ξ ≺ ζ₁`, `ζ₁ ≤ c ζ₂` eventually, `ζ₂ ≥ 0` imply `ξ ≺ ζ₂` (the factor `c` is absorbed by `N^{τ/2}`). -/
theorem st5_prec_mono (hsz : sz.SizeTendsto) {U : ℕ → Type*} {ξ ζ₁ ζ₂ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ℝ}
    (h : sz.Prec ξ ζ₁) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ₁ n u ω ≤ c * ζ₂ n u ω)
    (hζ₂ : ∀ n u ω, 0 ≤ ζ₂ n u ω) : sz.Prec ξ ζ₂ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, (tendsto_size sz hsz).eventually (eventually_le_rpow c (half_pos hτ))] with n hn hc
  intro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (c * ζ₂ n u ω) := mul_le_mul_of_nonneg_left (hn u ω) hpos
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂ n u ω) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (hζ₂ n u ω)) hpos
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]
  exact lt_of_le_of_lt h1 hu

/-- Two sign classes (or any two index sets) that cover the index set: `≺` on both gives `≺` on the whole. -/
theorem st5_prec_cover (hsz : sz.SizeTendsto) {U V₁ V₂ : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (φ₁ : ∀ n, V₁ n → U n) (φ₂ : ∀ n, V₂ n → U n)
    (hcov : ∀ n u, (∃ v, φ₁ n v = u) ∨ (∃ v, φ₂ n v = u))
    (h₁ : sz.Prec (fun n v ω => ξ n (φ₁ n v) ω) (fun n v ω => ζ n (φ₁ n v) ω))
    (h₂ : sz.Prec (fun n v ω => ξ n (φ₂ n v) ω) (fun n v ω => ζ n (φ₂ n v) ω)) : sz.Prec ξ ζ := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) h₁ h₂ fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun n => ?_⟩
  intro ω ⟨u, hu⟩
  rcases hcov n u with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact Or.inl ⟨v, hu⟩
  · exact Or.inr ⟨v, hu⟩

/-! ### The assembly `STDecay ∧ STDecayStrong` at `t` -/

/-- **Assembly**: the uniform conclusions of Step 5 give `(Eq:Gdecay)` and `(Eq:Gdecay+s<g)` at the time sequence `t`
(`1_2:1385`: "Hence the pointwise decay estimate `(Eq:Gdecay)` holds at time `t`"; the endpoint `u = t` of the index). -/
theorem ST_step5_assembly {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STStep5Concl sz E s t) :
    STDecay sz E t ∧ STDecayStrong sz E t := by
  obtain ⟨hW, hS⟩ := h
  refine ⟨fun D hD => ?_, fun D hD => ?_⟩
  · have := StochDomAt.precomp_param (hW D hD)
      (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) =>
        ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))
    simp only [Real.rpow_zero, one_mul] at this
    exact this
  · exact StochDomAt.precomp_param (hS D hD)
      (fun n (p : {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n}) =>
        (⟨((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p.1), p.2⟩ :
          {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n}))


/-! ### Deterministic comparisons -/

theorem st5_zeroModeSet_empty {n L : ℕ} [NeZero L] (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L (∅ : Finset (Fin n)) T = T := by
  simp [zeroModeSet]

/-- `STConStInd` is monotone in `𝔠_d`: a smaller exponent is the stronger hypothesis (it gives `W^{-d}B_{t,0} < 1`). -/
theorem st5_conStInd_mono {c c' : ℝ} {s t : ℕ → ℝ} (h : STConStInd sz c s t) (ht1 : ∀ n, t n < 1) (hc : 0 < c)
    (hcc : c ≤ c') : STConStInd sz c' s t := by
  filter_upwards [h] with n hn
  obtain ⟨h1, h2⟩ := hn
  refine ⟨le_trans ?_ h1, h2⟩
  have hB0 : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
  have hr : 0 < (1 - t n) / (1 - s n) := by
    by_contra hneg
    have : (sz.Bctl n (t n)) ^ c > 0 := Real.rpow_pos_of_pos hB0 c
    linarith [not_lt.1 hneg]
  have hB1 : sz.Bctl n (t n) < 1 := by
    by_contra hge
    have h1' : 1 ≤ sz.Bctl n (t n) := not_lt.1 hge
    have : 1 ≤ (sz.Bctl n (t n)) ^ c := Real.one_le_rpow h1' hc.le
    linarith
  exact Real.rpow_le_rpow_of_exponent_ge hB0 hB1.le hcc

/-- `W^{-d} B_{u,0} ≥ (2 ilambda² W^d)⁻¹` for `1 - u ≤ ilambda²`, `ilambda > 0`, `u < 1`: the first term of `B_{u,0}`
is `(ilambda² + 1 - u)⁻¹ ≥ (2 ilambda²)⁻¹`. -/
theorem st5_Bctl_ge (n : ℕ) {u : ℝ} (hlam : 0 < sz.lam n) (hu : u < 1) (hx : 1 - u ≤ sz.lam n ^ 2) :
    (2 * STAI sz n)⁻¹ ≤ sz.Bctl n u := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hx0 : 0 < 1 - u := by linarith
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
  unfold Sizes.Bctl Bparam STAI
  rw [abs_of_pos hx0]
  have h1 : (2 * sz.lam n ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have h2 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by positivity
  have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [h0, inv_one, mul_one]
  calc (2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d))⁻¹
      = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * sz.lam n ^ 2)⁻¹ := by
        rw [show 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) = (2 * sz.lam n ^ 2) * ((sz.W n : ℕ) : ℝ) ^ d by ring,
          mul_inv, mul_comm]
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- `zdistInf ≤ L`. -/
theorem st5_zdistInf_le (n : ℕ) (x : Zd d (sz.L n)) : zdistInf d (sz.L n) x ≤ sz.L n :=
  Finset.sup_le fun i _ => zdist_le_L (x i)

/-- `W^{-d} 𝒯̃^L_{u,D}(r) ≤ W^{-d} B_{u,r} e^{-(r/ℓ_u)^{1/2}} + W^{-d-D}` at `r = |a₁ - a₂| ≤ L`: the profile `STprof` at `ℓ = L`
splits into the profile `B_{u,r} e^{-(r/ℓ_u)^{1/2}}` of `(Eq:Gdecay_flow)` and the floor. -/
theorem st5_STprof_le (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) :
    STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) ≤
      STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hr : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast st5_zdistInf_le sz n (a 0 - a 1)
  have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmin : min ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ((sz.L n : ℕ) : ℝ) =
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := min_eq_left hr
  have hWd : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  unfold STprof tailW
  rw [hmin]
  have hT : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) =
      Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    unfold tailT
    rw [BparamR_natCast, ← Real.sqrt_eq_rpow]
  rw [hT]
  have hB0 : 0 ≤ Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1)) * Real.exp
      (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    rw [← hT]; exact tailT_nonneg hr0
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * max (Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)))
        (((sz.W n : ℕ) : ℝ) ^ (-D))
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
        mul_le_mul_of_nonneg_left (max_le_add_of_nonneg hB0 hW0) hWd
    _ = _ := by unfold STWB; ring


theorem st5_STprof_nonneg (n : ℕ) (u D ℓ : ℝ) (a b : Zd d (sz.L n)) : 0 ≤ STprof sz n u D ℓ a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  unfold STprof
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg hW.le _)) (tailW_pos hW _).le

theorem st5_STAI_nonneg (n : ℕ) : 0 ≤ STAI sz n := by
  unfold STAI
  positivity

/-- `t < 1` from `t ≤ lemT z` and `Im z > 0` (`z ∈ 𝐃_{κ,ε}`, `N ≥ 1`). -/
theorem st5_t_lt_one {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht : ∀ n, t n ≤ lemT (z n)) (n : ℕ) : t n < 1 := by
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hflow.2 n).2.1
  exact (ht n).trans_lt (lemT_lt_one him)

/-- `ilambda > 0` and `ilambda² W^d ≥ 1` eventually (`(eq:WO)`: `ilambda² W^d ≥ W^{2𝔡}`). -/
theorem st5_eventually_A_ge_one {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hWO : sz.WO 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ 1 ≤ STAI sz n := by
  filter_upwards [hWO] with n hn
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  refine ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hn.1, ?_⟩
  have h1 := lam_sq_mul_pow_ge sz n hn.1
  have h2 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.one_le_rpow hW (by linarith)
  unfold STAI
  linarith

/-- **Case (i), the closure of the constants**: with the initial-term control `F = A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}`, the
conclusion `F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}` of the integrated hierarchy is at most `4 (Δ_u^{1/5} W^{-d}B_{u,r}
e^{-(r/ℓ_u)^{1/2}} + W^{-D})`, the right side of `(Eq:Gdecay_flow)` (`(W^{-d}B_{u,0})^{1/5} ≥ (2A)^{-1/5}` since `B_{u,0} ≥
(ilambda² + 1-u)⁻¹ ≥ (2ilambda²)⁻¹` for `1 - u ≤ ilambda²`). -/
theorem st5_compare_I (n : ℕ) (hlam : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) {u D : ℝ} (hu : u < 1)
    (hx : 1 - u ≤ sz.lam n ^ 2) (a : Fin 2 → Zd d (sz.L n)) :
    ((STAI sz n) ^ (-(1 / 5) : ℝ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) +
        (STAI sz n) ^ (-(1 / 5) : ℝ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
      4 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hΔ := st5_Bctl_ge sz n hlam hu hx
  have hB0 : 0 < sz.Bctl n u := st_Bctl_pos sz hu
  -- `A^{-1/5} ≤ 2 Δ^{1/5}`
  have hA15 : (STAI sz n) ^ (-(1 / 5) : ℝ) ≤ 2 * (sz.Bctl n u) ^ (1 / 5 : ℝ) := by
    have h1 : (STAI sz n)⁻¹ ≤ 2 * sz.Bctl n u := by
      have : (STAI sz n)⁻¹ = 2 * (2 * STAI sz n)⁻¹ := by field_simp
      rw [this]; exact mul_le_mul_of_nonneg_left hΔ (by norm_num)
    rw [Real.rpow_neg hA0.le, ← Real.inv_rpow hA0.le]
    calc ((STAI sz n)⁻¹) ^ (1 / 5 : ℝ) ≤ (2 * sz.Bctl n u) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow (inv_nonneg.2 hA0.le) h1 (by norm_num)
      _ = 2 ^ (1 / 5 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.mul_rpow (by norm_num) hB0.le
      _ ≤ 2 * (sz.Bctl n u) ^ (1 / 5 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB0.le _)
          calc (2 : ℝ) ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hA1' : (STAI sz n) ^ (-(1 / 5) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  have hprof := st5_STprof_le sz n u D a
  have hprof0 := st5_STprof_nonneg sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
  have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  set P := STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
    Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    have : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
      unfold STWB Bparam
      have hx0 : 0 ≤ |1 - u| := abs_nonneg _
      positivity
    exact mul_nonneg this (Real.exp_pos _).le
  have hfl : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
          mul_le_mul_of_nonneg_right hWd hWD
      _ = _ := one_mul _
  have hX : (STAI sz n) ^ (-(1 / 5) : ℝ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) ≤
      2 * (sz.Bctl n u) ^ (1 / 5 : ℝ) * P + ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    calc (STAI sz n) ^ (-(1 / 5) : ℝ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
        ≤ (STAI sz n) ^ (-(1 / 5) : ℝ) * (P + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
          mul_le_mul_of_nonneg_left hprof (Real.rpow_nonneg hA0.le _)
      _ = (STAI sz n) ^ (-(1 / 5) : ℝ) * P +
            (STAI sz n) ^ (-(1 / 5) : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by ring
      _ ≤ 2 * (sz.Bctl n u) ^ (1 / 5 : ℝ) * P + 1 * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hA15 hP0) ?_
          calc (STAI sz n) ^ (-(1 / 5) : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D))
              ≤ 1 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
                mul_le_mul_of_nonneg_right hA1' (by positivity)
            _ ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (-D) := by linarith
      _ = _ := by ring
  have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
  rw [h0]
  nlinarith [hX, hWD, mul_nonneg (Real.rpow_nonneg hB0.le (1 / 5 : ℝ)) hP0]


/-- An empty index set gives `≺` for free. -/
theorem st5_prec_of_isEmpty {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (h : ∀ n, IsEmpty (U n)) :
    sz.Prec ξ ζ := by
  refine StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => ?_
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro u _
  exact (h n).false u

/-- **Case (i) from its ingredients** (`3_5:1957-2250`): the light-weight and quadratic-variation bounds `(S5WG+M000)`,
`(S5WG+M)` (`STEtermsMid`), the integrated hierarchy `(iois-mtx2)` (`STDuhamelI`) and the initial term `(iksjuwjx0)`
(`STIniTermI`, through `lem;CLT`) give `(Eq:Gdecay_flow)`; the strong estimate is void (`1 - t < 1 - s ≤ ilambda²`).
The constant `𝔠_d` is the minimum of the three pins' (`STConStInd` is monotone, `st5_conStInd_mono`). -/
theorem ST_step5_caseI_of_pins (hE : STEtermsMid d) (hD : STDuhamelI d) (hI : STIniTermI d) : STStep5I d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hE hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hD hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow ht
  have hcpos : 0 < min c₁ (min c₂ c₃) := lt_min hc₁ (lt_min hc₂ hc₃)
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hm₁ := st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)
  have hm₂ := st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))
  have hm₃ := st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_right _ _))
  have hE' := H₁ 𝔠 sz z hflow s t hs0 hst ht (st5_reg5I_mid (by omega) hR) hKb hKw hLK hDec hDecS hm₁ hS1 hS2
    hLmax hLKU
  have hD' := H₂ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₂ hS1 hS2 hLmax hLKU hE'
  have hI' := H₃ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₃ hS1 hS2 hLmax hLKU
  have hev := st5_eventually_A_ge_one sz hflow.1.2.1 hflow.1.2.2.2.2
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · have hdu := hD' D hD0
      (fun n p => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
      (fun n p => add_nonneg (mul_nonneg (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
        (st5_STprof_nonneg sz n _ _ _ _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hI' D hD0)
    have h1 := StochDomAt.precomp_param hdu
      (fun n (p : STIdx2 sz s t n) => ((p.1, ⟨p.2.1, trivial⟩, p.2.2) : STIdx2P sz STSigAll s t n))
    simp only [st5_zeroModeSet_empty] at h1
    refine st5_prec_mono sz hsz (c := 4) h1 ?_ ?_
    · filter_upwards [hev] with n hn
      intro p ω
      have hu : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
      have hx : 1 - (p.1 : ℝ) ≤ sz.lam n ^ 2 := by
        have := p.1.2.1
        have := (hR n).2
        linarith [p.1.2.1]
      have := st5_compare_I sz n hn.1 hn.2 (D := D) hu hx p.2.2
      simpa using this
    · intro n p ω
      have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) := by
        unfold Sizes.Bctl Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hS0 : 0 ≤ sz.STWB n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
        unfold STWB Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hr : (0 : ℝ) ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) := by
        rw [Real.rpow_zero]; norm_num
      positivity
  · refine st5_prec_of_isEmpty sz fun n => ⟨fun p => ?_⟩
    have h1 := (hR n).2
    have h2 := p.2
    have h3 := hst n
    linarith [p.1.1.2.1, p.1.1.2.2, h2]


/-! ### Case (iv): Step 5 is Step 4 (proved) -/

theorem st5_mE_im_le_one (E : ℝ) : (mE E).im ≤ 1 := by
  rw [mE_im]
  have h : Real.sqrt (4 - E ^ 2) ≤ 2 := by
    calc Real.sqrt (4 - E ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg E])
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

/-- **`W^{-d} B_{u,0} ≤ 1` on the flow window** (eventually in `n`, every `u ≤ t_n ≤ lemT z_n`): `W^{-d} B_{u,0} ≤ (ilambda² W^d)⁻¹ +
(N (1-u))⁻¹`, `(ilambda² W^d)⁻¹ ≤ W^{-2𝔡}` by `(eq:WO)`, and `1 - u ≥ 1 - lemT z ≥ Im z/16 ≥ N^{-1+ε}/16` (Lemma 2.8,
`lemma28_quant`; `z ∈ 𝐃_{κ,ε}`), so `(N(1-u))⁻¹ ≤ 16 N^{-ε}`: the smallness of the control `W^{-d}B_{u,0}` that every
exponent comparison of Steps 3-5 uses. -/
theorem st5_Bctl_le_one {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {t : ℕ → ℝ} (ht : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1 := by
  obtain ⟨⟨h𝔠, h𝔡, hsz, hbw, hWO⟩, hloc⟩ := hflow
  have hN : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
  have hNε : ∀ᶠ n in atTop, (32 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp hN).eventually_ge_atTop 32
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hbw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hN)
  have hW2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) :=
    ((tendsto_rpow_atTop (by linarith)).comp hWt).eventually_ge_atTop 2
  filter_upwards [hNε, hW2, hWO] with n hN32 hW2n hWOn u hu
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNeq : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hWOn.1
  have hA := lam_sq_mul_pow_ge sz n hWOn.1
  have hA2 : 2 ≤ STAI sz n := by unfold STAI; linarith
  have hloc' := hloc n
  obtain ⟨hre, hlow, hup⟩ := hloc'
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hlow
  have h28 := lemma28_quant hκ him hup hre
  have hzt := zt_im (lemE (z n)) (lemT (z n))
  have hT1 : lemT (z n) < 1 := lemT_lt_one him
  have hmE := st5_mE_im_le_one (lemE (z n))
  have hx : (1 / 16 : ℝ) * (z n).im ≤ 1 - lemT (z n) := by
    have h1 := h28.2.2.1
    rw [hzt] at h1
    have h2 : (1 - lemT (z n)) * (mE (lemE (z n))).im ≤ 1 - lemT (z n) :=
      mul_le_of_le_one_right (by linarith) hmE
    linarith
  have hx' : (1 / 16 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ 1 - u := by
    have := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 1 / 16)
    linarith [ht n]
  have hu1 : u < 1 := by linarith [ht n]
  have hx0 : 0 < 1 - u := by linarith
  -- the two terms of `W^{-d} B_{u,0}`
  have hB : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ +
      (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx0, hNeq]
    have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
    rw [h0, inv_one, mul_one]
    field_simp
  rw [hB]
  have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ 1 / 2 := by
    have hg2 : 0 < sz.lam n ^ 2 := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hg2 (by linarith)) (by positivity)
      _ = (STAI sz n)⁻¹ := by unfold STAI; rw [mul_inv]; ring
      _ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          exact (div_le_div_iff₀ (by linarith) (by norm_num)).2 (by linarith)
  have h2 : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ 1 / 2 := by
    have hlow' : ((sz.size n : ℕ) : ℝ) ^ ε / 16 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := by
      have : ((sz.size n : ℕ) : ℝ) * ((1 / 16 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε)) =
          ((sz.size n : ℕ) : ℝ) ^ ε / 16 := by
        rw [Real.rpow_add hNpos, Real.rpow_neg_one]
        field_simp
      calc ((sz.size n : ℕ) : ℝ) ^ ε / 16 = ((sz.size n : ℕ) : ℝ) * ((1 / 16 : ℝ) *
            ((sz.size n : ℕ) : ℝ) ^ (-1 + ε)) := this.symm
        _ ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left hx' hNpos.le
    have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ ε / 16 := by positivity
    calc (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ ε / 16)⁻¹ := inv_anti₀ hpos hlow'
      _ ≤ 1 / 2 := by
          rw [inv_eq_one_div, div_div_eq_mul_div, one_mul, div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
  linarith

theorem st5_exp_one_lt_three : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9
  linarith

/-- **Case (iv), the closure of the exponents**: for `1 - u ≤ ilambda²/L^d` and `W^{-d}B_{u,0} ≤ 1`, the Step-4 bound
`(W^{-d}B_{u,0})²` is at most `6 Δ_u^{1/5} W^{-d}B_{u,r} e^{-(r/ℓ_u)^{1/2}}`: `ℓ_u = L` (`ellT_eq_of_le`), `e^{-(r/L)^{1/2}} ≥ e⁻¹`
(`r ≤ L`), `B_{u,r} ≥ (L^d(1-u))⁻¹ ≥ ilambda⁻² ≥ (ilambda² + 1 - u)⁻¹`, so `B_{u,0} ≤ 2 (L^d(1-u))⁻¹ ≤ 2 B_{u,r}`
(`3_5:1940`: "`B_{t,0}` is dominated by the `(L^d|1-t|)⁻¹` term"). -/
theorem st5_compare_IV (n : ℕ) (hlam : 0 < sz.lam n) (hd : 2 ≤ d) {u D : ℝ} (hu : u < 1)
    (hΔ : sz.Bctl n u ≤ 1) (hx : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) (a : Fin 2 → Zd d (sz.L n)) :
    (sz.Bctl n u) ^ 2 ≤ 6 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by linarith
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hx0 : 0 < 1 - u := by
    by_contra hneg
    have h1 : 1 - u ≤ 0 := not_lt.1 hneg
    -- `u < 1` is a hypothesis
    linarith
  have hB0 : 0 < sz.Bctl n u := st_Bctl_pos sz hu
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  -- `ℓ_u = L`
  have hell : ellT (sz.L n) (sz.lam n) u = ((sz.L n : ℕ) : ℝ) := by
    refine ellT_eq_of_le hlam.le hu hL1 ?_
    refine hx.trans ?_
    exact div_le_div_of_nonneg_left hg2.le (by positivity) (pow_le_pow_right₀ hL1 hd)
  have hr : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast st5_zdistInf_le sz n (a 0 - a 1)
  have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp : Real.exp (-1) ≤ Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    rw [hell]
    apply Real.exp_le_exp.2
    have h1 : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ((sz.L n : ℕ) : ℝ) ≤ 1 :=
      (div_le_one hL0).2 hr
    have h2 : (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ((sz.L n : ℕ) : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
      calc _ ≤ (1 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (div_nonneg hr0 hL0.le) h1 (by norm_num)
        _ = 1 := Real.one_rpow _
    linarith
  -- `Z := (W^d)⁻¹ (L^d x)⁻¹ ≤ STWB`, `Δ ≤ 2 Z`
  set x := 1 - u with hxdef
  have hLx : ((sz.L n : ℕ) : ℝ) ^ d * x ≤ sz.lam n ^ 2 := by
    have := (le_div_iff₀ hLd).1 (show x ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d from hx)
    linarith
  have hgL : (sz.lam n ^ 2)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹ := inv_anti₀ (by positivity) hLx
  have hZ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹ ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    unfold STWB Bparam
    rw [abs_of_pos hx0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 0 ≤ (sz.lam n ^ 2 + x)⁻¹ * ((((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    linarith
  have hΔ2 : sz.Bctl n u ≤ 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹) := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx0]
    have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
    rw [h0, inv_one, mul_one]
    have h1 : (sz.lam n ^ 2 + x)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹ :=
      le_trans (inv_anti₀ hg2 (by linarith)) hgL
    have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + x)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹) ≤
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hΔS : sz.Bctl n u ≤ 2 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    calc sz.Bctl n u ≤ 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹) := hΔ2
      _ ≤ 2 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by linarith
  -- `Δ² ≤ Δ^{1/5} Δ`
  have hΔ15 : sz.Bctl n u ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hB0 hΔ (show (1 / 5 : ℝ) ≤ 1 by norm_num)
    simpa using this
  have hS0 : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) := by
    unfold STWB Bparam
    have hx0' : 0 ≤ |1 - u| := abs_nonneg _
    positivity
  have hD0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have h15 : 0 ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hB0.le _
  have hexp' : 1 ≤ Real.exp 1 * Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos 1).le
  set E' := Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) with hE'
  have hE0 : 0 < E' := Real.exp_pos _
  have h3 := st5_exp_one_lt_three
  have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
  rw [h0]
  have key : (sz.Bctl n u) ^ 2 ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * (2 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1))) := by
    calc (sz.Bctl n u) ^ 2 = sz.Bctl n u * sz.Bctl n u := sq _
      _ ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * sz.Bctl n u := mul_le_mul_of_nonneg_right hΔ15 hB0.le
      _ ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * (2 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1))) :=
          mul_le_mul_of_nonneg_left hΔS h15
  have hSE : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E' := mul_nonneg hS0 hE0.le
  have hfin : (sz.Bctl n u) ^ (1 / 5 : ℝ) * (2 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1))) ≤
      6 * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E') := by
    have h4 : 2 * STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) ≤
        6 * (STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E') := by
      have h5 : 1 ≤ 3 * E' := by nlinarith [hexp', Real.exp_pos 1]
      nlinarith [mul_le_mul_of_nonneg_left h5 hS0]
    calc _ ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * (6 * (STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) * E')) :=
          mul_le_mul_of_nonneg_left h4 h15
      _ = _ := by ring
  nlinarith [key, hfin, hD0, mul_nonneg h15 hSE]


/-- **Step 5, case (iv), proved** (`3_5:1940`: "the desired bound already follows from the conclusion `(Eq:L-KGt-flow)` in Step 4"):
the pin `STStep5IV` holds for every `d ≥ 3`, from `STLKU` at `k = 2`, `(W^{-d}B_{u,0})² ≤ 6 (W^{-d}B_{u,0})^{1/5} W^{-d}B_{u,r}
e^{-(r/ℓ_u)^{1/2}}` (`st5_compare_IV`) and `W^{-d}B_{u,0} ≤ 1` on the flow window (`st5_Bctl_le_one`); the strong estimate is void
(`1 - t < 1 - s ≤ ilambda²/L^d ≤ ilambda²`).  No ingredient pin is used. -/
theorem stStep5IV_holds (d : ℕ) : STStep5IV d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow ht
  have hev := st5_eventually_A_ge_one sz hflow.1.2.1 hflow.1.2.2.2.2
  have hΔ := st5_Bctl_le_one sz hκ hε hflow ht
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · refine st5_prec_mono sz hsz (c := 6) (hLKU 2 (by norm_num)) ?_ ?_
    · filter_upwards [hev, hΔ] with n hn hΔn
      intro p ω
      have hu : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
      have hx : 1 - (p.1 : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by
        linarith [hR n, p.1.2.1]
      have := st5_compare_IV sz n hn.1 (by omega) (D := D) hu (hΔn (p.1 : ℝ) p.1.2.2) hx p.2.2
      simpa using this
    · intro n p ω
      have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) := by
        unfold Sizes.Bctl Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hS0 : 0 ≤ sz.STWB n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
        unfold STWB Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hr : (0 : ℝ) ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) := by
        rw [Real.rpow_zero]; norm_num
      positivity
  · refine st5_prec_of_isEmpty sz fun n => ⟨fun p => ?_⟩
    have h1 := hR n
    have h2 := p.2
    have h3 := hst n
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have h4 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 := div_le_self (sq_nonneg _) hL1
    linarith



end RBM.Gauss.Sizes

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

/-! ### The four targets and the general statement -/

/-- **Step 5, case (i)** applied at `(szB, zB, 7/8, 15/16)`: `1/16 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`. -/
theorem inst_step5I (h : STStep5I 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_ing5_I STReg5I _ h szB_reg5I Cd hCd

/-- **Step 5, case (ii)** applied at `(szB, zB, 15/16, 31/32)`: `1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/16 ≤ 1/16`. -/
theorem inst_step5II (h : STStep5II 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_ing5_II STReg5II _ h szB_reg5II Cd hCd

/-- **Step 5, case (iii)** applied at `(sz0, z0, 0, 1/16)`: `ilambda_n² ≤ 15/16 = 1-t`. -/
theorem inst_step5III (h : STStep5III 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing5_III STReg5III _ h sz0_reg5III Cd hCd

/-- **Step 5, case (iv)** applied at `(szG, zB, 5/8, 3/4)`: `1-t = 1/4 ≤ 1-s = 3/8 ≤ ilambda²/L^3 = 25/64`. -/
theorem inst_step5IV (h : STStep5IV 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) Cd :=
  inst_ing5_IV STReg5IV _ h szG_reg4 Cd hCd

/-- Case (iv) is a theorem (`stStep5IV_holds`): the instance of the proved statement. -/
theorem inst_step5IV_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) Cd :=
  inst_step5IV (stStep5IV_holds 3) Cd hCd

/-- **Step 5, general** applied at `(sz0, z0, 0, 1/16)`. -/
theorem inst_step5 (h : STStep5 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing5_III STAny _ h trivial Cd hCd

/-- **The assembly** `STDecay ∧ STDecayStrong` at `t` from the uniform Step-5 conclusion, at `(sz0, z0, 0, 1/16)`. -/
theorem inst_assembly (h : STStep5Concl sz0 (STflowE z0) sInst tInst) :
    STDecay sz0 (STflowE z0) tInst ∧ STDecayStrong sz0 (STflowE z0) tInst :=
  ST_step5_assembly sz0 (fun n => (sz0_hst n).le) h

/-! ### The skeletons at the data (ingredients as hypotheses) -/

/-- Case (i) from its ingredients, at `(szB, zB, 7/8, 15/16)`: the three ingredient pins give the target pin, which is then
instantiated. -/
theorem inst_skeletonI (hE : STEtermsMid 3) (hD : STDuhamelI 3) (hI : STIniTermI 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_step5I (ST_step5_caseI_of_pins hE hD hI) Cd hCd

end RBM.Gauss.Step5Inst
