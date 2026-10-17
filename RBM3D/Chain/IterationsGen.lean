/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.IterationsA
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Chain.GridEnvelopeGen
import RBM3D.Chain.NQGood1Gen

/-!
# `lem:iterations` over the flow carrier, first file (U1s2, row b; ticket T2497)

Generic forms of `Induction/IterationsA.lean` (not edited) over a carrier `Cf : FlowFM sz` (resp. `Cm : Step2Mat sz`) and a law `μ`,
namespace `RBM.BA`, stem `IterationsGen_`, no `BA/*` import.  Paper: arXiv:2507.20274, `lem:iterations` (`3_5:1407-1417`, proof
`3_5:1772-1864`).  Scope S (DECISIONS §309 (2)): no generic text for the unprimed step `iterationsA_step` and its private controls.

* **Target 10** (§1): the `≺`-helpers at a law (`PrecL sz μ` for `Prec sz`; proofs verbatim): `st_prec_one_add_supg`,
  `st_prec_of_xig`, `iterationsA_prec_{mono_right,mono_left,absorb,rpow,one_add_mul}g`, `st_one_le_XiLg`, `st_one_le_XiLKg`.
* **Target 11** (§2): the odd chain bound `iterationsA_xiL_odd_leg` under `Step34Gen_LCompat`, `StepDecompGen_LoopForm` and a
  Hermitian flow matrix (`loopXi_le`, `loopMax_odd_sq_le` of `Split.lean` are model-free and used by name).
* **Target 12** (§3): `IterationsAScaleg` (content `T2497_IterScaleg`, `etaT (E n)` read as `Cf.eta n`), the plumbing
  `iterationsA_avg_of_STAvgUg`, `iterationsA_apriori_of_lRB1g`, `iterationsA_rela_of_Kg`, and the scale facts `iterationsA_scale_Ig`,
  `iterationsA_scale_IIg`, which are the band results at the energy `E'_n = 2 √(1 - (Im m_n)²)` (`Im mE(E'_n) = Im m_n`, `|E'_n| < 2`
  iff `Im m_n > 0`; as `sum_weighted_stepErrNg_le`, `GridEnvelopeGen:248`): the band `IterationsAScale` depends on `E` only through
  `etaT (E n)`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ} {sz : Sizes d} {μ : Measure sz.SeqΩ}

/-! ## 1. Target 10: the `≺` at a law -/

theorem st_prec_one_add_supg {U V : ℕ → Type*} [∀ n, Fintype (V n)] [hV : ∀ n, Nonempty (V n)]
    (hsize : Tendsto sz.size atTop atTop) (f : ∀ n, U n → V n → sz.SeqΩ → ℝ) (B : ∀ n, U n → ℝ)
    (hB : ∀ n u, 0 < B n u)
    (h : PrecL sz μ (U := fun n => U n × V n) (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1)) :
    PrecL sz μ (U := U)
      (fun n u ω => 1 + Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u)
      (fun _ _ _ => 1) := by
  intro τ hτ D hD
  filter_upwards [h (τ / 2) (half_pos hτ) D hD,
    hsize.eventually (eventually_le_rpow 2 (half_pos hτ))] with n hn h2
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := V n)) (fun v => f n u v ω)
  refine ⟨(u, v), ?_⟩
  have hNN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hh : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
  have hu' : ((sz.size n : ℕ) : ℝ) ^ τ < 1 + f n u v ω / B n u := by
    rw [← hv]; simpa using hu
  have hBpos := hB n u
  set a : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with ha
  have h3 : a < f n u v ω / B n u := by nlinarith
  change a * B n u < f n u v ω
  have := (lt_div_iff₀ hBpos).1 h3
  exact this

theorem st_prec_of_xig {U V : ℕ → Type*} [∀ n, Fintype (V n)] [hV : ∀ n, Nonempty (V n)]
    (f : ∀ n, U n → V n → sz.SeqΩ → ℝ) (B : ∀ n, U n → ℝ) (hB : ∀ n u, 0 < B n u)
    (h : PrecL sz μ (U := U)
      (fun n u ω => 1 + Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u)
      (fun _ _ _ => 1)) :
    PrecL sz μ (U := fun n => U n × V n) (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨⟨u, v⟩, hu⟩
  refine ⟨u, ?_⟩
  have hBpos := hB n u
  have h1 : f n u v ω ≤ Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) :=
    Finset.le_sup' (fun v => f n u v ω) (Finset.mem_univ v)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ τ < f n u v ω / B n u := by
    rw [lt_div_iff₀ hBpos]; exact hu
  have h3 : f n u v ω / B n u ≤ Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u :=
    div_le_div_of_nonneg_right h1 hBpos.le
  change ((sz.size n : ℕ) : ℝ) ^ τ * 1 < _
  linarith

/-- `0 ≤ max`, hence `Ξ̂ ≥ 1`, for a positive `W^{-d}B_{v,0}` (band `st_one_le_XiL`, `IterationsA:151`). -/
theorem st_one_le_XiLg (Cf : FlowFM sz) {n : ℕ} {v : ℝ} (k : ℕ) (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) :
    1 ≤ STXiLg Cf n v k ω := by
  unfold STXiLg
  have h0 : 0 ≤ STmaxLg Cf n v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Cf.L n v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

/-- Band `st_one_le_XiLK` (`IterationsA:160`). -/
theorem st_one_le_XiLKg (Cf : FlowFM sz) {n : ℕ} {v : ℝ} (k : ℕ) (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) :
    1 ≤ STXiLKg Cf n v k ω := by
  unfold STXiLKg
  have h0 : 0 ≤ STmaxLKg Cf n v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Cf.L n v p.1 p.2 ω - Cf.K n v p.1 p.2‖)
      (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB k).le
  linarith

/-! ### The `≺`-calculus used by the step (band `IterationsA:816-874`, proofs verbatim at `PrecL sz μ`) -/


/-- `ξ ≺ ζ` and `ζ ≤ ζ'` eventually give `ξ ≺ ζ'`. -/
theorem iterationsA_prec_mono_rightg {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) : PrecL sz μ ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with n hn
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `ξ ≤ ξ'` eventually and `ξ' ≺ ζ` give `ξ ≺ ζ`. -/
theorem iterationsA_prec_mono_leftg {U : ℕ → Type*} {ξ ξ' ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hle : ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ξ' n u ω) (h : PrecL sz μ ξ' ζ) : PrecL sz μ ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hle] with n hn
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_lt_of_le hu (hn u ω)⟩

/-- A constant factor on the right is absorbed: `ξ ≺ c ζ` gives `ξ ≺ ζ` (`ζ ≥ 0`). -/
theorem iterationsA_prec_absorbg (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ℝ} (hζ : ∀ᶠ n in atTop, ∀ u ω, 0 ≤ ζ n u ω)
    (h : PrecL sz μ ξ (fun n u ω => c * ζ n u ω)) : PrecL sz μ ξ ζ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow c (half_pos hτ)), hζ] with n hcN hζn
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : 0 ≤ ζ n u ω := hζn u ω
  calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (c * ζ n u ω)
      ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ n u ω) := by
        gcongr
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
        rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]

/-- Powers: `ξ ≺ ζ` gives `ξ^θ ≺ ζ^θ`, `θ > 0`, `ξ, ζ ≥ 0`. -/
theorem iterationsA_prec_rpowg {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, 0 ≤ ξ n u ω) (hζ : ∀ n u ω, 0 ≤ ζ n u ω) {θ : ℝ} (hθ : 0 < θ)
    (h : PrecL sz μ ξ ζ) : PrecL sz μ (fun n u ω => ξ n u ω ^ θ) (fun n u ω => ζ n u ω ^ θ) := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / θ, div_pos hτ hθ, Eventually.of_forall fun n => ?_⟩
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hN : 0 ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ τ = (((sz.size n : ℕ) : ℝ) ^ (τ / θ)) ^ θ := by
    rw [← Real.rpow_mul hN]; congr 1; field_simp
  have hu' : (((sz.size n : ℕ) : ℝ) ^ (τ / θ) * ζ n u ω) ^ θ < ξ n u ω ^ θ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN _) (hζ n u ω), ← h1]
    exact hu
  exact (Real.rpow_lt_rpow_iff (mul_nonneg (Real.rpow_nonneg hN _) (hζ n u ω)) (hξ n u ω) hθ).1 hu'

/-- `ξ ≺ ζ` gives `1 + c ξ ≺ 1 + c ζ` for a deterministic `c ≥ 0` (RBM2D `step3_one_add_inv_mul`, `Step3.lean:375`). -/
theorem iterationsA_prec_one_add_mulg (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ} (hc : ∀ n u, 0 ≤ c n u)
    (hξ : ∀ n u ω, 0 ≤ ξ n u ω) (h : PrecL sz μ ξ ζ) :
    PrecL sz μ (fun n u ω => 1 + c n u * ξ n u ω) (fun n u ω => 1 + c n u * ζ n u ω) := by
  have h1 : PrecL sz μ (U := U) (fun n _ _ => (1 : ℝ)) (fun _ _ _ => 1) :=
    StochDomAt.refl hsize fun _ _ _ => zero_le_one
  have h2 : PrecL sz μ (U := U) (fun n u _ => c n u) (fun n u _ => c n u) :=
    StochDomAt.refl hsize fun n u _ => hc n u
  have h3 := StochDomAt.mul hsize hξ (fun n u _ => hc n u) h2 h
  exact StochDomAt.add hsize h1 h3


/-! ## 2. Target 11: the odd chain bound

The loops `𝓛^{(m)}_{v,σ,a}` of the carrier are the list-based loops `loopL` of the Hermitian matrix `blockMat (Hf n v ω)` at
`z = ztOf (Cm.m n) (E n) v` (`Step34Gen_LCompat`, `StepDecompGen_LoopForm`), so `STmaxLg` is `RBM.Ind.loopMax` (`Split.lean`) and
`STXiLg = 1 + loopXi` with the scale `A = (W^{-d}B_{v,0})⁻¹`. -/

/-- `max_{σ,a} |𝓛^{(m)}_{v,σ,a}|` is the `loopMax` of the block matrix of the flow matrix (band `iterationsA_STmaxL_eq`, `IterationsA:716`). -/
private theorem iterationsA_STmaxLg_eq {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E : ℕ → ℝ}
    (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (v : ℝ) (m : ℕ) (ω : sz.SeqΩ) :
    STmaxLg Cm.toFlowFM n v m ω = RBM.Ind.loopMax d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (Hf n v ω)) (ztOf (Cm.m n) (E n) v) m := by
  have : Nonempty ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) := ⟨((fun _ => true), (fun _ => 0))⟩
  unfold STmaxLg RBM.Ind.loopMax
  rw [← Finset.sup'_univ_eq_ciSup]
  congr 1
  funext p
  show ‖Cm.L n v p.1 p.2 ω‖ = _
  rw [hLC n v p.1 p.2 ω, (hL n).2.2.1 v (Hf n v ω) (KLloopOf d (sz.L n) p.1 p.2)]
  rfl

/-- `Ξ̂^{(𝓛)}_{v,m} = 1 + Ξ^{(𝓛)}_m` with `Ξ_m = max|𝓛^{(m)}| (B_v⁻¹)^{m-1}` (band `iterationsA_STXiL_eq`, `IterationsA:729`). -/
private theorem iterationsA_STXiLg_eq {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E : ℕ → ℝ}
    (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) (v : ℝ) (m : ℕ) (ω : sz.SeqΩ) :
    STXiLg Cm.toFlowFM n v m ω = 1 + RBM.Ind.loopXi d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (Hf n v ω)) (ztOf (Cm.m n) (E n) v) (sz.Bctl n v)⁻¹ m := by
  unfold STXiLg RBM.Ind.loopXi
  rw [iterationsA_STmaxLg_eq hLC hL, div_eq_mul_inv, inv_pow]

/-- **Target 11, `iterationsA_xiL_odd_leg`** (band `iterationsA_xiL_odd_le`, `IterationsA:740`; `(suauwiioo1)`, `eq:boundtwochains`): for `N ≥ 3`
and `B_{v,0} > 0`, `Ξ̂^{(𝓛)}_{v,2N-1} ≤ 1 + B_v⁻¹ (Ξ̂_{2l₁} Ξ̂_{2l₂} Ξ̂_{2l₃} Ξ̂_{2l₄})^{1/2}`, pointwise in `ω`; the loops of the carrier
are those of the Hermitian flow matrix `Hf`. -/
theorem iterationsA_xiL_odd_leg {Cm : Step2Mat sz} {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E : ℕ → ℝ} (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E)
    (hHf : ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf n u ω).IsHermitian) (n : ℕ) {v : ℝ} (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) {N : ℕ} (hN : 3 ≤ N) :
    STXiLg Cm.toFlowFM n v (2 * N - 1) ω ≤ 1 + (sz.Bctl n v)⁻¹ *
      ((STXiLg Cm.toFlowFM n v (2 * ((N + 1) / 2)) ω * STXiLg Cm.toFlowFM n v (2 * (N / 2)) ω) *
        (STXiLg Cm.toFlowFM n v (2 * (N / 2)) ω * STXiLg Cm.toFlowFM n v (2 * ((N - 1) / 2)) ω)) ^ (1 / 2 : ℝ) := by
  set H := blockMat d (sz.L n) (sz.W n) (Hf n v ω) with hH
  set z := ztOf (Cm.m n) (E n) v with hz
  set A' : ℝ := (sz.Bctl n v)⁻¹ with hA'
  have hA'0 : 0 ≤ A' := (inv_pos.2 hB).le
  have hHerm : H.IsHermitian := (hHf n v ω).submatrix _
  set X : ℕ → ℝ := fun m => RBM.Ind.loopXi d (sz.L n) (sz.W n) H z A' m with hX
  have hXe : ∀ m, STXiLg Cm.toFlowFM n v m ω = 1 + X m := fun m => iterationsA_STXiLg_eq hLC hL n v m ω
  have hX0 : ∀ m, 0 ≤ X m := fun m => by
    simp only [hX, RBM.Ind.loopXi]
    exact mul_nonneg (RBM.Ind.loopMax_nonneg _) (pow_nonneg hA'0 _)
  -- (6.4)
  have hodd := RBM.Ind.loopMax_odd_sq_le (d := d) (L := sz.L n) (W := sz.W n) (z := z) hHerm (m := N - 1) (by omega)
  rw [show 2 * (N - 1) + 1 = 2 * N - 1 by omega, show 2 * (N - 1) + 2 = 2 * N by omega,
    show 2 * (N - 1) = 2 * N - 2 by omega] at hodd
  have hsq : X (2 * N - 1) ^ 2 ≤ X (2 * N - 2) * X (2 * N) := by
    simp only [hX, RBM.Ind.loopXi]
    have hp : A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1) = A' ^ (2 * N - 2 - 1) * A' ^ (2 * N - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hmul := mul_le_mul_of_nonneg_right hodd (show 0 ≤ A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1) by positivity)
    calc (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 1) * A' ^ (2 * N - 1 - 1)) ^ 2
        = RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 1) ^ 2 * (A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1)) := by ring
      _ ≤ (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 2) * RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N)) *
            (A' ^ (2 * N - 1 - 1) * A' ^ (2 * N - 1 - 1)) := hmul
      _ = (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N - 2) * A' ^ (2 * N - 2 - 1)) *
            (RBM.Ind.loopMax d (sz.L n) (sz.W n) H z (2 * N) * A' ^ (2 * N - 1)) := by
          rw [hp]; ring
  -- (5.118) twice
  have h1 : X (2 * N) ≤ X (2 * ((N + 1) / 2)) * X (2 * (N / 2)) * A' := by
    have := RBM.Ind.loopXi_le (d := d) (L := sz.L n) (W := sz.W n) (z := z) hHerm hA'0 (n := N - 1)
      (l₁ := (N + 1) / 2) (l₂ := N / 2) (by omega) (by omega) (by omega)
    rwa [show 2 * (N - 1) + 2 = 2 * N by omega] at this
  have h2 : X (2 * N - 2) ≤ X (2 * (N / 2)) * X (2 * ((N - 1) / 2)) * A' := by
    have := RBM.Ind.loopXi_le (d := d) (L := sz.L n) (W := sz.W n) (z := z) hHerm hA'0 (n := N - 2)
      (l₁ := N / 2) (l₂ := (N - 1) / 2) (by omega) (by omega) (by omega)
    rwa [show 2 * (N - 2) + 2 = 2 * N - 2 by omega] at this
  have hXX : X (2 * N - 1) ^ 2 ≤ A' ^ 2 * ((X (2 * ((N + 1) / 2)) * X (2 * (N / 2))) * (X (2 * (N / 2)) * X (2 * ((N - 1) / 2)))) := by
    refine hsq.trans ?_
    calc X (2 * N - 2) * X (2 * N)
        ≤ (X (2 * (N / 2)) * X (2 * ((N - 1) / 2)) * A') * (X (2 * ((N + 1) / 2)) * X (2 * (N / 2)) * A') :=
          mul_le_mul h2 h1 (hX0 _) (by have := hX0 (2 * (N / 2)); have := hX0 (2 * ((N - 1) / 2)); positivity)
      _ = A' ^ 2 * ((X (2 * ((N + 1) / 2)) * X (2 * (N / 2))) * (X (2 * (N / 2)) * X (2 * ((N - 1) / 2)))) := by ring
  -- from `Ξ ≤ Ξ̂`
  have hP : (X (2 * ((N + 1) / 2)) * X (2 * (N / 2))) * (X (2 * (N / 2)) * X (2 * ((N - 1) / 2))) ≤
      ((1 + X (2 * ((N + 1) / 2))) * (1 + X (2 * (N / 2)))) * ((1 + X (2 * (N / 2))) * (1 + X (2 * ((N - 1) / 2)))) := by
    have a1 := hX0 (2 * ((N + 1) / 2)); have a2 := hX0 (2 * (N / 2)); have a3 := hX0 (2 * ((N - 1) / 2))
    gcongr <;> linarith
  have hfin : X (2 * N - 1) ≤ A' * (((1 + X (2 * ((N + 1) / 2))) * (1 + X (2 * (N / 2)))) *
      ((1 + X (2 * (N / 2))) * (1 + X (2 * ((N - 1) / 2))))) ^ (1 / 2 : ℝ) := by
    set P : ℝ := ((1 + X (2 * ((N + 1) / 2))) * (1 + X (2 * (N / 2)))) * ((1 + X (2 * (N / 2))) * (1 + X (2 * ((N - 1) / 2)))) with hPdef
    have hP0 : 0 ≤ P := by
      have a1 := hX0 (2 * ((N + 1) / 2)); have a2 := hX0 (2 * (N / 2)); have a3 := hX0 (2 * ((N - 1) / 2))
      rw [hPdef]; positivity
    rw [← Real.sqrt_eq_rpow]
    have hle : X (2 * N - 1) ^ 2 ≤ (A' * Real.sqrt P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP0]
      exact hXX.trans (mul_le_mul_of_nonneg_left hP (by positivity))
    exact le_of_sq_le_sq hle (by positivity) |>.trans (le_refl _)
  rw [hXe (2 * N - 1), hXe (2 * ((N + 1) / 2)), hXe (2 * (N / 2)), hXe (2 * ((N - 1) / 2))]
  linarith




/-! ## 3. Target 12: the scale facts, the plumbing of the step -/

/-- **Target 12, `IterationsAScaleg`** (content `T2497_IterScaleg`; band record `IterationsAScale`, `IterationsA:1058`): the nine fields of the
band record, `etaT (E n)` read as `Cf.eta n`. -/
structure IterationsAScaleg (Cf : FlowFM sz) (s t A T : ℕ → ℝ) (cB cv K : ℝ) : Prop where
  cB_nonneg : 0 ≤ cB
  one_le_cv : 1 ≤ cv
  one_le_K : 1 ≤ K
  A_nonneg : ∀ n, 0 ≤ A n
  T_nonneg : ∀ n, 0 ≤ T n
  t_lt_one : ∀ n, t n < 1
  one_le_A : ∀ᶠ n in atTop, 1 ≤ A n
  rho : ∀ᶠ n in atTop, ∀ q : STPair s t n, 1 ≤ Cf.eta n (s n) / Cf.eta n q.1.2 ∧
    (Cf.eta n (s n) / Cf.eta n q.1.2) ^ 2 ≤ K * A n ^ (1 / 8 : ℝ) ∧
    T n * (Cf.eta n (s n) / Cf.eta n q.1.2) ^ 2 * A n ^ (7 / 8 : ℝ) ≤ cB * K
  TA : ∀ᶠ n in atTop, T n * A n ^ (3 / 4 : ℝ) ≤ cB
  Bctl : ∀ᶠ n in atTop, ∀ w : TimeIcc s t n, (cv * A n)⁻¹ ≤ sz.Bctl n (w : ℝ) ∧ sz.Bctl n (w : ℝ) ≤ T n

/-- A band record at any energy sequence `E` with `etaT (E n) = Cf.eta n` is the generic record of `Cf`. -/
private theorem IterationsAScaleg_of_band {Cf : FlowFM sz} {E s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hη : ∀ n u, etaT (E n) u = Cf.eta n u) (h : IterationsAScale sz E s t A T cB cv K) :
    IterationsAScaleg Cf s t A T cB cv K :=
  ⟨h.cB_nonneg, h.one_le_cv, h.one_le_K, h.A_nonneg, h.T_nonneg, h.t_lt_one, h.one_le_A, by simpa only [hη] using h.rho,
    h.TA, h.Bctl⟩

/-- `η_a / η_b = (1 - a)/(1 - b)` at the carrier (`η_u = (1 - u) Im m_n > 0`; band `scaleFacts_etaT_div_etaT`, `ScaleFacts:342`). -/
theorem IterationsGen_eta_ratio {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {a b : ℝ} :
    Cm.eta n a / Cm.eta n b = (1 - a) / (1 - b) := by
  rw [NQGood1Gen_eta_eq hL, NQGood1Gen_eta_eq hL]
  exact mul_div_mul_right _ _ (hL n).1.ne'

/-- **The energy `E'_n = 2 √(1 - (Im m_n)²)`** (`GridEnvelopeGen:248-261`): under `StepDecompGen_LoopForm` and `‖m‖ ≤ 1` it has `|E'_n| < 2`
(`Im m_n > 0`) and `etaT E'_n = Cm.eta n` (`Im mE(E'_n) = Im m_n`). -/
private theorem IterationsGen_Ep {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) :
    ∃ E' : ℕ → ℝ, (∀ n, |E' n| < 2) ∧ ∀ n u, etaT (E' n) u = Cm.eta n u := by
  refine ⟨fun n => 2 * Real.sqrt (1 - ((Cm.m n).im) ^ 2), fun n => ?_, fun n u => ?_⟩
  · have hy0 := (hL n).1
    have hr : Real.sqrt (1 - ((Cm.m n).im) ^ 2) < 1 :=
      (Real.sqrt_lt' (by norm_num)).2 (by nlinarith)
    rw [abs_of_nonneg (by positivity)]
    linarith
  · unfold etaT
    rw [GridEnvelopeGen_mE_im_Ep (hL n).1.le (NQGood1Gen_im_le_one (hm n)), NQGood1Gen_eta_eq hL]

/-- **The averaged law on the pairs** (`3_5:1386`, `3_5:1774`; band `iterationsA_avg_of_STAvgU`, `IterationsA:1359`): `Ξ̂^{(𝓛-𝒦)}_{v,1} ≺ 1`
uniformly in `(v,u)`, from `STAvgUgL`. -/
theorem iterationsA_avg_of_STAvgUg (Cf : FlowFM sz) (hsize : Tendsto sz.size atTop atTop) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STAvgUgL Cf μ s t) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 1 ω) (fun _ _ _ => 1) := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  have hBpos : ∀ n (v : TimeIcc s t n), 0 < (sz.Bctl n (v : ℝ)) ^ 1 := fun n v =>
    pow_pos (st_Bctl_pos sz (n := n) (lt_of_le_of_lt (v.2).2 (ht1 n))) 1
  exact StochDomAt.precomp_param
    (st_prec_one_add_supg hsize (U := fun n => TimeIcc s t n)
      (V := fun n => (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
      (fun n v p ω => ‖Cf.L n (v : ℝ) p.1 p.2 ω - Cf.K n (v : ℝ) p.1 p.2‖)
      (fun n v => (sz.Bctl n (v : ℝ)) ^ 1) (fun n v => hBpos n v) h) φ


/-- The real inequality behind `iterationsA_apriori_of_lRB1g` (band `IterationsGen_apriori_aux`, `IterationsA:1373`, private there). -/
private theorem IterationsGen_apriori_aux {S rv ru bs bv : ℝ} (hS : 0 ≤ S) (hrv : 1 ≤ rv) (hru : rv ≤ ru)
    (hbs : 0 < bs) (hbv : bs ≤ bv) : 1 + S / bv ≤ ru * (1 + S / (rv * bs)) := by
  have hrv0 : 0 < rv := by linarith
  have hbv0 : 0 < bv := by linarith
  have h1 : S / bv ≤ S / bs := div_le_div_of_nonneg_left hS hbs hbv
  have h2 : S / bs = rv * (S / (rv * bs)) := by field_simp
  have h3 : 0 ≤ S / (rv * bs) := by positivity
  have h4 : rv * (S / (rv * bs)) ≤ ru * (S / (rv * bs)) := mul_le_mul_of_nonneg_right hru h3
  nlinarith

/-- `1 ≤ (1 - s)/(1 - v)` for `s ≤ v < 1` (band `IterationsGen_one_le_ratio`, `IterationsA:876`, private there). -/
private theorem IterationsGen_one_le_ratio {s v : ℝ} (hsv : s ≤ v) (hv1 : v < 1) : 1 ≤ (1 - s) / (1 - v) := by
  have hxv : 0 < 1 - v := by linarith
  rw [le_div_iff₀ hxv]; linarith

/-- **The a priori bound `(sef8w483r324)` on the pairs** (`3_5:1391`; band `iterationsA_apriori_of_lRB1`, `IterationsA:1385`): `Ξ̂^{(𝓛)}_{v,m} ≺
(η_s/η_u)^{m-1}` uniformly in `(v,u)`, from `STStep1LoopgL`; `StepDecompGen_LoopForm` replaces `|E| < 2` (ratio `η_s/η_u = (1-s)/(1-u)`). -/
theorem iterationsA_apriori_of_lRB1g {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hsize : Tendsto sz.size atTop atTop) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) (h : STStep1LoopgL Cm.toFlowFM μ s t)
    (m : ℕ) (hm : 1 ≤ m) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1)) := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  have hv1 : ∀ n (v : TimeIcc s t n), (v : ℝ) < 1 := fun n v => lt_of_le_of_lt (v.2).2 (ht1 n)
  have hBc : ∀ n (v : TimeIcc s t n), 0 < ((1 - s n) / (1 - (v : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1) :=
    fun n v => by
      have h1 : 0 < 1 - s n := by linarith [(v.2).1, hv1 n v]
      have h2 : 0 < 1 - (v : ℝ) := by linarith [hv1 n v]
      have h3 : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (n := n) (by linarith [(v.2).1, hv1 n v])
      positivity
  have hX := st_prec_one_add_supg hsize (U := fun n => TimeIcc s t n)
    (V := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
    (fun n v p ω => ‖Cm.toFlowFM.L n (v : ℝ) p.1 p.2 ω‖)
    (fun n v => ((1 - s n) / (1 - (v : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1)) hBc (h m hm)
  have hX' := StochDomAt.precomp_param hX φ
  have hXnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ 1 + (Finset.univ.sup' Finset.univ_nonempty
      (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cm.toFlowFM.L n (φ n q : ℝ) p.1 p.2 ω‖)) /
        (((1 - s n) / (1 - (φ n q : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1)) := fun n q ω => by
    have h0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cm.toFlowFM.L n (φ n q : ℝ) p.1 p.2 ω‖) :=
      le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
        ‖Cm.toFlowFM.L n (φ n q : ℝ) p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
    have := hBc n (φ n q)
    positivity
  -- ρ_u^{m-1} · X ≺ ρ_u^{m-1} · 1
  have hρu : ∀ n (q : STPair s t n), 0 ≤ (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1) := fun n q => by
    rw [IterationsGen_eta_ratio hL n]
    have h1 : 0 ≤ 1 - s n := by linarith [q.2.1, hv1 n (φ n q)]
    have h2 : 0 ≤ 1 - q.1.2 := by linarith [q.2.2.2, ht1 n]
    positivity
  have hmul : PrecL sz μ (U := STPair s t)
      (fun n q ω => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1) * (1 + (Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cm.toFlowFM.L n (φ n q : ℝ) p.1 p.2 ω‖)) /
          (((1 - s n) / (1 - (φ n q : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1))))
      (fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1) * 1) :=
    StochDomAt.mul (ξ₁ := fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1))
      (ξ₂ := fun n q ω => 1 + (Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cm.toFlowFM.L n (φ n q : ℝ) p.1 p.2 ω‖)) /
          (((1 - s n) / (1 - (φ n q : ℝ))) ^ (m - 1) * (sz.Bctl n (s n)) ^ (m - 1)))
      (ζ₁ := fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1)) (ζ₂ := fun _ _ _ => 1) hsize
      (fun n q ω => hXnn n q ω) (fun n q _ => hρu n q)
      (StochDomAt.refl hsize (fun n q _ => hρu n q)) hX'
  refine iterationsA_prec_mono_rightg (iterationsA_prec_mono_leftg ?_ hmul)
    (Eventually.of_forall fun n q ω => by rw [mul_one])
  refine Eventually.of_forall fun n q ω => ?_
  -- the pointwise bound `Ξ̂ ≤ ρ_u^{m-1} X`
  have hsv : s n ≤ q.1.1 := q.2.1
  have hvu : q.1.1 ≤ q.1.2 := q.2.2.1
  have hv1' : q.1.1 < 1 := hv1 n (φ n q)
  have hu1 : q.1.2 < 1 := lt_of_le_of_lt q.2.2.2 (ht1 n)
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (n := n) (lt_of_le_of_lt hsv hv1')
  have hBv : sz.Bctl n (s n) ≤ sz.Bctl n q.1.1 := STBctl_mono sz n hsv hv1'
  have hS0 : 0 ≤ STmaxLg Cm.toFlowFM n q.1.1 m ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
      ‖Cm.toFlowFM.L n q.1.1 p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  rw [IterationsGen_eta_ratio hL n]
  have hrv := IterationsGen_one_le_ratio hsv hv1'
  have hrvu : (1 - s n) / (1 - q.1.1) ≤ (1 - s n) / (1 - q.1.2) := by
    have h2 : 0 < 1 - q.1.2 := by linarith
    exact div_le_div_of_nonneg_left (by linarith) h2 (by linarith)
  have key := IterationsGen_apriori_aux hS0 (one_le_pow₀ hrv : 1 ≤ ((1 - s n) / (1 - q.1.1)) ^ (m - 1))
    (pow_le_pow_left₀ (by linarith) hrvu _) (pow_pos hBs (m - 1)) (pow_le_pow_left₀ hBs.le hBv _)
  change 1 + STmaxLg Cm.toFlowFM n q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) ≤ _
  exact key


/-- **`(rela_XILXILK)` on the pairs** (`3_5:1387`; band `iterationsA_rela_of_K`, `IterationsA:1454`): `Ξ̂^{(𝓛)}_{v,m} ≺ 1 + W^{-d}B_{v,0}
Ξ̂^{(𝓛-𝒦)}_{v,m}`, from the `𝒦`-loop bound uniform in `(v,u)` and the labels. -/
theorem iterationsA_rela_of_Kg (Cf : FlowFM sz) (hsize : Tendsto sz.size atTop atTop) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (m : ℕ) (hm : 1 ≤ m)
    (hK : PrecL sz μ (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖Cf.K n p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1))) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω) := by
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (n := n) (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n))
  have hX := st_prec_one_add_supg hsize (U := STPair s t)
    (V := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
    (fun n q p ω => ‖Cf.K n q.1.1 p.1 p.2‖) (fun n q => sz.Bctl n q.1.1 ^ (m - 1))
    (fun n q => pow_pos (hBpos n q) _) hK
  have hGnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω :=
    fun n q ω => by
      have := st_one_le_XiLKg Cf (n := n) (v := q.1.1) m ω (hBpos n q)
      have := hBpos n q
      positivity
  have hadd := StochDomAt.add hsize hX
    (StochDomAt.refl hsize (ζ := fun n q ω => sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω) hGnn)
  refine iterationsA_prec_mono_leftg ?_ hadd
  refine Eventually.of_forall fun n q ω => ?_
  have hB0 := hBpos n q
  have hBm : 0 < sz.Bctl n q.1.1 ^ (m - 1) := pow_pos hB0 _
  set SK : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cf.K n q.1.1 p.1 p.2‖) with hSK
  have hSL : STmaxLg Cf n q.1.1 m ω ≤ SK + STmaxLKg Cf n q.1.1 m ω := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have h1 : ‖Cf.L n q.1.1 p.1 p.2 ω‖ ≤ ‖Cf.K n q.1.1 p.1 p.2‖ +
        ‖Cf.L n q.1.1 p.1 p.2 ω - Cf.K n q.1.1 p.1 p.2‖ := by
      calc ‖Cf.L n q.1.1 p.1 p.2 ω‖
          = ‖Cf.K n q.1.1 p.1 p.2 + (Cf.L n q.1.1 p.1 p.2 ω - Cf.K n q.1.1 p.1 p.2)‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖Cf.K n q.1.1 p.1 p.2‖ ≤ SK :=
      Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cf.K n q.1.1 p.1 p.2‖)
        (Finset.mem_univ p)
    have h3 : ‖Cf.L n q.1.1 p.1 p.2 ω - Cf.K n q.1.1 p.1 p.2‖ ≤ STmaxLKg Cf n q.1.1 m ω :=
      Finset.le_sup' (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) =>
        ‖Cf.L n q.1.1 p.1 p.2 ω - Cf.K n q.1.1 p.1 p.2‖) (Finset.mem_univ p)
    linarith
  have hGeq : sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω =
      sz.Bctl n q.1.1 + STmaxLKg Cf n q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) := by
    unfold STXiLKg
    have : sz.Bctl n q.1.1 ^ m = sz.Bctl n q.1.1 * sz.Bctl n q.1.1 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; field_simp
  change 1 + STmaxLg Cf n q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) ≤
    (1 + SK / sz.Bctl n q.1.1 ^ (m - 1)) + sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω
  rw [hGeq]
  have h4 : STmaxLg Cf n q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) ≤
      SK / sz.Bctl n q.1.1 ^ (m - 1) + STmaxLKg Cf n q.1.1 m ω / sz.Bctl n q.1.1 ^ (m - 1) := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hSL hBm.le
  linarith


/-- **Target 12, `iterationsA_scale_Ig`** (band `iterationsA_scale_I`, `IterationsA:1631`, at the energy `E'`, `IterationsGen_Ep`): case (i),
`A = lam² W^d`, `T = 2 A⁻¹`, `cB = cv = K = 2`, over the carrier `Cm.toFlowFM`; `StepDecompGen_LoopForm` and `‖m‖ ≤ 1` replace `|E| < 2`. -/
theorem iterationsA_scale_Ig (hd : 2 ≤ d) {Cm : Step2Mat sz} {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ}
    (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 16)
    (hreg : STRegIterI sz s t) (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1) :
    IterationsAScaleg Cm.toFlowFM s t (fun n => sz.STAI n) (fun n => 2 * (sz.STAI n)⁻¹) 2 2 2 := by
  obtain ⟨E', hE', hη⟩ := IterationsGen_Ep hL hm
  exact IterationsAScaleg_of_band hη (iterationsA_scale_I sz hd h𝔠d hc hreg hcon hWO ht1 hE')

/-- **Target 12, `iterationsA_scale_IIg`** (band `iterationsA_scale_II`, `IterationsA:1704`, at the energy `E'`): case (ii), `A = (W^{-d}B_{s,0})⁻¹`,
`T = A^{-1+𝔠d}`, `cB = cv = K = 1`. -/
theorem iterationsA_scale_IIg {Cm : Step2Mat sz} {E s t : ℕ → ℝ} {𝔠d : ℝ}
    (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 24)
    (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) :
    IterationsAScaleg Cm.toFlowFM s t (fun n => sz.STAII s n) (fun n => (sz.STAII s n) ^ (-1 + 𝔠d)) 1 1 1 := by
  obtain ⟨E', hE', hη⟩ := IterationsGen_Ep hL hm
  exact IterationsAScaleg_of_band hη (iterationsA_scale_II sz h𝔠d hc hcon ht1 hE')

/-! ## 4. Compiled nonempty instances (`d = 3`; band data `szB`, `zB` of `Induction/Step34Pins.lean:710-842`)

The carrier is `bandStep2Mat szB (STflowE zB)` (`bandFM` for the targets that read only the carrier); `ω ≡ 0`.  What stays a hypothesis
of an instance is a stochastic premise (`STAvgUgL`, `STStep1LoopgL`, the uniform `𝒦` bound). -/

end RBM.BA
