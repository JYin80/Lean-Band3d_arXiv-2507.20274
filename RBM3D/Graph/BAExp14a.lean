/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Carrier
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.ScaleFacts
import RBM3D.Graph.BASizeClaim
import RBM3D.BA.Step1Trivial
import RBM3D.BA.GreenLDE
import RBM3D.BA.LWPinsBA

/-!
# The generic machinery of the crude bound for the six families of `lem:LWterm_EXP` at BA

Paper: Subappendix B.1, proof of Lemma 6.2 (`lem:LWterm_EXP`): (B.1) `eq:ELW_term`, (B.20)
`GGGamma`, Lemma B.6 (`lanlw`).  This file is the model-free and deterministic half of the BA
counterpart of `Graph/LWExpTerm4.lean` (Sections 2-5): the `≺` toolbox at an arbitrary law
(`≺ → 𝔼` first moment, finite unions, one-index calculus), the fine-level Ward identity (as
`lwExpTerm4_ward_*`), the block combinatorics of the fine lattice and the pathwise bounds of the
sums `J` of the six families, the comparison arithmetic, and the deterministic BA data (`M`,
`ω = Θ^{(+,+)}`, `W - 1 = lift(ω - 1)`, `B ≤ 2`).  The statement `BAExp14aS1` and its proof are in
`Graph/BAExp14aB.lean`.  No twisted quantity (`BATwistAvgLaw`, `BATwistLoopLaw`) occurs.

All private helpers carry the stem `BAExp14a_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## A1. The toolbox of `≺` at an arbitrary law -/

section Toolbox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A deterministic `≺` is the pointwise bound for large `n`** (as `st6_prec_det_iff` in `Induction/Step6Kit.lean`, at an
arbitrary probability law). -/
theorem BAExp14a_det_iff [IsProbabilityMeasure P] {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop)
    {V : ℕ → Type*} (F G : ∀ n, V n → ℝ) :
    StochDomAt P size (fun n v (_ : Ω) => F n v) (fun n v _ => G n v) ↔
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, F n v ≤ ((size n : ℕ) : ℝ) ^ τ * G n v := by
  constructor
  · intro h τ hτ
    have h1 := h τ hτ 1 one_pos
    filter_upwards [h1, hsize.eventually (eventually_ge_atTop 2)] with n hn hN2
    intro v
    by_contra hcon
    push Not at hcon
    have hbad : badSetAt size (fun n v (_ : Ω) => F n v) (fun n v (_ : Ω) => G n v) τ n = (Set.univ : Set Ω) := by
      ext ω
      simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨v, hcon⟩
    rw [hbad, measure_univ] at hn
    have hN : (2 : ℝ) ≤ ((size n : ℕ) : ℝ) := by exact_mod_cast hN2
    have hlt : ((size n : ℕ) : ℝ) ^ (-(1 : ℝ)) < 1 := by
      rw [Real.rpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    have h2 : ENNReal.ofReal (((size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hlt
    exact absurd hn (not_le.2 h2)
  · intro h
    refine StochDomAt.of_eventually_empty fun τ hτ => ?_
    filter_upwards [h τ hτ] with n hn
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    exact fun v => hn v

/-- `≺` transports along pointwise equal families. -/
theorem BAExp14a_prec_congr {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hξ : ∀ l u ω, ξ l u ω = ξ' l u ω) (hζ : ∀ l u ω, ζ l u ω = ζ' l u ω) (h : StochDomAt P size ξ ζ) :
    StochDomAt P size ξ' ζ' := by
  have e1 : ξ = ξ' := by funext l u ω; exact hξ l u ω
  have e2 : ζ = ζ' := by funext l u ω; exact hζ l u ω
  subst e1 e2
  exact h

/-- `StochDomAt.of_subset` for two different index types: a failure event eventually contained in that of another `≺`. -/
theorem BAExp14a_prec_of_bad {size : ℕ → ℕ} {U₁ U₂ : ℕ → Type*} {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ}
    {ξ₂ ζ₂ : ∀ l, U₂ l → Ω → ℝ} (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, badSetAt size ξ₂ ζ₂ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) :
    StochDomAt P size ξ₂ ζ₂ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

/-- A pointwise smaller family is dominated by the same bound (the inequality only for large `l`). -/
theorem BAExp14a_prec_of_le_ev {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ξ₁ ζ : ∀ l, U l → Ω → ℝ}
    (hle : ∀ᶠ l in atTop, ∀ u ω, ξ l u ω ≤ ξ₁ l u ω) (h : StochDomAt P size ξ₁ ζ) : StochDomAt P size ξ ζ :=
  BAExp14a_prec_of_bad h fun τ hτ => ⟨τ, hτ, by
    filter_upwards [hle] with l hl ω ⟨u, hu⟩
    exact ⟨u, lt_of_lt_of_le hu (hl u ω)⟩⟩

/-- `ξ ≺ ζ₁` and (eventually) `ζ₁ ≤ K ζ₂` give `ξ ≺ ζ₂` (`K > 0`, `ζ₂ ≥ 0`). -/
theorem BAExp14a_prec_mono {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
    {ξ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} {K : ℝ} (hK : 0 < K) (hζ₂ : ∀ l u ω, 0 ≤ ζ₂ l u ω)
    (hle : ∀ᶠ l in atTop, ∀ u ω, ζ₁ l u ω ≤ K * ζ₂ l u ω) (h : StochDomAt P size ξ ζ₁) : StochDomAt P size ξ ζ₂ := by
  refine BAExp14a_prec_of_bad h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, hsize.eventually (eventually_le_rpow K (half_pos hτ))] with l hl hKN ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 := hζ₂ l u ω
  have h3 : (size l : ℝ) ^ (τ / 2) * ζ₁ l u ω ≤ (size l : ℝ) ^ τ * ζ₂ l u ω := by
    calc (size l : ℝ) ^ (τ / 2) * ζ₁ l u ω ≤ (size l : ℝ) ^ (τ / 2) * (K * ζ₂ l u ω) :=
          mul_le_mul_of_nonneg_left (hl u ω) hpos
      _ ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ₂ l u ω) := by
          refine mul_le_mul_of_nonneg_left ?_ hpos
          exact mul_le_mul_of_nonneg_right hKN h2
      _ = (size l : ℝ) ^ τ * ζ₂ l u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]
  exact lt_of_le_of_lt h3 hu

/-- **The first moment off the failure event** (as `lwExpTerm_first_moment` in `Graph/LWExpTerm.lean`). -/
private theorem BAExp14a_first_moment [IsProbabilityMeasure P] {f : Ω → ℂ} {S : Set Ω} {c B : ℝ} (hc : 0 ≤ c)
    (hB : ∀ ω, ‖f ω‖ ≤ B) (hin : ∀ ω, ω ∉ S → ‖f ω‖ ≤ c) : ∫ ω, ‖f ω‖ ∂P ≤ c + B * (P S).toReal := by
  classical
  set S' : Set Ω := toMeasurable P S with hS'
  have hmeas : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS : P S' = P S := measure_toMeasurable S
  have hpt : ∀ ω, ‖f ω‖ ≤ c + B * S'.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω]
      have := hB ω
      linarith
    · rw [Set.indicator_of_notMem hω]
      have := hin ω (fun h => hω (subset_toMeasurable P S h))
      linarith
  have hint : Integrable (fun ω => c + B * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const c).add (Integrable.const_mul ((integrable_const (1 : ℝ)).indicator hmeas) B)
  calc ∫ ω, ‖f ω‖ ∂P ≤ ∫ ω, (c + B * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = c + B * (P S).toReal := by
        rw [integral_add (integrable_const c) (Integrable.const_mul
          ((integrable_const (1 : ℝ)).indicator hmeas) B), integral_const,
          integral_const_mul, integral_indicator_const _ hmeas]
        simp [measureReal_def, hPS]

/-- **`≺ → 𝔼`** at an arbitrary probability law (as `lwExpTerm_prec_integral` in `Graph/LWExpTerm.lean`): from the `≺` of
`‖X_v‖` against a deterministic `R`, a polynomial envelope `N^{Kenv}` and a polynomial floor `R ≥ N^{-Kf}`: `‖𝔼 X_v‖ ≺ R`. -/
theorem BAExp14a_prec_integral [IsProbabilityMeasure P] {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop)
    {V : ℕ → Type*} (X : ∀ n, V n → Ω → ℂ) (R : ∀ n, V n → ℝ) {Kenv Kf : ℝ}
    (henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((size n : ℕ) : ℝ) ^ Kenv)
    (hfloor : ∀ᶠ n in atTop, ∀ v, ((size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v)
    (hprec : StochDomAt P size (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v)) :
    StochDomAt P size (fun n v (_ : Ω) => ‖∫ ω, X n v ω ∂P‖) (fun n v _ => R n v) := by
  refine (BAExp14a_det_iff hsize _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hDp : 0 < |Kenv| + |Kf| + 1 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp (tendsto_natCast_atTop_iff.2 hsize)).eventually (eventually_ge_atTop 2)
  filter_upwards [hprec (τ / 2) hτ2 (|Kenv| + |Kf| + 1) hDp, henv, hfloor, hC,
    hsize.eventually (eventually_ge_atTop 1)] with n hP hEnv hFl hN2 hN1
  intro v
  have hN : (1 : ℝ) ≤ ((size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hNpos : 0 < ((size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((size n : ℕ) : ℝ) with hNdef
  have hR0 : 0 ≤ R n v := (Real.rpow_nonneg hNpos.le _).trans (hFl v)
  set S : Set Ω := badSetAt size (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v) (τ / 2) n with hS
  have hPS : (P S).toReal ≤ N ^ (-(|Kenv| + |Kf| + 1)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hP
  have hin : ∀ ω, ω ∉ S → ‖X n v ω‖ ≤ N ^ (τ / 2) * R n v := by
    intro ω hω
    by_contra hc
    exact hω ⟨v, lt_of_not_ge hc⟩
  have hfm := BAExp14a_first_moment (P := P) (f := fun ω => X n v ω) (S := S)
    (c := N ^ (τ / 2) * R n v) (B := N ^ Kenv) (mul_nonneg (Real.rpow_nonneg hNpos.le _) hR0)
    (fun ω => hEnv v ω) hin
  have htail : N ^ Kenv * (P S).toReal ≤ R n v := by
    calc N ^ Kenv * (P S).toReal ≤ N ^ Kenv * N ^ (-(|Kenv| + |Kf| + 1)) :=
          mul_le_mul_of_nonneg_left hPS (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (Kenv + -(|Kenv| + |Kf| + 1)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (-Kf) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          have h1 := le_abs_self Kenv
          have h2 := le_abs_self Kf
          linarith
      _ ≤ R n v := hFl v
  have hX2 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc ‖∫ ω, X n v ω ∂P‖ ≤ ∫ ω, ‖X n v ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ N ^ (τ / 2) * R n v + N ^ Kenv * (P S).toReal := hfm
    _ ≤ N ^ (τ / 2) * R n v + R n v := add_le_add le_rfl htail
    _ ≤ N ^ (τ / 2) * R n v + N ^ (τ / 2) * R n v := by
        have : R n v ≤ N ^ (τ / 2) * R n v := by nlinarith
        linarith
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * R n v) := by
        have h3 : 0 ≤ N ^ (τ / 2) * R n v := mul_nonneg hX2 hR0
        linarith [mul_le_mul_of_nonneg_right hN2 h3]
    _ = N ^ τ * R n v := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring

/-- **A finite family of `≺`**: if `ξ k ≺ ζ` for each of the finitely many tags `k : κ`, then the family indexed by
`(k, u)` is `≺ ζ` (the union bound over `|κ|` events, `|κ| N^{-(D+1)} ≤ N^{-D}` for `N ≥ |κ|`). -/
theorem BAExp14a_prec_fin {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {κ : Type*} [Fintype κ]
    {U : ℕ → Type*} {ξ : κ → ∀ l, U l → Ω → ℝ} {ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ k, StochDomAt P size (ξ k) ζ) :
    StochDomAt P size (fun l (p : κ × U l) ω => ξ p.1 l p.2 ω) (fun l p ω => ζ l p.2 ω) := by
  intro τ hτ D hD
  have hall : ∀ᶠ l in atTop, ∀ k, P (badSetAt size (ξ k) ζ τ l) ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := by
    rw [Filter.eventually_all]
    exact fun k => h k τ hτ (D + 1) (by linarith)
  filter_upwards [hall, hsize.eventually (eventually_ge_atTop (Fintype.card κ + 2))] with l hl hN
  have hsub : badSetAt size (fun l (p : κ × U l) ω => ξ p.1 l p.2 ω) (fun l p ω => ζ l p.2 ω) τ l ⊆
      ⋃ k : κ, badSetAt size (ξ k) ζ τ l := by
    intro ω ⟨p, hp⟩
    exact Set.mem_iUnion.2 ⟨p.1, p.2, hp⟩
  have hNpos : (0 : ℝ) < (size l : ℝ) := by
    have : (0 : ℝ) < ((Fintype.card κ + 2 : ℕ) : ℝ) := by positivity
    exact lt_of_lt_of_le this (by exact_mod_cast hN)
  calc P (badSetAt size (fun l (p : κ × U l) ω => ξ p.1 l p.2 ω) (fun l p ω => ζ l p.2 ω) τ l)
      ≤ P (⋃ k : κ, badSetAt size (ξ k) ζ τ l) := measure_mono hsub
    _ ≤ ∑ k : κ, P (badSetAt size (ξ k) ζ τ l) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ k : κ, ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := Finset.sum_le_sum fun k _ => hl k
    _ = ENNReal.ofReal (Fintype.card κ * (size l : ℝ) ^ (-(D + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc : (Fintype.card κ : ℝ) ≤ (size l : ℝ) := by
          have : ((Fintype.card κ : ℕ) : ℝ) ≤ ((size l : ℕ) : ℝ) := by exact_mod_cast (by omega : Fintype.card κ ≤ size l)
          exact this
        have hp : (size l : ℝ) ^ (-D) = (size l : ℝ) * (size l : ℝ) ^ (-(D + 1)) := by
          rw [← Real.rpow_one_add' hNpos.le (by linarith)]
          congr 1; ring
        rw [hp]
        exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNpos.le _)

end Toolbox

/-! ## A2. One-index random variables: `f ≺ g` and its calculus at the law `μ` -/

section Dom

variable {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ)

/-- `f ≺ g` for a one-index random variable `f n ω` against a deterministic `g n` (the family indexed by `Unit`). -/
def BAExp14a_Dom (f : ∀ n : ℕ, sz.SeqΩ → ℝ) (g : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun _ : ℕ => Unit) (fun (n : ℕ) (_ : Unit) ω => f n ω) (fun (n : ℕ) (_ : Unit) _ => g n)

variable {sz μ}
variable (hsz : Tendsto sz.size atTop atTop)
include hsz

theorem BAExp14a_Dom.refl {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) : BAExp14a_Dom sz μ (fun n _ => g n) g :=
  StochDomAt.refl hsz fun n _ _ => hg n

theorem BAExp14a_Dom.mul {f₁ f₂ : ∀ n : ℕ, sz.SeqΩ → ℝ} {g₁ g₂ : ℕ → ℝ} (hf₂ : ∀ n ω, 0 ≤ f₂ n ω)
    (hg₁ : ∀ n, 0 ≤ g₁ n) (h₁ : BAExp14a_Dom sz μ f₁ g₁) (h₂ : BAExp14a_Dom sz μ f₂ g₂) :
    BAExp14a_Dom sz μ (fun n ω => f₁ n ω * f₂ n ω) (fun n => g₁ n * g₂ n) :=
  StochDomAt.mul hsz (fun n _ ω => hf₂ n ω) (fun n _ _ => hg₁ n) h₁ h₂

theorem BAExp14a_Dom.add {f₁ f₂ : ∀ n : ℕ, sz.SeqΩ → ℝ} {g₁ g₂ : ℕ → ℝ}
    (h₁ : BAExp14a_Dom sz μ f₁ g₁) (h₂ : BAExp14a_Dom sz μ f₂ g₂) :
    BAExp14a_Dom sz μ (fun n ω => f₁ n ω + f₂ n ω) (fun n => g₁ n + g₂ n) :=
  StochDomAt.add hsz h₁ h₂

theorem BAExp14a_Dom.of_le {f f' : ∀ n : ℕ, sz.SeqΩ → ℝ} {g : ℕ → ℝ} (hle : ∀ n ω, f n ω ≤ f' n ω)
    (h : BAExp14a_Dom sz μ f' g) : BAExp14a_Dom sz μ f g :=
  StochDomAt.of_le_left (fun n _ ω => hle n ω) h

theorem BAExp14a_Dom.mono {f : ∀ n : ℕ, sz.SeqΩ → ℝ} {g g' : ℕ → ℝ} {K : ℝ} (hK : 0 < K) (hg' : ∀ n, 0 ≤ g' n)
    (hle : ∀ᶠ n in atTop, g n ≤ K * g' n) (h : BAExp14a_Dom sz μ f g) : BAExp14a_Dom sz μ f g' :=
  BAExp14a_prec_mono hsz hK (fun n _ _ => hg' n) (hle.mono fun n hn _ _ => hn) h

theorem BAExp14a_Dom.const_mul {f : ∀ n : ℕ, sz.SeqΩ → ℝ} {g : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ n, 0 ≤ g n)
    (h : BAExp14a_Dom sz μ f g) : BAExp14a_Dom sz μ (fun n ω => c * f n ω) g :=
  StochDomAt.const_mul_left hsz hc (fun n _ _ => hg n) h

/-- A one-index domination is a domination of the same quantity indexed by anything (constant in the index). -/
theorem BAExp14a_Dom.index {f : ∀ n : ℕ, sz.SeqΩ → ℝ} {g : ℕ → ℝ} {V : ℕ → Type*} (h : BAExp14a_Dom sz μ f g) :
    PrecL sz μ (U := V) (fun n _ ω => f n ω) (fun n _ _ => g n) :=
  StochDomAt.precomp_param h (fun n (_ : V n) => ())

/-- **The master lemma `≺ → 𝔼`**: a family `Φ(n, v, ω)` with an eventual pathwise bound `‖Φ‖ ≤ Q(n, ω)` by a one-index random variable
`Q ≺ g`, `g ≤ K ζ`, a polynomial envelope `N^{Kenv}` and a polynomial floor `ζ ≥ N^{-Kf}` has `‖𝔼 Φ(n, v)‖ ≺ ζ`. -/
theorem BAExp14a_prec_int [IsProbabilityMeasure μ] {V : ℕ → Type} (Φ : ∀ n : ℕ, V n → sz.SeqΩ → ℂ)
    (Q : ∀ n : ℕ, sz.SeqΩ → ℝ) (g ζ : ℕ → ℝ) {K Kenv Kf : ℝ} (hK : 0 < K) (hζ0 : ∀ n, 0 ≤ ζ n)
    (hQ : ∀ᶠ n in atTop, ∀ v ω, ‖Φ n v ω‖ ≤ Q n ω) (hDom : BAExp14a_Dom sz μ Q g) (hg : ∀ᶠ n in atTop, g n ≤ K * ζ n)
    (henv : ∀ᶠ n in atTop, ∀ v ω, ‖Φ n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hfloor : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ ζ n) :
    PrecL sz μ (U := V) (fun n v _ => ‖∫ ω, Φ n v ω ∂μ‖) (fun n _ _ => ζ n) := by
  unfold PrecL
  refine BAExp14a_prec_integral hsz Φ (fun n _ => ζ n) henv (hfloor.mono fun n h _ => h) ?_
  refine BAExp14a_prec_mono hsz hK (fun n _ _ => hζ0 n) (hg.mono fun n hn _ _ => hn) ?_
  refine BAExp14a_prec_of_bad hDom fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hQ] with n hn ω hω
  obtain ⟨v, hv⟩ := hω
  exact ⟨(), lt_of_lt_of_le hv (hn v ω)⟩

end Dom

/-! ## A3. The fine-level Ward identity (as `lwExpTerm4_ward_*` in `Graph/LWExpTerm4.lean`) -/

section FineWard

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem BAExp14a_green_conj {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) :
    (green H z)ᴴ = green H ((starRingEnd ℂ) z) := by
  have hH' : Hᴴ = H := hH
  simp only [green, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH', Complex.star_def]

/-- `G - G^* = 2iη G^* G = 2iη G G^*` at one entry. -/
private theorem BAExp14a_ward_gram {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (green H z - (green H z)ᴴ = (2 * Complex.I * (z.im : ℂ)) • ((green H z)ᴴ * green H z)) ∧
    (green H z - (green H z)ᴴ = (2 * Complex.I * (z.im : ℂ)) • (green H z * (green H z)ᴴ)) := by
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH (z := (starRingEnd ℂ) z) (by simpa using hz)
  rw [BAExp14a_green_conj hH]
  refine ⟨green_sub_green_conj' hu hu', ?_⟩
  rw [green_sub_green hu hu', Complex.sub_conj]
  congr 1
  push_cast
  ring

/-- **Row Ward identity**: `Im z · Σ_y |G_{xy}|² = Im G_{xx}`. -/
theorem BAExp14a_ward_row {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    z.im * ∑ y, ‖green H z x y‖ ^ 2 = (green H z x x).im := by
  have h := congrFun (congrFun (BAExp14a_ward_gram hH hz).2 x) x
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def] at h
  have h1 : ∑ y, green H z x y * (starRingEnd ℂ) (green H z x y) = ((∑ y, ‖green H z x y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.mul_conj', ← Complex.ofReal_pow]
  rw [h1, Complex.sub_conj] at h
  have hI : (2 * Complex.I) ≠ 0 := by simp
  generalize (∑ y, ‖green H z x y‖ ^ 2 : ℝ) = S at h ⊢
  have h3 : ((z.im * S : ℝ) : ℂ) = ((green H z x x).im : ℂ) := by
    apply mul_left_cancel₀ hI
    push_cast at h ⊢
    linear_combination (-1 : ℂ) * h
  exact_mod_cast h3

/-- **Column Ward identity**: `Im z · Σ_y |G_{yx}|² = Im G_{xx}`. -/
theorem BAExp14a_ward_col {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    z.im * ∑ y, ‖green H z y x‖ ^ 2 = (green H z x x).im := by
  have h := congrFun (congrFun (BAExp14a_ward_gram hH hz).1 x) x
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def] at h
  have h1 : ∑ y, (starRingEnd ℂ) (green H z y x) * green H z y x = ((∑ y, ‖green H z y x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [h1, Complex.sub_conj] at h
  have hI : (2 * Complex.I) ≠ 0 := by simp
  generalize (∑ y, ‖green H z y x‖ ^ 2 : ℝ) = S at h ⊢
  have h3 : ((z.im * S : ℝ) : ℂ) = ((green H z x x).im : ℂ) := by
    apply mul_left_cancel₀ hI
    push_cast at h ⊢
    linear_combination (-1 : ℂ) * h
  exact_mod_cast h3

/-- `|G_{xx}| ≤ (Im z)⁻¹` (`|G_{xx}|² ≤ Σ_y |G_{xy}|² = Im G_{xx}/η ≤ |G_{xx}|/η`). -/
theorem BAExp14a_green_diag_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (x : ι) :
    ‖green H z x x‖ ≤ (z.im)⁻¹ := by
  have h := BAExp14a_ward_row hH hz.ne' x
  have h1 : ‖green H z x x‖ ^ 2 ≤ ∑ y, ‖green H z x y‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖green H z x y‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  have h2 : (green H z x x).im ≤ ‖green H z x x‖ := Complex.im_le_norm _
  set g : ℝ := ‖green H z x x‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have h3 : z.im * g ^ 2 ≤ g := by
    calc z.im * g ^ 2 ≤ z.im * ∑ y, ‖green H z x y‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hz.le
      _ = _ := h
      _ ≤ g := h2
  by_contra hcon
  push Not at hcon
  have h4 : 1 < z.im * g := by
    have := mul_lt_mul_of_pos_left hcon hz
    rwa [mul_inv_cancel₀ hz.ne'] at this
  nlinarith

end FineWard

/-! ## A3b. The comparison of the dominating functions with `(1 - t)⁻¹ B^{5/2}` (pure arithmetic) -/

section Compare

/-- The dominating function of `J_m = a² K₃ (1 + b)/η`: `(K₃ η⁻¹) (B² (1 + B^{1/2}))`. -/
def BAExp14a_gJ (K3 ηi B : ℝ) : ℝ := (K3 * ηi) * ((B * B) * (1 + B ^ (1 / 2 : ℝ)))

theorem BAExp14a_gJ_le {K3 ηi κi ω1 B : ℝ} (hB0 : 0 < B) (hB2 : B ≤ 2) (hK3 : 0 ≤ K3) (hηi : ηi ≤ κi * ω1)
    (hηi0 : 0 ≤ ηi) (hκ0 : 0 ≤ κi) (hω1 : 1 ≤ ω1) :
    BAExp14a_gJ K3 ηi B ≤ (3 * K3 * κi) * (ω1 * (B * B)) := by
  unfold BAExp14a_gJ
  have hs : B ^ (1 / 2 : ℝ) ≤ 2 := by
    have h1 : (B ^ (1 / 2 : ℝ)) ^ 2 = B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]; norm_num
    have h0 : 0 ≤ B ^ (1 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
    nlinarith
  have hs0 : 0 ≤ B ^ (1 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
  have hBB : 0 ≤ B * B := by positivity
  calc (K3 * ηi) * ((B * B) * (1 + B ^ (1 / 2 : ℝ))) ≤ (K3 * (κi * ω1)) * ((B * B) * 3) := by
        gcongr; linarith
    _ = (3 * K3 * κi) * (ω1 * (B * B)) := by ring

theorem BAExp14a_rpow_arith {B : ℝ} (hB : 0 < B) :
    B ^ (1 / 2 : ℝ) * (B * B) = B ^ (5 / 2 : ℝ) ∧ B ^ (1 / 2 : ℝ) * B = B ^ (3 / 2 : ℝ) ∧
      B * (B ^ (1 / 2 : ℝ) * B) = B ^ (5 / 2 : ℝ) ∧ B * (B * B) = B ^ (5 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by
  have h1 : B = B ^ (1 : ℝ) := (Real.rpow_one B).symm
  have h2 : B * B = B ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hB, Real.rpow_one]
  have h3 : B ^ (1 / 2 : ℝ) * B = B ^ (3 / 2 : ℝ) := by
    calc B ^ (1 / 2 : ℝ) * B = B ^ (1 / 2 : ℝ) * B ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = B ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hB]; norm_num
  refine ⟨?_, h3, ?_, ?_⟩
  · rw [h2, ← Real.rpow_add hB]; norm_num
  · rw [h3]
    calc B * B ^ (3 / 2 : ℝ) = B ^ (1 : ℝ) * B ^ (3 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = B ^ (5 / 2 : ℝ) := by rw [← Real.rpow_add hB]; norm_num
  · rw [h2]
    calc B * B ^ (2 : ℝ) = B ^ (1 : ℝ) * B ^ (2 : ℝ) := by rw [Real.rpow_one]
      _ = B ^ (3 : ℝ) := by rw [← Real.rpow_add hB]; norm_num
      _ = B ^ (5 / 2 : ℝ) * B ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hB]; norm_num

/-- **The two comparisons** with `ζ = ω₁ B^{5/2}` (`ω₁ = (1 - t)⁻¹ ≥ 1`): the dominating functions of `F^Ǧ` and of `F^M`. -/
theorem BAExp14a_cmp {B Wd c1 K3 SC ηi κi ω1 : ℝ} (hB0 : 0 < B) (hB2 : B ≤ 2) (hK3 : 0 ≤ K3) (hSC : 0 ≤ SC)
    (hWd : Wd ≤ c1 * B) (hWd0 : 0 ≤ Wd) (hc1 : 0 ≤ c1) (hηi : ηi ≤ κi * ω1) (hηi0 : 0 ≤ ηi) (hκ0 : 0 ≤ κi)
    (hω1 : 1 ≤ ω1) :
    (B ^ (1 / 2 : ℝ) * BAExp14a_gJ K3 ηi B + Wd * SC * (B ^ (1 / 2 : ℝ) * B)) ≤
      (3 * K3 * κi + c1 * SC) * (ω1 * B ^ (5 / 2 : ℝ)) ∧
    Wd * (1 * BAExp14a_gJ K3 ηi B) ≤ (6 * c1 * K3 * κi) * (ω1 * B ^ (5 / 2 : ℝ)) := by
  obtain ⟨r1, r2, r3, r4⟩ := BAExp14a_rpow_arith hB0
  have hgJ := BAExp14a_gJ_le hB0 hB2 hK3 hηi hηi0 hκ0 hω1
  have hs0 : 0 ≤ B ^ (1 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
  have hs : B ^ (1 / 2 : ℝ) ≤ 2 := by
    have h1 : (B ^ (1 / 2 : ℝ)) ^ 2 = B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]; norm_num
    nlinarith
  have hR0 : 0 ≤ B ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0.le _
  have hω0 : 0 ≤ ω1 := by linarith
  have hBB : 0 ≤ B * B := by positivity
  have hgJ0 : 0 ≤ BAExp14a_gJ K3 ηi B := by
    unfold BAExp14a_gJ; positivity
  refine ⟨?_, ?_⟩
  · have e1 : B ^ (1 / 2 : ℝ) * BAExp14a_gJ K3 ηi B ≤ (3 * K3 * κi) * (ω1 * B ^ (5 / 2 : ℝ)) := by
      calc B ^ (1 / 2 : ℝ) * BAExp14a_gJ K3 ηi B ≤ B ^ (1 / 2 : ℝ) * ((3 * K3 * κi) * (ω1 * (B * B))) :=
            mul_le_mul_of_nonneg_left hgJ hs0
        _ = (3 * K3 * κi) * (ω1 * (B ^ (1 / 2 : ℝ) * (B * B))) := by ring
        _ = _ := by rw [r1]
    have e2 : Wd * SC * (B ^ (1 / 2 : ℝ) * B) ≤ (c1 * SC) * (ω1 * B ^ (5 / 2 : ℝ)) := by
      calc Wd * SC * (B ^ (1 / 2 : ℝ) * B) ≤ (c1 * B) * SC * (B ^ (1 / 2 : ℝ) * B) := by gcongr
        _ = (c1 * SC) * (B * (B ^ (1 / 2 : ℝ) * B)) := by ring
        _ = (c1 * SC) * B ^ (5 / 2 : ℝ) := by rw [r3]
        _ ≤ (c1 * SC) * (ω1 * B ^ (5 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith
    linarith
  · calc Wd * (1 * BAExp14a_gJ K3 ηi B) ≤ (c1 * B) * (1 * ((3 * K3 * κi) * (ω1 * (B * B)))) := by gcongr
      _ = (3 * c1 * K3 * κi) * (ω1 * (B * (B * B))) := by ring
      _ = (3 * c1 * K3 * κi) * (ω1 * (B ^ (5 / 2 : ℝ) * B ^ (1 / 2 : ℝ))) := by rw [r4]
      _ ≤ (3 * c1 * K3 * κi) * (ω1 * (B ^ (5 / 2 : ℝ) * 2)) := by gcongr
      _ = (6 * c1 * K3 * κi) * (ω1 * B ^ (5 / 2 : ℝ)) := by ring

end Compare

/-! ## A4. The block combinatorics of the fine lattice and the frame bounds -/

section Lattice

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- A function of the block coordinate summed over the fine lattice: `Σ_x f([x]) = W^d Σ_c f(c)`. -/
theorem BAExp14a_sum_blk (f : Zd d L → ℝ) :
    ∑ x : Idx d L W, f (split d L W x).1 = (W : ℝ) ^ d * ∑ c : Zd d L, f c := by
  have h : ∑ x : Idx d L W, f (split d L W x).1 =
      ∑ x : Idx d L W, (fun p : Vtx d L W => f p.1) (splitEquiv d L W x) := rfl
  rw [h, Equiv.sum_comp (splitEquiv d L W) (fun p : Vtx d L W => f p.1), Fintype.sum_prod_type]
  simp [Finset.mul_sum]

/-- For every `x` there is exactly one `y` in the block `[b]` with the offset of `x`. -/
theorem BAExp14a_offset_count (b : Zd d L) (x : Idx d L W) :
    ∑ y ∈ Iblk d L W b, (if (split d L W x).2 = (split d L W y).2 then (1 : ℝ) else 0) = 1 := by
  have h : ∑ y ∈ Iblk d L W b, (if (split d L W x).2 = (split d L W y).2 then (1 : ℝ) else 0) =
      ∑ y : Idx d L W, (fun p : Vtx d L W => if p.1 = b then (if (split d L W x).2 = p.2 then (1 : ℝ) else 0) else 0)
        (splitEquiv d L W y) := by
    unfold Iblk
    rw [Finset.sum_filter]
    rfl
  rw [h, Equiv.sum_comp (splitEquiv d L W)
    (fun p : Vtx d L W => if p.1 = b then (if (split d L W x).2 = p.2 then (1 : ℝ) else 0) else 0),
    Fintype.sum_prod_type]
  simp

/-- The pairs `(x, y) ∈ [a] × [b]` of the same offset number `W^d`. -/
theorem BAExp14a_pair_count (a b : Zd d L) :
    ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, (if (split d L W x).2 = (split d L W y).2 then (1 : ℝ) else 0) =
      (W : ℝ) ^ d := by
  simp only [BAExp14a_offset_count, Finset.sum_const, nsmul_eq_mul, mul_one, card_Iblk]
  push_cast
  ring

/-- **The frame** of the families: `W^{-2d} Σ_{x ∈ [a], y ∈ [b]} tl(x,y) J(x,y)`. -/
def BAExp14a_frame (a b : Zd d L) (tl J : Idx d L W → Idx d L W → ℂ) : ℂ :=
  ((((W : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, tl x y * J x y

theorem BAExp14a_frame_le (a b : Zd d L) (tl J : Idx d L W → Idx d L W → ℂ) (w : Idx d L W → Idx d L W → ℝ)
    (hw : ∀ x y, ‖tl x y * J x y‖ ≤ w x y) :
    ‖BAExp14a_frame a b tl J‖ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, w x y := by
  unfold BAExp14a_frame
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hw x y)

/-- **Frame bound without support**: `|tl| ≤ τ`, `|J| ≤ Jm` give `|frame| ≤ τ Jm`. -/
theorem BAExp14a_frame_le_full (a b : Zd d L) (tl J : Idx d L W → Idx d L W → ℂ) {τ Jm : ℝ}
    (htl : ∀ x y, ‖tl x y‖ ≤ τ) (hJ : ∀ x y, ‖J x y‖ ≤ Jm) (hτ : 0 ≤ τ) (hJm : 0 ≤ Jm) :
    ‖BAExp14a_frame a b tl J‖ ≤ τ * Jm := by
  refine (BAExp14a_frame_le a b tl J (fun _ _ => τ * Jm) fun x y => ?_).trans ?_
  · rw [norm_mul]
    exact mul_le_mul (htl x y) (hJ x y) (norm_nonneg _) hτ
  · simp only [Finset.sum_const, nsmul_eq_mul, card_Iblk]
    have hW : (0 : ℝ) < (W : ℝ) ^ d := by
      have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
      positivity
    push_cast
    apply le_of_eq
    field_simp

/-- **Frame bound with offset support**: `tl · J` vanishes unless `x, y` have the same offset; then `|frame| ≤ W^{-d} τ Jm`. -/
theorem BAExp14a_frame_le_diag (a b : Zd d L) (tl J : Idx d L W → Idx d L W → ℂ) {τ Jm : ℝ}
    (htl : ∀ x y, ‖tl x y‖ ≤ τ) (hJ : ∀ x y, ‖J x y‖ ≤ Jm) (hτ : 0 ≤ τ) (hJm : 0 ≤ Jm)
    (hs : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → tl x y * J x y = 0) :
    ‖BAExp14a_frame a b tl J‖ ≤ ((W : ℝ) ^ d)⁻¹ * (τ * Jm) := by
  refine (BAExp14a_frame_le a b tl J
    (fun x y => if (split d L W x).2 = (split d L W y).2 then τ * Jm else 0) fun x y => ?_).trans ?_
  · by_cases h : (split d L W x).2 = (split d L W y).2
    · simp only [h, ↓reduceIte]
      rw [norm_mul]
      exact mul_le_mul (htl x y) (hJ x y) (norm_nonneg _) hτ
    · simp only [h, ↓reduceIte]
      rw [hs x y h, norm_zero]
  · have h1 : ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b,
        (if (split d L W x).2 = (split d L W y).2 then τ * Jm else 0) = (τ * Jm) * (W : ℝ) ^ d := by
      rw [← BAExp14a_pair_count (W := W) a b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> simp
    rw [h1]
    have hW : (0 : ℝ) < (W : ℝ) ^ d := by
      have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
      positivity
    apply le_of_eq
    field_simp

end Lattice

/-! ## A5. The pathwise bounds of the sums `J(x,y)` of the six families

Fine-lattice absolute-value estimates, model-free: `X : Zd d L → ℂ` the block averages `X_c = tr(Ǧ E_c)` (`|X_c| ≤ a`), `Mm` the
fine `M` (entries `≤ 1`, row and column sums `≤ CM`, supported on one offset), `Gm = Mm + Gc` the resolvent (`|Gm| ≤ g`,
Ward), `Wk` the weight kernel `W^{(k)}` (`W^{(0)} = 1`, `W^{(1)} = W - 1`) with column sums `≤ S`. -/

section Path

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `|Σ_α X_{[α]} T(α)| ≤ a Σ_α |T(α)|`. -/
theorem BAExp14a_sum_X_le (X : Zd d L → ℂ) (T : Idx d L W → ℂ) {a : ℝ} (ha : ∀ c, ‖X c‖ ≤ a) :
    ‖∑ α, X (split d L W α).1 * T α‖ ≤ a * ∑ α, ‖T α‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)

/-- The kernel `T(x,y,α) = Σ_β Wk_{αβ} M_{xβ} M_{βy}` of `F_MM` (`Wk = 1`) and `F_T1` (`Wk = W - 1`): `Σ_α |T| ≤ S · CM`. -/
theorem BAExp14a_T_MM_l1 (Wk Mm : Idx d L W → Idx d L W → ℂ) {S CM : ℝ}
    (hWk : ∀ β, ∑ α, ‖Wk α β‖ ≤ S) (hM1 : ∀ x y, ‖Mm x y‖ ≤ 1) (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM) (x y : Idx d L W) :
    ∑ α, ‖∑ β, Wk α β * Mm x β * Mm β y‖ ≤ S * CM := by
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hWk 0)
  calc ∑ α, ‖∑ β, Wk α β * Mm x β * Mm β y‖
      ≤ ∑ α, ∑ β, ‖Wk α β‖ * ‖Mm x β‖ := by
        refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
        rw [norm_mul, norm_mul]
        have := hM1 β y
        have h0 : 0 ≤ ‖Wk α β‖ * ‖Mm x β‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        nlinarith
    _ = ∑ β, (∑ α, ‖Wk α β‖) * ‖Mm x β‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ β, S * ‖Mm x β‖ :=
        Finset.sum_le_sum fun β _ => mul_le_mul_of_nonneg_right (hWk β) (norm_nonneg _)
    _ = S * ∑ β, ‖Mm x β‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ S * CM := mul_le_mul_of_nonneg_left (hMr x) hS0

/-- `T(x,y,α) = 0` for every `α` unless `x`, `y` have the same offset (`M` is supported on one offset). -/
theorem BAExp14a_T_MM_supp (Wk Mm : Idx d L W → Idx d L W → ℂ)
    (hMo : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → Mm x y = 0) (x y : Idx d L W)
    (hxy : (split d L W x).2 ≠ (split d L W y).2) (α : Idx d L W) :
    ∑ β, Wk α β * Mm x β * Mm β y = 0 := by
  refine Finset.sum_eq_zero fun β _ => ?_
  by_cases h : (split d L W x).2 = (split d L W β).2
  · have h2 : (split d L W β).2 ≠ (split d L W y).2 := fun h' => hxy (h.trans h')
    rw [hMo β y h2, mul_zero]
  · rw [hMo x β h]
    simp

/-- **Schur / AM-GM**: `Σ_{w,γ} |M_{wγ}| v_γ u_w ≤ (CM/2)(Σ_γ v_γ² + Σ_w u_w²)` (row and column sums of `|M|` at most `CM`). -/
theorem BAExp14a_schur (Mm : Idx d L W → Idx d L W → ℂ) {CM : ℝ} (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM)
    (hMc : ∀ y, ∑ x, ‖Mm x y‖ ≤ CM) (u v : Idx d L W → ℝ) :
    ∑ w, ∑ γ, ‖Mm w γ‖ * (v γ * u w) ≤ CM / 2 * (∑ γ, v γ ^ 2 + ∑ w, u w ^ 2) := by
  have h1 : ∀ w γ, ‖Mm w γ‖ * (v γ * u w) ≤ ‖Mm w γ‖ * (v γ ^ 2 / 2) + ‖Mm w γ‖ * (u w ^ 2 / 2) := by
    intro w γ
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    nlinarith [sq_nonneg (v γ - u w)]
  calc ∑ w, ∑ γ, ‖Mm w γ‖ * (v γ * u w)
      ≤ ∑ w, ∑ γ, (‖Mm w γ‖ * (v γ ^ 2 / 2) + ‖Mm w γ‖ * (u w ^ 2 / 2)) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun γ _ => h1 w γ
    _ = (∑ γ, (∑ w, ‖Mm w γ‖) * (v γ ^ 2 / 2)) + ∑ w, (∑ γ, ‖Mm w γ‖) * (u w ^ 2 / 2) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun γ _ => (Finset.sum_mul _ _ _).symm
        · exact Finset.sum_congr rfl fun w _ => (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ γ, CM * (v γ ^ 2 / 2)) + ∑ w, CM * (u w ^ 2 / 2) := by
        refine add_le_add (Finset.sum_le_sum fun γ _ => ?_) (Finset.sum_le_sum fun w _ => ?_)
        · exact mul_le_mul_of_nonneg_right (hMc γ) (by positivity)
        · exact mul_le_mul_of_nonneg_right (hMr w) (by positivity)
    _ = CM / 2 * (∑ γ, v γ ^ 2 + ∑ w, u w ^ 2) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-- `J_T3A(x,y) = Σ_α X_{[α]} Σ_{w,γ} Wk_{αw} M_{wγ} (t X_{[γ]}) G_{γy} Ǧ_{xw}`:
`|J| ≤ a² S (CM/2) (Σ_γ |G_{γy}|² + Σ_w |Ǧ_{xw}|²)`. -/
theorem BAExp14a_J_T3A_le (X : Zd d L → ℂ) (Wk Mm Gm Gc : Idx d L W → Idx d L W → ℂ) {a S CM : ℝ} {t : ℝ}
    (ha : ∀ c, ‖X c‖ ≤ a) (ht : |t| ≤ 1) (hWk : ∀ β, ∑ α, ‖Wk α β‖ ≤ S)
    (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM) (hMc : ∀ y, ∑ x, ‖Mm x y‖ ≤ CM) (x y : Idx d L W) :
    ‖∑ α, X (split d L W α).1 * ∑ w, ∑ γ, Wk α w * Mm w γ * ((t : ℂ) * X (split d L W γ).1) * Gm γ y * Gc x w‖ ≤
      a * (a * (S * (CM / 2 * (∑ γ, ‖Gm γ y‖ ^ 2 + ∑ w, ‖Gc x w‖ ^ 2)))) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hWk 0)
  have hsch := BAExp14a_schur Mm hMr hMc (fun w => ‖Gc x w‖) (fun γ => ‖Gm γ y‖)
  refine (BAExp14a_sum_X_le X _ ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ha0
  -- Σ_α |Σ_{w,γ} ...| ≤ a S Σ_{w,γ} |M_{wγ}| |G_{γy}| |Ǧ_{xw}|
  calc ∑ α, ‖∑ w, ∑ γ, Wk α w * Mm w γ * ((t : ℂ) * X (split d L W γ).1) * Gm γ y * Gc x w‖
      ≤ ∑ α, ∑ w, (‖Wk α w‖ * (a * ∑ γ, ‖Mm w γ‖ * (‖Gm γ y‖ * ‖Gc x w‖))) := by
        refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun γ _ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hX := ha (split d L W γ).1
        have h1 : |t| * ‖X (split d L W γ).1‖ ≤ a := by
          calc |t| * ‖X (split d L W γ).1‖ ≤ 1 * a := mul_le_mul ht hX (norm_nonneg _) zero_le_one
            _ = a := one_mul _
        have h2 : 0 ≤ ‖Wk α w‖ * ‖Mm w γ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have h3 : 0 ≤ ‖Gm γ y‖ * ‖Gc x w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc ‖Wk α w‖ * ‖Mm w γ‖ * (|t| * ‖X (split d L W γ).1‖) * ‖Gm γ y‖ * ‖Gc x w‖
            = (‖Wk α w‖ * ‖Mm w γ‖) * (|t| * ‖X (split d L W γ).1‖) * (‖Gm γ y‖ * ‖Gc x w‖) := by ring
          _ ≤ (‖Wk α w‖ * ‖Mm w γ‖) * a * (‖Gm γ y‖ * ‖Gc x w‖) := by
              gcongr
          _ = ‖Wk α w‖ * (a * (‖Mm w γ‖ * (‖Gm γ y‖ * ‖Gc x w‖))) := by ring
    _ = ∑ w, (∑ α, ‖Wk α w‖) * (a * ∑ γ, ‖Mm w γ‖ * (‖Gm γ y‖ * ‖Gc x w‖)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ w, S * (a * ∑ γ, ‖Mm w γ‖ * (‖Gm γ y‖ * ‖Gc x w‖)) := by
        refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hWk w) ?_
        exact mul_nonneg ha0 (Finset.sum_nonneg fun γ _ => mul_nonneg (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = a * (S * ∑ w, ∑ γ, ‖Mm w γ‖ * (‖Gm γ y‖ * ‖Gc x w‖)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ a * (S * (CM / 2 * (∑ γ, ‖Gm γ y‖ ^ 2 + ∑ w, ‖Gc x w‖ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsch hS0) ha0

/-- `J_C1(x,y) = Σ_α X_{[α]} Σ_{α'} M_{xα} (t X_{[α']}) M_{αα'} G_{α'y}`: `|J| ≤ a² g CM²`. -/
theorem BAExp14a_J_C1_le (X : Zd d L → ℂ) (Mm Gm : Idx d L W → Idx d L W → ℂ) {a g CM : ℝ} {t : ℝ}
    (ha : ∀ c, ‖X c‖ ≤ a) (ht : |t| ≤ 1) (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM) (hG : ∀ x y, ‖Gm x y‖ ≤ g)
    (x y : Idx d L W) :
    ‖∑ α, X (split d L W α).1 * ∑ α', Mm x α * ((t : ℂ) * X (split d L W α').1) * Mm α α' * Gm α' y‖ ≤
      a * (a * (g * (CM * CM))) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hG 0 0)
  have hCM0 : 0 ≤ CM := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hMr 0)
  refine (BAExp14a_sum_X_le X _ ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ha0
  calc ∑ α, ‖∑ α', Mm x α * ((t : ℂ) * X (split d L W α').1) * Mm α α' * Gm α' y‖
      ≤ ∑ α, ‖Mm x α‖ * (a * (g * ∑ α', ‖Mm α α'‖)) := by
        refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun α' _ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hX := ha (split d L W α').1
        have h1 : |t| * ‖X (split d L W α').1‖ ≤ a := by
          calc |t| * ‖X (split d L W α').1‖ ≤ 1 * a := mul_le_mul ht hX (norm_nonneg _) zero_le_one
            _ = a := one_mul _
        have := hG α' y
        calc ‖Mm x α‖ * (|t| * ‖X (split d L W α').1‖) * ‖Mm α α'‖ * ‖Gm α' y‖
            ≤ ‖Mm x α‖ * a * ‖Mm α α'‖ * g := by gcongr
          _ = ‖Mm x α‖ * (a * (g * ‖Mm α α'‖)) := by ring
    _ ≤ ∑ α, ‖Mm x α‖ * (a * (g * CM)) := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMr α) hg0) ha0
    _ = (∑ α, ‖Mm x α‖) * (a * (g * CM)) := (Finset.sum_mul _ _ _).symm
    _ ≤ CM * (a * (g * CM)) := mul_le_mul_of_nonneg_right (hMr x) (by positivity)
    _ = a * (g * (CM * CM)) := by ring

/-- `J_C2(x,y) = Σ_α X_{[α]} Σ_{α'} (t X_{[α']}) M_{xα'} G_{α'α} M_{αy}`: `|J| ≤ a² g CM²`. -/
theorem BAExp14a_J_C2_le (X : Zd d L → ℂ) (Mm Gm : Idx d L W → Idx d L W → ℂ) {a g CM : ℝ} {t : ℝ}
    (ha : ∀ c, ‖X c‖ ≤ a) (ht : |t| ≤ 1) (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM) (hMc : ∀ y, ∑ x, ‖Mm x y‖ ≤ CM)
    (hG : ∀ x y, ‖Gm x y‖ ≤ g) (x y : Idx d L W) :
    ‖∑ α, X (split d L W α).1 * ∑ α', ((t : ℂ) * X (split d L W α').1) * Mm x α' * Gm α' α * Mm α y‖ ≤
      a * (a * (g * (CM * CM))) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hg0 : 0 ≤ g := (norm_nonneg _).trans (hG 0 0)
  have hCM0 : 0 ≤ CM := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hMr 0)
  refine (BAExp14a_sum_X_le X _ ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ha0
  calc ∑ α, ‖∑ α', ((t : ℂ) * X (split d L W α').1) * Mm x α' * Gm α' α * Mm α y‖
      ≤ ∑ α, ‖Mm α y‖ * (a * (g * ∑ α', ‖Mm x α'‖)) := by
        refine Finset.sum_le_sum fun α _ => (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun α' _ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hX := ha (split d L W α').1
        have h1 : |t| * ‖X (split d L W α').1‖ ≤ a := by
          calc |t| * ‖X (split d L W α').1‖ ≤ 1 * a := mul_le_mul ht hX (norm_nonneg _) zero_le_one
            _ = a := one_mul _
        have := hG α' α
        calc |t| * ‖X (split d L W α').1‖ * ‖Mm x α'‖ * ‖Gm α' α‖ * ‖Mm α y‖
            ≤ a * ‖Mm x α'‖ * g * ‖Mm α y‖ := by gcongr
          _ = ‖Mm α y‖ * (a * (g * ‖Mm x α'‖)) := by ring
    _ ≤ ∑ α, ‖Mm α y‖ * (a * (g * CM)) := by
        refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMr x) hg0) ha0
    _ = (∑ α, ‖Mm α y‖) * (a * (g * CM)) := (Finset.sum_mul _ _ _).symm
    _ ≤ CM * (a * (g * CM)) := mul_le_mul_of_nonneg_right (hMc y) (by positivity)
    _ = a * (g * (CM * CM)) := by ring

/-- **`J_T3A` with the Ward identity**: `|Σ_γ |G_{γy}|²| ≤ (1 + b)/η` and `Σ_w |Ǧ_{xw}|² ≤ 2(1 + b)/η + 2`, so
`|J_T3A| ≤ a² · (5/2) S CM · (1 + b)/η`.  Hypotheses: `G = M + Ǧ`, `|Ǧ| ≤ b`, `|M| ≤ 1`, `Σ_y |M_{xy}|² ≤ 1`, the Ward
identities `η Σ_y |G_{xy}|² = Im G_{xx} = η Σ_y |G_{yx}|²`, `0 < η ≤ 1`. -/
theorem BAExp14a_J_T3A_bd (X : Zd d L → ℂ) (Wk Mm Gm Gc : Idx d L W → Idx d L W → ℂ) {a b S CM t η : ℝ}
    (ha : ∀ c, ‖X c‖ ≤ a) (ht : |t| ≤ 1) (hWk : ∀ β, ∑ α, ‖Wk α β‖ ≤ S)
    (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM) (hMc : ∀ y, ∑ x, ‖Mm x y‖ ≤ CM) (hM1 : ∀ x y, ‖Mm x y‖ ≤ 1)
    (hMsq : ∀ x, ∑ y, ‖Mm x y‖ ^ 2 ≤ 1) (hG : ∀ x y, Gm x y = Mm x y + Gc x y) (hb : ∀ x y, ‖Gc x y‖ ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) (hwr : ∀ x, η * ∑ y, ‖Gm x y‖ ^ 2 = (Gm x x).im)
    (hwc : ∀ y, η * ∑ x, ‖Gm x y‖ ^ 2 = (Gm y y).im) (x y : Idx d L W) :
    ‖∑ α, X (split d L W α).1 * ∑ w, ∑ γ, Wk α w * Mm w γ * ((t : ℂ) * X (split d L W γ).1) * Gm γ y * Gc x w‖ ≤
      a * (a * ((5 / 2 * S * CM) * ((1 + b) / η))) := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hWk 0)
  have hCM0 : 0 ≤ CM := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hMr 0)
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hdiag : ∀ v, ‖Gm v v‖ ≤ 1 + b := fun v => by
    rw [hG v v]
    exact (norm_add_le _ _).trans (add_le_add (hM1 v v) (hb v v))
  have hcol : ∑ γ, ‖Gm γ y‖ ^ 2 ≤ (1 + b) / η := by
    rw [le_div_iff₀ hη, mul_comm]
    calc η * ∑ γ, ‖Gm γ y‖ ^ 2 = (Gm y y).im := hwc y
      _ ≤ ‖Gm y y‖ := Complex.im_le_norm _
      _ ≤ 1 + b := hdiag y
  have hrow : ∑ w, ‖Gm x w‖ ^ 2 ≤ (1 + b) / η := by
    rw [le_div_iff₀ hη, mul_comm]
    calc η * ∑ w, ‖Gm x w‖ ^ 2 = (Gm x x).im := hwr x
      _ ≤ ‖Gm x x‖ := Complex.im_le_norm _
      _ ≤ 1 + b := hdiag x
  have hGc : ∑ w, ‖Gc x w‖ ^ 2 ≤ 2 * ((1 + b) / η) + 2 := by
    calc ∑ w, ‖Gc x w‖ ^ 2 ≤ ∑ w, (2 * ‖Gm x w‖ ^ 2 + 2 * ‖Mm x w‖ ^ 2) := by
          refine Finset.sum_le_sum fun w _ => ?_
          have h1 : Gc x w = Gm x w - Mm x w := by rw [hG x w]; ring
          have h2 : ‖Gc x w‖ ≤ ‖Gm x w‖ + ‖Mm x w‖ := by
            rw [h1]; exact norm_sub_le _ _
          nlinarith [norm_nonneg (Gc x w), norm_nonneg (Gm x w), norm_nonneg (Mm x w),
            sq_nonneg (‖Gm x w‖ - ‖Mm x w‖)]
      _ = 2 * ∑ w, ‖Gm x w‖ ^ 2 + 2 * ∑ w, ‖Mm x w‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * ((1 + b) / η) + 2 * 1 := by gcongr; exact hMsq x
      _ = 2 * ((1 + b) / η) + 2 := by ring
  have hone : (1 : ℝ) ≤ (1 + b) / η := by
    rw [le_div_iff₀ hη]; linarith
  have hsum : ∑ γ, ‖Gm γ y‖ ^ 2 + ∑ w, ‖Gc x w‖ ^ 2 ≤ 5 * ((1 + b) / η) := by linarith
  refine (BAExp14a_J_T3A_le X Wk Mm Gm Gc ha ht hWk hMr hMc x y).trans ?_
  have hk : S * (CM / 2 * (∑ γ, ‖Gm γ y‖ ^ 2 + ∑ w, ‖Gc x w‖ ^ 2)) ≤ (5 / 2 * S * CM) * ((1 + b) / η) := by
    calc S * (CM / 2 * (∑ γ, ‖Gm γ y‖ ^ 2 + ∑ w, ‖Gc x w‖ ^ 2)) ≤ S * (CM / 2 * (5 * ((1 + b) / η))) := by
          gcongr
      _ = (5 / 2 * S * CM) * ((1 + b) / η) := by ring
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk ha0) ha0

/-- **The Neumann bound for the average**: if `e = t M⁺ e + R` with `Σ_b |M^{(B)}_{cb}|² = 1`, `0 ≤ t < 1` and `|R| ≤ r`, then
`|e_c| ≤ r/(1 - t)` (`e_{c*} = max`: `|e| ≤ t |e| + r`). -/
theorem BAExp14a_neumann {ι : Type*} [Fintype ι] [Nonempty ι] (MB : ι → ι → ℂ) (e R : ι → ℂ) {t r : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hsq : ∀ c, ∑ b, ‖MB c b‖ ^ 2 = 1)
    (heq : ∀ c, e c = (t : ℂ) * ∑ b, (MB c b) ^ 2 * e b + R c) (hR : ∀ c, ‖R c‖ ≤ r) (c : ι) :
    ‖e c‖ ≤ r / (1 - t) := by
  obtain ⟨c₀, hc₀⟩ := Finite.exists_max (fun c => ‖e c‖)
  have h1 : ‖e c₀‖ ≤ t * ‖e c₀‖ + r := by
    calc ‖e c₀‖ = ‖(t : ℂ) * ∑ b, (MB c₀ b) ^ 2 * e b + R c₀‖ := by rw [← heq c₀]
      _ ≤ ‖(t : ℂ) * ∑ b, (MB c₀ b) ^ 2 * e b‖ + ‖R c₀‖ := norm_add_le _ _
      _ ≤ t * ‖e c₀‖ + r := by
          refine add_le_add ?_ (hR c₀)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
          refine mul_le_mul_of_nonneg_left ?_ ht0
          calc ‖∑ b, (MB c₀ b) ^ 2 * e b‖ ≤ ∑ b, ‖(MB c₀ b) ^ 2 * e b‖ := norm_sum_le _ _
            _ ≤ ∑ b, ‖MB c₀ b‖ ^ 2 * ‖e c₀‖ := by
                refine Finset.sum_le_sum fun b _ => ?_
                rw [norm_mul, norm_pow]
                exact mul_le_mul_of_nonneg_left (hc₀ b) (by positivity)
            _ = ‖e c₀‖ := by rw [← Finset.sum_mul, hsq, one_mul]
  have h2 : ‖e c₀‖ ≤ r / (1 - t) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  exact (hc₀ c).trans h2

/-- The coefficients of a frame that is linear in `X`: `κ_α = W^{-2d} Σ_{x ∈ [a], y ∈ [b]} tl(x,y) T(x,y,α)`. -/
def BAExp14a_kap (a b : Zd d L) (tl : Idx d L W → Idx d L W → ℂ) (T : Idx d L W → Idx d L W → Idx d L W → ℂ)
    (α : Idx d L W) : ℂ :=
  ((((W : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, tl x y * T x y α

/-- `frame(tl, J) = Σ_α X_{[α]} κ_α` for `J(x,y) = Σ_α X_{[α]} T(x,y,α)`. -/
theorem BAExp14a_frame_lin_eq (a b : Zd d L) (tl : Idx d L W → Idx d L W → ℂ)
    (T : Idx d L W → Idx d L W → Idx d L W → ℂ) (X : Zd d L → ℂ) :
    BAExp14a_frame a b tl (fun x y => ∑ α, X (split d L W α).1 * T x y α) =
      ∑ α, X (split d L W α).1 * BAExp14a_kap a b tl T α := by
  unfold BAExp14a_frame BAExp14a_kap
  simp only [Finset.mul_sum]
  have h1 : ∀ f : Idx d L W → Idx d L W → Idx d L W → ℂ,
      ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, ∑ α, f x y α = ∑ α, ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, f x y α := by
    intro f
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [h1]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `Σ_α |κ_α| ≤ W^{-d} SC` when `tl` is supported on one offset with `|tl| ≤ 1` and `Σ_α |T(x,y,α)| ≤ SC`. -/
theorem BAExp14a_kap_l1 (a b : Zd d L) (tl : Idx d L W → Idx d L W → ℂ)
    (T : Idx d L W → Idx d L W → Idx d L W → ℂ) {SC : ℝ} (htl : ∀ x y, ‖tl x y‖ ≤ 1)
    (hs : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → tl x y = 0) (hT : ∀ x y, ∑ α, ‖T x y α‖ ≤ SC)
    (hSC : 0 ≤ SC) :
    ∑ α, ‖BAExp14a_kap a b tl T α‖ ≤ ((W : ℝ) ^ d)⁻¹ * SC := by
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  have h1 : ∀ α, ‖BAExp14a_kap a b tl T α‖ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 *
      ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, ‖tl x y‖ * ‖T x y α‖ := by
    intro α
    unfold BAExp14a_kap
    rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => ?_))
    rw [norm_mul]
  calc ∑ α, ‖BAExp14a_kap a b tl T α‖
      ≤ ∑ α, (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, ‖tl x y‖ * ‖T x y α‖ :=
        Finset.sum_le_sum fun α _ => h1 α
    _ = (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, ‖tl x y‖ * ∑ α, ‖T x y α‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
    _ ≤ (((W : ℝ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b,
          (if (split d L W x).2 = (split d L W y).2 then SC else 0) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_) (by positivity)
        by_cases h : (split d L W x).2 = (split d L W y).2
        · simp only [h, ↓reduceIte]
          calc ‖tl x y‖ * ∑ α, ‖T x y α‖ ≤ 1 * SC := mul_le_mul (htl x y) (hT x y) (Finset.sum_nonneg fun _ _ => norm_nonneg _) zero_le_one
            _ = SC := one_mul _
        · simp only [h, ↓reduceIte]
          rw [hs x y h, norm_zero, zero_mul]
    _ = ((W : ℝ) ^ d)⁻¹ * SC := by
        have h2 : ∑ x ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b, (if (split d L W x).2 = (split d L W y).2 then SC else 0) =
            SC * (W : ℝ) ^ d := by
          rw [← BAExp14a_pair_count (W := W) a b, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs <;> simp
        rw [h2]
        field_simp

/-- **The polynomial envelope** (pure arithmetic): `a, b ≤ A0 ≤ 2N²`, `η⁻¹ ≤ N²`, `N ≥ 1`. -/
theorem BAExp14a_env_arith {N η A0 a b K3 SC Wd : ℝ} (hN : 1 ≤ N) (hη : 0 < η) (hη' : η⁻¹ ≤ N ^ 2)
    (hA0 : A0 ≤ 2 * N ^ 2) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ A0) (hb : b ≤ A0) (hK3 : 0 ≤ K3) (hSC : 0 ≤ SC)
    (hWd0 : 0 ≤ Wd) (hWd : Wd ≤ 1) :
    b * (a * (a * (K3 * ((1 + b) / η)))) + Wd * (b * (a * SC)) + a * (a * (K3 * ((1 + b) / η))) + a * SC ≤
      (36 * K3 + 6 * SC) * N ^ 10 := by
  set u : ℝ := N ^ 2 with hu
  have hu1 : 1 ≤ u := by rw [hu]; nlinarith
  have hu0 : 0 ≤ u := by linarith
  have hN10 : N ^ 10 = u ^ 5 := by rw [hu]; ring
  rw [hN10]
  have ha2 : a ≤ 2 * u := ha.trans hA0
  have hb2 : b ≤ 2 * u := hb.trans hA0
  have hq : (1 + b) / η ≤ 3 * u ^ 2 := by
    rw [div_eq_mul_inv]
    have h1 : 1 + b ≤ 3 * u := by linarith
    calc (1 + b) * η⁻¹ ≤ (3 * u) * u := mul_le_mul h1 hη' (inv_nonneg.2 hη.le) (by linarith)
      _ = 3 * u ^ 2 := by ring
  have hq0 : 0 ≤ (1 + b) / η := by positivity
  have hJ : a * (a * (K3 * ((1 + b) / η))) ≤ 12 * K3 * u ^ 4 := by
    calc a * (a * (K3 * ((1 + b) / η))) ≤ (2 * u) * ((2 * u) * (K3 * (3 * u ^ 2))) := by
          gcongr
      _ = 12 * K3 * u ^ 4 := by ring
  have hJ0 : 0 ≤ a * (a * (K3 * ((1 + b) / η))) := by positivity
  have hbJ : b * (a * (a * (K3 * ((1 + b) / η)))) ≤ 24 * K3 * u ^ 5 := by
    calc b * (a * (a * (K3 * ((1 + b) / η)))) ≤ (2 * u) * (12 * K3 * u ^ 4) := mul_le_mul hb2 hJ hJ0 (by linarith)
      _ = 24 * K3 * u ^ 5 := by ring
  have hW : Wd * (b * (a * SC)) ≤ 4 * SC * u ^ 2 := by
    calc Wd * (b * (a * SC)) ≤ 1 * ((2 * u) * ((2 * u) * SC)) := by gcongr
      _ = 4 * SC * u ^ 2 := by ring
  have haS : a * SC ≤ 2 * SC * u := by nlinarith
  have h4 : u ^ 4 ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have h2 : u ^ 2 ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have h1' : u ≤ u ^ 5 := by
    have := pow_le_pow_right₀ hu1 (show 1 ≤ 5 by norm_num)
    simpa using this
  nlinarith [mul_nonneg hK3 (sub_nonneg.2 h4), mul_nonneg hSC (sub_nonneg.2 h2), mul_nonneg hSC (sub_nonneg.2 h1')]

end Path


/-! ## A6. The deterministic BA data: `M`, `Θ^{(+,+)} = ω`, `W - 1`

`M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}` (`BAMres_fine_apply`), `ω = Θ^{(+,+)} = (1 - t M^{(B)}∘M^{(B)})⁻¹`
(`BATheta d L g E m t true true`), `(W - 1)_{αβ} = W^{-d}(ω - 1)_{[α][β]}`. -/

section Deterministic

private theorem BAExp14a_Msigma_shift {d L : ℕ} [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (x + c) (y + c) = BAMsigma d L (BAMB d L g z m) σ x y := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_shift]
  · exact BAMB_shift d L g z m x y c

/-- Translation invariance of `Θ`: `Θ(x, y) = Θ(0, y - x)` (as `KInduct_theta_shift` in `BA/KInduct.lean`). -/
private theorem BAExp14a_theta_shift {d L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BATheta d L g E m t s s' x y = BATheta d L g E m t s s' 0 (y - x) := by
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) s s' with hQ
  let e : Zd d L ≃ Zd d L := Equiv.addRight (-x)
  have hQe : ∀ a b, Q (e a) (e b) = Q a b := fun a b => by
    simp only [hQ, BAMss, Matrix.of_apply, e, Equiv.coe_addRight]
    rw [BAExp14a_Msigma_shift, BAExp14a_Msigma_shift]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q).submatrix e e = 1 - (t : ℂ) • Q := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQe]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q) e e
  rw [hA] at h2
  unfold BATheta PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  simp only [e, Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h3
  exact h3

/-- **The `ℓ¹` rows of `ω = Θ^{(+,+)}`, uniform in `t ∈ [0,1)`** (`baProp5s_holds`; as the private `KInduct_theta_l1` in `BA/KInduct.lean`):
`Σ_b |ω_{xb}| ≤ S`, `S = C_s (1 + Λ² expC k c_s)` depends on `(k, Λ, κ)` only. -/
theorem BAExp14a_theta_l1 {k : ℕ} (hk : 1 ≤ k) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ S : ℝ, 0 < S ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (x : Zd (k + 2) L),
        ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖ ≤ S := by
  obtain ⟨Cs, hCs, cs, hcs, hbd⟩ := baProp5s_holds (k + 2) Λ κ (by omega) hΛ hκ
  have hexpC : 0 ≤ expC k cs := by unfold expC; positivity
  refine ⟨Cs * (1 + Λ ^ 2 * expC k cs), by positivity, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 x
  have hpt : ∀ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖
      ≤ Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
    intro b
    rw [BAExp14a_theta_shift]
    have := hbd L hL g hg hgΛ E m hr t ht0 ht1 true (b - x)
    simpa [neg_mul] using this
  have h1 : ∑ b : Zd (k + 2) L, (if b - x = 0 then (1 : ℝ) else 0) = 1 := by
    simp [sub_eq_zero]
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ))) ≤ expC k cs :=
    (le_of_eq (Fintype.sum_equiv (Equiv.subRight x) _
      (fun y : Zd (k + 2) L => Real.exp (-(cs * (zdistD (k + 2) L y : ℝ)))) fun b => rfl)).trans
      (sum_radial_exp_decay_le k hcs)
  calc ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖
      ≤ ∑ b : Zd (k + 2) L, Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = Cs * (1 + g ^ 2 * ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1, ← Finset.mul_sum]
    _ ≤ Cs * (1 + g ^ 2 * expC k cs) := by gcongr
    _ ≤ Cs * (1 + Λ ^ 2 * expC k cs) := by
        have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
        gcongr

/-- The columns of `ω` have the same bound (`ω` is symmetric, `BATheta_isSymm`). -/
theorem BAExp14a_theta_col {k : ℕ} {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal (k + 2) L g κ E m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {S : ℝ}
    (hS : ∀ x : Zd (k + 2) L, ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖ ≤ S) (b : Zd (k + 2) L) :
    ∑ a : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true a b‖ ≤ S := by
  have hT := BATheta_isSymm (k + 2) L g κ E m hr t ht0 ht1 true true
  have : ∀ a, BATheta (k + 2) L g E m t true true a b = BATheta (k + 2) L g E m t true true b a := fun a => by
    have := congrFun (congrFun hT b) a
    simpa [Matrix.transpose_apply] using this
  simp only [this]
  exact hS b

/-- `|M_{xy}| ≤ 1` on the fine lattice (the fine Ward row `Σ_y |M_{xy}|² = 1`, `baM_row_sq`). -/
theorem BAExp14a_M_le_one {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (h : BASelf d L g0 (E : ℂ) m)
    (x y : Idx d L W) : ‖BAlwM d L W g0 E m x y‖ ≤ 1 := by
  have hrow := baM_row_sq d L W g0 E m h x
  have hle : ‖BAlwM d L W g0 E m x y‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAlwM d L W g0 E m x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ y)
  nlinarith [norm_nonneg (BAlwM d L W g0 E m x y)]

/-- `M` is supported on one offset. -/
theorem BAExp14a_M_supp {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (h : BASelf d L g0 (E : ℂ) m)
    (x y : Idx d L W) (hxy : (split d L W x).2 ≠ (split d L W y).2) : BAlwM d L W g0 E m x y = 0 := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using h.1.ne'
  unfold BAlwM
  rw [BAMres_fine_apply d L W g0 (E : ℂ) m hw x y]
  simp [hxy]

/-- The fine row `ℓ¹` sum of `|M|` is the block one: `Σ_y |M_{xy}| = Σ_b |M^{(B)}_{[x] b}|`. -/
theorem BAExp14a_M_row_eq {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (h : BASelf d L g0 (E : ℂ) m)
    (x : Idx d L W) :
    ∑ y, ‖BAlwM d L W g0 E m x y‖ = ∑ b : Zd d L, ‖BAMB d L g0 (E : ℂ) m (split d L W x).1 b‖ := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using h.1.ne'
  have h1 : ∑ y, ‖BAlwM d L W g0 E m x y‖ = ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then
      ‖BAMB d L g0 (E : ℂ) m (split d L W x).1 (split d L W y).1‖ else 0) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold BAlwM
    rw [BAMres_fine_apply d L W g0 (E : ℂ) m hw x y]
    split_ifs <;> simp
  rw [h1]
  exact BASizeClaim_fibre_sum x (fun b => ‖BAMB d L g0 (E : ℂ) m (split d L W x).1 b‖)

/-- **`ℓ¹` rows of the fine `M`**, uniform in `L, W` (`BAMB_row_l1`; `d = k + 2`): `Σ_y |M_{xy}| ≤ CM = c⁻¹ expC k c`. -/
theorem BAExp14a_M_row_l1 {k : ℕ} {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ CM : ℝ, 0 < CM ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ →
      BAReal (k + 2) L g κ E m → ∀ x : Idx (k + 2) L W, ∑ y, ‖BAlwM (k + 2) L W g E m x y‖ ≤ CM := by
  have hc := BAct_rate_pos (k + 2) Λ κ (by omega) hΛ hκ
  refine ⟨(BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ), by unfold expC; positivity, ?_⟩
  intro L W _ _ hL g E m hg hgΛ hr x
  rw [BAExp14a_M_row_eq hr.1]
  exact BAMB_row_l1 k L hL Λ g κ E m hΛ hg hgΛ hκ hr _

/-- The columns: `M` is symmetric (`baM_symm`). -/
theorem BAExp14a_M_col_eq {d L W : ℕ} [NeZero L] [NeZero W] (g0 E : ℝ) (m : ℂ) (y : Idx d L W) :
    ∑ x, ‖BAlwM d L W g0 E m x y‖ = ∑ x, ‖BAlwM d L W g0 E m y x‖ :=
  Finset.sum_congr rfl fun x _ => by rw [baM_symm g0 E m x y]

/-- `lift` commutes with scalars (as the private `BASizeClaim_lift_smul`). -/
private theorem BAExp14a_lift_smul {d L W : ℕ} [NeZero L] [NeZero W] (c : ℂ) (A : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (c • A) = c • lwLift d L W A := by
  ext x y; simp [lwLift]; ring

/-- `M⁺ · lift(Θ) = lift(M^{(+,+)} Θ)` (`M` is offset-diagonal: one `α` per block, `BASizeClaim_fibre_sum`). -/
theorem BAExp14a_Mp_lift {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (hw : ((E : ℂ) + m).im ≠ 0)
    (Θ : Matrix (Zd d L) (Zd d L) ℂ) :
    BAlwMp d L W g0 E m * lwLift d L W Θ = lwLift d L W (BAMss d L (BAMB d L g0 (E : ℂ) m) true true * Θ) := by
  ext x β
  simp only [Matrix.mul_apply, lwLift, Matrix.of_apply, BAlwMp, BAlwM]
  simp only [BAMres_fine_apply d L W g0 (E : ℂ) m hw]
  have h := BASizeClaim_fibre_sum x (fun b => BAMss d L (BAMB d L g0 (E : ℂ) m) true true (split d L W x).1 b *
    Θ b (split d L W β).1)
  have h2 : ∀ α : Idx d L W,
      (if (split d L W x).2 = (split d L W α).2 then BAMB d L g0 (E : ℂ) m (split d L W x).1 (split d L W α).1 else 0) *
        (if (split d L W α).2 = (split d L W x).2 then BAMB d L g0 (E : ℂ) m (split d L W α).1 (split d L W x).1 else 0) *
        (((W : ℂ) ^ d)⁻¹ * Θ (split d L W α).1 (split d L W β).1) =
      ((W : ℂ) ^ d)⁻¹ * (if (split d L W x).2 = (split d L W α).2 then
        (fun b => BAMss d L (BAMB d L g0 (E : ℂ) m) true true (split d L W x).1 b * Θ b (split d L W β).1)
          (split d L W α).1 else 0) := by
    intro α
    by_cases ho : (split d L W x).2 = (split d L W α).2
    · have ho' : (split d L W α).2 = (split d L W x).2 := ho.symm
      simp only [ho, ↓reduceIte]
      simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true]
      ring
    · have ho' : ¬ (split d L W α).2 = (split d L W x).2 := fun e => ho e.symm
      simp only [ho, ho', ↓reduceIte]
      simp
  simp only [h2, ← Finset.mul_sum]
  rw [h]

/-- **`W - 1 = lift(ω - 1)`** (`(W - 1)_{αβ} = W^{-d} (ω - 1)_{[α][β]}`), `ω = Θ^{(+,+)}`: from
`W = 1 + M⁺ (S W)` (`baW_mul`) and `S W = t · lift(ω)` (`baSp_eq`). -/
theorem BAExp14a_W_sub_one {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {g0 κ E t : ℝ} {m : ℂ}
    (hr : BAReal d L g0 κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BAlwW d L W g0 E t m - 1 = lwLift d L W (BATheta d L g0 E m t true true - 1) := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hr.1.1.ne'
  set Q := BAMss d L (BAMB d L g0 (E : ℂ) m) true true with hQ
  set Θ := BATheta d L g0 E m t true true with hΘ
  have hU := BATheta_isUnit d L g0 κ E m hr t ht0 ht1 true true
  have h1 : (1 - (t : ℂ) • Q) * Θ = 1 := by
    have : Θ = Ring.inverse (1 - (t : ℂ) • Q) := rfl
    rw [this]
    exact Ring.mul_inverse_cancel _ hU
  have hmul := baW_mul (W := W) hL g0 E t m hr.1 ht0 ht1
  have hmul' : (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) * BAlwW d L W g0 E t m = 1 :=
    mul_eq_one_comm.1 hmul
  have hSW := baSp_eq d L W hL g0 κ E t m hr ht0 ht1
  rw [sub_mul, one_mul] at hmul'
  have hWe : BAlwW d L W g0 E t m - 1 =
      BAlwMp d L W g0 E m * (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) := by
    rw [← Matrix.mul_assoc]
    exact sub_eq_of_eq_add' (sub_eq_iff_eq_add.1 hmul')
  have hQΘ : (t : ℂ) • (Q * Θ) = Θ - 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc] at h1
    exact (sub_eq_of_eq_add' (sub_eq_iff_eq_add.1 h1)).symm
  rw [hWe, hSW, Matrix.mul_smul, BAExp14a_Mp_lift hw, ← BAExp14a_lift_smul, hQΘ]

/-- **The column sums of `W - 1`**: `Σ_α |(W - 1)_{αβ}| ≤ S + 1` from the column sums of `ω` (`≤ S`). -/
theorem BAExp14a_Wsub_col {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {g0 κ E t : ℝ} {m : ℂ}
    (hr : BAReal d L g0 κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1) {S : ℝ}
    (hS : ∀ b : Zd d L, ∑ a : Zd d L, ‖BATheta d L g0 E m t true true a b‖ ≤ S) (β : Idx d L W) :
    ∑ α : Idx d L W, ‖(BAlwW d L W g0 E t m - 1) α β‖ ≤ S + 1 := by
  rw [BAExp14a_W_sub_one hL hr ht0 ht1]
  have hWd : (0 : ℝ) < ((W : ℝ) ^ d) := by
    have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  have e1 : ∀ α : Idx d L W, ‖(lwLift d L W (BATheta d L g0 E m t true true - 1)) α β‖ =
      ((W : ℝ) ^ d)⁻¹ * ‖(BATheta d L g0 E m t true true - 1) (split d L W α).1 (split d L W β).1‖ := by
    intro α
    simp only [lwLift, Matrix.of_apply, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  simp only [e1]
  rw [← Finset.mul_sum, BAExp14a_sum_blk (W := W) (fun c => ‖(BATheta d L g0 E m t true true - 1) c (split d L W β).1‖),
    ← mul_assoc, inv_mul_cancel₀ hWd.ne', one_mul]
  calc ∑ c : Zd d L, ‖(BATheta d L g0 E m t true true - 1) c (split d L W β).1‖
      ≤ ∑ c : Zd d L, (‖BATheta d L g0 E m t true true c (split d L W β).1‖ +
          (if c = (split d L W β).1 then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        simp only [Matrix.sub_apply, Matrix.one_apply]
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
        split_ifs <;> simp
    _ = ∑ c : Zd d L, ‖BATheta d L g0 E m t true true c (split d L W β).1‖ + 1 := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ S + 1 := by gcongr; exact hS _

end Deterministic

/-! ## A7. The scalars along the flow: `1 - t`, `η`, `B ≤ 2`, `W^{-d} ≤ (λ² + 1) B` -/

section Scalars

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `1 - t ≥ Im z / 2` for `t ≤ t₀ = Im m/(Im m + Im z)` (`‖m‖ ≤ 1`, `Im z ≤ 1`). -/
theorem BAExp14a_one_sub_t (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (ht : t ≤ BAflowT0 sz z n) : (z n).im / 2 ≤ 1 - t := by
  obtain ⟨hzpos, hmpos, -, -⟩ := BAflow_T0_bounds hκ hflow n
  have hz1 : (z n).im ≤ 1 := (hflow.2 n).2.2
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hzpos
  have hm1 : ‖BAm d (sz.L n) (sz.lam n) (z n)‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (sz.lam n) (z n) _ hzpos.le hm
  have hmi : (BAm d (sz.L n) (sz.lam n) (z n)).im ≤ 1 := (Complex.im_le_norm _).trans hm1
  have h0 : BAflowT0 sz z n = (BAm d (sz.L n) (sz.lam n) (z n)).im /
      ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im) := rfl
  set mi := (BAm d (sz.L n) (sz.lam n) (z n)).im with hmi_def
  have hden : 0 < mi + (z n).im := by linarith
  have h1 : 1 - BAflowT0 sz z n = (z n).im / (mi + (z n).im) := by
    rw [h0]; field_simp; ring
  have h2 : (z n).im / 2 ≤ (z n).im / (mi + (z n).im) := by
    apply div_le_div_of_nonneg_left hzpos.le hden
    linarith
  linarith

/-- The three eventual scalar facts along the flow: `N (1 - t) ≥ 1`, `(1 - t)⁻¹ ≤ N`, `4 ≤ N`, `0 < g₀ ≤ 𝔡⁻¹`. -/
theorem BAExp14a_eventually (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧
      0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹ := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hN2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hN2, hsz.eventually (eventually_ge_atTop 4), BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow]
    with n hn2 hn4 hlam
  refine ⟨?_, hn4, hlam.1, hlam.2⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1 := BAExp14a_one_sub_t hκ hflow n (ht n)
  have h2 := (hflow.2 n).2.1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hpos : 0 < 1 - t n := by
    have : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h2
    linarith
  have h3 : N * N ^ (-1 + ε) = N ^ ε := by
    rw [← Real.rpow_one_add' hN0.le (by linarith)]
    congr 1; ring
  have h4 : 1 ≤ N * (1 - t n) := by
    calc (1 : ℝ) ≤ N ^ ε / 2 := by linarith
      _ = N * N ^ (-1 + ε) / 2 := by rw [h3]
      _ ≤ N * (z n).im / 2 := by gcongr
      _ = N * ((z n).im / 2) := by ring
      _ ≤ N * (1 - t n) := by gcongr
  rw [inv_le_comm₀ hpos hN0]
  rw [inv_eq_one_div, div_le_iff₀ hN0]
  linarith

/-- `W^{-d} ≤ (λ² + 1) B` (`STBctl_ge`). -/
theorem BAExp14a_Wd_le (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n t := by
  have h := STBctl_ge sz n ht0 ht1
  have hl : 0 < sz.lam n ^ 2 + 1 := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (sz.lam n ^ 2 + 1) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) := by
        field_simp
    _ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n t := mul_le_mul_of_nonneg_left h hl.le

end Scalars

/-! ## A8. The Ward identity of the carrier and the pathwise envelope -/

section Carrier

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `G_t` of the carrier is the resolvent of the Hermitian `H = g₀ Ψ + H_t` at `z_t = E + (1 - t) m`. -/
theorem BAExp14a_G_green (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    (baFMz sz z).G n t ω = green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
      (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) :=
  BAGt_eq_green sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω

theorem BAExp14a_eta_eq (n : ℕ) (t : ℝ) : (baFMz sz z).eta n t = etaOf ((baFMz sz z).m n) t := rfl

/-- **Fine-level Ward identities of the carrier** (row and column): `η Σ_y |G_{xy}|² = Im G_{xx}`, `η Σ_y |G_{yx}|² = Im G_{xx}`. -/
theorem BAExp14a_G_ward (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x : Idx d (sz.L n) (sz.W n)) :
    (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω x y‖ ^ 2 = ((baFMz sz z).G n t ω x x).im ∧
      (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω y x‖ ^ 2 = ((baFMz sz z).G n t ω x x).im := by
  obtain ⟨-, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have hz : (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im ≠ 0 := hzi.ne'
  have e : (baFMz sz z).eta n t = (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im := by
    rw [ztOf_im]; rfl
  rw [BAExp14a_G_green, e]
  exact ⟨BAExp14a_ward_row hH hz x, BAExp14a_ward_col hH hz x⟩

/-- `η > 0`. -/
theorem BAExp14a_eta_pos (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) : 0 < (baFMz sz z).eta n t := by
  obtain ⟨-, -, -, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  rw [ztOf_im] at hzi
  exact hzi

/-- `‖G_{xy}‖ ≤ η⁻¹` pathwise. -/
theorem BAExp14a_G_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).G n t ω x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ := by
  obtain ⟨-, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have hdiag : ‖(baFMz sz z).G n t ω x x‖ ≤ ((baFMz sz z).eta n t)⁻¹ := by
    have e : (baFMz sz z).eta n t = (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im := by
      rw [ztOf_im]; rfl
    rw [BAExp14a_G_green, e]
    exact BAExp14a_green_diag_le hH hzi x
  obtain ⟨hw, -⟩ := BAExp14a_G_ward hκ hflow n ht0 ht ω x
  have h1 : ‖(baFMz sz z).G n t ω x y‖ ^ 2 ≤ ∑ w, ‖(baFMz sz z).G n t ω x w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(baFMz sz z).G n t ω x w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : ((baFMz sz z).G n t ω x x).im ≤ ((baFMz sz z).eta n t)⁻¹ :=
    (Complex.im_le_norm _).trans hdiag
  have h3 : (baFMz sz z).eta n t * ‖(baFMz sz z).G n t ω x y‖ ^ 2 ≤ ((baFMz sz z).eta n t)⁻¹ := by
    calc _ ≤ (baFMz sz z).eta n t * ∑ w, ‖(baFMz sz z).G n t ω x w‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hη.le
      _ = _ := hw
      _ ≤ _ := h2
  set e := (baFMz sz z).eta n t with he
  by_contra hcon
  push Not at hcon
  have h4 : e⁻¹ < ‖(baFMz sz z).G n t ω x y‖ := hcon
  have h5 : 1 < e * ‖(baFMz sz z).G n t ω x y‖ := by
    have := mul_lt_mul_of_pos_left h4 hη
    rwa [mul_inv_cancel₀ hη.ne'] at this
  nlinarith [mul_pos hη hη, norm_nonneg ((baFMz sz z).G n t ω x y), inv_pos.2 hη, mul_inv_cancel₀ hη.ne']

end Carrier


end RBM.BA

end
