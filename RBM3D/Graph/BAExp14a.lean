/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Carrier
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.ScaleFacts
import RBM3D.Graph.BASizeClaim

/-!
# BA-L L4a (T2418), part A: the generic machinery of the crude families S1 of `lem:LWterm_EXP` at BA

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:7-121` (`(eq:ELW_term)`, `B:11-14`), `GGGamma` (`B:393-405`),
`lanlw` (`B:359-372`); design `docs/reports/T2398-design.md` §1, §2.  This file is the model-free half of the twin of
`Graph/LWExpTerm4.lean` §§2-5 (`:129-826`): the fine-level Ward identity (the twin of `lwExpTerm4_ward_*`, `:136-192`), the
`≺ → 𝔼` first moment at an arbitrary law (the twin of `lwExpTerm_prec_integral`, `LWExpTerm.lean:143`), the calculus of `≺`
for one-index random variables, the block combinatorics of the fine lattice, and the pathwise bounds of the sums `J` of the
six families.  The BA data, the pin `BAExp14aS1` and its proof are in `Graph/BAExp14aB.lean`.

Reuse: `lwExpTerm4_ward_*` (`LWExpTerm4.lean:136-192`, private there; copied), `lwExpTerm_first_moment`,
`lwExpTerm_prec_integral` (`LWExpTerm.lean:106-143`; the latter at `sz.seqP` only; copied for an arbitrary law),
`st6_prec_det_iff` (`Induction/Step6Kit.lean:81`; at `seqP` only; copied for an arbitrary law).  Not used: §§6, 9 and the
twisted part of §8 of the band file (L4b2), `lwExpTerm4_kerSum`, `kward`, `L3` (decisions 2, 3 of Amend 1).
No `tw*` name, no `BATwistAvgLaw`/`BATwistLoopLaw`.

All private helpers carry the stem `BAExp14a_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The toolbox of `≺` at an arbitrary law -/

section Toolbox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A deterministic `≺` is the pointwise bound for large `n`** (`st6_prec_det_iff`, `Induction/Step6Kit.lean:81`, at an
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

/-- `ξ ≺ ζ₁` and `ζ₁ ≤ K ζ₂` give `ξ ≺ ζ₂` (`K > 0`, `ζ₂ ≥ 0`). -/
theorem BAExp14a_prec_mono {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
    {ξ ζ₁ ζ₂ : ∀ l, U l → Ω → ℝ} {K : ℝ} (hK : 0 < K) (hζ₂ : ∀ l u ω, 0 ≤ ζ₂ l u ω)
    (hle : ∀ l u ω, ζ₁ l u ω ≤ K * ζ₂ l u ω) (h : StochDomAt P size ξ ζ₁) : StochDomAt P size ξ ζ₂ := by
  have h2 : StochDomAt P size ζ₁ ζ₂ :=
    StochDomAt.of_le_left hle (StochDomAt.const_mul_left hsize hK.le hζ₂ (StochDomAt.refl hsize hζ₂))
  exact StochDomAt.trans hsize h h2

/-- **The first moment off the failure event** (copy of `lwExpTerm_first_moment`, `Graph/LWExpTerm.lean:106`, private there). -/
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

/-- **`≺ → 𝔼`** at an arbitrary probability law (the twin of `lwExpTerm_prec_integral`, `Graph/LWExpTerm.lean:143`): from the `≺` of
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

/-! ## 2. One-index random variables: `f ≺ g` and its calculus at the law `μ` -/

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
    (hle : ∀ n, g n ≤ K * g' n) (h : BAExp14a_Dom sz μ f g) : BAExp14a_Dom sz μ f g' :=
  BAExp14a_prec_mono hsz hK (fun n _ _ => hg' n) (fun n _ _ => hle n) h

theorem BAExp14a_Dom.const_mul {f : ∀ n : ℕ, sz.SeqΩ → ℝ} {g : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ n, 0 ≤ g n)
    (h : BAExp14a_Dom sz μ f g) : BAExp14a_Dom sz μ (fun n ω => c * f n ω) g :=
  StochDomAt.const_mul_left hsz hc (fun n _ _ => hg n) h

/-- A one-index domination is a domination of the same quantity indexed by anything (constant in the index). -/
theorem BAExp14a_Dom.index {f : ∀ n : ℕ, sz.SeqΩ → ℝ} {g : ℕ → ℝ} {V : ℕ → Type*} (h : BAExp14a_Dom sz μ f g) :
    PrecL sz μ (U := V) (fun n _ ω => f n ω) (fun n _ _ => g n) :=
  StochDomAt.precomp_param h (fun n (_ : V n) => ())

end Dom

/-! ## 3. The fine-level Ward identity (twin of `lwExpTerm4_ward_*`, `LWExpTerm4.lean:136-192`) -/

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

/-! ## 4. The block combinatorics of the fine lattice and the frame bounds -/

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
    · rw [if_pos h, norm_mul]
      exact mul_le_mul (htl x y) (hJ x y) (norm_nonneg _) hτ
    · rw [if_neg h, hs x y h, norm_zero]
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

/-! ## 5. The pathwise bounds of the sums `J(x,y)` of the six families

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

/-- `J_MM(x,y) = Σ_α X_{[α]} Σ_β Wk_{αβ} M_{xβ} M_{βy}`: `|J| ≤ a S CM`. -/
theorem BAExp14a_J_MM_le (X : Zd d L → ℂ) (Wk Mm : Idx d L W → Idx d L W → ℂ) {a S CM : ℝ}
    (ha : ∀ c, ‖X c‖ ≤ a) (hWk : ∀ β, ∑ α, ‖Wk α β‖ ≤ S) (hM1 : ∀ x y, ‖Mm x y‖ ≤ 1)
    (hMr : ∀ x, ∑ y, ‖Mm x y‖ ≤ CM) (x y : Idx d L W) :
    ‖∑ α, X (split d L W α).1 * ∑ β, Wk α β * Mm x β * Mm β y‖ ≤ a * (S * CM) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  exact (BAExp14a_sum_X_le X _ ha).trans
    (mul_le_mul_of_nonneg_left (BAExp14a_T_MM_l1 Wk Mm hWk hM1 hMr x y) ha0)

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

end Path

end RBM.BA

end
