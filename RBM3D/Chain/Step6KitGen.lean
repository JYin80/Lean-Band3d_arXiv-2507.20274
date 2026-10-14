/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step6Gen
import RBM3D.Induction.Step6Kit
import RBM3D.Chain.Step2EventsGen
import RBM3D.Chain.Step5CasesGen

/-!
# The Step 6 kit over the carrier (BA-V row V1s1, ticket T2502 row a)

Additive restatement of `Induction/Step6Kit.lean` (not edited) over a carrier `C : FlowFM sz` and a law `μ`, on the vocabulary and pins of
`Chain/Step6Gen.lean`.  Paper: arXiv:2507.20274, `1_2:1390-1396`, `6:93-152`.  Size-level band lemmas (`st6_lam_pos`, `st6_G_pos`, `st6_xB_*`,
`st6_cmp_ini`, `st6_target_*`, `st6_hi_of_reg5*`, `st6_flowE_*`, `st6_mE_im_ge`, `st6_Idiff_same`, ...) are reused by name.  Glue at a law (target 5);
LW readings and the Duhamel/average readings (target 6); initial terms (target 7); skeletons, per carrier (`st6_case*_coreg`) and per family
(`ST_step6_case*_of_pinsgL`), and `st6_GdecayW_of_zerog`, `ST_step6R_monogL` (target 8); instances (target 9).  The family premises of the wrappers
are written inline; no kernel, class or comparison is defined here.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private Step5CasesGen_prec_mono Step5CasesGen_prec_cover from RBM3D.Chain.Step5CasesGen

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Glue at a law (target 5) -/

section Glue

variable {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ)

/-- **A deterministic `Prec` is the pointwise bound for all large `n`** at a probability law (band `st6_prec_det_iff`, `Step6Kit:81`). -/
theorem st6_prec_det_iffg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {V : ℕ → Type*} (F G : ∀ n, V n → ℝ) :
    PrecL sz μ (U := V) (fun n v _ => F n v) (fun n v _ => G n v) ↔
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ v, F n v ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n v := by
  constructor
  · intro h τ hτ
    have h1 := h τ hτ 1 one_pos
    filter_upwards [h1, (tendsto_size sz hsz).eventually (eventually_ge_atTop 2)] with n hn hN2
    intro v
    by_contra hcon
    push Not at hcon
    have hbad : badSetAt sz.size (fun n v (_ : sz.SeqΩ) => F n v) (fun n v (_ : sz.SeqΩ) => G n v) τ n =
        (Set.univ : Set sz.SeqΩ) := by
      ext ω
      simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨v, hcon⟩
    rw [hbad, measure_univ] at hn
    have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN2
    have hlt : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) < 1 := by
      rw [Real.rpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by linarith)
    have h2 : ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hlt
    exact absurd hn (not_le.2 h2)
  · intro h
    refine StochDomAt.of_eventually_empty fun τ hτ => ?_
    filter_upwards [h τ hτ] with n hn
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    exact fun v => hn v

/-- **Per time sequence ⇒ uniform in `u ∈ [s,t]`** for a deterministic family (band `st6_precU_of_forall_seq`, `Step6Kit:115`), at a probability law. -/
theorem st6_precU_of_forall_seqg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    {W : ℕ → Type*} (F G : ∀ n, ℝ → W n → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      PrecL sz μ (U := W) (fun n w _ => F n (u n) w) (fun n w _ => G n (u n) w)) :
    PrecL sz μ (U := fun n => TimeIcc s t n × W n) (fun n p _ => F n (p.1 : ℝ) p.2)
      (fun n p _ => G n (p.1 : ℝ) p.2) := by
  classical
  rw [st6_prec_det_iffg sz μ hμ hsz]
  intro τ hτ
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  let u : ℕ → ℝ := fun n =>
    if hn : ∃ p : TimeIcc s t n × W n,
        ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2)
    then ((Classical.choose hn).1 : ℝ) else s n
  have hu1 : ∀ n, s n ≤ u n := by
    intro n
    by_cases hn : ∃ p : TimeIcc s t n × W n,
        ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2)
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.1
    · simp only [u, hn, ↓reduceDIte]; exact le_rfl
  have hu2 : ∀ n, u n ≤ t n := by
    intro n
    by_cases hn : ∃ p : TimeIcc s t n × W n,
        ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2)
    · simp only [u, hn, ↓reduceDIte]; exact (Classical.choose hn).1.2.2
    · simp only [u, hn, ↓reduceDIte]; exact hst n
  have h' := ((st6_prec_det_iffg sz μ hμ hsz (fun n (w : W n) => F n (u n) w)
    (fun n (w : W n) => G n (u n) w)).1 (h u hu1 hu2)) τ hτ
  obtain ⟨n, hn1, hn2⟩ := (hcon.and_eventually h').exists
  push Not at hn1
  obtain ⟨p, hp⟩ := hn1
  have hex : ∃ p : TimeIcc s t n × W n,
      ¬ (F n (p.1 : ℝ) p.2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * G n (p.1 : ℝ) p.2) := ⟨p, not_le.2 hp⟩
  have hun : u n = ((Classical.choose hex).1 : ℝ) := by simp only [u, hex, ↓reduceDIte]
  have hc := Classical.choose_spec hex
  have := hn2 (Classical.choose hex).2
  rw [hun] at this
  exact hc this

variable {sz μ}
variable (C : FlowFM sz)

/-! ### The bridges at a time sequence `u ∈ [s,t]` (band `Step6Kit:170-210`) -/

theorem STLKgL_of_STLKUgL_at {s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) (h : STLKUgL C μ s t) :
    STLKgL C μ u := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))

theorem STLmaxgL_of_STLmaxUgL_at {s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLmaxUgL C μ s t) : STLmaxgL C μ u := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))

theorem STLocalEntrygL_of_STLocalEntryUgL_at {s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLocalEntryUgL C μ s t) : STLocalEntrygL C μ u :=
  StochDomAt.precomp_param h
    (fun n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))

/-- `(Gt_avgbound_flow)` at the section `u`: `STAvgUgL` gives the premise `LWAvgLawgL` of `LWtermEXPG` (REQ `:40`), through the carrier datum `𝒦^{(1)}_{+,a} = m` at the times `0 ≤ τ < 1` (band `ST_Kloop_one`, `Step2Iterate:1237`, every `τ`; BA `baKsol_one`, `BA/KInduct:77`, `τ ∈ [0,1)`). -/
theorem LWAvgLawgL_of_STAvgUgL_at {s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (hK1 : ∀ (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 → C.K n τ (fun _ : Fin 1 => true) (fun _ => a) = C.m n)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (h : STAvgUgL C μ s t) : LWAvgLawgL C μ u := by
  have h1 := StochDomAt.precomp_param h
    (fun n (a : Zd d (sz.L n)) =>
      ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), ((fun _ : Fin 1 => true), (fun _ : Fin 1 => a))))
  have e : ∀ n (a : Zd d (sz.L n)), C.K n (u n) (fun _ : Fin 1 => true) (fun _ => a) = C.m n := fun n a =>
    hK1 n (u n) a ((hs0 n).trans (hsu n)) ((hut n).trans_lt (ht1 n))
  simp only [e, pow_one] at h1
  exact h1

/-- `(Eq:Gdecay_flow)` of Step 5 (`STGdecayWgL … 0`) at the section `u` is `(Eq:Gdecay)` at `u`. -/
theorem STDecaygL_of_STGdecayWgL_at {s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STGdecayWgL C μ s t 0) : STDecaygL C μ u := by
  intro D hD
  have := StochDomAt.precomp_param (h D hD)
    (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ((⟨u n, hsu n, hut n⟩ : TimeIcc s t n), p))
  simp only [Real.rpow_zero, one_mul] at this
  exact this

/-- The endpoint `u = t` of `STLocalEntryUgL`. -/
theorem STLocalEntrygL_of_STLocalEntryUgL {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLocalEntryUgL C μ s t) :
    STLocalEntrygL C μ t :=
  STLocalEntrygL_of_STLocalEntryUgL_at C hst (fun _ => le_rfl) h

end Glue

/-! ## 2. The `Prec` calculus at a law (target 5) -/

section PrecCalc

variable {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ)

/-- **The sup norm over the labels of a tensor is `≺` if the entries are** (band `st6_prec_pi_norm`, `Step6Kit:225`), for the deterministic tensor `f_s` of the carrier: from `(Eq:Gtlp_exp+IND)` (index `(σ,a)`) to the `L^∞` hypothesis of the kernel pins. -/
theorem st6_prec_pi_normg (hsz : sz.SizeTendsto) {s : ℕ → ℝ} {X : ℕ → ℝ} (hX : ∀ n, 0 ≤ X n) (C : FlowFM sz)
    (h : PrecL sz μ (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖STExpErrg C μ n (s n) p.1 p.2‖) (fun n _ _ => X n))
    (σ : Fin 2 → Bool) {V : ℕ → Type*} :
    PrecL sz μ (U := V) (fun n _ _ => ‖(fun b => STExpErrg C μ n (s n) σ b)‖) (fun n _ _ => X n) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨v, hv⟩ := hω
  have hr : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hX n)
  have : ¬ ‖(fun b => STExpErrg C μ n (s n) σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * X n := not_le.2 hv
  rw [pi_norm_le_iff_of_nonneg hr] at this
  push Not at this
  obtain ⟨a, ha⟩ := this
  exact Or.inl ⟨(σ, a), ha⟩

/-- **Finitely many signs** (band `st6_prec_of_forall_fin`, `Step6Kit:241`): `Prec` for each of finitely many index values gives `Prec` for the family indexed by `(i, v)` (union bound). -/
theorem st6_prec_of_forall_fing (hsz : sz.SizeTendsto) {ι : Type*} [Finite ι] {V : ℕ → Type*}
    (ξ ζ : ∀ n, ι → V n → sz.SeqΩ → ℝ)
    (h : ∀ i : ι, PrecL sz μ (U := V) (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω)) :
    PrecL sz μ (U := fun n => ι × V n) (fun n (p : ι × V n) ω => ξ n p.1 p.2 ω)
      (fun n (p : ι × V n) ω => ζ n p.1 p.2 ω) := by
  intro τ hτ D hD
  have : Fintype ι := Fintype.ofFinite ι
  have hall : ∀ᶠ n in atTop, ∀ i : ι, μ (badSetAt sz.size (fun n v ω => ξ n i v ω)
      (fun n v ω => ζ n i v ω) τ n) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) :=
    Filter.eventually_all.2 fun i => h i τ hτ (D + 1) (by linarith)
  filter_upwards [hall, (tendsto_size sz hsz).eventually (eventually_ge_atTop (Fintype.card ι)),
    (tendsto_size sz hsz).eventually (eventually_ge_atTop 1)] with n hn hN hN1
  have hsub : badSetAt sz.size (fun n (p : ι × V n) ω => ξ n p.1 p.2 ω)
      (fun n (p : ι × V n) ω => ζ n p.1 p.2 ω) τ n ⊆
      ⋃ i : ι, badSetAt sz.size (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω) τ n := by
    intro ω hω
    obtain ⟨p, hp⟩ := hω
    exact Set.mem_iUnion.2 ⟨p.1, p.2, hp⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hNr : (Fintype.card ι : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have hp : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg hN0.le _
  have hrw : ((sz.size n : ℕ) : ℝ) ^ (-D) =
      ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := by
    rw [← Real.rpow_one_add' hN0.le (by linarith)]
    congr 1; ring
  calc μ (badSetAt sz.size (fun n (p : ι × V n) ω => ξ n p.1 p.2 ω)
        (fun n (p : ι × V n) ω => ζ n p.1 p.2 ω) τ n)
      ≤ μ (⋃ i : ι, badSetAt sz.size (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω) τ n) :=
        measure_mono hsub
    _ ≤ ∑ i : ι, μ (badSetAt sz.size (fun n v ω => ξ n i v ω) (fun n v ω => ζ n i v ω) τ n) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := Finset.sum_le_sum fun i _ => hn i
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hrw]
        exact mul_le_mul_of_nonneg_right hNr hp

/-- Reindexing `(u,σ,a)` of `STExp2UgL` and of the sign class `P` (band `st6_cover_exp2U`, `Step6Kit:696`): two sign classes that cover. -/
theorem st6_cover_exp2Ug {s t : ℕ → ℝ} {ξ ζ : ∀ n, TimeIcc s t n → (Fin 2 → Bool) → (Fin 2 → Zd d (sz.L n)) → ℝ}
    (hsz : sz.SizeTendsto) {P₁ P₂ : (Fin 2 → Bool) → Prop} (hcov : ∀ σ, P₁ σ ∨ P₂ σ)
    (h₁ : PrecL sz μ (U := STIdx2P sz P₁ s t) (fun n p _ => ξ n p.1 p.2.1.1 p.2.2) (fun n p _ => ζ n p.1 p.2.1.1 p.2.2))
    (h₂ : PrecL sz μ (U := STIdx2P sz P₂ s t) (fun n p _ => ξ n p.1 p.2.1.1 p.2.2) (fun n p _ => ζ n p.1 p.2.1.1 p.2.2)) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ξ n p.1 p.2.1 p.2.2) (fun n p _ => ζ n p.1 p.2.1 p.2.2) := by
  refine Step5CasesGen_prec_cover sz μ hsz (V₁ := STIdx2P sz P₁ s t) (V₂ := STIdx2P sz P₂ s t)
    (fun n p => (p.1, p.2.1.1, p.2.2)) (fun n p => (p.1, p.2.1.1, p.2.2)) ?_ h₁ h₂
  intro n p
  rcases hcov p.2.1 with h | h
  · exact Or.inl ⟨(p.1, ⟨p.2.1, h⟩, p.2.2), rfl⟩
  · exact Or.inr ⟨(p.1, ⟨p.2.1, h⟩, p.2.2), rfl⟩

end PrecCalc

/-! ## 3. The LW readings (target 6) -/

section LWReading

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`STEGt = LWE`** over a carrier (band `st6_EGt_eq_LWE`, `Step6Kit:327`): the two forms of the light-weight term agree pointwise, by the cyclic rotation of the 3-loop (F7, `Step2EventsGen_Rot3`) and the order of the two factors. -/
theorem st6_EGt_eq_LWEg (hF7 : Step2EventsGen_Rot3 C) (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : STEGtg C n t σ a ω = LWEg C n t σ a ω := by
  unfold STEGtg LWEg LWcutg
  have h1 : ∀ s : Bool, (fun _ : Fin 1 => s) = ![s] := fun s => by
    funext i; fin_cases i; rfl
  have h1' : ∀ x : Zd d (sz.L n), (fun _ : Fin 1 => x) = ![x] := fun x => by
    funext i; fin_cases i; rfl
  simp only [h1, h1']
  have hB : ∀ x y : Zd d (sz.L n),
      (C.L n t ![σ 1] ![x] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.L n t ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω =
      C.S n x y * (C.L n t ![σ 1] ![x] ω - (if σ 1 then C.m n else (starRingEnd ℂ) (C.m n))) *
        C.L n t ![σ 1, σ 1, σ 0] ![y, a 1, a 0] ω := fun x y => by
    rw [hF7 n t (σ 0) (σ 1) (a 0) y (a 1) ω]; ring
  have hA : ∀ x y : Zd d (sz.L n),
      (C.L n t ![σ 0] ![x] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) * C.S n x y *
        C.L n t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω =
      C.S n x y * (C.L n t ![σ 0] ![x] ω - (if σ 0 then C.m n else (starRingEnd ℂ) (C.m n))) *
        C.L n t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω := fun x y => by ring
  simp only [Finset.sum_add_distrib, hA, hB]
  ring

/-- The expected light-weight term is `𝔼 LWEg` (band `st6_expEGt_eq`, `Step6Kit:353`). -/
theorem st6_expEGt_eqg (hF7 : Step2EventsGen_Rot3 C) (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STExpEGtg C μ n t σ a = ∫ ω, LWEg C n t σ a ω ∂μ := by
  unfold STExpEGtg
  congr 1
  funext ω
  exact st6_EGt_eq_LWEg C hF7 n t σ a ω

/-- **`(eq:ExpLWn=2)` uniformly in `u ∈ [s,t]`, per carrier** (band `st6_EGtHi_of_LW`, `Step6Kit:571`; the pin `T2502_EGtHiOfLW`): the LW bound at
every time sequence `u ∈ [s,t]` (the conclusion of `LWtermEXPG`, `LWGen:108`, at `u`; at BA of `BALWtermEXPTw`) gives `STExpEGtHiConclgL`,
through F7 and the deterministic `≺` calculus at the law `μ`. -/
theorem st6_EGtHi_of_LWg (s t : ℕ → ℝ) :
    IsProbabilityMeasure μ → sz.SizeTendsto → (∀ n, s n ≤ t n) → STDriftHi sz s t → Step2EventsGen_Rot3 C →
      (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
        PrecL sz μ (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u n})
          (fun n p _ => ‖∫ ω, LWEg C n (u n) p.1.1 p.1.2 ω ∂μ‖)
          (fun n _ _ => (1 - u n)⁻¹ * (sz.Bctl n (u n)) ^ (5 / 2 : ℝ))) →
        STExpEGtHiConclgL C μ s t := by
  intro hμ hsz hst hHi hF7 hLW
  refine st6_precU_of_forall_seqg sz μ hμ hsz hst
    (W := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖STExpEGtg C μ n u w.1 w.2‖)
    (fun n u _ => (1 - u)⁻¹ * (sz.Bctl n u) ^ (5 / 2 : ℝ)) ?_
  intro u hsu hut
  have h2 := StochDomAt.precomp_param (hLW u hsu hut)
    (fun n (w : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) =>
      (⟨w, (hHi n).trans (by have := hut n; linarith [hst n])⟩ :
        {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u n}))
  have e : (fun n (w : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
        ‖STExpEGtg C μ n (u n) w.1 w.2‖) =
      (fun n (w : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
        ‖∫ ω, LWEg C n (u n) w.1 w.2 ω ∂μ‖) := by
    funext n w ω
    rw [st6_expEGt_eqg C μ hF7]
  rw [e]
  exact h2

end LWReading

section Readings

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
  {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}

/-- **The Duhamel identity along `[s_n, t_n]`** from the eventual family pin `STExpDuhamelZgL` (band `st6_duhEq_of_pin`, `Step6Kit:361`; `t < 1` from the horizon). -/
theorem st6_duhEq_of_ping (hDu : STExpDuhamelZgL d law Flow mk) {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) :
    STExpDuhEqgL (mk sz z) (law sz) s t := by
  filter_upwards [hDu sz κ ε 𝔠 𝔡 z hκ hflow] with n hn
  intro u σ A a
  exact hn (s n) u (hs0 n) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 n)) σ A a

/-- **The `𝒬`-Duhamel identity along `[s_n,t_n]`** for a mollifier family, eventually in `n`, from `STExpDuhamelQgL` (band `st6_duhEqQ_of_pin`, `Step6Kit:833`). -/
theorem st6_duhEqQ_of_ping (hDu : STExpDuhamelQgL d law Flow mk) {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) :
    STExpDuhEqQgL (mk sz z) (law sz) s t ϑ := by
  filter_upwards [hϑ, hDu sz κ ε 𝔠 𝔡 z hκ hflow] with n hn hQ
  intro u σ a
  exact hQ Cq c (ϑ n) hn (s n) u (hs0 n) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 n)) σ a

/-- **`(res_ELK_n=1)` uniformly in `u ∈ [s,t]`** from the per-time pin `STImproveExpAvergL` (band `st6_expAvgU_of_pin`, `Step6Kit:557`): the premise `LWAvgLawgL` is the section of `STAvgUgL` (Step 2; carrier datum `hK1`), `STLKgL` the section of `STLKUgL` (Step 4). -/
theorem st6_expAvgU_of_ping (hAvg : STImproveExpAvergL d law Flow mk T0) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ)
    (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hflow : Flow sz κ ε 𝔠 𝔡 z)
    (hμ : IsProbabilityMeasure (law sz)) (hsz : sz.SizeTendsto)
    (hK1 : ∀ (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ T0 sz z n) (ht1 : ∀ n, t n < 1)
    (hS2 : STStep2CoregL (mk sz z) (law sz) s t) (hLKU : STLKUgL (mk sz z) (law sz) s t) :
    STExpAvgUgL (mk sz z) (law sz) s t := by
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le) (W := fun n => Bool × Zd d (sz.L n))
    (fun n u w => ‖(∫ ω, (mk sz z).L n u (fun _ : Fin 1 => w.1) (fun _ => w.2) ω ∂(law sz)) -
      (if w.1 then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n))‖) (fun n u _ => (sz.Bctl n u) ^ 2) ?_
  intro u hsu hut
  exact hAvg hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
    (fun n => (hut n).trans (htT n)) (LWAvgLawgL_of_STAvgUgL_at (mk sz z) hsu hut hK1 hs0 ht1 hS2.2)
    (STLKgL_of_STLKUgL_at (mk sz z) hsu hut hLKU)

end Readings

/-! ## 4. The initial terms (target 7) -/

section IniTerm

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Ker : STEKKer d}

/-- **The initial term of regimes (iii), (iv)** (band `st6_ini_sumNdecay`, `Step6Kit:600`): `‖𝒰_{s,u} f_s‖ ≺ ((1-s)/(1-u))² T_s` uniformly in
`(u,σ,a)`, from `(sum_res_Ndecay)` with `n = 2` (`STEKSumNdecaygL`, one kernel `Step2Gen_UN C`, no comparison hypothesis) applied to the
deterministic tensor `f_s`; `‖f_s‖_∞ ≺ T_s` is `(Eq:Gtlp_exp+IND)`.  `κm` is the bulk datum of the class `Ker`. -/
theorem st6_ini_sumNdecayg (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) (hμ : IsProbabilityMeasure (law sz))
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hExp : STExp2gL C (law sz) s) :
    PrecL sz (law sz) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖Step2Gen_UN C n p.2.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C (law sz) n (s n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (lt_trans (hst n) (ht1 n))
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le)
    (W := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖Step2Gen_UN C n w.1 (s n) u (fun b => STExpErrg C (law sz) n (s n) w.1 b) w.2‖)
    (fun n u _ => ((1 - s n) / (1 - u)) ^ 2 * STExpTarget sz n (s n)) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have key : ∀ σ : Fin 2 → Bool, PrecL sz (law sz) (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖Step2Gen_UN C n σ (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ b) a‖)
      (fun n _ _ => ((1 - s n) / (1 - u n)) ^ 2 * STExpTarget sz n (s n)) := by
    intro σ
    have hdom := st6_prec_pi_normg sz (law sz) hsz hX C hExp σ (V := fun n => TimeIcc s u n)
    have hk := hSum hd 2 le_rfl κm 𝔠 𝔡 hκm sz hadm C gK hKer hg s u hs0 hsu hu1 σ
      (fun n _ _ b => STExpErrg C (law sz) n (s n) σ b) (fun n _ _ => STExpTarget sz n (s n)) (fun n _ _ => hX n) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    refine StochDomAt.of_le_left (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖Step2Gen_UN C n σ (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ b)‖) (fun n a ω => ?_) h2
    exact norm_le_pi_norm (Step2Gen_UN C n σ (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ b)) a
  exact st6_prec_of_forall_fing sz (law sz) hsz
    (fun n (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖Step2Gen_UN C n σ (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ b) a‖)
    (fun n _ _ _ => ((1 - s n) / (1 - u n)) ^ 2 * STExpTarget sz n (s n)) key

/-- **The initial term of regime (ii)** (band `st6_ini_nonzero`, `Step6Kit:651`): `‖Q^{(A)} 𝒰_{s,u} f_s‖ ≺ T_s` uniformly in `(u,σ,a)`, for the sign
class `P` and `A ⊇ I_diff(σ)` (`(sum_res_Ndecay_nonzero)`, `STEKNonzerogL`, the A-form).  The band window `(1-s) L² ≤ lam²`
(`hsg`) becomes the A-form window by R1, `lam² ≤ Aof κm · gK²` (`hcmp`; DECISIONS §273 (1)); nothing else reads R1. -/
theorem st6_ini_nonzerog {Aof : ℝ → ℝ} (hNZ : STEKNonzerogL d law Ker Aof) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm)
    (hAof : 1 ≤ Aof κm) {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ → ℝ) (hKer : Ker sz C gK κm)
    (hg : ∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹)
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK n ^ 2)
    (hμ : IsProbabilityMeasure (law sz)) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) (hExp : STExp2gL C (law sz) s)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (hA : ∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) :
    PrecL sz (law sz) (U := STIdx2P sz P s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget sz n (s n)) := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hX : ∀ n, 0 ≤ STExpTarget sz n (s n) := fun n => st6_target_nonneg sz n (lt_trans (hst n) (ht1 n))
  have hwin : ∀ n, (1 - s n) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ Aof κm * gK n ^ 2 := fun n => by
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
      have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
      positivity
    have h1 : 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [hsg n]
    rw [le_div_iff₀ hL] at h1
    exact h1.trans (hcmp n).2.2
  refine st6_precU_of_forall_seqg sz (law sz) hμ hsz (fun n => (hst n).le)
    (W := fun n => {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n)))
    (fun n u w => ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n w.1.1 (s n) u
      (fun b => STExpErrg C (law sz) n (s n) w.1.1 b)) w.2‖)
    (fun n _ _ => STExpTarget sz n (s n)) ?_
  intro u hsu hut
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hut n) (ht1 n)
  have key : ∀ σ : {σ : Fin 2 → Bool // P σ}, PrecL sz (law sz) (U := fun n => Fin 2 → Zd d (sz.L n))
      (fun n a _ => ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ.1 (s n) (u n)
        (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a‖)
      (fun n _ _ => STExpTarget sz n (s n)) := by
    intro σ
    have hdom := st6_prec_pi_normg sz (law sz) hsz hX C hExp σ.1 (V := fun n => TimeIcc s u n)
    have hk := hNZ hd 2 le_rfl κm 𝔠 𝔡 hκm hAof sz hadm C gK hKer hg s u hwin hs0 hsu hu1 σ.1 A (hA σ.1 σ.2)
      (fun n _ _ b => STExpErrg C (law sz) n (s n) σ.1 b) (fun n _ _ => STExpTarget sz n (s n)) (fun n _ _ => hX n) hdom
    have h2 := StochDomAt.precomp_param hk
      (fun n (_ : Fin 2 → Zd d (sz.L n)) => (⟨s n, le_rfl, hsu n⟩ : TimeIcc s u n))
    refine StochDomAt.of_le_left (ξ₁ := fun n (_ : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b))‖)
      (fun n a ω => ?_) h2
    exact norm_le_pi_norm (zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ.1 (s n) (u n)
      (fun b => STExpErrg C (law sz) n (s n) σ.1 b))) a
  exact st6_prec_of_forall_fing sz (law sz) hsz
    (fun n (σ : {σ : Fin 2 → Bool // P σ}) (a : Fin 2 → Zd d (sz.L n)) (_ : sz.SeqΩ) =>
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ.1 (s n) (u n) (fun b => STExpErrg C (law sz) n (s n) σ.1 b)) a‖)
    (fun n _ _ _ => STExpTarget sz n (s n)) key

/-- **A mollifier family** (`Def:QtPt`, `rmk:choosechi`; band `st6_mollifier_family`, `Step6Kit:845`): the property `STMollifierProps` is read at the size coupling `sz.lam n` only (no carrier), so the statement is the band one. -/
theorem st6_mollifier_familyg (sz : Sizes d) (hd : 3 ≤ d) {𝔡 : ℝ} (h𝔡 : 0 < 𝔡) (hWO : sz.WO 𝔡) :
    ∃ Cq c : ℝ, 0 < Cq ∧ 0 < c ∧ ∃ ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ,
      ∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n) :=
  st6_mollifier_family sz hd h𝔡 hWO

end IniTerm

/-! ## 5. The skeletons per carrier (target 8): the cores

Each core is the body of the band skeleton at one `(C, μ, s, t)`: the ingredient pins are replaced by their conclusions there (`hlk`, `hegt`, `hdec`,
`hward`, `hini`, `hduh`, `hint`), `STExpEGtHiConclgL` (from `st6_EGtHi_of_LWg`) is an explicit hypothesis, the initial terms are the conclusions of
`st6_ini_sumNdecayg`, `st6_ini_nonzerog`.  No family, kernel class or comparison hypothesis occurs. -/

section Cores

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The initial term of regimes (iii), (iv) in the shape consumed by the cores (the conclusion of `st6_ini_sumNdecayg`). -/
private abbrev Step6KitGen_Ini3 (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖Step2Gen_UN C n p.2.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1 b) p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n))

/-- Regimes (iii), (iv) close the same way (`ST_step6_caseIII/IV_of_pins`, `Step6Kit:737-830`): from the integrated estimate and the initial term. -/
private theorem Step6KitGen_close34 {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcmp : ∀ n (p : STIdx2 sz s t n),
      ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) ≤
        5 * STExpTarget sz n (p.1 : ℝ))
    (hint : STExpIntConclgL C μ ∅ STSigAll s t) (hini : Step6KitGen_Ini3 C μ s t) : STStep6ConclgL C μ s t := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hini' : PrecL sz μ (U := STIdx2P sz STSigAll s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) := by
    have := StochDomAt.precomp_param hini (fun n (p : STIdx2P sz STSigAll s t n) =>
      ((p.1, p.2.1.1, p.2.2) : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
    simp only [st5_zeroModeSet_empty]
    exact this
  have hF0 : ∀ n (p : STIdx2P sz STSigAll s t n),
      0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n) := by
    intro n p
    have hx : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) :=
      div_nonneg (by linarith [hst n, ht1 n]) (by linarith [p.1.2.2, ht1 n])
    exact mul_nonneg (pow_nonneg hx 2) (st6_target_nonneg sz n (lt_trans (hst n) (ht1 n)))
  have hmain := hint (fun n p => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n)) hF0 hini'
  have h5 := Step5CasesGen_prec_mono sz μ hsz (c := 5) hmain
    (Eventually.of_forall fun n p ω => hcmp n ⟨p.1, p.2.1, p.2.2⟩)
    (fun n p ω => st6_target_nonneg sz n (lt_of_le_of_lt p.1.2.2 (ht1 n)))
  have h6 := StochDomAt.precomp_param h5 (fun n (p : STIdx2 sz s t n) =>
    ((p.1, ⟨p.2.1, trivial⟩, p.2.2) : STIdx2P sz STSigAll s t n))
  simp only [st5_zeroModeSet_empty] at h6
  exact h6

/-- **Step 6, regime (iii), per carrier** (band `ST_step6_caseIII_of_pins`, `Step6Kit:737`): the drift bounds `hlk`, `hegt`, the Duhamel identity
`hduh`, the integrated estimate `hint` and the initial term `hini` give `(Eq:Gtlp_exp_flow)`; the initial term closes by `st6_xB_III`,
`st6_cmp_ini` with the constant `4`, no `𝔠_d` loss. -/
theorem st6_caseIII_coreg {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hR : STReg5III sz s t) (hlk : STExpLKLKHiConclgL C μ s t) (hegt : STExpEGtHiConclgL C μ s t)
    (hduh : STExpDuhEqgL C μ s t)
    (hint : STExpDuhEqgL C μ s t → STExpDriftHiConclgL C μ s t → STExpIntConclgL C μ ∅ STSigAll s t)
    (hini : PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖Step2Gen_UN C n p.2.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n))) : STStep6ConclgL C μ s t :=
  Step6KitGen_close34 C μ hadm hs0 hst ht1 (fun n p => by
    have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have hxB := st6_xB_III sz n p.1.2.1 hu1 ((hR n).trans (by linarith [p.1.2.2]))
    have := st6_cmp_ini sz n p.1.2.1 hu1 hxB
    linarith) (hint hduh ⟨hlk, hegt⟩) hini

/-- **Step 6, regime (iv), per carrier** (band `ST_step6_caseIV_of_pins`, `Step6Kit:786`): `hlo` is the conclusion of `STExpDriftLogL` (its premise
`(res_ELK_n=1)` is `hAvgU`); the initial term closes by `st6_xB_IV` (constant `4`). -/
theorem st6_caseIV_coreg {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hR : STReg5IV sz s t) (hAvgU : STExpAvgUgL C μ s t)
    (hlo : STExpAvgUgL C μ s t → STExpDriftLoConclgL C μ s t) (hduh : STExpDuhEqgL C μ s t)
    (hint : STExpDuhEqgL C μ s t → STExpDriftLoConclgL C μ s t → STExpIntConclgL C μ ∅ STSigAll s t)
    (hini : PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p _ => ‖Step2Gen_UN C n p.2.1 (s n) (p.1 : ℝ) (fun b => STExpErrg C μ n (s n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz n (s n))) : STStep6ConclgL C μ s t :=
  Step6KitGen_close34 C μ hadm hs0 hst ht1 (fun n p => by
    have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have hxB := st6_xB_IV sz n p.1.2.1 hu1 (hR n)
    have := st6_cmp_ini sz n p.1.2.1 hu1 hxB
    linarith) (hint hduh (hlo hAvgU)) hini

/-- **Step 6, regime (ii), per carrier** (band `ST_step6_caseII_of_pins`, `Step6Kit:865`): the integrated estimate `hint` gives `Q^{({1,2})} f_u`
(`σ₁ ≠ σ₂`) and `f_u` (`σ₁ = σ₂`, `A = ∅`) from the initial terms `hiniM`, `hiniS` (`st6_ini_nonzerog`); the Ward decomposition `hward`
(`≺ B³ ≤ T`) closes `σ₁ ≠ σ₂`; the two sign classes are glued by `st6_cover_exp2Ug`. -/
theorem st6_caseII_coreg {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hR : STReg5II sz s t) (hlk : STExpLKLKHiConclgL C μ s t) (hegt : STExpEGtHiConclgL C μ s t)
    (hAvgU : STExpAvgUgL C μ s t) (hduh : STExpDuhEqgL C μ s t)
    (hint : STExpDuhEqgL C μ s t → STExpDriftHiConclgL C μ s t →
      STExpIntConclgL C μ (Finset.univ : Finset (Fin 2)) STSigMixed s t ∧ STExpIntConclgL C μ ∅ STSigSame s t)
    (hward : STExpAvgUgL C μ s t → STExpWardIIConclgL C μ s t)
    (hiniM : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2)) (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget sz n (s n)))
    (hiniS : PrecL sz μ (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
        (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget sz n (s n))) : STStep6ConclgL C μ s t := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hint' := hint hduh ⟨hlk, hegt⟩
  have hward' := hward hAvgU
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  have hmainM := hint'.1 (fun n p => STExpTarget sz n (s n)) (fun n p => hT0 n (s n) (hst n).le) hiniM
  have hmainS := hint'.2 (fun n p => STExpTarget sz n (s n)) (fun n p => hT0 n (s n) (hst n).le) hiniS
  -- `σ₁ = σ₂`
  have hS : PrecL sz μ (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    simp only [st5_zeroModeSet_empty] at hmainS
    refine Step5CasesGen_prec_mono sz μ hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have := st6_target_mono sz n p.1.2.1 (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) ≤ 2 * STExpTarget sz n (p.1 : ℝ)
    linarith
  -- `σ₁ ≠ σ₂`
  have hM : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainM hward'
    have hsum' : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
          (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2 -
          zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
            (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖
      calc ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
              (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            (STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2 -
              zeroModeSet d (sz.L n) (Finset.univ : Finset (Fin 2))
                (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    refine Step5CasesGen_prec_mono sz μ hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h1 := st6_target_mono sz n p.1.2.1 (lt_of_le_of_lt p.1.2.2 (ht1 n))
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (s n) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2Ug sz μ (ξ := fun n u σ a => ‖STExpErrg C μ n (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

/-- **Step 6, regime (i), per carrier** (band `ST_step6_caseI_of_pins`, `Step6Kit:947`).  `σ₁ = σ₂`: the plain Duhamel (`hint.1`) with the initial term
`hini.1`; `σ₁ ≠ σ₂`: for a mollifier family (`st6_mollifier_familyg`) the `𝒬`-Duhamel (`hint.2`, identity `hDuQ`) with the initial term `hini.2` and
`f_u = 𝒬_u f_u + (𝒫 f_u) ϑ_u`, `(𝒫 f_u) ϑ_u ≺ B³` from the Ward conclusion `hward` (`(eq:EPL-K)`). -/
theorem st6_caseI_coreg {𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (h𝔡 : 0 < 𝔡) (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ}
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t)
    (hlk : STExpLKLKHiConclgL C μ s t) (hegt : STExpEGtHiConclgL C μ s t) (hdec : STExpDriftDecayConclgL C μ s t)
    (hAvgU : STExpAvgUgL C μ s t) (hward : STExpAvgUgL C μ s t → STExpWardIConclgL C μ s t)
    (hini : STExpIniIConclgL C μ s t) (hduh : STExpDuhEqgL C μ s t)
    (hDuQ : ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := d) (sz.lam n) Cq c (ϑ n)) → STExpDuhEqQgL C μ s t ϑ)
    (hint : STExpDuhEqgL C μ s t → STExpDriftHiConclgL C μ s t → STExpDriftDecayConclgL C μ s t →
      STExpWardIConclgL C μ s t → STExpIntConclgL C μ ∅ STSigSame s t ∧ STExpIntQConclgL C μ s t) :
    STStep6ConclgL C μ s t := by
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hward' := hward hAvgU
  have hint' := hint hduh ⟨hlk, hegt⟩ hdec hward'
  have hT0 : ∀ n (u : ℝ), u ≤ t n → 0 ≤ STExpTarget sz n u := fun n u hu =>
    st6_target_nonneg sz n (lt_of_le_of_lt hu (ht1 n))
  -- `σ₁ = σ₂`
  have hS : PrecL sz μ (U := STIdx2P sz STSigSame s t)
      (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hiniS : PrecL sz μ (U := STIdx2P sz STSigSame s t)
        (fun n p _ => ‖zeroModeSet d (sz.L n) ∅ (Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STExpErrg C μ n (s n) p.2.1.1 b)) p.2.2‖)
        (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
      simp only [st5_zeroModeSet_empty]
      exact hini.1
    have hmainS := hint'.1 (fun n p => STExpTarget sz n (p.1 : ℝ)) (fun n p => hT0 n _ p.1.2.2) hiniS
    simp only [st5_zeroModeSet_empty] at hmainS
    refine Step5CasesGen_prec_mono sz μ hsz (c := 2) hmainS (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    linarith
  -- `σ₁ ≠ σ₂`
  obtain ⟨Cq, c', hC, hc', ϑ, hϑ⟩ := st6_mollifier_familyg sz hd h𝔡 hadm.2.2.2.2
  have hmainQ := hint'.2 Cq c' ϑ hϑ (hDuQ Cq c' ϑ hϑ) (fun n p => STExpTarget sz n (p.1 : ℝ))
    (fun n p => hT0 n _ p.1.2.2) (hini.2 Cq c' ϑ hϑ)
  have hw := (hward' Cq c' ϑ hϑ).1
  have hM : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
      (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖) (fun n p _ => STExpTarget sz n (p.1 : ℝ)) := by
    have hsum := StochDomAt.add (tendsto_size sz hsz) hmainQ hw
    have hsum' : PrecL sz μ (U := STIdx2P sz STSigMixed s t)
        (fun n p _ => ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖)
        (fun n p _ => (STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ)) + (sz.Bctl n (p.1 : ℝ)) ^ 3) := by
      refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
      change ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖ ≤
        ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖ +
        ‖STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2‖
      calc ‖STExpErrg C μ n (p.1 : ℝ) p.2.1.1 p.2.2‖
          = ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2 +
            STPsum (d := d) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) (p.2.2 0) * ϑ n (p.1 : ℝ) p.2.2‖ := by
            unfold STQop; ring_nf
        _ ≤ _ := norm_add_le _ _
    refine Step5CasesGen_prec_mono sz μ hsz (c := 3) hsum' (Eventually.of_forall fun n p ω => ?_)
      (fun n p ω => hT0 n _ p.1.2.2)
    have h2 := st6_cube_le_target sz n (lt_of_le_of_lt p.1.2.2 (ht1 n))
    change STExpTarget sz n (p.1 : ℝ) + STExpTarget sz n (p.1 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ 3 ≤
      3 * STExpTarget sz n (p.1 : ℝ)
    linarith
  exact st6_cover_exp2Ug sz μ (ξ := fun n u σ a => ‖STExpErrg C μ n (u : ℝ) σ a‖)
    (ζ := fun n u _ _ => STExpTarget sz n (u : ℝ)) hsz (P₁ := STSigSame) (P₂ := STSigMixed)
    (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h]) hS hM

end Cores

/-! ## 6. The skeletons per family (target 8): the wrappers

Family premises, as used (ticket table, U5S-C3): `hμ` (probability laws), `hFF` (`Step5CasesGen_FlowFacts`: admissibility, `T0 < 1`), `hRot` (F7), `hK1` (`𝒦^{(1)}_{+,a} = m` at the times
`[0,1)`, behind `LWAvgLawgL_of_STAvgUgL_at`), the kernel pins `hSum`, `hNZ`, the coupling `gK` and `hKer` (one bulk datum `κm` per `κ`, before `(sz, z)`: `κm ≤ Im m`, the class `Ker` at `κm`,
`0 < gK ≤ 𝔡⁻¹` eventually, and R1 at `Aof κm` in regime (ii)), `hLW` (`LWtermEXPG`), and the ingredient pins of the regime. -/

section Wrappers

variable {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
  {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
  {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}

/-- **Step 6, regime (iii), from its pins** (band `ST_step6_caseIII_of_pins`, `Step6Kit:737`): the ingredients are `STExpLKLKHigL`, `LWtermEXPG`, the Duhamel
family `STExpDuhamelZgL`, the integrated estimate `STExpIntIIIgL` and the kernel pin `hSum`; the constant `𝔠d` is the minimum of those of the two ingredient pins. -/
theorem ST_step6_caseIII_of_pinsgL {Ker : STEKKer d} (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRot : ∀ sz z, Step2EventsGen_Rot3 (mk sz z))
    (hK1 : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    (hSum : STEKSumNdecaygL d law Ker)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ ∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹)
    (hLW : LWtermEXPG d law Flow mk T0) (hDu : STExpDuhamelZgL d law Flow mk)
    (hLK : STExpLKLKHigL d law Flow mk T0) (hInt : STExpIntIIIgL d law Flow mk T0) :
    STStep6IIIgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  refine ⟨min c₁ c₂, hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
  obtain ⟨himm, hKer', hg'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  have hHi := st6_hi_of_reg5III sz hR
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (mk sz z) (law sz) s t (hμ sz) hadm.2.2.1 (fun n => (hst n).le) hHi (hRot sz z)
    (fun u hsu hut => hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
      (fun n => (hut n).trans (htT n)) (STLocalEntrygL_of_STLocalEntryUgL_at (mk sz z) hsu hut hS2.1)
      (LWAvgLawgL_of_STAvgUgL_at (mk sz z) hsu hut (hK1 sz z) hs0 ht1 hS2.2)
      (STLmaxgL_of_STLmaxUgL_at (mk sz z) hsu hut hLmax) (STLKgL_of_STLKUgL_at (mk sz z) hsu hut hLKU)
      (STDecaygL_of_STGdecayWgL_at (mk sz z) hsu hut hS5))
  have hduh := st6_duhEq_of_ping hDu hκ hflow hs0 ht1
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_right _ _)) hS2 hLmax hLKU hS5
  have hini := st6_ini_sumNdecayg hSum hd hκm hadm (mk sz z) (gK sz z) hKer' hg' (hμ sz) hs0 hst ht1 hExp
  exact st6_caseIII_coreg (mk sz z) (law sz) hadm hs0 hst ht1 hR hlk hegt hduh hint hini

/-- **Step 6, regime (iv), from its pins** (band `ST_step6_caseIV_of_pins`, `Step6Kit:786`): `STExpDriftLogL` carries `(eq:Exp(L-K)2)`,
`(eq:ExpLWn=2_smalleta)`; its premise `(res_ELK_n=1)` is compiled from `STImproveExpAvergL` (`st6_expAvgU_of_ping`). -/
theorem ST_step6_caseIV_of_pinsgL {Ker : STEKKer d} (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hK1 : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    (hSum : STEKSumNdecaygL d law Ker)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ ∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹)
    (hAvg : STImproveExpAvergL d law Flow mk T0) (hDu : STExpDuhamelZgL d law Flow mk)
    (hLo : STExpDriftLogL d law Flow mk T0) (hInt : STExpIntIVgL d law Flow mk T0) :
    STStep6IVgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLo hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  refine ⟨min c₁ c₂, hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
  obtain ⟨himm, hKer', hg'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  have hAvgU := st6_expAvgU_of_ping hAvg hd hκ hε h𝔡 hflow (hμ sz) hadm.2.2.1 (hK1 sz z) hs0 hst htT ht1 hS2 hLKU
  have hlo := H₁ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_ping hDu hκ hflow hs0 ht1
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_right _ _)) hS2 hLmax hLKU hS5
  have hini := st6_ini_sumNdecayg hSum hd hκm hadm (mk sz z) (gK sz z) hKer' hg' (hμ sz) hs0 hst ht1 hExp
  exact st6_caseIV_coreg (mk sz z) (law sz) hadm hs0 hst ht1 hR hAvgU hlo hduh hint hini

/-- **Step 6, regime (ii), from its pins** (band `ST_step6_caseII_of_pins`, `Step6Kit:865`).  The initial terms are `st6_ini_nonzerog` (the pin `hNZ` with the A-form window; the comparison R1 `hR1` is read only there). -/
theorem ST_step6_caseII_of_pinsgL {Ker : STEKKer d} {Aof : ℝ → ℝ} (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRot : ∀ sz z, Step2EventsGen_Rot3 (mk sz z))
    (hK1 : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    (hNZ : STEKNonzerogL d law Ker Aof) (hAof : ∀ κm : ℝ, 0 < κm → 1 ≤ Aof κm)
    (hKer : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n, κm ≤ ((mk sz z).m n).im) ∧ Ker sz (mk sz z) (gK sz z) κm ∧ (∀ᶠ n in atTop, 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹) ∧
        ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κm * gK sz z n ^ 2)
    (hLW : LWtermEXPG d law Flow mk T0) (hAvg : STImproveExpAvergL d law Flow mk T0)
    (hDu : STExpDuhamelZgL d law Flow mk) (hLK : STExpLKLKHigL d law Flow mk T0)
    (hInt : STExpIntIIgL d law Flow mk T0) (hWd : STExpWardIIgL d law Flow mk T0) :
    STStep6IIgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ c₃) := lt_min hc₁ (lt_min hc₂ hc₃)
  refine ⟨min c₁ (min c₂ c₃), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp hcon hS2 hLmax hLKU hS5
  obtain ⟨_, _, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, -, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  obtain ⟨κm, hκm, hKF⟩ := hKer κ hκ
  obtain ⟨himm, hKer', hg', hR1'⟩ := hKF sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  have hHi := st6_hi_of_reg5II sz hR
  have hAvgU := st6_expAvgU_of_ping hAvg hd hκ hε h𝔡 hflow (hμ sz) hadm.2.2.1 (hK1 sz z) hs0 hst htT ht1 hS2 hLKU
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)) hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (mk sz z) (law sz) s t (hμ sz) hadm.2.2.1 (fun n => (hst n).le) hHi (hRot sz z)
    (fun u hsu hut => hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
      (fun n => (hut n).trans (htT n)) (STLocalEntrygL_of_STLocalEntryUgL_at (mk sz z) hsu hut hS2.1)
      (LWAvgLawgL_of_STAvgUgL_at (mk sz z) hsu hut (hK1 sz z) hs0 ht1 hS2.2)
      (STLmaxgL_of_STLmaxUgL_at (mk sz z) hsu hut hLmax) (STLKgL_of_STLKUgL_at (mk sz z) hsu hut hLKU)
      (STDecaygL_of_STGdecayWgL_at (mk sz z) hsu hut hS5))
  have hduh := st6_duhEq_of_ping hDu hκ hflow hs0 ht1
  have hint := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))) hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec hExp
    (st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_right _ _))) hS2 hLmax hLKU hS5
  have hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n := fun n => by linarith [(hR n).2]
  exact st6_caseII_coreg (mk sz z) (law sz) hadm hs0 hst ht1 hR hlk hegt hAvgU hduh hint hward
    (st6_ini_nonzerog hNZ hd hκm (hAof κm hκm) hadm (mk sz z) (gK sz z) hKer' hg' hR1' (hμ sz) hs0 hst ht1 hsg hExp
      (Finset.univ : Finset (Fin 2)) STSigMixed (fun σ _ i _ => Finset.mem_univ i))
    (st6_ini_nonzerog hNZ hd hκm (hAof κm hκm) hadm (mk sz z) (gK sz z) hKer' hg' hR1' (hμ sz) hs0 hst ht1 hsg hExp
      (∅ : Finset (Fin 2)) STSigSame (fun σ hσ i hi => absurd hi (st6_Idiff_same hσ i)))

/-- **Step 6, regime (i), from its pins** (band `ST_step6_caseI_of_pins`, `Step6Kit:947`).  `σ₁ ≠ σ₂` needs a mollifier family (`st6_mollifier_familyg`) and the
`𝒬`-Duhamel family `STExpDuhamelQgL`; the premise `(res_ELK_n=1)` of the Ward pin is compiled from `STImproveExpAvergL`. -/
theorem ST_step6_caseI_of_pinsgL (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hRot : ∀ sz z, Step2EventsGen_Rot3 (mk sz z))
    (hK1 : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 →
      (mk sz z).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (mk sz z).m n)
    (hLW : LWtermEXPG d law Flow mk T0) (hAvg : STImproveExpAvergL d law Flow mk T0)
    (hDu : STExpDuhamelZgL d law Flow mk) (hDuQ : STExpDuhamelQgL d law Flow mk)
    (hLK : STExpLKLKHigL d law Flow mk T0) (hDec : STExpDriftDecaygL d law Flow mk T0)
    (hWd : STExpWardIgL d law Flow mk T0) (hIni : STExpIniIgL d law Flow mk T0) (hInt : STExpIntIgL d law Flow mk T0) :
    STStep6IgL d law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hLK hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hDec hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hIni hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := hInt hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₁ (min c₂ (min c₃ (min c₄ c₅))) :=
    lt_min hc₁ (lt_min hc₂ (lt_min hc₃ (lt_min hc₄ hc₅)))
  refine ⟨min c₁ (min c₂ (min c₃ (min c₄ c₅))), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hcon hS2 hLmax hLKU hS5
  obtain ⟨κm, hκm, hFl⟩ := hFF κ hκ
  obtain ⟨hadm, hT0, himm, -⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hT0 n)
  have m : ∀ c', min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hm1 := m c₁ (min_le_left _ _)
  have hm2 := m c₂ ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 := m c₃ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 := m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 := m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hHi := st6_hi_of_reg5I sz (by omega) hR
  have hAvgU := st6_expAvgU_of_ping hAvg hd hκ hε h𝔡 hflow (hμ sz) hadm.2.2.1 (hK1 sz z) hs0 hst htT ht1 hS2 hLKU
  have hlk := H₁ 𝔠 sz z hflow s t hs0 hst htT hHi hLK0 hDec0 hExp hm1 hS2 hLmax hLKU hS5
  have hegt := st6_EGtHi_of_LWg (mk sz z) (law sz) s t (hμ sz) hadm.2.2.1 (fun n => (hst n).le) hHi (hRot sz z)
    (fun u hsu hut => hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (fun n => (hs0 n).trans (hsu n))
      (fun n => (hut n).trans (htT n)) (STLocalEntrygL_of_STLocalEntryUgL_at (mk sz z) hsu hut hS2.1)
      (LWAvgLawgL_of_STAvgUgL_at (mk sz z) hsu hut (hK1 sz z) hs0 ht1 hS2.2)
      (STLmaxgL_of_STLmaxUgL_at (mk sz z) hsu hut hLmax) (STLKgL_of_STLKUgL_at (mk sz z) hsu hut hLKU)
      (STDecaygL_of_STGdecayWgL_at (mk sz z) hsu hut hS5))
  have hdec := H₂ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm2 hS2 hLmax hLKU hS5
  have hward := H₃ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm3 hS2 hLmax hLKU hS5
  have hini := H₄ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm4 hS2 hLmax hLKU hS5
  have hduh := st6_duhEq_of_ping hDu hκ hflow hs0 ht1
  have hint := H₅ 𝔠 sz z hflow s t hs0 hst htT hR hLK0 hDec0 hExp hm5 hS2 hLmax hLKU hS5
  exact st6_caseI_coreg (mk sz z) (law sz) hd h𝔡 hadm hs0 hst ht1 hR hlk hegt hdec hAvgU hward hini hduh
    (fun Cq c ϑ hϑ => st6_duhEqQ_of_ping hDuQ hκ hflow hs0 ht1 Cq c ϑ hϑ) hint

end Wrappers

/-! ## 7. Two lemmas of the probe's section 7b -/

section Mono

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `(Eq:Gdecay_flow)` without loss implies `(Eq:Gdecay_w)` with any loss `C_d ≥ 0` (band `st6_GdecayW_of_zero`, `Step6Kit:1046`). -/
theorem st6_GdecayW_of_zerog (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (h : STGdecayWgL C μ s t 0) : STGdecayWgL C μ s t Cd := by
  intro D hD
  refine Step5CasesGen_prec_mono sz μ hsz (c := 1) (h D hD) (Eventually.of_forall fun n p ω => ?_) (fun n p ω => ?_)
  · have h1 : 0 < 1 - (p.1 : ℝ) := by linarith [ht1 n, p.1.2.2]
    have hu : (1 : ℝ) ≤ (1 - s n) / (1 - (p.1 : ℝ)) := by
      rw [le_div_iff₀ h1]; linarith [p.1.2.1]
    have hr : (1 : ℝ) ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd := Real.one_le_rpow hu hCd
    have hB : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.rpow_nonneg (STBctl_pos sz n (by linarith [ht1 n, p.1.2.2])).le _
    have hW : 0 ≤ STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
      unfold STWB Bparam; positivity
    have hX : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) * STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) := by
      positivity
    simp only [Real.rpow_zero, one_mul]
    nlinarith
  · have h1 : 0 < 1 - (p.1 : ℝ) := by linarith [ht1 n, p.1.2.2]
    have hu : (1 : ℝ) ≤ (1 - s n) / (1 - (p.1 : ℝ)) := by
      rw [le_div_iff₀ h1]; linarith [p.1.2.1]
    have hbase : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) := by linarith
    have hB : 0 ≤ (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.rpow_nonneg (STBctl_pos sz n (by linarith [ht1 n, p.1.2.2])).le _
    have hW : 0 ≤ STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
      unfold STWB Bparam; positivity
    have hr0 : 0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd := Real.rpow_nonneg hbase _
    have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hE0 := (Real.exp_pos (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ))).le
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr0 hB) hW) hE0) hW0

end Mono

/-- The pin of a regime `R'` follows from the pin of a larger regime `R` (band `ST_step6R_mono`, `Step6Kit:1078`; `STAny` is the largest). -/
theorem ST_step6R_monogL {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ}
    {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz}
    {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ} {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STStep6RgL d R law Flow mk T0) :
    STStep6RgL d R' law Flow mk T0 := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hst htT hR' => H 𝔠 sz z hflow s t hs0 hst htT (hRR sz s t hR')⟩

end RBM.BA

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Gauss.Step6Inst

/-! ## 8. Compiled nonempty instances at `d = 3` (target 9)

Data: the merged ones of `Step6Pins` §8 and `Step6Kit` §8 (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `sz0`, `szB`, `szG`, `n = 0`, `E = 1/2`) at `bandFM`.  Discharged: flow,
time ranges, regime, law, admissibility, the kernel pins `stek_*gL_band` and the class `STEKBandKer`, flow facts, F7, the one-loop datum.  Hypotheses: pins of another
gate (`LWtermEXPG` and its per-`u` bound, the ingredient pins and Duhamel families of rows b, c and V1s2'/V1s3', `(Eq:Gtlp_exp+IND)` at `s`). -/

section Instances

/-- The one-loop datum of the band carrier: `𝒦^{(1)}_{+,a} = m(E)` (`ST_Kloop_one`). -/
private theorem Step6KitGen_K1_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)) (_ : 0 ≤ τ) (_ : τ < 1) :
    (bandFM sz E).K n τ (fun _ : Fin 1 => true) (fun _ => a) = (bandFM sz E).m n :=
  ST_Kloop_one sz n (E n) τ true a

/-- The class `STEKBandKer` at every bulk datum of a band flow. -/
private theorem Step6KitGen_Ker_band {d : ℕ} : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ →
    STFlow sz κ ε 𝔠 𝔡 z → ∀ κm : ℝ, 0 < κm → (∀ n, κm ≤ ((bandFM sz (STflowE z)).m n).im) →
      STEKBandKer sz (bandFM sz (STflowE z)) sz.lam κm :=
  fun sz κ _ _ _ z hκ hflow κm _ himm =>
    ⟨STflowE z, rfl, rfl, fun n => ⟨(st6_flowE_le sz hflow n).trans (by linarith), himm n⟩⟩

/-- **Targets 5, 6**: the glue at `sz0` (the deterministic family `F = 1 - u`, `G = 2 (1 - u)` on `[0, 1/2]`, index set `Bool`). -/
example : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
    ∀ v : TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n × Bool,
      1 - (v.1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ τ * (2 * (1 - (v.1 : ℝ))) :=
  (st6_prec_det_iffg sz0 (Sizes.seqP sz0) inferInstance sz0_tendsto
    (V := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n × Bool)
    (fun _ p => 1 - (p.1 : ℝ)) (fun _ p => 2 * (1 - (p.1 : ℝ)))).1 inst_precU

example : PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n × Bool)
    (fun _ p _ => 1 - (p.1 : ℝ)) (fun _ p _ => 2 * (1 - (p.1 : ℝ))) :=
  st6_precU_of_forall_seqg sz0 (Sizes.seqP sz0) inferInstance sz0_tendsto (fun n => by norm_num) (W := fun _ => Bool)
    (fun _ u _ => 1 - u) (fun _ u _ => 2 * (1 - u))
    (fun u hsu hut => prec_of_le sz0 (fun n w ω => by have h : u n ≤ 1 / 2 := hut n; change 0 ≤ 2 * (1 - u n); linarith)
      (fun n w ω => by have h : u n ≤ 1 / 2 := hut n; change 1 - u n ≤ 2 * (1 - u n); linarith))

/-- The bridges at the section `u ≡ 1/32 ∈ [0, 1/16]` (the five premises of `LWtermEXPG`): the uniform statements stay hypotheses. -/
example (hLE : STLocalEntryUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hAvg : STAvgUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hLmax : STLmaxUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hLK : STLKUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hDec : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst 0) :
    STLocalEntrygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 1 / 32) ∧
      LWAvgLawgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 1 / 32) ∧
      STLmaxgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 1 / 32) ∧
      STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 1 / 32) ∧
      STDecaygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 1 / 32) :=
  ⟨STLocalEntrygL_of_STLocalEntryUgL_at _ (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hLE,
    LWAvgLawgL_of_STAvgUgL_at _ (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) (Step6KitGen_K1_band sz0 (STflowE z0)) sz0_hs0 (fun n => by simp only [tInst]; norm_num) hAvg,
    STLmaxgL_of_STLmaxUgL_at _ (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hLmax,
    STLKgL_of_STLKUgL_at _ (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hLK,
    STDecaygL_of_STGdecayWgL_at _ (fun n => by simp only [sInst]; norm_num)
      (fun n => by simp only [tInst]; norm_num) hDec⟩

example (hLE : STLocalEntryUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :
    STLocalEntrygL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst :=
  STLocalEntrygL_of_STLocalEntryUgL _ (fun n => (sz0_hst n).le) hLE

/-- The sup norm over the labels of `f_s` is `≺ T_s` if the entries are: from `(Eq:Gtlp_exp+IND)` at `s = 0` (a hypothesis). -/
example (hExp : STExp2gL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst) (σ : Fin 2 → Bool) :
    PrecL sz0 (Sizes.seqP sz0) (U := fun _ => Unit)
      (fun n _ _ => ‖(fun b => STExpErrg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) n (sInst n) σ b)‖)
      (fun n _ _ => STExpTarget sz0 n (sInst n)) :=
  st6_prec_pi_normg sz0 (Sizes.seqP sz0) sz0_tendsto
    (fun n => st6_target_nonneg sz0 n (by simp only [sInst]; norm_num)) (bandFM sz0 (STflowE z0)) hExp σ

example : PrecL sz0 (Sizes.seqP sz0) (U := fun n => Bool × Unit)
    (fun _ p _ => if p.1 then (1 : ℝ) else 0) (fun _ _ _ => (1 : ℝ)) :=
  st6_prec_of_forall_fing sz0 (Sizes.seqP sz0) sz0_tendsto (ι := Bool) (V := fun _ => Unit)
    (fun _ i _ _ => if i then (1 : ℝ) else 0) (fun _ _ _ _ => (1 : ℝ))
    (fun i => prec_of_le sz0 (fun n w ω => by norm_num) (fun n w ω => by cases i <;> norm_num))

example : PrecL sz0 (Sizes.seqP sz0)
    (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
    (fun n p _ => 1 - (p.1 : ℝ)) (fun n p _ => 2 * (1 - (p.1 : ℝ))) :=
  st6_cover_exp2Ug sz0 (Sizes.seqP sz0) (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
    (ξ := fun n u _ _ => 1 - (u : ℝ)) (ζ := fun n u _ _ => 2 * (1 - (u : ℝ))) sz0_tendsto
    (P₁ := STSigSame) (P₂ := STSigMixed) (fun σ => by by_cases h : σ 0 = σ 1 <;> simp [STSigSame, STSigMixed, h])
    (prec_of_le sz0 (fun n p ω => by have h := p.1.2.2; change (p.1 : ℝ) ≤ 1 / 2 at h; change 0 ≤ 2 * (1 - (p.1 : ℝ)); linarith)
      (fun n p ω => by have h := p.1.2.2; change (p.1 : ℝ) ≤ 1 / 2 at h; change 1 - (p.1 : ℝ) ≤ 2 * (1 - (p.1 : ℝ)); linarith))
    (prec_of_le sz0 (fun n p ω => by have h := p.1.2.2; change (p.1 : ℝ) ≤ 1 / 2 at h; change 0 ≤ 2 * (1 - (p.1 : ℝ)); linarith)
      (fun n p ω => by have h := p.1.2.2; change (p.1 : ℝ) ≤ 1 / 2 at h; change 1 - (p.1 : ℝ) ≤ 2 * (1 - (p.1 : ℝ)); linarith))

/-- **Target 6**: `STEGt = LWE` and `𝔼 STEGt = 𝔼 LWE` at `(sz0, z0, n = 0, u = 1/32)`, the loop `((+,-), (0, e₁))` (F7 of the band carrier). -/
example (ω : sz0.SeqΩ) :
    STEGtg (bandFM sz0 (STflowE z0)) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ω =
      LWEg (bandFM sz0 (STflowE z0)) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ω :=
  st6_EGt_eq_LWEg _ (Step2EventsGen_bandRot3 sz0 (STflowE z0)) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ω

example : STExpEGtg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] =
    ∫ ω, LWEg (bandFM sz0 (STflowE z0)) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1] ω ∂(Sizes.seqP sz0) :=
  st6_expEGt_eqg _ _ (Step2EventsGen_bandRot3 sz0 (STflowE z0)) 0 (1 / 32) ![true, false] ![0, Pi.single 0 1]

/-- `(eq:ExpLWn=2)` uniformly in `u ∈ [0, 1/16]` from the LW bound at every section (the conclusion of `LWtermEXPG`, a hypothesis). -/
example (hLW : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
    PrecL sz0 (Sizes.seqP sz0) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - u n})
      (fun n p _ => ‖∫ ω, LWEg (bandFM sz0 (STflowE z0)) n (u n) p.1.1 p.1.2 ω ∂(Sizes.seqP sz0)‖)
      (fun n _ _ => (1 - u n)⁻¹ * (sz0.Bctl n (u n)) ^ (5 / 2 : ℝ))) :
    STExpEGtHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  st6_EGtHi_of_LWg _ _ sInst tInst inferInstance sz0_tendsto (fun n => (sz0_hst n).le) inst_hiIII
    (Step2EventsGen_bandRot3 sz0 (STflowE z0)) hLW

example (hDu : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z))) :
    STExpDuhEqgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  st6_duhEq_of_ping hDu (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 sz0_hs0 (fun n => by simp only [tInst]; norm_num)

example (hDuQ : STExpDuhamelQgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z))) :
    ∃ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) Cq c (ϑ n)) ∧
        STExpDuhEqQgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) ϑ := by
  obtain ⟨Cq, c, -, -, ϑ, hϑ⟩ := st6_mollifier_familyg szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_WO
  exact ⟨Cq, c, ϑ, hϑ, st6_duhEqQ_of_ping hDuQ (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (fun _ => by norm_num)
    (fun _ => by norm_num) Cq c ϑ hϑ⟩

/-- `(res_ELK_n=1)` uniformly from `STImproveExpAvergL`, `STAvgUgL` (in `STStep2CoregL`) and `STLKUgL` at `(sz0, z0, 0, 1/16)`. -/
example (hAvg : STImproveExpAvergL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hS2 : STStep2CoregL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hLKU : STLKUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :
    STExpAvgUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  st6_expAvgU_of_ping hAvg (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 inferInstance sz0_tendsto (Step6KitGen_K1_band sz0 (STflowE z0))
    sz0_hs0 sz0_hst sz0_ht (fun n => by simp only [tInst]; norm_num) hS2 hLKU

/-- **Target 7**: the initial term of regimes (iii), (iv) at `(sz0, z0, 0, 1/16)` from the proved band kernel pin `stek_sumNdecaygL_band` (class `STEKBandKer` at `κm = √(2κ)/2`, `gK = sz0.lam`); `(Eq:Gtlp_exp+IND)` stays a hypothesis. -/
example (hExp : STExp2gL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst) :
    PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖Step2Gen_UN (bandFM sz0 (STflowE z0)) n p.2.1 (sInst n) (p.1 : ℝ)
        (fun b => STExpErrg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) n (sInst n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - sInst n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz0 n (sInst n)) :=
  st6_ini_sumNdecayg (stek_sumNdecaygL_band 3) (by norm_num) (κm := Real.sqrt (2 * (1 / 10)) / 2) (by positivity)
    sz0_admissible (bandFM sz0 (STflowE z0)) sz0.lam
    (Step6KitGen_Ker_band sz0 _ _ _ _ z0 (by norm_num) flow_z0 _ (by positivity)
      (fun n => st6_mE_im_ge (by norm_num) (st6_flowE_le sz0 flow_z0 n)))
    (step34Gen_band_hg sz0_admissible) inferInstance sz0_hs0 sz0_hst (fun n => by simp only [tInst]; norm_num) hExp

/-- The initial term of regime (ii) at `(szB, zB, 15/16, 31/32)`, `A = {1,2}`, `σ₁ ≠ σ₂`: the boundary `1 - s = lam²/L²` of `(sum_res_Ndecay_nonzero)` is hit; the A-form with `Aof = 1`, `gK = szB.lam` (R1 holds with `A = 1`). -/
example (hExp : STExp2gL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16)) :
    PrecL szB (Sizes.seqP szB) (U := STIdx2P szB STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n p _ => ‖zeroModeSet 3 (szB.L n) (Finset.univ : Finset (Fin 2))
        (Step2Gen_UN (bandFM szB (STflowE zB)) n p.2.1.1 (15 / 16) (p.1 : ℝ)
          (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (15 / 16) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget szB n (15 / 16)) :=
  st6_ini_nonzerog (Aof := fun _ => 1) (stek_nonzerogL_band 3) (by norm_num) (κm := Real.sqrt (2 * (1 / 10)) / 2)
    (by positivity) le_rfl szB_admissible (bandFM szB (STflowE zB)) szB.lam
    (Step6KitGen_Ker_band szB _ _ _ _ zB (by norm_num) flow_zB _ (by positivity)
      (fun n => st6_mE_im_ge (by norm_num) (st6_flowE_le szB flow_zB n)))
    (step34Gen_band_hg szB_admissible) (fun n => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩) inferInstance
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun n => by simp [szB]; norm_num) hExp
    Finset.univ STSigMixed (fun σ _ i _ => Finset.mem_univ i)

/-- `0 < lam ≤ 𝔡⁻¹` eventually along a band flow (the premise `hg` of the wrappers at the band class, `gK = sz.lam`). -/
private theorem Step6KitGen_hg_band {d : ℕ} : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ →
    STFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ :=
  fun _ _ _ _ _ _ _ hflow => step34Gen_band_hg hflow.1

/-- The kernel facts of a band flow at the bulk datum `κm = √(2κ)/2`: the premise `hKer` of the wrappers (with R1 at `Aof = 1` for regime (ii)). -/
private theorem Step6KitGen_KerF_band {d : ℕ} : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → (∀ n, κm ≤ ((bandFM sz (STflowE z)).m n).im) ∧
      STEKBandKer sz (bandFM sz (STflowE z)) sz.lam κm ∧ ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ :=
  fun κ hκ => ⟨Real.sqrt (2 * κ) / 2, by positivity, fun sz ε 𝔠 𝔡 z hflow =>
    ⟨fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n), Step6KitGen_Ker_band sz κ ε 𝔠 𝔡 z hκ hflow _ (by positivity)
      (fun n => st6_mE_im_ge hκ (st6_flowE_le sz hflow n)), Step6KitGen_hg_band sz κ ε 𝔠 𝔡 z hκ hflow⟩⟩

private theorem Step6KitGen_KerFR1_band {d : ℕ} : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → (∀ n, κm ≤ ((bandFM sz (STflowE z)).m n).im) ∧
      STEKBandKer sz (bandFM sz (STflowE z)) sz.lam κm ∧ (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹) ∧
      ∀ n, 0 ≤ sz.lam n * sz.lam n ∧ sz.lam n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ (fun _ : ℝ => (1 : ℝ)) κm * sz.lam n ^ 2 :=
  fun κ hκ => let ⟨κm, h0, H⟩ := Step6KitGen_KerF_band κ hκ
    ⟨κm, h0, fun sz ε 𝔠 𝔡 z hflow => let ⟨a, b, c⟩ := H sz ε 𝔠 𝔡 z hflow
      ⟨a, b, c, fun n => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩⟩⟩

example (h : STExpLKLKHigL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst :=
  inst_expLKLK_III ((STExpLKLKHi_iff_gL 3).2 h)

/-- **Target 8, the cores** at the data of their regimes: the conclusions of the ingredient pins and the initial terms stay hypotheses; the administrative facts (admissibility, time ranges, regime) are discharged. -/
example (hlk : STExpLKLKHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hegt : STExpEGtHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hduh : STExpDuhEqgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst)
    (hint : STExpDuhEqgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
      STExpDriftHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
      STExpIntConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) ∅ STSigAll sInst tInst)
    (hini : PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖Step2Gen_UN (bandFM sz0 (STflowE z0)) n p.2.1 (sInst n) (p.1 : ℝ)
        (fun b => STExpErrg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) n (sInst n) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - sInst n) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget sz0 n (sInst n))) :
    STStep6ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst :=
  st6_caseIII_coreg _ _ sz0_admissible sz0_hs0 sz0_hst (fun n => by simp only [tInst]; norm_num) sz0_reg5III hlk hegt hduh hint hini

example (hAvgU : STExpAvgUgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4))
    (hlo : STExpAvgUgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4) →
      STExpDriftLoConclgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4))
    (hduh : STExpDuhEqgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4))
    (hint : STExpDuhEqgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4) →
      STExpDriftLoConclgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4) →
      STExpIntConclgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) ∅ STSigAll (fun _ => 5 / 8) (fun _ => 3 / 4))
    (hini : PrecL szG (Sizes.seqP szG)
      (U := fun n => TimeIcc (fun _ => (5 / 8 : ℝ)) (fun _ => (3 / 4 : ℝ)) n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (szG.L n)))
      (fun n p _ => ‖Step2Gen_UN (bandFM szG (STflowE zB)) n p.2.1 (5 / 8) (p.1 : ℝ)
        (fun b => STExpErrg (bandFM szG (STflowE zB)) (Sizes.seqP szG) n (5 / 8) p.2.1 b) p.2.2‖)
      (fun n p _ => ((1 - (5 / 8 : ℝ)) / (1 - (p.1 : ℝ))) ^ 2 * STExpTarget szG n (5 / 8))) :
    STStep6ConclgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  st6_caseIV_coreg _ _ szG_admissible (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) szG_reg4
    hAvgU hlo hduh hint hini

example (hlk : STExpLKLKHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hegt : STExpEGtHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hAvgU : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hduh : STExpDuhEqgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hint : STExpDuhEqgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpDriftHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpIntConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (Finset.univ : Finset (Fin 2)) STSigMixed
        (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
      STExpIntConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigSame (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hward : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpWardIIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32))
    (hiniM : PrecL szB (Sizes.seqP szB) (U := STIdx2P szB STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n p _ => ‖zeroModeSet 3 (szB.L n) (Finset.univ : Finset (Fin 2))
        (Step2Gen_UN (bandFM szB (STflowE zB)) n p.2.1.1 (15 / 16) (p.1 : ℝ)
          (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (15 / 16) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget szB n (15 / 16)))
    (hiniS : PrecL szB (Sizes.seqP szB) (U := STIdx2P szB STSigSame (fun _ => 15 / 16) (fun _ => 31 / 32))
      (fun n p _ => ‖zeroModeSet 3 (szB.L n) ∅
        (Step2Gen_UN (bandFM szB (STflowE zB)) n p.2.1.1 (15 / 16) (p.1 : ℝ)
          (fun b => STExpErrg (bandFM szB (STflowE zB)) (Sizes.seqP szB) n (15 / 16) p.2.1.1 b)) p.2.2‖)
      (fun n _ _ => STExpTarget szB n (15 / 16))) :
    STStep6ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  st6_caseII_coreg _ _ szB_admissible (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5II
    hlk hegt hAvgU hduh hint hward hiniM hiniS

example (hlk : STExpLKLKHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hegt : STExpEGtHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hdec : STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hAvgU : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hward : STExpAvgUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpWardIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hini : STExpIniIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hduh : STExpDuhEqgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16))
    (hDuQ : ∀ (Cq c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin 2 → Zd 3 (szB.L n)) → ℂ),
      (∀ᶠ n in atTop, STMollifierProps (d := 3) (szB.lam n) Cq c (ϑ n)) →
        STExpDuhEqQgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) ϑ)
    (hint : STExpDuhEqgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpDriftHiConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpWardIConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
      STExpIntConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigSame (fun _ => 7 / 8) (fun _ => 15 / 16) ∧
        STExpIntQConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STStep6ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  st6_caseI_coreg _ _ (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) szB_admissible (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) szB_reg5I hlk hegt hdec hAvgU hward hini hduh hDuQ hint

/-- **Target 8, the wrappers** at the band tuple: every deterministic family premise is discharged (`hμ`, the flow facts `step5CasesGen_flowFacts_band`,
F7 `Step2EventsGen_bandRot3`, the one-loop datum, the proved kernel pins `stek_*gL_band`, the class `STEKBandKer`, `0 < lam ≤ 𝔡⁻¹`, R1 with `Aof = 1`);
the ingredient pins, `LWtermEXPG` and the Duhamel families stay hypotheses; the conclusion is read at the data of the regime through `inst_step6*`. -/
example (hLW : LWtermEXPG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hDu : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)))
    (hLK : STExpLKLKHigL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hInt : STExpIntIIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst :=
  inst_step6III ((STStep6III_iff_gL 3).2
    (ST_step6_caseIII_of_pinsgL (Ker := @STEKBandKer 3) (fun sz _ => sz.lam) (fun sz => inferInstance)
      (step5CasesGen_flowFacts_band 3) (fun sz z => Step2EventsGen_bandRot3 sz (STflowE z))
      (fun sz z => Step6KitGen_K1_band sz (STflowE z)) (stek_sumNdecaygL_band 3)
      Step6KitGen_KerF_band hLW hDu hLK hInt))

example (hAvg : STImproveExpAvergL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hDu : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)))
    (hLo : STExpDriftLogL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hInt : STExpIntIVgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_step6IV ((STStep6IV_iff_gL 3).2
    (ST_step6_caseIV_of_pinsgL (Ker := @STEKBandKer 3) (fun sz _ => sz.lam) (fun sz => inferInstance)
      (step5CasesGen_flowFacts_band 3) (fun sz z => Step6KitGen_K1_band sz (STflowE z)) (stek_sumNdecaygL_band 3)
      Step6KitGen_KerF_band hAvg hDu hLo hInt))

example (hLW : LWtermEXPG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hAvg : STImproveExpAvergL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hDu : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)))
    (hLK : STExpLKLKHigL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hInt : STExpIntIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hWd : STExpWardIIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_step6II ((STStep6II_iff_gL 3).2
    (ST_step6_caseII_of_pinsgL (Ker := @STEKBandKer 3) (Aof := fun _ => 1) (fun sz _ => sz.lam)
      (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3) (fun sz z => Step2EventsGen_bandRot3 sz (STflowE z))
      (fun sz z => Step6KitGen_K1_band sz (STflowE z)) (stek_nonzerogL_band 3) (fun _ _ => le_rfl)
      Step6KitGen_KerFR1_band hLW hAvg hDu hLK hInt hWd))

example (hLW : LWtermEXPG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hAvg : STImproveExpAvergL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hDu : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)))
    (hDuQ : STExpDuhamelQgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)))
    (hLK : STExpLKLKHigL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hDec : STExpDriftDecaygL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hWd : STExpWardIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hIni : STExpIniIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)))
    (hInt : STExpIntIgL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I ((STStep6I_iff_gL 3).2
    (ST_step6_caseI_of_pinsgL (fun sz => inferInstance) (step5CasesGen_flowFacts_band 3)
      (fun sz z => Step2EventsGen_bandRot3 sz (STflowE z)) (fun sz z => Step6KitGen_K1_band sz (STflowE z))
      hLW hAvg hDu hDuQ hLK hDec hWd hIni hInt))

/-- **Section 7b**: `(Eq:Gdecay_flow)` without loss gives the lossy form at `(sz0, 0, 1/16)`; the general pin gives the regime (i) pin. -/
example (h : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst 0) :
    STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst 1 :=
  st6_GdecayW_of_zerog _ _ sz0_tendsto (fun n => by simp only [tInst]; norm_num) zero_le_one h

example (h : STStep6gL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_step6I ((STStep6I_iff_gL 3).2 (ST_step6R_monogL (fun _ _ _ _ => trivial) h))

end Instances

end RBM.BA

end
