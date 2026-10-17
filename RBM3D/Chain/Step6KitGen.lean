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

end Cores

/-! ## 6. The skeletons per family (target 8): the wrappers

Family premises, as used (ticket table, U5S-C3): `hμ` (probability laws), `hFF` (`Step5CasesGen_FlowFacts`: admissibility, `T0 < 1`), `hRot` (F7), `hK1` (`𝒦^{(1)}_{+,a} = m` at the times
`[0,1)`, behind `LWAvgLawgL_of_STAvgUgL_at`), the kernel pins `hSum`, `hNZ`, the coupling `gK` and `hKer` (one bulk datum `κm` per `κ`, before `(sz, z)`: `κm ≤ Im m`, the class `Ker` at `κm`,
`0 < gK ≤ 𝔡⁻¹` eventually, and R1 at `Aof κm` in regime (ii)), `hLW` (`LWtermEXPG`), and the ingredient pins of the regime. -/

/-! ## 7. Two lemmas of the probe's section 7b -/

end RBM.BA

/-! ## 8. Compiled nonempty instances at `d = 3` (target 9)

Data: the merged ones of `Step6Pins` §8 and `Step6Kit` §8 (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `sz0`, `szB`, `szG`, `n = 0`, `E = 1/2`) at `bandFM`.  Discharged: flow,
time ranges, regime, law, admissibility, the kernel pins `stek_*gL_band` and the class `STEKBandKer`, flow facts, F7, the one-loop datum.  Hypotheses: pins of another
gate (`LWtermEXPG` and its per-`u` bound, the ingredient pins and Duhamel families of rows b, c and V1s2'/V1s3', `(Eq:Gtlp_exp+IND)` at `s`). -/

end
