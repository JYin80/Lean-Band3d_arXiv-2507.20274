/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWPins
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLFinal

/-!
# LW-14a (T2236): `lem:LWterm_EXP`, part a of three

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:83-88` (`lem:LWterm_EXP`), proof
`paper/tex/B_graphical_lemmas.tex:7-121` (`B:line`): the reduction `LWE → LWcut` (`(eq:ELW_term)`,
`B:10-13`) and the two loop-level terms `I₁` (`(eq:termI1)`, `B:39-43`) and `I₄₁`
(`(eq:termI41)`, `B:59-72`).  `I₂, I₃, J₁–J₄`, the `GG` expansion and the assembly are LW-14b,
`I₄₂` (`(eq;EGxy:x=y)`) is LW-14c.  No port (RBM2D has no light-weight layer).

* §1 the vocabulary `LWCutExp`, `LWExpI1`, `LWExpI41`, `LWExpG5` (the check file
  `docs/tickets/checks/T2236-check.lean`, section 2, without the suffix `Pin`).
* §2 `lwExpTerm_prec_integral`: `≺ → 𝔼` (copy of `expDr_expect`, `Induction/ExpEtermsB.lean:553`: the first
  moment off the failure event, a polynomial envelope and floor).
* §4 `lwTermEXP_of_cut : LWCutExp d → LWtermEXP d`.
* §6 `lwExpI1_holds`; §12 `lwExpI41_holds`; §13 the compiled instances at `d = 3`.

Route of `I₁`, `I₄₁`: `𝓛^{(2)} = 𝒦^{(2)} + (𝓛-𝒦)^{(2)}`, `X = 𝓛^{(1)} - m`.  Merged inputs: `STExpAvgAt`
(`STExpAvgAt_of_LWAvgLaw`, the proof of `stImproveExpAver_holds`), `STKbound` and `STKward`
(`stKbound_of_flow`, `stKward_of_flow`), `STLK`, `STLmax` (hypotheses), `sum_gloop_two_ward` (`(WI_calL)`),
`KLK_rotate`.  In `I₄₁` the sum over `a₂` uses `𝓛^{(2)}_{(-,+),(a,a₂)} ≥ 0` (`lwExpTerm_loop2_nonneg`) and the
random Ward identity; the paper's factor `m` of `I₁`, `I₄₁` has `|m| = 1` and is not carried (pins of the
check file).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Vocabulary (the pins of the check file `docs/tickets/checks/T2236-check.lean`, section 2) -/

/-- **One cut term of `(eq:EGC)` in expectation** (`B:10-13`, `(eq:ELW_term)` read at the loop level):
under the premises of `LWtermEXP` (`LWPins.lean:311`, verbatim), for both charges `(σc, σo)` and both
blocks `(ac, ao)`, `‖𝔼 LWcut‖ ≺ (1-t)⁻¹ (W^{-d}B_{t,0})^{5/2}` on the index set `ĝ²/L^d ≤ 1 - t`. -/
def LWCutExp (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWcut sz n (STflowE z n) (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-! ## 2. `≺ → 𝔼`: the first moment off the failure event (copy of `expDr_first_moment`,
`expDr_expect`, `Induction/ExpEtermsB.lean:523-596`, which are not among the imports) -/

private theorem lwExpTerm_first_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℂ} {S : Set Ω} {c B : ℝ} (hc : 0 ≤ c) (hB : ∀ ω, ‖f ω‖ ≤ B)
    (hin : ∀ ω, ω ∉ S → ‖f ω‖ ≤ c) : ∫ ω, ‖f ω‖ ∂P ≤ c + B * (P S).toReal := by
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

/-- **`≺ → 𝔼`** (generic; the route of `STExpAvgAt_of_LWAvgLaw`, `ExpAvg.lean:799`, without the
Stein step): from the `≺` of `‖X_v‖` against a deterministic `R`, a polynomial envelope `N^{Kenv}` and a
polynomial floor `R ≥ N^{-Kf}`: `‖𝔼 X_v‖ ≺ R` (deterministic left side), no measurability needed. -/
theorem lwExpTerm_prec_integral {d : ℕ} (sz : Sizes d) {V : ℕ → Type} (X : ∀ n, V n → sz.SeqΩ → ℂ)
    (R : ∀ n, V n → ℝ) {Kenv Kf : ℝ} (hsz : sz.SizeTendsto)
    (henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv)
    (hfloor : ∀ᶠ n in atTop, ∀ v, ((sz.size n : ℕ) : ℝ) ^ (-Kf) ≤ R n v)
    (hprec : sz.Prec (U := V) (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v)) :
    sz.Prec (U := V) (fun n v _ => ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v _ => R n v) := by
  refine (st6_prec_det_iff sz hsz (fun n v => ‖∫ ω, X n v ω ∂(sz.seqP)‖) R).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  have hDp : 0 < |Kenv| + |Kf| + 1 := by positivity
  have hC : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hprec (τ / 2) hτ2 (|Kenv| + |Kf| + 1) hDp, henv, hfloor, hC,
    hsz.eventually (eventually_ge_atTop 1)] with n hP hEnv hFl hN2 hN1
  intro v
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN1
  have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hR0 : 0 ≤ R n v := (Real.rpow_nonneg hNpos.le _).trans (hFl v)
  set S : Set sz.SeqΩ := badSetAt sz.size (fun n v ω => ‖X n v ω‖) (fun n v _ => R n v) (τ / 2) n with hS
  have hPS : (sz.seqP S).toReal ≤ N ^ (-(|Kenv| + |Kf| + 1)) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hNpos.le _) hP
  have hin : ∀ ω, ω ∉ S → ‖X n v ω‖ ≤ N ^ (τ / 2) * R n v := by
    intro ω hω
    by_contra hc
    exact hω ⟨v, lt_of_not_ge hc⟩
  have hfm := lwExpTerm_first_moment (P := sz.seqP) (f := fun ω => X n v ω) (S := S)
    (c := N ^ (τ / 2) * R n v) (B := N ^ Kenv) (mul_nonneg (Real.rpow_nonneg hNpos.le _) hR0)
    (fun ω => hEnv v ω) hin
  have htail : N ^ Kenv * (sz.seqP S).toReal ≤ R n v := by
    calc N ^ Kenv * (sz.seqP S).toReal ≤ N ^ Kenv * N ^ (-(|Kenv| + |Kf| + 1)) :=
          mul_le_mul_of_nonneg_left hPS (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (Kenv + -(|Kenv| + |Kf| + 1)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (-Kf) := by
          refine Real.rpow_le_rpow_of_exponent_le hN ?_
          have h1 := le_abs_self Kenv
          have h2 := le_abs_self Kf
          linarith
      _ ≤ R n v := hFl v
  have hX2 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  calc ‖∫ ω, X n v ω ∂(sz.seqP)‖ ≤ ∫ ω, ‖X n v ω‖ ∂(sz.seqP) := norm_integral_le_integral_norm _
    _ ≤ N ^ (τ / 2) * R n v + N ^ Kenv * (sz.seqP S).toReal := hfm
    _ ≤ N ^ (τ / 2) * R n v + R n v := add_le_add le_rfl htail
    _ ≤ N ^ (τ / 2) * R n v + N ^ (τ / 2) * R n v := by
        have : R n v ≤ N ^ (τ / 2) * R n v := by nlinarith
        linarith
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * R n v) := by
        have h3 : 0 ≤ N ^ (τ / 2) * R n v := mul_nonneg hX2 hR0
        linarith [mul_le_mul_of_nonneg_right hN2 h3]
    _ = N ^ τ * R n v := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; congr 2; ring

/-! ## 3. Bounded measurable random variables (integrability of every random term) -/

/-- A bounded measurable `ℂ`-valued random variable. -/
private def lwExpTerm_BM {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C

section BM

variable {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℂ}

private theorem lwExpTerm_BM_const (c : ℂ) : lwExpTerm_BM (fun _ : Ω => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

private theorem lwExpTerm_BM_mul (hf : lwExpTerm_BM f) (hg : lwExpTerm_BM g) :
    lwExpTerm_BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hCg ω) (norm_nonneg _) ((norm_nonneg _).trans (hCf ω))

private theorem lwExpTerm_BM_add (hf : lwExpTerm_BM f) (hg : lwExpTerm_BM g) :
    lwExpTerm_BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.add hgm, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem lwExpTerm_BM_sub (hf : lwExpTerm_BM f) (hg : lwExpTerm_BM g) :
    lwExpTerm_BM (fun ω => f ω - g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

private theorem lwExpTerm_BM_sum {ι : Type*} (s : Finset ι) {F : ι → Ω → ℂ}
    (h : ∀ i ∈ s, lwExpTerm_BM (F i)) : lwExpTerm_BM (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lwExpTerm_BM_const (0 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact lwExpTerm_BM_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem lwExpTerm_BM_integrable {P : Measure Ω} [IsFiniteMeasure P] (hf : lwExpTerm_BM f) :
    Integrable f P := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall hC)

end BM

section LoopBM

variable {d : ℕ} (sz : Sizes d)

/-- The loops of the flow are bounded measurable (`walk_measurable_Lloop`, `norm_Lloop_le`). -/
private theorem lwExpTerm_BM_Lloop (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    lwExpTerm_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) :=
  ⟨walk_measurable_Lloop sz n E t σ a, (etaT E t)⁻¹ ^ (k + 1), fun ω => norm_Lloop_le sz n hE ht σ a ω⟩

private theorem lwExpTerm_BM_X (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool)
    (a : Zd d (sz.L n)) :
    lwExpTerm_BM (fun ω : sz.SeqΩ => Lloop sz n E t ![σ] ![a] ω - mSigma E σ) :=
  lwExpTerm_BM_sub (lwExpTerm_BM_Lloop sz n hE ht _ _) (lwExpTerm_BM_const _)

/-- `LWcut` is bounded measurable. -/
private theorem lwExpTerm_BM_LWcut (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σc σo : Bool)
    (ac ao : Zd d (sz.L n)) : lwExpTerm_BM (fun ω : sz.SeqΩ => LWcut sz n E t σc σo ac ao ω) := by
  unfold LWcut
  refine lwExpTerm_BM_mul (lwExpTerm_BM_const _) (lwExpTerm_BM_sum _ fun a₁ _ =>
    lwExpTerm_BM_sum _ fun a₂ _ => lwExpTerm_BM_mul (lwExpTerm_BM_mul (lwExpTerm_BM_const _)
      (lwExpTerm_BM_X sz n hE ht σc a₁)) ?_)
  exact lwExpTerm_BM_Lloop sz n hE ht (k := 2) _ _

end LoopBM

/-! ## 4. Target 2: the reduction `LWE → LWcut` (`(eq:ELW_term)`, `B:10-13`) -/

/-- **`lwTermEXP_of_cut`** (target 2): `LWE = LWcut(σ₁,σ₀,a₁,a₀) + LWcut(σ₀,σ₁,a₀,a₁)` (`LWPins.lean:218`, `rfl`);
`integral_add` (both cuts are bounded measurable: `lwExpTerm_BM_LWcut`, with `|E| < 2`, `t < 1` from the flow),
the triangle inequality, and `2 ≤ N^{τ/2}`; the index `((σ, a), _)` is sent to the two cut indices
`((σ 1, σ 0), (a 1, a 0))` and `((σ 0, σ 1), (a 0, a 1))` (both on the same index set `ĝ²/L^d ≤ 1 - t`). -/
theorem lwTermEXP_of_cut (d : ℕ) : LWCutExp d → LWtermEXP d := by
  intro hcut hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec
  have h := hcut hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have h' := (st6_prec_det_iff sz hsz _ _).1 h
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  filter_upwards [h' (τ / 2) hτ2, ((tendsto_rpow_atTop hτ2).comp hsz).eventually
    (eventually_ge_atTop 2)] with n hn hN2
  rintro ⟨⟨σ, a⟩, hg⟩
  have h1 := hn ⟨((σ 1, σ 0), (a 1, a 0)), hg⟩
  have h2 := hn ⟨((σ 0, σ 1), (a 0, a 1)), hg⟩
  simp only at h1 h2
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set ζ : ℝ := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) with hζdef
  have hζ0 : 0 ≤ ζ := by
    have h1t : 0 < 1 - t n := by linarith [ht1 n]
    have hB := STBctl_pos sz n (ht1 n)
    positivity
  have hint1 := lwExpTerm_BM_integrable (P := sz.seqP)
    (lwExpTerm_BM_LWcut sz n (hE2 n) (ht1 n) (σ 1) (σ 0) (a 1) (a 0))
  have hint2 := lwExpTerm_BM_integrable (P := sz.seqP)
    (lwExpTerm_BM_LWcut sz n (hE2 n) (ht1 n) (σ 0) (σ 1) (a 0) (a 1))
  have hsplit : ∫ ω, LWE sz n (STflowE z n) (t n) σ a ω ∂(sz.seqP) =
      ∫ ω, LWcut sz n (STflowE z n) (t n) (σ 1) (σ 0) (a 1) (a 0) ω ∂(sz.seqP) +
        ∫ ω, LWcut sz n (STflowE z n) (t n) (σ 0) (σ 1) (a 0) (a 1) ω ∂(sz.seqP) := by
    unfold LWE
    exact integral_add hint1 hint2
  change ‖∫ ω, LWE sz n (STflowE z n) (t n) σ a ω ∂(sz.seqP)‖ ≤ N ^ τ * ζ
  rw [hsplit]
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  calc _ ≤ ‖∫ ω, LWcut sz n (STflowE z n) (t n) (σ 1) (σ 0) (a 1) (a 0) ω ∂(sz.seqP)‖ +
        ‖∫ ω, LWcut sz n (STflowE z n) (t n) (σ 0) (σ 1) (a 0) (a 1) ω ∂(sz.seqP)‖ := norm_add_le _ _
    _ ≤ N ^ (τ / 2) * ζ + N ^ (τ / 2) * ζ := add_le_add h1 h2
    _ = 2 * (N ^ (τ / 2) * ζ) := by ring
    _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * ζ) :=
        mul_le_mul_of_nonneg_right hN2 (mul_nonneg (Real.rpow_nonneg hNpos.le _) hζ0)
    _ = N ^ τ * ζ := by rw [← mul_assoc, ← hNτ]

/-! ## 5. The flow facts and the common estimates of `I₁`, `I₄₁` -/

/-! ## 6. Target 3: the term `I₁` (`(eq:termI1)`, `B:39-43`) -/

/-! ## 7. The Ward identity `(WI_calL)` at `n = 2` and the positivity of `𝓛^{(2)}_{(-,+)}` -/

/-! ## 8. The sums over `(a₁, a₂, a₃)` with `S^{(B)}_{a₁a₂} S^{(B)}_{a₂a₃}` -/

/-! ## 9. The splitting of `𝔼[X A A']` and of the triple sum (abstract in the random variables) -/

/-! ## 10. The random part `T_a` of `I₄₁` -/

/-! ## 12. Target 4: the term `I₄₁` (`(eq:termI41)`, `B:59-72`) -/

end RBM.Gauss.Sizes

/-! ## 13. Compiled nonempty instances (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, the merged data `sz0`, `z0`,
`tInst` of `RBM.Gauss.LWInst`): every deterministic hypothesis is discharged (`3 ≤ 3`, `0 < 1/10`,
`flow_z0`, `0 ≤ tInst`, `tInst ≤ lemT z0`); the local laws (`LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`,
`STDecay`) and `LWCutExp` (LW-14b/c) are other gates' pins and stay hypotheses -/
