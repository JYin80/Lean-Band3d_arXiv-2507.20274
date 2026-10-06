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

/-- **The term `I₁`** (`(eq:termI1)`, `B:43-47`) at the loop level, all charges: `p = ((σ₁, σ), (a, b))`,
`‖Σ_{a₁} S^{(B)}_{a₁b} 𝔼[(𝓛^{(1)}_{σ₁,a₁} - m(σ₁)) 𝓛^{(2)}_{σ,(a,b)}]‖ ≺ (W^{-d}B_{t,0})³`
(`𝔼 tr(Ǧ E_{a₁}) · 𝒦^{(2)}` by `STExpAvgAt` and `STKbound`; `𝔼[tr(Ǧ E_{a₁}) (𝓛-𝒦)^{(2)}]` by `LWAvgLaw`, `STLK`). -/
def LWExpI1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖∑ a₁, (SB d (sz.L n) (sz.lam n) a₁ (p.2 1) : ℂ) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![a₁] ω - mSigma (STflowE z n) p.1.1) *
                Lloop sz n (STflowE z n) (t n) p.1.2 p.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (sz.Bctl n (t n)) ^ 3)

/-- **The term `I₄₁`** (`(eq:termI41)`, `B:66-80`) at the loop level: `p = (σ₁, (a, b))`,
`‖W^d Σ_{a₁,a₂,a₃} S^{(B)}_{a₁a₂} S^{(B)}_{a₂a₃} 𝔼[(𝓛^{(1)}_{σ₁,a₁} - m(σ₁)) 𝓛^{(2)}_{(-,+),(a,a₂)} 𝓛^{(2)}_{(-,+),(a₃,b)}]‖
≺ η_t⁻¹ (W^{-d}B_{t,0})³` (Ward `(WI_calL)` for `Σ_{a₂}`, `(WI_calK)` for `Σ_{a₃}`). -/
def LWExpI41 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1] ![a₁] ω - mSigma (STflowE z n) p.1) *
                Lloop sz n (STflowE z n) (t n) ![false, true] ![p.2 0, a₂] ω *
                Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, p.2 1] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3)

/-- **The term `I₄₂`** (`(eq;I42inG)`, `(eq;EGxy:x=y)`, `B:81-90`): the 5-loop
`‖W^d Σ_{a₁,a₂,a₃} S^{(B)}_{a₁a₂} S^{(B)}_{a₂a₃} 𝔼 𝓛^{(5)}_{(+,+,+,+,-),(a₂,a₁,a₃,b,a)}‖ ≺ η_t⁻¹ (W^{-d}B_{t,0})^{5/2}`
under the premises of `LWtermEXP`.  Stated here (interface of LW-14b/c), proved in LW-14c. -/
def LWExpG5 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : Fin 2 → Zd d (sz.L n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, Lloop sz n (STflowE z n) (t n) ![true, true, true, true, false]
                ![a₂, a₁, a₃, p.1 1, p.1 0] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

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

/-- `StochDomAt` transports along pointwise equal families. -/
private theorem lwExpTerm_prec_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U : ℕ → Type*} {ξ ξ' ζ ζ' : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, ξ l u ω = ξ' l u ω)
    (hζ : ∀ l u ω, ζ l u ω = ζ' l u ω) (h : StochDomAt P size ξ ζ) : StochDomAt P size ξ' ζ' := by
  have e1 : ξ = ξ' := by funext l u ω; exact hξ l u ω
  have e2 : ζ = ζ' := by funext l u ω; exact hζ l u ω
  subst e1 e2
  exact h

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

section Common

variable {d : ℕ} (sz : Sizes d)

private theorem lwExpTerm_vec1 {α : Type*} (x : α) : (![x] : Fin 1 → α) = fun _ => x := by
  funext i
  fin_cases i
  rfl

/-- `tr(Ǧ E_a)` against `𝒦^{(1)} = m` (`ST_Kloop_one`) in the `![·]` notation of the pins. -/
private theorem lwExpTerm_Kloop_one (n : ℕ) (E u : ℝ) (σ : Bool) (a : Zd d (sz.L n)) :
    STKloop sz n E u ![σ] ![a] = mSigma E σ := by
  rw [lwExpTerm_vec1, lwExpTerm_vec1]
  exact ST_Kloop_one sz n E u σ a

/-- The eventual facts along the flow at the time sequence `t`: `η_t⁻¹ ≤ N`, `W^{-d}B_{t,0} ≤ 1`,
`N⁻¹ ≤ W^{-d}B_{t,0}`, `4 ≤ N`, and `|𝒦^{(2)}| ≤ N` for every `(σ, a)`. -/
private theorem lwExpTerm_facts (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n in atTop, (etaT (STflowE z n) (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧
      sz.Bctl n (t n) ≤ 1 ∧ ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n (t n) ∧
      (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STKloop sz n (STflowE z n) (t n) σ a‖ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hK := (st6_prec_det_iff sz hsz _ _).1 (stKbound_of_flow sz hd hκ hz t ht0 ht1 2 (by norm_num)) 1
    one_pos
  filter_upwards [expAvg_eta_inv_le sz hκ hε hz, st5_Bctl_le_one sz hκ hε hz htz, hK,
    hsz.eventually (eventually_ge_atTop 4)] with n hη hB1 hKn hN4
  refine ⟨hη (t n) (htz n), hB1 (t n) le_rfl, expAvg_Bctl_ge sz n (ht0 n) (ht1 n), hN4, ?_⟩
  intro σ a
  have h := hKn (σ, a)
  have hB := hB1 (t n) le_rfl
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  simp only [Nat.reduceSub, pow_one, Real.rpow_one] at h
  calc _ ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n (t n) := h
    _ ≤ ((sz.size n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hB hNpos.le
    _ = _ := mul_one _

/-- `‖𝓛^{(1)} - m‖ ≤ 2N` (`‖𝓛^{(1)}‖ ≤ η⁻¹ ≤ N`, `‖m‖ = 1`). -/
private theorem lwExpTerm_env_X (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {N : ℝ}
    (hη : (etaT E t)⁻¹ ≤ N) (hN : 1 ≤ N) (σ : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t ![σ] ![a] ω - mSigma E σ‖ ≤ 2 * N := by
  have h1 : ‖Lloop sz n E t ![σ] ![a] ω‖ ≤ (etaT E t)⁻¹ ^ 1 :=
    norm_Lloop_le sz n hE ht (k := 0) ![σ] ![a] ω
  rw [pow_one] at h1
  calc _ ≤ ‖Lloop sz n E t ![σ] ![a] ω‖ + ‖mSigma E σ‖ := norm_sub_le _ _
    _ ≤ N + 1 := by rw [norm_mSigma hE.le]; linarith
    _ ≤ 2 * N := by linarith

/-- `‖𝓛^{(2)}‖ ≤ N²`. -/
private theorem lwExpTerm_env_L2 (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {N : ℝ}
    (hη : (etaT E t)⁻¹ ≤ N) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t σ a ω‖ ≤ N ^ 2 := by
  have h1 := norm_Lloop_le sz n hE ht (k := 1) σ a ω
  have h0 : 0 ≤ (etaT E t)⁻¹ := (inv_pos.2 (etaT_pos hE ht)).le
  exact h1.trans (pow_le_pow_left₀ h0 hη 2)

/-- `‖𝓛^{(2)} - 𝒦^{(2)}‖ ≤ 2N²` given `‖𝒦^{(2)}‖ ≤ N`, `1 ≤ N`. -/
private theorem lwExpTerm_env_D (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {N : ℝ}
    (hη : (etaT E t)⁻¹ ≤ N) (hN : 1 ≤ N) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hK : ‖STKloop sz n E t σ a‖ ≤ N) (ω : sz.SeqΩ) :
    ‖Lloop sz n E t σ a ω - STKloop sz n E t σ a‖ ≤ 2 * N ^ 2 := by
  calc _ ≤ ‖Lloop sz n E t σ a ω‖ + ‖STKloop sz n E t σ a‖ := norm_sub_le _ _
    _ ≤ N ^ 2 + N := add_le_add (lwExpTerm_env_L2 sz n hE ht hη σ a ω) hK
    _ ≤ 2 * N ^ 2 := by nlinarith

/-- `N^{-3} ≤ B³` from `N⁻¹ ≤ B`. -/
private theorem lwExpTerm_floor3 {N B : ℝ} (hN : 0 < N) (hB : N⁻¹ ≤ B) : N ^ (-(3 : ℝ)) ≤ B ^ 3 := by
  have h : N ^ (-(3 : ℝ)) = (N⁻¹) ^ 3 := by
    rw [Real.rpow_neg hN.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  rw [h]
  exact pow_le_pow_left₀ (inv_nonneg.2 hN.le) hB 3

/-- **`𝔼[(𝓛^{(1)} - m)(𝓛 - 𝒦)^{(2)}] ≺ B³`**, all charges, uniformly in `(σ₁, σ, a, a₁)`: the product
`‖X‖‖D‖ ≺ B · B²` (`STLK` at `k = 1, 2`, `ST_Kloop_one`; `StochDomAt.mul`), then `≺ → 𝔼` with the
envelope `4N³ ≤ N⁴` and the floor `N⁻³ ≤ B³` (`lwExpTerm_prec_integral`). -/
private theorem lwExpTerm_XD (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n))
    (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n))
      (fun n p _ => ‖∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![p.2.2] ω - mSigma (STflowE z n) p.1.1) *
          (Lloop sz n (STflowE z n) (t n) p.1.2 p.2.1 ω - STKloop sz n (STflowE z n) (t n) p.1.2 p.2.1)
            ∂(sz.seqP)‖)
      (fun n _ _ => (sz.Bctl n (t n)) ^ 3) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hfac := lwExpTerm_facts sz hd hκ hε hz ht0 htz
  refine lwExpTerm_prec_integral sz (V := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n))
    (fun n p ω => (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![p.2.2] ω - mSigma (STflowE z n) p.1.1) *
      (Lloop sz n (STflowE z n) (t n) p.1.2 p.2.1 ω - STKloop sz n (STflowE z n) (t n) p.1.2 p.2.1))
    (fun n _ => (sz.Bctl n (t n)) ^ 3) (Kenv := 4) (Kf := 3) hsz ?_ ?_ ?_
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro p ω
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 := lwExpTerm_env_X sz n (hE2 n) (ht1 n) hη hN1 p.1.1 p.2.2 ω
    have h2 := lwExpTerm_env_D sz n (hE2 n) (ht1 n) hη hN1 p.1.2 p.2.1 (hK _ _) ω
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    rw [norm_mul]
    calc _ ≤ (2 * N) * (2 * N ^ 2) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 4 * N ^ 3 := by ring
      _ ≤ N ^ (4 : ℝ) := by
          have h4 : N ^ (4 : ℝ) = N ^ 4 := by rw [← Real.rpow_natCast]; norm_num
          rw [h4]
          nlinarith [pow_pos hNpos 3]
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro p
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    exact lwExpTerm_floor3 hNpos hBN
  · have h₁ := StochDomAt.precomp_param (hLK 1 le_rfl)
      (fun n (p : (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n)) =>
        ((![p.1.1], ![p.2.2]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
    have h₂ := StochDomAt.precomp_param (hLK 2 (by norm_num))
      (fun n (p : (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n)) =>
        ((p.1.2, p.2.1) : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
    have hm := StochDomAt.mul (P := sz.seqP) (size := sz.size) (tendsto_size sz hsz)
      (fun n p ω => norm_nonneg _) (fun n p ω => pow_nonneg (STBctl_pos sz n (ht1 n)).le _) h₁ h₂
    refine lwExpTerm_prec_congr (fun n p ω => ?_) (fun n p ω => ?_) hm
    · simp only [Pi.mul_apply, norm_mul, lwExpTerm_Kloop_one]
    · simp only [Pi.mul_apply]; ring

/-- The column sums of `|S^{(B)}|`: `Σ_a ‖S^{(B)}_{ab}‖ = 1` (`sum_norm_SB_row`, `S^{(B)}` symmetric). -/
private theorem lwExpTerm_sum_norm_SB_col (L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) (b : Zd d L) :
    ∑ a : Zd d L, ‖SB d L g a b‖ = 1 := by
  have h := sum_norm_SB_row d L g hL b
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(SB_isSymm d L g).apply]

/-- `𝔼 (𝓛^{(1)} - m) = 𝔼 𝓛^{(1)} - m` (a probability space, `𝓛^{(1)}` bounded). -/
private theorem lwExpTerm_int_X (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool)
    (a : Zd d (sz.L n)) :
    ∫ ω, (Lloop sz n E t ![σ] ![a] ω - mSigma E σ) ∂(sz.seqP) =
      (∫ ω, Lloop sz n E t (fun _ : Fin 1 => σ) (fun _ => a) ω ∂(sz.seqP)) - mSigma E σ := by
  rw [integral_sub (lwExpTerm_BM_integrable (lwExpTerm_BM_Lloop sz n hE ht (k := 0) _ _))
    (integrable_const _), integral_const]
  simp [lwExpTerm_vec1]

/-- `𝔼[X 𝓛^{(2)}] = (𝔼 X) 𝒦^{(2)} + 𝔼[X (𝓛 - 𝒦)^{(2)}]`, `X = 𝓛^{(1)} - m`. -/
private theorem lwExpTerm_int_XL (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ₁ : Bool)
    (a₁ : Zd d (sz.L n)) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω ∂(sz.seqP) =
      (∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) ∂(sz.seqP)) * STKloop sz n E t σ a +
        ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
          (Lloop sz n E t σ a ω - STKloop sz n E t σ a) ∂(sz.seqP) := by
  have hX := lwExpTerm_BM_X sz n hE ht σ₁ a₁
  have h1 : lwExpTerm_BM (fun ω : sz.SeqΩ => (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      STKloop sz n E t σ a) := lwExpTerm_BM_mul hX (lwExpTerm_BM_const _)
  have h2 : lwExpTerm_BM (fun ω : sz.SeqΩ => (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      (Lloop sz n E t σ a ω - STKloop sz n E t σ a)) :=
    lwExpTerm_BM_mul hX (lwExpTerm_BM_sub (lwExpTerm_BM_Lloop sz n hE ht (k := 1) _ _)
      (lwExpTerm_BM_const _))
  have hpt : ∀ ω : sz.SeqΩ, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω =
      (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * STKloop sz n E t σ a +
        (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
          (Lloop sz n E t σ a ω - STKloop sz n E t σ a) := fun ω => by ring
  simp_rw [hpt]
  rw [integral_add (lwExpTerm_BM_integrable h1) (lwExpTerm_BM_integrable h2), integral_mul_const]

/-- **`I₁`, one size** (`(eq:termI1)`): `‖Σ_{a₁} S^{(B)}_{a₁b} 𝔼[X_{a₁} 𝓛^{(2)}]‖ ≤ x k + y` when
`‖𝔼 X_{a₁}‖ ≤ x`, `‖𝒦^{(2)}‖ ≤ k`, `‖𝔼[X_{a₁} (𝓛-𝒦)^{(2)}]‖ ≤ y` (`Σ_{a₁} ‖S^{(B)}_{a₁b}‖ = 1`). -/
private theorem lwExpTerm_I1_n (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ₁ : Bool)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) {x k y : ℝ}
    (hX : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) ∂(sz.seqP)‖ ≤ x)
    (hK : ‖STKloop sz n E t σ a‖ ≤ k)
    (hXD : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      (Lloop sz n E t σ a ω - STKloop sz n E t σ a) ∂(sz.seqP)‖ ≤ y) :
    ‖∑ a₁, (SB d (sz.L n) (sz.lam n) a₁ (a 1) : ℂ) *
        ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω ∂(sz.seqP)‖ ≤
      x * k + y := by
  have hx0 : 0 ≤ x := (norm_nonneg _).trans (hX 0)
  have hterm : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) *
      Lloop sz n E t σ a ω ∂(sz.seqP)‖ ≤ x * k + y := by
    intro a₁
    rw [lwExpTerm_int_XL sz n hE ht σ₁ a₁ σ a]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hXD a₁))
    rw [norm_mul]
    exact mul_le_mul (hX a₁) hK (norm_nonneg _) hx0
  have hxky : 0 ≤ x * k + y := (norm_nonneg _).trans (hterm 0)
  calc _ ≤ ∑ a₁, ‖(SB d (sz.L n) (sz.lam n) a₁ (a 1) : ℂ) *
        ∫ ω, (Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t σ a ω ∂(sz.seqP)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a₁, ‖SB d (sz.L n) (sz.lam n) a₁ (a 1)‖ * (x * k + y) := by
        refine Finset.sum_le_sum fun a₁ _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hterm a₁) (norm_nonneg _)
    _ = x * k + y := by
        rw [← Finset.sum_mul, lwExpTerm_sum_norm_SB_col (sz.L n) (sz.lam n) (sz.three_le_L n), one_mul]

end Common

/-! ## 6. Target 3: the term `I₁` (`(eq:termI1)`, `B:39-43`) -/

/-- **`lwExpI1_holds`** (target 3): `I₁ ≺ B³`.  Route of `B:39-43`: `𝓛^{(2)} = 𝒦^{(2)} + (𝓛-𝒦)^{(2)}`;
`‖𝔼 X_{a₁}‖ ≺ B²` is `STExpAvgAt` (merged `STExpAvgAt_of_LWAvgLaw`, `ExpAvg.lean:799`, the proof of
`stImproveExpAver_holds`), `‖𝒦^{(2)}‖ ≺ B` is `STKbound` (`stKbound_of_flow`, `k = 2`); the second part is
`lwExpTerm_XD` (`‖X‖ ≺ B` and `‖(𝓛-𝒦)^{(2)}‖ ≺ B²` from `STLK`, `k = 1, 2`, then `≺ → 𝔼`,
`lwExpTerm_prec_integral`); the sum over `a₁` is `Σ_{a₁} ‖S^{(B)}_{a₁b}‖ = 1`. -/
theorem lwExpI1_holds (d : ℕ) : LWExpI1 d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLW hLK
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hEX := (st6_prec_det_iff sz hsz _ _).1 (STExpAvgAt_of_LWAvgLaw sz hd hκ hε hz t ht0 htz hLW)
  have hKb := (st6_prec_det_iff sz hsz _ _).1
    (stKbound_of_flow sz hd hκ hz t ht0 ht1 2 (by norm_num))
  have hXD := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm_XD sz hd hκ hε hz ht0 htz hLK)
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ3 : 0 < τ / 3 := by positivity
  filter_upwards [hEX (τ / 3) hτ3, hKb (τ / 3) hτ3, hXD (τ / 3) hτ3,
    ((tendsto_rpow_atTop hτ3).comp hsz).eventually (eventually_ge_atTop 2)] with n hEXn hKn hXDn hN2
  rintro ⟨⟨σ₁, σ⟩, a⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := STBctl_pos sz n (ht1 n)
  have key := lwExpTerm_I1_n sz n (hE2 n) (ht1 n) σ₁ σ a (x := N ^ (τ / 3) * B ^ 2)
    (k := N ^ (τ / 3) * B) (y := N ^ (τ / 3) * B ^ 3)
    (fun a₁ => by rw [lwExpTerm_int_X sz n (hE2 n) (ht1 n)]; exact hEXn (σ₁, a₁))
    (by simpa using hKn (σ, a)) (fun a₁ => hXDn ((σ₁, σ), (a, a₁)))
  refine key.trans ?_
  have hu3 : N ^ τ = (N ^ (τ / 3)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
  rw [hu3]
  have hN2' : (2 : ℝ) ≤ N ^ (τ / 3) := hN2
  set u : ℝ := N ^ (τ / 3) with hu
  have hB3 : 0 < B ^ 3 := by positivity
  have h1 : 0 ≤ u ^ 2 - u - 1 := by nlinarith
  have h2 : 0 ≤ u * (u ^ 2 - u - 1) * B ^ 3 :=
    mul_nonneg (mul_nonneg (by linarith) h1) hB3.le
  nlinarith [h2]

/-! ## 7. The Ward identity `(WI_calL)` at `n = 2` and the positivity of `𝓛^{(2)}_{(-,+)}` -/

section Ward

variable {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

private theorem lwExpTerm_loopL_rot (s t : Bool) (b a : Zd d L) :
    loopL d L W H z ⟨[s, t], [b, a]⟩ = loopL d L W H z ⟨[t, s], [a, b]⟩ := by
  simp only [loopL, List.zip_cons_cons, List.zip_nil_left, List.foldr_cons, List.foldr_nil,
    Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

private theorem lwExpTerm_loopL_conj (a b : Zd d L) :
    loopL d L W H ((starRingEnd ℂ) z) ⟨[true, false], [a, b]⟩ =
      loopL d L W H z ⟨[false, true], [a, b]⟩ := by
  simp [loopL, Gres]

private theorem lwExpTerm_loopL_one (s : Bool) (a : Zd d L) :
    loopL d L W H z ⟨[s], [a]⟩ = Matrix.trace (green H (RBM.Ind.zSig z s) * Eblk d L W a) := by
  simp [loopL, ← RBM.Ind.Gres_eq_green_zSig]

/-- **`(WI_calL)` at `n = 2`**, summed over the SECOND label of the charges `(-,+)`
(`sum_gloop_two_ward` at `z̄`, `RBM2D/Hierarchy/WardResolvent.lean:85`; the bridge of the ticket's
`lwExpTerm_ward_two`): `2iη Σ_b 𝓛_{(-,+),(a,b)} = W^{-d} (𝓛^{(1)}_{+,a} - 𝓛^{(1)}_{-,a})`. -/
private theorem lwExpTerm_ward_loop (hH : H.IsHermitian) (hz : z.im ≠ 0) (a : Zd d L) :
    (2 * Complex.I * (z.im : ℂ)) * ∑ b : Zd d L, loopL d L W H z ⟨[false, true], [a, b]⟩ =
      (((W : ℂ) ^ d)⁻¹) * (loopL d L W H z ⟨[true], [a]⟩ - loopL d L W H z ⟨[false], [a]⟩) := by
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH
    (z := (starRingEnd ℂ) z) (by simpa using hz)
  have h1 := lwExpTerm_loopL_one (H := H) (z := z) true a
  have h2 := lwExpTerm_loopL_one (H := H) (z := z) false a
  simp only [RBM.Ind.zSig_true, RBM.Ind.zSig_false] at h1 h2
  rw [h1, h2]
  simp_rw [← lwExpTerm_loopL_conj (H := H) (z := z)]
  have h := sum_gloop_two_ward d L W (H := H) (z := (starRingEnd ℂ) z) hu' (by simpa using hu) a
  simp only [Complex.conj_conj, Complex.conj_im, Complex.ofReal_neg] at h
  linear_combination -h

private theorem lwExpTerm_green_conj (hH : H.IsHermitian) (hz : z.im ≠ 0) :
    green H ((starRingEnd ℂ) z) = (green H z)ᴴ := by
  have hH' : Hᴴ = H := hH
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  simp only [green, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH', Complex.star_def]

/-- **`𝓛^{(2)}_{(-,+),(a,b)} ≥ 0`**: `tr(G⁻ E_a G⁺ E_b) = tr(E_a Q Qᴴ)` with `Q = G⁺ D`, `D² = E_b`
(`trace_Eblk_mul_mul_conjTranspose`, `ConArgDet.lean`). -/
private theorem lwExpTerm_loop2_nonneg (hH : H.IsHermitian) (hz : z.im ≠ 0) (a b : Zd d L) :
    ∃ r : ℝ, 0 ≤ r ∧ loopL d L W H z ⟨[false, true], [a, b]⟩ = (r : ℂ) := by
  set G : Matrix (Vtx d L W) (Vtx d L W) ℂ := green H z with hG
  set D : Matrix (Vtx d L W) (Vtx d L W) ℂ := Matrix.diagonal
    (fun p : Vtx d L W => if p.1 = b then ((Real.sqrt (((W : ℝ) ^ d)⁻¹) : ℝ) : ℂ) else 0) with hD
  have hDD : D * D = Eblk d L W b := by
    rw [hD, Eblk, Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    by_cases hp : p.1 = b
    · simp only [hp, ↓reduceIte]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      rfl
    · simp [hp]
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext p
    by_cases hp : p.1 = b <;> simp [hp]
  have hloop : loopL d L W H z ⟨[false, true], [a, b]⟩ =
      Matrix.trace (Gᴴ * Eblk d L W a * (G * Eblk d L W b)) := by
    have e1 : Gres H z true = G := by
      simp only [hG, green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
    have e2 : Gres H z false = Gᴴ := by
      rw [hG, ← lwExpTerm_green_conj hH hz]
      simp only [green, Gres, Bool.false_eq_true, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
    simp only [loopL, List.zip_cons_cons, List.zip_nil_left, List.foldr_cons, List.foldr_nil,
      Matrix.mul_one, e1, e2]
  have hcyc : Matrix.trace (Gᴴ * Eblk d L W a * (G * Eblk d L W b)) =
      Matrix.trace (Eblk d L W a * (G * D) * (G * D)ᴴ) := by
    rw [Matrix.conjTranspose_mul, hDh, Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [← hDD]
    simp only [Matrix.mul_assoc]
  refine ⟨((W : ℝ) ^ d)⁻¹ * ∑ α : Fin (W ^ d), ∑ k : Vtx d L W,
    Complex.normSq ((G * D) (a, α) k), mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _), ?_⟩
  rw [hloop, hcyc, RBM.Ind.trace_Eblk_mul_mul_conjTranspose]
  push_cast
  rfl

end Ward

section WardLloop

variable {d : ℕ} (sz : Sizes d)

private theorem lwExpTerm_Lloop_eq2 (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    Lloop sz n E t σ a ω = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n t ω))
      (zt E t) ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  unfold Lloop loopFine
  rw [loopM_eq_loopL]
  simp [loopOf, List.ofFn_succ]

private theorem lwExpTerm_Lloop_eq1 (n : ℕ) (E t : ℝ) (s : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![s] ![a] ω = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n t ω))
      (zt E t) ⟨[s], [a]⟩ := by
  unfold Lloop loopFine
  rw [loopM_eq_loopL]
  simp [loopOf, List.ofFn_succ]

/-- **`(WI_calL)` for the model matrix** (`lwExpTerm_ward_two`): `2iη_t Σ_b 𝓛^{(2)}_{(-,+),(a,b)} =
W^{-d}(𝓛^{(1)}_{+,a} - 𝓛^{(1)}_{-,a})`. -/
private theorem lwExpTerm_ward_two (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (a : Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    (2 * Complex.I * ((etaT E t : ℝ) : ℂ)) * ∑ b : Zd d (sz.L n), Lloop sz n E t ![false, true] ![a, b] ω =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (Lloop sz n E t ![true] ![a] ω - Lloop sz n E t ![false] ![a] ω) := by
  have hpos := etaT_pos hE ht
  have hH : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n t ω)).IsHermitian :=
    (seqHflow_isHermitian sz n t ω).submatrix _
  have hz : (zt E t).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hpos.ne'
  have h := lwExpTerm_ward_loop (d := d) (L := sz.L n) (W := sz.W n) hH hz a
  rw [← etaT_eq_zt_im] at h
  simp only [lwExpTerm_Lloop_eq1, lwExpTerm_Lloop_eq2]
  exact h

/-- `W^d Σ_b ‖𝓛^{(2)}_{(-,+),(a,b)}‖ ≤ η_t⁻¹ ‖𝓛^{(1)}_{+,a}‖` (Ward with `𝓛^{(2)}_{(-,+)} ≥ 0`, `𝓛^{(1)}_- = conj 𝓛^{(1)}_+`). -/
private theorem lwExpTerm_ward_sum_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (a : Zd d (sz.L n))
    (ω : sz.SeqΩ) :
    (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b : Zd d (sz.L n), ‖Lloop sz n E t ![false, true] ![a, b] ω‖ ≤
      (etaT E t)⁻¹ * ‖Lloop sz n E t ![true] ![a] ω‖ := by
  have hpos := etaT_pos hE ht
  have hH : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n t ω)).IsHermitian :=
    (seqHflow_isHermitian sz n t ω).submatrix _
  have hz : (zt E t).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hpos.ne'
  have hnn : ∀ b : Zd d (sz.L n), ∃ r : ℝ, 0 ≤ r ∧ Lloop sz n E t ![false, true] ![a, b] ω = (r : ℂ) := by
    intro b
    have := lwExpTerm_loop2_nonneg (d := d) (L := sz.L n) (W := sz.W n) hH hz a b
    simpa [lwExpTerm_Lloop_eq2] using this
  choose r hr0 hr using hnn
  have hnorm : ∀ b, ‖Lloop sz n E t ![false, true] ![a, b] ω‖ = r b := by
    intro b
    rw [hr b, Complex.norm_real, Real.norm_of_nonneg (hr0 b)]
  simp only [hnorm]
  have hW := lwExpTerm_ward_two sz n hE ht a ω
  simp only [hr] at hW
  have hconj : ‖Lloop sz n E t ![false] ![a] ω‖ = ‖Lloop sz n E t ![true] ![a] ω‖ := by
    simp only [lwExpTerm_vec1, ST_Lloop_one_false, Complex.norm_conj]
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have := sz.W_pos n
    positivity
  have hsum : ‖(2 * Complex.I * ((etaT E t : ℝ) : ℂ)) * ∑ b, ((r b : ℝ) : ℂ)‖ = 2 * etaT E t * ∑ b, r b := by
    rw [norm_mul, norm_mul, ← Complex.ofReal_sum, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun b _ => hr0 b), Real.norm_of_nonneg hpos.le]
    simp
  have hrhs : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (Lloop sz n E t ![true] ![a] ω - Lloop sz n E t ![false] ![a] ω)‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ‖Lloop sz n E t ![true] ![a] ω‖) := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hWd.le)
    calc _ ≤ ‖Lloop sz n E t ![true] ![a] ω‖ + ‖Lloop sz n E t ![false] ![a] ω‖ := norm_sub_le _ _
      _ = _ := by rw [hconj]; ring
  have h1 : 2 * etaT E t * ∑ b, r b ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ‖Lloop sz n E t ![true] ![a] ω‖) := by
    rw [← hsum, hW]; exact hrhs
  have h2 : etaT E t * (((sz.W n : ℕ) : ℝ) ^ d * ∑ b, r b) ≤ ‖Lloop sz n E t ![true] ![a] ω‖ := by
    have : (((sz.W n : ℕ) : ℝ) ^ d) * (2 * etaT E t * ∑ b, r b) ≤ 2 * ‖Lloop sz n E t ![true] ![a] ω‖ := by
      calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ‖Lloop sz n E t ![true] ![a] ω‖)) :=
            mul_le_mul_of_nonneg_left h1 hWd.le
        _ = _ := by field_simp
    nlinarith
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  nlinarith

end WardLloop

/-! ## 8. The sums over `(a₁, a₂, a₃)` with `S^{(B)}_{a₁a₂} S^{(B)}_{a₂a₃}` -/

section Sums

variable {d : ℕ} (L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L)

include hL in
/-- `Σ_{a₁,a₂,a₃} ‖S_{a₁a₂}‖ ‖S_{a₂a₃}‖ h(a₂) = Σ_{a₂} h(a₂)`. -/
private theorem lwExpTerm_wsum2 (h : Zd d L → ℝ) :
    ∑ a₁, ∑ a₂, ∑ a₃, ‖SB d L g a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₂ = ∑ a₂, h a₂ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  have e : ∀ a₁, ∑ a₃, ‖SB d L g a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₂ = ‖SB d L g a₁ a₂‖ * h a₂ := by
    intro a₁
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_norm_SB_row d L g hL, mul_one]
  simp_rw [e]
  rw [← Finset.sum_mul, lwExpTerm_sum_norm_SB_col L g hL, one_mul]

include hL in
/-- `Σ_{a₁,a₂,a₃} ‖S_{a₁a₂}‖ ‖S_{a₂a₃}‖ h(a₃) = Σ_{a₃} h(a₃)`. -/
private theorem lwExpTerm_wsum3 (h : Zd d L → ℝ) :
    ∑ a₁, ∑ a₂, ∑ a₃, ‖SB d L g a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₃ = ∑ a₃, h a₃ := by
  rw [Finset.sum_comm]
  have e : ∀ a₂, ∑ a₁, ∑ a₃, ‖SB d L g a₁ a₂‖ * ‖SB d L g a₂ a₃‖ * h a₃ =
      ∑ a₃, ‖SB d L g a₂ a₃‖ * h a₃ := by
    intro a₂
    simp_rw [mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, lwExpTerm_sum_norm_SB_col L g hL, one_mul]
  simp_rw [e]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, lwExpTerm_sum_norm_SB_col L g hL, one_mul]

private theorem lwExpTerm_norm_sum3_le {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) :
    ‖∑ a₁, ∑ a₂, ∑ a₃, f a₁ a₂ a₃‖ ≤ ∑ a₁, ∑ a₂, ∑ a₃, ‖f a₁ a₂ a₃‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun _ _ => norm_sum_le _ _))

end Sums

section SumsN

variable {d : ℕ} (sz : Sizes d)

private theorem lwExpTerm_norm_Wd (n : ℕ) : ‖(((sz.W n : ℕ) : ℂ) ^ d)‖ = ((sz.W n : ℕ) : ℝ) ^ d := by
  rw [norm_pow, Complex.norm_natCast]

/-- **The `T_a`-type bound** (`B:66-72`, `O_≺(B³) · W^d Σ_{a₂} 𝓛^{(2)}`): if `‖x_{a₁}‖ ‖y_{a₃}‖ ≤ c` for all
`a₁, a₃`, then `‖W^d Σ S_{a₁a₂} S_{a₂a₃} x_{a₁} A_{a₂} y_{a₃}‖ ≤ c · W^d Σ_{a₂} ‖A_{a₂}‖`. -/
private theorem lwExpTerm_Ta_n (n : ℕ) (x A y : Zd d (sz.L n) → ℂ) {c : ℝ}
    (hc : ∀ a₁ a₃, ‖x a₁‖ * ‖y a₃‖ ≤ c) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (x a₁ * A a₂ * y a₃)‖ ≤
      c * ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ a₂, ‖A a₂‖) := by
  rw [norm_mul, lwExpTerm_norm_Wd]
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 := lwExpTerm_norm_sum3_le (fun a₁ a₂ a₃ => (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (x a₁ * A a₂ * y a₃))
  have h2 : ∑ a₁, ∑ a₂, ∑ a₃, ‖(SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (x a₁ * A a₂ * y a₃)‖ ≤
      ∑ a₁, ∑ a₂, ∑ a₃, ‖SB d (sz.L n) (sz.lam n) a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ *
        (c * ‖A a₂‖) := by
    refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun a₂ _ => Finset.sum_le_sum fun a₃ _ => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have hS : 0 ≤ ‖SB d (sz.L n) (sz.lam n) a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ := by positivity
    calc _ = ‖SB d (sz.L n) (sz.lam n) a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ *
          (‖x a₁‖ * ‖y a₃‖ * ‖A a₂‖) := by ring
      _ ≤ ‖SB d (sz.L n) (sz.lam n) a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ * (c * ‖A a₂‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc a₁ a₃) (norm_nonneg _)) hS
  rw [lwExpTerm_wsum2 (sz.L n) (sz.lam n) (sz.three_le_L n) (fun a₂ => c * ‖A a₂‖)] at h2
  rw [← Finset.mul_sum] at h2
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (c * ∑ a₂, ‖A a₂‖) := mul_le_mul_of_nonneg_left (h1.trans h2) hWd
    _ = _ := by ring

/-- **The `T_b`-type bound** (`B:66-72`, the `K^{(2)}_{(a₃,b)}` factor with `W^d Σ_{a₃}` kept): if
`‖u_{a₁a₂}‖ ≤ c` for all `a₁, a₂`, then `‖W^d Σ S_{a₁a₂} S_{a₂a₃} u_{a₁a₂} k_{a₃}‖ ≤ c · W^d Σ_{a₃} ‖k_{a₃}‖`. -/
private theorem lwExpTerm_Tb_n (n : ℕ) (u : Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (k : Zd d (sz.L n) → ℂ)
    {c : ℝ} (hu : ∀ a₁ a₂, ‖u a₁ a₂‖ ≤ c) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (u a₁ a₂ * k a₃)‖ ≤
      c * ((((sz.W n : ℕ) : ℝ) ^ d) * ∑ a₃, ‖k a₃‖) := by
  rw [norm_mul, lwExpTerm_norm_Wd]
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have h1 := lwExpTerm_norm_sum3_le (fun a₁ a₂ a₃ => (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (u a₁ a₂ * k a₃))
  have h2 : ∑ a₁, ∑ a₂, ∑ a₃, ‖(SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (u a₁ a₂ * k a₃)‖ ≤
      ∑ a₁, ∑ a₂, ∑ a₃, ‖SB d (sz.L n) (sz.lam n) a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ *
        (c * ‖k a₃‖) := by
    refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun a₂ _ => Finset.sum_le_sum fun a₃ _ => ?_
    rw [norm_mul, norm_mul, norm_mul]
    have hS : 0 ≤ ‖SB d (sz.L n) (sz.lam n) a₁ a₂‖ * ‖SB d (sz.L n) (sz.lam n) a₂ a₃‖ := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hu a₁ a₂) (norm_nonneg _)) hS
  rw [lwExpTerm_wsum3 (sz.L n) (sz.lam n) (sz.three_le_L n) (fun a₃ => c * ‖k a₃‖)] at h2
  rw [← Finset.mul_sum] at h2
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (c * ∑ a₃, ‖k a₃‖) := mul_le_mul_of_nonneg_left (h1.trans h2) hWd
    _ = _ := by ring

end SumsN

/-! ## 9. The splitting of `𝔼[X A A']` and of the triple sum (abstract in the random variables) -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `𝔼[X A A'] = 𝔼[X A (A' - K')] + (𝔼 X) K K' + 𝔼[X (A - K)] K'` (`A = K + (A - K)`, `A' = K' + (A' - K')`). -/
private theorem lwExpTerm_int_split3 {X A A' : Ω → ℂ} (K K' : ℂ) (hX : lwExpTerm_BM X)
    (hA : lwExpTerm_BM A) (hA' : lwExpTerm_BM A') :
    ∫ ω, X ω * A ω * A' ω ∂P = ∫ ω, X ω * A ω * (A' ω - K') ∂P + (∫ ω, X ω ∂P) * K * K' +
      (∫ ω, X ω * (A ω - K) ∂P) * K' := by
  have h1 : lwExpTerm_BM (fun ω => X ω * A ω * (A' ω - K')) :=
    lwExpTerm_BM_mul (lwExpTerm_BM_mul hX hA) (lwExpTerm_BM_sub hA' (lwExpTerm_BM_const _))
  have h2 : lwExpTerm_BM (fun ω => X ω * K * K') :=
    lwExpTerm_BM_mul (lwExpTerm_BM_mul hX (lwExpTerm_BM_const _)) (lwExpTerm_BM_const _)
  have h3 : lwExpTerm_BM (fun ω => X ω * (A ω - K) * K') :=
    lwExpTerm_BM_mul (lwExpTerm_BM_mul hX (lwExpTerm_BM_sub hA (lwExpTerm_BM_const _)))
      (lwExpTerm_BM_const _)
  have hpt : ∀ ω, X ω * A ω * A' ω =
      X ω * A ω * (A' ω - K') + X ω * K * K' + X ω * (A ω - K) * K' := fun ω => by ring
  simp_rw [hpt]
  rw [integral_add (lwExpTerm_BM_integrable (lwExpTerm_BM_add h1 h2)) (lwExpTerm_BM_integrable h3),
    integral_add (lwExpTerm_BM_integrable h1) (lwExpTerm_BM_integrable h2), integral_mul_const,
    integral_mul_const, integral_mul_const]

/-- `∫ c₀ Σ_{a₁a₂a₃} c f = c₀ Σ c ∫ f` for integrable `f`. -/
private theorem lwExpTerm_int_sum3 {ι : Type*} [Fintype ι] (c₀ : ℂ) (c : ι → ι → ι → ℂ)
    (f : ι → ι → ι → Ω → ℂ) (hf : ∀ a₁ a₂ a₃, Integrable (f a₁ a₂ a₃) P) :
    ∫ ω, c₀ * ∑ a₁, ∑ a₂, ∑ a₃, c a₁ a₂ a₃ * f a₁ a₂ a₃ ω ∂P =
      c₀ * ∑ a₁, ∑ a₂, ∑ a₃, c a₁ a₂ a₃ * ∫ ω, f a₁ a₂ a₃ ω ∂P := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun a₁ _ => integrable_finsetSum _ fun a₂ _ =>
    integrable_finsetSum _ fun a₃ _ => (hf a₁ a₂ a₃).const_mul _)]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [integral_finsetSum _ (fun a₂ _ => integrable_finsetSum _ fun a₃ _ => (hf a₁ a₂ a₃).const_mul _)]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  rw [integral_finsetSum _ (fun a₃ _ => (hf a₁ a₂ a₃).const_mul _)]
  refine Finset.sum_congr rfl fun a₃ _ => ?_
  rw [integral_const_mul]

/-- **The `I₄₁` split** (`B:66-72`): `W^d Σ S S 𝔼[X A A'] = 𝔼[W^d Σ S S X A (A' - K')]
+ W^d Σ S S ((𝔼 X) K) K' + W^d Σ S S (𝔼[X (A - K)]) K'`. -/
private theorem lwExpTerm_I41_split {ι : Type*} [Fintype ι] (c₀ : ℂ) (S : ι → ι → ℂ)
    (X A A' : ι → Ω → ℂ) (K K' : ι → ℂ) (hX : ∀ i, lwExpTerm_BM (X i)) (hA : ∀ i, lwExpTerm_BM (A i))
    (hA' : ∀ i, lwExpTerm_BM (A' i)) :
    c₀ * ∑ a₁, ∑ a₂, ∑ a₃, S a₁ a₂ * S a₂ a₃ * ∫ ω, X a₁ ω * A a₂ ω * A' a₃ ω ∂P =
      (∫ ω, c₀ * ∑ a₁, ∑ a₂, ∑ a₃, S a₁ a₂ * S a₂ a₃ * (X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃)) ∂P) +
        c₀ * ∑ a₁, ∑ a₂, ∑ a₃, S a₁ a₂ * S a₂ a₃ * (((∫ ω, X a₁ ω ∂P) * K a₂) * K' a₃) +
        c₀ * ∑ a₁, ∑ a₂, ∑ a₃, S a₁ a₂ * S a₂ a₃ * ((∫ ω, X a₁ ω * (A a₂ ω - K a₂) ∂P) * K' a₃) := by
  have hint : ∀ a₁ a₂ a₃, Integrable (fun ω => X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃)) P := fun a₁ a₂ a₃ =>
    lwExpTerm_BM_integrable (lwExpTerm_BM_mul (lwExpTerm_BM_mul (hX a₁) (hA a₂))
      (lwExpTerm_BM_sub (hA' a₃) (lwExpTerm_BM_const _)))
  rw [lwExpTerm_int_sum3 c₀ (fun a₁ a₂ a₃ => S a₁ a₂ * S a₂ a₃)
    (fun a₁ a₂ a₃ ω => X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃)) hint]
  have e : ∀ a₁ a₂ a₃, (∫ ω, X a₁ ω * A a₂ ω * A' a₃ ω ∂P) =
      (∫ ω, X a₁ ω * A a₂ ω * (A' a₃ ω - K' a₃) ∂P) + ((∫ ω, X a₁ ω ∂P) * K a₂) * K' a₃ +
        (∫ ω, X a₁ ω * (A a₂ ω - K a₂) ∂P) * K' a₃ := fun a₁ a₂ a₃ =>
    lwExpTerm_int_split3 (K a₂) (K' a₃) (hX a₁) (hA a₂) (hA' a₃)
  simp_rw [e, mul_add, Finset.sum_add_distrib]
  ring

end Split

/-! ## 10. The random part `T_a` of `I₄₁` -/

section Ta

variable {d : ℕ} (sz : Sizes d)

/-- `R_a = W^d Σ S S X_{a₁} 𝓛^{(2)}_{(-,+),(a,a₂)} (𝓛 - 𝒦)^{(2)}_{(-,+),(a₃,b)}`, `(σ₁, (a, b))` the index. -/
private def lwExpTerm_Ra (n : ℕ) (E t : ℝ) (σ₁ : Bool) (ab : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
    (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ((Lloop sz n E t ![σ₁] ![a₁] ω - mSigma E σ₁) * Lloop sz n E t ![false, true] ![ab 0, a₂] ω *
      (Lloop sz n E t ![false, true] ![a₃, ab 1] ω - STKloop sz n E t ![false, true] ![a₃, ab 1]))

/-- `‖R_a‖ ≺ η_t⁻¹ B³` as a random variable: on the complement of the failure events of `STLK` (`k = 1, 2`)
and `STLmax` (`k = 1`), `‖X_{a₁}‖ ‖D'_{a₃}‖ ≤ N^{τ/2} B³`, `‖𝓛^{(1)}_{+,a}‖ ≤ N^{τ/2}`, and
`Ta_n` with the Ward bound `lwExpTerm_ward_sum_le` give `‖R_a‖ ≤ N^τ η⁻¹ B³`. -/
private theorem lwExpTerm_Ra_prec {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (htz : ∀ n, t n ≤ lemT (z n))
    (hLmax : STLmax sz (STflowE z) t) (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖lwExpTerm_Ra sz n (STflowE z n) (t n) v.1 v.2 ω‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hB0 : ∀ n, 0 < sz.Bctl n (t n) := fun n => STBctl_pos sz n (ht1 n)
  have h₁ := StochDomAt.precomp_param (hLK 1 le_rfl)
    (fun n (p : Bool × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((![p.1], ![p.2.2.1]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
  have h₂ := StochDomAt.precomp_param (hLK 2 (by norm_num))
    (fun n (p : Bool × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((![false, true], ![p.2.2.2, p.2.1 1]) : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
  have hm := StochDomAt.mul (P := sz.seqP) (size := sz.size) (tendsto_size sz hsz)
    (fun n p ω => norm_nonneg _) (fun n p ω => pow_nonneg (hB0 n).le _) h₁ h₂
  have hF1 : StochDomAt sz.seqP sz.size
      (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖Lloop sz n (STflowE z n) (t n) ![p.1] ![p.2.2.1] ω - mSigma (STflowE z n) p.1‖ *
        ‖Lloop sz n (STflowE z n) (t n) ![false, true] ![p.2.2.2, p.2.1 1] ω -
          STKloop sz n (STflowE z n) (t n) ![false, true] ![p.2.2.2, p.2.1 1]‖)
      (fun n _ _ => (sz.Bctl n (t n)) ^ 3) := by
    refine lwExpTerm_prec_congr (fun n p ω => ?_) (fun n p ω => ?_) hm
    · simp only [Pi.mul_apply, lwExpTerm_Kloop_one]
    · simp only [Pi.mul_apply]; ring
  have hF2 : StochDomAt sz.seqP sz.size (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
      (fun n v ω => ‖Lloop sz n (STflowE z n) (t n) ![true] ![v.2 0] ω‖) (fun n _ _ => (1 : ℝ)) := by
    have := StochDomAt.precomp_param (hLmax 1 le_rfl)
      (fun n (p : Bool × (Fin 2 → Zd d (sz.L n))) =>
        ((![true], ![p.2 0]) : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
    refine lwExpTerm_prec_congr (fun n p ω => rfl) (fun n p ω => ?_) this
    simp
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) hF1 hF2 ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, Eventually.of_forall fun n ω hω => ?_⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨v, hv⟩ := hω
  obtain ⟨h1, h2⟩ := hno
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := hB0 n
  set η : ℝ := (etaT (STflowE z n) (t n))⁻¹ with hηdef
  have hη0 : 0 ≤ η := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
  have hu0 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  obtain ⟨σ₁, ab⟩ := v
  have hc : ∀ a₁ a₃ : Zd d (sz.L n),
      ‖Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁‖ *
        ‖Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1] ω -
          STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]‖ ≤ N ^ (τ / 2) * B ^ 3 :=
    fun a₁ a₃ => h1 (σ₁, ab, a₁, a₃)
  have hΛ : ‖Lloop sz n (STflowE z n) (t n) ![true] ![ab 0] ω‖ ≤ N ^ (τ / 2) := by
    have := h2 (σ₁, ab); simpa using this
  have hTa := lwExpTerm_Ta_n sz n
    (fun a₁ => Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁)
    (fun a₂ => Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω)
    (fun a₃ => Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1] ω -
      STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]) hc
  have hW := lwExpTerm_ward_sum_le sz n (hE2 n) (ht1 n) (ab 0) ω
  have hWd : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hfin : ‖lwExpTerm_Ra sz n (STflowE z n) (t n) σ₁ ab ω‖ ≤ N ^ (τ / 2) * B ^ 3 * (η * N ^ (τ / 2)) := by
    refine hTa.trans (mul_le_mul_of_nonneg_left (hW.trans ?_) (by positivity))
    exact mul_le_mul_of_nonneg_left hΛ hη0
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have : N ^ τ * (η * B ^ 3) = N ^ (τ / 2) * B ^ 3 * (η * N ^ (τ / 2)) := by rw [hNτ]; ring
  rw [this] at hv
  exact absurd hfin (not_le.2 hv)

/-- `η_t ≤ 1` for `0 ≤ t < 1`, `|E| < 2` (`η = (1-t) Im m`, `Im m ≤ ‖m‖ = 1`), so `η_t⁻¹ ≥ 1`. -/
private theorem lwExpTerm_eta_le_one {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) :
    etaT E t ≤ 1 := by
  have h1 : (mE E).im ≤ 1 := by
    have := Complex.im_le_norm (mE E)
    rwa [norm_mE hE.le] at this
  unfold etaT
  have him : 0 ≤ (mE E).im := (mE_im_pos hE).le
  nlinarith

/-- **`𝔼 R_a ≺ η_t⁻¹ B³`** (deterministic): `lwExpTerm_Ra_prec` then `≺ → 𝔼` with the envelope
`‖R_a‖ ≤ 4N³ · η⁻¹‖𝓛^{(1)}‖ ≤ 4N⁵ ≤ N⁶` (`Ta_n`, `lwExpTerm_ward_sum_le`) and the floor `η⁻¹ B³ ≥ N⁻³`. -/
private theorem lwExpTerm_Ta_det (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n))
    (hLmax : STLmax sz (STflowE z) t) (hLK : STLK sz (STflowE z) t) :
    sz.Prec (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
      (fun n v _ => ‖∫ ω, lwExpTerm_Ra sz n (STflowE z n) (t n) v.1 v.2 ω ∂(sz.seqP)‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3) := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hfac := lwExpTerm_facts sz hd hκ hε hz ht0 htz
  refine lwExpTerm_prec_integral sz (V := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
    (fun n v ω => lwExpTerm_Ra sz n (STflowE z n) (t n) v.1 v.2 ω)
    (fun n _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3) (Kenv := 6) (Kf := 3) hsz ?_ ?_
    (lwExpTerm_Ra_prec sz hκ hz htz hLmax hLK)
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro v ω
    obtain ⟨σ₁, ab⟩ := v
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hη0 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
    have hX1 : ∀ a₁ : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁‖ ≤ 2 * N :=
      fun a₁ => lwExpTerm_env_X sz n (hE2 n) (ht1 n) hη hN1 σ₁ a₁ ω
    have hD1 : ∀ a₃ : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1] ω -
          STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]‖ ≤ 2 * N ^ 2 :=
      fun a₃ => lwExpTerm_env_D sz n (hE2 n) (ht1 n) hη hN1 ![false, true] ![a₃, ab 1] (hK _ _) ω
    have hc : ∀ a₁ a₃ : Zd d (sz.L n),
        ‖Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁‖ *
          ‖Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1] ω -
            STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]‖ ≤ (2 * N) * (2 * N ^ 2) :=
      fun a₁ a₃ => mul_le_mul (hX1 a₁) (hD1 a₃) (norm_nonneg _) (by positivity)
    have hTa := lwExpTerm_Ta_n sz n
      (fun a₁ => Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁)
      (fun a₂ => Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω)
      (fun a₃ => Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1] ω -
        STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]) hc
    have hW := lwExpTerm_ward_sum_le sz n (hE2 n) (ht1 n) (ab 0) ω
    have hL1 : ‖Lloop sz n (STflowE z n) (t n) ![true] ![ab 0] ω‖ ≤ N := by
      have h1 : ‖Lloop sz n (STflowE z n) (t n) ![true] ![ab 0] ω‖ ≤ (etaT (STflowE z n) (t n))⁻¹ ^ 1 :=
        norm_Lloop_le sz n (hE2 n) (ht1 n) (k := 0) ![true] ![ab 0] ω
      rw [pow_one] at h1
      exact h1.trans hη
    have hW2 : ((sz.W n : ℕ) : ℝ) ^ d * ∑ a₂, ‖Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω‖ ≤
        N * N := hW.trans (mul_le_mul hη hL1 (norm_nonneg _) hNpos.le)
    have h6 : N ^ (6 : ℝ) = N ^ 6 := by rw [← Real.rpow_natCast]; norm_num
    change ‖lwExpTerm_Ra sz n (STflowE z n) (t n) σ₁ ab ω‖ ≤ N ^ (6 : ℝ)
    rw [h6]
    calc _ ≤ ((2 * N) * (2 * N ^ 2)) * (((sz.W n : ℕ) : ℝ) ^ d *
          ∑ a₂, ‖Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω‖) := hTa
      _ ≤ ((2 * N) * (2 * N ^ 2)) * (N * N) := mul_le_mul_of_nonneg_left hW2 (by positivity)
      _ = 4 * N ^ 5 := by ring
      _ ≤ N ^ 6 := by nlinarith [pow_pos hNpos 5]
  · filter_upwards [hfac] with n hn
    obtain ⟨hη, hB1, hBN, hN4, hK⟩ := hn
    intro v
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ :=
      (one_le_inv₀ (etaT_pos (hE2 n) (ht1 n))).2 (lwExpTerm_eta_le_one (hE2 n) (ht0 n))
    have h3 := lwExpTerm_floor3 hNpos hBN
    have hB3 : 0 ≤ (sz.Bctl n (t n)) ^ 3 := pow_nonneg (STBctl_pos sz n (ht1 n)).le _
    calc _ ≤ (sz.Bctl n (t n)) ^ 3 := h3
      _ = 1 * (sz.Bctl n (t n)) ^ 3 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hB3

/-- **`(WI_calK)` for the first label** (`B:72`, `W^d Σ_{a₃} |𝒦^{(2)}_{(-,+),(a₃,b)}| ≺ η_t⁻¹`): `STKward` (`k = 2`,
`stKward_of_flow`) sums the LAST label of `(+,-)`; `𝒦^{(2)}_{(-,+),(a₃,b)} = 𝒦^{(2)}_{(+,-),(b,a₃)}` by
`KLK_rotate`. -/
private theorem lwExpTerm_Kward (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ b : Zd d (sz.L n),
      ((sz.W n : ℕ) : ℝ) ^ d * ∑ a₃, ‖STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, b]‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (etaT (STflowE z n) (t n))⁻¹ := by
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hKw := (st6_prec_det_iff sz hsz _ _).1 (stKward_of_flow sz hd hκ hz t ht0 ht1 2 le_rfl)
  intro τ hτ
  filter_upwards [hKw τ hτ] with n hn
  intro b
  have h := hn (![true, false], ![b])
  have hrot : ∀ x : Zd d (sz.L n),
      STKI sz n (STflowE z n) (t n) ⟨List.ofFn ![true, false], List.ofFn ![b] ++ [x]⟩ =
        STKloop sz n (STflowE z n) (t n) ![false, true] ![x, b] := by
    intro x
    have hr := KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) (STflowE z n) (sz.three_le_L n) (sz.W_pos n)
      (hE2 n) (t n) ⟨ht0 n, ht1 n⟩ false x [true] [b] rfl
    simp only [STKI, STKloop, KLloopOf, List.ofFn_succ, List.ofFn_zero]
    simpa using hr.symm
  simp only [hrot] at h
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have := sz.W_pos n
    positivity
  have hη := etaT_pos (hE2 n) (ht1 n)
  simp only [Nat.sub_self, pow_zero, mul_one] at h
  calc _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ τ * ((((sz.W n : ℕ) : ℝ) ^ d *
        etaT (STflowE z n) (t n))⁻¹)) := mul_le_mul_of_nonneg_left h hWd.le
    _ = _ := by field_simp

end Ta

/-! ## 12. Target 4: the term `I₄₁` (`(eq:termI41)`, `B:59-72`) -/

/-- **`lwExpI41_holds`** (target 4): `I₄₁ ≺ η_t⁻¹ B³`.  Route of `B:59-72`: with `X = 𝓛^{(1)} - m`,
`A = 𝓛^{(2)}_{(-,+),(a,a₂)}`, `A' = 𝓛^{(2)}_{(-,+),(a₃,b)}`, `A = K + D`, `A' = K' + D'`:
`𝔼[X A A'] = 𝔼[X A D'] + (𝔼 X) K K' + 𝔼[X D] K'` (`lwExpTerm_I41_split`).  The first part is
`T_a = 𝔼 R_a ≺ η⁻¹ B³` (`lwExpTerm_Ta_det`: `‖X‖‖D'‖ ≺ B³` by `STLK`, `A ≥ 0`, Ward `(WI_calL)`
`lwExpTerm_ward_sum_le`, `‖𝓛^{(1)}‖ ≺ 1` by `STLmax`, then `≺ → 𝔼`); `T_{b1}`, `T_{b2}` are bounded by
`(‖𝔼X‖‖K‖ or ‖𝔼[X D]‖) · W^d Σ_{a₃} ‖K'‖` with `STExpAvgAt` (`STExpAvgAt_of_LWAvgLaw`), `STKbound`,
`lwExpTerm_XD` and `(WI_calK)` (`lwExpTerm_Kward`). -/
theorem lwExpI41_holds (d : ℕ) : LWExpI41 d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLW hLmax hLK
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hEX := (st6_prec_det_iff sz hsz _ _).1 (STExpAvgAt_of_LWAvgLaw sz hd hκ hε hz t ht0 htz hLW)
  have hKb := (st6_prec_det_iff sz hsz _ _).1
    (stKbound_of_flow sz hd hκ hz t ht0 ht1 2 (by norm_num))
  have hXD := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm_XD sz hd hκ hε hz ht0 htz hLK)
  have hTa := (st6_prec_det_iff sz hsz _ _).1 (lwExpTerm_Ta_det sz hd hκ hε hz ht0 htz hLmax hLK)
  have hKw := lwExpTerm_Kward sz hd hκ hz ht0 htz
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ4 : 0 < τ / 4 := by positivity
  filter_upwards [hEX (τ / 4) hτ4, hKb (τ / 4) hτ4, hXD (τ / 4) hτ4, hTa (τ / 4) hτ4, hKw (τ / 4) hτ4,
    ((tendsto_rpow_atTop hτ4).comp hsz).eventually (eventually_ge_atTop 2)] with
    n hEXn hKn hXDn hTan hKwn hN2
  rintro ⟨σ₁, ab⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB : 0 < B := STBctl_pos sz n (ht1 n)
  set e : ℝ := (etaT (STflowE z n) (t n))⁻¹ with hedef
  have he : 0 < e := inv_pos.2 (etaT_pos (hE2 n) (ht1 n))
  have hN2' : (2 : ℝ) ≤ N ^ (τ / 4) := hN2
  set u : ℝ := N ^ (τ / 4) with hu
  have hu0 : 0 ≤ u := by linarith
  have hsplit := lwExpTerm_I41_split (P := sz.seqP) (((sz.W n : ℕ) : ℂ) ^ d)
    (fun a₁ a₂ => SB d (sz.L n) (sz.lam n) a₁ a₂)
    (fun a₁ ω => Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁)
    (fun a₂ ω => Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω)
    (fun a₃ ω => Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1] ω)
    (fun a₂ => STKloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂])
    (fun a₃ => STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1])
    (fun a₁ => lwExpTerm_BM_X sz n (hE2 n) (ht1 n) σ₁ a₁)
    (fun a₂ => lwExpTerm_BM_Lloop sz n (hE2 n) (ht1 n) (k := 1) _ _)
    (fun a₃ => lwExpTerm_BM_Lloop sz n (hE2 n) (ht1 n) (k := 1) _ _)
  -- the three bounds
  have hx : ∀ a₁ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
      mSigma (STflowE z n) σ₁) ∂(sz.seqP)‖ ≤ u * B ^ 2 := fun a₁ => by
    rw [lwExpTerm_int_X sz n (hE2 n) (ht1 n)]; exact hEXn (σ₁, a₁)
  have hk : ∀ a₂ : Zd d (sz.L n),
      ‖STKloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂]‖ ≤ u * B := fun a₂ => by
    simpa using hKn (![false, true], ![ab 0, a₂])
  have hxd : ∀ a₁ a₂ : Zd d (sz.L n), ‖∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
      mSigma (STflowE z n) σ₁) * (Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω -
        STKloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂]) ∂(sz.seqP)‖ ≤ u * B ^ 3 :=
    fun a₁ a₂ => hXDn ((σ₁, ![false, true]), (![ab 0, a₂], a₁))
  have hkw : ((sz.W n : ℕ) : ℝ) ^ d * ∑ a₃,
      ‖STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]‖ ≤ u * e := hKwn (ab 1)
  have hT1 := lwExpTerm_Tb_n sz n
    (fun a₁ a₂ => (∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
      mSigma (STflowE z n) σ₁) ∂(sz.seqP)) * STKloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂])
    (fun a₃ => STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]) (c := (u * B ^ 2) * (u * B))
    (fun a₁ a₂ => by
      rw [norm_mul]
      exact mul_le_mul (hx a₁) (hk a₂) (norm_nonneg _) (by positivity))
  have hT2 := lwExpTerm_Tb_n sz n
    (fun a₁ a₂ => ∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω - mSigma (STflowE z n) σ₁) *
      (Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω -
        STKloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂]) ∂(sz.seqP))
    (fun a₃ => STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1]) (c := u * B ^ 3) hxd
  have hTa' := hTan (σ₁, ab)
  refine (congrArg norm hsplit).le.trans ?_
  have hW0 : 0 ≤ u * e := by positivity
  have hb1 : 0 ≤ (u * B ^ 2) * (u * B) := by positivity
  have hb2 : 0 ≤ u * B ^ 3 := by positivity
  calc _ ≤ ‖∫ ω, lwExpTerm_Ra sz n (STflowE z n) (t n) σ₁ ab ω ∂(sz.seqP)‖ +
        ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
          (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * (((∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
            mSigma (STflowE z n) σ₁) ∂(sz.seqP)) * STKloop sz n (STflowE z n) (t n) ![false, true]
              ![ab 0, a₂]) * STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1])‖ +
        ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
          (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) * ((∫ ω, (Lloop sz n (STflowE z n) (t n) ![σ₁] ![a₁] ω -
            mSigma (STflowE z n) σ₁) * (Lloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂] ω -
              STKloop sz n (STflowE z n) (t n) ![false, true] ![ab 0, a₂]) ∂(sz.seqP)) *
                STKloop sz n (STflowE z n) (t n) ![false, true] ![a₃, ab 1])‖ :=
        (norm_add₃_le).trans (le_of_eq rfl)
    _ ≤ u * (e * B ^ 3) + ((u * B ^ 2) * (u * B)) * (u * e) + (u * B ^ 3) * (u * e) := by
        refine add_le_add (add_le_add hTa' ?_) ?_
        · exact hT1.trans (mul_le_mul_of_nonneg_left hkw hb1)
        · exact hT2.trans (mul_le_mul_of_nonneg_left hkw hb2)
    _ ≤ N ^ τ * (e * B ^ 3) := by
        have hu4 : N ^ τ = u ^ 4 := by
          rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; congr 1; push_cast; ring
        rw [hu4]
        have h1 : 0 ≤ u ^ 3 - u ^ 2 - u - 1 := by nlinarith
        have h2 : 0 ≤ u * (u ^ 3 - u ^ 2 - u - 1) * (e * B ^ 3) :=
          mul_nonneg (mul_nonneg hu0 h1) (by positivity)
        nlinarith [h2]

end RBM.Gauss.Sizes

/-! ## 13. Compiled nonempty instances (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, the merged data `sz0`, `z0`,
`tInst` of `RBM.Gauss.LWInst`): every deterministic hypothesis is discharged (`3 ≤ 3`, `0 < 1/10`,
`flow_z0`, `0 ≤ tInst`, `tInst ≤ lemT z0`); the local laws (`LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`,
`STDecay`) and `LWCutExp` (LW-14b/c) are other gates' pins and stay hypotheses -/

namespace RBM.Gauss.LWInst

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **Instance of `lwTermEXP_of_cut`**: `LWCutExp 3` (LW-14b/c) gives `lem:LWterm_EXP` at the preflight
data, through the merged `inst_LWtermEXP`. -/
theorem lwExpTerm_inst_cut (hcut : LWCutExp 3) (h1 : STLocalEntry sz0 (STflowE z0) tInst)
    (h2 : LWAvgLaw sz0 (STflowE z0) tInst) (h3 : STLmax sz0 (STflowE z0) tInst)
    (h4 : STLK sz0 (STflowE z0) tInst) (h5 : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  inst_LWtermEXP (lwTermEXP_of_cut 3 hcut) h1 h2 h3 h4 h5

/-- **Instance of `lwExpI1_holds`** at `(sz0, z0, tInst)`. -/
theorem lwExpTerm_inst_I1 (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖∑ a₁, (SB 3 (sz0.L n) (sz0.lam n) a₁ (p.2 1) : ℂ) *
          ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1.1] ![a₁] ω - mSigma (STflowE z0 n) p.1.1) *
            Lloop sz0 n (STflowE z0 n) (tInst n) p.1.2 p.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (sz0.Bctl n (tInst n)) ^ 3) :=
  lwExpI1_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLW hLK

/-- **Instance of `lwExpI41_holds`** at `(sz0, z0, tInst)`. -/
theorem lwExpTerm_inst_I41 (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => Bool × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
          (SB 3 (sz0.L n) (sz0.lam n) a₁ a₂ : ℂ) * (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
          ∫ ω, (Lloop sz0 n (STflowE z0 n) (tInst n) ![p.1] ![a₁] ω - mSigma (STflowE z0 n) p.1) *
            Lloop sz0 n (STflowE z0 n) (tInst n) ![false, true] ![p.2 0, a₂] ω *
            Lloop sz0 n (STflowE z0 n) (tInst n) ![false, true] ![a₃, p.2 1] ω ∂(sz0.seqP)‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ 3) :=
  lwExpI41_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLW hLmax hLK

end RBM.Gauss.LWInst

