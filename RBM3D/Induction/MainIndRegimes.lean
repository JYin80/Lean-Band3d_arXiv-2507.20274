/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.SizesComp
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.PfStep5
import RBM3D.Induction.ExpIntEasy
import RBM3D.Induction.IterationsA
import RBM3D.Induction.LocalAvg1
import Mathlib.Data.Nat.Nth

/-!
# ST-5: the main-induction regime assembly (T2245)

Ticket T2245 (DECISIONS §68 (7), (9), (10), §76 (3); supervisor
`docs/supervisor/2026-10-05-1806.md`, "Answers to REQ-2026-10-05-1746", Q1, Q2 "The fix" and
"Assembly" 1-2, Q3).  Paper: arXiv:2507.20274,
`paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`): `lem:main_ind` `1256-1330`, Steps 1-6
`1317-1396`; regimes `3_5:1105`, `3_5:1939`, `6:93-97`.

* Section 1: `STMainIndR d R`, the shape of `STMainInd` under a regime `R` of the time sequences
  (`ST_mainInd_iff_any`, `STMainIndR_mono`).
* Section 2: the four regimes of Step 5/6 lie in the cases of Step 3/4 (`st_caseI_of_reg5III`, ...).
* Section 3: one main-induction step per regime, from the six step pins (`ST_mainIndR_of_steps`, the
  four regime instances `ST_mainIndR_III/I/II/IV_of_steps`).
* Section 4: two stages cut at an intermediate time (`STLocalMax_of_STLocalEntry`,
  `ST_mainIndR_seq`).
* Section 5: the seven predicates along a finite `StrictMono` cover (`STLK_iff_comp_cover`, ...).
* Section 6: the classifier of the stage pattern of `[s_n, t_n]`, and `ST_mainInd_of_regimes`.
* Section 7: `ST_mainInd_of_pins`.
* Section 8: the compiled nonempty instances (namespace `RBM.Gauss.MainIndRegimesInst`).

Why the regimes are assembled by subsequences (DECISIONS §67, §68): the proof of `lem:main_ind` in
`1_2:1317-1396` applies Steps 1-6 on the whole `[s,t]`, and Steps 3-6 are proved per regime
(`3_5:1105`, `3_5:1939`, `6:93-97`); "adding intermediate times" (`3_5:1939`) cannot be done inside
Steps 2-5 (their losses `((1-s)/(1-s'))^{C_d}` and `(L^d/4)^{k-1}` are anchored at `s`), so the
formal
proof reruns the whole induction step from each cut `1-g²`, `1-g²/L²`, `1-g²/L^d`, composes the
single-time conclusions (`ST_mainIndR_seq`), and glues the ten stage patterns along finitely many
subsequences (route (A), `Sizes.comp`; paper-delta candidates `T2245a`, `T2245b`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

universe w

/-! ## 1. The shape `STMainIndR` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`lem:main_ind` under a regime `R`** (`1_2:1256-1330`; DECISIONS §68 (7), supervisor 1806 Q2 "The fix"):
the body of `STMainInd` (`Induction/Defs.lean:294-306`) with the hypothesis `R sz s t` after
`t ≤ lemT z`.  One constant `𝔠_d` serves every flow. -/
def STMainIndR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) → R sz s t →
          (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
            STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
          STConStInd sz 𝔠d s t →
          STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
            STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
            STDecayStrong sz (STflowE z) t

/-- The body of `STMainIndR` after the constant `𝔠_d` (private: the constant is lowered and
combined in the assembly). -/
private def STMainIndRAt (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (κ ε 𝔡 𝔠d : ℝ) : Prop :=
  ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
      (∀ n, t n ≤ lemT (z n)) → R sz s t →
      (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
        STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
      STConStInd sz 𝔠d s t →
      STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
        STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
        STDecayStrong sz (STflowE z) t

/-- **`STMainInd` is the regime-free instance** (`STAny` is `True`). -/
theorem ST_mainInd_iff_any (d : ℕ) : STMainInd d ↔ STMainIndR d STAny := by
  constructor
  · intro h hd κ ε 𝔡 hκ hε h𝔡
    obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
    exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hsT hst htT _ hyp hcon =>
      H 𝔠 sz z hflow s t hs0 hsT hst htT hyp hcon⟩
  · intro h hd κ ε 𝔡 hκ hε h𝔡
    obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
    exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hsT hst htT hyp hcon =>
      H 𝔠 sz z hflow s t hs0 hsT hst htT trivial hyp hcon⟩

/-- **A weaker regime gives a stronger statement** (as `ST_step6R_mono`): `R' ⊆ R` and `STMainIndR d R`
give `STMainIndR d R'`. -/
theorem STMainIndR_mono (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STMainIndR d R) :
    STMainIndR d R' := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hc', H⟩ := h hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨c, hc, hc', fun 𝔠 sz z hflow s t hs0 hsT hst htT hR' hyp hcon =>
    H 𝔠 sz z hflow s t hs0 hsT hst htT (hRR sz s t hR') hyp hcon⟩

/-- `STMainIndRAt` at a smaller constant (a smaller exponent is the stronger hypothesis
`(con_st_ind)`, `st5_conStInd_mono`). -/
private theorem STMainIndRAt_mono {d : ℕ} {R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    {κ ε 𝔡 c c' : ℝ} (hc' : 0 < c') (hcc : c' ≤ c) (h : STMainIndRAt d R κ ε 𝔡 c) :
    STMainIndRAt d R κ ε 𝔡 c' := by
  intro 𝔠 sz z hflow s t hs0 hsT hst htT hR hyp hcon
  exact h 𝔠 sz z hflow s t hs0 hsT hst htT hR hyp
    (st5_conStInd_mono sz hcon (st5_t_lt_one sz hflow htT) hc' hcc)

/-! ## 2. The Step 5/6 regimes inside the Step 3/4 cases (supervisor 1806 Q2 "Assembly" 1) -/

/-- Regime (iii) `g² ≤ 1-t` lies in case (i) `g²/L² ≤ 1-t` (`g²/L² ≤ g²`, `L ≥ 3`). -/
theorem st_caseI_of_reg5III (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5III sz s t) :
    STCaseI sz s t := by
  intro n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
    nlinarith
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 :=
    div_le_self hg hL
  exact this.trans (h n)

/-- Regime (i) `g²/L² ≤ 1-t ∧ 1-s ≤ g²` lies in case (i): the first conjunct. -/
theorem st_caseI_of_reg5I (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5I sz s t) :
    STCaseI sz s t := fun n => (h n).1

/-- Regime (ii) `… ∧ 1-s ≤ g²/L²` lies in case (ii) `1-s ≤ g²/L²`: the second conjunct. -/
theorem st_caseII_of_reg5II (d : ℕ) (sz : Sizes d) (s t : ℕ → ℝ) (h : STReg5II sz s t) :
    STCaseII sz s t := fun n => (h n).2

/-- Regime (iv) `1-s ≤ g²/L^d` lies in case (ii) `1-s ≤ g²/L²` (`2 ≤ d`, `L ≥ 1`: `L^d ≥ L²`). -/
theorem st_caseII_of_reg5IV (d : ℕ) (hd : 2 ≤ d) (sz : Sizes d) (s t : ℕ → ℝ)
    (h : STReg5IV sz s t) : STCaseII sz s t := by
  intro n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
    linarith
  have h2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL hd
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have hpos : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by positivity
  have : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hg hpos h2
  exact (h n).trans this

/-! ## 3. One main-induction step per regime -/

/-- **One main-induction step** from the six step pins (the proof of the T2191 probe `ST_mainInd_of_steps`,
`t/T2191` 96c6b4c `:351-404`, with the regime `R` threaded through): Step 2 gives `(C_d, 𝔠_d²)`, Steps 3-6 give
their constants, Step 1 holds for every `𝔠_d ∈ (0, 10^{-2}]`; the constant is the minimum (`(con_st_ind)` for the
minimum implies it for each larger exponent, `st5_conStInd_mono`).  The Step 3/4 regime `R34` contains `R`
(`3 ≤ d → R ⊆ R34`).  `STKbound`, `STKward` are the theorems `stKbound_of_flow`, `stKward_of_flow`. -/
theorem ST_mainIndR_of_steps (d : ℕ) (R R34 : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hR : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t)
    (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3R d R34) (h4 : STStep4R d R34)
    (h5 : STStep5R d R) (h6 : STStep6R d R) : STMainIndR d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Cd, hCd, c₂, hc₂, hc₂', H₂⟩ := h2 hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := h3 hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := h4 hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := h5 hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₆, hc₆, hc₆', H₆⟩ := h6 hd κ ε 𝔡 hκ hε h𝔡
  have hcpos : 0 < min c₂ (min c₃ (min c₄ (min c₅ c₆))) :=
    lt_min hc₂ (lt_min hc₃ (lt_min hc₄ (lt_min hc₅ hc₆)))
  have hcle : min c₂ (min c₃ (min c₄ (min c₅ c₆))) ≤ 1 / 100 := (min_le_left _ _).trans hc₂'
  refine ⟨min c₂ (min c₃ (min c₄ (min c₅ c₆))), hcpos, hcle, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hsT hst htT hRst hyp hcon
  obtain ⟨hLK, hDec, hDecS, hLoc, hExp⟩ := hyp
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow htT
  have hKb : STKbound sz (STflowE z) := stKbound_of_flow sz hd hκ hflow
  have hKw : STKward sz (STflowE z) := stKward_of_flow sz hd hκ hflow
  have hR34 : R34 sz s t := hR hd sz s t hRst
  have m : ∀ c', min c₂ (min c₃ (min c₄ (min c₅ c₆))) ≤ c' → STConStInd sz c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  -- Step 1 (every `𝔠_d ∈ (0, 10^{-2}]`)
  obtain ⟨hS1L, hS1W⟩ := h1 κ ε 𝔡 hκ hε h𝔡 _ hcpos hcle 𝔠 sz z hflow s t hs0 hsT hst htT hKb hLK hLoc hcon
  -- Step 2
  have hS2 : STStep2Concl sz (STflowE z) s t Cd :=
    H₂ 𝔠 sz z hflow s t hs0 hsT hst htT hLK hDec (m c₂ (min_le_left _ _)) hS1L hS1W
  -- Step 3
  have hS3 : STLmaxU sz (STflowE z) s t :=
    H₃ 𝔠 sz z hflow s t hs0 hst htT hR34 hKb hKw hLK
      (m c₃ ((min_le_right _ _).trans (min_le_left _ _))) hS1L hS2
  -- Step 4
  have hS4 : STLKU sz (STflowE z) s t :=
    H₄ 𝔠 sz z hflow s t hs0 hst htT hR34 hKb hKw hLK
      (m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hS1L hS2 hS3
  -- Step 5
  have hS5 : STStep5Concl sz (STflowE z) s t :=
    H₅ 𝔠 sz z hflow s t hs0 hst htT hRst hKb hKw hLK hDec hDecS
      (m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
      hS1L hS2 hS3 hS4
  -- Step 6
  have hS6 : STExp2U sz (STflowE z) s t :=
    H₆ 𝔠 sz z hflow s t hs0 hst htT hRst hLK hDec hExp
      (m c₆ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
      ⟨hS2.1, hS2.2.1⟩ hS3 hS4 hS5.1
  -- the endpoints `u = t`
  obtain ⟨hD5, hDS5⟩ := ST_step5_assembly sz (fun n => (hst n).le) hS5
  exact ⟨STLK_of_STLKU sz (fun n => (hst n).le) hS4, STLmax_of_STLmaxU sz (fun n => (hst n).le) hS3, hD5,
    STExp2_of_STExp2U sz (fun n => (hst n).le) hS6,
    STLocalEntry_of_STLocalEntryU sz (fun n => (hst n).le) hS2.1, hDS5⟩

/-- **Regime (iii)** (`1-s ≥ 1-t ≥ ilambda²`): Steps 3-4 in case (i), Steps 5, 6 in regime (iii). -/
theorem ST_mainIndR_III_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3I d)
    (h4 : STStep4I d) (h5 : STStep5III d) (h6 : STStep6III d) : STMainIndR d STReg5III :=
  ST_mainIndR_of_steps d STReg5III STCaseI (fun _ => st_caseI_of_reg5III d) h1 h2 h3 h4 h5 h6

/-- **Regime (i)** (`ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²`): Steps 3-4 in case (i). -/
theorem ST_mainIndR_I_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3I d)
    (h4 : STStep4I d) (h5 : STStep5I d) (h6 : STStep6I d) : STMainIndR d STReg5I :=
  ST_mainIndR_of_steps d STReg5I STCaseI (fun _ => st_caseI_of_reg5I d) h1 h2 h3 h4 h5 h6

/-- **Regime (ii)** (`ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`): Steps 3-4 in case (ii). -/
theorem ST_mainIndR_II_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3II d)
    (h4 : STStep4II d) (h5 : STStep5II d) (h6 : STStep6II d) : STMainIndR d STReg5II :=
  ST_mainIndR_of_steps d STReg5II STCaseII (fun _ => st_caseII_of_reg5II d) h1 h2 h3 h4 h5 h6

/-- **Regime (iv)** (`1-t ≤ 1-s ≤ ilambda²/L^d`): Steps 3-4 in case (ii) (`3 ≤ d`). -/
theorem ST_mainIndR_IV_of_steps (d : ℕ) (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3II d)
    (h4 : STStep4II d) (h5 : STStep5IV d) (h6 : STStep6IV d) : STMainIndR d STReg5IV :=
  ST_mainIndR_of_steps d STReg5IV STCaseII
    (fun hd => st_caseII_of_reg5IV d (by omega)) h1 h2 h3 h4 h5 h6

/-! ## 4. Two stages cut at an intermediate time -/

/-- **`(Gt_bound)` gives `(Gt_bound+IND)`** (the input of the next stage from the conclusion of the previous one,
paper-delta candidate `T2245b`): `|(G_τ - M)_{xy}|² ≺ W^{-d}B_{τ,K} ≤ W^{-d}B_{τ,0} = Bctl` (`localAvg1_STWB_le`,
no hypothesis on `τ`), so `‖G_τ - M‖²_max ≺ Bctl` (`StochDomAt.of_subset`: the failure event is eventually
contained in the failure event of `STLocalEntry`, at the same exponent; `Bctl` is not needed to tend to `0`), and
`iterationsA_prec_rpow` with `θ = 1/2`, `(‖x‖²)^{1/2} = ‖x‖`, gives `‖G_τ - M‖ ≺ Bctl^{1/2}`. -/
theorem STLocalMax_of_STLocalEntry (d : ℕ) (sz : Sizes d) (E τ : ℕ → ℝ) (h : STLocalEntry sz E τ) :
    STLocalMax sz E τ := by
  have hsq : sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖ ^ 2) (fun n _ _ => sz.Bctl n (τ n)) := by
    refine RBM.StochDomAt.of_subset h fun τ' hτ' => ⟨τ', hτ', Eventually.of_forall fun n ω hω => ?_⟩
    obtain ⟨u, hu⟩ := hω
    refine ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩
    exact localAvg1_STWB_le sz n (τ n) _
  have hB : ∀ n, 0 ≤ sz.Bctl n (τ n) := fun n => by unfold Sizes.Bctl Bparam; positivity
  have h2 := iterationsA_prec_rpow sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => by positivity) (fun n _ _ => hB n) (θ := 1 / 2) (by norm_num) hsq
  have e : ∀ n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      (‖STGM sz n (E n) (τ n) ω p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) = ‖STGM sz n (E n) (τ n) ω p.1 p.2‖ := by
    intro n p ω
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  simp only [e] at h2
  exact h2

/-- **Two stages** `[s,m]`, `[m,t]` (`STRegSeq R₁ R₂`): the conclusions of stage 1 at `m` are the premises of stage 2
(`STLK`, `STDecay`, `STDecayStrong`, `STExp2` by identity, `STLocalMax` by `STLocalMax_of_STLocalEntry`),
`(con_st_ind)` passes to both pieces (`st_conStInd_sub`, `m` strictly inside) and to the smaller exponent
(`st5_conStInd_mono`, `t < 1`); the constant is `min c₁ c₂`. -/
private theorem STMainIndRAt_seq {d : ℕ} {R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    {κ ε 𝔡 c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h₁ : STMainIndRAt d R₁ κ ε 𝔡 c₁)
    (h₂ : STMainIndRAt d R₂ κ ε 𝔡 c₂) :
    STMainIndRAt d (STRegSeq R₁ R₂) κ ε 𝔡 (min c₁ c₂) := by
  intro 𝔠 sz z hflow s t hs0 hsT hst htT hR hyp hcon
  obtain ⟨m, hsm, hmt, hR₁, hR₂⟩ := hR
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow htT
  have hm1 : ∀ n, m n < 1 := fun n => (hmt n).trans (ht1 n)
  have hmT : ∀ n, m n ≤ lemT (z n) := fun n => (hmt n).le.trans (htT n)
  have hcon₁ : STConStInd sz (min c₁ c₂) s m :=
    st_conStInd_sub sz hcpos hcon (fun n => le_rfl) hsm (fun n => (hmt n).le) ht1
  have hcon₂ : STConStInd sz (min c₁ c₂) m t :=
    st_conStInd_sub sz hcpos hcon (fun n => (hsm n).le) hmt (fun n => le_rfl) ht1
  obtain ⟨hLK₁, -, hDec₁, hExp₁, hLE₁, hDecS₁⟩ :=
    h₁ 𝔠 sz z hflow s m hs0 hsT hsm hmT hR₁ hyp
      (st5_conStInd_mono sz hcon₁ hm1 hcpos (min_le_left _ _))
  exact h₂ 𝔠 sz z hflow m t (fun n => (hs0 n).trans (hsm n).le) hmT hmt htT hR₂
    ⟨hLK₁, hDec₁, hDecS₁, STLocalMax_of_STLocalEntry d sz _ _ hLE₁, hExp₁⟩
    (st5_conStInd_mono sz hcon₂ ht1 hcpos (min_le_right _ _))

/-- **Chaining two stages**: `STMainIndR d R₁ → STMainIndR d R₂ → STMainIndR d (STRegSeq R₁ R₂)`; the
constant is `min c₁ c₂`; the final conclusions are those of stage 2, all at the single time `t`. -/
theorem ST_mainIndR_seq (d : ℕ) (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h₁ : STMainIndR d R₁) (h₂ : STMainIndR d R₂) : STMainIndR d (STRegSeq R₁ R₂) := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := h₁ hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := h₂ hd κ ε 𝔡 hκ hε h𝔡
  exact ⟨min c₁ c₂, lt_min hc₁ hc₂, (min_le_left _ _).trans hc₁',
    STMainIndRAt_seq hc₁ hc₂ H₁ H₂⟩

end RBM.Gauss.Sizes

/-! ## 5. The seven predicates along a finite cover

`X sz E τ ↔ ∀ k, X (sz.comp (φ k)) (E ∘ φ k) (τ ∘ φ k)` for a finite family of strictly increasing
`φ k` whose ranges cover all large `n` (`Prec_iff_comp_cover`; the commutations of the per-`n` objects
with `reindex` are `rfl`, `Induction/SizesComp.lean:285-305`; for `STExp2` the deterministic left side
integrates over the whole law and transfers by `integral_Lloop_reindex`).  The outer `∀ k ≥ 1` /
`∀ D > 0` of the predicates is carried through. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

theorem STLK_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STLK sz E τ ↔ ∀ k, STLK (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  constructor
  · intro h k' k hk
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl) (h k hk)
  · intro h k hk
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => rfl)
      (fun k j u ω => rfl)).2 (fun k' => h k' k hk)

theorem STLmax_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STLmax sz E τ ↔ ∀ k, STLmax (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  constructor
  · intro h k' k hk
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl) (h k hk)
  · intro h k hk
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => rfl)
      (fun k j u ω => rfl)).2 (fun k' => h k' k hk)

theorem STDecay_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STDecay sz E τ ↔ ∀ k, STDecay (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  constructor
  · intro h k' D hD
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl) (h D hD)
  · intro h D hD
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => rfl)
      (fun k j u ω => rfl)).2 (fun k' => h k' D hD)

theorem STDecayStrong_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STDecayStrong sz E τ ↔
      ∀ k, STDecayStrong (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  constructor
  · intro h k' D hD
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl) (h D hD)
  · intro h D hD
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => rfl)
      (fun k j u ω => rfl)).2 (fun k' => h k' D hD)

theorem STLocalMax_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STLocalMax sz E τ ↔
      ∀ k, STLocalMax (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  constructor
  · intro h k'
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl) h
  · intro h
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => rfl)
      (fun k j u ω => rfl)).2 h

theorem STLocalEntry_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STLocalEntry sz E τ ↔
      ∀ k, STLocalEntry (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  constructor
  · intro h k'
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl) h
  · intro h
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => rfl)
      (fun k j u ω => rfl)).2 h

theorem STExp2_iff_comp_cover (d : ℕ) (sz : Sizes d) (ι : Type) [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (E τ : ℕ → ℝ) :
    STExp2 sz E τ ↔ ∀ k, STExp2 (sz.comp (φ k)) (fun j => E (φ k j)) (fun j => τ (φ k j)) := by
  have hξ : ∀ (k : ι) (j : ℕ) (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L (φ k j)))) (ω : SeqΩ sz),
      ‖(∫ ω', Lloop (sz.comp (φ k)) j (E (φ k j)) (τ (φ k j)) p.1 p.2 ω' ∂(seqP (sz.comp (φ k)))) -
          STKloop (sz.comp (φ k)) j (E (φ k j)) (τ (φ k j)) p.1 p.2‖ =
        ‖(∫ ω', Lloop sz (φ k j) (E (φ k j)) (τ (φ k j)) p.1 p.2 ω' ∂(seqP sz)) -
          STKloop sz (φ k j) (E (φ k j)) (τ (φ k j)) p.1 p.2‖ := by
    intro k j p ω
    exact congrArg (fun x : ℂ => ‖x - STKloop sz (φ k j) (E (φ k j)) (τ (φ k j)) p.1 p.2‖)
      (integral_Lloop_reindex sz (φ k) (hφ k).injective j (E (φ k j)) (τ (φ k j)) p.1 p.2)
  constructor
  · intro h k'
    exact Prec_comp sz (φ k') (hφ k') _ _ _ _ (fun j u ω => hξ k' j u ω) (fun j u ω => rfl) h
  · intro h
    exact (Prec_iff_comp_cover sz φ hφ hcov _ _ _ _ (fun k j u ω => hξ k j u ω)
      (fun k j u ω => rfl)).2 h

end RBM.Gauss.Sizes

/-! ## 6. The stage pattern of `[s_n, t_n]` and `ST_mainInd_of_regimes`

The cuts of `[0, t₀]` are `c₁ = 1-g²`, `c₂ = 1-g²/L²`, `c₃ = 1-g²/L^d` (`g = sz.lam n`); the four regimes of
Steps 5, 6 are the four intervals between them (`3_5:1939`, `6:93-97`).  `c₁ ≤ c₂ ≤ c₃ ≤ 1`, strictly if `g ≠ 0`
(`L ≥ 3`, `d ≥ 3`).  The stage of `s_n` is `0` if `s < c₁`, `1` if `c₁ ≤ s < c₂`, `2` if `c₂ ≤ s < c₃`, `3` if
`c₃ ≤ s`; the stage of `t_n` is `0` if `t ≤ c₁`, `1` if `c₁ < t ≤ c₂`, `2` if `c₂ < t ≤ c₃`, `3` if `c₃ < t`
(the `<`/`≤` choice excludes point-stages).  The pattern `(i, j)` has `i ≤ j` (ten values) and `[s,t]` is cut at
`c_{i+1}, …, c_j`, each stage on `[c_k, c_{k+1}]` with equality at the cuts. -/

namespace RBM.Gauss.Sizes
open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The cuts `c_1 = 1-g²`, `c_2 = 1-g²/L²`, `c_3 = 1-g²/L^d` of `[0, t₀]` at size index `n` (`k = 1, 2, 3`;
`g = sz.lam n`); `k = 0` and `k ≥ 4` are not used. -/
def STCutK {d : ℕ} (sz : Sizes d) : ℕ → ℕ → ℝ
  | 1, n => 1 - sz.lam n ^ 2
  | 2, n => 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2
  | _, n => 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d

/-- The cuts commute with `Sizes.comp`. -/
theorem STCutK_comp {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (k j : ℕ) :
    STCutK (sz.comp φ) k j = STCutK sz k (φ j) := by
  rcases k with _ | _ | _ | k <;> rfl

/-- `c_1 ≤ c_2 ≤ c_3` (`L ≥ 1`, `d ≥ 2`). -/
theorem STCutK_mono {d : ℕ} (hd : 2 ≤ d) (sz : Sizes d) {k k' : ℕ} (h1 : 1 ≤ k) (hkk : k ≤ k')
    (h3 : k' ≤ 3) (n : ℕ) : STCutK sz k n ≤ STCutK sz k' n := by
  have hL : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by linarith
  have hL2 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ 2 := one_le_pow₀ hL1
  have hLd : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have a12 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 := div_le_self hg hL2
  have a23 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hg (by positivity) hLd
  have hk3 : k ≤ 3 := hkk.trans h3
  interval_cases k <;> interval_cases k' <;> simp only [STCutK] <;> linarith

/-- `c_1 < c_2 < c_3` if `g ≠ 0` (`L ≥ 3`, `d ≥ 3`). -/
theorem STCutK_lt {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 2) (n : ℕ)
    (hg : 0 < sz.lam n ^ 2) : STCutK sz k n < STCutK sz (k + 1) n := by
  have hL : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast sz.three_le_L n
  have hL1 : (1 : ℝ) < ((sz.L n : ℕ) : ℝ) := by linarith
  have hL2 : (1 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := one_lt_pow₀ hL1 (by norm_num)
  have hLd : ((sz.L n : ℕ) : ℝ) ^ 2 < ((sz.L n : ℕ) : ℝ) ^ d := pow_lt_pow_right₀ hL1 (by omega)
  have a12 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < sz.lam n ^ 2 := div_lt_self hg hL2
  have a23 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 :=
    div_lt_div_of_pos_left hg (by positivity) hLd
  interval_cases k <;> simp only [STCutK] <;> linarith

/-- The regime of stage `k`: (iii), (i), (ii), (iv) for `k = 0, 1, 2, 3`. -/
def STRegK (k : ℕ) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  match k with
  | 0 => STReg5III sz s t
  | 1 => STReg5I sz s t
  | 2 => STReg5II sz s t
  | _ => STReg5IV sz s t

/-- The regime of the chain of stages `i, i+1, …, i+m`: the nesting `STRegSeq (STRegK i) (STRegSeq (STRegK (i+1)) …)`. -/
def STRegChain (i m : ℕ) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  match m with
  | 0 => STRegK i sz s t
  | m + 1 => ∃ mid : ℕ → ℝ, (∀ n, s n < mid n) ∧ (∀ n, mid n < t n) ∧ STRegK i sz s mid ∧
      STRegChain (i + 1) m sz mid t

/-- One step of the nesting is `STRegSeq`. -/
theorem STRegChain_succ (i m : ℕ) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) :
    STRegChain i (m + 1) sz s t ↔ STRegSeq (STRegK i) (STRegChain (i + 1) m) sz s t := Iff.rfl

set_option linter.flexible false in
/-- The regime of stage `k` in terms of the cuts: `c_k ≤ s` (`k ≥ 1`) and `t ≤ c_{k+1}` (`k ≤ 2`). -/
theorem STRegK_iff {d : ℕ} (sz : Sizes d) {k : ℕ} (hk : k ≤ 3) (a b : ℕ → ℝ) :
    STRegK k sz a b ↔ ∀ n, (1 ≤ k → STCutK sz k n ≤ a n) ∧ (k ≤ 2 → b n ≤ STCutK sz (k + 1) n) := by
  interval_cases k <;> refine forall_congr' fun n => ?_ <;> simp [STCutK] <;>
    first
    | exact ⟨fun h => by linarith, fun h => by linarith⟩
    | exact ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩

/-- The stage of `s_n`. -/
def STStageS {d : ℕ} (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) : ℕ :=
  if s n < STCutK sz 1 n then 0 else if s n < STCutK sz 2 n then 1
    else if s n < STCutK sz 3 n then 2 else 3

/-- The stage of `t_n`. -/
def STStageT {d : ℕ} (sz : Sizes d) (t : ℕ → ℝ) (n : ℕ) : ℕ :=
  if t n ≤ STCutK sz 1 n then 0 else if t n ≤ STCutK sz 2 n then 1
    else if t n ≤ STCutK sz 3 n then 2 else 3

/-- The defining properties of the stage of `s_n`. -/
theorem STStageS_spec {d : ℕ} (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) :
    STStageS sz s n ≤ 3 ∧ (1 ≤ STStageS sz s n → STCutK sz (STStageS sz s n) n ≤ s n) ∧
      (STStageS sz s n ≤ 2 → s n < STCutK sz (STStageS sz s n + 1) n) := by
  unfold STStageS
  split_ifs with h1 h2 h3
  · simpa using h1
  · refine ⟨by norm_num, fun _ => not_lt.1 h1, fun _ => by simpa using h2⟩
  · refine ⟨by norm_num, fun _ => not_lt.1 h2, fun _ => by simpa using h3⟩
  · refine ⟨by norm_num, fun _ => not_lt.1 h3, fun h => by omega⟩

/-- The defining properties of the stage of `t_n`. -/
theorem STStageT_spec {d : ℕ} (sz : Sizes d) (t : ℕ → ℝ) (n : ℕ) :
    STStageT sz t n ≤ 3 ∧ (STStageT sz t n ≤ 2 → t n ≤ STCutK sz (STStageT sz t n + 1) n) ∧
      (1 ≤ STStageT sz t n → STCutK sz (STStageT sz t n) n < t n) := by
  unfold STStageT
  split_ifs with h1 h2 h3
  · simpa using h1
  · refine ⟨by norm_num, fun _ => by simpa using h2, fun _ => not_le.1 h1⟩
  · refine ⟨by norm_num, fun _ => by simpa using h3, fun _ => not_le.1 h2⟩
  · refine ⟨by norm_num, fun h => by omega, fun _ => not_le.1 h3⟩

/-- Stage of `s` at most stage of `t` (`s < t`): `i > j` is empty. -/
theorem STStage_le {d : ℕ} (hd : 2 ≤ d) (sz : Sizes d) (s t : ℕ → ℝ) (n : ℕ) (hst : s n < t n) :
    STStageS sz s n ≤ STStageT sz t n := by
  by_contra h
  have h := not_le.1 h
  obtain ⟨hi3, hi1, -⟩ := STStageS_spec sz s n
  obtain ⟨hj3, hj2, -⟩ := STStageT_spec sz t n
  have h1 := hi1 (by omega)
  have h2 := hj2 (by omega)
  have h3 := STCutK_mono hd sz (k := STStageT sz t n + 1) (k' := STStageS sz s n) (by omega) (by omega)
    hi3 n
  linarith

/-- **The regime of a pattern** `(i, j)`, `i ≤ j`: the chain of stages `i, i+1, …, j`, cut at the intermediate times
`1 - g²`, `1 - g²/L²`, `1 - g²/L^d` that lie strictly inside `(s,t)` (`m = j - i` cuts). -/
theorem STRegChain_holds {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) :
    ∀ (m i : ℕ) (a b : ℕ → ℝ), i + m ≤ 3 → (∀ n, 1 ≤ i → STCutK sz i n ≤ a n) →
      (∀ n, i + m ≤ 2 → b n ≤ STCutK sz (i + m + 1) n) →
      (0 < m → ∀ n, 0 < sz.lam n ^ 2 ∧ a n < STCutK sz (i + 1) n ∧ STCutK sz (i + m) n < b n) →
      STRegChain i m sz a b := by
  intro m
  induction m with
  | zero =>
    intro i a b hi hlo hhi _
    exact (STRegK_iff sz (by omega) a b).2 fun n => ⟨hlo n, fun h => by simpa using hhi n (by omega)⟩
  | succ m ih =>
    intro i a b hi hlo hhi hstr
    obtain ⟨hg, -, -⟩ := hstr (Nat.succ_pos m) 0
    refine ⟨fun n => STCutK sz (i + 1) n, fun n => (hstr (Nat.succ_pos m) n).2.1, fun n => ?_, ?_, ?_⟩
    · exact lt_of_le_of_lt (STCutK_mono (by omega) sz (k := i + 1) (k' := i + (m + 1)) (by omega)
        (by omega) (by omega) n) (hstr (Nat.succ_pos m) n).2.2
    · exact (STRegK_iff sz (by omega) a _).2 fun n => ⟨hlo n, fun _ => le_rfl⟩
    · refine ih (i + 1) _ b (by omega) (fun n _ => le_rfl) (fun n h => ?_) (fun hm n => ?_)
      · have := hhi n (by omega)
        rwa [show i + (m + 1) + 1 = i + 1 + m + 1 by omega] at this
      · refine ⟨(hstr (Nat.succ_pos m) n).1, STCutK_lt hd sz (k := i + 1) (by omega) (by omega) n
          (hstr (Nat.succ_pos m) n).1, ?_⟩
        have := (hstr (Nat.succ_pos m) n).2.2
        rwa [show i + (m + 1) = i + 1 + m by omega] at this

/-- The stage pattern of `[s_n, t_n]`: the stage of `s_n` and of `t_n`, as an element of the finite type
`Fin 4 × Fin 4` (only the ten pairs `i ≤ j` occur, `STStage_le`). -/
def STPattern {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (n : ℕ) : Fin 4 × Fin 4 :=
  (⟨STStageS sz s n, by have := (STStageS_spec sz s n).1; omega⟩,
    ⟨STStageT sz t n, by have := (STStageT_spec sz t n).1; omega⟩)

/-- On a class of constant pattern `(i, j)`, enumerated by `φ`, the regime of the pattern holds along `sz.comp φ`. -/
theorem STRegChain_of_class {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (s t : ℕ → ℝ) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (φ : ℕ → ℕ) (P : Fin 4 × Fin 4) (hφ : ∀ j', STPattern sz s t (φ j') = P) :
    (P.1 : ℕ) ≤ P.2 ∧ STRegChain P.1 (P.2 - P.1) (sz.comp φ) (fun j' => s (φ j')) (fun j' => t (φ j')) := by
  have hS : ∀ j', STStageS sz s (φ j') = P.1 := fun j' => congrArg (fun q : Fin 4 × Fin 4 => (q.1 : ℕ)) (hφ j')
  have hT : ∀ j', STStageT sz t (φ j') = P.2 := fun j' => congrArg (fun q : Fin 4 × Fin 4 => (q.2 : ℕ)) (hφ j')
  have hij : (P.1 : ℕ) ≤ P.2 := by
    have := STStage_le (by omega) sz s t (φ 0) (hst _)
    rwa [hS 0, hT 0] at this
  have hj3 : (P.2 : ℕ) ≤ 3 := by omega
  refine ⟨hij, STRegChain_holds hd (sz.comp φ) (P.2 - P.1) P.1 _ _ (by omega) (fun n' h => ?_)
    (fun n' h => ?_) (fun hm n' => ?_)⟩
  · have := (STStageS_spec sz s (φ n')).2.1
    rw [hS n'] at this
    rw [STCutK_comp]
    exact this h
  · have := (STStageT_spec sz t (φ n')).2.1
    rw [hT n'] at this
    rw [STCutK_comp, show (P.1 : ℕ) + (P.2 - P.1) + 1 = P.2 + 1 by omega]
    exact this (by omega)
  · have hT1 := (STStageT_spec sz t (φ n')).2.2
    rw [hT n'] at hT1
    have hS2 := (STStageS_spec sz s (φ n')).2.2
    rw [hS n'] at hS2
    have hcut := hT1 (by omega)
    have hmono := STCutK_mono (by omega) sz (k := 1) (k' := (P.2 : ℕ)) le_rfl (by omega) hj3 (φ n')
    have hlam : 0 < sz.lam (φ n') ^ 2 := by
      have h1 : STCutK sz 1 (φ n') = 1 - sz.lam (φ n') ^ 2 := rfl
      linarith [ht1 (φ n')]
    refine ⟨hlam, ?_, ?_⟩
    · rw [STCutK_comp]
      exact hS2 (by omega)
    · rw [STCutK_comp, show (P.1 : ℕ) + (P.2 - P.1) = P.2 by omega]
      exact hcut

/-- Each stage `k ≤ 3` of the four regimes, at the common constant `c`. -/
private theorem STMainIndRAt_stage {d : ℕ} {κ ε 𝔡 c₀ c₁ c₂ c₃ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) (H₀ : STMainIndRAt d STReg5III κ ε 𝔡 c₀) (H₁ : STMainIndRAt d STReg5I κ ε 𝔡 c₁)
    (H₂ : STMainIndRAt d STReg5II κ ε 𝔡 c₂) (H₃ : STMainIndRAt d STReg5IV κ ε 𝔡 c₃) {k : ℕ}
    (hk : k ≤ 3) : STMainIndRAt d (STRegK k) κ ε 𝔡 (min (min c₀ c₁) (min c₂ c₃)) := by
  have hpos : 0 < min (min c₀ c₁) (min c₂ c₃) := lt_min (lt_min hc₀ hc₁) (lt_min hc₂ hc₃)
  interval_cases k
  · exact STMainIndRAt_mono hpos ((min_le_left _ _).trans (min_le_left _ _)) H₀
  · exact STMainIndRAt_mono hpos ((min_le_left _ _).trans (min_le_right _ _)) H₁
  · exact STMainIndRAt_mono hpos ((min_le_right _ _).trans (min_le_left _ _)) H₂
  · exact STMainIndRAt_mono hpos ((min_le_right _ _).trans (min_le_right _ _)) H₃

/-- Every chain of stages, at the common constant `c`: `ST_mainIndR_seq` at the level of constants. -/
private theorem STMainIndRAt_chain {d : ℕ} {κ ε 𝔡 c : ℝ} (hc : 0 < c)
    (h : ∀ k, k ≤ 3 → STMainIndRAt d (STRegK k) κ ε 𝔡 c) :
    ∀ m i : ℕ, i + m ≤ 3 → STMainIndRAt d (STRegChain i m) κ ε 𝔡 c := by
  intro m
  induction m with
  | zero => intro i hi; exact h i (by omega)
  | succ m ih =>
    intro i hi
    have := STMainIndRAt_seq hc hc (h i (by omega)) (ih (i + 1) (by omega))
    rw [min_self] at this
    exact this

/-- **`lem:main_ind` from the four regime steps** (route (A), DECISIONS §68 (7); supervisor 1806 Q1, Q2 "Assembly" 2):
the stage pattern `(i, j)` of `[s_n, t_n]` (`STPattern`; the cuts `1-g²`, `1-g²/L²`, `1-g²/L^d`) takes ten values; on each
infinite class the pattern regime is the chain of stages `i, …, j` (`STRegChain`, the nesting of `STRegSeq` in the order
(iii), (i), (ii), (iv)), whose `STMainIndR` follows from the four by `ST_mainIndR_seq`; the six conclusions are glued back
along the `Nat.nth` enumerations of the classes (`ST_*_iff_comp_cover`, `nth_cover`).  The constant is the minimum of the
four regime constants (every chain is at that constant, `STMainIndRAt_chain`); one `𝔠_d` serves every class. -/
theorem ST_mainInd_of_regimes (d : ℕ) (h₀ : STMainIndR d STReg5III) (h₁ : STMainIndR d STReg5I)
    (h₂ : STMainIndR d STReg5II) (h₃ : STMainIndR d STReg5IV) : STMainInd d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₀, hc₀, hc₀', H₀⟩ := h₀ hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := h₁ hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := h₂ hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := h₃ hd κ ε 𝔡 hκ hε h𝔡
  have hpos : 0 < min (min c₀ c₁) (min c₂ c₃) := lt_min (lt_min hc₀ hc₁) (lt_min hc₂ hc₃)
  refine ⟨min (min c₀ c₁) (min c₂ c₃), hpos, ((min_le_left _ _).trans (min_le_left _ _)).trans hc₀', ?_⟩
  have hchain := STMainIndRAt_chain hpos (fun k hk => STMainIndRAt_stage hc₀ hc₁ hc₂ hc₃ H₀ H₁ H₂ H₃ hk)
  intro 𝔠 sz z hflow s t hs0 hsT hst htT hyp hcon
  obtain ⟨hLK, hDec, hDecS, hLoc, hExp⟩ := hyp
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow htT
  -- the finite cover by the classes of constant pattern
  let ι : Type := {P : Fin 4 × Fin 4 // {m : ℕ | STPattern sz s t m = P}.Infinite}
  let φ : ι → ℕ → ℕ := fun P => Nat.nth (fun m => STPattern sz s t m = P.1)
  have hφ : ∀ P, StrictMono (φ P) := fun P => Nat.nth_strictMono P.2
  have hcov : ∀ᶠ n in atTop, ∃ P, n ∈ Set.range (φ P) := nth_cover (STPattern sz s t)
  have key : ∀ P : ι,
      STLK (sz.comp (φ P)) (fun j => STflowE z (φ P j)) (fun j => t (φ P j)) ∧
      STLmax (sz.comp (φ P)) (fun j => STflowE z (φ P j)) (fun j => t (φ P j)) ∧
      STDecay (sz.comp (φ P)) (fun j => STflowE z (φ P j)) (fun j => t (φ P j)) ∧
      STExp2 (sz.comp (φ P)) (fun j => STflowE z (φ P j)) (fun j => t (φ P j)) ∧
      STLocalEntry (sz.comp (φ P)) (fun j => STflowE z (φ P j)) (fun j => t (φ P j)) ∧
      STDecayStrong (sz.comp (φ P)) (fun j => STflowE z (φ P j)) (fun j => t (φ P j)) := by
    intro P
    have hmem : ∀ j, STPattern sz s t (φ P j) = P.1 := fun j => Nat.nth_mem_of_infinite P.2 j
    obtain ⟨hij, hreg⟩ := STRegChain_of_class hd sz s t hst ht1 (φ P) P.1 hmem
    have hj3 : (P.1.1 : ℕ) + (P.1.2 - P.1.1) ≤ 3 := by omega
    have htend : Tendsto (φ P) atTop atTop := (hφ P).tendsto_atTop
    refine hchain (P.1.2 - P.1.1) P.1.1 hj3 𝔠 (sz.comp (φ P)) (fun j => z (φ P j))
      (STFlow_comp sz (φ P) κ ε 𝔠 𝔡 z htend hflow) (fun j => s (φ P j)) (fun j => t (φ P j))
      (fun j => hs0 _) (fun j => hsT _) (fun j => hst _) (fun j => htT _) hreg
      ⟨(STLK_iff_comp_cover d sz ι φ hφ hcov _ _).1 hLK P,
        (STDecay_iff_comp_cover d sz ι φ hφ hcov _ _).1 hDec P,
        (STDecayStrong_iff_comp_cover d sz ι φ hφ hcov _ _).1 hDecS P,
        (STLocalMax_iff_comp_cover d sz ι φ hφ hcov _ _).1 hLoc P,
        (STExp2_iff_comp_cover d sz ι φ hφ hcov _ _).1 hExp P⟩ ?_
    exact STConStInd_comp sz (φ P) _ s t htend hcon
  exact ⟨(STLK_iff_comp_cover d sz ι φ hφ hcov _ _).2 fun P => (key P).1,
    (STLmax_iff_comp_cover d sz ι φ hφ hcov _ _).2 fun P => (key P).2.1,
    (STDecay_iff_comp_cover d sz ι φ hφ hcov _ _).2 fun P => (key P).2.2.1,
    (STExp2_iff_comp_cover d sz ι φ hφ hcov _ _).2 fun P => (key P).2.2.2.1,
    (STLocalEntry_iff_comp_cover d sz ι φ hφ hcov _ _).2 fun P => (key P).2.2.2.2.1,
    (STDecayStrong_iff_comp_cover d sz ι φ hφ hcov _ _).2 fun P => (key P).2.2.2.2.2⟩

end RBM.Gauss.Sizes

/-! ## 7. `lem:main_ind` from the ten step pins that are still owed -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **What `lem:main_ind` still owes** (T2245): `STMainInd d` from `STStep2`, `STStep3I/II`, `STStep4I/II`,
`STStep5I/II`, `STStep6I/II/III`.  The other four step pins are proved: `STStep1` by `RBM.Green.stStep1_holds`
(`Green/GbEXP.lean:816`), `STStep5III` by `stStep5III_holds` (`Induction/PfStep5.lean:2473`), `STStep5IV` by
`stStep5IV_holds` (`Induction/Step5Kit.lean:549`), `STStep6IV` by `stStep6IV_holds` (`Induction/ExpIntEasy.lean:626`). -/
theorem ST_mainInd_of_pins (d : ℕ) (h2 : STStep2 d) (h3I : STStep3I d) (h3II : STStep3II d)
    (h4I : STStep4I d) (h4II : STStep4II d) (h5I : STStep5I d) (h5II : STStep5II d)
    (h6I : STStep6I d) (h6II : STStep6II d) (h6III : STStep6III d) : STMainInd d := by
  intro hd
  have h1 : STStep1 d := RBM.Green.stStep1_holds hd
  exact ST_mainInd_of_regimes d
    (ST_mainIndR_III_of_steps d h1 h2 h3I h4I (stStep5III_holds d) h6III)
    (ST_mainIndR_I_of_steps d h1 h2 h3I h4I h5I h6I)
    (ST_mainIndR_II_of_steps d h1 h2 h3II h4II h5II h6II)
    (ST_mainIndR_IV_of_steps d h1 h2 h3II h4II (stStep5IV_holds d) (stStep6IV_holds d)) hd

end RBM.Gauss.Sizes

/-! ## 8. Compiled nonempty instances at `d = 3`

Data (all merged): `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `sz0`, `z0`, `(s,t) = (0, 1/16)` (regime (iii)); `szB` (`L = 4`,
`W_n = n + 4`, `ilambda = 1`), `zB`, `lemT zB ≥ 31/32`, `(7/8, 15/16)` (regime (i)), `(15/16, 31/32)` (regime (ii)),
`(7/8, 31/32)` cut at `15/16` (the two-stage regime); `szG` (`ilambda = 5`), `zB`, `(5/8, 3/4)` (regime (iv)).  Every
deterministic hypothesis (flow, time ranges, regime, `(con_st_ind)` for every `𝔠_d > 0`) is discharged; what stays a
hypothesis of an instance is a premise that is the statement of another gate's pin (`STStep2`, `STStep3I`, ..., the
regime statements `STMainIndR`) or the stochastic premises `(a)`-`(d)` at `s`. -/

namespace RBM.Gauss.MainIndRegimesInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.Step5Inst RBM.Path Filter

/-- 1. The regime-(iii) data of `sz0_reg5III` are in case (i) of Steps 3-4. -/
theorem inst_caseI_III : STCaseI sz0 sInst tInst := st_caseI_of_reg5III 3 sz0 sInst tInst sz0_reg5III

/-- 2. The regime-(i) data of `szB_reg5I`. -/
theorem inst_caseI_I : STCaseI szB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  st_caseI_of_reg5I 3 szB _ _ szB_reg5I

/-- 3. The regime-(ii) data of `szB_reg5II`. -/
theorem inst_caseII_II : STCaseII szB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  st_caseII_of_reg5II 3 szB _ _ szB_reg5II

/-- 4. The regime-(iv) data of `szG_reg4` (`d = 3`). -/
theorem inst_caseII_IV : STCaseII szG (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  st_caseII_of_reg5IV 3 (by norm_num) szG _ _ szG_reg4

/-- 5. Two nonempty stages (i), (ii) at `szB` on `[0, 49/50]`, cut at `15/16` (`1/16 ≤ 1/16`, `1 ≤ 1`; `1/64 ≤ 1/50`,
`1/16 ≤ 1/16`). -/
theorem inst_regSeq_szB : STRegSeq STReg5I STReg5II szB (fun _ => 0) (fun _ => 49 / 50) :=
  ⟨fun _ => 15 / 16, fun _ => by norm_num, fun _ => by norm_num,
    fun n => ⟨by norm_num [szB], by norm_num [szB]⟩, fun n => ⟨by norm_num [szB], by norm_num [szB]⟩⟩

/-- 6. The bridge `(Gt_bound) ⇒ (Gt_bound+IND)` at the merged flow data of `sz0` (the premise is the pin
`STLocalEntry`, the conclusion of the induction). -/
theorem inst_localMax_sz0 :
    STLocalEntry sz0 (STflowE z0) sInst → STLocalMax sz0 (STflowE z0) sInst :=
  STLocalMax_of_STLocalEntry 3 sz0 (STflowE z0) sInst

/-- 7. The four regime steps give `lem:main_ind` at `d = 3`. -/
theorem inst_regimes3 :
    STMainIndR 3 STReg5III → STMainIndR 3 STReg5I → STMainIndR 3 STReg5II → STMainIndR 3 STReg5IV →
      STMainInd 3 :=
  ST_mainInd_of_regimes 3

/-- 8. `lem:main_ind` at `d = 3` from the ten owed step pins. -/
theorem inst_mainInd3 :
    STStep2 3 → STStep3I 3 → STStep3II 3 → STStep4I 3 → STStep4II 3 →
      STStep5I 3 → STStep5II 3 → STStep6I 3 → STStep6II 3 → STStep6III 3 → STMainInd 3 :=
  ST_mainInd_of_pins 3

/-! ### Extra instances: the classifier at `(szB, 0, 49/50)`, the targets applied at the data -/

/-- The pattern of `(szB, 0, 49/50)` is `((i), (ii))` (stage `1` of `s`, stage `2` of `t`) for every `n`:
`c₁ = 0 ≤ 0 < c₂ = 15/16`, `c₂ = 15/16 < 49/50 ≤ c₃ = 63/64`. -/
theorem inst_pattern_szB (n : ℕ) :
    STPattern szB (fun _ => 0) (fun _ => 49 / 50) n = ((1 : Fin 4), (2 : Fin 4)) := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · change STStageS szB (fun _ => (0 : ℝ)) n = 1
    simp only [STStageS, STCutK, szB]
    norm_num
  · change STStageT szB (fun _ => (49 / 50 : ℝ)) n = 2
    simp only [STStageT, STCutK, szB]
    norm_num

/-- The regime of the pattern `((i), (ii))` at `szB` on `[0, 49/50]` (`STRegChain_of_class` at `φ = id`): the chain of
the two stages (i), (ii), cut at the intermediate time `c₂ = 15/16`. -/
theorem inst_chain_szB :
    STRegChain 1 1 (szB.comp id) (fun j => (fun _ => (0 : ℝ)) (id j)) (fun j => (fun _ => (49 / 50 : ℝ)) (id j)) :=
  (STRegChain_of_class (d := 3) (by norm_num) szB (fun _ => 0) (fun _ => 49 / 50)
    (fun _ => by norm_num) (fun _ => by norm_num) id ((1 : Fin 4), (2 : Fin 4))
    (fun j => inst_pattern_szB j)).2

/-- The seven cover transfers at `sz0` along the two parity classes. -/
theorem parity_strictMono (r : Fin 2) : StrictMono (Nat.nth (fun m => m % 2 = (r : ℕ))) :=
  Nat.nth_strictMono (SizesCompInst.parity_infinite r)

theorem parity_cover :
    ∀ᶠ n in atTop, ∃ r : Fin 2, n ∈ Set.range (Nat.nth fun m => m % 2 = (r : ℕ)) :=
  Eventually.of_forall fun n =>
    ⟨⟨n % 2, Nat.mod_lt _ (by norm_num)⟩, by
      rw [Nat.range_nth_of_infinite (SizesCompInst.parity_infinite _)]; rfl⟩

theorem inst_STLK_iff :
    STLK sz0 (STflowE z0) sInst ↔ ∀ r : Fin 2, STLK (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
      (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
      (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STLK_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ))) parity_strictMono
    parity_cover _ _

theorem inst_STLmax_iff :
    STLmax sz0 (STflowE z0) sInst ↔ ∀ r : Fin 2, STLmax (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
      (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
      (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STLmax_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ))) parity_strictMono
    parity_cover _ _

theorem inst_STDecay_iff :
    STDecay sz0 (STflowE z0) sInst ↔ ∀ r : Fin 2, STDecay (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
      (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
      (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STDecay_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ))) parity_strictMono
    parity_cover _ _

theorem inst_STDecayStrong_iff :
    STDecayStrong sz0 (STflowE z0) sInst ↔
      ∀ r : Fin 2, STDecayStrong (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
        (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
        (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STDecayStrong_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ)))
    parity_strictMono parity_cover _ _

theorem inst_STLocalMax_iff :
    STLocalMax sz0 (STflowE z0) sInst ↔
      ∀ r : Fin 2, STLocalMax (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
        (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
        (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STLocalMax_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ)))
    parity_strictMono parity_cover _ _

theorem inst_STLocalEntry_iff :
    STLocalEntry sz0 (STflowE z0) sInst ↔
      ∀ r : Fin 2, STLocalEntry (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
        (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
        (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STLocalEntry_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ)))
    parity_strictMono parity_cover _ _

theorem inst_STExp2_iff :
    STExp2 sz0 (STflowE z0) sInst ↔ ∀ r : Fin 2, STExp2 (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
      (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
      (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j)) :=
  STExp2_iff_comp_cover 3 sz0 (Fin 2) (fun r => Nat.nth (fun m => m % 2 = (r : ℕ))) parity_strictMono
    parity_cover _ _

/-- Targets 1: the regime-free statement gives regime (i) (the weaker regime). -/
theorem inst_mono_I : STMainInd 3 → STMainIndR 3 STReg5I := fun h =>
  STMainIndR_mono 3 STAny STReg5I (fun _ _ _ _ => trivial) ((ST_mainInd_iff_any 3).1 h)

/-- The result of applying a regime statement `STMainIndR 3 R` at the data `(sz, z, s, t)`: the constant `𝔠_d`, then the
stochastic premises `(a)`-`(d)` at `s`, then the conclusions at `t`. -/
def InstMainIndRConcl (_R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (sz : Sizes 3) (z : ℕ → ℂ)
    (s t : ℕ → ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ((STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
        STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
      STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
        STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧ STDecayStrong sz (STflowE z) t)

/-- The common shape of the instances: the constant `𝔠_d`, then the deterministic data with the regime `R` and
`(con_st_ind)`. -/
theorem inst_mainIndR (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STMainIndR 3 R)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ lemT (z n)) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) :
    InstMainIndRConcl R sz z s t := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨𝔠d, h0, h1, fun hyp => H (1 / 6) sz z hflow s t hs0 hsT hst ht hR hyp (hcon 𝔠d h0)⟩

/-- Target 4 applied: two stages (i), (ii) of `szB` cut at `15/16` on `[7/8, 31/32]`, every deterministic hypothesis
discharged. -/
theorem inst_mainIndR_seq (hI : STMainIndR 3 STReg5I) (hII : STMainIndR 3 STReg5II) :
    InstMainIndRConcl (STRegSeq STReg5I STReg5II) szB zB (fun _ => 7 / 8) (fun _ => 31 / 32) :=
  inst_mainIndR _ (ST_mainIndR_seq 3 STReg5I STReg5II hI hII) szB zB flow_zB _ _ (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun _ => by norm_num) (szB_flow_ht (by norm_num))
    ⟨fun _ => 15 / 16, fun _ => by norm_num, fun _ => by norm_num, szB_reg5I, szB_reg5II⟩
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- Target 3 applied, regime (iii) at `(sz0, z0, 0, 1/16)`. -/
theorem inst_steps_III (h2 : STStep2 3) (h3 : STStep3I 3) (h4 : STStep4I 3) (h5 : STStep5III 3)
    (h6 : STStep6III 3) : InstMainIndRConcl STReg5III sz0 z0 sInst tInst :=
  inst_mainIndR _ (ST_mainIndR_III_of_steps 3 (RBM.Green.stStep1_holds (by norm_num)) h2 h3 h4 h5 h6)
    sz0 z0 flow_z0 sInst tInst sz0_hs0 (fun n => (sz0_hst n).le.trans (sz0_ht n)) sz0_hst sz0_ht
    sz0_reg5III sz0_con

/-- Target 3 applied, regime (i) at `(szB, zB, 7/8, 15/16)`. -/
theorem inst_steps_I (h2 : STStep2 3) (h3 : STStep3I 3) (h4 : STStep4I 3) (h5 : STStep5I 3)
    (h6 : STStep6I 3) : InstMainIndRConcl STReg5I szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  inst_mainIndR _ (ST_mainIndR_I_of_steps 3 (RBM.Green.stStep1_holds (by norm_num)) h2 h3 h4 h5 h6)
    szB zB flow_zB _ _ (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5I
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- Target 3 applied, regime (ii) at `(szB, zB, 15/16, 31/32)`. -/
theorem inst_steps_II (h2 : STStep2 3) (h3 : STStep3II 3) (h4 : STStep4II 3) (h5 : STStep5II 3)
    (h6 : STStep6II 3) : InstMainIndRConcl STReg5II szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_mainIndR _ (ST_mainIndR_II_of_steps 3 (RBM.Green.stStep1_holds (by norm_num)) h2 h3 h4 h5 h6)
    szB zB flow_zB _ _ (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_reg5II
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- Target 3 applied, regime (iv) at `(szG, zB, 5/8, 3/4)`. -/
theorem inst_steps_IV (h2 : STStep2 3) (h3 : STStep3II 3) (h4 : STStep4II 3) :
    InstMainIndRConcl STReg5IV szG zB (fun _ => 5 / 8) (fun _ => 3 / 4) :=
  inst_mainIndR _ (ST_mainIndR_IV_of_steps 3 (RBM.Green.stStep1_holds (by norm_num)) h2 h3 h4
      (stStep5IV_holds 3) (stStep6IV_holds 3))
    szG zB flow_zG _ _ (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szG_reg4
    (fun _ h𝔠 => conStInd_const szG szG_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- Target 7 applied: `lem:main_ind` at `d = 3` on `(szB, zB, 0, 31/32)` (the pattern `((i), (ii))` over three
cuts), from the ten owed step pins; only the stochastic premises `(a)`-`(d)` at `s` stay. -/
theorem inst_mainInd3_data (h2 : STStep2 3) (h3I : STStep3I 3) (h3II : STStep3II 3) (h4I : STStep4I 3)
    (h4II : STStep4II 3) (h5I : STStep5I 3) (h5II : STStep5II 3) (h6I : STStep6I 3) (h6II : STStep6II 3)
    (h6III : STStep6III 3) :
    InstMainIndRConcl STAny szB zB (fun _ => 0) (fun _ => 31 / 32) :=
  inst_mainIndR _ ((ST_mainInd_iff_any 3).1 (ST_mainInd_of_pins 3 h2 h3I h3II h4I h4II h5I h5II h6I h6II h6III))
    szB zB flow_zB _ _ (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) trivial
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

end RBM.Gauss.MainIndRegimesInst
