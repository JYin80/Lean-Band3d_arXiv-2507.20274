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
# The main-induction regime assembly

Theorem 2.24 (`lem:main_ind`) assembled from one induction step per regime.  Paper: the proof of
Theorem 2.24 in the subsection "Proof of the main results" (Steps 1-6); the regimes of Steps 5 and 6 are
those of Section 5 (`Sec:Step5`) and of the proof of Lemma 6.2 (`lem:LWterm_EXP`).

* Section 1: `STMainIndR d R`, the shape of `STMainInd` under a regime `R` of the time sequences.
* Section 2: the four regimes of Steps 5 and 6 lie in the cases of Steps 3 and 4 (`st_caseI_of_reg5III`, ...).
* Section 3: one main-induction step per regime, from the step statements (`ST_mainIndR_of_steps`;
  the instances `ST_mainIndR_II_of_steps`, `ST_mainIndR_IV_of_steps`).
* Section 4: two stages cut at an intermediate time (`STLocalMax_of_STLocalEntry`).
* Section 5: the seven predicates along a finite `StrictMono` cover (`STLK_iff_comp_cover`, ...).
* Section 6: the classifier of the stage pattern of `[s_n, t_n]` (`STPattern`), `STRegChain_holds`
  and `ST_mainInd_of_regimes`.

Why the regimes are assembled by subsequences: the proof of Theorem 2.24 applies Steps 1-6 on the
whole `[s,t]`, and Steps 3-6 are proved per regime (Section 4 `Sec:Steps34`, Section 5 `Sec:Step5`,
the proof of Lemma 6.2 `lem:LWterm_EXP`); "adding intermediate times" (Section 5) cannot be done inside
Steps 2-5 (their losses `((1-s)/(1-s'))^{C_d}` and `(L^d/4)^{k-1}` are anchored at `s`), so the formal
proof reruns the whole induction step from each cut `1-g²`, `1-g²/L²`, `1-g²/L^d`, composes the
single-time conclusions, and glues the ten stage patterns along finitely many subsequences
(`Sizes.comp`).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

universe w

/-! ## 1. The shape `STMainIndR` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`lem:main_ind` under a regime `R`**: the body of `STMainInd` (`Induction/Defs.lean`) with the
hypothesis `R sz s t` after `t ≤ lemT z`.  One constant `𝔠_d` serves every flow. -/
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

/-- `STMainIndRAt` at a smaller constant (a smaller exponent is the stronger hypothesis
`(con_st_ind)`, `st5_conStInd_mono`). -/
private theorem STMainIndRAt_mono {d : ℕ} {R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    {κ ε 𝔡 c c' : ℝ} (hc' : 0 < c') (hcc : c' ≤ c) (h : STMainIndRAt d R κ ε 𝔡 c) :
    STMainIndRAt d R κ ε 𝔡 c' := by
  intro 𝔠 sz z hflow s t hs0 hsT hst htT hR hyp hcon
  exact h 𝔠 sz z hflow s t hs0 hsT hst htT hR hyp
    (st5_conStInd_mono sz hcon (st5_t_lt_one sz hflow htT) hc' hcc)

/-! ## 2. The Step 5/6 regimes inside the Step 3/4 cases -/

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

/-- **One main-induction step** from the six step statements (with the regime `R` threaded through): Step 2 gives
`(C_d, 𝔠_d²)`, Steps 3-6 give their constants, Step 1 holds for every `𝔠_d ∈ (0, 10^{-2}]`; the constant is the
minimum (`(con_st_ind)` for the minimum implies it for each larger exponent, `st5_conStInd_mono`).  The Step 3/4
regime `R34` contains `R` (`3 ≤ d → R ⊆ R34`).  `STKbound`, `STKward` are the theorems `stKbound_of_flow`,
`stKward_of_flow`. -/
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

/-- **`(Gt_bound)` gives `(Gt_bound+IND)`** (the input of the next stage from the conclusion of the previous one):
`|(G_τ - M)_{xy}|² ≺ W^{-d}B_{τ,K} ≤ W^{-d}B_{τ,0} = Bctl` (`localAvg1_STWB_le`,
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

end RBM.Gauss.Sizes

/-! ## 5. The seven predicates along a finite cover

`X sz E τ ↔ ∀ k, X (sz.comp (φ k)) (E ∘ φ k) (τ ∘ φ k)` for a finite family of strictly increasing
`φ k` whose ranges cover all large `n` (`Prec_iff_comp_cover`; the commutations of the per-`n` objects
with `reindex` are `rfl`, see `Induction/SizesComp.lean`; for `STExp2` the deterministic left side
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
Steps 5, 6 are the four intervals between them (Section 5 `Sec:Step5`, the proof of Lemma 6.2 `lem:LWterm_EXP`).
`c₁ ≤ c₂ ≤ c₃ ≤ 1`, strictly if `g ≠ 0` (`L ≥ 3`, `d ≥ 3`).  The stage of `s_n` is `0` if `s < c₁`, `1` if
`c₁ ≤ s < c₂`, `2` if `c₂ ≤ s < c₃`, `3` if `c₃ ≤ s`; the stage of `t_n` is `0` if `t ≤ c₁`, `1` if
`c₁ < t ≤ c₂`, `2` if `c₂ < t ≤ c₃`, `3` if `c₃ < t` (the `<`/`≤` choice excludes point-stages).  The pattern
`(i, j)` has `i ≤ j` (ten values) and `[s,t]` is cut at `c_{i+1}, …, c_j`, each stage on `[c_k, c_{k+1}]` with
equality at the cuts. -/

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

/-- Every chain of stages, at the common constant `c`: the two-stage composition at the level of constants. -/
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

/-- **`lem:main_ind` from the four regime steps**: the stage pattern `(i, j)` of `[s_n, t_n]` (`STPattern`; the
cuts `1-g²`, `1-g²/L²`, `1-g²/L^d`) takes ten values; on each infinite class the pattern regime is the chain of
stages `i, …, j` (`STRegChain`, the nesting of `STRegSeq` in the order (iii), (i), (ii), (iv)), whose `STMainIndR`
follows from the four by the two-stage composition; the six conclusions are glued back along the `Nat.nth`
enumerations of the classes (`ST_*_iff_comp_cover`, `nth_cover`).  The constant is the minimum of the four regime
constants (every chain is at that constant, `STMainIndRAt_chain`); one `𝔠_d` serves every class. -/
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
