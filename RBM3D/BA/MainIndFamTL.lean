/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MainIndOutBA
import RBM3D.BA.Step34BA
import RBM3D.BA.Step1Prime
import RBM3D.BA.TwistLoop
import RBM3D.BA.TwistStep2
import RBM3D.BA.DecayLoopBA
import RBM3D.BA.Step5CasesBA
import RBM3D.BA.Step5IIITargets
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step6Gen
import RBM3D.Chain.Step6KitGen
import RBM3D.Graph.BATermHoldsB
import RBM3D.Induction.MainIndRegimes
import RBM3D.Induction.MainIndChain

/-!
# The block Anderson main induction per regime, in family form with TL2

Theorem 8.2 (`lem:main_ind_BA`), the block Anderson form of Lemma 2.24 (`lem:main_ind`), per regime `R` in family form (`BAMainIndFamTL d R`, `BA/MainIndOutBA`), proved from
Steps 1-6 at the BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.  The proof follows the band step
`ST_mainIndR_of_steps` (`Induction/MainIndRegimes`) at the BA tuple with the TL2 conjunct.

* `baKboundMember_holds`: `STKboundgL` at every member of `Fam(s)` (the member as a flow after a finite modification).
* `baStep1Fam_call`: the family Step-1 call (`baStep1_holds'` at its exact type).
* private `MainIndFamTL_S1`, `MainIndFamTL_famOfS1`, `MainIndFamTL_s1OfSteps`: the single-flow step with Steps 1-2 as premises, the wrapper to the family step, the body of
  the band step.
* `baMainIndFamTL_of_steps`: the generic step in `R`, `R34`, `Rtl`, with Steps 3-6 as hypotheses and Step 6 in slot form (`STIngR6gL` at an arbitrary conclusion slot).
* `baMainIndFamTL_III_of`, `baMainIndFamTL_I_of`, `baMainIndFamTL_II_of`, `baMainIndFamTL_IV_of`: the four regimes, Steps 3-4 and the TL2 step by name from the
  theorems `baStep3RegIII_holds`, `baStep4RegIII_holds`, `baStep3RegI_holds`, `baStep4RegI_holds`, `baStep3II_holds`, `baStep4II_holds` and from `BA/TwistLoop`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The `K` bound at a member, the family Step-1 call -/

/-- `baKboundMember_holds`: `STKboundgL` at every member `z'` of `Fam(s)`: the member is a `BAFlow` at `(κ', ε')`
after a finite modification (`BAFlowMember_holds`, `BA/Step1Fam`), `baKbound_holds` there, and `STKboundgL_congr` along `baFMz_eqAt`. -/
theorem baKboundMember_holds (d : ℕ) :
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
          STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s hs0 z' hz'
  obtain ⟨κ', ε', hκ', -, hε', -, H⟩ := BAFlowMember_holds d κ ε 𝔡 hκ hε h𝔡
  obtain ⟨n₀, hfl⟩ := H 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' (BAFamZ_mono (s := fun _ => 0) hs0 hz')
  refine (STKboundgL_congr _ (C := baFMz sz (fun n => if n < n₀ then z n else z' n)) (C' := baFMz sz z') ?_).mp
    (baKbound_holds d hd κ' ε' 𝔡 hκ' hε' h𝔡 𝔠 sz _ hfl)
  exact eventually_atTop.mpr ⟨n₀, fun n hn => baFMz_eqAt sz (by simp [not_lt.mpr hn])⟩

/-- `baStep1Fam_call`: the Step-1 pair at every member of `Fam(t)` from the six conclusions at every member of `Fam(s)`:
`baStep1_holds'` at its exact type, the `K` bound from `baKboundMember_holds`, `STLKgL` and `STLocalMaxgL` and `STExp2gL` from the family premise. -/
theorem baStep1Fam_call (d : ℕ) :
    3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
          (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' →
            let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0)
            STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
          sz.STConStInd 𝔠d s t →
          ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
            STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧ STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d0 h𝔠d1 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT H hcon
  exact baStep1_holds' d (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d0 h𝔠d1 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT
    (fun z' hz' => ⟨baKboundMember_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s hs0 z' hz',
      (H z' hz').1, (H z' hz').2.2.2.1⟩) hcon

/-! ## 2. The single-flow step, the wrapper to the family step, the body of the band step -/

/-- Private `MainIndFamTL_S1`: the single-flow step with Steps 1-2 (`STStep1LoopgL`, `STStep1WeakgL`) as premises, at a `BAFlow`; the
constant `𝔠d` is fixed by `(κ, ε, 𝔡)` before `(𝔠, sz, z)`. -/
private def MainIndFamTL_S1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t →
        let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
        (STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
        sz.STConStInd 𝔠d s t → STStep1LoopgL C μ s t → STStep1WeakgL C μ s t →
          STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧
            STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

/-- Private `MainIndFamTL_famOfS1`: the family step from the single-flow step.  A member `z'` of `Fam(t) ⊆ Fam(s)` is a `BAFlow` `z''` at `(κ', ε')` with the
same carrier eventually (`baFamMember_flow`); the single-flow step at `z''` is fed the six conclusions and the Step-1 pair (`baStep1Fam_call`) transported along the ten congruence lemmas `STLKgL_congr`, …, `STStep1WeakgL_congr` of `BA/Step1Fam` and
`BATwistLoopLaw_congr`, and the seven conclusions are carried back. -/
private theorem MainIndFamTL_famOfS1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    MainIndFamTL_S1 d R → BAMainIndFamTL d R := by
  intro hS1 hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨κ', ε', hκ', -, hε', -, Hm⟩ := baFamMember_flow d κ ε 𝔡 hκ hε h𝔡
  obtain ⟨𝔠d, h0, h1, H⟩ := hS1 hd κ' ε' 𝔡 hκ' hε' h𝔡
  refine ⟨𝔠d, h0, h1, fun 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT hR hfam hcon z' hzt => ?_⟩
  obtain ⟨-, z'', hfl, hT, hev⟩ := Hm 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t (fun n => (hs0 n).trans (hst n).le) htT z' hzt
  have hzs : BAFamZ sz z c₁ s z' := BAFamZ_mono (fun n => (hst n).le) hzt
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hfam z' hzs
  have hpair := baStep1Fam_call d hd κ ε 𝔡 hκ hε h𝔡 𝔠d h0 h1 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT hfam hcon z' hzt
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := H 𝔠 sz z'' hfl s t hs0 (fun n => (hst n).le.trans (hT n)) hst hT hR
    ⟨(STLKgL_congr _ hev s).mpr a1, (STDecaygL_congr _ hev s).mpr a2, (STDecayStronggL_congr _ hev s).mpr a3,
      (STLocalMaxgL_congr _ hev s).mpr a4, (STExp2gL_congr _ hev s).mpr a5, (BATwistLoopLaw_congr d sz _ _ _ s hev).mpr a6⟩ hcon
    ((STStep1LoopgL_congr _ hev s t).mpr hpair.1) ((STStep1WeakgL_congr _ hev s t).mpr hpair.2)
  exact ⟨(STLKgL_congr _ hev t).mp b1, (STLmaxgL_congr _ hev t).mp b2, (STDecaygL_congr _ hev t).mp b3,
    (STExp2gL_congr _ hev t).mp b4, (STLocalEntrygL_congr _ hev t).mp b5, (STDecayStronggL_congr _ hev t).mp b6,
    (BATwistLoopLaw_congr d sz _ _ _ t hev).mp b7⟩

/-- Private `MainIndFamTL_s1OfSteps`: the body of `ST_mainIndR_of_steps` (`Induction/MainIndRegimes`) at the BA tuple, with the TL2 step.  Step 2 gives `(Cd, c₂)` (`baStep2Decay_holds`
at `baLWterm_holds`, `baLWtermExp_holds`), Steps 3-5 and the TL2 step their constants at `Cd`, Step 6 its constant; `𝔠d` is the minimum of the six; the `K` bound and the Ward bound are `baKbound_holds`, `baKward_holds`; TL1 (`TwistStep2_tl1`) and TL2
(the TL2 step) at every `u ∈ [s, t]` are fed to the bridge; the endpoints `u = t` are the generic ones. -/
private theorem MainIndFamTL_s1OfSteps (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hR : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t)
    (hRtl : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → Rtl sz s t)
    (hTL : BATwistLoopStep d Rtl)
    (h3 : STStep3RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z))
    (h4 : STStep4RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z))
    (h5 : STIngR5gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t))
    (Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (h6 : STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6)
    (hb : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
      (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
        BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
      Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) :
    MainIndFamTL_S1 d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Cd, hCd, c₂, hc₂, hc₂', H₂⟩ := baStep2Decay_holds d (baLWterm_holds d) (baLWtermExp_holds d) hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := h3 hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := h4 hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₅, hc₅, hc₅', H₅⟩ := h5 hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₆, hc₆, hc₆', H₆⟩ := h6 hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c₇, hc₇, hc₇', H₇⟩ := hTL hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₂ (min c₃ (min c₄ (min c₅ (min c₆ c₇)))) :=
    lt_min hc₂ (lt_min hc₃ (lt_min hc₄ (lt_min hc₅ (lt_min hc₆ hc₇))))
  refine ⟨min c₂ (min c₃ (min c₄ (min c₅ (min c₆ c₇)))), hcpos, (min_le_left _ _).trans hc₂', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hsT hst htT hRst C μ hyp hcon hS1L hS1W
  obtain ⟨hLK, hDec, hDecS, hLoc, hExp, hTL2s⟩ := hyp
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have m : ∀ c', min c₂ (min c₃ (min c₄ (min c₅ (min c₆ c₇)))) ≤ c' → sz.STConStInd c' s t :=
    fun c' hcc => st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hKb : STKboundgL C μ := baKbound_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hKw : STKwardgL C μ := baKward_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hS2 := H₂ 𝔠 sz z hflow s t hs0 hsT hst htT hLK hDec (m c₂ (min_le_left _ _)) hS1L hS1W
  have hS3 : STLmaxUgL C μ s t :=
    H₃ 𝔠 sz z hflow s t hs0 hst htT (hR hd sz s t hRst) hKb hKw hLK
      (m c₃ ((min_le_right _ _).trans (min_le_left _ _))) hS1L hS2.1
  have hS4 : STLKUgL C μ s t :=
    H₄ 𝔠 sz z hflow s t hs0 hst htT (hR hd sz s t hRst) hKb hKw hLK
      (m c₄ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hS1L hS2.1 hS3
  have hS5 : STStep5ConclgL C μ s t :=
    H₅ 𝔠 sz z hflow s t hs0 hst htT hRst hKb hKw hLK hDec hDecS
      (m c₅ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))) hS1L hS2.1 hS3 hS4
  have hS6 : Concl6 sz z s t :=
    H₆ 𝔠 sz z hflow s t hs0 hst htT hRst hLK hDec hExp
      (m c₆ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
      ⟨hS2.1.1, hS2.1.2.1⟩ hS3 hS4 hS5.1
  have hTL2 : ∀ τ : ℕ → ℝ, (∀ n, s n ≤ τ n) → (∀ n, τ n ≤ t n) → BATwistLoopLaw C μ τ :=
    H₇ 𝔠 sz z hflow s t hs0 hst htT (hRtl hd sz s t hRst)
      (m c₇ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
      ⟨hS2.1, hS3, hS4, hS2.2⟩ hTL2s
  have hS6' : STStep6ConclgL C μ s t :=
    hb sz z s t (fun u h1 h2 => ⟨TwistStep2_tl1 hd hκ hε h𝔡 hflow hs0 htT hS2.1.2.1 hS3 h1 h2, hTL2 u h1 h2⟩) hS6
  obtain ⟨hD5, hDS5⟩ := ST_step5_assemblygL C μ s t (fun n => (hst n).le) hS5
  exact ⟨STLKgL_of_STLKUgL C μ (fun n => (hst n).le) hS4, STLmaxgL_of_STLmaxUgL C μ (fun n => (hst n).le) hS3, hD5,
    STExp2gL_of_STExp2UgL C μ (fun n => (hst n).le) hS6', STLocalEntrygL_of_STLocalEntryUgL C (fun n => (hst n).le) hS2.1.1, hDS5,
    hTL2 t (fun n => (hst n).le) (fun _ => le_rfl)⟩

/-! ## 3. The generic step and the four regimes -/

/-- `baMainIndFamTL_of_steps` (generic in `R`, `R34 ⊇ R` (Steps 3-4), `Rtl ⊇ R` (the TL2 step); Steps 3-6 as hypotheses, Step 6 in slot form): `lem:main_ind_BA` in family form with TL2.
Step 5 is `STIngR5gL … STStep5ConclgL` (the unfolding of `STStep5RgL`, `Chain/Step5Gen`).  Step 6 is `STIngR6gL` at an arbitrary conclusion slot `Concl6`; the bridge `hb` turns TL1 and TL2
on `[s, t]` and the slot into `STStep6ConclgL`.  The proof is `MainIndFamTL_famOfS1` after `MainIndFamTL_s1OfSteps`. -/
theorem baMainIndFamTL_of_steps (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t) →
    (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → Rtl sz s t) →
    BATwistLoopStep d Rtl →
    STStep3RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) →
    STStep4RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) →
    STIngR5gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
    ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop,
      STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z => BAflowT0 sz z) Concl6 →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
        Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
      BAMainIndFamTL d R :=
  fun hR hRtl hTL h3 h4 h5 Concl6 h6 hb =>
    MainIndFamTL_famOfS1 d R (MainIndFamTL_s1OfSteps d R R34 Rtl hR hRtl hTL h3 h4 h5 Concl6 h6 hb)

/-- `baMainIndFamTL_III_of`: regime (iii) (`1 - s ≥ 1 - t ≥ lam²`); `(R, R34, Rtl) = (STReg5III, STReg5III, STCaseI)`; Steps 3-4 are `baStep3RegIII_holds`, `baStep4RegIII_holds`,
the TL2 step is `baTwistLoopStep_caseI` along `st_caseI_of_reg5III`; Step 5 (iii) is the hypothesis `STStep5IIIgL d …` (supplied for every `d ≥ 3` by `baStep5III_holds_any`);
Step 6 and the bridge are the slot hypotheses. -/
theorem baMainIndFamTL_III_of (d : ℕ) :
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) →
    ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop,
      STIngR6gL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z => BAflowT0 sz z) Concl6 →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
        Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
      BAMainIndFamTL d STReg5III :=
  fun h5 => baMainIndFamTL_of_steps d STReg5III STReg5III STCaseI (fun _ _ _ _ h => h) (fun _ => st_caseI_of_reg5III d)
    (baTwistLoopStep_caseI d) (baStep3RegIII_holds d) (baStep4RegIII_holds d) h5

/-- `baMainIndFamTL_I_of`: regime (i) (`lam²/L² ≤ 1 - t ≤ 1 - s ≤ lam²`); `(STReg5I, STReg5I, STCaseI)`; Steps 3-4 `baStep3RegI_holds`, `baStep4RegI_holds`; Step 5 `baStep5I_holds`. -/
theorem baMainIndFamTL_I_of (d : ℕ) :
    ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop,
      STIngR6gL d STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z => BAflowT0 sz z) Concl6 →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
        Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
      BAMainIndFamTL d STReg5I :=
  baMainIndFamTL_of_steps d STReg5I STReg5I STCaseI (fun _ _ _ _ h => h) (fun _ => st_caseI_of_reg5I d)
    (baTwistLoopStep_caseI d) (baStep3RegI_holds d) (baStep4RegI_holds d) (fun hd => baStep5I_holds d hd hd)

/-- `baMainIndFamTL_II_of`: regime (ii) (`lam²/L^d ≤ 1 - t ≤ 1 - s ≤ lam²/L²`); `(STReg5II, STCaseII, STCaseII)`; Steps 3-4 `baStep3II_holds`, `baStep4II_holds`; TL2 step
`baTwistLoopStep_caseII`; Step 5 `baStep5II_holds`. -/
theorem baMainIndFamTL_II_of (d : ℕ) :
    ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop,
      STIngR6gL d STReg5II (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z => BAflowT0 sz z) Concl6 →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
        Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
      BAMainIndFamTL d STReg5II :=
  baMainIndFamTL_of_steps d STReg5II STCaseII STCaseII (fun _ => st_caseII_of_reg5II d) (fun _ => st_caseII_of_reg5II d)
    (baTwistLoopStep_caseII d) (baStep3II_holds d) (baStep4II_holds d) (fun hd => baStep5II_holds d hd hd)

/-- `baMainIndFamTL_IV_of`: regime (iv) (`1 - t ≤ 1 - s ≤ lam²/L^d`); `(STReg5IV, STCaseII, STCaseII)` along `st_caseII_of_reg5IV` (`2 ≤ d`); Step 5 `baStep5IV_holds`. -/
theorem baMainIndFamTL_IV_of (d : ℕ) :
    ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop,
      STIngR6gL d STReg5IV (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        (fun sz z => BAflowT0 sz z) Concl6 →
      (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
        Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
      BAMainIndFamTL d STReg5IV :=
  baMainIndFamTL_of_steps d STReg5IV STCaseII STCaseII (fun hd => st_caseII_of_reg5IV d (by omega)) (fun hd => st_caseII_of_reg5IV d (by omega))
    (baTwistLoopStep_caseII d) (baStep3II_holds d) (baStep4II_holds d) (baStep5IV_holds d)

end RBM.BA

end
