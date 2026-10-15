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
# V row V2a, row a (T2511): the BA main induction per regime in family form with TL2

`lem:main_ind_BA` per regime `R` in family form (`BAMainIndFamTL d R`, `BA/MainIndOutBA.lean:60`, merged, read by name), proved from the
merged Steps 1-6 of the BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`.  New BA leaves only; the proof model is the band step
`ST_mainIndR_of_steps` (`Induction/MainIndRegimes.lean:165`) at the BA tuple with the TL2 conjunct (T2503 probe `RBM3D/Probe/T2503Pins.lean:103-139`, `t/T2503`).

* `baKboundMember_holds` (K2): `STKboundgL` at every member of `Fam(s)` (the member as a flow after a finite modification).
* `baStep1Fam_call`: the family Step-1 call (`baStep1_holds'` at its exact type).
* private `MainIndFamTL_S1`, `MainIndFamTL_famOfS1`, `MainIndFamTL_s1OfSteps`: the single-flow step with Steps 1-2 as premises, the wrapper to the family step, the body of
  the band step.
* `baMainIndFamTL_of_steps`: the generic step in `R`, `R34`, `Rtl`, with Steps 3-6 as hypotheses and Step 6 in slot form (`STIngR6gL` at an arbitrary conclusion slot).
* `baMainIndFamTL_III_of`, `_I_of`, `_II_of`, `_IV_of`: the four regimes, Steps 3-4 and the TL2 step by name from T2509 and `BA/TwistLoop`.
* Compiled `d = 3` instances: K2, the Step-1 call, the step (iii) at `sz0`, and (i), (ii), (iv) at private data.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Targets 1, 2: K2 at a member, the family Step-1 call -/

/-- **Target 1, `baKboundMember_holds`** (K2; T2503 probe `T2503_k2Member`): `STKboundgL` at every member `z'` of `Fam(s)`: the member is a `BAFlow` at `(κ', ε')`
after a finite modification (`BAFlowMember_holds`, `Step1Fam:624`), `baKbound_holds` there, and `STKboundgL_congr` along `baFMz_eqAt`. -/
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

/-- **Target 2, `baStep1Fam_call`** (T2503 probe `T2503_famStep1Call`): the Step-1 pair at every member of `Fam(t)` from the six conclusions at every member of `Fam(s)`:
`baStep1_holds'` at its exact type, K2 from target 1, `STLKgL` and `STLocalMaxgL` and `STExp2gL` from the family premise. -/
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

/-! ## 2. Targets 3-5: the single-flow step, the wrapper to the family step, the body of the band step -/

/-- **Target 3, private `MainIndFamTL_S1`** (T2503 D1 (b) `BAMainIndS1TL`): the single-flow step with Steps 1-2 (`STStep1LoopgL`, `STStep1WeakgL`) as premises, at a `BAFlow`; the
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

/-- **Target 4, private `MainIndFamTL_famOfS1`** (T2503 probe `T2503_famOfS1`, `:124-139`): the family step from the single-flow step.  A member `z'` of `Fam(t) ⊆ Fam(s)` is a `BAFlow` `z''` at `(κ', ε')` with the
same carrier eventually (`baFamMember_flow`); the single-flow step at `z''` is fed the six conclusions and the Step-1 pair (`baStep1Fam_call`) transported along the ten `_congr` of `Step1Fam:205-260` and
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

/-- **Target 5, private `MainIndFamTL_s1OfSteps`**: the body of `ST_mainIndR_of_steps` (`Induction/MainIndRegimes.lean:165-214`) at the BA tuple, with the TL2 step.  Step 2 gives `(Cd, c₂)` (`baStep2Decay_holds`
at `baLWterm_holds`, `baLWtermExp_holds`), Steps 3-5 and the TL2 step their constants at `Cd`, Step 6 its constant; `𝔠d` is the minimum of the six; K12 is `baKbound_holds`, `baKward_holds`; TL1 (`TwistStep2_tl1`) and TL2
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

/-! ## 3. Targets 6-9: the generic step and the four regimes -/

/-- **Target 6, `baMainIndFamTL_of_steps`** (generic in `R`, `R34 ⊇ R` (Steps 3-4), `Rtl ⊇ R` (the TL2 step); Steps 3-6 as hypotheses, Step 6 in slot form): `lem:main_ind_BA` in family form with TL2.
Step 5 is `STIngR5gL … STStep5ConclgL` (the unfolding of `STStep5RgL`, `Chain/Step5Gen.lean:214`).  Step 6 is the merged `STIngR6gL` at an arbitrary conclusion slot `Concl6`; the bridge `hb` turns TL1 and TL2
on `[s, t]` and the slot into `STStep6ConclgL`.  The proof is target 4 after target 5. -/
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

/-- **Target 7, `baMainIndFamTL_III_of`**: regime (iii) (`1 - s ≥ 1 - t ≥ lam²`); `(R, R34, Rtl) = (STReg5III, STReg5III, STCaseI)`; Steps 3-4 are T2509's `baStep3RegIII_holds`, `baStep4RegIII_holds`
(DECISIONS §331 (2)), the TL2 step `baTwistLoopStep_caseI` along `st_caseI_of_reg5III`; Step 5 (iii) is the hypothesis (DECISIONS §316), Step 6 and the bridge are the slot hypotheses. -/
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

/-- **Target 8, `baMainIndFamTL_I_of`**: regime (i) (`lam²/L² ≤ 1 - t ≤ 1 - s ≤ lam²`); `(STReg5I, STReg5I, STCaseI)`; Steps 3-4 `baStep3RegI_holds`, `baStep4RegI_holds`; Step 5 `baStep5I_holds`. -/
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

/-- **Target 9 (a), `baMainIndFamTL_II_of`**: regime (ii) (`lam²/L^d ≤ 1 - t ≤ 1 - s ≤ lam²/L²`); `(STReg5II, STCaseII, STCaseII)`; Steps 3-4 `baStep3II_holds`, `baStep4II_holds`; TL2 step
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

/-- **Target 9 (b), `baMainIndFamTL_IV_of`**: regime (iv) (`1 - t ≤ 1 - s ≤ lam²/L^d`); `(STReg5IV, STCaseII, STCaseII)` along `st_caseII_of_reg5IV` (`2 ≤ d`); Step 5 `baStep5IV_holds`. -/
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

/-! ## 4. Compiled `d = 3` instances (target 9′)

Regime (iii) at `(sz0, zSeq, flow_sz0)` weakened to `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2 ≤ T₀` (`half_lt_t0`), `lam² ≤ 1/4096 ≤ 1 - t`, with the non-main member
`BAzSrc sz0 zSeq (2/3) (17/25)` (the data of `MainIndOutBA` §7, read by `open private`).  Regimes (i), (ii), (iv) are empty at `sz0` (`TwistStep2_no_caseII_sz0`: `1 - s ≤ lam²` fails), so they are applied at the
private data of `Step5CasesBA` §5 (`L ≡ L`, `W_n = n + W₀`, `lam ≡ lam`, `w = (5003/5000) i`, flow `(κ_dom, 1/2, 1/9, 1/10)`, `s ≡ 0 < t ≡ t₀ ≤ T₀`, `(con_st_ind)` at every `𝔠d > 0`; read by `open private`),
at the family `κ = κ_dom/2` with the window `c₁` of `BAWinBulk_of_dom_holds`.  The six family conjuncts at every member of `Fam(s)` (the induction hypothesis) and the Step-6 slot with its bridge
(T2510; closed in `BA/MainIndRegBA`) stay hypotheses; every deterministic premise is discharged. -/

section Inst

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1FamInst
open private MainIndOutBA_flow MainIndOutBA_win MainIndOutBA_mem from RBM3D.BA.MainIndOutBA
open private Step5CasesBA_Datum Step5CasesBA_szI Step5CasesBA_zI Step5CasesBA_szII Step5CasesBA_zII Step5CasesBA_szIV Step5CasesBA_zIV Step5CasesBA_sz
  Step5CasesBA_datI Step5CasesBA_datII Step5CasesBA_datIV Step5CasesBA_regI Step5CasesBA_regII Step5CasesBA_regIV from RBM3D.BA.Step5CasesBA
local notation "μ0" => Sizes.seqP (sz0.withLam 0)
local notation "mem0" => BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)
local notation "Fam6" "(" C ", " μ ", " s ")" =>
  STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s
local notation "Fam7" "(" C ", " μ ", " t ")" =>
  STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

-- target 1: K2 at the non-main member of `Fam(1/10)`
example : STKboundgL (baFMz sz0 mem0) μ0 :=
  baKboundMember_holds 3 le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos
    (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win (fun _ => 1 / 10) (fun _ => by norm_num) mem0 (MainIndOutBA_mem _ (by norm_num))

-- target 2: the Step-1 pair at the non-main member of `Fam(1/2)`; the six conclusions at every member of `Fam(1/10)` are the one hypothesis
example (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    STStep1LoopgL (baFMz sz0 mem0) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) ∧ STStep1WeakgL (baFMz sz0 mem0) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) :=
  baStep1Fam_call 3 le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win (fun _ => 1 / 10) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 17 / 25).trans (t0_sz0_ge n)) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hfam (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) (by norm_num))
    mem0 (MainIndOutBA_mem _ (by norm_num))

/-- A family step at regime `R` applied at `(sz0, zSeq)`, `κ = 1/4`, `s ≡ 1/10 < t ≡ 1/2`, `c₁ = 1/3`: the seven conclusions at the non-main member of `Fam(1/2)` from the six at every member of `Fam(1/10)`. -/
private theorem MainIndFamTL_atSz0 {R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hfs : BAMainIndFamTL 3 R)
    (hR : R sz0 (fun _ => 1 / 10) (fun _ => 1 / 2)) (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := hfs le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win (fun _ => 1 / 10) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 17 / 25).trans (t0_sz0_ge n)) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hR hfam (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h0) mem0 (MainIndOutBA_mem _ (by norm_num))

section Slot
variable (Concl6 : ∀ (sz : Sizes 3) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)
  (hb : ∀ (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ),
    (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
    Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
include hb

-- target 6 at `(sz0, zSeq)`, regime (iii): `R, R34, Rtl` explicit, Steps 3-5 by name (Step 5 (iii) is `baStep5III_holds`), the slot Step 6 and its bridge the hypotheses
example (h6 : STIngR6gL 3 STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6)
    (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) :=
  MainIndFamTL_atSz0
    (baMainIndFamTL_of_steps 3 STReg5III STReg5III STCaseI (fun _ _ _ _ h => h) (fun _ => st_caseI_of_reg5III 3) (baTwistLoopStep_caseI 3)
      (baStep3RegIII_holds 3) (baStep4RegIII_holds 3) baStep5III_holds Concl6 h6 hb)
    (fun n => by nlinarith [sz0_lam_le n, sz0_lam_pos n]) hfam

-- target 7 at the same data
example (h6 : STIngR6gL 3 STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6)
    (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) :=
  MainIndFamTL_atSz0 (baMainIndFamTL_III_of 3 baStep5III_holds Concl6 h6 hb) (fun n => by nlinarith [sz0_lam_le n, sz0_lam_pos n]) hfam

end Slot

/-- A regime step at a private datum `(sz, z, κ_dom, t)` of `Step5CasesBA` (`s ≡ 0`): the family at `κ_dom / 2` with the window `c₁` of `BAWinBulk_of_dom_holds`. -/
private theorem MainIndFamTL_famData {sz : Sizes 3} {z : ℕ → ℂ} {κ : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ (1 / 2) (1 / 9) (1 / 10) z) (Λ : ℝ) (hΛ : 0 < Λ)
    (hlam : ∀ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ BAFlow sz (κ / 2) (1 / 2) (1 / 9) (1 / 10) z ∧ BAWinBulk sz z c₁ (κ / 2) := by
  obtain ⟨c₁, h0, h1, H⟩ := BAWinBulk_of_dom_holds 3 le_rfl κ Λ hκ hΛ
  exact ⟨c₁, h0, h1, ⟨hflow.1, fun n => ⟨(by linarith : κ / 2 ≤ κ).trans (hflow.2 n).1, (hflow.2 n).2⟩⟩, H (1 / 2) sz z hlam hflow.2⟩

/-- The family step at regime `R` applied at a private datum (`s ≡ 0`, `κ = κ_dom / 2`, `ε = 1/2`, `𝔠 = 1/9`, `𝔡 = 1/10`): the seven conclusions at the main flow at `t`, given the six at every member of `Fam(0)`. -/
private theorem MainIndFamTL_atDatum (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (hfs : BAMainIndFamTL 3 R) {sz : Sizes 3} {z : ℕ → ℂ} {κ : ℝ}
    {t : ℕ → ℝ} (hD : Step5CasesBA_Datum sz z κ (fun _ => 0) t) (Λ : ℝ) (hΛ : 0 < Λ) (hlam : ∀ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (hR : R sz (fun _ => 0) t) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ((∀ z', BAFamZ sz z c₁ (fun _ => 0) z' → Fam6(baFMz sz z', Sizes.seqP (sz.withLam 0), fun _ => 0)) →
      Fam7(baFMz sz z, Sizes.seqP (sz.withLam 0), t)) := by
  obtain ⟨hκ, hflow, hs0, hst, ht, hcon⟩ := hD
  obtain ⟨c₁, h0, h1, hfl, hwin⟩ := MainIndFamTL_famData hκ hflow Λ hΛ hlam
  obtain ⟨𝔠d, hc0, hc1, H⟩ := hfs le_rfl (κ / 2) (1 / 2) (1 / 10) (half_pos hκ) (by norm_num) (by norm_num)
  exact ⟨c₁, h0, h1, fun hfam => H (1 / 9) sz z hfl (fun n => (hlam n).1) c₁ h0 h1 hwin (fun _ => 0) t (fun _ => le_rfl)
    (fun n => (hst n).le.trans (ht n)) hst ht hR hfam (hcon 𝔠d hc0) z (BAFamZ_main _ _ _ _)⟩

section Slot2
variable (Concl6 : ∀ (sz : Sizes 3) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)
  (hb : ∀ (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ),
    (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
      BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) →
    Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
include hb

-- target 8, regime (i) at the datum `(L, W₀, lam, κ_dom, t) = (4, 25, 1, 1/70, 1/100)`
example (h6 : STIngR6gL 3 STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
      ((∀ z', BAFamZ Step5CasesBA_szI Step5CasesBA_zI c₁ (fun _ => 0) z' →
          Fam6(baFMz Step5CasesBA_szI z', Sizes.seqP (Step5CasesBA_szI.withLam 0), fun _ => 0)) →
        Fam7(baFMz Step5CasesBA_szI Step5CasesBA_zI, Sizes.seqP (Step5CasesBA_szI.withLam 0), fun _ => 1 / 100)) :=
  MainIndFamTL_atDatum STReg5I (baMainIndFamTL_I_of 3 Concl6 h6 hb) Step5CasesBA_datI 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szI, Step5CasesBA_sz], by norm_num [Step5CasesBA_szI, Step5CasesBA_sz]⟩) Step5CasesBA_regI

-- target 9 (a), regime (ii) at `(4, 25, 4, 1/1100, 9/10000)`
example (h6 : STIngR6gL 3 STReg5II (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
      ((∀ z', BAFamZ Step5CasesBA_szII Step5CasesBA_zII c₁ (fun _ => 0) z' →
          Fam6(baFMz Step5CasesBA_szII z', Sizes.seqP (Step5CasesBA_szII.withLam 0), fun _ => 0)) →
        Fam7(baFMz Step5CasesBA_szII Step5CasesBA_zII, Sizes.seqP (Step5CasesBA_szII.withLam 0), fun _ => 9 / 10000)) :=
  MainIndFamTL_atDatum STReg5II (baMainIndFamTL_II_of 3 Concl6 h6 hb) Step5CasesBA_datII 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szII, Step5CasesBA_sz], by norm_num [Step5CasesBA_szII, Step5CasesBA_sz]⟩) Step5CasesBA_regII

-- target 9 (b), regime (iv) at `(3, 40, 6, 1/1000, 1/2000)`
example (h6 : STIngR6gL 3 STReg5IV (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
      ((∀ z', BAFamZ Step5CasesBA_szIV Step5CasesBA_zIV c₁ (fun _ => 0) z' →
          Fam6(baFMz Step5CasesBA_szIV z', Sizes.seqP (Step5CasesBA_szIV.withLam 0), fun _ => 0)) →
        Fam7(baFMz Step5CasesBA_szIV Step5CasesBA_zIV, Sizes.seqP (Step5CasesBA_szIV.withLam 0), fun _ => 1 / 2000)) :=
  MainIndFamTL_atDatum STReg5IV (baMainIndFamTL_IV_of 3 Concl6 h6 hb) Step5CasesBA_datIV 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szIV, Step5CasesBA_sz], by norm_num [Step5CasesBA_szIV, Step5CasesBA_sz]⟩) Step5CasesBA_regIV

end Slot2

end Inst

end RBM.BA

end
