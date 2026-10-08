/-
Release check for T2314 (dispatcher V1, Thu Oct  8 02:10 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §127, §129).
Gate S3-18b2b (induction ST-3): the lift `PrecPT → Prec` of the per-time round `STXiRoundPT''` (T2313) to the
round pin `STXiRound'` (T2304) over the pair set `STPair s t`, and the assembly
  `stXiRoundQt_holds : ∀ d, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t)`,
  `stOeqQt'_holds : ∀ d, STOeqQt' d` (= `stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)`),
which deletes the owed registry line `RBM3D/Test/Axioms.lean:125` (`STOeqQt'`).
File `RBM3D/Induction/QtXiRoundLift.lean` (new).
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` ae94fa7).
Section 2: no new pin (every pin is merged: `STXiRound'`, `STXiBoot'`, `STOeqQt'`, `STXiRoundPT''`).
Section 3: the pinned statement shapes as `Prop`s (the two public theorems and the private helpers that are new text).
Section 4: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2314-check.lean`.
-/
import RBM3D.Induction.QEndB1
import RBM3D.Induction.QtNonzeroBoot
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Induction.QtNonzeroFlowLift
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.IterationsB
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Defs
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Sizes
import RBM3D.Gauss.Domination
import RBM3D.Green.Pins
import RBM3D.Loop.KLFinal

open MeasureTheory Filter Topology

/-! ## 1. Merged names -/

-- T2313 (S3-18b2a, `Induction/QEndB1` ae94fa7): the per-time round at `n_ ≥ 2` (`:100`, `:121`, `:1841`)
#check @RBM.Gauss.Sizes.STXiRoundPT''
#check @RBM.Gauss.Sizes.STOeqQtRoundPT''
#check @RBM.Ind.stOeqQtRoundPT''_holds
#check @RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT''
-- T2310 (S3-18b1, same file): the `3 ≤ n_` predecessor (`:84`, `:117`, `:1790`); not used by the proof
#check @RBM.Gauss.Sizes.STXiRoundPT'
#check @RBM.Gauss.Sizes.STOeqQtRoundPT'
#check @RBM.Ind.stOeqQtRoundPT'_holds

-- T2304 (S3-22c, `Induction/QtNonzeroBoot` 7812b3c): the round pin (`:92`) and the regime-generic bootstrap (`:581`)
#check @RBM.Gauss.Sizes.STXiRound'
#check @RBM.Ind.stBoot_rounds
#check @RBM.Ind.stXiBoot'_of_round
#check @RBM.Ind.stXiBootR_of_round
#check @RBM.Ind.stXiRoundNZ_holds
#check @RBM.Ind.stOeqQtNZ'_holds
#check @RBM.Ind.QtNonzeroBootInst.inst_OeqQtNZ'

-- the R2* pins (`Induction/NQEndFlow` 0f60da2): `STXiBoot'` `:95`, `STOeqQt'` `:127` (owed; target), `STIterR'` `:134`
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STOeqQt'
#check @RBM.Gauss.Sizes.STOeqQtNZ'
#check @RBM.Gauss.Sizes.STIterR'
#check @RBM.Gauss.Sizes.STIterations'
#check @RBM.Gauss.Sizes.STNQConclPT''
#check @RBM.Gauss.Sizes.STNQConcl''
#check @RBM.Gauss.Sizes.stOeqQt'_of_stOeqQt

-- the lift twins (`Induction/NQEndFlowLift` d0484be, `Induction/QtNonzeroFlowLift` 2cf288c): the public envelope
-- `nqFlowSharp` `:68` (reused), the public `𝒦` modulus `stKloop_lip` `:581` (reused), the targets of T2258/T2299
#check @RBM.Ind.nqFlowSharp
#check @RBM.Gauss.Sizes.stKloop_lip
#check @RBM.Ind.stOeqNQ''_holds
#check @RBM.Ind.NQEndFlowLiftInst.inst_OeqNQ''
#check @RBM.Gauss.Sizes.STNZConcl''
#check @RBM.Ind.stOeqNZ''_holds

-- the setting and the pins' vocabulary (`Induction/Step34Pins` fc76526, `Induction/Defs` 64bdfd3,
-- `Loop/GLoopFlow` 868b3b4)
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STmaxLK
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STStep3R
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STStep3I
#check @RBM.Gauss.Sizes.STStep4I
#check @RBM.Gauss.Sizes.STRegIterI
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.etaT
#check @RBM.lemT

-- the time modulus inputs (`Induction/LemDecCalELip` e4126a2, `Induction/ContinuityNet` 5b6cbc1,
-- `Gauss/Domination` 1c2e756, `Induction/ScaleFacts` 5d1e6b1, `Green/Pins` 64bdfd3, `Defs/Sizes` 0a873f1)
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_env
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.Gauss.netSize
#check @RBM.Gauss.netPt
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible

-- `≺` algebra (`Defs/StochDomAt` 9e2b00f): `StochDomAt` `:61`, `PerTimeDomAt` `:105`, `Prec` `:121`, `PrecPT` `:125`
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
#check @RBM.StochDomAt.of_le_left

-- consumers (`Induction/IterationsB` 64ed77f; S3-25 combines `STIterations'` with `STXiBoot'` from here)
#check @RBM.Gauss.Sizes.stIterations'_holds

-- instance data, case (i) (`Defs/Sizes` 0a873f1, `Induction/Defs` 64bdfd3, `Induction/Step34Pins` fc76526,
-- `Loop/KLFinal` 471b643)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.sz0_caseI
#check @RBM.Gauss.Step34Inst.sz0_con
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow

noncomputable section

namespace RBM.Gauss.Sizes.T2314Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 2. No new pin

Every pin this ticket touches is merged and unchanged: `STXiRound'` (QtNonzeroBoot.lean:92, the round; owed, stays),
`STXiBoot'` (NQEndFlow.lean:95; owed, stays), `STOeqQt'` (NQEndFlow.lean:127; owed; **proved here, line deleted**),
`STXiRoundPT''` (QEndB1.lean:100, the per-time input).  The only new names are the two public theorems of §3 and
private helpers with prefix `qtLift_`. -/

/-! ## 3. Pinned statement shapes -/

/-- **The intermediate (case-(i) round)**: `RBM.Ind.stXiRoundQt_holds` has exactly this type (the case-(i) twin of
`RBM.Ind.stXiRoundNZ_holds`, QtNonzeroBoot.lean:1059; the `𝔠_d` is that of `stOeqQtRoundPT''_holds d`). -/
def T2314_stXiRoundQt_holds : Prop := ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t)

/-- **T2314 (main)**: `RBM.Ind.stOeqQt'_holds` has exactly this type
(`example : RBM.Gauss.Sizes.T2314Check.T2314_stOeqQt'_holds := @RBM.Ind.stOeqQt'_holds`), and its term is
`fun d => stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)`. -/
def T2314_stOeqQt'_holds : Prop := ∀ d : ℕ, STOeqQt' d

/-- The merged consumer shape of `stXiBootR_of_round` at `R := STCaseI` (QtNonzeroBoot.lean:1233, compiled there). -/
def T2314_consumer_I : Prop :=
  ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) → STOeqQt' d

/-- `STXiRoundPT''` (`2 ≤ n_`) subsumes `STXiRoundPT'` (`3 ≤ n_`): the two texts differ only in the threshold, so the
T2310 theorem `stOeqQtRoundPT'_holds` is not needed (the proof uses `stOeqQtRoundPT''_holds` for every `n_ ≥ 2`).
Not a target; documents the drafting check (weakening the threshold hypothesis `2 ≤ n_` to `3 ≤ n_` proves it). -/
def T2314_PT''_imp_PT' : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), STXiRoundPT'' sz E s t → STXiRoundPT' sz E s t

/-- **Diagonal restriction of the per-time statement** (private `qtLift_diag_PT`, new text, ≈ 12 lines): a per-time
`≺` over the pairs whose left side depends on `q.1.1` only and whose right side depends on `q.1.2` only restricts to the
diagonal `w ↦ ((w, w), _)`, a per-time `≺` over `TimeIcc s t n × Unit` (the shape `nqLift_core_below` consumes). -/
def T2314_diag_PT : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (g : ℕ → ℝ → ℝ),
    PrecPT sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => g n q.1.2) →
    PrecPT sz (U := fun n => TimeIcc s t n × Unit) (fun n w ω => f n (w.1 : ℝ) ω) (fun n w _ => g n (w.1 : ℝ))

/-- **Diagonal → pair propagation** (private `qtLift_diag_to_pair`, new text, ≈ 20 lines): for a right side `g`
non-decreasing in the endpoint on `[s_n, t_n]`, the uniform `≺` on the diagonal gives the uniform `≺` over the pairs
(`g n q.1.1 ≤ g n q.1.2`; the pair-bad event is inside the diagonal-bad event at the same `τ`; `StochDomAt.of_subset`). -/
def T2314_diag_to_pair : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (g : ℕ → ℝ → ℝ),
    (∀ (n : ℕ) (v u : ℝ), s n ≤ v → v ≤ u → u ≤ t n → g n v ≤ g n u) →
    Prec sz (U := fun n => TimeIcc s t n × Unit) (fun n w ω => f n (w.1 : ℝ) ω) (fun n w _ => g n (w.1 : ℝ)) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => g n q.1.2)

/-- **The one-sided closeness of `Ξ̂^{(𝓛-𝒦)}_{·,n_}` on `contGood`** (private `qtLift_xiLK_close`, new text, ≈ 30 lines):
the per-loop closeness `nqLift_xi_close` (NQEndFlowLift.lean:757, copied as `qtLift_xi_close`) passed through the finite
`sup'` of `STmaxLK` (`Finset.sup'_le`, `Finset.le_sup'`): `Ξ̂_u ≤ Ξ̂_{u'} + 1` for `s ≤ u' ≤ u ≤ t`,
`u - u' ≤ N^{-(6 n_ + 20)}`. -/
def T2314_xiLK_close : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ),
    0 ≤ s → s ≤ u' → u' ≤ u → u ≤ t → t < 1 → N = ((sz.size n : ℕ) : ℝ) → (3 * n_ + 1 : ℝ) ≤ N →
    |E| < 2 → (etaT E t)⁻¹ ≤ N ^ 2 → ω ∈ RBM.Ind.ContinuityNet.contGood sz n →
    u - u' ≤ N ^ (-((6 * n_ + 20 : ℕ) : ℝ)) →
    (∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
      ‖STKloop sz n E u σ a - STKloop sz n E u' σ a‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) →
    STXiLK sz n E u n_ ω ≤ STXiLK sz n E u' n_ ω + 1

/-- **The lift `STXiRoundPT'' → STXiRound'`** (private `qtLift_lift`; private because its binder is the per-time pin,
which no public theorem concludes: the registry scan would report it): the shape of `nqLift_lift`
(NQEndFlowLift.lean:868) with the round pins in place of `STNQConclPT''`/`STNQConcl''`. -/
def T2314_lift : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {E s t : ℕ → ℝ} {κ' gmax : ℝ}, 0 < κ' → 0 < gmax →
    (∀ n, |E n| ≤ 2 - κ') → sz.SizeTendsto → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) →
    (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
    (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) →
    STXiRoundPT'' sz E s t → STXiRound' sz E s t

/-- **The right side at the envelope controls is non-decreasing in the endpoint** (private `qtLift_zeta_mono`, the
`lo = 1` copy of `nqLift_zeta_mono`, NQEndFlowLift.lean:189): the monotonicity `T2314_diag_to_pair` needs. -/
def T2314_zeta_mono : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {s t : ℕ → ℝ}, (∀ n, t n < 1) →
    ∀ {XL XLK : ℕ → ℕ → ℝ → ℝ}, (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    ∀ (n_ p n : ℕ) {θ u : ℝ}, s n ≤ θ → θ ≤ u → u ≤ t n →
    (sz.Bctl n θ) ^ (1 / 6 : ℝ) * RBM.Ind.nqFlowSharp t XLK n_ n θ +
      STbootRHS 1 (fun m => RBM.Ind.nqFlowSharp t XL m n θ) (fun m => RBM.Ind.nqFlowSharp t XLK m n θ)
        (sz.Bctl n (s n)) n_ p ≤
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * RBM.Ind.nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => RBM.Ind.nqFlowSharp t XL m n u) (fun m => RBM.Ind.nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p

/-! ## 4. Well-formedness (Prop-valued; no proof obligation) -/

/-- The target at `d = 3`, and the Step-3/4 case-(i) targets of S3-25/S3-26 that consume it. -/
example : Prop := STOeqQt' 3

example : Prop := STStep3I 3 ∧ STStep4I 3

/-- The target's ingredient form at the case-(i) instance data (instance (1); as `inst_OeqNQ''`,
`inst_OeqQtRoundPT''`). -/
example : Prop :=
  RBM.Gauss.Step34Inst.InstIngConcl (fun sz E s t => STXiBoot' sz E s t) RBM.Gauss.SizesInst.sz0
    RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst 1

/-- The round's ingredient form at the same data (instance (2)). -/
example : Prop :=
  RBM.Gauss.Step34Inst.InstIngConcl (fun sz E s t => STXiRound' sz E s t) RBM.Gauss.SizesInst.sz0
    RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst 1

/-- The per-time input at the same data is merged (`inst_OeqQtRoundPT''`, QEndB1.lean:1975). -/
example : Prop :=
  RBM.Gauss.Step34Inst.InstIngConcl (fun sz E s t => STXiRoundPT'' sz E s t) RBM.Gauss.SizesInst.sz0
    RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst 1

/-- The diagonal of the pair set is nonempty at every `n` (the index set of the net lift). -/
example : Prop :=
  ∀ n : ℕ, ∃ q : STPair RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst n, q.1.1 = q.1.2

/-- The envelope at the instance window (as the T2258/T2299 examples). -/
example : Prop := RBM.Ind.nqFlowSharp RBM.Gauss.InductionDefsInst.tInst (fun _ _ _ => 1) 0 0 0 = 1

example : Prop :=
  T2314_stXiRoundQt_holds ∧ T2314_stOeqQt'_holds ∧ T2314_consumer_I ∧ T2314_PT''_imp_PT' ∧ T2314_diag_PT ∧
    T2314_diag_to_pair ∧ T2314_xiLK_close ∧ T2314_lift ∧ T2314_zeta_mono

end RBM.Gauss.Sizes.T2314Check

end
