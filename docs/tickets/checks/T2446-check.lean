/-
Release check for T2446 (dispatcher V3, Mon Oct 12 09:34 UTC 2026; DECISIONS §257).  BA-L L3a5 `BALvl1C`: the existence of a step, the measure with `nExt`, the induction
along `BAReach`, and the BA `lvl1 lemma` (T2395 §6 row L3a5; twin of LWLvl1 §12-§14 and of `lvl1_lemma_size`).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2446_`; the 1b names them `BAlvl1ExistsStep`, `BAlvl1Lemma`,
`BAlvl1LemmaSize`, `ba_lvl1_mu_lt`, `BAReach.trans`, `ba_lvl1_induction`, or as the 1a fixes; content binding).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2446-check.lean
-/
import RBM3D.Graph.BALvl1B2
import RBM3D.Graph.BALvl1B
import RBM3D.Graph.BALvl1A
import RBM3D.Graph.BAStepS
import RBM3D.Graph.BASim
import RBM3D.Graph.BASim3
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BASymm2
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWLvl1
import RBM3D.Graph.LocalRegular
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.BA.MFixedPoint

set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open RBM RBM.Gauss RBM.Graph

/-! ## Part 1: merged names -/
-- L3a4 (T2442, `Graph/BALvl1B`, `BALvl1B2`): the measure predicate, the step is good (proved), the counter half, the atom helper
#check @RBM.Graph.BALvl1Good
#check @RBM.Graph.ba_good_of_lit
#check @RBM.Graph.BAlvl1StepGood
#check @RBM.Graph.baLvl1StepGood_holds
#check @RBM.Graph.BAstepMono
#check @RBM.Graph.baStepMono_holds
#check @RBM.Graph.BALvl1B_atom_eq_of_mem
-- L3a3 (T2440, `Graph/BALvl1A`): the step, reachability (registered `.below`), the step identity (proved), integrability, packing, instances
#check @RBM.Graph.BALocStep
#check @RBM.Graph.BAReach
#check @RBM.Graph.BAReach.refl
#check @RBM.Graph.BAReach.step
#check @RBM.Graph.BALvl1A_reach_refl
#check @RBM.Graph.BAlvl1StepIdentity
#check @RBM.Graph.baLvl1StepIdentity_holds
#check @RBM.Graph.BALvl1A_integrable_val
#check @RBM.Graph.BALvl1A_val_of_factor
#check @RBM.Graph.BALvl1A_val_of_not
#check @RBM.Graph.BALvl1A_comb_append
#check @RBM.Graph.BALvl1A_twist_invol
#check @RBM.Graph.BALvl1AInst.locStepB
#check @RBM.Graph.BALvl1AInst.normalB
-- R1 (T2423, `Graph/BASim*`): the five frame steps (their constructor hypotheses are what target 2 discharges), the twist of a packed graph
#check @RBM.Graph.BAFrameStep
#check @RBM.Graph.BAFrameStep.weight
#check @RBM.Graph.BAFrameStep.within
#check @RBM.Graph.BAFrameStep.edge
#check @RBM.Graph.BAFrameStep.gg
#check @RBM.Graph.BAFrameStep.ggSplit
#check @RBM.Graph.BAPGraph.twist
#check @RBM.Graph.BASimInst.baPB
-- R0 (T2417, `Graph/BAAtomic`): atom-level `LocStd` and its pieces, the measure pieces, the atom lemmas
#check @RBM.Graph.BAGraph.LocStd
#check @RBM.Graph.BAGraph.atEdges
#check @RBM.Graph.BAGraph.atCharge
#check @RBM.Graph.BAGraph.sameAtom
#check @RBM.Graph.BAGraph.intAtom
#check @RBM.Graph.BAGraph.nExt
#check @RBM.Graph.BAGraph.nLoops
#check @RBM.Graph.BAGraph.nPairs
#check @RBM.Graph.baPG
#check @RBM.Graph.BAGraph.BAAtomic_sameAtom_comm
#check @RBM.Graph.BAGraph.BAAtomic_sameAtom_iff
#check @RBM.Graph.BAGraph.BAAtomic_sameAtom_iff_atom_eq
#check @RBM.Graph.BAGraph.BAAtomic_intAtom_iff
-- L3a1, L3a2 (T2425, T2432, `Graph/BASymm1`, `BASymm2`): the twist keeps atoms, `sameAtom`, `intAtom`, counters, normality; the selected pair in the frame
#check @RBM.Graph.BAGraph.twist
#check @RBM.Graph.BAGraph.BASymm1_twist_atom
#check @RBM.Graph.BAGraph.BASymm1_twist_sameAtom
#check @RBM.Graph.BAGraph.BASymm1_twist_intAtom
#check @RBM.Graph.BASymm1_twistS_ends
#check @RBM.Graph.ba_twist_inv_out
#check @RBM.Graph.BAGraph.twist_invol
#check @RBM.Graph.BASymm2_frame_mem
#check @RBM.Graph.BASymm2_pair_mem
#check @RBM.Graph.BASymm2_frame_circ
-- the band's twist selectors (`LWSymm` §5), generic in the vertex type
#check @RBM.Graph.lwSplit
#check @RBM.Graph.lwSymmTwistS
#check @RBM.Graph.lwSymmTwistP
#check @RBM.Graph.lwSymmTwistG_solid
#check @RBM.Graph.lwSymm_lwSplit_twistP
#check @RBM.Graph.lwSymmTwistS_eq
#check @RBM.Graph.lwSymmTwistS_circ
#check @RBM.Graph.lwSymmTwistS_loop
#check @RBM.Graph.lwSymmTwistS_at
#check @RBM.Graph.lwSymm_twist_out
#check @RBM.Graph.lwSymm_twist_in
#check @RBM.Graph.lwSymm_twist_pair_in
#check @RBM.Graph.lwSymm_twist_pair_out
#check @RBM.Graph.lwSymm_twist_weight
#check @RBM.Graph.lwSymm_selector_edge
#check @RBM.Graph.lwSymm_selector_pair
-- counters, values, the BA data and law, list integrals
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.nS
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nA
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.counters
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.BAGraph.scalingSize
#check @RBM.Graph.Counters.scalingSize
#check @RBM.Graph.ord
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAComb.val
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
#check @RBM.Gauss.Idx
#check @RBM.BA.BASelf
#check @RBM.Graph.owx_integrable_list_sum
#check @RBM.Graph.owx_integral_list_sum
#check @RBM.Graph.BAVocabInst.baGGLhs
-- the band twin (`LWLvl1` §12-§15)
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.LocStep
#check @RBM.Graph.lvl1_exists_split_fst
#check @RBM.Graph.lvl1_split_two
#check @RBM.Graph.lvl1_exists_step
#check @RBM.Graph.Lvl1Reach
#check @RBM.Graph.Lvl1Reach.trans
#check @RBM.Graph.lvl1_induction
#check @RBM.Graph.Lvl1Mu
#check @RBM.Graph.Lvl1Lt
#check @RBM.Graph.lvl1Lt_wf
#check @RBM.Graph.lvl1_mu_lt
#check @RBM.Graph.lvl1_choose_list
#check @RBM.Graph.lvl1_sum_flatMap
#check @RBM.Graph.lvl1_exists_aux
#check @RBM.Graph.lvl1_lemma
#check @RBM.Graph.lvl1_lemma_induction
#check @RBM.Graph.lvl1Cutoff
#check @RBM.Graph.lvl1_size_le
#check @RBM.Graph.lvl1_lemma_size
-- downstream readers: L3b4′ (T2443, `Graph/BAStepS`, merged 9eaf866) along `BAReach`; the band consumer of `lvl1_lemma_size` that L3b1 twins
#check @RBM.Graph.BALocReg6
#check @RBM.Graph.baLocReg6_reach
#check @RBM.Graph.baReach_bReach
#check @RBM.Graph.lw_localregular_expansion

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- Target 1 (`BAlvl1ExistsStep`, `t/T2395` probe 275 verbatim; proved as target 2): a normal graph that is not locally standard at the atom level has a step. -/
def T2446_ExistsStep : Prop := ∀ {E : Type} (P : BAPGraph E), P.g.Normal → ¬ P.g.LocStd → ∃ outs, BALocStep P outs

/-- Target 3 (`ba_lvl1_mu_lt`, design §3 Step 4, K3): along a good output below the cutoff the measure `((K - ord)⁺, nExt, loops, n_S, pairs)` falls
lexicographically (the 1b's `BALvl1Lt (BALvl1Mu K Q) (BALvl1Mu K Γ)` unfolds to this). -/
def T2446_MuLt : Prop := ∀ {E : Type} (K : ℤ) (Γ Q : BAPGraph E), Γ.g.scalingOrder < K → BALvl1Good Γ.g Q.g →
  Prod.Lex (fun a b : ℕ => a < b) (Prod.Lex (fun a b : ℕ => a < b) (Prod.Lex (fun a b : ℕ => a < b) (Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b))))
    ((K - Q.g.scalingOrder).toNat, Q.g.nExt, Q.g.nLoops, Q.g.nS, Q.g.nPairs)
    ((K - Γ.g.scalingOrder).toNat, Γ.g.nExt, Γ.g.nLoops, Γ.g.nS, Γ.g.nPairs)

/-- Target 3 (`BAReach.trans`, twin of `Lvl1Reach.trans`, `LWLvl1:3755`). -/
def T2446_Trans : Prop := ∀ {E : Type} {K : ℤ} {P Q R : BAPGraph E}, BAReach K P Q → BAReach K Q R → BAReach K P R

/-- Target 3 (`ba_lvl1_induction`, twin of `lvl1_induction`, `LWLvl1:3763`): a predicate that holds at `P` and passes along every `BALocStep` holds at every
graph that `BAReach` reaches from `P`. -/
def T2446_Induction : Prop := ∀ {E : Type} {K : ℤ} {P Q : BAPGraph E}, BAReach K P Q → ∀ Pred : BAPGraph E → Prop, Pred P →
  (∀ (A : BAPGraph E) (L : List (BAPGraph E)), BALocStep A L → Pred A → ∀ B ∈ L, Pred B) → Pred Q

/-- Target 1 (`BAlvl1Lemma d`, probe 281-287 verbatim; proved as target 4): the BA `lvl1 lemma` (`B:407-409`; `lvl1_lemma`, `LWLvl1:3907`); the lists
do not depend on the data; the identity is BA's own (`BASelf`, `0 ≤ t < 1` only, C1). -/
def T2446_Lemma (d : ℕ) : Prop :=
  ∀ {E : Type} (K : ℤ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧ (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ outs ++ errs, BAReach K P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- Target 5 (`BAlvl1LemmaSize d`, twin of `lvl1_lemma_size`, `LWLvl1:4047`; design §3 Step 5): the paper's form at the cutoff
`K = lvl1Cutoff c K0 d D P.g.counters`; the errors have scaling size `≤ W^{-D}` in the window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`. -/
def T2446_LemmaSize (d : ℕ) : Prop :=
  ∀ {E : Type} (c : ℝ), 0 < c → ∀ (K0 : ℕ) (D : ℝ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
    (∀ Q ∈ outs ++ errs, BAReach (lvl1Cutoff c K0 d D P.g.counters : ℤ) P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧
      Q.g.nM ≤ P.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- Statement level: targets 2-5, and target 2 at `baGGLhs` (normal, not locally standard: probe 373) and at the twist of R1's macro datum `P_B`
(a within-atom solid edge: an atom-level loop). -/
example : Prop := T2446_ExistsStep
example : Prop := T2446_MuLt
example : Prop := T2446_Trans
example : Prop := T2446_Induction
example : Prop := T2446_Lemma 3
example : Prop := T2446_LemmaSize 3
example : Prop := ∃ outs, BALocStep (baPG BAVocabInst.baGGLhs) outs
example : Prop := ∃ outs, BALocStep ((baPG BASimInst.baPB).twist true true) outs

/-- Downstream fit (L3b4′ = T2443, merged 9eaf866): `BALocReg6` reads `BAReach K P0 Q` at `E = Fin 2`, which is the third conjunct of `T2446_Lemma`. -/
example : Prop := ∀ (d : ℕ) (K : ℤ) (P0 : BAPGraph (Fin 2)), T2446_Lemma d → P0.g.Normal →
  ∃ outs errs : List (BAPGraph (Fin 2)), ∀ Q ∈ outs ++ errs, BAReach K P0 Q
