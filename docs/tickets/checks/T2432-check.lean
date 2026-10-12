/-
Release check for T2432 (dispatcher V3, Mon Oct 12 00:33 UTC 2026; DECISIONS §243).  BA-L L3a2 `BASymm2`: the twisted forms of the three BA expansions
(twin of LWSymm §5; T2395 §6 row L3a2).  Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2432_`;
the 1b names them `BAtwistSum`, `BAtwistFormE` or as the 1a fixes; content binding).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2432-check.lean
-/
import RBM3D.Graph.BASymm1
import RBM3D.Graph.LWSymm
import RBM3D.Graph.LWStein
import RBM3D.Graph.BAVocab
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.BA.MFixedPoint
import RBM3D.BA.CouplingWindow

set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open RBM RBM.Gauss RBM.Graph

/-! ## Part 1: merged names -/
-- L3a1 (T2425, `Graph/BASymm1`)
#check @RBM.Graph.BAGraph.twist
#check @RBM.Graph.ba_twist_counters
#check @RBM.Graph.BAtwistInv
#check @RBM.Graph.baTwistInv_holds
#check @RBM.Graph.BAtwistIntegral
#check @RBM.Graph.baTwistIntegral_holds
#check @RBM.Graph.BAGraph.BASymm1_val_twist
#check @RBM.Graph.BASymm1_data_real
#check @RBM.Graph.BASymm1_dataTr_flip
#check @RBM.Graph.BASymm1_flip_measurePreserving
#check @RBM.Graph.BASymm1Inst.G0
-- the frame identities and the counters of their terms (L2c1, L2c2, `lanlw`)
#check @RBM.Graph.lanlw_val
#check @RBM.Graph.BAGraph.lanlwTerms
#check @RBM.Graph.lanlw_ord
#check @RBM.Graph.lanlw_scalingOrderG
#check @RBM.Graph.BAGraph.lw2
#check @RBM.Graph.BAGraph.lw4
#check @RBM.Graph.baSum
#check @RBM.Graph.baExpFrame_lw
#check @RBM.Graph.lw_counters
#check @RBM.Graph.lw_raw
#check @RBM.Graph.lw_mono
#check @RBM.Graph.BAGraph.gg2
#check @RBM.Graph.BAGraph.gg4
#check @RBM.Graph.BAexpFrameE
#check @RBM.Graph.baExpFrameE_holds
#check @RBM.Graph.gg_counters
#check @RBM.Graph.gg_raw
#check @RBM.Graph.gg_mono
-- vocabulary, data, law, instance datum
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAGraph.counters
#check @RBM.Graph.BAGraph.scalingOrder
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.nExt
#check @RBM.Graph.BAGraph.nLoops
#check @RBM.Graph.BAGraph.nPairs
#check @RBM.Graph.BAlwData
#check @RBM.Gauss.PF
#check @RBM.Gauss.Idx
#check @RBM.BA.BASelf
#check @RBM.BA.CouplingWindowInst.flowP_data
-- the band basis (`LWSymm` §1, §3, §5) and the selectors reused by import
#check @RBM.Graph.lwSplit
#check @RBM.Graph.lwSymmTwistS
#check @RBM.Graph.lwSymmTwistP
#check @RBM.Graph.lwSymmTwistG_invol
#check @RBM.Graph.lwSymmTwistG_solid
#check @RBM.Graph.lwSymmTwistS_circ
#check @RBM.Graph.lwSymmTwistS_loop
#check @RBM.Graph.lwSymm_lwSplit_twistP
#check @RBM.Graph.lwSymm_cj_list_sum
#check @RBM.Graph.lwSymm_integral_cj
#check @RBM.Graph.lwSymm_twist_weight
#check @RBM.Graph.lwSymm_selector_edge
#check @RBM.Graph.lwSymm_selector_pair
#check @RBM.Graph.lwSymm_weight_graph_E
#check @RBM.Graph.lwSymm_oe1x_graph_E
#check @RBM.Graph.lwSymm_oe2x_graph_E
#check @RBM.Graph.lwSymm_weight_counters
#check @RBM.Graph.lwSymm_oe1x_counters
#check @RBM.Graph.lwSymm_oe2x_counters

/-! ## Part 2: the target statements (Prop values; no proof) -/

/-- Target 2 (`BAtwistSum d`): the twist of two lists of graphs in expectation at the BA law.  Two lists because the integrands of
`BAexpFrameE` are one integral of a sum (no integrability is needed); `lanlwTerms` is the case `B = []`. -/
def T2432_TwistSum (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Iy Iz : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Iy] [DecidableEq Iy] [Fintype Iz] [DecidableEq Iz]
      (c t' : Bool) (A : List (BAGraph Ex Iy)) (B : List (BAGraph Ex Iz)) (ℓe : Ex → Idx d L W),
      ∫ ω, baSum (A.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
          baSum (B.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        (if c then (star : ℂ → ℂ) else id)
          (∫ ω, baSum A (BAlwData d L W g0 Em t m ω) ℓe + baSum B (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- Target 3 (`BAtwistFormE d`): the three frame identities at a self-loop, an edge, a pair of either colour and direction.  The
selector `(c, t')` makes the twisted selected edge blue (twins of `lwSymm_weight_graph_E`, `lwSymm_oe1x_graph_E`,
`lwSymm_oe2x_graph_E`); the frame is `Γ.twist c t'`, every output is twisted back. -/
def T2432_FormE (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W)
      (c t' : Bool),
      -- (a) `lem_lweight` (`lw2`, `lw4`) at a circled self-loop
      (∀ p ∈ lwSplit Γ.solid, (lwSymmTwistS c t' p.1).σ = true → p.1.circ = true → p.1.src = p.1.dst →
        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, baSum (((Γ.twist c t').lw2 (lwSymmTwistP c t' p)).map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
            baSum (((Γ.twist c t').lw4 (lwSymmTwistP c t' p)).map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe
              ∂(PF d L W 0)) ∧
      -- (b) `lanlw` at a circled edge (the twisted edge is the blue out-edge of its source)
      (∀ p ∈ lwSplit Γ.solid, (lwSymmTwistS c t' p.1).σ = true → p.1.circ = true →
        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, baSum ((BAGraph.lanlwTerms (Γ.twist c t') (lwSymmTwistP c t' p)).map (BAGraph.twist c t'))
            (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) ∧
      -- (c) `GGGamma` (`gg2`, `gg4`) at a circled pair of one colour, an out- and an in-edge of one vertex after the twist
      (∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, (lwSymmTwistS c t' p.1).σ = true → p.1.circ = true →
        (lwSymmTwistS c t' q.1).σ = true → q.1.circ = true → (lwSymmTwistS c t' p.1).src = (lwSymmTwistS c t' q.1).dst →
        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, baSum (((Γ.twist c t').gg2 (lwSymmTwistP c t' p) (lwSymmTwistP c t' q)).map (BAGraph.twist c t'))
              (BAlwData d L W g0 Em t m ω) ℓe +
            baSum (((Γ.twist c t').gg4 (lwSymmTwistP c t' p) (lwSymmTwistP c t' q)).map (BAGraph.twist c t'))
              (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- Statement level at `d = 3` (the instances of the 1b use `L = 4`, `W = 2`, `flowP_data`). -/
example : Prop := T2432_TwistSum 3
example : Prop := T2432_FormE 3
