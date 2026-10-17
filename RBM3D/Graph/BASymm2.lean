/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASymm1
import RBM3D.Graph.BAExpandWOrd
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGOp
import RBM3D.BA.CouplingWindow

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open private BAWeightOp_circ_counters from RBM3D.Graph.BAWeightOp

/-!
# BA-L L3a2 (T2432): the twisted forms of the three BA expansions

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:353-405` (cited `B:line`: `lanlw`, `lem_lweight`, `GGGamma`).  Design:
`docs/reports/T2395-design.md` §6 (row L3a2 `BASymm2`), probe `t/T2395:RBM3D/Probe/T2395Pins.lean:150-209, 232-256`.  The BA twin of
`Graph/LWSymm.lean` §5-§6 (`:1212-2326`), with the instance pattern of §6.  Under the chain S′ a BA step runs the merged frame
identity at the frame `Γ.twist c t` and twists every output back.  Here the merged frame identities (`lanlw_val`, `baExpFrameE_holds`)
are carried to an edge, a self-loop or a pair of either colour and direction of `Γ` itself.

## Contents (namespace `RBM.Graph`, private prefix `BASymm2_`)

1. **Target 1** `BAGraph.twist_invol`: the twist is an involution (twin of `lwSymmTwistG_invol`, `LWSymm.lean:181`).
2. **Target 2** `baSum_twist` (pathwise: the twist of a list of terms is the conjugate of the list at the transposed data), `baTwistIntegral_gen`
   (any functional `F` of the BA data: `∫ cj^c F(Tr^t' D ω) = cj^c ∫ F(D ω)`, no integrability hypothesis), `BAtwistSum`, `baTwistSum_holds`.
   `baTwistIntegral_gen` is the transport of any number of lists (the three- and four-list macro sums of L3a3 are one functional `F`).
3. **Target 3** `BAtwistFormE` (three conjuncts, twins of `lwSymm_weight_graph_E`, `lwSymm_oe1x_graph_E`, `lwSymm_oe2x_graph_E`,
   `LWSymm.lean:1590, 1639, 1690`), `baTwistFormE_holds`.  The hypotheses are on the twisted edges `lwSymmTwistS c t' _`; the frame is
   `Γ.twist c t'` at `lwSymmTwistP c t' p`; every output is twisted back.  No `LWSymm` §4 twin (`OwxE`): `lanlw_val` and `baExpFrameE_holds` hold at
   every endpoint `p.1.src : Ex ⊕ Ix`.  No uncircling (`lwSymmUncirc`, `M a b = 0`, `M a a = m`: C1 and T2395 F5).
4. **Target 4**: the twisted outputs have the counters, `scalingOrder`, `nExt`, `nLoops`, `nPairs` and normality of the untwisted ones
   (`ba_twist_inv_out`); the order and monotonicity bookkeeping of the three forms (`lanlw_ord`, `lw_raw`, `lw_mono`, `gg_raw`, `gg_mono`) holds for
   the twisted outputs relative to `Γ` (`baTwist_lanlw_ord`, `baTwist_lw_raw`, `baTwist_lw_mono`, `baTwist_gg_raw`, `baTwist_gg_mono`).
   `scalingOrderG` is a minimum over the partition of the output; `scalingOrderG (T.twist c t) = scalingOrderG T` needs the bridge
   `LGraph.partition (twist Γ) ≅ (partition Γ).map twist` assigned to L3b4′ (`T2423-amend-1.md` S1), so for `scalingOrderG` the statements are at
   the frame terms relative to `Γ` (`baTwist_lanlw_scalingOrderG`, `baTwist_lw_scalingOrderG`, `baTwist_gg_scalingOrderG`).
5. Compiled instances (`BASymm2Inst`) at `d = 3`, `L = 4`, `W = 2` and the flow point `flowP` (`BASelf` and `0 < t₀ < 1` are `flowP_data`).

`BASelf` and `0 ≤ t < 1` enter targets 2-3 only through the merged frame identities; targets 1, 2 (pathwise and `baTwistIntegral_gen`) and 4 use
neither (C1: no `M a b = 0`, no `M a a = m`, no uncircling, no smallness of `g₀`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
namespace RBM.Graph
open RBM RBM.Gauss RBM.Green

/-! ## 1. Target 1: the twist is an involution -/

section Invol

variable {E I : Type}

/-- **Target 1: the twist `(c, t)` is an involution** on `BAGraph` (twin of `lwSymmTwistG_invol`, `LWSymm.lean:181`; the dotted edges:
`BAMEdge.twist` flips the colour twice and swaps the ends twice, `BAPsiEdge.twist` swaps the ends twice). -/
theorem BAGraph.twist_invol (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).twist c t = Γ := by
  have h1 : ∀ e : BAPsiEdge (E ⊕ I), BAPsiEdge.twist t (BAPsiEdge.twist t e) = e := fun e => by
    cases e; cases t <;> rfl
  have h2 : ∀ e : BAMEdge (E ⊕ I), BAMEdge.twist c t (BAMEdge.twist c t e) = e := fun e => by
    cases e with | mk σ x y => cases c <;> cases t <;> simp [BAMEdge.twist]
  cases Γ with | mk G psi md =>
  simp only [BAGraph.twist, lwSymmTwistG_invol, List.map_map, Function.comp_def, h1, h2, List.map_id']

end Invol

/-! ## 2. Target 2: the twist of lists of terms in expectation -/

section Gen

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- **The twist integral of any functional of the BA data** (no integrability hypothesis): `∫ cj^c F(D^{t'} ω) = cj^c ∫ F(D ω)` over `PF d L W 0`,
where `D^{t'} ω` is the data of `ω` transposed if `t'`, which is the data at the flipped sample (`BASymm1_dataTr_flip`).  `F` is the integrand of
any finite sum of lists of terms: the three- and four-list macro sums of L3a3 are one such `F`. -/
theorem baTwistIntegral_gen (g0 Em t : ℝ) (m : ℂ) (c t' : Bool) (F : BALData (Idx d L W) → ℂ) :
    ∫ ω, lwSymmCj c (F (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t')) ∂(PF d L W 0) =
      lwSymmCj c (∫ ω, F (BAlwData d L W g0 Em t m ω) ∂(PF d L W 0)) := by
  rw [lwSymm_integral_cj]
  congr 1
  cases t'
  · rfl
  · simp only [BASymm1_dataTr_flip]
    exact (BASymm1_flip_measurePreserving d L W 0).integral_comp' (fun ω => F (BAlwData d L W g0 Em t m ω))

end Gen

/-! ## 3. Target 3: the three frame identities at an edge, a self-loop, a pair of either colour and direction -/

section Frame

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The selected pair of `Γ` in the frame `Γ.twist c t` is `lwSymmTwistP c t p` (the twisted edge first, the twisted rest). -/
theorem BASymm2_frame_mem (c t : Bool) (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) :
    lwSymmTwistP c t p ∈ lwSplit (Γ.twist c t).solid := by
  have hs : (Γ.twist c t).solid = Γ.solid.map (lwSymmTwistS c t) := lwSymmTwistG_solid c t Γ.toLGraph
  rw [hs, lwSymm_lwSplit_twistP]
  exact List.mem_map_of_mem hp

/-- The second selected edge of a pair in the frame. -/
theorem BASymm2_pair_mem (c t : Bool) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) :
    lwSymmTwistP c t q ∈ lwSplit (lwSymmTwistP c t p).2 := by
  rw [show (lwSymmTwistP c t p).2 = p.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP]
  exact List.mem_map_of_mem hq

/-- The circle of the selected edge is kept by the twist. -/
theorem BASymm2_frame_circ (c t : Bool) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hc : p.1.circ = true) :
    (lwSymmTwistP c t p).1.circ = true := by
  rw [show (lwSymmTwistP c t p).1 = lwSymmTwistS c t p.1 from rfl, lwSymmTwistS_circ]
  exact hc

end Frame

/-! ## 4. Target 4: the twisted outputs keep the counters, the order and the monotonicity data -/

section Out

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **Target 4, the twist of an output** (twin of `lwSymmTwistG_counters`, `lwSymm_cnt5`): `T.twist c t` has the counters, `scalingOrder`, `nExt`,
`nLoops`, `nPairs` of `T`, and is normal if `T` is (`ba_twist_counters`, `baTwistInv_holds`). -/
theorem ba_twist_inv_out (c t : Bool) (T : BAGraph E I) :
    (T.twist c t).counters = T.counters ∧ (T.twist c t).scalingOrder = T.scalingOrder ∧ (T.twist c t).nExt = T.nExt ∧
      (T.twist c t).nLoops = T.nLoops ∧ (T.twist c t).nPairs = T.nPairs ∧ (T.Normal → (T.twist c t).Normal) := by
  obtain ⟨h1, h2, h3, h4⟩ := baTwistInv_holds c t T
  exact ⟨ba_twist_counters c t T, by unfold BAGraph.scalingOrder; rw [ba_twist_counters c t T], h2, h3, h4, h1⟩

end Out

/-! ## 5. Compiled instances (`d = 3`, `L = 4`, `W = 2`, the flow point `flowP`) -/

end RBM.Graph

end
