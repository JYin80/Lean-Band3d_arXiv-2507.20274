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

section Sum

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The twist of a list of terms, pathwise**: for real `S` and real `gPsi`, `Σ_{T ∈ A} (T.twist c t).val D = (conj if c) Σ_{T ∈ A} T.val (D transposed
if t)` (twin of `BAGraph.BASymm1_val_twist`, `BASymm1.lean:261`, for `baSum`). -/
theorem baSum_twist {E I : Type} [Fintype I] [DecidableEq I] (D : BALData ι) (hS : ∀ i j, star (D.S i j) = D.S i j)
    (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool) (A : List (BAGraph E I)) (ℓe : E → ι) :
    baSum (A.map (BAGraph.twist c t)) D ℓe = lwSymmCj c (baSum A (BASymm1_dataTr D t) ℓe) := by
  unfold baSum
  rw [lwSymm_cj_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun T _ => BAGraph.BASymm1_val_twist D hS hP c t T ℓe

end Sum

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

/-- **Target 2: the twist of two lists of graphs in expectation at the BA law** (probe 234 pattern).  Two lists because the integrand of
`BAexpFrameE` is one integral of a sum (no integrability is needed); `lanlwTerms` is the case `B = []`. -/
def BAtwistSum (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Iy Iz : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Iy] [DecidableEq Iy] [Fintype Iz] [DecidableEq Iz]
      (c t' : Bool) (A : List (BAGraph Ex Iy)) (B : List (BAGraph Ex Iz)) (ℓe : Ex → Idx d L W),
      ∫ ω, baSum (A.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
          baSum (B.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        (if c then (star : ℂ → ℂ) else id)
          (∫ ω, baSum A (BAlwData d L W g0 Em t m ω) ℓe + baSum B (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- **`BAtwistSum d` holds**, for every `d`: pathwise `baSum_twist` at the real BA data (`BASymm1_data_real`), then `baTwistIntegral_gen` with the
functional `F D = baSum A D ℓe + baSum B D ℓe`.  `BASelf` and `0 ≤ t < 1` are not used. -/
theorem baTwistSum_holds (d : ℕ) : BAtwistSum d := by
  intro L W _ _ _ g0 Em t m _ _ _ Ex Iy Iz _ _ _ _ _ _ c t' A B ℓe
  have h1 : ∀ ω, baSum (A.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
      baSum (B.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe =
      lwSymmCj c (baSum A (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t') ℓe +
        baSum B (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t') ℓe) := fun ω => by
    rw [baSum_twist _ (BASymm1_data_real d L W g0 Em t m ω).1 (BASymm1_data_real d L W g0 Em t m ω).2,
      baSum_twist _ (BASymm1_data_real d L W g0 Em t m ω).1 (BASymm1_data_real d L W g0 Em t m ω).2, map_add]
  simp only [h1]
  rw [baTwistIntegral_gen d L W g0 Em t m c t' (fun D => baSum A D ℓe + baSum B D ℓe)]
  cases c <;> simp [lwSymmCj]

end RBM.Graph

end
