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

private theorem BASymm2_baSum_nil {E' I' ι : Type} [Fintype I'] [DecidableEq I'] [Fintype ι] [DecidableEq ι] (D : BALData ι)
    (ℓe : E' → ι) : baSum ([] : List (BAGraph E' I')) D ℓe = 0 := by
  simp [baSum]

end Frame

section Forms

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- **Twisting the frame identity back**: the frame identity `E Γ'.val = E (Σ_A + Σ_B)` at `Γ' = Γ.twist c t'` gives `E Γ.val = E (Σ_{A.map twist} +
Σ_{B.map twist})` (`baTwistIntegral_holds` and `baTwistSum_holds`: the twist is an involution of the expectations). -/
private theorem BASymm2_back (g0 Em t : ℝ) (m : ℂ) (c t' : Bool) (hL : 3 ≤ L) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (h0 : 0 ≤ t)
    (h1 : t < 1) {Ex Ix Iy Iz : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] [Fintype Iy] [DecidableEq Iy]
    [Fintype Iz] [DecidableEq Iz] (Γ : BAGraph Ex Ix) (A : List (BAGraph Ex Iy)) (B : List (BAGraph Ex Iz)) (ℓe : Ex → Idx d L W)
    (h : ∫ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, baSum A (BAlwData d L W g0 Em t m ω) ℓe + baSum B (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) :
    ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, baSum (A.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
        baSum (B.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  have e1 := baTwistSum_holds d L W hL g0 Em t m hSelf h0 h1 c t' A B ℓe
  have e2 := baTwistIntegral_holds d L W hL g0 Em t m hSelf h0 h1 c t' Γ ℓe
  rw [e1, ← h, e2]
  cases c <;> simp

/-- The one-list case of `BASymm2_back` (`B = []`). -/
private theorem BASymm2_back1 (g0 Em t : ℝ) (m : ℂ) (c t' : Bool) (hL : 3 ≤ L) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (h0 : 0 ≤ t)
    (h1 : t < 1) {Ex Ix Iy : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] [Fintype Iy] [DecidableEq Iy]
    (Γ : BAGraph Ex Ix) (A : List (BAGraph Ex Iy)) (ℓe : Ex → Idx d L W)
    (h : ∫ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, baSum A (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) :
    ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, baSum (A.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  have := BASymm2_back d L W g0 Em t m c t' hL hSelf h0 h1 Γ A ([] : List (BAGraph Ex Iy)) ℓe
    (by simpa only [BASymm2_baSum_nil, add_zero] using h)
  simpa only [List.map_nil, BASymm2_baSum_nil, add_zero] using this

end Forms

/-- **Target 3: the twisted forms of the three BA expansions** (twins of `lwSymm_weight_graph_E`, `lwSymm_oe1x_graph_E`, `lwSymm_oe2x_graph_E`,
`LWSymm.lean:1590, 1639, 1690`).  The selector `(c, t')` makes the twisted selected edge blue (`c = true` iff the selected edge is red, `t' = true` iff it
is an in-edge of its vertex, `lwSymm_selector_edge`, `lwSymm_selector_pair`); the frame is `Γ.twist c t'` at `lwSymmTwistP c t' p`; every output is twisted
back.  (a) `lem_lweight` (`lw2`, `lw4`) at a circled self-loop; (b) `lanlw` at a circled edge; (c) `GGGamma` (`gg2`, `gg4`) at a circled pair. -/
def BAtwistFormE (d : ℕ) : Prop :=
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

/-- **`BAtwistFormE d` holds**, for every `d`: the merged frame identities `baExpFrame_lw`, `lanlw_val`, `baExpFrame_gg` at the frame `Γ.twist c t'`
(their hypotheses are those of the twisted edges: `σ`, `circ` kept by `lwSymmTwistS_circ`, loops kept by `lwSymmTwistS_loop`), carried back by
`BASymm2_back` (`baTwistIntegral_holds`, `baTwistSum_holds`).  No `LWSymm` §4 twin: the endpoint `p.1.src : Ex ⊕ Ix` is free. -/
theorem baTwistFormE_holds (d : ℕ) : BAtwistFormE d := by
  intro L W _ _ hL g0 Em t m hSelf h0 h1 Ex Ix _ _ _ _ Γ ℓe c t'
  refine ⟨fun p hp hσ hc hxx => ?_, fun p hp hσ hc => ?_, fun p hp q hq hσp hcp hσq hcq hxy => ?_⟩
  · exact BASymm2_back d L W g0 Em t m c t' hL hSelf h0 h1 Γ _ _ ℓe
      (baExpFrame_lw d L W hL g0 Em t m hSelf h0 h1 (Γ.twist c t') ℓe (lwSymmTwistP c t' p) (BASymm2_frame_mem c t' Γ p hp) hσ
        (BASymm2_frame_circ c t' p hc) ((lwSymmTwistS_loop c t' p.1).2 hxx))
  · exact BASymm2_back1 d L W g0 Em t m c t' hL hSelf h0 h1 Γ _ ℓe
      (lanlw_val d L W hL g0 Em t m hSelf h0 h1 (Γ.twist c t') (lwSymmTwistP c t' p) (BASymm2_frame_mem c t' Γ p hp) hσ
        (BASymm2_frame_circ c t' p hc) ℓe)
  · exact BASymm2_back d L W g0 Em t m c t' hL hSelf h0 h1 Γ _ _ ℓe
      (baExpFrame_gg d L W hL g0 Em t m hSelf h0 h1 (Γ.twist c t') ℓe (lwSymmTwistP c t' p) (BASymm2_frame_mem c t' Γ p hp)
        (lwSymmTwistP c t' q) (BASymm2_pair_mem c t' p q hq) hσp (BASymm2_frame_circ c t' p hcp) hσq
        (BASymm2_frame_circ c t' q hcq) hxy)

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

/-- The circled twisted graph: the same counters and atoms as the circled graph. -/
private theorem BASymm2_circ_twist (c t : Bool) (T : BAGraph E I) :
    (BAWeightOp_circ (T.twist c t)).counters = (BAWeightOp_circ T).counters ∧
      (BAWeightOp_circ (T.twist c t)).atom = (BAWeightOp_circ T).atom := by
  refine ⟨by rw [BAWeightOp_circ_counters, BAWeightOp_circ_counters, ba_twist_counters], ?_⟩
  change (T.twist c t).atom = T.atom
  exact BAGraph.BASymm1_twist_atom c t T

/-- The raw order of a circled twisted output is that of the output. -/
private theorem BASymm2_circ_twist_ord (c t : Bool) (T : BAGraph E I) :
    (BAWeightOp_circ (T.twist c t)).scalingOrder = (BAWeightOp_circ T).scalingOrder := by
  unfold BAGraph.scalingOrder; rw [(BASymm2_circ_twist c t T).1]

/-- The monotonicity data of a circled twisted output (`lw_mono`): the same `n_M`, `n_A - n_W` and number of external atoms; the frame `Γ.twist c t` has those
of `Γ` (`ba_twist_counters`, `BAGraph.BASymm1_twist_atom`). -/
private theorem BASymm2_mono (c t : Bool) (Γ : BAGraph E I) {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (T : BAGraph E' I')
    (h : (BAWeightOp_circ T).nM = (Γ.twist c t).nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW =
        ((Γ.twist c t).nA : ℤ) - (Γ.twist c t).nW ∧
      ((Finset.univ.filter fun v : E' ⊕ I' => v.isLeft = true).image (BAWeightOp_circ T).atom).card ≤
        ((Finset.univ.filter fun v : E ⊕ I => v.isLeft = true).image (Γ.twist c t).atom).card) :
    (BAWeightOp_circ (T.twist c t)).nM = Γ.nM ∧ ((BAWeightOp_circ (T.twist c t)).nA : ℤ) - (BAWeightOp_circ (T.twist c t)).nW =
        (Γ.nA : ℤ) - Γ.nW ∧
      ((Finset.univ.filter fun v : E' ⊕ I' => v.isLeft = true).image (BAWeightOp_circ (T.twist c t)).atom).card ≤
        ((Finset.univ.filter fun v : E ⊕ I => v.isLeft = true).image Γ.atom).card := by
  have hc := (BASymm2_circ_twist c t T).1
  have hΓ := ba_twist_counters c t Γ
  rw [BAGraph.BASymm1_twist_atom] at h
  rw [(BASymm2_circ_twist c t T).2]
  have e1 : (BAWeightOp_circ (T.twist c t)).nM = (BAWeightOp_circ T).nM := congrArg Counters.nM hc
  have e2 : (BAWeightOp_circ (T.twist c t)).nA = (BAWeightOp_circ T).nA := congrArg Counters.nV hc
  have e3 : (BAWeightOp_circ (T.twist c t)).nW = (BAWeightOp_circ T).nW := congrArg Counters.nW hc
  have g1 : (Γ.twist c t).nM = Γ.nM := congrArg Counters.nM hΓ
  have g2 : (Γ.twist c t).nA = Γ.nA := congrArg Counters.nV hΓ
  have g3 : (Γ.twist c t).nW = Γ.nW := congrArg Counters.nW hΓ
  rw [e1, e2, e3]
  rw [g1, g2, g3] at h
  exact h

end Out

section OutForms

variable {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix]

/-- **`lanlw_ord` for the twisted outputs** (`B:361-363`): every term of the frame list `lanlwTerms (Γ.twist c t) (lwSymmTwistP c t p)`, twisted back, has raw order
`ord Γ + 1`. -/
theorem baTwist_lanlw_ord (c t : Bool) (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : (lwSymmTwistS c t p.1).σ = true) (hc : p.1.circ = true) :
    ∀ Δ ∈ (BAGraph.lanlwTerms (Γ.twist c t) (lwSymmTwistP c t p)).map (BAGraph.twist c t), Δ.scalingOrder = Γ.scalingOrder + 1 := by
  intro Δ hΔ
  obtain ⟨Δ0, h0, rfl⟩ := List.mem_map.1 hΔ
  rw [(ba_twist_inv_out c t Δ0).2.1, lanlw_ord (Γ.twist c t) _ (BASymm2_frame_mem c t Γ p hp) hσ (BASymm2_frame_circ c t p hc) Δ0 h0,
    (ba_twist_inv_out c t Γ).2.1]

/-- **`lanlw_scalingOrderG` at the frame terms, relative to `Γ`** (`B:354-372`): for a normal `Γ`, every term of the frame list has `scalingOrderG ≥ ord Γ`
(`Γ.twist c t` is normal and has the order of `Γ`).  `scalingOrderG` of the twisted term itself is L3b4′'s bridge (module docstring). -/
theorem baTwist_lanlw_scalingOrderG (c t : Bool) (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : (lwSymmTwistS c t p.1).σ = true) (hc : p.1.circ = true) (hN : Γ.Normal) :
    ∀ Δ ∈ BAGraph.lanlwTerms (Γ.twist c t) (lwSymmTwistP c t p), ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ Δ.scalingOrderG := by
  have := lanlw_scalingOrderG (Γ.twist c t) _ (BASymm2_frame_mem c t Γ p hp) hσ (BASymm2_frame_circ c t p hc)
    ((ba_twist_inv_out c t Γ).2.2.2.2.2 hN)
  rwa [(ba_twist_inv_out c t Γ).2.1] at this

/-- **`lw_raw` for the twisted outputs** (`B:353`): every term of `lw2` and `lw4` of the frame, twisted back, has `ord T° = ord Γ + 1`. -/
theorem baTwist_lw_raw (c t : Bool) (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : (lwSymmTwistS c t p.1).σ = true) (hc : p.1.circ = true) :
    (∀ T ∈ ((Γ.twist c t).lw2 (lwSymmTwistP c t p)).map (BAGraph.twist c t), (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) ∧
      (∀ T ∈ ((Γ.twist c t).lw4 (lwSymmTwistP c t p)).map (BAGraph.twist c t), (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) := by
  obtain ⟨h2, h4⟩ := lw_raw (Γ.twist c t) _ (BASymm2_frame_mem c t Γ p hp) hσ (BASymm2_frame_circ c t p hc)
  rw [(ba_twist_inv_out c t Γ).2.1] at h2 h4
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    rw [BASymm2_circ_twist_ord]; exact h2 T0 h0
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    rw [BASymm2_circ_twist_ord]; exact h4 T0 h0

/-- **`lw_mono` for the twisted outputs** (L3a4): `n_M`, `n_A - n_W` and the number of external atoms of `T°` for the twisted terms, relative to `Γ`. -/
theorem baTwist_lw_mono (c t : Bool) (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : (lwSymmTwistS c t p.1).σ = true) (hc : p.1.circ = true) :
    (∀ T ∈ ((Γ.twist c t).lw2 (lwSymmTwistP c t p)).map (BAGraph.twist c t), (BAWeightOp_circ T).nM = Γ.nM ∧
        ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW = (Γ.nA : ℤ) - Γ.nW ∧
        ((Finset.univ.filter fun v : Ex ⊕ (Ix ⊕ Fin 2) => v.isLeft = true).image (BAWeightOp_circ T).atom).card ≤
          ((Finset.univ.filter fun v : Ex ⊕ Ix => v.isLeft = true).image Γ.atom).card) ∧
      (∀ T ∈ ((Γ.twist c t).lw4 (lwSymmTwistP c t p)).map (BAGraph.twist c t), (BAWeightOp_circ T).nM = Γ.nM ∧
        ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW = (Γ.nA : ℤ) - Γ.nW ∧
        ((Finset.univ.filter fun v : Ex ⊕ (Ix ⊕ Fin 4) => v.isLeft = true).image (BAWeightOp_circ T).atom).card ≤
          ((Finset.univ.filter fun v : Ex ⊕ Ix => v.isLeft = true).image Γ.atom).card) := by
  obtain ⟨h2, h4⟩ := lw_mono (Γ.twist c t) _ (BASymm2_frame_mem c t Γ p hp) hσ (BASymm2_frame_circ c t p hc)
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    exact BASymm2_mono c t Γ T0 (h2 T0 h0)
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    exact BASymm2_mono c t Γ T0 (h4 T0 h0)

/-- **`lw_scalingOrderG` at the frame terms, relative to `Γ`** (`B:354-355`). -/
theorem baTwist_lw_scalingOrderG (c t : Bool) (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : (lwSymmTwistS c t p.1).σ = true) (hc : p.1.circ = true) (hN : Γ.Normal) :
    (∀ T ∈ (Γ.twist c t).lw2 (lwSymmTwistP c t p), ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
      (∀ T ∈ (Γ.twist c t).lw4 (lwSymmTwistP c t p), ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) := by
  have := lw_scalingOrderG (Γ.twist c t) _ (BASymm2_frame_mem c t Γ p hp) hσ (BASymm2_frame_circ c t p hc)
    ((ba_twist_inv_out c t Γ).2.2.2.2.2 hN)
  rwa [(ba_twist_inv_out c t Γ).2.1] at this

/-- **`gg_raw` for the twisted outputs** (`B:393-405`): `A1` of the frame, twisted back, has `ord = ord Γ + 2κ` (`κ` at the atoms of `y = p'.1.dst`,
`y' = q'.1.src` of the frame, which are those of `Γ`); every other term of `gg2` and every term of `gg4`, twisted back, has `ord T° = ord Γ + 1`. -/
theorem baTwist_gg_raw (c t : Bool) (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) :
    ((BAGGOp_A1 (Γ.twist c t) (lwSymmTwistP c t p) (lwSymmTwistP c t q)).twist c t).scalingOrder =
        Γ.scalingOrder + 2 * (BAGGOp_kappa Γ (lwSymmTwistP c t q).1.src (lwSymmTwistP c t p).1.dst : ℤ) ∧
      (∀ T ∈ (((Γ.twist c t).gg2 (lwSymmTwistP c t p) (lwSymmTwistP c t q)).tail).map (BAGraph.twist c t),
        (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) ∧
      (∀ T ∈ ((Γ.twist c t).gg4 (lwSymmTwistP c t p) (lwSymmTwistP c t q)).map (BAGraph.twist c t),
        (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) := by
  obtain ⟨h1, h2, h4⟩ := gg_raw (Γ.twist c t) _ _ (BASymm2_frame_mem c t Γ p hp) (BASymm2_pair_mem c t p q hq)
  have hk : BAGGOp_kappa (Γ.twist c t) (lwSymmTwistP c t q).1.src (lwSymmTwistP c t p).1.dst =
      BAGGOp_kappa Γ (lwSymmTwistP c t q).1.src (lwSymmTwistP c t p).1.dst := by
    simp only [BAGGOp_kappa, BAGraph.BASymm1_twist_atom]
  rw [hk, (ba_twist_inv_out c t Γ).2.1] at h1
  rw [(ba_twist_inv_out c t Γ).2.1] at h2 h4
  refine ⟨by rw [(ba_twist_inv_out c t _).2.1]; exact h1, fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    rw [BASymm2_circ_twist_ord]; exact h2 T0 h0
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    rw [BASymm2_circ_twist_ord]; exact h4 T0 h0

/-- **`gg_mono` for the twisted outputs** (L3a4), relative to `Γ`. -/
theorem baTwist_gg_mono (c t : Bool) (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) :
    (∀ T ∈ ((Γ.twist c t).gg2 (lwSymmTwistP c t p) (lwSymmTwistP c t q)).map (BAGraph.twist c t), BAGGOp_Mono Γ T) ∧
      (∀ T ∈ ((Γ.twist c t).gg4 (lwSymmTwistP c t p) (lwSymmTwistP c t q)).map (BAGraph.twist c t), BAGGOp_Mono Γ T) := by
  obtain ⟨h2, h4⟩ := gg_mono (Γ.twist c t) _ _ (BASymm2_frame_mem c t Γ p hp) (BASymm2_pair_mem c t p q hq)
  have key : ∀ {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (T : BAGraph E' I'),
      BAGGOp_Mono (Γ.twist c t) T → BAGGOp_Mono Γ (T.twist c t) := fun T h => by
    obtain ⟨m1, m2, m3⟩ := h
    have hΓ := ba_twist_counters c t Γ
    have g1 : (Γ.twist c t).nM = Γ.nM := congrArg Counters.nM hΓ
    have g2 : (Γ.twist c t).nA = Γ.nA := congrArg Counters.nV hΓ
    have g3 : (Γ.twist c t).nW = Γ.nW := congrArg Counters.nW hΓ
    have hc := (BASymm2_circ_twist c t T).1
    have e1 : (BAWeightOp_circ (T.twist c t)).nM = (BAWeightOp_circ T).nM := congrArg Counters.nM hc
    have e2 : (BAWeightOp_circ (T.twist c t)).nA = (BAWeightOp_circ T).nA := congrArg Counters.nV hc
    have e3 : (BAWeightOp_circ (T.twist c t)).nW = (BAWeightOp_circ T).nW := congrArg Counters.nW hc
    refine ⟨by rw [e1]; omega, by rw [e2, e3]; omega, ?_⟩
    unfold BAGGOp_nExt at m3 ⊢
    rw [BAGraph.BASymm1_twist_atom] at m3
    rw [(BASymm2_circ_twist c t T).2]
    exact m3
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    exact key T0 (h2 T0 h0)
  · obtain ⟨T0, h0, rfl⟩ := List.mem_map.1 hT
    exact key T0 (h4 T0 h0)

/-- **`gg_scalingOrderG` at the frame terms, relative to `Γ`** (`B:354-355`). -/
theorem baTwist_gg_scalingOrderG (c t : Bool) (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hN : Γ.Normal) :
    (∀ T ∈ (Γ.twist c t).gg2 (lwSymmTwistP c t p) (lwSymmTwistP c t q), ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
      (∀ T ∈ (Γ.twist c t).gg4 (lwSymmTwistP c t p) (lwSymmTwistP c t q), ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) := by
  have := gg_scalingOrderG (Γ.twist c t) _ _ (BASymm2_frame_mem c t Γ p hp) (BASymm2_pair_mem c t p q hq)
    ((ba_twist_inv_out c t Γ).2.2.2.2.2 hN)
  rwa [(ba_twist_inv_out c t Γ).2.1] at this

end OutForms

/-! ## 5. Compiled instances (`d = 3`, `L = 4`, `W = 2`, the flow point `flowP`) -/

namespace BASymm2Inst

open RBM.BA.CouplingWindowInst

/-- The graph of the instances: external `v0 = inl 0`, `v1 = inl 1`, internal `x = inr 0`, `y = inr 1`.  Solid edges (all circled, so the graph is normal):
the **red** circled self-loop `Ḡ̊_{v0 v0}`, the **red** circled in-edge `Ḡ̊_{v1 x}` of `x`, the **red** circled out-edge `Ḡ̊_{x v0}` of `x` and the blue circled
`G̊_{x y}`; waved edges: the coloured `S⁺_{v0 v1}` and the black `S_{x y}`; the `×`-dotted edge `v0 v1`; the `Ψ`-dotted edge `Ψ_{v1 y}`; the `M`-dotted
edge `M_{x y}`; the coefficient `1 + i/2`. -/
def G1 : BAGraph (Fin 2) (Fin 2) where
  solid := [⟨false, true, Sum.inl 0, Sum.inl 0⟩, ⟨false, true, Sum.inl 1, Sum.inr 0⟩, ⟨false, true, Sum.inr 0, Sum.inl 0⟩,
    ⟨true, true, Sum.inr 0, Sum.inr 1⟩]
  waved := [⟨true, true, Sum.inl 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 0, Sum.inr 1⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inl 1⟩]
  coeff := 1 + (1 / 2 : ℂ) * Complex.I
  psi := [⟨Sum.inl 1, Sum.inr 1⟩]
  mdot := [⟨true, Sum.inr 0, Sum.inr 1⟩]

theorem G1_normal : G1.Normal := ⟨by decide, by decide⟩

/-- The counters of `G1`: `n_S = 4`, `n_W = 2`, `n_A = 0` (`Ψ`- and `M`-dotted edges join `x`, `y` to the atom of `v1`), `n_M = 0`, so `ord G1 = 8`. -/
theorem G1_counts : (G1.nS, G1.nW, G1.nA, G1.nM) = (4, 2, 0, 0) ∧ G1.scalingOrder = 8 := by decide

/-- (a) the red self-loop `Ḡ̊_{v0 v0}` with the other three edges. -/
def Pa : SEdge (Fin 2 ⊕ Fin 2) × List (SEdge (Fin 2 ⊕ Fin 2)) :=
  (⟨false, true, Sum.inl 0, Sum.inl 0⟩, [⟨false, true, Sum.inl 1, Sum.inr 0⟩, ⟨false, true, Sum.inr 0, Sum.inl 0⟩,
    ⟨true, true, Sum.inr 0, Sum.inr 1⟩])

/-- (b), (c) the red in-edge `Ḡ̊_{v1 x}` of `x` with the other three edges. -/
def Pb : SEdge (Fin 2 ⊕ Fin 2) × List (SEdge (Fin 2 ⊕ Fin 2)) :=
  (⟨false, true, Sum.inl 1, Sum.inr 0⟩, [⟨false, true, Sum.inl 0, Sum.inl 0⟩, ⟨false, true, Sum.inr 0, Sum.inl 0⟩,
    ⟨true, true, Sum.inr 0, Sum.inr 1⟩])

/-- (c) the second edge of the red pair `Ḡ̊_{v1 x}`, `Ḡ̊_{x v0}`: the red out-edge of `x`. -/
def Qc : SEdge (Fin 2 ⊕ Fin 2) × List (SEdge (Fin 2 ⊕ Fin 2)) :=
  (⟨false, true, Sum.inr 0, Sum.inl 0⟩, [⟨false, true, Sum.inl 0, Sum.inl 0⟩, ⟨true, true, Sum.inr 0, Sum.inr 1⟩])

/-- The memberships (`SEdge` has no `DecidableEq`, so `simp` unfolds `lwSplit` instead of `decide`). -/
theorem Pa_mem : Pa ∈ lwSplit G1.solid := by simp [lwSplit, Pa, G1]
theorem Pb_mem : Pb ∈ lwSplit G1.solid := by simp [lwSplit, Pb, G1]
theorem Qc_mem : Qc ∈ lwSplit Pb.2 := by simp [lwSplit, Pb, Qc]

/-- Two nonempty lists over different vertex types, for the instance of target 2 (`G0` of `BASymm1Inst`: five vertices; `G1`: four). -/
def A0 : List (BAGraph (Fin 2) (Fin 3)) := [BASymm1Inst.G0, BASymm1Inst.G0.twist true false]
def B0 : List (BAGraph (Fin 2) (Fin 2)) := [G1, G1.twist false true]

/-- **Target 1** at `G1`: the twist `(true, true)` is an involution and moves `G1` (the red self-loop becomes blue). -/
example : (G1.twist true true).twist true true = G1 ∧ G1.twist true true ≠ G1 := by
  refine ⟨BAGraph.twist_invol true true G1, fun h => ?_⟩
  have := congrArg (fun Γ : BAGraph (Fin 2) (Fin 2) => (Γ.solid.map SEdge.σ)) h
  simp [G1, BAGraph.twist, lwSymmTwistG, LGraph.conj, LGraph.transpose, SEdge.conj, SEdge.transpose] at this

/-- **Target 2** at two nonempty lists (`A0` of two graphs over `Fin 2`, `Fin 3`; `B0` of two graphs over `Fin 2`, `Fin 2`), the twist `(true, true)`
(conjugate and transpose): the expectation of the twisted sums is the conjugate of that of the sums. -/
example :
    ∫ ω, baSum (A0.map (BAGraph.twist true true)) (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 +
        baSum (B0.map (BAGraph.twist true true)) (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      (if true then (star : ℂ → ℂ) else id)
        (∫ ω, baSum A0 (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 + baSum B0 (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0
          ∂(PF 3 4 2 0)) :=
  baTwistSum_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 true true A0 B0 BASymm1Inst.ℓ0

/-- `baTwistIntegral_gen` at a nonlinear functional of the data (a product of two list sums), the twist `(false, true)`. -/
example :
    ∫ ω, lwSymmCj false ((fun D => baSum A0 D BASymm1Inst.ℓ0 * baSum B0 D BASymm1Inst.ℓ0)
        (BASymm1_dataTr (BAlwData 3 4 2 g0P EP t0P m0P ω) true)) ∂(PF 3 4 2 0) =
      lwSymmCj false (∫ ω, (fun D => baSum A0 D BASymm1Inst.ℓ0 * baSum B0 D BASymm1Inst.ℓ0) (BAlwData 3 4 2 g0P EP t0P m0P ω) ∂(PF 3 4 2 0)) :=
  baTwistIntegral_gen 3 4 2 g0P EP t0P m0P false true (fun D => baSum A0 D BASymm1Inst.ℓ0 * baSum B0 D BASymm1Inst.ℓ0)

/-- **Target 3 (a)** at the red self-loop `Pa`, `c = true` (`t'` is immaterial for a loop): `lem_lweight` at the frame `G1.twist true t'`. -/
example (t' : Bool) :
    ∫ ω, G1.val (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, baSum (((G1.twist true t').lw2 (lwSymmTwistP true t' Pa)).map (BAGraph.twist true t')) (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 +
        baSum (((G1.twist true t').lw4 (lwSymmTwistP true t' Pa)).map (BAGraph.twist true t')) (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0
          ∂(PF 3 4 2 0) :=
  (baTwistFormE_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 G1 BASymm1Inst.ℓ0 true t').1
    Pa Pa_mem (by cases t' <;> rfl) rfl rfl

/-- **Target 3 (b)** at the red in-edge `Pb` of `x`, `(c, t') = (true, true)`: the twisted edge is the blue out-edge `G̊_{x v1}`; `lanlw` at the frame. -/
example :
    ∫ ω, G1.val (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, baSum ((BAGraph.lanlwTerms (G1.twist true true) (lwSymmTwistP true true Pb)).map (BAGraph.twist true true))
        (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) :=
  (baTwistFormE_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 G1 BASymm1Inst.ℓ0 true true).2.1
    Pb Pb_mem rfl rfl

/-- **Target 3 (c)** at the transposed red pair `Ḡ̊_{v1 x}`, `Ḡ̊_{x v0}` (`p = Pb`, `q = Qc`), `(c, t') = (true, true)`: after the twist the pair is the blue
`G̊_{x v1}`, `G̊_{v0 x}` (an out- and an in-edge of `x`); `GGGamma` (`gg2`, `gg4`) at the frame. -/
example :
    ∫ ω, G1.val (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, baSum (((G1.twist true true).gg2 (lwSymmTwistP true true Pb) (lwSymmTwistP true true Qc)).map (BAGraph.twist true true))
          (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 +
        baSum (((G1.twist true true).gg4 (lwSymmTwistP true true Pb) (lwSymmTwistP true true Qc)).map (BAGraph.twist true true))
          (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) :=
  (baTwistFormE_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 G1 BASymm1Inst.ℓ0 true true).2.2
    Pb Pb_mem Qc Qc_mem rfl rfl rfl rfl rfl

/-- The frame lists of the instances are nonempty: `lanlw` has `1 + |lwSplit Pb.2| = 4` terms, `lw2` has `4`, `gg2` has `5 + |lwSplit Qc.2| = 7`. -/
example : ((BAGraph.lanlwTerms (G1.twist true true) (lwSymmTwistP true true Pb)).map (BAGraph.twist true true)).length = 4 ∧
    (((G1.twist true true).lw2 (lwSymmTwistP true true Pa)).map (BAGraph.twist true true)).length = 4 ∧
    (((G1.twist true true).gg2 (lwSymmTwistP true true Pb) (lwSymmTwistP true true Qc)).map (BAGraph.twist true true)).length = 7 := by
  refine ⟨rfl, rfl, rfl⟩

/-- **Target 4** at `G1`: the twisted outputs keep the counters, the order and the monotonicity data. -/
example := ba_twist_inv_out true true G1
example := baTwist_lanlw_ord true true G1 Pb Pb_mem rfl rfl
example := baTwist_lanlw_scalingOrderG true true G1 Pb Pb_mem rfl rfl G1_normal
example := baTwist_lw_raw true true G1 Pa Pa_mem rfl rfl
example := baTwist_lw_mono true true G1 Pa Pa_mem rfl rfl
example := baTwist_lw_scalingOrderG true true G1 Pa Pa_mem rfl rfl G1_normal
example := baTwist_gg_raw true true G1 Pb Qc Pb_mem Qc_mem
example := baTwist_gg_mono true true G1 Pb Qc Pb_mem Qc_mem
example := baTwist_gg_scalingOrderG true true G1 Pb Qc Pb_mem Qc_mem G1_normal

/-- The orders at the instance: `ord G1 = 8`, so every twisted term of `lanlw` has `ord = 9` (`baTwist_lanlw_ord` and `G1_counts`). -/
example : ∀ Δ ∈ (BAGraph.lanlwTerms (G1.twist true true) (lwSymmTwistP true true Pb)).map (BAGraph.twist true true), Δ.scalingOrder = 9 := by
  intro Δ hΔ
  rw [baTwist_lanlw_ord true true G1 Pb Pb_mem rfl rfl Δ hΔ, G1_counts.2]
  norm_num

end BASymm2Inst

end RBM.Graph

end
