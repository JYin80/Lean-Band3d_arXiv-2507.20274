/-
Release check for T2450 (dispatcher V3, Mon Oct 12 11:56 UTC 2026; DECISIONS §263).  BA-L L4d2b `Graph/BAS3Close`, `BAS3CloseB`: the S3 roots
(`MERGED` = `T3C-tr_0 + D1X`, `T3C-tr_1`, `D2X`), their root lists and expansion identity, the fold leaf class `BAFoldLeaf`
(over the merged `twLoop2X`, in the frame of `twFold2Prec`), the 14 reductions, the factor bound of #17/#47, and the closure
"`BAG5LeafProps` ∨ fold" with its packed form (supervisor 0851 Q2, S3A-C5, Q3; 0554 Q2; 0655 O3 (A); Fable
`docs/claude-team/fable/2026-10-12-s3-fold-A.md` §1, §3, §4, §5; `docs/reports/T2433-prove.md` §(a⁗)).
Section 1: merged names only.  Section 2: the targets as Prop pins.  The roots `rM r1 rD`, the root lists `ER` and the stuck
catalogue `St` enter as variables (as `L2X` in T2445-check); their bodies are pinned by `T2450_*_eq` and, for the catalogue's anchor,
by the value pin `T2450_stuck0_val`.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2450-check.lean
-/
import RBM3D.Graph.BAG5Leaf
import RBM3D.BA.TwistFold2B
import RBM3D.Graph.BAExp14bB
import RBM3D.BA.FlowPins
import RBM3D.BA.Ward
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenStab
import RBM3D.BA.GreenLDE
import RBM3D.BA.EMn2BA
import RBM3D.BA.Prop5Short
import RBM3D.BA.Prop6Path
import RBM3D.Graph.LWExpSound
import RBM3D.Graph.LWExpTerm6

-- Section 1: merged names
-- L4e-C generic half (T2433, `Graph/BAG5Leaf`): the leaf pins, `BACtx`, the Lemma, the selector, instances
#check @RBM.Graph.BAG5Tgt
#check @RBM.Graph.BAG5Leaf
#check @RBM.Graph.BAG5Expand
#check @RBM.Graph.BAG5Attached
#check @RBM.Graph.BAG5LeafProps
#check @RBM.Graph.BACtx
#check @RBM.Graph.BAG5CtxLemma
#check @RBM.Graph.BAG5CtxKids
#check @RBM.Graph.baG5CtxLemma_holds
#check @RBM.Graph.baG5CtxKids_holds
#check @RBM.Graph.BAselStar
#check @RBM.Graph.baselStar_spec
#check @RBM.Graph.baselStar_eq_none_iff
#check @RBM.Graph.BAG5LeafInst.instCtx
#check @RBM.Graph.BAG5LeafInst.baAllMP
#check @RBM.Graph.BAG5LeafInst.baAllM_leaf
-- L4d (T2419, `Graph/BAExpandId`): the procedure, the step identity, the identity of `baG5Graph` (the twin of target 1)
#check @RBM.Graph.baG5Graph
#check @RBM.Graph.BAG5Identity
#check @RBM.Graph.BARCand
#check @RBM.Graph.BARCand.kids
#check @RBM.Graph.BARCand.kids_normal
#check @RBM.Graph.BARCand.kids_identity
#check @RBM.Graph.BASel
#check @RBM.Graph.BAstep
#check @RBM.Graph.BAexpand
#check @RBM.Graph.BAexpandRoot
#check @RBM.Graph.baExpandIdentity_holds
#check @RBM.Graph.BAExpandId_ggL2
#check @RBM.Graph.BAExpandId_ggL4
#check @RBM.Graph.BAExpandIdInst.baExpandId_inst_identity
#check @RBM.Graph.BAExpandInst.baSelf_zero
#check @RBM.Gauss.Sizes.expandG
#check @RBM.Gauss.Sizes.expandG_sum
-- vocabulary (`Graph/LWVocab`, `Graph/BAVocab`) and the counters of the GG step (`Graph/BAGGOp`)
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.BAMEdge
#check @RBM.Graph.BALData
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAGraph.val
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.packMerge
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.val_eq_partition
#check @RBM.Graph.BAGraph.partition_normal
#check @RBM.Graph.BAGraph.partition_of_normal
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.gg_counters
#check @RBM.Graph.gg_raw
#check @RBM.Graph.gg_mono
#check @RBM.Graph.gg_scalingOrderG
-- the graph data of the flow (`Graph/BAExpand`, `Graph/BAExpandW`) and the expansions the roots come from (T2433 (a⁗) (a))
#check @RBM.Graph.BAlwData
#check @RBM.Graph.BAlwG
#check @RBM.Graph.BAlwGc
#check @RBM.Graph.BAlwM
#check @RBM.Graph.BAlwS
#check @RBM.Graph.BAlwMp
#check @RBM.Graph.BAlwW
#check @RBM.Graph.BAGGGammaR
#check @RBM.Graph.BAlanlwR
-- L4b1 (T2434, `Graph/BAExp14b*`): S3, its families and frame, the identity, the carrier entries, ties, loops, the slice
#check @RBM.BA.BAExp14bS3
#check @RBM.BA.BAExp14bS3Fam
#check @RBM.BA.BAExp14b_FS3
#check @RBM.BA.BAExp14b_FD1X
#check @RBM.BA.BAExp14b_FD2X
#check @RBM.BA.BAExp14b_FT3CX
#check @RBM.BA.BAExp14b_outerDX
#check @RBM.BA.BAExp14bExpand
#check @RBM.BA.baExp14b_expand_holds
#check @RBM.BA.BAExp14b_MB
#check @RBM.BA.BAExp14b_om
#check @RBM.BA.BAExp14b_kap
#check @RBM.BA.BAExp14b_pt
#check @RBM.BA.BAExp14b_sum_blk
#check @RBM.BA.BAExp14b_M_pt
#check @RBM.BA.BAExp14b_S_pt
#check @RBM.BA.BAExp14b_Wk_pt_true
#check @RBM.BA.BAExp14b_Wk_blk
#check @RBM.BA.BAExp14b_twTie
#check @RBM.BA.BAExp14b_twTie_ba
#check @RBM.BA.BAExp14b_L2_eq
#check @RBM.BA.BAExp14a_slc
#check @RBM.BA.BAExp14a_int_slice
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_tailG
-- L4d2a (T2445, `BA/TwistFold2*`): the fold, the `≺` row, the weight of root term #2 at the instance
#check @RBM.BA.twBlk
#check @RBM.BA.twShift
#check @RBM.BA.twChg
#check @RBM.BA.twLoopX
#check @RBM.BA.twMB
#check @RBM.BA.twMB_ba
#check @RBM.BA.twLoop2X
#check @RBM.BA.twLoop2X_trace
#check @RBM.BA.twFold2_holds
#check @RBM.BA.twFold2_bound_holds
#check @RBM.BA.twMrow_le_holds
#check @RBM.BA.twMblk_le_holds
#check @RBM.BA.twB0_ge_holds
#check @RBM.BA.twEta_ge_holds
#check @RBM.BA.twFold2Prec
#check @RBM.BA.twFold2Prec_holds
#check @RBM.BA.twFold2PrecDet
#check @RBM.BA.twFold2PrecDet_holds
#check @RBM.BA.TwistFold2_rho2
#check @RBM.BA.TwistFold2_rho2_bounds
#check @RBM.BA.TwistFold2_one_prec
-- the carrier, `≺`, the stochastic premises (registered owed, `Test/Axioms.lean:133, 144`), the flow
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFMz
#check @RBM.BA.BAmF
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
-- the merged deterministic bounds for `r₁, r₂` (S3A-C5 (b)): `M`-Ward, symmetry, shift, ℓ¹ rows, `ρ₂`, the short range of `Θ^{(σσ)}`
#check @RBM.BA.BASelf
#check @RBM.BA.BAReal
#check @RBM.BA.BAMB
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMB_row_sq_real
#check @RBM.BA.BAMB_symm
#check @RBM.BA.BAMB_shift
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.baM_row_l1
#check @RBM.BA.baM_col_l1
#check @RBM.BA.baM_rho2
#check @RBM.BA.BATheta
#check @RBM.BA.baTheta_row_le
#check @RBM.BA.baTheta_col_le
#check @RBM.BA.BAProp5s
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.BAProp5to8
#check @RBM.BA.baProp5to8_holds
-- the band's packed forms and their consumer (twins of target 5 and of L4g)
#check @RBM.Gauss.Sizes.LWG5ExpandSplit
#check @RBM.Gauss.Sizes.LWG5Expand'
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand'
-- the `d = 3` instance data (`Defs/Sizes.lean` §Inst, `BA/FlowPins.lean` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

-- Section 2: the targets (Prop pins) and shapes
noncomputable section

namespace RBM.Graph.T2450Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-! ### Target 2: the fold leaf class -/

/-- Target 2 (`BAFoldLeaf`; 0851 Q2 `:126-131`, Q3 `:134-150`: a separate `Prop` predicate, averaged form; Fable §1, §3, §4).
`q` is a fold leaf if there are a tail charge `σ`, a flag `e` (the random 2-loop factor of #17, #47) and an explicit block
weight `ρ` with (i) at the carrier `baFMz sz z` and the slice `BAExp14a_slc`, pathwise, for `0 ≤ t ≤ T₀` and every block pair
`(a, b)` (also `a = b`): `W^{-2d} Σ_{x∈[a], y∈[b]} q(x, y) = twLoop2X Ǧ Ǧ (Ǧ E_b Ǧ(σ)) (ρ · X^e) a`, with
`X(c₂, c₄) = W^d Tr(E_{c₂} Ǧ E_{c₄} Ǧ) = W^{-d} Σ_{u∈[c₂], v∈[c₄]} Ǧ_{uv} Ǧ_{vu}` (the closing edge circled; `C` and the frame
as in `twFold2Prec`); (ii) `r₁ = max_{c₁} Σ_{c₂c₃c₄} |ρ| ≤ Cρ`, `r₂ = max_{c₄} Σ_{c₁c₂c₃} |ρ| ≤ Cρ`, eventually in `n`, uniformly
in `t ∈ [0, T₀]` and `(a, b)` (the hypothesis shape of `twFold2Prec`, `twFold2PrecDet`). -/
def T2450_BAFoldLeaf (q : BAPGraph (Fin 2)) : Prop :=
  ∃ (σ e : Bool) (ρ : ∀ (d : ℕ) (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → Zd d (sz.L n) → Zd d (sz.L n) →
      Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y] =
          twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
            (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
              ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
            (fun c₁ c₂ c₃ c₄ => ρ d sz z n t a b c₁ c₂ c₃ c₄ *
              (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
                (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a) ∧
    (∀ (d : ℕ), 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
      BAFlow sz κ ε 𝔠 𝔡 z → ∃ Cρ : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
        ∀ a b : Zd d (sz.L n), (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ))

/-- Target 2, transfer (`baFoldLeaf_congr`): the class depends on `q` only through its value. -/
def T2450_foldCongr : Prop :=
  ∀ q q' : BAPGraph (Fin 2),
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι), q.val D ℓ = q'.val D ℓ) →
      T2450_BAFoldLeaf q → T2450_BAFoldLeaf q'

/-- Target 3′ (`BAS3Xprec`; 0851 S3A-C5 (b): "`X(c₂,c₃) ≺ W^d·Bctl` from `STLmaxgL`, `k = 2`"; Fable §4): the factor of #17, #47 in
the hypothesis shape of `twFold2Prec` (index `q = (p, c₁, c₂, c₃, c₄)`, the factor reads `(c₂, c₄)`), from the two premises of
`twFold2Prec` (registered owed; inside this statement only). -/
def T2450_BAS3Xprec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      PrecL sz (Sizes.seqP (sz.withLam 0))
        (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n q ω => ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n q.2.2.1, ∑ v ∈ twBlk n q.2.2.2.2,
          (baFMz sz z).GM n (t n) ω u v * (baFMz sz z).GM n (t n) ω v u‖)
        (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n))

/-- The consumers (0851 Q3 `:146-149`): fold leaves enter L4c1, L4g through `twFold2PrecDet` (`e = false`) or `twFold2Prec` with
target 3′ (`e = true`); the S3 pin they prove.  Elaboration check only. -/
example : Prop := BAExp14bS3 3 ∧ twFold2PrecDet 3 ∧ twFold2Prec 3 ∧ T2450_BAS3Xprec 3 ∧ T2450_foldCongr

/-! ### Target 1 (roots, root lists, identity), target 4 (closure), target 5 (packed form) -/

section Roots

-- the roots `MERGED` (`T3C-tr_0 + D1X`), `T3C-tr_1`, `D2X` at the tail charge `s`; the root lists of a selector and a fuel
variable (rM : Bool → BAGraph (Fin 2) (Fin 4)) (r1 : Bool → BAGraph (Fin 2) (Fin 6)) (rD : Bool → BAGraph (Fin 2) (Fin 4))
  (ER : BASel → ℕ → Fin 3 → Bool → List (BAPGraph (Fin 2)))

/-- Target 1, root `MERGED` (T2433-prove `:170-177`, supervisor 0554 F1 item 2; `x = inl 0`, `y = inl 1`, `iJ = inr J`;
`i0..i3 = w, γ, δ, v`): `G(x,i0) G(i2,y) G(i3,i2) G(i1,i3)` and the tail `G(y,x)` (`s = true`) or `Ḡ(x,y)` (`s = false`), all
uncircled; black `S(i1,i2)`, `S(i0,i3)` (the block identity `W^{-d} 1[v ∈ [w]] = S_{wv}/t`, F1); `M(i0,i1)`; coefficient `1`
(root value `= t ×` S3 integrand). -/
def T2450_rootM_eq : Prop :=
  ∀ s : Bool, rM s =
    ({ solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
          SEdge.mk true false (Sum.inr 3) (Sum.inr 2), SEdge.mk true false (Sum.inr 1) (Sum.inr 3),
          if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
        waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 0) (Sum.inr 3)],
        dotted := [], coeff := 1, psi := [],
        mdot := [BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)] } : BAGraph (Fin 2) (Fin 4))

/-- Target 1, root `T3C-tr_1` (T2433-prove `:170-177`; `i0..i5 = α, b, w, γ, δ, v`): `Ǧ(x,i2)` circled, `G(i4,y) G(i5,i4) G(i3,i5)`,
the tail; `S⁺(i1,i2)` (coloured), black `S(i3,i4)`, `S(i0,i5)`; `M(i0,i1) M(i1,i0)` (`M⁺`), `M(i2,i3)`; coefficient `1`. -/
def T2450_root1_eq : Prop :=
  ∀ s : Bool, r1 s =
    ({ solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 2), SEdge.mk true false (Sum.inr 4) (Sum.inl 1),
          SEdge.mk true false (Sum.inr 5) (Sum.inr 4), SEdge.mk true false (Sum.inr 3) (Sum.inr 5),
          if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
        waved := [WEdge.mk true true (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 3) (Sum.inr 4),
          WEdge.mk false false (Sum.inr 0) (Sum.inr 5)],
        dotted := [], coeff := 1, psi := [],
        mdot := [BAMEdge.mk true (Sum.inr 0) (Sum.inr 1), BAMEdge.mk true (Sum.inr 1) (Sum.inr 0),
          BAMEdge.mk true (Sum.inr 2) (Sum.inr 3)] } : BAGraph (Fin 2) (Fin 6))

/-- Target 1, root `D2X` (T2433-prove `:170-177`; `i0..i3 = α, α', v, β`): `G(i3,i0) G(i2,i3) G(i1,i2)`, the tail; black
`S(i1,i3)`, `S(i0,i2)`; `M(x,i1)`, `M(i0,y)`; coefficient `1`. -/
def T2450_rootD_eq : Prop :=
  ∀ s : Bool, rD s =
    ({ solid := [SEdge.mk true false (Sum.inr 3) (Sum.inr 0), SEdge.mk true false (Sum.inr 2) (Sum.inr 3),
          SEdge.mk true false (Sum.inr 1) (Sum.inr 2),
          if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
        waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 3), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)],
        dotted := [], coeff := 1, psi := [],
        mdot := [BAMEdge.mk true (Sum.inl 0) (Sum.inr 1), BAMEdge.mk true (Sum.inr 0) (Sum.inl 1)] } : BAGraph (Fin 2) (Fin 4))

/-- Target 1, the root lists (`BAS3expandRoot`, twin of `BAexpandRoot`, `BAExpandId.lean:379`): index `0 = MERGED`, `1 = T3C-tr_1`,
`2 = D2X`; the partition of the root, each term expanded, the exponent pairs dropped. -/
def T2450_expandRoot_eq : Prop :=
  ∀ (sel : BASel) (fuel : ℕ) (s : Bool),
    ER sel fuel 0 s = (rM s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd) ∧
    ER sel fuel 1 s = (r1 s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd) ∧
    ER sel fuel 2 s = (rD s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd)

/-- Target 1, the identity statement (`BAS3Identity`, twin of `BAG5Identity`, `BAExpandId.lean:89`): for lists `Ls r s`, the
expectation identity `𝔼 root = Σ_μ 𝔼 Γ_μ` at `BAlwData` over `PF d L W 0`, `BASelf`, `0 ≤ t < 1`, for the three roots. -/
def T2450_BAS3Identity (d : ℕ) (Ls : Fin 3 → Bool → List (BAPGraph (Fin 2))) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (s : Bool) (x y : Idx d L W),
      (∫ ω, (rM s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
          ((Ls 0 s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum) ∧
        (∫ ω, (r1 s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
          ((Ls 1 s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum) ∧
        (∫ ω, (rD s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
          ((Ls 2 s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum)

/-- Target 1, the identity theorem (`baS3Identity_holds`, twin of `baExpandIdentity_holds`, `BAExpandId.lean:589`): every selector,
every fuel. -/
def T2450_identity : Prop := ∀ (d : ℕ) (sel : BASel) (fuel : ℕ), T2450_BAS3Identity rM r1 rD d (ER sel fuel)

/-- Target 4 (`BAS3Close`; 0851 S3A-C5 (c), Q3 `:138`): every output of the three trees, both charges, under `BAselStar` at fuel 2,
is a leaf with the five properties of `BAG5LeafProps` or a fold leaf (`x ~ y` included: `BAG5Tgt` carries it). -/
def T2450_BAS3Close : Prop :=
  ∀ (r : Fin 3) (s : Bool), ∀ q ∈ ER BAselStar 2 r s, BAG5LeafProps (fun _ _ => [q]) ∨ T2450_BAFoldLeaf q

/-- Target 5 (`BAS3Expand'`; 0554 Q2 "the packaged twin of `BAG5Expand'`"; twin of `LWG5ExpandSplit`, `LWExpSound.lean:50`): the form
L4c1, L4g and the producer of `BAExp14bS3` consume. -/
def T2450_BAS3Expand' (d : ℕ) : Prop :=
  ∃ Ls : Fin 3 → Bool → List (BAPGraph (Fin 2)),
    (∀ (r : Fin 3) (s : Bool), ∀ q ∈ Ls r s, BAG5LeafProps (fun _ _ => [q]) ∨ T2450_BAFoldLeaf q) ∧
      T2450_BAS3Identity rM r1 rD d Ls

/-- Targets 4, 5 as theorems (shapes). -/
example : Prop := T2450_BAS3Close ER ∧ ∀ d : ℕ, T2450_BAS3Expand' rM r1 rD d

/-- Target 6, shapes: the identity at the data of `baExpandId_inst_identity` (`d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`,
`t = 1/2`, `m = i`); the lists are nonempty and both disjuncts of target 4 occur in the list of `MERGED` at `s = false`. -/
example : Prop := T2450_BAS3Identity rM r1 rD 3 (ER BAselStar 2)

example : Prop :=
  (∀ (r : Fin 3) (s : Bool), ER BAselStar 2 r s ≠ []) ∧
    (∃ q ∈ ER BAselStar 2 0 false, BAG5LeafProps (fun _ _ => [q])) ∧ (∃ q ∈ ER BAselStar 2 0 false, T2450_BAFoldLeaf q)

end Roots

/-! ### Target 3: the 14 reductions, both charges -/

section Stuck

-- the stuck catalogue: `St k j s` is stuck node `j` of `T3C-tr_k` at the tail charge `s`, packed over `Fin` (`ext = id`), in the
-- order of `stuck_one.py` (T2433-prove `:246-262`): `j = 0` root term #2, `j = 1..6` kids #1, #2, #17, #22, #47, #52;
-- `s = false` replaces the circled tail `Ǧ(y,x)` by `\bar{Ǧ}(x,y)` (`stuck_cmp.py`, `:264-266`)
variable (St : Bool → Fin 7 → Bool → BAPGraph (Fin 2))

/-- Target 3, the anchor of the catalogue, as a value (`BAFoldLeaf` reads `q` only through `q.val`, target 2 transfer): root term #2
of `T3C-tr_0` (T2433-prove `:247`; Fable §1: `Ǧ_{xw} M_{wγ} Ǧ_{γv} M_{vδ} Ǧ_{δy} · tail`, `S_{wv}`, `S_{γδ}`; `i0..i3 = w, γ, δ, v`),
tail `Ǧ(y,x)` (`s = true`) or `\bar{Ǧ}(x,y)` (`s = false`), all solid edges circled. -/
def T2450_stuck0_val : Prop :=
  ∀ (s : Bool) {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι),
    (St false 0 s).val D ℓ =
      ({ solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 2) (Sum.inl 1),
            SEdge.mk true true (Sum.inr 1) (Sum.inr 3),
            if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)],
          waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 0) (Sum.inr 3)],
          dotted := [], coeff := 1, psi := [],
          mdot := [BAMEdge.mk true (Sum.inr 3) (Sum.inr 2), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)] } :
        BAGraph (Fin 2) (Fin 4)).val D ℓ

/-- Target 3 (`baS3Fold_holds`; 0851 S3A-C5 (a), (b)): every catalogue graph, both roots, both charges, is a fold leaf, with the
explicit `ρ` of the 1a table (Fable §4, corrected; the six kids of `T3C-tr_1` derived in the 1a). -/
def T2450_reductions : Prop := ∀ (k : Bool) (j : Fin 7) (s : Bool), T2450_BAFoldLeaf (St k j s)

example : Prop := T2450_stuck0_val St ∧ T2450_reductions St

end Stuck

end RBM.Graph.T2450Check

end
