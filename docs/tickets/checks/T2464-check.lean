/-
Release check for T2464 (dispatcher V3, Mon Oct 12 16:38 UTC 2026; DECISIONS §271).  BA-L L4c1 `Graph/BAExp14c`, `BAExp14cB`: the sub-root
`T3C-tr_0` of `MERGED`, the bridge "S3 family = t⁻¹ × root average" for the four families, the `≺ → 𝔼` kit of a BA graph
value (the moved part of band §3), the `t`-carrying fold class, the averaged leaf bound under the disjunction of supervisor
0851 Q3 with the `x ~ y` support, and the conditional assembly `BAG5LeafPrec d → BAExp14bS3 d` (0851 Q3, S3A-C4; 0554 Q2;
0951 Q3, L4-C8; design T2398 §5, §7; T2387 §6).
Section 1: merged names only.  Section 2: the targets as Prop pins.  The sub-root `rT0` (the 1b's `baS3RootT0`) enters as a
variable; its body is pinned in `T2464_rootT0_eq` (as `rM` in T2450-check).  No proofs.
Run: lake env lean docs/tickets/checks/T2464-check.lean
-/
import RBM3D.Graph.BAS3CloseC
import RBM3D.Graph.BAAtom
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWExpTerm6

-- Section 1: merged names
-- L4d2b (T2450, `Graph/BAS3Close*`): the roots, the lists, the identity, the fold class, the catalogue, the closure
#check @RBM.Graph.baS3RootM
#check @RBM.Graph.baS3Root1
#check @RBM.Graph.baS3RootD
#check @RBM.Graph.BAS3expandRoot
#check @RBM.Graph.BAS3Identity
#check @RBM.Graph.baS3Identity_holds
#check @RBM.Graph.BAFoldLeaf
#check @RBM.Graph.baFoldLeaf_congr
#check @RBM.Graph.baS3Stuck
#check @RBM.Graph.baS3Fold_holds
#check @RBM.Graph.baS3Stuck0_val
#check @RBM.Graph.baS3Close_mod
#check @RBM.Graph.BAS3Close
#check @RBM.Graph.baS3Close_holds
#check @RBM.Graph.BAS3Expand'
#check @RBM.Graph.baS3Expand'_holds
#check @RBM.Graph.BAS3Xprec
#check @RBM.Graph.baS3Xprec_holds
#check @RBM.Graph.BAS3CloseInst.baS3_inst_close
#check @RBM.Graph.BAS3CloseInst.baS3_inst_expand'
-- L4e-C generic half (T2433, `Graph/BAG5Leaf`): the leaf predicates and the selector; the procedure (L4d)
#check @RBM.Graph.BAG5Tgt
#check @RBM.Graph.BAG5Leaf
#check @RBM.Graph.BAG5Attached
#check @RBM.Graph.BAG5LeafProps
#check @RBM.Graph.BAselStar
#check @RBM.Graph.BASel
#check @RBM.Graph.BAexpand
-- vocabulary (`Graph/LWVocab`, `Graph/BAVocab`) and the graph data of the flow (`Graph/BAExpand`, `Graph/BAExpandW`)
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.BAMEdge
#check @RBM.Graph.BALData
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAGraph.val
#check @RBM.Graph.BAGraph.term
#check @RBM.Graph.BAGraph.atom
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.splitG
#check @RBM.Graph.BAGraph.partition
#check @RBM.Graph.BAGraph.val_eq_partition
#check @RBM.Graph.baSplitSolid
#check @RBM.Graph.BAComb.val
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAlwData
#check @RBM.Graph.BAlwS
#check @RBM.Graph.BAlwW
#check @RBM.Graph.BAlwM
-- L3c1, L3c3a (`Graph/BAAtom*`, `Graph/BAAuxGraph2*`): atoms are offset-diagonal (the `x ~ y` support); the `GtoAG` and `ζ`
-- inputs of the producers of the leaf pin (L4c2)
#check @RBM.Graph.baAtom_offset
#check @RBM.Graph.BAAtom_offdiag_E
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_E
#check @RBM.Graph.BAGbyZeta
#check @RBM.Graph.baGbyZeta_holds
#check @RBM.Graph.baZeta_ward_sum
#check @RBM.Graph.baZetaVar
-- L4b1 (T2434, `Graph/BAExp14b*`): S3, its families and frame, the expansion identity
#check @RBM.BA.BAExp14bS3
#check @RBM.BA.BAExp14bS3Fam
#check @RBM.BA.BAExp14b_FS3
#check @RBM.BA.BAExp14b_FD1X
#check @RBM.BA.BAExp14b_FD2X
#check @RBM.BA.BAExp14b_FT3CX
#check @RBM.BA.BAExp14b_outerDX
#check @RBM.BA.BAExp14b_dX
#check @RBM.BA.BAExp14bExpand
#check @RBM.BA.baExp14b_expand_holds
-- L4a (T2418, `Graph/BAExp14a*`): the slice, `W^{(k)}`, the `≺` calculus, the floor, the scalars, continuity
#check @RBM.BA.BAExp14a_slc
#check @RBM.BA.BAExp14a_int_slice
#check @RBM.BA.BAExp14a_tail
#check @RBM.BA.BAExp14a_Wk
#check @RBM.BA.BAExp14a_W_sub_one
#check @RBM.BA.BAExp14a_theta_l1
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_prec_fin
#check @RBM.BA.BAExp14a_prec_of_le_ev
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_floor
#check @RBM.BA.BAExp14a_Bctl_le_two
#check @RBM.BA.BAExp14a_eta_inv_le
#check @RBM.BA.BAExp14a_eventual_scalars
#check @RBM.BA.BAExp14a_GM_le
#check @RBM.BA.BAExp14a_cont_G
#check @RBM.BA.BAExp14a_cont_GM
#check @RBM.BA.BAExp14a_integrable
-- L4d2a (T2445, `BA/TwistFold2*`): the fold, the `≺` rows, S3A-C2, S3A-C3
#check @RBM.BA.twBlk
#check @RBM.BA.twChg
#check @RBM.BA.twLoop2X
#check @RBM.BA.twFold2Prec
#check @RBM.BA.twFold2Prec_holds
#check @RBM.BA.twFold2PrecDet
#check @RBM.BA.twFold2PrecDet_holds
#check @RBM.BA.twB0_ge
#check @RBM.BA.twB0_ge_holds
#check @RBM.BA.twEta_ge
#check @RBM.BA.twEta_ge_holds
-- the carrier, `≺`, the five Step 1/2 pins (other gates'), the flow, the scalar facts of `Bctl`
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.FlowFM.eta
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.baFMz
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BASelf
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Gauss.Sizes.expAvg_Bctl_ge
-- the band basis (`Graph/LWExpTerm3`: §2 bridge, §3 kit `:1229-1425` and the `q ≤ 1` pin, §4 assembly) and L4g's band file
#check @RBM.Gauss.Sizes.LwExpTerm3Bridge
#check @RBM.Gauss.Sizes.lwExpTerm3_bridge
#check @RBM.Gauss.Sizes.lwExpTerm3_lwS_zero
#check @RBM.Gauss.Sizes.lwExpTerm3_val_zero
#check @RBM.Gauss.Sizes.lwExpTerm3_val_norm_le
#check @RBM.Gauss.Sizes.lwExpTerm3_floor
#check @RBM.Gauss.Sizes.lwExpTerm3_etaT_le_one
#check @RBM.Gauss.Sizes.lwExpTerm3_X_norm_le
#check @RBM.Gauss.Sizes.lwExpTerm3_poly
#check @RBM.Gauss.Sizes.LwGraphPrec1
#check @RBM.Gauss.Sizes.lwGraphPrec1
#check @RBM.Gauss.Sizes.lwExpTerm3_pairsum
#check @RBM.Gauss.Sizes.lwExpTerm3_val_ext_ne
#check @RBM.Gauss.Sizes.lwExpTerm3_graph_pair_bound
#check @RBM.Gauss.Sizes.lwExpTerm3_T4pos
#check @RBM.Gauss.Sizes.lwExpTerm3_T4zero
#check @RBM.Gauss.Sizes.LWG5Expand
#check @RBM.Gauss.Sizes.LwExpG5'OfExpand
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand
#check @RBM.Gauss.Sizes.LWExpG5'
#check @RBM.Gauss.Sizes.LwGraphPrecJoin
#check @RBM.Gauss.Sizes.LWG5Expand'
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand'
-- the `d = 3` instance data (`Defs/Sizes.lean` §Inst, `BA/FlowPins.lean` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

-- Section 2: the targets (Prop pins) and shapes
noncomputable section

namespace RBM.Graph.T2464Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-! ### Target 1 (the sub-root of `T3C-tr_0`) and target 2 (the bridge) -/

section Root

-- the sub-root `T3C-tr_0` at the tail charge `s` (the 1b's `baS3RootT0`)
variable (rT0 : Bool → BAGraph (Fin 2) (Fin 4))

/-- Target 1, the sub-root `T3C-tr_0` (T2433-prove `:171`; `x = inl 0`, `y = inl 1`, `iJ = inr J`, `i0..i3 = w, γ, δ, v`): the data
of `baS3RootM` with the first solid edge circled, `Ǧ(x,i0) G(i2,y) G(i3,i2) G(i1,i3)` and the tail `G(y,x)` (`s = true`) or
`Ḡ(x,y)` (`s = false`); black `S(i1,i2)`, `S(i0,i3)`; `M(i0,i1)`; coefficient `1`. -/
def T2464_rootT0_eq : Prop :=
  ∀ s : Bool, rT0 s =
    ({ solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
          SEdge.mk true false (Sum.inr 3) (Sum.inr 2), SEdge.mk true false (Sum.inr 1) (Sum.inr 3),
          if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)],
        waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 2), WEdge.mk false false (Sum.inr 0) (Sum.inr 3)],
        dotted := [], coeff := 1, psi := [],
        mdot := [BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)] } : BAGraph (Fin 2) (Fin 4))

/-- Target 1, inclusion of the partitions: every term of the sub-root's partition is a term of `MERGED`'s (the circled child of
`G(x,i0)` in the first step of `baSplitSolid`). -/
def T2464_rootT0_sub : Prop :=
  ∀ s : Bool, ∀ P ∈ (rT0 s).partition, P ∈ (baS3RootM s).partition

/-- Target 1, inclusion of the expanded lists: every output of the sub-root's expansion is an output of `MERGED`'s list (index `0`
of `BAS3expandRoot`), so the closure of L4d2b classifies it. -/
def T2464_rootT0_list : Prop :=
  ∀ (sel : BASel) (fuel : ℕ) (s : Bool),
    ∀ q ∈ (rT0 s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd), q ∈ BAS3expandRoot sel fuel 0 s

/-- Target 1, the identity of the sub-root (twin of `BAS3Identity` for one root): `𝔼 root = Σ_μ 𝔼 Γ_μ` at `BAlwData` over
`PF d L W 0`, `BASelf`, `0 ≤ t < 1`, every selector and fuel. -/
def T2464_rootT0_identity (d : ℕ) : Prop :=
  ∀ (sel : BASel) (fuel : ℕ) (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ),
    BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 → ∀ (s : Bool) (x y : Idx d L W),
      ∫ ω, (rT0 s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        (((rT0 s).partition.flatMap (fun P => (BAexpand sel fuel P).map Prod.snd)).map fun q =>
          ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum

/-- Target 2 (`BAS3Bridge`; 0554 Q2 `:173`: "the S3 integrands = Σ root values"; band `LwExpTerm3Bridge`, `LWExpTerm3:336`):
pathwise at the carrier `baFMz sz z` and the slice `BAExp14a_slc`, for `0 ≤ t ≤ T₀`, every `ω`, tail charge `σ` and block pair
`(a, b)` (also `a = b`), `t ×` the fine-sum family of `BAExp14b` is the `[a]×[b]` average of the root value at `BAlwData`:
`T3C-tr_0` (sub-root), `D1X + T3C-tr_0` (`MERGED`), `T3C-tr_1`, `D2X`.  The factor `t` is the black edge `S_{wv} = t W^{-d} 1[v ∈ [w]]`
of the root (T2433-prove `:184-196`, T2450-prove S5). -/
def T2464_BAS3Bridge (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (σ : Bool) (a b : Zd d (sz.L n)),
      ((t : ℂ) * BAExp14b_FT3CX sz z n t ω false σ a b =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (rT0 σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y]) ∧
      ((t : ℂ) * (BAExp14b_FD1X sz z n t ω σ a b + BAExp14b_FT3CX sz z n t ω false σ a b) =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3RootM σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y]) ∧
      ((t : ℂ) * BAExp14b_FT3CX sz z n t ω true σ a b =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3Root1 σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y]) ∧
      ((t : ℂ) * BAExp14b_FD2X sz z n t ω σ a b =
          ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
            (baS3RootD σ).val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
              (BAExp14a_slc sz n ω)) ![x, y])

/-- Targets 1, 2, shapes at `d = 3`. -/
example : Prop :=
  T2464_rootT0_eq rT0 ∧ T2464_rootT0_sub rT0 ∧ T2464_rootT0_list rT0 ∧ T2464_rootT0_identity rT0 3 ∧ T2464_BAS3Bridge rT0 3

/-- Target 7, shape: the sub-root's partition is nonempty for both tail charges. -/
example : Prop := ∀ s : Bool, (rT0 s).partition ≠ []

end Root

/-! ### Target 3: the `≺ → 𝔼` kit of a BA graph value (band `LWExpTerm3:1229-1425`) -/

/-- Target 3, values at `t = 0` (twin of `lwExpTerm3_val_zero`, `LWExpTerm3:1241`): a graph with a waved edge vanishes at
`BAlwData` with `t = 0` (`BAlwS 0 = 0`, `S⁺ = S W`). -/
def T2464_val_zero : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (ω : sz.SeqΩ) (P : BAPGraph (Fin 2)), P.g.nW ≠ 0 →
    ∀ ℓ : Fin 2 → Idx d (sz.L n) (sz.W n),
      P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) 0 ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ℓ = 0

/-- Target 3, the envelope (twin of `lwExpTerm3_val_norm_le`, `lwExpTerm3_X_norm_le`, `lwExpTerm3_poly`,
`LWExpTerm3:1279, 1374, 1417`): for every packed BA graph a polynomial envelope `t^{n_W} N^K`, eventually in `n`, uniformly in
`0 ≤ t ≤ T₀`, the sample and the labels. -/
def T2464_val_env : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ P : BAPGraph (Fin 2), ∃ K : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
      ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
        ‖P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![x, y]‖ ≤ t ^ P.g.nW * ((sz.size n : ℕ) : ℝ) ^ K

/-! ### Target 4: the `t`-carrying fold class -/

/-- Target 4 (`BAFoldLeafT`): `BAFoldLeaf` (`BAS3CloseC:965`) with the weight `t · ρ` in clause (i) and the uniform `ℓ¹` bounds
`r₁, r₂ ≤ Cρ` on `ρ` in clause (ii).  The S3 integrand is `t⁻¹ ×` the root average (target 2); the weights of L4d2b are
`BAS3Close_rho (2 + qq) = t · BAS3Close_rho (1 + qq)` (`BAS3CloseC:780-784`). -/
def T2464_BAFoldLeafT (q : BAPGraph (Fin 2)) : Prop :=
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
            (fun c₁ c₂ c₃ c₄ => (t : ℂ) * ρ d sz z n t a b c₁ c₂ c₃ c₄ *
              (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
                (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a) ∧
    (∀ (d : ℕ), 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
      BAFlow sz κ ε 𝔠 𝔡 z → ∃ Cρ : ℝ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
        ∀ a b : Zd d (sz.L n), (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
          (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ d sz z n t a b c₁ c₂ c₃ c₄‖ ≤ Cρ))

/-- Target 4, transfer (`baFoldLeafT_congr`): the class depends on `q` only through its value. -/
def T2464_foldTCongr : Prop :=
  ∀ q q' : BAPGraph (Fin 2),
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι), q.val D ℓ = q'.val D ℓ) →
      T2464_BAFoldLeafT q → T2464_BAFoldLeafT q'

/-- Target 4, the class refines L4d2b's (`baFoldLeafT_fold`). -/
def T2464_foldT_weaken : Prop := ∀ q : BAPGraph (Fin 2), T2464_BAFoldLeafT q → BAFoldLeaf q

/-- Target 4, the catalogue (`baS3FoldT_holds`): the 14 stuck graphs, both roots `T3C-tr_k`, both tail charges. -/
def T2464_foldT_cat : Prop := ∀ (k : Bool) (j : Fin 7) (s : Bool), T2464_BAFoldLeafT (baS3Stuck k j s)

/-- Target 4, the closure with the `t`-carrying class (`BAS3CloseT`; from `baS3Close_mod`, `BAS3CloseB:827`): every output of the
three lists at `BAselStar`, fuel `2`, both tail charges, is a `BAG5LeafProps` leaf or a `BAFoldLeafT` leaf. -/
def T2464_BAS3CloseT : Prop :=
  ∀ (r : Fin 3) (s : Bool), ∀ q ∈ BAS3expandRoot BAselStar 2 r s, BAG5LeafProps (fun _ _ => [q]) ∨ T2464_BAFoldLeafT q

/-! ### Target 5: the analytic leaf bound under the disjunction of 0851 Q3 -/

/-- Target 5, the `x ~ y` support (`BAExp14c_xy_support`; the BA form of the `x = y` case of `lwExpTerm3_val_ext_ne`,
`LWExpTerm3:1797`): if the external vertices lie in one atom, the value at `BAlwData` vanishes at labels of different offsets
(`baAtom_offset`, `BAAtom_offdiag_E`), so only `W^d` of the `W^{2d}` pairs of `[a]×[b]` contribute. -/
def T2464_xy_support : Prop :=
  ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (P : BAPGraph (Fin 2)),
      P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1)) →
      ∀ x y : Idx d (sz.L n) (sz.W n), (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
        P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
          (BAExp14a_slc sz n ω)) ![x, y] = 0

/-- Target 5 (a), the leaf pin (`BAG5LeafPrec`; statement only, owed to L4c2 and L4g; twin of `LwGraphPrec1`,
`LWExpTerm3:1430`, and of the probe's `BAGraphPrecJoin`, T2398 probe `:444`): for every `P` with the leaf properties of
`BAG5LeafProps` and every pair `(x, y)`, `‖𝔼 P_{xy}‖ ≺ t^{n_W} η_t⁻¹ Bctl^{ord(P)/2}` at `BAlwData` over the carrier law, under the
five premises of `BAExp14bS3`. -/
def T2464_BAG5LeafPrec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- Target 5 (b) (`BAS3LeafAvg`; supervisor 0851 Q3 `:146-149`, binding): given the leaf pin and the five premises, every
`q` that is a `BAG5LeafProps` leaf or a `BAFoldLeafT` leaf has `‖𝔼 W^{-2d} Σ_{x∈[a], y∈[b]} q_{xy}‖ ≺ t (1 - t)⁻¹ Bctl^{5/2}`,
uniformly in the block pair `(a, b)`.  A `BAG5LeafProps` leaf goes through `GtoAG`/`(Gammamuxy)` pointwise (the pin, per pair)
and is then averaged, with the `x ~ y` support; a fold leaf goes through L4d2a directly, in averaged form (`twFold2PrecDet`,
or `twFold2Prec` with `baS3Xprec_holds`; `𝔼` through `BAExp14a_prec_integral`; the factor `t` restored afterwards). -/
def T2464_BAS3LeafAvg (d : ℕ) : Prop :=
  T2464_BAG5LeafPrec d →
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ q : BAPGraph (Fin 2), (BAG5LeafProps (fun _ _ => [q]) ∨ T2464_BAFoldLeafT q) →
        PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p _ => ‖∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n p.1, ∑ y ∈ twBlk n p.2,
              q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
                (BAExp14a_slc sz n ω)) ![x, y]) ∂μ‖)
          (fun n _ _ => t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))

/-! ### Target 6: the conditional assembly of the merged pin S3 -/

/-- Target 6 (`BAExp14bS3OfLeaf`; 0554 Q2 "the assembly"; band `LwExpG5'OfExpand`, `LWExpTerm3:2029`): the leaf pin gives the
merged S3 pin `BAExp14bS3` (`BAExp14b:181`, per family, five premises), unchanged. -/
def T2464_S3OfLeaf (d : ℕ) : Prop := T2464_BAG5LeafPrec d → BAExp14bS3 d

/-! ### Shapes -/

/-- Targets 3–6, shapes at `d = 3`. -/
example : Prop :=
  T2464_val_zero ∧ T2464_val_env ∧ T2464_foldTCongr ∧ T2464_foldT_weaken ∧ T2464_foldT_cat ∧ T2464_BAS3CloseT ∧
    T2464_xy_support ∧ T2464_BAS3LeafAvg 3 ∧ T2464_S3OfLeaf 3

/-- Target 7, shape: both disjuncts of target 4 occur in the list of `MERGED` at `s = false`. -/
example : Prop :=
  (∃ q ∈ BAS3expandRoot BAselStar 2 0 false, BAG5LeafProps (fun _ _ => [q])) ∧
    (∃ q ∈ BAS3expandRoot BAselStar 2 0 false, T2464_BAFoldLeafT q)

-- Target 7, shape: the conditional at the `d = 3` data (`sz0`, `zSeq`, `t ≡ 1/2`); the leaf pin and the Step 1/2 pins (other
-- gates') stay hypotheses.
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst in
example : Prop :=
  T2464_S3OfLeaf 3 → STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) →
    STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) → T2464_BAG5LeafPrec 3 → BAExp14bS3 3

end RBM.Graph.T2464Check

end
