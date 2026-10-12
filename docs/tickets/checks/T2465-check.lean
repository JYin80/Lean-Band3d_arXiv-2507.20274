/-
Release check for T2465 (dispatcher V3, Mon Oct 12 17:08 UTC 2026; DECISIONS §271).  BA-L L4g `Graph/BAExp14e`: the joined-graph bound `BAGraphPrecJoin`
(T2398 probe `t/T2398:RBM3D/Probe/T2398Pins.lean:444-452`, band `LwGraphPrecJoin`), the leaf pin `BAG5LeafPrec` of T2464 proved (the
`n_M = 0` half here, the `n_M = 1` half from L4c2 = T2466), and the merged pin `BAExp14bS3` through T2464's `baExp14bS3_of_leaf`
(supervisor 0851 Q3, 0554 Q2, 0951 L4-C7, 0655 Q1; designs T2398 §5, §7, T2387 §6; the cut of DECISIONS §271).
Section 1: merged names only (`main` a1412ad).  Section 2: the targets as Prop pins and shapes.  T2464 and T2466 are not merged:
`T2465_BAG5LeafPrec` copies T2464's pin `T2464_BAG5LeafPrec` (`docs/tickets/checks/T2464-check.lean:338-347`) verbatim up to the name;
the target pins take the leaf pin (`LP`) and the `n_M = 1` statement of T2466 (`Q1`) as parameters; `T2465_Q1Need` is the weakest `Q1`
read.  No proofs.
Run: lake env lean docs/tickets/checks/T2465-check.lean
-/
import RBM3D.Graph.BAS3CloseC
import RBM3D.Graph.BASizeClaim2
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.BA.LWPinsBA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWExpTerm6

-- Section 1: merged names
-- L4e-C (T2433, `Graph/BAG5Leaf`): the leaf properties (the hypothesis of `BAG5LeafPrec`), the all-`M` leaf (`n_M = 0`)
#check @RBM.Graph.BAG5Tgt
#check @RBM.Graph.BAG5Leaf
#check @RBM.Graph.BAG5Attached
#check @RBM.Graph.BAG5LeafProps
#check @RBM.Graph.BAG5LeafInst.baAllMP
#check @RBM.Graph.BAG5LeafInst.baAllM_leaf
-- L4d2b (T2450, `Graph/BAS3Close*`): the closure that T2464's assembly reads (read only here)
#check @RBM.Graph.BAS3expandRoot
#check @RBM.Graph.baS3Close_mod
#check @RBM.Graph.BAS3Close
#check @RBM.Graph.baS3Close_holds
#check @RBM.Graph.BAS3Expand'
#check @RBM.Graph.baS3Expand'_holds
-- the vocabulary and the graph data of the flow (`Graph/BAVocab`, `Graph/BAExpand`, `Graph/BAExpandW`)
#check @RBM.Graph.BAGraph
#check @RBM.Graph.BAPGraph
#check @RBM.Graph.BAPGraph.val
#check @RBM.Graph.BAPGraph.scalingOrder
#check @RBM.Graph.BAGraph.mol
#check @RBM.Graph.BAGraph.nM
#check @RBM.Graph.BAGraph.nW
#check @RBM.Graph.BAGraph.Normal
#check @RBM.Graph.BAGraph.scalingSize
#check @RBM.Graph.BALData
#check @RBM.Graph.BAlwData
#check @RBM.Graph.BAlwS
#check @RBM.Graph.BAlwW
#check @RBM.Graph.BAlwM
#check @RBM.Graph.baW_mul
-- L3c2 (T2412, `Graph/BASizeClaim*`): `claim:size` at BA (target 1's pathwise step) and the kernel bounds of the model
#check @RBM.Graph.baClaimSize
#check @RBM.Graph.baClaimSize_E
#check @RBM.Graph.BAGraph.sizeConst
#check @RBM.Graph.baKBound_E
#check @RBM.Graph.LWKBound
-- the merged parts of T2466's `n_M = 1` route (read, not proved here): `GtoAG`, `ζ`, the entrywise `Ψ`, the L3d1 pin
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.BAGbyZeta
#check @RBM.Graph.baGbyZeta_holds
#check @RBM.Graph.BAEntryPsi
#check @RBM.Graph.BAAnpAuxG
-- L4b1, L4a (`Graph/BAExp14b*`, `Graph/BAExp14a*`): S3 (target 3), S1, S2, the identity; the slice, `≺ → 𝔼`, floor, scalars, `W − 1`
#check @RBM.BA.BAExp14bS3
#check @RBM.BA.BAExp14bS3Fam
#check @RBM.BA.BAExp14bS2
#check @RBM.BA.BAExp14bExpand
#check @RBM.BA.baExp14b_expand_holds
#check @RBM.BA.BAExp14aS1
#check @RBM.BA.baExp14a_S1_holds
#check @RBM.BA.BAExp14a_slc
#check @RBM.BA.BAExp14a_int_slice
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_floor
#check @RBM.BA.BAExp14a_eta_inv_le
#check @RBM.BA.BAExp14a_Bctl_le_two
#check @RBM.BA.BAExp14a_eventual_scalars
#check @RBM.BA.BAExp14a_W_sub_one
#check @RBM.BA.BAExp14a_theta_l1
-- L4d2a (T2445, `BA/TwistFold2`): S3A-C2, S3A-C3
#check @RBM.BA.twB0_ge
#check @RBM.BA.twB0_ge_holds
#check @RBM.BA.twEta_ge
#check @RBM.BA.twEta_ge_holds
-- the carrier, `≺`, the five Step 1/2 pins (inside statement defs only), the flow, the scale facts
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
#check @RBM.BA.BAmF
#check @RBM.BA.ba_G_data
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BASelf
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.expAvg_Bctl_ge
-- the consumers of target 3: the BA terminal pin (L6, V1-BA)
#check @RBM.BA.baPin
#check @RBM.BA.BALWtermEXP
-- the band twins: `LWExpTerm6` §1–§4 (target 1), the one-line chain (target 3), §5–§6 (T2464, mapped out); `LWExpTerm3` helpers
#check @RBM.Gauss.Sizes.LwGraphPrecJoin
#check @RBM.Gauss.Sizes.lwExpTerm6_pathwise
#check @RBM.Gauss.Sizes.lwExpTerm6_arith
#check @RBM.Gauss.Sizes.lwGraphPrecJoin_holds
#check @RBM.Gauss.Sizes.lwExpTerm6_T4pos
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand'
#check @RBM.Gauss.Sizes.lwExpG5'_holds
#check @RBM.Gauss.Sizes.lwCutExp_holds
#check @RBM.Gauss.Sizes.lwTermEXP_holds
#check @RBM.Gauss.Sizes.stStep6I_holds
#check @RBM.Gauss.Sizes.stStep6II_holds
#check @RBM.Gauss.Sizes.stStep6III_holds
#check @RBM.Gauss.Sizes.LwGraphPrec1
#check @RBM.Gauss.Sizes.lwGraphPrec1
#check @RBM.Gauss.Sizes.lwExpTerm3_Sp_decay
#check @RBM.Gauss.Sizes.lwExpTerm3_val_norm_le
#check @RBM.Gauss.Sizes.lwExpTerm3_floor
#check @RBM.Gauss.Sizes.lwExpTerm3_etaT_le_one
-- the `d = 3` instance data (`Defs/Sizes.lean` §Inst, `BA/FlowPins.lean` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

-- Section 2: the targets (Prop pins) and shapes
noncomputable section

namespace RBM.BA.T2465Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-! ### Target 1: the joined bound -/

/-- Target 1 (`BAGraphPrecJoin`; T2398 probe `:444-452`, design §5; band `LwGraphPrecJoin`, `LWExpTerm6.lean:55`): for a normal packed
BA graph with `n_M = 0` (every vertex in a molecule of an external vertex), `‖𝔼 Γ_{xy}‖ ≺ t^{n_W} η_t⁻¹ (W^{-d} B_{t,0})^{ord/2}` at every
pair `(x, y)`, from the entrywise law alone.  The data are those of T2464's `BAG5LeafPrec` (`BAExp14a_slc`, `(baFMz sz z).m n`); the probe
text is definitionally the same (`BAExp14a_slc sz n ω = Sizes.slice (sz.withLam 0) n ω`,
`(baFMz sz z).m n = BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n`). -/
def T2465_BAGraphPrecJoin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → ∀ P : BAPGraph (Fin 2), P.g.Normal → P.g.nM = 0 →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂(Sizes.seqP (sz.withLam 0))‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- Target 1 for every `d`, and the instance shape (the all-`M` leaf of L4e-C is normal with `n_M = 0`). -/
example : Prop := (∀ d : ℕ, T2465_BAGraphPrecJoin d) ∧ BAG5LeafInst.baAllMP.g.Normal ∧ BAG5LeafInst.baAllMP.g.nM = 0

/-! ### Target 2: T2464's leaf pin, proved from the two halves -/

/-- T2464's leaf pin `BAG5LeafPrec` (T2464 target 5 (a); `T2464_BAG5LeafPrec`, `T2464-check.lean:338-347`), copied verbatim up to the
name, so that the shapes below elaborate before T2464 merges.  At release the scratch check of the 1b uses `RBM.BA.BAG5LeafPrec` itself;
a difference is stop rule S3. -/
def T2465_BAG5LeafPrec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- The `n_M = 1` half this row reads (not a target here; owner T2466 = L4c2, band §3 `:384-1228`, `:1426-1661`): `BAG5LeafPrec`
restricted to leaves with `n_M = 1`.  It is the weakest form target 2 needs; T2466's exported statement must imply it (stop rule S2). -/
def T2465_Q1Need (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) → P.g.nM = 1 →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- Target 2, the conditional form (`baG5LeafPrec_of`): the joined bound (the `n_M = 0` half) and the `n_M = 1` statement `Q1` give the
leaf pin `LP` (`LP := BAG5LeafPrec` of T2464, `Q1 :=` T2466's statement, both fixed at release). -/
def T2465_LeafPrecOf (Q1 LP : ℕ → Prop) (d : ℕ) : Prop := T2465_BAGraphPrecJoin d → Q1 d → LP d

/-- Target 2 (shapes): the conditional form at the copied pin and the weakest `Q1`, and the unconditional `baG5LeafPrec_holds`. -/
example : Prop := (∀ d : ℕ, T2465_LeafPrecOf T2465_Q1Need T2465_BAG5LeafPrec d) ∧ (∀ d : ℕ, T2465_BAG5LeafPrec d)

/-! ### Target 3: the producer of S3 through T2464's assembly -/

/-- Target 3 (`baExp14bS3_holds`), shape: T2464's assembly `baExp14bS3_of_leaf : ∀ d, BAG5LeafPrec d → BAExp14bS3 d` (T2464 target 6,
`T2464_S3OfLeaf`) applied to target 2 gives the merged pin `BAExp14bS3` (`Graph/BAExp14b.lean:181`, five premises) for every `d`. -/
example : Prop :=
  (∀ d : ℕ, T2465_BAG5LeafPrec d → BAExp14bS3 d) → (∀ d : ℕ, T2465_BAG5LeafPrec d) → ∀ d : ℕ, BAExp14bS3 d

/-- The consumers of target 3 (shapes): the L4a2 assembly reads S1 (proved), S2 (L4b2), S3 and the expansion identity (proved); the BA
terminal pin (L6, V1-BA) follows through the L4a2 assembly and reduction. -/
example : Prop := BAExp14aS1 3 ∧ BAExp14bS2 3 ∧ BAExp14bS3 3 ∧ BAExp14bExpand 3 ∧ BALWtermEXP 3

/-! ### Target 4: instance shapes at `d = 3` -/

example : Prop :=
  T2465_BAGraphPrecJoin 3 ∧ BAG5LeafProps (fun _ _ => [BAG5LeafInst.baAllMP]) ∧ T2465_BAG5LeafPrec 3 ∧ BAExp14bS3 3

end RBM.BA.T2465Check

end
