/-
T2265 (LW-14e) check file: merged names (section 1), the pin texts of the targets (section 2), drafts of the
downstream LW-14f pins (section 3, NOT targets of T2265), instance shapes (section 4).
No proofs, no `sorry`, no `by`.  Compiles on `main` (20de014) as is.
-/
import RBM3D.Graph.LWExpTerm3
import RBM3D.Graph.LWExpTerm4
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWVocab
import RBM3D.Graph.ScalingOrder
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.LWPins
import RBM3D.Defs.Semicircle
import RBM3D.Green.IBPPoly
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step6Pins
import RBM3D.Induction.ExpIntIQ
import RBM3D.Induction.ExpEtermsA
import RBM3D.Induction.ExpDuhamel
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ExpIntEasy
import RBM3D.Induction.ExpIntII
import RBM3D.Induction.ExpWardII

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## Section 1. Merged names (each in the namespace of its enclosing `namespace … end` block) -/

-- `Graph/LWExpTerm3.lean` (T2255, 20de014, `namespace RBM.Gauss.Sizes` `:48-2224`)
#check @RBM.Gauss.Sizes.LWG5Graph
#check @RBM.Gauss.Sizes.LWG5Data
#check @RBM.Gauss.Sizes.LWAttached
#check @RBM.Gauss.Sizes.LWG5Expand
#check @RBM.Gauss.Sizes.LwGraphPrec1
#check @RBM.Gauss.Sizes.lwGraphPrec1
#check @RBM.Gauss.Sizes.lwExpTerm3_bridge
#check @RBM.Gauss.Sizes.LwExpG5'OfExpand
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand
#check @RBM.Gauss.Sizes.lwCutExp_of_expand
#check @RBM.Gauss.Sizes.lwTermEXP_of_expand
#check @RBM.Gauss.Sizes.lwExpTerm3_T4pos
#check @RBM.Gauss.Sizes.lwExpTerm3_T4zero
#check @RBM.Gauss.Sizes.lwExpTerm3_val_zero
#check @RBM.Gauss.Sizes.lwExpTerm3_val_ext_ne
#check @RBM.Gauss.Sizes.lwExpTerm3_Data_G
#check @RBM.Gauss.Sizes.lwExpTerm3_Data_M
#check @RBM.Gauss.Sizes.lwExpTerm3_Sp_decay
#check @RBM.Gauss.Sizes.lwExpTerm3_entry_whp
#check @RBM.Gauss.Sizes.lwExpTerm3_X_norm_le
-- `Graph/LWExpTerm4.lean` (T2254, 3a3ed6a, `namespace RBM.Gauss.Sizes` `:48-1720`)
#check @RBM.Gauss.Sizes.lwExpI1K_holds
#check @RBM.Gauss.Sizes.lwExpI23K_holds
#check @RBM.Gauss.Sizes.lwExpI41K_holds
#check @RBM.Gauss.Sizes.lwCutExp_of_G5'
-- `Graph/LWExpTerm2.lean` (T2243, d6ebc39, `namespace RBM.Gauss.Sizes` `:63-2053`)
#check @RBM.Gauss.Sizes.LWExpG5'
#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.Gauss.Sizes.lwCutExp_of_terms
-- `Graph/LWExpTerm.lean` (T2236, 23d83c4, `namespace RBM.Gauss.Sizes` `:43-1210`)
#check @RBM.Gauss.Sizes.LWCutExp
#check @RBM.Gauss.Sizes.lwTermEXP_of_cut
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
-- `Graph/LWPins.lean` (975f4ff; `LWtermEXP` in `namespace RBM.Gauss.Sizes` `:187-503`, instance in `RBM.Gauss.LWInst` `:578-676`)
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.LWInst.inst_LWtermEXP
-- `Graph/LWGGExp.lean` (T2120, 5c69cb4, `namespace RBM.Graph` `:56-1748`)
#check @RBM.Graph.oe2x_graph_E
#check @RBM.Graph.oe2xR1
#check @RBM.Graph.oe2xR1d
#check @RBM.Graph.oe2xR1_val
#check @RBM.Graph.oe2xR2
#check @RBM.Graph.oe2xR4
#check @RBM.Graph.oe2xR5
#check @RBM.Graph.oe2xR6
#check @RBM.Graph.oe2xR7
#check @RBM.Graph.oe2xR8
#check @RBM.Graph.oe2xR1_counters
#check @RBM.Graph.oe2xR2_counters
#check @RBM.Graph.oe2xR4_counters
#check @RBM.Graph.oe2xR5_counters
#check @RBM.Graph.oe2xR6_counters
#check @RBM.Graph.oe2xR7_counters
#check @RBM.Graph.oe2xR8_counters
#check @RBM.Graph.oe2xR1_nM_ge
#check @RBM.Graph.oe2xR2_nM_ge
#check @RBM.Graph.oe2xR1_ord
#check @RBM.Graph.oe2xR2_ord
#check @RBM.Graph.oe2xR4_ord
#check @RBM.Graph.oe2xR5_ord
#check @RBM.Graph.oe2xR6_ord
#check @RBM.Graph.oe2xR7_ord
#check @RBM.Graph.oe2xR8_ord
-- `Graph/LWWeightExp.lean` (T2107, 975f4ff, `namespace RBM.Graph` `:51-1507`)
#check @RBM.Graph.owxT1
#check @RBM.Graph.owxDE
#check @RBM.Graph.LGraph.owxExt
#check @RBM.Graph.lwWx_im_pos
#check @RBM.Graph.lwWx_mE_ne
#check @RBM.Graph.lwWx_flow
-- `Graph/LWStein.lean` (T2060, 89f29cf, `namespace RBM.Graph` `:82-1894`)
#check @RBM.Graph.lwSplit
#check @RBM.Graph.lwSplus_spec
#check @RBM.Graph.lwSampleData
#check @RBM.Graph.lwS
#check @RBM.Graph.lwSplus
-- `Graph/LWVocab.lean` (T2050, 37db678, `namespace RBM.Graph` `:67-2559`)
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.DEdge
#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.term
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LGraph.mol
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.nS
#check @RBM.Graph.LGraph.nW
#check @RBM.Graph.LGraph.nV
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.relabel
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.lwSplitLoops
#check @RBM.Graph.LGraph.splitWeights
#check @RBM.Graph.LGraph.val_splitWeights
#check @RBM.Graph.LGraph.dotChoices
#check @RBM.Graph.LGraph.withDots
#check @RBM.Graph.LGraph.merge
#check @RBM.Graph.LGraph.partitionTerms
#check @RBM.Graph.LGraph.mergeSplitP
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.val_eq_partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.PGraph
#check @RBM.Graph.PGraph.val
#check @RBM.Graph.PGraph.val_of_factor
#check @RBM.Graph.PGraph.val_of_not
#check @RBM.Graph.LGraph.pack
#check @RBM.Graph.LGraph.pack_val
#check @RBM.Graph.LComb.val
-- `Graph/ScalingOrder.lean` (3c07bc8, `namespace RBM.Graph` `:44-118`)
#check @RBM.Graph.ord
-- `Graph/AuxGraph.lean` (T2170, 87cf70c, `namespace RBM.Graph`): why F2 is not covered
#check @RBM.Graph.LWGtoAG
#check @RBM.Graph.lwGtoAG_holds
#check @RBM.Graph.LWScalemole
#check @RBM.Graph.lwScalemole_holds
-- `Defs/Semicircle.lean` (fbc9870, `namespace RBM` `:30-381`)
#check @RBM.mE
#check @RBM.norm_mE
-- `Green/IBPPoly.lean` (3b8c687, `namespace RBM.Green` `:49-1157`)
#check @RBM.Green.gaussIBP
-- Step 6 consumers of `LWtermEXP` (for LW-14f; all other inputs are proved)
-- `Induction/ExpIntIQ.lean` (T2257, 193512b, `namespace RBM.Gauss.Sizes` `:66-1365`)
#check @RBM.Gauss.Sizes.stStep6I_of_LW
-- `Induction/Step6Kit.lean` (T2211, 9e0d6a7, `namespace RBM.Gauss.Sizes` `:711-1030`)
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins
-- `Induction/Step6Pins.lean` (T2204, cda3bb2, `namespace RBM.Gauss.Sizes` `:38-155`)
#check @RBM.Gauss.Sizes.STStep6I
#check @RBM.Gauss.Sizes.STStep6II
#check @RBM.Gauss.Sizes.STStep6III
-- `Induction/ExpEtermsA.lean` (cd6fcba), `ExpDuhamel` (1fb83da), `ExpAvg` (d0d79ce), `ExpIntEasy` (cc4d165),
-- `ExpIntII` (f6650b2), `ExpWardII` (e64e4f0); all `namespace RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.stExpLKLKHi_holds
#check @RBM.Gauss.Sizes.stExpDuhamelZ_holds
#check @RBM.Gauss.Sizes.stImproveExpAver_holds
#check @RBM.Gauss.Sizes.stExpIntIII_holds
#check @RBM.Gauss.Sizes.stExpIntII_holds
#check @RBM.Gauss.Sizes.stExpWardII_holds

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

namespace T2265Check

/-! ## Section 2. Pin texts (the file `RBM3D/Graph/LWExpTerm5.lean` states them verbatim without the suffix `Pin`) -/

/-- Target 1 (vocabulary): **a joined packed graph**: the two external vertices are distinct, lie in one molecule,
and there is no internal molecule (finding F2: outputs of the dotted partition in which the internal molecule
`M₀ ∋ α, γ, β` absorbs both `x` and `y`, e.g. `α = x`, `β = y` with the waved `S_{xy}`). -/
def LWJoinedPin (P : PGraph (Fin 2)) : Prop :=
  P.ext 0 ≠ P.ext 1 ∧ P.g.molOf (Sum.inl (P.ext 0)) = P.g.molOf (Sum.inl (P.ext 1)) ∧ P.g.nM = 0

/-- Target 2: **`(eq:sizeGammamu_E)` with the expansion `𝔼 𝒢_xy = Σ_μ 𝔼 Γ_μ`** (`B:78-108`), primed successor of
`LWG5Expand` (`LWExpTerm3.lean:1781`): the coefficient of a graph is `c · m^j · m̄^{j'}` (`c` in the graph's
`coeff`, `E`-independent; finding F1: red weights `Ḡ_{xx}` split into `m̄`), and each graph has distinct external
molecules **or** is joined (finding F2). -/
def LWG5Expand'Pin (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List ((ℕ × ℕ) × PGraph (Fin 2)),
    (∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
        ((∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∨ LWJoinedPin q.2) ∧
        (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) ∧
    ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
      (x y : Idx d (sz.L n) (sz.W n)),
      ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        ((Ls k s).map fun q =>
          (mE E) ^ q.1.1 * star (mE E) ^ q.1.2 *
            ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-! ## Section 3. Drafts of the LW-14f pins (NOT targets of T2265; for the LW-14f drafter) -/

/-- LW-14f: **`(Gammamuxy)` for a joined graph** (`q = 0`, one molecule containing both external vertices):
the analogue of `LwGraphPrec1` (`LWExpTerm3.lean:1430`) without `ξ` (pathwise: waved spanning tree,
`W^{-d} ≤ (𝔡⁻² + 1) B` by `STBctl_ge`). -/
def LwGraphPrecJoinPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t →
        ∀ P : PGraph (Fin 2), P.g.Normal → LWJoinedPin P →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p _ => ‖∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖)
            (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
              (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))

/-- LW-14f: the consumer (copy of `lwExpTerm3_T4pos` + `lwExpG5'_of_expand` with `‖m^j m̄^{j'}‖ = 1`). -/
def LwExpG5'OfExpand'Pin (d : ℕ) : Prop := LWG5Expand'Pin d → LwGraphPrecJoinPin d → LWExpG5' d

/-! ## Section 4. Instance shapes (`d = 3`; Prop-valued, no proof obligations) -/

example : Prop := LWG5Expand'Pin 3
example (P : PGraph (Fin 2)) : Prop := LWJoinedPin P
example : Prop := LWG5Expand 3
example : Prop := LwGraphPrecJoinPin 3
example : Prop := LwExpG5'OfExpand'Pin 3
example : Prop := LWtermEXP 3

end T2265Check

end RBM.Gauss.Sizes
