/-
Release check for T2303 (dispatcher V1, Thu Oct  8 02:05 UTC 2026, revised from the draft of Tue Oct  6 14:00 UTC 2026;
CLAUDE.md §4 step 0; DECISIONS §129 (1), §128, §98 (2), §102, §105 (5), §57 (1), §57 (3), §29, §20, §17, §16).
BA-L2b1 (block Anderson graph expansion; T2161 split P.9; BA-L2b cut in two by §129 (1)): `RBM3D/Graph/BAExpandW.lean`,
the pin `BAlweight` (`paper/tex/B_graphical_lemmas.tex:376-387`, `lem_lweight`, [yang2024Del, Lemma B.10]) landed and
proved, and `lanlw` (`B:359-372`) as a graph operation on `BAGraph` with its value identity.  The order bookkeeping
(target 3(c)) and instances (I3)-(I4) are T2315 (`Graph/BAExpandWOrd`).
Section 1: the merged names the file uses (exact namespaces from the enclosing `namespace … end` blocks; file:line,
last commit on `main` 8a0c4cd; unchanged on `main` ae94fa7).
Section 2: the pin, in the temporary namespace `RBM.Graph.T2303Check`; T2303 copies it verbatim into namespace
`RBM.Graph` (source: `t/T2161:RBM3D/Probe/T2161Pins.lean:1394-1406, 1435-1441`, 82e72b3, with `BASelf` qualified
and the probe's garbled `Σ_{α,β}` in the docstring repaired).
Section 3: the graph-operation vocabulary of target 2 and the model data, also copied verbatim.
Section 4: the target statements as `Prop`s (T2303 proves them with these exact texts) and the instance graphs.
Statements, definitions and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2303-check.lean`.
-/
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWVocab
import RBM3D.BA.Ward
import RBM3D.BA.FlowPins
import RBM3D.BA.MFixedPoint
import RBM3D.Gauss.BlockAnderson
import RBM3D.Gauss.FineModel
import RBM3D.Loop.GLoopFlow
import RBM3D.Green.IBPPoly
import RBM3D.Green.LDEQuad
import RBM3D.Defs.Sizes
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! ## 1. Merged names -/

-- T2295 (BA-L2a1, ad9bb6d): `RBM3D/Graph/BAExpand.lean`, namespace `RBM.Graph` (`:48-902`)
#check @RBM.Graph.BAlwH                       -- :60
#check @RBM.Graph.BAlwM                       -- :64
#check @RBM.Graph.BAlwG                       -- :67
#check @RBM.Graph.BAlwGc                      -- :71
#check @RBM.Graph.BAlwS                       -- :75
#check @RBM.Graph.BAlwMp                      -- :78
#check @RBM.Graph.BAlwW                       -- :82
#check @RBM.Graph.BAlwf                       -- :86
#check @RBM.Graph.BAlwdf                      -- :90
#check @RBM.Graph.BAlanlwL                    -- :102
#check @RBM.Graph.BAlanlwR                    -- :106
#check @RBM.Graph.BAlanlw                     -- :117
#check @RBM.Graph.baGm                        -- :148
#check @RBM.Graph.baG                         -- :153
#check @RBM.Graph.dhSample_baG                -- :250
#check @RBM.Graph.dhSample_baG_star           -- :256
#check @RBM.Graph.baG_tame1                   -- :305
#check @RBM.Graph.baVar                       -- :319
#check @RBM.Graph.baPoly                      -- :325
#check @RBM.Graph.baPoly_tame1                -- :339
#check @RBM.Graph.stein_baPoly                -- :354
#check @RBM.Graph.baWx_baG                    -- :378
#check @RBM.Graph.baWx_baPoly                 -- :400
#check @RBM.Graph.baWx_dh                     -- :485
#check @RBM.Graph.BAExpand_defect             -- :512
#check @RBM.Graph.BAExpand_defect_identity    -- :517
#check @RBM.Graph.BAExpand_G_sub_M            -- :554
#check @RBM.Graph.BAExpand_integral_defect    -- :602
#check @RBM.Graph.BAExpand_integral           -- :647 (`lanlw` on `Sizes.seqP`, any `M` with `M_ββ = m`)
#check @RBM.Graph.BAExpand_M_diag             -- :722
#check @RBM.Graph.BAExpand_Gc_zero            -- :731
#check @RBM.Graph.baLanlw_holds               -- :744
#check @RBM.Graph.BAExpandInst.baS_row_sum    -- :793
#check @RBM.Graph.BAExpandInst.baLanlw_t0     -- :800
#check @RBM.Graph.BAExpandInst.baSelf_zero    -- :865

-- T2287 (BA-L1, c230ce5): `RBM3D/Graph/BAVocab.lean`, namespace `RBM.Graph` (`:34-1424`)
#check @RBM.Graph.BALData                     -- :39
#check @RBM.Graph.BAPsiEdge                   -- :43
#check @RBM.Graph.BAMEdge                     -- :48
#check @RBM.Graph.BAGraph                     -- :55
#check @RBM.Graph.BAPsiEdge.map               -- :59
#check @RBM.Graph.BAMEdge.map                 -- :61
#check @RBM.Graph.BAMEdge.val                 -- :68
#check @RBM.Graph.BAGraph.term                -- :72
#check @RBM.Graph.BAGraph.val                 -- :78
#check @RBM.Graph.BAGraph.addM                -- :87
#check @RBM.Graph.BAGraph.atomAdj             -- :92
#check @RBM.Graph.BAGraph.atom                -- :105
#check @RBM.Graph.BAGraph.nA                  -- :110
#check @RBM.Graph.BAGraph.adj                 -- :116
#check @RBM.Graph.BAGraph.mol                 -- :125
#check @RBM.Graph.BAGraph.nM                  -- :130
#check @RBM.Graph.BAGraph.nS                  -- :135
#check @RBM.Graph.BAGraph.nW                  -- :138
#check @RBM.Graph.BAGraph.counters            -- :141
#check @RBM.Graph.BAGraph.scalingOrder        -- :146
#check @RBM.Graph.BAGraph.Normal              -- :158
#check @RBM.Graph.baSplitSolid                -- :163
#check @RBM.Graph.BAGraph.splitG              -- :170
#check @RBM.Graph.BAGraph.packMerge           -- :220
#check @RBM.Graph.BAGraph.partition           -- :229
#check @RBM.Graph.BAGraph.scalingOrderG       -- :234
#check @RBM.Graph.BAGraph.term_addM           -- :254
#check @RBM.Graph.BAGraph.mem_atom_iff        -- :387
#check @RBM.Graph.BAGraph.mem_mol_iff         -- :394
#check @RBM.Graph.BAGraph.nA_le_card          -- :435
#check @RBM.Graph.BAGraph.val_splitG          -- :647
#check @RBM.Graph.BAGraph.splitG_circ         -- :688
#check @RBM.Graph.BAGraph.splitG_edges        -- :697
#check @RBM.Graph.BAGraph.val_eq_partition    -- :919
#check @RBM.Graph.BAGraph.partition_normal    -- :930
#check @RBM.Graph.BAGraph.partition_of_normal -- :1137
#check @RBM.Graph.BAGraph.le_scalingOrderG_iff -- :1154
#check @RBM.Graph.BAGraph.scalingOrderG_of_normal -- :1167
#check @RBM.Graph.BAVocabInst.baLWT1          -- :1201
#check @RBM.Graph.BAVocabInst.baGedge_ordG    -- :1308

-- LW-03 (37db678): `RBM3D/Graph/LWVocab.lean`, namespace `RBM.Graph` (`:67-2559`)
#check @RBM.Graph.LData                       -- :73
#check @RBM.Graph.SEdge                       -- :82
#check @RBM.Graph.WEdge                       -- :89
#check @RBM.Graph.LGraph                      -- :104
#check @RBM.Graph.LGraph.term                 -- :129
#check @RBM.Graph.LGraph.adj                  -- :157
#check @RBM.Graph.SEdge.map                   -- :412
#check @RBM.Graph.Counters                    -- ScalingOrder.lean:49 (3c07bc8)
#check @RBM.Graph.ord                         -- ScalingOrder.lean:65

-- LW-04 (89f29cf): `RBM3D/Graph/LWStein.lean`, namespace `RBM.Graph` (`:82-1894`)
#check @RBM.Graph.owxDefect                   -- :100
#check @RBM.Graph.owx_defect_identity         -- :107 (the band twin of the pathwise solve)
#check @RBM.Graph.dhSample                    -- :521
#check @RBM.Graph.Tame1                       -- :703
#check @RBM.Graph.lwSplit                     -- :891
#check @RBM.Graph.lwS                         -- :998
#check @RBM.Graph.stein_sample                -- :1013
#check @RBM.Graph.lwS_row_sum                 -- :1215
#check @RBM.Graph.owx_integral                -- :1239 (the band twin of target 1)
#check @RBM.Graph.lwSplus                     -- :1308
#check @RBM.Graph.lwS_isUnit                  -- :1313 (Gershgorin, the twin of target 1b)
#check @RBM.Graph.lwSplus_spec                -- :1346
#check @RBM.Graph.LGraph.dTerm                -- :1381 (coefficient `-Γ.coeff`; `lanlwD` has `+Γ.coeff`)
#check @RBM.Graph.lwSampleData                -- :1420 (`lwGm` only: the BA twin is new)
#check @RBM.Graph.lwStein_term_eq             -- :1506

-- LW-05 (975f4ff): `RBM3D/Graph/LWWeightExp.lean`, namespace `RBM.Graph` (`:51-1507`)
#check @RBM.Graph.lwWxSizes                   -- :60
#check @RBM.Graph.lwWx_lwS_apply              -- :281
#check @RBM.Graph.lwWx_integral               -- :330
#check @RBM.Graph.lwWeightExp_holds           -- :407
#check @RBM.Graph.owxEmb                      -- :454
#check @RBM.Graph.LGraph.owxExt               -- :458
#check @RBM.Graph.owxDE                       -- :468
#check @RBM.Graph.LGraph.term_owxExt          -- :474
#check @RBM.Graph.owxDE_val                   -- :487
#check @RBM.Graph.owx_nM_eq                   -- :514
#check @RBM.Graph.owxExt_nM                   -- :591
#check @RBM.Graph.owxT4                       -- :688 (the derivative-term pattern)
#check @RBM.Graph.owxT1_counters              -- :741
#check @RBM.Graph.lwSplit_perm                -- :928
#check @RBM.Graph.owx_integral_list_sum       -- :956
#check @RBM.Graph.owx_sum_fin2                -- :985
#check @RBM.Graph.owxEdgePoly                 -- :1001
#check @RBM.Graph.owx_term_integral           -- :1060
#check @RBM.Graph.owx_graph_E                 -- :1316

-- LW pins (975f4ff): `RBM3D/Graph/LWPins.lean`, namespace `RBM.Graph` (`:53-185`)
#check @RBM.Graph.LWPins_dH                   -- :62
#check @RBM.Graph.LWPins_resPoly              -- :73

-- Stein hypothesis, discharged; `Tame` (namespace `RBM.Green`)
#check @RBM.Green.Tame                        -- LDEQuad.lean:165 (cca94be)
#check @RBM.Green.GaussIBP                    -- LDEQuad.lean:302
#check @RBM.Green.Tame.integrable             -- LDEQuad.lean:312
#check @RBM.Green.gaussIBP                    -- IBPPoly.lean:305 (3b8c687)

-- the model (namespace `RBM.Gauss`)
#check @RBM.Gauss.Idx                         -- Defs/Sizes.lean:46 (0a873f1)
#check @RBM.Gauss.split                       -- Defs/Sizes.lean:64
#check @RBM.Gauss.splitEquiv                  -- Defs/Sizes.lean:87
#check @RBM.Gauss.svarF                       -- Gauss/FineModel.lean:47 (0a873f1)
#check @RBM.Gauss.Ω                           -- :84
#check @RBM.Gauss.PF                          -- :97
#check @RBM.Gauss.Sizes.seqP                  -- :169
#check @RBM.Gauss.Hflow                       -- :437
#check @RBM.Gauss.PsiI                        -- Gauss/BlockAnderson.lean:52 (868b3b4)
#check @RBM.Gauss.ztOf                        -- Loop/GLoopFlow.lean:55 (868b3b4)
#check @RBM.Gauss.Gres                        -- :74
#check @RBM.Gauss.Mres                        -- :81

-- BA deterministic layer (namespace `RBM.BA`)
#check @RBM.BA.BAMB                           -- BA/MFixedPoint.lean:190 (ae63e74)
#check @RBM.BA.BASelf                         -- :193
#check @RBM.BA.BAMB_symm                      -- BA/Ward.lean:83 (b4fb28b)
#check @RBM.BA.BAMB_diag_eq                   -- :89
#check @RBM.BA.BAMB_row_sq_real               -- :125
#check @RBM.BA.BAMres_fine_kron               -- BA/FlowPins.lean:70 (b750bf3)
#check @RBM.BA.BAMres_fine_apply              -- :100

-- Mathlib (root namespace): Gershgorin
#check @det_ne_zero_of_sum_row_lt_diag        -- Mathlib/LinearAlgebra/Matrix/Gershgorin.lean:63
#check @Matrix.isUnit_iff_isUnit_det

/-! ## 2. The pin (copied verbatim by T2303 into namespace `RBM.Graph`) -/

noncomputable section

open MeasureTheory Matrix RBM.Gauss

namespace RBM.Graph.T2303Check

section LWBAPinsW

variable (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ)
  (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)

/-- Left side of `lem_lweight`: `Ǧ_{xx} f` (`B:376-387`, [yang2024Del, Lemma B.10]). -/
noncomputable def BAlweightL (x : Idx d L W) (ω : Ω d L W) : ℂ :=
  BAlwGc d L W g0 E t m ω x x * BAlwf d L W g0 E t m P ω

/-- Right side of `lem_lweight` before `𝔼`: `Σ_y (1 + M^+S^+)_{xy} (Σ_{α,β} M_{yα} S_{αβ} Ǧ_{αy} Ǧ_{ββ} f -
Σ_{α,β} M_{yα} S_{αβ} G_{βy} ∂_{h_{βα}} f)`, with `1 + M^+S^+ = (1 - M^+S)⁻¹ = BAlwW` (`B:380-385`). -/
noncomputable def BAlweightR (x : Idx d L W) (ω : Ω d L W) : ℂ :=
  ∑ y, BAlwW d L W g0 E t m x y *
    (∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω α y *
        BAlwGc d L W g0 E t m ω β β * BAlwf d L W g0 E t m P ω -
      ∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β * BAlwG d L W g0 E t m ω β y *
        BAlwdf d L W g0 E t m P ω β α)

variable {d L W g0 E t m P}

/-- **`lem_lweight`** (`B:376-387`, [yang2024Del, Lemma B.10]): `𝔼[BAlweightL] = 𝔼[BAlweightR]` for every resolvent
polynomial `f` over the BA law `PF d L W 0`.  Needs `(self_m)` (through `lanlw`) and `IsUnit (1 - M^+S)` (from
`BASelf`, `t < 1`: the rows of `M^+S` have absolute sum `≤ t`).  Registry: proved (T2303). -/
def BAlweight (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W),
      ∫ ω, BAlweightL d L W g0 E t m P x ω ∂(PF d L W 0) = ∫ ω, BAlweightR d L W g0 E t m P x ω ∂(PF d L W 0)

end LWBAPinsW

/-! ## 3. `lanlw` as a graph operation: vocabulary (copied verbatim) -/

section ModelData

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The graph data of the BA flow at the sample `ω` (T2287 Consumers): `G` the flow resolvent, `M = BAlwM`,
`S = t·svarF d L W 0`, `S⁺ = S (1 - M^+S)⁻¹`, `gPsi = g₀ Ψ`. -/
noncomputable def BAlwData (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) : BALData (Idx d L W) where
  G := Matrix.of fun x y => BAlwG d L W g0 E t m ω x y
  M := BAlwM d L W g0 E m
  S := Matrix.of (BAlwS d L W t)
  Sp := Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m
  gPsi := (g0 : ℂ) • PsiI d L W

end ModelData

section LanlwGraph

variable {E I : Type}

/-- `Γ` on the vertices `E ⊕ (I ⊕ Fin 2)` (old vertices by `owxEmb 2`, `α = inr (inr 0)`, `β = inr (inr 1)`) with
its solid edges replaced by `rest`, the solid edges `s`, waved edges `w`, `M`-dotted edges `md` appended, the
`Ψ`-dotted edges carried along, and the coefficient multiplied by `c`. -/
def BAGraph.lanlwExt (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (c : ℂ)
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.mk (({ Γ.toLGraph with solid := rest } : LGraph E I).owxExt (owxEmb 2) c s w)
    (Γ.psi.map (BAPsiEdge.map (owxEmb 2))) (md ++ Γ.mdot.map (BAMEdge.map (owxEmb 2)))

/-- **Term 1 of `lanlw`** (`B:363`) for `p ∈ lwSplit Γ.solid` with `p.1 = Ǧ_{xy}` (blue, circled; `x = p.1.src`,
`y = p.1.dst`): `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f`; `coeff = coeff Γ`. -/
def BAGraph.lanlwT1 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.lanlwExt Γ p.2 1
    [⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 2 p.1.dst⟩]
    [⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]
    [⟨true, owxEmb 2 p.1.src, Sum.inr (Sum.inr 0)⟩]

/-- **The derivative term of `lanlw` for the solid edge `q.1` of `f`** (`q ∈ lwSplit p.2`, `B:363`):
`-Σ_{α,β} M_{xα} S_{αβ} G_{βy} ∂_{h_{βα}}` applied to `q.1`, i.e. `q.1` replaced by the two edges of `owxDE β α`
(`G_{ab} ↦ G_{aβ} G_{αb}`, `Ḡ_{ab} ↦ Ḡ_{aα} Ḡ_{βb}`); **`coeff = + coeff Γ`** (the `-` of `lanlw` cancels the `-` of
`∂G = -GG`; T2295-prove (a) row 10). -/
def BAGraph.lanlwD (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.lanlwExt Γ q.2 1
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 1), owxEmb 2 p.1.dst⟩]
    [⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]
    [⟨true, owxEmb 2 p.1.src, Sum.inr (Sum.inr 0)⟩]

/-- **The terms of `lanlw`** at the edge `p.1` of `Γ`: term 1, then one derivative term for each solid edge of
`f` (light-weights, weights and red edges included). -/
def BAGraph.lanlwTerms (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 2)) :=
  BAGraph.lanlwT1 Γ p :: (lwSplit p.2).map (BAGraph.lanlwD Γ p)

end LanlwGraph

/-! ## 4. Target statements (T2303 proves them with these texts) and the instance graphs -/

/-- Target 1b: the fine-lattice Ward row, `Σ_α |M_{xα}|² = 1` (`BAMres_fine_apply` + `BAMB_row_sq_real`). -/
def T2303_baM_row_sq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], ∀ (g0 E : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    ∀ x : Idx d L W, ∑ α, ‖BAlwM d L W g0 E m x α‖ ^ 2 = 1

/-- Target 1b: `1 - M^+S` is invertible (Gershgorin; rows of `M^+S` have absolute sum `≤ t < 1`). -/
def T2303_baW_isUnit : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 → IsUnit (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t))

/-- Target 1c (`baLweight_holds`). -/
def T2303_baLweight_holds : Prop := ∀ d : ℕ, BAlweight d

/-- Target 3(b): the value identity in expectation at the model data. -/
def T2303_lanlw_val : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
      (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true →
      ∀ ℓe : Ex → Idx d L W,
        ∫ ω, Γ.val (BAlwData d L W g0 E t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAlwData d L W g0 E t m ω) ℓe).sum ∂(PF d L W 0)

/-- (I3): `Ǧ_{xy}`, `x, y = inl 0, inl 1` external. -/
def baGcxy : BAGraph (Fin 2) (Fin 0) where
  solid := [⟨true, true, .inl 0, .inl 1⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- (I4): the weight `Ǧ_{xx}`, `x = inr 0` internal. -/
def baGcxx : BAGraph (Fin 0) (Fin 1) where
  solid := [⟨true, true, .inr 0, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- (I5): the pin at `d = 3`. -/
example : Prop := BAlweight 3

end RBM.Graph.T2303Check

end
