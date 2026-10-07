/-
Release check for T2295 (dispatcher V1, Tue Oct  6 12:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §97 (3),
§58 (3), §57 (1), §57 (3), §29, §20, §17, §16).
BA-L2a (block Anderson graph expansion, first of three; T2161 split P.9 `docs/reports/T2161-portmap.md:1045`, `:1103`):
`RBM3D/Graph/BAExpand.lean`, the BA Stein layer, the pin `BAlanlw` (`paper/tex/B_graphical_lemmas.tex:359-372`,
`lanlw`, [yang2024Del, Lemma B.9]) landed and proved, and `lanlw` as a graph operation on `BAGraph` with its order
bookkeeping through `scalingOrderG`.
Section 1: the merged names the file uses (exact namespaces from the enclosing `namespace … end` blocks; file:line,
last commit on `main` 30f7ef8).
Section 2: the vocabulary and the pin, in the temporary namespace `RBM.Graph.T2295Check`; T2295 copies it verbatim into
namespace `RBM.Graph` (source: `t/T2161:RBM3D/Probe/T2161Pins.lean:1340-1427`, 82e72b3, with `BASelf` qualified;
`BAlwMp`, `BAlwW` are shared with BA-L2b/L2c and land here unused).
Section 3: the merged instances BA-L2a reads (no new instance graphs here: the prover builds them, Targets (I1)-(I4)).
Statements, definitions and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2295-check.lean`.
-/
import RBM3D.Graph.BAVocab
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWLvl1
import RBM3D.BA.Ward
import RBM3D.BA.FlowPins
import RBM3D.BA.MFixedPoint
import RBM3D.Gauss.BlockAnderson
import RBM3D.Gauss.FineModel
import RBM3D.Loop.GLoopFlow
import RBM3D.Green.IBPPoly

/-! ## 1. Merged names -/

-- T2287 (BA-L1, c230ce5): `RBM3D/Graph/BAVocab.lean`, namespace `RBM.Graph` (`:34-1424`)
#check @RBM.Graph.BALData                     -- :39
#check @RBM.Graph.BAPsiEdge                   -- :43
#check @RBM.Graph.BAMEdge                     -- :48
#check @RBM.Graph.BAGraph                     -- :55
#check @RBM.Graph.BAMEdge.val                 -- :68
#check @RBM.Graph.BAGraph.term                -- :72
#check @RBM.Graph.BAGraph.val                 -- :78
#check @RBM.Graph.BAGraph.addM                -- :87
#check @RBM.Graph.BAGraph.atom                -- :105
#check @RBM.Graph.BAGraph.nA                  -- :110
#check @RBM.Graph.BAGraph.mol                 -- :125
#check @RBM.Graph.BAGraph.nM                  -- :130
#check @RBM.Graph.BAGraph.counters            -- :141
#check @RBM.Graph.BAGraph.scalingOrder        -- :146
#check @RBM.Graph.BAGraph.Normal              -- :158
#check @RBM.Graph.BAGraph.splitG              -- :170
#check @RBM.Graph.BAGraph.partition           -- :229
#check @RBM.Graph.BAGraph.scalingOrderG       -- :234
#check @RBM.Graph.BAGraph.term_addM           -- :254
#check @RBM.Graph.BAGraph.val_splitG          -- :647
#check @RBM.Graph.BAGraph.splitG_circ         -- :688
#check @RBM.Graph.BAGraph.splitG_edges        -- :697
#check @RBM.Graph.BAGraph.val_eq_partition    -- :919
#check @RBM.Graph.BAGraph.partition_normal    -- :930
#check @RBM.Graph.BAGraph.partition_of_normal -- :1137
#check @RBM.Graph.BAGraph.le_scalingOrderG_iff -- :1154
#check @RBM.Graph.BAGraph.scalingOrderG_of_normal -- :1167
#check @RBM.Graph.BAVocabInst.baGGLhs         -- :1181
#check @RBM.Graph.BAVocabInst.baLWT1          -- :1201
#check @RBM.Graph.BAVocabInst.baGedge         -- :1210

-- T2050 (LW-03, 37db678): `RBM3D/Graph/LWVocab.lean`, namespace `RBM.Graph`
#check @RBM.Graph.LData                       -- :73
#check @RBM.Graph.SEdge                       -- :82
#check @RBM.Graph.SEdge.val                   -- :115
#check @RBM.Graph.LGraph                      -- :104
#check @RBM.Graph.Counters                    -- ScalingOrder.lean:49
#check @RBM.Graph.ord                         -- ScalingOrder.lean:65

-- T2060 (LW-04, 89f29cf): `RBM3D/Graph/LWStein.lean`, namespace `RBM.Graph` (`:82-1894`)
#check @RBM.Graph.lwStein_hasDerivAt_inv      -- :441
#check @RBM.Graph.lwGm                        -- :469
#check @RBM.Graph.lwG                         -- :474
#check @RBM.Graph.lwStein_hasDerivAt_lwG      -- :487
#check @RBM.Graph.lwPartial                   -- :509
#check @RBM.Graph.dhSample                    -- :521
#check @RBM.Graph.dhSample_lwG                -- :561
#check @RBM.Graph.dhSample_lwG_star           -- :591
#check @RBM.Graph.Tame1                       -- :703
#check @RBM.Graph.Tame1.mul                   -- :773
#check @RBM.Graph.Tame1.sum                   -- :802
#check @RBM.Graph.lwStein_dh_mul              -- :855
#check @RBM.Graph.lwStein_dh_sum              -- :876
#check @RBM.Graph.lwStein_tame_GDG            -- :917
#check @RBM.Graph.lwG_tame1                   -- :929
#check @RBM.Graph.lwVar                       -- :944
#check @RBM.Graph.lwPoly                      -- :949
#check @RBM.Graph.lwPoly_tame1                -- :965
#check @RBM.Graph.lwS                         -- :998
#check @RBM.Graph.stein_sample                -- :1013
#check @RBM.Graph.lwStein_resolvent_id        -- :1116
#check @RBM.Graph.integral_owxDefect          -- :1136
#check @RBM.Graph.lwS_row_sum                 -- :1215
#check @RBM.Graph.lwS_isUnit                  -- :1313
#check @RBM.Graph.LGraph.dTerms               -- :1390

-- T2107 (LW-05, 975f4ff): `RBM3D/Graph/LWWeightExp.lean`, namespace `RBM.Graph` (`:51-1507`)
#check @RBM.Graph.lwWxSizes                   -- :59
#check @RBM.Graph.lwWx_lwG                    -- :70
#check @RBM.Graph.lwWx_Gres_false             -- :124
#check @RBM.Graph.lwWxRename                  -- :157
#check @RBM.Graph.lwWx_lwPoly_eval            -- :163
#check @RBM.Graph.lwWx_dh_var                 -- :189
#check @RBM.Graph.lwWx_hasDerivAt             -- :215
#check @RBM.Graph.lwWx_dh                     -- :267
#check @RBM.Graph.lwWx_lwS_apply              -- :281
#check @RBM.Graph.lwWx_integral               -- :330
#check @RBM.Graph.lwWeightExp_holds           -- :407
#check @RBM.Graph.LGraph.owxExt               -- :458
#check @RBM.Graph.owx_nM_eq                   -- :514

-- LW pins (975f4ff): `RBM3D/Graph/LWPins.lean`, namespace `RBM.Graph` (`:53-185`)
#check @RBM.Graph.LWPins_dH                   -- :62
#check @RBM.Graph.LWPins_resPoly              -- :73
#check @RBM.Graph.LWweightExp                 -- :106

-- T2128 (LW-08, c967b9c): `RBM3D/Graph/LWLvl1.lean` (consumer pattern only)
#check @RBM.Graph.lvl1_good_R2                -- :2531
#check @RBM.Graph.LocStep                     -- :3260

-- Stein hypothesis, discharged (T2088, 3b8c687 / cca94be): namespace `RBM.Green`
#check @RBM.Green.GaussIBP                    -- LDEQuad.lean:302
#check @RBM.Green.gaussIBP                    -- IBPPoly.lean:305

-- the model (namespace `RBM.Gauss`)
#check @RBM.Gauss.Idx                         -- Defs/Sizes.lean:46 (0a873f1)
#check @RBM.Gauss.svarF                       -- Gauss/FineModel.lean:47 (0a873f1)
#check @RBM.Gauss.Ω                           -- :84
#check @RBM.Gauss.PF                          -- :97
#check @RBM.Gauss.Sizes.seqP                  -- :169
#check @RBM.Gauss.Sizes.slice                 -- :176
#check @RBM.Gauss.Sizes.seqHflow              -- :225
#check @RBM.Gauss.Hflow                       -- :437
#check @RBM.Gauss.Sizes.seqHflow_isHermitian  -- :531
#check @RBM.Gauss.PsiI                        -- Gauss/BlockAnderson.lean:52 (868b3b4)
#check @RBM.Gauss.PsiI_isHermitian            -- :65
#check @RBM.Gauss.ztOf                        -- Loop/GLoopFlow.lean:55 (868b3b4)
#check @RBM.Gauss.Gres                        -- :74
#check @RBM.Gauss.Mres                        -- :81

-- BA deterministic layer (namespace `RBM.BA`)
#check @RBM.BA.BAMB                           -- BA/MFixedPoint.lean:190 (ae63e74)
#check @RBM.BA.BASelf                         -- :193
#check @RBM.BA.BAMB_symm                      -- BA/Ward.lean:83 (b4fb28b)
#check @RBM.BA.BAMB_diag_eq                   -- :89
#check @RBM.BA.BAMB_row_sq_real               -- :125
#check @RBM.BA.BAm_norm_le_one                -- :136
#check @RBM.BA.BAMres_fine_apply              -- BA/FlowPins.lean:100 (b750bf3)
#check @RBM.BA.BASelf_iff_fine                -- :139

/-! ## 2. Vocabulary and the pin (copied verbatim by T2295 into namespace `RBM.Graph`) -/

noncomputable section

open MeasureTheory Matrix RBM.Gauss

namespace RBM.Graph.T2295Check

section LWBA

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `H_t = g₀ Ψ + √t V` at a sample `ω` of `PF d L W 0` (`(MBM)`, `1_2:685`; law `S^{(B)}(0) = I`, §57 (3)). -/
def BAlwH (g0 t : ℝ) (ω : Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  (g0 : ℂ) • PsiI d L W + Hflow d L W t ω

/-- `M = (g₀ Ψ - E - m)⁻¹` on the fine lattice (`(def_G0)`, `1_2:631`). -/
def BAlwM (g0 E : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ := Mres ((g0 : ℂ) • PsiI d L W) (E : ℂ) m

/-- `G_{xy}` of the flow, `z_t = E + (1 - t) m`. -/
def BAlwG (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) (x y : Idx d L W) : ℂ :=
  Gres (BAlwH d L W g0 t ω) (ztOf m E t) true x y

/-- `Ǧ_{xy} = G_{xy} - M_{xy}`. -/
def BAlwGc (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) (x y : Idx d L W) : ℂ :=
  BAlwG d L W g0 E t m ω x y - BAlwM d L W g0 E m x y

/-- `S_{αβ} = t W^{-d} 1([α] = [β])`: the variance of `√t V` (`S^{(B)}(0) = I`). -/
def BAlwS (t : ℝ) (x y : Idx d L W) : ℂ := (t : ℂ) * svarF d L W 0 x y

/-- `M^+_{xy} = M_{xy} M_{yx}` (`B:388`). Shared with BA-L2b/L2c. -/
def BAlwMp (g0 E : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun x y => BAlwM d L W g0 E m x y * BAlwM d L W g0 E m y x

/-- `1 + M^+ S^+ = (1 - M^+ S)⁻¹` (`(eq:def-Spm)`, `7_8:110`). Shared with BA-L2b/L2c. -/
def BAlwW (g0 E t : ℝ) (m : ℂ) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Ring.inverse (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t))

/-- `f(G)` of the expansions: a resolvent polynomial at the flow matrix. -/
def BAlwf (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W) : ℂ :=
  LWPins_resPoly d L W (ztOf m E t) P (BAlwH d L W g0 t ω)

/-- `∂_{h_{αw}} f(G)`. -/
def BAlwdf (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (ω : Ω d L W)
    (α w : Idx d L W) : ℂ :=
  LWPins_dH (LWPins_resPoly d L W (ztOf m E t) P) (BAlwH d L W g0 t ω) α w

end LWBA

section LWBAPins

variable (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ)
  (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)

/-- Left side of `lanlw`: `Ǧ_{xy} f` (`B:359-372`, [yang2024Del, Lemma B.9]). -/
def BAlanlwL (x y : Idx d L W) (ω : Ω d L W) : ℂ :=
  BAlwGc d L W g0 E t m ω x y * BAlwf d L W g0 E t m P ω

/-- Right side of `lanlw` before `𝔼`: `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f - Σ_{α,β} M_{xα} S_{αβ} G_{βy} ∂_{h_{βα}} f`. -/
def BAlanlwR (x y : Idx d L W) (ω : Ω d L W) : ℂ :=
  (∑ α, ∑ β, BAlwM d L W g0 E m x α * BAlwS d L W t α β * BAlwGc d L W g0 E t m ω β β *
      BAlwG d L W g0 E t m ω α y * BAlwf d L W g0 E t m P ω -
    ∑ α, ∑ β, BAlwM d L W g0 E m x α * BAlwS d L W t α β * BAlwG d L W g0 E t m ω β y *
      BAlwdf d L W g0 E t m P ω β α)

variable {d L W g0 E t m P}

/-- **`lanlw`** (`B:359-372`, [yang2024Del, Lemma B.9]): `𝔼[BAlanlwL] = 𝔼[BAlanlwR]` for every resolvent polynomial `f`
over the BA law `PF d L W 0`.  Needs `(self_m)` (`M_{ββ} = m`; false for an arbitrary `m`, T2161 report (b.7)).
Registry: proved (T2295). -/
def BAlanlw (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m →
    0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y : Idx d L W),
      ∫ ω, BAlanlwL d L W g0 E t m P x y ω ∂(PF d L W 0) = ∫ ω, BAlanlwR d L W g0 E t m P x y ω ∂(PF d L W 0)

end LWBAPins

end RBM.Graph.T2295Check

end

/-! ## 3. Prop-valued pin texts (no proof obligation) -/

namespace RBM.Graph.T2295Check

/-- Target 2: the pin holds for every `d` (T2295 proves `baLanlw_holds (d : ℕ) : BAlanlw d`). -/
def T2295_baLanlw_holds : Prop := ∀ d : ℕ, BAlanlw d

/-- The band twin it follows (merged, proved): the shape of target 2. -/
example : Prop := ∀ d : ℕ, RBM.Graph.LWweightExp d

end RBM.Graph.T2295Check
