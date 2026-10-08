/-
T2297 (LW-02, `lem:LW_moment`) check file.  Compiles on `main` (1ba63a2) as is.
Amend 1 (dispatcher V1, Thu Oct  8 14:52 UTC 2026; DECISIONS §150): `import RBM3D.Graph.LWEngine` and the engine names (T2332, merged 015198c).
Only imports of merged modules, `open`/`namespace`, pin texts, `#check` of merged names.
No proofs, no `sorry`, no `by`.
-/
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWSizeClaim
import RBM3D.Green.IBPPoly
import RBM3D.Graph.LWEngine

/-! ## 1. Merged names used by the route (namespace of each from its enclosing `namespace … end`) -/

-- `Graph/LWPins.lean` (975f4ff), `namespace RBM.Gauss.Sizes` (`:187-503`)
#check @RBM.Gauss.Sizes.LWMoment          -- :325, the owed pin (target)
#check @RBM.Gauss.Sizes.LWAssm            -- :234
#check @RBM.Gauss.Sizes.LWf               -- :199
#check @RBM.Gauss.Sizes.LWS               -- :194
#check @RBM.Gauss.Sizes.LWInit            -- :222
#check @RBM.Gauss.Sizes.LWLoop2           -- :228
#check @RBM.Gauss.Sizes.LWXi              -- :360
#check @RBM.Gauss.Sizes.LWAnp             -- :409
-- `Graph/LWPins.lean`, `namespace RBM.Gauss.LWInst` (`:578-676`, `:753-828`): consumers
#check @RBM.Gauss.LWInst.inst_LWMoment         -- :638
#check @RBM.Gauss.LWInst.inst_LWMoment_endT    -- :794
-- `Graph/LWPsi.lean` (461ae86), `namespace RBM.Gauss.Sizes` (`:38-426`)
#check @RBM.Gauss.Sizes.LWWindow          -- :47
#check @RBM.Gauss.Sizes.LWClass           -- :52
#check @RBM.Gauss.Sizes.LWPsiRel          -- :59
#check @RBM.Gauss.Sizes.LWPsiAll          -- :66
-- `Defs/StochDomAt.lean`
#check @RBM.Gauss.Sizes.Prec              -- :121
-- `Induction/Defs.lean`
#check @RBM.Gauss.Sizes.STGM              -- :77
#check @RBM.Gauss.Sizes.STblk             -- :73
-- `Graph/LocalRegular6d.lean` (37289f6), `namespace RBM.Graph` (`:111-`)
#check @RBM.Graph.lw_localregular         -- :1107
-- Amend 1: `Graph/LWEngine.lean` (T2332, 015198c), `namespace RBM.Graph`: the `m`-free expansion
#check @RBM.Graph.lw_localregularX        -- LWEngine.lean:771
#check @RBM.Graph.lwEvX                   -- LWEngine.lean:57
#check @RBM.Graph.LWLocRegConcl           -- LWEngine.lean:61
#check @RBM.Graph.lw_nWS_ge               -- LWEngine.lean:605
#check @RBM.Gauss.Sizes.STGavLGEX         -- Induction/Defs.lean:220 (F2: the max bound)
-- `Graph/LocalRegular.lean` (3bf20e1), `namespace RBM.Graph` (`:109-`)
#check @RBM.Graph.fxyPowGraph             -- :1354
#check @RBM.Graph.fxyPowGraph_val_eq      -- :1739
#check @RBM.Graph.fxyPowGraph_ord         -- :1983
#check @RBM.Graph.fxyPowGraph_nM          -- :1577
#check @RBM.Graph.fxyPowGraph_normal      -- :1462
-- `Graph/LWLvl1.lean`, `namespace RBM.Graph`
#check @RBM.Graph.LocStep                 -- :3260
#check @RBM.Graph.lvl1_induction          -- :3763
-- `Graph/LWVocab.lean` (37db678), `namespace RBM.Graph` (`:67-`)
#check @RBM.Graph.LData                   -- :73
#check @RBM.Graph.WEdge.val               -- :120
#check @RBM.Graph.LGraph.val              -- :135
#check @RBM.Graph.LGraph.nW               -- :173
#check @RBM.Graph.LGraph.nM               -- :177
#check @RBM.Graph.fxyVal                  -- :217
#check @RBM.Graph.LGraph.scalingSize      -- :1667
-- `Graph/LWStein.lean` (89f29cf), `namespace RBM.Graph` (`:82-`)
#check @RBM.Graph.lwS                     -- :998
#check @RBM.Graph.lwGm                    -- :469
#check @RBM.Graph.lwSampleData            -- :1420
-- `Graph/LWSizeClaim.lean` (dd1748c), `namespace RBM.Graph` (`:75-`)
#check @RBM.Graph.lwSpOf                  -- :135
#check @RBM.Graph.lwSpOf_eq               -- :165
#check @RBM.Graph.lwSpOf_decay_E          -- :461
#check @RBM.Graph.LGraph.sizeConst        -- :1098
-- `Graph/AuxGraph.lean` (87cf70c), `namespace RBM.Graph` (`:53-1845`)
#check @RBM.Graph.LGraph.auxVal           -- :79
#check @RBM.Graph.LGraph.auxOrd           -- :86
#check @RBM.Graph.LWGtoAG                 -- :979
#check @RBM.Graph.lwGtoAG_holds           -- :1018
#check @RBM.Graph.LWScalemole             -- :1003
#check @RBM.Graph.lwScalemole_holds       -- :1130
#check @RBM.Graph.LWAuxNested             -- :1597
#check @RBM.Graph.lwAuxNested_holds       -- :1606
-- `Graph/AuxGraph2.lean` (fbaa460), `namespace RBM.Graph` (`:56-`)
#check @RBM.Graph.lwXiVar                 -- :76
#check @RBM.Graph.LWXiClaim               -- :951
#check @RBM.Graph.lwXiClaim_holds         -- :965
#check @RBM.Graph.LWGbyXi                 -- :1106
#check @RBM.Graph.lwGbyXi_holds           -- :1122
#check @RBM.Graph.lwGbyXi_hxi             -- :1160
#check @RBM.Graph.LWEntryPsi              -- :1177
#check @RBM.Graph.lwEntryPsi_holds        -- :1191
#check @RBM.Graph.LWXiRad                 -- :1236
#check @RBM.Graph.lwXiRad_holds           -- :1241
-- `Graph/AnpKey6.lean` (e2703ec), `namespace RBM.Graph` (`:44-`)
#check @RBM.Graph.lwAnp_holds             -- :952
-- `Graph/LWExpTerm.lean`, `namespace RBM.Gauss.Sizes` (`:43-`): the `≺ → 𝔼` upgrade
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral   -- :143
-- `Graph/LWExpTerm2.lean` (d6ebc39), `namespace RBM.Gauss.Sizes` (`:63-`)
#check @RBM.Gauss.Sizes.lwExpTerm2_Gt_eq_Gsm      -- :873
-- `Green/IBPPoly.lean` (3b8c687), `namespace RBM.Green` (`:49-`)
#check @RBM.Green.gaussIBP                -- :305

/-! ## 2. Pins (targets; the theorems state these with no added hypothesis) -/

namespace T2297Check

open RBM RBM.Gauss RBM.Graph

/-- Main target `lwMoment_holds : LWMomentPin` (the owed pin, unchanged). -/
def LWMomentPin : Prop := ∀ d : ℕ, RBM.Gauss.Sizes.LWMoment d

/-- Target `lwMoment_val_smul : LWMomHomPin`: the value of a graph is homogeneous of degree
"number of black waved edges" in `S` (coloured `S^±` edges and `M`, `G` untouched). -/
def LWMomHomPin : Prop :=
  ∀ {E I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (Γ : LGraph E I) (D : LData ι) (s : ℂ) (ℓe : E → ι),
    Γ.val { D with S := s • D.S } ℓe = s ^ (Γ.waved.countP (fun e => !e.col)) * Γ.val D ℓe

/-- Target `lwMoment_fxy_bridge : LWfBridgePin`: the graph `f_{xy}` at the flow data (variance
`S^{(t)} = t · svarF`) is `t` times the pinned `LWf` (variance `svarF`). -/
def LWfBridgePin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ)
    (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)),
    fxyVal (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) Sp ω) x y =
      (t : ℂ) * RBM.Gauss.Sizes.LWf sz n E t ω x y

end T2297Check
