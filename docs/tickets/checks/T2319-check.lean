/-
Release check for T2319 (dispatcher V1, Thu Oct  8 02:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §130, §107 (1), §108 (1),
§95 (1)).  LW-14e-1′ "Cert′": the corrected lite flag `belowOf'` (`X0` read from `Δ.dotBase`, the dotted edges that
`withDots` keeps, instead of every `×`-edge of `Δ`) and the kernel certificate `cert_all'` for it, copies of T2306's
`RBM3D/Graph/LWExpCert.lean:152-282`, `LWExpCertS0.lean`, `LWExpCertS1.lean` with primed names and one changed line
(the defect: `docs/reports/T2318-prove.md` (a); the design: `docs/claude-team/fable/2026-10-08-t2318-belowof.md`).
Section 1: `#check` of every merged name the copied code uses (`Graph/LWExpCert` 8096694, namespace `RBM.Graph.LWCert`
`:35-291`; `Graph/LWVocab` 37db678, `Graph/LWStein` 89f29cf, `Graph/LWWeightExp` 975f4ff, `Graph/LWGGExp` 5c69cb4,
`Graph/LWExpTerm3` 20de014, namespaces from the enclosing `namespace … end` blocks) and of the Mathlib / core names of
its proofs.  `cert_FF`, `cert_FT`, `cert_all` (`LWExpCertS0.lean:277`, `LWExpCertS1.lean:277, :297`) are the templates of
`cert_FF'`, `cert_FT'`, `cert_all'`; their modules are not imported here (nothing of them is used by the new proofs).
Section 2: the changed line as a Prop pin (well-typed in the context of `belowOf`), the exactness it restores (shape only;
T2318 proves it), the shape of the target `cert_all'` and of the diagnostic instances, in the temporary namespace
`RBM.Graph.LWCert.T2319Check`.  The full text of `belowOf'` is in the ticket ("Target") and is checked there by `diff`.
Statements and `#check` only: no proof, no tactic block, no `theorem`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2319-check.lean`.
-/
import RBM3D.Graph.LWExpCert

/-! ## 1. Merged names -/

-- T2306 (LW-14e-1 Cert, 8096694): `RBM3D/Graph/LWExpCert.lean`, namespace `RBM.Graph.LWCert` (`:35`)
#check @RBM.Graph.LWCert.MNode               -- :46
#check @RBM.Graph.LWCert.vi                  -- :59
#check @RBM.Graph.LWCert.unite               -- :62
#check @RBM.Graph.LWCert.labsOf              -- :69
#check @RBM.Graph.LWCert.repsOf              -- :72
#check @RBM.Graph.LWCert.posOf               -- :75
#check @RBM.Graph.LWCert.pairOf              -- :78
#check @RBM.Graph.LWCert.mkV                 -- :81
#check @RBM.Graph.LWCert.cMerge              -- :87 (its test reads `(Δ.withDots c).dotted = Δ.dotBase ++ c.2`)
#check @RBM.Graph.LWCert.cPartition          -- :100
#check @RBM.Graph.LWCert.Cand                -- :113
#check @RBM.Graph.LWCert.cands               -- :121
#check @RBM.Graph.LWCert.renum               -- :133
#check @RBM.Graph.LWCert.fams                -- :138
#check @RBM.Graph.LWCert.tgt                 -- :147
#check @RBM.Graph.LWCert.leaf                -- :150
#check @RBM.Graph.LWCert.belowOf             -- :157 (the defective flag; template of `belowOf'`; used only by the instance `lwCertB_cex_bites`)
#check @RBM.Graph.LWCert.childrenB           -- :192 (template of `childrenB'`; not used)
#check @RBM.Graph.LWCert.goodB               -- :197 (template of `goodB'`; not used)
#check @RBM.Graph.LWCert.rootInfo            -- :204 (template of `rootInfo'`; used only by the instance `lwCertB_root_eq`)
#check @RBM.Graph.LWCert.rootAt              -- :206 (template; not used)
#check @RBM.Graph.LWCert.kids                -- :209 (template; not used)
#check @RBM.Graph.LWCert.kidsOk              -- :212 (template; not used)
#check @RBM.Graph.LWCert.kid                 -- :215 (template; not used)
#check @RBM.Graph.LWCert.all_of_getD         -- :217 (reused as is by `goodB'_succ_of` and `cert_all'`)
#check @RBM.Graph.LWCert.goodB_succ_of       -- :226 (template of `goodB'_succ_of`)
#check @RBM.Graph.LWCert.inner_node_one      -- :259 (template of `inner_node_one'`)
#check @RBM.Graph.LWCert.root_FF_shape       -- :267
#check @RBM.Graph.LWCert.root_FT_shape       -- :268
#check @RBM.Graph.LWCert.lwCert_root0_nonleaf -- :272
#check @RBM.Graph.LWCert.lwCert_roots_below  -- :279

-- LW-03 (`Graph/LWVocab`, T2050, 37db678; `namespace RBM.Graph` `:67-2559`)
#check @RBM.Graph.SEdge                      -- :82
#check @RBM.Graph.WEdge                      -- :89
#check @RBM.Graph.DEdge                      -- :96 (`⟨eq, x, y⟩`)
#check @RBM.Graph.DEdge.eq
#check @RBM.Graph.DEdge.x
#check @RBM.Graph.DEdge.y
#check @RBM.Graph.LGraph                     -- :104 (`⟨solid, waved, dotted, coeff⟩`)
#check @RBM.Graph.LGraph.solid
#check @RBM.Graph.LGraph.waved
#check @RBM.Graph.LGraph.dotted
#check @RBM.Graph.LGraph.coeff
#check @RBM.Graph.LGraph.SBetween            -- :969 (decidable, :979)
#check @RBM.Graph.LGraph.isB                 -- :1066 (`×` with no solid edge between the ends: the b-edges)
#check @RBM.Graph.LGraph.bEdges              -- :1069
#check @RBM.Graph.LGraph.dotBase             -- :1073 (**the changed line reads this**: `Γ.dotted.filter fun e => !Γ.isB e`)
#check @RBM.Graph.LGraph.dotChoices          -- :1086
#check @RBM.Graph.LGraph.withDots            -- :1091 (`dotted := Γ.dotBase ++ c.2`)
#check @RBM.Graph.LGraph.splitWeights        -- :1246
#check @RBM.Graph.LGraph.Consistent          -- :1267 (what the corrected skip test decides; T2318's L7)
#check @RBM.Graph.LGraph.scalingOrder        -- :1672
#check @RBM.Graph.ord                        -- `Graph/ScalingOrder` :65

-- LW-04 (`Graph/LWStein`, T2060, 89f29cf; `namespace RBM.Graph`), LW-05 (`Graph/LWWeightExp`, T2107, 975f4ff),
-- LW-07 (`Graph/LWGGExp`, T2120, 5c69cb4): the families (`fams`, unchanged, imported)
#check @RBM.Graph.lwSplit                    -- :891
#check @RBM.Graph.owxT1                      -- :658
#check @RBM.Graph.LGraph.owxExt              -- :458 (`dotted := Γ.dotted.map (DEdge.map emb)`: the families keep the `×`-edges)
#check @RBM.Graph.oe2xR2                     -- :485
#check @RBM.Graph.oe2xR4                     -- :491
#check @RBM.Graph.oe2xR5                     -- :500
#check @RBM.Graph.oe2xR6                     -- :508
#check @RBM.Graph.oe2xR7                     -- :518
#check @RBM.Graph.oe2xR8                     -- :529

-- LW-14c (`Graph/LWExpTerm3`, T2255, 20de014; `namespace RBM.Gauss.Sizes` `:48-2224`): the root (`rootInfo'`)
#check @RBM.Gauss.Sizes.LWG5Graph            -- :54 (`dotted := []`)

-- Mathlib / core (verified in the probe and T2306, `docs/reports/T2288-prove.md` (c), `T2306-prove.md` (c))
#check @finSumFinEquiv
#check @List.getElem_of_mem
#check @List.getD_eq_getElem
#check @List.all_eq_true
#check @List.getElem?_eq_getElem
#check @Bool.or_eq_true

noncomputable section

namespace RBM.Graph.LWCert

open RBM.Gauss.Sizes

namespace T2319Check

/-! ## 2. The changed line, the exactness it restores, and the shapes (Prop pins; T2319 states `belowOf'` as a
`def` — its full text is in the ticket — and `cert_all'` as the theorem) -/

/-- **The one changed line of `belowOf'`** (`LWExpCert.lean:162`: `Δ.dotted` → `Δ.dotBase`), pinned as the identity of the
new `X0` with the `×`-edges that have a solid edge between their ends (T2306's `X0` is the left side with `Δ.dotted`). -/
def belowOf'_X0_pin : Prop :=
  ∀ (a b : ℕ) (Δ : LGraph (Fin (a+1)) (Fin b)),
    ((Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)) =
      ((Δ.dotted.filter fun e => !e.eq && decide (Δ.SBetween e.x e.y)).map (pairOf a b))

/-- **The exactness restored** (T2318 Amend 1, L7; shape only here): the skip test of `belowOf'` at a choice `c` is the test
of `cMerge (Δ.withDots c) ext` (`LWExpCert.lean:88-89`), i.e. `¬ (Δ.withDots c).Consistent`. -/
def belowOf'_skip_pin : Prop :=
  ∀ (a b : ℕ) (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) (c : ℤ × List (DEdge (Fin (a+1) ⊕ Fin b))),
    (let n := a + 1 + b
     let X0 : List (ℕ × ℕ) := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)
     let E0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => e.eq).map (pairOf a b)
     let E1 := (c.2.filter fun e => e.eq).map (pairOf a b)
     let X1 := (c.2.filter fun e => !e.eq).map (pairOf a b)
     let labs := labsOf n (E0 ++ E1)
     (X0 ++ X1).any (fun e => labs.getD e.1 0 == labs.getD e.2 0)) = true ↔
    cMerge (Δ.withDots c) ext = none

/-- The target `cert_all'` with the certificate functions abstracted (T2319 defines `rootInfo'`, `goodB'`). -/
def cert_all'_shape : Prop :=
  ∀ (rootInfo' : Bool → Bool → Bool × List MNode) (goodB' : ℕ → MNode → Bool),
    ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true

/-- The counterexample graph of T2318 (a) (`lwCertB_cex`): one external pair, no internal vertex, one b-edge `×(0,1)`;
and the shapes of the instances (5)-(7) with `lostOf`, `lostAt` abstracted. -/
def lwCertB_cex_shape : Prop :=
  ∀ (lostOf : ∀ {a b : ℕ}, LGraph (Fin (a+1)) (Fin b) → ℕ) (lostAt : MNode → ℕ → ℕ → ℕ) (rootAt' : Bool → Bool → ℕ → MNode)
    (belowOf' : ∀ {a b : ℕ}, LGraph (Fin (a+1)) (Fin b) → (Fin 2 → Fin (a+1)) → Bool × List MNode),
    (belowOf (a := 1) (b := 0) ⟨[], [], [⟨false, Sum.inl 0, Sum.inl 1⟩], 1⟩ ![0, 1]).2.length = 1 ∧
    (belowOf' (a := 1) (b := 0) ⟨[], [], [⟨false, Sum.inl 0, Sum.inl 1⟩], 1⟩ ![0, 1]).2.length = 2 ∧
    lostOf (a := 1) (b := 0) ⟨[], [], [⟨false, Sum.inl 0, Sum.inl 1⟩], 1⟩ = 1 ∧
    lostAt (rootAt' false false 9) 0 0 = 5 ∧ lostAt (rootAt' false false 9) 0 6 = 36 ∧
    lostOf (a := 1) (b := 3) (LWG5Graph false false) = 0 ∧ lostOf (a := 1) (b := 3) (LWG5Graph false true) = 0

/-! ## 3. Statement shapes -/

example : Prop := belowOf'_X0_pin ∧ belowOf'_skip_pin ∧ cert_all'_shape ∧ lwCertB_cex_shape
-- `inner_node_one'`, `lwCert_root0_nonleaf'` (instances (1), (2)) with the functions abstracted
example : Prop := ∀ (goodB' : ℕ → MNode → Bool) (rootAt' : Bool → Bool → ℕ → MNode),
  goodB' 3 (rootAt' false false 0) = true ∧ leaf (rootAt' false false 0) = false ∧
    (rootAt' false false 0).g.scalingOrder = 3 ∧ tgt (rootAt' false false 0) = 4 ∧ (rootAt' false false 0).b = 2 ∧
    (cands (rootAt' false false 0).g).length = 2

end T2319Check

end RBM.Graph.LWCert

end
