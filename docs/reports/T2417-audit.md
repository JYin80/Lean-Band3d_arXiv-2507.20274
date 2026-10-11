Auditor model: claude-opus-5-5

# T2417 audit (round 1) — BA-L R0 `BAAtomic`, branch `t/T2417` @ `7253ee9`, worktree `RBM3D-wt/T2417-audit1`
Date (`date -u`): Sun Oct 11 11:06:00 UTC 2026. Merge base `b51fead`; upstream files (`BAVocab`, `LWVocab`, `LWLvl1`,
`LocalRegular{,2,6a}`) unchanged between merge base and `main` `5d88807` (`git diff --stat b51fead main -- …`: empty).

**Verdict: PASS** (all five targets). No dispatcher sign-off needed.

## 1. Build, axioms, diff, forbidden tokens
```
$ lake build RBM3D.Graph.BAAtomic RBM3D.Graph.BAAtomic2 | grep -E "error|warning: RBM3D/Graph/BAAtomic|Build completed"; echo exit
Build completed successfully (3388 jobs).
exit 0
$ lake env lean ax.lean          # import RBM3D.Graph.BAAtomic2; #print axioms …
'RBM.Graph.BAimg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAImgNormal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAImgCounters_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAImgMol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAPathLift_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.img95_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.img95_equiv_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.liftC_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.img_locStd_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAAtomic_counters_liftC' depends on axioms: [propext, Classical.choice, Quot.sound]
$ printf "import RBM3D\nimport RBM3D.Graph.BAAtomic\nimport RBM3D.Graph.BAAtomic2\n#assert_rbm_axioms\n" > pre.lean; lake env lean pre.lean
exit 0
axiom audit: 11867 theorems, 3604 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean docs/tickets/checks/T2417-check.lean   (in the audit worktree)
check file exit 0
$ git diff --name-only main...HEAD
RBM3D/Graph/BAAtomic.lean
RBM3D/Graph/BAAtomic2.lean
$ git diff main...HEAD | grep -cE '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom '
0
$ wc -l RBM3D/Graph/BAAtomic.lean RBM3D/Graph/BAAtomic2.lean      # stop line 2,000 per file
     985 RBM3D/Graph/BAAtomic.lean
     262 RBM3D/Graph/BAAtomic2.lean
```
Only sole writable files touched; `RBM3D.lean` not edited (hub adds both imports at merge). No frozen signature touched (new files only).

## 2. Statements against the pins (script diff, `pindiff.py`)
Probe text from `git show t/T2395:RBM3D/Probe/T2395Pins.lean` (27-66, 218-232) and `t/T2397:…/T2397Pins.lean`
(29-48, 108-120, 219-246, 355), declarations extracted and whitespace-normalised, against the branch files:
```
T2395 BAGraph.sameAtom: SAME          T2395 BAGraph.intAtom: SAME       T2395 BAGraph.nLoops: SAME
T2395 BAGraph.nExt: SAME              T2395 BAGraph.nShare: SAME        T2395 BAGraph.pairsAux: SAME
T2395 BAGraph.nPairs: SAME            T2395 BAGraph.atEdges: SAME       T2395 BAGraph.atCharge: SAME
T2395 BAGraph.LocStd: SAME            T2395 baPG: SAME up to section-variable binders
T2395 BALvl1Good: ABSENT in branch    T2395 BALvl1GoodLit: ABSENT in branch
T2395 BAGraph.img: DIFF   (probe: mergeP-first construction; branch: `(promoteC Γ).mergeP`)
T2395 BAPGraph.img: DIFF  (only `{E : Type}` made explicit; probe has it as section variable) -> same
T2395 BAimg: SAME
T2397 atomSetoid: SAME   T2397 promoteC: SAME   T2397 liftG: SAME   T2397 liftC: SAME   T2397 liftC_normal: SAME (statement)
T2397 BAImgNormal / BAImgCounters / BAPathLift: SAME up to binders and `img` -> `BAPGraph.img`
T2397 BAImgMol: SAME (manual re-check of probe 118-120 vs branch 429-431: identical text)
T2397 img: ABSENT (replaced by `BAPGraph.img`; branch example :964 `BAPGraph.img Q = ((promoteC Q.g).mergeP).lvl1Comp Q.ext Q.ext_surj := rfl`)
T2397 scostA, locStdA, BABridge, scostA_liftC, simP_liftStepT: ABSENT in branch
```
Assessment of each DIFF/ABSENT:
- `BAGraph.img`: target 2 asks for **one** map; the branch takes T2397's order (`promoteC` then `mergeP`). The T2395 probe
  construction is kept verbatim as `BAGraph.img95` (:726; its `eq1` inlined in private `BAAtomic_dot95` :720 as
  `Γ.dotted ++ (psi… ++ mdot…)`, the same list). So `BAimg` (T2395:230, text SAME) is now a statement about the one map, as
  the ticket requires.
- `img` → `BAPGraph.img`: definitional at `Fin 2` (rfl example above). Pins (m0), (m1), (m2), `BAPathLift` unchanged in content.
- `BALvl1Good(Lit)`, `scostA`, `locStdA`, `BABridge`, `scostA_liftC`: not in the ticket's explicit name lists for targets 1/4
  (target 1 lists `sameAtom … LocStd`; T2397 list `atomSetoid, promoteC, img`; (m3) excluded). Correctly absent.

**Target 2 relation statement** (extracted):
```
theorem BAGraph.img95_equiv (Γ : BAGraph E I) (hN : Γ.Normal) :
    ∃ (eE : Γ.img95.E' ≃ Γ.img.E') (eI : Γ.img95.I' ≃ Γ.img.I'),
      (∀ a, Γ.img.ext a = eE (Γ.img95.ext a)) ∧ Γ.img.g = Γ.img95.g.relabel (Sum.map eE eI)
theorem BAGraph.img95_equiv_gen (Γ : BAGraph E I) : ∃ eE eI, (ext compatible) ∧ waved = ∧ dotted = ∧ coeff = ∧
      (Γ.img95.g.relabel (Sum.map eE eI)).solid = Γ.img.g.solid.map fun e => { e with circ := decide (e.src = e.dst) }
```
`PGraph.lvl1Comp` (`LWLvl1.lean:3095`) only recomposes `ext`; the band's equivalence of packed graphs is relabelling
(`LGraph.relabel`, `LWVocab.lean:460`) with compatible `ext`. Exact record equality after relabel for normal `Γ`; for
non-normal `Γ` the two constructions differ exactly in the circle of uncircled in-atom solid edges (shown at `G2`, example
:976). Equality of the packed graphs is not expressible (different quotient types), as the report says. This difference
only concerns non-normal graphs; every circle-sensitive conjunct of the pins (`BAimg` 5-6, (m0)) assumes `Normal`; it is
covered by paper-delta candidate `T2417a`. Accepted: the ticket delegated the order choice to 1a, and `promoteC` is a
verbatim T2397 pin.

**Other statement checks.** `BAimg`: quantifies over every `E I` with `Fintype`/`DecidableEq`, six conjuncts as pinned,
`Normal` only as antecedent of conjuncts 5-6 (as pinned). (m0)-(m2), `BAPathLift` over `BAPGraph (Fin 2)` / `PGraph (Fin 2)`
as in the probe; general-`E,I` graph forms also proved (`BAGraph.img_normal` :308, `img_counters` :538,
`img_molOf_eq_iff` :388). `BAPathLift`: `∀ P0, P0.g.Normal → ∀ k, …` — quantifier order as probe 355.

## 3. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` introduced; all pins are `def … : Prop` with every hypothesis in the binder list. No hypothesis
  carried as a field. `BAPGraph` is the merged `BAVocab.lean:176` structure (instance fields only).
- Dependencies: only merged modules (`BAVocab`, `LWLvl1`, `LocalRegular6a`, `LocalRegular2`); `BAAtomic2` imports
  `BAAtomic`. Nothing imports the new files; no cycle. No external hypothesis (no limit check needed).
- Proof chain: `BAimg_holds` := ⟨`img_counters`, `img_nLoops`, `img_nPairs`, `card_extCls`, `(img_normal hN).1`,
  `img_locStd_iff hN`⟩ (:706-707); `BAImg*_holds` are one-liners from the graph forms (:709-711); `BAPathLift_holds`
  (BAAtomic2:201) via `BAAtomic_pathFam_iff` and `liftG` lemmas. No pin is assumed.

## 4. Compiled nonempty instances (20 `example`s, all compile in the module build above)
| Endpoint | Instance (file:line) | Data / hypotheses discharged |
|---|---|---|
| `BAimg_holds` | BAAtomic:922 (`G0`), :928 (`G1`, `LocStd` true), :934 (`G0`, `LocStd` false both sides); BAAtomic2:252 (`liftC p2Graph.pack`) | `G0_normal`, `G1_normal` by `decide` |
| `BAImgNormal_holds` (m0) | BAAtomic:940 (`baPG G0`), BAAtomic2:237 (lift) | `G0_normal`; `liftC_normal _ BAAtomic_p2_normal.1` |
| `BAImgCounters_holds` (m1) | BAAtomic:943, BAAtomic2:241 | none needed |
| `BAImgMol_holds` (m2) | BAAtomic:946, :953 (concrete `α`,`γ` via waved edge), BAAtomic2:246 | none needed |
| `BAPathLift_holds` | BAAtomic2:228 at `P0 = p2Graph.pack`, all `k` | `BAAtomic_p2_normal : p2Graph.pack.g.Normal := by decide` |
| `img95_equiv` / `_gen` | BAAtomic:958 (`G0`, normal), :973 (`G2`, non-normal), :976 (circle difference) | `G0_normal` |
| `liftC_normal` | BAAtomic2:232 | `BAAtomic_p2_normal.1` |
Nondegeneracy (BAAtomic:917, `by decide`): `G0` has `nS = 4, nW = 1, nA = 2, nM = 1, nLoops = 2, nExt = 2`,
`inr 1 ∈ atom (inr 0)`, `inr 2 ∉ atom (inr 0)`. `G0` = `E = Fin 2`, `I = Fin 3`, `M_{αβ}` parallel to solid `α→β`
(solid edge inside an atom, K1) and solid `x→α`, `γ→y` between atoms. Since `BAGraph.atomAdj` (`BAVocab.lean:92`) joins the
ends of every `M`-edge, an `M`-edge is always inside an atom; the ticket's "one between atoms" can only be a solid edge
between atoms, which `G0` has. Lift data: `p2Graph` (`LWVocab.lean:191`, `E = Fin 2`, `I = Fin 4`, 6 solid, 2 waved).
No `N = 0`, empty index, `False` premise or large witness.

## 5. Name clashes
```
$ for n in <31 public pin/graph-form names>; do git grep -nE "^(private )?(noncomputable )?(def|theorem|abbrev|lemma) $n( |$)" main -- 'RBM3D/*.lean' | wc -l; done
all 0   (sameAtom … LocStd, baPG, atomSetoid, promoteC, BAGraph.img, BAPGraph.img, BAimg, BAImg*, BAPathLift, liftG, liftC,
         liftC_normal, img95, img_normal, img_counters, img_molOf_eq_iff, card_extCls, img_nLoops, img_nPairs, img_locStd_iff)
$ git diff main...t/T24{20,18,19,11,16} | grep new decls matching those names or BAAtomic_*   -> no hits
$ git grep "instance.*Decidable.*Normal|LocStd" main -- 'RBM3D/*.lean'  -> only LGraph instances (LWVocab:995, LWLvl1:3211)
```

## 6. Paper deltas
- Image map vs `B:308-313` (keeps in-atom solid edges, adds `×`-dots, drops BA `×`-dots): candidates `T2395a` (T2395 design
  §7) and `T2397a` (T2397 design §7.3, cited in the `promoteC` docstring). Not yet in `docs/paper-deltas.md` (grep: 0), pending
  dispatcher numbering, as the T2397 audit recorded.
- New here: `T2417a` (one map keeps an uncircled in-atom edge of a non-normal `Γ` uncircled; `img95` circles every loop),
  `T2417b` ((m0)-(m2) pinned at `Fin 2`; graph forms general). Coverage complete for every statement difference found in §2.

## 7. Observations (no RETURN)
- O1. Several unpinned public names are not stem-prefixed (§3 (E)): `BAGraph.img_normal`, `img_counters`, `img_molOf_eq_iff`,
  `card_extCls`, `img_nLoops`, `img_nPairs`, `img_locStd_iff`, `img95`, `img95_equiv(_gen)`, `*_holds`. They are target
  statements/graph forms of pins, not helpers, and clash with nothing on `main` or sibling branches.
- O2. Several stem-prefixed helpers are public (`BAAtomic_atomSetoid_iff`, `BAAtomic_vmap_*`, …); allowed by §3 (E).
- O3. Two `Decidable` instances (`BAGraph.Normal`, `BAGraph.LocStd`, BAAtomic:75-78) are anonymous public instances; a later
  file declaring them again would give duplicates (report finding (4) already says so).
- O4. Prove report's `#assert_rbm_axioms` count (11675 theorems) differs from this run (11867; cause not investigated,
  the root `RBM3D` oleans here come from a later copy of the main build cache); both report 0 axioms in `RBM`.

## Verdict per target
| Target | Verdict |
|---|---|
| 1 vocabulary + `baPG` | PASS (verbatim, §2) |
| 2 one map + relation to T2395 construction | PASS (`img` = T2397 order; `img95_equiv` exact relabel for normal Γ; `_gen` for all Γ; delta T2417a) |
| 3 `BAimg` | PASS |
| 4 (m0) `BAImgNormal`, (m1) `BAImgCounters`, (m2) `BAImgMol`, `BAPathLift` | PASS |
| 5 instances | PASS |
| Build / axioms / diff | PASS |
