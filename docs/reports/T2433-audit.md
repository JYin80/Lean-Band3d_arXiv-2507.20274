Auditor model: claude-opus-5-5

# T2433 audit, round 1 (generic half: Amend 1, H234, H235 Q3-C1/Q3-C2) — Mon Oct 12 11:20:49 UTC 2026 (`date -u`)

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2433-audit1`, detached at `t/T2433` = `40155a3`; merge-base with `main` `a24d4e9`; `main` = `adb4a19`.
Scope in force (Amend 1 item 1, H234): `BACtx`; the GG-with-context Lemma, both charges, and its `kids` form; `BAselStar` (H235 Q3-C2: `BACtx` candidates only);
`BAG5LeafProps`, `BAG5Attached` as definitions; no `baG5Graph` table, no target 4, no closure/completeness claim (Q3-C1). `BAG5Leaf2.lean` may stay unused (Amend 1 item 3).

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.BAG5Leaf            # audit worktree
✔ [3912/3912] Built RBM3D.Graph.BAG5Leaf (9.0s)
Build completed successfully (3912 jobs).
$ lake env lean ax.lean                      # import RBM3D.Graph.BAG5Leaf; #print axioms of every public theorem
'RBM.Graph.baG5CtxLemma_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baG5CtxKids_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baselStar_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baselStar_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.instCtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.baG5CtxLemma_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.baG5CtxKids_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.baAllM_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.baG5Ctx_H3_needed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.baG5Attached_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.baselStar_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAG5LeafInst.instP_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
$ lake env lean full.lean                    # import RBM3D; import RBM3D.Graph.BAG5Leaf; #assert_rbm_axioms
axiom audit: 13206 theorems, 4158 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
EXIT=0       # 215 output lines; grep -niE "error|unregistered|BAG5|BACtx|baselStar": 0 hits
$ (main worktree, main = adb4a19) lake env lean <audit wt>/RBM3D/Graph/BAG5Leaf.lean
MAIN_EXIT=0 lines= 0
$ lake env lean docs/tickets/checks/T2433-check.lean     # on the branch
CHECK_EXIT=0 error-lines=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom " RBM3D/Graph/BAG5Leaf.lean | wc -l
       0
$ git diff --name-status main...t/T2433
A	RBM3D/Graph/BAG5Leaf.lean
A	RBM3D/Probe/T2433Pins.lean
$ git diff --stat a24d4e9 main -- Graph/{BAExpandId,BAGGOp,BAVocab,BAWeightOp,BAExpandWOrd}.lean   # upstream inputs moved since base?
(empty)
$ grep -rn "import RBM3D.Probe" RBM3D.lean RBM3D/ | wc -l
       0
```
Both files are sole writable files; the probe is the never-merged probe step (hub brings in `BAG5Leaf.lean` only). No existing file is touched, so no frozen signature changes. Only import: `RBM3D.Graph.BAExpandId` (merged, L4d): no cycle.

## 2. Statements against the pins
```
$ diff <(T2398 probe 158-166, defs only) <(branch BAG5Leaf.lean 82-89, defs only) && echo empty
empty
$ diff <(check file 92-99, prefix T2433_ dropped) <(branch 82-89) && echo empty
empty
$ for n in BAG5Attached BAG5LeafProps BACtx BAG5CtxLemma BAG5CtxKids BAselStar: md5 of the def body, T2433 probe vs branch
BAG5Attached probe=a0b5b2891d2f647e3ea98e3edd05ee42 branch=a0b5b2891d2f647e3ea98e3edd05ee42
BAG5LeafProps probe=21018858624669c6e95fd90625224e2f branch=21018858624669c6e95fd90625224e2f
BACtx probe=a976767108ad0c9df809a917517d27a9 branch=a976767108ad0c9df809a917517d27a9
BAG5CtxLemma probe=0b936bca5ab38cdb812dbe11738aebc2 branch=0b936bca5ab38cdb812dbe11738aebc2
BAG5CtxKids probe=191ea3af4cea310783d7de7d9453851c branch=191ea3af4cea310783d7de7d9453851c
BAselStar probe=5267f779ff811cd02f48130e9c9f82d8 branch=5267f779ff811cd02f48130e9c9f82d8
```
Lean text of the targets (`BAG5Leaf.lean:108-126, 927, 947, 965-986`):
```
def BACtx {P : BAPGraph (Fin 2)} (c : BARCand P) : Prop :=
  P.g.Normal ∧ (∀ w ∈ P.g.atom c.v, w.isRight = true) ∧
    (P.g.solid.filter fun e => decide (e.src ∈ P.g.atom c.v ∨ e.dst ∈ P.g.atom c.v)).length = 2 ∧
    P.g.atom c.v ≠ P.g.atom c.p.1.dst ∧ P.g.atom c.v ≠ P.g.atom c.q.1.src ∧ P.g.atom c.q.1.src ≠ P.g.atom c.p.1.dst ∧
    ((∀ w ∈ P.g.atom c.q.1.src, w.isRight = true) ∨ (∀ w ∈ P.g.atom c.p.1.dst, w.isRight = true))
def BAG5CtxLemma : Prop := ∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c →
    (∀ T ∈ BAExpandId_ggL2 c.σ P.g c.p c.q, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
    (∀ T ∈ BAExpandId_ggL4 c.σ P.g c.p c.q, ((P.scalingOrder + 1 : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)
def BAG5CtxKids : Prop := ∀ (P : BAPGraph (Fin 2)) (c : BARCand P), BACtx c → ∀ r ∈ c.kids, P.scalingOrder + 1 ≤ r.2.scalingOrder
theorem baG5CtxLemma_holds : BAG5CtxLemma
theorem baG5CtxKids_holds : BAG5CtxKids
def BAselStar : BASel := fun P => open Classical in
  if BAG5Leaf P then none else if h : ∃ c : BARCand P, c.σ = true ∧ BACtx c then some h.choose else none
theorem baselStar_spec (P) (c : BARCand P) (h : BAselStar P = some c) : ¬ BAG5Leaf P ∧ c.σ = true ∧ BACtx c
theorem baselStar_eq_none_iff (P) : BAselStar P = none ↔ BAG5Leaf P ∨ ¬ ∃ c : BARCand P, c.σ = true ∧ BACtx c
```
Against the ticket's mathematics (design `T2398-design.md` §3.3, ticket target 2):
- `BACtx` = "Γ normal" ∧ H1 (atom(v) internal; exactly two solid edges meet it — `BARCand` forces `p.1`, `q.1` to meet `v`, so count 2 = exactly these) ∧ H2 (three pairwise `≠`) ∧ H3 (disjunction). "One charge": `BARCand.hpσ/hqσ`. `v` internal follows from H1. Matches.
- Lemma: every term of `gg2`/`gg4` of the candidate's charge (`BAExpandId_ggL2/4 c.σ`: blue lists, conjugate lists at `σ = false`) has `ordG ≥ ord P + 1`; `scalingOrderG` is the min over the `G = Ǧ + M` partition (`BAGraph.le_scalingOrderG_iff : ↑k ≤ Γ.scalingOrderG ↔ ∀ P ∈ Γ.partition, k ≤ P.scalingOrder`). Both charges, quantified over every `P`, `c`: the general statement, not a special case. Kids form verbatim as target 2.
- Quantifier order/loss: `+1`, no constant, no smallness, no scalar data (C1).
- `BAselStar` (Q3-C2): selects only candidates with `c.σ = true ∧ BACtx c` (a subset of `BACtx`); not widened to V2/V3. Blue-only is the probe's pin; red candidates are covered by the Lemma.
- Q3-C1: no theorem concludes `BAG5Expand`/`BAG5LeafProps` of a tree or a root list (grep `BAexpandRoot|baG5Graph|BAG5Expand'|BAG5Fuel`: one hit, line 16, docstring). The only `BAG5LeafProps` conclusion is the singleton instance `fun _ _ => [baAllMP]`. `BAselStar` returns `none` off leaves when no candidate exists, so nothing forecloses an extra leaf class or step type.
- `BARCand` fields (`#print`): `σ v p q hp hq hpσ hpc hqσ hqc hpv hqv` — the merged L4d candidate data; no H1–H3 field hidden there, and `BACtx` is an explicit hypothesis.
Verdict on statements: match pins and ticket mathematics within the amended scope.

## 3. Compiled nonempty instances (same file, `namespace BAG5LeafInst`)
| endpoint | instance | data / hypotheses discharged |
|---|---|---|
| `baG5CtxLemma_holds` | `baG5CtxLemma_inst` (both charges) | `instP` (merged, `E' = Fin 2`, `I' = Fin 3`, 5 solid edges, `ord 3` by `instP_ord`), `instCand`/`instCandRed`; `BACtx` by `instCtx` (`decide`/`decide +kernel`); conclusion `ordG ≥ 4` |
| `baG5CtxKids_holds` | `baG5CtxKids_inst` | same; `instCand.kids.length = 63`, `instCandRed.kids.length = 63` (nonempty lists), every kid `ord ≥ 4` |
| `baselStar_spec`, `baselStar_eq_none_iff` | `baselStar_inst`, `baAllM_leaf` | `¬BAG5Leaf instP` by `decide +kernel`; `BAselStar instP = some c` with `BACtx c`; at `baAllMP` (ord 4, `x ~ y`) leaf and `BAselStar = none` |
| pins | `baAllM_leaf`, `baG5Attached_inst` | `BAG5Leaf`, `BAG5LeafProps` at `[baAllMP]`; `BAG5Attached instP` holds and fails when one crossing edge is removed |
No `N = 0`, empty index, collapsed list or `False` premise; no external hypothesis, so no limit check applies. Control `baG5Ctx_H3_needed`: at merged `baGGLhs` H1, H2 hold, H3 fails and a `gg2` term has `ordG < ord Γ + 1` (the hypothesis is not decorative).

## 4. Paper deltas
```
$ grep -nE "T2398a|T2398b" docs/supervisor/requests/REQ-2026-10-11-0845-L4.md
49:Candidates with temporary tags: … `T2398a`–`d` … They are entered in the paper-delta register when the rows that prove them merge …
$ grep -nE "T2398a|T2398b|T2433" docs/paper-deltas.md
(no hits)
```
Lean/paper statement differences in this file: (1) `BAG5Tgt` = `ord ≥ 5 − 2·1[x ~ y]` vs `B:92` pointwise — T2398a (report (d), carried as pin; compiled witness `baAllM_leaf`); (2) `(eq:GGraisesord)` (`B:99`) only under H1–H3 — T2398b (report (d), proved here by `baG5CtxLemma_holds`). Further candidates T2433a (attachment by Even+Connected, stated NOT proved here), T2433b (`T3C-tr` configuration), T2433c (observation: `atom v ≠ atom y'` unused). Coverage complete; numbering is the dispatcher's.

## 5. Observations (no RETURN)
- O1. Prove report is 433 lines (`wc -l`): above CLAUDE.md §6's 300 and the ticket's 250; the report says so itself ((b) item 7). Changes no statement, instance, build or axiom.
- O2. Pins `BAG5Fuel`, `BAG5Expand'` of the probe are not in the file and `BAG5Leaf2.lean` is not created: consistent with Amend 1 (target 4 and the closure dropped; file 2 may stay unused).
- O3. T2433c: the inequality `atom v ≠ atom y'` of `BACtx` is unused by the proof (destructured as `-`, line 929); the pin is unchanged, weakening it is the dispatcher's call.
- O4. Ticket instances `baG5Expand'_holds 3` and `BAexpandRoot BAselStar F k s ≠ []` are not delivered: both are about `baG5Graph` / target 4, dropped by Amend 1 and H234.
- O5. Consumers: a later theorem assuming `BAG5Leaf`/`BAG5Tgt`/`BACtx`/`BAG5Attached` will need a registry line (report (d) note 1); not this ticket's obligation (premise scan above is clean).

## Verdict
| target (amended scope) | verdict |
|---|---|
| 1 pins `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand`, `BAG5Attached`, `BAG5LeafProps`, `BACtx`, `BAG5CtxLemma`, `BAG5CtxKids` | PASS |
| 2 `baG5CtxLemma_holds` (both charges), `baG5CtxKids_holds` | PASS |
| 3 `BAselStar` (`baselStar_spec`, `baselStar_eq_none_iff`; Q3-C1, Q3-C2 respected) | PASS |
| 4 dropped (Amend 1) | — |
| 5 instances, 6 C1, 7 registry (none; premise scan clean) | PASS |
**Ticket T2433: PASS.** No dispatcher sign-off needed.
