Auditor model: claude-opus-5-5

# T2318 audit, round 1 (LW-14e-4 Sound; ticket + Amend 1), Thu Oct  8 11:54:50 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2318-audit1`, detached at `t/T2318` = `4eda3d2` (merge-base with `main` = `7b9fefe` = `main`).
Scratch: `scratchpad/T2318/` (`pin.lean`, `pin_neg.lean`, `precheck.lean`, `build.log`, `sim.diff`).
## 1. Files touched, `LWExpSim.lean` diff, hygiene
```
$ git diff --name-only main...t/T2318
RBM3D/Graph/LWExpSim.lean
RBM3D/Graph/LWExpSound.lean
RBM3D/Test/Axioms.lean
$ git diff -U0 main...t/T2318 -- RBM3D/Graph/LWExpSim.lean > sim.diff; python3 (removed vs added lines)
29 29
all removed = added with 'private ' token: True
hunks 29 all 1-line: True
un-privated (29): lwExpSim_vi_lt lwExpSim_vi_inj lwExpSim_vi_inr lwExpSim_R lwExpSim_LabsGood lwExpSim_good_unite
 lwExpSim_labsOf_good lwExpSim_labs lwExpSim_labs_good lwExpSim_test_iff lwExpSim_cMerge_none lwExpSim_cMerge_some
 lwExpSim_equivs lwExpSim_cls_relabel lwExpSim_consistent_relabel lwExpSim_splitLoopsX_map lwExpSim_vmap_inl lwExpSim_real
 lwExpSim_model lwExpSim_R0 lwExpSim_sBetween_relabel lwExpSim_xBetween_relabel lwExpSim_dotBase_relabel
 lwExpSim_dotChoices_relabel lwExpSim_terms_relabel lwExpSim_forall₂_flatMap lwExpSim_partition_sim lwExpSim_relabel_refl
 lwExpSim_forall₂_flatMap_same
$ grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b|implemented_by|@\[extern' LWExpSound.lean LWExpSim.lean
(no output)
$ grep -nE '^\s*(structure|class|instance|axiom|opaque|unsafe)' LWExpSound.lean
(no output; only linter `set_option`s at :23-30)
$ grep -nP "\b(cert_all|cert_FF|cert_FT|belowOf|childrenB|goodB|goodB_succ_of|rootInfo|rootAt|kidsOk|kids|kid)\b(?!')" LWExpSound.lean | grep -v '\.kids'
1453: (doc comment: "`5` choices that `belowOf` skipped and `belowOf'` evaluates ...")
1468: (doc comment: "Instance of `soundStep` at the first kid ...")
$ grep -n '^import' LWExpSound.lean   ->  RBM3D.Graph.LWExpSim, RBM3D.Graph.LWExpCertBS0, RBM3D.Graph.LWExpCertBS1
```
Every remaining `kids` occurrence is `.kids` (`RCand.kids`, T2307), checked by reading; the unprimed T2306 certificate is unused.
Name clash (`grep -rnE "(theorem|def|abbrev|lemma|structure) +<name>( |$)" RBM3D` outside `LWExpSound.lean`, `RBM3D/Probe`):
0 for each of the 22 new public non-`lwExpSound_` names; `lwExpSound_` occurs in no other file.

## 2. Build and axioms
```
$ /usr/bin/time -l lake build RBM3D.Graph.LWExpSound
⚠ [3884/3888] Replayed RBM3D.Graph.LWExpCertB
⚠ [3885/3888] Replayed RBM3D.Graph.LWExpCertBS0
⚠ [3886/3888] Replayed RBM3D.Graph.LWExpCertBS1
✔ [3887/3888] Built RBM3D.Graph.LWExpSim (5.6s)
ℹ [3888/3888] Built RBM3D.Graph.LWExpSound (15s)
info: RBM3D/Graph/LWExpSound.lean:1318:0: '_private...lwExpSound_key_FF' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Graph/LWExpSound.lean:1319:0: '_private...lwExpSound_key_FT' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3888 jobs).
       23.89 real        28.82 user         6.65 sys
          4110450688  maximum resident set size
exit 0      ($ grep -c '^error' build.log -> 0)
```
Certificate modules replayed, not rebuilt (H101). `#print axioms` (scratch `pin.lean`, below):
```
'RBM.Gauss.Sizes.lwG5Expand'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwG5LeafProps_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.relKids' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.relInvariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.belowOfSound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.soundStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.soundRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpSound_inst_relKids' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpSound_inst_belowOfSound_R2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpSound_inst_leafOK_R2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpSound_inst_leafProps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (revised check file, Amend 1) and T2265's `LWG5Expand'Pin`
`pin.lean` = `import RBM3D.Graph.LWExpSound` + sections 2-3 of `docs/tickets/checks/T2318-check.lean` copied by `sed` (lines from
`namespace T2318Check` to before `## 4.`) + `LWJoinedPin` and `LWG5Expand'Pin` copied from `T2265-check.lean:190-191, 197-207`; then
11 `Iff.rfl` examples (`T2318Check.X ↔ RBM.Gauss.Sizes.X` for LWG5LeafProps, LWG5ExpandSplit, LWG5Expand', LWG5Expand'Pin↔LWG5Expand',
LWG5ExpandOfHalves, RelInvariance, LeafOK, SoundStep, SoundRoot, RelKids, BelowOfSound) and 12 examples applying the targets at the pinned
Props (`relInvariance`, `relKids`, `belowOfSound`, `soundStep`, `soundRoot`, `lwG5LeafProps_holds`, `lwG5ExpandOfHalves`,
`@lwG5Expand'_holds : ∀ d, T2318Check.LWG5Expand'Pin d`, `lwG5ExpandSplit_iff`, `lwG5LeafProps_iff`, `@Rel.ext_surj`, `goodB'_mono`).
```
$ lake env lean pin.lean            -> exit 0 (only the #print axioms lines above)
$ sed 's/P.g.Normal ∧ P.g.nM ≤ 1/P.g.Normal ∧ P.g.nM ≤ 2/' pin.lean > pin_neg.lean; lake env lean pin_neg.lean
pin_neg.lean:117:74: error: Type mismatch   (and 7 more `Type mismatch` lines: 118, 119, 121, 124, 125, 126, 131)
```
So all ten pinned/new Props are verbatim (definitional) copies of the revised check file, with `belowOf'`/`childrenB'`/`rootInfo'`
where Amend 1 puts them, and `lwG5Expand'_holds` is exactly T2265's pin `∀ d, LWG5Expand'Pin d`. `BelowOfSound` is general
(`∀ a b Δ ext`, only `Function.Surjective ext` and the flag, no b-edge-free hypothesis); `SoundRoot` is `∀ k s` (k = true covered).

Dependencies (signatures read): `lwExpandIdentity_holds : ∀ (sel : Sel) (fuel : ℕ), LWExpandIdentity sel fuel` (`LWExpTerm5.lean:594`,
unconditional); `cert_all' : ∀ s, (rootInfo' false s).1 = true ∧ (rootInfo' false s).2.all (goodB' 3) = true` (`LWExpCertBS1.lean:583`);
`Rel` (`LWExpSim.lean:120`) is a `def` with existential equivalences, no structure field; `partitionSim`, `childrenSim`, `rel_self` merged.
The assembly (`:1393-1409`): `lwG5LeafProps_holds` from `cert_all'`, `soundRoot`, `goodB'_mono 3`, and the private induction
`lwExpSound_expand` (uses `relKids`, `belowOfSound` via `lwExpSound_childSound`, `Rel.leaf_iff`); `lwG5Expand'_holds d :=
lwG5ExpandOfHalves (lwExpandIdentity_holds selClassical 4) lwG5LeafProps_holds d`. No hypothesis on any public target; no cycle
(the targets only use merged results and earlier lines of the same file). No external hypothesis (combinatorial ticket).

## 4. Compiled nonempty instances (file section 10, `:1413-1488`; all compile in the build above)
| endpoint | instance (line) | data |
|---|---|---|
| `lwG5Expand'_holds` | `example : LWG5Expand' 3` (:1429) | `d = 3` |
| `relInvariance` | `example := relInvariance lwExpSound_N _ _ (rel_self …)` (:1433) | `N = rootAt' false false 9` |
| `relKids` | `theorem lwExpSound_inst_relKids` (:1436): `∃ c ∈ cands N.g, Forall₂ … ∧ kids.length = (childrenX N c).length` | `c' = Cand.toR N h (cands N.g)[0]`; nondegeneracy example :1423 by `decide +kernel`: `a = 0, b = 3, ord 2, tgt 4, #cands 3, #childrenX 533` |
| `belowOfSound` | root (:1446 leaf term `[0]`, :1448 below-target term `[95]`), flag `root_FF_shape'.1`; R2 family (:1455 `lwExpSound_inst_belowOfSound_R2`, :1460 `lwExpSound_inst_leafOK_R2 : LeafOK (r.2.toP _)` via `rel_self`; :1463 below-target term `[8]`) | `f = (fams N.g c)[0]`, `ext = N.ext` (surjective by `decide +kernel`), flag `(belowOf' f N.ext).1` and `leaf` by `decide +kernel`; term `[2]` has `b = 1`, `ord = 7` (:1423), i.e. the merged-b-edge choice (old `belowOf` skipped it) |
| `soundStep` | `example := soundStep N h c _ (by decide +kernel) (kids[0]) _` (:1469) | flag `(childrenB' N c).1` by kernel |
| `soundRoot` | `example (k : Bool) := soundRoot k false cert_FF'.1 ((partitionX (LWG5Graph k false))[0]) _` (:1475) | both `k` (bound by `cases k <;> decide +kernel`) |
| `lwG5LeafProps_holds` | `theorem lwExpSound_inst_leafProps : ∃ q ∈ expandRoot selClassical 4 false false, LeafOK q.2` (:1479) | membership of a real leaf exhibited |
| kernel facts L8 (d) | `lwExpSound_key_FF`, `lwExpSound_key_FT` (:1306-1316), `decide +kernel`, axioms printed in §2 | 163 terms per `s` |
| `lwG5ExpandSplit_iff`, `lwG5LeafProps_iff`, `lwG5ExpandOfHalves` | `example := And.intro (… 3) (…)` (:1430) | `Iff.rfl` / definitional |

No `N = 0`, empty list, collapsed window, `False` premise. Every deterministic hypothesis is discharged.
## 5. Registry (`RBM3D/Test/Axioms.lean`)
```
$ git diff main...t/T2318 -- RBM3D/Test/Axioms.lean   (summary of the three hunks)
-  owedProps:        `RBM.Gauss.Sizes.LWG5Expand, -- `(eq:sizeGammamu_E)`, `B:91-108`: …
+  structuralProps:  `RBM.Graph.LGraph.IsExtCls, -- a class of `=`-dotted vertices contains an external vertex (`dot-def`, `7_8:222`; T2050):
                      a defining predicate of the merged graph, hypothesis of `lwExpSim_equivs` (T2311), public since T2318
+  supersededProps:  `RBM.Gauss.Sizes.LWG5Expand]  -- superseded by `LWG5Expand'` (proved, T2318): … (ticket comment verbatim)
$ lake build RBM3D.Test.Axioms  -> ✔ Built (2.0s)
$ printf 'import RBM3D\nimport RBM3D.Graph.LWExpSound\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean
exit 0
axiom audit: 9953 theorems, 2994 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: …
premises found by scanning: 145 (borrowed 1, owed 83, structural 42, refuted 6, superseded 13).
```
`LWG5Expand` move: as the ticket says (`LWtermEXP`, `LWCutExp`, `LWExpG5'` stay owed). `IsExtCls`
(`LWVocab.lean:741`: `def LGraph.IsExtCls (Γ) (q : Γ.Cls) : Prop := ∃ a : E, Γ.cls (Sum.inl a) = q`) is a defining predicate. It is a
premise only because `lwExpSim_equivs` (hypothesis `h3`, `LWExpSim.lean:694`) is public now, after the permitted `private` deletion.
**The ticket says: "if it lists anything else, report and ask (no owed line without the dispatcher)".** The prover reported it
(prove report (d) 1) and wrote a *structural* (not owed) line instead of waiting. The classification looks correct to me (same kind as
`IsExtMol`, `XBetween`), but the ticket leaves this decision to the dispatcher: **needs dispatcher sign-off** for this one registry line.
Without it the merge's `#assert_rbm_axioms` fails (prover's pre-check on main's registry: exit 1, `[RBM.Graph.LGraph.IsExtCls]`).
The other option (a private copy of `lwExpSim_equivs` in `LWExpSound.lean`, so `lwExpSim_equivs` stays private) would also stay within the file cap.

## 6. Paper deltas
The targets formalize the soundness of a finite check (paper-delta T2288e). The Lean statements add no hypothesis, loss or range
that the paper's `(eq:sizeGammamu_E)` (`B:92-94`) does not have. The leaf properties are the six conjuncts of T2265's pin. The colour-blindness of `Rel` matches
`7_8:134-139, 172, 238-272` and `B:442-448` (ticket O2 check). Prove report (d) 5: candidates none. I found no Lean/paper difference that is not covered.

## 7. Observations (not defects)
- O1. `LWExpSound.lean` is 1490 lines, just under the 1500 cap; the preset cut was not taken.
- O2. The `soundRoot` instance is one `example (k : Bool)` and not two separate applications. Both `k` are discharged (`cases k`).
- O3. `RBM3D.Test.Axioms` was rebuilt in this audit worktree for the pre-check; no certificate module was rebuilt.

## 8. Verdicts
| target | verdict |
|---|---|
| 1 `relInvariance` | PASS |
| 2 `relKids` (+ `Rel.ext_surj`, `goodB'_mono`) | PASS |
| 3 `belowOfSound` | PASS |
| 4 `soundStep` | PASS |
| 5 `soundRoot` | PASS |
| 6 `lwG5LeafProps_holds` | PASS |
| 7 `lwG5ExpandSplit_iff`, `lwG5LeafProps_iff`, `lwG5ExpandOfHalves` | PASS |
| 8 `lwG5Expand'_holds` | PASS |
| registry line `RBM.Graph.LGraph.IsExtCls` in `structuralProps` | needs dispatcher sign-off (ticket: "report and ask") |

Overall: **PASS on all targets; needs dispatcher sign-off** for the `IsExtCls` structural registry line (§5) before merge.
