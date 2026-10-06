Auditor model: claude-opus-5-5

# T2264 audit (round 1): LW-12e `AnpKey5`, Tue Oct  6 07:36:08 UTC 2026

Branch `t/T2264` at `c21b6c0`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2264-audit1` (detached). Scratch: `<scratchpad>/T2264/audit1/`.
Targets: `anpKey5_cert : AnpKey5CertPin` (endpoint) and intermediate pins `anpKey5_cross_ge`, `anpKey5_inside_ge`, `anpKey5_graph`.

## 1. Statements against the pins (check file section 2, verbatim up to names)

`conf.lean` = `import RBM3D.Graph.AnpKey5` + check-file lines 98-246 (section 2 and 3 verbatim, namespace `RBM.Graph.T2264Check`) + these audit lines:
```
example : @inSPin = @anpKey5_inS := rfl            -- likewise crossPin, crossAtPin, insidePin, earlyPin,
example : @sumOrderPin = @AnpSumOrder := rfl       -- restPin, perPathPin (8 vocabulary names, all rfl)
example : figIVext = anpKey5_figIVext := rfl       -- and piIV = anpKey5_piIV, resAux = anpKey5_resAux
theorem audit_sumCert_iff {p q : ℕ} : ∀ (n : ℕ) (E : List (NV p q × NV p q)), sumCertPin n E ↔ AnpSumCert n E
  | 0, E => Iff.rfl
  | n + 1, E => by simp only [sumCertPin, AnpSumCert, audit_sumCert_iff n]; exact Iff.rfl
example : AnpKey5CrossPin := @anpKey5_cross_ge
example : AnpKey5InnerPin := @anpKey5_inside_ge
example : AnpKey5CertPin := fun p q Γ M hN hM =>
  let ⟨n, h⟩ := anpKey5_cert p q Γ M hN hM; ⟨n, (audit_sumCert_iff n _).2 h⟩
example : AnpKey5GraphPin := fun p q E h1 h2 h3 =>
  let ⟨n, h⟩ := anpKey5_graph p q E h1 h2 h3; ⟨n, (audit_sumCert_iff n _).2 h⟩
-- plus the four Prop shapes of check-file section 3, each closed by the file's instance theorem
```
```
$ lake env lean <scratch>/conf.lean; echo exit=$?
'RBM.Graph.anpKey5_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_cross_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inside_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_figIVext' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_resAux' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_figAuxGh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_figIVext_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey5_inst_cross_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
`AnpSumCert` vs `sumCertPin` is not `rfl` (two separate structural recursions) but is proved equivalent by the one-line induction above, so all four pins are discharged exactly, with no added hypothesis. Token diff of the code (comments stripped, names substituted) of check-file `:104-150` vs `AnpKey5.lean:58-108`: only docstring words and `section Vocab` differ (script `difflib`, 0 code-token differences).

Statements in the file (`sed -n '931,934p;1250,1252p;1268,1271p'`):
```
theorem anpKey5_graph : ∀ (p q : ℕ) (E : List (NV p q × NV p q)), (∀ e ∈ E, e.1 ≠ e.2) →
    (∀ S : Finset (Fin q), S.card ≤ anpKey5_cross E S) →
    (∀ S : Finset (Fin q), (∀ v ∈ S, anpKey5_crossAt E S v ≤ 1) → S.card ≤ anpKey5_inside E S) →
    ∃ n : ℕ, AnpSumCert n E := by
theorem anpKey5_cross_ge : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∀ S : Finset (Fin q), S.card ≤ anpKey5_cross (anpKey5_rest Γ M) S := by
theorem anpKey5_inside_ge : ∀ (p q : ℕ) (Γ : NGraph p q) (M : Finset (Fin Γ.es.length)), Γ.IsNested →
    anpKey5_perPath Γ M → ∀ S : Finset (Fin q),
      (∀ v ∈ S, anpKey5_crossAt (anpKey5_rest Γ M) S v ≤ 1) →
        S.card ≤ anpKey5_inside (anpKey5_rest Γ M) S := by
```
`anpKey5_cert` (`:1327`): `∀ p q Γ M, Γ.IsNested → anpKey5_perPath Γ M → ∃ n, AnpSumCert n (anpKey5_rest Γ M)`: the pin. No quantifier reordering; no `GhostOK`, region, `NoA2`, case or `AnpIH` hypothesis (general, not a special case).

## 2. Hidden hypotheses, vacuity, cycles

- Hypotheses are `IsNested` (merged `LWVocab.lean`, a 6-conjunct Prop, no structure fields carrying assumptions) and `anpKey5_perPath` (a decidable data condition on `(Γ, M)`), both satisfied at the concrete instances below. No external hypothesis (no limit check owed).
- Imports: `RBM3D.Graph.AnpKey3` and five Mathlib modules only (`grep -n "^import"`: lines 6-11); no `import RBM3D`. Dependencies are merged (`git diff --stat main...HEAD -- AnpKey.lean AnpKey2.lean AnpKey3.lean LWVocab.lean`: empty). No cycle.
- Non-vacuity of `IsNested`: `anpKey5_figIVext` (p=2, q=1) and `figAux` (p=q=2) both satisfy it by `decide +kernel` in the instances.

## 3. Compiled nonempty instances (`AnpKey5.lean:1347-1425`, Section 8)

| ticket item | theorem | data | hypotheses discharged |
|---|---|---|---|
| (1) | `anpKey5_inst_figIVext` | `figIVext`, p=2, q=1, 6 edges | GhostOK, IsNested, NoA2, ¬CaseI, ¬CaseIII, degS=3, ordN=2, nngh=0, `AnpSumOrder … [0]`; all `decide +kernel` |
| (2) | `anpKey5_inst_resAux` | `figAux`, M=`{0,5}` | perPath; no order among both permutations; `AnpSumCert 1` with pair `0`,`3`, orders `[0,1]`,`[1,0]` |
| (3) | `anpKey5_inst_figAuxGh` | `anpKey2_figAuxGh`, M=∅ | perPath by `decide +kernel`, nested by merged `anpKey2_figAuxGh_nested`; applies `anpKey5_cert` |
| (4) | `anpKey5_inst_figIVext_cert` | `figIVext`, M=∅ | perPath; applies `anpKey5_cert` with `IsNested` from (1); `¬perPath` with edge 1 reserved |
| intermediate | `anpKey5_inst_cross_inside` | `figAux`, M=`{0,5}` | applies `anpKey5_cross_ge`, `anpKey5_inside_ge` (crossAt premise by decide), `anpKey5_graph` (all three premises by decide) |

No `N = 0`, empty index or `False` premise; `q ≥ 1`, `p ≥ 2`, edge lists nonempty. All compile (build below) and their shapes match check-file section 3 (`conf.lean`, exit 0).

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Graph.AnpKey5 2>&1 | tail -2; grep -c "AnpKey5" <build log>
✔ [3349/3349] Built RBM3D.Graph.AnpKey5 (9.0s)
Build completed successfully (3349 jobs).
1            # the only AnpKey5 line is the ✔ line: no warning or error in AnpKey5.lean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^import RBM3D$" RBM3D/Graph/AnpKey5.lean | wc -l
       0
$ git diff --name-status main...HEAD
A	RBM3D/Graph/AnpKey5.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep -cE '^-[^-]'      # deletions
0
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep '^+ ' | cut -c1-110
+   `RBM.Graph.anpKey5_perPath, -- every path of a nested graph has at most one edge that is a ghost or in
$ lake build RBM3D RBM3D.Test.Axioms | grep -E "error:|Build completed"; lake env lean reg.lean > reg2.out; echo exit=$?
Build completed successfully (4070 jobs).
exit=0      # reg.lean = import RBM3D; import RBM3D.Graph.AnpKey5; import RBM3D.Test.Axioms; #assert_rbm_axioms
$ head -3 reg.out
axiom audit: 7806 theorems, 2599 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
$ grep -ciE "error|anpKey5" reg2.out
0           # anpKey5_perPath is registered (structuralProps, :309); no unregistered premise reported
$ wc -l RBM3D/Graph/AnpKey5.lean
    1427    # below the ticket's 1500-line split threshold
```
Axioms of the four targets and five instances: the three standard ones only (section 1 output). Frozen signatures: no merged file touched. Registry: one addition to `structuralProps`, no deletion (as the ticket requires; `AnpDetGhCaseIV` stays).

Name clash (`anpKey5_|AnpSumOrder|AnpSumCert` in `*.lean` of the audit worktree and main worktree, excluding `AnpKey5.lean`; and `docs/tickets/T226*.md`, `checks/T226*`):
```
RBM3D/Test/Axioms.lean:309:   `RBM.Graph.anpKey5_perPath, -- every path of a nested graph has at most one edge
/Users/junyin/Lean_proof/RBM3D/docs/tickets/T2264.md
/Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2264-check.lean
```
Only this ticket's own registry line and ticket files. All 112 public declarations carry the `anpKey5_` prefix or a pinned name (`AnpSumOrder`, `AnpSumCert`) (rule (E)).

## 5. Paper deltas

The Lean statements differ from `7_8:1385-1451` exactly where the ticket's route says; the prove report §(d) proposes:
- T2264a: the pigeonhole `7_8:1388-1393` (`q = p`, one B1 per vertex, B2 per path) fails (`anpKey5_figIVext`, compiled: GhostOK, IsNested, NoA2, ¬CaseI, ¬CaseIII, q=1<p=2); replaced by Hall crossing bound.
- T2264b: `(eq:degali)` replaced by `anpKey5_inside_ge`.
- T2264c: re-rooting (i)-(iii) `:1440-1449` replaced by one AM-GM split at a non-bridge pair.
- T2264d: the order exists for every nested graph with `perPath` (no case analysis).
These cover all four expected candidates (a)-(d) of the ticket. `grep -n T2264 docs/paper-deltas.md`: no hits yet (to be appended by the dispatcher). Complete coverage.

## 6. Observations (no verdict impact)

- `anpKey5_decIsNested` (`:1347`) is a global `Decidable Γ.IsNested` instance for every `NGraph`; it coexists with merged `LWVocab.lean:384` (`figAux` only). Harmless (Prop-valued decidability), but downstream files importing `AnpKey5` will see it.
- The ticket asked "each vocabulary `…Pin` shown `rfl`"; for `sumCertPin` this is an `Iff` by induction (not `rfl`); the report says so, and the audit reproduced the bridge (section 1).
- The prove report's `$ grep -c "anpKey5|anpKey2_stepOK"` note and inspections (a′) are consistent with what the audit reproduced.

## Verdict

| target | statement | hidden hyp / vacuity / cycle | instance | build / axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `anpKey5_cert` (`AnpKey5CertPin`) | = pin | none | (3), (4) | pass / 3 std | a-d | **PASS** |
| `anpKey5_cross_ge` (`AnpKey5CrossPin`) | = pin | none | `inst_cross_inside` | pass / 3 std | a | **PASS** |
| `anpKey5_inside_ge` (`AnpKey5InnerPin`) | = pin | none | `inst_cross_inside` | pass / 3 std | b | **PASS** |
| `anpKey5_graph` (`AnpKey5GraphPin`) | = pin | none | `inst_cross_inside` | pass / 3 std | c | **PASS** |

Ticket T2264: **PASS**. No dispatcher sign-off needed.
