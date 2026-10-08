Auditor model: claude-opus-5-5

# T2315 audit (round 1) — BA-L2b2 `RBM3D/Graph/BAExpandWOrd.lean`

Audit time (`date -u`): Thu Oct  8 04:56:52 UTC 2026. Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2315-audit1`,
detached at `t/T2315` = `6dc5c58` (merge-base with `main` = `4a63165`). Scratch: scratchpad `T2315/audit/`.

## 1. Diff scope

```
$ git diff --stat main...t/T2315
 RBM3D/Graph/BAExpandWOrd.lean | 1005 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1005 insertions(+)
$ grep -n "^import" RBM3D/Graph/BAExpandWOrd.lean
6:import RBM3D.Graph.BAExpandW
```
Only the sole writable file is touched (new); `RBM3D/Test/Axioms.lean` untouched; no merged file changed, so no frozen
signature is touched. Imports exactly as the ticket requires.

## 2. Build and axioms

```
$ lake build RBM3D.Graph.BAExpandWOrd        (audit worktree; error lines: grep -c "^error" -> 0)
Build completed successfully (3780 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|axiom " RBM3D/Graph/BAExpandWOrd.lean     -> (no output)
$ grep -nE "unsafe|implemented_by|extern|opaque|ofReduceBool|sorryAx|@\[csimp" ...    -> grep exit 1 (no match)
```
`#print axioms` (in scratch `eq.lean`, `lake env lean`, exit 0):
```
'RBM.Graph.lanlwT1_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lanlwD_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lanlw_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lanlw_scalingOrderG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandWOrdInst.T2315_I3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandWOrdInst.T2315_I4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExpandWOrdInst.T2315_D' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Instances use kernel `decide` (not `native_decide`), consistent with the axiom list.

## 3. Statements against the pins (check file `docs/tickets/checks/T2315-check.lean`, section 2)

(a) Text diff (`stmtdiff.py`: body of `def T2315_<n> : Prop :=` vs text between `theorem <n> :` and `:= by`,
whitespace-normalised):
```
$ python3 -I stmtdiff.py docs/tickets/checks/T2315-check.lean RBM3D/Graph/BAExpandWOrd.lean
lanlwT1_counters identical
lanlwD_counters identical
lanlw_ord identical
lanlw_scalingOrderG identical
T2315_I3 identical
T2315_I4 identical
```
(b) Compile equality: scratch = check file (all imports, `#check` lines dropped) + `import RBM3D.Graph.BAExpandWOrd`, then
```
example : RBM.Graph.T2315Check.T2315_lanlwT1_counters := RBM.Graph.lanlwT1_counters
example : RBM.Graph.T2315Check.T2315_lanlwD_counters := RBM.Graph.lanlwD_counters
example : RBM.Graph.T2315Check.T2315_lanlw_ord := RBM.Graph.lanlw_ord
example : RBM.Graph.T2315Check.T2315_lanlw_scalingOrderG := RBM.Graph.lanlw_scalingOrderG
example : RBM.Graph.T2315Check.T2315_I3 := RBM.Graph.BAExpandWOrdInst.T2315_I3
example : RBM.Graph.T2315Check.T2315_I4 := RBM.Graph.BAExpandWOrdInst.T2315_I4
```
`lake env lean eq.lean` -> exit 0 (with the axiom lines of §2, no error).

(c) Mathematics. Hypotheses per target, read from the signatures:
- `lanlwT1_counters`, `lanlwD_counters`, `lanlw_ord`: `Fintype`/`DecidableEq` on `Ex`, `Ix`; `p ∈ lwSplit Γ.solid`;
  `p.1.σ = true`; `p.1.circ = true`; (`lanlwD`) `q ∈ lwSplit p.2`. No `Normal`: the ticket's fallback (C1) for
  non-normal `Γ` was not needed, and the statement is the stronger (general-Γ) form the pin fixes. Conclusion
  `counters = ⟨nS+1, nW+1, nA+1, nM, 0, 0⟩` / `scalingOrder = scalingOrder Γ + 1` = (C1) of the ticket, with
  `scalingOrder = ord counters = nS + 2(nW − nA)` (`BAVocab.lean:146`, `(eq:ordG_BA)` `B:353`).
- `lanlw_scalingOrderG`: additionally `Γ.Normal` (`BAVocab.lean:158`: no `=`-dotted edge, all solid edges circled);
  conclusion `(ord Γ : WithTop ℤ) ≤ Δ.scalingOrderG` for every `Δ ∈ lanlwTerms Γ p` = (C2). For normal `Γ`,
  `ord Γ = ordG Γ` (`scalingOrderG_of_normal`), so this is the paper's "order does not decrease" for `(eq:BE)`.
- Quantifier order: `Γ, p` then hypotheses then `∀ q`/`∀ Δ`, as pinned. No parameters, windows or exponents.
- `lanlwTerms` (`BAExpandW.lean:144`) = term 1 :: one derivative term per `q ∈ lwSplit p.2`: the statements cover
  every term of `(eq:BE)` (`B:361-363`), not a special case.
Verdict on statements: identical to the pins; general, not a special case.

## 4. Hidden hypotheses, vacuity, cycles

- No structure with Prop fields is introduced; the public declarations are exactly
```
757:theorem lanlwT1_counters :     769:theorem lanlwD_counters :     781:theorem lanlw_ord :
803:theorem lanlw_scalingOrderG :  871:theorem T2315_I3 :  896:theorem T2315_I4 :  938:theorem T2315_D :
```
  39 `private` declarations, all prefixed `BAExpandWOrd_` (grep of non-prefixed privates: empty).
- No external hypothesis (pure combinatorics); no analysis or limit hypotheses, so no TEAM §8 lesson 14 limit check
  is needed.
- Dependencies: only `RBM3D.Graph.BAExpandW` (merged, 8f90d6d) and what it imports; no cycle (new leaf module).
- Hypotheses satisfiable: see §5 (all discharged at concrete graphs). The unused hypotheses `p.1.σ = true`,
  `p.1.circ = true` (prove report (d)) make the theorems no weaker; they are pinned.

## 5. Compiled nonempty instances (same file, namespace `RBM.Graph.BAExpandWOrdInst`)

| endpoint | application | data | hypotheses discharged |
|---|---|---|---|
| `lanlwT1_counters` | `example` `:921` | `baGcxy` (`Ex = Fin 2`, `Ix = Fin 0`, one circled blue edge `x→y`) | `p ∈ lwSplit` by `simp`, σ/circ `rfl` |
| `lanlwD_counters` | `example` `:984` | `BAVocabInst.baGGLhs` (2 external, 1 internal vertex, 2 solid edges), `q` = other edge | `List.mem_cons_self`, `rfl` |
| `lanlw_ord` | `example` `:926` (baGcxy), `:991` (baGGLhs, includes a derivative term) | as above | as above |
| `lanlw_scalingOrderG` | `example` `:931` (baGcxy), `:996` (baGGLhs); also used inside `T2315_I3/I4/D` | as above | + `Normal` by `simp` |
| (I3) `T2315_I3` | theorem, statement = pin | `lanlwT1 baGcxy`: `⟨2,1,1,0,0,0⟩`, ord 2, ordG 1 | `decide`; ordG by `le_antisymm` of target 3 and an explicit split member |
| (I4) `T2315_I4` | theorem, statement = pin | `lanlwT1 baGcxx`: `⟨2,1,2,1,0,0⟩`, ord 0, ordG −1 | same |

None is degenerate: nonempty vertex types, nonempty edge lists, `lwSplit p.2 ≠ []` in the derivative case (an
application of `lanlwD_counters` at `baGcxy` would have been vacuous; the prover correctly used `baGGLhs`). The
concrete values (I3) and (I4) are non-trivial numerical checks of the definitions, and `T2315_D` (ordG 0 = ord Γ)
exhibits the tight case of (C2). All compile (build of §2).

## 6. Paper deltas

The targets are bookkeeping for `(eq:BE)` (`B:359-363`) under `(eq:ordG_BA)` and `def scalingBA` (`B:345-355`); the
paper states no counter lemma, and the Lean statements contradict nothing in it. The vocabulary readings they rest
on (`Normal` (ii) as "no `=`-dotted edge", molecules through `Ψ`/`M` edges) are already D599 (T2287a–b) in
`docs/paper-deltas.md:1558`; `lanlw` coefficients are covered by D402/D606. No new Lean/paper statement difference;
the prove report's "no candidate" is correct.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. `T2315_D` is an unpinned public name; it lives in namespace `RBM.Graph.BAExpandWOrdInst` (file stem in the
  namespace), consistent with the instance namespace the ticket fixes. Acceptable under §3 (E) as read here.
- O2. Prove report (b): the build/exit lines of the verification block are interleaved (`exit` / `0` on separate
  lines, an empty `exit`); the audit re-ran the build and the checks independently (§2–§3).
- O3. File size 1005 lines (ticket estimate 650/850/1200; stop rule 1500 not reached).
- O4. The full `lake build` / `#assert_rbm_axioms` is the hub's at merge (main has moved to `b582dab` since the
  merge-base `4a63165`).

## 8. Verdict

| target | verdict |
|---|---|
| 1 `lanlwT1_counters`, `lanlwD_counters` | PASS |
| 2 `lanlw_ord` | PASS |
| 3 `lanlw_scalingOrderG` | PASS |
| 4 `T2315_I3`, `T2315_I4` + applications | PASS |

Ticket T2315: **PASS**. No dispatcher sign-off needed.
