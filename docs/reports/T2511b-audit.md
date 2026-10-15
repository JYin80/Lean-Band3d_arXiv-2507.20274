Auditor model: claude-opus-5-5

# T2511b audit (row b: targets 11-12 and the registry), round 1. Written Thu Oct 15 07:19:43 UTC 2026

Branch `t/T2511b` at 45c1b6db; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2511b-audit1` (detached at 45c1b6db).
Merge base = `main` = a082fcfe (row a and T2512 merged).

## 1. Diff scope
```
$ git diff --name-only main...t/T2511b
RBM3D.lean
RBM3D/BA/MainIndTermBA.lean
RBM3D/Test/Axioms.lean
$ git merge-base main t/T2511b; git rev-parse main
a082fcfeb139b1489c0b009255bddbc099c9fb10
a082fcfeb139b1489c0b009255bddbc099c9fb10
$ git diff --stat main...t/T2511b -- RBM3D/Chain RBM3D/Induction RBM3D/Graph RBM3D/BA/MainIndFamTL.lean RBM3D/BA/MainIndRegBA.lean RBM3D/BA/MainIndGlue.lean RBM3D/BA/MainIndOutBA.lean  # expect empty
$ wc -l RBM3D/BA/MainIndTermBA.lean   # stop line 200
     124 RBM3D/BA/MainIndTermBA.lean
```
`RBM3D.lean`: one line `+import RBM3D.BA.MainIndTermBA` after the last import, before `#assert_rbm_axioms`.
`Test/Axioms.lean` (hunks `@@ -134,13 +134,12`, `@@ -183,14 +182,14`, `@@ -221,7 +220,7`): `:140` `BAMainIndFamTL` deleted; owner texts naming T2511 / T2511b
on `:143` `STStep1WeakgL`, `:186` `STInitialGT2gL`, `:188` `BATwistAvgLaw`, `:192` `STStep2DecayPTgL`, `:193` `STGdecayWgL`, `:224` `STStep1LoopgL`;
`:139`, `:189`, `:194`, `:195`, `:226` untouched. The note "left this list (T2511b …)" is added to the comment line `:137` (see Observations).

## 2. Statements against the pins (scratch file, uncommitted)
Scratch `AuditT2511b.lean` = `import RBM3D.BA.MainIndTermBA` + the whole of `docs/tickets/checks/T2511-check.lean` (imports dropped) + the block below,
compiled in the audit worktree. The T2512 pins are copied verbatim from `docs/tickets/checks/T2512-check.lean:123-125, 184-186`.
```
namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
def Aud_T2512_OfRegimes (d : ℕ) : Prop :=
  BAMainIndFamTL d STReg5III → BAMainIndFamTL d STReg5I → BAMainIndFamTL d STReg5II → BAMainIndFamTL d STReg5IV →
    BAMainIndFamTL d STAny
def Aud_T2512_AnyD : Prop :=
  ∀ d : ℕ, STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny
example : T2511_Terminal := ⟨baMainIndFamTL_three, baMLOutTL_three, unMLOutBA_three⟩
example : T2511_AnyD := baMainIndFamTL_any
example : Aud_T2512_AnyD := baMainIndFamTL_any
example : T2511_AnyD = Aud_T2512_AnyD := rfl
example : Aud_T2512_OfRegimes 3 := baMainIndFamTL_of_regimes 3
example (d : ℕ) : Aud_T2512_OfRegimes d := baMainIndFamTL_of_regimes d
example : T2511_Closed := ⟨baMainIndFamTL_III, baMainIndFamTL_III_three, baMainIndFamTL_I, baMainIndFamTL_II, baMainIndFamTL_IV⟩
end RBM.BA
#print axioms RBM.BA.baMainIndFamTL_three
#print axioms RBM.BA.baMLOutTL_three
#print axioms RBM.BA.unMLOutBA_three
#print axioms RBM.BA.baMainIndFamTL_any
```
```
$ lake env lean AuditT2511b.lean > aud.out 2>&1; echo "exit $?"; grep -n error aud.out; grep -n "depends on axioms" aud.out
exit 0
'RBM.BA.baMainIndFamTL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMLOutTL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_any' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(Only unused-variable warnings in the check's pin texts.) The whole T2511 check compiles on this branch; the ticket's item `example : T2512_OfRegimes 3 := baMainIndFamTL_of_regimes 3` holds (also for every `d`).
Target statements in the file (extracted from the diff):
```
theorem baMainIndFamTL_three : BAMainIndFamTL 3 STAny :=
  baMainIndFamTL_of_regimes 3 baMainIndFamTL_III_three (baMainIndFamTL_I 3) (baMainIndFamTL_II 3) (baMainIndFamTL_IV 3)
theorem baMLOutTL_three : BAMLOutTL 3 := baMLOutTL_of_famStep 3 baMainIndFamTL_three
theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIndFamTL_three
theorem baMainIndFamTL_any : ∀ d : ℕ,
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny :=
  fun d h5 => baMainIndFamTL_of_regimes d (baMainIndFamTL_III d h5) (baMainIndFamTL_I d) (baMainIndFamTL_II d) (baMainIndFamTL_IV d)
```
Target 11 = `T2511_Terminal` (three theorems, exact types); target 12 = `T2511_AnyD` = `T2512_AnyD` (`rfl`). Binder order (iii), (i), (ii), (iv) as
`T2512_OfRegimes`. The targets are compositions of merged names only; `BAMainIndFamTL`, `BAMLOutTL`, `UNMLOutBA` are read by name, not restated.

## 3. Vacuity, hidden hypotheses, cycles
- `BAMainIndFamTL` (`BA/MainIndOutBA.lean:60`) is a `Prop` def, no structure fields; at `STAny` (`Induction/Step34Pins.lean:272`, `:= True`) the regime premise
  is trivial, so `BAMainIndFamTL 3 STAny` is the full, unrestricted family step (all `κ ε 𝔡 > 0`, all flows, windows `c₁ ∈ (0,1/2]`, `0 ≤ s < t ≤ T₀`).
- Target 11 has no hypotheses. Target 12's one hypothesis `STStep5IIIgL d` is the ticket's specified shape (Q4, DECISIONS §316, Jun decision B), discharged at
  `d = 3` by `baStep5III_holds` (limit check: the instance `baMainIndFamTL_any 3 baStep5III_holds` below compiles).
- No cycle: inputs `baMainIndFamTL_of_regimes` (merged T2512 a47cf1e1), `baMainIndFamTL_III/_III_three/_I/_II/_IV` (merged row a a082fcfe),
  `baMLOutTL_of_famStep`, `unMLOutBA_of_famStep` (merged T2504) do not import `MainIndTermBA`.
- V2O-C1: outside the new file, `BAMainIndFamTL 3 STAny` / `BAMLOutTL 3` / `UNMLOutBA 3` appear only as hypotheses/examples or comments:
```
$ grep -rnE 'BAMainIndFamTL 3 STAny|BAMLOutTL 3\b|UNMLOutBA 3\b' RBM3D | grep -v MainIndTermBA
MainIndOutBA.lean:334, :407 (doc/comment); :409 variable (hm : BAMainIndFamTL 3 STAny); :422 example := ... (baMLOutTL_of_famStep 3 hm) ...
MainIndGlue.lean:393 example (h : BAMainIndFamTL 3 STAny) ...; RandomLayerBGBA.lean:161/185 (doc), :162/:186 example (hML : UNMLOutBA 3) ...; UNPins.lean:1012 (doc)
```
(output lines condensed to one row per hit; no theorem concluding these exists elsewhere.)

## 4. Compiled nonempty instances (in `RBM3D/BA/MainIndTermBA.lean`, built)
Data `d = 3`, `sz0`, `zSeq`, `MainIndOutBA_flow` (`flow_sz0` at `κ = 1/4`), `(ε, 𝔡, 𝔠) = (1/10, 1/10, 1/6)`, `c₁ = 1/3`, `half_lt_t0`:
- target 11: `example : BAMainIndFamTL 3 STAny ∧ BAMLOutTL 3 ∧ Univ.UNMLOutBA 3`; `baMLOutTL_three` and `unMLOutBA_three` applied at `t ≡ 1/2` and `t ≡ 0`
  with every hypothesis discharged (`norm_num`, `le_rfl`, `half_lt_t0`) — hypothesis-free (the `hm` of `MainIndOutBA:409` is gone).
- target 12: `baMainIndFamTL_any 3 baStep5III_holds`; plugged into `baMLOutTL_of_famStep 3` at `t ≡ 1/2`; and applied at `s ≡ 0 < t ≡ 1/2`,
  member `BAzSrc sz0 zSeq (2/3) (17/25)`, with the induction hypothesis on `Fam(0)` discharged by `baFamMember_base` and `(con_st_ind)` by
  `s1Setup_conStInd_const` — fully hypothesis-free, concluding the seven conjuncts at a concrete member. A further `s ≡ 1/10` example keeps the
  induction hypothesis on `Fam(1/10)` as its one binder (supplementary; the hypothesis-free one above suffices).
Nondegenerate: `d = 3`, `0 < sz0.lam` (`sz0_lam_pos`), `s < t` strictly, window `c₁ = 1/3 ∈ (0, 1/2]`. Instances verdict: present, nondegenerate.

## 5. Build, axioms, hygiene
```
$ lake build RBM3D.BA.MainIndTermBA RBM3D.Test.Axioms; echo "exit $?"     # audit worktree
⚠ [4312/4312] Built RBM3D.BA.MainIndTermBA (6.2s)
warning: RBM3D/BA/MainIndTermBA.lean:13:100: This line exceeds the 100 character limit, please shorten it!   (docstring lines 13-21 only)
Build completed successfully (4312 jobs).
exit 0
$ lake build RBM3D; echo "exit $?"     # full library, runs #assert_rbm_axioms (supplementary; the hub reruns it at merge)
premises found by scanning: 128 (borrowed 1, owed 55, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 120 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
non-vacuity certificates: 0 of 122 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4418 jobs).
exit 0
$ grep -n BAMainIndFamTL full.log ; echo rc=$?
rc=1
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/MainIndTermBA.lean; echo rc=$?
rc=1
$ grep -nE "^(private )?(noncomputable )?(def|abbrev|structure|class|instance) " RBM3D/BA/MainIndTermBA.lean; echo rc=$?
rc=1
$ grep -nE "STIngR6gL|STStep6ConclgL|BATwistAvgLaw" RBM3D/BA/MainIndTermBA.lean; echo rc=$?
rc=1
$ grep -nE "mE|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT" RBM3D/BA/MainIndTermBA.lean; echo rc=$?
rc=1
$ grep -n withLam RBM3D/BA/MainIndTermBA.lean
54:    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
69:local notation "μ0" => Sizes.seqP (sz0.withLam 0)
$ grep -rnE "(theorem|lemma|def) (baMainIndFamTL_three|baMLOutTL_three|unMLOutBA_three|baMainIndFamTL_any)" RBM3D/
RBM3D/BA/MainIndTermBA.lean:40:theorem baMainIndFamTL_three : BAMainIndFamTL 3 STAny :=
RBM3D/BA/MainIndTermBA.lean:44:theorem baMLOutTL_three : BAMLOutTL 3 := baMLOutTL_of_famStep 3 baMainIndFamTL_three
RBM3D/BA/MainIndTermBA.lean:47:theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIndFamTL_three
RBM3D/BA/MainIndTermBA.lean:53:theorem baMainIndFamTL_any : ∀ d : ℕ,
```
Registry scan after the edit matches the prove report's "after" scan (owed 121 → 120, carry-nothing 162 → 161, `BAMainIndFamTL` absent; 0 new premises).
No frozen signature touched (no merged file in the diff except the registry list lines).

## 6. Paper deltas
- `BAMainIndFamTL` in family form with `0 < lam` and eventual conclusions: D536, D538 (existing).
- BA terminal proved at `d = 3` only; general `d` under `STStep5IIIgL d`: D723 (`docs/paper-deltas.md:1803`, Jun decision B).
- No further Lean/paper statement difference introduced by row b; the prove report's "no new candidate (`T2511ba`: none)" is consistent.

## 7. Observations (no RETURN)
- O1: the "left this list (T2511b …)" note is written on the comment line `Test/Axioms.lean:137` (with the other "left this list" notes of that
  block) rather than on one of the seven listed lines; this follows the file's convention and changes no statement or registry classification.

## Verdict
| target | statement | vacuity / hidden hyp. / cycle | instance | build / axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| 11 `baMainIndFamTL_three`, `baMLOutTL_three`, `unMLOutBA_three` | = `T2511_Terminal` | none | yes, hypothesis-free, `d = 3` | ok / std 3 | D536, D538, D723 | **PASS** |
| 12 `baMainIndFamTL_any` | = `T2511_AnyD` = `T2512_AnyD` | `STStep5IIIgL d` (ticket shape), discharged at `d = 3` | yes, hypothesis-free | ok / std 3 | D723 | **PASS** |
| registry (`Test/Axioms.lean`) | `:140` removed; six owner texts | scan 0 new premises | n/a | full build ok | n/a | **PASS** |

**T2511b: PASS.** No dispatcher sign-off needed.
