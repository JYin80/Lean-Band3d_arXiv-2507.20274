Auditor model: claude-opus-5-5

# T2252 audit (round 1): LW-12c, `anpDetGhCaseI_holds`, Graph/AnpKey3

Written Tue Oct  6 04:56:47 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2252-audit1`, detached at `f6b9f8f` (`t/T2252`).

## Verdict: PASS (target `anpDetGhCaseI_holds`; instances (1)-(5) compiled)

## 1. Diff scope
```
$ git diff --name-status main...t/T2252
A	RBM3D/Graph/AnpKey3.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...t/T2252 | grep -c '^-[^-]'       # deleted lines
0
$ git diff main...t/T2252 -- RBM3D/Test/Axioms.lean   (added line only)
+   `RBM.Graph.AnpIH, -- the induction hypothesis of `AnpDetGhStep` (`7_8:1107`) for `k < q`, premise of the compiled instances of LW-12c (`anpKey3_inst_*`, T2252); proved inside `anpDetGh_of_step` (T2234) once LW-12f proves `AnpDetGhStep` (DECISIONS §20: owed)
$ grep -n "^import" RBM3D/Graph/AnpKey3.lean | grep -v Mathlib
6:import RBM3D.Graph.AnpKey2
```
Only the two sole writable files; `AnpKey2.lean` (where the pin `AnpDetGhCaseI` lives) is untouched, so the frozen pin is unchanged. No deletion in `Axioms.lean`.

## 2. Statement vs pin (script)
Check file section 2 and section 3 (`namespace RBM.Graph.T2252Check … end`) extracted by `sed` from `docs/tickets/checks/T2252-check.lean`, followed by these lines, in a scratch file importing `RBM3D.Graph.AnpKey3`:
```
example : AnpKey3CaseIHoldsPin := @anpDetGhCaseI_holds
example : figAuxMix = anpKey3_figAuxMix := rfl
example : piMix = anpKey3_pi := rfl
example : (AnpIH 3 2 → AnpDetGhRegAt 3 anpKey2_figAuxGh (fun _ _ => false)) := anpKey3_inst_figAuxGh
example : figAux.NoA2 piMix ∧ AnpCaseI figAux piMix ∧ (AnpIH 3 2 → AnpDetGhRegAt 3 figAux piMix) := anpKey3_inst_figAux
example : figAuxMix.GhostOK ∧ figAuxMix.IsNested ∧ figAuxMix.NoA2 piMix ∧ AnpCaseI figAuxMix piMix ∧
    (AnpIH 3 2 → AnpDetGhRegAt 3 figAuxMix piMix) := anpKey3_inst_figAuxMix
example : AnpDetGhCaseIII 3 → AnpDetGhCaseIV 3 → LWAnpKeyGh 3 := anpKey3_inst_chain
example : ∃ (p' : ℕ) (Γ'' : NGraph p' 1), Γ''.GhostOK ∧ Γ''.IsNested ∧
    Γ''.ordN = anpKey2_figAuxGh.ordN ∧ Γ''.nngh = anpKey2_figAuxGh.nngh := anpKey3_inst_gh2
#print axioms RBM.Graph.<each of the 9 names below>
```
```
$ lake env lean AuditPin.lean; echo "exit $?"
'RBM.Graph.anpDetGhCaseI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_figAuxGh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_figAux' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_figAuxMix' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_gh2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_types' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_figAuxGh_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey3_inst_figAux_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
The target elaborates exactly as `AnpKey3CaseIHoldsPin := ∀ d : ℕ, AnpDetGhCaseI d`, and all five instances have exactly the shapes in check-file section 3 (definitional equality via `example`). Target source (`AnpKey3.lean:431`): `theorem anpDetGhCaseI_holds : ∀ d : ℕ, AnpDetGhCaseI d`. The binder of `Γ.NoA2 π` is `_` (`intro d q hq hIH p Γ π hG hN _ hcase`), so NoA2 is unused, as the ticket expects.

Pin content checked against the merged `AnpKey2.lean:137-185` and `7_8:1152-1244`. The proof keeps:
- `d` arbitrary, with no `3 ≤ d`;
- `∀ q, 0 < q → AnpIH d q → ∀ p Γ π, GhostOK → IsNested → NoA2 → AnpCaseI → AnpDetGhRegAt`;
- inside `AnpDetGhRegAt`: `∃ C c` before `∀ L ψ θ ξ a b`, so `(C, c)` are uniform in `L` and `(a, b)` (§29 (5));
- the loss `θ^q ψ(0)^{ordN - nngh}` and `ψ(c·|a_i - b_i|)` on ghost-free paths, unweakened.

Cases (I)+(II) are proved together for any `i₀` and any `deg`. This is general, not a special case.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|^\s*(structure|class|instance)\b" RBM3D/Graph/AnpKey3.lean; echo $?
1
```
- No structure, class or instance is declared, so there are no hidden fields.
- Dependencies are merged: `AnpKey2` (T2242), `AnpKey` (T2234) and `LWVocab`.
- The target adds no premise beyond those of the pin.
- `AnpIH d q` belongs to the merged pin (the induction hypothesis). LW-12f discharges it via the merged `anpDetGh_of_step`, which consumes `AnpDetGhStep`, and that is built from this target through `anpDetGhRegStep_of_cases`. This is an induction, not a cycle: `AnpIH d q` covers only graphs with `k < q` internal vertices.
- No external hypothesis, so no limit check is needed.

## 4. Compiled nonempty instances (`AnpKey3.lean:565-714`)
| # | theorem | data | deterministic hypotheses discharged | premise left |
|---|---|---|---|---|
| 1 | `anpKey3_inst_figAuxGh` :590 | `d=3, p=q=2`, `figAuxGh`, `π≡false` (B1+B1) | `anpKey3_inst_figAuxGh_hyp` (GhostOK, IsNested, NoA2, AnpCaseI; from merged `anpKey2_inst_figAuxGh`) | `AnpIH 3 2` |
| 2 | `anpKey3_inst_figAux` :602 | `figAux`, `π₀ = fun i _ => decide (i=1)` (A1+A1) | `anpKey3_inst_figAux_hyp`: NoA2, AnpCaseI by `decide +kernel` | `AnpIH 3 2` |
| 3 | `anpKey3_inst_figAuxMix` :609 | `anpKey3_figAuxMix` (= check `figAuxMix`, `rfl`), `π₀` (B1+A1) | GhostOK, IsNested, NoA2, AnpCaseI by `decide +kernel` | `AnpIH 3 2` |
| 4 | `anpKey3_inst_chain` :620 | `d=3` | target applied in `anpKey2_inst_chain` | `AnpDetGhCaseIII 3`, `AnpDetGhCaseIV 3` (other gates' pins) |
| 5 | `anpKey3_inst_gh2` :659 | `figAuxGh` fixed at `i₀=0` via `anpKey2_fixV`, double ghostify | GhostOK, IsNested, `ordN''=ordN` (omega), `nngh''=nngh=0` | none |

All five instances apply the target (or its section-2 machinery for (5)) at concrete nondegenerate data: `p = q = 2`, `d = 3`, nonempty path sets. The only premises are other gates' pins (`AnpIH`, `AnpDetGhCaseIII/IV`), which the ticket allows. `anpKey3_inst_types` (:625) certifies the edge types B1+B1, A1+A1 and B1+A1 by `decide +kernel`. Instance (1) has `nngh = 0`, and instances (2) and (3) have ghost-free paths (`nngh = 2` and `1` per preflight), so the `ψ(c|a-b|)` factor is exercised.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.AnpKey3 > build.out 2>&1; echo "exit $?"
exit 0
$ grep -E "AnpKey3|error|Build completed" build.out
Build completed successfully (3348 jobs).
```
(The only warnings are style-linter warnings in upstream merged files: `Defs/Tail.lean`, `Green/LDEQuad.lean`.)

Registry pre-check (ticket acceptance; temporary file `import RBM3D` / `import RBM3D.Graph.AnpKey3` / `#assert_rbm_axioms`, kept in the scratchpad):
```
$ lake build RBM3D RBM3D.Test.Axioms; echo "build exit $?"
build exit 0
Build completed successfully (4056 jobs).
$ lake env lean RegPre.lean > reg.out 2>&1; echo "pre-check exit $?"
pre-check exit 0
$ grep -nE "error|axiom audit|premises found|AnpIH|AnpDetGhCaseI|^registry" reg.out | cut -c1-220
1:axiom audit: 7520 theorems, 2533 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
75:  RBM.Graph.AnpDetGhCaseI: 3 [no certificate]
76:  RBM.Graph.AnpDetGhCaseIII: 3 [no certificate]
77:  RBM.Graph.AnpDetGhCaseIV: 3 [no certificate]
78:  RBM.Graph.AnpIH: 3 [no certificate]
167:premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
168:registry: 2 borrowed + 158 owed + 98 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
199: RBM.Graph.AnpDetGhCaseI,
```
- Info (as the ticket foresees): `RBM.Graph.AnpDetGhCaseI` is registered but carries nothing. Its line stays until LW-12f.
- `AnpIH` is new as a theorem premise. On `main`, `git show main:RBM3D/Test/Axioms.lean | grep AnpIH` and `git grep -nE "AnpIH [0-9]+ [0-9]+ →" main -- RBM3D` both return nothing, so the instances' premise `AnpIH 3 2 →` makes the one added registry line necessary. That is within the ticket's "add only what the pre-check lists".

Name clashes: each of the 25 public names (`anpKey3_*` plus `anpDetGhCaseI_holds`) was grepped over the audit worktree's `RBM3D/` and main's `RBM3D/`, excluding `AnpKey3.lean` and `Axioms.lean`. Every name had 0 hits.
```
anpKey3_endAt_mem:0 anpKey3_end_solid:0 anpKey3_endAt_of:0 anpKey3_noGhost_single:0 anpKey3_gh2_props:0 anpKey3_endFactor:0
anpKey3_far_end:0 anpKey3_far_gen:0 anpKey3_far:0 anpKey3_prod:0 anpKey3_sum_xx:0 anpDetGhCaseI_holds:0 anpKey3_pi:0
anpKey3_figAuxMix:0 anpKey3_inst_figAuxGh_hyp:0 anpKey3_inst_figAuxGh:0 anpKey3_inst_figAux_hyp:0 anpKey3_inst_figAux:0
anpKey3_inst_figAuxMix:0 anpKey3_inst_chain:0 anpKey3_inst_types:0 anpKey3_fixV_ng_iff:0 anpKey3_figAuxGh_seg:0 anpKey3_inst_gh2:0
```

## 6. Paper deltas
The Lean statement is the merged pin `AnpDetGhCaseI`. Its statement-level differences from `lem:Anp_key_gh` are already recorded in `docs/paper-deltas.md`:
```
1512:- **D553（T2234a–d）**: `lem:Anp_key_gh` deterministic form …
1518:- **D559（T2242a–e）**: regions / ending-edge types as combinatorial data …
```
The proof-route differences of this ticket are proposed in prove report (d) as T2252a–e:
- (a) no auxiliary ghost path: the two one-step paths are made ghost instead;
- (b) both sides, `ξ(e_t, x)`;
- (c) `ord'' = ord` exactly, with only `nngh ≤ nngh''` proved and the surplus absorbed by `ψ(0)`;
- (d) `c ↦ c/2` and `2xy ≤ x² + y²`;
- (e) Cases (I) and (II) are one proof.

These match the ticket's expected list. No uncovered difference.

## 7. Observations (no effect on statement, instance, build, axioms, or delta coverage)
- O1: The new registry line classifies `RBM.Graph.AnpIH` as *owed*. It is a definitional induction hypothesis, not a paper claim, so the dispatcher may prefer *structural* (the prove report (d) says the same). This is bookkeeping only; the pre-check passes either way.
- O2: Step 5 does not use the ticket's fibrewise route. `anpKey3_prod` uses an injective choice `ρ` of one ghost-free segment per path. This is a proof-route difference only; the statement is unaffected.

## Per-target verdict
- `anpDetGhCaseI_holds : ∀ d : ℕ, AnpDetGhCaseI d`: **PASS**
- Instances (1)-(5): **PASS** (compiled, nondegenerate, only other gates' pins as premises)
- Needs dispatcher sign-off: no.
