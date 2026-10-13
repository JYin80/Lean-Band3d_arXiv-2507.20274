Auditor model: claude-opus-5-5

# T2483b audit (L3d2b-2 of T2483: targets 6-10, `RBM3D/Graph/BAMomentExpGenB.lean`), round 1 — Tue Oct 13 04:17:16 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2483b-audit1`, detached at `t/T2483b` = `eead4288`. Ticket `docs/tickets/T2483.md`; check file
`docs/tickets/checks/T2483-check.lean`; prove report `docs/reports/T2483b-prove.md`; stage 1a = `docs/reports/T2483-prove.md` (a).

## 0. Diff, hygiene, scope
```
$ git diff --name-status main...t/T2483b          # merge-base 772b1ca1 (L3d2b-1)
A	RBM3D/Graph/BAMomentExpGenB.lean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom |^(structure|inductive|class) " RBM3D/Graph/BAMomentExpGenB.lean; echo $?
1
$ grep -rn "import RBM3D.Graph.BAMomentExpGenB" RBM3D RBM3D.lean; echo $?
1
$ grep -c BAShapePath RBM3D/Graph/BAMomentExpGenB.lean
0
$ grep -nw BAAnpAuxG RBM3D/Graph/BAMomentExpGenB.lean  (code lines only)
1202:def BALWMomentExpOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMomentExp d
1288 / 1294 / 1317: example (hAnp : BAAnpAuxG 3) ...      # instances only
$ git grep -n "def BAAnpAuxG" main -- RBM3D ; git grep -nE "(theorem|lemma) [^:]*:[^=]*BAAnpAuxG" main -- RBM3D
main:RBM3D/Graph/BAAuxGraph2B.lean:865:def BAAnpAuxG (d : ℕ) : Prop :=      # no proof on main: L3d1 not merged, target 9 as pinned
```
Only the sole writable file `Graph/BAMomentExpGenB.lean` is touched (the root import line is the hub's). No merged file edited, no frozen signature
touched. `decide +kernel` (line 1262) is kernel decide, not `native_decide`. One `set_option maxHeartbeats 3200000 in` (line 634).

## 1. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BAMomentExpGenB
✔ [4069/4069] Built RBM3D.Graph.BAMomentExpGenB (67s)
Build completed successfully (4069 jobs).
exit=0
$ grep -E "BAMomentExpGenB.lean.*(warning|error)" build.log | wc -l
0
$ lake env lean ax.lean     # #print axioms of every public theorem of the file
'RBM.BA.baMomExpNoExp_of_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMomentExp_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMomentExp_LWfgD_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMomentExp_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMomentExp_pin_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMomExpFarPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMomExpNearPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMomentExp_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWMomentExp_of_anp' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D ; lake env lean scan.lean   # scan.lean = import RBM3D + import RBM3D.Graph.BAMomentExpGenB + #assert_rbm_axioms
exit=0
axiom audit: 14377 theorems, 4529 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
scan exit=0                                  # Test/Axioms.lean unchanged; BALWMoment / BAAnpAuxG not in the scan
```
Public declarations (`grep -nE "^(theorem|lemma|def|abbrev|instance)"`): defs 146 `BAMomExpNoExp`, 160 `BAMomExpNoExpOfMoment`, 978 `BAMomentExpOn`,
992 `BAMomExpFarPin`, 996 `BAMomExpNearPin`, 1141 `BAMomentExpOfParts`, 1202 `BALWMomentExpOfAnp`; the 9 theorems above. Helpers: 13 `private`, stem `BAMomentExpGenB_`.

## 2. Statements against the pin (script diff)
`eq.lean` = the check file verbatim, plus `import RBM3D.Graph.BAMomentExpGenB`, the non-binding shapes of targets 6 / 8 (check lines 431 / 444)
renamed `def Shape6` / `def Shape8` by script, and these lines appended before `end RBM.BA.T2483Check`:
```
theorem eq6a : Shape6 ↔ ∀ d : ℕ, BAMomExpNoExpOfMoment d := Iff.rfl
theorem eq6b : Shape6 := baMomExpNoExp_of_moment
theorem eq8a : Shape8 ↔ ∀ d dom reg, BAMomentExpOn d dom reg := Iff.rfl
theorem eq9a : ∀ d, T2483_MomentExpOfAnp d ↔ BALWMomentExpOfAnp d := fun d => Iff.rfl
theorem eq9b : T2483_MomentExp := baLWMomentExp_of_anp
theorem eq9c : ∀ d, T2483_BALWMomentExp d ↔ BALWMomentExp d := fun d => Iff.rfl
theorem eq9d : ∀ d, BALWMomentExpOfAnp d ↔ (BAAnpAuxG d → baPin T2483_LWMomentExpG d) := fun d => Iff.rfl
theorem eqParts : ∀ d, BAMomentExpOfParts d ↔ ∀ K : ℝ, 0 < K → BAMomExpNoExp d K → BAMomExpFarPin d K → BAMomExpNearPin d K → T2483_BALWMomentExp d := fun d => Iff.rfl
$ lake env lean eq.lean ; echo "eq exit=$?" ; grep -c error eq.out
eq exit=0
0
```
(The same run shows the check file compiles on the branch.)
- **Target 6** (`baMomExpNoExp_of_moment : ∀ d, BAMomExpNoExpOfMoment d`): equal to the ticket's shape by `Iff.rfl` (quantifier order `d, BALWMoment d,
  K, 0 < K, 3 ≤ d, κ ε 𝔡, p, 𝔠 sz z, BAFlow, t, ε₀ Ψ ℓ, LWAssmExpgL, D, PrecL` with `∀ᶠ n` inside `PrecL`; index set `λ²/L² < 1-t ∧ regA d K`;
  loss `(η⁻¹ B_ctl^{1/2} 𝖳_t(|a-b|∧ℓ))^p + W^{-D}`). The wrapper def is needed so `BALWMoment` is not a theorem premise (as `BALWMomentOfAnp`, T2470). PASS.
- **Target 7** (`BAMomentExp_expand`, `:348`; no pin, ticket math `E|LWfgD|^p ≤ Σ_o ‖E Q.valW‖`): hypotheses `Even p`, the engine facts `hW`
  (`p ≤ #waved black`) and `hX : BAWExp ...` (both conclusions of `ba_localregularXP`), `0 < t n`, plus section variables `0 < κ`, `BAFlow`,
  `0 ≤ t ≤ BAflowT0`; conclusion `∫‖LWfgD (baFMz sz z) n (t n) ω Dm x y‖^p ≤ (outs.map ‖∫ o.Q.valW (BAMomentGen_D ..) (BAMomentExp_wt sz n Dm o) ![x,y]‖).sum`.
  Matches the ticket; `t = 0` covered by `BAMomentExp_LWfgD_zero`, integrability by `BAMomentExp_integrable`. PASS.
- **Target 8** (`BAMomentExpOn`, `BAMomExpFarPin/NearPin`, `BAMomentExp_pin_gen`, `baMomExpFarPin_holds`, `baMomExpNearPin_holds`): `BAMomentExpOn`
  equals the shape by `Iff.rfl` (unfolding `LWfgD`). Far pin = `domFar`, near pins = `domNearA`, `domNearB`, each at `reg = ¬ regA d K`, for every
  `K > 0`; `_holds` take only `0 < K`. `pin_gen`'s `hPin` (model-free `lwMomentExp_PinN` for nested ghost-free NGraphs) is discharged by the merged
  `lwMomentExp_pinN_far` / `_near`. PASS.
- **Target 9** (`BALWMomentExpOfAnp`, `baLWMomentExp_of_anp`, `BAMomentExpOfParts`, `baMomentExp_of_parts`): pinned content equal by `Iff.rfl`
  (`eq9a`–`eq9d`); `eq9b` proves `T2483_MomentExp` from the Lean theorem directly. Proof at `K = 1` composes `baLWMomentOfAnp_closed` (part A, merged),
  target 6 and the pins. `T2483_MomentExpClosed` not owed (L3d1 not merged, §0; ticket start decision). PASS.

## 3. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`/`inductive` (§0 grep). Statement-level premises: `BAFlow`, `0 ≤ t ≤ BAflowT0`, `LWAssmExpgL` (whose fields
  `STInitialGT2gL`, `LWLoopExpgL` are other gates' pins, allowed by ticket "Inputs used as hypotheses only"), `BALWMoment` (only inside
  `BAMomExpNoExpOfMoment`), `BAAnpAuxG` (only as the antecedent of `BALWMomentExpOfAnp`, exact type). No path binder (`BAShapePath`: 0).
- L40-C2 (thresholds independent of the coupling): constants obtained before every `filter_upwards`; `Kc` is the list-size sum of
  `ba_localregularXP p (ε₁/2) K0 d ((D+1)/𝔠)` (lines 1021-1024), fixed before `n`; `baGtoAGTRooted_holds d hd 𝔡⁻¹ κ` (`:703`) before
  `filter_upwards` (`:720`) with `BAflow_lam0_window` (`:726`). The limit check / O4 numbers are the 1a's, rerun in the prove report (eventual
  thresholds; no instance uses them). No stop rule triggered.
- No cycle: the file imports `BAMomentExpGen`, `BAZetaExp`, `BAExp14dB`, `LWMomentExpA` only; `BAAnpAuxG` (`BAAuxGraph2B:865`) is upstream and
  unproved; no importer of this file (§0).

## 4. Compiled nonempty instances (all in the file, compiled by the build in §1)
Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`), `flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `zSeq`, `t ≡ 1/2` (`half_lt_t0`),
`ε₀ = 1/20`, `Ψ0`, `ℓ = ℓT`, `p = 2`; `LWAssmExpgL` built from `window0`, `ℓT_one_le`, `ℓT_window` (`BAMomentExpGenB_assmExp0`, line 1224).
| target | line | applies | left as hypotheses |
|---|---|---|---|
| 9 | 1288 | `baLWMomentExp_of_anp 3 hAnp le_rfl ... D hD` | `BAAnpAuxG 3`, `STInitialGT2gL`, `LWLoopExpgL` |
| 6 | 1294 | `baMomExpNoExp_of_moment 3 (baLWMomentOfAnp_closed 3 hAnp) 6 ...` | same |
| 8 far / nearA / nearB | 1301 / 1306 / 1311 | `baMomExpFarPin_holds 3 (K := 1/100)`, `(baMomExpNearPin_holds ..).1`, `.2` | `STInitialGT2gL`, `LWLoopExpgL` |
| 9 assembly | 1317 | `baMomentExp_of_parts 3 (1/100) ...` | as target 9 |
| 7 | 1326 | `BAMomentExp_expand` at `n = 0`, `Dm = {0}`, `x = 0`, `y = 1`, lists from `ba_localregularXP 2 (1/4) _ 2 3 10` | none |
| 7 aux | 1334 / 1337 | `BAMomentExp_integrable`, `BAMomentExp_LWfgD_zero` | none |
Index sets nonempty: target-9 set at every `n` (`(0,0)`, `BAMomentExpGenB_strict`, line 1245); regime-(A) set for every `K > 0` (diagonal, line 1248);
pins' `¬ regA (1/100)` set at `n = 0` (`x = 0`, `y = (32,32,32)`, block distance 1 by `decide +kernel`, line 1258). Every hypothesis left open is
another gate's pin (allowed by CLAUDE.md §4 step 2 and ticket target 10 (i)); every deterministic hypothesis is discharged. Not degenerate:
`N = 2^21`, nonempty index sets, `t = 1/2`, `p = 2`, no `False` premise.

## 5. Paper deltas
Lean/paper differences of this part and their coverage:
- `ρ = (2K+1)(log W)^{3/2}` for the `ζ` window and `ε₁ = min(ε₀, d c₀/4)` (proof-internal): candidate `T2483c` in the prove report (d).
- `∀ K > 0` pins, `K = 1` in the target, the `domFar/domNearA/domNearB` split ("and" domain): band analogues numbered (D596, D618-D623 via
  `paper-deltas.md:1669`); BA reading has the same statement shape.
- Target 6 through a statement def (`BAMomExpNoExpOfMoment`, `Iff.rfl` to the shape): no content difference; reported as a finding in (d).
- Target 9 conditional on `BAAnpAuxG` (L3d1's unproved pin): an open input, stated in (d) as conditional (CLAUDE.md §5.6), not a paper-statement delta.
No uncovered statement difference.

## 6. Observations (no RETURN)
- O1. The prove report says "(a) ... this stage wrote no section (a)" and uses the 1a of `T2483-prove.md`; consistent with the split.
- O2. The report's statement list cuts long signatures at 165 characters; the full statements were checked here by `eq.lean` and by reading lines 146-160, 348-358, 978-1006, 1141-1144, 1202-1209.
- O3. The band twin's unused hypothesis `hreg2` is dropped in the private BA twin (`_prec_anp`); private, no public statement effect.

## Verdict
| target | verdict |
|---|---|
| 6 regime (A) | PASS |
| 7 weighted expansion | PASS |
| 8 far/near pins | PASS |
| 9 assembly and `baLWMomentExp_of_anp` | PASS |
| 10 (i) instances | PASS |
**T2483b: PASS.** No dispatcher sign-off needed.
