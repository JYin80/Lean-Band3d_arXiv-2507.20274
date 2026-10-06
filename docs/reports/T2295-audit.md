Auditor model: claude-opus-5-5

# T2295 audit (round 1) — BA-L2a1 `Graph/BAExpand` — verdict PASS

Written Tue Oct  6 13:43:41 UTC 2026 (`date -u`). Audited: `t/T2295` at `d57aa36`, detached worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2295-audit1`. Targets as reduced by `docs/tickets/T2295-amend-1.md` (CONTROL H99):
target 1 (vocabulary + pin `BAlanlw`), target 2 (`baLanlw_holds`), instances (I1)-(I2). Target 3 and (I3)-(I4) are moved
to BA-L2b and are not audited here. `S` = scratchpad `T2295/`.

## 1. Statement (target 1, target 2) against the pin

```
$ python3 $S/eq.py    # check section 2 block (namespace RBM.Graph.T2295Check ... end), whitespace-normalized, vs BAExpand.lean
check block chars(normalized): 3224  found in BAExpand.lean: True
BAlwH BAlwM BAlwG BAlwGc BAlwS BAlwMp BAlwW BAlwf BAlwdf BAlanlwL BAlanlwR BAlanlw
```
Text equality does not exclude a different name resolution (BAExpand.lean opens `RBM RBM.Gauss RBM.Green` in
`RBM.Graph`), so the elaborated terms were compared: scratch file = check-file imports + `import RBM3D.Graph.BAExpand` +
check sections 2-3 verbatim + the three lines below.
```
example : RBM.Graph.T2295Check.T2295_baLanlw_holds := RBM.Graph.baLanlw_holds
example (d : ℕ) : RBM.Graph.T2295Check.BAlanlw d = RBM.Graph.BAlanlw d := rfl
example : ∀ d : ℕ, RBM.Graph.BAlanlw d := RBM.Graph.baLanlw_holds
$ lake env lean $S/defeq.lean; echo exit=$?
exit=0
```
So the landed `BAlanlw` is definitionally the pinned one, and `baLanlw_holds (d : ℕ) : BAlanlw d` (BAExpand.lean:744) is
check section 3's `T2295_baLanlw_holds`.

Against the paper (`B_graphical_lemmas.tex:359-372`, `(eq:BE)`):
`Ǧ_{xy} f(G) =_E Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} f(G) − Σ_{α,β} M_{xα} S_{αβ} G_{βy} ∂_{h_{βα}} f(G)`.
`BAlanlwR` has the same two double sums with the same index placement (`BAlwGc … β β`, `BAlwG … α y`; `BAlwG … β y`,
`BAlwdf … β α`) and the same sign; `BAlanlwL = BAlwGc x y * BAlwf`. Quantifiers: `∀ L W, 3 ≤ L → ∀ g0 E t m, BASelf → 0 ≤ t → t < 1
→ ∀ P x y`; the law is `PF d L W 0` (§57 (3)); `d` free (no `3 ≤ d` needed). No losses or exponents occur (an exact identity).
Differences from the printed lemma: `f` a resolvent polynomial rather than "a differentiable function of G" (covered by
D64 = T2040d) and the `∂_h` convention (D65 / T2060a); see §5.

## 2. Hidden hypotheses, vacuity, cycles

- The pin is a plain `Prop` (no structure); its only data hypothesis is `RBM.BA.BASelf d L g0 E m`
  (`MFixedPoint.lean:193`: `0 < m.im ∧ m = (L^d)⁻¹ * tr (BAMB d L g0 E m)`), plus `3 ≤ L`, `0 ≤ t`, `t < 1`.
- Not vacuous: `baSelf_zero : BASelf 3 3 0 0 i` is proved (BAExpand.lean:865), and the instance of §3 uses it.
- `GaussIBP` is discharged inside the proof by the merged `RBM.Green.gaussIBP`; the internal hypotheses of
  `BAExpand_integral` (`M_{ββ} = m`, the pathwise identity `G − M = −M(H+tm)G`) are discharged by `BAExpand_M_diag`
  (from `BASelf`) and `BAExpand_G_sub_M` (BAExpand.lean:744-779). No external hypothesis remains, so no limit check is needed.
- No cycle: the file is new; its imports are exactly the five of the ticket, all merged on `main`:
```
$ grep -n "^import" RBM3D/Graph/BAExpand.lean
6:import RBM3D.Graph.BAVocab
7:import RBM3D.Graph.LWWeightExp
8:import RBM3D.BA.Ward
9:import RBM3D.BA.FlowPins
10:import RBM3D.Gauss.BlockAnderson
```

## 3. Compiled nonempty instances

Endpoint `baLanlw_holds`: fully discharged instance at BAExpand.lean:879-887 (`d = 3`, `L = 3`, `W = 1`, `N = 27`,
`g₀ = 0`, `E = 0`, `t = 1/2`, `m = i`, `x = 0`, `y = e₀ ≠ x`, `P = X (true, e₀, 0)`):
```
  baLanlw_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I baSelf_zero (by norm_num) (by norm_num) _ _ _
```
Every hypothesis is discharged (`3 ≤ 3`, `BASelf` by `baSelf_zero`, `0 ≤ 1/2`, `1/2 < 1`); `t = 1/2` uses the Stein
branch of the proof, not the `t = 0` branch. Second instance (:889-899) at `g₀ = 1/2`, `E = 3/10`, `t = 1/2`,
`f = G_{e₀0} Ḡ_{e₀0}` with `m`, `hSelf` as hypotheses (no merged theorem produces a real-energy solution at `g₀ ≠ 0`;
the fully discharged one above suffices).
(I1) `baS_diag : BAlwS 3 3 1 (1/2) x x = 1/2` (:789), `baS_row_sum : Σ_y BAlwS 3 3 1 (1/2) x y = 1/2` (:793).
(I2) `baLanlw_t0` (:800): at `t = 0` both integrals are `0` and equal, the last conjunct obtained from
`baLanlw_holds 3 3 1 _ g0 E 0 m hSelf le_rfl one_pos P x y`. Plus 8 `example`s of the Stein-layer helpers at
`d = L = 3`, `W = 1`, `g₀ = 1/2`, `z = i`, `u = 1/2` (:817-863). All compile (§4). Nothing degenerate (`N = 27`, `x ≠ y`,
window `0 < t < 1` open; `W = 1` is the ticket's instance size).

## 4. Build, axioms, hygiene, files

```
$ rm -f .lake/build/lib/lean/RBM3D/Graph/BAExpand.olean; lake build RBM3D.Graph.BAExpand 2>&1 | grep -E "error|declaration uses|Built RBM3D.Graph.BAExpand|Build completed"
✔ [3778/3778] Built RBM3D.Graph.BAExpand (5.3s)
Build completed successfully (3778 jobs).
$ lake env lean RBM3D/Graph/BAExpand.lean > $S/elab.txt 2>&1; echo exit=$?; grep -c "" $S/elab.txt
exit=0
0
$ # #print axioms of all 13 non-private theorems (35 theorems in the file, 22 private `BAExpand_` helpers used by them)
$ lake env lean $S/ax.lean 2>&1 | ... | sort | uniq -c
  13 [propext, Classical.choice, Quot.sound]
'RBM.Graph.baLanlw_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|set_option|@\[implemented_by|@\[extern|unsafe|opaque" RBM3D/Graph/BAExpand.lean
36:set_option linter.style.setOption false
37:set_option linter.style.longLine false
38:set_option linter.unusedSectionVars false
39:set_option linter.flexible false
40:set_option linter.unusedFintypeInType false
41:set_option linter.unusedDecidableInType false
```
(only linter options; no `sorry`/`admit`/`axiom`/`native_decide`.)
```
$ git diff --name-only main...HEAD
RBM3D/Graph/BAExpand.lean
$ printf "import RBM3D\nimport RBM3D.Graph.BAExpand\n\n#assert_rbm_axioms\n" > $S/precheck.lean; lake env lean $S/precheck.lean > $S/pre.txt 2>&1; echo exit=$?; head -1 $S/pre.txt
exit=0
axiom audit: 8567 theorems, 2815 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ # name clash: 30 new public names, grep -rlw over RBM3D/*.lean, Probe/ and BAExpand.lean excluded
clash grep done (30 public names)      # no name printed = 0 hits
```
Only a sole writable file is touched; no merged file changed (§57 (1)); no frozen signature touched. All 12 helper names
the ticket pins (`baGm … stein_baPoly`) exist; every other helper is `private`/`BAExpand_`-prefixed.

## 5. Paper deltas

| Lean/paper difference | coverage |
|---|---|
| `f` = resolvent polynomial in `G`, `G*` (paper: "differentiable function of `G`", `B:360`) | D64 (T2040d), class convention of the expansion pins |
| `∂_{h_{βα}}` as the derivative along `E_{βα}` (`BAlwdf` = `LWPins_dH`) | D65 / T2060a |
| model data `M = Mres(g₀Ψ, E, m)`, `S = t·svarF d L W 0`, `z_t = E+(1−t)m`, law `PF d L W 0`, `0 ≤ t < 1`, `BASelf` | the pinned "setting of the block Anderson model" (§57 (3)); `BASelf` is `(self_m)` `1_2:626-629`, not a delta |
| D402 (`GGGamma`) | not used by these targets |

No new candidate is needed; the prover's "none" (report (d) 2) is consistent.

## Verdicts

- Target 1 (vocabulary + pin `BAlanlw`): **PASS** (verbatim and definitionally equal to check section 2).
- Target 2 (`baLanlw_holds (d : ℕ) : BAlanlw d`, unconditional): **PASS**.
- Instances (I1), (I2) and the endpoint instance: **PASS** (compiled, fully discharged instance at `t = 1/2`, `N = 27`).
- Target 3, (I3), (I4): out of scope by Amend 1 (moved to BA-L2b).

Overall: **PASS**. No dispatcher sign-off needed.

## Observations (no statement, instance, build, axiom or delta-coverage effect)

1. Registry: the ticket asks for one `RBM3D/Test/Axioms.lean` line for `BAlanlw` (class proved); none was added.
   The pre-check above exits 0 (the pin is concluded by `baLanlw_holds`), and the twin `LWweightExp` has no line either
   (`grep -c "LWweightExp\|BAlanlw" RBM3D/Test/Axioms.lean` → `0`). The hub's full `lake build` at merge is the check.
2. D64 cites only `7_8:295, 310, 335`; the dispatcher may add `B:360` (BA `lanlw`) to its citations.
3. The prove report is 304 lines (limit 300).
