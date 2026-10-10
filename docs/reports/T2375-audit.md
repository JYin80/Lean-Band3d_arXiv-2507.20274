Auditor model: claude-opus-5-5

# T2375 audit (round 1) — LW-01 + ST-6 R4: `Graph/LWTermHolds.lean`, `Induction/MainIndHolds.lean`

`date -u`: Sat Oct 10 09:13:52 UTC 2026. Branch `t/T2375` at `6646c14`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2375-audit1` (detached).
Scratch: `scratchpad/T2375/{audit.lean,audit.out,build.log,root.log,root_sim.lean,root_sim.out,check.out}`.

## 1. Diff and hygiene

```
$ git diff --stat main...t/T2375
 RBM3D/Graph/LWTermHolds.lean      | 1801 +++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/MainIndHolds.lean |   93 ++
 RBM3D/Test/Axioms.lean            |   30 +-
 3 files changed, 1902 insertions(+), 22 deletions(-)
$ git diff main...t/T2375 | grep -nE "^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom " | wc -l
       0
$ wc -l LWTermHolds.lean MainIndHolds.lean | tail -1        # stop line 2300
    1894 total
$ git merge-tree --write-tree main t/T2375 >/dev/null && echo clean     # main = d38df76
merge-tree clean
```
Only the three sole writable files. No new `def`/`structure` in namespace `RBM.Gauss.Sizes` except `private def LWTermHolds_r` (`:307`);
the one public def `LWTermHolds_tMix` (`:1774`, instance data) carries the stem. Name clash on `main` (`git grep -c <name> main -- RBM3D | wc -l`):
`lwInteg_holds 0, lwterm_holds 0, lwtermExp_holds 0, stMainInd_holds 0, unMLOut_holds 0, stStep2_holds 0, LWTermHolds_ 0, MainIndHolds_ 0`.

## 2. Build (audit worktree)

```
$ lake build RBM3D.Graph.LWTermHolds RBM3D.Induction.MainIndHolds RBM3D.Test.Axioms
✔ [4062/4064] Built RBM3D.Test.Axioms (4.1s)
✔ [4063/4064] Built RBM3D.Graph.LWTermHolds (73s)
✔ [4064/4064] Built RBM3D.Induction.MainIndHolds (3.5s)
Build completed successfully (4064 jobs).
exit 0
$ grep -c "warning: RBM3D/Graph/LWTermHolds\|warning: RBM3D/Induction/MainIndHolds" build.log
0
$ lake env lean docs/tickets/checks/T2375-check.lean      # check file on the branch
check exit 0   (0 error lines)
```

## 3. Statements (script `audit.lean`, `lake env lean`, exit 0)

The targets are the merged pins of `Graph/LWPins.lean` (no new pin); each is checked by ascription against `∀ d, <pin> d`, and the R4
theorems by `rfl` against the ticket's one-line definitions:
```
example : ∀ d, LWInteg d := lwInteg_holds   -- likewise LWReduceB/lwReduceB_holds, LWReduceT/lwReduceT_holds, LWterm/lwterm_holds,
-- LWtermB/lwtermB_holds, LWtermExpS/…S_holds, LWtermExpN/…N_holds, LWtermExp/lwtermExp_holds, STMainInd/stMainInd_holds, UNMLOut/unMLOut_holds
example : @stMainInd_holds = fun d => stMainInd_of_LW d (lwterm_holds d) (lwtermExp_holds d) := rfl
example : @RBM.Univ.unMLOut_holds = fun d => RBM.Univ.unMLOut_of_LW d (lwterm_holds d) (lwtermExp_holds d) := rfl
example : @lwtermExpN_holds = fun d => lwtermExpN_of_LWterm d (lwterm_holds d) := rfl
```
Output of the `#check`s of the extra theorems (registry extension):
```
stStep2_holds : ∀ (d : ℕ), STStep2 d
stEtermsMid_holds : ∀ (d : ℕ), STEtermsMid d
stStep5I_holds : ∀ (d : ℕ), STStep5I d
stStep5II_holds : ∀ (d : ℕ), STStep5II d
```
- Hypotheses, quantifier order, dimensions, windows, `D`, regimes are those of the pins (identical types). Step 2 is not re-proved: `stMainInd_holds`
  is `stMainInd_of_LW` applied (`rfl` above); `stStep2_holds` is the same `ST_step2_of_pinsLW'` term that `stMainInd_of_LW` uses (`MainIndOut.lean:160`).
- Hidden hypotheses / vacuity / cycles: none added — the types are the pins; the random premises `LWInit`, `LWLoop2`, `LWLoopExp` are fields of the
  pinned `LWAssm`/`LWAssmExp` (merged, registered owed), discharged inside `stMainInd_of_LW` for `STMainInd`/`UNMLOut`. Imports are merged modules
  only (`LWMoment`, `LWMomentExp` = T2364 merged `9b484e2`, `LWTermExpN`, `AuxGraph2`, `GbEXP`, `MainIndOut`). No external hypothesis added.
- Pin guards (`sed` of the defs): `STMainInd`, `UNMLOut` start with `3 ≤ d →` (`Induction/Defs.lean:295`, `Universality/Pins.lean:433`);
  `STLWB`, `STLWT`, `STOptL2` (`Step2Defs.lean:406,421,667`) start with `∀ κ ε 𝔡` (no guard) — so keeping them owed is correct.

## 4. Axioms (`audit.out`)

```
'RBM.Gauss.Sizes.lwInteg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwReduceB_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwReduceT_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwterm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwtermB_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwtermExpS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwtermExpN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwtermExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stMainInd_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stEtermsMid_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep5I_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep5II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMLOut_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Registry (target 4)

`git diff main...t/T2375 -- RBM3D/Test/Axioms.lean`: 14 `owedProps` lines deleted — `STMainInd`, `STStep2`, `LWterm`, `LWtermB`, `LWtermExp`,
`LWtermExpS`, `LWtermExpN`, `LWReduceB`, `LWReduceT`, `LWInteg`, `UNMLOut`, `STStep5I`, `STStep5II`, `STEtermsMid` — each has an unconditional
`∀ d` theorem in §3/§4. Comments changed (not deleted): `STOptL2`, `STLWB`, `STLWT`, `STMainIndG`, `LWInit`, `LWLoop2`, `LWLoopExp`.

Root build on the branch as is (no root imports, hub's step):
```
$ lake build RBM3D
error: RBM3D.lean:420:0: axiom audit: 6 premise(s) that no theorem of this development proves are in none of ... :
  [RBM.Gauss.Sizes.LWtermExp, RBM.Gauss.Sizes.LWterm, RBM.Gauss.Sizes.LWtermB, RBM.Gauss.Sizes.LWReduceB,
   RBM.Gauss.Sizes.LWtermExpS, RBM.Gauss.Sizes.LWReduceT]
```
Expected: these six are proved only in the new modules, which the branch root does not import. Merge simulation (`root_sim.lean` = branch
`RBM3D.lean` with `import RBM3D.Graph.LWTermHolds`, `import RBM3D.Induction.MainIndHolds` inserted after the last `import`, line 417):
```
$ lake env lean root_sim.lean
exit 0
1:axiom audit: 10947 theorems, 3209 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
117:premises found by scanning: 123 (borrowed 1, owed 61, structural 42, refuted 6, superseded 13).
```
No unregistered premise once the root imports are in (DECISIONS §181 (2) satisfied). The hub must add **both** imports at merge; the
full `lake build` at merge (against current `main`) decides.

## 6. Compiled nonempty instances (in the same files; built in §2)

`LWTermHolds.lean:1636-1799` (`d = 3`, merged `sz0`, `z0`, `flow_z0`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`ε₀ = 1/20`, `Ψ0 = Φ0 ≡ W^{-1}`, `(C₁,C₂,C₃,Cc) = (2,2,1,1)`, `ℓ = ℓ_t`):
- `lwInteg_holds 3 sz0 0 … 2 x y` — no hypothesis left (`|E| < 2`, `t < 1` by `LWTermHolds_flow_facts`).
- `lwReduceB_holds` with its `f`-premise discharged by the Markov step `LWTermHolds_fB`; `inst_LWterm (lwterm_holds 3)`; `lwtermB_holds` at
  `c₀ = 3`, `K = L`, `ε₀ = 1/5` (window and class discharged by merged `LWPsiInst`).
- `lwReduceT_holds` at `D = 7` (premise branch) and `D = 5 < 2d+1` (moment branch), `f`-premise by `LWTermHolds_fT`; `lwtermExpS_holds` at
  `t ≡ 1/16` (index set = all `n`, `strict_all`); `inst_LWtermExpN (lwtermExpN_holds 3)` at `tEnd`; `lwtermExp_holds` at `tInst`, `tEnd` and
  at the alternating `LWTermHolds_tMix`, with a compiled proof that both regimes are nonempty (`n = 0`: strict; `n = 6001`: `1 - t ≤ ĝ²/L²`,
  via `LWTermHolds_N_regime_tEnd`, `n ≥ 6000`).
- Deterministic steps at numbers: Markov `p₀ = ⌈7/(1/10)⌉₊ + 1 = 71`, `7 ≤ 14.2`; `Φ0(r/2) ≤ KΦ0(r)` (`LWPsiAll.shift`); regime split at `n = 0`.
- Hypotheses left: only `LWInit`, `LWLoop2`, `LWLoopExp` (stochastic pins of other gates, registered owed) — allowed by §4 step 2.
`MainIndHolds.lean:74-91`: `(RBM.Univ.unMLOut_holds 3 … sz0 z0 flow_z0 (fun n => lemT (z0 n)/2) …).1 : sz0.STLK …` with **no hypothesis
left** (this exercises `stMainInd_holds`, `lwterm_holds`, `lwtermExp_holds` end to end); `stMainInd_holds`, `stStep2_holds`,
`stEtermsMid_holds`, `stStep5I_holds`, `stStep5II_holds` applied at `d = 3`, `κ = ε = 𝔡 = 1/10` (and `C_d = 1`).
Not degenerate: `N_0 = 2^21`, index sets nonempty, `t ∈ (0, 1)`, no `False` premise.

## 7. Paper deltas

Prove report (d) proposes T2375a (`(GavLGEX)` window, `7_8:65`), T2375b (`Ψ`/`Φ` split, `LWInit.2` unused), T2375c (`LWReduceT` from its
premise only for `D ≥ 2d+1`; shift constant of `(eq:directG2)`), T2375d (`ℓ` vs `L`, `min(ℓ, L)`). The targets are the merged pins, so no
further Lean/paper statement difference is introduced; coverage complete.

## 8. Observations (no RETURN)

- O1. The report's pre-check (`import RBM3D` + `MainIndHolds`, exit 0) cannot be rerun literally on the branch (root fails, §5); the merge
  simulation of §5 prints the same result, exit 0.
- O2. The `stMainInd_holds`/`stStep2_holds`/`stEtermsMid_holds`/`stStep5I/II_holds` examples are partial applications; the full instance of
  `stMainInd_holds` is the `unMLOut_holds` example (no hypothesis left).
- O3. Extra deletions `STStep2`, `STEtermsMid`, `STStep5I`, `STStep5II` fall under the ticket's "unconditional corollary" clause (§3, §4).

## Verdicts

All LW targets (`lwInteg/lwReduceB/lwterm/lwtermB/lwReduceT/lwtermExpS/lwtermExpN/lwtermExp_holds`): PASS. R4 (`stMainInd_holds`,
`unMLOut_holds`, plus `stStep2/stEtermsMid/stStep5I/stStep5II_holds`): PASS. Instances (target 3): PASS. Registry (target 4): PASS
(the merge must add both root imports, §5).

**Overall: PASS.**
