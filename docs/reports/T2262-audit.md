Auditor model: claude-opus-5-5

# T2262 audit (BA-S2b2a, `RBM3D/BA/Step1Setup.lean`), round 1 — Tue Oct  6 07:20:18 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2262-audit1` (detached at `t/T2262` = abfd0c6; merge base 20de014).
Scratch files in `scratchpad/T2262/` (`aud_stmt.lean`, `aud_diff.py`, `aud_pre.lean`).

## 1. Scope, hygiene, build
```
$ git diff --stat main...t/T2262 ; git diff --name-only main...t/T2262
 RBM3D/BA/Step1Setup.lean | 1279 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1279 insertions(+)
RBM3D/BA/Step1Setup.lean
$ sed -n 6,8p RBM3D/BA/Step1Setup.lean        # allowed imports only (no RBM3D, no RBM3D.Induction.Step1)
import RBM3D.BA.Step1Boot
import RBM3D.Induction.Continuity
import RBM3D.Induction.Step1Setup
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b" RBM3D/BA/Step1Setup.lean | wc -l
       0
$ lake build RBM3D.BA.Step1Setup 2>&1 | grep -E "error|declaration uses|Build completed"
Build completed successfully (3755 jobs).
$ git diff --name-only 20de014 main | grep ^RBM3D/   # main drift since merge base: no overlap
RBM3D/Graph/AnpKey4.lean
RBM3D/Induction/QDriftB.lean
RBM3D/Test/Axioms.lean
$ for n in baS1Std baG_continuousOn baGopbound flowFM_omegaC_mono flowFM_wl_det baNetLift; do git grep -lw $n main -- RBM3D | wc -l; done
baS1Std:0 baG_continuousOn:0 baGopbound:0 flowFM_omegaC_mono:0 flowFM_wl_det:0 baNetLift:0
```
Frozen signatures: none touched (one new file only). `RBM3D/Test/Axioms.lean` not edited (no new `Prop`-valued hypothesis; the `BABootstrap'` owed line stays, as the ticket says).
28 `private` helpers, all prefixed `BASetup_`; public unpinned names live in `RBM.BA.Step1SetupInst` (`sI`, `tI`, `inst_*`).

## 2. Statements against the pins (check file section 1)
```
$ python3 scratchpad/T2262/aud_diff.py   # theorem type text vs `def X_stmt` body, whitespace-normalised
baS1Std identical 294
baG_continuousOn identical 210
baGopbound identical 539
flowFM_omegaC_mono identical 117
flowFM_wl_det identical 850
baNetLift identical 899
$ lake env lean scratchpad/T2262/aud_stmt.lean ; echo exit=$?
#   (= import RBM3D.BA.Step1Setup + check file section 1 verbatim, then
#    `example (d : ℕ) : RBM.BA.T2262Check.X_stmt d := X d` for the six targets, then #print axioms)
'RBM.BA.baS1Std' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baG_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGopbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.flowFM_omegaC_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.flowFM_wl_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baNetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baS1Std' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baG_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baGopbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baNetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_flowFM_wl_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_flowFM_omegaC_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake build RBM3D && lake env lean scratchpad/T2262/aud_pre.lean   # import RBM3D; import RBM3D.BA.Step1Setup; #assert_rbm_axioms
Build completed successfully (4070 jobs).
axiom audit: 7737 theorems, 2575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; ...
exit=0
```
Against the ticket's mathematics (§29 checklist), all six read as pinned: times `0 ≤ s ≤ t ≤ t₀(z)` (T1),
`0 ≤ u,u' ≤ 1 − N⁻¹` (T3), `0 ≤ s ≤ t < 1` with `RangeCond τ t` (T6), `b < 1` only (T2); arbitrary `lam0`, `E`
in T2/T3/T6 with `κ ≤ Im m`, `‖m‖ ≤ 1` for all `n`; law `seqP (sz.withLam 0)` in T3/T6; T5 over an arbitrary
`C : FlowFM sz`, constant `(2·9^d + 1)`, `‖G‖_max ≤ C₀` free; T1 at the main flow `z`, `τ = ε/2`, `κ' = min κ 1`.

## 3. Hidden hypotheses, vacuity, cycles
- All six are theorems; premises are explicit. The only bundled premise is `BAFlow` (merged def,
  `FlowPins.lean:546`: `Admissible ∧ ∀ n, BAdom …`), discharged at the instance by the merged `flow_sz0`.
- T1 dummy energy: `S1Std` (`Induction/Step1Setup.lean:237`) has one energy field `hE : ∀ n, |E n| ≤ 2 − κ`;
  at `E ≡ 0`, `κ' = min κ 1` it is true. `S1Std` reads of `hE`:
  ```
  $ grep -n "h\.hE" RBM3D/Induction/Step1Setup.lean RBM3D/Induction/Step1.lean   # output condensed to line numbers + enclosing decls
  Step1Setup.lean:744, 783, 809, 830 (s1_h55, s1_LI);  Step1.lean:181, 271, 422, 489, 537 (s1_wl_seq, s1_forb, s1_boot, s1_loopPT, step1TargetV3_holds)
  ```
  All are band lemmas that S2b2b replaces by BA ports (`baBoot_LI`, targets 2, 3, 5, 6), as the ticket plans.
  The conclusion `S1Std …` is a true Prop at the BA data, so it creates no vacuity; it is a Lean bridge (covered by T2262c).
- No circular dependency: imports are merged modules only; no owed hypothesis is consumed (no `BABootstrap'`,
  `BAGbEXP*`, `BAFlowMember` among the premises).

## 4. Compiled nonempty instances (namespace `RBM.BA.Step1SetupInst`, same file, built above)
| target | instance | data | hypotheses discharged |
|---|---|---|---|
| T1 `baS1Std` | `inst_baS1Std` | `sz0`, `zSeq`, `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `𝔠d=1/100`, `s≡1/2`, `t≡2/3` | all: `flow_sz0`, `inst_BAFamZ_horizon` (`t ≤ t₀`), `s1Setup_conStInd_const` |
| T2 `baG_continuousOn` | `inst_baG_continuousOn` | `n=0`, `[0,2/3]`, all-ones sample, entry `(0,0)` | all: `BAmF_sz0_im_pos 0`, `2/3 < 1` |
| T3 `baGopbound` | `inst_baGopbound` | `κ=1/2`, `C=1`, flow data of `zSeq` | all: `inst_im_m_ge`, `inst_norm_m_le`, `sz0_tendsto` |
| T4 `flowFM_omegaC_mono` | `inst_flowFM_omegaC_mono` | `baFMz sz0 zSeq`, `n=u=0`, `C₁=1<C₂=3` | all |
| T5 `flowFM_wl_det` | `inst_flowFM_wl_det` (+ `example` at the all-ones sample) | `n=u=0`, `a=1/64`, `c'=1/20`, `g=W⁻³`, `Nτ=4`, `C₀=3` | all: `baFM_loop_det`, `baM_entry_le`, `G_0 − M = 0` |
| T6 `baNetLift` | `inst_baNetLift` | `κ=τ=1/2`, `s≡1/2`, `t≡2/3` | all deterministic ones incl. `inst_rangeCond`; the two `PerTimeDomAt` premises remain (stochastic per-time inputs, proved in BA-S2b2b) |

Nondegenerate: `n = 0` gives `L = 4`, `W = 32`, `N = 2^21`; no empty index, no collapsed window
(`[1/2, 2/3]`, `[0, 2/3]`), no `False` premise. `inst_im_m_ge` proves `1/2 ≤ Im m` for every `n` (no `BAWinBulk`
hypothesis needed, (a′) 1). T5 at `u = 0` has `G − M = 0` exactly as the ticket prescribes; the premise set is
nonetheless genuine (`‖G_0‖_max ≤ 3` and the loop bound are discharged from merged estimates), and
`inst_omegaC_three` shows `omegaC = 1` there.

## 5. Paper deltas
Report (d) proposes T2262a (no `7_8` statement for BA time continuity: `baGopbound`, `baG_continuousOn`),
T2262b (`7_8:1987-1990` read as band weak-law core with `G − M`, threshold `C₀`), T2262c (dummy energy `E ≡ 0`,
`κ' = min κ 1` in `baS1Std`), T2262d (bulk premise `|E| ≤ 2 − κ` replaced by `κ ≤ Im m`, `‖m‖ ≤ 1`;
`C' = 2C + 10`). These cover every Lean/paper statement difference I found; T2262a, T2262b are the two the ticket expects.

## 6. Observations (no verdict impact)
- O1. `sI`, `tI` are public unpinned defs in `RBM.BA.Step1SetupInst` (namespace-qualified, no clash:
  `Induction/Step2Core.lean:1314-1315` are `private`). Making them `private` would follow §3 (E) more literally.
- O2. `STConStInd` at `s≡1/2`, `t≡2/3` holds only from `n = 8` (prove report (a)(ii)(B)); the instance uses the
  merged eventual lemma, which is correct for an `∀ᶠ` premise.
- O3. The file is 1279 lines (ticket 900 / 1200 / 1500).

## Verdicts
- T1 `baS1Std`: **PASS**
- T2 `baG_continuousOn`: **PASS**
- T3 `baGopbound`: **PASS**
- T4 `flowFM_omegaC_mono`: **PASS**
- T5 `flowFM_wl_det`: **PASS**
- T6 `baNetLift`: **PASS**

Ticket verdict: **PASS**. No dispatcher sign-off needed.
