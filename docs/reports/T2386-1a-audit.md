Auditor model: claude-opus-5-5

# T2386 1a-audit, round 2 (design gate, under Amend 1): Sat Oct 10 15:31:59 UTC 2026

Inputs: `docs/tickets/T2386.md`, `docs/tickets/T2386-amend-1.md`, `docs/reports/T2386-prove.md` (a) and (a′)
(lines 101-154). Branch `t/T2386` = worktree `../RBM3D-wt/T2386` = 61849a6 (no Lean yet); `main` = e67bfbd.
This file replaces the round-1 1a-audit (RETURN, R1/R3; Amend 1 answered it). Scripts: `S=<scratchpad>/T2386`
(the prover's, rerun unchanged); auditor scratch in `S/audit2/`.

## 1. Layout and cones (deliverable (i)): rerun of `layout.py`
`python3 -I $S/layout.py ../RBM3D-wt/T2386 RBM3D.Induction.Step2Defs RBM3D.Chain.Carrier RBM3D.BA.FlowPins RBM3D.Induction.LocalAvg1 RBM3D.Induction.LocalAvg2`
```
RBM3D.Induction.Step2Defs: cone 177 modules / 207314 lines; LWExpCert* in cone: 6
RBM3D.Chain.Carrier: cone 39 modules / 33295 lines; LWExpCert* in cone: 0
RBM3D.BA.FlowPins: cone 38 modules / 33117 lines; LWExpCert* in cone: 0
RBM3D.Induction.LocalAvg1: cone 8 modules / 2854 lines; LWExpCert* in cone: 0
RBM3D.Induction.LocalAvg2: cone 4 modules / 916 lines; LWExpCert* in cone: 0
union of the four edited modules' cones: 43 modules / 35423 lines; LWExpCert*: 0
closure(Step2Defs+Carrier) contains RBM3D.Induction.Step2Events : False
closure(Step2Defs+Carrier) contains RBM3D.Induction.Step2Iterate : False
closure(Step2Defs+Carrier) contains LocalAvg1/FlowPins (cycle): False
```
The same script on current `main` e67bfbd (T2384/T2385 merged since the branch base):
```
RBM3D.Chain.Carrier: cone 41 modules / 35828 lines; LWExpCert* in cone: 0
RBM3D.BA.FlowPins: cone 40 modules / 35650 lines; LWExpCert* in cone: 0
union of the four edited modules' cones: 45 modules / 37956 lines; LWExpCert*: 0
```
Drift of the sole writable files since the base: `git diff --stat 61849a6 e67bfbd -- <Step2Defs, LocalAvg1/2, Carrier, FlowPins, Test/Axioms, RBM3D.lean>`
gives `RBM3D.lean | 2 ++` only (one-line union). Still no certificate module in the cone, so the ticket stays out of the certificate lane.
The (a′) C1 claim that the kernels the 16 names read lie in `Step2Gen`'s import closure (inline script over the import graph):
```
KLK ['RBM3D.Loop.KLTree'] in closure(Step2Defs+Carrier): [True]
ThetaN / uKer / UN ['RBM3D.Kernel.Evolution'] in closure(Step2Defs+Carrier): [True]
blockMat / Gres ['RBM3D.Loop.GLoopFlow'] in closure(Step2Defs+Carrier): [True]
pathH / pathP ['RBM3D.Path.Walk'] in closure(Step2Defs+Carrier): [True]
```
`grep -ln irreducible Kernel/Evolution.lean Propagator/Basic.lean Loop/KLTree.lean Defs/Semicircle.lean` returns no output (exit 1), as (a′) says.

## 2. Amend 1 items against (a′)
| item | (a′) | audit check | result |
|---|---|---|---|
| 1 `STGMM` | field `GMM` of `Step2Mat` (band `STGMM sz n (E n)`), `STGMMg := Cm.GMM`, `rfl` | `Step2Defs.lean:146-148` is `Gres H (zt E u) true x y - (if x = y then mE E else 0)`, a matrix-level def like `STLM` (:60-62) | met |
| 2 three energy-quantified pins | `mk : ∀ sz, (ℕ → ℝ) → Step2Mat sz`, read at `mk sz (fun _ => E)`; `Iff.rfl` at `mk := bandStep2Mat` | the bodies (:363-375, :377-378, :568-572) read only `STGMM, STthetaOp, STLKM, STJhatM, STELKLKM, STprof, STKloop, sz.lam, sz.L`; each is a `Step2Mat` field or `bandFM` field at `E n`, or depends only on `sz`. `(fun _ => E) n` β-reduces. The reason a `z`-family cannot be used, `lemE z = -2 Re(msc z)/‖msc z‖` (`Semicircle.lean:190`) and not `Re z`, is checked | met (O1) |
| 3 N-loop 12 | fields `LIM`, `KI` (`KLK … (E n) τ I`); `ThetaN/uKer/UN/thetaKer` over `Cm.S n`, `rfl` by delta | `Kernel/Evolution.lean:51-67`: `thetaKer = (μ • SB d L g) * Theta d L g (t*μ)`, `uKer = (1 - (s*μ) • SB) * Theta (t*μ)`, `ThetaN`/`UN` are built from these; `Theta ξ = Ring.inverse (1 - ξ • SB d L g)` (`Propagator/Basic.lean:70`); `bandFM.S n = SB d (sz.L n) (sz.lam n)` (`FlowPins.lean:343`); `mSigma E s` (`Semicircle.lean:85`) has the same body as `STmsig` (`Step2Defs.lean:56`); the 12 bodies (:713-854) read `loopL/blockMat/KLK/SB/mSigma/pathH/pathP/gridTime/KLloopOf/cutGlue*/STeeLoop/UN/uKer/ThetaN/STFlow/lemT/sz.size` only | met |
| 4 line prediction | net 972 / 1,185 / 1,460 | rerun, §3 | met (O4) |
| 5 O1 (`μ`) | not applied: the pilot has `μ` | `git show t/T2326:…/T2326PilotStep2.lean` line 75: `  μ : Measure sz.SeqΩ`; fields 69-178: `E T0 μ Pp Hflow Hpath LKM flowOK imLow ev1 ev2 ev3 ev4 Good ident martTail pLWT pEMe pNew` + `LKM_eq LKM_meas flowOK_adm flowOK_T flowOK_m imLow_pos` | (a) R3 was right; the round-1 O1 was wrong (O2) |
| 6 O3 | G1 list extended | C5 | met |
| 7 O4 | owed lines only if the pre-check needs them; the 16 new pins are assumed by no theorem | consistent with the amend | met |
| 8 O5 | instruction to 1b (`T2386a`) | C5 | met |

Name clashes on `main` e67bfbd (`grep -rlw` over `RBM3D`, `RBM3D.lean`, excluding `Probe/`): every planned new name
(`Step2Mat bandStep2Mat bandStep2Data Step2Data BAStep2 STStep2G STGMMg STNewKLKAtgL STNewKLKgL STK2decaygL
STGridRepNAtgL STGridRepNgL STLIMg STLKIMg STksimLKMg STelklkMg STavgErrMg STegtMg STeeMg STgANg STgDriftNg STeeUMg
Step2Gen_thetaKer Step2Gen_uKer Step2Gen_ThetaN Step2Gen_UN`) is found in `0` files.

## 3. Line prediction (deliverable (v)): rerun
`python3 -I $S/a1/sz16.py; python3 -I $S/a1/pred.py`
```
GMM 3 [('STGMM', 3)]
energy3 19 [('STNewKLKAt', 12), ('STNewKLK', 2), ('STK2decay', 5)]
Nloop12 90 [('STLIM', 3), ('STLKIM', 3), ('STksimLKM', 12), ('STelklkM', 6), ('STavgErrM', 3), ('STegtM', 5), ('STeeM', 5), ('STgAN', 3), ('STgDriftN', 9), ('STeeUM', 6), ('STGridRepNAt', 34), ('STGridRepN', 1)]
total body lines of the 16: 112
(a) rows recomputed total net: [757, 917, 1127]  (a) states 775/917/1150
Amend-1 additions (all in Step2Gen/Axioms): [215, 268, 333]
revised net total low/central/high: [972, 1185, 1460]  stop line 1500; margin at high: 40
new file alone:  [861, 1023, 1228]
```
The block sizes match a hand count of `Step2Defs.lean` (`STNewKLKAt` :363-374 = 12 lines; `STGridRepNAt` :817-850 = 34).
The net reading is the one Amend 1 item 4 fixes. The prediction is below 1,500 in all three cases, so the stop line is not hit and no split is required.

## 4. Instances: rerun
`python3 -I $S/a1/nl.py` (tail):
```
n=10 lam=8.820e-09 1/dd=10 E_n=lemE(z_n)=+0.500000 2-kap=1.9 L=44 K_n=ceil(N^1)=1e25.07 Delta=5.36e-27 t<=lemT=1.000000000000  newKLK/K2decay/grid hyps: True
ALL NEW-PIN HYPOTHESIS CHECKS: True
```
`python3 -I $S/inst.py | diff - $S/inst.out` gives no difference (output identical; tail `ALL HYPOTHESIS CHECKS: True`).

## 5. Deliverables (i)-(v) and stop lines
| deliverable | status |
|---|---|
| (i) layout | confirmed (§1); no text goes into `Step2Defs`; not in the certificate lane |
| (ii) vocabulary | every `Step2Defs` definition has a generic form or reads only `sz`; none is deferred; bridges `rfl`/`Iff.rfl`, except `STGijGEX` (F1, a proof inside `StochDomAt`, paper-delta `T2386a`); the heavy defeq risk on `STGridRepNAt` is flagged with a no-content fallback |
| (iii) `Step2Data` fields | `Step2Mat` (data: `LM GMM LIM KI Pp Hpath` + `FlowFM`) ⊂ `Step2Data` (`T0 flowOK`, facts `flowOK_adm flowOK_T L_swap`); the pilot fields deferred to T7/T1 are listed; the band values are `rfl` |
| (iv) `LocalAvg1/2` | unchanged from (a) (round 1 PASS); outside users re-grepped: `localAvg1_STWB_le` (`Graph/LWExpTerm3`, `MainIndChain`, `MainIndRegimes`), `stLocalAvgOfL2_holds` (`MainIndHolds`, `MainIndOut`) |
| (v) lines and cones | net 972 / 1,185 / 1,460 ≤ 1,500; cones §1 |
| stop lines | 1,500 not hit; `Step2Defs` untouched; not in the certificate lane |

## 6. Verdict
**PASS.** Every stage-1a deliverable is met under Amend 1, and no binding stop line is hit. No dispatcher sign-off is requested.

Observations (no RETURN; none changes a statement, an instance, the build, the axioms or the paper-delta coverage):
- O1. Amend item 2 named a `mk : ∀ sz z` family. (a′) uses an energy-sequence family `mk : ∀ sz, (ℕ → ℝ) → Step2Mat sz`
  and gives the reason (`lemE ≠ Re`). The resulting bridge is `Iff.rfl`, which is stronger than the amend's `→` fallback.
  It also leaves two family shapes (energy-indexed for `STNewKLKAtgL/STNewKLKgL/STK2decaygL`; `z`-indexed for
  `STGridRepNAtgL` and the `STStep2G` family). Because `baFM sz lam0 E` takes two sequences, a BA reading of
  the energy-indexed pins must fix `lam0` outside `mk`; the `∃ C δ₀` would then depend on `lam0`. This is a T8-BA/stage-G
  concern and not a T8 deliverable; it is recorded for the dispatcher.
- O2. The round-1 1a-audit O1 (and so Amend item 5's premise "the pilot has no `μ` field") was wrong: pilot line 75 has `μ`.
  (a) R3 is correct as written.
- O3. `localAvg1_data` (LA1:238; it reads `STFlow`, `lemT`) is not classified explicitly in (a) R4. It stays a band fact
  and discharges `hdat` in the corollaries. 1b should keep it unchanged.
- O4. The margin at the high case is 40 lines. A split is a dispatcher decision (ticket (v), Amend item 4), so if 1b
  measures over 1,500 it must stop and report. The (a′) C4 sentence "the split … is the fallback" does not let 1b split on its own.
- O5. Script cosmetics: the `pred.py` row label says "fields Gm LI KI, derived GMM/LKI", while (a′) names the fields `GMM LIM KI`
  and the derived `LKM LKIM`. In `nl.py` the condition `0<=L<=L` is a tautology (ℓ = 0 is the instance). Neither changes a number.
