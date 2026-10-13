Auditor model: claude-opus-5-5

# T2496 1a-audit (design gate, U U4s3) — Tue Oct 13 08:47:09 UTC 2026
Inputs: ticket `docs/tickets/T2496.md`, check `docs/tickets/checks/T2496-check.lean`, `docs/reports/T2496-prove.md` (a), (a″).
Audit worktree `../RBM3D-wt/T2496-1a-audit1`, detached at `t/T2496` 4e5e3b82 (base 6ccc6be2). Scratch: `scratchpad/T2496/audit1a/`.

## 1. Diff and probe compile
```
$ git diff --stat main...t/T2496
 RBM3D/Probe/T2496Pins.lean | 375 +++++++++++++++++++++++++++++++++++++++++++++
$ cd ../RBM3D-wt/T2496-1a-audit1 && lake env lean RBM3D/Probe/T2496Pins.lean      # started Tue Oct 13 08:42:20 UTC 2026
new premises found by the scan: []; with T2496_flowMod_band, T2496_flowMod_BA withheld: [RBM.BA.T2496_FlowMod]
RBM.BA.T2496_flowMod_band: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_flowMod_BA: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_sub: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_ev: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_ev_ba_sz0: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_Lloop_ev_band_szB: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_STKloop_two_lip: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_duhamelForm_band: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_duhamelForm_of_ker: [propext, Classical.choice, Quot.sound]
RBM.BA.T2496_duhamel_ba_sz0: [propext, Classical.choice, Quot.sound]
lake env lean RBM3D/Probe/T2496Pins.lean  17.27s user 3.23s system 91% cpu 22.361 total
exit 0
```
375 lines (≤ 400). `grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2496Pins.lean` → `0`; "declaration uses" warnings in the compile log: `0`.

## 2. Numerics rerun (the prover's scripts, outputs diffed against the prover's)
```
$ cd scratchpad/T2496 && python3 d1.py / inst.py / lines.py / misc.py;  cd <audit wt> && python3 textdiff.py / a3.py
d1 0  inst 0  lines 0  misc 0  td 0  a3 0                      (exit codes)
d1 identical  inst identical  lines identical  misc identical  td identical  a3 identical
$ bash audit1a/d1port.sh      # same script, pointed at the audit worktree
ported block = lines 304-671 of RBM3D/BA/Step5IIIWalk.lean: 368 lines; non-blank, non-comment: 324
last commit of the file: f2af0245
$ bash clash.sh | grep "total hits"      # main now c2542930
main: total hits 0 / t/T2491 0 / t/T2493 0 / t/T2494 0 / t/T2495 0 / t/T2496 0
```
Hand check of rows 6, 7: N=27, k=2: `27·2·27^8·(2·27²+1) = 2.225e16 ≤ 6·27^11 = 3.335e16`; `log10(4·27²) − (729/2)·log10 e = 3.465 − 158.3 = −154.8`. Both as in (a).

## 3. D1, D2, D3 texts (script diff, probe vs check) — texts fixed here
```
$ diff <(sed -n 236,246p check) <(sed -n 162,172p probe)  &&  echo "D1 identical"
D1 identical
$ diff <(sed -n 251,256p check) <(sed -n 48,53p probe)
6c6
<       ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'|
---
>       ∀ x y, ‖Hm n u ω x y - Hm n u' ω x y‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ c * Real.sqrt |u - u'|
$ D3: check :272-274 body vs probe :182-183 body (whitespace-normalised): identical; = T2491-check :364-366 at k = 2
```
- **D1 fixed** = check `T2496_DuhamelForm` (`:236-245`) verbatim. Proof route (F1) = the merged model-free `Step5IIIWalk_duhamel`
  (`BA/Step5IIIWalk:578`, from `pfStep5Grid_abs` + K1-K3); the block `:304-671` uses no `BA*`/`ba*` name (grep: 0 hits), so a copy
  into `DuhamelI` with stem-prefixed/private names is layering-legal (`BA/*` import forbidden). Band discharge (:174) and BA
  instance (:282, :288: `d=3, L=4, k=3, Δ=1/48, Rem_j=j/10, Mart_j=−j/10`, all hypotheses discharged) compile.
- **D2 fixed** = check `T2496_FlowMod` with `2 *` (A1, probe :48-53). Reason verified: `cont_norm_Xentry_le` (`ContinuityNet:526`)
  gives `‖Xentry‖ ≤ 2 * B`, and the true complex sup is `√2 N > N`, so the unamended text fails at `c = 1`; with A1 `c = 1` and the
  band type `3k N^(2k+7)` of `LemDecCalELip_Lloop_sub` (`:278-284`) is recovered (probe :148, compiled). The text is a
  "design-gate default (text fixed at the 1a-audit)" (check :9), not a binding pin: no stop line.
- **D3 fixed** = inline premise, text of `T2491_KLip C t 2`. Band discharge via A2 (`T2496_STKloop_two_lip`, Lipschitz `N²|Δu|`;
  the band Hölder statement `:352-355` recovered at :215; D3 at `(szB, zB)` :226). In the band file it stays inline (no def):
  the probe's `def T2496_D3` is a probe convenience only.

## 4. Binding pins (targets 2, 5, 8, 9)
Target 2 bridge `T2496_BandLemDecCalE`: auditor scratch (uncommitted, check + one line):
```
example : T2496_BandLemDecCalE := fun d =>
  Step5Gen_ingR5_iff_congr d STReg5III (fun sz E s t => STLemDecCalEConcl sz E s t) _ (fun sz z s t => Iff.rfl)
$ lake env lean scratchpad/T2496/audit1a/bridge.lean ; echo exit $?
exit 0          (0 error lines)
```
So target 2 (pins `T2496_LemDecCalEConclgL`, `T2496_LemDecCalEgL`, bridge) is provable as stated; text = `STLemDecCalEConcl`
(`Step5Pins:161-188`) with `Prec`→`PrecL sz μ`, `STLK2/STELKLK/STEGt/STee` → generic (`bandFM_*`, `bandStep34_STee` are `rfl`).
Targets 5, 8, 9: heads `STEtermsMidgL/STDuhamelIgL/STDuhamelIIgL` at `(mkM sz z).toFlowFM` typecheck at BA (probe :301) and in the check.
**Hypothesis lists fixed (check :8):** the ticket's family-premise table rows 1-11 plus the Steps 1-4 premises inside `STIngR5gL`,
with row 8 = D2 as amended (family form `∀ κ ε 𝔡, ∃ c` guarded, `c = 1`; compiled band :269, BA :273) and row 9 = D3 inline +
`‖m n‖ ≤ 1` inline; row 11 none (the 1a found no drift premise). The window `(η_t)⁻¹ ≤ N²` of the packaged form (:254) is not a new
row: it is derived inside from row 1 (`Step5CasesGen_FlowFacts`: `κm ≤ Im m`, `eta = (1 − t) Im m`, `Step5CasesGen:142-145`).

## 5. Stage-1a deliverables (ticket fill-in table, CONTROL H250 (4)); D1-D4
| item | finding |
|---|---|
| (i) exponent table | rows 1-14 present; rows 4, 6, 7 rerun/recomputed (§2) |
| (ii) instances | D2 band (:74) and BA (:237, :273), `c = 1`, `P(G^c)` 10^-154.8 (N=27) / 10^-9.55e11; D1 numeric at g = 1/64, 1, 10 (`d1.py`, reproduced) and Lean at the BA kernel `(sz0, zSeq)` (:288); external-hypothesis limit checks rows 7, 8 |
| (iii) hypothesis table | moved to the 1b start (allowed, ticket "(iii) … may move"); A1/A2 changes stated |
| (iv)-(vi) D1, D2, D3 | decided; probe lines listed; texts fixed in §3 |
| (vii) family table | as ticket, row 8/9 updated (§4); premise-level check at 1b start (allowed) |
| (viii) scope | present (public/private counts per section); D4 scope as accepted by dispatcher answer (2) |
| (ix) UBA-C1 | R1 only at `DuhamelI:516` and `DuhamelII:102-201`; guard (g) numerics 0 violations |
| (x) scan, registry | probe scan run: `[]`; `T2496_FlowMod` covered by public discharges (F4), so no `owedProps` line for D2 |
| (xi) `open private` | lists given; A3 12 names compile (probe :33-34, :44) |
| (xii) lines | see §6 |
| (xiii) clashes | 0 hits (rerun §2) |
| probe content (ticket "Probe" line) | D1, D2 texts with band discharges at `szB/zB`; generic `Lloop_sub` from D2; D1 at a BA kernel; BA readings: all compiled (§1) |
| D4 | scope accepted by the dispatcher; no change proposed |

## 6. Row packing and calibration (F1 applied)
```
$ python3 scratchpad/T2496/audit1a/split.py
D1=336: central 2040  rows 2  U4s3a 921  U4s3b 1119  x1.57 3203  vs calibration 3540: central passes=False
   DuhamelI part after DuhamelI2 cut (a) 1690 + 116 = 1806  (stop line 2000)
D1=380: central 2084  rows 2  U4s3a 921  U4s3b 1163  x1.57 3272  vs calibration 3540: central passes=False
   DuhamelI part after DuhamelI2 cut (a) 1690 + 160 = 1850  (stop line 2000)
```
**Decision: the pre-signed split applies** (1a central 2,040-2,084 > 1,950; < 3,900, so no third row):
**U4s3a** = `LemDecCalELip` + `EtermsMid` + `EtermsMid2` (targets 1-5, ≈ 921) on `t/T2496`; **U4s3b** = `DuhamelI` + `DuhamelI2` +
`DuhamelII` (targets 6-10, ≈ 1,119-1,163) on `t/T2496b`, stacked, after U4s3a's audit PASS. The central does not pass the
calibration line 3,540, so no new-file comparison is needed before the 1b. Instances of targets 1-5 land in U4s3a.

**A3 (EtermsMid cut) confirmed.** `EtermsMid` is imported only by `DuhamelI` and `stEtermsMid_of_LWT` reaches `MainIndOut`/
`MainIndHolds` through `DuhamelII → DuhamelI → EtermsMid`:
```
$ grep -rn "^import RBM3D.Induction.EtermsMid$\|open private.*from RBM3D.Induction.EtermsMid" RBM3D | grep -v Probe
RBM3D/Induction/DuhamelI.lean:6:import RBM3D.Induction.EtermsMid
$ grep -n "^import" RBM3D/Induction/MainIndOut.lean | grep Duhamel
RBM3D/Induction/MainIndOut.lean:9:import RBM3D.Induction.DuhamelII
```
Under the split, the ticket's draft cut (`EtermsMid2` = §8-§10) would move the frozen `stEtermsMid_of_LWT` out of every
`MainIndOut` import path while `DuhamelI` is untouched (U4s3a), so it is unworkable; the reverse cut (`EtermsMid2` = §1-§7, 48
private / 0 public, imported only by `EtermsMid`; `EtermsMid` keeps §8-§10 and the pin) keeps every ticket rule (no frozen name moves,
no private deleted, new file imported only by the next band file and `RBM3D.lean`). Within the sole writable files; no sign-off.

## 7. Stop lines (ticket "Stop rules")
| stop line | status |
|---|---|
| file > 2,000 / sibling-reserve rule | not hit: `DuhamelI` ≈ 1,806-1,850, `DuhamelI2` ≈ 840, `EtermsMid2` ≈ 1,480, `EtermsMid` ≈ 580, `LemDecCalELip` ≈ 1,727, `DuhamelII` ≈ 1,202 |
| G1 corollary not statable | two probed (`Lloop_sub` :148, `STKloop_two_sub` :215) with old name/type; the rest at 1b |
| band `def` change, import cycle | none planned; `misc.py`: cycles 0, direct BA imports 0 (`NewKLKGen → BA.FlowPins` transitively, imports named by the ticket) |
| binding `T2496_*` unprovable | no: target 2 bridge compiles (§4); heads typecheck |
| D1/D2 field without BA source | no: `T2496_flowMod_BA` :237, `T2496_duhamel_ba_sz0` :282 compiled |
| `∃` after `(sz, z)`; unguarded flow premise; `∀ n` drift | no (`∃ c` before `(sz, z)`, guarded :269/:273; row 11 none) |
| new kernel / `FlowFM` field / `BA/*` import / `STGridRepNgL` | none (grep `STGridRepNgL` in probe: 0) |
| `sz.withLam`, other comparison | only in BA discharges/readings (probe/check), not in a generic statement |
| C1 scan of generic probe statements | 0 hits except the substring `Lloop` of the probe's own declaration names (:80, :252) |

## 8. Observations (no RETURN)
- O1: the 1b's C1/X1-C1 scan must scan statement bodies: the planned name `LemDecCalELip_Lloop_subg` contains `Lloop`.
- O2: line citations off by 1-3 (`LemDecCalELip_Lloop_sub` `:277` → `:278`; `STKloop_two_sub` `:355` → `:352`); reverse cone 77 vs ticket 74.
- O3: D3's BA discharge (`baKsol_two`, `KInduct:88`, a closed form, not a modulus) is only typechecked; owner U3-BA as the ticket says.
- O4: the per-file sizes of (a) (xii) were not updated after F1; §6 gives `DuhamelI` ≈ 1,806-1,850 (below 2,000, above 1,800).
- O5: paper-delta candidates: none at the design level (A1, A2 change Lean design classes, not paper statements); the 1b report item (10) lists them.

## Verdict
**PASS** (design gate). Every stage-1a deliverable is met, no binding stop line is hit. Fixed here: D1 = check text; D2 = check text
with `2 *` (A1), `c = 1`; D3 inline (A2 discharge); hypothesis lists of targets 5, 8, 9 as in §4; A3 reverse cut; A4 engine.
**Row packing: pre-signed split U4s3a (targets 1-5, `t/T2496`) / U4s3b (targets 6-10, `t/T2496b`, after U4s3a's audit PASS).**
No dispatcher sign-off needed.
