Auditor model: claude-opus-5-5

# T2498 1a-audit (design gate, U3s3) — Wed Oct 14 02:33:47 UTC 2026
Inputs: ticket `docs/tickets/T2498.md`; section (a) and (a″) of `docs/reports/T2498-prove.md`; branch `t/T2498` at `3118c1d0`;
audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498-1a-audit` (detached at `3118c1d0`). Scratch: scratchpad `T2498/audit1a/` (`$A`).

## 1. Numerics of (a): rerun, verbatim diff against the preflight's saved outputs
```
$ bash $S/rep.sh > $A/rep.out; bash $S/rep2.sh > $A/rep2.out; diff $S/rep.out $A/rep.out; diff $S/rep2.out $A/rep2.out
rep diff: IDENTICAL
rep2 diff:
< HEAD: total hits 0 t/T2498: total hits 0 t/T2499: total hits 0
> HEAD: total hits 0 t/T2498: total hits 1 t/T2499: total hits 0
$ git grep -n -w -F alt_hkerQNg t/T2498 -- RBM3D | cut -d: -f2-3 | tr '\n' ' '     # the one new hit
RBM3D/Probe/T2498Pins.lean:23 RBM3D/Probe/T2498Pins.lean:100 RBM3D/Probe/T2498Pins.lean:111 RBM3D/Probe/T2498Pins.lean:180 RBM3D/Probe/T2498Pins.lean:252
```
All exponent rows (i) 1-10, the instance (ii), the size table (xii), import cycles, scope closure, G1, premise-scan preview reproduce
byte for byte. The single difference is the probe's own comments (committed after (a) ran; never merged): observation only.
Spot check of row 3/5 by hand: `A=(κ+1)/κ` at `κ=.6097` → 2.640; `3·√2.64·64^.2 = 11.2 ≤ 64^.9 = 42.2`. `expo.py:4-14` encodes the 20
conjuncts of `altBudgetExpQN` (`QBudgetB.lean:92-106`, counted: 20) with `C4 := Cv` (A1).

## 2. Probe: recompiled in the audit worktree
```
$ cd .../RBM3D-wt/T2498-1a-audit && lake env lean RBM3D/Probe/T2498Pins.lean > $A/probe.out 2>&1; echo "exit $?"
exit 0          (Wed Oct 14 02:29:04 → 02:29:16 UTC)
$ grep -v "^RBM.BA.probe.*\[propext, Classical.choice, Quot.sound\]$" $A/probe.out | wc -l ; grep -c "\[propext, Classical.choice, Quot.sound\]" $A/probe.out
0
12
$ wc -l RBM3D/Probe/T2498Pins.lean; grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2498Pins.lean; grep -c Probe RBM3D.lean
397 RBM3D/Probe/T2498Pins.lean
0
0
$ git diff --stat main...t/T2498
 RBM3D/Probe/T2498Pins.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
$ python3 -I $S/verb.py     # probe texts vs docs/tickets/checks/T2498-check.lean (comments stripped, whitespace collapsed)
T2498_KerEK4 IDENTICAL 683 683
T2498_KerEK4Fam IDENTICAL 394 394
T2498_XiRoundPTgL'' IDENTICAL 684 684
T2498_OeqQtRoundPTgL'' IDENTICAL 327 327
```
Probe line of the ticket, item by item (statement-level reading of `T2498Pins.lean`):
- D1 text + band discharge: `probe_kerEK4Fam_band` (general `d`, `C4 = qProxy4C d k 𝔡⁻¹ (min κ (4/5)) KL`, `∀ᶠ n` from WO) and at `(szB, zB)`
  (`probe_D1_flows`, first conjunct). **BA reading discharged**, not only typechecked: `probe_kerEK4Fam_ba` from the merged
  `baEKSumDecay2_holds` (`EKSum:1772`) via `Step2Kern_UN_BA`, `BAflow_real`, `BAflow_lam0_window`; at `(sz0, zSeq)` (second conjunct).
  Quantifier order of `T2498_KerEK4Fam` (`:47-51`): `3 ≤ d → ∀ k ≥ 2, ∀ κ ε 𝔡 KL > 0, ∃ C4 > 0, ∀ sz 𝔠 z, Flow → ∀ᶠ n` = ticket D1.
- `alt_hkerQNg` instance at BA-type kernels: `probe_alt_hker_ba_three` applies `probe_alt_hkerQNg` (`:306`) at `baFM (probe_szG g) g₀ E`,
  `0 < g₀ < g`, `g = 1/64, 1, 10`; `d=3, L=16, W=2^16, k=2, KL=1, ε=7/8, τ'=1/16, Cv=C4+4`, grid `u_j=j/2`, `X = 1_{b=0}-1_{b=(0,e)} ≠ 0`
  sum-zero, every `σ`, `a`; every deterministic hypothesis discharged (`hcmp`, `hA`, `hLK: 4096 ≤ 65536`, `hWε`, `hlog`, `hdW`, `hAk`,
  window `u₁ = 1/2 ≤ 1 - g²/256`). Nondegenerate (`N > 0`, `X ≠ 0`, window `[0,1/2]`). `δ = 0` is admissible (support spread ≤ 1).
- D2 text `T2498_GridDriftQEv` + per-index reduction `probe_gridDriftQ_step` to merged `gridDriftQNg` (`Chain/QGridGen:759`, T2497) at `m+1`.
- Round pin band bridge: `probe_round_band : STOeqQtRoundPT'' d ↔ T2498_OeqQtRoundPTgL'' d …` by `bandFM_STIngR` alone.

## 3. D1–D4
**D1: PASS.** Text = check (script above); band and BA discharges compile; no stop line (BA source exists and is proved).
A1 (vocabulary carries `Cv` with `A^k ≤ W^{(Cv-C4)ε}`, band `Cv = C4`, `A = 1`) is the ticket's own UBA-C1 row (c) (`step34Gen_ratio_pow_le`,
`A^k into W^{(Cv−C4)ε}`), and `probe_hker_altQNg` proves it at one index; no pin changes.

**D2: decided; text fixed here with one correction (binding for 1b).** The probe text quantifies the link as `∀ n, HierDriftGen_KLink Cm n`,
which covers only `w ∈ [0,1)`, while the wing envelope that (a)(v) names as the route needs the link for every `w`:
```
$ sed -n 677,679p RBM3D/Chain/HierDriftGen.lean; sed -n 1085,1086p RBM3D/Chain/HierDriftGen.lean
def HierDriftGen_KLink (Cm : Step2Mat sz) (n : ℕ) : Prop :=
  ∀ w ∈ Set.Ico (0 : ℝ) 1, ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
    Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
```
(`exists_norm_KI_le_wing` uses its helpers `gdn_loopOf_eq`, `gdn_Bctl_le` from `GridDriftN`, which are `private`, so a restricted copy is
not cheap.) **Fixed D2 text** = the probe's `T2498_GridDriftQEv` (`:361-375`) with the premise `(∀ n, HierDriftGen_KLink Cm n)` replaced
by the all-`w` link `(∀ n w k σ a, Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)` — the `hKK` of `exists_norm_KI_le_wing`
(`HierDriftGen:1085`) and of `stOeqNQPTgL''_of` (`NQEndFlowGen:710`), so the target-12 bundle already carries it; BA source
`baStep2Mat_KI` (`Step2BA:89`, any `u`), band source the merged band instance of that row. Everything else of the probe text stands
(drift classes and `0 < lam` under `∀ᶠ n`; `hS`, link, `‖m‖ ≤ 1`, `hη` for all `n`; conclusion `rGridQNg ≤ qErrQNg` at `B = N^τK η(j+1)^{-(m+2)}`).
```
$ cd .../RBM3D-wt/T2498-1a-audit && lake env lean $A/D2fixed2.lean; echo "exit $?"   # fixed text + feed check (uncommitted scratch)
exit 0
```
`$A/D2fixed2.lean` holds `def T2498_GridDriftQEvFixed` and an `example` deriving from its premises both `∀ n, HierDriftGen_KLink Cm n`
(restriction, for `gridDriftQNg`) and the wing bound `exists_norm_KI_le_wing … (m+1+1) τ` at any `v` in `[0,1)` (the worst-sequence
`w₀` of the band proof `QEndA:332-346`). BA sources of the drift classes exist and are merged:
```
$ grep -n "^theorem baHierDrift_\(kLink\|kLoop\|kTwo\|uStep\|expand\)\|^theorem baStep2Mat_KI\|^theorem ba_G_data" RBM3D/BA/*.lean | cut -c1-60
RBM3D/BA/GreenLDE.lean:55:theorem ba_G_data {d : ℕ} {κ ε 𝔠 𝔡
RBM3D/BA/GridDriftBA.lean:102:theorem baHierDrift_kLink (sz 
RBM3D/BA/GridDriftBA.lean:107:theorem baHierDrift_kLoop (sz 
RBM3D/BA/GridDriftBA.lean:263:theorem baHierDrift_kTwo (sz :
RBM3D/BA/GridDriftBA.lean:389:theorem baHierDrift_uStep (sz 
RBM3D/BA/GridDriftBA.lean:556:theorem baHierDrift_expand (sz
RBM3D/BA/Step2BA.lean:89:theorem baStep2Mat_KI {d : ℕ} (sz :
```
No `∀ n` drift premise; not a third `GridDriftNg` envelope (conclusion is the 𝒬-remainder bound): UP-C4 respected.

**D3: PASS.** `T2498_XiRoundPTgL''`, `T2498_OeqQtRoundPTgL''` identical to the check; band bridge compiles. **Bundle of
`stOeqQtRoundPTgL''_of` fixed** = the 22 hypotheses of `stOeqNQPTgL''_of` + `QProxyG_KerEK4Fam` (row 8) + `∀ κ > 0, ∃ C₆ > 0, …
Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆` (row 9, `∃ C₆` after `κ`, before `(sz, z)`) + `B45Gen_Facts` (row 9):
```
$ awk 'NR>=673 && NR<=757' RBM3D/Chain/NQEndFlowGen.lean | grep -oE "\(h[A-Za-z0-9₀']+ :" | tr -d ' (:' | tr '\n' ' '
hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hKerFam hR1 hT0      (22)
$ sed -n 269,270p RBM3D/BA/NewKLKBA.lean
private theorem NewKLKBA_tail (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
```
The BA tail constant depends on `κ`, so A4 (`∃ C₆` after `κ`) is required and matches the ticket's family table row 9. The check's
non-binding BA shape (`T2498-check.lean:257`: `∀ 𝔡, ∃ C₆, ∀ sz κ ε 𝔠 z`) puts `∃ C₆` before `κ`: observation for the dispatcher (the check
shape, not a pin). Band: `step5KerGen_thDecay_band` (`Step5KerGen:242`) gives `C₆(d, Λ)` under `∀ n, |E n| ≤ 2` (holds on `STFlow`).

**D4: PASS.** Scope = primed chain; mixed 8 + 2; layering (no Chain module of the in-place imports reaches a Q file other than
`QGridA`/`QGridB`, both above `QProxy`/`QEndA`; no BA module reached) reproduced (`rep2.out` SUMMARY line identical). Part 3 count:
```
$ sed -n 264,308p docs/tickets/checks/T2498-check.lean | grep -oE "@RBM\.[A-Za-z0-9_'.]+" | sort -u | wc -l
36          (= 32 in-place names + STXiRoundPT'', STOeqQtRoundPT'', stOeqQtRoundPT''_holds, altGridEndQN'; A5's 32, ticket text says 33)
```

## 4. Fill-in table (§269 (5)) and stop lines
(i)-(xiii) all present and backed by script output (rows reproduced in §1). (iii), (vii), (viii), (xi), (xiii) are filled already.
Stop lines checked: file over 2,000 — forecast max `QProxy` 1,800 central / 1,923 hi / 1,989 at ×1.60 (not hit); band reader outside
writable files needing an edit — none (G1 keeps 32 names); band `def` change — none (twins); in-place file importing a new file or a
downstream module — none; import cycle — none; binding `T2498_*` unprovable — D1 and the round bridge proved, conclusion of target 12 is
`T2498_OeqQtRoundPTgL''`; D1/D2 field without BA source — none; pinned `∃` after `(sz, z)` — none; `∀ n` drift premise — none (after the D2
fix the link is `∀ n`, as `hKK` in the ticket's row 11); new kernel / field / `BA/*` import / `STGridRepNgL` in writable row files — none
planned; restated merged text — none (D2 is a new envelope theorem, A2). No stop line is hit.

## 5. Row packing
```
$ grep -n "U3s3a total\|split at\|total a+b+c" $A/rep.out
40:siblings QProxy2 130 + QEndA2 70 = 200; U3s3a total added = 1981 / 2508 / 3167  (cut 1,950)
41:split at QLevelsB|QBudgetA: a1 = 971 / 1229 / 1551 ; a2 = 1009 / 1279 / 1616
43:total a+b+c central 4799 (lo 3814, hi 6375); ticket 4,830; UP-C3 line 5,850
```
The 1a central for U3s3a is 2,508 > 1,950, and even the low end (1,981) passes the cut: **the ticket's pre-signed cut applies:
U3s3a = `QProxy`, `QDriftA`, `QDriftB`, `QLevelsA`, `QLevelsB`, `QProxy2` (targets 1-6 and their part of 9) on `t/T2498` | U3s3a′ =
`QBudgetA`, `QBudgetB`, `QEndA`, `QEndA2` (targets 7, 8 and their part of 9) on `t/T2498a2`**, stacked, then U3s3b, U3s3c. Total central
4,799 < 5,850: no further row under UP-C3. The cut is pre-signed in the ticket (and in decision (7), "33 if row a splits"): no sign-off needed.

## 6. Observations (none changes a verdict)
- O1. The relief named in (a)(xii) for `QProxy` ("move the D1 band discharge to `QProxy2`, needs no reader") would break the band
  corollaries: `alt_hkerGridQN` (`QEndA:698`, a G1 name read by `QEndGrid`) reads `qProxy4C` through `QDriftA` (`grep -c qProxy4C`:
  QProxy 40, QDriftA 20, QBudgetA 69, QBudgetB 12), and `QProxy2` is imported only by `RBM3D.lean`. Not needed at the forecast (≤ 1,989).
- O2. A3: `Step5KerGen_ThDecay` has no concluder with that head; the planned band concluder (row a, ≈ 10 lines) closes the scan. Its BA
  owner is U4-BA (a) (ticket row 9).
- O3. The Lean instance does not use (a)(ii)'s numbers (`W = 2^16`, `A ≤ 36/25 + g²L³` instead of `W = 64`, `A = (κ+1)/κ`); (a″) says so.
- O4. The probe contains `sz.withLam 0` only inside the check's BA law shape (`:355`), never merged; 1b files must not.
- O5. Ticket says 33 Part 3 in-place names; the check has 32 (A5): price 20 × 15 = 300, not 495.

## Verdict
Stage-1a deliverables met (exponent table, nondegenerate instances, D1-D4, fill-in table, probe compiles with the standard three axioms),
no binding stop line hit. D2 text fixed above (all-`w` link); D3 bundle fixed above. Row packing: U3s3a | U3s3a′ (pre-signed cut).
**PASS.**
