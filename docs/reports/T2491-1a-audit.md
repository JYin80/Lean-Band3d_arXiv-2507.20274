Auditor model: claude-opus-5-5

# T2491 1a-audit (design gate D1-D5, probe, row packing) — Tue Oct 13 06:46:50 UTC 2026
Inputs: ticket, check `docs/tickets/checks/T2491-check.lean`, `docs/reports/T2491-prove.md` (a) l.3-92 (90 lines), (a″) l.94-177. Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2491-1a-audit` (detached at `t/T2491` = 9b4bc546). Scratch `$A` = scratchpad `T2491/audit1a/`;
the prover's scripts `$S` = scratchpad `T2491/` were run unmodified.

## 1. Numerics rerun (section (a) (i)-(ii), (xii))
```
$ cd $A; python3 $S/kerD1.py > kerD1.out; python3 -I $S/expo.py > expo.out; python3 -I $S/thresh.py > thresh.out   (all exit 0)
$ diff <(cat kerD1.out expo.out thresh.out) <(sed -n '29,52p' docs/reports/T2491-prove.md) && echo IDENTICAL
IDENTICAL to report lines 29-52
$ cd <audit wt>; python3 -I $S/size.py > $A/size.out; diff $A/size.out <(sed -n '77,88p' docs/reports/T2491-prove.md)
size IDENTICAL to report lines 77-88
$ python3 -I $S/hand.py | awk '/regenerated decls/{printf "%s %s; ", $1, $6}'   (regenerated band lines per file)
NQGood1 580; NQGood2 471; NQBudget 678; NQLin 778; NQEndLin 647; NQEndFlow 479;
```
The counts 580/471/678/778/647/479 used by `size.py` match `hand.py`. D1 at band and BA (`g₀ < g`, `A = g²/g₀²`), the 20 end-arith
inequalities, WO/Bandwidth (0 violations), RangeCond and D2's `(1-T0)⁻¹ ≤ N` reproduce; the R1 crossings (`log10 W ≥ 45.8 … 260.4`)
are eventual limit checks only (the Lean instance is at band `A = 1`, `τ' = 0`: `d·W^0 = 3 ≤ W^ε = 4`).

## 2. Probe recompile (`lake env lean`, audit worktree)
```
$ date -u; lake env lean RBM3D/Probe/T2491Pins.lean; echo "exit code: $?"; date -u
Tue Oct 13 06:43:17 UTC 2026
new premises found by the scan: [RBM.BA.T2491_EnvelopeEv]; with probe_kerNAL_band_at withheld: [RBM.BA.T2491_EnvelopeEv,
 RBM.BA.T2491_KerNAL]
RBM.BA.probe_kerNAL_band_at: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerNALFam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kLipFam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_shiftSpec_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_r1Fam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerNALFam_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_shiftSpec_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_r1Fam_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_hkerNg: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_hker_instance: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_band_szB: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_ba_sz0: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_envelope_of_ev: [propext, Classical.choice, Quot.sound]
exit code: 0
Tue Oct 13 06:43:36 UTC 2026
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2491Pins.lean; wc -l < RBM3D/Probe/T2491Pins.lean
0
397
$ git diff --stat main...HEAD | tail -2
 RBM3D/Probe/T2491Pins.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 397 insertions(+)
$ lake env lean docs/tickets/checks/T2491-check.lean > $A/check.out 2>&1; echo "check exit $?"; grep -c error $A/check.out
check exit 0
0
$ lake env lean $S/d5_ev.lean     (scratch proof of the D5 text)
'RBM.BA.scratch_envelope_ev' depends on axioms: [propext, Classical.choice, Quot.sound]
d5_ev exit 0
```

## 3. Class texts (check vs probe; D5 scratch vs probe), name clashes
```
$ for nm in T2491_KerNAL T2491_KerNALFam T2491_KLip T2491_KLipFam T2491_ShiftSpec T2491_R1Fam; do <extract def block from check / probe>; diff; done
T2491_KerNAL check 10 lines, probe 10 lines, diff: 0
T2491_KerNALFam check 5 lines, probe 5 lines, diff: 0
T2491_KLip check 4 lines, probe 4 lines, diff: 0
T2491_KLipFam check 4 lines, probe 4 lines, diff: 0
T2491_ShiftSpec check 3 lines, probe 3 lines, diff: 0
T2491_R1Fam check 6 lines, probe 6 lines, diff: 0
$ diff <(ext d5_ev.lean) <(ext T2491Pins.lean)    (def T2491_GridDriftNgAt … end of def T2491_EnvelopeEv)
D5 block GridDriftNgAt..EnvelopeEv: scratch = probe (      39 lines)
$ for r in main t/T2491 t/T2492 t/T2486b t/T2489b t/T2493; do git grep -w -E "GridDriftNgAt|gridDriftNg_envelope_ev|NQGoodGen_KerNAL|NQEndFlowGen_KLip|nqGoodGen_kerNAL_band" $r -- RBM3D ':!RBM3D/Probe' | wc -l; done
main: 0   t/T2491: 0   t/T2492: 0   t/T2486b: 0   t/T2489b: 0   t/T2493: 0
```
`T2491_HQg` (check :334-337) against `azumaProxy_subG_goodExitg`'s `hQ` (`AzumaProxyGen.lean:237-238`): same binder
`∀ M, GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' M → M.IsHermitian → gridStep … * ((k:ℝ) * qvFormNg …) ≤ (Q:ℝ)` (read by eye; verbatim).

## 4. Design items D1-D5 (statement-centred)
- **D1 PASS.** Text fixed = check `T2491_KerNAL` (:342) / `T2491_KerNALFam` (:355), diff 0; 1b names `NQGoodGen_KerNAL`, `NQGoodGen_KerNALFam`.
  `∃ Ck` sits after `(k, κ, ε, 𝔡)` and before `(sz, 𝔠, z)` (no F1). Band discharge compiled for all `d` (`probe_kerNALFam_band`,
  `Ck = nqGood1C d k 𝔡⁻¹ (min κ (4/5))`, inside `∀ᶠ n` from `WO`); BA discharge compiled (`probe_kerNALFam_ba`: `baEKSumDecayNAL_holds`,
  `Step2Kern_UN_BA`, `BAflow_real`, `BAflow_lam0_window`) and instantiated at the merged `(sz0, zSeq, flow_sz0)` (`probe_ba_sz0`).
  No BA source missing. A1 holds: the scan lists `T2491_KerNAL` exactly when the per-index band theorem is withheld, so the 1b
  needs both `nqGoodGen_kerNAL_band_at` (per index) and `nqGoodGen_kerNAL_band` (family).
- **D2 PASS.** Text fixed = check `T2491_KLip` (:363) / `T2491_KLipFam` (:369), diff 0; 1b names `NQEndFlowGen_KLip(Fam)`. Band discharge
  `probe_kLipFam_band` from `stKloop_lip` + `v3_premises_of_stFlow` (guarded by the flow; `0<κ`, `0<ε`, `3≤d` used); instantiated at
  `(szB, zB)` (`probe_band_szB`). Premise of no target here; BA twin owner U3-BA (BA text only typechecked, probe :246-248).
- **D3 PASS.** Inline `∀ n, ‖Cm.m n‖ ≤ 1` (DECISIONS §294 (3) (5)); band `probe_shiftSpec_band` (`norm_mE`), BA `probe_shiftSpec_ba`
  (`BAm_norm_le_one`, `BAflow_real`) and at `(sz0, zSeq)`. (M3) `‖z_u − z_u'‖ = |u−u'|‖m‖`, `η_u = (1−u) Im m` is what the shift layer needs.
- **R1 (UBA-C1) PASS.** `T2491_R1Fam` (diff 0) is the §271 (4) form; band (`A = 1`) and BA (`(κ+1)/κ`, `TwistStep2_lam0_sq`) compiled.
  Target 2 shape `probe_hkerNg`: hypotheses `hcmp` (the R1 text), `1 ≤ A`, `hKer : T2491_KerNAL C gK k Ck n`, `Ck ≤ Cv`,
  `hdW : d·√A·W^{τ'} ≤ W^ε`, `hAk : A^{k−1} ≤ W^{(Cv−Ck)ε}`; conclusion = band `hker_of_case1N` (NQGood1:310) with `nqGood1C ↦ Cv`,
  `g ↦ sz.lam`. `hdW`, `hAk` are W-crossings at the index, not a second comparison form; at `A = 1`, `Cv = Ck` they are the band's
  `hdW` and `1 ≤ W^0`. Not the stop "a comparison other than R1". (UBA-C1 row (e) `step34Gen_decayK_of_cmp` is the stochastic
  `STEKDecayKgL` conversion for the ℰ-decays, separate from `hdW`; it stays as planned for target 14.)
- **D5 PASS (DECISIONS §294 (3) (9)).** Text fixed = probe `T2491_GridDriftNgAt` (:89-105, the body of `GridDriftNg` at one `n`;
  `GridDriftNg ↔ (… → ∀ n, GridDriftNgAt …)` by `Iff.rfl`, :107-109) and `T2491_EnvelopeEv` (:122-128: `gridDriftNg_envelope` with
  `hGD : ∀ᶠ n, GridDriftNgAt …`, same conclusion). Proved in scratch (`d5_ev.lean`, exit 0, standard axioms); merged form recovered by
  `Eventually.of_forall` (`probe_envelope_of_ev`). Per-index producer exists: `gridDriftNg_at` (HierDriftGen:818) concludes exactly the
  `GridDriftNgAt` body from the per-index classes `HierDriftGen_Expand/KLoop/KTwo/UStep/KLink … n` (defs :320-677 take `n`).
  1b names `GridDriftNgAt`, `gridDriftNg_envelope_ev` (0 hits above), in `NQEndLinGen` (only reader `nqEndLin_assembly`, NQEndLin:816).
- **D4 PASS.** Lift `stOeqNQ''_holds` dropped (§294 (3) (2)); scope table (viii), `open private` list (xi) and the census are present.

## 5. Row packing, stop lines, C6
```
$ python3 -I $A/pack.py    (contiguous blocks in band import order; files NQGood1Gen … NQEndFlowGen)
1a central (bottom-up, size.py): total 5360; max file 1057 (>1800: []); best 2-row split after NQBudgetGen: max row 2874 (<=1950: False); pre-signed rows a|b|c = 1634/1909/1817; 3-row splits <=1950: 1; fourth row (total>5850): False; C6 edit+twin 5710 > 6150: False
ticket formula, pure regex: total 3740; max file 818 (>1800: []); best 2-row split after NQBudgetGen: max row 1966 (<=1950: False); pre-signed rows a|b|c = 1078/1384/1278; 3-row splits <=1950: 4; fourth row (total>5850): False; C6 edit+twin 4090 > 6150: False
ticket formula, wide regex: total 4234; max file 874 (>1800: []); best 2-row split after NQBudgetGen: max row 2304 (<=1950: False); pre-signed rows a|b|c = 1222/1582/1430; 3-row splits <=1950: 3; fourth row (total>5850): False; C6 edit+twin 4584 > 6150: False
```
- **Row packing: the pre-signed three rows are confirmed, no merge to two.** U3s2a = `NQGood1Gen` + `NQGood2Gen` (targets 1-6, 1,634) /
  U3s2b = `NQBudgetGen` + `NQLinGen` (7-10, 1,909; `t/T2491b`) / U3s2c = `NQEndLinGen` + `NQEndFlowGen` (11-15, 1,817; `t/T2491c`).
  The 1a central 5,360 > 3,900, and no two-row packing keeps both rows ≤ 1,950 under any of the three readings (even the 3,740
  reading's best split is 1,774 / 1,966). At the central the pre-signed split is the only three-row split with every row ≤ 1,950.
- **No fourth row:** the 1a central is 5,360 ≤ 5,850 (margin 490). The binding figure is the 1a central (ticket: "1a central > 5,850");
  the prover's 1.57× T2484 extrapolation (6,440) is not the 1a central, so no REQ.
- **Per file:** max central 1,057, max hi (×1.38) 1,459: below the 1,800 reserve trigger and the 2,000 stop line. The prover's proposed
  reserves `NQLinGen2`, `NQEndLinGen2`, `NQGood1Gen2` (2.6× stress) are **not ratified**: the ticket's reserve rule (1a prediction > 1,800)
  does not fire, so the sole writable files stay the six named files (a file reaching 2,000 in the 1b is a stop).
- **C6:** edit + twin = 5,360 + 350 = 5,710 ≤ 6,150: no notice.
- **Stop lines (ticket "Stop rules"):** none hit. Files ≤ 2,000; binding `T2491_*` conclusions unchanged (check compiles); D1, D3 have BA
  sources (compiled); no pinned `∃` after `(sz, z)`; family premises guarded (KerNALFam, KLipFam, ShiftSpec, R1Fam take `Flow`);
  no new kernel, carrier field, `STGridRepNgL` premise or band/merged edit (diff = the probe only); no `sz.withLam`; coupling `gK` only;
  new `Prop` premises in the scan: `T2491_EnvelopeEv` (proved in scratch; the 1b concludes it) and `T2491_KerNAL` (concluded by the band
  theorem, A1). BA imports are in the probe only (four `BA/*` imports, allowed for the BA readings).

## 6. H250 (4) fill-in table (ticket rows (i)-(xiii))
| row | present | audit result |
|---|---|---|
| (i) exponent table | (a) l.6-24 | 16 rows; script outputs reproduce (§1) |
| (ii) D1 instance band + BA (`g₀<g`, g = 1/64, 1, 10) | (a) l.25-53 | reproduced (§1); Lean instances `probe_hker_instance`, `probe_band_szB`, `probe_ba_sz0` compile (§2) |
| (iii) hypothesis table | (a) l.65, (a″) l.157 | compiled band/BA discharges for D1, D2, D3, R1 |
| (iv) D1 decided, probe lines | (a) l.55, (a″) l.158 | §4 |
| (v), (vi) D2, D3 decided | (a) l.56-57 | §4 |
| (vii) family-premise table | (a) l.68, (a″) l.161 | rows 1-12 named; rows 1, 3, 4, 9 owed by T2486/T5-BA (name-level at 1b start, §294 (3) (10)) |
| (viii) scope table | (a) l.69 | counts match `hand.py` |
| (ix) UBA-C1 table | (a) l.70, (a″) l.163 | R1 only; §4 |
| (x) premise-scan preview | (a) l.71, (a″) l.164 | reproduced (§2 first line) |
| (xi) `open private` list | (a) l.72, (a″) l.165 | lists given; name-level at 1b start |
| (xii) lines per file, split, C6 | (a) l.75-90 | §5 |
| (xiii) name-clash grep | (a) l.74, (a″) l.167 | 0 hits; my grep of the D-item names also 0 (§3) |
D1-D5 all decided; 13 of 13 rows filled.

## 7. Observations (no RETURN)
- O1. Row U3s2b has 41 lines of headroom under 1,950 at the central; the per-file stop line 2,000 binds in the 1b.
- O2. The 1b's endpoint instances must keep the decay clause non-trivial as `probe_hker_instance` does (diagonal `X`, `ellT > 0 = diam`),
  and the BA readings of R1 crossings (`hdW`, `hAk`, thresholds `log10 W ≈ 88-260`) are eventual only: state them as `∀ᶠ n` premises
  discharged by limits, not by a concrete witness.
- O3. Paper-delta coverage for the 1b report: `T2491a` should also name D5 (drift premise eventual, §294 (9)) and the BA vocabulary
  constant `Cv = Ck + 1` with the `√A` crossing in target 2.

## Verdict
**PASS** — every stage-1a deliverable (D1-D5, probe, H250 (4) rows (i)-(xiii)) is met and no binding stop line is hit. Fixed texts:
D1 = check :342-362, D2 = check :363-375, D5 = probe :89-128 (`GridDriftNgAt`, `gridDriftNg_envelope_ev`). Rows: the pre-signed three
rows U3s2a / U3s2b / U3s2c (no two-row merge, no fourth row). No dispatcher sign-off needed; the 1b may start with U3s2a.
