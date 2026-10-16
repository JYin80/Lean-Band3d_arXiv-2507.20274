Auditor model: claude-opus-5-5
# T2519 1a-audit (Amend 1; design gate; no proof target) — Fri Oct 16 13:04 UTC 2026
Inputs: `docs/tickets/T2519.md`, `T2519-amend-1.md`, `checks/T2519-pins.lean`, `docs/supervisor/2026-10-16-1134.md`, `docs/reports/T2519-prove.md` (a), (a′), (a″).
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2519-1a-audit1` (detached `t/T2519` = b992c2e7, parent 25e22c0b = `main`). Scratch: `<scratchpad>/T2519/audit/`.

## 1. Probe compile, hygiene, diff
```
$ git diff --name-only main...HEAD ; git rev-parse main HEAD~1
RBM3D/Probe/T2519Pins.lean
25e22c0b62e0040357826deb2138a6d1326ee4d6   (both)
$ grep -cE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Probe/T2519Pins.lean
0
$ (date -u; lake env lean RBM3D/Probe/T2519Pins.lean; echo "exit=$?"; date -u)
Fri Oct 16 12:59:22 UTC 2026
'RBM.BA.T2519Probe.probe_ident' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2519Probe.probe_lead' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2519Probe.probe_Kt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
T2519_HoffBA : ℕ → Prop
T2519_LeadBA : ℕ → Prop
exit=0
$ lake env lean docs/tickets/checks/T2519-pins.lean; echo "pins exit=$?"; lake env lean docs/tickets/checks/T2519-check.lean | grep -c error
pins exit=0
0          (check exit=0)
```
Probe is 298 lines (ticket ≤ 200, cap 300): inside the cap. Branch-only file, never merged.

## 2. Statements: probe texts against the pins + Amend 1 item 1 (own script `audit/adiff.py`, comments stripped, token diff)
```
T2519_ProdBA: IDENTICAL        T2519_LLBA: IDENTICAL        T2519_QueBA: IDENTICAL
T2519_KFamBA: 1 change(s)   replace: [3] -> [4]                      (A1 (b): I.length ≤ 4 * 4)
T2519_PathBoundsBA: IDENTICAL
T2519_PBBA: 1 change(s)     replace: [3) 3] -> [4) 4]                (A1 (a): gueGridK sz 4, n0 = 4)
T2519_ProducersBA: IDENTICAL
T2519_HoffBA: 3 change(s)
   replace: [1] -> [4]                                               (F1: 1 ≤ n0 → 4 ≤ n0; not in A1)
   insert: [] -> [0 < g n →]                                         (F2: guard on Kt = m; not in A1)
   insert: [] -> [→ (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length → I.length ≤ 4 → ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1))]   (A1 (c))
T2519_EdRealBA / T2519_FlowEtaBA / T2519_KdiscBA / T2519_MapMixBA: in pins only (unchanged by Amend 1; compile in pins, exit 0)
T2519_LeadBA: in probe only (R1's leading expansion; statement, not a pin)
```
`hoff` conclusion against the merged C4 a text (own script):
```
GUEOneLoop:1208-1216 [K := gueGridK sz n0] == probe :90-98 : True 167      (tokens)
```
and by type: probe `:246` passes `T2519_HoffBA`'s conclusion as the `hoff` argument of `gueGrid_expect_oneLoopBA` at `K = gueGridK sz 4` (compiles).
A1 (c) form against C5H-C1: band `Hyp_Kt_detDom` (`HypA:707-711`) concludes `∀ ε > 0, ∀ᶠ n, ∀ t ∈ Icc (t1 n) (t0 n), ∀ I, I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 → ‖Kt n t I‖ ≤ N ^ ε * (gueScale sz E n t)⁻¹ ^ (I.length - 1)`; the premise is this with `gueScale ↦ N · etaOf (m n)` and range cut to `≤ 4`, i.e. C5H-C1 verbatim (not `C (2Λ_u)^{k-1}`).
F1/F2 judged: F1 is forced by Amend 1 item 3 (R1 reads `lk 4`; with `n0 ≤ 3` PB has no 4-loop field) and stays inside item 4 (`n0 ≥ 5` is admitted, not required; every consumer passes `n0 = 4`). F2 weakens a premise (scratch check `audit/A1.lean`: pins form ⇒ guarded form, compiles); its need is shown by the 1a's S3 (guard removed ⇒ 2 type errors at `:241`, `:289`, (a″)). The consumer use is eventual (`∀ᶠ n, 0 < g n`), so R1 is unaffected. Both are sound and I sign them; they go beyond the letter of Amend 1 item 1, so the dispatcher records them (see §8).
Quantifier order, losses, ranges: `3 ≤ d →` first; `(sz, κ, Λ)` then the families, then `n0`, `Kt`; all premises `∀ n` or `∀ᶠ n` as in the band `gueGrid_eq729` (`Eq729B:622-640`: `hlam` `∀ᶠ`, `hE`, `ht*` `∀ n`); the loss in the conclusion `‖M^B_aq‖ (N η_u)⁻¹` is sharp (no `N^ε` beyond `StochDomAt`). No structure field (all texts are `def … : Prop`); no circular dependency (probe imports 7 merged modules; closure has no `BA.MainInd|TwistPins|Step6|TwistStep|TwistAvg*`, (a″) `closure.py` output).

## 3. Exact-type chain (Amend 1 item 2) and the `d = 3` instance
Compiled in the probe (exit 0 above): `:199` (i) `T2519_ProducersBA → UNG1Rowk …` with the amended `PBBA`, `KFamBA`; `:209` `KFamBA ⇒ KClauses` at `g = √t₀λ`; `:235` (ii) `KClauses` + `Hyp_Kt_detDomBA`-form `hKdet` (range `≤ 2 * 4`) + PB ⇒ every premise of `T2519_HoffBA` (n0 = 4, `le_rfl`); `:246` hoff fit; `:277` `∃ Kt, KClauses …` at `sz0` (lengths `4 * 4`); `:286` `T2519_HoffBA 3` at `sz0`, `κ = 1/2`, `Λ = 10`, `n0 = 4`, every deterministic premise discharged; PB (row c) and the K-bound (row a's `Hyp_Kt_detDomBA`) stay hypotheses (other gates' pins).
Audit scratch (`audit/A1.lean` = probe `:1-297` + 3 examples; uncommitted):
```
$ (date -u; lake env lean <scratch>/T2519/audit/A1.lean | grep -vE "depends on axioms|^T2519_"; echo exit=0; date -u)
Fri Oct 16 13:02:10 UTC 2026
exit=0
Fri Oct 16 13:02:26 UTC 2026
```
(1) one concrete `Kt` (from `gueK_existsBA`) with `KClauses` **and** the discharged `Kt = m` premise at once; (2) `∀ᶠ n, 0 < inst_g n ∧ inst_g n ≤ 10` and `∀ n, inst_t1 n < inst_t0 n` (window of positive length); (3) F2 weakening. Nondegenerate: `N_0 = 2^21`, `L ≥ 4`, window `δ/N > 0`.
```
$ python3 -I inst_check2.py      (rerun; identical to (a″))
0    | 0.0625 (<= 1: True) | 0.5 | 0.25 | 9.54e-07 <= 4.830e-01: True | 4.000e+00 <= 4.830e-01: False
100  | 0.0625 (<= 1: True) | 5.152e+05 | 2.576e+05 | 7.97e-43 <= 7.586e-03: True | 3.882e-06 <= 7.586e-03: True
```
Observation (1b, not a defect here): `Hyp_Kt_detDomBA`'s text is not pinned; row a must conclude exactly `hKdet`'s form (`:238-240`).

## 4. D1 (i) under Amend 1 items 3–4 (reruns, seeded scripts, identical to the report)
```
$ python3 -I kb.py | head -3                                (diff kb.out: identical)
row4': L4 exp 3 L2 exp 1 -> |S1|,|S2| exp 2 (needed 2); beta exp 2 -> T exp 1 (needed 1)
   entrywise-only (a) row 4: |S_i| exp 3/2 -> T exp 3/4
n0=4: lk fields k<=n0: [1, 2, 3, 4]; gueGridK exponent 192; Hyp_Kt_detDom |I| range [2,8] needs {2,4}: ok (slack 4); hK / KFam length bound 4*n0=16; lk 4 present: True; eq729 (3<=n0): ok
$ python3 mc_p2.py A | grep "(q,a)=(0,0)"
   (q,a)=(0,0): E|T|^4=2.657e-02; self=-1.784e-02, S1-term=-2.486e-02, S2-term=6.917e-02; |E|T|^4-sum|=1.7e-03 (z=0.48); control drop S1-term: 2.8e-02, drop S2-term: 7.5e-02; ...; CS(HS) S1 bound/Lam^2=3.100, S2 bound/Lam^2=3.388
$ python3 mc_loops.py
[loops] N=512 Lam=4.524e-01 Nη=2.21 S=300: E max_r L4_r/Lam^3 = 2.549 (max over samples 29.844); E max_(q,a) L2/Lam = 2.349 (max 7.181)
[loops] N=1728 Lam=1.340e-01 Nη=7.46 S=30: E max_r L4_r/Lam^3 = 1.110 (max over samples 1.982); E max_(q,a) L2/Lam = 1.036 (max 1.227)
$ python3 lead_check.py           (T2519_LeadBA at d = 1, 10^6 samples; 2nd line = wrong σ control)
... sigma_scale=1.0 S=1000000: max|E T|=1.974e-01; max|E[T - RHS]|=6.167e-04; max z=0.97; mean z=0.53
... sigma_scale=1.5 S=1000000: max|E T|=1.973e-01; max|E[T - RHS]|=7.153e-02; max z=124.92; mean z=110.42
$ python3 mc_hoff.py A | grep -E "pathwise|\(q,a\)=\(0,0\)"      (p = 1; matches (a) run A)
    pathwise: max_p|g_p-m|/Lam=4.74; max_(q,a)|twTr|/Lam=4.74
    pair (q,a)=(0,0): E|T|^2=1.034e-01; self-term+R2 = 1.003e-01 (+6e-03i); |diff|=6.6e-03 (z=1.6); ...; CS(HS) bound/Lam^2=3.387; ...; negative control (R2 dropped): |E|T|^2-self|=1.65e-01
```
Written argument checked: exact p-moment identity (self + `𝒮₁` (`p ≥ 2`) + `𝒮₂`) re-derived from `G − M = −M(X+um)G` and Gaussian IBP; HS pairing 4-loop `≺ Λ³` × 2-loop `≺ Λ` gives `Λ²` on both derivative terms (exponent slack 0, losses inside `≺`); self-term coefficient `u ρΛ_u C_M`, `C_M = BAct_rate⁻¹·expC` depends on `(d, Λ, κ)` only (`probe_lead`, compiled) ⇒ C5S-C2 not hit; union exponent `(N+1)^{192}·N²` absorbed by fixed `p ≥ 2040` (row 7′). Inputs used ⊆ Amend 1 item 3: PB `lk 1..4` + `localLaw` and the K-bound at the grid time, `Kt = m` on 1-loops, `BAReal`, `baM_row_l1`/`baM_rho2`, `ol_gueHBA_eq`/`mixMatBA`, `BA/TwistAvg*` lemmas (listed in (a′)). No twisted 2-loop, no `twTr` at `t₁`, no `n0 ≥ 5` required, no extra `gueGrid_eq729BA` premise (`:235` uses only the band-twin premises). **Item 4 stop: not hit.**
Observation for the dispatcher: (a′) plans `open private TwistAvgB_S1, _markov, _expo, _union from RBM3D.BA.TwistAvgB` and imports `BA/TwistAvgA2`/`B`, which puts `RBM3D.BA.TwistPins` (TL pins, not V) in the closure. Decision (10)/item 3 allow merged `BA/TwistAvg*` lemmas "read by name"; reading their *privates* via `open private` (the layout authorises that for the twelve band files only) and the `TwistPins` closure are not ruled on.

## 5. D1 (ii)–(v)
- (ii) vocabulary: `PathBoundsBA` (fields `lk k`, `localLaw` against `Mres`; no twist field), `KFamBA`, `PBBA`, `ProducersBA`, `ProdBA/LLBA/QueBA` at exact type (`:199`; pins `:61-70`). C1 regex on both files (own script, comments stripped): probe 0 hits; pins 1 hit = the allowed `ouP (UNModel.band (sz.withLam 0))` (`MapMixBA`). `Pgue` only at `sz.withLam 0` (0 exceptions); `sz.lam` only in `√t₀ · sz.lam` wrappers (UBA-C1). No `RBG_*` text changes ⇒ D1 (ii) stop not hit.
- (iii) `hKb` from `Ed κ'` + eventual scale rows + `BAFlow` on an eventually equal `z′`, padding ≈ 40 ((a) rows 6, 12; S0: `W^{-d}B = 0.344 ≤ 0.440`); no primed `RBG_Prod` ⇒ stop not hit.
- (iv) L1 (rerun `central.py`): `Duhamel layer: … x2.54: pure -1059 wide -160 (C5S-C3 needs >= 500 at x2.54)` ⇒ L1, no REQ. Layout L1 signed.
- (v) `M`-local law: rerun greps `zt`/`gueH` per file reproduce (a) exactly (Proc 76/42, HypA 26/19, HypB 51/52, BoundsA 19/18, PathBounds 6/6, EntryGrid 20/27); `mE…•` counts reproduce for five files (Proc 8, HypA 2, HypB 12, BoundsA 15, PathBounds 3), EntryGrid 11 vs (a)'s 5 (regex not stated; observation). `norm_egtNGUE_le` (`Proc:596-601`) reads only `avgErr` (diagonal) and loop bounds: confirmed.

## 6. Census, split, reserves, C5S-C1 (reruns identical)
```
$ python3 -I central.py | tail -6
row a: pure 1704 wide 2184 mean 1944  vs cap 1950: pure ok (slack 246), wide OVER (-234), mean ok (6)
row b: pure 1636 wide 2535 mean 2086  vs cap 1950: pure ok (slack 314), wide OVER (-585), mean OVER (-136)
row c: pure 1645 wide 2098 mean 1872  vs cap 1950: pure ok (slack 305), wide OVER (-148), mean ok (78)
row d: pure 1429 wide 1495 mean 1462  vs cap 1950: pure ok (slack 521), wide ok (455), mean ok (488)
total: pure 6414 wide 8312 mean 7363; C5S-C1 line 9025: wide slack 713; ...
$ python3 -I price7.py | tail -9           (diff price7.out: identical)
central-equivalent, /1.34 (ticket's recent-landing ratio, T2519.md Price): lo 1243 central 1628 hi 2112
   row b unsplit pure 2404 (cap 1950: OVER), with lo 2019
   C5S-C1: total wide central = 8312-860+1628 = 9080 vs 9025: FIRES (margin -55); lo 8695, hi 9564; trigger T = 1573
central-equivalent, /1.46 (TL1's own landed/design: 2,817/1,936): lo 1145 central 1499 hi 1945
   row b unsplit pure 2275 (cap 1950: OVER), with lo 1921
   C5S-C1: total wide central = 8312-860+1499 = 8951 vs 9025: does not fire (margin +74); lo 8597, hi 9397; trigger T = 1573
```
(GUETwistBA landed basis, undeflated: 2,181 wc lines ⇒ total 9,633.)
- **Rows' 1a central against 1,950 (pure, Decision (3)):** a 1,704, c 1,645, d 1,429 ≤ 1,950; b unsplit 2,404 > 1,950 ⇒ **reserve b′ booked** at the 1a (pre-signed; Amend 1 item 5): b = `GUEDuhamelBA` (+`GUEDuhamelBA2` past 1,500; wide 1,675), b′ = `GUETwistBA` 1,628 (hi 2,112). **a′, c′ not booked.** Split a | b | b′ | c | d at the ticket's file boundaries: signed, subject to §7.
- Per-file stop lines: none above 2,000 at the central (`GUETwistBA` hi 2,112 exceeds 2,000 at the upper end only); `GUEDuhamelBA` wide 1,675 > 1,500 ⇒ its reserve file.
- **C5S-C1 (fixed 9,025 against the total wide central, supervisor 1134 Q2): 9,080 at the ticket's own calibration ratio 1.34 (the 1a's primary figure) ⇒ the line is crossed by 55**; 8,951 (margin 74) only under the alternative ratio 1.46. The stop rule reads "the 1a's rerun puts C5's total wide central above 9,025 → short REQ before any 1b". At the 1a's primary figure the rerun is above the line, so I treat it as **hit**. Choosing between the two ratios changes the outcome and is a dispatcher decision, not an audit one.
- Counts with b′: M/N rows a–d = 13–16, b′ = 17, N2 = 18 ≤ flag 20; no REQ on counts.

## 7. 1a fill-in table (§269 (5)) coverage
(i) constants ✓ ((a) rows 2, 3, 7′, 9); (ii) instance + script ✓; (iii) D1 (i)–(v) ✓; **(iv) coverage as used: missing**; (v) census per file, split, reserves ✓; (vi) hoff vs `T2517_OneLoopBA` ✓; (vii) C1/UBA-C1 greps: not in the report, run here (§5 (ii): 0 hits); **(viii) registry preview: missing**; (ix) imports/closure ✓ (with §4 observation); (x) lines per file vs stop lines ✓; (xi) name clash: the report covers 28 probe names + 6 of the ticket's list; the full list (own grep, `main`+probe) is clean:
```
GUEPathBoundsBA=0 BAKFam=0 BAPB=0 gueDevBA=0 gueStopBA=0 gueLmaxBA=0 gueDmaxBA=0 gueLprocBA=0 gueDprocBA=0 Hyp_Kt_detDomBA=0 Hyp_Kt_oneBA=0 Hyp_gridBA=0 gueKproc_detDomBA=0 norm_egtNGUEOf_le=0 gueDevBA_succ_le=0 gueGrid_entry_boundBA=0 map_gueHBA_eq_mixMatBA=0 gueGrid_loop_duhamelBA=0 Duhamel_drift_remainder_aeBA=0 gueGrid_twistBA=0 Bounds_pathBA=0 gueGrid_pathBoundsBA=0 oull_of_pathBoundsBA=0 gueGrid_eq729BA=0 baEq729_Kdisc=1 ba_prodG=0 ba_LLG=0 ba_QueG=0 twTrBA=0
(baEq729_Kdisc=1: comment, BA/GUEEq729BA.lean:47) ; all ten BA/GUE*BA.lean, GUEHyp.lean: absent
```

## 8. Paper deltas
`T2519a` (GUE grid needs (I3) at `n = 4`: PB to `n0 = 4` vs band 3; twisted 1-loop law with T.7's input set; `p` carries the grid union) — C5H-C4 covered. `T2519b` (grid local law against `M^{(B)} ⊗ 1`) covered. `T2519c` (positivity guard, now used by F2) covered in (a″). F1 (`4 ≤ n0`) is inside `T2519a`. No uncovered Lean/paper difference found.

## 9. Verdict
Signed (statement level): `T2519_ProdBA`, `T2519_LLBA`, `T2519_QueBA`, `T2519_PathBoundsBA`, `T2519_ProducersBA` (pins verbatim); `T2519_KFamBA`, `T2519_PBBA` (Amend 1 item 1 (a), (b)); `T2519_HoffBA` (item 1 (c) + F1 + F2, probe `:79-98`); `T2519_EdRealBA`, `T2519_FlowEtaBA`, `T2519_KdiscBA`, `T2519_MapMixBA` (pins, unchanged); item 2 examples; D1 (i) under items 3–4 (no item 4 stop); D1 (ii)–(v); layout L1; census with `GUETwistBA` repriced per item 5; split a | b | b′ | c | d (b′ booked; a′, c′ free).
**RETURN, needs dispatcher sign-off.** Defect: binding stop line **C5S-C1 is hit**. The 1a's rerun puts the total wide central at 9,080 > 9,025 at the ticket's calibration ratio 1.34; the alternative ratio 1.46 gives 8,951. Under T2519 Stop rules (C5S-C1), this is a short REQ before any 1b (H183 (3)); no 1b row starts.
Required for resubmission:
1. Dispatcher/supervisor ruling on C5S-C1. Either the line is hit (9,080) and C5's budget is re-decided, or a ruling that the TL1-calibrated `GUETwistBA` central is deflated by ×1.46 (8,951, margin 74).
2. The dispatcher records F1 (`4 ≤ n0`) and F2 (`0 < g n →` guard) in the signed `T2519_HoffBA` text (an amend line), since they go beyond Amend 1 item 1.
3. The dispatcher rules on `open private … from RBM3D.BA.TwistAvgB` and on the `BA.TwistPins` closure of the `TwistAvg*` imports (§4).
4. The report adds fill-in rows (iv) "coverage as used" and (viii) "registry preview" (one line each, or "n/a, because …").
