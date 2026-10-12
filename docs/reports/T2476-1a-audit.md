Auditor model: claude-opus-5-5
# T2476 1a-audit (design gate D1 + probe) — Mon Oct 12 23:03:40 UTC 2026
Inputs: ticket `docs/tickets/T2476.md`; check `docs/tickets/checks/T2476-check.lean`; report `docs/reports/T2476-prove.md` (a), (a″).
Audit worktree `../RBM3D-wt/T2476-1a-audit` (detached at `t/T2476` 86eecc2d; main ab435c6e). Scratch: `scratchpad/T2476/audit/`.

## 1. Diff and base
```
$ git diff --stat main...HEAD
 RBM3D/Probe/T2476Pins.lean | 300 +++++++++++++++++++++++++++++++++++++++++++++
$ git diff --stat eaa247c4 ab435c6e -- RBM3D        # main moved since the branch point
 RBM3D/Chain/CltGen.lean | 5 +++--                  # docstring R1 (H260); not in any T2476 cone
```
Only the probe (≤ 300 lines, never merged, no root import). No sole writable file touched yet (1a stage).

## 2. Probe recompile (`lake env lean`, own worktree)
```
$ date -u; lake env lean RBM3D/Probe/T2476Pins.lean; echo "exit $?"; date -u
Mon Oct 12 22:59:09 UTC 2026
'RBM.Univ.T2476_ouMatC_ba_add' depends on axioms: [propext, Classical.choice, Quot.sound]
  (same line, verbatim, for the other 12 probe declarations: grid_energy_win, hdiagWin_of_band, keff, hdiagWin_of_K, hbad_of_K,
   BulkWindowk_band/_ba, BadBoundk_band/_ba, Bad2Boundk_band, bad2_subset_ba, Bad2Boundk_ba)
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
Mon Oct 12 22:59:17 UTC 2026
$ grep -ci "error\|warning\|sorry" probe.out  ->  0 ;  wc -l probe.out -> 39 (5 #check blocks + 15 axiom lines + exit)
```
Proposals in the probe vs the check file (extracted `def … ` blocks, `diff`):
```
T2476_BulkWindowk: check 3 lines, probe 3 lines, diff: 0
T2476_BadBoundk:   check 12 lines, probe 12 lines, diff: 0
T2476_Bad2Boundk:  check 13 lines, probe 13 lines, diff: 0
T2476_unEMCTE2k_ba: check 3 lines, probe 3 lines, diff: 0
```
`open private Jak_fixed_time Jak_queBound_eq … Uyw_fixed_time Uyw_queBound_eq` (probe 25-26) elaborates: dispatcher answer (4)
(K-forms in the leaf by `open private`, no `PinsK` import in band files) is reachable.

## 3. D1: bulk-window finding against T2449 MN3
T2449 MN3 (`T2449-design.md:13`, §4 `:119`) prices E2 as a two-coupling generalisation only; its B5 table counts carrier
tokens (`T2449-prove.md:211-214`), not the bulk. The band bulk sits in the private lemmas:
```
$ grep -n "2 - κ" RBM3D/Universality/{Jak,Uyw}.lean (code lines)
Jak:355 (hE : |E| ≤ 2 - κ) [Jak_grid_energy_lt]   Jak:570 (hE …) [Jak_fixed_time]   Jak:574 (hdiag : ∀ e, |e| < 2 - κ / 2 → …
Uyw:329 (hE …) [Uyw_grid_energy_lt]                Uyw:506 (hE …) [Uyw_fixed_time]   Uyw:509 (hdiag : ∀ e, |e| < 2 - κ / 2 → …
$ grep -n "bulk :=" RBM3D/BA/UNPins.lean RBM3D/Universality/PinsK.lean
UNPins.lean:87:  bulk := fun sz κ E n => BAbulk d (sz.L n) (sz.lam n) κ E          # BAbulk = κ ≤ BArho (MFixedPoint:429)
PinsK.lean:318:  bulk := fun _ κ E _ => |E| ≤ 2 - κ
$ awk 'NR>=575&&NR<=853&&/hdiag|grid_energy|\bhE\b/' Jak.lean ; same for Uyw 510-792
700: have he := Jak_grid_energy_lt hηt0 hE hq1 hq0 hqκ (by rw [hηt]; exact h3) hj
701: have := hdiag _ he
643: have he := Uyw_grid_energy_lt hηt0 hE hq1 hq0 hqκ (by rw [hηt]; exact h3) hj
644: have := hdiag _ he
```
Finding confirmed: `hE` and `hdiag` are used only at the grid energies (one call each), so the window form
`|e − E| < κ/2` (probe `T2476_grid_energy_win` :79, same proof without `hE`) is a private change. Uses of `lam` in the two
fixed-time lemmas (grep): `hlam`, `hque`, `scirc`, `blockM`/`blockM2`, `measure_bad*_le_of_queBadMat`, `*_pointwise_*`
(kernel calls take `lam` with no hypothesis): the (v) table's two-coupling split (`lamV` in scirc/blockM, `hbad` replacing
`hlam`+`hque`) matches. Discharges compiled (§2): band window from `|E| ≤ 2 − κ` (`T2476_hdiagWin_of_band`), any kind from
`UNOUDiagk` + `T2476_BulkWindowk` at `κ_eff ≤ 2r` (`T2476_hdiagWin_of_K`), BA window `κ' = κ/2`, `r = (πκ)³/8`
(`T2476_BulkWindowk_ba` by `BAbulk_window`); transfers: band (`measure_bad_le_of_queBadMat`, `measure_bad2_le_of_queBadMat`),
BA (`unBadY_of_blockM` + `unBadYBA_measure_le`; one-block pair lemma `T2476_bad2_subset_ba`, 51 lines + 7). Jak's `hbad`
from `T2476_BadBoundk`, `UNOUQUEk` and `sz.WO` (`T2476_hbad_of_K`): no premise beyond the allowed list (`3 ≤ d`, `WO`
are binders of the check-file K-form shapes / `Admissible`). The target 5 (c) form fits `UNJakUywRowk` (`PinsK:435`:
`∀ κ > 0, ∀ E, (∀ᶠ n, (K d).bulk sz κ E n) → …`). D1: PASS.
Not compiled by the probe (outside answer (1)'s scope; prover's observation (4)): the edited `Jak_fixed_time`/`Uyw_fixed_time`
proofs and E1 (`eq225_intervalShift`, translation lemmas). E1 plan check (signatures): `ouGenerator_hasDerivAt_integral`
(`OUGenerator:1057`), `ouGenerator_integral_sub_eq` (`:1073`) take any `Φ` with `TestFunH`; `TestFunH` (`:68`) quantifies over
Hermitian `M` only, so `A` Hermitian makes it translation-stable; `centeredVariance_wirtProduct_kernel_bound_Lt`
(`OUContraction:1077`) takes any Hermitian `H` and `lam`. `UNKind.ba.lamV = fun _ _ => 0` (`UNPins:84`); `ouP_ba_eq_band` is `rfl`.
No edit of `OUGenerator/OUHessian/OUContraction/EMCTE2` is needed. The 7 `open private` names exist as `private`:
```
EMCTE2.lean:221 EMCTE2_integrable_L1t_term  :233 EMCTE2_integrable_L2t_term  :245 EMCTE2_hsum (def)  :251 EMCTE2_integrable_hsum
:260 EMCTE2_hsum_nonneg  :289 EMCTE2_hsum_bdd  :411 EMCTE2_sum_integral_swap
```

## 4. Numerics rerun (section (a) (i)-(ii))
```
$ python3 -I ../pre.py | grep -E "^A\.|^   Jak:|^   Uyw:|^B\.|^   BA kappa|band (J|U) n=0|BA   J n=(0|1)|BA   U n=0|failing|C0=1|^D\."
A. exponents: c=2cd=1/30 c'=cd/30=1/1800 delta=1/28 K=2d+1=7 C=3nf+16=22 D_Jak=37/4 D_Uyw=21/2
   Jak: target exponent 1-c'+C tau=11699/1800 ; good-part slack (T-6tau minus exponent)=10807/18900 ; bad-part slack=1/14 ; crude: exponent a+2-D=-1 exactly (needs 12(3+m)<=X)
   Uyw: target exponent 2-c'+C tau=13499/1800 ; good-part slack=6757/18900 ; bad-part slack=5/14 ; crude exponent -1 (needs 16(4+m)<=X)
B. window: band kappa'=r=kappa/2 -> kappa_eff=min(k,2,2r)=k (kappa<=2): [(0.1, 0.1), (0.5, 0.5), (1.0, 1.0), (2.0, 2.0)]
   BA kappa'=kappa/2, r=(pi k)^3/8 -> [(0.01, 4e-06, 8e-06), (0.05, 0.000484, 0.000969), (0.1, 0.003876, 0.007752), (0.3, 0.104646, 0.209292)]
   band J n=0 L=4 W=32 N=2.097e+06 lam=0.01562 kf=0.5 const_h5=1.891e+05 X^(6tau)=3.037e+09 -> all numeric hypotheses True
   band U n=0 L=4 W=32 N=2.097e+06 lam=0.01562 kf=0.5 const_h5=2490 X^(6tau)=3.037e+09 -> all numeric hypotheses True
   BA   J n=0 L=4 W=32 N=2.097e+06 lam=0.3 kf=0.0077516 const_h5=7.044e+09 X^(6tau)=3.037e+09 -> all numeric hypotheses False
      failing: ['h5 const<=X^(6tau)']
   BA   J n=1 L=4 W=1024 N=6.872e+10 lam=0.3 kf=0.0077516 const_h5=7.044e+09 X^(6tau)=1.801e+16 -> all numeric hypotheses True
   BA   U n=0 L=4 W=32 N=2.097e+06 lam=0.3 kf=0.0077516 const_h5=8.521e+06 X^(6tau)=3.037e+09 -> all numeric hypotheses True
   C0=1 at n=0 band (h2 needs X>=2^180): False  ; 2^180 = 1.53e+54
D. grid-energy window band n=0: max|e-E|=0.126355 < kf/2=0.25 : True
D. grid-energy window BA n=1: max|e-E|=0.00194547 < kf/2=0.00387578 : True
$ python3 ../alg.py        # (-I fails: numpy is a user-site package)
(1) |blockM2_{w=delta_a0} - u_a0| identity: max deviation ... = 2.22e-16
    threshold equivalence mismatches (of 576 pairs, threshold W^(d-dd/6)/N, W=2, d=3): 0
(2) d^2/ds^2 Phi(A+M+sB) vs Phi_A: 0.0418246771721 vs 0.041824677173 (|diff|=8.67e-13) ; also Hermiticity of A+M preserved: True
```
Identical to (a) (ii). `h5` failing at BA n=0 is an eventual hypothesis (passes at n=1): not a degeneracy.

## 5. Deliverables (iii), (iv), (viii)-(x) rerun
```
$ python3 -I cone.py . RBM3D.Universality.{Jak,JakSpectral,Uyw,EMCTE2}   (worktree; +1 = RBM3D.Probe.T2476Pins)
Jak 6 [BUniv,BUnivHolds,BandTerminal,Probe,UnivMain,Uyw]  JakSpectral 9 [+JakKernel,UywKernel,Jak]  Uyw 5  EMCTE2 5
LWExpCert* in any cone: []   twin forward closure 104, LWExpCert: [], BandTerminal imported: False
BA.* modules in Jak/JakSpectral/Uyw forward closures: []   PinsK in forward closure of Jak/Uyw: False False
$ ticket awk signature dump on main and t/T2476
Jak: main 7 decls sha1 7b30439c; diff main..branch lines: 0      JakSpectral: 24, 40661814, 0
Uyw: 7, 9966be39, 0                                                EMCTE2: 8, 235795ae, 0
$ wc -l RBM3D/Universality/{Jak,JakSpectral,Uyw,EMCTE2}.lean  ->  1003 675 968 778
$ git grep -w <12 new names/stems> -- RBM3D RBM3D.lean (excl. probe)  ->  all 0
$ lake env lean RBM3D.lean   (exit 0)
axiom audit: 14065 theorems, 4452 definitions, 0 axioms in `RBM` ...  All within [propext, ...
premises found by scanning: 132 (borrowed 1, owed 66, structural 45, refuted 6, superseded 14).
registry: 2 borrowed + 109 owed + 122 structural + 7 refuted + 18 superseded; 126 registered premise(s) carry nothing yet
$ sed -n 177,188p RBM3D/Test/Axioms.lean -> UNEMCTE2k, UNJakk, UNUywk, UNEMCTE2Rowk, UNJakUywRowk (177-181), UNEMCTE2RowBA (187), UNJakUywRowBA (188)
```
Cones equal the ticket table (5/8/4/4) plus the probe. Counts, sha1s, scan numbers and registry lines equal the report.
Readers: `jakRow` in `Pins.lean:636,647,658` and `jakUywRow` in `BUnivHolds.lean:18` are comments only; report's reader list holds.
(viii) arithmetic: twin 360+195+36+25+145+30 = 791; total 30+30+791 = 851 < 1,950 (no pre-signed split); 2.6×: 1,081 / 1,046 / 2,057.

## 6. Fill-in table (H250 (4)) and stop lines
Rows (i) L18, (ii) L42, (iii) L62, (iv) L70, (v) L71, (vi) L79, (vii) L88, (viii) L96, (ix) L97, (x) L98 + (a″), D1 L99 + (a″):
every row filled; reruns equal (§2-§5); (v)-(vii) checked against the greps/signatures of §3; section (a) is 101 lines (≤ 120).
Stop rules: no public change in `Jak`/`JakSpectral`/`Uyw` (signature diff empty, K-forms in the leaf); no private deleted;
no K-form premise beyond the allowed list and no OU/EMCTE2 edit (§3); no edit outside the sole writable files and no `BA/*`
import in `Universality` (§5); no file past 2,000 at central (1,033 / 998 / 791); no `LWExpCert*` cone; central 851 ≤ 1,950;
axioms baseline standard three (§2). No binding stop line is hit; no sign-off question.

## 7. Observations (no verdict effect)
1. Reserve rule: (viii) plans to move targets 7-10 to `BA/JakUywBA.lean` when the twin reaches 1,500 lines. The ticket allows
   the reserve "only if the 1a predicts the twin above 1,800" (central here 791) and makes a twin past the stop line a stop
   (short REQ). 1b follows the ticket's rule, not a 1,500 trigger; the twin's 2.6× upper reference (2,057) now exceeds the
   ticket's TLC-4 twin figure (1,310) because the K-forms moved into the leaf under dispatcher answer (4).
2. (ii) BA numerics use stand-ins (κ = 0.1, g0 = 0.3; `S0`'s `κ_*`, `E_*` have no closed form); the BA bulk membership at
   the real data is compiled in the probe (`S0_bulk` + `BAbulk_window`, probe 262-265).
3. `alg.py` needs numpy from the user site (`python3 -I` fails); the report's command has no `-I`, so it is reproducible.
4. The probe `RBM3D/Probe/T2476Pins.lean` is on `t/T2476` and is not a sole writable file: it must not reach `main`
   (hub step (A) 2-3 brings only the sole writable files).
5. Ticket target 3 wording `λΨ + ouMat` vs merged subtract form (`UNPins:445`): equivalent; the additive form needs the
   `show` cast of probe 70-75 (prover finding (1), observation (3)).
6. Paper-delta candidates `T2476a`, `T2476b` (ticket) are for the 1b report (9); D1's bulk-window margin is already in `T2476b`.

## Verdict
1a design gate (section (a) + (a″) probe, D1): **PASS**. Every stage-1a deliverable (i)-(x) and the D1 row is met and
reproduced; no binding stop line is hit; no dispatcher sign-off needed. Stage 1b may start (order `Jak` → `Uyw` → `BA/EMCTE2BA`).
