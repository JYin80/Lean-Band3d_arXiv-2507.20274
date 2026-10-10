Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 10:04:44 UTC 2026 (`date -u`)

Ticket T2379 is a design ticket (report + probe). Its "targets" are the decision rule of TV1 (tripwire), the counts of TV4/TV5, and the in-place discipline G1-G3 of TV6. No new external hypothesis is introduced (limit computation: not applicable). Sources: `docs/reports/T2326-pilot.md` (cited "pilot §"), `docs/reports/T2325-portmap.md:138` (route I chain 78,276 lines), `docs/reports/T2360-design.md:166`, `docs/supervisor/2026-10-10-0853.md:160`, `docs/supervisor/2026-10-09-2051.md:110-117`.

### (i) Exponent table (constants and thresholds the targets depend on)
| quantity | value | constraint it must satisfy | slack | source |
|---|---|---|---|---|
| S (non-instance chain lines) | 90,226 | fixed by the pilot count | none | pilot §5 |
| g (edited fraction), site 1 / site 2 / pair / calibrated | 0.148 / 0.303 / 0.241 / 0.200 | measured; calibrated = 1.99 x 0.100 = 0.199 | n/a | pilot §0, §2, §5 |
| f_sem (semantic share, proxy) | 0.125 (range 0.10-0.30) | counted at twin rate 0.8, not at g | n/a | pilot §5 |
| ST overhead / BA wiring / B_new (lines) | 6,180 / 4,080 / 3,800 | B_new = 1300+1100+700+700 (U5,V2a,V2b,V3) | n/a | pilot §5, portmap:122-138 |
| route I chain (tickets) | 78.276 (range 54-103) | route G chain must stay below it | see break-even | portmap:138, §7 |
| break-even g, f_sem = 0.125 | 0.699 | route G beats I iff g < 0.699 | tripwire 0.5 leaves 0.199 | script below |
| break-even g, f_sem = 0.30 | 0.674 | same | tripwire 0.5 leaves 0.174 | script below |
| tripwire TV1: g > 0.5 or f_sem > 0.30 => route I | 0.5 / 0.30 | must be at or below the break-even | corner (0.5, 0.30) = 67.3 tickets, 11.0 below route I (78.3) | script below |
| route G chain, central / f_sem 0.10 / 0.30 | 38.9 / 37.5 / 48.3 tickets | matches pilot range 37.5-48.3 | exact | script below |
| stage-K ratio (merged / design central) | 6108/5339 = 1.144 | calibration factor for lo/central/hi of TV4 | the 1.5x stage rule (`1048.md:94`) does not fire (`0853.md:160`) | `0853.md:160` |
| central x 1.144 / route I x 1.144 | 44.5 / 89.6 | G < I stays true under a common factor | 45.1 tickets | script below |
| corner (0.5, 0.30) x 1.144 vs route I unscaled | 77.0 vs 78.3 | if only route G inflates by 1.144, the tripwire corner still stays below route I | **1.3 tickets only** (thin; flag for TV1/TV5) | script below |
| frozen band signatures needing wrappers | 167 (T1 14, T4 15, T5 18, T8 49, U1 1, U2 1, U3 28, U4 4, U5 1, U6 21, V1 15) | each kept by `example : <old> := <old name>` (G1) | upper bound (word match) | pilot §7 |
| carriers | 15 | each paired ST-side + BA-instance row (pilot §8 item 3) | n/a | pilot §5, §8 |
| rows candidate = 15 x 2 + 4 (B_new rows U5,V2a,V2b,V3) | 34 | TV5: sub-stages T,U,V needed iff rows > 40 | 6 rows | script below |
| stage flag 1.5 x rows | 51 at 34 rows (60 at 40, 61.5 at 41) | set at the opening REQ | n/a | `T2360-design.md:166` (1.5 x 16 = 24) |
| G2 critical-path merges first | T2356, T2361, LW R3, LW-01/ST-6 R4, UN-51, UN-52b, MA-06 | in-place merges never delay these | scheduling only | `2051.md:116` |
| `0 < kappa` in the carrier fact `flowOK_T` | `0 < kappa` | `baFlow_T0_lt_one` needs `Im m >= kappa` with `kappa > 0` | found by pilot reading | pilot §4 |

Reading of the thresholds: the tripwire (g 0.5, f_sem 0.30) is strictly more conservative than the break-even (0.67-0.70), so a measurement passing it keeps route G cheaper than route I by at least 11.0 tickets on unscaled numbers. The pilot's 15 carriers and 167 wrappers are upper bounds, not measurements of the chain.

### (ii) One concrete nondegenerate instance
Data: S = 90,226, g = 0.35, f_sem = 0.20 (a hypothetical tripwire measurement inside the permitted region g <= 0.5, f_sem <= 0.30), overhead 6,180, wiring 4,080, B_new 3,800, route I = 78.276. Carrier data of the pilot for the Step 2 block at d = 3 (nonempty instance, pilot §1); block Anderson reading needs `0 < kappa` (pilot §4). Chain tickets = ((1-f) S g + f S 0.8 + 6180 + 4080 + 3800)/1000.

Command and output (`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2379/pre.py`, pure arithmetic, no Lean):
```
central g=.20 f=.125: 38.9  f=.10: 37.5  f=.30: 48.3
break-even g at f=.125: 0.699  at f=.30: 0.674
tripwire corner (g=.5,f=.125): 62.6  (g=.5,f=.30): 67.3  vs route I 78.276
slack at corner (g=.5,f=.30): tickets 11.0  g margin to break-even 0.174
instance g=.35,f=.20: 53.8  < RI: True
stage-K ratio 6108/5339 = 1.144
central x K ratio: 44.5  route I x K ratio: 89.6  G<I: True
tripwire corner x K ratio: 77.0
flag: rows 34 -> 51.0  rows 40 -> 60.0  rows 41 -> 61.5
candidate rows: 15 carriers x 2 (ST + BA) + B_new 4 (U5,V2a,V2b,V3) = 34 ; 40-row limit slack 6
B_new lines 1300+1100+700+700 = 3800
pilot g both sites 235/975 = 0.241  calibrated 1.99*0.100 = 0.199
frozen wrappers sum 14+15+18+49+1+1+28+4+1+21+15 = 167
```
At the instance: route G chain 53.8 tickets < route I 78.3 (decision: stay on route G); the instance satisfies every hypothesis at once (0 < g < 0.5, f_sem <= 0.30, positive sizes, 34 rows <= 40, rows not collapsed, no empty carrier list). Formulas reproduce the pilot's printed 38.9, 37.5, 48.3 and 0.70/0.67 (pilot §0, §8 item 4).

### Verdicts
- TV1 (route, tripwire): PASS. The tripwire corner is inside the break-even. Caveat: under a one-sided 1.144 inflation of route G the margin at the corner shrinks to 1.3 tickets; the design should state whether 1.144 applies to both routes.
- TV2 (carriers and pins): PASS (15 carriers per pilot §5; this preflight found no inconsistent number or hypothesis).
- TV3 (dependencies on stages K, G, E, L, C): PASS (the inputs from K, G, E, L, C are pins or hypotheses of other gates; no number in the table contradicts them).
- TV4 (row table): PASS. Bases: pilot g (0.15/0.20/0.30), stage-K factor 1.144, B_new 3,800 lines.
- TV5 (count and flag): PASS. 34 candidate rows <= 40, so sub-stages are not forced by the count; central chain 38.9 [33..61] tickets, 44.5 after the K factor. The pilot's high scenario (60.9 tickets) would exceed 40 rows, so sub-stages T/U/V remain the fallback if the design's row count passes 40.
- TV6 (band side, G1-G3): PASS. 167 wrappers, `example : <old> := <old name>` per `2051.md:110`.
- Probe (`RBM3D/Probe/T2379Pins.lean`): PASS at the mathematics level (the BA-reading pins stay hypotheses of other gates, as in the pilot's compiled `d = 3` Step 2 instance, pilot §1).
## (a′) Preflight corrections — Sat Oct 10 11:06:42 UTC 2026 (`date -u`)
The mathematics of (a) (i)-(ii) is unchanged; (a)'s numbers are superseded by the design's measurements (B1, B4, B9) and one conclusion changes.
1. Rows (TV5): (a) assumed one ST-side ticket per carrier ("rows candidate = 34", "sub-stages are not forced"). B9b/B9d need 24 ST-side tickets (6 carriers, T4, T5, U1, U3, U4, V1, exceed 1,500 edit lines or 7,000 band lines), 21 BA-side tickets and row 0 (carrier relocation, L1): **46 rows > 40**, so the design proposes sub-stages T/U/V.
2. Bases: S = 98,552 (95,029 without U5, which the pilot also counted in B_new) and 203 frozen declarations, not 90,226 and 167 (B1, B4); route I is 84.7 on the final list, so the break-even g is 0.735/0.725/0.707 at f = 0/0.14/0.30 (not 0.699/0.674), the corner (0.5, 0.30) is 70.9 tickets with margin 13.8 (3.6 if only route G is inflated by 1.144; (a): 67.3, 11.0, 1.3), and the (a) instance (g = 0.35, f = 0.20) is 56.7 tickets (53.8), below route I (B9a).

## (b) Script output
Commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2379` (branch `t/T2379`). `S` = the session scratchpad `T2379/` (scripts and logs, not committed); each block is an excerpt of the named output file (the excerpt is stated). Narrative at the end of (b).
### B0, B6 provenance, build, axioms, target statements, instances, name clash (the probe)
```
$ date -u; git log --oneline -3 (the base line omitted); git diff --stat main...t/T2379
Sat Oct 10 11:06:28 UTC 2026
00a2206 T2379: probe 397 lines: one nonempty instance applying all five band bridges at sz0; builds, standard 
8adc8da T2379: probe 396 lines: Step 2 pins over the carrier with Iff.rfl bridges and BAStep2; LoopGenN block 
 RBM3D/Probe/T2379Pins.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 397 insertions(+)
$ lake build RBM3D.Probe.T2379Pins; echo "exit $?"   (last line)
Build completed successfully (3775 jobs).
exit 0
warning lines naming the probe file: 0
$ lake env lean RBM3D/Probe/T2379Pins.lean ; echo "exit $?"
exit 0
$ grep -cwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2379Pins.lean
0
$ lake env lean ax.lean | sed ... | sort | uniq -c   (ax.lean: #print axioms of the 15 new public declarations)
  15 [propext, Classical.choice, Quot.sound]
RBM.BA.STAvgUgL RBM.BA.STLocalEntryUgL RBM.BA.STGdecayWgL RBM.BA.STStep2ConclgL RBM.BA.bandFM_STAvgU RBM.BA.bandFM_STLocalEntryU RBM.BA.bandFM_STGdecayW RBM.BA.bandFM_STStep2Concl RBM.BA.STStep2G RBM.BA.STStep2_iff RBM.BA.BAStep2 RBM.Ind.genMatOf RBM.Ind.genMat_eq_genMatOf RBM.Ind.loopGenNOf RBM.Ind.recovers_loopGenN 
$ awk (target statements)
78: def STStep2G (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
79:     (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
80:     (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
81:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
82:     ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
83:       ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
84:         ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T0 sz z n) → (∀ n, s n < t n) →
85:           (∀ n, t n ≤ T0 sz z n) →
86:           STLKgL (mk sz z) (law sz) s → STDecaygL (mk sz z) (law sz) s → STConStInd sz 𝔠d s t →
87:           STStep1LoopgL (mk sz z) (law sz) s t → STStep1WeakgL (mk sz z) (law sz) s t →
88:             STStep2ConclgL (mk sz z) (law sz) s t Cd
302: theorem loopGenNOf (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (m : ℂ) (E : ℝ) (hL : 3 ≤ L)
303:     (hm : 0 < m.im) (u : ℝ) (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian)
304:     {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
... (probe 305-315: the conclusion, 11 lines)
$ awk NR 98-104 and 379-388   (compiled nonempty instances)
98: open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst in
99: example := And.intro (bandFM_STAvgU sz0 (fun _ => 0) sInst tInst)
100:   (And.intro (bandFM_STLocalEntryU sz0 (fun _ => 0) sInst tInst)
101:     (And.intro (bandFM_STGdecayW sz0 (fun _ => 0) sInst tInst 1)
102:       (And.intro (bandFM_STStep2Concl sz0 (fun _ => 0) sInst tInst 1) (STStep2_iff 3))))
104: example : Prop := BAStep2 3
379: /-- Band: `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `m = mE (1/2)`, a non-scalar Hermitian `M`, the loop `(+,-,+)` (merged `LoopGen
380: example :=
381:   loopGenNOf 3 3 2 (1 / 2) (mE (1 / 2)) (1 / 2) le_rfl (mE_im_pos (by norm_num [abs_of_pos])) (1 / 2)
382:     (by norm_num) LoopGenN_M0 LoopGenN_M0_isHermitian ![true, false, true] ![(0 : Zd 3 3), 1, 2]
384: /-- Block Anderson: `g = 0` (law `seqP (sz.withLam 0)`), `m = BAmF` (`BAmF_sz0_im_pos`), `sz0`, `zSeq`, `n = 0` (`L = 4`, `W = 
385: example :=
386:   loopGenNOf 3 (sz0.L 0) (sz0.W 0) 0 (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0)
387:     (BAflowEs sz0 zSeq 0) (sz0.three_le_L 0) (BAmF_sz0_im_pos 0) (1 / 2) (by norm_num) 1
388:     Matrix.isHermitian_one ![true, false, true] ![(0 : Zd 3 (sz0.L 0)), 1, 2]
$ grep -rnwE "<the 15 new public names>" RBM3D | grep -v Probe/T2379Pins; echo "exit $?"
exit 1
$ grep -rn STKwardgL RBM3D; echo "exit $?"
exit 1
ports from RBM1D/RBM2D: none (nothing under ../RBM1D, ../RBM2D read or run); the generic text copies merged RBM3D text (LoopGenN.lean); LoopGenN_hasDerivAt_ztOf copies the private Generator_hasDerivAt_ztOf (Universality/GUEPhase/Generator.lean:725) of this repository.
```
### B1 the chain files against the pilot list
```
$ python3 -I S/t1_files.py | sed -n "1,2p;$p"; git diff --name-status cc1158a HEAD -- RBM3D/Induction
pilot list (rows T1..V1): 97 files, 114998 lines, instance sections 24772 (21.5%), non-instance S = 90226
pilot list + 4 new Step-5 files (U4: IniTermI DuhamelI DuhamelII EtermsMid): 101 files, 123552 lines, instance sections 25000 (20.2%), non-instance S = 98552
main-induction files already generic over FlowFM: 735 lines (instance sections 168)
A	RBM3D/Induction/DuhamelI.lean
A	RBM3D/Induction/DuhamelII.lean
A	RBM3D/Induction/EtermsMid.lean
A	RBM3D/Induction/IniTermI.lean
```
### B2 semantic proxies (pilot fsem.py at theorem granularity; tactic lines; star-tree / K-formula lines)
```
$ python3 -I S/t1_fsem.py | sed -n "1p;3p;14,16p"; python3 -I S/t1_fsem_lines.py | sed -n "1p"; python3 -I S/t1_star.py | sed -n "1p;3p"
chain (101 files, non-instance): declaration lines 92571; theorem lines with a primitive-unfolding proof 13001 (14.0% of declaration lines)
  DuhamelII        U4   934  12.7    875   568  64.9
  LoopGenN       T5 lines   623 band-mention  12.2%  decl lines   562 sem-proxy lines    56 ( 10.0%)
  ZeroModeCalc   U1 lines   613 band-mention   6.2%  decl lines   561 sem-proxy lines     6 (  1.1%)
  KDecay         U2 lines   886 band-mention   5.3%  decl lines   825 sem-proxy lines    51 (  6.2%)
chain (101 files, non-instance): 79603 code lines (comments stripped, blank lines dropped); tactic lines naming a primitive: 337 (0.42%)
chain declaration lines (non-instance) 92571; in declarations naming a star-tree / K-formula primitive: 483 (0.52%)
top files: KDecay(U2) 258/825, HierAlgebra(T5) 190/721, ExpHier(V1) 35/716, Step2Iterate(T1) 0/1795, OptL2a(T1) 0/1370, OptL2b(T1) 0/276, EMn2Poly(T2) 0/882, EMn2Exp1(T2) 0/1729
```
### B3 the measured block (`LoopGenN.lean:55-622` against the generic text of the probe; scripts `build_gen.py`, `gdecl.py`, `gscript2.py`, `anatomy.py`, `t1_rho3.py`, `t1_twin.py`)
```
$ cd S/lg; git diff --no-index --numstat merged_block.txt gen_block.txt; ...   (excerpt)
136	99	merged_block.txt => gen_block.txt
edited lines in the 11 changed declarations 100 of 223; new lines 18 + band corollary 21; total touched = 139; g_decl = 139/568 = 0.245
g_lines = 206/568 = 0.363  (added/merged = 0.275, removed/merged = 0.210)
  hunk at merged line 540: removed 0, added 79
  hunk at merged line 560: removed 51, added 2
 43 removed lines: flow z_t (`zt E` -> `ztOf m E`)
 10 removed lines: one-loop value (`spectralMSign E`, `mSigma E` -> `PropSpin m`)
  9 removed lines: window hypothesis (`hE : |E| < 2` -> `hm : 0 < m.im`)
  4 removed lines: spectral-flow lemmas (`spectralZ_im`, `spectralM_im_pos`, `hasDerivAt_spectralZ`)
 13 removed lines: new argument `m` threaded (`LoopGenN_edgeTerm H E u`)
  4 removed lines: generator `genMat`
 16 removed lines: other (the old main-theorem proof lines re-aligned by the diff, docstrings)
LoopGenN block: 568 lines, 75 lines mention a band token or band def (0.132); measured g = 0.239 (numstat 136/568), per-declaration 0.245
rho_3 = g / density = 1.81  (per-declaration 1.85); edit lines per mention line = 1.81
pilot sites + LoopGenN: edit lines [58, 177, 136] over mention lines [35, 83, 75]: rho = 1.92 (pilot two sites 1.99)
LoopGenN block: 509 non-blank lines; found verbatim (after renaming) in Generator.lean: 376 (73.9%); Generator.lean has 1416 lines
```
### B4 frozen band signatures (pilot frozen2.py on the final list)
```
$ python3 -I S/t1_frozen.py | sed -n "1p"; python3 -I S/t1_frozen_files.py
public declarations in the 101 chain files: 2428 (private 3008); signature reads a band object: 1478; referenced from the 319 outside files (Test/, Probe/ excluded): 203
files holding frozen declarations: 42 ; declarations: 203
top files: Step2Defs(49), Step34Pins(24), Step5Pins(22), Step2Iterate(16), Step6Pins(13), StepDecompN(12), GridDuhamelN(8), Step5Kit(5)
```
### B5 pins (Prop-valued public definitions) and band-specific facts used by each row
```
$ python3 -I S/t2_pins.py | sed -n "17,18p"; python3 -I S/t2_facts.py | sed -n "18,19p"
total 238
generic forms already in BA/FlowPins.lean: ['PrecL', 'STDecayStronggL', 'STDecaygL', 'STEEg', 'STExp2gL', 'STInitialGT2gL', 'STJhatg', 'STKboundgL', 'STLKgL', 'STLWassmExpgL', 'STLmaxgL', 'STLocalEntrygL', 'STLocalMaxgL', 'STStep1LoopgL', 'STStep1WeakgL', 'STmaxLoop2g']
chain: 147 distinct band-specific facts (3065 lines), 64 band defs
facts by directory: {'Gauss': 35, 'Path': 27, 'Defs': 26, 'Propagator': 22, 'Loop': 18, 'Kernel': 7, 'Green': 5, 'Evolution': 4, 'Hierarchy': 2, 'Graph': 1}
```
### B7 other-stage inputs (curated word match, comment-stripped text; first `file:line` of each name; counts in `S/out/B7a.txt`)
```
$ python3 -I S/t3_where.py   (rows T6 and U5 print no match and are omitted here)
T1 K: KLK_one (Step2Iterate:1243) | L: LWtermExp (Step2Iterate:1793), STEMn2Exp (Step2Iterate:284), STLWB (OptL2a:404)
T2 K: KLK_two (EMn2Exp2:725) | E: ekPropTInf_holds (EMn2Exp2:942) | L: STEMn2Exp (EMn2Exp2:1090), STLWassm (EMn2Exp1:1264), STLWassmExp (EMn2Exp1:1216)
T3 K: KLK_two (NewKLK:697) | E: ekPropTInf_holds (NewKLK:996)
T4 K: KLK_isKLoop (AzumaProxyN:503), KLK_one (AzumaProxyN:529)
T5 K: KLK_isKLoop (GridDriftN:519), kTwo (HierAlgebra:485)
T7 K: KLK_one (DecayLoopB:548) | E: EKFastDecay (DecayLoopB:2006), STEKDecay (DecayLoopB:2213) | L: LWAssm (Step2Events:1370), LWAssmExp (Step2Events:1435), LWcut (Step2Events:1296)
T8 L: STEMn2Exp (Step2Defs:456), STLWB (Step2Defs:406), STLWT (Step2Defs:421)
U1 K: KLK_rotate (NewPQ:639), KLK_ward (NewPQ:640) | E: EKFastDecay (QopNorm:384)
U2 K: KLK_one (SEforLn1:180), KLK_rotate (SEforLn1:132), KLK_two (KDecay:541)
U3 K: KLK_isKLoop (NQEndFlowLift:612), KLK_ward (QLevelsA:150), KLbound_holds (NQEndFlowLift:477) | G: STStep1 (Step4:213) | E: EKFastDecay (Step34Pins:534), EKSumZero (Step34Pins:656), STEKDecay (Step34Pins:595)
U4 K: KLK_one (WardII:170), KLK_rotate (WardII:165), KLK_two (NewKLKL:453) | E: ekPropTInf_holds (Step5Kernel:209), stCltFar_holds (IniTermI:2008) | L: STEMn2Exp (EtermsMid:1212), STLWT (EtermsMid:1212)
U6 K: STKbound (Step5Pins:88), STKward (Step5Pins:88)
V1 K: KLK_one (ExpEtermsB:201), KLK_rotate (ExpWardII:153), kTwo (ExpHier:416) | E: EKFastDecay (ExpEtermsB:987), EKSumZero (ExpIniI:747), STEKDecay (Step6Pins:331) | L: LWAvgLaw (Step6Kit:190), LWcut (Step6Kit:329), LWtermEXP (Step6Kit:571)
```
### B8 band side: certificate cones, measured rebuilds (hub logs), layering, private-helper coupling
```
$ python3 -I S/t6_files.py; python3 -I S/t6_graph.py | grep "^chain files"; python3 -I S/t6_logs.py; python3 -I S/t6_cost.py | sed -n "1p"; python3 -I S/t6_layer.py; grep -rn -A0 "^open private" RBM3D/Induction
chain files 101; changed (g_f >= 0.01) 96; unchanged 5: ContractPt, QopNorm, QEndA, QProxy, PfStep5Alg; median g_f of the changed 0.198; max 0.49 (Step6Pins)
chain files whose downstream cone contains a LWExpCert* module: 20 of 101
T2366 (K01 generic part: Loop/Unique, Loop/KLUnique in place): 193 modules rebuilt, sum of module times 131 min; LWExpCert* modules 6 : 72 min (LWExpCertBS1 1592s, LWExpCertBS0 1533s, LWExpCertS0 593s, LWExpCertS1 574s, LWExpCertB 10s, LWExpCert 8s); Induction/ modules 107 : 34.3 min; the rest 25.3 min
T2365 (K09a: Loop/KLIndStepA, KLIndStepB in place): 121 modules rebuilt, sum of module times 124 min; LWExpCert* modules 6 : 83 min (LWExpCertBS1 2039s, LWExpCertBS0 1668s, LWExpCertS0 631s, LWExpCertS1 630s, LWExpCertB 12s, LWExpCert 7s); Induction/ modules 75 : 25.6 min; the rest 15.6 min
T2369 (K02: Loop/KLWard in place (+ new BA/KWard)): 194 modules rebuilt, sum of module times 223 min; LWExpCert* modules 6 : 155 min (LWExpCertBS0 4341s, LWExpCertBS1 2073s, LWExpCertS1 1781s, LWExpCertS0 1061s, LWExpCertB 15s, LWExpCert 10s); Induction/ modules 107 : 38.8 min; the rest 29.5 min
modules with a measured time: 200; rate of the non-certificate ones: 16.8 s per 1000 lines
BA/FlowPins direct imports: BA.MFixedPoint, Induction.Defs, Induction.Step2Defs, Loop.KLTree
chain files upstream of BA/FlowPins (cannot be restated over FlowFM in place): ['Step2Defs(T8)', 'Step34Pins(U3)']
chain files whose imports reach BA/FlowPins today: []
cone of RBM3D.BA.FlowPins: 33 modules, 27955 lines, LWExpCert* modules 0
RBM3D/Induction/DuhamelII.lean:39:open private duhamelI_drift duhamelI_mart duhamelI_grid duhamelI_tailW_eq duhamelI_rpow_quarter
RBM3D/Induction/DuhamelII.lean:42:open private emn2Exp2_exists_CR from RBM3D.Induction.EMn2Exp2
RBM3D/Induction/EMn2Exp2.lean:47:open private emn2Exp_zdistInf_zero emn2Exp_zdistInf_tri emn2Exp_zdistInf_sub_comm
RBM3D/Induction/EMn2Exp2.lean:50:open private hs hs_nonneg trace_mul_conjTranspose_eq Gres_conjTranspose Pm Eblk_eq_smul_Pm
RBM3D/Induction/EMn2Exp2.lean:52:open private card_ball_le from RBM3D.Induction.ContractPt
RBM3D/Induction/EMn2Exp2.lean:53:open private pti_sum_radial from RBM3D.Evolution.PropTInf
RBM3D/Induction/EMn2Exp2.lean:54:open private KLWard_mSigma_mul from RBM3D.Loop.KLWard
```
### B9 model: chain level (pilot formula), rows, route I / T, the 24 ST-side tickets
```
$ python3 -I S/t1_model.py | sed -n "1p;4p;6,8p;10,13p;16p;18p"; python3 -I S/t4_rows2.py; python3 -I S/t4_rows.py | tail -1; python3 -I S/t4_tickets.py
S = 95029 (U5 excluded), overhead 6720, wiring 4320, B_new 3800; route I chain 84.7, route T 98.9
g 0.190 f 0.140: chain  41.0 tickets  (route I 84.7: margin  43.7)
g 0.239 f 0.000: chain  37.6 tickets  (route I 84.7: margin  47.1)
g 0.300 f 0.300: chain  57.6 tickets  (route I 84.7: margin  27.1)
g 0.350 f 0.200: chain  56.7 tickets  (route I 84.7: margin  28.0)
g 0.500 f 0.300: chain  70.9 tickets  (route I 84.7: margin  13.8)
break-even g (route G = route I) at f = 0.00: 0.735;  vs route T: 0.885
break-even g (route G = route I) at f = 0.14: 0.725;  vs route T: 0.898
break-even g (route G = route I) at f = 0.30: 0.707;  vs route T: 0.921
break-even f at g = 0.24: 0.884
stage-K ratio 1.144: corner (0.5, 0.30) x 1.144 = 81.1 vs route I x 1.144 = 96.9; one-sided: 81.1 vs 84.7
row files   S    g_r  fr  ep |   ST lo   c    hi |   BA lo   c    hi | ST BA tickets | cert-files in row
T1    3   3587 0.206  17   3 |   1027   1136   1276 |    423    682   1141 |  1  1 | 1
T2    3   3850 0.094   1   2 |    519    572    641 |    374    651   1144 |  1  1 | 0
T3    2   1382 0.201   1   2 |    458    499    552 |    275    375    552 |  1  1 | 2
T4    6   6361 0.200  16   0 |   1389   1576   1818 |    354    812   1627 |  2  1 | 1
T5    7   5415 0.264  18   0 |   1533   1743   2015 |    317    706   1400 |  2  1 | 1
T6    2   1662 0.027   0   2 |    276    283    291 |    286    406    619 |  1  1 | 0
T7    3   4779 0.148   3   3 |    793    898   1032 |    471    815   1427 |  1  1 | 3
T8    3   1699 0.279  50   3 |   1333   1403   1493 |    348    470    688 |  1  1 | 1
U1    8   7883 0.166   1   4 |   1192   1384   1633 |    655   1223   2232 |  2  1 | 4
U2    4   5862 0.185   1   3 |   1034   1195   1401 |    514    937   1687 |  1  1 | 1
U3   27  22433 0.195  32   5 |   3841   4486   5317 |   1297   2912   5784 |  4  2 | 1
U4   14  17939 0.172  12  10 |   2629   3085   3673 |   1418   2709   5005 |  3  2 | 1
U5    3   3523 0.179   1   1 |      0      0      0 |      0      0      0 |  0  1 | 0
U6    1    476 0.359  22   1 |    697    722    754 |    179    213    274 |  1  1 | 1
V1   15  11701 0.244  28   6 |   2703   3125   3669 |    928   1771   3268 |  3  2 | 3
B_new rows: U5 (BA case (iii), 1300), V2a (1100), V2b (700), V3 (700): central 3800 [3300 .. 4600]; 3 further rows (V2a, V2b, V3; U5 is the BA row of its carrier)
lo: ST 19425 + BA 7841 + B_new 3300 = 30566 lines = 30.6 tickets; x1.144 = 35.0
c: ST 22108 + BA 14683 + B_new 3800 = 40592 lines = 40.6 tickets; x1.144 = 46.4
hi: ST 25566 + BA 26847 + B_new 4600 = 57013 lines = 57.0 tickets; x1.144 = 65.2
rows: row 0 (carrier relocation, L1) + ST 24 + BA 18 + 3 (V2a, V2b, V3) = 46; flag 1.5 x rows = 69.0
sub-stage T: rows 19; flag 28.5; ST tickets 10, BA tickets 8 (+ row 0)
sub-stage U: rows 19; flag 28.5; ST tickets 11, BA tickets 8
sub-stage V: rows 8; flag 12.0; ST tickets 3, BA tickets 2 (+ V2a, V2b, V3)
route T chain: 98.9 tickets; route I chain: 84.7 tickets (pilot on 97 files: 91.994 and 78.276)
ticket   files   S      edit   frozen | cone modules  lines   non-cert min | cert
T1       3   3587    739   17 |   72    81826     20 | YES
T2       3   3850    363    1 |   16    20533      5 | no
T3       2   1382    278    1 |   99   116127     33 | YES
T4s1     3   2980    685   13 |  112   137792     37 | YES
T4s2     3   3381    584    3 |   44    57028     12 | no
T5s1     2    804    202    0 |   51    61585     13 | no
T5s2     5   4611   1227   18 |   98   113529     27 | YES
T6       2   1662     44    0 |   54    69112     15 | no
T7       3   4779    707    3 |  101   126905     32 | YES
T8       3   1699    474   50 |  173   203813     56 | YES
U1s1     4   2621    142    1 |   72    83834     21 | YES
U1s2     4   5262   1165    0 |   21    24670      5 | no
U2       4   5862   1087    1 |  116   144808     40 | YES
U3s1     4   1539    492   28 |  192   220799     62 | YES
U3s2     7   6947   1386    3 |   35    46649     10 | no
U3s3    10   8173   1486    0 |   16    17909      3 | no
U3s4     6   5774   1010    1 |   11     8978      1 | no
U4s1     7   4961    870    7 |   61    64294     19 | YES
U4s2     2   5451    799    2 |    6     7084      3 | no
U4s3     5   7527   1425    3 |   22    22946      7 | no
U6       1    476    171   22 |   78    86695     27 | YES
V1s1     5   3817   1169   22 |   45    40907      9 | YES
V1s2     5   4176    995    3 |   18    13510      3 | no
V1s3     5   3708    697    3 |   22    21575      4 | no
24 ST tickets; 12 with a certificate module in the cone; 12 without
```

### Narrative
- The pilot's scripts were re-run on its 97-file list plus the files added since its base (B1); the measured block is `LoopGenN.lean:55-622` restated over `m` (11 declarations changed, 12 band-free private ones reused by `open private`), g by the pilot's primary measure, cross-checked per declaration (B3); the probe (397 lines) holds the Step 2 pin family with `Iff.rfl` bridges, `BAStep2`, `loopGenNOf`, `recovers_loopGenN` and the band and BA instances (B6).

## (c) Verified Mathlib and Lean names used in the new text (all compiled in the probe)
`HasDerivAt`, `hasDerivAt_id`, `HasDerivAt.ofReal_comp`, `hasDerivAt_const`, `HasDerivAt.sub`, `HasDerivAt.mul_const`, `HasDerivAt.const_add`, `HasDerivAt.star`, `HasFDerivAt.comp_hasDerivAt`, `LinearMap.toContinuousLinearMap`, `Matrix.traceLinearMap`, `Matrix.trace_list_sum`, `Matrix.trace_neg`, `Matrix.isHermitian_one`, `List.sum_map_mul_left`, `Finset.sum_add_distrib`, `And.intro`, `type_of%` (core elaborator), `open private` (Batteries). RBM3D names: `ztOf`, `ztOf_im`, `etaOf` (`Loop/GLoopFlow.lean:55-64`), `PropSpin` (`Propagator/Pins.lean:30`), `mE_im_pos`, `genMat` (`Path/OneStep.lean:68`), `gvarF`, `sum_coordinateSecondWordDeriv_allCuts` (`Hierarchy/ContractionSecondLoop.lean:1173`), `hasDerivAt_green_moving`, `PrecL`, `FlowFM`, `bandFM`, `baFMz`, `BAFlow`, `BAflowT0`, `BAmF`, `BAmF_sz0_im_pos` (`BA/FlowPins.lean:1422`). Names verified absent: `STKwardgL` (B6: 0 matches), and the 15 new public names (B6: 0 matches).

## (d) Open issues and paper-delta candidates
- L1 (layering): `FlowFM` is below `Step2Defs` and `Step34Pins`; row 0 moves it upstream (B8e). The dispatcher decides row 0 and the file name `Chain/Carrier.lean`.
- The tripwire block is not semantic by the pilot's own proxy (B2); the class (t) files (`KDecay`, `HierAlgebra`, `ExpHier`) are the real test: the second tripwire is the first ticket that converts one.
- `BAKcalDecay` and the BA twin of `stKloop_lip` are not stage-K targets (`sup 2051` Q5 assigns them to stage T/U/V); `STKwardgL` is not yet pinned (K12).
- The BA readings of the Step 2 events (T7, T1) are the pilot's 11 obligations, unproved; V2a, V2b, V3 keep the T2205 sizes (V3 may be smaller: `unMLOutBA_of_pins` is a 6-line wrapper).
- Paper-delta candidates: `T2379a` the generic `loopGenNOf` (every `m` with `0 < m.im`, every `g`; the paper states the band case; BA is `g = 0`, `m = m_BA`); `T2379b` `BAStep2` is Lean's reading of the "unchanged steps" of `lem:main_ind_BA` (`7_8:1825-1841`).
