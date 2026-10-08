Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 04:54:14 UTC 2026

T2325 is a report-only design probe (BA-DP2). It has no analytic hypothesis: its targets are the tables of (i) graph layer, (ii) chain, and the BA re-portmap with one cap number. The quantities the targets depend on are the budget constants and row counts below, all taken from the files.

### (i) Exponent table (constants, thresholds, counts the re-portmap depends on)

| quantity | value | constraint | slack / note | source |
|---|---|---|---|---|
| BA cap (rows/tickets) | 72 | final recommendation = one number, to be compared with the projection | projection 80-85 (range 76-95), gap 8..13 over cap | supervisor 0344 Q1, DECISIONS §128 |
| BA tickets merged so far | 25 | "25 reached" | plan 71 | supervisor 0344 gate table |
| portmap rows (T2161) | 57 | rows listed at T2161-portmap.md:995-1051+ | script below: 57 parsed | portmap |
| portmap rows already merged (rows of the table) | 13 (D1,D2,D3,D4,D6,D7,P1,G1,S1,S2,S3,L1,L2) | remaining = 57 - 13 | remaining = 44, NOT the ticket's "46" (C1,C2,D8 merged but not table rows) | script |
| remaining rows by class | P7 K5 E3 G5 T8 U6 V3 L2 M3 N2 | sum = 44 | - | script |
| remaining portmap lo/central/hi | 37060 / 51890 / 74250 lines | baseline for the revised lo/central/hi | - | script |
| class ratio, deterministic | 0.55 (3.9k/7.3k over 7 merged files) | applies to D,P,K,E,G rows | portmap central of remaining D/P/K/E/G rows (script): 12430 after x0.55 | supervisor Q1 table |
| class ratio, stochastic chain | 2.7 (8.6k/3.2k, S1-S3 incl. one-time event re-pin); supervisor suggests 1.3-1.5 for T,U,V | ratio for T/U/V rows chosen in (ii), must lie in [1.3, 2.7] | T+U+V central = 10900+6800+3200 = 20900; at 1.3/1.5/2.7 = 27170/31350/56430 | supervisor Q1; script |
| class ratio, graph | 1.3 (4.2k/3.3k, L1+L2) | applies only to un-twinned residual | - | supervisor Q1 |
| BA-L3 twin source size | LWLvl1.lean 4462 lines vs portmap central 1590 | twin cost lower bound = merged twin size x alpha | supervisor: L3 +2 rows, lweight op +1 | wc -l |
| BA-L4 twin source size | LWExp* chain ~10k lines (LWExpTerm..5, LWExpCert*, LWExpSim, Sound) vs central 1500 | instantiate: +1..+2 rows, twin: +4..+6 | supervisor Q1 | supervisor |
| merge candidates | (a) G2-G6 -> 4 rows (-1), (b) E1+E3 (-1), (c) P7+P8 (-1), (d) N1 dropped (-1), (e) K5 dropped (-1) | total -1..-4 per supervisor; each needs a check against merged code | - | supervisor Q1 |
| ord(Gamma) | n_S + 2(n_W - n_A) (eq:ordG_BA); size = (L^d)^{n_M} Psi_t^{n_S} W^{-d(n_W-n_A)} | the model objects read by lvl1/LWterm are exactly (n_S,n_W,n_A,n_M), Psi_t, W^d | merged as BAGraph.scalingOrder := RBM.Graph.ord counters (BAVocab.lean:145-148, 203) | B:345-356 |
| expandG / ExpandGSum / lwExpandIdentity_holds | signatures at LWExpTerm5.lean:189, :199, :594; expandG takes an abstract step function st : X -> Option (List ((N x N) x X)) | genericity of the engine in the state X is already in the signature (a preliminary lead for (i), to be confirmed in the report by reading the declarations) | - | grep below |

### (ii) One concrete nondegenerate instance

The targets are tables, so the instance is a numeric re-portmap check at the actual data (44 remaining rows, nonzero lines, non-empty classes) plus a worked scaling-order value. Script: scratchpad T2325/inst.py (python, no Lean; parses T2161-portmap.md:995-1062, reads `git log` of RBM3D/BA and Graph/BA*, sums classes, prints ord for n_S=5, n_W=2, n_A=1).

Command and output:

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2325/inst.py
rows parsed 57
merged row names in log: ['BA-C1', 'BA-C2', 'BA-D1', 'BA-D2', 'BA-D3', 'BA-D4', 'BA-D6', 'BA-D7', 'BA-D8', 'BA-G1', 'BA-L1', 'BA-L2', 'BA-P1', 'BA-S1', 'BA-S2', 'BA-S3']
remaining 44 ['BA-E1', 'BA-E2', 'BA-E3', 'BA-G2', 'BA-G3', 'BA-G4', 'BA-G5', 'BA-G6', 'BA-K1', 'BA-K2', 'BA-K3', 'BA-K4', 'BA-K5', 'BA-L3', 'BA-L4', 'BA-M1', 'BA-M2', 'BA-M3', 'BA-N1', 'BA-N2', 'BA-P2', 'BA-P3', 'BA-P4', 'BA-P5', 'BA-P6', 'BA-P7', 'BA-P8', 'BA-T1', 'BA-T2', 'BA-T3', 'BA-T4', 'BA-T5', 'BA-T6', 'BA-T7', 'BA-T8', 'BA-U1', 'BA-U2', 'BA-U3', 'BA-U4', 'BA-U5', 'BA-U6', 'BA-V1', 'BA-V2', 'BA-V3']
{'P': [7, 5000, 6900, 9800], 'K': [5, 4600, 6100, 8400], 'E': [3, 2200, 3200, 4500], 'G': [5, 4600, 6400, 9100], 'T': [8, 7800, 10900, 15400], 'U': [6, 4600, 6800, 9800], 'V': [3, 2200, 3200, 4700], 'L': [2, 2560, 3090, 4150], 'M': [3, 2300, 3300, 4900], 'N': [2, 1200, 2000, 3500]}
remaining portmap lo/c/hi 37060 51890 74250
central x0.55 on deterministic classes DPKEG: 12430.0
ticket claim: 46 rows; remaining+merged = 44 + 16
ord= 7
cap 72; merged BA tickets 25; projection 80-85 -> gap 8 13
```

Arithmetic at this instance (all from the output above): remaining rows 44, every class P,K,E,G,T,U,V,L,M,N nonempty; remaining central 51890 lines; ord(n_S=5,n_W=2,n_A=1) = 5 + 2(2-1) = 7 (formula B:353, instance values are illustrative, not a paper graph).

Closed-form consistency of the cap target: projection 80-85 versus cap 72 gives a gap of 8 to 13 rows; the cap number must be a single integer in the final report, chosen between the "instantiate where possible" and "twin everything" totals.

Hypothesis check for the ticket's external statements (no external hypothesis is used by this design probe; limit computation not applicable).

Observations for the prover (no verdict impact): (1) the ticket says "46 rows"; the table at T2161-portmap.md:995-1062 has 57 rows, of which 13 are merged, leaving 44 (script); (2) the supervisor's graph row "Ord ~850" has no separate file under RBM3D/Graph/ (ls: BAExpand, BAExpandW, BAVocab only; line counts BAVocab (1424), BAExpand (904), BAExpandW (1066) lines via wc -l), ord is at BAVocab.lean:145-148.

### Verdict

- Target (i) graph-layer table: PASS (all inputs exist; check file compiled with exit 0 per CONTROL).
- Target (ii) chain table: PASS.
- Target re-portmap and cap: PASS (inputs: T2161 portmap, supervisor 0344 ratios, merged git log; no missing input).

## (a′) Preflight corrections — Thu Oct  8 07:30:02 UTC 2026

- The row accounting of (a) is off by two rows: `inst.py` finds merged rows by the regex `BA-X<n>` in commit messages, so BA-P2 (T2317, message "merge BA/KKernel") was counted as remaining, and BA-L2 as merged although the `lem_lweight` graph operation and `BAGGGamma` (BA-L2c) are open (T2315 ticket "Not targets", `BAExpandW.lean` docstring). Corrected (B2): 13 table rows merged (D1 D2 D3 D4 D6 D7 P1 P2 G1 S1 S2 S3 L1), BA-P3 in flight (T2324), 42 table rows not released, plus the open part of L2 = 43, plus BA-C3..C5 (`T2173-prove.md:234-236`) = 46 = the ticket's count; the "44" of (a) is wrong.
- The chain ratio 2.7 of (a) is 8618/3200 with `FlowPins` and `CouplingWindow`; the S1-S3 files alone are 6115/3200 = 1.91 (B2). No verdict of (a) changes.

## (b) Script output and design evidence (stage 1b) — Thu Oct  8 07:30:02 UTC 2026

Scope: report-only design ticket (CONTROL H124). Written: `docs/reports/T2325-portmap.md` (main worktree), this report, and the probe `RBM3D/Probe/T2325BAGen.lean` (branch `t/T2325`, commit 05b9293, 213 lines, never merged). No other file of the worktree changed. `S` below is the session scratchpad `T2325/` (scripts `acct.py decl_inv.py decls.py privshare.py steps.py direct.py similar.py reuse.py iface.py matlevel.py cone.py chain.py reportcalc.py`).

### B1 the probe: build, axioms, hygiene, statements, name clashes
```
$ date -u; cd RBM3D-wt/T2325; git --no-optional-locks log --oneline -2; git --no-optional-locks diff --stat main...t/T2325
Thu Oct  8 07:23:20 UTC 2026
05b9293 T2325: probe on model-generic instantiation of the graph layer (BA-DP2)
044707b T2315: merge BA-L2b2 Graph/BAExpandWOrd
 RBM3D/Probe/T2325BAGen.lean | 213 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 213 insertions(+)
$ lake build RBM3D.Probe.T2325BAGen 2>&1 | grep 'T2325BAGen\|Build completed'
Build completed successfully (3906 jobs).
$ lake env lean RBM3D/Probe/T2325BAGen.lean; echo "exit $?"
exit 0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Probe/T2325BAGen.lean
0
$ grep -rnw --include='*.lean' -e baEngine_sum -e baGraph_size_le -e inst_size_le -e BALvl1Good -e BAMu -e ba_mu_lt -e baMu_wf -e scalarM_hyp_fails_at_baD -e 'RBM.Probe.T2325' RBM3D | grep -v '^RBM3D/Probe/T2325BAGen.lean' | wc -l
       0
$ lake env lean $S/ProbeAx.lean   # the probe file plus seven #print axioms lines
'RBM.Probe.T2325.baEngine_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.baGraph_size_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.inst_size_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.BALvl1Good_ofLGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.ba_mu_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Probe.T2325.baMu_wf' does not depend on any axioms
'RBM.Probe.T2325.scalarM_hyp_fails_at_baD' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "^theorem\|^def\|^example" RBM3D/Probe/T2325BAGen.lean | cut -c1-110
51:theorem baEngine_sum (st : BAPGraph (Fin 2) → Option (List ((ℕ × ℕ) × BAPGraph (Fin 2))))
59:example (P : BAPGraph (Fin 2)) (n : ℕ) :
73:theorem baGraph_size_le (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (Γ : BAGraph E₁ I₁) (Δ : BAGraph E₂ I₂)
87:theorem inst_size_le :
139:def BALvl1Good (Γ : BAGraph E₁ I₁) (Q : BAGraph E₂ I₂) : Prop :=
147:theorem BALvl1Good_ofLGraph (Γ : LGraph E₁ I₁) (Q : LGraph E₂ I₂) (hΓ : ∀ e ∈ Γ.dotted, e.eq = false)
168:def BAMu {E : Type} (K : ℤ) (P : BAPGraph E) : ℕ × ℕ × ℕ × ℕ :=
173:theorem ba_mu_lt {E : Type} {K : ℤ} {Γ Q : BAPGraph E} (hK : Γ.scalingOrder < K)
195:theorem baMu_wf : WellFounded Lvl1Lt := lvl1Lt_wf
202:theorem scalarM_hyp_fails_at_baD (m : ℂ) :
$ sed -n '73,78p;87,88p;202,203p' RBM3D/Probe/T2325BAGen.lean   # the statements of baGraph_size_le, inst_size_le, scalarM_hyp_fails_at_baD
theorem baGraph_size_le (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (Γ : BAGraph E₁ I₁) (Δ : BAGraph E₂ I₂)
    (W L : ℕ) (Ψ : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) (hLW : (L : ℝ) ^ d ≤ (W : ℝ) ^ K0)
    (hlow : (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) (hup : Ψ ≤ (W : ℝ) ^ (-c))
    (hK : (lvl1Cutoff c K0 d D Γ.counters : ℤ) ≤ Δ.scalingOrder) (hM : Δ.nM ≤ Γ.nM)
    (hV : (Δ.nA : ℤ) - Δ.nW ≤ (Γ.nA : ℤ) - Γ.nW) :
    Δ.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D) :=
theorem inst_size_le :
    (BAGraph.ofLGraph figGraph).scalingSize (1 / 4) 4 3 1 ≤ (4 : ℝ) ^ (-(-2 : ℝ)) := by
theorem scalarM_hyp_fails_at_baD (m : ℂ) :
    ¬ ∀ x y : Fin 2, BAVocabInst.baD.toLData.M x y = if x = y then m else 0 := by
```
Instance: `inst_size_le` applies `baGraph_size_le` at `d = 3`, `W = 4`, `L = 1`, `Ψ = 1/4`, `c = 1`, `K0 = 0`, `D = -2` to the BA readings of the merged `p2Graph` (`n_S = 6, n_W = 2, n_A = 4, n_M = 2`) and `figGraph` (`8, 4, 6, 2`, `ord = 4`): cutoff `⌈(-2 + 0 + 3·2)/1⌉ = 4 ≤ ord`, window `W^{-3/2} = 1/8 ≤ Ψ ≤ W^{-1} = 1/4`; no hypothesis is left open. `baEngine_sum` is applied at the carrier `BAPGraph (Fin 2)`; the `example` at line 59 evaluates `expandG` of the empty step by `rfl`.

### B2 rows, merged files, class ratios (T2161-portmap.md:995-1062, `wc -l`)
```
$ python3 -I $S/acct.py | sed -n '1p;3,32p;34p'
portmap rows parsed from T2161-portmap.md:995-1062: 57
row     role      lo central     hi |  actual  ratio
BA-D1   p       1000   1300   1600 |    2578   1.98  BA/MFixedPoint.lean + BA/FlowPins.lean
BA-D2   hard     700    900   1200 |       0   0.00  
BA-D3   p        650    950   1400 |     427   0.45  BA/Ward.lean
BA-D4   hard     700   1000   1400 |     674   0.67  BA/CombesThomas.lean
BA-D6   hard     800   1200   1800 |     349   0.29  BA/Boundary.lean
BA-D7   max      800   1300   2200 |     479   0.37  BA/ImmLower.lean
BA-P1   hard     500    700   1000 |     814   1.16  BA/Prop5Short.lean
BA-P2   p        500    700   1000 |     528   0.75  BA/KKernel.lean
BA-G1   max     1000   1400   2000 |     615   0.44  BA/GreenSchur.lean
BA-S1   hard     800   1100   1500 |    1982   1.80  BA/ConArg.lean
BA-S2   hard     800   1100   1600 |    3105   2.82  BA/Step1Trivial.lean + BA/Step1Boot.lean + BA/Step1Setup.lean + BA/Step1.lean
BA-S3   p        700   1000   1500 |    1028   1.03  BA/Step1Fam.lean
BA-L1   p        873    873   1746 |    1424   1.63  Graph/BAVocab.lean
BA-L2   hard    2400   2400   2400 |    2975   1.24  PARTIAL (L2c GGGamma and lem_lweight graph op open): Graph/BAExpand.lean + Graph/BAExpandW.lean + Graph/BAExpandWOrd.lean
BA-C1   (not a T2161 row; T2173/T2205) actual 1312 : BA/UNPins.lean
BA-C2   (not a T2161 row; T2173/T2205) actual 384 : BA/MReg.lean
BA-D8   (not a T2161 row; T2173/T2205) actual 921 : BA/CouplingWindow.lean
in flight: BA-P3 = T2324 (BA/KSymbol, portmap row BA-P3)

class ratios (actual lines / portmap central):
  new-math deterministic (D3 D6 D7 G1 P2)           2398 /  5550 = 0.43
  twin deterministic (D4 P1)                        1488 /  1700 = 0.88
  supervisor 0344 Q1 set (D3 D4 D6 D7 G1 P1 P2)     3886 /  7250 = 0.54
  stochastic chain S1 S2 S3 files only              6115 /  3200 = 1.91
  graph L1                                          1424 /   873 = 1.63
  graph L2 (three of four cuts merged)              2975 /  2400 = 1.24
  D1+D2                                             2578 /  2200 = 1.17   (D1 + D2: MFixedPoint + FlowPins)
  S1-S3 + FlowPins + CouplingWindow                 8618 /  3200 = 2.69   (supervisor: 8.6k / 3.2k)
  BA files total 19595 lines in 22 merged code tickets (git log: 21 commits touching RBM3D/BA, RBM3D/Graph/BA* plus T2315) = 891 lines per ticket
remaining portmap rows not yet released (excl. BA-P3 in flight): 42
```
### B3 twin ratio, copy tax, reuse by reference (BA S-chain against ST-1; BA graph L2 against LW)
```
$ python3 -I $S/direct.py
ST-1 Induction files (10): lines 9050, direct-mention 2692 (30%), private 2348
ST-1 twinned-topic files (6): lines 5856, direct-mention 2253 (38%)
BA S-chain twin files own lines (ConArg, Step1Boot, Step1Setup, Step1) = 4879 ; ratio to direct-mention of the 6 = 2.17 ; to direct-mention of the 10 = 1.81
$ python3 -I $S/similar.py
BA S-chain twin files vs ST-1 Induction files: BA declaration-lines (decls >= 8 lines) 4113 ; with a >=0.70-similar ST declaration: 1079 (26%) ; 0.50-0.70: 1287 (31%)
BA graph L2 files vs LWStein/LWWeightExp/LWVocab/LWSymm: BA declaration-lines (decls >= 8 lines) 2264 ; with a >=0.70-similar ST declaration: 337 (15%) ; 0.50-0.70: 428 (19%)
BA P1/D4/P2 vs Propagator (control): BA declaration-lines (decls >= 8 lines) 1307 ; with a >=0.70-similar ST declaration: 0 (0%) ; 0.50-0.70: 0 (0%)
BA S-chain twin files: BA decl-lines 4113; near-copy (sim>=0.5) lines by (ST source visibility, ST source mentions a band token): {('public', 'band'): 873, ('private', 'band-free'): 756, ('private', 'band'): 651, ('public', 'band-free'): 86}
$ python3 -I $S/reuse.py | grep -v '^  '
BA S-chain (S1,S2,S3): own lines 5434; distinct public declarations referenced from Induction/: 99 (their total length 1235 lines)
BA C1a/D8/C1b: own lines 3292; distinct public declarations referenced from Induction/: 37 (their total length 247 lines)
BA graph L1,L2 (vs Graph/): own lines 3696; distinct public declarations referenced from Graph/: 99 (their total length 885 lines)
BA deterministic rows (vs other gates): own lines 3062; distinct public declarations referenced from Propagator/,Green/,Universality/,Loop/,Kernel/,Evolution/: 41 (their total length 302 lines)
```
### B4 volume now against the T2161 base (`T2161-portmap.md:195-222`: `Induction/` 57206 decl-lines, ST-3 18712), private share, model-base interface
```
$ python3 -I $S/steps.py | sed -n '1,8p'
step (files under Induction/)      files decl-lines   private    sig-hw   body-hw
ST-1 Induction (Step 1)               10      9050      2348       974      1718
ST-2 Induction (Step 2)               28     27939     12060      8006      4328
ST-3 Induction (Steps 3-4)            43     49672     26863     11921     10479
ST-4 Induction (Step 5)               14     14020      6771      4128      2282
ST-5 Induction (Step 6)               15     12279      3872      4704      1040
ST-6 Induction (main induction)        2      1382       167        48       136
sum                                         114342     52081     29781     19983
$ python3 -I $S/privshare.py
dir            decl-lines   private  priv%
Induction        114342     52081    46%
Path              26200     16135    62%
Evolution         16563      9871    60%
Propagator         8107      4604    57%
Universality      37584     18265    49%
Loop              16179      6930    43%
Green             24280      5985    25%
Graph             48752     10169    21%
BA                12870      3478    27%
$ python3 -I $S/iface.py | sed 's/ | by dir.*//'
Step 2     files 28 lines  31828 | distinct model-base declarations referenced:  210 (their total length   1961 lines)
Steps 3-4  files 43 lines  56133 | distinct model-base declarations referenced:  195 (their total length   2036 lines)
Step 5     files 14 lines  16006 | distinct model-base declarations referenced:  146 (their total length   1263 lines)
Step 6     files 15 lines  13944 | distinct model-base declarations referenced:  162 (their total length   1886 lines)
$ python3 -I $S/matlevel.py | sed -n '1,6p'
step       decl-lines matrix-level  share
Step 2         27939         4515    16%
Steps 3-4      49672         4570     9%
Step 5         14020          961     7%
Step 6         12279          310     3%
Steps 2-6     103910        10356    10%
```
### B5 declaration cones of the endpoint theorems (name resolution: same file first, then a unique public declaration)
```
$ python3 -I $S/cone.py | sed -n '1,8p;32,41p'
endpoint(s)                                    decls |  ST lines   private | cone lines by dir (Induction / Path / Evolution / Loop / Green / Gauss / Defs / Graph)
Step 2: ST_step2_of_pins                        1468 |      4961       206 | 4961 / 542 / 52 / 248 / 4139 / 840 / 1357 / 2899
Step 3: stStep3RegIII/RegI/II_holds             4777 |     43295     26909 | 43295 / 3802 / 2467 / 12457 / 4257 / 1688 / 2119 / 2926
Step 4: stStep4I/II_holds                       4661 |     40859     26000 | 40859 / 3802 / 2467 / 12443 / 4257 / 1688 / 2119 / 2926
Step 5: stStep5III/IV, caseI/II                 4743 |     15838      8535 | 15838 / 14178 / 848 / 11537 / 17086 / 1673 / 2028 / 2998
Step 6: stStep6IV, caseI-III from pins          3317 |     14337      6287 | 14337 / 122 / 2828 / 11559 / 4158 / 3326 / 2088 / 2930
Main: ST_mainInd_of_pins'                       6942 |     57720     32910 | 57720 / 14327 / 2512 / 12703 / 17538 / 3834 / 2194 / 3006
union of the cones: Induction lines 67894 of 114342 (59%); all dirs 138174 lines
Induction decl-lines by (in the union cone of the endpoints | outside it, visibility, band-token mention):
   ('cone', 'private', 'band')                                    16325
   ('cone', 'private', 'band-free')                               18635
   ('cone', 'public', 'band')                                     18985
   ('cone', 'public', 'band-free')                                13949
   ('pins-proofs-etc', 'private', 'band')                          6006
   ('pins-proofs-etc', 'private', 'band-free')                    11115
   ('pins-proofs-etc', 'public', 'band')                          13923
   ('pins-proofs-etc', 'public', 'band-free')                      9722
   total 108660 ; band-mentioning 55239 (51%) ; private & band-free 29750 (27%)
```
### B6 the re-portmap computation (chain per row, group A summary, graph rows, totals); route T = 0.80 x file lines, route I = 1.45 x D
```
$ python3 -I $S/reportcalc.py | grep -v '^BA-[CEGKMNP][0-9]' | grep -v '^$'   # the 26 group A rows are in the portmap, section 5
CHAIN ROWS (ST source files of Steps 2-6; file lines, direct-mention lines D; route T = 0.80 x file lines, route I = 1.45 x D)
row     files src.lines       D  portc |    T.lo     T.c    T.hi |    I.lo     I.c    I.hi | tkTl tkTc tkTh | tkIc ratioT
BA-T1       3     3947    2565   1500 |    2368    3158    3947 |    2565    3719    4874 |    3    4    4 |    4  2.1
BA-T2       3     4445    1332   1700 |    2667    3556    4445 |    1332    1931    2531 |    3    4    5 |    2  2.1
BA-T3       2     1552     935   1200 |     931    1242    1552 |     935    1356    1776 |    1    2    2 |    2  1.0
BA-T4       6     8530    4338   1400 |    5118    6824    8530 |    4338    6290    8242 |    6    7    9 |    7  4.9
BA-T5       7     6171    2983   1400 |    3703    4937    6171 |    2983    4325    5668 |    4    5    7 |    5  3.5
BA-T6       2     1781     117   1400 |    1069    1425    1781 |     117     170     222 |    2    2    2 |    1  1.0
BA-T7       3     5756    2288   1200 |    3454    4605    5756 |    2288    3318    4347 |    4    5    6 |    4  3.8
BA-T8       3     2128    1294   1100 |    1277    1702    2128 |    1294    1876    2459 |    2    2    3 |    2  1.5
BA-U1       8     8886    2871   1200 |    5332    7109    8886 |    2871    4163    5455 |    6    8    9 |    5  5.9
BA-U2       4     6705    3175   1200 |    4023    5364    6705 |    3175    4604    6032 |    5    6    7 |    5  4.5
BA-U3      27    35050   17469   1000 |   21030   28040   35050 |   17469   25330   33191 |   22   29   36 |   26 28.0
BA-U4      10    10304    4663   1200 |    6182    8243   10304 |    4663    6761    8860 |    7    9   11 |    7  6.9
BA-U5       3     4658    2257   1300 |     900    1300    1900 |     900    1300    1900 |    1    2    2 |    2  1.0
BA-U6       1     1044     243    900 |     626     835    1044 |     243     352     462 |    1    1    2 |    1  0.9
BA-V1      15    13944    7090   1000 |    8366   11155   13944 |    7090   10280   13471 |    9   12   14 |   11 11.2
BA-V2a      -        -       -   1100 |     800    1100    1600 |     800    1100    1600 |    1    2    2 |    2
BA-V2b      -        -       -    700 |     500     700    1000 |     500     700    1000 |    1    1    1 |    1
BA-V3       -        -       -    700 |     500     700    1000 |     500     700    1000 |    1    1    1 |    1
chain total lines: route T [68846, 91994, 115743] | route I [54063, 78276, 103090] ; tickets (per-row ceil): T [79, 102, 123] | I [63, 88, 111] ; portmap T+U+V central 20900 (17 rows)
GROUP A (deterministic and twin-type rows; ratio to portmap lines: new 0.35/0.55/0.90, twin 0.70/1.00/1.30; tickets = ceil(lines/1500) per row)
row     type       portmap lo/c/hi |      revised lo/c/hi | tkl tkc tkh
group A rows: 26 ; tickets before merges: lo/c/hi = [26, 28, 44] ; portmap central lines 29487 -> revised central 26562
after merge candidates (b),(c),(d) [(a) and (e) not supported]: tickets lo/c/hi = [23, 25, 42]
GRAPH ROWS (LW source file lines; route T = 0.80 x, route I = 0.86 x route T (publicize copy tax 14%: Graph private share 21%); +BA-new lines)
BA-L2c  GGGamma graph op + lem_lweight graph op                2698 -> T   2158  I   1856  (3 / 2 tickets at 1000 lines)
BA-L3a  lvl1 + symmetric forms                                 6668 -> T   5334  I   4588  (6 / 5 tickets at 1000 lines)
BA-L3b  localregular (1)-(6)                                  10565 -> T   8452  I   7269  (9 / 8 tickets at 1000 lines)
BA-L3c  claim:size, GtoAG, claim:xi                            4831 -> T   3865  I   3324  (4 / 4 tickets at 1000 lines)
BA-L3d  moment + Anp lift + aux->NGraph                        1604 -> T   2083  I   1904  (3 / 2 tickets at 1000 lines)
BA-L4   LW-14 chain (Term..Term5 less engine, Cert, Sim, Sound est.)  11701 -> T   9361  I   8050  (10 / 9 tickets at 1000 lines)
graph total: route T 31254 lines, route I 26990 lines; portmap L2(rest)+L3+L4 central 3090 (L2 open part not sized separately)
Anp deterministic (AnpKey..AnpKey6) 7157 file lines: parametric as is, 0 BA lines
TOTALS (tickets, central; lo/hi in brackets)
  used (merged 22 code + 3 design + T2324 in flight): 26
  group A (after merges b,c,d): 25 [23..42]
  chain: route T 92 [69..116] ; route I 78 [54..103]
  graph: route T 31 [23..39] ; route I 27 [20..34]
  G tickets (publicize, ST 5 + LW 2) route I: 7 [5..9]
  TOTAL route T (twin everything): 174 [141..223]
  TOTAL route I (instantiate where possible): 163 [128..214]
  top-down (T2161 T/U/V central x 1.91 measured S-chain factor; graph x 1.3; ignores source growth): 96
  supervisor 0344 Q1 projection 80-85 (76-95); cap 72 (DECISIONS 128)
```
### Narrative
- The worktree was moved from b582dab to main 044707b with `git merge --ff-only` before any analysis (T2315, `Graph/BAExpandWOrd`, is merged), so the BA graph layer in the tables is the current one. Stage 1b is a rerun after a usage-limit stop (CONTROL done-line of 06:24:37 UTC); section (a) is unchanged.
- The probe's statements are not ticket targets; they compile the "parametric as is" claims at BA objects (engine, cutoff lemma with a nondegenerate instance, `Lvl1Lt` measure) and one failing hypothesis (`scalarM_hyp_fails_at_baD`: `LWGtoAG`'s `D.M x y = if x = y then m else 0` at the merged datum `baD`). `ba_mu_lt` is the proof text of `lvl1_mu_lt` with BA counters; the BA twin of the one-step claim and the measure is 31 lines (`BALvl1Good` 7, `BAMu` 3, `ba_mu_lt` 21), the measured size of the generalization G of the lvl1 skeleton.
- Calibration (B2, B3): new-math deterministic rows 0.43 of the portmap central, twin deterministic rows 0.88, stochastic S1-S3 1.91, graph L1 1.63 and L2 1.24; BA twin lines are 0.73 (S-chain) and 0.85 (graph L2) of the lines of the files they port; 18% of the S-chain twin lines copy private band-free helpers.
- Volume (B4, B5): `Induction/` doubled since T2161 (114342 decl-lines against 57206; ST-3 49672 against 18712); 46% of its lines are private; the 23 files NQ*, QBudget*, QDrift*, QEnd*, QLevels*, QProxy, Qt* (32874 lines) occur in no T2161 row (`grep -c "NQ\|QEnd\|Qt"` on `T2161-portmap.md` gives 0). The ST proofs reference only 146-210 model-base declarations per step (B4), the endpoint cones cover 59% of `Induction/` (B5); declarations whose signature is a deterministic statement at an explicit Hermitian matrix are 10% of the Steps 2-6 lines (B4, `matlevel.py`), so a cheap generalization reaches only that tenth.
- Judgment, not script output: the assignment of ST and LW files to BA rows (by file title and the portmap source lists; the file lists are the strings in `chain.py`, `reportcalc.py`) and each verdict of the two tables (read from the statements cited in the portmap). A closure of "band dependence" over definition names (`stmt_dep.py`) marks all but 2% of the `Induction/` lines private or band-dependent through name collisions (`s`, `Xi`, `Ze`); it is uninformative and is not used.
- Not measured: the edited fraction of a carrier refactor (G-in-place), the twin ratio of the KL and Green rows (no merged twin among K, E, G2-G6), the size of T2318 `Sound` (1400 is the ticket's central, DECISIONS §129 (6)).
- Process: `lake build RBM3D.Graph.BAExpandWOrd` (3780 jobs, 8.4 s) ran once in this worktree at 07:05 UTC while T2319's audit certificate build (`LWExpCertBS1`, pid 41271) was running; `vm_stat` just before showed Pages free 6861 and Pages inactive 638454 (16 KiB pages). The background wait I started returned at once with an empty output file. Nothing under `../RBM1D` or `../RBM2D` was read or written; ports from RBM1D/RBM2D: none (no BA or LW graph layer there).

## (c) Verified Mathlib names (each by `#check` in the context of the probe, output in the tool log)

- `Real.rpow_mul` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:415`), `Real.rpow_neg` (`:260`), `Real.rpow_neg_one` (`:474`).
- `Nat.ceil_eq_iff` (`Mathlib/Algebra/Order/Floor/Semiring.lean:189`), `le_rfl` (`Mathlib/Order/Defs/PartialOrder.lean:66`), `one_pos`, `Prod.lex_def` (`Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2`).
- Names verified absent: none looked up. RBM names reused: `expandG_sum`, `ExpandGSum`, `lvl1_size_le`, `lvl1Cutoff`, `Lvl1Lt`, `lvl1Lt_wf`, `Lvl1Good`, `BAGraph.counters_ofLGraph`, `BAGraph.scalingOrder_ofLGraph`, `p2Graph_counters`, `figGraph_counters`, `figGraph_ord`, `BAVocabInst.baD` (all merged, signatures read in B1's file).

## (d) Open issues and paper-delta candidates

- The chain estimate (92k / 78k lines) is a range [69..116] / [54..103]; it rests on two merged twin ratios, on the file assignment, and on the claim that Steps 2-6 need an analogue of every file; the G-in-place pilot (portmap §4) would test the one alternative.
- T2161 rows T1-V3 need re-cutting by the file groups of portmap §3; U3 alone is 28 tickets at the central.
- The `lem_lweight` graph operation is in no ticket (DECISIONS §129 (2)); it is in the row L2c of the re-portmap.
- Publishing tickets edit merged files; they must precede the BA rows that reference the published helpers.
- Paper-delta candidates (the dispatcher numbers them): **T2325a** `B_graphical_lemmas.tex:409-497` sketches the BA proof of `lem:LW_moment` (`:409` "only sketch", `:497` "carries over verbatim"); its Lean cost is a twin of LW-08, LW-10, LW-11, LW-13 (portmap §2). **T2325b** `LWGtoAG` and `lwClaimSize` hypothesize `M = m I`; BA needs bounds on `Ǧ = G - M` with a non-scalar `M` (probe, `scalarM_hyp_fails_at_baD`). **T2325c** BA Step 5 for large `t` (`3_5:2284`, `7_8:2101`) is cited from `[RBSO1D]` and is not in the paper.
