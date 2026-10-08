Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 10:05:02 UTC 2026

Ticket T2326 is a report-only design probe (no theorem with analytic exponents). The "exponents" are the cap-formula constants and the instance data of the band `example`s. Sources: `docs/reports/T2325-portmap.md` (§3 table, §7 totals), `docs/supervisor/2026-10-08-0944.md` (Q3 (b), O2), `RBM3D/BA/FlowPins.lean:332-486`, `RBM3D/Induction/Step2Iterate.lean:284,1937-1948`.

### (i) Exponent table

| quantity | value | constraint | slack / note |
|---|---|---|---|
| `g` (edited fraction) | measured in stage 1b | `g` = (lines changed or added) / (block lines), per site | route-G chain = `S·g + B`; supervisor: `g ≲ 0.3` halves BA (0944 Q3 (b)) |
| `S` = ST Steps 2-6 twin-source lines | 115.8k (T2325 §3 sum row) | the base `g` multiplies | `g` is a file-line fraction, same unit as `S`; decl-line base 103,910 (§3) not used |
| `B` = BA-specific content | ≥ 3.8k (= U5 1300 + V2a 1100 + V2b 700 + V3 700, T2325 §3 col 1) | T1 deterministic `J`, T8 BA pin, carrier-field proofs are not quantified there | `B` = 10k is a sensitivity value, not measured |
| route I chain / route T chain | 78k / 92k lines (T2325 §3 sum row) | route G beats route I iff `S g + B < 78` | break-even `g` = 0.641 (B = 3.8k), 0.587 (B = 10k); vs route T 0.762 / 0.708 |
| totals other than chain | used 26 + group A 25 + graph 27 + G-pub 7 = 85 (route I components, T2325 §7) | route G keeps them (G-pub-ST may shrink: lower bound 85 - 5 = 80, not claimed) | script: 85 + 78 = 163, 26+25+92+31 = 174 reproduce T2325 §7 |
| K/G correction | +20 to +25 tickets (0944 Q1 correction 1) | applies to every route | script uses 22.5 |
| stop rule | probe files ≤ 2500 lines in total | site 1 + site 2 + carriers + examples | estimate 1784 (site 2 = QtNonzeroFlow) or 2135 (QDriftA); slack 716 / 365 |
| site 1 block | `ST_selfImprove_section`, `Step2Iterate.lean:284-669` (386 lines in `section Main`; ticket says ~399 with helpers) | all band reads = `Lloop sz`, `STKloop sz`, `STflowE z`, `STDecay`, `STStep1Weak`, `STScaleInv` | merged carrier precedent already has `STJhatg`, `STEEg`, `STLWassmExpgL` (`FlowPins.lean:~440-460`) |
| site 2 block | `QDriftA` (1341 lines, 55 private decls, in the closure of `Step3`) | ticket: substitute if "mostly band-free" | measured: 56 band lines = 4.2%; see below |
| carrier | `FlowFM sz` fields `L K G M S eta m` (`FlowPins.lean:332-348`), `bandFM sz E` (`:469`), `baFM sz lam0 E` (`:479`) | band instance must recover `Lloop`, `STKloop`, `Gt`, `SB d (sz.L n) (sz.lam n)`, `mE`, `etaT` | `bandFM_STLK` etc. are `Iff.rfl` (`:490-501`), so shape-level recovery is free; proof-level is what `g` measures |

Site-2 choice. The closure of `RBM3D.Induction.Step3` (the module holding `stStep3RegIII_holds`/`stStep3RegI_holds`/`stStep3II_holds`) contains QDriftA, but QDriftA has 4.2% band-mentioning lines (token list in the script), the 10th of 15 Q/NQ files of 800-1500 lines. Under the ticket's substitution rule the candidates by density are `QtNonzeroFlow` (990 lines, 16.9%), `NQEndFlow` (1096, 15.0%), `QtNonzeroBoot` (1265, 14.2%). Recommended: site 2 = `QtNonzeroFlow` (the densest, also cheapest for the 2500-line stop rule); if its imports show it is not on the alternating endpoint chain, take `NQEndFlow`. QDriftA's low `g` would be an under-estimate of the Steps 3-4 average.

Band-line density (token regex over each file; a proxy for "band objects read", not a count of edits):
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2326/density.py
in Step3 import closure: QDriftA = True
file lines band-lines(%) tokens/100lines   [Q/NQ files of 800-1500 lines in the closure]
QtNonzeroFlow          990  167 (16.9)  20.1
NQEndFlow             1096  164 (15.0)  17.9
QtNonzeroBoot         1265  179 (14.2)  16.7
QtNonzeroFlowLift      968  116 (12.0)  17.6
QtXiRoundLift         1099  125 (11.4)  17.0
QBudgetA              1340  143 (10.7)  10.7
NQEndFlowLift         1152  113 ( 9.8)  14.5
NQGood1               1482   79 ( 5.3)   6.3
NQGood2               1186   62 ( 5.2)   5.6
QDriftA               1342   56 ( 4.2)   4.9
QVN                    875   28 ( 3.2)   3.7
QBudgetB              1143   35 ( 3.1)   3.3
QDriftB                952   23 ( 2.4)   2.7
QopAlgebra            1000   19 ( 1.9)   3.1
QopDecay              1079    7 ( 0.6)   1.1
```

### (ii) Concrete nondegenerate instance

Site 1 band instance (the compiled example to be restated over the carrier): the merged `example` at `Step2Iterate.lean:1937-1948` applies `ST_selfImprove_section` at `d = 3`, `(sz0, z0)` (`Defs/Sizes.lean:260`, `Induction/Defs.lean:413`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `Step2Iterate.lean:1853`), `s ≡ 0` (`sInst`), `t ≡ 1/16` (`tInst`), `tt ≡ 1/32`, `D = 1`, `C = 1`, `δ₀ = κ = ε = 𝔡 = 1/10`, `C₀ = 1`, `𝔠d = 1/240`, `𝔠 = 1/6`. The only numerical hypothesis is `h3 : (3C+1)·𝔠d ≤ 1/60`: LHS = 4/240 = 1/60, slack 0 (equality, nondegenerate, all other numerical hypotheses are strict positivity). The pins `STLWT 3`, `STEMn2Exp 3`, `STNewKLKAt`, `STGridMartAt`, `STDecay`, `STStep1Weak`, `STScaleInv` stay hypotheses of the example (other gates' pins, CLAUDE.md §4 step 2). The generic theorem is then applied at `C := bandFM sz0 (fun n => E n)` with `E n` the `z0`-flow energy `STflowE z0`, `μ = seqP sz0`; predicate-level recovery is `Iff.rfl` for the pins already in `FlowPins.lean:490-501`; whether the proof-level recovery is `rfl` is what stage 1b measures.
External hypothesis: none is added by this ticket (the carrier facts are fields/hypotheses of the probe, discharged at `bandFM` by existing merged lemmas; undischarged ones are listed as BA obligations in the pilot report, not assumed true).

Cap-formula instance, checked by script (inputs: T2325 §3, §7 numbers; `g` values are hypothetical, to be replaced by the measured ones):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2326/routeG.py
check route I total 163 (portmap 163)
check route T total 174 (portmap 174)
B=3.8k  break-even g vs route I chain 78k: 0.641;  vs route T chain 92k: 0.762
  g=0.10 chain_G=  15.4 tickets  total_G= 100.4  (+22.5 K/G corr =  122.9)
  g=0.20 chain_G=  27.0 tickets  total_G= 112.0  (+22.5 K/G corr =  134.5)
  g=0.30 chain_G=  38.5 tickets  total_G= 123.5  (+22.5 K/G corr =  146.0)
  g=0.45 chain_G=  55.9 tickets  total_G= 140.9  (+22.5 K/G corr =  163.4)
  g=0.60 chain_G=  73.3 tickets  total_G= 158.3  (+22.5 K/G corr =  180.8)
  g=1.00 chain_G= 119.6 tickets  total_G= 204.6  (+22.5 K/G corr =  227.1)
B=10.0k  break-even g vs route I chain 78k: 0.587;  vs route T chain 92k: 0.708
  g=0.10 chain_G=  21.6 tickets  total_G= 106.6  (+22.5 K/G corr =  129.1)
  g=0.20 chain_G=  33.2 tickets  total_G= 118.2  (+22.5 K/G corr =  140.7)
  g=0.30 chain_G=  44.7 tickets  total_G= 129.7  (+22.5 K/G corr =  152.2)
  g=0.45 chain_G=  62.1 tickets  total_G= 147.1  (+22.5 K/G corr =  169.6)
  g=0.60 chain_G=  79.5 tickets  total_G= 164.5  (+22.5 K/G corr =  187.0)
  g=1.00 chain_G= 125.8 tickets  total_G= 210.8  (+22.5 K/G corr =  233.3)
site1 block lines (Step2Iterate 284-669): 386 ; site2 candidate QtNonzeroFlow: 990 ; carrier ~FlowFM 332-460: 129
probe estimate (copies+2 carriers+examples~150): 1784 <= 2500: True
same with QDriftA (1341): 2135 <= 2500: True
```

Reading: at `g = 0.30`, `B = 3.8k` the route-G chain is 38.5 tickets and the total 123.5 (146.0 with the K/G correction), against 163 (route I) and 174 (route T) before that correction. Route G wins over route I below `g` ≈ 0.64 and is not worth the ST edits above that.

### Verdicts

- Site 1 (`ST_selfImprove_section` over the carrier, with band `example`): **PASS** — statement shape already carrier-generic in `FlowPins.lean`; instance data exist, `h3` closes with slack 0, stop-rule budget has slack 716.
- Site 2 (Q-file family): **PASS** with a flagged substitution — QDriftA is mostly band-free (4.2% band lines), so stage 1b should substitute the densest in-closure file (`QtNonzeroFlow`, else `NQEndFlow`) and say why; the 2500-line budget closes for either (slack 716 / 365).
- Cap deliverable (g, chain, one BA cap): **PASS** as a formula; the numbers depend on the measured `g`. Not claimed here: `B` beyond 3.8k, G-pub-ST savings, the size of new BA field obligations.

## (a′) Preflight corrections — Thu Oct  8 12:06:00 UTC 2026
Two statements of (a) are corrected by an exact traversal of the Lean environment (B6). The verdicts of (a) (PASS, PASS, PASS) are unchanged; the site-2 recommendation changes.
1. "QDriftA is mostly band-free (4.2% band lines)": the denominator was the whole file (1342 lines by the script, 1341 by `wc -l`), of which 703 (`QDriftA.lean:639-1341`) are the instance section. In the 22 declarations that `stStep3RegI_holds` reaches (`:56-495`) the T2325 measure (lines of declarations that mention a band token) is 257/385 = 66.8%, against 50.3% (17784/35324) over the whole cone; token-line density 7.3% against 6.6% (B6).
2. "Site 2 = `QtNonzeroFlow`, else `NQEndFlow`": `QtNonzeroFlow` is reached by `stStep3II_holds` (33 declarations) and by none of `stStep3RegI_holds`, `stStep3RegIII_holds`, `stStep4I_holds` (0). The ticket's cone is that of `stStep3RegI_holds`; QDriftA is in it (22 declarations, also reached from `stStep4I_holds`). No substitution: site 2 = `QDriftA.lean`, block `:54-637`. (a) estimated the probe at 1784 or 2135 lines; the two probe files total 1719 (B0).

## (b) Script output
Commands run in `RBM3D-wt/T2326` (branch `t/T2326`). `S` = the session scratchpad `T2326/` (scripts and logs, not committed). `docs/reports/T2326-pilot.md` cites B5 and B6 and prints its own script output in its section 10.
### B0 provenance and size (stop rule: probe files ≤ 2500 lines)
```
$ date -u; git log --oneline -2; git diff --stat main...t/T2326; wc -l RBM3D/Probe/T2326Pilot*.lean
Thu Oct  8 12:06:00 UTC 2026
4fca3d2 T2326: site 2 probe: concrete-data examples for the four measurability targets
688b372 T2326: site 1 probe: BA carrier constructor baStep2 with the 11 open obligations as arguments; flowOK_
 RBM3D/Probe/T2326PilotQ.lean     | 878 +++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2326PilotStep2.lean | 909 +++++++++++++++++++++++++++++++++++++++
 2 files changed, 1787 insertions(+)
     878 RBM3D/Probe/T2326PilotQ.lean
     909 RBM3D/Probe/T2326PilotStep2.lean
    1787 total
```
### B1 build and axioms (the new public declarations; all 47 print the same set)
```
$ lake build RBM3D.Probe.T2326PilotStep2; lake build RBM3D.Probe.T2326PilotQ   # logs b1.log (12:00:00 UTC), b2.log (12:04:36 UTC)
✔ [3778/3778] Built RBM3D.Probe.T2326PilotStep2 (21s)
Build completed successfully (3778 jobs).
exit code 0
✔ [3847/3847] Built RBM3D.Probe.T2326PilotQ (4.0s)
Build completed successfully (3847 jobs).
exit code 0
warning lines naming a probe file in the two logs: 0
```
```
$ lake env lean <probe file + #print axioms lines>   # ax1.log (Step2, 11:59:37 UTC), ax2.log (Q, 12:04:32 UTC); exit code 0 both
15 + 32 lines '... depends on axioms: [propext, Classical.choice, Quot.sound]', no other axiom.
Step2: ST_selfImprove_sectionG JhatG JhatG_measurable STScaleInvgL GridMartPin bandStep2 bandStep2Facts bandStep2_martPin recovers_merged baLKM baHpath baLKM_eq baLKM_meas baFlow_T0_lt_one baStep2
Q: AvecN aTrueQN dGridQN altB4N altB5N dFlowQN dGridQN_eq_dFlowQN dFlowQN_sumZero aTrueQN_sumZero Qop_fastDecay fastDecay_of_diamInf hker_altQN alt_hkerQN goodSetN_A0clsQN alt_hA0clsQN measurable_altB4N measurable_altB5N measurable_STQopDriftN measurable_dFlowQN bandKer bandQ recovers_dGridQN_eq_dFlowQN recovers_dFlowQN_sumZero recovers_aTrueQN_sumZero recovers_hker_altQN recovers_alt_hkerQN recovers_goodSetN_A0clsQN recovers_alt_hA0clsQN recovers_measurable_altB4N recovers_measurable_altB5N recovers_measurable_STQopDriftN recovers_measurable_dFlowQN
```
### B2 hygiene, name clashes, ports
```
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/Probe/T2326Pilot*.lean; grep -rnw ... <the 14 new public names and the 2 namespaces> RBM3D | grep -v Probe/T2326Pilot | wc -l
RBM3D/Probe/T2326PilotStep2.lean:0
RBM3D/Probe/T2326PilotQ.lean:0
       0
site 2 keeps the merged short names (`altB4N`, `dFlowQN`, ...) inside `RBM.Ind.T2326Pilot`; their full names differ from `RBM.Ind.*` (the probe is not imported anywhere).
ports from RBM1D/RBM2D: none (the probes restate merged RBM3D text; nothing under ../RBM1D or ../RBM2D was read or run)
```
### B3 target statements (extracted from the files by script)
```
$ awk '/^theorem ST_selfImprove_sectionG/{f=1} f{print NR": "$0} /:= by$/&&f{exit}' RBM3D/Probe/T2326PilotStep2.lean
304: theorem ST_selfImprove_sectionG {sz : Sizes d} (Cm : Step2Data sz) (Fa : Step2Facts Cm)
305:     (hLWT : Cm.pLWT) (hEMe : Cm.pEMe) (hd : 0 < d)
306:     {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
307:     (hflow : Cm.flowOK κ ε 𝔠 𝔡) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
308:     (htT : ∀ n, t n ≤ Cm.T0 n)
309:     {C δ₀ C₀ 𝔠d : ℝ} (hC : 0 < C) (hδ₀ : 0 < δ₀) (hC₀ : 0 ≤ C₀)
310:     (hnew : Cm.pNew κ 𝔡 C δ₀) (hmart : GridMartPin Cm C₀)
311:     (h𝔠d : 0 < 𝔠d) (h3 : (3 * C + 1) * 𝔠d ≤ 1 / 60)
312:     (hDec : STDecaygL Cm.toFlowFM Cm.μ s) (hCon : STConStInd sz 𝔠d s t)
313:     (hS1W : STStep1WeakgL Cm.toFlowFM Cm.μ s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
314:     (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
315:       cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
316:     (Kf : ℕ → ℝ → ℝ) (hKok : STScaleOk sz s t Kf) (hinv : STScaleInvgL Cm.toFlowFM Cm.μ s t Kf)
317:     (tt : ∀ n, TimeIcc s t n) (D : ℝ) (hD : 0 < D) :
318:     PrecL sz Cm.μ (U := fun n => STLab sz n)
319:       (fun n i ω => ‖Cm.L n (tt n : ℝ) i.1 i.2 ω - Cm.K n (tt n : ℝ) i.1 i.2‖)
320:       (fun n i _ => ((1 - s n) / (1 - (tt n : ℝ))) ^ (3 * C + 1) *
321:         (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
322:         STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (i.2 0) (i.2 1)) := by
```
```
$ awk ... RBM3D/Probe/T2326PilotQ.lean   # heads of the generic targets 2-7 (the other 3 measurability theorems have the same head)
254: theorem dGridQN_eq_dFlowQN {d : ℕ} {sz : Sizes d} (Cq : QDriftData sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (
266: theorem dFlowQN_sumZero {d : ℕ} {sz : Sizes d} (Cq : QDriftData sz) (n : ℕ) (u : ℝ) {m : ℕ}
320: theorem aTrueQN_sumZero {d : ℕ} {sz : Sizes d} (Cq : QDriftData sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n :
392: theorem hker_altQN {d : ℕ} (Ck : QKerData d) :
455: theorem alt_hkerQN {d : ℕ} (Ck : QKerData d) :
540: theorem goodSetN_A0clsQN {d : ℕ} {sz : Sizes d} (Cq : QDriftData sz) (hd : 3 ≤ d) (m : ℕ)
575: theorem alt_hA0clsQN {d : ℕ} {sz : Sizes d} (Cq : QDriftData sz) (hd : 3 ≤ d) (m : ℕ)
620: theorem measurable_altB4N (u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
```
### B4 compiled nonempty instances and the recovery of the merged statements
```
$ sed -n '/^theorem recovers_merged/,...' RBM3D/Probe/T2326PilotStep2.lean   # `type_of%` = the type of the merged theorem, proved from the generic one
theorem recovers_merged : type_of% @ST_selfImprove_section :=
  fun {d} sz hLWT hEMe hd {κ ε 𝔡 𝔠} hκ hε h𝔡 {z} hflow {s t} hs htT {C δ₀ C₀ 𝔠d} hC hδ₀ hC₀ hnew hmart h𝔠d h3 hDec
      hCon hS1W {cB c} hcB hc hBd Kf hKok hinv tt D hD =>
    ST_selfImprove_sectionG (bandStep2 sz z) (bandStep2Facts sz z) hLWT hEMe hd hκ hε h𝔡 hflow hs htT hC hδ₀ hC₀
      ...
```
```
$ sed -n '/^open RBM.Gauss.SizesInst.../,/hinv (fun n/p' RBM3D/Probe/T2326PilotStep2.lean   # d = 3, sz0, z0, s = 0, t = 1/16, tt = 1/32, D = 1, C = 1, delta0 = kappa = eps = d = 1/10, C0 = 1, c_d = 1/240
open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step2DefsInst RBM.Gauss.Step2IterateInst in
example (hLWT : STLWT 3) (hEMe : STEMn2Exp 3)
    (hnew : STNewKLKAt 3 (1 / 10) (1 / 10) 1 (1 / 10)) (hmart : STGridMartAt 3 1)
    (hDec : STDecay sz0 (STflowE z0) sInst) (hS1W : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hinv : STScaleInv sz0 (STflowE z0) sInst tInst (Kseq0 0)) :=
  ST_selfImprove_sectionG (bandStep2 sz0 z0) (bandStep2Facts sz0 z0) hLWT hEMe (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) flow_z0 hs0 htT (C := 1) (δ₀ := 1 / 10) (C₀ := 1) (𝔠d := 1 / 240) one_pos
    (by norm_num) (by norm_num) hnew (bandStep2_martPin sz0 z0 hmart) (by norm_num) (by norm_num) hDec
    (conStInd_inst (by norm_num)) hS1W bdata_spec.1 bdata_spec.2.1 bdata_spec.2.2 (Kseq0 0)
    (Kseq0_adm.2.1 0) hinv (fun n => ⟨1 / 32, by simp only [sInst, tInst, Set.mem_Icc]; norm_num⟩) 1 one_pos
```
```
$ grep -c '^theorem recovers_' ...PilotQ.lean; grep -c '^example' ...PilotQ.lean; <first example>   # data of QDriftAInst (QDriftA.lean:649-700)
11
7
example :
    dGridQN (bandQ sz0 E0) s0 t0 K0 0 moll sigma4 0 ω0 =
      dFlowQN (bandQ sz0 E0) 0 (gridTime s0 t0 K0 0 0) moll sigma4 ((bandQ sz0 E0).Hpath s0 t0 K0 0 0 ω0) :=
  dGridQN_eq_dFlowQN (bandQ sz0 E0) s0 t0 K0 0 moll sigma4 0 ω0
```
### B5 the edited fraction g (primary measure: `git diff --no-index --numstat`, g = max(added, removed) / merged lines)
```
$ sed -n 277,667p RBM3D/Induction/Step2Iterate.lean > m1.txt; awk '/^-- BEGIN GENERIC BLOCK$/{f=1;next}/^-- END GENERIC BLOCK$/{f=0}f' RBM3D/Probe/T2326PilotStep2.lean > g1.txt
$ sed -n 54,637p RBM3D/Induction/QDriftA.lean > m2.txt; awk '(same awk)' RBM3D/Probe/T2326PilotQ.lean > g2.txt; wc -l m1.txt g1.txt m2.txt g2.txt; git diff --no-index --numstat m1.txt g1.txt; git diff --no-index --numstat m2.txt g2.txt
     391 m1.txt
     391 g1.txt
     584 m2.txt
     497 g2.txt
58	58	m1.txt => g1.txt
90	177	m2.txt => g2.txt
```
```
$ python3 -I S/gscript.py <merged> <first> <last> <probe> BEGIN END [-v]   # difflib cross-check (hunk-wise max), site 1 then site 2
lines equal 333; hunks 39; lines removed 58; lines added 58; edit cost (sum of max(removed, added) per hunk) = 61
g_lines = edit cost / merged lines = 61/391 = 0.156   (added/merged = 0.148)
tokens: merged 5567, generic 5457, edit cost 269, g_tokens = 0.048
lines equal 407; hunks 62; lines removed 177; lines added 90; edit cost (sum of max(removed, added) per hunk) = 177
g_lines = edit cost / merged lines = 177/584 = 0.303   (added/merged = 0.154)
tokens: merged 7877, generic 6735, edit cost 1390, g_tokens = 0.176
  hunk at merged line 503: removed 60, added 1
  hunk at merged line 265: removed 20, added 0
  hunk at merged line 576: removed 7, added 0
```
g_1 = 58/391 = 0.148; g_2 = 177/584 = 0.303 (added lines only: 90/584 = 0.154); both = 235/975 = 0.241. 87 of site 2's 177 removed lines are pure deletions whose text moves into the band instance (hunks at merged lines 503: 60, 265: 20, 576: 7).
### B6 the exact declaration cone of `stStep3RegI_holds` (Lean environment traversal; theorem values included, project modules only)
```
$ lake env lean S/ConeDump.lean (writes cone_decls.tsv); python3 -I S/coneanal.py stStep3RegI_holds | grep ...
== stStep3RegIII_holds: 192 project constants in 23 modules; Induction decl-lines 210
== stStep3RegI_holds: 6006 project constants in 144 modules; Induction decl-lines 35324
== stStep3II_holds: 5205 project constants in 125 modules; Induction decl-lines 23390
== stStep4I_holds: 5769 project constants in 142 modules; Induction decl-lines 33355
stStep3RegI_holds: Induction cone decl-lines 35324, direct-mention (decl-level) 17784 (50.3%), private 22151 (62.7%), token lines 2324 (6.6%)
QDriftA                 385      257 (66.8)       28 ( 7.3)   1342
reached declarations in QDriftA       (RegIII, RegI, II, Step4I): [0, 22, 0, 22]
reached declarations in QtNonzeroFlow (RegIII, RegI, II, Step4I): [0, 0, 33, 0]
reached declarations in NQEndFlow     (RegIII, RegI, II, Step4I): [0, 35, 6, 33]
```
QDriftA declarations reached from `stStep3RegI_holds` (`S/cone.log`, 22 with a source range, lines 56-495): `altB4N altB5N dFlowQN altClsQN kappaAltQN epsAltQN` (private `Psum_add Psum_sub ekSumZero_of_Psum`) `dGridQN_eq_dFlowQN dFlowQN_sumZero Qop_fastDecay fastDecay_of_diamInf` (private `qProxy4C_spec`) `hker_altQN alt_hkerQN` (private `window_of_diamInf`) `QDriftA_W0` (private `W0_spec`) `QDriftA_W0_gt_one goodSetN_A0clsQN alt_hA0clsQN`; the measurability section `:499-637` is not reached.
### B7 gate before every Lean run (CONTROL H101 (4), H122, H129: wait while free memory < 12 GB and a build runs)
```
$ python3 -I S/waitmem2.py   # free = (free + speculative + inactive) pages x 16 KiB (vm_stat); proceeds at >= 12 GB or when no other bin/lean or bin/lake process runs; first line of five run logs
10:27:33 UTC gate open: free+spec+inactive = 9.66 GB, other lean/lake processes = 0, quiet polls = 3
10:39:05 UTC gate open: free+spec+inactive = 10.33 GB, other lean/lake processes = 0, quiet polls = 3
11:00:37 UTC gate open: free+spec+inactive = 11.59 GB, other lean/lake processes = 0, quiet polls = 3
11:59:37 UTC gate open: free+spec+inactive = 11.43 GB, other lean/lake processes = 0, quiet polls = 1
12:00:00 UTC gate open: free+spec+inactive = 11.30 GB, other lean/lake processes = 0, quiet polls = 1
```
Before 10:20 UTC the gate waited: `ps` at 10:11:11 showed `lake build RBM3D.Graph.LWExpCertBS1` (RSS 5.0 GB, 20 min old) and free+spec+inactive = 9.0 GB; it ended before 10:20:36 UTC. The first runs used 3 consecutive quiet polls 10 s apart; from 11:37 UTC 1 poll 2 s apart (other workflows' short `lake env lean` runs kept resetting the window); every run started with 0 other lean/lake processes. Peak memory footprint of the probe runs: 140-210 MB (`/usr/bin/time -l`; max RSS 3.5 GB is the memory-mapped olean closure).

### Narrative
- Two blocks were restated over carriers, compiled with `lake build`, and diffed against the merged text: `ST_selfImprove_section` (`Step2Iterate.lean:277-667`, 391 lines) and `QDriftA.lean:54-637` (584 lines: the 22 declarations of the cone of `stStep3RegI_holds`, plus the measurability section). The probe files hold the generic block between the markers `-- BEGIN GENERIC BLOCK` and `-- END GENERIC BLOCK`.
- Site 1: `Step2Data sz` extends `FlowFM sz` with 19 fields (energy, horizon, laws, matrix flow, grid walk, `(L-K)` of a matrix, the flow setting, `Im m` bound, and 7 opaque predicates and 3 pins that the proof only passes around) and 6 base facts; `Step2Facts Cm` states the 7 lemmas of other blocks that the proof calls (`ST_event_*`, `ST_good_prob`, `ST_good_engine`, `ST_model_le_path`). The generic theorem has the merged hypotheses one for one, with `Cm`, `Fa` added and `sz`, `z` removed; the proof text keeps 333 of 391 lines.
- Site 2: `QKerData d` (propagator family, energy domain, `Im m`, and the kernel fact EK-4) and `QDriftData sz` (9 data fields, 7 facts). Three private helper groups leave the block (87 lines: their text is the band proof of a carrier fact) and the three definitions `AvecN`, `aTrueQN`, `dGridQN` of other files are restated in 35 lines.
- Both band instances recover the merged statements as compiled `type_of%` theorems (1 + 11) and apply the generic theorems at the `d = 3` data of the merged instances (1 + 7 `example`s: targets 2, 3, 4a and the four measurability targets at site 2); pins and stochastic premises stay hypotheses of the example, as in the merged instance.
- Block Anderson: the base layer of `Step2Data` is compiled at BA objects (`baLKM`, `baHpath`, `baLKM_eq`, `baLKM_meas`, `baFlow_T0_lt_one`, section 7 of the Step2 probe), and `baStep2` (section 8) is `Step2Data` at the BA flow with the 11 open obligations (`ev1`-`ev4`, `Good`, `ident`, `martTail`, three pins, `flowOK_m`) as constructor arguments. The BA reading corrected one carrier fact: `flowOK_T` takes `0 < κ` (commit `688b372`; the two generic-block lines that use it were already edited, g unchanged). Not compiled: the proofs of the 11 obligations, the 7 block facts, all of site 2 at BA.
- No concrete-data `example` in the probe for targets 4b, 4c, 5a, 5b, 6a, 6b of site 2: their merged instances (`QDriftA.lean:711-1337`) use private numeric helpers of `QDriftAInst`; the `recovers_*` theorems exist for 5a, 5b, 6a, 6b, and 4b, 4c are unchanged copies. A generic theorem at the band carrier has the merged hypotheses (definitionally) and the merged instances exist, so it is not vacuous.
- Not restated: the other 1670 lines of `Step2Iterate.lean`, the instance sections (`QDriftA.lean:639-1341`, 703 lines; `Step2Iterate.lean:1851-2061`, 211 lines), and the 7 lemmas behind `Step2Facts` (their own `g` is assumed equal to the measured one in the chain count). The two blocks are plumbing-type; the proof-level share that unfolds a primitive band object (12.5% of the chain's declaration lines by a tactic-name proxy) is not measured by them.
- The extrapolation to the chain, the route totals, the BA obligations, the frozen signatures and the cap are in `docs/reports/T2326-pilot.md`; their script outputs are printed there (section 10).
- DECISIONS §144 (Jun, 2026-10-08) removes the BA cap; the ticket's "one recommended BA cap" is delivered as a planning figure for the stage gates, not as a request.

## (c) Verified Mathlib and Lean names used in the new text (all compiled)
`Finset.measurable_sup'`, `Measurable.div_const`, `Measurable.norm`, `Measurable.sub_const`, `Finset.measurable_sum`, `Measurable.mul`, `measurable_const`, `inv_anti₀`, `LT.lt.trans_le`, `Real.sqrt_pos`, `Real.rpow_pos_of_pos`, `Matrix.of`, `Classical.choose_spec`, `dite_eq_left_of_eq_true`, `eq_true`, `norm_le_pi_norm`, `Finset.univ.sup'`/`Finset.le_sup'`, and the core elaborator `type_of%`. RBM3D names: `walk_measurable_loopFine` (`Path/Walk.lean:794`), `BAt0_lt_one` (`BA/MFixedPoint.lean:285`), `BAFlow`, `BAflowT0`, `BAKloop`, `BALloop`, `BAmF`, `ztOf`, `PsiI`, `Sizes.seqHflowBA` (`Gauss/BlockAnderson.lean:83`). Names verified absent: none searched (no Mathlib name was invented; every name above is used in a file that compiled).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. The probes state no new mathematics: each generic statement is the merged statement with band objects replaced by carrier fields.
- The pilot's `g` is a plumbing measure. The share `f_sem` of blocks whose proofs unfold a primitive band object is bounded by a proxy only (pilot report section 5); a first ticket of the T/U/V stage on a semantic-heavy block (for example `LoopGenN`, `ZeroModeCalc`, `KDecay`) would measure it.
- Design freedom: a lower-level carrier (loop data `(H, z)` instead of the observables `LKM`, `ksim`, ...) would shrink the generic text of upper blocks and enlarge the carrier; the pilot did not compare the two.
- Open obligations of `baStep2` (11 arguments): `flowOK_m` (needs `BAWinBulk`, `CouplingWindow.lean:799`, and `BAm_im_lower`, `ImmLower.lean:391`), the events, `Good`, `ident`, `martTail` and the pins; at site 2: `QKerData.ek4` (BA-E2 of T2161, priced in T2325 group A), `Theta_sumZero` (BA twin of `QopAlgebra.lean:715-805`, 91 lines).
- Method note on S: T2325's `S` (115.8k) counts file lines including instance sections; my recount of the same file lists gives 114,998 lines, of which 24,772 (21.5%) are instance sections (pilot report, section 10). Under route G the instance sections of the ST files stay as they are (wrappers keep the band signatures).
