Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct 13 06:09:55 UTC 2026
**Verdicts (math): 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 PASS.** No pin false, no stop rule hit. **Split: the pre-signed 1,950 split does NOT apply** (central 1,758; GridDriftBA 998, GridGoodBA 760; margin +192). C6 notice not due (target 3 central 170 <= 223; hi 260). **T2486 (a) has merged** (`7be99aae`, main HEAD; `docs/queue/T2486.state` updated Tue Oct 13 05:54:13 UTC 2026): the inputs (a) of target 8 exist by name (`baKcalDecay_holds` `KDecayBA:692`, `baSEforLn_holds` `SEforLnBA:221`, `baEtermDecaygL` `:271`, `baStep2Mat_loopForm` `:135`, `baStep34_LCompat` `:122`), so the closure `baGridGood_holds` is expected to be written without a HOLD; but `t/T2492` is at `f1a377e0`, which does not contain them (`git merge-base --is-ancestor 7be99aae HEAD`: no): the 1b must merge main into `t/T2492` first, and the exact-type inline hypotheses of `baGridGood_of` are then unnecessary.
### (i) Exponent table (T = target of the ticket; scripts and outputs below)
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | flow point | d=3, `sz0` (`Defs/Sizes:260`: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6), `zSeq`, `flow_sz0` (`FlowPins:1214`), (kappa,eps,c,dd)=(1/2,1/10,1/6,1/10) | `BAFlow`; `kappa<=Im mF<=1` (T1 (b): `EMn2BA_mF_data`, `BAm_norm_le_one` `Ward:136`) | `Im mF-kappa>=0.499`; `1-Im mF`=5.1e-4, 1.2e-7, 9.6e-10, 3.0e-11 (n=0..3): the bound `<=1` is a theorem, not a margin |
| 2 | F1 window | g0=1.30e-2, 2.0e-4, 1.8e-5, 3.2e-6 (n=0..3) | `KLoop` (`BAKsol_isKLoopS` `KSolve:606`, `hg: 0<g`) and `KTwo` (`baKsol_two` `KInduct:88`) need `0<g0`; `BAflow_lam0_window` (`GreenSchur:72`) gives `0<g0<=dd^-1` only `forall^f n`; `Sizes.lam : N -> R` has no sign field (`Defs/Sizes:144`) | at `sz0` all n: `0<g0<=10`; WO ratio `lam/W^(-3/2+dd)=2(n+1)` exactly (inst.py: True n=0..3) |
| 3 | CT rate (T7) | `c=BAct_rate(3,dd^-1=10,1/2)=4.158e-3`, `B=1/c=240.5` (n-independent) | `BAMB_decay_large` (`CombesThomas:509`): `‖M_ab‖<=c^-1 e^{-c|a-b|}`, `0<g0<=dd^-1`, `BAReal`; CT core (`:288`) with `nu=log(1+kappa/(4 d g0))` has `2 d g0(e^nu-1)=kappa/2` (equality) | flow.py (`U_r=max_{|x|=r} sum_k g0^k a_k(x)/|E+mF|^(k+1)>=|M_0x|`, a_k = walk counts on Z_L^3): `max_r log(U_r/bound)` = -4.29..-4.56 (CT core), -5.48 (c^-1 e^{-cr}); `|mF-trM/L^3|<=2.2e-16` (= `BAMB_diag_eq` `Ward:89`) |
| 4 | (D4) level `C0` (T7) | `C0=1` (any `C0>0`) | at `H0=g0 Psi` (s n=0): `G0=M` (`BAGt_sub_BAMfine` `GreenSchur:219`, `ztOf m E 0=E+m` `GLoopFlow:55`) => `LM=LIM=BAMLoop` (`BAMLoop_trace` `KBase:434`); `K0=BAMLoop` for length>=2 (`IsKLoopS` clause 2, `KLTree:832`) and `=m_sigma` for length 1 (clause 3, `:833`) => `STLKIMg=0` on all loops of `ksim/elklk/egt/ee`; clauses read `0<=RHS` (Gamma>=0, Gamma Phi>=1, eta_0=Im m>=kappa, Bctl>0) | levels (Gamma,Lambda,Phi)=(1,1,1): `1<=Gamma Phi` slack 0; `C0<=Gamma(Gamma Lambda)=1` slack 0. F2's route via `BAMB_row_l1`/Bctl lower bound is not needed; only clause 3 (`‖LM‖<=W^-D'`) has content |
| 5 | far threshold (T7) | `(k,tau',D')`=(2,1,1),(3,1,1): n*=4; (3,1/5,1): 87,742; (3,1/10,1): 4.07e10 | `B^(2k+2) e^{-c W^tau'/(2k+1)}<=W^-D'` (one far edge of the closed path, `j<=2k+2`; `W^{-(j-1)d}<=1` dropped; the ticket's `N^P` is absent: no sum survives) | far set `{ellT W^tau'<=diam_inf}` is empty at `sz0` for n>=1 if tau'=1 (W>L/2); non-empty iff tau'<=1/5 (`W^(1/5)=2(n+1)=L/2`, ellT=1 at u=0). n* is inside the `forall^f` conclusion; the instance uses `Filter.Eventually.exists` |
| 6 | `KTwo` (T3) | algebra defect 2.5e-16 (M sym), 5.1e-16 (non-sym); k=2..6, t in {.3,.8} | needs `0<kappa`, `0<g0`, `BAReal` (`hIm:(E+m).im<>0` of `Step2Kern_thetaKer_BA` `Step2Kern:90`) | pin is true (ktwo.py) |
| 7 | `UStep` (T4) | `‖Mss‖_{inf->inf}`=1.000000; field 1 ratio<=1 (+3e-13 rounding at t=.999); field 2 max ratio 0.999 | `BAReal` only (no `0<g0`): `uKer-1=(t-s)Mss Theta_t` (`BAuKer_eq_one_add` `EKPins:62`), difference `=D^2 Mss Theta_{u+D} Mss Theta_u`, `‖Theta_t‖<=(1-t)^-1` (`EKPins:161`) | field 2 is `D^2/((1-u-D)(1-u))<=D^2/(1-u-D)^2`; so `UStep` holds every n along the flow, the pin's eventual conjunct (T6) is weaker, true |
| 8 | `Expand` constant (T5) | `16(k+3)^4 N^4 (1+eta^-1)^(k+4) D^(3/2)` | same text at `HierDriftGen:660` and `TwistGridRem:578` (`l.length=I.length`); `eta=etaOf` (`baFM`, `FlowPins:328`); needs `0<Im m`, `‖m‖<=1`, `u+D<1` | slack 0 (identical constants) |
| 9 | grid (T5,T9) | `(s,t,K)=(0,1/32,4)`, `D=1/128`, `u_j=j/128` | `0<=s<=t<1`, `K<>0`, `t<=BAflowT0` | `t0=0.694` vs 1/32 slack 0.66; `eta_{u_4}=0.968` (inst.py) |
| 10 | d (T7, T8) | instance d=3; pins are for every d | d=0: `STdiamInf a=0<1<=ellT W^tau'` makes the far premise false; d<3: the `3<=d ->` guard of `BAKcalDecay` (`KDecayBA:689`) and `baEtermDecaygL` (`SEforLnBA:272`), `T2486-prove.md` row 13 | two case splits, about 5 lines each |
### (ii) One concrete nondegenerate instance (numbers; scripts are Python only, no Lean anywhere)
`d=3`, `sz0`, `zSeq`, `flow_sz0` at `(kappa,eps,c,dd)=(1/2,1/10,1/6,1/10)`; index n in {0,1,2,3} (L=4,8,12,16; W=32,1024,7776,32768); `E_n=0` to 1e-18; `(s,t,K)=(0,1/32,4)`, `D=1/128`; loop length k=3, `sigma=(+,-,+)`, `tau'=1/5`, `D'=1`; levels `(Gamma,Lambda,Phi)=(1,1,1)`, `C0=1`. Every hypothesis of T1-T10 that is not an input holds (rows 1, 2, 9; `BAReal`: `BASelf` defect <= 2.2e-16 and `kappa<=Im mF`): T1 (a) `lam0=g0` real, `Psi` Hermitian; (b) `Im mF<=1`; (c) `S=1` (`EMn2BA_SB_zero`, `EMn2BA:77`) so row sums = 1; T2-T5 `0<kappa`, `0<g0`, `BAReal`; T6 flow + `0<kappa`; T7 `s n=0`, `0<=Gamma`, `1<=Gamma Phi`, `C0<=Gamma(Gamma Lambda)`, conclusion eventual (row 5); T8 `3<=d`, `kappa m=kappa<=Im mF` (`hSpec`), inputs (a) read by name from the merged T2486 (a); T9 `STKboundgL` stays a hypothesis (registered `:134`); T10 `hQ` stays a hypothesis. External hypotheses (inputs (b)-(d); (a) is now merged and proved) are not recomputed: the limit computations for them are T2486's 1a (`T2486-prove.md` rows 3-10, 15, 16), `STKboundgL` is proved at `baFMz` (`baKbound_holds`), `hQ` is U3s2's; the only limits this ticket adds are the eventual/CT ones of rows 3 and 5, computed above.
Command (verbatim output follows; sources of each script in `scratchpad/T2492/*.py`):
`bash /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2492/run_all.sh`
```
## flow.py
n  L    W          lam        t0       g0         E          Im mF   |mF-trM/L^3| flow-ok | CT: max_r log(U_r/((2/kap)e^{-nu r})), nu=log(1+kap/(4 d g0)) | max_r log(U_r/(c^-1 e^{-c r})), c=0.004158
0  4    32         1.562e-02  0.69374 1.301e-02  3.124e-18  0.99949 1.11e-16      True                | -4.289       | -5.481
1  8    1024       2.441e-04  0.69444 2.035e-04  2.439e-20  1.00000 2.22e-16      True                | -4.559       | -5.483
2  12   7776       2.143e-05  0.69444 1.786e-05  6.626e-21  1.00000 2.22e-16      True                | -4.564       | -5.483
3  16   3.277e+04  3.815e-06  0.69444 3.179e-06  1.525e-21  1.00000 2.22e-16      True                | -4.564       | -5.483
5  24   2.488e+05  3.349e-07  0.69444 2.791e-07  1.223e-22  1.00000 2.22e-16      True                | -4.564       | -5.483
## far.py
c=BAct_rate=0.004158  B=1/c=240.50  ln B=5.483
k=2 tau'=1    D'=1 : n* = 4        (L=20, W=1e+05, log10 N=(WL)^3 = 18.9) | far set {ellT W^tau' <= diam_inf} nonempty at n*: False
k=3 tau'=1    D'=1 : n* = 4        (L=20, W=1e+05, log10 N=(WL)^3 = 18.9) | far set {ellT W^tau' <= diam_inf} nonempty at n*: False
k=3 tau'=0.2  D'=1 : n* = 87742    (L=350972, W=1.66e+26, log10 N=(WL)^3 = 95.3) | far set {ellT W^tau' <= diam_inf} nonempty at n*: True
k=3 tau'=0.1  D'=1 : n* = 40701159098 (L=162804636396, W=3.57e+54, log10 N=(WL)^3 = 197.3) | far set {ellT W^tau' <= diam_inf} nonempty at n*: True
## inst.py
n  0<g0<=1/dd  WO: W^(-3/2+dd)<=lam  |mF|<=1  kap<=Im mF  1-Im mF  | s<=t<=t0 (t0)   t<1  K!=0  u_j=j/128 (j<=4) < 1 | eta_(u_4)=(1-u_4)Im mF | 3<=L  W>=1
0  True        True                   True     True        5.07e-04 | True (0.6937)          True  True  True                     | 0.9683 | True True
1  True        True                   True     True        1.24e-07 | True (0.6944)          True  True  True                     | 0.9687 | True True
2  True        True                   True     True        9.57e-10 | True (0.6944)          True  True  True                     | 0.9687 | True True
3  True        True                   True     True        3.03e-11 | True (0.6944)          True  True  True                     | 0.9687 | True True
## ktwo.py
M symmetric: True  max rel. defect over k=2..6, t in {0.3,0.8}, 6 draws each: 2.482534153247273e-16
M symmetric: False  max rel. defect over k=2..6, t in {0.3,0.8}, 6 draws each: 5.117875266520903e-16
## ustep.py
n=0: g0=1.3014e-02 E=1.0e-18 mF=-0.000000+0.999493j |mF-trM/N|=2.2e-16
max_{pairs}||Mss||_{inf->inf} = 1.000000 (<=1);  field 1: worst ratio-1 = 3.1e-13 (<=0 up to rounding);  field 2: worst ratio = 0.9990 (<=1)
## lines.py
GridDriftBA (lo/c/hi): hdr 35/45/60 | 1 50/73/120 | 2 20/30/50 | 3 110/170/260 | 4 90/130/210 | 5 280/380/600 | 6 80/110/170 | inst 40/60/100
GridGoodBA (lo/c/hi): hdr 30/40/55 | 7 300/430/680 | 8 60/85/130 | 9 70/100/160 | 10 35/55/90 | inst 35/50/80
GridDriftBA lo/c/hi = [705, 998, 1570] (ticket 555/835/1335) | GridGoodBA = [530, 760, 1195] (ticket 485/745/1175) | total = [1235, 1758, 2765] (ticket 1040/1580/2510)
target 3 (KTwo) lo/c/hi = 110/170/260 ; C6 notice if predicted > 223: central no, hi yes
split rule: central total 1758 vs 1950 -> does not apply (margin +192 = 10%) ; hi 2765 -> would apply
reserve rule (>1800 predicted per file): GridDriftBA c=998 hi=1570 -> no ; GridGoodBA c=760 hi=1195 -> no ; stop 2000/file: none above
calibrated (x0.78..x1.62): total 1363..2847 ; GridDriftBA 774..1616 ; GridGoodBA 589..1231 ; 1950 crossed above x1.11 ; TLC-4 2.6x on my central: 2594 / 1976 (ticket's: 2171 / 1937)
## reg.py
BAFlow (T1,6,7,8,9,10)             flow_sz0                     concludes: BAFlow sz0 (1 / 2) (1 / 10) (1 / 6
BAReal (T2-5)                      BAflow_real                  concludes: BAReal d (sz.L n) (BAflowLam0 sz z
StepDecompGen_LoopForm (T6,8,9,10) stepDecompGen_loopForm_band  concludes: StepDecompGen_LoopForm (bandStep2M
StepDecompGen_WalkForm (T10)       stepDecompGen_walkForm_band  concludes: StepDecompGen_WalkForm (bandStep2M
Step34Gen_LCompat (T8)             bandStep34_LCompat           concludes: Step34Gen_LCompat (bandStep2Mat sz
Step34Gen_KCompat (T8)             bandStep34_KCompat           concludes: Step34Gen_KCompat (bandStep2Mat sz
STDecayLoopUgL (T8, inside hEK)    stDecayLoopUgL_of_step2      concludes: STDecayLoopUgL C μ s t
QVPropagatedNg (T10 hQV)           qvPropagatedNg               concludes: QVPropagatedNg Cm g
AzumaSubGNg (T10 h)                azumaSubGNg                  concludes: AzumaSubGNg Cm lam' s t K
GridRepTailGen_Ker (T10 hKer)      gridRepTailGen_ker_BA        concludes: GridRepTailGen_Ker (baStep2Mat sz 
YMomentsNg (conclusion)            yMomentsNg                   concludes: YMomentsNg Cm κm τ' s t K
registered: GoodSetNg Axioms.lean:237; STKcalDecaygL Axioms.lean:195; STSEforLngL Axioms.lean:235; STEKDecaygL Axioms.lean:236; STKboundgL Axioms.lean:134
T4-BA occurrences in Axioms.lean: [237]
```
### (iv)-(vi) formulas, size, registry (each line backed by the output above or by the cited file:line)
- **KTwo (T3).** `K^(2)_{s0 s1}(a0,a1)=W^-d (Theta_u Mss)^{s0 s1}(a0,a1)` (`baKsol_two`), `S=1`; in `ksim` at `l_K=2` the right factor has length 2 iff `l'=k'+1` (k-1 cuts), the left iff `(k',l')=(1,k)` (1 cut): k terms = the k slots of `Step2Gen_ThetaN`, `thetaKer=Theta Mss` (`Step2Kern:90`); ktwo.py checks it with the cut operators of `TreeRep:75-82`. The merged algebra `couplingLen_two_Kval_eq_thetaOp` (`HierAlgebra:620`) is not reusable: its helpers `HierAlgebra_thetaR_term/thetaL_term/couplingLen_two_eq_sum` (`:484-563`) are `private` and assume the scalar `kTwo` (`Primitive:46`); BA `K^(2)` is matrix valued, so three lemmas are re-proved (inside T3's 170).
- **Expand (T5).** (1) freeze: pattern `TwistGridRem2_condExp_step` (`:168`) with the loop word `TwistGridRem_F` (generic `l : List (Bool x iota)`, `TwistGridRem:73`); (2) `TwistGridRem_envelope_word` (`:572`), constants identical (row 8), `‖Eblk‖<=1` (`OneStep_norm_Eblk_le_one`); (3) `TwistGridRem_g 0 + J1 = genMatOf 0 m E u` is not merged for a loop word (only the twisted-2-loop analogue `twGenM`, `TwistGrid:117`), then `genMatOf=treeEqRhsS (S)+STegtMg` by `loopGenNOf` (`LoopGenN`, Hermitian `Hpath` from `baStep2Mat_Hpath_herm`). **Filtration trap:** `PathOmega sz := N -> Sizes.SeqOmega sz`, `SeqOmega` depends on `(L,W)` only (`FineModel:156-160`), so `filt sz j` and `filt (sz.withLam 0) j` are definitionally equal; the merged `TwistGridRem2:217` already uses `change Measurable[filt (sz.withLam 0) j] (... : PathOmega sz ...)`. No obstruction.
- **T7 far clause.** Only `‖LM‖<=W^-D'` has content (row 4); `DecayGenTw_baWardPair` (merged) gives a pair `c` with `diam<=(k-1)|c1-c2|`, a possible shortcut; `zdistInf_le_zdistD` (`Defs/Sizes:117`) turns `diam_inf` into the l1 distance of `BAMB_decay_large`. **T9:** `hKK` (KLink, every n), `hη` (`0<eta<=1-v`: `Im m` in `[kappa,1]`, every n) are `forall n` and hold; only `hGD` needs the eventual copy.
- **Size (v).** Per file, central: `GridDriftBA` 998, `GridGoodBA` 760, total 1,758 (ticket 835 + 745 = 1,580). Differences: instances of T1-T6 live in `GridDriftBA` (CLAUDE.md 4 step 2), the ticket counted all of T11 in `GridGoodBA`; T3 170 (ticket 130), T7 430 (ticket 450), T8 85 (the conditional form may drop: -30 at most). Rule "central > 1,950" is false => no split, no REQ; reserve rule (>1,800 per file) not triggered; stop line 2,000: hi 1,570 / 1,195. Realized/central of peers 0.78-1.62 (`T2486-prove.md:69`) would give 1,363-2,847: 1,950 is crossed only above x1.11, then per file 1,616 / 1,231 < 2,000. T3 hi 260 > 223: the notice would be due only if T3 is realized above 223.
- **Registry (`Test/Axioms.lean`, 646 lines, scan `:471-492`).** Prop defs in binder types of the new public theorems are either registered (`GoodSetNg` `:237` (T10 `hQ`), `STKcalDecaygL` `:195`, `STSEforLngL` `:235`, `STEKDecaygL` `:236`, `STKboundgL` `:134`) or the conclusion head of a theorem (reg.py above). `GoodSetNg` is concluded by no theorem (T7 concludes `∃ C0 ...`), so it stays assumed (`hQ`). **Lines needed: none added; one comment edit at `:237`** ("BA: the initial membership is owed to T4-BA (...)" becomes "BA: the initial membership is `baGoodSetNg_init` (T2492, T5-BA; `∀ᶠ n`, 2351 T4S2-C2/C3)"); `T4-BA` occurs only there. T2486 (a) merged with its `Test/Axioms.lean` edit (8 lines): the line numbers above are read on main `7be99aae`. Root imports: `RBM3D.BA.GridDriftBA`, `RBM3D.BA.GridGoodBA` after the last import (`RBM3D.lean:579` on main now).
- **Per target.** T1 PASS (`WalkForm` at `lam'=0`: `Pp`, `Hpath` definitional, `Psi` Hermitian; `Im m<=1` row 1); T2 PASS (`KLink` = `baStep2Mat_KI` + `baFM` K field `BAKloop`, FlowPins:324; `KLoop` row 2); T3 PASS (row 6, hi 260); T4 PASS (row 7); T5 PASS (row 8, three steps below); T6 PASS (`UStep` every n, `KLoop/KTwo` eventually: row 2); T7 PASS (rows 4-5; simpler than the ticket's F2: no (D4) work); T8 PASS (11 premises of `gridGoodNgL_of` as in table F3, all discharged by merged names once main is merged in; `by_cases 3<=d`; `hSE` at `R:=STAny`; the conditional `baGridGood_of` is dropped or kept as a 10-line wrapper, closure last); T9 PASS (private eventual copy); T10 PASS (`gridRepTailGen_ker_BA` for `hKer`, `qvPropagatedNg` at `g=0` for `hQV`); T11 PASS (inst.py).
- **Stop rules 1-7:** 1 no (central 998 / 760 per file); 2 no (T3/T4/T5 need only `0<kappa`, `0<g0`, `BAReal`; `C0=1` does not depend on `(sz,z)`); 3 no (nothing compares `BAflowLam0` with `sz.lam`; the far clause uses only `1<=ellT`, `one_le_ellT` `Defs/Params:39`; `withLam` only in `seqP (sz.withLam 0)` and `WalkForm` at `0`); 4-7 no (no new `Prop` def, kernel or field; no merged file edited; no second proof of a T2486 fact).
- **Paper-delta candidates:** T2492a (BA initial membership holds eventually; `C0=1` since `𝓛_0=𝒦_0`, far clause by Combes-Thomas); T2492b (BA drift classes `KLoop/KTwo` hold past the WO window, F1).
- **Observations for the 1b:** `UStep` holds every n (row 7); instances of T1-T6 go into `GridDriftBA`; target 7's instance applies the eventual statement at `Filter.Eventually.exists` (n* of row 5 is not computed in Lean); `d=0` and `d<3` case splits (row 10).

## (a′) Preflight corrections — Tue Oct 13 07:01:07 UTC 2026
- **Row 4 / T7 (D4) is not vacuous.** Section (a) says `STLKIMg=0` on all loops of `ksim/elklk/egt/ee` and that `C0=1` (any `C0>0`) works. `STeeMg` is built from `STLIMg` (a `(2k+2)`-loop of `𝓛`), not `𝓛-𝒦` (`Step2Gen.lean:960` `STeeMg`), so its summands are `BAMLoop` values of `(2k+2)`-loops, not zeros (the Lean proof does not use vanishing there); the `ksim/elklk/egt` clauses do vanish. The Lean level is `C₀ = k (1+𝔡⁻²)^{2k}` (`GridGoodBA_ee_level`, `GridGoodBA_goodSet_n`): `‖STeeMg‖ ≤ k W^{-2kd}` from Ward and Cauchy-Schwarz, `Bctl n 0 ≥ W^{-d}(1+𝔡⁻²)⁻¹` once `g_n ≤ 𝔡⁻¹`. No Combes-Thomas and no `BAMB_row_l1` enters this clause.
- **Row 5 / T7 far clauses.** Section (a) drops the sum. The `ee` far clause sums over the free label `b`; the Lean threshold is `k L^d c⁻¹ e^{-c W^{τ'}/(2k+2)} ≤ W^{-D'}` with `L^d ≤ N ≤ W^{1/𝔠}` (Bandwidth), proved eventually by `Tendsto` (`GridGoodBA_far_ev`); n* is not computed in Lean.
- **Row 10 / T8.** T2486 (a) is merged, so `baGridGood_holds` reads `baKcalDecay_holds`, `baStep2Mat_carrierFacts`, `baSEforLn_holds`, `baEtermDecaygL` by name; `baGridGood_of` keeps the four as hypotheses of exact type (check shape) and the closure is one line.
- **Size (v).** Realized lines are in (b); the split rule (central > 1,950) was not triggered by (a) and no file passes 2,000.

## (b) Script output

### (b1) Lines per file against the stop line 2,000; split; C6
```
$ wc -l RBM3D/BA/GridDriftBA.lean RBM3D/BA/GridGoodBA.lean   # no reserve file used; no split (a) central 1,758 <= 1,950
     757 RBM3D/BA/GridDriftBA.lean
    1331 RBM3D/BA/GridGoodBA.lean
    2088 total
$ C6: KTwo = "section Two" .. "end KTwoBA" in GridDriftBA.lean
lines 115 to 332 = 218 (notice threshold 223)
```
### (b2) Build (branch t/T2492, HEAD 27b930f0)
```
$ lake build RBM3D.BA.GridDriftBA RBM3D.BA.GridGoodBA | tail -4
warning: RBM3D/BA/GridGoodBA.lean:25:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4109 jobs).
$ lake build | tail -3     # full library with the two root imports and #assert_rbm_axioms
 RBM.Gauss.Sizes.STLWT].
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4355 jobs).
```
### (b3) `#print axioms` of every public declaration of the two files
```
$ lake env lean axioms.lean   # one #print axioms per public theorem/instance (24), output grouped by axiom set
24 decls with axioms [propext, Classical.choice, Quot.sound]:   baStep2Mat_walkForm   baStep2Mat_imLeOne   baStep2Mat_S   baStep2Mat_S_rowSum   baStep2Mat_isProb   baHierDrift_kLink   baHierDrift_kLoop   baHierDrift_kTwo   baHierDrift_uStep   baHierDrift_expand   baHierDrift_kClasses   baHierDrift_classes   baGridDrift_ev   baQVPropagated   GridDriftBAInst.inst_real   GridDriftBAInst.inst_lam0_pos   GridDriftBAInst.inst_loopForm   baGridGood_of   baGridGood_holds   baGridDrift_envelope   baAzumaSubG   baYMoments   baAzumaProxy_subG_goodExit   baGoodSetNg_init
```
### (b4) Target statements (extracted by script; full text at file:line)
Names for the pins: 1a `T2492_WalkForm`=baStep2Mat_walkForm; 1b `T2492_ImLeOne`=baStep2Mat_imLeOne; 1c `T2492_SLaw`=baStep2Mat_S, `T2492_ProbPp`=baStep2Mat_isProb; 2 `T2492_KLink`=baHierDrift_kLink; 2-4 `T2492_KClasses`=baHierDrift_kClasses (parts baHierDrift_kLoop/kTwo/uStep); 5 `T2492_Expand`=baHierDrift_expand; 6 `T2492_DriftClasses`=baHierDrift_classes; 7 `T2492_InitMem`=baGoodSetNg_init; 8 `T2492_BAGridGood d`=baGridGood_holds d (conditional baGridGood_of).
```
$ python3 extract.py   # signature text of each target, whitespace collapsed, cut at 420 characters
[1a] GridDriftBA.lean:71: theorem baStep2Mat_walkForm (sz : Sizes d) (lam0 E : ℕ → ℝ) : StepDecompGen_WalkForm (baStep2Mat sz lam0 E) 0 (fun n => ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))
[1b] GridDriftBA.lean:81: theorem baStep2Mat_imLeOne (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n).im ≤ 1
[1c] GridDriftBA.lean:86: theorem baStep2Mat_S (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) : (baStep2Mat sz lam0 E).S n = SB d (sz.L n) 0
[1c] GridDriftBA.lean:90: theorem baStep2Mat_S_rowSum (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (a : Zd d (sz.L n)) : ∑ b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).S n a b‖ ≤ 1
[1c] GridDriftBA.lean:98: instance baStep2Mat_isProb (sz : Sizes d) (lam0 E : ℕ → ℝ) : IsProbabilityMeasure (baStep2Mat sz lam0 E).Pp
[2] GridDriftBA.lean:102: theorem baHierDrift_kLink (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) : HierDriftGen_KLink (baStep2Mat sz lam0 E) n
[2] GridDriftBA.lean:107: theorem baHierDrift_kLoop (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : 0 < lam0 n) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_KLoop (baStep2Mat sz lam0 E) n
[3] GridDriftBA.lean:263: theorem baHierDrift_kTwo (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : 0 < lam0 n) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_KTwo (baStep2Mat sz lam0 E) n
[4] GridDriftBA.lean:389: theorem baHierDrift_uStep (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_UStep (baFM sz lam0 E) n
[5] GridDriftBA.lean:556: theorem baHierDrift_expand (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (s t : ℕ → ℝ) (K : ℕ → ℕ) : HierDriftGen_Expand (baStep2Mat sz lam0 E) s t K n
[2-4] GridDriftBA.lean:622: theorem baHierDrift_kClasses (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (hg : 0 < lam0 n) (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) : HierDriftGen_KLoop (baStep2Mat sz lam0 E) n ∧ HierDriftGen_KTwo (baStep2Mat sz lam0 E) n ∧ HierDriftGen_UStep (baFM sz lam0 E) n
[6] GridDriftBA.lean:631: theorem baHierDrift_classes (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) : (∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ), HierDriftGen_Expand (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n) ∧ (∀ n : ℕ, HierDriftGen_KLink (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n) ∧ (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz ...
[6] GridDriftBA.lean:649: theorem baGridDrift_ev (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0) : ∀ᶠ n in Filter.atTop, ∀ j : ℕ, j < K n → ∀ k : ℕ, 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk → (∀ ...
[6] GridDriftBA.lean:672: theorem baQVPropagated (sz : Sizes d) (lam0 E : ℕ → ℝ) (hL : StepDecompGen_LoopForm (baStep2Mat sz lam0 E) E) : QVPropagatedNg (baStep2Mat sz lam0 E) 0
[7] GridGoodBA.lean:1232: theorem baGoodSetNg_init {d : ℕ} (κ ε 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (k : ℕ) (hk : 1 ≤ k) : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ Γ Λ Φ : ℕ → ℝ, (∀ n, 0 ≤ Γ n) → (∀ n, 1 ≤ Γ n * Φ n) → (∀ n, C₀ ≤ Γ n * (Γ n * Λ n)) → ∀ τ' D' : ℝ, 0 < τ' → 0 < D' → ∀ᶠ n in atTop, ∀ (s v : ℕ → ℝ) (K : ℕ → ℕ) (ω : PathΩ sz), s n = 0 → GoodSetNg (baStep2Mat sz (BAflowLam0 sz z)...
[8] GridGoodBA.lean:59: theorem baGridGood_of (d : ℕ) (hKcal : 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (baFMz sz z)) (hCarrier : (∀ (sz : Sizes d) (lam0 E : ℕ → ℝ), Step34Gen_LCompat (baStep2Mat sz lam0 E) (sz.seqHflowBA lam0) ∧ Step34Gen_KCompat (baStep2Mat sz lam0 E)) ∧ (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → StepDecompGen_LoopForm (baStep2Mat sz...
[8] GridGoodBA.lean:106: theorem baGridGood_holds (d : ℕ) : GridGoodNgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => BAflowT0 sz z)
[9] GridGoodBA.lean:197: theorem baGridDrift_envelope {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)) (hKb : STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))) (k : ℕ) (hk : 2 ≤ k) (τK : ℝ) (hτK : 0 < τK) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ BAflowT...
[10] GridGoodBA.lean:233: theorem baAzumaSubG (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGNg (baStep2Mat sz lam0 E) 0 s t K
[10] GridGoodBA.lean:239: theorem baYMoments (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)) (κm τ' : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : YMomentsNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) κm τ' s t K
[10] GridGoodBA.lean:249: theorem baAzumaProxy_subG_goodExit (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hL : StepDecompGen_LoopForm (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (BAflowEs sz z)) {s v : ℕ → ℝ} {K : ℕ → ℕ} (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ K n) (a : Fin k → Zd d ...
```
### (b5) Statement diff against the pins `T2492_*` (Part 2 of `docs/tickets/checks/T2492-check.lean`, copied verbatim into `pins_check.lean`)
```
$ tail -11 pins_check.lean
example : RBM.BA.T2492_WalkForm := fun sz lam0 E => RBM.BA.baStep2Mat_walkForm sz lam0 E
example : RBM.BA.T2492_ImLeOne := fun sz κ ε 𝔠 𝔡 z h n => RBM.BA.baStep2Mat_imLeOne sz κ ε 𝔠 𝔡 z h n
example : RBM.BA.T2492_SLaw := fun sz lam0 E n => RBM.BA.baStep2Mat_S sz lam0 E n
example : RBM.BA.T2492_ProbPp := fun sz lam0 E => RBM.BA.baStep2Mat_isProb sz lam0 E
example : RBM.BA.T2492_KLink := fun sz lam0 E n => RBM.BA.baHierDrift_kLink sz lam0 E n
example : RBM.BA.T2492_KClasses := fun sz lam0 E n κ hκ hg hr => RBM.BA.baHierDrift_kClasses sz lam0 E n κ hκ hg hr
example : RBM.BA.T2492_Expand := fun sz lam0 E n κ hκ hr s t K => RBM.BA.baHierDrift_expand sz lam0 E n κ hκ hr s t K
example : RBM.BA.T2492_DriftClasses := fun sz κ ε 𝔠 𝔡 z hκ hflow => RBM.BA.baHierDrift_classes sz κ ε 𝔠 𝔡 z hκ hflow
example : RBM.BA.T2492_InitMem := fun κ ε 𝔡 hκ hε h𝔡 k hk => RBM.BA.baGoodSetNg_init κ ε 𝔡 hκ hε h𝔡 k hk
example : ∀ d, RBM.BA.T2492_BAGridGood d := fun d => RBM.BA.baGridGood_holds d
end
$ lake env lean pins_check.lean     # imports RBM3D.BA.GridDriftBA, RBM3D.BA.GridGoodBA
(empty output: the ten examples elaborate; a mis-typed negative control, pins_neg.lean, gives "Type mismatch")
$ lake env lean shape_check.lean   # Shape1..5 = the check shapes of 6, 9, QV, Y moments, Azuma (not binding); "example : ShapeK := name"
example : Shape1 := @baGridDrift_ev
example : Shape2 := @baGridDrift_envelope
example : Shape3 := @baQVPropagated
example : Shape4 := @baYMoments
example : Shape5 := fun sz lam0 E _ s t K => baAzumaSubG sz lam0 E s t K
errors in shape_check.lean (Shape6 only): 1
$ Shape6 = shape of baGridGood_of; the two STEKDecaygL implicits in the error text (has type / expected type):
@STEKDecaygL d (sz.withLam 0) (sz.withLam 0).seqP
@STEKDecaygL d sz (sz.withLam 0).seqP
$ same, with "STEKDecaygL (Sizes.seqP" -> "STEKDecaygL (sz := sz) (Sizes.seqP" in Shape6 (shape_check_fixed.lean); example : Shape6 := baGridGood_of
(empty output)
```
### (b6) Compiled nonempty instances (d = 3, `sz0`, `zSeq`, `flow_sz0` at (1/2, 1/10, 1/6, 1/10), grid (s,t,K) = (0, 1/32, 4))
```
$ grep -n "^example\|^theorem inst_" (line numbers only)
GridDriftBA.lean (targets 1-6, no hypothesis left): 690 695 699 705 709 712 715 719 723 726 730 734 738 743 745 747 751 
GridGoodBA.lean  (targets 7-10; hypotheses left: STLKgL, STStep2ConclgL, hQ): 1269 1275 1287 1297 1304 1307 1311 
$ sed -n 1286,1296p RBM3D/BA/GridGoodBA.lean    # target 7: the eventual statement applied, then Filter.Eventually.exists
/-- **Target 7** at the data: `k = 3`, `(κ, ε, 𝔡) = (1/2, 1/10, 1/10)`, the levels `Γ ≡ Φ ≡ 1`, `Λ ≡ C₀`; the conclusion holds
at some index `n`, for every `ω`, on the grid `(s, v, K) = (0, 1/32, 4)`. -/
example : ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ n : ℕ, ∀ ω : PathΩ sz0,
    GoodSetNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) n (gridTime (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) n 0)
      3 1 C₀ 1 1 1 ((baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).Hpath (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) n 0 ω) := by
  obtain ⟨C₀, hC₀, H⟩ := baGoodSetNg_init (d := 3) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 3 (by norm_num)
  have h := H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1) (fun _ => C₀) (fun _ => 1) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by simp) 1 1 one_pos one_pos
  obtain ⟨n, hn⟩ := h.exists
  exact ⟨C₀, hC₀, n, fun ω => hn (fun _ => 0) (fun _ => 1 / 32) (fun _ => 4) ω rfl⟩

```
### (b7) Name clash, greps, layering, diff, registry
```
$ clash.sh   # 24 new public names against main and branches t/T2477..t/T2493 (git grep of theorem/def/instance/lemma/abbrev heads)
refs checked:       25; names:       24; clash lines: 0
$ grep -nE 'STGridRepNgL|baStep1_holds\b|\|E\||2 - κ|\bmE\b|zt E|STFlow|lemT|‖m‖ = 1' both files; echo exit=$?
exit=1
$ grep -nE "≤ A \*" both files; echo exit=$?
exit=1
$ grep -nE "^(noncomputable )?(private )?(def|abbrev|structure|class) "   # all private, none Prop-valued (ℂ, Zd, Zd)
GridGoodBA.lean:456:private def GridGoodBA_edge (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L))
GridGoodBA.lean:642:private def GridGoodBA_eeX {k : ℕ} (a : Fin k → Zd d L) (c : ℕ) : Zd d L :=
GridGoodBA.lean:646:private def GridGoodBA_eeY {k : ℕ} (a' : Fin k → Zd d L) (c : ℕ) : Zd d L :=
$ grep -n withLam both files: 22 hits are "seqP (sz.withLam 0)" (the law, in statements and instances); the others are not statements:
GridDriftBA.lean:97 (docstring) 99 (proof of the Prob instance) 449 (docstring) 461-511 (private freeze lemma, proof body); GridGoodBA.lean:54 (docstring)
$ grep -rl "import RBM3D.BA.GridDriftBA\|import RBM3D.BA.GridGoodBA" RBM3D RBM3D.lean
RBM3D/BA/GridGoodBA.lean
RBM3D.lean
$ git diff --stat main...t/T2492
 RBM3D.lean                |    2 +
 RBM3D/BA/GridDriftBA.lean |  757 ++++++++++++++++++++++++++
 RBM3D/BA/GridGoodBA.lean  | 1331 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    2 +-
 4 files changed, 2091 insertions(+), 1 deletion(-)
$ git diff main...t/T2492 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep "^[+-]" | cut -c1-230
+import RBM3D.BA.GridDriftBA
+import RBM3D.BA.GridGoodBA
-   `RBM.BA.GoodSetNg, -- the good set of the grid walk at a spectral time over a carrier (`Chain/GridGoodGen.lean:145`, `T2473_GoodSetNg`) as a premise: the initial membership `H_0 ∈ GoodSetNg` at `s n = 0` (hypothesis `h0` of `a
+   `RBM.BA.GoodSetNg, -- the good set of the grid walk at a spectral time over a carrier (`Chain/GridGoodGen.lean:145`, `T2473_GoodSetNg`) as a premise: the initial membership `H_0 ∈ GoodSetNg` at `s n = 0` (hypothesis `h0` of `a
$ grep -n "T4-BA" RBM3D/Test/Axioms.lean; echo exit=$?   # no other occurrence
exit=1
```
### (b8) Narrative
- **Delivered:** targets 1-11 (no split: (a) central 1,758 <= 1,950; realized 757 + 1,331 lines, both under 2,000; no reserve file). T2486 (a) is on `main`, so `baGridGood_holds` is written by name and `baGridGood_of` keeps the four T2486 texts as exact-type hypotheses (check shape); no `HOLD closure`.
- **Base:** `t/T2492` was merged with `main` at 4e78c3da (fast-forward) before the first Lean line. `main` is now 5fbefff2 (T2486b, T2489 merged); `git diff 4e78c3da main` over `RBM3D/BA|Chain|Induction|Path` shows only the new `BA/B45BA.lean`, so no file imported here changed.
- **Ports:** none from RBM1D/RBM2D (no `diff --stat`). Patterns are internal files: `HierAlgebra.lean:408, 434` (`primBilLen_two_eq`, `primBilLenR_two_eq`, with `S` in place of `SB`), `TwistGridRem2.lean:168` (freeze), `GridEnvelopeGen.lean:67` (envelope), `AzumaProxyN.lean:924` (initial membership, band).
- **T1-T2:** `WalkForm` is definitional plus `PsiI_isHermitian`; `Im m <= 1` is `EMn2BA_mF_data.2`; `KLink` is `rfl`; `KLoop` is `BAKsol_isKLoopS (baKsolve d)` at `Lambda = g = lam0 n`.
- **T3 (`KTwo`):** `GridDriftBA_coupling_two` is the `l = 2` coupling at `S = 1` for a generic one-index kernel `T` with `K^(2) = W^{-d} T` and `T s1 s2 x y = T s2 s1 y x`; the symmetry comes from `BAKsol_rotate`, not from `Theta` symmetry; `baKsol_two` + `Step2Kern_thetaKer_BA` identify `T` with `thetaKer`.
- **T4 (`UStep`):** needs only `0 < kappa` and `BAReal`, every `n` (`GridDriftBA_uKer_second`: resolvent identities, `Step2Kern_Theta_comm`, `EKPins_norm_Theta_le`).
- **T5 (`Expand`):** `GridDriftBA_condExp_step` freezes the step at coupling `0` for any bounded continuous observable; `filt sz j` and `filt (sz.withLam 0) j` are one sigma-algebra (the lemma compiles with `filt sz j`). `TwistGridRem_envelope_word` with letters `Eblk`, then `GridDriftBA_genMatOf_eq` (`TwistGridRem_deriv_deriv`, `TwistGridRem_hasDerivAt_spec0`) and `GridDriftBA_genMatOf_pair` (`loopGenNOf` at `g = 0`, `S = 1`; no `LoopForm` is read).
- **T6:** `baHierDrift_classes` (Expand, KLink, row sums every `n`; KLoop/KTwo/UStep eventually through `BAflow_lam0_window`); `baGridDrift_ev` (`gridDriftNg_at` past the window); `baQVPropagated` (`qvPropagatedNg` at `g = 0`).
- **T7:** `G_0 = M` (`BAMres_fine_kron`, `ST_Gres_false`), `L_0 = BAMLoop = K_0` on well-formed loops of length >= 1, so the clauses with `L - K`, `ksim`, `elklk`, `egt` are `0`. Level (D4): `GridGoodBA_ee_level`. Far clauses: `GridGoodBA_BAMLoop_far` (a far pair on a cyclic list forces one far edge, `GridGoodBA_far_edge`; `BAMB_decay_large` at `Lambda = 𝔡⁻¹`), thresholds `GridGoodBA_far_ev`. `d = 0` is excluded by `GridGoodBA_pos_d` (a far pair forces `0 < d`); the pin's `3 <= d` guard is inside `GridGoodNgL` (`baGridGood_of` splits on it).
- **T9:** the envelope is a private eventual copy `GridGoodBA_envelope_ev` (X1-C4); T2491's generic eventual envelope will make it redundant.
- **Deviations from the ticket text:** `GridDriftBA` imports `BA/SEforLnBA` (not in the ticket's list) only for `baStep2Mat_loopForm` in its instances; `baStep2Mat_isProb` is an `instance`; the check shape of `baGridGood_of` mis-elaborates `STEKDecaygL` (see (d)); the (D4) level and far thresholds differ from (a) (see (a′)).
- **Hypotheses left in instances (other gates' pins):** `STLKgL`, `STStep2ConclgL` (T1-BA, target 8 example), `hQ` (input (d), target 10). `STKboundgL` and `STKwardgL` are discharged by `inst_BAKbound` and `baKward_holds` (targets 8-9). Everything deterministic is discharged, including `LoopForm` (T2486) and `(con_st_ind)`.

## (c) Verified Mathlib names (each used in a file that builds)
`Finset.prod_sdiff`, `Finset.prod_pair`, `Finset.prod_singleton`, `Finset.prod_le_one₀` (the root `Finset.prod_le_one` takes one hypothesis here: absent in the two-argument form), `Finset.sum_mul_sq_le_sq_mul_sq`, `Finset.exists_mem_eq_sup`, `Finset.sup'_le`, `Finset.sum_eq_single`, `List.getD_eq_getElem`, `List.getD_append`, `List.getD_append_right`, `List.getElem_rotate`, `List.length_eq_one_iff`, `List.mem_iff_getElem`, `List.mem_ofFn`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.submatrix_submatrix`, `Matrix.submatrix_one_equiv`, `Matrix.submatrix_sub`, `Matrix.submatrix_smul`, `Matrix.conjTranspose_kronecker`, `Matrix.IsHermitian.submatrix`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_le_rpow`, `div_le_div_of_nonneg_left`, `Nat.add_mod_right`, `Nat.mod_eq_of_lt`, `pow_le_pow_left₀`, `one_le_pow₀`, `pow_le_one₀`.

## (d) Open issues and paper-delta candidates — Tue Oct 13 07:04:38 UTC 2026
- No target is open. Merge notes: the branch adds to `RBM3D.lean` two import lines (`RBM3D.BA.GridDriftBA`, `RBM3D.BA.GridGoodBA`) after `import RBM3D.Graph.BAExp14a2` (the last import at the base) and edits one comment line of `Test/Axioms.lean:237`; `main` moved after the base, so expect a textual union in `RBM3D.lean`.
- **T2492a (paper-delta candidate):** the BA initial membership `H_0 = g₀ Ψ ∈ GoodSetNg` holds eventually in `n`, with a (D4) level `C₀ = k (1 + 𝔡⁻²)^{2k}` depending on `(𝔡, k)` only (band: `Γ² Λ >= k (1 + g²)^{2k}`, `zero_mem_goodSetN_of_levels`); the far clauses need Combes-Thomas decay of `M^{(B)}` past a threshold (`baGoodSetNg_init`).
- **T2492b (paper-delta candidate):** the BA drift classes `KLoop`, `KTwo` hold only past the WO window (`BAflow_lam0_window`); `Expand`, `KLink`, `UStep`, the row sums and the walk class hold at every `n`; `baGridDrift_ev` and `baGridDrift_envelope` take the drift eventually.
- **T2492c (observation on the check, not a paper delta):** in `docs/tickets/checks/T2492-check.lean:309-313`, the shape of `baGridGood_of` writes `STEKDecaygL (Sizes.seqP (sz.withLam 0)) ...`, which elaborates with `sz := sz.withLam 0` (coupling `0`; `STEKDecaygL` reads `sz.lam`, `Chain/Step34Gen.lean:516-518`). The Lean text uses `(sz := sz)`, the form of `baEtermDecaygL` and of `gridGoodNgL_of`'s `hEK`; with that one change the shape is accepted (`shape_check_fixed.lean`).
- `baGoodSetNg_init` keeps the pin's unused binder `0 < ε`. `T2491` (U3s2) may publish the generic eventual envelope; `GridGoodBA_envelope_ev` is then redundant.
- Registry: one comment line of `Test/Axioms.lean`; no line added or removed; the full `lake build` runs `#assert_rbm_axioms` (b2).

## Repair (audit round 1) — Tue Oct 13 07:12:47 UTC 2026
Repairer model: claude-opus-5-5. Items 1-3 of "Required for resubmission" in `T2492-audit.md`; nothing else changed.
```
$ git log --oneline -1            # branch t/T2492
9f0a3641 T2492: repair (audit round 1): discharge STKboundgL/STKwardgL in the target 8 and 9 instances by inst_BAKbound, baKward_holds
$ git diff 27b930f0 9f0a3641 --stat
 RBM3D/BA/GridGoodBA.lean | 17 ++++++++---------
$ git diff 27b930f0 9f0a3641 -U0 | grep '^[+-]' | grep -v '^+++\|^---' | grep -v '^.`(s, t\|^.stays\|^.`STKbound\|^./-- '
-example (hKb : STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)))
-    (hKw : STKwardgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)))
-    (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10))
+example (hLK : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 10))
-    (fun n => (t0_sz0 n).trans' (by norm_num)) trivial hKb hKw hLK
+    (fun n => (t0_sz0 n).trans' (by norm_num)) trivial inst_BAKbound
+    (baKward_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0) hLK
-example (hKb : STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0))) :=
-  baGridDrift_envelope sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 inst_loopForm hKb 2 le_rfl 1 one_pos
+example :=
+  baGridDrift_envelope sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 inst_loopForm inst_BAKbound 2 le_rfl 1 one_pos
$ lake build RBM3D.BA.GridGoodBA 2>&1 | tail -1 ; lake build RBM3D.BA.GridGoodBA 2>&1 | grep -c error
Build completed successfully (4109 jobs).
0
$ lake build 2>&1 | grep -A2 "All within" ; lake build 2>&1 | tail -1     # full library, branch root imports
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
Build completed successfully (4355 jobs).
$ wc -l RBM3D/BA/GridGoodBA.lean      # stop line 2,000
    1330 RBM3D/BA/GridGoodBA.lean
```
Hypotheses left in the instances of targets 8-10: `STLKgL`, `STStep2ConclgL` (target 8), `hQ` (target 10). Lines (b6) and (b8) and the section 5 docstring (`GridGoodBA.lean:1260-1261`) now say so. No statement and no public declaration changed (only `example`s and one docstring), so (b3)-(b5) stand.
