Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 17:25:27 UTC 2026

Row b (targets 11-15), `main` dff951fe (T2510 row a dc358686 and T2508 row b dff951fe merged). Targets in mathematics: the T2508 producers `stExpWardIIgL_of`, `stExpIntIIIgL_of`, `stExpIntIVgL_of`, `stExpIntIgL'_of` at the BA tuple `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `gK = BAflowLam0 = sqrt(T0)*lam`, `Ker = BAEKKer`, `Aof kappa = (kappa+1)/kappa`; then `BAStep6R d R` for `R in {STReg5III, STReg5I, STReg5II, STReg5IV}` from them and the merged row-a pins (regime I: the body of `ST_step6_caseI_of_pinsgL` with `st6_caseI_coreg'`, `ExpIntIGen:473`, in the shape of row a's `baStep6RegII_of_pin`).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `c_d` of the T2508 pins (`refine <1/100,..>` at `ExpWardIIGen:302`, `ExpIntEasyGen:329, 345`; `refine <1/(100 d),..>` at `ExpIntIQGen:1165`) | WardII, IntIII, IntIV: `1/100`; IntI': `1/(100 d)` (= 1/300 at d = 3) | `0 < c_d <= 1/100` (`STIngR6gL`); IntI': `d c_d < 1` | `d c_d = 1/100`; `1/100 - 1/(100 d) = 1/150` at d = 3 |
| 2 | `c_d` per regime (target 13/14) = min of the input pins' constants | (iii): `min(c_LKLK, c_IntIII) = 1/100`; (iv): `min(c_DriftLog, c_IntIV) = 1/100`; (ii): `min(c_LKLK, c_IntII, c_WardII) = 1/100`; (i): `min(c_LKLK, c_DriftDecay, c_WardI', c_IniI', c_IntI') = 1/(100 d)` | `0 < c_d <= 1/100`; `STConStInd sz c_d s t` follows from the pins' `c_d` by `st5_conStInd_mono` | (i): `c_d = c_IniI' = c_IntI'` (slack 0 to the two smallest, 1/150 to the rest) |
| 3 | R1 `Aof kappa_m = (kappa+1)/kappa` at `kappa_m = kappa` (`baEKKer_flow` 4th conjunct) | at datum (i) `334.33` | `1 <= Aof`; `g0^2 <= lam^2`; `lam^2 <= Aof g0^2`, i.e. `1/T0 <= (kappa+1)/kappa`, i.e. `T0 >= kappa/(kappa+1)` | datum (i): `1/T0 = 2.917` vs 334.33; sz0: `1.44` vs 3 |
| 4 | `gK = g0 = sqrt(T0) lam` | datum (i) `1.171` | `0 < g0 <= 1/dd` eventually (`BAflow_lam0_window`) | `1.171 <= 10` |
| 5 | `kappa'`, `delta` (`baIniTermGen_cltFlow`; IntI' and IniI') | `min(kappa,1)`, `eps/2` | `kappa' <= Im m`; `N^(-1+delta) <= 1 - T0` eventually | datum (i): `3.16e-5 <= 0.657` |
| 6 | `C_6` (`baStep5KerGen_thDecay`, `exists` after `(kappa, dd)`), `Cs`, `CM` | not values; the adapter swaps the binders to `(dd, kappa)` | `0 < C_6`, depends on `(d, kappa, dd)` only | no value enters an instance |
| 7 | `K_6` (`baB45Gen_facts`) | `1` | `0 < K_6` | n/a |
| 8 | regime windows (the pins' `R`) | (i) `lam^2/L^2 <= 1-t`, `1-s <= lam^2`; (ii) `lam^2/L^3 <= 1-t`, `1-s <= lam^2/L^2`; (iii) `lam^2 <= 1-t`; (iv) `1-s <= lam^2/L^3` | per datum, see (ii) | (i) `0.25 <= 0.9975`, `1 <= 4`; (ii) `0.391 <= 0.9995`, `1 <= 1.5625`; (iii) `2.4e-4 <= 0.4`; (iv) `1 <= 1.333` |
| 9 | `STConStInd` ratio `(1-t)/(1-s)` and threshold | (i) `0.9975`; (ii), (iv) `0.9995`; (iii) `4/5` | `Bctl^c_d <= (1-t)/(1-s) < 1` eventually; `Bctl = W^-3 B_{t,0}`, `Bctl -> 0` | holds for every `n >= 0` at data (i),(ii),(iv); `n >= 2` at (iii) (script) |
| 10 | `t` against `kappa/(kappa+1) <= T0` (datum lemma `Step5CasesBA_datum`) | (i) `t = 1/400`; (ii), (iv) `t = 1/2000` | `t <= kappa/(kappa+1)` | (i) `0.0025 <= 0.00299`; (ii) `0.0005 <= 0.0006`; (iv) `0.0005 <= 0.001` |
| 11 | `d` | all `d` for the pins (the T2508 pins carry `3 <= d ->`), `3 <= d` for the BA inputs `SEforLnBA_Kbound`, `baStep5KerGen_thDecay` | `hd` is introduced before the producer is applied (the pattern of `baExpIniIgL'`) | none needed for 11's WardII, IntIII, IntIV hypotheses (no `hd`) |
| 12 | exponents `3/2` (TL2), `5/2` (LW), `-1/5` (`STExp2UgL`), `-d/2 + dd` (WO) | carried by merged texts | none recomputed in row b | n/a |

Corrections to the ticket (none moves a pin, a row or a stop line; no new mathematics):
- **G1 (targets 11, 12, hypotheses).** The T2508 producers take the family hypotheses at every `d`: `hRep`, `hK1`, `hWI`, `hB45`, `hSum`, `hKer` (WardII, IntIII, IntIV) are `baCltRepg_holds`, `baKsol_oneLoop d`, `baStep5CasesGen_wardIdent d`, `baB45Gen_facts d`, `baEKSumNdecaygL_holds d`, `baEKKer_flow d` (all `d`, no `hd`); `hKer` of IntIII/IntIV is the first three conjuncts of `baEKKer_flow` (4th is the R1 conjunct, used by IntI'). `hKb` of `stExpIntIgL'_of` is unguarded in `d`, `SEforLnBA_Kbound d hd` needs `3 <= d`: supply it after `intro hd` (as `baExpIniIgL'`).
- **G2 (target 12).** `hTh` is `forall dd>0, forall kappa>0, exists C_6 ...` and `baStep5KerGen_thDecay d hd kappa dd` is `exists C_6` after `(kappa, dd)`: the adapter is `fun dd hdd kappa hkappa => baStep5KerGen_thDecay d hd kappa dd hkappa hdd` (row-22 order adapter, decision (7)); both state `Step5KerGen_ThDecay (baFMz sz z) (BAflowLam0 sz z) dd^-1 C_6`.
- **G3 (target 13).** Regime (i) at BA reads TL1, TL2 on `[s,t]` from the `Concl` slot of `BAStep6R` for (a) the LW bound (`Step6BridgeBA_LW`, private, all inputs as in regime (ii) of row a) and (b) `hAvgU = baExpAvgUgL_of_tl1`; `hHi = st6_hi_of_reg5I` (`lam^2/L^d <= lam^2/L^2 <= 1-t`); `hward`: the WardI' pin conclusion `STExpAvgUgL -> STExpWardIConclgL'`; `hini`: the IniI' pin; `hint`: the IntI' pin (premise shape = `st6_caseI_coreg'`'s `hint`, `ExpIntIGen:480-481`); `hDuQ = st6_duhEqQ_of_ping (baExpDuhamelQgL d)`. No `STImproveExpAvergL`, no every-`n` `hK1`, no `LWtermEXPG` is needed.
- **G4 (target 15, instances).** Row b reads row a's private data by `open private ... from RBM3D.BA.Step6PinsBA` (`Step6PinsBA_szI/zI/datI/regI`, `_szII/..`, `_szIV/..`, `_prem`, `_applyD`, `_con0`, `_reg3`, `_tT0`, `_TL`) and `Step6BridgeBA_LW`; `SEforLnBA_Kbound` by its own `open private`. No text is copied; the ticket's import list stands (`Step5CasesBA` is read transitively).

### (ii) One concrete nondegenerate instance

`d = 3`. Data of row a (a'): regime (i) `(L, W0, lam, kappa, s, t) = (4, 25, 2, 3/1000, 0, 1/400)`, (ii) `(4, 25, 5, 3/5000, 0, 1/2000)`, (iv) `(3, 40, 6, 1/1000, 0, 1/2000)`, each `w = (5003/5000) i`, `(eps, c, dd) = (1/2, 1/9, 1/10)`, `W_n = n + W0`, constant `L`, `lam`; regime (iii) `(sz0, zSeq, flow_sz0)`, `(kappa, eps, c, dd) = (1/2, 1/10, 1/6, 1/10)`, `s = 1/2`, `t = 3/5`. Targets: 11 WardII at (ii), IntIII at (iii), IntIV at (iv); 12 IntI' at (i), `c_d = 1/300`; 13, 14 `baStep6RegI/II/III/IV_holds` at (i), (ii), (iii), (iv). Binders left (other gates' owed pins): the seven `STIngR6gL` carrier premises (`Step6PinsBA_prem`), TL1, TL2 at every `u in [s,t]`, and the mollifier premises of `STExpIntQConclgL'` (`STMollifierProps`, `STExpDuhEqQgL`, `F`, `PrecL`); every deterministic hypothesis (flow, `0 <= s < t <= T0`, regime, `(con_st_ind)` at every `c_d > 0`, R1, the T2508 family rows) is discharged at the numbers.

```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2510b/inst.py   # Fourier spectrum of Psi^(B) on Z_L^3: m_w = L^-3 tr(g Psi - w)^-1, T0 = Im m / Im w, Bctl = W^-3((lam^2+|1-t|)^-1 + (L^3|1-t|)^-1)
pin constants (d=3): LKLK, DriftDecay, WardI', WardII, IntII, IntIII, IntIV, DriftLog = 1/100; IniI', IntI' = 1/(100d) = 0.0033333333333333335
regime (i) c_d = min(1/100,1/100,1/100,1/300,1/300) = 0.0033333333333333335  <= 1/100: True ; d*c_IntI' = 0.01 < 1
-- regime (i)  baStep6RegI_holds, baExpIntIgL': (L,W0,lam,kappa,s,t)=(4,25,2,0.003,0,0.0025), (eps,c,dd)=(1/2,1/9,1/10), n=0, N0=1000000
   flow: Im m_w lower bound Im w/(|w|^2+lam^2 L^3) = 0.00389 >= kappa=0.003: True; Im m=0.34300; N0^(-1+eps)=0.001 <= Im z=0.65760 <= 1; W0=25 >= N0^c=4.642; WO: W0^(-3/2+dd)=0.0110 <= lam=2 <= 10
   t=0.0025 <= kappa/(kappa+1)=0.00299 <= T0=0.34280; 1-T0=0.6572 >= N0^(-1+eps/2)=3.16e-05 (IniTerm CltFlow, delta=eps/2, kappa'=min(kappa,1)=0.003)
   R1 (gK=g0=sqrt(T0)*lam=1.17098): 0<g0<=10: True; g0^2=1.3712 <= lam^2=4; lam^2/g0^2 = 1/T0 = 2.9172 <= (kappa+1)/kappa = 334.33
   STReg5I: lam^2/L^2=0.25 <= 1-t=0.9975, 1-s=1 <= lam^2=4  (STDriftHi: lam^2/L^3=0.0625 <= 1-t)
   (con_st_ind) c_d=0.00333333: Bctl^c_d <= (1-t)/(1-s)=0.99750 for all n>= 0 (n<400); Bctl(n=0)^c_d=0.96339
-- regime (ii) baStep6RegII_holds, baExpWardIIgL: (L,W0,lam,kappa,s,t)=(4,25,5,0.0006,0,0.0005), (eps,c,dd)=(1/2,1/9,1/10), n=0, N0=1000000
   flow: Im m_w lower bound Im w/(|w|^2+lam^2 L^3) = 0.00062 >= kappa=0.0006: True; Im m=0.31746; N0^(-1+eps)=0.001 <= Im z=0.68314 <= 1; W0=25 >= N0^c=4.642; WO: W0^(-3/2+dd)=0.0110 <= lam=5 <= 10
   t=0.0005 <= kappa/(kappa+1)=0.00060 <= T0=0.31727; 1-T0=0.6827 >= N0^(-1+eps/2)=3.16e-05 (IniTerm CltFlow, delta=eps/2, kappa'=min(kappa,1)=0.0006)
   R1 (gK=g0=sqrt(T0)*lam=2.81633): 0<g0<=10: True; g0^2=7.9317 <= lam^2=25; lam^2/g0^2 = 1/T0 = 3.1519 <= (kappa+1)/kappa = 1667.67
   STReg5II: lam^2/L^3=0.39062 <= 1-t=0.9995, 1-s=1 <= lam^2/L^2=1.5625
   (con_st_ind) c_d=0.01: Bctl^c_d <= (1-t)/(1-s)=0.99950 for all n>= 0 (n<400); Bctl(n=0)^c_d=0.88185
-- regime (iv) baStep6RegIV_holds, baExpIntIVgL: (L,W0,lam,kappa,s,t)=(3,40,6,0.001,0,0.0005), (eps,c,dd)=(1/2,1/9,1/10), n=0, N0=1728000
   flow: Im m_w lower bound Im w/(|w|^2+lam^2 L^3) = 0.00103 >= kappa=0.001: True; Im m=0.44580; N0^(-1+eps)=0.000761 <= Im z=0.55480 <= 1; W0=40 >= N0^c=4.932; WO: W0^(-3/2+dd)=0.0057 <= lam=6 <= 10
   t=0.0005 <= kappa/(kappa+1)=0.00100 <= T0=0.44554; 1-T0=0.5545 >= N0^(-1+eps/2)=2.1e-05 (IniTerm CltFlow, delta=eps/2, kappa'=min(kappa,1)=0.001)
   R1 (gK=g0=sqrt(T0)*lam=4.00491): 0<g0<=10: True; g0^2=16.0393 <= lam^2=36; lam^2/g0^2 = 1/T0 = 2.2445 <= (kappa+1)/kappa = 1001.00
   STReg5IV: 1-s=1 <= lam^2/L^3=1.3333
   (con_st_ind) c_d=0.01: Bctl^c_d <= (1-t)/(1-s)=0.99950 for all n>= 0 (n<400); Bctl(n=0)^c_d=0.87097
-- regime (iii) baStep6RegIII_holds, baExpIntIIIgL: sz0 n=0 (L,W,lam)=(4,32,0.015625), (kappa,eps,c,dd)=(1/2,1/10,1/6,1/10), s=1/2,t=3/5, N=2097152
   Im m=0.83249 >= 1/2; N^(-1+eps)=2.04e-06 <= Im z=0.3675 <= 1; W/N^c=2.828; WO: W^(-1.4)=0.00781 <= lam <= 10; t=3/5 <= 2/3 <= T0=0.69374; kappa/(kappa+1)=1/3
   R1: g0=0.01301, 1/T0=1.4415 <= (kappa+1)/kappa=3; STReg5III: lam^2=0.000244 <= 1-t=2/5 for n<400: True
   (con_st_ind) c_d=1/100 (= min(c_LKLK, c_IntIII)): Bctl^c_d <= (1-t)/(1-s)=4/5 for all n>= 2 (n<400)
general d>=3: c_d(IntI')=1/(100d) in (0,1/100], d*c_d=1/100<1: True
```

External hypothesis: none is added. Limits: `Bctl_n^{c_d} -> 0` (`W_n^-3 -> 0`, `W_n = n + W0`), thresholds in the output; the eventual windows `0 < g0 <= 1/dd` (`g0 = 1.171`, `2.816`, `4.005` at (i), (ii), (iv): all `<= 10`; sz0: `0.013`). TL1, TL2 and the seven carrier premises are owed pins, binders. No new constant, exponent or stochastic hypothesis is introduced.

### Verdicts
- Target 11 (`baExpWardIIgL`, `baExpIntIIIgL`, `baExpIntIVgL`): **PASS** (hypotheses G1 hold for all `d`; `c_d = 1/100`).
- Target 12 (`baExpIntIgL'`): **PASS** (G1, G2; `c_d = 1/(100 d)`, `d c_d = 1/100 < 1`).
- Target 13 (`baStep6RegI_of_pins`): **PASS** (G3; `c_d = 1/(100 d)`, R1 `1/T0 = 2.917 <= 334.33` at (i)).
- Target 14 (`baStep6RegIII/I/II/IV_holds`): **PASS** (row a's `baStep6RegIII/IV/II_of_pin` with the target-11 pins; regime I with target 13 and 12).
- Target 15 (instances): **PASS** (data above, every deterministic hypothesis holds; the windows are nonempty).
- No pin, row or stop line moves; (iii) is not a row-b matter. No 1a-audit needed.

### (a′) Preflight corrections — Wed Oct 14 17:39:17 UTC 2026
None that changes a verdict. Observation: (a) G1 lists `hRep, hK1, hWI, hB45, hSum, hKer` jointly for WardII, IntIII, IntIV; per producer (files) WardII takes `hRep, hK1, hWI, hB45` and IntIII/IntIV take `hSum, hKer`; all are discharged as (a) lists.

## (b) Script output — Wed Oct 14 17:39:17 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2510b`, branch `t/T2510b`, HEAD `7dc39fd9`, base `dff951fe`. `S` = scratchpad dir `T2510b/` (scratch scripts, uncommitted).

```
$ lake build RBM3D.BA.Step6BA 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4246 jobs).
$ full build (background, log in S/full_build.log); start/end from `date -u`:
start: Wed Oct 14 17:33:24 UTC 2026
7621:ℹ [4413/4414] Built RBM3D (65s)
7622:info: RBM3D.lean:644:0: axiom audit: 15429 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7915:Build completed successfully (4414 jobs).
7916:exit=0
Wed Oct 14 17:34:32 UTC 2026
errors in full build log (': error'): 0; 'declaration uses' sorry: 0; Step6BA.lean warnings: 9 longLine (module doc lines), 0 other
$ wc -l RBM3D/BA/Step6BA.lean
     240 RBM3D/BA/Step6BA.lean
```

**Axioms** (`lake env lean S/axioms.lean`: `#print axioms` of every new public declaration)
```
'RBM.BA.baExpWardIIgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExpIntIIIgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExpIntIVgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExpIntIgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegI_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegIII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep6RegIV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Target statements** (`python3 -I S/extract.py stmts`, from `RBM3D/BA/Step6BA.lean`)
```
theorem baExpWardIIgL (d : ℕ) :
    STExpWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z)
theorem baExpIntIIIgL (d : ℕ) :
    STExpIntIIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z)
theorem baExpIntIVgL (d : ℕ) :
    STExpIntIVgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z)
theorem baExpIntIgL' (d : ℕ) :
    STExpIntIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z)
theorem baStep6RegI_of_pins (d : ℕ) :
    STExpIntIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAStep6R d STReg5I
theorem baStep6RegIII_holds (d : ℕ) : BAStep6R d STReg5III
theorem baStep6RegI_holds (d : ℕ) : BAStep6R d STReg5I
theorem baStep6RegII_holds (d : ℕ) : BAStep6R d STReg5II
theorem baStep6RegIV_holds (d : ℕ) : BAStep6R d STReg5IV
```

**Compiled nonempty instances** (target 15; `python3 -I S/examples.py`: docstring, header line, then the proof term; every `example` is in section `Inst` of the file, `d = 3`)
```
/-- **Target 11, `baExpWardIIgL`** at the regime-(ii) datum, `s ≡ 0`, `t ≡ 1/2000`: the Ward decomposition, given `(res_ELK_n=1)`. -/
   example (hp : Step6PinsBA_prem Step6PinsBA_szII Step6PinsBA_zII (fun _ => 0) (fun _ => 1 / 2000)) :
   := Step6PinsBA_applyD STReg5II _ (baExpWardIIgL 3) Step6PinsBA_datII Step6PinsBA_regII hp
/-- **Target 11, `baExpIntIIIgL`** at `sz0`, regime (iii), `s ≡ 1/2 < t ≡ 3/5`: the integrated estimate, given the Duhamel identity and the upper drif
   example (hp : Step6PinsBA_prem sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 5)) :
   := Step6PinsBA_apply STReg5III _ (baExpIntIIIgL 3) (by norm_num) (by norm_num) (by norm_num) flow_sz0 (fun _ => by norm_num) (fun _ => by norm_num) Step6PinsBA_tT0 Step6Pin
/-- **Target 11, `baExpIntIVgL`** at the regime-(iv) datum, `s ≡ 0`, `t ≡ 1/2000`. -/
   example (hp : Step6PinsBA_prem Step6PinsBA_szIV Step6PinsBA_zIV (fun _ => 0) (fun _ => 1 / 2000)) :
   := Step6PinsBA_applyD STReg5IV _ (baExpIntIVgL 3) Step6PinsBA_datIV Step6PinsBA_regIV hp
/-- **Target 12, `baExpIntIgL'`** at the regime-(i) datum, `s ≡ 0`, `t ≡ 1/400`, `𝔠_d = 1/300`: both conjuncts (`σ₁ = σ₂`, and the `𝒬`-estimate for a 
   example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400)) :
   := Step6PinsBA_applyD STReg5I _ (baExpIntIgL' 3) Step6PinsBA_datI Step6PinsBA_regI hp
/-- **Target 13, `baStep6RegI_of_pins`** at the regime-(i) datum, with the pin `STExpIntIgL'` of target 12: Step 6 (`STStep6ConclgL`) given the seven 
   example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400))
   := Step6PinsBA_applyD STReg5I _ (baStep6RegI_of_pins 3 (baExpIntIgL' 3)) Step6PinsBA_datI Step6PinsBA_regI hp hTL
/-- **Target 14, `baStep6RegIII_holds`** at `sz0`, `s ≡ 1/2 < t ≡ 3/5`: Step 6 in regime (iii), no owed generic pin left. -/
   example (hp : Step6PinsBA_prem sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 5)) (hTL : Step6PinsBA_TL sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 5)) :
   := Step6PinsBA_apply STReg5III _ (baStep6RegIII_holds 3) (by norm_num) (by norm_num) (by norm_num) flow_sz0 (fun _ => by norm_num) (fun _ => by norm_num) Step6PinsBA_tT0 St
/-- **Target 14, `baStep6RegI_holds`** at the regime-(i) datum, `s ≡ 0`, `t ≡ 1/400`. -/
   example (hp : Step6PinsBA_prem Step6PinsBA_szI Step6PinsBA_zI (fun _ => 0) (fun _ => 1 / 400))
   := Step6PinsBA_applyD STReg5I _ (baStep6RegI_holds 3) Step6PinsBA_datI Step6PinsBA_regI hp hTL
/-- **Target 14, `baStep6RegII_holds`** at the regime-(ii) datum, `s ≡ 0`, `t ≡ 1/2000`. -/
   example (hp : Step6PinsBA_prem Step6PinsBA_szII Step6PinsBA_zII (fun _ => 0) (fun _ => 1 / 2000))
   := Step6PinsBA_applyD STReg5II _ (baStep6RegII_holds 3) Step6PinsBA_datII Step6PinsBA_regII hp hTL
/-- **Target 14, `baStep6RegIV_holds`** at the regime-(iv) datum, `s ≡ 0`, `t ≡ 1/2000`. -/
   example (hp : Step6PinsBA_prem Step6PinsBA_szIV Step6PinsBA_zIV (fun _ => 0) (fun _ => 1 / 2000))
   := Step6PinsBA_applyD STReg5IV _ (baStep6RegIV_holds 3) Step6PinsBA_datIV Step6PinsBA_regIV hp hTL
```

**Statement diff against the pins** (auditor-style scratch file `S/audit_pins.lean`, uncommitted: imports `RBM3D.BA.Step6BA`, the Part 2 texts of `T2508-check.lean:100-247` and `T2510-check.lean:137-216` copied by script, then `example`s)
```
$ lake env lean S/audit_pins.lean; echo exit=$?
exit=0
$ grep -nE "^example" S/audit_pins.lean | cut -c1-165   # the compiled comparisons
252:example : T2510_RowB := fun d => ⟨baStep6RegIII_holds d, baStep6RegI_holds d, baStep6RegII_holds d, baStep6RegIV_holds d⟩
254:example (d : ℕ) : T2510_Step6BA d STReg5III := baStep6RegIII_holds d
255:example (d : ℕ) : T2510_Step6BA d STReg5I := baStep6RegI_holds d
256:example (d : ℕ) : T2510_Step6BA d STReg5II := baStep6RegII_holds d
257:example (d : ℕ) : T2510_Step6BA d STReg5IV := baStep6RegIV_holds d
260:example (d : ℕ) : T2510_RegIIIOfPin d := baStep6RegIII_of_pin d
261:example (d : ℕ) : T2510_RegIVOfPin d := baStep6RegIV_of_pin d
262:example (d : ℕ) : T2510_RegIIOfPin d := baStep6RegII_of_pin d
265:example (d : ℕ) : STExpWardIIgL d (BAlaw d) (BAFl d) (BAmk d) (BAT0 d) := baExpWardIIgL d
266:example (d : ℕ) : STExpIntIIIgL d (BAlaw d) (BAFl d) (BAmk d) (BAT0 d) := baExpIntIIIgL d
267:example (d : ℕ) : STExpIntIVgL d (BAlaw d) (BAFl d) (BAmk d) (BAT0 d) := baExpIntIVgL d
268:example (d : ℕ) : T2508_ExpIntIgL' d (BAlaw d) (BAFl d) (BAmk d) (BAT0 d) := baExpIntIgL' d
272:example (d : ℕ) (hd : 3 ≤ d) : T2508_FamBase d (BAlaw d) (BAFl d) (BAmk d) (BAT0 d) :=
275:example (d : ℕ) : T2508_FamRep d (BAlaw d) (BAFl d) (BAmk d) :=
277:example (d : ℕ) : T2508_FamK1 d (BAFl d) (BAmk d) := by
281:example (d : ℕ) : T2508_FamKer5 d (BAFl d) (BAmk d) (@BAEKKer d) (fun sz z => BAflowLam0 sz z) := Step6BA_Ker3 d
282:example (d : ℕ) : T2508_FamWardIdent d (BAFl d) (BAmk d) := fun sz κ ε 𝔠 𝔡 z hκ hf => baStep5CasesGen_wardIdent d sz κ ε 𝔠 𝔡 z hκ hf
283:example (d : ℕ) : T2508_FamKerR1 d (BAFl d) (BAmk d) (@BAEKKer d) (fun sz z => BAflowLam0 sz z) (fun κ => (κ + 1) / κ) :=
285:example (d : ℕ) (hd : 3 ≤ d) : T2508_FamThDecay d (BAFl d) (BAmk d) (fun sz z => BAflowLam0 sz z) :=
```

**Name clash** (`bash S/clash.sh`)
```
other Lean files under RBM3D/, RBM3D.lean: baExpWardIIgL=0 baExpIntIIIgL=0 baExpIntIVgL=0 baExpIntIgL'=0 baStep6RegI_of_pins=0 baStep6RegIII_holds=0 baStep6RegI_holds=0 baStep6RegII_holds=0 baStep6RegIV_holds=0
docs/tickets/checks: baExpWardIIgL=0 baExpIntIIIgL=0 baExpIntIVgL=0 baExpIntIgL'=0 baStep6RegI_of_pins=0 baStep6RegIII_holds=0 baStep6RegI_holds=0 baStep6RegII_holds=0 baStep6RegIV_holds=0
Test/Axioms.lean lines naming them (owner texts): 226 235 237 239 240 242 
```

**Hypothesis rules** (`bash S/hyp.sh`; code with docstrings and `--` comments removed by `extract.py strip`)
```
C1  (mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM) in Step6BA code: 0
X1-C4 defs, abbrevs, structures in Step6BA code: 0; in the three row files (raw): only `def BAStep6R` (Step6PinsBA)
UBA withLam occurrences in Step6BA code: 28; of the form seqP (X.withLam 0): 28; of the form isProbabilityMeasure_seqP (X.withLam 0): 5
V1L-C1 (STImproveExpAver|st6_expAvgU_of_ping|LWtermEXPG) in Step6BA code: 0
cut grep on row a files (raw, T2508|ExpWardIIGen|ExpIntEasyGen|ExpIntIGen|QopDecayGen|ExpIntIQGen): RBM3D/BA/Step6BridgeBA.lean:0 RBM3D/BA/Step6PinsBA.lean:0 
forbidden tokens sorry|admit|native_decide|axiom in Step6BA code: 0
STNN: STGridRepNgL in Step6BA code (TN-C4): 0
```

**Registry scan** (`lake env lean RBM3D.lean`, which ends in `#assert_rbm_axioms`; before = base files, after = this branch; `diff S/scan_before.log S/scan_after.log`)
```
1c1
< axiom audit: 15420 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 15429 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
122c122
<   RBM.BA.STExpWardIIgL: 4 [no certificate]
---
>   RBM.BA.STExpWardIIgL: 5 [no certificate]
126,127c126,127
<   RBM.BA.STExpIntIIIgL: 4 [no certificate]
<   RBM.BA.STExpIntIVgL: 4 [no certificate]
---
>   RBM.BA.STExpIntIIIgL: 5 [no certificate]
>   RBM.BA.STExpIntIVgL: 5 [no certificate]
before: premises found by scanning: 128 (borrowed 1, owed 55, structural 52, refuted 6, superseded 14).
after:  premises found by scanning: 128 (borrowed 1, owed 55, structural 52, refuted 6, superseded 14).
before: registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded
after:  registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded
lines of the scan output after that name BAStep6R: 0
$ git diff dff951fe..HEAD -U0 -- RBM3D/Test/Axioms.lean | grep "^@@"
@@ -225,2 +225,2 @@ def owedProps : List Name :=
@@ -235 +235 @@ def owedProps : List Name :=
@@ -237 +237 @@ def owedProps : List Name :=
@@ -239,2 +239,2 @@ def owedProps : List Name :=
@@ -242 +242 @@ def owedProps : List Name :=
```

**Diff and ports**
```
$ git diff --stat main...t/T2510b
 RBM3D.lean             |   1 +
 RBM3D/BA/Step6BA.lean  | 240 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |  14 +--
 3 files changed, 248 insertions(+), 7 deletions(-)
$ git diff --name-status main...t/T2510b -- RBM3D/Chain RBM3D/Induction RBM3D/Graph RBM3D/BA   # merged files untouched; the new file only
A	RBM3D/BA/Step6BA.lean
Ports from ../RBM1D, ../RBM2D: none (no file under either was read or copied in this run); RBM1D/RBM2D diff-stat: n/a.
```

**Narrative** (items 1-9 of the ticket's report list; facts from the output above and the files)
- (1) Lines: `Step6BA.lean` 240 (`wc -l` above) against bottom-up 330 (230/560), calibrated 320-420, stop line 550; `wc -l` at the section commits: 157 (`be1ac7ea`, targets 11-14), 240 (`5f2e7b47`, instances). No stop rule hit; no 1a-audit needed.
- (2) Routes. **11**: one call each of `stExpWardIIgL_of`, `stExpIntIIIgL_of`, `stExpIntIVgL_of` (T2508 a) at the BA family rows (table below); IntIII/IntIV take `hKer` as the first three conjuncts of `baEKKer_flow` (private `Step6BA_Ker3`). **12**: `stExpIntIgL'_of` as row a's `baExpIniIgL'`, plus `hTh` = `baStep5KerGen_thDecay` with the binders `(κ, 𝔡)` swapped to `(𝔡, κ)` (decision (7)), `hB45 = baB45Gen_facts`, `hDuQ = baExpDuhamelQgL`; `hKb` after `intro hd`. **13**: the body of `ST_step6_caseI_of_pinsgL''` (`Chain/ExpIntIGen:543`) per flow at BA, core `st6_caseI_coreg'`: `hlk, hdec, hward, hini` = row a's `baExpLKLKHigL, baExpDriftDecaygL, baExpWardIgL', baExpIniIgL'`; `hint` = the hypothesis `STExpIntIgL'`; `hegt` = `st6_EGtHi_of_LWg` with `Step6BridgeBA_LW`; `hAvgU = baExpAvgUgL_of_tl1` (TL1 from the `Concl` slot); `hduh`, `hDuQ` from `baExpDuhamelZgL`, `baExpDuhamelQgL`; `𝔠d = min` of the five pins' constants. **14**: `baStep6RegIII/II/IV_holds` = row a's `baStep6RegIII/II/IV_of_pin` with 11; `baStep6RegI_holds = baStep6RegI_of_pins d (baExpIntIgL' d)`. **15**: nine `example`s on row a's private data, read by `open private` (`Step6PinsBA_szI`, `_datI`, `_regI`, ..., `_apply`, `_applyD`, `_prem`, `_TL`, `_con0`, `_reg3`, `_tT0`); no text copied.
- (3) Statements: the scratch file compiles (exit 0) `T2510_RowB` from the four theorems, the three `T2510_*OfPin` from row a, the three T2508 pins and `T2508_ExpIntIgL'` at the BA tuple, and the seven `T2508_Fam*` rows at BA from merged BA names alone (so `T2508_RowAOf`, `T2508_RowBOf` hold at BA with no hidden hypothesis). Target 13 is not pinned in the check; its text is the one printed above. Two rows need `3 <= d`: `FamBase` (row 17, `SEforLnBA_Kbound`) and `FamThDecay` (`baStep5KerGen_thDecay`); the producers receive them after `intro hd` (preflight G1).
- (4) Family rows as used (BA discharge): `FamBase` = `isProbabilityMeasure_seqP`, `Step2EventsGenTw_baFlow`, `baStep5CasesGen_flowFacts`, `baIniTermGen_cltFlow`, `SEforLnBA_Kbound`; `FamRep` = `baCltRepg_holds` (`g' = 0`, `E = BAflowEs`); `FamK1` = `baKsol_oneLoop` (eventual); `FamWardIdent` = `baStep5CasesGen_wardIdent`; `FamKer5` = `Step6BA_Ker3`; `FamKerR1` = `baEKKer_flow`, `Aof κ = (κ+1)/κ`, `1 <= Aof` by `Step6PinsBA_Aof`; `FamThDecay` = `baStep5KerGen_thDecay`; `B45Gen_Facts` = `baB45Gen_facts`; `STEKSumNdecaygL`, `STEKSumRes2NALgL`, `STEKSumRes2gL` = `baEKSumNdecaygL_holds`, `baEKSumRes2NALgL_holds`, `baEKSumRes2gL_holds`. Constants: `1/100` in the three pins (`ExpWardIIGen:302`, `ExpIntEasyGen:329, 345`), `1/(100 d)` in IntI' (`ExpIntIQGen:1165`), `1/300` at `d = 3`.
- (5) F1: row b adds no twin. The regime-(i) average and the LW bound come from row a's `baExpAvgUgL_of_tl1` and `Step6BridgeBA_LW` (eventual `hK1` by `baKsol_oneLoop`); the V1L-C1 grep is 0, so no `STImproveExpAvergL`, no every-`n` `hK1`, no `LWtermEXPG` in row b.
- (6) Instance data, `d = 3`, `(L, W0, lam, kappa, s, t)`: (i) `(4, 25, 2, 3/1000, 0, 1/400)`, (ii) `(4, 25, 5, 3/5000, 0, 1/2000)`, (iv) `(3, 40, 6, 1/1000, 0, 1/2000)`, each with `(eps, c, dd) = (1/2, 1/9, 1/10)`; (iii) `(sz0, zSeq, flow_sz0)`, `(kappa, eps, c, dd) = (1/2, 1/10, 1/6, 1/10)`, `s = 1/2`, `t = 3/5`. Binders left (other gates' owed pins): the seven stochastic premises `Step6PinsBA_prem`, TL1 and TL2 at every `u in [s,t]` (`Step6PinsBA_TL`), and the premises in the pins' conclusion slots (Duhamel identity, drift bounds, `(res_ELK_n=1)`, mollifier family).
- (7) Registry: owner texts at lines 225-226, 235, 237, 239-240, 242 edited (hunks above); 230 and 241 untouched; no name leaves `owedProps`. Scan: theorems 15420 to 15429; the counts of `STExpWardIIgL`, `STExpIntIIIgL`, `STExpIntIVgL` rise by 1 (the three producers have them in their types); the premises line and the registry line are unchanged; the scan output does not name `BAStep6R`, so it stays out of `structuralProps`. `RBM3D.lean`: one import line after the last import.
- (8) Greps: all in the output above (C1, X1-C4, UBA 28 of 28 occurrences are `seqP (X.withLam 0)`, five of them inside `isProbabilityMeasure_seqP`; V1L-C1, cut grep, forbidden tokens, name clash).
- (9) Paper deltas: none new. Row b reads the primed regime-(i) pins (D725) through `baStep6RegI_of_pins`; F1 is Lean-internal (row a).

### (c) Verified Mathlib names
- `lt_min`, `min_le_left`, `min_le_right` (`#check` in `S/axioms.out`; `lt_min : a < b → a < c → a < min b c`). No other Mathlib name is written in `Step6BA.lean`; none verified absent.

### (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2510ba` not used).
- `baStep6RegI_of_pins` takes the pin `STExpIntIgL'` as a hypothesis of merged type, as target 14's "13 with 12" reads; `baStep6RegI_holds` discharges it with `baExpIntIgL'`. The scan does not list `STExpIntIgL'` as an unproved premise (the build passes).
- The instances keep the owed pins of (6) as binders; no deterministic hypothesis is left. `BAStep6R`'s TL1, TL2 premise is V2a's input (ticket text), not discharged here.
- The build prints 9 longLine style warnings for lines of the module doc of `Step6BA.lean`; no error, no `sorry`.
