Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 22:36:16 UTC 2026

Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3 = 2^21 (n+1)^18`),
`(𝔠, 𝔡) = (1/6, 1/10)`, `k = 1`, `τ_U = 1/60`. Sources read: `PinsK:149-275`, `PinsC2:60-130`, `Pins:195-330`, `GreenCorr:690-870`,
`Step1Band:640-1141`, `UnivMain:505-560`, `GUETranslation:55-110, 700-800`, `Step1Cond:290-380`, `BA/UNPins:55-80, 195-306`, `PinsDens:55-65, 205-240`.

### (i) Exponent table  (`N = N_n`; all inequalities exact, from the script below)

| quantity | value / definition | constraint (source) | slack at instance |
|---|---|---|---|
| `𝔠𝔡` | `1/60` | `< 1/2` (`un_admissible_cd_lt_half`, `Step1Good:234`) | `1/2 - 1/60` |
| `τ_U` (Step 1, target 4) | `1/60` | `0 < τ_U ≤ 𝔠𝔡` (premise of `UNStep1GoodC''`, `PinsC2:94`; `τ_U < 1`, and `< 8/11` for the `N^{-3τ/8}` term, follow from `𝔠𝔡 < 1/2`) | `0` (boundary, allowed: `≤`) |
| `t*` | `N^{-1+τ_U} = N^{-59/60}`; flow time `1 - e^{-t*} ≤ t*` | `t* ≤ 1`; `1-e^{-x} ≥ x/2` for `x ≤ 1` (`un_L32_arith`) | `t*_0 = 6.08e-7` |
| `σ` | `min(τ/4, (1-τ)/3) = 1/240` | `σ > 0` (`UNL32` premise `0 < δ, σ`) | `(1-τ)/3 - τ/4 = 59/180 - 1/240` |
| `g = N^{-1+τ/4}`, `G = N^{-σ}`, `q = 1/2` | `N^{-239/240}`, `N^{-1/240}`, `E = 0` | `N^σ/N ≤ g` iff `σ ≤ τ/4`; `g ≤ N^{-σ}` iff `σ ≤ 1 - τ/4`; `g N^σ ≤ t`; `t ≤ N^{-σ}G² = N^{-3σ}` iff `σ ≤ (1-τ)/3`; `\|E\| ≤ qG` | exponents: `0`, `119/120`, `0`, `233/240`, `E=0` |
| `N^{τ/2} ≥ 2` | `N^{1/120} ≥ 2` | needed for `g N^σ ≤ N^{-1+τ/2} ≤ N^{-1+τ}/2 ≤ t` (`Pins:329-346`); the only non-exponent threshold | holds from `n ≥ 45` (`N ≥ 2^120`); only eventual conclusions use it |
| `UNL32` (external) | [32] Thm 2.2, GUE, unit density | premises are exactly the six rows above plus `IsRegular32`, `IsFreeConv32`, density limit; involve only `N, τ` | see limit computation below |
| good event, bad prob. | `≤ N^{-D}`, `D = k+1 = 2`, then `≤ N^{-1}` | `D ≥ 1`; final error `K0/N`, `K0 = 2·sup\|O\|` (`Step1Band:1036`); `N ≥ 27` for `d ≥ 3` | `N_0 = 2^21 ≫ 27`; `N^{-2} ≤ N^{-1}` |
| `CV₀`, `CV₀+1` (regularity) | `CV₀ = 1`: `\|λ_i(ouInit) - E\| ≤ \|μ\| + \|H\| + \|E\| ≤ N^{CV₀+1}` | `UNNormBound` (`≤ N^{CV₀}`) and `UNMeanBound` (`≤ N^{CV₀}`) together; `N ≥ 27` gives `2N^{CV₀} + \|E\| ≤ N^{CV₀+1}` eventually; `c, C` come from the merged `step1GoodC''` | `N^{CV₀}(N-2) ≥ 25 N^{CV₀}` |
| `UNMeanBound` (BA) | `‖λ_nΨ‖ ≤ 2d·lam_n` (row sum `2d = 6`, `L ≥ 3`) | `lam_n ≤ 𝔡⁻¹ = 10` (WO), `2d𝔡⁻¹ = 60 ≤ N^{CV₀}` (`unMeanBound_ba`, `UNPins:285`) | `CV₀=1`: `60 ≤ 2^21`; `2d·lam_0 = 0.09375` |
| density (`UNDens'`) | `msc`, `E = 0`, `ρ = ρ_sc(0) = 1/π`, `δ = 1/4` | `c = 9/100, K = 1, Lp = 62` at `δ = 1/2` (`un_dens'_msc_zero`), `UNDens'.mono` to `1/4`; range `[c/π, C/π] ∋ 1/π` | `δ: 1/2 → 1/4` |
| GreenCorr `τ₀` | `c'/(2(Cmax+1))`, `Cmax = max(0, max_{nf ≤ k} Cn nf)` (`GreenCorr:810`); `c' = 1/10`, `Cn ≡ 1` ⇒ `1/40` | `τ_U ≤ τ₀`; `Cmax·τ_U ≤ c'/2` so `N^{-c'+Cmax τ_U}` decays | `1/40 - 1/60 = 1/120`; `c' - Cmax τ_U = 1/12 ≥ c'/2 = 1/20` |
| GreenCorr error | `K (N^{-c'+Cτ_U} + N^{-τ_U/2})`, `K` independent of `n` and of `r_n ∈ [a,b]` | `K = 2^k Σ\|c_i\|(μa^k ∫\|Oj_i\| + 2 Cs_i mb ca^k)`, `μa = max(1,a⁻¹)`, `ca = max(1,a⁻²)`, `mb = max(1,b)` | dilation `r_n = 1+1/(n+1) ∈ [1,2]`: `a=1, b=2` |
| smoothing `ε₀` | `ε = N^{-τ_U}` | `N^{-τ_U} ≤ mb⁻¹ = 1/2` iff `N ≥ 2^60` | eventual from `n ≥ 4` |
| `E4` window `C₀` | `C₀ = R/a + 1` (support radius `R ≥ 1`) | `UNClaim417C` holds for every `C₀ > 0` | none needed |
| `τ₁` (rows 4b, 5) | `τ₁ = 𝔠𝔡` (band proof `step1Band_row`) | `> 0`; target 5 adds GUE translation at `κ = (2-\|E'\|)/2 > 0`, `\|E'\| < 2` | `E' = 0`: `κ = 1` |
| row 7 `τ₀` | `min(τ', inf'_{nf ≤ k} τ₀(nf))`, `τ'` of `UNGreenCorrC` | positive (finite inf of positives); independent of `τ_U, O` | `min(1/40, ·)`; claim data are pins |

**Target 3 (formulas).** `ouMatC = ouInit + √(1-e^{-t}) X`, `ouInit = μ + e^{-t/2}(H-μ)` (`PinsK:60-93`). With `H₀ := e^{t/2}•ouInit` (real
scalar `> 0`, Hermitian, measurable in `ω₁`): `e^{-t/2}H₀ + √(1-e^{-t})X = ouMatC`, and `λ(H₀) = e^{t/2}λ(ouInit)` (positive scalar),
so `Step1Cond_cond_general` (`Step1Cond:319`) gives the diagonal `e^{-t/2}·e^{t/2}λ(ouInit)_i = λ(ouInit)_i` at time `1-e^{-t}`; the energy shift
(`diag(v) + √s X - E` has the spectrum of `diag(v-E) + √s X`) turns `vOUC` (`= λ(ouInit) - E`) and `kPoint … E` into energy `0`. No exponent enters.
**Target 6.** `ouMatC M n 0 ω = M.H n ω.1 = ouMat M.toUNModel n 0 ω` (`ouMatC_zero`, `ouMat_zero`); the integrand depends on `ω.1` only and
`gueP` is a probability measure. **Target 8.** `min τ₀ τ₁ > 0` and `(univ-main) + (1infyuniv)` add (`un_core_of_rows'`, `PinsDens:220`), no new exponent.

**External-hypothesis limit computation (`UNL32`, TEAM §8 lesson 14).** At `τ=1/60, σ=1/240`: `N^{σ-1} = g` (equal), `g N^σ = N^{-1+1/120}`,
`N^{-1+1/120} ≤ N^{-1+1/60}/2 ≤ t` iff `N^{1/120} ≥ 2` (n ≥ 45); `t ≤ N^{-59/60} ≤ N^{-3/240}`; the `UNL32` conclusion is `Tendsto`, so no threshold
appears when the theorem is applied. `UNGUELocal`, `UNGreenCorrAllC` (premise of target 7, concluded by target 2), `UNClaimAllC`, `UNNormBound`, band
`UNTrLocal` are other gates' pins or conclusion heads: stay hypotheses.

### (ii) Concrete nondegenerate instance

Hypotheses of all targets at once: `d=3`, `sz0` admissible at `(1/6,1/10)` (`size → ∞`, `W ≥ N^{1/6}`, WO), `M` = band model (`mean 0`) and the BA-type model
(`mean = lam_n Ψ ≠ 0`), `m = msc`, `E = E' = 0`, `ρ ≡ ρ_sc(0) = 1/π ≠ 0`, `δ = 1/4`, `k = 1`, `𝒪 = bump` (`bump 0 = 1`), `τ_U = 1/60`, `c' = 1/10`, `Cn ≡ 1`,
`CV₀ = 1`, dilation `r_n = 1+1/(n+1)`, `a=1, b=2`. Command: `cd scratchpad/T2477 && python3 -I inst.py` (exact `Fraction` for exponents, floats for sizes).

```
cd= 1/60 tau<=cd: True cd<1/2: True slack cd-tau= 0
GreenCorr tau0= 1/40 tau<=tau0: True cp-Cmax*tau= 1/12 >= cp/2: True
sigma= 1/240 (tau/4,(1-tau)/3)= 1/240 59/180
N^sigma/N<=g: True | g<=N^-sigma: True | g N^sigma<=N^(-1+tau/2): True | t<=N^-3sigma (t<=N^(-1+tau)): True
slacks: 0 119/120 0 233/240
n=0: L=4 W=32 N=2097152 (~2^21.00) lam=1/64=~1.562e-02
   W>=N^(1/6): True ; W^(-d/2+1/10) <= lam <= 10: True ; N>=27: True ; N=W^3 L^3: True
   t*=N^(-59/60)=6.078e-07; 1-exp(-t*)=6.078e-07; 2d*lam=9.3750e-02 <= N^1: True; 2d/dd=60<=N: True
   N^(tau/2)=1.129 (>=2?), N^-tau=0.785 (<=1/2?)
n=1: L=8 W=1024 N=549755813888 (~2^39.00) lam=1/4096=~2.441e-04
   W>=N^(1/6): True ; W^(-d/2+1/10) <= lam <= 10: True ; N>=27: True ; N=W^3 L^3: True
   t*=N^(-59/60)=2.854e-12; 1-exp(-t*)=2.854e-12; 2d*lam=1.4648e-03 <= N^1: True; 2d/dd=60<=N: True
   N^(tau/2)=1.253 (>=2?), N^-tau=0.637 (<=1/2?)
n=10: L=44 W=5153632 N=11659991713824860234842112 (~2^83.27) lam=1/113379904=~8.820e-09
   W>=N^(1/6): True ; W^(-d/2+1/10) <= lam <= 10: True ; N>=27: True ; N=W^3 L^3: True
   t*=N^(-59/60)=2.244e-25; 1-exp(-t*)=2.244e-25; 2d*lam=5.2919e-08 <= N^1: True; 2d/dd=60<=N: True
   N^(tau/2)=1.618 (>=2?), N^-tau=0.382 (<=1/2?)
first n with N^(tau/2)>=2 : 45
first n with N^-tau<=1/2 (b=2): 4
rhoSC(0)= 0.3183098861837907 =1/pi: True
dilation r_n=1+1/(n+1) in [1,2]: True
UNDens' msc constants c=9/100,K=1,Lp=62 at delta=1/2 -> use delta=1/4 <= 1/2 (mono)
```

Reading of the output. `n = 0, 1, 10` give `N = 2^21, 2^39, 2^83.27` (all nonzero, `≥ 27`), `t*_n = 6.1e-7, 2.9e-12, 2.2e-25`, `2d·lam_n = 0.094, 1.5e-3, 5.3e-8 ≤ N`
(`UNMeanBound` at `CV₀ = 1`, also `60 ≤ N`). The instance is asymptotic (conclusions are `Tendsto`): thresholds on the conclusion side are `n ≥ 4` (`N^{-τ_U} ≤ 1/2`)
and `n ≥ 45` (`N^{τ/2} ≥ 2`); the merged `step1GoodC''` has its own eventual thresholds (not recomputed here).

### Verdicts

- Target 1 `unGreenCorrC`, 2 `greenCorrAllC`: PASS (`τ₀ = c'/(2(Cmax+1))` independent of `n`, `r`, model; `K` uniform; a priori input read at `ouMatC M n 0 = M.H`).
- Target 3 `step1Band_integral_ouPC`: PASS (identity, formulas above).
- Targets 4, 5 `step1BandC''`, `step1Band_rowC''`, `un_infty1RowC''`: PASS (premises of `step1GoodC''` exactly `UNDens'`, `UNTrLocalInit'`, `UNNormBound`, `UNMeanBound`; `τ_U ≤ 𝔠𝔡` is the only exponent constraint, slack `0` at `τ_U = 𝔠𝔡` is allowed).
- Targets 6, 7, 8 `univMain_transferC`, `univMainRowC`, `unCoreC''_holds`: PASS.
- Overall: PASS. Items (iii)-(viii) of the ticket's preflight list (cones, read-outside list, generalisation table, premise scan, line predictions) are outside this section's two-part scope and are not covered here.

## (a′) Preflight corrections — Mon Oct 12 23:03:54 UTC 2026

No mistake found in (a) (items (i)–(ii)). Scope: (a) states that items (iii)–(viii) of the ticket's preflight list were not covered by 1a; stage 1b produced them in (b)1–(b)5. The in-file instances use `c' = 1`, `C_n ≡ 1` (as the merged band instances, `τ₀ = 1/4`), (a) used `c' = 1/10`; both satisfy (a)(i); no verdict changes.

## (b) Script output (stage 1b, Mon Oct 12 23:03:54 UTC 2026)

```
$ git log --oneline eaa247c4..t/T2477 ; git diff --name-only main...t/T2477
2b1c9956 registry: remove UNGreenCorrC, UNGreenCorrAllC, UNCoreC''   | 8a4ce438 UnivMain | 0b582c2d Step1Band | 450e69f6 GreenCorr
RBM3D/Test/Axioms.lean  RBM3D/Universality/{GreenCorr,Step1Band,UnivMain}.lean   (PinsK/PinsC2/Pins/GUETranslation/Step1Cond/Step1Good/BA/Main: no diff; RBM3D.lean unchanged)
```
**(b)1 line counts** (`git show main:F | wc -l` / `git show t/T2477:F | wc -l`)
```
GreenCorr 1004 -> 1238 (+234; census +130)   Step1Band 1240 -> 1533 (+293; census +300)
UnivMain   690 ->  905 (+215; census +170)   PinsDens   702 ->  702 (0; no edit)
landed +742 < 2.6 x 600 = 1560; each file < 1800 and < 2000; Step1BandC reserve not created
```
**(b)2 cones** (`cones.py`: reverse import cone over RBM3D/**/*.lean; forward closure by `closure.py`); before = after except line counts
```
GreenCorr: reverse_cone=4  LWExpCert=0  BandTerminal=True | Step1Band: 5, 0, True | UnivMain: 3, 0, True | PinsDens: 15, 0, True
diff(before,after) ignoring line counts: identical.   git diff main...t/T2477 | grep '^[+-]import':  +PinsK (GreenCorr)  +PinsC2 (Step1Band)  +PinsC2 (UnivMain)
forward closure main -> branch: GreenCorr 44 -> 45 (+PinsK), Step1Band 51 -> 52 (+PinsC2), UnivMain 81 -> 82 (+PinsC2); removed: none; acyclic (full build)
```
**(b)3 signature diff (GMN-C2)** `for f: git show {main,t/T2477}:RBM3D/Universality/$f.lean | python3 -I sigs2.py`, then `diff`
```python
import re, sys
S = re.compile(r'((noncomputable|protected|nonrec|partial|unsafe) |@\[[^\]]*\] ?)*(theorem|lemma|def|abbrev|structure|instance)\b')
L = sys.stdin.read().split('\n')
for i, l in enumerate(L):
    if l[:1].strip() and S.match(l) and not l.startswith('private'):
        t = '\n'.join(L[i:i + 80]); d = 0; k = 0
        while k < len(t):
            d += (t[k] in '([{⟨') - (t[k] in ')]}⟩')
            if d == 0 and (t.startswith(':=', k) or re.match(r' where\b', t[k:k + 7])): break
            k += 1
        print(' '.join(t[:k].split()))
```
```
GreenCorr: decls 8 -> 14, removed_or_changed=0, added=6 | Step1Band: 16 -> 23, 0, 7 | UnivMain: 15 -> 26, 0, 11 | PinsDens: 31 -> 31, 0, 0
read-outside list of the ticket (25 names: greenCorrAll, univMainRow, unClaimRow(k), 6 Step1Band, 15 PinsDens): statement text identical on main and branch: 25/25
added = the 9 targets + 15 instances (names in (b)8); private helpers are not in the diff
```
**(b)4 statement diff against `T2477_*`** (`branchcheck.lean` = the check file's Part 1-2 + examples, `lake env lean`, exit 0, 0 errors)
```
example : T2477_GreenCorrC := @unGreenCorrC          example : T2477_GreenCorrAllC := greenCorrAllC
example : T2477_integral_ouPC := @step1Band_integral_ouPC   example : T2477_Step1BandC := step1BandC''
example : T2477_Step1BandRowC := step1Band_rowC''       example : T2477_Infty1RowC := un_infty1RowC''
example : T2477_univMain_transferC := @univMain_transferC   example : T2477_UnivMainRowC := univMainRowC
example : T2477_CoreC := unCoreC''_holds                 -- all 9 compile: no binder-implicitness or premise difference to report
example : <S5 premises> -> ∀ d, RBM.BA.BAEnd_BUnivL d := fun h32 hGL => baBUniv_of_rows unCoreC''_holds h32 hGL greenCorrAllC   -- S5 (abridged), compiles
example : UNGreenCorrAll := greenCorrAllC.toAll   -- band recovery of E4, compiles
```
**(b)5 generalisation table** (main file:line -> branch file:line; no private deleted; `grep -c "open private"` over the 4 files = 0)
```
GreenCorr gcc_quantitative 701->756, gcc_tendsto 820->878: (M : UNModel sz) -> carrier (P : ∀ n, Measure _) [∀ n, IsProbabilityMeasure (P n)]
  (A : ∀ n, ℝ -> _ -> Matrix _ _ ℂ) (hAm : Measurable (A n t)) (hAh : Hermitian); h417 : GreenCorr_Claim417 sz P A E ..; hap : GreenCorr_Apriori sz P A E
  band callers unGreenCorr :925, instance_greenCorrAll_tauU :1050: (ouP M) (ouMat M) (measurable_ouMat M) (ouMat_isHermitian M); C caller unGreenCorrC :945
  new private: GreenCorr_Claim417 705, GreenCorr_Apriori 718, GreenCorr_measurable_ouMatC 728, GreenCorr_apriori_C 743, GreenCorr_{blk0,blk32,ofs_eq,psiI_entry,baC,baC_mean_ne} (instances)
Step1Band Step1Band_F 656->802, _good 703->871, _core 719->888: (M) (τs E₀)/(E) -> (vf : ∀ n, SeqΩ -> Idx -> ℝ) (τs); E dropped from _good/_core/_F
  Step1Band_uniform 959->1129: (M) -> (vf) (μ) [IsProbabilityMeasure μ];  Step1Band_measurable_F 663->834: (M τs E₀) -> (vf τs) (hv : Measurable (vf n))
  step1Band 1006->1284 body -> new Step1Band_assemble 1178 (vf, hvm, μ, Aflow, hcond); step1Band = short wrapper at vf = vOU, Aflow = ouMat functional, hcond = step1Band_integral_ouP
  new private: Step1Band_measurable_vOU 810, _vOUC 819, _eigenvalues_congr 667, _eigenvalues_smul 676, _condModel 737; step1BandC'' 1329, step1Band_rowC'' 1356 (vf = vOUC)
UnivMain: no band private changed (univMainRow untouched); new private UnivMain_eigenvalues_congr 568
```
**(b)6 axioms** (`#print axioms`; before = worktree at `eaa247c4`, after = branch)
```
before: 'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.Endpoints.bUniv_holds' ... [propext, Classical.choice, Quot.sound]
after : 'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]   'RBM.Endpoints.bUniv_holds' ... [propext, Classical.choice, Quot.sound]
new public declarations (24: 9 targets + 15 instances, names from the diff): grep -c "depends on axioms: [propext, Classical.choice, Quot.sound]" newaxioms.out = 24 of 24; no sorry/admit/axiom/native_decide in '+' lines of git diff main...t/T2477
```
**(b)7 registry and scan** (`git diff main...t/T2477 -- RBM3D/Test/Axioms.lean`: 3 deletions = lines 175, 176, 182 of main; no line added)
```
-   RBM.Univ.UNGreenCorrC, -- ... (T2187, UN-01b: owed; owner BA-N3 ..)     -   RBM.Univ.UNGreenCorrAllC, -- ...     -   RBM.Univ.UNCoreC'', -- ...
full `lake build` (branch): axiom audit: 14089 theorems, 4452 definitions, 0 axioms in `RBM`;  premises found by scanning: 130 (borrowed 1, owed 64, structural 45, refuted 6, superseded 14); Build completed successfully (4316 jobs); exit=0 (2:48.73)
scan.lean (scanPremises on the built env): UNGreenCorrC, UNGreenCorrAllC, UNCoreC'': in scan result = false; in registry = false.  Prop-def binders of the 9 new theorems: UNL32, UNNormBound (scanned unproved, registered);
  UNMeanBound, UNTrLocalInit', UNDens', UNDens, UNTrLocal, Admissible (registered); IsTestFun, UNGUELocal, UNClaimAllC, UNGreenCorrAllC (concluded by merged/new theorems, not registered)
```
**(b)8 builds, instances, name clashes**
```
$ lake build RBM3D.Universality.GreenCorr RBM3D.Universality.Step1Band RBM3D.Universality.UnivMain | tail -n 1   ->  Build completed successfully (3411 jobs).  (no warnings in the three files)
instances (all compiled, in the same files; d = 3, sz0 with sz0.size 0 = 2097152 = 2^21, (𝔠,𝔡) = (1/6,1/10), k = 1, bump 0 = 1):
 T1/T2 GreenCorr: GreenCorrCheck.instance_unGreenCorrC_band, instance_unGreenCorrC_baC (private GreenCorr_baC: mean λΨ ≠ 0 proved; r_n = 1+1/(n+1) ∈ [1,2]), instance_greenCorrAllC_band, instance_greenCorrAllC_baC
 T3 Step1BandInst: inst_step1Band_integral_ouPC (∃ M nonzero mean, flow ≠ ouMat), inst_step1Band_integral_ouPC_band;  T4a inst_step1BandC''_band;  T4b inst_step1Band_rowC''_band  (τ_U = 1/60 = 𝔠𝔡)
 T5 UnivMainInst: inst_un_infty1RowC''_band_zero (E' = 0), _band_one (E' = 1, ρ_sc(0)/ρ_sc(1) ≠ 1);  T6 inst_univMain_transferC_band, _nonzero_mean;  T7 inst_univMainRowC_band_zero, _nonzero_mean;  T8 inst_unCoreC''_holds_band_zero
 discharged: UNDens' (UNDens'.mono, un_dens'_msc_zero), UNTrLocalInit' (unTrLocalInit'_band_zero), UNMeanBound (unMeanBound_toC), UNGreenCorrAllC (greenCorrAllC), Admissible, IsTestFun bump; kept (other gates' pins): UNL32, UNGUELocal, band UNTrLocal at 1/2, UNNormBound, UNClaimAllC
$ clash.sh (git grep -w -F of the 41 new public/private names on main, t/T2475, t/T2476)   ->  refs checked: main t/T2475 t/T2476 ; total hits: 0
```
**Narrative.**
1. GreenCorr: `gcc_quantitative`/`gcc_tendsto` generalised in place over the carrier `(P n, A n t)`; the band `unGreenCorr` and the C-form `unGreenCorrC` are two instantiations of one private proof; the a priori input is read at `ouMatC M n 0 = M.H n = ouMat M.toUNModel n 0` (`GreenCorr_apriori_C`).
2. Step1Band: the body of `step1Band` is now the private `Step1Band_assemble` (generalised once, instantiated twice, ticket note (4)); band `step1Band` keeps its statement and its own good event (`step1Good'`); `step1BandC''` uses `step1GoodC''` (`UNTrLocalInit'`, `UNNormBound`, `UNMeanBound`; `UNTrLocal` is not a premise).
3. Target 3 (vi): neither `open private` nor a copy of `Step1Cond_cond_general`. The public `integral_kPoint_ouMat_cond` is applied to the auxiliary model `Step1Band_condModel` (law `M.μ`, matrix `e^{t*_n/2} • ouInit`, whose OU matrix at `t*_n` is `ouMatC`); the eigenvalue scaling is the exact identity `λ(c • A) = c λ(A)`, `c > 0` (`Step1Band_eigenvalues_smul`: spectral theorem, `charpoly_mul_comm`, sorted root list), so no permutation argument is needed; then `Step1Band_integral_dbm_shift`.
4. UnivMain: targets 5-8 are the band text with `UNInfty1 -> UNInfty1C`, `ouMat -> ouMatC`, `step1Band_row -> step1Band_rowC''`, `UNApriori` at `M.toUNModel`; `GUETranslation_size_tendsto` is replaced by `tendsto_natCast_atTop_iff.1 hA.2.2.1` (as the band `univMainRow`), not copied; `unCoreC''_holds` is the text of `un_core_of_rows'` over targets 5 and 7 (`PinsDens` untouched).
5. Instances: deviation in form from ticket item 9: Step1Band and UnivMain take the nonzero-mean model from the public `UNKInst.inst_ouMatC_ne_ouMat` (PinsK:728; the existential carries the certificate that its flow differs from `ouMat`) instead of a second private copy of `unPinsK_baC`; GreenCorr, where the dilation `r_n` is also exercised, has the private `GreenCorr_baC` with `mean 0 ≠ 0` proved.
6. Scratch smoke test (not committed, `bacheck.lean`, `lake env lean`, no error): `greenCorrAllC 3 le_rfl sz0 _ (UNModelC.ba sz0)` and `unCoreC''_holds` at `UNModelC.ba sz0` with `unMeanBound_ba sz0 hA 1 one_pos`; the auditor's own check (note (5)) is still required.

## (c) Verified Mathlib names (each by `#check`/compile)
`Matrix.charpoly_diagonal`, `Matrix.charpoly_mul_comm`, `Matrix.IsHermitian.{charpoly_eq, roots_charpoly_eq_eigenvalues₀, sort_roots_charpoly_eq_eigenvalues₀, eigenvalues₀_antitone, spectral_theorem}`, `Antitone.sortedGE_ofFn`, `List.mergeSort_of_pairwise`, `List.sortedGE_iff_pairwise`, `List.ofFn_injective`, `Fin.univ_val_map`, `Multiset.map_univ_val_equiv`, `Polynomial.{roots_prod, roots_X_sub_C, X_sub_C_ne_zero}`, `Multiset.bind_singleton`, `Matrix.mem_unitaryGroup_iff{,'}`, `Unitary.conjStarAlgAut_apply`. Verified absent (`grep -rn` over Mathlib: 0 hits): `charpoly_smul`, `eigenvalues_smul`, `perm_ofFn_iff`.

## (d) Open issues and paper-delta candidates
- `T2477a`: the C-form Step 1 and `(univ-main)` (`1_2:566-581`) run on the centred flow `μ + e^{-t/2}(H - μ) + √(1-e^{-t}) H'`; the DBM initial data are `λ(μ + e^{-t*/2}(H - μ))` (`vOUC`), not `e^{-t*/2} λ(H)`; at BA `μ = λΨ`, band `μ = 0`.
- `T2477b`: the Green-function comparison (`1_2:566-581`, "Thm 15.3 in [25]") uses only Claim `(417)` and the a priori bound at `t = 0` along the centred OU path; it holds for every model with a deterministic mean.
- Open: none for targets 1-10. Merge: one at a time with T2476 (union of `Test/Axioms.lean` hunks, then full build and the `band_terminal`/`bUniv_holds` axiom comparison, ticket note (8)).
