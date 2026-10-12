Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 14:36:38 UTC 2026

### (i) Tables (U6 restates band text; every exponent is copied. `:N` = `Induction/Step5Pins.lean` unless named; paper lines read in this stage)

**(i-a) Exponent table**

| exponent / constant | value, band line, paper line | constraint | slack |
|---|---|---|---|
| loss exponent in `STStep5Concl` | `C_d = 0` (`STGdecayW … 0`, :98); `Eq:Gdecay_flow` 1_2:1379-1382 has no `((1-s)/(1-u))^{C_d}` | equals band | exact |
| `STDecayStrongU` | `B_{u,0}^2 e^{-|a1-a2|^{1/2}} + W^{-D}`, index `lam^2 ≤ 1-t` (:69-76); paper 1_2:1384-1386 | verbatim | exact |
| `STEtermsMidConcl` | `A^{-1/3}`, `A^{-1/2}`, `A^{-1/2}`, `A = lam^2 W^d` (`STAI`, Step34Pins:79), `eta^{-1}` (:259-272); paper 3_5:1970 `S5WG+M000`, 3_5:1975 `S5WG+M` | verbatim | exact |
| `STIniTermConcl`, `STDuhamelConcl` | `A^{-1/5}` (:280-308); paper 3_5:1985, 2095 | verbatim | exact |
| `STPfConcl`, `STWardIIConcl` | `STtailTD`, `A^{-1} (N eta)^{-1}` (:202, :340) | verbatim | exact |
| `𝔠d` | `0 < 𝔠d ≤ 1/100` (:85); `STConStInd`: `Bctl(t)^{𝔠d} ≤ (1-t)/(1-s) < 1` eventually (Induction/Defs:168) | `ConStInd` needs `Bctl → 0` | `(ii)`: n0 = 0 at `𝔠d = 1/100` |
| closure, `E^{LK×LK}` (inputs of U4s3, not a U6 constraint) | `rho ≤ (2A)^{𝔠d}`: `rho A^{-1/3} ≤ A^{-1/5}`: `1/100 - 1/3 = -97/300` | `≤ -1/5` | 0.1233 |
| closure, `E^{G~}` (same) | `1/100 - 1/2 = -49/100` | `≤ -1/5` | 0.2900 |
| closure, `dE^M` (same) | `rho^2 A^{-1/4}` (paper 3_5:2043, 2048): `2/100 - 1/4 = -23/100`; band docstring `rho^3`: `-11/50` | `≤ -1/5` | 0.0300 / 0.0200 (`A ≥ 2^{k/100·1/slack}` = 1.59 / 2.83) |
| target 6 constants | `ℓ = L`; `Ck`, `δ₀ > 0` after `κ, 𝔡`; band `δ₀ = κ/2` (`stNewKLKL_holds`, NewKLKL:836-840); generic `κ ≤ Im m` | band at margin `κ' = κ²`: `κ ≤ √(4-E²)/2 ⇒ |E| ≤ 2√(1-κ²) ≤ 2-κ²` (needs `κ ≤ 1`, automatic: `Im m ≤ 1`) | `(2-κ²) - 2√(1-κ²)`, `= 2.51e-5 = κ⁴/4` at `κ = 0.1`; generic `δ₀ = κ²/2` |
| target 7 constants | `Cc` after `κ` only; band `C = (3 e^{(4d+1)/4})²` (TailtoTail:582-586); `((1-s)/(1-t))² W^{-D}`; hyps `0 < lam`, `lam² ≤ 1-t`, `0 ≤ s ≤ t < 1` | `‖m‖ = 1` from `κ > 0`, `κ ≤ Im mE` ⇒ `4-E² > 0` ⇒ `|E| < 2` (`norm_mE`) | `Cc` independent of `κ` |
| `lam ≤ 𝔡⁻¹` (target 6) | `𝔡⁻¹ = 10` | `lam ∈ {1, 5, 1/64}` | ≥ 5 |
| `3 ≤ d` | all pins | `d = 3` | 0 (d=3 sharp) |

**(i-b) Bridge table (iii)** (kinds are predictions from the merged lemmas read; Lean not run)

| band (line) → generic | kind |
|---|---|
| `STDecayStrongU` (:69), `STStep5Concl` (:97), `STLK2` (:143), `STELKLK` (:147) → `…gL` / `STLK2g` / `STELKLKg` | `Iff.rfl` / `rfl` (`Prec sz = PrecL sz (seqP sz)`; `bandFM` fields; `STLM_seqHflow` is `rfl`; `C.S = SB d L lam`) |
| `STEtermsMidConcl` (:259), `STWardIIConcl` (:340), `STPfConcl` (:202) | `Iff.rfl` (`bandFM_STEGt`, `bandFM_STEEk`, `etaT (E n) = C.eta n`) |
| `STIniTermConcl` (:280), `STDuhamelConcl` (:297) | proved, only through `bandStep2_Ugen` (kernel under the `Prec` binder; arguments `STLKM … (seqHflow …) = C.L - C.K` by `rfl`) |
| `STNewKLKL` (:247) ⇒ `STNewKLKLgL'` | band ⇒ generic only: apply band at `(κ², 𝔡)`; domain fact above; `bandStep2_STELKLKM/_STJhatM/_STGMM` are `rfl` at `fun _ => E` |
| `STTailtoTail` (:121) ⇒ `STTailtoTailgL'` | band ⇒ generic only: `Step2Kern_UN_band`, `EKsgn (mE E) σ = fun i => mSigma E (σ i)` by `rfl`, `norm_mE`, `mE_im`, `sz.three_le_L`, `W_pos` |
| `STIngR5` (:82) → `STIngR5gL` | `↔`, proved: `bandFM_STKward` (list vs `Fin k` index, `Carrier_ofFn_ext`); other premises `Iff.rfl`; Steps 3-4 premises are definitionally the inline pair |
| `STStep5R`, `STStep5I-IV`, `STStep5`, `STEtermsMid`, `STWardII`, `STPfStep5` (:101, :453-463, :275, :348, :211) | `STIngR5_iff_gL` with `Iff.rfl`-level `Concl` |
| `STDuhamelI/II`, `STIniTermI/II` (:317-333) | `STIngR5_iff_gL` must take a pointwise `Concl ↔ Concl'` hypothesis (the `Ugen` rows are not defeq); the lemma stated for defeq `Concl` only cannot close these four |

**(i-c) (iv), (v), (vi)**
- (iv) Target 1 names are read as they are (they mention only `sz.L, sz.W, sz.lam`, times). `sz.lam n` enters: regimes `STReg5I/II/Mid/III/IV` (:45-64) and the index subtype `lam² ≤ 1-t` (:72, :205); `Bctl`/`Bparam` and `STAI = lam²W^d`; `STprof` (`tailW … lam`, Step2Defs:75), so targets 4, 6; hypotheses `0 < lam`, `lam ≤ 𝔡⁻¹` (target 6), `0 < lam`, `lam² ≤ 1-t` (target 7); `ellT L lam` in `STGdecayWgL` (merged, Step2Gen:510). In target 7 the kernel sees `g` only through `C.S n` (Step2Gen:189-191: `Step2Kern_Mss * C.S n`), not through `sz.lam`: the generic pin links `sz.lam` and `C.S` by no hypothesis; at `bandFM` they agree (`S = SB d L lam`), at BA the carrier has `S := 1` (BA/FlowPins:327), so `g` vs `g₀` is U5's and U6-BA's question (record for T2459).
- (v) T2457: `docs/queue/T2457.state` = `blocked` (1a-audit RETURN, 1b not started); `RBM3D/Chain/Step34Gen.lean` is absent on `main` (`ls RBM3D/Chain`: Carrier, GridDuhamelGen, LWGen, NewKLKGen, Step2Gen, Step2Kern). So: target 8 writes the Steps 3-4 premises inline (conjuncts 2-3 of `twSteps`, BA/TwistPins:135-138; same text as band `STLmaxU`, `STLKU` at Step34Pins:176-186); **target 11 moves to U4s3** (dispatcher-accepted, H248/§266). D2: `T2457_IngRgL` (check lines 361-370) and `T2458_STIngR5gL` have the same binder order `(d R law Flow mk T0 Concl)` and `Concl : ∀ sz z, (ℕ→ℝ)→(ℕ→ℝ)→Prop`; the premise lists differ (Step 5 adds `STDecay`, `STDecayStrong`, `STStep1Loop`, `LmaxU`, `LKU`), as the band `STIngR` and `STIngR5` differ.
- (vi) Imports `RBM3D.Chain.GridDuhamelGen`, `RBM3D.Induction.Step5Pins` only (no `Step34Gen` while T2457 is unmerged). `FlowFM`, `PrecL`, `STEEg` (Carrier), `Step2Gen_UN`, `STEGtg`, `STELKLKMg`, `STJhatMg`, `STGMMg` (Step2Gen), `bandStep2_Ugen` (GridDuhamelGen) are all reached through these. Reverse cone: empty (new file, only the `RBM3D.lean` import line). Line estimate: not redone (stage-1a rule); ticket stop line 2,000 stands.

### (ii) One concrete nondegenerate instance (d = 3, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6, E = 0)
Data: `szB` (L=4, W_n=n+4, lam=1), `szG` (szB with lam=5), `sz0` (L_n=4(n+1), W_n=(2(n+1))^5, lam_n=(2(n+1))^-6), flows `zB = 1/2 + i/64`, `z0 = 1/2 + i N^{-4/5}` (the merged `Step5Inst` data, Step5Pins:477-490, Step34Pins:710-765, Defs:413). Regimes: (i) and the window `Mid` at `szB`, (s,t)=(49/100,1/2); (ii) `szB`, (1899/2000,19/20); (iii) `sz0`, (0,1/16); (iv) `szG`, (61/100,123/200) (near-1 ratios, so `ConStInd` holds from n=0 at `𝔠d = 1/100`). Targets 6-7 at `E = 0` (`mE = i`, `Im = 1 ≥ κ`), `lam ∈ {1,5,1/64}`, `u ∈ [0,1)`, `0 ≤ s ≤ t < 1`, `lam² ≤ 1-t` (`sz0`, n=0: 1/4096 ≤ 15/16). External/other-gate hypotheses: `STNewKLKL`, `STTailtoTail` are the merged `stNewKLKL_holds d`, `stTailtoTail_holds d` (no premises, NewKLKL:836, TailtoTail:582); the stochastic Steps 1-4 premises of target 8 stay hypotheses (other gates). Limit computation for the one eventual deterministic hypothesis: `Bctl_n(t) = W_n^{-3}(B0)`, `B0 = (lam²+1-t)^{-1} + (L³(1-t))^{-1}`, so `Bctl^{𝔠d} ≤ rho` iff `W ≥ (B0^{𝔠d}/rho)^{1/(3𝔠d)}`; `Bctl → 0`, so it holds for every `𝔠d > 0` eventually; thresholds below (the pin supplies `𝔠d ≤ 1/100`; Lean examples discharge it for every `𝔠d > 0`, as the merged `conStInd_const`).

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2458/inst.py`
```
== (A) deterministic data of targets 8-10, d=3, kappa=eps=dd=1/10, c=1/6, n=0..3000
I   szB s,t= 49/100 1/2 | regime+WO+Bandwidth all n: True | locDomain & t<=lemT(z) all n: True | lemT(z_0)=0.98399
II  szB s,t= 1899/2000 19/20 | regime+WO+Bandwidth all n: True | locDomain & t<=lemT(z) all n: True | lemT(z_0)=0.98399
Mid szB s,t= 49/100 1/2 | regime+WO+Bandwidth all n: True | locDomain & t<=lemT(z) all n: True | lemT(z_0)=0.98399
III sz0 s,t= 0 1/16 | regime+WO+Bandwidth all n: True | locDomain & t<=lemT(z) all n: True | lemT(z_0)=0.99999
IV  szG s,t= 61/100 123/200 | regime+WO+Bandwidth all n: True | locDomain & t<=lemT(z) all n: True | lemT(z_0)=0.98399
== con_st_ind (Bctl(t)^cd <= (1-t)/(1-s) < 1): first n, W=n+4 (szB,szG) / sz0 n=0
cd=1/100: I n0=0 rho=0.9804; II n0=0 rho=0.9901; Mid n0=0 rho=0.9804; III n0=0 rho=0.9375; IV n0=0 rho=0.9872
cd=1/1000: I n0=649 rho=0.9804; II n0=26 rho=0.9901; Mid n0=649 rho=0.9804; III n0=37 rho=0.9375; IV n0=28 rho=0.9872
== (B) targets 6-7: kappa<=Im m, E sweep; Im mE = sqrt(max(0,4-E^2))/2 (Real.sqrt of a negative is 0)
pairs (kappa,E) with kappa<=Im mE: 312040 violations of |E|<=2-kappa^2 or |mE|=1: 0
kappa=0.1: boundary |E|=2sqrt(1-k^2)=1.9899749 <= 2-k^2=1.9900000 slack 2.51e-05 (kappa^4/4=2.5e-05)
E=0: mE=i, Im=1>=0.1; lam=1<=1/dd=10 (szB); lam=5<=10 (szG); lam_0=1/64 (sz0)
kappa>1: Im mE<=1<kappa, hypothesis empty (consistent with margin 2-kappa^2 only used for kappa<=1)
target 7 at sz0 n=0: lam^2=1/4096 <= 1-t=15/16
== (C) exponent closure (rho<=(2A)^cd, cd<=1/100; need rho^k A^-a <= A^-1/5 for large A)
LK x LK A^-1/3                           k=1 exponent k/100-a=-97/300=-0.3233 vs -1/5: slack 0.1233; needs A^slack>=2^(k/100): A>=1.058
G~ A^-1/2                                k=1 exponent k/100-a=-49/100=-0.4900 vs -1/5: slack 0.2900; needs A^slack>=2^(k/100): A>=1.024
dE^M A^-1/4 (rho^2, paper 3_5:2048)      k=2 exponent k/100-a=-23/100=-0.2300 vs -1/5: slack 0.0300; needs A^slack>=2^(k/100): A>=1.587
dE^M A^-1/4 (rho^3, band docstring)      k=3 exponent k/100-a=-11/50=-0.2200 vs -1/5: slack 0.0200; needs A^slack>=2^(k/100): A>=2.828
A=lam^2 W^d at szB n=0: 64; at sz0 n=0: 8
```
(Line `(A)`: regime + `WO` (`W^{-3/2+𝔡} ≤ lam ≤ 𝔡⁻¹`) + `Bandwidth` (`W ≥ N^{1/6}`) + `locDomain` + `t ≤ lemT z`, `lemT z = ‖msc z‖²` computed from the root of `m²+zm+1` of smaller modulus, for n = 0..3000; `N → ∞` is clear for `W_n → ∞`. Case (iii) `lemT(z0) = 0.99999 ≥ 1/16`.)

### Verdicts
- Targets 1-10, 12-15: PASS (statements are band text with `sz`-carrier substitutions; the check file `T2458-check.lean` compiled on `main` 6bdc5a3, exit 0, errors 0, CONTROL H247 (2); exponent rows exact or with the slacks above; instance nonempty).
- Target 11: not written here (T2457 unmerged); moves to U4s3, as the ticket allows.
- Target 7 at BA (check line 462) is a shape, not a target (H248 (3)).
- Required notes for 1b: (1) `STIngR5_iff_gL` must take a pointwise `Concl` iff (four `Ugen` rows); (2) docstrings of generic pins must not contain the grep-13 tokens (`|E|`, `mE`, `‖m‖`, …) or they count as hits; (3) record the `sz.lam` vs `C.S` remark of (iv) for U5.
## (b) Script output and narrative (stage 1b, branch t/T2458, commits a3d9518 ec51d7e 48a7583)
### 1. Layout, cone, size
```
$ date -u; git rev-parse --short HEAD main; git diff --stat main...t/T2458 | tail -1
Mon Oct 12 14:57:35 UTC 2026 / 48a7583 c0ea2d6  1 file changed, 666 insertions(+)
$ git diff main...t/T2458 -- <Induction, BA, Carrier, Step2Gen, Step2Kern, GridDuhamelGen, NewKLKGen> | wc -l; grep -rln "Chain.Step5Gen" RBM3D RBM3D.lean | wc -l; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Chain/Step5Gen.lean; wc -l < RBM3D/Chain/Step5Gen.lean
0 / 0 / 0 / 666
$ grep -n "^import" RBM3D/Chain/Step5Gen.lean
6:import RBM3D.Chain.GridDuhamelGen | 7:import RBM3D.Induction.Step5Pins
```
Layout: additive new file (sections 1-10: conclusions, vocabulary, cases, primed pins 6-7, shape `STIngR5gL`, conclusion bridges, band theorems, pin bridges, instances); `Step5Pins` and every band file untouched (G1). Reverse cone empty: no importer; the hub adds the `RBM3D.lean` import at merge (CLAUDE.md §3 (A) step 4; t/T2453 likewise changed one .lean file). 666 lines against stop line 2000.
### 2. T2457 status and target 11
```
$ head -1 / sed -n 3p docs/queue/T2457.state; git ls-tree --name-only main RBM3D/Chain/
state: held / updated: Mon Oct 12 14:51:34 UTC 2026
Carrier.lean GridDuhamelGen.lean LWGen.lean NewKLKGen.lean Step2Gen.lean Step2Kern.lean 
```
T2457 is not merged and `Chain/Step34Gen.lean` does not exist: target 8 writes the Steps 3-4 premises inline (no `Step34Gen` import); **target 11 is not written and moves to U4s3** (count-neutral; ticket target 11 and §266). D2: `STIngR5gL d R law Flow mk T0 Concl` has the binder order and the `Concl : ∀ sz z, (ℕ → ℝ) → (ℕ → ℝ) → Prop` index of `T2457_IngRgL` ((a) (v)).
### 3. Builds and axioms
```
$ lake build RBM3D.Chain.Step5Gen   # exit 0
Build completed successfully (3778 jobs).
$ lake build with a temporary, uncommitted import line in RBM3D.lean (reverted); exit 0; date -u after it: Mon Oct 12 14:51:02 UTC 2026
info: RBM3D.lean:514:0: axiom audit: 13315 theorems, 4196 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4282 jobs).
$ #print axioms RBM.BA.<name> for the 26 public theorems; same for the 27 `example`s renamed to theorems in a scratch copy; | sed "s/.*axioms: //" | sort | uniq -c
     26 [propext, Classical.choice, Quot.sound]
     27 [propext, Classical.choice, Quot.sound]
$ #assert_rbm_axioms in AssertCheck.lean (Test.Axioms, Step5Gen) > assert.out; AssertCheck2.lean (+ Induction.NewKLKL, Induction.TailtoTail) > assert2.out
$ grep -c "STNewKLKL,\|STTailtoTail,\|Step5Gen\|gL" assert.out assert2.out   # unproved-premise lists
assert.out:2   assert2.out:0     (the premises of targets 6-7 leave the list once the files of stNewKLKL_holds, stTailtoTail_holds are imported)
```
### 4. Statements against the pins `T2458_*` (targets 2-10)
```
$ python3 -I stmtdiff2.py   # check Part 2 vs Step5Gen.lean
identical 22 of 25 (token streams, docstrings/comments removed, prefix T2458_ removed)
STEtermsMidConclgL: differs in 3 hunks; first: check "‖( ( ( sz.W n : ℕ ) : ℂ ) ^ d ) * ∑ x : Zd d ( sz.L n ), ∑ y : Zd d ( " -> file "‖STELKLKg C"
STPfConclgL: differs in 2 hunks; first: check "‖C.L" -> file "STLK2g C"
STIngR5gL: differs in 6 hunks; first: check "LmaxU_inline" -> file "( ∀ k : ℕ, 1 ≤ k → PrecL sz ( law sz ) ( U := fun n => TimeIcc s t n ×"
$ lake env lean EqCheck.lean   # scratch: Part 2 of the check + 26 examples "T2458_X ↔ X := Iff.rfl" + STLK2g = ‖L - K‖ := rfl
exit=0, 0 output lines
```
Change table for U5 (U-C5), every change from the `T2458_*` pins (the three are `Iff.rfl` by EqCheck):
| name | old (check) | new (file) |
|---|---|---|
| `STEtermsMidConclgL` | 1st conjunct: inline `‖W^d Σ_x Σ_y (L-K)(x,a₁) C.S (L-K)(a₀,y)‖` | `‖STELKLKg C n (p.1:ℝ) p.2.1 p.2.2 ω‖` (a def of the same term) |
| `STPfConclgL` | `‖C.L … - C.K …‖` | `STLK2g C n (p.1.1:ℝ) p.1.2.1 p.1.2.2 ω` (a def of the same term) |
| `STIngR5gL` | premises `T2458_LmaxU_inline`, `T2458_LKU_inline` | the two `∀ k, 1 ≤ k → PrecL …` premises inline, same text, no name |
| other 22 pins | prefix `T2458_` | prefix dropped |
### 5. Bridge table (kinds extracted by script from the proof terms of the 26 public theorems)
```
Iff.rfl: bandFM_STDecayStrongU, bandFM_STStep5Concl, bandFM_STEtermsMidConcl, bandFM_STWardIIConcl, bandFM_STPfConcl
rfl: bandFM_STLK2, bandFM_STELKLK
proved: unfold; simp only [bandStep2_Ugen]; exact Iff.rfl: bandFM_STIniTermConcl, bandFM_STDuhamelConcl
band => generic, proved (band pin at margin κ² / Step2Kern_UN_band, norm_mE, mE_im): stNewKLKLgL'_band, stTailtoTailgL'_band
proved (helper, pointwise Concl iff hC): STKward via bandFM_STKward, other premises Iff.rfl: Step5Gen_ingR5_iff_congr
Step5Gen_ingR5_iff_congr + the conclusion bridge of the same row (Iff.rfl for STIngR5_iff_gL): STIngR5_iff_gL, STStep5R_iff_gL, STEtermsMid_iff_gL, STDuhamelI_iff_gL, STIniTermI_iff_gL, STDuhamelII_iff_gL, STIniTermII_iff_gL, STWardII_iff_gL, STPfStep5_iff_gL
STStep5R_iff_gL d <regime>: STStep5I_iff_gL, STStep5II_iff_gL, STStep5III_iff_gL, STStep5IV_iff_gL, STStep5_iff_gL
```
### 6. Target statements (script extract)
```
$ line:name of every public def/theorem of sections 1-9, then the statements of the two band theorems
51:STDecayStrongUgL 62:STStep5ConclgL 68:STLK2g 74:STELKLKg 85:STEtermsMidConclgL 102:STIniTermConclgL 115:STDuhamelConclgL 130:STWardIIConclgL 139:STPfConclgL 151:STNewKLKLAtgL' 164:STNewKLKLgL' 169:STTailtoTailConclgL 178:STTailtoTailgL' 191:STIngR5gL 214:STStep5RgL 226:STStep5IgL 227:STStep5IIgL 228:STStep5IIIgL 229:STStep5IVgL 230:STStep5gL 234:STEtermsMidgL 236:STDuhamelIgL 239:STIniTermIgL 241:STDuhamelIIgL 246:STIniTermIIgL 250:STWardIIgL 252:STPfStep5gL 263:bandFM_STDecayStrongU 266:bandFM_STStep5Concl 269:bandFM_STLK2 272:bandFM_STELKLK 275:bandFM_STEtermsMidConcl 278:bandFM_STWardIIConcl 281:bandFM_STPfConcl 285:bandFM_STIniTermConcl 292:bandFM_STDuhamelConcl 319:stNewKLKLgL'_band 332:stTailtoTailgL'_band 354:Step5Gen_ingR5_iff_congr 376:STIngR5_iff_gL 387:STStep5R_iff_gL 393:STStep5I_iff_gL 398:STStep5II_iff_gL 403:STStep5III_iff_gL 408:STStep5IV_iff_gL 413:STStep5_iff_gL 420:STEtermsMid_iff_gL
319: theorem stNewKLKLgL'_band (d : ℕ) (h : STNewKLKL d) :
320:     STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) := by
332: theorem stTailtoTailgL'_band (d : ℕ) (h : STTailtoTail d) :
333:     STTailtoTailgL' d (fun sz E => bandFM sz E) := by
```
### 7. Greps of targets 12-14
```
$ grep -nE "^(noncomputable )?(private )?(def|abbrev|structure|instance)" RBM3D/Chain/Step5Gen.lean | wc -l   # 12(a) heads
      30   (one is the docstring word "definitionally", line 353)
$ python3 -I scan.py   # 12(a): each def/abbrev body, docstrings removed, for Ring.inverse|Step2Gen_Theta|thetaKer|uKer|Mss|Matrix.of|cycProd: bodies scanned, bodies hit
29 0
$ grep -nE "Ring\.inverse|Step2Gen_Theta|Step2Gen_thetaKer|Step2Gen_uKer|Step2Kern_Mss|ukerMat|cycProd|RBM\.UN|\bUN d|Ugen|EKsgn|PropSpin|Theta d" RBM3D/Chain/Step5Gen.lean   # 12(b): line numbers
284 288 291 295 344 
$ grep -c "Step2Gen_UN" RBM3D/Chain/Step5Gen.lean; grep -nE "(def|theorem|lemma|abbrev) [A-Za-z_']*Ugen" RBM3D/Chain/Step5Gen.lean | wc -l   # 12(c), 12(d)
11          0
$ grep -nE "<13 pattern>" RBM3D/Chain/Step5Gen.lean | awk (hits per line range: generic defs 1-256 | conclusion bridges | band theorems | pin bridges | instances)
<257: 0 | 257-299: 7 | 300-348: 11 | 349-476: 48 | 477+: 61
$ grep -nE "Clt|fFar|cltB|cltX|ExpInv" RBM3D/Chain/Step5Gen.lean | wc -l   # 14
       0
```
12(b): lines 284, 288, 291, 295 are the two bridges that read the older kernel (docstring, `simp only [bandStep2_Ugen]`), line 344 is the proof of `stTailtoTailgL'_band`. 13: no hit in lines 1-256 (all generic definitions). `sz.lam` enters (grep): regime index `lam² ≤ 1-t` lines 54, 142; `STAI = lam² W^d` 89-135; `0 < lam`, `lam ≤ 𝔡⁻¹` 152; `0 < lam`, `lam² ≤ 1-t` 180-181; `STprof`, `STtailTD`; `Step2Gen_UN` sees `S` only as `C.S n` (see (d) 4).

### 8. Compiled nonempty instances (27 `example`s in section 10, `d = 3`; each one axiom-checked in 3)
Data: `szB`, `zB` (case (i) `(7/8,15/16)`, case (ii) `(15/16,31/32)`), `sz0`, `z0`, `(sInst,tInst) = (0,1/16)` of `Step5Inst`; index sets nonempty (`lam_n² ≤ 15/16` at `sz0`). By kind: 11 bridges of targets 2-5 at concrete `(sz, E, s, t)`; 7 re-derivations of `inst_etermsMid`, `_duhamelI`, `_iniTermI`, `_wardII`, `_pfStep5`, `_duhamelII`, `_iniTermII` from the generic wrapped pin through its bridge (that pin is the only hypothesis: another row's); 1 of target 8 (`STIngR5_iff_gL` with `inst_ing5_I`, any band `Concl`); 6 pin bridges of target 9 (`STReg5Mid`, I-IV, general); 2 band-theorem instances, below. `STNewKLKL 3`, `STTailtoTail 3` stay hypotheses (proved in `Induction/NewKLKL`, `Induction/TailtoTail`, not importable here: cycle with U4s1). Discharged: `0 < lam`, `lam ≤ 𝔡⁻¹ = 10`, `κ = 1/10 ≤ Im m(0) = 1`, `H = 0` Hermitian with `‖G_0 - M‖_max = 0 ≤ δ₀`, `0 ≤ s ≤ t < 1`, `lam² = 1/4096 ≤ 1/4 = 1-t`, extremal tensor `A_b = T_{s,D}(|b₁-b₂|)`, and flow, regime, `(con_st_ind)` through `inst_ing5_I`.
```
$ sed -n 622,624p / 635,636p / 645,647p / 658,660p RBM3D/Chain/Step5Gen.lean
622: example (h : STNewKLKL 3) :
623:     ∃ Ck δ₀ : ℝ, 0 < Ck ∧ 0 < δ₀ ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
624:       ‖STELKLKMg Step5Gen_cm0 0 0 Step5Gen_H0 σ a‖ ≤
635:   exact hAt sz0 0 0 0 1 hlam hlam' Step5Gen_im_zero le_rfl one_pos zero_le_one Step5Gen_H0 Matrix.isHermitian_zero
636:     (fun x y => by
645: example (h : STTailtoTail 3) :
646:     ∃ Cc : ℝ, 0 < Cc ∧ ∀ a : Fin 2 → Zd 3 (sz0.L 0),
647:       ‖Step2Gen_UN (bandFM sz0 (fun _ => (0 : ℝ))) 0 ![true, false] (1 / 2 : ℝ) (3 / 4 : ℝ)
658:   exact H sz0 0 0 2 (1 / 2) (3 / 4) hlam Step5Gen_im_zero (by norm_num) (by norm_num) (by norm_num) hlam2
659:     ![true, false] _
660:     (fun b => by rw [Complex.norm_real, Real.norm_of_nonneg (tailTD_nonneg (by norm_num))]) a
```
### 9. Name-clash grep of the 53 new public names
```
$ git grep -h -E "^\s*(noncomputable |private )*(def|theorem|abbrev|lemma|structure|instance) " <ref> -- RBM3D, then each name as a declaration name (script); counts per ref
main@c0ea2d6:0 t/T2454@e949c71:0 t/T2455@b981c85:0 t/T2457@ee3d8a0:0 t/T2449@921369b:0 t/T2452@cbcaf33:0 t/T2450@fd0c76e:0 t/T2456@6bdc5a3:0 t/T2458@48a7583:53
```
0 on main and on the seven sibling branches; 53 on t/T2458 (the sanity count). The private helper is `Step5Gen_abs_le_of_im`; the public helper carries the stem (`Step5Gen_ingR5_iff_congr`, §3 (E)).
## (c) Verified names (the file compiles with each)
Mathlib/core: `abs_le_of_sq_le_sq` (Mathlib/Algebra/Order/Ring/Abs.lean:131), `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.sqrt_nonneg`, `Real.sqrt_sq`, `imp_congr` (core Init/Core.lean:1779), `and_congr`, `Nat.cast_pos`, `Complex.norm_real`, `Real.norm_of_nonneg`, `Matrix.isHermitian_zero`; names verified absent: none searched. Merged: `bandStep2_Ugen` (Chain/GridDuhamelGen.lean:181), `Step2Kern_UN_band` (Step2Gen.lean:328), `bandFM_STKward` (Step2Gen.lean:810), `mE_im` (Defs/Semicircle.lean:42), `norm_mE`, `tailTD_nonneg`, `Step2DefsInst.STGMM_zero` (Induction/Step2Defs.lean:907), `Step5Inst.inst_*` of `Step5Pins`.
## (d) Open issues and paper-delta candidates
1. Target 11 (`STLemDecCalEConclgL`, `STLemDecCalEgL`) is not written (section 2); it moves to U4s3, count-neutral.
2. **T2458a** (paper-delta candidate): the generic pins of targets 6-7 carry the spectral datum as `κ ≤ Im m` of the family at the constant sequence (shape of `STNewKLKAtgL'`, MN0), not as `|E| ≤ 2 - κ` or `‖m‖ = 1`. The band theorems run band => generic only: target 6 applies the band pin at the margin `κ²` (`κ ≤ Im m(E)` gives `|E| ≤ 2 - κ²`; private `Step5Gen_abs_le_of_im`), target 7 uses `|E| ≤ 2` for `‖m(E)‖ = 1`. Not claimed at the block Anderson carrier: U5's design question (T2459).
3. **T2458b** (paper-delta candidate): the kernel of the generic Step-5 pins is the drift kernel `Step2Gen_UN C n` read from the carrier, not the named propagator of the band; band identification `bandStep2_Ugen`, BA identification `Step2Kern_UN_BA` (merged).
4. For U5 / T2459 (`sz.lam` against `C.S`): the generic pins read `sz.lam n` in indices, regimes, `STAI`, `STprof`, `STtailTD` and the kernel's `S` as `C.S n`; no hypothesis links them. At `bandFM`, `C.S n = SB d (sz.L n) (sz.lam n)`; at `baFM`, `S := fun n => 1` (BA/FlowPins.lean:327). The BA reading of `sz.lam` (`g` or `g₀`) stays with X1a's measurement and U6-BA.
5. Consumers of the four rows that read the kernel (`STDuhamelI/II`, `STIniTermI/II`) must use `Step5Gen_ingR5_iff_congr` with the pointwise conclusion equivalences `bandFM_STIniTermConcl`, `bandFM_STDuhamelConcl`; `STIngR5_iff_gL` alone covers definitionally equal conclusions.
6. `RBM3D.lean` is listed as writable by the ticket and given to the hub by CLAUDE.md §1; the branch does not touch it (precedent t/T2453), the hub adds the import at merge.
7. Style only: module docstring lines above 100 characters (the `set_option` follows the docstring, as in the other chain files).
