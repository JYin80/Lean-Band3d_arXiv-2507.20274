Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 02:41:31 UTC 2026

Sources: RBM2D at `c9a24cf` (`git show c9a24cf:RBM2D/Green/{CondDom,CondStable,EntryGauss}.lean`: 647/645/151 lines; public declarations 13/7/4, as portmap P.1 rows 28, 30, 34); merged RBM3D at worktree HEAD `5bef95c`. `SP` = the scratchpad directory `T2101/`.

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `size n = (W L)^d` (R3), `W_le_self` (CondDom:298) | `W ≤ W L ≤ (W L)^d` | needs `d ≥ 1` (RBM2D `Nat.le_self_pow` at exponent 2) | `d=3,L=3,W=2`: `2 ≤ 6 ≤ 216`. At `d=0`: `size=1 < W=2`, so the ported statement is false at `d=0`: add `(hd : 1 ≤ d)` (T2101a) |
| 2 | lower bound on `size` (CondStable:79 `9 ≤ size`, `9 = 3^2`) | `size ≥ 3^d = 27` (`L=3,W=1`) | used only as `1 ≤ size` (all `d`) and `2 ≤ size` in `perTimeDomAt_of_le_left_on` (`2x^{-(D+1)} ≤ x^{-D}`, needs `x ≥ 2`) | `27 ≥ 2`. `2 ≤ size` fails at `d=0` (`size=1`): add `(hd : 1 ≤ d)` there (T2101a); `perTimeDomAt_const`, `_of_highProb` need none |
| 3 | diagonal variance `S_ii` (CondDom:57,215: `(5W²)⁻¹`) | `svarF_diag`: `W^{-d}(1+2d g²)⁻¹`, `g = sz.lam n` | `≥ 0` only (it multiplies `A_diag`) | `d=3,W=2,g=1/2`: `1/(8·2.5) = 1/20` (SA) |
| 4 | row sum `Σ_k svarF i k = 1` (RBM2D `IBP_sum_svar_row`) | `IBP_sum_svarF_row g (3 ≤ L) i` (`a + 2d·g²a = 1`, `a=(1+2dg²)⁻¹`) | `L ≥ 3` (`2d` distinct neighbours); no condition on `g` | `L=3`: exact equality (SB first line) |
| 5 | moment wrapper `perTimeDomAt_of_moment` (CondDom:316) | `p = ⌈(D+1)/τ⌉`, `C ≤ size^{τp-D}` eventually | `τp ≥ D+1`, exponent `τp-D ≥ 1`; `size → ∞` | exponent `= 1` at the four sampled `(τ,D)` (SA); statement is `d`-free (general `P`, `size`) |
| 6 | `hsize` cannot be dropped (private `condDom_no_hsize`, CondDom:587) | constant `L=3,W=2`: `size = 6^d` (RBM2D 36; here 216) | `Y≡10, Φ≡1`: `size^{1/10} < 10` | `216^{0.1} = 1.7118 < 10`, `P = 1 > 216⁻¹` (SA) |
| 7 | `perTimeDomAt_condRow_of_envelope` (CondStable:216) | `D₁ = Kenv+B+D+2`, `M = Kenv+B`; three exceptional sets at `(τ/3, ·)`; final `2·size^{2τ/3}χ ≤ size^τ χ` | `size^{τ/3} ≥ 2`; `3x^{-(D+2)} ≤ x^{-D}` via `2x^{-(D+2)} ≤ x^{-(D+1)}`, `2x^{-(D+1)} ≤ x^{-D}` (`x ≥ 2`) | `d`-free given `hsize`. `τ=1/10`: threshold `size ≥ 2^{30}`; at `sz0`: `n=0` size `2.1e6` fails, `n=1` `5.5e11` holds (eventual, SA) |
| 8 | (4.9) `norm_greenDiagCentered_sub_minor_le` (CondStable:410) | factor `2`; `δ' ≤ 1/2`, `‖m‖=1` give `‖G_ii‖ ≥ 1/2` | `u < 1` (`η_u > 0`), `\|E\| < 2`; no `0 ≤ u` | `d`-free; sample: `‖G_ii‖ = 1.0004` (SB) |
| 9 | `η_t = (1-t) Im m(E)` (RBM2D `Path/Scales:38`) | merged `RBM.Gauss.etaT` (`Loop/GLoop.lean:75`), `etaT_pos` (`:83`) | `\|E\|<2`, `t<1` | `d`-free. This is the only `Path/Scales` helper the three files use (grep of the three texts: no `scaleM`, `ellT`, `tailT`, `ellStar`, `Meta`, `ellz`, `etaT_div_etaT`), so no private scales copy is needed; the `d`-dimensional scales do not occur. `E=0,t=1/2`: `η = 1/2` (SA) |
| 10 | EntryGauss constants `κ, 𝔠, 𝔡, δ, c` | `κ=1/20, 𝔠=1/6, 𝔡=1/10, δ=1/20, c=1/40` at `sz0` (`d=3`) | `Admissible`: `N^𝔠 ≤ W`; `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`; `\|E n\| < 2-κ`; `0 ≤ t n < 1`; `RangeCond`: `N^{-1+δ} ≤ 1-t n` | `n=0`: `11.31 ≤ 32`; `7.8e-3 ≤ 1.56e-2 ≤ 10`; `0.5 < 1.95`; `9.9e-7 ≤ 0.9375` (SC) |
| 11 | signature change, EntryGauss | RBM2D `hsz : SizeTendsto`, `hbw : Bandwidth` become `hA : sz.Admissible 𝔠 𝔡` (merged `entry_bound_stochDom` etc., `Pins.lean` `GbEXPHypV3` order); `giiOmegaSeq`, `giiSeq_of_asGMc` get `hd : 3 ≤ d` (merged `diag_bound_stochDom*` take it); `gij*` take none | `κ>0`, `δ>0` (kept, unused) | stage 1b records as T2101b |

`d=2` tokens (portmap P.7 columns): CondDom `d=2:3` = lines 58, 62, 297 (docstrings), `Z2/zdist2:1` = line 64 (docstring), code `^ 2` at 302 becomes `^ d` (row 1); CondStable `d=2:1` = line 59, `Z2:2` = lines 61, 622 (docstrings), code `3^2` at 83-84 is replaced by rows 1-2; EntryGauss none. Other `d=2` text: instance `^ 2` (CondDom:382, 570; CondStable:452) and `size ≡ 36` (CondDom:313, 526, 586-621) become `^ d` (`d=3`) and `216`. Other renames: `svar … i k` → `svarF d (sz.L n) (sz.W n) (sz.lam n) i k`, `spectralZ/spectralM` → `zt/mE`, `hG : GaussIBP d` dropped (`gaussIBP` is a theorem, T2091 O1), `Sizes.size` → `(W L)^d`. No `UniformWeight` or `BoundedWeight` occurs in the three texts (grep), so DECISIONS §30 needs no action here.

DECISIONS §29 items for every statement with a time (`norm_green_diag_sub_mE_le`, `norm_condExpDiag_sub_le_offdiag`, `etaT_le_of_le`, `inv_etaT_le_inv_etaT`, `norm_greenDiagCentered_sub_minor_le`, EntryGauss four): (1) domain: only `t < 1` (`u < 1`) and, for `condExpDiag_eq_sum_Sblk`, `0 ≤ t`; no `s`, no `t ≤ lemT`; EntryGauss takes the pin's own `∀ n, 0 ≤ t n < 1` unchanged. (2) the case `ilambda > L`/`1 - ilambda²/L²`: no statement contains `ℓ`, `lemT` or `ilambda`; `g` enters only through `svarF`, whose row sum is `1` for every real `g`. (3) `L^d ≤ W^K` is used nowhere; the only `W`–`size` relation is row 1 (`W ≤ W L ≤ (W L)^d`); `Bandwidth` occurs only inside `Admissible`. (4) `∀ n` versus `∀ᶠ n`: in the envelope statements `hEnvpoly` is `∀ᶠ` and `henv` is `∀ n` with `Env` free (enlarge `Env n` at finitely many `n`); `hζ0`, `hχ0` (nonnegativity) and measurability are `∀ n` and are structural; EntryGauss `∀ n` bulk/time hypotheses are those of the merged pin, `RangeCond` and `Admissible` are `∀ᶠ`.

### (ii) One concrete nondegenerate instance

**SA** `python3 $SP/exps.py` (exponent rows, endpoint data of `norm_condExpDiag_sub_le_offdiag`, `perTimeDomAt_of_moment`, the envelope lemma):
```
W<=size? d=3 L=3 W=2: size=216 -> True
W<=size? d=3 L=4 W=32: size=2097152 -> True
W<=size? d=1 L=3 W=2: size=6 -> True
W<=size? d=0 L=3 W=2: size=1 -> False
min size, d=3, L=3, W=1: 27 >=9: True >=2: True
tau=0.1 D=1: p=20 tau*p-D=1 (>=1: True); C<=size^e eventually: size(0)^e=2.097e+06
tau=0.1 D=2: p=30 tau*p-D=1 (>=1: True); C<=size^e eventually: size(0)^e=2.097e+06
tau=0.25 D=3: p=16 tau*p-D=1 (>=1: True); C<=size^e eventually: size(0)^e=2.097e+06
tau=0.03333 D=5: p=180 tau*p-D=1 (>=1: True); C<=size^e eventually: size(0)^e=2.097e+06
no-hsize: size 216 size^(1/10)*Phi= 1.711769859409705 <10: True ; size^-1= 0.004629629629629629 < prob 1
envelope: D1=Kenv+B+D+2 = 5 ; tau/3 = 0.03333333333333333 ; 2tau/3 = 0.06666666666666667
 thresholds: size^(tau/3)>=2 <=> size >= 2^(3/tau) = 1073741824.0  ; 3 x^-(D+2) <= x^-D <=> x^2>=3 ; 2x^-(D+1+1)<=x^-(D+1) <=> x>=2
  sz0 n=0: size=2.097e+06 size^(tau/3)=1.625 >=2: False
  sz0 n=1: size=5.498e+11 size^(tau/3)=2.462 >=2: True
  sz0 n=2: size=8.125e+14 size^(tau/3)=3.14 >=2: True
  sz0 n=3: size=1.441e+17 size^(tau/3)=3.732 >=2: True
 3x^-(D+2) <= x^-D at n=1: True
c=1/40 <= d/2 = 1.5 : slack d/2-c = 1.475
W_n^-(d/2-c) at n=0,1,50: [0.00602426, 3.629e-05, 0.0]
instance E=0,t=1/2: eta_t = 0.5 ; (1/eta+1)^2 = 9.0 ; S_ii = 0.05 ; A+S_ii*Adiag = 9.45
sequence L=W=n+3, size=((n+3)^2)^3: [729, 4096, 15625, 46656] ; >= n: True
```
Endpoint data for CondDom/CondStable (`d=3`): constants `L=3, W=2, lam≡1/2` (`N=216`), `E=0` (`m=i`), `t=1/2`, site `i=(0,0,0)`: hypotheses `|E|<2`, `0 ≤ t < 1`, `‖ibpRem(i,k)‖ ≤ 9 = A = A_diag` hold, conclusion `≤ 9 + 9/20 = 9.45` (rows 3, 9 and SA). For the `≺` statements: `L=W=n+3` (`size=(n+3)^6 → ∞`), `V n = Unit`, `k n = 0`, `X = 2` on `{ω_c < 0}`, `1` off it (non-constant, bounded), `Φ ≡ 1`, `hsize` holds (SA last line).

**SB** (target `norm_greenDiagCentered_sub_minor_le`, ticket check): `d=3, L=3, W=2, g=1/2`, `N=216`, one Gaussian sample from the model law (`svarF` variance, `gvarF` real/imaginary split), `H = √u X`, `z = zt E u = E + (1-u) m(E)`, `i=(0,0,0)`, `k=(0,0,1)`. Command `python3 $SP/check_minor.py`:
```
row sum of svarF (should be 1): 1.0 1.0  S_ii = 0.05  W^-d/(1+2dg^2) = 0.05
[ticket z=0.3+0.2i] E=0.333861 u=0.797154 z=0.300000+0.200000j |E|<2:True u<1:True |m|=1.000000
  i=(0, 0, 0) k=(0, 0, 1) i!=k:True same block:True svarF(i,k)=0.05000
  max_xy|G-m I|=0.8339 -> GoodEvent with delta'<=1/2: False; |G_ii|=1.0769 (>=1/2: True)
  identity: |G_kk-G^(i)_kk - G_ki G_ik/G_ii| = 2.85e-15
  LHS=1.318402e-01  RHS=2|G_ki||G_ik|=2.839537e-01  LHS<=RHS: True
[good-event instance E=0,u=0.05] E=0.000000 u=0.050000 z=0.000000+0.950000j |E|<2:True u<1:True |m|=1.000000
  i=(0, 0, 0) k=(0, 0, 1) i!=k:True same block:True svarF(i,k)=0.05000
  max_xy|G-m I|=0.1511 -> GoodEvent with delta'<=1/2: True; |G_ii|=1.0004 (>=1/2: True)
  identity: |G_kk-G^(i)_kk - G_ki G_ik/G_ii| = 1.67e-17
  LHS=4.698162e-03  RHS=2|G_ki||G_ik|=9.400543e-03  LHS<=RHS: True
```
The ticket's `z = 0.3+0.2i` is `zt E u` at `E=0.333861, u=0.797154`; both sides hold there (`0.1318 ≤ 0.2840`) but this sample is not in `Ω(t,c)` at `δ'=1/2` (`max|G-mI| = 0.8339`), so the Lean hypothesis `hω` fails at it. The instance of the Lean hypotheses is the second one (`E=0, u=0.05`, `max|G-mI| = 0.1511 ≤ 1/2`, `0.00470 ≤ 0.00940`). At `u=0` one has `G = m·1`, `G_ki = 0`, both sides are `0`: a compiled instance must carry an explicit `ω` with `G_ki ≠ 0` (T2101 hypothesis `hω` is then checked for that `ω`).

**SC** (target EntryGauss, merged `sz0` of `RBM3D/Defs/Sizes.lean:263`, flow `E_n = lemE(z_n)`, `z_n = 1/2 + i N_n^{-4/5}`, `t ≡ 1/16 ≤ lemT`; matches `Instance.premises` of `Green/Pins.lean`, with `κ = (1/10)/2`). Command `python3 $SP/inst_entrygauss.py` (output cut to 250 columns):
```
n=0 L=4 W=32 N=2097152 lam=1.562e-02 | Bandwidth N^c<=W: 11.31<=32:True | WO: W^(-d/2+dd)=7.813e-03<=lam<=1/dd=10: True | |E|=0.50000<2-kappa=1.95:True | t=1/16<=lemT=0.99999:True t<1 |
   RangeCond N^(-1+delta)=9.873e-07<=1-t=0.9375:True
n=1 L=8 W=1024 N=549755813888 lam=2.441e-04 | Bandwidth N^c<=W: 90.51<=1024:True | WO: W^(-d/2+dd)=6.104e-05<=lam<=1/dd=10: True | |E|=0.50000<2-kappa=1.95:True | t=1/16<=lemT=1.00000:True t<1 |
   RangeCond N^(-1+delta)=7.028e-12<=1-t=0.9375:True
n=50 L=204 W=11040808032 N=11425969980610183329762199225554173952 lam=8.880e-13 | Bandwidth N^c<=W: 1.501e+06<=11040808032:True | WO: W^(-d/2+dd)=8.706e-15<=lam<=1/dd=10: True | |E|=0.50000<2-kappa=1.95:True | t=1/16<=lemT=1.00000:True t<1 |
   RangeCond N^(-1+delta)=6.237e-36<=1-t=0.9375:True
asGMc control W^-c at n=0: 0.917 >= W^(-d/2) = 0.005524 (paper: W^(-d/2) <= Psi <= W^(-eps0))
```
External hypothesis `AsGMcSeq sz0 E t c` (the paper's `(asGMc)`, `paper/tex/3_5_Loop_Hierarchy.tex:16`, `‖G_t-M‖_max ≤ W^{-ε₀}`), taken as a hypothesis by `gijSeq_of_asGMc`, `giiSeq_of_asGMc`: it is not proved here and its truth at the instance is not claimed. Limit data: the paper requires `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}`, so `ε₀ = c = 1/40 ≤ d/2 = 3/2`; `W_n^{-(d/2-c)}` is `6.0e-3` at `n=0`, `3.6e-5` at `n=1`, `→ 0` (SA, line `W_n^-(d/2-c)`).

### Verdicts
- CondDom (`perTimeDomAt_of_moment` and the 12 other public declarations): PASS; `W_le_self` needs `hd : 1 ≤ d` (row 1).
- CondStable (`norm_greenDiagCentered_sub_minor_le` and the 6 others): PASS; `perTimeDomAt_of_le_left_on` needs `hd : 1 ≤ d` (row 2).
- EntryGauss (`giiSeq_of_asGMc`, `gijOmegaSeq`, `giiOmegaSeq`, `gijSeq_of_asGMc`): PASS with the signature change of row 11. These are conditional adapters for `gijSeq_of_asGMc` and `giiSeq_of_asGMc`: the hypothesis `AsGMcSeq` stays.
- No statement is false at `d ≥ 3` as ported; the private `Path/Scales` helper reduces to the merged `etaT`, `etaT_pos` (row 9). Overall: PASS.

## (a′) Preflight corrections — Sun Oct  4 03:18:38 UTC 2026
Row SC of (a) cites `RBM3D/Defs/Sizes.lean:263` for `sz0`; `grep -n "def sz0" RBM3D/Defs/Sizes.lean` prints `260:def sz0 : Sizes 3 where`. No verdict changes; the other file:line citations of (a) that I re-checked agree with the files (`Path/Scales:38`, `GLoop.lean:75/83`, RBM2D `CondDom:298/316`, `CondStable:79/410`, `EntryGauss:93`).

## (b) Script output — Sun Oct  4 03:18:38 UTC 2026
Branch `t/T2101`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2101`. `git diff --name-only main...t/T2101` (script output below) lists only the new `RBM3D/Green/CondDom.lean`; `RBM3D/Test/Axioms.lean` is untouched (no registry line needed, b.3).
### b.1 Build, library build, hygiene
```
$ git log --oneline -2 ; git diff --name-only main...t/T2101 ; wc -l RBM3D/Green/CondDom.lean
72a80c4 T2101: docstrings of the sz0 instances
3f36aa8 T2101: instances at sz0 (generic rank-two (4.9) instance, generic ibpRem envelope)
RBM3D/Green/CondDom.lean
    1458 RBM3D/Green/CondDom.lean
$ date -u; lake build RBM3D.Green.CondDom   # file unchanged since the HEAD above (the date -u line is the start of that run)
Sun Oct  4 03:16:47 UTC 2026
✔ [3336/3336] Built RBM3D.Green.CondDom (4.6s)
Build completed successfully (3336 jobs).
$ lake build   # whole library incl. root #assert_rbm_axioms (the root does not yet import the module; the hub adds it at merge)
Build completed successfully (3845 jobs).
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Green/CondDom.lean
0
```
### b.2 `#print axioms` of every public declaration and private check (scratch copy of the file plus `#print axioms` lines; `axsum.py`)
```
declarations printed: 65; public: 24; private (checks): 41
[propext, Classical.choice, Quot.sound]: 64 declarations
[propext, Quot.sound]: 1 declarations = W_le_self
the 3 key targets and 4 key instances (perTimeDomAt_of_moment, norm_greenDiagCentered_sub_minor_le, giiSeq_of_asGMc, condDom_inst_moment, condStable_inst_minor_nd, EntryGauss_chk_gii, EntryGauss_chk_adapters): propext, Classical.choice, Quot.sound
```
### b.3 Registry pre-check (DECISIONS §20, ST1-COMMON item 8): scratch `import RBM3D` + `import RBM3D.Green.CondDom` + `#assert_rbm_axioms`, `lake env lean`
```
exit=0 (with and without the CondDom import)
base: axiom audit: 3153 theorems, 1175 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
with: axiom audit: 3175 theorems, 1177 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
base: premises found by scanning: 83 (borrowed 2, owed 66, structural 15).
with: premises found by scanning: 83 (borrowed 2, owed 66, structural 15).
with: registry: 5 borrowed + 101 owed + 38 structural;
```
The module defines no `Prop`-valued predicate (new definitions: `condRowReal`, `rowSlice`); +22 theorems and +2 definitions are the 24 public declarations; the scan finds the same 83 premises, so no registry line is appended.
### b.4 Statements against RBM2D `c9a24cf` (`adiff.py`: public headers up to `:=`; RBM2D side renamed by R1-R4 and `hG` dropped)
```
CondDom (13 public), identical after renaming (RBM2D line>RBM3D line): condRowReal(84>78), condRowReal_const(88>82), rowSlice(96>90), measurableSet_rowSlice(100>94), measurable_measure_rowSlice(105>99), lintegral_me
CondStable (7 public), identical after renaming (RBM2D line>RBM3D line): perTimeDomAt_const(102>381), perTimeDomAt_of_highProb(156>434), inv_etaT_le_inv_etaT(195>474), perTimeDomAt_condRow_of_envelope(216>496), perT
EntryGauss (4 public), identical after renaming (RBM2D line>RBM3D line): 
DIFF W_le_self (2D:298, 3D:295):
    2D(ren): theorem W_le_self (sz : Sizes d) (n : ℕ) : sz.W n ≤ sz.size n
    3D     : theorem W_le_self (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) : sz.W n ≤ sz.size n
DIFF perTimeDomAt_of_le_left_on (2D:123, 3D:401):
    [] -> [(hd : 1 ≤ d)]
DIFF common to gijOmegaSeq (2D:55, 3D:753), giiOmegaSeq (2D:67, 3D:765), gijSeq_of_asGMc (2D:81, 3D:780), giiSeq_of_asGMc (2D:93, 3D:792):
    [] -> [𝔡]
    [(h𝔠 : 0 < 𝔠)] -> []
    [(hsz] -> [(hA]
    [SizeTendsto d) (hbw : Bandwidth d 𝔠)] -> [sz.Admissible 𝔠 𝔡)]
    [RangeCond d] -> [sz.RangeCond]
  extra in giiOmegaSeq: [] -> [(hd : 3 ≤ d)]
  extra in giiSeq_of_asGMc: [] -> [(hd : 3 ≤ d)]
identical after renaming: 18 of 24; differing: 6
public declarations of the RBM3D file not in the three RBM2D files: []
```
### b.5 Target statements (extracted by `stmt.py`)
```
RBM3D/Green/CondDom.lean:314-319
  theorem perTimeDomAt_of_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      [IsFiniteMeasure P] {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop) {U : ℕ → Type*}
      {Y : ∀ l, U l → Ω → ℝ} {Φ : ∀ l, U l → ℝ} (hΦ : ∀ l u, 0 < Φ l u)
      (hint : ∀ (p l : ℕ) (u : U l), Integrable (fun ω => |Y l u ω| ^ (2 * p)) P)
      (hmom : MomentDomAt P size Y Φ) :
      PerTimeDomAt P size Y (fun l u _ => Φ l u) :=
RBM3D/Green/CondDom.lean:703-710
  theorem norm_greenDiagCentered_sub_minor_le (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2)
      (hu1 : u < 1) {δ' : ℝ} (hδ' : δ' ≤ 1 / 2) {ω : Sizes.SeqΩ sz}
      (hω : GoodEvent (green (Sizes.seqHflow sz n u ω) (zt E u)) (mE E) δ')
      (i k : Idx d (sz.L n) (sz.W n)) (hik : i ≠ k) :
      ‖greenDiagCentered sz n u (zt E u) (mE E) k ω
          - greenMinorDiagCentered sz n u (zt E u) (mE E) i ⟨k, Ne.symm hik⟩ ω‖
        ≤ 2 * (‖green (Sizes.seqHflow sz n u ω) (zt E u) k i‖
            * ‖green (Sizes.seqHflow sz n u ω) (zt E u) i k‖) :=
RBM3D/Green/CondDom.lean:792-796
  theorem giiSeq_of_asGMc (sz : Sizes d) (hd : 3 ≤ d) {κ 𝔠 𝔡 δ : ℝ} (hκ : 0 < κ) (_hδ : 0 < δ)
      (hA : sz.Admissible 𝔠 𝔡) (E t : ℕ → ℝ) (hE : ∀ n, |E n| < 2 - κ)
      (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1) (_hR : sz.RangeCond δ t) (c : ℝ) (hc : 0 < c)
      (hAs : AsGMcSeq sz E t c) :
      GiiSeq sz E t :=
```
### b.6 Compiled nonempty instances (section `Checks`, `CondDom.lean:805-1456`)
Data at `d = 3`: the preflight sequence `sz0` of `Defs/Sizes.lean` (slice `0`: `L=4, W=32, lam=1/64`, 2097152 sites of `Z_128^3`; `size_n -> inf` by `tendsto_sz0_size`) for every instance; `Instance.premises` for EntryGauss; the constant sizes `condDomCkS` (`L=3, W=2`, `size = 216`) only for the negative statement `condDom_no_hsize`. First use of each public declaration in `Checks` (`cover.py`), then the instances of the three key targets (extracted by line range):
```
checks section starts at line 805; first use of each public declaration in it:
  condRowReal@837  condRowReal_const@838  rowSlice@843  measurableSet_rowSlice@844
  measurable_measure_rowSlice@848  lintegral_measure_rowSlice@852  meas_measure_rowSlice_ge@858  norm_condRow_le_split@867
  norm_green_diag_sub_mE_le@883  norm_condExpDiag_sub_le_offdiag@949  etaT_le_of_le@961  W_le_self@963
  perTimeDomAt_of_moment@1012  perTimeDomAt_const@1115  perTimeDomAt_of_le_left_on@1168  perTimeDomAt_of_highProb@1178
  inv_etaT_le_inv_etaT@1195  perTimeDomAt_condRow_of_envelope@1105  perTimeDomAt_condRow_sub_self@1135  norm_greenDiagCentered_sub_minor_le@1405
  gijOmegaSeq@1436  giiOmegaSeq@1442  gijSeq_of_asGMc@1449  giiSeq_of_asGMc@1451
1009  private theorem condDom_inst_moment :
1010      PerTimeDomAt (Sizes.seqP sz0) sz0.size condDomCkY
1011        (fun _ _ _ => (1 : ℝ)) :=
1012    perTimeDomAt_of_moment tendsto_sz0_size (fun _ _ => one_pos) condDomCkY_int
1013      condDomCkY_moment
1397  private theorem condStable_inst_minor_nd (hik : i ≠ k) :
1398      ‖greenDiagCentered sz 0 (1 / 4) (zt 0 (1 / 4)) (mE 0) k (condStableΩ sz i k)
1399          - greenMinorDiagCentered sz 0 (1 / 4) (zt 0 (1 / 4)) (mE 0) i ⟨k, Ne.symm hik⟩
1400            (condStableΩ sz i k)‖
1401        ≤ 2 * (‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) k i‖
1402            * ‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) i k‖) ∧
1403      0 < ‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) k i‖
1404          * ‖green (Sizes.seqHflow sz 0 (1 / 4) (condStableΩ sz i k)) (zt 0 (1 / 4)) i k‖ :=
1405    ⟨norm_greenDiagCentered_sub_minor_le sz 0 (by norm_num) (by norm_num) (δ' := 1 / 2) le_rfl
1406      (condStable_goodEvent_nd hik) i k hik,
1407      by rw [condStable_green_ki hik, condStable_green_ik hik]; norm_num⟩
1422  example :=
1423    condStable_inst_minor_nd (sz := sz0) (i := condDomCk0) (k := condDomCk1) condDomCk01
1445  open RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst in
1446  private theorem EntryGauss_chk_adapters (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40)) :
1447      GijSeq sz0 (STflowE z0) tInst ∧ GiiSeq sz0 (STflowE z0) tInst := by
1448    obtain ⟨hA, hE, h0, h1, hR⟩ := Instance.premises
1449    exact ⟨gijSeq_of_asGMc sz0 (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num) (by norm_num)
1450        hA (STflowE z0) tInst hE h0 h1 hR (1 / 40) (by norm_num) hAs,
1451      giiSeq_of_asGMc sz0 (by norm_num) (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num)
1452        (by norm_num) hA (STflowE z0) tInst hE h0 h1 hR (1 / 40) (by norm_num) hAs⟩
```
(4.9) instance: `condStable_inst_minor_nd` holds for every `sz : Sizes 3` and sites `i != k` of slice `0`, at `E = 0`, `u = 1/4`, with the sample `omega` whose real coordinates `(i,k,true)`, `(k,i,true)` equal `1/2` and all others `0`; `GoodEvent ... (1/2)` is proved (`condStable_goodEvent_nd`) from the explicit resolvent (`condStable_green`: rank-two block algebra), `G_ki = G_ik = 2/5` (`condStable_green_ki/_ik`). The `example` applies it at `sz0`, `i = (0,0,0)`, `k = (1,0,0)`. The closed forms do not depend on the number of sites; independent numeric check at `L=3, W=2` (216x216 matrices, `check_nd.py`):
```
n=216, u=0.25, z=0.75j, H_ik=0.2500
max_xy |G - m I| = 0.400000 (<= 1/2: True)
G_ii=1.2j G_kk=1.2j G_ik=0.400000 G_ki=0.400000 G_xx(other)=1.333333j
LHS=|(G_kk-m)-(G^(i)_kk-m)|=0.133333  RHS=2|G_ki||G_ik|=0.320000  LHS<=RHS: True
```
Other instances: `condDom_inst_offdiag` (`sz0`, `n=0`, `E=0, t=1/2`, `A = A_diag = 9`, bound `9 + 9/32816` with `svarF_diag = 1/32816`, every `omega`); `condDom_no_hsize` (compiled negative statement at `size = 216`); `condStable_inst_*` at `sz0` (`X = 2` on `{omega_c < 0}`, `1` off it; `hsize` proved); `EntryGauss_chk_gij/_gii` fully discharged at `sz0`. The adapters keep `hAs : AsGMcSeq` (the paper `(asGMc)`, `3_5:16`, `3_5:30`, another gate's pin) as a hypothesis.
### b.7 Name clash and RBM2D diff-stat
```
$ git grep -nwE "(condRowReal|condRowReal_const|rowSlice|measurableSet_rowSlice|measurable_measure_rowSlice|lintegral_measure_rowSlice|meas_measure_rowSlice_ge|norm_condRow_le_split|norm_green_diag_sub_mE_le|norm_condExpDiag_sub_le_offdiag|etaT_le_of_le|W_le_self|perTimeDomAt_of_moment|perTimeDomAt_const|perTimeDomAt_of_le_left_on|perTimeDomAt_of_highProb|inv_etaT_le_inv_etaT|perTimeDomAt_condRow_of_envelope|perTimeDomAt_condRow_sub_self|norm_greenDiagCentered_sub_minor_le|gijOmegaSeq|giiOmegaSeq|gijSeq_of_asGMc|giiSeq_of_asGMc)" 5bef95c -- RBM3D/*.lean RBM3D.lean | cut -c1-150
5bef95c:RBM3D/Test/Axioms.lean:105:   `RBM.Green.GijOmegaSeq,          -- `(GijGEX)` on `Ω` per sequence: S1-24 `gijOmegaSeq`, RBM2D `Green/EntryGauss
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/CondDom.lean RBM2D/Green/CondStable.lean RBM2D/Green/EntryGauss.lean ; git -C ../RBM2D --no-optional-locks log -1 --format=%h
 RBM2D/Green/CondDom.lean    | 379 +++++---------------------------------------
 RBM2D/Green/CondStable.lean | 325 +++++--------------------------------
 RBM2D/Green/EntryGauss.lean |  85 +++-------
 3 files changed, 100 insertions(+), 689 deletions(-)
9e0f275
```
The one hit is the existing registry comment naming `gijOmegaSeq`; no declaration clashes; every unpinned helper is `private`.
### b.8 `d = 2` tokens of the portmap rows: RBM2D line(s) | text => RBM3D line (`tokens.py`)
```
CondDom:58,CondDom:297 | * `etaT_le_of_le`, `W_le_self` -- `η_t ≤ η_u`   =>  :292 /-- **`W ≤ size`** (RBM2D `W_le_self`, `CondDom:298`).  For 
CondDom:62,CondStable:59 | ## d = 2 changes  =>  :49 ## Differences from RBM2D (residual, after the renaming)
CondDom:64,CondStable:61 | `Sblk` becomes the variance profile `svar` on   =>  :23 `Z2 L`/`Idx L W` become `Zd d L`/`Idx d L W`, `size = (W L)^
CondDom:302 | _ ≤ (d.W n * d.L n) ^ 2 := Nat.le_self_pow (by  =>  :299 _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
CondDom:313 | constant sizes `L = 3`, `W = 2` (`size ≡ 36`),  =>  :311 (`size ≡ 6^d`), `Y ≡ 10`, `Φ ≡ 1` satisfy `MomentDomAt`, whi
CondDom:382 | change n ≤ ((n + 3) * (n + 3)) ^ 2  =>  :1012 perTimeDomAt_of_moment tendsto_sz0_size (fun _ _ => one_pos)
CondDom:526 | example : (2 : ℕ) ≤ 36 := W_le_self condDomCkS  =>  :963 example : (32 : ℕ) ≤ 2097152 := W_le_self sz0 (by norm_num) 
CondDom:570 | change 1 ≤ ((l + 3) * (l + 3)) ^ 2  =>  :1002 exact_mod_cast sz0.one_le_size l
CondDom:592 | have h36 : ∀ l : ℕ, condDomCkS.size l = 36 :=   =>  :1032 have h216 : ∀ l : ℕ, condDomCkS.size l = 216 := fun _ => rfl
CondStable:83 | calc 9 = 3 ^ 2 := by norm_num  =>  :373 calc 3 ≤ sz.W n * sz.L n := h3
CondStable:84 | _ ≤ (d.W n * d.L n) ^ 2 := Nat.pow_le_pow_left  =>  :374 _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
CondStable:452 | change n ≤ ((n + 3) * (n + 3)) ^ 2  =>  :1107 (Env := fun _ => 2) (Kenv := 1) (B := 1) tendsto_sz0_size
CondStable:622 | `k = (1,0)` of `Idx 3 3 = Z2 9`. -/  =>  :1204 at `sz0` with `i = (0,0,0)`, `k = (1,0,0)` of `Z_128^3`. -/
$ grep -cE "lemT|ilambda|ℓ|W \^ K|L \^ d|UniformWeight|BoundedWeight" RBM3D/Green/CondDom.lean   # DECISIONS §29, §30
0
```
### Narrative
1. All 24 public declarations of the three RBM2D files (13/7/4, portmap rows 28, 30, 34) are in `RBM3D/Green/CondDom.lean`; none dropped. 18 have the RBM2D header after R1-R4, 6 differ (b.4). Imports: `Green.{IBP,Pins,EntryDom,LDE,IBPPoly}`, `Induction.PerTimeCalc`, `Gauss.DominationAt`, `Loop.GLoop`.
2. Reused, not copied: `condRow`, `rowSplit`, `measurePreserving_rowSplit`, `FinDepOffRow`, `condRow_sub`, `greenMinorMat_eq_minorGreen` (FlucVanish); `ibpRem`, `condExpDiag_eq_sum_Sblk`, `IBP_sum_svarF_row` (IBP, called without `hG`); `norm_greenDiagCentered_le_env`, `isUnit_det_Hflow_sub`, `stochDom_ldeRow/Col`, `stochDom_normSq_Hflow_diag` (LDE); `stochDom_ldeQuad` (IBPPoly); `entry_bound_stochDom*`, `diag_bound_stochDom*` (EntryDom); `GoodEvent.norm_greenMinor_sub_le` (EntryCore); the `perTimeCalc_*` lemmas.
3. Import cut `Path/Scales`: the three RBM2D texts use only `etaT`, which is the merged `RBM.Gauss.etaT` (`Loop/GLoop.lean:75`, `etaT_pos` :83, `etaT_eq_zt_im`); no private scales copy exists. RBM2D `scaleM`, `ellT`, `tailT`, `ellStar`, `Meta`, `ellz` do not occur in them (grep count 0).
4. `d`-exponents: `size = (W L)^d`. `W_le_self` reads `W <= W L <= (W L)^d` and needs `hd : 1 <= d` (at `d = 0`, `size = 1 < W`: (a) row 1). RBM2D `9 <= size` becomes the private `3 <= size` (`d >= 1`), used by `perTimeDomAt_of_le_left_on` (`hd : 1 <= d`; T2101a). Every other statement is `d`-free (`size` is abstract); no statement is false at `d >= 3` as ported.
5. DECISIONS §29 items as in (a): the time conditions are `t < 1` (`u < 1`, `v < 1`), `u <= t` (the two `η` monotonicity statements) and `0 <= t` (`norm_condExpDiag_sub_le_offdiag` only); no `ℓ`, `lemT`, `ilambda`, `L^d <= W^K` or weight occurs (b.8); `hEnvpoly` is `∀ᶠ`, `henv` is `∀ n`; EntryGauss keeps the `∀ n` bulk/time hypotheses and `RangeCond` of the pin `GbEXPHypV3`.
6. `hsize : Tendsto size atTop atTop` stays a hypothesis of `perTimeDomAt_of_moment`, `_condRow_of_envelope`, `_sub_self` (D20); `condDom_no_hsize` compiles the negative statement at `d = 3`.
7. EntryGauss takes the premises of `GbEXPHypV3` in its order with `hA : sz.Admissible 𝔠 𝔡` in place of `hsz`, `hbw` (D39); `giiOmegaSeq`, `giiSeq_of_asGMc` take `hd : 3 <= d` like the merged `diag_bound_stochDom` (T2101b); `_hδ`, `_hR` are unused, as in RBM2D.
8. The RBM2D (4.9) instance is at `u = 0` (`G = m I`, both sides `0`). Here the instance is the explicit rank-two sample of b.6 with `G_ki = 2/5`: `LHS = 0.1333 <= RHS = 0.32`, `‖G - m‖_max = 0.4 <= 1/2` (numeric check at 216 sites; the closed forms and the Lean proof do not depend on the number of sites). The second sample of (a) SB (a Gaussian draw at `u = 0.05`) has no explicit resolvent, so it is not the compiled instance.
9. The only hypothesis of an instance that is not discharged is `hAs : AsGMcSeq`; it is the premise of the merged `entry_bound_stochDom_of_asGMc` and `diag_bound_stochDom_of_asGMc` and I add no hypothesis; limit data in (a) SC. The private `Checks` sections of RBM2D are replaced by section `Checks`.
10. Registry: no `Prop`-valued predicate is defined, `Test/Axioms.lean` is unchanged, and the pre-check (b.3) exits 0.

## (c) Verified Mathlib names (`#check` in `lake env lean`, first 105 columns of each output)
```
Matrix.single.{u_2, u_3, u_7} {m : Type u_2} {n : Type u_3} {α : Type u_7} [DecidableEq m] [DecidableEq n
Matrix.single_mul_single_same.{u_1, u_2, u_3, u_7} {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
Matrix.single_mul_single_of_ne.{u_1, u_2, u_3, u_7} {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
Matrix.inv_eq_right_inv.{u', v} {n : Type u'} {α : Type v} [Fintype n] [DecidableEq n] [CommRing α] {A B 
Matrix.one_apply_ne.{v, u_3} {n : Type u_3} {α : Type v} [DecidableEq n] [Zero α] [One α] {i j : n} : i ≠
Complex.I_sq : Complex.I ^ 2 = -1
Complex.norm_real (r : ℝ) : ‖↑r‖ = ‖r‖
Nat.le_self_pow {n : ℕ} (hn : n ≠ 0) (a : ℕ) : a ≤ a ^ n
MeasureTheory.mul_meas_ge_le_lintegral₀.{u_1} {α : Type u_1} {mα : MeasurableSpace α} {μ : Measure α} {f 
measurable_measure_prodMk_left.{u_1, u_2} {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSp
MeasureTheory.Measure.prod_apply.{u_1, u_2} {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [Measurable
MeasureTheory.integral_indicator_const.{u_1, u_3} {X : Type u_1} {E : Type u_3} {mX : MeasurableSpace X} 
ENNReal.le_div_iff_mul_le {a b c : ENNReal} (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ⊤ ∨ c ≠ ⊤) : a ≤ c / b ↔ a * b
ENNReal.ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) : ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.of
Real.rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1
Real.one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z
pow_le_one₀.{u_2} {M₀ : Type u_2} [MonoidWithZero M₀] [Preorder M₀] {a : M₀} [PosMulMono M₀] {n : ℕ} (ha₀
Filter.tendsto_atTop_mono.{u_3, u_4} {α : Type u_3} {β : Type u_4} [Preorder β] {l : Filter α} {f g : α →
inv_anti₀.{u_3} {G₀ : Type u_3} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectL
```
Verified absent: none sought. Tactic `match_scalars` is available (used in `blk_alg`).

## (d) Open issues and paper-delta candidates
- **T2101a** (new): `W_le_self` and `perTimeDomAt_of_le_left_on` take `hd : 1 ≤ d`; RBM2D has `size = (W L)^2 ≥ 9` for free, and at `d = 0` `size = 1`.
- **T2101b** (new): `giiOmegaSeq`, `giiSeq_of_asGMc` take `hd : 3 ≤ d` (as the merged `diag_bound_stochDom`); the `Admissible` form of the other premises is D39 (cited, not re-proposed); `hG : GaussIBP` is dropped (T2091 audit O1, cited).
- Observation: RBM2D `HEAD` `9e0f275` differs from `c9a24cf` in the three files (b.7: 100 insertions, 689 deletions); the port follows `c9a24cf` (ST1-COMMON item 1) and the RBM2D HEAD statements were not compared.
- Observation: the registry lists `RBM.Green.GijOmegaSeq` (owed) with the comment "S1-24 `gijOmegaSeq`"; the premise scan finds the same 83 premises with and without this module (b.3), so nothing needs to change there at merge.
