Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 17:09:54 UTC 2026

Sources: RBM2D `c9a24cf` (`CltResolvent.lean` 977 lines, `CltPath.lean` 320, `CltStep.lean` 737, `Induction/Defs.lean:140-175`, `Case3Defs.lean:63`); merged RBM3D at `ae259a6`. "RBM3D" locations below are file:line read in this session.

### (i) Exponent table

**Dictionary (RBM2D → RBM3D merged).**

| RBM2D | RBM3D | note |
|---|---|---|
| `Z2 L`, `zdist2` | `Zd d L`, `zdistInf d L` (`Defs/Sizes.lean:115`) | `zdistInf_le_zdistD` :117; triangle/neg for `zdistInf` only as private copies (`Induction/B45.lean:904`, `Green/Pins.lean:501`) → re-prove privately from public `zdist_add_le`, `zdist_neg` (`Defs/Lattice.lean:38,53`) |
| `Idx L W`, `splitEquiv` | `Idx d L W = Zd d (W*L)` (`Sizes:46`), `splitEquiv d L W` (`Sizes:87`) | `card_Idx : card = (W*L)^d` (`Sizes:107`) |
| `Coord`, `Ω`, `gvar` | `CoordF d L W`, `Ω d L W`, `gvarF d L W g` (`Gauss/FineModel.lean:89`) | `g` is a parameter (via `svarF`, :46) |
| `coordinateMatrix`, `Xmat_update`, `Hflow` | `FineModel.lean:384`, `:393`, `:437`; `Hflow_isHermitian` :461 | `Xentry` has the same orientation-by-`idxKey` shape |
| `gEntry E s M σ x y` | **no merged analogue** (grep): define `gEntry := Gres M (zt E s) σ x y` (`Loop/GLoopFlow.lean:74`) | `Gres_eq_green_zSig` (`Induction/ConArgDet.lean:367`): `= green M (zSig (zt E s) σ)` = RBM2D's `(M − z_σ·1)⁻¹ x y` |
| `spectralZ E u` | `zt E u` (`Defs/Semicircle.lean:179`) | `spectralZ_im` (`Gauss/FlowCalculus.lean:51`): `Im z = (1−u) Im m`; `mE_im` (`Semicircle:42`): `Im m = √(4−E²)/2` |
| `green`, `isUnit_sub_smul_one_of_im_ne_zero`, `norm_green_le` | `green` (`Green/EntryCore.lean:34`), `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero` (`ConArgDet:380`), `norm_Gsig_le_inv_eta` (`FlowCalculus:644`) | `hasDerivAt_lineInverse` and `isHermitian_add_realSmul` have no public merged copy (private ones in `Path/OneStep:1264` etc.) → port privately (leads: `hasDerivAt_green_moving` `FlowCalculus:374`) |
| `LocalForm L W k K`, `eval`, `Local τ s` | `LocalForm d L W k K` (labels `Fin k → Zd d L`), `eval` with merged `gEntry`; `Local ρ` | not merged (grep, 0 hits); `Local`: `∃ m, zdistInf(blk x − b m) + zdistInf(blk y − b m) < ρ` (RBM2D: `< ellT L s * W^τ`) |
| `N = (WL)^2` | `N = (W*L)^d = card Idx`; `2N²` real coordinates unchanged | RBM2D `cltres_card_idx` (:651) is the only place `N` is computed |
| `sbSupport` (5 pts) | `sbKernelR` (`Defs/Block.lean:74-76`): nonzero iff `x = 0` or `zdistD x = 1` | script (iii-c): 7 = `2d+1` per row at `d=3`; `zdistInf ≤ 1` cube has `3^d = 27` |

**Constants and exponents (all dimension-free except those marked N, ρ, R).**

| # | constant | value / constraint | slack |
|---|---|---|---|
| 1 | step length `|t| ≤ 2W^{-1/2}`, hyp `16W^{-1/2} ≤ 1` | needs `8|t| ≤ 1` (M1: `4|t|g ≤ 1`, `g=2`; `hstep`: `2|t|·4·γ ≤ γ`), i.e. `W ≥ 256` | `W=2^24` (`szCL`, n=0): `16W^{-1/2} = 0.0039`, 256× |
| 2 | M1/M2/M3 constants `2g`, `2|t| g_t max`, `2g max` | identities `G−G_t = tGAG_t = tG_tAG`, `A` supported on `{(a₀,b₀),(b₀,a₀)}`, entries `≤ 1`; independent of `d` | script (iii-b): ratios `0.50`, `0.17`, `0.17` (≤ 1) |
| 3 | path derivative bound | `g=4` (M1 at `g=2`), `φ=2γ` (M2) ⇒ `‖D‖ ≤ 2·j·4^j·2γ·|coef| = 4γ·cltCoefSum` | exact (RBM2D `cltpath_deriv`) |
| 4 | N: `c_κ/N ≤ Im z_u` | `c_κ = √(κ(4−κ))/2 ≤ Im m` for `|E| ≤ 2−κ` (`4−E² ≥ κ(4−κ)`), `Im z = (1−u)Im m ≥ c_κ N^{-1+δ} ≥ c_κ/N` when `N^{-1+δ} ≤ 1−u`, `N=(WL)^d ≥ 1` | `N=27,δ=1/2`: `0.032 ≤ 0.5` |
| 5 | N: `‖cltY‖ ≤ (K+1)N^{C'}(2N³/c_κ)^K` | per factor `2N²` triples × entry `≤ N/c_κ`; `N` enters only as `card Idx` | `N=27,K=1,C'=0`: `9.09·10^4` vs `|Y| ≤ 2` |
| 6 | **ρ, R (new)**: threshold `θ := R/2 − ρ − 1` of `cltGoodAt` | `x` within `ρ` of `b`, `a` at `≥ R/2` from `b`, `|a'−a| ≤ 1` ⇒ `|x−a| ≥ R/2−ρ`, `|x−a'| ≥ R/2−ρ−1`; pure triangle inequality, no hypothesis on `ρ, R, W` | `ρ=w, R=10w`: `θ = 4w−1 ≥ c w` iff `(4−c)w ≥ 1`; `w=(log W)^3ℓ_s ≥ 1.326` (`W ≥ 3`, `ℓ_s ≥ 1`); `c=1`: 3.25×, `c=3`: ok (script iii-a) |
| 7 | far-set bound for `STFarEntryAtLog` (T2141 Am.1) | indicator `c w ≤ dist` is implied by `θ ≤ dist` when `θ ≥ c w` | `c ∈ {1,3}` at `ρ=w,R=10w` |
| 8 | `cltFarGeomHalf` | `R ≤ |b_i−b_k|` ∀k≠i ⇒ `R/2 ≤ |a−b_i|` or `∀k≠i, R/2 ≤ |a−b_k|`; triangle + neg only | `R = 10w`: half `5w` |
| 9 | `Bandwidth`: `W^{-D'} ≤ N^{-D''}` for `D' = D''/𝔠` | `N^𝔠 ≤ W` (`Defs/Sizes.lean:168`); dimension-free | consumer side (S5-21) |

### (ii) One concrete nondegenerate instance (all numbers by script)

* **Resolvent bounds, `d=3, L=3, W=1, g=1/2`** (`N = 27`): `M = 0`, `E = 0`, `u = 1/2` (`z = i/2`), `t = 1/8`, `κ=1, δ=1/2`; every coordinate `c = (x,y,β)`, `√u·coordinateMatrix c` is a `cltCoordDir` (729 nonzero directions). `4|t|g = 1` with `g = 2` (`max|G_0| = 2`). `M1,M2,M3,E4,M5` checked in (iii-b); `cltFarGeomHalf`, `cltFarGeomNear`, `cltCoord_adj` checked at `L=5,6,7` in (iii-a), (iii-c) (at `L=3` every pair is adjacent, so adjacency is tested at `L=7`).
* **`cltPath_bound` on `szCL`, `n=0`** (`Step5Pins.lean:640`: `L=2·24^5`, `W=2^24`, `lam=1`, `ℓ_s=1` by `szCL_ellT_s`:799): `E=0, u=1/2, ω₀=0` (`G(σ) = −z⁻¹·1`, diagonal, `|G_xx| = 2 ≤ 2`, off-diagonal `0 ≤ W^{-D'}` for every `D'>0`, so `cltGoodAt` holds at any `θ>0`); `w=(log W)^3=4603.73`, `ρ=w`, `R=10w`, `R/2=23018.66 ≤ L/2`; block `c.1` at `|[c.1]−b|_∞ = 23019 ≥ R/2`, `c.2.1 = c.1` (adjacent); `F` = one monomial `G_{xy}` with `blk x = blk y = b` (locality sum `0 < ρ`), left index `x` at distance `23019 ≥ θ = 18413.93` from `c.1`; `|s−ω₀ c| ≤ 2W^{-1/2} = 4.9·10^{-4}`. All hypotheses hold simultaneously; `E`, `ω₀` are concrete, nothing is a hypothesis.
* No external hypothesis in these targets (all deterministic); the T2141 pin `STFarEntryAtLog` is only the *source* of `cltGoodAt` at the consumer, so no limit computation is owed here.

### (iii) Scripts (scratch `…/scratchpad/T2144/`, S = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2144`)

(a) `python3 $S/pre.py` — exhaustive triangle check on `Z_L^3` (periodic `‖·‖_∞`, `b=0`) and the threshold arithmetic:
```
geom d=3 L=5: violations of |x-a|>=|a-b|-|x-b| and |x-a'|>=|a-b|-|x-b|-1 (|a'-a|<=1): (0, True, True)
geom d=3 L=6: violations of |x-a|>=|a-b|-|x-b| and |x-a'|>=|a-b|-|x-b|-1 (|a'-a|<=1): (0, True, True)
geom d=3 L=7: violations of |x-a|>=|a-b|-|x-b| and |x-a'|>=|a-b|-|x-b|-1 (|a'-a|<=1): (0, True, True)
w=(log W)^3 ell_s, ell_s>=1, W>=3 => w>=1.3260
W=3 ell_s=1 w=1.326 | rho=w, R=10w: theta/w=3.2458 (c=1 ok:True c=3 ok:True) | rho=w+1, R'=8w (2-label): theta/w=1.4917 (c=1 ok:True c=3 ok:False) | rho=2w, R'=8w (2-label): theta/w=1.2458 (c=1 ok:True c=3 ok:False)
W=3 ell_s=5 w=6.630 | rho=w, R=10w: theta/w=3.8492 (c=1 ok:True c=3 ok:True) | rho=w+1, R'=8w (2-label): theta/w=2.6983 (c=1 ok:True c=3 ok:False) | rho=2w, R'=8w (2-label): theta/w=1.8492 (c=1 ok:True c=3 ok:False)
W=16777216 ell_s=1 w=4603.733 | rho=w, R=10w: theta/w=3.9998 (c=1 ok:True c=3 ok:True) | rho=w+1, R'=8w (2-label): theta/w=2.9996 (c=1 ok:True c=3 ok:False) | rho=2w, R'=8w (2-label): theta/w=1.9998 (c=1 ok:True c=3 ok:False)
W=16777216 ell_s=5 w=23018.664 | rho=w, R=10w: theta/w=4.0000 (c=1 ok:True c=3 ok:True) | rho=w+1, R'=8w (2-label): theta/w=2.9999 (c=1 ok:True c=3 ok:False) | rho=2w, R'=8w (2-label): theta/w=2.0000 (c=1 ok:True c=3 ok:False)
```
(b) `python3 $S/inst.py` — `d=3, L=3, W=1, g=1/2`, all coordinates, faithful `Xentry`/`idxKey` orientation:
```
N=27  Im z=0.500  max|G0|=2.0000 (good-set bound 2)
nonzero coordinate directions: 729  max |[x]-[y]|_inf over gvar!=0 coords: 1
M1 max |G_t|/(2g) = 0.5000 (<=1)   M2 max ratio = 0.1741 (<=1)   M3 max |fd - (-G_t A G_t)| = 2.79e-10   M3 bound ratio = 0.1741 (<=1)
E4: N^(-1+delta)=0.19245 <= 1-u=0.50 ; c_kappa/N=0.03208 <= Im z=0.50 ; |E|=0<=2-kappa=1
M5: (K+1) N^C' (2N^3/c_kappa)^K = 90911.9  vs  |Y|=|G0_{ab}| <= 2
szCL0: L=15925248 W=16777216  16 W^(-1/2)=0.00391<=1  2W^(-1/2)=4.883e-04  w=(log W)^3=4603.73 rho=4603.73 R/2=23018.66 theta=18413.93  L/2=7962624
block c.1 at |[c.1]-b|_inf = 23019 >= R/2 = 23018.66 and < L/2: True ; left index at block b: dist to c.1 = 23019 >= theta: True
omega0 = 0, E=0, u=1/2: G(sigma) = -z^-1 Id, |G_xx| = 2.000 <= 2, off-diagonal = 0 <= W^(-D') (far pairs have x != y); local monomial G_{x y}, blk x = blk y = b: sum of dists 0 < rho
```
(c) `python3 $S/adj.py` — which distance `gvarF ≠ 0` gives (`S^B` support, `d=3, L=7, g=1/2`):
```
L=7 d=3: #pairs with S^B!=0 per row: 7 (2d+1 = 7) | max zdistD: 1 | max zdistInf: 1 | pairs with zdistInf<=1 per row: 27 (3^d = 27)
```
So `gvarF c ≠ 0 ⇒ zdistD(blk x − blk y) ≤ 1 ⇒ zdistInf ≤ 1` (`sbKernelR`'s two cases; `g` arbitrary; no `3 ≤ L` used, RBM2D's `3 ≤ L` came from `zdist2_le_one_of_mem_sbSupport`).
(d) `python3 $S/eta.py` — regime (i) `N^{-1+δ} ≤ 1−s` (`1−s ≥ 1−t ≥ λ²/L²`, `λ ≥ W^{-d/2+𝔡}`, `𝔡=0.1`, `δ=1/15 ≤ 2𝔡/d`, `d(1−δ) ≥ 2`) and step length vs std:
```
W=16777216 L=15925248: log N^(-1+delta)=-93.01 <= log(lam^2/L^2)=-79.75 : True
W=16777216 L=16777216: log N^(-1+delta)=-93.16 <= log(lam^2/L^2)=-79.85 : True
W=4 L=4: log N^(-1+delta)=-7.76 <= log(lam^2/L^2)=-6.65 : True
W=2^24: threshold/std >= 1.678e+07 (= W^((d-1)/2)); Gaussian tail exponent W^(d-1)/2 = 1.407e+14
```
(`std ≤ W^{-d/2}` since `svarF = W^{-d}·SBR` and `SBR` entries are `a=(1+2dg²)⁻¹ ≤ 1` or `g²a ≤ 1/(2d)`.)

### Statements whose form changes (old → new)

* `CltFarGeomNear`: `∀ L w ℓ a a' b x, 6 ≤ w → 1 ≤ ℓ → w²ℓ/2 ≤ |a−b|₂ → |a'−a|₂ ≤ 1 → |x−b|₂ < ℓw → ℓw ≤ |x−a|₂ ∧ ℓw ≤ |x−a'|₂` → `∀ d L ρ R (a a' b x : Zd d L), R/2 ≤ |a−b|_∞ → |a'−a|_∞ ≤ 1 → |x−b|_∞ < ρ → R/2−ρ−1 ≤ |x−a|_∞ ∧ R/2−ρ−1 ≤ |x−a'|_∞` (no hypothesis on `ρ,R`; the `nlinarith` step `ℓw+1 ≤ w²ℓ/2−ℓw` disappears).
* `CltCoordAdj`: `∀ L W, 3 ≤ L → ∀ c, (gvar c ≠ 0 → zdist2(blk c.1 − blk c.2.1) ≤ 1) ∧ …` → `∀ d L W g, ∀ c : CoordF d L W, (gvarF d L W g c ≠ 0 → zdistInf d L (blk c.1 − blk c.2.1) ≤ 1) ∧ …` (two entry conjuncts unchanged; `g` explicit).
* `CltEtaLower`, `CltEvalDetLe`: `(W*L)^2` → `(W*L)^d`; `cltEta_lower d L W`, `cltEval_det_le d L W`. `CltPertMaxLe/SubLe`, `CltDerivEntry`, `cltCoordDir`, `cltCk`: unchanged (generic in the index type).
* `CltPathBound`: hypotheses `F.Local τ u`, `6 ≤ W^τ`, `1 ≤ ellT L u`, `(W^τ)²ℓ/2 ≤ |[c.1]−b|₂`, `cltGoodAt E u (ℓW^τ) D' ω₀` → `F.Local ρ`, `R/2 ≤ |[c.1]−b|_∞`, `cltGoodAt E u θ D' ω₀` with `θ ≤ R/2−ρ−1` (kept: `0 ≤ u < 1`, `Im z_u ≠ 0`, `16W^{-1/2} ≤ 1`, adjacency, `|s−ω₀ c| ≤ 2W^{-1/2}`); conclusion unchanged (`≤ |s−ω₀ c|·4·cltCoefSum F b·W^{-D'}`). `cltGoodAt`: `(∀σ x y, ‖G‖ ≤ 2) ∧ ∀σ x y, θ ≤ zdistInf(blk x − blk y) → ‖G‖ ≤ W^{-D'}`.

### Consumer check

| statement | user | scale of use | verdict |
|---|---|---|---|
| `cltCoord_adj` | S5-21 (RBM2D `CltStep.lean:342`) | `zdistInf ≤ 1` (cube, `3^d`) | closes |
| `cltFarGeomHalf` | S5-21 (`:407`, case A/B) | `R = 10(log W)^3 ℓ_s`, `STCltIsoConcl` (`Step5Pins.lean:418-421`: isolation of the first coordinates `b i 0`, window `(log W)^3 ℓ_s`) | closes; RBM2D's `hiso` `W^{2τ}ℓ_u` and `hw : 6 ≤ W^τ` are not needed |
| `cltPath_bound` | S5-21 twice (`:426` case A, `:524` case B) | `ρ=w`, `R=10w` (θ = 4w−1) | closes (row 6) |
| `cltEta_lower`, `cltCk` | S5-21 (`:636`), `CltDecorrelation.lean:324` | `N=(WL)^3`, `δ ≤ 2𝔡/d` | closes (script d) |
| `cltEval_det_le` | S5-21 (`:648`), `CltDecorrelation.lean:328-330` | `N^{a}`, `a = C'+3K+2` | closes (`N` only through `card Idx`) |
| `cltPert_*`, `cltDeriv_*` | inside `cltPath_bound` only | step `|t| ≤ 2W^{-1/2}` | closes (row 1) |
| S5-20 `CltGood.lean` | — | uses none of these names (grep, 0 hits); supplies the event `θ ≤ dist ∧ W^{-D'} < ‖G‖` | threshold `θ ≥ c w` from `STFarEntryAtLog` |

No constant fails to close under the re-scaling; the `W^{-1/2}` step is dimension-free (rows 1–3) and `W^{-1/2}/std ≥ W^{(d-1)/2}` at `d=3`.
**Finding F1 (not a scale failure).** `STcltB`/`STcltX` take two labels `b : Fin 2 → Zd d L` (`Step5Pins.lean:399,404`) and `STLKM` is generic in `k` (`Induction/Step2Defs.lean:68`), while `cltY F E s M b := F.eval E s M (fun _ => b)` (`Case3Defs.lean:63`) and `CltStep` (`:272`) are one-label. `LocalForm` already has `k` labels. Recommendation for 1b, inside the sole files: state `cltY`, `cltYo`, `cltCoefSum`, `CltDerivEval`, `CltPathBound` for `k` labels (`b : Fin k → Zd d L`, `F.coef b`, hypothesis `∀ m, R/2 ≤ |[c.1] − b m|`); `k = 1` is the ticket's statement. For a 2-label cluster with window `w`, `cltFarGeomHalf` at `R=10w` on first coordinates gives `5w` from `b_{·,0}` and `4w` from `b_{·,1}`; with `ρ = w+1` (locality sum of `x∈[b_0], y∈[b_1]` is `≤ w`) `θ = 4w−ρ−1 = 3w−2 ≥ w` for `w ≥ 1` (script a: `c=1` ok, `c=3` not at `ρ=w+1`), so use `c ≤ 2` in `STFarEntryAtLog`. Paper-delta candidate `T2144a`: label count `k` in the CLT vocabulary (RBM2D one-label).
**Not ported / changed.** RBM2D `3 ≤ L` in `CltCoordAdj` (not needed); `spectralZ` → `zt`; `gEntry` defined here (no merged one).

### Verdicts
* Target 1 (vocabulary `LocalForm`, `eval`, `Local ρ`, `gEntry`, `cltY`): **PASS**.
* Target 2 (`CltResolvent` port with `ρ`, `R` geometry): **PASS** (row 6; exhaustive check `L=5,6,7`).
* Target 3 (`CltPath` port): **PASS** (instance on `szCL` at `n=0`, all hypotheses concrete).
* Consumer check: no constant breaks; finding F1 (label count) for the dispatcher/1b.

## (b) Script output — Sun Oct  4 17:38:54 UTC 2026

```
$ git diff --stat main...t/T2144; git log -1; wc -l <files>
 RBM3D/Evolution/CltPath.lean      |  551 ++++++++++++++++++
 RBM3D/Evolution/CltResolvent.lean | 1118 +++++++++++++++++++++++++++++++++++++
 2 files changed, 1669 insertions(+)
d846287 Jun Yin <321276894+JYin80@users.noreply.github.com>
    1118 RBM3D/Evolution/CltResolvent.lean
     551 RBM3D/Evolution/CltPath.lean
    1669 total
```
```
$ lake build RBM3D.Evolution.CltResolvent
Build completed successfully (3299 jobs). exit=0
$ lake build RBM3D.Evolution.CltPath
Build completed successfully (3777 jobs). exit=0
$ lake build   (whole library; root RBM3D.lean does not import the new modules yet, the hub adds the imports at merge)
Build completed successfully (3890 jobs). exit=0
$ lake env lean precheck.lean   (registry pre-check: import RBM3D, CltResolvent, CltPath; #assert_rbm_axioms)
axiom audit: 4452 theorems, 1604 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). exit=0
$ same with `import RBM3D` only (baseline)
axiom audit: 4435 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
`#print axioms` lines at the end of the two files (build output), 19 declarations (11 + 2 target theorems, 6 instance checks):
```
cltPert_max_le, cltPert_sub_le, cltDeriv_entry, cltDeriv_eval_le, cltDeriv_evalMulti_le, cltEta_lower, cltEval_det_le, cltEval_detMulti_le, cltFarGeomHalf, cltFarGeomNear, cltCoord_adj, cltres_chk_witness, cltres_chk_near, cltres_chk_half, cltPathMulti_bound, cltPath_bound, cltpath_chk_szCL, cltpath_chk_szCL_multi, cltpath_chk_nondeg
19 declarations depend on exactly: [propext, Classical.choice, Quot.sound]
```

Statements new or changed against RBM2D, extracted from the files (collapsed whitespace; `CltRes` = CltResolvent.lean, `CltPat` = CltPath.lean):
```
CltRes:87  def Local (F : LocalForm d L W k K) (ρ : ℝ) : Prop := ∀ b j q, F.coef b j q ≠ 0 → ∀ i, ∃ m : Fin k, ((zdistInf d L ((split d L W (q i).1).1 - b m) + zdistInf d L ((split d L W (q i).2.1).1 - b m) : ℕ) : ℝ) < ρ
CltRes:61  def gEntry (E s : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) (x y : Idx d L W) : ℂ := Gres M (zt E s) σ x y
CltRes:224  def CltFarGeomNear : Prop := ∀ (d L : ℕ) [NeZero L] (ρ R : ℝ) (a a' b x : Zd d L), R / 2 ≤ (zdistInf d L (a - b) : ℝ) → zdistInf d L (a' - a) ≤ 1 → (zdistInf d L (x - b) : ℝ) < ρ → R / 2 - ρ - 1 ≤ (zdistInf d L (x - a) : ℝ)
      ∧ R / 2 - ρ - 1 ≤ (zdistInf d L (x - a') : ℝ)
CltRes:235  def CltCoordAdj : Prop := ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (c : CoordF d L W), (gvarF d L W g c ≠ 0 → zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1) ∧ (∀ i j, coordinateMatrix d L W c i j ≠ 0 →
      (i = c.1 ∧ j = c.2.1) ∨ (i = c.2.1 ∧ j = c.1)) ∧ (∀ i j, ‖coordinateMatrix d L W c i j‖ ≤ 1)
CltPat:83  def cltGoodAt (d L W : ℕ) [NeZero L] [NeZero W] (E u θ D' : ℝ) (ω : Ω d L W) : Prop := (∀ σ x y, ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ 2) ∧ ∀ σ x y, θ ≤ (zdistInf d L ((split d L W x).1 - (split d L W y).1) : ℝ) →
      ‖gEntry d L W E u (Hflow d L W u ω) σ x y‖ ≤ (W : ℝ) ^ (-D')
CltPat:110  def CltPathBound (d L W : ℕ) [NeZero L] [NeZero W] : Prop := ∀ (K : ℕ) (F : LocalForm d L W 1 K) (E u ρ R θ D' : ℝ) (b : Zd d L) (c : CoordF d L W) (ω₀ : Ω d L W) (s : ℝ), 0 ≤ u → u < 1 → (zt E u).im ≠ 0 → F.Local ρ → 16 *
      (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 → zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 → R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b) : ℝ) → θ ≤ R / 2 - ρ - 1 → cltGoodAt d L W E u θ D' ω₀ → |s - ω₀ c| ≤ 2 * (W : ℝ) ^
      (-(1 / 2 : ℝ)) → ‖cltYo F E u (Function.update ω₀ c s) b - cltYo F E u ω₀ b‖ ≤ |s - ω₀ c| * 4 * cltCoefSum F b * (W : ℝ) ^ (-D')
CltPat:97  def CltPathBoundMulti (d L W k : ℕ) [NeZero L] [NeZero W] : Prop := ∀ (K : ℕ) (F : LocalForm d L W k K) (E u ρ R θ D' : ℝ) (b : Fin k → Zd d L) (c : CoordF d L W) (ω₀ : Ω d L W) (s : ℝ), 0 ≤ u → u < 1 → (zt E u).im ≠ 0 →
      F.Local ρ → 16 * (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 → zdistInf d L ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 → (∀ m, R / 2 ≤ (zdistInf d L ((split d L W c.1).1 - b m) : ℝ)) → θ ≤ R / 2 - ρ - 1 → cltGoodAt d L W E u θ D' ω₀ → |s
      - ω₀ c| ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) → ‖cltEvalAt F E u (Function.update ω₀ c s) b - cltEvalAt F E u ω₀ b‖ ≤ |s - ω₀ c| * 4 * cltCoefSumMulti F b * (W : ℝ) ^ (-D')
```
Script `dictdiff.py`: each RBM2D statement (`git show c9a24cf:...`) with the textual dictionary applied (`Z2 L`→`Zd d L`, `zdist2 L`→`zdistInf d L`, `Idx L W`→`Idx d L W`, `Coord`→`CoordF`, `spectralZ`→`zt`, `splitEquiv`→`split`, `(W*L)^2`→`(W*L)^d`, extra `d`), token diff against the RBM3D statement:
```
0 differing token runs: cltCoordDir, CltPertMaxLe, CltPertSubLe, CltDerivEntry, CltDerivEval, cltCk, CltEtaLower, CltEvalDetLe, CltFarGeomHalf, cltYo
CltFarGeomNear: 5 differing token runs after dictionary
   2D→3D: [w ℓ] → [ρ R]
   2D→3D: [6 ≤ w → 1 ≤ ℓ → w ^ 2 * ℓ] → [R]
   2D→3D: [ℓ * w] → [ρ]
   2D→3D: [ℓ * w] → [R / 2 - ρ - 1]
   2D→3D: [ℓ * w] → [R / 2 - ρ - 1]
CltCoordAdj: 3 differing token runs after dictionary
   2D→3D: [] → [( g : ℝ )]
   2D→3D: [W], 3 ≤ L → ∀] → [W] (]
   2D→3D: [W,] → [W ) ,]
cltCoefSum: 2 differing token runs after dictionary
   2D→3D: [∑ j : Fin ( K + 1 ) , ∑ q : Fin j → Idx d L W × Idx d L W × Bool, ‖F.coef] → [cltCoefSumMulti F]
   2D→3D: [j q‖ * ( j : ℝ ) * 4 ^ ( j : ℕ )] → []
cltGoodAt: 3 differing token runs after dictionary
   2D→3D: [] → [d L W : ℕ ) [NeZero L] [NeZero W] (]
   2D→3D: [ρ] → [θ]
   2D→3D: [ρ] → [θ]
CltPathBound: 6 differing token runs after dictionary
   2D→3D: [τ] → [ρ R θ]
   2D→3D: [τ u → 6 ≤ ( W : ℝ ) ^ τ → 1 ≤ ellT L u] → [ρ]
   2D→3D: [( ( W : ℝ ) ^ τ ) ^ 2 * ellT L u] → [R]
   2D→3D: [] → [θ ≤ R / 2 - ρ - 1 →]
   2D→3D: [] → [d L W]
   2D→3D: [( ellT L u * ( W : ℝ ) ^ τ )] → [θ]
```
Compiled instances (script `instmap.py`: target <- private check theorem:line in the same file that applies it, every hypothesis proved in the check, none left open; data in narrative):
```
cltPert_max_le <- cltres_chk_M1:924; cltPert_sub_le <- cltres_chk_M2:931; cltDeriv_entry <- cltres_chk_M3:949; cltDeriv_eval_le <- cltres_chk_M4:976; cltDeriv_evalMulti_le <- cltres_chk_M4Multi:989; cltEta_lower <- cltres_chk_E4:1010;
  cltEval_det_le <- cltres_chk_M5:1015; cltEval_detMulti_le <- cltres_chk_M5Multi:1025; cltFarGeomHalf <- cltres_chk_half:1035; cltFarGeomNear <- cltres_chk_near:1061; cltCoord_adj <- cltres_chk_dir:854, cltres_chk_adj:1072;
  cltPath_bound <- cltpath_chk_szCL:486; cltPathMulti_bound <- cltpath_chk_szCL_multi:510
```
The `cltPath_bound` instance at `szCL`, `n = 0` (statement as in the file; every hypothesis of the theorem is proved in the check, see `cltpath_chk_good`, `cltpath_chk_local`, `cpx_far`, `cltpath_chk_step`):
```
CltPat:486  private theorem cltpath_chk_szCL : ‖cltYo (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 (1 / 2) (Function.update 0 cpc cpS) 0 - cltYo (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L
      0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 (1 / 2) 0 0‖ ≤ |cpS - (0 : Ω 3 (szCL.L 0) (szCL.W 0)) cpc| * 4 * cltCoefSum (cltpath_chkForm 1 (fun _ => (0 : Zd 3 (szCL.L 0))) (0 : Idx 3 (szCL.L 0) (szCL.W 0))) 0 * (((szCL.W 0 : ℕ) :
      ℝ)) ^ (-(1 : ℝ))
szCL n=0: L=15925248 W=16777216 log W=16.6355 w=(log W)^3=4603.73
rho=w=4603.73 R=10w=46037.33 R/2=23018.66 <= 70000 (block distance of x1): True; 2*70000 <= L: True
theta=R/2-rho-1=18413.93  theta/w=3.9998 (>=1: True, >=3: True)
16 W^(-1/2) = 0.00391 <= 1; step s = W^(-1/2) = 2.441e-04; |s|<=2W^(-1/2)
Z_(WL)^3 side W*L = 267181325549568; 70000*W = 1174405120000 < W*L: True
```
```
$ name-clash grep of the 36 new public names in `main` (3b1c6a5), `git grep ... main -- RBM3D | wc -l`
       0
```
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the four ported files>   (sources were read with `git show c9a24cf:<file>`, not from the working tree)
RBM2D HEAD 9e0f275
 RBM2D/Evolution/Case3Defs.lean    |  88 +++------
 RBM2D/Evolution/CltPath.lean      |  86 ++-------
 RBM2D/Evolution/CltResolvent.lean | 372 ++++++--------------------------------
 RBM2D/Induction/Defs.lean         | 259 +++++++-------------------
 4 files changed, 163 insertions(+), 642 deletions(-)
```
Consumer check, `grep -n` of the names in RBM2D at `c9a24cf` (line numbers; empty = no use; lines 26-31 of `CltStep.lean` are its module docstring):
```
CltStep.lean: cltCoord_adj:26,342, cltFarGeomHalf:26,407, cltFarGeomNear: cltPath_bound:27,28,269,426,524, cltEta_lower:636, cltEval_det_le:31,648, cltDeriv_eval_le: cltPert_max_le: cltPert_sub_le: cltDeriv_entry:  | CltGood:
CltDecorrelation:322,330,
```

### Narrative

* Delivered: `RBM3D/Evolution/CltResolvent.lean` (vocabulary `gEntry`, `LocalForm` with `eval`, `Local ρ`, `cltY`; the eleven definitions/pins of RBM2D `CltResolvent` with their proofs) and `RBM3D/Evolution/CltPath.lean` (`cltYo`, `cltCoefSum`, `cltGoodAt`, `CltPathBound`, `cltPath_bound`), commit `d846287` on `t/T2144`, only the two writable files (diff-stat above); `Test/Axioms.lean` untouched, the pre-check exits 0.
* Source: RBM2D at `c9a24cf` via `git show` (the RBM2D working tree is at `9e0f275` and differs: diff-stat above). Mathlib and Lean pins of RBM2D and RBM3D are equal (`lean-toolchain` v4.34.0, mathlib rev `5ed2965`), so the Mathlib names of the ported proofs are unchanged.
* `dictdiff.py` shows the statements of `cltCoordDir`, `CltPertMaxLe`, `CltPertSubLe`, `CltDerivEntry`, `CltDerivEval`, `cltCk`, `CltEtaLower`, `CltEvalDetLe`, `CltFarGeomHalf`, `cltYo` equal to RBM2D's after the dictionary; the changes are exactly the re-scaled ones: `CltFarGeomNear` (`ρ`, `R`; proof is the triangle inequality, no hypothesis on `ρ`, `R`, so RBM2D's `6 ≤ w` and its `nlinarith` step are gone), `CltCoordAdj` (`g` explicit, `3 ≤ L` dropped), `cltGoodAt` and `CltPathBound` (`ρ`, `R`, `θ ≤ R/2 - ρ - 1` in place of `τ`, `ellT`, `6 ≤ W^τ`, `1 ≤ ellT`), `Local ρ`.
* Adjacency: `gvarF c ≠ 0` gives `sbKernelR ((split c.1).1 - (split c.2.1).1) ≠ 0`, whose support is `{0} ∪ {zdistD = 1}` (`Defs/Block.lean:74`); with `zdistInf_le_zdistD` this gives `zdistInf ≤ 1` for every `g` and `L`. The conclusion is in `zdistInf` (RBM2D: `zdist2`), as the `R`-forms need.
* Label count (finding F1 of section (a)): every statement that mentions labels has the one-label form of RBM2D (names kept) and a `Multi` form with `b : Fin k → Zd d L`, `F.eval`, `∀ m, R/2 ≤ |[c.1] - b m|`: `CltDerivEvalMulti`, `CltEvalDetLeMulti`, `CltPathBoundMulti`, `cltPathMulti_bound`, `cltDeriv_evalMulti_le`, `cltEval_detMulti_le`; the one-label theorems are one-line corollaries at `k = 1` (`cltCoefSum F b := cltCoefSumMulti F (fun _ => b)`, `cltY F E s M b := F.eval E s M (fun _ => b)`).
* Lean differences in proofs: `RBM.isUnit_sub_smul_of_isHermitian` for RBM2D's `isUnit_sub_smul_one_of_im_ne_zero`; the derivative of the resolvent is the merged `hasDerivAt_green_moving` (`hasDerivAt_lineInverse` has no merged copy); `gEntry := Gres M (zt E s) σ x y` (no merged `gEntry`, grep: 0 hits in `main`) with the private bridge `cltres_gEntry_eq` to `green`; the entry bound is `norm_Gsig_le_inv_eta` + `norm_matrix_entry_le_opNorm`; `zdistInf` has only private triangle/neg lemmas (grep: `EntryDom.lean:105`, `Green/Pins.lean:501`, `Evolution/PropTInf.lean:43`, `Induction/B45.lean:904,914`), re-proved privately (`cltres_zdistInf_*`, `cltpath_zdistInf_neg`).
* Instances (data in the file headers): `d = 3`, `L = 3`, `W = 1`, `g = 1/2` (`N = 27`), `M = 0`, `E = 0`, `u = 1/2`, `t = 1/8`, `κ = 1`, `δ = 1/2`, `K = 1`; `cltres_chk_witness` takes one coordinate with `gvarF ≠ 0`, `c.1 ≠ c.2.1`, entry `1` and applies M1, M3, M4 at it; the geometry is applied on `Z_7^3` (`R = 3`, `m = 2`) and `Z_61^3` (`ρ = 1`, `R = 16`, `a = (10,0,0)`, `a' = (11,0,0)`, `x = 0`, conclusion `6 ≤ |x-a|, |x-a'|`). The `cltPath_bound` instance is on `szCL` at `n = 0` with `ρ = w`, `R = 10 w`, `θ = R/2 - ρ - 1`, `w = (log W)^3 ℓ_s` (`cpw`, `cpw_eq` via `szCL_ellT_s`); `ω₀ = 0`, so `Hflow = 0` and the resolvent is diagonal (`cltpath_gEntry_zero`); `cltpath_chk_nondeg`: `s > 0`, coefficient weight `≥ 4`, `θ ≥ w` and `θ ≥ 3 w` (numbers in the script output). The same data are applied to `cltPathMulti_bound` with two labels.
* Consumer check (grep above; the ticket's S5-20/S5-21): RBM2D `CltStep` uses `cltCoord_adj` (`:342`), `cltFarGeomHalf` (`:407`, with `R = W^{2τ} ℓ_u`), `cltPath_bound` (`:426` case A, `:524` case B), `cltEta_lower` (`:636`), `cltEval_det_le` (`:648`); `CltDecorrelation` uses `cltEta_lower` (`:322`), `cltEval_det_le` (`:330`); `CltStep` uses none of `cltFarGeomNear`, `cltDeriv_*`, `cltPert_*`; `CltGood` uses none of the five names grepped. At d ≥ 3 the scale enters only through the free reals `ρ`, `R`, `θ` and through `N = (W L)^d` (E4, M5: `N` appears only via `card_Idx`); M1-M3, the step length `|s - ω₀ c| ≤ 2 W^{-1/2}` and `16 W^{-1/2} ≤ 1` do not involve `d` or the scale. No constant fails to close; nothing to stop on.
* Not ported: RBM2D's checks `cltres_chk_near_needs_w` and `cltpath_chk_item7_fails_W3` (counterexamples for `6 ≤ w` and `W = 3`; no such hypotheses here); the private `cltres_cltY_le` (replaced by `cltres_eval_le` with `k` labels), `zdist_neg_T2125`, `zdist2_neg_T2125`, `cltpath_coordEntry`, `cltpath_zdist2_neg` (replaced by `cltCoord_adj` conjuncts and the private `zdistInf` lemmas). No public RBM2D pin of the two files is dropped. Section (a) was not edited; no correction was needed, so there is no (a′).

## (c) Verified Mathlib and merged names (`#check @name`, signature truncated to 100 characters; all other Mathlib names are those of the RBM2D proofs, same Mathlib rev)

```
Matrix.inv_eq_right_inv : ∀ {A B : Matrix n n α}, A * B = 1 → A⁻¹ = B
Matrix.one_apply_ne : ∀ {i j : n}, i ≠ j → 1 i j = 0
Finset.single_le_sum : ∀ {f : ι → N} {s : Finset ι} [AddLeftMono N], (∀ i ∈ s, 0 ≤ f i) → ∀ {a : ι},
Finset.le_sup : ∀ {s : Finset β} {f : β → α} {b : β}, b ∈ s → f b ≤ s.sup f
Finset.sup_le : ∀ {s : Finset β} {f : β → α} {a : α}, (∀ b ∈ s, f b ≤ a) → s.sup f ≤ a
ZMod.val_natCast_of_lt : ∀ {n a : ℕ}, a < n → (↑a).val = a
Real.le_sqrt_of_sq_le : ∀ {x y : ℝ}, x ^ 2 ≤ y → x ≤ √y
Nat.mul_div_cancel : ∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
RBM.isUnit_sub_smul_of_isHermitian : ∀ {H : Matrix n n ℂ}, H.IsHermitian → ∀ {z : ℂ}, z.im ≠ 0 → IsUnit 
RBM.Gauss.hasDerivAt_green_moving : ∀ {H : ℝ → Matrix n n ℂ} {z : ℝ → ℂ} {H' : Matrix n n ℂ} {z' : ℂ} {u : ℝ},
RBM.Gauss.norm_Gsig_le_inv_eta : ∀ {H : Matrix n n ℂ}, H.IsHermitian → ∀ {z : ℂ} {η : ℝ}, 0 < η → η ≤ |z.im| →
RBM.Gauss.norm_matrix_entry_le_opNorm : ∀ (M : Matrix n n ℂ) (p q : n), ‖M p q‖ ≤ ‖M‖
RBM.zt_im : ∀ (E t : ℝ), (zt E t).im = (1 - t) * (mE E).im
RBM.mE_im : ∀ (E : ℝ), (mE E).im = √(4 - E ^ 2) / 2
RBM.Gauss.card_Idx : ∀ (d L W : ℕ) , Fintype.card (Idx d L W) = (W * L) ^ d
RBM.Gauss.Xmat_update : ∀ (d L W : ℕ) (ω : Ω d L W) (c : CoordF d L W) (t : ℝ), Xmat d L W (Function.update ω 
RBM.Gauss.Hflow_isHermitian : ∀ (d L W : ℕ) (u : ℝ) (ω : Ω d L W), (Hflow d L W u ω).IsHermitian
RBM.zdist_add_le : ∀ (L : ℕ) [NeZero L] (u v : ZMod L), zdist L (u + v) ≤ zdist L u + zdist L v
RBM.zdist_neg : ∀ (L : ℕ) [NeZero L] (u : ZMod L), zdist L (-u) = zdist L u
RBM.Gauss.zdistInf_le_zdistD : ∀ (d L : ℕ) (x : Zd d L), zdistInf d L x ≤ zdistD d L x
RBM.Gauss.idxKey_lt_or_eq_or_lt : ∀ (d L W : ℕ) (i j : Idx d L W), idxKey d L W i < idxKey d L W j ∨ i = j ∨ i
RBM.Gauss.Step5Inst.szCL_ellT_s : ∀ (n : ℕ), ellT (Step5Inst.szCL.L n) (Step5Inst.szCL.lam n) (Step5Inst.sCL n
RBM.Gauss.Step5Inst.szCL_log_W_le : ∀ (n : ℕ), Real.log ↑(Step5Inst.szCL.W n) ≤ ↑n + 24
RBM.Gauss.Step5Inst.szCL_one_le_log_W : ∀ (n : ℕ), 1 ≤ Real.log ↑(Step5Inst.szCL.W n)
RBM.Gauss.Sizes.neZeroL : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), NeZero (sz.L n)
```
(No name was checked as absent. `Real.sqrt_eq_rpow` is stated for `x ^ (1/2)`; the instances `cltres_chk_R`, `cltpath_chk_step` use it.)

## (d) Open issues and paper-delta candidates — Sun Oct  4 17:39:35 UTC 2026

* S5-21 instantiation (not done here): for the two-label `STcltB`, S5-21 has to choose `ρ`, `R`, `θ` in `CltPathBoundMulti` (`Local ρ` sums the distances to ONE label `b m`; the far hypothesis is `∀ m`, i.e. both labels of a cluster). The arithmetic of the 2-label cluster (`ρ = w + 1`, `θ = 3 w - 2`, `c ≤ 2` in `STFarEntryAtLog`) is the claim of section (a), script (iii-a); I did not re-verify it beyond `inst_szcl.py` above, which is the 1-label case `ρ = w`, `R = 10 w`.
* Hub: add `import RBM3D.Evolution.CltResolvent` and `import RBM3D.Evolution.CltPath` after the last `import` line of `RBM3D.lean`; `CltPath` imports `RBM3D.Induction.Step5Pins` (for `szCL`) and `CltResolvent` imports `RBM3D.Evolution.CltSwap`, `RBM3D.Gauss.FlowCalculus`, `RBM3D.Green.EntryCore`.
* Public names that the ticket does not pin (CLAUDE.md §3 (E)): `CltDerivEvalMulti`, `cltDeriv_evalMulti_le`, `CltEvalDetLeMulti`, `cltEval_detMulti_le`, `CltPathBoundMulti`, `cltPathMulti_bound`, `cltEvalAt`, `cltCoefSumMulti`; deliberate (F1, the `k`-label statements S5-21 needs), all with the `clt` prefix; every other helper is `private` with the `cltres_`/`cltpath_` prefix.
* Paper-delta candidates (Lean/route differences; the paper omits the proof of `eq:bound_isolated` (`3_5_Loop_Hierarchy.tex:2245-2248`: "exactly the same as that for [DYYY25, (7.39)] and [RBSO1D, (A.112)]"), so the replacement step is not in it):
  * `T2144a`: the local-form vocabulary carries the label count `k`; RBM2D has `k = 1` in `cltY`, `CltDerivEval`, `CltEvalDetLe`, `CltPathBound` (the `Multi` forms are the `k`-label statements).
  * `T2144b`: `CltFarGeomNear` has locality radius `ρ` and separation `R` (conclusion `R/2 - ρ - 1`); RBM2D has `w ≥ 6`, `ρ = ℓ w`, `R = w^2 ℓ`.
  * `T2144c`: `CltCoordAdj` takes `g` explicitly, needs no `3 ≤ L`, and its adjacency is `zdistInf ≤ 1` (the `sbKernelR` support has `2d + 1` points, the `∞`-ball `3^d`).
  * `T2144d`: `cltGoodAt`/`CltPathBound` take the far threshold `θ` with `θ ≤ R/2 - ρ - 1` (RBM2D: `ρ = ℓ W^τ`); `gEntry` is the merged `Gres` entry; `Local ρ` has `ρ` as a parameter.
