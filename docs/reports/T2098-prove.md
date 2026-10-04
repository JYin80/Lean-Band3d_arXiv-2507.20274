Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 01:57:42 UTC 2026

Targets (ST2-26; RBM2D `Path/Expansion` at `c9a24cf`, 1159 lines): defs `Avec`, `martInc`, `predInc`, `StoppedDuhamel105`; `stoppedDuhamel105`; `condExp_A_succ` (drift split, `Dgrid`, `Rgrid`); `grid_expansion_all`; the bridge `stepZ_ukerMat_eq_Uker` ... `grid_expansion_all'` (RBM2D 636-1056). All are deterministic or a.e. statements at fixed `(d,L,W,g)` and fixed `n`; no external hypothesis (no limit computation needed).
Math: `A_k = L_{(+,-),a}(H_k, z_{u_k}) - K_{u_k}(a)`, `K_u = W^{-d}|m|^2 Θ_{u|m|^2}`, `|m|^2 = 1`; `U_{v,w} = (1 - vS)Θ_w` per slot; `pred_j + mart_j = A_{j+1} - U_{u_j,u_{j+1}} A_j` (the conditional mean cancels); Duhamel telescope; `pred_j = Δ D_j + R_j` with `R_j` by subtraction and the bound `‖R_j‖ ≤ envConst Δ^{3/2} + 7 N η_{u_{j+1}}^{-4} Δ^2`.

### (i) Exponent table
**A. Every `W^2` / `Z2` occurrence** (command `bash cnt.sh`, scratchpad `T2098/`, on `git show c9a24cf:RBM2D/Path/Expansion.lean`; output = RBM2D line numbers):
```
total lines:     1159
== Z2 : 49 56 62 213 246 313 320 325 334 409 412 426 438 461 544 547 561 636 641 649 650 653 656 668 669 686 687 690 701 719 721 735 736 740 757 759 760 762 764 768 773 775 790 792 793 795 806 809 833 840 845 851 862 898 927 961 977 1025 1090 1096 1111 
== \^ 2|\^2 : 213 249 255 258 261 275 279 298 301 302 303 336 337 338 349 368 369 371 372 373 374 376 380 381 383 384 385 393 394 396 397 398 417 516 517 519 520 523 524 530 552 570 1103 
== W\)⁻¹\) \^ 2|W : ℝ\)⁻¹\) \^ 2|d\.W n : ℝ\)⁻¹ \^ 2 : 249 298 301 302 303 337 
== d\.L n \* d\.W n\) \^ 2 : 336 519 520 524 530 
== d = 2 : 13 625 
== scaleM|ellT|tailT|ellStar|Meta|ellz : 
```
| RBM2D token (lines) | `d >= 3` replacement | why it holds |
|---|---|---|
| `Z2 L` (49,56,62,... 61 lines, list above), `Idx L W` (185,196,641,...) | `Zd d L`, `Idx d L W` | sums over labels and `SB`; no step uses `d`; `‖SB‖_{ℓ∞ op} = 1` needs only `3 <= L` (row sums of `S^(B)` are 1: `Block.lean:123,136`) |
| `((W:ℂ)⁻¹)^2` in `Kpm` (213), `((W:ℝ)⁻¹)^2` (249,298,301-303,338,349,516,523) | `((W:ℂ)^d)⁻¹`, `((W:ℝ)^d)⁻¹` =: `w` | `kTwo = (W^d)⁻¹ (m m) Θ_{t(m m)}` (`Loop/Primitive.lean:46`), `m(+)m(-) = |m|^2 = 1`; numerically: `A_0 = 0` at `H = 0, u = 0` needs `K_0 = W^{-d} = 1/8`; with `W^{-2} = 1/4` the defect is `1.25e-01` (output below) |
| `(d.L n * d.W n)^2` (336,519,520,524,530) | `(W L)^d = sz.size n` (`Defs/Sizes.lean:157`) | `card Vtx = (L W)^d` (`Gauss/FlowCalculus.lean`, `card_BlockIndex`), used by the crude bound `‖L‖ <= N (η⁻¹ W^{-d})^2` (`norm_gloop_le_crude`, `FlowCalculus.lean:708`, loop length 2); `N = 216 >= 1` |
| `((d.W n:ℝ)⁻¹ ^ 2)^2` inside the crude bound (337) | `(η⁻¹ (W^d)⁻¹)^2` | same lemma, `length = 2`: `(η⁻¹ W^{-d})^2`, so `W^{-2d}` in total, not `W^{-4}` |
| `^ 2` in `Expansion_arith` (368-398), `Δ^2`, `(1-u)⁻¹^2` | unchanged | `w <= 1`, `N >= 1`, `a,b,c <= x`, `1 <= x` only; `d` enters through `w`, `N` only; slack in the table B |
| `^ 2` at 570 (`Δ^2 <= Δ^{3/2}`), `3/2` (415,550,565) | unchanged | exponent `3/2` is the `OneStepEnvelope` exponent (`Δ^{3/2}`, `OneStep.lean:85`); `Δ <= 1` since `Δ <= u_{j+1} < 1` |
| `d = 2` in docstrings (13, 625) | none | `scaleM, ellT, tailT, ellStar, Meta, ellz`: no occurrence (grep above); `etaT E u` only |
| `normSq (spectralM E) = 1` (64,75,127,...) | `normSq (mE E)`, `= 1` from `‖m‖ = 1` (`norm_mE`, `Semicircle.lean`) | dimension-free; used to set `ξ = 1` in `Uop` and `K` |
| `Sizes d` -> `sz : Sizes d`; `envConst (L n) (W n) E 2 v` -> `envConst d (L n) (W n) E 2 v` | `envConst = 16 (k+3)^4 N^4 (1+η_v⁻¹)^{k+4}`, `N = (WL)^d` (`OneStep.lean:78`) | `d` only through `N` |

**B. Constants and slacks** (`d = 3`, `L = 3`, `W = 2`, `N = 216`, `w = 1/8`, `g = 1/2`, `E = 0.7`, times of the instance below):

| item | value | constraint | slack |
|---|---|---|---|
| `|E|` | 0.7 (and 0) | `|E| < 2` (`etaT_pos`, `Loop/GLoop.lean:83`) | `2 - |E| = 1.3` |
| window `s, t, K` | `s = 0.25`, `t = 0.45`, `K = 2`, `Δ = 0.1` | `0 <= s <= t < 1`, `K != 0`, `min(k,τ) <= K`; so `u_j <= t < 1` | `1 - t = 0.55`; boundary runs `s = 0` (`H_0 = 0`), `t = 0.998` (`η_t = 1.873e-3`), `Δ = 0` (`s = t`) below |
| `‖SB‖`, `‖Θ_u‖` | 1, `<= (1-u)⁻¹` | `3 <= L` (`norm_SB`), `u in [0,1)` | equality at `L = 3`: row sums `1.000000000000000` (output line 1) |
| `Kpm` step | `w a b^2 Δ^2` with `a = (1-u')⁻¹`, `b = (1-u)⁻¹` (two resolvent identities) | exact when `S = I` | at `g = 1/64`, `Δ = 0.2` (second run): actual `8.78e-03` vs bound `8.82e-03` (ratio 0.995): sharp |
| `Uop` step | `3 Δ^2 a^2 α`, `α = N (η_u⁻¹ w)^2 + w b` (`uopOneStep`, `3 = 1+1+1`) | row sums of `ukerMat`-difference `<= Δ β^2` | actual `7.78e-05` vs `4.97e-01` |
| `Expansion_arith` | `w a b^2 Δ^2 + 3Δ^2 a^2 (N (c w)^2 + w b) <= 7 N x^4 Δ^2`, `x = η_{u'}⁻¹` | `w <= 1`, `N >= 1`, `a,b,c <= x`, `1 <= x`; `7 = (1+3) + 3` | `x^3 <= N x^4` and `4 x^3 + 3 N x^4 <= 7 N x^4` are tight only at `N = x = 1`; here ratio `219.7`, `231.4` (output) |
| `envConst Δ^{3/2}` | `16 (2+3)^4 N^4 (1+x)^6 Δ^{3/2}` | from `OneStepEnvelope`, loop length 2 | `2.3e+14` (vacuous numerically, valid) |
| `d`-dependence | only `w = W^{-d}` and `N = (WL)^d` | no `L`-`W` relation, no `n`-asymptotics used (`d, L, W, g` fixed) | none needed |

**C. Hypotheses that are not in the ticket's import list** (findings, no verdict change): the port uses `uopOneStep` (UBounds:553, constant `3`), `thetaGen` (UBounds:52), `normSqSpectralMOne` (UBounds:416) and `ukerNonneg` (UBounds:424) of RBM2D `Path/UBounds`; the ticket's dependencies are ST2-21/23/24 and T2097 (ST2-25, `Path/UBounds`) is `preflight-fail` and unmerged, and `StepDecompLoop_ukerNonneg` is `private` (`StepDecompLoop.lean:530`):
```
$ grep -rln "uopOneStep" RBM3D | wc -l
       0
$ sed -n 1p docs/queue/T2097.state
state: preflight-fail
$ grep -n "private theorem StepDecompLoop_ukerNonneg" RBM3D/Path/StepDecompLoop.lean | cut -c1-110
530:private theorem StepDecompLoop_ukerNonneg (hL : 3 ≤ L) {ξ v w : ℝ} (hξ : 0 ≤ ξ) (hv : 0 ≤ v)
$ sed -n 62,63p docs/reports/T2097-prove.md | cut -c1-120
- `thetaGenMat`, `thetaGen`, `normSqSpectralMOne` (UBounds:48,52,416): **PASS** (rows 1, 4).
- `ukerNonneg`, `ukerRowSum`, `sumNdecay`, `sumNdecayEta`, `uopBack`, `uopOneStep` (UBounds:424-553): **PASS** (rows 1-4
```
(T2097's `FAIL` is `tailtoTail`, a different target.) The proofs are dimension-free (T2097 report row 3, and `norm_SB` for any `d`); so they must be re-proved or copied here as `private` / `Expansion_`-prefixed (ST1-COMMON item 4), with `thetaGen` = merged `STthetaOp` at `σ = (+,-)` (`Induction/Step2Defs.lean:119`), not a new `thetaGen`. The U-step in the instance below confirms the statement at `d = 3`.

### (ii) One concrete nondegenerate instance
`d = 3, L = 3, W = 2` (`N = (WL)^d = 216`, `L^d = 27` labels, `27^2 = 729` pair labels), `g = 1/2`, `E = 0.7`, `s = 0.25`, `t = 0.45`, `K = 2` (`Δ = 0.1`, `u = 0.25, 0.35, 0.45`), one sample `(X_0, X_1, X_2)` of the model law (Hermitian, `Var X_ij = W^{-d} SBR`), stopping indices `min(k,τ) in {0,1,2}`. The conditional mean `E[A_{j+1}|F_j]` is replaced by an antithetic Monte Carlo value (3000 pairs): it cancels exactly in `pred + mart`, so the identity does not depend on it; `D_j := genMat(L_j) - ∂_u K - Θ-gen(A_j)` (= `ELKLK + EGt` by `hierarchyN2`), computed in closed form from the Gaussian covariance, and `R_j := pred_j - Δ D_j`.
Lean example data: merged `sz0` (`d = 3`, `L = 4`, `W = 32`, `lam = 1/64`), `n = 0`, `E = 0`, `s = 1/10`, `t = 1/2`, `K = 4` (as `LoopStep_check_step_sz0`); the second run below uses the same `E, s, t, g` with `K = 2` at `L = 3`, `W = 2`.
Commands (numpy, scratchpad `T2098/check.py`; exit 0): `python3 check.py 3000` (50 s) and `GG=0.015625 python3 check.py 1500`:
```
d=3 L=3 W=2 N=(WL)^d=216 L^d=27 W^d=8 g=0.5 SB rowsum min/max 1.000000000000000 1.000000000000000
--- main: E=0.7, s=0.25, t=0.45, K=2 (two grid steps)
E=0.7 s=0.25 t=0.45 K=2 Delta=0.1 u=[0.25, 0.35, 0.45] |m|^2=1.000000000000000 eta_t=0.5152
  loop literal tr(G E_a1 Gm E_a2) vs aggregated: |diff|=1.7e-21
  j=0: max|A_j|=8.982e-03  max|pred_j|=8.619e-04  max|Delta*D_j|=8.419e-04  max|R_j|=9.865e-05  MC max-stderr=2.98e-05
  j=1: max|A_j|=1.468e-02  max|pred_j|=1.131e-03  max|Delta*D_j|=1.117e-03  max|R_j|=1.007e-04  MC max-stderr=3.82e-05
  min(k,tau)=0: max|LHS|=8.9823e-03  max|LHS-RHS(105)|=8.67e-18  max|LHS-RHS(grid_expansion_all)|=8.67e-18
  min(k,tau)=1: max|LHS|=1.4684e-02  max|LHS-RHS(105)|=6.94e-18  max|LHS-RHS(grid_expansion_all)|=6.94e-18
  min(k,tau)=2: max|LHS|=1.7501e-02  max|LHS-RHS(105)|=1.73e-17  max|LHS-RHS(grid_expansion_all)|=1.73e-17
  j=0 max|R_j|=9.865e-05 <= envConst*D^1.5 + 7 N eta^-4 D^2 = 2.343e+14 (7N x^4 D^2 = 1.100e+02); K-step 5.23e-04 <= 3.42e-03; U-step 7.78e-05 <= 4.97e-01; |A_j|<=crude: True
  j=1 max|R_j|=1.007e-04 <= envConst*D^1.5 + 7 N eta^-4 D^2 = 4.454e+14 (7N x^4 D^2 = 2.146e+02); K-step 6.99e-04 <= 5.38e-03; U-step 1.50e-04 <= 9.22e-01; |A_j|<=crude: True
--- boundary s=0 (H_0=0), t=0.998: u_K close to 1
E=0.7 s=0.0 t=0.998 K=2 Delta=0.499 u=[0.0, 0.499, 0.998] |m|^2=1.000000000000000 eta_t=0.001873
  min(k,tau)=1: max|LHS|=1.8835e-02  max|LHS-RHS(105)|=2.08e-17  max|LHS-RHS(grid_expansion_all)|=2.08e-17
  min(k,tau)=2: max|LHS|=2.1235e+00  max|LHS-RHS(105)|=5.22e-14  max|LHS-RHS(grid_expansion_all)|=5.22e-14
  j=0 max|R_j|=3.195e-04 <= envConst*D^1.5 + 7 N eta^-4 D^2 = 7.226e+15 (7N x^4 D^2 = 7.761e+03); K-step 1.04e-02 <= 6.21e-02; U-step 3.58e-19 <= 1.18e+01; |A_j|<=crude: True
  j=1 max|R_j|=1.324e+00 <= envConst*D^1.5 + 7 N eta^-4 D^2 = 1.794e+29 (7N x^4 D^2 = 3.056e+13); K-step 2.33e+00 <= 6.20e+01; U-step 1.46e+00 <= 2.91e+06; |A_j|<=crude: True
--- boundary s=t=0.3 (Delta=0): all grid times equal
E=0.7 s=0.3 t=0.3 K=2 Delta=0 u=[0.3, 0.3, 0.3] |m|^2=1.000000000000000 eta_t=0.6557
  min(k,tau)=1: max|LHS|=1.7270e-02  max|LHS-RHS(105)|=0.00e+00  max|LHS-RHS(grid_expansion_all)|=0.00e+00
  min(k,tau)=2: max|LHS|=1.7270e-02  max|LHS-RHS(105)|=1.04e-17  max|LHS-RHS(grid_expansion_all)|=1.04e-17
normalisation: H=0,u=0: max|A_0| with W^d=8: 1.21e-18; if W^2=4 were used for K: 1.25e-01
Expansion_arith u=0.25 u'=0.35: w=0.1250 a=1.5385 b=1.3333 c=1.4234 x=1.6423 N=216: LHS=5.0076e-01 <= 7N x^4 D^2=1.1000e+02  ratio=219.7; 1<=x True, w<=1 True, a,b,c<=x True
Expansion_arith u=0.35 u'=0.45: w=0.1250 a=1.8182 b=1.5385 c=1.6423 x=1.9409 N=216: LHS=9.2726e-01 <= 7N x^4 D^2=2.1459e+02  ratio=231.4; 1<=x True, w<=1 True, a,b,c<=x True
Expansion_arith u=0.0 u'=0.499: w=0.1250 a=1.9960 b=1.0000 c=1.0675 x=2.1308 N=216: LHS=1.1881e+01 <= 7N x^4 D^2=7.7608e+03  ratio=653.2; 1<=x True, w<=1 True, a,b,c<=x True
--- second run (g = 1/64 = sz0.lam, E = 0):
--- sz0-like data: E=0, s=0.1, t=0.5, K=2
E=0.0 s=0.1 t=0.5 K=2 Delta=0.2 u=[0.1, 0.3, 0.5] |m|^2=1.000000000000000 eta_t=0.5
  j=1: max|A_j|=2.032e-02  max|pred_j|=1.648e-02  max|Delta*D_j|=9.941e-03  max|R_j|=6.538e-03  MC max-stderr=2.94e-04
  min(k,tau)=1: max|LHS|=2.0321e-02  max|LHS-RHS(105)|=3.47e-18  max|LHS-RHS(grid_expansion_all)|=3.47e-18
  min(k,tau)=2: max|LHS|=2.5034e-02  max|LHS-RHS(105)|=4.16e-17  max|LHS-RHS(grid_expansion_all)|=4.16e-17
  j=0 max|R_j|=8.706e-04 <= envConst*D^1.5 + 7 N eta^-4 D^2 = 3.995e+14 (7N x^4 D^2 = 2.519e+02); K-step 8.78e-03 <= 8.82e-03; U-step 1.10e-03 <= 1.05e+00; |A_j|<=crude: True
```
Reading: both sides of `stoppedDuhamel105` / `grid_expansion_all` agree to `1.7e-17` (main run) at `min(k,τ) = 0,1,2` (each side `~1.8e-02`, so the agreement is not `0 = 0`); `|R_j| ~ 1e-4` against `|Δ D_j| ~ 8e-4..1e-3` at MC stderr `3e-5`: the drift split with `W^d`, `N = (WL)^d` is the right one (it fails by a factor `2` in `K` for `W^2`). Boundaries: `s = 0` (`H_0 = 0`, `A_0 = 1.2e-18`, `u_K = 0.998`, `R_1 = 1.3` vs bound `1.8e+29`), `Δ = 0`: identity exact (`1e-17`), `R_j = 1.04e-17`, bound `0` (so `R_j = 0` up to rounding).

### Verdict per target
- `Avec`, `martInc`, `predInc`, `StoppedDuhamel105`, `stoppedDuhamel105`, `grid_expansion_all`, `grid_expansion`: **PASS** (exact algebra from the Duhamel telescope; hypotheses `|E|<2, 0<=s<=t<1, K!=0` hold together at the instance, including the `s = 0`, `t = 0.998`, `Δ = 0` boundaries).
- `condExp_A_succ`, `Expansion_condExp_A_succ_*` (`Dgrid`, `Rgrid`): **PASS** with `W^2 -> W^d`, `(LW)^2 -> (WL)^d`, constants `7`, `3/2` unchanged; needs the UBounds items of part C re-proved privately.
- Bridge `stepZ_eq_sum_gridDelta`, `stepZ_ukerMat_eq_Uker`, `stepXi_/stepY_..._ae`, `Zvec`, `Yvec`, `grid_expansion'`, `grid_expansion_all'` (RBM2D 636-1056): **PASS** (algebra at `ξ = 1`; sign of `ukerMat` from `ukerNonneg`, which must be re-derived, part C). P.1 marks only `Avec`, `StoppedDuhamel105` as consumed; the prover decides which of these to drop.
- Overall **PASS**. Paper-delta candidate `T2098a`: none expected (no statement changes beyond `W^2 -> W^d`, `(LW)^2 -> (WL)^d`).

## (b) Script output and narrative - Sun Oct  4 02:17:41 UTC 2026

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2098 && git log -1 --format="%h %an <%ae>" && git diff --stat main...t/T2098
d673266 Jun Yin <321276894+JYin80@users.noreply.github.com>
 RBM3D/Path/Expansion.lean | 1747 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1747 insertions(+)
$ lake build RBM3D.Path.Expansion 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3754 jobs).
$ grep -n "Path/Expansion" <that build output>   (compiler messages of the new file)
(no lines)
$ lake build   (whole library, root #assert_rbm_axioms included; the new module is not yet a root import)
Build completed successfully (3839 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Path/Expansion.lean   (exit code 1)
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Path.Expansion; #assert_rbm_axioms)
exit code: 0; first lines and the registry line:
axiom audit: 3112 theorems, 1155 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
112:premises found by scanning: 82 (borrowed 2, owed 65, structural 15).
113:registry: 5 borrowed + 100 owed + 37 structural; 60 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ lake env lean axioms.lean   (#print axioms of all 34 new public declarations), condensed by: sed -E "s/.*depends on axioms: //" | sort | uniq -c
  34 [propext, Classical.choice, Quot.sound]
$ lake env lean axioms.lean 2>&1 | grep -c "depends on axioms"
34
$ grep -c "^#print axioms" axioms.lean
34
```
```
$ python3 stmt.py Avec StoppedDuhamel105 stoppedDuhamel105 condExp_A_succ grid_expansion_all   (statements extracted from the file; unified diff against RBM2D@c9a24cf after R1-R3)
===  Avec
--- RBM3D statement (extracted from RBM3D/Path/Expansion.lean):
def Avec (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    Zd d (sz.L n) × Zd d (sz.L n) → ℂ :=
  fun a => sz.STLKM n E (gridTime s t K n k) (pathH sz s t K n k ω) ![true, false] ![a.1, a.2]
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
@@ -3,3 +3 @@
-  fun a => gloop (sz.L n) (sz.W n) (blockMat (pathH d s t K n k ω))
-      (spectralZ E (gridTime s t K n k)) (pmLoop a.1 a.2) -
-    Kpm (sz.L n) (sz.W n) E (gridTime s t K n k) a.1 a.2
+  fun a => sz.STLKM n E (gridTime s t K n k) (pathH sz s t K n k ω) ![true, false] ![a.1, a.2]
===  StoppedDuhamel105
--- RBM3D statement (extracted from RBM3D/Path/Expansion.lean):
def StoppedDuhamel105 (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  |E| < 2 → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n : ℕ) (τ : PathΩ sz → ℕ) (k : ℕ) (ω : PathΩ sz), min k (τ ω) ≤ K n →
      Avec sz E s t K n (min k (τ ω)) ω =
        Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec sz E s t K n 0 ω) +
          ∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n (min k (τ ω)))
              (predInc sz E s t K n j ω + martInc sz E s t K n j ω)
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
@@ -8,2 +8,2 @@
-            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
-              (gridTime s t K n (min k (τ ω)))
+            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
+              (gridTime s t K n (j + 1)) (gridTime s t K n (min k (τ ω)))
===  stoppedDuhamel105
--- RBM3D statement (extracted from RBM3D/Path/Expansion.lean):
theorem stoppedDuhamel105 (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedDuhamel105 sz E s t K
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
(none)
===  condExp_A_succ
--- RBM3D statement (extracted from RBM3D/Path/Expansion.lean):
theorem condExp_A_succ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) (hj : j < K n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    (∀ (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)),
        predInc sz E s t K n j ω a
          = (gridStep s t K n : ℂ) * Dgrid sz E s t K n j ω a + Rgrid sz E s t K n j ω a) ∧
      ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
        ‖Rgrid sz E s t K n j ω a‖
          ≤ envConst d (sz.L n) (sz.W n) E 2 (gridTime s t K n (j + 1))
                * gridStep s t K n ^ ((3 : ℝ) / 2)
            + 7 * (sz.size n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4
                * gridStep s t K n ^ 2
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
(none)
===  grid_expansion_all
--- RBM3D statement (extracted from RBM3D/Path/Expansion.lean):
theorem grid_expansion_all (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n : ℕ) (τ : PathΩ sz → ℕ) (k : ℕ) (ω : PathΩ sz) (hkτ : min k (τ ω) ≤ K n) :
    Avec sz E s t K n (min k (τ ω)) ω
      = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec sz E s t K n 0 ω)
        + ∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n (min k (τ ω)))
              ((gridStep s t K n : ℂ) • Dgrid sz E s t K n j ω + Rgrid sz E s t K n j ω
                + martInc sz E s t K n j ω)
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
(none)
$ python3 stmt.py -d martInc predInc Dgrid Rgrid
===  martInc
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
(none)
===  predInc
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
(none)
===  Dgrid
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
@@ -3,2 +3,2 @@
-  fun a => ELKLK (sz.L n) (sz.W n) E (gridTime s t K n j) (pathH d s t K n j ω) a.1 a.2
-    + EGt (sz.L n) (sz.W n) E (gridTime s t K n j) (pathH d s t K n j ω) a.1 a.2
+  fun a => sz.STELKLKM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false] ![a.1, a.2]
+    + sz.STEGtM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false] ![a.1, a.2]
===  Rgrid
--- diff, RBM2D (-) vs RBM3D (+) after R1-R3:
(none)
```
```
$ bash names.sh   (34 public names; then grep for declarations of the same names elsewhere in RBM3D)
--- clash grep (declarations with these names elsewhere in RBM3D, excluding RBM3D/Path/Expansion.lean):
--- (end of clash grep)
$ grep -c "^example" RBM3D/Path/Expansion.lean   (24 compiled examples at sz0 incl. 6 boundary ones; line numbers:)
1567 1588 1610 1618 1637 1642 1653 1658 1662 1666 1671 1675 1680 1686 1691 1699 1704 1709 1714 1719 1724 1729 1734 1739 
$ sed -n 1567,1585p RBM3D/Path/Expansion.lean   (instance of stoppedDuhamel105; every hypothesis discharged)
example (ω : PathΩ sz0) :
    Avec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0
        (min 4 ((fun _ : PathΩ sz0 => 3) ω)) ω
      = Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
            (gridTime Expansion_instS Expansion_instT Expansion_instK 0 0)
            (gridTime Expansion_instS Expansion_instT Expansion_instK 0
              (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (Avec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω)
        + ∑ j ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
            Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
              (gridTime Expansion_instS Expansion_instT Expansion_instK 0 (j + 1))
              (gridTime Expansion_instS Expansion_instT Expansion_instK 0
                (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
              (predInc sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω
                + martInc sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω) :=
  stoppedDuhamel105 sz0 0 Expansion_instS Expansion_instT Expansion_instK Expansion_inst_E
    Expansion_inst_s0 Expansion_inst_st Expansion_inst_t1 Expansion_inst_K 0 (fun _ => 3) 4 ω
    (by norm_num [Expansion_instK])

$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/Expansion.lean RBM2D/Path/UBounds.lean   (RBM2D HEAD = 9e0f275; the port is from c9a24cf)
 RBM2D/Path/Expansion.lean | 299 ++++++++--------------------------------------
 RBM2D/Path/UBounds.lean   | 147 +++++------------------
 2 files changed, 77 insertions(+), 369 deletions(-)
```

Narrative (facts from the files and the logs above):
- New file `RBM3D/Path/Expansion.lean` (1747 lines, commit d673266 on `t/T2098`, the only file in `git diff main...t/T2098`); `RBM3D/Test/Axioms.lean` is unchanged (registry pre-check exit 0: no new premise is assumed by a theorem; `StoppedDuhamel105` is proved by `stoppedDuhamel105`).
- Imports: `Path/{StepDecompLoop,DriftAlgebra,LoopStep,Kernel}` and `Kernel/Evolution` (for `sum_norm_row_le`). `Path/QVIdentity` is not imported: no declaration of the port uses `EE`, `loop6`, `cutDeriv*`, `loopDeriv`.
- Port source: RBM2D `Path/Expansion` at `c9a24cf` (1159 lines), all public declarations ported, none dropped. RBM2D HEAD (`9e0f275`) differs from `c9a24cf` in this file and in `Path/UBounds` (diff-stat above); only `c9a24cf` was used.
- Vocabulary: `Avec` is `sz.STLKM n E u H ![true,false] ![a.1,a.2]` (`= loopFine - STKloop`), `Dgrid` is `STELKLKM + STEGtM`; `Uop d L g ξ` carries `g = sz.lam n`, `ξ = ↑(normSq (mE E))`; `Kpm` is `STKloop` = `(W^d)⁻¹ Θ_u` (`Expansion_STKloop_eq`, via `KLK_two_eq_kTwo`, `m(+)m(-) = 1`); `Expansion_loopObs` uses `Green.loopPM`, the family of `hermTestFun_loopPM`/`stepDecomp_loopPM`.
- Part C of (a) confirmed: `uopOneStep`, `ukerNonneg`, `normSqSpectralMOne` are not in RBM3D (T2097 unmerged); re-proved here as private `Expansion_uopOneStep` (`‖ξ‖ = 1`, merged `norm_Theta_le` with `m = ξ`), `Expansion_ukerNonneg` (copy of the private `StepDecompLoop_ukerNonneg` method), `Expansion_normSq_mE`; `thetaGen` is the private `Expansion_thetaGen`, tied to the merged `STthetaOp` by `Expansion_STthetaOp_eq`.
- Class b exponents (table (a)(i)): `W^2 → W^d` in the `𝒦` normalisation and the second-order step (`Expansion_K_step` with `c = (W^d)⁻¹`), `(L W)^2 → (L W)^d` in `Expansion_norm_Avec_le` (`norm_gloop_le_crude`, loop length 2); `Expansion_arith` (constant `7`) and the `3/2` of `condExp_A_succ` are unchanged. No statement was false at `d ≥ 3`; the script diff shows only vocabulary changes.
- Added (not in RBM2D): `stoppedDuhamel105_at`, `grid_expansion_all_at`, `grid_expansion_at`, `grid_expansion'_at`, `grid_expansion_all'_at` (hypotheses `0 ≤ s n`, `s n ≤ t n`, `t n < 1`, `K n ≠ 0` only at `n`, DECISIONS §29 (4)); the pinned `∀ n` forms are one-line corollaries.
- DECISIONS §29 boundary instances compiled at `sz0`: `s = 0` (`u_0 = 0`), `s = t` (`Δ = 0`), `t = 99/100` with the last step `j = 3` (examples at lines 1724-1739).
- `sz0` data: `d = 3`, `L = 4`, `W = 32`, `lam = 1/64`, `E = 0`, `s = 1/10`, `t = 1/2`, `K = 4`, `τ = 3`, `k = 4`.
- The numeric check of (a)(ii) was run in the preflight stage at `L = 3`, `W = 2`; no new numeric run in this stage.

## (c) Verified Mathlib names (compiled `#check` of each, exit 0, no errors)
`Finset.sum_induction`, `Finset.single_le_sum`, `MeasureTheory.condExp_sub`, `condExp_const`, `condExp_smul`, `condExp_finsetSum`, `memLp_top_of_bound`, `ae_all_iff`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.rpow_two`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Complex.abs_im_le_norm`, `Complex.re_sum`, `Complex.norm_real`, `Fin.sum_univ_two`, `Matrix.trace_sum`, `Matrix.isHermitian_add_transpose_self`, `Matrix.IsHermitian.submatrix`, `inv_anti₀`, `one_le_inv₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `pow_le_one₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `Nat.one_le_cast`, `Nat.one_le_pow`.
Verified absent in RBM3D (grep of `def|theorem|lemma|abbrev` lines over `RBM3D/`, excluding the new file, no hit): `norm_entry_le_norm` (RBM2D's helper; replaced by the private `Expansion_norm_entry_le`, from `sum_norm_row_le`), `uopOneStep`, `ukerNonneg`, `normSqSpectralMOne`, `Kpm`, `pmLoop`. `gloop` exists in RBM3D (`Loop/GLoop.lean:97`) with a different signature (on `Omega d L W`) and is not used; the loops here are `loopL`/`loopFine`.

## (d) Open issues and paper-delta candidates
- `T2098a` (pin form, not a mathematics change): `StoppedDuhamel105`, `grid_expansion_all`, `grid_expansion`, `grid_expansion'`, `grid_expansion_all'` carry `∀ n` hypotheses on `s, t, K` as in the RBM2D pin; the paper has no such quantifier. The `_at` forms are the hypotheses-at-`n` versions for consumers with `∀ᶠ n`.
- `T2098b` (vocabulary): `Avec`, `Dgrid` are defined through the merged `STLKM`, `STELKLKM`, `STEGtM` at `σ = (+,-)`; `Avec sz E s t K n k ω` takes `sz` first and is a function on `Zd d (sz.L n) × Zd d (sz.L n)`, whereas `Step2Defs` tensors are functions on `Fin 2 → Zd d (sz.L n)` (bridge: `Expansion_STthetaOp_eq`, private). ST-3 consumers should check this shape against their pins.
- Open for the dispatcher: T2097 (ST2-25, `Path/UBounds`) is unmerged (state `preflight-fail`, section (a) part C). If it later merges public `uopOneStep`, `ukerNonneg`, `normSqSpectralMOne`, this file's private `Expansion_` copies do not clash but duplicate that proof.
- `T2098c` (statement form of (int_K-L_ST)): `StoppedDuhamel105`/`stoppedDuhamel105`, `grid_expansion(_all)`, `grid_expansion'`, `grid_expansion_all'` and their `_at` forms are the time-discrete, pathwise form of `(int_K-L_ST)` (`paper/tex/3_5_Loop_Hierarchy.tex:134-139`, Lemma `Sol_CalL`, "Lemma 5.3 of [YY_25]"): the paper's identity is a continuous-time integral equation at a stopping time `τ ≥ s`; Lean's is a telescope on the grid `u_j = s + jΔ`, only for `n = 2`, `σ = (+,-)`: `stoppedDuhamel105`, `grid_expansion_all` stop it at the index `min k (τ ω)` with `τ : PathΩ sz → ℕ` any function (not only stopping times), pathwise; `grid_expansion` is at a fixed `k ≤ K n`, pathwise; `grid_expansion'`, `grid_expansion_all'` are a.e. at `k ≤ K n`. The increments `predInc + martInc` (`stoppedDuhamel105`), `Δ·Dgrid + Rgrid + martInc` (`grid_expansion(_all)`) and `Zvec + Yvec + Δ·Dgrid + Rgrid` (the primed forms) replace the paper's `∫ … du` and `∫ dE^M` terms. Related existing entries: D21 (grid-walk representation), D162 (Duhamel: discrete algebraic part only).
- `T2098d` (Lean-only statement): `condExp_A_succ` (and `Expansion_condExp_A_succ_of_lt_one`, `Expansion_condExp_A_succ_rpow`) is an Euler-step drift split with no counterpart in the paper: `predInc_j = Δ·(E^{LK×LK} + E^{G̃})_{u_j} + R_j` with `‖R_j‖ ≤ envConst d L W E 2 u_{j+1} Δ^{3/2} + 7 N η_{u_{j+1}}^{-4} Δ^2` a.e., `N = (WL)^d`; the `d`-dimensional constants come from `W^{-d}` / `W^{-2d}` and replace RBM2D's `W^{-2}`, `(LW)^2`. Related existing entries: D151 (`condExp_loop_drift` bound), D159 (`W^{-2d}` in the one-step decomposition).
- Correction of section (a), "Verdict per target", last line ("Paper-delta candidate `T2098a`: none expected"): wrong; the candidates are `T2098a`-`T2098d` above.

## Repair - Sun Oct  4 02:22:56 UTC 2026
Report-only repair for the RETURN of `docs/reports/T2098-audit.md` (round 1), items 1-3: candidates `T2098c`, `T2098d` and the correction of (a) are added in (d) above. No `.lean` file changed; `t/T2098` stays at d673266.
```
$ grep -n "label{int_K-L_ST}\|label{Sol_CalL}" paper/tex/3_5_Loop_Hierarchy.tex
134:\begin{lemma}[Integrated loop hierarchy, Lemma 5.3 of \cite{YY_25}] \label{Sol_CalL}
136:\begin{align}\label{int_K-L_ST}
156:% \begin{align}\label{int_K-L_ST}
$ grep -nE "^## D(21|151|159|162) " docs/paper-deltas.md | cut -c1-40
228:## D21 · 流用单时刻律与网格游走表示，全体尺寸放在一个乘积空间上
611:## D151 · `condExp_loop_drift` 的界（20
643:## D159 · 一步分解的 `W^{-2d}` 与常数（2026-1
655:## D162 · Duhamel 只有离散代数部分（2026-10-0
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2098 log -1 --format=%h ; git -C /Users/junyin/Lean_proof/RBM3D-wt/T2098 status --short
d673266
```
(line 156 is a commented-out copy.)
