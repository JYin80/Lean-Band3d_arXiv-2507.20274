Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 22:45:29 UTC 2026

Targets (all deterministic statements on finite matrices; no external hypothesis, so no limit computation): `EECutIdentity`, `QVPropagated`, `EEShift`
(RBM2D `Path/QVIdentity.lean`, 844 lines at `c9a24cf`) and `v_gradMat_eq_quadVar` (RBM2D `Path/QVForm.lean`, 325 lines at `c9a24cf`).

### (i) Exponent table

**A. Every `W^2` / `Z2` occurrence.**  Command (script `cnt.sh`, scratchpad `T2084/`, on `git show c9a24cf:RBM2D/Path/QVIdentity.lean`); output = RBM2D line numbers:
```
Z2 (index set Z_L^2)       : 207 228 245 270 281 298 315 316 317 320 331 332 347 359 361 362 370 382 391 432 490 492 493 500 502 520 548 566 610 611 612 686 716 731 741 752 761 770 773 825 827 
(W:C)^2 / (W:R)^2 (W^2)    : 207 245 247 320 405 406 716 781 795 797 
(W:C)⁻¹^2 / (W:R)⁻¹^2 (w)  : 215 230 246 247 689 710 
(L:R)^2 (L^2 = card Z2 L)  : 739 771 787 795 797 799 802 
(W*L)^2 / card BlockIndex  : 372 783 784 
norm_Eblk_le_inv_W_sq      : 695 
svar_cast_eq_Spaper/Spaper : 19 220 227 377 
gvar/svar/Coord (no g)     : 19 143 145 148 149 150 160 161 171 204 211 318 348 355 360 489 491 498 519 529 816 824 ...
lines total:      844
```
`QVForm.lean` at `c9a24cf`: `grep -cE 'Z2|\(W : [ℂℝ]\)|W \* L|BlockIndex'` gives 0 lines; its only `d = 2` tokens are the docstring lines 9 and 21.

| RBM2D token (lines) | d >= 3 replacement | why it holds |
|---|---|---|
| `Z2 L` (41 lines) | `Zd d L`, `Idx L W` -> `Idx d L W` | only sums over the index and `SB`; symmetry `SB_transpose` (Defs/Block.lean:58), `svarF_comm` (FineModel) do not use `d` |
| `(W:ℂ)^2` (207,245,247,320,405,406,716,781,795,797) | `(W:ℂ)^d` | `svarF = W^{-d}·SBR` (FineModel.lean:47), `Eblk` entries `W^{-d}` (Loop/GLoop.lean:55): `W^d·(W^{-d})^2 = W^{-d}` (`QVIdentity_svar_sum`); numerically below |
| `(W)⁻¹^2` (215,230,246,247,689,710) | `(W^d)⁻¹` | same entries of `Eblk` |
| `norm_Eblk_le_inv_W_sq` (695) | `‖Eblk d L W b‖ <= (W^d)⁻¹` | `norm_Eblk_le`, Induction/Split.lean:681 |
| `(L:ℝ)^2` = `card Z2 L` (739,771,787,795,797,799,802) | `L^d` (`Fintype.card (Zd d L)`, `ZMod.card`) | row sums of `SB` are 1: `sum_norm_SB_row`/`sum_SB_row` (Block.lean:108), needs `3 <= L` |
| `(W*L)^2`, `card_BlockIndex` (372,783,784) | `(W*L)^d` = `card (Vtx d L W)` = `L^d W^d` = `sz.size n` | `card_Idx` (Defs/Sizes.lean:107), `split_bijective` |
| `svar_cast_eq_Spaper`, `Spaper_eq`, `Svar_apply` (19,220,227,377) | `svarF_eq_svar` (FineModel.lean:68, `rfl`); `svar = W^{-d}·SBR` (Gauss/Model.lean:63) | **`SB d L g` carries the coupling `g`**: `g : ℝ` is a new parameter of `EE`, of the three pins, and (through `gvarF d L W g`, FineModel.lean:89) of `v_gradMat_eq_quadVar`; RBM2D has none |
| `gvar`, `Coord`, `coordinateMatrix` | `gvarF`, `CoordF` (card `2N^2`), `coordinateMatrix d L W` (FineModel.lean:384) | R4 of ST1-COMMON; `gvarF = svarF` on the diagonal, `svarF/2` off it, as RBM2D |

**B. Exponents, thresholds, constants.**

| item | value | constraint | slack |
|---|---|---|---|
| `d` | 3 | statements and RBM2D proofs contain no `d`-dependent step beyond table A | n/a |
| `L` | 3 (sz0: 4) | `3 <= L`: `card_nbhd` (Defs/Neighbours.lean:158) gives `2d` neighbours, rows of `SB` sum to 1 | 0 at `L = 3` (met); the Lean instance at sz0 has `L = 4` |
| `W` | 2 (sz0: 32) | `1 <= W` (`NeZero W`): `w = W^{-d} <= 1`, `L^d <= N` | factor `W^{6d} = 2^18` in the last step of `EEShift` |
| `g` | 1/2 and 1/64 | any real (Block.lean docstring: no sign condition); 1/64 is the `lam` of `scales_sz0` (Defs/Sizes.lean) | none needed |
| `E`, `u`, `Δ` | 0.7 (and 1.0), 1/2, 1/1000 | `|E| < 2` (`mE_im_pos`, `norm_mE` Defs/Semicircle.lean:56,63); `u < 1` (`etaT_pos`, Loop/GLoop.lean:83); `0 <= Δ`, `u + Δ < 1`; `0 <= u` is in the RBM2D pin but not used | `2 - |E| = 1.3`; `1 - (u+Δ) = 0.499`; boundary runs `u = 0` and `u+Δ = 0.999` below |
| `η = etaT E (u+Δ)` | 0.467438 | `= (1-u-Δ) Im m(E)` (`zt_im`); exponent 7 = 2 (from `G(z1)-G(z2) = (z1-z2) G G`) + 5 (other five `G` of the six-loop, `η⁻¹` each); 6 = 3n, `n = 2` is the loop length, not `d` | exact count |
| `w = ‖E_b‖` | `W^{-d}` | six `E` factors give `w^6`; with the prefactor `W^d`: net `W^{-5d}` | exact |
| `N` | `(WL)^d = 216` | `EEShift`: `12 L^d N W^{-5d} η^-7 Δ <= 12 N^2 η^-7 Δ <= 16 N^2 η^-7 Δ` (`L^d <= N`, `W^{-5d} <= 1`) | ratio `(4/3) W^{6d} = 349525.3`; printed `1.5309e5 / 4.3801e-1` |
| `2` in `QVPropagated` | 2 = number of cuts | `‖x+y‖^2 <= 2‖x‖^2 + 2‖y‖^2` | `LHS/RHS = 0.237` (random `M`), `0.75` (`M = 0`, `E = 1`) |
| `#CoordF` | `2N^2 = 93312` (46656 nonzero matrices) | `v_gradMat_eq_quadVar` sums over all of `CoordF`; unused coordinates have `coordinateMatrix = 0` | none |
| DECISIONS §29 | (1) `u+Δ<1`, `0<=Δ` stated; (2) no `ilambda` window; (3) no `L`–`W` relation used, only `L>=3`, `W>=1`; (4) fixed `(d,L,W,g)`, no `n`-quantifier | constants 12, 16 contain no `W`, `L`, `g` | paper argument above, runs below |

### (ii) One concrete nondegenerate instance
`d = 3, L = 3, W = 2` (`N = 216`), `g = 1/2`, `E = 0.7`, `u = 1/2`, `Δ = 10^-3` (`u + Δ = 0.501`), one sample `M` of the model law (Hermitian, `‖M‖ = 2.09`), labels `a = (0,13)`, `a' = (26,4)`, four-label `κ`;
`Φ = tr(A^3)` (holomorphic) and `Φ = |tr A|^2` (non-holomorphic), both real on Hermitian matrices, `gradMat` built from the basis formula of `StepDecomp.lean:80`, `linTr = Re tr(A X)`.
The Lean example data is `M = 0`, `E = 1`, `a = a' = (5,5)` (second block of output; `LHS = 6.9e-4 > 0`) at the merged `sz0` (`d = 3`, `L = 4`, `W = 32`).
Command: `cd scratchpad/T2084 && python3 check.py 0.5` (numpy 2.0.2, exit 0, 3 s; `check.py` computes `EE` both by the literal six-loop sum and by block aggregation, the coordinate sums over all coordinates, `loopDeriv` by finite difference):
```
d=3 L=3 W=2 N=(WL)^d=216 L^d=27 g=0.5  SB row sums min/max = 1.000000000000000 1.000000000000000  SB symmetric: True
#coords total 2N^2 = 93312  used: 46656
sample M: Hermitian, ||M||_op = 2.0910
[v_gradMat_eq_quadVar] Phi=tr_cube: FD check phi(Xd) vs tr(G Xd) rel.err=8.42e-10; max|Im phi(X_c)|=0.0e+00
   LHS linTrVar(gradMat)= 1.414313781386e+02   RHS sum_c gvar_c|phi(X_c)|^2 = 1.414313781386e+02   rel.diff = 0.00e+00
   one step Delta=0.001: Delta*LHS = 1.414313781386e-01   Delta*RHS = 1.414313781386e-01
[v_gradMat_eq_quadVar] Phi=abs_tr_sq: FD check phi(Xd) vs tr(G Xd) rel.err=7.31e-11; max|Im phi(X_c)|=0.0e+00
   LHS linTrVar(gradMat)= 4.515286183439e-01   RHS sum_c gvar_c|phi(X_c)|^2 = 4.515286183439e-01   rel.diff = 0.00e+00
   one step Delta=0.001: Delta*LHS = 4.515286183439e-04   Delta*RHS = 4.515286183439e-04
---- random Hermitian sample M: E=0.7 u=0.5 (0<=u<1, |E|<2)
EE(a,a') fast=3.0557507707e-09+3.4508941180e-24j literal=3.0557507707e-09-2.4434139813e-24j |diff|=5.9e-24
[EECutIdentity] a=(0, 13) a'=(26, 4): EE=3.0557507707e-09+3.4508941180e-24j  sum_c gvar_c(cut1 conj cut1'+cut2 conj cut2')=3.0557507707e-09+3.3604212385e-24j  |diff|=4.2e-25
   diagonal a=a'=(5,5): EE=3.4739161439e-04-1.9243636947e-22j  rhs=3.4739161439e-04-1.5696799362e-22j  |diff|=1.1e-19
[loopDeriv = cutDeriv1+cutDeriv2] finite-difference rel.err on 3 random coords: 3.5e-08
[QVPropagated] LHS sum_c gvar_c |sum_b kappa_b loopDeriv|^2 = 2.1790876303e-05 <= 2 Re sum kappa kappa* EE = 9.2075332865e-05  holds: True  (Im part of the double sum 1.1e-21)
[EEShift] u=0.5 Delta=0.001 u+Delta=0.501<1 : eta_{u+D}=0.467438; |EE(u+D)-EE(u)| = 5.020734e-11 <= 12 L^d N W^-5d eta^-7 D = 4.380060e-01 <= 16 N^2 eta^-7 D = 1.530942e+05: True
---- M = 0 (Lean example data), diagonal labels: E=1.0 u=0.5 (0<=u<1, |E|<2)
EE(a,a') fast=4.6296296296e-04+0.0000000000e+00j literal=4.6296296296e-04+0.0000000000e+00j |diff|=0.0e+00
[EECutIdentity] a=(5, 5) a'=(5, 5): EE=4.6296296296e-04+0.0000000000e+00j  sum_c gvar_c(cut1 conj cut1'+cut2 conj cut2')=4.6296296296e-04+0.0000000000e+00j  |diff|=0.0e+00
   diagonal a=a'=(5,5): EE=4.6296296296e-04+0.0000000000e+00j  rhs=4.6296296296e-04+0.0000000000e+00j  |diff|=0.0e+00
[loopDeriv = cutDeriv1+cutDeriv2] finite-difference rel.err on 3 random coords: 0.0e+00
[QVPropagated] LHS sum_c gvar_c |sum_b kappa_b loopDeriv|^2 = 6.9444444444e-04 <= 2 Re sum kappa kappa* EE = 9.2592592593e-04  holds: True  (Im part of the double sum 0.0e+00)
[EEShift] u=0.5 Delta=0.001 u+Delta=0.501<1 : eta_{u+D}=0.432147; |EE(u+D)-EE(u)| = 1.851847e-09 <= 12 L^d N W^-5d eta^-7 D = 7.588057e-01 <= 16 N^2 eta^-7 D = 2.652218e+05: True
[EEShift boundary] E=0.7 u=0.998 u+Delta=0.999: eta=9.367e-04, |dEE|=1.4841e+01 <= 16 N^2 eta^-7 Delta = 1.1794e+24: True
[EEShift boundary] E=0.7 u=0.0 u+Delta=0.001: eta=9.358e-01, |dEE|=1.3235e-07 <= 16 N^2 eta^-7 Delta = 1.1877e+03: True
```
The same script with `g = 0.015625` also reports `rel.diff = 0.00e+00` (both `Φ`), `QVPropagated` and `EEShift` `True`, `EECutIdentity` `|diff| = 1.2e-38` (`EE = 9.3e-23`) and `0` (diagonal).

### Findings for stage 1b (none blocks the mathematics)
Command: `cd RBM3D-wt/T2084 && grep -rnE "def (EE|loop6|cutDeriv1|cutDeriv2|loopDeriv)\b" RBM3D; echo "grep exit=$?"` gives `grep exit=1`: **`loop6`, `EE`, `cutDeriv1`, `cutDeriv2`, `loopDeriv` do not exist in RBM3D** (RBM2D `Path/Step2Vocab.lean:87,93,99,104,109`; the T2039 portmap row 39 maps `Step2Vocab` to the `STLM..STEEM` vocabulary of `Induction/Step2Defs.lean`). `STEEM`/`STEEkM` (Step2Defs.lean:131,141) are the diagonal case `a = a'` with `σ` as argument, so they cannot state `EECutIdentity` (`a ≠ a'`; the instance above uses `a ≠ a'`). The five definitions must therefore be written in `RBM3D/Path/QVIdentity.lean` with `SB d L g`, `loopFine`, `greenBlk`, `Eblk d L W`, `zt` (all merged); their text is RBM2D's with `Z2 L -> Zd d L`, `W^2 -> W^d`, `SB L -> SB d L g`. The dispatcher should fix their names in the ticket, since later tickets (ST2-26, ST2-28) consume them.

### Verdict
- `EECutIdentity`: PASS (`a != a'`: |diff| 4.2e-25 against `EE = 3.1e-9`; diagonal: |diff| 1.1e-19 for random `M`, 0 for `M = 0`).
- `QVPropagated`: PASS (`2.18e-5 <= 9.21e-5`; `6.94e-4 <= 9.26e-4`).
- `EEShift`: PASS (exponents close with slack `(4/3) W^{6d}`; boundary runs `u = 0`, `u + Δ = 0.999` hold).
- `v_gradMat_eq_quadVar`: PASS (both sides equal to all printed digits for both `Φ`).

### (a′) Preflight corrections — Sat Oct  3 23:02:10 UTC 2026
Section (a) (ii) names the Lean example data `M = 0`, `a = a' = (5,5)`; the compiled instances use `M = 1` and `a = (0,1) ≠ a' = (1,0)` at the merged `sz0`. No verdict of (a) changes; (a) is not edited.

## (b) Script output

Branch `t/T2084`, commit `c626bdf`; sole writable file `RBM3D/Path/QVIdentity.lean` (1309 lines); `RBM3D/Test/Axioms.lean` not touched.
```
$ git diff --stat main...t/T2084; git diff --name-only main...t/T2084
 RBM3D/Path/QVIdentity.lean | 1309 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1309 insertions(+)
RBM3D/Path/QVIdentity.lean
$ lake build RBM3D.Path.QVIdentity 2>&1 | grep -v "^trace" | grep -E "QVIdentity|Build completed|error"   # olean mtime Oct 3 15:57 local (commit date has offset -07:00); this rerun is up to date
Build completed successfully (3340 jobs).
$ lake env lean -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 RBM3D/Path/QVIdentity.lean; echo exit=$?   # lakefile options, no warning
exit=0
$ (time lake build) > fullbuild.out 2>&1; tail -2 fullbuild.out   # full library, root #assert_rbm_axioms; root imports not yet include the new module
non-vacuity certificates: 4 of 94 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/Int
Build completed successfully (3823 jobs).
$ lake env lean precheck.lean > precheck.out; echo exit=$?; head -1 precheck.out   # precheck.lean (outside the repository) = import RBM3D, import RBM3D.Path.QVIdentity, #assert_rbm_axioms
exit=0
axiom audit: 2669 theorems, 1103 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean ax.lean | sed | awk   # #print axioms of every public declaration, grouped by axiom set
18 declarations with axioms [propext, Classical.choice, Quot.sound]: vB vB_self vB_nonneg_diag v_sum_eq abs_vB_le v_gradMat_eq_quadVar QVForm_check_v_gradMat_eq_quadVar loop6 EE cutDeriv1 cutDeriv2 loopDeriv EECutIdentity QVPropagated EEShift eeCutIdentity qvPropagated eeShift
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Path/QVIdentity.lean; echo "grep exit=$?"
grep exit=1
```

Target statements, extracted by `extract.py` from the file (the three pins are `Prop` definitions; `eeCutIdentity`, `qvPropagated`, `eeShift` prove them):
```
-- QVIdentity.lean:398
def EECutIdentity : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ∀ a a' : Zd d L × Zd d L,
      EE d L W g E u M a a' = ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        (cutDeriv1 d L W E u M (coordinateMatrix d L W c) a *
            (starRingEnd ℂ) (cutDeriv1 d L W E u M (coordinateMatrix d L W c) a') +
          cutDeriv2 d L W E u M (coordinateMatrix d L W c) a *
            (starRingEnd ℂ) (cutDeriv2 d L W E u M (coordinateMatrix d L W c) a'))

-- QVIdentity.lean:410
def QVPropagated : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ∀ κ : Zd d L × Zd d L → ℂ,
      ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) *
          ‖∑ b : Zd d L × Zd d L, κ b * loopDeriv d L W E u M (coordinateMatrix d L W c) b‖ ^ 2 ≤
        2 * (∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          κ b * (starRingEnd ℂ) (κ b') * EE d L W g E u M b b').re

-- QVIdentity.lean:421
def EEShift : Prop :=
  ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u Δ : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → 0 ≤ Δ →
    u + Δ < 1 → ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ a a' : Zd d L × Zd d L,
      ‖EE d L W g E (u + Δ) M a a' - EE d L W g E u M a a'‖ ≤
        16 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (etaT E (u + Δ))⁻¹ ^ 7 * Δ

-- QVIdentity.lean:795
theorem eeCutIdentity : EECutIdentity

-- QVIdentity.lean:917
theorem qvPropagated : QVPropagated

-- QVIdentity.lean:1115
theorem eeShift : EEShift

-- QVIdentity.lean:284
theorem v_gradMat_eq_quadVar {d : ℕ} (sz : Sizes d) (n : ℕ)
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hd : DifferentiableAt ℝ Φ M) (hReal : ∀ A, A.IsHermitian → (Φ A).im = 0)
    (hM : M.IsHermitian) :
    linTrVar n (gradMat Φ M)
      = ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ)
          * ‖fderiv ℝ Φ M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2
```
Pins against RBM2D (`pindiff.py`: RBM2D `Path/QVIdentity.lean:345-372` at `c9a24cf`, docstrings removed, R2/R3/R4 and the parameter `g` applied by script, whitespace normalised; `diff a.txt b.txt`):
```
diff exit=0
```

Compiled nonempty instances at `d = 3` (merged `sz0`: `L = 4`, `W = 32`, `g = 1/64`; `M = 1`, `E = 1`, `u = 1/2`, `Δ = 1/1000`, labels `(0,1) ≠ (1,0)`), `section Instances`, built by the commands above; every hypothesis discharged. Lines 1261, 1268, 1286, 1295: statement not repeated here:
```
-- QVIdentity.lean:1234
example : EE 3 4 32 (1 / 64) 1 (1 / 2) 1 (0, 1) (1, 0) =
    ∑ c : CoordF 3 4 32, ((gvarF 3 4 32 (1 / 64) c : ℝ) : ℂ) *
      (cutDeriv1 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (0, 1) *
          (starRingEnd ℂ) (cutDeriv1 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (1, 0)) +
        cutDeriv2 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (0, 1) *
          (starRingEnd ℂ) (cutDeriv2 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) (1, 0))) :=
  eeCutIdentity 3 4 32 (1 / 64) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)
-- QVIdentity.lean:1244
example : ∑ c : CoordF 3 4 32, (gvarF 3 4 32 (1 / 64) c : ℝ) *
      ‖∑ b : Zd 3 4 × Zd 3 4, (fun _ => (1 : ℂ)) b *
        loopDeriv 3 4 32 1 (1 / 2) 1 (coordinateMatrix 3 4 32 c) b‖ ^ 2 ≤
    2 * (∑ b : Zd 3 4 × Zd 3 4, ∑ b' : Zd 3 4 × Zd 3 4,
      (fun _ => (1 : ℂ)) b * (starRingEnd ℂ) ((fun _ => (1 : ℂ)) b') *
        EE 3 4 32 (1 / 64) 1 (1 / 2) 1 b b').re :=
  qvPropagated 3 4 32 (1 / 64) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 Matrix.isHermitian_one (fun _ => 1)
-- QVIdentity.lean:1254
example : ‖EE 3 4 32 (1 / 64) 1 (1 / 2 + 1 / 1000) 1 (0, 1) (1, 0) -
      EE 3 4 32 (1 / 64) 1 (1 / 2) 1 (0, 1) (1, 0)‖ ≤
    16 * (((32 * 4) ^ 3 : ℕ) : ℝ) ^ 2 * (etaT 1 (1 / 2 + 1 / 1000))⁻¹ ^ 7 * (1 / 1000) :=
  eeShift 3 4 32 (1 / 64) 1 (1 / 2) (1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)
-- QVIdentity.lean:1261 (statement omitted here, proof term:)
  eeShift 3 4 32 (1 / 64) 1 0 (1 / 1000) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)
-- QVIdentity.lean:1268 (statement omitted here, proof term:)
  eeShift 3 4 32 (1 / 64) 1 (998 / 1000) (1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 Matrix.isHermitian_one (0, 1) (1, 0)
-- QVIdentity.lean:1276
example : linTrVar (sz := sz0) 0 (gradMat
        (fun A : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
          (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) 1)
      = ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ)
          * ‖fderiv ℝ (fun A : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
              (((Real.sin (Matrix.trace A).re : ℝ)) : ℂ)) 1
              (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c)‖ ^ 2 :=
  QVForm_check_v_gradMat_eq_quadVar sz0 0 Matrix.isHermitian_one
-- QVIdentity.lean:1286 (statement omitted here, proof term:)
example : |vB (sz := sz0) 0 (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ...
  abs_vB_le 0 1 1
-- QVIdentity.lean:1295 (statement omitted here, proof term:)
example : linTrVar (sz := sz0) 0 (∑ i : Fin 2, (((fun _ : Fin 2 => (1 : ℝ)) i : ℝ) : ℂ) • ...
  v_sum_eq 0 _ _
```
Name clash (main worktree; the new file is not there) and `d = 2` residue:
```
$ for n in <18 public names>; do printf "$n=%s " $(grep -rnE "(def|theorem|lemma|abbrev|structure|instance|axiom) +(RBM\.[A-Za-z.]+\.)?$n" RBM3D | wc -l); done
vB=0 vB_self=0 vB_nonneg_diag=0 v_sum_eq=0 abs_vB_le=0 v_gradMat_eq_quadVar=0 QVForm_check_v_gradMat_eq_quadVar=0 loop6=0 EE=0 cutDeriv1=0 cutDeriv2=0 loopDeriv=0 EECutIdentity=0 QVPropagated=0 EEShift=0 eeCutIdentity=0 qvPropagated=0 eeShift=0 
$ grep -nE "Z2|BlockIndex|Spaper|svar_cast|\(W : [ℂℝ]\) \^ 2|\(L : ℝ\) \^ 2" RBM3D/Path/QVIdentity.lean
31:Renaming (`docs/tickets/ST1-COMMON.md` items 2-3): `Z2 L` becomes `Zd d L`, `Idx L W` becomes
32:`Idx d L W`, `BlockIndex L W` becomes `Vtx d L W`, `Coord/svar/gvar` become `CoordF/svarF/gvarF`,
46:  (`card_BlockIndex`); the bound is `12 L^d N W^{-5d} η⁻⁷ Δ ≤ 16 N² η⁻⁷ Δ`, `N = (W L)^d`, using
354:`cutDeriv2`, `loopDeriv` are RBM2D's definitions with `Z2 L → Zd d L`, `W^2 → W^d`, `SB L → SB d L g`
1194:    rw [hNdef, card_BlockIndex]
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/QVForm.lean RBM2D/Path/QVIdentity.lean RBM2D/Path/Step2Vocab.lean   # RBM2D HEAD = 9e0f275
 RBM2D/Path/QVForm.lean     | 212 +++------------------------------------------
 RBM2D/Path/QVIdentity.lean |  74 ++++------------
 RBM2D/Path/Step2Vocab.lean |  57 +++---------
 3 files changed, 46 insertions(+), 297 deletions(-)
```

Narrative (facts from the file and the commands above):
- One file, two parts. Part 1 ports RBM2D `Path/QVForm.lean:47-313` (`vB`, `vB_self`, `vB_nonneg_diag`, `v_sum_eq`, `abs_vB_le`, `v_gradMat_eq_quadVar`, the `sin ∘ Re tr` check, public as `QVForm_check_v_gradMat_eq_quadVar`). Part 2 ports `Path/QVIdentity.lean:41-838` plus the five definitions of `Path/Step2Vocab.lean:87-109`.
- No public RBM2D declaration is dropped. The RBM2D `Checks` examples (`QVIdentity.lean:812-838`) and the `#print axioms` lines are replaced by `section Instances`.
- `loop6`, `EE`, `cutDeriv1`, `cutDeriv2`, `loopDeriv` did not exist in RBM3D (grep in (a)); they are defined here in `RBM.Path` with `loop6 := loopFine d L W M (zt E u)`, `EE` carrying `g`. The merged `Induction/Step2Defs.lean` has `STEEM`/`STEEkM` for `a = a'` only, so it cannot state `EECutIdentity` for `a ≠ a'`.
- Imports: `Path.StepDecomp` (`gradMat`, `lin_eq_fderiv`), `Green.Pins` (`greenBlk`, `loopPM`), `Gauss.FlowCalculus` (`hasDerivAt_green_moving`, `norm_Gsig_le_inv_eta`, `norm_Eblk_le_inv_W_sq`, `card_BlockIndex`, `norm_matrix_trace_le_card_mul`), `Induction.ConArgDet` (`Ind.Gres_eq_add_smul_mul`, `Ind.isUnit_sub_zSig`, `Ind.norm_zSig_sub_zSig`); `Path.Markov` via `StepDecomp`. Private copies for what the merged files keep private: `Gres_conjTranspose`, `hasDerivAt_line`, `gvarF` diagonal/off-diagonal values.
- `W^2`/`Z2` accounting (ST1-COMMON item 2; table (a)(i) A): `Z2 L → Zd d L`, `Idx L W → Idx d L W`, `BlockIndex → Vtx d L W` (R2); `(W:ℂ)^2 → (W:ℂ)^d` in `EE`, `QVIdentity_svar_sum`, `eeShift` (`hWw : W^d · W^{-d} = 1`); `(W:ℂ)⁻¹^2 → ((W:ℂ)^d)⁻¹` (entries of `Eblk`); `norm_Eblk_le_inv_W_sq` is the merged lemma of the same name; `(L:ℝ)^2 → (L:ℝ)^d` (`hsum`, `Fintype.card (Zd d L) = L^d` by `simp [Zd, ZMod.card]`) and `(W*L)^2 → (W*L)^d` (`hNval` through `card_BlockIndex`); `svar_cast_eq_Spaper`, `Spaper_eq`, `Svar_apply → QVIdentity_svarF_cast` (`svarF_eq_svar`, `SB_eq_map_SBR`); `Coord/gvar → CoordF/gvarF`. The grep above finds no `Z2`/`W^2`/`L^2` left (only the merged `card_BlockIndex` and docstring lines).
- `eeShift` at `d ≥ 3`: six `E_b` give `w^6`, `w = W^{-d}`; with the prefactor `W^d` the bound is `12 L^d N W^{-5d} η⁻⁷ Δ ≤ 16 N² η⁻⁷ Δ` (`L^d ≤ N = (WL)^d`, `W^{-5d} ≤ 1`); the constants `12`, `16` and the exponent `7 = 2 + 5` contain no `d`, as in table (a)(i) B.
- Statements: the three pins equal RBM2D's after R2/R3/R4 and the new parameter `g` (empty script diff above); `v_gradMat_eq_quadVar` has `{d : ℕ} (sz : Sizes d)` for RBM2D's `d : Sizes` and `gvarF d (sz.L n) (sz.W n) (sz.lam n)` for `gvar`. No hypothesis added or removed. These are unconditional statements, not adapters; `0 ≤ u` is a hypothesis of the pins that no proof uses (as in RBM2D).
- DECISIONS §29: (1) `u + Δ < 1`, `0 ≤ Δ` stated and used (`etaT_pos`); instances at `u = 0` and `u + Δ = 999/1000`; (2) no `ilambda` window; (3) only `3 ≤ L`, `NeZero L`, `NeZero W` are used, no `L`–`W` relation; (4) fixed `(d, L, W, g)`, no `n`-quantifier.
- Numerical check of the identities at `d = 3`, `L = 3`, `W = 2`: section (a)(ii) (python, not Lean). Ports are from `c9a24cf`; RBM2D HEAD (`9e0f275`) has since changed the three files (diff-stat above), not used.

## (c) Verified Mathlib and merged names (each occurs in the file, which builds)
- Mathlib: `Finset.sum_mul_sq_le_sq_mul_sq`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `Real.mul_self_sqrt`, `Real.sq_sqrt`, `Matrix.trace_mul_comm`, `Matrix.trace_sub`, `Matrix.trace_sum`, `Matrix.submatrix_add`, `Matrix.submatrix_smul`, `Matrix.conjTranspose_nonsing_inv`, `Fintype.sum_prod_type`, `Fintype.sum_bool`, `Complex.normSq_eq_norm_sq`, `Complex.mul_conj`, `sub_eq_iff_eq_add'`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `le_mul_of_one_le_left`, `pow_le_one₀`, `mul_inv_cancel₀`.
- Merged RBM3D: `lin_eq_fderiv`, `loopM_eq_loopL`, `SB_eq_map_SBR`, `sum_norm_SB_row`, `svarF_eq_svar`, `svarF_comm`, `idxKey_lt_or_eq_or_lt`, `Eblk_isHermitian`, `SB_transpose`, `etaT_pos`, `mE_im_pos`, `norm_mE`, `zt_im`, and the imports listed above.
- Verified absent under the guessed name (tool log of the check run): `RBM.isUnit_sub_smul_one_of_im_ne_zero` (it is `RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero`), `RBM.coordFinset` (it is `RBM.Path.coordFinset`); `sz0` lives in `RBM.Gauss.SizesInst`; no public `hasDerivAt_line` in RBM3D (private copies only).

## (d) Open issues and paper-delta candidates
- `T2084a`: the coupling `g` of `S^{(B)}(g)` is a parameter of `EE`, `EECutIdentity`, `QVPropagated`, `EEShift` (RBM2D has no coupling); `gvarF` of `v_gradMat_eq_quadVar` is taken at `sz.lam n`.
- `T2084b` (process, for the dispatcher): `loop6`, `EE`, `cutDeriv1`, `cutDeriv2`, `loopDeriv` are public in `RBM.Path` of this file, not in `Induction/Step2Defs.lean`; tickets ST2-26, ST2-28 that use them must import `RBM3D.Path.QVIdentity`.
- `T2084c` (added Sat Oct  3 23:08:40 UTC 2026, audit round 1 item 1): `(𝓔⊗𝓔)` (`defEOTE`, `paper/tex/3_5_Loop_Hierarchy.tex:166-190`) is called "the quadratic variation of the martingale term in `def_Edif`" (`3_5:166`), but it is not literally that quadratic variation. Lean proves instead (i) the per-cut identity `EECutIdentity`: `(𝓔⊗𝓔)_{a,a'} = Σ_c S_c Σ_{k=1,2} ∂^{(k)}_c𝓛_a · conj ∂^{(k)}_c𝓛_{a'}` (no cross-cut terms `k ≠ k'`), and (ii) the bound `QVPropagated`: `Σ_c S_c |Σ_b κ_b ∂_c𝓛_b|² ≤ 2 Re Σ_{b,b'} κ_b κ̄_{b'} (𝓔⊗𝓔)_{b,b'}` (factor `2 = n`). Cross-references: D54 (factor `n` of `lem:SEforLn` (4), not the identity) and RBM2D delta #22 correction (T2049e, `../RBM2D/docs/paper-deltas.md:35`). Witness at `d = 3` (`M = 0`, `u = 0`, `E = 0`, so `z = i`; `a = a'`): the QV is `0` and `(𝓔⊗𝓔)_{a,a} > 0`, so `QV ≠ (𝓔⊗𝓔)`; the per-cut sum equals `EE` (identity (i)). Script `qvwit.py` (scratchpad `T2084/`; lines 1-43 copied from `check.py` of (a)(ii), then QV = `Σ_c gvar_c |cutDeriv1 + cutDeriv2|²`, `EE` by block aggregation):
```
$ python3 qvwit.py 0.5 0 0; echo exit=$?      # args: g E u
d=3 L=3 W=2 N=(WL)^d=216 L^d=27 g=0.5  SB row sums min/max = 1.000000000000000 1.000000000000000  SB symmetric: True
#coords total 2N^2 = 93312  used: 46656
a=a'=(5, 5): z=0.0000+1.0000j  QV=sum_c gvar_c|loopDeriv|^2 = 0.0000000000e+00  EE(a,a) = 1.9531250000e-04+0.0e+00j  per-cut sum = 1.9531250000e-04  QV<=2EE: True  QV==EE: False
a=a'=(0, 1): z=0.0000+1.0000j  QV=sum_c gvar_c|loopDeriv|^2 = 0.0000000000e+00  EE(a,a) = 0.0000000000e+00+0.0e+00j  per-cut sum = 0.0000000000e+00  QV<=2EE: True  QV==EE: True
exit=0
$ python3 qvwit.py 0.015625 0 0 | tail -2; echo exit=$?
a=a'=(5, 5): z=0.0000+1.0000j  QV=sum_c gvar_c|loopDeriv|^2 = 0.0000000000e+00  EE(a,a) = 4.8756704047e-04+0.0e+00j  per-cut sum = 4.8756704047e-04  QV<=2EE: True  QV==EE: False
a=a'=(0, 1): z=0.0000+1.0000j  QV=sum_c gvar_c|loopDeriv|^2 = 0.0000000000e+00  EE(a,a) = 0.0000000000e+00+0.0e+00j  per-cut sum = 0.0000000000e+00  QV<=2EE: True  QV==EE: True
exit=0
```
- `T2084d` (added Sat Oct  3 23:08:40 UTC 2026, audit round 1 item 2): `EE` is `defEOTE` only at `n = 2` and `σ = (+,−)` (`(𝓔⊗𝓔)^{M,(2)}_{u,(+,−),a,a'}`, both cuts `k = 1, 2`); the paper defines `(𝓔⊗𝓔)^{M,(n)}_{t,σ,a,a'}` for all `n` and `σ ∈ {+,−}^n` and uses `max_σ` (`eq:MG_nloop`, `3_5:1043`). `EEShift` (`‖EE(u+Δ) − EE(u)‖ ≤ 16 N² η_{u+Δ}^{-7} Δ`, `N = (WL)^d`) is a Lean-only time-discretisation bound; it has no statement in the paper (audit round 1, §5 (iii)).
- Registry (DECISIONS §20): no line added; no theorem of this file takes `EECutIdentity`, `QVPropagated` or `EEShift` as a hypothesis. The first ticket that does (ST-3) registers it. The root import is added by the hub at merge.
- Nothing blocks the mathematics; no statement was weakened.
