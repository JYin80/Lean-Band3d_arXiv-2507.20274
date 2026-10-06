Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 14:49:21 UTC 2026

Notation: `n = N = (WL)^d = |Idx d L W|`; `Eblk a = W^{-d} 1_{[a]}`; `SBgue = L^{-d}`; `m(+) = m`, `m(-) = conj m`.
Source: RBM2D `c9a24cf` `Universality/GUEPhase/Generator.lean:1-1148`, saved read-only as `scratchpad/T2305_src.txt`.

### (i) Exponent table

| # | quantity | value at `d` | constraint it must satisfy (where it enters) | slack |
|---|---|---|---|---|
| 1 | coordinate variance `gueVar` | `1/N` diag, `1/(2N)` off-diag (real coords), `N = (WL)^d` | must equal `|Idx d L W|^{-1}` so that the leaf `sum_c gueVar_c tr(A D_c C D_c) = N^{-1} trA trC` holds (off-diag: re and im coordinate give `(A_ii C_jj + A_jj C_ii)` twice with weight `1/(2N)`; the `A_ji C_ji` terms cancel by `1 + i^2 = 0`) | equality, any `N` |
| 2 | prefactor `W^d` of `primRhsGUE`, `egtNGUE` | `W^d` (RBM2D `W^2`) | `2 * (1/2) * W^{2d}/N = W^d L^{-d}`, from `tr A = W^d sum_b tr(A E_b)` (`sum_b E_b = W^{-d} 1`) twice, times `N^{-1}=(WL)^{-d}`, times `SBgue = L^{-d}` | equality; `W^{2d}/N = W^d L^{-d}` = 0.2963 at `d,L,W = 3,3,2` |
| 3 | `SBgue` entry | `L^{-d}` (RBM2D `L^{-2}`) | `sum_a SBgue_{ab} = L^d L^{-d} = 1` (`|Z_L^d| = L^d`; used for the `m`-cancellation and in row 2) | equality |
| 4 | `Eblk` data | `tr E_a = |[a]| W^{-d} = 1`; `sum_a E_a = W^{-d} 1` | `|[a]| = W^d` (block of `Z_{WL}^d`) | equality; `W^d W^{-d} = 1.0` |
| 5 | auxiliary flow time in the second derivative | `1` (`HflowBlock d L W 1 omega_M = blockMat M`) | source lines 345, 377, 397, 612-614 carry `2 u W^d` at `u = 1`; the `1/2` outside leaves `W^d` | exact; no `d` |
| 6 | spectral derivative | `d_u ztOf m E u = -m` (`ztOf m E v = E + (1-v) m`) | `d_u G(+) = -m G^2`, `d_u G(-) = -conj(m) G^2` (`hasDerivAt_green_moving`, needs `M` Hermitian, `Im z != 0`); contributes `-m(sigma_k) W^d sum_b L(cut_k^{(b)})` | exact, any `m` |
| 7 | `m`-cancellation | `egtNGUEOf` carries `-m(sigma_k) W^d sum_{a,b} tr(E_a) SBgue_{ab} L(cut_k^{(b)})` | rows 3,4: `sum_a tr(E_a) SBgue_{ab} = 1`, so it cancels row 6 | equality |
| 8 | `Im m` | `> 0` (generic); band `m = mE E`, `Im mE E = sqrt(4-E^2)/2 > 0` for `|E| < 2` | `Im z_u = (1-u) Im m != 0` for `H - z` to be invertible for Hermitian `H` (the only use of `hE` in the source: lines 724, 1077, via `spectralM_im_pos`; `spectralM E` appears elsewhere only through `spectralMSign`, line 720-810) | at `E=0,u=1/2,m=i`: `Im z = 0.5` |
| 9 | time `u` | `u < 1` (generic and band); `0 <= u` carried in band pins only, unused (source `_hu0`) | `Im z_u = (1-u) Im m > 0` | `1 - u = 1/2` |
| 10 | `3 <= L` | carried, unused (source `_hL`) | column sums of `SBgue` need only `NeZero L` | numerics below at `L = 1, 2, 3` |
| 11 | loop length `k` | generic `loopGenGUEOf`: every `k` (`k = 0`: both sides `0` (constant trace, empty sums); `k = 1`: `primRhsGUE = 0` (`Ioc 1 1` empty)); band `loopGenGUE`: `2 <= k`, `loopGenGUE_one`: `k = 1` | no relation between `k` and `d, L, W` | none needed |
| 12 | `3 <= d` | not used by any statement | no step uses `d >= 3`: no `log`, no `Kstab`, no neighbour count, no scalar `^2` | numerics at `d = 2` also agree |

d-token count (script `grep`, source lines 1-1148): 46 lines match `\^ 2|Z2,|card_prod|ZMod.card|W²|L²|(W L)²|d = 2`
(identical to the ticket's list), classified by script: 21 `(W:C)^2 -> W^d` (prefactor), 8 `(W*L)^2 -> (W*L)^d` (`N`), 1 `((W:C)^-1)^2 -> (W^d)^-1`
(line 284), 2 `((L:C)^2)^-1 -> (L^d)^-1` (289-290), 2 `Z2/card_prod/ZMod.card` (1016-1017, replaced by merged `sum_SBgue_col`), 12 docstring/comment.
Scalar `^ 2` (not `W`, `L`, `(W L)`) in lines 1-1148: 0. Every `d`-dependence is of the form `W^d`, `L^d`, `(WL)^d`.

### (ii) One concrete nondegenerate instance (ticket data, `d=3, L=3, W=2, E=0, u=1/2, M=2*I`, `m = i = mE 0`)

Hypotheses at once: `NeZero 3`, `NeZero 2`; `3 <= L` (3); `|E| = 0 < 2`; `0 <= 1/2 < 1`; `M = 2*I` Hermitian on `Idx 3 3 2` (216 points, 27 blocks, `M = 2*I != 0`);
`Im m = 1 > 0`; `k = 2, 3` (`2 <= k`); no external hypothesis (every hypothesis is scalar/size/Hermiticity), so no limit computation is owed.
Brute force: all coordinates `c` (46656 nonzero directions: 216 diagonal, 2 x 23220 off-diagonal), central differences `h = 1e-3`, both sides from the definitions (`gueVar`, `coordinateMatrix`, `cutGlue`, `cutGlueL/R`, `Gres`, `Eblk`, `SBgue`, prefactor `W^d`):

```
$ python3 instance.py 2   # sigma=(+,-), a=(0,0)
d=3 L=3 W=2 N=(WL)^d=216 blocks=L^d=27 E=0.0 u=0.5 m=1j M=2*I k=2: lhs=1.938923e-02+0.000000e+00j rhs=1.938922e-02+7.589415e-19j relerr=3.49e-08 |tr E_a - 1|=0e+00
$ python3 instance.py 3   # sigma=(+,-,+), a=(0,0,0)
d=3 L=3 W=2 N=(WL)^d=216 blocks=L^d=27 E=0.0 u=0.5 m=1j M=2*I k=3: lhs=1.885531e-03-1.825884e-04j rhs=1.885532e-03-1.825888e-04j relerr=2.27e-07 |tr E_a - 1|=0e+00
```

Same identity at random Hermitian `M` (seed 7), `E=0.3`, `u=0.4`, band `m = mE E` and generic `m = 0.2+0.9i`, `d=3`; also `L=2,W=2` and `L=1,W=2/3` (`W != L`, `3 <= L` unused), with the wrong-exponent control (`W^2, L^-2` instead of `W^d, L^-d`), and a `d=2` sanity case:
```
$ python3 gen_check.py
d=3 L=3 W=1 m=mE k=1 loop=1: relerr=3.78e-05
d=3 L=3 W=1 m=mE k=2 loop=2: relerr=1.93e-06
d=3 L=3 W=1 m=mE k=3 loop=3: relerr=6.50e-05
d=3 L=3 W=1 m=mE k=3 loop=3b: relerr=3.29e-05
d=3 L=3 W=1 m=0.2+0.9i k=1 loop=1: relerr=1.59e-06
d=3 L=3 W=1 m=0.2+0.9i k=2 loop=2: relerr=4.37e-06
d=3 L=3 W=1 m=0.2+0.9i k=3 loop=3: relerr=4.68e-06
d=3 L=3 W=1 m=0.2+0.9i k=3 loop=3b: relerr=1.05e-05
d=3 L=2 W=2 L=2,W=2,m=mE k=1 loop=1: relerr=8.05e-06
d=3 L=2 W=2 L=2,W=2,m=mE k=2 loop=2: relerr=3.82e-06
d=3 L=2 W=2 L=2,W=2,m=mE k=3 loop=3: relerr=6.75e-06
d=3 L=2 W=2 L=2,W=2,m=mE k=3 loop=3b: relerr=3.61e-06
d=3 L=1 W=2 L=1,W=2 k=2 loop=2: relerr=4.24e-06  | wrong-exponent control (W^2, L^-2): relerr=5.00e-01
d=3 L=1 W=2 L=1,W=2 k=3 loop=3: relerr=6.08e-06  | wrong-exponent control (W^2, L^-2): relerr=5.00e-01
d=3 L=1 W=3 L=1,W=3 k=2 loop=2: relerr=4.37e-06  | wrong-exponent control (W^2, L^-2): relerr=6.67e-01
d=3 L=1 W=3 L=1,W=3 k=3 loop=3: relerr=7.14e-06  | wrong-exponent control (W^2, L^-2): relerr=6.67e-01
d=2 L=3 W=1 d=2 control k=1 loop=1: relerr=2.97e-05
d=2 L=3 W=1 d=2 control k=2 loop=2: relerr=3.85e-06
d=2 L=3 W=1 d=2 control k=3 loop=3: relerr=1.91e-04
d=2 L=3 W=1 d=2 control k=3 loop=3b: relerr=1.03e-04
$ for h in 4e-3 2e-3 1e-3 5e-4: HSTEP=$h python3 gen_check.py m=mE | grep loop=3:   # O(h^2) convergence
relerr: 1.04e-03, 2.60e-04, 6.50e-05, 1.62e-05
$ python3 -c ...   # parameter identities
mE(0) = 1j == I: True; Im z_u = 0.5 = (1-u) Im m; W^2d/N = 0.2963 = W^d L^-d; sum_a SBgue_ab = 1.0; tr E_a = 1.0; (W^2 L^-2)/(W^d L^-d) = 0.5 (L=1,W=2), 0.333 (L=1,W=3)
```
Reading: every error is the `O(h^2)` finite-difference error (halving `h` divides it by 4); the identity `genMatGUE(L) = primRhsGUE(L) + egtNGUE` holds at `d=3` for the band `m` and a generic `m`; the control with `W^2, L^-2` fails with relative error `0.5`, `0.667` (`= 1 - W^{2-d}` at `L = 1`, `W = 2, 3`), so the exponents `W^d`, `L^{-d}`, `N=(WL)^d` are forced.

### Verdicts
- Targets 1 (vocabulary, `genMatGUE_eq_Of`, `egtNGUE_eq_Of`): PASS. `genMatGUE = genMatGUEOf (mE E)` is `rfl` (`zt_eq_ztOf`); `egtNGUE = egtNGUEOf (mE E)` needs `tr E_a = 1` (row 4) and `mSigma E = mSigOf (mE E)`; numerics confirm `|tr E_a - 1| = 0`.
- Target 3 (`loopGenGUEOf`, every `k`, `0 < m.im`, `u < 1`): PASS (rows 1-9, 11); the class-P generalization uses `m` only through `d_u ztOf = -m` and `m(sigma)`.
- Target 4 (`loopGenGUE`, `loopGenGUE_one`): PASS (from 3 at `m = mE E`, `spectralM_im_pos`; unused `3 <= L`, `0 <= u`).
- Statement-level finding: no statement of `:1-1148` is false at general `d`; the one dimension-dependent identity is row 2 (`W^{2d}/N = W^d L^{-d}`).
- Overall: PASS.

## (b) Script output (stage 1b, written Tue Oct  6 15:11:19 UTC 2026; evidence scripts run Oct  6 15:10:27 UTC 2026; worktree clean; git log -2: see below)

$ git --no-optional-locks log --oneline -2; git --no-optional-locks status --short | wc -l   # in the worktree, Tue Oct  6 15:11:19 UTC 2026
9ab0f74 T2305: add the k = 0 instance of loopGenGUEOf, tidy the instance docstring
5577542 T2305: UN-28 Universality/GUEPhase/Generator (Lemma 2.11 for the GUE profile, class P)
0
$ git --no-optional-locks diff --stat main...t/T2305
 RBM3D/Universality/GUEPhase/Generator.lean | 1415 ++++++++++++++++++++++++++++
 1 file changed, 1415 insertions(+)

### B1. build (run 15:04:51 UTC on the committed file, HEAD 9ab0f74)
$ lake build RBM3D.Universality.GUEPhase.Generator > build4.log 2>&1; echo $?; tail -8 build4.log
0
Note: This linter can be disabled with `set_option linter.style.longLine false`
ℹ [3338/3338] Built RBM3D.Universality.GUEPhase.Generator (10s)
info: RBM3D/Universality/GUEPhase/Generator.lean:1411:0: 'RBM.Univ.GUEPhase.genMatGUE_eq_Of' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1412:0: 'RBM.Univ.GUEPhase.egtNGUE_eq_Of' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1413:0: 'RBM.Univ.GUEPhase.loopGenGUEOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1414:0: 'RBM.Univ.GUEPhase.loopGenGUE' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1415:0: 'RBM.Univ.GUEPhase.loopGenGUE_one' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3338 jobs).

### B2. hygiene
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/GUEPhase/Generator.lean
0
$ wc -l RBM3D/Universality/GUEPhase/Generator.lean
    1415 RBM3D/Universality/GUEPhase/Generator.lean
### B3. target statements, extracted by script (python3 extract.py <names>; vocabulary defs: binder line `variable` and signature up to `:=`)
58:variable (d L W : ℕ) [NeZero L] [NeZero W]
62-62:
def mSigOf (m : ℂ) (σ : Bool) : ℂ :=

68-69:
def genMatGUEOf (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=

79-80:
def egtNGUEOf (m : ℂ) (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=

89-89:
def genMatGUE (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=

97-97:
def egtNGUE (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=

1142-1145:
theorem genMatGUE_eq_Of :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
      (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)),
      genMatGUE d L W E u M I = genMatGUEOf d L W (mE E) E u M I :=

1149-1152:
theorem egtNGUE_eq_Of :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
      (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : LoopIdx (Zd d L)),
      egtNGUE d L W E u M I = egtNGUEOf d L W (mE E) E u M I := by

1168-1174:
theorem loopGenGUEOf :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (m : ℂ), 0 < m.im → ∀ (E u : ℝ), u < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d L),
        genMatGUEOf d L W m E u M (loopOf σ a) =
          primRhsGUE d L W (loopL d L W (blockMat d L W M) (ztOf m E u)) (loopOf σ a) +
            egtNGUEOf d L W m E u M (loopOf σ a) := by

1229-1235:
theorem loopGenGUE :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
        genMatGUE d L W E u M (loopOf σ a) =
          primRhsGUE d L W (loopL d L W (blockMat d L W M) (zt E u)) (loopOf σ a) +
            egtNGUE d L W E u M (loopOf σ a) := by

1242-1246:
theorem loopGenGUE_one :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
      ∀ (σ : Fin 1 → Bool) (a : Fin 1 → Zd d L),
        genMatGUE d L W E u M (loopOf σ a) = egtNGUE d L W E u M (loopOf σ a) := by

### B4. instances (namespace RBM.Univ.GUEPhase.GeneratorCheck, d=3, L=3, W=2, E=0, u=1/2); full text of the generic-m, non-scalar-M one (the class-P core, k=3); application lines of all ten
example :
    genMatGUEOf 3 3 2 (1 / 5 + (9 / 10) * Complex.I) 0 (1 / 2) Generator_M0
        (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) =
      primRhsGUE 3 3 2 (loopL 3 3 2 (blockMat 3 3 2 Generator_M0)
          (ztOf (1 / 5 + (9 / 10) * Complex.I) 0 (1 / 2)))
          (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) +
        egtNGUEOf 3 3 2 (1 / 5 + (9 / 10) * Complex.I) 0 (1 / 2) Generator_M0
          (loopOf ![true, false, true] ![(0 : Zd 3 3), 1, 2]) :=
  loopGenGUEOf 3 3 2 _ (by simp) 0 (1 / 2) (by norm_num) Generator_M0 Generator_M0_isHermitian
    3 ![true, false, true] ![(0 : Zd 3 3), 1, 2]
-- application lines of all ten instances (grep -n on the file)
1303:  loopGenGUE 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
1316:  loopGenGUE 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
1326:  loopGenGUE_one 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
1335:  loopGenGUE_one 3 3 2 0 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
1347:  loopGenGUEOf 3 3 2 Complex.I (by simp) 0 (1 / 2) (by norm_num)
1361:  loopGenGUEOf 3 3 2 _ (by simp) 0 (1 / 2) (by norm_num) Generator_M0 Generator_M0_isHermitian
1372:  loopGenGUEOf 3 3 2 Complex.I (by simp) 0 (1 / 2) (by norm_num)
1384:  loopGenGUEOf 3 3 2 Complex.I (by simp) 0 (1 / 2) (by norm_num)
1394:  genMatGUE_eq_Of 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
1402:  egtNGUE_eq_Of 3 3 2 0 (1 / 2) (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ))
### B5. pins against the check file (scratch pins_scratch.lean = check file section 2 verbatim + 5 pin examples + 5 vocabulary rfl examples; not committed)
$ lake env lean pins_scratch.lean > pins_scratch.out 2>&1; echo $?; wc -l < pins_scratch.out; grep -c "^example" (the part after `namespace RBM.Univ.GUEPhase`)
exit 0, output lines 0
example : T2305Check.T2305_genMatGUE_eq_Of := genMatGUE_eq_Of
example : T2305Check.T2305_egtNGUE_eq_Of := egtNGUE_eq_Of
example : T2305Check.T2305_loopGenGUEOf := loopGenGUEOf
example : T2305Check.T2305_loopGenGUE := loopGenGUE
example : T2305Check.T2305_loopGenGUE_one := loopGenGUE_one
(then 5 vocabulary rfl examples: mSigOf, genMatGUEOf, egtNGUEOf, genMatGUE, egtNGUE = T2305Check.<name>V)

### B6. registry pre-check and whole-library build
$ lake env lean registry_precheck.lean > registry.out 2>&1   # file: import RBM3D; import RBM3D.Universality.GUEPhase.Generator; #assert_rbm_axioms
exit 0
axiom audit: 8651 theorems, 2833 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -c 'Generator\|genMatGUE\|egtNGUE\|loopGenGUE' RBM3D/Test/Axioms.lean   # registry lines owed/added
0
$ lake build   # whole library on t/T2305; RBM3D.lean unchanged (the hub adds the root import at merge)
exit 0
Build completed successfully (4111 jobs).

### B7. name-clash grep: grep -rnw <name> RBM3D/ --include=*.lean, hits outside the new file
 mSigOf:0 genMatGUEOf:0 egtNGUEOf:0 loopGenGUEOf:0 genMatGUE:0 egtNGUE:0 genMatGUE_eq_Of:0 egtNGUE_eq_Of:0 loopGenGUE:0 loopGenGUE_one:0 GeneratorCheck:0

### B8. port (source RBM2D c9a24cf, RBM2D/Universality/GUEPhase/Generator.lean:72-1148; RBM2D HEAD hash below)
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/Generator.lean
 RBM2D/Universality/GUEPhase/Generator.lean | 120 ++++++++---------------------
 1 file changed, 32 insertions(+), 88 deletions(-)
$ python3 cmp_port.py <git show c9a24cf:...Generator.lean> RBM3D/Universality/GUEPhase/Generator.lean | grep SUMMARY   # own import map (Z2 L -> Zd d L, Idx L W -> Idx d L W, ... W^2 -> W^d), per declaration
declarations in source (72-1148): 55 | in new file: 69 | statement identical after import map: 39
statement differs (14): genMatGUE egtNGUE Generator_hasDerivAt_Gsig_spec Generator_edgeTerm Generator_hasDerivAt_word_spec Generator_deriv_spec Generator_trace_edgeTerm Generator_pairCut Generator_specEdge Generator_avgErr Generator_sum_algebra Generator_edge_algebra loopGenGUE loopGenGUE_one
only in source (2): Generator_sum_SBgue_col Generator_core
only in new file (16): mSigOf genMatGUEOf egtNGUEOf Generator_sum_Eblk Generator_hasDerivAt_ztOf Generator_cutGlue_split Generator_loopL_eq Generator_gloopProd_nil Generator_gloopProd_cons Generator_gloopProd_append genMatGUE_eq_Of egtNGUE_eq_Of loopGenGUEOf Generator_diag_isHermitian Generator_M0_isHermitian Generator_M0_apply
identical statement, proof body differs (5): Generator_blockContraction Generator_Xmat_omega Generator_HflowBlock_one Generator_getD Generator_gloop_same

### Narrative
Facts (every number is in B1-B8; line numbers are of the committed file):
- Scope: the sole file `RBM3D/Universality/GUEPhase/Generator.lean` (1415 lines, commits 5577542 and 9ab0f74 on `t/T2305`); `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are untouched (no registry line expected: no `Prop`-valued definition, nothing owed; B6). Imports are the four of the ticket's import map, no Mathlib import.
- Result: the five pins of the check file section 2 hold with exactly their statements (B5: exit 0, no output) and the five vocabulary names are `rfl` to the check file's `...V` definitions; all five theorems depend only on `propext`, `Classical.choice`, `Quot.sound` (B1). No pinned signature, no hypothesis and no merged file was changed.
- Port: source lines 72-1148 hold 55 declarations; 39 have statements identical to the source after the import map, 14 differ, 2 are not ported (B8).
  - The 5 identical statements with edited proofs: `Generator_blockContraction` (`Generator_sum_Eblk`, and a closing `ring` since `((W*L)^d)` expands to `W^d * L^d`), `Generator_Xmat_omega` (`change Xentry ...`, there is no `Xmat_apply`), `Generator_HflowBlock_one` (final `rfl` removed), `Generator_getD` (`List.getD_eq_getElem?_getD`), `Generator_gloop_same` (private copies `Generator_cutGlue_split`, `Generator_loopL_eq`, `Generator_gloopProd_nil/cons/append`, as `LoopGenN.lean:373-405`).
  - The 14 differing statements: the two band defs (target 1: `zt E u`, `RBM.Green.avgErr d L W`, `loopL d L W (blockMat d L W M) (zt E u)` in place of `spectralZ`, `avgErr`, `LLf`); the class-P generalisation `spectralZ E -> ztOf m E`, `spectralMSign E -> mSigOf m`, `hE : |E| < 2 -> hm : 0 < m.im` in `Generator_hasDerivAt_Gsig_spec`, `Generator_edgeTerm`, `Generator_hasDerivAt_word_spec`, `Generator_deriv_spec`, `Generator_trace_edgeTerm`, `Generator_specEdge`, `Generator_edge_algebra`; `Generator_pairCut` (takes `z`, no `LLf`); `Generator_avgErr` (the band bridge `avgErr = tr(Gres .. * Eblk) - mSigOf (mE E) sigma`, used by `egtNGUE_eq_Of`); `Generator_sum_algebra` (binder `g` renamed `t`, uses merged `sum_SBgue_col`); `loopGenGUE`, `loopGenGUE_one` (`d` added, `LLf` replaced).
  - Not ported: `Generator_sum_SBgue_col` (merged `sum_SBgue_col`), `Generator_core` (its proof, generic in `m`, is the proof of the public `loopGenGUEOf`; `loopGenGUE`, `loopGenGUE_one` follow from it at `m = mE E` with `spectralM_im_pos`). `Generator_gueVar_diag/offDiag`, `Generator_leaf` and the contraction chain are identical after the import map: `(W*L)^d` is the `N` of `gueVar`.
- The only `d`-dependence is `W^d`, `L^d`, `(WL)^d` (section (a) (i): 46 lines classified, 0 scalar `^ 2`); `grep -n '\^ 2'` on the new file has one hit, header docstring line 19 (`W ^ 2 -> W ^ d`, `(W * L) ^ 2 -> (W * L) ^ d`).
- Instances (B4): ten `example`s in `GeneratorCheck` at `d = 3`, `L = 3`, `W = 2` (`Idx 3 3 2`: 216 sites), `E = 0`, `u = 1/2`: `loopGenGUE` k = 2, 3; `loopGenGUE_one` (+) and, at the non-scalar Hermitian `Generator_M0` (entry `(0,1)` equal to 1, `Generator_M0_apply`), (-); `loopGenGUEOf` at `m = I` for k = 0, 1, 2 and at the generic `m = 1/5 + (9/10) I` with `Generator_M0`, k = 3; `genMatGUE_eq_Of`, `egtNGUE_eq_Of`. Every hypothesis is discharged (scalar, size, Hermiticity); no external premise.
- Not done in stage 1b: the paper TeX was not re-read (the dimension evidence is section (a) (i)-(ii), including the numerical identity at `d = 3` and the wrong-exponent control); the full-library `lake build` does not contain the new module until the hub adds the root import.

## (c) Verified Mathlib / merged names used (`#check`; signatures abbreviated)
- `HasDerivAt.ofReal_comp : HasDerivAt f u z -> HasDerivAt (fun y => (f y : C)) (u : C) z` (new vs. `LoopGenN`; used in `Generator_hasDerivAt_ztOf`)
- `HasDerivAt.star` (needs `TrivialStar` of the base field; used for `conj (ztOf m E v)`), `HasDerivAt.const_add`, `HasDerivAt.mul_const`, `hasDerivAt_const`
- `HasFDerivAt.comp_hasDerivAt`, `deriv_comp_add_const`, `Finset.sum_nbij'`, `Equiv.sum_comp`, `Real.mul_self_sqrt`
- `List.getD_eq_getElem?_getD : l.getD i a = l[i]?.getD a` (core; replaces `List.getD_append_right`)
- `List.map_fst_zip`, `List.sum_map_mul_left`, `Matrix.trace_list_sum`, `Matrix.submatrix_mul_equiv`, `Matrix.isHermitian_diagonal_iff`
- merged `RBM.Gauss.coordinateMatrix_isHermitian : (coordinateMatrix d L W c).IsHermitian` (all `#check`ed in one scratch file importing the new module: `lake env lean names.lean`, exit 0, no error line)
- verified absent / not visible (compile errors in the tool log): `List.getD_append_right` is `Mathlib/Data/List/GetD.lean:74` but not in the transitive imports of the four imported modules ("Unknown constant"); `RBM.Gauss.Xmat_apply` ("Unknown identifier"); `RBM.Endpoints.gueVar` (RBM2D name; the twin is `RBM.Univ.gueVar`); a public `sum_Eblk` (only the private `contraction_sum_Eblk`, copied as `Generator_sum_Eblk`)

## (d) Open issues and paper-delta candidates
- Open issues: none. Nothing owed is proved or assumed; no unproved premise is used (every hypothesis is a scalar, size or Hermiticity condition); the class-P statement `loopGenGUEOf` is the general one, the band forms are its instance `m = mE E` (the band forms alone would not be the general statement).
- `T2305a` (Lean structure, not a paper delta): class P of T2173: the generator identity is stated for the generic flow `ztOf m E u` at every `m` with `Im m > 0`, every `u < 1` and every loop length `k` (no `3 <= L`, no `0 <= u`, no `|E| < 2`); the band `zt E u` is `m = mE E` (`genMatGUE_eq_Of` is `rfl`).
- `T2305b` (bookkeeping, not a paper delta): `(WL)^2 -> (WL)^d`, `W^2 -> W^d`, `L^{-2} -> L^{-d}`; no other `d`-dependence in the generator identity (section (a) (i)).
- `T2305c` (Lean structure, not a paper delta): `LLf` has no general-size RBM3D twin, replaced by `loopL d L W (blockMat d L W M) (zt E u)` (the ticket records `= STLIM sz n E u M` by `rfl`, `Induction/Step2Defs.lean:713`; not re-checked in this stage); the GUE generator carries no coupling `g`.
- Observation (no delta): the band pins `loopGenGUE`, `loopGenGUE_one` carry `3 <= L` and `0 <= u` that the proofs do not use (intro names `_hL`, `_hu0`), as in the source and as pinned.
