Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 03:09:20 UTC 2026

Targets restated only as far as needed. **T1** `stLoopGenNForm_holds d : STLoopGenNForm d`
(`Induction/HierarchyN.lean:42`): for `sz n`, `|E|<2`, `0<=u<1`, Hermitian `M`, `k>=2`, `sigma`, `a`:
`genMat d L W g E u M (loopOf sigma a) = STllPairN + STegtM` (`L=sz.L n, W=sz.W n, g=sz.lam n`);
`genMat = 1/2 sum_c gvarF_c d^2_c loopL(blockMat(M+y X_c))(zt E u) + d_v loopL(blockMat M)(zt E v)|_{v=u}` (OneStep.lean:68).
**T2** `qvPropagatedN`: same hypotheses and `kappa : (Fin k -> Zd d L) -> C`:
`sum_c gvarF_c ||sum_b kappa_b loopDerivN(X_c; sigma, b)||^2 <= k * Re sum_{b,b'} kappa_b conj(kappa_b') STeeM sigma b b'`.
`hierarchyN_holds` is the one-line corollary of T1 (HierarchyN.lean:69 `hierarchyN_of_loopGenN`).

### (i) Exponent table

**A. `d = 2` tokens** (command: `python3 tok.py` on `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/{LoopGenN,QVN}.lean`, files of 575 / 739 lines; output = line numbers):

| RBM2D token (file: lines) | `d >= 3` replacement | why it holds |
|---|---|---|
| `Z2 L` (LoopGenN 49 lines, QVN 48), `Idx L W`/`BlockIndex` (25 / 45) | `Zd d L`, `Idx d L W`, `Vtx d L W` | index type only; no step uses `d = 2` |
| `(W:C)^2` (LoopGenN 223,412,466,470,472,501,514,515,522,523; QVN 222,260,262,574,588) | `(W:C)^d` | block size `W^d`: `tr E_a = 1`, `sum_b E_b = W^{-d} 1` (so `m·1 = m W^d sum_b E_b`, spectral cut); contraction `S_ij = W^{-d} SB`, `sum_{i in p} P_ii = W^d tr(P E_p)` gives `W^{-d}·W^{2d} = W^d` (same-edge and pair cuts) |
| `(W:C)^{-1}^2` (QVN 230,245,261,262) | `((W:C)^d)^{-1}` | entries of `Eblk` are `W^{-d}` on the block |
| `SB L` (LoopGenN 14 lines, QVN 8) | `SB d L g`, `g = sz.lam n` | RBM2D's fixed 5-point profile becomes `sbKernel` (Block.lean:38): `1/(1+2dg^2)` at `0`, `g^2/(1+2dg^2)` at `zdistD = 1` |
| column sums `sum_a SB a b = 1` (`LoopGenN_sum_SB_col`, line 436, uses `3<=L`) | same, `sum_SB_row` (Block.lean:108) | `(1+2dg^2)^{-1}(1 + #{x: zdistD x = 1} g^2) = 1` needs `#{...} = 2d`, true for `L >= 3` (Neighbours.lean `card_nbhd`); `sz.three_le_L n` supplies it |
| `gvar`, `Coord`, `svar` (LoopGenN 91; QVN 23 lines) | `gvarF`, `CoordF`, `svarF` (FineModel.lean:47,89) | `svarF = W^{-d} SBR`; `gvarF = svarF` on the diagonal, `svarF/2` off it; unused coordinates (key `i > j`) give the zero matrix |
| `spectralZ`, `spectralMSign`, `gloop`, `Gsig`, `LLf`, `avgErr` | `zt`, `mSigma`, `loopL`, `Gres`, `STLIM`, `STavgErrM` | vocabulary only (`zt E u = E + (1-u) mE E`, `d_v zt = -mE`) |
| `\|^ 2` other (QVN 605-611, 657-671, 698, 712, 725) | unchanged | squares of norms, Cauchy-Schwarz `||sum_j P_j||^2 <= k sum_j ||P_j||^2` (`QVN_norm_sum_sq_le`, QVN:604): dimension-free |
| `scaleM, ellT, tailT, ellStar, Meta, ellz`, `1/5`, `N2`, `inv2`, `(W*L)^2`, `(L:R)^2` | none occur | `tok.py` prints `n=0` for every one of these in both files |

How `loopGenN` gives `STLoopGenNForm` exactly: port the general statement
`genMat d L W g E u M (loopOf sigma a) = W^d sum_{k'∈Icc 1 len} sum_{l'∈Ioc k' len} sum_{a,b} loopL(.. cutGlueL k' l' a ..) SB a b loopL(.. cutGlueR k' l' b ..) + W^d sum_{k'∈Icc 1 len} sum_{a,b} (loopL(<[sigma_{k'-1}],[a]>) - mSigma E sigma_{k'-1}) SB a b loopL(.. cutGlue k' b ..)`
for all `(d L W g)`, `3<=L`, then instantiate at `(sz.L n, sz.W n, sz.lam n)`. The two right terms are `STllPairN` (HierAlgebra.lean:693) and
`STegtM` (Step2Defs.lean:750) after unfolding `STLIM` (Step2Defs.lean:713, `= loopL (blockMat H) (zt E tau)`) and `STavgErrM` (Step2Defs.lean:745). The proof is RBM2D's: `genMat` Hessian = same-edge + pair cuts
(`sum_coordinateSecondWordDeriv_allCuts`), spectral derivative = single-edge insertions, then the one algebraic identity `sum_{a,b}(t_a - m) S_ab f_b = sum f_p S_pq t_q - m sum f_p` using `sum_a SB a b = 1`. No hypothesis beyond `3<=L` is used; `d` need not be `>=3`.

**B. Exponents, thresholds, constants**

| item | value | constraint | slack |
|---|---|---|---|
| `d` | 3 | statements and proofs are uniform in `d : N` (table A) | n/a |
| `L` | 3 | `3 <= L` (`sz.three_le_L`): row/column sums of `SB` are `1` | `0` at `L = 3` (met; printed row sums `1.000000000000000`, min = max) |
| `W` | 2 (`W^d = 8` points per block) | `W >= 1` (`NeZero`) | none needed; `N = (WL)^d = 216`, `L^d = 27` blocks |
| `g` (= `sz.lam n`) | `1/2`: `1+2dg^2 = 2.5`, kernel `0.4` at `0`, `0.1` at the 6 neighbours, row sum `0.4+6·0.1 = 1` | any real | none needed |
| `E` | `0.7` | `\|E\| < 2` (`Im mE > 0`) | `2-\|E\| = 1.3`; `Im m = 0.93675` |
| `u` | `0.5` | `0 <= u < 1` for `eta_u = (1-u) Im m > 0` (`0<=u` unused in the proof) | `1-u = 0.5`; `eta_u = 0.46837` |
| loop length `k` | 3, `sigma = (+,-,+)` | `2 <= k` | slack 1; pair terms `k(k-1)/2 = 3`, edge terms `3`; `a = (b0, b9, b22)` (blocks as indices of `Z_3^3`) |
| prefactor of `llPairN`, `egtN`, `eeN` | `W^d` | exact count in table A | identity, no slack: numerical relative gap `~1e-16` below |
| `#CoordF` | `2N^2 = 93312`, nonzero `coordinateMatrix`: `N + N(N-1) = 46656` | the literal sum runs over all of `CoordF` | none |
| `k` in `qvPropagatedN` | `3` = number of cuts | Cauchy-Schwarz over `k` cuts | `LHS/(k Re) = 0.3088` at the main instance; factor `1` is false in general: `LHS/Re = 1.0931 > 1` at `d=3,L=3,W=1` (below) |

### (ii) One concrete nondegenerate instance

`d = 3, L = 3, W = 2` (`N = 216`), `g = 1/2`, `E = 0.7`, `u = 1/2`, `k = 3`, `sigma = (+,-,+)`, `a` = blocks `(0,0,0),(1,0,0),(2,1,1)` (indices 0, 9, 22), one Hermitian `M` (a sample of the model law, `||M||_op = 1.9971`).
All hypotheses of T1 and T2 hold (`3<=L`, `|E|<2`, `0<=u<1`, `M` Hermitian, `2<=k`, no `N=0`, no collapsed window; every loop value is nonzero, magnitudes `~1e-5` because of `w = W^{-d} = 1/8` per `E`). No external hypothesis, so no limit computation.
Script (python, numpy 2.0.2; scratchpad `T2103/check.py`, `qv.py`; no Lean). It computes `genMat` three ways: the covariance contraction `sum_c gvarF_c X_c⊗X_c = sum_ij S_ij E_ij⊗E_ji` (exact), the literal sum over all nonzero coordinates by central second differences (`h = 1e-3`) and `d_v` by central difference, and the right side `STllPairN + STegtM` from the definitions (cutGlueL/R/cutGlue, `SB d L g`, `mSigma`).

T1, k = 3: command `python3 check.py 3 3 2 0.5 1 k3` (0.4 s) and `python3 check.py 3 3 2 0.5 1 k3literal` (several minutes; literal coordinate sum):
```
d=3 L=3 W=2 N=(WL)^d=216 g=0.5 E=0.7 u=0.5  SB row sums min/max 1.000000000000000 1.000000000000000  SB symmetric True
M Hermitian: True  ||M||_op = 1.9971
k=3 sigma=+-+ a=[0, 9, 22]: genMat[contraction]=4.9248586615e-06+1.3993837437e-05j  pair=3.030444e-06+7.118309e-06j egt=1.894415e-06+6.875528e-06j  RHS=4.9248586615e-06+1.3993837437e-05j  |diff|=3.05e-21
   literal coordinate sum (all 46656 nonzero X_c), FD:  genMat=4.9248625134e-06+1.3993849118e-05j   |lit-RHS|=1.23e-11   (|RHS| = 1.48e-05; FD error O(h^2))
```
Also checked (same script, other sizes, all `|genMat - RHS| < 5e-17` by contraction, literal sum `< 2e-7`): `python3 check.py 1 3 2 0.5 1 literal` and `python3 check.py 3 3 1 0.5 1 literal` at `k = 2, 3, 4`; `python3 check.py 2 3 1 0.5 2` at `k = 2, 3, 4` (contraction only). So `STLoopGenNForm` holds at `d = 1, 2, 3` numerically, and `k = 2, sigma = (+,-)` is the merged `LoopGenN2` shape.

T2, k = 3: command `python3 qv.py main` (11 s); `kappa` random complex on the three loops `b = (0,9,22), (0,9,13), (5,9,22)`; `STeeM` is computed from `STeeLoop` (Step34Pins.lean:152) with `SB d L g`, prefactor `W^d`, and checked against the explicit 8-loop trace:
```
d=3 L=3 W=2 N=216 g=0.5 E=0.7 u=0.5
   300 random coordinates: max rel |FD loopDerivN - (-tr(X_c T))| = 2.39e-08
   [brute check, p=2, beta=4, beta'=11] explicit loop 3.8417942645e-17-1.0118959188e-15j vs aggregated 3.8417942645e-17-1.0118959188e-15j |diff|=6.2e-32
   |support| = 3  Im parts: RHS double sum -4.6e-25, per-cut sum 1.7e-27
   LHS = sum_c gvar_c |sum_b kappa_b dL_b|^2 = 2.5908366240e-09
   Re sum kappa conj(kappa') eeN        = 2.7965732545e-09   (per-cut sum_j sum_xy S_xy A_j conj A'_j = 2.7965732545e-09, |diff| = 0.0e+00)
   k * Re(...) = 8.3897197635e-09;   LHS <= k*Re(...): True;  LHS/(k*Re) = 0.3088;  LHS > 0: True;  LHS/Re = 0.9264 (factor k needed iff > 1)
```
Here `LHS = sum_ij S_ij |T_ji|^2` with `T = sum_b kappa_b sum_p A_p(b)`, `A_p = G_p E_p F_{p+1}..F_{p-1} G_p`, `d_X L_b = -sum_p tr(X A_p(b))` (checked by finite differences on 300 random coordinates). The printed per-cut equality `Re sum kappa conj kappa' eeN = sum_j (cut j)` is the per-cut identity `eeN = sum_j W^d sum_{x,y} S^B_xy tr(A_j(b) E_x A_j(b')^H E_y)` of RBM2D `QVN_cut`/`QVN_eeN_eq` (`QVN:506`, `:592` at `c9a24cf`), and `LHS <= k·RHS` is Cauchy-Schwarz over the `k` cuts. Literal coordinate sums at smaller sizes, command `python3 qv.py small`:
```
d=1 L=3 W=2 N=6:  LHS literal (all nonzero coordinates, central FD of loopDerivN) = 6.1550015601e-01 ; contraction LHS = 6.1550015644e-01 ; Re sum = 6.3807025201e-01 (per-cut sum equal, |diff| 3.3e-16); LHS/Re = 0.9646
d=3 L=3 W=1 N=27: LHS literal = 4.4197488243e-04 ; contraction LHS = 4.4197488256e-04 ; Re sum = 4.0432283848e-04 (per-cut sum equal, |diff| 1.6e-19); LHS/Re = 1.0931 (> 1: `(𝓔⊗𝓔)` alone is not an upper bound, the factor `k` is needed)
```

### Verdicts
- **T1 `stLoopGenNForm_holds` (and `hierarchyN_holds`): PASS.** Hypothesis set satisfiable (instance above), identity holds numerically at `d = 3` to `3e-21` (contraction) and `1e-11` (literal coordinate sum); every `d = 2` token maps to `d` as in table A; no statement is false at `d >= 3`.
- **T2 `qvPropagatedN`: PASS.** Inequality holds with ratio `0.31` (main instance) and `0.36`, `0.32` (small); the factor `k` cannot be replaced by `1` (`LHS/Re = 1.093` at `d=3,L=3,W=1`), consistent with the ticket's "inequality form with factor `n`" (T2084, D152-D155).
- Caveat: one Hermitian sample and one `kappa` per instance; the numerics support, but do not replace, the proofs.

## (b) Script output

Prover model of this stage: claude-sonnet-5-5.  Branch `t/T2103`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2103`.  Section (a) is unchanged: no verdict in it was found wrong, so no (a').

### b.1 Build, axioms, registry pre-check, scope (`build.out`)
```
$ date -u
Sun Oct  4 03:23:57 UTC 2026
$ lake build RBM3D.Induction.LoopGenN RBM3D.Induction.QVN 2>&1 | tail -8
Note: This linter can be disabled with `set_option linter.style.longLine false`
warning: RBM3D/Path/StepDecomp.lean:52:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
ℹ [3762/3762] Replayed RBM3D.Induction.QVN
info: RBM3D/Induction/QVN.lean:873:0: 'RBM.Ind.qvPropagatedN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QVN.lean:874:0: 'RBM.Ind.loopDerivN' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3762 jobs).
$ lake build (full library; root import of the new modules is added by the hub)
 RBM.Path.UkerFar].
non-vacuity certificates: 4 of 107 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3847 jobs).
$ registry pre-check: lake env lean precheck.lean (import RBM3D, RBM3D.Induction.LoopGenN, RBM3D.Induction.QVN, #assert_rbm_axioms)
exit=0
axiom audit: 3233 theorems, 1182 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
$ grep -nE "sorry|admit|native_decide|^axiom" new files
(grep exit 1)
$ git diff --stat main...t/T2103
 RBM3D/Induction/LoopGenN.lean | 720 ++++++++++++++++++++++++++++++++++
 RBM3D/Induction/QVN.lean      | 874 ++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1594 insertions(+)
94131ca T2103: QVN docstring fix
     720 RBM3D/Induction/LoopGenN.lean
     874 RBM3D/Induction/QVN.lean
    1594 total
```

`#print axioms` of every new public declaration (`#print axioms` lines at the end of each file):
```
$ lake build RBM3D.Induction.LoopGenN RBM3D.Induction.QVN 2>&1 | grep -E "(LoopGenN|QVN).lean.*depends on axioms"
info: RBM3D/Induction/LoopGenN.lean:718:0: 'RBM.Ind.loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:719:0: 'RBM.Ind.stLoopGenNForm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:720:0: 'RBM.Ind.hierarchyN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QVN.lean:873:0: 'RBM.Ind.qvPropagatedN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QVN.lean:874:0: 'RBM.Ind.loopDerivN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.2 Target statements (extracted by script from the files; `extract.py`, `sed -n`)
```
--- RBM3D/Induction/LoopGenN.lean:548
theorem loopGenN (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ) (hL : 3 ≤ L) (hE : |E| < 2)
    (u : ℝ) (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    genMat d L W g E u M (loopOf σ a) =
      (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 (loopOf σ a).length,
          ∑ l' ∈ Finset.Ioc k' (loopOf σ a).length, ∑ x : Zd d L, ∑ y : Zd d L,
        loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlueL k' l' x) * SB d L g x y *
          loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlueR k' l' y) +
        (W : ℂ) ^ d * ∑ k' ∈ Finset.Icc 1 (loopOf σ a).length, ∑ x : Zd d L, ∑ y : Zd d L,
          (loopL d L W (blockMat d L W M) (zt E u)
              ⟨[(loopOf σ a).σ.getD (k' - 1) false], [x]⟩ -
            mSigma E ((loopOf σ a).σ.getD (k' - 1) false)) * SB d L g x y *
          loopL d L W (blockMat d L W M) (zt E u) ((loopOf σ a).cutGlue k' y) := by
--- RBM3D/Induction/LoopGenN.lean:615
theorem stLoopGenNForm_holds (d : ℕ) : STLoopGenNForm d := by
--- RBM3D/Induction/LoopGenN.lean:621
theorem hierarchyN_holds (d : ℕ) : HierarchyN d :=
--- RBM3D/Induction/QVN.lean:62
def loopDerivN (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d L) : ℂ :=
--- RBM3D/Induction/QVN.lean:799
def QVPropagatedN (d : ℕ) : Prop :=
--- RBM3D/Induction/QVN.lean:812
theorem qvPropagatedN (d : ℕ) : QVPropagatedN d := by
```
`QVPropagatedN` (`QVN.lean:799-810`) and the unchanged owed pin `STLoopGenNForm` (`HierarchyN.lean:42-47`; `git diff main...t/T2103 -- RBM3D/Induction/HierarchyN.lean` is empty, see the `--stat` above):
```
def QVPropagatedN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ),
        ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
            ‖∑ b : Fin k → Zd d (sz.L n), κ b *
              loopDerivN d (sz.L n) (sz.W n) E u M
                (coordinateMatrix d (sz.L n) (sz.W n) c) σ b‖ ^ 2 ≤
          (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
            κ b * (starRingEnd ℂ) (κ b') * sz.STeeM n E u M σ b b').re

/-- **`qvPropagatedN`** (RBM2D `Induction/QVN.lean:622`): the variance proxy of a propagated
---
def STLoopGenNForm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M (loopOf σ a) =
          sz.STllPairN n E u M (loopOf σ a) + sz.STegtM n E u M (loopOf σ a)
```
RBM2D pins at `c9a24cf` (`Induction/HierVocab.lean:547-552`, `:485-494`) for the statement comparison (CLAUDE ST1-COMMON item 6):
```
(`Path/DriftAlgebra.lean`).  Consumer: `HierarchyN` (row B3). -/
def LoopGenN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), 3 ≤ L → |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian →
    ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Z2 L),
      genMat E u M (loopOf σ a) = llPairN L W E u M (loopOf σ a) + egtN L W E u M (loopOf σ a)
---
identity of `def:CALE` / #22).  Consumers: the conditional-variance proxies of R2.6. -/
def QVPropagatedN : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ), 3 ≤ L → |E| < 2 → 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx L W) (Idx L W) ℂ, M.IsHermitian → ∀ (k : ℕ), 2 ≤ k →
    ∀ (σ : Fin k → Bool) (κ : (Fin k → Z2 L) → ℂ),
      ∑ c : Coord L W, (gvar L W c : ℝ) *
          ‖∑ b : Fin k → Z2 L, κ b * loopDerivN L W E u M (coordinateMatrix L W c) σ b‖ ^ 2 ≤
        (k : ℝ) * (∑ b : Fin k → Z2 L, ∑ b' : Fin k → Z2 L,
          κ b * (starRingEnd ℂ) (κ b') * eeN L W E u M σ b b').re
```

### b.3 Compiled nonempty instances (`inst.py`: proof terms; statements are in the cited lines)
`d = 3` throughout.  `loopGenN`: `L = 3`, `W = 2` (`Idx 3 3 2` has 216 sites), `g = 1/2`, `E = 1/2`, `u = 1/2`, `k = 3`, `M = LoopGenN_M0` a non-scalar Hermitian matrix (`LoopGenN_M0_apply` in the file proves its `(0,1)` entry is `1`).  The rest at the merged `sz0` (`L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), size `0`.  No hypothesis is left open; no `N = 0`, empty index set or `False` premise.
```
RBM3D/Induction/LoopGenN.lean:657-678  LoopGenN_check_loopGenN  (statement lines 657-675; proof term:)
  loopGenN 3 3 2 (1 / 2) (1 / 2) le_rfl (by norm_num [abs_of_pos]) (1 / 2) (by norm_num)
    LoopGenN_M0 LoopGenN_M0_isHermitian
    ![true, false, true] ![(0 : Zd 3 3), 1, 2]
RBM3D/Induction/LoopGenN.lean:682-690  LoopGenN_check_stLoopGenNForm_sz0  (statement lines 682-688; proof term:)
  stLoopGenNForm_holds 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) _ _
RBM3D/Induction/LoopGenN.lean:695-710  LoopGenN_check_hierarchyN_sz0  (statement lines 695-708; proof term:)
  hierarchyN_holds 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) _ _
RBM3D/Induction/QVN.lean:830-842  QVN_check_sz0_one  (statement lines 830-840; proof term:)
  qvPropagatedN 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 3 (by norm_num) ![true, false, true] (fun _ => 1)
RBM3D/Induction/QVN.lean:846-865  QVN_check_sz0_two  (statement lines 846-860; proof term:)
  qvPropagatedN 3 sz0 0 (1 / 2) (by norm_num [abs_of_pos]) (1 / 3) (by norm_num) (by norm_num)
    (coordinateMatrix 3 (sz0.L 0) (sz0.W 0)
      ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true))
    (coordinateMatrix_isHermitian 3 (sz0.L 0) (sz0.W 0) _) 3 (by norm_num) ![true, true, false]
    (fun b => if b 0 = b 1 then 1 else 0)
```

### b.4 Name-clash grep, ports, d = 2 tokens
```
Sun Oct  4 03:22:32 UTC 2026
$ git diff --stat main...t/T2103
 RBM3D/Induction/LoopGenN.lean | 720 ++++++++++++++++++++++++++++++++++
 RBM3D/Induction/QVN.lean      | 873 ++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1593 insertions(+)
$ git log main..t/T2103 --format="%h %s"
86b46e3 T2103: QVN (general-n variance proxy qvPropagatedN) and doc fixes
355531e T2103: LoopGenN (general-n loop generator; stLoopGenNForm_holds, hierarchyN_holds)
$ grep name clash (main worktree RBM3D/)
loopGenN:        0
stLoopGenNForm_holds:        0
hierarchyN_holds:        0
loopDerivN:        0
QVPropagatedN:        0
qvPropagatedN:        0
$ same names in the two new files (decl lines)
RBM3D/Induction/QVN.lean:62:def loopDerivN (E u : ℝ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ)
RBM3D/Induction/QVN.lean:799:def QVPropagatedN (d : ℕ) : Prop :=
RBM3D/Induction/QVN.lean:812:theorem qvPropagatedN (d : ℕ) : QVPropagatedN d := by
RBM3D/Induction/LoopGenN.lean:548:theorem loopGenN (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ) (hL : 3 ≤ L) (hE : |E| < 2)
RBM3D/Induction/LoopGenN.lean:615:theorem stLoopGenNForm_holds (d : ℕ) : STLoopGenNForm d := by
RBM3D/Induction/LoopGenN.lean:621:theorem hierarchyN_holds (d : ℕ) : HierarchyN d :=
$ grep -rn "LoopGenN_check\|QVN_check" main RBM3D (count)
       0
$ RBM2D diff-stat
9e0f275
 RBM2D/Induction/LoopGenN.lean |  53 +++-------------
 RBM2D/Induction/QVN.lean      | 137 ++++++++++++++----------------------------
 2 files changed, 51 insertions(+), 139 deletions(-)
```
```
$ d=2 token scan, new files (Z2, BlockIndex, "W ^ 2", "(W:ℂ)^2", scaleM, ellT, tailT, ellStar, Meta, ellz, N2, inv2)
RBM3D/Induction/LoopGenN.lean:17:rules R1-R4 of `docs/tickets/ST1-COMMON.md`; `Z2 L → Zd d L`, `Idx L W → Idx d L W`,
RBM3D/Induction/LoopGenN.lean:18:`BlockIndex L W → Vtx d L W`, `Gsig → Gres`, `spectralZ → zt`, `gloop L W → loopL d L W`,
RBM3D/Induction/QVN.lean:17:`Z2 L → Zd d L`, `Idx L W → Idx d L W`, `BlockIndex L W → Vtx d L W`, `Gsig → Gres`,
(count of ' ^ 2' occurrences, all norm squares:)
0
RBM3D/Induction/LoopGenN.lean:19:`Coord/gvar → CoordF/gvarF`, `SB L → SB d L g`, `W ^ 2 → W ^ d` (the block size `W^d`: `tr E_a = 1`,
RBM3D/Induction/QVN.lean:18:`spectralZ → zt`, `gloop → loopL`, `Coord/gvar → CoordF/gvarF`, `SB L → SB d L g`, `W ^ 2 → W ^ d`,
RBM3D/Induction/QVN.lean:697:    ‖∑ j, P j‖ ^ 2 ≤ (k : ℝ) * ∑ j, ‖P j‖ ^ 2 := by
RBM3D/Induction/QVN.lean:698:  calc ‖∑ j, P j‖ ^ 2 ≤ (∑ j, ‖P j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
RBM3D/Induction/QVN.lean:699:    _ ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) * ∑ j, ‖P j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
$ same scan on RBM2D sources (counts)
LoopGenN: Z2=49
LoopGenN: (W:ℂ)^2 / W)⁻¹ ^ 2 =10
QVN: Z2=48
QVN: (W:ℂ)^2 / W)⁻¹ ^ 2 =8
```
(The QVN `^ 2` lines are squares of norms: `‖Σ_j P_j‖^2`, Cauchy-Schwarz over the `k` cuts, dimension-free; all `W^2`/`Z2` occurrences of RBM2D are replaced, counts above.)

### b.5 Ports (CLAUDE.md §5.2)
Source: RBM2D `RBM2D/Induction/LoopGenN.lean` (575 lines) and `RBM2D/Induction/QVN.lean` (739 lines) at `c9a24cf`; RBM2D `HEAD` is `9e0f275`.  Also `RBM3D/Path/QVIdentity.lean:430-688` (merged, T2084; the `private` coordinate algebra, copied with prefix `QVN_`) and `RBM3D/Hierarchy/ContractionBasic.lean:791` (`LoopGenN_cutGlue_split`, `LoopGenN_gloopProd_*`: the merged versions are `private`).  Merged lemmas used, not copied: `sum_coordinateSecondWordDeriv_allCuts` (`Hierarchy/ContractionSecondLoop.lean:1173`), `hasDerivAt_deriv_gloop_update` (`Gauss/LoopCoordinate.lean:383`), `neg_trace_scalarDrift_cutGlue_split` (`Hierarchy/ContractionBasic.lean:859`), `sum_SB_row` (`Defs/Block.lean:108`), `hasDerivAt_green_moving` (`Gauss/FlowCalculus.lean:374`).

### b.6 Narrative (at most 40 lines)
1. `loopGenN` is RBM2D `LoopGenN` proved at general `(d, L, W, g)` with `3 <= L`, `u < 1`, `|E| < 2`, Hermitian `M`, any loop `(sigma, a)`; the right side is written out (not through `STllPairN`/`STegtM`, which need a `Sizes`), and `stLoopGenNForm_holds` is its instance at `(sz.L n, sz.W n, sz.lam n)` by `exact` (definitional unfolding of `STllPairN`, `STegtM`, `STLIM`, `STavgErrM`).  `hierarchyN_holds` is the one-line composition ordered by DECISIONS §32.
2. Route and renamings are those of section (a) (i): `W^2 -> W^d` (10 lines in LoopGenN, 8 in QVN, now `W^d`/`(W^d)^{-1}`), `Z2 -> Zd d`, `SB L -> SB d L g`, `Gsig -> Gres`, `spectralZ -> zt`.  The Hessian step uses the merged `sum_coordinateSecondWordDeriv_allCuts` at flow time `1` with the matrix `M` itself as the sample (`LoopGenN_omega`, `LoopGenN_HflowBlock_one`).
3. The only place `3 <= L` enters is `Sum_a S^B_{ab} = 1` (`LoopGenN_sum_SB_col`, `sum_SB_row`), supplied by `sz.three_le_L n` in `stLoopGenNForm_holds`.  `0 <= u` and `2 <= k` are not used (they stay in the pin `STLoopGenNForm`, whose type is unchanged).
4. `qvPropagatedN d : QVPropagatedN d`.  RBM2D's `loopDerivN` (a `def` of `HierVocab`, not ported by T2049) is defined here, public; `eeN` is `STeeM` (same `eeLoop` layout as `STeeLoop`, compared in the source).  The statement is `forall sz n`, `g = sz.lam n`, factor `k`; `3 <= L` is implied by `sz`, so RBM2D's explicit hypothesis `3 <= L` is dropped.  The factor `k` cannot be `1` (section (a), `LHS/Re = 1.0931` at `d = 3, L = 3, W = 1`); this agrees with the inequality form of T2084 (D152-D155, T2084c).
5. Residual differences from RBM2D after renaming (script-extracted pins above): (i) `LoopGenN : Prop` (RBM2D) is the merged `STLoopGenNForm d` (`HierarchyN.lean`, T2095), `llPairN + egtN` are `STllPairN + STegtM`; (ii) `QVPropagatedN : Prop` is `QVPropagatedN d` with `sz`; (iii) hypothesis `3 <= L` is absorbed into `sz`; (iv) `gvar` is `gvarF d L W g`, a `NNReal`-valued variance cast to `R` exactly as in the merged `QVPropagated`.
6. Registry (DECISIONS §20): no line added.  No theorem of the two files takes a `Prop` predicate as hypothesis.  `QVPropagatedN` is a new pin; the first ticket that assumes it (ST-3) registers it.  The owed line `RBM.Ind.STLoopGenNForm` in `RBM3D/Test/Axioms.lean:190` can go once this ticket merges (not edited here: `hierarchyN_of_loopGenN` still takes it as hypothesis; the pre-check above passes with the line present).
7. No scratch file is committed; scratch is in `scratchpad/T2103/` (`conv1.py`, `extract.py`, `inst.py`, `precheck.lean`, `names.lean`).  The root import of `RBM3D.Induction.LoopGenN` and `RBM3D.Induction.QVN` is added by the hub.

## (c) Verified Mathlib / project names (`#check` in `names.lean`, no error)
`Matrix.trace_mul_comm`, `Matrix.trace_list_sum`, `Finset.sum_nbij'`, `Finset.sum_Ico_add'`, `Finset.sum_range`, `sq_sum_le_card_mul_sum_sq`, `pow_le_pow_left₀`, `norm_sum_le`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.nonsing_inv_eq_ringInverse`, `List.sum_map_mul_left`, `List.getD_append_right`, `List.take_succ_eq_append_getElem`, `List.zip_append`, `List.map_fst_zip`, `List.map_snd_zip`, `deriv_comp_add_const`, `HasDerivAt.congr_deriv`, `Matrix.isHermitian_one`, `Matrix.IsHermitian.submatrix`, `Matrix.IsHermitian.coe_re_apply_self`.  Project names: `RBM.Gauss.neg_trace_scalarDrift_cutGlue_split`, `RBM.Gauss.sum_coordinateSecondWordDeriv_allCuts`, `RBM.sum_SB_row`, `RBM.Gauss.hasDerivAt_green_moving` (in namespace `RBM.Gauss`; the unqualified `#check` failed only for that reason).
Not found in the merged tree (`#check` of these exact qualified names gives `unknown identifier`): `Matrix.Xmat_apply`, `RBM.Loop.LoopIdx.cutGlue_split`, `RBM.Gauss.Gsig_true`, `RBM.Gauss.spectralM`.  (`Xmat_apply` exists only as `private fineModel_Xmat_apply`; `cutGlue_split`, `gloopProd_nil/cons/append` only as `private` in `ContractionBasic`/`GLoopFlow`; hence the `private` copies `LoopGenN_*`.)

## (d) Open issues and paper-delta candidates
- `T2103a`: `qvPropagatedN` carries the factor `k` (the number of cuts), not `1`: `(E (x) E)` of `defEOTE` (`3_5:166-190`) is not literally the quadratic variation (cross-cut terms).  This repeats T2084c / D152-D155 for general `n`; section (a) gives the numerical witness (`LHS/Re = 1.0931 > 1` at `d = 3, L = 3, W = 1`).  Nothing new to the paper's mathematics, only the Lean form.
- `T2103b`: coupling `g` of `S^{(B)}(g)` is a parameter of `loopGenN`, `QVN_core` (as T2084a, T2077a); `W^2` of RBM2D is `W^d` in every Lean statement (rule R3).  No other Lean/paper statement difference.
- Dispatcher actions: (1) remove the owed registry line `RBM.Ind.STLoopGenNForm` (`Axioms.lean:190`) after the merge, if desired; (2) `QVPropagatedN d` is a `Prop` pin to be registered by the first consumer (ST-3).

