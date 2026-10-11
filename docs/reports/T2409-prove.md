Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct 11 04:47:17 UTC 2026

Target (mathematics only). For `0 ≤ t < 1`, `BASelf`, `3 ≤ L`, every resolvent polynomial `f = P` and `x,y,y'`:
`𝔼[Ǧ_{y'x}Ǧ_{xy}f] = 𝔼[Σ_β (W−1)_{xβ}(M_{βy}M_{y'β} + Ǧ_{βy}M_{y'β} + M_{βy}Ǧ_{y'β}) f + Σ_{w,α,β} W_{xw}M_{wα}S_{αβ}(Ǧ_{ββ}G_{αy}Ǧ_{y'w}f + Ǧ_{αw}G_{βy}G_{y'β}f − G_{βy}Ǧ_{y'w}∂_{βα}f)]`
(pin `BAGGGamma`, probe `t/T2387:RBM3D/Probe/T2387Pins.lean:324-349`; paper `B:393-405` has `S⁺_{xβ}` in sums 1-2: D402).

### (i) Exponent / constant table (no scaling exponents enter: the target is an exact algebraic identity of expectations)
| quantity | value at the instance | constraint | slack |
|---|---|---|---|
| `t` | `1/2` | `0 ≤ t < 1` (`baW_isUnit`, Gershgorin) | `1 − t = 1/2` |
| `‖M⁺S‖_{row,1}` | `t·Σ_α|M_{xα}|² = 1/2` | `< 1` (diagonal dominance of `1 − M⁺S`) | `1/2` (Ward row `Σ_α|M_{xα}|² = 1`, `baM_row_sq`) |
| `L` | `3` | `3 ≤ L` (`svarF` row sums, `lwWxSizes`) | `0` (hypothesis, allowed) |
| `W`, `d` | `1`, `3` | `NeZero W`; no `3 ≤ d` needed | n/a (all `d`) |
| `g₀, E` | `0, 0` | none (any real); `BASelf` only | n/a |
| `m` | `i` | `Im m > 0`, `m = L^{-d} tr M^{(B)}` | `Im m = 1` |
| `W` matrix | `W = (1 − M⁺S)⁻¹ = (2/3)·I` | `W(1 − M⁺S) = 1` (`baW_mul`) | exact |
| D402 coefficient | `(W−1)_{xx} = −1/3 = (M⁺S⁺)_{xx}`, `S⁺_{xx} = +1/3` | `W − 1 = M⁺S W` (`ba_W_sub_one`) | printed vs corrected differ by `2/3` |
| t = 0 | `Ǧ = 0`, `S = 0`, `W = 1` | both sides vanish pathwise | n/a |
Smallness of `g` or of `‖M − m₀I‖`, `(Cλ)^{|a−b|}`: not used (C1/L5). Only `BASelf`, `baM_row_sq`, `baM_symm`, `baW_isUnit` enter.
The only sum identity used is `Σ_β S_{αβ} = t` (inside `baW_isUnit`, needs `3 ≤ L`).

### (ii) Proof route (confirms the ticket's route; replaces nothing)
1. **Basic expansion at `x`** with `P̃ := (X(true,y',x) − C(M_{y'x}))·P`, so `BAlwf P̃ = Ǧ_{y'x}·f` (`baWx_baPoly`) and, by the product rule for the two `HasDerivAt`'s (`BAExpand_bridge_hasDerivAt`, `lwWx_hasDerivAt_Gres`), `BAlwdf P̃ β α = −G_{y'β}G_{αx}·f + Ǧ_{y'x}·∂_{βα}f` (`t > 0`).
   `baLanlw_holds` at `(x,y)`: `𝔼[Ǧ_{xy}Ǧ_{y'x}f] = 𝔼[Σ M_{xα}S_{αβ}Ǧ_{ββ}G_{αy}Ǧ_{y'x}f + Σ M_{xα}S_{αβ}G_{βy}G_{y'β}G_{αx}f − Σ M_{xα}S_{αβ}G_{βy}Ǧ_{y'x}∂_{βα}f]`.
2. **Pathwise split** `G_{αx} = Ǧ_{αx} + M_{αx}`, `G_{βy}G_{y'β} = Ǧ_{βy}Ǧ_{y'β} + Ǧ_{βy}M_{y'β} + M_{βy}Ǧ_{y'β} + M_{βy}M_{y'β}`, with `Σ_α M_{xα}M_{αx}S_{αβ} = (M⁺S)_{xβ}`. With `v_x := 𝔼[Ǧ_{y'x}Ǧ_{xy}f]`:
   `v_x = Σ_β (M⁺S)_{xβ} v_β + r_x`, `r_x = Σ_β (M⁺S)_{xβ} 𝔼ζ_β + 𝔼B_x`, where `ζ_β = (MM + ǦM + MǦ)f` (sums 1-2 summand) and `B_x` is the summand of sum 3 at `w = x`.
3. **Solve** `(1 − M⁺S)v = r`, `v = W r` (`baW_mul`, as in `baLweight_holds`): `v_x = Σ_w W_{xw}r_w`. By `W·M⁺S = W − 1` (from `W(1 − M⁺S) = 1`), `Σ_w W_{xw}(M⁺S)_{wβ} = (W−1)_{xβ}`: **this is where D402 enters** (sums 1-2 carry `(W−1)_{xβ} = (M⁺S⁺)_{xβ}`, sum 3 carries `W_{xw} = (1+M⁺S⁺)_{xw}`). `ba_W_sub_one` is only the restatement `W − 1 = M⁺SW`.
4. **Integrability** of `Ǧ_{y'x}Ǧ_{xy}f`, `ζ_β`, `B_w` on `PF d L W 0` by `Tame` closure through `lwWxSec`, exactly as `baLweight_holds` (`BAExpandW.lean:354-439`, private helper `BAExpandW_integrable_PF` and local macro `baw_tame` must be re-copied). `t = 0`: both sides `0` pathwise, as in `baLweight_holds`.
Symmetry `M_{αx} = M_{xα}` is used only inside `baW_isUnit`; the system step uses `M⁺_{xα} = M_{xα}M_{αx}` by definition (`BAlwMp`).

**Band `LWGGExp` §1-§3 (`:74-463`): what transfers.** Does not transfer: `oe2x_defect_identity` / `oe2x_integral` (scalar `m`, `m³S⁺`, `S⁺(1−m²S) = S`, own Stein defect on `lwG`, `LWggExp` for the uncircled pair; BA has `M` non-scalar and `W`). Replaced by: `baLanlw_holds` plus the `W`-solve (no new Stein identity, no sequence-space integral). Transfers as pattern only: the `t = 0` case split and the `Tame`-closure macro (no `lwWx_integral` transport is needed: `baLanlw_holds` is already on `PF d L W 0`).
Merge: the cone of `RBM3D.Graph.BAExpandW` has 93 `RBM3D` modules, 10 under `RBM3D/Graph/`, none named `LWExpCert*` (script below). `BAExpandWOrd` not needed.
Note for 1b: in the probe the pins sit under `open RBM RBM.Gauss RBM.BA`; `BAExpandW.lean` opens `RBM RBM.Gauss RBM.Green`: add `RBM.BA` (or qualify `RBM.BA.BASelf`).

### (iii) One concrete nondegenerate instance (and numerical evidence)
Lean instance: `d=3, L=3, W=1` (27 sites), `g₀=0, E=0, m=i` (`BAExpandInst.baSelf_zero`, `BAExpand.lean:865`), `t=1/2`, `P=1` and `P` nonconstant (`X(true,a,a)`, i.e. `f = G_{aa}`), `x,y,y'` among `{0,1}`.
```
$ python3 inst.py   # (scratchpad T2409/inst.py; sha256 below) 27x27 instance data
self_m: m=L^-d tr M = 1j  Im m>0: True  t in [0,1): True  3<=L: True
Ward row sum_a |M_xa|^2 = 1.0  Gershgorin row sum of |Mp S| = 0.5  margin 1-t = 0.5
W_00 = 0.6666666666666666  (W-1)_00 = -0.33333333333333337  (M+ S+)_00 = -0.3333333333333333  S+_00 (printed coeff) = 0.3333333333333333
W-1 = M+ S W (ba_W_sub_one): True   W(1-M+S)=1: True
$ python3 gg_pf.py   # (annotations in parentheses are mine, not script output) (scratchpad T2409/gg_pf.py) exact-in-practice trapezoid quadrature of E[LHS]-E[RHS], H=g·Psi+sqrt(t)·diag(v), v_k iid N(0,1)
N=1 (E=.3,t=.5,g=0)        printed   max|E[LHS]-E[RHS]| over 1 index tuples = 4.794e-01
N=1 (E=.3,t=.5,g=0)        corrected max|E[LHS]-E[RHS]| over 1 index tuples = 7.473e-17
N=1 f=1 (P=1)              printed   max|E[LHS]-E[RHS]| over 1 index tuples = 7.776e-01
N=1 f=1 (P=1)              corrected max|E[LHS]-E[RHS]| over 1 index tuples = 1.415e-16
N=2 coupled (g=.35,t=.6)   printed   max|E[LHS]-E[RHS]| over 32 index tuples = 8.572e-01      (|M_01|=0.3489: nonscalar M, f=G_ab)
N=2 coupled (g=.35,t=.6)   corrected max|E[LHS]-E[RHS]| over 32 index tuples = 3.255e-16
N=2 coupled f=1 (P=1)      printed   max|E[LHS]-E[RHS]| over 8 index tuples = 7.606e-01
N=2 coupled f=1 (P=1)      corrected max|E[LHS]-E[RHS]| over 8 index tuples = 1.717e-16
N=27 Lean instance fill=0.0 printed   max|E[LHS]-E[RHS]| over 16 index tuples = 8.603e-01
N=27 Lean instance fill=0.0 corrected max|E[LHS]-E[RHS]| over 16 index tuples = 2.431e-11     (h=0.12 grid; other 25 coordinates fixed)
N=27 Lean instance fill=1.3 printed   max|E[LHS]-E[RHS]| over 16 index tuples = 8.603e-01      (same result with the other coordinates at 1.3:
N=27 Lean instance fill=1.3 corrected max|E[LHS]-E[RHS]| over 16 index tuples = 2.431e-11       the integrand does not depend on them)
$ shasum -a 256 gg_pf.py inst.py
3a66aaa22a77ee08593022b3fcd9a15883d258c4ca971bf0d6759982cac63d0e  gg_pf.py
f94e304a64b09e3c649cf5fda5b2de8c3ca081b4003b5f2abd88ac47e22f6971  inst.py
$ (cone) python3 - <<EOF ... transitive imports of RBM3D/Graph/BAExpandW.lean ... EOF
93 RBM3D modules in the cone of BAExpandW
LWExpCert in cone: []
```
Hypothesis check (all at once, nondegenerate): `BASelf 3 3 0 0 i` holds (`Im m = 1 > 0`, `m = i = 27⁻¹ tr M`), `0 ≤ 1/2 < 1`, `3 ≤ 3`, `N = 27 ≠ 0`, `S = I/2`, `W = 2I/3` (not collapsed), `Pm = −I/2`. No external hypothesis (`gaussIBP` discharged inside `baLanlw_holds`), so no limit computation is needed.

### (iv) Plan against the stop line 1,300 (`wc -l RBM3D/Graph/BAGGExp.lean`; estimate 450 / 650 / 1,000)
| part | lines |
|---|---|
| header, imports, pin copy (`ba_W_sub_one`, `GGGammaPin`, `BAGGGamma`) | ~90 |
| `baw_tame` macro, `BAGGExp_integrable_PF` (re-copy) | ~40 |
| derivative of `P̃` (product rule, evaluation) | ~80 |
| pathwise split (steps 1-2) | ~130 |
| integrability pieces | ~100 |
| `t = 0` case, solve `v = W r`, assembly (steps 3-4) | ~150 |
| `BAGGExpInst` (`baGGGamma_holds 3` at the instance, `P = 1`, nonconstant `P`) | ~60 |
| total | ~650 (stop line 1,300: slack ~650) |

### Verdicts
- Target 1 (copy `ba_W_sub_one`, `GGGammaPin`, `BAGGGamma`): PASS.
- Target 2 (`baGGGamma_holds : ∀ d, BAGGGamma d`): PASS (hypotheses satisfiable at the instance; corrected identity verified numerically, printed form fails: 0.48 to 0.86 vs 1e-16).
- Target 3 (C1 / L5: only `BASelf`, `baM_row_sq`, `baM_symm`, `baW_isUnit`): PASS.
- Target 4 (instances and numeric check): PASS (instance data above; numeric check is `gg_pf.py`).
- Target 5 (registry none; merge lane): PASS (no `LWExpCert*` in the cone).

## (b) Script output — Sun Oct 11 05:02:28 UTC 2026 (stage 1b, branch t/T2409, commit 88cc0fa)
```
$ wc -l RBM3D/Graph/BAGGExp.lean   # stop line 1,300 (CONTROL H134)
     533 RBM3D/Graph/BAGGExp.lean
$ lake build RBM3D.Graph.BAGGExp 2>&1 | tail -1
Build completed successfully (3782 jobs).
$ lake build 2>&1 | tail -1   # whole library incl. #assert_rbm_axioms; RBM3D.lean has the new import line
Build completed successfully (4216 jobs).
$ lake env lean ax.lean | python3 axgroup.py   # import RBM3D.Graph.BAGGExp; #print axioms of the 5 public declarations (prefix RBM.Graph. dropped)
baGGGamma_holds, ba_W_sub_one, BAGGGamma, BAGGGammaL, BAGGGammaR : [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BAGGExp.lean
0
$ lake env lean docs/tickets/checks/T2409-check.lean >/dev/null 2>&1; echo $?   # main worktree file, run on the branch
0
$ git diff --name-only main...t/T2409 | tr "
" " "
RBM3D.lean RBM3D/Graph/BAGGExp.lean 
$ python3 cone3.py   # transitive imports of RBM3D/Graph/BAGGExp.lean
94 RBM3D modules in the cone, 11 under Graph/; LWExpCert* in cone: []
$ python3 (extract the block `def BAGGGamma` and the line `theorem baGGGamma_holds` from RBM3D/Graph/BAGGExp.lean)   # target statements
def BAGGGamma (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y y' : Idx d L W),
      ∫ ω, BAGGGammaL d L W g0 E t m P x y y' ω ∂(PF d L W 0) = ∫ ω, BAGGGammaR d L W g0 E t m P x y y' ω ∂(PF d L W 0)
theorem baGGGamma_holds (d : ℕ) : BAGGGamma d
$ diff <(probe T2387Pins.lean:286-293,324-348 @fe433f2) <(BAGGExp.lean:50-57,59-83)   # pin copy
identical (ba_W_sub_one, GGGammaPin, BAGGGamma)
$ sed -n 487,492p RBM3D/Graph/BAGGExp.lean   # instance (I1); (I2)-(I6): five more examples, lines 495-527
example :
    ∫ ω, BAGGGammaL 3 3 1 0 0 (1 / 2) Complex.I (1 : MvPolynomial (Bool × Idx 3 3 1 × Idx 3 3 1) ℂ) 0 e0 e1 ω
        ∂(PF 3 3 1 0) =
      ∫ ω, BAGGGammaR 3 3 1 0 0 (1 / 2) Complex.I (1 : MvPolynomial (Bool × Idx 3 3 1 × Idx 3 3 1) ℂ) 0 e0 e1 ω
        ∂(PF 3 3 1 0) :=
  baGGGamma_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I baSelf_zero (by norm_num) (by norm_num) _ _ _ _
$ git grep -l -w -e BAGGGamma -e BAGGGammaL -e BAGGGammaR -e baGGGamma_holds -e ba_W_sub_one -e BAGGExpInst main -- RBM3D RBM3D.lean | wc -l   # name clash on main
0
$ python3 gg_pf.py > gg_pf.out; python3 cmp.py   # preflight script (sha256 3a66aaa2..., see (a)), rerun and compared with (a)
(a) rows: 12  rerun rows: 12  same (kind, #tuples, value) multiset: True
printed error range [0.479, 0.860]; corrected error range [7.5e-17, 2.4e-11]
```

Narrative (stage 1b). No port from RBM1D/RBM2D (no diff-stat); `BAGGExp_integrable_PF` re-copies the private `BAExpandW_integrable_PF` (`BAExpandW.lean:295-310`, main 1c25de0).
- Route of (a)(ii) followed, nothing replaced. The local macro `baw_tame` is not copied: a private predicate `BAGGExp_TL` ("tame through the slice at size 0", closed under `+ - *`, finite sums; atoms `G`, `Ǧ`, `f`, `∂f`) with macro `bagg_tl` gives every integrability.
- `BAGGExp_Pt P y' x := (X(true,y',x) - C(M_{y'x})) P`; `BAGGExp_f_mul` (value `Ǧ_{y'x} f`), `BAGGExp_df_mul` (derivative `-G_{y'β}G_{αx} f + Ǧ_{y'x} ∂_{βα} f`, `0 < t`; product rule of `lwWx_hasDerivAt_Gres` and `BAExpand_bridge_hasDerivAt`).
- `BAGGExp_pathwise`: `BAlanlwR(P̃) x y = Σ_β (M⁺S)_{xβ} Ǧ_{y'β}Ǧ_{βy} f + Σ_β (M⁺S)_{xβ} ζ_β + B_x` (uses only `G = Ǧ + M`); `BAGGExp_R_eq`: the pin's right side is `Σ_β (W-1)_{xβ} ζ_β + Σ_w W_{xw} B_w`.
- `baGGGamma_holds`, `t > 0`: `baLanlw_holds` at `(x, y)` with `P̃` gives `v - (M⁺S) v = r` for `v_a = 𝔼[Ǧ_{y'a}Ǧ_{ay} f]`; `baW_mul` gives `v = W r`; D402 enters at `hWP : W (M⁺S) = W - 1`, turning `Σ_w W_{xw} Σ_β (M⁺S)_{wβ} 𝔼ζ_β` into `Σ_β (W-1)_{xβ} 𝔼ζ_β`. The copied `ba_W_sub_one` (`W - 1 = M⁺SW`) is not used in this proof, only in instance (I6). `t = 0`: `Ǧ = 0`, `S = 0`, `W = 1`, both sides are `0`.
- C1/L5: hypotheses used are `BASelf`, `3 ≤ L`, `0 ≤ t < 1` (through `baLanlw_holds`, `baW_mul`); no smallness of `g` or `‖M - m₀ I‖`, no `3 ≤ d`.
- Instances (all `d = 3`, `L = 3`, `g₀ = 0`, `E = 0`, `m = i` by `baSelf_zero`, no hypothesis left open): (I1) `P = 1`; (I2) `f = G_{e₀0}`; (I3) `f = G_{00} Ḡ_{e₀e₀}`, sites permuted; (I4) `W = 2` (216 sites); (I5) `t = 0` (boundary, not a nondegeneracy witness); (I6) `ba_W_sub_one`. (I1)-(I4): `t = 1/2` and three distinct sites `x, y, y'`.

## (c) Verified Mathlib names (module of the declaration read from the environment by a `#where` script, scratch T2409/where.lean)
- Mathlib.MeasureTheory.Integral.Bochner.Basic: integral_add, integral_finsetSum, integral_const_mul, integral_congr_ae
- Mathlib.MeasureTheory.Function.L1Space.Integrable: integrable_finsetSum, Integrable.const_mul, Integrable.add, integrable_map_measure
- Mathlib.Algebra.BigOperators.Group.Finset.{Sigma,Defs,Basic} and Ring.Finset: Finset.sum_comm, sum_sub_distrib, sum_add_distrib, sum_congr, mul_sum, sum_mul
- Mathlib.Analysis.Calculus.Deriv.{Mul,Add,Basic}: HasDerivAt.mul, HasDerivAt.sub_const, HasDerivAt.deriv
- Mathlib.Algebra.MvPolynomial.Eval: MvPolynomial.eval_mul; Mathlib.Data.Matrix.Mul: Matrix.mulVec_mulVec, sub_mulVec, one_mulVec, mul_apply; Mathlib.Algebra.GroupWithZero.Units.Basic: Ring.mul_inverse_cancel. Absent: `Matrix.mul_vec_mul_vec` (the name is `Matrix.mulVec_mulVec`).

## (d) Open issues and paper-delta candidates
- T2409a (D402 status): `(B.20)` as printed (`B:393-405`) has `S⁺_{xβ}` in sums 1-2; Lean proves the corrected `(W-1)_{xβ} = (M⁺S⁺)_{xβ}` (`baGGGamma_holds`); the numerics in (b) give printed 0.479-0.860, corrected at most 2.4e-11. Propose recording D402 as proved in Lean.
- T2409b: Lean's `f` is a resolvent polynomial `P` evaluated at `(G, G*)` (`BAlwf`), the paper's is "a differentiable function of `G`"; the paper's `=_E` is `∫ ... ∂(PF d L W 0)` with explicit `BASelf`, `3 ≤ L`, `0 ≤ t < 1` (the same shape as `BAlanlw`, `BAlweight`).
- Observation on the ticket: "the cone of `Graph/BAExpandW` is 2 modules"; the script gives 94 `RBM3D` modules (11 under `Graph/`) for `BAGGExp` (93 and 10 for `BAExpandW`, in (a)). The claim that matters (no `LWExpCert*`) holds.
- Merge lane: `RBM3D.lean` carries `import RBM3D.Graph.BAGGExp` after `import RBM3D.Chain.NewKLKGen`, so the hub's rule (A)(4) adds nothing; the full `lake build` passes on the branch. No open issue for the targets (1-5 delivered).
