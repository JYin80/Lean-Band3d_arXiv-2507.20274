Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 05:37:19 UTC 2026

Target 1: `theorem unNormBandRow : UNNormBandRow` (`Pins.lean:834`): for all `d ≥ 3`, `sz` admissible, there is `CV₀ ≥ 0` with: for all `D > 0`, eventually in `n`, `seqP sz {ω | ∃ i, N^CV₀ < |λ_i(seqXmat sz n ω)|} ≤ ofReal (N^(-D))`, `N = sz.size n` (`UNNormBound`, `Pins.lean:477-479`).
Route (the shape of the T2371 branch commit ba6da7e, `Main/BUnivHolds.lean:221-366` (146 lines), which Amend 1 removed; read as a lead only): coordinates of `seqP` are `N(0, v)`, `v ≤ 1`; threshold `t = N`; two-sided Gaussian tail; union over the `2N²` real coordinates of size `n`; on the good event every entry has `‖H_xy‖ ≤ 2t`; `|λ_i| ≤ #ι · max‖H_xy‖` (ℓ^∞ operator norm via `H ψ = λ ψ`); `measure_mono`.

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| `CV₀` | 3 | need `0 ≤ CV₀` and `N · 2t = 2N² ≤ N^CV₀` | `2N² ≤ N³` iff `N ≥ 2`; at `N = 2^21` ratio `N³/(2N²) = 2^20`. (`CV₀ = 2` would need `2N² ≤ N²`, false; `CV₀ = 1` of the `Pins.lean:470-475` docstring would need `t ≤ 1/2`, then the tail `2e^{-1/8}` is not small. The statement only asks `∃ CV₀ ≥ 0`.) |
| threshold `t` on `|ω_c|` | `t = N` | entries `≤ 2t` (two coordinates per off-diagonal entry); tail must beat `N^{-(D)}` after the union | tail exponent `t²/2 = N²/2` against needed `(D+2) ln N` |
| variance bound | `gvarF ≤ 1` for every `c` | `gvarF` is `svarF` (diag) or `svarF/2`; `svarF = W^{-d} · SBR ≤ 1` since `sbKernelR ≥ 0` and `∑ sbKernelR = 1` (`sum_sbKernelR`, needs `3 ≤ L`, from `sz.three_le_L`) and `W ≥ 1`; holds for every real coupling `sz.lam n` | at sz0, n = 0: diag `svar = 3.0473e-5` (`≤ W^{-d} = 3.0518e-5 ≪ 1`) |
| sub-Gaussian proxy | `1` (`HasSubgaussianMGF (ω ↦ ω c) 1 (seqP sz)`, via `seqP_map_eval`, `mgf_id_gaussianReal`) | `v ≤ 1` gives `exp(v t²/2) ≤ exp(t²/2)`; avoids `v > 0` (a variance `v = 0` costs nothing) | none needed |
| tail per coordinate | `P(N ≤ ω_c) + P(N ≤ -ω_c) ≤ 2 e^{-N²/2}` | `measure_ge_le` of the proxy-1 sub-Gaussian | exact |
| coordinates in the union | `#CoordF = 2N²` (`Idx × Idx × Bool`, `card_Idx`: `#Idx = N`) | only size-`n` coordinates enter (the event involves `seqXmat sz n` only); polynomial in `N` | `N = 2^21`: `2N² = 8796093022208` |
| union total | `4N² e^{-N²/2} ≤ N^{-D}` | eventual in `n` | route: `N^{D+2} e^{-N/2} ≤ 1/4` (from `N²/2 ≥ N/2`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`); at `D = 1` first true at `N = 22`, at `D = 10` at `N = 118`; `ln` slack at `N = 2^21`, `D = 1`: 2.199e12 nats |
| `∀ᶠ n` conditions | (1) `N^{D+2}e^{-N/2} ≤ 1/4`; (2) `N ≥ 2` | both are eventual in `N`, so eventual in `n` by `Admissible`'s `SizeTendsto` (`hA.2.2.1`) | sz0, n = 0: `N = 2097152 ≥ 118` |
| used from `Admissible 𝔠 𝔡` | only `SizeTendsto`; `𝔠, 𝔡`, `Bandwidth`, `WO`, `3 ≤ d` are not needed | | |
| external inputs | none | | |

### (ii) Concrete instance (check script `scratchpad/T2372/check.py`)
Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260`), `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`, `D = 1`, `(𝔠,𝔡) = (1/6,1/10)` (`sz0_admissible`, `Sizes.lean:331`). Limit computation for `SizeTendsto`: `size n = (W L)^3 = (128 (n+1)^6)^3 = 2^21 (n+1)^18 → ∞` (printed for `n = 0..3`; `sz0_tendsto` is merged, `Sizes.lean:300`). Deterministic instance: `Fin 2` matrix `[[1, 1+i],[1-i, -1]]`, Hermitian, nondiagonal, eigenvalues `±√3`.
```
$ cd scratchpad/T2372 && python3 -I check.py
L,W,lam,N = 4 32 1/64 2097152 N==2097152: True 3<=L: True 3<=d: True
svar_diag = 3.047294002925402e-05 <= W^-d = 3.0517578125e-05 <= 1: True
coordinates 2N^2 = 8796093022208
entry bound 2N = 4194304  eig bound N*2N = 8796093022208  CV0=3: N^3 = 9223372036854775808  2N^2<=N^3: True  N>=2: True
D=1: ln(4N^2 e^(-N^2/2)) = -2.199023e+12  <=  ln N^-D = -14.5561  slack(nats) = 2.199023e+12  ok=True
      ln(N^(D+2) e^(-N/2)) = -1.048532e+06 <= ln(1/4) = -1.3863: True
D=10: ln(4N^2 e^(-N^2/2)) = -2.199023e+12  <=  ln N^-D = -145.5609  slack(nats) = 2.199023e+12  ok=True
      ln(N^(D+2) e^(-N/2)) = -1.048401e+06 <= ln(1/4) = -1.3863: True
D=1: first N with N^(D+2)e^(-N/2)<=1/4 is 22; (decreasing for N>2(D+2)=6); sz0.size 0 = 2097152 >= 22: True
      exact condition 4N^2e^(-N^2/2)<=N^-D holds first at N=4
D=10: first N with N^(D+2)e^(-N/2)<=1/4 is 118; (decreasing for N>2(D+2)=24); sz0.size 0 = 2097152 >= 118: True
      exact condition 4N^2e^(-N^2/2)<=N^-D holds first at N=8
H = [[(1+0j), (1+1j)], [(1-1j), (-1+0j)]]  trace, det = 0.0 -3.0  eigenvalues = [-1.7320508075688772, 1.7320508075688772]  B = max|H_xy| = 1.4142135623730951  card*B = 2.8284271247461903
|lambda_i| <= card*B for all i: True  Frobenius sum lambda^2 = 5.999999999999999 = sum|H_xy|^2 = 6.000000000000001
$ python3 -I -c "for n in range(4): L,W=4*(n+1),(2*(n+1))**5; N=(W*L)**3; print(n,N,N==2**21*(n+1)**18)"
0 2097152 True
1 549755813888 True
2 812479653347328 True
3 144115188075855872 True
```
All hypotheses hold at once: `3 ≤ d`, `3 ≤ L`, `W ≥ 1`, `N ≥ 118`, `D = 1 > 0`, a nonempty index (`#Idx = N = 2^21`), `2N² ≤ N³`; the Fin 2 matrix has `|λ_i| ≤ 2 · max‖H_xy‖ = 2.828` with `max‖H_xy‖ = √2` (`Σ λ² = Σ |H_xy|² = 6`).

### (iii) Reuse check
`grep -rln "seqXmat" RBM3D` lists Green/, Path/, Universality/ files; no public entry bound or operator-norm bound of `seqXmat` under `seqP` exists on `main`: the eigenvalue-bound lemmas found are all private (`Step1RegularityGUE_eigenvalue_le`, `Step1RegularityGUE.lean:568`, for `gueP`, entries `≤ 1`, bound `#ι`) or about other statements (`un_eigenvalues_abs_le_convex`, `eigenvalues₀_abs_sub_le`; `EigenMeasurable.opNorm_sq_le_frob` (`EigenMeasurable.lean:39`) is private). Reusable by copy with stem `NormBand_`: `Markov_norm_Xentry_le` (`Markov.lean:661`, `≤ 2t`), the `gvarF ≤ 1` proof (`AzumaProxyN2.lean:227`), the sub-Gaussian setup (`Step1RegularityGUE.lean:167`, `CltGood.lean:225`), and the ℓ^∞ route of `Step1RegularityGUE_eigenvalue_le` generalised to a bound `B` (via `Matrix.linfty_opNorm_mulVec`, `Mathlib/Analysis/Matrix/Normed.lean:364`). `gue_highProb_incr_le` and `highProbAt_iInter` are not needed: a direct union over `2N²` coordinates at one size (`measure_iUnion_fintype_le`) suffices (no `HighProbAt` form is required by the target).

### (iv) Plan against the stop line (500)
Existing worked proof of this exact route: 146 lines (`wc -l` of `BUnivHolds.lean` lines 221-366 at ba6da7e); plus the file header/imports and two instances. The stop line has room.

### Verdicts
- Target 1 (`unNormBandRow`): PASS (every hypothesis holds at the instance; the exponents close with slack above; no external input).
- Target 2 (instances): PASS (Fin 2 matrix and the threshold arithmetic at sz0, n = 0, N = 2097152, D = 1 are numerically checked above).
- Target 3 (registry): PASS (`Test/Axioms.lean:196` is the line `UNNormBandRow`; `UNNormBound` stays at `:195`; `:182-183` comment is T2371's).

## (b) Script output — Sat Oct 10 05:49:28 UTC 2026

Branch `t/T2372` (worktree `RBM3D-wt/T2372`), base f184210 (main has since advanced to c0a7747, T2371):
```
$ git log --format="%h %s" f184210..HEAD; git diff --name-only f184210..HEAD; wc -l RBM3D/Universality/NormBand.lean
7df528d T2372: instances of the deterministic steps and of unNormBandRow; registry: drop owed UNNormBandRow
1741ead T2372: unNormBandRow (UN-10a) main proof
RBM3D/Test/Axioms.lean
RBM3D/Universality/NormBand.lean
     299 RBM3D/Universality/NormBand.lean
```

Build:
```
Sat Oct 10 05:48:15 UTC 2026
$ lake build RBM3D.Universality.NormBand 2>&1 | grep -v "^trace\|^$" | tail -5
warning: RBM3D/Defs/Tail.lean:170:100: This line exceeds the 100 character limit, please shorten it!
Note: This linter can be disabled with `set_option linter.style.longLine false`
warning: RBM3D/Defs/Tail.lean:171:100: This line exceeds the 100 character limit, please shorten it!
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3333 jobs).
```

Axioms (scratch file `axioms.lean` = `import RBM3D.Universality.NormBand`, six `#print axioms` lines for the public declarations, then `example : RBM.Univ.UNNormBandRow := RBM.Univ.unNormBandRow`):
```
$ lake env lean axioms.lean   (exit 0, 05:47:46 UTC)
'RBM.Univ.unNormBandRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.NormBandInst.H2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.NormBandInst.H2_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.NormBandInst.H2_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.NormBandInst.Nsz_sz0_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.NormBandInst.exp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statement (`Pins.lean` pins; the theorem line of `NormBand.lean`):
```
$ grep -n "^def UNNormBandRow" -A3 RBM3D/Universality/Pins.lean; grep -n "^def UNNormBound" -A3 RBM3D/Universality/Pins.lean; grep -n "^theorem unNormBandRow" RBM3D/Universality/NormBand.lean
834:def UNNormBandRow : Prop :=
835-  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
836-    ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz (UNModel.band sz) CV₀
837-
477:def UNNormBound (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ) : Prop :=
478-  ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
479-    M.μ {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
480-
173:theorem unNormBandRow : UNNormBandRow := by
```

Compiled nonempty instances (`NormBand.lean:254-265, 278-288, 290-295`, by `sed -n`; helpers `H2`, `H2_isHermitian`, `H2_entry_le`, `Nsz_sz0_zero`, `exp_ge` are above them; all compiled in the build above):
```lean
/-- The deterministic step (`NormBand_eig_le`) at `H2`: the matrix is nondiagonal (`H2 0 1 ≠ 0`),
every entry has modulus `≤ 3/2` (the actual maximum is `√2`), and `|λ_i| ≤ #ι · B = 2 · 3/2 = 3`
for both eigenvalues (they are `±√3`). -/
example : H2 0 1 ≠ 0 ∧ ∀ i : Fin 2, |H2_isHermitian.eigenvalues i| ≤ 3 := by
  refine ⟨?_, fun i => ?_⟩
  · have h : H2 0 1 = 1 + Complex.I := rfl
    rw [h]
    intro hz
    have := congrArg Complex.im hz
    simp at this
  have h := NormBand_eig_le H2_isHermitian H2_entry_le i
  simpa using h.trans_eq (by norm_num)
...
/-- The threshold arithmetic of the union bound (`NormBand_tail_arith`) at `sz0`, `n = 0`,
`N = 2097152`, `D = 1`: both hypotheses (`N ≥ 1`, `N^{D+2} e^{-N/2} ≤ 1/4`) are discharged, and
`4 N² e^{-N²/2} ≤ N^{-1}`. -/
example : 4 * Nsz sz0 0 ^ 2 * Real.exp (-(Nsz sz0 0 ^ 2 / 2)) ≤ Nsz sz0 0 ^ (-(1 : ℝ)) := by
  rw [Nsz_sz0_zero]
  refine NormBand_tail_arith 1 _ (by norm_num) ?_
  rw [show ((1 : ℝ) + 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show (-(1 / 2) * (2097152 : ℝ)) = -1048576 by norm_num, Real.exp_neg,
    ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc (2097152 : ℝ) ^ 3 ≤ 1 / 4 * 131073 ^ 8 := by norm_num
    _ ≤ 1 / 4 * Real.exp 1048576 := by gcongr; exact exp_ge
...
/-- **The target at concrete data**: `unNormBandRow` at `d = 3`, `sz0` (`N = 2097152` at `n = 0`),
`(𝔠, 𝔡) = (1/6, 1/10)` (`sz0_admissible`, every deterministic hypothesis discharged). -/
example : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀ :=
  unNormBandRow 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible

example : UNNormBandRow := unNormBandRow
```

Name clashes and hygiene:
```
$ git grep -n -E "unNormBandRow|NormBand_|NormBandInst|Nsz_sz0_zero" main -- RBM3D RBM3D.lean
main:RBM3D/Main/BUnivHolds.lean:26:  `unNormBandRow`);
$ git grep -n -E "theorem exp_ge|def H2( |$)" main -- RBM3D
$ grep -c 'sorry\|admit\|native_decide' RBM3D/Universality/NormBand.lean; grep -c '^axiom' RBM3D/Universality/NormBand.lean
0 0
```

Registry (target 3), diff and pre-check:
```
$ git diff f184210..HEAD -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-140
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNNormBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
$ cat precheck.lean   (temporary, uncommitted, in scratchpad/T2372/)
import RBM3D
import RBM3D.Universality.NormBand

#assert_rbm_axioms
$ lake build RBM3D.Test.Axioms   (05:46:28 UTC) -> Build completed successfully (2 jobs)
$ lake env lean precheck.lean > precheck.out   (UTC start, end; exit code appended by the script)
Sat Oct 10 05:46:36 UTC 2026 Sat Oct 10 05:47:35 UTC 2026 
axiom audit: 10835 theorems, 3187 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
...
$ grep -c UNNormBandRow precheck.out
0
non-vacuity certificates: 0 of 127 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
exit=0
```

Ports (RBM2D read only; HEAD 9e0f275, last commit of both files 81fca44):
```
$ git -C ../RBM2D --no-optional-locks diff --stat 81fca44 HEAD -- RBM2D/Universality/Step1RegularityB.lean RBM2D/Universality/Step1RegularityA.lean
(empty: no change since 81fca44)
$ python3 -I -c "import math; print(math.erfc(0.5/math.sqrt(2)))"   # P(|g|>1/2), g ~ N(0,1)
0.6170750774519739
```

Simulated merge build (the hub's step (A)5): one line `import RBM3D.Universality.NormBand` added after the last import of `RBM3D.lean`, uncommitted, then removed again (`git status --short` empty afterwards):
```
$ lake build   (UTC start, end; then tail of the output)
Sat Oct 10 05:50:03 UTC 2026 Sat Oct 10 05:51:01 UTC 2026 
non-vacuity certificates: 0 of 127 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4182 jobs).
exit=0
```

### Narrative (script output above is the evidence)
- `RBM3D/Universality/NormBand.lean` (299 lines, stop line 500): `theorem unNormBandRow : UNNormBandRow` with `CV₀ = 3`; every other
  declaration before the instances is `private` with the stem `NormBand_`; the instance helpers sit in `namespace NormBandInst`.
- Route, as in the preflight's lead (T2371 commit `ba6da7e`, `Main/BUnivHolds.lean:221-366`, read with `git show`; a lead, re-checked by the build):
  coordinates of `seqP` are `N(0, v)`, `v ≤ 1` (`NormBand_gvar_le`, `sum_sbKernelR`, `sz.three_le_L`); sub-Gaussian proxy `1`; threshold `N`;
  union over the `2N²` real coordinates of size `n` (`measure_iUnion_fintype_le`); `4N²e^{-N²/2} ≤ N^{-D}` eventually (`NormBand_tail_arith`,
  `NormBand_tail_eventually`); entries `≤ 2N` (`NormBand_Xentry_le`); `|λ_i| ≤ #ι · 2N = N · 2N = 2N² ≤ N³` for `N ≥ 2`, `#ι = N` (`NormBand_eig_le`, `Sizes.card_Idx`); `measure_mono`.
- From `Admissible 𝔠 𝔡` only `SizeTendsto` (`hA.2.2.1`) is used; `3 ≤ d`, `Bandwidth`, `WO` are not used by the proof (the statement is the pin's, unchanged, with its hypotheses).
- Not used from the ticket's template list: `gue_highProb_incr_le`, `highProbAt_iInter` (a direct union at one size suffices, as the preflight (iii) found).
- Instances (target 2): `Fin 2` matrix `[[1, 1+i],[1-i, -1]]` (nondiagonal, Hermitian) through `NormBand_eig_le`; the threshold arithmetic of
  `NormBand_tail_arith` at `sz0`, `n = 0`, `N = 2097152`, `D = 1` (`Nsz sz0 0 = 2097152`; `N^{3} e^{-N/2} ≤ 1/4` via `e^{2^20} ≥ 131073^8`);
  and the theorem itself at `sz0`, `d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)` with `sz0_admissible` (all deterministic hypotheses discharged, nothing left as a hypothesis),
  plus `example : UNNormBandRow := unNormBandRow`.
- Registry (target 3): the one `owedProps` line `` `RBM.Univ.UNNormBandRow `` deleted; `UNNormBound` stays. The pre-check names no unregistered premise (exit 0, `grep -c UNNormBandRow` = 0 in its output).
- `git diff --name-only f184210..HEAD` lists exactly the two sole writable files. The branch is based on f184210; `main` is now c0a7747 (T2371 merged), which edited
  `Test/Axioms.lean` near this line (deleted its neighbours `UNTrLocalBandRow`, `UNDensBandRow`); the hub re-applies the one-line deletion against that `main` (ticket sibling scan, H23 (b)).
- Section (a) is unchanged; no preflight correction was needed (no `(a′)`).

## (c) Verified Mathlib names (all resolve in the build above; locations by `grep` in `.lake/packages/mathlib/Mathlib`)
- `HasSubgaussianMGF.id_map_iff` (`Probability/Moments/SubGaussian.lean:296`), `HasSubgaussianMGF.measure_ge_le`, `HasSubgaussianMGF.neg` (resolve by dot notation)
- `ProbabilityTheory.mgf_id_gaussianReal` (`Probability/Distributions/Gaussian/Real.lean:505`), `integrable_exp_mul_gaussianReal` (`:514`)
- `Matrix.linfty_opNorm_mulVec` (`Analysis/Matrix/Normed.lean:364`), `Matrix.linfty_opNorm_def` (`:284`)
- `Matrix.IsHermitian.mulVec_eigenvectorBasis` (`Analysis/Matrix/Spectrum.lean:75`), `IsHermitian.eigenvectorBasis.norm_eq_one` (resolves)
- `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` (`Analysis/SpecialFunctions/Pow/Asymptotics.lean:143`)
- `MeasureTheory.measure_iUnion_fintype_le` (`MeasureTheory/OuterMeasure/Basic.lean:84`), `measureReal_union_le` (resolves), `ENNReal.le_ofReal_iff_toReal_le` (`Basic/ENNReal/Real.lean:278`)
- `Real.add_one_le_exp` (`Analysis/Complex/Exponential.lean:632`), `Real.exp_nat_mul`, `pow_le_pow_left₀` (`Algebra/Order/GroupWithZero/Basic.lean:514`), `Complex.sq_norm`, `Complex.normSq_apply` (resolve)
- Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- **T2372a (doc fix, not a statement change).** The docstring of `UNNormBandRow` (`Pins.lean:830-833`) and of `UNNormBound` (`Pins.lean:470-475`) say "`CV₀ = 1` from the Gaussian entry tails
  `|h_xy| ≤ 1` ... `|λ| ≤ N`", derived from `S_xy ≤ 1`. From `S_xy ≤ 1` alone `|h_xy| ≤ 1` w.h.p. is false (a variance-1 real Gaussian has `P(|g| > 1/2) = 0.617`, script output above), and this proof
  uses threshold `N` and `CV₀ = 3`. The pin is `∃ CV₀ ≥ 0`, so the statement is unaffected. Proposed docstring: "proved with `CV₀ = 3` (`NormBand.lean`)".
  A smaller `CV₀` is not attempted (the pin asks only `∃ CV₀ ≥ 0`).
- No Lean/paper statement difference: the row is the pin `UNNormBandRow` (merged, unchanged); the paper's `(bandcw0)` (`1_2:295-296`) and `(eq:variancematrix)` (`1_2:303-304`, read in `paper/tex/1_2_Intro_model_result.tex`) give Gaussian entries with `S_xy = W^{-d} S^{(B)}_{ab}`.
- Consumers: `UNNormBandRow` remains a hypothesis of `bUniv_holds` on `main` (`Main/BUnivHolds.lean:26`, T2371 docstring says "producer T2372"); passing `unNormBandRow` is a separate (consumer) edit, not in this ticket's files.
