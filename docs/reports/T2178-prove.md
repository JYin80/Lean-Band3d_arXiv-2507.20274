Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 06:02:42 UTC 2026

Source: RBM2D `c9a24cf`, `RBM2D/Universality/PoissonSmoothing.lean` (`poissonSmooth_error` :975, helper lemmas :88-:886) and `InjSum.lean` (:28, :31).
Target (mathematics): for `O ∈ C_c^∞(ℝ^k)` (`InjSum_IsTestFun O := ContDiff ℝ ⊤ O ∧ HasCompactSupport O`) there is `C ≥ 0` with, for all `0 < ε ≤ 1` and `x ∈ ℝ^k`,
`|O x − (O*P_ε)(x)| ≤ C ε ∏_j (1+x_j²)⁻¹`, `P_ε(u)=ε/(π(u²+ε²))`, `(O*P_ε)(x)=∫ O(y) ∏_j P_ε(x_j−y_j) dy`. The only hypothesis is `hO` (no `d`, no `N`, no spectral parameter).
`InjSum_stieltjes`, `stieltjes_eta_mul_im_mono` (`0<η≤η̃ ⇒ η Im m(E+iη) ≤ η̃ Im m(E+iη̃)`) are definitions/finite-matrix identities with no exponents.

### (i) Exponent table (constants read from the proof of `poissonSmooth_error`, source lines :630-:975)

Notation: `M0 = sup|O|`, `M2` = a Lipschitz constant of `fderiv O` (the proof takes `M2 ≥ sup‖D²O‖`), `R ≥ 1` with `tsupport O ⊆ [−R,R]^k`.

| constant | value in the proof | constraint it must satisfy | slack |
|---|---|---|---|
| `C1` (uniform `O(ε)` bound, all x) | `k(2·M2+4·M0)/π` | `|O x − O*P_ε(x)| ≤ C1 ε` (near part `M2·k·2ε/π` by Taylor + oddness; far part `4M0 k ε/π`) | none claimed (proof constant) |
| `D` (box mass, all `t`, `ε ≤ 1`) | `1+4R²+8R(1+(4R²)⁻¹)/π` | `∫_{[−R,R]} P_ε(t−y)dy ≤ D(1+t²)⁻¹` | numeric below at `ε=1,R=2`: `D=22.41`, actual mass·(1+t²)/D ≤ 0.094 at the tested `t` |
| `Dfar` (far mass, `|t|>2R`) | `8R(1+(4R²)⁻¹)/π` | `∫_{[−R,R]} P_ε(t−y)dy ≤ Dfar·ε(1+t²)⁻¹` | `≥ 3.0×` at the tested `t` (table (ii)) |
| `C2` (escaping bound, some `|x_j|>2R`) | `M0·Dfar·D^{k−1}` | `|O x − O*P_ε(x)| ≤ C2 ε ∏(1+x_j²)⁻¹` (`O x=0` there) | none claimed |
| final `C` | `max(C1(1+4R²)^k, C2)` | box case `|x_j| ≤ 2R`: `∏(1+x_j²)⁻¹ ≥ (1+4R²)^{−k}` | exact (`(1+x_j²) ≤ 1+4R²`) |
| range of `ε` | `0<ε≤1` | used in `D`; `ε≤1` is the range of the source statement | — |
| decay exponent | `(1+x_j²)⁻¹`, i.e. `|x|⁻²` per coordinate | the Cauchy kernel has infinite 2nd moment, so the proof gives `O(ε)` (not `ε²`); the decay `x⁻²` per coordinate comes from the far box-mass bound `Dfar` | sharp in `ε` (see error at `x=0`: 4.3e-4 ≈ 0.43 ε) |
| dimension | none: `k` only enters as `(1+4R²)^k`, `D^{k−1}`, factor `k` in C1 | all `Fin k → ℝ`; no `d`, `L`, `W`, `N` | the file is dimension-free (class a) |

Rows the ticket asks for: the error constant of `poissonSmooth_error` in terms of the test function's derivatives and the scale `ε` (= the ticket's `η`) is
`C = max( k(2M2+4M0)(1+4R²)^k/π , M0·(8R(1+(4R²)⁻¹)/π)·D^{k−1} )` and the error is `≤ C·ε·∏(1+x_j²)⁻¹`, linear in `ε`; `M2 = sup‖D²O‖`, `M0 = sup|O|`, `R` = support radius (sup norm).
For the theorem as stated `C` is existential (depends on `O` only); the Lean statement does not expose the constants.

### (ii) One concrete nondegenerate instance

Data: `k = 1`, `ε = 10⁻³` (the ticket's `η = 1/1000`), `O(x) = smoothTransition(2−|x|)` (`=1` on `|x|≤1`, `=0` on `|x|≥2`, `C^∞`, `tsupport = [−2,2]`, so `R = 2`, `M0 = 1`); `hO` holds (smooth, compact support).
(Lean's `UNInst.bump` is a `ContDiffBump` with `rIn=1, rOut=2`, whose profile is Mathlib's; the theorem uses only `ContDiff ∧ HasCompactSupport`, so the explicit profile here is a model of the same instance; the numbers are model numbers, not Lean values.)
Script (`mpmath` 1.4.1, `scipy` 1.13.1; `M2` by 2nd derivative on a 2001-point grid of `[1,2]`, the only place `O''≠0`; smoothed value by `quad` split at `−2,−1,0,1,2,x`; error scanned on 241 grid points of `[−6,6]` plus `x ∈ {0.999,1,1.001,1.5,2,2.001,2.002,2.01,2.1,3,10,30,100}`):

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2178/pre.py
M0=1.0000 M2=9.8410 C1=7.5382 C1*(1+4R^2)^k=128.1496 C2=5.4113 C=128.1496
eps=0.001  max_x |O-O*P|(1+x^2)/eps = 6.2154 at x=1.800 ; proof constant C=128.1496 ; ratio=0.0485
  x=  0.0 err=4.296e-04 bound=C*eps/(1+x^2)=1.281e-01
  x=  1.5 err=1.064e-04 bound=C*eps/(1+x^2)=3.943e-02
  x=  2.0 err=6.382e-04 bound=C*eps/(1+x^2)=2.563e-02
  x=  3.0 err=1.440e-04 bound=C*eps/(1+x^2)=1.281e-02
  x= 10.0 err=9.777e-06 bound=C*eps/(1+x^2)=1.269e-03
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2178/mass.py
Dfar=5.4113 D=22.4113
far t=4.01: mass=1.054e-04  bound Dfar*eps/(1+t^2)=3.168e-04
far t=5: mass=6.063e-05  bound Dfar*eps/(1+t^2)=2.081e-04
far t=10: mass=1.326e-05  bound Dfar*eps/(1+t^2)=5.358e-05
far t=100: mass=1.274e-07  bound Dfar*eps/(1+t^2)=5.411e-07
all t=0 eps=1: mass=7.048e-01  bound D/(1+t^2)=2.241e+01
all t=1 eps=1: mass=6.476e-01  bound D/(1+t^2)=1.121e+01
all t=2 eps=1: mass=4.220e-01  bound D/(1+t^2)=4.482e+00
all t=3 eps=1: mass=1.872e-01  bound D/(1+t^2)=2.241e+00
all t=4 eps=1: mass=9.502e-02  bound D/(1+t^2)=1.318e+00
all t=10 eps=1: mass=1.312e-02  bound D/(1+t^2)=2.219e-01
```

Reading: with `R=2, k=1`: `C1=7.54`, `C=max(128.15, 5.41)=128.15`; the observed worst `(1+x²)|O−O*P_ε|/ε = 6.22` (at `x=1.8`), so the bound holds with slack factor `128.15/6.22 = 20.6` (ratio printed 0.0485). `Dfar` and `D` mass bounds hold at all tested `t` (far: factor ≥ 3.0; `ε=1`: factor ≥ 10).
All hypotheses hold at once: `k=1 ≥ 1`, `0 < 10⁻³ ≤ 1`, `R=2 ≥ 1`, `O` smooth with compact support, `O(0)=1≠0` (nondegenerate). No external hypothesis (the statement has none), so no limit computation is needed.
For the Stieltjes endpoints the instance is any finite Hermitian matrix, e.g. `diag(1,2,3)`, `E=0`, `0 < η=1/10 ≤ η̃=1` (the RBM2D compiled instances at `InjSum.lean:570-581`); the inequality is the monotonicity of `η ↦ η²/((λ−E)²+η²)` in `η`, termwise.

## Verdict
- `poissonSmooth_error`: PASS (hypothesis set nonempty, constants close with the slack above; statement is dimension-free, no `d=2` dependence beyond tokens).
- `InjSum_IsTestFun`, `InjSum_stieltjes`: PASS (definitions; instance above).
- Note for stage 1b (dependency, not a mathematical obstruction): RBM2D `InjSum.lean:33,55` uses `green` and `green_eq_spectral` (RBM2D `Delocalization.lean:47`, dimension-free linear algebra, 25 lines). In RBM3D, `green` is in `RBM3D/Green/EntryCore.lean:34`; by an import-closure script of `RBM3D.Universality.Pins` that module is not imported by `Pins` and `green_eq_spectral` has no RBM3D declaration. RBM3D `stieltjesN` is `(card)⁻¹ * (Gres M z true).trace` (`Pins.lean:88`), so RBM2D's `InjSum_stieltjesN_eq_stieltjes := rfl` (`InjSum.lean:150`) needs the identity `Gres H z true = green H z` (proved in 1 line by `simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]` at `RBM3D/Green/IBPRem.lean:105-108`, `private` there).
- Also: `git -C ../RBM2D diff --stat c9a24cf HEAD` on the two source files is non-empty (17 insertions, 130 deletions; `HEAD` = 9e0f275), so port from `c9a24cf` as the ticket says.

## (b) Script output — Mon Oct  5 06:06:29 UTC 2026

### Build and axioms
```
$ lake build RBM3D.Universality.InjSum RBM3D.Universality.PoissonSmoothing 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3333 jobs).
$ lake env lean ax.lean   (import RBM3D.Universality.PoissonSmoothing; #print axioms ...)
'RBM.Univ.InjSum_IsTestFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.InjSum_stieltjes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.poissonSmooth_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.InjSum_stieltjesN_eq_stieltjes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.stieltjes_eta_mul_im_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.stieltjes_im_eq_normalized_specWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.injSum_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.sum_poissonSmooth_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.sum_prod_lorentz_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/{InjSum,PoissonSmoothing}.lean; echo rc=$?
rc=1
```

### Target statements (extracted by script)
```
29:def InjSum_IsTestFun {k : ℕ} (O : (Fin k → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) O ∧ HasCompactSupport O
30-
31-/-- The Stieltjes transform `m(z) = N⁻¹ Tr (H - z)⁻¹` (RBM1D `Flow/Universality.lean:1518`). -/
32-noncomputable def InjSum_stieltjes {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
32:noncomputable def InjSum_stieltjes {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
33-    ℂ :=
34-  (Fintype.card n : ℂ)⁻¹ * (green H z).trace
35-
975:theorem poissonSmooth_error {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : InjSum_IsTestFun O) :
976-    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin k → ℝ,
977-      |O x - poissonSmooth ε O x| ≤ C * ε * ∏ j, (1 + x j ^ 2)⁻¹ := by
978-  obtain ⟨R, hR1, hRsupp⟩ : ∃ R : ℝ, 1 ≤ R ∧
```

### Diff against the RBM2D source (c9a24cf) by script
```
$ diff <(git -C ../RBM2D show c9a24cf:RBM2D/Universality/PoissonSmoothing.lean) RBM3D/Universality/PoissonSmoothing.lean   (only comment/import lines and the appended instances)
6c6
16c16
18c18
22c22
1057a1058,1072
$ diff <(... InjSum.lean) RBM3D/Universality/InjSum.lean | grep -E "^[0-9]"
8c8,9
11c12
13c14
37a39,72
38a74,79
55c96
152c193,194
159c201
166c208
```

### Compiled nonempty instances (in the files)
```
/-- Ticket T2178 instance: `poissonSmooth_error` at `k = 1`, the merged bump `UNInst.bump`
(`Universality/Pins.lean`; nondegenerate: value `1` at `0`, `0` at `3`), applied at the smoothing
scale `ε = 1/1000`; the constant is the one produced by the theorem. -/
example : (UNInst.bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ (UNInst.bump : (Fin 1 → ℝ) → ℝ) (fun _ => 3) = 0 ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin 1 → ℝ,
      |(UNInst.bump : (Fin 1 → ℝ) → ℝ) x - poissonSmooth (1 / 1000 : ℝ) (UNInst.bump : (Fin 1 → ℝ) → ℝ) x| ≤
        C * (1 / 1000 : ℝ) * ∏ j, (1 + x j ^ 2)⁻¹ := by
  obtain ⟨h0, h3⟩ := UNInst.bump_nondegenerate
  obtain ⟨C, hC, hbd⟩ := poissonSmooth_error
    (show InjSum_IsTestFun (UNInst.bump : (Fin 1 → ℝ) → ℝ) from UNInst.bump_testFun)
  exact ⟨h0, h3, C, hC, fun x => hbd (1 / 1000) (by norm_num) (by norm_num) x⟩

/-- Ticket T2178 instance: `InjSum_IsTestFun` holds for the merged bump on `ℝ^1`. -/
example : InjSum_IsTestFun (UNInst.bump : (Fin 1 → ℝ) → ℝ) := UNInst.bump_testFun
-- also source instances kept: InjSum.lean bump_isTestFun k (InjSumCheck), injSum_decomp at k=2, Stieltjes at diag(1,2,3)
RBM3D/Universality/InjSum.lean:588:private theorem bump_isTestFun (k : ℕ) : InjSum_IsTestFun (bump k) :=
RBM3D/Universality/InjSum.lean:600:example :
RBM3D/Universality/InjSum.lean:607:example :
RBM3D/Universality/InjSum.lean:613:example :
RBM3D/Universality/InjSum.lean:620:example :
RBM3D/Universality/InjSum.lean:626:example : (bump 2) 0 = 1 ∧
RBM3D/Universality/PoissonSmoothing.lean:1041:private theorem bump_isTestFun (k : ℕ) : InjSum_IsTestFun (bump k) :=
RBM3D/Universality/PoissonSmoothing.lean:1053:example : (bump 1) 0 = 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin 1 → ℝ,
RBM3D/Universality/PoissonSmoothing.lean:1061:example : (UNInst.bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ (UNInst.bump : (Fin 1 → ℝ) → ℝ) (fun _ => 3) = 0 ∧
RBM3D/Universality/PoissonSmoothing.lean:1071:example : InjSum_IsTestFun (UNInst.bump : (Fin 1 → ℝ) → ℝ) := UNInst.bump_testFun
RBM3D/Universality/PoissonSmoothing.lean:1074:example :
RBM3D/Universality/PoissonSmoothing.lean:1082:example :
```

### Name clash and scope
```
$ for n in <13 public names>; do git grep -c -w -- $n main -- RBM3D RBM3D.lean; done   (matches on main)
injSum_decomp:        0
InjSum_IsTestFun:        0
InjSum_stieltjes:        0
InjSum_stieltjesN_eq_stieltjes:        0
poissonKernel:        0
poissonSmooth:        0
poissonSmooth_error:        0
stieltjes_eta_mul_im_mono:        0
stieltjes_im_eq_normalized_specWeight:        0
stieltjesN_eta_mul_im_mono:        0
stieltjesN_im_eq_normalized_specWeight:        0
sum_poissonSmooth_eq:        0
sum_prod_lorentz_eq:        0
$ git diff --stat main...t/T2178
 RBM3D/Universality/InjSum.lean           |  643 ++++++++++++++++++
 RBM3D/Universality/PoissonSmoothing.lean | 1092 ++++++++++++++++++++++++++++++
 2 files changed, 1735 insertions(+)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <InjSum, PoissonSmoothing, Delocalization>
 RBM2D/Delocalization.lean                | 56 +++-----------------
 RBM2D/Universality/InjSum.lean           | 88 ++++----------------------------
 RBM2D/Universality/PoissonSmoothing.lean | 59 +++------------------
 3 files changed, 23 insertions(+), 180 deletions(-)
```

### Narrative
- Ports: RBM2D `Universality/InjSum.lean` (601 lines) and `Universality/PoissonSmoothing.lean` (1077 lines) at `c9a24cf`, read via `git show`. Both are dimension-free (no `Z2`, `d = 2` or `(WL)^2` tokens; checked by grep before the port); nothing outside the T2162 classification (F1-F5) arose.
- Changes vs source: imports (`RBM2D.Universality.*` -> `RBM3D.Universality.*`, plus `RBM3D.Green.EntryCore` for `RBM.green`), header comments, and the dependency on `green_eq_spectral` / `stieltjesN` (preflight note): `green_eq_spectral` (RBM2D `Delocalization.lean:47`, copied verbatim) is a private helper `InjSum_green_eq_spectral`; `InjSum_Gres_true : Gauss.Gres H z true = green H z` (private, same proof as `IBPRem_Gres_true`) replaces the `rfl` of `InjSum_stieltjesN_eq_stieltjes`, and the two `stieltjesN_*` corollaries now go through it. All statements are unchanged; every public name of both source files is kept (13 names, none exists on `main`).
- `InjSum_stieltjes` keeps the source body with `green` (RBM3D `RBM.green`, `Green/EntryCore.lean:34`, same definition `(H - z • 1)⁻¹`), so it is no longer definitionally `stieltjesN` (RBM3D `stieltjesN` uses `Gres H z true`); the equality is the proved theorem `InjSum_stieltjesN_eq_stieltjes`.
- Instances: source examples kept (k=1 bump `poissonSmooth_error`, k=2 `injSum_decomp`, Stieltjes at diag(1,2,3)); added the two ticket examples with `UNInst.bump` (k=1, `ε = 1/1000`; `bump 0 = 1`, `bump 3 = 0`) for `poissonSmooth_error` and `InjSum_IsTestFun`. `InjSum_stieltjes` has its own instances (diag(1,2,3), `η = 1/10 <= 1`).
- The full `lake build` (with `#assert_rbm_axioms`) is not run here: the two modules are not imported by `RBM3D.lean` until the hub's merge step; module builds and axioms of every public declaration listed above are the evidence.

## (c) Verified Mathlib names
All names used are those of the RBM2D files, which compile unchanged under the pinned Mathlib: `ContDiffBump`, `ContDiffBump.contDiff`, `.hasCompactSupport`, `.one_of_mem_closedBall`, `.zero_of_le_dist` (via `UNInst.bump_nondegenerate`), `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.IsHermitian.eigenvectorUnitary`, `Matrix.inv_eq_right_inv`, `Matrix.isHermitian_diagonal_of_self_adjoint` (all elaborated in the builds above).

## (d) Open issues and paper-delta candidates
- Open: none. `InjSum_stieltjes` (source `green` body) vs `stieltjesN` (`Gres _ _ true`) differ only definitionally; bridged by `InjSum_stieltjesN_eq_stieltjes`. T2178a (candidate, not a paper difference): note for later UN tickets that `stieltjesN_*` and `InjSum_*` statements are interchangeable only through that theorem, not `rfl`.
- Preflight section (a) not corrected; its dependency note (green / `green_eq_spectral` / `Gres`) was confirmed.

## Repair (amend 1; repairer claude-opus-5-5; Mon Oct  5 06:42:53 UTC 2026)

Scope: `docs/tickets/T2178-amend-1.md`: one registry line in `RBM3D/Test/Axioms.lean` (`structuralProps`). Commit `a28f98e` on `t/T2178`. No other file changed.
```
$ git diff e90fa53 a28f98e --stat
 RBM3D/Test/Axioms.lean | 1 +
 1 file changed, 1 insertion(+)
$ git diff e90fa53 a28f98e | grep "^[+-] "
+   `RBM.Univ.InjSum_IsTestFun, -- T2178: test-function condition (smooth, compact support) on data; a hypothesis of deterministic lemmas (DECISIONS §20, §56)
$ git diff main...t/T2178 --stat
 RBM3D/Test/Axioms.lean                   |    1 +
 RBM3D/Universality/InjSum.lean           |  643 ++++++++++++++++++
 RBM3D/Universality/PoissonSmoothing.lean | 1092 ++++++++++++++++++++++++++++++
 3 files changed, 1736 insertions(+)
```
Registry pre-check (worktree `RBM3D-wt/T2178` at `a28f98e`; file in scratchpad `T2178/precheck.lean`):
```
$ cat precheck.lean
import RBM3D
import RBM3D.Universality.InjSum
import RBM3D.Universality.PoissonSmoothing
#assert_rbm_axioms
$ lake env lean precheck.lean; echo exit=$?   (first 2 and lines 122-123 of 193 output lines)
axiom audit: 5324 theorems, 1883 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
premises found by scanning: 102 (borrowed 1, owed 79, structural 22).
registry: 2 borrowed + 113 owed + 57 structural; 70 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
exit=0
$ grep -c "error" precheck.out
0
```
Full build (worktree at `a28f98e`; its `RBM3D.lean` is that of `d5e2848`, and `Axioms.lean` is unchanged between `d5e2848` and `main` `52c856e`: `git diff --stat d5e2848 main -- RBM3D/Test/Axioms.lean` prints nothing):
```
$ lake build 2>&1 | tail -1; echo exit
Build completed successfully (3976 jobs).
exit=0
```
