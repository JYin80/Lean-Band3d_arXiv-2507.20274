Auditor model: claude-opus-5-5

# T2019 audit (round 1) — PT-D Laplace-product representation and product-kernel bounds

Audit time (`date -u`): Sat Oct  3 04:00:08 UTC 2026.
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2019-audit1`, detached at `t/T2019` = `ee4e9f9f3e48919205a01b89fbe9fcaf58f19742`.

## 1. Scope

```
$ git diff --stat main...t/T2019
 RBM3D/Propagator/HeatProduct.lean | 1257 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1257 insertions(+)
$ git log --oneline main..t/T2019
ee4e9f9 T2019: PT-D Laplace-product representation of Theta_t, 1/d sum-of-minima lemma, product-kernel bounds and gap
```
Only the sole writable file is touched (new file); no frozen signature changed. Imports: `RBM3D.Propagator.HeatTorus1D`, `RBM3D.Propagator.LaplaceGauss`, `RBM3D.Propagator.Basic` and four Mathlib files; not `RBM3D`.

## 2. Statements against the pins

Script diff (`python3 diff.py`: regex-extract each pin body from `docs/tickets/checks/T2019-check.lean` and each theorem type from the source, whitespace-normalised):
```
LaplaceProd  vs Theta_eq_laplace_prod : IDENTICAL (218 chars)
SumMin       vs sum_min_ge            : IDENTICAL (146 chars)
KProdBound   vs kProd_le              : IDENTICAL (231 chars)
KProdDiff1   vs kProd_diff1_le        : IDENTICAL (287 chars)
KProdDiff2   vs kProd_diff2_le        : IDENTICAL (373 chars)
KProdGap     vs kProd_gap             : IDENTICAL (524 chars)
kProd def: IDENTICAL
```
Lean check (`lake env lean AuditCheck.lean` in the audit worktree; file = `import RBM3D.Propagator.HeatProduct` + the check file's namespace `RBM.Heat.T2019Check` verbatim + the lines below), exit 0, no errors:
```
example : LaplaceProd := RBM.Heat.Theta_eq_laplace_prod
example : SumMin := RBM.Heat.sum_min_ge
example : KProdBound := RBM.Heat.kProd_le
example : KProdDiff1 := RBM.Heat.kProd_diff1_le
example : KProdDiff2 := RBM.Heat.kProd_diff2_le
example : KProdGap := RBM.Heat.kProd_gap
example : kProd = RBM.Heat.kProd := rfl
```
Against the ticket's mathematics: `LaplaceProd` has `3 ≤ L`, `0 < g`, real `t ∈ [0,1)`, all `a`, `γ = lgGam d g t`, exponent `-(1-t)s` over `Ioi 0`; the bounds carry `min(1, τ^{-d/2})`, `τ^{-(d+1)/2}`, `τ^{-(d+2)/2}` for `0 < τ ≤ L²`, the `ℓ¹` torus norm `zdistD`, constants `∃ C c` after `d` only (uniform in `L, τ, a, i, j`); `KProdGap` for `L² ≤ τ` with `L^{-d}`, `L^{-(d+1)}`, `L^{-(d+2)}` and `e^{-cτ/L²}`; `SumMin` keeps the `1/d` factor. Upstream definitions used by the pins:
```
RBM3D/Propagator/Basic.lean:70:noncomputable def Theta (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
RBM3D/Propagator/Basic.lean-71-  Ring.inverse (1 - ξ • SB d L g)
RBM3D/Propagator/HeatKernel1D.lean:133:noncomputable def hkT (L : ℕ) [NeZero L] (τ : ℝ) (x : ZMod L) : ℝ :=
RBM3D/Propagator/HeatKernel1D.lean-134-  (L : ℝ)⁻¹ * ∑ k : ZMod L,
RBM3D/Propagator/HeatKernel1D.lean-135-    Real.cos (2 * Real.pi * (k.val : ℝ) * (x.val : ℝ) / L)
RBM3D/Propagator/HeatKernel1D.lean-136-      * Real.exp (-2 * τ * (1 - Real.cos (2 * Real.pi * (k.val : ℝ) / L)))
RBM3D/Propagator/LaplaceGauss.lean:34:noncomputable def lgGam (d : ℕ) (g t : ℝ) : ℝ := t * g ^ 2 / (1 + 2 * (d : ℝ) * g ^ 2)
RBM3D/Defs/Lattice.lean:25:def zdist (L : ℕ) (u : ZMod L) : ℕ := min u.val (L - u.val)
RBM3D/Defs/Lattice.lean:71:def zdistD (d L : ℕ) (x : Zd d L) : ℕ := ∑ i, zdist L (x i)
```
`Theta` is the genuine `Ring.inverse`, so `Theta_eq_laplace_prod` is a real identity, not a definitional unfolding.

## 3. Hidden hypotheses, vacuity, cycles

- No hypothesis `Prop`, no structure, no class in the file. Public declarations (script):
```
68:theorem sum_min_ge : ...
270:noncomputable def kProd (d L : ℕ) [NeZero L] (τ : ℝ) (a : Zd d L) : ℝ := ∏ j, hkT L τ (a j)
439:theorem kProd_le : ...      462:theorem kProd_diff1_le : ...   518:theorem kProd_diff2_le : ...
626:theorem kProd_gap : ...     1171:theorem Theta_eq_laplace_prod :
```
  All other declarations are `private`. Name-clash grep on `main` (`git grep -nwE "(def|theorem|lemma) <name>" main -- RBM3D | wc -l`): 0 for each of the seven names.
- `Theta_eq_laplace_prod` closes via `eq_Theta_of_mul d L g (norm_SB d L g hL) hnorm (laplace_matrix hL hg ht0 ht1)`: merged upstream `eq_Theta_of_mul`, `norm_SB`, plus the in-file private `laplace_matrix` (left inverse, proved from the heat equation `hkT_hasDerivAt` and integration by parts). No dependency on any unmerged or downstream declaration; no cycle.
- No external hypothesis is introduced, so no limit check is required.

## 4. Compiled nonempty instances (in `HeatProduct.lean`, lines 1194–1255)

| target | instance | deterministic hypotheses discharged |
|---|---|---|
| `Theta_eq_laplace_prod` | `d=3, L=3, g=1, t=1/2, a=0` | `3 ≤ 3` (`le_rfl`), `0<1`, `0 ≤ 1/2`, `1/2 < 1` |
| `sum_min_ge` | `d=3, τ=10, x=(1,50,0)` | `1 ≤ 3`, `0 < 10`, `0 ≤ x j` (`fin_cases`) |
| `kProd_le` | `d=3, L=5, τ=4, a=(0,1,2)` | `1 ≤ 3`, `0 < 4`, `4 ≤ 25` |
| `kProd_diff1_le` | same, `j=1` | same |
| `kProd_diff2_le` | same, `(i,j)=(0,2)` and `(1,1)` | same |
| `kProd_gap` | `d=3, L=5, τ=50, a=(0,1,2), (i,j)=(0,2)` | `1 ≤ 3`, `25 ≤ 50` |

All three instances the ticket requires are present at exactly the requested data; none is degenerate (`L ≥ 3`, `t > 0` so `γ = 1/14 > 0`, `τ` strictly inside each regime, `a ≠ 0`). The constants `C, c` stay existential, as in the pinned statements. All seven `example`s compiled in the build below.

## 5. Build, hygiene, axioms

```
$ lake build RBM3D.Propagator.HeatProduct      # in the audit worktree; error/warning lines only
warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
⚠ [3401/3401] Built RBM3D.Propagator.HeatProduct (7.8s)
warning: RBM3D/Propagator/HeatProduct.lean:218:0: `abs_prod_sub_prod_le` does not use the following hypothesis in its type:
  • [DecidableEq ι] (#2)
Build completed successfully (3401 jobs).
exit 0
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Propagator/HeatProduct.lean || echo "(none)"
(none)
$ lake env lean AuditCheck.lean   # #print axioms part
'RBM.Heat.kProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.Theta_eq_laplace_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.sum_min_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Heat.kProd_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

## 6. Paper deltas

The six statements equal the dispatcher's pins verbatim (§2); the prover introduced no Lean/paper statement difference. Prove report (d): "Paper-delta candidates: none." Agreed. The restriction to real `t ∈ [0,1)` in `LaplaceProd` is part of the pin itself (route H infrastructure, not a paper-stated lemma); no new candidate is needed from this ticket.

## 7. Observations (no verdict impact)

- O1. Linter warning: private helper `abs_prod_sub_prod_le` (line 218) carries an unused `[DecidableEq ι]`. Cosmetic.
- O2. Prove report (d) states the preflight (ii) numerics were not rerun by the prover; that does not affect the statements, which are proved in Lean.

## 8. Verdicts

| target | verdict |
|---|---|
| `kProd` (definition) | PASS |
| `Theta_eq_laplace_prod` | PASS |
| `sum_min_ge` | PASS |
| `kProd_le` | PASS |
| `kProd_diff1_le` | PASS |
| `kProd_diff2_le` | PASS |
| `kProd_gap` | PASS |

Ticket T2019: **PASS**. No dispatcher sign-off needed. Merge step for the hub: add `import RBM3D.Propagator.HeatProduct` after the last `import` line of `RBM3D.lean`, then run the full `lake build`.
