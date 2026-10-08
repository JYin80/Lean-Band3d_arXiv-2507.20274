Auditor model: claude-opus-5-5

# T2331 audit (round 1) — BA-P4a `RBM3D/BA/KHeat.lean`

Thu Oct  8 12:35:49 UTC 2026 (`date -u`). Audit worktree `../RBM3D-wt/T2331-audit1`, detached at `t/T2331` = `adff21c`
(merge-base with `main` `7b9fefe`; `main` = `d760deb`). Scratch files: scratchpad `T2331/` (`eq.lean`, `cmp.py`, `inst.lean`).

## 1. Scope, hygiene, build

```
$ git diff --stat main...t/T2331
 RBM3D/BA/KHeat.lean | 1420 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1420 insertions(+)
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/BA/KHeat.lean
(no output)
$ grep -cE "^\s*(structure|class|instance)\b" RBM3D/BA/KHeat.lean
0
$ grep -n "^import" RBM3D/BA/KHeat.lean
6:import RBM3D.BA.KSymbol
7:import RBM3D.Propagator.HeatProduct
8:import Mathlib.Analysis.Normed.Algebra.MatrixExponential
$ lake build RBM3D.BA.KHeat 2>&1 | grep -E "error|Build completed"
Build completed successfully (3741 jobs).
```
The third import is the Mathlib file of `Matrix.exp_add_of_commute`, listed in the prove report (ticket: "and what a
lemma needs; list it"). No merged file changed, so no frozen signature changes. No new structure, so no hypothesis hidden in a field.

## 2. Statements against the pins (check file `docs/tickets/checks/T2331-check.lean`, section 2)

```
$ python3 -I cmp.py <check> RBM3D/BA/KHeat.lean RBM3D/Propagator/HeatProduct.lean   (whitespace-normalized text)
BAP def equal: True
kBA def equal: True
BATheta_eq_laplace_kBA statement equal: True
BAP_semigroup_shift statement equal: True
kBA_basic statement equal: True
kBA_fourier statement equal: True
kBA_diag_le statement equal: True
kBA_gap statement equal: True
kProd_gap (kProd d L τ -> kBA d L g E m τ) vs kBA_gap, equal: False
   (ndiff: `1 ≤ d` -> `0 < d`; inserted `∀ Λ κ : ℝ, 0 < Λ → 0 < κ →` before `∃ C c`, and
    `3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →` after `[NeZero L],`; conclusions identical)
```
The kernel-specific binders of `kBA_gap` are the pin's (the check file), placed before `∃ C c` only for `(d, Λ, κ)`, so
`C, c` are uniform in `L`, `g ∈ (0, Λ]`, `E`, `m`. The three conclusions (exponents `L^{-d}`, `L^{-(d+1)}`,
`L^{-(d+2)}`, rate `e^{-cτ/L²}`, cut `τ ≥ L²`) are `kProd_gap`'s verbatim, as supervisor 1048 C1 requires.

Elaboration equality (check file + `import RBM3D.BA.KHeat` + one `example` per target + `rfl` on the definitions):
```
$ lake env lean eq.lean   (examples: `example : RBM.BA.T2331Check.T2331_<n> := RBM.BA.<n>` for the six;
                           `example : @RBM.BA.T2331Check.BAP = @RBM.BA.BAP := rfl`, same for `kBA`)
'RBM.BA.BATheta_eq_laplace_kBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAP_semigroup_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_basic' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
lean exit 0
```
Against the ticket's mathematics:
- `BATheta_eq_laplace_kBA` covers (2): `0 ≤ t < 1`, `Θ^{(+,-)}_t(0,a) = ∫_{Ioi 0} e^{-(1-t)u} kBA(t g² u, a) du`.
- `BAP_semigroup_shift` covers (1), semigroup and shift.
- `kBA_basic` covers (1): `0 ≤ kBA ≤ 1` and mass 1 for `τ ≥ 0`, `δ_0` at `τ = 0`, even, continuous.
- `kBA_fourier` covers (3): it holds for all real `τ` with no `BASelf`, which is stronger than (3) needs.
- `kBA_diag_le` covers (4): `≤ C(min(1, τ^{-d/2}) + L^{-d})` for `τ > 0`.
- `kBA_gap` covers (5).
- No index range is collapsed: `a`, `i`, `j` and `k` range over all of `Zd d L` / `Fin d`.

## 3. Vacuity, hidden hypotheses, cycles

- All hypotheses are explicit Props in the signatures: `BASelf`, `BAReal := BASelf ∧ κ ≤ m.im` (`MFixedPoint.lean:432`),
  `0 < g`, `g ≤ Λ`, `3 ≤ L`, and the `t`, `τ`, `s` ranges.
- No external hypothesis and no `∀ᶠ`, so no limit check applies.
- Dependencies are merged modules (`KSymbol`, `HeatProduct`, plus Mathlib). `KHeat` is imported by no module, so no cycle is possible.
- `BASelf` is satisfiable at the concrete data (§4). The `FlowPt` fields used are proved, not assumed:
```
structure FlowPt (L : ℕ) [NeZero L] (g : ℝ) where          -- MFixedPoint.lean:877
  E : ℝ ; m0 : ℂ ; g0 : ℝ ; g0_pos : 0 < g0 ; g0_le : g0 ≤ g ; real : BAReal 3 L g0 m0.im E m0
def P : FlowPt 4 10 := (exists_flowPt 4 (g := 10) (by norm_num)).some   -- MFixedPoint.lean:893 (merged theorem)
```
  `κ = P.m0.im > 0` comes from `P.real.1.1`, so the instance is not at `κ = 0`.

## 4. Compiled nonempty instances (namespace `RBM.BA.KHeatInst`, data `d = 3`, `L = 4`, `Λ = 10`, `P`)

| target | instance(s) | concrete data | hypotheses discharged |
|---|---|---|---|
| `kBA_basic` | `inst_zero_delta`, `inst_mass`, `inst_nonneg_le_one`, `inst_even`, `inst_continuous` | `τ = 0, 1, 2, 1/2`, `a = (1,0,2)` | `P.g0_pos`, `P.real.1` |
| `kBA_fourier` | `inst_fourier` | `τ = 1`, `a = (1,0,2)` | `P.g0_pos` |
| `BAP_semigroup_shift` | `inst_semigroup`, `inst_shift` | `s = 1/2`, `s' = 3/2`; `a = (1,1,0)`, `b = (0,1,2)` | `P.real.1`, `norm_num` |
| `BATheta_eq_laplace_kBA` | `inst_laplace`, `inst_laplace_origin` | `t = 1/2`, `a = (1,0,0)`; `t = 3/4`, `a = 0` | `3 ≤ 4`, `P.g0_pos`, `P.real.1`, `0 ≤ t < 1` |
| `kBA_diag_le` | `inst_diag_le` | `τ = 4`, `a = 0`, `Λ = 10`, `κ = Im m₀` | `0 < 3`, `0 < 10`, `0 < κ`, `3 ≤ 4`, `P.g0_pos`, `P.g0_le`, `P.real`, `0 < 4` |
| `kBA_gap` | `inst_gap`, `inst_gap_diag` | `τ = 16 = L²`, `a = (1,0,2)`, `(i,j) = (0,2)`; `τ = 32`, `(1,1)` | same, plus `16 ≤ 4²` |

All three instances the ticket asks for are present: `τ = 0` gives `δ_0`, `Σ_a kBA 1 a = 1`, and `kBA_gap` at `τ = 16`.
No hypothesis is left open. None of the data is degenerate: `N = 4³ = 64`, no empty index, `t ∈ (0,1)`, `τ ≥ L² > 0`, no `False` premise.
```
$ lake env lean inst.lean   (import RBM3D.BA.KHeat; #print axioms of instances)
'RBM.BA.KHeatInst.inst_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatInst.inst_laplace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatInst.inst_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatInst.inst_zero_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatInst.inst_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatInst.inst_semigroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatInst.inst_fourier' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.BA.MFixedPointInst.P : RBM.BA.MFixedPointInst.FlowPt 4 10
exit 0
```

## 5. Names

```
$ git grep (main, RBM3D/*.lean outside Probe/) for declarations named
  BAP kBA BAP_nonneg BAP_row_sum BAP_le_one BAP_shift BAP_neg BAP_zero kBA_fourier kBA_basic
  BAP_semigroup_shift BATheta_eq_laplace_kBA kBA_gap kBA_diag_le KHeatInst
all 0
```
The public names are the ticket's targets, the public helpers the ticket allows (`BAP_*`), and the instances, which sit in `KHeatInst`. The 46 other helpers are `private`.

## 6. Paper deltas

- The Poisson semigroup `P_s`, the diffusive time `τ = g² s`, the Laplace identity and regime (ii) are Lean-side design
  (supervisor 1048 C1/C2). They are not in `A_deterministic_estimates.tex`, which has only the Neumann series and a random-walk sketch.
- Prove report (d) proposes them as candidate `T2331a`.
- `git grep T2331 main -- docs/paper-deltas.md` finds 0 hits, so the dispatcher still has to append it.
- I found no other Lean/paper statement difference.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. `BAP_semigroup_shift` carries `BASelf` and `0 ≤ s, s'`, which its proof does not use (prove report says so). These are pinned hypotheses and only make the statement weaker than possible.
- O2. `kBA_gap` constants are existential. The internal rate `c_g` from `BAK_gap` is of order `1e-18`, which a
  downstream ticket needing explicit constants should note. The pin does not ask for explicit constants.
- O3. I did not rerun the full `lake build` (the hub runs it at merge). The prove report pastes a registry pre-check with exit 0.

## Verdict per target

- `BAP`, `kBA` (definitions): PASS
- `BATheta_eq_laplace_kBA`: PASS
- `BAP_semigroup_shift`: PASS
- `kBA_basic`: PASS
- `kBA_fourier`: PASS
- `kBA_diag_le`: PASS
- `kBA_gap`: PASS

**Ticket verdict: PASS.** No dispatcher sign-off needed. Paper-delta candidate `T2331a` still has to be appended by the dispatcher.
