Auditor model: claude-opus-5-5

# T2324 audit (round 1) — BA-P3 `RBM3D/BA/KSymbol.lean`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2324-audit1`, detached at `t/T2324` = `cf189e6`; `date -u`: Thu Oct  8 06:31:07 UTC 2026.
Scripts and scratch files: scratchpad `T2324/` (`eq.lean`, `ax.lean`).

## 1. Statements against the pin (check file sections 2 and 3)

```
$ python3 (whitespace-normalized text of check-file section 2/3 vs RBM3D/BA/KSymbol.lean)
def BAKhat equal: True
def BAthetaSq equal: True
thm BAvar_lower equal: True
thm BAMB_perm equal: True
thm BAK_dir_eq equal: True
thm BAK_dir_ge equal: True
thm BAKhat_eq equal: True
thm BAK_gap equal: True
thm BAK_lazy equal: True
thm BAK_second_moment equal: True
```
Elaboration check: `eq.lean` is the check file with section 2 deleted (so `BAKhat`/`BAthetaSq` resolve to `RBM.BA`),
`import RBM3D.BA.KSymbol` added, and `example : T2324_<n> := @RBM.BA.<n>` for the 8 targets.
```
$ lake env lean eq.lean 2>&1 | grep -iE "error|sorry"; echo "eq exit ${pipestatus[1]}"
eq exit 0
```
Mathematics vs ticket: T1 `R = 2dg + |E+m|`, `3 ≤ L`, `0 < d` (as pinned); T4, T6, T8: `∃ c` (resp. `C`) after
`d, Λ, κ` and before `L, g, E, m` (uniform in `L` and in `g ∈ (0, Λ]`, as required by §29 (iii)); `2 ≤ d` only in T8;
T7 has no hypothesis on `g`, `L`; T2 holds for every `z m` (conjugation commutes with `Ring.inverse`). No hypothesis added or
dropped relative to the pin. None is a special case or conditional adapter.

## 2. Vacuity, hidden hypotheses, cycles

- No structure-field hypothesis: every hypothesis is an explicit binder of the pinned `Prop`; `BAReal = BASelf ∧ κ ≤ Im m` (merged, `MFixedPoint.lean:432`).
- Imports: `RBM3D.BA.KKernel` only (line 6; `FlowPins` transitive, used at `:421` `baSelf_none_of_gt`). All dependencies are merged on `main`
  (`BAMB_trace_eq_sum` `:213`, `BAK_adj_sum_ge` `:440`, `BAK_exp_moment_le` for T8). No registry `Prop`, no external hypothesis, so no limit check is needed.
- No cycle: the file is new and nothing on `main` imports it.

## 3. Compiled nonempty instances (`RBM.BA.KSymbolInst`, `KSymbol.lean:759-826`)

Data: `P : FlowPt 4 10 := (exists_flowPt 4 (g := 10) _).some` (merged `MFixedPoint.lean:893`); fields `0 < P.g0 ≤ 10`,
`P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`, so `κ = Im m₀ > 0` (`P.real.1.1`). `d = 3`, `L = 4`, `Λ = 10`.
| target | instance | hypotheses discharged |
|---|---|---|
| T1 `BAvar_lower` | `inst_var_lower` | `3 ≤ 4`, `0 < 3`, `P.g0_pos`, `P.real.1.1`, `P.real` |
| T2 `BAMB_perm` | `inst_perm` at `Equiv.swap 0 1`, `a = e₁`, `b = e₂` | none needed |
| T3 `BAK_dir_eq` | `inst_dir_eq` at `(i,s) = (0,true)` | `3 ≤ 4`, `0 < 3` |
| T4 `BAK_dir_ge` | `inst_dir_ge` at `(1,false)` | `0 < 10`, `0 < κ`, `3 ≤ 4`, `P.g0_pos`, `P.g0_le`, `P.real` |
| T5 `BAKhat_eq` | `inst_Khat_eq` at `k = (1,0,0)` | none needed |
| T6 `BAK_gap` | `inst_gap` at `k = (1,0,0)`, with `inst_thetaSq_pos : 0 < BAthetaSq 3 4 ![1,0,0]` | as T4 |
| T7 `BAK_lazy` | `inst_lazy` at `k = (1,0,0)` | `P.real.1.1`, `P.real` |
| T8 `BAK_second_moment` | `inst_second_moment` | `2 ≤ 3`, as T4 |
| ticket extra | `inst_Khat_zero : BAKhat 3 4 P.g0 P.E P.m0 0 = 1` | `P.real.1` |

No `N = 0`, no empty index, no `False` premise; the gap instance is at a nonzero momentum (`|θ|² > 0` proved).
No hypothesis is left open in any instance. All compile (build below; axioms in section 4).

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.BA.KSymbol 2>&1 | grep -E "error|warning|sorry|Build completed"   (filtered to KSymbol.lean)
$ lake build RBM3D.BA.KSymbol 2>&1 | grep -c "KSymbol.lean"
0
Build completed successfully (3739 jobs).
exit 0
```
(The remaining warning lines of the build are in merged upstream files: `Defs/Tail.lean`, `Propagator/*`, `Induction/*`, `Path/*`, `BA/Ward.lean`.)
```
$ lake env lean ax.lean   (#print axioms of 8 targets, 2 defs, BAK_perm, 10 instances); exit 0
'RBM.BA.BAvar_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_dir_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_dir_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKhat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_lazy' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKhat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAthetaSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAK_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_var_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_dir_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_dir_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_Khat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_thetaSq_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_lazy' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KSymbolInst.inst_Khat_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|@\[implemented_by|extern" RBM3D/BA/KSymbol.lean
20:set_option linter.style.longLine false
21:set_option linter.unusedSimpArgs false
22:set_option linter.unusedVariables false
23:set_option linter.style.setOption false
24:set_option linter.flexible false
$ git diff --stat main...t/T2324 | tail -1
 1 file changed, 828 insertions(+)
$ git diff --name-only main...t/T2324 -- ':!RBM3D/BA/KSymbol.lean' | wc -l
       0
```
Only linter options; no `sorry`/`admit`/`axiom`/`native_decide`. Only the sole writable file is touched; no merged file and no frozen
signature is changed. File length 828 lines: the preset P3a/P3b cut (1500) is not triggered.
The full `lake build` (and `#assert_rbm_axioms`) is left to the hub at merge.

## 5. Paper deltas

D614 (`docs/paper-deltas.md:1573`) records the gap these targets close: non-degeneracy for `g ∈ [(2C)⁻¹, Λ]`, which the paper does not cover,
the variance bound `1 − |m|² ≥ 2dg²/R⁴`, permutation invariance, `Σ_{b∼0} K_{0b} ≥ c g²`. The symbol, gap, laziness and second-moment
statements (T5–T8) are the input of `A:58-64`'s local CLT on the same route. The prove report proposes no new candidate. I found no
further Lean/paper statement difference: the constants are explicit and not sharp, which CLAUDE.md §7 allows.

## 6. Observations (no verdict effect)

- O1. `BAK_perm` (`KSymbol.lean:346`) is public, not pinned, and has no `KSymbol_` prefix (CLAUDE.md §3 (E)). The ticket's name-clash grep lists
  `BAK_perm` (0 hits on `main`), so the dispatcher expected the name. No statement, instance, build or axiom is affected. The dispatcher may rename it later.
- O2. `KSymbol_eig_le` duplicates the private `FlowPins_eig_le` (`FlowPins.lean:734`). This is copied text, not an import.
- O3. The instance datum `P` is an `Exists.some` (merged `MFixedPointInst.P`), not a numeric literal. It still satisfies every
  deterministic hypothesis (`0 < g0 ≤ 10`, `BAReal` with `κ = Im m₀ > 0`) with `L = 4`, `d = 3`, so it is a nondegenerate instance.

## Verdict

| target | verdict |
|---|---|
| T1 `BAvar_lower` | PASS |
| T2 `BAMB_perm` | PASS |
| T3 `BAK_dir_eq` | PASS |
| T4 `BAK_dir_ge` | PASS |
| T5 `BAKhat_eq` | PASS |
| T6 `BAK_gap` | PASS |
| T7 `BAK_lazy` | PASS |
| T8 `BAK_second_moment` | PASS |
| defs `BAKhat`, `BAthetaSq` | PASS (verbatim) |

**T2324: PASS.** No dispatcher sign-off is needed.
