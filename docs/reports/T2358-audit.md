Auditor model: claude-opus-5-5

# T2358 audit, round 2 (LW-13b R1, `RBM3D/Graph/LWProv.lean`)

Written Fri Oct  9 20:55:39 UTC 2026. Inputs: ticket `docs/tickets/T2358.md`, Amend 1, Amend 2 (DECISIONS §167, R-a), prove report `docs/reports/T2358-prove.md`, branch `t/T2358` at 6d6ef4d, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2358-audit2` (detached at 6d6ef4d). `F` = `RBM3D/Graph/LWProv.lean`. `S` = scratchpad `T2358/`.

**Overall verdict: PASS.** Every target of the ticket as amended (Amend 1, Amend 2) is in `F` with the pinned statement, compiles, uses only the three standard axioms, adds no premise to the ledger, and has a compiled nondegenerate instance. The Amend 2 edit is only the five named deletions plus docstring edits (checked by script).

## 1. Scope of the branch
```
$ git diff --stat main...HEAD
 RBM3D/Graph/LWProv.lean | 1820 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1820 insertions(+)
$ grep -n "^import" $F
6:import RBM3D.Graph.LWEngine
7:import RBM3D.Graph.LWMoment
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " $F ; wc -l $F
    1820 RBM3D/Graph/LWProv.lean          (no grep hits; 1820 ≤ stop line 1950)
```
Only the sole writable file is touched. It is a new file, so no frozen signature is touched. The imports are the two that the ticket allows.

## 2. Amend 2 edit check (`git diff da182dc..HEAD -- F`)
```
$ git diff da182dc..HEAD --numstat
10	80	RBM3D/Graph/LWProv.lean
$ python3 -I $S/amend2.py old.lean(=da182dc:F) F
  # strips /- -/ blocks and -- comments in both; deletes from old the blocks headed by the 5 Amend-2 names
declarations removed: ['LocStepXProv', 'lwProv_Functional', 'lwProv_pin_of_functional', 'lwProv_StepFunctional', 'lwProv_locStepXProv_of_functional']
code lines removed: 55  old code lines: 1522  new code lines: 1467
old minus named decls == new (comments/docstrings stripped): True
```
The hunks that remain are docstring and comment hunks: the module doc (F:13-19), the docstring of `lwProv_stepPos` (F:1510), the section-9 header, and the docstrings of `lwProv_LocStepXProvPos` and of the `lwProv_wildGraph` remark. That is edit items 1–3 of Amend 2. Item 4 (everything else byte-identical in code) holds. **PASS.**

## 3. Statements against the pin (probe `t/T2348:RBM3D/Probe/T2348Pins.lean:29-185, 291-310`)
```
$ (sed -n 29,185p probe; sed -n 291,310p probe) > probe_pins; sed -n 37,208p F > file_pins
$ diff <(strip probe_pins) <(strip file_pins) | grep '^[0-9]'     # strip = drop docstrings/comments/blank lines
24,28d23     <- def LWExpData (C3: not a definition of the file)
31c26,29     <- WExp binder: "LWExpData sz n z u m Sp M →" replaced by the 9 conjuncts curried, same order
44c42        <- WExp.refl proof: intro of the 9 hypotheses
48,49c46,47  <- WExp.comp proof: same
51c49        <- WExp.comp proof: same
55c53,56     <- WExp.prod binder: (hD : LWExpData …) replaced by (hG)(hz)(hu)(hm0)(hzm)(hSp)(hSpT)(hM)(hM0)
59c60,61     <- WExp.prod proof term
81,85d82     <- def LocStepXProv (removed by Amend 2)
```
The nine inline conjuncts are, in order: `GaussIBP sz`, `0 < z.im`, `0 < u`, `m ≠ 0`, `z + u m = -m⁻¹`, the `Sp` identity, `Spᵀ = Sp`, `∀ a, M a a = m`, and `∀ a b, a ≠ b → M a b = 0`. They match the probe's `LWExpData` (probe :69-75) one by one. `LWEngineProv`, `lwEngineProv_imp_localregularX`, `ProvOut*`, `CoverBy*`, `ProvOutX*`, `mkProv`, `stepOuts`, `LWfD` and `LWfD_union` show no code hunk. The only differences are C3, the namespace and Amend 2. **Copied declarations: PASS.**

### Targets (`lake env lean $S/Check.lean` in the audit worktree, exit 0)
```
lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos
lw_localregularXP : LWEngineProv
def RBM.Graph.lwProv_LocStepXProvPos : Prop :=
∀ (P : PGraph (Fin 2)) (LX : List ((ℕ × ℕ) × PGraph (Fin 2))),
  LocStepX P LX →
    P.g.Normal →
      ∃ ps,
        List.map (fun o => (o.tag, o.Q)) ps = LX ∧
          (∀ o ∈ ps, o.ExtOK ∧ { Q := o.Q, π := o.π }.Molecular) ∧
            ∀ (m : ℂ) (t0 : ℕ × ℕ), WExp m (lwEvX m (t0, P)) (List.map (fun o => mkProv m t0 P (o.tag, o.Q) o.π) ps)
RBM.Graph.LocStepXProv: false
RBM.Graph.locStepXProv_holds: false
```
- `lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos` (F:1797). This is the replacement target of Amend 2 (R-a). It has the name and statement that Amend 2 pins ("exactly as on da182dc"; §2 shows no code change). The `Normal` premise of Amend 1 is present. The proof is `fun P LX h hN => lwProv_stepPos P LX h hN`, with no further hypothesis. **PASS.**
- `lw_localregularXP : LWEngineProv` (F:1680). This is the pinned type. `LWEngineProv` is the probe's text and, as Amend 1 states, has no `Normal` premise: the root normality comes from `fxyPowGraph_normal p` inside the proof. **PASS.**
- `lwProv_bridge` (C1, F:233). The left side is `pvalW (fxyPowGraph p).pack (lwMoment_D …) (fun ℓ => ∏ k, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ D then 1 else 0) ![x, y]`. The right side is `((‖LWfD sz n E t ω D x y‖ ^ p : ℝ) : ℂ)`. The hypotheses are `Even p` (the same as the twin `lwMoment_fxyPow_val`, `LWMoment.lean:1748`: `{p : ℕ} (hp : Even p)`) plus `D`. Both sides match the ticket text. **PASS.**
- The old target `locStepXProv_holds : LocStepXProv` is gone, as Amend 2 decides. Neither name exists in the environment (above), and `grep -rn "LocStepXProv\b\|locStepXProv_holds" RBM3D | grep -v /Probe/` finds nothing.

## 4. Hidden hypotheses, vacuity, cycles
- The structures `ProvOut` (fields `Q`, `π`, F:66-68) and `ProvOutX` (fields `tag`, `Q`, `π`, F:145-148) carry data only and no Prop field.
- The three targets have no hypotheses beyond those shown (`lwProv_bridge`: only `Even p`). `lw_localregularXP` applies `lwProv_exists` with `fxyPowGraph_normal p`, which is merged.
- Dependencies are merged modules only (the imports in §1). No module imports `LWProv` (new file), so there is no cycle.
- Registry pre-check: the ledger is the same with and without `F`:
```
$ lake env lean $S/Check.lean   (import RBM3D; import RBM3D.Graph.LWProv; … ; #assert_rbm_axioms)   check_exit=0
axiom audit: 10645 theorems, 3136 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 133 (borrowed 1, owed 71, structural 42, refuted 6, superseded 13).
$ lake env lean $S/Base.lean    (import RBM3D; #assert_rbm_axioms)   base_exit=0
axiom audit: 10542 theorems, 3090 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 133 (borrowed 1, owed 71, structural 42, refuted 6, superseded 13).
$ diff <(ledger part of base.out) <(ledger part of check.out); echo ledger_diff_exit=$?
ledger_diff_exit=0
```
No new premise enters the ledger, as C3 requires. **PASS.**

## 5. Compiled nonempty instances (namespace `RBM.Graph.LWProvInst`, F:1710-1782, and section 9)
| target | where | data | verdict |
|---|---|---|---|
| `ProvOut.molecular_id` (pinned instance) | F:1713 | theorem for every `P`; used at `fxyPowGraph 2` | PASS |
| `valW_one`/`pvalW_one` | F:1716 | `fxyPowGraph 2`, `lwWxInstSz`, `ω = 0` | PASS |
| `WExp.refl`, `WExp.comp` at `fxyPowGraph 2` | F:1722 | `p = 2` | PASS |
| `Molecular.comp`, `CoverBy.comp`, initial `Cover` | F:1726-1729 | `fxyPowGraph 2` | PASS |
| `lw_localregularXP`, `lwEngineProv_imp_localregularX` | F:1733-1734 | `p = 2`, `c = 1/4` (`0 < c` by `norm_num`), `K0 = 1`, `d = 3`, `D = 10` | PASS |
| `WExp.prod` | F:1738 | all nine data hypotheses discharged by merged lemmas (`gaussIBP`, `lwWx_inst_im`, `lwWx_flow`, …); `WExp` from `lw_localregularXP`; weights `1` or `1/2` | PASS |
| bridge, `p = 2`, `D = univ` = merged value | F:1753 | `lwWxInstSz` (d = 3), `n = 0`, `ω = 0`, `x = 0`, `y = Pi.single 0 1`; ends at `‖LWf …‖^2` | PASS |
| bridge, proper `D = {0}` | F:1767 | every `ω` | PASS |
| `LWfD_union` | F:1774 | `{0}`, `{1}` disjoint | PASS |
| `lwProv_locStepXProvPos_holds` | F:1800 | `p2Graph = fxyPowGraph 2`, the merged `LocStepX.weight` step `lwEngine_inst_stepX`, `Normal` by `fxyPowGraph_normal 2` | PASS |

None of the instances is degenerate: no `N = 0`, no empty index set, no `False` premise. Every deterministic hypothesis is discharged.

## 6. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.LWProv; echo exit=$?
✔ [3895/3895] Built RBM3D.Graph.LWProv (12s)
Build completed successfully (3895 jobs).
exit=0                                   (grep -c "^error" build.log: 0)
'RBM.Graph.lwProv_locStepXProvPos_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_localregularXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwProv_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWfD_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwEngineProv_imp_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.CoverBy.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ProvOut.Molecular.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWProvInst.ProvOut.molecular_id' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The build warnings are linter warnings in upstream modules only. **PASS.**

### Name clash on current main (a4bc3b3)
```
$ git grep -n "lwProv_\|LWProvInst\|LWfD\b\|ProvOutX\|LWEngineProv\|pvalW" main -- RBM3D ':!RBM3D/Probe'
main:RBM3D/Graph/LWMomentExpA.lean:55:as in the target: the `D`-restricted `LWfD` of R1 is not used here, R3 converts by `LWfD … univ = LWf`). -/
```
The only hit is in a docstring, not a declaration, so there is no clash. `F` does not exist on main.

## 7. Paper deltas
`grep -n "T2358\|LWProv\|LocStepXProv" docs/paper-deltas.md` finds nothing. Prove report (d) item 3 proposes no candidate, and gives the reason: C3 (inline data), Amend 1 (the `P.g.Normal` premise, supplied by the recursion and by the root) and Amend 2 (one provenance map per position instead of per value) are encodings of the design's Lean provenance layer. They change no statement of the paper. The auditor agrees: none of the delivered statements restates a paper equation differently. The paper's content enters through `lw_localregularX`, which is merged and strengthened here, and through `LWfD`/`lwProv_bridge` (the paper's `f^{>ℓ}`, `f^{≤ℓ}`, `7_8:1607-1611`). **Coverage adequate. PASS.**

## 8. Verdicts
| target | verdict |
|---|---|
| copied probe declarations + `LWfD`, `LWfD_union` (C3, Amend 1, Amend 2 only) | PASS |
| `lwProv_bridge` (C1) | PASS |
| `lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos` (Amend 2 replacement of `locStepXProv_holds`) | PASS |
| `lw_localregularXP : LWEngineProv` | PASS |
| Amend 2 edit scope (`git diff da182dc..HEAD`) | PASS |

No dispatcher sign-off is needed. The hub can merge by rule (A) and still runs the full `lake build` at merge.

## Observations (no effect on the verdict)
- O1. Many unpinned helpers are public. They carry the file prefix `lwProv_`, which §3 (E) allows. The `git grep` above finds no clash.
- O2. The `lwProv_wildGraph` remark (F:1802-1816, the R-b analysis) stays in the file, as Amend 2 item 2 allows. `lwProv_wildGraph` is a public def that no target uses.
