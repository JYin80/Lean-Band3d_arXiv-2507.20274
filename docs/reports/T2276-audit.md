Auditor model: claude-opus-5-5

# T2276 audit (UN-51a `Universality/ZeroModeProfile`), round 1 — Tue Oct  6 09:42:41 UTC 2026

Branch `t/T2276` at 33f413b; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2276-audit1` (detached).
Scratch files: `<scratchpad>/T2276/{defs.py,match.lean,ax.lean,root_merge.lean,ll.py}`.
## 1. Statements against the pin (check file `docs/tickets/checks/T2276-check.lean`)

Text diff of the 15 vocabulary/pin definitions (check sections 2-3), `noncomputable def` normalised to `def`:
```
$ python3 defs.py docs/tickets/checks/T2276-check.lean
ouZeta       IDENTICAL 1 lines      ouEtaQ       IDENTICAL 2 lines
Stilde       IDENTICAL 2 lines      profPMTilde  IDENTICAL 3 lines
Jmat         IDENTICAL 1 lines      profPPTilde  IDENTICAL 2 lines
SBtilde      IDENTICAL 2 lines      UNOULL       IDENTICAL 7 lines
ThetaTilde   IDENTICAL 3 lines      UNOUEq747    IDENTICAL 17 lines
xiQ          IDENTICAL 2 lines      UNG1Row      IDENTICAL 4 lines
ouTauMax     IDENTICAL 1 lines      UNG2bRow     IDENTICAL 3 lines
```
Lean match: the check file + `import RBM3D.Universality.ZeroModeProfile`, then
`example : RBM.Univ.T2276Check.T2276_<t> := @RBM.Univ.<t>` for the 13 theorems
(`Stilde_zero sum_Stilde_row ouVar_eq_Stilde Stilde_eq_SBtilde_mul ThetaTilde_zero ThetaTilde_eq
norm_ThetaTilde_sub_le profTilde_rowDiff profPMTilde_zero ouTauMax_pos ouTauMax_slack ouDiag_of_ouLL
ouRow_of_pins`) and `example : @RBM.Univ.<v> = @RBM.Univ.T2276Check.<v> := rfl` for the 15 names:
```
$ grep -c '^example' match.lean ; lake env lean match.lean > match.out 2>&1; echo "exit $?"; grep -c error match.out
34
exit 0
0
```
(34 = 6 shape examples of the check file + 13 + 15.) Every target type is the pinned type; quantifier order
of 2.4/2.5 is `∀ d, 3 ≤ d → ∀ 𝔡 κ, … → ∃ C, 0 < C ∧ ∀ L … lam … z … ζ … σ u v` (C before `L`, `lam`, `z`, `ζ`:
`C = C(d,𝔡,κ)`, no `log L`), loss `C * (lam^2)⁻¹` (2.4) and `C * (lam^2)⁻¹ / W^d` (2.5), as pinned.
Special cases (stated in the prove report, narrative): 2.4/2.5 only at `ξ = xiQ z σ ∈ {m², |m|²}`, bulk,
`0 < lam ≤ 𝔡⁻¹` — exactly the ticket's pin, not a general `Θ̃` bound; `ouDiag_of_ouLL`, `ouRow_of_pins`
are conditional on the owed pins `UNOULL`, `UNG1Row`, `UNG2bRow`, as pinned.

## 2. Hidden hypotheses, vacuity, cycles

- The four new `Prop`s are plain `def`s (no structure fields). `norm_ThetaTilde_sub_le` takes `C = 1` only
  in the branch `2 < κ` (empty bulk, `|z.re| ≤ 2 - κ < 0`); the main branch obtains `C₈` from the merged
  `prop5to8_holds … |>.zeroMode` (no hypothesis left; `Prop8ZeroMode` discharged). `ouDiag_of_ouLL`'s
  vacuous branch is `2 < κ` (|E| ≤ 2-κ < 0), the general branch covers `κ ≤ 2`.
- No cycle: `UNG1Row`, `UNG2bRow`, `UNOULL`, `UNOUEq747` do not mention `UNOURow`/`UNOUDiag`; imports are
  `Universality.OU, Endpoints, Propagator.Prop6Hold, Green.IBP, Path.Walk, Induction.Split` (all merged;
  `Path.Walk` imports `Gauss.FineModel, Defs.StochDomAt, Loop.GLoopFlow` + Mathlib; no `Main.*`, `Graph.*`, root).
- Registry: `UNOULL`, `UNG1Row`, `UNG2bRow` added to `owedProps`, `UNOUDiag`, `UNOURow` deleted (by text):
```
$ git diff main...t/T2276 -- RBM3D/Test/Axioms.lean | grep -E '^[-+] '
-   `RBM.Univ.UNOUDiag, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNOURow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
+   `RBM.Univ.UNOULL, -- (T2276, UN-51a: owed; owner UN-51 `RandomLayerB` `g1Row`; ...)
+   `RBM.Univ.UNG1Row, -- (T2276, UN-51a: owed; owner UN-51 `RandomLayerA/B`; ...)
+   `RBM.Univ.UNG2bRow, -- (T2276, UN-51a: owed; owner UN-52 `QUEFlow` `g2bRow`; ...)
```
- Limit check of the new owed moment pin `UNOULL` (at `t = 0`, `𝐇_0 = H` band, `d = 3`, `W = 2`, `lam = 1/2`,
  `E = 0.3`, `η = N^{-1+2τ}`, `τ = 1/1000`, 6 samples; the moments stay O(1) as `N` grows, far below the
  deterministic `η^{-2p}`, consistent with `≤ N^δ` eventually):
```
$ python3 ll.py
L=3 N=216 eta=4.68e-03 rowsum=1.000 E|G|^2=3.14 E|G|^4=39.97 E|G|^6=1407.63 maxN^0.1=1.71
L=4 N=512 eta=1.98e-03 rowsum=1.000 E|G|^2=2.41 E|G|^4=26.07 E|G|^6=632.15 maxN^0.1=1.87
L=5 N=1000 eta=1.01e-03 rowsum=1.000 E|G|^2=2.32 E|G|^4=28.05 E|G|^6=966.26 maxN^0.1=2.00
```

## 3. Compiled nonempty instances (file lines 727-804, namespace `RBM.Univ.ZeroModeProfileInst`)

| target | instance | data / discharged hypotheses |
|---|---|---|
| `sum_Stilde_row` | `inst_sum_Stilde_row` | d=3, L=4, W=2, lam=1/2, ζ=ouZeta 1; `3 ≤ 4` by `norm_num` |
| `ouVar_eq_Stilde` | `inst_ouVar_eq_Stilde` | t=1, `0 ≤ 1`, diagonal coordinate |
| `ThetaTilde_eq` | `inst_ThetaTilde_eq` | ξ=1/2, ζ=1/100: `‖ξ‖<1`, `0 ≤ ζ ≤ 1`, `3 ≤ 4` |
| `norm_ThetaTilde_sub_le` | `inst_norm_ThetaTilde_sub_le` | 𝔡=κ=1/10 (main branch κ ≤ 2), L=4, lam=1/2 ≤ 10, z=1/2+i/2, ζ=1/2, both σ, u=0, v=e₀ |
| `profTilde_rowDiff` | `inst_profTilde_rowDiff` | sz0, n=0 (`0 < lam`, `lam ≤ 10` by `simp/norm_num [sz0]`), z=1/2+i/2, ζ=1/2 |
| `profPMTilde_zero` | `inst_profPMTilde_zero` | sz0, n=0 |
| `ouTauMax_slack` (+`_pos`) | `inst_ouTauMax`, `inst_ouTauMax_slack` | 𝔠=1/6, 𝔡=1/10, τU=1/1000 ≤ 1/720 |
| `ouDiag_of_ouLL` | `inst_ouDiag` | sz0, τU=1/1000; `UNOULL` (owed pin) stays a hypothesis |
| `ouRow_of_pins` | `inst_ouRow`, `inst_g1` | `UNG1Row`, `UNG2bRow` (owed pins) stay; `inst_g1` discharges `sz0_admissible`, `0 < τU ≤ ouTauMax` |

No `N = 0`, empty index, collapsed window or `False` premise. The hypothesis-free identities `Stilde_zero`,
`Stilde_eq_SBtilde_mul`, `ThetaTilde_zero` and `ouTauMax_pos` have no instance in the file (the ticket's
target 5 does not list them); the auditor compiled them at concrete data (observation O1):
```
$ cat ax.lean | tail -4   # appended after the #print axioms lines
example (i j : Idx 3 4 2) := Stilde_zero 3 4 2 (1/2) i j
example (i j : Idx 3 4 2) := Stilde_eq_SBtilde_mul 3 4 2 (1/2) (1/3) i j
example := ThetaTilde_zero 3 4 (1/2) (1/2 : ℂ)
example : 0 < ouTauMax (1/6) (1/10) := ouTauMax_pos (by norm_num) (by norm_num)
$ lake env lean ax.lean > ax.out 2>&1; echo "exit $?"   ->   exit 0
```

## 4. Build, axioms, scope

```
$ lake build RBM3D.Universality.ZeroModeProfile 2>&1 | grep -E "error|sorry|Build completed|✖"
Build completed successfully (3737 jobs).
$ # ax.lean: #print axioms of the 13 theorems and the 11 instances (24 declarations)
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out ; grep -vE "<same pattern>" ax.out
24
(no other line)
$ git diff main...t/T2276 | grep -nE "^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom "; echo "grep exit $?"
grep exit 1
$ git diff --stat main...t/T2276
 RBM3D/Test/Axioms.lean                  |   5 +-
 RBM3D/Universality/ZeroModeProfile.lean | 806 ++++++++++++++++++++++++++++++++
 2 files changed, 809 insertions(+), 2 deletions(-)
```
Only the two sole writable files; no merged signature touched (new file; registry lines only).
Registry pre-check (root `RBM3D.lean` with `import RBM3D.Universality.ZeroModeProfile` after the `UywKernel`
line, as the hub will do; scratch copy, `lake env lean` after `lake build RBM3D` rebuilt `Test/Axioms`):
```
$ diff RBM3D.lean root_merge.lean
313a314
> import RBM3D.Universality.ZeroModeProfile
$ lake env lean root_merge.lean > root.out 2>&1; echo "exit $?"; grep -nE "error|axiom audit|UNOULL|UNG1Row|UNG2bRow" root.out
exit 0
1:axiom audit: 8025 theorems, 2634 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
107:  RBM.Univ.UNOULL: 3 [no certificate]
108:  RBM.Univ.UNG1Row: 3 [no certificate]
109:  RBM.Univ.UNG2bRow: 2 [no certificate]
```
Without the root import, `lake build RBM3D` fails with `axiom audit: 1 premise(s) … [RBM.Univ.UNOURow]`, as
expected (the deleted `UNOURow` is proved only in the new module, which the hub root-imports at merge).

## 5. Paper deltas

Lean/paper differences: (i) the `d ≥ 3` layer interface (`UNOULL` moment form at `N^{-1+2τ_U}`,
`UNOUEq747` in `QDiff`'s expectation shape at `etaQ(𝔡/3)` with `Θ̃`) — candidate **T2276a** (report (d));
(ii) `ouTauMax = min(𝔠/12, 𝔠𝔡/12, 1/100)` — candidate **T2276b** (report (d)). 2.4 is the paper's
`(prop:ThfadC0)` consequence (no `log L`), restricted as pinned; no other statement difference found. Covered.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)

- O1. No in-file instance for `Stilde_zero`, `Stilde_eq_SBtilde_mul`, `ThetaTilde_zero`, `ouTauMax_pos`
  (no deterministic hypotheses beyond `NeZero`/positivity; not in target 5); compiled by the auditor above.
- O2. Import `RBM3D.Path.Walk` (for `walk_measurable_Gres_apply`) is not in the ticket's import list; it is
  allowed (not `Main.*`/`Graph.*`/root) and stated in the prove report.
- O3. **Merge note for the hub.** `main` now contains T2273 (803bb88), which edits the same `owedProps`
  region; `git merge-tree --write-tree main t/T2276` reports `CONFLICT (content): Merge conflict in
  RBM3D/Test/Axioms.lean`. Bringing in the branch's `Axioms.lean` verbatim would revert T2273's lines.
  The resolution is the ticket's §20 (3) union: delete `UNJak`, `UNOUDiag`, `UNOURow`; keep T2273's
  `UNOUClaims`; add `UNOULL`, `UNG1Row`, `UNG2bRow`. Registered-but-unused entries are reported, not
  errors (`Test/Axioms.lean:586-596`), so the union cannot fail the root check on that account.

## Verdict

Targets 1 (vocabulary), 2.1-2.7, 3 (pins), 4 (`ouDiag_of_ouLL`, `ouRow_of_pins`), 5 (instances): all PASS.
**T2276: PASS.** No dispatcher sign-off needed. The hub must apply the union resolution of O3 when it merges.
