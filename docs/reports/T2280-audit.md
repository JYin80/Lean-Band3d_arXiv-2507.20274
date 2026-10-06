Auditor model: claude-opus-5-5

# T2280 audit (UN-23 `Universality/Uyw`), round 1

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2280-audit1`, detached at `t/T2280` = `2ab9373`; merge-base with main `7a8a4eb`.
Written `Tue Oct  6 10:32:58 UTC 2026` (from `date -u`).

## 1. Statements against the pin (check file §2.1-§2.2, §3)

Script: the whole of `Uyw.lean` (without its `#print axioms` lines) followed by sections 2-3 of
`docs/tickets/checks/T2280-check.lean` (`namespace T2280Check` … up to `## 4`), then one `example` per pinned statement.
The examples apply the library's declarations, private ones included, at the check-file `def`s, so this is a
definitional-equality diff that Lean checks:
```
$ grep -n '^example' UywAuditCheck.lean | sed 's/:=.*//'
1085:example : T2280_unUyw_of_ouClaims      (:= unUyw_of_ouClaims)
1086:example : T2280_uywRow                 (:= uywRow)
1087:example : T2280_jakUywRow              (:= jakUywRow)
1088:example : T2280_inst_row               (:= UywInst.inst_row)
1089:example : T2280_inst_uywRow            (:= UywInst.inst_uywRow)
1090:example : T2280_inst_unUyw            (:= UywInst.inst_unUyw)
1091:example : T2280_inst_window            (:= UywInst.inst_window)
1092:example : T2280_Uyw_o_le               (private, eta-expanded application)
1093:example : T2280_Uyw_good_total_le      (private)
1094:example : T2280_Uyw_crude_total_le     (private)
1095:example : T2280_Uyw_queBound_eq        (private)
1096:example : T2280_Uyw_fixed_time         (:= @Uyw_fixed_time; library has `Type*`, check `Type`)
$ lake env lean UywAuditCheck.lean > check.out 2>&1; echo "lean exit=$?"; grep -c error check.out
lean exit=0
0
```
(The only messages are `unusedVariables` warnings on the eta-binders of examples 1092-1095.)

Target 3 is the merged row verbatim: `theorem jakUywRow : UNJakUywRow` (Uyw.lean:881). The `UNUyw` integrand
(Pins.lean:712-716 on the branch: `(Gres … (z i) b₁ * Gres … (z i) b₁) x y * scirc … x y * (Gres … (z j) b₂ * Gres … (z j) b₂) y x`)
is the conclusion of the check-pinned `Uyw_fixed_time` at `Hr = ouMat (UNModel.band sz) n t`, `u₁ = z i`, `u₂ = z j`.
The proof applies it at exactly that point (Uyw.lean:846-852). Quantifier order: fixed `d, 𝔠, 𝔡, sz, κ, E, nf, τU`
and then `C₀ ε` come before `∀ᶠ n`. The eventual conditions `ev1`-`ev5` (Uyw.lean:814-836) depend only on these fixed
parameters. The exponent is `c' = 𝔠 * 𝔡 / 30` with `C = 3nf+16` and `τ₀ = min τ₁ (1/4)`, as pinned.

## 2. Hidden hypotheses, vacuity, cycles

- Every public theorem's hypotheses are in its signature (§1). `Sizes.Admissible` is destructured as
  `⟨h𝔠, h𝔡, hsize', hband, hWO⟩` (Uyw.lean:799), the merged MD-1 predicate. The new file adds no structure.
- Premises that are not discharged: `UNOUQUE`, `UNOUDiag` (target 1) and `UNLocAvgBand`, `UNOUClaims` (targets 2-3,
  as in the merged `UNJakUywRow`). All are other gates' pins. They are registered owed, or concluded by
  `ouDiag_of_ouLL` from the owed `UNOULL`. None is external, so no limit check is needed.
- Imports (Uyw.lean:6-7): only `RBM3D.Universality.Jak` and `RBM3D.Universality.UywKernel`, both merged. No cycle.
- The pin index `i ≠ j` is bound as `_hij` and not used (Uyw.lean:841), which the ticket's §29 (7) allows.

## 3. Compiled nonempty instances

The instances are in `RBM.Univ.UywInst`, Uyw.lean:900-958, and compile (§1 and §4). They use `sz0` (`d = 3`) with the
admissibility proof `UNInst.sz0_adm`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/2`, `E = 1` (`|1| ≤ 3/2`) and `nf = 2`.
- `inst_row` / `inst_uywRow` apply `jakUywRow` / `uywRow`. `inst_unUyw` applies `unUyw_of_ouClaims` for every
  `τU ∈ (0, 1/4]`.
- Every deterministic hypothesis (`3 ≤ d`, `Admissible`, `0 < κ`, `|E| ≤ 2-κ`) is discharged by `le_rfl`, `sz0_adm`
  or `norm_num`.
- `inst_window` shows that the premises of `UNUyw` hold at every `n` and every `τU > 0`, so the endpoint is
  nondegenerate: `z 0 = 1 + i/N` and `z 1 = 1 + 1/N + i/N` are distinct points in `InWindow sz0 1 1 τU n`, with
  `(0 : Fin 2) ≠ 1` and `0 ≤ ouTStar`.
- `N = Nsz sz0 n ≥ 1` is proved, not assumed (Uyw.lean:934-938). There is no `N = 0`, no empty index, no collapsed
  window and no `False` premise. The pins of other gates stay hypotheses, as the ticket allows.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Universality.Uyw 2>&1 | grep -E "Uyw.lean.*depends on axioms|error|Build completed"
info: RBM3D/Universality/Uyw.lean:960:0: 'RBM.Univ.unUyw_of_ouClaims' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:961:0: 'RBM.Univ.uywRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:962:0: 'RBM.Univ.jakUywRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:963:0: 'RBM.Univ.UywInst.inst_row' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:964:0: 'RBM.Univ.UywInst.inst_uywRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:965:0: 'RBM.Univ.UywInst.inst_unUyw' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:966:0: 'RBM.Univ.UywInst.inst_window' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3335 jobs).
```
The only warnings are `longLine` warnings (Uyw.lean:13-38, docstring header; the file sets `linter.style.longLine false` after that).
```
$ grep -nwE 'sorry|admit|native_decide|axiom' RBM3D/Universality/Uyw.lean     (no output)
$ git diff --name-only main...t/T2280
RBM3D/Test/Axioms.lean
RBM3D/Universality/Uyw.lean
$ for n in unUyw_of_ouClaims uywRow jakUywRow UywInst; do git grep -nw $n main -- RBM3D RBM3D.lean | wc -l; done
0 0 0 0
```
The diff touches only the two sole writable files. No merged file is changed, so no frozen signature changes. All
unpinned helpers are `private` with the `Uyw_` prefix (grep `^private theorem Uyw_`, Uyw.lean:54-497).

**Registry** (`git diff main...t/T2280 -- RBM3D/Test/Axioms.lean`): the lines `UNUyw` and `UNJakUywRow` are deleted
from `owedProps`. The comment on the `UNOUClaims` line is changed to the ticket's text ("owner: `ouRow_of_pins`
(`ZeroModeProfile.lean:719`) + the consumed inputs `UNG1Row`, `UNG2bRow`"). Nothing else changes.
```
owedProps count: merge-base 7a8a4eb = 148, t/T2280 = 146   (−2)
```
The registry pre-check reproduces the hub's merge state: `RBM3D.lean` with `import RBM3D.Universality.Uyw` inserted
after its last import line, compiled as a scratch file (no source edited):
```
$ diff RBM3D.lean RootWithUyw.lean
320a321
> import RBM3D.Universality.Uyw
$ lake env lean RootWithUyw.lean > root.out 2>&1; echo "lean exit=$?"; grep error root.out
lean exit=0
```
Without the root import, `lake build RBM3D` on the branch reports
`axiom audit: 1 premise(s) … [RBM.Univ.UNJakUywRow]` at `RBM3D.lean:323`. This is expected: the hub adds the root
import at merge (§3 (A) 4), and with it the assert passes (above). The prove report records the same (prove.md:153).

## 5. Paper deltas

- The Lean/paper differences of the pin itself (`c' = 𝔠𝔡/30` at `d ≥ 3`, where `ℙ(𝓑)` binds; recomputing
  `C = 3nf+16`) are covered by D386 (T2162e) in `docs/paper-deltas.md`:1345 on main.
- The pair-block form `2d+1` is covered by D582 (T2271a).
- This ticket proposes T2280a (design table: `C = 3nf+16`, `τ₀ = min τ₁ (1/4)` confirmed; `20 → 4(2d+1)`,
  `c ≤ 1/2 → c ≤ 1`; registry −2). It reports no T2280b (prove.md:262-263).
- The new theorems state the merged pins verbatim (§1), so they add no new statement difference.

## 6. Observations (no effect on the verdict)

- Main has moved to `596a83a` (T2277 merged; its change to `Axioms.lean` is another `owedProps` line). The hub
  merges the registry change as the union (ticket merge note, §20 (3)).

## Verdict

| target | statement | hidden/vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `unUyw_of_ouClaims` | = check 2.1 | none | `inst_unUyw` + `inst_window` | ok | D386, T2280a | **PASS** |
| `uywRow` | = check 2.1 | none | `inst_uywRow` | ok | D386, T2280a | **PASS** |
| `jakUywRow : UNJakUywRow` | = merged pin | none | `inst_row` | ok | D386, T2280a | **PASS** |
| instances (check 2.2) | = check 2.2 | — | — | ok | — | **PASS** |

**T2280: PASS.** No dispatcher sign-off is needed.
