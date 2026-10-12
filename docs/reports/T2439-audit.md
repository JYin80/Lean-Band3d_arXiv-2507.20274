Auditor model: claude-opus-5-5
# T2439 audit (round 1): BA-TL TL2a4, `baTwistGridWTail_holds`

Written Mon Oct 12 05:13:43 UTC 2026 (`date -u`). Branch `t/T2439` at `3ef3862` (base `b16ad61`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2439-audit1` (detached, fresh).

## 1. Diff scope and frozen signatures
```
$ git diff main...t/T2439 --stat
 RBM3D/BA/TwistGridWTail.lean  | 1822 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistGridWTail2.lean | 1334 ++++++++++++++++++++++++++++++
 2 files changed, 3156 insertions(+)
$ git diff main...t/T2439 -- RBM3D/BA/TwistGrid2.lean RBM3D/BA/TwistGrid.lean | wc -l
       0
$ git diff --name-status b16ad61 main | grep RBM3D      # main moved since the base: only new files, no upstream edit
M	RBM3D.lean
A	RBM3D/BA/TwistGridRem.lean
A	RBM3D/BA/TwistGridRem2.lean
A	RBM3D/BA/TwistGridTail.lean
A	RBM3D/BA/TwistGridTail2.lean
```
Only the sole writable files are touched (`RBM3D.lean` is left to the hub). Line counts are 1822 and 1334, both under the 2,000 stop line.

## 2. Statement against the pin (target 1)
```
$ git show main:RBM3D/BA/TwistGrid2.lean | grep -n 'def BATwistGridWTail'
248:def BATwistGridWTail (d : ℕ) : Prop :=
$ git show t/T2439:RBM3D/BA/TwistGridWTail2.lean | grep -n 'theorem baTwistGridWTail_holds'
1234:theorem baTwistGridWTail_holds (d : ℕ) : BATwistGridWTail d := by
$ lake env lean docs/tickets/checks/T2439-check.lean        (audit worktree)
check exit=0 ; error lines: 0
$ example : ∀ d, RBM.BA.BATwistGridWTail d := RBM.BA.baTwistGridWTail_holds     (scratch ax.lean)
(compiles, no message)
```
The theorem's type is the merged pin itself, with no added hypothesis. It holds for every `d` (no `3 ≤ d`) and does not change the pin (diff 0 lines). So the quantifier order, the fixed parameters before `∀ᶠ n`, the `∀ i` over `(σ, a, c₁, c₂)`, the loss `N^{ε'}(…)^{1/2}`, the bound `N^{-D}`, and the weights `Ũ_{u_j,u_k}` are exactly as the pin states them. The proof gives `CK = 3D + 40` (`refine ⟨3 * D + 40, by positivity, ?_⟩`), as the ticket's 1a item (i) asks.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE 'sorry|admit|native_decide|^axiom|^structure|^class|^instance|^opaque|implemented_by|extern' RBM3D/BA/TwistGridWTail{,2}.lean
(no output)
$ grep -nE '^(noncomputable )?(theorem|lemma|def|abbrev) ' … | grep -vE '(TwistGridWTail_|TwistGridWTail2_)'
RBM3D/BA/TwistGridWTail2.lean:1234:theorem baTwistGridWTail_holds (d : ℕ) : BATwistGridWTail d := by
$ grep -n '^import' RBM3D/BA/TwistGridWTail.lean   (TwistGridWTail2 imports only RBM3D.BA.TwistGridWTail)
import RBM3D.BA.TwistGrid2 / GreenCond2 / EMn2BA / Path.DifREP2 / Induction.StepDecompN / Path.QVIdentity / Kernel.Evolution
```
- The ticket adds no new structure or class, so no hypothesis is hidden in a field. Every non-target public name carries a file stem (§3 (E)).
- Every import is a merged module, so there is no cycle. The target does not depend on `BATwistGridRem` or `BATwistGridTail`.
- The proof's eventual conditions all come from the pin's own data:
  - `2^70 ≤ N`, the `Z` budget, and `1/(8κ) ≤ N^ε` follow from `hz.1.2.2.1 : sz.SizeTendsto`.
  - `η_u ≥ 1/(16N)` and `(1−u)⁻¹ ≤ 16N` for `u ≤ t` are derived inline from `EMn2BA_one_sub_T0`, `EMn2BA_mF_data`, `(hz.2 n).2.1`.
  - The proof then closes with `TwistGridWTail2_tail_at`. None of these steps is an assumption.
- The pin has no external hypothesis, so no limit check is owed. The preflight's budget script (prove report `:25-36`) evaluates the budgets at `sz0`, and they hold from `n* = 16`.

Name clashes against current `main` (`98aab64`, which now contains T2437 and T2438):
```
$ (100 public names of the two files) | while read n; do git grep -q -w -F "$n" main -- RBM3D && echo clash; done
clashes on main: 0
```

## 4. Compiled nonempty instance
`TwistGridWTail2.lean` section `Inst` has 4 examples. All compile in the module build (§5):
- (1) `baTwistGridWTail_holds 3` at concrete data:
  - `sz0`, `zSeq`, and `flow_sz0` at `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`;
  - `s ≡ 1/2`, `t ≡ 2/3`, with `s ≤ t` by `norm_num` and `t ≤ T0` by `t0_sz0`;
  - `D = 1` (`one_pos`), `K_n = ⌈N_n^{CK}⌉ + 1` (`≠ 0` by `Nat.succ_ne_zero`, `N^{CK} ≤ K` by `Nat.le_ceil`), and `ε' = 1/10`.

  It ends with `H2.exists`.
- (2) The same instance with the full conclusion kept: `∃ CK n, 0 ≤ CK ∧ ∀ i, Pp{…} ≤ ofReal (N^{-1})`. `D = 1` appears as `(-1 : ℝ)`.
- (3) `baTwistGridAssemble_holds 3 11 … hRem hTail (baTwistGridWTail_holds 3)`.
- (4) Example (3) applied at the same BA datum.

Every deterministic hypothesis is discharged at nondegenerate data: nonempty lattice, `s < t`, `D > 0`, `K_n ≥ 1`. Only the other gates' pins `BATwistGridRem 3 11` and `BATwistGridTail 3` (T2437, T2438) stay as hypotheses, and only in examples (3) and (4). There is no `False` premise, no `N = 0`, and no collapsed window. `K_n` is huge, but it is the pin's own hypothesis `N^{CK} ≤ K n`, passed as a function and never evaluated (the pattern of `TwistGrid2:333-343` that the ticket prescribes).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.TwistGridWTail RBM3D.BA.TwistGridWTail2 2>&1 | tail -1 ; echo exit=$?
Build completed successfully (4039 jobs).
exit=0
$ grep -c error build.log
0
$ grep -E '^(warning|error).*TwistGridWTail' build.log      (only longLine warnings in the module docstrings)
warning: RBM3D/BA/TwistGridWTail.lean:17:100: This line exceeds the 100 character limit, please shorten it!
… (lines 17-22, 26 of file 1; 11-13 … of file 2; no other kind)
$ lake env lean ax.lean     (Lean.collectAxioms over every constant `RBM.BA.TwistGridWTail*` and the target)
public decls checked: 104; union of axioms: [Quot.sound, Classical.choice, propext]; non-standard: []
'RBM.BA.baTwistGridWTail_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The hub runs the full `lake build` (`#assert_rbm_axioms`) at merge. Since the base, `main` has gained only new files, and none of the 100 public names occurs on `main`.

## 6. Paper deltas
- The target proves the merged pin exactly. It adds no new Lean/paper statement difference.
- `T2439a` (proof device: Azuma/Doob in place of BDG for clause (iv), with explicit `C' = D + 14`, `CK = 3D + 40`) is proposed in prove report (d) `:163`.
- As the ticket item 4 says, the mismatch between the pin's weights `Ũ_{u_j,u_k}` and the exact 4 (a) weights stays with TL2d (T2428 (a″) decision 4). It is not a gap of this ticket.
- Coverage is complete.

## 7. Ticket items
| item | result |
|---|---|
| 1 target `baTwistGridWTail_holds (d : ℕ) : BATwistGridWTail d`, every `d` | PASS (§2-§5) |
| 2 helpers shared with T2438 | copied with stem `TwistGridWTail_`; `TwistGridTail.lean` was not on `main` at 1b start (report `:92`) |
| 3 instance at `sz0`, `s ≡ 1/2`, `t ≡ 2/3`, `D = 1`, `K_n = ⌈N^{CK}⌉+1`, `ε' = 1/10`, fed to `baTwistGridAssemble_holds 3` | PASS (§4) |
| 4 registry | none, as pinned |
| check file; `∀ d` example; axioms; no sorry; diff scope; ≤ 2,000 lines/file | PASS |

## 8. Observations (no RETURN)
- O1. The split between files differs from the ticket's suggestion: the coarse grid and the `Z` part are in `TwistGridWTail2`, not `TwistGridWTail`. Both files stay under 2,000 lines and the import order is as pinned. No statement is affected.
- O2. The proof does not use the ticket-listed `BATheta_conj`, `BAMss_pm_eq`, `BATheta_pm_eq`. The conjugation `Ũ^{(σ̄)} = conj Ũ^{(σ)}` is proved privately (`TwistGridWTail_twU_conj`, file 1 `:83`) through `BATheta_isUnit` and the ring map `starRingEnd`. The statement is unaffected.
- O3. Item (v) of section (a) (predicted lines per file) was not given (report `:80`). The landed counts are 1822 and 1334, so this is a report-only gap.
- O4. The prove report's axiom count says 100 declarations; this audit's script counts 104 constants under the stem filter, which includes auxiliary equation lemmas. Both runs found only the standard three axioms.

## Verdict
Target 1 `baTwistGridWTail_holds`: **PASS**. The instance passes, the build passes, the axioms are the standard three, the diff stays in scope, and paper-delta coverage is complete. No dispatcher sign-off is needed.
