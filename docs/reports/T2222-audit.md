Auditor model: claude-opus-5-5

# T2222 audit (round 1) — S6-06 `Induction/ExpEtermsA.lean`, proves `STExpLKLKHi`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2222-audit1` (detached at `t/T2222` = e96b222); finished Mon Oct  5 22:52:59 UTC 2026 (`date -u`).
Scratch: `scratchpad/T2222/` (`audit_eq.lean`, `pre2.lean`, `pre_base.lean` and their `.out`).

## 1. Scope of the diff
```
$ git diff --stat main...HEAD
 RBM3D/Induction/ExpEtermsA.lean | 705 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   1 -
$ git diff main...t/T2222 -- RBM3D/Test/Axioms.lean | grep '^[-+][^-+]'
-   `RBM.Gauss.Sizes.STExpLKLKHi, -- `6:58-62` (L-K)x(L-K) drift bound: S6-06; S6-01 (T2204, DECISIONS §67: owed)
$ git diff main -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/Step6Kit.lean RBM3D/Induction/KDecay.lean | wc -l
0
$ git show main:RBM3D/Test/Axioms.lean | grep -n STExpLKLKHi     # line still on main (e.g. 3b51ca4); STExpLKLKHiConcl stays
230:   `RBM.Gauss.Sizes.STExpLKLKHi, -- ... owed)
322:   `RBM.Gauss.Sizes.STExpLKLKHiConcl, -- ... structural)
```
Only the two sole writable files; the Axioms diff is exactly the one owed line; no frozen/merged signature touched.

## 2. Build, hygiene, axioms
```
$ lake build RBM3D.Induction.ExpEtermsA
Build completed successfully (3847 jobs).
$ grep -cwE 'sorry|admit|native_decide' RBM3D/Induction/ExpEtermsA.lean ; grep -nw axiom RBM3D/Induction/ExpEtermsA.lean
0
(no output)
$ grep -nE '^(private )?(theorem|lemma|def|abbrev|structure|class|instance)' RBM3D/Induction/ExpEtermsA.lean | cut -c1-60
54 theorem expLK_window_le | 98 theorem expLK_latticeSum | 126 private theorem expLK_norm_Kloop_le
146 theorem expLK_env | 176 private theorem expLK_Bctl_ge | 202 private theorem expLK_eta_inv_le
245 theorem expLK_env_poly | 294 private theorem expLK_det_core | 385 theorem expLK_prec
461 private theorem expLK_first_moment | 492 theorem expLK_expect | 594 theorem STExpLKLKHiConcl_of_LKU
607 theorem stExpLKLKHi_holds | 623-699 theorem inst_* (11, namespace RBM.Gauss.Step6Inst)
```
No new `def`/`structure` (no hidden hypothesis fields); unpinned helpers are `private` and prefixed `expLK_` (§3 (E)).
`#print axioms` (in `audit_eq.lean`, `lake env lean`, exit 0), all 19 public declarations:
```
'RBM.Gauss.Sizes.expLK_window_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_latticeSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_env' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_env_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expLK_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STExpLKLKHiConcl_of_LKU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpLKLKHi_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expLKLK_I_holds' / _II_holds / _III_holds / inst_skeleton6III_LK / inst_expLK_latticeSum /
 inst_expLK_env / inst_expLK_window / inst_expLK_env_poly / inst_expLK_prec / inst_expLK_expect / inst_expLKLK_of_LKU:
 11 lines, each "depends on axioms: [propext, Classical.choice, Quot.sound]"
```

## 3. Statements against the pin (script, compiled)
`audit_eq.lean` = the check file's imports + `import RBM3D.Induction.ExpEtermsA` + check sections 1–2 verbatim, then
one `example : RBM.Gauss.Sizes.T2222Check.X := @RBM.Gauss.Sizes.X` for each of the 8 section-2 pins, `example (d : ℕ) :
STExpLKLKHi d := stExpLKLKHi_holds d`, and for each of the 6 section-3 statements `example : <statement copied by script
from the check file> := @RBM.Gauss.Step6Inst.<name>`.
```
$ grep -c '^example' audit_eq.lean
15
$ lake env lean audit_eq.lean > audit_eq.out; echo exit $?
exit 0
$ grep -ciE 'error|warning|sorry' audit_eq.out
0
```
So every target has exactly the dispatcher-pinned type (definitional check, no rewriting). The pin itself is the merged
`STExpLKLKHi d := STIngR6 d STDriftHi (fun sz E s t => STExpLKLKHiConcl sz E s t)` (`Step6Pins.lean:301`, diff empty), and
`stExpLKLKHi_holds (d : ℕ) : STExpLKLKHi d` has **no hypotheses**: it is the general target, not a special case or adapter.
Against the paper `6_Step6_two_loop.tex:58-62` (`(eq:Exp(L-K)1)`): `𝔼ℰ^{(L-K)×(L-K)}_{u,σ,a} ≺ (1-u)⁻¹(W^{-d}B_{u,0})^{11/5}`;
merged `STExpLKLKHiConcl` = `Prec` over `STIdx2 sz s t` (all `u ∈ [s,t]`, `σ`, `a`) of `‖STExpELKLK‖` against
`(1-u)⁻¹ * Bctl^(11/5)`: exponent `11/5`, the `(1-u)⁻¹` loss, uniformity in `u` and index ranges match; constants fixed before `∀ᶠ n`
(`𝔠_d = 1/100`, then `∀ 𝔠 sz z`, conclusion `Prec`). The paper's window `1-u ≥ ilambda²/L^d` is the premise `STDriftHi`, which
the proof does not use (`intro … hHi …`, `hHi` unused) — the Lean result is at least as strong as the paper's; covered by candidate T2222a.
Inputs used (from the proof term, `ExpEtermsA.lean:607-613`, `:594-602`): `STFlow`, `0 ≤ s`, `t ≤ lemT z`, `STLKU`, `STGdecayW … 0`
— exactly the pin's premises `(Eq:L-KGt-flow)` and `(Eq:Gdecay_flow)` that `6:58` cites; `STGdecayW` is used with `Cd = 0` as pinned
and at `D = 2/𝔠` (its `∀ D > 0` binder), `STLKU` at `k = 2`.
Helper targets (`expLK_window_le`, `expLK_latticeSum`, `expLK_env`, `expLK_env_poly`, `expLK_prec`, `expLK_expect`,
`STExpLKLKHiConcl_of_LKU`): types = check section 2 (above); hypotheses are deterministic side conditions (`2 ≤ d`, `0 ≤ lam`, `u < 1`,
`|E| < 2`, `Bandwidth`, `SizeTendsto`) or the two stochastic premises of the pin — none is stronger than the pin supplies (the assembly
discharges each from `STFlow`, `st5_t_lt_one`, `st6_flowE_lt_two`, `st6_lam_pos`).
Statement verdict: all 8 targets PASS.

## 4. Vacuity, hidden hypotheses, cycles
- No new structure/def; `Sizes`, `STFlow`, `Prec` are merged and unchanged.
- No cycle: `stExpLKLKHi_holds` takes no hypothesis; its axioms are the three standard ones, so no owed `Prop` is assumed (an owed pin
  would appear as a hypothesis, there is none). `STLKU`, `STGdecayW` are premises *inside* the pin (Steps 4, 5 of `lem:main_ind`), not
  external hypotheses of the theorem; no new external input (DECISIONS: nothing to authorize).
- Non-vacuity of the conclusion: `STExpLKLKHiConcl` is a genuine `Prec` bound (the right side `(1-u)⁻¹ B^{11/5} > 0`, `STBctl_pos`);
  the proof derives it from the premises rather than from an inconsistency (route: window + merged lattice sum `KDecay_sum_tailT_le`
  + first moment off the union of failure events).
- Registry (§20): root-import pre-check, scratch file = every `import` line of `RBM3D.lean` (+/− the new module) + `#assert_rbm_axioms`:
```
$ lake env lean pre_base.lean   # without ExpEtermsA (branch Axioms.lean, line deleted)
pre_base.lean:262:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of …
  [RBM.Gauss.Sizes.STExpLKLKHi]
exit 1
$ lake env lean pre2.lean       # with import RBM3D.Induction.ExpEtermsA
premises found by scanning: 125 (borrowed 1, owed 93, structural 25, refuted 6).
registry: 2 borrowed + 144 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [...]
exit 0
$ grep -oE 'STExpLKLKHi[A-Za-z_]*' pre2.out | sort | uniq -c
   1 STExpLKLKHiConcl
```
`STExpLKLKHi` is absent from the owed ledger and the carry-nothing list (only the structural `STExpLKLKHiConcl` remains, as the ticket
requires). As expected, `lake build` (whole library) on the branch **without** the root import fails with the same `axiom audit` error
(`RBM3D.lean:264:0`); the hub must add `import RBM3D.Induction.ExpEtermsA` in the same merge commit as the `Axioms.lean` deletion
(CLAUDE.md §3 (A) step 4) — merge note, not a defect.

## 5. Compiled nonempty instances (same file, compiled in the module build)
| endpoint | instance | data | open hypotheses |
|---|---|---|---|
| `stExpLKLKHi_holds` | `inst_expLKLK_I/II/III_holds`, `inst_skeleton6III_LK` | merged `szB, zB` on `[7/8,15/16]`, `[15/16,31/32]`; `sz0, z0, sInst, tInst` | stochastic premises inside `InstIng6Concl`; other gates' pins `LWtermEXP`, `STExpDuhamelZ`, `STExpIntIII` |
| `expLK_window_le` | `inst_expLK_window` | `sz0`, `n=0`, `E=u=1/2`, `seqHflow`, `σ=(+,-)`, `a=0`, `M = Σ_x ‖·‖` | none |
| `expLK_latticeSum` | `inst_expLK_latticeSum` | `sz0`, `n=0` (`L=4, W=32, lam=1/64`), `u=1/2`, `a=0` | none (`2≤3`, `0≤lam` by `sz0_values`, `1/2<1`) |
| `expLK_env` | `inst_expLK_env` | `sz0`, `n=0`, `E=u=1/2` | none |
| `expLK_env_poly` | `inst_expLK_env_poly` | `sz0`, `z0` (`flow_z0`), `t = tInst` | none |
| `expLK_prec`, `STExpLKLKHiConcl_of_LKU` | `inst_expLK_prec`, `inst_expLKLK_of_LKU` | `sz0, z0, sInst, tInst`, `𝔠=1/6` | `STLKU`, `STGdecayW … 0` (Steps 4, 5) |
| `expLK_expect` | `inst_expLK_expect` | same, `Kenv = 6` via `inst_expLK_env_poly` | the `Prec` input |
Every deterministic hypothesis is discharged at concrete data (`norm_num`, `sz0_tendsto`, `sz0_bandwidth`, `sz0_WO`, `flow_z0`,
`sixteenth_le_lemT`); no `N = 0`, empty index, collapsed window or `False` premise (`L = 4`, `|Z_4^3| = 64`, `0 ≤ s < t < 1`).
The time windows are the merged nondegenerate ones (`7/8 < 15/16`, `15/16 < 31/32`, `sInst < tInst`). PASS.

## 6. Paper deltas
Lean/paper differences found: (1) the window `1-u ≥ ilambda²/L^d` of `6:58` is a premise but unused (the result holds for all
`u < 1`); (2) the `≲` of `6:61` is realised by the explicit constant `KDecay_tailC d` (+1), absorbed into `N^τ` eventually.
Both are proposed in the prove report (d) as `T2222a`, `T2222b`. No other statement difference (the pin is merged and unchanged).
Coverage: PASS.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. `inst_expLK_expect` keeps the derived `Prec` as a hypothesis; the composed chain with only the Step-4/5 premises open is
  `inst_expLKLK_of_LKU`, so the endpoint is still covered.
- O2. Prove report (a) row 3 gives `C_∞(3) = 403108609`; report (b) narrative states the zero-mode absorption used is
  `N⁻¹ ≤ B^{1/5}` (weaker than (a) row 6), which is sufficient; no statement depends on either.

## Verdict
| target | statement | vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `expLK_window_le` | = pin | ok | ok | ok | — | PASS |
| `expLK_latticeSum` | = pin | ok | ok | ok | T2222b | PASS |
| `expLK_env` | = pin | ok | ok | ok | — | PASS |
| `expLK_env_poly` | = pin | ok | ok | ok | — | PASS |
| `expLK_prec` | = pin | ok | ok | ok | — | PASS |
| `expLK_expect` | = pin | ok | ok | ok | — | PASS |
| `STExpLKLKHiConcl_of_LKU` | = pin | ok | ok | ok | — | PASS |
| `stExpLKLKHi_holds` (merged pin `STExpLKLKHi`) | = pin, unconditional | ok | ok | ok | T2222a | PASS |
| instances (target 4) | = check section 3 | — | — | ok | — | PASS |

**T2222: PASS.** No dispatcher sign-off needed. Hub: commit the `Axioms.lean` deletion together with the root import
`import RBM3D.Induction.ExpEtermsA` (after the last `import` line of `RBM3D.lean`); the full `lake build` fails without it.
