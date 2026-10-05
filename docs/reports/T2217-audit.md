Auditor model: claude-opus-5-5

# T2217 audit (round 1): S6-03 `Induction/ExpAvg`, prove `STImproveExpAver`

Written Mon Oct  5 22:08:52 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2217-audit1`,
detached at `t/T2217` = `f8cf545` (merge-base with `main`: `122f299`; `main` = `63d62b4`).
Scratch: scratchpad `T2217/audit_{eq,ax,pre}.lean` and their `.out`.

## 1. Diff scope and frozen files
```
$ git diff --stat main...t/T2217
 RBM3D/Induction/ExpAvg.lean | 1019 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    1 -
$ git diff main...t/T2217 -- RBM3D/Test/Axioms.lean    (the only changed line)
-   `RBM.Gauss.Sizes.STImproveExpAver, -- `6:12-17` improved averaged bound per time: S6-03; S6-01 (T2204, DECISIONS §67: owed)
$ git diff main...HEAD --stat -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/Step6Kit.lean | wc -l
       0
$ grep -n -E "sorry|admit|native_decide|^axiom|^\s*axiom |set_option.*maxHeartbeats|@\[implemented_by|extern" RBM3D/Induction/ExpAvg.lean
(no output)
$ grep -n "^import" RBM3D/Induction/ExpAvg.lean
6:import RBM3D.Induction.Step6Kit      7:import RBM3D.Induction.ConArgDet   8:import RBM3D.Gauss.LoopGenerator
9:import RBM3D.Gauss.DominationAt      10:import RBM3D.Evolution.XiPins     11:import RBM3D.Propagator.Pins
$ grep -nE "^(private )?(noncomputable )?(def|structure|class|abbrev)" RBM3D/Induction/ExpAvg.lean
942:private def instLoop (b : Zd 3 4) (ω : Ω 3 4 32) : ℂ :=
```
Exactly the two sole writable files; `Axioms.lean` diff is the one prescribed deletion; the file defines no `Prop`,
no structure (no hypothesis can hide in a field); imports are the check file's, not `RBM3D`.
Name clashes on `main` (`git grep -w -c <name> main -- 'RBM3D/*.lean' RBM3D.lean`, all 26 public theorems): 0 hits each.

## 2. Statements against the pins (check file section 2 and 3, compiled)
Script: imports of `docs/tickets/checks/T2217-check.lean` + `import RBM3D.Induction.ExpAvg` + its sections 1–2 verbatim
+ one `example : RBM.Gauss.Sizes.T2217Check.X := @RBM.Gauss.Sizes.X` per pin `X` (11) + the pin example + section 3
with each `example : Prop := S` rewritten to `example : S := @RBM.Gauss.Step6Inst.<inst>` (8).
```
$ grep -n "^example" audit_eq.lean | cut -c1-110
284:example : RBM.Gauss.Sizes.T2217Check.expAvg_stein := @RBM.Gauss.Sizes.expAvg_stein
285:example : RBM.Gauss.Sizes.T2217Check.expAvg_selfcons := @RBM.Gauss.Sizes.expAvg_selfcons
286:example : RBM.Gauss.Sizes.T2217Check.expAvg_norm_solve := @RBM.Gauss.Sizes.expAvg_norm_solve
287:example : RBM.Gauss.Sizes.T2217Check.expAvg_expErr_le := @RBM.Gauss.Sizes.expAvg_expErr_le
288:example : RBM.Gauss.Sizes.T2217Check.expAvg_Bctl_ge := @RBM.Gauss.Sizes.expAvg_Bctl_ge
289:example : RBM.Gauss.Sizes.T2217Check.expAvg_eta_inv_le := @RBM.Gauss.Sizes.expAvg_eta_inv_le
290:example : RBM.Gauss.Sizes.T2217Check.expAvg_moment := @RBM.Gauss.Sizes.expAvg_moment
291:example : RBM.Gauss.Sizes.T2217Check.expAvg_integral_conj := @RBM.Gauss.Sizes.expAvg_integral_conj
292:example : RBM.Gauss.Sizes.T2217Check.expAvg_u_zero := @RBM.Gauss.Sizes.expAvg_u_zero
293:example : RBM.Gauss.Sizes.T2217Check.STExpAvgAt_of_LWAvgLaw := @RBM.Gauss.Sizes.STExpAvgAt_of_LWAvgLaw
294:example : RBM.Gauss.Sizes.T2217Check.stImproveExpAver_holds := @RBM.Gauss.Sizes.stImproveExpAver_holds
295:example (d : ℕ) : RBM.Gauss.Sizes.STImproveExpAver d := RBM.Gauss.Sizes.stImproveExpAver_holds d
304:example : ∀ (hA : LWAvgLaw sz0 (STflowE z0) tInst), STExpAvgAt sz0 (STflowE z0) tInst :=
308:example :   313:example :   319:example :   326:example :   332:example :   338:example :   343:example :
$ lake env lean audit_eq.lean > audit_eq.out 2>&1; echo exit=$?
exit=0
$ grep -c "error" audit_eq.out
0
```
(only `unusedVariables` warnings on the section-3 binder names `hA`, which come from the check file's text.)
All 11 statements are definitionally the dispatcher's pinned text (closed `Prop`s, `@`-terms, no coercion), and the
merged pin `STImproveExpAver` (`Step6Pins.lean:191`, unchanged) is proved with no extra hypothesis. Mathematics:
pin = `lem:improve_exp_aver` (`6:12-21`) per time sequence `u` (paper: uniformly in `u ∈ [s,t]`; covered by D487),
both charges (paper: charge `+`; charge `-` is the conjugate: a strengthening). `STExpAvgAt_of_LWAvgLaw` drops the
premise `STLK` and `0 < 𝔡` (the latter is inside `STFlow`): stronger than the pin, as the ticket designs.
Constants: `expAvg_norm_solve`/`expAvg_expErr_le` give `∃ C` after `d, Λ, κ` and before `L, W, g, E, u, K`
(binder order compiled above), i.e. `C = C(d, Λ, κ)`, no `log L` (§29).

## 3. Vacuity, hidden hypotheses, cycles
- `stImproveExpAver_holds` (file `:879-881`) is `STExpAvgAt_of_LWAvgLaw sz hd hκ hε hz u hu0 hut hLW`; `_hLK` unused.
- No new `def`/`structure` except the private instance abbreviation `instLoop`; hypotheses are in the signatures only.
- Dependencies: imports are merged modules on `main` (check file section 1 compiled in `audit_eq.lean`, exit 0); no
  file of this ticket is imported by them (new module, not in `RBM3D.lean`): no cycle.
- External/stochastic premise `LWAvgLaw` (`(Gt_avgbound_flow)`) is a premise of the paper's lemma itself; concrete
  limit check in prove report (a)(ii) (`Bctl(1/16)·W^d → 16/15`, `Bctl·N → ∞`). Deterministic premises are satisfiable:
  `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (merged) and `sz0_ht` discharge them in §4 below.

## 4. Compiled nonempty instances (file `:885-1019`, namespace `RBM.Gauss.Step6Inst`)
| endpoint | instance | data / discharged | left as hypothesis |
|---|---|---|---|
| `STExpAvgAt_of_LWAvgLaw` | `inst_expAvgAt_holds` | `sz0, z0, tInst`, `3≤3`, `0<1/10`×2, `flow_z0`, `0≤tInst n`, `sz0_ht` | `LWAvgLaw` |
| `stImproveExpAver_holds` | `inst_improveExpAver_holds`, `inst_expAvgU_holds`, `inst_skeleton6{I,II,IV}_avg` | merged instance data via `inst_improveExpAver`, `inst_expAvgU`, `inst_skeleton6I/II/IV` with `hAvg := stImproveExpAver_holds 3` | `LWAvgLaw`, `STLK`, `STStep2Core`, `STLKU`, other gates' pins `STExp*`, `LWtermEXP` |
| `expAvg_eta_inv_le` | `inst_eta_inv_le` | `sz0, z0`, `flow_z0` (eventual, as ticket) | — |
| `expAvg_u_zero` | `inst_expAvg_u_zero` | `sz0`, `n=0` (`L=4, W=32`), `E=1/2`, `a=0` | — |
| `expAvg_stein`, `_selfcons`, `_norm_solve`, `_expErr_le`, `_Bctl_ge`, `_moment`, `_integral_conj` | `inst_expAvg_*` (7) | `d=3, L=4, W=32, g=1/64, u=1/16, E=1/2` (`z=i` for Stein), `norm_solve` at `x≡1, y≡1-u m², K=2` (equation proved by `ring` from the column sum) | `LWAvgLaw` (moment only) |
None degenerate: `N = 2097152` at `n = 0`, `Zd 3 4` has 64 points, `0 < 1/64 ≤ Λ`, `u = 1/16 ∈ [0,1)`, `|E| = 1/2`.
All compile (module build below; the 8 ticket instances also re-elaborated against section 3 in §2).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.ExpAvg 2>&1 | grep -E "error|ExpAvg|Build completed"
✔ [3851/3851] Built RBM3D.Induction.ExpAvg (6.6s)
Build completed successfully (3851 jobs).
$ lake env lean RBM3D/Induction/ExpAvg.lean ; echo exit=$?      (fresh elaboration, warnings only in other files filtered)
exit=0
$ lake env lean audit_ax.lean > audit_ax.out   # #print axioms of the 11 Sizes theorems and the 15 Step6Inst theorems
$ grep -c "depends on axioms" audit_ax.out
26
$ grep "depends on axioms" audit_ax.out | grep -v "\[propext, Classical.choice, Quot.sound\]" | wc -l
       0
```
Registry pre-check (§20 (2)): `audit_pre.lean` = `RBM3D.lean` of the branch with `import RBM3D.Induction.ExpAvg`
inserted after the last `import` (line 258), `#assert_rbm_axioms` last (line 261).
```
$ lake build      # branch as committed (root without the ExpAvg import)
✖ [4019/4020] Building RBM3D (6.3s)
error: RBM3D.lean:260:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`:
$ lake env lean audit_pre.lean > audit_pre.out 2>&1; echo exit=$?
exit=0
axiom audit: 6460 theorems, 2222 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 95, structural 25, refuted 6)
registry: 2 borrowed + 146 owed + 80 structural + 7 refuted
$ grep -c STImproveExpAver audit_pre.out
0
$ for r in main HEAD; do git show $r:RBM3D/Test/Axioms.lean | grep -c "^\s*\`RBM.*STImproveExpAver"; done
1
0
```
The error without the import is expected (the pin becomes unclassified until the hub adds the root import at merge,
CLAUDE.md §3 (A) step 4); with the import the registry check passes. `main` has advanced past the merge-base
(`5d313ca` T2215, `63d62b4` T2205); the hub's full `lake build` at merge covers the combination.

## 6. Paper deltas
- Per-time form of `lem:improve_exp_aver` (paper: uniform in `u ∈ [s,t]`): D487 (T2191c), present
  (`docs/paper-deltas.md:1446`), cited in prove report (d).
- Lean adds charge `-` and drops the premise `(Eq:L-KGt-flow)` in `STExpAvgAt_of_LWAvgLaw`: strengthenings of the
  merged pin, not differences of `STImproveExpAver` (text unchanged); no new candidate needed. Prove report proposes none.

## 7. Verdicts
| target | statement | vacuity / hidden / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1a `expAvg_stein` | = pin | none | `inst_expAvg_stein` | ok | n/a | PASS |
| 1b `expAvg_selfcons` | = pin | none | `inst_expAvg_selfcons` | ok | n/a | PASS |
| 1c `expAvg_norm_solve` | = pin | none | `inst_expAvg_norm_solve` | ok | n/a | PASS |
| 1d `expAvg_expErr_le` | = pin | none | `inst_expAvg_expErr_le` | ok | n/a | PASS |
| 2a `expAvg_Bctl_ge` | = pin | none | `inst_expAvg_Bctl_ge` | ok | n/a | PASS |
| 2b `expAvg_eta_inv_le` | = pin | none | `inst_eta_inv_le` | ok | n/a | PASS |
| 2c `expAvg_moment` | = pin | none | `inst_expAvg_moment` | ok | n/a | PASS |
| 2d `expAvg_integral_conj` | = pin | none | `inst_expAvg_integral_conj` | ok | n/a | PASS |
| 2e `expAvg_u_zero` | = pin | none | `inst_expAvg_u_zero` | ok | n/a | PASS |
| 3a `STExpAvgAt_of_LWAvgLaw` | = pin | none | `inst_expAvgAt_holds` | ok | D487 | PASS |
| 3b `stImproveExpAver_holds` | = `STImproveExpAver d` | none | 5 instances | ok | D487 | PASS |
| 4 the 8 ticket instances | = section 3 | — | compiled | ok | — | PASS |
| registry (`Axioms.lean`) | one owed line deleted | — | — | pre-check exit 0 | — | PASS |

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1: the 7 extra public instance theorems `inst_expAvg_{stein,selfcons,norm_solve,expErr_le,Bctl_ge,moment,integral_conj}`
  are not pinned and are prefixed `inst_` rather than the file stem (§3 (E)); they live in `RBM.Gauss.Step6Inst`,
  have 0 clashes on `main`, and serve as the compiled instances of targets 1–2.
- O2: `inst_expAvg_norm_solve` exhibits only the conclusion at `a = 0` (`‖1‖ ≤ C·2`); the theorem is nonetheless applied
  with every hypothesis discharged at nondegenerate data, which is what §4 requires.
- O3: merge note for the hub: `Axioms.lean` was branched at `122f299`; on conflicts in the lists take the union with
  `STImproveExpAver` deleted (ticket §20 (3)); add `import RBM3D.Induction.ExpAvg` after the last import line.

Overall: **PASS** (all targets). No dispatcher sign-off needed.
