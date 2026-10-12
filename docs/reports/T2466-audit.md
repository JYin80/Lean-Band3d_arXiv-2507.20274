Auditor model: claude-opus-5-5
# T2466 audit (round 1) — Mon Oct 12 18:58:14 UTC 2026
Ticket `docs/tickets/T2466.md`; check `docs/tickets/checks/T2466-check.lean`; branch `t/T2466` at `cebb7791`; audit worktree
`../RBM3D-wt/T2466-audit1` (detached). Scratch: `$S = <scratchpad>/T2466` (not committed).

## 1. Diff scope and sizes
```
$ git diff --stat main...HEAD
 RBM3D/Graph/BAExp14d.lean  | 620 +++++++++++++++++++++++++++++++
 RBM3D/Graph/BAExp14dB.lean | 908 +++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1528 insertions(+)
$ git diff main...HEAD -- RBM3D/Test RBM3D.lean | wc -l
       0
```
Only sole writable files; both below the 2,000-line stop line; reserve `BAExp14dC.lean` not created; `Test/Axioms.lean` unchanged.

## 2. Build
```
$ lake build RBM3D.Graph.BAExp14d RBM3D.Graph.BAExp14dB
⚠ [4011/4012] Built RBM3D.Graph.BAExp14d (7.0s)
warning: RBM3D/Graph/BAExp14d.lean:29:100: This line exceeds the 100 character limit, please shorten it!
⚠ [4012/4012] Built RBM3D.Graph.BAExp14dB (10s)
warning: RBM3D/Graph/BAExp14dB.lean:23:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (4012 jobs).
exit 0          (grep -cE '^error' build.log: 0)
```

## 3. Statements against the pins (script: check file + `import RBM3D.Graph.BAExp14dB` + term-mode examples)
`$S/audit_check2.lean` = check-file lines 11-335 (imports and both sections verbatim) + `T2465_Q1Need` pasted from
`T2465-check.lean:184-193` + the lines below, closed by terms only (no tactic):
```
example : T2466_dataT_eq BAExp14d_dataT := BAExp14d_dataT_eq
example : T2466_val_scale BAExp14d_dataT := BAExp14d_val_scale
example : ∀ d, T2466_BAGtoAGT d := baGtoAGT_holds
example : ∀ d, T2466_Bctl_small d := BAExp14d_Bctl_small
example : ∀ d, T2466_entry d := baExp14dEntry_holds
example : ∀ d, T2466_BAG5LeafPrec1 d := baG5LeafPrec1_holds
example : ∀ d, T2465_Q1Need d := baG5LeafPrec1_holds
example : BAGtoAGT = T2466_BAGtoAGT := rfl
example : BAExp14dEntry = T2466_entry := rfl
example : BAG5LeafPrec1 = T2466_BAG5LeafPrec1 := rfl
example : BAG5LeafPrec1 = T2465_Q1Need := rfl
$ lake env lean $S/audit_check2.lean > check2.out 2>&1; echo "exit $?"; grep -c error check2.out
exit 0
0
```
Negative control (`$S/neg.lean`: `example : ∀ d, BAExp14dEntry d := baGtoAGT_holds`): `grep -c error` = 1.
The three statement defs are definitionally the pins (`rfl`), and every target theorem closes its pin as a term; S5 does not
occur (`BAG5LeafPrec1 = T2465_Q1Need := rfl`).

Mathematical reading of the pins (ticket targets 1-6):
- T1 `BAExp14d_dataT`: `G`, `M`, `g₀Ψ` of `BAlwData`, `S = svarF(0)`, `S⁺ = lwLift (BATheta … t true true)`; `val_scale` for every
  `P : BAPGraph (Fin 2)`, `3 ≤ L`, `BAReal`, `0 ≤ t < 1` (`t = 0` included), factor `t^{n_W}` exact. Matches ticket.
- T2 `BAGtoAGT`: the form of `baGtoAG_E` with `D.S = S'`, `D.Sp = lift(ω_t)`, no `hext`; constants `∃ K₀ K₁ Kd C c` chosen after
  `(d, Λ, κ)` and before `L W g0 E t m Γ D`, i.e. uniform in `0 ≤ t < 1`. Quantifier order as in the ticket.
- T4 `Bctl_small`: `∃ c₀ > 0` before `t`, `∀ᶠ n`, `B ≤ 2N^{-c₀}`; `BAExp14dEntry`: only `STLocalEntrygL` as premise, `∃ ε₁ > 0`,
  `‖G_t − M‖_max ≺ W^{-ε₁}`.
- T6 `BAG5LeafPrec1`: the five Step 1/2 premises, `BAG5LeafProps [P] → P.g.nM = 1 →` the `≺` bound
  `t^{n_W} η_t⁻¹ B^{ord/2}`; no distinct-molecule hypothesis on `P` (S3). It is the `n_M = 1` half of T2464's `BAG5LeafPrec`
  by design (ticket target 6); it is not the general leaf pin, and the prove report (d) says so (§5.6).
- T3, T5 are private by the ticket; they enter only through T6.

## 4. Hidden hypotheses, vacuity, cycles
```
$ grep -nwE 'sorry|admit|axiom|native_decide' RBM3D/Graph/BAExp14d.lean RBM3D/Graph/BAExp14dB.lean; echo $?
1
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus|LWG5Data' <both files>; echo $?      # C1
1
$ grep -nE '^(private )?(structure|class|inductive)' <both files> | wc -l
0
$ grep -n '^import\|^open private' <both files>
BAExp14d.lean: import RBM3D.Graph.BAAtom2 / BAExp14aB / BAG5Leaf / LWExpTerm3
BAExp14d.lean:43:open private lwExpTerm3_auxVal_zero lwExpTerm3_auxVal_one from RBM3D.Graph.LWExpTerm3
BAExp14d.lean:44:open private BASizeClaim_theta_decay from RBM3D.Graph.BASizeClaim
BAExp14dB.lean: import RBM3D.Graph.BAExp14d / BAAuxGraph2B
BAExp14dB.lean:35-36: open private BAExp14d_det BAExp14d_GM_le hr0 g0_bounds data_bounds Ψ0_pos ones_row from RBM3D.Graph.BAExp14d
```
- No new structure; the targets' hypotheses are all in the signatures above. Every import is a merged module or part A; no
  T2464/T2465 file is read; no cycle.
- `hext` occurs in the new files only in comments/docstrings (`grep -nw hext`: lines 12, 25, 26, 130, 136, 266, 267, 391, 477,
  580 of part A; none in B), i.e. G3 is genuinely `hext`-free.
- No new external hypothesis: the five Step 1/2 pins are existing registered premises and appear only inside `BAExp14dEntry`
  (one) and `BAG5LeafPrec1` (five). Premise scan unchanged:
```
$ lake env lean $S/ax.lean      # import RBM3D; import RBM3D.Graph.BAExp14dB; #assert_rbm_axioms   (exit 0)
axiom audit: 13501 theorems, 4290 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 63, structural 45, refuted 6, superseded 13).
$ lake env lean $S/ax0.lean     # import RBM3D only (baseline)
axiom audit: 13490 theorems, 4282 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 63, structural 45, refuted 6, superseded 13).
```

## 5. Axioms (from `$S/audit_check2.lean`)
```
'RBM.BA.BAExp14d_dataT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14d_val_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baGtoAGT_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14d_Bctl_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baExp14dEntry_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baG5LeafPrec1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAExp14dInst.leaf1_props' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Compiled nonempty instances (in the modules built in §2; namespace `BAExp14dInst`)
Data: `d = 3`, `sz0` at `n = 0` (`L = 4`, `W = 32`), `zSeq`, `flow_sz0`, `t ≡ 1/2` (`half_lt_t0`), `κ = 1/2`, `Λ = 10`.
`leaf1 : BAGraph (Fin 2) (Fin 4)` (3 solid, 2 waved, 3 `M`-dotted edges; externals tied in one molecule, so `hext` would fail).
`leaf1_props : BAG5LeafProps [leaf1P] ∧ leaf1P.g.nM = 1 ∧ leaf1P.scalingOrder = 3`, by `decide`/`simp`.

| target | location | application | deterministic hyps discharged | kept as hypotheses |
|---|---|---|---|---|
| T1 `dataT_eq` | A:524 | at instance data, any `ω` | — | none |
| T1 `val_scale` | A:536 | `leaf1P`, `t = 1/2` | `3 ≤ L` (`three_le_L`), `BAReal` (`hr0` = `BAflow_real … flow_sz0 0`), `0 ≤ 1/2 < 1` | none |
| T2 `baGtoAGT_holds` | A:582 | `leaf1`, `D0 ω`, `Ψ0 = η⁻¹+1`, `A = 1`, `r = R = 0`, `ξ ≡ Ψ0` | `0 < g0 ≤ 10` (`g0_bounds`), `BAReal`, `Normal` (decide), four `D` equalities (`rfl`), `‖G−M‖ ≤ Ψ0` and window (`data_bounds`), `card·0 ≤ 0`, `ξ ≥ 0` | none |
| T3 (private det) | A:599, B:864 | `leaf1`/`leaf1P`, `ξ₀ ≡ 1`, `cc = Ψ0`, `S2 = L^3` | as T2, plus `nM ≤ 1`, `BAG5Attached` from `leaf1_props`, row sums (`ones_row`) | none |
| T4 `Bctl_small` | B:881 | `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2` | `0 < κ, ε, 𝔡`, `BAFlow`, `0 ≤ t ≤ T₀` | none |
| T4 `entry` | B:887 | same | same | `STLocalEntrygL` (other gate's pin) |
| T6 `baG5LeafPrec1_holds` | B:895 | same, `P = leaf1P` | as T4, `BAG5LeafProps`, `nM = 1` (`leaf1_props`) | the five Step 1/2 pins |

All compile (§2). Nondegenerate: `N = 2^21`, nonempty index sets, `t = 1/2` interior, a nontrivial `n_M = 1` leaf with
`ord = 3`; the only hypotheses left are other gates' pins (allowed by CLAUDE.md §4 step 2).

## 7. Paper deltas
- Dropping "distinct external vertices in distinct molecules" from `(G_by_auxG_BA)` (`B:486-490`): proposed as `T2466a`;
  the band analogue is already `D425 (T2170f)` in `docs/paper-deltas.md:1384`.
- Internal parameter choices (`ρ`, `D₁`, `c₀`, `ε₁`, Ward constant 4, window constant): `T2466b` (no statement change).
- T6 is a conditional `n_M = 1` half (the five premises), stated in prove report (d) as a §5.6 conditional adapter; the leaf pin
  itself is T2464's, whose paper deltas belong to that ticket.
Coverage complete for the statements of this ticket.

## 8. Observations (no RETURN)
- O1. Prove report (b) says `lake env lean` on both files prints 0 lines; the build prints one `longLine` warning per file
  (A:29, B:23, inside the module docstrings, before `set_option linter.style.longLine false`). No statement/build effect.
- O2. The statement defs of targets 4 and 6 sit in part B, not part A as in the ticket's file note; the prove report (d) records
  it; no pin changed.
- O3. `open private` dependencies on `lwExpTerm3_auxVal_zero/_one`, `BASizeClaim_theta_decay` are fragile under upstream
  renames (recorded in prove report (d)).

## Verdict
| target | verdict |
|---|---|
| 1 `BAExp14d_dataT`, `BAExp14d_dataT_eq`, `BAExp14d_val_scale` | PASS |
| 2 `BAGtoAGT`, `baGtoAGT_holds` | PASS |
| 3 `BAExp14d_det` (private) | PASS |
| 4 `BAExp14d_Bctl_small`, `BAExp14dEntry`, `baExp14dEntry_holds` | PASS |
| 5 private pathwise/envelope/floor/arithmetic | PASS |
| 6 `BAG5LeafPrec1`, `baG5LeafPrec1_holds` | PASS |
| 7 instances | PASS |
| 8 registry (no `inductive`; premise scan unchanged) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
