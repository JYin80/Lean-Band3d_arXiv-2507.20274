Auditor model: claude-opus-5-5

# T2198 (S5-09a) audit, round 1: `RBM3D/Induction/LemDecCalELip.lean`

Date (`date -u`): Mon Oct  5 18:15:30 UTC 2026. Branch `t/T2198` at 9c319c0 (merge-base with `main` 9eb0502). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2198-audit1` (detached at `t/T2198`). Scratch files: scratchpad `T2198/` (not committed).

## 1. Diff scope and frozen signatures

```
$ git diff --stat main...t/T2198
 RBM3D/Induction/LemDecCalELip.lean | 1365 ++++++++++++++++++++++++++++++++++++
 1 file changed, 1365 insertions(+)
$ git grep -n "LemDecCalELip\|lemDecCalELip" main -- RBM3D | wc -l
       0
$ grep -nE "^(theorem|noncomputable def|def|private)" .../LemDecCalELip.lean | grep -vE "LemDecCalELip_|lemDecCalELip_"
(empty)
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " .../LemDecCalELip.lean
none
```
Only the sole writable file is touched; no merged file, pin or `cont_core` changed; `RBM3D/Test/Axioms.lean` untouched (no new `Prop`; registry pre-check below exits 0).

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.LemDecCalELip      (warnings all in merged files; none in LemDecCalELip)
✔ [3779/3779] Built RBM3D.Induction.LemDecCalELip (8.8s)
Build completed successfully (3779 jobs).
exit 0
$ printf 'import RBM3D\nimport RBM3D.Induction.LemDecCalELip\n#assert_rbm_axioms\n' > Reg.lean; lake env lean Reg.lean
registry pre-check exit 0
axiom audit: 5904 theorems, 2080 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
```
(`RBM3D.olean` in the audit worktree is the copied cache of the main worktree; the hub's full `lake build` at merge is authoritative.)
`#print axioms` of all 24 public declarations of the file (script `Ax.lean`, names extracted by `grep` of the file): every line is
`depends on axioms: [propext, Classical.choice, Quot.sound]`; `grep -v` of that string leaves only the (partial-import) registry
message of the extra `#assert_rbm_axioms` line, superseded by the full-import pre-check above. The eight targets:
```
'RBM.Gauss.Sizes.LemDecCalELip_Jsharp_basic' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_LK2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_ELKLK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_EGt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_ee' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_relcont' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_Jsharp_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.LemDecCalELip_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (script)

Scratch `PinCheck.lean` = `import RBM3D.Induction.LemDecCalELip` + lines 5..(end of section 2) of
`docs/tickets/checks/T2198-check.lean` verbatim (sections 1 and 2) + the following lines:
```
example : RBM.Gauss.Sizes.LemDecCalELip_Jsharp_basic_pin := @RBM.Gauss.Sizes.LemDecCalELip_Jsharp_basic
example : RBM.Gauss.Sizes.LemDecCalELip_LK2_pin := @RBM.Gauss.Sizes.LemDecCalELip_LK2
example : RBM.Gauss.Sizes.LemDecCalELip_ELKLK_pin := @RBM.Gauss.Sizes.LemDecCalELip_ELKLK
example : RBM.Gauss.Sizes.LemDecCalELip_EGt_pin := @RBM.Gauss.Sizes.LemDecCalELip_EGt
example : RBM.Gauss.Sizes.LemDecCalELip_ee_pin := @RBM.Gauss.Sizes.LemDecCalELip_ee
example : RBM.Gauss.Sizes.LemDecCalELip_relcont_pin := @RBM.Gauss.Sizes.LemDecCalELip_relcont
example : RBM.Gauss.Sizes.LemDecCalELip_Jsharp_rel_pin := @RBM.Gauss.Sizes.LemDecCalELip_Jsharp_rel
example : RBM.Gauss.Sizes.LemDecCalELip_lift_pin := @RBM.Gauss.Sizes.LemDecCalELip_lift
example : @LemDecCalELip_Jsharp_voc = @LemDecCalELip_Jsharp := rfl
$ lake env lean PinCheck.lean
pincheck exit 0
```
Body of `LemDecCalELip_Jsharp` vs the check file's `LemDecCalELip_Jsharp_voc` (awk extraction from `noncomputable def` to the
`STtailTD sz n u D p.2))` line, name stripped):
```
$ diff <(extract check _voc) <(extract file LemDecCalELip_Jsharp) && echo IDENTICAL
IDENTICAL (       5 lines)
```
Check-file section 4, third example (2a at the instance data) proved by `LemDecCalELip_LK2` with every premise discharged
(scratch `Inst2a.lean`, statement copied verbatim from the check file): `inst2a exit 0`.

Reading of the pinned statements against the ticket's mathematics:
- Target 1: `1 ≤ J♯`; `STLK2 ≤ J♯·STtailTD` for all `σ, a`; minimality among `X ≥ 1`. Unconditional; matches ticket item 1.
- 2a–2d: premises `3 ≤ d`, `SizeTendsto`, `0 < κ`, `|E n| ≤ 2 − κ`, `0 ≤ s n`, `t n < 1`, `∀ᶠ n, (1 − t n)⁻¹ ≤ N`;
  `∃ C ≥ 0` before `∀ᶠ n` (uniform constant), `∀ ω ∈ contGood sz n`, `∀ u u' ∈ TimeIcc s t n`, all indices (2d every `a, a'`,
  no distance restriction), `‖F(u) − F(u')‖ ≤ N^C √|u−u'|` (2a with `|·|`, the others with `‖·‖`). Matches ticket item 2.
- Target 3: five inequalities with `ρ = 1 + (1−t)⁻¹|u−u'|`, powers `ρ, ρ, ρ, ρ², ρ⁴`; hypotheses only `t < 1`, `u, u' ≤ t`. Matches item 3.
- Target 4: (L1) premises plus `0 < D`; `J♯(u') ≤ (1 + N^C√|u−u'|) J♯(u)` on `contGood`, eventually, uniform `C`. Matches item 4.
- Target 5: `#V ≤ N^{Cv}` eventually, `J ≥ 1`, `R₀ ≥ 0`, `R ≥ N^{-CR}` eventually, `m ≥ 0`, relative continuity of `R₀, R`
  (deterministic) and `J` (on `contGood`), Hölder-1/2 of `ξ` on `contGood`, `PrecPT → Prec` on `TimeIcc × V`. Matches item 5.
  It is a generic lemma (no paper statement pinned); its use for `STLemDecCalEConcl` is T2193's step (N), not claimed here.

## 4. Hidden hypotheses, vacuity, cycles

- No new `structure`/`class`; every premise is in the signature (pin check above). No new `Prop` (registry unchanged).
- `contGood` (merged, `ContinuityNet.lean:225`) is `{ω | ∀ c, |ω ⟨n, c⟩| ≤ N}`, a genuine event; `cont_highProbAt_good` (`:369`)
  gives `HighProbAt sz.seqP sz.size (contGood sz)` from `Tendsto sz.size`; (G) uses it inside `cont_core` (file `:1197-1199`),
  so the `contGood` restriction of (L1)/target 4 is discharged in (G), not assumed.
- `(1 − t n)⁻¹ ≤ N` (eventually) is a deterministic premise, not an external input; it is satisfied at the instance data
  (`16/15 ≤ N_n`, discharged in Lean by `lemDecCalELip_inst_tN`), and preflight rows 16–17 give the two §29 (2) chains.
- No external hypothesis is introduced; all dependencies are merged on `main` (`git grep` of the imported names on `main`
  resolves; build passes against `main`'s modules). No cycle: the file imports only `Step5Pins`, `NetLift2`, `Deriv`, `Props4`.

## 5. Compiled nonempty instances (file `:1274-1363`, compiled in the build of §2)

| target | instance | data | deterministic premises |
|---|---|---|---|
| 2a, 2b, 2c, 2d | four `example`s (`:1295, :1304, :1313, :1322`) | `d = 3`, `sz0` (`N_n = 2²¹(n+1)¹⁸`), `E ≡ 1/2`, `κ = 1`, `sInst ≡ 0`, `tInst ≡ 1/16` | all discharged: `norm_num`, `sz0_tendsto`, `lemDecCalELip_inst_tN` |
| 3 | `:1332` | `sz0`, `n = 1`, `t = 1/16`, `u = 0`, `u' = 1/16`, `D = 42`, `a ≡ 0` (`ρ = 16/15`) | `t < 1`, `u ≤ t`, `u' ≤ t` discharged |
| 1 | `:1337` | `sz0`, `E ≡ 1/2`, `D = 42`, `n = 1`, `u = 0`, `ω ≡ 0` | none (unconditional) |
| 4 | `:1340` | as 2a, `D = 42` | all discharged incl. `0 < 42` |
| 5 | `:1351` | `sz0`, `V ≡ Unit`, `ξ ≡ 0`, `J ≡ 1`, `R₀ ≡ 0`, `R ≡ 1`, `m = 2`, `Cv = C = CR = 0`, `[0, 1/16]` | all discharged; `PrecPT` by `precPT_of_le` |

No `N = 0` (`N_n ≥ 4`), no empty index (`TimeIcc = [0,1/16]`, `Unit`, `Fin 2 → Bool`, `Zd 3 L` nonempty), no collapsed window,
no `False` premise, no astronomically large witness. Instance (d) has trivial `ξ` and `J`, exactly as prescribed by the ticket.

## 6. Paper deltas

The prove report's section (d) proposes `T2198a` (`contGood` with coordinates `≤ N` and the premise `(1−t)⁻¹ ≤ N` in place of
the paper's `‖H‖ ≤ N^C` and the `N^{-C}`-net, `1_2:1400`; explicit constants), `T2198b` (the form `PrecPT(ξ ≺ R₀ + J^m R) → Prec`
of (G)), `T2198c` (`J♯` is a realized random control at a single time, not the deterministic `J*` of `eq:def_new_J*`, `3_5:2310`).
Together with the dispatcher's `T2193c′` (`docs/tickets/T2193-amend-1.md:12`), these cover every Lean/paper difference of the
targets (the Hölder constants, the good event, the time-window premise, the realized control, the lift form).

## 7. Observations (no RBM3D statement, instance, build, axiom or delta coverage affected)

- O1. `T2198c` says `T2193c′` "was not read"; the overlap of T2198c with T2193c′ is for the dispatcher to merge when numbering.
- O2. File length 1365 lines, above the ticket's estimate of 600–900; not an acceptance criterion.
- O3. Prove report: 249 lines (≤ 300), line 1 `Prover model: claude-sonnet-5-5`.

## 8. Verdicts

| target | verdict |
|---|---|
| 1 `LemDecCalELip_Jsharp` (def, body = `_voc`) + `LemDecCalELip_Jsharp_basic` | PASS |
| 2a `LemDecCalELip_LK2` | PASS |
| 2b `LemDecCalELip_ELKLK` | PASS |
| 2c `LemDecCalELip_EGt` | PASS |
| 2d `LemDecCalELip_ee` | PASS |
| 3 `LemDecCalELip_relcont` | PASS |
| 4 `LemDecCalELip_Jsharp_rel` | PASS |
| 5 `LemDecCalELip_lift` | PASS |

**Overall: PASS.** No dispatcher sign-off needed. Merge per CLAUDE.md §3 (A): the only file is `RBM3D/Induction/LemDecCalELip.lean`;
root import `import RBM3D.Induction.LemDecCalELip` after the last `import` line of `RBM3D.lean`.
