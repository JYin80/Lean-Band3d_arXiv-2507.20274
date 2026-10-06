Auditor model: claude-opus-5-5

# T2228 audit (round 1) — S6-07 `Induction/ExpEtermsB` (`STExpDriftLo`, `STExpDriftDecay`)

Audit time (`date -u`): Tue Oct  6 00:08:00 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2228-audit1`, detached at `62288d9` (`t/T2228`).
Scratch files: scratchpad `T2228/` (`audit_eq.lean`, `build.log`, `eq.out`).

## 1. Diff scope and frozen signatures
```
$ git diff --stat main...t/T2228
 RBM3D/Induction/ExpEtermsB.lean | 1177 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |    2 -
 2 files changed, 1177 insertions(+), 2 deletions(-)
$ git diff main...t/T2228 -- RBM3D/Test/Axioms.lean   (removed lines only)
-   `RBM.Gauss.Sizes.STExpDriftLo, -- `6:63-66`, `6:73-79` drift bound in regime (iv): S6-07; S6-01 (T2204, DECISIONS §67: owed)
-   `RBM.Gauss.Sizes.STExpDriftDecay, -- `3_5:1634` drift decay: S6-07; S6-01 (T2204, DECISIONS §67: owed)
$ git diff t/T2228 main --stat -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/Step34Pins.lean RBM3D/Defs/StochDomAt.lean
(empty)
$ git merge-tree --write-tree main t/T2228   (main = dc2d99b, base 37289f6)
merge-tree exit 0
```
Exactly the two sole writable files; the Axioms diff is the two pinned deletions; merged pin texts unchanged; merges cleanly into current `main`.

## 2. Build and hygiene (audit worktree)
```
$ lake build RBM3D.Induction.ExpEtermsB 2>&1 | grep -E "error|Build completed"; echo exit
Build completed successfully (3854 jobs).
exit 0
$ grep -c "ExpEtermsB.lean:" build.log          # warnings/errors located in the new file
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|opaque|implemented_by|extern|unsafe" RBM3D/Induction/ExpEtermsB.lean
39:set_option linter.style.longLine false
```
Helpers: 23 `private theorem expDr_*`; public names = the 14 targets of the ticket + 14 instances (§3 (E) respected).

## 3. Statements against the ticket's pins (compiled script)
`audit_eq.lean` = check file `docs/tickets/checks/T2228-check.lean` lines 19-26 (imports) + `import RBM3D.Induction.ExpEtermsB` + lines 27-329 (sections 1-2) + the following, run with `lake env lean` in the audit worktree:
```
example : RBM.Gauss.Sizes.T2228Check.X := @RBM.Gauss.Sizes.X     -- for X ∈ {expDr_Bctl_le_IV, expDr_envEGt,
   expDr_EGt_split, expDr_env_poly, expDr_expect, expDr_LK_prec, expDr_EGtLK_prec, expDr_EGtK_prec,
   STExpDriftLoConcl_of_LKU, stExpDriftLo_holds, STExpDriftDecayConcl_of_GdecayW, stExpDriftDecay_holds}   (12)
example : @RBM.Gauss.Sizes.T2228Check.expDrEGtLKM = @RBM.Gauss.Sizes.expDrEGtLKM := rfl
example : @RBM.Gauss.Sizes.T2228Check.expDrEGtK = @RBM.Gauss.Sizes.expDrEGtK := rfl
example (d : ℕ) : STExpDriftLo d := stExpDriftLo_holds d
example (d : ℕ) : STExpDriftDecay d := stExpDriftDecay_holds d
-- section 3: six `example : <check-file statement> := @RBM.Gauss.Step6Inst.<name>` for inst_expDriftLo_holds,
--   inst_expDriftDecay_holds, inst_skeleton6IV_Lo, inst_skeleton6I_Dec, inst_expDr_Bctl_le_IV, inst_expDr_envEGt
-- + #print axioms of the 12 theorems and the 6 section-3 instances
$ lake env lean audit_eq.lean > eq.out 2>&1; echo "exit $?"; grep -cE "error" eq.out
exit 0
0
```
All 22 equality examples elaborate: every public statement is definitionally the dispatcher's pinned text (hypotheses, binder order, `∀ᶠ`/`Prec`/`Whp` shape, exponents `6`, `-Kf`, `4`, `(1-u)⁻¹((N(1-u))⁻¹)^3`), and both merged pins `STExpDriftLo d`, `STExpDriftDecay d` are proved for every `d` exactly as stated in `Step6Pins.lean:323`, `:335`.

Paper check (`paper/tex/6_Step6_two_loop.tex:63-79`): `(eq:Exp(L-K)2)` and `(eq:ExpLWn=2_smalleta)` are `≺ (1-u)^{-1}(N|1-u|)^{-3}` for `1-u ≤ λ²/L^d`; the merged conclusion `STExpDriftLoConcl` bounds `‖𝔼ℰ^{LK×LK}+𝔼ℰ^{G̃}‖` by the same `R_u`, uniformly over `TimeIcc s t × σ × a` — same mathematics (sum of the two paper bounds). `(deccA0)` (`3_5:1634`) is the `W^{-D}` level of `STEKDecay` in `STExpDriftDecayConcl`. No special case or conditional adapter: the theorems are the full pins.

## 4. Hidden hypotheses, vacuity, cycles
- The pins are `STIngR6 d R Concl` (merged, `Step6Pins.lean:111-123`): all premises are explicit binders; no structure carrying hypotheses is introduced in `ExpEtermsB.lean` (no `structure`/`class` declared; the two new `def`s are `ℂ`-valued vocabulary).
- Proof of the pins (file `:901-905`, `:1049-1053`): `refine ⟨1/100, by norm_num, le_rfl, ?_⟩` then the `_of_LKU` / `_of_GdecayW` lemma; extra `STIngR6` premises are unused (only weakening). No premise is `False`; `𝔠_d = 1/100` satisfies `0 < 𝔠_d ≤ 1/100`.
- Dependencies: only merged modules (imports `ExpEtermsA`, `ExpAvg`, `ExpIniI`, `DecayLoopB`, `Step2Iterate`, `KDecay`, `Loop/KLFinal`, `Path/Walk`); nothing imports `ExpEtermsB`; no cycle.
- External hypotheses: the stochastic premises `STLKU`, `STExpAvgU`, `STGdecayW … 0` are premises of the merged pins (not new); the preflight gives a limit check along `szG`, `n → ∞` (`B N(1-u) → 1+64(1-u)/(26-u) ≤ 2`), prove report (a)(ii). `expDr_expect`'s `Prec` input is a generic random `≺` hypothesis of a tool lemma (not an external input).

## 5. Compiled nonempty instances
All instances are in `RBM3D/Induction/ExpEtermsB.lean` §7 (`namespace RBM.Gauss.Step6Inst`, `:1070-1175`) and compile in the module build.
| endpoint | instance | data | deterministic hyps |
|---|---|---|---|
| `stExpDriftLo_holds` | `inst_expDriftLo_holds` (= merged `inst_expDriftLo (stExpDriftLo_holds 3)`), `inst_skeleton6IV_Lo` | `szG`, `zB`, `[5/8,3/4]`, `d=3`, `N_0=4096` | discharged in merged `inst_ing6_IV` (`flow_zG`, `s<t`, `szB_flow_ht`, `szG_reg4`, `conStInd_const`) |
| `stExpDriftDecay_holds` | `inst_expDriftDecay_holds`, `inst_skeleton6I_Dec` | `szB`, `zB`, `[7/8,15/16]` | discharged in merged `inst_ing6_I` (`szB_reg5I`) |
| `STExpDriftLoConcl_of_LKU` | `inst_STExpDriftLoConcl_of_LKU` | `szG`, `zB`, `[5/8,3/4]` | `3≤3`, `0<1/10`, `flow_zG`, time range, `szG_reg4` |
| `STExpDriftDecayConcl_of_GdecayW` | `inst_STExpDriftDecayConcl_of_GdecayW` | `szB`, `zB`, `[7/8,15/16]` | `flow_zB`, time range |
| `expDr_Bctl_le_IV` | `inst_expDr_Bctl_le_IV` | `szG`, `n=0`, `u=3/4` (`1/4 ≤ 25/64`) | `by norm_num`, `simp [szG, szB]; norm_num` |
| `expDr_envEGt`, `expDr_EGt_split` | `inst_expDr_envEGt`, `inst_expDr_EGt_split` | `sz0`, `n=0`, `E=u=1/2`, `σ=(+,-)`, `a=(0,0)` | `|1/2|<2`, `1/2<1` |
| `expDr_env_poly`, `expDr_expect` | `inst_expDr_env_poly`, `inst_expDr_expect` | `szG`, `zB`, `[5/8,3/4]`, `Kenv=6`, `Kf=3` | env/floor discharged (`expDr_floor`), `SizeTendsto` from `flow_zG` |
| `expDr_LK_prec`, `expDr_EGtLK_prec`, `expDr_EGtK_prec` | `inst_expDr_*_prec` | `szG`, `zB`, `[5/8,3/4]` | all discharged |
Left as hypotheses only: the stochastic premises inside `InstIng6Concl` / `STLKU` / `STExpAvgU` / `STGdecayW … 0`, `expDr_expect`'s `≺` input, and other gates' unproved pins (`STExpDuhamelZ/Q`, `STExpIntIV`, `STExpIntI`, `STExpWardI`, `LWtermEXP`). No `N = 0`, empty index, collapsed window (`s < t` in every instance) or `False` premise.

## 6. Axioms
```
$ grep "depends on axioms" eq.out | cut -c1-110      (18 lines)
'RBM.Gauss.Sizes.stExpDriftLo_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpDriftDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STExpDriftLoConcl_of_LKU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STExpDriftDecayConcl_of_GdecayW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_EGt_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_env_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_LK_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_EGtLK_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_EGtK_prec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_Bctl_le_IV' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expDr_envEGt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expDriftLo_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expDriftDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_skeleton6IV_Lo' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_skeleton6I_Dec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expDr_Bctl_le_IV' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expDr_envEGt' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" eq.out
18
```
(The two `def`s are data; the full root `#assert_rbm_axioms` with the registry deletion is run by the hub at merge with the root import added; the prover's pre-check output is in the prove report b.6.)

## 7. Paper-delta coverage
Lean/paper differences and their candidates (prove report (d)):
- `(deccA0)` for `D_u` holds in every regime (`STReg5I` unused; paper states it for the regime-(i) window) — `T2228a`.
- `6:65`, `6:77`: `≺ W^dL^d(N|1-u|)^{-4}` obtained via `B_{u,0} ≤ 2(L^d(1-u))⁻¹`, constant `16` per term — `T2228b`.
- `6:78` `(eq:bcal_k)` (n=3) used uniformly in `u`; the `ℰ^{LK×LK}` bound needs no regime — `T2228c`.
- `≺ → 𝔼` needs a polynomial envelope `N⁶` and floor `N^{-3}` — `T2228d`.
These are the ticket's three required candidates (a)-(c) plus one; the merged pin texts are unchanged, so no statement-level delta is unrecorded.

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The report uses the tag `T2228a` for an ordinary candidate, while the ticket reserved `T2228a…` for a forced primed successor (none is needed). Tag naming only; the dispatcher numbers the entries.
- O2. Report b.2 prints names with a trailing `'` (e.g. `Sizes.expDrEGtLKM'`), a shell-quoting artifact; the audit's own `#print axioms` (§6) is clean.
- O3. Report b.1's `grep` pattern for hygiene (`sorry|admit|native_decide|^axiom`) is narrower than the audit's; the wider audit grep finds nothing forbidden either.

## Verdict
| target | verdict |
|---|---|
| 0 `expDrEGtLKM`, `expDrEGtK` (vocabulary; `rfl` to check file) | PASS |
| 1a-c `expDr_Bctl_le_IV`, `expDr_envEGt`, `expDr_EGt_split` | PASS |
| 2a-e `expDr_env_poly`, `expDr_expect`, `expDr_LK_prec`, `expDr_EGtLK_prec`, `expDr_EGtK_prec` | PASS |
| 3a-b `STExpDriftLoConcl_of_LKU`, `stExpDriftLo_holds` | PASS |
| 3c-d `STExpDriftDecayConcl_of_GdecayW`, `stExpDriftDecay_holds` | PASS |
| 4 instances (6 pinned + 8 extra) | PASS |
| registry (`Test/Axioms.lean`: the two owed lines deleted) | PASS |

**T2228: PASS.** No dispatcher sign-off needed. Merge note (from the ticket): T2224 deletes the adjacent lines `STExpDuhamelZ/Q`; keep all four deleted; commit the root import `RBM3D.Induction.ExpEtermsB` with the deletion.
