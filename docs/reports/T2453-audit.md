Auditor model: claude-opus-5-5
# T2453 audit (round 1) — Mon Oct 12 13:04:57 UTC 2026

Branch `t/T2453` at e54487c, merge base = `main` 4d4091e. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2453-audit1` (detached).
Scratch files in the session scratchpad `T2453/`: `AuditT2453.lean` (targets vs. pins), `AuditT2453G1.lean` (Part 3 G1 + axioms), `Ax.lean`, `AxMain.lean`.

## 1. Diff, build, hygiene, imports
```
$ git diff --name-only main...t/T2453
RBM3D/Chain/GridDuhamelGen.lean
$ git diff main...t/T2453 -- RBM3D/Induction RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/Carrier.lean | wc -l
       0
$ git rev-parse main:RBM3D/Induction/GridDuhamelN.lean t/T2453:RBM3D/Induction/GridDuhamelN.lean
7f523c7043e5ae07234f36d6b720b6800f6a4493
7f523c7043e5ae07234f36d6b720b6800f6a4493
$ lake build RBM3D.Chain.GridDuhamelGen     (warnings: 37, all in other modules; errors: 0)
✔ [3760/3760] Built RBM3D.Chain.GridDuhamelGen (4.1s)
Build completed successfully (3760 jobs).
$ grep -nE '\b(sorry|admit|native_decide)\b|^axiom|^\s*axiom ' RBM3D/Chain/GridDuhamelGen.lean ; echo exit=$?
exit=1
$ grep -n '^import' RBM3D/Chain/GridDuhamelGen.lean
6:import RBM3D.Chain.Step2Gen
7:import RBM3D.Induction.GridDuhamelN
$ wc -l RBM3D/Chain/GridDuhamelGen.lean        (stop line 2,000)
683
$ lake env lean docs/tickets/checks/T2453-check.lean >/dev/null 2>&1; echo exit=$?    (in the audit worktree)
check file exit=0
```
`RBM3D.lean` is not touched (the hub adds the import line at merge). No `BA/*` import. Privates of `GridDuhamelN` reused by `open private` (l.32), none deleted.

## 2. Axioms (all 16 public theorems/defs)
```
$ lake env lean AuditT2453G1.lean   (tail: #print axioms RBM.BA.<name>)
'RBM.BA.step2Gen_USemigroup_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step2Gen_UN_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step2Gen_UN_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step2Gen_UN_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step2Gen_UNHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step2Gen_UNHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step2Gen_UN_duhamel_telescope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandStep2_Ugen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.AvecNg_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandStep2_AvecN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandStep2_martIncN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandStep2_predIncN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stoppedDuhamelNg_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stoppedDuhamelNg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stoppedAzumaNg_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stoppedAzumaNg' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Premise scan (partial import; the full `import RBM3D` run is the hub's):
```
$ lake env lean Ax.lean      # import Test.Axioms + Chain.GridDuhamelGen; #assert_rbm_axioms
error: axiom audit: 26 premise(s) that no theorem of this development proves ... (26 names)
$ grep -E 'Ng|Semigroup|GridDuhamelGen|AvecNg|Step2Gen_U' ax.names ; echo exit=$?
exit=1
$ diff axmain.names ax.names ; echo exit=$?   # baseline: same check importing only Step2Gen + GridDuhamelN
exit=0
```
The new module adds no unproved premise; the 26 names are those of the import cone alone (concluded by modules outside it).

## 3. Statements against the pins (`AuditT2453.lean`: the check file's four `T2453_*` defs copied verbatim, then)
```lean
example : T2453_UNTelescope := fun C n h => Step2Gen_UN_duhamel_telescope C n h
example ... : Step2Gen_USemigroup C n ↔ T2453_USemigroup C n := Iff.rfl
example ... : StoppedDuhamelNg Cm s t K ↔ T2453_StoppedDuhamelNg Cm s t K := Iff.rfl
example ... : T2453_StoppedDuhamelNg Cm s t K := stoppedDuhamelNg Cm s t K
example ... [IsProbabilityMeasure Cm.Pp] ... : StoppedAzumaNg Cm s t K ↔ T2453_StoppedAzumaNg Cm s t K := Iff.rfl
example ... : T2453_StoppedAzumaNg Cm s t K := stoppedAzumaNg Cm s t K
example : ∀ {d} (sz) (E) (n), |E n| ≤ 2 → T2453_USemigroup (bandFM sz E) n := fun sz E n h => step2Gen_USemigroup_band sz E n h
example : ∀ ..., (Ugen d (sz.L n) (sz.lam n) (E n) σ v w A = Step2Gen_UN (bandFM sz E) n σ v w A) ↔
                 (UN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) v w A = Step2Gen_UN (bandFM sz E) n σ v w A) := ... Iff.rfl
example : ∀ ..., Ugen d (sz.L n) (sz.lam n) (E n) σ v w A = Step2Gen_UN (bandFM sz E) n σ v w A := ... bandStep2_Ugen ...
example : ∀ ..., STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) σ a = STgAg Cm s t K n σ a j ω := ... AvecNg_two ...
example ... : martIncNg Cm s t K n j σ ω = fun a => STLKMg … (j+1) … - condExp (filt sz j) Cm.Pp (…) ω := rfl
example ... : predIncNg Cm s t K n j σ ω = fun a => condExp (filt sz j) Cm.Pp (…) ω - Step2Gen_UN Cm.toFlowFM n σ u_j u_{j+1} (A_j) a := rfl
example : ∀ ..., T2453_StoppedDuhamelNg (bandStep2Mat sz E) s t K → RBM.Ind.StoppedDuhamelN sz E s t K := by ...   -- check route 7(a)
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2453-audit1 && lake env lean AuditT2453.lean; echo exit=$?
exit=0
```
- T3 `Step2Gen_USemigroup`: definitionally the pin (`Iff.rfl`); band theorem `step2Gen_USemigroup_band` has exactly the check's band shape (`|E n| ≤ 2`; `3 ≤ L` from `sz.three_le_L`).
- T1: `Step2Gen_UN_duhamel_telescope` proves `T2453_UNTelescope` as a term (same quantifier order, `0 ≤ u j`, `u j < 1` for `j ≤ m`). `_add` (no premise), `_self`/`_comp` (premise T3 + `0 ≤ v,w < 1`), `UNHom(_apply)`: the band statements with `Ugen ↦ Step2Gen_UN`, `(3 ≤ L, |E| ≤ 2) ↦ T3` (file l.74–138 vs `GridDuhamelN:82–153`, read).
- T2 (U-C4): no kernel, no `abbrev` added; the `Iff.rfl` shape compiles; the bridge is `(Step2Kern_UN_band …).symm`.
- T4: `AvecNg`/`martIncNg`/`predIncNg` equal the `let`s of the G1 pin (`rfl`); `bandStep2_AvecN`, `_martIncN` are `rfl`, `_predIncN` is proved; `AvecNg_two` is `rfl`.
- T5: `StoppedDuhamelNg` ↔ pin by `Iff.rfl`; `stoppedDuhamelNg_at` has premises at `n` only (T3 at `n`, `0 ≤ s n ≤ t n < 1`, `K n ≠ 0`, `min j (τ ω) ≤ K n`).
- T6: `StoppedAzumaNg` ↔ pin by `Iff.rfl` (measurability premise kept exactly as pinned, not restated); `stoppedAzumaNg_at` has `hmeas`, `hτ`, `hsubG`, `0 ≤ x`; no window premise (as the band `:553`).
- T8 (C1/E-C1): grep of the generic declarations:
```
$ P='mE|mSigma|\bzt\b|etaT|\bSB\b|sz\.lam|cycProd|\|E|‖m‖|pathP|bandFM|bandStep2Mat'
  hits per range: l.46-55: 1 (l.50, docstring) ; l.67-175: 0 ; l.186-214: 0 ; l.235-414: 0
```
All other hits are in `step2Gen_USemigroup_band` (l.56–65), `bandStep2_Ugen` (l.179–184), `bandStep2_*` (l.220–231) and the band sections ≥ l.416.

## 4. G1 in-place rule: Part 3 names (`AuditT2453G1.lean`, statements copied from `main:RBM3D/Induction/GridDuhamelN.lean`)
21 `example`s, one per name, each `example <binders> : <statement> := <name> …` (defs: `rfl` for the body, Prop defs `Iff.rfl` to the full body):
`Ugen`, `GridDuhamelN_Ugen_add`, `_self`, `_comp`, `GridDuhamelN_UgenHom`, `_UgenHom_apply`, `_Ugen_duhamel_telescope`, `Ugen_two_eq_Uop`, `AvecN`, `martIncN`, `predIncN`, `StoppedDuhamelN`, `stoppedDuhamelN_at`, `stoppedDuhamelN`, `AvecN_two`, `martIncN_two`, `predIncN_two`, `stoppedDuhamel105_of_stoppedDuhamelN`, `StoppedAzumaN`, `stoppedAzumaN_at`, `stoppedAzumaN`.
```
$ lake env lean AuditT2453G1.lean ; echo exit=$?     (only the #print axioms lines of §2 are printed)
exit=0
```
The blob hash of `GridDuhamelN.lean` is unchanged (§1).

## 5. Compiled nonempty instances (file §9, l.484–679; all in the module build above)
Data: `d = 3`, `sz0` (`L_0 = 4`), `n = 0`, `E ≡ 0`, `σ = ![true,true,false]` (non-constant, `decide` l.497), `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`.
| endpoint | instance (line) | hypotheses discharged |
|---|---|---|
| `step2Gen_USemigroup_band` | l.522 | `|0| ≤ 2` by `norm_num` |
| `bandStep2_Ugen` | l.526 at `v,w = 1/4,1/2` | none needed |
| `Step2Gen_UN_add` / `_self` / `_comp` / `UNHom_apply` | l.532 / 539 / 545 / 553 | T3 by the band theorem; `0 ≤ 1/4, 1/2, 3/4 < 1` |
| `Step2Gen_UN_duhamel_telescope` | l.559, `u j = j/10`, `m = 3` | T3; `0 ≤ j/10 < 1` for `j ≤ 3` |
| `AvecNg_two` | l.575 | — |
| `stoppedDuhamelNg_at` | l.584, `τ ≡ 3`, `j = 4` (`min = 3 ≤ 4`) | all: T3, `s0`, `st`, `t1`, `K ≠ 0`, `hjτ` |
| `stoppedDuhamelNg` | l.608 | (term) |
| `stoppedAzumaNg_at` | l.614, `τ ≡ 3`, `m = 2` | `hmeas` by `walk_measurable_loopFine ∘ pathH_measurable_filt`; `hτ` by `MeasurableSet.const`; `hsubG` kept (input (d), producer `azumaSubGN`, T4s2) |
| `stoppedAzumaNg_at` | l.649, `τ ≡ 0`, `c ≡ 0` | all, `hsubG` by `HasCondSubgaussianMGF.fun_zero` |
| `stoppedAzumaNg` | l.675 | (term), instance via private `GridDuhamelGen_bandPp_isProbabilityMeasure` |
Band corollaries 7(a): l.436 re-derives `stoppedDuhamelN_at`'s statement, l.452 `StoppedDuhamelNg (bandStep2Mat) → StoppedDuhamelN`, l.461 `stoppedAzumaN_at`'s statement, all from the generic targets through the bridges.

## 6. Hidden hypotheses, vacuity, cycles
- No new structure; T3 enters as an explicit `Prop` premise (`Step2Gen_USemigroup`), discharged at the band by `step2Gen_USemigroup_band` (proved), BA owed by T4-BA (ticket input (a)). No `False`-like premise: T3 holds at the concrete band data.
- Dependencies: only merged modules (`Chain.Step2Gen`, `Induction.GridDuhamelN`); the new file has no importer (no cycle).
- `hsubG` is ticket input (d), a premise of the pinned G3 statement itself, as in the merged band pin; it is an internal producer (`azumaSubGN`, T4s2), not a paper-cited external input, so no TEAM §8 lesson-14 limit check applies.

## 7. Paper deltas
Lean/paper differences: (1) the window `3 ≤ L, |E| ≤ 2` replaced by the carrier semigroup premise T3 — proposed `T2453a`; (2) G3 drops the five unused window premises and adds the `filt`-measurability premise of `AvecNg` — proposed `T2453b`. The conditional sub-Gaussian input is unchanged from the band pin. Coverage complete.

## 8. Observations (no verdict effect)
- O1. The only fully discharged Azuma instance has `τ ≡ 0` (empty stopped sum); the nondegenerate `τ ≡ 3` instance keeps `hsubG` as a hypothesis. Both are what target 7(b) asks for, and (d) is a declared input.
- O2. `GridDuhamelGen_bandPp_isProbabilityMeasure` is a `private instance`; the instance attribute still applies in importers (a true instance; no conflict observed).
- O3. The check's non-binding route shape `T2453_StoppedAzumaNg (bandStep2Mat …) → StoppedAzumaN` is not stated in the file; the `_at` re-derivation (l.461) covers target 7(a).

## Verdict
| target | verdict |
|---|---|
| 1 kernel algebra (`Step2Gen_UN_add/_self/_comp`, `Step2Gen_UNHom(_apply)`, `_duhamel_telescope`) | PASS |
| 2 `bandStep2_Ugen` (U-C4, no third kernel) | PASS |
| 3 `Step2Gen_USemigroup`, `step2Gen_USemigroup_band` | PASS |
| 4 `AvecNg`, `martIncNg`, `predIncNg`, bridges, `AvecNg_two` | PASS |
| 5 `StoppedDuhamelNg`, `stoppedDuhamelNg_at`, `stoppedDuhamelNg` | PASS |
| 6 `StoppedAzumaNg`, `stoppedAzumaNg_at`, `stoppedAzumaNg` | PASS |
| 7 band corollaries and instances | PASS |
| 8 C1 / E-C1 grep | PASS |
| 9 G1 (in-place rule, 21 Part 3 names) | PASS |

**Ticket T2453: PASS.** No dispatcher sign-off needed.
