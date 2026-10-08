Auditor model: claude-opus-5-5

# T2333 audit (round 1): S5-15 `Induction/DuhamelI.lean`, `stDuhamelI_holds`, `stDuhamelConcl_engine`

Time: Thu Oct  8 14:10:58 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2333-audit1`, detached at
`533cf8e` (= `t/T2333`). Merge base `979f823`; `main` = `015198c`. Scratch files: scratchpad `T2333/`.

## 1. Diff scope

```
$ git diff --stat main...t/T2333
 RBM3D/Induction/DuhamelI.lean | 1994 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
$ git diff main...t/T2333 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STDuhamelI, -- integrated hierarchy `(iois-mtx2)`, case (i); S5-01 (T2138, DECISIONS §40: owed)
```
Only the two sole writable files; the registry edit is exactly the `STDuhamelI` line. No merged file touched, so no frozen
signature changed. 1994 lines < stop rule 2000.

## 2. Build and axioms

```
$ lake build RBM3D.Induction.DuhamelI      (tail; error/warning lines naming DuhamelI: 0)
✔ [3888/3888] Built RBM3D.Induction.DuhamelI (45s)
Build completed successfully (3888 jobs).
exit 0
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stDuhamelI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDuhamelConcl_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_duhamelI_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.duhamelI_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stDuhamelI_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STDuhamelI d
[exit 0]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom |set_option|@\[implemented_by|@\[extern|opaque " DuhamelI.lean
28:set_option linter.style.longLine false
965:set_option maxHeartbeats 1000000 in
1413:set_option maxHeartbeats 1000000 in
$ grep -nE "^\s*(private )?(structure|class|axiom|opaque)" DuhamelI.lean
(no hits)
```
Registry pre-check (scratch `registry.lean` = branch `RBM3D.lean` with `import RBM3D.Induction.DuhamelI` after its last import,
after `lake build` populated the oleans; the plain worktree `lake build` stops at the registry, as expected without the root import):
```
$ lake build | grep -E "axiom audit|^error|STDuhamelI"
error: RBM3D.lean:373:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...:
  [RBM.Gauss.Sizes.STDuhamelI]
$ lake env lean registry.lean     [exit 0]
axiom audit: 9944 theorems, 2979 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
$ grep -c "STDuhamelI\b" registry.out
0
```

## 3. Target 1 `stDuhamelI_holds : ∀ d, STDuhamelI d` — statement

The pin is the merged `STDuhamelI` (`Step5Pins.lean:317`), unchanged. Statement equality against the check file by Lean:
```
$ cat checkeq.lean = check imports (EtermsMid, Step5Kernel, Step5Kit, DifREP3) + import RBM3D.Induction.DuhamelI
    + check sections 1-2 + `example : RBM.Gauss.Sizes.T2333Check.T2333_stDuhamelI_holds := RBM.Gauss.Sizes.stDuhamelI_holds`
$ lake env lean checkeq.lean > checkeq.out; echo $?; grep -ci error checkeq.out
[checkeq exit 0]
0
```
Proof body (extracted): `refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩`, then `stDuhamelConcl_engine` with `STReg5I → STReg5Mid`
(`st5_reg5I_mid`), `hTTT := Or.inl (hReg n).1`, `hCon` at `𝔠_d = 1/100`, `hE` = the pin's `STEtermsMidConcl`, `P := STSigAll`.
The existential `𝔠_d = 1/100` satisfies the pin's `0 < 𝔠_d ≤ 1/100`; quantifier order is the pin's (constants, then `∃ 𝔠_d`,
then sizes and `∀ᶠ` inside `Prec`). Nine Step 1-4 premises and `Cd` are bound and unused (proof is stronger than needed; no
statement issue). No hypothesis hidden in a structure (no `structure`/`class` in the file); no cycle: the file imports only merged
modules and does not mention `STDuhamelI` as a hypothesis. **Statement: PASS.**

## 4. Target 2 `stDuhamelConcl_engine` — statement (shape fixed by the prover)

```
theorem stDuhamelConcl_engine (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hCon : STConStInd sz (1 / 100) s t)
    (hE : <body of STEtermsMidConcl sz (STflowE z) s t, written out>) (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz ∅ P (STflowE z) s t
```
`hE` is definitionally `STEtermsMidConcl`: both compiled examples (§5) pass `hE : STEtermsMidConcl …` to it. The ticket asked for
a general zero-mode set `Q` but permitted `Q = ∅` if the general form is too costly ("keep `Q = ∅` and say so"); the report says so
(narrative item 1: 6 lines left to the stop rule). The engine is general in the sign class `P` and covers case (i) and the
`STSigSame` half of case (ii) through `hTTT`. It is a reported engine shape, not a pinned target. **Statement: PASS** (the `Q = ∅`
restriction is the ticket's allowed fallback; S5-26's `Q^{(1)}` conjunct is still open, see O3).

## 5. Compiled nonempty instances

Data `szB` (`Step34Pins.lean:710`): `d = 3`, `L_n = 4`, `W_n = n + 4`, `lam = 1`; `zB = 1/2 + i/64`; `s = 7/8`, `t = 15/16`
(case (i): `lam²/L² = 1/16 ≤ 1 - t = 1/16`, `1 - s = 1/8 ≤ 1`). Nondegenerate (no `N = 0`, nonempty lattice, `s < t`).
```
theorem inst_duhamelI_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_duhamelI (stDuhamelI_holds 3) Cd hCd
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STDuhamelConcl szB ∅ STSigAll (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  stDuhamelConcl_engine (by norm_num) … szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (st5_reg5I_mid (by norm_num) szB_reg5I) (fun n => Or.inl (szB_reg5I n).1)
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigAll
example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STDuhamelConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) := … (case (ii) data, `Or.inr`)
```
All compile (module build above). Every deterministic hypothesis (flow, time ranges, regime, `hTTT`, `STConStInd`) is
discharged at the concrete data. The only remaining hypotheses are `STEtermsMidConcl` (the pin's own hypothesis, proved from
the open `STLWT` by `stEtermsMid_of_LWT`) and, inside `InstIng5Concl`, the Step 1-4 pins: these are allowed gate pins. The
exponent-closure check `duhamelI_absorb` at `A = 2^99`, `ρ = 2` also compiles (numeric lemma, not an endpoint; see O4).
**Instances: PASS** for both endpoints.

## 6. Paper deltas

The target is the merged pin, so the Lean statement adds no new difference from the paper. The prove report §(d) proposes
`T2333a` (martingale by Abel summation of the slot weights against the diagonal conjunct of `STGridMartAt`, factor `ρ²`; conjunct
4 / `STeeUM` unused; deviates from the route in the pin's docstring and `(uuwmskiow)`), `T2333b` (`u`-uniform lift by
near-minimizers per net cell for an arbitrary deterministic `F`), `T2333c` (unused premises of the pin), and `T2333d` (registry scan
and Prop-valued hypotheses of public engines). `grep -n T2333 docs/paper-deltas.md`: no hits yet (the dispatcher numbers them).
Coverage: complete. **PASS.**

## 7. Observations (no RETURN)

- O1 (imports): the ticket says "Imports (exactly)" `EtermsMid, Step5Kernel, Step5Kit, DifREP3`. The file imports
  `EtermsMid, Step5Kernel, PfStep5Grid, DifREP3` (`DuhamelI.lean:6-9`). `PfStep5Grid` (merged, needed for `pfStep5Grid_duhamel`)
  imports `Step5Kit`, so the ticket's module set is still covered transitively. The report flags this (item 8). No effect on
  statement, build or axioms.
- O2 (hub, merge hazard): `RBM3D/Test/Axioms.lean` on `main` changed after the merge base `979f823` (11 lines: T2318/T2332/T2334/
  T2329 registry edits, e.g. `STIniTermI` removed and `LWG5Expand` moved to superseded). `git diff t/T2333 main -- Axioms.lean`
  shows these lines. Copying the branch file wholesale would undo them. At merge, apply only the one-line `STDuhamelI` deletion
  to main's file (for example `git diff main...t/T2333 -- RBM3D/Test/Axioms.lean | git apply`). Since the base, `main` has also
  merged `Induction/IniTermI.lean` (T2329). `git grep` on `main` finds 0 hits for `stDuhamelI_holds|stDuhamelConcl_engine|
  inst_duhamelI_proved|duhamelI_` outside `Probe/`; the hub's full build at merge decides.
- O3 (S5-26): the engine has `Q = ∅` only. `STDuhamelII`'s `Q^{(1)} = zeroModeSet {0}` (mixed-sign) conjunct needs a separate
  zero-mode kernel engine (report §(d)). The dispatcher should size S5-26 with this in mind.
- O4: the `duhamelI_absorb` example uses `A = 2^99` so that `ρ = 2 ≤ (2A)^{1/100}` holds. It is a numeric closure check, not an
  endpoint instance, and the endpoint instances use the merged `szB` data.
- O5: the file is 1994 lines, over the ticket's size band 1100/1400/1900 but under the binding stop rule of 2000.

## Verdict

| target | verdict |
|---|---|
| `stDuhamelI_holds : ∀ d, STDuhamelI d` | **PASS** |
| `stDuhamelConcl_engine` (`Q = ∅`, any `P`) | **PASS** |
| registry line `STDuhamelI` deleted | **PASS** |

Overall: **PASS**. No dispatcher sign-off needed for the verdict. O2 is a merge instruction for the hub.
