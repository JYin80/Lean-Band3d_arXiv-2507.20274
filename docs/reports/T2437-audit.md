Auditor model: claude-opus-5-5
# T2437 audit (round 1): BA-TL TL2a2, `baTwistGridRem_holds`. Mon Oct 12 04:20:03 UTC 2026
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2437-audit1`, detached at `t/T2437` = `1869c73`. Scratch scripts are in the scratchpad `T2437/`.

## Verdict
- Target 1 `baTwistGridRem_holds`: **PASS**.
- Target 2 (instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, then fed to `baTwistGridAssemble_holds 3`): **PASS**.
- Target 3 (registry: none): nothing to check.
- Overall: **PASS**. No dispatcher sign-off needed.

## 1. Statement against the pin
The ticket pins `baTwistGridRem_holds (d : ℕ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridRem d C₀`, where `BATwistGridRem` is the merged def `TwistGrid2.lean:227`. The branch does not touch that file.
```
$ grep -n "^theorem baTwistGridRem_holds" RBM3D/BA/TwistGridRem2.lean
394:theorem baTwistGridRem_holds (d : ℕ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridRem d C₀ := by
$ lake env lean audit.lean     (#check, plus the acceptance example and a consumer-fit example, both elaborated)
baTwistGridRem_holds : ∀ (d : ℕ), ∃ C₀, 0 ≤ C₀ ∧ BATwistGridRem d C₀
exit 0
```
`audit.lean` compiles the following three checks:
- `example : ∀ d : ℕ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridRem d C₀ := baTwistGridRem_holds`. This is the ticket's acceptance check.
- The consumer fit, `(d) (hT : BATwistGridTail d) (hW : BATwistGridWTail d) : BATwistGridMart d`, proved from `baTwistGridRem_holds d` and `baTwistGridAssemble_holds`.
- The ticket's check file:
```
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2437-check.lean; echo $?; grep -c error check.out
check exit 0
0
```
Comparison with the ticket's mathematics:
- **Quantifier order.** `C₀` is fixed per `d` before `κ ε 𝔡 𝔠 sz z`. The witness is `C₀ = 11` (`refine ⟨11, …⟩`, `TwistGridRem2.lean:395`). `CK = 6` comes after the data (`:397`), and every `K` with `N^{CK} ≤ K` eventually is allowed.
- **`CK`.** The ticket "expected" `CK = 36`. A smaller `CK` asks less of `K`, so `6` is the stronger statement. It is not binding in the pin, which is `∃ CK`.
- **Dimension.** There is no `3 ≤ d`; the statement holds for every `d`, as the ticket requires.
- **Clause (i).** Discharged by the merged `baTwistGrid_decomp_ae` (`:399`).
- **Clause (ii).** Proved on the filter `{0 < g₀_n} ∩ {N_n ≥ max 1 (10⁴(1+2/κ)⁶+8)} ∩ {N^6 ≤ K_n}`, which is the pin's `∀ᶠ n`. The proof follows the ticket's route:
  - the per-step bound is `TwistGridRem2_step_le` (`:291`);
  - `ae_all_iff` collects the steps;
  - the sum is `TwistGridRem2_rem_arith`.
- **Losses.** `Z₁ = 10⁴(1+2/κ)⁶N^{10}` and `Z₂ = 8N³` (`:425-427`). Together they give `≤ N^{11}√Δ`, which matches the pin exactly.

## 2. Vacuity, hidden hypotheses, cycles
- **Hypotheses.** The target has none beyond `d`. All hypotheses sit in the merged pin `BATwistGridRem`, which the branch leaves unchanged. No structure carries a proof field.
- **Measure.** The almost-sure statement is over `(baStep2Mat …).Pp = pathP (sz.withLam 0)` (`Step2BA.lean:68`). That measure is a probability measure (`instance isProbabilityMeasure_pathP`, `Path/Walk.lean:94`), so the a.s. clause is not vacuous.
- **Dependencies.** The proof uses only merged results: `BAflow_real`, `BAflow_lam0_window`, `EMn2BA_T0_lt_one`, `BATwistHier_holds`, `condExp_freeze`, `seqP_map_slice`, `pathH_succ`, `EKPins_norm_*`, `BATheta_hasDerivAt`, plus band private lemmas via `open private`. Nothing depends on T2438 or T2439. There is no cycle: `TwistGridRem` imports into `TwistGridRem2`, which imports `TwistGrid2`.
- **External hypotheses.** None.

## 3. Compiled nonempty instances
The datum is `d = 3`, `sz0`, `zSeq`, `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, with window `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`) and grid `K_n = ⌈N_n^{CK}⌉ + 1 ≠ 0`.
- **`TwistGridRem2.lean:468-480`** applies `baTwistGridRem_holds 3`. Every deterministic hypothesis is discharged:
  - `0 < κ, ε, 𝔡` by `norm_num`;
  - `BAFlow` by `flow_sz0`;
  - `0 ≤ s`, `s ≤ t` by `norm_num`;
  - `t ≤ T0` by `t0_sz0`;
  - `K ≠ 0` by `Nat.succ_ne_zero`;
  - `N^{CK} ≤ K` by `Nat.le_ceil`.

  The result is the nonvacuous clause (ii) at this datum. The window is not collapsed, `N` is not 0, and the label index `(Fin 2 → Bool) × Zd 3 (4(n+1))³` is nonempty.
- **`TwistGridRem2.lean:483-491`** feeds the result to `baTwistGridAssemble_holds 3 C₀ hC₀ hRem hTail hW`. The only hypotheses are `BATwistGridTail 3` and `BATwistGridWTail 3`, the pins of T2438 and T2439, which the ticket allows. Every deterministic hypothesis (`D > 0`, window, `K`) is discharged.
- **Matrix level, `TwistGridRem.lean:1056-1075`.** These instantiate `TwistGridRem_envelope`, `TwistGridRem_twK_taylor` and `TwistGridRem_step` at `n = 0`, `u = 1/2`, `Δ = 1/24`, with `M = seqHflowBA` Hermitian, `BAReal` from `BAflow_real`, and `0 < g₀` from `gI_pos`.

All three files compile; the build is in §4.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.TwistGridRem RBM3D.BA.TwistGridRem2; echo exit $?
exit 0
Build completed successfully (4015 jobs).
$ grep -E "^(warning|error)" build.log | grep TwistGridRem | wc -l
0
$ (#print axioms for every `theorem` of both files: 27 names, generated by grep) | sed 's/.* depends on axioms: //' | sort | uniq -c
  27 [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistGridRem_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/TwistGridRem*.lean | wc -l
0
$ git diff --name-status main...t/T2437
A	RBM3D/BA/TwistGridRem.lean
A	RBM3D/BA/TwistGridRem2.lean
$ git diff --stat main...HEAD -- RBM3D/BA/TwistGrid2.lean RBM3D/BA/TwistGrid.lean RBM3D.lean | wc -l
0
$ git grep -nE "TwistGridRem2?_|baTwistGridRem_holds" main -- RBM3D RBM3D.lean | wc -l     (name clash on main)
0
$ wc -l RBM3D/BA/TwistGridRem.lean RBM3D/BA/TwistGridRem2.lean     (stop line 2,000 per file)
    1078 RBM3D/BA/TwistGridRem.lean
     494 RBM3D/BA/TwistGridRem2.lean
```
- **Writable files.** The diff touches only the sole writable files. `RBM3D.lean` is untouched; the hub adds the two imports at merge.
- **Helper names.** Every public helper carries the stem `TwistGridRem_` or `TwistGridRem2_` (rule (E)). The grep listing public declarations shows only stem-prefixed names, plus the pinned `baTwistGridRem_holds`.
- **Full build.** Not run here; the hub runs it at merge.

## 5. Paper deltas
The target is the merged pin `BATwistGridRem` from T2428, with explicit constants. The branch introduces no new Lean/paper statement difference, and the prove report (d)4 proposes no candidate. This agrees with what I found.

## Observations (not RETURN)
1. **`open private` instead of copying.** The two files use `open private` for 44 private names from `Path/OneStep`, `Path/LoopStep`, `BA/TwistGrid` and `BA/TwistPins`. The ticket's 1a (ii) allowed "kept" for band lemmas, and there is a precedent (`BA/Step2BA.lean:35`). The ticket said "copy" for `TwistGrid_second` and `TwistGrid_deriv_spec`, but the proof does not use them. This changes no statement. A later edit to those private signatures would break these files, so the dispatcher may want to record it (prove report (d)1).
2. **The assembly example (`TwistGridRem2.lean:483`) concludes `True`.** Its substance is the elaborated `have` of `baTwistGridAssemble_holds` applied at the datum. This is the same pattern as the merged `TwistGrid2.lean:335`. The substantive instance of target 1 is `:468`.
3. **Prove report (a) says the line prediction and the route table are "not given".** Both appear in the report's Result header (`C₀ = 11`, `CK = 6`, `Z₁`, `Z₂`, route table, line counts 1078 and 494). This is a report-order issue only.
