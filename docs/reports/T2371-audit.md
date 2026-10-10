Auditor model: claude-opus-5-5

# T2371 audit (UN-52b, `Main/BUniv`, `Main/BUnivHolds`), round 1 — Sat Oct 10 05:34:25 UTC 2026

Branch `t/T2371` at 8f08c54 (merge-base e586ec8); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2371-audit1`.

## 1. Diff scope and frozen files
```
$ git diff main...t/T2371 --stat
 RBM3D/Main/BUniv.lean      |  52 +++++++++
 RBM3D/Main/BUnivHolds.lean | 261 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   6 +-
$ git diff main...t/T2371 -- RBM3D/Endpoints.lean RBM3D.lean | wc -l
0
$ git diff --stat e586ec8 main -- RBM3D RBM3D.lean      (main moved to f184210 since the branch point)
(empty)
$ wc -l RBM3D/Main/BUniv.lean RBM3D/Main/BUnivHolds.lean      (stop line 500)
 52 / 261 / 313 total
```
`Test/Axioms.lean` hunks (verbatim summary of `git diff main...t/T2371 -- RBM3D/Test/Axioms.lean`): owner comment of
`UNBUniv` and of `UNOUClaims` extended (comment text only); lines `UNTrLocalBandRow`, `UNDensBandRow` deleted from
`owedProps`; line `UNNormBandRow` unchanged (Amend 1: belongs to T2372). Deletions are allowed: both pins are proved
unconditionally here as closed theorems (§2, §4).

## 2. Statements against the pin
```
$ lake env lean <scratch>/audit_check.lean
  (= check file lines 1-30 with `import RBM3D.Main.BUnivHolds` added, then:)
  example : RBM.Endpoints.T2371Check.BUnivFromLeaves := @RBM.Endpoints.bUniv_of_leaves
  example : RBM.Univ.UNOURow := RBM.Endpoints.unOURow
  example : RBM.Univ.UNDensBandRow := RBM.Endpoints.unDensBandRow
  example : RBM.Univ.UNTrLocalBandRow := RBM.Endpoints.unTrLocalBandRow
  example : RBM.Endpoints.BUniv = RBM.Univ.UNBUniv := rfl
  example : UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail → UNBUniv
    := @RBM.Endpoints.bUniv_holds
  #check / #print axioms ...
output:
Endpoints.bUniv_holds : UNNormBandRow →
  UNL32 → (∀ (d : ℕ), UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail → UNBUniv
'RBM.Endpoints.unOURow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unDensBandRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.unTrLocalBandRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
- `unOURow` (`BUniv.lean:41`): `ouRow_of_pins GUEPhase.g1Row g2bRow`, type `UNOURow` exactly (pin `Pins.lean:793`).
- `bUniv_of_leaves` (`BUniv.lean:45`): definitionally the check file's `BUnivFromLeaves` (example above compiles);
  body is `un_bUniv_of_rows'` with `un_infty1Row'`, `univMainRow`, `unClaimRow`, `unEMCTE2Row`, `jakUywRow`, `unOURow`,
  `greenCorrAll` plugged in — the seven rows the ticket lists, in the argument order of `PinsDens.lean:233`.
- `bUniv_holds` (`BUnivHolds.lean:227`): hypotheses `{UNNormBandRow, UNL32, ∀d UNMLOut d, UNLocAvgBand, UNQueBand,
  UNGUESchurTail}`. Against the ticket's allowed set `{UNDensBandRow, UNTrLocalBandRow, UNNormBandRow, UNL32,
  ∀d UNMLOut d, UNLocAvgBand, UNQueBand, UNGUELocal}`: a subset, with `UNGUELocal` replaced by `UNGUESchurTail`
  through the merged `un_gueLocal_of_tail` (`GUELocalBootstrap.lean:952`), which target 2 permits; the 1a names the
  producer and Amend 1 fixes it (T2373). Conclusion `UNBUniv` is the frozen `BUniv` (rfl above), quantifier order
  `d, 3≤d, 𝔠 𝔡, sz, Admissible, k, 1≤k, κ, 0<κ, E, |E|≤2-κ, O, IsTestFun` unchanged (pin `Pins.lean:177-185`).
- `unDensBandRow`, `unTrLocalBandRow`: closed theorems at the pin types `UNDensBandRow` (`Pins.lean:826`) and
  `UNTrLocalBandRow` (`Pins.lean:842`); `Pins.lean` is not in the diff, so the pins are unchanged.
  `UNTrLocalBandRow` carries `UNLocAvgBand →` inside its own definition, so proving it is unconditional as a Prop.
- Special case (CLAUDE.md §5.6): `bUniv_holds` is conditional on six leaves; it is not unconditional Thm 2.4.
  The ticket asks for exactly this conditional form, and the registry keeps `UNBUniv` owed. Correctly labelled
  in the docstring and prove report.

**Amend 1 checks.**
```
$ git diff main...t/T2371 | grep -nE "^\+.*(unNormBandRow|NormBand|gaussianReal|eigenvalue)"
89:+* `UNNormBandRow`: hypothesis, owed pin; producer T2372 (UN-10a, `Universality/NormBand.lean`,
90:+  `unNormBandRow`);
(remaining hits are the hypothesis type `UNNormBandRow` and `.eigenvalues` inside the `UNBUniv` instance statements)
$ grep -n "^theorem\|^private\|^example" RBM3D/Main/BUnivHolds.lean
55 BUniv_msc_re_im · 63 BUniv_msc_im_ge · 77 BUniv_msc_lip · 119 unDensBandRow · 168 BUniv_card_zd ·
172 BUniv_trace_le · 205 unTrLocalBandRow · 227 bUniv_holds · 239 example · 249 example
```
No `NormBand`-type proof of leaf 11 in the tree. The module docstring (`BUnivHolds.lean:25-33`) names the producers:
`UNNormBandRow` → T2372; `UNGUESchurTail` → T2373; `UNMLOut` → ST-6; `UNLocAvgBand`, `UNQueBand` → MA inputs;
`UNL32` → borrowed (LSY Thm 2.2, DECISIONS §5). Matches Amend 1.

## 3. Hidden hypotheses, vacuity, cycles
- No structure fields: all leaves are `Prop` arguments of the theorem signatures; the new private helpers carry no
  hypotheses beyond explicit arguments (`0 < Im z`, `Im z ≤ 10`, `0 < c`, `c ≤ Im msc`).
- No cycle: `BUniv.lean` imports only merged modules (`Endpoints`, `Universality/*`); `BUnivHolds` imports `Main.BUniv`.
  Every plugged-in row is a merged theorem (check-file Part 2 `#check`s compile, exit 0 above).
- External hypothesis: only `UNL32`, already borrowed (`borrowedProps`); no new external hypothesis is introduced.
  The other remaining hypotheses are other gates' pins (T2372, T2373, ST-6, MA), as allowed by CLAUDE.md §4 step 2.
```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Main/BUniv.lean RBM3D/Main/BUnivHolds.lean | wc -l
0
```

## 4. Compiled nonempty instances
`BUnivHolds.lean:239` and `:249`: two `example`s applying `bUniv_holds hN h32 hML hLoc hQ hT 3 le_rfl (1/6) (1/10)
sz0 sz0_admissible 1 le_rfl (1/10) (by norm_num) E (by norm_num) bump bump_testFun` at `E = 0` and `E = 19/10 = 2-κ`.
This is the data of the frozen `Endpoints.lean:600-605` (`inst_BUniv`): `sz0` (`Sizes.lean:260`: `L = 4(n+1)`,
`W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `d = 3`, `k = 1`, `κ = 1/10`, `𝒪 = bump`. Every deterministic hypothesis
(`3≤3`, `Admissible`, `1≤1`, `0<κ`, `|E|≤2-κ`, `IsTestFun bump`) is discharged; only the six leaves stay hypotheses.
Nondegenerate: `N = (WL)^3 = 2097152` at `n = 0`, `k = 1` nonempty index, window `|E| ≤ 1.9`. Both compile (build §5).
`bUniv_of_leaves`, `unDensBandRow`, `unTrLocalBandRow`, `unOURow` are closed or are instantiated through
`bUniv_holds` (whose body applies `bUniv_of_leaves unDensBandRow unTrLocalBandRow ...`). Accepted.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Main.BUniv RBM3D.Main.BUnivHolds 2>&1 | grep -E "error|warning|Build completed" | tail -1
Build completed successfully (3885 jobs).
$ lake build RBM3D.Main.BUniv RBM3D.Main.BUnivHolds 2>&1 | grep -E "^(error|warning).*Main/BUniv" | wc -l
0
```
Registry pre-check, merged-root simulation (no source edited: a scratch file with all 410 `import` lines of the
branch's `RBM3D.lean`, plus `import RBM3D.Main.BUniv`, `import RBM3D.Main.BUnivHolds`, `#assert_rbm_axioms`):
```
$ lake build <the 410 root modules> RBM3D.Main.BUnivHolds 2>&1 | grep -E "^error|Build completed" | tail -1
Build completed successfully (4181 jobs).
$ lake env lean <scratch>/mergeroot.lean ; echo exit=$?
axiom audit: 10835 theorems, 3186 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
exit=0
```
Without the two new root imports, the branch's own root fails, as expected after the two `owedProps` deletions:
```
$ lake build RBM3D 2>&1 | grep -A1 "axiom audit: 2 premise"
error: RBM3D.lean:413:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of ...
  [RBM.Univ.UNTrLocalBandRow, RBM.Univ.UNDensBandRow]
```
The hub's merge step (A)4 adds the imports before the full build (A)5, so the merge build is the simulation above.

## 6. Name clashes
```
$ for n in unOURow bUniv_of_leaves bUniv_holds unDensBandRow unTrLocalBandRow; do git grep -nE "(theorem|def|lemma) $n\b" main -- 'RBM3D/*.lean' | wc -l; done
0 0 0 0 0
```
Private helpers carry the stem `BUniv_` (§3 (E)).

## 7. Paper deltas
- T2371a (prove report (d)): `UNGUELocal` replaced by `UNGUESchurTail` in `bUniv_holds` through `un_gueLocal_of_tail`
  (a reduction of a Lean pin). Covers the only statement difference from the check-file pin.
- The proved band rows are existing Lean pins, unchanged; `UNBUniv` unchanged. No further difference.

## 8. Observations (no effect on verdict)
- O1. Prove report registry line numbers (`:196-198`) are one off the ticket's (`:195-197`); stated there. No effect.
- O2. Branch history contains ba6da7e with a leaf-11 proof later removed (8f08c54); the final tree has none
  (§2 Amend 1 check). The prove report flags it as a lead for T2372.

## Verdicts
| target | verdict |
|---|---|
| 1. `unOURow`, `bUniv_of_leaves` (`Main/BUniv.lean`) | PASS |
| 2. `bUniv_holds` (+ proved leaves `unDensBandRow`, `unTrLocalBandRow`) (`Main/BUnivHolds.lean`) | PASS |
| 3. Instances (two `example`s at `inst_BUniv` data, `E = 0`, `E = 19/10`) | PASS |
| 4. Registry (`Test/Axioms.lean`: two owed lines deleted for pins proved unconditionally; two owner comments) | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
