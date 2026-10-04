Auditor model: claude-opus-5-5

# T2105 audit (S1-22, `RBM3D/Green/MinorGoodLe.lean`): round 1, Sun Oct  4 04:55:58 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2105-audit1`, detached at `t/T2105` = f9b6449 (merge-base with main: e56d95c).
Scratch: `scratchpad/T2105/{sdiff.py,sdiff_lib.py,ax.lean,precheck.lean,a_FIH.lean,a_MGL.lean}`.
The ticket pins no Lean text (the check file has only `#check` lines). The pin is RBM2D `c9a24cf` `Green/FlucIterHigh.lean:751` and `Green/MinorGoodLe.lean:319`, renamed by ST1-COMMON item 2.

## 1. Statements against the pin (script diff, comments stripped, renaming R1 plus `spectralZ/M -> zt/mE`)
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Green/{FlucIterHigh,MinorGoodLe}.lean > a_FIH.lean, a_MGL.lean   (970, 474 lines)
$ python3 sdiff.py a_FIH.lean a_MGL.lean RBM3D/Green/MinorGoodLe.lean
MinorDiffGainUpTo' IDENTICAL
flucGainUpTo'_of_minorDiffGainUpTo' IDENTICAL
MinorGoodLe IDENTICAL
minorGoodLe_of_goodEvent IDENTICAL
minorGoodLe_of_goodEvent_flow IDENTICAL
$ python3 sdiff_lib.py   (every def/abbrev/structure, signature and body)
AgreeOffRows IDENTICAL / greenSetMat, gEnt, minorDiff, qList, greenSetDiagCentered, flucDiagSet,
insertRowEquiv, MinorDiffGainUpTo', MinorGoodLe IDENTICAL
FinDepOffRows DIFF, offRowsCoords DIFF   -- only residual: `Sizes.SeqCoord d` -> `Sizes.SeqCoord sz` (R1; my script did not rename it)
new in 3D: []
$ public-name coverage (theorem|lemma|def|abbrev|structure|instance)
missing in RBM3D: (none)
new in RBM3D: inst_annihilation inst_finDepOffRows inst_flucGain_word inst_gEnt_empty inst_gEnt_insert inst_isUnit_det
  inst_level_one inst_minorGoodLe_flow inst_minorGoodLe_general inst_norm_gEnt inst_qList
```
Elaborated signatures (`lake env lean ax.lean`):
```
@flucGainUpTo'_of_minorDiffGainUpTo' : ∀ {d : ℕ} {sz : RBM.Gauss.Sizes d} {n : ℕ} {E t : ℝ},
  |E| < 2 → t < 1 → ∀ (u : ℝ) {B ρ : ℝ} {M K : ℕ},
    MinorDiffGainUpTo' sz n u (RBM.zt E t) (RBM.mE E) B ρ M K → FlucGainUpTo' sz n u (RBM.zt E t) (RBM.mE E) B ρ M K
@minorGoodLe_of_goodEvent_flow : ∀ {d : ℕ} {sz : RBM.Gauss.Sizes d} {n : ℕ} {u : ℝ} {ω : sz.SeqΩ} {Ψ : ℝ} {M : ℕ} {E : ℝ},
  |E| ≤ 2 → (RBM.zt E u).im ≠ 0 → 0 ≤ Ψ → Ψ ≤ 1 / 4 → 8 * ↑M * Ψ ≤ 1 →
    GoodEvent (RBM.green (sz.seqHflow n u ω) (RBM.zt E u)) (RBM.mE E) Ψ →
      MinorGoodLe sz n u (RBM.zt E u) (RBM.mE E) ω (2 * Ψ) M
```
The conclusion of target 1 is the merged T2096 `FlucGainUpTo'` (FlucIterGain.lean:727). Its body is the same as
`MinorDiffGainUpTo'` (line 751) except for `flucDiag … (k i)` versus `minorDiff … (qList (L i)) (flucDiagSet … (k i))`.
The two statements are general in `d`. They contain no `d = 2` exponent, so no `d`-dimensional exponent had to be supplied.
Grep of the new file: 0 hits for `d = 2|Z2|W \^ 2|zdist2`, and no weight in the code, so D192/§30 does not arise.
The quantifier order is RBM2D's. Both targets are stated at one fixed slice `n` (no `∀ᶠ n`), with `u` real and constrained only by `hz`.

## 2. Vacuity, hidden hypotheses, cycles
- Target 1 has one non-deterministic hypothesis, `MinorDiffGainUpTo'`, which the ticket requires to stay a hypothesis
  (S1-25). It is a plain `def … : Prop` with all of its content visible, not a structure field. It is registered as owed
  (`Test/Axioms.lean`, owedProps). Satisfiability is compiled: `minorDiffGain_szH` proves it at `(B,ρ,M,K) = (64,1,2,2)`
  (gain-free, `ρ = 1`). Limit check (TEAM §8 l.14): the prove report (a) has a numeric `q = 0` scale `B ≈ 0.55·W^{-d/2}`,
  at W = 2, 3, 4 with log-slope −1.56, against d/2 = 1.5. This is consistent with a satisfiable asymptotic form. The gain `ρ < 1` for `q ≥ 1` is S1-25's content.
- Target 2: `GoodEvent` (EntryCore.lean:406) is an explicit hypothesis and is registered structural (`Axioms.lean:212`).
  `MinorGoodLe` is a structure that appears only in the conclusion, so its fields are outputs and not hidden premises.
- No cycle: the file imports `RBM3D.Green.FlucIterGain` (merged T2096) plus two Mathlib modules, and not `RBM3D`.
  Nothing on main imports the new module.
- Registry diff, two lines and nothing else:
```
+   `RBM.Green.MinorDiffGainUpTo', -- … hypothesis of `flucGainUpTo'_of_minorDiffGainUpTo'` (T2105, …   [owedProps]
+   `RBM.Green.AgreeOffRows,   -- … hypothesis of `Xentry_congr_of_not_mem`, `Hflow_submatrix_set_congr` (T2105, S1-22) [structuralProps]
```

## 3. Compiled nonempty instances (same file, built in §4)
`szH : Sizes 3` with `L = 3`, `W = 2`, `lam = 1/2` (index `Z_6^3`, 216 sites). This is a private constant sequence, as in the merged FlucIter/FlucIterGain/LDE checks.
```
1135: example (u : ℝ) : FlucGainUpTo' szH 0 u (zt 0 0) (mE 0) 64 1 2 2 :=
        flucGainUpTo'_of_minorDiffGainUpTo' (E := 0) (t := 0) hE0 (by norm_num) u (minorDiffGain_szH u)
1264: theorem inst_minorGoodLe_flow :
        MinorGoodLe szH 0 (1 / 16) (zt 0 (1 / 16)) (mE 0) 0 (2 * (1 / 8)) 1 :=
        minorGoodLe_of_goodEvent_flow (E := 0) (by norm_num) zt_im_ne (by norm_num) (by norm_num)
          (by norm_num) goodEvent_omega_zero
```
- Target 1: every hypothesis is discharged, including the owed pin (proved gain-free). The data are nondegenerate: `K = 2`
  slots and words of length up to `M = 2`. `inst_flucGain_word` applies the conclusion to a word with `numQ = 2`. `B = 64` is not astronomically large.
- Target 2: every hypothesis is discharged at `ω = 0`, `u = 1/16`, `E = 0`, `Ψ = 1/8`, `M = 1`. `goodEvent_omega_zero` proves
  the event from `G = (16/15)i·1`, `m = i`, `‖G−m‖ = 1/15 ≤ 1/8`, so `G ≠ m·1`. The index set and the levels are nonempty (`|S| ≤ 1`),
  and no premise is `False`. `8MΨ = 1` sits at the boundary of the budget. That is allowed.

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Green.MinorGoodLe
Build completed successfully (3334 jobs).            exit=0
$ lake env lean RBM3D/Green/MinorGoodLe.lean | grep -E "MinorGoodLe.lean:[0-9]+:[0-9]+: (error|warning)"
(no output)
$ lake build RBM3D        (root, branch sources; the module is not yet imported by the root)
info: RBM3D.lean:150:0: axiom audit: 3256 theorems, 1184 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3851 jobs).            exit=0
$ lake env lean precheck.lean      (import RBM3D / import RBM3D.Green.MinorGoodLe / #assert_rbm_axioms)
axiom audit: 3320 theorems, 1197 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Green.MinorDiffGainUpTo': 1 [no certificate]
premises found by scanning: 83 (borrowed 2, owed 65, structural 16).
exit=0
$ lake env lean ax.lean
'RBM.Green.flucGainUpTo'_of_minorDiffGainUpTo'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.minorGoodLe_of_goodEvent_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.minorGoodLe_of_goodEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorGoodLeInst.inst_flucGain_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorGoodLeInst.inst_minorGoodLe_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.MinorGoodLeInst.inst_minorGoodLe_general' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Green/MinorGoodLe.lean ; echo $?
1
$ git diff --stat main...HEAD
 RBM3D/Green/MinorGoodLe.lean | 1326 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    2 +
$ git diff --stat e56d95c main | grep "\.lean"     (main moved since the branch point)
 RBM3D.lean | 3 + ; RBM3D/Induction/EMn2Poly.lean ; RBM3D/Induction/GridDuhamelN.lean ; RBM3D/Path/DuhamelTail.lean
```
Only the two sole writable files are touched, and no frozen signature is changed. The files main changed since e56d95c
(Induction/Path) are not in the import closure of `Green/MinorGoodLe`. The hub's full build at merge is still required.

## 5. Paper deltas
`grep -c T2105 docs/paper-deltas.md` → 0. The report's (d) proposes candidates for each Lean/paper difference:
T2105a (both targets hold for every real `u`, while the paper has `0 ≤ s ≤ t < 1`; a generalization),
T2105b (`MinorDiffGainUpTo'` and `MinorGoodLe` with `2Ψ`, `8MΨ ≤ 1`, `‖(G^{(S)}_{aa})⁻¹‖ ≤ 2` are Lean constructions;
the paper defers `(GavLGEX)` (`3_5:33`) to Lemma 4.1 of `[YY_25]`), and T2105c (the equation numbers (4.x) are `[YY_25]`'s).
Together these cover every difference found in §1. No further candidate is needed.

## Observations (no effect on verdict)
- Prove report (b) gives `main = 90a2761` for the diff. The branch point is e56d95c. The three-dot diff is unaffected.
- ST1-COMMON item 7 names "the MD-1 instance sequence or the T2015 probe's `sz0`/`sz1`". The file uses a private `szH`
  (d = 3, L = 3, W = 2), following the practice of the merged ST-1 files. It is concrete and nondegenerate.
- The registry lines are inserted before the closing element of each list, not at the textual end. These are registry lines only.

## Verdict
| Target | Verdict |
|---|---|
| `flucGainUpTo'_of_minorDiffGainUpTo'` (line 764; RBM2D FIH:751) | PASS |
| `minorGoodLe_of_goodEvent_flow` (line 1019; RBM2D MGL:319) | PASS |
| other ported public declarations (59/59 statements identical after renaming) | PASS |

Overall: **PASS**. No dispatcher sign-off is needed.
