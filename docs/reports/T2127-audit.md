Auditor model: claude-opus-5-5

# T2127 audit (round 2) — Sun Oct  4 11:17:50 UTC 2026

Branch `t/T2127` = `21c1575` (merge of `main` 0ce09c2 into `4bfcb32`); `main` = `0ce09c2` = merge-base. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2127-audit2` (detached, fresh build cache). Scratch: `scratchpad/T2127/`.

## 1. Build, scope, hygiene

```
$ lake build                         (whole library, runs #assert_rbm_axioms)
Build completed successfully (3877 jobs).   exit 0      error lines: 0   "declaration uses 'sorry'": 0
info: RBM3D.lean:176:0: axiom audit: 3944 theorems, 1357 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 72 (borrowed 0, owed 57, structural 15).
registry: 1 borrowed + 76 owed + 39 structural; 44 registered premise(s) carry nothing yet: [RBM.Loop.KLPT, ...
$ lake build RBM3D.<each of the 16 writable modules>
Build completed successfully (3735 jobs).
$ git diff --name-only main...HEAD | grep -vxE '<the 16 sole writable files>'      -> (none, exit 1)
$ git diff main...HEAD -- RBM3D.lean | wc -l                                       -> 0
$ git diff main...HEAD | grep -nE '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom '   -> (none, exit 1)
$ git grep -nw <name> -- RBM3D | wc -l   (14 deleted names)
ThetaDiffOne 0  ThetaDiffTwo 0  PropTH 0  KTreeRep 0  TwoLoopBounded 0  Prop6Old_false 0  Prop7Old_false 0
PropTH_false 0  thetaDiffOne_fixedL 0  thetaDiffTwo_fixedL 0  propTH_fixedL 0  twoLoopBounded_kTwoLoop 0
KLretire_kTwoFormula 0  KLretire_kThree 0
```

Axioms (`lake env lean scratchpad/T2127/axioms.lean`, exit 0, 25 `#print axioms`):
```
23 x "depends on axioms: [propext, Classical.choice, Quot.sound]": KLretire_twoLoopBounded, kTwoFormula_of_isKLoop,
  kThree_eq_of_isKLoop, pureLoop_two_of_isKLoop, pureLoop_three, stNewKLKAt_holds, KLUniqueInst_{retire_twoLoopBounded,
  kTwoFormula, kThree, pureLoop_two, pureLoop_three}, the 6 KLMolecule_*, KLmSigma_mul_not, Flong_eq_iff_cut,
  prod_leaves_cut, exists_innermost, Flong_subset_diagonals, Flong_subset
'RBM.Loop.sigmaIn' depends on axioms: [propext, Quot.sound]
'RBM.Loop.sigmaOut' depends on axioms: [propext, Quot.sound]
```

## 2. Targets

### Item 1: delete `ThetaDiffOne`, `ThetaDiffTwo`, `PropTH` and the refutations: PASS
`git diff -U0 main...t/T2127` (declaration lines only): `-def ThetaDiffOne`, `-def ThetaDiffTwo`, `-structure PropTH`
(4 fields) in `Interface.lean`; `-theorem Prop6Old_false/Prop7Old_false/PropTH_false`, 5 `-private` helpers, 3 `-example`
in `Pins.lean`. `ThetaDecay`, `ThetaDecayShort`, `ThetaZeroMode` untouched (not in the diff). No remaining use (grep §1);
docstrings in `Basic.lean`, `TreeRep.lean`, `Pins.lean` rewritten. The refutation statements and lines at the base are
recorded in prove report (b) Block 5. The full build shows nothing depended on the deleted names.

### Item 2: delete `KTreeRep`, `TwoLoopBounded`; drop `hbdd` from the four theorems: PASS
Signature script (`scratchpad/T2127/sig.py`: header of each theorem on `main` with the line
`(hbdd : TwoLoopBounded …) :` replaced by `:`, whitespace-normalised, compared to `t/T2127`):
```
kTwoFormula_of_isKLoop: main with '(hbdd : TwoLoopBounded ..) :' -> ':' equals branch: True
pureLoop_two_of_isKLoop: main with '(hbdd : TwoLoopBounded ..) :' -> ':' equals branch: True
kThree_eq_of_isKLoop: main with '(hbdd : TwoLoopBounded ..) :' -> ':' equals branch: True
pureLoop_three: main with '(hbdd : TwoLoopBounded ..) :' -> ':' equals branch: True
```
So each of the four is strictly stronger (one premise fewer, same conclusion). Moved lemma, conclusion vs the deleted body:
```
$ diff <(main TreeRep.lean:172-174 body of TwoLoopBounded) <(t/T2127 Unique.lean:296-297)
<  ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R
>  ∀ T₀ : ℝ, T₀ < 1 → ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T₀, ∀ I : LoopIdx (Zd d L), I.WF → I.length = 2 → ‖K t I‖ ≤ R := by
#check @KLretire_twoLoopBounded : ∀ {d L : ℕ} [inst : NeZero L] {W : ℕ} {g : ℝ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd d L) → ℂ}, ...
```
Same binders as on `main` (`{d L W} [NeZero L] {g} {m} {K} (hK : IsKLoop …)`), only hypothesis `hK`; the non-writable
user `KLWard.lean:1080` builds unchanged. Proof: continuity on compact `[0,T₀]` + finitely many `LoopVec` (no hidden
premise; `IsKLoop` is a definition in `TreeRep.lean`, merged). No cycle: `Unique` imports neither `KLUnique` nor
`KLTreeDeriv` (import-closure script, §3). Wrappers `KLretire_kTwoFormula`/`KLretire_kThree`: deleted; on `main` their
only uses were the two `KLUniqueInst_retire_*` instances (`git grep` outside `KLUnique.lean`: only `docs/tickets/T2025.md`
text). `KLoopBound` untouched (not in the diff).

### Item 3: privates to public: PASS (for the ticket's enumerated lines)
`git diff -U0` of `KLMolecule/KLTree/KLSumZeroWard.lean`: 14 declaration lines, each removed and re-added identical up to
the `private ` prefix (script: `sort | uniq -c` gives 14 pairs). `open private` lines at `KLIndStepA.lean:40-43`,
`KLInduct.lean:79-80`, `KLWardIneq.lean:81` removed. No clash (the full build would fail on a duplicate in `RBM.Loop`).
See O1 for the remaining `open private` matches outside the writable files.

### Item 4: `stNewKLKAt_holds`: PASS
```
theorem stNewKLKAt_holds (d : ℕ) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    STNewKLKAt d κ 𝔡 (stNewKLK_holds d hd κ 𝔡 hκ h𝔡).choose
      (stNewKLK_holds d hd κ 𝔡 hκ h𝔡).choose_spec.choose :=
  (stNewKLK_holds d hd κ 𝔡 hκ h𝔡).choose_spec.choose_spec.2.2
```
Matches the ticket: conclusion `STNewKLKAt` at the `C, δ₀` of the merged `stNewKLK_holds`; hypotheses exactly those of
`STNewKLK` (`3 ≤ d`, `0 < κ`, `0 < 𝔡`); appended at the end of `NewKLK.lean` (before `end RBM.Gauss.Sizes`).

### Item 5: registry: PASS
Script over the three lists of `Test/Axioms.lean` (`main` vs `t/T2127`):
```
borrowedProps 5 -> 1     owedProps 95 -> 76     structuralProps 39 -> 39
removed (23): Gauss.Sizes.STConArg Gauss.Sizes.STContract Gauss.Sizes.STContractPt Gauss.Sizes.STEMn2Poly Gauss.Sizes.STK2decay
  Gauss.Sizes.STKbound Gauss.Sizes.STMollifierEx Gauss.Sizes.STNetLift Gauss.Sizes.STNetLift2 Gauss.Sizes.STNewKLKAt
  Gauss.Sizes.STNewPQ Gauss.Sizes.STQopNorm Gauss.Sizes.STScaleExists Green.GaussIBP Green.GijOmegaSeq
  Green.MinorDiffGainUpTo' Ind.STLoopGenNForm Ind.Step1TargetV3 Loop.KTreeRep Loop.TwoLoopBounded PropTH ThetaDiffOne ThetaDiffTwo
added: []
ticket names not removed: []
removed not in ticket: []
do-not-touch present on main / branch: [('Green.GbEXPV3Theorem', False, False), ('Green.FixedTimeFAThm', False, False),
  ('Green.IBPDetThm', False, False), ('Gauss.Sizes.STStep1', False, False), ('Gauss.Sizes.STEMn2Exp', False, False),
  ('Gauss.Sizes.STGridRepN', True, True)]
```
Every removal is licensed by the pre-check: the full build (which errors on any scanned premise that is unregistered)
passes without these lines (§1). No `LW*` line changed. `certificates := []` (its four entries named deleted theorems).
The round-1 RETURN (stale base) is resolved: merge-base is current `main`, the T2126/T2118 removals are not re-added.

### Item 6: `Test/InterfaceShape.lean`: PASS
Diff removes exactly `thetaDiffOne_fixedL`, `thetaDiffTwo_fixedL`, `propTH_fixedL`, `twoLoopBounded_kTwoLoop` and their
docstring bullets; the other shape checks are untouched.

## 3. Compiled nonempty instances

- `stNewKLKAt_holds`: same-file `example` at `d = 3`, `κ = 𝔡 = 1/10`, all hypotheses by `le_rfl`/`norm_num` (builds).
- `KLretire_twoLoopBounded`, `kTwoFormula_of_isKLoop`, `kThree_eq_of_isKLoop`, `pureLoop_two_of_isKLoop`, `pureLoop_three`:
  `KLUniqueInst_retire_twoLoopBounded`, `KLUniqueInst_kTwoFormula`, `KLUniqueInst_kThree`, `KLUniqueInst_pureLoop_two`,
  `KLUniqueInst_pureLoop_three` (`KLUnique.lean`), at `d = 3, L = 5, W = 2, g = 1/2, E = 0, t = 9/10`; `hK` is the merged
  `KLTreeDerivInst_isKLoop`, `hshort` the proved `thetaDecayShort_holds`, `Im m(+) > 0` by `mE_im_pos`; no premise left.
- Auditor's own check at a second point (compiled in `scratchpad/T2127/axioms.lean`, exit 0):
```
example : KTwoFormula 4 3 1 1 (mSigma (1 / 2)) (fun t I => KLK 4 3 1 1 (1 / 2) t I) :=
  kTwoFormula_of_isKLoop (by norm_num) (by norm_num) (fun s => norm_mSigma (by norm_num) s)
    (KLK_isKLoop 4 3 1 1 (1 / 2) (by norm_num) le_rfl (by norm_num))
```
Import closure (script over `import` lines): `closure(Loop.Unique) contains KLTreeDeriv/KLUnique: False False`;
`closure(Loop.TreeThree) contains KLUnique: False`. See O2 on file placement.

## 4. Hidden hypotheses, vacuity, cycles
No hypothesis added anywhere; no new structure; one structure deleted (`PropTH`). The four theorems lose a premise; the
moved lemma takes only `IsKLoop`. Dependencies are merged (`KLK_isKLoop`, `KLTreeDerivInst_isKLoop`, `stNewKLK_holds`).
No external hypothesis introduced, so no limit check is required.

## 5. Paper deltas
No new Lean/paper statement difference: the deletions remove Lean-only premises (the four theorems move closer to the
paper), `stNewKLKAt_holds` restates the merged `lem:newKLK` form. Trail: prove report (d) proposes `T2127a` for the
`docs/paper-deltas.md` entries naming the deleted declarations (`grep -n` hits at lines 34, 35, 136, 137, 148, 160, 707);
coverage adequate.

## 6. Verdict
All six items: **PASS**. Overall: **PASS**. No dispatcher sign-off required.

## 7. Observations (no verdict effect)
- O1. `grep -rn "open private" RBM3D` is not empty on `t/T2127`: `Loop/KLIndStepB.lean:13` (a comment) and
  `Induction/EMn2Exp2.lean:47-54` (real `open private`, merged by T2118 = `6329018` after the ticket's line list; it opens
  privates of `ContractPt`, `PropTInf`, `KLWard` and others, none of them writable here). The ticket's acceptance grep
  cannot pass within its sole writable files; the enumerated lines are removed. Prove report Block 8 shows only
  `KLIndStepB` because it predates the merge of `main`. Suggest a follow-up ticket for `EMn2Exp2.lean`.
- O2. The instances of the four `Unique`/`TreeThree` theorems and of `KLretire_twoLoopBounded` are in `KLUnique.lean`,
  not the declaring file (the concrete `IsKLoop` witness lives downstream in `KLTreeDeriv.lean`); same placement as the
  merged `KLUniqueInst_retire_*`. Compiled and nondegenerate.
- O3. The unused instance theorems `KLUniqueInst_retire_kTwoFormula/kThree` were renamed `KLUniqueInst_kTwoFormula/kThree`
  (no other use on `main`); `KLUnique.lean` now imports `RBM3D.Propagator.Prop6Hold` (for `thetaDecayShort_holds`). `InterfaceShape`'s `Loop.Unique` import is now unused.
- O4. Prove report (b) Blocks 1, 2, 8, 9 describe `4bfcb32` against `471b643`; the repair section and Block 7 give the
  figures on the current base, which this audit reproduces (3944 theorems, 1357 definitions, `1 + 76 + 39`, 44).
