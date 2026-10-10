Auditor model: claude-opus-5-5

# T2366 audit (round 1) — Sat Oct 10 00:46:07 UTC 2026

Branch `t/T2366` at f4e179e; merge-base with `main` b1f0988. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2366-audit1` (detached at f4e179e).
Scratch files: `<scratchpad>/T2366/` (`pins_eq.lean` = check file + 8 lines; `axioms.lean`; outputs `*.out`).

## 1. Scope and stop line
```
$ git diff --name-only main...t/T2366
RBM3D/Loop/KLUnique.lean
RBM3D/Loop/Unique.lean
$ git diff main...t/T2366 | grep -E "^[+-]import"
+import RBM3D.Loop.KLTreeDeriv
$ wc -l of the two files (git show <rev>:<file> | wc -l)
main Unique=374 KLUnique=766 total=1140
t/T2366 Unique=459 KLUnique=935 total=1394          (stop line 1560: not reached)
```
Only the two sole writable files. The one new import is `RBM3D.Loop.KLTreeDeriv` (not `RBM3D`, not `BA/`); allowed by the ticket.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Loop.Unique RBM3D.Loop.KLUnique ; grep -E "error|warning" (files of this ticket only)
warning: RBM3D/Loop/KLUnique.lean:71:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Loop/KLUnique.lean:72:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Loop/KLUnique.lean:73:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Loop/KLUnique.lean:76:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3620 jobs).
exit=0
$ git diff main...t/T2366 | grep -E "^\+" | grep -cE "sorry|admit|native_decide|^\+\s*axiom"
0
$ lake env lean axioms.lean   (#print axioms of 24 declarations, list below)
axioms exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
24
$ grep -v "propext, Classical.choice, Quot.sound" ax.out
(no output)
```
Declarations: UniqS RetireS RotS TranslS uniqS_holds retireS_holds rotS_holds translS_holds eq_on_levelS eq_on_level
isKLoop_unique KLretire_twoLoopBounded kTwoFormula_of_isKLoop pureLoop_two_of_isKLoop KLK_unique KLK_translate KLK_rotate
kernel_one_rot_transl kernel_SB_rot_transl UniqueInst_retireS UniqueInst_uniqS KLUniqueInst_uniqS_shifted KLUniqueInst_rotS
KLUniqueInst_translS. (Full `lake build` is the hub's at merge; the edit re-checks the importers of `Unique`/`KLUnique`.)

## 3. Statements: pins (Part 1) and band statements (Part 2 of the check file)
```
$ lake env lean docs/tickets/checks/T2366-check.lean > check.out ; echo exit=$? ; grep -c error check.out
check exit=0
0
$ diff docs/tickets/checks/T2366-check.lean (branch) <main worktree copy> && echo same
same-as-main-worktree
$ tail -8 pins_eq.lean   (appended to a copy of the check file)
example : @RBM.Loop.UniqS = @RBM.Loop.T2366Check.UniqS := rfl
example : @RBM.Loop.RetireS = @RBM.Loop.T2366Check.RetireS := rfl
example : @RBM.Loop.RotS = @RBM.Loop.T2366Check.RotS := rfl
example : @RBM.Loop.TranslS = @RBM.Loop.T2366Check.TranslS := rfl
example : RBM.Loop.UniqS := RBM.Loop.uniqS_holds
example : RBM.Loop.RetireS := RBM.Loop.retireS_holds
example : RBM.Loop.RotS := RBM.Loop.rotS_holds
example : RBM.Loop.TranslS := RBM.Loop.translS_holds
$ lake env lean pins_eq.lean ; echo exit=$?
pins_eq exit=0
```
The four pins are definitionally the dispatcher's pins (`rfl`), and the four `*_holds` theorems have exactly the pin types.
Part 2 of the check file (the 18 band declarations: `eq_on_level`, `isKLoop_unique`, `KLretire_twoLoopBounded`,
`kTwoFormula_of_isKLoop`, `pureLoop_two_of_isKLoop`, `KLK_unique`, `KLK_translate`, `KLK_rotate`, the cut/LoopVec lemmas,
`norm_SB_apply_le`, `norm_mul_mul_sub_le`) elaborates on the branch at exit 0: G1 holds, so no band statement changed.

Public declarations (script: top-level `theorem|def|…` names, `git show main:` vs `git show t/T2366:`, `comm`):
```
RBM3D/Loop/Unique.lean removed: (none)
RBM3D/Loop/Unique.lean added: eq_on_levelS RetireS retireS_holds UniqS uniqS_holds UniqueInst_retireS UniqueInst_uniqS
RBM3D/Loop/KLUnique.lean removed: (none)
RBM3D/Loop/KLUnique.lean added: kernel_one_rot_transl kernel_SB_rot_transl KLUniqueInst_rotS KLUniqueInst_translS
  KLUniqueInst_uniqS_shifted RotS rotS_holds TranslS translS_holds
$ new private helpers (git diff | grep "^+private")
KLUnique_treeEqRhsS_shift KLUnique_isKLoopS_shift KLUnique_isKLoop_shift KLUnique_treeEqRhsS_split KLUnique_treeEqRhsS_rot
KLUnique_rot_eq_on_level KLUnique_MLoop_rot_cons KLUnique_M_rot KLUnique_isKLoopS_rot
$ git grep for definitions of each new public name outside the two files, on t/T2366
UniqS:0 RetireS:0 RotS:0 TranslS:0 uniqS_holds:0 retireS_holds:0 rotS_holds:0 translS_holds:0 eq_on_levelS:0
kernel_one_rot_transl:0 kernel_SB_rot_transl:0 UniqueInst_retireS:0 UniqueInst_uniqS:0 KLUniqueInst_uniqS_shifted:0
KLUniqueInst_rotS:0 KLUniqueInst_translS:0
```
No public name deleted or renamed; private helpers carry the stem `KLUnique_` (§3 (E)). The old §6 band instances
(`KLUniqueInst_unique_*`, `_rotate_*`, `_translate_three`, `_retire_*`, `_kTwoFormula`, `_kThree`, `_pureLoop_*`) lie in
no diff hunk (hunks end at main line 761, where the new block is appended): unchanged, and they compile.

## 4. Hidden hypotheses, vacuity, cycles
- `IsKLoopS` (`Loop/KLTree.lean:828`, merged, not edited): three clauses (ODE `treeEqRhsS` at length ≥ 2 on `T`;
  `K 0 I = M I` at length ≥ 2; `K t ⟨[s],[a]⟩ = m s`). No structure, no extra field; the only facts on `S`/`M` in the
  four pins are the explicit arrows: `UniqS`: `‖S a b‖ ≤ 1`; `RetireS`: none; `RotS`: symmetry, `‖S a b‖ ≤ 1`, rotation
  of `M`; `TranslS`: translation of `S`, `‖S a b‖ ≤ 1`, translation of `M`. These are exactly the ticket's lists.
- Proof routes (read in the files): `uniqS_holds` = strong induction on `eq_on_levelS` (hypothesis `hS` replaces
  `norm_SB_apply_le`); `retireS_holds` uses only `hK.1` (continuity) and compactness, no fact on `S`, `m`, `M`;
  `translS_holds` cases length 0 (`rfl`), 1 (clause 3), ≥ 2 (`KLUnique_isKLoopS_shift` + `retireS_holds` twice +
  `uniqS_holds`); `rotS_holds` cases `a = []` (`rfl`) and length ≥ 2 (`KLUnique_isKLoopS_rot` with `retireS_holds`).
- Band re-derivation (ticket item 4): `isKLoop_unique := uniqS_holds … (SB d L g) m (MLoop d L W m) (norm_SB_apply_le g hL)`;
  `KLretire_twoLoopBounded := retireS_holds …`; `eq_on_level := eq_on_levelS … (SB d L g) …`; `KLK_translate`,
  `KLK_rotate` are one-term applications of `translS_holds`/`rotS_holds` at `SB`, `MLoop`, `KLK_isKLoop`. As specified.
- No cycle: `lake build RBM3D.Loop.Unique` succeeds with the new `import RBM3D.Loop.KLTreeDeriv` (a cycle is a hard
  Lean error). Dependencies are merged (`IsKLoopS`, `treeEqRhsS`, `KLK_isKLoop`, `KLTreeDerivInst_isKLoop`, `SB_*`).
- No external hypothesis is introduced.

## 5. Compiled nonempty instances (same files; all compile, §2)
| Target | Instance | Data | Hypotheses discharged |
|---|---|---|---|
| `retireS_holds` | `UniqueInst_retireS` (Unique.lean) | d=3, L=5, W=2, S=SB 3 5 (1/2), m=mSigma 0, M=MLoop, K=𝒦, T₀=9/10 | family (`KLTreeDerivInst_isKLoop`), `9/10 < 1` |
| `uniqS_holds` | `UniqueInst_uniqS` (K=K'=𝒦) and `KLUniqueInst_uniqS_shifted` (K=𝒦∘shift_{e₁}, K'=𝒦, loop length 3) | same, t=9/10 | `‖S‖≤1` (`norm_SB_apply_le`, `3≤5`), both families, `Icc 0 (9/10) ⊆ Ico 0 1`, `R` from `retireS_holds`, WF, `2 ≤ 3` |
| `rotS_holds` | `KLUniqueInst_rotS` | same, n=3, charges (+,−,+), labels (0,1,2) | symmetry, norm (`kernel_SB_rot_transl`), `M` rotation (`KLUnique_MLoop_rot_cons`), family, `t∈[0,1)`, lengths |
| `translS_holds` | `KLUniqueInst_translS` | same, c=e₁, loop of length 3 | translation, norm, `M` shift (`KLUnique_MLoop_shift`), family, `t`, WF |
| kernel facts | `kernel_one_rot_transl` (S=1, any d, NeZero L), `kernel_SB_rot_transl` (S=SB, 3≤L) | — | all three `S`-hypotheses of `RotS`/`TranslS` |

None is degenerate (L=5, 125 blocks; t=9/10 interior; loops of length 3; `KLUniqueInst_uniqS_shifted` compares two
families that differ as functions). The band endpoints keep the old §6 instances. `UniqueInst_uniqS` has a reflexive
conclusion, but every hypothesis of `uniqS_holds` is discharged there and the non-reflexive case is
`KLUniqueInst_uniqS_shifted`; not a defect.

## 6. Paper deltas
The targets are the band statements of `Def_Ktza` uniqueness / rotation / translation (merged, already covered) restated
over a kernel `S` and initial data `M` with the needed facts as explicit hypotheses (design BA-DK, DECISIONS §144, §172).
The band statements are unchanged (check file Part 2). No new Lean/paper statement difference; report proposes no
`T2366a`, consistent with the ticket ("none expected").

## 7. Observations (no RETURN)
- O1. `KLUnique.lean` lines 71–73, 76 (module docstring added by this ticket) trigger 4 long-line linter warnings even
  though `set_option linter.style.longLine false` follows at line 81 (the docstring precedes it). Style only.
- O2. `Unique.lean` now imports `KLTreeDeriv`; every importer of `Unique` sees it. The prove report records a full
  `lake build` success at f4e179e; the hub's full build at merge is the binding check.
- O3. `eq_on_levelS` is a new public intermediate (allowed by the ticket) with no direct instance; it is exercised
  through `uniqS_holds`'s instances.
- O4. No `IsKLoopS` family at `S = 1` is built (that is K03's `BAKexists`); only the kernel hypotheses are compiled at
  `S = 1`, as the ticket requires.

## Verdicts
| Target | Verdict |
|---|---|
| Pins `UniqS`, `RetireS`, `RotS`, `TranslS` | PASS (rfl against check file) |
| `uniqS_holds`, `retireS_holds` | PASS |
| `rotS_holds`, `translS_holds` | PASS |
| Re-derivation G1 (Part 2, 18 band declarations) | PASS (check file exit 0; no public name removed) |
| Instances `kernel_one_rot_transl`, `kernel_SB_rot_transl`, `*Inst_*` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
