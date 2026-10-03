Auditor model: claude-opus-5-5

# T2006 audit (round 1) — MD-1 fine lattice, size data, fine-lattice Gaussian model, linear forms

Written Sat Oct  3 00:37:21 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2006-audit1`,
detached at `t/T2006` = `9381f0f`. `$SP` = session scratchpad `.../scratchpad/audit2006` (outside the repository).

## 1. Scope, build, hygiene, axioms
```
$ git diff --name-only main...t/T2006
RBM3D/Defs/Sizes.lean
RBM3D/Gauss/FineModel.lean
RBM3D/Gauss/LinearForm.lean
$ git diff --stat 6a555f7 main -- RBM3D RBM3D.lean lakefile.lean lake-manifest.json   # branch base -> main
(empty: no Lean change on main since the branch base)
$ lake build RBM3D.Defs.Sizes RBM3D.Gauss.FineModel RBM3D.Gauss.LinearForm   # exit=0; grep error|warning: none
✔ [3243/3245] Built RBM3D.Defs.Sizes (3.1s)
✔ [3244/3245] Built RBM3D.Gauss.FineModel (5.7s)
✔ [3245/3245] Built RBM3D.Gauss.LinearForm (3.3s)
Build completed successfully (3245 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|implemented_by|extern" <3 files>; echo $?
1
$ lake env lean $SP/Ax.lean   # run_cmd: collectAxioms of every non-internal constant whose module is one of the 3
constants in the 3 modules: 163; union of axioms: [Quot.sound, Classical.choice, propext]; outside the standard three: 0
$ lake env lean $SP/Full.lean   # import RBM3D + the 3 modules; #assert_rbm_axioms
axiom audit: 612 theorems, 216 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...   (exit=0)
```
New public names vs `main` (`git grep` of declaration lines for `Idx blk ofs split splitEquiv Iblk zdistInf Sizes size WO
Bandwidth SizeTendsto Admissible withLam locDomain Bctl svarF idxKey CoordF Ω gvarF PF Xentry Xmat SeqCoord SeqΩ seqGvar seqP
slice seqXmat seqHflow Xlinear coordinateMatrix Hflow linVar glue map_lin measurable_lin sz0 iIndepFun_coord`): 0 hits.
All three files are new; no frozen signature is touched. Unpinned helpers: `fineModel_*` (4, `private`), `checkSizes` and
`check_map_sum_const_mul_coord` (`private`), the instance namespace `RBM.Gauss.SizesInst` (stem-prefixed).

## 2. Statements

### Item 1 — pinned probe text (`5d2a4a8:RBM3D/Probe/T2002Vocab.lean` lines 39–446), verbatim
```
$ diff <(git show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean | sed -n 39,249p) <(sed -n 36,246p RBM3D/Defs/Sizes.lean); echo exit=$?
exit=0
$ diff <(git show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean | sed -n 251,446p) <(sed -n 37,232p RBM3D/Gauss/FineModel.lean); echo exit=$?
exit=0
```
Elaborated types (imports differ from the probe, so the text identity is re-checked after elaboration): `$SP/P.lean` = probe
lines 1–446 + `end RBM.Gauss` + `#check @<name>` (pp.fullNames) for the 57 declarations of lines 39–446 (extracted by script);
`$SP/M.lean` = `import RBM3D.Defs.Sizes, RBM3D.Gauss.FineModel` + `open scoped NNReal` + the same checks.
```
$ lake env lean $SP/P.lean > P.out; lake env lean $SP/M.lean > M.out; diff P.out M.out; echo "exit=$? lines=$(wc -l < M.out)"
exit=0 lines=      79
```
(Without `open scoped NNReal` the only diff lines are `ℝ≥0` vs `NNReal` in `gvarF`, `seqGvar`: notation only.)
Every name of ticket item 1 is among the 57 (`Idx … size_rpow_le_W_rpow`, `svarF … seqXmat_isHermitian`). Mathematical
reading of the pinned definitions (checked against `(eq:variancematrix)`, `(bandcw0)`, `(eq:WO)`, `(Main_DEL_COND)`):
`svarF i j = (W^d)⁻¹ * SBR d L g [i] [j]`; `gvarF` = `S_ii` on the diagonal, `S_ij/2` off it; `PF` = `infinitePi` of
`gaussianReal 0 gvarF`; `Xentry` Hermitian by orientation `idxKey`; `WO 𝔡`: eventually `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`;
`Bandwidth 𝔠`: eventually `N^𝔠 ≤ W`, `N = (W L)^d`; `Sizes` fields `L W lam three_le_L W_pos` only (no hidden hypothesis;
`lam` is a free sequence). Item 1: **PASS** (identical to the pin).

### Item 2 — RBM2D `Model.lean@c9a24cf` lemmas, statement diff after R1–R4
Script (`$SP`, python): each statement up to `:=`, RBM2D side rewritten by R1 (`d.L n`→`sz.L n`, `Seq* d`→`Seq* sz`),
R4 (`Coord/svar/gvar/P`→`CoordF/svarF/gvarF/PF`) and the inserted arguments (`d` before `L W`; coupling `g` at fixed
size, `sz.lam n` along the sequence: the pinned `svarF` carries the coupling, rule R3).
```
P_map_eval 136->270 identical            P_map_restrict 142->277 identical       measurable_Xentry 180->282 identical
integrable_sq_coord 188->291 identical   integral_sq_coord 198->302 identical    integral_normSq_Xentry 210->314 identical
Xmat_add 253->359 identical              Xmat_smul 261->367 identical            Xlinear 270->377 identical
coordinateMatrix 277->384 identical      coordinateMatrix_isHermitian 283->388 identical
Xmat_update 287->393 identical           Xmat_eq_sum_coordinates 300->407 identical  continuous_Xmat 319->427 identical
Hflow 327->437 identical                 Hflow_eq_realSmul 337->446 identical    continuous_Hflow 344->454 identical
Hflow_isHermitian 350->461 identical     measurable_Hflow 357->469 identical     Hflow_sub 363->475 identical
Hflow_sub_apply 369->481 identical       integral_normSq_Hflow 376->488 identical norm_Hflow_sub 387->500 identical
seqP_map_eval 448->516 identical         seqP_map_restrict 452->521 identical    seqHflow_eq_smul 499->527 identical
seqHflow_isHermitian 508->531 identical  measurable_seqHflow_entry 511->536 identical
integral_normSq_seqXmat 517->543 identical  integral_normSq_seqHflow 530->557 identical
seqXmat_eq_sum_coordinates 544->572 identical  seqXmat_update 550->579 identical
statements identical after R1-R4 + inserted (d, g / sz.lam n): 32 / 32
```
(Output re-flowed into columns; one line per lemma in the raw output.) Section variables: RBM2D `(L W) [NeZero L] [NeZero W]`
with `omit … [NeZero W]` on several lemmas; here `(d L W) (g) [NeZero L] [NeZero W]`, `omit [NeZero L]` only, because the
pinned `svarF` itself requires `[NeZero W]` (probe type `svarF : (d L W : ℕ) → ℝ → [NeZero W] → …`). `[NeZero W]` is
discharged by `Sizes.W_pos`; no content change. `seqHflow` keeps the probe's definition (`√u • seqXmat`), and
`seqHflow_eq_smul` is `rfl`, as the ticket directs. Item 2: **PASS**.

### Item 3 — RBM2D `LinearForm.lean@c9a24cf`, whole file with R1
```
$ sed -E 's/Sizes\.SeqCoord d\b/Sizes.SeqCoord sz/g; s/Sizes\.(seqGvar|seqP|SeqΩ) d\b/Sizes.\1 sz/g; s/\(d : Sizes\)/(sz : Sizes d)/g' LF2D.lean > LF2D_R1.lean
$ diff LF2D_R1.lean RBM3D/Gauss/LinearForm.lean   # hunks summarised (raw output is longer)
6c6        import RBM2D.Gauss.Model -> import RBM3D.Gauss.FineModel
13,18c13,23 header docstring
33c38      variable (sz : Sizes d) -> variable {d : ℕ} (sz : Sizes d)
37,38c42,44 line break only in `iIndepFun_infinitePi (P := …)`
42-115     docstring text `seqGvar d c` -> `seqGvar sz c`, and `Sizes.seqP_map_eval d c` / `iIndepFun_coord d` -> `… sz …` (R1 in proofs)
63a70, 134a142, 179a188,189   `set_option linter.{unusedDecidableInType,unusedSectionVars,overlappingInstances} false in`
235-253    private `checkSizes : Sizes 3` (+ `lam _ := 1/2`, coordinates `(0, 0, true)`)
259a271..  new `example`s at `SizesInst.sz0` (section AtSz0)
263,280d   RBM2D's `#print axioms` lines removed
```
No statement line differs beyond R1. Item 3: **PASS**.

## 3. Hidden hypotheses, vacuity, cycles
- `Sizes` has exactly the fields `L W lam three_le_L W_pos`; `Admissible`, `WO`, `Bandwidth`, `SizeTendsto`, `locDomain`
  are separate `Prop` predicates (not structure fields). The ported lemmas carry no hypothesis beyond `NeZero` instances and
  `hu : 0 ≤ u` (as in RBM2D). No external hypothesis; nothing to limit-check.
- Imports: `Sizes` ← `RBM3D.Gauss.Model`, `RBM3D.Defs.Params` (merged); `FineModel` ← `Sizes`; `LinearForm` ← `FineModel`.
  No cycle; every dependency is merged on `main` (§1: no Lean change on main since base; check file `#check`s them).

## 4. Compiled nonempty instances (compile in the build of §1)
`SizesInst.sz0 : Sizes 3`: `L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6}`; at `n = 0`: `L = 4, W = 32,
lam = 1/64, N = 2097152` (`sz0_values`). Nondegenerate: `L ≥ 4`, `W ≥ 32`, `lam → 0` (`sz0_lam_tendsto`), WO window ratio
`lam / W^{-7/5} = 2(n+1)`; no astronomically large witness (`N^{1/6} ≤ W` holds already at `n = 0`).
```
Sizes.lean:331  theorem sz0_admissible : sz0.Admissible (1 / 6) (1 / 10) :=
                  ⟨by norm_num, by norm_num, sz0_tendsto, sz0_bandwidth, sz0_WO⟩      -- every conjunct proved
Sizes.lean:406  theorem sz0_locDomain : sz0.locDomain (1/10) (1/10) 0 ⟨1/2, N_0^(-(4/5))⟩
FineModel.lean:613 example (i j : Idx 3 (sz0.L 0) (sz0.W 0)) : svarF … = svar … (split i) (split j) ∧ ∫‖Xentry‖² ∂PF = svarF …
                   := ⟨svarF_eq_svar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j, integral_normSq_Xentry … i j⟩
FineModel.lean:623 example : ∫ ω, ‖Xentry 3 4 32 ω 0 0‖ ^ 2 ∂(PF 3 4 32 (1/64)) = (32^3)⁻¹ * (1 + 6 (1/64)^2)⁻¹
FineModel.lean:629 example : ∫ ω, ‖Xentry 3 4 32 ω 0 ![32,0,0]‖ ^ 2 ∂(PF 3 4 32 (1/64)) = (32^3)⁻¹ * ((1/64)^2 (1+6(1/64)^2)⁻¹)
FineModel.lean:662 example : (Sizes.seqP sz0).map (Sizes.slice sz0 0) = PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) := Sizes.seqP_map_slice sz0 0
LinearForm.lean:276 example … at sz0 : iIndepFun_coord ∧ hasLaw_coord ∧ hasLaw_const_mul_coord ∧ iIndepFun_const_mul_coord ∧ map_sum_const_mul_coord
```
The four instances the ticket requires (`Admissible` at a `d = 3` sequence, `svarF_eq_svar`, `integral_normSq_Xentry`,
`seqP_map_slice` at it) are present and nondegenerate; the off-diagonal example at two neighbouring blocks gives a nonzero
value (`g ≠ 0`). Further examples (16 in FineModel, 6 in LinearForm) apply the remaining ported lemmas at `Ω 3 4 32` / `sz0`.

## 5. Paper deltas
Pinned text carries the signed T2002a–i (DECISIONS §12; cited in the prove report, not re-proposed). The prove report
proposes **T2006a** (the sample space `Ω`/`SeqΩ` contains independent coordinates that `Xentry` never reads; the law of `X`
is exactly `(bandcw0)`). The ports add no further Lean/paper difference (§2 item 2: only the coupling argument inserted,
which is the paper's `g`). Coverage complete.

## 6. Observations (no statement, instance, build, axiom or delta effect)
- O-a: the prove report b.2 says its type-diff gave exit 0; reproduced above only with `open scoped NNReal` in the import
  side (notation difference otherwise). Consistent.
- O-b: prove report (d) O1/O2 are forward-looking dispatcher questions (public pins of the unported RBM2D simp lemmas;
  whether `Sizes.Admissible` should be registered as structural in the premise scan, given that the public
  `SizesInst.sz0_admissible` makes the scan count it as proved). Neither affects this ticket's statements or merge.
- O-c: RBM2D HEAD (`bcc2c11`) has since deleted some ported lemmas (`git diff --stat c9a24cf HEAD -- …`:
  `2 files changed, 3 insertions(+), 202 deletions(-)`); the ticket pins `c9a24cf`, so no effect.

## Verdict
| Target | Verdict |
|---|---|
| Item 1 `Defs/Sizes.lean` + `Gauss/FineModel.lean` sections 3–4 (probe pin) | PASS |
| Item 2 RBM2D `Model.lean` ports (32 declarations) | PASS |
| Item 3 `Gauss/LinearForm.lean` port | PASS |

T2006: **PASS**. No dispatcher sign-off needed for the merge.
