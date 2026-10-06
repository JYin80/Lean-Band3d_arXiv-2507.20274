Auditor model: claude-opus-5-5

# T2305 audit (round 1) — UN-28 `Universality/GUEPhase/Generator` — Tue Oct  6 15:13:50 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2305-audit1`, detached at `t/T2305` = `9ab0f74`.
Scratch files in the auditor's scratchpad `T2305/` (not committed).

## 1. Scope of the branch

```
$ git diff --name-status main...t/T2305
A	RBM3D/Universality/GUEPhase/Generator.lean
$ git log --format='%h %an <%ae>' main..t/T2305
9ab0f74 Jun Yin <321276894+JYin80@users.noreply.github.com>
5577542 Jun Yin <321276894+JYin80@users.noreply.github.com>
```
Only the sole writable file; `RBM3D/Test/Axioms.lean` untouched (no line expected: no `Prop`-valued def, nothing owed); no merged file touched.

## 2. Statements against the pins (check file `docs/tickets/checks/T2305-check.lean` §2)

(a) Script diff of the target signatures / def bodies against the pins (namespace prefixes stripped, `…V` suffix dropped):
```
$ python3 T2305/sdiff.py
genMatGUE_eq_Of IDENTICAL
egtNGUE_eq_Of IDENTICAL
loopGenGUEOf IDENTICAL
loopGenGUE IDENTICAL
loopGenGUE_one IDENTICAL
def genMatGUEOf body IDENTICAL
def egtNGUEOf body IDENTICAL
def genMatGUE body IDENTICAL
def egtNGUE body IDENTICAL
```
(b) Elaboration check: scratch file = `import RBM3D.Universality.GUEPhase.Generator` + check file §2 copied verbatim
(`diff` of the copied lines: "section2 verbatim") + the five pin examples + the five vocabulary `rfl` examples:
```
example : T2305Check.T2305_genMatGUE_eq_Of := genMatGUE_eq_Of
example : T2305Check.T2305_egtNGUE_eq_Of := egtNGUE_eq_Of
example : T2305Check.T2305_loopGenGUEOf := loopGenGUEOf
example : T2305Check.T2305_loopGenGUE := loopGenGUE
example : T2305Check.T2305_loopGenGUE_one := loopGenGUE_one
example (m : ℂ) (σ : Bool) : mSigOf m σ = T2305Check.mSigOfV m σ := rfl
example (d L W …) : genMatGUEOf d L W m E u M I = T2305Check.genMatGUEOfV d L W m E u M I := rfl
example (d L W …) : egtNGUEOf d L W m E u M I = T2305Check.egtNGUEOfV d L W m E u M I := rfl
example (d L W …) : genMatGUE d L W E u M I = T2305Check.genMatGUEV d L W E u M I := rfl
example (d L W …) : egtNGUE d L W E u M I = T2305Check.egtNGUEV d L W E u M I := rfl
$ lake env lean T2305/pins.lean; echo $?
pins exit 0          (no output)
```
(c) Mathematics (ticket "Targets", §29 checklist):
- `loopGenGUEOf` is the general class-P statement: every `d` (no `3 ≤ d`), every `L, W` with `NeZero`, every `m` with `0 < m.im`, every `E`, every `u < 1`, every Hermitian `M`, every `k` (incl. 0, 1). No `3 ≤ L`, no `0 ≤ u`, no `|E| < 2`. Generator = `½ Σ_c gueVar(c) ∂²_c 𝓛 + ∂_u 𝓛`; RHS = `primRhsGUE` (merged, `W^d` prefactor, `SBgue = L^{-d}`) + `egtNGUEOf` (`W^d Σ_k Σ_{a,b}(tr(G E_a) − m(σ_k)) L^{-d} 𝓛(cut)`), as the ticket's Lemma 2.11 for the GUE profile.
- `loopGenGUE` / `loopGenGUE_one`: binder order `d L W [NeZero L] [NeZero W] E hL hE u hu0 hu1 M hM k hk σ a` = source / consumer UN-44 shape; band pins carry `3 ≤ L`, `0 ≤ u` unused (pinned so; source `_hL`, `_hu0`). They are the `m = mE E` special case of `loopGenGUEOf` and are **not** claimed as the general statement (prove report (d)).
- `genMatGUE_eq_Of` (`rfl`), `egtNGUE_eq_Of` (via `Generator_avgErr` + `rfl`): bridges only.
- `d`-dependence: `W^d`, `L^{-d}`, `N = (WL)^d` only; no scalar `^ 2` (prove report (a)(i), with a wrong-exponent numerical control in (a)(ii)).

Verdict on statements: all five pins and the five vocabulary definitions match exactly.

## 3. Hidden hypotheses, vacuity, cycles

- No structure, no class, no `Prop`-valued def in the file; every hypothesis of every target is in its signature and is a scalar/size/Hermiticity condition (`NeZero L`, `NeZero W`, `0 < m.im`, `u < 1`, `M.IsHermitian`; band: `3 ≤ L`, `|E| < 2`, `0 ≤ u`, `2 ≤ k`). No external hypothesis, so no limit check is owed.
- Public declarations (script):
```
$ grep -nE '^(theorem|lemma|def|noncomputable def|abbrev)' Generator.lean | wc -l   → 10
  (mSigOf, genMatGUEOf, egtNGUEOf, genMatGUE, egtNGUE, genMatGUE_eq_Of, egtNGUE_eq_Of, loopGenGUEOf, loopGenGUE, loopGenGUE_one)
$ grep -c '^private' Generator.lean   → 60   (all unpinned helpers private, prefixed Generator_)
```
- Imports: `Universality.GUEPhase.Bootstrap`, `Universality.Pins`, `Green.Pins`, `Hierarchy.ContractionSecondLoop` — all merged on `main`; no import of `Induction.LoopGenN` or `RBM3D`; no cycle.
- Registry pre-check (no new premise found by the scanner, axiom audit clean):
```
$ printf 'import RBM3D\nimport RBM3D.Universality.GUEPhase.Generator\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean; echo $?
reg exit 0
axiom audit: 8651 theorems, 2833 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 152 (borrowed 1, owed 93, structural 41, refuted 6, superseded 11).
$ grep -nE 'genMatGUE|egtNGUE|loopGenGUE|mSigOf|Generator' reg.out; echo $?
grep-exit 1
```

## 4. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.GeneratorCheck`, file lines 1267–1405)

Data: `d = 3`, `L = 3`, `W = 2` (`Idx 3 3 2`: 216 sites, 27 blocks), `E = 0`, `u = 1/2`; every hypothesis discharged
(`by norm_num` for `3 ≤ 3`, `|0| < 2`, `0 ≤ 1/2`, `1/2 < 1`, `2 ≤ 3`; `by simp` for `0 < Complex.I.im` and `0 < (1/5 + 9/10 I).im`;
Hermiticity by `Generator_diag_isHermitian` / `Generator_M0_isHermitian`, both proved in the file). Applications (grep):
```
1303:  loopGenGUE 3 3 2 0 … diag(2) … 2 le_rfl ![true, false] ![0, 0]
1316:  loopGenGUE 3 3 2 0 … diag(2) … 3 (by norm_num) ![true, false, true] ![0, 0, 0]
1326:  loopGenGUE_one 3 3 2 0 … diag(2) … ![true] ![0]
1335:  loopGenGUE_one 3 3 2 0 … Generator_M0 … ![false] ![1]
1347:  loopGenGUEOf 3 3 2 Complex.I … diag(2) … 2 ![true, false] ![0, 0]
1361:  loopGenGUEOf 3 3 2 (1/5 + 9/10 I) … Generator_M0 … 3 ![true, false, true] ![0, 1, 2]
1372:  loopGenGUEOf 3 3 2 Complex.I … 0 ![] ![]          (extra, k = 0)
1384:  loopGenGUEOf 3 3 2 Complex.I … 1 ![true] ![0]
1394:  genMatGUE_eq_Of 3 3 2 0 (1/2) diag(2) (loopOf ![true, false] ![0, 0])
1402:  egtNGUE_eq_Of 3 3 2 0 (1/2) diag(2) (loopOf ![true, false] ![0, 0])
```
`Generator_M0` (non-scalar Hermitian) is shown nonzero by `Generator_M0_apply : Generator_M0 0 1 = 1`.
Every ticket-listed instance is present; nondegenerate (N = 216, k ≥ 1 for each band endpoint, `Im z_u = 1/2`). The `k = 0` example is extra; the endpoint is also exercised at k = 1, 2, 3.
All ten compile (module build below). No `False` premise, no empty index, no collapsed window.

## 5. Build, axioms, hygiene (audit worktree)

```
$ lake build RBM3D.Universality.GUEPhase.Generator > build.log 2>&1; echo $?   # error/warning lines of Generator.lean other than longLine: none
ℹ [3338/3338] Built RBM3D.Universality.GUEPhase.Generator (10s)
info: RBM3D/Universality/GUEPhase/Generator.lean:1411:0: 'RBM.Univ.GUEPhase.genMatGUE_eq_Of' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1412:0: 'RBM.Univ.GUEPhase.egtNGUE_eq_Of' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1413:0: 'RBM.Univ.GUEPhase.loopGenGUEOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1414:0: 'RBM.Univ.GUEPhase.loopGenGUE' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEPhase/Generator.lean:1415:0: 'RBM.Univ.GUEPhase.loopGenGUE_one' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3338 jobs).
exit 0
$ grep -nE 'sorry|admit|native_decide|^\s*axiom|set_option (maxHeartbeats|debug)|@\[implemented_by|unsafe|opaque' Generator.lean; echo $?
hyg-exit 1
```
Name clash on `main` (`git grep -w <name> main -- 'RBM3D/*.lean' | wc -l`):
```
mSigOf:0 genMatGUEOf:0 egtNGUEOf:0 loopGenGUEOf:0 genMatGUE:0 egtNGUE:0 genMatGUE_eq_Of:0 egtNGUE_eq_Of:0 loopGenGUE:0 loopGenGUE_one:0 GeneratorCheck:0
```
Frozen signatures: no merged file changed (§1). Root import not added (hub's step at merge).

## 6. Paper deltas

Lean/paper differences and their coverage (prove report (d)):
- class-P generalisation `zt E ↦ ztOf m E`, `0 < Im m` (Lean structure) → `T2305a`.
- `(WL)^2 → (WL)^d`, `W^2 → W^d`, `L^{-2} → L^{-d}` (bookkeeping vs RBM2D; matches the paper's `d`) → `T2305b`.
- `LLf ↦ loopL d L W (blockMat d L W M) (zt E u)`; no coupling `g` in the GUE generator → `T2305c`.
- Unused `3 ≤ L`, `0 ≤ u` in the band pins: pinned as in the source; recorded as observation in the report (no statement difference vs paper beyond extra unused hypotheses on the special case; the general `loopGenGUEOf` drops them).
All three candidates proposed as `T2305a–c`; `docs/paper-deltas.md` has no T2305 entry yet (`grep -n T2305` → 0), as expected before merge. Coverage complete.

## 7. Observations (no RETURN)

- O1. Prove report (b) narrative: "the paper TeX was not re-read"; the statement check here is against the ticket's pins and mathematics, which match; no effect on statement/instance/build.
- O2. Prove report B8 lists 14 private helpers whose statements differ from the source after its import map (class-P generalisation, `LLf` removal); they are private and proved, and no target depends on an unproved premise.

## Verdict

| target | verdict |
|---|---|
| vocabulary `mSigOf`, `genMatGUEOf`, `egtNGUEOf`, `genMatGUE`, `egtNGUE` | PASS (`rfl` to the pins) |
| `genMatGUE_eq_Of` | PASS |
| `egtNGUE_eq_Of` | PASS |
| `loopGenGUEOf` | PASS |
| `loopGenGUE` | PASS |
| `loopGenGUE_one` | PASS |

**T2305: PASS.** No dispatcher sign-off needed.
