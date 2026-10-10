Auditor model: claude-opus-5-5

# T2365 audit (round 1): BA-K09a, `indStepAbs_of` over abstract data, in place

Written Sat Oct 10 01:12:33 UTC 2026 (`date -u`); worktree `RBM3D-wt/T2365-audit1` at b74e5fd; `S` = scratchpad `T2365/`.

## 1. Diff scope, size, hygiene

```
$ git diff --name-only main...t/T2365
RBM3D/Loop/KLIndStepA.lean
RBM3D/Loop/KLIndStepB.lean
$ git merge-base main t/T2365 ; git diff --stat 1fe7b7f main -- <the two files>
1fe7b7fd4d4b711f346bd3292b5118ac8500af2b
(empty: neither file changed on main since the merge base)
$ wc -l main vs branch
KLIndStepA.lean main=1474 branch=1659 ; KLIndStepB.lean main=947 branch=1043   (total 2702 <= stop line 3121)
$ git grep -E 'sorry|admit|native_decide|axiom' t/T2365 -- <the two files> | wc -l   -> 0
$ git diff main...t/T2365 | grep -E '^[+-]import'   -> (none)
```

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Loop.KLIndStepB
⚠ [3629/3630] Built RBM3D.Loop.KLIndStepA (14s)
⚠ [3630/3630] Built RBM3D.Loop.KLIndStepB (12s)
Build completed successfully (3630 jobs).
exit 0
(warnings in the two files: style.longLine only; main's versions already have >100-char lines)
$ lake env lean S/axioms.lean
(14 declarations; every line ends `depends on axioms: [propext, Classical.choice, Quot.sound]`:)
IndStepAbs SigSumZeroAbs SigDecayAbs IndStepTH KLindStepAt_iff indStepAbs_of sigSumZeroAbs_band
sigDecayAbs_band indStepTH_band KLindStepAt_holds KLindStepPin_holds KLindStep_alt KLindStep_nonAlt
KLindStep_nonAlt_noloss
$ lake env lean S/axioms.lean > ax.txt; wc -l < ax.txt; grep -v 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' ax.txt | wc -l
14
0
```

## 3. Statements against the pins (targets 1-3)

`S/pins_rfl.lean` = the check file (Part 1 + Part 2) followed by:
```
example : @RBM.Loop.IndStepAbs = @RBM.Loop.T2365Check.IndStepAbs := rfl
example : @RBM.Loop.SigSumZeroAbs = @RBM.Loop.T2365Check.SigSumZeroAbs := rfl
example : @RBM.Loop.SigDecayAbs = @RBM.Loop.T2365Check.SigDecayAbs := rfl
-- IndStepTH (a structure): Iff field-wise both ways, and each field type equal by rfl:
--   have e1 : type_of% h.transl = type_of% h'.transl := rfl   ... e7 (rowSum), h : branch, h' : check copy
example : T2365Check.IndStepAbsOfStmt := by intro ...; exact indStepAbs_of ... ⟨hTH.transl, ..., hTH.rowSum⟩ hD hS
example : ∀ (d n : ℕ) [NeZero n] (gmax : ℝ) {ι : Type} (L ...) ..., 3 ≤ d → 3 ≤ n → (∀ i, 3 ≤ L i ∧ 0 < g i ∧
    g i ≤ gmax ∧ 0 ≤ t i ∧ t i < 1) → RBM.Loop.IndStepTH d L g t TH → T2365Check.SigDecayAbs d n L Sig →
    T2365Check.SigSumZeroAbs d n L g t Sig → T2365Check.IndStepAbs d n L (fun i => Bparam ..0) Sig TH
  := @RBM.Loop.indStepAbs_of        -- binder order of IndStepAbsOfStmt, term-mode, no wrapping
example ... : KLindStepAt d n κ gmax ↔ T2365Check.IndStepAbs (ι := KLPar κ gmax) ... := RBM.Loop.KLindStepAt_iff d n κ gmax
```
```
$ lake env lean S/pins_rfl.lean ; echo exit $?
exit 0          (no error lines)
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2365-check.lean   (on the branch)
exit 0 ; error lines: 0
$ literal ticket protocol for the structure pin (S/lit.lean)
lit.lean:154:66: error: Type mismatch   -- @RBM.Loop.IndStepTH = @T2365Check.IndStepTH := rfl
lit.lean:155:50: error: Type mismatch   -- T2365Check.IndStepAbsOfStmt := @RBM.Loop.indStepAbs_of
```
The two literal failures are forced by the protocol, not by the branch: `IndStepTH` is a `structure`, and the
check file's copy is a second, distinct inductive type, so no implementation can make them `rfl`-equal.
All seven field types are definitionally equal (`rfl` per field, above) and the field-wise `Iff` compiles; with
the branch's own `IndStepTH`, `@indStepAbs_of` has exactly the pinned type. `KLindStepAt_iff` is `Iff.rfl`.
- Target 1 (four pins): **PASS** (three by `rfl`, `IndStepTH` field-by-field definitional equality).
- Target 2 (`KLindStepAt_iff`): **PASS**.
- Target 3 (`indStepAbs_of`): **PASS**. Hypotheses: `3 ≤ d`, `3 ≤ n`, the range conjunction and the three
  bundles, nothing else (signature in the prove report (b), lines 173-178, matches the file). No `0 < gmax`,
  no nonempty `ι`: these are weakenings of the hypothesis set, so the statement is at least the pinned one.

## 4. Band instances and G1 re-derivation (targets 4-5)

Public-declaration statements, main vs branch (`S/decls.py`, comments stripped, text up to `:=`):
```
KLIndStepA public main 38 branch 50
  removed: []
  added: ['IndStepTH', 'KLIndStepA_crude_abs', 'KLIndStepA_decay_le_zero', 'KLIndStepA_f12_abs',
   'KLIndStepA_leaf_abs', 'KLIndStepA_nonAlt_abs', 'KLIndStepA_slice_vanish', 'SigDecayAbs', 'SigSumZeroAbs',
   'indStepTH_band', 'sigDecayAbs_band', 'sigSumZeroAbs_band']
  statement changed: []
KLIndStepB public main 5 branch 8
  removed: []
  added: ['IndStepAbs', 'KLindStepAt_iff', 'indStepAbs_of']
  statement changed: []
```
Elaborated types (catches `variable`-block changes; the diff moves `variable {d : ℕ} {κ gmax : ℝ}` blocks):
```
$ S/checks.lean = `#check @RBM.Loop.<name>` for all 43 public names of the two files on main
$ (main oleans) lake env lean S/checks.lean > checks_main.txt ; (audit worktree) ... > checks_branch.txt
$ diff checks_main.txt checks_branch.txt && echo identical
43 #check @name outputs: identical main vs branch
```
Band instances (`KLIndStepA.lean:1090, 1098, 1106`): `sigSumZeroAbs_band`/`sigDecayAbs_band (n) [NeZero n]
(hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ) (hg : 0 < gmax)`, `indStepTH_band (hκ : 0 < κ) (hPT : KLPT d κ gmax)`, all
at `(ι := KLPar κ gmax)`, `fun p => p.L / p.g / p.t`, `Σ^{(∅)} = KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅`, `thetaEdge`.
`KLindStepAt_holds` (`KLIndStepB.lean:906-912`) is `(KLindStepAt_iff d n κ gmax).2 (indStepAbs_of ... (indStepTH_band hκ hPT) ...)`,
statement unchanged (in the 43-name diff). `KLindStepPin_holds`, `KLindStep_alt`, `KLindStep_nonAlt`: unchanged.
- Target 4: **PASS** (data as pinned). Target 5 (G1): **PASS**; no public name removed/renamed; check Part 2 exit 0.

## 5. Vacuity, hidden hypotheses, cycles

- The only structure is the pinned bundle `IndStepTH`, an explicit hypothesis of `indStepAbs_of`; its fields are the
  dispatcher's pin (field types equal to the check file, §3). No field carries the conclusion.
- Non-vacuity of the bundles: `indStepTH_band` (from `KLPT`), `sigDecayAbs_band` (from `KLmolecule_holds`) and
  `sigSumZeroAbs_band` (from `KLsumZero_weighted`, `KLSigmaPi_reflect`, `KLIndStepA_SigmaPi_add_const`) are merged
  band results; only `KLPT` (gate PT, already a hypothesis of every merged §7 example and of `KLindStepPin`) remains.
- No cycle: no new import; band instances use merged lemmas only. No new external hypothesis (no limit check due).

## 6. Compiled nonempty instances (same files, built in §2)

- `KLIndStepB.lean:1018-1039`: `example (hPT : KLPT 3 1 1)` applies `indStepAbs_of 3 4 1` at `ι = KLPar 1 1` with
  `indStepTH_band one_pos hPT`, `sigDecayAbs_band 4 ...`, `sigSumZeroAbs_band 4 ...`, `τ = 1`, range discharged by
  `⟨p.hL, p.hg0, p.hg1, p.ht0, p.ht1⟩`, then evaluates at `KLinstPar` (`d = 3`, `L = 5`, `g = 1/2`, `E = 0`,
  `t = 9/10`), `n = 4`, `a = ![0,1,2,3]`, for alternating `σ` (root 1, case (ii)) and `σ = (+,+,+,-)` (root 2, case (i)).
- `KLIndStepA.lean:1629-1655`: the three band bundles evaluated at `KLinstPar` (translation, row sum of a long edge,
  decay of `Σ`, reflection at `c = 1+1`, signed and `Q = 4` weighted slice estimates at root 1, `x = 0`).
- Nondegenerate: `n = 4`, 125 sites, `0 < t < 1`, `g > 0`; the only hypothesis left is `KLPT 3 1 1` (another gate's pin,
  allowed by CLAUDE.md §4 step 2). **PASS**.

## 7. Paper deltas

The weighted sum-zero interface is D194 (`docs/paper-deltas.md:787`), cited by the pin; the `(|s|+1)`-weighted
`(eq:f12)` is D193 (`:783`). `indStepAbs_of` restates `(eq:ind-step-bound)` over abstract data with the same
conclusion as `KLindStepAt` (identical by `Iff.rfl`); `IndStepTH` uses properties 6, 7 at `c = 1/2` only, which
weakens the hypothesis. No new Lean/paper statement difference; no `T2365a` needed. **PASS**.

## 8. Observations (no statement, instance, build, axiom or delta effect)

1. The ticket's literal protocol `example : @RBM.Loop.IndStepTH = @T2365Check.IndStepTH := rfl` (and through it
   `IndStepAbsOfStmt := @indStepAbs_of`) cannot compile for any implementation, because a `structure` copied into
   a second namespace is a distinct inductive type. Checked here by field-wise definitional equality instead (§3).
   For future pins of structures, the check file should `#check` the target's structure or state field equalities.
2. `indStepTH_band` takes `(hκ : 0 < κ)` besides `hPT` (ticket text lists `hPT` only). It is needed to get
   `|E| ≤ 2` from `KLPar.hE : |E| ≤ 2 - κ` for `KLIndStepA_thetaEdge_long`; every consumer (`KLindStepAt_holds`,
   the other two band instances) already carries `hκ`. Instance-level only; the pinned statements are unaffected.

## Verdict

- 1 pins `SigSumZeroAbs`, `SigDecayAbs`, `IndStepTH`, `IndStepAbs`: PASS
- 2 `KLindStepAt_iff`: PASS
- 3 `indStepAbs_of`: PASS
- 4 `sigSumZeroAbs_band`, `sigDecayAbs_band`, `indStepTH_band`: PASS
- 5 G1 re-derivation of `KLindStepAt_holds`, band statements unchanged: PASS

T2365: **PASS**. No dispatcher sign-off needed; the hub's full `lake build` at merge remains required.
