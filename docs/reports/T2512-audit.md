Auditor model: claude-opus-5-5

# T2512 audit (round 1): V2b, `BA/MainIndGlue` — regime glue of `lem:main_ind_BA` in family form with TL2

`date -u`: Thu Oct 15 06:45:46 UTC 2026. Branch `t/T2512` = 0810e3e2, merge base = `main` 97779231.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2512-audit1` (detached at 0810e3e2). Scratch files (uncommitted, in the
auditor scratchpad `T2512/`): `AuditT2512.lean` (= the check file + `import RBM3D.BA.MainIndGlue` + pin `example`s),
`InstT2512.lean` (`T2512_InstOfRegimes` proved at the data).

## 1. Build, check file, axioms

```
$ lake build RBM3D.BA.MainIndGlue        # in the audit worktree; only warnings are longLine in other files
Build completed successfully (4161 jobs).
$ lake env lean RBM3D/BA/MainIndGlue.lean ; echo $?        -> (no output) 0
$ lake env lean docs/tickets/checks/T2512-check.lean ; echo $?   -> CHECK_EXIT 0
$ lake env lean .../T2512/AuditT2512.lean     # EXIT 0; only output besides two unusedVariables warnings:
'RBM.BA.baMainIndFamTL_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_of_regimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.BA.MainIndGlue.0.RBM.BA.MainIndGlue_extendMember' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.BA.MainIndGlue.0.RBM.BA.MainIndGlue_down' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.BA.MainIndGlue.0.RBM.BA.MainIndGlue_up' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/BA/MainIndGlue.lean   -> (empty)
```

## 2. Statements against the binding pins (script: `example`s in `AuditT2512.lean`, all compile, EXIT 0)

```
example (d : ℕ) : T2512_Mono d := fun R R' h => baMainIndFamTL_mono d R R' h
example (d : ℕ) : T2512_Seq d := fun R₁ R₂ => baMainIndFamTL_seq d R₁ R₂
example (d : ℕ) : T2512_Chain d := baMainIndFamTL_chain d
example (d : ℕ) : T2512_OfRegimes d := baMainIndFamTL_of_regimes d
example (d : ℕ) : T2512_ExtendMember d := fun sz z c₁ u φ hφ z'' h => MainIndGlue_extendMember sz z c₁ u φ hφ z'' h
example (d : ℕ) : T2512_DownShape d := fun sz z τ ι _ φ hφ hcov => MainIndGlue_down sz z τ φ hφ hcov   -- shape
example (d : ℕ) : T2512_UpShape d := fun sz z τ ι _ φ hφ hcov => MainIndGlue_up sz z τ φ hφ hcov       -- shape
#check (baMainIndFamTL_of_regimes : ∀ d, T2512_OfRegimes d)   -- elaborates
```
Signatures read from the file (lines 46-47, 57-58, 82-84, 288-289): each target's type is literally the pin text with the
pin's `∀`/`→` binders made explicit (target 4: binders `h₃ h₁ h₂ h₄` = `STReg5III, STReg5I, STReg5II, STReg5IV` in the pin
order; conclusion `BAMainIndFamTL d STAny`). All targets are for every `d`; the `3 ≤ d` guard, `∃ 𝔠d` before `(𝔠, sz, z)`,
`∀ c₁`, window, times `0 ≤ s < t ≤ T0`, and TL2 come only from the merged def `BAMainIndFamTL` (`MainIndOutBA:60`), which is
not restated. No `STStep5IIIgL` in any statement (Q4/§316): consistent with F3 (the `d > 3` regime-(iii) condition lives in
the producer of `h₃`). Target 7 (terminal) correctly absent (V2O-C1).

Per target: 1 `baMainIndFamTL_mono` = pin; 2 `baMainIndFamTL_seq` = pin; 3 `baMainIndFamTL_chain` = pin;
4 `baMainIndFamTL_of_regimes` = pin; 5 private `MainIndGlue_extendMember` = pin; 6 private `_down`/`_up` = shapes.

## 3. Hidden hypotheses, vacuity, cycles, rule greps (verbatim outputs, on `RBM3D/BA/MainIndGlue.lean`)

```
--- C1  grep -nE 'mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT'          -> (empty)
--- grep -n STStep5IIIgL                                                         -> (empty)
--- X1-C4  grep -nE '^(private )?(noncomputable )?(def|abbrev|structure|instance|class|axiom) '  -> (empty)
--- withLam not inside `seqP (`:
122:`seqP_withLam_reindex_preimage`, `SizesComp:239`). -/          # docstring, lemma name
131:    (fun k s => seqP_withLam_reindex_preimage sz (φ k) 0 ...   # lemma name (hlaw)
141:    (Sizes.integral_reindex (sz.withLam 0) φ hφ.injective        # integral_reindex at the law of seqP (sz.withLam 0)
--- grep -n '· + n₀'                                                             -> (empty)
--- terminal names  grep -nE 'baMainIndFamTL_three|baMLOutTL_three|unMLOutBA_three'   -> (empty)
--- F1 cut, own names excluded: grep -nE 'baMainIndFamTL_(III|I|II|IV)\b|MainIndRegBA|BAStep6R|baStep6' | wc -l  -> 0
```
(The ticket's raw F1 pattern `MainIndFamTL_` also hits this file's own names `baMainIndFamTL_mono/_seq/_chain/_of_regimes`;
no T2511/T2510 name is read.) `∃` hits: only `hcov : ∀ᶠ n in atTop, ∃ k, …` in private helper binders (l.124-265, 306) and
`∃ 𝔠d` in the conclusions of three instance `example`s (l.394, 403, 414); no `∃` in any target statement (U5S-C3 holds via
the merged def).

No new def/structure, so no structure-field hypothesis. Imports: `BA/MainIndOutBA`, `Induction/MainIndRegimes` (both merged
on `main`); the four regime steps are hypotheses of the merged type `BAMainIndFamTL`, so no cycle and no unmerged
dependency. `STAny` is `True` (`Step34Pins:272: def STAny … : Prop := True`), so target 4 is the genuine general statement
(no regime restriction). No external hypothesis is introduced (§8 lesson 14 not triggered).

Name clash: `grep -rn "theorem <name>\b" RBM3D | wc -l` = 1 for each of the four public names (the definition itself).

## 4. Compiled nonempty instances (file l.331-432, all in the module, build passes)

Data (`d = 3`): `sz0` (`L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6} > 0`), main flow `zSeq`,
`κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2 < T0` (`half_lt_t0 : ∀ n, 1/2 < BAflowT0 sz0 zSeq n`),
member `BAzSrc sz0 zSeq (2/3) (17/25)` of `Fam(1/2)` (`MainIndOutBA_mem`), `(con_st_ind)` by `s1Setup_conStInd_const`.

| target | instance (file line) | hypotheses left | discharged at the data |
|---|---|---|---|
| 1 mono | l.393 (`STAny ⊇ STReg5III`) | `h : BAMainIndFamTL 3 STAny`, `Hyp6` | flow, `lam>0`, window, times, regime (`MainIndGlue_reg`), con_st_ind, member |
| 2 seq | l.368 split (hyp-free, = `T2512_InstSeqReg`), l.403 | `h : …STReg5III`, `Hyp6` | as above; cut `m ≡ 3/10` |
| 3 chain | l.413 at `(i,m)=(0,0)` | four regime steps, `Hyp6` | as above |
| 4 of_regimes | l.423 (= `T2512_InstOfRegimes`) | four regime steps, `Hyp6` | as above; regime `STAny` by `trivial` |
| pattern | l.372 (hyp-free, = `T2512_InstPattern`) | none | `STPattern … n = (0,0)` |
| 5 extendMember | l.387 at `φ = (2 ·)` (hyp-free) | none | injectivity, member along `sz0.comp φ` |

Left hypotheses are exactly those ticket item 8 allows: the regime steps (pins of T2511) and the six family conjuncts at
`s` (`Hyp6`, the induction premise). Independent re-check that the pin `T2512_InstOfRegimes` (check file text) is proved:
```
$ lake env lean .../T2512/InstT2512.lean    # example : <T2512_InstOfRegimes text> := by intro …; baMainIndFamTL_of_regimes 3 …
half_lt_t0 : ∀ (n : ℕ), 1 / 2 < BAflowT0 sz0 zSeq n
sz0_lam_pos : ∀ (n : ℕ), 0 < sz0.lam n
EXIT 0
```
Nondegenerate: `d = 3`, `L n ≥ 4`, `s < t` strictly with `t < T0`, non-main member, pattern one class `(0,0)` (regime (iii)),
no `N = 0`, empty index or `False` premise; constants are small rationals.

## 5. Diff scope and frozen signatures

```
$ git diff --name-only main...t/T2512
RBM3D.lean
RBM3D/BA/MainIndGlue.lean
RBM3D/Test/Axioms.lean
$ git diff --stat main...t/T2512 -- RBM3D/Chain RBM3D/Induction RBM3D/Graph | wc -l   -> 0
$ git diff --name-status main...t/T2512 -- 'RBM3D/BA/*'                              -> A RBM3D/BA/MainIndGlue.lean
```
`RBM3D.lean`: one line `+import RBM3D.BA.MainIndGlue` after the last import, before `#assert_rbm_axioms`.
`RBM3D/Test/Axioms.lean`: comment-only edits; the `owedProps` name list is unchanged:
```
$ diff <(main owedProps names) <(t/T2512 owedProps names) && echo identical   -> owedProps name list identical (287)
$ changed lines, comment stripped, +/- stripped | sort | uniq -c
   2 `RBM.BA.STDecayStronggL,   2 `RBM.BA.BAMainIndFamTL,   2 `RBM.BA.BATwistLoopLaw,   2 `RBM.BA.STDecaygL,
   2 `RBM.BA.STLKgL,            2 `RBM.BA.STLmaxgL,         2 `RBM.BA.STLocalEntrygL,   2 `RBM.BA.STLocalMaxgL,
```
These are exactly the ticket's eight owner lines (`:133, :135, :136, :140, :141, :189, :204, :215`); the texts follow the
ticket's wording; `:139`, `:143`, `:186`, `:188`, `:192`, `:193`, `:224` and T2510's lines untouched. No merged statement or
`private` changed. File length 436 lines (< stop line 800).

## 6. Paper deltas

The targets add no Lean/paper statement difference beyond the merged def: family form on `Fam(u)` = D536, BA conclusion
for `d > 3` regime (iii) out of scope = D723. Both present in `docs/paper-deltas.md` (l.1495 D536, l.1803 D723); the prove
report (d) proposes none beyond these. Coverage complete.

## 7. Observations (no verdict effect)

- O1: the ticket's raw F1 cut grep pattern `MainIndFamTL_` matches this ticket's own public names; the intended cut
  (T2511/T2510 names) has 0 hits (§3).
- O2: the full `lake build` (`#assert_rbm_axioms`, registry scan before/after) was not rerun here; the hub runs it at merge.
  `RBM3D.lean` and `RBM3D/Test/Axioms.lean` are a union with T2511 row a at merge (CONTROL H313 (3)).

## Verdict

| target | statement | vacuity / hidden hyp / cycle | instance | build / axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `baMainIndFamTL_mono` | = pin | none | l.393 | ok / std 3 | D536 | PASS |
| 2 `baMainIndFamTL_seq` | = pin | none | l.368, l.403 | ok / std 3 | D536 | PASS |
| 3 `baMainIndFamTL_chain` | = pin | none | l.413 | ok / std 3 | D536 | PASS |
| 4 `baMainIndFamTL_of_regimes` | = pin | none | l.423 | ok / std 3 | D536, D723 | PASS |
| 5 `MainIndGlue_extendMember` (private) | = pin | none | l.387 | ok / std 3 | — | PASS |
| 6 `MainIndGlue_down/_up` (private) | = shapes | none | used in 4 | ok / std 3 | — | PASS |

**T2512: PASS.** No dispatcher sign-off needed.
