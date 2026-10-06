Auditor model: claude-opus-5-5

# T2277 audit (round 1): BA-S3 `RBM3D/BA/Step1Fam.lean`
Tue Oct  6 10:13:44 UTC 2026 (`date -u`). Worktree `RBM3D-wt/T2277-audit1` detached at `t/T2277` = 4632a75 (base 66cddb4).

**Verdict: PASS** (all targets 1-12 and the listed instances). No dispatcher sign-off needed.
## 1. Scope of the diff, hygiene

```
$ git diff --name-only main...t/T2277
RBM3D/BA/Step1Fam.lean
RBM3D/Test/Axioms.lean
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/BA/Step1Fam.lean | wc -l
       0
$ grep -n "^import" RBM3D/BA/Step1Fam.lean
6:import RBM3D.BA.Step1
$ git diff main...t/T2277 -- RBM3D/Test/Axioms.lean   (content lines only)
-   `RBM.BA.BAFlowMember, -- finite modification of a member of `Fam(0)` is a `BAFlow` sequence (route (A), ...
+   `RBM.BA.FlowFM.EvEq, -- two flow carriers agree for large `n` (T2277, BA-S3, portmap P.2: structural)
$ owedProps entries: main / t/T2277
149
148
```
Only the sole writable files; no frozen signature touched; `PrecL_congr` used, not redeclared (`Step1Fam.lean:207,213`).

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.Step1Fam
✔ [3757/3757] Built RBM3D.BA.Step1Fam (12s)
Build completed successfully (3757 jobs).
exit 0
$ lake build RBM3D.Test.Axioms | tail -1; lake env lean precheck.lean; echo exit $?  (import RBM3D; import RBM3D.BA.Step1Fam; #assert_rbm_axioms)
Build completed successfully (2 jobs).
exit 0
axiom audit: 8113 theorems, 2645 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
$ grep -c BAFlowMember scratchpad/T2277/precheck.out
0
```
`#print axioms` of 32 declarations (every target theorem and every named instance, appended to `stmts.lean`, §3):
```
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" stmts.out; grep -c "" stmts.out
32
32
$ grep -E "inst_baStep1' |baStep1_holds|BAStep1_of_parts" stmts.out
'RBM.BA.BAStep1_of_parts'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1FamInst.inst_baStep1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (check file `docs/tickets/checks/T2277-check.lean`)

`stmts.lean` = the check file with `import RBM3D.BA.Step1` replaced by `import RBM3D.BA.Step1Fam` and `#check` lines dropped,
followed by 21 `example`s:
```
example : @RBM.BA.BAzSrc = @RBM.BA.T2277Check.BAzSrc := rfl            -- also BAtauS, cκ, BAStep1, BALmaxFromLK
example (d : ℕ) : RBM.BA.T2277Check.BAStep1_of_parts'_stmt d := RBM.BA.BAStep1_of_parts' d
example (d : ℕ) : RBM.BA.T2277Check.baStep1_holds_stmt d := RBM.BA.baStep1_holds d
example (d : ℕ) : RBM.BA.BAFlowMember d := RBM.BA.BAFlowMember_holds d
example (d : ℕ) : RBM.BA.T2277Check.BAzSrc_spec_stmt d :=
  fun sz z z' c₁ κ a b c e s u n f g h i j k l m o => RBM.BA.BAzSrc_spec sz z z' c₁ κ a b c e s u n f g h i j k l m o
-- likewise `fun … =>` for BAFamZ_closed, BAFamZ_mono_max, BAConArgLoop''_congr, BAConArgVec_congr, STLmaxgL_max;
-- section 4: mS_im_ge, t0_sz0_ge, sz0_win, inst_conArg_lt, inst_BALmaxFromLK, inst_baStep1, inst_baStep1_low
$ lake env lean scratchpad/T2277/stmts.lean ; echo exit $?
exit 0
```
Every pinned statement (targets 2-4, 6-10, `BAFlowMember_holds` at the merged pin, vocabulary, the seven section-4
instance statements) elaborates against the check file, binders in the pinned order.

Verbatim targets and `FlowFM.EqAt` against the probe (`git show 96e4087:RBM3D/Probe/T2205Pins.lean`; `t/T2205` = 96e4087),
whitespace-normalised, statement = text before the first `:=`:
```
$ python3 scratchpad/T2277/vdiff.py probe.lean RBM3D/BA/Step1Fam.lean <36 names>     (condensed; long lines cut at ...)
<32 lines> <name>: stmt EQUAL; whole EQUAL   for BAm_self_of_im_pos BAtauS BAzSrc BAlamS_eq BAflowT0_congr BAflowEs_congr
  FlowFM.EqAt FlowFM.EvEq FlowFM.EqAt.GM, the ten ST*gL_congr, baFM_eqAt baFMz_eqAt BAlamS_congr HighProbAt_congr PrecL_ite
  BAStep1 BALmaxFromLK Bctl_le_one_of_conStInd BAFamZ_ite cκ cκ_pos cκ_le_one BAmember_dom_at
BAFlowMember_holds: stmt EQUAL; whole DIFF
BALmaxFromLK_holds: stmt EQUAL; whole DIFF
BAConArgVec_congr: stmt DIFF; whole DIFF
  probe: theorem BAConArgVec_congr (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} (h : ...) ... : BAConArgVec sz z₁ s t ↔ ...
  file : theorem BAConArgVec_congr (sz : Sizes d) (z₁ z₂ : ℕ → ℂ) (h : ...) ... : (BAConArgVec sz z₁ s t ↔ ...)
STLmaxgL_max: stmt DIFF; whole DIFF
  probe: theorem STLmaxgL_max (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s : ℕ → ℝ) (c : ℝ) ...
  file : theorem STLmaxgL_max (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s : ℕ → ℝ) (c : ℝ) ...
```
The two statement differences are binder explicitness only, as the check file pins them (compiled above).

Mathematics of the generalized targets (ticket targets 2-3, §86): `BAzSrc_spec` has `0 < t₀(z)`, `u n ≤ max t₀(z) (s n)` and
first conclusion `min t₀(z) (s n) ≤ τ''`, exactly the ticket's text; `BAFamZ_closed` has `∀ n, u n ≤ max t₀ (s n)`,
conclusion `BAFamZ … s (BAzSrc …)`; `BAStep1` keeps `0 ≤ s`, `s ≤ t₀`, `s < t ≤ t₀`, `0 < c₁ ≤ 1/2`, `0 < 𝔠d ≤ 1/100`,
`∀ n, 0 < lam n`, `BAWinBulk`, the family premise at `s` and `STConStInd`, conclusion for every `z' ∈ Fam(t)` (§29
checklist of the ticket: matches). `baStep1_holds : BAGbEXPii d → BAGbEXPij d → BAStep1 d` is the §90 conditional form;
it is a conditional assembly, not an unconditional Step 1 (the report says so, (b) narrative).

## 4. Hidden hypotheses, vacuity, cycles

- The only new structure is `FlowFM.EqAt` (seven field equalities `L K G M S eta m` at index `n`, `Step1Fam.lean:187-194`);
  it appears only as a premise of congruence lemmas and is concluded by `baFM_eqAt`/`baFMz_eqAt`. `FlowFM.EvEq` is
  registered as structural (diff above), as the ticket instructs.
- Hypotheses of `BAStep1` are merged definitions (`BAFlow`, `BAWinBulk` (structural, registered), `BAFamZ`, `STConStInd`)
  and the owed pins `STKboundgL`, `STLKgL`, `STLocalMaxgL` (family premise; owed per §91 (3)).
- `baStep1_holds` depends on merged `BAFlowMember_holds` (this file), `BALmaxFromLK_holds` (this file),
  `BATrivialLmax_holds`, `baConArg''_holds`, `baBootstrap'_holds` (merged on `main`); no cycle. The only open inputs are
  the owed `BAGbEXPii/ij` (other gate BA-G6), as allowed by CLAUDE.md §4 step 2.
- Name clash grep (63 public names, short names, `RBM3D/` minus probe): one hit, `FlowFM.EqAt.GM` vs `FlowFM.GM`
  (`FlowPins.lean:353`), different full names; not a clash.

## 5. Compiled nonempty instances (same file, namespace `RBM.BA.Step1FamInst`)

Data: `d = 3`, `sz0` (`lam > 0`, `sz0_lam_pos`), `zSeq`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`, `c₁ = 1/3`.
| endpoint | instance | hypotheses left |
|---|---|---|
| `BAzSrc_spec` | examples `:847` (case `u ≤ t₀`, `(2/3,17/25)`), `:862` (case `t₀ < u`, `c₁ = 1/10`, `s = u = 9/10`, with `:877` `t₀ < 9/10`) | none |
| `BAFamZ_closed` | `inst_BAFamZ_closed` `:820`, examples `:827`, `:839`, `:880` | none |
| `BAFamZ_mono_max` | example `:880` | none |
| `BAConArgLoop''_congr`, `BAConArgVec_congr` | examples `:890`, `:894` along `zMod` (differs from `zSeq` for `n < 3`) | none |
| `STLmaxgL_max` (helper) | example `:946`; used inside `baStep1_holds` (instances below) | `STLmaxgL` at `2/3` |
| `BAFlowMember_holds` | `inst_BAFlowMember` `:952` (member `BAzSrc sz0 zSeq (2/3) (17/25)`) | none |
| `BALmaxFromLK_holds` | `inst_BALmaxFromLK` `:962` (`τ = sI`, `sz0_tendsto`, `Bctl ≤ 1` via `s1Setup_conStInd_const`) | `STKboundgL`, `STLKgL` (owed pins) |
| ConArg source (target 9 ingredient) | `inst_conArg_lt` `:921` (`baConArg''_holds 3`, `(2/3,17/25)`, `s < u`) | none |
| `baStep1_holds` / `BAStep1_of_parts'` | `inst_baStep1` `:982` (`(1/2,2/3)`), `inst_baStep1_low` `:1000` (`(0,1/16)`, §86 case) | `BAGbEXPii 3`, `BAGbEXPij 3`, family premise (owed) |
| T2269 consumer | `inst_baBootstrap'_full` `:1018` (`hmem := BAFlowMember_holds 3`, `hwin := sz0_win_third`) | `BAGbEXP*`, `STKboundgL/STLKgL/STLocalMaxgL` at `zSeq` |

All deterministic premises (`0 ≤ s`, `s ≤ t₀`, `s < t`, `t ≤ t₀`, the window `sz0_win_third`, `STConStInd`, `BAFlow`
`flow_sz0`, `lam > 0`) are discharged by terms in the file (`:982-1016`); the `STStep1*` conclusions are at the member
`zSeq ∈ Fam(t)` (`BAFamZ_main`). No `N = 0`, empty index, collapsed window or `False` premise; `N ≥ 2^21` is the band
instance's, not an astronomically large witness for a hypothesis. Section-4 instance statements equal the check file
(§3 above). `BAStep1_of_parts'` is exercised through `baStep1_holds` (term `:695`).

## 6. Paper deltas

- Family form of Step 1 (`7_8:1987-1990` on `Fam(u)`, the window, ConArg with `Im m(E,g_s) ≥ κ`): existing **D536** (T2205b).
- Unused premises of `BABootstrap'` supplied by BA-S3: existing **D581** (T2269a-c); refined by proposed **T2277b**.
- §86 ConArg range `[max(s,1−c₁), max(t,1−c₁)]` and the case `t₀(z) < 1 − c₁` with `u = s₁` (generalized `BAzSrc_spec`):
  proposed **T2277a** (prove report (d)).
- Conditional `baStep1_holds` (owed `BAGbEXPii/ij`): DECISIONS §90. Every Lean/paper difference found is covered.

## 7. Observations (no effect on verdict)

O1. Report (b) quotes `8096 theorems`; here the pre-check prints `8113` (cache of a later `main`). O2. The hub must add
`import RBM3D.BA.Step1Fam` at merge, else `#assert_rbm_axioms` lists `RBM.BA.BAFlowMember` as unclassified (report (b)).

## Verdict per target

Targets 1-12 (§1 source, §2 congruence, §3 pins and helpers, §4 `BAStep1_of_parts'`, `baStep1_holds` (conditional on the
owed `BAGbEXPii/ij`, §90), §5 `BAFlowMember_holds`, `BALmaxFromLK_holds`) and the registry edit: all **PASS**. Overall: **PASS**.
