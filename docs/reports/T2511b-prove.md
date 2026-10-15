Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 07:05:00 UTC 2026

Row b of T2511 (targets 11-12 and the registry; `t/T2511b` from `main` a082fcfe, row a and T2512 a47cf1e1 merged). Mathematics only. Row b adds no mathematics: it composes the merged glue `baMainIndFamTL_of_regimes` (`RBM3D/BA/MainIndGlue.lean:288`; binder order `d h₃ h₁ h₂ h₄`, exactly `T2512_OfRegimes`, `T2512-check.lean:123-125`) with the merged regime closures `baMainIndFamTL_III_three`, `baMainIndFamTL_I`, `_II`, `_IV` (`MainIndRegBA.lean:42, 45, 49, 53`) and the merged terminal plug-ins `baMLOutTL_of_famStep` (`MainIndOutBA.lean:315`), `unMLOutBA_of_famStep` (`:326`).

Targets (math only):
- 11: `BAMainIndFamTL 3 STAny`, `BAMLOutTL 3`, `UNMLOutBA 3` (= `T2511_Terminal`, `T2511-check.lean:209`), hypothesis-free.
- 12: `∀ d, STStep5IIIgL d (BA tuple) → BAMainIndFamTL d STAny` (= `T2511_AnyD`, `:213`, same text as `T2512_AnyD`, `T2512-check.lean:184`).

### (i) Exponent table (1a fill-in table (i)-(vii) of the ticket)

Row b has no exponent of its own: every exponent and threshold sits inside the merged producers read by name. Constants it touches:

| item | value | constraint | slack |
|---|---|---|---|
| (i) `𝔠d` of `STAny` | `inf'` over the 16 pairs `P : Fin 4 × Fin 4` of the constants `c P` of `baMainIndFamTL_chain d … ((P.2:ℕ)-P.1) P.1` (`MainIndGlue:292-300`); a function of `(κ, ε, 𝔡)` only, no `∃` after `(sz, z)` (U5S-C3) | `0 < 𝔠d ≤ 1/100`: each `c P` has `0 < c P` and `c P ≤ 1/100` (the `BAMainIndFamTL` text, `MainIndOutBA:60`); `inf'` of a nonempty finite set is `≤` every member and `>0` | exact: `𝔠d ≤ min_P c P ≤ 1/100`; no new constant in row b |
| (i) per regime `R` | each regime's own `𝔠d_R` (row a, `MainIndRegBA`) enters only through `c (P)` | the `min` over regimes (iii), (i), (ii), (iv) = `STReg5III, STReg5I, STReg5II, STReg5IV` | the glue uses chains `STRegChain i m`, `i + m ≤ 3`, so only these four are needed |
| dimension | `d = 3` (target 11); general `d` (target 12) | `3 ≤ d` is the first premise of `BAMainIndFamTL d R` | target 12 has no `3 ≤ d` binder of its own; `BAMainIndFamTL d STAny` starts `3 ≤ d →`; `d > 3` regime (iii) enters only as hypothesis `STStep5IIIgL d` (DECISIONS §316, Jun decision B) |
| (ii) route 11 | `baMainIndFamTL_three := baMainIndFamTL_of_regimes 3 baMainIndFamTL_III_three (baMainIndFamTL_I 3) (baMainIndFamTL_II 3) (baMainIndFamTL_IV 3)`; `baMLOutTL_three := baMLOutTL_of_famStep 3 baMainIndFamTL_three`; `unMLOutBA_three := unMLOutBA_of_famStep 3 baMainIndFamTL_three` | types match by unfolding only | exact |
| (ii) route 12 | `baMainIndFamTL_any d h5 := baMainIndFamTL_of_regimes d (baMainIndFamTL_III d h5) (baMainIndFamTL_I d) (baMainIndFamTL_II d) (baMainIndFamTL_IV d)` (`MainIndRegBA:36, 45, 49, 53`) | `h5 : STStep5IIIgL d …` is the only premise, and it is exactly `baMainIndFamTL_III`'s premise (same text, `MainIndRegBA:36-38`) | exact; at `d = 3` `baMainIndFamTL_three` is `baMainIndFamTL_any 3 baStep5III_holds` (`Step5IIITargets:57`; the same pairing compiles in `MainIndRegBA:42`) |
| (iii) instance data | `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `t ≡ 1/2` and `t ≡ 0`; `sz0` (`Defs/Sizes.lean:260`), `zSeq` (`FlowPins:1181`) | `flow_sz0` (`FlowPins:1214`) is at `κ = 1/2`, weakened to `1/4` as `MainIndOutBA_flow` (`MainIndOutBA` §7); `half_lt_t0` (`FlowPins:1254`): `1/2 < T0`; `sz0_win_third` (`Step1Fam:802`): window `(1/3, 1/2)` weakened to `κ = 1/4` | `c₁ = 1/3 ≤ 1/2`; `κ = 1/4 ≤ 1/2`; `t = 1/2 < T0 n` for all `n`; `n₀` is not used (no tail passage in row b) |
| (iv) registry preview | after row b: delete `Test/Axioms.lean:140` (`BAMainIndFamTL`); edit the owner texts on `:143, :186, :188, :192, :193, :224` | the scan is head-based (`scanPremises`, `Test/Axioms.lean:494-515`): `BAMainIndFamTL` is `proved` as soon as some non-certificate theorem concludes it, which row a / T2512 already do, so it is not in `found`; `unused` is only reported (the `registryLine`), never an error | 0 new premises: row b's theorems take only `STStep5IIIgL` (premise of 12), whose head is concluded by `baStep5III_holds`; it is not in the registry (`grep STStep5IIIgL Test/Axioms.lean` = 0 hits) and row a already carries it |
| (v) lines of `MainIndTermBA.lean` | bottom-up 40 / 60 / 120 (header 10 / 20 / 30; targets 10 / 15 / 30; instances 20 / 25 / 60); calibrated 58-77 | stop line 200 (file limit 2,000) | central 60 vs 200: 140 spare |
| (vi) greps | C1 `mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT` = 0 expected (file names only `BAMainIndFamTL`, `BAMLOutTL`, `UNMLOutBA`, `STStep5IIIgL`, `BAFlow`, `baFMz`, `BAflowT0`); `grep -nE 'STIngR6gL|STStep6ConclgL|BATwistAvgLaw'` on the new file = 0 expected; `grep -nE '^(private )?(noncomputable )?(def|abbrev|structure) '` = 0 hits (no def in row b); `grep -n withLam` only `seqP (sz.withLam 0)` inside `STStep5IIIgL`'s tuple argument | V2O-C1: `baMainIndFamTL_three`, `baMLOutTL_three`, `unMLOutBA_three` only here | row a files carry 0 hits of `STAny|BAMLOutTL 3|UNMLOutBA 3` (command below) |
| (vii) slot unification of 10 | n/a, because row a's target 10 is merged and read by name; row b restates no `BAStep6R`/`STIngR6gL` | | |

Check run on the current branch (V2O-C1 and name-freshness; empty output = 0 hits):
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2511b && grep -nE 'STAny|BAMLOutTL 3|UNMLOutBA 3' RBM3D/BA/MainIndFamTL.lean RBM3D/BA/MainIndRegBA.lean
$ grep -rn "baMainIndFamTL_three\|baMLOutTL_three\|unMLOutBA_three\|baMainIndFamTL_any\|MainIndTermBA" RBM3D RBM3D.lean
$ grep -n "MainIndRegBA\|MainIndGlue\|MainIndTermBA" RBM3D.lean
642:import RBM3D.BA.MainIndGlue
644:import RBM3D.BA.MainIndRegBA
```
(the first two commands print nothing; the third shows the two merged imports and no `MainIndTermBA`. `RBM3D.BA.MainIndFamTL` is `RBM3D.lean:643`; the new import goes after the last `import` line, `RBM3D.lean:644` at present.)

### (ii) One concrete nondegenerate instance

Instances of row b (as `MainIndOutBA:408-426`, where `BAMainIndFamTL 3 STAny` was a hypothesis `hm`; now `baMainIndFamTL_three`, no hypothesis): `baMLOutTL_three`, `unMLOutBA_three` and `baMLOutTL_of_famStep 3 (baMainIndFamTL_any 3 baStep5III_holds)` applied at `d = 3`, `sz0`, `zSeq`, `MainIndOutBA_flow` (= `flow_sz0` at `κ = 1/4`; private, by `open private … from RBM3D.BA.MainIndOutBA`, the pattern of `MainIndRegBA:64-65`), `(κ, ε, 𝔡, 𝔠) = (1/4, 1/10, 1/10, 1/6)`, `t ≡ 1/2` (hyps `0 ≤ 1/2`, `1/2 ≤ T0 n` by `half_lt_t0`) and `t ≡ 0` (`0 ≤ 0`, `0 ≤ T0 n` by `half_lt_t0`). No `N = 0`, empty index, collapsed window or `False` premise: `sz0` has `L n = 4(n+1) ≥ 3`, `lam n = (2(n+1))^{-6} > 0`, every hypothesis of 11 and 12 is a deterministic fact discharged by merged theorems. No external hypothesis (no cited-paper input) in row b, so TEAM §8 lesson 14 needs no limit computation; the only hypothesis of 12 is `STStep5IIIgL d`, proved at `d = 3` by `baStep5III_holds`.

```
$ python3 -I .../scratchpad/T2511b/inst2.py      # numbers of the instance (script: sz0 from Defs/Sizes.lean:260-264)
sz0: L>=3 and 0<lam<=1/64 for n<2000: True | lam(0)= 1/64 lam(1999)<1e-20: True
hyp 3<=d: 3<=3: True
0<kappa,eps,dd: True
kappa=1/4 <= flow_sz0 kappa=1/2 (flow weakening): True
0<c1<=1/2, window kappa<=1/2 : True True
flow_sz0 (eps,cc,dd) = (1/10,1/6,1/10) matches: True
t1=1/2 < T0 (half_lt_t0), s=1/10 < t1: True ; t2=0: 0<=t2: True
```
The script covers the numerical hypotheses; the analytic facts `1/2 < T0 n`, the flow and the window at `κ = 1/4` are the merged compiled theorems `half_lt_t0`, `flow_sz0` and `sz0_win_third` (already used at this data in `MainIndOutBA` §7 and in `MainIndRegBA` §2).

### Verdicts

- Target 11 (`baMainIndFamTL_three`, `baMLOutTL_three`, `unMLOutBA_three`): PASS. Inputs are merged and match their pins: `baMainIndFamTL_of_regimes` has the binder order of `T2512_OfRegimes`; the four regime premises at `d = 3` are `baMainIndFamTL_III_three`, `baMainIndFamTL_I 3`, `_II 3`, `_IV 3`.
- Target 12 (`baMainIndFamTL_any`): PASS; the premise `STStep5IIIgL d …` of `baMainIndFamTL_III` is the same text as the premise of `T2511_AnyD`.
- Registry: PASS as planned (delete `:140`, six owner texts, 0 new premises). Observation, not a move: `:141` and `:189` also contain the text "(T2511)" in the owner descriptions ("V2a, T2511"); the ticket lists `:189` as untouched and does not list `:141`; the sentences stay true after row b (they name the regime producers), so no change is proposed.
- No pin, row or stop line moves: no 1a-audit needed.

### (a′) Preflight corrections

None. (Observation, no verdict change: the six registry lines the ticket lists contain no literal text "T2511" before row b; the edit adds it. See (d).)

## (b) Script output (row b, branch t/T2511b, commit 45c1b6db, written Thu Oct 15 07:14:15 UTC 2026)

### Build
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2511b && lake build RBM3D.BA.MainIndTermBA   # tail

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4311 jobs).
$ lake build   # whole library, runs #assert_rbm_axioms (log: scratchpad full_after.log)
Build completed successfully (4418 jobs).
lake build  70.56s user 7.64s system 104% cpu 1:14.78 total
info: RBM3D.lean:648:0: axiom audit: 15449 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/MainIndTermBA.lean ; echo rc=$?
rc=1
$ wc -l RBM3D/BA/MainIndTermBA.lean
     124 RBM3D/BA/MainIndTermBA.lean
```

### Axioms of the new public declarations, and the pin diffs (scratch file, not committed; its example lines and `#print axioms` outputs)
```
$ lake env lean audit_row_b.lean (scratchpad T2511b/)   # imports RBM3D.BA.MainIndTermBA; defs T2511_Terminal, T2511_AnyD, T2512_OfRegimes copied by sed from the two check files
18:example : T2511_Terminal := ⟨baMainIndFamTL_three, baMLOutTL_three, unMLOutBA_three⟩
19:example : T2511_AnyD := baMainIndFamTL_any
20:example : T2512_OfRegimes 3 := baMainIndFamTL_of_regimes 3
'RBM.BA.baMainIndFamTL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMLOutTL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_any' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean docs/tickets/checks/T2511-check.lean ; lake env lean docs/tickets/checks/T2512-check.lean   # on this branch
T2511-check exit=0
T2512-check exit=0
```

### Target statements, extracted by script (`sed -n 36,57p`; the proofs are one-line compositions)
```
/-! ## 1. Target 11: the terminal at `d = 3` -/
/-- **Target 11, `baMainIndFamTL_three`**: `lem:main_ind_BA` in family form with TL2 at `STAny`, `d = 3`, unconditional:
`baMainIndFamTL_of_regimes` of the four closed regimes. -/
theorem baMainIndFamTL_three : BAMainIndFamTL 3 STAny :=
  baMainIndFamTL_of_regimes 3 baMainIndFamTL_III_three (baMainIndFamTL_I 3) (baMainIndFamTL_II 3) (baMainIndFamTL_IV 3)
/-- **Target 11, `baMLOutTL_three`**: `BAMLOutTL 3`, unconditional (`baMLOutTL_of_famStep`, `MainIndOutBA:315`). -/
theorem baMLOutTL_three : BAMLOutTL 3 := baMLOutTL_of_famStep 3 baMainIndFamTL_three
/-- **Target 11, `unMLOutBA_three`**: `UNMLOutBA 3`, unconditional (`unMLOutBA_of_famStep`, `MainIndOutBA:326`). -/
theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIndFamTL_three
/-! ## 2. Target 12: the general-`d` step at `STAny` -/
/-- **Target 12, `baMainIndFamTL_any`**: the family step at `STAny` for every `d` under Step 5 (iii) `STStep5IIIgL d` (0342 Q4; the text of
`T2512_AnyD`); `BAMainIndFamTL d STAny` starts `3 ≤ d →`. `d = 3`: `baStep5III_holds`. -/
theorem baMainIndFamTL_any : ∀ d : ℕ,
    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STAny :=
  fun d h5 => baMainIndFamTL_of_regimes d (baMainIndFamTL_III d h5) (baMainIndFamTL_I d) (baMainIndFamTL_II d) (baMainIndFamTL_IV d)
```

### The compiled nonempty instances (`sed -n 65,120p`; all inside the built file, `d = 3`)
```
section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.Step1FamInst
open private MainIndOutBA_flow MainIndOutBA_win MainIndOutBA_mem from RBM3D.BA.MainIndOutBA
local notation "μ0" => Sizes.seqP (sz0.withLam 0)
local notation "mem0" => BAzSrc sz0 zSeq (fun _ => 2 / 3) (fun _ => 17 / 25)
local notation "Fam6" "(" C ", " μ ", " s ")" =>
  STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s
local notation "Fam7" "(" C ", " μ ", " t ")" =>
  STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t
-- target 11: the three outputs as one conjunction (the pin `T2511_Terminal`)
example : BAMainIndFamTL 3 STAny ∧ BAMLOutTL 3 ∧ Univ.UNMLOutBA 3 := ⟨baMainIndFamTL_three, baMLOutTL_three, unMLOutBA_three⟩
-- target 12 at `d = 3` with Step 5 (iii) proved: it is target 11
example : BAMainIndFamTL 3 STAny := baMainIndFamTL_any 3 baStep5III_holds
-- target 11: `BAMLOutTL 3` at `t ≡ 1/2` and at `t ≡ 0` (hypothesis-free; the instances of `MainIndOutBA:408-426` without `hm`)
example := baMLOutTL_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
example := baMLOutTL_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])
-- target 11: `UNMLOutBA 3` at `t ≡ 1/2` and at `t ≡ 0`
example := unMLOutBA_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
example := unMLOutBA_three le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq
  MainIndOutBA_flow (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])
-- target 12 at `d = 3`: the plug-in on the general-`d` step with `baStep5III_holds`
example := baMLOutTL_of_famStep 3 (baMainIndFamTL_any 3 baStep5III_holds) le_rfl (1 / 4) (1 / 10) (1 / 10) (1 / 6) (by norm_num)
  (by norm_num) (by norm_num) sz0 zSeq MainIndOutBA_flow (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
-- target 12 at `s ≡ 0 < t ≡ 1/2`, hypothesis-free: the six conclusions on `Fam(0)` are the base; the seven at the non-main member of `Fam(1/2)`
example : ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_any 3 baStep5III_holds le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 0) (fun _ => 1 / 2) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n]) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) trivial ?_ (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _
    (MainIndOutBA_mem (1 / 2) (by norm_num))⟩
  intro z' hz'
  obtain ⟨⟨b1, -, b3, b4, b5, b6⟩, tl⟩ := baFamMember_base 3 (baBaseG_holds 3) (baG0M_holds 3) le_rfl (1 / 4) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num)
    MainIndOutBA_win z' hz'
  exact ⟨b1, b3, b6, STLocalMaxgL_of_STLocalEntrygL _ _ _ b5, b4, tl⟩
-- target 12 at `s ≡ 1/10 < t ≡ 1/2` (the data of T2511 row a): the six conclusions on `Fam(1/10)` (the induction hypothesis) are the one binder
example (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
  obtain ⟨𝔠d, h𝔠, -, H⟩ := baMainIndFamTL_any 3 baStep5III_holds le_rfl (1 / 4) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨𝔠d, h𝔠, H (1 / 6) sz0 zSeq MainIndOutBA_flow sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) MainIndOutBA_win
    (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (by norm_num : (1 / 10 : ℝ) ≤ 1 / 2).trans (half_lt_t0 n).le)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) trivial hfam
    (Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) h𝔠) _ (MainIndOutBA_mem (1 / 2) (by norm_num))⟩
end Inst
```

### Greps (labelled; rc=1 means 0 hits)
```
$ C1: grep -nE 'mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT' RBM3D/BA/MainIndTermBA.lean
rc=1
$ X1-C4: grep -nE '^(private )?(noncomputable )?(def|abbrev|structure) ' RBM3D/BA/MainIndTermBA.lean   (no def in row b)
rc=1
$ BAStep6R text: grep -nE 'STIngR6gL|STStep6ConclgL|BATwistAvgLaw' RBM3D/BA/MainIndRegBA.lean RBM3D/BA/MainIndTermBA.lean
rc=1
$ V2O-C1 (row a files): grep -nE 'STAny|BAMLOutTL 3|UNMLOutBA 3' RBM3D/BA/MainIndFamTL.lean RBM3D/BA/MainIndRegBA.lean
rc=1
$ V2O-C1 (this file, the sole writer): grep -nE '^theorem (baMainIndFamTL_three|baMLOutTL_three|unMLOutBA_three)' RBM3D/BA/MainIndTermBA.lean
40:theorem baMainIndFamTL_three : BAMainIndFamTL 3 STAny :=
44:theorem baMLOutTL_three : BAMLOutTL 3 := baMLOutTL_of_famStep 3 baMainIndFamT
47:theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIn
$ UBA: grep -n withLam RBM3D/BA/MainIndTermBA.lean   (hit 1: inside the STStep5IIIgL tuple argument of target 12; hit 2: the local notation μ0 = seqP (sz0.withLam 0))
54:    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z
69:local notation "μ0" => Sizes.seqP (sz0.withLam 0)
$ U5S-C3: grep -n '∃' RBM3D/BA/MainIndTermBA.lean   (both hits are the conclusion of an example, the pattern of the merged MainIndGlue §5 examples, not a target statement; the constant is the one the family step fixes by (κ, ε, 𝔡) before (sz0, zSeq))
99:example : ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
113:    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) := by
$ name clash: grep -rn "baMainIndFamTL_three\|baMLOutTL_three\|unMLOutBA_three\|baMainIndFamTL_any\|MainIndTermBA" RBM3D RBM3D.lean | grep -v "^RBM3D/BA/MainIndTermBA.lean"  (cut at 60 chars; the Axioms.lean hits are the registry texts of this ticket, none outside it and RBM3D.lean:645)
RBM3D/Test/Axioms.lean:137:   -- T2340 (ST-6 R1-R3, DECISION
RBM3D/Test/Axioms.lean:142:   `RBM.BA.STStep1WeakgL, -- `(Gt
RBM3D/Test/Axioms.lean:185:   `RBM.BA.STInitialGT2gL, -- `(i
RBM3D/Test/Axioms.lean:187:   `RBM.BA.BATwistAvgLaw, -- TL1:
RBM3D/Test/Axioms.lean:191:   `RBM.BA.STStep2DecayPTgL, -- `
RBM3D/Test/Axioms.lean:192:   `RBM.BA.STGdecayWgL, -- `(Eq:G
RBM3D/Test/Axioms.lean:223:   `RBM.BA.STStep1LoopgL, -- `(lR
RBM3D.lean:645:import RBM3D.BA.MainIndTermBA
$ same grep on main a082fcfe (before this commit): git grep -n ... a082fcfe -- RBM3D RBM3D.lean ; echo rc=$?
rc=1
```

### Registry (`RBM3D/Test/Axioms.lean`): changed fragments of `git diff --word-diff=porcelain -U0 a082fcfe HEAD` (long lines cut at 200 chars), and the scan before / after
```
+T2504); `BAMainIndFamTL` (registered by
+left this list (T2511b: concluded at `STAny`, `d = 3`, by `baMainIndFamTL_three`, and for every `d` under `STStep5IIIgL d` by `baMainIndFamTL_any`, `BA/MainIndTermBA`)
-   `RBM.BA.BAMainIndFamTL, -- the family step of the BA main induction (`lem:main_ind_BA` on `Fam(u)`, `7_8:1954-1990`, D536; `BA/MainIndOutBA.lean`), premise of `baChainFamTL_holds`, `baMLOutTL_of_f
-BA chain, BA-S3)
+the family Step 1 call `baStep1Fam_call`, `BA/MainIndFamTL`, T2511: `baStep1_holds'` at the members of `Fam(t)`; inside `baMainIndFamTL_three`, `BA/MainIndTermBA`, T2511b)
+= T2511
-chain),
+chain: the family Step 1 call `baStep1Fam_call`, `BA/MainIndFamTL`; terminal `baMainIndFamTL_three`, `BA/MainIndTermBA`, T2511b),
-`twSteps`)
+`twSteps`: `TwistStep2_tl1` fed to the Step-6 bridge in `baMainIndFamTL_of_steps`, `BA/MainIndFamTL`, T2511; terminal `baMainIndFamTL_three`, `BA/MainIndTermBA`, T2511b)
-(BA-V);
+(BA-V = T2511: the Step 1 pair of `baStep1Fam_call` is consumed by `baStep2Decay_holds` in `baMainIndFamTL_of_steps`, `BA/MainIndFamTL`; terminal `baMainIndFamTL_three`, `BA/MainIndTermBA`, T2511b);
-(BA-V);
+(BA-V = T2511: the Step 1 pair of `baStep1Fam_call` is consumed by `baStep2Decay_holds` in `baMainIndFamTL_of_steps`, `BA/MainIndFamTL`; terminal `baMainIndFamTL_three`, `BA/MainIndTermBA`, T2511b);
-BA chain, BA-S3)
+the family Step 1 call `baStep1Fam_call`, `BA/MainIndFamTL`, T2511: `baStep1_holds'` at the members of `Fam(t)`; inside `baMainIndFamTL_three`, `BA/MainIndTermBA`, T2511b)
$ git diff a082fcfe..HEAD --stat -- RBM3D/Test/Axioms.lean RBM3D.lean RBM3D/BA/MainIndTermBA.lean
 RBM3D.lean                  |   1 +
 RBM3D/BA/MainIndTermBA.lean | 124 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |  15 +++---
 3 files changed, 132 insertions(+), 8 deletions(-)
$ diff <(grep -v "^lake build " scan_before.txt) <(grep -v "^lake build " scan_after.txt)   # #assert_rbm_axioms output of lake build: registry unedited (new file and import present) vs edited
43d42
<   RBM.BA.BAMainIndFamTL: 19 [no certificate]
131c130
< registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
---
> registry: 2 borrowed + 120 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
152d150
<  RBM.BA.BAMainIndFamTL,
293c291
< non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
---
> non-vacuity certificates: 0 of 122 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ grep -hE "^premises found|^registry:" scan_before.txt scan_after.txt
premises found by scanning: 128 (borrowed 1, owed 55, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
premises found by scanning: 128 (borrowed 1, owed 55, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 120 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ git diff a082fcfe..HEAD --name-only
RBM3D.lean
RBM3D/BA/MainIndTermBA.lean
RBM3D/Test/Axioms.lean
$ git diff a082fcfe..HEAD --stat -- RBM3D/Chain RBM3D/Induction RBM3D/Graph RBM3D/BA/MainIndFamTL.lean RBM3D/BA/MainIndRegBA.lean RBM3D/BA/MainIndGlue.lean RBM3D/BA/MainIndOutBA.lean   # empty
```

### Route per target (merged `file:line`; the ticket coverage table as used by row b)
| target | route |
|---|---|
| 11 `baMainIndFamTL_three` | `baMainIndFamTL_of_regimes` (`MainIndGlue:288`) at `baMainIndFamTL_III_three` (`MainIndRegBA:42`), `baMainIndFamTL_I 3`, `_II 3`, `_IV 3` (`:45, 49, 53`); binder order (iii), (i), (ii), (iv) = `T2512_OfRegimes` |
| 11 `baMLOutTL_three`, `unMLOutBA_three` | `baMLOutTL_of_famStep 3`, `unMLOutBA_of_famStep 3` (`MainIndOutBA:315, 326`) at `baMainIndFamTL_three` |
| 12 `baMainIndFamTL_any` | `baMainIndFamTL_of_regimes d` at `baMainIndFamTL_III d h5` (`MainIndRegBA:36`), `_I d`, `_II d`, `_IV d`; `h5` has the premise text of `baMainIndFamTL_III`; at `d = 3` `baStep5III_holds` (`Step5IIITargets:57`) |
| instances | `baFamMember_base` (`MainIndOutBA:112`), `baBaseG_holds` (`:300`), `baG0M_holds` (`:250`), `STLocalMaxgL_of_STLocalEntrygL` (`MainIndChain:126`), `s1Setup_conStInd_const` (`Step1Setup:1226`), `half_lt_t0` (`FlowPins:1254`) |

### Instance data (numbers; 1a table (iii))
`d = 3`; `sz0`, `zSeq`; `κ = 1/4` (`flow_sz0` is at `1/2`, weakened by the private `MainIndOutBA_flow`); `(ε, 𝔡, 𝔠) = (1/10, 1/10, 1/6)`; `c₁ = 1/3`; member `BAzSrc sz0 zSeq (2/3) (17/25)`. Terminal at `t ≡ 1/2` and `t ≡ 0`. Target 12 at `(s, t) = (0, 1/2)` with no hypothesis, and at `(1/10, 1/2)` with the six conclusions on `Fam(1/10)` as one binder. `n₀` is not used (no tail passage in row b).

### Narrative
- Row b composes merged names only. Targets 11 and 12 compiled at the first `lake build RBM3D.BA.MainIndTermBA`; no stop rule fired; no correction of (a).
- Size: 124 lines = 35 (header, docs, namespace) + 22 (targets, lines 36-57) + 67 (instances, lines 58-124). Ticket bottom-up 40 / 60 / 120 (header 10 / 20 / 30, targets 10 / 15 / 30, instances 20 / 25 / 60): 4 above the high; calibrated 58-77: 47 above its top; stop line 200: 76 spare.
- Instances: the terminal examples have no hypothesis (they are the examples of `MainIndOutBA:408-426` without `hm`). Target 12 is hypothesis-free at `s ≡ 0` (the six conclusions on `Fam(0)` are `baFamMember_base`, with `STLocalMaxgL` from `STLocalEntrygL`). At `s ≡ 1/10` the six conclusions on `Fam(1/10)` stay one binder: the induction hypothesis of the statement, not another gate's pin.
- Registry: `Test/Axioms.lean` edited at the ticket's seven places (`:140` deleted; owner texts of `:143, :186, :188, :192, :193, :224`, now one line lower; the deletion note is appended to the `T2340` comment line). Scan: premises found 128 before and after (0 new); owed 121 to 120; `BAMainIndFamTL` leaves the unused list and the owed ledger (it carried 19 theorems); `#assert_rbm_axioms` passed in the full build.
- Reading of the ticket: none of the six owner lines contained the text "T2511" before; I took "owner texts naming T2511" (T2504 Decision (3) amended, §334 (4)) as: name T2511 and the producing theorem, as pasted above.
- Not established: `STInitialGT2gL` is not in the type of `baStep1Fam_call` or `baStep1_holds'` (grep of `BA/Step1Prime.lean`: one hit, a docstring at `:912`). Its edited text names T2511 as the owner chain, as the ticket says, and does not claim a theorem concludes it.

## (c) Verified Mathlib names
None used directly in `MainIndTermBA.lean` (names read: merged RBM3D declarations in the route table; tactics `norm_num`, `linarith`, `le_rfl`, `trivial`). No Mathlib name was checked as absent.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none (`T2511ba`: none; the known D536, D538, D723 stand).
- Observation, no change made: the owner texts of the original `:141` (`STLocalEntrygL`) and `:189` (`BATwistLoopLaw`) already mention "T2511"; the ticket lists `:189` as untouched and does not list `:141`.
- `baMainIndFamTL_any` takes `STStep5IIIgL d` for the regime (iii) producer at every `d`; `d > 3` (iii) stays out of scope (Jun decision B, D723, DECISIONS §316).
