Auditor model: claude-opus-5-5

# T2511 audit, round 1 (row a: targets 1-10) — Thu Oct 15 07:00:02 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2511-audit1`, detached at `t/T2511` eed83cc4 (base `main` 97779231; current `main` a47cf1e1 has T2512 merged).
Scratch: `<scratchpad>/T2511/audit.lean` = `docs/tickets/checks/T2511-check.lean` (pins) + `import RBM3D.BA.MainIndFamTL`, `RBM3D.BA.MainIndRegBA` + the auditor's examples below. Nothing committed.

## 1. Build and axioms
```
$ lake build RBM3D.BA.MainIndFamTL RBM3D.BA.MainIndRegBA 2>&1 | grep -E "error|sorry|Build completed"
Build completed successfully (4309 jobs).
$ lake build 2>&1 | grep -E "error:|axiom audit|premise\(s\) that no theorem|Build completed|registry:" | cut -c1-200
info: RBM3D.lean:646:0: axiom audit: 15441 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4416 jobs).
$ lake env lean <scratchpad>/T2511/audit.lean ; echo exit=$? ; grep -c error audit.out
exit=0
0
$ grep "depends on axioms" audit.out   (private ones wrapped over 3 lines; each = [propext, Classical.choice, Quot.sound])
'RBM.BA.baKboundMember_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep1Fam_call' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.BA.MainIndFamTL.0.RBM.BA.MainIndFamTL_famOfS1' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.BA.MainIndFamTL.0.RBM.BA.MainIndFamTL_s1OfSteps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_III_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_I_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_II_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_IV_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_III' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_III_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_II' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMainIndFamTL_IV' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|^axiom|native_decide" A B | wc -l          # A, B = the two new files
       0
```

## 2. Diff scope
```
$ git diff --stat main...t/T2511
 RBM3D.lean                 |   2 +
 RBM3D/BA/MainIndFamTL.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/MainIndRegBA.lean | 113 +++++++++++++
 3 files changed, 512 insertions(+)
$ git diff --name-only main...t/T2511 -- RBM3D/Chain RBM3D/Induction RBM3D/Graph RBM3D/Test | wc -l
       0
$ git diff 97779231 t/T2511 -- RBM3D.lean | grep "^[+-]import"
+import RBM3D.BA.MainIndFamTL
+import RBM3D.BA.MainIndRegBA
```
Only the row-a sole writable files and two import lines; no merged file, no frozen signature touched; registry (`Test/Axioms.lean`) unedited, as decision (4) requires for row a.

## 3. Statements against the pins
Auditor examples (in `audit.lean`, all compile, exit 0 above):
```
open private MainIndFamTL_S1 MainIndFamTL_famOfS1 MainIndFamTL_s1OfSteps from RBM3D.BA.MainIndFamTL
example (d : ℕ) : T2511_K2Member d := baKboundMember_holds d
example (d : ℕ) : T2511_FamStep1Call d := baStep1Fam_call d
example (d : ℕ) (R : …) : MainIndFamTL_S1 d R = T2511_S1 d R := rfl
example (d : ℕ) (R : …) : T2511_FamOfS1 d R := MainIndFamTL_famOfS1 d R
example (d : ℕ) (R R34 Rtl : …) : T2511_S1OfSteps d R R34 Rtl := MainIndFamTL_s1OfSteps d R R34 Rtl
example (d : ℕ) (R R34 Rtl : …) : T2511_FamOfSteps d R R34 Rtl := baMainIndFamTL_of_steps d R R34 Rtl
example (d : ℕ) (R : …) : T2511_S5 d R = STIngR5gL d R (BA tuple) (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) := rfl
example (d : ℕ) : T2511_RegIIIOf d := baMainIndFamTL_III_of d      -- likewise RegIOf/_I_of, RegIIOf/_II_of, RegIVOf/_IV_of
example : T2511_Closed := ⟨baMainIndFamTL_III, baMainIndFamTL_III_three, baMainIndFamTL_I, baMainIndFamTL_II, baMainIndFamTL_IV⟩
example (d : ℕ) : BAStep6R d STReg5I = T2511_S6In d STReg5I (fun sz z s t => T2511_TLOn sz z s t → STStep6ConclgL …) := rfl
example (d : ℕ) : T2511_Bridge6 d (fun sz z s t => T2511_TLOn sz z s t → STStep6ConclgL …) := fun _ _ _ _ h c => c h
```
Whitespace-normalised text compare (script `tdiff.py`, pin body vs statement):
```
$ python3 -I tdiff.py T2511-check.lean RBM3D/BA/MainIndFamTL.lean
T2511_K2Member vs baKboundMember_holds : identical
T2511_FamStep1Call vs baStep1Fam_call : identical
T2511_S1 vs MainIndFamTL_S1 body: identical
```
- Targets 6-9 state the check-local abbreviations `T2511_S3/S4/S6In/Bridge6/TLOn` unfolded (the ticket permits "up to unfolding"). The one non-syntactic point is the Step-5 binder of target 6 (and private 5): `STIngR5gL … (fun sz z s t => STStep5ConclgL …)` instead of `STStep5RgL …`. It is `rfl`-equal to `T2511_S5` (example above), so the hypothesis is neither stronger nor weaker. The reason given (prove report (a) F(iv)) is that `STStep5RgL` is unregistered; the full build's scan above throws nothing.
- Quantifier order (U5S-C3): `MainIndFamTL_S1` (= the merged `BAMainIndFamTL` shape) has `∃ 𝔠d` after `(κ, ε, 𝔡)` and before `(𝔠, sz, z)`. In `s1OfSteps`, `𝔠d = min c₂ … c₇`: Step 2 `(Cd, c₂)` is taken at `(κ, ε, 𝔡)`; Steps 3, 4, 5 and TL2 at `Cd`; Step 6 at `(κ, ε, 𝔡)`. Nothing depends on `(sz, z)` (file lines 141-149).
- Regime triples `(R, R34, Rtl)` match ticket target 7-9: (iii) `(STReg5III, STReg5III, STCaseI)`, (i) `(STReg5I, STReg5I, STCaseI)`, (ii) `(STReg5II, STCaseII, STCaseII)`, (iv) `(STReg5IV, STCaseII, STCaseII)` (lines 221, 234, 248, 261). Steps 3-4 come from T2509's names, as F3 requires.
- Q4 / §316: `baMainIndFamTL_III` takes `STStep5IIIgL d` as a hypothesis for general `d`. `baMainIndFamTL_III_three` discharges it with `baStep5III_holds`. (i), (ii), (iv) are unconditional for every `d`; each conclusion `BAMainIndFamTL d R` starts with `3 ≤ d →`.
- Target 10 closes the slot with `baStep6Reg*_holds d` and the bridge `fun _ _ _ _ h c => c h`, without an adapter (MainIndRegBA:39-54). `BAStep6R` is not restated:
```
$ grep -nE 'STIngR6gL|STStep6ConclgL|BATwistAvgLaw' RBM3D/BA/MainIndRegBA.lean | wc -l
       0
```
- Downstream fit (row b / T2512, current `main`): `git show main:RBM3D/BA/MainIndGlue.lean:288-289` is `theorem baMainIndFamTL_of_regimes (d) (h₃ : BAMainIndFamTL d STReg5III) (h₁ : … STReg5I) (h₂ : … STReg5II) (h₄ : … STReg5IV) : BAMainIndFamTL d STAny`. Its hypothesis types are exactly the conclusions of target 10.

## 4. Hidden hypotheses, vacuity, cycles
- No structure is introduced. The one def is `private def MainIndFamTL_S1 : Prop` (an implication chain, no fields). Its use is `MainIndFamTL_s1OfSteps → MainIndFamTL_famOfS1`, a one-way chain, so there is no cycle.
- Every producer is a merged name: `baStep1_holds'`, `baStep2Decay_holds`, `baKbound/Kward_holds`, `TwistStep2_tl1`, `baTwistLoopStep_caseI/II`, `baStep3/4*_holds`, `baStep5I/II/IV_holds`, `baStep5III_holds`, `baStep6Reg*_holds`, `baFamMember_flow`, `BATwistLoopLaw_congr`.
- The hypotheses of 6-9 are the step pins (slot Step 6, bridge, (iii) Step 5). Target 10 discharges all of them except the authorized `STStep5IIIgL d` for `d ≠ 3` (D723, Jun decision B). There is no external hypothesis.
```
$ grep -nE "^(private )?(noncomputable )?(def|abbrev|structure|class|instance) " A B
RBM3D/BA/MainIndFamTL.lean:88:private def MainIndFamTL_S1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
$ grep -nE 'mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT' A B | wc -l        # C1
       0
$ grep -nE 'STAny|BAMLOutTL 3|UNMLOutBA 3' A B | wc -l                            # V2O-C1
       0
$ grep -n withLam A B | grep -vE "seqP \(([A-Za-z0-9_]+)\.withLam 0\)" | wc -l      # UBA-C1
       0
$ for n in <12 public names>; do git grep -nw $n main -- RBM3D | wc -l; done        # clash on current main: all 0
```

## 5. Compiled nonempty instances (`d = 3`; compiled as part of the module build in §1)
| target | instance (file:line) | data | hypotheses left |
|---|---|---|---|
| 1 | FamTL:286 | `sz0, zSeq`, κ=1/4, (ε,𝔠,𝔡)=(1/10,1/6,1/10), c₁=1/3, s≡1/10, member `BAzSrc sz0 zSeq (2/3) (17/25)` | none |
| 2 | FamTL:291 | as 1, 𝔠d=1/100, t≡1/2 (`half_lt_t0`), `STConStInd` by `s1Setup_conStInd_const` | `hfam` (induction hyp.) |
| 3-5 | private; exercised by 6 (`rfl`/examples in §3) | — | — |
| 6, 7 (iii) | FamTL:317, :327 | as 2; regime `lam² ≤ 1-t` by `nlinarith [sz0_lam_le, sz0_lam_pos]`; Steps 3-5 by name | `hfam`, slot `Concl6`, `h6`, `hb` (ticket 7-9: "slot and bridge stay hypotheses") |
| 8 (i), 9 (ii), 9 (iv) | FamTL:362, :372, :382 | merged `Step5CasesBA` data (L,W₀,lam,κ_dom,t) = (4,25,1,1/70,1/100), (4,25,4,1/1100,9/10000), (3,40,6,1/1000,1/2000), s≡0, κ=κ_dom/2, Λ=10 | `hfam`, `Concl6`, `h6`, `hb` |
| 10 | RegBA:76, :81 (iii, both forms), :86 (i), :94 (ii), :102 (iv) | as above | `hfam` only |
The (i), (ii), (iv) data are nondegenerate: `s < t` (`Step5CasesBA_dat*`), the regime holds (`Step5CasesBA_reg*`), and `lam` lies in `(0, 10]`, proved by `norm_num`. The window `c₁` is the existential of `BAWinBulk_of_dom_holds` (`0 < c₁ ≤ 1/2`). The slot hypotheses left open in the instances of 6-9 are closed at concrete data by the instances of 10, which leave only the family induction hypothesis. The ticket (9′) keeps that hypothesis as a binder.

## 6. Paper deltas
The prove report proposes none (`T2511a`: none). Row a introduces no new Lean/paper statement difference. The conclusion is the merged `BAMainIndFamTL`. Its known differences are already in `docs/paper-deltas.md`, the entries the ticket expects:
```
$ grep -nE "\bD(536|538|723)\b|^- \*\*D(51|685)" docs/paper-deltas.md | cut -c1-60    # output truncated; parenthesised notes are the auditor's
352:- **D51（T2041d）**：Steps 3–4 按区间谓词 `R ∈ {STAny, STCaseI, …     (regime split R/R34)
1495:- **D536（T2205b）**：`lem:main_ind_BA` 的 Step 1 …                     (family form Fam(u))
1497:- **D538（T2205d）**：族钉文带 `∀ n, 0 < sz.lam n` …                     (lam > 0)
1649:- **D685（T2434c）**：S2 钉文 `BAExp14bS2` … TL1、TL2 …                   (TL1/TL2 conjuncts)
1803:- **D723**（Jun 决定 B，2026-10-14）… BA 终端只在 d = 3 证明 …           ((iii) at general d hypothesised)
```
Covered.

## 7. Observations (no RETURN)
- O1. Prove report (b), clash block: "main RBM3D/ + DECISIONS.md hits: baKboundMember_holds(main:1)". My `git grep -nw` over `main:RBM3D` gives 0 for all 12 names, so the hit was presumably in DECISIONS. No effect.
- O2. The instances of 8, 9 and 10 (i)/(ii)/(iv) conclude at the main flow (`BAFamZ_main`), not at a non-main member. The (iii) instances use the non-main member `BAzSrc …`. This is nondegenerate either way.
- O3. `MainIndFamTL.lean` imports `Induction/MainIndChain`, which it does not use (the ticket lists it; report (d) says so). The proof does not use the `STLocalMaxgL_of_STLocalEntrygL` endpoint from the ticket's table.
- O4. Merge: `main` a47cf1e1 already has `import RBM3D.BA.MainIndGlue` after `import RBM3D.BA.Step6BA`, and the branch adds its two lines at the same place. The hub takes the union (CONTROL H313); `#assert_rbm_axioms` stays last.

## Verdict
| target | verdict |
|---|---|
| 1 `baKboundMember_holds` | PASS |
| 2 `baStep1Fam_call` | PASS |
| 3 private `MainIndFamTL_S1` | PASS |
| 4 private `MainIndFamTL_famOfS1` | PASS |
| 5 private `MainIndFamTL_s1OfSteps` | PASS |
| 6 `baMainIndFamTL_of_steps` | PASS |
| 7-9 `baMainIndFamTL_III_of`, `_I_of`, `_II_of`, `_IV_of` | PASS |
| 10 `baMainIndFamTL_III`, `_III_three`, `_I`, `_II`, `_IV` | PASS |
**T2511 row a: PASS.** No dispatcher sign-off needed.
