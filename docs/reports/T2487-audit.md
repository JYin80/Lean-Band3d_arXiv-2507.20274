Auditor model: claude-opus-5-5
# T2487 audit, round 1 (BA-T T1-BA, BA Step 2), written Tue Oct 13 04:34:47 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2487-audit1`, detached at `t/T2487` = 3b9c210d. Section (a) D1: the pre-signed split
did **not** fire (central 1,408 < 1,950), so all targets 1-12 (+9b, dispatcher answer (3)) are on `t/T2487`; no `t/T2487b`, no reserve file.

## 1. Diff, size, layering
```
$ git diff --name-only main...t/T2487
RBM3D.lean
RBM3D/BA/Step2CloseBA.lean
RBM3D/BA/Step2IterBA.lean
RBM3D/Test/Axioms.lean
$ wc -l RBM3D/BA/Step2IterBA.lean RBM3D/BA/Step2CloseBA.lean
     833 RBM3D/BA/Step2IterBA.lean
     259 RBM3D/BA/Step2CloseBA.lean
$ git grep -n 'import RBM3D.BA.Step2\(Iter\|Close\)BA' t/T2487 -- '*.lean'
t/T2487:RBM3D.lean:568:import RBM3D.BA.Step2IterBA ; t/T2487:RBM3D.lean:569:import RBM3D.BA.Step2CloseBA ; t/T2487:RBM3D/BA/Step2CloseBA.lean:6:import RBM3D.BA.Step2IterBA
```
All four paths are sole writable files; no Chain/Induction/Evolution/Path/merged BA file changes. The imports precede `#assert_rbm_axioms`. Each file is under the 2,000 stop line and the 1,800 reserve rule.

## 2. Builds and axioms
```
$ lake build RBM3D.BA.Step2IterBA RBM3D.BA.Step2CloseBA   (grep error|sorry|Build completed)
Build completed successfully (4089 jobs).
$ lake build   (full library, branch root imports; grep error|axiom audit|Build completed)
info: RBM3D/Test/AuditNegative.lean:30:0: audit reverse test: an unclassified premise is caught (RBM.Audit.Fixture.FakePremise).
info: RBM3D.lean:572:0: axiom audit: 14433 theorems, 4533 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4340 jobs).
$ lake env lean docs/tickets/checks/T2487-check.lean  -> exit 0, 0 error lines
$ lake env lean <scratch>/audit.lean   (#print axioms part)
'RBM.BA.baStep2Mat_Hpath_herm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_oneLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Mat_listLink' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_K2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_newKLK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTBdatagL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baScaleExists_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTOptL2gL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTGijDecgL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTLocalAvgOfL2gL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE 'sorry|admit|axiom|native_decide' <each new file>   -> exit 1 (both files)
```

## 3. Statements against the pins (script)
Scratch file `audit.lean`: imports of the check file, then the two new modules, the check's lines 37-263 (the `T2487_*` pins, verbatim),
the guarded-skeleton shape (check lines 265-285) as `def T2487_skel`, then:
```
example : T2487_HpathHerm := @baStep2Mat_Hpath_herm   -- likewise OneLoop/ListLink/K2/NewKLK/Bdata/ScaleExists/OptL2/LocalAvgOfL2
example : T2487_OneLoop := @baStep2_oneLoop ; example : T2487_ListLink := @baStep2Mat_listLink ; example : T2487_K2 := @baStep2_K2
example : T2487_NewKLK := @baStep2_newKLK ; example : T2487_Bdata := @baSTBdatagL_holds ; example : T2487_ScaleExists := @baScaleExists_holds
example : T2487_OptL2 := @baSTOptL2gL_holds ; example : T2487_LocalAvgOfL2 := @baSTLocalAvgOfL2gL_holds
example : ∀ d, 2 ≤ d → T2487_BAGijDec d := @baSTGijDecgL_holds
example : T2487_Step2Holds := fun d hL hE _ => baStep2_holds d hL hE ; example : ∀ d, BALWterm d → BALWtermExp d → BAStep2 d := @baStep2_holds
open private Step2CloseBA_step2_of_pins from RBM3D.BA.Step2CloseBA ; example : T2487_skel := @Step2CloseBA_step2_of_pins
$ lake env lean <scratch>/audit.lean -> exit 0; 0 error lines; warnings only "Variable name `κ`/`sz`/`z` is not explicitly referenced" (9, in the pasted pin text)
```
Targets 1-9 match their pins exactly (`@name` elaborates at the pin type). Target 11 is **stronger** than `T2487_Step2Holds`: it drops input
(b), which target 9b (`baSTGijDecgL_holds : ∀ d, 2 ≤ d → T2487_BAGijDec d`) now proves. Dispatcher answer (3) authorizes this ("≤ 100
lines": 9b is 10 lines). The conclusion is the frozen pin `BAStep2 d` (`BA/FlowPins.lean:432`, not edited).

Target 10 (private) against the merged body (`Chain/Step2IterGen2.lean:299-372` vs `Step2CloseBA.lean:100-174`):
```
$ diff -u a.txt b.txt | grep -E '^[-+@]'
-theorem ST_step2_of_pinsg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
+private theorem Step2CloseBA_step2_of_pins (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
@@ -7,7 +7,8 @@
-    (hOne : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2IterGen_OneLoop (mk sz z).toFlowFM)
+    (hOne : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
+      Step2IterGen_OneLoop (mk sz z).toFlowFM)
@@ -70,5 +71,5 @@
-  exact ST_concl_of_step2g _ _ hl ha hd' (hOne sz z) hs ht1
+  exact ST_concl_of_step2g _ _ hl ha hd' (hOne sz κ ε 𝔠 𝔡 z hκ hflow) hs ht1
```
The only change is the F2 guard; the shape check `T2487_skel` compiles. Because the copy is private, there is no second public skeleton (X1-C4).

## 4. Hidden hypotheses, vacuity, cycles, forbidden forms
```
$ grep -nE '^(private |protected )?(noncomputable )?(theorem|lemma|def|abbrev|instance) ' <new files> | grep -v ':theorem '
Step2IterBA.lean:116/123/128/141/167/178/490: private theorem Step2IterBA_{lam_window,ellT_mono,inv_le,tailT_le,tailW_le,prof_le,newKLKAtN_of}
Step2CloseBA.lean:100: private theorem Step2CloseBA_step2_of_pins
$ grep -nE '^(noncomputable )?(def|abbrev|structure) ' <new files>   -> exit 1 (no new def/abbrev/structure: no new field, no second Prop name)
$ grep -nE 'STGridRepNgL|STGijGEXgL|baStep1_holds\b|\|E\||2 - κ|STFlow|lemT|\bmE\b' <new files>   -> exit 1 (both)
$ grep -n withLam <new files>   (public-statement hits)
Step2CloseBA.lean:49, 68, 84, 85: `Sizes.seqP (sz.withLam 0)` only; line 254 is inside an `example`
  other hits: proofs (IterBA:65, 209, 214, 733-737; CloseBA:50, 56, 86, 184, 191), docstrings (IterBA:60, 195-196, 701; CloseBA:177),
  `local notation μ0` (CloseBA:208), the private `Step2IterBA_prof_le` (IterBA:178-180, R1 forward comparison, proof-internal)
$ open private lines: IterBA:46-49 (NewKLKBA_conv_P, NewKLKBA_tail; nkl_*; NewKLKGen_bound2, NewKLKGen_ward_LKM; st2sSeq*, st2s_*)
```
- Public premises: `3 ≤ d`/`2 ≤ d`/`0 < d`, `0 < κ`, `BAFlow` (all deterministic; `flow_sz0` shows `BAFlow` is satisfiable), the class pins
  `Step2IterGen_*` (merged T1a/T1b statements), and the stage-L pins `BALWterm d`, `BALWtermExp d` (input (a), merged `abbrev`s
  `BA/LWPinsBA:45, 47`, owner BA-L6). No unproved `Prop` beyond input (a) enters a public statement. Input (b) is now proved (9b).
  The `STStep2G` binders (Step 1, `STLKgL`, `STDecaygL`, `STConStInd`) are parts of the pin's conclusion, not premises.
- No cycle: the dependencies are merged results (the merged-source table in the prove report, §(b), is consistent with the build); the
  new files import only merged modules and each other.
- The comparison text `≤ A *` appears only in the private R1 lemmas and in proofs (prove report §(b) grep; the public statements above
  contain none). UBA-C1 is respected, so stop rule 3 is not triggered.

## 5. Compiled nonempty instances (target 12)
`d = 3`, `sz0` (L_n = 4(n+1), W_n = (2(n+1))^5, g_n = (2(n+1))^-6), `zSeq`, `flow_sz0 : BAFlow sz0 … zSeq` at (κ,ε,𝔠,𝔡) =
(1/2, 1/10, 1/6, 1/10), s ≡ 1/10 < t ≡ 1/2 ≤ t₀ (`half_lt_t0`). All of these were built in §2.
```
$ grep -c '^example' <new files>   -> RBM3D/BA/Step2CloseBA.lean:5  RBM3D/BA/Step2IterBA.lean:7
```
| target | instance (file:line) | open hypotheses of the example |
|---|---|---|
| 1 | IterBA:793, `ω : PathΩ sz0`, n = 0, k = 1, K ≡ 3 | none (ω is a sample point) |
| 2 | IterBA:798, `0 < 1/2` by norm_num, `flow_sz0` | none |
| 3 | IterBA:802 | none |
| 4 | IterBA:806, `3 ≤ 3`, the κ/ε/𝔡 positivities, window 1/10 ≤ 1/2 | none |
| 5 | IterBA:814, `C, δ₀` first, then `∀ᶠ n` at `sz0, zSeq` | none |
| 6 | IterBA:820, `u ≤ 1/2 ≤ t₀` | none |
| 7 | IterBA:827, `STScaleAdm sz0 (1/10) (1/2)` | none |
| 9b | CloseBA:211, u ≡ 1/10 ≤ t₀ | none |
| 8 | CloseBA:216 | `BALWterm 3` (stage L); Step 1, `STLKgL`, `STConStInd` binders |
| 9 | CloseBA:228, Green input = 9b | `STStep1WeakgL`, `STL2decayPTgL` binders |
| 11 | CloseBA:237 | `BALWterm 3`, `BALWtermExp 3`; `STStep2G` binders |
None of these instances is degenerate: N_n = (W_n L_n)^3 → ∞, the window [1/10, 1/2] is nonempty, and no premise is `False`. The witnesses
`sz0`, `zSeq` are polynomial in n. The hypotheses left open are other gates' pins (BA-L6, V), which CLAUDE.md §4 step 2 permits.

## 6. Paper deltas
Prove report §(d) proposes **T2487a** (`lem:newKLK` at BA, `3_5:371`, `7_8:1994`: kernel at `g₀ = √t₀ g`, profile at `g`, `K_c = A K_c⁰`,
`A = (κ+1)/κ`; F1) and **T2487b** (the Step 2 one-loop input, `Def_Ktza` `1_2:988`, read under `0 < κ` and the flow: `BAKsol` = 0 off the
solution set; F2). Together they cover the two Lean/paper differences that the targets introduce. Target 9b reads the existing primed pin
`BAGbEXPij'` (delta T2455a, an earlier row). Target 11 dropping input (b) is a change of Lean inputs, not a paper difference. Coverage is complete.

## 7. Observations (no RETURN)
- O1. Target 11 has fewer hypotheses than `T2487_Step2Holds` (answer (3)), and the BA owner text of `STGijDecgL` moves from U4-BA to
  T1-BA. The dispatcher should update the consumer tickets (T2485, T2486, U3-BA, U4-BA, V) to read `baStep2_holds d hLW hLWE` and `baSTGijDecgL_holds`.
- O2. `Test/Axioms.lean` adds two `owedProps` lines (`BALWterm`, `BALWtermExp`) because the premise scan asks for them. On `main`,
  `git grep -n BALWterm main -- 'RBM3D/*.lean'` finds only the `abbrev`s, docstrings and `example`s (LWPinsBA:45-102,
  Step2EventsGenTw:29-148), so no public theorem had them as a binder before. The nine other edits are comment text. `#assert_rbm_axioms` passes.
- O3. `open private NewKLKGen_bound2 NewKLKGen_ward_LKM` goes beyond the ticket's list. No `private` is deleted and no merged file is edited (§153 (1) holds).
- O4. The split was not applied (D1): one branch carries targets 1-12, and no `t/T2487b` is needed.

## Verdict
| target | statement | vacuity/hidden/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1, 3, 4, 6, 7 (`baStep2Mat_Hpath_herm`, `baStep2Mat_listLink`, `baStep2_K2`, `baSTBdatagL_holds`, `baScaleExists_holds`) | = pin | ok | IterBA:793/802/806/820/827 | ok | none needed | PASS |
| 2 `baStep2_oneLoop` | = pin | ok | IterBA:798 | ok | T2487b | PASS |
| 5 `baStep2_newKLK` | = pin | ok (F1 uniform C) | IterBA:814 | ok | T2487a | PASS |
| 8 `baSTOptL2gL_holds` | = pin | ok (input (a)) | CloseBA:216 | ok | none needed | PASS |
| 9b `baSTGijDecgL_holds` | = `T2487_BAGijDec` | ok | CloseBA:211 | ok | T2455a (existing) | PASS |
| 9 `baSTLocalAvgOfL2gL_holds` | = pin | ok | CloseBA:228 | ok | none needed | PASS |
| 10 private skeleton | = shape (diff §3) | ok | via 11 | ok | T2487b | PASS |
| 11 `baStep2_holds` | stronger than pin (answer (3)) | ok (input (a) only) | CloseBA:237 | ok | none needed | PASS |
| 12 instances | — | nondegenerate | 12 examples | ok | — | PASS |

**Ticket verdict: PASS.** The ticket needs no dispatcher sign-off, since answer (3) already covers O1. Report: this file.
