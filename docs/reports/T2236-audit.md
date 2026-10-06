Auditor model: claude-opus-5-5

# T2236 audit (LW-14a, `lem:LWterm_EXP` part a) — round 1, Tue Oct  6 01:40:02 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2236-audit1` (detached at f282b96 = `t/T2236`). Scratch `scratchpad/T2236/`.

## 1. Diff scope and hygiene
```
$ git diff --name-only main...t/T2236
RBM3D/Graph/LWExpTerm.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2236 -- RBM3D/Test/Axioms.lean   (only + line)
+   `RBM.Gauss.Sizes.LWCutExp, -- one cut of `(eq:EGC)` in expectation, `(eq:ELW_term)` (`B:10-13`), premise of `lwTermEXP_of_cut` (T2236): LW-14b
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWExpTerm.lean
0
$ grep -nE "^import" RBM3D/Graph/LWExpTerm.lean
6:import RBM3D.Graph.LWPins
7:import RBM3D.Induction.ExpAvg
8:import RBM3D.Induction.ConArgDet
9:import RBM3D.Loop.KLFinal
```
No merged file is modified; no `structure`/`class` declared in the new file. Public names: the 4 pinned defs, 3 pinned theorems, `lwExpTerm_prec_integral` (stem-prefixed), 3 instances `lwExpTerm_inst_*`; all other helpers `private`.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.LWExpTerm      (errors: none; 181 warning lines, all longLine/style)
Build completed successfully (3852 jobs).
$ lake build RBM3D                       (branch root, to run the pre-check)
Build completed successfully (4039 jobs).
build exit=0
$ lake env lean verify.lean   (excerpt; full output below in §3)
'RBM.Gauss.Sizes.lwTermEXP_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI41_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm_prec_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm_inst_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm_inst_I1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm_inst_I41' depends on axioms: [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.Graph.LWExpTerm\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean
axiom audit: 6879 theorems, 2336 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
  RBM.Gauss.Sizes.LWtermEXP: 19 [no certificate]
  RBM.Gauss.Sizes.LWCutExp: 2 [no certificate]
...
exit=0
```

## 3. Statements against the pins (script)
`verify.lean` = header (`import RBM3D.Graph.LWExpTerm`, the check file's `open` lines) + the check file's text from `namespace T2236Check` to `/-! ## Section 3` copied by a python slice (unedited) + the lines below.
```
theorem pin_cut (d : ℕ) : LWCutExpPin d ↔ LWCutExp d := Iff.rfl
theorem pin_I1 (d : ℕ) : LWExpI1Pin d ↔ LWExpI1 d := Iff.rfl
theorem pin_I41 (d : ℕ) : LWExpI41Pin d ↔ LWExpI41 d := Iff.rfl
theorem pin_G5 (d : ℕ) : LWExpG5Pin d ↔ LWExpG5 d := Iff.rfl
theorem thm_cut (d : ℕ) : LwTermEXPOfCutPin d := @lwTermEXP_of_cut d
theorem thm_I1 (d : ℕ) : LWExpI1Pin d := @lwExpI1_holds d
theorem thm_I41 (d : ℕ) : LWExpI41Pin d := @lwExpI41_holds d
$ lake env lean verify.lean | grep -v longLine ; echo exit
(7 axiom lines of §2)
@lwExpTerm_prec_integral : ∀ {d : ℕ} (sz : Sizes d) {V : ℕ → Type} (X : (n : ℕ) → V n → sz.SeqΩ → ℂ)
  (R : (n : ℕ) → V n → ℝ) {Kenv Kf : ℝ},
  sz.SizeTendsto →
    (∀ᶠ (n : ℕ) in atTop, ∀ (v : V n) (ω : sz.SeqΩ), ‖X n v ω‖ ≤ ↑(sz.size n) ^ Kenv) →
      (∀ᶠ (n : ℕ) in atTop, ∀ (v : V n), ↑(sz.size n) ^ (-Kf) ≤ R n v) →
        (sz.Prec (fun n v ω => ‖X n v ω‖) fun n v x => R n v) →
          sz.Prec (fun n v x => ‖∫ (ω : sz.SeqΩ), X n v ω ∂sz.seqP‖) fun n v x => R n v
exit=0
```
So: target 1 (`LWCutExp`, `LWExpI1`, `LWExpI41`, `LWExpG5`) is definitionally the pinned text; targets 2–4 have exactly the pinned types, no added hypothesis, no primed successor.

Against the paper (`B:39-43`, `:59-72`; `6:83-88`), read from `paper/tex/B_graphical_lemmas.tex`:
- `LWExpI1`: paper `I₁ = m Σ_{a₁} S^B_{a₁b} 𝔼 tr(ǦE_{a₁}) 𝓛^{(2)}_{(-,+),(a,b)} ≺ B³`; Lean: all charges `(σ₁, σ)`, without `m` — stronger or equal (`|m| ≤ 1`). Hypotheses `STFlow`, `0 ≤ t ≤ lemT z`, `LWAvgLaw` (`Gt_avgbound_flow`), `STLK` (`Eq:L-KGt-flow`) ⊂ the lemma's `(Gt_bound_flow)–(Eq:Gdecay_flow)`; `(res_ELK_n=1)` is derived internally (`STExpAvgAt_of_LWAvgLaw`), not assumed.
- `LWExpI41`: paper `I₄₁ = m W^d Σ S^B S^B 𝔼 tr(ǦE_{a₁}) 𝓛^{(2)}_{(-,+),(a,a₂)} 𝓛^{(2)}_{(-,+),(a₃,b)} ≺ η_t⁻¹B³`; Lean: same sum and exponents, `η_t⁻¹ = (etaT …)⁻¹`, both `σ₁`, no `m`; hypotheses add `STLmax` (`Gt_bound_flow`, used at `B:69`), still within the lemma's list.
- `LWCutExp` (premise, not proved here): one `LWcut` bounded by `(1-t)⁻¹B^{5/2}` on `ĝ²/L^d ≤ 1-t`, the hypothesis list of `LWtermEXP` verbatim; the reduction `LWE = LWcut + LWcut` (`LWPins.lean:218`) makes `lwTermEXP_of_cut` a genuine implication to the merged general pin `LWtermEXP`, not a special case.
- Quantifier order: fixed `κ ε 𝔡 𝔠 sz z t` before `Prec` (which carries `∀ τ D, ∀ᶠ n`), as in the merged pins.

## 4. Vacuity, hidden hypotheses, cycles
- No structure fields: the hypotheses are the merged Props `STFlow`, `LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`, `STDecay` (other gates' pins, already in the registry) and `LWCutExp` (registered owed, LW-14b).
- No cycle: `lwExpI1_holds`/`lwExpI41_holds` have no premise beyond the pin (checked by `@name` above), so every dependency is a proved merged theorem; the axiom print rules out `sorry`.
- External hypotheses: none new (`LWCutExp` is an internal owed pin, proved by LW-14b/c; registered).

## 5. Compiled nonempty instances (`RBM3D/Graph/LWExpTerm.lean:1223-1253`)
```
$ sed -n "1230p;1239,1240p;1252,1253p" RBM3D/Graph/LWExpTerm.lean
  inst_LWtermEXP (lwTermEXP_of_cut 3 hcut) h1 h2 h3 h4 h5
  lwExpI1_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLW hLK
  lwExpI41_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLW hLmax hLK
$ grep -n "def sz0" -A4 RBM3D/Defs/Sizes.lean; grep -n "def z0\|def tInst\|theorem flow_z0" -A1 RBM3D/Induction/Defs.lean
260:def sz0 : Sizes 3 where
261-  L := fun n => 4 * (n + 1)
262-  W := fun n => (2 * (n + 1)) ^ 5
263-  lam := fun n => ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
413:def z0 (n : ℕ) : ℂ := ⟨1 / 2, ((sz0.size n : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))⟩
435:theorem flow_z0 : STFlow sz0 (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0 :=
440:def tInst : ℕ → ℝ := fun _ => 1 / 16
```
Deterministic hypotheses (`3 ≤ 3`, positivity, `STFlow` by merged `flow_z0`, `0 ≤ tInst ≤ lemT z0` by merged `tInst_range`) are all discharged. Data are nondegenerate: `d = 3`, `L ≥ 4`, `W ≥ 32`, `N ≥ 2^21`, `t = 1/16`; index sets `Bool × (Fin 2 → Bool) × (Fin 2 → Zd 3 L)` are nonempty, and the subtype `lam²/L³ ≤ 15/16` holds for every `p` (`lam ≤ 2^{-6}`). Remaining hypotheses are other gates' pins (`LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`, `STDecay`, `LWCutExp`), as the ticket's instance shape (1) prescribes. All three compile (module build, §2).

## 6. Paper deltas
Candidates in the prove report (d): `T2236a` (`(res_ELK_n=1)` used in `B:40-42`, `:64-66` but outside `lem:LWterm_EXP`'s hypothesis list; derived in Lean from `LWAvgLaw`), `T2236b` (`𝓛^{(2)}_{(-,+)} ≥ 0` used silently at `B:61`; proved in Lean), `T2236c` (pins drop `m` and cover all charges: stronger or equal). These cover every Lean/paper statement difference of targets 3–4. `LWCutExp`'s `(1-t)⁻¹` versus `(eq:ELW_term)`'s `η_t⁻¹` is the pin of LW-14b (equivalent up to `√(2/κ)`, prove report (a)(i) row 27 and (d) bullet 1); no delta is owed by this ticket.

## 7. Verdicts
| target | verdict |
|---|---|
| 1 vocabulary `LWCutExp`, `LWExpI1`, `LWExpI41`, `LWExpG5` | PASS (`Iff.rfl` to pins) |
| 2 `lwTermEXP_of_cut` | PASS |
| 3 `lwExpI1_holds` | PASS |
| 4 `lwExpI41_holds` | PASS |
| 5 instances `lwExpTerm_inst_cut`, `_I1`, `_I41` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.

## 8. Observations (no verdict impact)
1. **Merge mechanics (for the hub).** `main` changed `RBM3D/Test/Axioms.lean` after the branch base:
```
$ git merge-base main t/T2236 → f6650b2; main = e5b944a
$ git diff --stat f6650b2 main -- RBM3D/Test/Axioms.lean
 RBM3D/Test/Axioms.lean | 4 +---
$ git merge-tree --write-tree main t/T2236 → clean (exit 0)
```
   Copying the branch's `Axioms.lean` wholesale would revert main's T2234/T2235 registry lines (`AnpDetGhStep` back, `STStep6IV`, `STExpIntIII`, `STExpIntIV` re-added). Apply only the one `+ LWCutExp` line (or a 3-way merge of that file); the new `LWExpTerm.lean` has no conflict.
2. `LWExpG5` is defined but not registered: the ticket expected it, but it is a premise of no theorem in this file, so the pre-check does not list it (report (b) item 8 states this). LW-14b/c must register it once it becomes a premise.
3. Preflight (a)(i) disagrees with the ticket's normalisation remark (`(eq:ELW_term)` = one `LWcut` with factor 1, not `W^{-d}`); this is for LW-14b, and no statement here depends on it.
