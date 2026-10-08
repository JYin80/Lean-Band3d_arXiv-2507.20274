Auditor model: claude-opus-5-5

# T2314 audit (round 1): S3-18b2b `Induction/QtXiRoundLift`, lift `PrecPT -> Prec` and `lem:STOeq_Qt` (case (i))

Written Thu Oct  8 02:28:55 UTC 2026 (`date -u`). Audit worktree `../RBM3D-wt/T2314-audit1`, detached at `t/T2314` 3967cc9.
`git merge-base --is-ancestor main t/T2314` -> "main is ancestor of t/T2314".

## 1. Statements against the pins (script)

Scratch file = `docs/tickets/checks/T2314-check.lean` with `import RBM3D.Induction.QtXiRoundLift` added and, inside
`namespace RBM.Gauss.Sizes.T2314Check`:
```
example : T2314_stXiRoundQt_holds := @RBM.Ind.stXiRoundQt_holds
example : T2314_stOeqQt'_holds := @RBM.Ind.stOeqQt'_holds
example : T2314_consumer_I := fun d h => RBM.Ind.stXiBootR_of_round d STCaseI h
#print axioms RBM.Ind.stOeqQt'_holds
$ lake env lean T2314pincheck_tmp.lean      -> exit 0, 0 lines matching "error"
'RBM.Ind.stOeqQt'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The pins are `T2314_stXiRoundQt_holds := ∀ d, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t)` and
`T2314_stOeqQt'_holds := ∀ d, STOeqQt' d`; both are checked by definitional type ascription. The file's statements are:
```
714: theorem stXiRoundQt_holds : ∀ d : ℕ, STIngR d STCaseI (fun sz E s t => STXiRound' sz E s t) := by
736: theorem stOeqQt'_holds : ∀ d : ℕ, STOeqQt' d := fun d => stXiBootR_of_round d STCaseI (stXiRoundQt_holds d)
```
The private helper shapes are checked in the file itself (`:1053-1090`, `example … := @qtLift_diag_PT`, `@qtLift_diag_to_pair`,
`@qtLift_xiLK_close`, `@qtLift_lift`, `@qtLift_zeta_mono`). Their texts match `T2314_diag_PT`, `T2314_diag_to_pair`,
`T2314_xiLK_close`, `T2314_lift` and `T2314_zeta_mono` of the check file token for token, and they compile (§4).
- Hypotheses, quantifier order, regime, and the constant `𝔠_d ∈ (0, 1/100]` all come from the merged `STIngR`
  (`Step34Pins.lean:445-453`), unchanged. The conclusion is the merged `STXiRound'` / `STXiBoot'` (unchanged, §4).
  There is no special case: both theorems are unconditional, for every `d`. Verdict: **statement PASS** for both targets.

## 2. Vacuity, hidden hypotheses, cycles

- Neither target has a hypothesis. `stXiRoundQt_holds` uses `stOeqQtRoundPT''_holds` (T2313) and
  `RBM.Green.v3_premises_of_stFlow`, then the private `qtLift_lift`. `stOeqQt'_holds` = `stXiBootR_of_round d STCaseI` (T2304).
  Both inputs are merged:
```
$ git grep -n -E "theorem (stOeqQtRoundPT''_holds|stXiBootR_of_round)" main -- RBM3D
main:RBM3D/Induction/QEndB1.lean:1841:theorem stOeqQtRoundPT''_holds : ∀ d : ℕ, STOeqQtRoundPT'' d := by
main:RBM3D/Induction/QtNonzeroBoot.lean:581:theorem stXiBootR_of_round (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
```
- The lift's binders (`QtXiRoundLift.lean:640-645`) are plain hypotheses, with no structure fields: `3 ≤ d`, `0 < κ'`,
  `0 < gmax`, `|E n| ≤ 2-κ'`, `SizeTendsto`, `0 ≤ s < t < 1`, `∀ᶠ (1-t)⁻¹ ≤ N`, `∀ᶠ 0 < lam ≤ gmax`, `STXiRoundPT''`.
  `stXiRoundQt_holds` (`:714-734`) discharges every one of them from `v3_premises_of_stFlow`, `RangeCond` and
  `qtLift_flowLam`. The file has no external hypothesis and adds no new pin or `def` in `RBM.Gauss.Sizes`.
- There is no cycle: the new module imports only merged modules (`:6-14`), and nothing imports it.
- Registry scan (my run; root built in the audit worktree with `lake build RBM3D` -> exit 0, "Build completed successfully (4123 jobs)"):
```
$ printf 'import RBM3D\nimport RBM3D.Induction.QtXiRoundLift\n#assert_rbm_axioms\n' > T2314reg_tmp.lean; lake env lean T2314reg_tmp.lean
reg exit 0
axiom audit: 8983 theorems, 2923 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).
registry: 2 borrowed + 139 owed + 105 structural + 7 refuted + 12 superseded; 117 registered premise(s) carry nothing yet: …
```
  The owed count goes 140 -> 139 (the prove report's "before" run shows 140; `found` stays at 148). No new unregistered
  premise is flagged, and `STXiRoundPT''` reaches no public binder. Verdict: **PASS**.

## 3. Compiled nonempty instances (namespace `RBM.Ind.QtXiRoundLiftInst`)

The data is `sz0` (`d = 3`, `n = 0`: `L = 4`, `W = 32`, `N = 2^21`), the flow `z0` with `flow_z0` (`κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`), `sInst ≡ 0`, `tInst ≡ 1/16`, `sz0_caseI`, `sz0_con`, and `C_d = 1`.
- (1) `inst_OeqQt'` `:756` and (2) `inst_RoundQt` `:761` are `inst_ing STCaseI _ (stOeqQt'_holds 3 | stXiRoundQt_holds 3)
  sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos`. Every deterministic hypothesis is discharged.
- (3) `:770`, (3′) `:786` and (3″) `:802` open the conclusion of `STXiBoot'` at `n_ = 2` and of `STXiRound'` at `n_ = 3` and
  `n_ = 2`, with `p = 1` and `XL ≡ XLK ≡ 1`. `STKbound` and `STKward` are discharged by `stKbound_of_flow` and
  `stKward_of_flow`. The remaining hypotheses are `STLK`, `STStep2Concl` and the pair controls `Ξ̂ ≺ 1`; these are other
  gates' stochastic pins, which the ticket allows.
- (7) `:1021` applies `qtLift_lift` at the data. The one remaining hypothesis is `STXiRoundPT''` (the T2313 pin; the merged
  instance `inst_OeqQtRoundPT''` exists). `κ' = 1/20`, `gmax = 10`, `t < 1`, `inst_htN` and the `lam` window are discharged.
- (4) `:828`: `qtLift_xiLK_close` at `n_ = 2`, `A = 32`, `[0, 1/16]`, with the `∃ n` form.
- (5) `:850`: the core at `V = Unit`, with `ξ = u`, `ζ ≡ 1` and `Ξ = contGood`.
- (6) `:891-980`: the envelope, including a jump control with `X♯(0) = 3 ≠ 4 = X(0)`.
- (7′) `:982-988`: the pair and diagonal index sets are nonempty, with both `q.1.1 < q.1.2` and `q.1.1 = q.1.2`.
- (8) `:1032-1047`: the pinned types, the `rfl` unfolding of `STOeqQt' 3`, the consumer term, and `PT'' -> PT'`.
- No instance is degenerate: there is no `N = 0`, empty index, collapsed window (`0 < 1/16`) or `False` premise, and the
  witness is moderate (`N = 2^21` at `n = 0`, all statements `∀ᶠ`). Verdict: **PASS**.

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Induction.QtXiRoundLift       (audit worktree)
ℹ [3905/3905] Built RBM3D.Induction.QtXiRoundLift (6.0s)
info: RBM3D/Induction/QtXiRoundLift.lean:1095:0: 'RBM.Ind.stXiRoundQt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtXiRoundLift.lean:1096:0: 'RBM.Ind.stOeqQt'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtXiRoundLift.lean:1097:0: 'RBM.Ind.QtXiRoundLiftInst.inst_OeqQt'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtXiRoundLift.lean:1098:0: 'RBM.Ind.QtXiRoundLiftInst.inst_RoundQt' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3905 jobs).   exit 0;  grep -c "^error" build.log -> 0
$ touch …/QtXiRoundLift.lean; /usr/bin/time -p lake env lean RBM3D/Induction/QtXiRoundLift.lean | grep -E "error|sorry|real"
real 6.54
$ grep -nE "sorry|admit|native_decide|^axiom| axiom |open private|_private|maxHeartbeats" RBM3D/Induction/QtXiRoundLift.lean
(no output)
$ git diff --name-only main...HEAD
RBM3D/Induction/QtXiRoundLift.lean
RBM3D/Test/Axioms.lean
$ git diff --patience main...HEAD | grep -c '^-[^-]'
2
```
The registry hunk (`Test/Axioms.lean`) does exactly what the ticket asks: it deletes the `STOeqQt'` owed line, and it changes
the `STXiRound'` comment tail to "case (i) proved by `stXiRoundQt_holds` (T2314); no generic proof". There are no other
`-` lines. No merged file or frozen signature changes. The only public declarations are `stXiRoundQt_holds`,
`stOeqQt'_holds`, `inst_OeqQt'` and `inst_RoundQt`; every helper is `private` with prefix `qtLift_` (or the private
`inst_htN`). The name-clash grep (`git grep -F` on `main`, `RBM3D` and `RBM3D.lean`, excluding the docstring at
`QtNonzeroBoot.lean:579`) gives 0 hits each for `stXiRoundQt_holds`, `stOeqQt'_holds`, `QtXiRoundLiftInst`, `inst_OeqQt'`
and `inst_RoundQt`. Verdict: **PASS**.

## 5. Paper deltas

The one Lean/paper difference is in proof order and form. The paper (`3_5:1764`) solves first and then applies an
`N^{-C}`-net. The Lean proof applies a one-sided floor net on the diagonal to the round, using the monotone envelope, and then
the deterministic bootstrap. This is proposed as `T2314a` (prove report §(d), line 209), as the ticket expected. The statement
itself is the merged pin, so the file adds no new statement delta. Verdict: **PASS**.

## Observations (no effect on the verdict)

- The file has 1098 lines, against the ticket's 720/850/1000 estimate; the stop rule (1200) is not reached.
- The proof is regime-agnostic as gate §29 (2) requires: `STCaseI` enters only through `stOeqQtRoundPT''_holds`.

## Verdict

- `RBM.Ind.stXiRoundQt_holds`: **PASS**.
- `RBM.Ind.stOeqQt'_holds`: **PASS**.
- Ticket T2314: **PASS**; no dispatcher sign-off is needed.
