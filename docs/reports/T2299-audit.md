Auditor model: claude-opus-5-5

# T2299 audit (round 1) — Tue Oct  6 14:07:01 UTC 2026

Ticket T2299 (= "T2292b" of `docs/tickets/T2292.md`, paragraph "Split"). Branch `t/T2299` at 993f772 (merge-base ad9bb6d).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2299-audit1` (detached at 993f772). Target: `RBM.Ind.stOeqNZ''_holds : ∀ d, STOeqNZ'' d`, with pins `STNZConcl''`, `STOeqNZ''`.

## 1. Statement against the pin (check file `docs/tickets/checks/T2299-check.lean` §2-§3)

```
$ awk-extract def STNZConcl'' from check §2 (binders {d} (sz : Sizes d) normalised to the file's section variables) and from the new file; diff
== diff check-pin vs file-pin (binder line normalised)
IDENTICAL
      15 pin_new.txt
== STOeqNZ''
T2299-check.lean:232:def STOeqNZ'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConcl'' sz E s t)
QtNonzeroFlowLift.lean:88:def STOeqNZ'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConcl'' sz E s t)
== merged STNZConclPT'' (QtNonzeroFlow.lean) vs new STNZConcl''
8c8
<     PrecPT sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
---
>     Prec sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
```
The only hunk against the merged per-time pin is `PrecPT ↦ Prec`, which is exactly what the ticket allows. Hypotheses,
the index set (every `σ`, every `A ⊇ I_diff σ`, every label), the normalisation `/B_u^{n_}` and the right side
(`B_u^{1/6} XLK n_ + STbootRHS 2 … B_s n_ p`, R2*) are unchanged.

Compiled statement script (check-file imports + `import RBM3D.Induction.QtNonzeroFlowLift` + check §2-§3 verbatim, namespace `RBM.Gauss.Sizes.T2292Check`, then):
```
example : RBM.Gauss.Sizes.T2292Check.T2292b_stOeqNZ''_holds := @RBM.Ind.stOeqNZ''_holds
example : @RBM.Gauss.Sizes.T2292Check.STNZConcl'' = @RBM.Gauss.Sizes.STNZConcl'' := rfl
example : @RBM.Gauss.Sizes.T2292Check.STOeqNZ'' = @RBM.Gauss.Sizes.STOeqNZ'' := rfl
#check @RBM.Gauss.Sizes.STNZConcl''
#print axioms RBM.Ind.stOeqNZ''_holds
$ lake env lean $S/stmt.lean; echo EXIT
@RBM.Gauss.Sizes.STNZConcl'' : {d : ℕ} → RBM.Gauss.Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
'RBM.Ind.stOeqNZ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT 0
```
Statement verdict: **matches the pin** (text identical, and the type of the target is the check file's `T2292b_stOeqNZ''_holds`).

## 2. Vacuity, hidden hypotheses, cycles

```
$ grep -nE "^(theorem|lemma|def|abbrev)" QtNonzeroFlowLift.lean      (public declarations)
68:def STNZConcl'' (E s t : ℕ → ℝ) : Prop :=
88:def STOeqNZ'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz
763:theorem stOeqNZ''_holds : ∀ d : ℕ, STOeqNZ'' d := by
799:theorem inst_OeqNZ'' :
$ grep -cE "^private (theorem|lemma|def)" QtNonzeroFlowLift.lean
22
```
- No new structure; the target's only premises are those of the merged `STIngR` (unchanged); no hypothesis is added.
- Proof of the target (file :763-779): `stOeqNZPT''_holds d …` (merged T2292, 59a0ab5, `QtNonzeroFlow.lean`) then `v3_premises_of_stFlow`
  and the private `nzLift_lift`, with the same `𝔠d` as the per-time theorem. Its dependencies are merged results
  (`stOeqNZPT''_holds`, `nqFlowSharp`, `stKloop_lip`, `LemDecCalELip_Lloop_sub/_env`, `ContinuityNet.cont_highProbAt_good`).
  There is no cycle: the target is not used in its own proof, and no module imports the new file.
- External hypotheses: none were added, so no limit check is owed.
- §95 (3): the lift adds no drift or good-set level. Its only event is `contGood` (merged `ContinuityNet`). `ζ♯` is deterministic in the controls.

## 3. Compiled nonempty instances (file :791-958, namespace `RBM.Ind.QtNonzeroFlowLiftInst`)
- **(1) `inst_OeqNZ''` (:799):** `inst_ing STCaseII … (stOeqNZ''_holds 3) szB zB flow_zB` at `s ≡ 15/16`, `t ≡ 31/32`, `C_d = 1`.
  Every deterministic premise is discharged: `0 ≤ s`, `s < t` (`norm_num`), `szB_flow_ht`, `szB_caseII` (`1−s = 1/16 = λ²/L²`), `conStInd_const`, and `0 < 1`.
  The data are nondegenerate: `d = 3`, `L = 4`, `W_n = n+4`, `N_0 = 4096`, and the window is not collapsed.
- **(2) The applied form (:812):** `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`, with `STKbound`/`STKward` discharged by `stKbound_of_flow`/`stKward_of_flow`.
  The hypotheses that remain are `STLK s`, `STStep2Concl` and the two pair hypotheses `Ξ̂ ≺ 1`. These are stochastic pins of other gates, which the ticket allows.
- **(3) Further instances:**
  - `nzLift_xi_close_ev` at the data, with all deterministic hypotheses discharged and `.exists` taken (:839).
  - `0 ∈ contGood szB n` (:861).
  - `#V ≤ N^6` at size index 0 (:865).
  - The parameter type is nonempty, with members `(sig3, {0,1})` and `(const true, ∅)` (:872, :876).
- **Helper instances (:882-950):** `nzLift_arith`, `nzLift_proj_le`, `nzLift_core_below`, `nzLift_netPt_floor`, `nzLift_bootRHS_mono` and the envelope, each at numbers.
- **Statement examples (:954, :956).**
All of these compile (§4 build). None is degenerate: there is no `N = 0`, no empty index set, no collapsed window, no `False` premise, and no astronomically large witness.

## 4. Build, axioms, hygiene, diff scope

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2299-audit1; date -u; time lake build RBM3D.Induction.QtNonzeroFlowLift 2>&1 | grep -E "error|warning|axioms|Build|sorry"   (axiom lines of upstream modules omitted)
Tue Oct  6 14:05:24 UTC 2026
warning: RBM3D/Induction/QtNonzeroFlowLift.lean:24:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/QtNonzeroFlowLift.lean:29:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/QtNonzeroFlowLift.lean:32:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/QtNonzeroFlowLift.lean:33:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/QtNonzeroFlowLift.lean:37:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3861 jobs).
lake build RBM3D.Induction.QtNonzeroFlowLift 2>&1  13.28s user 6.75s system 158% cpu 12.620 total
$ (same build, axiom lines of the new module)
info: RBM3D/Induction/QtNonzeroFlowLift.lean:964:0: 'RBM.Gauss.Sizes.STNZConcl''' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlowLift.lean:965:0: 'RBM.Gauss.Sizes.STOeqNZ''' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlowLift.lean:966:0: 'RBM.Ind.stOeqNZ''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QtNonzeroFlowLift.lean:967:0: 'RBM.Ind.QtNonzeroFlowLiftInst.inst_OeqNZ''' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/QtNonzeroFlowLift.lean | wc -l
       0
$ git diff --name-status main...t/T2299
A	RBM3D/Induction/QtNonzeroFlowLift.lean
$ git diff --name-only main...t/T2299 -- RBM3D/Test RBM3D.lean | wc -l
       0
```
- The build has no errors. Its only warnings are 5 `longLine` style warnings in the module docstring (:24-37), even though `set_option linter.style.longLine false` is at :42, after the docstring. This is an observation only.
- The axioms are only `propext`, `Classical.choice` and `Quot.sound`.
- The diff touches only the sole writable file. No merged file or frozen signature is changed, and the registry is unchanged, as the ticket expects.

## 5. Paper deltas

```
$ grep -n "T2292a\|T2258a\|T2299" docs/paper-deltas.md | cut -c1-120
1530:- **D571（T2258a–b）**：一致于 `u` 的 `STNQConcl''`（`(am;asoiuw)`）由逐时刻形经控制量单调包络 `X♯` 上的单侧网得出（`nqFlowSharp`、`stOeqNQ''_hold
1563:- **D604（T2292a, c–e）**：情形 (ii) 逐时刻端点在流处对 `Q^{(A)}(𝓛−𝒦)^{(n_)}`、一切 `σ`、一切 `A ⊇ I_diff(σ)` 陈述（`STNZConclPT''`），`STbo
$ sed -n '1931p' paper/tex/3_5_Loop_Hierarchy.tex | cut -c1-120   (excerpt)
solving which yields \eqref{am;asoi222} at $u=t$. Obviously, the same argument applies to each fixed $u\in [s,t]$. Fin
```
- **Inherited differences.** The index set (every `A ⊇ I_diff σ`) and the R2* first summand at `B_s` are inherited from `STNZConclPT''`. Both are covered by D604 (T2292a).
- **New differences.** The prove report (d) proposes two candidates:
  - `T2299a`: the uniform form is derived before the `newPQ` bootstrap, whereas the paper lifts after it (`3_5:1931`).
  - `T2299b`: the `Q^{(A)}` time modulus, with factor `2^{n_}` (`(normQA2)`), and the threshold `2^{n_}(3n_+1) ≤ N`.
- Every Lean/paper difference of this ticket is therefore covered.

## Observations (no effect on the verdict)
- The 5 `longLine` warnings in the module docstring (see §4).
- Prove report (b): the name-clash grep for `STOeqNZ''` reports one hit in the docstring of merged `QtNonzeroFlow.lean:21`. This is a docstring mention, not a declaration.

## Verdict
- `RBM.Ind.stOeqNZ''_holds` (with pins `STNZConcl''`, `STOeqNZ''`): **PASS**.
- No dispatcher sign-off is needed.
