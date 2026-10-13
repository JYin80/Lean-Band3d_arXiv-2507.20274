Auditor model: claude-opus-5-5
# T2492 audit (round 2) — Tue Oct 13 07:16:25 UTC 2026
Branch `t/T2492` at 9f0a3641 (repair of round 1), merge-base with `main` 4e78c3da; audit worktree `../RBM3D-wt/T2492-audit2` (detached, fresh).
Scope: section (a) did **not** confirm the split (central 1,758 <= 1,950), so targets 1-11 are audited. T2486 (a) is on the base, so the closure `baGridGood_holds` exists (no `HOLD closure`).

**Verdict: PASS** (targets 1-11). The round-1 defect (merged `STKboundgL`/`STKwardgL` left as instance hypotheses) is repaired. No dispatcher sign-off needed.

## 1. Statements against the pins
Scratch `T2492/pins_audit2.lean`: the check's imports (lines 16-33) + `import RBM3D.BA.GridGoodBA`, Part 2 of `docs/tickets/checks/T2492-check.lean` verbatim (lines 159-327; the 7 `example : Prop` shapes renamed `def Shape1..7`), then:
```
example : T2492_WalkForm := fun {d} => @baStep2Mat_walkForm d
example : T2492_ImLeOne := fun {d} => @baStep2Mat_imLeOne d
example : T2492_SLaw := fun {d} => @baStep2Mat_S d
example : T2492_ProbPp := fun {d} => @baStep2Mat_isProb d
example : T2492_KLink := fun {d} => @baHierDrift_kLink d
example : T2492_KClasses := fun {d} => @baHierDrift_kClasses d
example : T2492_Expand := fun {d} => @baHierDrift_expand d
example : T2492_DriftClasses := fun {d} => @baHierDrift_classes d
example : T2492_InitMem := fun {d} => @baGoodSetNg_init d
example (d : ℕ) : T2492_BAGridGood d := @baGridGood_holds d
example : Shape1 := fun {d} => @baGridDrift_ev d
example : Shape2 := fun {d} => @baGridDrift_envelope d
example : Shape3 := fun {d} => @baQVPropagated d
example : Shape4 := fun {d} => @baYMoments d
example : Shape5 := fun {d} sz lam0 E _ s t K => @baAzumaSubG d sz lam0 E s t K
example : Shape6 := @baGridGood_of
example : T2492_Expand := fun {d} => @baHierDrift_kLink d -- NEGATIVE CONTROL
$ lake env lean pins_audit2.lean 2>&1 | grep error
pins_audit2.lean:204:20: error: Type mismatch        # Shape6
pins_audit2.lean:205:37: error: Type mismatch        # negative control
$ lake env lean pins_audit2_fixed.lean 2>&1 | grep error   # same file, "STEKDecaygL (Sizes.seqP" -> "STEKDecaygL (sz := sz) (Sizes.seqP"
pins_audit2_fixed.lean:205:37: error: Type mismatch  # negative control only
```
All ten binding pins (targets 1-8) are matched exactly by the branch's declarations, up to binder style. That covers hypotheses, quantifier order and the eventual parts. Target 6: `KLoop ∧ KTwo ∧ UStep` hold `∀ᶠ n` and the rest hold every `n`. Target 7: `∃ C₀` comes before `(𝔠, sz, z)`, then the levels, then `∀ᶠ n`. Target 8 holds for every `d`. Shapes 1-5 also match.
Shape6 (not binding) mismatch is a check-text defect:
```
$ sed -n 515,517p RBM3D/Chain/Step34Gen.lean
def STEKDecaygL {sz : Sizes d} (μ : Measure sz.SeqΩ) {m : ℕ} (s t : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) : Prop :=
  STEKDecayKgL sz.lam μ s t 𝒜
$ grep -n "STEKDecaygL (sz := sz)" RBM3D/BA/SEforLnBA.lean | head -1     # merged producer baEtermDecaygL
276:        STEKDecaygL (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (m := k)
```
The check text infers `sz := sz.withLam 0`, which gives coupling `0`. The branch writes `(sz := sz)`, as the merged producer does. The closure `baGridGood_of d … (baEtermDecaygL d)` compiles, so the branch text is right. This is an observation, already proposed as T2492c.

## 2. Vacuity, hidden hypotheses, cycles
- The closure is `GridGoodBA.lean:106-109`: `baGridGood_of d (baKcalDecay_holds d) (baStep2Mat_carrierFacts d) (baSEforLn_holds d) (baEtermDecaygL d)`. All four inputs are merged T2486 (a) theorems, so the closure has no cycle and no unproved premise. `baGridGood_of` splits on `3 ≤ d`, and its `¬ 3 ≤ d` branch is the pin's own guard.
- Statement hypotheses: merged `Prop`s (`BAFlow`, `BAReal`, `0 < κ`, `0 < lam0 n`); input (b) `StepDecompGen_LoopForm` (merged `baStep2Mat_loopForm`); input (c) `STKboundgL` (merged `inst_BAKbound`); input (d) `hQ` (owed to U3s2-U3s3).
- No public def, structure or class is added. The X1-C4 grep (§4) finds 3 `private def`s, valued in `ℂ`/`Zd`. The eventual envelope copy is `private theorem GridGoodBA_envelope_ev` (`GridGoodBA.lean:121`).
- Levels and limits: the (D4) level `C₀ = k(1+𝔡⁻²)^{2k}` (`GridGoodBA_ee_level`, private, `:767`) depends on `(𝔡, k)` only, and the pin forces it before `(sz, z)`. Far thresholds are eventual through `Tendsto` (`GridGoodBA_far_ev`, `:1175`). Preflight far.py gives n* = 4 at τ' = 1, so no astronomically large witness is involved.

## 3. Compiled nonempty instances
Data: `d = 3`, `sz0`, `zSeq`, `flow_sz0` at (1/2, 1/10, 1/6, 1/10).
- **Targets 1-6** (`GridDriftBA.lean:678-753`): applied at `n = 1` (`L = 8`, `W = 1024`), grid (0, 1/32, 4). Premises are discharged by `inst_real` (= `BAflow_real`), `inst_lam0_pos` (`baStep2Fam_lam_pos_le`) and `inst_loopForm` (`baStep2Mat_loopForm`). No hypothesis is left. **PASS.**
- **Targets 7-10** (`GridGoodBA.lean:1258-1326`):
  - Target 7: `baGoodSetNg_init` at k = 3, with levels Γ ≡ Φ ≡ 1 and Λ ≡ C₀, then `Eventually.exists`, for every ω. No hypothesis is left.
  - Target 8, two examples: the conditional form at `d = 3` (four facts by name, no hypothesis left); the closure at (1/2, 1/10, 1/10, 1), with windows 1/10 < 1/2 ≤ t₀. The round-1 repair (`git diff 27b930f0 9f0a3641`) now passes `inst_BAKbound` and `baKward_holds 3 le_rfl … sz0 zSeq flow_sz0`.
  - Target 9: the envelope at k = 2, σ = (+,-). It now takes `inst_BAKbound` and has no hypothesis left.
  - Target 10: `baAzumaSubG` and `baYMoments` have no hypothesis left. `baAzumaProxy_subG_goodExit` keeps only `hQ` (input (d)).
- Hypotheses still left are `hLK : STLKgL …` and `hStep2 : STStep2ConclgL …` in the closure instance, plus `hQ`. Each is an owed pin, not a merged result:
```
$ grep -n "RBM.BA.STLKgL\|STStep2ConclgL" RBM3D/Test/Axioms.lean | cut -c1-150
135:   `RBM.BA.STLKgL, -- `(Eq:L-KGt)` (a) at a law `μ` over a flow carrier, hypothesis of the instance `inst_baBootstrap'` (T2269); owe
232:   `RBM.BA.STStep2ConclgL, -- the three Step 2 conclusions that Steps 3-4 consume (`STLocalEntryUgL ∧ STAvgUgL ∧ STGdecayWgL`, `Chain/
$ grep -rn "STLKgL (baFMz\|STStep2ConclgL (baFMz" RBM3D | grep -v GridGoodBA | grep -vE "→ *$|→ |\(h[A-Za-z0-9]* :" | cut -c1-60
RBM3D/BA/Step2CloseBA.lean:242:        STStep2ConclgL (baFMz   # example under STLKgL → STDecaygL → … premises
RBM3D/BA/Step1Prime.lean:1130 / 1147, Step1Fam.lean:370/986/1004   # under a `∀ z', BAFamZ … →` premise
RBM3D/BA/RandomLayerBGBA.lean:62, UNPins.lean:113, FlowPins.lean:1362, SEforLnBA.lean:197   # def bodies / Prop examples / docstring
RBM3D/BA/UNPins.lean:1016 (hyp `UNMLOutBA 3`, time 0); Induction/MainIndOut.lean:209 (hyps STMainIndG/STHorizonG/STBaseG, time 1/2)
```
(Output lines grouped by hand; each hit was read.) No merged theorem concludes either pin unconditionally at this data.
**Targets 7-10 instances: PASS.**

## 4. Build, axioms, hygiene, diff (audit worktree)
```
$ lake build RBM3D.BA.GridDriftBA RBM3D.BA.GridGoodBA
Build completed successfully (4109 jobs).   exit=0
$ grep -E "^warning: RBM3D/BA/Grid(Drift|Good)BA" build_mod.log | sed -E 's/:[0-9]+:[0-9]+:/:/' | sort | uniq -c
   4 warning: RBM3D/BA/GridDriftBA.lean: This line exceeds the 100 character limit, please shorten it!
   3 warning: RBM3D/BA/GridGoodBA.lean: This line exceeds the 100 character limit, please shorten it!
$ lake build          # full library with the branch's root imports (RBM3D.lean +2 lines), #assert_rbm_axioms
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
Build completed successfully (4355 jobs).   exit=0
$ lake env lean ax2.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"   # 24 public theorems/instance
24
$ lake env lean ax2.lean | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -c .
0
$ grep -nE '\bsorry\b|\badmit\b|^\s*axiom\b|native_decide' GridDriftBA.lean GridGoodBA.lean; echo exit=$?
exit=1
$ git diff --stat main...t/T2492
 RBM3D.lean                |    2 +
 RBM3D/BA/GridDriftBA.lean |  757 ++++++++++++++++++++++++++
 RBM3D/BA/GridGoodBA.lean  | 1330 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    2 +-
 4 files changed, 2090 insertions(+), 1 deletion(-)
$ git diff main...t/T2492 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep "^[+-][^+-]" | grep -o "^+import.*\|BA: the initial membership[^)]*)"
+import RBM3D.BA.GridDriftBA
+import RBM3D.BA.GridGoodBA
BA: the initial membership is owed to T4-BA (supervisor 2351 T4S2-C2/C3: only as a hypothesis in `∀ᶠ n` / instance-`n` form)
BA: the initial membership is `baGoodSetNg_init` (T2492, T5-BA; `∀ᶠ n`, 2351 T4S2-C2/C3)
$ wc -l GridDriftBA.lean GridGoodBA.lean        # stop line 2,000 per file
     757 RBM3D/BA/GridDriftBA.lean
    1330 RBM3D/BA/GridGoodBA.lean
```
Every touched file is a sole writable file; no merged file is edited (no frozen signature changes); the registry edit is the ticket's text.

## 5. Ticket greps and layering
```
$ grep -nE 'STGridRepNgL|baStep1_holds\b|\|E\||2 - κ|\bmE\b|zt E|STFlow|lemT|‖m‖ = 1' <both files>; echo exit=$?
exit=1
$ grep -nE '≤ A \*' <both files>; echo exit=$?
exit=1
$ grep -nE '^(noncomputable )?(private )?(def|abbrev|structure|class) ' <both files> | cut -c1-90
RBM3D/BA/GridGoodBA.lean:456:private def GridGoodBA_edge (M : Bool → Matrix (Zd d L) (Zd d
RBM3D/BA/GridGoodBA.lean:642:private def GridGoodBA_eeX {k : ℕ} (a : Fin k → Zd d L) (c :
RBM3D/BA/GridGoodBA.lean:646:private def GridGoodBA_eeY {k : ℕ} (a' : Fin k → Zd d L) (c :
$ grep -rln "import RBM3D.BA.GridDriftBA\|import RBM3D.BA.GridGoodBA" RBM3D RBM3D.lean
RBM3D/BA/GridGoodBA.lean
RBM3D.lean
```
`withLam` appears in public statements only as `seqP (sz.withLam 0)`, plus `(sz := sz) (Sizes.seqP (sz.withLam 0))` in `baGridGood_of`'s `hEK` (the T2486 text); see the §1 extraction.

## 6. Paper deltas
- **T2492a** covers the eventual BA initial membership, the level `C₀ = k(1+𝔡⁻²)^{2k}` and the Combes–Thomas far clauses (target 7).
- **T2492b** covers `KLoop`/`KTwo` holding only past the WO window, and the eventual drift and envelope readings (targets 6 and 9).
- **T2492c** is correctly a check-text observation, not a paper delta. T2492a/b are not yet in `docs/paper-deltas.md` (numbered at merge).
No Lean/paper statement difference is left uncovered.

## 7. Per-target verdicts
| target | statement | instance | verdict |
|---|---|---|---|
| 1 (a)-(c) walkForm / imLeOne / S / S_rowSum / isProb | = pins | no hyp | PASS |
| 2 `baHierDrift_kLink`, `_kLoop` | = pin / in KClasses | no hyp | PASS |
| 3 `baHierDrift_kTwo` | in `T2492_KClasses` | no hyp | PASS |
| 4 `baHierDrift_uStep` | in `T2492_KClasses` | no hyp | PASS |
| 5 `baHierDrift_expand` | = pin | no hyp | PASS |
| 6 `baHierDrift_classes`, `baGridDrift_ev`, `baQVPropagated` | = pin / shapes | no hyp | PASS |
| 7 `baGoodSetNg_init` | = pin | no hyp, nondegenerate | PASS |
| 8 `baGridGood_of`, `baGridGood_holds` | = pin (closure); shape modulo check text | only owed `STLKgL`, `STStep2ConclgL` | PASS |
| 9 `baGridDrift_envelope` | = shape | no hyp | PASS |
| 10 `baAzumaSubG`, `baYMoments`, `baAzumaProxy_subG_goodExit` | = shapes | only `hQ` (input (d)) | PASS |
| 11 instances | — | as above | PASS |

## Observations (no RETURN)
- The prove report is 274 lines. The ticket asks for at most 200 and CLAUDE.md §6 for at most 300.
- The check's target-8 shape (`T2492-check.lean:309-319`) mis-elaborates `STEKDecaygL` (§1); the dispatcher may fix the check.
- `main` has moved to bbe91c0a. `git merge-tree main t/T2492` reports a textual conflict in `RBM3D.lean` only (import lines; take the union). Main changed no file that the new modules import: only the new `BA/B45BA`, `Graph/BAExp14b2` and `Graph/BAExp14b2B` were added since 4e78c3da.
