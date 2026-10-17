Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 17 08:15:23 UTC 2026

(i) no exponents; (ii) not applicable; PASS

Verdict: T2534 PASS (ticket Process line 6 of docs/tickets/T2534.md prescribes this short preflight; hub compile of docs/tickets/checks/T2534-check.lean Part 1 on main feb83715: exit 0, no error lines, per CONTROL H341 (3), H343 (2)).

## (b) Script output — Sat Oct 17 08:23 UTC 2026 (branch t/T2534, commits c0e181a2, 70759768 on main feb83715)

Amend 1 item 3: **option 1 taken** (full `d = 4` instance over a nonempty bulk). Instance = `RBM3D/Main/FinalShape.lean:118-227` (110 lines, docstring included; budget about 150). Bulk witness at `d = 4`: `FinalShape_bulk4` (`Main/FinalShape.lean:188`) gives `g₀ ∈ (0, 3/10]`, `E`, `κ = Im m₀/π > 0` with `BAbulk 4 4 g₀ κ E`, built from `BASelf_subord 4 4`, `BAzztE_data 4 4`, `BAbulk_iff_exists 4 4` (`BA/MFixedPoint.lean:215, :297, :781`; the `d = 3` twin is `exists_flowPt`, `MFixedPoint.lean:837`, whose `FlowPt` structure hard-codes `d = 3`, so it is rebuilt at `d = 4` rather than reused). The example (`:212`) returns `BAbulk 4 (sz.L n) (sz.lam n) κ E` eventually (every `n`) and `∀ n, ∃ z, BAendDom sz κ (1/10) n z` (`FinalShape_dom4`, `:200`). Sizes: `FinalShape_cls4 g₀` (`L = 4`, `W_n = (2(n+1))^5`, `lam = g₀`), `Admissible (1/8) (1/10)` proved (`:143`). Four conjuncts (decol, locSC, QUE, QDiff) of `(final_shape h32).2 4` applied; BUniv not applied (reads UN data at `d = 3`).
Deviation from the ticket text, stated: the ticket lists `baThm27L_all` "after `baThm27L_three`" and also `baThm27L_three := baThm27L_all h32 3 le_rfl`; the second needs the first earlier, so `baThm27L_three` was moved after `baThm27L_all` (same name and type). The design's `T2524_sz4` data (`L = 4(n+1)`, `lam → 0`) was not used: with `lam → 0` a fixed `κ` has no bulk witness, hence the constant-`lam` class sequence at `d = 4`.

```
$ lake build   (whole library, run at c0e181a2 and again at 70759768)
non-vacuity certificates: 0 of 100 premises in the two ledgers; ...
Build completed successfully (4426 jobs).          # exit 0; no `unregistered` line in the output
$ git diff --stat main...t/T2534
 RBM3D/BA/UNBUniv.lean      |  25 ++++---
 RBM3D/Main/FinalShape.lean | 159 ++++++++++++++++++++++++++++++++++++++-------
$ wc -l RBM3D/Main/FinalShape.lean RBM3D/BA/UNBUniv.lean   ->  231, 286
$ lake env lean <scratch copy of docs/tickets/checks/T2534-check.lean with Part 2 uncommented + #print axioms>   # exit 0
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Part 2's three `example`s (`final_shape : FinalShapeNew`, `Thm27_of_L32`, `baThm27L_all`) and Part 1 compiled in that scratch copy.

Targets (extracted from the files):
```
RBM3D/BA/UNBUniv.lean:271  theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d :=
RBM3D/BA/UNBUniv.lean:272    fun d hd => baThm27L_any d hd (baStep5III_holds_any d hd) h32
RBM3D/BA/UNBUniv.lean:276  theorem baThm27L_three : UNL32 → BAThm27L 3 :=
RBM3D/BA/UNBUniv.lean:277    fun h32 => baThm27L_all h32 3 le_rfl
RBM3D/Main/FinalShape.lean:35  def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
RBM3D/Main/FinalShape.lean:38  theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_all
RBM3D/Main/FinalShape.lean:42-44  theorem final_shape : RBM.Univ.UNL32 →
    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27 := fun h32 =>
  ⟨band_terminal h32, Thm27_of_L32 h32⟩
```
Compiled nonempty instances (same file): `d = 3`: the five-conjunct examples now read `(final_shape h32).2 3 le_rfl` (`:83`, `:97`, the two `have h` lines and the five accessors via `h2`); `d = 4`: `example (h32 : UNL32) : ∃ g0 E κ, 0 < κ ∧ Admissible (1/8) (1/10) ∧ (∀ᶠ n, BAbulk 4 ..) ∧ ∀ n, ∃ z, BAendDom ..` at `Main/FinalShape.lean:212-226`, only `UNL32` a hypothesis, bulk nonempty. Docstrings of both files now state Theorem 2.7 for every `d ≥ 3` (closing (v)); band statements untouched (diff touches only the two files).
Name-clash grep (`grep -rn "FinalShape_cls4\|FinalShape_bulk4\|FinalShape_dom4"` in RBM3D): only `Main/FinalShape.lean`; `baThm27L_all` as a Lean name occurs only in `UNBUniv.lean` (the other hits are in `docs/PAPER-VS-LEAN.md`). New helpers are `private` with the file-stem prefix. No port from RBM1D/RBM2D (no diff-stat needed).

## (c) Verified Mathlib names
`Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`, `Real.pow_rpow_inv_natCast`, `Real.rpow_le_one_of_one_le_of_nonpos`, `inv_anti₀`, `Nat.le_self_pow`, `Nat.pow_le_pow_left`, `Nat.one_le_pow`, `tendsto_atTop_mono` (all compile in `Main/FinalShape.lean`).

## (d) Open issues and paper-delta candidates
No Lean/paper statement difference added by this ticket. Observation: the BUniv conjunct of `Thm27 4` is not instantiated (UN data is `d = 3`); `FinalShape_dom4` shows only a nonempty end domain `Re z ∈ B_κ`, not a computed probability bound.
