Auditor model: claude-opus-5-5

# T2534 audit (round 1): BA-D row R2, the assembly — Sat Oct 17 08:26:09 UTC 2026

Branch `t/T2534` at `70759768` (on main `feb83715`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2534-audit1` (detached).
Inputs: `docs/tickets/T2534.md`, `docs/tickets/T2534-amend-1.md`, `docs/tickets/checks/T2534-check.lean`, `docs/reports/T2534-prove.md`.

## 1. Statements against the ticket pin (script diff)

```
$ sed -n '/^```lean/,/^```/p' docs/tickets/T2534.md | grep -E "^(theorem|def|  fun)" > pin.txt   # Lean side extracted by grep from the two files
$ diff pin.txt lean.txt && echo "PIN DIFF: identical"
PIN DIFF: identical
theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d :=
  fun d hd => baThm27L_any d hd (baStep5III_holds_any d hd) h32
def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27 := RBM.BA.baThm27L_all
theorem final_shape : RBM.Univ.UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
```
`final_shape` text: unchanged in `git diff main...t/T2534` (only its docstring line changed). Closing (iii): `baThm27L_three : UNL32 → BAThm27L 3 := fun h32 => baThm27L_all h32 3 le_rfl` (`BA/UNBUniv.lean:276-277`), same name and type (Part 1 of the check below elaborates it at exact type). It was moved after `baThm27L_all` (needed for the forward reference; stated in the prove report).

Check file with Part 2 uncommented (scratch copy, `sed 's|^-- example|example|'`, plus `#print axioms`), in the audit worktree after the full build:
```
$ lake env lean T2534/check2.lean; echo "exit $?"
baThm27L_any : ∀ (d : ℕ),
  3 ≤ d →
    (STStep5IIIgL d (fun sz => (sz.withLam 0).seqP) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
        fun sz z => BAflowT0 sz z) →
      Univ.UNL32 → BAThm27L d
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Part 1 (`baStep5III_holds_any` at exact type, `baThm27L_three : UNL32 → BAThm27L 3`) and Part 2 (`final_shape : FinalShapeNew`, `Thm27_of_L32 : UNL32 → Thm27New`, `baThm27L_all : UNL32 → ∀ d, 3 ≤ d → BAThm27L d`) all elaborate.

Quantifier order and scope: `Thm27` is `∀ d, 3 ≤ d → BAThm27L d`, matching `MR:decol_BA` (`1_2:644-645`, all `d ≥ 3`); each `BAEnd_*L d` keeps fixed parameters (`𝔠 𝔡 sz`, `κ ε τ D`) before `∀ᶠ n` (`BA/MAPins.lean:96-124`, merged, unchanged).

## 2. Hidden hypotheses, vacuity, cycles

- No structure field carries a hypothesis: `Thm27` is a `def` of a `Prop`; the only external hypothesis is `UNL32` (borrowed, LSY Thm 2.2; registered as borrowed, DECISIONS (2(b)) line 347 and the premise scan "borrowed 1"). Not new in this ticket; its limit check predates T2534.
- Dependencies are merged on `main`:
```
$ grep -n "theorem baStep5III_holds_any" -A2 RBM3D/BA/Step5IIITargets.lean
58:theorem baStep5III_holds_any (d : ℕ) (hd : 3 ≤ d) :
59:    STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
$ git log --oneline -1 main -- RBM3D/BA/Step5IIITargets.lean
feb83715 T2533: merge BA-D row R1 (BA case (iii) of Step 5 at every d >= 3, baStep5III_holds_any)
```
  `baThm27L_any` is merged on main (`BA/UNBUniv.lean:263`, unchanged by the diff). No cycle: `baThm27L_all → baThm27L_any, baStep5III_holds_any`; `baThm27L_three → baThm27L_all`; `Thm27_of_L32 → baThm27L_all`.
- Premise scan (full build, see §4): the audit throws on any unregistered premise (`RBM3D/Test/Axioms.lean:532-536`, `unless unregistered.isEmpty do throwError`); the build passed, so `unregistered: []`. No owed line for BA-D:
```
$ grep -n "STStep5IIIgL\|Step5III" T2534-full.log | grep -v "warning\|Replayed"     # (no output)
premises found by scanning: 94 (borrowed 1, owed 36, structural 57, refuted 0, superseded 0).
```

## 3. Compiled nonempty instances (`RBM3D/Main/FinalShape.lean`)

- `d = 3` (`:83`, `:97`): `have h := (final_shape h32).2 3 le_rfl`, then all five BA conjuncts at `S0`, `κ_* = clsκ 4`, `E_* = (fp 4 _).E` with `S0_bulk`; the whole `final_shape` (ten conjuncts) in the second example. Only `UNL32` is a hypothesis.
- `d = 4` (Amend 1 option 1; `:118-227`, 110 lines ≤ ~150):
```
$ grep -n "^private\|^example (h32 : UNL32) : ∃\|^end D4Instance" RBM3D/Main/FinalShape.lean
131:private def FinalShape_cls4 (g0 : ℝ) : Sizes 4 where
138:private theorem FinalShape_cls4_W4 (n : ℕ) : 4 ≤ (FinalShape_cls4 0).W n := by
143:private theorem FinalShape_cls4_adm {g0 : ℝ} (h0 : 0 < g0) (h10 : g0 ≤ 10) :
188:private theorem FinalShape_bulk4 : ∃ g0 E κ : ℝ, 0 < g0 ∧ g0 ≤ 3 / 10 ∧ 0 < κ ∧ BAbulk 4 4 g0 κ E := by
200:private theorem FinalShape_dom4 {g0 E κ ε : ℝ} (hε : ε ≤ 1) (hb : BAbulk 4 4 g0 κ E) (n : ℕ) :
212:example (h32 : UNL32) : ∃ g0 E κ : ℝ, 0 < κ ∧ (FinalShape_cls4 g0).Admissible (1 / 8) (1 / 10) ∧
227:end D4Instance
```
  The example's conclusion (`:212-214`) is Lean-checked: `0 < κ`, `Admissible (1/8) (1/10)` (proved: `N = (4W)^4 → ∞`, `W ≥ N^{1/8}` from `W ≥ 4`, `W^{-19/10} ≤ g₀ ≤ 10` eventually), `∀ᶠ n, BAbulk 4 (L n) (lam n) κ E` (the bulk the conjuncts read, `BAendDom`/`BAdecolBad`, `BA/MAPins.lean:65-66, 105`), and `∀ n, ∃ z, BAendDom sz κ (1/10) n z`. The bulk is nonempty by an actual solution of `(self_m)` at `(d, L) = (4, 4)` (`BASelf_subord 4 4`, `BAzztE_data 4 4`, `BAbulk_iff_exists 4 4`) with `κ = Im m₀/π > 0` — not the empty-bulk `κ = 1/2` instance Amend 1 forbids. Four conjuncts of `(final_shape h32).2 4 (by norm_num)` (decol, locSC, QUE, QDiff) are applied with every deterministic hypothesis discharged; BUniv not applied at `d = 4` (ticket closing (vii) excludes it; it is applied at `d = 3`). Nondegenerate: `W_n = (2(n+1))^5 → ∞`, `L = 4 ≥ 3`, `g₀ > 0`, `κ > 0`, `ε = 1/10 ∈ (0,1]`.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.BA.UNBUniv RBM3D.Main.FinalShape        # audit worktree
✔ [4419/4420] Built RBM3D.BA.UNBUniv (17s)
⚠ [4420/4420] Built RBM3D.Main.FinalShape (3.5s)
warning: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
Build completed successfully (4420 jobs).   exit 0;  grep -c error -> 0
$ lake build RBM3D                                          # whole library, runs #assert_rbm_axioms and the premise scan
non-vacuity certificates: 0 of 100 premises in the two ledgers; ...
Build completed successfully (4426 jobs).   exit 0;  grep -c error -> 0
$ git diff main...t/T2534 | grep -nE "^\+.*\b(sorry|admit|axiom|native_decide)\b" || echo none
no sorry/admit/axiom/native_decide in added lines
$ git diff --stat main...t/T2534
 RBM3D/BA/UNBUniv.lean      |  25 ++++---
 RBM3D/Main/FinalShape.lean | 159 ++++++++++++++++++++++++++++++++++++++-------
 2 files changed, 151 insertions(+), 33 deletions(-)
$ git diff --name-only main...t/T2534 -- RBM3D/Main/BandTerminal.lean RBM3D/Main/BUnivHolds.lean | wc -l
0
```
The FinalShape warning is pre-existing (`set_option` at line 10 before the module doc on `main` too). Axioms: §1 (six names, standard three). Band statements and `band_terminal`, `bUniv_holds` untouched. New helpers are `private` with the file-stem prefix (rule (E)).

## 5. Paper deltas

The Lean/paper difference closed by this ticket (Thm 2.7 at `d = 3` only, D723) is already withdrawn in `docs/paper-deltas.md:1873` (D754 ← DECISIONS §371: Thm 2.7 at every `d ≥ 3`, paper unchanged). The statements now agree with `MR:decol_BA` in scope; no new difference is introduced (the `d = 4` data are an instance, not a statement).

## Closing conditions

(ii) `Thm27`/`final_shape` at exact type: yes. (iii) `baThm27L_three` same name/type: yes. (iv) axioms of `band_terminal`, `bUniv_holds` standard: yes. (v) docstrings state every `d ≥ 3` (`FinalShape.lean:13-26, 32-41`; `UNBUniv.lean:18, 35-37, 268-270`): yes. (vi) no owed BA-D line, `unregistered: []`: yes. (vii) `d = 4` instance over a nonempty bulk (option 1): yes. Diff only the two files: yes.

## Observations (no statement, instance, build, axiom or delta effect)

1. The `d = 4` data are `L = 4`, `lam = g₀` constant, not the design's `L = 4(n+1)`, `lam = (2(n+1))^{-6}` named in closing (vii); Amend 1 option 1 requires a nonempty bulk, which a vanishing `lam` with fixed `κ` does not give; the prover states the deviation in the prove report (b).
2. `baThm27L_all` and `baThm27L_three` have no `example` inside `BA/UNBUniv.lean`; their instances are in `Main/FinalShape.lean` through `Thm27_of_L32 := RBM.BA.baThm27L_all` at `d = 3` and `d = 4`, the location the ticket prescribes. The §5 header of `UNBUniv.lean` (`:281-286`) announces instances the file does not contain (already so on `main`).
3. `baThm27L_three`'s docstring (`UNBUniv.lean:274`) and `baThm27L_any`'s (`:261`) still cite D723, now withdrawn (D754).

## Verdict

- `baThm27L_all`: PASS. `Thm27`: PASS. `Thm27_of_L32`: PASS. `final_shape`: PASS. `baThm27L_three` (closing (iii)): PASS.
- **T2534: PASS.** No dispatcher sign-off needed (the dispatcher activates Part 2 of the check at merge).
