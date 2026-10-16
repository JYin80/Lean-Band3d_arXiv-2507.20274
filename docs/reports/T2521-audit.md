Auditor model: claude-opus-5-5

# T2521 audit (MA-06b, final shape), round 1 — Fri Oct 16 19:54:15 UTC 2026

Branch `t/T2521` at `e4cfe86f`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2521-audit1` (detached, cache cloned from main).
Scratch: `$SP/T2521/` (`$SP` = session scratchpad).

## 1. Build, diff, hygiene

```
$ lake build RBM3D.Main.FinalShape ; grep -c error ; grep FinalShape ; tail -1
exit=0
0
⚠ [4427/4427] Replayed RBM3D.Main.FinalShape
warning: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
Build completed successfully (4427 jobs).
$ git diff --name-only main...HEAD
RBM3D/Main/FinalShape.lean
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Main/FinalShape.lean ; echo match-exit=$?
match-exit=1
```
The only file touched is the sole writable file. `Endpoints.lean`, `Main/BandTerminal.lean` and `BA/*` are unchanged (frozen signatures untouched). `RBM3D/Test/Axioms.lean` is not touched; the prove report's full build with a temporary root import passed without a registry line. The hub runs the full build at merge.

## 2. Statements against the pins (script diff), stop rule, axioms

Script: extract `T2521_*` from `docs/tickets/checks/T2521-check.lean` and targets 1–3 from the file, normalise whitespace and namespace prefixes, compare.
```
Thm27 | pin: RBM.BA.BAThm27L 3
      | file: RBM.BA.BAThm27L 3
      | equal: True
Thm27_of_L32 | pin: UNL32 → Thm27
             | file: UNL32 → Thm27
             | equal: True
final_shape | pin: UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
            | file: UNL32 → (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
            | equal: True
```
Exact-type check by Lean: check file lines 1–48 with line 11's import activated, then the line 50–53 block activated, then extra exact-type `example`s and axiom prints (`$SP/T2521/Aud.lean`):
```
example : RBM.Endpoints.T2521Check.T2521_Thm27OfL32 := RBM.BA.baThm27L_three          -- check line 52
example : (RBM.Univ.UNL32 → RBM.BA.BAThm27L 3) := @RBM.BA.baThm27L_three              -- stop rule vs T2520_Thm27Three
example : RBM.Endpoints.T2521Check.T2521_Thm27 = RBM.Endpoints.Thm27 := rfl
example : RBM.Endpoints.T2521Check.T2521_Thm27OfL32 := RBM.Endpoints.Thm27_of_L32
example : RBM.Endpoints.T2521Check.T2521_FinalShape := RBM.Endpoints.final_shape
example : RBM.Endpoints.T2521Check.T2521_FinalShape = (RBM.Univ.UNL32 → (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧
  RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧ RBM.Endpoints.Thm27) := rfl
$ lake env lean $SP/T2521/Aud.lean ; echo exit=$?
RBM.Endpoints.band_terminal : RBM.Univ.UNL32 →
  RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff
RBM.Endpoints.decol : Prop
RBM.Endpoints.locSC : Prop
RBM.Endpoints.QUE : Prop
RBM.Endpoints.QDiff : Prop
RBM.Endpoints.BUniv : Prop
RBM.Univ.UNL32 : Prop
RBM.BA.BAThm27L : ℕ → Prop
RBM.BA.baThm27L_three : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -n T2520_Thm27Three docs/tickets/checks/T2520-pins.lean
223:def T2520_Thm27Three : Prop := UNL32 → BAThm27L 3
```
Stop rule: `baThm27L_three` on `main` has type `UNL32 → BAThm27L 3` = `T2520_Thm27Three` (exact type, it elaborates). Decision (4) fallback did not fire; `Thm27_of_L32` is `RBM.BA.baThm27L_three` by name.

`band_terminal` axioms on `main` (main worktree, `main` = 9d2b0883):
```
$ lake env lean $SP/T2521/Main.lean     # import RBM3D.Main.BandTerminal; #print axioms RBM.Endpoints.band_terminal
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Unchanged against the branch output above.

## 3. No hidden hypothesis, no vacuity, no cycle (closing condition (vi))

```
$ lake env lean $SP/T2521/Sig.lean  | tee sig.out    # #check @final_shape, @Thm27_of_L32, #print Thm27
RBM.Endpoints.final_shape : RBM.Univ.UNL32 →
  (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
    RBM.Endpoints.Thm27
RBM.Endpoints.Thm27_of_L32 : RBM.Univ.UNL32 → RBM.Endpoints.Thm27
def RBM.Endpoints.Thm27 : Prop :=
RBM.BA.BAThm27L 3
grep -c 'STStep5IIIgL\|UNMLOutBA\|UNLocAvgBA\|UNQueBA' sig.out = 0
$ grep -n "^def BAEnd_\|^def BAThm27L" RBM3D/BA/MAPins.lean ; grep -rn "def BAEnd_QUEL\|def BAEnd_BUnivL" RBM3D
97:def BAEnd_locSCL   107:def BAEnd_QDiffL   121:def BAEnd_decolL   126:def BAThm27L
RBM3D/BA/UNPins.lean:333:def BAEnd_QUEL (d : ℕ) : Prop :=
RBM3D/BA/UNPins.lean:343:def BAEnd_BUnivL (d : ℕ) : Prop :=
$ (bodies of the five BAEnd_*L + BAThm27L) | grep -c 'STStep5IIIgL\|UNMLOutBA\|UNLocAvgBA\|UNQueBA'
0        # MAPins:97-127 (awk extract) and UNPins:333-346
```
- `Thm27` is a `def` (not a structure); its unfolding `BAThm27L 3` is the conjunction of five `Prop` pins whose only premises are the paper's (`3 ≤ d`, `Admissible 𝔠 𝔡`, positivity of `κ, ε, τ, D`, QUE ranges `ε₀ < 𝔡/2`, `c < ε₀`, `c < 𝔡/5`, bulk `E`, `|E'| < 2`, `k ≥ 1`, test function). No hidden field.
- `final_shape` has `UNL32` as its only premise; the two dependencies are merged (`band_terminal`, `Main/BandTerminal:104`; `baThm27L_three`, `BA/UNBUniv`, merged in 9d2b0883). No cycle: `FinalShape` imports them, nothing imports `FinalShape`.
- External hypothesis `UNL32`: not new in this ticket; registered (`RBM3D/Test/Axioms.lean:93`, "LSY Thm 2.2 (arXiv:1609.09011), the one external input of bulk universality (DECISIONS §5; T2174, UN-01)"); it was already the sole premise of the merged `band_terminal`. No new limit check is required by this ticket.

## 4. Compiled nonempty instances (target 4)

All in `RBM3D/Main/FinalShape.lean`, compiled in the build of §1; `h32 : UNL32` is the only hypothesis of every `example`.
- Lines 59–76: each band conjunct of `(final_shape h32).1` fed to `Inst.inst_decol/locSC/QUE/BUniv/QDiff` (merged, `Endpoints.lean:561-600`), which apply the conjunct at `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `Defs/Sizes:260`), `(𝔠,𝔡) = (1/6,1/10)`, `sz0_admissible`, with all positivity side goals by `norm_num`, e.g.
  `h 3 le_rfl (1/6) (1/10) sz0 sz0_admissible (1/10) (1/10) 1 (by norm_num) (by norm_num) (by norm_num)`.
- Lines 84–95: the five BA conjuncts of `(final_shape h32).2` at `S0`, `S0_adm`, `κ_* = clsκ 4 _` (`clsκ_pos`), `E_* = (fp 4 _).E` (`S0_bulk`), `E' = 0`, `k = 1`, `UNInst.bump`/`bump_testFun`; argument lists are token-identical to `BA/MAPins:213-224` (compared by reading; only the private name `MAPins_hg` → `FinalShape_hg : (0:ℝ) < 3/10`).
- Lines 98–114: the whole `final_shape h32`, all ten conjuncts at once at the same data.
Nondegenerate: `N = (W L)^3 ≥ 2.1e6` at `n = 0` for both sequences (preflight script (a)(ii)); no `N = 0`, empty index, collapsed window or `False` premise; every deterministic hypothesis is discharged. PASS.

## 5. Paper deltas

Paper `1_2:644` (`\label{MR:decol_BA}`): "Fix any dimension $d\ge 3$ …". Lean: `BAThm27L 3`. This `d = 3` restriction is covered by the existing entry:
```
$ grep -n "D723" docs/paper-deltas.md | head -1
1803:- **D723**（Jun 决定 B，2026-10-14）：论文 Thm 2.7（`MR:decol_BA`，`1_2:644-645`）对所有 `d ≥ 3` … Lean 的 BA 终端只在 **`d = 3`** 证明 …
```
`UNL32` is the authorized borrowed input (DECISIONS §5). The band half is the merged `band_terminal` (its own deltas were covered at its merge). `final_shape` is only the conjunction of the two halves, so it adds no new Lean/paper difference; the absence of a `T2521a` candidate is correct.

## 6. Verdicts

| Target | Statement | Hidden/vacuity/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| 1 `Thm27` | = `T2521_Thm27` (rfl) | none | via lines 84–114 | ok / n/a (def) | D723 | PASS |
| 2 `Thm27_of_L32` | = `T2521_Thm27OfL32`; `baThm27L_three` by name, exact type of `T2520_Thm27Three` | `UNL32` only | lines 84–114 | ok / std three | D723 | PASS |
| 3 `final_shape` | = `T2521_FinalShape` (rfl); grep (vi) = 0 | `UNL32` only | lines 59–114 | ok / std three | none new | PASS |
| 4 instances | — | — | compiled, nondegenerate | ok | — | PASS |
| 5 pastes | axioms of `final_shape`, grep (vi), `band_terminal` vs main: reproduced above | — | — | ok | — | PASS |

Observations (no RETURN):
- O1: style-linter warning `FinalShape.lean:10:0` (`set_option` before the module docstring); it does not affect build, statements or axioms.
- O2: in the prove report, the closing-(vi) grep ran over `#check` output, where `Thm27` is folded. This audit also ran the grep over the unfolded `BAEnd_*L`/`BAThm27L` bodies and got 0.

Overall: **PASS**. No dispatcher sign-off needed.
