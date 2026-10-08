Auditor model: claude-opus-5-5

# T2341 audit (round 1) — Thu Oct  8 19:36:38 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2341-audit1`, detached at `t/T2341` = `9a65c58`; merge base `2fa1442`, `main` = `1546ef7`.
Scratch: `$S = <scratchpad>/T2341/audit` (`eq.lean`, `reg.lean`).

## 1. Files touched, frozen signatures

```
$ git diff --name-only main...t/T2341
RBM3D/BA/Prop5.lean
RBM3D/BA/PropUnit.lean
$ diff <(git show main:RBM3D/BA/Prop5.lean | sed -E 's/^private //') <(sed -E 's/^private //' RBM3D/BA/Prop5.lean) | wc -l
       0
$ git diff main...HEAD -- RBM3D/BA/Prop5.lean | grep -cE '^-private'
8
$ git diff --stat 2fa1442 main -- RBM3D/BA/ RBM3D/Propagator/ | tail -3
(empty: no drift of main in BA/ or Propagator/ since the branch base)
```
The 8 removed `private` keywords are exactly the ticket's list (`baP5Gam`, `baP5Eps`, `baP5_gam_pos`, `baP5_eps_pos`, `baP5_Theta_mixed`, `baP5_Theta_zero`, `baP5_theta_eq`, `baP5_convA`; `git diff` lines in the prove report (b), re-read here). No signature changed.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.PropUnit 2>&1 | grep -E "error|warning|Build completed"
(warnings only in upstream merged files: Defs/Tail, LaplaceGauss, HeatProduct, Propagator/PropUnit, Step34Pins, Walk, Stop, Step2Defs, Ward, KHeatDiff; none in BA/PropUnit.lean or BA/Prop5.lean)
Build completed successfully (3746 jobs).
exit 0
$ grep -nE 'sorry|admit|native_decide|^axiom| axiom ' RBM3D/BA/PropUnit.lean | wc -l
       0
```
`$S/eq.lean` = check-file imports + `import RBM3D.BA.PropUnit` + sections 2–3 of the check file + the four equality examples + `#print axioms`:
```
example : @RBM.BA.T2341Check.T2341_BAPropUnit1mixed = @RBM.BA.BAPropUnit1mixed := rfl
example : @RBM.BA.T2341Check.T2341_BAPropUnit2mixed = @RBM.BA.BAPropUnit2mixed := rfl
example : RBM.BA.T2341Check.T2341_baPropUnit1mixed_holds := RBM.BA.baPropUnit1mixed_holds
example : RBM.BA.T2341Check.T2341_baPropUnit2mixed_holds := RBM.BA.baPropUnit2mixed_holds
$ lake env lean $S/eq.lean
'RBM.BA.baPropUnit1mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropUnit2mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropUnit_laplace_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit1_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit2_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit1_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_unit2_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.PropUnitInst.inst_laplace_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.MFixedPointInst.P' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
Registry pre-check:
```
$ printf 'import RBM3D\nimport RBM3D.BA.PropUnit\n#assert_rbm_axioms\n' > $S/reg.lean; lake env lean $S/reg.lean
axiom audit: 10330 theorems, 3048 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit 0
```

## 3. Statements against the pins

Both pins are definitionally equal to the check file's section 2 (`rfl` above). Text diff as well:
```
$ diff <(check-file pins, `T2341_` stripped) <(sed -n '59,82p' RBM3D/BA/PropUnit.lean)   # comment/blank lines filtered
pin diff exit 0
$ grep -n '^theorem baPropUnit[12]mixed_holds' RBM3D/BA/PropUnit.lean
886:theorem baPropUnit1mixed_holds (d : ℕ) (Λ κ : ℝ) : BAPropUnit1mixed d Λ κ := by
942:theorem baPropUnit2mixed_holds (d : ℕ) (Λ κ : ℝ) : BAPropUnit2mixed d Λ κ := by
```
Against the mathematics: fixed `d, Λ, κ` before `∃ C` before `∀ L g E m t σ a j`; `C` depends on `(d,Λ,κ)` only; window `0 ≤ t < 1` (including `t = 0`); decay `(|a|+1)^{-(d-1)}` (first) and `^{-d}` (second, both `i = j` and `i ≠ j`); loss `(g² + |1-t|)⁻¹` — the band `PropUnit1/2` shape with the ticket's substitutions. Restriction `σ₁ ≠ σ₂` is the pinned special case (the ticket's target, not the general `BAProp6/7`; `σ₁ = σ₂` is P8), recorded as T2341c.

New public lemma (ticket: "name and exact statement reported"):
```
theorem baPropUnit_laplace_head (d n : ℕ) (hd : 3 ≤ d) (hn1 : 1 ≤ n) (hn2 : n ≤ 2) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g t A : ℝ), 0 < g → g ≤ Λ → 0 < t → t < 1 → 0 ≤ A →
      IntegrableOn (fun τ => exp(-(baP5Eps g t) τ) * (min 1 (τ^(-(d+n)/2)) * (1 + A²/max τ 1)^(-(d/2+1)))) (Ioi 0) ∧
      (baP5Gam g t)⁻¹ * ∫ τ in Ioi 0, (same) ≤ C * ((g² + (1-t))⁻¹ * ((A+1)^(d+n-2))⁻¹)
```
(abridged from `RBM3D/BA/PropUnit.lean:485-492`). Versus ticket step (2): integral over `(0,∞)` instead of `(0,L²]` (stronger, integrand `≥ 0`, no `L`); `M = d/2+1` (ℕ division = `⌊d/2⌋+1`), exponent `d+n-2`, prefactor `(g²+1-t)⁻¹`: as pinned. `0 < t` is needed for `γ = t g² > 0`; `t = 0` is handled separately in the targets. Recorded as T2341b.

## 4. Hidden hypotheses, vacuity, cycles

```
$ grep -nE '^(private )?(noncomputable )?(theorem|lemma|def) ' RBM3D/BA/PropUnit.lean | grep -v private | grep -vE "baPropUnit|BAPropUnit|inst_"
(empty: every unpinned helper is private; `grep -c private` = 38)
```
- No `structure`/`class` in the new file; pins are `Prop` definitions whose hypotheses are all explicit (`3 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ L`, `0 < g ≤ Λ`, `BAReal`, `0 ≤ t < 1`, `σ₁ ≠ σ₂`).
- No external hypothesis: inputs `kBA_diff1_le`, `kBA_diff2_le`, `kBA_gap`, `BATheta_eq_laplace_kBA`, `baP5_*` are merged theorems (check file section 1 elaborates them on `main`); no limit check needed.
- No cycle: imports are `RBM3D.BA.KHeatDiff`, `RBM3D.BA.Prop5` only (ticket's `RBM3D.Propagator.PropUnit` dropped as transitive, as the ticket allows; prove report (b) shows `RBM.propUnit1_holds` visible). Never `import RBM3D`.
- `MFixedPointInst.P` (instance data) is `def P : FlowPt 4 10 := (exists_flowPt 4 (g := 10) (by norm_num)).some` (`BA/MFixedPoint.lean:893`), a proved existence; its fields `g0_pos`, `g0_le`, `real` are proved data, not assumptions.

## 5. Compiled nonempty instances

`RBM.BA.PropUnitInst` (`PropUnit.lean:1020-1117`), all compiled (build + axioms above). Each applies the target at `d = 3`, `Λ = 10`, `κ = Im P.m0` (`P.real.1.1`), `L = 4`, `g = P.g0` (`P.g0_pos`, `P.g0_le`), `E = P.E`, `m = P.m0`, `BAReal` by `P.real`, `σ₁ ≠ σ₂` by `decide`; no hypotheses left open:

| instance | target | t | σ | a | dirs | extras proved |
|---|---|---|---|---|---|---|
| `inst_unit1` | 1 | 1/2 | (true,false) | (1,0,0) | j=0 | `a ≠ 0`, `zdistD a = 1` |
| `inst_unit1_large_eps` | 1 | 1/100 | (false,true) | (2,1,0) | j=1 | `zdistD a = 3` |
| `inst_unit1_zero` | 1 | 0 | (true,false) | (1,0,0) | j=0 | |
| `inst_unit2` | 2 | 1/2 | (true,false) | (1,0,0) | i=j=0 | `a ≠ 0`, `zdistD a = 1` |
| `inst_unit2_large_eps` | 2 | 1/100 | (false,true) | (2,1,0) | (0,2) | `zdistD a = 3` |
| `inst_unit2_zero` | 2 | 0 | (true,false) | (1,0,0) | (0,2) | |
| `inst_laplace_head` | lemma | 1/2 | — | A = 1 | n=2 | g = 1 |

The ticket's required instances (`d = 3`, `L = 4`, `t = 1/2`, `a = ![1,0,0]`, `i = j = 0`) are `inst_unit1`, `inst_unit2`. Nondegenerate: `L = 4 ≥ 3`, `t ∈ (0,1)` and `t = 0`, `a ≠ 0`, both charge orders; constants existential as in the pins.

## 6. Paper deltas

Proposed in the prove report (d): T2341a (polynomial head `min(1,τ^{-(d+n)/2})(1+|a|²/max(τ,1))^{-M}` instead of the exponential factor of A:58-67, `max τ 1`), T2341b (Laplace lemma over `(0,∞)`, exponent `d+n-2` also for the supremum; the ticket's `(A+1)^{-(d+n)}` sup claim is false), T2341c (pins are the special case `σ₁ ≠ σ₂`), T2341d (eight `baP5_*` made public, no statement change). These cover every Lean/paper and Lean/ticket statement difference found in §3.

## 7. Observations (no RETURN)

- O1: ticket step (2) states the `ε`-side sup bound as `C (A+1)^{-(d+n)}`; preflight (a)(b') shows this is false at `d=3, n=2`, and the proof uses the correct `(A+1)^{-(d+n-2)}`. Affects no statement (the lemma's pinned conclusion is unchanged); covered by T2341b.
- O2: the prove report's full `lake build` predates the import drop (stated so in the report); the hub runs the full build at merge.

## Verdict

- `baPropUnit1mixed_holds`: **PASS**.
- `baPropUnit2mixed_holds`: **PASS**.
- `baPropUnit_laplace_head` (new public lemma): **PASS**.

Ticket T2341: **PASS**. No dispatcher sign-off needed.
