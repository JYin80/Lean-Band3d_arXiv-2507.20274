Auditor model: claude-opus-5-5
# T2026 audit (round 1) — EK-2: `Ξ` decay, `Ξ` ball sums, same-sign row
Date (`date -u`): Sat Oct  3 04:53:10 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2026-audit1`, detached at `0ff7fcc` (`t/T2026`).

## 1. Statements against the pin (check file `docs/tickets/checks/T2026-check.lean`)
```
$ diff <(sed -n 31,63p T2026-check.lean) <(sed -n 280,312p RBM3D/Evolution/XiPins.lean)   # docstring of EKXiDecay .. end of EKSameRow
diff exit 0
$ diff <(git show c961e62:RBM3D/Probe/T2016Pins.lean | sed -n 210,447p) <(sed -n 35,272p XiPins.lean)   # copied probe lemmas
exit 0 (XiPins lines 35-272)
$ lake env lean ax2026.lean   (#check)
RBM.ekXiDecay_holds : ∀ (d : ℕ) (Λ : ℝ), RBM.EKXiDecay d Λ
RBM.ekXiBall_holds : ∀ (d : ℕ) (Λ : ℝ), RBM.EKXiBall d Λ
RBM.ekSameRow_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.EKSameRow d Λ κ
```
The three `def`s equal the check file text (namespace `RBM.T2026Check` → `RBM`); theorem types are exactly the ticket's.
Pin content (read, not re-derived): constants `C, c` precede `L, g, μ, s, t, a, b`; `g ∈ (0, Λ]`; `‖μ‖ = 1` general;
`0 ≤ s ≤ t < 1`, `g²/L² ≤ 1 − t` (paper `lem:sum_decay` range `t ≤ 1 − g²/L²`, T2016 report N5); exponent `d − 2`,
factor `(1 − s)(g² + |1 − t|)⁻¹`, decay `e^{−c|a−b|/ℓ_t}` — matches `(eq:decayXi)` (`A_deterministic_estimates.tex:115`).
`EKXiBall`: any `D` within `R ∈ [1, Λ'ℓ_s]` of `ctr`, bound `C Λ'² (g²+|1−s|)/(g²+|1−t|)` (paper line 166, without the `W^{4ε}`).
`EKSameRow`: `‖(1 − sμS)Θ_{tμ}‖_{∞→∞} ≤ C`, `μ = m(σ)²`, `κ ≤ Im m`, both `σ`; `uKer` = `(1 − (s μ)•SB) * Theta (t μ)` (`Kernel/Evolution.lean:56`).

Signatures the proofs consume (`RBM3D/Propagator/Pins.lean`):
```
35:def Prop5Decay (d : ℕ) (Λ : ℝ) : Prop :=
36-  3 ≤ d → 0 < Λ →
37-    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
38-      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
39-        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
41-          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
42-            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)
RBM3D/Propagator/Prop5Short.lean:400:theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
```
`ekXiDecay_holds` instantiates `Prop5Decay` at `m` with `m * m = μ` (`xp_exists_sqrt`, `m = exp(log μ / 2)`), `σ₁ = σ₂ = true`
(`PropSpin m true = m`), feeding the probe lemma's `hbd` verbatim; `ekXiBall_holds` applies the probe ball lemma to
`ekXiDecay_holds`'s output with `C = 4 C₀ ballC k`; `ekSameRow_holds` uses `prop5Short_holds` (proved) and `‖Ξ‖ ≤ ‖S‖‖Θ‖`.
All constants are chosen before `L, g, μ, s, t` (read in the proof terms at XiPins.lean:328-427).

## 2. Vacuity, hidden hypotheses, cycles
- No structures; no hypothesis in a field. `Prop5Decay` is the antecedent inside `EKXiDecay`/`EKXiBall` (DECISIONS §16
  form); the theorems take no unproved `Prop` argument. `EKSameRow` has no external antecedent (uses `prop5Short_holds`).
- Dependencies are merged modules on `main` (`Evolution.Pins`, `Kernel.SumDecay`, `Kernel.Evolution`, `Propagator.Prop5Short`);
  the branch adds one file; no cycle.
- External antecedent `Prop5Decay` (TEAM §8 lesson 14): prove report (a) block `== (3)` scans `L ≤ 25`, `t → 1 − 10⁻⁶`, four `μ`:
  ratio `≤ 2.0` with `c = .25` (zero mode is the second term of `B`), so the antecedent is satisfiable, not vacuous.
- Hypotheses of the pins are jointly satisfiable at the instance data below (`g²/L² = 1/100 ≤ 1/10 = 1 − t`).

## 3. Compiled nonempty instances (XiPins.lean, `section Instances`, built in §4)
```
$ grep -c "^example" RBM3D/Evolution/XiPins.lean
3
```
- `ekXiDecay_holds 3 1 h5 …` at `L = 5, g = 1/2, μ = 1, s = 1/2, t = 9/10`, all `a b : Zd 3 5`; every deterministic
  hypothesis by `norm_num`/`simp`; only `h5 : Prop5Decay 3 1` (PT-F1 in flight) left as a hypothesis.
- `ekXiBall_holds 3 1 h5 …` at the same data, `Λ' = 1, R = 1 ≤ ℓ_s` (`one_le_ellT`), `a = ctr = 0`,
  `D = xpBall` = `{b | zdistD 3 5 (0 − b) ≤ 1}` (7 points; nonemptiness `0 ∈ xpBall` is proved in the example's conclusion).
- `ekSameRow_holds 3 1 (1/2) …` at `L = 5, g = 1/2, m = I` (`Im m = 1 ≥ 1/2`), both `σ`, `s = 1/2, t = 9/10`; no hypothesis.
Nondegenerate: `N = 125`, nonempty ball, open window `0 ≤ s < t < 1`, no `False` premise, no astronomically large witness.

## 4. Build, axioms, hygiene
```
$ lake build RBM3D.Evolution.XiPins 2>&1 | grep -E "error|warning|sorry|Build completed"
Build completed successfully (2545 jobs).
exit 0
$ lake env lean ax2026.lean   (#print axioms)
'RBM.ekXiDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekXiBall_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekSameRow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_norm_XiKer_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_sum_ball_norm_XiKer_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Evolution/XiPins.lean
exit 1
$ git diff --name-status main...t/T2026
A	RBM3D/Evolution/XiPins.lean
$ grep -n "^import" RBM3D/Evolution/XiPins.lean
6:import RBM3D.Evolution.Pins
7:import RBM3D.Kernel.SumDecay
8:import RBM3D.Kernel.Evolution
9:import RBM3D.Propagator.Prop5Short
$ for n in <8 public names>; grep -rnw $n RBM3D RBM3D.lean | grep -v Evolution/XiPins.lean | wc -l
ek_norm_XiKer_apply_le 0 | ek_sum_ball_norm_XiKer_le 0 | EKXiDecay 0 | EKXiBall 0 | EKSameRow 0
ekXiDecay_holds 0 | ekXiBall_holds 0 | ekSameRow_holds 0
```
Only the sole writable file is touched (new); no frozen signature changed; imports as the ticket allows (not `RBM3D`).

## 5. Paper deltas
- Uniformity in `g ∈ (0, Λ]` and the `ℓ¹` distance: T2016f (signed, DECISIONS §18), cited by the prove report (d); not re-proposed, as the ticket asks.
- `g²/L² ≤ 1 − t` in `EKXiDecay`/`EKXiBall`: the paper's range for `lem:sum_decay` (T2016 report N5); no delta.
- `EKXiDecay` for general unit `μ` (paper: `μ = M^{(σ,σ')}`): stronger, contains the paper's case; ball sum without `W^{4ε}`: stronger.

## Observations (no statement, instance, build, axiom or delta-coverage effect)
- O1. `EKSameRow` is the pinned consumed form `‖1 + Ξ‖_{∞→∞} ≲ 1` (`A_deterministic_estimates.tex:227`), weaker than the first half
  of `(eq:samecolor)` (`‖Ξ‖ ≲ t − s`) and without its `Proj_{e⊥}` half. This is the dispatcher's pin (diff exit 0), not a prover
  choice; the dispatcher may want a T2016-series note if a later ticket needs the `t − s` factor or the projected bound.
- O2. The `EKSameRow` instance is at `m = I` (`μ = −1`), not `μ = 1` as the ticket's instance line says: `μ = 1` needs `m = ±1`,
  which violates `κ ≤ Im m` with `κ = 1/2`; the chosen data is the natural nondegenerate one.
- O3. The public unpinned names `ek_norm_XiKer_apply_le`, `ek_sum_ball_norm_XiKer_le` are not file-stem prefixed (§3 (E)); they are
  required verbatim by the ticket's probe-text diff criterion and clash with nothing.
- O4. `ekXiDecay_holds` uses the `m * m = μ` route instead of the ticket's property-4 route; both are allowed by `Prop5Decay`'s
  quantifiers (all unit `m`, all `σ₁, σ₂`).

## Verdicts
| target | statement | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|
| `ekXiDecay_holds` | = pin | yes (h5 only) | ok | T2016f | PASS |
| `ekXiBall_holds` | = pin | yes (h5 only) | ok | T2016f | PASS |
| `ekSameRow_holds` | = pin | yes (none) | ok | T2016f; O1 | PASS |

Ticket T2026: PASS. No dispatcher sign-off needed.
