Auditor model: claude-opus-5-5

# T2059 audit (round 1) — S3-05 `Induction/QopNorm`, `lem_+Q` — Sat Oct  3 15:11:27 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2059-audit1`, detached at `t/T2059` = `386d02a`.

## 0. Scope, hygiene, frozen files
```
$ git diff --name-only main...t/T2059
RBM3D/Induction/QopNorm.lean
$ git diff main...t/T2059 | grep -nE "sorry|admit|native_decide|^\+axiom|^\+\s*axiom" ; echo "grep rc=$?"
grep rc=1
$ git diff main...t/T2059 -- RBM3D/Induction/Step34Pins.lean RBM3D/Induction/QopAlgebra.lean RBM3D/Evolution/Pins.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -n "^theorem\|^def\|^structure\|^class\|^instance\|^axiom" RBM3D/Induction/QopNorm.lean
261:theorem stQopNorm_holds (d : ℕ) : STQopNorm d := by
378:theorem stQop_sub_fastDecay (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
```
All other declarations (`qn_*`, `qnA*`) are `private`. No new `def`/`structure`: no hypothesis can hide in a structure field. Imports: `RBM3D.Induction.QopAlgebra`, `RBM3D.Evolution.Pins` only (no root import, no cycle).

## 1. Build and axioms
```
$ lake build RBM3D.Induction.QopNorm 2>&1 | grep -E "error|warning|Build"   (QopNorm lines only shown)
warning: RBM3D/Induction/QopNorm.lean:16:100: This line exceeds the 100 character limit, please shorten it!
  ... (same linter warning at :17, :18, :20, :21, :22; module docstring before `set_option linter.style.longLine false`)
Build completed successfully (3705 jobs).
exit=0
$ lake env lean scratchpad/T2059/audit.lean     (import RBM3D.Induction.QopNorm)
stQopNorm_holds : ∀ (d : ℕ), STQopNorm d
'RBM.Gauss.Sizes.stQopNorm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stQop_sub_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
QopAlgebra_mollifier_props : ∀ (d L m : ℕ) [inst : NeZero L],
  3 ≤ L →
    ∀ {g : ℝ}, 0 < g → STMollifierProps g ((1 + 40 * ↑(d * m)) * 6 ^ (d * m)) (1 / 2) (QopAlgebra_mollifier d L m g)
ellT : ℕ → ℝ → ℝ → ℝ
exit=0
```
The same file also elaborates `example : (∀ d, STQopNorm d) := stQopNorm_holds` (exit 0 above).

## 2. Target 1 `stQopNorm_holds (d : ℕ) : STQopNorm d`

**Statement.** Its type is the merged pin, elaborated as `∀ d, STQopNorm d` by `#check` above; the pin
(`Step34Pins.lean:528`, unchanged on the branch) reads
```
def STQopNorm (d : ℕ) : Prop :=
  3 ≤ d → ∀ (m : ℕ) (Λ K C c : ℝ), 0 < Λ → 0 < K → 0 < C → 0 < c →
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K →
      ... ∀ ϑ, STMollifierProps (d := d) g C c ϑ → ∀ t, 0 ≤ t → t < 1 → ∀ 𝒜, EKFastDecay g t W ε D 𝒜 →
        ‖STQop (d := d) ϑ t 𝒜‖ ≤ W ^ (Cn * ε) * ‖𝒜‖ + W ^ (-D + Cn)
```
Against `(normQA)` (`3_5:1285`): `C_n` is chosen before `L, g, W, ε, D, t, 𝒜` (independent of `ε, D`, as the paper says). Extra
hypotheses `4 ≤ W^ε`, `L^d ≤ W^K` are D50 (`T2041c`). Proved `C_n = C + (2d+K)m` (report (a)(i)).

**Vacuity / hidden hypotheses / cycle.** `STMollifierProps` and `EKFastDecay` are the merged `Prop` defs (no structure);
the mollifier is not an external input (discharged by merged `QopAlgebra_mollifier_props`). No external hypothesis.

**Compiled instance** (`QopNorm.lean:499`, compiled in the build above): `stQopNorm_holds 3` at `m = 1, Λ = 1, K = 2`,
`C = (1+40·3)·6^3`, `c = 1/2` (the T2055 constants, matching `QopAlgebra_mollifier_props` above), `L = 5, g = 1, t = 1/2`,
`W = 16, ε = 1/2, D = 4`, `𝒜 = qnA = 1_{b 0 = b 1}` with `qnA ≠ 0` proved. Every hypothesis discharged by `norm_num`/
merged theorems; `EKFastDecay` of `qnA` proved (`qnA_fastDecay`). Nondegeneracy of the decay hypothesis checked:
```
$ python3 scratchpad/T2059/inst.py
ell_{1/2}=1.4142 diam=6
inst1: W^eps*ell=5.6569  #{x: zdistD(x)>=window}=8 of 125 (EKFastDecay hyp non-vacuous)
inst2: W>=16, eps'=1: window>=22.6274 > diam=6 -> far set empty
K/d=0.6667 < eps'=1
```
(`ellT L g t = min (max (g/√|1-t|) 1) L`, `Defs/Params.lean:32`; `zdistD = Σ_i zdist`, `Defs/Lattice.lean:71`.) At instance 1 the
far set is nonempty (8 of 125 differences), `qnA ≠ 0`, `4 ≤ 16^{1/2}` with equality and `125 ≤ 256`: nondegenerate.

**Paper deltas.** D50 (`T2041c`) covers `4 ≤ W^ε`, `L^d ≤ W^K`; D49 (`T2041b`) covers the abstract mollifier (`STMollifierProps`):
```
$ grep -n "D50\|D49" docs/paper-deltas.md
350:- **D49（T2041b）**：`rmk:choosechi` 的 mollifier 按性质钉（`STMollifierProps`：...
351:- **D50（T2041c）**：`lem_+Q` 带 `4 ≤ W^ε` 与 `L^d ≤ W^K`（...）。
```
**Verdict target 1: PASS.**

## 3. Target 2 `stQop_sub_fastDecay`
```
theorem stQop_sub_fastDecay (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' (A - STQop (d := d) ϑ t A) := by
```
**Statement vs ticket / paper (`3_5:1287-1288`).** Paper: if `‖𝒜‖_∞ ≤ W^C` then `(𝒫𝒜)_{a_1}ϑ_{t,a}` is `(t,ε',D')`-decaying
for any `ε', D' > 0`. Lean: `A - STQop ϑ t A` is definitionally `(𝒫A)_{a 0} ϑ t a` (`STQop`, `Step34Pins.lean:92`); `W₀` is
chosen after `(d, m, K, C, c, C₀, ε', D')` and before `L, g, W, ϑ, t, A`, i.e. uniform in all of them, as the ticket asks.
Differences from the ticket text:
- `Λ`, `g ≤ Λ` absent: stronger (uniform in all `g > 0`).
- `0 < D'`, `0 < C₀` dropped: stronger.
- `K` and `L^d ≤ W^K` added. Permitted by the ticket ("if your form needs more (e.g. `L^d ≤ W^K`), say so and propose
  `T2059a`"). Needed: the only control of `(𝒫A)_{a_1}` from `‖A‖ ≤ W^{C₀}` is `L^{dm} W^{C₀}`, and with `t → 1`
  (`ℓ_t = L`) the factor `e^{-cW^{ε'}/2}` does not beat an unbounded `L^{dm}`. Proposed as `T2059a` (report (d)).
- `W₀` is existential (via Mathlib `isLittleO_rpow_exp_atTop`), not a formula. The ticket asks to "state the threshold:
  `∃ W₀` depending on ..."; the statement does that.
This is the general decay clause (no special case): `A` arbitrary with the sup bound, any mollifier with constants `C, c`.

**Vacuity.** The hypotheses are jointly satisfiable for every `L` (take `W ≥ max(W₀, L^{d/K})`). The conclusion has
content whenever `ε' < K/d` (then `W^{ε'}ℓ_t ≤ diam` is possible with `L^d ≤ W^K`). No hidden hypothesis, no external input.

**Compiled instance** (`QopNorm.lean:517`, compiled): applied at `d = 3, m = 1, K = 2`, the T2055 constants, `C₀ = 0`,
`ε' = D' = 1`, `L = 5, g = 1, t = 1/2`, `A = qnA ≠ 0`, `W = max W₀ 16`; discharged: `5^3 ≤ W^2` (from `16 ≤ W`),
`STMollifierProps` (merged theorem), `‖qnA‖ ≤ W^0`. All hypotheses are nondegenerate. `W` is not a numeral because
`W₀` is existential by the ticket's own form.

**Paper deltas.** `T2059a` (proposed, report (d)) covers `K`, `L^d ≤ W^K` and the quantifier order; D49 covers the
abstract mollifier. Coverage complete.

**Verdict target 2: PASS.**

## 4. Observations (no RETURN)
- O1. Instance 2 has a vacuous conclusion: with the data the ticket prescribes (`L = 5`, `ε' = 1`, `K = 2`), the window is
  `W^{ε'}ℓ_{1/2} ≥ 22.6 > diam = 6` (script above), so `EKFastDecay` holds trivially. The hypotheses (the subject of the
  instance rule) are all nondegenerate and discharged. The prover disclosed this. A future ticket may want an instance with
  `ε' < K/d` and `L` large enough that `diam ≥ W^{ε'}ℓ_t`. This would need an explicit `W₀`.
- O2. The report says "No RBM1D/RBM2D text was copied or read", but the ticket lists RBM2D `QopBounds.lean` as required
  reading. This changes no statement, instance or build.
- O3. Long-line linter warnings at `QopNorm.lean:16-22` (module docstring before the `set_option`). Cosmetic.
- O4. Registry: `RBM.Gauss.Sizes.STQopNorm` is still at `RBM3D/Test/Axioms.lean:128` (registered owed). `Axioms.lean` is
  untouched, as allowed. The report says the line can go (cleanup ticket).

## Verdict
| Target | Verdict |
|---|---|
| `stQopNorm_holds` | PASS |
| `stQop_sub_fastDecay` | PASS |

Ticket T2059: **PASS**. No dispatcher sign-off needed. Paper-delta candidate `T2059a` goes to the dispatcher for numbering.
