Auditor model: claude-opus-5-5

# T2035 audit (round 1) — EK-5 `ekSumDecayNonzero_holds`

Written: Sat Oct  3 13:07:02 UTC 2026 (`date -u`). Branch `t/T2035` @ `b9a2440`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2035-audit1` (detached).

Target: `theorem ekSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNonzero d n Λ κ`.
**Verdict: PASS.**

## 1. Statement

```
$ git show t/T2035:RBM3D/Evolution/Nonzero.lean | grep -n "^theorem"
146:theorem ekSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNonzero d n Λ κ := by
$ cat ax.lean   # (also elaborates the ticket's pinned target type)
import RBM3D.Evolution.Nonzero
#print axioms RBM.ekSumDecayNonzero_holds
#print axioms RBM.ekDelta0
open RBM in
example : ∀ (d n : ℕ) (Λ κ : ℝ), EKSumDecayNonzero d n Λ κ := ekSumDecayNonzero_holds
$ lake env lean ax.lean; echo "exit $?"
'RBM.ekSumDecayNonzero_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekDelta0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ diff <(sed -n 128,137p RBM3D/Evolution/Pins.lean) <(git show t/T2035:RBM3D/Evolution/Pins.lean | sed -n 128,137p) && echo "pin unchanged on branch"
pin unchanged on branch
```

The type is exactly the ticket's target, i.e. the merged EK-1 pin (`Pins.lean:128-137`):
`Prop5Short d Λ κ → Prop8ZeroMode d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C > 0, ∀ L ≥ 3, g ∈ (0,Λ],
0 ≤ s, 1 - g²/L² ≤ s ≤ t < 1, ‖m‖ = 1, κ ≤ Im m, σ, A ⊇ I_diff(σ), 𝒜,
‖zeroModeSet d L A (UN d L g (EKsgn m σ) s t 𝒜)‖ ≤ C‖𝒜‖`. Constants after `(d, n, Λ, κ)`, before
`L, g, s, t, m, σ, A, 𝒜`; no `L^τ` loss; both charges via `EKsgn`. Matches paper
`lem:sum_decay_nonzero` (`3_5_Loop_Hierarchy.tex:1666-1671`) up to D37/D38 (§5).

## 2. Vacuity, hidden hypotheses, cycles

- No structure-field hypotheses; the file defines no new `Prop`, so no registry line is needed
  (`RBM3D/Test/Axioms.lean` untouched, see §4 diff).
- The two antecedents of the pin are discharged by merged theorems with standard axioms:
```
$ lake env lean ax2.lean   # import RBM3D.Evolution.Nonzero; #print axioms of the two
'RBM.prop5Short_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop8ZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
- Dependencies used (signatures read): `ekSameRow_holds` (`XiPins.lean:357`, merged EK-2),
  `prop8ZeroMode_holds` (`Prop5Hold.lean:1266`), `sum_radial_pow_le` (`Defs/RadialSum.lean:192`,
  `Σ_x ((|x|+1)^k)⁻¹ ≤ e^{√(k+2)}·2^{k+2}·radC 1·L²`), plus the merged `Kernel/Evolution` machinery
  (`UN_eq_tensorKer`, `zeroModeSet_tensorKer`, `norm_tensorKer_le`, `uKer_eq_one_add`,
  `projMat_mul_SB_comm`, `projMat_mul_Theta`, `norm_projMat_le`, `norm_SB`). No cycle: the new
  file is imported by nothing on main or the branch.
- Mathematics checked against the signatures: the `i ∈ A` factor is
  `projMat + (t-s)μ·SB·Θ̊_{tμ}`; `‖Θ̊‖ ≤ C₀(g²+|1-t|)⁻¹·E·L²` (pin 8 with exponent `d-2 = k`,
  then the radial sum); `(t-s)(g²+|1-t|)⁻¹L² ≤ (1-s)L²/g² ≤ 1` from `1-s ≤ g²/L²`. The `i ∉ A`
  factor has `σ i = σ(finRotate n i)` from `hA` and uses EK-2. Constant `max(Cs, 2+C₀E)^n`,
  depending on `(d, n, Λ, κ)` only (`Cs`, `C₀` come from `(d,Λ,κ)`-level existentials).

## 3. Compiled nonempty instances (same file, lines 192-226)

| | d | n | Λ | κ | L | g | s | t | m | σ | A | 𝒜 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ex. 1 | 3 | 2 | 1 | 1/2 | 5 | 1/2 | 995/1000 | 999/1000 | `I` | `![true,false]` | `univ` | `δ₀` |
| ex. 2 | 3 | 3 | 1 | 1/2 | 5 | 1/2 | 995/1000 | 999/1000 | `I` | `![true,true,false]` | `{1,2}` | `δ₀` |

- Both apply `ekSumDecayNonzero_holds` with `prop5Short_holds 3 1 (1/2)` and
  `prop8ZeroMode_holds 3 1 (1/2)` (no open hypothesis left), and discharge every deterministic
  hypothesis at the data: `1 - g²/L² = 99/100 ≤ 995/1000 ≤ 999/1000 < 1`, `‖I‖ = 1`,
  `1/2 ≤ Im I = 1`; `A ⊇ I_diff(σ)` by `mem_univ` / `decide` (ex. 2: `finRotate 3` maps 0→1→2→0,
  sign changes at `i = 1, 2`, `i = 0` same-sign, so `A = I_diff(σ)` is the minimal admissible
  set, nonempty and proper).
- Non-degeneracy: `L = 5`, `n ≥ 2`, open window, `𝒜 = δ₀` with `ekDelta0 _ 3 5 0 ≠ 0` proved in
  the example. Both compile in the module build (§4). No `False` premise, no huge witness.

## 4. Build, axioms, hygiene, scope

```
$ lake build RBM3D.Evolution.Nonzero 2>&1 | grep -E "error|warning|Build completed|✖" | tail -20
warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/HeatProduct.lean:218:0: `abs_prod_sub_prod_le` does not use the following hypothesis in its type:
Build completed successfully (3418 jobs).
$ git diff --name-only main...t/T2035
RBM3D/Evolution/Nonzero.lean
$ git diff main...t/T2035 -- RBM3D/Evolution/Pins.lean RBM3D/Test/Axioms.lean RBM3D/Kernel | wc -l
       0
$ git show t/T2035:RBM3D/Evolution/Nonzero.lean | grep -nE "sorry|admit|^axiom|native_decide|^theorem|^noncomputable def|^def|^lemma|^structure|^example"
146:theorem ekSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNonzero d n Λ κ := by
192:noncomputable def ekDelta0 (n d L : ℕ) : (Fin n → Zd d L) → ℂ := fun a => if a = 0 then 1 else 0
196:example :
211:example :
$ git grep -n -e "ekDelta0" -e "ekSumDecayNonzero_holds" main -- 'RBM3D/*.lean'; echo "(end)"
(end)
```

- Warnings are in pre-existing upstream files only; none in `Nonzero.lean`.
- Only the sole writable file is touched; frozen pin, Kernel files and registry unchanged.
- Public names `ekSumDecayNonzero_holds`, `ekDelta0` are `ek`-prefixed and new on main; the other
  helpers (`ekE`, `ekE_pos`, `ek_norm_*`) are `private`. Imports: `RBM3D.Evolution.XiPins`,
  `RBM3D.Propagator.Prop5Hold` only (not `RBM3D`).
- `decide` in ex. 2 is kernel `decide`, not `native_decide`.

## 5. Paper deltas

```
$ grep -n "T2016e\|T2016f" docs/paper-deltas.md
303:## D37 · `lem:sum_decay_nonzero` 无损、两种电荷（2026-10-03，T2016e；`EKSumDecayNonzero`）
307:## D38 · EK 钉文的常数对 `g ∈ (0, Λ]` 一致，距离用 `ℓ¹`（2026-10-03，T2016f）
```

The Lean/paper differences of this target (loss-free `C‖𝒜‖` instead of `≺`, both charges,
uniform in `g ∈ (0, Λ]`) are D37/D38, cited in the prove report (line 209). The proof adds no
statement difference of its own.

## Observations (no effect on verdict)

- The pin carries `0 ≤ s` in addition to the paper's `1 - λ²/L² ≤ s`; this is a property of the
  merged EK-1 pin (frozen), not of this ticket, and is automatic in the paper's regime
  (`λ ≤ 𝔡⁻¹` small, `L ≥ 3`). The dispatcher may want D37/D38 to mention it explicitly.
- The `Prop5Short` antecedent is unused in the proof (`_h5`); harmless, EK-2 proves it itself.

## Verdict

ekSumDecayNonzero_holds: **PASS**. No dispatcher sign-off needed.
