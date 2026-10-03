Auditor model: claude-opus-5-5

# T2034 audit, round 1 (EK-3: `(sum_res_1)`, `(sum_res_2_NAL)` for every `n ≥ 2`)

Written Sat Oct  3 06:17:16 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2034-audit1`, detached at `t/T2034` = `31797d9`; merge base with `main` = `890a89f`.

## 0. Diff scope

```
$ git diff --name-only main...t/T2034
RBM3D/Evolution/SumDecay.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2034 -- RBM3D/Test/Axioms.lean
-   `RBM.Green.Stable]         -- stability of `1 − ξS` with constant `K`; band profile S1-24
+   `RBM.Green.Stable,         -- stability of `1 − ξS` with constant `K`; band profile S1-24
+   `RBM.EKFastDecay]          -- `(deccA0)`: decay of the tensor `A` beyond the window `W^ε ℓ_s`, a data condition on `A` (EK-3, T2034)
$ git diff --stat 890a89f main -- RBM3D/Test/Axioms.lean RBM3D/Evolution/ RBM3D/Kernel/ RBM3D/Propagator/
(empty: nothing these files depend on changed on main since the branch base)
```
Both files are sole writable files (`SumDecay.lean` new; `Axioms.lean` appended registry line only, Amend 1). `Pins.lean` and `Kernel/*` are untouched. The module imports `RBM3D.Evolution.XiPins` and `RBM3D.Propagator.Prop5Hold` only, not `RBM3D`.

## 1. Statements against the pins

```
$ grep -n "^theorem ekSumDecay" RBM3D/Evolution/SumDecay.lean
325:theorem ekSumDecay1_holds (d n : ℕ) (Λ : ℝ) : EKSumDecay1 d n Λ := by
420:theorem ekSumDecayNAL_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNAL d n Λ κ := by
$ cat ax_T2034.lean    # scratch file outside the repository
import RBM3D.Evolution.SumDecay
open RBM
example : ∀ d n Λ, EKSumDecay1 d n Λ := ekSumDecay1_holds
example : ∀ d n Λ κ, EKSumDecayNAL d n Λ κ := ekSumDecayNAL_holds
#print axioms RBM.ekSumDecay1_holds
#print axioms RBM.ekSumDecayNAL_holds
#print axioms RBM.ek_UN_anchor_bound
$ lake env lean ax_T2034.lean; echo exit=$?
'RBM.ekSumDecay1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekSumDecayNAL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_UN_anchor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The theorem types are exactly the ticket's pinned types (`EKSumDecay1 d n Λ`, `EKSumDecayNAL d n Λ κ`, merged definitions in `RBM3D/Evolution/Pins.lean`, unchanged). Reading those definitions (Pins.lean:76, :92): `∃ C` after `(d, n, Λ[, κ])`, before `L, g, W, ε, D, s, t, m, σ, A`; `0 < g ≤ Λ`; `4 ≤ W^ε`; `0 ≤ s ≤ t ≤ 1 − g²/L²`; `W⁻¹ ≤ (1−t)/(1−s)`; `‖m‖ = 1`; `(sum_res_1)` RHS `W^{Cε} (ℓ_t²/ℓ_s²) r^n ‖A‖ + W^{−D+C}`; NAL with `κ ≤ Im m`, `∃ k, σ k = σ (finRotate n k)`, RHS `W^{Cε} r^{n−1} ‖A‖ + W^{−D+C}`. All `n ≥ 2` (general target, not a special case). Statement: matches the pin for both targets.

## 2. Vacuity, hidden hypotheses, cycles

- No structure-field hypotheses. The only antecedents are those inside the pins: `Prop5Decay`, `Prop5Short` (proved: `prop5Decay_holds` Prop5Hold.lean:784, `prop5Short_holds` Prop5Short.lean:400, both unconditional `theorem … : Prop5Decay d Λ` / `Prop5Short d Λ κ`), and the data condition `EKFastDecay` (DECISIONS §20 names `(deccA0)` as structural; registered as such).
- Inputs used are merged theorems: `ekXiBall_holds` (XiPins.lean:346), `ekSameRow_holds` (XiPins.lean:357), `norm_uKer_le`, `sum_norm_row_le`, `uKer_eq_one_add_XiKer`. No circular dependency (the module imports only upstream files).
- Public helper `ek_UN_anchor_bound` takes `EKFastDecay` and the window-sum bound `hX` as explicit hypotheses; `hX` is discharged from `ekXiBall_holds` inside both targets.
- No external hypothesis remains in either target, so no limit check is needed.

Registry pre-check (DECISIONS §20), scratch file outside the repository:
```
$ printf 'import RBM3D\nimport RBM3D.Evolution.SumDecay\n#assert_rbm_axioms\n' > pre_T2034.lean
$ lake env lean pre_T2034.lean; echo exit=$?
axiom audit: 1120 theorems, 415 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
...
premises found by scanning: 13 (borrowed 2, owed 0, structural 11).
...
exit=0
```

## 3. Compiled nonempty instances (SumDecay.lean:520–629)

Data: `d=3, L=5, g=1/2, Λ=1, κ=1/2, W=25, ε=1/2 (W^ε=5), D=2, s=1/2, t=9/10, m=Complex.I, A=ekSDdelta0 n = δ_0`.
```
592: example : ∃ C : ℝ, 0 < C ∧ ‖UN 3 5 (1/2) (EKsgn Complex.I ![true, false]) (1/2) (9/10) (ekSDdelta0 2)‖ ≤ …
  obtain ⟨C, hC, H⟩ := ekSumDecay1_holds 3 2 1 (prop5Decay_holds 3 1) le_rfl le_rfl one_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ekSD_sqrt25]; norm_num)
    (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
    Complex.norm_I ![true, false] (ekSDdelta0 2) (ekSD_fastDecay 2)⟩
604: same, ekSumDecay1_holds 3 3 1 …, σ = ![true, false, true], ekSDdelta0 3
616: ekSumDecayNAL_holds 3 3 1 (1 / 2) (prop5Decay_holds 3 1) (prop5Short_holds 3 1 (1 / 2)) …,
     … Complex.norm_I (by norm_num [Complex.I_im]) ![true, true, false] ⟨0, by decide⟩ (ekSDdelta0 3) (ekSD_fastDecay 3)
574: example (n : ℕ) : ‖ekSDdelta0 n‖ = 1                     -- A ≠ 0
583: example (n : ℕ) (hn : 2 ≤ n) : ∃ a i j, 25^(1/2) * ellT 5 (1/2) (1/2) ≤ zdistD 3 5 (a i - a j)
                                                              -- far set of (deccA0) nonempty (distance 5, ℓ_s = 1)
```
Every hypothesis is discharged at concrete numbers (`norm_num`, `Complex.norm_I`, `decide` for `σ 0 = σ 1`, private `ekSD_fastDecay` for `EKFastDecay`); `Prop5Decay`/`Prop5Short` by the proved theorems. Nondegenerate: `n ∈ {2,3}`, `L = 5`, `‖A‖ = 1`, window radius 5 below the torus `ℓ¹` diameter 6, `W^ε = 5` (not astronomically large), `t < 1 − g²/L² = 0.99`, `W⁻¹ = 1/25 < 1/5`. These are exactly the ticket's required instances. The file builds, so they elaborate.

## 4. Build, axioms, forbidden tokens

```
$ lake build RBM3D.Evolution.SumDecay 2>&1 | grep -E "error|warning.*SumDecay|sorry"
(no output)
$ lake build RBM3D.Evolution.SumDecay 2>&1 | tail -1
Build completed successfully (3418 jobs).
$ lake build 2>&1 | tail -1
Build completed successfully (3731 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|opaque|implemented_by|extern" RBM3D/Evolution/SumDecay.lean
(no output)
```
Axioms: only `propext`, `Classical.choice`, `Quot.sound` (§1 output; registry pre-check §2).

Name-clash grep (new public names vs every other `RBM3D/**/*.lean`, `Probe/` excluded):
```
$ for n in …; do grep -rnwE "(theorem|lemma|def) $n" RBM3D --include='*.lean' | grep -v Evolution/SumDecay.lean | grep -v Probe | wc -l; done
ek_ellT_sq_ge other-defs=0
ek_ratio_le other-defs=0
ek_anchor_sum_le other-defs=0
ek_prod_sum_le other-defs=0
ek_core_bound other-defs=0
ek_arith_res1 other-defs=0
ek_arith_nal other-defs=0
ek_UN_anchor_bound other-defs=0
ekSumDecay1_holds other-defs=0
ekSumDecayNAL_holds other-defs=0
```
All public helpers are `ek`-prefixed (ticket, §3 (E)); instance data are `private`.

## 5. Paper deltas

The targets are the signed pins; the Lean/paper differences they carry are the candidates T2016a, T2016b (`4 ≤ W^ε`), T2016f (uniform in `g ∈ (0, Λ]`, `ℓ¹` distance in `(deccA0)`), signed in DECISIONS §18 and cited (not re-proposed) in the prove report (d). The proof adds no hypothesis to either pin, so no new candidate is needed. Covered.

## 6. Observations (no RETURN)

- O1. The ticket's preflight numeric list includes `t = 1 − g²/L²` with `W = 25`, where the pin's own hypothesis `W⁻¹ ≤ (1−t)/(1−s)` fails; the preflight used `W = max(25, P)` there and said so. Ticket-side wording only; it changes no statement or instance.
- O2. `Axioms.lean` registry line may conflict at merge with other Amend-1 lines on the last list element; DECISIONS §20 (3) (take the union) applies. `main` has not changed `Axioms.lean` since the branch base (§0).

## Verdicts

| target | statement | vacuity/hidden/cycle | instance | build/axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `ekSumDecay1_holds` | = pin | clean | n=2, n=3 compiled | pass | covered (T2016a/b/f) | **PASS** |
| `ekSumDecayNAL_holds` | = pin | clean | n=3, σ=(+,+,−) compiled | pass | covered (T2016a/b/f) | **PASS** |

Overall: **PASS**. No dispatcher sign-off needed.
