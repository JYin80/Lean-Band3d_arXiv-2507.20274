Auditor model: claude-opus-5-5

# T2042 audit (round 1) — `ekSumDecay2_holds : EKSumDecay2 d n Λ κ` (amended pin, Amend 1 / DECISIONS §21)

Audit worktree `RBM3D-wt/T2042-audit1`, detached at `t/T2042` = `dde1751`; merge base `cca94be`; main `bac6c2f`.

## 1. Scope of the diff
```
$ git diff --stat main...t/T2042
 RBM3D/Evolution/Pins.lean         |   10 +-
 RBM3D/Evolution/SumDecayZero.lean | 1746 +++++++++++++++++++++++++++++++++++++
$ git diff --stat cca94be main -- RBM3D/Evolution/{Pins,SumDecay,XiPins}.lean
(no output: main did not touch these files since the merge base)
$ git diff main...HEAD --stat -- RBM3D/Test/Axioms.lean
(no output: registry not edited)
```
Both touched files are sole writable files (SumDecayZero.lean new; Pins.lean by Amend 1).

## 2. Statement
### 2a. The amended pin vs the check file (Amend 1: "verbatim")
```
$ awk '/^def EKSumDecay2/{f=1} f{print} f&&/W \^ \(-D \+ C\)/{exit}' docs/tickets/checks/T2042-check.lean > pin_check.txt
$ awk '...same...' RBM3D/Evolution/Pins.lean > pin_branch.txt
$ wc -l: 14 pin_check.txt, 14 pin_branch.txt
$ diff pin_check.txt pin_branch.txt && echo IDENTICAL
IDENTICAL
```
### 2b. The three Pins.lean edits allowed by Amend 1 (full diff, only hunks)
```
@@ -105,13 +105,16 @@ def EKSumDecayNAL
-`T2016a`). -/
+`T2016a`).  `L^d ≤ W^K` (candidate `T2042a`, DECISIONS §21) is the paper's `(Main_DEL_COND)` read
+with `K = 1/𝔠`; `C` depends on `K`. -/
 def EKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
   Prop5Decay d Λ → Prop5Short d Λ κ → Prop6Diff1 d Λ κ (1 / 2) →
     3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
+    ∀ K : ℝ, 0 < K →
     ∃ C : ℝ, 0 < C ∧
...
+        (L : ℝ) ^ d ≤ W ^ K →
@@ -363,10 +366,11 @@ private theorem ekInstDecay2
-    (by norm_num)
+    (by norm_num) 2 two_pos
-    ek_log5 (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
+    ek_log5 (by norm_num [Real.rpow_two]) (1 / 2) (9 / 10) (by norm_num) (by norm_num)
+    (by norm_num) (by norm_num) Complex.I
```
Docstring sentence = Amend 1 text; `ekInstDecay2` uses `K = 2` (`5^3 ≤ 25^2`). Nothing else in Pins.lean changed.
Downstream users of the amended `def` on main: `git grep -n EKSumDecay2 main -- RBM3D` lists only Pins.lean (doc line 20, def 109, `ekInstDecay2` 358–359).

### 2c. Target
```
$ lake env lean axs.lean     (#print axioms / #check)
'RBM.ekSumDecay2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.ekSumDecay2_holds : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecay2 d n Λ κ
```
This is the type pinned in the ticket: same name, no extra binders, no hypotheses.

### 2d. Against the paper (`3_5_Loop_Hierarchy.tex:1640–1663`, `lem:sum_decay` (II))
- `(deccA0)` "max_{i,j}|a_i−a_j| ≥ W^ε ℓ_s ⇒ |A_a| ≤ W^{-D}" corresponds to `EKFastDecay` (Pins.lean:51–53, `∃ i j, W^ε * ellT L g s ≤ zdistD (a i - a j) → ‖A a‖ ≤ W^(-D)`).
- `(sumAzero)` "Σ_{a_2..a_n} A_a = 0 ∀ a_1" corresponds to `EKSumZero` (Pins.lean:56–58, index `i₀.val = 0` fixed at `x`).
- `0 ≤ s ≤ t ≤ 1 − λ²/L²` and `(1−t)/(1−s) ≥ W^{-1}` appear verbatim. The conclusion `W^{Cε} r^n ‖A‖ + W^{-D+C}` matches `(sum_res_2)` with exponent `n`.
- Quantifier order: `∃ C` comes before `∀ L g W ε D s t m σ A`, so `C` is independent of `ε, D`, as the paper requires. `C` depends on `K`, which is the signed delta T2042a.
- Lean/paper differences: `log L ≤ W^ε` (T2016a = D33), `4 ≤ W^ε` (T2016b = D34), uniformity in `g ∈ (0,Λ]` and `ℓ¹` (T2016f = D38), and `∀ K, L^d ≤ W^K` (T2042a, signed in DECISIONS:181, number assigned at merge per DECISIONS:188). Propagator inputs enter as antecedents `Prop5Decay`, `Prop5Short`, `Prop6Diff1 (c = 1/2)`, all proved (§3).
- Every difference is the pin's text, which the dispatcher fixed in Amend 1. The target adds nothing.
**Statement: PASS.**

## 3. Hidden hypotheses, vacuity, cycles
- `EKFastDecay` and `EKSumZero` are `def … : Prop` predicates on the data `A`, not structures, and they carry no fields (Pins.lean:51, 56).
- The pin's propagator antecedents are discharged by merged theorems that take no hypotheses:
```
RBM3D/Propagator/Prop5Hold.lean:784:theorem prop5Decay_holds (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := by
RBM3D/Propagator/Prop5Short.lean:400:theorem prop5Short_holds (d : ℕ) (Λ κ : ℝ) : Prop5Short d Λ κ := by
RBM3D/Propagator/Prop6Hold.lean:353:theorem prop6Diff1_holds (d : ℕ) (Λ κ c : ℝ) : Prop6Diff1 d Λ κ c := by
```
- The proof opens with `intro h5 _h5s h6 hd hn hΛ hκ K hK` and uses `ekXiBall_holds` and `ekXiDecay_holds` (EK-2, merged), `latC`/`latticesum_d3` (Kernel/SumDecay, merged), and `h6` (the antecedent).
- No cycle: the file imports `RBM3D.Evolution.SumDecay` and `RBM3D.Propagator.Prop6Hold` only, and nothing on main imports it.
- External hypotheses: none. The three antecedents are proved Props, so no limit check is owed.
- Non-vacuity of the antecedents: all of them are discharged at concrete data in §4, including `L^d ≤ W^K` (125 ≤ 625) and the far premise of `(deccA0)` (an `example` with `zdistD = 5 = W^ε ℓ_s`).
**PASS.**

## 4. Compiled nonempty instances (SumDecayZero.lean:1713–1744, built in §5)
```
example : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekSZAz2‖ ≤ … := by
  obtain ⟨C, hC, H⟩ := ekSumDecay2_holds 3 2 1 (1 / 2) (prop5Decay_holds 3 1)
    (prop5Short_holds 3 1 (1 / 2)) (prop6Diff1_holds 3 1 (1 / 2) (1 / 2)) le_rfl le_rfl one_pos
    (by norm_num) 2 two_pos
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) … 25 (1 / 2) 2 … ekSZ_log5 (by norm_num [Real.rpow_two])
    (1 / 2) (9 / 10) … Complex.I Complex.norm_I … ![true, false] ekSZAz2 ekSZ_fastDecay2 ekSZ_sumZero2⟩
(n = 3: ekSumDecay2_holds 3 3 1 (1/2) …, σ = ![true, false, true], ekSZAz3 = δ₀⊗(δ₀−δ_e)⊗δ₀, same data)
```
- The data are those of the ticket: d=3, L=5, g=1/2, Λ=1, κ=1/2, K=2, W=25, ε=1/2, D=2, s=1/2, t=9/10, m=i, `A = δ₀⊗(δ₀−δ_e)` with e=(1,0,0).
- Every hypothesis is discharged in the term:
  - the three pins, by the `_holds` theorems;
  - `EKFastDecay`, by `ekSZ_fastDecay2/3` (private theorems);
  - `EKSumZero`, by `ekSZ_sumZero2/3` (private theorems);
  - the numeric premises, by `norm_num` / `ekSZ_log5`.
- Non-degeneracy:
  - the tensors take the values 1 and −1, by the `example`s at :1695 and :1699;
  - the far premise is reachable, by the `example` at :1705;
  - N = 5³ = 125, and the window is not collapsed (W^ε ℓ_s = 5 < torus ℓ¹-diameter 6).
- The ticket's `n = 2` σ is `![true,false]`. The ticket gives no σ for `n = 3`, and `(+,-,+)` is a valid choice.
**PASS.**

## 5. Build, axioms, forbidden tokens, names (audit worktree)
```
$ lake build RBM3D.Evolution.SumDecayZero
Build completed successfully (3421 jobs).
$ lake build RBM3D.Evolution.Pins
Build completed successfully (2544 jobs).
$ lake build RBM3D        (whole library with the amended Pins.lean; root #assert_rbm_axioms)
info: RBM3D.lean:79:0: axiom audit: 1345 theorems, 469 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 16 (borrowed 2, owed 1, structural 13).
Build completed successfully (3739 jobs).
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Evolution.SumDecayZero; #assert_rbm_axioms)
axiom audit: 1346 theorems, 469 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 16 (borrowed 2, owed 1, structural 13).
$ #print axioms RBM.ekSumDecay2_holds
'RBM.ekSumDecay2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " SumDecayZero.lean Pins.lean
(no output, exit 1)
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev|instance|structure)" SumDecayZero.lean
1411:theorem ekSumDecay2_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecay2 d n Λ κ := by
$ grep -c "^private" SumDecayZero.lean
44
$ git grep -n "ekSumDecay2_holds" main -- RBM3D RBM3D.lean
(no output, exit 1: no clash)
```
- The registry pre-check reports the same premise count with and without the new module (16), so the registry is unchanged.
- The only lemma that takes `EKFastDecay`/`EKSumZero` as hypotheses is private (`ekSZ_concrete`).
- No frozen signature changed. The `EKSumDecay2` body change is authorized by Amend 1.
**PASS.**

## 6. Paper deltas
| Lean/paper difference | coverage |
|---|---|
| `∀ K > 0`, `L^d ≤ W^K`, `C = C(K)` | T2042a, signed (DECISIONS §21, l.181); numbered at merge (l.188) |
| `log L ≤ W^ε` | D33 (T2016a) |
| `4 ≤ W^ε` | D34 (T2016b) |
| `g ∈ (0,Λ]` uniform constants, `ℓ¹` distance | D38 (T2016f) |
| `ρ`-power `m₁+2n+2` vs paper `n+5` | inside the existential `C_n`; the paper's `C_n` is also unspecified, so this is not a statement difference |
The report cites all four entries and proposes no new candidate. **PASS.**

## 7. Observations (not RETURN: none changes a statement, an instance, the build, the axioms or delta coverage)
- O1. Section (a) row 7 counts `ρ^{n+3}`; the file proves `ρ^{m₁+2n+2}`. The report states this in (a′) and (d)(iii). `C` is existential, so no statement changes.
- O2. `Prop5Short` (`_h5s`) and `1 < D` are unused antecedents of the pin. The report lists them for the dispatcher in (d)(i). Dropping them would be a pin amendment, so the target is unaffected.
- O3. The RBM2D templates named in the ticket were not opened. No port was made, so no diff-stat is owed.
## Verdict
`ekSumDecay2_holds` — **PASS** (statement, non-vacuity, instances, build/axioms, paper deltas). The three Pins.lean edits match Amend 1. No dispatcher sign-off needed.
