Auditor model: claude-opus-5-5

# T2156 audit (round 1) — S3-13b `Induction/QGridB`

Sun Oct  4 19:19:52 UTC 2026 — audit worktree `RBM3D-wt/T2156-audit1` (detached at t/T2156 = 07cb977).

## Verdict
- Target 1 `RBM.Ind.sum_weighted_qErrQN_le`: **PASS**
- Target 2 `RBM.Ind.QGridBCheck.sum_weighted_qErrQN_instance`: **PASS**
- Overall: **PASS**.

## 1. Statement (target 1) against the ticket's mathematics
There is no pinned text in the ticket (the check file has `#check` lines only), and RBM2D has no `_Stmt` pin.
The target is "port RBM2D `AltGridQ.lean` §10 `sum_weighted_qErrQN_le` with the T2132/T2153 dictionary".
Script diff: RBM2D statement at `c9a24cf:2147-2163` under the dictionary `k := m+1` (T2132c: `m+1` indices,
`Lp = (L^d)^m`), sum length `m := p`, `d.` := `sz.`, `2 ≤ k` := `1 ≤ m`, `qErrQN d … k` := `qErrQN sz … m C C₂`,
compared hypothesis by hypothesis with `QGridB.lean:565-580`:
```
$ python3 scratchpad/T2156/sd.py   (inputs r2.lean = RBM2D :2147-2163, r3.lean = QGridB.lean :565-580)
RBM2D (k:=m+1, sum length m:=p) vs RBM3D, hypothesis by hypothesis
common: 19 of 19
only in RBM3D:
    0 ≤ C
    0 ≤ C₂
only in RBM2D:
```
So the 4 rows (with `D_t + (m+1)`), `RangeCond`, `SizeTendsto`, the grid hypothesis `N^{C_K} ≤ K n`, the quantifier
order (fixed `κ τ' τK C_K D_t C C₂ m` before `∀ᶠ n`, then `∀ p ≤ K n`) and the conclusion `≤ N^{-D_t}` are RBM2D's
exactly. The only additions are `0 ≤ C`, `0 ≤ C₂`, which are arbitrary universally quantified constants: the merged
`qErrQN` (`QGridA.lean:1349`) takes them as arguments. The theorem is not a special case: it holds for all
`d`, `sz`, `m ≥ 1`, `C, C₂ ≥ 0`.

Merged `qErrQN` signature (the object summed):
```
def qErrQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (C C₂ Bk : ℝ) (j : ℕ) : ℝ :=
  qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
    (lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk)
    (driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk)
    (stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1))
      (gridStep s t K n) Bk)
```
It uses `stepErrN … (m + 1) …` and the envelope `Bk = N^{τK} η_{u_{j+1}}^{-(m+1)}`. The merged
`SumWeightedStepErrN_Stmt` (`GridEnvelopeN.lean:595-610`) is stated at loop length `k`, decay `D_t`. QGridB applies it
at `k = m+1`, decay `D_t + (m+1)`. This matches RBM2D's `D_t + k`.

Ticket deviations. Both are the prover's report T2156b/T2156c, and neither weakens the RBM2D statement.
- The ticket text says "decay exponent `D_t + m` (RBM2D `D_t + k`)". The ticket's own dictionary (`m+1` indices, so RBM2D
  `k ↦ m+1`) turns RBM2D's `D_t + k` into `D_t + m + 1`, which is what the Lean has. The prover's arithmetic
  (report (a)(i)) shows that the `D_t + m` reading cannot close: the first term is `(1+C·Lp)·N^{-(D_t+m)} ≤ (1+C)N^{-D_t}`,
  which is not `≤ N^{-D_t}/2`. Observation: this is an index slip in the ticket text. The Lean is the faithful port.
- There is no `STKbound` hypothesis (the ticket says "with the hypothesis `STKbound` as in `gridDriftN_envelope`").
  The RBM2D theorem and the merged `sum_weighted_stepErrN_le` are deterministic, and dropping the hypothesis only
  strengthens the statement.

## 2. Vacuity, hidden hypotheses, cycles
- The new file introduces no structure, class or `Prop`-valued def. The only structures used are the merged
  `Sizes d`/`SizeTendsto`/`RangeCond` (unchanged).
- Imports are `RBM3D.Induction.QGridA` and `RBM3D.Induction.GridEnvelopeN` only. Both are merged on main (549a62d, a438a51).
  No cycle.
- No external hypothesis is introduced, so no limit check is needed.
- The hypotheses are jointly satisfiable at nondegenerate data (§3).

## 3. Compiled nonempty instance
`QGridB.lean:717-733` applies the theorem at `d = 3`, `sz = sz0` (`N_n = (W_n L_n)^3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`),
`m = 3`, `κ = 1`, `E ≡ 0`, `s ≡ 0`, `t ≡ 1/2`, `τ' = τK = 1/2`, `D_t = 1`, `C_K = 31`, `K n = N_n^{31}`, and the merged
`gridDriftQN` constants `C = (1+40·9)6^9`, `C₂ = 1000(1+9)²`. Every hypothesis is discharged by a term:
```
  sum_weighted_qErrQN_le 3 sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 31) (D_t := 1)
    (C := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (C₂ := 1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
    (E := E1) (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc31) 3 (by positivity)
    (by positivity) one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sz0_tendsto (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun _ => by norm_num) Kc31_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Eventually.of_forall rpow_31_le_Kc31)
```
The rows evaluate to `30, 20, 10.5, 0.5 < 31` (discharged by `norm_num`). `Kc31 n = sz0.size n ^ 31 ≠ 0` and
`rpow_31_le_Kc31` are proved for all `n`. `E1 = fun _ => 0` (`GridEnvelopeN.lean:676`) and `rangeCond_half` are merged.
Nothing is left as a hypothesis. The instance is not degenerate: the sums are nonempty for `p ≥ 1`, the window `[0,1/2]` is
not collapsed, and `K n = N^{C_K}` is the size the theorem itself requires, the same shape as RBM2D's `N^{138}` instance.

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Induction.QGridB   (audit worktree; QGridB lines + tail)
ℹ [3795/3795] Built RBM3D.Induction.QGridB (12s)
info: RBM3D/Induction/QGridB.lean:741:0: 'RBM.Ind.sum_weighted_qErrQN_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:742:0: 'RBM.Ind.QGridBCheck.Kc31' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:743:0: 'RBM.Ind.QGridBCheck.Kc31_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:744:0: 'RBM.Ind.QGridBCheck.rpow_31_le_Kc31' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:745:0: 'RBM.Ind.QGridBCheck.sum_weighted_qErrQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3795 jobs).
lake build RBM3D.Induction.QGridB  19.89s user 5.06s system 151% cpu 16.414 total
$ grep -nE "sorry|admit|native_decide|^\s*axiom" RBM3D/Induction/QGridB.lean ; echo $?
1
$ git diff --stat main...t/T2156
 RBM3D/Induction/QGridB.lean | 745 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 745 insertions(+)
$ git grep -nE "sum_weighted_qErrQN|QGridBCheck|Kc31|qGridB_" main -- RBM3D RBM3D.lean
RBM3D/Induction/QGridA.lean:36:Not here: RBM2D's section 10 (`sum_weighted_qErrQN_le`, the summed envelope), which needs
```
- No errors.
- The QGridB axioms are only `propext`, `Classical.choice` and `Quot.sound`. The other warnings in the log are in pre-existing modules (`Path/*`).
- The only file touched is the sole writable file. `Test/Axioms.lean` is untouched, and no registry line was expected.
- No frozen signature is changed.
- No name clash: the only match on main is a docstring.
- Unpinned helpers are `private qGridB_*`. `Kc31`, `Kc31_ne_zero` and `rpow_31_le_Kc31` sit in the file-stem namespace `QGridBCheck`,
  as in the merged `GridEnvelopeNCheck`.
- The file has `set_option linter.style.longLine/unusedSectionVars/unusedVariables false` (linters only; not a soundness issue).

## 5. Paper-delta coverage
Lean-vs-source differences, each matched to a candidate in the prove report (d):
- extra constants `0 ≤ C, C₂`: T2156a;
- decay `D_t + (m+1)` vs the ticket's `D_t + m`: T2156b;
- no `STKbound`: T2156c;
- `m ≥ 1` tensor index / sum length `p` (a renaming only): listed in (d).

None is yet in `docs/paper-deltas.md` (`grep T2156` returns nothing). They are candidates for the dispatcher to number.
Coverage is complete.

## Observations (no effect on the verdict)
- The ticket text's `D_t + m` is an index slip (see §1). Consumers S3-14/S3-15a must supply the rows with `D_t + (m+1)`,
  as RBM2D's consumers do with `D_t + k`.
- The branch base is 88600b1. Main has since moved to 74400b7 (T2152, `Evolution/CltStep`), which does not touch QGridB's imports.
- The instance needs a new grid `N^{31}`: the merged `Kc = N^{21}` is too small, because row R1 is 30.
- The prove report (c) says "Names verified absent: none checked". That is a report gap only.
