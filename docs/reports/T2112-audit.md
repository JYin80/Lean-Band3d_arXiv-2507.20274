Auditor model: claude-opus-5-5
# T2112 audit (S3-20, `RBM3D/Induction/ZeroModeCalc.lean`) — round 1, Sun Oct  4 07:02:57 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2112-audit1` (detached at `t/T2112` = c6ff966). The check file
`docs/tickets/checks/T2112-check.lean` holds only `#check` lines and no pinned statement text, so each statement is
compared with the ticket's mathematics and the paper (`3_5_Loop_Hierarchy.tex:1444-1559, 1891-1893`).

## 1. Diff scope, hygiene, build
```
$ git diff --stat main...t/T2112
 RBM3D/Induction/ZeroModeCalc.lean | 820 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 820 insertions(+)
$ git log --oneline t/T2112..main      # main moved by one unrelated merge, no shared file
2270c89 T2116: merge ST2-15 Induction/OptL2b (stOptL2_of_pins)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' RBM3D/Induction/ZeroModeCalc.lean; echo "grep exit=$?"
grep exit=1
$ grep -n "Prop :=" RBM3D/Induction/ZeroModeCalc.lean; echo "exit=$?"   # no new Prop def => no registry line owed
exit=1
$ lake build RBM3D.Induction.ZeroModeCalc 2>&1 | grep -E '^error|ZeroModeCalc|Build completed'; echo "exit=${pipestatus[1]}"
Build completed successfully (3761 jobs).
exit=0
```
The first build in the worktree also printed only warnings from other merged files (none in `ZeroModeCalc`).
Name clash, 22 public short names of the file, `git grep -nw <name> main -- 'RBM3D/*.lean'`: `total hits on main: 0`.

## 2. Axioms (`lake env lean scratchpad/T2112/ax.lean`)
```
'RBM.norm_zeroModeSet_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.norm_zeroModeOp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeSet_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeSet_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeSet_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeSet_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeSet_UN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeSet_ThetaN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeOp_UN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.zeroModeOp_ThetaN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.zeroModeSet_Ugen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.zeroModeCalc_duhamel_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.zeroModeCalc_duhamel_inside_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.zeroModeCalc_LK_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.zeroModeCalc_LK_expansion_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.sameSignOutside_of_STIdiff_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The same scratch file also compiled `example : RBM.Gauss.SizesInst.sz0.L 0 = 4 := by simp [sz0_values]` (no output, so the `sz0` instances are at `L = 4`).

## 3. Statements against the ticket and paper
Definitions used (merged, `Kernel/Evolution.lean:190-201`): `avgOp i A a = L^{-d} Σ_c A(a[i↦c])`, `zeroModeOp = A − avgOp`,
`zeroModeSet A = foldr zeroModeOp over A.toList`. These are paper `def;zero_mode_remove` (`P^{(i)}`, `Q^{(i)} = I − P^{(i)}`, `Q^{(A)} = ∏_{i∈A} Q^{(i)}`).
The norm on `(Fin n → Zd d L) → ℂ` is Mathlib's Pi sup norm, which is the `‖·‖_∞` of `(normQA2)`.

| target | Lean (file line) | ticket / paper | check |
|---|---|---|---|
| 1 `(normQA2)` | `norm_zeroModeOp_le:124` `‖Q^{(i)}T‖ ≤ 2‖T‖`; `norm_zeroModeSet_le:163` `‖Q^{(A)}T‖ ≤ 2^{A.card}‖T‖`; no hypotheses beyond `[NeZero L]` | `3_5:1466` (one index, constant 2); ticket: `2^{|A|}` | matches; constant has no `L,W,λ` |
| 1 linearity | `zeroModeSet_add:91`, `_smul:96`, `zeroModeSetLin:101` (a `ℂ`-linear map), `_zero`, `_sub`, `_sum`, `_empty` | "Q^{(A)} is linear" | matches |
| 2 Θ | `zeroModeSet_ThetaN:395`: `(3 ≤ L) (∀ i, ‖t·cycProd m i‖ < 1)`, `∀ A T`, `Q^{(A)}(ThetaN m t T) = ThetaN m t (Q^{(A)} T)` | `3_5:1542` commutation remark | matches; hyps make `Θ_{tμ}` exist (T2112a) |
| 2 𝒰 | `zeroModeSet_UN:332`: the same hyps, `s` free | as above | matches |
| 2 `Ugen` | `Ind.zeroModeSet_Ugen:450`: `3 ≤ L`, `|E| ≤ 2`, `0 ≤ w < 1`, `v` free | as above, DECISIONS §29 window | matches; weaker than §29 (`s ≤ t` not needed) |
| 3 `(iisuwjyys)` grid | `Ind.zeroModeCalc_duhamel_at:493` (Q outside 𝒰) and `_inside_at:522` (Q inside 𝒰). Hyps: `|E n| < 2`, `0 ≤ s n ≤ t n < 1`, `K n ≠ 0`, `min j (τ ω) ≤ K n`; any `k`, `σ`, `A`, `τ`, `ω`. Kernel index `u_{i+1}` | `3_5:1545`; ticket: initial + predictable + martingale sums | matches the merged `stoppedDuhamelN_at` (same hyps, read at `GridDuhamelN.lean:310-319`); `u_{i+1}` vs ticket `u_j` is the merged telescope index (T2112c) |
| 4 newPQ combination | `Gauss.Sizes.zeroModeCalc_LK_expansion:563` (every `A`) and `_empty:595` (`A = ∅`): `∃ ℓ k ξ σ' ι A'`, `1 ≤ k α ≤ m − 1`, `STIdiff (σ' α) ⊆ A' α`, then `∀ sz n E τ`, `|E|<2`, `0 ≤ τ < 1`, `∀ ω a`: `(𝓛−𝒦)_{σ,a} = Q^{(I_diff σ)}(𝓛−𝒦)_{σ,a} + Σ_α ξ_α/(2iNη_τ)^{m−k_α} Q^{(A'_α)}(𝓛−𝒦)_{σ'_α, a∘ι_α}` | `3_5:1891-1893` `(eq:expandQAempty)`; `yurenAL`, `yurenAK` (`A_n = A ∪ I_diff`) | matches; data uniform in `(sz,n,E,τ,ω,a)`, as in the merged `STNewPQ` |

Quantifier order: the expansion data comes before `∀ sz n` (fixed before `N`), the same as `stNewPQ_holds`. `(𝓛−𝒦)` is the merged `STLKM … (sz.seqHflow n τ ω)`
(`Step2Defs.lean:68`: `STLM − STKloop`). Target 4's range remark: `sameSignOutside_of_STIdiff_subset:419` / `sameSignOutside_union_STIdiff:427` turn `I_diff σ ⊆ A` into
`SameSignOutside (fun i => f (σ i)) A` for any `f : Bool → ℂ`. The report's finding F1 is confirmed by script:
```
$ sed -n 629,631p RBM3D/Kernel/Evolution.lean
theorem norm_zeroModeSet_UN_le {k n : ℕ} {g : ℝ} {m : Fin n → ℂ} {A : Finset (Fin n)}
    (hd : 3 ≤ k + 2) (hg : 0 < g) (hm : ∀ i, ‖m i‖ = 1) (hmi : ∀ i, 0 < (m i).im)
$ sed -n 85p RBM3D/Defs/Semicircle.lean
noncomputable def mSigma (E : ℝ) (s : Bool) : ℂ := if s then mE E else (starRingEnd ℂ) (mE E)
```
So the bridge provides `SameSignOutside`, but `norm_zeroModeSet_UN_le` itself applies only when every `m i` has positive imaginary part.
This is a defect in a merged file, not in T2112 (paper-delta candidate T2112e). The ticket's own text allows
"if this needs … a different form, say so", and the report says so.

**Statement verdicts:** targets 1–4 PASS. None is a special case of the ticket's target. Target 4 is stated for every `A`,
with `A = ∅` as a corollary. That is more general than the ticket asks, and the paper's `yurenAL` is stated for every `A` too.

## 4. Vacuity, hidden hypotheses, cycles
- No new `structure` or `Prop` definition. All hypotheses are explicit, deterministic and satisfiable (instances below).
- Dependencies are merged results only: `stoppedDuhamelN_at`, `GridDuhamelN_Ugen_add` (T2104); `stNewPQ_holds` (T2086,
  a proved theorem, `NewPQ.lean:584`); `projMat_mul_SB_comm`, `zeroModeOp_tensorKer`, `Theta_transpose_of_three_le` (EK-5);
  `norm_mul_mSigma_lt_one` (Defs). There is no external hypothesis, so no limit check is owed. Nothing imports `ZeroModeCalc`, so there is no cycle.

## 5. Compiled nonempty instances (in the file, built above; 18 `example`s)
Data: `σ = (+,−,+)` (`zmcSigma`), `A = STIdiff σ` with `card = 2` (`decide`), and `T = δ₀` on `(Z_4^3)^3` with `zmcDelta ≠ 0` proved.
- T1: `:642` gives `zmcDelta ≠ 0 ∧ ‖Q^{(A)}δ₀‖ ≤ 2^2‖δ₀‖` at `d=3, L=4`; `:649` is the one-index form; `:653/:659/:665/:669` cover add, smul, sub, sum and empty.
- T2: `:678` (`UN`), `:686` (`ThetaN`) and `:694` (`Ugen`) at `d=3, L=4, g=1/2, E=0, (s,t)=(9/10, 99/100)`, with
  `A = STIdiff σ` and `δ₀ ≠ 0`. `3 ≤ L` is discharged by `norm_num` and the slot bound by `zmc_slot_lt_one`.
- T3: `:741` and `:763` at `sz0`, `n = 0` (`L = 4`), `E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`, `j = 4`.
  Then `min j τ = 3`, so each sum has 3 terms. Every hypothesis is discharged by `norm_num`. `ω` is universally quantified (that is not a premise).
- T4: `:786` (`_empty`) and `:802` (`A = {2}`) at `sz0`, `n=0`, `E=0`, `τ=1/2`, `m=3`, `σ=(+,−,+)`, with `|E|<2` and `0 ≤ τ < 1` discharged.
No instance uses `N = 0`, an empty index, a collapsed window, a `False` premise or an astronomically large witness. All PASS.

## 6. Paper-delta coverage
The report proposes T2112a (commutation hypotheses `3 ≤ L`, `‖tμ_i‖ < 1`; for `Ugen`, `|E| ≤ 2` and `0 ≤ w < 1`),
T2112b (`(normQA2)` for `Q^{(A)}` with `2^{|A|}`), T2112c (the pathwise stopped grid identity replaces the time integral; kernel index `u_{i+1}`),
T2112d (the combination for every `A`, through `STLKM` at `seqHflow`) and T2112e (`hmi` in the merged `norm_zeroModeSet_UN_le`).
Every Lean/paper difference in §3 is covered by one of these. PASS.

## 7. Observations (no verdict change)
- O1. Ticket target 3's parenthetical says "the martingale part stays a martingale". It is not a Lean statement here:
  the report (F3) defers the `condExp`/integrability bookkeeping to S3-21. The identity itself, in both orders, is stated
  and proved. S3-21 should know that it must prove `Q^{(A)} martIncN` is a martingale increment (a finite linear combination of coordinates).
- O2. T2112e: `norm_zeroModeSet_UN_le` (merged EK-5) is usable only when every `m i` has `Im > 0`, which is the all-`+` charge.
  For mixed `σ`, consumers must use `ekSumDecayNonzero_holds` / `STEKNonzero`. This is for the dispatcher to route, not a T2112 defect.
- O3. `main` advanced by T2116 after the branch point. No file is shared, and the hub's full build at merge covers it.

## Verdict
| target | verdict |
|---|---|
| 1 `(normQA2)` + linearity | PASS |
| 2 commutation `ThetaN`, `UN`, `Ugen` | PASS |
| 3 grid `(iisuwjyys)` (outside / inside) | PASS |
| 4 newPQ combination (`A` general, `A = ∅`) | PASS |

**T2112: PASS.** No dispatcher sign-off is needed for the merge. O1 and O2 are forwarded as notes for S3-21 and EK-5.
