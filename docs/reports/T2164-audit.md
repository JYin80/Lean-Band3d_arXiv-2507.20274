Auditor model: claude-opus-5-5
# T2164 audit (round 1), Sun Oct  4 22:27:08 UTC 2026

Branch `t/T2164` at `53bfb7b`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2164-audit1` (detached). Scratch files: `scratchpad/T2164/{ax,inst2}.lean`.

## 1. Build, hygiene, diff
```
$ git diff --name-only main...HEAD
RBM3D/Path/LemDecCalE.lean
$ lake build RBM3D.Path.LemDecCalE 2>&1 | grep -E "error|warning|Build completed" | tail -5
warning: RBM3D/Path/Markov.lean:766:100: This line exceeds the 100 character limit, ...   (other merged files only)
warning: RBM3D/Path/StepDecomp.lean:33:100: ...
warning: RBM3D/Path/StepDecomp.lean:52:100: ...
warning: RBM3D/Path/DriftAlgebra.lean:27:100: ...
Build completed successfully (3780 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|unsafe" RBM3D/Path/LemDecCalE.lean | wc -l
       0
$ lake env lean scratchpad/T2164/ax.lean      (#print axioms)
'RBM.Path.lossE2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.E2Hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_lk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.lemDecCalE_lk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_e2Hyp_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.LemDecCalE_e7' / _e8 / _e6 / _e9 / _e10b / _sum_tail_tail: [propext, Classical.choice, Quot.sound] (each)
exit=0
```
New file only; no frozen signature touched; `Test/Axioms.lean` untouched (none expected by the ticket).

## 2. Target 3 `lemDecCalE_lk : LemDecCalE_lk d` (res_deccalE_lk, `3_5:2318`)
Pinned shape (ticket): `|𝓔^{LK×LK}_{u,σ,a}| ≤ lossE2 · (1−u)⁻¹ (W^d|1−u|)⁻¹ (J*)² · T_{u,D}(|a₁−a₂|)` in the scale of the first conjunct of `STLemDecCalEConcl`.
Script comparison of the right side (consumer `Step5Pins.lean:169-170` with `p.1 ↦ u`, `Jst n u D ↦ J`, `p.2.2 ↦ a`; target `LemDecCalE.lean:103-104` with `lossE2 … *` removed; spaces/parens stripped):
```
consumer: 1-u⁻¹*sz.Wn:ℕ^d*|1-u|⁻¹*J^2*STtailTDsznuDa
target  : 1-u⁻¹*sz.Wn:ℕ^d*|1-u|⁻¹*J^2*STtailTDsznuDa
```
Identical. Left side: target `‖STELKLKM sz n E u M σ a‖`; consumer `STELKLK sz n E u σ a ω := STELKLKM sz n E u (sz.seqHflow n u ω) σ a` (`Step5Pins.lean:147`), so instantiating `M := seqHflow n u ω` gives the consumer's left side. Quantifiers: `∀ sz n E u D Λ K₀ J M, E2Hyp … → ∀ σ a` — every `σ ∈ {±}²`, `a ∈ (Z_L^d)²`, as in `3_5:2317`. `STtailTD` = `tailTD d W u D (zdistInf …)`, `tailTD = ((W^d|1−u|)⁻¹)² e^{-√r} + W^{-D}` (`Defs/Tail.lean:173`) = `def_WTuD` (`3_5:2297`). Deterministic at one time `u` (§29 (5)). The `≺` is replaced by the explicit `lossE2 = 10¹²(1600d⁴)^d K₀²Λ⁶(1+log(L^dW^{2d}))⁴(1+log W)³e^{8(log W)^{3/4}}`: polylog in `N`, `W` times `e^{O((log W)^{3/4})}` = `W^{o(1)}`, so admissible as a `≺` loss; `d`-dependent leading constant is covered by T2164d.
**Verdict: PASS.**

## 3. Target 1 `lossE2`, `E2Hyp` (explicit premises replacing `goodSet`)
Ticket's list vs `E2Hyp` conjuncts (`LemDecCalE.lean:69-92`, read directly):
| ticket item | `E2Hyp` conjunct | check |
|---|---|---|
| (e6) `|G_pq − δ_pq m| ≤ Λ M_u^{-1/4}` | `∀ x y, ‖Gres M (zt E u) true x y − δ·mE E‖ ≤ Λ (W^d(1−u))⁻¹^{1/4}` | = RBM2D clause 3 (`GoodSet.lean:54`, `llErrMat`) with `M_u=W^d(1−u)` |
| (e7)/(e8) GijGEX clause | `∀ p ≠ q, ‖Gres … p q‖² ≤ Λ·gexRHS … (STblk q) (STblk p)` | same orientation as merged `GijGEXPTSwap` (`Green/Pins.lean:283`) |
| (e9) averaged law, `(ℓ_u/ℓ_s)²` | `∀ σ a, ‖avgErr … σ a‖ ≤ Λ (W^d(1−u))⁻¹` | `ℓ_u=ℓ_s=1` since `ellT = min(max(lam/√|1−u|,1),L)` (`Defs/Params.lean:32`) `=1` under `lam² ≤ 1−u`; both σ (RBM2D: σ=+) — S5-09 obligation, observation |
| `J*_{u,D} ≤ W` | `1 ≤ J ∧ J ≤ W` | present (unused by the proofs here) |
| `𝒦` bound | `‖STKloop (+,−) (a,b)‖ ≤ K₀ (W^d(1−u))⁻¹` | RBM2D `Kpm ≤ K₀ M_u⁻¹` |
| (Kell*) | `(1/8)(log W)^{3/2}·ellT ≤ |a−b|_∞ → ‖STKloop‖ ≤ W^{-D}` | shape of `KellStarEv` (`Path/KellStar.lean:54`) |
| floor (C3), d form | `L^d W^{2d} ≤ W^D` | see §6 (M1) |
| `W ≥ e⁴` | `4 ≤ log W` | present |
| §29 (6) `1 ≤ L, 0<lam, lam² ≤ 1−u, |E|<2` | `3 ≤ L n` is the merged field `Sizes.three_le_L`; the others are conjuncts | present |
| control `J*` | `∀ σ a, ‖STLKM … σ a‖ ≤ J·STtailTD …` | = consumer hyp `Prec STLK2 ≤ Jst·STtailTD` (`STLKM = STLM − STKloop`, `Step2Defs.lean:68`) |
Additional conjuncts `3 ≤ d`, `0 ≤ u < 1`, `1 ≤ lam²W^d`, `M.IsHermitian`, `1 ≤ Λ, K₀` are explicit. No premise is inside a structure field except the merged `Sizes` fields (`three_le_L`, `W_pos`, `Defs/Sizes.lean:138-146`). RBM2D's `goodSet` clauses 2 (loopAbs) and 5 (GiiGEX) are not projected in the source (prove report (a) grep) and are dropped — weaker hypothesis, fine. The §29 (7) premise → `STIngR5` table is in the prove report (b), with three rows marked "missing" (M1–M3), as the ticket's checklist allows.
**Verdict: PASS.**

## 4. Target 2 (e1)–(e10)
Public names (grep of the branch file): `LemDecCalE_e1, _e1_rpow, _e2, _floor, _floor_A, _tailT_le_two_inv_sq, _tailT_mono_scale, _tailT_anti, _tailT_shift, _e4c, _lk_le, _loopPM_eq, _loopPM_le, _e6_err, _e6, _e7, _e8, _e9, _e10a_nat, _e10a, _e10b, _sum_zd_le, _exp_conv, _sum_tail_tail, _lk_const_le_lossE2`. Statements read: (e1) `W^d M_u⁻² = (1−u)⁻¹M_u⁻¹`; (e2) `1 ≤ M_u ≤ W^d`; (e6) `‖G_xy(σ)‖ ≤ 2Λ`; (e7) `|G_pq|² ≤ 9^d Λ (W^{-D} + J T(|[q]−[p]|−2))` for `|[q]−[p]|_∞ ≥ ℓ*/8+2`; (e8) `≤ Λ(9^d(K₀M_u⁻¹+2JM_u⁻²)+W^{-d})` and `≤ 2·9^dΛK₀M_u⁻¹(1+J/M_u)`; (e9) projection of (P-e9); (e10b) `#{|z|_∞ ≤ 1} ≤ 3^d`. `d`-dimensional counts `3^d`, `9^d` replace RBM2D's `5`, `25` (ticket item 1 asks to state it: done in the statements of (e7), (e8)). All hypotheses are `E2Hyp` plus explicit numeric ones. RBM2D names kept where the statement is unchanged in shape; renamings listed in the prove report (b) narrative.
Applicability at the instance (all compile, every hypothesis except e7's distance condition discharged by `LemDecCalE_inst`):
```
$ cat scratchpad/T2164/inst2.lean   (#check LemDecCalE_{e2,floor,tailT_le_two_inv_sq,loopPM_le,e6,e8,e9,e7} LemDecCalE_inst)
$ lake env lean scratchpad/T2164/inst2.lean > inst2.out; echo exit=$?; grep -c error inst2.out
exit=0
0
$ python3 (sz0: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6, Defs/Sizes.lean:260)
sz0 n=1: L=8 W=1024 max zdistInf=4 e7 threshold (log W)^1.5/8+2=4.281 satisfiable=False floor(D=8)=True lam^2W^3=64.0 logW=6.93
sz0 n=2: L=12 W=7776 max zdistInf=6 e7 threshold (log W)^1.5/8+2=5.352 satisfiable=True floor(D=8)=True lam^2W^3=216.0 logW=8.96
```
Observation (O1): the distance hypothesis of `LemDecCalE_e7` cannot hold at the `n = 1` data (`L = 8`), but it is satisfiable at `sz0 n = 2` together with every numeric premise of `LemDecCalE_e2Hyp_zero`; so (e7) is not vacuous. The ticket's "Instances to compile" names only `E2Hyp` and `lemDecCalE_lk`; (e1)–(e10) are supporting lemmas for S5-06..09.
**Verdict: PASS.**

## 5. Compiled nonempty instance
`LemDecCalE_inst : E2Hyp sz0 1 (1/2) 0 8 1 1 1 0` at `d = 3` (`L = 8`, `W = 1024`, `lam = 1/4096`, `N = 2^39`), proved through `LemDecCalE_e2Hyp_zero`, whose hypotheses are only numeric (`|E|<2`, `0<lam`, `lam² ≤ 1`, `1 ≤ lam²W^d`, `1 ≤ Λ, K₀`, `4 ≤ log W`, floor, `1 ≤ J ≤ W`). Each one is discharged at the concrete numbers (`log 1024 ≥ 4` via `Real.exp_one_lt_d9`, `8³·1024⁶ ≤ 1024⁸` by `norm_num`). The `example` at `LemDecCalE.lean:1444` applies `lemDecCalE_lk 3 sz0 1 (1/2) 0 8 1 1 1 0 LemDecCalE_inst` at `σ=(+,−)`, `a = (0, e₁)` (distinct points); the second `example` (`:1454`) proves the right side is `> 0`. `M = 0`, `u = 0` is the ticket's prescribed witness (RBM2D `:1190` redone). Nondegenerate: `N ≠ 0`, nonempty index, no `False` premise, moderate sizes. Built as part of the module (§1).
**PASS.**

## 6. Hidden hypotheses, cycles, consumer gaps
- No cycle: imports are `Induction/Step5Pins`, `Green/Pins`, `Path/KellStar`, `Mathlib.Analysis.PSeries` (all merged on `main`); no pin of a later gate is assumed.
- External hypotheses: none (the paper omits the proof; DECISIONS §5 makes it internal, and the file proves it).
- (M1) floor `L^dW^{2d} ≤ W^D` is stronger than the paper's "`W^D ≥ N`" (`3_5:2317`), and stronger than the hypothesis `size ≤ W^D` of `STLemDecCalEConcl` (`Step5Pins.lean:163`). My check: the floor term `W^d J² Σ_x W^{-2D} = W^d J² L^d W^{-2D}` must be bounded by `loss · W^d M_u⁻² J² W^{-D}`, i.e. `L^d W^{2d}(1−u)² ≤ loss·W^D`. With only `W^D ≥ N` this fails by `W^d` when `1−u ≍ 1`. So the stronger premise is needed for this crude bound, and `T2164a` covers it. S5-09 cannot discharge it from the current consumer pin. The ticket's §29 (7) routes this to the dispatcher before S5-09.
- (M2) the GijGEX clause and (M3) `J ≤ W` have no `STIngR5` source (prove report grep count 0). Both are premises the ticket itself requires in `E2Hyp`, and both are routed to the dispatcher before S5-09.
These are statement-level facts for downstream tickets. They are not defects of the T2164 targets, since the ticket pins these premises.

## 7. Paper-delta coverage
| Lean/paper difference | candidate |
|---|---|
| floor `L^dW^{2d} ≤ W^D` vs paper `W^D ≥ N` | T2164a |
| neighbour pairs `9^d` (`zdistInf ≤ 1`) vs portmap `(1+2d)²` | T2164b |
| `M_u = W^d(1−u)` (no `Im m`, `ℓ_u = 1`); single time `u`, no `s, v` | T2164c |
| explicit loss with `(1600d⁴)^d`, `S_d = (1+1536d⁴)^d` in place of `≺` | T2164d |
| `goodSet` replaced by explicit premises (Hermitian, P-e6, P-e7/8, P-e9) | design of the ticket (target 1); stated in the file header and in T2164c/report (b) |
Every difference I found is covered. Observation (O2): the (P-e9) premise is quantified over both `σ` (RBM2D: `σ = +` only). This is a slightly stronger premise, not a paper difference, and S5-09 inherits it.

## 8. Observations (no RETURN)
- (O1) `LemDecCalE_e7` is vacuous at the `n = 1` instance data and non-vacuous at `sz0 n = 2` (§4 script).
- (O2) (P-e9) is stated for both σ.
- (O3) The prove report's (a) exponent table uses the exact `S_3 = 3.687e5`, but the file proves `S_d ≤ (1+1536d⁴)^d`. The report notes this deviation in (b), and it changes no statement.

## Verdicts
- Target 1 (`lossE2`, `E2Hyp`): **PASS**
- Target 2 ((e1)–(e10)): **PASS**
- Target 3 (`lemDecCalE_lk`): **PASS**
- Ticket T2164: **PASS**. For the dispatcher before S5-09, not blocking this merge: M1 (floor vs `size ≤ W^D` in `STLemDecCalEConcl`), M2 (GijGEX source) and M3 (`J ≤ W` source).
