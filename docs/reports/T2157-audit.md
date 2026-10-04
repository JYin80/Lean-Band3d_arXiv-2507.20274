Auditor model: claude-opus-5-5

# T2157 audit (round 1): S5-22b `Evolution/MeanFar`, the mean part of `f^{far}`
Time: Sun Oct  4 21:17:01 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2157-audit1`, detached at `4e072ee` (t/T2157).
The check file `docs/tickets/checks/T2157-check.lean` holds `#check` lines only (no pinned statement text). Target 1 is "drafted by the preflight, then pinned", so it is checked against the ticket's mathematics, the preflight design (a)(i')(3) and (a′), and `3_5:2192-2212`. Target 2 is checked by script against `STCltFarConcl`.

## 1. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Evolution.MeanFar   (audit worktree)
✔ [3779/3779] Built RBM3D.Evolution.MeanFar (34s)
Build completed successfully (3779 jobs).
$ grep "^warning: RBM3D/Evolution/MeanFar" build.log | wc -l
       0
$ lake env lean ax.lean
'RBM.Gauss.Sizes.meanFar_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_T1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_T2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stMeanFar' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Evolution/MeanFar.lean | wc -l
       0
$ git diff --name-status main...t/T2157
A	RBM3D/Evolution/MeanFar.lean
$ git grep -n -E "meanFar_|STMeanFar|stMeanFar" main -- RBM3D RBM3D.lean | wc -l
       0
```
The only file changed is the sole writable file (new). No frozen signature is touched. Imports: `Evolution.ExpInv`, `Propagator.Prop5Hold`, `Propagator.Prop6Hold` (all merged), and `Mathlib.NumberTheory.Harmonic.Bounds`; `RBM3D` is not imported. No registry line is needed: `STMeanFar` is proved by `stMeanFar`.

## 2. Target 1: deterministic core `meanFar_core` (lines 666-681) + adapters `meanFar_T1`, `meanFar_T2`
Statement (from the file): for `3 ≤ d`, `T : Zd d L → ℂ` and `B` with `hBtr : B (a+c) (b+c) = B a b` and `hBsym : B a b = B b a`, together with
- `hT1 : ‖T x‖ ≤ K₁/(|x|_∞+1)^(d-2)`,
- `hT2 : |r|₁ ≤ w₁ → ρ < |a|_∞ → ‖T(a+r)+T(a-r)-2T a‖ ≤ K₂|r|₁²/(|a|_∞+1)^d`,
- `hB1 : |x|₁ ≤ w₁ → ‖B 0 x‖ ≤ K/(|x|_∞+1)^(d-2)` and `hB2 : w₁ < |x|₁ → ‖B 0 x‖ ≤ K'`,
- and a far set `S` (`ρ < |b-a₀|_∞ ∧ ρ < |b-a₁|_∞`),

the conclusion is
`‖Σ_{b₁∈S} Σ_{b₂} T(b₁-a₀) B b₁ b₂ (T(a₁-b₂) - T(a₁-b₁))‖ ≤ Cd(d) K₁K₂K (1+log(L+1)) (w₁+1)⁴/(|a₀-a₁|_∞+1)^(d-2) + 2K₁²K'L^{2d}`.

Comparison with the ticket and the paper:
- **Kernel hypotheses and summand.** The invariances, the window decay `K` and the crude bound `K'` beyond the window are as in the ticket. The summand is the ticket's bilinear form without the scalar `(1-s)²`, with `Θ_{xy} = T(y-x)` (`meanFar_Theta_shift`, property 2). The sum `Σ*` is any `S` inside the far set, which is more general than the ticket's set.
- **Constant.** `Cd = meanFar_Cd d` depends on `d` only, as the ticket requires. `K₁` and `K₂` carry `C₅/g²` and `C₇/g²` (`meanFar_T1`, `meanFar_T2`), so after the caller multiplies by `(1-s)²` the form is `C K (1-s)²g^{-4}(w₁+1)⁴(1+log(L+1))`.
- **Loss differences from the ticket's literal `ℓ_s⁴`.** The Lean bound has `(w₁+1)⁴` with `w₁ = d(log W)³ℓ_s`, which is a factor `(log W)^{12}`, and a factor `1+log(L+1)`. The `(log W)^{12}` is the paper's own `|r|² ≤ ((log W)³ℓ_s)²` and window volume, hidden in `≺` at `3_5:2209`. The `1+log(L+1)` comes from the critical sum `Σ_b(|b-a₂|+1)^{-d}`. Both are `≤ N^τ`, and the final `(eq:boundEfar)` form in target 2 is unchanged. Both differences are proposed as `T2157a`. The ticket's literal "`C K (1-s)²ilambda^{-4}ℓ_s⁴`" is not attainable without such factors (preflight (a) row 6, script). I accept this as the preflight-pinned form allowed by the ticket.
- **Window norm.** The window is in `ℓ¹`, while the ticket wrote `|b₁-b₂|_∞ ≤ w`. The caller uses `w₁ = d·w`. This is proposed as `T2157b`.
- **`(prop:BD2)` condition.** `meanFar_T2` covers `|r| ≤ c|a|` with `c = 1/2` through `2w₁ ≤ ⌊ρ⌋₊+1`, so the ticket's stop condition does not trigger.
- **Denominator.** The core's `(|a₀-a₁|+1)^(d-2)` is at least `|a₀-a₁|^(d-2)+1`, so the core is no weaker than the paper's form. Target 2 states the paper's form.

Vacuity, hidden hypotheses, cycles: there is no structure argument; every hypothesis is in the signature. `K₁ ≥ 0` and `K ≥ 0` are derived, not assumed. `hT1` and `hT2` are discharged at `Θ` by `meanFar_T1`/`meanFar_T2` from the proved `prop5Decay_holds`/`prop7Diff2_holds`, with no external hypothesis.
**Verdict: PASS.**

## 3. Target 2: `stMeanFar : STMeanFar d` (lines 2088-2106) and `meanFar_eventually` (1980)
The pin is `STMeanFar d := STIngR5 d STReg5I (STMeanFarConcl …)`, which is the ticket's form ("`Prec`/deterministic form, as S5-25 needs").
```
$ python3 cmp.py        # STMeanFarConcl vs merged STCltFarConcl (Step5Pins.lean:385), whitespace-normalised
U identical: True
zeta identical: True
xi Clt : (fun n p ω => ‖STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω‖)
xi Mean: (fun n p _ => ‖∫ ω, STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω ∂(sz.seqP)‖)
```
- **Index set, bound, regime, `σ₁ ≠ σ₂`.** The index set and the bound `A^{-6/5}/(|a₁-a₂|^{d-2}+1)` (`STAI = lam²W^d`) are identical to S5-25's input. `σ₁ ≠ σ₂` sits in `U`. The regime is `STReg5I`, the paper's case (i).
- **`meanFar_eventually`.** It is a stronger deterministic form: for every `σ` and `a`, eventually, `‖∫ STfFar‖ ≤ N^τ·(…)`. This is proposed as `T2157c`.
- **Integral not vacuous.** `meanFar_integrable_L` gives `Lloop` integrable (measurable, `‖·‖ ≤ η^{-2}`), and `meanFar_B_eq` uses it. So `∫ STfFar` is the genuine expectation, not Lean's junk value 0.
- **`≺ ⟹ 𝔼`.** This goes through the a.s. envelope plus the bad event of `STGdecayW` (`meanFar_bad_le`, `meanFar_B_bound`). It uses merged pins only, with no new moment input, and is proposed as `T2157d`.
- **Dependencies and cycles.**
  - The `𝔼𝓑` invariances come from merged `stExpInv_holds` and `Theta_apply_add_right_of_three_le`/`Theta_transpose_of_three_le`.
  - `STGdecayW` is taken from `hStep2.2.2`, the `STStep2Concl` premise of `STIngR5`.
  - Every dependency is imported from merged modules, so there is no cycle.
  - `STConStInd` and the other stochastic premises are unused; leaving them unused only makes the result stronger.
- **`Prec` is not vacuous.** `StochDomAt` requires `P(badSetAt) ≤ N^{-D}`. For the deterministic `ξ`, `badSetAt = ∅` is proved from `meanFar_eventually`.

**Verdict: PASS.**

## 4. Compiled nonempty instances (in the file; elaborated by the build above, 0 warnings/errors)
- **`meanFar_core`, nonzero `B` (example at 2194).**
  - Data: `d = 3`, `L = 5`, `a = (0, e₁)`, `ρ = w₁ = 1`, `K = 1`, `K' = 0`.
  - `T = Θ_{9/10}(0,·)` at `g = 1/2` with `m = i`.
  - `B(a,b) = 1/(|a-b|_∞+1)` on `|a-b|₁ ≤ 1`, else 0.
  - All of `hBtr`, `hBsym`, `hT1`, `hT2`, `hB1`, `hB2`, `hS` are discharged. `hT1` and `hT2` come from the proved pins via `meanFar_inst_T`; `K₁` and `K₂` are existential only because `C₅` and `C₇` are.
  - Nondegeneracy (example at 2220): the far set contains `(2,2,2)`, `B(0,0) = 1`, `B(0,e₁) = 1/2`, and `|e₁|₁ = 1 ≤ w₁`.
- **`meanFar_core`, `B = 0` (2244).** Same data, `K = K' = 0`.
- **`stMeanFar` at `d = 3` (2266).**
  - Applied through merged `Step5Inst.inst_ing5` at `(szCL, zCL, sCL, tCL)`.
  - Discharged: the flow, `0 ≤ s < t ≤ lemT`, `STReg5I` and `STConStInd`.
  - Kept as hypotheses: the stochastic premises of other gates (`STKbound` … `STStep2Concl`, `STLKU`), as allowed.
  - The index set is nonempty for every `n` (2275, `szCL_cltFar_index_nonempty`).
- **`meanFar_eventually` at `szCL` (2290).** Only `STGdecayW` is kept as a hypothesis. The flow, `(eq:WO)`, bandwidth, regime and `|E| ≤ 2-κ` are discharged.

## 5. Paper-delta coverage
The candidates `T2157a`–`T2157d` are in the prove report (d), lines 225-228:
- `T2157a`: the `(log W)^{12}` and `log L` losses;
- `T2157b`: the `ℓ¹` window and the `⌊ρ⌋₊` premise;
- `T2157c`: valid for all `σ` and `a`;
- `T2157d`: the `≺ ⟹ 𝔼` route.

`grep -c T2157 docs/paper-deltas.md` gives 0: the candidates are not yet numbered, which is the dispatcher's task. Every Lean/paper difference found in §2–§3 is covered.

## 6. Observations (no effect on verdict)
- O1. The `stMeanFar` and `meanFar_eventually` instances use `szCL` (`N ≈ 1.9e43` at `n = 0`), not the ticket's suggested `sz0`/T2039 data. This size is forced by the index set (`(log W)⁵ℓ_s ≤ ℓ_t`, `ρ < L/2`); it is the merged data of `inst_cltFar`, and the hypotheses do not hold "only because a quantity is huge".
- O2. File length is 2311 lines against the ticket estimate of about 600 (process note only).
- O3. The core's denominator `(|a₀-a₁|_∞+1)^{d-2}` differs in shape from the paper's `|a₁-a₂|^{d-2}+1` but is stronger. It is noted in (a′)4 and needs no delta.

## Verdict
| target | verdict |
|---|---|
| `meanFar_core` (+ `meanFar_T1`, `meanFar_T2`) | PASS |
| `stMeanFar` (+ `meanFar_eventually`) | PASS |

Ticket T2157: **PASS**. No dispatcher sign-off needed. Scratch scripts: `scratchpad/T2157/{ax.lean,cmp.py,build.log}`.
