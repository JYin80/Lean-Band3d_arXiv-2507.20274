Auditor model: claude-opus-5-5

# T2385 (BA-K08a) — 1a-audit round 2 (design gate, K08a + K08b), Sat Oct 10 12:52:14 UTC 2026

Inputs: ticket `docs/tickets/T2385.md`; sections (a), (a+), (d) of `docs/reports/T2385-prove.md` (168 lines; (a) = lines 3-65,
header "repair round: statements of (iv) written in full", 12:49:17 UTC). Round 1 RETURNed on D1 (`baK_sumAll_eq_layers` false
at `W = 0`, missing `3 ≤ L`, `0 < κ`, `0 < g`) and D2 (`..` elisions in `baSigmaPi_total_le`, `baSig_signed_sum_unif`).
Branch: `git diff --stat main...t/T2385` → empty (no Lean yet, as expected at 1a).
Scripts: the prover's `$S/T2385/*.py` copied to `$S/T2385/audit2/` and rerun there unchanged (`$S` = session scratchpad).

## 1. Numerics rerun (ticket (ii), binding)
`python3 inst_P.py | tail -4` (flow point of (3,4,10), n=4, σ=(+,−,+,−)): identical to the report, e.g.
```
t=0.5: #layers=1 nonzero slice entries=262144/262144  |signed slice sum|=1.0583e+00  /(1-t)=2.1165  V1: |(1-t)^n sum_a K - Stot|=7.2e-12  slice indep of x: 8.9e-16  abs weighted Q=2/(g0^2+1-t)=14.9029  Ward-sum |q^-1 sum_a K| eta^(n-1)=0.3730
t=0.999: #layers=1 nonzero slice entries=262144/262144  |signed slice sum|=1.5913e-03  /(1-t)=1.5913  V1: |(1-t)^n sum_a K - Stot|=1.2e-12  slice indep of x: 2.9e-15  abs weighted Q=2/(g0^2+1-t)=12.0576  Ward-sum |q^-1 sum_a K| eta^(n-1)=0.2805
```
`python3 chk_stmts.py | tail -12` (new in the repair; checks the (iv) statements' hypotheses and the `W` rows):
```
hyps: 3<=d True  3<=n True  alt True  3<=L True  0<kappa True  0<g0 True  g0<=Lam True  kappa<=Im m True  BASelf resid<1e-12 True
t=0.5: baSigmaPi_slice  |L^d*slice - total| = 1.7e-13
   W=0: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +0.000000e+00+0.0e+00j   rhs=sum_pi sum_delta Sigma = +6.772809e+01-4.9e-47j   |lhs-rhs|=6.8e+01
   W=1: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +6.772809e+01-5.6e-45j   rhs=sum_pi sum_delta Sigma = +6.772809e+01-4.9e-47j   |lhs-rhs|=7.2e-12
   W=2: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +6.772809e+01-5.6e-45j   rhs=sum_pi sum_delta Sigma = +6.772809e+01-4.9e-47j   |lhs-rhs|=7.2e-12
   T1 ratio |sum_a K|/(L^d (W^d eta)^-(n-1)) at W=1 = 0.3730;  T2 ratio |total|/(L^d (1-t)) = 2.1165;  slice ratio |slice|/(1-t) = 2.1165
t=0.999: baSigmaPi_slice  |L^d*slice - total| = 7.8e-14
   W=0: ... |lhs-rhs|=1.0e-01     W=1: ... |lhs-rhs|=1.2e-12     W=2: ... |lhs-rhs|=1.2e-12
   T1 ratio |sum_a K|/(L^d (W^d eta)^-(n-1)) at W=1 = 0.2805;  T2 ratio |total|/(L^d (1-t)) = 1.5913;  slice ratio |slice|/(1-t) = 1.5913
```
`python3 table.py 3 3 4 "1/64,1,10" 1e-1,1e-5,0 1,2,4` and `... "1/256" 1e-5,0 1,2,4`:
```
d3L3n4    g=0.015625  Im m=0.988 1-t=1e-01  signed=  0.5391 Q1=    0.567 Q2=    0.592 Q4=    0.749 c0=  0.543
d3L3n4    g=0.015625  Im m=0.988 1-t=1e-05  signed=  0.5122 Q1=    9.462 Q2=   16.137 Q4=   58.404 c0=  2.969
d3L3n4    g=0.015625  Im m=0.988 1-t=0e+00  signed= 7.0e-16* Q1=    9.828 Q2=   16.777 Q4=   60.773 c0=  3.070
d3L3n4    g=1         Im m=0.670 1-t=1e-01  signed=  1.1703 Q1=   35.363 Q2=  135.750 Q4= 2058.781 c0=  0.082
d3L3n4    g=1         Im m=0.670 1-t=1e-05  signed=  1.1152 Q1=   38.194 Q2=  146.711 Q4= 2226.490 c0=  0.080
d3L3n4    g=1         Im m=0.670 1-t=0e+00  signed= 3.4e-16* Q1=   38.194 Q2=  146.712 Q4= 2226.509 c0=  0.080
d3L3n4    g=10        Im m=0.650 1-t=1e-01  signed=  1.2456 Q1=    0.303 Q2=    1.166 Q4=   17.756 c0=  0.001
d3L3n4    g=10        Im m=0.650 1-t=1e-05  signed=  1.1836 Q1=    0.297 Q2=    1.145 Q4=   17.457 c0=  0.001
d3L3n4    g=10        Im m=0.650 1-t=0e+00  signed= 2.2e-15* Q1=    0.297 Q2=    1.145 Q4=   17.457 c0=  0.001
d3L3n4    g=0.0039062 Im m=0.989 1-t=1e-05  signed=  0.5116 Q1=    5.836 Q2=    9.620 Q4=   32.405 c0=  2.058
d3L3n4    g=0.0039062 Im m=0.989 1-t=0e+00  signed= 9.6e-16* Q1=    9.325 Q2=   15.588 Q4=   53.304 c0=  3.072
```
`python3 verify_alg.py | tail -6; python3 verify8.py | tail -3` (identities V1–V3 behind A2, A4, A5):
```
V1  (1-t)^n sum_a sum_F Gamma  = (0.8137970963817787-7.450580596923818e-15j)
V1  sum_pi Stot(pi)            = (0.8137970963816943-1.9133999940024182e-15j)
V2  Stot(sigma6,{(0,3)})       = (0.5072104712297367-7.580741590018647e-16j)
V2  t/(1-t) S4 S4 / q          = (0.5072104712297313-3.315054017627938e-17j)
V3  Stot(empty) = (-0.7078343173075097-1.734723475976807e-16j)  (1-t)^n sumK - sum_{pi!=0} Stot = (-0.7078343173074253-5.710652950519081e-15j)
V2 two disjoint chords: (0.4409776279254281+5.277028813921447e-15j) (0.44097762792542594-6.527713765870078e-16j)
V2 nested chords      : (0.4409776279254165-1.1931428067768479e-14j) (0.4409776279254262-7.975006733937332e-16j)
```
Reading: every row of the report reproduces digit for digit. Signed ratio bounded as `1−t → 0` at `g = 1/64, 1, 10` and the
signed sum is ≤ 2.2e-15 at `t = 1`; weighted ratios plateau in `t ↑ 1` and do not grow as `g ↓` (1/64 → 1/256: Q1 9.83 → 9.33,
Q4 60.8 → 53.3). No REQ trigger (2051 K-b). The design-data reruns of round 1 (`aud_design.py`: 1.0208 at q=5, n=4) stand;
the repair changed no numerics script except adding `chk_stmts.py` (`cmp` of the other 12 scripts vs round-1 copies: equal).

## 2. Written argument (ticket (i))
Section (a+)(i) is unchanged from round 1 except the `W`/range hypotheses; round 1 checked A1–A5 and B1–B3 against the merged
signatures (`baSigmaPi_shift` KMolecule:204, `baK_eq_sum_Kpi` :133, `baSigmaPi_cut` :313, `baK_ward` KWard:305,
`BATheta_row_sum_pm` KBase:381, `baPure_loop` KPure:813, `baSig_decay` :632). Re-read this round:
- `baSigmaPi_cut` (KMolecule:313-320): hypotheses `2 ≤ n`, `F₀ ∈ TSP n`, `KLFlong F₀ σ = π`, `J ∈ π`, innermost; no hypothesis
  on `M` or `t` — A4 as written.
- `baPure_loop` (KPure:813-818): `∃ C c` before `L W g E m t`, `0 < g ≤ Λ`, `BAReal`, `t < 1`, bound `C·(W^{-d})^{n−1}e^{-c·maxDist}`;
  with `η = (1−t)·Im m ≤ 1` this gives A3's base `≤ B L^d (W^dη)^{-(n−1)}`: correct.
- `baK_ward` RHS uses `(PropSpin m true).im`; `example (m : ℂ) : PropSpin m true = m := by simp [PropSpin]` compiles (§3),
  so `baK_sumAll_le`'s `m.im` is the same `η`. Exponent count `n − (n−1) = 1` (A5) and cut count `−1+1+1 = 1` (A4): correct.
No external input, no hypothesis left open, no circular dependency (all inputs merged on `main`).

## 3. Public statements fixed by the 1a (target 1; round-1 D1, D2)
The six K08a statements of (iv) (lines 147-158) were copied verbatim into `$S/T2385/audit2/Stmts.lean` as `Prop`-valued
`def`s (`S(d,L,g,E,m)` expanded to `BAMsigma d L (BAMB d L g (E : ℂ) m)`, as (iv) prescribes), plus two fit checks against
the K-b pin and `BASig`. Command: `lake env lean $S/T2385/audit2/Stmts.lean` (main worktree; `t/T2385` = `main` base):
```
... warning: Variable name `hshift` is not explicitly referenced.   [only unused-binder linter warnings: binder names in Prop defs]
PropSpin : ℂ → Bool → ℂ
exit=0
```
Fit checks in the same file (compiled):
```
example ... (h : ∀ i σ, (∀ j, σ j ≠ σ (j + 1)) → ∀ r x, ‖∑ δ ∈ univ.filter (δ r = x), BASig d n L g E m t i σ δ‖ ≤ C * (1 - t i)) ...
  : ‖∑ δ ∈ ..., (BASig d n L g E m t) i σ δ‖ ≤ C * (1 - t i) := h i σ hσ r x     -- = signed clause of SigSumZeroAbs (KLIndStepA:1036)
example ... : BASig d n L g E m t i σ δ = BASigmaPi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ ∅ δ := rfl
example (m : ℂ) : PropSpin m true = m := by simp [PropSpin]
```
Per statement:
| statement | hypotheses / quantifiers | verdict |
|---|---|---|
| `baSigmaPi_slice` | any `M` with `hshift`; every `t σ π r x`; `NeZero L` | PASS (true by translation, numerics 1.7e-13) |
| `baK_sumAll_eq_layers` | `0<κ`, `0<g`, `3≤L`, `1≤W`, `BAReal`, `t∈Ico 0 1`, `3≤n`, alternation | PASS — D1 fixed (W=0 excluded; `chk_stmts` W=1,2 rows 7e-12) |
| `baK_sumAll_le` | `∃ B > 0` before `L W g E m t σ`; `3≤d`, `1≤n`, `0<Λ`, `0<κ`; `3≤L`, `1≤W`, `0<g≤Λ`, `BAReal`, `0≤t<1` | PASS (C1 uniform) |
| `baSigmaPi_total_le` | `∃ C > 0` before data; `3≤n`; `3≤L`, `0<g≤Λ`, `BAReal`, `0≤t<1`, alternation, `∀ π` | PASS — D2 fixed |
| `baSig_signed_sum_unif` | as above, slice `δ r = x`, layer `∅`, bound `C(1−t)` | PASS — D2 fixed |
| `baSig_signed_sum` | family form, hyps of `baSig_decay` with `ht1 : t i < 1`; conclusion = signed clause of `SigSumZeroAbs` | PASS |
Constants depend only on `(d, n, Λ, κ)` (no smallness of `g`, C1). The strict `t < 1`, `3 ≤ n` ranges match the consumers'
`ht1` (`KLIndStepB.lean:297, 362`) and the band instance `sigSumZeroAbs_band` (`KLIndStepA.lean:1091`, `3 ≤ n`). Not a pin
change: `SigSumZeroAbs` is untouched; the ranges are hypotheses of K08b's theorem.

## 4. Q4 line, split and plan (ticket (iii), (iv))
Q4: K08a 1000 / 1380 / 2060, K08b 720 / 990 / 1520, sum 1720 / 2370 / 3580 vs 4.8k (central 49 %, hi 75 %): below the line.
Stop line 2400 (`wc -l RBM3D/BA/KSumZeroA.lean`) above K08a hi 2060; checkpoints 800 / 1150 / 1800 (REQ at 1800 without the
instance). Split: K08a = the six statements above (one file), K08b = `baSig_nc_pointwise`, `baSig_weighted`, `baSig_sumZeroAbs`
in `BA/KSumZeroB.lean`. Met. No binding stop line hit.

## 5. Instance plan, paper deltas
Instance plan at `P` of (3,4), `Λ = 10`, `κ = P.m0.im`, n=4, `KLsigAlt 4`, `t = 1/2, 999/1000`, `W = 1`, `P.real`: every
deterministic hypothesis dischargeable at the data (`hyps:` line above); nondegenerate (262144/262144 nonzero slice entries, one
nonempty layer, signed sum 1.058 ≠ 0 at t=1/2). Paper-delta candidates `T2385a` (claim proved, TeX cites), `T2385b`
(`3 ≤ n`, `t < 1` ranges; `n = 2` gives slice sum 1), `T2385c` (uniform constants vs `≺`) cover every Lean/paper difference.

## Observations (no verdict effect)
- O1. The instance list of (iv) names `baSig_signed_sum_unif`, `baSigmaPi_total_le`, `baK_sumAll_le`, `baK_sumAll_eq_layers`,
  `baSigmaPi_slice` but not the family form `baSig_signed_sum`. It is an endpoint (the K-b-shaped conclusion), so stage 1b must
  add its own compiled instance (e.g. `ι = Unit`, `L = fun _ => 4`, `g = fun _ => P.g0`, `t = fun _ => 1/2`, σ = `KLsigAlt 4`);
  stage 2 will RETURN otherwise.
- O2. The `unusedVariables` warnings in `Stmts.lean` come from named binders inside `Prop` definitions in the scratch check;
  they do not concern the planned theorems.
- O3. Round-1 observations O1–O3 (the "required pin repair" wording; the design-data rerun; `∀ π` in `baSigmaPi_slice`) stand.

## Verdict
- (i) argument for both clauses: met. (ii) numerics: rerun, reproduced, no growth in `g ↓` or `t ↑ 1`; no REQ.
- (iii) Q4 line: met (49 % central). (iv) split, plan, public statements: met; D1, D2 of round 1 repaired; all six statements
  elaborate against merged `main`.
- No binding stop line hit. No dispatcher sign-off needed.

**PASS.**
