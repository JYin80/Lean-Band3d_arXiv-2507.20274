Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 12:49:17 UTC 2026 (repair round: statements of (iv) written in full)

Targets in mathematics (BA data `(d,L,g,E,m,t)`, `BAReal d L g κ E m`, `3 ≤ L`, `0 < g ≤ Λ`, `0 ≤ t < 1`, `M(σ) = BAMsigma (BAMB ..)`, `η_t = (1−t) Im m`, `𝒮(σ,π) := Σ_δ Σ^{(π)}(σ,δ)`):
- **T1** (Ward bound for sums of `𝒦`): `|Σ_{a∈Z^n} 𝒦^{(n)}_{t,σ,a}| ≤ B L^d (W^d η_t)^{-(n−1)}`, every `σ`, `n ≥ 1`.
- **T2** (signed sum-zero): `σ` cyclically alternating, `3 ≤ n` (so `n` even `≥ 4`), every layer `π`: `|𝒮(σ,π)| ≤ C L^d (1−t)`; hence `|Σ_{δ_r=x} BASig i σ δ| ≤ C (1−t)` for every root `r`, label `x`. `B`, `C` depend on `(d,n,Λ,κ)` only.
The design-gate items of the ticket (argument for both clauses, numerics, Q4 line, split) are in section (a+).

### (i) Exponent table
| # | quantity | value (instance) | constraint | slack |
|---|---|---|---|---|
| 1 | `d` | 3 | `3 ≤ d` (hyp. of `baPure_edge`, `baPure_loop`, `baSig_decay`) | 0 |
| 2 | `n` | 4, `σ = (+,−,+,−) = KLsigAlt 4` | `3 ≤ n`, `σ_j ≠ σ_{j+1}` cyclically ⇒ `n` even `≥ 4`; `n = 2` excluded: signed slice sum `= 1`, not `O(1−t)` (N0, (a+)) | 1 (n=4 is the least admissible) |
| 3 | `L` | 4 | `3 ≤ L` (row sums, `BATheta_row_sum_pm`) | 1 |
| 4 | `Λ` | 10 | `g ≤ Λ`; `g₀ = 4.672337` | 5.327663 |
| 5 | `κ` | `Im m₀ = 0.560680` | `κ ≤ Im m` (`BAReal`); `Im m ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`) so `η_t ≤ 1−t ≤ 1` | 0 below (κ = Im m₀), 0.4393 above |
| 6 | `t` | 1/2, 0.9, 0.99, 0.999 | `0 ≤ t < 1` strict (`Θ^{(+,−)}` has `(1−t)⁻¹`; `baK_ward` is on `[0,1)`) | `1−t` = 0.5, 0.1, 0.01, 0.001 |
| 7 | `W` | 1 (any `W ≥ 1`) | `hW : 1 ≤ W` is a hypothesis of `baK_sumAll_eq_layers` and `baK_sumAll_le`: `W^{(n−1)d}` cancels in `(W^d)^{n−1}(1−t)^n Σ_a 𝒦 = Σ_π 𝒮` only for `W ≠ 0` (at `W = 0` Lean's `0⁻¹ = 0` makes the left side `0`; script (ii-c)) | 0 (W=1 is the least) |
| 8 | power of `(1−t)` gained | `n − (n−1) = 1` (n=4: 4 − 3) | column sums give `(1−t)^{-n}`, Ward bound `(1−t)^{-(n−1)}`; clause needs 1 | 0 (tight) |
| 9 | cut recursion | `(1−t) L^d 𝒮(σ,π) = t 𝒮_in 𝒮_out`; `−1 + 1 + 1 = 1` | `|𝒮_in|,|𝒮_out| ≤ C L^d (1−t)` ⇒ `|𝒮(σ,π)| ≤ C_in C_out L^d (1−t)` (uses `t ≤ 1`) | 0 (tight) |
| 10 | sizes of a long chord `J=(i,j)` | `n_in = j−i+1`, `n_out = n−(j−i)+1`, `n_in + n_out = n+2` | `j−i ≥ 2` (diagonal) and `j−i ≤ n−2` (not the whole polygon) ⇒ `3 ≤ n_in, n_out ≤ n−1`: strong induction closes | 1 each side |
| 11 | layers | `≤ 2^{n²}`; n=4: `TSP 4 = {∅,{(0,2)},{(1,3)}}`, both chords short ⇒ only `π = ∅` nonempty; n=6: 4 layers (V1) | finite | — |
| 12 | Ward step factor | `|(2iW^dη)⁻¹|·2 = (W^dη)⁻¹` | `B_n = max(B_{n−1}, B_n^{pure})`: no growth per level | 0 |
| 13 | pure base `n ≥ 3` | `|𝒦(a)| ≤ C W^{-(n−1)d} e^{-c maxDist a}`, `c = r/4`; `Σ_a e^{-c maxDist} ≤ L^d expC(d−2,c/n)^{n−1}` | `W^{-(n−1)d} ≤ (W^dη)^{-(n−1)}` needs `η ≤ 1` (row 5): at t=1/2 `η = 0.2803` | 0.7197 |
| 14 | `g²` gain (K08b) | exponent 2 | one off-diagonal chord (`Θ^{(s,s)}_{xy} ≤ C g² e^{-c|x−y|}`, `baProp5s_of_real`) or two off-diagonal `M`-edges of one node (`|M_{xy}|² = K_{xy} ≤ A g² e^{-2c|x−y|}`, `BAK_off_le`) | 0 |
| 15 | weight `Q` (K08b) | `Q ≤ 2(d−1) = 4` | `C_Q = 2^Q (1 + Q!/(c/2)^Q)` finite for every `Q` | any `Q` |

### (ii) One concrete nondegenerate instance
Flow point of `(d,L,g) = (3,4,10)` (`wI = 6i/5`, `mS = L^{-3} tr(gΨ − wI)⁻¹`, `zS = wI − mS`, `t₀ = Im mS/(Im mS + Im zS)`, `E = BAflowE`, `m₀ = mS/√t₀`, `g₀ = √t₀ g`; `MFixedPoint.lean:849-893`), `Λ = 10`, `κ = Im m₀`, `n = 4`, `σ = (+,−,+,−)`, `W = 1`, `t ∈ {1/2, 0.9, 0.99, 0.999}`. The script builds `M = (g₀Ψ − E − m₀)⁻¹` on `Z_4³` (64 sites), the cactus values of the three trees of `TSP 4`, and checks the identity of `(1−t)^n Σ_a 𝒦` against `𝒮`.
Command: `cd $S/T2385 && python3 inst_P.py` (`S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad`). Output verbatim:
```
flow point (d,L,g)=(3,4,10): t0=0.218307 g0=4.672337 E=-0.000000 m0=0.000000+0.560680j  kappa=Im m0=0.560680  |m0|=0.560680
BASelf residual |m0 - L^-3 tr(g0 Psi - E - m0)^-1| = 3.33e-16;  Lambda=10 >= g0: True;  kappa<=|m0|<=1: True
Ward row sum sum_b |M_0b|^2 = 1.000000000000
t=0.5: #layers=1 nonzero slice entries=262144/262144  |signed slice sum|=1.0583e+00  /(1-t)=2.1165  V1: |(1-t)^n sum_a K - Stot|=7.2e-12  slice indep of x: 8.9e-16  abs weighted Q=2/(g0^2+1-t)=14.9029  Ward-sum |q^-1 sum_a K| eta^(n-1)=0.3730
t=0.9: #layers=1 nonzero slice entries=262144/262144  |signed slice sum|=1.6737e-01  /(1-t)=1.6737  V1: |(1-t)^n sum_a K - Stot|=7.7e-12  slice indep of x: 2.4e-15  abs weighted Q=2/(g0^2+1-t)=12.5257  Ward-sum |q^-1 sum_a K| eta^(n-1)=0.2950
t=0.99: #layers=1 nonzero slice entries=262144/262144  |signed slice sum|=1.5985e-02  /(1-t)=1.5985  V1: |(1-t)^n sum_a K - Stot|=6.3e-12  slice indep of x: 3.3e-15  abs weighted Q=2/(g0^2+1-t)=12.0986  Ward-sum |q^-1 sum_a K| eta^(n-1)=0.2817
t=0.999: #layers=1 nonzero slice entries=262144/262144  |signed slice sum|=1.5913e-03  /(1-t)=1.5913  V1: |(1-t)^n sum_a K - Stot|=1.2e-12  slice indep of x: 2.9e-15  abs weighted Q=2/(g0^2+1-t)=12.0576  Ward-sum |q^-1 sum_a K| eta^(n-1)=0.2805
```
(ii-c) Check of the statements as written in (iv) (all hypotheses of `baSigmaPi_slice`, `baK_sumAll_eq_layers`, `baK_sumAll_le`, `baSigmaPi_total_le`, `baSig_signed_sum_unif` at the instance; the `W` rows use the formula of `baK_eq_sum_Kpi`, `K = ((W^d)⁻¹)^{n−1} Σ_π K^{(π)}` with `0⁻¹ = 0`, applied to the computed `Σ_a Σ_π K^{(π)}`). Command: `cd $S/T2385 && python3 chk_stmts.py | tail -12`. Output verbatim:
```
hyps: 3<=d True  3<=n True  alt True  3<=L True  0<kappa True  0<g0 True  g0<=Lam True  kappa<=Im m True  BASelf resid<1e-12 True
t=0.5: baSigmaPi_slice  |L^d*slice - total| = 1.7e-13
   W=0: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +0.000000e+00+0.0e+00j   rhs=sum_pi sum_delta Sigma = +6.772809e+01-4.9e-47j   |lhs-rhs|=6.8e+01
   W=1: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +6.772809e+01-5.6e-45j   rhs=sum_pi sum_delta Sigma = +6.772809e+01-4.9e-47j   |lhs-rhs|=7.2e-12
   W=2: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +6.772809e+01-5.6e-45j   rhs=sum_pi sum_delta Sigma = +6.772809e+01-4.9e-47j   |lhs-rhs|=7.2e-12
   T1 ratio |sum_a K|/(L^d (W^d eta)^-(n-1)) at W=1 = 0.3730;  T2 ratio |total|/(L^d (1-t)) = 2.1165;  slice ratio |slice|/(1-t) = 2.1165
t=0.999: baSigmaPi_slice  |L^d*slice - total| = 7.8e-14
   W=0: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +0.000000e+00+0.0e+00j   rhs=sum_pi sum_delta Sigma = +1.018439e-01-2.6e-46j   |lhs-rhs|=1.0e-01
   W=1: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +1.018439e-01+0.0e+00j   rhs=sum_pi sum_delta Sigma = +1.018439e-01-2.6e-46j   |lhs-rhs|=1.2e-12
   W=2: lhs=(W^d)^(n-1)(1-t)^n sum_a K = +1.018439e-01+0.0e+00j   rhs=sum_pi sum_delta Sigma = +1.018439e-01-2.6e-46j   |lhs-rhs|=1.2e-12
   T1 ratio |sum_a K|/(L^d (W^d eta)^-(n-1)) at W=1 = 0.2805;  T2 ratio |total|/(L^d (1-t)) = 1.5913;  slice ratio |slice|/(1-t) = 1.5913
```
The `W = 0` rows show the identity fails there (`|lhs−rhs| = 68`), hence `hW : 1 ≤ W`; the other added hypotheses (`3 ≤ L`, `0 < κ`, `0 < g`) hold at the instance (`hyps` line). The numerics of (a+)(ii) are unchanged by the repair: they compute `Σ^{(π)}` and cactus values, which contain no `W`; the instance of (ii) has `W = 1`, `L = 4`, `g₀ > 0`, `κ = Im m₀ > 0`.
Hypothesis checklist: `3 ≤ d` (3), `3 ≤ n` and alternation (4, `KLsigAlt 4`), `3 ≤ L` (4), `0 < g ≤ Λ` (4.672 ≤ 10), `BAReal` (residual 3.3e-16, Ward row sum 1; in Lean: merged `P.real`, `MFixedPoint.lean:893`), `κ ≤ Im m` (equality), `0 ≤ t < 1`, `1 ≤ W`. No `N = 0`, empty index, collapsed window: all 262144 slice entries are nonzero, the signed sum is nonzero for `t < 1` (1.058 at `t = 1/2`), the slice sum is independent of `x`.
External hypotheses: none. Every input is a merged theorem (`baK_ward`, `baKsolve`, `baTreeRep`, `baKsol_two`, `BAKsol_rotate/translate`, `baPure_loop`, `baSig_decay`, `baSigmaPi_cut`, `baK_eq_sum_Kpi`, `BATheta_row_sum_pm`); no pin stays a hypothesis, so no limit computation (TEAM §8 l.14) is owed.

### Verdict
- T1 Ward bound for sums of `𝒦`: **PASS** (induction on `n` from `baK_ward`; base cases from merged `baPure_loop`, `baKsol_two`).
- T2 signed sum-zero: **PASS** (identity of V1, recursion V2, Ward bound; no unproved fact, no external input).
- Instances at the flow point (ticket target 2): **PASS** (hypotheses all hold at once, above).
- K08b items (design gate): **PASS** (argument in (a+); numerics show no growth in `g ↓` or `t ↑ 1`).
- Required pin repair (an amend, inside the domain): `SigSumZeroAbs` (`KLIndStepA.lean:1036`) has no `n` or `t` range; it is false at `n = 2` (N0), so K08b's `SigSumZeroAbs d n L g t (BASig d n L g E m t)` carries `3 ≤ n` and `t i < 1`, as `sigSumZeroAbs_band` (`KLIndStepA.lean:1091`) and its consumers (`KLIndStepB.lean:299, 364`).

## (a+) Design gate: ticket stage-1a items (i)–(iv), for K08a and K08b together

### (i) The complete argument (inputs are paper-internal; the TeX only cites [YY_25 L3.10], [RBSO1D L4.29, Claim 4.30] at `A:731-734`)
Notation `K^{(n)} = BAKsol`, `K^{(π)} = BAKpi`, `Σ^{(π)} = BASigmaPi`, `T_n(σ) = Σ_{a∈Z^n} K^{(n)}(σ,a)`, `σ` cyclically alternating (each leaf pair and each long chord is `(+,−)` or `(−,+)`).
**Signed clause (K08a).**
- **A1 (slice).** `baSigmaPi_shift` (`KMolecule.lean:204`) gives `Σ_{δ_r=x} Σ^{(π)} = 𝒮(σ,π)/L^d` for every `r`, `x`, `π` (twin of `SumZero_sum_slice`; no closed form). So the clause is `|𝒮(σ,∅)| ≤ C L^d (1−t)`.
- **A2 (column sums).** `Σ_a Θ^{(+,−)}_{ax} = (1−t)⁻¹` (`BATheta_row_sum_pm`, `KBase.lean:381`, with `BATheta_isSymm`, `BATheta_swap` for `(−,+)`). With `baKpi_eq_sum_SigmaPi` (`KMolecule.lean:110`): `Σ_a K^{(π)}(σ,a) = (1−t)^{-n} 𝒮(σ,π)`; with `baK_eq_sum_Kpi` (`:133`): `(W^d)^{n−1}(1−t)^n T_n(σ) = Σ_π 𝒮(σ,π)`.
- **A3 (Ward bound, T1).** Claim `|T_n(σ)| ≤ B_n L^d (W^dη_t)^{-(n−1)}` for all `σ`, `n ≥ 1`, by induction on `n`. `σ` not constant: rotate (`BAKsol_rotate`, `KSolve.lean:619`) to `σ_1 = +`, `σ_n = −`; `baK_ward` (`KWard.lean:305`, `K := BAKsol`, `hK := BAKsol_isKLoopS (baKsolve d)`, `hn2 := baKsol_two`, `KInduct.lean:88`) summed over `a_1..a_{n−1}` gives `T_n(+,μ,−) = (2iW^dη)⁻¹ (T_{n−1}(+,μ) − T_{n−1}(−,μ))`, so `B_n = B_{n−1}`. `σ` constant: `n=1` `|T_1| = L^d|m| ≤ L^d`; `n=2` `K^{(2)} = W^{-d} Θ^{ss}M^{ss}` with entries `≤ B e^{-r|·|}` (`baPure_edge`, `KPure.lean:205`), row sums `≤ B³ expC²`; `n ≥ 3` `baPure_loop` (`KPure.lean:813`) and `Σ_a e^{-c maxDist a} ≤ L^d expC(d−2,c/n)^{n−1}` (`KLMolecule_sum_exp_maxDist`, translation). `W^{-(n−1)d} ≤ (W^dη)^{-(n−1)}` since `η ≤ 1`.
- **A4 (cut recursion).** For `π = KLFlong F₀ σ ≠ ∅`, `J = (i,j)` innermost (`exists_innermost`, `KLSumZeroWard.lean:577`): `baSigmaPi_cut` (`KMolecule.lean:313`) writes `Σ^{(π)} = Σ_{u,w} Σ^{(∅)}_{in}(·,u) · tΘ^{(σ_i,σ_j)}(u,w) · Σ^{(π')}_{out}(·,w)`. The map `δ ↦ (BAdeltaIn J δ u, BAdeltaOut J δ w)` is a bijection of `Z^n` onto `{x_last = u} × {y_glue = w}` (the vertex sets `[i,j)` and the rest partition `Fin n`); by A1 the two inner sums are `𝒮_in/L^d`, `𝒮_out/L^d` (independent of `u,w`); `Σ_{u,w} Θ^{(σ_i,σ_j)}(u,w) = L^d (1−t)⁻¹` (A2; `σ_i ≠ σ_j`). Hence `(1−t) L^d 𝒮(σ,π) = t 𝒮(σ_in,∅) 𝒮(σ_out,π')`; `σ_in = sigmaIn σ J`, `σ_out = sigmaOut σ J` are again cyclically alternating of lengths `n_in, n_out ≥ 3`, `≤ n−1`.
- **A5 (induction).** `P(n)`: `∃ C_n`, all data, all alternating `σ`, all `π`: `|𝒮(σ,π)| ≤ C_n L^d (1−t)`; strong induction on `n ≥ 3`. `π` not of the form `KLFlong F₀ σ`: `𝒮 = 0` (empty sum). `π ≠ ∅` realisable: A4, `P(n_in)`, `P(n_out)`. `π = ∅`: `𝒮(σ,∅) = (1−t)^n T_n − Σ_{π≠∅} 𝒮(σ,π)` at `W = 1`, `|(1−t)^n T_n| ≤ B_n κ^{1−n} L^d (1−t)`; at most `2^{n²}` layers. Then A1 gives the clause for every `r`, `x`. No `t = 1` limit, no Lipschitz step, no gap function.
**Absolute weighted clause (K08b).**
- **B1 (combinatorics).** Layer `∅`: every chord short. For a labelling `β` of the slots consistent with a non-constant `δ` there is a chord with `β(In) ≠ β(Out)` or a node with two `M`-edges with unequal ends: otherwise every chord and every node cycle (`BAnextSlot_orbit`, `KCactus.lean:403`) is constant, `T(β) = 0`, and `baSlot_path_le` (`KPure.lean:377`) makes `β`, hence `δ`, constant.
- **B2 (pointwise `g²`).** Off-diagonal short chord `≤ C_s g² e^{-c_s|x−y|}` (`baProp5s_of_real`, `Prop5Short.lean:608`); off-diagonal `M`-edge `≤ A^{1/2} g e^{-c|x−y|}` (`BAK_off_le`, `KKernel.lean:198`); other edges `≤ B e^{-r|x−y|}`. So `∏‖edges‖ ≤ Γ g² e^{-r T(β)}` and `baSigmaTree_bound` (`KPure.lean:414`, `hprod` form) gives `‖Σ^{(∅)}(σ,δ)‖ ≤ G g² e^{-c maxDist δ}` for non-constant `δ`, every `σ`, uniform in `(L,g,E,m,t)`.
- **B3 (weighted).** On the slice `S = {δ_r = x}` with `c₀ ≡ x`: `‖Σ(c₀)‖ ≤ C₁(1−t) + g² R` (signed clause minus the non-constant terms, `R = G expC^{n−1}`), `Σ_{S∖c₀} ‖Σ‖(maxDist+1)^Q ≤ g² G C_Q expC(d−2,c/(2n))^{n−1}`; total `≤ (C₁ + 2R + 1)(g² + 1−t)`: the proof of band `KLsumZero_weighted` (`KLIndStepA.lean:941-1000`), with B2 for `KLIndStepA_nc_pointwise`. Reflection and translation: `baSig_transl` (`KMolecule.lean:244`).
**Where BA differs from the band blueprint.**
1. No scalar closed form: the cactus has `M`-cycles, so `Qlayer`, `Alayer`, `sum_selfW` have no twin. They are replaced by the exact identities A1, A2, A4 (the leaf and the long-chord row sums used are only `Σ_bΘ^{(+,−)}_{ab} = (1−t)⁻¹`; no row sum of `M(σ)` or `M^{(σσ)}` enters the signed clause).
2. The band `R_n(1) = 0` step (`KLSumZeroWard` §6-9, `gapK`, Lipschitz) is not needed: `O(1−t)` holds for every `t < 1` directly.
3. The band closed-form pure bound (`KLSumAll` §3-5) is replaced by the merged `baPure_loop`.
4. New: the `g²` gain needs B1 (two off-diagonal `M`-edges in one cycle); in the band every node has one label, no `M`-edges. `g²` comes from the off-diagonal entries (`BAK_off_le`, `baProp5s_of_real`); `Im m ≥ κ` enters only through the constants `BAct_C`, `BAct_rate`.

### (ii) Numerics (scripts in `$S/T2385`, `$S` as in (a)(ii); `kode/mgraph/molecule` are the T2360 B8 scripts copied)
Setting: `Σ^{(∅)}` of the cactus (`molecule_weight`, trees with no long chord), `E = 0.3`, `σ = (+,−,+,−,…)`, `Z_L^d` torus with `Ψ` = adjacency, `m` from `(self_m)`. Columns: `signed = |Σ_{δ_0=0} Σ^{(∅)}|/(1−t)` (at `t = 1`: the absolute value, marked `*`), `Qk = Σ_{δ_0=0} ‖Σ‖(maxDist+1)^k/(g²+1−t)`, `c0 = ‖Σ(0,…,0)‖/(g²+1−t)`. `Q ≤ 2(d−1)`.
`python3 table.py 3 3 4 "1/64,1,10" 1e-1,1e-3,1e-5,0 1,2,4` (and `"1/256" 1e-5,0`):
```
d3L3n4    g=0.015625  Im m=0.988 1-t=1e-01  signed=  0.5391 Q1=    0.567 Q2=    0.592 Q4=    0.749 c0=  0.543
d3L3n4    g=0.015625  Im m=0.988 1-t=1e-03  signed=  0.5125 Q1=    2.345 Q2=    3.715 Q4=   12.385 c0=  1.012
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
(rows `g=1`, `1-t=1e-03` and `g=10`, `1-t=1e-03` of the same run are omitted; they lie between the shown rows.) Reading: the signed ratio converges as `1−t → 0` (0.512 / 1.115 / 1.184 at `1e-5` for `g = 1/64, 1, 10`) and the signed sum is `≤ 2.2e-15` at `t = 1`. For `g = 1/64` the weighted ratios rise with `t ↑ 1` from 0.57 to 9.83 (`Q1`) and level off at the `t = 1` value: the sum is `≈ A g² + B(1−t)` with `B ≈ 0.57`, `A ≈ 9.8`, both finite; as `g ↓` (1/64 → 1/256) the `t = 1` values move 9.83 → 9.33 (`Q1`), 60.8 → 53.3 (`Q4`): no growth. `c0` levels at 3.07, i.e. `Σ(c₀) ≈ 3 g²`.
`python3 table.py 3 3 4 "0.05,0.1,0.25,0.5,1,2,5,10" 1e-6 1,4` (supremum over `g` at `1−t = 1e-6`):
```
d3L3n4    g=0.05      Im m=0.981 1-t=1e-06  signed=  0.5191 Q1=   12.943 Q4=  133.752 c0=  2.972
d3L3n4    g=0.1       Im m=0.961 1-t=1e-06  signed=  0.5419 Q1=   24.050 Q4=  524.961 c0=  2.636
d3L3n4    g=0.25      Im m=0.853 1-t=1e-06  signed=  0.6874 Q1=  110.842 Q4= 5275.670 c0=  1.306
d3L3n4    g=0.5       Im m=0.723 1-t=1e-06  signed=  0.9556 Q1=  125.122 Q4= 7024.278 c0=  0.354
d3L3n4    g=1         Im m=0.670 1-t=1e-06  signed=  1.1152 Q1=   38.194 Q4= 2226.507 c0=  0.080
d3L3n4    g=2         Im m=0.655 1-t=1e-06  signed=  1.1650 Q1=    8.634 Q4=  507.285 c0=  0.019
d3L3n4    g=5         Im m=0.651 1-t=1e-06  signed=  1.1808 Q1=    1.235 Q4=   72.564 c0=  0.003
d3L3n4    g=10        Im m=0.650 1-t=1e-06  signed=  1.1836 Q1=    0.297 Q4=   17.457 c0=  0.001
```
The maximum is at `g ≈ 0.25–0.5` (a constant depending on `Λ, κ`, as in `C(d,n,Λ,κ)`), not at `g ↓`.
`python3 table.py 2 3 6 "1/64,1" 1e-1,1e-3,1e-5,0 1,2` (`n = 6`, `d = 2`, `L = 3`; `g = 10` has `Im m = 3e-23`, outside `BAReal`, skipped by the script):
```
d2L3n6    g=0.015625  Im m=0.988 1-t=1e-01  signed=  0.3698 Q1=    0.382 Q2=    0.394 c0=  0.370
d2L3n6    g=0.015625  Im m=0.988 1-t=1e-05  signed=  0.3932 Q1=    4.749 Q2=    8.032 c0=  1.523
d2L3n6    g=0.015625  Im m=0.988 1-t=0e+00  signed= 1.2e-15* Q1=    4.928 Q2=    8.345 c0=  1.570
d2L3n6    g=1         Im m=0.541 1-t=1e-01  signed=  4.0332 Q1=   87.553 Q2=  262.055 c0=  0.001
d2L3n6    g=1         Im m=0.541 1-t=1e-05  signed=  4.3893 Q1=   92.980 Q2=  278.289 c0=  0.001
d2L3n6    g=1         Im m=0.541 1-t=0e+00  signed= 3.3e-15* Q1=   92.981 Q2=  278.291 c0=  0.001
```
Finite-size limit (stated, not hidden): at `g = 1`, `d = 3`, `L = 3 → 4` (`Im m` 0.670 → 0.572, command `python3 table.py 3 4 4 "1/64,1,10" 1e-5 1,4`) `Q1` goes 38.2 → 85.8, `Q4` 2226 → 18185 (at `g = 1/64`: 9.46 → 9.08, 58.4 → 56.1). The uniformity in `L` is not tested by this numerics; it is the merged `baSig_decay` (rate `r/4` uniform) plus B3.
Identities behind A2–A5 (`python3 verify_alg.py`, `d = 1`, `q = 5`, `n = 6`, `g = 0.8`, `E = 0.3`, `t = 0.9`; `python3 verify8.py`, `q = 3`, `n = 8`):
```
V1  (1-t)^n sum_a sum_F Gamma  = (0.8137970963817787-7.450580596923818e-15j)
V1  sum_pi Stot(pi)            = (0.8137970963816943-1.9133999940024182e-15j)
V2  Stot(sigma6,{(0,3)})       = (0.5072104712297367-7.580741590018647e-16j)
V2  t/(1-t) S4 S4 / q          = (0.5072104712297313-3.315054017627938e-17j)
V3  Stot(empty) = (-0.7078343173075097-1.734723475976807e-16j)  (1-t)^n sumK - sum_{pi!=0} Stot = (-0.7078343173074253-5.710652950519081e-15j)
n=8 layers: 21 (2s)
V2 two disjoint chords: (0.4409776279254281+5.277028813921447e-15j) (0.44097762792542594-6.527713765870078e-16j)
V2 nested chords      : (0.4409776279254165-1.1931428067768479e-14j) (0.4409776279254262-7.975006733937332e-16j)
```
`python3 ward_sum.py` (`n = 6`, `q = 5`), the Ward-sum quantity `|q⁻¹ Σ_a K| η_t^{n−1}` and every layer: `g = 1/64`, `1−t = 1e-4`: 0.3707, `max_{π≠∅}|s(π)|/(1−t) = 0.2619`, `|s(∅)|/(1−t) = 0.3928`; `g = 1`, `1−t = 1e-4`: 0.2457, 1.3573, 2.0358 (full output `out/C5b.txt`).
N0 (`n = 2`, `σ = (+,−)`, `q = 5`, `g = 0.8`, `t = 0.9`): signed slice sum `= (1+0j)`, `1−t = 0.1`.
Conclusion: no ratio grows as `g ↓` or `t ↑ 1` beyond its plateau; no REQ (2051 K-b).

### (iii) Q4 line (K08a + K08b re-estimated against 4.8k)
Items (lines, lo / central / hi): A1-A2 120 / 150 / 220; label-splitting bijection 110 / 150 / 230; A4 recursion with `σ_in`, `σ_out` alternation 150 / 200 / 300; A3 Ward bound (rotation, list/vector conversions, pure `n = 1, 2, ≥ 3`) 350 / 500 / 750; A5 induction 130 / 180 / 260; wrappers (uniform + family) 60 / 80 / 120; instances 80 / 120 / 180: **K08a 1000 / 1380 / 2060** (stop line 2400 above hi). K08b: B1 160 / 220 / 330; B2 150 / 200 / 330; layer-`∅` sum 90 / 120 / 180; B3 190 / 250 / 380; assembly `SigSumZeroAbs` + instances 130 / 200 / 300: **K08b 720 / 990 / 1520**. Sum **1720 / 2370 / 3580** against the 4.8k line (central 49 %, hi 75 %): below the line; no question for Jun. Basis: line counts of the merged twins (`KMolecule` 449, `KPure` 1016, `KInduct` 991) and of the band blueprint, the segments listed here; assumptions, not measurements.

### (iv) Split and plan
**K08a** (`RBM3D/BA/KSumZeroA.lean`, public, namespace `RBM.BA`; helpers `private`, stem `KSumZeroA_`):
Context of every K08a statement: `{d L n : ℕ} [NeZero L] [NeZero n]` (`NeZero` instances are part of the statement; `Zd d L := Fin d → ZMod L`); `S(d,L,g,E,m)` below stands for the literal term `BAMsigma d L (BAMB d L g (E : ℂ) m)` and is written out in the Lean statements. Every hypothesis is listed; none is elided.
- `baSigmaPi_slice` (A1), any translation-invariant `M`, no range hypotheses (`NeZero L` gives `card (Zd d L) = L^d`):
  `(M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (r : Fin n) (x : Zd d L) : (L : ℂ) ^ d * ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x), BASigmaPi d L n M t σ π δ = ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ`.
- `baK_sumAll_eq_layers` (A2), the `W`-explicit identity (false at `W = 0`, see script (ii-c)):
  `{κ g E : ℝ} {m : ℂ} (hκ : 0 < κ) (hg : 0 < g) (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (hn : 3 ≤ n) (σ : Fin n → Bool) (halt : ∀ j, σ j ≠ σ (j + 1)) : ((W : ℂ) ^ d) ^ (n - 1) * ((1 - (t : ℂ)) ^ n * ∑ a : Fin n → Zd d L, BAKsol d L W S(d,L,g,E,m) (PropSpin m) t (KLloopOf d L σ a)) = ∑ π ∈ (diagonals n).powerset, ∑ δ : Fin n → Zd d L, BASigmaPi d L n S(d,L,g,E,m) t σ π δ`.
- `baK_sumAll_le` (T1), the constant `B` before `L, W, g, E, m, t, σ`:
  `{d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 1 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, ‖∑ a : Fin n → Zd d L, BAKsol d L W S(d,L,g,E,m) (PropSpin m) t (KLloopOf d L σ a)‖ ≤ B * (L : ℝ) ^ d * (((W : ℝ) ^ d * ((1 - t) * m.im))⁻¹) ^ (n - 1)`.
- `baSigmaPi_total_le` (A5):
  `{d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) → ∀ π : Finset (Fin n × Fin n), ‖∑ δ : Fin n → Zd d L, BASigmaPi d L n S(d,L,g,E,m) t σ π δ‖ ≤ C * (L : ℝ) ^ d * (1 - t)`.
- `baSig_signed_sum_unif` (T2, uniform; from `baSigmaPi_total_le` with `C` the same and `baSigmaPi_slice` with `M = S(d,L,g,E,m)`, `hshift := BAMsigma_shift`, `KSolve.lean:558`):
  `{d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d L), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x), BASigmaPi d L n S(d,L,g,E,m) t σ ∅ δ‖ ≤ C * (1 - t)`.
- `baSig_signed_sum` (T2, family form; hypotheses as `baSig_decay`, `KPure.lean:632`, with `ht1` strict):
  `{ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1) : ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), BASig d n L g E m t i σ δ‖ ≤ C * (1 - t i)`.
- Instances at the flow point `P` of `(3,4)` (`Λ = 10`, `κ = P.m0.im`, `n = 4`, `σ = KLsigAlt 4`, `t = 1/2` and `999/1000`, `W = 1`): `baSig_signed_sum_unif`, `baSigmaPi_total_le` and `baK_sumAll_le` applied with `P.real`, `hd := 3 ≤ 3`, `hL := 3 ≤ 4`, `hg : 0 < g₀`, `g₀ ≤ 10`, the concrete inequality extracted; `baK_sumAll_eq_layers` (at `W = 1`) and `baSigmaPi_slice` as identities. Nonvacuity: `TSP 4` has three trees, only `π = ∅` is nonempty.
**K08b** (`BA/KSumZeroB.lean`, next ticket): `baSig_nc_pointwise` (B2), `baSig_weighted` (B3, every `Q`), `baSig_sumZeroAbs : SigSumZeroAbs d n L g t (BASig d n L g E m t)` under `3 ≤ n`, `t i < 1`, `BAReal`, `g i ≤ Λ` (K-b predicate for K09b; first two conjuncts `baSig_transl`, third = K08a signed + B3).
**Plan against the stop line (2400, `wc -l RBM3D/BA/KSumZeroA.lean`).** Order: (1) A1-A2 and wrappers (≈ 300); (2) T1 (≈ 500, checkpoint at 800); (3) label-splitting bijection and A4 (≈ 350, checkpoint at 1150); (4) A5 and T2 (≈ 260); (5) instances (≈ 120). Central 1380; hi 2060; the checkpoint at 1800 with the instance still unwritten is a REQ.
Risks, none a mathematical gap: the label-splitting bijection (`Fin n = [i,j) ⊔ rest`) and the list/vector conversions in the Ward induction are bookkeeping; if the bijection exceeds 230 lines the budget of step (3) is re-checked at the 1150 checkpoint (the sole writable file is `RBM3D/BA/KSumZeroA.lean`; no second file).

## (b) Script output (stage 1b; times by `date -u`, Sat Oct 10 2026: final-tree build finished 13:24:15 UTC, check file / registry / axioms run in the window 13:24:27 to 13:25:05 UTC, this section written 13:28:36 UTC; working tree equals commit ab58d55)
```
$ git log --format='%h %s' main..t/T2385
ab58d55 T2385: KSumZeroA module docstring rewrapped (no linter warnings)
9aac504 T2385: KSumZeroA instances at n = 6 (nonempty long layer), decided layer facts, docstring fixes
664d62e T2385: KSumZeroA sections 5-8 (alternating polygons, strong induction, signed sum-zero, instances)
13b5440 T2385: KSumZeroA sections 1-4 (slice sums, layer identity, Ward bound for sums, cut identity)
$ git diff --stat main...t/T2385
RBM3D/BA/KSumZeroA.lean | 1195 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1195 insertions(+)
$ wc -l RBM3D/BA/KSumZeroA.lean    # at the four commits (tool log): 732, 1170, 1190, 1195; stop line 2400 (binding), not reached
$ lake build RBM3D.BA.KSumZeroA    # finished 13:24:15 UTC; `grep -c 'KSumZeroA.lean:'` on the build log: 0 warnings from the new file
✔ [3771/3771] Built RBM3D.BA.KSumZeroA (6.1s)
Build completed successfully (3771 jobs).
exit=0
$ lake env lean docs/tickets/checks/T2385-check.lean    # the dispatcher's check file, on the branch
exit=0   (9 `#check` outputs, no error line)
$ lake env lean reg.lean    # `import RBM3D`, `import RBM3D.BA.KSumZeroA`, `#assert_rbm_axioms`  (registry pre-check)
axiom audit: 11030 theorems, 3225 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
exit=0
$ #print axioms (the six public declarations)
'RBM.BA.baSigmaPi_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_sumAll_eq_layers' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_sumAll_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSigmaPi_total_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_signed_sum_unif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_signed_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Target statements, extracted from the file by script (`theorem NAME` up to `:= by`, whitespace normalised). The script also compares each one with the (a+)(iv) text, `S(d,L,g,E,m)` expanded to `(BAMsigma d L (BAMB d L g (E : ℂ) m))`: it printed `identical` 6 times out of 6.
```
theorem baSigmaPi_slice (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (hshift : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (t : ℝ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (r : Fin n) (x : Zd d L) : (L : ℂ) ^ d * ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x), BASigmaPi d L n M t σ π δ = ∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ π δ
theorem baK_sumAll_eq_layers {κ g E : ℝ} {m : ℂ} (hκ : 0 < κ) (hg : 0 < g) (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (hn : 3 ≤ n) (σ : Fin n → Bool) (halt : ∀ j, σ j ≠ σ (j + 1)) : ((W : ℂ) ^ d) ^ (n - 1) * ((1 - (t : ℂ)) ^ n * ∑ a : Fin n → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)) = ∑ π ∈ (diagonals n).powerset, ∑ δ : Fin n → Zd d L, BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ
theorem baK_sumAll_le {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 1 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, ‖∑ a : Fin n → Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)‖ ≤ B * (L : ℝ) ^ d * (((W : ℝ) ^ d * ((1 - t) * m.im))⁻¹) ^ (n - 1)
theorem baSigmaPi_total_le {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) → ∀ π : Finset (Fin n × Fin n), ‖∑ δ : Fin n → Zd d L, BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ π δ‖ ≤ C * (L : ℝ) ^ d * (1 - t)
theorem baSig_signed_sum_unif {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Fin n → Bool, (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d L), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = x), BASigmaPi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ ∅ δ‖ ≤ C * (1 - t)
theorem baSig_signed_sum {ι : Type} {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (hL : ∀ i, 3 ≤ L i) (hg : ∀ i, 0 < g i) (hgΛ : ∀ i, g i ≤ Λ) (hr : ∀ i, BAReal d (L i) (g i) κ (E i) (m i)) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i < 1) : ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) (σ : Fin n → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin n) (x : Zd d (L i)), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d (L i) => δ r = x), BASig d n L g E m t i σ δ‖ ≤ C * (1 - t i)
```
Compiled nonempty instances (14 `example`s of `namespace RBM.BA.KSumZeroAInst`, extracted by script: the statement, or the head of the application term; data = the merged flow point `P` of `(3,4)`, `Λ = 10`, `κ = P.m0.im`, `P.real`):
```
[1] example : ∀ j : Fin 4, KLsigAlt 4 j ≠ KLsigAlt 4 (j + 1) 
[2] example : KLTSPlong 4 (KLsigAlt 4) ∅ = TSP 4 
[3] example : (TSP 4).card = 3 
[4] example := baSigmaPi_slice (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (fun σ x y c => BAMsigma_shift 3 4 P.g0 _ P.m0 σ x y c) (1 / 2) (KLsigAlt 4) ∅ 0 0
[5] example := baK_sumAll_eq_layers (d := 3) (L := 4) (n := 4) P.real.1.1 P.g0_pos (by norm_num) 1 le_rfl P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩ (by norm_num) (KLsigAlt 4) (by decide)
[6] example := baK_sumAll_eq_layers (d := 3) (L := 4) (n := 4) P.real.1.1 P.g0_pos (by norm_num) 2 (by norm_num) P.real (t := 999 / 1000) ⟨by norm_num, by norm_num⟩ (by norm_num) (KLsigAlt 4) (by decide)
[7] example : ∃ B : ℝ, 0 < B ∧ ‖∑ a : Fin 4 → Zd 3 4, BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2) (KLloopOf 3 4 (KLsigAlt 4) a)‖ ≤ B * (4 : ℝ) ^ 3 * (((2 : ℝ) ^ 3 * ((1 - 1 / 2) * P.m0.im))⁻¹) ^ 3 
[8] example : ∃ B : ℝ, 0 < B ∧ ‖∑ a : Fin 3 → Zd 3 4, BAKsol 3 4 1 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (999 / 1000) (KLloopOf 3 4 (fun _ => true) a)‖ ≤ B * (4 : ℝ) ^ 3 * (((1 : ℝ) ^ 3 * ((1 - 999 / 1000) * P.m0.im))⁻¹) ^ 2 
[9] example : ∃ C : ℝ, 0 < C ∧ ‖∑ δ : Fin 4 → Zd 3 4, BASigmaPi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (999 / 1000) (KLsigAlt 4) ∅ δ‖ ≤ C * (4 : ℝ) ^ 3 * (1 - 999 / 1000) 
[10] example : ∀ j : Fin 6, KLsigAlt 6 j ≠ KLsigAlt 6 (j + 1) 
[11] example : ({((0 : Fin 6), (3 : Fin 6))} : Finset (Fin 6 × Fin 6)) ∈ KLTSPlong 6 (KLsigAlt 6) {((0 : Fin 6), (3 : Fin 6))} 
[12] example : ∃ C : ℝ, 0 < C ∧ ‖∑ δ : Fin 6 → Zd 3 4, BASigmaPi 3 4 6 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (KLsigAlt 6) {((0 : Fin 6), (3 : Fin 6))} δ‖ ≤ C * (4 : ℝ) ^ 3 * (1 - 1 / 2) 
[13] example : ∃ C : ℝ, 0 < C ∧ ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ 0 = 0), BASigmaPi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 1 / 2) 
[14] example : ∃ C : ℝ, 0 < C ∧ ∀ (i : Unit) (σ : Fin 4 → Bool), (∀ j, σ j ≠ σ (j + 1)) → ∀ (r : Fin 4) (x : Zd 3 4), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 4 => δ r = x), BASig 3 4 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (999 : ℝ) / 1000) i σ δ‖ ≤ C * (1 - ( ...
```
Declaration index (line, name; script): 55 baSigmaPi_slice (public); 100 theta_row; 113 theta_col; 131 baK_sumAll_eq_layers (public); 187 rot1; 209 rotN; 226 sum_rot; 241 ward_fin; 278 const_or_rot; 306 sum_exp; 321 pure_two; 386 pure_three; 411 pure_aux; 431 ward_aux; 534 baK_sumAll_le (public); 649 split_sum; 678 cut_sum; 793 sigmaIn_alt; 817 sigmaOut_alt; 868 offdiag; 938 total_aux; 1042 baSigmaPi_total_le (public); 1058 baSig_signed_sum_unif (public); 1079 baSig_signed_sum (public).
Name-clash grep of the six public names and of the stem `KSumZeroA_` over `RBM3D/` (worktree and main worktree, own file excluded): 0 hits. `grep -n 'sorry\|admit\|native_decide\|axiom'` on the new file: 0 hits. Public declarations: 6; private declarations with the stem: 33; private declarations without it: 0.
Ports: none. No code was copied from `../RBM1D` or `../RBM2D` and nothing under them was opened in this stage (tool log); no diff-stat applies.

**Narrative.**
- Delivered: `RBM3D/BA/KSumZeroA.lean` (1195 lines, namespace `RBM.BA`), six public theorems (the six statements of (a+)(iv), identical to the audited text by script), 33 private helpers, 14 examples. The branch diff touches only this file. No hypothesis added, no target weakened, no pin changed, no scope widened; no obstruction, no REQ trigger.
- The argument of (a+)(i) was implemented as written, with no external input and no unproved pin: `baKsolve` (`BA/KTreeRep.lean:1699`) is a merged theorem. Inputs used (all merged): `baK_ward`, `BAKsol_isKLoopS`, `BAKsol_rotate`, `baKsol_one`, `baKsol_two`, `baK_eq_sum_Kpi`, `baKpi_eq_sum_SigmaPi`, `baSigmaPi_cut`, `baSigmaPi_shift`, `BATheta_row_sum_pm`, `BATheta_swap`, `BATheta_isSymm`, `baPure_edge`, `baPure_loop`, `KLMolecule_sum_exp_maxDist`, `BAsum_exp_decay_le`, `BAK_row_sum`, `BAMss_norm_eq_BAK`, `BAm_norm_le_one`, `BAMsigma_shift`, `exists_innermost`, `Flong_subset_diagonals`.
- Map of the plan A1-A5 to the file (lines in the index above): A1 `baSigmaPi_slice`; A2 `KSumZeroA_theta_row/col`, `baK_sumAll_eq_layers`; A3 `KSumZeroA_rot1/rotN/sum_rot` (rotation in `Fin` form), `KSumZeroA_ward_fin` (`baK_ward` summed over the last label), `KSumZeroA_const_or_rot`, `KSumZeroA_pure_two/pure_three/pure_aux` (constant `σ`: `n = 2` by hand, `n ≥ 3` by `baPure_loop` and `KSumZeroA_sum_exp`), `KSumZeroA_ward_aux` (induction on `n`, constant `max B Bp`), `baK_sumAll_le`; A4 `KSumZeroA_split_sum` (the label-splitting bijection, `Finset.sum_bij'` with the glued labelling `KSumZeroA_glue`), `KSumZeroA_cut_sum`; A5 `KSumZeroA_sigmaIn_alt/sigmaOut_alt` (the two polygons of a long chord are alternating), `KSumZeroA_offdiag` (layers `π ≠ ∅`), `KSumZeroA_total_aux` (layer `∅` through `baK_sumAll_eq_layers` at `W = 1`), `baSigmaPi_total_le`; wrappers `baSig_signed_sum_unif`, `baSig_signed_sum`.
- Bookkeeping choices, not mathematical departures: (i) the induction of A5 is an ordinary induction on `N` whose constant `C` serves every length `3 ≤ n ≤ N` (`KSumZeroA_total_aux`), in place of a strong induction with one constant per length; (ii) the rotation of A3 is `σ ↦ σ(· + r)` with `σ_last = -σ_0` (`KSumZeroA_const_or_rot`), and `baK_ward` is applied for either value of `σ_0` (it is stated for every `s`); (iii) the leaf column sums are used in A2 and the row sums of the long chord in A4.
- Q4 line: K08a is 1195 lines against (a+)(iii) K08a 1000 / 1380 / 2060. With (a+)(iii)'s K08b central estimate 990 (an estimate, not measured) K08a + K08b is about 2185 against the 4.8k line; no question for Jun arises from this number.
- Instances: each of the six public theorems is applied at `P` (items [4]-[14]); `KLsigAlt 4` and `KLsigAlt 6` are cyclically alternating (decided, [1], [10]); `KLTSPlong 4 σ ∅ = TSP 4` with three trees (decided, [2], [3]); at `n = 6` the long layer `{(0,3)}` is nonempty (decided, [11]) and `baSigmaPi_total_le` is applied to it ([12]). Observation O1 of `T2385-1a-audit.md` (an instance of the family form `baSig_signed_sum`) is item [14]. The numerics of (a)(ii) are not rerun: the mathematics did not change.
- For K08b: the public interface is `baSig_signed_sum` (clause 1 of `SigSumZeroAbs` at `BASig`, under `3 ≤ n`, `t i < 1`, `BAReal`, `g i ≤ Λ`), `baSigmaPi_slice` and `baSigmaPi_total_le`; the helpers are private. `SigSumZeroAbs` (`KLIndStepA.lean:1036`) is untouched (T2385b).

## (c) Verified Mathlib names
`#check` on 67 names in a scratch file importing `RBM3D.BA.KSumZeroA`: 0 errors. Finset.sum_nbij', Finset.sum_fiberwise, Finset.sum_bij', Finset.sum_mul_sum, Finset.sum_product', Finset.add_sum_erase, Finset.card_powerset, Finset.card_le_univ, Finset.card_erase_le, Finset.ne_of_mem_erase, Finset.empty_mem_powerset, Finset.sum_const, Finset.card_univ, Finset.sum_comm, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_le_sum, Finset.sum_congr, Finset.prod_univ_sum, Finset.prod_congr, Finset.nonempty_iff_ne_empty, Fintype.sum_equiv, Fintype.sum_prod_type, Fintype.piFinset_univ, Fintype.card_fun, Fintype.card_fin, Equiv.arrowCongr, Equiv.addRight, Fin.snocEquiv, Fin.snoc_castSucc, Fin.snoc_last, Fin.coeSucc_eq_succ, Fin.last_add_one, Fin.succ_last, Fin.val_add_one_of_lt, Fin.cast_val_eq_self, Fin.val_last, List.ofFn_succ, List.ofFn_succ', List.ofFn_cons, piFinTwoEquiv, piFinTwoEquiv_symm_apply, inv_anti₀, pow_le_pow_left₀, one_le_pow₀, Complex.im_le_norm, Complex.norm_real, Complex.norm_natCast, Complex.norm_I, le_of_mul_le_mul_left, mul_left_cancel₀, norm_sub_le, norm_sum_le, mul_inv_cancel₀, Nat.lt_or_ge, Nat.cast_succ, Function.update_of_ne, Function.update_self, lt_max_of_lt_left, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, Real.norm_eq_abs, Matrix.mul_apply, Matrix.transpose_apply, Fin.NatCast.instNatCast.
Verified absent: a `grep` in `.lake/packages/mathlib/Mathlib` for `theorem sum_pi_succ`, `prod_pi_snoc`, `sum_fin_snoc` had no hit (the only hits were uses of `Fin.sum_univ_castSucc`, which sums over `Fin n`, not over functions `Fin n → G`); the split of a sum over `Fin (k+2) → G` therefore uses `Fin.snocEquiv` with `Fintype.sum_prod_type`.

## (d) Open issues and paper-delta candidates
Open issues: none mathematical; nothing blocked; no REQ.
- `T2385a`: `(eq:Sigma-empty-sum-zero)` (`A:731-734`) is cited, not proved in the TeX; here it is proved from `(WI_calK)` (`baK_ward`), the cut factorisation `(eq:molecule-Kpi)` and translation invariance; no use of [YY_25 L3.10] or `Q(1) = 0`.
- `T2385b`: `SigSumZeroAbs` (`KLIndStepA.lean:1036`) has no range for `n` or `t` and is false at `n = 2` (N0: signed slice sum 1); the BA instance carries `3 ≤ n`, `t i < 1` (the band instance already has `3 ≤ n`, its consumers `t i < 1`). `baSig_signed_sum` carries both; the pin is not changed here.
- `T2385c`: the Lean slice bounds are uniform in `L, W, g ≤ Λ, E, t` (C1); the paper's `O(|1−t|)`, `O(λ² + |1−t|)` are stated with `≺`.
- `T2385d`: `baK_sumAll_eq_layers` and `baK_sumAll_le` carry `1 ≤ W`; at `W = 0` the identity is false in Lean because `0⁻¹ = 0` (script (ii-c) of (a)). A candidate only: the TeX was not re-read for this hypothesis in stage 1b.
- `T2385e`: `baSigmaPi_total_le` bounds `Σ_δ Σ^{(π)}(δ)` for every layer `π` and every alternating `σ`; the paper's first estimate of `(eq:Sigma-empty-sum-zero)` is the layer `π = ∅` on a slice (`baSig_signed_sum`). The other layers are the induction invariant of the cut recursion; `A:700-740` (the lines read) does not state a bound for them.
