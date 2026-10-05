# Independent check of Lemma `TailtoTail`, estimate `(neiwuj)`, arXiv:2507.20274 (d >= 3)

Scope: ticket T2097 preflight (`docs/reports/T2097-prove.md`, row 10 and Part C) and DECISIONS §33's
claim that `(neiwuj)` is false at d >= 3 "by a factor rho_eta = (1-s)/(1-t)" and "may be a genuine gap
in Step 5 of the paper".

Files read: `3_5_Loop_Hierarchy.tex` (109-128 `DefTHUST`/`def_Ustz`; 311-325 `def: TTfunc`; 1620-1626
`sum_res_Ndecay`; 1957-2075 regime lambda^2/L^2 <= 1-t <= 1-s <= lambda^2; 2284-2383 regime
1-t >= lambda^2 incl. `def_WTuD`, `lem_dec_calE`, `TailtoTail`, `eq:def_TTT`, `lem:pf_step5`),
`1_2_Intro_model_result.tex` (262-278 metric; 302-307 `eq:variancematrix`; 714-722 flow; 1068-1170
`def_Theta`, `defi:ofB`, `lem_propTH`; 1256-1299 `lem:main_ind`; 1379-1386 Step 5 targets), the 2D paper
(`7_Evolution_kernel_estimates.tex` 1-40, `5-6_loop-hierarchy-analysis.tex` 285-470), Lean
`Defs/Tail.lean`, `Defs/Params.lean`, `RBM2D/Path/UTransport.lean` 400-520, `docs/DECISIONS.md` §29, §33.

Scripts/raw output here: `check_neiwuj.py` -> `out_check.txt`, `check_extra.py` -> `out_extra.txt`.

---

## 0. Verdict

`(neiwuj)` is TRUE as stated for every d >= 2 (in particular d >= 3), with a constant depending only
on d. The team's FAIL comes from substituting the wrong tail function. The paper has two:

* `calT_t(r) := B_{t,r} e^{-sqrt(r/ell_t)}`, `wT^ell_{t,D}(r) := max(calT_t(r ∧ ell), W^{-D})`
  (Definition `def: TTfunc`, Section 3, lines 311-322; = Lean `tailT`/`tailW` in `Defs/Tail.lean`);
  amplitude `B_{t,r} ∝ (g^2+|1-t|)^{-1}`; used in Step 2 and in the Step 5 regimes `1-t <= lambda^2`.
* `T_{u,D}(r) := (W^d |1-u|)^{-2} exp(-r^{1/2}) + W^{-D}` (`def_WTuD`, lines 2296-2297, subsection
  "The case 1-t >= lambda^2"); amplitude `∝ (1-u)^{-2} = eta_u^{-2}`, exactly as in d = 1, 2
  (2D: `M_u^{-2}`, `M_u = W^2 ell_u^2 eta_u`).

Lemma `TailtoTail` (2344-2362) is stated for the second (`T_{s,D}`, `T_{t,D}`: upright T, no tilde,
no superscript, 50 lines after `def_WTuD`, and with the matching additive `(|1-s|/|1-t|)^2 W^{-D}`).
With this `T`, the factor `((1-s)/(1-t))^2` of `sum_res_Ndecay` converts `(W^d(1-s))^{-2}` into
`(W^d(1-t))^{-2}` exactly, and `e^{-sqrt r}` is preserved because in the regime `1-t >= lambda^2` the
kernel has range `ell_t = 1`. The team's Part C used `calT_u` instead, for which the ratio is indeed
`≈ rho_eta` -- a fact the paper knows and handles elsewhere by a different argument (§5). I reproduce
the team's `53.6` exactly with `calT` and get ratios in `[0.66, 1.36]` with the paper's `T_{u,D}`.

---

## 1. Objects (paper's definitions)

Random band matrix model, flow framework, bulk energy so `|m(E+i0)| = 1`:

* `S^{(B)}_{ab} = (1+2d g^2)^{-1} 1_{a=b} + g^2 (1+2d g^2)^{-1} 1_{a~b}` (`eq:variancematrix`; `g = \ilambda`,
  `W^{-d/2+fd} <= g <= fd^{-1}` by `eq:WO`).
* `M^{(sig1,sig2)} = m(sig1) m(sig2) I` (`eq:Msig`); for `(+,-)`: `I`.
* `Theta_t = (1 - t M S^{(B)})^{-1}` (`def_Thxi`), row sums `1/(1-t)` for `(+,-)` (`eq:THETAinftinf`),
  `|Theta^{(sig)}_{t,ab}| <= Theta^{(+,-)}_{t,ab}`.
* `(U^{(2)}_{s,t,sig} o A)_a = sum_{b1,b2} P_{a1 b1} P_{a2 b2} A_{b1 b2}`, `P := (1 - sMS)(1 - tMS)^{-1}`
  (`def_Ustz`). By `(1-tMS)Theta_t = 1`: `P = (s/t) I + ((t-s)/t) Theta_t` (`eq:decompU`, line 1983), so
  for `(+,-)`: `P >= 0` entrywise, row sums `rho := (1-s)/(1-t)` (= `sum_res_Ndecay`, equality at `A ≡ 1`).
* Metric: periodic `l^infty` on `Z_L^d` (lines 274-275).
* `B_{t,K} = (g^2+|1-t|)^{-1}(K+1)^{-(d-2)} + (L^d|1-t|)^{-1}`; `ell_t = min(max(g|1-t|^{-1/2},1),L)`.
  In the regime `1-t >= g^2`: `ell_t = 1`, `B_{t,K} <= 2/(1-t)`, `B_{t,0} ≍ (1-t)^{-1}`.
* `prop:ThfadC`: `|Theta_t(0,a)| <= C_d B_{t,|a|} e^{-c_d|a|/ell_t}`; in the regime: `(1-t)|Theta_t(0,a)| <= 2C_d e^{-c_d|a|}`.
* Hypothesis of `TailtoTail`: `1-s >= 1-t >= g^2` (so `0 <= s <= t < 1`, `g < 1`, `ell_s = ell_t = 1`),
  `|A_a| <= T_{s,D}(|a1-a2|)`; conclusion `|(U o A)_a| ≲ T_{t,D}(|a1-a2|) + rho^2 W^{-D}`.

Amplitude consistency: Step 5 target `(Eq:Gdecay+s<g_flow)` (1_2:1384) is
`|(L-K)^{(2)}_u| ≺ (W^{-d}B_{u,0})^2 e^{-|a1-a2|^{1/2}} + W^{-D}` for `1-t >= g^2`, and 3_5:2288 says
"the prefactor `(W^{-d}B_{u,0})^2` ... is of order `(W^d|1-u|)^{-2}` ... precisely matching the setting in
dimension 1". The stopping time `(eq:def_TTT)`, `lem_dec_calE` (`res_deccalE_lk`:
`(1-u)^{-1}(W^d|1-u|)^{-1}(J*)^2 T_{u,D}`) and the input `(Eq:Gdecay+IND_s<g)` (1_2:1271) all use this `T`.

---

## 2. Proof of `(neiwuj)` (all `a`, constant depends only on d)

Let `Ptilde := P/rho` (stochastic). Since `U = P ⊗ P >= 0` entrywise and `|A| <= T_{s,D}`,

    |(U o A)_a| <= (U o T_{s,D})_a
                = (W^d(1-s))^{-2} rho^2 sum_{b} Ptilde_{a1 b1} Ptilde_{a2 b2} e^{-sqrt|b1-b2|} + rho^2 W^{-D}
                = (W^d(1-t))^{-2}       sum_{b} Ptilde_{a1 b1} Ptilde_{a2 b2} e^{-sqrt|b1-b2|} + rho^2 W^{-D}.

(Exact amplitude conversion `(1-s)^{-2} rho^2 = (1-t)^{-2}`: the d = 1, 2 mechanism, 2D `res_deccalE_0`
and Lean `hid`, with `ell_s = ell_t = 1`, so no `(ell_t/ell_s)^4`.)

Spatial part: `sqrt|a1-a2| <= sqrt|a1-b1| + sqrt|b1-b2| + sqrt|b2-a2|` (triangle inequality for the periodic
`l^infty` distance + subadditivity of sqrt), hence

    sum_b Ptilde_{a1 b1} Ptilde_{a2 b2} e^{-sqrt|b1-b2|} <= e^{-sqrt|a1-a2|} ( sum_x Ptilde_{0x} e^{sqrt|x|} )^2.

Kernel bound (regime `1-t >= g^2`): off-diagonal `Ptilde_{0x} = [(t-s)/(t(1-s))] (1-t)Theta_t(0,x)
<= (1-t)Theta_t(0,x)` (bracket `<= 1` since `s(1-t) >= 0`), `Ptilde_{00} <= 1`. With
`1 - tS = alpha - beta Adj`, `alpha = (1+2dg^2-t)/(1+2dg^2)`, `beta = t g^2/(1+2dg^2)`, `alpha - 2d beta = 1-t`,
the Neumann series gives

    (1-t) Theta_t(0,x) <= q^{|x|_1},  q := 2d beta/alpha = 2d t g^2/(1+2d g^2 - t) <= 2d/(2d+1)  (uses 1-t >= g^2),

uniformly in s, t, L, W, g (numerically verified, `out_extra.txt` (1); `prop:ThfadC` gives the same with
`2C_d e^{-c_d|x|}`). Therefore `sum_x Ptilde_{0x} e^{sqrt|x|} <= 1 + sum_{x != 0} q^{|x|_1} e^{sqrt|x|_1} =: C_d`,
and `(neiwuj)` holds with explicit constant `C_d^2`: `|(U o A)_a| <= C_d^2 T_{t,D}(|a1-a2|) + rho^2 W^{-D}`.
(Crude `C_3 ≈ 3.6e5`; an exponential-moment bound with `sqrt r <= r/2 + 1/2` gives
`C_3 <= 1 + e^{1/2} 2^3/(1 - 6(cosh(1/2) - 1)) ≈ 57`; the true constant in d = 3 is `<= 1.36` in every
parameter set tried, §3.) Other charges: `|P^{(sig)}_{ab}| <= P^{(+,-)}_{ab}` entrywise, same bound
(`out_extra.txt` (2)). Block Anderson: same proof on `lem_propTH` (stated for both models).

Remarks. (i) `1-t >= g^2` enters twice: `B_{u,0} ≍ (1-u)^{-1}` (so `T_{u,D}` is the right amplitude) and
`ell_t = 1` (so `e^{-sqrt r}` is preserved without rescaling). (ii) The paper's "basic calculus fact"
(line 2365) is the continuum version of the convolution step (also what makes `res_deccalE_lk`
dimension-free). (iii) No `|a1-a2| >= ell*_t` restriction is needed in d >= 3, unlike 2D.

---

## 3. Numerics (d = 3, exact `U^{(2)}_{s,t,(+,-)}`, extremal `A = T_s(|b1-b2|)`)

`check_neiwuj.py`: `Z_L^3`, periodic `l^infty`, `S^{(B)}` from `eq:variancematrix`, `P = (1-sS)(1-tS)^{-1}` by
FFT (translation invariance: `(U o f(b1-b2))(a) = (P*P*f)(a1-a2)`); dense `L = 6` agrees to 1e-6. `U >= 0`
makes `A = T_s(|b1-b2|)` the exact worst case. `R_paper(r) := (U o T_s)(a)/T_t(|a1-a2|)` with the paper's
`T_{u,D}` (main part; the `W^{-D}` part gives exactly `rho^2 W^{-D}`); `R_team(r)` with `calT_u`.

Regime of the lemma, `1-s >= 1-t >= g^2` (`ell_s = ell_t = 1`):

| L  | g     | 1-s   | 1-t          | rho  | R_paper r=1/2/3/L/2            | max R_paper | R_team r=1/2/3/L/2           | max R_team |
|----|-------|-------|--------------|------|--------------------------------|-------------|------------------------------|------------|
| 16 | 0.01  | 0.5   | 0.01         | 50   | 1.022 / 1.005 / 1.003 / 1.008  | 1.022       | 53.63 / 51.37 / 50.94 / 51.17 | 53.63 (team: 53.62) |
| 16 | 0.01  | 0.1   | 0.01         | 10   | 1.020 / 1.005 / 1.003 / 1.007  | 1.020       | 10.67 / 10.25 / 10.17 / 10.21 | 10.67 |
| 16 | 0.01  | 0.02  | 0.01         | 2    | 1.011 / 1.003 / 1.001 / 1.004  | 1.011       | 2.08 / 2.03 / 2.02 / 2.02     | 2.08 |
| 16 | 0.1   | 0.5   | 0.01 (=g^2)  | 50   | 0.675 / 0.867 / 0.982 / 1.343  | 1.343       | 55.3 / 89.0 / 111.6 / 172.3   | 172.3 (≈3.4 rho) |
| 16 | 0.1   | 0.999 | 0.01         | 99.9 | 0.672 / 0.865 / 0.981 / 1.346  | 1.346       | 110 / 179 / 225 / 349         | 349 |
| 16 | 0.3   | 0.9   | 0.09 (=g^2)  | 10   | 0.769 / 0.941 / 1.024 / 1.255  | 1.255       | 12.8 / 18.8 / 21.8 / 27.8     | 27.8 |
| 16 | 0.5   | 0.99  | 0.25 (=g^2)  | 4    | 0.896 / 1.012 / 1.046 / 1.157  | 1.157       | 5.8 / 7.3 / 7.6 / 8.2         | 8.2 |
| 16 | 0.01  | 0.5   | 1e-4 (=g^2)  | 5000 | 0.658 / 0.853 / 0.973 / 1.360  | 1.360       | 5386 / 8837 / 11237 / 18026   | 18026 |
| 16 | 0.001 | 0.5   | 1e-6 (=g^2)  | 5e5  | 0.658 / 0.853 / 0.973 / 1.360  | 1.360       | 5.4e5 / 8.8e5 / 1.1e6 / 1.8e6 | 1.8e6 |
| 32 | 0.1   | 0.5   | 0.01         | 50   | 0.675 / 0.866 / 0.980 / 1.219  | 1.219       | 55.3 / 89.0 / 111.5 / 134.2   | 134.2 |
| 64 | 0.1   | 0.5   | 0.01         | 50   | 0.675 / 0.866 / 0.980 / 1.141  | 1.141       | 55.3 / 89.0 / 111.6 / 117.7   | 127.8 |
| 64 | 0.3   | 0.9   | 0.09         | 10   | 0.769 / 0.941 / 1.024 / 1.105  | 1.105       | 12.8 / 18.8 / 21.8 / 20.9     | 22.8 |

With the paper's `T_{u,D}` the ratio is `<= 1.36` for all `a`, `L in {16,32,64}`, `rho` from 2 to 5e5, incl.
the boundary `1-t = g^2`, and does not grow with `rho` or `L`. With `calT_u` it is `≈ rho` (up to `≈ 3.5 rho`
at `1-t = g^2`): the team's numbers are right for the function they used, which is not the lemma's.

Literal statement with `W, D` (`out_extra.txt` (4)): `(U o T_{s,D})(a) <= 1.4 T_{t,D}(|a1-a2|) + rho^2 W^{-D}` at
every `a` for `(L,W,D,g,1-s,1-t) = (16,10,5,0.1,0.5,0.01)`, `(16,10,8,0.01,0.5,1e-4)`, `(16,100,12,0.3,0.9,0.09)`.
Squared profile `e^{-2 sqrt r}` (quadratic-variation/martingale term, amplitude `rho^4 (W^d(1-s))^{-4}
= (W^d(1-t))^{-4}`): max ratio `<= 2.02` (`out_extra.txt` (3)).
Outside the hypothesis (`1-t < g^2`), for information: ratio with the paper's `T` still `<= 2.1` at `L <= 32`,
but `T_{u,D}` is not the relevant function there (`B_{u,0} ≍ g^{-2}`) and the paper does not use `TailtoTail` there.

Difference from the team's construction: identical `S`, `Theta`, `U` (my positivity/row-sum checks agree
with their Part A); the only difference is `A = T_{s,D}` (`def_WTuD`) versus `A = calT_s` (`defTUL`).

---

## 4. Answers

(1) Is `(neiwuj)` false at d >= 3 as stated? No: true with a d-dependent constant (§2), numerically `≈ 1.36`
in d = 3 (§3). The team misread the tail function: Lean `tailT` (= `calT_t`, `def: TTfunc`) was used where
the lemma has `T_{u,D}` (`def_WTuD`, 3_5:2296). With `calT` the factor `rho_eta` is real, but the paper
never claims that. Secondary: "regime (b) `1-t <= g^2/L^2`" is outside the hypothesis `1-t >= g^2`; the paper
handles it with the zero-mode-removing operator precisely because of the `rho`-growth of the zero mode
(3_5:1439-1440, 2251-2282). The 2D identity `r^2 M_s^{-2} = rho_ell^4 M_t^{-2}` (row 10) has as d >= 3
counterpart `rho^2 (W^d(1-s))^{-2} = (W^d(1-t))^{-2}` with `rho_ell = 1`.

(2) Correct d >= 3 statement: the paper's. Explicit Lean form (`0 <= s <= t < 1`, `g^2 <= 1-t`, periodic `l^infty`):

    T_{u,D}(r) := ((W^d)(1-u))^{-2} exp(-sqrt r) + W^{-D}                                    -- def_WTuD
    (∀ b, ‖A b‖ ≤ T_{s,D}(|b1-b2|)) → ∀ a, ‖(Uop A) a‖ ≤ C_d^2 · T_{t,D}(|a1-a2|) + ((1-s)/(1-t))^2 · W^{-D},
    C_d := 1 + Σ_{x ∈ Z^d\{0}} (2d/(2d+1))^{|x|_1} e^{sqrt|x|_1}   (or any constant from Prop5Decay at ell_t = 1).

Proof = §2: `Uop = P ⊗ P`, `P = (s/t)1 + ((t-s)/t)Theta_t >= 0`, row sum `rho` (`ukerNonneg`, `ukerRowSum`
already ported); amplitude identity; triangle inequality for `sqrt(zdistInf)`; Neumann bound on
`(1-t)Theta_t` (or `prop5Decay_holds`). No `uT_scalar`, no `ell_t/ell_s`, no `|a1-a2| >= ell*_t`. If the
2D `uopLocalMax` near/far route is kept, the near radius `ell*_t/4 = (log W)^{3/2}/4` costs
`e^{sqrt(ell*_t/2)} = W^{o(1)}` -- fine under `≺`, not a true constant; the direct proof is simpler and sharper.

(3) Impact on `lem:pf_step5`/Step 5: no gap. Stopping time `(eq:def_TTT)` at threshold `W^eps`, Duhamel from
s to fixed `t' <= t` for the stopped process, net + continuity in `t'` (as 2D `5-6:380-470`). Divided by
`T_{t',D}(|a1-a2|)`:
* initial term `U_{s,t'} o (L-K)_s`: `(Eq:Gdecay+IND_s<g)` + `B_{s,0} <= 2/(1-s)` give `|(L-K)_s| <= 4W^delta T_{s,D}`;
  `(neiwuj)` (linear in A): `≺ 4C_d^2 + rho^2 W^{-D+C}` (`rho <= (W^{-d}B_{t,0})^{-c_d} <= W^C` by `con_st_ind`).
  This is where 2D loses `(ell_t/ell_s)^4 1(|a1-a2| <= ell*_t)`; 3D loses nothing.
* `E^{(L-K)x(L-K)}`: `(res_deccalE_lk)` + `(neiwuj)` + `∫_s^{t'}(1-u)^{-2}du <= (1-t')^{-1}`:
  `≺ W^{2eps}(W^d(1-t'))^{-1} <= W^{2eps}(g^2 W^d)^{-1} <= W^{2eps-2fd}`.
* `E^{G̃}`: `(res_deccalE_wG)` second part `≺ W^{1.5eps} 2(W^d(1-t'))^{-1/2} <= W^{1.5eps-fd}`; the indicator part
  lives at `|b1-b2| <= (log W)^{3/2}`, after `U_{u,t'}` (range 1) at `|a1-a2| <= 3(log W)^{3/2}`, where
  `∫(1-u)^{-1}du <= log rho <= C log W`; or use Step 4 `(Eq:L-KGt-flow)` directly there:
  `(W^d(1-u))^{-2}/T_{u,D}(3(log W)^{3/2}) <= e^{sqrt3 (log W)^{3/4}} = W^{o(1)}`.
* martingale: BDG `(alu9_STime)` + `(res_deccalE_dif)` + `U ⊗ U` version of `(neiwuj)` for `e^{-2 sqrt r}`
  (amplitude `rho^4 (W^d(1-s))^{-4} = (W^d(1-t'))^{-4}`): `≺ W^{1.5eps}(W^d(1-t'))^{-1/4} + 1(|a1-a2| <= 6(log W)^{3/2})(log W)^{1/2}`.
Sum: `J*_{t'∧T} ≺ C + log W + W^{2eps - fd/2} < W^eps` for `eps < fd/4`, W large; so `T >= t` w.h.p. and
`(Eq:Gdecay+s<g_flow)` follows. Nothing must be absorbed by `B_{t,0}`, by `W^{-D}` or by another tail function;
the constant of `(neiwuj)` is absorbed by the `W^eps` threshold as in [YY_25]. A `rho` factor would appear only
if `calT` were used as tail function in this regime, which the paper does not do.

---

## 5. The paper is internally consistent about the `rho` factor

For `calT`/`wT` the paper knows the kernel costs `rho`: in the regime `g^2/L^2 <= 1-t <= 1-s <= g^2` it uses
`(eq:decompU)`, proves `(uwp2-92kj)` `(1-u) Σ_b Theta_t(a1,b) wT^L_{u,D}(|b-a2|) ≺ wT^L_{t,D-1}(|a1-a2|)`
(`TTT2`/`lem:propT`), and gets `(uwftgwesj)` `max_u A_{u,t,a} ≺ ((1-s)/(1-t)) W^{-d} wT^L_{t,D-2}(|a1-a2|)`
-- the team's `rho`, absorbed there via `(g^2 W^d)^{-1/4} rho^2 <= (g^2 W^d)^{-1/5}` (`con_st_ind`,
`c_d <= 10^{-2}`). For `1-t <= g^2/L^2` the zero mode grows like `rho` (3_5:1439) and is removed by `Q^{(1)}`
(3_5:2254-2282). Step 2's `(Eq:Gdecay_w)` even carries an explicit loss `((1-s)/(1-u))^{C_d}` for the
`calT` profile. Only for `1-t >= g^2` with `T_{u,D}` (amplitude `eta_u^{-2}`) is there no loss -- `TailtoTail`.

---

## 6. Recommendations for the Lean project

1. Retract the "possible genuine gap" note in DECISIONS §33; drop paper-delta candidate T2097a (or record
   "no delta; `T_{u,D}` was misread as `calT`").
2. Add `tailTD d W t D r := ((W:ℝ)^d * |1-t|)⁻¹^2 * exp(-√r) + W^(-D)` (`def_WTuD`) in `Defs/Tail.lean`, with a
   docstring: Step 5 (`1-t >= g^2`) tail function, not `calT`.
3. Port `tailtoTail` as in §4(2), hypotheses `0 ≤ s ≤ t < 1`, `g^2 ≤ 1-t` (DECISIONS §29 boundary check: no
   `t = 1`, `s ≥ 0`; `g = 0` allowed), via `ukerNonneg`, `ukerRowSum`, triangle inequality for `√(zdistInf)`,
   and the Neumann bound on `(1-t)Theta_t` or `prop5Decay_holds` at `ell_t = 1`. Constant free of `s,t,L,W,g`.
4. For `lem:pf_step5` (ST-D4) use it as in §4(3); the squared-profile version follows from the same proof
   with `e^{-√r}` replaced by `e^{-2√r}`.

---

## 7. Confidence

High (≈ 95%) that `(neiwuj)` is true as stated and the FAIL is a misidentified tail function: the text is
unambiguous (`def_WTuD` vs `def: TTfunc`, different symbols, the subsection's own amplitude explanation at
3_5:2288), the §2 proof is elementary and complete, and the exact-kernel numerics confirm both the lemma
(ratio `<= 1.36`) and the team's number for the other function (`53.63` vs `53.62`). Moderate-to-high (≈ 85%)
on the Step 5 closure sketch: a transcription of the 1D/2D argument with `ell ≡ 1`; I checked the integrals
and the absorption of the constant by `W^eps`, but took `lem_dec_calE` (`res_deccalE_lk/wG/dif`) as given.
