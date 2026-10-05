Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 15:31:06 UTC 2026

Notation (d = 3): x = 1-u, g = ilambda, `Bc_u := W^{-d}B_{u,0} = W^{-d}[(g²+x)^{-1} + (L^d x)^{-1}]` (merged `Sizes.Bctl`), `G := (g²W^d)^{-1/5}`, target `T_t := Bc_t²(G + Bc_t)` (`1_2:1390-1396`). Scripts in `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2191`.

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| target exponent | `2 + 1/5` (G term), `3` (Bc term) | `G ≥ Bc_t` so `T_t ≍ Bc_t²G` | all 12 rows below: `G ≫ Bc_t` (closest: I n=0, `G=0.4353`, `Bc_t=0.0186`) |
| `(Exp(L-K)1)` `6:58` | `11/5 = 2 + 1/5` | `Bc_u^{1/5} ≤ C·G` iff `g²B_{u,0} ≤ C^5`; (i),(ii): `g²B ∈ [1/2,2]` (`consts.py`), (iii): `g²B ≤ 1+L^{-d}`; so `C = 2^{1/5}` | exponent slack 0, constant 1.15; **false in (iv)** (`g²B = 2.55` at IV n=0, unbounded as x→0) so (iv) uses `(Exp(L-K)2)` only |
| LW, `(eq:ExpLWn=2)` `6:83` | `5/2` (x ≥ g²/L^d) | `≥ 11/5` | 3/10 |
| `(eq:boundELKQ1)`, `(boundcommutator)` | `3` | `≥ 11/5` | 4/5 |
| `(Exp(L-K)2)`, `(ExpLWn=2_smalleta)` | `x^{-1}(N x)^{-3} = W^dL^d(Nx)^{-4}` (x ≤ g²/L^d) | `Bc_t ≥ (N x_t)^{-1}`; `∫((1-u)/(1-t))² x^{-1}(Nx)^{-3} ≤ (N x_t)^{-3} ≤ Bc_t³` | 4/5 over 11/5 |
| `u`-integral, (iii),(iv), kernel `((1-u)/(1-t))²` | `x^{2-1-11/5} = x^{-6/5}` ⇒ `∫ ≤ 5x_t^{-1/5}`; `5/2`: `x^{-3/2}` | exponent `> -1` | 1/5 resp. 1/2: no `log` |
| `u`-integral, (i),(ii) (`Bc_u` ≍ const, `g²B ∈ [1/2,2]`) | `∫ x^{-1}dx = log(x_s/x_t)` ≤ `2 log L` (i), `(d-2) log L` (ii) | `≺` absorbs `log L ≤ N^τ` | `log` is `≺`, not a tracked loss (0.693 at the instances) |
| initial term (iii) | kernel `(x_s/x_t)²` (`sum_res_Ndecay`, n=2) vs `Bc_s²/Bc_t²`: `x·B(x) = x/(g²+x)+L^{-d} ∈ [1/2, 1+L^{-d}]` | ratio `≤ 4(1+1/27)² = 4.30` | **closes with no `𝔠_d` loss** (answer to preflight (iii)); `G+Bc_s ≤ G+Bc_t` |
| initial term (iv) | same, `x·B ∈ [L^{-d}, 2L^{-d}]` | ratio `≤ 4` | closes, no `𝔠_d` loss |
| initial term (i), `σ₁=σ₂` / `σ₁≠σ₂` | `(sum_res_2_NAL)`: `((g²+x_s)/(g²+x_t))^1`; `(sum_res_2)` on `Q`-part: `^2` | `≤ 2`, `≤ 4` (`x_s ≤ g²`) | `L^∞`-only: at the extreme `(x_s/x_t)² = Bc_t^{-2𝔠_d} ≥ W^{4𝔡𝔠_d}/4^{𝔠_d}` (`g²B ≤ 2`, `g²W^d ≥ W^{2𝔡}`), a power of `W`, not `≺`-absorbable |
| initial term (ii) | `(sum_res_Ndecay_nonzero)` (`3_5:1667`), `A ⊃ I_diff(σ)` | no ratio | `L^∞`-only loss `Bc_t^{-2𝔠_d}` removed. **F1 below** for `σ₁=σ₂` |
| `(ℓ_t^d x_t)^{-1} ≤ C B_{t,0}` (regime (i) `P`-term `(eq:EPL-K)`) | (i): `x^{d/2-1}g^{-d} ≤ g^{-2}`; (ii),(iv): `=(L^dx)^{-1}`; (iii): `x^{-1}` | `g²B ≥ 1/2` | C = 2; numerics 0.21 (I), 0.34 (II), ≈1.0 (III), 0.61 (IV) |
| `(Nη_t)^{-1} ≤ Bc_t / Im m` (regime (ii) Ward term) | `η_t = x_t Im m`, `(N x_t)^{-1} ≤ Bc_t` | `Im m ≥ c(κ)` (bulk) | `Im m(E+i0) = 0.968` at the instances; ratio 0.22 (I), 0.35 (II), ≤0.016 (III), 0.63 (IV) |
| `Σ_b B_{u,|b|}e^{-(|b|/ℓ_u)^{1/2}} ≲ x^{-1}` (`(Exp(L-K)1)` `6:58`) | `K`-power `d-2 = 1`; (i): `g^{-2}ℓ² = x^{-1}` | absolute constant | `(1-t)S_t` = 1.43, 1.00, 0.70 (I, II, IV, same for n=0,10,100); III: 9.1, 170.9, 258.0 at n=0,10,100 (L = 4, 44, 404), bounded in `L` by the convergent series `Σ_r shell_r e^{-√r}/(r+1)` |
| `𝔠_d ≤ 1/100` | window `(1-t)/(1-s) ≥ Bc_t^{𝔠_d} ≥ W^{-1}` (needed by `STEKWin`, `Step34Pins.lean:607-610`) | `d·𝔠_d < 1` | `d𝔠_d ≤ 0.03`, slack 0.97; **Step 6 adds no further upper bound on `𝔠_d`** (all kernel ratios above are constants) |
| `(eq:WO)`, `𝔡 = 1/10` | `W^{-3/2+1/10} ≤ lam ≤ 10` | `lam > 0` | min over 12 rows of `lam/W^{-3/2+1/10}` = 2 (so `lam n > 0`, `G` finite, nonzero) |
| RBM2D bound replaced | `(scaleM^2)⁻¹` (`Evolution/Defs.lean:123`), `(scaleM^3)⁻¹` (`:141`, commit `c9a24cf`) | | → `Bc_t²(G+Bc_t)` |

(F1) **Regime (ii), `σ₁=σ₂`.** `6:97` says `(sum_res_2_NAL)`, but `lem:sum_decay` (`3_5:1637`) needs `t ≤ 1-g²/L²`; the merged window `STEKWin` (`Step34Pins.lean:607-610`) and `ekSumDecayNAL_holds` (`SumDecay.lean:435` derives `g²/L² ≤ 1-t` from its hypotheses) derive this, while regime (ii) has `1-s ≤ g²/L²`: both together give `1-t = 1-s = g²/L²`, i.e. `s = t`, excluded by `s < t`. Fix that closes: `(sum_res_Ndecay_nonzero)` with `A = ∅` (`I_diff(σ)=∅`; `3_5:1667`; `stek_nonzero_holds` `Prec.lean:422`, `zeroModeSet_empty` `ZeroModeCalc.lean:119`), regime (ii) has `1-s ≤ g²/L²`. Paper-delta candidate `T2191a`.

Numerics, 4 Step-5 instances × `n ∈ {0,10,100}` (`init = K·T_s/T_t` with the kernels of the table; `Linf = (x_s/x_t)²`; drift columns = `∫ K(u)·drift(u) du / T_t`; "extreme" = fixed point `x_t = Bc(x_t)^{𝔠_d}x_s`, `𝔠_d = 1/100`, in-regime in all rows):
```
$ cd $S && python3 final.py
reg  n      W        Bc_t        G        T_t   | init=K*T_s/T_t Linf=(xs/xt)^2 | drift/T_t: D1(11/5) D3(5/2) D4(3)  [D2 if x<=g2/L^3] | extreme x_t=Bc^c x_s: xt*/xs  (xs/xt*)^2  Linf-init
  I   0         4  1.861e-02   0.4353  1.572e-04 |    0.807    4.000   |   6.06e-01 1.79e-01 2.35e-02      |  0.9595  1.0862  1.066
  I  10        14  4.341e-04   0.2053  3.876e-08 |    0.812    4.000   |   6.30e-01 6.03e-02 1.21e-03      |  0.9242  1.1708  1.131
  I 100       104  1.059e-06   0.0616  6.911e-14 |    0.812    4.000   |   6.31e-01 9.94e-03 9.84e-06      |  0.8703  1.3202  1.242
 II   0         4  2.296e-02   0.4353  2.417e-04 |    0.651    4.000   |   5.62e-01 1.76e-01 2.53e-02      |  0.9610  1.0827  1.060
 II  10        14  5.356e-04   0.2053  5.904e-08 |    0.657    4.000   |   5.90e-01 5.97e-02 1.31e-03      |  0.9257  1.1670  1.121
 II 100       104  1.307e-06   0.0616  1.052e-13 |    0.657    4.000   |   5.92e-01 9.85e-03 1.07e-05      |  0.8718  1.3158  1.224
III   0        32  3.305e-05   0.6598  7.208e-10 |    1.000    1.138   |   1.23e-02 5.53e-04 3.13e-06      |  0.9023  1.2282  1.000
III  10  5.15e+06  7.793e-21   0.1565  9.505e-42 |    1.000    1.138   |   3.90e-05 3.58e-11 3.11e-21      |  0.6319  2.5046  1.000
III 100  3.36e+11  2.804e-35   0.0414  3.253e-71 |    1.000    1.138   |   1.90e-07 8.13e-18 4.23e-35      |  0.4546  4.8390  1.000
 IV   0         4  1.595e-03   0.2287  5.860e-07 |    1.417    2.250   |   5.30e-04 5.30e-04 2.96e-03 D2   |  0.9358  1.1419  1.064
 IV  10        14  3.721e-05   0.1078  1.493e-10 |    1.419    2.250   |   2.64e-05 2.64e-05 1.47e-04 D2   |  0.9015  1.2306  1.102
 IV 100       104  9.077e-08   0.0324  2.667e-16 |    1.419    2.250   |   2.14e-07 2.14e-07 1.20e-06 D2   |  0.8491  1.3870  1.162
```
All `init` ≤ 1.42, all drift ratios ≤ 0.64: every term closes against `T_t` with an absolute constant; `G = (g²W^d)^{-1/5} > 0` in all 12 rows (IV n=0: 0.2287; I n=0: 0.4353).

### (ii) Concrete instance, identity, hypotheses

Instances (ticket item 7): I `szB (7/8,15/16)`, II `szB (15/16,31/32)`, III `sz0 (0,1/16)`, IV `szG (5/8,3/4)`; `d=3`, `κ=ε=1/10`, `𝔡=1/10`, `𝔠=1/6`; regimes of the table recomputed by `exps.py::regime`. Hypotheses checked by script (`python3 wo.py`: `WO`, `Bandwidth` `N^{1/6} ≤ W`, `N^{-9/10} ≤ η`, all 12 rows true; `python3 lemt.py`): `lemT(1/2+i/64) = |m|² = 0.98399 ≥ 31/32` (`zB`), `lemT(z0)` at `n=0` = 0.99999095 `≥ 1/16`.

(F2) **`(con_st_ind)` `1_2:1296`** (`Defs.lean:168`, eventually in n; `𝔠_d` is produced by the theorem and smaller `𝔠_d` is harder). Limit: `Bc_t = B_{t,0}/W³ → 0` along `W = n+4` (szB, szG; `B_{t,0}` constant) and along `sz0`, hence `Bc_t^{𝔠_d} → 0 < (1-t)/(1-s)`. Numerics at `𝔠_d = 1/100` (largest allowed):
```
$ cd $S && python3 const.py
I  mandated (szB,7/8,15/16)        ratio=0.5000 regime=  I  holds n=0,10,100: [False, False, False]  needs W >= 1.15e+10  (B_t0=1.191)
I  alt      (szB,14/15,15/16)      ratio=0.9375 regime=  I  holds n=0,10,100: [False, True, True]  needs W >= 9.11  (B_t0=1.191)
II mandated (szB,15/16,31/32)      ratio=0.5000 regime= II  holds n=0,10,100: [False, False, False]  needs W >= 1.23e+10  (B_t0=1.470)
II alt      (szB,15/16,241/256)    ratio=0.9375 regime= II  holds n=0,10,100: [False, True, True]  needs W >= 9.16  (B_t0=1.211)
III mandated (sz0,0,1/16)          ratio=0.9375 regime=III  holds n=0,10,100: [True, True, True]  needs W >= nan  (B_t0=1.083)
IV mandated (szG,5/8,3/4)          ratio=0.6667 regime= IV  holds n=0,10,100: [False, False, False]  needs W >= 3.46e+05  (B_t0=0.102)
IV alt      (szG,5/8,83/128)       ratio=0.9375 regime= IV  holds n=0,10,100: [True, True, True]  needs W >= 3.76  (B_t0=0.084)
```
So at the mandated times of I, II, IV the hypothesis holds only for `W ≥ 1.15e10, 1.23e10, 3.46e5` at `𝔠_d = 1/100` (symbolic limit only). Alternative times (all other hypotheses unchanged: `t ≤ lemT`, regimes as printed) give a numeric witness at `n = 10, 100` (I', II') and `n = 0,10,100` (IV'); III holds at all `n`. Proposed instance times: I' `(14/15, 15/16)`, II' `(15/16, 241/256)`, IV' `(5/8, 83/128)`, III as mandated.

**Regime-(ii) Ward decomposition `6:138-140`** (`tr = Tr`, `E_a = W^{-d}1_{[a]}`, `N=(WL)^d`, `η_t` real; `K` = model tensor `κ W^{-d}δ_{a₁a₂}`, `κ = Im m/η`, `K^{(1)} = m`, satisfying `(WI_calK)`): identity `f − Q^{(1)}Q^{(2)}f = Im[tr(G̃(E_{a₁}+E_{a₂})) − N^{-1}tr G̃]/(Nη)`, `f = L−K`, `G̃ = G−m`; `P^{(i)} f = Im tr(G̃E_{a_{3-i}})/(Nη)` by `(WI_calL)` and `L^{-d}/(W^dη) = 1/(Nη)`:
```
$ cd $S && python3 ward.py
d=3 L=3 W=1 N=  27 sigma=(+,-)  max|f - Q12 f - Im[tr(G~(E_a1+E_a2)) - N^-1 tr G~]/(N eta)| = 2.26e-16  (size of f - Q12 f: 8.23e-02)
d=3 L=3 W=1 N=  27 sigma=(-,+)  max|f - Q12 f - Im[tr(G~(E_a1+E_a2)) - N^-1 tr G~]/(N eta)| = 2.29e-16  (size of f - Q12 f: 1.23e-01)
d=3 L=3 W=1 N=  27 sigma=(+,+)  max|f - Q12 f - Im[tr(G~(E_a1+E_a2)) - N^-1 tr G~]/(N eta)| = 2.81e-01  (size of f - Q12 f: 1.82e-01)
d=3 L=3 W=2 N= 216 sigma=(+,-)  max|f - Q12 f - Im[tr(G~(E_a1+E_a2)) - N^-1 tr G~]/(N eta)| = 2.73e-17  (size of f - Q12 f: 3.60e-03)
d=3 L=3 W=2 N= 216 sigma=(-,+)  max|f - Q12 f - Im[tr(G~(E_a1+E_a2)) - N^-1 tr G~]/(N eta)| = 4.03e-17  (size of f - Q12 f: 3.51e-03)
d=3 L=3 W=2 N= 216 sigma=(+,+)  max|f - Q12 f - Im[tr(G~(E_a1+E_a2)) - N^-1 tr G~]/(N eta)| = 1.76e-02  (size of f - Q12 f: 1.40e-02)
```
The formula and the normalisation `N^{-1}tr(G−M)` of `6:138-140` hold for `σ₁≠σ₂`; the `(+,+)` rows are a control (identity not claimed there). Sign of the `ϑ̇` term at `6:115`: `∂_u(Q_u f_u) = Q_u∂_u f_u − (𝒫f_u)∂_uϑ_u` from `Q_u = I − 𝒫ϑ_u` (`3_5` `(eq:sumzero_op)`), so `−` is consistent.

Other scripts (`cd $S`): `python3 consts.py` → `(iii) sup (x_s B_s)^2/(x_t B_t)^2 = 4.000 (bound 4.302)`, `(iv) 4.000 (bound 4)`, `(i),(ii) g²B_{u,0} ∈ [0.500, 2.000]`; `python3 shell.py` (n=100) → `(1-t)S_t` = 1.427 (I), 1.001 (II), 258.008 (III), 0.695 (IV).

### Verdicts
- Pins `STExp2U`, `STStep6R` (I-IV), `STStep6` and the exponent table (items 2, 3): **PASS**; the exponents close in all four regimes with constants only; no `𝔠_d` loss in (iii),(iv); (i),(ii) need `(sum_res_2_NAL)/(sum_res_2)/(sum_res_Ndecay_nonzero)`, not `L^∞`. Regime (ii) `σ₁=σ₂`: use `(sum_res_Ndecay_nonzero)` at `A = ∅` (F1).
- Compiled skeleton and `STMainInd` (item 5): no mathematical obstruction from Step 6 (it adds no constraint on `𝔠_d` beyond `d𝔠_d < 1`): **PASS** on that; the Lean fit of Steps 1-5 (`STStep1Weak`, ranges of `s`) is not examined in this stage.
- Instances (item 7): **PASS** with the alternative times I', II', IV' (F2); as specified (mandated I, II, IV) the `(con_st_ind)` witness is numerically astronomic at `𝔠_d = 1/100` (symbolic limit only).
- Overall: **PASS**.

## (a′) Preflight corrections — Mon Oct  5 17:30:05 UTC 2026

- Replay (Mon Oct  5 16:58:49 UTC 2026): `python3 final.py` and `python3 ward.py` reproduce the pasted blocks of (a) line for line; `python3 const.py` reproduces its seven rows (its header line is not pasted in (a)); `diff` of the saved outputs.
- Refinement, no change of verdict: lines 18-19 of (a) bound the initial-term ratio by 4.30 (iii) and 4 (iv); the Lean closing comparison has the constant 4 in both: `(1-s)B_s ≤ 2(1-u)B_u` (`st6_xB_III`, `st6_xB_IV`), `((1-s)/(1-u))² T_s ≤ 4 T_u` (`st6_cmp_ini`), at the boundary data `inst_cmp_III`, `inst_cmp_IV`.
- (F2) The Lean instances use the mandated times of I, II, IV, not I', II', IV': `STConStInd` is `∀ᶠ n` (`Induction/Defs.lean:168`); it is discharged for every `𝔠_d > 0` by the merged `conStInd_const` (`szB`, `szG`) and `sz0_con` (`sz0`).
- The reserve of verdict 2 of (a) ("the Lean fit of Steps 1-5 ... is not examined") is answered in (b): `ST_mainInd_of_steps` compiles with no change to a merged signature; one finding on `STStep2Concl` (F-shape, (d)).
- New data for item 7, not in (a): `(szFour, zB, 0, 49/50)`, `L = 3`, `ilambda = 4/5`, `W_n = n + 6` (`szFour`): `1-ilambda² = 9/25 < 1-ilambda²/L² = 209/225 < 1-ilambda²/L^3 = 659/675 < 49/50 ≤ lemT zB` (`lemT_zB_hi`; (a) line 52: `lemT zB = 0.98399`), so all four regimes lie in one interval; `(con_st_ind)` at ratio `1/50`.
- Citations of (a) F1: `lem:sum_decay` begins at `3_5:1632` (the hypothesis `t ≤ 1-ilambda²/L²` is the line `3_5:1637`); `SumDecay.lean:435` is `RBM3D/Evolution/SumDecay.lean:435`, inside `ekSumDecayNAL_holds` (`:420`).

## (b) Script output (branch `t/T2191` head `96c6b4c`, probe 2348 lines; commands ran in `/Users/junyin/Lean_proof/RBM3D-wt/T2191`, except the RBM2D `git` command (main worktree `/Users/junyin/Lean_proof/RBM3D`, where `../RBM2D` exists); scripts and outputs: portmap P.10, `final_run.sh`)

```
$ lake build RBM3D.Probe.T2191Pins 2>&1 | grep -E "T2191Pins|Build completed"
✔ [3845/3845] Built RBM3D.Probe.T2191Pins (7.1s)
Build completed successfully (3845 jobs).
$ grep -c "^warning: RBM3D/Probe" <the build log above>
0
$ lake env lean RBM3D/Probe/T2191Pins.lean; echo "exit code $?"
exit code 0
$ grep -c -E "\bsorry\b|\badmit\b|native_decide|^axiom |^\s*axiom " RBM3D/Probe/T2191Pins.lean
0
$ git rev-list --count 0818c49..t/T2191
17
$ git diff --stat 0818c49 t/T2191
 RBM3D/Probe/T2191Pins.lean | 2348 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2348 insertions(+)
$ git status --short | wc -l
       0
$ python3 axioms.py   # `#print axioms` of every public theorem of the probe (Lean run on a generated file)
print-axioms lines: 142; public theorems declared in the probe: 142; theorems without a line: []; errors: 0
[propext, Classical.choice, Quot.sound] : 142 declarations
last line: 'RBM.Gauss.Step6Inst.inst_mollifier_family' depends on axioms: [propext, Classical.choice, Quot.sound]
$ python3 axtargets.py | head -9   # raw `#print axioms` of the endpoint theorems (30 lines in total)
'RBM.Gauss.Sizes.STExp2_of_STExp2U' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6R_of_any' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6R_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_mainInd_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6_caseI_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6_caseII_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6_caseIII_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step6_caseIV_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Target statements, extracted by script (`python3 stmts.py RBM3D/Probe/T2191Pins.lean 230 <names>`; all 41 pins and the theorems in full: portmap P.2c, P.2d; pin table with consumers (probe line), tickets, instances: P.2)
```
L81: def STExp2U (E s t : ℕ → ℝ) : Prop := Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω ∂(sz.seqP)) - STKloop sz n (E n) (p.1 : ℝ) p.2.1  ...
L121: def STIngR6 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ ( ...
L136: def STStep6R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := STIngR6 d R (fun sz E s t => STStep6Concl sz E s t)
L141: def STStep6I (d : ℕ) : Prop := STStep6R d STReg5I
L144: def STStep6II (d : ℕ) : Prop := STStep6R d STReg5II
L147: def STStep6III (d : ℕ) : Prop := STStep6R d STReg5III
L150: def STStep6IV (d : ℕ) : Prop := STStep6R d STReg5IV
L155: def STStep6 (d : ℕ) : Prop := STStep6R d STAny
L97: theorem STExp2_of_STExp2U {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2U sz E s t) : STExp2 sz E t
L351: theorem ST_mainInd_of_steps (h1 : STStep1 d) (h2 : STStep2 d) (h3 : STStep3 d) (h4 : STStep4 d) (h5 : STStep5 d) (h6 : STStep6 d) : STMainInd d
L1452: theorem ST_step6_caseI_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d) (hIni : STExpIniI d) (hInt : STE ...
L1370: theorem ST_step6_caseII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hInt : STExpIntII d) (hWd : STExpWardII d) : STStep6II d
L1242: theorem ST_step6_caseIII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hDu : STExpDuhamelZ d) (hInt : STExpIntIII d) : STStep6III d
L1291: theorem ST_step6_caseIV_of_pins (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hLo : STExpDriftLo d) (hInt : STExpIntIV d) : STStep6IV d
L236: theorem st6_precU_of_forall_seq (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {W : ℕ → Type*} (F G : ∀ n, ℝ → W n → ℝ) (h : ∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → sz.Prec (U
L1062: theorem st6_expAvgU_of_pin (hAvg : STImproveExpAver d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀  ...
L1076: theorem st6_EGtHi_of_LW (hLW : LWtermEXP d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ le ...
L105: def STStep2Core (E s t : ℕ → ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t
L1645: def STRegSeq (R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop := ∃ m : ℕ → ℝ, (∀ n, s n < m n) ∧ (∀ n, m n < t n) ∧ R₁ sz s m ∧ R₂ sz m t
L1650: theorem ST_step6_compose {R₁ R₂ : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (h₁ : STStep6R d R₁) (h₂ : STStep6R d R₂) : STStep6R d (STRegSeq R₁ R₂)
L1729: theorem ST_step6R_mono {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STStep6R d R) : STStep6R d R'
L1684: theorem ST_step6_four_of_regimes (h1 : STStep6I d) (h2 : STStep6II d) (h3 : STStep6III d) (h4 : STStep6IV d) : STStep6R d (STRegSeq STReg5III (STRegSeq STReg5I (STRegSeq STReg5II STReg5IV)))
L1690: def STGenericPos {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop := ∀ n, 0 < sz.lam n ∧ s n < 1 - sz.lam n ^ 2 ∧ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d < t n
L1694: theorem st6_genericPos_regSeq (hd : 3 ≤ d) {s t : ℕ → ℝ} (h : STGenericPos sz s t) : STRegSeq STReg5III (STRegSeq STReg5I (STRegSeq STReg5II STReg5IV)) sz s t
L1722: theorem ST_step6_generic_of_regimes (h1 : STStep6I d) (h2 : STStep6II d) (h3 : STStep6III d) (h4 : STStep6IV d) : STStep6R d STGenericPos
L1585: theorem st6_restrict_GdecayW {E s t s' t' : ℕ → ℝ} (hs : ∀ n, s n ≤ s' n) (ht : ∀ n, t' n ≤ t n) (h : STGdecayW sz E s t 0) : STGdecayW sz E s' t' 0
L1596: theorem st6_GdecayW_of_zero (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) {Cd : ℝ} (hCd : 0 ≤ Cd) (h : STGdecayW sz E s t 0) : STGdecayW sz E s t Cd
L1233: theorem st6_F1_window_vs_reg5II {s t : ℕ → ℝ} (hI : STCaseI sz s t) (hII : STReg5II sz s t) (n : ℕ) : t n ≤ s n
```

### Compiled nonempty instances at `d = 3` (`python3 insts.py`; stochastic premises and the pins of other gates stay hypotheses)
```
67 public instance theorems (RBM.Gauss.Step6Inst), by data:
  own data (deterministic pin / lemma): 28: inst_ing6 inst_improveExpAver inst_expHier inst_duhamelZ inst_duhamelQ inst_precU inst_cover_two inst_restrict inst_GdecayW_of_zero inst_F1 inst_bridges inst_endpoints inst_assembly6 inst_exp
  (szB, zB, 7/8, 15/16)  regime (i): 12: inst_ing6_I inst_step6I inst_step6_atI inst_hiI inst_expLKLK_I inst_expDriftDecay inst_expWardI inst_expIniI inst_expIntI inst_skeleton6I inst_step6R_mono inst_step6R_of_any
  (szB, zB, 15/16, 31/32) regime (ii): 8: inst_ing6_II inst_step6II inst_hiII inst_expLKLK_II inst_expWardII inst_expIntII inst_skeleton6II inst_ini_nonzero
  (sz0, z0, 0, 1/16)     regime (iii): 8: inst_ing6_III inst_step6III inst_step6 inst_hiIII inst_expLKLK_III inst_expIntIII inst_skeleton6III inst_cmp_III
  (szG, zB, 5/8, 3/4)    regime (iv): 6: inst_ing6_IV inst_step6IV inst_expDriftLo inst_expIntIV inst_skeleton6IV inst_cmp_IV
  (szFour, zB, 0, 49/50) all four regimes (generic position): 4: inst_genericPos inst_genericPos_regSeq inst_four inst_generic
  (szB, zB, 7/8, 31/32) two stages (i)+(ii) cut at 15/16: 1: inst_compose
regime inequalities in exact fractions (g = ilambda; L = 4, except szFour: L = 3):
  szB      regime (i) : g^2=1 g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/16 1-s=1/8 | (i) g2/L2<=1-t<=1-s<=g2: True | (ii) g2/L3<=1-t<=1-s<=g2/L2: False | (iii) g2<=1-t: False | (iv) 1-s<=g2/L3: False
  szB      regime (ii): g^2=1 g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/32 1-s=1/16 | (i) g2/L2<=1-t<=1-s<=g2: False | (ii) g2/L3<=1-t<=1-s<=g2/L2: True | (iii) g2<=1-t: False | (iv) 1-s<=g2/L3: False
  sz0 n=0  regime (iii): g^2=1/4096 g^2/L^2=1/65536 g^2/L^3=1/262144 1-t=15/16 1-s=1 | (i) g2/L2<=1-t<=1-s<=g2: False | (ii) g2/L3<=1-t<=1-s<=g2/L2: False | (iii) g2<=1-t: True | (iv) 1-s<=g2/L3: False
  szG      regime (iv): g^2=25 g^2/L^2=25/16 g^2/L^3=25/64 1-t=1/4 1-s=3/8 | (i) g2/L2<=1-t<=1-s<=g2: False | (ii) g2/L3<=1-t<=1-s<=g2/L2: False | (iii) g2<=1-t: False | (iv) 1-s<=g2/L3: True
  szFour (L = 3, ilambda = 4/5): boundaries 1-g^2 = 9/25, 1-g^2/L^2 = 209/225, 1-g^2/L^3 = 659/675; s = 0 < 9/25 < 209/225 < 659/675 < t = 49/50: True
  A = g^2 W^d at sz0 n=0: (1/64)^2 * 32^3 = 8 ; G = A^(-1/5) = 0.6598
```

### Name clashes, inventory, split, ports
```
$ python3 clash.py
new public declarations in the probe: 191 (49 def, 142 theorem); distinct short names 191; namespaces: ['RBM.Gauss.Sizes', 'RBM.Gauss.Step6Inst']
(1) RBM3D worktree (base 0818c49, Probe excluded): short names occurring in 0 files: []
(2) RBM3D main checkout (HEAD 9eb0502, may hold uncommitted work): hits []
(3) RBM2D working tree: hits [] ; RBM1D: hits []
$ python3 inv.py summary
file                lines(c9a24cf) kept(c9a24cf) lines(HEAD 9e0f275) kept(0c1330a,T2002) class | public thm/def | occurrences Z2 scaleM ellT "log L" | lines W^2 L^2
Step61                1021        933          939              948     c |   1/1   |    81    10     2    13 |   13   11
MLExpVocab            1349       1213          760              774     c |  60/17  |    37    34     0     0 |   15    6
MLExpHier              731        648          670              673     c |   4/0   |    29     0     0     0 |    0    0
MLExpDuhamel           532        474          448              461     c |  25/0   |    59     0     0     0 |    0    0
MLExpDrift            1673       1545         1597             1614     c |   5/0   |    99    20    26     0 |   27   39
MLExpInv               878        766          815              818     c |  13/2   |   103     0     0     0 |    0    4
MLExpQ                1669       1533         1539             1558     c |  71/5   |   144    60    46    19 |   14    5
TOTAL                 7853       7112         6768             6846     c | 204 public decls
Evolution/Defs.lean:107-145 (oneLoopExpErr, expLoopErr, Step61Concl, DecayLoopPT, MLExpConcl): 219 lines in file, 39 lines in range, kept 32; occurrences Z2=5 W^2=0 L^2=0 scaleM=2 ellT=1 log L=0
$ python3 split.py   # table: portmap P.5
tickets 13; est lines 14000; mean 1076; min 700; max 1500
roles: {'prover': 3, 'prover-hard': 7, 'prover-max': 3} | risk: {'low': 2, 'medium': 5, 'medium-high': 3, 'high': 3}
DECISIONS §9 O2: ST-5 = 1 design + 13 proof tickets = 14: band under 25 (25/40/50): question to Jun: no
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/Step61.lean RBM2D/Evolution/MLExpVocab.lean RBM2D/Evolution/MLExpHier.lean RBM2D/Evolution/MLExpDuhamel.lean RBM2D/Evolution/MLExpDrift.lean RBM2D/Evolution/MLExpInv.lean RBM2D/Evolution/MLExpQ.lean RBM2D/Evolution/Defs.lean
 RBM2D/Evolution/Defs.lean         | 130 ++-----
 RBM2D/Evolution/MLExpDrift.lean   | 124 ++-----
 RBM2D/Evolution/MLExpDuhamel.lean | 126 ++-----
 RBM2D/Evolution/MLExpHier.lean    |  95 +----
 RBM2D/Evolution/MLExpInv.lean     | 107 ++----
 RBM2D/Evolution/MLExpQ.lean       | 196 ++--------
 RBM2D/Evolution/MLExpVocab.lean   | 757 +++++---------------------------------
 RBM2D/Evolution/Step61.lean       | 130 ++-----
 8 files changed, 251 insertions(+), 1414 deletions(-)
$ grep -rn "StrictMono\|[Ss]ubseq" RBM3D | grep -vc "^RBM3D/Probe/"
0
```

### Narrative
1. Deliverables: probe `RBM3D/Probe/T2191Pins.lean` (2348 lines, only file changed against `0818c49`); portmap `docs/reports/T2191-portmap.md` (items 1, 3, 4, 6 in full, statements of all pins P.2c-P.2d, scripts P.10).
2. Result: 191 new public declarations (49 def, 142 theorem); all 142 theorems on the three standard axioms; no `sorry`/`admit`/`native_decide`/`axiom`; `lake build` and `lake env lean` give no diagnostic for the probe.
3. Pins (item 2): 41 `Prop` defs, 20 owed (each with its S6 ticket and compiled consumer, P.2), 21 structural, none borrowed.  Target `STExp2U` = `(Eq:Gtlp_exp_flow)` uniform in `u`; endpoint `STExp2_of_STExp2U` (consumer `Induction/Defs.lean:304`; UN `Universality/Pins.lean:428-436`).
4. Shape: `STIngR6` is `STIngR5` without the premises Step 6 does not use (`STKbound`, `STKward`, `STDecayStrong s`, `STDecayStrongU`, `STStep1Loop`) and with `STStep2Core` for `STStep2Concl … C_d`, so no `∀ C_d` (T2191b); then every premise restricts to a sub-interval (`st6_restrict_*`).
5. `lem:improve_exp_aver`: per time `STImproveExpAver` with both premises of the paper (`LWAvgLaw`, `STLK` at `u`).  `STExpAvgU` and `(eq:ExpLWn=2)` uniform in `u` are compiled from the per-time pins `STImproveExpAver`, `LWtermEXP` by (g) `st6_precU_of_forall_seq` and the bridges `*_at` (no separate LW bridge ticket).
6. Drift `D_u = 𝔼ℰ^{LK×LK} + 𝔼ℰ^{G̃}` uses the merged `STELKLK`, `STEGt`; the rotation bridge `STEGt = LWE` is compiled (`st6_EGt_eq_LWE`, a copy of the private `STB_EGt_eq_LWE`, `Induction/Step2Events.lean:1294`).
7. Duhamel forms (item 2 (c)): `STExpDuhamelZ` at `A = ∅` (plain) and `A = {1,2}` (`zeroModeSet univ`), `STExpDuhamelQ` (`𝒬_u`, commutator, `-(𝒫 f_u)∂_uϑ_u`); from `s`, deterministic at fixed size.  `(normQA2)` at `A = {1,2}` is the merged `norm_zeroModeSet_le` (`inst_normQA2`).
8. Skeletons (item 5): `ST_step6_caseI..IV_of_pins` (`𝔠_d` = minimum of the pins' constants; initial terms (iii), (iv) from `stek_sumNdecay_holds`, (ii) from `stek_nonzero_holds`; constant 4); `ST_mainInd_of_steps` compiles from `STStep1..STStep6` with no change to a merged signature.
9. Assembly mismatches (item 5b), none blocking: `STStep1Weak` is consumed only by `STStep2` (`STStep1Loop` by Steps 2-5); Steps 1-2 take `s ≤ lemT` besides `s < t ≤ lemT` (implied); `STStep2` is `∃ C_d ∃ 𝔠_d`, Steps 3-5 `∀ C_d ∃ 𝔠_d`, Step 6 `∃ 𝔠_d`; `STKbound`, `STKward` come from `stKbound_of_flow`, `stKward_of_flow`.
10. Glue: `ST_step6_compose` (two stages cut at one intermediate time), instance `inst_compose` at `(szB, zB, 7/8, 31/32)` cut at `15/16`; `ST_step6_four_of_regimes` (stages (iii), (i), (ii), (iv)) and `ST_step6_generic_of_regimes` (`STStep6R d STGenericPos`: every `[s_n,t_n]` contains `1-ilambda²`, `1-ilambda²/L²`, `1-ilambda²/L^d`), instances `inst_four`, `inst_generic` at `(szFour, zB, 0, 49/50)` (`L = 3`, `ilambda = 4/5`, all four regimes inside `[0, lemT zB]`).  **NOT compiled**: `STStep6` for arbitrary `(s,t)` (owed pin, S6-13): the nonempty stages depend on `n`, a pin needs `s_n < t_n` and `(con_st_ind)` for every `n`, and `RBM3D/` has no subsequence transfer for `Sizes` (grep above); (d) 1.
11. Mathematics: regime (ii), `σ₁ = σ₂` needs `(sum_res_Ndecay_nonzero)` at `A = ∅` (F1, T2191a; compiled negative statement `st6_F1_window_vs_reg5II`, `inst_F1`); (iii), (iv) close with constant 4, no `𝔠_d` loss, and their `u`-integrals have no `log` (`x^{-6/5}`, `x^{-3/2}`, `x^{-4}`) whereas in (i), (ii) `∫ x⁻¹ dx` is `≤ 2 log L`, `(d-2) log L`, absorbed by `≺` (the ticket's "no `log`" holds for (iii), (iv) only); (i), (ii) cannot use the plain `(sum_res_Ndecay)` (it loses `(W^{-d}B_{t,0})^{-2𝔠_d}`, a power of `W`); `(eq:Exp(L-K)1)` is not usable in (iv) (`g²B_{u,0}` unbounded), `(eq:Exp(L-K)2)` is; the Ward decomposition `6:138-140` holds for `σ₁ ≠ σ₂` (section (a), `ward.py`).
12. `𝔠_d`: Step 6 adds no bound beyond `d 𝔠_d < 1` for the kernel window (`st_EKWin`, `ScaleFacts3.lean:466`).  `(eq:WO)` gives `0 < lam n` eventually (`st6_lam_pos`), so `(ilambda² W^d)^{-1/5} ≠ 0` (`inst_G_pos_*`; `ilambda² W^d = 8` at `sz0`, `n = 0`: `inst_A_value`); at `lam n = 0` the target would be `(W^{-d}B)^3` (`st6_target_lam_zero`): no defect of the merged `STExp2`.
13. Inventory (item 1): seven files, 7853 lines, 7112 kept at `c9a24cf` (the ticket's per-file figures; its header figure 6846 is the T2002 column), class c; 26 imported modules, each with an RBM3D replacement (P.1e) except `Evolution/XiBounds` (missing: the short-row bound is replaced by the merged `ekSameRow_holds`, no `log L`) and `Path/ScalesBridge` (none: one scale `Bctl`); `MLExpInv` not ported (merged `stExpInv_holds`); `d = 2` exponents occur in 1271 of 1673 lines of `MLExpDrift` and 892 of 1669 of `MLExpQ` (re-derived), 584 lines of `MLExpQ` are type-only (port `Z2 → Zd d`).
14. Split (item 6): 13 proof tickets S6-01…S6-13, 14000 estimated lines (700-1500 each, table in P.5); ST-5 = 14 with the design ticket, below the 25 band of DECISIONS §9 O2: no question to Jun.
15. Ports (CLAUDE.md §5.2): `st6_mE_im_ge` ports `MLExpVocab_im_ge` (`RBM2D/Evolution/MLExpVocab.lean:384`, `c9a24cf`; `spectralM → mE`); statements `STExpErr`, `STExpDrift`, `STExpQsrc`, `STExpHier`, `STExpDuhamelZ`, `STExpDuhamelQ` correspond to `expErrT :57`, `expDriftT :62`, `qDriftT :70`, `ExpHierPin :111`, `ExpDuhamelPin :124`, `ExpQDuhamelPin :131` (same file), `STExpAvgAt` to `Step61Concl` (`Evolution/Defs.lean:120`) and `Step61Pin` (`Step61.lean:843`); RBM1D: nothing ported; each statement re-derived at `d ≥ 3`.

## (c) Verified Mathlib names (each resolved by Lean with its module: `python3 mathlibnames.py`, one line per name in portmap P.9 (125 lines); the non-trivial ones, by top directory of `Mathlib/`)
- `Mathlib/Algebra/`: Finset.sum_add_distrib, Finset.sum_const, Finset.sum_le_sum, abs_nonneg, abs_of_pos, add_nonneg, div_le_div_of_nonneg_left, div_le_iff₀, div_le_one, div_lt_div_of_pos_left, div_lt_self, div_mul_eq_mul_div, div_nonneg, div_one, inv_anti₀, inv_lt_one_of_one_lt₀, inv_mul_eq_div, inv_one, le_div_iff₀, mul_comm, mul_inv, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, nsmul_eq_mul, one_le_pow₀, one_pos, pow_le_pow_left₀, pow_lt_pow_right₀, pow_nonneg, sq_abs, sq_nonneg, zero_le_one, zero_pow.
- `Mathlib/Analysis/`: Real.exp_pos, Real.one_le_rpow, Real.pow_rpow_inv_natCast, Real.rpow_le_rpow, Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow_of_nonpos, Real.rpow_neg, Real.rpow_neg_one, Real.rpow_nonneg, Real.rpow_one_add', Real.rpow_pos_of_pos, Real.rpow_zero, Real.sqrt_eq_rpow, Real.sqrt_le_sqrt, Real.sqrt_one, Real.sqrt_sq, Real.zero_rpow, norm_add_le, norm_le_pi_norm, pi_norm_le_iff_of_nonneg.
- `Mathlib/Basic/`: ENNReal.ofReal_le_ofReal, ENNReal.ofReal_lt_ofReal_iff, ENNReal.ofReal_mul, ENNReal.ofReal_natCast, ENNReal.ofReal_one.
- `Mathlib/Data/`: Finset.card_univ, Fintype.card_fin, Fintype.ofFinite, Nat.cast_nonneg, Nat.le_add_right, Nat.le_self_pow, Nat.pow_le_pow_left, Set.mem_empty_iff_false, Set.mem_ofPred_eq.
- `Mathlib/LinearAlgebra/`: Matrix.trace_mul_comm.
- `Mathlib/MeasureTheory/`: MeasureTheory.measure_iUnion_fintype_le, MeasureTheory.measure_mono.
- `Mathlib/Order/`: Filter.Eventually.of_forall, Filter.eventually_ge_atTop, Filter.not_eventually, Filter.tendsto_atTop_mono, lt_min, lt_of_le_of_lt, lt_of_lt_of_le, lt_trans, min_le_left, min_le_right, not_lt, tendsto_natCast_atTop_atTop.
- Deprecated in this Mathlib (message of `lake env lean`): `dif_pos` ("Use `dite_eq_left` instead"; the probe uses `simp only [..., ↓reduceDIte]`), `Set.mem_setOf_eq` ("Use `Set.mem_ofPred_eq` instead"; used).  Names verified absent: none recorded.

## (d) Open issues and paper-delta candidates
- **T2191a** (`6:97`, regime (ii), `σ₁ = σ₂`): the paper cites `(sum_res_2_NAL)`, whose lemma `lem:sum_decay` (`3_5:1632-1637`) needs `t ≤ 1-ilambda²/L²`, which with `1-t < 1-s ≤ ilambda²/L²` forces `s = t`.  Lean: `(sum_res_Ndecay_nonzero)` (`3_5:1667`) at `A = ∅` (`I_diff = ∅`: `STExpIntII`, `st6_Idiff_same`).
- **T2191b** (shape): the Step-6 pins drop `STKbound`, `STKward`, `STDecayStrong s`, `STDecayStrongU`, `STStep1Loop`, take `STStep2Core` for `STStep2Concl … C_d`, and have no `∀ C_d` (the paper's Step 6 uses none of them).
- **T2191c** (`6:12-21`): `lem:improve_exp_aver` is pinned per time sequence `u` (both premises at `u`); the paper's form uniform in `[s,t]` is `STExpAvgU`, compiled from it by (g) for a deterministic left side.
- **T2191d** (`6:104-132`, `6:137-141`): the Ward bounds `(eq:EPL-K)`, `(eq:boundELKQ1)`, `(eq:boundcommutator)` and the regime-(ii) decomposition are pinned uniformly in `u ∈ [s,t]` (paper: at `t`), the first three for every mollifier family with `STMollifierProps` eventually (paper: the one of `Def:QtPt`).
- **T2191e** (`1_2:1390-1396`): `max_{σ,a}` of `(Eq:Gtlp_exp_flow)` is the union over `(u,σ,a)` inside `Prec` at scale `N` (merged convention); `lam n > 0` only eventually (`(eq:WO)`).
1. General `STStep6` from the four regime pins (S6-13) is compiled only in generic position (`ST_step6_generic_of_regimes`).  Options for S6-13: (A) split `ℕ` into the finitely many patterns of nonempty stages and transfer a pin to a subsequence of the sizes (`Sizes d` has five fields, `Defs/Sizes.lean:138`; no transfer on `main`); (B) restate the regime pins with the regime condition inside the index set (as `LWtermEXP`).  The merged `STStep3R`, `STStep4R`, `STStep5R` carry `STStep2Concl … C_d`, whose loss `((1-s)/(1-u))^{C_d}` does not restrict to a start `s' > s`: not checked whether S5-29 meets it.
2. S6-03: RBM2D's `Step61Pin` uses `(Eq:L-KGt)` at `k = 1` only (`Step61.lean:841-845`); the pin keeps the paper's two premises, `LWAvgLaw` being the `k = 1` case of `STLK`; the prover may drop `STLK`.
3. Risks: S6-12 (regime (ii): no RBM2D source), S6-09 (1500 lines), S6-13; `STExpLKLKHi` needs the new lattice sum `Σ_b B_{u,|a₁-b|} e^{-(|a₁-b|/ℓ_u)^{1/2}} ≲ (1-u)^{-1}` (S6-06).  `(con_st_ind)` at the mandated times of I, II, IV holds numerically only for `W ≥ 1.15e10, 1.23e10, 3.46e5` at `𝔠_d = 1/100` ((a) F2); the instances do not need it (premise eventual).
4. Premises from other gates, all with a proving ticket: `LWtermEXP` (LW-14), `STStep2..STStep5`, `STLK`, `STDecay`, `STExp2` at `s`, `STStep2Core`, `STLmaxU`, `STLKU`, `STGdecayW`; `STStep1` is proved (`stStep1_holds`).
- Registry (DECISIONS §16, §20), proposed: **owed** (20): `STExp2U`, `STStep6I`, `STStep6II`, `STStep6III`, `STStep6IV`, `STStep6`, `STImproveExpAver`, `STExpHier`, `STExpDuhamelZ`, `STExpDuhamelQ`, `STExpLKLKHi`, `STExpDriftLo`, `STExpDriftDecay`, `STExpWardI`, `STExpWardII`, `STExpIntIII`, `STExpIntIV`, `STExpIntII`, `STExpIntI`, `STExpIniI`; **structural** (21): `STStep2Core`, `STRegSeq`, `STGenericPos`, `STIngR6`, `STStep6R`, `STStep6Concl`, `STExpAvgAt`, `STExpAvgU`, `STExpDuhEq`, `STExpDuhEqQ`, `STDriftHi` and the ten `*Concl` predicates; **borrowed**: none.
