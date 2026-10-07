Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct  7 05:33:46 UTC 2026

### (i) Exponent table (d = 3, Λ = 10, nominal κ = 0.5; formulas as in the check file, section 2)

| quantity | value | constraint it must satisfy | slack |
|---|---|---|---|
| `ε = κ²/4` | 0.0625 | `ε ≤ |1−tm(σ)²|` and `1−|m|² ≤ (1−ε)|1−tm²|`, t∈[0,1] (`BAoffDiag_scalar`, `Ward.lean:202`) | numeric: flag `eps<=|D|` true for every t, σ, instance point (script below) |
| `C₀ = 16d²/κ³` | 1152 | `BAMB_upper_small` for `g < (2C₀)⁻¹` (`CombesThomas.lean:375`) | threshold `(2C₀)⁻¹ = 4.34e-4`; instance has g=5e-4 (κ=1: g < 3.5e-3 holds) on the small branch |
| `c₀ = min(log(1+κ/(4dΛ)), κ/2)` | 4.158e-3 | `0 < c₀ ≤ κ/2 ≤ 1/2` (κ ≤ Im m ≤ ‖m‖ ≤ 1); Target 5 needs `2c₀ ≤ 1 < log 4` and `c₀ ≤ 1` | `log 4 − 2c₀ = 1.378`; `1/c₀² = 5.8e4 ≥ 1` |
| `A = 4(C₀/c₀)²` | 3.070e11 | small branch: `4C₀²g² ≤ A g²` (needs c₀ ≤ 1); large branch (`g ≥ (2C₀)⁻¹`): `c₀⁻²·(2C₀g)² = A g²` | small branch slack factor `c₀⁻² = 5.8e4`; large branch equality |
| `S = expC(d−2, c₀)` | 2.055e13 | `Σ_x e^{−c₀|y−x|} ≤ S`, `d = (d−2)+2`, uniform in L (`RadialSum.lean:275`) | numeric T6 below: sums 2.1…3.6e3 vs `expC(1,c)` = 6.1e11, 9.9e4, 6.4e2 at c = .01, .5, 2 (L∈{4,8,16}) |
| `μ = min(c₀, ε²c₀/(2AΛ²S))` | 1.287e-32 | `0 < μ ≤ c₀` (convexity, T9, T8 `μ ≤ c`); `μ·AΛ²S/c₀ ≤ ε²/2` | `c₀/μ = 3.2e29`; second constraint tight by definition: `μAΛ²S/c₀ = 0.001953125 = ε²/2` |
| row-weighted constant `1−ε/2` | 0.96875 | T9: `t(1−|m|²) + (μ/c₀)AΛ²S ≤ (1−ε)|D| + ε²/2 ≤ (1−ε/2)|D|` using `|D| ≥ ε` | `(ε/2)|D| − ε²/2 ≥ 0`, i.e. zero slack at `|D| = ε` |
| T7 constant `2/ε²` | 512 | `V ≤ 2/(ε|D|) ≤ 2/ε²`; needs `(ε/2)|D|V ≤ 1` from `|D|V ≤ 1+(1−ε/2)|D|V` | — |
| T8 constant `2AS/ε³` | 5.17e28 | `|D||Θ_ya| ≤ t B (2/ε²) Σ_{x≠y}e^{−c r}`, `t≤1`, `|D| ≥ ε`, `−2cr−μψx ≤ −μψy − cr` (μ ≤ c) | — |
| `C = 2/ε² + 2AS/ε³` | 5.17e28 | `C ≥ 2/ε²` (a=0: bound `C(1+g²)`), `C ≥ 2AS/ε³` (a≠0: `C g² e^{−μ|a|}` with B = Ag²) | exact: C is the sum of the two requirements |
| dimension / size / coupling | d=3 (used: 2≤d), L ≥ 3, 0<g≤Λ, 0<κ, t∈[0,1] | premises of T2290 (`3 ≤ L`, `0<d`) and of the pin | `t<1` and `3≤d` beyond `2≤d` are not used |

Algebra checked by hand (no numerics needed): T5 small branch `(C₀g)^{2r} ≤ C₀²g²·4^{1−r}`; `4^{−r} ≤ e^{−2c₀r}`; T9 convexity
`e^{μr}−1 ≤ (μ/c₀)(e^{c₀r}−1)` for 0≤μ≤c₀ (also scanned: 0 violations in the script below); the `δ_ya` term is `e^{μψ(a)}=1` at `y=a`.
Nominal values: inline python re-evaluating the formulas (tool log): `C0=1152.0 c0=0.004158010148663677 A=3.07e11 S=2.0555e13 eps=0.0625 mu=1.2868e-32 C=5.170e28`.

### (ii) One concrete nondegenerate instance (all hypotheses of Targets 1-11 at once)

Data: d=3, Λ=10, `Ψ^{(B)}` = adjacency of Z_L^3 (`Adj`: `zdistD(x−y)=1`, `Gauss/BlockAnderson.lean:45`), dense `N=L³` matrices (N = 64, 216, 512),
`(g,E)` as listed, `m` = the root of `m = N⁻¹ tr(gΨ−E−m)⁻¹` with Im m>0 (Newton along η↓0 then η=0; residual column `res`),
`κ = Im m` (so `BAReal` holds; an earlier run of the same checks at `κ = Im m/2`, 12 of these points, also ended `ALL OK`), `t ∈ {0, .5, .9, .999, 1−1e-6, 1}` (endpoint t=1 included), both σ, all `a`/`y`.
Checked per point: T2 (`|M^{σσ}_{xy}| = |M_xy|²`), T3 (`diag M = m`, `diag Q = m(σ)²`), T4/Ward (`Σ_b|M_ab|²=1`), `κ ≤ Im m`, `|m| ≤ 1`, `g ≤ Λ`,
`ε ≤ |1−tq|`, `1−tQ` invertible (cond < 1e13: unit case), T5 (`max ratio ≤ 1`), T6, T9 (hypothesis of T7/T8, all rows y; `T9m` = min of `(1−ε/2)|D| − tΣ_{x≠y}e^{μr}|Q_yx|`),
T7 (`T7r = max |Θ_ya|/(2/ε² e^{−μ|y−a|}) ≤ 1`), T8 (`T8r`, y≠a), and the pin conclusion `|Θ_0a| ≤ C(1_{a=0}+g²e^{−μ|a|})` (`concl_r ≤ 1`).

Command (script in the session scratchpad, python3 + numpy 2.0.2, not Lean):
`cd <scratchpad>/T2308 && python3 inst2.py`   (6.9 s). Output (verbatim except that the columns `res`, `C` and `FAIL=[]` were cut for width; one row per point; `small=True` marks the branch `g<(2C₀)⁻¹`):
```
L=4 g=0.0005 E=0 m=-0.0000+1.0000i kap=1.0000 small=True c0=8.30e-03 A=1.2e+09 S=1.3e+12 mu=1.7e-27 T5=8.4e-10 T9m=0.875 T7r=3.1e-02 T8r=1.3e-24 concl_r=5.0e-24
L=4 g=0.002 E=0.5 m=-0.2500+0.9682i kap=0.9682 small=True c0=8.04e-03 A=1.6e+09 S=1.5e+12 mu=9.6e-28 T5=6.5e-10 T9m=0.883 T7r=2.7e-02 T8r=7.5e-25 concl_r=2.8e-24
L=4 g=0.02 E=0.5 m=-0.2494+0.9672i kap=0.9672 small=False c0=8.03e-03 A=1.6e+09 S=1.5e+12 mu=9.4e-28 T5=6.4e-10 T9m=0.883 T7r=2.7e-02 T8r=7.3e-25 concl_r=2.7e-24
L=4 g=1.5 E=0.5 m=-0.2353+0.5113i kap=0.5113 small=False c0=4.25e-03 A=2.6e+11 S=1.9e+13 mu=1.9e-32 T5=5.1e-13 T9m=0.506 T7r=2.1e-03 T8r=2.3e-30 concl_r=8.9e-30
L=4 g=3 E=6.6 m=-0.3267+0.4034i kap=0.4034 small=False c0=3.36e-03 A=1.7e+12 S=4.8e+13 mu=3.3e-34 T5=1.5e-14 T9m=0.336 T7r=8.3e-04 T8r=8.0e-33 concl_r=4.1e-32
L=4 g=10 E=0 m=+0.0000+0.5594i kap=0.5594 small=False c0=4.65e-03 A=1.3e+11 S=1.3e+13 mu=8.7e-32 T5=2.6e-14 T9m=0.574 T7r=3.1e-03 T8r=2.8e-31 concl_r=1.4e-30
L=6 g=0.003 E=0 m=-0.0000+1.0000i kap=1.0000 small=True c0=8.30e-03 A=1.2e+09 S=1.3e+12 mu=1.7e-27 T5=8.4e-10 T9m=0.875 T7r=3.1e-02 T8r=1.3e-24 concl_r=5.0e-24
L=6 g=1.5 E=0.5 m=-0.1900+0.2084i kap=0.2084 small=False c0=1.74e-03 A=3.4e+14 S=6.8e+14 mu=4.5e-39 T5=1.3e-16 T9m=0.084 T7r=5.9e-05 T8r=1.2e-37 concl_r=8.6e-37
L=6 g=3 E=3 m=-0.0147+0.4154i kap=0.4154 small=False c0=3.46e-03 A=1.4e+12 S=4.3e+13 mu=5.5e-34 T5=1.4e-14 T9m=0.320 T7r=9.3e-04 T8r=8.7e-33 concl_r=6.9e-32
L=8 g=1 E=0 m=-0.0000+0.4665i kap=0.4665 small=False c0=3.88e-03 A=5.3e+11 S=2.7e+13 mu=4.0e-33 T5=8.1e-14 T9m=0.402 T7r=1.5e-03 T8r=1.5e-31 concl_r=2.8e-30
L=8 g=0.5 E=2 m=-0.4349+0.4435i kap=0.4435 small=False c0=3.69e-03 A=8.0e+11 S=3.3e+13 mu=1.7e-33 T5=1.5e-13 T9m=0.438 T7r=1.2e-03 T8r=2.4e-31 concl_r=1.8e-30
L=6 g=3 E=0 m=+0.0000+0.3413i kap=0.3413 small=False c0=2.84e-03 A=6.5e+12 S=9.4e+13 mu=2.0e-35 T5=1.8e-15 T9m=0.217 T7r=4.2e-04 T8r=1.6e-34 concl_r=2.0e-33
L=8 g=3 E=7.7 m=-0.0011+0.1000i kap=0.1000 small=False c0=8.33e-04 A=1.2e+17 S=1.3e+16 mu=1.7e-44 T5=1.4e-20 T9m=0.019 T7r=3.1e-06 T8r=7.1e-45 concl_r=5.1e-43
L=6 g=1.5 E=6.3 m=-0.2295+0.2339i kap=0.2339 small=False c0=1.95e-03 A=1.3e+14 S=4.3e+14 mu=3.2e-38 T5=1.7e-16 T9m=0.108 T7r=9.4e-05 T8r=4.2e-37 concl_r=6.9e-36
ALL OK
```
Rows (L,g,E): the last two (8,3,7.7) and (6,1.5,6.3) are near-edge points (κ = 0.100, 0.234). All 14 points: FAIL list empty (stripped from the lines above), `ALL OK`.
T6, "two data, one model" (§66 (5)) and convexity: inline python (heredoc) that execs the definitions of `inst2.py` (tool log; abridged here, T6 lines are re-formatted):
```
T6 L=4  c=.01,.5,2: 6.2e+01<=6.1e+11, 1.7e+01<=9.9e+04, 2.1e+00<=6.4e+02  (all True)   L=8, L=16: all True
common kappa=0.1, Λ=10: (8,3,7.7) Im m=.1000, (4,.0005,0) Im m=1.0000, (6,1.5,6.3) Im m=.2339: all three give mu=1.706e-44 C=1.953e+41, fail=[]
convexity violations: 0     0.5 < log 4: True
```
(The `T6` lines are abridged from the printed output: for L=8, 16 the sums were 4.8e2, 44, 2.26 and 3.6e3, 64, 2.26, all below `expC`.)
External hypotheses: none (`BAReal`, `BASelf` are discharged as numerical solutions; no `Step2LocalPT`-type pin enters). The Lean instance `P : FlowPt 4 10` is a `.some`
(`MFixedPoint.lean:893`), so its numbers are not available here; the instance above is the same kind of datum (real-axis solution of `(self_m)`, Im m = κ >0) at d=3, L ∈ {4,6,8}.
Nondegeneracy: N = 64..512 points, `a` ranges over all of Z_L^3, both branches of T5 occur (`small=True` rows and `False` rows), t=1 included, g ∈ [5e-4, 10], κ ∈ [0.10, 1.0].
Note on size: `μ ≈ 1e-27…1e-44` and `C ≈ 2e23…2e41` are lossy (allowed by the pin and §18); the data (L, g, E, m, t) are not large, only the constants are.

### Verdicts (per target; all by the mathematics above plus the script)

- T1 (`BAp5s_A/S/rate/C`, `_C_pos`, `_rate_pos`): PASS. Positivity: `C₀>0`, `c₀>0` (`κ/(4dΛ)>0`, `κ/2>0`), `A>0`, `S>0` (`expC`, `c₀>0`), `ε>0`, hence `μ>0`, `C>0`.
- T2, T3 (`BAMss_ss_norm`, `BAMss_ss_diag`, `BAnorm_one_sub_tq_sigma`): PASS (σ=−: `Mᴴ_{ba} = conj M_{ab}`, symmetry `M_ab=M_ba`; `|1−t conj(m)²| = |conj(1−tm²)|`, t real). Script T2/T3 columns hold.
- T4 (`BAMss_row_offdiag_sum`): PASS: `Σ_{x≠y}|M_yx|² = 1−|m|²` from `Σ_b|M_yb|²=1` and `M_yy = m` (script `T4ward`).
- T5 (`BAMB_sq_off_le`): PASS, both branches (derivation in the table notes; `T5` ratios between 1.4e-20 and 8.4e-10, all ≤ 1). Needs `c₀ ≤ 1/2` and `x≠y` (r≥1).
- T6 (`BAsum_exp_decay_le`, 2 ≤ d): PASS; `sum_shift` re-indexes `α↦a−α`.
- T7 (`BApropQ_decay`): PASS. Row identity `(1−tq)Θ_ya − tΣ_{x≠y}Q_yxΘ_xa = δ_ya`; weights `v_y=e^{μψ(y)}|Θ_ya|`, `ψ(y)=zdistD(y−a)`; `e^{μψ(y)} ≤ e^{μ r_yx}e^{μψ(x)}` by `zdistD_add_le`, μ≥0;
  at a maximiser `|D|V ≤ 1 + (1−ε/2)|D|V`, so `V ≤ 2/(ε|D|) ≤ 2/ε²`; non-unit case `Θ=0`. Script `T7r ≤ 3.1e-2 < 1`.
- T8 (`BApropQ_offdiag`): PASS (derivation in the table row for T8; uses T7 for `Θ_xa`). Script `T8r ≤ 1.3e-24`.
- T9 (`BAp5s_row_weighted`): PASS (the `(1−ε)+ε/2` split in the table row; `T9m ≥ 0.019 > 0` at every point, tightest at the near-edge κ=0.1 point).
- T10 (`baProp5s_of_real`), T11 (`baProp5s_holds`): PASS. `a=0`: T7 at `y=a=0` gives `≤ 2/ε² ≤ C(1+g²)`; `a≠0`: T8 at y=0, `B=Ag²`, `zdistD(0−a)=zdistD a`, `≤ (2Ag²S/ε³)e^{−μ|a|} ≤ C g² e^{−μ|a|}`. Script `concl_r ≤ 5.0e-24`.
  Constants `C, μ` depend on `(d, Λ, κ)` only and are chosen before `L, g, E, m, t, σ, a` (§18, `1_2:1150`).
- Against the paper: `(prop:ThfadC_short)` is `1_2:1148`, BA constants may depend on `λ⁻¹` (`1_2:1150`): statement matches the pin; the route differs from `A:26-41` (weighted ℓ^∞ vs Neumann series), statement equal; `(eq:off_diagM)` `A:32-34` = `BAoffDiag_scalar` + T4; `(−,−)` is the entrywise conjugate of `(+,+)` (`Q^{−−}_{ab} = conj Q^{++}_{ab}`), `|1−t conj(m)²|=|1−tm²|`.
- Paper-delta candidate T2308a (confirmed numerically, not used): the convolution bound `Σ_b e^{−c|a₁−b|−c|a₂−b|} ≲ e^{−c|a₁−a₂|}` (`A:41`) holds only with a rate loss: the sum contains the geodesic box
  `∏(|Δ_i|+1)` points each equal to `e^{−c|a₁−a₂|}`. Script (`conv.py`, L=40, c=0.5, d=3, `a₂=(n,n,n)`), ratio `Σ/e^{−c|a|}` for n=1..8: 31.7, 72.2, 137.7, 234.2, 367.7, 544.1, 769.6, 1050.0 (unbounded). Harmless for `(prop:ThfadC_short)`.
- Unused premises to report: `t<1` (bound holds at t=1, checked), `3≤d` beyond `2≤d`.
- Overall: **PASS** for all targets (no false hypothesis set, every exponent closes, no missing input).

## (b) Script output — Wed Oct  7 05:55:51 UTC 2026

Branch t/T2308, commit e0064e5, author Jun Yin; worktree /Users/junyin/Lean_proof/RBM3D-wt/T2308. Scratch files (scripts, logs) are in the session scratchpad T2308/.

### b.1 Build and diff
```
$ lake build RBM3D.BA.Prop5Short 2>&1 | tail -1
Build completed successfully (3737 jobs).
$ git diff --stat main...t/T2308
 RBM3D/BA/Prop5Short.lean | 814 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   1 -
 2 files changed, 814 insertions(+), 1 deletion(-)
$ git diff main...t/T2308 -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-110
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.BA.BAProp5s, -- property 5, short form (`prop:ThfadC_short`) for `Θ_BA`: BA-P1 (T2197; T2161 b.2: owe
$ wc -l RBM3D/BA/Prop5Short.lean; grep -n "^import" RBM3D/BA/Prop5Short.lean
     814 RBM3D/BA/Prop5Short.lean
6:import RBM3D.BA.FlowPins
7:import RBM3D.BA.CombesThomas
8:import RBM3D.Defs.RadialSum
```

### b.2 Axioms (one #print axioms per declaration: 17 public declarations + 14 instance theorems)
```
$ lake env lean axioms.lean | sed -E "s/^.*(\[.*\])$/\1/" | sort | uniq -c
  31 [propext, Classical.choice, Quot.sound]
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/Prop5Short.lean
0
```

### b.3 Target statements (extracted by script from RBM3D/BA/Prop5Short.lean, line number : signature)
```
$ python3 -I extract2.py BAp5s_A BAp5s_S BAp5s_rate BAp5s_C   # the four definitions, with bodies
49: def BAp5s_A (d : ℕ) (Λ κ : ℝ) : ℝ := 4 * (BAct_C d κ / BAct_rate d Λ κ) ^ 2
52: def BAp5s_S (d : ℕ) (Λ κ : ℝ) : ℝ := RBM.expC (d - 2) (BAct_rate d Λ κ)
55: def BAp5s_rate (d : ℕ) (Λ κ : ℝ) : ℝ :=
  min (BAct_rate d Λ κ) ((κ ^ 2 / 4) ^ 2 * BAct_rate d Λ κ / (2 * BAp5s_A d Λ κ * Λ ^ 2 * BAp5s_S d Λ κ))
59: def BAp5s_C (d : ℕ) (Λ κ : ℝ) : ℝ :=
  2 / (κ ^ 2 / 4) ^ 2 + 2 * BAp5s_A d Λ κ * BAp5s_S d Λ κ / (κ ^ 2 / 4) ^ 3
$ python3 -I extract.py <the 13 theorem names>   # signatures up to ":="; sections use `variable (d L : ℕ) [NeZero L]`
77: theorem BAp5s_C_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAp5s_C d Λ κ :=
84: theorem BAp5s_rate_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAp5s_rate d Λ κ :=
99: theorem BAMss_ss_norm (g : ℝ) (z m : ℂ) (σ : Bool) (x y : Zd d L) :
    ‖BAMss d L (BAMB d L g z m) σ σ x y‖ = ‖BAMB d L g z m x y‖ ^ 2 :=
110: theorem BAMss_ss_diag (g : ℝ) (z m : ℂ) (h : BASelf d L g z m) (σ : Bool) (y : Zd d L) :
    BAMss d L (BAMB d L g z m) σ σ y y = (if σ then m else star m) ^ 2 :=
132: theorem BAnorm_one_sub_tq_sigma (t : ℝ) (m : ℂ) (σ : Bool) :
    ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖ = ‖1 - (t : ℂ) * m ^ 2‖ :=
121: theorem BAMss_row_offdiag_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (σ : Bool) (y : Zd d L) :
    ∑ x ∈ Finset.univ.erase y, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖ = 1 - ‖m‖ ^ 2 :=
159: theorem BAMB_sq_off_le (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (x y : Zd d L) (hxy : x ≠ y) :
    ‖BAMB d L g (E : ℂ) m x y‖ ^ 2
      ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (x - y) : ℝ))) :=
251: theorem BAsum_exp_decay_le (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (y : Zd d L) :
    ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) ≤ RBM.expC (d - 2) c :=
301: theorem BApropQ_decay (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t ε μ : ℝ)
    (hQ : ∀ y, Q y y = q) (hε : 0 < ε) (hεD : ε ≤ ‖1 - (t : ℂ) * q‖) (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (hrow : ∀ y, t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖
        ≤ (1 - ε / 2) * ‖1 - (t : ℂ) * q‖)
    (y a : Zd d L) :
    ‖PropThetaQ Q t y a‖ ≤ 2 / ε ^ 2 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) :=
395: theorem BApropQ_offdiag (Q : Matrix (Zd d L) (Zd d L) ℂ) (q : ℂ) (t ε μ B c S : ℝ)
    (hQ : ∀ y, Q y y = q) (hε : 0 < ε) (hεD : ε ≤ ‖1 - (t : ℂ) * q‖) (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hrow : ∀ y, t * ∑ x ∈ Finset.univ.erase y, Real.exp (μ * (zdistD d L (y - x) : ℝ)) * ‖Q y x‖
        ≤ (1 - ε / 2) * ‖1 - (t : ℂ) * q‖)
    (hB : 0 ≤ B) (hμc : μ ≤ c)
    (hQB : ∀ y x : Zd d L, x ≠ y → ‖Q y x‖ ≤ B * Real.exp (-(2 * c * (zdistD d L (y - x) : ℝ))))
    (hS : ∀ y : Zd d L, ∑ x : Zd d L, Real.exp (-(c * (zdistD d L (y - x) : ℝ))) ≤ S)
    (y a : Zd d L) (hya : y ≠ a) :
    ‖PropThetaQ Q t y a‖ ≤ 2 * B * S / ε ^ 3 * Real.exp (-(μ * (zdistD d L (y - a) : ℝ))) :=
500: theorem BAp5s_row_weighted (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ : Bool) (y : Zd d L) :
    t * ∑ x ∈ Finset.univ.erase y,
        Real.exp (BAp5s_rate d Λ κ * (zdistD d L (y - x) : ℝ))
          * ‖BAMss d L (BAMB d L g (E : ℂ) m) σ σ y x‖
      ≤ (1 - κ ^ 2 / 4 / 2) * ‖1 - (t : ℂ) * (if σ then m else star m) ^ 2‖ :=
608: theorem baProp5s_of_real (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ : Bool) (a : Zd d L) :
    ‖BATheta d L g E m t σ σ 0 a‖
      ≤ BAp5s_C d Λ κ * ((if a = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-BAp5s_rate d Λ κ * (zdistD d L a : ℝ))) :=
667: theorem baProp5s_holds (d : ℕ) (Λ κ : ℝ) : BAProp5s d Λ κ :=
```

### b.4 Compiled nonempty instances (namespace `RBM.BA.Prop5sInst`, d = 3, L = 4, Λ = 10, P = RBM.BA.MFixedPointInst.P)
```
$ grep -o "^theorem inst_[A-Za-z_]*" RBM3D/BA/Prop5Short.lean | sed "s/theorem //" | tr "\n" " "   # the 14 instance theorems (each compiled, axioms in b.2)
inst_sum_exp_decay inst_ss_norm inst_ss_diag inst_norm_sigma inst_row_offdiag_sum inst_sq_off_le inst_row_weighted inst_BApropQ_decay inst_BApropQ_offdiag inst_of_real_half inst_of_real_one inst_BAProp inst_C_pos inst_rate_pos 
$ python3 -I extract2.py inst_of_real_one inst_BAProp5s_closed   # full text of two of them (t = 1 endpoint; merged instance closed)
790: theorem inst_of_real_one :
    ‖BATheta 3 4 P.g0 P.E P.m0 1 false false 0 0‖
      ≤ BAp5s_C 3 10 P.m0.im * ((if (0 : Zd 3 4) = 0 then (1 : ℝ) else 0)
          + P.g0 ^ 2 * Real.exp (-BAp5s_rate 3 10 P.m0.im * (zdistD 3 4 (0 : Zd 3 4) : ℝ))) :=
  baProp5s_of_real 3 4 (by norm_num) (by norm_num) 10 P.g0 P.m0.im P.E P.m0 (by norm_num) P.g0_pos
    P.g0_le P.real.1.1 P.real 1 (by norm_num) (by norm_num) false 0
798: theorem inst_BAProp5s_closed : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]‖ ≤
      C * ((if (![1, 0, 0] : Zd 3 4) = 0 then (1 : ℝ) else 0) +
        P.g0 ^ 2 * Real.exp (-c * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ))) :=
  RBM.BA.FlowPinsInst.inst_BAProp5s (baProp5s_holds 3 10 P.m0.im)
```

### b.5 Registry pre-check (RBM3D.lean copy with `import RBM3D.BA.Prop5Short` after its last import line, as the hub does at merge, §3 (A) 4)
```
$ lake env lean precheck.lean > precheck.out; echo "exit $?"   # precheck.lean = RBM3D.lean + that import line + the final #assert_rbm_axioms
exit 0
$ grep -n "axiom audit:\|registry:" precheck.out | cut -c1-110; grep -c "BAProp5s" precheck.out
1:axiom audit: 8701 theorems, 2844 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
153:registry: 2 borrowed + 143 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) ca
0
$ git diff main...t/T2308 -- RBM3D/Test/Axioms.lean | grep -c "^-   .RBM"   # owed entries removed (b.1 shows the line)
1
$ lake build 2>&1 | grep -n "^error\|Build completed\|BAProp5s"   # worktree as committed: RBM3D.lean has no import of the new module
3697:error: RBM3D.lean:347:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
3698:  [RBM.BA.BAProp5s]
3702:error: build failed
```

### b.6 Check-file equality (scratch file = check file with `import RBM3D.BA.Prop5Short` + 17 examples, `lake env lean`)
```
$ grep -c "^example : RBM.BA.T2308Check" eqcheck.lean; grep -n "^example : RBM.BA.T2308Check.BAp5s_A\|^example : RBM.BA.T2308Check.baProp5s_holds" eqcheck.lean
17
227:example : RBM.BA.T2308Check.BAp5s_A = RBM.BA.BAp5s_A := rfl
243:example : RBM.BA.T2308Check.baProp5s_holds_pin := @RBM.BA.baProp5s_holds
$ lake env lean eqcheck.lean | grep -c error; echo exit
0
exit 0
```

### b.7 Greps
```
$ grep -c "Matrix.Norms" RBM3D/BA/Prop5Short.lean; grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/Prop5Short.lean   # §57 (3)
0
0
$ bash clash.sh | awk "{print \$2, \$3}" | sort | uniq -c   # 19 names (17 pinned, Prop5sInst, BP5_) in all other RBM3D Lean files and docs/tickets except T2308
  19 worktree=0 main=0
$ grep -c "^private theorem BP5_" RBM3D/BA/Prop5Short.lean; grep -c "^theorem BP5_\|^def BP5_" RBM3D/BA/Prop5Short.lean   # unpinned helpers: private, prefix BP5_
9
0
```

### Narrative (facts as in b.1-b.7 and the files)
- Delivered: 4 definitions + 13 theorems of Targets 1-11 in `RBM3D/BA/Prop5Short.lean` (814 lines, limit 1500), imports exactly FlowPins, CombesThomas, RadialSum;
  `baProp5s_holds : ∀ d Λ κ, BAProp5s d Λ κ` unconditional; statements equal the check file (b.6, 17 `rfl` examples, exit 0); the only merged file touched is `RBM3D/Test/Axioms.lean` (one registry line deleted).
- Route as in the ticket: weighted `ℓ^∞` maximum argument (`BApropQ_decay`: maximiser of `v y = e^{μ|y-a|}‖Θ_ya‖` by `Finite.exists_max`,
  unit / non-unit split by `Ring.inverse`), no `tsum`, no `Matrix` norm instance (b.7), no Neumann series. `(−,−)` runs through the same lemmas
  (`BAMss_ss_norm`, `BAMss_ss_diag`, `BAnorm_one_sub_tq_sigma`).
- Target 5 small branch: `1/4 ≤ e^{-2c₀}` is proved from `Real.add_one_le_exp` (`e^{-x} = (e^{-x/2})² ≥ (1-x/2)²`, `0 ≤ x ≤ 1`), so no extra Mathlib import is needed.
- Target 9: `e^{μr} = 1 + (e^{μr}-1)`; unweighted part by `BAMss_row_offdiag_sum` + `BAoffDiag_scalar`; weighted part by the convexity bound `BP5_exp_sub_one_le`,
  `BAMB_sq_off_le`, `BAsum_exp_decay_le` and the definition of `BAp5s_rate`; `ε²/2 ≤ (ε/2)|D|` closes with zero slack at `|D| = ε`, as (a) predicted.
- Premises used: `2 ≤ d`, `0 < Λ`, `0 < κ`, `3 ≤ L` (only through `BAMB_sq_off_le`, i.e. T2290), `0 < g ≤ Λ`, `BAReal`, `0 ≤ t ≤ 1`.
  Not used: `t < 1` (`baProp5s_of_real` takes `t ≤ 1`; instance `inst_of_real_one` is the endpoint `t = 1`) and `3 ≤ d` beyond `2 ≤ d`. The pin is unchanged.
- Constants `BAp5s_C`, `BAp5s_rate` depend on `(d, Λ, κ)` only and are chosen before `L, g, E, m, t, σ, a`; they are lossy (see (a): `μ ≈ 1e-27 … 1e-44`), which the pin allows (§18).
- Registry: the owed line `RBM.BA.BAProp5s` is deleted (b.1), no line is added. Pre-check (b.5): exit 0, `BAProp5s` has 0 hits in its output.
  The committed worktree's own `lake build` stops at the root audit with `[RBM.BA.BAProp5s]` only because the hub-owned `RBM3D.lean` does not yet import the module
  (hub step §3 (A) 4); I did not edit `RBM3D.lean`. `git merge-tree --write-tree main t/T2308` (main 3c11598): exit 0, no conflict (the branch base is ec3f678).
- I did not re-run the numeric check of Preflight (v); the table is in the ticket and the preflight's run is in (a) (lines 36-52 of this report).

## (c) Verified Mathlib names used (`#check @name`, `lake env lean names.lean`, exit 0; signatures in the scratchpad `names.out`)
`Ring.inverse_non_unit`, `Ring.mul_inverse_cancel`, `Finite.exists_max`, `convexOn_exp`, `Finset.add_sum_erase`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.erase_subset`,
`Finset.ne_of_mem_erase`, `Finset.sum_sub_distrib`, `Finset.sum_ite_eq`, `norm_sum_le`, `norm_add_le`, `Complex.norm_conj`, `Complex.norm_real`, `Complex.im_le_norm`,
`Real.exp_le_exp`, `Real.exp_nat_mul`, `Real.one_le_exp`, `Real.add_one_le_exp`, `pow_le_pow_left₀`, `mul_le_of_le_one_left`, `le_div_iff₀`, `div_le_iff₀`, `div_le_one`,
`inv_mul_cancel₀`, `mul_inv_cancel₀`, `Matrix.conjTranspose_apply`, `Matrix.mul_apply`, `abs_of_nonneg` (all exist). Not used: `Real.exp_one_lt_d9` (exists, in `Mathlib.Analysis.Complex.ExponentialBounds`).
Deprecated (replaced by `ite_false`/`ite_true`/`↓reduceIte`): `if_false`, `if_true`, `if_neg`.

## (d) Open issues and paper-delta candidates — Wed Oct  7 05:57:28 UTC 2026
1. For the hub at merge: add `import RBM3D.BA.Prop5Short` after the last `import` line of `RBM3D.lean` (b.5 shows the pre-check green with it), then the full `lake build`.
2. Stale text, not edited (§57 (1)): docstring of `BAProp5s`, `RBM3D/BA/FlowPins.lean:180-181` ("the BA proof is the Taylor expansion `(eq:expMLn)`"); the T2197 registry comment block above the owed list in `RBM3D/Test/Axioms.lean:141`.
   `inst_BAProp5s` (`FlowPins.lean:1222`) keeps its hypothesis `h`; `Prop5sInst.inst_BAProp5s_closed` closes it with `baProp5s_holds`.
3. For BA-P7/BA-P8 consumers: `baProp5s_of_real` (explicit constants, `t ≤ 1`) is the `(σ,σ)` input of `A:50`; `baProp5s_holds` supplies the field `short` of `BAProp5to8`. Nothing for `(+,-)` or `BAProp8` is proved here.
4. **T2308a (paper-delta candidate, confirmed, not used by this route):** `A_deterministic_estimates.tex:41` states the convolution bound
   `Σ_b e^{-c|a₁-b|-c|a₂-b|} ≲ e^{-c|a₁-a₂|}` at the same rate `c`; it holds only with a rate loss (`c → c/2`): every `b` of the `ℓ¹`-geodesic box contributes exactly `e^{-c|a₁-a₂|}`.
   Script `conv1d.py` (`d = 1`, `L = 400`, `c = 0.5`, `a₁ = 0`, `a₂ = a`), ratio `Σ_b / e^{-c|a|}` for `a = 1,2,4,8,16,32,64`:
   `3.164, 4.164, 6.164, 10.164, 18.164, 34.164, 66.164` (each equals `a + 2.164`: unbounded); the preflight's `d = 3` run (a), lines 80-81 of this report, gives `31.7 … 1050.0` for `n = 1..8`.
   This Lean route does not use the convolution bound; `BAProp5s` is proved without it.
5. Route remark (not a delta): weighted `ℓ^∞` estimate instead of `(eq:expMLn2)`; `(−,−)` by the same lemmas, where the paper treats `(+,+)` only.
