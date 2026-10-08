Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 02:15:10 UTC 2026

### (i) Exponent table
`K_ab = ‖M_ab‖²`, `M = (gΨ − E − m)⁻¹`, `Ψ` = adjacency of `Z_L^d` (`PsiB`), `BAReal d L g κ E m = BASelf ∧ κ ≤ Im m`.
Values at instance B (d=3, L=4, Λ=10, g=1.5, E=0.5, κ=Im m=0.511322); instance A (g=0.003) in brackets.

| quantity | value (B) [A] | constraint | slack |
|---|---|---|---|
| `C = 16d²/κ³` (`BAct_C`) | 1077.16 [158.649] | `C>0` (κ>0, d>0) | none needed |
| `(2C)⁻¹` small-g threshold | 4.64e-4 [3.152e-3] | `g < (2C)⁻¹` only for `BAK_le_small`, `BAK_adj_ge_small` | A: g=0.003 < 0.0031516 (margin 5%); B not small (the all-g Target 9 covers it) |
| `c = min(log(1+κ/(4dΛ)), κ/2)` | 4.252e-3 [8.036e-3] | `c>0`; `c ≤ κ/2 ≤ 1/2` | `c⁻² = 5.53e4 [1.55e4] ≥ 1 ≥ K_aa`, so `BAK_le_decay` holds on the diagonal too (`K_aa=‖m‖²≤1`) |
| `A = 4(C/c)²` (`BAp5s_A`) | 2.567e11 [1.559e9] | `K_ab ≤ A g² e^{−2c‖a−b‖}`, `a≠b` | measured max `K/(A g² e^{−2cr})` = 5.1e-13 [6.5e-10] |
| `S = expC(d−2,c) = 256(1+24/c⁴)` at d=3 | 1.880e13 [1.473e12] | `Σ_x e^{−c‖y−x‖} ≤ S`, needs `2 ≤ d`, uniform in `L` | huge (`c` small) but finite; bound is lossy only |
| exp-moment rate `μ` | `0 ≤ μ ≤ c` | `e^{μr}e^{−2cr} ≤ e^{−cr}` | slack `c·r ≥ 0` per entry, `r ≥ 1` off diagonal |
| exp-moment RHS `‖m‖²+A g² S` | 1.09e25 [2.07e16] | `≥ Σ_b K_ab e^{μr}` | LHS = 1.012 (μ=c) [1.000]: slack enormous, the data (`K`, `m`, `g`) are of ordinary size; only the *constant* is large |
| laziness `κ² ≤ ‖m‖² ≤ 1` | B: `0.261 ≤ 0.317 ≤ 1`; A: `0.937 ≤ 1.000 ≤ 1` (script prints True) | `κ ≤ Im m ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`, real `E`) | strict |
| scalar `(κ/2)(1−‖m‖²) ≤ ‖1+(E+m)m‖` | ratio 3.873 [2.066] | `κ ≤ Im m`, `‖m‖ ≤ 1`; proof: `Re w=s+u p`, `Im w=u q`, `s=1−‖m‖²`, split `|u| ≤ s/2` (then `Re w ≥ s/2 ≥ κ s/2` since `κ≤1`) else `|Im w| = q|u| ≥ κ s/2` | ratio ≥ 2 (2.0003 min over 2e6 random samples, sweep below); factor 2 spare |
| neighbour count | `card N = 2d = 6` | `3 ≤ L` (`card_adj`) | `L=4` ok; `L≥3` needed for `±e_i` distinct |
| Target 9 `Σ_{b∼a}K_ab ≥ (κ(1−‖m‖²))²/(8dg²)` | ratio 14.999 [4.267] | `(Σ‖M‖)² ≤ 2d Σ‖M‖²`, `Σ_{b∼a}‖M_ab‖ ≥ ‖1+(E+m)m‖/g ≥ (κ/2)s/g` | min ratio over 138-point sweep d∈{1,2,3}: 4.00003 (factor 4 = the two losses `(κ/2)²`, `1/(2d)`); all-g, no small-g restriction |
| small-g lower `(C⁻¹g)² ≤ K_ab`, `a∼b` | min ratio 2.52e4 [A] | `g < (2C)⁻¹`, `Adj` | sweep min 256.0 (22 small-g points) |
| small-g upper `K_ab ≤ (Cg)^{2r}` | max ratio 0.99995 [A] (r=0: `K_aa=‖m‖²≈1`) | `g < (2C)⁻¹` | tight at r=0 only (`‖m‖²≤1`, exact `(Cg)^0=1`) |
| `d`, `L`, `g`, `Λ` ranges | d=3, L=4, g∈(0,10], Λ=10 | `0<d` (all but exp-moment: `2 ≤ d`), `3 ≤ L` (tails, neighbour), `0<g≤Λ` (tails only), `g>0` (`BAMB_adj_sum`, Target 9) | `3 ≤ d` never used; no `t`, no law |

Statement-truth review (paper `7_8:1857, 1867-1871, 1888-1904`, `A:18-19, 59`, `1_2:1070-1071`) against the check file
`docs/tickets/checks/T2317-check.lean` Section 3, by hand and by the sweep:
- `BAMss true false a b = M_ba · (Mᴴ)_ab = M_ba conj(M_ba) = ‖M_ba‖² = ‖M_ab‖²` (symmetry); `BAMss false true a b = conj(M_ab) M_ab = ‖M_ab‖²`; all four charge pairs have norm `‖M_ba‖‖M_ab‖ = K_ab`. True.
- `BAMB_adj_sum` is the `(a,a)` entry of `(gΨ−E−m)M = 1`: `g Σ_{c∼a}M_ca − (E+m)m = 1`, `M_ca=M_ac`, `g≠0`. True for every `g>0`.
- `BAK_exp_moment_le`: off-diagonal `K_ab e^{μr} ≤ A g² e^{−cr}`, `Σ_{b≠a} ≤ S` (orientation `zdistD(a−b)` matches `BAsum_exp_decay_le`), diagonal `K_aa=‖m‖²`. True.
- `BAK_pow_*`: `n=0` is `1` (row sum 1, shift-invariant, symmetric); induction preserves all four. True.
- Pin quantifier/binder orders in the check file are consistent with the merged signatures read in the worktree (`BAMB_sq_off_le`, `BAMB_decay_large`, `BAMB_upper_small`, `BAMB_lower_small`, `BAMB_resolvent_row`, `BAsum_exp_decay_le`, `card_adj`).
- No external hypothesis: every target is unconditional given `BASelf`/`BAReal` (merged D3/D4/P1 lemmas); so no limit computation is owed.

### (ii) One concrete nondegenerate instance
Data: d=3, L=4 (64 sites), Λ=10; A: g=0.003, E=0.5 (small branch); B: g=1.5, E=0.5; C: same as B with κ=Im m/2.
`m` solves `(self_m)` by Newton on the 64×64 spectrum (residual ≤ 2.3e-16, `Im m>0`), `M` is the dense inverse; every hypothesis
(`BASelf`, `κ ≤ Im m`, `0<g≤Λ`, `3≤L`, `2≤d`, `0<d`) is printed at the point. `‖m‖²` is 0.317 (B), 1.000 (A), `g` is 0.003 (A, inside the small branch) or 1.5 (B, C), no empty index, no collapsed window.

Command: `python3 rep.py` (scratch `…/scratchpad/T2317/rep.py`; numpy 2.0.2), output verbatim:
```
[A] g=0.003 E=0.5 m=-0.249987+0.968221j kappa=0.968221 Lam=10.0
  HYP: BASelf resid=2.3e-16, Im m>0:True, 0<kappa<=Im m:True, 0<g<=Lam:True, 3<=L:True, 2<=d:True, small branch g<(2C)^-1:True
  CONST: C=158.649 c=0.00803614 A=1.55899e+09 S=expC(1,c)=1.4732e+12 (2C)^-1=0.0031516
  T2-5: symm=3.4e-20 shift=3.1e-15 zero_neg=5.1e-21 row-1=2.7e-15 col-1=3.4e-15 diag-|m|^2=2.7e-15 offdiag-(1-|m|^2)=1.1e-16 k^2<=|m|^2<=1:True
  BRIDGE: max|  |Mss|-K |=3.3e-16 Mss(+-)-K=2.2e-16 Mss(-+)-K=2.2e-16 Theta_(1/2)^(+-)-(1-K/2)^-1=6.7e-16
  POWERS (n,rowsum err,nonneg): [(0, '0e+00', np.True_), (2, '5e-15', np.True_), (3, '7e-15', np.True_), (5, '1e-14', np.True_)] (K^3)_(0,a)=(K^3)_(r,a+r) err=7.0e-15
  TAILS: max K/(A g^2 e^-2cr)=6.52e-10 (<=1)  max K/(c^-2 e^-2cr)=6.46e-05 (<=1)  max K/(Cg)^(2r)=0.99995 (<=1)  min_nb K/(g/C)^2=2.52e+04 (>=1)
  EXPMOM mu=0,c/2,c: 1.000000 1.000000 1.000000 <= |m|^2+A g^2 S=2.067e+16: True
  NBR: card N=6=2d:True identity err=7.4e-14 |1+(E+m)m|/((kap/2)s)=2.066 (>=1) nbsum=5.3991e-05 lb=1.2654e-05 ratio=4.267 (>=1)
[B] g=1.5 E=0.5 m=-0.235329+0.511322j kappa=0.511322 Lam=10.0
  HYP: BASelf resid=8.3e-17, Im m>0:True, 0<kappa<=Im m:True, 0<g<=Lam:True, 3<=L:True, 2<=d:True, small branch g<(2C)^-1:False
  CONST: C=1077.16 c=0.00425196 A=2.56708e+11 S=expC(1,c)=1.87972e+13 (2C)^-1=0.000464185
  T2-5: symm=4.4e-16 shift=8.9e-16 zero_neg=9.7e-17 row-1=1.1e-15 col-1=1.3e-15 diag-|m|^2=5.0e-16 offdiag-(1-|m|^2)=7.8e-16 k^2<=|m|^2<=1:True
  BRIDGE: max|  |Mss|-K |=4.4e-16 Mss(+-)-K=4.4e-16 Mss(-+)-K=1.1e-16 Theta_(1/2)^(+-)-(1-K/2)^-1=4.4e-16
  POWERS (n,rowsum err,nonneg): [(0, '0e+00', np.True_), (2, '2e-15', np.True_), (3, '3e-15', np.True_), (5, '3e-15', np.True_)] (K^3)_(0,a)=(K^3)_(r,a+r) err=6.8e-16
  TAILS: max K/(A g^2 e^-2cr)=5.06e-13 (<=1)  max K/(c^-2 e^-2cr)=5.73e-06 (<=1)  [small-g bounds: not applicable, g>=(2C)^-1]
  EXPMOM mu=0,c/2,c: 1.000000 1.006032 1.012126 <= |m|^2+A g^2 S=1.086e+25: True
  NBR: card N=6=2d:True identity err=1.9e-16 |1+(E+m)m|/((kap/2)s)=3.873 (>=1) nbsum=3.3893e-02 lb=2.2597e-03 ratio=14.999 (>=1)
[C] g=1.5 E=0.5 m=-0.235329+0.511322j kappa=0.255661 Lam=10.0
  HYP: BASelf resid=8.3e-17, Im m>0:True, 0<kappa<=Im m:True, 0<g<=Lam:True, 3<=L:True, 2<=d:True, small branch g<(2C)^-1:False
  CONST: C=8617.26 c=0.00212824 A=6.55778e+13 S=expC(1,c)=2.9948e+14 (2C)^-1=5.80231e-05
  T2-5: symm=4.4e-16 shift=8.9e-16 zero_neg=9.7e-17 row-1=1.1e-15 col-1=1.3e-15 diag-|m|^2=5.0e-16 offdiag-(1-|m|^2)=7.8e-16 k^2<=|m|^2<=1:True
  BRIDGE: max|  |Mss|-K |=4.4e-16 Mss(+-)-K=4.4e-16 Mss(-+)-K=1.1e-16 Theta_(1/2)^(+-)-(1-K/2)^-1=4.4e-16
  POWERS (n,rowsum err,nonneg): [(0, '0e+00', np.True_), (2, '2e-15', np.True_), (3, '3e-15', np.True_), (5, '3e-15', np.True_)] (K^3)_(0,a)=(K^3)_(r,a+r) err=6.8e-16
  TAILS: max K/(A g^2 e^-2cr)=1.93e-15 (<=1)  max K/(c^-2 e^-2cr)=1.44e-06 (<=1)  [small-g bounds: not applicable, g>=(2C)^-1]
  EXPMOM mu=0,c/2,c: 1.000000 1.003011 1.006038 <= |m|^2+A g^2 S=4.419e+28: True
  NBR: card N=6=2d:True identity err=1.9e-16 |1+(E+m)m|/((kap/2)s)=7.746 (>=1) nbsum=3.3893e-02 lb=5.6493e-04 ratio=59.996 (>=1)
```

```
Command: python3 sweep.py  (random scalar test of Target 8; sweep of d∈{1,2,3}, L∈{3,4,5,7}, g∈{.002..10}, E∈{0,.7,−1.3,1.9}, κ=Im m, Λ=10)
scalar Target 8: min |1+(E+m)m| / ((kap/2)(1-|m|^2)) over 2e6 samples = 2.00028147449938 (need >=1)
row count 138 max 6.439293542825908e-15
diag count 138 max 3.4416913763379853e-15
tail count 138 max 6.255559837662698e-07
dec count 138 max 0.0006097154207822512
nbs count 138 min 4.0000319999672165
ident count 138 max 1.3443757124482317e-13
sm count 22 min 256.0020479672316
```

### Verdicts
All 28 declarations (`BAK` + 27 theorems), as pinned in the check file: PASS. Reasons: every statement was verified by hand against the merged signatures
and numerically at the three data above and in the sweep (d=1,2,3 with `L ≥ 3`); no hypothesis set is empty, no exponent fails to close
(`c ≤ κ/2 ≤ 1/2` makes `c⁻² ≥ 1`; `μ ≤ c` closes `e^{μr−2cr} ≤ e^{−cr}`; the scalar and Target 9 constants have slack 2 and 4).
Remarks (not defects): the exponential-moment constant `A g² S` is ~1e16–1e29 (true, lossy); Target 9's `(κ/2)²/(2d)` loses a factor 4 relative to the measured minimum;
the instance `BAone_add_wm_ge (1/2) 0 ((3/5) i)` is a scalar instance only (`E=0`, `m=(3/5)i` is not a `(self_m)` solution; the scalar lemma needs only `κ ≤ Im m`, `‖m‖ ≤ 1`).

## (b) Script output — Thu Oct  8 02:23:44 UTC 2026

```
$ git log -1 --format="%h %an %s" t/T2317; git diff --stat main...t/T2317
30bcc14 Jun Yin T2317: BA-P2 kernel K = M^(+,-) of the block Anderson model (BAK)
 RBM3D/BA/KKernel.lean | 528 ++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 528 insertions(+)
$ wc -l RBM3D/BA/KKernel.lean
     528 RBM3D/BA/KKernel.lean
$ lake build RBM3D.BA.KKernel 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3738 jobs).
$ lake build 2>&1 | tail -1   (full library, worktree, before handing over)
Build completed successfully (4123 jobs).
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.BA.KKernel; #assert_rbm_axioms; exit 0 both with and without KKernel)
with KKernel:    premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).|registry: 2 borrowed + 140 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Lo|
main (no file):  premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).|registry: 2 borrowed + 140 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Lo|
audit line:      axiom audit: 9032 theorems, 2924 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```

### Axioms of the definition, the 27 public theorems and the 25 instance theorems
```
$ lake env lean axioms.lean   # one `#print axioms` per name (53 names); output lines grouped:
  53 depends on axioms: [propext, Classical.choice, Quot.sound]
$ the 53 names printed:
53
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/KKernel.lean
0
$ grep -c "Matrix.Norms\|tsum" RBM3D/BA/KKernel.lean
0
$ grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/KKernel.lean
0
```

### Check-file equality (compiled)
```
$ lake env lean eq.lean   # check file + import RBM3D.BA.KKernel + 28 examples (`@T2317Check.BAK = @BAK := rfl`, `T2317Check.Y_pin := @RBM.BA.Y`)
exit 0
examples in eq.lean (incl. the check file's own): 41
pin examples: 27
error lines: 0
```

### Target statements extracted from the file (script: stm.py pub)
```
noncomputable def BAK (g E : ℝ) (m : ℂ) : Matrix (Zd d L) (Zd d L) ℝ
theorem BAK_apply (g E : ℝ) (m : ℂ) (a b : Zd d L) : BAK d L g E m a b = ‖BAMB d L g (E : ℂ) m a b‖ ^ 2
theorem BAK_nonneg (g E : ℝ) (m : ℂ) (a b : Zd d L) : 0 ≤ BAK d L g E m a b
theorem BAK_symm (g E : ℝ) (m : ℂ) (a b : Zd d L) : BAK d L g E m a b = BAK d L g E m b a
theorem BAK_transpose (g E : ℝ) (m : ℂ) : Matrix.transpose (BAK d L g E m) = BAK d L g E m
theorem BAK_shift (g E : ℝ) (m : ℂ) (a b r : Zd d L) : BAK d L g E m (a + r) (b + r) = BAK d L g E m a b
theorem BAK_zero_neg (g E : ℝ) (m : ℂ) (a : Zd d L) : BAK d L g E m 0 (-a) = BAK d L g E m 0 a
theorem BAMss_pm_eq (g E : ℝ) (m : ℂ) : BAMss d L (BAMB d L g (E : ℂ) m) true false = Matrix.map (BAK d L g E m) Complex.ofReal
theorem BAMss_mp_eq (g E : ℝ) (m : ℂ) : BAMss d L (BAMB d L g (E : ℂ) m) false true = Matrix.map (BAK d L g E m) Complex.ofReal
theorem BAMss_norm_eq_BAK (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L) : ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b‖ = BAK d L g E m a b
theorem BATheta_pm_eq (g E : ℝ) (m : ℂ) (t : ℝ) : BATheta d L g E m t true false = PropThetaQ (Matrix.map (BAK d L g E m) Complex.ofReal) t
theorem BAK_diag (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) : BAK d L g E m a a = ‖m‖ ^ 2
theorem BAK_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) : ∑ b, BAK d L g E m a b = 1
theorem BAK_col_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (b : Zd d L) : ∑ a, BAK d L g E m a b = 1
theorem BAK_offdiag_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) : ∑ b ∈ Finset.univ.erase a, BAK d L g E m a b = 1 - ‖m‖ ^ 2
theorem BAK_diag_bounds (g κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) : κ ^ 2 ≤ BAK d L g E m a a ∧ BAK d L g E m a a ≤ 1
theorem BAK_pow_nonneg (g E : ℝ) (m : ℂ) (n : ℕ) (a b : Zd d L) : 0 ≤ (BAK d L g E m ^ n) a b
theorem BAK_pow_row_sum (g E : ℝ) (m : ℂ) (h : BASelf d L g (E : ℂ) m) (n : ℕ) (a : Zd d L) : ∑ b, (BAK d L g E m ^ n) a b = 1
theorem BAK_pow_transpose (g E : ℝ) (m : ℂ) (n : ℕ) : Matrix.transpose (BAK d L g E m ^ n) = BAK d L g E m ^ n
theorem BAK_pow_shift (g E : ℝ) (m : ℂ) (n : ℕ) (a b r : Zd d L) : (BAK d L g E m ^ n) (a + r) (b + r) = (BAK d L g E m ^ n) a b
theorem BAK_off_le (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a b : Zd d L) (hab : a ≠ b) : BAK d L g E m a b ≤ BAp5s_A d Λ κ * g ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)))
theorem BAK_le_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) : BAK d L g E m a b ≤ (BAct_C d κ * g) ^ (2 * zdistD d L (a - b))
theorem BAK_le_decay (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a b : Zd d L) : BAK d L g E m a b ≤ (BAct_rate d Λ κ)⁻¹ ^ 2 * Real.exp (-(2 * BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)))
theorem BAK_exp_moment_le (hL : 3 ≤ L) (hd : 2 ≤ d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμc : μ ≤ BAct_rate d Λ κ) (a : Zd d L) : ∑ b, BAK d L g E m a b * Real.exp (μ * (zdistD d L (a - b) : ℝ)) ≤ ‖m‖ ^ 2 + BAp5s_A d Λ κ * g ^ 2 * BAp5s_S d Λ κ
theorem BAK_adj_ge_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) (hab : Adj d L a b) : ((BAct_C d κ)⁻¹ * g) ^ 2 ≤ BAK d L g E m a b
theorem BAMB_adj_sum (g E : ℝ) (m : ℂ) (hg : 0 < g) (h : BASelf d L g (E : ℂ) m) (a : Zd d L) : ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L a b), BAMB d L g (E : ℂ) m a b = (1 + ((E : ℂ) + m) * m) / (g : ℂ)
theorem BAone_add_wm_ge (κ E : ℝ) (m : ℂ) (hκ : 0 < κ) (hκm : κ ≤ m.im) (hm : ‖m‖ ≤ 1) : κ / 2 * (1 - ‖m‖ ^ 2) ≤ ‖1 + ((E : ℂ) + m) * m‖
theorem BAK_adj_sum_ge (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a : Zd d L) : (κ * (1 - ‖m‖ ^ 2)) ^ 2 / (8 * (d : ℝ) * g ^ 2) ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd d L => Adj d L a b), BAK d L g E m a b
```

### Compiled nonempty instances (`RBM.BA.KKernelInst`, d=3, L=4, Λ=10, κ=Im m0, P : FlowPt 4 10; script: stm.py inst)
```
inst_row_sum : ∑ b, BAK 3 4 P.g0 P.E P.m0 0 b = 1
inst_col_sum : ∑ a, BAK 3 4 P.g0 P.E P.m0 a ![1, 0, 0] = 1
inst_diag : BAK 3 4 P.g0 P.E P.m0 0 0 = ‖P.m0‖ ^ 2
inst_offdiag_sum : ∑ b ∈ Finset.univ.erase (0 : Zd 3 4), BAK 3 4 P.g0 P.E P.m0 0 b = 1 - ‖P.m0‖ ^ 2
inst_diag_bounds : P.m0.im ^ 2 ≤ BAK 3 4 P.g0 P.E P.m0 0 0 ∧ BAK 3 4 P.g0 P.E P.m0 0 0 ≤ 1
inst_symm : BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] = BAK 3 4 P.g0 P.E P.m0 ![1, 0, 0] 0
inst_shift : BAK 3 4 P.g0 P.E P.m0 (0 + ![1, 1, 0]) (![1, 0, 0] + ![1, 1, 0]) = BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
inst_zero_neg : BAK 3 4 P.g0 P.E P.m0 0 (-![1, 0, 0]) = BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
inst_Mss_pm : BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false = Matrix.map (BAK 3 4 P.g0 P.E P.m0) Complex.ofReal
inst_Mss_mp : BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false true = Matrix.map (BAK 3 4 P.g0 P.E P.m0) Complex.ofReal
inst_Mss_norm (σ₁ σ₂ : Bool) : ‖BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ₁ σ₂ 0 ![1, 0, 0]‖ = BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
inst_Theta_pm : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false = PropThetaQ (Matrix.map (BAK 3 4 P.g0 P.E P.m0) Complex.ofReal) (1 / 2)
inst_pow_row_sum : ∑ b, (BAK 3 4 P.g0 P.E P.m0 ^ 3) 0 b = 1
inst_pow_nonneg : 0 ≤ (BAK 3 4 P.g0 P.E P.m0 ^ 2) 0 ![1, 0, 0]
inst_pow_transpose : Matrix.transpose (BAK 3 4 P.g0 P.E P.m0 ^ 2) = BAK 3 4 P.g0 P.E P.m0 ^ 2
inst_pow_shift : (BAK 3 4 P.g0 P.E P.m0 ^ 2) (0 + ![0, 1, 0]) (![1, 0, 0] + ![0, 1, 0]) = (BAK 3 4 P.g0 P.E P.m0 ^ 2) 0 ![1, 0, 0]
inst_off_le : BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] ≤ BAp5s_A 3 10 P.m0.im * P.g0 ^ 2 * Real.exp (-(2 * BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ)))
inst_le_decay : BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] ≤ (BAct_rate 3 10 P.m0.im)⁻¹ ^ 2 * Real.exp (-(2 * BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]) : ℝ)))
inst_exp_moment : ∑ b, BAK 3 4 P.g0 P.E P.m0 0 b * Real.exp (BAct_rate 3 10 P.m0.im * (zdistD 3 4 ((0 : Zd 3 4) - b) : ℝ)) ≤ ‖P.m0‖ ^ 2 + BAp5s_A 3 10 P.m0.im * P.g0 ^ 2 * BAp5s_S 3 10 P.m0.im
inst_exp_moment_zero : ∑ b, BAK 3 4 P.g0 P.E P.m0 0 b * Real.exp (0 * (zdistD 3 4 ((0 : Zd 3 4) - b) : ℝ)) ≤ ‖P.m0‖ ^ 2 + BAp5s_A 3 10 P.m0.im * P.g0 ^ 2 * BAp5s_S 3 10 P.m0.im
inst_adj_ge_small (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) : ((BAct_C 3 P.m0.im)⁻¹ * P.g0) ^ 2 ≤ BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0]
inst_le_small (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) : BAK 3 4 P.g0 P.E P.m0 0 ![1, 0, 0] ≤ (BAct_C 3 P.m0.im * P.g0) ^ (2 * zdistD 3 4 ((0 : Zd 3 4) - ![1, 0, 0]))
inst_adj_sum : ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b), BAMB 3 4 P.g0 (P.E : ℂ) P.m0 0 b = (1 + ((P.E : ℂ) + P.m0) * P.m0) / (P.g0 : ℂ)
inst_adj_sum_ge : (P.m0.im * (1 - ‖P.m0‖ ^ 2)) ^ 2 / (8 * (3 : ℝ) * P.g0 ^ 2) ≤ ∑ b ∈ Finset.univ.filter (fun b : Zd 3 4 => Adj 3 4 0 b), BAK 3 4 P.g0 P.E P.m0 0 b
inst_scalar : (1 / 2 : ℝ) / 2 * (1 - ‖(3 / 5 : ℂ) * Complex.I‖ ^ 2) ≤ ‖1 + (((0 : ℝ) : ℂ) + (3 / 5 : ℂ) * Complex.I) * ((3 / 5 : ℂ) * Complex.I)‖
```

### Premises used per theorem (script: stm.py lim; rows with any hypothesis beyond [NeZero L])
```
BAK_off_le               3<=L:True  g<=Λ:True  2<=d:False 0<d:True  3<=d:False
BAK_le_small             3<=L:True  g<=Λ:False 2<=d:False 0<d:True  3<=d:False
BAK_le_decay             3<=L:True  g<=Λ:True  2<=d:False 0<d:True  3<=d:False
BAK_exp_moment_le        3<=L:True  g<=Λ:True  2<=d:True  0<d:False 3<=d:False
BAK_adj_ge_small         3<=L:True  g<=Λ:False 2<=d:False 0<d:True  3<=d:False
BAK_adj_sum_ge           3<=L:True  g<=Λ:False 2<=d:False 0<d:True  3<=d:False
```

### Name-clash grep (new public names + KKernelInst + BKK_ against RBM3D/, Probe excluded)
```
$ git -C /Users/junyin/Lean_proof/RBM3D grep -lwE "BAK|BAK_[a-z_]*|BAMss_pm_eq|BAMss_mp_eq|BAMss_norm_eq_BAK|BATheta_pm_eq|BAMB_adj_sum|BAone_add_wm_ge|KKernelInst|BKK_[A-Za-z_]*" main -- RBM3D | grep -v Probe
$ same grep in the worktree, files hit:
RBM3D/BA/KKernel.lean
$ (same grep on main, number of files hit, Probe excluded)
       0
$ grep -c "^example : @RBM.BA.T2317Check.BAK = @RBM.BA.BAK := rfl" eq.lean
1
```

Ports: none. No RBM1D/RBM2D file was read or copied (ticket: no block Anderson file there); no diff-stat owed.

### Narrative (b)
- One new file `RBM3D/BA/KKernel.lean` (528 lines, commit 30bcc14 on `t/T2317`); no other file touched (`git diff --stat` above). `RBM3D/Test/Axioms.lean` untouched: the registry pre-check output with the file is identical in the premise/registry counts to `main`.
- The definition `BAK` and the 27 public theorems have the binder order of the check file; the 28 compiled `example`s of the check-file equality (`BAK` by `rfl`, 27 pins) exit 0.
- Proof routes are the ticket's: `BAMB_symm/shift/diag_eq/row_sq_real` for Targets 1-4; `Equiv.sum_comp (Equiv.addRight r)` and induction for the powers; `BAMB_sq_off_le`, `BAMB_upper_small`, `BAMB_decay_large`, `BAsum_exp_decay_le` for the tails; `BAMB_resolvent_row` at `(a, a)` for the neighbour-sum identity; `BAone_add_wm_ge` by the case split on `|E + 2 Re m| <= (1 - |m|^2)/2` (`nlinarith`); `sq_sum_le_card_mul_sum_sq` with `card_adj` for `BAK_adj_sum_ge`.
- No hypothesis was added, no statement weakened; no `sorry`. No law, no `t` except in `BATheta_pm_eq`.
- Instances: all at `P : FlowPt 4 10` (`d = 3`, `L = 4`, `Λ = 10`, `κ = Im m0`, 64 sites, `g0 > 0`), every deterministic hypothesis discharged. The two small-branch statements (`inst_adj_ge_small`, `inst_le_small`) are implications in `g0 < (2 C)^-1`, as in T2290 (no merged datum proves that premise). `inst_scalar` is at the merged Ward scalar datum (`E = 0`, `m = (3/5) i`, not a `(self_m)` solution; the scalar lemma needs only `kappa <= Im m`, `|m| <= 1`); `BAK_adj_sum_ge` at `P` uses the lemma at a genuine solution.
- The root import is not yet in `RBM3D.lean` (hub adds it at merge), so the worktree's full `lake build` does not compile `KKernel`; it was built by `lake build RBM3D.BA.KKernel` and imported by the pre-check file.
- The numeric table of Preflight (v) is section (a); it was not rerun here.
- The preflight remark that Target 9 is tight within a factor 4 and the supervisor note (`1 - |m|^2 >= c g^2`, hyperoctahedral symmetry) are not touched by any theorem here.

## (c) Verified Mathlib names (all used in the compiled file)
- `Complex.mul_conj'`, `Complex.conj_mul'` (`z * conj z = (‖z‖ : ℂ)^2`), `Complex.star_def`, `Complex.norm_conj`, `Complex.sq_norm`, `Complex.normSq_apply`, `Complex.re_le_norm`, `Complex.abs_im_le_norm`, `Complex.im_le_norm`, `Complex.norm_real`, `Complex.ofReal_ne_zero`
- `Matrix.transpose_pow`, `Matrix.mul_apply`, `Matrix.one_apply`, `Matrix.map_apply`, `Matrix.conjTranspose_apply`, `Matrix.of_apply`
- `Equiv.sum_comp`, `Equiv.coe_addRight`, `Finset.sum_ite_eq`, `Finset.sum_comm`, `Finset.mul_sum`, `Finset.add_sum_erase`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.erase_subset`, `Finset.ne_of_mem_erase`, `sq_sum_le_card_mul_sum_sq`, `norm_sum_le`, `norm_div`
- `pow_le_pow_left₀`, `pow_le_one₀`, `div_le_div_of_nonneg_right`, `div_le_iff₀`, `eq_div_iff`, `abs_le`, `not_le`, `Real.exp_add`, `Real.exp_le_exp`
- Deprecated in this Mathlib (compiler warnings seen, replaced): `if_pos` (use `simp only [↓reduceIte]`), `push_neg` (use `not_le.mp`).
- No Mathlib import added beyond `RBM3D.BA.Prop5Short` (the Chebyshev lemma and `Matrix.transpose_pow` were already available).

## (d) Open issues and paper-delta candidates
- Obstructions: none; all 28 declarations are proved as pinned.
- Paper-delta candidates: none. Route remarks only (not deltas): the paper writes `M^{(+,-)}_{ab}` without `= |M_ab|^2`; `BAMss_pm_eq`/`BAMss_norm_eq_BAK` prove the equality and the equality of the norms for all four charge pairs (`A:18` states only `<=`). `BAK_adj_sum_ge` (all-`g` neighbour lower bound) is not in the paper; this report does not confirm the paper needs it, so no `T2317a` is proposed.
- Unused premises: `3 <= d` is never a hypothesis of any theorem; `3 <= L` appears only in the six rows of the premises table above (`NeZero L` elsewhere); `g <= Λ` only in `BAK_off_le`, `BAK_le_decay`, `BAK_exp_moment_le`; `2 <= d` only in `BAK_exp_moment_le`.
