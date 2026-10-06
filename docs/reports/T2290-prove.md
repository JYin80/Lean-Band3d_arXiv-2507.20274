Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 11:50:07 UTC 2026

Notation: `d ≥ 1`, `g` = paper's `ilambda`, `w = z + m`, `M = (gΨ − w)⁻¹`, `n = zdistD(a−b)`, `ρ_c = 2d` (`card_adj`, `3 ≤ L`). Paper `7_8:1888-1904`, proof `:1909-1911`. No external hypothesis (Aizenman Thm 10.5 is not used; `BAReal` = `BASelf ∧ κ ≤ Im m` is a data condition, §51), so no limit computation is owed.

### (i) Exponent table

| Quantity | Value | Constraint it must satisfy | Slack / check |
|---|---|---|---|
| `C` = `BAct_C d κ` | `16d²/κ³` (d,κ only, as paper `:1888`) | `C>0`; `8d/κ² ≤ C` (T6); `1/C ≤ κ²/4` (T7) | `C/(8d/κ²)=2d/κ ≥ 2` as `κ ≤ 1`; `(κ²/4)/(1/C)=4d²/κ ≥ 4` |
| threshold `(2C)⁻¹` | `κ³/(32d²)` | small branch `g < thr` | numerics (v): `g/thr ∈ {0.144, 0.97}` |
| `κ` range | `κ ≤ Im m ≤ ‖m‖ ≤ 1` | needs `BAm_norm_le_one` (merged) | `κ ≤ 1 ≤ 2d`, `κ ≤ 1 ≤ 4d²` |
| `c` = `BAct_rate d Λ κ` | `min(ν₀, κ/2)`, `ν₀ = log(1+κ/(4dΛ))` | `c>0` (`Real.log_pos`, `κ/(4dΛ)>0`); `c ≤ κ/2` ⇒ `2/κ ≤ c⁻¹`; `c ≤ ν₀` ⇒ `e^{−ν₀n} ≤ e^{−cn}` | exact (equalities of min) |
| core gap, large (T5) | `2dg(e^{ν₀}−1) = gκ/(2Λ)` | `≤ κ/2` iff `g ≤ Λ` | slack `(κ/2)(1−g/Λ)`; 0 at `g=Λ` (allowed, `≤`) |
| core gap, small (T6) | `C₁ = 4d/κ`, `e^ν = (C₁g)⁻¹`, `ν ≥ 0` iff `C₁g ≤ 1` | `C₁g < κ²/(8d) ≤ 1`; `2dg(e^ν−1) ≤ 2d/C₁ = κ/2` | `C₁g` slack factor `≥ 8d` below 1 |
| T6 chain | `(2/κ)(C₁g)^n ≤ (8dg/κ²)^n ≤ (Cg)^n`, `n ≥ 1` | `2/κ ≥ 1`; `κ ≤ 2d` | `n=0`: `M_aa = m`, `‖m‖ ≤ 1 = (Cg)^0` |
| T7 neighbour sum | `C₂g := 8dg/κ² < κ/(4d) ≤ 1` (`‖M_cb‖ ≤ (C₂g)^{n} ≤ C₂g`, `c≠b`) | `‖R‖ ≤ 2d·C₂g < κ/2`; `‖m+R‖ > κ − κ/2 = κ/2` (`‖m‖ ≥ Im m ≥ κ`) | strict, margin `κ/2 − ‖R‖ > 0` |
| T7 `‖w‖` | row (a,a): `w m = gΣ_{c∼a}M_ca − 1`, `‖M_ca‖ ≤ 1` | `2dg ≤ 1` (`2dg < κ³/(16d) < 1`) ⇒ `‖w‖‖m‖ ≤ 2`, `‖w‖ ≤ 2/κ` | factor `≥ 16d/κ³ ≥ 16` |
| T7 conclusion | `‖M_ab‖ = g‖m+R‖/‖w‖ ≥ gκ²/4` | `≥ g/C` iff `κ ≤ 4d²` | slack `4d²/κ ≥ 4` |
| core (T3) | `‖v‖ ≤ 2/κ`; `‖Kv‖ ≤ 2dρ‖v‖`, `ρ = g(e^ν−1)` | `2dρ ≤ κ/2`; `κ ≤ Im w ≤ |Im w|`; `|e^{νs}−1| ≤ e^ν−1` for `|s| ≤ 1, ν ≥ 0` | `κ‖v‖ − (κ/2)‖v‖ ≤ ‖δ_b‖ = 1` |
| premises | `0<d, 0<Λ, 0<κ, 3 ≤ L, 0<g ≤ Λ, BAReal` | **unused**: `(2C)⁻¹ ≤ g` (T5 holds for all `0<g≤Λ`); `3 ≤ d` beyond `0<d` | report only, pin unchanged |

Core derivation (T3), checked line by line: row eq `gΣ_{c∼x}u_c − w u_x = δ_xb`; `v = e^{νψ}u`, `ψ x = zdistD(x−b)`, `ψ b = 0`: `(gΨ−w)v = δ_b − Kv`, `(Kv)_x = gΣ_{c∼x}(e^{ν(ψx−ψc)}−1)v_c`; `‖(gΨ−w)v‖ ≥ |Im w|‖v‖ ≥ κ‖v‖` (`ℓ²`, Hermitian); `|(Kv)_x|² ≤ ρ²·2d·Σ_{c∼x}|v_c|²`, `Σ_xΣ_{c∼x}|v_c|² = 2d‖v‖²` ⇒ `‖Kv‖ ≤ 2dρ‖v‖`. Edge-Lipschitz of `ψ`: `zdistD(x−b) ≤ zdistD(x−y)+zdistD(y−b)`, `Adj ⇔ zdistD(x−y)=1`, symmetry by `zdistD_neg`.

Paper comparison: (Mbound_AO) `C⁻¹g1(a∼b) ≤ |M_ab| ≤ (Cg)^{|a−b|}` for `g<(2C)⁻¹` (`:1891`): PASS with `C=16d²/κ³`, `|a−b|=zdistD`; at `a=b` reads `|m| ≤ 1`. (Mbound_AO2) `|M_ab| ≤ c⁻¹e^{−c|a−b|}` (`:1902`): PASS, `c` depends on `(d,Λ,κ)` (paper leaves `c` unspecified; §18). Paper region `|E| ≤ e_g−κ`+(eq:WO) replaced by `BAReal` (§51). BAPropM conjuncts 1-4 = `baPropM12_holds` (needs `BASelf`, from `BAReal.1`); conjuncts 5-6 = T8. `C, c` precede `L, g, E, m` and do not depend on them; consequence ("two data, one model", §66(5)): any two data with same `(d,Λ,κ)` share `C, c`, and T5-T7 use only `κ ≤ Im m`, `‖m‖ ≤ 1`, `g ≤ Λ`, `card_adj`: PASS.

### (ii) Concrete nondegenerate instance (script output)

Command: `python3 T2290/pf.py` and `python3 T2290/rnd.py` (numpy 2.0.2; `Ψ` from `zdist`-distance 1 on `Z_L^3`, `m` by Newton with `η ↓ 1e-13`, `M` by dense inversion, column `b=0`, `Λ=3`, `κ := Im m`). Columns: `self` = residual of (self_m), `deg` = `#{b∼0}` (= `2d`), `ward` = `max_a|Σ_b|M_ab|²−1|`, `core(ν₀)` = `max_a|M_a0|e^{ν₀n} − 2/κ` (≤0), `large` = `max_a(|M_a0| − c⁻¹e^{−cn})` (≤0), `small` (only `g<thr`) = `max_{n≥1}|M|/(Cg)^n` (≤1), `min_adj|M|/(g/C)` (≥1), CT at `ν=log(1/(C₁g))` minus `2/κ` (≤0).
```
== real-axis data, Lam=3 ==
L=3 g=0.0005 E=0 m=-0.00000+1.00000i self=1e-13 kap=1.0000 deg=6 |m|=1.0000 g/thr=0.144 core(nu0)=-1.00 large=-33.62 | small: max|M|/(Cg)^n=6.94e-03 min_adj|M|/(g/C)=144.0 CT(nu=log(1/C1g)) -1.00
L=3 g=0.4 E=0.5 m=-0.20693+0.72841i self=6e-14 kap=0.7284 deg=6 |m|=0.7572 g/thr=298.077 core(nu0)=-1.99 large=-46.90
L=3 g=1.5 E=0.5 m=-0.24978+0.62724i self=1e-13 kap=0.6272 deg=6 |m|=0.6751 g/thr=1750.580 core(nu0)=-2.51 large=-54.80
L=4 g=0.0005 E=0 m=0.00000+1.00000i self=1e-13 kap=1.0000 deg=6 |m|=1.0000 g/thr=0.144 core(nu0)=-1.00 large=-30.96 | small: max|M|/(Cg)^n=6.94e-03 min_adj|M|/(g/C)=144.0 CT(nu=log(1/C1g)) -1.00
L=4 g=0.02 E=0.5 m=-0.24940+0.96716i self=1e-13 kap=0.9672 deg=6 |m|=0.9988 g/thr=6.367 core(nu0)=-1.07 large=-32.17
L=4 g=0.5 E=1 m=-0.21377+0.61420i self=3e-14 kap=0.6142 deg=6 |m|=0.6503 g/thr=621.497 core(nu0)=-2.61 large=-53.14
L=4 g=1.5 E=0.5 m=-0.23533+0.51132i self=9e-14 kap=0.5113 deg=6 |m|=0.5629 g/thr=3231.473 core(nu0)=-3.34 large=-64.62
L=4 g=3 E=0 m=0.00000+0.56306i self=1e-13 kap=0.5631 deg=6 |m|=0.5631 g/thr=4840.097 core(nu0)=-2.95 large=-58.16
L=6 g=0.1 E=0 m=-0.00000+0.97201i self=9e-14 kap=0.9720 deg=6 |m|=0.9720 g/thr=31.360 core(nu0)=-1.09 large=-29.53
L=6 g=1.5 E=0.5 m=-0.19001+0.20839i self=9e-14 kap=0.2084 deg=6 |m|=0.2820 g/thr=47739.130 core(nu0)=-9.28 large=-164.33
L=6 g=3 E=3 m=-0.01466+0.41541i self=9e-14 kap=0.4154 deg=6 |m|=0.4157 g/thr=12052.812 core(nu0)=-4.38 large=-78.22
== near band edge, g=1.5: scan E for kappa in (0.05,0.15) ==
edge L=4 g=1.5 E=5.6 m=0.10693+0.11165i self=1e-13 kap=0.1116 deg=6 |m|=0.1546 g/thr=310412.257 core(nu0)=-17.56 large=-316.66
edge L=6 g=1.5 E=5.1 m=-0.36175+0.12617i self=1e-13 kap=0.1262 deg=6 |m|=0.3831 g/thr=215083.357 core(nu0)=-15.47 large=-276.87
== small branch g/thr in [0.95,1) (fixed point g=0.97*kap(g)^3/288) ==
small L=4 g=0.000103 E=1.9 m=-0.95000+0.31225i self=1e-13 kap=0.3122 deg=6 |m|=1.0000 g/thr=0.970 core(nu0)=-5.41 large=-109.94 | small: max|M|/(Cg)^n=2.11e-04 min_adj|M|/(g/C)=4729.9 CT(nu=log(1/C1g)) -5.41
small L=4 g=0.00337 E=0.0 m=-0.00000+0.99997i self=1e-13 kap=1.0000 deg=6 |m|=1.0000 g/thr=0.970 core(nu0)=-1.00 large=-30.97 | small: max|M|/(Cg)^n=6.94e-03 min_adj|M|/(g/C)=144.0 CT(nu=log(1/C1g)) -1.00
small L=4 g=0.00219 E=1.0 m=-0.49999+0.86602i self=1e-13 kap=0.8660 deg=6 |m|=1.0000 g/thr=0.970 core(nu0)=-1.31 large=-36.48 | small: max|M|/(Cg)^n=4.51e-03 min_adj|M|/(g/C)=221.7 CT(nu=log(1/C1g)) -1.31
small L=6 g=0.000103 E=1.9 m=-0.95000+0.31225i self=1e-13 kap=0.3122 deg=6 |m|=1.0000 g/thr=0.970 core(nu0)=-5.41 large=-107.13 | small: max|M|/(Cg)^n=2.11e-04 min_adj|M|/(g/C)=4729.9 CT(nu=log(1/C1g)) -5.41
small L=6 g=0.00337 E=0.0 m=-0.00000+0.99997i self=1e-13 kap=1.0000 deg=6 |m|=1.0000 g/thr=0.970 core(nu0)=-1.00 large=-28.52 | small: max|M|/(Cg)^n=6.94e-03 min_adj|M|/(g/C)=144.0 CT(nu=log(1/C1g)) -1.00
small L=6 g=0.00219 E=1.0 m=-0.49999+0.86602i self=1e-13 kap=0.8660 deg=6 |m|=1.0000 g/thr=0.970 core(nu0)=-1.31 large=-33.97 | small: max|M|/(Cg)^n=4.51e-03 min_adj|M|/(g/C)=221.7 CT(nu=log(1/C1g)) -1.31
== complex instance: L=4,g=10,w=6i/5,nu=log1.01 ==
L 3 max|M|e^{nu n}= 0.37107756713324225 <= 2/kappa= 1.6666666666666667  gap 2dg(e^nu-1)= 0.6000000000000005 = kappa/2=0.6
L 4 max|M|e^{nu n}= 0.27508822013918466 <= 2/kappa= 1.6666666666666667  gap 2dg(e^nu-1)= 0.6000000000000005 = kappa/2=0.6
```
```
core random test: n= 300  max (max_a|M_a0|e^{nu n})/(2/kappa) = 0.4998  (must be <=1)
algebra grid failures: 0
```
rnd.py: 300 random complex `w` (`Im w ≥ κ`), `g` in [1e-3, 20], `ν` saturating the gap, `L ∈ {3,4}`; and an algebraic grid check (d = 1..6, `κ ∈ (0,1]`, `g = f·thr`, f ∈ {0.001, 0.5, 0.999}) of the T6/T7 inequality chain of (i). All asserts of pf.py passed (exit 0): every inequality of T3, T5, T6, T7 holds at every datum, at `L=3` (minimal `3 ≤ L`), `4`, `6`; points with `κ<0.15` (`κ=0.112, 0.126`) and small-branch points with `g/thr=0.970` included. Both branches of BAPropM are exercised: `g/thr = 0.144, 0.970 < 1` (small) and `g/thr ≥ 6.3` (large). Complex-point instance of the core (`L=3,4`, `g=10`, `w=6i/5`, `κ=6/5`, `ν=log 1.01>0`): gap `2·3·10·0.01 = 0.6 = κ/2` (equality allowed), `max|M|e^{νn} = 0.371, 0.275 ≤ 5/3`; no `N=0`, empty index, or collapsed window (`|Z_L^3| = 27, 64, 216`).

### Verdicts

- `BAzdist_adj_lip`, `BAMB_resolvent_row`, `BAMB_ct_core`, `BAct_C_pos`, `BAct_rate_pos`, `BAMB_upper_small`, `BAMB_lower_small`, `BAMB_decay_large`, `BAPropM3_of_real`, `baPropM_holds`: **PASS** (pins true as stated at `d ≥ 3`; hypothesis set satisfiable at the instances above; all exponents close with the slacks of (i)).
- Instance remark (only as math): for the ticket's merged flow point `P`, `g₀ < κ³/288` is not provable from merged data (ticket says so), so the small branch is instantiated as an implication; the numeric small-branch data above show the hypothesis set `g<(2C)⁻¹ ∧ BAReal ∧ g ≤ Λ` is nonempty.

## (b) Script output — Tue Oct  6 12:10:19 UTC 2026; branch t/T2290, commit bda6b84; `RBM3D/BA/CombesThomas.lean` 674 lines

Build (`lake build RBM3D.BA.CombesThomas`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2290`):
```
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3333 jobs).
exit=0
```
Full library with the module imported (temporary root import after the last `import`, restored afterwards; `git status` clean): `lake build`
```
Tue Oct  6 12:06:33 UTC 2026
info: RBM3D.lean:333:0: axiom audit: 8311 theorems, 2695 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4097 jobs).
exit=0
```
Axioms (`lake env lean ax.lean`, 12 public declarations; the 13 instance theorems give the same line, 25 of 25 lines below match):
```
'RBM.BA.BAct_C' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAct_rate' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAzdist_adj_lip' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_resolvent_row' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_ct_core' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAct_C_pos' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAct_rate_pos' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_upper_small' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_lower_small' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMB_decay_large' → [propext, Classical.choice, Quot.sound]
'RBM.BA.BAPropM3_of_real' → [propext, Classical.choice, Quot.sound]
'RBM.BA.baPropM_holds' → [propext, Classical.choice, Quot.sound]
lines of the form `... depends on axioms: [propext, Classical.choice, Quot.sound]`: 25 of 25
```
Statements, extracted by script from the file (`extract` = python over the file text):
```lean
-- RBM3D/BA/CombesThomas.lean:42
def BAct_C (d : ℕ) (κ : ℝ) : ℝ := 16 * (d : ℝ) ^ 2 / κ ^ 3
-- RBM3D/BA/CombesThomas.lean:45
def BAct_rate (d : ℕ) (Λ κ : ℝ) : ℝ := min (Real.log (1 + κ / (4 * (d : ℝ) * Λ))) (κ / 2)
-- RBM3D/BA/CombesThomas.lean:72
theorem BAzdist_adj_lip (x y b : Zd d L) (h : Adj d L x y) :
    zdistD d L (x - b) ≤ zdistD d L (y - b) + 1 :=
-- RBM3D/BA/CombesThomas.lean:81
theorem BAMB_resolvent_row (g : ℝ) (z m : ℂ) (hz : (z + m).im ≠ 0) (a b : Zd d L) :
    (g : ℂ) * ∑ c ∈ Finset.univ.filter (fun c : Zd d L => Adj d L a c), BAMB d L g z m c b
        - (z + m) * BAMB d L g z m a b = if a = b then 1 else 0 :=
-- RBM3D/BA/CombesThomas.lean:288
theorem BAMB_ct_core (hL : 3 ≤ L) (g κ ν : ℝ) (z m : ℂ) (hg : 0 ≤ g) (hκ : 0 < κ)
    (hw : κ ≤ (z + m).im) (hν : 0 ≤ ν) (hgap : 2 * (d : ℝ) * g * (Real.exp ν - 1) ≤ κ / 2)
    (a b : Zd d L) :
    ‖BAMB d L g z m a b‖ ≤ 2 / κ * Real.exp (-(ν * (zdistD d L (a - b) : ℝ))) :=
-- RBM3D/BA/CombesThomas.lean:47
theorem BAct_C_pos (d : ℕ) (κ : ℝ) (hd : 0 < d) (hκ : 0 < κ) : 0 < BAct_C d κ :=
-- RBM3D/BA/CombesThomas.lean:52
theorem BAct_rate_pos (d : ℕ) (Λ κ : ℝ) (hd : 0 < d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    0 < BAct_rate d Λ κ :=
-- RBM3D/BA/CombesThomas.lean:375
theorem BAMB_upper_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) :
    ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_C d κ * g) ^ zdistD d L (a - b) :=
-- RBM3D/BA/CombesThomas.lean:396
theorem BAMB_lower_small (hL : 3 ≤ L) (hd : 0 < d) (g κ E : ℝ) (m : ℂ) (hg : 0 < g) (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) (hsm : g < (2 * BAct_C d κ)⁻¹) (a b : Zd d L) (hab : Adj d L a b) :
    (BAct_C d κ)⁻¹ * g ≤ ‖BAMB d L g (E : ℂ) m a b‖ :=
-- RBM3D/BA/CombesThomas.lean:509
theorem BAMB_decay_large (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) (a b : Zd d L) :
    ‖BAMB d L g (E : ℂ) m a b‖ ≤
      (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ)) :=
-- RBM3D/BA/CombesThomas.lean:539
theorem BAPropM3_of_real (hL : 3 ≤ L) (hd : 0 < d) (Λ g κ E : ℝ) (m : ℂ) (hΛ : 0 < Λ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hr : BAReal d L g κ E m) :
    (g < (2 * BAct_C d κ)⁻¹ → ∀ a b : Zd d L,
      (BAct_C d κ)⁻¹ * g * (if Adj d L a b then 1 else 0) ≤ ‖BAMB d L g (E : ℂ) m a b‖ ∧
        ‖BAMB d L g (E : ℂ) m a b‖ ≤ (BAct_C d κ * g) ^ zdistD d L (a - b)) ∧
    ((2 * BAct_C d κ)⁻¹ ≤ g → ∀ a b : Zd d L,
      ‖BAMB d L g (E : ℂ) m a b‖ ≤
        (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * (zdistD d L (a - b) : ℝ))) :=
-- RBM3D/BA/CombesThomas.lean:562
theorem baPropM_holds (d : ℕ) (Λ κ : ℝ) : BAPropM d Λ κ :=
```
Check-file equality (scratch = check file + `import RBM3D.BA.CombesThomas` + 12 examples, `lake env lean`):
```
example : RBM.BA.T2290Check.BAct_C = RBM.BA.BAct_C := rfl
example : RBM.BA.T2290Check.BAct_rate = RBM.BA.BAct_rate := rfl
example : RBM.BA.T2290Check.BAzdist_adj_lip_pin := @RBM.BA.BAzdist_adj_lip
example : RBM.BA.T2290Check.BAMB_resolvent_row_pin := @RBM.BA.BAMB_resolvent_row
example : RBM.BA.T2290Check.BAMB_ct_core_pin := @RBM.BA.BAMB_ct_core
example : RBM.BA.T2290Check.BAct_C_pos_pin := @RBM.BA.BAct_C_pos
example : RBM.BA.T2290Check.BAct_rate_pos_pin := @RBM.BA.BAct_rate_pos
example : RBM.BA.T2290Check.BAMB_upper_small_pin := @RBM.BA.BAMB_upper_small
example : RBM.BA.T2290Check.BAMB_lower_small_pin := @RBM.BA.BAMB_lower_small
example : RBM.BA.T2290Check.BAMB_decay_large_pin := @RBM.BA.BAMB_decay_large
example : RBM.BA.T2290Check.BAPropM3_of_real_pin := @RBM.BA.BAPropM3_of_real
example : RBM.BA.T2290Check.baPropM_holds_pin := @RBM.BA.baPropM_holds
lake env lean T2290-check-eq.lean: exit=0, lines containing "error": 0
```
Compiled nonempty instances (namespace `RBM.BA.CombesThomasInst`, `d = 3`, `L = 4`; all 13 theorems of that section, `grep -n "^theorem"`):
```
10:theorem gap_im : (6 / 5 : ℝ) ≤ (zS 4 10 + mS 4 10).im := by
14:theorem nu_pos : 0 < Real.log (1 + 1 / 100) := Real.log_pos (by norm_num)
17:theorem gap_cond : 2 * ((3 : ℕ) : ℝ) * 10 * (Real.exp (Real.log (1 + 1 / 100)) - 1) ≤ (6 / 5 : ℝ) / 2 := by
22:theorem core_at_point (a b : Zd 3 4) :
29:theorem row_at_point (a b : Zd 3 4) :
37:theorem lip_at_point :
42:theorem decay_large_at_P (a b : Zd 3 4) :
49:theorem propM3_at_P :
60:theorem upper_small_at_P (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) (a b : Zd 3 4) :
65:theorem lower_small_at_P (h : P.g0 < (2 * BAct_C 3 P.m0.im)⁻¹) (a b : Zd 3 4) (hab : Adj 3 4 a b) :
70:theorem propM_at_P :
84:theorem C_pos_at : 0 < BAct_C 3 (1 / 2) := BAct_C_pos 3 (1 / 2) (by norm_num) (by norm_num)
87:theorem rate_pos_at : 0 < BAct_rate 3 10 (1 / 2) := BAct_rate_pos 3 10 (1 / 2) (by norm_num) (by norm_num) 
```
The core instance and the `baPropM_holds` instance in full (lines 603-608, 651-664 of the file):
```lean
theorem core_at_point (a b : Zd 3 4) :
    ‖BAMB 3 4 10 (zS 4 10) (mS 4 10) a b‖ ≤
      2 / (6 / 5) * Real.exp (-(Real.log (1 + 1 / 100) * (zdistD 3 4 (a - b) : ℝ))) :=
  BAMB_ct_core 3 4 (by norm_num) 10 (6 / 5) (Real.log (1 + 1 / 100)) (zS 4 10) (mS 4 10)
    (by norm_num) (by norm_num) gap_im nu_pos.le gap_cond a b

theorem propM_at_P :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      (∀ a b r : Zd 3 4, BAMB 3 4 P.g0 (P.E : ℂ) P.m0 (a + r) (b + r) = BAMB 3 4 P.g0 (P.E : ℂ) P.m0 a b) ∧
  exact ⟨C, hC, c, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real⟩
```
Name-clash grep (`namegrep.sh`; columns: files in worktree `RBM3D/` except the new file, files in main `RBM3D/`, files in main `docs/tickets` except T2290*):
```
worktree HEAD: bda6b84; main worktree HEAD: 30f7ef8
name  files-in-RBM3D/(except BA/CombesThomas.lean)  main-RBM3D/  main-docs/tickets (except T2290*)
BAct_C  0  0  0
BAct_rate  0  0  0
BAct_C_pos  0  0  0
BAct_rate_pos  0  0  0
BAzdist_adj_lip  1  0  0
BAMB_resolvent_row  0  0  0
BAMB_ct_core  0  0  0
BAMB_upper_small  0  0  0
BAMB_lower_small  1  0  0
BAMB_decay_large  0  0  0
BAPropM3_of_real  0  0  0
baPropM_holds  0  0  0
CombesThomasInst  0  0  0
CT_ (lean, other files): 0  (tickets except T2290*): 0
T2291 draft files: T2291.md T2291-check.lean 
```
(The two worktree hits are `RBM3D/Test/Axioms.lean`, the registry comment line of this ticket.)

Registry pre-check (temporary uncommitted `precheck.lean` = `import RBM3D`, `import RBM3D.BA.CombesThomas`, `#assert_rbm_axioms`; `lake env lean`):
```
before the registry line, exit=1 (path abbreviated):
/.../T2290/precheck.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Adj]
after the line in `structuralProps`, exit=0:
axiom audit: 8311 theorems, 2695 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
```
Other greps and diff:
```
$ grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/CombesThomas.lean
0
$ grep -c "Matrix.Norms" RBM3D/BA/CombesThomas.lean
0
$ grep -c "sorry\|admit\|^axiom\|native_decide" RBM3D/BA/CombesThomas.lean
0
$ grep -n "^import" RBM3D/BA/CombesThomas.lean
6:import RBM3D.BA.Ward
$ git diff --stat main...t/T2290
 RBM3D/BA/CombesThomas.lean | 674 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   1 +
 2 files changed, 675 insertions(+)
```
Ports: none. No RBM1D/RBM2D file was opened or copied (the RBM2D edge-ratio idea is only the model named in the ticket), so no `git diff --stat <commit> HEAD` for ports.
Numeric table (Preflight (v)): section (a)(ii) above is the preflight rerun (L = 3, 4, 6; `κ = 0.112, 0.126`; small branch `g/thr = 0.144, 0.970`; complex point).

Narrative.
1. Route. `BAMB_ct_core` (file :288) is a two-line wrapper (proof term) of the private `CT_core_abs` (:152): `v = e^{νψ}u` in `EuclideanSpace ℂ (Zd d L)`, `norm_sub_smul_ge_of_isHermitian` gives `κ‖v‖ ≤ ‖(gΨ-w)v‖`, the Schur bound `‖Kv‖ ≤ 2dρ‖v‖` uses `Finset.sum_mul_sq_le_sq_mul_sq` (f ≡ 1), `card_adj` and `CT_sum_adj` (`Σ_x Σ_{c∼x} = 2d Σ_c`).  No Taylor series, no `Matrix` norm instance (`Matrix.Norms` grep = 0).  `CT_upper_C2` (n ≥ 1, `ν = log((C₁g)⁻¹)`), `BAMB_upper_small`, `BAMB_lower_small` (row equation at `(a,b)` and `(a,a)`), `BAMB_decay_large` (`ν₀ = log(1 + κ/(4dΛ))`) follow Targets 5-7 of the ticket.
2. Pins. All 10 theorems and both definitions are equal to the check file's `*_pin` and bodies (12 examples, exit 0); no statement was changed, no primed successor; explicit argument order = binder order.
3. Registry. The pre-check flagged `RBM.Adj` (a hypothesis of `BAzdist_adj_lip` and `BAMB_lower_small`, whose statements are pinned).  One line was added to `structuralProps` in `RBM3D/Test/Axioms.lean` (the ticket's registry clause); after it the pre-check and the full `lake build` with the module imported pass.  Class written: structural (predicate on the lattice data); the dispatcher may reclassify.
4. Instances. `core_at_point`: complex point `(zS 4 10, mS 4 10)`, `g = 10`, `κ = 6/5`, `ν = log(1 + 1/100) > 0` (`nu_pos`), gap `2·3·10·(1/100) = 3/5 = κ/2` (`gap_cond`, equality), `(zS+mS).im = 6/5` (`gap_im`): no hypothesis left open.  `decay_large_at_P`, `propM3_at_P`, `propM_at_P` at the merged flow point `P` (`L = 4`): the theorems have no open hypothesis (`P.g0_le`, `P.real`, `P.g0_pos` supply them); the two branches are implications.  The small-branch statements (`upper_small_at_P`, `lower_small_at_P`, first conjunct of `propM3_at_P`/`propM_at_P`) are instances as implications in the data condition `g₀ < (2C)⁻¹`: no merged datum proves it (the ticket says so); the satisfiability of that hypothesis set is the numeric (a)(ii) (`g/thr = 0.144, 0.970`), not a Lean instance.  `lip_at_point` (`x = (1,0,0)`, `y = 0`, `b = (0,0,2)`, `3 ≤ 3`, `Adj` by `decide`) and `row_at_point` cover the two helper theorems.
5. Unused premises. `(2C)⁻¹ ≤ g` is not a hypothesis of `BAMB_decay_large` (it holds for every `0 < g ≤ Λ`); `3 ≤ d` is used only to get `0 < d` (`omega` in `baPropM_holds`), all other theorems take `0 < d`.  `BAMB_ct_core` has no `BAReal`: it holds for any `z, m` with `κ ≤ (z+m).im`.
6. Base. Branch `t/T2290` is based on `acb4f83` (`git rev-parse --short HEAD~1`); `main` has advanced since (name-clash header above), the hub's merge build covers that.
7. Not touched: `MFixedPoint.lean`, `Ward.lean`, `RBM3D.lean` (the hub adds the root import).  No `(a′)` section: no correction to (a) was needed; the inequalities of (a)(i) are the ones `CT_small`, `CT_upper_C2`, `BAMB_lower_small` use.

## (c) Verified Mathlib names
All 45 names below were `#check`ed by script (`lake env lean names.lean`, lines containing "error": 0); grouped by use.
- `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy-Schwarz over a finset, with `f ≡ 1`); `EuclideanSpace.norm_sq_eq`; `PiLp.norm_apply_le`; `EuclideanSpace.single`, `PiLp.single_apply`.
- `Finset.add_sum_erase`, `Finset.card_erase_le`, `Finset.single_le_sum`, `Finset.sum_comm`, `Finset.sum_filter`, `Finset.sum_sub_distrib`, `Finset.mul_sum`, `Finset.sum_ite_eq`; `norm_sum_le`, `norm_sub_le`.
- `Real.exp_log`, `Real.exp_neg`, `Real.exp_nat_mul`, `Real.exp_add`, `Real.exp_le_exp`, `Real.exp_le_one_iff`, `Real.one_le_exp`, `Real.add_one_le_exp`, `Real.exp_pos`, `Real.log_pos`, `Real.log_nonneg`.
- `pow_le_pow_left₀`, `le_self_pow₀`, `pow_le_of_le_one`, `abs_le_of_sq_le_sq'`, `inv_anti₀`, `one_le_inv₀`, `inv_div`, `le_div_iff₀`, `div_le_div_iff₀`, `div_lt_iff₀`, `lt_div_iff₀`, `div_le_iff₀`.
- `Complex.abs_im_le_norm`, `Complex.norm_real`; `Ring.mul_inverse_cancel`; `Matrix.mul_apply`, `Matrix.one_apply`, `Matrix.toLpLin_apply`, `WithLp.ofLp_toLp`.
- Absent or unusable (observed in this ticket's build log): `sq_sum_le_card_mul_sum_sq` is `Unknown identifier` in the closure of `RBM3D.BA.Ward` (it is at `Mathlib/Algebra/Order/Chebyshev.lean:144`, not imported); deprecated (warnings): `EuclideanSpace.norm_single` (use `simp`), `EuclideanSpace.single_apply`, `if_pos`, `if_neg`, `push_neg`.  No Mathlib module was added to the imports (`RBM3D.BA.Ward` only).

## (d) Open issues and paper-delta candidates
- Hub, at merge: root import `import RBM3D.BA.CombesThomas` after the last `import`.  Stale docstrings (`grep -n "Owed: BA-D3\|BA-D4" RBM3D/BA/MFixedPoint.lean RBM3D/BA/Ward.lean`, not edited, §57 (1)):
```
  RBM3D/BA/MFixedPoint.lean:557:Owed: BA-D3. -/
  RBM3D/BA/MFixedPoint.lean:566:/-- **`lem:propM`** (`7_8:1847-1912`) in the bulk `κ ≤ Im m`.  Owed: BA-D3 (items (1)(2)), BA-D4 (item (3)). -/
  RBM3D/BA/MFixedPoint.lean:582:/-- **`(eq:off_diagM)`** (`A:32-34`).  Owed: BA-D3. -/
```
- Registry: one line `RBM.Adj` in `structuralProps`; a second ticket flagging `RBM.Adj` would add the same line (merge conflict in that line only).  No owed line is added or removed for `BAPropM`; consumers apply `baPropM_holds d Λ κ`.
- Paper-delta candidate T2290a (strengthening, not a contradiction): the paper asserts "there exist `C` (depending on `d, κ`) and `c`" (`7_8:1888-1904`); Lean fixes `C = 16d²/κ³`, `c = min(log(1+κ/(4dΛ)), κ/2)` (depends on `Λ`, DECISIONS §18), and `(Mbound_AO2)` holds for every `0 < g ≤ Λ`, not only `g ≥ (2C)⁻¹`.
- Route remark (not a delta): `(Mbound_AO)` follows from the Combes-Thomas estimate at `e^ν = (C₁g)⁻¹` plus the row equation; no Taylor series (`7_8:1909`) is used.
- The small-branch half has no Lean instance with its data condition discharged (narrative 4); `|a-b|` is `zdistD`, the paper's `(eq:WO)` and `|E| ≤ e_g - κ` are the datum `BAReal` (§51).
