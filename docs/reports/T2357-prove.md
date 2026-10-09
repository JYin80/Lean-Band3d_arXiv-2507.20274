Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 01:16:32 UTC 2026

Notation: `C_s, c'` are the constants of `baProp5s_holds d Λ κ` (functions of `(d,Λ,κ)`); `(C₁,·)`, `(C₂,·)`, `(C_m,c_m)`, `C_m8` are those of `baPropUnit1mixed_holds`, `baPropUnit2mixed_holds`, `baProp5mixed_holds`, `baProp8mixed_holds`. Standing facts (hypotheses of every pin): `3 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `0 ≤ t < 1`, so `0 < g²+|1-t| ≤ Λ²+1` (`|1-t| = 1-t ≤ 1`), i.e. `1 ≤ (Λ²+1)(g²+|1-t|)⁻¹` (E1) and `g² ≤ Λ²(Λ²+1)(g²+|1-t|)⁻¹` (E2). Let `S(m,x) := 2^m(1+m!/x^m)`; then `(r+1)^m e^{-xr} ≤ S(m,x)` for `r ≥ 0`, `x > 0` (E3; from `(r+1)^m ≤ 2^m(1+r^m)` and `pow_mul_exp_neg_le`, `Defs/RadialSum.lean:236`, as inside `sum_radial_exp_decay_le`, `RadialSum.lean:275-300`).

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `c₅` (P5, σ₁=σ₂ rate) | `c₅ = min(c_m, c'/2)` (one `c` for both cases) | `c₅ ≤ c_m` (mixed: `e^{-c_m x/ℓ} ≤ e^{-c₅ x/ℓ}`, a smaller rate gives a larger right side) and `c₅ ≤ c'/2` | both hold, one with equality at the min; `c₅ > 0` |
| `C₅` | `max(C_m, C_s·max((1+Λ²)(Λ²+1), Λ²(Λ²+1)S(d-2,c'/2)))` | σ₁≠σ₂: `baProp5mixed_holds` at rate `c_m ≥ c₅`; σ₁=σ₂: `a=0`: `1+g² ≤ 1+Λ²`, `B_{t,0} ≥ (g²+|1-t|)⁻¹` (E1), `e⁰=1`; `a≠0`: `g²e^{-c'|a|} = g²e^{-c'|a|/2}·e^{-c'|a|/2}`, `e^{-c'|a|/2} ≤ e^{-c₅|a|/ℓ_t}` since `ℓ_t ≥ 1`, and `g²e^{-c'|a|/2} ≤ Λ²(Λ²+1)S(d-2,c'/2)(g²+|1-t|)⁻¹(|a|+1)^{-(d-2)} ≤ …B_{t,|a|}` (E2, E3, `Bparam` lower bound) | explicit; depends on `(d,Λ,κ)` only |
| `ℓ_t ≥ 1` | `one_le_ellT (hL : 1 ≤ (L:ℝ))`, `Defs/Params.lean:39` (`ellT = min (max (g/√|1-t|) 1) L`, `:32`) | `L ≥ 3 ≥ 1` | `ℓ_t ≥ 1`, slack `L-1 ≥ 2` for the min |
| `Bparam` lower bound | `B_{t,K} ≥ (g²+|1-t|)⁻¹((K+1)^{d-2})⁻¹` (second summand `(L^d|1-t|)⁻¹ ≥ 0`); NO merged public lemma in the import closure (`KLlat_inv_le_Bparam`, `Loop/KLIndStepA.lean:109`, is at `K=0` only and `Loop.KLIndStepA` is not imported: checked by import closure script) | name: private `baP8_Bparam_ge`, 3 lines (unfold, `positivity`, `linarith` as in `KLIndStepA.lean:109-115`) | exact |
| `c''` (P6/P7, σ₁=σ₂) | `c'' = c'(1-c)` | `|a±r| ≥ (1-c)|a|`: `|a| = |(a±r) + (∓r)| ≤ |a±r|+|r|` (`zdistD_add_le`, `Defs/Lattice.lean:98`; `zdistD_neg`, `:103`), `|r| ≤ c|a|`; `a ≠ 0 ⇒ |a| ≥ 1` (`zdistD_eq_zero_iff`, `:83`), so `(1-c)|a| > 0` and `a±r ≠ 0` | `c'' > 0` since `c<1`; numerically min `(|a±r|-(1-c)|a|)=0` (tight), min `|a±r|=1` |
| `C₆` | `max(C₁(1-c)^{-(d-1)}, 2C_s Λ²(Λ²+1) S(d-1,c''))` | σ₁≠σ₂: `p6h_bound` path argument; σ₁=σ₂, `a≠0`, `r≠0`: `‖Θ(a+r)-Θ(a)‖ ≤ 2C_s g² e^{-c''|a|}`, E2, E3 at `m=d-1`, `|r| ≥ 1`; `r=0`: LHS `=0`; `a=0 ⇒ |r| ≤ 0 ⇒ r=0` | depends on `(d,Λ,κ,c)` only |
| `C₇` | `max(3^d C₂(1-c)^{-d}, 4C_s Λ²(Λ²+1) S(d,c''))` | as `C₆`: four-term bound, E3 at `m=d`, `|r|² ≥ 1`; `r=0`: `Θ(a)+Θ(a)-2Θ(a)=0` | same |
| `C₈` | `max(C_m8, C_s(1+Λ²)(Λ²+1) + C_sΛ²(Λ²+1)S(d-2,c') + (d+1)^{d-2}C_s(1+Λ²·expC(d-2,c'))(Λ²+1))` | `Θ̊(0,a) = Θ(0,a) - L^{-2d}ΣΣΘ(a',b')`; translation inv. `Θ(a',b')=Θ(0,b'-a')` ⇒ `L^{-2d}ΣΣ = L^{-d}Σ_bΘ(0,b)`; `Σ_b‖Θ(0,b)‖ ≤ C_s(1+g²Σ_b e^{-c'|b|}) ≤ C_s(1+Λ²expC(d-2,c'))` (`BAsum_exp_decay_le`, `BA/Prop5Short.lean:251`, `2 ≤ d`, `y=0`, `zero_sub`+`zdistD_neg`); `L^{-d} ≤ (d+1)^{d-2}(|a|+1)^{-(d-2)}` from `|a| ≤ dL` (`zdistD_le`, `Defs/RadialSum.lean:44`) and `L ≥ 1`; then E1 | explicit |
| lattice bound `L^{-d}(|a|+1)^{d-2}` | `≤ (d+1)^{d-2}·L^{-2} ≤ (d+1)^{d-2}` | `(|a|+1) ≤ dL+1 ≤ (d+1)L` | at `(3,4)`: max `0.1094` vs `4` |
| translation invariance | NO merged `BATheta` lemma (grep `(theorem|lemma) BATheta` in `RBM3D/` outside `Probe/`: only `BATheta_eq_laplace_kBA` (`KHeat.lean:540`), `BATheta_pm_eq` (`KKernel.lean:107`), neither is shift invariance). Re-derive: `BAMB_shift` (`BA/Ward.lean:53`, public, unconditional) ⇒ `BAMss(a+r,b+r)=BAMss(a,b)` (`BAMsigma` entries are `M b a` / `star (M b a)`); `BATheta = Ring.inverse(1-tQ)`; `Matrix.nonsing_inv_eq_ringInverse`+`Matrix.inv_submatrix_equiv` (same pattern as `BAMB_shift`, handles singular case) ⇒ `Θ(a+r,b+r)=Θ(a,b)`; `Fintype.sum_equiv (Equiv.addRight _)` | private `baP8_Theta_shift`, `baP8_sum_shift` (~35 lines) | numerical error `3.2e-15`, `8.9e-16` below |
| `d` | `3 ≤ d` (only `2 ≤ d` for `BAsum_exp_decay_le`; `d-2 ≥ 1` natural subtraction exact) | exponents `d-2, d-1, d` | `d-2 ≥ 1` |
| quantifier order (iii) | `BAProp6/7`: `∃ C` after `(d,Λ,κ,c)`, before `L,g,E,m,t,σ,a,r` (`BA/FlowPins.lean:192-212`); `C₆,C₇` above use only `d,Λ,κ,c,C₁,C₂,C_s,c'` | no `L,g,E,m,t` in any constant | OK: also `BAProp5` (`∃C,∃c` before `L`), `BAProp8` |

Path argument (ii) is the band file verbatim with `Θ ↦ BATheta d L g E m t σ₁ σ₂ 0 ·`: the pins `BAPropUnit1mixed`, `BAPropUnit2mixed` (`BA/PropUnit.lean:59-80`) have exactly the hypotheses `hU` of `p6h_bound` (`K = C₁(g²+|1-t|)⁻¹`, `p = d-1`) and `p6h_unitQ` (`K = C₂(g²+|1-t|)⁻¹`, `q = d`): forward unit steps `x + Pi.single j 1`, `‖f(x+e_i+e_j) - f(x+e_i) - f(x+e_j) + f x‖`. Copied lemmas (source `Propagator/Prop6Hold.lean`, commit `01ea41d`, `main` = worktree HEAD): `p6h_tri` 50-57, `p6h_path` 60-98, `p6h_unit` 101-121, `p6h_bound` 124-139, `p6hQ` 144-145, `p6hQ_comm` 147-152, `p6hQ_neg_left` 154-165, `p6h_reduce` 168-206, `p6h_unitQ` 209-224, `p6h_second` 226-315, `p6h_conv1` 322-330, `p6h_conv2` 332-350 (≈ 300 lines). Change beyond renaming `p6h_ ↦ baP8_`: none (all generic in `f : Zd d L → ℂ`, `[NeZero L]`); `exists_step` (`Propagator/Gap.lean:88`), `exists_unitVec_of_zdistD_eq_one` (`Defs/Neighbours.lean:117`), `unitVec`, `zdistD_unitVec` (`Neighbours.lean:90`) are public and in the import closure of `BA.Prop5/PropUnit/Prop5Short/FlowPins` (checked: `Propagator.Gap`, `Defs.Neighbours`, `Defs.RadialSum`, `BA.Ward`, `BA.KKernel`, `Propagator.Prop6Hold` all in the closure). Namespace `RBM.BA` with `open RBM`.

§29 / §45 (O2) items, one line each:
1. Time domain: all pins have `0 ≤ t < 1` as in `BAProp5..8`; `|1-t| ≤ 1` (needs `t ≥ 0`) is used in E1, `|1-t| = 1-t > 0` for `Bparam`; no `s`, no cut. OK.
2. Case-(ii) boundary `1 - ilambda²/L²`: not present (no heat-kernel cut in P8; only `ℓ_t ≥ 1`). N/A.
3. `L`–`W` relation: no `W`; only `L ≥ 3` and `|a| ≤ dL`. Nothing unwritten.
4. `∀ n` vs `∀ᶠ n`: no sequences; all pins are `∀ L ≥ 3` with constants before `L`. N/A.
5. `PrecPT` vs `Prec`: deterministic statements, no probability. N/A.
6. Parameter lower bounds (`g ≥ W^{-Q}`, `N → ∞`): none used; only `0 < g ≤ Λ` (E2 uses `g ≤ Λ`, no lower bound on `g`). OK.
7. Scale vs consumer: `ℓ_t = ellT L g t` exactly as `BAProp5` (`FlowPins.lean:171`); consumers take the bundle at real `t ∈ [0,1)`, `BAReal` data (`1048.md` Downstream shape); no `(log W)^k`.

### (ii) One concrete nondegenerate instance

`d=3, L=4 (N=64), Λ=10, κ=1/2, c=1/2, g=1/2, E=0, t=1/2`, `m` the numerical solution of `(self_m)` (`BASelf`: `m = N⁻¹ tr(gΨ-E-m)⁻¹`, `Ψ` = nearest-neighbour adjacency, `Adj: |x-y|=1`), `a=(2,0,0)`, `r=(1,0,0)` (`|r|=1 ≤ c|a|=1`: window not collapsed; at `a=(1,0,0)`, `c=1/2` the window of P6/P7 collapses to `r=0`, so the P6/P7 reduction instance must use `a=(2,0,0)`; `a=(1,0,0)` is the right datum for P5/P8). All hypotheses of all five targets hold; the targets have no external hypothesis (every input is a merged theorem), so no limit computation is owed. The script solves `m`, builds `Θ=(1-tM^{(σ₁,σ₂)})⁻¹` for both charge types (`M^{(σ₁,σ₂)}_{ab}=M_{ba}(σ₁)M_{ab}(σ₂)`), checks translation invariance, `Θ̊`, and, for σ₁=σ₂, all four reductions with the explicit constants of the table, evaluated with fitted short-bound constants `C_s, c'=1/2` (these stand in for the existential `C_s, c'`; reductions hold for any positive values). Command (script in the scratchpad, not in the repo): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2357/check.py`

```
d=3 L=4 N=L^d=64 Lambda=10 kappa=0.5 c=0.5 g=0.5 E=0 t=0.5
m=0.000000+0.698785i  |m-tr/N|=1.1e-16  Im m>=kappa:True  0<g<=Lambda:True  0<=t<1:True
(s1,s2)=(True, True) transl.err=3.2e-15 |Th(0,0)|=0.8051 |Th(0,(1,0,0))|=0.0090 |Th(0,(2,0,0))|=0.0023; a=(2,0,0) r=(1,0,0) |r|=1<=c|a|=1.0: |D1|=0.0113 |D2|=0.0225 |Th0(0,a)|=0.0148 L^-d|sum_b Th(0,b)|=0.0125
  sigma1=sigma2 reductions with fitted short-bound constants C_s=1.6582, c'=0.50 (c=c'/2=0.25; c''=c'(1-c)=0.250): P5 True P6 True P7 True (692 pairs, r!=0) P8 True; C5=1.67e+05 C6=4.42e+06 C7=2.06e+08 C8=6.6e+09
  sum_b e^{-c'|b|}=17.192<=expC(d-2,c')=9.86e+04; max_a L^-d(|a|+1)^(d-2)=0.1094<=(d+1)^(d-2)=4; min_{a!=0,|r|<=c|a|}(|a+-r|-(1-c)|a|)=0; min|a+-r|=1
(s1,s2)=(True, False) transl.err=8.9e-16 |Th(0,0)|=1.3305 |Th(0,(1,0,0))|=0.0290 |Th(0,(2,0,0))|=0.0111; a=(2,0,0) r=(1,0,0) |r|=1<=c|a|=1.0: |D1|=0.0179 |D2|=0.0358 |Th0(0,a)|=0.0201 L^-d|sum_b Th(0,b)|=0.0313
```

(`c=c'/2=0.25` in the printed line is the P5 rate `c₅`, not the path parameter `c = 1/2`; the numeric constants are the table's formulas evaluated at `Λ=10`, `d=3`, with `expC` from `Defs/RadialSum.lean:271`; the Lean instance uses the `FlowPins` flow point `P` (`inst_BAProp5s`, `FlowPins.lean:1222`) as the ticket asks.)

### Verdicts

- `baProp5_holds`: PASS (mixed: `baProp5mixed_holds`; equal: reduction of the table, every inequality from merged facts `baProp5s_holds`, `one_le_ellT`, E1-E3, private `Bparam` lower bound).
- `baProp6_holds`: PASS (mixed: path argument on the copied `baP8_*`, `baPropUnit1mixed_holds`; equal: `a=0 ⇒ r=0`; `a≠0`: `zdistD_add_le`/`zdistD_neg`, `baProp5s_holds`, E2, E3).
- `baProp7_holds`: PASS (mixed: `baPropUnit2mixed_holds`, `p6h_second`/`conv2`; equal: as P6, four terms).
- `baProp8_holds`: PASS (mixed: `baProp8mixed_holds`; equal: needs private translation invariance of `BATheta` (re-derived from public `BAMB_shift`; not merged), `BAsum_exp_decay_le`, `zdistD_le`).
- `baProp5to8_holds`: PASS (fields `decay, short, diffOne, diffTwo, zeroMode` = the four above and `baProp5s_holds`).
- Notes for 1b: (1) three small private helpers are needed beyond the copied band lemmas: `baP8_Bparam_ge`, `baP8_Theta_shift` (+ `BAMss` shift), E3. (2) `BAProp5s` is not in the registry (only the five lines `Test/Axioms.lean:137-141` are owed). (3) Paper-delta candidates: none beyond DECISIONS §161 (the `σ₁=σ₂` reductions are the paper's "follow directly", `A:50`).

## (a′) Preflight corrections — Fri Oct  9 01:37:15 UTC 2026

Two imprecisions in (a), neither changes a verdict, a constant used in a statement, or an instance:
1. Translation-invariance row: `BAMss M σ₁ σ₂ a b = BAMsigma M σ₁ b a * BAMsigma M σ₂ a b` with `BAMsigma M σ x y = M x y` (σ = +) or `star (M y x)` (σ = −) (`BA/MFixedPoint.lean:507-513`); the entries are `M b a` / `star (M a b)`, not `M b a` / `star (M b a)`.  `BAMB_shift` handles both (`baP8_BAMss_shift`).
2. `C₈` of the table has `C_s(1+Λ²)(Λ²+1)` for the indicator term; the file uses `C_s(Λ²+1)` (the indicator is `≤ 1 ≤ (Λ²+1)(g²+|1-t|)⁻¹`, E1 once), a smaller admissible constant.  Helper names in the file: `baP8_BATheta_shift`, `baP8_BAMss_shift`, `baP8_sum_shift` (not `baP8_Theta_shift`).

## (b) Script output

```
$ git log --oneline main..t/T2357; git diff --stat main...t/T2357; wc -l RBM3D/BA/Prop6Path.lean
67fa717 T2357: Prop6Path: shorten five header docstring lines (long-line lint)
1e44b45 T2357: Prop6Path section 6 (instances); delete the five owed BAProp5..BAProp5to8 registry li
e4d3202 T2357: Prop6Path sections 5-6 (sigma1=sigma2 zero mode, the five targets)
976f5eb T2357: Prop6Path sections 1-4 (copied band path lemmas, elementary bounds, shift invariance,
 RBM3D/BA/Prop6Path.lean | 1178 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    5 -
 2 files changed, 1178 insertions(+), 5 deletions(-)
    1178 RBM3D/BA/Prop6Path.lean
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/BA/Prop6Path.lean
0
$ lake build RBM3D.BA.Prop6Path 2>&1 | grep -c "Prop6Path.lean"; lake build RBM3D.BA.Prop6Path 2>&1 | tail -1; lake env lean RBM3D/BA/Prop6Path.lean | wc -l
0
Build completed successfully (3747 jobs).
       0
```

**Axioms** (`#print axioms` after `import RBM3D.BA.Prop6Path`):
```
'baProp5_holds' : [propext, Classical.choice, Quot.sound]
'baProp6_holds' : [propext, Classical.choice, Quot.sound]
'baProp7_holds' : [propext, Classical.choice, Quot.sound]
'baProp8_holds' : [propext, Classical.choice, Quot.sound]
'baProp5to8_holds' : [propext, Classical.choice, Quot.sound]
$ lake env lean ax2.lean | grep Inst | grep -c "\[propext, Classical.choice, Quot.sound\]"   # the 9 instances
9
```

**Target statements** (`awk` over `RBM3D/BA/Prop6Path.lean`; the pins are `BA/FlowPins.lean:171-236`, unchanged, each `3 ≤ d → 0 < Λ → 0 < κ → …`, with `0 < c < 1` for 6, 7):
```
theorem baProp5_holds (d : ℕ) (Λ κ : ℝ) : BAProp5 d Λ κ := by
theorem baProp6_holds (d : ℕ) (Λ κ c : ℝ) : BAProp6 d Λ κ c := by
theorem baProp7_holds (d : ℕ) (Λ κ c : ℝ) : BAProp7 d Λ κ c := by
theorem baProp8_holds (d : ℕ) (Λ κ : ℝ) : BAProp8 d Λ κ := by
theorem baProp5to8_holds (d : ℕ) (Λ κ c : ℝ) : BAProp5to8 d Λ κ c :=
```

**Compiled nonempty instances** (`RBM.BA.Prop6PathInst`, `Prop6Path.lean:1053-1178`; `P : FlowPt 4 10` the merged flow point; `d = 3`, `L = 4`, `Λ = 10`, `κ = Im m₀`; every deterministic hypothesis discharged by `by norm_num`/`P.real`; no external hypothesis exists):
```
$ grep -nE "^(theorem|example)" RBM3D/BA/Prop6Path.lean | sed -n "6,20p" | cut -c1-96
1065:theorem inst_bundle : BAProp5to8 3 10 P.m0.im (1 / 2) := baProp5to8_holds 3 10 P.m0.im (1 /
1068:example := inst_BAProp5 (baProp5_holds 3 10 P.m0.im)
1070:example := inst_BAProp6 (baProp6_holds 3 10 P.m0.im (1 / 2))
1072:example := inst_BAProp7 (baProp7_holds 3 10 P.m0.im (1 / 2))
1074:example := inst_BAProp8 (baProp8_holds 3 10 P.m0.im)
1077:theorem inst_prop5_eq : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
1086:theorem inst_prop5_eq_zero : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
1095:theorem inst_prop6_eq : ∃ C : ℝ, 0 < C ∧
1108:theorem inst_prop7_eq : ∃ C : ℝ, 0 < C ∧
1122:theorem inst_prop8_eq : ∃ C : ℝ, 0 < C ∧
1131:theorem inst_reduction5 : ∃ Cs c' : ℝ, 0 < Cs ∧ 0 < c' ∧
1145:theorem inst_reduction6 : ∃ Cs c' : ℝ, 0 < Cs ∧ 0 < c' ∧
1161:theorem inst_reduction8 : ∃ Cs c' : ℝ, 0 < Cs ∧ 0 < c' ∧
$ sed -n 1094,1105p RBM3D/BA/Prop6Path.lean   # P6 at equal charge, a=(2,0,0), r=(1,0,0), |r|=1 <= (1/2)|a|=1: window not collapsed
/-- Property 6 at equal charges `σ = (-,-)`, `a = (2,0,0)`, `r = (1,0,0)`. -/
theorem inst_prop6_eq : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 (![2, 0, 0] + ![1, 0, 0]) -
        BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![2, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) *
        (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp6_holds 3 10 P.m0.im (1 / 2) (by norm_num) (by norm_num) P.real.1.1
    (by norm_num) (by norm_num)
  refine ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) false false ![2, 0, 0] ![1, 0, 0] ?_⟩
  rw [zd_a, zd_r]
  norm_num
```

**Name clash, check-file equality, copied lemmas:**
```
$ bash clash.sh   # grep -rnE of the new names (5 targets, Prop6PathInst, baP8_) over RBM3D/ and RBM3D.lean, outside RBM3D/Probe/ and the new file
hits (excluding RBM3D/Probe/ and the new file): 0
git cat-file -e main:RBM3D/BA/Prop6Path.lean exit=128 (nonzero: the file is new)
$ lake env lean checkeq.lean; echo exit=$?   # check file + import RBM3D.BA.Prop6Path + 5 examples
exit=0
$ grep -c '^example : RBM.BA.T2357Check.T2357_baProp' checkeq.lean
5
$ diff <(sed -n 45,349p RBM3D/Propagator/Prop6Hold.lean | sed -e "s/p6hQ/baP8_Q/g" -e "s/p6h_/baP8_/g") <(sed -n 52,356p RBM3D/BA/Prop6Path.lean); echo diff-exit=$?
diff-exit=0
$ git diff --stat main -- RBM3D/Propagator/Prop6Hold.lean | wc -l   # source untouched
       0
```

**Registry pre-check** (five owed lines `Test/Axioms.lean:137-141` deleted; scratch file outside the repo):
```
$ cat precheck.lean
import RBM3D
import RBM3D.BA.Prop6Path
#assert_rbm_axioms
$ lake env lean precheck.lean > precheck.out; echo exit=$?
exit=0
$ head -1 precheck.out; grep -c "BAProp5\|BAProp6\|BAProp7\|BAProp8" precheck.out
axiom audit: 10505 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
$ git diff main...t/T2357 -- RBM3D/Test/Axioms.lean | grep -c "^-   \`RBM.BA.BAProp"
5
```

**Full `lake build`.**  The hub adds `import RBM3D.BA.Prop6Path` at merge; the worktree `RBM3D.lean` has no such line, so the root audit flags the five now-unclassified pins (first run, exit 1).  Second run (exit 0): temporary uncommitted import line after the last import, restored by `cp` afterwards.
```
$ lake build   (RBM3D.lean as committed)
error: RBM3D.lean:398:0: axiom audit: 5 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps
  [RBM.BA.BAProp7, RBM.BA.BAProp5to8, RBM.BA.BAProp5, RBM.BA.BAProp8, RBM.BA.BAProp6]
error: build failed
$ lake build   (RBM3D.lean + `import RBM3D.BA.Prop6Path`); echo exit=$?
Build completed successfully (4167 jobs).
exit=0
axiom audit: 10505 theorems, 3078 definitions, 0 axioms in `RBM`
$ git status --short | wc -l   # after restoring RBM3D.lean
       0
```

**Narrative** (facts as in the script output above; line numbers of `RBM3D/BA/Prop6Path.lean`, 1178 lines, stop size 1300 not reached).
- Layout: `:52-356` the copied band lemmas (`diff` above: identical modulo `p6h_ ↦ baP8_`, `p6hQ ↦ baP8_Q`); `:358-471` elementary bounds (`baP8_S`, `baP8_poly_exp` (E3), `baP8_E1`, `baP8_E2`, `baP8_g2_exp`, `baP8_Bparam_ge`, `baP8_lower`, `baP8_tail`); `:473-528` translation invariance; `:530-844` the `σ₁ = σ₂` reductions, generic in the row `T = Θ(0,·)`; `:846-1051` the five targets; `:1053-1178` the instances.
- `σ₁ ≠ σ₂`: (5), (8) are `baProp5mixed_holds`, `baProp8mixed_holds`.  (6), (7): `baP8_bound`, `baP8_second` at `f := BATheta d L g E m t σ₁ σ₂ 0 ·`; their hypotheses `hU` are exactly the merged pins `baPropUnit1mixed_holds` (`K = C₁(g²+|1-t|)⁻¹`, `p = d-1`) and `baPropUnit2mixed_holds` (`K = C₂(g²+|1-t|)⁻¹`, `q = d`); conversions `baP8_conv1/2`; constants `C₁(1-c)^{-(d-1)}`, `3^d C₂(1-c)^{-d}`, no loss.
- `σ₁ = σ₂`: `baProp5s_holds` gives `C_s, c'`; E1 `1 ≤ (Λ²+1)(g²+|1-t|)⁻¹`, E2 `g² ≤ Λ²(Λ²+1)(g²+|1-t|)⁻¹`, E3 `(r+1)^m e^{-xr} ≤ S(m,x) := 2^m(1+m!/x^m)`.  Constants (the formulas of (a) (i), with (a′) item 2): `c₅ = min(c_m, c'/2)`, `C₅ = max(C_m, C_s·max((Λ²+1)², Λ²(Λ²+1)S(d-2,c'/2)))`; `C₆ = max(C₁(1-c)^{-(d-1)}, 2C_sΛ²(Λ²+1)S(d-1,c'(1-c)))`; `C₇ = max(3^dC₂(1-c)^{-d}, 4C_sΛ²(Λ²+1)S(d,c'(1-c)))`; `C₈ = max(C_m8, C_s(Λ²+1) + C_sΛ²(Λ²+1)S(d-2,c') + C_s(1+Λ²expC(d-2,c'))(d+1)^{d-2}(Λ²+1))`.  Each is built before `intro L …`, so it depends on `(d,Λ,κ)` (`(d,Λ,κ,c)` for 6, 7) only, the order of the pins.
- (6), (7) at equal charge: `r = 0` gives LHS `= 0`; `r ≠ 0 ⇒ |r| ≥ 1`, and `a ≠ 0` (else `|r| ≤ c·0`); `baP8_lower`: `(1-c)|a| ≤ |a±r|` from `zdistD_add_le`, `zdistD_neg`; `baP8_tail` drops the indicator since `a±r ≠ 0`.
- (8) at equal charge: no `BATheta` shift lemma is merged; `baP8_BATheta_shift` derives it from `BAMB_shift` by `Matrix.inv_submatrix_equiv` + `Matrix.nonsing_inv_eq_ringInverse` (no invertibility needed); `baP8_sum_shift`: `ΣΣΘ = L^d Σ_b Θ(0,b)`; `baP8_row_sum_le` uses `BAsum_exp_decay_le` (`y = 0`); `baP8_Linv_le` uses `zdistD_le`.
- `Bparam` lower bound: private `baP8_Bparam_ge`; the merged `KLlat_inv_le_Bparam` (`Loop/KLIndStepA.lean:109`) is at `K = 0` only.
- No pin, signature or hypothesis was changed, added or weakened; the targets are the general statements (all charge pairs), not adapters; all helpers are `private` with prefix `baP8_`.
- Registry: the five owed lines are deleted; the pre-check passes with `Prop6Path` in the environment (the five `Prop`s are then proved).

## (c) Verified names (script `#nm` after `import RBM3D.BA.Prop6Path`: every name below returned `ok` with its signature, 0 `ABSENT`; the file compiles with them)

Mathlib: `Real.exp_le_exp`, `Real.exp_le_one_iff`, `Real.exp_pos`, `Real.exp_add`, `div_le_self`, `div_le_div_iff₀`, `div_le_div_of_nonneg_right`, `le_div_iff₀`, `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `mul_pow`, `mul_self_le_mul_self`,
`Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.conjTranspose_apply`, `Matrix.submatrix_apply`, `Fintype.sum_equiv`, `Equiv.subRight`, `Equiv.addRight`, `norm_sum_le`, `norm_sub_le`, `norm_add_le`,
`Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_univ`, `Nat.pos_of_ne_zero`, `Nat.eq_zero_or_pos`, `lt_max_of_lt_left`, `abs_of_pos`, `Complex.norm_natCast`, `add_neg_cancel_right`, `sub_add_cancel`.
Project: `one_le_ellT`, `ellT_pos`, `Bparam`, `pow_mul_exp_neg_le`, `expC`, `zdistD_add_le`, `zdistD_neg`, `zdistD_eq_zero_iff`, `zdistD_le`, `zdistD_zero`, `card_Zd`, `exists_step`, `exists_unitVec_of_zdistD_eq_one`, `BAMB_shift`, `BAsum_exp_decay_le`, `baProp5s_holds`, `baProp5mixed_holds`, `baProp8mixed_holds`, `baPropUnit1mixed_holds`, `baPropUnit2mixed_holds`, `inst_BAProp5…8` (`FlowPins.lean:1214-1253`).
Absent (grep `(theorem|lemma) BATheta` in `RBM3D/` outside `Probe/`): no `BATheta` translation-invariance lemma (only `BATheta_eq_laplace_kBA`, `BATheta_pm_eq`).  `if_neg` is accepted but the compiler warned `deprecated: use ite_eq_right`; the file uses `simp only [.., ite_false]` instead.

## (d) Open issues and paper-delta candidates

1. **Hub, at merge:** add `import RBM3D.BA.Prop6Path` after the last `import` line of `RBM3D.lean` (rule (A) step 4).  Before that line exists, the worktree's `lake build` fails at the root audit with the five unclassified pins (b, "Full `lake build`"); with it, `lake build` exits 0.  Per the ticket's sibling scan `T2355` also writes `Test/Axioms.lean` (line 194, `UNG2bRowk`); this ticket's hunk is lines 137-141 only.
2. Paper-delta candidates: none (`T2357a`: none).  The Lean pins are those of T2197 (`FlowPins.lean:171-236`); the `σ₁ = σ₂` cases are the paper's "follow directly" (`A:50`), as (a) says.
3. Observations (no statement, instance, build, axiom or delta coverage affected): (i) the statements of `inst_reduction5/6/8` mention the private `baP8_S` (they compile; nothing imports them); (ii) `baP8_BATheta_shift` is private, a consumer needing shift invariance of `BATheta` would need it public; (iii) the four `example := inst_BAProp5 (baProp5_holds …)` … `inst_BAProp8 (baProp8_holds …)` are anonymous (their types are those of `FlowPins.lean:1214-1253`, mixed charge `σ = (+,-)`).
