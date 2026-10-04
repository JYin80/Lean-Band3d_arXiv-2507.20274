Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 04:13:31 UTC 2026
Scripts (python3+numpy, outside the repo, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2107` (`model.py` builds `svarF d L W g` from `Defs/Block.lean` `sbKernelR`, `Defs/Sizes.lean` `split` (block `= val / W`) and samples `X` as `Xentry`: complex off-diagonal, real diagonal, `E|X_ij|^2 = S_ij`).
Notation: `m = mE E`, `z = zt E t = E + (1-t) m`, `S = t·svarF`, `Sp = S (1 - m² S)⁻¹`, `Ǧ = G - m`; sizes constant: `sz = (L, W, g)`, `n = 0`, `u = t`.

### (i) Exponent table (the pin has no exponents; these are its thresholds and constants)
| quantity | value | constraint it must satisfy | slack (script) |
|---|---|---|---|
| `|E| < 2` | pin; `Im m = √(4-E²)/2` (`mE_im`) | `Im z > 0` for `t<1` (hz of `owx_integral`), `m ≠ 0` | grid min `Im z = 9.99e-5` at `E=1.99, t=0.999`; fails only at `E=±2` (outside the pin) |
| `t < 1` | pin | `Im z = (1-t) Im m > 0` (`zt_im`, Semicircle:182) | `Im z → 0` as `t → 1`: no uniform slack, none needed |
| `0 < t` for the bridge | `owx_integral`, `dhSample_lwG_eq_deriv` take `0 < u` (`dhSample` has `0⁻¹ = 0` at `u=0`) | `t = 0` is a separate case | see row `t = 0` |
| `‖m‖ = 1` | `norm_mE` (Semicircle:63), `|E|≤2` | `lwS_isUnit` needs `‖m‖² t < 1` | `‖m‖²t = t`, slack `1-t` |
| flow relation | `z + t m = E + m = -m⁻¹` (`mE_mul`) | hzm of `owx_integral` | grid residual `2.3e-16` |
| row sums of `S` | `= t` (`lwS_row_sum`; kernel sums to 1 for `3 ≤ L`) | `owx_defect_identity` `hS` with `s = t` | grid residual `2.2e-16`; also `d ∈ {0,1,2}` (below) |
| `‖S‖_op` | `= t` (symmetric, `≥ 0`, row sums `t`) | ticket's "`‖S‖ ≤ t < 1`" | grid `‖S‖-t ≤ 7.8e-16` |
| `hSp` | `Sp_ij - m² Σ_w Sp_iw S_wj = S_ij` for `Sp = LWPins_lwSp = of S · Ring.inverse(1 - m² of S)` | `1 - m² S` a unit (`lwS_isUnit`), then `lwSplus_spec` | grid residual `1.3e-15`; min singular value of `1 - m² S` over grid `0.0373` |
| `g` | enters `svarF`, `sbKernelR` only through `g²` (`(1+2dg²)⁻¹`, `g²(1+2dg²)⁻¹`; Defs/Block.lean "No sign condition on `g` is needed") | pin has `∀ g : ℝ` | `g ≤ 0` is covered, not degenerate: `S(g) = S(-g)` (output below), `g = 0` gives block-diagonal `S ≠ 0` |
| `L, W` | `3 ≤ L` (pin; `sum_sbKernelR` uses `card_nbhd d L hL` with `hL : 3 ≤ L`), `0 < W` (`NeZero`) | `Sizes.three_le_L`, `W_pos` of `sz` | no `L`–`W` relation, no `ilambda`, no `∀ᶠ n` is used (DECISIONS §29 items (2)(3)(4) not triggered) |
| `d` | pin is `∀ d` (no `3 ≤ d`) | row sums use only `card_nbhd` | row sums `= 1` checked for `d ∈ {0,1,2,3}` |
| `t = 0` | `H_0 = √0 X = 0`, `S = 0`, `Sp = 0`, `zt E 0 = E + m = -m⁻¹`, `G = (−z)⁻¹ I = m I` | LHS `Ǧ_xx f = 0` since `G_xx = m`; every RHS term has a factor `S` or `Sp` `= 0` (the derivative terms are `0·∂f`, no differentiability needed) | exact (`G(0) - mI` below `= 0`). Merged `Gres_zero_eq_scalar` is on `Vtx`, not `Idx`: prove the scalar form on `Idx` |
| counters, `x` internal | T1 `(ΔnS,ΔnW,ΔnV,ΔnM) = (1,1,1,0)`, T2 `(1,2,2,0)`, T3 `(1,1,1,0)`, T4 `(1,2,2,0)`; `Δord = ΔnS + 2(ΔnW - ΔnV) = +1` each | new vertices hang on `x` by waved edges, solid edges do not enter molecules, so `ΔnM = 0` | counters script below; agrees with merged `owx_ord`, `owx_ord_H` |

### (ii) One concrete nondegenerate instance
Targets: bridge (a)-(d), `lwWeightExp_holds`, `(Owx)` as graph operation. Instance: `d=3, L=3, W=1, g=1/2, E=0, t=1/2` (`N=(WL)^d=27`, `x = (0,0,0)`), `P = X(true,x,x)`; second instance `W=2` (`N=216`).
Bridge item (c), variable map (checked, not assumed). `LWPins_resPoly`: variable `(σ,a,b) ↦ Gres H z σ a b`, `Gres H z false = (H - z̄)⁻¹`. `lwVar`: `(i,j,true) ↦ G_ij`, `(i,j,false) ↦ conj G_ij`. At Hermitian `H`, `(H - z̄)⁻¹_{ab} = conj(G_{ba})`. So `φ(true,a,b) = (a,b,true)`, `φ(false,a,b) = (b,a,false)` and `P' = rename φ P` (ring map); the plain reorder `(false,a,b) ↦ (a,b,false)` is wrong for `a ≠ b` (output: error `1.12` against `3.9e-16`).
Bridge item (d), derivative: blue `∂_{αw}G_ab = -G_{aα}G_{wb}` (merged `dhSample_lwG_eq_deriv`); red variable `(H+sE_{αw}-z̄)⁻¹_{ab}`: `-(G*)_{aα}(G*)_{wb} = -conj(G_{bw}G_{αa})`, which is `dhSample_lwG_star` for `conj G_{ba}`: same swap. Then both sides are derivations on `MvPolynomial`: induction `C / add / mul_X` (merged `lwStein_dh_mul`, `lwStein_dh_add`, `lwStein_dh_const`, `lwVar_tame1`). `T2060 (d).3` records that the matrix-level red rule is not merged: it is part of this ticket.
Bridge (a): `∫ F ∘ slice ∂seqP = ∫ F ∂PF` by `seqP_map_slice` (FineModel:184) and measurability of `F` (continuous in finitely many coordinates, `‖G‖ ≤ (Im z)⁻¹`). (b): `seqHflow = Hflow ∘ slice` is `rfl` (FineModel:432-436 comment); `lwG sz 0 z t x y ω = LWPins_lwG … (slice ω) x y`; `lwS sz 0 t = of LWPins_lwS` (push_cast: `((t·s : ℝ) : ℂ) = (t:ℂ)·(s:ℂ)`); `LWPins_lwSp = lwSplus sz 0 t (mE E)`; `Ǧ_xx` of the pin is `LWPins_lwGc x x = G_xx - m`.

`cd $S && python3 checks.py` (verbatim):
```
g=-2.00 row sums min/max 1.000000000000 1.000000000000 ; S(g)==S(-g): True
g=-0.50 row sums min/max 1.000000000000 1.000000000000 ; S(g)==S(-g): True
g= 0.00 row sums min/max 1.000000000000 1.000000000000 ; S(g)==S(-g): True
g= 0.50 row sums min/max 1.000000000000 1.000000000000 ; S(g)==S(-g): True
g= 3.00 row sums min/max 1.000000000000 1.000000000000 ; S(g)==S(-g): True
Hermitian: True  max|Gs[a,b]-conj(G[b,a])| = 3.908020529499657e-16  (plain reorder Gs[a,b]-conj(G[a,b])): 1.1199813679132495
blue: dH = (-0.017706305534617717-0.1158029158399021j) CR: (-0.017706305519005205-0.11580291582949376j)  formula -G[a,al]G[w,b] = (-0.017706305527751428-0.11580291584345152j)
red : dH = (-0.037347284820299365-0.05831078801407652j) CR: (-0.03734728482897298-0.058310788021882776j)  -Gs[a,al]Gs[w,b] = (-0.03734728482603091-0.058310788020288204j)  dhSample rule on conj G_{ba}: -conj(G[b,w]G[al,a]) = (-0.037347284826030905-0.05831078802028818j)
dhSample[G_ab] = (-0.01770630552532327-0.11580291584955976j)   formula (-0.017706305527751428-0.11580291584345152j)
dhSample[conj G_ab] = (0.0009294921142223696+0.003130425615167486j)   formula (0.0009294921061645495+0.003130425610308878j)
```
(`dH` = finite difference of `H ↦ F(H + sE_{αw})` in `s` real and `s = ih` (CR check); `dhSample` = `(2√u)⁻¹(∂_a - i∂_b)` by real finite differences; `a,b,α,w = 3,17,5,11` in the `N=27` model, `E=0, t=1/2`.)

`cd $S && python3 inst.py` (verbatim; hypotheses of `owx_integral` at the instance, `t=0`, MC of the target at `P = X(true,x,x)`, parameter grid):
```
instance d=3 L=3 W=1 g=0.5 E=0.0 t=0.50  N=(WL)^d=27  x=(0, 0, 0)
|E|<2: True  3<=L: True  0<t<1: True  mE= 1j  |mE|= 1.0  Im z=0.5000  z+t m= 1j  -1/m= 1j
row sums of S=tS^B: min 0.500000000000 max 0.500000000000 (t=0.50)  ||S||_op=0.500000000000  |m|^2 t=0.500  min sing(1-m^2 S)=1.0500
hSp residual max|Sp - m^2 Sp S - S| = 1.39e-16   Sp row0 (first 4): [0.1581+0.j 0.0341+0.j 0.0341+0.j 0.0341+0.j]
t=0: max|G(H=0)-m I| = 0.00e+00   (zt E 0 = E+mE = -1/m: True)
P=X(true,x,x), N=1e5: LHS +0.11129-0.00134j(0.00182) | T1 -0.01129-0.00026j(0.00024) T2 +0.00584+0.00003j(0.00005) T3 +0.13584+0.00062j(0.00099) T4 -0.01992-0.00009j(0.00015) | RHS +0.11047+0.00031j(0.00089) | LHS-RHS +0.00082-0.00165j(0.00268)
grid L,W in {(3,1),(4,1),(5,1),(3,2)}, g in {-2,-.5,0,.5,3}, E in {-1.9,0,1,1.99}, t in {.001,.5,.9,.999}: 320 points
{'hsp': 1.34e-15, 'rs': 2.22e-16, 'hzm': 2.29e-16, 'sing': 0.0373, 'nrm': 7.77e-16, 'zim': 9.99e-5}
```
`python3 -c "…svarF(d,L,2,g) for d in (0,1,2), L in (3,4), g in (-1.5,0.5)…"`: `row sums of S^B-profile, d in {0,1,2}, L in {3,4}, W=2, g in {-1.5,0.5}: min 1.000000000000 max 1.000000000000`.

(iii) Monte Carlo of `(Owx)`, `d=3, L=3, g=1/2`, 10⁴ samples of `H_t`, `x = 0`, `y = (1,0,0)`; `f ∈ {G_xy, Ḡ_xy, G_xx Ḡ_yy}`; `∂f` from the rules above; `LHS = E[Ǧ_xx f]`, T1..T4 = the four RHS terms with their signs; last column `|mean(LHS-RHS)|/SE` (SE of the complex sample std). `cd $S && python3 mc_report.py W E` for `W ∈ {1,2}`, `E ∈ {0,1}` (verbatim):
```
W=1 E=0 t=0.5 G_xy       LHS -0.001-0.001j | T1 -0.000-0.000j T2 -0.000+0.000j T3 -0.000+0.000j T4 +0.000-0.000j | LHS-RHS -0.000-0.001j (|diff|/SE=0.77)
W=1 E=0 t=0.5 Gbar_xy    LHS -0.002-0.001j | T1 -0.000+0.000j T2 +0.000+0.000j T3 -0.001-0.000j T4 +0.000+0.000j | LHS-RHS -0.001-0.001j (|diff|/SE=1.06)
W=1 E=0 t=0.5 Gxx_Gbaryy LHS +0.011-0.125j | T1 +0.000+0.012j T2 -0.000-0.006j T3 -0.007-0.140j T4 +0.001+0.010j | LHS-RHS +0.017-0.001j (|diff|/SE=1.71)
W=1 E=0 t=0.9 G_xy       LHS -0.002+0.000j | T1 +0.000+0.002j T2 -0.000-0.001j T3 +0.002+0.000j T4 -0.000-0.001j | LHS-RHS -0.005-0.001j (|diff|/SE=0.20)
W=1 E=0 t=0.9 Gbar_xy    LHS +0.005+0.000j | T1 -0.005+0.003j T2 +0.001-0.001j T3 +0.001-0.003j T4 +0.000+0.001j | LHS-RHS +0.008-0.000j (|diff|/SE=0.69)
W=1 E=0 t=0.9 Gxx_Gbaryy LHS -0.035-0.141j | T1 -0.011+0.053j T2 +0.007-0.015j T3 +0.038-0.038j T4 -0.014-0.089j | LHS-RHS -0.055-0.051j (|diff|/SE=0.76)
W=1 E=0 t=0 (3 f): LHS and T1..T4 and RHS all vanish, max abs value 0.0e+00
W=1 E=1 t=0.5 G_xy       LHS -0.001-0.001j | T1 +0.000+0.000j T2 +0.000-0.000j T3 -0.000+0.000j T4 +0.000-0.000j | LHS-RHS -0.001-0.001j (|diff|/SE=0.61)
W=1 E=1 t=0.5 Gbar_xy    LHS +0.000-0.001j | T1 -0.000+0.000j T2 +0.000-0.000j T3 +0.000-0.000j T4 -0.000+0.000j | LHS-RHS -0.000-0.001j (|diff|/SE=0.43)
W=1 E=1 t=0.5 Gxx_Gbaryy LHS +0.106-0.046j | T1 -0.014-0.003j T2 +0.002+0.008j T3 +0.128-0.050j T4 -0.008-0.010j | LHS-RHS -0.001+0.011j (|diff|/SE=0.99)
W=1 E=1 t=0.9 G_xy       LHS +0.001+0.001j | T1 +0.007+0.013j T2 -0.001-0.005j T3 +0.007+0.013j T4 +0.001-0.006j | LHS-RHS -0.014-0.014j (|diff|/SE=0.49)
W=1 E=1 t=0.9 Gbar_xy    LHS +0.001+0.013j | T1 -0.004-0.010j T2 -0.000+0.003j T3 -0.004+0.016j T4 +0.001-0.002j | LHS-RHS +0.008+0.007j (|diff|/SE=0.58)
W=1 E=1 t=0.9 Gxx_Gbaryy LHS +0.062+0.091j | T1 +0.004-0.044j T2 -0.032+0.024j T3 -0.151+0.144j T4 +0.197-0.001j | LHS-RHS +0.044-0.031j (|diff|/SE=0.32)
W=1 E=1 t=0 (3 f): LHS and T1..T4 and RHS all vanish, max abs value 1.6e-16
W=2 E=0 t=0.5 G_xy       LHS -0.000-0.000j | T1 -0.000-0.000j T2 +0.000+0.000j T3 -0.000+0.000j T4 +0.000+0.000j | LHS-RHS +0.000-0.000j (|diff|/SE=0.27)
W=2 E=0 t=0.5 Gbar_xy    LHS -0.000-0.000j | T1 -0.000-0.000j T2 -0.000+0.000j T3 +0.000+0.000j T4 +0.000-0.000j | LHS-RHS -0.000-0.000j (|diff|/SE=1.04)
W=2 E=0 t=0.5 Gxx_Gbaryy LHS +0.001-0.020j | T1 +0.000+0.000j T2 -0.000-0.000j T3 -0.000-0.019j T4 -0.000-0.000j | LHS-RHS +0.001-0.001j (|diff|/SE=0.75)
W=2 E=0 t=0.9 G_xy       LHS -0.000-0.002j | T1 -0.000-0.000j T2 +0.000-0.000j T3 +0.000+0.000j T4 -0.000+0.000j | LHS-RHS -0.001-0.002j (|diff|/SE=1.39)
W=2 E=0 t=0.9 Gbar_xy    LHS +0.000+0.002j | T1 +0.000-0.000j T2 -0.000-0.000j T3 +0.000+0.000j T4 -0.000-0.000j | LHS-RHS +0.000+0.002j (|diff|/SE=1.28)
W=2 E=0 t=0.9 Gxx_Gbaryy LHS -0.004-0.024j | T1 +0.000+0.000j T2 +0.000-0.000j T3 +0.001-0.023j T4 +0.000-0.005j | LHS-RHS -0.005+0.004j (|diff|/SE=1.24)
W=2 E=0 t=0 (3 f): LHS and T1..T4 and RHS all vanish, max abs value 0.0e+00
W=2 E=1 t=0.5 G_xy       LHS -0.000+0.000j | T1 +0.000+0.000j T2 +0.000-0.000j T3 +0.000-0.000j T4 -0.000+0.000j | LHS-RHS -0.000+0.000j (|diff|/SE=0.55)
W=2 E=1 t=0.5 Gbar_xy    LHS -0.000+0.000j | T1 -0.000-0.000j T2 -0.000+0.000j T3 -0.000+0.000j T4 +0.000+0.000j | LHS-RHS +0.000+0.000j (|diff|/SE=0.68)
W=2 E=1 t=0.5 Gxx_Gbaryy LHS +0.020-0.005j | T1 -0.000-0.000j T2 +0.000+0.000j T3 +0.019-0.004j T4 +0.001-0.000j | LHS-RHS +0.000-0.001j (|diff|/SE=0.35)
W=2 E=1 t=0.9 G_xy       LHS -0.001-0.001j | T1 +0.000-0.000j T2 +0.000-0.000j T3 -0.000+0.000j T4 +0.000+0.000j | LHS-RHS -0.000-0.001j (|diff|/SE=0.96)
W=2 E=1 t=0.9 Gbar_xy    LHS -0.001-0.000j | T1 -0.000-0.000j T2 -0.000+0.000j T3 -0.001+0.000j T4 -0.000+0.000j | LHS-RHS -0.000-0.001j (|diff|/SE=0.41)
W=2 E=1 t=0.9 Gxx_Gbaryy LHS +0.026-0.007j | T1 -0.001+0.000j T2 +0.000+0.000j T3 +0.022-0.006j T4 +0.007+0.000j | LHS-RHS -0.000-0.001j (|diff|/SE=0.47)
W=2 E=1 t=0 (3 f): LHS and T1..T4 and RHS all vanish, max abs value 1.6e-16
```
Every `|diff|/SE ≤ 1.71` (24 rows, 3-decimal print). The informative rows are `G_xx Ḡ_yy`: `T3` (the derivative term) is the largest term (e.g. `W=1,E=0,t=0.5`: `-0.140j` of `LHS -0.125j`). `cd $S && python3 mc_big.py`: at 10⁵ samples, `W=1, t=0.5, Gxx_Gbaryy`: `E=0` `|diff|/SE = 0.85`, `E=1` `1.04`.

`cd $S && python3 counters.py` (re-implementation of `LGraph.nS/nW/nV/nM/ord`; the four term graphs built by the rule: T1 adds internal `α`, edge `S_{xα}`, `Ǧ_αα`; T2 drops `Ǧ_xx`, adds `α,β`, `S⁺_{xα}`, `S_{αβ}`, `Ǧ_αα Ǧ_ββ`; T3/T4 drop `Ǧ_xx`, add `G_{αx}` resp. `G_{βα}`, `S_{xα}` resp. `S⁺_{xα}S_{αβ}`, and one derivative graph per remaining solid edge with `w = x` resp. `(β,α)`), output (lines containing `...` abridged from the identical per-graph set the script prints):
```
p2Graph, x=beta1=inr 1 counters (nS,nW,nV,nM,ord) = (6, 2, 4, 2, 2)
  T1: 1 graph(s); delta (nS,nW,nV,nM,ord) per graph = [(1, 1, 1, 0, 1)]
  T2: 1 graph(s); delta (nS,nW,nV,nM,ord) per graph = [(1, 2, 2, 0, 1)]
  T3: 5 graph(s); delta (nS,nW,nV,nM,ord) per graph = [(1, 1, 1, 0, 1)]
  T4: 5 graph(s); delta (nS,nW,nV,nM,ord) per graph = [(1, 2, 2, 0, 1)]
g1: two weights, x=inr 0 counters (nS,nW,nV,nM,ord) = (5, 1, 2, 1, 3)
  T1: 1 graph(s); ... [(1, 1, 1, 0, 1)]   T2: 1 ... [(1, 2, 2, 0, 1)]   T3: 4 ... [(1, 1, 1, 0, 1)]   T4: 4 ... [(1, 2, 2, 0, 1)]
owxH0 (external x) counters (2, 0, 0, 0, 2)
  T1: 1 graph(s); delta = [(1, 1, 1, 0, 1)]   T2: ... [(1, 2, 2, 0, 1)]   T3: 1 ... [(1, 1, 1, 0, 1)]   T4: 1 ... [(1, 2, 2, 0, 1)]
```
(`p2Graph` = merged `LWVocab` `p2Graph` with its weight `Ǧ_{β₁β₁}`; the number of T3 resp. T4 graphs is `nS(Γ) - 1`.)

### Verdicts
- **Target 1 (bridge a-d): PASS.** Hypotheses hold at the instance and on the 320-point grid; (c) needs `P' = rename φ P` with the swap `φ(false,a,b) = (b,a,false)`; (d) holds with the same swap (numbers above). Remaining work for stage 1b: the red matrix-level derivative (not merged), `Gres` Hermitian-conjugate identity `conj(G_{ba}) = (H-z̄)⁻¹_{ab}`, measurability for (a). No hypothesis set is empty or collapsed.
- **Target 2 (`lwWeightExp_holds`): PASS.** `0 < t < 1`: `owx_integral` (`hG := gaussIBP sz`, `hz` from `zt_im`, `hSp` from `lwS_isUnit` + `lwSplus_spec` with `‖m‖² t = t < 1`) plus the bridge; `t = 0`: both sides vanish (`G = mI`, `S = Sp = 0`). The pin holds for every `d`, `g : ℝ` (sign irrelevant), `L ≥ 3`, `W ≥ 1`, `|E| < 2`, `0 ≤ t < 1`; MC agrees (`|diff|/SE ≤ 1.71`, 24 rows, 4 parameter blocks, 3 `f`, 4 terms separate).
- **Target 3 (`(Owx)` as graph operation): PASS, with two notes.** Counters and `ord` per term are as in the table (`Δord = +1`), no definition outside `LWVocab` (`nS, nW, nV, nM, ord`, `relabel`, `dTerm`, `lwStein_nM_congr`) is needed. Notes: (1) T3/T4 are not the merged `LGraph.dTerm` (two new external vertices) but its instance with `α` summed (internal) and `w := x` (resp. `(β,α)`); `counters_relabel_equiv` needs an equivalence, so the identification is a direct construction (as `owxH3`, `owxH4`), `nM` by `lwStein_nM_congr` (only waved/dotted edges). (2) The expectation identity needs `D.M a a = m` for every vertex `a` (the new `Ǧ_αα`, `Ǧ_ββ` and the weight) and `D.S = lwS`, `D.Sp = lwSplus`; off-diagonal circled edges are constants of `f`. Form for LW-08: for `Γ` with `⟨true,true,inr x,inr x⟩ ∈ Γ.solid`, `E Γ.val = E(val T1 + val T2 + Σ val T3_k + Σ val T4_k)` (signs and `m, m³` in `coeff`), the lists having `1, 1, nS-1, nS-1` graphs with counter changes `(1,1,1,0), (1,2,2,0), (1,1,1,0), (1,2,2,0)`.

## (a′) Preflight corrections — Sun Oct  4 05:33:36 UTC 2026
- Section (a), Verdict "Target 2: PASS" and "the pin holds for every `d`, `g`, `L ≥ 3`, `W ≥ 1`, `|E| < 2`, `0 ≤ t < 1`" are wrong **for the pin as written**.
  `LWPins_lwSp` takes `(g, E, t)` (`#print` in (b)); the pin `LWweightExp` (`Graph/LWPins.lean:106-116`) applies it as `LWPins_lwSp d L W E g t`.
  The Monte Carlo of (a)(iii) used the true `S⁺ = S(g)(1 - m(E)² S(g))⁻¹` (`mc.py:6`: `Sp = S @ inv(I - m**2 S)`, `S = t·svarF(g)`, `m = mE(E)`), not the pin's matrix. Verdict for the verbatim pin: FAIL (false, numbers in (b)).
  Targets 1 and 3 are unaffected; stage 1b continued on them and added the corrected successor `LWweightExpFix` (proved) and `LWweightExp_zero_false` (compiled).

### Addendum to (a′) after Amend 1 — Sun Oct  4 06:18:28 UTC 2026
- Amend 1 (ticket, DECISIONS §34, CONTROL H61) re-pinned the defect: `Graph/LWPins.lean` lines 112, 115 (`LWweightExp`) and 169, 172, 176, 180 (`LWggExp`) now read `LWPins_lwSp d L W g E t` (diff in (b)).
  `LWweightExpFix`, `LWweightExp_zero_false` and the helper lemmas used only by it are deleted from the new file; the "added ... `LWweightExpFix` (proved) and `LWweightExp_zero_false` (compiled)" sentence above describes the first stage-1b round and is superseded.
  The Monte Carlo of (a)(iii) used `S⁺ = S(g)(1 - m(E)² S(g))⁻¹` (`mc.py:6`), which is `LWPins_lwSp d L W g E t`; so the verdict "Target 2: PASS" of (a) applies to the amended pin. No change to the verdicts for targets 1 and 3.

## (b) Script output
### Build, axioms, registry (stage 1b after Amend 1; branch t/T2107 at 273e270)
```
$ lake build RBM3D.Graph.LWPins 2>&1 | tail -1;  … | grep -c "RBM3D/Graph/LWPins.lean"    # messages from LWPins.lean
Build completed successfully (3345 jobs).
0
$ lake build RBM3D.Graph.LWWeightExp 2>&1 | tail -1;  … | grep -c "RBM3D/Graph/LWWeightExp.lean"   # messages from the new file
Build completed successfully (3361 jobs).
0
$ lake build RBM3D.Test.Axioms 2>&1 | tail -1
Build completed successfully (2 jobs).
$ lake build   # whole library, `import RBM3D.Graph.LWWeightExp` temporarily inserted after line 152 of RBM3D.lean (restored; `git status --short` empty afterwards); started Sun Oct  4 06:14:52 UTC 2026
info: RBM3D.lean:156:0: axiom audit: 3441 theorems, 1239 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3857 jobs).
$ grep -c "LWweightExp" buildfull2.log ; grep -n "LWggExp" buildfull2.log     # registry ledger: LWweightExp gone, LWggExp still owed
0
658:  RBM.Graph.LWggExp: 0 [no certificate]
730: RBM.Graph.LWggExp,
$ #print axioms of the 86 public declarations of the file (grep of ^theorem|def|abbrev|lemma; names_new.txt):
  78 = [propext, Classical.choice, Quot.sound]; 5 = "does not depend on any axioms"; 2 = [propext, Quot.sound] (lwSplit_perm, lwSplit_prod); 1 = [propext] (owxLab2); sorryAx: 0
  lwWeightExp_holds, lwWx_integral, lwWx_lwPoly, lwWx_dh, lwWx_lwdf, lwWx_lwG, lwWx_hSp, owx_graph_E, owx_term_integral,
  owxT1_counters, owxT2_counters, owxT3_counters, owxT4_counters, owxT1_ord, owxT2_ord, owxT3_ord, owxT4_ord : [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWWeightExp.lean RBM3D/Graph/LWPins.lean
RBM3D/Graph/LWWeightExp.lean:0
RBM3D/Graph/LWPins.lean:0
$ git diff --stat main...t/T2107
 RBM3D/Graph/LWPins.lean      |   12 +-
 RBM3D/Graph/LWWeightExp.lean | 1507 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    1 -
 3 files changed, 1513 insertions(+), 7 deletions(-)
```
### The change of `Graph/LWPins.lean` (Amend 1): the six edits, and nothing else
```
$ git diff -U0 main...t/T2107 -- RBM3D/Graph/LWPins.lean | grep -E "^(@@|[-+][^-+])" | cut -c1-140
@@ -112 +112 @@ def LWweightExp (d : ℕ) : Prop :=
-            mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W E g t x α * LWPins_lwS d L W g t α β *
+            mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β *
@@ -115 +115 @@ def LWweightExp (d : ℕ) : Prop :=
-            mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W E g t x α * LWPins_lwS d L W g t α β *
+            mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β *
@@ -169 +169 @@ def LWggExp (d : ℕ) : Prop :=
-          mE E ^ 3 * LWPins_lwSp d L W E g t x y * LWPins_lwG d L W E t ω y' y * LWPins_lwf d L W E t P ω +
+          mE E ^ 3 * LWPins_lwSp d L W g E t x y * LWPins_lwG d L W E t ω y' y * LWPins_lwf d L W E t P ω +
@@ -172 +172 @@ def LWggExp (d : ℕ) : Prop :=
-          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W E g t x α * LWPins_lwS d L W g t α β * LWPins_lwGc d L W E t ω β β *
+          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β * LWPins_lwGc d L W E t ω β β *
@@ -176 +176 @@ def LWggExp (d : ℕ) : Prop :=
-          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W E g t x α * LWPins_lwS d L W g t α β * LWPins_lwGc d L W E t ω α α *
+          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β * LWPins_lwGc d L W E t ω α α *
@@ -180 +180 @@ def LWggExp (d : ℕ) : Prop :=
-          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W E g t x α * LWPins_lwS d L W g t α β * LWPins_lwG d L W E t ω β y *
+          mE E ^ 3 * ∑ α, ∑ β, LWPins_lwSp d L W g E t x α * LWPins_lwS d L W g t α β * LWPins_lwG d L W E t ω β y *
$ git diff -U0 main...t/T2107 -- RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]" | cut -c1-120   # registry: the owed line of the proved pin
-   `RBM.Graph.LWweightExp, -- `(Owx)` (`7_8:294-306`): LW-05
$ diff <(git show bdf97cd:RBM3D/Graph/LWWeightExp.lean | sed -n 371,381p) <(sed -n 106,116p RBM3D/Graph/LWPins.lean)   # old LWweightExpFix vs amended pin
1c1
< def LWweightExpFix (d : ℕ) : Prop :=
---
> def LWweightExp (d : ℕ) : Prop :=
$ # why the six edits (first stage-1b round): the definition, and the pin's matrix against the true one, Monte Carlo d = 3, L = 3, W = 1, 2·10⁵ samples
def RBM.Graph.LWPins_lwSp : (d L W : ℕ) →
  [NeZero L] → [NeZero W] → ℝ → ℝ → ℝ → Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ :=
fun (d L W : ℕ) [NeZero L] [NeZero W] (g E t : ℝ) =>
  Matrix.of (RBM.Graph.LWPins_lwS d L W g t) *
    Ring.inverse (1 - RBM.mE E ^ 2 • Matrix.of (RBM.Graph.LWPins_lwS d L W g t))
$ python3 pinswap.py   # Sp=ok: LWPins_lwSp d L W g E t, Sp=pin: LWPins_lwSp d L W E g t (the pre-amendment text)
g=0.5 E=0.0 t=0.5 f=G_xx       Sp=ok  LHS +0.1115+0.0014j T2 +0.0058-0.0000j T4 -0.0199+0.0001j | LHS-RHS +0.00116+0.00195j SE 0.00189 |diff|/SE=1.2
g=0.5 E=0.0 t=0.5 f=G_xx       Sp=pin LHS +0.1115+0.0014j T2 +0.0038-0.0007j T4 -0.0458+0.0080j | LHS-RHS +0.02911-0.00527j SE 0.00176 |diff|/SE=16.8
g=0.5 E=0.0 t=0.9 f=G_xx       Sp=ok  LHS +0.1607+0.0058j T2 +0.0188-0.0006j T4 -0.0431+0.0015j | LHS-RHS +0.00876+0.01022j SE 0.01649 |diff|/SE=0.8
g=0.5 E=0.0 t=0.9 f=G_xx       Sp=pin LHS +0.1607+0.0058j T2 +0.0109-0.0030j T4 -0.0941+0.0259j | LHS-RHS +0.06760-0.01182j SE 0.01324 |diff|/SE=5.2
```
### Target statements, extracted from the file by script (`extract.py`; statement up to `:=`)
```
theorem lwWeightExp_holds (d : ℕ) : LWweightExp d := by
theorem lwWx_integral {F : Sizes.SeqΩ (lwWxSizes d L W g hL) → ℂ} {G : Ω d L W → ℂ}
    (hF : Continuous F) (h : ∀ ω', G (Sizes.slice (lwWxSizes d L W g hL) 0 ω') = F ω') :
    ∫ ω, G ω ∂(PF d L W g) = ∫ ω', F ω' ∂(Sizes.seqP (lwWxSizes d L W g hL)) := by
theorem lwWx_lwPoly (ω : Sizes.SeqΩ (lwWxSizes d L W g hL))
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    lwPoly (lwWxSizes d L W g hL) 0 (zt E t) t (lwWxRename d L W P) ω =
      LWPins_lwf d L W E t P (Sizes.slice (lwWxSizes d L W g hL) 0 ω) :=
theorem lwWx_dh {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    dhSample (lwWxSizes d L W g hL) 0 u α w (lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W P)) ω =
      LWPins_dH (LWPins_resPoly d L W z P) (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)) α w :=
theorem lwWx_lwdf (hz : 0 < (zt E t).im) (ht : 0 < t) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    LWPins_lwdf d L W E t P (Sizes.slice (lwWxSizes d L W g hL) 0 ω) α w =
      dhSample (lwWxSizes d L W g hL) 0 t α w (lwPoly (lwWxSizes d L W g hL) 0 (zt E t) t (lwWxRename d L W P)) ω :=
theorem lwWx_lwG (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (x y : Idx d L W) :
    lwG (lwWxSizes d L W g hL) 0 (zt E t) t x y ω =
      LWPins_lwG d L W E t (Sizes.slice (lwWxSizes d L W g hL) 0 ω) x y := rfl
theorem lwWx_lwS : lwS (lwWxSizes d L W g hL) 0 t = Matrix.of (LWPins_lwS d L W g t) := by
theorem lwWx_lwSp : lwSplus (lwWxSizes d L W g hL) 0 t (mE E) = LWPins_lwSp d L W g E t := by
theorem lwWx_hSp (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (i j : Idx d L W) :
    LWPins_lwSp d L W g E t i j - mE E ^ 2 * ∑ w, LWPins_lwSp d L W g E t i w *
        lwS (lwWxSizes d L W g hL) 0 t w j = lwS (lwWxSizes d L W g hL) 0 t i j := by
theorem owx_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (hx : p.1 = ⟨true, true, Sum.inr x, Sum.inr x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT2 m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
theorem owxT1_counters (m : ℂ) (Γ : LGraph E I) (x : I) :
    (owxT1 m Γ x).nS = Γ.nS + 1 ∧ (owxT1 m Γ x).nW = Γ.nW + 1 ∧ (owxT1 m Γ x).nV = Γ.nV + 1 ∧
      (owxT1 m Γ x).nM = Γ.nM := by
theorem owxT1_ord (m : ℂ) (Γ : LGraph E I) (x : I) :
    ord (owxT1 m Γ x).counters = ord Γ.counters + 1 := by
```
### Compiled nonempty instances (`grep -n "^example"` lines: 1393 1403 1411 1415 1422 1430 1440 1446 1468 1484 1492; `d = 3, L = 3, W = 1, g = 1/2, E = 0, t = 1/2`, `N = (WL)^d = 27`)
```
-- bridge: (b) flow data 1393; (a) 1403; (c) variable map and `lwPoly` at a red variable with a ≠ b 1411, 1415, 1422; (d) 1430  (unchanged since bdf97cd)
-- target 2 (every deterministic hypothesis by norm_num; P = X (true, x, x), x = 0), lines 1440-1442:
example := lwWeightExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  (MvPolynomial.X (true, (0 : Idx 3 3 1), 0)) 0
-- target 2 at the merged instance of the pin (LWPins.lean `inst_ssl`: d = 3, L = 3, W = 2, N = 216, g = 1, E = 0, t = 1/2, P = G_{01} Ḡ_{01}), line 1446:
example (x : Idx 3 3 2) := LWInstFixed.inst_ssl (lwWeightExp_holds 3) x
-- target 3: the merged `owxG2` data (1468); `Ǧ_{xx} G_{ax}` (1484; `gaussIBP` proved, hSp = `lwSplus_spec`, M = m I); the counters of the four terms of `Ǧ_{xx} G_{ax}` by `decide` (1492): Γ = (2,0,1,1), T1 = (3,1,2,1), T2 = (3,2,3,1), T3 = (3,1,2,1), T4 = (3,2,3,1)
$ lake env lean final_check.lean   # #check @lwWeightExp_holds ; example : ∀ d, LWweightExp d := lwWeightExp_holds ; #check (the application of the target-2 instance) ; #print axioms   (0 errors, 0 sorry)
lwWeightExp_holds : ∀ (d : ℕ), LWweightExp d
… (norm_num proof terms elided) type of the instance, first lines, then the `S⁺` factor:
  0 : ∫ (ω : Ω 3 3 1),
    LWPins_lwGc 3 3 1 0 (1 / 2) ω 0 0 * LWPins_lwf 3 3 1 0 (1 / 2) (MvPolynomial.X (true, 0, 0)) ω ∂PF 3 3 1 (1 / 2) =
  ∫ (ω : Ω 3 3 1),
    mE 0 *
                LWPins_lwSp 3 3 1 (1 / 2) 0 (1 / 2) 0 α * LWPins_lwS 3 3 1 (1 / 2) (1 / 2) α β *
'RBM.Graph.lwWeightExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### Name-clash grep, ports
```
$ for NAME in the 86 public names of the file: git grep -nE "(theorem|def|abbrev|lemma|structure|instance)[[:space:]]+([A-Za-z_.]*\.)?NAME([[:space:]]|$|\()" main -- 'RBM3D/*.lean'
public names checked: 86; clash candidates on main (37ac2ae): 0
$ git log --oneline 6187713..main ; git diff --name-only 6187713 main | grep -v "^docs/"   # main since the branch base
37ac2ae T2114: merge S1-29 Green/IBPRem
778bdf7 T2113: merge S1-25 Green/MinorDiff
6f8ca5b T2110: merge ST2-14 Induction/OptL2a
f590e74 T2106: merge KL10b Loop/KLIndStepB (proves KLindStepPin)
RBM3D.lean
RBM3D/Green/IBPRem.lean
RBM3D/Green/MinorDiff.lean
RBM3D/Induction/OptL2a.lean
RBM3D/Loop/KLIndStepB.lean
```
No port from RBM1D/RBM2D: nothing was copied, no `git diff --stat` for ports.

### Narrative (≤ 40 lines)
1. Verdict. All three targets are delivered: the bridge (a)-(d) and `(Owx)` as a graph operation (both unchanged since bdf97cd), and `lwWeightExp_holds : ∀ d, LWweightExp d` against the pin as amended.
2. Amend 1, `Graph/LWPins.lean`: exactly the six edits of the ticket (lines 112, 115, 169, 172, 176, 180: `LWPins_lwSp d L W E g t` ↦ `LWPins_lwSp d L W g E t`); the diff above shows six `-`/`+` pairs and no other change; the amended pin differs from the former `LWweightExpFix` only in its name (diff above).
3. `Graph/LWWeightExp.lean`: `LWweightExpFix` and `LWweightExp_zero_false` are deleted, with the helpers used only by them (section 5: `lwWxRHS`, `LWweightExp_iff_rhs`, `LWweightExpFix_iff_rhs`, `lwWx_one_*`, `lwWx_mE_zero`, `lwWx_mE_one_sq_im`); `lwWeightExpFix_holds` is renamed `lwWeightExp_holds` and states `LWweightExp d` (proof text unchanged); the file went from 1754 to 1507 lines. Docstrings were updated; no other declaration was touched.
4. Proof of `lwWeightExp_holds` (`LWWeightExp.lean:407`): `0 < t < 1` by `owx_integral` (`hG := gaussIBP sz`, proved) through the bridge; `t = 0` separately: `Hflow 0 = 0`, `zt E 0 = -m⁻¹`, `G = m·1` (`lwWx_gc_zero`), `LWPins_lwS … 0 = 0 = LWPins_lwSp … 0`, both integrands vanish. No sign condition on `g : ℝ`.
5. Bridge (unchanged): (a) `lwWx_integral` (`G = F ∘ lwWxSec`, `integral_map`, `seqP_map_slice`); (b) `lwWx_lwG` is `rfl`, `lwWx_lwS`, `lwWx_lwSp : lwSplus … = LWPins_lwSp d L W g E t`, `lwWx_hSp`, `lwWx_flow`, `lwWx_im_pos`, `lwWx_mE_ne`; (c) `lwWxRename = rename lwWxVar`, `(true,a,b) ↦ (a,b,true)`, `(false,a,b) ↦ (b,a,false)` (`lwWx_Gres_false`: `(H - z̄)⁻¹_{ab} = conj((H - z)⁻¹_{ba})` at Hermitian `H`); (d) `lwWx_dh`, `lwWx_lwdf` (`0 < t`).
6. `(Owx)` as a graph operation (unchanged): `owxT1`, `owxT2`, `owxT3 q`, `owxT4 q`, `owx_graph_E` (identity of expectations of values), `owxT*_counters` and `owxT*_ord`: `Δ(n_S, n_W, n_V, n_M) = (1,1,1,0), (1,2,2,0), (1,1,1,0), (1,2,2,0)`, `Δord = +1` each; no definition outside `LWVocab` is needed.
7. Registry, `RBM3D/Test/Axioms.lean`: the owed line `RBM.Graph.LWweightExp` is removed (one `-` line above); the `LWggExp` line is restored to its text on main (the first-round comment on it is dropped); the full build ledger lists `LWggExp` (owed, LW-07) and not `LWweightExp`.
8. Users of the pins: the full `lake build` (3857 jobs) compiles `inst_ssl` (LWPins.lean:732, `LWweightExp 3` as a hypothesis) and `inst_gg` (`LWggExp 3`); the new example applies `inst_ssl` to `lwWeightExp_holds 3`. No file on main outside `LWPins.lean` mentions `LWPins_lwSp d L W E g t` (`git grep` on main at 37ac2ae: only the six lines of `LWPins.lean` edited here).
9. For LW-06/07: reuse `lwWxSizes`, `lwWx_integral`, `lwWx_lwPoly`, `lwWx_lwdf`, `lwWx_hSp`, `lwWx_lwSp`; for LW-08 (`lvl1`): `owx_graph_E` with the counter theorems.

## (c) Mathlib names verified (`#check` in `mlnames2.lean`: 17 exist) and absent
`MvPolynomial.eval_rename`, `Function.Injective.extend_apply`, `Function.extend_apply'`, `SimpleGraph.ConnectedComponent.{map,lift,eq}`, `SimpleGraph.fromRel_adj`, `Equiv.sumArrowEquivProdArrow`, `Equiv.funUnique`, `finTwoArrowEquiv`, `MeasureTheory.integral_finsetSum`, `MeasureTheory.integral_map`, `MeasureTheory.integral_congr_ae`, `List.Perm.prod_eq`, `List.sum_map_mul_left`, `map_list_prod`, `Nat.card_congr`.
Absent: `Function.extend_apply` (`error(lean.unknownIdentifier)`, line 19 of `mlnames2.lean`); use `Function.Injective.extend_apply`.

## (d) Open issues and paper-delta candidates
- **T2107a (resolved by Amend 1)**: the pins `LWweightExp` and `LWggExp` of T2067 had `LWPins_lwSp d L W E g t` (coupling and energy swapped against the definition `(g E t)`); fixed by the six edits above. `LWggExp` keeps the amended text and stays owed (LW-07). Paper-delta candidate: record that the pins' `S⁺` is `S(g)(1 - m(E)² S(g))⁻¹` (`eq:def-Spm`), the order `(g, E, t)`.
- T2107b: `(Owx)` as a graph operation is stated for the blue circled weight `Ǧ_{xx}` at an internal vertex, `p ∈ lwSplit Γ.solid`, `0 < u`, `M_{aa} = m`; the red weight and the case `u = 0` are not stated (separate statements, not needed by the targets).
- T2107c: the derivative terms are one graph per solid edge of `f` (list `lwSplit p.2`), `w = x` realised by the edge lists (`owxDE`), not by `LGraph.dTerm` (which has two new external vertices); `∂_{h_{αx}}` is the `dhSample` of T2060a.
- T2107d: the bridge is stated for the constant size sequence `lwWxSizes d L W g hL` at `n = 0`; `lwWx_integral` needs a continuous `F` (all integrands of the pin are continuous functions of the sample).
- Observation: the branch base is 6187713; main is at 37ac2ae (four later merges, T2106, T2110, T2113, T2114: new files and `RBM3D.lean` imports only); the hub's full build at merge is the check on the merged tree.
- All targets delivered: `all_targets_done = true`.
