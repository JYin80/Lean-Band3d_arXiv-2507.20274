Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 10:47:03 UTC 2026

Scripts (not in the repository): scratchpad `T2381/` = `k10.py` (cut, base levels, bound chains), `k10_lattice.py` (lattice instance); mirrors copied from `T2374/`, `T2376/` (`mirror.py`, `mgraph.py`, `k6.py`, `kode.py`). Notation: `Ms = BAMsigma d L (BAMB d L g E m)`, `Θ^{σσ'} = BAThetaOf Ms t σ σ'`, `J = (i,j)`, `w = j-i = KLwIn J`, `n_in = w+1`, `n_out = n-w+1`, `σin/σout = sigmaIn/sigmaOut σ J`, `π' = (π.erase J).image KLshiftOut J`, `B = Bparam d L g t 0`.

### (i) Exponent table and public statements

| quantity | value | constraint | slack |
|---|---|---|---|
| `n` | instance 4, 5 | cut needs a diagonal `J ∈ π ⊆ diagonals n`, so `n ≥ 4` (pin `3 ≤ n` as `KLKpi_cut`, only `2 ≤ n` is used) | `n - 4` |
| `w = j-i` | 2 (`J = (0,2)`) | `2 ≤ w ≤ n-2` (diagonal, not `(0,n-1)`) | `n-2-w = 1` at `n = 5` |
| `n_in`, `n_out` | 3, 4 at `n = 5` | `n_in, n_out ∈ [3, n-1]` (so the IH applies to the outer polygon) | `n-1-n_in = 1`, `n_out-3 = 1` |
| `B`-exponent of the step | `(n_in-2)+(n_out-1) = 4` | `= n-1` | 0 (exact, nothing lost) |
| loss | `L^{τ/2}·L^{τ/2}` | `= L^τ` | 0 (exact split; `L ≥ 3`, `τ > 0` give `L^{τ/2} > 1`) |
| prefactor `t` | `1/2` | `‖(t:ℂ)‖ ≤ 1` (`t ∈ [0,1)`); `1-t` enters only through `B = (g²+\|1-t\|)⁻¹ + (L^d\|1-t\|)⁻¹` | `1 - t = 1/2` |
| `W` | `2`, `W^d = 8` | the cut is `W`-free (`BAKpi` has no `W`); `W^{-d(n-1)}` enters once, in `baK_eq_sum_Kpi` (K06) | none to spend |
| `C_d` (sup of `Θ`) | `BAProp5 d Λ κ` | `‖Θ^{σσ'}(x,y)‖ ≤ C_d B` (`B_{t,\|a\|} ≤ B_{t,0}` by `KLIndStepA_Bparam_le_zero`, `exp ≤ 1`); needs `3 ≤ d`, `0<Λ`, `0<κ`, `0<g≤Λ`, `BAReal`, `t∈[0,1)` | measured `A = max\|Θ\| = 1.27..5.22` (numerics (c)), no claim on `C_d` |
| `S` (`ℓ¹` of a short `Θ`) | `C_s(1 + Λ²·expC k c_s)`, `d = k+2` | `≥ max_{σ,x} Σ_b \|Θ^{σσ}(x,b)\|` (`BAProp5s`, `sum_exp_decay_centre`) | measured `S = 0.77..1.11` |
| `C_M` (`ℓ¹` of `M`) | `C'·expC k c'`, `c' = min(ln 2, c)`, `C' = max(1, c⁻¹)` | `Σ_b \|M(σ)_{ab}\| ≤ C_M` uniformly in `L` (`BAPropM` items 5, 6: `(Cg)^{\|·\|} ≤ 2^{-\|·\|}` for `g < (2C)⁻¹`, else `c⁻¹e^{-c\|·\|}`; `\|M(-)_{ab}\| = \|M(+)_{ab}\|`) | measured `Cm = 1.70..2.13` |
| `n = 2` chain | `A·colsum` | `‖(ΘM^{σσ'})(x,y)‖ ≤ C_d B·Σ_z‖M^{σσ'}(z,y)‖`, `Σ_z‖M^{σσ'}(z,y)‖ = Σ_z BAK(z,y) = 1` (`BAMss_norm_eq_BAK`, `BAK_col_sum`) | measured ratio `≤ 0.85` (ratio = `max\|K2\| / (A·colsum)`) |
| `n = 3` chain | `C_d² S C_M²`, two `B`'s | an equal-charge cyclic pair exists; its `Θ` is summed (`S`), the other two are sup-bounded; `\|M\| ≤ 1` (row sum of squares `= 1`) and two `ℓ¹` rows of `M`; `B`-exponent `2 = n-1` | measured ratio `≤ 0.19` (ratio = `max\|K3\| / (A²SC_M²)`; slack factor `≥ 5`, not claimed) |
| `n = 1` | `‖m‖ ≤ 1` (`BAm_norm_le_one`, `Ward.lean:136`) | `1 ≤ L^τ` | `3^τ - 1 > 0` |
| orientation | chord `(u,w)`: `u` = inner end | none transposed, no symmetry of `M` used | control with transposed chord: `2e-3..6e-3` on non-symmetric data; formula: `≤ 4e-17` |
| numerics tolerance | `1e-12` | max defect | `3.1e-14` (cut), `7e-13` (base (b), `n = 3`, `t = 0.95`; all other base entries `≤ 3e-14`) |

Public statements (namespace `RBM.BA`, file `RBM3D/BA/KInduct.lean`; helpers `private`, stem `KInduct_`). Common hypotheses `H`: `0<κ`, `0<g`, `3 ≤ L`, `BAReal d L g κ E m`, `t ∈ [0,1)` (the signature of `baK_eq_sum_Kpi`); `Λ := g` in `baKsolve`/`baTreeRep` (`le_rfl`).

| name | statement | proof | consumers |
|---|---|---|---|
| `baKsol_one/two/three` | under `H`: `𝒦^{(1)} = PropSpin m σ₀`; `𝒦^{(2)}_{σ,a} = (W^d)⁻¹ (Θ^{σ₀σ₁}M^{σ₀σ₁})(a₀,a₁)` `(Kn2sol)`; `𝒦^{(3)}_{σ,a} = Σ_{b} ∏_k Θ^{σ_kσ_{k+1}}(a_k,b_k)·BAMLoop(σ,b)` `(Kn3sol)`; `𝒦 := BAKsol … t (KLloopOf σ a)` | `BAKsol_isKLoopS (baKsolve d)` gives clause 3 (n=1); `baK_unique` against the `baKsolve` witness gives the 2-clause (0350 C4); n=3: `baTreeRep` at `n=3`, `TSP_three`, `BACactusVal_three_BAMLoop` | K11 (n=2 base of `wardineq_K`, every `σ`), K12 (`BAKBoundAt_*`, `BAKward` n=2 clause) |
| `BAKBoundAt d n Λ κ` | verbatim probe `t/T2360:RBM3D/Probe/T2360Pins.lean:38` (not on `main`: grep 0 hits) | def | K12 imports it (D1) |
| `BAKpiBoundAt d n Λ κ` | `∀τ>0 ∃C>0`, uniform in `L≥3`, `0<g≤Λ`, `BAReal`, `t∈[0,1)`, `σ`, `π`, `a`: `‖BAKpi d L n Ms t σ a π‖ ≤ C L^τ B^{n-1}` (no `W`; twin of `KLKpiBoundAt`) | def | K09b/K12 (D2) |
| `baKBoundAt_one/two/three` | `BAKBoundAt d n Λ κ` for `n = 1` (any `d`); `n = 2, 3` (`3 ≤ d`, `0<Λ`, `0<κ`) | rows `C_d, S, C_M` above, `KInduct_theta_shift` (copy of private `KMolecule_theta_perm`, `Θ(x,y)=Θ(0,y-x)`), `baProp5_holds`, `baProp5s_holds`, `baPropM_holds` (all unconditional theorems) | K12 (`KLboundPin_holds` twin) |
| `baKpi_cut` | `3 ≤ n`, any `M`, `t`; `F₀ ∈ TSP n`, `KLFlong F₀ σ = π`, `J ∈ π` innermost: `BAKpi M t σ a π = (t:ℂ)·Σ_u A(u)·BAKpi M t σout (BAdeltaOut J a u) π'`, `A(u) = Σ_{δ: δ_last = u} BASigmaPi M t σin ∅ δ · ∏_{k≠last} Θ^{σin_k σin_{k+1}}(a_{BAinVinv J k}, δ_k)` | §ii | K09b (hypothesis of the step), K11 |
| `baKpi_cut_abs` | `baKpi_cut` at `ι`, `Ms i`, `Sig = BASig`, `TH i = BAThetaOf (Ms i)`, `Kp = BAKpi`: `A(u)` is verbatim the summand of `IndStepAbs d n_in L Bp Sig TH` at `r = Fin.last`, `σin_last ≠ σin_0` (`σ_j ≠ σ_i`, long) | `baKpi_cut` (`BASig` unfolds) | K09b: `Iff.rfl` / one-line bridge to its hypothesis |
| `baKpi_cut_S` | same with `Σ_uΣ_w t·A(u)·(1:Matrix) u w·BAKpi(… BAdeltaOut J a w …)` (the shape of `KLKpi_cut` at `SB ↦ 1`) | `Finset.sum_ite_eq` | K09b if its hypothesis carries a kernel `S` |
| `baKpi_empty_slice`, `baKpi_empty_short` | `K^{(∅)} = Σ_b Θ^{σ_rσ_{r+1}}(a_r,b)X_b`; `‖K^{(∅)}‖ ≤ C_Σ S^n` from `‖Σ^{(∅)}‖ ≤ C_Σ` and leaf `ℓ¹ ≤ S` | `baKpi_eq_sum_SigmaPi` (merged), algebra only | K09b/K12 (the analytic `‖K^{(∅)}‖ ≲ B^{n-1}` needs K07's `(eq:molecule-decay)` and the proved `IndStepAbs`: not here, D3) |

Merged layer form: `baK_eq_sum_Kpi`, `baKpi_eq_sum_SigmaPi` (K06), not restated. `baKsolveLe3_holds` (K03) is not used for the base levels: `IsKLoopSLe 3` is not `IsKLoopS`, so `baK_unique` does not apply to it; `baKsolve` and `baTreeRep` (K05b) give the same closed forms (deviation from the ticket's source list, no change of statement).

### (ii) The instance, the argument, the numerics, the plan

**Instance** (every hypothesis of every target at once): `(d,L) = (3,4)`, `W = 2`, `t = 1/2`, `Λ = 10`, real-axis BA data `(g,E,m)` with `BASelf`, `κ = Im m > 0` (Lean: `P : FlowPt 4 10`, `P.real`; the script solves the self-consistent equation on `Z_4^3` for two `(g,E)`). `baKpi_cut`: `n = 4`, `σ = (+,+,-,+)`, `F₀ = π = {(0,2)}`, `J = (0,2)`, `π' = ∅`; `n = 5`, `σ = (+,+,-,+,+)`, `F₀ = π = {(0,2),(2,4)}` (both long, both innermost, mixed charges), cut at `(0,2)` and `(2,4)`. `baKsol_*`, `baKBoundAt_*`: the same data at `n = 1,2,3`. No external hypothesis (`baKsolve`, `baTreeRep`, `baProp5to8_holds`, `baPropM_holds` are theorems on `main`), so no limit computation.
```
$ cd T2381 && python3 k10_lattice.py
-- (d,L)=(3,4) g=0.5 E=0.3: m=-0.0961+0.6814j kappa=0.6814 rowsum|M|^2=1.000000000 |M-M^T|=5e-16 t=1/2
I1: n=4 sg=++-+ pi=[(0, 2)] J=(0, 2) n_in=3 n_out=3 sg_in=++- sg_out=+-+ pi'=[] |K^pi|=2.81e-04 |diff|=5.5e-20
I1eq: n=4 sg=++-+ pi=[(0, 2)] J=(0, 2) n_in=3 n_out=3 sg_in=++- sg_out=+-+ pi'=[] |K^pi|=9.12e-02 |diff|=5.4e-16
I2: n=5 sg=++-++ pi=[(0, 2), (2, 4)] J=(0, 2) n_in=3 n_out=4 sg_in=++- sg_out=+-++ pi'=[(1, 3)] |K^pi|=4.00e-07 |diff|=2.9e-22
I2: n=5 sg=++-++ pi=[(0, 2), (2, 4)] J=(2, 4) n_in=3 n_out=4 sg_in=-++ sg_out=++-+ pi'=[(0, 2)] |K^pi|=4.00e-07 |diff|=1.5e-21
   worst |diff| 5.4e-16
-- (d,L)=(3,4) g=1.2 E=-0.4: m=0.1818+0.5431j kappa=0.5431 rowsum|M|^2=1.000000000 |M-M^T|=1e-15 t=1/2
I1: n=4 sg=++-+ pi=[(0, 2)] J=(0, 2) n_in=3 n_out=3 sg_in=++- sg_out=+-+ pi'=[] |K^pi|=2.25e-05 |diff|=2.0e-20
I1eq: n=4 sg=++-+ pi=[(0, 2)] J=(0, 2) n_in=3 n_out=3 sg_in=++- sg_out=+-+ pi'=[] |K^pi|=5.66e-02 |diff|=1.1e-16
I2: n=5 sg=++-++ pi=[(0, 2), (2, 4)] J=(0, 2) n_in=3 n_out=4 sg_in=++- sg_out=+-++ pi'=[(1, 3)] |K^pi|=5.38e-08 |diff|=1.4e-22
I2: n=5 sg=++-++ pi=[(0, 2), (2, 4)] J=(2, 4) n_in=3 n_out=4 sg_in=-++ sg_out=++-+ pi'=[(0, 2)] |K^pi|=5.38e-08 |diff|=1.2e-22
   worst |diff| 1.1e-16
```
(`I1`, `I2`: labels pairwise distinct neighbours; `I1eq`: all four labels equal. `K^pi` is a layer sum of cactus values at fixed `a`; the right side is `t Σ_u A(u) K^{π'}(a_out(u))`, `A(u)` computed as the sum over `H ∈ TSPlong(σin,∅)` of the inner cactus with identity last leaf. The `Z_4^3` run asserts `F₀ ∈ TSP 5`, `KLFlong F₀ σ = π`, innermost.)

**Written argument for `baKpi_cut`** (route R2, tree level). (1) *Layer bijection*: `Flong_eq_iff_cut` (`J` innermost in `π`): for `F ∈ TSP n`, `J ∈ F`: `KLFlong F σ = π ⟺ KLFlong (KLFOut F J) σout = π' ∧ KLFlong (KLFIn F J) σin = ∅`; `KLsum_cut` turns `Σ_{F ∋ J}` into `Σ_{G ∈ TSP n_out}Σ_{H ∈ TSP n_in}` (as `baSigmaPi_cut`, whose assembly is copied). (2) *The `tΘ` glue*: for one tree `F ∋ J`, `BAGamma M t F σ a` is `KLgval` with leaf weights `Θ^{σ_vσ_{v+1}}` and chord `J` weighted `tΘ^{σ_iσ_j}`. `baCactus_cut` with `P = 1`, `S = t·1`, `Q = Θ^{σ_iσ_j}` has `P·S·Q = tΘ^{σ_iσ_j}` (the weight already on `J`, so the `update` is the identity) and gives `Σ_{u,w} (inner, last leaf 1ᵀ = 1, labels BAdeltaIn J a u)·t·1_{uw}·(outer, glue leaf Q, labels BAdeltaOut J a w)`; `1_{uw}` collapses `w = u`. `baCactus_leafW_out` (`J.1+2 ≤ J.2`) says the glue leaf `Θ^{σ_iσ_j} = Θ^{σout_g σout_{g+1}}`, so the outer factor is `BAGamma M t F_out σout (BAdeltaOut J a u)` itself. *Replacement of `Θ − 1 = ξ_J SΘ`*: BA has the chord `tΘ` and no `S`; the chord is the glue leaf of the outer polygon evaluated at the glue label `u` = inner root label, hence one sum `Σ_u` instead of the band's `Σ_{u,w} ξ S_{uw}`; `mul_Theta` is not needed. (3) *Leaf reattachment*: the inner cactus with leaf weights `(Θ^{σin_kσin_{k+1}})_{k<last}, 1` at labels `(a_{i..j-1}, u)` is `Σ_{δ: δ_last=u} BASigmaTree(δ)∏_{k<last}Θ(a_k,δ_k)` (copy of the private `KMolecule_gval_eq_sum`; the twin of `KLInduct_inner_eq`); summing over `H ∈ TSPlong(σin,∅)` gives `A(u)`. (4) *`W` powers*: none (`BAKpi`, `BASigmaPi` carry no `W`); `W^{-d(n-1)}` multiplies the sum over `π` once; `(n_in-2)+(n_out-1) = n-1`. (5) *Reversed leaf* (0350 C2): the leaf reversed by the cut is the inner last leaf `Pᵀ`, and `P = 1`, `1ᵀ = 1`; nothing is transposed, so `BATheta_swap`/`BAMssOf` symmetry are not used and `M` may be non-symmetric (stress run below). Alternative R1 (fallback, same size): `baKpi_eq_sum_SigmaPi` + `baSigmaPi_cut`, then reindex `Fin n → Z ≃ (KLLIn J → Z) × (KLLOut J → Z)`; heavier index arithmetic.

**Numerics** (no ODE, tolerance `1e-12`, `n = 4..6`, every `σ`, every nonempty layer `π`, every innermost `J ∈ π`; form 1 is `baKpi_cut`, form 2 its unfolding `Σ_{u,w}A(u)(tΘ)_{uw}B(w)`; `q` is the cyclic lattice `Z_q`, BA data `M(-) = M^*`):
```
$ python3 k10.py cut 6; python3 k10.py base
-- BA q=4 g=0.5 E=0.3 t=0.7 m=-0.1177+0.8281j |M-M^T|=3e-17
BA(q=4) n=4: cases=16 (|pi|>=2: 0) max|K^pi-form1|=1.1e-15 max|K^pi-form2|=1.6e-15 max|K^pi|=1.5 | control(transposed chord) 1.6e-15
BA(q=4) n=5: cases=128 (|pi|>=2: 48) max|K^pi-form1|=5.3e-15 max|K^pi-form2|=4.1e-15 max|K^pi|=3.1 | control(transposed chord) 4.1e-15
BA(q=4) n=6: cases=832 (|pi|>=2: 544) max|K^pi-form1|=2.8e-14 max|K^pi-form2|=3.1e-14 max|K^pi|=6.5 | control(transposed chord) 3.1e-14
-- BA q=3 g=1.1 E=0.0 t=0.6 m=-0.4764+0.5558j |M-M^T|=8e-17
BA(q=3) n=4: cases=16 (|pi|>=2: 0) max|K^pi-form1|=5.6e-16 max|K^pi-form2|=5.7e-16 max|K^pi|=0.92 | control(transposed chord) 5.7e-16
BA(q=3) n=5: cases=128 (|pi|>=2: 48) max|K^pi-form1|=1.2e-15 max|K^pi-form2|=1.0e-15 max|K^pi|=1.8 | control(transposed chord) 1.1e-15
BA(q=3) n=6: cases=832 (|pi|>=2: 544) max|K^pi-form1|=3.1e-15 max|K^pi-form2|=3.6e-15 max|K^pi|=3.7 | control(transposed chord) 4.1e-15
-- stress q=3 t=0.55: M(+),M(-) independent random NON-symmetric
RAND n=4: cases=16 (|pi|>=2: 0) max|K^pi-form1|=1.1e-17 max|K^pi-form2|=9.3e-18 max|K^pi|=0.026 | control(transposed chord) 2.1e-03
RAND n=5: cases=128 (|pi|>=2: 48) max|K^pi-form1|=2.1e-17 max|K^pi-form2|=2.2e-17 max|K^pi|=0.038 | control(transposed chord) 3.0e-03
RAND n=6: cases=832 (|pi|>=2: 544) max|K^pi-form1|=3.7e-17 max|K^pi-form2|=4.2e-17 max|K^pi|=0.07 | control(transposed chord) 5.6e-03
elapsed 11s
q=4 g=0.5 E=0.3 t=0.7: (a) n=3 |Gamma(empty)-Kn3sol|=2e-15; (b) level eq. n=2 9e-16, n=3 1e-14; (c) A=2.13 S=0.77 Cm=1.78 col=1.000: |K2|<=A*colsum True (ratio 0.76), |K3|<=A^2*S*Cm^2 True (ratio 0.19)
q=3 g=1.1 E=0.0 t=0.6: (a) n=3 |Gamma(empty)-Kn3sol|=5e-16; (b) level eq. n=2 4e-16, n=3 2e-15; (c) A=1.65 S=1.11 Cm=1.70 col=1.000: |K2|<=A*colsum True (ratio 0.66), |K3|<=A^2*S*Cm^2 True (ratio 0.17)
q=5 g=0.8 E=0.3 t=0.95: (a) n=3 |Gamma(empty)-Kn3sol|=1e-14; (b) level eq. n=2 3e-14, n=3 7e-13; (c) A=5.22 S=0.92 Cm=2.13 col=1.000: |K2|<=A*colsum True (ratio 0.85), |K3|<=A^2*S*Cm^2 True (ratio 0.14)
q=4 g=0.5 E=0.3 t=0.3: (a) n=3 |Gamma(empty)-Kn3sol|=3e-16; (b) level eq. n=2 1e-16, n=3 4e-16; (c) A=1.27 S=0.89 Cm=1.78 col=1.000: |K2|<=A*colsum True (ratio 0.71), |K3|<=A^2*S*Cm^2 True (ratio 0.18)
elapsed 0s
```
(Counts match T2376's (C): 16/128/832 innermost cases. (a) is `W^{-2d}Γ(∅)` against `(Kn3sol)` with `BAMLoop` in the paper pairing `σ_i` on `(b_{i-1},b_i)`; (b) the closed forms `ΘM^{σσ'}`, `(Kn3sol)` against the level equations of `kode.rhs` at `S = 1` with the analytic `t`-derivative `∂Θ = ΘM^{σσ'}Θ`.)

**Plan** (stop line 2000, `wc -l RBM3D/BA/KInduct.lean` at each commit): §1 header, pins `BAKBoundAt`, `BAKpiBoundAt`, `baKsol_one/two/three` ≈ 190; §2 `Θ`/`M` calculus (`KInduct_theta_shift`, sup, `ℓ¹` of short `Θ`, `ℓ¹` of `M`, `M^{σσ'}` column sum) ≈ 220 → commit ≈ 410; §3 `baKBoundAt_one/two/three` ≈ 280 → ≈ 690; §4 cut (`KInduct_gval_eq_sum` copy 25, inner regroup 60, tree cut 50, layer assembly 70, `baKpi_cut`, `_abs`, `_S` 70) ≈ 300 → ≈ 990; §5 `baKpi_empty_slice/short` ≈ 80 → ≈ 1070; §6 instances at `P`, `n = 4, 5`, base levels, `BAKBoundAt` at `P`, registry pre-check file ≈ 150 → ≈ 1220 (central 1100, hi 1800 of the ticket; 780 below the stop line). Imports: `BA.KMolecule`, `BA.KCactusCut`, `BA.KTreeRep`, `BA.KSolve`, `Loop.KLIndStepB`, plus `BA.Prop6Path`, `BA.CombesThomas`, `BA.KKernel`, `Loop.PureLoop` (`sum_exp_decay_centre`); not `Loop.KLInduct` (K09b edits it; `KLone_le_rpow` is copied private).

**Decisions for the dispatcher.** D1 `BAKBoundAt` is defined here (verbatim) and K12 imports it (K12 depends on K10). D2 `BAKpiBoundAt` is a new pin proposed here (twin of `KLKpiBoundAt`); K09b may instead abstract it. D3 the analytic empty-layer bound (`KLInduct_Kpi_empty_bound` twin) stays with K09b/K12 (needs K07 and the proved `IndStepAbs`). Paper-delta candidates: `T2381a` the BA cut has one glue sum with the chord `tΘ` as the outer glue leaf (no `S^{(B)}`, no `Θ − 1 = ξSΘ`), against the band's `Σ_{u,w} t A S_{uw} K`; `T2381b` `BAKBoundAt` is the uniform-constant reading of `≺` (`T2360e`, unchanged).

**Verdicts.** `baKsol_one/two/three`: PASS. `BAKBoundAt`, `BAKpiBoundAt`, `baKBoundAt_one/two/three`: PASS (inputs `baProp5_holds`, `baProp5s_holds`, `baPropM_holds`, `BAK_col_sum` are merged theorems; the chains are verified numerically with measured constants). `baKpi_cut`, `baKpi_cut_abs`, `baKpi_cut_S`: PASS (identity holds to `3e-14` on every case; no hypothesis on `M`, `t`). `baKpi_empty_slice/short`: PASS (algebra). Instances: PASS (nonvacuous, `n = 4, 5`, two-edge layer with mixed charges).

## (b) Script output — Sat Oct 10 11:38:09 UTC 2026

Stage 1b, `prover-max` (model claude-sonnet-5-5). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2381`, branch `t/T2381`. Scripts are outside the repository: scratchpad `T2381/rep/{stmt,inst,mk_b}.py|sh`, `T2381/lean/{Registry,RegistryBase,Axioms,ChkNames}.lean`.
```
$ for h in $(git log main..t/T2381 --reverse --format=%h); do echo "$h $(TZ=UTC git log -1 --format=%cd --date=format-local:%H:%M:%SZ $h) $(git log -1 --format=%b $h | grep -o 'wc -l.*') | $(git log -1 --format=%s $h | cut -c1-70)"; done
cd80776 11:08:26Z wc -l RBM3D/BA/KInduct.lean =      480 at this commit (stop line 2000). | T2381: KInduct sections 1-3 (base levels baKsol_one/two/three, baKBoun
384fd9f 11:13:32Z wc -l RBM3D/BA/KInduct.lean =      793 at this commit (stop line 2000). | T2381: KInduct sections 4-5 (baKpi_cut, baKpi_cut_S, baKpi_cut_abs, ba
fc48e8e 11:22:34Z wc -l RBM3D/BA/KInduct.lean =      976 at this commit (stop line 2000). | T2381: KInduct section 6 (compiled nonempty instances at the flow poin
47897ca 11:25:17Z wc -l RBM3D/BA/KInduct.lean =      981 at this commit (stop line 2000). | T2381: KInduct public theorems with inline binders (no hidden section
0f9fe77 11:26:13Z wc -l RBM3D/BA/KInduct.lean =      991 at this commit (stop line 2000). | T2381: KInduct instance of baKpi_cut at a non-symmetric M (0350 C2)
bccb85b 11:37:59Z wc -l RBM3D/BA/KInduct.lean =      991 at this commit (stop line 2000). | T2381: baKpi_cut docstring cites (eq:molecule-Kpi) instead of the band
$ git diff --stat main...t/T2381; wc -l RBM3D/BA/KInduct.lean; grep -cE 'sorry|admit|axiom|native_decide' RBM3D/BA/KInduct.lean
 RBM3D/BA/KInduct.lean | 991 ++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 991 insertions(+)
     991 RBM3D/BA/KInduct.lean
0
$ lake build RBM3D.BA.KInduct 2>&1 | tail -1; lake env lean RBM3D/BA/KInduct.lean 2>&1 | wc -l   # lines of warnings/errors of the module
Build completed successfully (3768 jobs).
       0
$ lake build 2>&1 | tail -1   # full library; RBM3D.lean does not import the new module yet (the hub adds it at merge)
Build completed successfully (4196 jobs).
$ lake env lean docs/tickets/checks/T2381-check.lean > /dev/null; echo exit=$?
exit=0
$ lake env lean Axioms.lean   # #print axioms of the 13 public declarations (scratch file, import RBM3D.BA.KInduct)
 [propext, Classical.choice, Quot.sound] <-  BAKBoundAt BAKpiBoundAt baKsol_one baKsol_two baKsol_three baKBoundAt_one baKBoundAt_two baKBoundAt_three baKpi_cut baKpi_cut_S baKpi_cut_abs baKpi_empty_slice baKpi_empty_short
$ lake env lean Registry.lean; lake env lean RegistryBase.lean   # import RBM3D [+ import RBM3D.BA.KInduct] + #assert_rbm_axioms
Registry exit=0 axiom audit: 11013 theorems, 3223 definitions, 0 axioms | premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
RegistryBase exit=0 axiom audit: 11000 theorems, 3221 definitions, 0 axioms | premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).
```
**Target statements, extracted from the file by script** (`stmt.py RBM3D/BA/KInduct.lean <names>`: whitespace collapsed, proof removed)
```
[KInduct.lean:55]
def BAKBoundAt (d n : ℕ) (Λ κ : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by
  omega⟩ BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L), ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)‖ ≤ C *
  (L : ℝ) ^ τ * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 1)
[KInduct.lean:66]
def BAKpiBoundAt (d n : ℕ) [NeZero n] (Λ κ : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
  BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d L), ‖BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π‖ ≤ C * (L :
  ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1)
[KInduct.lean:77]
theorem baKsol_one (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ : Fin
  1 → Bool) (a : Fin 1 → Zd d L) : BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) = PropSpin m (σ 0)
[KInduct.lean:88]
theorem baKsol_two (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ : Fin
  2 → Bool) (a : Fin 2 → Zd d L) : BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) = (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t (σ 0) (σ 1) * BAMss d L
  (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) (a 1)
[KInduct.lean:105]
theorem baKsol_three (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ :
  Fin 3 → Bool) (a : Fin 3 → Zd d L) : BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) = ∑ b₀ : Zd d L, ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, BATheta d L g E m t
  (σ 0) (σ 1) (a 0) b₀ * BATheta d L g E m t (σ 1) (σ 2) (a 1) b₁ * BATheta d L g E m t (σ 2) (σ 0) (a 2) b₂ * BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (KLloopOf d L σ ![b₀, b₁,
  b₂])
[KInduct.lean:270]
theorem baKBoundAt_one (d : ℕ) (Λ κ : ℝ) : BAKBoundAt d 1 Λ κ
[KInduct.lean:291]
theorem baKBoundAt_two {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : BAKBoundAt d 2 Λ κ
[KInduct.lean:425]
theorem baKBoundAt_three {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : BAKBoundAt d 3 Λ κ
[KInduct.lean:627]
theorem baKpi_cut {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n} (hn : 3 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}
  (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d L) : BAKpi d L n M t σ a π = ∑ u : Zd d L,
  (t : ℂ) * (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u), BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ * ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn
  J)), BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) * BAKpi d L (n - KLwIn J + 1) M t (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J))
[KInduct.lean:708]
theorem baKpi_cut_S {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n} (hn : 3 ≤ n) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)}
  (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d L) : BAKpi d L n M t σ a π = ∑ u : Zd d L, ∑
  w : Zd d L, (t : ℂ) * (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u), BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ * ∏ k ∈ Finset.univ.erase
  (Fin.last (KLwIn J)), BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) * (1 : Matrix (Zd d L) (Zd d L) ℂ) u w * BAKpi d L (n - KLwIn J + 1) M t (sigmaOut σ J)
  (BAdeltaOut J a w) ((π.erase J).image (KLshiftOut J))
[KInduct.lean:734]
theorem baKpi_cut_abs {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ) (i : ι) {n : ℕ} [NeZero n] {J : Fin n × Fin n} (hn : 3 ≤ n) (σ : Fin n → Bool)
  {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d (L i)) : BAKpi
  d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ a π = ∑ u : Zd d (L i), (t i : ℂ) * (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d (L i) => δ
  (Fin.last _) = u), BASig d (KLwIn J + 1) L g E m t i (sigmaIn σ J) δ * ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)), BAThetaOf (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i)))
  (t i) (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) * BAKpi d (L i) (n - KLwIn J + 1) (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) (sigmaOut σ J)
  (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J))
[KInduct.lean:758]
theorem baKpi_empty_slice {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (r : Fin n) : BAKpi d L n M t σ a ∅
  = ∑ b : Zd d L, BAThetaOf M t (σ r) (σ (r + 1)) (a r) b * ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = b), BASigmaPi d L n M t σ ∅ δ * ∏ i ∈ Finset.univ.erase r, BAThetaOf M t
  (σ i) (σ (i + 1)) (a i) (δ i)
[KInduct.lean:776]
theorem baKpi_empty_short {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) {Cm S : ℝ} (hCm : ∀ δ, ‖BASigmaPi d
  L n M t σ ∅ δ‖ ≤ Cm) (hS : ∀ (v : Fin n) (x : Zd d L), ∑ b, ‖BAThetaOf M t (σ v) (σ (v + 1)) x b‖ ≤ S) : ‖BAKpi d L n M t σ a ∅‖ ≤ Cm * S ^ n
$ diff <(git show t/T2360:RBM3D/Probe/T2360Pins.lean | sed -n '/^def BAKBoundAt/,/(n - 1)$/p') <(sed -n '/^def BAKBoundAt/,/(n - 1)$/p' RBM3D/BA/KInduct.lean) && echo 'def BAKBoundAt: IDENTICAL to the probe'
def BAKBoundAt: IDENTICAL to the probe
```
**Compiled nonempty instances** (`namespace KInductInst`; every example is elaborated by the build above; `inst.py`: line and head of each `example`, cut at 205 characters; the private helpers `KInduct_F5_*` prove `F₀ ∈ TSP 5`, `KLFlong F₀ σ = π` and the innermost conditions by `decide`)
```
818: example := baKsol_one 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩ ![true] ![![0, 0, 0]]
823: example := baKsol_two 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩ ![true, false] ![![0, 0, 0], ![1, 0, 0]]
828: example := baKsol_three 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩ ![true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]
833: example : ∃ C : ℝ, 0 < C ∧ ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2) (KLloopOf 3 4 ![true] ![![0, 0, 0]])‖ ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4…
842: example : ∃ C : ℝ, 0 < C ∧ ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2) (KLloopOf 3 4 ![true, false] ![![0, 0, 0], ![1, 0, 0]])‖ ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) …
851: example : ∃ C : ℝ, 0 < C ∧ ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2) (KLloopOf 3 4 ![true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]])‖ ≤ C * (4 : ℝ) ^ (1…
861: example := baKpi_cut (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true] (F₀ := {((0 : Fin 4), (2 : …
870: example := baKpi_cut (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num) (fun s : Bool => Matrix.of fun x y : Zd 3 4 => if x = ![0, 0, 0] ∧ y = ![1, 0, 0] then (if s then (1 : ℂ) el…
879: example := baKpi_cut_S (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true] (F₀ := {((0 : Fin 4), (2 …
915: example : (({((2 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5)).image (KLshiftOut ((0 : Fin 5), (2 : Fin 5)))) = {((1 : Fin 4), (3 : Fin 4))} ∧ KLwIn ((0 : Fin 5), (2 : Fin 5)) + 1 = 3 ∧ 5 - KLwIn ((0 …
925: example := baKpi_cut (d := 3) (L := 4) (n := 5) (J := ((0 : Fin 5), (2 : Fin 5))) (by norm_num) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true, true] (F₀ := {((0 : Fin 5),…
933: example := baKpi_cut (d := 3) (L := 4) (n := 5) (J := ((2 : Fin 5), (4 : Fin 5))) (by norm_num) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true, true] (F₀ := {((0 : Fin 5),…
941: example := baKpi_cut_abs (ι := Unit) 3 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => 1 / 2) () (n := 5) (J := ((0 : Fin 5), (2 : Fin 5))) (by norm_num) ![true, true, false, true, t…
951: example (h : IndStepAbs (ι := Unit) 3 3 (fun _ => 4) (fun _ => Bparam 3 4 P.g0 (1 / 2) 0) (BASig 3 3 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2)) (fun _ s s' …
972: example := baKpi_empty_slice (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] 1
979: example : ∃ S : ℝ, 0 < S ∧ ∃ Cm : ℝ, ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (fun _ => true) ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ∅‖ ≤ Cm * S ^ 4 := by obtain ⟨S, h…
```
**Name clashes, section map, routing of the base levels (1a-audit O1)**
```
$ grep -rnwE 'BAKBoundAt|BAKpiBoundAt|baKsol_(one|two|three)|baKBoundAt_(one|two|three)|baKpi_cut(_S|_abs)?|baKpi_empty_(slice|short)|KInductInst|KInduct_[A-Za-z0-9_]*' RBM3D | grep -v '^RBM3D/BA/KInduct.lean' | wc -l
       0
$ grep -n '^/-! ## ' RBM3D/BA/KInduct.lean | cut -d: -f1,2 | cut -c1-45 | paste -sd' ' -
49:/-! ## 1. The pins and the base levels of  119:/-! ## 2. The `Θ` and `M` calculus at the 260:/-! ## 3. The bounds at the base levels,  486:/-! ## 4. The cut of `K^{(π)}` at an inne 751:/-! ## 5. The layer `π = ∅` -/ 804:/-! ## 6. Compiled nonempty instances
$ grep -rlE 'KLBoundAt_(one|two|three)' RBM3D; sed -n '1191,1193p;990p;1058p' RBM3D/Loop/KLInduct.lean | cut -c1-96
RBM3D/Loop/KLInduct.lean
  obtain ⟨C₀, hC₀, H₀⟩ := KLInduct_Kpi_empty_bound d n κ gmax hd hn hκ hg hPT τ hτ
  rw [KLKpi_cut d p.L p.g p.hL hn (mSigma p.E) p.t hm σ hF₀T hπ hJ hinner a]
  · exact KLBoundAt_one (k + 2) hκ
  · exact KLBoundAt_two hκ hPT
  · exact KLBoundAt_three hκ hPT
```
**Narrative** (every number is from the output above or from the file; nothing was read, copied or built from RBM1D/RBM2D, so there is no RBM1D/RBM2D diff-stat)
- **Delivered**: two pins and eleven theorems, exactly the public table of (a): `BAKBoundAt` (identical to the probe's), `BAKpiBoundAt`, `baKsol_one/two/three`, `baKBoundAt_one/two/three`, `baKpi_cut`, `baKpi_cut_S`, `baKpi_cut_abs`, `baKpi_empty_slice`, `baKpi_empty_short`. Every other declaration is `private` with the stem `KInduct_`, and all binders of the public theorems are written inline. The file has 991 lines (§1 at :49, §2 :119, §3 :260, §4 :486, §5 :751, §6 :804); the stop line 2000 was never approached (480, 793, 976, 981, 991, 991 at the six commits); the branch differs from `main` in that file only.
- **Base levels**: `baKsol_one` is the third clause of `IsKLoopS` for `BAKsol` (`BAKsol_isKLoopS` at `baKsolve`, `Λ = g`); `baKsol_two` carries the `(Kn2sol)` clause of the `baKsolve` witness to `BAKsol` through `baK_unique` (0350 C4); `baKsol_three` is `baTreeRep` at `n = 3` with `TSP_three` and `BACactusVal_three_BAMLoop`. As announced in (a), `baKsolveLe3_holds` is not used.
- **Bounds**: `baKBoundAt_one` is the probe's proof (any `d, Λ, κ`, `C = 1`). `baKBoundAt_two`, `C = C_d`: the sup bound of `Θ` (`baProp5_holds`, translation invariance `KInduct_theta_shift`, `B_{t,|a|} ≤ B_{t,0}`) times `Σ_z |M^{(σσ')}_{zy}| = 1` (`BAMss_norm_eq_BAK`, `BAK_col_sum`). `baKBoundAt_three`, `C = C_d² S C_M²`: two neighbouring charges of a triangle agree (`KInduct_bool3`); that leaf is summed (`baProp5s_holds`, `S = C_s(1 + Λ² expC k c_s)`), the two others are sup-bounded; the `M`-loop is bounded by `|M| ≤ 1` (`BAMB_row_sq_real`) and two `ℓ¹` rows (`C_M = c⁻¹ expC k c`, `c = BAct_rate (k+2) Λ κ`, `BAMB_row_l1`); the three positions of the short leaf are the three cyclic rotations of one lemma (`KInduct_three_short`, `KInduct_three_bound`).
- **Cut** (route R2 of (a)): `KInduct_tree_cut` applies the merged `baCactus_cut` (`BA/KCactusCut.lean:1111`, imported: the file has no copy of the cut machinery) at `Lw = Θ`, `P = 1`, `S = t·1`, `Q = Θ^{(σ_i,σ_j)}`; `P S Q` is the weight already on the chord, so the update is the identity, `S = t·1` collapses the glue labels, and `baCactus_leafW_in/out` identify the leaves of the two polygons. The layer is assembled with `Flong_eq_iff_cut` and `KLsum_cut` as in `baSigmaPi_cut` (`BA/KMolecule.lean:313`). `baKpi_cut` has no hypothesis on `M` or `t`; the example at :870 applies it at a non-symmetric, non-translation-invariant `M` (0350 C2: no `BATheta_swap`, no symmetry of `M`).
- **Interface**: `baKpi_cut_abs` is `baKpi_cut` at `Sig = BASig` and `TH i = Θ` of the BA data over the family `ι`; the example at :951 takes `IndStepAbs … BASig …` as its only hypothesis and obtains the bound on `Σ_u ‖A(u)‖` by `exact`, i.e. `A(u)` is the `IndStepAbs` summand at `r = Fin.last`. `baKpi_cut_S` is the shape of `KLKpi_cut` at `S = 1`.
- **Routing** (1a-audit O1): in `Loop/KLInduct.lean` `KLBoundAt_one/two/three` occur only in docstrings (:20, :21, :119, :1185, :1233, :1266), their definitions (:223, :233, :264), `KLboundPin_holds` (:1191-1193) and the examples of §8 (:1282, :1284, :1286); `KLKpi_step` uses `KLInduct_Kpi_empty_bound` (:990) and `KLKpi_cut` (:1058). The base levels are therefore stated here in BA form (`BAKBoundAt`) for K12; only the cut and the layer `π = ∅` are generic.
- **Differences from (a)**, none changes a statement or a verdict: (1) `C_M` is the merged `BAMB_row_l1` bound, not the two-regime bound from `BAPropM` items 5, 6; (2) the imports `BA.GreenSchur` and the lemma `sum_radial_exp_decay_le` (`Defs/RadialSum.lean`) replace `BA.CombesThomas`, `Loop.PureLoop`, `sum_exp_decay_centre`; (3) the instance of `baKpi_empty_short` takes the leaf constant from `KInduct_theta_l1` and the molecule constant as a finite supremum.
- **Copies inside RBM3D** (base `442d3aa`): `KInduct_theta_perm` ← `KMolecule_theta_perm` (`BA/KMolecule.lean:166`); `KInduct_norm_sigma` ← `BKK_norm_sigma` (`BA/KKernel.lean:76`); `KInduct_one_le_rpow` ← `KLone_le_rpow` (`Loop/KLInduct.lean:219`); `KInduct_theta_l1` ← `KLedge_l1` (:168); `KInduct_gval_last` ← `KMolecule_gval_eq_sum` (`BA/KMolecule.lean:87`); `baKpi_empty_slice/short` ← `KLInduct_Kpi_empty_slice/short` (:781, :799); `baKBoundAt_one` ← the probe's `BAKBoundAt_one` (`t/T2360:RBM3D/Probe/T2360Pins.lean:318`).
- **Registry**: the pre-check passes (exit 0); the module adds 13 theorems and 2 definitions and no premise (113 before and after); `BAKBoundAt` is the conclusion of `baKBoundAt_*`, `BAKpiBoundAt` is the hypothesis of no theorem.
- **Verdict (1b)**: all targets of the ticket are built and committed on `t/T2381` (last commit `bccb85b`); no `sorry`, no new axiom; every public theorem has a compiled nonempty instance.

## (c) Verified Mathlib names used
`#check @name` on 56 Mathlib names used in `KInduct.lean` (a curated list in `T2381/mathlib_checked.txt`: the lemma names with a namespace prefix and six without; routine lemmas such as `norm_mul`, `mul_le_mul` are not listed), script `ChkNames.lean`: exit 0, no error; no name is claimed absent. The 20 below are the non-routine ones, one line each; the rest are listed after them.
- `Finset.sum_fiberwise`
- `Finset.single_le_sum`
- `Finset.sum_mul_sum`
- `Finset.prod_univ_sum`
- `Fintype.piFinset_univ`
- `Fintype.sum_equiv`
- `Finset.mul_prod_erase`
- `Finset.prod_le_prod₀`
- `Finset.sum_eq_single`
- `Finset.sum_filter`
- `Finite.bddAbove_range`
- `Equiv.addRight`
- `Equiv.subRight`
- `Matrix.inv_submatrix_equiv`
- `Matrix.nonsing_inv_eq_ringInverse`
- `Real.one_le_rpow`
- `Complex.norm_natCast`
- `Function.update_eq_self`
- `Function.update_of_ne`
- `pow_le_pow_left₀`
Also checked, same run: Complex.norm_conj, Complex.star_def, Equiv.coe_addRight, Finset.card_univ, Finset.mul_sum, Finset.ne_of_mem_erase, Finset.prod_congr, Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_nonneg, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_congr, Finset.sum_le_sum, Finset.sum_mul, Finset.sum_nonneg, Finset.sum_singleton, Fintype.card_fin, Function.update_self, List.ofFn_succ, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Matrix.one_mul, Matrix.smul_apply, Matrix.smul_mul, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_one, Nat.sub_self, add_neg_cancel, sub_eq_add_neg, norm_sum_le, norm_prod, ite_true.

## (d) Open issues and paper-delta candidates
- **Routing items of the 1a (D1-D3), unchanged**: D1 `BAKBoundAt` is defined here and K12 imports it; D2 `BAKpiBoundAt` is a new pin proposed here (no theorem of this file concludes it; K09b may abstract it); D3 the analytic layer-`∅` bound `‖K^{(∅)}‖ ≲ B^{n-1}` (the twin of `KLInduct_Kpi_empty_bound`, `Loop/KLInduct.lean:833`, used at :990) is not delivered here: it needs K07's `(eq:molecule-decay)` and a proved `IndStepAbs`; `baKpi_empty_short` takes the molecule bound as its hypothesis `hCm`.
- `baKpi_cut`, `baKpi_cut_S`, `baKpi_cut_abs` carry `3 ≤ n` as the pinned `KLKpi_cut` does; only `2 ≤ n` is used. Not in this ticket: `BAKBoundAt` for `n ≥ 4` and `BAKpiBoundAt` itself (K09b, K12).
- **`T2381a`** (candidate): the BA cut of `K^{(π)}` at an innermost long edge has one glue sum and the chord `tΘ^{(σ_i,σ_j)}` as the glue leaf of the outer polygon, `K^{(π)} = t Σ_u A(u) K^{(π')}(σ_out, a_out(u))` (Lean `baKpi_cut`), against the band's `Σ_{u,w} t A(u) S^{(B)}_{uw} K^{(π'')}(w)` through `Θ - 1 = ξ_J SΘ` (`KLKpi_cut`, `Loop/KLInduct.lean:606`); BA has no `Θ - 1 = ξ_J SΘ` (design §5). The paper gives the chord weight (`A:561`, `(f-internal2)`) but no statement of the cut.
- **`T2381b`** (candidate, = `T2360e`): `BAKBoundAt` reads `≺` of `ML:Kbound` as a loss `C L^τ` with `C` uniform in `L, W, g ≤ Λ, E, t`; `baKBoundAt_one/two/three` prove it for `n = 1, 2, 3`.
