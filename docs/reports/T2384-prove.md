Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 12:18:45 UTC 2026

Read at worktree T2384 = `2192dea` (K02, K10 merged). `main` is now `8609423` (T2380 = K07 merged after the branch point: `BA/KPure.lean`, `baSig_decay` at `:632`). No Lean written, no `lake` run. Scripts (not in the repository): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2384`: `k11.py` (modes `struct|theta|empty|cut|target`, second data set with `big`), `k11_lattice.py`, `k11_limit.py`, `summ2.py`; mirrors copied from `T2381/` (`mirror.py`, `mgraph.py`, `k6.py`, `kode.py`, `k10.py`, `k10_lattice.py`). Notation: `Ms = BAMsigma d L (BAMB d L g E m)`, `Θ^{σσ'} = BAThetaOf Ms t σ σ'`, `B = Bparam d L g t 0 = (g²+|1-t|)⁻¹+(L^d|1-t|)⁻¹`, `η = (1-t)·Im m` (as `baK_ward`, `BA/KWard.lean:290-305`), `n = m+1`, `Σ^∅ = BASigmaPi … ∅`, `X_b` = the summand of `IndStepAbs` at root `Fin.last`, `J = (i,j)`, `w = j-i`, `n_in = w+1`, `n_out = n-w+1`.

### (i) Public statements, exponent and constant table

Public statements (namespace `RBM.BA`, file `RBM3D/BA/KWardIneq.lean`; helpers `private`, stem `KWardIneq_`). Binders of the defs as `BAKBoundAt` (`BA/KInduct.lean:55`): `∀ L ≥ 3, g ∈ (0,Λ], E, m, BAReal d L g κ E m, t ∈ [0,1)`, plus `W ≥ 1` in `BAWardIneqAt` only (`BAKpi`, `BASigmaPi` carry no `W`); every constant `C` depends on `(d,n,Λ,κ,τ)` only.
| name | statement | proof | consumer |
|---|---|---|---|
| `BAWardIneqAt d n Λ κ` | `∀τ>0 ∃C>0 ∀ …, ∀σ : Fin n → Bool, a : Fin (n-1) → Zd d L:  Σ_x ‖BAKsol d L W Ms (PropSpin m) t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖ ≤ C·L^τ·(W^d η)⁻¹·(W^{-d}B)^{n-2}` (twin of `KLwardIneqAt`, `Loop/KLWardIneq.lean:90`; `Gauss.etaT ↦ (1-t)·m.im`, `KLPar ↦` the binders) | def | K12: carrier form `STKwardgL` (`Step34Pins.lean:229` `STKward` shape), `KLFinal.lean:159-162` twin |
| `KWardIneq_IndAt d k Λ κ` `[NeZero k]` | `(eq:ind-step-bound)` (`A:703`) at BA: `∀τ>0 ∃C>0 ∀ …, ∀σ r, σ r ≠ σ (r+1) → ∀a : Fin k → Zd d L: Σ_b ‖Σ_{δ_r=b} Σ^∅(σ,δ)·∏_{j≠r} Θ^{σ_jσ_{j+1}}(a_j,δ_j)‖ ≤ C L^τ B^{k-2}` = `IndStepAbs` (`KLIndStepB.lean:77`) at `BASig`, `Bp = B` | def, **premise** (owed) | K12 (from K09b `indStepAbs_of`, `KLIndStepB.lean:879`) |
| `KWardIneq_MolAt d k Λ κ` | `(eq:molecule-decay)` (`A:691`): `∃C c>0 ∀ …, ∀σ δ: ‖Σ^∅(σ,δ)‖ ≤ C·exp(-c·KLmaxDist δ)` = `SigDecayAbs` (`KLIndStepA.lean:1050`) at `BASig` | def; **theorem `baWardMol_holds`** from `baSig_decay` (ι = subtype of data) if the branch contains K07, else premise | K11 (case S) |
| `BAWardKpiAt d m Λ κ` | layer form (twin of `KLWardIneq_KpiAt`, `:662`): `∀τ ∃C ∀ …, σ : Fin (m+1) → Bool, π, a: Σ_x ‖BAKpi d L (m+1) Ms t σ (update a (Fin.last m) x) π‖ ≤ C L^τ η⁻¹ B^{m-1}` | def | K11 internal |
| `baWardIneq_two` (`3≤d` not needed) | `0<κ ⊢ BAWardIneqAt d 2 Λ κ`, every σ (`baKsol_two`, `KInduct.lean:88`; twin `KLWardIneq_At_two` `:863`) | theorem, no premise | K12 |
| `baWardKpi_empty_bound`, `baWardKpi_step`, `baWardKpi_holds` | twins of `:430`, `:675`, `:851`; `3≤d, 0<Λ, 0<κ`; premises `∀k∈[3,m+1], KWardIneq_IndAt d k`, `KWardIneq_MolAt d k`; `_step` also `hout : ∀m''∈[2,m), BAWardKpiAt d m''` | theorems | K11 |
| `baWardIneq_of_Kpi`, `baWardIneq_holds` | `BAWardKpiAt d m ⊢ BAWardIneqAt d (m+1)` (`baK_eq_sum_Kpi`, `KMolecule.lean:133`; twin `:898`); `baWardIneq_holds`: `3≤d, 0<Λ, 0<κ, 2≤n`, premises `IndAt`, `MolAt` at `k∈[3,n]` `⊢ BAWardIneqAt d n Λ κ` | theorems | K12 |

| quantity | value | constraint | slack |
|---|---|---|---|
| `n`; `m = n-1` | instance `n = 2,3,4`; numerics `2..5` | `n ≥ 2`; layers need `n ≥ 3` (`baK_eq_sum_Kpi`), step `m ≥ 2` | `n=2` has no layer |
| `w`, `n_in`, `n_out` | `w ∈ [2,n-2]`; `n_in, n_out ∈ [3,n-1]` (all 77 diagonals, `n=4..9`: 0 violations) | IH at outer size `m'' = n-w ∈ [2,m-1]`; `IndAt` at `k = n_in < n` | `n-1-n_in ≥ 0` |
| `B`-exponent | `(n_in-2)+(n_out-2) = n-2` | `= n-2` | 0 (exact) |
| loss | `L^{τ/2}·L^{τ/2} = L^τ`; empty layer, long last leaf: one `L^τ`; short last leaf: none | `L ≥ 3 ⇒ L^τ ≥ 1` | 0 (exact split) |
| `η⁻¹` | once (outer factor, or `(1-t)⁻¹ ≤ η⁻¹`) | `0 < κ ≤ Im m ≤ ‖m‖ ≤ 1` (`BAReal`; `BAm_norm_le_one`, `Ward.lean:136`) | ratio `η⁻¹/(1-t)⁻¹ = 1/Im m ∈ [1,1/κ]`; measured `Im m = 0.556..0.986` |
| `Σ_b‖Θ^{σσ'}(a,b)‖` (and column) | `≤ (1-t)⁻¹`, all four `(σ,σ')`: Neumann series in the `linfty` norm, `Σ_b‖M^{σσ'}_{ab}‖ = Σ_b BAK_{ab} = 1` (`BAMss_norm_eq_BAK` `KKernel.lean:102`, `BAK_col_sum` `:128`) | `0 ≤ t < 1` | 0: attained (ratio `1.0000`) |
| `t` prefactor | `‖t‖ ≤ 1` | `t ∈ [0,1)` | measured cut ratio `≤ 0.999` |
| `W` | `W^{-d(n-1)}η⁻¹B^{n-2} = (W^dη)⁻¹(W^{-d}B)^{n-2}` (`mul_inv`, no hypothesis on `W`) | `1 ≤ W` only as in `BAKBoundAt` | exact; layer `C_π` = `C_wardineq` at `n=3,4` (table) |
| layers | `2^{|diagonals n|}`, `|diagonals n| = n(n-3)/2` = 2, 5, 9 at `n = 4,5,6` | constant `2^{n(n-3)/2}·C_π` | none to spend |
| `S` (ℓ¹ of short `Θ`), `C_d` (sup `Θ`), `C_M` | `baProp5s_holds` (`Prop5Short.lean:667`), `baProp5_holds` (`Prop6Path.lean:850`), `B_{t,r} ≤ B_{t,0}`; used only in case (S) | `3 ≤ d`, `0<Λ`, `0<κ` | measured `S = 0.54..1.11`, `C_abs = 0.03..2.61` |

### (ii) Instance, written argument, numerics, plan

**Instance.** Lean: flow point `P : FlowPt 4 10` (`BA/MFixedPoint.lean:893`, `P.real`), `(d,L) = (3,4)`, `N = 64`, `Λ = 10`, `κ = Im m₀ > 0`, `W = 2`, `t = 1/2`, `τ = 1`. `n = 2`: `baWardIneq_two` at `σ = (+,-)`, `(+,+)`, no premise. `n = 3,4`: `baWardIneq_holds` at `σ = (+,-,+)`, `(+,+,-,-)`, spread labels, last label summed; `n = 4` also `baWardKpi_step` at `m = 3` (layers `∅`, `{(0,2)}`, `{(1,3)}`, `n_in = n_out = 3`, `hout` at `m'' = 2`). `IndAt`, `MolAt` stay hypotheses of the examples (K09b / K07 pins); every deterministic hypothesis is discharged. The script uses `(g,E) = (0.5,0.3)`, `(1.2,-0.4)` (`P` is a choice, as T2381). `W` here: `W^d = 8`.
```
$ S=…/scratchpad/T2384; cd $S && python3 k11_lattice.py
-- (d,L)=(3,4) N=64 g=0.5 E=0.3 t=0.5 W=2: kappa=Im m=0.6814 |m|=0.6881 rowsum|M|^2=1.000000000 |M-M^T|=5e-16 eta_t=0.3407 B_t0=1.3646
   n=2 sg=+-,++: sum_x|K2| = 0.25000, 0.08562 <= W^-d (1-t)^-1 = 0.25000 <= (W^d eta)^-1 = 0.36689
   n=3 sg=+-+,+++,++-: measured C = sum_x|K^(n)| / [(W^d eta)^-1 (W^-d B)^(n-2)] = 0.0444, 0.0135, 0.0431
   n=4 sg=++--,++-+,++++: measured C = sum_x|K^(n)| / [(W^d eta)^-1 (W^-d B)^(n-2)] = 0.0033, 0.0030, 0.0012
   cut n=4 sg=++-+ pi={(0,2)} J=(0,2): sum_x|K^pi(a[x])| = 2.276e-03 <= t sum_u|A_u| sum_x|K^pi'(aout(u)[x])| = 6.950e-03 <= t sum_u|A_u| max_u = 5.252e-02; sum_u|A_u| = 0.093 B (sg_in=++-, n_in=3)
-- (d,L)=(3,4) N=64 g=1.2 E=-0.4 t=0.5 W=2: kappa=Im m=0.5431 |m|=0.5728 rowsum|M|^2=1.000000000 |M-M^T|=1e-15 eta_t=0.2716 B_t0=0.5467
   n=2 sg=+-,++: sum_x|K2| = 0.25000, 0.09039 <= W^-d (1-t)^-1 = 0.25000 <= (W^d eta)^-1 = 0.46029
   n=3 sg=+-+,+++,++-: measured C = sum_x|K^(n)| / [(W^d eta)^-1 (W^-d B)^(n-2)] = 0.0291, 0.0141, 0.0242
   n=4 sg=++--,++-+,++++: measured C = sum_x|K^(n)| / [(W^d eta)^-1 (W^-d B)^(n-2)] = 0.0056, 0.0042, 0.0028
   cut n=4 sg=++-+ pi={(0,2)} J=(0,2): sum_x|K^pi(a[x])| = 5.266e-04 <= t sum_u|A_u| sum_x|K^pi'(aout(u)[x])| = 2.487e-03 <= t sum_u|A_u| max_u = 1.805e-02; sum_u|A_u| = 0.081 B (sg_in=++-, n_in=3)
```
**External hypotheses, limit computation** (`IndAt`, `MolAt` are K09b's and K07's statements for `d ≥ 3`; the scan is the `d = 1` mirror of T2374/T2376/T2381, `B = (g²+1-t)⁻¹+(q(1-t))⁻¹`, `L = q → 24`, every σ, every `a`; entries `C_ind/C_abs`; `C_ind = max Σ_b|X_b|/B^{n-2}` over long last leaves, `C_abs = max (Σ_δ|Σ^∅ ∏Θ|)(1-t)/B^{n-2}` over short last leaves):
```
$ cd $S && python3 k11_limit.py
t=0.7 n=3 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 0.472/0.634  q=8: 0.503/0.610  q=12: 0.534/0.642  q=16: 0.553/0.663  q=24: 0.572/0.687
t=0.7 n=4 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 0.355/0.129  q=6: 0.354/0.135  q=8: 0.395/0.147  q=12: 0.447/0.166
t=0.99 n=3 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 0.556/1.323  q=8: 0.566/1.274  q=12: 0.580/1.153  q=16: 0.611/1.072  q=24: 0.690/1.007
t=0.99 n=4 (g=0.5,E=0.3) C_ind/C_abs by q: q=4: 1.008/0.014  q=6: 1.022/0.017  q=8: 1.045/0.016  q=12: 1.134/0.016
```
Bounded on the scanned range (slow drift of `C_ind`, `d = 1`); the `d ≥ 3` statements are K09b's and K07's gates, not claimed here.

**Written argument** (band `KLWardIneq.lean` steps that touch the star structure (22% of its lines, `T2360-design.md:38,159`) and their cactus replacements; the induction skeleton, the exponent bookkeeping and the case split are unchanged). (1) *Scalars* (`:101-127`, `Gauss.etaT`, `(mE E).im ≤ 1`): `η = (1-t)Im m`, `κ ≤ Im m ≤ ‖m‖ ≤ 1`, so `0 < η ≤ 1-t` and `(1-t)⁻¹ ≤ η⁻¹`. (2) *`ℓ¹` of a leaf* (`:135-153`, `Theta_transpose_of_three_le`, `sum_norm_Theta_row_le`, star `Θ(ξ)` with `‖μ‖=1`): column sum `=` row sum by `BATheta_isSymm` (`KBase.lean:371`, BA data) and `Σ_b‖Θ^{σσ'}(a,b)‖ ≤ (1-t)⁻¹` for all `σσ'` by the Neumann series (new, ≈ 70 lines; the `ℓ¹` norm of `M^{σσ'}` is `1` by `BAMss_norm_eq_BAK`). (3) *Empty layer* (`:155-523`): `K^∅(a[x]) = Σ_b Θ^{σ_vσ_{v+1}}(x,b) X_b` is `baKpi_empty_slice` (`KInduct.lean:758`, root `r = Fin.last`) plus the `ℓ¹` step; long last leaf: `Σ_b|X_b| ≤ C L^τ B^{n-2}` is `IndAt` at `k = n`, loss `L^τ`; short last leaf (not covered by the paper's displayed line `A:816-818`, which writes `Θ^{(+,-)}`; paper-delta `T2384b`): `|Σ^∅| ≤ C e^{-cD}` (`MolAt`), all leaves but vertex `0` and `v` are `≤ C_d B` (`baProp5_holds`, `B_{t,|a|} ≤ B_{t,0}`), vertex `0` is summed (`≤ (1-t)⁻¹`, (2)), `Σ_{δ_0=y} e^{-cD} ≤ expC^{n-1}` (copy of `KLWardIneq_sum_exp_maxDist`, generic lattice sums, `sum_exp_decay_centre`), and the last leaf has `ℓ¹ ≤ S` (`baProp5s_holds`): `Σ_x|K^∅| ≤ S·C(1-t)⁻¹B^{n-2}`, no `L^τ`. (4) *Cut* (`KLKpi_cut`, `Σ_{u,w} ξ A S^{(B)}_{uw} K`, then `Σ_w|S^{(B)}_{uw}| = 1`): `baKpi_cut` (`KInduct.lean:627`) gives one glue sum `t Σ_u A(u) K^{π'}(σout, BAdeltaOut J a u)` (chord `tΘ` = glue leaf, no `S^{(B)}`, paper-delta `T2381a`), so `Σ_x|K^π| ≤ t (Σ_u|A_u|)·sup_u Σ_x|K^{π'}(aout(u)[x])|` by the triangle inequality, `Σ_u|A_u| ≤ C L^{τ/2}B^{n_in-2}` (`IndAt`, `A` is the summand of `IndStepAbs`, `baKpi_cut_abs` `:734`) and the outer sum by the IH at `τ/2` (`η⁻¹ B^{n_out-2}`). Label bookkeeping (twins of `aIn_update`, `aOut_update`, `:531-595`, over `BAinVinv`, `BAdeltaOut`, `KCactusCut.lean:44,59`): `A` sees only `a_i..a_{j-1}` (`j ≤ n-1`), the last outer vertex is `n-1`, the glue vertex is not last (`struct` line below). (5) *Assembly* (`:898`): `baK_eq_sum_Kpi` gives `W^{-d(n-1)}Σ_π K^π`, `2^{|diagonals n|}` layers, `(W^{-d})^{n-1}η⁻¹B^{n-2} = (W^dη)⁻¹(W^{-d}B)^{n-2}`. (6) `n = 2`: `baKsol_two` and (2). **`baK_ward` does not enter** (neither the paper's proof `A:811-826` nor the band file uses a Ward identity; at `n = 2`, `σ = (s,-s)` the bound is the Ward value: `|W^d(1-t)Σ_x K2 - 1| ≤ 2.2e-15`). Orientation (0350 C2): no non-symmetric-`M` fact; `baKpi_cut` is valid for any `M` (T2381, RAND run); symmetric `Θ` is used only at BA data. Range-uniform (1155 C1): no smallness of `g`, no `(Cλ)^{|a-b|}` form; measured below at `g = 0.05..4.67`.

**Numerics** (no ODE; identities by relative defect `‖a-b‖_∞/max(1,‖a‖_∞) ≤ 1e-12`; bounds with measured constants; `d = 1` cyclic mirror, `W = 2`; every σ, every layer, every innermost `J`, every `a` with the last label summed; `n = 2..5`, `q = 5` to `n = 4`). `C_ind`, `C_abs`: the premises' constants; `C_empty`, `C_π`: layers `π = ∅`, `π ≠ ∅`; `C_wardineq`: target (W cancels); cut: `max lhs/rhs` of `Σ_x|K^π| ≤ t Σ_u|A_u| Σ_x|K^{π'}(aout(u)[x])|`.
```
$ cd $S && python3 k11.py struct; for m in theta empty cut target; do python3 k11.py $m > out_$m.txt; python3 k11.py $m big > out_big_$m.txt; done; python3 summ2.py
n=4..9, all 77 diagonals J=(i,j): w=j-i in [2,n-2]; n_in=w+1, n_out=n-w+1 in [3,n-1]; (n_in-2)+(n_out-2)=n-2; j<=n-1; inner labels a_i..a_(j-1) avoid a_(n-1); glue vertex != last; last outer vertex = vertex n-1. violations: 0
data (d_lat=1) | Im m | l1(Theta) row,col /(1-t)^-1 | S | n=2: sum|K2|/(W^d eta)^-1 | n=3/4/5: C_ind | C_abs | C_empty | C_pi | C_wardineq | cut chain max lhs/rhs (n=4/5)
q=4 g=0.5 t=0.7 | 0.828 | 1.0000,1.0000 | 0.77 | 0.828 | 0.47/0.35/0.03 | 0.63/0.13/0.08 | 0.39/0.29/0.02 | -/0.10/0.08 | 0.39/0.29/0.18 | -/0.91/0.94
q=3 g=1.1 t=0.6 | 0.556 | 1.0000,1.0000 | 1.11 | 0.556 | 0.87/1.17/0.40 | 1.01/0.50/0.71 | 0.48/0.65/0.22 | -/0.21/0.28 | 0.48/0.65/0.76 | -/0.90/0.96
q=5 g=0.8 t=0.95 | 0.700 | 1.0000,1.0000 | 0.92 | 0.700 | 0.63/0.81/- | 1.44/0.11/- | 0.44/0.53/- | -/0.24/- | 0.44/0.53/- | -/0.99/-
q=4 g=0.5 t=0.3 | 0.828 | 1.0000,1.0000 | 0.89 | 0.828 | 0.63/0.49/0.19 | 0.72/0.36/0.22 | 0.52/0.41/0.16 | -/0.07/0.06 | 0.52/0.41/0.27 | -/0.74/0.85
q=4 g=4.67 t=0.7 | 0.693 | 1.0000,1.0000 | 1.00 | 0.693 | 1.59/4.30/0.78 | 2.61/2.10/1.30 | 1.10/2.98/0.54 | -/1.22/3.30 | 1.10/2.98/6.12 | -/1.00/1.00
q=4 g=0.05 t=0.9 | 0.986 | 1.0000,1.0000 | 0.54 | 0.986 | 0.42/0.33/0.05 | 0.75/0.03/0.09 | 0.41/0.32/0.05 | -/0.15/0.12 | 0.41/0.32/0.19 | -/0.99/1.00
max relative identity defect (K0 = sum_b Theta X_b; K^pi = form1; sum_F Gamma = sum_pi K^pi) over all runs: 1.5e-14
```
All chains held (assertions in the scripts): `Σ_x|K^∅| ≤ colmax(Θ_last)·Σ_b|X_b| ≤ colmax·(absolute sum)`, the cut chain, `Σ_b‖Θ‖ ≤ (1-t)⁻¹` (attained), `W^d(1-t)Σ_x|K2| = 1` for `(s,-s)`. The statement `lem_wardineq_K` holds on every case with `C_wardineq ≤ 6.12` (largest at `g = 4.67`, `n = 5`), uniformly in `t ∈ [0.3,0.95]`, `g ∈ [0.05,4.67]`.

**Plan** (stop line 2000, `wc -l RBM3D/BA/KWardIneq.lean` at each commit; imports `BA.KInduct`, `BA.KMolecule`, `Loop.KLSumZeroWard` (`exists_innermost`, `Flong_subset_diagonals` are public, `:577`, `:594`), `Loop.PureLoop`; `BA.KWard` is not needed; `BA.KPure` if rebased): §1 header, pins ≈ 120; §2 `η` facts 35, Neumann `ℓ¹` 70, copies of `KInduct_theta_sup/_l1` (private there, `:188`, `:203`) 75, misc 20 → ≈ 320; §3 empty layer (slice + `ℓ¹` step 60, two lattice-sum copies 90, absolute sum 110, bound 70) ≈ 330 → ≈ 650; §4 label twins ≈ 65 → ≈ 715; §5 triangle step 25, step 230, induction 25, `n = 2` 50, assembly 70 + final 20 ≈ 420 → ≈ 1135; §6 instances ≈ 140 → ≈ 1275; `baWardMol_holds` ≈ 45 → ≈ 1320 (ticket 800 / 1100 / 1800; 680 below the stop line).

**Decisions for the dispatcher.** D1 *Registry (differs from the ticket's "none expected")*: `#assert_rbm_axioms` fails on a `Prop` def that a theorem assumes and no theorem concludes (`Test/Axioms.lean:415-440` `scanPremises`; `unregistered` at `:506-510`). `KWardIneq_IndAt` is such a premise: one owed line `RBM.BA.KWardIneq_IndAt` (`(eq:ind-step-bound)` at BA, `A:703`; K12 concludes it from K09b `indStepAbs_of`, K08b `SigSumZeroAbs`, K07 `baSig_decay`) is needed by the hub at merge (precedent: T2368 Amend 1, one `owedProps` line for `RBM.BA.BAKsolve`); `KWardIneq_MolAt` needs none under D2. Inline binders would hide the premise from the ledger; not recommended. D2 `t/T2384` is at `2192dea`, K07 merged at `8609423`: merge `main` into the branch before 1b so `baWardMol_holds` (from `baSig_decay`, `SigDecayAbs` at `BASig`) discharges `MolAt`; otherwise a second owed line. D3 the ticket's text that `baK_ward` enters is not borne out; `import RBM3D.BA.KWard` is dropped (K12 still uses `baK_ward` for `BAKward`). D4 K09b's analytic empty-layer bound (T2381 D3: `BAKpiBoundAt`, sup form, `B^{n-1}`) is a different statement from this file's sum-over-last-label layer bound; both consume `IndAt`. Paper-delta candidates: `T2384a` `(wardineq_K)` read with uniform constants `C(d,n,Λ,κ,τ)` and `η = (1-t)Im m`; `T2384b` short last leaf (`σ_n = σ_1`) absent from `A:816-818`, proved here as in the band; `T2384c` K11 is conditional on `(eq:ind-step-bound)` (and `(eq:molecule-decay)` unless D2) as premises, not the unconditional lemma; `T2381a` reused.

**Verdicts.** `BAWardIneqAt`, `baWardIneq_two`: PASS. `KWardIneq_IndAt`, `KWardIneq_MolAt` (statements): PASS (true on all scanned data). `BAWardKpiAt`, `baWardKpi_empty_bound`, `baWardKpi_step`, `baWardKpi_holds`, `baWardIneq_of_Kpi`, `baWardIneq_holds`: PASS (conditional on `IndAt`, `MolAt`; special-case/conditional form, not the unconditional `lem_wardineq_K`). Instances: PASS (nonvacuous, `n = 2,3,4`). Stop lines: none hit (0350 C2, 1155 C1, 2000).

## (b) Script output — Sat Oct 10 12:56:41 UTC 2026

Branch `t/T2384`, HEAD `7dac9b5`, one file changed. Scripts and logs are in the scratchpad `T2384/` (not in the repository). Times are `date -u`; the git reflog is in local time (-0700).
```
$ git reflog --date=iso | grep "merge main"; git log --oneline main..t/T2384; git diff --stat main...t/T2384
5bc433a HEAD@{2026-10-10 05:29:12 -0700}: merge main: Fast-forward
7dac9b5 T2384: BA/KWardIneq docstring wording
4b8cca3 T2384: BA/KWardIneq docstring, nondegeneracy certificates
b9038aa T2384: BA/KWardIneq section 7 (compiled instances), header
fec3467 T2384: BA/KWardIneq sections 4-6 (labels, step, induction, n = 2, assembly)
edec007 T2384: BA/KWardIneq sections 1-3 (statements, l1 bounds, empty layer)
 RBM3D/BA/KWardIneq.lean | 1338 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1338 insertions(+)
$ for c in edec007 fec3467 b9038aa 4b8cca3 7dac9b5; do echo "$c $(git show $c:RBM3D/BA/KWardIneq.lean | wc -l)"; done
edec007      692
fec3467     1130
b9038aa     1308
4b8cca3     1338
7dac9b5     1338      # stop line 2000: not hit
```
```
$ rm <the 5 build files of RBM3D.BA.KWardIneq>; lake build RBM3D.BA.KWardIneq     # 12:52:43 UTC, HEAD 7dac9b5
✔ [3770/3770] Built RBM3D.BA.KWardIneq (5.5s)
Build completed successfully (3770 jobs).      # grep -n KWardIneq build_final.log: this one line (no warning from the file)
$ lake build     # whole library of the branch (no root import of the module), started 12:49:48 UTC at 4b8cca3
Build completed successfully (4198 jobs).      # `#assert_rbm_axioms` in RBM3D.lean: 11024 theorems, 3225 definitions, 0 axioms
$ lake env lean ax.lean     # #print axioms of the 13 new public declarations: BAWardIneqAt KWardIneq_IndAt KWardIneq_MolAt BAWardKpiAt KWardIneq_Data baWardMol_holds KWardIneq_IndAt_of_abs baWardIneq_two baWardKpi_empty_bound baWardKpi_step baWardKpi_holds baWardIneq_of_Kpi baWardIneq_holds
$ grep -c 'propext, Classical.choice, Quot.sound' ax.out; grep -vc 'propext, Classical.choice, Quot.sound' ax.out
13
0
$ grep -nE 'sorry|admit|native_decide|^axiom|[^A-Za-z]axiom ' RBM3D/BA/KWardIneq.lean | wc -l
0
$ lake env lean docs/tickets/checks/T2384-check.lean; echo exit=$?     # 9 #check outputs, 0 error lines
exit=0
$ grep -rn -e KWardIneq -e BAWardIneqAt -e BAWardKpiAt -e baWardIneq -e baWardKpi -e baWardMol RBM3D --include='*.lean' | grep -v '^RBM3D/BA/KWardIneq.lean' | wc -l
0
$ git grep -n -e KWardIneq_ -e BAWardIneqAt -e BAWardKpiAt -e baWardIneq_ -e baWardKpi_ -e baWardMol_holds main -- RBM3D | wc -l     # main = 69b7abc
0
```
Registry pre-check (ticket target 3): `precheck.lean` = `import RBM3D`, `import RBM3D.BA.KWardIneq`, `#assert_rbm_axioms`; then the same file text without `KWardIneq_IndAt_of_abs` and its example (`nobridge.lean`):
```
$ lake env lean precheck.lean | grep -n 'axiom audit\|premises found\|error'
1:axiom audit: 11042 theorems, 3238 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
91:premises found by scanning: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13).     # no error line; the library without the module: 113 (borrowed 1, owed 48, structural 45, refuted 6, superseded 13)
$ lake env lean nobridge.lean | grep -A1 error
nobridge.lean:1304:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, ...:
  [RBM.BA.KWardIneq_IndAt]
```
Target statements, extracted from the file by script (`extract.py`; line number = declaration line; proofs omitted):
```
93: def BAWardIneqAt (d n : ℕ) (Λ κ : ℝ) : Prop :=
      ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ →
        ∀ (E : ℝ) (m : ℂ),
          haveI : NeZero L := ⟨by omega⟩
          BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin (n - 1) → Zd d L),
            ∑ x : Zd d L,
                ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖
              ≤ C * (L : ℝ) ^ τ * (((W : ℝ) ^ d) * ((1 - t) * m.im))⁻¹ *
                  (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 2)

106: def KWardIneq_IndAt (d k : ℕ) [NeZero k] (Λ κ : ℝ) : Prop :=
      ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (r : Fin k), σ r ≠ σ (r + 1) →
          ∀ a : Fin k → Zd d L,
            ∑ b : Zd d L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin k → Zd d L => δ r = b),
                BASigmaPi d L k (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ ∅ δ *
                  ∏ j ∈ Finset.univ.erase r,
                    BAThetaOf (BAMsigma d L (BAMB d L g (E : ℂ) m)) t (σ j) (σ (j + 1)) (a j) (δ j)‖
              ≤ C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (k - 2)

119: def KWardIneq_MolAt (d k : ℕ) [NeZero k] (Λ κ : ℝ) : Prop :=
      ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin k → Bool) (δ : Fin k → Zd d L),
          ‖BASigmaPi d L k (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ ∅ δ‖
            ≤ C * Real.exp (-(c * (KLmaxDist d L δ : ℝ)))

129: def BAWardKpiAt (d m : ℕ) (Λ κ : ℝ) : Prop :=
      ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (z : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin (m + 1) → Bool)
          (π : Finset (Fin (m + 1) × Fin (m + 1))) (a : Fin (m + 1) → Zd d L),
          ∑ x : Zd d L,
              ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ (Function.update a (Fin.last m) x) π‖
            ≤ C * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1)

141: structure KWardIneq_Data (d : ℕ) (Λ κ : ℝ) where  -- fields L hL g hg hgΛ E m hr t ht0 ht1 (lines 142-152)

363: theorem baWardMol_holds {d k : ℕ} [NeZero k] (hd : 3 ≤ d) (hk : 3 ≤ k) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
        KWardIneq_MolAt d k Λ κ := by

376: theorem KWardIneq_IndAt_of_abs {d k : ℕ} [NeZero k] {Λ κ : ℝ}
        (h : IndStepAbs (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => Bparam d i.L i.g i.t 0)
          (BASig (ι := KWardIneq_Data d Λ κ) d k (fun i => i.L) (fun i => i.g) (fun i => i.E) (fun i => i.m) (fun i => i.t))
          (fun i s s' => BAThetaOf (BAMsigma d i.L (BAMB d i.L i.g (i.E : ℂ) i.m)) i.t s s')) :
        KWardIneq_IndAt d k Λ κ := by

1068: theorem baWardIneq_two (d : ℕ) {Λ κ : ℝ} (hκ : 0 < κ) : BAWardIneqAt d 2 Λ κ := by

658: theorem baWardKpi_empty_bound (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
        (hInd : KWardIneq_IndAt d (m + 1) Λ κ) (τ : ℝ) (hτ : 0 < τ) :
        ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (z : ℂ),
          haveI : NeZero L := ⟨by omega⟩
          BAReal d L g κ E z → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d L),
            ∑ x : Zd d L, ‖BAKpi d L (m + 1) (BAMsigma d L (BAMB d L g (E : ℂ) z)) t σ (Function.update a (Fin.last m) x) ∅‖
              ≤ C * (L : ℝ) ^ τ * ((1 - t) * z.im)⁻¹ * (Bparam d L g t 0) ^ (m - 1) := by

864: theorem baWardKpi_step (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
        (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ m + 1 → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ)
        (hout : ∀ m'' : ℕ, 2 ≤ m'' → m'' < m → BAWardKpiAt d m'' Λ κ) :
        BAWardKpiAt d m Λ κ := by

1046: theorem baWardKpi_holds (d m : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hm : 2 ≤ m) (hΛ : 0 < Λ) (hκ : 0 < κ)
        (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ m + 1 → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ) :
        BAWardKpiAt d m Λ κ := by

1120: theorem baWardIneq_of_Kpi (d m : ℕ) {Λ κ : ℝ} (hκ : 0 < κ) (hm : 2 ≤ m) (h : BAWardKpiAt d m Λ κ) :
        BAWardIneqAt d (m + 1) Λ κ := by

1183: theorem baWardIneq_holds (d n : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hn : 2 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ)
        (hInd : ∀ k : ℕ, 3 ≤ k → k ≤ n → ∀ [NeZero k], KWardIneq_IndAt d k Λ κ) :
        BAWardIneqAt d n Λ κ := by
```
Compiled nonempty instances, namespace `KWardIneqInst` (`extract_inst.py`; flow point `P` of `(d,L) = (3,4)`, `Λ = 10`, `κ = Im m₀`, `W = 2`, `t = 1/2`, `τ = 1`; every `example` is in the file, lines 1193-1337):
```
L1209 example: The flow point is a datum of the family `KWardIneq_Data`. -/
L1213 example: **`baWardIneq_two`** at the flow point (`n = 2`, `σ = (+,-)` and `(+,+)`, `W = 2`, `t = 1/2`, `τ = 1`): `∑_x |
      obtain ⟨C, hC, H⟩ := baWardIneq_two 3 (Λ := 10) P.real.1.1 1 one_pos
L1231 example: **`baWardIneq_holds`** at the flow point, `n = 3` (`σ = (+,-,+)`) and `n = 4` (`σ = (+,+,-,-)`): `∑_x |𝒦^{(n)}
      · obtain ⟨C, hC, H⟩ := baWardIneq_holds 3 3 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1
      · obtain ⟨C, hC, H⟩ := baWardIneq_holds 3 4 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1
L1254 example: **`baWardKpi_empty_bound`** at the flow point, `n = 4` (`m = 3`): the layer `π = ∅` with the last label summed
      obtain ⟨C, hC, H⟩ := baWardKpi_empty_bound 3 3 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd4 1 one_pos
L1269 example: **`baWardKpi_step`** at the flow point, `n = 4` (`m = 3`): the three layers `π = ∅`, `{(0,2)}`, `{(1,3)}` of `
      obtain ⟨C, hC, H⟩ := baWardKpi_step 3 3 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd
      (fun m'' h2 hlt => baWardKpi_holds 3 m'' (Λ := 10) le_rfl h2 (by norm_num) P.real.1.1
L1289 example: **`baWardKpi_holds`** at `m = 2` (`n = 3`, the triangle, `π = ∅` the only layer) and **`baWardIneq_of_Kpi`**: 
L1298 example: **`baWardMol_holds`** at the flow point (`k = 4`): `|Σ^{(∅)}(σ,δ)| ≤ C e^{-c max|δ_i - δ_j|}` with distinct la
      obtain ⟨C, hC, c, hc, H⟩ := baWardMol_holds (d := 3) (k := 4) le_rfl (by norm_num) (Λ := 10) (by norm_num) P.real.1.1
L1307 example: **`KWardIneq_IndAt_of_abs`** at the flow point's family: the abstract `IndStepAbs` (the output of `indStepAbs_
      obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
      obtain ⟨C, hC, H⟩ := baWardIneq_holds 3 4 (Λ := 10) le_rfl (by norm_num) (by norm_num) P.real.1.1 hInd 1 one_pos
L1330 example: **Nondegeneracy of the instances above**: for `σ = (+,+,-,-)` the last leaf is long (`σ_3 ≠ σ_0`, the case (L)
```

**Narrative (b)** (facts from the logs above and the files):
- *Base (D2 of (a)).* `t/T2384` was at `2192dea`; `git merge --ff-only main` (reflog above, 12:29:12 UTC) moved it to `5bc433a`, which has K07 (`RBM3D/BA/KPure.lean`, `baSig_decay`). The branch diff is the one file. `main` has moved on (`69b7abc`); T2382 moved `FlowFM`, `PrecL` and the generic `…gL` predicates out of `BA/FlowPins.lean` into `Chain/Carrier.lean`; the file mentions none of those names (`grep -c "FlowFM\|PrecL\|gL\b\|Carrier"` = 0) and was not rebuilt against `69b7abc` (the hub's full build at merge does that).
- *D1 (registry) is resolved without an owed line.* (a) planned `KWardIneq_IndAt` as a premise with one owed line in `Test/Axioms.lean`. The file adds `KWardIneq_IndAt_of_abs` (`IndStepAbs` over the family `KWardIneq_Data d Λ κ`, the output of `indStepAbs_of`, gives `KWardIneq_IndAt`), a theorem that concludes the premise. The pre-check passes with no change of `Test/Axioms.lean` (113 premises found with and without the module), and the same text without that theorem fails with exactly `[RBM.BA.KWardIneq_IndAt]`. Additions to (a)'s public table: `KWardIneq_Data` (a structure of the data `(L, g, E, m, t)` with their hypotheses, no other field), its `NeZero` instance, `KWardIneq_IndAt_of_abs`. If the dispatcher drops them, one owed line `RBM.BA.KWardIneq_IndAt` is needed instead.
- *`MolAt` is not a hypothesis.* (a)'s table lists `KWardIneq_MolAt` as a premise "if the branch contains K07, else premise"; the branch contains K07, so `baWardMol_holds` (`baSig_decay` at `ι = KWardIneq_Data d Λ κ`, no hypothesis beyond `3 ≤ d`, `3 ≤ k`, `0 < Λ`, `0 < κ`) is used inside `baWardKpi_empty_bound`; no public theorem takes `MolAt` (only the private `KWardIneq_abs_sum_le` does). The only open premise is `KWardIneq_IndAt` at `k ∈ [3, n]`.
- *D3.* `baK_ward` does not enter; the imports are `BA.KInduct`, `BA.KMolecule`, `BA.KPure` (no `BA.KWard`).
- *Routes that differ from (a)'s plan.* The `ℓ¹` bounds `Σ_b |Θ^{(s,s')}(a,b)| ≤ (1-t)⁻¹` and `Σ_a |Θ^{(s,s')}(a,b)| ≤ (1-t)⁻¹` (all four charge pairs) come from the resolvent identities of `BATheta_resolvent` and `Σ_b |M^{(s,s')}_{cb}| = Σ_b K_{cb} = 1`, not from a Neumann series (private `KWardIneq_row_of_resolvent`, `_col_of_resolvent`, `KWardIneq_theta_row_le`, `_col_le`). `baKpi_cut` has one glue sum, so `KWardIneq_norm_cut_sum_le` has no kernel `S^{(B)}`. Case (S) turns the row bound of property 5' into a column bound with `BATheta_isSymm` (BA data); no fact for non-symmetric `M` is used (0350 C2: `baKpi_cut` has no hypothesis on `M`). Constants are chosen before `L, W, g, E, m, t` and depend on `(d, n, Λ, κ, τ)` only; nothing assumes `g` small (1155 C1). No correction of (a) is needed ((a′) not written).
- *Ports* (all from RBM3D's own merged files, none from RBM1D or RBM2D, so there is no RBM1D/RBM2D diff-stat): `KInduct_theta_perm`, `_shift`, `_sup`, `_l1`, `KInduct_one_le_rpow` (`BA/KInduct.lean:128, 147, 188, 203, 265`, commit `306957f`; private there) and `KLWardIneq_sum_slice`, `_sum_exp_maxDist`, `_aIn_update`, `_aOut_update` (`Loop/KLWardIneq.lean:220, 255, 531, 550`, commit `b06ff9b`; private there). The empty layer, the step, `n = 2` and the assembly are twins of `Loop/KLWardIneq.lean:430, 675, 863, 898` (replacements in the module docstring). Size 1338 lines against the plan ≈ 1320 of (a) and the stop line 2000.
- *Instances.* Each target of the ticket has a compiled `example` at the flow point: `baWardIneq_two` (`σ = (+,-)`, `(+,+)`), `baWardIneq_holds` (`n = 3, 4`), `baWardKpi_empty_bound` (`σ = (+,+,-,-)` long last leaf, `(+,+,-,+)` short last leaf), `baWardKpi_step` (`m = 3`, layers `∅`, `{(0,2)}`, `{(1,3)}`; `decide` certificates in the last `example` show both chords long and both layers nonempty), `baWardKpi_holds` (`m = 2, 3`), `baWardIneq_of_Kpi`, `baWardMol_holds`, `KWardIneq_IndAt_of_abs` (via `IndStepAbs` at sizes 3 and 4). Hypotheses left in the examples: `KWardIneq_IndAt` or `IndStepAbs` only (K09b/K12's pin; its limit check is in (a)).

## (c) Verified Mathlib names (each by `#check @name` in `chk.lean`, imports of `RBM3D.BA.KWardIneq`; 118 candidate tokens, 116 names pass, the other 2 (`J`, `q`) are local variables, not names; grouped by namespace)
```
root: Ne, add_halves, add_neg_cancel, add_zero, half_pos, inv_anti₀, inv_pos, ite_true, le_div_iff₀, le_of_eq, le_rfl, le_trans, mul_inv, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_one, mul_pos, mul_pow, neg_mul, norm_add_le, norm_inv, norm_mul, norm_nonneg, norm_pow, norm_prod, norm_sum_le, norm_zero, nsmul_eq_mul, one_div, one_mul, one_pos, pow_add, pow_le_pow_left₀, pow_nonneg, pow_succ, pow_zero, smul_eq_mul, sub_eq_add_neg, sub_eq_zero, true_and, zero_le_one
Complex: im_le_norm, norm_natCast, norm_real
Equiv: addRight, coe_addRight, subRight
Fin: last_add_one, lt_def, snoc_castSucc, snoc_last, update_snoc_last, val_last, val_zero
Finset: card_erase_of_mem, card_powerset, card_univ, le_sup, mem_erase, mem_filter, mem_range, mem_univ, mul_prod_erase, mul_sum, ne_of_mem_erase, nonempty_iff_ne_empty, prod_congr, prod_const, prod_le_prod₀, prod_nonneg, prod_univ_sum, single_le_sum, sum_add_distrib, sum_comm, sum_congr, sum_const, sum_const_zero, sum_empty, sum_fiberwise, sum_ite_eq, sum_ite_eq', sum_le_sum, sum_mul, sum_neg_distrib, sum_nonneg
Fintype: card_fin, mem_piFinset, sum_equiv
Function: update_of_ne, update_self
List: ofFn_succ, ofFn_succ'
Matrix: add_apply, inv_submatrix_equiv, mul_apply, nonsing_inv_eq_ringInverse, of_apply, one_apply, smul_apply, sub_apply, submatrix_apply, transpose_apply
Nat: add_sub_cancel, cast_nonneg, lt_or_ge, strong_induction_on
NeZero: pos
Real: exp_le_exp, exp_pos, exp_sum, norm_of_nonneg, one_le_rpow, rpow_add, rpow_nonneg
```
Not reachable from the BA imports: `KLone_le_rpow` (`Loop/KLInduct.lean:219`; `Unknown identifier` in `t0.lean`), copied as `KWardIneq_one_le_rpow`. `Mathlib.olean` does not exist in this build (`import Mathlib` fails), so names were checked through the module's imports.

## (d) Open issues and paper-delta candidates
- `T2384a`: `(wardineq_K)` is read with constants `C(d, n, Λ, κ, τ)` uniform in `L ≥ 3`, `W ≥ 1`, `g ∈ (0, Λ]`, the real-axis data and `t ∈ [0,1)`, loss `L^τ`, and `η_t = (1-t) Im m` (`1_2:721`).
- `T2384b`: the short last leaf `σ_n = σ_1` is not covered by the paper's displayed line `A:816-818` (it writes `Θ^{(+,-)}_{t,a_n b_n}`); case (S) is proved here (`KWardIneq_abs_sum_le`), as in the band.
- `T2384c`: K11 is conditional on `(eq:ind-step-bound)` (`KWardIneq_IndAt`) as a premise, not the unconditional lemma (the paper's proof applies the already established `(eq:ind-step-bound)`, `A:809-818`); the induction is on polygon vertices, not on molecules (the band's difference (i)).
- `T2381a` (reused): the BA chord is `tΘ^{(σ_i,σ_j)}`, one glue sum, no `S^{(B)}` and no `Θ - 1 = ξ_J SΘ`.
- Open for K12: produce `IndStepAbs` over `KWardIneq_Data d Λ κ` (`indStepAbs_of`, `Loop/KLIndStepB.lean:879`: needs `IndStepTH`, `SigDecayAbs` (K07 `baSig_decay`) and `SigSumZeroAbs` (K08a/K08b) at BA) and apply `KWardIneq_IndAt_of_abs`; K12 consumes `BAWardIneqAt` for the carrier form `STKwardgL`.
- Hub: root import `import RBM3D.BA.KWardIneq` after the last `import` line of `RBM3D.lean` (no `Test/Axioms.lean` line is needed, see (b)). `1 ≤ W` is a hypothesis of `BAWardIneqAt` (as in `BAKBoundAt`) that no proof uses.
