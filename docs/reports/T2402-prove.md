Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 02:47:55 UTC 2026
Stage 1a = the ticket's design gate (CONTROL H194). No Lean was written. Notation: `u=(a,o)` (block `a`, offset `o`), `X=√t V` in-block GUE (`svar d L W 0`: `S_uk=W^{-d}1_{[k]=[u]}`, `Σ_kS_uk=1`), `D=g₀Ψ⊗I`, `G=(D+X−z_t)⁻¹`, `M=M^B⊗I`, `m=M_uu`, `Δ=G−M`, `Y=X+tm`, `v̄_a=W^{-d}Σ_oΔ_{(a,o)(a,o)}`, `E_u=condRow` (integrates row `u` of `X`).
Citations `path:N` are relative to `RBM3D/` on main `1181514`; `7_8:N` is `paper/tex/7_8_light_weight.tex`. Scripts and verbatim outputs: `docs/reports/T2402/{consts5c,disp,ravg,rem,fit,inst5c,ibpcost}.py` with `consts5c.out`, `disp_g.out`, `disp_g2.out`, `disp_szP.out`, `ravg_d1.out`, `ravg_d3.out`, `rem.out`, `fit.out`, `inst5c.out`, `ibpcost.out` (`stab.py` is the T2390 module, byte-identical).

### (i) Exponent table and design rows
| row | quantity (g = 1/64 / 1 / 10; L = 64 / 96 / 128, w = 1.2i / 1.2i / 1.0i, `consts5c.out`) | constraint | slack |
|---|---|---|---|
| N1 | `κ` design 0.5 / 0.25 / 0.04; `Im m(z)` 0.8325 / 0.3435 / 0.0439 (uniform in `L`) | `κ ≤ Im m(z)` (`BAdom`) | 1.67× / 1.37× / 1.10× |
| N2 | `|m₀|=|M_uu|` 0.9995 / 0.6420 / 0.2095; `g₀` 0.0130 / 0.5350 / 2.0955 | `κ ≤ |m₀| ≤ 1` (`BAMB_diag_eq` `BA/Ward.lean:89`, `BAm_norm_le_one` `:136`); `g₀ ≤ Λ=10` | 2.0× / 2.6× / 5.2×; 770× / 18.7× / 4.8× |
| N3 | minor-replacement constant `2/κ` = 4 / 8 / 50 (band: `2`, `Green/CondDom.lean:697`, `|G_ii|≥1/2`) | `|G_uu| ≥ κ−δ ≥ κ/2` needs `δ ≤ κ/2` | instance B `δ=W^{-1}=1/32 ≤ κ/2=1/4` (`κ=1/2`): 8× |
| N4 | `ρ_off=Σ_{b≠a}|M_ab|` observed 0.0833 / 15.27 / 447.0 | finite, uniform in `L` (`BAMfine_row_l1` `BA/GreenSchur.lean:173`; analytic `c⁻¹expC` 4.9e15 / 1.6e17 / 1.5e21, T2390 (a), only eventual) | — |
| N5 | `Σ_{b≠a}|M_ab|²` = 0.001015 / 0.587849 / 0.956090 | `=1−|m₀|²` (Ward, `BAMB_ward_row` `Ward.lean:108`) | equal to 6 digits |
| N6 | `Σ_kS_uk` = 1.000000000000 (`L=4,W=2`, `inst5c.out`) | `=1` for `3 ≤ L` (`IBP_sum_svarF_row` `Green/IBP.lean:1205`) | exact |
| N7 | slope in `W` (`fit.out`): `R_uu` pointwise −0.50 / −0.49 (`d=1`, `g=1,10`), −1.51 / −1.50 (`d=3`); `⟨R⟩_a` −1.00 / −1.01 (`d=1`), −3.01 / −2.93 (`d=3`) | `R~Ψ=W^{-d/2}` first order, `⟨R⟩~Ψ²=W^{-d}` (not claimed here, D5) | `⟨R⟩/R`: 0.345 / 0.177 / 0.129 vs `W^{-d/2}` 0.354 / 0.192 / 0.125 (`d=3,g=10,W=2,3,4`) |
| N8 | window `[W^{-d/2}, W^{-ε₀}]` at `sz0`, `n=0` (`W=32`, `ε₀=1/10`): `[5.52e-3, 0.707]`, `Ψ=W^{-1}=0.0313`; `δ=W^{-1}` | nonempty iff `ε₀ ≤ d/2`; `size^{-1} ≤ Ψ²` (`IBPRem_hΨlow_of_floor` `Green/IBPRem.lean:126`) | `size^{-1}=4.8e-7 ≤ 9.8e-4` |
| N9 | first-order bound of `R`: `ρ(3/2(δ+√A_b)+√X_b)/Ψ` = 2.1e19 / 9.2e21 / 7.1e22 (`GreenCore_Ab/Xb/R0` `BA/GreenCore.lean:1348-1355`, T2390 instance data) | finite, `(d,κ,𝔡)` only; a `≤` statement, nothing is absorbed | eventual in `n` only (as `K_BA`, T2390 R2) |
| N10 | Stein check, 2e6 draws of row `u` per `g`, 24 z-scores per run: max `|z|` 2.29 (`disp_g.out`, seed 12345), 2.01 (`disp_g2.out`, seed 999), 1.44 (`disp_szP.out`: `L=4,W=2,g=10,t=1/2`) | `E_u[(YG)_uy]=−tΣ_kS_uk E_u[(G_kk−m)G_uy]` | `|mean LHS|` 0.117 vs `|mean(LHS−RHS)|` 2e-4 at `g=1/64`, `y=u` |
| N11 | display remainder (`rem.out`), `RMS|KE_uu|/W^{-d}` at `W=2,3,4`: 0.530/0.309/0.205 (`g=1/64`), 0.029/0.017/0.011 (`g=1`), 0.034/0.020/0.013 (`g=10`) | `KE=tΣ_kS_uk ibpRem(u,k;y) ≲ Ψ²`, `‖Δ‖_maxW^{d/2}∈[0.89,1.17]` (`g=1,10`) | decreasing in `W` |

**D1 (i) display** (exact; `GreenSchur.lean:219`, `GreenCore_E0` `GreenCore.lean:755`). `M_uu=m` and `M_uv=0` for `v∈[u]∖u` (offsets differ, `BAMfine_eq` `GreenSchur.lean:93`), so `Δ_uy=−m(YG)_uy+R_uy`, `R_uy:=−Σ_{v≠u}M_uv(YG)_vy` (`v` in other blocks, offset `o(u)`; `|Δ_uu+m(YG)_uu−R_uu|`=2.5e-16, `inst5c.out`). Stein in row `u` (`∂_pG=−G B_p G`, the squared off-diagonal terms cancel between the two tags): `E_u[−m(YG)_uy]=t m Σ_kS_uk E_u[(G_kk−m)G_uy]` for every `y` (checked N10, `y=u`, same block, same-offset/other-offset other blocks). At `y=u` this is the band display `condExpDiag_eq_sum_Sblk` (`Green/IBP.lean:1227`) with `m=M_uu` constant; hence `E_uΔ_uu=t m²v̄_{[u]}+t mΣ_kS_uk ibpRem(u,k)+E_uR_uu`, `ibpRem(u,k)=E_u[G_uu(G_kk−m)]−m(G_kk−m)` (`:1331`, `ibpRem_eq_add` `:1344`). The off-diagonal analogue (`y≠u`: `ibpRem(u,k;y)=E_u[(G_kk−m)G_uy]−M_uy(G_kk−m)`, non-scalar `M_uy` kept) has no consumer: stated, not pinned.
**D2 band terms** (`Green/IBP.lean`, class): replaced by merged BA facts: `green_sub_smul_one_eq` `:92` → `BAGt_sub_BAMfine`/`GreenCore_E0`, `zt_im_ne_zero_of_lt_one` `:271` → hypothesis `z.im≠0` (`ba_G_data` `BA/GreenLDE.lean:55`). **New term: `R`** (no band counterpart: `(MYG)_ii=m(YG)_ii` there). Class-G twins over `D+seqHflow` (574 band lines, `ibpcost.out`): `hasDerivAt_green_Hflow_update` `:142`, `tame_green_apply` `:279`, `hasDerivAt_green_apply_update` `:315`, `tame_green_mul_mul_green_apply` `:344`, `tame_const_mul_green_apply` `:722`, `tame_const_mul_sandwich_apply` `:736`, `hasDerivAt_const_mul_green_apply_update` `:953`, `condRow_coord_mul_Bmat_mul_green_diag` `:1000`, `condRow_Hflow_mul_green_diag` `:1043`, `tame_Hflow_mul_green_apply` `:1165`, `condExpDiag_eq_sum_Sblk` `:1227`, `ibpRem(_eq_add)` `:1331/:1344`. Reused as they are (statements free of `green`): `hasDerivAt_Hflow_update` `:122`, `sum_gvar_Bmat_sandwich_diag(_mul)` `:675/:686` (arbitrary `G`), `condRow_coord_mul` `:884`, `condRow_const_mul/finsetSum/tame_add/tame_sub` `:911-1190`, `IBP_sum_svarF_row` `:1205`, `gaussIBP` (`Green/IBPPoly.lean:309`, any `Sizes`), `finDepOffRow_of_minor` (`Green/FlucVanish.lean:309`, any `F`), `perTimeDomAt_condRow_of_envelope` (`Green/CondDom.lean:496`). Not needed: the full-expectation lemmas `integral_coord_mul_*` `:368/:755`.
**D3 layout (C5)**: no, the new file does not cost "about 100" more. Twin `574×(0.73/0.97/1.61)` = 419 / 557 / 924 lines against in place `574×(0.15/0.24/0.30)` = 86 / 138 / 172: **+333 / +419 / +752** (ratios of `T2378-design.md` §1). In place needs a certificate-lane merge (supervisor 1155 C5, 52-62 min per merge); the new file does not. Dispatcher chooses; the pins below are for the new file.
**D4 (ii) remainder.** `ibpRem(u,k)` for `k∈[u]∖u`: `G_kk−m=Δ_kk` (`M_kk=m`), `|G_ku|=|Δ_ku|` (cross-offset: `M_ku=0`, one lemma from `BAMfine_eq`), minor replacement `|G_kk−G^{(u)}_kk| ≤ (2/κ)|G_ku||G_uk|` (N3), `ibpRem_eq_add` + conditionalisation: `≺Ψ²`; `k=u`: `≺1` with weight `S_uu=W^{-d}≤Ψ²`; so `|E_u[−m(YG)_uu]−t m²v̄_{[u]}| ≺ Ψ²`. Needs only the entrywise local law, no loops. **Finding F1:** `R_uu` is first order. `E_uΔ_uu−t m²v̄` is not `≺Ψ²` pointwise (N7: `R_uu` slope `−d/2`); the `Ψ²` gain holds for the offset average `⟨R⟩_a` (slope `−d`), which is G5a/G5b's two-block fluctuation averaging (supervisor 2254 G1), not claimed here. `R` is kept exact: `R_uu=tΣ_{b'≠a}M_ab'v̄_{b'}G_{vu}−Σ_{b'≠a}M_ab'[(A_v+tv̄_{b'})G_vu+𝔛_vu]`, `v=(b',o)` (`GreenCore_E1` `:84`, `GreenCore_Arow_eq` `:651`), first order by `GreenCore_Xi` `:1130` and `GreenCore_Xstar` `:1066`.
**D5 (iii) interface.** From G3a (merged): `E0,E1,Arow_eq,Xi,Xstar,vbar,K,E3`; G3b's `baStab_of_real` (`BA/GreenStab.lean:46`) is not used. G5a: none needed (`o(x)≠o(y)⇒M_xy=0⇒G_xy=Δ_xy` is re-proved in 12 lines; import T2401's if merged). G6a supplies `hll`. **Finding F2:** T2401 `G.5-G.6` (`docs/reports/T2401-prove.md`, read at 02:46 UTC, unaudited) proves `BAGbEXPav` from `BAFAav`, `baStab_of_real`, `GreenCore_E3`, with Schur moments `E_u𝔛=0` and no Stein display: on that route no row consumes G5c. The display is the band-parallel route (`IBPDetThm` `Green/LocalLaw.lean:186`, T2378 §5 row G6b). Decision for the dispatcher (before 1b): drop 1b, keep File 1 only (certificate, 760 lines), or run both.
**D6 (iv) C1/G2.** Uniform facts only: `κ≤|m|≤1`, `M_uu=m`, Kronecker support, `Σ_kS_uk=1`, `‖M_xy‖≤1`; `g₀≤Λ=10` enters only through merged `ρ`, `c₀`, `2dg₀` (`Xi`). Not used: `g≤W^{-ε}`, smallness of `‖M−m₀I‖`, `(Cλ)^{|a-b|}`, `c_λ`; no `∃c` before the flow; constants at `g=1/64,1,10` in N1-N9.
**D7 (v) pins, files, split.** File 1 `BA/GreenIBP.lean` (stem `GreenIBP_`; imports `Green.IBP`, `BA.GreenSchur`): 560 / 760 / 1210 (twins 419/557/924, `R`-algebra and display 60/90/140, instances 80/110/150). File 2 `BA/GreenIBPRem.lean` (imports File 1, `BA.GreenCore`, `Green.CondDom`): 730 / 1020 / 1600 (`IBPRem` T-lines 467×(0.73/0.97/1.61), cross-offset and minor 50/70/110, `R_eq/R_bound` 100/150/230, `BAIBPDet` 120/180/260, instances 120/170/250). Total 1290 / 1780 / 2810 against the ticket's 946 / 1531 / 2294; every file `<` the 2000 stop line at `hi`; the split is forced (central total > 1500). Registry owed lines: none (`BAIBPDet` is a theorem; `hll`, `hΩ` are premises). Pseudo-Lean, to be compiled in `RBM3D/Probe/T2402Pins.lean` by a Lean-capable step:
```
-- File 1.  G η := green (D + Matrix.of fun i j => seqHflow sz n t η i j) z ;  Y η := seqHflow.. + (t*m)•1 ;  R η i j := -Σ_{v∈univ.erase i} M i v * (Y η * G η) v j
theorem GreenIBP_condRow_Hflow_mul_G_diag (hD : D.IsHermitian) (hz : z.im ≠ 0) (ht : 0 ≤ t) (i) (ω) :   -- IBP:1043 with D
  condRow sz n i (fun η => (seqHflow sz n t η * G η) i i) ω = -(t * Σ k, svarF d (sz.L n) (sz.W n) (sz.lam n) i k * condRow sz n i (fun η => G η i i * G η k k) ω)
theorem GreenIBP_delta_eq (hD) (hz) (hMR' : M * (D - s•1) = 1) (hzs : z = s - t*m) (hMd : ∀ i, M i i = m) (i η) :
  G η i i - m = -m * (Y η * G η) i i + R η i i
theorem GreenIBP_display (hD) (hz) (ht : 0 ≤ t) (hL : 3 ≤ sz.L n) (i) (ω) :
  condRow sz n i (fun η => -m * (Y η * G η) i i) ω = t * m * Σ k, svarF.. i k * condRow sz n i (fun η => G η i i * (G η k k - m)) ω
theorem GreenIBP_ibpRem_eq_add (i k ω) : ibpRem i k ω = condRow i (fun η => (G η i i - m)*(G η k k - m)) ω + m*(condRow i (fun η => G η k k - m) ω - (G ω k k - m))
-- File 2.  Ω δ n := {ω | ∀ x y, ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ δ n}
theorem GreenIBP_cross_offset (hm : 0 < (BAmF sz lam0 E n).im) (hku : k ≠ u) (hb : (split d _ _ k).1 = (split d _ _ u).1) : BAMfine sz lam0 E n k u = 0
theorem GreenIBP_minor_replace (hκ : 0 < κ) (hGuu : κ/2 ≤ ‖G u u‖) (hk : k ≠ u) : ‖G k k - greenMinor G u k k‖ ≤ (2/κ) * ‖G k u‖ * ‖G u k‖
theorem GreenIBP_R_eq (hyps of GreenCore_Arow_eq) (u : Vtx d L W) : R u u = t Σ_{b'≠u.1} Mb u.1 b' * vbar b' * G (b',u.2) u - Σ_{b'≠u.1} Mb u.1 b' * ((Arow + t*vbar)(b',u.2) * G (b',u.2) u + Xrow G X (b',u.2) u)
theorem GreenIBP_R_bound (hyps of GreenCore_Xi ∧ GreenCore_Xstar) (u y) : ‖R u y‖ ≤ Σ_{b'≠u.1} ‖Mb u.1 b'‖ * (3/2 * (t*‖vbar b'‖ + Bxi (b',u.2)) + Bxs (b',u.2) y)   -- Bxi, Bxs = right sides of :1130, :1066
def BAIBPDet (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0<κ → 0<ε → 0<𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ δ : ℕ → ℝ, (∀ n, 0 ≤ Ψ n) →
  (∀ᶠ n, W^(-d/2) ≤ Ψ n) → (∀ᶠ n, Ψ n ≤ W^(-ε₀)) → (∀ᶠ n, δ n ≤ κ/2) → HighProbAt (seqP (sz.withLam 0)) sz.size (Ω δ) →
  PrecL sz (seqP (sz.withLam 0)) (U := Idx × Idx) (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Ψ n) →      -- hll: ‖G_t-M‖_max ≺ Ψ
  PrecL sz (seqP (sz.withLam 0)) (U := Idx) (fun n u ω => ‖condRow sz n u (fun η => -m n * (Y η * G η) u u) ω - t n * m n ^ 2 * vbar [u]‖) (fun n _ _ => Ψ n ^ 2)
theorem baIBPDet_holds (hd : 1 ≤ d) : BAIBPDet d      -- Ω-form `BAIBP_rem_off` (U := {q // q.1≠q.2 ∧ same block}, ζ=Ψ²), `BAIBP_rem_diag` (ζ=1)
```

### (ii) One concrete nondegenerate instance
**A (File 1; `R_eq`; display).** Merged one-point data `szP` (`BA/CouplingWindow.lean:849-864`): `d=3, L=4, W=2` (`N=512`), flow point of `z_S(4,10)`, `t=1/2`, one GUE sample. `python3 docs/reports/T2402/inst5c.py` (Part A, verbatim):
```
  flow data: g0=4.672337 E=1.1e-15 m0=-0.000000+0.560680j |m0|=0.5607 t0=0.2183 (t=1/2 > t0: outside the flow window, irrelevant for the identity); Im z_t=0.2803 > 0; 3 <= L: True
  hypotheses: D Hermitian residual 0.0e+00;  (D - s) M = 1 residual 5.1e-15;  M_uu = m0 residual 1.7e-15;  z = s - t m0: 0.0e+00
  S row sum sum_k S_uk = 1.000000000000; S_uk = W^-d 1([k]=[u]) support 8 sites = W^d = 8; M_ku = 0 for k != u in [u]: max = 0.0e+00; M_uv != 0 only at the offset of u: 0.0e+00
  identities: |Delta + M Y G|_max = 1.0e-14;  |Delta_uu + m0 (YG)_uu - R_uu| = 2.5e-16;  R_uu = 0.05329+0.01604j, Delta_uu = -0.05244+0.06969j, ||Delta||_max = 0.3271 (all non-zero)
```
The display at this data (`python3 docs/reports/T2402/disp.py 2 20 100000 777 4 10 0.5`, `disp_szP.out`): `y=u`: `|mean LHS|=0.00664`, `mean(LHS−RHS)=+2.78e-05−2.77e-05i`, `SE=5.5e-05,1.1e-04`, `z=+0.51,−0.25`; the other three `y`-types `|z|≤1.44`.
**B (File 2; `BAIBPDet`, `baIBPDet_holds`).** `d=3`, `sz0` (`Defs/Sizes.lean:260`), `flow_sz0` (`κ,ε,𝔠,𝔡 = 1/2, 1/10, 1/6, 1/10`, `BA/FlowPins.lean:1214`), `t≡1/2<BAflowT0` (`half_lt_t0` `:1254`), `ε₀=1/10`, `Ψ=δ=W^{-1}`; `python3 docs/reports/T2402/inst5c.py` (Part B, verbatim; `Kenv=B=1`):
```
  n   L    W        size       lam       t0     1/2<=t0  delta<=k/2  W^-3/2<=Psi<=W^-eps0  size^-1<=Psi^2  (1/eta+1)^2<=size  Im m0   |m0|
  0  4   32       2097152    1.562e-02 0.6937  True      True        True              True            True          0.9995 0.9995
  3  16  32768    144115188075855872 3.815e-06 0.6944  True      True        True              True            True          1.0000 1.0000
```
(`n=1,2` in `inst5c.out`, all `True`.) Every deterministic hypothesis holds for all `n`; `hΩ` and `hll` (G6a's output, T2401 G.6) stay hypotheses of the example. No external input (DECISIONS) is used, so no limit computation is owed; the scale of `hll` is attained: `‖Δ‖_maxW^{d/2}∈[0.89,1.17]` (`d=3`, `g=1,10`, `W=2..4`), `[0.80,1.31]` (`d=1`, `g=1`, `W=4..128`), `[0.12,0.18]` (`d=1`, `g=10`) (`fit.out`): `‖Δ‖_max ≤ 1.31 W^{-d/2}` throughout. `GreenIBP_R_bound` is instantiated at the hypothesis data of the merged G3a instance (`GreenCoreInst`, `GreenCore.lean:1684`): its value is the finite N9 number, not small.

**Verdicts.** `GreenIBP_display`, `GreenIBP_delta_eq`, `GreenIBP_ibpRem_eq_add`: PASS (exact, N6, N10, instance A). `BAIBP_rem_off/diag`, `baIBPDet_holds`: PASS as the row-`u` statement (N3, N8, N11, instance B); it is not a statement for `E_uΔ_uu` (F1). `GreenIBP_R_eq`, `GreenIBP_R_bound`: PASS, first order only. Layout check D3: not within 100 lines (+419 central). F2 (no consumer on T2401's route) is for the dispatcher. Paper-delta candidates: `T2402a` the BA display carries the non-scalar term `R` (band: none); `T2402b` the IBP pin is for the row-`u` part, the pointwise `Ψ²` form for `E_uΔ_uu` is false (N7); `T2402c` `2/κ` replaces the band's `2` (N3).

## (a′) Preflight corrections — Sun Oct 11 03:17:31 UTC 2026
Found while writing the pins of (a) (v) as Lean (section (a″)); none changes a verdict of (a). Probe lines are `RBM3D/Probe/T2402Pins.lean` at `4b5f864`.
1. `GreenIBP_R_eq`: (a) (v) has "(hyps of GreenCore_Arow_eq)" (`hM`, `hMd`, `hw`: `BA/GreenCore.lean:651-652`). The pin takes the hypotheses of `GreenCore_E1` (`:84`): `G * (D + X - z • 1) = 1`, `hM`, `∀ u, G u u ≠ 0`. `hMd` and `z = s - t m` are not hypotheses; `t`, `m` are free (probe `:128-135`).
2. `BAIBPDet`: (a) (v) has `condRow sz n u`. The pin has `condRow (sz.withLam 0) n u` (`GreenIBP_dispLHS`, probe `:183-185`): the row-`u` integral is over the law of `X`, `Sizes.seqP (sz.withLam 0)` ((a) (i); as `BAGiiGEX`, `BA/Step1Boot.lean:79`). `condRow sz` integrates against `Sizes.seqP sz`.
3. `GreenIBP_ibpRem_eq_add`: (a) (v) lists no hypotheses; the pin has `D.IsHermitian` and `z.im ≠ 0`, as the other File 1 pins (probe `:102-107`).
4. `GreenIBP_minor_replace`: `hk : k ≠ u` is kept as in (a) (v); its squared twin `GreenCore_m1` (`BA/GreenCore.lean:400`) has no `k ≠ u` hypothesis.

## (a″) Probe compile — Sun Oct 11 03:17:31 UTC 2026
Stage 1a probe step (CONTROL H194, as T2390 Amend 1 D1), role prover-max. Probe: `/Users/junyin/Lean_proof/RBM3D-wt/T2402/RBM3D/Probe/T2402Pins.lean`, 592 lines, branch `t/T2402`, commit `4b5f864` (never merged, no root import). It has defs, `#check` lines and 12 `example`s; no theorem: each theorem of (a) (v) is a `Prop` `GreenIBP_<name>_pin`, `BAIBPDet` is a `def`. Compile run on the clean tree (`git status --short` printed no line), started Sun Oct 11 03:15:21 UTC 2026, finished Sun Oct 11 03:15:37 UTC 2026:
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2402 && lake env lean RBM3D/Probe/T2402Pins.lean > out.txt 2>&1; echo "exit code: $?"
exit code: 0
$ cat out.txt        # the 20 `#check` lines, verbatim
@GreenIBP_G : {d : ℕ} →
  (sz : Sizes d) →
    (n : ℕ) →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
        ℂ → ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
@GreenIBP_Y : {d : ℕ} →
  (sz : Sizes d) → (n : ℕ) → ℝ → ℂ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
@GreenIBP_R : {ι : Type} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Matrix ι ι ℂ → Matrix ι ι ℂ → ι → ι → ℂ
@GreenIBP_rem : {d : ℕ} →
  (sz : Sizes d) →
    (n : ℕ) →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ →
        ℂ → ℂ → ℝ → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ
GreenIBP_condRow_Hflow_mul_G_diag_pin : Prop
GreenIBP_delta_eq_pin : Prop
GreenIBP_display_pin : Prop
GreenIBP_ibpRem_eq_add_pin : Prop
GreenIBP_cross_offset_pin : Prop
GreenIBP_minor_replace_pin : Prop
GreenIBP_R_eq_pin : Prop
GreenIBP_Bxs : (d L W : ℕ) →
  [NeZero L] →
    Matrix (Vtx d L W) (Vtx d L W) ℂ →
      Matrix (Vtx d L W) (Vtx d L W) ℂ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (Zd d L → Zd d L → ℝ) → Vtx d L W → Vtx d L W → ℝ
GreenIBP_Bxi : (d L W : ℕ) →
  [NeZero L] →
    Matrix (Vtx d L W) (Vtx d L W) ℂ →
      Matrix (Vtx d L W) (Vtx d L W) ℂ →
        Matrix (Vtx d L W) (Vtx d L W) ℂ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (Zd d L → Zd d L → ℝ) → Vtx d L W → ℝ
GreenIBP_R_bound_pin : Prop
@GreenIBP_Omega : {d : ℕ} → (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → (ℕ → ℝ) → ℕ → Set sz.SeqΩ
@GreenIBP_hll : {d : ℕ} → Sizes d → (ℕ → ℂ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
@GreenIBP_dispLHS : {d : ℕ} → (sz : Sizes d) → (ℕ → ℂ) → (n : ℕ) → ℝ → Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ
@GreenIBP_concl : {d : ℕ} → Sizes d → (ℕ → ℂ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
BAIBPDet : ℕ → Prop
baIBPDet_holds_pin : Prop
```
```
$ grep -nE "sorry|admit|axiom|native_decide|^theorem|^lemma" RBM3D/Probe/T2402Pins.lean ; echo "grep exit $?"
grep exit 1
$ grep -rln "GreenIBP_\|BAIBPDet\|baIBPDet_holds" /Users/junyin/Lean_proof/RBM3D/RBM3D /Users/junyin/Lean_proof/RBM3D-wt/*/RBM3D
/Users/junyin/Lean_proof/RBM3D-wt/T2402/RBM3D/Probe/T2402Pins.lean
$ sed -n 201,210p RBM3D/Probe/T2402Pins.lean        # BAIBPDet, verbatim
def BAIBPDet (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ δ : ℕ → ℝ, (∀ n, 0 ≤ Ψ n) →
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
          (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          (∀ᶠ n in atTop, δ n ≤ κ / 2) →
          HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (GreenIBP_Omega sz z t δ) →
          GreenIBP_hll sz z t Ψ → GreenIBP_concl sz z t Ψ
```
Pins, probe lines and instances (`:N` are lines of the probe; every deterministic hypothesis of each example is discharged, `i`, `u`, `y`, `ω` arbitrary where free):
| pin of (a) (v) | `Prop` / def | example | data |
|---|---|---|---|
| `GreenIBP_condRow_Hflow_mul_G_diag` | `_pin` `:71` | `:280` | `sz0.withLam 0`, `n=0`, `t=1/2`, `D=g₀Ψ`, `z=z_t` (flow `flow_sz0`) |
| `GreenIBP_delta_eq` | `_pin` `:81` | `:287` | same, `M=BAMfine`, `s=E+m`, `M_ii=m` (`BAMfine_eq`, `BAMB_diag_eq`) |
| `GreenIBP_display` | `_pin` `:93` | `:302` | same, `3 ≤ L` |
| `GreenIBP_ibpRem_eq_add` | `_pin` `:102` | `:308` | same |
| `GreenIBP_cross_offset` | `_pin` `:113` | `:315` | `sz0`, `n=0`: `k=e_0`, `u=0` in `Z_128^3`, `Im m>0` |
| `GreenIBP_minor_replace` | `_pin` `:120` | `:336` | `Fin 2`, `G=[[1,1/2],[1/2,1]]`, `κ=1`, `k=1`, `u=0` |
| `GreenIBP_R_eq` | `_pin` `:128` | `:343` | `sz0`, `n=0`, `t=1/2`, every `ω` (`GreenCore_carrier`) |
| `GreenIBP_R_bound` | `_pin` `:152` | `:403` | `sz0`, `n=3`, `t₁=10⁻¹¹`, `ω₀=0`, `κ=1/2`, `Φ=1`, `δ=2·10⁻⁷`, `ρ=S=4096`, `φ≡3` (data of `BA/GreenCore.lean:1684-1966`) |
| `BAIBPDet` | def `:201` | `:352` | `sz0`, `flow_sz0`, `t≡1/2`, `ε₀=1/10`, `Ψ=δ=W⁻¹`; `hΩ`, `hll` stay hypotheses |
| `baIBPDet_holds` | `_pin` `:214` | `:374` | `d=3` |
Resolutions of the pseudo-Lean of (a) (v) besides (a′):
- `G η`, `Y η`, `R η i j` are `GreenIBP_G` (`:44`), `GreenIBP_Y` (`:49`), `GreenIBP_R` (`:58`, any index type: File 1 `Idx`, File 2 `Vtx`). The examples at `:270`, `:273` show `GreenIBP_Y (sz.withLam 0) n t (BAmF ..) ω = BAflowPert ..` (`rfl`) and `BAGt .. = GreenIBP_G (sz.withLam 0) n (g₀ Ψ) z_t ..` (`BAGt_eq_green`, `BA/GreenLDE.lean:46`).
- `ibpRem i k ω` is `GreenIBP_rem` (`:63`; the band `ibpRem`, `Green/IBP.lean:1331`, at free `m`). `vbar [u]` is `GreenCore_vbar (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (STblk sz n u)`. `Ω δ`, `hll`, the conclusion are `GreenIBP_Omega`, `GreenIBP_hll`, `GreenIBP_concl` (`:173-193`).
- `Bxi`, `Bxs` are `GreenIBP_Bxi` (`:143`), `GreenIBP_Bxs` (`:138`), the right sides of `GreenCore_Xi` (`BA/GreenCore.lean:1142-1145`) and `GreenCore_Xstar` (`:1076-1077`); the example at `:403` (`hxi`, `hxs`) states those two theorems with these right sides and it compiles.
- The File 1 examples use `sz0` at `n=0` and not `szP` of (a) (ii) A: the bundle `flow_sz0` and `GreenCore_carrier` supply the hypotheses, and the pins are generic in `sz`. The `szP` numerics of (a) are unchanged.
- In the example at `:403` the large deviation inputs `hLrow`, `hLcol`, `hLquad`, `hLdiag` and `hΩ` are discharged at `X = 0`, `t₁ > 0` as in `BA/GreenCore.lean:1761-1826`; `G ≠ M` is proved in the probe (`iΔ`, as `BA/GreenCore.lean:1902`). Those lemmas are private in `GreenCore.lean`, so their proofs are repeated inside the one `example`.
- Statement shape of `BAIBPDet` (extract above): no `∃`; the premises are `BAFlow`, `0 ≤ t ≤ BAflowT0`, the window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}`, `δ ≤ κ/2`, `hΩ`, `hll`. No `g ≤ W^{-ε}`, no smallness of `‖M - m₀ I‖`, no `(Cλ)^{|a-b|}`.
