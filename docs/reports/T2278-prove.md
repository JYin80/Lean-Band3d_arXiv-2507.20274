Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 09:50:17 UTC 2026

### (i) Exponent table (d = 3 data: L = 3, W = 2, N = (WL)^d = 216, g = Λ = κ = 1, E = 0; scripts in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2278/`)

| quantity | value | constraint | slack |
|---|---|---|---|
| lattice exponent in `N`, `Smix`, `card Vtx` | `d` (RBM2D: 2) | `N = (WL)^d = W^d L^d`, `card Vtx = N`, `card Zd = L^d` | identity; instance 216 = 8·27 |
| `S_xy ≤ W^{-d}` (`svarF_le`, constant 1 not 1/5) | `S^(B)(g) ≤ 1` | `svar_le_inv_Wd g hL`, `svarF_eq_svar` is `rfl` | max `svarF` 0.01786 = 1/56 vs `W^{-d}` 0.125 (factor 7 = 1+2dg²) |
| `N⁻¹ ≤ W^{-d}` (`Snorm_le`) | `L^d ≥ 1` | `1 ≤ L` | factor `L^d` = 27 |
| `W^{-d} ≤ 4 maxLoopPM` (`inv_Wd_le_maxLoopPM`, merged, hyp `δ ≤ 1/2`) | 4 | `‖G_xx‖ ≥ 1-δ ≥ 1/2` | at G = i/(1-u)·I: 0.125 vs 4·0.12506 = 0.5003 (factor 4) |
| `inv_N_le_maxLoopPM` | `Im m/(2 N η) ≤ maxLoopPM` | Ward col, `Im G_αα ≥ Im m - δ ≥ Im m/2` (`δ ≤ Im m/2`), `card Zd = L^d`, fibre `W^d`: `W^{-2d}·W^d = W^{-d}` | see (ii) |
| `sum_Snorm_le` | `(1+3/Im m)·maxLoopPM` | `α²·mL + (1-α²)(Y/N)`, `Y = 3/(2η)` (`Im G ≤ 3/2` from `‖m‖=1`, `δ ≤ 1/2`), `Y/N ≤ 3 mL/Im m`; `α = a/u`, `2αβ+β² = 1-α²` | hΛ1 at instance 0.00794 vs 0.50025 |
| `mixC = √(2κ)/2` | `≤ 1`, `≤ Im mE E` | `4-E² ≥ κ(4-κ) ≥ 2κ` iff `κ ≤ 2` (from `\|E\| ≤ 2-κ`) | `κ(2-κ)`: 1 at κ=1, 0 at κ=2,E=0 (equality allowed); scan: 0 violations |
| `1+3/mixC ≥ 4` (hΛ2: `S' ≤ W^{-d} ≤ 4 mL`) | needs `mixC ≤ 1` | κ ≤ 2 | κ=1: 5.243 vs 4 |
| `mixK = Kstab3 d Λ κ (1+1/gapK κ)` | `≥ 1` (`one_le_Kstab3`, `gapK ≤ 1`: even `≥ 2`) | `0<κ≤2` | `Kstab3` L-free (merged); RBM2D `Kstab2 ∝ 1+log L` gone (`:631-635` only) |
| `mixDelta = min(1/2, 1/(2 mixK), mixC/2)` | `> 0` | `δ ≤ 1/2`, `mixK δ ≤ 1/2`, `δ ≤ mixC/2 ≤ Im m/2` | `mixK ≥ 1` so `> 0`; κ=1, K=1: 0.3536 |
| `36 Φ δ² ≤ 1`, Φ = 216 | δ ≤ 1/√7776 = 0.01134 | | δ = 1e-3: 7.776e-3 (factor 129) |
| `mixCdet = (2160 K² + 162)(1+3/mixC)` | `162 ≤ 2160K²+162`, `2160K² ≤` same | `norm_sq_green_offdiag_le` (162 = 2·81), `norm_sq_green_diag_sub_le` (2160), `Λ = (1+3/mixC)mL` | κ=1, K=1: 12173.4 |
| `stable_mix`: `t = a < 1` for `stable_svar_bulk` | `a = u-b ≤ u < 1` | `hb`, `hu1`; `0 ≤ a` from `ha` | instance a = 1/2: slack 1/2 |
| `stable_mix` constant | `Kstab3 d Λ κ (1+1/gapK)` | `‖V‖ gapK ≤ N B`, `‖(1-um²)‖ ≥ gapK` (`gapK_le_norm`, `mSigma E true = mE E`), `\|b m² V/N\| ≤ b B/gapK ≤ B/gapK` | numeric ratio ≤ 0.6874 (below) |
| hypotheses of `Kstab3` / `stable_svar_bulk` | `3 ≤ d`, `3 ≤ L`, `0<g≤Λ`, `0<κ`, `\|E\| ≤ 2-κ`, `0 ≤ t < 1` | | d=3: 0; L=3: 0 (allowed); g = Λ: 0 (allowed); `\|E\|`: 1 |
| quadratic LDE (instance, `H = 0`, `G` diagonal) | `(Σ_{k≠i} S_ik)² ≤ (N-1) Σ S_ik²` | `N-1 = 215 ≤ Φ = 216` | max LHS/(Φ RHS) = 0.5795 |
| `Φ = 1` in `mix_diag_det_inst` | `u²(N-1) ≤ 1`, u ≤ 0.0682 | tiny `u = δ/4` | u = 2.5e-4: 1.3e-5 |
| external hypotheses | none in any target | `Kstab3` uses the **proved** `prop5Short_holds` (`Propagator/Prop5Short.lean:400`, `theorem`) | n/a; consumer `WO` limit computed in (ii) |

d-token count of RBM2D `EntryDet.lean` at `c9a24cf`, lines 1-891 (command `python3 tok.py`; verbatim):
```
lines 1-891 with a lattice/size/log token (W*L)^2, W^2, L^2, W^-2, 1/5, log, Fin W x Fin W, Z2, BlockIndex: 56
  109, 234, 240, 242, 244, 246, 249, 251, 255, 269, 357, 371-373, 376, 378, 381, 386-390, 395-396, 398, 400, 403-406, 409, 411, 413-414, 478, 480, 485, 495, 501, 533, 541, 563, 631, 633, 635, 709, 728, 730, 740, 742, 753, 755, 785, 851, 865, 878
  by target: stable_mix N 1; svar_le/Snorm_le/Snorm_zero_left 9; inv_N_le_maxLoopPM 24; card/sum_Snorm_le 5; mixK_one_le log 3; mix_det hS_W,hLam2 2; BlockIndex (mix_det) 6
other lines with ^ 2 (scalar squares: ‖.‖^2, E^2, m^2, t^2, Φ^2, δ^2, α^2, β^2, N^2 as a number, (mixK..)^2): 96
Z2 lines count: 10  BlockIndex lines: 17  log lines: [631, 633, 635]
```
Classification of the "other `^ 2`" bases (read off by script `classify2.py`): `‖G_kl‖`, `m`, `E`, `Φ`, `α`, `β`, `N` (square of the number `N`, stays 2), `κ`, `δ`, `t`, `u`, `(mixK κ L)` (square of a constant); no lattice exponent. Differences from the ticket's list: it cites `:111`, `:249-253`, `:401`, `:479`, `:502`; the script's lines are `109`, `240-255`, `386-406`, `478-480`, `501` (an offset of a few lines; the same places). In `inv_N_le_maxLoopPM` the outer `^ 2` of `((W⁻¹)^d)^2` stays 2 (`norm_loopPM_eq` states `(W⁻¹^d)^2`).

### (ii) One concrete nondegenerate instance (d = 3, L = 3, W = 2, N = Φ = 216, g = Λ = κ = 1, E = 0)
Commands: `cd <scratch>/T2278; python3 stab.py` and `python3 inst.py` (each rebuilds `S = W^{-3} S^(B)(g)` on `Z_6^3` by the definitions `sbKernelR`, `svarF`, `Smix`; `K = ‖(1-ξS')⁻¹‖_{∞→∞}`, which is the least constant of `Stable`). Output (edited as noted below the block):
```
cases 672 max ratio K_mix/(K_band(1+1/gapK))=0.6874 max K_band=26.790
worst case (L,W,g,E,a,b,K_mix,K_band,gapK): (3, 2, 0.05, 1, 0, 0.5, 1.3748925431587748, 1.0, 1)
instance N=216  m=1j  K_mix=1.5103  K_band(a)=1.5006  gapK(2)=1.0000  (1+1/gapK)=2.0000
N=(W L)^d = 216  Phi=|Vtx|= 216  L^d= 27  W^d= 8
u=3/4, m:=G_ii=4i (free m, delta=0): G_ii=0.0000+4.0000j delta=|G-m|=0.0000 <= Im m/2=2.0000: True; maxLoopPM=2.00000; LHS Im m/(2 N eta)=0.037037; LHS<=maxLoopPM: True
u=1/4, m=mE 0=i, delta=1/3: G_ii=0.0000+1.3333j delta=|G-m|=0.3333 <= Im m/2=0.5000: True; maxLoopPM=0.22222; LHS Im m/(2 N eta)=0.003086; LHS<=maxLoopPM: True
delta=0.001: u=2.500e-04  u/(1-u)=2.501e-04 <= delta: True;  36*Phi*delta^2=7.776e-03 <= 1: True;  delta<=1/2: True
delta=1e-06: u=2.500e-07  u/(1-u)=2.500e-07 <= delta: True;  36*Phi*delta^2=7.776e-09 <= 1: True;  delta<=1/2: True
mix_det_inst: LDEQuad(Smix,t=1,Phi=216): max LHS/(Phi*RHS) = 0.5795  (<=1 needed)
mix_diag_det_inst: LDEQuad(Snorm,t=u,Phi=1): max LHS/(Phi*RHS) = 7.824e-06 (<=1 needed; Phi=1 works only because u is tiny: u^2*(N-1)=1.344e-05)
Cauchy-Schwarz: (sum_{k!=i} S_ik)^2 <= (N-1) sum S_ik^2, N-1=215 <= Phi=216: True
maxLoopPM at G=i/(1-u) I: 0.12506252344531496  closed form W^-d/(1-u)^2 = 0.12506252344531493
hLambda1: max_ij sum S'_ik|G_kl|^2 S'_lj = 0.00794 <= (1+3/Im m) maxLoopPM = 0.50025: True
hLambda2: max S'_ij = 0.01124 <= W^-d = 0.12500 <= 4 maxLoopPM = 0.50025: True
svarF<=W^-d: True  (max svarF=0.01786, W^-d=0.12500; g=1: 1/7 * 1/8)  Snorm(a=0,b)=1/N: True
mixC<=1, mixC<=Im mE E, 1+3/mixC>=4 on kappa in (0,2], |E|<=2-kappa: violations 0  min slack Im m - mixC = 0.00e+00
kappa=1: mixC=0.7071  mixCdet(K=1)=12173.412; 162*(1+3/c)=849.308; 2160K^2(1+3/c)=11324.104
mixDelta<=min(1/2,1/(2K),c/2)=0.3536 at K=1,kappa=1
 L=3 (N=27): K_band(a=.999,E=1.9,g=1)=3.138   (L=4: 3.536; L=5: 3.722; L=6, N=216: 3.829)
n=1: W^(-d/2+fd)=3.789e-01 <= lam=0.5 <= 1/fd=10.0: True;  0<lam<=Lambda:=1/fd: True   (n=10, 1000, 10^6: True; fd = 𝔡 = 1/10)
```
(Edited from the script's printout: the `np.float64(...)` wrappers are removed, the four `L=` rows and the four `n=` rows are merged into one line each; all numbers are the script's.)
Reading:
- `stable_mix_inst`, (a, b) = (1/2, 1/4), u = 3/4 < 1: `K_mix = 1.5103 ≤ K_band(a)(1+1/gapK) = 3.0012`. The 672-case scan (L,W) ∈ {(3,1),(4,1),(5,1),(3,2)}, g ∈ {0.05,0.5,1,3}, E ∈ {0,1,1.9}, a, b grids, `0 < a+b < 1`, reproduces the dispatcher's numbers (max ratio 0.6874 ≤ 1, max `K_band` 26.79). Every hypothesis holds: `3 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `0 < κ`, `|E| = 0 ≤ 1`, `a, b ≥ 0`, `0 < u < 1`.
- `inv_N_le_maxLoopPM_inst` at `u = 3/4`, `M = 0`: `G = 4i·I`, `maxLoopPM = 2`. **Caution for the prover:** `m` must be the free variable `m := 4i` (`δ = 0`), because with `m = mE 0 = i` the good event fails (`‖G-m‖ = 3 > Im m/2 = 1/2`). The theorem's `m` is free (no `‖m‖ = 1`), so this is a legitimate instance (LHS 0.037 ≤ 2). The alternative `u = 1/4`, `m = mE 0`, `δ = 1/3` also holds (0.0031 ≤ 0.2222).
- `mix_det_inst`: `M = 0`, `G = (-z)⁻¹ I = i/(1-u) I`, `H = blockMat 0 = 0`; `LDERow`/`LDECol` have LHS 0; `LDEQuad` with `t = 1`, `Φ = 216` is Cauchy–Schwarz (`215 ≤ 216`); `hLdiag` is `0 ≤ Φ S_ii`; `δI = min(1/1000, mixDelta 3 1 1)`, `a = b = δI/8`, `u = δI/4`: `u/(1-u) ≤ δI` (checked at δ = 1e-3 and 1e-6; monotone in δ), `36·216·δI² ≤ 7.8e-3`, `mixK δI ≤ 1/2` from `δI ≤ 1/(2 mixK)`. `Kstab3` is `Classical.choose`-valued, so `mixDelta 3 1 1` has no numeric value; the data are valid for every `δI ∈ (0, min(1/1000, mixDelta 3 1 1)]` and `0 < δI` by `mixDelta_pos` (needs `0 < κ ≤ 2`, `1 ≤ mixK`); this is a small positive witness, not an astronomically large one. Conclusion check: `G_pq = 0` for `p ≠ q`, `|G_pp - m|² = (u/(1-u))² ≤ 1e-7 ≤ mixCdet·Φ²·maxLoopPM` (RHS ≥ 162·4·216²/8).
- `mix_diag_det_inst` with `Φ = 1`: `LDEQuad(Snorm, t = u)` ratio 7.8e-6 ≤ 1, true because `u²(N-1) ≤ 1` (u ≤ 0.0682); `Φ = 1` would fail at `u` of order 1.
- `sum_Snorm_le_inst` (s = 0, M = 0): hΛ1 row above is the same sum at the instance (0.00794 ≤ 0.50025).
- External hypothesis / consumer limit (§29 (6), TEAM §8 lesson 14): no target has an external hypothesis. The consumer's `WO 𝔡` (`Defs/Sizes.lean:164`: `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` eventually) gives `0 < lam n` (lower bound `> 0`) and `lam n ≤ 𝔡⁻¹ = Λ`: with d = 3, 𝔡 = 1/10, `W_n = n+1`, `lam n = 1/2`: `W_n^{-1.4} → 0` (3.8e-1 at n = 1, 4.0e-9 at n = 10^6) and `1/2 ≤ 10`; `Λ = 𝔡⁻¹` makes `Kstab3 d 𝔡⁻¹ κ` `n`-free.
- §29 items: (1) `u = a+b ∈ (0,1)` only via `hu`, `hu1`; `a < 1` from `hb`; (3) no L–W relation, `W^d ≤ (WL)^d`; (4) no `∀ᶠ`; (5) per matrix; (6) `3 ≤ d` only through `stable_svar_bulk`; (7) constants depend on `(d, Λ, κ)` only.
- Registry plan: no `Prop`-valued definition in the file (`Snorm`, `mixC`, `mixK`, `mixDelta`, `mixCdet` are `ℝ`-valued); `grep -n "EntryDet\|mix_det\|stable_mix" RBM3D/Test/Axioms.lean` gave 0 hits in the main worktree.

### Verdict per target (math only)
- 1 `stable_mix`: PASS (`‖V‖/N ≤ B/gapK` by the column-sum identity `Σ_j r_j = (1-um²)V`; band part `stable_svar_bulk` at `t = a`).
- 2 `Snorm` family, `svarF_le`, `Snorm_le`, `Snorm_zero_left`: PASS.
- 3 `mix_offdiag_det`, `mix_diag_det`: PASS (`hmz : m(tm+z) = -1` is `mE_mul_add_zt`, `t = u ≤ 1`, `hSrow` equality from `sum_Smix_row`).
- 4 `ward_col`, `green_transpose`, `ward_row`, `im_diag_le`: PASS (`Im G = η G*G` for normal `G`).
- 5 `inv_N_le_maxLoopPM`: PASS (instance caveat on `m` above).
- 6 `sum_Snorm_le`: PASS.
- 7 constants and `*_smul` lemmas: PASS.
- 8 `mix_det`: PASS (`hΛ1` via `sum_Snorm_le` with `3/Im m ≤ 3/mixC`; `hΛ2` via `W^{-d} ≤ 4 mL`; LDE inputs rescale by `u ≤ 1`, `u² ≤ 1`).
- Overall: PASS. No hypothesis set is empty, no exponent fails to close.

## (b) Script output, stage 1b (written Tue Oct  6 10:08:56 UTC 2026)

Branch `t/T2278`, commit `8e5f0b9`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2278`; scratch files in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2278/`.

### Build
```
$ lake build RBM3D.Universality.GUEPhase.EntryDet 2>&1 | tail -6   (the two warnings in the tail are in RBM3D/Green/IBPPoly.lean:1082, a merged file;
  the fresh compile of EntryDet.lean (14 s, status ✔) printed no warning; a later grep -c EntryDet of the full output: 0)

Note: This linter can be disabled with `set_option linter.style.longLine false`
warning: RBM3D/Green/IBPPoly.lean:1082:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3359 jobs).
exit=0
$ lake build   (whole worktree library; RBM3D.lean does not import EntryDet yet, the hub adds it at merge)
exit 0, "Build completed successfully (4084 jobs)."
$ wc -l EntryDet.lean ; grep -c "sorry\|admit\|native_decide" EntryDet.lean ; grep -c "^axiom" EntryDet.lean
1459, 0, 0
```
### Axioms
```
#print axioms of all 58 public declarations of the file (theorems and defs; script `axioms.lean`, exit 0):
  58 declarations: [propext, Classical.choice, Quot.sound]
names (RBM.Univ.): stable_mix, Snorm, Snorm_nonneg, sum_Snorm_row, sum_Snorm_col, Snorm_symm, svarF_le, Snorm_le, Snorm_zero_right, Snorm_zero_left,
    mix_offdiag_det, mix_diag_det, ward_col, inv_N_le_maxLoopPM, green_transpose, ward_row, im_diag_le, sum_Snorm_le, mixC, mixK, mixDelta, mixCdet,
    mixC_pos, mixK_one_le, mixDelta_pos, mixCdet_nonneg, ldeRowRHS_smul, ldeColRHS_smul, ldeQuadRHS_smul, ldeQuadLHS_smul, mix_det,
    EntryDetCheck.stable_mix_inst, EntryDetCheck.inv_N_le_maxLoopPM_inst, EntryDetCheck.ward_col_inst, EntryDetCheck.ward_row_inst,
    EntryDetCheck.green_transpose_inst, EntryDetCheck.sum_Snorm_le_inst, EntryDetCheck.svarF_le_inst, EntryDetCheck.Snorm_le_inst,
    EntryDetCheck.Snorm_nonneg_inst, EntryDetCheck.sum_Snorm_row_inst, EntryDetCheck.sum_Snorm_col_inst, EntryDetCheck.Snorm_symm_inst,
    EntryDetCheck.Snorm_zero_right_inst, EntryDetCheck.Snorm_zero_left_inst, EntryDetCheck.im_diag_le_inst, EntryDetCheck.mixC_pos_inst,
    EntryDetCheck.mixK_one_le_inst, EntryDetCheck.mixDelta_pos_inst, EntryDetCheck.mixCdet_nonneg_inst, EntryDetCheck.ldeRowRHS_smul_inst,
    EntryDetCheck.ldeColRHS_smul_inst, EntryDetCheck.ldeQuadRHS_smul_inst, EntryDetCheck.ldeQuadLHS_smul_inst, EntryDetCheck.mix_offdiag_det_inst,
    EntryDetCheck.mix_diag_det_inst, EntryDetCheck.mix_det_inst, EntryDetCheck.mix_det_inst_vars
```
### Target statements, extracted from the file by script (`extract.py stmt <names>`; L = line in EntryDet.lean)
```
L91 theorem stable_mix (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 < a + b) (hu1 : a + b < 1) : Stable (fun x y : Idx d L W => Smix d L W g a b x y / (a + b)) (((a + b : ℝ) : ℂ) * mE E ^ 2) (Kstab3 d Λ κ *
    (1 + 1 / RBM.Loop.gapK κ))
L229 theorem svarF_le (g : ℝ) (hL : 3 ≤ L) (x y : Idx d L W) : svarF d L W g x y ≤ ((W : ℝ) ^ d)⁻¹
L236 theorem Snorm_le (hL : 3 ≤ L) {g a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (x y : Idx d L W) : Snorm d L W g a b x y ≤ ((W : ℝ) ^ d)⁻¹
L262 theorem Snorm_zero_left (g : ℝ) {b : ℝ} (hb : 0 < b) (x y : Idx d L W) : Snorm d L W g 0 b x y = 1 / (((W * L) ^ d : ℕ) : ℝ)
L272 theorem mix_offdiag_det (hL : 3 ≤ L) {g a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) {H G : Matrix (Idx d L W) (Idx d L W) ℂ} {z m : ℂ} {δ Φ Λ
    : ℝ} (hGM : G * (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) = 1) (hMG : (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * G = 1) (hm : ‖m‖ =
    1) (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G (Snorm d L W g a b) Φ) (hLcol : LDECol H G
    (Snorm d L W g a b) Φ) (hΛ1 : ∀ i j, ∑ k, ∑ l, Snorm d L W g a b i k * ‖G k l‖ ^ 2 * Snorm d L W g a b l j ≤ Λ) (hΛ2 : ∀ i j, Snorm d L W g a b i
    j ≤ Λ) {i j : Idx d L W} (hij : i ≠ j) : ‖G i j‖ ^ 2 ≤ 162 * Φ ^ 2 * Λ
L289 theorem mix_diag_det (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 < a + b) (hu1 : a + b < 1) {H G : Matrix (Idx d L W) (Idx d L W) ℂ} {δ Φ Λ' : ℝ} (hGM : G * (H - zt E (a + b) • (1 : Matrix (Idx d L W)
    (Idx d L W) ℂ)) = 1) (hMG : (H - zt E (a + b) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * G = 1) (hΩ : GoodEvent G (mE E) δ) (hδ : δ ≤ 1 / 2) (hΦ1
    : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G (Snorm d L W g a b) Φ) (hLcol : LDECol H G (Snorm d L W g a b) Φ) (hLquad : LDEQuad H G
    (Snorm d L W g a b) (a + b) Φ) (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * Snorm d L W g a b i i) (hΛ1 : ∀ i j, ∑ k, ∑ l, Snorm d L W g a b i k * ‖G k l‖ ^ 2
    * Snorm d L W g a b l j ≤ Λ') (hΛ2 : ∀ i j, Snorm d L W g a b i j ≤ Λ') (hKδ : (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) * δ ≤ 1 / 2) (i : Idx d
    L W) : ‖G i i - mE E‖ ^ 2 ≤ 2160 * (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) ^ 2 * Φ ^ 2 * Λ'
L334 theorem ward_col {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : ν) : ∑ x, ‖green H z x
    i‖ ^ 2 = (green H z i i).im / z.im
L443 theorem ward_row {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (k : ν) : ∑ l, ‖green H z k l‖ ^ 2 = (green H z k k).im / z.im
L464 theorem im_diag_le {G : Matrix ν ν ℂ} {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (x : ν) : (G x x).im ≤ 3 / 2
L354 theorem inv_N_le_maxLoopPM {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (hz : 0 < (zt E u).im) {m : ℂ} {δ : ℝ} (hΩ :
    GoodEvent (greenBlk d L W E u M true) m δ) (hδ : δ ≤ m.im / 2) : m.im / (2 * ((((W * L) ^ d : ℕ) : ℝ) * (zt E u).im)) ≤ maxLoopPM d L W E u M
L500 theorem sum_Snorm_le (hL : 3 ≤ L) {g E s : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (hz : 0 < (zt E s).im) {m : ℂ} (hm : ‖m‖ =
    1) (him : 0 < m.im) {δ : ℝ} (hΩ : GoodEvent (greenBlk d L W E s M true) m δ) (hδ12 : δ ≤ 1 / 2) (hδm : δ ≤ m.im / 2) {a b : ℝ} (ha : 0 ≤ a) (hb :
    0 ≤ b) (hu : 0 < a + b) (p q : Vtx d L W) : ∑ k, ∑ l, Snorm d L W g a b ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm k) * ‖greenBlk d L W
    E s M true k l‖ ^ 2 * Snorm d L W g a b ((splitEquiv d L W).symm l) ((splitEquiv d L W).symm q) ≤ (1 + 3 / m.im) * maxLoopPM d L W E s M
L631 theorem mixC_pos {κ : ℝ} (hκ : 0 < κ) : 0 < mixC κ
L638 theorem mixK_one_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (d : ℕ) (Λ : ℝ) : 1 ≤ mixK d Λ κ
L647 theorem mixDelta_pos {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) (d : ℕ) (Λ : ℝ) : 0 < mixDelta d Λ κ
L653 theorem mixCdet_nonneg {κ : ℝ} (hκ : 0 < κ) (d : ℕ) (Λ : ℝ) : 0 ≤ mixCdet d Λ κ
L719 theorem mix_det (hd : 3 ≤ d) (hL : 3 ≤ L) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ
    : 0 < κ) (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b) (hu1 : a + b < 1) {δ Φ : ℝ} (hΩ : GoodEvent (greenBlk d L W E (a + b) M
    true) (mE E) δ) (hδ : δ ≤ mixDelta d Λ κ) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow (blockMat d L W M) (greenBlk d L W E (a + b) M
    true) (fun x y => Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) Φ) (hLcol : LDECol (blockMat d L W M) (greenBlk d L W
    E (a + b) M true) (fun x y => Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) Φ) (hLquad : LDEQuad (blockMat d L W M)
    (greenBlk d L W E (a + b) M true) (fun x y => Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) 1 Φ) (hLdiag : ∀ i,
    ‖blockMat d L W M i i‖ ^ 2 ≤ Φ * Smix d L W g a b ((splitEquiv d L W).symm i) ((splitEquiv d L W).symm i)) (p q : Vtx d L W) : ‖(greenBlk d L W E
    (a + b) M true - mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p q‖ ^ 2 ≤ mixCdet d Λ κ * Φ ^ 2 * maxLoopPM d L W E (a + b) M
L202 def Snorm (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) (x y : Idx d L W) : ℝ
L619 def mixC (κ : ℝ) : ℝ
L623 def mixK (d : ℕ) (Λ κ : ℝ) : ℝ
L626 def mixDelta (d : ℕ) (Λ κ : ℝ) : ℝ
L629 def mixCdet (d : ℕ) (Λ κ : ℝ) : ℝ
```
### Pin examples (check file §2 copied verbatim into a scratch file that imports `RBM3D.Universality.GUEPhase.EntryDet`)
```
$ lake env lean PinExamples.lean ; echo exit=$?
exit=0
21 `example`s. 16 pins, each the library theorem with exactly the pinned statement:
T2278_stable_mix T2278_svarF_le T2278_Snorm_le T2278_Snorm_zero_left T2278_mix_offdiag_det T2278_mix_diag_det T2278_ward_col
T2278_ward_row T2278_im_diag_le T2278_inv_N_le_maxLoopPM T2278_sum_Snorm_le T2278_mixC_pos T2278_mixK_one_le T2278_mixDelta_pos
T2278_mixCdet_nonneg T2278_mix_det ; and 5 `rfl`: SnormV=Snorm, mixCV=mixC, mixKV=mixK, mixDeltaV=mixDelta, mixCdetV=mixCdet.
(ward_col, ward_row, im_diag_le: `@RBM.Univ.<name>.{0}`.)
```
### Compiled nonempty instances (in the file, namespace `RBM.Univ.EntryDetCheck`; d = 3, L = 3, W = 2, N = |Vtx 3 3 2| = 216; headline ones)
```
L969 theorem stable_mix_inst : Stable (fun x y : Idx 3 3 2 => Smix 3 3 2 1 (1 / 2) (1 / 4) x y / (1 / 2 + 1 / 4)) (((1 / 2 + 1 / 4 : ℝ) : ℂ) * mE 0 ^ 2)
    (Kstab3 3 1 1 * (1 + 1 / RBM.Loop.gapK 1))
L980 theorem inv_N_le_maxLoopPM_inst : (4 * Complex.I : ℂ).im / (2 * ((((2 * 3) ^ 3 : ℕ) : ℝ) * (zt 0 (3 / 4)).im)) ≤ maxLoopPM 3 3 2 0 (3 / 4) (0 : Matrix
    (Idx 3 3 2) (Idx 3 3 2) ℂ)
L992 theorem ward_col_inst (i : Idx 3 3 2) : ∑ x, ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I x i‖ ^ 2 = (green (0 : Matrix (Idx 3 3 2) (Idx 3
    3 2) ℂ) Complex.I i i).im / Complex.I.im
L997 theorem ward_row_inst (i : Idx 3 3 2) : ∑ x, ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I i x‖ ^ 2 = (green (0 : Matrix (Idx 3 3 2) (Idx 3
    3 2) ℂ) Complex.I i i).im / Complex.I.im
L1010 theorem sum_Snorm_le_inst (p q : Vtx 3 3 2) : ∑ k, ∑ l, Snorm 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm p) ((splitEquiv 3 3 2).symm k) *
    ‖greenBlk 3 3 2 0 0 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true k l‖ ^ 2 * Snorm 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm l) ((splitEquiv
    3 3 2).symm q) ≤ (1 + 3 / Complex.I.im) * maxLoopPM 3 3 2 0 0 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
L1301 theorem mix_offdiag_det_inst {i j : Idx 3 3 2} (hij : i ≠ j) : ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t)) i j‖ ^ 2 ≤ 162
    * (1 : ℝ) ^ 2 * 4
L1341 theorem mix_diag_det_inst (i : Idx 3 3 2) : ‖green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (check_t + check_t)) i i - mE 0‖ ^ 2 ≤ 2160 * (Kstab3
    3 1 1 * (1 + 1 / RBM.Loop.gapK 1)) ^ 2 * (1 : ℝ) ^ 2 * 4
L1392 theorem mix_det_inst (p q : Vtx 3 3 2) : ‖(greenBlk 3 3 2 0 (check_t + check_t) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true - mE 0 • (1 : Matrix (Vtx
    3 3 2) (Vtx 3 3 2) ℂ)) p q‖ ^ 2 ≤ mixCdet 3 1 1 * (216 : ℝ) ^ 2 * maxLoopPM 3 3 2 0 (check_t + check_t) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
L1430 theorem mix_det_inst_vars {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian) (hΩ : GoodEvent (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true) (mE 0)
    (mixDelta 3 1 1 / 3)) (hLrow : LDERow (blockMat 3 3 2 M) (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true) (fun x y => Smix 3 3 2 1 (1 / 2) (1 / 4)
    ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y)) 1) (hLcol : LDECol (blockMat 3 3 2 M) (greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true) (fun x y
    => Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y)) 1) (hLquad : LDEQuad (blockMat 3 3 2 M) (greenBlk 3 3 2 0
    (1 / 2 + 1 / 4) M true) (fun x y => Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y)) 1 1) (hLdiag : ∀ i,
    ‖blockMat 3 3 2 M i i‖ ^ 2 ≤ 1 * Smix 3 3 2 1 (1 / 2) (1 / 4) ((splitEquiv 3 3 2).symm i) ((splitEquiv 3 3 2).symm i)) (p q : Vtx 3 3 2) :
    ‖(greenBlk 3 3 2 0 (1 / 2 + 1 / 4) M true - mE 0 • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) p q‖ ^ 2 ≤ mixCdet 3 1 1 * (1 : ℝ) ^ 2 * maxLoopPM 3 3
    2 0 (1 / 2 + 1 / 4) M
```
One more instance per remaining public theorem is in the file: `green_transpose_inst`, `svarF_le_inst`, `Snorm_le_inst`, `Snorm_nonneg_inst`,
`sum_Snorm_row_inst`, `sum_Snorm_col_inst`, `Snorm_symm_inst`, `Snorm_zero_right_inst`, `Snorm_zero_left_inst`, `im_diag_le_inst`, `mixC_pos_inst`,
`mixK_one_le_inst`, `mixDelta_pos_inst`, `mixCdet_nonneg_inst`, `ldeRowRHS_smul_inst`, `ldeColRHS_smul_inst`, `ldeQuadRHS_smul_inst`, `ldeQuadLHS_smul_inst`.
In `mix_offdiag_det_inst`, `mix_diag_det_inst`, `mix_det_inst` no deterministic hypothesis is left open: `H = 0`, `G = (i/(1-u))·1`, `u = check_t + check_t
= check_dI/4`, `check_dI := min (1/1000) (mixDelta 3 1 1)` (positive by `mixDelta_pos`), `Φ = 216` in `mix_det_inst` (`check_card_vtx : card (Vtx 3 3 2) = 216`),
the quadratic LDE by Cauchy-Schwarz (`check_ldeQuad_scalar`). `mix_det_inst_vars` keeps the good event and the four LDE inputs as hypotheses (other gates' pins).
### Name clash and registry
```
$ bash clash.sh   (grep -rnw --include='*.lean' <name> RBM3D/ in the main worktree, for each of the 58 public names; private helpers are prefixed EntryDet_ or check_)
names checked: 58; names with a hit in main RBM3D/: 0
main HEAD: 95d8b2a; EntryDet.lean in main RBM3D/: ls: RBM3D/Universality/GUEPhase/EntryDet.lean: No such file or directory
$ grep -n "EntryDet\|mix_det\|stable_mix" RBM3D/Test/Axioms.lean | wc -l    -> 0   (no Prop-valued definition added; Axioms.lean not touched)
$ printf 'import RBM3D\nimport RBM3D.Universality.GUEPhase.EntryDet\n\n#assert_rbm_axioms\n' > precheck.lean ; lake env lean precheck.lean ; echo exit=$?
axiom audit: 8086 theorems, 2639 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
...  exit=0   (no error line; "0 axioms in `RBM`")
```
### Git
```
$ git diff --stat main...t/T2278 ; git log -1 --format='%h %an <%ae>' ; git status --short | wc -l
 RBM3D/Universality/GUEPhase/EntryDet.lean | 1459 +++++++++++++++++++++++++++++
 1 file changed, 1459 insertions(+)
8e5f0b9 Jun Yin <321276894+JYin80@users.noreply.github.com>
       0
```
### Port citation and statement comparison with the source
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/EntryDet.lean
 RBM2D/Universality/GUEPhase/EntryDet.lean | 653 +++---------------------------
 1 file changed, 48 insertions(+), 605 deletions(-)
Source: RBM2D/Universality/GUEPhase/EntryDet.lean at c9a24cf, lines 1-891 ported (instances 893-1337 rewritten at d = 3). RBM1D not read.
$ python3 cmp2.py   (header text of each ported declaration of RBM2D :1-891, import map applied, whitespace-normalised, diffed with the RBM3D header)
declarations compared: 34 ; identical after the import map: 16 ; differing: 18
stable_mix: ''->'(hd : 3 ≤ d)'; '{κ'->'{g Λ κ'; ''->'(hg : 0 < g) (hgΛ : g ≤ Λ)'
Snorm_nonneg: '{a'->'{g a'
sum_Snorm_row: '{a'->'{g a'
sum_Snorm_col: '{a'->'{g a'
Snorm_symm: '(a'->'(g a'
svar_le => svarF_le: ''->'(g : ℝ) (hL : 3 ≤ L)'; 'svar'->'svarF d'; ''->'g'; '(5 : ℝ)⁻¹ *'->''
Snorm_le: '{a'->'{g a'
Snorm_zero_right: '{a'->'{g a'; ''->'d'; ''->'g'; 'svar'->'svarF d'; ''->'g'
Snorm_zero_left: ''->'(g : ℝ)'; ''->'d'; ''->'g'
mix_offdiag_det: '{a'->'{g a'
mix_diag_det: ''->'(hd : 3 ≤ d)'; '{κ'->'{g Λ κ'; ''->'(hg : 0 < g) (hgΛ : g ≤ Λ)'; 'Λ'->"Λ'"; 'Λ)'->"Λ')"; 'Λ)'->"Λ')"; 'Λ'->"Λ'"
sum_Snorm_le: '{E'->'{g E'
mixK_one_le: '(L'->'(d'; ''->'(Λ : ℝ)'
mixDelta_pos: '(L'->'(d'; ''->'(Λ : ℝ)'
mixCdet_nonneg: '(L'->'(d'; ''->'(Λ : ℝ)'
mixC_le_spectralM_im => EntryDet_mixC_le_mE_im: 'mixC_le_mE_im'->'EntryDet_mixC_le_mE_im'
mix_det: ''->'(hd : 3 ≤ d)'; '{κ'->'{g Λ κ'; ''->'(hg : 0 < g) (hgΛ : g ≤ Λ)'
card_blockIndex_real => EntryDet_card_vtx_real: '(L'->'(d L'
source declarations in lines 1-891 not compared (not ported): ["gapK_le_norm'", "norm_one_sub_sq'"]
RBM3D declarations before §8 not compared (new private helpers): ['EntryDet_gapK_le_norm', 'EntryDet_greenBlk_true_eq', 'EntryDet_stable_relabel', 'EntryDet_svarF_symm']
```
### Narrative (every point checked against the file and the output above)
- `EntryDet.lean` is new (1459 lines, commit 8e5f0b9); `git diff --stat main...t/T2278` lists only it. `RBM3D/Test/Axioms.lean` is untouched: `Snorm`, `mixC`, `mixK`, `mixDelta`, `mixCdet` are `ℝ`-valued, no new `Prop` definition.
- Section (a) was not edited; I found nothing in it that changes a verdict, so there is no (a′). The compiled instance data are those of (a) (`δI = min (1/1000) (mixDelta 3 1 1)`, `a = b = δI/8`, `Φ = 216`).
- Proofs are the RBM2D bodies at `c9a24cf` through the import map, with these changes beyond renaming: `stable_mix` takes the gap from the merged `gapK_le_norm` (wrapper `EntryDet_gapK_le_norm`, `mSigma E true = mE E`) and the band part from `stable_svar_bulk hd hL hg hgΛ`; `svarF_le` is `svar_le_inv_Wd` through `svarF_eq_svar` (constant 1, needs `hL`); `inv_N_le_maxLoopPM` sums over `Zd d L` (`card_Zd`) with fibre `Fin (W ^ d)`; `sum_Snorm_le` uses the private bridge `EntryDet_svarF_symm` and the merged `sum_sum_svar_le_maxLoopPM`, `sum_svar_row`, `sum_svar_col`; `mixK_one_le` is `one_le_Kstab3` with `1 ≤ 1 + 1/gapK κ` (no `log`); `mix_det` takes `hΛ2` from `inv_Wd_le_maxLoopPM`.
- Private helpers: the three copies named in the ticket (`EntryDet_stable_relabel`, `EntryDet_greenBlk_true_eq`, `EntryDet_gapK_pos`), the wrapper `EntryDet_gapK_le_norm`, `EntryDet_card_vtx_real` (RBM2D `card_blockIndex_real`), `EntryDet_svarF_symm`, `EntryDet_mixC_le_mE_im` (RBM2D `mixC_le_spectralM_im`).
- Differences from the ticket text: (1) `im_diag_le` keeps `[Fintype ν]` because the check file's pin has it; `linter.unusedFintypeInType` is switched off for that one declaration (RBM2D used `omit [Fintype ν]`). (2) There is one small instance per public theorem beyond the ticket's list. (3) The file is 1459 lines, above the ticket's "hi" estimate 1350 and below the 1500 split line.
- Binders where the check file has no pin: `Snorm_nonneg`, `sum_Snorm_row`, `sum_Snorm_col` take `{g a b}`, `Snorm_zero_right` takes `{g a}`; `Snorm_symm (g a b)` is explicit as RBM2D `(a b)`. `d L W` are implicit in the lattice theorems (as `L W` in RBM2D); the pins are matched by `fun d L W _ _ …` lambdas.
- `Kstab3` is `Classical.choose`-valued, so `mixDelta 3 1 1` has no numeric value; the instances use the symbolic `check_dI` (`mixDelta_pos`), not RBM2D's explicit `10⁻³¹`.

## (c) Verified Mathlib names (`mathlib_names.lean`: `46 names checked, 0 missing`; names verified absent: none checked)
Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv, Matrix.isHermitian_zero, Matrix.one_apply_ne,
Matrix.IsHermitian.submatrix, Equiv.sum_comp, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fintype.card_congr, Finset.sum_mul_sq_le_sq_mul_sq,
Finset.card_le_univ, Finset.sum_ite_eq, Finset.le_sup', Nat.pow_le_pow_left, Nat.le_mul_of_pos_right, one_div_le_one_div_of_le, inv_mul_le_iff₀,
div_le_div_of_nonneg_right, div_le_div_of_nonneg_left, pow_le_pow_left₀, Real.sqrt_le_sqrt, Real.sqrt_sq, Real.sqrt_pos, Complex.abs_im_le_norm,
Complex.im_le_norm, Complex.norm_real, Complex.normSq_eq_norm_sq, RCLike.star_def, Complex.re_sum, norm_sum_le, le_div_iff₀, div_le_iff₀, neg_abs_le,
le_abs_self, abs_of_nonneg, abs_of_pos. Merged names used (also in the list): RBM.Loop.gapK_le_norm, RBM.Green.stable_svar_bulk, IBP_sum_svarF_row,
inv_Wd_le_maxLoopPM, sum_sum_svar_le_maxLoopPM, RBM.card_Zd, RBM.Gauss.card_Idx, svarF_eq_svar, RBM.Green.im_green_diag.

## (d) Open issues and paper-delta candidates
- No open issue blocks a target: all 16 pins are proved with exactly their statements and every public theorem has a compiled instance.
- T2278a (bookkeeping, not a paper delta): `mixK d Λ κ = Kstab3 d Λ κ (1 + 1 / gapK κ)` is `L`-free; RBM2D `mixK κ L` carries `Kstab2 κ L` with `1 + log L`.
- T2278b (candidate): `svarF_le` states `S ≤ W^{-d}` from `S^(B)(g) ≤ 1` (RBM2D `1/5`); `hΛ2` of `mix_det` uses `W^{-d} ≤ 4 maxLoopPM` (merged `inv_Wd_le_maxLoopPM`).
- T2278c (Lean structure): band instance here (`0 < g ≤ Λ`, `m = mE E`); `stable_mix`, `mix_diag_det`, `mix_det` need `hg : 0 < g`, so `UNKind.ba` (`lamV := fun _ _ => 0`, `BA/UNPins.lean:86`) needs the BA form of BA-C3.
- T2278d (Lean structure, not a paper delta): `im_diag_le` keeps an unused `[Fintype ν]` to match the pin.
