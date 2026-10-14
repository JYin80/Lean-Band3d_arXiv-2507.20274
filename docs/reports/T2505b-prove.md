Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 09:22:20 UTC 2026

Row b (U3s4b), targets 6-9, branch `t/T2505b` at d3104f3b. Band sources (unedited): `Induction/QtNonzero.lean` (1,726 lines), `Induction/QtNonzeroEnd.lean` (1,584). Scripts (Python, no Lean) are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505b/`.

### (i) Exponent table (`nzGridEndN`, `QtNonzeroEnd:1025-1094`; `budgetNZN` hypotheses H1-H6, `QtNonzero:872-905`; fixed order C → e0 → ε₁ → D'' → D' → τ' → C_P → C_K)
| item | value | constraint | slack |
|---|---|---|---|
| Λg / κ' | `𝔡⁻¹` / `min κ (4/5)` | `0<gK n≤Λg` eventually (WO; BA: `BAflow_lam0_window`, `GreenSchur:72`); `κ'≤Im m` (band `nqGood1_mE_im_ge`, `|E|≤2-κ`; generic: `DecayGen_Spec κm`) | instance `0.80 ≤ 0.9682` |
| D1 constant `C5` | `Ci^k`, `Ci(d,k,Λg,κ',A)`, one value, fixed after `(k,κ,𝔡)`, before `(sz,z)`; no ε, 𝔠 | band `nzUgen_holds` (A=1); BA `baTwKerZero_holds` (`TwistKer:256`, `C(A)=2+A·C₀E_k`, ∀A>0) + `baEKSameRow_holds` (`EKPins:568`) | numerics below: `Ci`≈2.11 (Λg=1, A=1; g in (0.015625, 0.125, 0.5, 1)), 30.0 (Λg=10, A=1), 87.1 (Λg=10, A=3): `(87.1-2)/(30.0-2)=3.04≈A`, affine in A |
| `e0 = min ε₀ 1` | `ε₀'` | `>0` | — |
| `ε₁ = ε_q` | `e0/8` | H1 `ε₁<e0`; H2, H3 `2ε₁<e0` (log factors absorbed) | `7e0/8`, `3e0/4`; grid min H1 `7/800`, H2/H3 `3/400` at `ε₀=1/100` |
| `D''` | `2(k+2)/𝔠+1` (`𝔠D''/2=k+2+𝔠/2`) | H4 `ε_q+k-𝔠D''/2<e0` (`W≥N^𝔠`) | `e0-ε₁+2+𝔠/2 ≥ 2.01` over the grid; `71/24` at the instance |
| `D'`, `τ'`, `τ_K` | `D''+1`, `1`, `1` | `>0` | — |
| `D_Y=D_t`, `cA` | `k+2`, `2^k` | H5, H6 `k-D<e0` | `2+e0 ≥ 2.01` |
| `C_P^*` (`Cmax`) | from `yMomentsUnifNg` (existential, symbolic ≥0) | `≥0` | symbolic; checked at 0, 1, 50 |
| `C_K` (net mesh, `N^{C_K}≤K_n≤⌈N^{C_K}⌉`, `Δ=(v-s)/K`) | `D₁+2(Cmax+2k+2)+D''+16k+40` | `hC1..hC6` (`:1065-1074`: budget h1-h4 of `nqBudget_merged_inputs` (`NQBudget:834`; generic `nqBudget_merged_inputsg` `NQBudgetGen:734`), `hδ`, assembly) | min slack over grid: hC1 54, hC2 62.7, hC3 73.1, hC4 82.7, hC5 92.2, hC6 75.1 |
| window | `1-s ≤ lam²/L²` (STCaseII), grid `u_i ≥ s`; R1 `lam² ≤ A gK²` | D1 A-form `(1-u)L² ≤ A gK²` for `u_i ∈ [s,v]` | equality at `s=15/16` (band, A=1) |
| bootstrap `c` | n/a, because row b has no bootstrap (rows a: targets 2, 4) | | |

### (ii) One nondegenerate instance (`d=3`, `szB`: L=4, W_n=n+4, lam≡1, N_n=(4(n+4))³; E≡1/2, κ=1, 𝔠=1/6, 𝔡=1, τ=1/2, k=3, s=15/16, v=t=31/32, ε₀=1, D₁=1)
`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505b/expo.py` (exact rationals; exponent grid, then the instance):
```
grid k{2,3,4,6} tau{.1,.5,1,3} D1{.1,1,10} c{.01,1/6,.5,1} eps0{.01,.1,1,5} Cmax{0,1,50}: min slack over grid (all > 0 required)
  C_K slacks : hC1=54.0  hC2=62.7  hC3=73.1  hC4=82.7  hC5=92.2  hC6=75.1
  N-exponent gaps (a power of N left over):  H1=0.00875  H2=0.0075  H3=0.0075  H4=2.0137  H5=2.01  H6=2.01
instance exponents: e0=1 eps1=eps_q=1/8 D''=61 D'=62 tau'=1 tauR=1/2 tauK=1 D_Y=D_t=5 cA=8  C_K=166 + 2 Cmax
  instance slacks (Cmax=0): {'hC1': '117', 'hC2': '138', 'hC3': '293/2', 'hC4': '156', 'hC5': '331/2', 'hC6': '94', 'H1 gap e0-eps1': '7/8', 'H2 gap e0-2eps1': '3/4', 'H3 gap e0-2eps1': '3/4', "H4 gap e0-(eps1+k-c*D''/2)": '71/24', 'H5 gap e0-(k-(k+2))': '3', 'H6 gap e0-(k-(k+2))': '3'}
  n=0: W=4 N=4096 | W>=N^(1/6): True | W^(-3/2+dd)<=lam<=1/dd (dd=1): True | RangeCond N^(-1/2)<=1-t=1/32: True
  n=16: W=20 N=512000 | W>=N^(1/6): True | W^(-3/2+dd)<=lam<=1/dd (dd=1): True | RangeCond N^(-1/2)<=1-t=1/32: True
  n=40: W=44 N=5451776 | W>=N^(1/6): True | W^(-3/2+dd)<=lam<=1/dd (dd=1): True | RangeCond N^(-1/2)<=1-t=1/32: True
  |E|=0.50 <= 2-kappa=1.00: True; kappa'=0.80 <= Im mE(E)=0.9682: True
  case (ii): 1-s=1/16 <= lam^2/L^2=1/16 : True ; 0<=s<=v<=t<1: True ; s<v (non-collapsed): True
  D1 A-form window at grid time u=15/16: (1-u) L^2 = 1 <= A gK^2 = 1 : True
  D1 A-form window at grid time u=61/64: (1-u) L^2 = 3/4 <= A gK^2 = 1 : True
  D1 A-form window at grid time u=31/32: (1-u) L^2 = 1/2 <= A gK^2 = 1 : True
  BA-type R1 (kappa_BA=1/2, Aof=(k+1)/k=3, gK=3/5 lam): lam^2=1 <= Aof gK^2=27/25 : True ; gK<=lam: True ; window (1-s)L^2=1 <= Aof gK^2: True
  H1-H6 hold for all N > e^13.10 = 4.88e+05 (C5=9.528, eps0=1, Lambda_g=1); szB index with (4(n+4))^3 above it: n >= 16
  H1-H6 hold for all N > e^164.81 = 3.76e+71 (C5=9.528, eps0=0.1, Lambda_g=1); szB index with (4(n+4))^3 above it: n >= 180496799646136259313664
  H1-H6 hold for all N > e^24.55 = 4.59e+10 (C5=2.727e+04, eps0=1, Lambda_g=10); szB index with (4(n+4))^3 above it: n >= 891
  H1-H6 hold for all N > e^277.90 = 4.9e+120 (C5=2.727e+04, eps0=0.1, Lambda_g=10); szB index with (4(n+4))^3 above it: n >= 4245450928271499603713328925332958347264
```
`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505b/d1num.py` (the D1 operator bound, one index; tensor kernel ⇒ `‖⊗‖_∞→∞ = ∏`, so `C5 = Ci^k`; band kernel `S^(B)(g)`, circulant, `SB` `Defs/Block.lean:44`):
```
one-index D1 kernel on Z_L^3, E=1/2 (Im m=0.9682), d_inf->inf norm = sum_x|K(x)|; v=max(0,1-A g^2/L^2) (edge of the A-form window), w in {v,1-1e-3,1-1e-9}
T1 = Q.K(mu=1) [sigma_i != sigma_{i+1}, i in A];  T2 = Q.K(mu=m^2);  T3 = K(mu=m^2) [i not in A];  NEG = K(mu=1) without Q (i not in A, sigma_i != sigma_{i+1})
A=1 g=0.015625  T1 at L=(4, 8, 12, 24): 1.993 2.003 2.002 2.002 | max T2=2.001 T3=1.001 | NEG at L=4: 1.53e+04
A=1 g=1         T1 at L=(4, 8, 12, 24): 2.019 2.094 2.105 2.110 | max T2=2.000 T3=1.104 | NEG at L=4: 6.25e+07
A=1 g=10        T1 at L=(4, 8, 12, 24): 5.468 19.001 29.546 29.916 | max T2=4.858 T3=4.709 | NEG at L=4: 1e+09
A=3 g=0.015625  T1 at L=(4, 8, 12, 24): 2.043 2.027 2.023 2.021 | max T2=2.001 T3=1.000 | NEG at L=4: 4.58e+04
A=3 g=1         T1 at L=(4, 8, 12, 24): 2.493 2.587 2.614 2.631 | max T2=2.006 T3=1.311 | NEG at L=4: 1.88e+08
A=3 g=10        T1 at L=(4, 8, 12, 24): 5.468 19.001 41.901 86.815 | max T2=5.076 T3=4.782 | NEG at L=4: 1e+09
```
D1 is not an external hypothesis (band lemma `nzUgen_holds`; BA lemma `baTwKerZero_holds` merged): the limit check is the saturation in L (`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505b/d1large.py`, `T1`, `g=10`, `w=1-1e-9`):
```
A=1 g=10 T1 Q.K(mu=1), w=1-1e-9: L=12: 29.55  L=16: 29.78  L=24: 29.92  L=32: 29.98  L=48: 30.02
A=3 g=10 T1 Q.K(mu=1), w=1-1e-9: L=12: 41.90  L=16: 73.95  L=24: 86.82  L=32: 87.01  L=48: 87.13
```
NEG shows `A ⊇ I_diff(σ)` is necessary. Window `v ≤ w < 1`, `0 ≤ v`: tested at `w=v`, `1-1e-3`, `1-1e-9`.
Hypotheses at the instance (all in the script output): `|E|≤2-κ`, `κ'≤Im m`, `1-s=lam²/L²`, `s<v` (non-collapsed), WO(𝔡=1), `W≥N^{1/6}`, RangeCond, D1 window at `u=s, (s+v)/2, v`; BA-type R1 row (`Aof=3`, `gK=3/5·lam`). Limit: the conclusion is eventual; H1-H6 hold for `N>4.9e5` (n ≥ 16, `N=512000`) at `ε₀=1`, `Λg=1`; `ε₀=1/10` needs `N>3.8e71` — the example must use `ε₀=1`, `𝔡=1` (merged instances take the `∃ n` from the filter, not a number).

### 1a fill-in table (§269 (5))
| item | line |
|---|---|
| (i) | table above. |
| (ii) | script outputs above (band A=1; A-form window with A=3 on the band kernel at g=1/64, 1, 10, a proxy: the BA-kernel typecheck is the probe's). |
| (iii) | D1: band `nzUgen_holds` `QtNonzero:299` → `QtNZGen_KerNZ` via `bandStep2_Ugen` (`GridDuhamelGen:181`), `nqGood1_mE_im_ge`, `ZeroModeCalc_STIdiff_subset_iff` (`ZeroModeCalc:412`), `Aof=1`, `gK=lam` → BA `baTwKerZero_holds` (i ∈ A) + `baEKSameRow_holds` (i ∉ A) at `g=BAflowLam0`, `BAflow_real`, `Step2Kern_UN_BA` (`Chain/Step2Kern:124`). Others: `zeroModeSet_UNg` ← `ZeroModeGen_KerSums` (`zeroModeGen_kerSums_band`, field of `B45Gen_Facts`); `nz_hdriftNg` ← `driftTensorNg_norm_le_of_goodLin` (`NQLinGen:430`). |
| (iv) | D1 default text `T2505_KerNZ`/`Fam` (check `:154-170`) accepted unchanged: `(∀ i, σ i ≠ σ (finRotate k i) → i ∈ Aset)` is `STIdiff σ ⊆ Aset`; `1-g²/L²≤v ⟺ (1-v)L²≤g²`; `∃ C5` after `(k,κ,𝔡)`. Probe lines: D1 text, band discharge at `szB`, BA reading, BA-kernel instance. BA source exists: not BLOCKED. |
| (v) | row 14 (D1 Fam) is the only new class premise of row b; rows 15, 16 (`KLipFam`, `hFM`) enter only through the lifts of rows a, c, not read by targets 6-9; the case-(ii) subset of rows 1-7, 9 and the drift classes (eventual, `gridDriftNg_envelope_ev`, `NQEndLinGen:93`) go to the 1b start (0149 `:98`). |
| (vi) | converted: `cQVNZN`, `assembledRHSNZN`, `nz_hker`, `nz_hdriftN`, `subGaussStop_nzN`, `yMomentBounds_nzN`, `budgetNZN`, `nzGridEndN` (+ privates reading `mE (E n)`); reused: `zeroModeSet_idem`, `nzUgen_holds` (D1 discharge only); band only: `QtNonzeroInst`, `QtNonzeroEndInst`; instances: new at `bandStep2Mat`. |
| (vii) | UBA-C1 as planned: R1 enters only at target 8 (A-form window, merged precedent `st6_ini_nonzerog`, `Step6KitGen:401`, `hcmp`: `0≤gK·lam ∧ gK²≤lam² ∧ lam²≤Aof κm gK²`); D1 reads `gK`; no `sz.withLam`, no second comparison form. |
| (viii) | premise scan: see registry below. |
| (ix) | `open private` (model-free by the wide regex, list from `census_names.py`): `QtNonzero`: `qtNZ_tensorKer_one qtNZ_zeroModeSet_eq qtNZ_f qtNZ_q qtNZ_zeroModeSet_apply qtNZ_sum_abs_f_le qtNZ_sum_abs_q_le qtNZ_sum_norm_le_of_bound qtNZ_abs_le qtNZ_comb qtNZ_scalar qtNZ_absorb qtNZ_final`; `QtNonzeroEnd`: `nzEnd_ev_rpow_le nzEnd_ev_rpow_log_le nzEnd_ev_polylog_le nzEnd_one_le_size nzEnd_size_cast nzEnd_W_le_size nzEnd_Wpow_le nzEnd_ev_H1 nzEnd_ev_H4 nzEnd_ev_H56 nzEnd_ev_W_rpow_ge nzEnd_step_le nzEnd_K_mul_step nzEnd_gridTime_succ_sub nzEnd_gridTime_nonneg nzEnd_gridTime_le nzEnd_rangeCond_mono nzEnd_ev_union`. Copies (read `mE`, `etaT`): H2, H3, `hη`, `hδ`, `yMomentsMax`, assembly, row-sum lemmas (`qtNZ_row_of_op`, `qtNZ_re_sum_le`), on the model of `NQEndLinGen_*` (`open private … from RBM3D.Chain.NQEndLinGen`). |
| (x) | below. |
| (xi) | below (0 hits). |

### Lines (x)
`$HOME/scr_u3s4/census*.py` is absent on this device, so the census is re-derived by `census.py` (regex: ticket's list; wide adds band N-vocabulary names). `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505b/census.py`:
```
QtNonzero.lean         pure  decl-lines=1072 (to line 1136) B=621(8) P=53(3) M=398(17) census=719 x1.06=762
QtNonzero.lean         wide  decl-lines=1072 (to line 1136) B=682(11) P=55(3) M=335(14) census=781 x1.06=827
QtNonzeroEnd.lean      pure  decl-lines=1121 (to line 1183) B=824(10) P=0(0) M=297(20) census=887 x1.06=940
QtNonzeroEnd.lean      wide  decl-lines=1121 (to line 1183) B=862(12) P=0(0) M=259(18) census=925 x1.06=980
```
Per file (×1.24; ×1.06): ticket `QtNonzero` 737; 781, `QtNonzeroEnd` 915; 970 (sum 1,652; 1,751). Mine, mean of pure/wide: `QtNonzero` 750; 795, `QtNonzeroEnd` 906; 960. **Central (×1.06) row b = 1,755** (pure 1,702, wide 1,807) < 1,950: no split at 1a; each file ≤ 960 < 2,000. Not in either census figure (new text and instances): D1 text and band discharge, and the instance sections (merged twins: `NQEndLinGen:897-1022` 126 lines, `QEndGridGen:1057-1168` 112; band sections here 566 and 398, `T2505.md:6`). My bottom-up guess with D1 ≈ 90 and instances ≈ 125 + 150 is ≈ 2,120; the ticket's new-file factors (`T2505.md:14`) are ×1.16, ×1.09, ×0.69, ×1.06, ×0.99 (1.16 × 1,755 = 2,036). Risk flagged; checkpoint after file 1 (`QtNonzeroGen`): if file 1 > 1,000 or file 1 + the 960 projection > 1,950, split at the file boundary (`t/T2505b2`).

### Registry (`Test/Axioms.lean`) and scan (viii)
`python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2505b/cone.py; grep` (name clash, importers):
```
cone modules: 182 | BA.* / Chain.Step2Kern / Chain.Qt* in the cone of the planned imports: []
grep new public names/files in RBM3D/ (worktree): 0 hits; Qt*-importers among RBM3D/Chain|BA|Graph: 0
```
Premises of the new public theorems (`nz_hkerg`, `nz_hdriftNg`, `subGaussStop_nzNg`, `yMomentBounds_nzNg`, `budgetNZNg`, `nzGridEndNg`, D1): `STKboundgL` (line 134, owedProps, stays); `SizeTendsto` (255), `Admissible` (256), `locDomain` (258), structural. Already assumed by merged theorems (so classified by the merged scan, `main` builds), band discharges: `StepDecompGen_LoopForm`/`WalkForm` (`stepDecompGen_loopForm_band`, `_walkForm_band`), `DecayGen_Spec` (`DecayGen_bandSpec`), `GridRepTailGen_Ker` (`gridRepTailGen_ker_band`), `HierDriftGen_Expand/KLoop/KTwo/UStep` (`hierDriftGen_*_band`), `ZeroModeGen_KerSums` (`zeroModeGen_kerSums_band`), `STCaseII` (`szB_caseII`). Row b adds no other assumed `Prop`. **New Props `QtNZGen_KerNZ`, `QtNZGen_KerNZFam`**: the scan counts a `Prop` def taken as a hypothesis (any constant in a binder) that no theorem concludes at its head. Row-b theorems take the per-index `QtNZGen_KerNZ`, so file 1 must also contain a per-index band theorem `qtNZGen_kerNZ_band_at` (head `QtNZGen_KerNZ`, as `nqGoodGen_kerNAL_band_at`) besides `qtNZGen_kerNZ_band` (head `Fam`). Then no new line is needed; lines 121, 214 belong to rows a, c. Without the per-index theorem `#assert_rbm_axioms` would report an unclassified premise.

### Verdicts
- Target 6 (D1): PASS. Window, constant order, BA source (`baTwKerZero_holds`, `baEKSameRow_holds`) and band discharge close; numerics above.
- Target 7 (`QtNonzero` §2-§8 twins): PASS. All premises are merged generic classes; exponents close (table).
- Target 8 (`nzGridEndNg`): PASS. `hC1..hC6`, H1-H6 slack positive on the grid; the instance needs `ε₀=1`, `𝔡=1` to avoid an astronomical threshold.
- Target 9 (instances at `d=3`): PASS, with the data above (`szB`, band carrier `bandStep2Mat szB (E ·)`).

## (a′) Preflight corrections — Wed Oct 14 12:37:17 UTC 2026
No verdict changes. (1) (a)(ix) lists `H2`, `H3`, `hη`, `hδ`, `yMomentsMax`, the assembly and the row-sum lemmas `qtNZ_row_of_op`, `qtNZ_re_sum_le` as copies. In the files `hη`, `hδ`, `yMomentsMax` are the merged `NQEndLinGen_*` privates and `qtNZ_re_sum_le` is the model-free band private, all reused by `open private`; the copies are `H2`, `H3`, `qtNZ_row_of_op` (as `qtNZGen_row_of_op`), `qtNZ_stopped_comm` (as `QtNZGen_stopped_comm`), the projected collapse and the assembly.
(2) (a)(ii) says the example must use `ε₀ = 1`, `𝔡 = 1`: `nzGridEndNg` has no `𝔡` (the coupling window is inside D1) and the instance unfolds the eventual conclusion at one `n` (`Eventually.exists`); it uses the merged `QtNonzeroEndInst` data (`ε₀ = 1/10`, `D₁ = 1`, `Λg = 10`, `𝔠 = 1/6`, `τ = 1/2`, `κm = √1/2`).

## (a″) Probe compile — Wed Oct 14 09:48:16 UTC 2026

Probe commit `bf9aaf6a` on `t/T2505b` (author from `.git/config`): `RBM3D/Probe/T2505Pins.lean`, 292 lines (cap 300), not imported by `RBM3D.lean`; `git diff main...t/T2505b --stat` lists this file only. Section (a) is unedited.

Command (cwd `/Users/junyin/Lean_proof/RBM3D-wt/T2505b`, run at Wed Oct 14 09:47:41 UTC 2026, on the committed file), exit code 0:
```
$ lake env lean RBM3D/Probe/T2505Pins.lean
unclassified T2505_ premises, file as written: []
same, `probe_kerNZ_band_at'` excluded as a head: [RBM.BA.T2505_KerNZ]
@T2505_KerNZ : {d : ℕ} → {sz : Sizes d} → FlowFM sz → (ℕ → ℝ) → ℕ → ℝ → ℝ → ℕ → Prop
T2505_KerNZFam : (d : ℕ) →
  (Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop) →
    ((sz : Sizes d) → (ℕ → ℂ) → FlowFM sz) → (Sizes d → (ℕ → ℂ) → ℕ → ℝ) → (ℝ → ℝ) → Prop
probe_shape_KerNZ : ∀ (d : ℕ),
  (T2505_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz x => sz.lam)
      fun x => 1) ∧
    T2505_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z)
      fun κ => (κ + 1) / κ
'RBM.BA.probe_kerNZ_band_at'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_kerNZFam_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_kerNZ_BA_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_kerNZFam_BA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_shape_KerNZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_BAReal_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_BA_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
exit code: 0
```
Declarations of the probe (`grep -nE "^(theorem|def|example) " RBM3D/Probe/T2505Pins.lean | cut -c1-110`):
```
39:def T2505_KerNZ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (A C5 : ℝ) (n : ℕ) : Prop :=
45:def T2505_KerNZFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
55:def probeDelta (L : ℕ) : (Fin 3 → Zd 3 L) → ℂ := fun a => if a = 0 then 1 else 0
57:theorem probeDelta_norm (L : ℕ) [NeZero L] : ‖probeDelta L‖ = 1 := by
63:def probeBandC (d k : ℕ) (Λg κ' : ℝ) : ℝ :=
66:theorem probeBandC_pos {d : ℕ} (hd : 3 ≤ d) {k : ℕ} (hk : 2 ≤ k) {Λg κ' : ℝ} (hΛg : 0 < Λg) (hκ' : 0 < κ') 
73:theorem probe_kerNZ_band_at' {d : ℕ} (hd : 3 ≤ d) {k : ℕ} (hk : 2 ≤ k) {Λg κ' : ℝ} (hΛg : 0 < Λg) (hκ' : 0 
92:theorem probe_kerNZFam_band (d : ℕ) :
108:example : ∃ C5 : ℝ, 0 < C5 ∧ ∃ n : ℕ, (1 - (15 / 16 : ℝ)) * ((szB.L n : ℕ) : ℝ) ^ 2 ≤ 1 * szB.lam n ^ 2 ∧
126:theorem probe_kerNZ_BA_at (d k : ℕ) (Λ κ A : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) (hA : 0 < A) :
165:theorem probe_kerNZFam_BA (d : ℕ) :
175:theorem probe_shape_KerNZ : ∀ d : ℕ,
186:theorem probe_BAReal_pt (g : ℝ) (hg : 0 < g) :
209:theorem probe_BA_inst (g : ℝ) (hg : 0 < g) :
241:example : ∃ (g0 E0 κ0 : ℝ), 0 < g0 ∧ g0 ≤ 1 / 64 ∧ 0 < κ0 ∧ ∃ C5 : ℝ, 0 < C5 ∧ ∃ v w : ℝ, 0 < v ∧ v < w ∧ 
248:example : ∃ (g0 E0 κ0 : ℝ), 0 < g0 ∧ g0 ≤ 1 ∧ 0 < κ0 ∧ ∃ C5 : ℝ, 0 < C5 ∧ ∃ v w : ℝ, 0 < v ∧ v < w ∧ w < 1
256:example : ∃ (g0 E0 κ0 : ℝ), 0 < g0 ∧ g0 ≤ 10 ∧ 0 < κ0 ∧ ∃ C5 : ℝ, 0 < C5 ∧ ∃ w : ℝ, 0 < w ∧ w < 1 ∧
268:theorem probe_consumer {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (A C5 : ℝ) (n : ℕ)
```
Checks (scripts): D1 text against the check, forbidden words, name clash outside the probe, axioms of the four `example`s (a scratchpad copy of the committed file with each `example` renamed `probe_example_N`, then `#print axioms`):
```
D1 text vs docs/tickets/checks/T2505-check.lean:154-167: identical (blank lines stripped)
sorry|admit|native_decide|axiom in the probe: 0 hits
T2505_KerNZ|probe_* names outside the probe in RBM3D/: 0 hits
'RBM.BA.probe_example_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_example_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_example_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_example_4' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Measured size (`awk` over the committed file, blank lines dropped): D1 text 13 lines; band discharge (`probeBandC` .. `probe_kerNZFam_band`, with docstrings) 40 lines; BA product step plus family (`probe_kerNZ_BA_at` .. `probe_kerNZFam_BA`, probe only) 50 lines.

### What the probe shows (narrative)
1. **D1 text compiles unchanged** (script diff above) against `main` d3104f3b: `T2505_KerNZ`, `T2505_KerNZFam` with the A-form window `(1 - v) L² ≤ A gK²`, `∃ C5` after `(k, κ, 𝔡)`, `∀ᶠ n`. (a)(iv) is confirmed; no (a′) needed.
2. **Band discharge** (`Aof = 1`, `gK = sz.lam`). `probe_kerNZ_band_at'` is `nzUgen_holds` (`QtNonzero:299`) read through `bandStep2_Ugen` (`GridDuhamelGen:181`) and `ZeroModeCalc_STIdiff_subset_iff`; the window `(1 - v) L² ≤ lam²` is `1 - lam²/L² ≤ v`. `probe_kerNZFam_band` is the family at `STFlow` with `Λg = 𝔡⁻¹`, `κ' = min κ (4/5)`: `0 < lam ≤ 𝔡⁻¹` eventually from the fifth `Admissible` field (`WO 𝔡`), `|E| ≤ |Re z| ≤ 2 - κ` by `abs_lemE_le` and `locDomain`, `κ' ≤ Im mE` by `nqGood1_mE_im_ge`.
3. **Band instance at `szB`** (example 1): the merged datum `flow_zB` (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; (a)(ii) uses `κ = 𝔡 = 1`, `E ≡ 1/2`, which the probe does not use), window `(1 - 15/16) · 16 = 1 ≤ 1 · lam²`, `k = 3`, `σ = (+,-,+)`, `A = {0,1} = I_diff(σ)`, `X = δ₀` with `‖X‖ = 1`, grid pair `(15/16, 31/32)`: the conclusion holds at some `n` taken from the filter.
4. **BA reading, with a proof.** `probe_kerNZ_BA_at` proves the per-index D1 at the BA carrier `baFM sz lam0 E` for every `A > 0`: `Step2Kern_UN_BA` (`Chain/Step2Kern:124`) turns `Step2Gen_UN` into `BAUN`; the product over indices uses `baTwKerZero_holds` (`TwistKer:256`) at `i ∈ Aset` and `baEKSameRow_holds` (`EKPins:568`) at `i ∉ Aset`, the product step of `baEKSumDecayNonzero_holds` (`EKNonzero:261`) with the A-form lemma; `C5 = (max Cs C1)^k`, fixed by `(d, Λ, κ, A)` before `(sz, z)`. `probe_kerNZFam_BA` is `T2505_KerNZFam` at `BAFlow`, `baFMz`, `BAflowLam0`, `Aof κ = (κ+1)/κ`, for every `d`, from `BAflow_lam0_window` and `BAflow_real` (`GreenSchur`). `probe_shape_KerNZ` is the check's `T2505_shape_KerNZ` proved at both families. So D1 has a BA source and the stop rule "D1 without a BA source" does not fire. The BA modules and `Chain.Step2Kern` are imported by the probe only; the new row-b files may not.
5. **BA-kernel instance at `g = 1/64, 1, 10`** (examples 2-4, `probe_BA_inst`). `probe_BAReal_pt` gives `BAReal 3 4 g₀ κ₀ E₀ m₀` at the chain point `(L, g) = (4, g)` from `zS`, `mS` (`MFixedPointInst`, as `flowP_real` `CouplingWindow:878` at `g = 10`): `0 < g₀ ≤ g`, `0 < κ₀ < 6/5`, `Aof κ₀ · g₀² = (5/6)(κ₀ + 1) g²` (`t₀ = 5κ₀/6` since `z_S + m_S = 6i/5`). The carrier is `baFM szB (fun _ => g₀) (fun _ => E₀)`; `lam0` is a free argument of `baFM`, so `szB.lam` is not read. Every hypothesis of `T2505_KerNZ` is discharged. `g = 1/64` and `g = 1`: a genuine window `0 < v < w < 1`, `(1 - v) · 16 ≤ A g₀²`. `g = 10`: `16 ≤ A g₀²`, the window is all of `[0, 1)` (`v = 0`). Not probed: the `BAFlow` domain (`Im z ≤ 1`) at `g = 1, 10`; D1 per index reads `BAReal` only.
6. **Premise scan (finding for 1b).** `RBM.Audit.scanPremises` (`Test/Axioms.lean:485`) run on the probe environment, filtered to `RBM.BA.T2505_*`: `[]` with the per-index theorem `probe_kerNZ_band_at'` (head `T2505_KerNZ`) present, `[RBM.BA.T2505_KerNZ]` with it excluded as a witness (`probe_consumer` assumes `T2505_KerNZ`, as `nz_hkerg` will). An `∃ C5` per-index form has head `Exists` and would not count (`conclusionHead` walks `∀` only). So (a)'s registry paragraph holds, with one addition: the per-index band theorem must conclude `QtNZGen_KerNZ` with an explicit constant, which needs one public real-valued `def` in file 1 (probe: `probeBandC`, a total `Classical.choose` of the `∃ C` of `nzUgen_holds`, 2 lines); the family theorem alone is not enough.
7. No finding changes a verdict of (a); sections (b)-(d) belong to stage 1b proper.

## (b) Script output — Wed Oct 14 12:37:17 UTC 2026
```
$ git rev-parse --short HEAD; git status --short | wc -l; git diff --stat d3104f3b..HEAD     # G1: no band, BA, Graph or merged Chain file; the probe stays on the branch
29c0faf2   0 uncommitted
 RBM3D.lean                       |   2 +
 RBM3D/Chain/QtNonzeroEndGen.lean | 688 ++++++++++++++++++++++++++++
 RBM3D/Chain/QtNonzeroGen.lean    | 956 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2505Pins.lean       | 292 ++++++++++++
 4 files changed, 1938 insertions(+)
$ imports / importers / import cone (python over `import` lines)
QtNonzeroGen: ZeroModeGen NQLinGen GridAssemblyGen AzumaProxyGen StepDecompGen Induction.QtNonzero; QtNonzeroEndGen: QtNonzeroGen NQEndLinGen NQBudgetGen Induction.QtNonzeroEnd
importers: QtNonzeroEndGen, RBM3D.lean; cone: 184 modules; BA.*, Chain.Step2Kern, other Chain.Qt* in the cone: []
$ lake env lean docs/tickets/checks/T2505-check.lean      # 12:27:06 UTC
exit 0, 0 'error' lines
$ lake build RBM3D.Chain.QtNonzeroGen RBM3D.Chain.QtNonzeroEndGen 2>&1 | grep -E 'Built|Replayed|Build completed|error' | grep -E 'QtNonzero(End)?Gen|Build comp|error'     # 12:36:02 UTC
⚠ [3885/3889] Replayed RBM3D.Chain.QtNonzeroGen
⚠ [3889/3889] Replayed RBM3D.Chain.QtNonzeroEndGen
Build completed successfully (3889 jobs).
$ lake build      # full, 12:34:25 UTC at HEAD 29c0faf2 (RBM3D.lean imports both modules)
Built RBM3D (66s);  info: RBM3D.lean:622:0: axiom audit: 15230 theorems, 4704 definitions, 0 axioms in `RBM`;  premises found by scanning: 143 (borrowed 1, owed 64, structural 58, refuted 6, superseded 14)
Build completed successfully (4392 jobs).   lake build  65.61s user 1:08.43 total
$ #print axioms (scratch copies of both files with the 11 examples renamed; scratchpad ax_f1.txt, ax_f2.txt)
19 public decls: QtNZGen_KerNZ, QtNZGen_KerNZFam, qtNZGen_bandC, qtNZGen_bandC_pos, qtNZGen_kerNZ_band_at, qtNZGen_kerNZ_band, qtNZGen_row_of_op, qtNZGen_row_of_kerNZ, cQVNZNg, assembledRHSNZNg, nz_hkerg, nz_hdriftNg, subGaussStop_nzNg, yMomentBounds_nzNg, budgetNZNg, qtNZGen_subGaussStop_instance, nzGridEndNg, nzGridEndN_of_gen, qtNZEndGen_instance
and 11 instance examples: all depend exactly on [propext, Classical.choice, Quot.sound]; other: 0
$ statements by script (D1 whole; others: declaration line numbers, text in the files)
QtNonzeroGen.lean:56-59
def QtNZGen_KerNZ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (A C5 : ℝ) (n : ℕ) : Prop :=
  ∀ v w : ℝ, 0 ≤ v → (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ A * gK n ^ 2 → v ≤ w → w < 1 →
    ∀ (σ : Fin k → Bool) (Aset : Finset (Fin k)), (∀ i, σ i ≠ σ (finRotate k i) → i ∈ Aset) →
      ∀ X : (Fin k → Zd d (sz.L n)) → ℂ, ‖zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X)‖ ≤ C5 * ‖X‖
QtNonzeroGen.lean:62-66
def QtNZGen_KerNZFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C5 : ℝ, 0 < C5 ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, QtNZGen_KerNZ (mk sz z) (gK sz z) k (Aof κ) C5 n
QtNonzeroGen: 71 qtNZGen_bandC; 74 qtNZGen_bandC_pos; 81 qtNZGen_kerNZ_band_at; 102 qtNZGen_kerNZ_band; 121 qtNZGen_row_of_op; 144 qtNZGen_row_of_kerNZ; 161 cQVNZNg; 168 assembledRHSNZNg; 191 nz_hkerg; 213 nz_hdriftNg; 247 subGaussStop_nzNg; 372 yMomentBounds_nzNg; 488 budgetNZNg; 883 qtNZGen_subGaussStop_instance
QtNonzeroEndGen: 382 nzGridEndNg; 553 nzGridEndN_of_gen; 639 qtNZEndGen_instance
$ diff <(T2505-check.lean:154-167, T2505_KerNZ -> QtNZGen_KerNZ, blank lines stripped) <(QtNonzeroGen:56-66, blank lines stripped)    # no output: identical
$ diff <(QtNonzeroEnd.lean `theorem nzGridEndN :` .. `:= by`) <(QtNonzeroEndGen:553 `nzGridEndN_of_gen`, renamed)    # 36 statement lines, 0 diff lines
$ grep -nE "^(example|theorem .*instance)" -> compiled nonempty instances: QtNonzeroGen 777 D1 family at szB/flow_zB (X = δ₀, ‖X‖ = 1, A = {0,1}); 793 row-sum form at szB; 803 nz_hkerg at szB (X = Q^(A)δ₀ ≠ 0);
835 nz_hdriftNg at sz0 (A = ∅, I_diff); 846 drift level > 0; 883 subGaussStop_nzNg (every A, m ≤ 4, j < m, label a); 894 proxy > 0; 909 yMomentBounds_nzNg at Y_j = ζ_jδ₀; 923 budgetNZNg (N = 2^21);
QtNonzeroEndGen 639 qtNZEndGen_instance (nzGridEndNg at szB, grid KB C_K, s = 15/16 < v = 31/32, Δ > 0) and examples 676, 679, 682 (k = 2, 3, 4)
$ wc -l RBM3D/Chain/QtNonzero{,End}Gen.lean; instance sections = from "## 7. Compiled" / "## 4. Compiled" to the end
956 QtNonzeroGen.lean;688 QtNonzeroEndGen.lean;1644 total;
file 1: non-instance 751 lines, instance section 205; file 2: non-instance 620 lines (incl. 74-line band re-derivation (546-619)), instance section 68
census (ticket T2505.md:13, x1.24; x1.06): QtNonzero 737; 781, QtNonzeroEnd 915; 970 (sum 1,652; 1,751); (a) Lines (x) mean: 750; 795 and 906; 960 (row 1,755 central)
measured/census: file 1 total 1.30 / 1.22, non-instance 1.02 / 0.96; file 2 total 0.75 / 0.71, non-instance 0.68 / 0.64; row total 0.995 / 0.939
$ C1/X1-C1 regex over the 19 public statements (stmts.py): 5 hits, all band discharge / band re-derivation (`qtNZGen_bandC` nzUgen; `_kerNZ_band_at` mE; `_kerNZ_band` STFlow, STflowE; `nzGridEndN_of_gen` 2 - κ); 0 in generic statements
whole-file hits (classify.py): QtNonzeroGen {docstring 8, D1 band discharge 9, instances 1}; QtNonzeroEndGen {docstring 7, band re-derivation 5, instances 3}; generic code 0;  X1-C4 def hits 0
$ grep -cE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds|sorry|admit|native_decide|^axiom|withLam" (both files): 0, 0
$ grep -nE "∀ \(sz : Sizes d\)" (both files): QtNonzeroGen:62, 63, 65 (the guarded D1 family def; row 14)
$ name clash: grep -rnE of the 19 new public names over RBM3D/ (this worktree and main), minus the two files and the probe: 0 hits.  No RBM1D/RBM2D port in this ticket (no port diff-stat).
$ open private (reuse, no copy): QtNonzeroGen from QtNonzero (9): qtNZ_sum_norm_le_of_bound qtNZ_sum_abs_q_le qtNZ_q qtNZ_zeroModeSet_apply qtNZ_re_sum_le qtNZ_comb qtNZ_aesm_of_pow4 qtNZ_absorb qtNZ_final
  QtNonzeroGen from QtNonzero (15): qnDelta qnU qnU_nonneg qnU_lt_one qnU_ge qnU_mono qn_mE0_im qn_gridTime_nonneg qn_gridTime_le qn_W0 qn_N0 qn_N_eps1 qn_N_nine qn_Ls_le qn_Ls_nonneg
  QtNonzeroGen from NQLinGen (8): NQLinGen_Cm0 NQLinGen_hL0 NQLinGen_hWalk0 NQLinGen_hQV0 NQLinGen_hm0 NQLinGen_hS0 NQLinGen_tau0 NQLinGen_tau0_pos
  QtNonzeroEndGen from QtNonzeroEnd (12): nzEnd_ev_H1 nzEnd_ev_H2 nzEnd_ev_H3 nzEnd_ev_H4 nzEnd_ev_H56 nzEnd_one_le_size nzEnd_step_le nzEnd_K_mul_step nzEnd_gridTime_nonneg nzEnd_gridTime_le nzEnd_rangeCond_mono nzEnd_ev_union
  QtNonzeroEndGen from NQEndLinGen (7): NQEndLinGen_Ep NQEndLinGen_ev_hη NQEndLinGen_ev_hδ NQEndLinGen_stepErrNg_nonneg NQEndLinGen_eta_win NQEndLinGen_Hpath_collapse NQEndLinGen_yMomentsMax
```

### Name-level tables (0149 :98); owners of the BA column are read from the T2498/T2505 tables, not re-verified here
(iii) hypothesis table (band fact → generic hypothesis of `nzGridEndNg` / D1 → band discharge → BA source)
| band fact | generic hypothesis | band discharge | BA source |
|---|---|---|---|
| `nzUgen_holds` (`|E|<2`, `‖m‖=1`, window `1-g²/L² ≤ v`) | `QtNZGen_KerNZ C gK k A C5 n` (D1, A-form window), `hKerN : ∀ᶠ n` | `qtNZGen_kerNZ_band_at`, `_band` (`A = 1`, `gK = lam`) | `baTwKerZero_holds`, `baEKSameRow_holds` (probe `probe_kerNZ_BA_at`); U3-BA (a) |
| `zeroModeSet_Ugen` (`3 ≤ L`, `|E| ≤ 2`) | `hKS : ∀ n, ZeroModeGen_KerSums` (`B45Gen_Facts` field) | `zeroModeGen_kerSums_band` | `baB45Gen_facts` |
| `etaT`, `mE`, `|E|<2`; walk `pathH` | `StepDecompGen_LoopForm`, `hm : ‖m‖ ≤ 1`; `StepDecompGen_WalkForm`, `hSeq` | `stepDecompGen_loopForm_band`, `norm_mE`; `stepDecompGen_walkForm_band` | U2-BA carrier facts; T5-BA |
| `κ' ≤ Im m`, `η = (1-u) Im m` | `hspec : DecayGen_Spec κm` | `DecayGen_bandSpec` (`√κ/2`) | `EMn2BA_mF_data` |
| row sums, K1–K4, link | `hRow : ∀ n, GridRepTailGen_Ker`, `hS`, `hKK` | `gridRepTailGen_ker_band`, `hierDriftGen_SB_row` | `gridRepTailGen_ker_BA`, `BAflow_real` |
| `gridDriftN_envelope`, `STKbound` | `hExp hKL hKT hU` (`∀ᶠ n`), pin `hKb : STKboundgL` | `hierDriftGen_*_band`, `stKbound_holds` | T5-BA eventual classes (UP-C4); the pin `STKboundgL` stays in owedProps |
| `STCaseII`, `lam ≤ …` window | `hcase : STCaseII`, `hR1 : lam² ≤ Ar gK²`, `hrange`, `hband` | `szB_caseII`, `Ar = 1`, `rangeCond_tB`, `szB_bandwidth` | `TwistStep2_lam0_sq`, `BAflow_lam0_window`, `Aof κ = (κ+1)/κ` |
(v) family premises as used: row 14 (D1 `QtNZGen_KerNZFam`, guarded, `∃ C5` after `(k, κ, 𝔡)`, `∀ᶠ n`) is the only new class premise of row b. Targets 6–9 read T2498 rows 3, 4, 6 (`DecayGen_Spec` only), 7, 9 (the field `ZeroModeGen_KerSums` only), 10 (`lam² ≤ Ar gK²` only), 11 (eventual classes, `hKK`; `hη` derived from `LoopForm`), 12; not read: rows 1, 2, 5, 8 (EK-4, NAL), 9 (`hTh`, `WardCls`, thetaKer), 15, 16 (the lifts of rows a, c).
(vi) scope: converted `cQVNZN`, `assembledRHSNZN`, `nz_hker`, `nz_hdriftN`, `subGaussStop_nzN`, `yMomentBounds_nzN`, `budgetNZN`, `nzGridEndN` (+ private `qtNZ_row_of_op` → `qtNZGen_row_of_op`, `qtNZ_stopped_comm` → `QtNZGen_stopped_comm`, `nzEnd_assembly`/`nzEnd_collapse`/`nzEnd_ev_H2`/`H3` → `QtNZEndGen_*`); reused `zeroModeSet_idem`, `nzUgen_holds` (D1 band discharge only), the model-free privates (above); band only `QtNonzeroInst`, `QtNonzeroEndInst` (public facts by name); new in Lean: D1 defs, `qtNZGen_bandC(_pos)`, `qtNZGen_kerNZ_band(_at)`, `qtNZGen_row_of_kerNZ`, `nzGridEndN_of_gen`.

### Narrative
1. Targets 6–9: `QtNonzeroGen.lean` = D1 (§1), vocabulary (§2), fields (§3), Azuma (§4), `Y` moments (§5), budget (§6), instances (§7); `QtNonzeroEndGen.lean` = regime (§1), assembly (§2), `nzGridEndNg` (§3), band re-derivation (§3b), instance (§4). Sections §1–§6 of file 1 started from the uncommitted draft the previous stage left (a lead); its statements were compared with the band `QtNonzero` ones before it was kept.
2. D1 is the check text (diff above). Both the family theorem and the per-index theorem `qtNZGen_kerNZ_band_at` (head `QtNZGen_KerNZ`) are present (1a-audit O2); the per-index constant is `qtNZGen_bandC`, a total `Classical.choose` of `nzUgen_holds`. The scan of the full build lists 143 premises and none unclassified; row b needs no registry line and `Test/Axioms.lean` is untouched.
3. R1 enters once: at a grid time `u ≥ s`, `(1 − u) L² ≤ (1 − s) L² ≤ lam² ≤ Ar gK²` from `STCaseII` and `hR1` (`hcaseU` in `QtNZEndGen_assembly`), which is D1's window; no `sz.withLam`, no other comparison, no other coupling.
4. `nzGridEndNg` against `nqGridEndLinNg`: D1 per index (`hKerN`, constant `C` after `k`) replaces `NQGoodGen_KerNAL`, `Ck`/`Cv`, `hcmp`, `hA`; `STCaseII` replaces `STCaseI` and `hWt`; no `𝔡`, `WO`; `hKS` is added. `hst` is unused (kept from the band text). The kernel bound is loss-free, so the exponents are the band's ((a)(i)).
5. `nzGridEndN_of_gen` has the band statement of `nzGridEndN` (diff above) and is proved from `nzGridEndNg` at `bandStep2Mat sz E`, `seqP sz`, `Ar = 1`, `gK = lam`: every hypothesis of `nzGridEndNg` is dischargeable at the band for all `d ≥ 3`, not only at one point.
6. Instances: D1 itself at `szB` (777, 793, 803; the window is the equality `(1 − 15/16)·16 = 1 ≤ lam²`) and `nzGridEndNg` at `szB` for `k = 2, 3, 4` (639–682, non-collapsed window). The `sz0` grid `u ≤ 1/32` is below the D1 window (`1 − lam²/L² = 65535/65536`), so `subGaussStop_nzNg` there takes the coarse row `2^{|A|}(1 + 32/31)^3` (`GridAssemblyGen_norm_UN_coarse`), as the band instance does.
7. Calibration: non-instance lines 751 and 620 against the census 737; 781 and 915; 970 (ratios above). File 2 is below the census because the regime lemmas `hη`, `hδ`, `yMomentsMax`, the step-error sign, `Hpath_collapse` are the merged `NQEndLinGen_*` privates (opened, not copied); the instance sections are 205 and 68 lines.
8. Stop rules: none fired (files 956, 688 ≤ 2,000; no band edit; cone clean; D1 text identical; every `∃` and guard as in D1; no `∀ n` drift premise: `hExp hKL hKT hU` are eventual, `hRow`, `hKS` are the merged `∀ n` forms; no new kernel, `FlowFM` field or `STGridRepNgL`; scan clean).

## (c) Verified Mathlib names
`#check @n` in the worktree (scratchpad `mlnames.lean`, 23 names, 0 errors): Finset.sum_pos, NNReal.coe_pos, Real.toNNReal_pos, pi_norm_le_iff_of_nonneg, norm_le_pi_norm, Real.rpow_le_rpow_of_exponent_le, MeasureTheory.measureReal_iUnion_fintype_le, MeasureTheory.measureReal_empty, Fintype.card_subtype_le, Set.compl_iInter, div_le_div_iff₀, le_div_iff₀, pow_le_pow_left₀, pow_le_pow_right₀, LinearMap.continuous_of_finiteDimensional, Real.sqrt_le_iff, Real.rpow_neg_one, Real.one_le_rpow, Finset.sup'_le, Filter.eventually_all, Real.rpow_pos_of_pos, Real.rpow_le_rpow_of_nonpos, MeasureTheory.condExp_nonneg. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- The new files prove D1 at the band only; its BA instance (`QtNZGen_KerNZFam` at `BAFlow`, `Aof κ = (κ+1)/κ`) is U3-BA (a) (the probe compiles it; probe never merged). What stays hypothetical for BA: D1 family, `hKS` (`B45Gen_Facts`), `hR1`, the four eventual drift classes, the pin `STKboundgL` (owedProps, unchanged).
- Merge: `main` moved after the branch point (74b7c64b merged row a); `RBM3D.lean` carries two added import lines after `QEndB1Gen` and is a union of import lines at merge.
- `T2505ba` (D1; `lem:sum_decay_nonzero`, `3_5:1666`): constant `C5` instead of `≺`, A-form window `(1 − v)L² ≤ A gK²`, kernel coupling `gK` (BA: `gK ≠ lam`); covered in substance by D37, D588, D699 (b) (1a-audit O5).
- `T2505bb` (`nzGridEndNg`; `lem:STOeq_Qt_nonzero`, `3_5:1561`): takes the D1 constant and `hR1`, has `STCaseII`, no `𝔡`, `WO`, `κ` (`DecayGen_Spec κm`), and adds `ZeroModeGen_KerSums`, `STKboundgL`; the band `nzGridEndN` is recovered by `nzGridEndN_of_gen`.
- `T2505bc` (Lean only): `qtNZGen_bandC`, the `Classical.choose` of the `∃ C` of `nzUgen_holds`, so that the per-index band theorem concludes `QtNZGen_KerNZ` (1a-audit O2).
