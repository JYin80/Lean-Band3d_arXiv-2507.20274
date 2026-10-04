Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 21:08:21 UTC 2026

Source: RBM2D `Induction/AzumaProxyN.lean` at `c9a24cf` (2469 lines there: `git show c9a24cf:… | wc -l` = 2469; RBM2D HEAD `9e0f275` has a trimmed 1471-line file, so all line numbers below are `c9a24cf`). `N = size n = (W L)^d` (`Defs/Sizes.lean:157`), `#Idx = N` (`card_Idx`, `Sizes.lean:160`), `#CoordF = 2N²` (merged private `StepDecomp_card_Coord`, `Path/StepDecomp.lean:475`). Merged names are from the T2159 file `RBM3D/Induction/AzumaProxyN.lean` (main `43ab861`), `GridAssemblyN.lean`, `StepDecompN.lean`, `LoopC2N.lean`.

### (i) Exponent table and dictionary

| # | item | RBM2D (d = 2) | RBM3D (d ≥ 3) | check |
|---|---|---|---|---|
| 1 | `N` and `#Coord` | `N=(WL)^2`, `#Coord = 2N²` | `N=(WL)^d`, `#CoordF = 2N²` (brute force d=3,L=3,W=1: 1458 = 2·27²) | PART A below |
| 2 | `gvar ≤ 1` (needed for `E ω⁸ = 105 v⁴ ≤ 105`, `v ≤ 1`) | trivial (fixed 5-point `svar ≤ 1`) | **`3 ≤ L` is used**: `svarF = W^{-d}·S^(B)(g)` entry, rows of `S^(B)` sum to 1 (`sum_sbKernelR`, `Defs/Block.lean:93`, needs `card_nbhd`, `3 ≤ L`); tight at `g=0, W=1` (diag = 1). Merged lemma is private (`StepDecomp_gvar_le_one`, `StepDecomp.lean:448`) → copy as `azumaProxy2_gvarF_le_one` | PART A: row sums 1, max svarF ≤ 1 |
| 3 | `E‖X‖² ≤ c₂ N^a`, `E‖X‖⁴ ≤ c₄ N^b` | `16 N⁴`, `768 N⁸` | same, merged public `integral_normSq_incr_le`, `integral_normPow4_incr_le` (`StepDecomp.lean:699,708`) | `4·#Coord²=16N⁴`, `48·#Coord⁴=768N⁸` (`#Coord=2N²`) |
| 4 | `E‖X‖⁸ ≤ 6881280 N^16` (new, target 1) | `256·#Coord⁷·#Coord·105 = 26880·(2N²)⁸ = 6881280 N^16` | identical (only `#Coord = 2N²` and `v ≤ 1` enter): 26880·256 = 6881280 | PART B |
| 5 | v-level `2ρ²(B₄+m₂²)`, `ρ = S C₂ Δ/2`, `m₂ ≤ 16N⁴` | `2ρ²(768+256)N⁸ = 512 (S C₂)²Δ² N⁸ ≤ Δ²P` (slack 2000/512 = 3.9) | same constants | PART B |
| 6 | w-level `8ρ⁴(B₈+m₂⁴)`, `m₂⁴ ≤ 65536 N^16` | `3473408 (S C₂)⁴Δ⁴N^16 ≤ Δ⁴P²`, `P² = 4·10⁶ (S C₂)⁴N^16` (slack 1.152) | same | PART B |
| 7 | `C₂` (Hermitian 2nd derivative of loops) | `k(k+1) N η_u^{-(k+2)}` | merged `hermTestFunLoopN` (`LoopC2N.lean:469`): `((k(k+1):ℕ):ℝ)·size n·(etaT E u)⁻¹^(k+2)`, no `[NeZero k]`, `0 ≤ u` unused | N-exponent 1 |
| 8 | `η_u⁻¹ ≤ N^{1−τ'}/c₀`, `c₀ = √(κ(4−κ))/2` | from `RangeCond`: `N^{-1+τ'} ≤ 1−t`, `u ≤ t`, `|E| ≤ 2−κ` (`Im m = √(4−E²)/2 ≥ c₀`) | same; `RangeCond` is `sz.RangeCond τ' t` (`Green/Pins.lean:55`), `etaT` `Loop/GLoop.lean:75`, `spectralM_im`/`etaT_pos` exist | PART C (E=1/2: Im m = 0.9682 ≥ 0.8660) |
| 9 | row sum of `Ugen` kernel `S` | `(1+(1−w)⁻¹)^k ≤ (2Θ)^k`, `Θ = N^{max 0 (1−τ')}` | same bound; slot kernel `uKer d L g (cycProd (mSigma E σ) i) v w`; proof of `‖uKer‖ ≤ 1+(1−w)⁻¹` = merged private `gridAsm_norm_uKer_le` (`GridAssemblyN.lean:586`, uses public `uKer_eq_one_add`, `norm_Theta_le`, `norm_SB`, `norm_cycProd`, `norm_mSigma`) → copy; needs `0 ≤ v,w < 1`, no `v ≤ w`; `d` enters only via `g`-independent norms (`‖SB‖ = 1`) | — |
| 10 | **`P ≤ N^{C_P}`, `C_P`** | `C_P = 11 + (4k+4)θ`, `θ = max 0 (1−τ')`: `P = 2000 (S C₂)² N⁸ = 2000 A² Θ^{4k+4} N^{10}`, `A = 2^k k(k+1) c₀^{-(k+2)}`; `N⁸` from `B₈`/`P²`, `N²` from `C₂²`, `+1` absorbs `2000A²` | **unchanged**: `C_P = 11 + (4k+4)·max 0 (1−τ')` (d enters only through the symbol `N`; every moment is a polynomial in `N` with the same coefficients; item 1–9) | `N ≥ 2000A²` slack `N/(2000A²)`: 7.1·10³ at n=1 (PART C) |
| 11 | eventual threshold | `N ≥ max 1 (2000 A²)` | same; `SizeTendsto` gives it (`sz.SizeTendsto`, `Sizes.lean:173`), `RangeCond` is `∀ᶠ n` | at `k=3,κ=1`: `2000A² = 7.77·10⁷` > `N(n=0)=2.1·10⁶`: the statement is **eventual**, first good `n` is 1 |
| 12 | `YMomentsUnifN` order (target 2) | `∃ C_P` **before** `∀ K` (`AzumaProxyN:2042`) | same shape, `sz`, no `[NeZero k]`; witness is independent of `κ,E,s,t,K,σ`; threshold independent of `K` (only `k,κ,τ',N`); so `K` can be introduced after `C_P` and the proof is that of `yMomentsN` | PART E |

**`C_P` does not change** (row 10); the arithmetic is in PART B/C below.

**Consumer (iii).** Merged `AssembledN` (`GridAssemblyN.lean:227`) fixes `k, ε, D, D₁, C_P, C_K` with `D₁+4D+k+2C_P+8 ≤ C_K`, then `∀ᶠ n, ∀ K ≤ ⌈N^{C_K}⌉ …, 0 ≤ P ≤ N^{C_P}`, `v j ≤ Δ²P`, `w j ≤ Δ⁴P²`, `hY : YMomentBoundsN sz E σ u τ K Y v w` (field of `GridAssemblyHypN`, `GridAssemblyN.lean:213`); the grid `K n = ⌈N^{C_K}⌉`-type depends on `C_K`, hence on `C_P`. The merged pin `YMomentsN` has `∃ C_P` inside the `K` binder (`YMomentsConclN`, `:159`) so `C_P` may depend on `K`: circular. `YMomentsUnifN` gives `C_P` first (`C_P → C_K → K`), and the same `C_P` serves every `σ` (explicit formula). `yMomentsN_of_unif : YMomentsUnifN → YMomentsN` (`:2053`, 4-line proof) keeps the merged pin proved. RBM2D consumers: `NonAltEnd:1102` (`yMomentsUnifN … k σ`, `C_K = 100 + 2C_P` at `:1483`), `AltProxyQ:1104` (`YMomentsQUnifN`, `C_P + 2k`). No 3D file consumes `YMomentsN`/`YMomentsUnifN` yet (grep: only `GridAssemblyN`, `LoopC2N` docstrings). **No registry line**: `grep -c YMoments RBM3D/Test/Axioms.lean` = 0 (`T2154-prove.md:227`: `Axioms.lean` unchanged), so there is no line to delete.

**Ported (RBM2D `c9a24cf`, section:lines → 3D file `AzumaProxyN2.lean`, helpers prefixed `azumaProxy2_`):** §3 Gaussian moments 370-439 (private copies; 3D has them only private in `Green/RowIndep.lean:92,112` and `StepDecomp.lean`); §3 `MomentsBound8` 443-594 with `Coord→CoordF d`, `gvar→gvarF d L W g` (row 2 above, `3 ≤ L` hypothesis added), `Xentry`/`Xmat d L W`, `card_Idx`; `MomentsPath8` 600-640 (public `AzumaProxyN_integrable_normPow8_incr`, `…_integral_normPow8_incr_le`; source of the transfer: merged private `StepDecomp_transfer`, `map_incr` `Path/Walk.lean:265`, `gridTime_last` `Walk.lean:160`, `Sizes.seqP_map_slice`); §4 `YMoments` 655-804 (`indep_incr` `Walk.lean:226`; `condExp_indep_eq` is Mathlib); §5 `KernelRows` 813-912 (row 9); §6 `YFields` 931-1081; §7 `YMomentsFinal` 1096-1235 (`yMomentsN`); §10 2018-2127 (`YMomentsUnifN`, `yMomentsN_of_unif`, `yMomentsUnifN`); §11 2188-2457 (`stopW`, `YfieldsW`, five `_pub`); §8 instances 1237-1386; §8b 1388-1800. Name changes: `ukerMat L ξ`/`KLoop.mSig` → `uKer d L g (cycProd (fun i => mSigma E (σ i)) i)`; `spectralM`→`mE`/`spectralM_im` (`FlowCalculus.lean:45`); `GoodEvent_gridTime_{nonneg,le}`, `GoodEvent_gridStep_nonneg` **do not exist** in RBM3D → in-file copies (3D privates: `GridDuhamelN.lean:239-258`, `gridTime_last`); `stronglyMeasurable_YvecN` → merged public `gridAsm_stronglyMeasurable_YvecN` (`GridAssemblyN.lean:937`); `Ugen d L g E σ v w`, `stoppedEdgeN sz …` already merged (`GridDuhamelN.lean:65`, `StepDecompN.lean:198`); `stepDecompCN` needs `ι : Type`.
**Not ported:** §1 `testFun_*` and §2 `azumaSubGN` (T2159, merged); §9 statement checks/`#print axioms` (recreated as `example`s); §8c `qProxy3_pos` (already merged in T2159, `AzumaProxyN.lean:1441`) and `yMomentsN_instance_nonzero` (src 1960-1979: no consumer, so skipped). §8b is ported only at `n = 0` (T2159's `AzumaProxyNInst` already has `phi3, fsc, z1, phi3_scalar, qProxy3`); `xmu`, `xmu_Xmat` exist (`:1094,1097`). `P_ball_pos` (src 1602) already handles zero variance (Dirac at 0): in 3D `svarF` vanishes off the `S^(B)` support but `xmu μ` is `0` there and `svarF_diag > 0` (`svarF_diag`, `FineModel.lean:61`) — same proof.

### (ii) One nondegenerate instance (for targets 1-4)

`d = 3`, `sz0` (`Defs/Sizes.lean:260`), **`n = 1`** (`L=8, W=1024, N = 5.4976·10¹¹`), `κ = 1`, `E ≡ 1/2` (`|E| ≤ 1 = 2−κ`), `τ' = 1/2`, `s ≡ 0`, `t ≡ v ≡ 1/32` (`vg`), `K ≡ 4` (`Kg`, `Δ = 1/128`, `u_j = j/128`, `grid_data`), `k = 3`, `σ = (+,−,+)`, `θ = 1/2`, `C_P = 19`, `τ ≡ K n` (`{j<τ}` everything). External hypotheses: none (`sz0_tendsto`, `Sizes.lean:300`; `RangeCond` is `N^{-1/2} ≤ 31/32` iff `N ≥ 1.07`, and `sz0.size n ≥ 2.1·10⁶` (`size` is increasing in `n`; values in PART C); `Kg ≠ 0`). Nondegenerate: `Δ > 0`, `P > 0`; `yvecN_not_ae_zero` is the non-triviality of the `Y` field at `n = 0`, `j = 0`, `b = (0,0,0)` (§8b). No external hypothesis, so no limit computation (lesson 14) is needed. The eventual threshold fails at `n = 0` (`N/thr = 0.027`), which is why the instance picks `n` from the filter (`.exists`) and the numbers use `n = 1`.

Command (scratch `scratchpad/T2160/check.py`, 60 lines): `python3 check.py | grep -vE "^    g=(0.01|0.5|3.0)|bookkeeping|eta_u|Im m|PART D" | cut -c1-215`
```
PART A: sizes, N=(WL)^d, #CoordF=2N^2, gvarF<=1 (L>=3)
  n=0 L=4 W=32 N=2.0972e+06 2N^2=8.7961e+12 Delta=(t-s)/K=0.0078125
  n=1 L=8 W=1024 N=5.4976e+11 2N^2=6.0446e+23 Delta=(t-s)/K=0.0078125
  n=2 L=12 W=7776 N=8.1248e+14 2N^2=1.3202e+30 Delta=(t-s)/K=0.0078125
  brute d=3 L=3 W=1: #Idx=27=(WL)^d=27; #CoordF=1458=2(WL)^(2d)=1458
    g=0.0: row sum S^(B)=1.000000000000 (needs 3<=L: 2d=6 distinct neighbours) max svarF=1.0000
    g=1.0: row sum S^(B)=1.000000000000 (needs 3<=L: 2d=6 distinct neighbours) max svarF=0.1429
    g=50.0: row sum S^(B)=1.000000000000 (needs 3<=L: 2d=6 distinct neighbours) max svarF=0.1667
  max gvarF <= 1: True
PART B: moment constants (symbolic in N via card=2N^2)
  E|X|^2<= 16 N^4 (merged 16N^4);  E|X|^4<= 768 N^8 (merged 768N^8);  E|X|^8<= 6881280 N^16 (RBM2D 6881280)
  v-level: 2 rho^2 (768+256) N^8 = 512 (S C2)^2 D^2 N^8  <= 2000 (...) :  512.0 <= 2000
  w-level: 8 rho^4 (6881280+65536) N^16 =  3473408.0 (S C2)^4 D^4 N^16 <= 4e6 (=2000^2): True
PART C: c0=sqrt(kappa(4-kappa))/2=0.866025 theta=0.5 C_P=11+(4k+4)theta=19.0  A=2^k k(k+1)c0^-(k+2)=197.0689 threshold 2000A^2=7.7672e+07
  n=0: N=2.0972e+06 N>=thr:False  log_N P=19.248138 <= C_P=19.0: False  ratio N/thr=2.700e-02  RangeCond N^(-1/2)=6.905e-04<=1-t=0.96875: True
  n=1: N=5.4976e+11 N>=thr:True  log_N P=18.672074 <= C_P=19.0: True  ratio N/thr=7.078e+03  RangeCond N^(-1/2)=1.349e-06<=1-t=0.96875: True
  n=2: N=8.1248e+14 N>=thr:True  log_N P=18.529200 <= C_P=19.0: True  ratio N/thr=1.046e+07  RangeCond N^(-1/2)=3.508e-08<=1-t=0.96875: True
PART E: AssembledN order: k=3,eps=0.1,D=1,D1=2 -> C_P=19.0 (before K) -> C_K>=D1+4D+k+2C_P+8=55.0 -> K_n=ceil(N^C_K)
```
The script computes the constants from `#CoordF = 2N²`, not from the Lean statements; the 3D `E‖X‖²`, `E‖X‖⁴` constants `16, 768` are read from `Path/StepDecomp.lean` (`integral_normSq_incr_le`, `integral_normPow4_incr_le`). `E ω⁸ = 105 v⁴` is the Stein recursion `E x^{2p+2} = (2p+1) v E x^{2p}` (RBM2D `:391`).

### Verdicts
- Target 1 (§3-§7, `yMomentsN`): **PASS** (rows 1-11; `C_P`, `P`, thresholds unchanged; the one new `d ≥ 3` input is `gvarF ≤ 1` via `3 ≤ L`, row 2).
- Target 2 (`YMomentsUnifN`, `yMomentsN_of_unif`, `yMomentsUnifN`): **PASS**; `C_P = 11 + (4k+4)·max 0 (1−τ')` **does not change** for `N = (WL)^d` (row 10); no paper-delta needed for it.
- Target 3 (§11 `stopW`, `YfieldsW`, `_pub`): **PASS** (same constants; `[NeZero k]` dropped as in the merged pin).
- Target 4 (§8 instances, §8b `yvecN_not_ae_zero`): **PASS** at `n = 0` for §8b and at `n = 1` (from the filter) for the `YMomentsUnifN` instance; §8c: only `yMomentsN_instance_nonzero` remains, no consumer, skip.

## (b) Script output (commit below, worktree `RBM3D-wt/T2160`, branch `t/T2160`)

```
$ git log --oneline -1; git diff --stat main...t/T2160
aafa0ab T2160: ST2-35 Induction/AzumaProxyN2 (Y moments: yMomentsN, YMomentsUnifN, weighted Y fields)
 RBM3D/Induction/AzumaProxyN2.lean | 1912 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1912 insertions(+)
$ lake build RBM3D.Induction.AzumaProxyN2 > build3.out   # run 21:36:17 UTC; filtered:
ℹ [3791/3791] Built RBM3D.Induction.AzumaProxyN2 (11s)
Build completed successfully (3791 jobs).
warnings from AzumaProxyN2.lean: 0
$ lake build   # whole library in the worktree (the module is not imported by RBM3D.lean until the hub merges)
Build completed successfully (3925 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.AzumaProxyN2\n#assert_rbm_axioms\n' > audit.lean; lake env lean audit.lean
axiom audit: 4818 theorems, 1708 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 83 (borrowed 0, owed 64, structural 19).
   (same command without the AzumaProxyN2 import:)
axiom audit: 4800 theorems, 1705 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 83 (borrowed 0, owed 64, structural 19).
$ grep -c 'sorry\|admit\|native_decide' RBM3D/Induction/AzumaProxyN2.lean; grep -c '^ *axiom ' RBM3D/Induction/AzumaProxyN2.lean
0
0
$ grep 'AzumaProxyN2.lean:.*depends on axioms' build3.out | sed ... | sort | uniq -c   # #print axioms at the end of the file
  19 [propext, Classical.choice, Quot.sound]
declarations printed: AzumaProxyN_integrable_normPow8_incr AzumaProxyN_integral_normPow8_incr_le yMomentsUnifN yMomentsN_of_unif yMomentsN AzumaProxyN_stopW AzumaProxyN_YfieldsW AzumaProxyN_c0_pos_pub AzumaProxyN_inv_one_sub_le_pub AzumaProxyN_etaT_inv_le_pub AzumaProxyN_P_le_pub AzumaProxyN_rowsum_Ugen_pub AzumaProxyN2Inst.normPow8_instance AzumaProxyN2Inst.yMomentsUnifN_instance AzumaProxyN2Inst.yMomentsN_of_unif_instance AzumaProxyN2Inst.yMomentsN_instance AzumaProxyN2Inst.yfieldsW_instance AzumaProxyN2Inst.yvecN_not_ae_zero AzumaProxyN2Inst.yMomentsUnifN_instance_nonzero
```

Registry (ticket: delete the `YMomentsN` line when the pre-check passes):
```
$ grep -c 'YMoments' RBM3D/Test/Axioms.lean; git diff --stat main...t/T2160 -- RBM3D/Test/Axioms.lean | wc -l
0
       0
```

Target statements, extracted from the file by script (`extract.py stmts`):
```lean
-- AzumaProxyN2.lean:358
theorem AzumaProxyN_integrable_normPow8_incr (n j : ℕ) :
    Integrable (fun ω : PathΩ sz => ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 8) (pathP sz) :=
-- AzumaProxyN2.lean:367
theorem AzumaProxyN_integral_normPow8_incr_le (n j : ℕ) :
    ∫ ω : PathΩ sz, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 8 ∂(pathP sz)
      ≤ 6881280 * (sz.size n : ℝ) ^ 16 :=
-- AzumaProxyN2.lean:894
def YMomentsUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  sz.SizeTendsto → sz.RangeCond τ' t →
  ∀ (k : ℕ) (σ : Fin k → Bool), ∃ C_P : ℝ, 0 ≤ C_P ∧ ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsN sz (E n) σ (gridTime s t K n) τ (K n)
          (fun j ω => YvecN sz E s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)
-- AzumaProxyN2.lean:915
theorem yMomentsUnifN (κ τ' : ℝ) (E s t : ℕ → ℝ) : YMomentsUnifN sz κ τ' E s t := by
-- AzumaProxyN2.lean:980
theorem yMomentsN_of_unif {κ τ' : ℝ} {E s t : ℕ → ℝ} (h : YMomentsUnifN sz κ τ' E s t)
    (K : ℕ → ℕ) : YMomentsN sz κ τ' E s t K := by
-- AzumaProxyN2.lean:992
theorem yMomentsN (κ τ' : ℝ) (E s t : ℕ → ℝ) (K : ℕ → ℕ) : YMomentsN sz κ τ' E s t K :=
-- AzumaProxyN2.lean:1016
def AzumaProxyN_stopW (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (κ : (Fin k → Zd d (sz.L n)) → ℂ) (τ : PathΩ sz → ℕ) (ω : PathΩ sz) : ℂ :=
  {ω' | j < τ ω'}.indicator (fun ω' => ∑ c, κ c * YvecN sz E s t K n j σ ω' c) ω
-- AzumaProxyN2.lean:1025
theorem AzumaProxyN_YfieldsW (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ)
    {Smax C2 P : ℝ} (hS0 : 0 ≤ Smax) (hC20 : 0 ≤ C2) (hrow : ∑ c, ‖κ c‖ ≤ Smax)
    (hC2 : ∀ (a : Fin k → Zd d (sz.L n))
      (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), M.IsHermitian →
      y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (loopFamN sz E s t K n j σ a)) M y y‖ ≤ C2 * ‖y‖ ^ 2)
    (hP : 2000 * (Smax * C2) ^ 2 * (sz.size n : ℝ) ^ 8 ≤ P)
    (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) :
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im | filt sz j] =ᵐ[pathP sz] 0 ∧
    Integrable (fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re ^ 4) (pathP sz) ∧
    Integrable (fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im ^ 4) (pathP sz) ∧
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
    (pathP sz)[fun ω => (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => gridStep s t K n ^ 2 * P) ∧
    ∫ ω, (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).re ^ 4 ∂(pathP sz)
      ≤ gridStep s t K n ^ 4 * P ^ 2 ∧
    ∫ ω, (AzumaProxyN_stopW sz E s t K n j σ κ τ ω).im ^ 4 ∂(pathP sz)
      ≤ gridStep s t K n ^ 4 * P ^ 2 := by
```

Compiled nonempty instances (`extract.py inst`; the others by `extract.py list`: `file line: head`):
```lean
-- AzumaProxyN2.lean:1315
theorem yMomentsUnifN_instance (σ : Fin 3 → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => YvecN sz0 Einst sInst vg Kg n j σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsUnifN sz0 1 (1 / 2) Einst sInst vg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto azumaProxy2_rangeCond_vg 3 σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg azumaProxy2_Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, azumaProxy2_gridStep_pos n, hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩
```
```
1231: theorem AzumaProxyN_c0_pos_pub {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
1237: theorem AzumaProxyN_inv_one_sub_le_pub {u t τ' N : ℝ} (hut : u ≤ t) (hN0 : 0 < N)
1243: theorem AzumaProxyN_etaT_inv_le_pub {κ E u t τ' N : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
1250: theorem AzumaProxyN_P_le_pub (k : ℕ) {c0 θ N : ℝ} (hc0 : 0 < c0) (hθ : 0 ≤ θ) (hN1 : 1 ≤ N)
1258: theorem AzumaProxyN_rowsum_Ugen_pub {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {E : ℝ}
1306: theorem normPow8_instance :
1315: theorem yMomentsUnifN_instance (σ : Fin 3 → Bool) :
1329: theorem yMomentsN_of_unif_instance (σ : Fin 3 → Bool) :
1345: theorem yMomentsN_instance (σ : Fin 3 → Bool) :
1375: theorem yfieldsW_instance (κ : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) :
1412: example : 0 < Real.sqrt (1 * (4 - 1)) / 2 :=
1417: example : (1 - (1 / 4 : ℝ))⁻¹ ≤ (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) :=
1426: example : (etaT (1 / 2) (1 / 4))⁻¹ ≤ (4 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (Real.sqrt (1 * (4 - 1)) / 2) :=
1435: example : 2000 * ((2 * (32000 : ℝ) ^ (0 : ℝ)) ^ 1 *
1443: example : ∑ b : Fin 3 → Zd 3 4, ‖∏ i : Fin 3,
1800: theorem yvecN_not_ae_zero :
1860: theorem yMomentsUnifN_instance_nonzero :
1882: example {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) (K : ℕ → ℕ) :
1885: example {d : ℕ} (sz : Sizes d) (κ τ' : ℝ) (E s t : ℕ → ℝ) : YMomentsUnifN sz κ τ' E s t :=
```

Name clash, port diff-stat, section map:
```
$ python3 clash.py   # every public declaration of the file grepped as theorem/def/abbrev in RBM3D/**/*.lean
public declarations in the file: 21 ; private declarations: 71
same-named declarations elsewhere in RBM3D: 0
uses of the prefix azumaProxy2_ outside the file: 0
private declarations without the prefix azumaProxy2_: []
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/AzumaProxyN.lean
9e0f275
 RBM2D/Induction/AzumaProxyN.lean | 1140 +++-----------------------------------
 1 file changed, 71 insertions(+), 1069 deletions(-)
$ python3 extract.py sections   # section headers of AzumaProxyN2.lean (line: text)
86: /-! ## 1. Gaussian moments up to order 8 -/
156: /-! ## 2. The eighth moment of one increment: `E ‖X‖⁸ ≤ 6881280 N¹⁶`, `N = (W L)^d` -/
377: /-! ## 3. The stopped `Y` increments: moments from domination by `ρ (‖X_{j+1}‖² + m)`
540: /-! ## 4. The kernel row sums of `Ugen` (copied from the private helper `gridAsm_norm_u
608: /-! ## 5. One step, one label: the eight moment fields of `YMomentBoundsN`
806: /-! ## 6. Target: `yMomentsN`
997: /-! ## 7. The weighted `Y` fields (RBM2D `AzumaProxyN` §11, `:2188-2457`)
1268: /-! ## 8. Compiled nonempty instances (`d = 3`)
1452: /-! ## 9. `YvecN` is not a.e. zero at the instance data (RBM2D `AzumaProxyN` §8b, `:13
1874: /-! ## 10. Statement checks -/
```

Narrative (facts from the files and the tool log above):
1. Delivered: targets 1-4 in `RBM3D/Induction/AzumaProxyN2.lean` (21 public, 71 private declarations; commit `aafa0ab`; `git diff --stat main...t/T2160` lists only this file; builds and scratch audit run 21:36 UTC by `date -u`).  `Test/Axioms.lean` is untouched.
2. Ports from RBM2D `Induction/AzumaProxyN.lean` at `c9a24cf` (src line -> section above): §3 Gaussian moments 370-439 -> §1; `MomentsBound8`, `MomentsPath8` 443-640 -> §2; §4 655-804 -> §3; §5 813-912 -> §4; §6 931-1081 -> §5; §7 1096-1235 and §10 2018-2127 -> §6; §11 2188-2457 -> §7; §8 1237-1386 -> §8; §8b 1388-1800 -> §9.  Not ported: §1-§2 (`testFun_*`, `azumaSubGN`: T2159), §8c `qProxy3_pos` (merged in T2159) and `yMomentsN_instance_nonzero` (replaced by `yMomentsUnifN_instance_nonzero`, no consumer).  RBM2D `HEAD` differs from `c9a24cf` in this file (diff-stat above); every port is from `c9a24cf`; nothing from RBM1D.
3. Exponents: `C_P = 11 + (4k+4)·max 0 (1-τ')` does not change for `N = (W L)^d`.  The proof has the same arithmetic as RBM2D: `E‖X‖² ≤ 16N⁴` and `E‖X‖⁴ ≤ 768N⁸` (merged `integral_normSq_incr_le`, `integral_normPow4_incr_le`), `E‖X‖⁸ ≤ 6881280 N¹⁶` (new, `azumaProxy2_integral_normPow8_le`, from `#CoordF = 2N²` = `azumaProxy2_card_Coord` and `E ω⁸ = 105 v⁴ ≤ 105`), `C₂ = k(k+1)Nη⁻ᵏ⁻²` (merged `hermTestFunLoopN`), `P = 2000 (S C₂)² N⁸ ≤ N^{C_P}` (`azumaProxy2_P_le`, same statement as RBM2D `AzumaProxyN_P_le` with `N` a real variable).  The one new `d ≥ 3` input is `gvarF ≤ 1` from `3 ≤ L` (`azumaProxy2_gvarF_le_one`, copy of the merged private lemma `StepDecomp_gvar_le_one`), used with `sz.three_le_L n`.
4. Dictionary: `d : Sizes` -> `sz : Sizes d`, `Z2 (d.L n)` -> `Zd d (sz.L n)`, `Coord/gvar/P/Xmat` -> `CoordF/gvarF/PF/Xmat d L W`, `ukerMat/KLoop.mSig` -> `uKer d L g (cycProd (fun i => mSigma E (σ i)) i)`, `spectralM` -> `mE`, `[NeZero k]` dropped as in the merged pin.  `GoodEvent_gridTime_*` do not exist: in-file copies `azumaProxy2_gridTime_nonneg/_le`, `azumaProxy2_gridStep_nonneg`.  `AzumaProxyN_*` public names are RBM2D's (grepped: no clash, no `azumaProxy2_` use outside the file).
5. `YMomentsUnifN` is the RBM2D pin (docstring ported) with `sz.SizeTendsto`, `sz.RangeCond`, no `[NeZero k]`; `C_P` is chosen before `∀ K`.  `yMomentsN` is `yMomentsN_of_unif sz (yMomentsUnifN …) K` (RBM2D proves the two separately); the merged pin `YMomentsN` of `GridAssemblyN.lean:173` is not changed.
6. Instances at `sz0`, `E ≡ 1/2`, `(s, t, K) = (0, 1/32, 4)` (`Δ = 1/128`), `k = 3`, `τ' = 1/2`: the eventual statements are applied at an `n` obtained from the filter (`Filter.Eventually.exists`); `RangeCond (1/2) vg` is proved in the file (`azumaProxy2_rangeCond_vg`, `N ≥ 4`), `SizeTendsto` is the merged `sz0_tendsto`; no hypothesis is left open.  (a) records that the eventual threshold fails at `n = 0` (PART C), so the instance cannot be placed at `n = 0`.  `yfieldsW_instance` is at `n = 0`, `j = 0`, every weight vector `κ`, with `C₂` from `hermTestFunLoopN`.  The five `_pub` helpers have `example`s (lines 1412-1443).
7. `yvecN_not_ae_zero` is proved for every size index `n` (preflight planned `n = 0` only), with the `d = 3` ingredients: `W^{-2d}` profile through the merged `azumaProxy_loop3_scalar` (T2159), `AvecN = loopFine - STKloop` (constant `𝒦`) in place of RBM2D's `Kcal`, `svarF_diag > 0` in place of `svar_diag_pos`.  `yMomentsUnifN_instance_nonzero` combines it with the moment bounds at the same `n`.
8. Registry: `grep -c YMoments RBM3D/Test/Axioms.lean` is 0, so there is no line to delete; the scanner finds the same 83 premises with and without the module (no new unclassified premise; `YMomentsN`, `YMomentsUnifN` are proved by `yMomentsN`, `yMomentsUnifN`).
9. Section (a) is not edited; the file:line citations of (a) that I used (`StepDecomp.lean:448,475,699,708`, `Walk.lean:160,226,265`, `GridAssemblyN.lean:586`, `Sizes.lean:157`) match the files, so there is no (a′).

## (c) Verified Mathlib names used
```
$ lake env lean names.lean   # 45 `#check @name` lines; errors: 1
```
Verified present (`#check @name`, all elaborate): `memLp_id_gaussianReal'`, `integrable_withDensity_iff_integrable_smul'`, `gaussianPDF_lt_top`, `gaussianReal_zero_var`, `gaussianReal_of_var_ne_zero`, `ProbabilityTheory.gaussianReal_absolutelyContinuous'`, `integral_dirac`, `pow_sum_le_card_mul_sum_pow`.
Verified present: `MeasureTheory.condExp_indep_eq` (needs `import Mathlib.Probability.ConditionalExpectation`), `condExp_indicator`, `ContinuousLinearMap.comp_condExp_comm`, `condExp_mono`, `condExp_finsetSum`, `condExp_smul`, `condExp_congr_ae`, `integral_mono_ae`, `ae_map_iff`, `measure_mono_null`, `integral_map`, `integrable_map_measure`.
Verified present: `Real.rpow_le_rpow_of_nonpos` (`0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z`), `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_neg`, `Real.rpow_natCast`, `Fintype.prod_sum`, `Finset.prod_univ_sum`, `Finset.measurable_sum`, `measurable_const_smul`.
Verified present: `MeasureTheory.Measure.infinitePi_eq_pi`, `ball_pi`, `Measure.pi_pi`, `Measure.dirac_apply'`, `Metric.eventually_nhds_iff`, `ContinuousAt.eventually_ne`, `tendsto_nhds_unique`, `Filter.tendsto_inv₀_cobounded`, `tendsto_norm_atTop_iff_cobounded`, `Matrix.cstar_norm_def`, `Matrix.toEuclideanCLM`, `PiLp.norm_single`, `norm_indicator_le_norm_self`, `Complex.abs_re_le_norm`, `Nat.cast_pos`.
Verified absent (`Unknown constant`): `Real.rpow_le_rpow_of_exponent_nonpos`.

## (d) Open issues and paper-delta candidates
- `T2160a` (Lean-only construction, no paper statement): the paper bounds the martingale term by BDG (`3_5:166`, `3_5:216`); the Lean grid walk has the second-order remainder `Y` and its moment pins `v_j = Δ²P`, `w_j = Δ⁴P²`, `P ≤ N^{C_P}`, proved with the explicit `C_P = 11 + (4k+4)·max 0 (1-τ')` (same constant as RBM2D, narrative 3).  RBM2D records the same difference as its own T2160a, T2160b (#118, #119; RBM2D `AzumaProxyN.lean:76-78` at `c9a24cf`).
- `T2160b` (necessary condition, same as T2001a): the bound `E ω_c⁸ ≤ 105` uses `gvarF ≤ 1`, which needs `3 ≤ L` (`sum_sbKernelR`); stated as `sz.three_le_L n`.
- `T2160c` (statement shape, not a paper difference): `YMomentsUnifN` (C_P before the grid `K`) is the form `AssembledN` can consume; the merged `YMomentsN` (`∃ C_P` inside the `K` binder) is kept and derived (`yMomentsN_of_unif`).
- Open: none for this ticket.  The consumers of `YMomentsUnifN` (the order `C_P → C_K → K` of `AssembledN`) are later tickets; no 3D file consumes it yet (`grep -rl YMoments RBM3D` lists `GridAssemblyN`, `LoopC2N` and this file).
