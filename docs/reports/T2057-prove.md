Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 13:51:38 UTC 2026

Targets (mathematics only). **A** `norm_avgErr_le` (EntryBlock:594): with `S = svar d L W g` on `Vtx d L W` (`g = lam`), `3 ≤ d`, `3 ≤ L`,
`0 < g ≤ Λ`, `|E| ≤ 2-κ`, `0 ≤ u < 1`: `|avgErr_a| ≤ B' + K (A+B)`, `K = Kstab3 d Λ κ` (inputs `hIBP`: A, `hFA`: B, `hFA'`: B').
**B** `avg_bound_stochDom` (EntryDom:696, `(GavLGEX)` 3_5:33): `GavLDetSeq` from `hIBP`, `hFArow`, `hFAblk` (each `≺ max 𝓛`) and `LoopDetSeq` (`max 𝓛 ≺ Ψ²`).
Paper 3_5:37 says the proof is dimension-independent (resolvent identities and LDE). `N = (WL)^d = sz.size`, block fibre `Fin (W^d)`.

### (i) Exponent table

Part 1. Each `d = 2` occurrence by statement (RBM2D at `c9a24cf`). Script `tokgroup.py` (code text, comments stripped) gives EntryBlock
`W⁻²`-type 12, `Z2/zdist2` 81, `1/5,1/25` 8, `L²` 1; EntryDom `W⁻²` 2, `Z2/zdist2` 12, `L²` 1. The portmap row gave 18 / 82 (its regex is not reproduced here).
```
$ python3 tokgroup.py   (git show c9a24cf; keys W-2, L2, Z2/zd2, 1/5+1/25; groups by declaration)
== EntryBlock total {'W-2': 12, 'L2': 1, 'Z2/zd2': 81, '1/5,1/25': 8}
  sb kernel/profile (Sblk2,sbKre2, sums) {'W-2': 6, 'L2': 0, 'Z2/zd2': 48, '1/5,1/25': 8} decls 23
  loop sums {'W-2': 0, 'L2': 0, 'Z2/zd2': 3, '1/5,1/25': 0} decls 1
  lower bounds / (4.3) {'W-2': 4, 'L2': 1, 'Z2/zd2': 6, '1/5,1/25': 0} decls 2
  blkCoef2 / (4.5) {'W-2': 2, 'L2': 0, 'Z2/zd2': 9, '1/5,1/25': 0} decls 9
  checks {'W-2': 0, 'L2': 0, 'Z2/zd2': 15, '1/5,1/25': 0} decls 4
== EntryDom total {'W-2': 2, 'L2': 1, 'Z2/zd2': 12, '1/5,1/25': 0}
  other {'W-2': 1, 'L2': 1, 'Z2/zd2': 10, '1/5,1/25': 0} decls 7
  checks {'W-2': 1, 'L2': 0, 'Z2/zd2': 2, '1/5,1/25': 0} decls 2
```

| RBM2D statement (line) | `d = 2` token | `d ≥ 3` replacement and why it holds |
|---|---|---|
| `sbKre2` (:90), `Sblk2` (:95), `sum_sbKre2*`, `sum_Sblk2_row/col` (:183,:194) | `1/5` on `zdist2 ≤ 1`; `(W⁻¹)²`; fibre `Fin W × Fin W` | **No `Sblk2`**: the profile is the merged `svar d L W g x y = (W^d)⁻¹ SBR d L g x.1 y.1` (Gauss/Model.lean:63), kernel `a = (1+2dg²)⁻¹` at 0, `g²a` on `zdistD = 1` (Defs/Block.lean). `Σ_u kernel = a + 2d g²a = 1` (`sum_sbKernelR`, `card_nbhd`, `3 ≤ L`); `Σ_{b,β} S = W^d (W^d)⁻¹ Σ_b SB = 1`; symmetric (`svar_comm`) |
| `sbKre2_le` (≤ 1/5), `Sblk2_le`, `Sblk2_le_ind`, `sbKre2_le_ind` | `1/5`, `W⁻²` | `sup SB = max(1,g²)/(1+2dg²) ≤ 1` (g²a ≤ 1/(2d)); `S ≤ (W^d)⁻¹ 1(supp)` |
| (4.2) `sbKre2_mul_mul_le`, `sum_sum_Sblk2_le_gexRHS`, `Sblk2_le_gexRHS_ind`, `offSq_le_gexRHS_blk` (:351,:376,:390,:406) | `zdist2 ≤ 1` is the `ℓ¹` ball (5 points) | merged `gexRHS` uses `zdistInf d L ≤ 1` (cube, Defs/Sizes.lean:115); `supp SB ⊂ {zdistD ≤ 1}` and `zdistInf ≤ zdistD` (Sizes.lean:117), so the indicator dominates. Constant 81 unchanged (`SB ≤ 1`). Second term `S_pq ≤ (W^d)⁻¹ 1(zdistInf(q.1-p.1) ≤ 1)` is the second term of `gexRHS` |
| `sum_sbKre2_sub_mul(')`, `sum_sum_Sblk2_eq_nbr` (:140,:153,:283, `1/25`) | uniform weight `(1/5)²` | false at general `g` (weights `a`, `g²a`); **drop all three** (git grep at `c9a24cf`: 0 uses outside the two files, see (ii)) |
| `Sblk2_eq_svar`, `stable_relabel`, `stable_Sblk2_bulk` (:215,:226,:241) | `Kstab2 κ L` | drop (the profile is `svar`); stability is merged `stable_svar_bulk_vtx` (Stability.lean:320, `3 ≤ d`, `0<g`, `g ≤ Λ`), constant `Kstab3 d Λ κ`, no `L` |
| `inv_W2_le_maxLoopPM` (:430) | `(W⁻¹)² ≤ 4 maxLoop` | `(W^d)⁻¹ ≤ 4 maxLoopPM`: `loop(0,0) = (W^d)⁻² Σ_{β,α}|G|²` (`norm_loopPM_eq`, Pins.lean) `≥ (W^d)⁻² W^d / 4`, diagonal `|G_ii| ≥ 1/2` from `δ ≤ 1/2` |
| `Sblk2_le_maxLoopPM`, `diagSq_le_maxLoopPM_blk` (:461,:477) | `S ≤ (1/5)W⁻² ≤ 2 maxLoop`, result `2160 K²Φ²(2 maxLoop)` | `S ≤ (W^d)⁻¹ ≤ 4 maxLoopPM`; take `Λ = 4 maxLoopPM`: result `2160 K3² Φ² (4 maxLoopPM)`. **Residual difference** (constant 2 → 4): the proof route keeps only `(W^d)⁻¹ ≤ 4 maxLoopPM`, while `sup SB → 1` as `g → 0` (see (ii)) and `WO` allows `lam → 0` (`sz0`). Paper-delta candidate T2057a. `ΣΣ S|G|²S ≤ maxLoop ≤ Λ` as before (rows of `SB` sum to 1) |
| `blkCoef2` (:509), `abs_/sum_abs_/sum_blkCoef2`, `trace_sub_mul_Eblk2`, `avgErr_eq_sum_blkCoef2` | `W⁻² 1(k ∈ 𝓘_a)` | `(W^d)⁻¹ 1(k.1 = a)`; `Σ_k = W^d (W^d)⁻¹ = 1` (`Eblk d L W a` is diagonal, Loop/GLoop.lean:55) |
| `norm_trace_green_sub_mul_Eblk2_le`, `norm_avgErr_le` (:574,:594) | `Kstab2 κ L` | `Kstab3 d Λ κ`, extra hyps `3 ≤ d`, `0 < g`, `g ≤ Λ`; `‖u m²‖ = u ≤ 1`; conclusion `B' + K(A+B)` unchanged |
| EntryDom `card_z2` (:192), `card_z2_le` (:202), `card_z2_sq_le` (:206), `card_idx_sq`, `card_offPair_le` | `L²`, `L² ≤ N`, `L⁴ ≤ N²` | `L^d`; `L^d ≤ N` (slack `W^d`); `L^{2d} ≤ N²` (slack `W^{2d}`); `|Idx|² = N²` (`card_Idx`); `|OffPair| ≤ N²`; `|BlockIndex| = N`. All counted in `N`, so the grid exponents `m` are dimension-free |
| EntryDom `eventually_Kstab2_le_rpow`, `…const_kstab2_sq_le`, `…one_add_two_kstab2_le` | `Kstab2 ~ 1 + log L ≤ N^ε` | `K3` is an `n`-independent real: `1+2K3 ≤ N^ε` and `8640 K3² ≤ N^ε` hold eventually from `N → ∞` alone; `K3 W^{-c} ≤ 1/2` is `eventually_Kstab3_mul_rpow_le`. Simpler than `d = 2` (no `log L`, no `Bandwidth` for the constant) |
| hypotheses `SizeTendsto`, `Bandwidth 𝔠`, `h𝔠` | | `sz.Admissible 𝔠 𝔡` plus `3 ≤ d`; `WO` gives `0 < lam n ≤ 𝔡⁻¹` eventually, so `Λ = 𝔡⁻¹`; `Bandwidth` is still used for `δ = W^{-c} ≤ N^{-𝔠c}` and `goodSet (c/2)` |

D40: the one-orientation `gexRHS … [q] [p]` holds at `d ≥ 3`. `Σ_{k,l} S_{pk}|G_kl|²S_{lq} = Σ_{a',b'} SB_{[p]a'} SB_{b'[q]} ‖𝓛(b',a')‖` (`norm_loopPM_eq`: rows block `b`, columns block `a`), and each term is `≤` the `(a',b')` term of `gexRHS … [q] [p]`. The stop condition is not triggered.

Part 2. Constants and thresholds.

| quantity | value | constraint | slack |
|---|---|---|---|
| `Φ`-power `k` | 2 (4.2), 2 (4.3), 1 (4.5) | `τ' = min(τ/(2(k+1)), c₀)`: `τ'k ≤ τ/2`, `τ' ≤ c₀` | `c = 1/2`, `𝔠 = 1/6`, `τ = 1`, `k = 2`: `τ' = 1/12`, `τ'k = 1/6 ≤ 1/2` |
| `δ_n = W^{-c}`, `c₀ = 𝔠c` | (4.5): `δ ≡ 0`, `c₀ = 1` | `δ ≤ N^{-c₀}` (Bandwidth `N^𝔠 ≤ W`); `36 Φ δ² ≤ 1` for `Φ = N^{τ'}`, `τ' ≤ c₀` | `36 N^{-c₀} ≤ 1` for `N ≥ 36^{1/c₀}` |
| constants | 81, `8640 K3²` (was `4320 K2²`), `1 + 2 K3` | `≤ N^ε` eventually, all `ε > 0` | script: `8640 K² ≤ N^0.1` first at `n = 884` (K=10) |
| `hKδ` | `K3 W^{-c} ≤ 1/2` | `W → ∞` | `K = 10`, `c = 1/2`: first `n = 1` |
| `Ω(t, c/2)` from `AsGMcSeq c` | `N^{𝔠c/2} W^{-c} ≤ W^{-c/2}` | Bandwidth | ratio `0.771` at `n = 0` (0.324 vs 0.420) |
| `Ψ ≤ N^{-a}` for `Ψ² = (W^d)⁻¹` | `a = 1/4`, `Ψ = W^{-3/2}` | `N ≤ W^6` (`L ≤ W`) | `5.5e-3 ≤ 2.6e-2` at `n = 0` |
| `Λ`, `S` bound | `Λ = 4 maxLoopPM`, `S ≤ (W^d)⁻¹` | `(W^d)⁻¹ ≤ 4 maxLoopPM` | sample: `0.1250 ≤ 0.6183` (ratio 0.2022) |
| `K` | `Kstab3 d 𝔡⁻¹ κ` | `3 ≤ d`, `0 < g ≤ 𝔡⁻¹`, `\|E\| ≤ 2-κ`, `‖ξ‖ = u < 1` | sample `K_num = 1.625 ≤ 1 + max_a Σ_b\|Θ_ab\| = 2.556` |

### (ii) One concrete nondegenerate instance

Block sample for **A** (`d = 3`, `L = 4`, `W = 2`, `N = 512`, `g = 1`, `E = 0`, `κ = 1`, `u = 1/2`, `Λ = 1`; `m = i`, `z_u = (1-u)m = i/2`).
`K_num = ‖(1 - u m² S)⁻¹‖_{max→max}` is the least admissible `Stable` constant; the merged theorem gives `K_num ≤ Kstab3`, and the bound is monotone in `K`.
`Kstab3` itself is not computed. `x` is `u m² S (G_kk - m)` plus noise of size `0.01/√N`.
```
$ cd <scratchpad>/T2057 && python3 inst.py
S^(B): row sums min/max 0.9999999999999999 0.9999999999999999 | symmetric True | nonzeros per row 7 7 | a=b entry 0.14285714285714285
N = 512 | S row sums min/max 0.9999999999999998 0.9999999999999998 | (max S)*W^d = 0.14285714285714285
m = 1j | z_t = 0.5j | |E| <= 2-kappa: True
delta = ||G-m||_max = 0.3686  (<= 1/2: True)
maxLoopPM = 1.545723e-01 | W^-d = 0.1250 | W^-d/(4 maxLoop) = 0.2022 (<=1: True) | max S = 0.01786
|xi| = 0.500 (<=1) | K_num = ||(1-xi S)^-1||_{max->max} = 1.625198 | 1+max_a sum_b|Theta_ab| = 2.555556 | K_num <= 1+KTheta: True
A = 1.633e-03  B = 5.024e-02  max_a B'_a = 9.577e-02
max_a |avgErr_a| = 9.036e-02 | min_a [B'_a + K_num (A+B)] = 8.558e-02 | all a: lhs <= rhs: True | min slack = 7.630e-02
Stable(K_num) spot check: max|v| = 0.3056 <= K_num*B = 0.4876 : True
g = 1.00000 : max S^(B) entry = 0.14286
g = 0.01562 : max S^(B) entry = 0.99854
g = 0.00000 : max S^(B) entry = 1.00000
t=0: maxLoopPM = 0.125000 = W^-d = 0.125000 ; off-diagonal loops max = 0.0e+00 ; avgErr = 0.0e+00
```
Every hypothesis of **A** holds at this sample (`3 ≤ 3`, `3 ≤ 4`, `κ = 1 > 0`, `|0| ≤ 1`, `0 ≤ 1/2 < 1`, `0 < 1 ≤ Λ`, `hIBP/hFA/hFA'` with the printed `A, B, B'`), and the conclusion is nonvacuous: `max_a |avgErr_a| = 0.0904`, the right side is `≥ 0.0856` on every block, per-block slack `≥ 0.0763`.
`δ = 0.369` exceeds `1/6`, so this sample is not an instance of the deterministic (4.2)/(4.3) lemmas (`36Φδ² ≤ 1` at `Φ = 1`). Their instance is the `u = 0` point (`δ = 0`, last line).

Sequence level for **B**: `sz0` (Defs/Sizes.lean:260; `sz0_admissible : sz0.Admissible (1/6) (1/10)` at :331), `d = 3`, `κ = 1/2`, `E ≡ 0`, `t ≡ 1/2`.
Limit computation (external hypotheses `Admissible`, `WO`, `Bandwidth`, grid counts, `Ψ`):
```
$ cd <scratchpad>/T2057 && python3 seq.py
n=    0 L=     4 W=3.200e+01 N=2.097e+06 lam=1.562e-02 | N^(1/6)<=W:True | W^(-3/2+1/10)=7.81e-03<=lam<=10:True | L^d<=N, L^2d<=N^2:True | L^2d/N^2=9.31e-10 (=W^-2d)
n=   10 L=    44 W=5.154e+06 N=1.166e+25 lam=8.820e-09 | N^(1/6)<=W:True | W^(-3/2+1/10)=4.01e-10<=lam<=10:True | L^d<=N, L^2d<=N^2:True | L^2d/N^2=5.34e-41 (=W^-2d)
n=10000 L= 40004 W=3.202e+21 N=2.101e+78 lam=1.562e-26 | N^(1/6)<=W:True | W^(-3/2+1/10)=7.81e-31<=lam<=10:True | L^d<=N, L^2d<=N^2:True | L^2d/N^2=9.29e-130 (=W^-2d)
  K=1e+01: first n with 1+2K<=N^0.1: 2 ; 8640K^2<=N^0.1: 884 ; K W^-1/2<=1/2: 1
  K=1e+03: first n with 1+2K<=N^0.1: 30 ; 8640K^2<=N^0.1: 194581 ; K W^-1/2<=1/2: 10
(4.5) GavLDetSeq (delta=0, c0=1)   k=1: tau'=min(tau/(2(k+1)),c0) satisfies tau' k <= tau/2, tau'<=c0 for tau in {1/10,1,10}; c0=1
n=    0: Psi=W^-3/2=5.524e-03 <= N^-1/4=2.628e-02 : True
n=10000: Psi=W^-3/2=5.520e-33 <= N^-1/4=2.627e-20 : True
```
(Lines for the (4.2), (4.3) exponents and the `n = 5, 100` rows of the `Ω(t,c/2)` check are in the full output; omitted here for length.)
At `t ≡ 0` (`H = 0`, `G = m 1`, last line of `inst.py`: `maxLoopPM = W^-d`, `avgErr = 0`) all four stochastic inputs of **B** hold with `x ≡ 0`, `Ψ_n = W_n^{-3/2}`, `a = 1/4` (RBM2D `check_avg_zero`, EntryDom:1011).
At `t ≡ 1/2` the inputs `hIBP`, `hFArow`, `hFAblk`, `hLoop` are other gates' pins and stay hypotheses of the example.
Name evidence (git grep `-w` at `c9a24cf`, files other than EntryBlock/EntryDom): `sum_sum_Sblk2_eq_nbr` 0, `sum_sbKre2_sub_mul` 0, `stable_Sblk2_bulk` 0, `abs_blkCoef2_le` 0, `Sblk2_eq_svar` 12 (it is replaced by the merged `svar`).

### Verdicts
- **A `norm_avgErr_le`: PASS.** The statement closes with `svar`, `Kstab3 d Λ κ`, `3 ≤ d`, `0 < g ≤ Λ`.
- **B `avg_bound_stochDom`: PASS.** `k = 1`, `δ ≡ 0`, grid `N` or `L^d ≤ N`, `K3` constant; hypotheses `sz.Admissible 𝔠 𝔡` plus `3 ≤ d`.
- `goodSet`, `blkCoef2`, `sum_blkCoef2` (public per portmap P.3): PASS, with `(W^d)⁻¹` and `Fin (W^d)`.
- D40 (one-orientation `gexRHS`): holds, no switch to `STgexRHS`.
- Statement differences for the prover to report as paper-delta candidates: (1) the constant `2 maxLoopPM → 4 maxLoopPM` in `diagSq_le_maxLoopPM_blk`, and `4320 → 8640` in the `diag` ≺ step; (2) `zdist2 ≤ 1` → `zdistInf ≤ 1` in `gexRHS`-facing bounds. Recommend dropping `sum_sbKre2_sub_mul(')`, `sum_sum_Sblk2_eq_nbr`, `Sblk2_eq_svar`, `stable_relabel`, `stable_Sblk2_bulk`.

## (b) Script output — Sat Oct  3 14:28:26 UTC 2026
Commit and scope (branch `t/T2057`):
```
$ git log --oneline -1; git diff --name-only main...t/T2057
d8fe7c5 T2057: S1-16 Green/EntryDom: block-average error (4.5) and the ≺ layer of lem_GbEXP at d ≥ 3
RBM3D/Green/EntryDom.lean
$ wc -l RBM3D/Green/EntryDom.lean; grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/Green/EntryDom.lean
    1628  lines;  forbidden-token count = 0
$ lake build RBM3D.Green.EntryDom   (its olean was removed first, so the module is rebuilt)
✔ [3320/3320] Built RBM3D.Green.EntryDom (14s)
Build completed successfully (3320 jobs).
$ lake build   (full library, root #assert_rbm_axioms; the root does not import the new module before merge)
Build completed successfully (3751 jobs).
```
`#print axioms` of all 36 public declarations of the file (`axioms_all.lean`, `import RBM3D.Green.EntryDom`):
```
35 declarations: [propext, Classical.choice, Quot.sound]; others: OffPair depends on axioms: [propext]
'RBM.Green.norm_avgErr_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.avg_bound_stochDom' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Target statements (`extract.py`: text of the file from the declaration to its `:=`):
```lean
-- RBM3D/Green/EntryDom.lean:573
theorem norm_avgErr_le (hd : 3 ≤ d) (hL : 3 ≤ L) {g Λ : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    {E κ u : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (x : Vtx d L W → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - (u : ℂ) * mE E ^ 2 *
      ∑ k, (svar d L W g i k : ℂ) * (greenBlk d L W E u M true k k - mE E)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (svar d L W g i k : ℂ) *
      ((greenBlk d L W E u M true k k - mE E) - x k)‖ ≤ B) (a : Zd d L)
    (hFA' : ‖∑ k, (blkCoef2 d L W a k : ℂ) *
      ((greenBlk d L W E u M true k k - mE E) - x k)‖ ≤ B') :
    ‖avgErr d L W E u M true a‖ ≤ B' + Kstab3 d Λ κ * (A + B) :=
-- RBM3D/Green/EntryDom.lean:1192
theorem avg_bound_stochDom {κ 𝔠 𝔡 : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hA : sz.Admissible 𝔠 𝔡)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n < 1)
    (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ)
    (hIBP : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖x n ω i - (t n : ℂ) * mE (E n) ^ 2 *
        ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
          (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
            mE (E n))‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)))
    (hFArow : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
        ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
          mE (E n)) - x n ω k)‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)))
    (hFAblk : sz.PrecPT (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖∑ k, (blkCoef2 d (sz.L n) (sz.W n) a k : ℂ) *
        ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
          mE (E n)) - x n ω k)‖)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)))
    {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq sz E t Ψ) :
    GavLDetSeq sz E t Ψ :=
-- RBM3D/Green/EntryDom.lean:484
noncomputable def blkCoef2 (d L W : ℕ) (a : Zd d L) (k : Vtx d L W) : ℝ :=
-- RBM3D/Green/EntryDom.lean:507
theorem sum_blkCoef2 [NeZero L] [NeZero W] (a : Zd d L) : ∑ k, blkCoef2 d L W a k = 1 :=
-- RBM3D/Green/EntryDom.lean:688
def goodSet {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (c : ℝ) (n : ℕ) : Set sz.SeqΩ :=
```
Compiled nonempty instances in the same file (`example`s, compiled by the `lake build` above):
```lean
-- :1345  norm_avgErr_le at sz0, n = 0 (d=3, L=4, W=32, g = lam 0 = 1/64 <= Lambda = 10), E=0, kappa=1, u=1/2, M=0, x = -i/2, A=0, B=B'=3/2
example (a : Zd 3 4) :
    ‖avgErr 3 4 32 0 (1 / 2) 0 true a‖ ≤ 3 / 2 + Kstab3 3 10 1 * (0 + 3 / 2) := by
  refine norm_avgErr_le (d := 3) (L := 4) (W := 32) (g := 1 / 64) (Λ := 10) (E := 0) (κ := 1)
    (u := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) 0 (fun _ => -(Complex.I / 2)) (A := 0) (B := 3 / 2)
    (B' := 3 / 2) ?_ ?_ a ?_
-- :1370  nondegeneracy:  ‖avgErr‖ = 1  and  3 ≤ 3/2 + Kstab3 3 10 1 * (0 + 3/2)
-- :1426  avg_bound_stochDom at sz0, t ≡ 0, E ≡ 0, kappa = 1: hIBP, hFArow, hFAblk, hLoop all proved
example : GavLDetSeq sz0 (fun _ => 0) (fun _ => 0)
    (fun n => Real.sqrt ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹)) := by
  refine avg_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 0) (fun n => by norm_num) (fun n => le_rfl)
    (fun n => by norm_num) (fun _ _ _ => 0) ?_ ?_ ?_ entryDom_loopDet_zero
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n u ω => ?_) (fun n u ω => maxLoopPM_nonneg _ _ _)
-- :1503  avg_bound_stochDom at t ≡ 1/2 (hIBP, hFArow, hFAblk: section variables, hLoop: argument; the rest is discharged)
example {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) Ψ) :
    GavLDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) Ψ :=
  avg_bound_stochDom sz0 (κ := 1) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) one_pos
    sz0_admissible (E := fun _ => 0) (t := fun _ => 1 / 2) (fun n => by norm_num)
    (fun n => by norm_num) (fun n => by norm_num) x hIBP hFArow hFAblk hLoop
```
Other instances: `entry_bound_stochDom` (:1487), `diag_bound_stochDom` (:1494) at `t ≡ 1/2` (LDE inputs as hypotheses); both at `t ≡ 0` with every hypothesis proved (:1580); `offSq_le_gexRHS_blk`, `diagSq_le_maxLoopPM_blk` at `u = 0` (:1549, :1561).
Statement diff against RBM2D `c9a24cf` (`classify.py`: RBM2D statement text, renamed by `stmtdiff.py` rules, token-diffed against the RBM3D statement):
```
31 ported statements compared; 100 residual token differences, 59 of them the renaming R1-R3 (explicit `d`/`sz` argument, `g` of the profile)
  offSq_le_gexRHS_blk: replace: RBM2D[offSq] -> RBM3D[( if p = q then 0 else ‖greenBlk d]
  offSq_le_gexRHS_blk: insert: RBM2D[] -> RBM3D[true]
  offSq_le_gexRHS_blk: replace: RBM2D[q] -> RBM3D[q‖ ^ 2 )]
  diagSq_le_maxLoopPM_blk: replace: RBM2D[{κ] -> RBM3D[{g Λ κ]
  diagSq_le_maxLoopPM_blk: insert: RBM2D[] -> RBM3D[( hg : 0 < g ) ( hgΛ : g ≤ Λ )]
  diagSq_le_maxLoopPM_blk: replace: RBM2D[2] -> RBM3D[4]
  svar_le_maxLoopPM: replace: RBM2D[Sblk2_le_maxLoopPM] -> RBM3D[svar_le_maxLoopPM ( hL : 3 ≤ L )]
  svar_le_maxLoopPM: insert: RBM2D[] -> RBM3D[g : ℝ ) (]
  svar_le_maxLoopPM: replace: RBM2D[2] -> RBM3D[4]
  sum_sum_svar_eq: replace: RBM2D[sbKre2] -> RBM3D[sbKernelR d]
  sum_sum_svar_eq: insert: RBM2D[] -> RBM3D[g]
  sum_sum_svar_eq: replace: RBM2D[sbKre2] -> RBM3D[sbKernelR d]
  sum_sum_svar_eq: insert: RBM2D[] -> RBM3D[g]
  norm_trace_green_sub_mul_Eblk2_le: insert: RBM2D[] -> RBM3D[) {g Λ : ℝ} ( hg : 0 < g ) ( hgΛ : g ≤ Λ]
  norm_avgErr_le: insert: RBM2D[] -> RBM3D[) {g Λ : ℝ} ( hg : 0 < g ) ( hgΛ : g ≤ Λ]
  plus, in the sequence theorems: `𝔡` added, `h𝔠 : 0 < 𝔠) (hsz …) (hbw …)` -> `hA : sz.Admissible 𝔠 𝔡` (8 statements), `hd : 3 ≤ d` added where Kstab3 is used
```
d = 2 token scan of the code (comments stripped; `d2scan.py`), RBM2D `EntryBlock`+`EntryDom` at `c9a24cf` against this file:
```
token group                                                RBM2D(c9a24cf)  RBM3D
Z2 / zdist2                                                      93          0
BlockIndex                                                       68          0
Sblk2 / sbKre2 / sbSupport                                      148          0
W^2, W⁻² (fibre Fin W x Fin W, ((W:R)⁻¹)^2, W^2)                 28          0
L^2, L^4 (grid counts)                                            4          0
1/5, 1/25 (profile weight)                                        8          0
Kstab2 / eventually_Kstab2                                       21          0
spectralM / spectralZ                                            55          0
Sizes (d : Sizes) / d.L n / d.W n / d.size                      439          0
Instance / SizeTendsto d / Bandwidth d                           26          0
```
Name-clash grep and RBM2D diff-stat:
```
$ for n in $(cat pubnames.txt); do git grep -w -l "$n" main -- RBM3D RBM3D.lean; done   (36 public names)
files containing any of the 36 new public names on main: 0
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/EntryBlock.lean RBM2D/Green/EntryDom.lean   (RBM2D HEAD = 9e0f275)
 RBM2D/Green/EntryBlock.lean | 368 ++++------------------------------
 RBM2D/Green/EntryDom.lean   | 471 +++-----------------------------------------
 2 files changed, 60 insertions(+), 779 deletions(-)
```
Axiom-registry pre-check (`registry_precheck.lean` = `import RBM3D`, `import RBM3D.Green.EntryDom`, `#assert_rbm_axioms`; `lake env lean`):
```
axiom audit: 1708 theorems, 640 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
base (`import RBM3D` only): axiom audit: 1675 theorems, 637 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 47 (borrowed 2, owed 34, structural 11).
exit=0
```
`RBM3D/Test/Axioms.lean`: unchanged (no new `Prop`-valued predicate; exit 0).

Narrative (each fact checked against the file, the logs above, or section (a)):
- One new file `RBM3D/Green/EntryDom.lean` (1628 lines, `d8fe7c5`): RBM2D `Green/EntryBlock` (836 lines) then `Green/EntryDom` (1042 lines) at `c9a24cf`; 36 public declarations (33 theorems, `blkCoef2`, `goodSet`, `OffPair`); RBM2D's compile checks are replaced by the instances above.  Section (a) needed no correction: its table (constants `81`, `8640 K²`, `1 + 2K`, `Λ' = 4 maxLoopPM`, `k = 2, 2, 1`, `Λ = 𝔡⁻¹`) is what the file proves.
- Profile: RBM2D's `Sblk2` (five-point weight `1/5`, `W⁻²`) is the merged `svar d L W g = W^{-d} SBR d L g`; its facts are re-proved from `sbKernelR` (`≥ 0`, `Σ = 1` so `≤ 1`, support in `{zdistInf ≤ 1}`): `sum_svar_row`, `sum_svar_col`, `svar_le_inv_Wd`.  Exponent map: `W⁻² → W^{-d}`, fibre `Fin W × Fin W → Fin (W^d)`, `L² → L^d`, `L⁴ ≤ N² → L^{2d} ≤ N²`, `|BlockIndex| = N`, `1/5 → S^(B)(g)`, `zdist2 ≤ 1 → zdistInf ≤ 1`; the token scan above shows no `d = 2` token left in the code.
- D40: the one-orientation right side `gexRHS … [q] [p]` is proved at `d ≥ 3` (`offSq_le_gexRHS_blk`, constant `81` as in RBM2D, through `sum_sum_svar_eq` and `norm_loopPM_eq`); no switch to `STgexRHS`; `Pins.lean` untouched.
- Constants (T2057a): RBM2D has `Λ' = 2 maxLoop` from `S ≤ (1/5) W⁻²`; here `S ≤ W^{-d} ≤ 4 maxLoopPM` (`inv_Wd_le_maxLoopPM`, `svar_le_maxLoopPM`), so `diagSq_le_maxLoopPM_blk` has `2160 K² Φ² (4 maxLoopPM)` and `diag_bound_stochDom` the constant `8640 K²` (RBM2D `4320`).
- Stability: RBM2D's `Kstab2 κ L` is the merged `Kstab3 d Λ κ` (`stable_svar_bulk_vtx`; hypotheses `3 ≤ d`, `0 < g ≤ Λ`); per sequence `Λ = 𝔡⁻¹` and `0 < lam n ≤ 𝔡⁻¹` eventually from `(eq:WO)` (`entryDom_lam_window`).  Where RBM2D absorbs `1 + 2 Kstab2 κ L_n ≤ size^ε` and `4320 Kstab2² ≤ size^ε` (`Kstab2 = O(1 + log L_n)`, needing `Bandwidth`), the `d ≥ 3` step is simpler: `K` does not depend on `n`, so `C ≤ size^ε` follows from `size → ∞` alone (`entryDom_const_le_rpow`).  `Bandwidth` is still used for `δ = W^{-c} ≤ size^{-𝔠c}`, for `goodSet` and for `Kstab3 · W^{-c} ≤ 1/2`.
- Fine lattice vs block index: the merged `offSq`, `diagSq`, `GijOmegaSeq`, `GiiOmegaSeq` are on `Idx d L W`; `greenBlk`, `blockMat`, `LDERow …`, `avgErr` on `Vtx d L W`.  The block lemmas are stated on `Vtx`; `offSq_le_gexRHS_fine`, `diagSq_le_maxLoopPM_fine` (new) transport them through `splitEquiv` (`entryDom_greenBlk_apply`, a copy of the private `gres_blockMat_true`, `Green/Pins.lean:350`).
- Dropped, not ported: `sbKre2`, `Sblk2` and their elementary lemmas (replaced by `sbKernelR`, `svar`, merged `svar_nonneg`); `sum_sbKre2_sub_mul(')` and `sum_sum_Sblk2_eq_nbr` (uniform weight `1/5`; false for the weights `a`, `g² a`; 0 uses outside the two files, (a)); `Sblk2_eq_svar`, `stable_relabel`, `stable_Sblk2_bulk` (`svar` is already on `Vtx`; stability is `stable_svar_bulk_vtx`); `eventually_Kstab2_le_rpow` and its two corollaries; the RBM2D `check_*` examples.
- Instances: the pointwise `norm_avgErr_le` instance has `‖avgErr‖ = 1` against a right side `≥ 3`; at `t ≡ 0` every hypothesis of `entry_bound_stochDom`, `diag_bound_stochDom`, `avg_bound_stochDom` is proved (left sides vanish there, so this shows only joint satisfiability); at `t ≡ 1/2` the LDE inputs `hLrow`, `hLcol`, `hLquad`, `hLdiag`, the IBP / fluctuation-averaging inputs `hIBP`, `hFArow`, `hFAblk` and `hLoop` stay hypotheses of the example.

## (c) Verified names (`names.lean`, `lake env lean`: the first two lists elaborate, the third does not)
Mathlib: `Equiv.subLeft`, `Equiv.subRight`, `Finset.le_sup'`, `Finset.lt_sup'_iff`, `Finset.single_le_sum`, `Finset.sum_eq_single`, `Finset.sum_mul_sum`, `Finset.sup_congr`, `Fintype.card_congr`, `Fintype.card_subtype_le`, `Fintype.sum_equiv`, `Fintype.sum_prod_type`, `Matrix.inv_submatrix_equiv`, `Matrix.isHermitian_zero`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.mul_diagonal`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.one_apply_ne`, `Real.one_le_rpow`, `Real.rpow_add'`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_mul_natCast`, `Real.sq_sqrt`, `Real.sqrt_sq`, `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `ZMod.card`, `tendsto_natCast_atTop_iff`, `Filter.Tendsto.eventually_gt_atTop`, `pow_le_pow_left₀`, `mul_inv_le_iff₀`, `le_div_iff₀`, `ite_eq_left`, `ite_eq_right`, `Complex.ofReal_sum`, `Complex.norm_real`, `Nat.pow_le_pow_left`, `Nat.le_mul_of_pos_left`, `inv_eq_of_mul_eq_one_right`, `Real.rpow_natCast`.
Project: `RBM.isUnit_sub_smul_of_isHermitian`, `RBM.zt_im`, `RBM.mE_im_pos`, `RBM.norm_mE`, `RBM.mE_mul`, `RBM.Gauss.zdistInf_le_zdistD`, `RBM.Gauss.Sizes.seqHflow_eq_smul`, `RBM.Gauss.Sizes.card_Idx`, `RBM.Gauss.blockMat_zero`, `RBM.Gauss.ring_inverse_smul_one`, `RBM.sbKernelR`, `RBM.sum_sbKernelR`, `RBM.Green.stable_svar_bulk_vtx`, `RBM.Green.eventually_Kstab3_mul_rpow_le`, `RBM.Green.norm_loopPM_eq`, `RBM.Green.greenBlk_time_zero`, `RBM.Green.perTimeDomAt_of_nonpos`.
Verified absent (`Unknown identifier`): `RBM.Gauss.isUnit_sub_smul_one_of_im_ne_zero`, `RBM.Green.Sblk2`, `RBM.Green.sbKre2`, `RBM.Green.Kstab2`; `RBM.Gauss.card_BlockIndex` is not in the ticket's import closure (`RBM3D/Gauss/FlowCalculus.lean:701`), so `entryDom_card_vtx` uses `Fintype.card_congr (splitEquiv …).symm` and `Sizes.card_Idx`.

## (d) Open issues and paper-delta candidates
- **T2057a** (RBM2D to RBM3D statement difference, not a difference with the paper, which has only `≺`): the loop-floor constant `2 maxLoopPM → 4 maxLoopPM` in `svar_le_maxLoopPM`, `diagSq_le_maxLoopPM_blk` and `4320 → 8640` in `diag_bound_stochDom`: the profile `S^(B)(g)` has entries tending to `1` as `g → 0` (section (a), last lines of `inst.py`), so the RBM2D weight `1/5` is not available.
- **T2057b** (statement form): `|E n| ≤ 2 - κ` here against `<` in `GbEXPHypV3`, which the S1-30 assembly can pass as `<` implies `≤`; the merged pins `GijOmegaSeq`/`GiiOmegaSeq` are on `Idx d L W` while the block lemmas are on `Vtx d L W` (bridged by `offSq_le_gexRHS_fine`, `diagSq_le_maxLoopPM_fine`).
- Open inputs, not proved here and not added to any pin: `hLrow`, `hLcol`, `hLquad`, `hLdiag` (LDE, S1-18), `hIBP`, `hFArow`, `hFAblk` (IBP and fluctuation averaging), `hLoop` (`LoopDetSeq`); `3 ≤ d` and `0 < g ≤ Λ` are used only through `Kstab3`.
- Registry observation: the scan now counts `GoodEvent` (concluded by `entryDom_goodEvent_of_llErr`) and `GijOmegaSeq` (concluded by `entry_bound_stochDom`) as proved, so both appear under "carry nothing yet" (base: 49 premises found, with the module: 47; exit 0; no registry line needed).  The owed line for `GijOmegaSeq` (comment: S1-24) is unchanged; the dispatcher may want to reclassify.
- Section (a) verdict candidate (2), `zdist2 ≤ 1 → zdistInf ≤ 1`, is the signed distance convention D18 (`docs/tickets/ST1-COMMON.md` item 3), so it is cited, not proposed again.
- RBM2D HEAD `9e0f275` differs from the pinned `c9a24cf` in both source files (diff-stat above); the port is from `c9a24cf` as the ticket says, and the HEAD versions were not compared.
