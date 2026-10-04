Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 20:18:17 UTC 2026

Notation: `g = sz.lam n`, `m = mE E`, `b = (1+g²)⁻¹ + L⁻ᵈ`, `B(0) = Bctl n 0 = W⁻ᵈ b` (`Defs/Sizes.lean:214`, `Bparam` `Defs/Params.lean`), `η = etaT E 0 = Im m = √(4-E²)/2`, `S_cc = (1+2dg²)⁻¹` (`sbKernel`, `Defs/Block.lean:38`). RBM2D = `RBM2D/Induction/AzumaProxyN.lean` at `c9a24cf` (commit exists; its line numbers below).

### (i) Exponent table

**Item 1: dictionary and route** (all merged statements used exist in the worktree; names and lines read from the files).

| # | RBM2D (`AzumaProxyN`) | RBM3D merged | where |
|---|---|---|---|
| 1 | `d : Sizes`, `Z2 (d.L n)`, `Idx L W`, `Coord`, `gvar` | `sz : Sizes d`, `Zd d (sz.L n)`, `Idx d L W`, `CoordF d L W`, `gvarF d L W (sz.lam n)` | `FineModel.lean:80,89` |
| 2 | pin `AzumaSubGN d s t K` (`GridGoodN:335`) | `AzumaSubGN sz s t K`: same shape, `Coord ↦ CoordF`, `gvar ↦ gvarF d (sz.L n) (sz.W n) (sz.lam n)`; no `[NeZero k]` | `GridAssemblyN.lean:122` |
| 3 | `AzumaProxyN_linTrVar_eq` (`:199`) via `vB_self` | `vB_self` (`Path/QVIdentity.lean:92`) unfolds to `Σ_{c ∈ coordFinset n} seqGvar sz c · linTr …`; `seqGvar ⟨n,c⟩ = gvarF d (sz.L n) (sz.W n) (sz.lam n) c` is `rfl` (`FineModel.lean:164`); `coordFinset` is `univ.map sigmaMk` (`Markov.lean:139`) | the identity `Pi.single ⟨n,c⟩ 1 ↦ coordinateMatrix c` is private in 3D (`QVIdentity.lean:264`): copy as `azumaProxy_seqXmat_single` |
| 4 | variance bound `linTrVar A, linTrVar((-I)A) ≤ Σ_c gvar_c ‖D_c‖²`, `D_c = Σ κ_b ∂_c Φ_b` | `Re`, `Im` of `D_c` squared `≤ ‖D_c‖²`; `linTr n A X = (tr(AX)).re` (`Markov.lean:134`); `linTr n ((-I)•A) X = (tr(AX)).im` (private copies in 3D: `StepDecompN`, so copy as `azumaProxy_linTr_neg_I_smul`) | trace identity `fderiv_eq_trace_gradMat` (`Path/StepDecomp.lean:123`, Hermitian `X`: `coordinateMatrix_isHermitian` `FineModel.lean:388`) |
| 5 | `stepDecompCN_Z_subG` | same name, `StepDecompN.lean:881` (premises: `HermTestFun`, `{j<τ}` `filt j`-measurable, `Δ·linTrVar(AbCN) ≤ c`, `Δ·linTrVar((-I)AbCN) ≤ c`, `0 ≤ c`); inside it `hasCondSubgaussianMGF_linear` (`Path/Markov.lean:636`) | ticket route confirmed |
| 6 | `Σ_b κ_b Z_b = stepZCN` with kernel `(b,a) ↦ κ_a` | `ZfamN` `StepDecompN.lean:176`, `stepZCN` `:106`; `Σ_b κ_b ZfamN b = √Δ · tr(AbCN X_{j+1})`, `X_{j+1}` and `pathH` Hermitian (`Gauss/FineModel.lean:229`, `Path/Walk.lean:98`) | empty label set: the sum is `0` (`HasCondSubgaussianMGF` of `0`, any proxy) |
| 7 | `Δ<0` case | `gridStep = (t-s)/K` may be `<0` (`Path/Walk.lean:67`); `linTrVar_nonneg` (`Markov.lean:242`) gives `Δ·linTrVar ≤ 0 ≤ Q` | no sign hypothesis needed |
| 8 | `testFun_const_smul`, `testFun_linComb` (`:110`, `:133`) | `HermTestFun` (`Path/StepDecomp.lean:186`: `contDiffAt` at Hermitian points, `bdd₀`): `ContDiffAt.const_smul`, bound `‖q‖C₀`; sums by `ContDiffAt.sum`, `norm_sum_le`. Neither name exists in RBM3D (grep) | pure mathematics, `d`-free |

**Item 2: `0 ∈ GoodSetN` at `u = 0` (`GridGoodN.lean:124`).** At `H = 0`, `u = 0`: `zt E 0 = E + m = -1/m` (`mE_mul`, `Semicircle.lean:49`), `|m| = 1`, `Gres 0 z σ = m_σ·1` (`Gres_zero_eq_scalar`, `LoopGenerator.lean:411`), `Eblk a = W⁻ᵈ 1_{blk=a}`. Hence `𝓛_I(0) = W^{-d(len-1)} ∏ m_σ · 1(all a equal) = MLoop` (merged `initialLoopValue_nonempty/_all_same/_zero_of_adjacentMismatch`, `LoopGenerator.lean:572,654,644`, with `initialGreenScalar = mSigma`), and `𝒦_I(0) = MLoop` for `WF`, `len ≥ 2` (`KLK_isKLoop` field 2, `KLTreeDeriv.lean:1049`, from private `Kgen_zero:993`) and `𝒦^{(1)} = m` (`KLK_one`, `KLTree.lean:206`). So `(𝓛-𝒦)_I(0) = 0` for every `WF` `I` of length `≥ 1` (not for length 0: `𝓛 = tr 1`, `𝒦 = 0`; the cut loops have lengths `k+n-l+1 ≥ 2`, `l-k+1 ≥ 2`, `TreeRep.lean:86`).

| # | clause of `GoodSetN` | value at `H = 0, u = 0` | RHS / level | condition on levels |
|---|---|---|---|---|
| 1 | Hermitian | `Matrix.isHermitian_zero` | — | none |
| 2 | (G2) `STXiLKM m = 1 + max|𝓛-𝒦|/B^m`, `1 ≤ m < k` | `1` | `ΓΦ` | `1 ≤ ΓΦ` |
| 3 | (Dec) `‖𝓛‖+‖𝓛-𝒦‖`, far labels | `0`: far means `ellT·W^{τ'} ≤ diam_∞ a`, `ellT = min(max(g,1),L) ≥ 1` (`one_le_ellT`, `Params.lean:39`), so `diam_∞ > 0`, labels not all equal, `𝓛(0) = 0` | `W^{-D'} > 0` | none (any `τ', D'`) |
| 4 | (D1) `STksimLKM`, `3 ≤ l ≤ k` | `0` (every `STLKIM` factor is `0`) | `Γ(ΓΦ)B^k/η ≥ 0` | `Γ ≥ 0`, `ΓΦ ≥ 0` |
| 5 | (D2) `STelklkM` | `0` | `Γ k(ΓΦ)²B^k/η ≥ 0` | same |
| 6 | (D3) `STegtM` | `0`: `STavgErrM = 𝓛^{(1)} - m = 0` | `Γ(ΓΦ)B^k/η ≥ 0` | same |
| 7 | (D4) `STeeM` | `k·S_cc·W^{-2kd}` if all labels of `a, a'` equal, else `0` (exactly one term `b = b' = c` per cut, signs pair to `|m|^{2k+2} = 1`) | `Γ(ΓΛ)B(0)^{2k}/η` | **`k·η·S_cc ≤ Γ²Λ·b^{2k}`** (`W` cancels) |
| 8 | (Va) | `0` | `W^{-D'}` | none |
| 9 | (Vb) far in `Fin.append a a'` | `0`: every `STeeLoop` contains all labels of `a, a'`, so a mismatch kills it | `W^{-D'}` | none |

Level conditions of the target (hypotheses, deterministic): `|E| < 2`, `3 ≤ L`, `1 ≤ W`, `1 ≤ k`, `0 ≤ Γ`, `1 ≤ ΓΦ`, `k·η·S_cc ≤ Γ²Λ·b^{2k}` (sufficient: `Γ²Λ ≥ k(1+g²)^{2k}`, since `η ≤ 1`, `S_cc ≤ 1`, `b ≥ (1+g²)⁻¹`). The case `Γ = Λ = Φ = 1` is **not** covered: threshold `r_k = kηS_cc/b^{2k} > 1` (rows below). No `ΓΛ ≥ 1` condition (G1 is not a clause in 3D, `GridGoodN.lean:119-123`); RBM2D's `k/5 ≤ Γ²Λ` (`NonAltGood:996`, `S_cc` there is `1/5`) becomes the `g`-dependent `r_k` above (paper-delta candidate `T2159a`).

| # | constant | value | constraint | slack |
|---|---|---|---|---|
| 10 | `r_k` at `sz0` n=0 (`L=4,W=32,g=1/64,E=1/2`) | `k=2: 1.819`, `k=3: 2.647` | `r_k ≤ Γ²Λ` | `Γ²Λ = 51.90` (`Γ = N^{1/10} = 4.287`, `Λ = B(0)^{-1/10} = 2.824`, `Φ = 1`): slack 28.5 (k=2), 19.6 (k=3) |
| 11 | `r_k` at `g = 1/64`, `E = 0`, `L = 3` | `1.728` (k=2), `2.412` (k=3) | `≤ k(1+g²)^{2k} = 2.002, 3.004` | `≈ 0.3, 0.6` |
| 12 | `Γ·Φ` | `4.287` | `≥ 1` | `3.287` |
| 13 | `Bctl n 0 > 0`, `η > 0` | `3.0987e-5`, `0.968` | `RHS ≥ 0` of D1-D4 | positive |

**Consumers (iii).** RBM2D `AzumaProxyN:1300-1304` is a docstring only: the instance holds for all `Γ Λ Φ τ' D'` and notes `0 ∈ GoodSetN` "is not proved here". `NonAltGood:996` is the theorem `zero_mem_goodSetN (hL) (hE) (hk : 1 ≤ k) (hΓ : 0 ≤ Γ) (hΓΛ : 1 ≤ ΓΛ) (hΓΦ : 1 ≤ ΓΦ) (hee : k·(1/5) ≤ Γ(ΓΛ))`; it is used with unit levels `Γ=Λ=Φ=1`, `k=4` (`AltEnd:1858`, `AltProxyQ:1462,1497`), with `Γ = N^{1/100}`, `Λ = Φ = 1` (`NonAltGood:1599`) and `∀ᶠ n` levels (`NonAltGood:1106`). In `d ≥ 3` the unit levels fail (rows 10-11: `r_2 ≥ 1.67 > 1` at every tested `E ∈ {0, 1/2}`, `g ∈ {1/64, 1}`, `L, W`), so a 3D consumer must pass `Γ²Λ ≥ r_k`; the `T2146` levels (`Γ = N^ε`, `Λ = B(0)^{-1/(2q)}`, `Φ ≡ 1`) satisfy it. `Λ ≥ 1`/`ΓΛ ≥ 1` is not needed.

**Item 3 interface.** `azumaSubG_ugen`, `azumaSubG_goodExit` (`RBM2D GridGoodN:1104,1134`), `pathH_zero_of_s_zero` (`:1383`) and `hΦ_of_hermTestFunLoopN` (`:1087`) are **not** in RBM3D (grep, 0 hits; `StepDecompN_loopFam_hermTestFun:1058` is private). Replacements: `pathH sz s t K n 0 ω = √(s n)•X_0 + √Δ•Σ_{Icc 1 0} = 0` when `s n = 0` (`Walk.lean:75`); `mem_of_lt_gridExitTauN` (`GridGoodN:199`), `goodExitMeasN` (`:423`); the composition is re-derivable from the proved `azumaSubGN` with `hermTestFunLoopN` (`LoopC2N.lean:469`) for the test class and `qvPropagatedN` (`QVN.lean:813`: `Σ_c gvarF‖Σ κ ∂_c 𝓛‖² ≤ k·Re Σ κ κ̄' STeeM`, needs `2 ≤ k`, `0 ≤ u < 1`, `u = u_{j+1} ≤ t < 1`, `M` Hermitian) for `hQ`; alternatively `StepDecompN_subGaussStopN_zvecN` (`StepDecompN.lean:1317`). Not a blocker: new in-file lemmas with prefix `azumaProxy_`.

### (ii) One nondegenerate instance

`d = 3`, `sz0` (`n = 0`: `L=4`, `W=32`, `lam=1/64`, `N=2^{21}`), `E ≡ 1/2` (`η = 0.968`), `s = sInst ≡ 0`, `t = vg ≡ 1/32`, `K = Kg ≡ 4`, `Δ = 1/128`, `u_j = j/128` (`grid_data`, `GridGoodN.lean:1129`), `j = 0`, `k = 3`, `σ = (+,-,+)`, `τ' = 1/2`, `D' = 1`. Target 1: `ι = Fin 3 → Zd 3 4`, `Φ_b = loopFamN` (in `HermTestFun` by `hermTestFunLoopN`, `|E|<2`, `u_1 = 1/128 ∈ [0,1)`), `κ_b` the `Ugen` weights, `τ ≡ 4` (`{j<τ}` is everything), `G 0 = Herm ∩ {0}` (`H_0 = 0` as `s = 0`), `Q` the exact form `Δ Σ_c gvarF‖Σ κ ∂_cΦ‖²` at `M = 0`. Target 2: `0 ∈ GoodSetN sz0 0 (1/2) 0 3 Γ Λ 1 (1/2) 1` with `Γ = N^{1/10} = 4.287`, `Λ = B(0)^{-1/10} = 2.824` (`gridTime sInst vg Kg 0 0 = 0`). Target 3: `τ = goodExitTauN` at these levels, `G 0 = GoodSetN ∩ {0}` nonempty by target 2, so `τ` is not identically `0`. External hypotheses: none (target 2 is deterministic; `KLK_isKLoop` and `initialLoopValue_*` are merged theorems, no pin). Limit computation (lesson 14) is not needed: no external hypothesis.

Command (scratch `scratchpad/T2159/check.py`, 42 lines, selection):
`python3 check.py | grep -E "^PART|L=3 W=1 k=[23] g=0.0156|L=3 W=1 k=[23] E=0.0 g=0.0156|L=5 W=2 k=3 E=0.5 g=1.0000|k=[23]: r_k" | cut -c1-230`
```
PART A: brute-force diag-matrix trace vs M-loop W^{-d(n-1)}prod m 1(all equal), L in{3,5},W in{1,2},E in{0,.5,1.5},n<=8: 576 loops, max |diff| = 1.12e-15
PART B: m(m+E)=-1 and |m|=1 at E in {0,.5,1.5}: True;  avgErr=L^(1)-m:  1.2412670766236366e-16
PART C: ee(0) full (b,b') sum vs closed form k*S_cc*W^{-2kd} (all labels equal) / 0 (else); S_cc=1/(1+2dg^2)
  L=3 W=1 k=2 g=0.0156: max rel.err all-equal = 2.4e-16 ; max |ee(0)| at a label-mismatch = 0.0e+00 ; ee(0)=1.9971e+00
  L=3 W=1 k=3 g=0.0156: max rel.err all-equal = 3.0e-16 ; max |ee(0)| at a label-mismatch = 0.0e+00 ; ee(0)=2.9956e+00
PART D: threshold r_k = k*eta*S_cc/b^(2k) for Gamma^2*Lambda (b=(1+g^2)^-1+L^-d), sufficient k*(1+g^2)^(2k); unit levels Gamma=Lambda=Phi=1 pass iff r_k<=1
  L=3 W=1 k=2 E=0.0 g=0.0156: eta=1.0000 b=1.03679 B(0)=1.037e+00  r_k=1.7283 (<=suff 2.002)  unit-levels D4 ok: False
  L=3 W=1 k=3 E=0.0 g=0.0156: eta=1.0000 b=1.03679 B(0)=1.037e+00  r_k=2.4118 (<=suff 3.004)  unit-levels D4 ok: False
  L=5 W=2 k=3 E=0.5 g=1.0000: eta=0.9682 b=0.50800 B(0)=6.350e-02  r_k=24.1450 (<=suff 192.000)  unit-levels D4 ok: False
PART E: sz0 n=0: N=2097152 Gamma=N^(1/10)=4.287 B(0)=3.0987e-05 Lambda=B^(-1/10)=2.824 Phi=1 ; G2: Gamma*Phi=4.287>=1: True
  k=2: r_k=1.8191 <= Gamma^2*Lambda=51.90 : True ; ee(0)=1.732e-18 <= D4 level=4.942e-17 : True (ratio 28.5)
  k=3: r_k=2.6467 <= Gamma^2*Lambda=51.90 : True ; ee(0)=2.420e-27 <= D4 level=4.746e-26 : True (ratio 19.6)
PART F: ellT L g 0 = min(max(g,1),L) >= 1 for L in{3,5}, g in{1/64,.5,1,7}: True => far (ellT*W^tau' <= diam_inf) implies diam_inf>0, so the labels are not all equal, L(0)=K(0)=0
```
Part A checks `𝓛(0)` by explicit diagonal matrices; `𝒦(0) = MLoop` is the merged lemma (not recomputed by the script). Part E reproduces `T2146-prove.md` (a) part E (`ee(0) = 1.732e-18`, level `4.942e-17`).

### Verdicts
- Target 1 (`testFun_const_smul`, `testFun_linComb`, `azumaSubGN`): **PASS** (rows 1-8; merged pin matches RBM2D up to the dictionary; no hypothesis blocks).
- Target 2 (`zero_mem_goodSetN`): **PASS** with the level hypotheses of (i) (`0 ≤ Γ`, `1 ≤ ΓΦ`, `kηS_cc ≤ Γ²Λ b^{2k}`; unit levels are false in `d = 3`; `τ', D'` arbitrary).
- Target 3 (instances): **PASS**; the composition lemma and `pathH_zero_of_s_zero` must be written in the file (absent from RBM3D); the `goodExit` instance must use levels with `Γ²Λ ≥ r_k` (e.g. the T2146 levels above).

## (b) Script output (stage 1b, written Sun Oct  4 20:59:18 UTC 2026)

```
$ lake build RBM3D.Induction.AzumaProxyN 2>&1   # lines of the new module only; `Lnnn:0` = the `#print axioms` at file line nnn (`info:`, `RBM.Ind.` dropped, wrapped lines joined)
ℹ [3789/3789] Replayed RBM3D.Induction.AzumaProxyN
L1473:0: 'testFun_const_smul' axioms: [propext, Classical.choice, Quot.sound]
L1474:0: 'testFun_linComb' axioms: [propext, Classical.choice, Quot.sound]
L1475:0: 'azumaSubGN' axioms: [propext, Classical.choice, Quot.sound]
L1476:0: 'zero_mem_goodSetN' axioms: [propext, Classical.choice, Quot.sound]
L1477:0: 'azumaProxy_hee_of_levels' axioms: [propext, Classical.choice, Quot.sound]
L1478:0: 'zero_mem_goodSetN_of_levels' axioms: [propext, Classical.choice, Quot.sound]
L1479:0: 'azumaProxy_pathH_zero_of_s_zero' axioms: [propext, Classical.choice, Quot.sound]
L1480:0: 'azumaProxy_subG_ugen' axioms: [propext, Classical.choice, Quot.sound]
L1481:0: 'azumaProxy_subG_goodExit' axioms: [propext, Classical.choice, Quot.sound]
L1482:0: 'azumaProxy_pos_gridExitTauN' axioms: [propext, Classical.choice, Quot.sound]
L1483:0: 'azumaProxy_loop3_scalar' axioms: [propext, Classical.choice, Quot.sound]
L1484:0: 'AzumaProxyNInst.azumaSubGN_instance' axioms: [propext, Classical.choice, Quot.sound]
L1485:0: 'AzumaProxyNInst.zero_mem_goodSetN_instance' axioms: [propext, Classical.choice, Quot.sound]
L1486:0: 'AzumaProxyNInst.zero_mem_goodSetN_of_levels_instance' axioms: [propext, Classical.choice, Quot.sound]
L1487:0: 'AzumaProxyNInst.zero_mem_goodSetN_instance_grid' axioms: [propext, Classical.choice, Quot.sound]
L1488:0: 'AzumaProxyNInst.azumaSubGN_goodExit_zero_instance' axioms: [propext, Classical.choice, Quot.sound]
L1489:0: 'AzumaProxyNInst.goodExitTauN_pos_instance' axioms: [propext, Classical.choice, Quot.sound]
L1490:0: 'AzumaProxyNInst.azumaSubGN_goodExit_instance' axioms: [propext, Classical.choice, Quot.sound]
L1491:0: 'AzumaProxyNInst.testFun_linComb_instance' axioms: [propext, Classical.choice, Quot.sound]
L1492:0: 'AzumaProxyNInst.testFun_const_smul_instance' axioms: [propext, Classical.choice, Quot.sound]
L1493:0: 'AzumaProxyNInst.qProxy3_pos' axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3789 jobs).
```
```
$ grep -nwE "sorry|admit|native_decide|axiom" <file> | wc -l; git rev-parse --short HEAD; git diff main...t/T2159 --stat; git diff main -- GridAssemblyN.lean Test/Axioms.lean | wc -l; grep -n "AzumaSubGN\|azumaSubGN" Test/Axioms.lean | wc -l
       0
bf84610
 RBM3D/Induction/AzumaProxyN.lean | 1493 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 1493 insertions(+)
       0
       0
```
```
$ python3 extract.py <target names>   # statement text from the file, up to the first `:=`
-- RBM3D/Induction/AzumaProxyN.lean:90
theorem testFun_const_smul
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (h : HermTestFun sz n Φ) (q : ℂ) : HermTestFun sz n (fun M => q • Φ M) := by
-- RBM3D/Induction/AzumaProxyN.lean:108
theorem testFun_linComb {ι : Type*} [Fintype ι] (q : ι → ℂ)
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (h : ∀ i, HermTestFun sz n (Φ i)) :
    HermTestFun sz n (fun M => ∑ i : ι, q i * Φ i M) :=
-- RBM3D/Induction/AzumaProxyN.lean:257
theorem azumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGN sz s t K := by
-- RBM3D/Induction/AzumaProxyN.lean:801
theorem zero_mem_goodSetN {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
    {Γ Λ Φ τ' D' : ℝ} (hΓ : 0 ≤ Γ) (hΓΦ : 1 ≤ Γ * Φ)
    (hee : (k : ℝ) * ((1 + 2 * (d : ℝ) * (sz.lam n) ^ 2)⁻¹ * etaT E 0) ≤
      Γ * (Γ * Λ) * (Bparam d (sz.L n) (sz.lam n) 0 0) ^ (2 * k)) :
    (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) ∈
      sz.GoodSetN n E 0 k Γ Λ Φ τ' D' := by
-- RBM3D/Induction/AzumaProxyN.lean:924
theorem zero_mem_goodSetN_of_levels {E : ℝ} (hE : |E| < 2) {k : ℕ} (hk : 1 ≤ k)
    {Γ Λ Φ τ' D' : ℝ} (hΓ : 0 ≤ Γ) (hΓΦ : 1 ≤ Γ * Φ)
    (hΓΛ : (k : ℝ) * (1 + (sz.lam n) ^ 2) ^ (2 * k) ≤ Γ * (Γ * Λ)) :
    (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) ∈
      sz.GoodSetN n E 0 k Γ Λ Φ τ' D' :=
```
```
$ python3 extract.py <instance names>   # all inside `namespace RBM.Ind.AzumaProxyNInst` (data: sz0, n = 0, E = 1/2, s = sInst, v = vg, K = Kg, k = 3)
-- RBM3D/Induction/AzumaProxyN.lean:1168
theorem azumaSubGN_instance (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    SubGaussFormN sz0 0 (fun _ => Kg 0)
      (fun ω => ∑ b, kap3 m a b * ZfamN sz0 sInst vg Kg 0 0 phi3 ω b) (qProxy3 m a) := by
-- RBM3D/Induction/AzumaProxyN.lean:1189
theorem zero_mem_goodSetN_instance :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      sz0.GoodSetN 0 (1 / 2) 0 3 4 3 1 (1 / 2) 1 := by
-- RBM3D/Induction/AzumaProxyN.lean:1200
theorem zero_mem_goodSetN_of_levels_instance :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      sz0.GoodSetN 0 (1 / 2) 0 3 4 3 1 (1 / 2) 1 := by
-- RBM3D/Induction/AzumaProxyN.lean:1210
theorem zero_mem_goodSetN_instance_grid :
    (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
      sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Λ3 0) (Φ1 0) (1 / 2) 1 := by
-- RBM3D/Induction/AzumaProxyN.lean:1220
theorem azumaSubGN_goodExit_zero_instance (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ)
    (a : Fin 3 → Zd 3 (sz0.L 0)) :
    SubGaussFormN sz0 0 (goodExitTauN sz0 Einst sInst vg Kg 3 Γ Λ Φ τ' D' 0)
      (fun ω => ∑ b, kap3 m a b * ZfamN sz0 sInst vg Kg 0 0 phi3 ω b) (qProxy3 m a) := by
-- RBM3D/Induction/AzumaProxyN.lean:1240
theorem goodExitTauN_pos_instance (ω : PathΩ sz0) :
    0 < goodExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 (1 / 2) 1 0 ω := by
-- RBM3D/Induction/AzumaProxyN.lean:1251
theorem azumaSubGN_goodExit_instance (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (m : ℕ) (hm : m ≤ Kg 0)
    (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < m) (Q : ℝ≥0)
    (hQ : ∀ M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ 0) (Λ 0) (Φ 0) τ' D',
      M.IsHermitian → gridStep sInst vg Kg 0 * ((3 : ℕ) * qvFormN sz0 0 (Einst 0)
        (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 m) sig3 M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
      (goodExitTauN sz0 Einst sInst vg Kg 3 Γ Λ Φ τ' D' 0)
      (fun j ω => ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω) m a j Q :=
-- RBM3D/Induction/AzumaProxyN.lean:1264
theorem testFun_linComb_instance (m : ℕ) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    HermTestFun sz0 0 (fun M => ∑ b, kap3 m a b * phi3 b M) :=
-- RBM3D/Induction/AzumaProxyN.lean:1269
theorem testFun_const_smul_instance (b : Fin 3 → Zd 3 (sz0.L 0)) :
    HermTestFun sz0 0 (fun M => Complex.I • phi3 b M) :=
-- RBM3D/Induction/AzumaProxyN.lean:1441
theorem qProxy3_pos : 0 < qProxy3 1 b0 := by
```
```
$ sed -n "/^section StatementChecks/,/^end StatementChecks/p" <file>   # the merged pin, unchanged, proved by azumaSubGN
section StatementChecks

example {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) : AzumaSubGN sz s t K :=
  azumaSubGN sz s t K

end StatementChecks
```
```
$ name-clash grep of the new public names outside the new file (worktree; then `main` branch)
       0
       0
```
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h [c9a24cf]; ... diff --stat c9a24cf HEAD -- <ported files>   (no RBM1D file ported)
9e0f275
c9a24cf
 RBM2D/Induction/AzumaProxyN.lean | 1140 ++------------------------
 RBM2D/Induction/GridGoodN.lean   |  847 ++------------------
 RBM2D/Induction/NonAltGood.lean  | 1629 ++------------------------------------
 3 files changed, 213 insertions(+), 3403 deletions(-)
```
```
$ registry pre-check (DECISIONS §20): lake env lean precheck.lean   [import RBM3D; import RBM3D.Induction.AzumaProxyN; #assert_rbm_axioms]  -> exit 0
axiom audit: 4782 theorems, 1702 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
```
$ full `lake build` with the root import added temporarily (RBM3D.lean restored afterwards, git status clean)
1829:info: RBM3D.lean:206:0: axiom audit: 4782 theorems, 1702 definitions, 0 axioms in `RBM` (compiler-generated declara
Build completed successfully (3924 jobs).
       0
```
```
$ python3 thr.py   # D4 threshold r_k = k eta S_cc / b^(2k) at sz0, n = 0, E = 1/2 (cf. (a) rows 10-11)
k=2: S_cc=0.998537 eta=0.968246 b=1.015381 r_k=1.8191  suff k(1+g^2)^(2k)=2.0020  Gamma^2*Lambda at (4,3)=48
k=3: S_cc=0.998537 eta=0.968246 b=1.015381 r_k=2.6467  suff k(1+g^2)^(2k)=3.0044  Gamma^2*Lambda at (4,3)=48
```

Narrative (facts from the files and the logs above):
- Result: targets 1, 2, 3 are built in the new file `RBM3D/Induction/AzumaProxyN.lean` (1493 lines), commits `85f8fb9`, `bf84610` (HEAD) on `t/T2159`; the diff against `main` is this one file; the last real build before `bf84610` printed `Built RBM3D.Induction.AzumaProxyN (8.6s)`; `GridAssemblyN.lean` (the pin) and `Test/Axioms.lean` are unchanged.
- Target 1: `azumaSubGN` proves the merged pin `AzumaSubGN sz s t K` (`GridAssemblyN.lean:122`) with no added hypothesis (the `example` above). Port of RBM2D `AzumaProxyN:279` at `c9a24cf` through the dictionary of (a) rows 1-8: `Σ_b κ_b Z_b = stepZCN`, `linTrVar ≤ Σ_c gvarF_c ‖Σ_b κ_b ∂_c Φ_b‖²` via `vB_self` (`azumaProxy_linTrVar_eq`), then `stepDecompCN_Z_subG` (`hasCondSubgaussianMGF_linear`, `Path/Markov.lean:636`); the empty label set and `Δ < 0` are handled as in (a) rows 6-7. `testFun_const_smul`, `testFun_linComb` are ports of `AzumaProxyN:110, 133` for the merged `HermTestFun`.
- Target 2: `zero_mem_goodSetN` is proved for all `sz`, `n`, `|E| < 2`, `k ≥ 1`, `τ'`, `D'`, with the deterministic level hypotheses of (a) (i): `0 ≤ Γ`, `1 ≤ Γ Φ`, `hee`. Route: `𝓛_0 = 𝒦_0` at `H = 0` from `KLK_isKLoop` and `initialLoopValue_nonempty` (`azumaProxy_loopL_zero_eq_KLK`) gives `STmaxLKM = 0` (so `Ξ̂ = 1` in (G2)) and value `0` in (D1)-(D3), (Va); (Dec) and (Vb) use that the far condition forces two distinct labels and `loopL = 0` there; (D4) is the one-term-per-cut bound `azumaProxy_norm_STeeM_zero_le` with `S_cc = (1 + 2dg²)⁻¹`. The values and conditions agree with (a) rows 1-9; no correction to (a) was needed, so there is no (a′).
- Instance levels: (a) (ii) uses `Γ = N^{1/10}`, `Λ = B(0)^{-1/10}`; the instances use `Γ = 4`, `Λ = 3`, `Φ = 1` at `sz0`, `n = 0`, `E = 1/2`, `k = 3` (`Γ²Λ = 48 ≥ r_3 = 2.65`, `thr.py` above), so that `hee` is discharged by `norm_num` (`azumaProxy_hee_of_levels`).
- Target 3: `azumaProxy_subG_ugen` / `azumaProxy_subG_goodExit` (RBM2D `GridGoodN:1104, 1134`) and `azumaProxy_pathH_zero_of_s_zero` (`:1383`) are not in the merged `GridGoodN`; they are written here from the proved `azumaSubGN`, `hermTestFunLoopN` and `qvPropagatedN` (they need `2 ≤ k`, as `QVPropagatedN`). `azumaSubGN_instance` and `azumaSubGN_goodExit_zero_instance` apply `azumaSubGN` with the loop family of the step `0 → 1` and `Q` the exact variance form at `H_0 = 0`; `qProxy3_pos` shows `Q > 0` at `m = 1`, `a = (0,0,0)` (port of RBM2D §8c `:1811-1958`), and `goodExitTauN_pos_instance` shows `0 < τ` at every sample, from `zero_mem_goodSetN_instance_grid`. `azumaSubGN_goodExit_instance` keeps the majorant `hQ` on `GoodSetN` as a hypothesis, as RBM2D `AzumaProxyN:1324` does: it is the output of the Step 3 tickets, not proved here.
- Registry: `Test/Axioms.lean` has no `AzumaSubGN` line (grep above: 0), so nothing was deleted or added; the pre-check and the full build (root import added temporarily, then restored) pass with 0 axioms.

## (c) Verified Mathlib names
`#check` of each name in a scratch file importing the new module: 0 errors (`scratchpad/T2159/names.lean`, 56 names; those used are listed).
- `ContDiffAt.const_smul`, `ContDiffAt.sum`, `ContDiffAt.differentiableAt`, `norm_sum_le`, `norm_smul`, `Complex.abs_re_le_norm`, `Complex.abs_im_le_norm`, `pow_le_pow_left₀`.
- `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.smul_const`, `HasDerivAt.const_add`, `DifferentiableAt.hasFDerivAt`, `HasDerivAt.inv`, `HasDerivAt.comp_ofReal`, `HasDerivAt.mul`, `HasDerivAt.const_mul`, `HasDerivAt.congr_deriv`, `HasDerivAt.deriv`.
- `Finset.sup'_le`, `Finset.le_sup'_of_le`, `Finset.sup_le`, `Finset.sum_pos'`, `Finset.sum_eq_single`, `Finset.sum_map`, `Function.Embedding.sigmaMk_apply`, `List.map_fst_zip`, `List.mem_ofFn`, `List.length_ofFn`, `Fin.addCases`, `Fin.append_left`, `Fin.append_right`.
- `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.toNNReal_pos`, `Real.le_coe_toNNReal`, `Real.one_le_exp`, `Real.norm_of_nonneg`, `Complex.norm_real`, `inv_le_one_of_one_le₀`, `mul_inv_cancel₀`, `le_div_iff₀`, `inv_eq_of_mul_eq_one_right`, `MeasureTheory.hittingBtwn_le_iff_of_lt`, `MeasurableSet.const`, `Matrix.isHermitian_zero`.
- Deprecated in this Mathlib (build warnings of the first compile, avoided in the final file): `push_neg` (use `push Not`), `if_pos`, `if_neg`, `if_true`, `if_false` (replaced by `simp only [eq_true h, eq_false h, ↓reduceIte]`).

## (d) Open issues and paper-delta candidates
- `T2159a` (Lean statement differs from RBM2D `NonAltGood:996`, not from the paper): the (D4) clause at `H = 0`, `u = 0` needs `k S_{cc} η_0 ≤ Γ² Λ b^{2k}`, `S_{cc} = (1 + 2 d g²)⁻¹`, `b = (g²+1)⁻¹ + L^{-d}`; RBM2D's `k/5 ≤ Γ² Λ` becomes this `g`-dependent condition, which the unit levels `Γ = Λ = Φ = 1` need not satisfy (threshold `1.82`, `2.65` for `k = 2, 3` at `sz0`, `thr.py`; (a) rows 10-11). A consumer must pass levels with `hee`, e.g. `Γ² Λ ≥ k (1 + g²)^{2k}` (`zero_mem_goodSetN_of_levels`). The failure at unit levels is script evidence ((a) parts C-D, `thr.py`); Lean proves only the upper bound `azumaProxy_norm_STeeM_zero_le`, not the exact value of `STeeM` at `H = 0`.
- Open: the majorant `hQ` of `Δ k qvFormN` on `GoodSetN` (`azumaSubGN_goodExit_instance`) belongs to S3-10/S3-14. `YMomentsN` (ST2-35) and the primed `YMomentsUnifN` (T2154 (d) item 2) are not in this ticket and untouched.
- Observation: RBM2D `HEAD` (`9e0f275`) differs from the ported `c9a24cf` (diff-stat above); all ports are from `c9a24cf`, as the ticket says. No RBM1D file was ported.
- Observation: `AzumaSubGN` is now a hypothesis of two lemmas (`azumaProxy_subG_ugen`, `azumaProxy_subG_goodExit`) and proved by `azumaSubGN`, so the registry scan needs no owed line (pre-check exit 0).
