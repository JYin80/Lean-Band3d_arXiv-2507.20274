Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 06:08:35 UTC 2026

Targets (mathematics only): `HermTestFunLoopN`/`hermTestFunLoopN` (`‖∂²𝓛_{u,σ,b}(M)[y,y]‖ ≤ k(k+1) N η_u^{-(k+2)} ‖y‖²`, `N=(WL)^d`, `η_u=(1-u)Im m(E)`, `HermTestFun`); `GridDriftN`/`gridDriftN` (`‖P_j(a) − Δ S_j(a)‖ ≤ stepErrN`); `exists_norm_Kcal_le_win`. RBM2D sources at `c9a24cf`, lines of `git show c9a24cf:RBM2D/...`.

### (i) Exponent / `W²`-`Z2`-`L²` table
Token counts (grep on the two RBM2D files): LoopC2N `Z2`=10, `Idx L W`=19, `(L W)^2`=2; GridDriftN `Z2`=100, `SB L`=14, `Theta L`=14, `thetaGenMat L`=16, `(W:ℝ)^2`=8, `(L:ℝ)^2`=5, `(W⁻¹)^2)^`=2, `(W L)^2`=1.

| # | RBM2D occurrence | d≥3 replacement and why it holds | slack |
|---|---|---|---|
| 1 | `Z2 L`, `Idx L W`, `BlockIndex L W` | `Zd d L`, `Idx d L W`, `Vtx d L W` (R2); `blockMat d L W`, `card_BlockIndex : card (Vtx d L W) = (L*W)^d` (FlowCalculus.lean:701) | equality |
| 2 | trace cost `(L W)^2` (LoopC2N:458 `hN`) | `Sizes.size n = (W n * L n)^d` (Sizes.lean:157); `‖tr A‖ ≤ card·‖A‖` with card = N | equality |
| 3 | `‖E_b‖ ≤ W⁻² ≤ 1` (LoopC2N) | `‖Eblk d L W a‖ ≤ (W^d)⁻¹` (FlowCalculus.lean:663), `≤ 1` as `W ≥ 1` | factor `W^d`=8 (instance); statement keeps the pin's `‖E_b‖ ≤ 1` count |
| 4 | Hessian constant `k(k+1)` (LoopC2N:441) | dimension-free: `(R E Q)'' = R''EQ+2R'EQ'+REQ''`, `R''=2RDRDR`, `‖R‖≤η⁻¹`; count `2k + k(k−1) = k(k+1)` (script: 12=12 at k=3); only `N` carries `d` | 0 (tight count) |
| 5 | `η_u=(1-u)Im m`, `z_u` (`spectralZ`) | `zt E u = E+(1-u) mE E` (Semicircle.lean:179), `etaT` (GLoop.lean:75), `Im z = η` ; `0 ≤ u`, `u<1`, `|E|<2` as the pin; `0 ≤ u` is not used by the proof (as `hermTestFun_loopPM`) | pin kept verbatim |
| 6 | `SB L` (5-point) | `SB d L g`, `(2d+1)`-point, doubly stochastic for `3 ≤ L`, any real `g`: `norm_SB` (Block.lean:136), script `‖SB‖_{∞→∞}=1.0` | equality |
| 7 | `Theta L ξ`, `‖Θ_{tm}‖≤(1-t)⁻¹` | `Theta d L g ξ`; `norm_Theta_le` (Props4.lean:218, real `t`, `‖m‖=1`); complex-argument form is **private** `norm_Theta_le_of_lt` (UBounds.lean:252): copy as private; `Theta_sub_Theta` (Deriv.lean:57) needs `‖SB‖=1` | script `1.19 ≤ 2.29` |
| 8 | `thetaGenMat L ξ s`; row-sum helpers | `thetaGenMat d L g ξ u` public (UBounds.lean:53); `sum_norm_thetaGenMat_row_le`, `..._diff_row_le`, `sum_norm_row_le_opNorm` are private there: copy private (`gdn_row_*`), proofs use only `‖SB‖=1`, `norm_Theta_le_of_lt`: dimension-free | — |
| 9 | `𝒰` step `uStepC k Δ v` (GridDriftN `gdn_Ugen_step_le` :408; `thetaSig`) | dimension-free (k, Δ, v only); `thetaSig ↦ ThetaN` (`thetaKer μ t = (μ SB) Θ_{tμ}`, `μ_i = cycProd`); `Ugen d L g E σ v w` (GridDuhamelN.lean:65) | script: `1.0e-2 ≤ 1.25e-1` |
| 10 | `𝒦` step `kStepC`: `W²k²L²` (:461, :493; HierVocab:432) | `c = W^d k² L^d = N k²` from `norm_primBil_le` (HierAlgebra.lean:254, `W^d n² L^d B_F B_G`); `kStepC = 2cB(cB²)+c(cB²)²`; derivative `HasDerivAt` from `KLK_isKLoop` (KLTreeDeriv.lean:1049) with `treeEqRhs` for `primRhs` | script `c=864,1944=N k²`; remainder `7e-4, 2e-4 ≤ 3e3, 4e4` |
| 11 | `stepErrN`: `((W⁻¹)^2)^(k−1)` (HierVocab:440) | `((W^d)⁻¹)^(k−1)` from `norm_gloop_le_of_le_abs_im` (Split.lean:757): `‖𝓛‖ ≤ η⁻ᵏ (W^{-d})^{k−1}` | — |
| 12 | `envConst L W E k v` | `envConst d L W E k v = 16(k+3)⁴ N⁴ (1+η_v⁻¹)^{k+4}` (OneStep.lean:78), `N=(WL)^d`; `condExp_loop_drift` (LoopStep.lean:310) | value `2.9e15·Δ^{3/2}` at the instance (dominates; observed residual `≤2e-5`) |
| 13 | `exists_norm_Kcal_le_win`: `W²L²=N`, `Mt=W²ℓ²η`, input `Kbound_prec_uncond` | `(WL)^d=N`; `Bctl = W^{-d}·Bparam d L g t 0` (Sizes.lean:214, Params.lean:36); input **no proof in RBM3D**: `STKbound sz E` (Induction/Defs.lean:174, registered owed, DECISIONS §16/§19, KL7). See F1 | see (ii) |
| 14 | `Bctl(u) ≤ 2 η_v⁻¹` for `0≤u≤v<1` (replaces `Mt⁻¹ ≤ η_v⁻¹`) | `Bparam d L g u 0 = (g²+1−u)⁻¹ + (L^d(1−u))⁻¹ ≤ 2/(1−u)`; `W^{-d} ≤ 1`; `1/(1−u) ≤ 1/(1−v) ≤ η_v⁻¹` (`Im m ≤ 1`); the `2^{m−1}` is absorbed by `N^{τ/2}` eventually | script: `0.209 ≤ 4.57`, `0.60 ≤ 40` |
| 15 | §29 boundary: `0 ≤ s`, `t<1`, `|E|<2`, `K n ≠ 0`, `∀ n` | present as hypotheses (pin shape); only values at the index `n` are used (`gdn_time_facts`); `Δ ≤ 1` follows from `0≤s≤t<1`, `K≥1`; `L^d ≤ W^K` not used by `gridDriftN`; `∀ n` hypotheses are stronger than needed: see F2 | instance: `s=1/2,t=3/4,Δ=1/16` |

Import cuts (declarations used from the cut files; none carries a `d=2` argument, none is class c):
- `GridGoodN` (into LoopC2N): only `HermTestFunLoopN` (defined here) and the instance data `energy, sTime, tTime, Kg, GridGoodN` (§6 check): replace by `sz0` data (Sizes.lean:260).
- `Path/GoodEvent`: only `GoodEvent_measurable_gloop` ↦ `walk_measurable_loopL` (Walk.lean:780) ∘ `walk_measurable_blockMat` ∘ `pathH_measurable_filt` (Stop.lean:159), as T2104 did (DuhamelTail.lean:36). `gridStep`, `gridTime` are in merged `Path/Walk`.
- `Path/ScalesBridge`: only `kloop_Mt_eq` (and `one_le_ellT`, `etaT`, `etaT_pos`): `Mt`-chain replaced by row 14 (`one_le_ellT` is Params.lean:39).
- `Loop/KBound`: `Kbound_prec_uncond` has no RBM3D counterpart (row 13, F1). `Hierarchy/Loops`, `Path/Step2Props`, `Gauss/{LoopEnvelope,SpectralWindow}` ↦ merged `loopL, blockMat, loopOf, zt, mE_im_pos`.
- Not ported (P.1 unused): none; `hierarchyN` ↦ `hierarchyN_holds d` (LoopGenN.lean:621); `lkTensor, ksimLK, elklkN, egtN` ↦ `STLKM, STksimLKM, STelklkM, STegtM` at `H = pathH` (Step2Defs.lean:68, 723–750); `AvecN, predIncN` merged (GridDuhamelN.lean:272, 284).

Findings. F1: `exists_norm_Kcal_le_win` as ported rests on RBM2D's proved `Kbound_prec_uncond`; RBM3D has only the owed pin `STKbound`. Proposed form: `∀ sz E, STKbound sz E → (∀ n,|E n|<2) → u v sequences (0≤u≤v<1) → ∀ m, τ>0, ∀ᶠ n, ∀ J WF, 2≤len≤m, ‖KLK d (L n) (lam n) (W n) (E n) (u n) J‖ ≤ N^τ η_{v n}^{-m}` (sequence-level, since `STKbound` is a `Prec` along `sz`; deterministic from `Prec` because `size ≥ 27` so `N^{-D}<1`). Paper-delta candidate T2111a. F2: pin `GridDriftN` has `∀ n` hypotheses (§29 (4)); proof needs them only at `n`: prove an `_at` form (T2104c) and derive the pin.

### (ii) Nondegenerate instance and numerics
Instance: `d=3, L=3, W=2` (`N=216`), `E=0` (`m=i`), `g=2^{-3/2}`, `k=3`, `σ=(+,−,+)`. (a) `u=1/2`, `η=1/2`. (b) `s=1/2, t=3/4, K=4, j=0`: `Δ=1/16`, `u_j=1/2`, `u_{j+1}=9/16<1`, `Bk=0.188579` (sup of `|𝒦_w(J)|`, `w≤9/16`, `|J|∈{2,3}`, all sign patterns, `𝒦` by RK4 of `(pro_dyncalK)`: `KLK` solves it, `KLK_isKLoop` KLTreeDeriv.lean:1049, unique by `KLK_unique` KLUnique.lean:117). Hermitian state `H=√u_j X` (one model sample). MC: 10⁴ samples = 5000 antithetic pairs. Lean examples use `sz0` (L₀=4, W₀=32, lam₀=1/64, size 2097152; `sz0_values`, Sizes.lean:267) with `STKbound sz0 E` left as hypothesis (owed pin); a constant `L=3,W=2` sequence cannot carry `STKbound` (ratio 1.08>1 below), so it is used for the deterministic checks only.

Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2111 && python3 check.py` (output `check.out`; 4 min):
```
PART 1: C^2 bound of hermTestFunLoopN, d=3 L=3 W=2 (N=216) E=0 u=1/2 eta=0.5000 k=3 sigma=(+,-,+)
bound k(k+1) N eta^-(k+2) = 82944.0 ; with extra (W^-d)^k = 162.0000
max over 15 trials |d^2Phi[y,y]|/||y||^2 = 0.255467 ; ratio to bound = 3.080e-06 ; ratio to sharp = 1.577e-03
2k+k(k-1) = 12  k(k+1) = 12
PART 2: one grid step of gridDriftN, d=3 L=3 W=2 E=0 g=2^-1.5 k=3 sigma=(+,-,+), s=1/2 t=3/4 K=4 j=0
Delta=0.06250 u_j=0.50000 u_{j+1}=0.56250 eta_{u_j}=0.50000 eta_{u_{j+1}}=0.43750
envelope B_k = sup_{w<=u_{j+1}, 2<=|J|<=3} |K_w(J)| = 0.188579 (grid, RK4 h=1/256)
stepErrN pieces: envConst*D^1.5=2.916e+15 kStepC*D^2=3.649e+04 uStepC*(..)=3.931e-02 total=2.916e+15
label a      P_j                        Delta*S                    |P-DS|     MC SE      |DS|       <=err?
(0, 0, 0)    4.95418e-05+7.95415e-05j   4.37175e-05+8.32107e-05j   6.884e-06  7.984e-06  9.400e-05  True
(4, 4, 4)    -1.83188e-04-1.10476e-04j  -1.73556e-04-9.33770e-05j  1.963e-05  1.080e-05  1.971e-04  True
(4, 4, 5)    1.21870e-05+4.26003e-06j   9.28118e-06+3.53989e-06j   2.994e-06  1.389e-06  9.933e-06  True
(0, 1, 2)    1.69514e-06-9.30542e-08j   1.36932e-06+3.43109e-08j   3.498e-07  2.927e-07  1.370e-06  True
(13, 13, 14) -8.22975e-06+2.31164e-05j  -7.86358e-06+2.11540e-05j  1.996e-06  1.276e-06  2.257e-05  True
(5, 9, 20)   -3.29926e-08-1.18600e-09j  -2.04385e-08-1.17914e-08j  1.643e-08  1.200e-08  2.360e-08  True
```
(Part 1: 12 random/structured `(M,y,b)`, plus `y=1`, `y=P_b`, `M=0`; `f''` by 5-point differences, `h=0.01`. Part 2: `P_j=E[A_{j+1}|F_j]−𝒰A_j`, `S` = `Σ_{l=3}^{3}ksimLK+elklk+egt` at `(H,u_j)`; residual within 1–2 MC standard errors and ≈10% of `|ΔS|`, so the drift term is not vacuous.)

Command: same directory, `python3 check3.py` (`check3.out`):
```
||SB||_inf-inf = 1.0  (norm_SB: 1 for 3<=L)
||Theta(t m)||_inf <= 1/(1-t): 1.1919491716391541 <= 2.2857142857142856
U-step: max|UA-A-Delta*ThetaN A| = 1.015e-02  <=  uStepC*M = 1.254e-01 (M=1.00)  True
envelope B = 0.188579 ; c(k=2)=864 c(k=3)=1944 = N k^2 = 864, 1944
K-step k=2: max|K(u+D)-K(u)-D K'(u)| = 7.299e-04 <= kStepC*D^2 = 3.225e+03
K-step k=3: max|K(u+D)-K(u)-D K'(u)| = 2.285e-04 <= kStepC*D^2 = 3.649e+04
W=2 L=3 g=0.3536 w=0.5000 v=0.5625: Bctl=2.0926e-01  2/eta_v=4.5714  ok=True
W=32 L=4 g=0.0156 w=0.5625 v=0.5625: Bctl=7.0805e-05  2/eta_v=4.5714  ok=True
N^tau * eta_v^-m at the instance (N=216, tau=1, m=3, v=9/16) = 2579.4 >= B = 0.1886
```
Hypothesis `STKbound` (owed, not external): concrete limit computation, `python3 check2.py` (`check2.out`): `max_{t≤9/16,σ,a} |𝒦^{(k)}| / Bctl(t)^{k−1}`, `g=W^{-3/2}`, `L=3` (by the ODE scaling `𝒦^{(k)} = W^{-d(k−1)} κ(g,t)` the ratio depends on `W` only through `g`):
```
W= 2 g=0.35355  k=2: 1.0786   k=3: 1.1609
W= 4 g=0.12500  k=2: 0.9785   k=3: 0.9541
W= 8 g=0.04419  k=2: 0.9661   k=3: 0.9297
W=16 g=0.01562  k=2: 0.9645   k=3: 0.9267
```
Bounded as `g→0`, consistent with `≺ (W^{-d}B)^{k−1}`; at `W=2` the ratio exceeds 1, so `STKbound` fails on that constant sequence.

### Verdicts
- `hermTestFunLoopN` (and pin `HermTestFunLoopN`): PASS. Constant `k(k+1)N η^{-(k+2)}` holds at `d=3` (tight Leibniz count, observed ratio `3.1e-6`); hypotheses `0≤u<1`, `|E|<2`, `∀ n` all hold at the instance.
- `gridDriftN` (pin `GridDriftN`, `stepErrN`, `kStepC`, `uStepC`): PASS. Constants `c=Nk²`, `(W^d)⁻¹`, `envConst d …` as rows 10–12; all hypotheses hold at the instance (`s=1/2≥0`, `t=3/4<1`, `K=4≠0`, `|E|=0<2`, `j=0<4`, `k=3≥2`, `Bk` envelope, `Δ=1/16≤1`).
- `exists_norm_Kcal_le_win`: PASS with flag F1 (statement changes form: needs the owed pin `STKbound`, registered; no new axiom class). If the dispatcher refuses a hypothesis form, this target is BLOCKED (missing input: proof of `STKbound`, KL7).

## (a′) Preflight corrections — Sun Oct  4 06:31:52 UTC 2026
Row 13 / F1 of (a): "size ≥ 27" needs `3 ≤ d` (`Sizes d` allows any `d`). The Lean `exists_norm_Kcal_le_win` takes `sz.SizeTendsto` instead (`2 ≤ size n` eventually) and bounds all `w ∈ [0, v_n]` for a sequence `v` (RBM2D: all `u ≤ v`), not a sequence `u n`. No verdict changes.

## (b) Script output — Sun Oct  4 06:31:52 UTC 2026
```
$ lake build RBM3D.Induction.LoopC2N RBM3D.Induction.GridDriftN   (no warning/error line from the two files; last line, HEAD 3fc1018)
Build completed successfully (3768 jobs).
$ lake build   (full; first/last `date -u` and tail)
Sun Oct  4 06:30:46 UTC 2026
Build completed successfully (3858 jobs).
exit 0
Sun Oct  4 06:30:50 UTC 2026
$ lake env lean precheck.lean   (scratch: import RBM3D + both new modules, #assert_rbm_axioms)
exit 0:
axiom audit: 3419 theorems, 1234 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STKbound: 6 [no certificate]
$ git diff --stat main...t/T2111
 RBM3D/Induction/GridDriftN.lean | 1261 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/LoopC2N.lean    |  573 ++++++++++++++++++
 2 files changed, 1834 insertions(+)
$ git log --oneline main..t/T2111
3fc1018 T2111: shorten docstring lines
a351024 T2111: GridDriftN docstring line cites
8f6c82f T2111: Induction/LoopC2N + Induction/GridDriftN (hermTestFunLoopN, gridDriftN, exists_norm_Kcal_le_win)
3019421 T2111: Induction/LoopC2N (HermTestFunLoopN, hermTestFunLoopN)
$ grep -nE "sorry|admit|native_decide|^axiom" (the two files) | wc -l
0
```
The root `RBM3D.lean` does not import the new modules (the hub adds them at merge), so the full build's `#assert_rbm_axioms` did not see them; the pre-check does. No registry line added (`Test/Axioms.lean` untouched): no theorem takes `HermTestFunLoopN`/`GridDriftN` as a hypothesis; `exists_norm_Kcal_le_win` takes `STKbound`, already registered owed.

`#print axioms` (grep of the build output):
```
17 declarations of the two files; distinct axiom sets: {'[propext, Classical.choice, Quot.sound]'}
hermTestFunLoopN, LoopC2NCheck.instance_data, LoopC2NCheck.hermTestFunLoopN_k3_instance, LoopC2NCheck.hermTestFunLoopN_k3_same_instance, LoopC2NCheck.hermTestFunLoopN_k1_instance, kStepC, uStepC, stepErrN, GridDriftN, gridDriftN_at, gridDriftN, GridDriftN_exists_envelope, exists_norm_Kcal_le_win, GridDriftNCheck.data, GridDriftNCheck.gridDriftN_instance, GridDriftNCheck.envelope_instance, GridDriftNCheck.exists_norm_Kcal_le_win_instance
```
Target statements (script `extract.py` over the two files; `gridDriftN_at`, the single-index form, is at GridDriftN.lean:777):
```lean
def HermTestFunLoopN : Prop :=
  ∀ (k : ℕ) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)),
      HermTestFun sz n (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt E u) (loopOf σ b)) ∧
      ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
        y.IsHermitian →
        ‖fderiv ℝ (fderiv ℝ (fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt E u)
              (loopOf σ b))) M y y‖ ≤
          ((k * (k + 1) : ℕ) : ℝ) * (Sizes.size sz n : ℝ) * (etaT E u)⁻¹ ^ (k + 2) * ‖y‖ ^ 2
theorem hermTestFunLoopN : HermTestFunLoopN sz := by
def GridDriftN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n j : ℕ), j < K n → ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (Bk : ℝ), 0 ≤ Bk →
    (∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ k → ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤ Bk) →
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncN sz E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))‖
        ≤ stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n) Bk
theorem gridDriftN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : GridDriftN sz E s t K := by
theorem GridDriftN_exists_envelope {d L W : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) (hW : 1 ≤ W)
    {E : ℝ} (hE : |E| < 2) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Set.Icc (0 : ℝ) v, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      J.length ≤ k → ‖KLK d L g W E w J‖ ≤ B := by
theorem exists_norm_Kcal_le_win (hsz : sz.SizeTendsto) (E : ℕ → ℝ) (hKb : sz.STKbound E)
    (hE : ∀ n, |E n| < 2) (v : ℕ → ℝ) (hv0 : ∀ n, 0 ≤ v n) (hv1 : ∀ n, v n < 1) (m : ℕ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (v n), ∀ J : LoopIdx (Zd d (sz.L n)), J.WF →
      2 ≤ J.length → J.length ≤ m →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (E n) (v n))⁻¹) ^ m := by
```
Compiled nonempty instances (script extract; `sz0`: `d = 3`, `L_0 = 4`, `W_0 = 32`, `N = 2097152`; `LoopC2NCheck` also has `_k3_same_instance`, `_k1_instance`, `instance_data`; `GridDriftNCheck.envelope_instance` is `GridDriftN_exists_envelope` at `n = 0`, `v = 1/5`, `k = 3`):
```lean
theorem hermTestFunLoopN_k3_instance :
    HermTestFun sz0 0
        (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
          loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
            (loopOf ![true, false, true] ![0, 1, 2])) ∧
      ‖fderiv ℝ (fderiv ℝ
          (fun M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
            loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) M) (zt 0 (1 / 2))
              (loopOf ![true, false, true] ![0, 1, 2]))) 0 1 1‖ ≤
        ((3 * (3 + 1) : ℕ) : ℝ) * (Sizes.size sz0 0 : ℝ) * (etaT (0 : ℝ) (1 / 2))⁻¹ ^ (3 + 2) *
          ‖(1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)‖ ^ 2 := by

theorem gridDriftN_instance :
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ᵐ ω ∂(pathP sz0), ∀ a : Fin 3 → Zd 3 (sz0.L 0),
      ‖predIncN sz0 E0 s0 t0 K0 0 0 ![true, false, true] ω a - (gridStep s0 t0 K0 0 : ℂ) *
          (∑ l ∈ Finset.Icc 3 3, sz0.STksimLKM 0 (E0 0) (gridTime s0 t0 K0 0 0)
              (pathH sz0 s0 t0 K0 0 0 ω) l (loopOf ![true, false, true] a) +
            sz0.STelklkM 0 (E0 0) (gridTime s0 t0 K0 0 0) (pathH sz0 s0 t0 K0 0 0 ω)
              (loopOf ![true, false, true] a) +
            sz0.STegtM 0 (E0 0) (gridTime s0 t0 K0 0 0) (pathH sz0 s0 t0 K0 0 0 ω)
              (loopOf ![true, false, true] a))‖
        ≤ stepErrN 3 (sz0.L 0) (sz0.W 0) (E0 0) 3 (gridTime s0 t0 K0 0 0)
            (gridTime s0 t0 K0 0 (0 + 1)) (gridStep s0 t0 K0 0) Bk := by

theorem exists_norm_Kcal_le_win_instance (hKb : sz0.STKbound E0) :
    ∀ᶠ n in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 3 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) (1 / 2))⁻¹) ^ 3 :=
  exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num) (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) 3 1 one_pos
```
`hermTestFunLoopN`, `gridDriftN`: every hypothesis discharged. `exists_norm_Kcal_le_win`: `hKb` (the owed pin `STKbound`, limit check `check2.py` in (a)) stays a hypothesis; `SizeTendsto` is `sz0_tendsto`.

Pin diff against RBM2D `c9a24cf` (script `pindiff.py`: 2D text renamed `Z2 (d.L n)→Zd d (sz.L n)`, `d.L/d.W→sz.L/sz.W`, `spectralZ→zt`, `gloop→loopL`, `Kcal→KLK d … (sz.lam n)`, `ksimLK/elklkN/egtN→STksimLKM/STelklkM/STegtM`; then token diff):
```
=== pin HermTestFunLoopN : token diff 2D(c9a24cf, renamed) vs 3D; "-" 2D only, "+" 3D only
  delete 2D: [ NeZero k ] || 3D: -
  insert 2D: - || 3D: d   (x3)
  insert 2D: - || 3D: d ( sz.L n ) ( sz.W n )
  insert 2D: - || 3D: d   (x5)
  insert 2D: - || 3D: d ( sz.L n ) ( sz.W n )
=== pin GridDriftN : token diff 2D(c9a24cf, renamed) vs 3D; "-" 2D only, "+" 3D only
  delete 2D: [ NeZero k ] || 3D: -
  insert 2D: - || 3D: d
=== pin kStepC : token diff 2D(c9a24cf, renamed) vs 3D; "-" 2D only, "+" 3D only
  insert 2D: - || 3D: d
  replace 2D: 2 || 3D: d   (x8)
=== pin uStepC : token diff 2D(c9a24cf, renamed) vs 3D; "-" 2D only, "+" 3D only
=== pin stepErrN : token diff 2D(c9a24cf, renamed) vs 3D; "-" 2D only, "+" 3D only
  insert 2D: - || 3D: d   (x3)
  insert 2D: - || 3D: (
  insert 2D: - || 3D: ^ d )
  delete 2D: ^ 2 || 3D: -
```
Name clash, port commit and diff-stat (RBM2D read-only):
```
$ git grep -nwE "HermTestFunLoopN|hermTestFunLoopN|kStepC|uStepC|stepErrN|GridDriftN|gridDriftN|gridDriftN_at|GridDriftN_exists_envelope|exists_norm_Kcal_le_win|LoopC2NCheck|GridDriftNCheck" main -- RBM3D
main:RBM3D/Induction/Step2Defs.lean:505:DuhamelTail}`, `Induction/{LoopGenN, GridDriftN, StepDecompN, AzumaProxyN, GridAssemblyN}`): for every
(exit 0; end of matches)

$ git grep -n "LoopC2N_\|gdn_\|GridDriftN_" main -- RBM3D | wc -l
       0

$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/LoopC2N.lean RBM2D/Induction/GridDriftN.lean RBM2D/Induction/GridGoodN.lean RBM2D/Induction/HierVocab.lean
 RBM2D/Induction/GridDriftN.lean | 130 ++----
 RBM2D/Induction/GridGoodN.lean  | 847 ++++------------------------------------
 RBM2D/Induction/HierVocab.lean  | 392 ++++---------------
 RBM2D/Induction/LoopC2N.lean    | 148 +------
 4 files changed, 202 insertions(+), 1315 deletions(-)
(end)
$ grep -cE "Z2|W \^ 2|L \^ 2|KLoop\.|spectralZ|gloop" over the two files: 12 lines, all comments/docstrings or merged `norm_gloop_*` names (no d = 2 token in code)
```

Narrative:
- `LoopC2N.lean` (573 lines): the 2D proof (`LoopC2N:82`–`:441`) with the private jets of the merged `Path/StepDecompLoop.lean` copied as `LoopC2N_*`; `word_jets` is an induction on the word (`2k + k(k−1) = k(k+1)`, dimension-free); only the trace cost carries `N = (L W)^d` (`card_BlockIndex`); `‖E_b‖ ≤ (W^d)⁻¹ ≤ 1`. `0 ≤ u` is not used.
- `GridDriftN.lean` (1261 lines): tensor/`𝒰`/`𝒦` steps and assembly ported (`GDN:56`–`:656`); `thetaSig → ThetaN`, `Kcal/primRhs → KLK/treeEqRhs`, `hierarchyN → hierarchyN_holds`, `condExp_loop_drift` from `Path/LoopStep`. `𝒦` step: `c = W^d k² L^d = N k²` (`norm_primBil_le`). `𝒰` step: `uStepC` unchanged (dimension-free).
- Import cuts (no used declaration carries a `d = 2` argument; none stopped the ticket): `GridGoodN` — only `HermTestFunLoopN`, defined here (instance data: merged `sz0`); `Path/GoodEvent` — `GoodEvent_measurable_gloop` ↦ `walk_measurable_loopL`, `walk_measurable_blockMat`, `pathH_measurable_filt` (in `gdn_integrable_loopL`), `gridStep/gridTime` from `Path/Walk`; `Path/ScalesBridge` — the `Mt` chain ↦ `gdn_Bctl_le` (`W^{-d}B_{w,0} ≤ 2(1−v)⁻¹ ≤ 2η_v⁻¹`); `Loop/KBound` — no counterpart, replaced by the owed pin `STKbound`; the four row-sum helpers of the private part of `Path/UBounds` copied as `gdn_*`.
- Not ported: 2D `hΦ_of_hermTestFunLoopN_instance` (its consumer is in `GridGoodN`), 2D `gridDriftN_check` and its data `sizes/E0/s0/t0/K0` (replaced by `gridDriftN_instance` at `sz0`); `GridGoodN`'s `hermTestFunLoopN_two_pm`.
- DECISIONS §29: the pin `GridDriftN` keeps its `∀ n` hypotheses; `gridDriftN_at` needs `|E n| < 2`, `0 ≤ s n ≤ t n < 1`, `K n ≠ 0` only at `n`; `Δ ≤ 1` is derived (`gdn_time_facts`).
- New (no RBM2D analogue): `GridDriftN_exists_envelope` (finite `B` from continuity of `𝒦` on `[0,v]` and finiteness of loops of length `≤ k`), used to discharge the envelope of `gridDriftN_instance`; `exists_norm_Kcal_le_win` changes form (F1 of (a), T2111a).

## (c) Verified Mathlib names (all `#check`-ed, script `mathlib_names.lean`; names verified absent: none checked)
- `condExp_sub`: exists
- `condExp_const`: exists
- `memLp_top_of_bound`: exists
- `norm_image_sub_le_of_norm_deriv_le_segment'`: exists
- `IsCompact.exists_bound_of_continuousOn`: exists
- `Filter.eventually_all_finset`: exists
- `Filter.not_eventually`: exists
- `Filter.Frequently.and_eventually`: exists
- `tendsto_rpow_atTop`: exists
- `ENNReal.one_le_ofReal`: exists
- `Real.rpow_neg_one`: exists
- `Real.rpow_add`: exists
- `NonUnitalStarAlgHom.norm_map`: exists
- `contDiffAt_ringInverse`: exists
- `Matrix.linfty_opNNNorm_def`: exists
- `inv_anti₀`: exists
- `one_le_inv₀`: exists
- `ae_all_iff`: exists
- `measure_univ`: exists
- `measure_mono`: exists

## (d) Open issues and paper-delta candidates
- **T2111a** (`exists_norm_Kcal_le_win`): RBM2D proves it uniformly in `(L,W,E,u,v)` from `Kbound_prec_uncond`; here it is along a size sequence, conditional on the owed `STKbound sz E` (KL7) and `SizeTendsto`, for all `w ∈ [0,v_n]`. Consumer ST2-31 must use this form. If the dispatcher refuses the hypothesis form, this target is BLOCKED on a proof of `STKbound`.
- **T2111b**: `[NeZero k]` dropped from `HermTestFunLoopN` and `GridDriftN` (D204 precedent; strictly stronger; `k = 0` is covered by the proof).
- **T2111c**: `GridDriftN_exists_envelope` is new (a pointwise-in-`n` deterministic envelope; not a paper statement).
- **T2111d**: `stepErrN`/`kStepC` are Lean-only intermediates with `W^d`, `L^d` (pin diff above); the paper has no corresponding statement.
- `STKbound` is unproved (KL7). By the script `check2.py` of (a), at `W = 2`, `k = 2` the ratio is `1.0786 > 1`, so a constant `(L,W) = (3,2)` sequence cannot carry it; `sz0` has `W_0 = 32`.
- Branch `t/T2111` has 4 commits touching only the two writable files (`git diff --stat` above).
