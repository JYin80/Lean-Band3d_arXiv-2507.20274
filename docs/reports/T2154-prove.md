Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 18:49:00 UTC 2026

Sources read: RBM2D `Induction/GridGoodN.lean:233-530` and `Induction/GridAssemblyN.lean` at `c9a24cf` (the RBM2D working tree is at `9e0f275`, different; every line number below is `c9a24cf`); merged `RBM3D/Induction/{StepDecompN,LoopC2N,GridDuhamelN,GridGoodN,QVN}.lean`, `Kernel/Evolution.lean`, `Path/{Azuma,Markov}.lean`.

### (i) Exponent table, dictionary, pins, consumers

| # | Item | Value / form | Constraint | Slack / comment |
|---|---|---|---|---|
| 1 | Grid exponent `C_K` (AssembledN) | `D₁+4D+k+2C_P+8 ≤ C_K` (same as RBM2D `GridGoodN:492-502`) | `0 ≤ C_K` | unchanged: `d` enters only through the label count (row 2). Instance `k=3,D=D₁=1,C_P=0`: `16 ≤ 17`, slack 1 |
| 2 | Label count `Lc = card(Fin k → Zd d L)` | old `(L·L)^k ≤ N^k`, `N=(WL)^2`; new `(L^d)^k ≤ N^k`, `N=(WL)^d` (`Sizes.size`, `Defs/Sizes.lean:157`) | `L^d ≤ (WL)^d` from `W ≥ 1` (`W_pos`); true for every `d` | exponent `k` unchanged; at `sz0,n=0,k=3`: `2^18 ≤ 2^63` |
| 3 | Azuma budget (`zBudget`) | `4 K Lc e^{-(N^ε)²/4} ≤ N^{-D₁}/2`, from `K ≤ 2N^{C_K}`, `Lc ≤ N^k`; needs `ln(16 N^{C_K+k+D₁}) ≤ N^{2ε}/4` | eventual in `N`, any `ε>0`; `SizeTendsto sz` supplies it | at `ε=1`,`C_K=17,k=3,D₁=1`: holds for `N ≥ 15.6`; `N_0=2^21` far above |
| 4 | `Y` budget (`yBudget`) | `Lc·88ΔP²/(N^{-D})⁴ ≤ N^{-D₁}/2`; exponent `k−C_K+2C_P+4D+D₁ ≤ −8` and `176 N^{-8} ≤ 1` (`N ≥ 1.91`) | row 1 is exactly this | instance exponent `-9` (slack 1) |
| 5 | Moment budget | `(K+1)·4(8V²+3W) ≤ 88ΔP²` from `v ≤ Δ²P, w ≤ Δ⁴P², KΔ ≤ 1, 1 ≤ K` | pure arithmetic, `d`-free | none |
| 6 | Azuma tail (`stoppedAzumaZN`) | `P(x ≤ ‖Σ_{j<min(m,τ)} 𝒰 Z_j‖) ≤ 4 exp(-x²/(4 Σ_{j<m} c_j))` = merged `azuma_complex` (`Path/Azuma.lean:87`) | `d`-free | at `x=8`, `Σc=4`: `4e^{-4}=0.0733<1` |
| 7 | Coarse kernel row sum (the `(1+(1-u_m)⁻¹)^k` of AssembledN, and `729`) | `‖uKer μ v w‖ ≤ 1+(1-w)⁻¹` for `0≤v,w<1`, **no order `v ≤ w`**: `uKer_eq_one_add` (`Kernel/Evolution.lean:90`, needs only `‖wμ‖<1`) + `norm_Theta_le` + `norm_SB`, `\|w-v\| ≤ 1`; the merged `norm_uKer_le`/`norm_UN_apply_le` (`:114,:131`) need `s ≤ t` and `u` is not monotone in `AssembledN`, so they do not apply | `‖μ‖ = 1` (`norm_mSigma`, `\|E\|≤2`) | row sum over `Fin k` slots `≤ (1+(1-u_m)⁻¹)^k`; `d`-free, `g`-sign-free |
| 8 | **The `729`** (RBM2D `GridAssemblyN_witProxy`) | `729 = ((1+(1-u_m)⁻¹)^k)²` at `k=3`, `u_m ≤ 1/2`: `(1+2)^6`. **Not a `(2d+1)`/`3^d` count**: `d` does not enter | `Re²,Im² ≤ ‖ρ‖²` | at the 3D data `u_m ≤ 1/16, k=3`: `(31/15)^6 = 77.92`, constant `78` |
| 9 | `YMomentsN` | `∃ C_P` placed after `K` (inside `YMomentsConclN`); `d` enters only through `N=(WL)^d` in `C₂ = k(k+1)Nη^{-(k+2)}` (merged `HermTestFunLoopN`) | true; but `C_P` may depend on `K` | **consumers cannot use it**: `AssembledN` needs `C_P` before `C_K` (hence `K`); RBM2D uses the primed `YMomentsUnifN` (`AzumaProxyN:2042` of a 2469-line file; portmap row 1 keeps 1540 lines for ST2-34/35, so check it is in range): the dispatcher should add it to ST2-34/35 |
| 10 | `RangeCond` (in `YMomentsN`) | merged `sz.RangeCond δ t := ∀ᶠ n, N^{-1+δ} ≤ 1-t n` (`Green/Pins.lean:55`) = RBM2D `Step2Props:121` | — | identical form |
| 11 | `SizeTendsto` | `N_n = 2^21 (n+1)^18 → ∞` at `sz0` (`sz0_tendsto`, `Defs/Sizes.lean:300`) | necessary: `W≡1,L≡3` gives bounded `N`, Azuma tail `4e^{-N^{2ε}/4}` a positive constant | limit computed in (ii) |

**Dictionary** (`d : Sizes` → `{d} (sz : Sizes d)`): `Z2 (d.L n)`→`Zd d (sz.L n)`; `Coord L W`→`CoordF d L W`; `gvar L W c`→`gvarF d L W (sz.lam n) c`; `coordinateMatrix L W c`→`coordinateMatrix d L W c` (`Gauss/FineModel.lean:384`); `Ugen (d.L n) E σ v w`→`Ugen d (sz.L n) (sz.lam n) E σ v w` (`GridDuhamelN.lean:65`, `= UN` with `cycProd = m(σ_i)m(σ_{i+1})` via `finRotate`); `ukerMat L (mSig*mSig) v w`→`uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w` (`= ukerMat`, `rfl`); `eeN L W E v M σ b b'`→`sz.STeeM n E v M σ b b'` (`Step2Defs:757`); `HermTestFun d n Φ`→`HermTestFun sz n Φ`; `SizeTendsto d`→`sz.SizeTendsto`; `RangeCond d τ' t`→`sz.RangeCond τ' t`; `d.size`→`sz.size`; `[NeZero k]` dropped as in merged `SubGaussStopN` (`Fin k → Zd d L` is nonempty for every `k`; paper-delta candidate `T2154a`).

**Pins and status.** Merged: `dirDerivN, ZfamN, ZvecN, YvecN, stoppedEdgeN, SubGaussFormN, SubGaussStopN` (`StepDecompN:168-215`), `HermTestFunLoopN` (`LoopC2N:453`). Ported here as statements: `StoppedAzumaZN`, `YMomentBoundsN`, `GridAssemblyHypN`, `AssembledN`; **proved here**: `stoppedAzumaZN`, `assembledN`. Statement only, proofs owed to ST2-34/35: `AzumaSubGN`, `YMomentsN` (`YMomentsConclN`). `qvFormN` (a definition): 3D form `Re Σ_{b,b'} κ_b conj(κ_{b'}) sz.STeeM n E v M σ b b'` with `κ_b = ∏_i uKer … (a i) (b i)`, exactly the right side of the merged `QVPropagatedN` (`QVN.lean:799`, which carries the factor `k`, as RBM2D `qv_at_propagator`). RBM2D `GridGoodN §6` (`azumaSubG_ugen`, `qv_at_propagator`, ...) is not in any target of this ticket.

**Consumers** (RBM2D at `c9a24cf`): `NonAltGood` (`GridAssemblyHypN` fields, `AzumaSubGN` via `subGaussStop_nonAlt`, `qvFormN`); `NonAltEnd`, `AltEnd`, `AltEndCompose`, `AltDriftQ` (`assembledN`, `YMomentBoundsN`, `GridAssemblyHypN`); `AltProxyQ` (`qvFormN` with `𝒬`, `YMomentBoundsN`); `PPVocab`, `PPCondVar` (`assembledN`, `GridAssemblyHypN`, `AzumaSubGN`, `qvFormN`, `YMomentsUnifN`); `AzumaProxyN` (proves `AzumaSubGN`, `YMomentsN`; uses `YMomentBoundsN`). `StoppedEndDefs` is not ported (portmap F16).

**Levels of the merged `GoodSetN` (T2146a/b) against `hdrift`/`hDcls`.** `GridAssemblyHypN` has `Dr, dDrift, δD, Cls` abstract, so the pin does not change. The consumer (S3-10) takes `Dr_j = Σ_{l=3}^k STksimLKM_l + STelklkM + STegtM` at `(u_j,H_j)` (the very sum of GoodSetN clause 7). Clauses 3-5 give `‖Dr_j(b)‖ ≤ dDrift = Γ(ΓΦ)(B_{u_j}^k/η_{u_j})·((k-1) + kΓΦ)` (`(k-2)+1` copies of `Γ(ΓΦ)B^k/η`, plus `Γ k (ΓΦ)² B^k/η`), `≥ 0`, with **no additive `W^{-D'}`**; RBM2D `dDriftNonAlt` was `((k-1)²+1)Γ²Φ M^{-k}η^{-1} + 2W^{-D'}`. `hDcls`: clause 7 (far, `ell_{u_j} W^{τ'} ≤ STdiamInf a`) gives `δD = W^{-D'}`; the class index `j+1` needs `ellT_u_j ≤ ellT_u_{j+1}` (`ellT_mono`, `Kernel/PropT.lean:58`, hypothesis `0 ≤ sz.lam n`, not a field of `Sizes`: S3-10 needs it as hypothesis or the direct argument `g<0 ⇒ ellT = min 1 L`). Fits; the changes are in the consumer's `dDrift` formula, not here.

### (ii) One concrete nondegenerate instance (`d=3`, `sz0`, `n=0`)

Data: `L=4, W=32, N=2^21`, `k=3`, `σ=(+,+,-)`, `E≡1/2`, `ε=1`, `D=D₁=1`, `C_P=0`, `C_K=17`, window `(s,t)=(sInst,tInst)=(0,1/16)` (`Induction/Defs.lean:439-440`), `K_n=N_n^{17}`, `Δ=(t-s)/K`, `τ≡K`, `P=1`, `v=Δ²`, `w=Δ⁴`, `Y=R=0`, `Dr≡0`, `A_0≡1`, `Cls≡True`, `Z_j=√Δ·Re tr X_{j+1}` (not zero: `markov_linTrVar_one_pos`, `Path/Markov.lean:694`), proxy `c=78Δ·linTrVar(1)+1>0` (row 8; `SubGaussStopN` proved from `hasCondSubgaussianMGF_linear`, `Path/Markov.lean:636`, `𝒰(const)=ρ·const`), `hexp` by defining `A_m` as the right side. `K` is only a bound, never enumerated; it is forced: `KΔ ≤ 1` and `Δ ≤ N^{-C_K}` with window `1/16` give `K ≥ N^{C_K}/16` (RBM2D `GridAssemblyN_assembledN_instance_random` also uses `K=gridK`, `C_K=138`). The alternative with `K=1`, `t=N^{-17}` has a collapsed window and is not used.
**The merged `Kg≡4, vg≡1/32` (`Δ=1/128`) cannot serve `assembledN`**: it needs `Δ ≤ N^{-C_K}` with `C_K ≥ 8+k`; it serves `stoppedAzumaZN` (`m=τ≡4`, `c≡1`, `x=8`, `hsub` stays the ST2-34/35 hypothesis).

Command: `python3 scratchpad/T2154/inst.py` (the script is outside the repository; output verbatim):
```
n=0: L,W,N = 4 32 2097152 = 2^21 (sz0_values: 2097152) True
N_n == 2^21 (n+1)^18 for n<=2000: True
N_n at n=1,10,100: [549755813888, 11659991713824860234842112, 2508503070931240586116700541954360451530752]  N_n>=n+1: True
k=3: Lc=(L^d)^k = 262144 <= N^k = 9223372036854775808 True  (ratio W^{dk} = 35184372088832 = 35184372088832 )
D1+4D+k+2CP+8 = 16 <= C_K = 17 slack 1
1<=K: True  K<=ceil(N^CK): True  Delta<=N^-CK: True  K*Delta = 1/16 <=1: True  log2 K = 357.0  log2 Delta = -361.0
P=1<=N^CP=N^0=1: True ; v_j=Delta^2 P, w_j=Delta^4 P^2 (satisfy v<=Delta^2 P, w<=Delta^4 P^2 with equality)
u_0,u_K = 0 1/16 both in [0,1): True
Z-budget (nats): ln(16 N^(CK+k+D1)) = 308.5  <= N^(2eps)/4 = 1099511627776.0 True
smallest real N with Z-budget (eps=1,CK=17,k=3,D1=1) = 15.542  (N_0 = 2^21 is far above)
Y-budget exponent k-CK+2CP+4D+D1 = -9  (<= -8 required) ; 176*N^e = 2.2430734108744928e-55  <=1
N^8>=176 needs N>= 1.908
coarse (1+(1-u_m)^-1) at u_m<=1/16 = 31/15 ; ^k = 29791/3375 ; squared = 887503681/11390625 = 77.91527514951989  -> proxy constant 78 >= 77.91527514951989 True
2D witness: u_m<=1/2,k=3: (1+2)^(2*3) = 729
alternative sharp row sum ((1-s)/(1-t))^k needs s<=t; (16/15)^(2k) = 1.472896877914952
merged Kg=4: Delta=1/128; largest C_K with Delta<=N^-C_K at N=2^21: 0.3333333333333333  vs required C_K>=D1+4D+k+2CP+8 >= 8+k = 11   -> merged Kg unusable for assembledN
stoppedAzumaZN bound 4 exp(-x^2/(4*sum c)) at x=8, sum c=4: 0.07326255555493671 <1: True
```
External hypothesis `SizeTendsto sz0`: `N_n = ((2(n+1))^5·4(n+1))^3 = 2^21 (n+1)^18 ≥ n+1 → ∞` (lines 2-3 of the output; the Lean proof is the merged `sz0_tendsto`). `hexp, hker, hA0cls, hdrift, hDcls` are discharged by the definitions above (`κ_{im} = (1+(1-u_m)⁻¹)^k`, `εK = 0`, `dDrift = δD = 0`).

### Verdicts
- Target 1 (pins, dictionary): PASS (no pin changes beyond the dictionary; `[NeZero k]` dropped; `YMomentsN` kept verbatim, finding in row 9).
- Target 2 (`stoppedAzumaZN`, `assembledN`): PASS; the coarse kernel bound must be re-derived without `s ≤ t` (row 7), constants unchanged, `729` is `k`-/`u_m`-dependent, not `d`-dependent.
- Target 3 (instances): PASS with the grid `K_n=N_n^{17}` for `assembledN`, not the merged `Kg≡4` (above).

## (b) Script output (scripts in scratchpad/T2154/, outside the repository; assembled Sun Oct  4 19:51:33 UTC 2026)

### Branch and build
$ git log --format="%h %ad %s" --date=iso main..t/T2154; git status --short | wc -l
20bd020 2026-10-04 12:19:22 -0700 T2154: lint cleanup in the instances
b02e3c1 2026-10-04 12:18:31 -0700 T2154: free constant proxy in the Azuma/zvec instances
3fc4584 2026-10-04 12:16:01 -0700 T2154: GridAssemblyN pins, stoppedAzumaZN, assembledN, instances (ST2-33)
       0
Sun Oct  4 19:49:06 UTC 2026
$ lake build RBM3D.Induction.GridAssemblyN 2>&1 | grep -E "GridAssemblyN.lean:[0-9]+:[0-9]+: (warning|error)|^(warning|error).*GridAssemblyN|Build completed|Replayed RBM3D.Induction.GridAssemblyN|Built RBM3D.Induction.GridAssemblyN"
exit 0
ℹ [3784/3784] Replayed RBM3D.Induction.GridAssemblyN
Build completed successfully (3784 jobs).
$ lake build ... | python3 axsum.py   (lines "depends on axioms" of GridAssemblyN.lean)
#print axioms lines of GridAssemblyN.lean: 17; exactly [propext, Classical.choice, Quot.sound]: 17; others: []
  stoppedAzumaZN, assembledN, gridAsm_stronglyMeasurable_ZvecN, gridAsm_stronglyMeasurable_YvecN,
  GridAssemblyNInst.gridAsm_stoppedAzumaZN_instance, GridAssemblyNInst.gridAsm_stoppedAzumaZN_bound_lt_one,
  GridAssemblyNInst.gridAsm_stoppedAzumaZN_instance_concrete, GridAssemblyNInst.gridAsm_grid_data,
  GridAssemblyNInst.gridAsm_witSubGaussStop, GridAssemblyNInst.gridAsm_witAzuma, GridAssemblyNInst.gridAsm_bundle,
  GridAssemblyNInst.gridAsm_assembledN_instance_gen, GridAssemblyNInst.gridAsm_assembledN_instance_random,
  GridAssemblyNInst.gridAsm_witZ_ne_zero, GridAssemblyNInst.gridAsm_witZ_zero, GridAssemblyNInst.gridAsm_witA_ne,
  GridAssemblyNInst.gridAsm_assembledN_instance_zvec
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^private axiom" RBM3D/Induction/GridAssemblyN.lean | wc -l
       0
    2306 RBM3D/Induction/GridAssemblyN.lean
$ git diff --stat main...t/T2154; wc -l RBM3D/Induction/GridAssemblyN.lean
 RBM3D/Induction/GridAssemblyN.lean | 2306 ++++ ; 1 file changed, 2306 insertions(+); 2306 lines

### Registry pre-check (`import RBM3D; import RBM3D.Induction.GridAssemblyN; #assert_rbm_axioms`) and full build (RBM3D.lean given `import RBM3D.Induction.GridAssemblyN` after line 197 for the run, then restored: `git status --short` empty)
Sun Oct  4 19:44:00 UTC 2026  (reg0.out/reg.out; `lake env lean` of the two-line files)
without the module: axiom audit: 4659 theorems, 1662 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
with the module:    axiom audit: 4709 theorems, 1677 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
full `lake build` (Sun Oct  4 19:45:13 UTC 2026 to Sun Oct  4 19:45:34 UTC 2026; `lake build 2>&1 | grep -E "error|Build completed|axiom audit:|premises found|registry:"`): exit 0; Build completed successfully (3919 jobs). premises found by scanning: 86 (borrowed 0, owed 66, structural 20). no `error` line.

### Pins against RBM2D `GridGoodN.lean:297-530` at `c9a24cf` (token diff after the dictionary; `qvFormN` hunks joined by `;`)
== StoppedAzumaZN: RBM2D tokens 220 (after dictionary), RBM3D tokens 220, differing hunks 0
== qvFormN: RBM2D tokens 121 (after dictionary), RBM3D tokens 131, differing hunks 14
   replace: [(L W] -> [(n]; delete: [[NeZero L] [NeZero W]] -> []; replace: [L W)] -> [d (sz.L n) (sz.W n))]; replace: [L W)] -> [d (sz.L n) (sz.W
   n))]; replace: [Z2 L)] -> [Zd d (sz.L n))]; replace: [Z2 L,] -> [Zd d (sz.L n),]; replace: [Z2 L,] -> [Zd d (sz.L n),]; replace: [ukerMat L
   (KLoop.mSig] -> [uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma]; insert: [] -> [i))]; delete: [* KLoop.mSig E (σ (i + 1)))] -> []; replace:
   [ukerMat L (KLoop.mSig] -> [uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma]; insert: [] -> [i))]; delete: [* KLoop.mSig E (σ (i + 1)))] ->
   []; replace: [eeN L W] -> [sz.STeeM n]
== AzumaSubGN: RBM2D tokens 203 (after dictionary), RBM3D tokens 203, differing hunks 0
== YMomentBoundsN: RBM2D tokens 278 (after dictionary), RBM3D tokens 278, differing hunks 0
== YMomentsConclN: RBM2D tokens 135 (after dictionary), RBM3D tokens 135, differing hunks 0
== YMomentsN: RBM2D tokens 91 (after dictionary), RBM3D tokens 91, differing hunks 0
== GridAssemblyHypN: RBM2D tokens 546 (after dictionary), RBM3D tokens 546, differing hunks 0
== AssembledN: RBM2D tokens 491 (after dictionary), RBM3D tokens 491, differing hunks 0

### Target statements (copied from the file by script)
-- stoppedAzumaZN (sig) at line 1014
theorem stoppedAzumaZN (E s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedAzumaZN sz E s t K := by
-- assembledN (sig) at line 1605
theorem assembledN : AssembledN sz := by
-- StoppedAzumaZN (full) at line 87
def StoppedAzumaZN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ),
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ (m : ℕ), m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      (∀ j < m, SubGaussStopN sz (E n) σ (gridTime s t K n) τ
        (fun j ω => ZvecN sz E s t K n j σ ω) m a j (c j)) →
      ∀ x : ℝ, 0 ≤ x →
        (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              (ZvecN sz E s t K n j σ ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))
-- AssembledN (full) at line 227
def AssembledN : Prop :=
  sz.SizeTendsto → ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ (D D₁ C_P C_K : ℝ), 0 ≤ C_K →
    D₁ + 4 * D + (k : ℝ) + 2 * C_P + 8 ≤ C_K →
    ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
      (Δ : ℝ) (Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop)
      (A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ sz → ℝ)
      (c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      1 ≤ K → K ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊ →
      Δ ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 →
      0 ≤ P → P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
      (∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j)) →
      (∀ m ≤ K, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
        SubGaussStopN sz E σ u τ Z m a j (c m a j)) →
      GridAssemblyHypN sz E σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Zd d (sz.L n),
          ‖A m ω a‖ ≤
            κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) +
            εK 0 m * δ0 +
            Δ * ∑ j ∈ Finset.range m,
              (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) +
            ((sz.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) +
            ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j
pin definitions in the file: qvFormN@105, AzumaSubGN@122, YMomentBoundsN@141, YMomentsConclN@159, YMomentsN@173, GridAssemblyHypN@183, AssembledN@227

### Compiled nonempty instances (`d = 3`, `sz0`; theorems of the file, axioms above)
-- gridAsm_stoppedAzumaZN_instance_concrete (sig) at line 1711
theorem gridAsm_stoppedAzumaZN_instance_concrete (C : ℝ≥0) (hC : 0 < C)
    (hsub : ∀ j < Kg 0, SubGaussStopN sz0 (gridAsm_E 0) ![true, true, false]
      (gridTime sInst vg Kg 0) (fun _ => Kg 0)
      (fun j ω => ZvecN sz0 gridAsm_E sInst vg Kg 0 j ![true, true, false] ω) (Kg 0)
      (fun _ => 0) j C) :
    (pathP sz0).real {ω | 4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min (Kg 0) (Kg 0)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (gridAsm_E 0) ![true, true, false]
            (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 (Kg 0))
            (ZvecN sz0 gridAsm_E sInst vg Kg 0 j ![true, true, false] ω) (fun _ => 0)‖} ≤
      4 * Real.exp (-4) := by
-- gridAsm_assembledN_instance_random (sig) at line 2137
theorem gridAsm_assembledN_instance_random :
    ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz0),
      (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
      ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
        ‖Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) ![true, true, false]
            (gridTime sInst tInst gridAsm_K n 0) (gridTime sInst tInst gridAsm_K n m)
            (fun _ => (1 : ℂ)) a +
          ∑ j ∈ Finset.range m, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) ![true, true, false]
            (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
            (gridAsm_witZvec n j ω) a‖ ≤
          (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * Real.sqrt (m * gridAsm_witProxy n) +
            ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
-- gridAsm_witZ_ne_zero (sig) at line 2185
theorem gridAsm_witZ_ne_zero (n j : ℕ) :
    ∃ ω : PathΩ sz0, gridAsm_witZ n j ω ≠ 0 := by
gridAsm_witSubGaussStop (line 1911): `SubGaussStopN` for the random `Z` at proxy `78 Δ linTrVar + 1` is proved. gridAsm_witAzuma (1988): the stopped Azuma tail for the random `Z`, no hypothesis.
gridAsm_assembledN_instance_random = `assembledN sz0 sz0_tendsto 3 1 _ 1 1 0 17 …` via `gridAsm_assembledN_instance_gen`; SizeTendsto, `1 ≤ K ≤ ⌈N^17⌉`, `Δ ≤ N^-17`, `KΔ = 1/16`, `P = 1 ≤ N^0`, `hτmeas`, `hZmeas`, `hsubG`, `GridAssemblyHypN` (`gridAsm_bundle`) all discharged.
gridAsm_assembledN_instance_zvec (2244): `Z = ZvecN` (`hZmeas` from `gridAsm_stronglyMeasurable_ZvecN`); only `SubGaussStopN` for `ZvecN` (ST2-34/35) stays a hypothesis. `example`s at 2277-2282 check the types of the targets against the pins.

### Name clash and ports
$ git show main:RBM3D/Induction/GridGoodN.lean | grep -c stronglyMeasurable_ZvecN   # the merged GridGoodN lacks the measurability lemmas
0
44 public names; main = 3013163 ; hits: [('YMomentsN', ['main:RBM3D/Induction/LoopC2N.lean:450:`azumaSubG_ugen` and of `YMomentsN` (`C₂` in `stepDe'])]
44 public names; hits outside the file: [('YMomentsN', ['RBM3D/Induction/LoopC2N.lean:450:`azumaSubG_ugen` and of `YMomentsN` (`C₂` in `stepDecompN`).  Differences from RBM2D: `Z2 → Zd d`,'])]
RBM2D HEAD 9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/GridGoodN.lean RBM2D/Induction/GridAssemblyN.lean   (the cited text is `c9a24cf`, not HEAD)
 2 files changed, 129 insertions(+), 1439 deletions(-)
RBM1D HEAD de0de42
$ git -C ../RBM1D --no-optional-locks diff --stat c06b103 HEAD -- RBM1D/Gauss/{GridAssemblyV2,GridDuhamelTail,GridAssembly}.lean RBM1D/Hierarchy/SumZeroDyn.lean
 4 files changed, 80 insertions(+), 1204 deletions(-)
RBM1D declarations cited in the docstrings found at the cited line of `c06b103` (`git show`+`grep -nE`, 16 names): 16 of 16
Port map (`gridAsm_` omitted; `@` line in RBM3D; GA = RBM2D `GridAssemblyN.lean`, GG = `GridGoodN.lean` at `c9a24cf`, helper names there are `GridAssemblyN_*`/`GridGoodN_*`):
  abs_le_B1@266<-GA:64; abs_mul_le_B@271<-GA:69; abs_sq_le_B@276<-GA:74; abs_cube_mul_le_B@280<-GA:78; abs_sq_mul_sq_le_B@291<-GA:89;
  pow4_add_le@296<-GA:94; pow4_add_le_eight@300<-GA:98; moment4_step@309<-GA:107; mart_moment4@411<-GA:209; prependZero@461<-GA:259;
  sum_range_succ_prependZero@465<-GA:263; azuma_step@475<-GA:273; stronglyMeasurable_Ugen_apply@556<-GA:355; Ugen_four@566<-GA:365;
  norm_uKer_le@586<-new (cf. GA:410-449); norm_Ugen_coarse@616<-GA:462; tendsto_of_rat@661<-GG:732; measurable_deriv_zero@708<-GG:779;
  det_line_analytic@758<-GG:829; inv_line_regular@777<-GG:848; foldr_continuousAt@797<-GG:868; loopL_line_regular@812<-GG:881 `gloop_line_regular`;
  measurable_loopDerivN@851<-GG:915; measurable_coord@876<-GA:1267; measurable_pair@886<-GG:948; measurable_ZvecN_apply@897<-GG:959;
  measurable_AvecN@907<-new; measurable_martIncN_apply@915<-GG:968; stronglyMeasurable_ZvecN@927<-GG:981; stronglyMeasurable_YvecN@937<-GG:990;
  azuma_Ugen@959<-GA:513; gridStep_nonneg@988<-new; gridTime_nonneg@993<-new; gridTime_le@998<-new; stoppedAzumaZN@1014<-GA:548;
  eventually_exp_small@1028<-GA:562; zBudget@1054<-GA:588; moment4_budget_le@1093<-GA:627; yBudget@1144<-GA:678; norm_pow4_le_re_im@1196<-GA:730;
  stronglyMeasurable_stoppedEdgeN@1205<-GA:739; stopped_sum_eq@1216<-GA:750; moment4_fixed@1232<-GA:766; moment4_union@1296<-GA:830;
  core@1378<-GA:912; card_label@1578<-GA:1111; assembledN@1605<-GA:1140; stoppedAzumaZN_bound_lt_one@1687<-new; gridTime_bounds@1784<-new;
  hasCondSubG_mono@1870<-GA:1277; hasCondSubG_const_mul@1884<-GA:1292; Ugen_const@1902<-GA:1373; linTr_one_single@2157<-GA:1619

### Notes (checked against the blocks above; Sun Oct  4 19:52:14 UTC 2026)
1. `RBM3D/Induction/GridAssemblyN.lean` (imports `GridGoodN`, `StepDecompN`, `GridDuhamelN`, `LoopC2N`) holds the eight pins, the targets `stoppedAzumaZN` and `assembledN`, the instances (namespace `GridAssemblyNInst`) and the public `gridAsm_stronglyMeasurable_ZvecN/YvecN` (RBM2D `GridGoodN:981-996`; not in the merged `GridGoodN`, see `grep -c` above; the pin `AssembledN` asks `hZmeas` for `Z = ZvecN`). Other helpers are `private` or `gridAsm_*`.
2. The seven pins other than `qvFormN` are equal to RBM2D's after the dictionary (0 hunks); `qvFormN` differs by dictionary hunks only (`ukerMat L (m m')` is `uKer d L g (cycProd m i)`, `eeN` is `STeeM`), and it carries no factor `k`, unlike the right side of the merged `QVPropagatedN` (`QVN.lean:799`). `[NeZero k]` is dropped everywhere (T2154a).
3. `d` enters only through `N = (W L)^d`: `gridAsm_card_label` gives `|Fin k → Zd d L| = (L^d)^k ≤ N^k`, so the exponent count `D₁ + 4D + k + 2C_P + 8 ≤ C_K` is RBM2D's. The `729 = (1+2)^6` of the RBM2D instance proxy depends on `k` and `u_m`, not on `d`; the instance proxy is `78 Δ linTrVar + 1` (`gridAsm_witProxy`), `78 ≥ ((31/15)^3)^2 = 77.915…` ((a) row 8).
4. The coarse kernel bound is re-derived without `s ≤ t` (`gridAsm_norm_uKer_le`, `gridAsm_norm_Ugen_coarse`): the merged `norm_uKer_le` (`Kernel/Evolution.lean:114`) needs `s ≤ t`, and `u` is not monotone in `AssembledN` ((a) row 7).
5. `AzumaSubGN` and `YMomentsN` (`YMomentsConclN`) are statements only (ST2-34/35). No theorem of the file takes either as a hypothesis, so the premise scan finds 86 premises with and without the module (registry block above); `RBM3D/Test/Axioms.lean` is unchanged.
6. `assembledN` instance: window `(0, 1/16)`, `K_n = N_n^17`, `C_K = 17`, `k = 3`, `ε = 1`, `D = D₁ = 1`, `C_P = 0`, `Z_j = √Δ Re tr X_{j+1}` (not zero: `gridAsm_witZ_ne_zero`, `gridAsm_witA_ne`), `SubGaussStopN` proved, `hexp` by the definition of `A_m`; no unproved pin remains. The merged `Kg ≡ 4`, `vg ≡ 1/32` (`Δ = 1/128`) cannot serve `assembledN` (`Δ = 1/128 ≤ N^{-C_K}` at `N = 2^21` holds only for `C_K ≤ 1/3`, (a) script output, while the instance has `C_K = 17`), so `stoppedAzumaZN` is instantiated on it with `hsub` (the output of `AzumaSubGN`) as the hypothesis.
7. Levels of the merged `GoodSetN` clauses against `hdrift`/`hDcls` ((a), end of (i)): `GridAssemblyHypN` keeps `Dr, dDrift, δD, Cls` abstract, so the pin did not change; nothing in this file depends on them.

## (c) Verified Mathlib names
$ lake env lean scratchpad/T2154/mathlib_used.lean   # every identifier token of the file (comments removed) resolved by `resolveGlobalConst` under the file's `open`s; kept those that are theorems of Mathlib/core (242 after dropping the tactic names by_cases by_contra congr symm trans trivial). Names verified absent: none recorded.
Dotted names (137):
  Complex.abs_im_le_norm, Complex.abs_re_le_norm, Complex.continuous_ofReal, Complex.im_sum, Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_real, Complex.ofReal_sub,
  Complex.re_sum, Continuous.matrix_trace, ContinuousAt.comp, ContinuousInv₀.continuousAt_inv₀, Filter.Eventually.of_forall, Filter.eventually_ge_atTop,
  Filter.eventually_gt_atTop, Finset.analyticAt_fun_prod, Finset.analyticAt_fun_sum, Finset.card_range, Finset.card_univ, Finset.le_sup', Finset.mem_univ,
  Finset.mul_sum, Finset.prod_const, Finset.prod_le_prod₀, Finset.prod_nonneg, Finset.prod_univ_sum, Finset.range_mono, Finset.stronglyMeasurable_fun_sum,
  Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_congr, Finset.sum_const, Finset.sum_le_sum, Finset.sum_le_sum_of_subset_of_nonneg, Finset.sum_mul,
  Finset.sum_nonneg, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_succ', Finset.univ_nonempty, Fintype.card_fin, Fintype.card_fun,
  Fintype.piFinset_univ, Function.comp_apply, List.foldr_cons, Matrix.add_apply, Matrix.det_apply, Matrix.diag_apply, Matrix.ext,
  Matrix.nonsing_inv_apply_not_isUnit, Matrix.nonsing_inv_eq_ringInverse, Matrix.one_mul, Matrix.smul_apply, Matrix.submatrix_add, Matrix.submatrix_smul,
  Measurable.of_eval, Measurable.of_eval_matrix, Measurable.stronglyMeasurable, MeasurableSet.const, MeasurableSet.univ, MeasureTheory.StronglyMeasurable.limUnder,
  MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto, MeasureTheory.ae_iff, MeasureTheory.ae_of_all, MeasureTheory.condExp_mul_of_stronglyMeasurable_left,
  MeasureTheory.integrable_condExp, MeasureTheory.integrable_const, MeasureTheory.integral_add, MeasureTheory.integral_condExp, MeasureTheory.integral_congr_ae,
  MeasureTheory.integral_const_mul, MeasureTheory.integral_mono, MeasureTheory.integral_mono_ae, MeasureTheory.integral_nonneg, MeasureTheory.integral_zero,
  MeasureTheory.measureReal_biUnion_finset_le, MeasureTheory.measureReal_iUnion_fintype_le, MeasureTheory.measureReal_mono, MeasureTheory.measureReal_union_le,
  MeasureTheory.measure_ne_top, MeasureTheory.mul_meas_ge_le_integral_of_nonneg, MeasureTheory.stronglyMeasurable_const, Metric.continuousAt_iff,
  Metric.eventually_nhds_iff, Metric.tendsto_nhdsWithin_nhds, NNReal.coe_mul, NNReal.coe_pos, NNReal.coe_sum, Nat.add_sub_cancel, Nat.card_Icc, Nat.cast_le,
  Nat.cast_ne_zero, Nat.cast_nonneg, Nat.cast_pos, Nat.cast_pow, Nat.ceil_lt_add_one, Nat.ceil_natCast, Nat.le_mul_of_pos_left, Nat.le_succ, Nat.mul_pos,
  Nat.pow_le_pow_left, Nat.zero_le, NormOneClass.norm_one, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, ProbabilityTheory.mgf_const_mul, Prod.mk.injEq,
  Rat.cast_ne_zero, Rat.cast_zero, Rat.dist_eq, Real.add_one_lt_exp, Real.coe_toNNReal, Real.dist_eq, Real.exp_neg, Real.exp_pos, Real.norm_eq_abs,
  Real.norm_of_nonneg, Real.one_le_rpow, Real.rpow_add, Real.rpow_le_rpow_of_exponent_le, Real.rpow_mul, Real.rpow_natCast, Real.rpow_neg, Real.rpow_nonneg,
  Real.rpow_pos_of_pos, Real.sq_sqrt, Real.sqrt_pos, Real.toNNReal_le_iff_le_coe, Ring.inverse_eq_inv', Set.indicator_of_mem, Set.indicator_of_notMem,
  Set.indicator_univ, Set.mem_iUnion, Set.mem_ofPred_eq, Sigma.mk.inj_iff, Units.smul_def, ZMod.card
Root-namespace names (105):
  abs_add_le, abs_le, abs_lt, abs_mul, abs_neg, abs_nonneg, abs_of_nonneg, abs_of_pos, abs_pos, add_le_add, add_left_cancel, add_lt_add, add_nonneg,
  analyticAt_const, and_true, comap_measurable, compl_compl, congrFun, continuousAt_const, continuousAt_matrix_inv, continuous_apply, continuous_const,
  continuous_finsetSum, continuous_id, deriv_zero_of_not_differentiableAt, dist_comm, dist_triangle, div_eq_mul_inv, div_le_div_iff₀, div_le_div_of_nonneg_right,
  div_le_iff₀, div_nonneg, eventually_nhdsWithin_iff, exists_rat_btwn, funext, gt_mem_nhds, half_pos, hasDerivAt_iff_tendsto_slope, heq_eq_eq, inv_anti₀, ite_false,
  ite_true, le_abs_self, le_add_self, le_div_iff₀, le_rfl, le_self_add, le_trans, lt_irrefl, lt_min, lt_of_lt_of_le, lt_self_iff_false, measurable_const,
  measurable_pi_apply, min_eq_left, min_le_left, min_le_right, mul_assoc, mul_comm, mul_inv_cancel₀, mul_inv_lt_iff₀, mul_le_mul, mul_le_mul_of_nonneg',
  mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_nonneg, mul_one, mul_pos, mul_pow, neg_mul, nhdsWithin_le_nhds, norm_add_le, norm_mul, norm_mul_le,
  norm_nonneg, norm_prod, norm_smul_le, norm_sum_le, not_isUnit_zero, nsmul_eq_mul, one_div, one_mul, one_pos, pow_le_pow_iff_left₀, pow_le_pow_left₀,
  pow_le_pow_of_le_one, pow_pos, self_mem_nhdsWithin, smul_eq_mul, sq_abs, sq_nonneg, sub_nonneg, sub_pos, sub_zero, tendsto_nhdsWithin_iff, tendsto_rpow_atTop,
  tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero, true_and, vsub_eq_sub, zero_le, zero_le_one, zero_lt_one, zero_smul, zero_sub, zsmul_eq_mul

## (d) Open issues and paper-delta candidates
1. `AzumaSubGN`, `YMomentsN` (`YMomentsConclN`): pins whose proofs are owed to ST2-34/35 (DECISIONS §16, §20). The scan lists a `Prop` definition only when some theorem takes it as a hypothesis and none proves it; a theorem taking either pin as a hypothesis makes the registry lines (`owedProps`) necessary.
2. `YMomentsN` has `∃ C_P` after `K` (RBM2D `GridGoodN:429`, kept verbatim), while `AssembledN` needs `C_P` before `C_K` and hence before `K`; RBM2D bridges this with the primed pin `YMomentsUnifN` (`AzumaProxyN.lean:2042` at `c9a24cf`, `yMomentsN_of_unif` `:2053`). The dispatcher should put `YMomentsUnifN` in the scope of ST2-34/35 ((a) row 9).
3. `ellT_mono` (`Kernel/PropT.lean:58`) needs `0 ≤ sz.lam n`, which is not a field of `Sizes`: S3-10 needs it as a hypothesis for the class index `j+1` of `hDcls` ((a), end of (i)); the `dDrift` of S3-10 changes as stated there (no additive `W^{-D'}`).
4. The instance of `stoppedAzumaZN` keeps `SubGaussStopN` for `ZvecN` as a hypothesis (another gate's pin `AzumaSubGN`); the same tail is proved without hypothesis for the random `Z` (`gridAsm_witAzuma`).
5. Paper-delta candidates: `T2154a`: `[NeZero k]` dropped from the pins and targets (strictly stronger, as the merged `SubGaussStopN`). `T2154b`: `YMomentsN` fixes `C_P` after `K` (item 2). Per-time laws and Azuma instead of BDG are DECISIONS §7, §10 (no new candidate).
