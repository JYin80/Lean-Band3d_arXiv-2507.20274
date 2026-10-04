Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 07:23:58 UTC 2026

Source: `git show c9a24cf:RBM2D/Induction/StepDecompN.lean` (1550 lines; RBM2D HEAD is 9e0f275) and `Induction/GridGoodN.lean:241-290`. Mathematics: for a label family `Φ_a` in `HermTestFun` with Hermitian bound `‖∂²Φ_a(M)[y,y]‖ ≤ C₂‖y‖²`, one grid step `H_{j+1}=H_j+√Δ X_{j+1}` gives `ξ_b = Σ_a U(b,a)(Φ_a(H_{j+1}) − E[Φ_a(H_{j+1})|F_j]) = Z_b + Y_b`, `Z_b=√Δ tr(A_b X_{j+1})`, `A_b=Σ_a U(b,a)∇Φ_a(H_j)` `F_j`-measurable; `E[Y|F_j]=0`, `‖Y‖ ≤ g+E[g|F_j]`, `g=(Σ_a‖U(b,a)‖)(C₂/2)Δ‖X_{j+1}‖²`, `E‖Y‖² ≤ 4((Σ‖U‖)C₂/2)²Δ² E‖X_{j+1}‖⁴`; loop family `loopFamN`, `C₂=k(k+1)N η_{u_{j+1}}^{-(k+2)}`, `N=(WL)^d`, `η_u=(1-u)Im m(E)`.

### (i) Exponent table: every `d=2` token of the ported file (counts by `grep -c` on the c9a24cf text)
| # | RBM2D token (count) | `d ≥ 3` replacement | why it holds | slack |
|---|---|---|---|---|
| 1 | `d : Sizes` (R1), `PathΩ d`/`pathP d`/`filt d` (49) | `sz : Sizes d`, `PathΩ sz`, `pathP sz`, `filt sz` | renaming (ST1-COMMON 2) | none |
| 2 | `Z2 (d.L n)` (20), `Idx (d.L n) (d.W n)` (42) | `Zd d (sz.L n)`, `Idx d (sz.L n) (sz.W n)` (R2) | index types only; no statement uses the cardinality of `Zd` | none |
| 3 | `Sizes.size d n` in `C₂` (3 occurrences; RBM2D `(W L)^2`) | `Sizes.size sz n = (W n * L n)^d` (Sizes.lean:157) | merged `HermTestFunLoopN` (LoopC2N.lean:453) has exactly `k(k+1) * size * (etaT E u)⁻¹^(k+2)`; `‖tr A‖ ≤ card·‖A‖`, `card Idx = size` (`Sizes.card_Idx`, Sizes.lean:160) | equality; numbers in (ii) |
| 4 | `‖E_b‖ ≤ W^{-2}` (inside the merged `hermTestFunLoopN`, not restated here) | `W^{-d} ≤ 1` | the merged proof drops `W^{-dk}`; constant stays the Leibniz count `2k+k(k-1)=k(k+1)` (dimension-free) | `W^{-d}`: 0.125 at W=2, 3.05e-5 at W=32 |
| 5 | `gloop (L)(W) (blockMat M) (spectralZ (E n) u) (loopOf σ a)` in `loopFamN` (2, 1) | `loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt (E n) u) (loopOf σ a)` | the form of the merged pin `HermTestFunLoopN`; merged `AvecN`/`martIncN` (GridDuhamelN.lean:272-281) read `STLKM = STLM − STKloop`, `STLM = loopFine = loopM d L W (blockMat H) z σ a`, `loopM_eq_loopL` (GLoopFlow.lean:127) | equality |
| 6 | `KLoop.Kcal (L)(W)(E n) u (loopOf σ b)` (3) in `martIncN_eq_stepXiCN` | merged `STKloop sz n (E n) u σ b` (Induction/Defs.lean:64) | it is deterministic (no `M`), so `E[𝓛−𝒦|F_j]=E[𝓛|F_j]−𝒦` by `condExp_sub`, `condExp_const` (integrable constant): d-free | none |
| 7 | `ukerMat (L) (mSig(σ i)*mSig(σ(i+1))) v w` (13), `KLoop.mSig` (10) | `Ugen d (sz.L n) (sz.lam n) (E n) σ v w A := UN …` with kernel `∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i)(b i)`, `g = sz.lam n`, `cycProd m i = m i * m (finRotate k i)` (Evolution.lean:49-65; GridDuhamelN.lean:65). `uKer = ukerMat` by `rfl` (GridDuhamelN private `uKer_eq`) | `Ugen` of RBM3D has the coupling `g` (RBM2D's `Ugen` has none) and `finRotate` instead of `i+1`; identity `Ugen(Z)_a = Σ_b U(a,b) Z_b` is the definition of `UN` | kernel identity is definitional |
| 8 | `[NeZero k]` (5: `stoppedEdgeN`, `SubGaussStopN`, `Ugen_stepZCN`, `Ugen_stepYCN`, `StepDecompN_subGaussStopN_zvecN`) | dropped | merged `Ugen`/`UN` need none (GridDuhamelN.lean:27); the `i+1` that needed it is `finRotate`; precedent D204, T2111b | statements strictly stronger |
| 9 | `hermTestFunLoopN`-test-class step `StepDecompN_loopFam_hermTestFun`, `k=0` branch (`gloop, gloopProd` simp) | `k=0`: `loopL` of the empty list is `tr 1`, constant; `HermTestFun` holds (`⟨contDiffAt_const, _, le_rfl⟩`); merged `hermTestFunLoopN` already has no `[NeZero k]` | d-free | none |
| 10 | `spectralZ`, `etaT`, `GoodEvent_gridTime_nonneg/_le`, `GoodEvent_gridStep_nonneg` (`Path/GoodEvent`, import cut) | `zt`, `etaT`, `etaT_pos hE hu1` (GLoop.lean:75,83); `gridStep ≥ 0` and `0 ≤ u_{j+1} ≤ t n < 1` from `0≤s≤t<1`, `j+1≤K n`: elementary, d-free; the merged versions are `private` (GridDuhamelN.lean:239-256): copy as private | no new inputs | `u_{j+1}≤t n` uses `Δ=(t−s)/K`, `K ≥ j+1 ≥ 1` |
| 11 | `Sizes.seqXmat d n`, `gradMat`, `linTr`, `linTrVar`, `hasCondSubgaussianMGF_linear`, `integrable_normSq_incr`, `integrable_normPow4_incr`, `pathH_measurable_filt`, `pathH_succ` | all merged and `d`-generic: Markov.lean:134,238,636; StepDecomp.lean:80,687,693; Stop.lean:159; LoopStep.lean:48 | `E‖X‖²`, `E‖X‖⁴` are not bounded in the statement (kept as the integral), so no `d`-dependent estimate enters | — |
| 12 | §29 (`0 ≤ s`, `t<1`, `|E|<2`, `∀ n` vs `∀ᶠ n`) | the RBM2D statements are already per-`n` (`|E n|<2`, `0≤s n`, `s n≤t n`, `t n<1`, `j+1≤K n`; no `∀ n`, no `∀ᶠ n`); no `_at` form needed (contrast T2111 F2) | `StepDecompCN_Stmt` has only `0 ≤ gridStep` | none |
| 13 | `k=2` reduction to merged `Path/StepDecomp` | `stepDecomp` (StepDecomp.lean:1185): `ι = Zd d L × Zd d L`, real `U`, `hReal`, `stepZ`/`stepY` real-kernel. `stepDecompCN` at `ι = Zd×Zd`, `U ↦ (U:ℂ)`: with `Φ` real on Hermitian points `tr(A X)=fderiv Φ[X]` is real (`fderiv_eq_trace_gradMat`, StepDecomp.lean:123), so `stepZCN_im=0`, `stepZCN=↑stepZ`, `stepXiCN=stepXi`, `stepYCN=stepY`, `|U b a|=‖(U b a:ℂ)‖`; hypotheses of `stepDecompCN` are implied by those of `stepDecomp` | merged statement is a special case (real kernel, `hReal`, `k=2` labels) | — |

Pinned definitions not in the table need no change beyond rows 1-3: `AbCN, stepZCN_re/_im, stepZCN, stepXiCN, stepYCN, StepDecompCN_Stmt, stepDecompCN, stepDecompCN_Z_subG, integrable_stepZCN_re/im_of_hermTestFun, stepDecompCN_Y_sq` are `ι`-generic; the only `d` entering is `C₂` through the hypothesis `hC₂`. No `1/5`, `ellT`, `tailT`, `scaleM`, `Meta`, `ellz`, `W ^ 2`, `L ^ 2` occurs (grep).

`GridGoodN:241-290` vocabulary used. Ticket's six: `ZfamN`(:249), `ZvecN`(:258), `YvecN`(:266), `stoppedEdgeN`(:271), `SubGaussFormN`(:279), `SubGaussStopN`(:287). `ZvecN` needs merged `loopDerivN d L W E u M X σ b` (QVN.lean:62, `deriv` of `y ↦ loopL …(M+y•X)` at 0): equal to RBM2D's. `StoppedAzumaZN` (:297), `qvFormN`, `AzumaSubGN` are not in the six and are not ported. **Finding F1 (stop condition of the ticket):** `ZfamN` is defined through `dirDerivN` (GridGoodN:241-243: `deriv (fun y : ℝ => Φ (M + (y:ℂ)•X)) 0`), a seventh declaration of `GridGoodN` not in the ticket's list. `ZfamN`/`dirDerivN` occur 0 times in `StepDecompN.lean`, and in no RBM3D file; they occur in `AzumaProxyN` (23), `GridGoodN` (11), `AltProxyQ` (4) at c9a24cf. Resolution needed from the dispatcher: authorize `dirDerivN` (3 lines, dimension-free, `d` enters only through `Idx d L W`) as a seventh vocabulary definition, or drop `ZfamN` from this ticket.

### (ii) One nondegenerate instance: `d=3, L=3, W=2` (`N=(WL)^d=216`), `E=0` (`m=i`, `Im m=1`), `k=3`, `σ=(+,−,+)`, `b=(0,0,0)` (all insertions in block 0, so `∇𝓛 ≠ 0`), identity kernel, `g=W^{-d/2}`, `s≡1/2`, `t≡11/20`, `K≡5`, `j=0`
`Δ=1/100`, `u_j=1/2`, `u_{j+1}=0.51`, `η=0.49`. The Lean instance data is the merged `sz0` (`L 0=4, W 0=32, N=2097152`, `sz0_values`, Sizes.lean:267) at the same `E,s,t,K,j,k,σ`.
Model (read from FineModel.lean:50-99, Block.lean:36-44): `X` Hermitian on `Z_{WL}^d`, `E|X_xy|²=W^{-d}S^{(B)}_{[x][y]}`, `S^{(B)}` = `a` at 0, `g²a` at ℓ¹-distance 1 (6 neighbours), `a=(1+2dg²)^{-1}`; diagonal real, off-diagonal complex with `Re,Im ~ N(0,S/2)`. `𝓛(H)=tr ∏ G_{σ_i}(H) E_{a_i}`, `G_±=(H−z_u)^{-1}`, `(H−z̄_u)^{-1}`, `z_u=E+(1−u)m`, `E_a=W^{-d}1_{[x]=a}`; `H_0=√s X_0`; `𝓛'` exact (`dG=−G dX G`); `ξ=𝓛(H+√Δ X)−mean`, `Z=√Δ tr(A X)`, `Y=ξ−Z`; 10⁴ iid samples of `X_{j+1}`; `‖X‖` = spectral norm (`L2Operator`).

Command (scratchpad `T2121/`, outputs `check.out`, `check2.out`, `check3.out`): `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2121 && python3 check.py 10000 && python3 check3.py`
```
row sums of S (should be 1): 0.9999999999999999 1.0
max |E|X_ij|^2 - S_ij| (200 samples, S_ij ~ 8.93e-03..7.14e-02): 1.87e-02     [check2.out, 5000 samples: 4.37e-03]
N=216 Delta=0.01 u_j=0.5 u_{j+1}=0.51 eta=0.49 g=0.35355
C2 = k(k+1) N eta^-(k+2) = 9.176025e+04
check DL[X]=tr(A X): 6.837354044672718e-18
Delta*linTrVar(A) = 7.814646e-08 ; Delta*linTrVar(-iA) = 2.530457e-07
max |xi - (Z+Y)| = 2.711e-20 (identity by definition of YvecN)
E Z ~ (-2.3099e-06-1.7659e-06j) (SE 5.78e-06);  E Y ~ (2.309888e-06+1.765927e-06j) (SE 9.25e-07)
MC Var Re Z = 7.692460e-08 vs Delta*linTrVar = 7.814646e-08 ; Var Im Z = 2.573097e-07 vs 2.530457e-07
E|Y|^2 (MC, 10000 samples) = 8.561462e-09
E||X||^4 (MC) = 16.073127
bound 4 (C2/2)^2 Delta^2 E||X||^4 = 1.353348e+07
E|Y|^2 <= bound: True  ratio = 6.326e-16
pathwise |R_s| <= (C2/2) Delta ||X_s||^2 for all 10000 samples: True ; max ratio = 3.712e-07
```
Hypotheses of every target at the instance (exact, `check3.py`):
```
Delta = 1/100  u_j = 1/2  u_{j+1} = 51/100
{'|E|<2': True, '0<=s': True, 's<=t': True, 't<1': True, 'K!=0': True, 'j+1<=K': True, '0<=Delta': True, 'u_{j+1}<1': True, '0<=u_{j+1}': True, 'u_{j+1}<=t': True}
d=3,L=3,W=2 : N=(WL)^d = 216  C2=k(k+1)N eta^-(k+2) = 91760.25188670601   ||E_b||<=W^-d = 0.125
sz0 n=0 (d=3,L=4,W=32) : N=(WL)^d = 2097152  C2=k(k+1)N eta^-(k+2) = 890903684.0958763   ||E_b||<=W^-d = 3.0517578125e-05
```
Reading: `Var Re Z` and `Var Im Z` agree with `Δ·linTrVar` (the sub-Gaussian proxy of `stepDecompCN_Z_subG`) to 1.6% and 1.7%; the pathwise Taylor remainder bound and the `L²` bound hold with ratios `3.7e-7` and `6.3e-16` (the bound is crude: `C₂` carries `N η^{-5}`); `E‖X‖⁴ ≈ 16 = 2⁴` (spectral norm ≈ 2). No external hypothesis occurs: the test-class and `C₂` input is the merged theorem `hermTestFunLoopN` (no hypothesis), so no limit computation is owed. The `HasCondSubgaussianMGF` conclusion needs a proxy `c ≥ Δ·linTrVar` on `{j<τ}`; at the instance `c=3e-7` works for both parts (row `Δ·linTrVar` above).

### Verdicts
- `stepDecompCN`, `stepDecompCN_Z_subG`, `stepDecompCN_Y_sq`, `integrable_stepZCN_re/im_of_hermTestFun`, `loopFamN`, `ZvecN`, `YvecN`, `stoppedEdgeN`, `SubGaussFormN`, `SubGaussStopN`, `ZvecN_eq_stepZCN`, `Ugen_stepZCN`, `martIncN_eq_stepXiCN`, `YvecN_eq_stepYCN`, `Ugen_stepYCN`, `StepDecompN_subGaussStopN_zvecN`: PASS (every exponent closes at `d=3`: only `N=(WL)^d` in `C₂` changes; hypotheses hold at the instance; Lean statements differ from RBM2D by rows 1-3, 5, 7, 8: paper-delta candidate T2121a = `[NeZero k]` dropped and `Ugen` carries `g = sz.lam n`).
- `ZfamN`: BLOCKED on F1 (`dirDerivN` is not among the six vocabulary declarations; the ticket says to stop; missing input = dispatcher decision: authorize `dirDerivN` or drop `ZfamN`).

## (a′) Preflight corrections — Sun Oct  4 08:04:56 UTC 2026
- Section (a) says the Lean instance uses "the same `E,s,t,K,j,k,σ`" as the Monte-Carlo instance (`s≡1/2, t≡11/20, K≡5`). The Lean instance uses `s≡0, t≡1/2, K≡4` at `sz0` (`Δ=1/8`, `u_1=1/8`, `u_2=1/4`): with `s≡0` the walk `H_0=0` is deterministic, so the `Δ·linTrVar` hypotheses of `stepDecompCN_Z_subG` hold uniformly in `ω` (constant `c3`). No verdict changes; every target hypothesis is checked in Lean by `norm_num` at these data (`hE0 … hj1`, `StepDecompNCheck`).
- F1 of (a) (`ZfamN` blocked on `dirDerivN`) is resolved by Amend 1 of the ticket: `dirDerivN` is ported as a seventh vocabulary declaration.

## (b) Script output
Commit `e15ef7f` on `t/T2121` (author `Jun Yin <321276894+JYin80@users.noreply.github.com>`); only file: `RBM3D/Induction/StepDecompN.lean` (1588 lines). `RBM3D/Test/Axioms.lean` unchanged (see registry pre-check).

### b.1 Build
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2121 && date -u && lake build RBM3D.Induction.StepDecompN   # final run, before the pre-check below (build.out)
$ grep -c "StepDecompN.lean.*\(warning\|error\)" build.out  ->  0
$ tail -1 build.out  ->  Build completed successfully (3763 jobs).
$ lake build   # full library, Sun Oct  4 08:03:43 UTC 2026, exit 0  ->  Build completed successfully (3867 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/StepDecompN.lean  ->  (no output)
```
### b.2 Registry pre-check (DECISIONS §20), scratch file outside the repository
```
$ cat precheck.lean:  import RBM3D / import RBM3D.Induction.StepDecompN / #assert_rbm_axioms
$ lake env lean precheck.lean   # Sun Oct  4 08:03:21 UTC 2026
axiom audit: 3681 theorems, 1301 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice,
exit code: 0 (scan line of the output above: 80 premises found: borrowed 2, owed 63, structural 15; none is declared in this file)
```
### b.3 `#print axioms` of every target and vocabulary declaration (from `build.out`)
```
loopFamN: [propext, Classical.choice, Quot.sound]
dirDerivN: [propext, Classical.choice, Quot.sound]
ZfamN: [propext, Classical.choice, Quot.sound]
ZvecN: [propext, Classical.choice, Quot.sound]
YvecN: [propext, Classical.choice, Quot.sound]
stoppedEdgeN: [propext, Classical.choice, Quot.sound]
SubGaussFormN: [propext, Classical.choice, Quot.sound]
SubGaussStopN: [propext, Classical.choice, Quot.sound]
stepDecompCN: [propext, Classical.choice, Quot.sound]
stepDecompCN_Z_subG: [propext, Classical.choice, Quot.sound]
integrable_stepZCN_re_of_hermTestFun: [propext, Classical.choice, Quot.sound]
integrable_stepZCN_im_of_hermTestFun: [propext, Classical.choice, Quot.sound]
stepDecompCN_Y_sq: [propext, Classical.choice, Quot.sound]
ZvecN_eq_stepZCN: [propext, Classical.choice, Quot.sound]
Ugen_stepZCN: [propext, Classical.choice, Quot.sound]
martIncN_eq_stepXiCN: [propext, Classical.choice, Quot.sound]
YvecN_eq_stepYCN: [propext, Classical.choice, Quot.sound]
Ugen_stepYCN: [propext, Classical.choice, Quot.sound]
StepDecompN_subGaussStopN_zvecN: [propext, Classical.choice, Quot.sound]
```
### b.4 Statements, extracted from the file by script (`extract.py`; docstrings and proofs omitted)
```lean
def loopFamN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    (Fin k → Zd d (sz.L n)) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
def dirDerivN {d L W : ℕ} [NeZero L] [NeZero W]
    (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) : ℂ :=
def ZfamN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (ω : PathΩ sz) : ι → ℂ :=
def ZvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
def YvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
def stoppedEdgeN {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ)
    (τ : PathΩ sz → ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (b : Fin k → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) : ℂ :=
def SubGaussFormN (j : ℕ) (τ : PathΩ sz → ℕ) (F : PathΩ sz → ℂ) (c : ℝ≥0) : Prop :=
def SubGaussStopN {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
    (Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ) (a : Fin k → Zd d (sz.L n))
    (j : ℕ) (c : ℝ≥0) : Prop :=
theorem stepDecompCN {d : ℕ} (sz : Sizes d) : StepDecompCN_Stmt sz := by
theorem stepDecompCN_Z_subG {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) (U : ι → ι → ℂ) (b : ι)
    (E : Set (PathΩ sz)) (hE : MeasurableSet[filt sz j] E) (c : ℝ) (hc : 0 ≤ c)
    (hboundRe : ∀ ω ∈ E, gridStep s t K n * linTrVar n (AbCN sz s t K n j Φ U b ω) ≤ c)
    (hboundIm : ∀ ω ∈ E,
      gridStep s t K n * linTrVar n ((-Complex.I) • AbCN sz s t K n j Φ U b ω) ≤ c) :
    HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => E.indicator (fun ω => stepZCN_re sz s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP sz)
    ∧ HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
      (fun ω => E.indicator (fun ω => stepZCN_im sz s t K n j Φ U b ω) ω) ⟨c, hc⟩ (pathP sz) := by
theorem stepDecompCN_Y_sq {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {ι : Type*}
    [Fintype ι]
    {Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a)) {C₂ : ℝ}
    (hC₂ : ∀ a (M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ (Φ a)) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (hΔ : 0 ≤ gridStep s t K n) (U : ι → ι → ℂ) (b : ι) :
    ∫ ω, ‖stepYCN sz s t K n j Φ U b ω‖ ^ 2 ∂(pathP sz)
      ≤ 4 * ((∑ a, ‖U b a‖) * (C₂ / 2)) ^ 2 * (gridStep s t K n) ^ 2
          * ∫ ω, ‖Sizes.seqXmat sz n (ω (j + 1))‖ ^ 4 ∂(pathP sz) := by
theorem ZvecN_eq_stepZCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
    ZvecN sz E s t K n j σ ω b =
      stepZCN sz s t K n j (loopFamN sz E s t K n j σ) (fun a a' => if a = a' then 1 else 0) b ω := by
theorem Ugen_stepZCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (m : ℕ) (a : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
        (ZvecN sz E s t K n j σ ω) a =
      stepZCN sz s t K n j (loopFamN sz E s t K n j σ)
        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω := by
theorem martIncN_eq_stepXiCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Fin k → Zd d (sz.L n),
      martIncN sz E s t K n j σ ω b =
        stepXiCN sz s t K n j (loopFamN sz E s t K n j σ) (fun a a' => if a = a' then 1 else 0)
          b ω := by
theorem YvecN_eq_stepYCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Fin k → Zd d (sz.L n),
      YvecN sz E s t K n j σ ω b =
        stepYCN sz s t K n j (loopFamN sz E s t K n j σ) (fun a a' => if a = a' then 1 else 0)
          b ω := by
theorem Ugen_stepYCN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (m : ℕ) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin k → Zd d (sz.L n),
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (YvecN sz E s t K n j σ ω) a =
        stepYCN sz s t K n j (loopFamN sz E s t K n j σ)
          (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω := by
theorem StepDecompN_subGaussStopN_zvecN {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hj : j + 1 ≤ K n)
    {k : ℕ} (σ : Fin k → Bool) (τ : PathΩ sz → ℕ)
    (hτ : MeasurableSet[filt sz j] {ω | j < τ ω}) (m : ℕ) (a : Fin k → Zd d (sz.L n))
    (c : ℝ) (hc : 0 ≤ c)
    (hboundRe : ∀ ω, j < τ ω → gridStep s t K n * linTrVar n
      (AbCN sz s t K n j (loopFamN sz E s t K n j σ)
        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω) ≤ c)
    (hboundIm : ∀ ω, j < τ ω → gridStep s t K n * linTrVar n
      ((-Complex.I) • AbCN sz s t K n j (loopFamN sz E s t K n j σ)
        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω) ≤ c) :
    SubGaussStopN sz (E n) σ (gridTime s t K n) τ (fun j ω => ZvecN sz E s t K n j σ ω) m a j
      ⟨c, hc⟩ := by
```
`loopFamN` body: `fun a M => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) (zt (E n) (gridTime s t K n (j + 1))) (loopOf σ a)`.
### b.5 Script diff against RBM2D `StepDecompN` at `c9a24cf` (`d→sz`, `(sz : Sizes)→{d : ℕ} (sz : Sizes d)`, `Idx (→Idx d (`, `Z2 (→Zd d (`)
```
identical after renaming (signature text): AbCN, stepZCN_re, stepZCN_im, stepZCN, stepXiCN, stepYCN, StepDecompCN_Stmt, loopFamN, stepDecompCN, stepDecompCN_Z_subG, integrable_stepZCN_re_of_hermTestFun, integrable_stepZCN_im_of_hermTestFun, stepDecompCN_Y_sq, ZvecN_eq_stepZCN, martIncN_eq_stepXiCN, YvecN_eq_stepYCN
== Ugen_stepZCN: differs
@@ -3,2 +3,2 @@
-    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (m : ℕ) (a : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
-    Ugen (sz.L n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
+    {k : ℕ} (σ : Fin k → Bool) (m : ℕ) (a : Fin k → Zd d (sz.L n)) (ω : PathΩ sz) :
+    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
@@ -7,3 +7,2 @@
-        (fun a b => ∏ i : Fin k, ukerMat (sz.L n)
-          (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
-          (gridTime s t K n m) (a i) (b i)) a ω := by
+        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
+          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω := by
== Ugen_stepYCN: differs (same three changes as Ugen_stepZCN: `[NeZero k]`, `Ugen d … (sz.lam n)`, `uKer … cycProd` kernel; lines omitted here)
== StepDecompN_subGaussStopN_zvecN: differs
@@ -3 +3 @@
-    {k : ℕ} [NeZero k] (σ : Fin k → Bool) (τ : PathΩ sz → ℕ)
+    {k : ℕ} (σ : Fin k → Bool) (τ : PathΩ sz → ℕ)
@@ -8,3 +8,2 @@
-        (fun a b => ∏ i : Fin k, ukerMat (sz.L n)
-          (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
-          (gridTime s t K n m) (a i) (b i)) a ω) ≤ c)
+        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
+          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω) ≤ c)
@@ -13,3 +12,2 @@
-        (fun a b => ∏ i : Fin k, ukerMat (sz.L n)
-          (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) (gridTime s t K n (j + 1))
-          (gridTime s t K n m) (a i) (b i)) a ω) ≤ c) :
+        (fun a b => ∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i)
+          (gridTime s t K n (j + 1)) (gridTime s t K n m) (a i) (b i)) a ω) ≤ c) :
```
Residual differences: `Ugen` carries `d`, `(sz.lam n)`; the kernel is `uKer … (cycProd (fun i => mSigma (E n) (σ i)) i)` (merged `UN`) instead of `ukerMat … (mSig σ_i * mSig σ_{i+1})`; `[NeZero k]` dropped; `loopFamN` body (`gloop/spectralZ → loopL/zt`).
### b.6 Compiled nonempty instances (`section Instances`, `StepDecompNCheck`; `sz0`, `d=3`, `E≡0, s≡0, t≡1/2, K≡4`, `n=0`, `k=3`, `σ=(+,-,+)`, `b=(0,0,0)`; all in the build above, no `sorry`)
```
$ grep -n "^example" RBM3D/Induction/StepDecompN.lean | cut -c1-110
1444:example :=
1450:example :=
1458:example :=
1461:example :=
1464:example :=
1467:example :=
1471:example := stepDecompCN_Y_sq sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3
1473:example := stepDecompCN_Y_sq sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3
1507:example :=
1513:example : SubGaussStopN sz0 (E0 0) σ3 (gridTime s0 t0 K0 0) (fun _ => K0 0)
1524:example (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :=
1527:example := martIncN_eq_stepXiCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3
1529:example := YvecN_eq_stepYCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3
1532:example (a : Fin 3 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
1535:example := Ugen_stepYCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 1
1541:example :=
1548:example := stepDecompCN_Y_sq sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ (U3 1 2) b3
1550:example (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :=
1553:example := martIncN_eq_stepXiCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3
1555:example := YvecN_eq_stepYCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3
1557:example (a : Fin 3 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
1560:example := Ugen_stepYCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 2
```
The instances at `j=0` (`H_0=0`) cover every target: `stepDecompCN` (identity kernel `δ3` and propagator kernel `U3 0 1`), `integrable_stepZCN_re/im_of_hermTestFun`, `stepDecompCN_Y_sq`, `stepDecompCN_Z_subG` (`E = univ`, `c3`), `StepDecompN_subGaussStopN_zvecN` (stated as a `SubGaussStopN` example, `τ ≡ K 0`), `ZvecN_eq_stepZCN`, `martIncN_eq_stepXiCN`, `YvecN_eq_stepYCN`, `Ugen_stepZCN`, `Ugen_stepYCN`; `j=1` (random `H_1`) repeats `stepDecompCN`, `stepDecompCN_Y_sq` and the identification theorems, not the sub-Gaussian ones. Every deterministic hypothesis is discharged (`hΦ3` and `hC₂3` from the merged `hermTestFunLoopN`, `C₂3_pos : 0 < C₂ = 12·2097152·η^{-5}`). Nothing is left as a hypothesis (no other gate pin is used).
### b.7 Name-clash grep and ports
```
$ for n in <new public names>; do grep -rnE "(def|theorem|lemma|abbrev|structure) $n( |$)" RBM3D --include=*.lean | grep -v Induction/StepDecompN.lean; done
  (no output: no clash; the only hit was `theorem data` of `GridDriftNCheck`, a different namespace; here `data` is `private`)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf  ->  c9a24cf
Port: RBM2D `RBM2D/Induction/StepDecompN.lean:1-1291` and `Induction/GridGoodN.lean:241-290` at c9a24cf (read with `git show`); RBM2D `Instances` (`:1292-1528`) rewritten for `sz0`.
RBM1D/RBM2D diff-stat: not applicable (the port source is the fixed commit c9a24cf; no later change is used).
```
### b.8 Narrative
- Port: the RBM2D file `Induction/StepDecompN` is ported by renaming (R1 `d : Sizes`→`sz : Sizes d`, R2 `Z2`/`Idx`→`Zd d`/`Idx d`) and the substitutions of b.5; every public declaration of RBM2D is kept (nothing dropped); every helper stays `private` (75 `private` declarations, prefix `StepDecompN_` or file-local `StepDecompNCheck` names).
- `d ≥ 3` exponents: the statements `stepDecompCN`, `_Z_subG`, `_Y_sq` are `ι`-generic; the dimension enters only through `C₂` of the loop family, which comes from the merged `hermTestFunLoopN` (`k(k+1)·N·η^{-(k+2)}`, `N = sz.size n = (W L)^d`); no `W^{-2}` or `L²` occurs (preflight table (a) rows 1-13 stand).
- Vocabulary: the seven declarations `dirDerivN, ZfamN, ZvecN, YvecN, stoppedEdgeN, SubGaussFormN, SubGaussStopN` are defined here (section 1b), `d`-dimensional, without `[NeZero k]`; nothing else of `GridGoodN` is ported or needed.
- Imports: `LoopC2N`, `GridDuhamelN` (`martIncN`, `AvecN`, `Ugen`), `QVN` (`loopDerivN` is defined there, not in `GridDriftN`), `Path.LoopStep`, `Path.StepDecomp`. `GridDriftN`, `HierAlgebra` are not imported: no name of them is used. `QVN` is an ST-2 file already merged; it does not import `GridGoodN`.
- `martIncN_eq_stepXiCN`: `AvecN = STLKM = STLM - STKloop` and `STLM = loopFine = loopM` are unfolded, `loopM_eq_loopL` turns it into `loopFamN b (H_{j+1}) - sz.STKloop …`; the constant `STKloop` cancels by `condExp_sub`, `condExp_const`.
- `k = 0` needs no case split (the merged `hermTestFunLoopN` covers all `k`; RBM2D had a `k = 0` branch for `gloop`).
- Grid-time facts (`0 ≤ u_j`, `u_{j+1} < 1`) are re-proved privately (`StepDecompN_gridTime_nonneg/_lt_one`); the merged `GridDuhamelN_*` versions are private.
- `k = 2` reduction to the merged `Path/StepDecomp` (`stepDecomp`, real `U`, `hReal`, labels `Zd × Zd`): as in (a) row 13 (the real kernel and real `Φ` give `stepZCN = ↑stepZ`, `stepXiCN = stepXi`); this is an argument, not a compiled lemma, and the ticket does not require one.
- §29: all statements are per `n` with `|E n|<2`, `0≤s n≤t n`, `t n<1`, `j+1≤K n`; no `∀ᶠ n`, no `_at` form needed.
- Instances use `s ≡ 0` so that `H_0 = 0`; see (a′). The `E‖X‖⁴` factor of `stepDecompCN_Y_sq` stays an integral (no `d`-dependent moment bound enters).

## (c) Verified Mathlib names (grep in `.lake/packages/mathlib/Mathlib/` or compiled)
- condExp_sub (ConditionalExpectation/Basic.lean:336)
- condExp_const (…/Basic.lean:148)
- condExp_finsetSum (…/Basic.lean:304)
- condExp_smul (…/Basic.lean:318)
- norm_image_sub_le_of_norm_deriv_right_le_segment (Analysis/Calculus/MeanValue.lean:308)
- image_norm_le_of_norm_deriv_right_le_deriv_boundary (MeanValue.lean:299)
- memLp_top_of_bound (MeasureTheory/Function/LpSeminorm/Basic.lean:611)
- Finset.measurable_sum (used at StepDecompN.lean:471, compiled)
- Verified absent: none needed.

## (d) Open issues and paper-delta candidates
- T2121a: RBM2D `[NeZero k]` is dropped from `stoppedEdgeN`, `SubGaussStopN`, `Ugen_stepZCN`, `Ugen_stepYCN`, `StepDecompN_subGaussStopN_zvecN` (statements strictly stronger; same as D204, T2111b), and `Ugen` is the merged `Ugen d L g` with `g = sz.lam n` (cyclic `finRotate`, kernel `uKer … cycProd`) instead of RBM2D `Ugen`/`ukerMat`/`mSig σ_{i+1}`; formal renaming, no change in meaning for `d ≥ 3`.
- Not a delta: `dirDerivN` added as the seventh vocabulary declaration (Amend 1); ST2-32 must import it from this file.
- Open: none. `RBM3D.lean` root import is for the hub at merge; the pre-check b.2 confirms the assertion passes with the new module imported.
