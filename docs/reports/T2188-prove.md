Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 14:52:13 UTC 2026

Sources read: ticket T2188; RBM2D `Universality/GreenCorr.lean:440-740` (`gcc_step`, `gcc_quantitative`, `gcc_tendsto`, `greenCorrAll`); RBM3D `Universality/Pins.lean:495-560` (`UNClaim417`, `UNApriori`, `UNGreenCorr`, `UNGreenCorrAll`); `PoissonSmoothing.lean` (`poissonSmooth`, `poissonSmooth_error` signature); `InjSum.lean:556` (`injSum_decomp`); `Defs/Sizes.lean` (`sz0`).

### (i) Exponent table

Notation: `N = Nsz sz n`, `ε = N^{-τ_U}`, `Cmax = max 0 (max_{nf≤k} Cn nf)`, `R` = support radius of `O` (sup-norm, from `injSum_decomp` hypothesis `hR`), `ε₀ = (max 1 b)⁻¹ ≤ 1`.

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| `τ₀` | `c'/(2(Cmax+1))` | `> 0` (`c'>0`, `Cmax ≥ 0`); depends only on `c', k, Cn` (not `E, O, r, a, b, M`) | `τ₀ > 0` since `Cmax+1 ≥ 1` |
| `Cmax·τ_U` | `≤ Cmax·c'/(2(Cmax+1)) < c'/2` for `τ_U ≤ τ₀` | need `-c'+Cmax τ_U ≤ -c'/2` | strict: `c'/2 - Cmax τ_U ≥ c'/(2(Cmax+1)) > 0` |
| error term 1 | `N^{-c'+Cmax τ_U} ≤ N^{-c'/2}` (`N ≥ 1`) | exponent `< 0` so `→ 0` as `N → ∞` | exponent `≤ -c'/2 < 0` |
| error term 2 | `N^{-τ_U/2}` | `τ_U > 0` | exponent `-τ_U/2 < 0` |
| a priori bound used | `UNApriori` at `p = nf ≤ k`, `ε_ap = τ_U/2`: `E(Im m_0(E+i/N))^nf ≤ N^{τ_U/2}` | need `ε·N^{τ_U/2} = N^{-τ_U/2}` (the `hεB` identity, `ε = N^{-τ_U}`) | exact identity |
| smoothing scale `ε` | `N^{-τ_U}` | `0 < ε ≤ ε₀ ≤ 1`; equivalent to `N ≥ (max 1 b)^{1/τ_U}`, eventual since `N → ∞` | threshold depends on `τ_U, b` only; allowed (eventuality) |
| window radius `C₀` | `R/a + 1` (`gcc_step` is applied with support radius `R' = R/a`, window `(R'+1)/N`) | `UNClaim417` quantifies `∀ C₀ > 0`; `R/a+1 > 0` | any `C₀>0` allowed; need `|y_j|/N ≤ (R/a+1)/N` for `|y_j| ≤ R/a`: slack `1/N` |
| dilated support radius | `O_n(x)=O(r_n x) ≠ 0 ⇒ |r_n x_j| ≤ R ⇒ |x_j| ≤ R/r_n ≤ R/a` | `r_n ≥ a > 0` | — |
| decomposition of `O_n` | `Σ_f O(r•(lam∘f)) = Σ_i c_i Σ_g Oj_i(r•(lam∘g))` (`injSum_decomp` at `r•lam`); `c, kk, ι` unchanged; `Oj'_i(x) = Oj_i(r x)` | `Oj'_i` is a test function (`r ≠ 0`, `isTestFun_comp_smul`) | — |
| (B-i) `L¹` mass | `∫|Oj'_i| = r^{-kk_i} ∫|Oj_i| ≤ (max 1 a⁻¹)^k ∫|Oj_i|` | `r ≥ a`, `kk_i ≤ k`, base `max 1 a⁻¹ ≥ 1` | — |
| (B-ii) smoothing identity | `poissonSmooth ε (f(r·)) x = poissonSmooth (rε) f (r x)` (`r>0`): substituting `u=ry`, `P_ε(x-u/r)/r = P_{rε}(rx-u)` per coordinate (`P_ε(t)=ε/(π(t²+ε²))`) | `r>0` | exact |
| (B-ii) smoothing error of `Oj'_i` | `|Oj'_i(x) - ps_ε Oj'_i(x)| = |Oj_i(rx) - ps_{rε}Oj_i(rx)| ≤ Cs_i · rε · ∏_j(1+r²x_j²)⁻¹ ≤ Cs_i · max 1 b · (max 1 a⁻²)^{kk_i} · ε · ∏_j(1+x_j²)⁻¹` | needs `rε ≤ 1`: `rε ≤ b·ε₀ ≤ 1`; uses `(1+r²t²)⁻¹ ≤ max(1,r⁻²)(1+t²)⁻¹` (if `r≥1`: `1+r²t² ≥ 1+t²`; if `r<1`: `1+r²t² ≥ r²(1+t²)`) and `r ≤ b ≤ max 1 b`, `r⁻² ≤ a⁻²` | `rε ≤ 1` slack factor `≥ 1` (equality possible only if `b ≥ 1`, `ε = ε₀`) |
| `Cs'_i` | `Cs_i · max 1 b · (max 1 a⁻²)^k` (valid for `0<ε≤ε₀`; replaces `hCs` for all `ε ≤ 1` by `hCs` for `ε ≤ ε₀`) | `Cs'_i ≥ 0`; `gcc_step` uses it only at `ε = N^{-τ_U} ≤ ε₀` (`:549`) and `ε ≤ 1` (in `hεA`) | `ε₀ ≤ 1` retained |
| uniform constant | `K̄ = 2^k Σ_i |c_i| ((max 1 a⁻¹)^k ∫|Oj_i| + 2 Cs_i · max 1 b · (max 1 a⁻²)^k)` | independent of `n` and of `r_n ∈ [a,b]`; dominates `K_n = 2^k Σ|c_i|(∫|Oj'_i| + 2 Cs'_i)` term by term | `K_n ≤ K̄` (not equality unless `a ≥ 1`... only when bases are 1) |
| prefactor | `N^k / N.descFactorial k ≤ 2^k` | `N ≥ 2k` (eventual) | — |
| conclusion | `|diff_n| ≤ K̄ (N^{-c'+Cmax τ_U} + N^{-τ_U/2}) → 0` | all eventualities hold together (finite intersection: `2k ≤ N`, `N^{-τ_U} ≤ ε₀`, `a ≤ r_n ≤ b`, `UNClaim417` for `nf ≤ k` at `C₀=R/a+1`, `UNApriori` for `nf ≤ k`) | — |

Conclusion of (i): every `n`-dependent quantity in `gcc_step` is bounded uniformly for `r_n ∈ [a,b]`; the only new ingredients over RBM2D are the scaling facts (B-i), (B-ii) and the extra eventuality `N^{-τ_U} ≤ ε₀`. No new estimate beyond a rescaling is needed; `τ₀` is unchanged from RBM2D. Edge `kk_i = 0`: `ps` over `Fin 0` is the identity, error `0`, mass scaling factor `1`; consistent with the formulas.

### (ii) Concrete nondegenerate instance

Data: `d = 3`, `sz0` (`sz0_values`: `N(0) = 2097152 = 2^21`; `N(n) = ((2(n+1))^5·4(n+1))^3`), `E = 0`, `k = 1`, `c' = 1`, `Cn ≡ 1`, `τ_U = 1/10`, `O = bump`. For `k = 1`, `injSum_decomp` is trivial (one piece, `c=1`, `kk=1`, `Oj=O`). Model/dilation uses: band with `r ≡ rhoSC 0 = 1/π` (`a = b = 1/π`), BA with `r_n = 1 + 1/(n+1)` (`a = 1, b = 2`). The quadrature identity is checked for `f(x)=exp(-1/(1-x²))` on `(-1,1)` (a smooth compact-support test function); an independent midpoint rule (2·10⁶ nodes) is added. `UNClaim417`/`UNApriori` are hypotheses (other gates), not discharged here; they are the only non-deterministic inputs. Hypothesis `UNClaim417` is stated for `∀ C₀ > 0`, so `C₀ = R/a+1` is admissible (`R=2`: band `C₀ = 2π+1`, BA `C₀ = 3`).

Command: `python3 $SCRATCH/T2188/pre.py` (scratch script; scipy 1.13.1)

```
(ii) identity: ps_eps(f(r.))(x) vs ps_{r eps}(f)(r x), k=1, eps=1/10
r=0.5 x=0 LHS=3.438784946646916e-01 RHS=3.438784946646916e-01 diff=0.00e+00
r=0.5 x=0.7 LHS=2.977623904672038e-01 RHS=2.977623904672038e-01 diff=0.00e+00
r=0.5 x=3 LHS=4.021609565890543e-03 RHS=4.021609565890543e-03 diff=0.00e+00
r=1 x=0 LHS=3.216668524989023e-01 RHS=3.216668524989023e-01 diff=0.00e+00
r=1 x=0.7 LHS=1.366365434062367e-01 RHS=1.366365434062367e-01 diff=0.00e+00
r=1 x=3 LHS=1.656485937640481e-03 RHS=1.656485937640481e-03 diff=0.00e+00
r=2 x=0 LHS=2.823150485005079e-01 RHS=2.823150485005079e-01 diff=0.00e+00
r=2 x=0.7 LHS=1.859548366518611e-02 RHS=1.859548366518611e-02 diff=0.00e+00
r=2 x=3 LHS=7.947510638419710e-04 RHS=7.947510638419710e-04 diff=0.00e+00
max diff 0
(1+r^2x^2)^-1 <= max(1,r^-2)(1+x^2)^-1: grid pts 800400 violations 0 max ratio 1.0
grid estimate Cs(f) over eps in {.01..1}, |x|<=4: 1.1511
band r=rhoSC(0)=1/pi: a=0.3183 b=0.3183 max(1,1/a)=3.1416 max(1,a^-2)=9.8696 max(1,b)=1 eps0=1/max(1,b)=1.0 Kbar(with Cs_est,int|f|=0.4440)=48.2328
BA r_n=1+1/(n+1): a=1.0000 b=2.0000 max(1,1/a)=1.0000 max(1,a^-2)=1.0000 max(1,b)=2.0 eps0=1/max(1,b)=0.5 Kbar(with Cs_est,int|f|=0.4440)=10.0967
N(0)= 2097152 =2^21: True
N(0)^-tU = 0.23325824788420182  <= 1/b=0.5: True ; monotone nonincreasing n=0..2000: True max over n: 0.23325824788420182
c'=1,k=1,Cn=1: Cmax= 1.0 tau0= 0.25 tauU= 0.1 <=tau0: True
Cmax*tauU= 0.1 <= c'/2= 0.5 ; exponent -c'+Cmax tauU= -0.9 <= -c'/2= -0.5 ; N^-tauU/2 exponent -0.05
N(0)^(-c'+Cmax tauU)= 2.0442456484533175e-06  N(0)^(-tauU/2)= 0.48296816446242274
2k<=N: True
```

Independent midpoint check (`python3 $SCRATCH/T2188/chk.py`), columns `r, x, quad(LHS), quad(RHS), |L-R|, midpoint(LHS)`:

```
0.5 0 0.3438784946646916 0.3438784946646916 |L-R|=0.0e+00 midpoint=0.343878494636
0.5 0.7 0.2977623904672038 0.2977623904672038 |L-R|=0.0e+00 midpoint=0.297762390443
0.5 3 0.0040216095658905425 0.0040216095658905425 |L-R|=0.0e+00 midpoint=0.004021609566
1 0 0.32166685249890226 0.32166685249890226 |L-R|=0.0e+00 midpoint=0.321666852472
1 0.7 0.13663654340623677 0.13663654340623677 |L-R|=0.0e+00 midpoint=0.136636543395
1 3 0.0016564859376404805 0.0016564859376404805 |L-R|=0.0e+00 midpoint=0.001656485938
2 0 0.2823150485005079 0.2823150485005079 |L-R|=0.0e+00 midpoint=0.282315048477
2 0.7 0.018595483665186114 0.018595483665186114 |L-R|=0.0e+00 midpoint=0.018595483664
2 3 0.000794751063841971 0.000794751063841971 |L-R|=0.0e+00 midpoint=0.000794751064
```

Reading of the output: identity (B-ii) holds to quadrature precision at all 9 points (`r ∈ {1/2,1,2}`, `x ∈ {0,0.7,3}`, `ε=1/10`; `rε ≤ 0.2 ≤ 1`); the inequality `(1+r²x²)⁻¹ ≤ max(1,r⁻²)(1+x²)⁻¹` has 0 violations on an 800400-point grid (max ratio 1.0, attained at `r = 1` or `x=0`). At `sz0`, `τ_U = 1/10`: `N^{-τ_U} ≤ 0.2333 ≤ 1/2 = (max 1 b)⁻¹` for `b = 2` from `n = 0` on (monotone since `N(n)` is increasing in `n`, formula above; threshold `N ≥ 2^{10}`, `N(0) = 2^{21}`). `τ_U = 1/10 ≤ τ₀ = 1/4`; `Cmax τ_U = 0.1 ≤ 1/2`; `2k ≤ N`. The printed `K̄` values use the numerical grid estimate `Cs(f) ≈ 1.15` (a lower estimate; informational only, `K̄` is finite for any `Cs`).

### Verdicts

- Target 1 `unGreenCorr` (`UNGreenCorr sz M`): **PASS**. Hypothesis set consistent (all hypotheses are satisfiable at the instance above; `UNClaim417`, `UNApriori` remain external pins); exponents close with slack `c'/2 - Cmax τ_U > 0`; dilation handled by rescaling only (no new estimate).
- Target 2 `greenCorrAll` (`UNGreenCorrAll`): **PASS** (one line from target 1; `3 ≤ d` unused).

## (b) Script output (stage 1b; the commit is the one printed under `git log` below)

```
Mon Oct  5 15:05:20 UTC 2026
$ lake build RBM3D.Universality.GreenCorr (GreenCorr lines only)
ℹ [3337/3337] Replayed RBM3D.Universality.GreenCorr
info: RBM3D/Universality/GreenCorr.lean:994:0: 'RBM.Univ.unGreenCorr' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:995:0: 'RBM.Univ.greenCorr_step' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:996:0: 'RBM.Univ.greenCorrAll' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:997:0: 'RBM.Univ.GreenCorrCheck.instance_band' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:998:0: 'RBM.Univ.GreenCorrCheck.instance_ba' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:999:0: 'RBM.Univ.GreenCorrCheck.instance_greenCorrAll' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:1000:0: 'RBM.Univ.GreenCorrCheck.instance_greenCorrAll_tauU' : [propext, Classical.choice, Quot.sound]
Build completed successfully (3337 jobs).
$ lake build   (whole library, runs #assert_rbm_axioms in RBM3D.lean; GreenCorr is not yet a root import)
info: RBM3D.lean:234:0: axiom audit: 5455 theorems, 1951 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3992 jobs).
exit=0
$ printf 'import RBM3D\nimport RBM3D.Universality.GreenCorr\n#assert_rbm_axioms\n' > precheck.lean && lake env lean precheck.lean
exit=0
axiom audit: 5463 theorems, 1951 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 129 premises in the two ledgers; the rest are not known to be satisfi
ledger lines mentioning UNGreenCorr or UNGreenCorrAll (exact names): 0
```

Targets, extracted from `RBM3D/Universality/GreenCorr.lean` by script, and the type check against the pins:
```
theorem unGreenCorr {d : ℕ} (sz : Sizes d) (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (M : UNModel sz) : UNGreenCorr sz M
theorem greenCorrAll : UNGreenCorrAll
$ lake env lean typecheck.lean   (#check (@unGreenCorr : ∀ {d} (sz : Sizes d), Tendsto .. → ∀ M : UNModel sz, UNGreenCorr sz M); example : UNGreenCorrAll := greenCorrAll)
@unGreenCorr : ∀ {d : ℕ} (sz : Sizes d), Tendsto (fun n => sz.size n) atTop atTop → ∀ (M : UNModel sz), UNGreenCorr sz M
greenCorrAll : UNGreenCorrAll
```

Compiled nonempty instances (statements extracted by script; `d = 3`, `sz0`, `N(0) = 2^21`, `E = 0`, `k = 1`, `c' = 1`, `Cn ≡ 1`, bump; `UNClaim417`, `UNApriori` stay hypotheses; the axioms of all four are in the build output above):
```
theorem instance_band :
    (bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ (bump : (Fin 1 → ℝ) → ℝ) (fun _ => 3) = 0 ∧
    sz0.size 0 = 2097152 ∧ 0 < rhoSC 0 ∧
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      (∀ nf ≤ 1, UNClaim417 sz0 (UNModel.band sz0) 0 nf τU 1 1) →
      UNApriori sz0 (UNModel.band sz0) 0 →
      Tendsto (fun n =>
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) (rhoSC 0 • α)) 0
            (ouMat_isHermitian (UNModel.band sz0) n 0 ω).eigenvalues
            ∂(ouP (UNModel.band sz0) n)) -
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) (rhoSC 0 • α)) 0
            (ouMat_isHermitian (UNModel.band sz0) n (ouTStar sz0 τU n) ω).eigenvalues
            ∂(ouP (UNModel.band sz0) n)))
        atTop (𝓝 0)
theorem instance_ba :
    (1 + 1 / (((0 : ℕ) : ℝ) + 1) : ℝ) ≠ 1 + 1 / (((1 : ℕ) : ℝ) + 1) ∧
    (bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ sz0.size 0 = 2097152 ∧
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      (∀ nf ≤ 1, UNClaim417 sz0 (UNModel.ba sz0) 0 nf τU 1 1) →
      UNApriori sz0 (UNModel.ba sz0) 0 →
      Tendsto (fun n : ℕ =>
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((1 + 1 / ((n : ℝ) + 1)) • α)) 0
            (ouMat_isHermitian (UNModel.ba sz0) n 0 ω).eigenvalues
            ∂(ouP (UNModel.ba sz0) n)) -
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((1 + 1 / ((n : ℝ) + 1)) • α)) 0
            (ouMat_isHermitian (UNModel.ba sz0) n (ouTStar sz0 τU n) ω).eigenvalues
            ∂(ouP (UNModel.ba sz0) n)))
        atTop (𝓝 0)
theorem instance_greenCorrAll :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      (∀ nf ≤ 1, UNClaim417 sz0 (UNModel.band sz0) 0 nf τU 1 1) →
      UNApriori sz0 (UNModel.band sz0) 0 →
      Tendsto (fun n =>
        (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
            (ouMat_isHermitian (UNModel.band sz0) n 0 ω).eigenvalues
            ∂(ouP (UNModel.band sz0) n)) -
        (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
            (ouMat_isHermitian (UNModel.band sz0) n (ouTStar sz0 τU n) ω).eigenvalues
            ∂(ouP (UNModel.band sz0) n)))
        atTop (𝓝 0)
theorem instance_greenCorrAll_tauU
    (h417 : ∀ nf ≤ 1, UNClaim417 sz0 (UNModel.ba sz0) 0 nf (1 / 10) 1 1)
    (hap : UNApriori sz0 (UNModel.ba sz0) 0) :
    Tendsto (fun n : ℕ =>
      (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((1 + 1 / ((n : ℝ) + 1)) • α)) 0
          (ouMat_isHermitian (UNModel.ba sz0) n 0 ω).eigenvalues
          ∂(ouP (UNModel.ba sz0) n)) -
      (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((1 + 1 / ((n : ℝ) + 1)) • α)) 0
          (ouMat_isHermitian (UNModel.ba sz0) n (ouTStar sz0 (1 / 10) n) ω).eigenvalues
          ∂(ouP (UNModel.ba sz0) n)))
      atTop (𝓝 0)
```

Statement comparison with RBM2D `c9a24cf` (`python3 cmp2.py src.lean GreenCorr.lean`): every other ported statement, the (A) renamings applied to the RBM2D text first:
```
(A) renamings applied to the RBM2D text: \(d : Sizes\) -> (sz : Sizes d) (M : UNModel sz) ; \(\(d\.size n : ℕ\) : ℝ\) -> Nsz sz n ; d\.size -> sz.size ; \(d\.L n\) \(d\.W n\) -> M n ; ouTStar d  -> ouTStar sz  ; Claim417 d  -> UNClaim417 sz M  ; AprioriImM d E -> UNApriori sz M E ...
gcc_card_idx: DROPPED (Sizes.card_Idx)
IDENTICAL or (A)-renaming only: gcc_continuous_eigenvalues₀_subtype, gcc_continuous_eigenvalues_subtype, gcc_measurable_eigenvalues, gccSpec, gccSpec_nonneg, gccSpec_le, gccSpec_measurable, gcc_stieltjes_im_eq, gcc_stieltjes_im_eq_inv, gcc_imInv_props, gcc_main, gcc_fullSum_integrable, gcc_err, gcc_piece, gcc_kPoint_expand, gcc_prefactor_le, gcc_ouTStar_nonneg(A-only), gccCmax, gccCmax_nonneg, le_gccCmax
NEW: gcc_poissonKernel_smul, gcc_poissonSmooth_comp_smul, gcc_integral_abs_comp_smul, gcc_lorentz_smul_le
--- gcc_step -> greenCorr_step (after (A) renamings)
-private theorem gcc_step {k : ℕ} {O : (Fin k → ℝ) → ℝ} (E : ℝ)
-    {τU c' C R Nr : ℝ} (Cn : ℕ → ℝ) (hτU : 0 < τU) (hCn : ∀ nf ≤ k, Cn nf ≤ C)
-    (hR : 0 < R + 1) {ι : Type} [Fintype ι] (c : ι → ℤ) (kk : ι → ℕ)
+theorem greenCorr_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
+    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
+    {H0 H1 : Ω → Matrix ι ι ℂ} (hm0 : Measurable H0) (hm1 : Measurable H1)
+    (hH0 : ∀ ω, (H0 ω).IsHermitian) (hH1 : ∀ ω, (H1 ω).IsHermitian)
+    {k : ℕ} {O : (Fin k → ℝ) → ℝ} (E : ℝ)
+    {τU c' C R Nr ε₀ : ℝ} (Cn : ℕ → ℝ) (hτU : 0 < τU) (hCn : ∀ nf ≤ k, Cn nf ≤ C)
+    (hR : 0 < R + 1) {κ : Type} [Fintype κ] (c : κ → ℤ) (kk : κ → ℕ)
-    (Cs : ι → ℝ) (hCs0 : ∀ i, 0 ≤ Cs i)
-    (hCs : ∀ i, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : Fin (kk i) → ℝ,
+    (Cs : κ → ℝ) (hCs0 : ∀ i, 0 ≤ Cs i)
+    (hCs : ∀ i, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x : Fin (kk i) → ℝ,
-    (hcardN : (Fintype.card (ι) : ℝ) = Nr) (hNr1 : 1 ≤ Nr)
-    (h2k : 2 * k ≤ Fintype.card (ι))
+    (hε₀ : Nr ^ (-τU) ≤ ε₀)
+    (hcardN : (Fintype.card ι : ℝ) = Nr) (hNr1 : 1 ≤ Nr)
+    (h2k : 2 * k ≤ Fintype.card ι)
-      ∫ ω, (stieltjesN (H0 ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ nf
-        ∂P ≤ Nr ^ (τU / 2)) :
+      ∫ ω, (stieltjesN (H0 ω) ((E : ℂ) + ((Nr : ℂ))⁻¹ * Complex.I)).im ^ nf ∂P ≤
+        Nr ^ (τU / 2)) :
--- gcc_quantitative -> gcc_quantitative (after (A) renamings)
-    (hap : UNApriori sz M E) :
+    (hap : UNApriori sz M E) (r : ℕ → ℝ) {a b : ℝ} (ha : 0 < a)
+    (hr : ∀ᶠ n in atTop, a ≤ r n ∧ r n ≤ b) :
-      |(∫ ω, kPoint k O E (ouMat_isHermitian M n 0 ω).eigenvalues
+      |(∫ ω, kPoint k (fun α => O (r n • α)) E (ouMat_isHermitian M n 0 ω).eigenvalues
-        ∫ ω, kPoint k O E (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues
-            ∂(ouP M n)| ≤
+        ∫ ω, kPoint k (fun α => O (r n • α)) E
+            (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)| ≤
--- gcc_tendsto -> gcc_tendsto (after (A) renamings)
-private theorem gcc_tendsto (sz : Sizes d) (M : UNModel sz) (hsize : Tendsto (fun n => sz.size n) atTop atTop)
+private theorem gcc_tendsto (sz : Sizes d) (M : UNModel sz)
+    (hsize : Tendsto (fun n => sz.size n) atTop atTop)
-    {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) :
+    {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) (r : ℕ → ℝ) {a b : ℝ} (ha : 0 < a)
+    (hr : ∀ᶠ n in atTop, a ≤ r n ∧ r n ≤ b) :
-      (∫ ω, kPoint k O E (ouMat_isHermitian M n 0 ω).eigenvalues
+      (∫ ω, kPoint k (fun α => O (r n • α)) E (ouMat_isHermitian M n 0 ω).eigenvalues
-      (∫ ω, kPoint k O E (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues
-          ∂(ouP M n)))
+      (∫ ω, kPoint k (fun α => O (r n • α)) E
+          (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n)))
--- greenCorrAll -> unGreenCorr (after (A) renamings)
-theorem greenCorrAll : GreenCorrAll
+theorem unGreenCorr {d : ℕ} (sz : Sizes d) (hsize : Tendsto (fun n => sz.size n) atTop atTop)
+    (M : UNModel sz) : UNGreenCorr sz M
```

```
grep -rnw unGreenCorr RBM3D RBM3D.lean, excluding GreenCorr.lean:        0 hits
grep -rnw greenCorrAll RBM3D RBM3D.lean, excluding GreenCorr.lean:        0 hits
grep -rnw greenCorr_step RBM3D RBM3D.lean, excluding GreenCorr.lean:        0 hits
grep -rnw GreenCorrCheck RBM3D RBM3D.lean, excluding GreenCorr.lean:        0 hits
grep -rn 'gcc_\|gccSpec\|gccCmax' RBM3D RBM3D.lean, excluding GreenCorr.lean:        0 hits
hygiene grep 'sorry|admit|native_decide|^axiom' in GreenCorr.lean: 0 hits; public theorems: 8, defs: 0; lines:     1004
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  ->  9e0f275 (HEAD); port source is c9a24cf:RBM2D/Universality/GreenCorr.lean (810 lines)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GreenCorr.lean
 RBM2D/Universality/GreenCorr.lean | 156 +++++++++-----------------------------
 1 file changed, 36 insertions(+), 120 deletions(-)
$ git log -1 --format="%h %an <%ae>"
939857e Jun Yin <321276894+JYin80@users.noreply.github.com>
$ git diff main...t/T2188 --stat
 RBM3D/Test/Axioms.lean            |    2 -
 RBM3D/Universality/GreenCorr.lean | 1004 +++++++++++++++++++++++++++++++++++++
 2 files changed, 1004 insertions(+), 2 deletions(-)
```

Narrative.
- Route as in the ticket: the 15 `Generic`-section declarations and `gcc_prefactor_le` are copied with identical statements (comparison above); `gcc_main`, `gcc_err` keep their statements, and their proofs rewrite `stieltjesN` to `InjSum_stieltjes` by `InjSum_stieltjesN_eq_stieltjes` before `sum_poissonSmooth_eq` / `sum_prod_lorentz_eq`.
- (A): `gcc_step` is `greenCorr_step` on a generic carrier (probability measure `P`, two measurable Hermitian families `H0 H1`, index type `ι`); `gcc_card_idx` (the only `Z2` token) is replaced by `Sizes.card_Idx`; `open RBM.Endpoints` is dropped.
- (B): `gcc_quantitative` decomposes `O` once (`injSum_decomp`, `R ≥ 1`), rescales it by `r n` (`Oj' i = Oj i (r n ·)`, support radius `R / a`, window `C₀ = R / a + 1`), and applies `greenCorr_step` with `Cs' i = Cs i * max 1 b * (max 1 a⁻²)^k`. The uniform constant is `K̄ = 2^k Σ_i |c_i| ((max 1 a⁻¹)^k ∫|Oj i| + 2 (Cs i * max 1 b * (max 1 a⁻²)^k))`, independent of `n` and `r`, as in (a). Scaling facts: `gcc_integral_abs_comp_smul` (B-i), `gcc_poissonKernel_smul`, `gcc_poissonSmooth_comp_smul`, `gcc_lorentz_smul_le` (B-ii). The extra eventuality `N^{-τ_U} ≤ (max 1 b)⁻¹` is `e5` in `gcc_quantitative`.
- Nothing beyond a rescaling was needed, so the stop clause of the ticket was not triggered; no hypothesis was added, no pinned signature changed.
- `greenCorr_step` takes `ε₀` and `hε₀ : Nr^(-τU) ≤ ε₀`, and `hCs` for `ε ≤ ε₀`; the ticket's `ε₀ ≤ 1` is not a hypothesis, because `ε = Nr^(-τU) ≤ 1` is already derived from `1 ≤ Nr` inside the proof.
- `Real.pi_gt_three` is not reachable from the imports (unknown constant at the first compile); `gcc_piece` uses `Real.two_le_pi` instead.
- Registry: the two owed lines `RBM.Univ.UNGreenCorr` and `RBM.Univ.UNGreenCorrAll` were deleted from `RBM3D/Test/Axioms.lean` (they stood at lines 185 and 200 of the worktree file at `fbaa460`, the ticket says `:186`, `:201`; deleted by content). The pre-check above has exit 0.
- Instances: band model with the constant dilation `r ≡ rhoSC 0`; block Anderson model with `r_n = 1 + 1/(n+1)` (`a = 1`, `b = 2`, `r_0 ≠ r_1` is a conjunct); `greenCorrAll` at `d = 3`; explicit `τ_U = 1/10` through `gcc_tendsto` with `Cmax = 1`, `τ₀ = 1/4`.
- Root import for the hub: `import RBM3D.Universality.GreenCorr` after the last import line of `RBM3D.lean`.

## (c) Verified Mathlib names (all compile in this file; locations by grep)
- `MeasureTheory.Measure.integral_comp_smul` (`Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:92`)
- `Module.finrank_fin_fun` (`Mathlib/LinearAlgebra/Dimension/Constructions.lean:326`)
- `Real.two_le_pi` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:147`)
- `inv_anti₀` (`Algebra/Order/GroupWithZero/Basic.lean:1221`), `div_le_div_iff₀` (`:1424`), `pow_le_pow_right₀` (`:501`), `pow_le_pow_left₀` (`:514`)
- `Finset.prod_le_prod₀` (`Algebra/Order/BigOperators/GroupWithZero/Finset.lean:39`)
- `tendsto_natCast_atTop_iff` (`Order/Filter/AtTopBot/Archimedean.lean:35`), `tendsto_natCast_atTop_atTop` (`:44`)
- `tendsto_rpow_neg_atTop` (`Analysis/SpecialFunctions/Pow/Asymptotics.lean:50`), `eventually_all_finset` (`Order/Filter/Finite.lean:258`)
- `Finset.sup'_const` (`Data/Finset/Lattice/Fold.lean:581`), `gt_mem_nhds` (`Topology/Order/Basic.lean:123`, `to_dual`), `div_le_one` (`Algebra/Order/Field/Basic.lean:43`)
- Absent from the imports of this file: `Real.pi_gt_three` (needs `Mathlib.Analysis.Real.Pi.Bounds`; `unknown constant` at compile).

## (d) Open issues and paper-delta candidates
- No (a′) section: nothing in (a) was found wrong. No new paper-delta candidate; the generalisation to dilation sequences is the existing D385 (T2162d).
- `UNClaim417` and `UNApriori` (other gates' pins) remain hypotheses of `unGreenCorr`, as pinned; no certificate for them exists (`non-vacuity certificates: 0 of 129` in the pre-check).
- `greenCorr_step` is an extra public name (recommended by the ticket for UN-01b, DECISIONS §57 (1)); it has no pin and no instance of its own, it is applied inside `unGreenCorr`.
- Hub at merge: add the root import; `lake build` of the library was run on the branch without it (output above).
