Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct  5 14:23:35 UTC 2026
Scope: T2187 adds no new exponent; it copies pins whose exponents are those of T2173 (a)(i) (`ε₀ = 𝔡/3`, `c = 𝔡/6`, `c' = 𝔠𝔡/30`, `C = 21`), and bridges that are matrix identities. `μ` = `M.mean`, `g` = `lam`. Data `sz0` (`RBM3D/Defs/Sizes.lean:260-263`): `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = (WL)^3 = 2^21 (n+1)^18`; `sz0_admissible : sz0.Admissible (1/6) (1/10)` (`Sizes.lean`). Script `pre.py` (python3, numpy, mpmath; no Lean), output pasted below.
### (i) Exponent table (d = 3; `(𝔠,𝔡) ∈ {(1/6,1/10), (1/10,1/20)}`)
| quantity | value at (1/6,1/10); (1/10,1/20) | constraint | slack |
|---|---|---|---|
| `𝔠` | 1/6; 1/10 | `0 < 𝔠`, `W ≥ N^𝔠` (`Sizes.Bandwidth`), `d𝔠 < 1` | `1 − 3𝔠` = 1/2; 7/10 |
| `𝔡` | 1/10; 1/20 | `0 < 𝔡`; `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`Sizes.WO`) | at `sz0`, `n = 0`: `1/128 ≤ 1/64 ≤ 10` |
| `ε₀ = 𝔡/3` | 1/30; 1/60 | `0 < ε₀ < 𝔡/2` | 1/60; 1/120 |
| `c = 𝔡/6` | 1/60; 1/120 | `0 < c < ε₀`, `c < 𝔡/5` | vs `ε₀`: 1/60; 1/120; vs `𝔡/5`: 1/300; 1/600 |
| QUE exponent | `−(2ε₀ ∧ 2𝔡/5) + 2c = −𝔡/15` = −1/150; −1/300 | equals `−𝔡/15` | exact |
| `c'` | `min(𝔠𝔡/6, 𝔠(𝔡/15 − 𝔡/30)) = 𝔠𝔡/30` = 1/1800; 1/6000 | `c' > 0`; the literal `𝔠 * 𝔡 / 30` in `UNJakUywRowk`/`UNClaimRowk` | exact |
| `C` (Claim 417 constant) | 21 | exponent `−c' + Cτ_U ≤ −c'/2` | at `τ_U = c'/(2(C+1))` = 1/79200; 1/264000: `−c' + Cτ_U` = −23/79200; −23/264000, slack `c'/2 − Cτ_U` = 1/79200; 1/264000 |
| `τ_U` | ≤ 1/79200; ≤ 1/264000 | `0 < τ_U ≤ τ₀`, `τ₀` existential in rows | `t* = N^{-1+τ_U} ∈ (0,1)` |
| `τ_s` (`UNTrLocalInit`, `ouTStar sz τs`) | `0 < τ_s < 1`; `UNL32` data `τ_s ≤ 𝔠𝔡 = 1/60` (`Pins.lean`, `inst_step1_floor`) | `UNL32` premises need `N^{τ_s/2} ≥ 2` | `τ_s = 1/60`: first `n = 45` (`N_n/2^120 = 1.342`); `τ_s = 1/2`: `n = 0` (`N/2^4 = 131072`) |
| flow identity 1 | `ouMatC = ouMat + (1 − e^{-t/2}) μ` | `T2187_ouMatC_eq_ouMat_add` | residual 5.55e-17 (nonzero `μ`, `t = 0.7`) |
| flow identity 2 | `μ = 0 ⇒ ouMatC = ouMat`; `ouInit(μ=0) = e^{-t/2} H`; `ouMatC(t=0) = H` | bridges `ouMatC_toC`, `ouInit_toC`, `ouMatC_zero` | residual 0 |
| flow identity 3 | `ouMatC = ouInit + √(1−e^{-t}) H'` | `ouMatC_eq_ouInit_add` | residual 0 |
| mean `0` vs `μ ≠ 0` | `max|ouMatC − ouMat|` = 0.0886 = `(1−e^{-0.35})·0.3` at `t = 0.7` | `inst_ouMatC_ne_ouMat` | at `sz0`, `n = 0`, adjacent-block entry: `(1−e^{-0.35})/64` = 0.00461 > 0 |
### (ii) One concrete nondegenerate instance
Data: `sz0`, `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`; `(𝔠,𝔡) = (1/6,1/10)`, `κ = 1/10`, `E = 0`, `δ = 1/2`, `E' = 0`, `k = 1`, `ρ = rhoSC 0`, `𝒪 = bump`, `τ_U = 1/79200`. Hypotheses checked: Admissible (`W ≥ N^{1/6}`, `(eq:WO)`, for all `n < 10^5` and by `W^6 ≥ N`, `W^{-7/5} = (2(n+1))^{-7} ≤ (2(n+1))^{-6} ≤ 10`), bulk `|0| ≤ 2 − κ`, `δ > 0`, `|E'| < 2`, `k ≥ 1`, window of (417) nonempty (`z = E + i/N`), nonzero mean entry `lam·Ψ_ij = 1/64` at adjacent blocks `(0,0,0) ~ (1,0,0)`, matrix identities at `d = 3`, `L = 3`, `W = 2`, `N = 216`, `λ = 0.3`, `t ∈ {0, 0.7}`, `V` block-diagonal GUE, `H' ` GUE, seed 7.
`$ cd .../scratchpad/T2187 && python3 pre.py` (30 lines):
```
== (i) exponent table, exact ==
c=1/6 d=1/10: eps0=1/30 (<d/2=1/20, slack 1/60) c_Q=1/60 (<eps0 slack 1/60; <d/5 slack 1/300) QUE=-1/150 (=-d/15 True) c'=1/1800 tauU<=1/79200 -c'+C*tauU=-23/79200 <= -c'/2=-1/3600 slack 1/79200  3c<1 slack 1/2  lam range W^(-3/2+d)..1/d  all=True
c=1/10 d=1/20: eps0=1/60 (<d/2=1/40, slack 1/120) c_Q=1/120 (<eps0 slack 1/120; <d/5 slack 1/600) QUE=-1/300 (=-d/15 True) c'=1/6000 tauU<=1/264000 -c'+C*tauU=-23/264000 <= -c'/2=-1/12000 slack 1/264000  3c<1 slack 7/10  lam range W^(-3/2+d)..1/d  all=True

== matrix identities, d=3 L=3 W=2 N=216 ==
N= 216 ||Psi||= 6.000000000000002 hermitian True
mu=lam*Psi t=0.0: |ouMatC-(ouMat+(1-e^-t/2)mu)|=0.00e+00  |ouMatC-ouMat|=0.00e+00  |ouMatC-(ouInit+sqrt(1-e^-t)H')|=0.00e+00  |ouMatC(t=0)-H|=0.00e+00  |ouInit(mu=0)-e^(-t/2)H|=nan
mu=lam*Psi t=0.7: |ouMatC-(ouMat+(1-e^-t/2)mu)|=5.55e-17  |ouMatC-ouMat|=8.86e-02  |ouMatC-(ouInit+sqrt(1-e^-t)H')|=0.00e+00  |ouMatC(t=0)-H|=0.00e+00  |ouInit(mu=0)-e^(-t/2)H|=nan
mu=0 t=0.0: |ouMatC-(ouMat+(1-e^-t/2)mu)|=0.00e+00  |ouMatC-ouMat|=0.00e+00  |ouMatC-(ouInit+sqrt(1-e^-t)H')|=0.00e+00  |ouMatC(t=0)-H|=0.00e+00  |ouInit(mu=0)-e^(-t/2)H|=0.00e+00
mu=0 t=0.7: |ouMatC-(ouMat+(1-e^-t/2)mu)|=0.00e+00  |ouMatC-ouMat|=0.00e+00  |ouMatC-(ouInit+sqrt(1-e^-t)H')|=0.00e+00  |ouMatC(t=0)-H|=0.00e+00  |ouInit(mu=0)-e^(-t/2)H|=0.00e+00
mu nonzero: |ouMatC-ouMat|_max at t=0.7 = 0.08859357308438598  (1-e^-0.35)*lam*1 = 0.08859357308438597

== (ii) instance sz0, n=0 ==
L,W,N,lam = 4 32 2097152 1/64
W>=N^c: W^6>=N: True  N^(1/6)= 11.31370849898476  W= 32
WO: W^(-3/2+d)= 0.007812500000000002  <= lam= 0.015625  <= 1/d= 10 True
Bandwidth(W^6>=N) and WO lower/upper hold for all n<1e5; failures: []
kappa=1/10: |E|=0 <= 2-kappa= 19/10 True | delta>0 True | |E'|<2 True | k=1>=1
InWindow nonempty: z=E+i/N: N^(-1-tau)=4.767495e-07 <= 1/N=4.768372e-07 <= N^(-1+tau)=4.769248e-07 : True
t*=N^(-1+tau)= 4.769248036934783e-07  in [0,1]
blocks a=(0,0,0),b=(1,0,0) adjacent in Z_4^3: True  lam_0*Psi_ij = 1/64 !=0 True
ouMatC-ouMat entry at (i,j) adjacent, t=0.7: (1-e^{-t/2})*lam_0 = 0.0046142485981451025  >0

== external hypothesis UNL32: limit computation of arithmetic premises (UNL32 premises in N,tau only) ==
N=2097152 tau=1/2: ((True, True, True, True, True, True), True)
N=65536 tau=1/8 (sharp N=2^(2/tau)): ((True, True, True, True, True, True), True)
tau_s=1/2: need N>=2^4; first n with N_n=2^21(n+1)^18 >= threshold: n=0, N_n/2^4=131072.000; monotone so holds for all n>=n0
   premises at that n: ((True, True, True, True, True, True), True)
tau_s=1/60: need N>=2^120; first n with N_n=2^21(n+1)^18 >= threshold: n=45, N_n/2^120=1.342; monotone so holds for all n>=n0
   premises at that n: ((True, True, True, True, True, True), True)
```
External hypothesis `UNL32` (borrowed; DECISIONS §5; kept as a hypothesis of the instances `inst_bUniv_band_k`, `inst_coreC_band`; untouched here): its premises involve only `N` and `τ`; the limit computation above (mpmath, 200 digits; premise 1 `N^σ/N ≤ g` is an equality when `σ = τ/4`, tested with relative tolerance 1e-150) holds at `N = 2^21`, `τ = 1/2`, at the sharp point `N = 2^16`, `τ = 1/8` (`N^{τ/2} = 2`), and along `sz0` from `n = 45` for `τ_s = 1/60`, with `N_n` increasing. Not astronomically large: `N_45 ≈ 1.34·2^120` is only the `eventually` threshold; the instances themselves are at `n = 0` with `UNL32`, `UNGUELocal`, `UNGreenCorrAll(C)`, `UNTrLocal`, `UNTrLocalInit` as hypotheses (other gates' pins, as in merged `inst_core_band`).
### Verdict per target
1 Vocabulary and flow identities (target 1): PASS (identities 1-3 verified; `ouMatC_zero` is `μ + (H − μ) + √0·X = H`, residual 0).
2 Claim-level copies and mean-0 bridges (target 2): PASS (no exponent or hypothesis change: the copies differ from the merged pins only by the flow `ouMatC`, which equals `ouMat` at mean `0` (identity 2)).
3 Class and generic pins (target 3): PASS (exponents as T2173 (a)(i): `ε₀`, `c`, `c' = 𝔠𝔡/30` close with the slacks above).
4 Band bridges and instances (target 4 and instances): PASS (every deterministic hypothesis holds at the instance; `UNKind.band` has `bulk = (|E| ≤ 2 − κ)`, constant in `n`, so `∀ᶠ n` is `Filter.eventually_const`).
Overall: **PASS**.
## (b) Script output — Mon Oct  5 14:42:31 UTC 2026
Branch `t/T2187`, commit `c167e00546e6cc3c0cff08589c4fd8ba5eb9eec3` (identity Jun Yin). Files: `RBM3D/Universality/PinsK.lean` (752 lines, new; `import RBM3D.Universality.Pins` only), `RBM3D/Test/Axioms.lean` (registry lines).
```
$ git diff --stat main...t/T2187
 RBM3D/Test/Axioms.lean        |  18 +
 RBM3D/Universality/PinsK.lean | 752 ++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 770 insertions(+)
$ lake build RBM3D.Universality.PinsK 2>&1 | tail -1
Build completed successfully (3329 jobs).
$ lake lean RBM3D/Universality/PinsK.lean 2>&1 | grep -c PinsK        (the other output lines are replayed Defs/Tail.lean long-line warnings)
0
$ lake build            (worktree, full; exit 0; root RBM3D.lean does not import PinsK yet, the hub adds it at merge)
info: RBM3D.lean:232:0: axiom audit: 5397 theorems, 1905 definitions, 0 axioms in `RBM` ... 
Build completed successfully (3990 jobs).
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/PinsK.lean   ->  (no output)
```
### Axioms of every declaration of the module (scratch `axioms.lean`: `import RBM3D.Universality.PinsK` + `collectAxioms` over the module's constants, grouped by axiom set)
```
theorems: 48, definitions/structures: 46 axiom set [propext, Classical.choice, Quot.sound] (94): [RBM.Univ.UNClaim417C, RBM.Univ.UNClaim417C_toC, RBM.Univ.UNClaimAllC, RBM.Univ.UNClaimAllC_toC, RBM.Univ.UNClaimRowk, RBM.Univ.UNClaimRowk_band, RBM.Univ.UNCoreC, RBM.Univ.UNEMCTE2Rowk, RBM.Univ.UNEMCTE2Rowk_band, RBM.Univ.UNEMCTE2k, RBM.Univ.UNEMCTE2k_band, RBM.Univ.UNGreenCorrAllC, RBM.Univ.UNGreenCorrC, RBM.Univ.UNGreenCorrC_toC, RBM.Univ.UNInfty1C, RBM.Univ.UNInfty1C_toC, RBM.Univ.UNJakUywRowk, RBM.Univ.UNJakUywRowk_band, RBM.Univ.UNJakk, RBM.Univ.UNJakk_band, RBM.Univ.UNKind, RBM.Univ.UNLocAvgk, RBM.Univ.UNLocAvgk_band, RBM.Univ.UNModelC, RBM.Univ.UNOUClaimsk, RBM.Univ.UNOUClaimsk_band, RBM.Univ.UNOUDiagk, RBM.Univ.UNOUDiagk_band, RBM.Univ.UNOUQUEk, RBM.Univ.UNOUQUEk_band, RBM.Univ.UNOUQUEk_zero_of_UNQuek, RBM.Univ.UNOURowk, RBM.Univ.UNOURowk_band, RBM.Univ.UNQuek, RBM.Univ.UNQuek_band, RBM.Univ.UNStep1GoodC, RBM.Univ.UNTrLocalInit, RBM.Univ.UNUnivMainC, RBM.Univ.UNUnivMainC_toC, RBM.Univ.UNUywk, RBM.Univ.UNUywk_band, RBM.Univ.ouInit, RBM.Univ.ouInit_isHermitian, RBM.Univ.ouInit_toC, RBM.Univ.ouMatC, RBM.Univ.ouMatC_eq_ouInit_add, RBM.Univ.ouMatC_eq_ouMat_add, RBM.Univ.ouMatC_isHermitian, RBM.Univ.ouMatC_toC, RBM.Univ.ouMatC_toC_apply, RBM.Univ.ouMatC_zero, RBM.Univ.ouP_cylinder, RBM.Univ.unPinsK_band_M, RBM.Univ.unPinsK_band_bulk, RBM.Univ.unPinsK_toC_toUNModel, RBM.Univ.un_claimAll_of_rowsk, RBM.Univ.un_claimAll_of_rowsk_band, RBM.Univ.vOUC, RBM.Univ.UNGreenCorrAllC.toAll, RBM.Univ.UNKInst.inWindow_nonempty, RBM.Univ.UNKInst.inst_OUQUEk_zero_band, RBM.Univ.UNKInst.inst_bUniv_band_k, RBM.Univ.UNKInst.inst_claimAllC_band, RBM.Univ.UNKInst.inst_claimAll_band_k, RBM.Univ.UNKInst.inst_coreC_band, RBM.Univ.UNKInst.inst_ouMatC_ne_ouMat, RBM.Univ.UNKind.M, RBM.Univ.UNKind.band, RBM.Univ.UNKind.bulk, RBM.Univ.UNKind.casesOn, RBM.Univ.UNKind.ctorIdx, RBM.Univ.UNKind.lamV, RBM.Univ.UNKind.mdet, RBM.Univ.UNKind.noConfusion, RBM.Univ.UNKind.noConfusionType, RBM.Univ.UNKind.recOn, RBM.Univ.UNModel.toC, RBM.Univ.UNModelC.casesOn, RBM.Univ.UNModelC.ctorIdx, RBM.Univ.UNModelC.mean, RBM.Univ.UNModelC.mean_herm, RBM.Univ.UNModelC.noConfusion, RBM.Univ.UNModelC.noConfusionType, RBM.Univ.UNModelC.recOn, RBM.Univ.UNModelC.toUNModel, RBM.Univ.UNKind.mk.inj, RBM.Univ.UNKind.mk.injEq, RBM.Univ.UNKind.mk.noConfusion, RBM.Univ.UNKind.mk.sizeOf_spec, RBM.Univ.UNModelC.mk.congr_simp, RBM.Univ.UNModelC.mk.inj, RBM.Univ.UNModelC.mk.injEq, RBM.Univ.UNModelC.mk.noConfusion, RBM.Univ.UNModelC.mk.sizeOf_spec] 
```
The script printed `theorems: 48, definitions/structures: 46`: all 94 theorem/definition constants of the module (structure projections and structure-generated `mk.inj`, `mk.injEq`, `UNModelC.mk.congr_simp` included) depend on exactly `propext`, `Classical.choice`, `Quot.sound`; 5445 - 5397 = 48 matches the theorem counts of the two audits.
### Target statements, extracted from the file by script (`stmts.py`: docstrings dropped, whitespace normalised; for `def` only the header, the body is compared by the diffs below)
```
structure UNModelC {d : ℕ} (sz : Sizes d) extends UNModel sz
def UNModel.toC {d : ℕ} {sz : Sizes d} (M : UNModel sz) : UNModelC sz := ⟨body: see diff⟩
def ouMatC (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := ⟨body: see diff⟩
def ouInit (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := ⟨body: see diff⟩
theorem ouMatC_isHermitian (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : (ouMatC M n t ω).IsHermitian
theorem ouMatC_zero (M : UNModelC sz) (n : ℕ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC M n 0 ω = M.H n ω.1
theorem ouInit_isHermitian (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) : (ouInit M n t ω).IsHermitian
theorem ouMatC_eq_ouInit_add (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC M n t ω = ouInit M n t ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
theorem ouMatC_eq_ouMat_add (M : UNModelC sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC M n t ω = ouMat M.toUNModel n t ω + (1 - Real.exp (-t / 2)) • M.mean n
theorem ouMatC_toC_apply (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : ouMatC M.toC n t ω = ouMat M n t ω
theorem ouMatC_toC (M : UNModel sz) : ouMatC M.toC = ouMat M
theorem ouInit_toC (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) : ouInit M.toC n t ω = Real.exp (-t / 2) • M.H n ω
def UNClaim417C (sz : Sizes d) (M : UNModelC sz) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) : Prop := ⟨body: see diff⟩
def UNClaimAllC (sz : Sizes d) (M : UNModelC sz) (E : ℝ) : Prop := ⟨body: see diff⟩
theorem UNClaim417C_toC (M : UNModel sz) (E : ℝ) (nf : ℕ) (τU c' Cn : ℝ) : UNClaim417C sz M.toC E nf τU c' Cn ↔ UNClaim417 sz M E nf τU c' Cn
theorem UNClaimAllC_toC (M : UNModel sz) (E : ℝ) : UNClaimAllC sz M.toC E ↔ UNClaimAll sz M E
def UNGreenCorrC (sz : Sizes d) (M : UNModelC sz) : Prop := ⟨body: see diff⟩
def UNGreenCorrAllC : Prop := ⟨body: see diff⟩
def UNInfty1C (sz : Sizes d) (M : UNModelC sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop := ⟨body: see diff⟩
def UNUnivMainC (sz : Sizes d) (M : UNModelC sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : Prop := ⟨body: see diff⟩
theorem UNGreenCorrC_toC (M : UNModel sz) : UNGreenCorrC sz M.toC ↔ UNGreenCorr sz M
theorem UNInfty1C_toC (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : UNInfty1C sz M.toC ρ E E' k O τU ↔ UNInfty1 sz M ρ E E' k O τU
theorem UNUnivMainC_toC (M : UNModel sz) (ρ : ℕ → ℝ) (E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ) (τU : ℝ) : UNUnivMainC sz M.toC ρ E k O τU ↔ UNUnivMain sz M ρ E k O τU
theorem UNGreenCorrAllC.toAll (h : UNGreenCorrAllC) : UNGreenCorrAll
def UNTrLocalInit (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop := ⟨body: see diff⟩
def vOUC (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ sz) : Idx d (sz.L n) (sz.W n) → ℝ := ⟨body: see diff⟩
def UNStep1GoodC : Prop := ⟨body: see diff⟩
def UNCoreC : Prop := ⟨body: see diff⟩
structure UNKind (d : ℕ)
def UNKind.band (d : ℕ) : UNKind d where M := ⟨body: see diff⟩
def UNOUQUEk (K : UNKind d) (sz : Sizes d) (𝔡 τU : ℝ) : Prop := ⟨body: see diff⟩
def UNOUDiagk (K : UNKind d) (sz : Sizes d) (τU : ℝ) : Prop := ⟨body: see diff⟩
def UNEMCTE2k (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : Prop := ⟨body: see diff⟩
def UNJakk (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop := ⟨body: see diff⟩
def UNUywk (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop := ⟨body: see diff⟩
def UNQuek (K : ∀ d, UNKind d) : Prop := ⟨body: see diff⟩
def UNLocAvgk (K : ∀ d, UNKind d) : Prop := ⟨body: see diff⟩
def UNOUClaimsk (K : ∀ d, UNKind d) : Prop := ⟨body: see diff⟩
def UNOURowk (K : ∀ d, UNKind d) (ML Loc Que : Prop) : Prop := ⟨body: see diff⟩
def UNEMCTE2Rowk (K : ∀ d, UNKind d) : Prop := ⟨body: see diff⟩
def UNJakUywRowk (K : ∀ d, UNKind d) (Loc : Prop) : Prop := ⟨body: see diff⟩
def UNClaimRowk (K : ∀ d, UNKind d) : Prop := ⟨body: see diff⟩
theorem un_claimAll_of_rowsk (K : ∀ d, UNKind d) {ML Loc Que : Prop} (rC : UNClaimRowk K) (rE : UNEMCTE2Rowk K) (rJ : UNJakUywRowk K Loc) (rO : UNOURowk K ML Loc Que) (hML : ML) (hLoc : Loc) (hQ : Que) : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E
theorem ouP_cylinder (M : UNModelC sz) (n : ℕ) (S : Set (Sizes.SeqΩ sz)) : ouP M.toUNModel n {ω | ω.1 ∈ S} = M.μ S
theorem UNOUQUEk_zero_of_UNQuek (K : ∀ d, UNKind d) (hQ : UNQuek K) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) (κ τQ : ℝ) (hκ : 0 < κ) (hτ : 0 < τQ) : ∀ᶠ n in atTop, ∀ E : ℝ, (K d).bulk sz κ E n → ∀ a : Zd d (sz.L n), ouP ((K d).M sz).toUNModel n {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) (𝔡 / 3) (𝔡 / 6) E a (ouMatC ((K d).M sz) n 0 ω)} ≤ queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ
theorem UNOUQUEk_band (sz : Sizes d) (𝔡 τU : ℝ) : UNOUQUEk (UNKind.band d) sz 𝔡 τU ↔ UNOUQUE sz 𝔡 τU
theorem UNOUDiagk_band (sz : Sizes d) (τU : ℝ) : UNOUDiagk (UNKind.band d) sz τU ↔ UNOUDiag sz τU
theorem UNEMCTE2k_band (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : UNEMCTE2k (UNKind.band d) sz E nf τU Cn ↔ UNEMCTE2 sz E nf τU Cn
theorem UNJakk_band (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : UNJakk (UNKind.band d) sz E nf τU C c' ↔ UNJak sz E nf τU C c'
theorem UNUywk_band (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : UNUywk (UNKind.band d) sz E nf τU C c' ↔ UNUyw sz E nf τU C c'
theorem UNQuek_band : UNQuek (fun d => UNKind.band d) ↔ UNQueBand
theorem UNLocAvgk_band : UNLocAvgk (fun d => UNKind.band d) ↔ UNLocAvgBand
theorem UNOUClaimsk_band : UNOUClaimsk (fun d => UNKind.band d) ↔ UNOUClaims
theorem UNOURowk_band : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNOURow
theorem UNEMCTE2Rowk_band : UNEMCTE2Rowk (fun d => UNKind.band d) ↔ UNEMCTE2Row
theorem UNJakUywRowk_band : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand ↔ UNJakUywRow
theorem UNClaimRowk_band : UNClaimRowk (fun d => UNKind.band d) ↔ UNClaimRow
theorem un_claimAll_of_rowsk_band (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d)) (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand) (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E
theorem inWindow_nonempty (sz : Sizes 3) (E C₀ τU : ℝ) (n : ℕ) (hC : 0 ≤ C₀) (hτ : 0 ≤ τU) : InWindow sz E C₀ τU n ⟨E, (Nsz sz n)⁻¹⟩
theorem inst_claimAllC_band (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d)) (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand) (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) : UNClaimAllC sz0 (UNModel.band sz0).toC 0
theorem inst_claimAll_band_k (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d)) (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand) (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) : UNClaimAll sz0 (UNModel.band sz0) 0
theorem inst_bUniv_band_k (rI : UNInfty1Row) (rU : UNUnivMainRow) (rC : UNClaimRowk (fun d => UNKind.band d)) (rE : UNEMCTE2Rowk (fun d => UNKind.band d)) (rJ : UNJakUywRowk (fun d => UNKind.band d) UNLocAvgBand) (rO : UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand) (rD : UNDensBandRow) (rT : UNTrLocalBandRow) (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) : Tendsto (fun n => (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) - (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0)
theorem inst_coreC_band (hcore : UNCoreC) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAllC) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2)) (hTi : UNTrLocalInit sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 2)) (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) (hC : UNClaimAllC sz0 (UNModel.band sz0).toC 0) : UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ)
theorem inst_OUQUEk_zero_band (hQ : UNQueBand) : ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 → ∀ a : Zd 3 (sz0.L n), ouP (UNModel.band sz0) n {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) ((1 / 10) / 3) ((1 / 10) / 6) E a (ouMatC (UNModel.band sz0).toC n 0 ω)} ≤ queBound (sz0.W n) (1 / 10) ((1 / 10) / 3) ((1 / 10) / 6) (1 / 2)
theorem inst_ouMatC_ne_ouMat (t : ℝ) (ht : 0 < t) : ∃ M : UNModelC sz0, ∀ ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0), ∃ i j : Idx 3 (sz0.L 0) (sz0.W 0), ouMatC M 0 t ω i j ≠ ouMat M.toUNModel 0 t ω i j
```
### Script diffs (`diffs2.py`; whitespace-normalised declaration text, docstrings dropped; EMPTY = identical)
Substitutions applied to the source text, in order: `UNModel sz`->`UNModelC sz` (S1); `ouMat[_isHermitian|_zero|_eq_ouInit_add]`->`ouMatC…` (S2); `ouP (K.M sz)|((K d).M sz)|M n`->`ouP ….toUNModel n` (S3); `UNNormBound|UNTrLocal|UNUnivDilAt sz M`->`… sz M.toUNModel`, `UNApriori sz M E`->`UNApriori sz M.toUNModel E` (S4); `UNClaimAll`->`UNClaimAllC`, `UNGreenCorrAll`->`UNGreenCorrAllC` (S5; merged `UNClaim417|UNGreenCorr|UNInfty1|UNUnivMain` renamed `…C`); `UNModel.band sz`->`(UNModel.band sz).toC`, `M := UNModel.band`->`M := fun sz => (UNModel.band sz).toC` (S6). For merged `UNStep1Good`: also `UNTrLocal sz M.toUNModel m E δ`->`UNTrLocalInit sz M m E δ`, `vOU`->`vOUC`; merged `UNCore`: also the added hypothesis `UNTrLocalInit sz M m E δ →`.
```
$ python3 scratchpad/T2187/diffs2.py
check file section 2 vs PinsK, verbatim with docstrings: EMPTY 19 [UNModelC ouMatC ouInit UNClaim417C UNClaimAllC UNTrLocalInit UNKind UNOUQUEk UNOUDiagk UNEMCTE2k UNJakk UNUywk UNQuek UNLocAvgk UNOUClaimsk UNOURowk UNEMCTE2Rowk UNJakUywRowk UNClaimRowk]
check-file Props T2187_* appear as the statements of examples: EMPTY 3 [T2187_ouMatC_eq_ouMat_add T2187_ouMatC_mean_zero T2187_un_claimAll_of_rowsk]
probe a543154 under S1-S6: EMPTY 24 [UNKind UNKind.band UNOUQUEk UNOUDiagk UNEMCTE2k UNJakk UNUywk UNQuek UNLocAvgk UNOUClaimsk UNOURowk UNEMCTE2Rowk UNJakUywRowk UNClaimRowk un_claimAll_of_rowsk ouInit ouInit_isHermitian vOUC UNTrLocalInit UNStep1GoodC UNCoreC ouP_cylinder UNOUQUEk_zero_of_UNQuek inWindow_nonempty]
probe ouMat* renamed: EMPTY 4 [ouMat->ouMatC ouMat_isHermitian->ouMatC_isHermitian ouMat_zero->ouMatC_zero ouMat_eq_ouInit_add->ouMatC_eq_ouInit_add]
merged Pins.lean under S1-S5: EMPTY 6 [UNClaim417->UNClaim417C UNClaimAll->UNClaimAllC UNGreenCorr->UNGreenCorrC UNGreenCorrAll->UNGreenCorrAllC UNInfty1->UNInfty1C UNUnivMain->UNUnivMainC]
merged Pins.lean under S1-S5: EMPTY 2 [UNStep1Good->UNStep1GoodC UNCore->UNCoreC]
```
### Name-clash grep (`clash.py`: `grep -rnw --include=*.lean <base name> RBM3D/ RBM3D.lean` in the main worktree, `Probe/` excluded; every public base name of the new file)
```
68 public base names grepped: 1 with hits
band -> only prose in docstrings of Green/Pins.lean:209, Green/FlucVanish.lean:25, Green/LDE.lean:26 ("random band matrix"); the new name is the qualified `UNKind.band`; `UNModel.band` is a different declaration
```
(0 hits for the other 67 names: `UNModelC … un_claimAll_of_rowsk_band`, `toC`, `toAll`, `ouMatC*`, `ouInit*`, `ouP_cylinder`, `vOUC`, `inWindow_nonempty`, `inst_*`, `unPinsK_*`.)
### Registry (DECISIONS §16, §20): lines added to `RBM3D/Test/Axioms.lean`
17 `owedProps` lines, each `-- bulk universality pin, model-generic (T2187, UN-01b: owed)`: `UNClaim417C UNGreenCorrC UNGreenCorrAllC UNTrLocalInit UNStep1GoodC UNCoreC UNOUQUEk UNOUDiagk UNEMCTE2k UNJakk UNUywk UNQuek UNLocAvgk UNOURowk UNEMCTE2Rowk UNJakUywRowk UNClaimRowk` (as the ticket lists), plus 1 `structuralProps` line `RBM.Univ.UNKind.bulk` (flagged by the pre-check, see narrative).
```
$ (temporary uncommitted scratch file) import RBM3D / import RBM3D.Universality.PinsK / #assert_rbm_axioms ; lake env lean precheck.lean > precheck.out 2>&1 ; echo "exit=$?"
exit=0
axiom audit: 5445 theorems, 1945 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
premises found by scanning: 109 (borrowed 1, owed 85, structural 23).
registry: 2 borrowed + 129 owed + 58 structural; 80 registered premise(s) carry nothing yet: [...]
  RBM.Univ.UNClaim417C: 1  UNGreenCorrC: 1  UNGreenCorrAllC: 1  UNTrLocalInit: 1  UNStep1GoodC: 0  UNCoreC: 1  UNOUQUEk: 1  UNOUDiagk: 1  UNEMCTE2k: 1  UNJakk: 1  UNUywk: 1  UNQuek: 2  UNLocAvgk: 1  UNOURowk: 6  UNEMCTE2Rowk: 6  UNJakUywRowk: 6  UNClaimRowk: 6  (theorems resting on each)
```
The first pre-check run, before the `UNKind.bulk` line, ended: `error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`: [RBM.Univ.UNKind.bulk]`.
Ports from RBM1D/RBM2D: none (the sources are the T2173 probe `a543154:RBM3D/Probe/T2173Pins.lean` and the merged `RBM3D/Universality/Pins.lean`); no RBM1D/RBM2D diff-stat applies.
### Narrative
1. Design as the ticket: `UNModelC sz extends UNModel sz` (fields `mean`, `mean_herm`); the mean determines `ouMatC` and `ouInit`; flow and initial matrix are not fields of `UNKind`. No merged signature or file was touched (`Pins.lean`, `OU.lean`, `EigenMeasurable.lean`, `GUEInvariance.lean`, `Step1Cond.lean` are not in the diff).
2. The pinned text (check-file section 2) was copied into the file by script from the check file, so the first diff is empty by construction and is kept as the check; the three `T2187_*` Props of the check file are compiled as `example`s whose statements are the check-file bodies.
3. Flow identities: `ouMatC_eq_ouMat_add` (`ext`; `simp only`; `push_cast`; `ring`), `ouMatC_toC_apply`, `ouMatC_toC` (function equality), `ouInit_toC`. The eigenvalue pins (`UNGreenCorrC_toC`, `UNInfty1C_toC`, `UNUnivMainC_toC`) rewrite the Hermitian-proof-dependent `eigenvalues` through the private `unPinsK_eigenvalues_congr` (`subst h; rfl`) and `unPinsK_eig_toC`; `UNGreenCorrAllC.toAll` goes through `toC`.
4. The five Claim band bridges are proved by `unfold; rw [unPinsK_band_M, ouMatC_toC]; exact Iff.rfl` (no `simp`, so the module creates no `L1t/L2t/scirc.congr_simp` auxiliary constants; the constant list above has only the structure-generated `UNModelC.mk.congr_simp`). `UNQuek_band`, `UNLocAvgk_band` are `Iff.rfl`; `UNOUClaimsk_band`, `UNOURowk_band` use the claim bridges; `UNEMCTE2Rowk_band`, `UNJakUywRowk_band`, `UNClaimRowk_band` use `unfold` and `simp only` with `unPinsK_band_bulk` and `Filter.eventually_const` (the last also `UNClaimAllC_toC`).
5. `un_claimAll_of_rowsk` carries the probe proof verbatim (diff EMPTY); `un_claimAll_of_rowsk_band` applies it at the band kind with `Filter.Eventually.of_forall` and `UNClaimAllC_toC`.
6. Instances (namespace `RBM.Univ.UNKInst`, all compiled): `inst_claimAllC_band`, `inst_claimAll_band_k`, `inst_bUniv_band_k`, `inst_coreC_band`, `inst_OUQUEk_zero_band`, `inWindow_nonempty` (probe `:3454`, diff EMPTY), `inst_ouMatC_ne_ouMat`. Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`, `E = E' = 0`, `δ = 1/2`, `k = 1`, `bump`. Discharged in the instances: `Admissible` (`UNInst.sz0_adm`), `3 ≤ 3`, `0 < κ`, `|0| ≤ 2 - 1/10`, `UNDens` at `msc` (`un_dens_msc_zero`), `|0| < 2`, `1 ≤ 1`, `IsTestFun bump`. Kept as hypotheses (other gates' pins): the rows, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNL32` (borrowed), `UNGUELocal`, `UNGreenCorrAll(C)`, `UNTrLocal`, `UNTrLocalInit`, the norm bound, `UNCoreC`, `UNClaimAllC` (in `inst_coreC_band`).
7. `inst_ouMatC_ne_ouMat`: for every `t > 0` there is a `UNModelC sz0` (private `unPinsK_baC`: the law and matrix of `UNModel.ba sz0` with mean `lam • PsiI`, not the BA kind) for which `ouMatC` and `ouMat` differ at `n = 0` in the entry between the block `0` and the block `e₁`, offset `0`. Route: `Ψ_{ij} = 1` there (`unPinsK_psiI_entry`: `decide` on `blk`/`ofs`/`Adj`, then `simpa`), `lam 0 = 1/64`, and `ouMatC_eq_ouMat_add` gives the difference `(1 - e^{-t/2})/64 ≠ 0`.
8. Not targets (as the ticket says): band bridges for `vOUC`/`UNStep1GoodC`/`UNCoreC`; rows decomposing `UNCoreC`; the generator identity and `drift_entry`; all BA-specific items (`UNKind.ba`, `UNQueBA`, …). Model-level merged pins are reused at `M.toUNModel` (S4); no copy of `UNApriori`.
9. Registry: the pre-check flagged `RBM.Univ.UNKind.bulk` (the Prop-valued field `bulk : ∀ sz, ℝ → ℝ → ℕ → Prop` is assumed by the generic pins). The ticket says "unsure: owed"; I registered it as **structural**, because §20 classes a `Prop` that describes a condition on data (here the energy set of the model class: `|E| ≤ 2 - κ` for the band kind) as structural, and it is not a result anyone proves. If the dispatcher prefers owed, it is a one-line move between the two lists. `UNModelC`, `UNKind` themselves were not flagged (data).
10. The full `lake build` of the worktree does not import `PinsK` (the hub adds the root import at merge); the registry pre-check above is the check that includes the new module (5445 theorems = 5397 + 48).
## (c) Verified Mathlib names (scratch `names.lean`, `env.contains`, and the successful build)
Present: `Filter.eventually_const`, `Filter.Eventually.of_forall`, `Matrix.isHermitian_zero`, `Matrix.IsHermitian.eigenvalues`, `Matrix.IsHermitian.add/sub/smul`, `IsSelfAdjoint.all`, `Real.exp_lt_one_iff`, `Complex.real_smul`, `Complex.ofReal_eq_zero`, `Complex.ofReal_mul`, `Complex.conj_ofReal`, `Matrix.conjTranspose_smul`, `Matrix.add_apply/smul_apply/sub_apply`, `Matrix.kroneckerMap_apply`, `Matrix.submatrix_apply`, `MeasureTheory.Measure.prod_prod`, `Real.rpow_neg_one`, `Real.rpow_le_rpow_of_exponent_le`; `measure_univ` resolves as the `IsProbabilityMeasure` field (`@measure_univ : ∀ {α} {m0} {μ} [self : IsProbabilityMeasure μ], μ Set.univ = 1`).
Verified absent (`env.contains` false): `Real.exp_lt_one`, `self_eq_add_right`, `Filter.eventually_of_forall`, `MeasureTheory.measure_univ`.
## (d) Open issues and paper-delta candidates
- T2187a (Lean structure only): the probe amends `UNModel` (field `mean`) and `ouMat` in place; here `UNModelC` extends `UNModel`, `ouMatC` is the centred flow, `UNKind.M : ∀ sz, UNModelC sz`, and the claim-level pins `UNClaim417C … UNUnivMainC` are copies over `UNModelC`. After S1-S6 every declaration compared above is identical to the probe or the merged text; the flow identities, the bridges and the instances are new. The mathematical amendment (centred flow) is T2173c.
- T2187b (registry): `RBM.Univ.UNKind.bulk` registered structural (narrative 9); dispatcher to confirm.
- Observation: `UNStep1GoodC` (like merged `UNStep1Good`) is carried by 0 theorems in the pre-check count (`UNStep1GoodC: 0`).
- No open issue blocks the merge. The hub still has to add `import RBM3D.Universality.PinsK` after the last import line of `RBM3D.lean`.
