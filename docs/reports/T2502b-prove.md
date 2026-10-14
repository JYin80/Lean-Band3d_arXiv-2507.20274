Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 07:26:52 UTC 2026

Row b only (targets 10-13: `ExpHierGen` → `ExpDuhamelGen`; main `bd5531ea`, row a merged). Mathematics: at one size index `n`, `f_u = 𝔼 𝓛^{(2)}_u - 𝒦^{(2)}_u` solves `∂_u f = Θ^{(2)}_{u,σ} f + D_u` on `(0,1)` (continuous on `[0,1)`), and then `f_t = 𝒰_{s,t} f_s + ∫_s^t 𝒰_{u,t} D_u du`, where `Θ^{(2)}` has the two slots `(σ_0,σ_1)`, `(σ_1,σ_0)`, `X = M^{(σσ')} S`, `θ_t = X(1-tX)⁻¹`, `𝒰_{s,t} = (1-sX)(1-tX)⁻¹`. Hypotheses of the targets (ticket `T2502_ExpHierAtOf`, `T2502_ExpDuhamelZAtOf`): `CltRepg` (`μ = seqP(sz.withLam g')`, `H₀` Hermitian), `LoopForm` (`0 < Im m`, `η = (1-u) Im m`), `S n = SB d L g'`, `KLoop`, `KTwo`, `KLink` at `n`, `Step2Gen_USemigroup`.

### (i) Exponent table
| # | quantity | value | constraint | slack (instance below) |
|---|---|---|---|---|
| 1 | lattice `d`, `L` | `d = 3`, `L = 4` | `3 ≤ L` (`SB` row sums 1, `norm_SB`; `sz.three_le_L`). Row b does not use `3 ≤ d` (ExpDuhamel band header: "not used") | `L - 3 = 1` |
| 2 | walk coupling `g'` in `S n = SB d L g'` | `1/64` (sz0 n=0 `lam`), `1` (szB), `0` (BA, `S = 1`) | any real `g'`: row sums of `SB` are 1 | row-sum error ≤ 1.1e-16 at all three |
| 3 | one-loop value `m`, `ztOf m E u = E + (1-u) m` | `E = 1/2`, `m = mE(E) = -0.25 + 0.968246 i` | `0 < Im m` (`LoopForm`); `Im (ztOf) = (1-u) Im m > 0` for `u < 1` | `Im m = 0.968246`; `|m| = 1` |
| 3a | Good-class bound on `[0,b]`, loop length `k = 2` | `B(b) = N ((1-b) Im m)^{-1} W^{-d})^2`, `N = (WL)^d = 2097152`, `W = 32` | finite for every `b < 1` (`η_b = (1-b) Im m > 0`) | `B(1/2) = 8.3e-3`, `B(15/16) = 0.533`, `B(0.99) = 20.8` |
| 4 | time window | `0 ≤ s ≤ t < 1`; `Step2Gen_USemigroup` is for `v, w ∈ [0,1)`, `u` arbitrary | `1 - vX` must be a unit (`uKer v v = 1`) | tested `v, w ≤ 0.99`; residuals ≤ 2.7e-13 |
| 5 | contraction `ρ(u X)`, band `X = |m|² S` | `= u` (`|m| = 1`) | `< 1` for `u < 1` (band only; BA: `USemigroup` is the premise 13, no contraction assumed) | `1 - u = 0.01` at `u = 0.99` (printed `0.9900`) |
| 6 | hierarchy order `k = 2` | `Σ_{l ∈ Icc 3 2} = ∅` | only `ELKLK`, `EGt`, `Θ` terms remain | n/a (exact) |
| 7 | `𝒦^{(2)}_u = W^{-d} μ Θ_{uμ}(S)`, `μ = |m|²`; `KLoop`: `∂_u K = W^d K S K` | `W^d = 32³` | holds for `u < 1` (`1 - uμS` unit) | rel. error 1.9e-10 (`g' = 1/64`), 2.2e-9 (`g' = 1`), 3.3e-11 (`g' = 0`), `u = 0.6` |
| 8 | W2: `∂_u 𝔼 𝓛(H₀ + √u X, z_u) = 𝔼[½ Σ_c g_c ∂²_c 𝓛 + ∂_v 𝓛(·, z_v)|_{v=u}]` | independent of `H₀` (a deterministic Hermitian shift does not enter the second line derivatives) | needs `η > 0` along `z_u`; `x = √u` (`d/du = (1/(2x)) d/dx`, `d/dx 𝔼 f(M + xX) = x Σ_c g_c 𝔼 ∂²_c f`) | 2×2 toy, `H₀ ≠ 0`: `|diff| = 9.2e-6` (`H₀ = 0`: `5.1e-6`; Gauss-Hermite error) |
| 9 | row b cut: bottom-up central (ticket) `ExpHierGen` 990 + `ExpDuhamelGen` 485 = **1,475**; W2 at `H₀`: 300-450 instead of 300 | row b ∈ [1,475; 1,625] | split threshold 1,950; stop line 2,050; one file ≤ 2,000 | ≥ 325 below 1,950; ≥ 425 below 2,050; the split rule does not trigger |

### (ii) One concrete nondegenerate instance
`d = 3`, `L = 4`, `E = 1/2`, `m = mE(1/2)`, sz0 `n = 0` (`W = 32`, `lam = 1/64`, `N = 2097152`, same data as row a (a)(ii)); `g' ∈ {1/64, 1, 0}`; `s = 0.2`, `t = 0.8`; charges `σ = (+,-)`; carrier A = band (`M = m I`, `X = |m|² S`), carrier B = BA-shaped (`g' = 0`, `S = 1`, non-scalar `M^{(σσ')}` with `ρ(X) = 0.95`); tensors on `Z_4^3 × Z_4^3` (64×64), `f_u = e^{-u} c_1 + u² c_2` random complex, `D_u := f'_u - Θ f_u`; mollifier `ϑ_u(a_0,a_1) = e^{-(1+u)|a_1-a_0|}/Σ_{a_1}`. Checked: `Im m > 0`; `Mss(+-) = |m|² I` on the fine lattice `W = 2, 3`; `S` doubly stochastic; `USemigroup` (all four charge pairs, `u ∈ {-0.3, 0, 0.4, 0.7}`, `v, w ∈ {0, 0.5, 0.9, 0.99}`); `KLoop` ODE; the plain, zero-mode (`A = ∅, {0}, {0,1}`; `Q` applied outside `𝒰`, the pinned form) and `𝒬`-Duhamel identities by 40-point Gauss-Legendre; the `H₀ ≠ 0` heat identity of W2 (toy). No hypothesis is external: `KLoop`, `KTwo`, `KLink`, `USemigroup` are per-index family premises (table rows 11-13 of the ticket), so no limit computation is needed; the eventual form is `STExpDuhamelZgL/QgL`'s `∀ᶠ n` and is not a row-b premise.

Command: `cd / && python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2502b/inst.py` (≈ 10 s). Output:
```
d=3 L=4 E=0.5: m=-0.250000+0.968246j Im m=0.968246 |m|=1.000000000000 (hyp: Im m>0, |E|<2)
W=2: max|Mss(+-) - |m|^2 I| = 0.00e+00  (Mss = m_s m_s' I, as used below)
W=3: max|Mss(+-) - |m|^2 I| = 6.66e-16  (Mss = m_s m_s' I, as used below)
g'=0.015625: row-sum err 1.1e-16, symmetric err 0.0e+00, ||S||_inf=1; USemigroup residuals: uKer(v,v)=1: 2.0e-15; semigroup law: 2.7e-13; KLoop (K'=W^d KSK, u=.6) rel.err 1.9e-10; max spectral radius of u X at u=0.99: 0.9900
g'=1.000000: row-sum err 1.1e-16, symmetric err 0.0e+00, ||S||_inf=1; USemigroup residuals: uKer(v,v)=1: 2.4e-15; semigroup law: 8.1e-14; KLoop (K'=W^d KSK, u=.6) rel.err 2.2e-09; max spectral radius of u X at u=0.99: 0.9900
g'=0.000000: row-sum err 0.0e+00, symmetric err 0.0e+00, ||S||_inf=1; USemigroup residuals: uKer(v,v)=1: 2.2e-16; semigroup law: 2.8e-14; KLoop (K'=W^d KSK, u=.6) rel.err 3.3e-11; max spectral radius of u X at u=0.99: 0.9900
Duhamel (Q outside U, pinned form) band g'=1/64 (X=|m|^2 S), s=0.2, t=0.8, rel. residual  A=empty: 2.2e-14; A={0}: 2.6e-14; A={0,1}: 2.7e-14
   commutation Q U_(s,t) = U_(s,t) Q, rel. defect  A=empty: 0.0e+00; A={0}: 1.5e-15; A={0,1}: 2.0e-15
Duhamel (Q outside U, pinned form) band g'=1 (X=|m|^2 S), s=0.2, t=0.8, rel. residual  A=empty: 3.2e-15; A={0}: 4.3e-15; A={0,1}: 2.8e-15
   commutation Q U_(s,t) = U_(s,t) Q, rel. defect  A=empty: 0.0e+00; A={0}: 1.2e-15; A={0,1}: 1.3e-15
Duhamel (Q outside U, pinned form) BA-shaped (g'=0, S=1, non-scalar Mss, rho(X01)=rho(X10)=0.95), s=0.2, t=0.8, rel. residual  A=empty: 2.0e-15; A={0}: 2.0e-15; A={0,1}: 2.6e-15
   commutation Q U_(s,t) = U_(s,t) Q, rel. defect  A=empty: 0.0e+00; A={0}: 1.3e-01; A={0,1}: 1.4e-01
heat-flow toy H0=[[.3,.2],[.2,-.1]]: d/du E F = 1.53621983+0.00000000j, E[generator] = 1.53622905-0.00000000j, |diff| = 9.2e-06
heat-flow toy H0=0: d/du E F = 1.19552593-0.00000000j, E[generator] = 1.19553099+0.00000000j, |diff| = 5.1e-06
Q-Duhamel (pinned Q-form, theta_u=normalised exp(-(1+u)|x|)) band g'=1: rel. residual 6.4e-12
Q-Duhamel (pinned Q-form, theta_u=normalised exp(-(1+u)|x|)) BA-shaped (S=1, non-scalar Mss): rel. residual 4.8e-12
Good-class bound b=0.5: eta_b=(1-b) Im m=0.4841, B(b)=8.333e-03 (finite for every b<1)
Good-class bound b=0.9375: eta_b=(1-b) Im m=0.0605, B(b)=5.333e-01 (finite for every b<1)
Good-class bound b=0.99: eta_b=(1-b) Im m=0.0097, B(b)=2.083e+01 (finite for every b<1)
```
Size evidence for table row 9 (code lines = non-blank, non-comment; command `python3 -I …/T2502b/count.py`):
```
  610 code lines  Induction/ExpHier.lean:1-778  band ExpHier non-instance
  453 code lines  Induction/ExpDuhamel.lean:1-584  band ExpDuhamel non-instance
  210 code lines  Gauss/LoopGenerator.lean:54-312  LoopGenerator 54-312 (ticket W2 budget range)
  698 code lines  Gauss/LoopFlowStein.lean:45-888  LoopFlowStein 1-4 (Stein, envelope, d/du E)
  660 code lines  Gauss/LoopCoordinate.lean:34-817  LoopCoordinate 1-4 (coordinate 1st/2nd derivs, bounds)
  173 code lines  Gauss/FlowCalculus.lean:363-580  FlowCalculus 3 (derivs along spectral flow)
```

### Verdicts (targets 10-13)
- **10 PASS, 11 PASS, 12 PASS.** Hypotheses hold jointly at the instance; the identity `∂_u 𝔼 𝓛 = 𝔼[genMat]` does not depend on `H₀` (row 8, toy with `H₀ ≠ 0`). W2 does not need a class beyond `CltRepg`. The merged `Gauss/LoopGenerator:312`, `LoopFlowStein`, `LoopCoordinate` (the four-file Stein stack, 1,741 code lines above the band) are fixed at `HflowBlock`, `zt E`, `|E| < 2` (grep: `H₀` 0 hits in all four Gauss files), so copying that stack at `H₀` would pass the 2,000-line stop. It is not needed: `Path/OneStep.lean:1827` (`OneStep_hasDerivAt_F`, private, `open private`) is `d/dx 𝔼 loopL(blockMat(M + xX)) z I = x Σ_c g_c 𝔼 J2(…)` for **every Hermitian `M`** and `z.im ≠ 0` (Stein + domination), `OneStep_hasDerivAt_line0/1` (`:1305, :1314`) give `J1/J2` as the first/second line derivative, and `ExpHier` already imports `Path.DriftAlgebra`, which imports `Path.OneStep`. With `x = √u` the u⁻¹ factors of the band `expHier_second_deriv` disappear. The remaining W2 work is the joint chain rule in `(x = √u, z_u)` (both partials continuous by dominated convergence); the pointwise step `genMatOf → ThetaN + ELKLK + EGt` is the merged `hierarchyNg_of` (`HierDriftGen:441`) at any Hermitian `M`, so the cut form of `LoopGenerator` is not used (target 10's `ExpHierGen_genMat_eq_cuts` reduces to the `J2`/line-derivative bridge).
- **13 PASS**, with one correction to the ticket text. The ticket says target 13 uses "`zeroModeSet` commutes with `Step2Gen_UN`". That commutation is **false** for a general carrier (rows `commutation`: defect 0.13-0.14 at carrier B; holds only where `X` commutes with the all-ones matrix, as at the band) and is **not needed**: in the pinned texts `T2502_ExpDuhamelZAtgL`, `STExpDuhEqgL` the zero-mode operator is applied outside `𝒰` (`zeroModeSet A (Step2Gen_UN … f_s)`), so the identity follows from the plain Duhamel formula by linearity of `Q^{(A)}` (residual 2.7e-14 at A = {0,1}, also at carrier B 2.6e-15). The prover must not state or prove the commutation. Proof of the plain form (`(1-vX)Θ_v = 1` from `USemigroup` at `v = w`; `𝒰_{v,t} θ_v = θ_t`; `uKer` affine in its first time with `∂_s = -XΘ_t`; FTC with `f` continuous on `[s,t]`, ODE on `(s,t)`); the `𝒬`-form is algebraic from it (`g = 𝒬_u f`: `g' = Θ g + 𝒬D + (𝒬Θ f - Θ𝒬 f) - 𝒫f · ∂_uϑ`, residual 6.4e-12, carrier B 4.8e-12), with `∂_uϑ` bounded and measurable on `(0,1)` (interval-integrable source, band `ExpDuhamel` header, change 2).
- **Rows, layout, cut unchanged** (row b ∈ [1,475; 1,625] < 1,950): no `rows/layout changed` line; no 1a-audit needed. Stop lines of the ticket stay (row b 2,050; file 2,000). Reserve `ExpHierGen2` only if W2 passes 450.
- Paper-delta candidates: none from the mathematics (`6:12-21`, "same as [YY_25]", covers `H₀ ≠ 0`); the ticket-text correction above is a dispatcher fix, not a paper delta.

## (b) Script output (stage 1b) — Wed Oct 14 08:15:07 UTC 2026
Worktree `RBM3D-wt/T2502b`, branch `t/T2502b` (commits, script): 
```
94db77fa T2502b: ExpDuhamelGen consumer-chain example, header linter option
13be941a T2502b: ExpHierGen instance at a nonzero H0 (W2 core)
b5fa1da8 T2502b: RBM3D.lean import lines for ExpHierGen, ExpDuhamelGen
d4635d55 T2502b: ExpDuhamelGen (target 13: plain, zero-mode and Q Duhamel over the carrier) and ExpHierGen rename
241c6805 T2502b: ExpHierGen section (targets 10-12: expected hierarchy at n = 2 over the carrier, H0 + seqHflow)
```
### Build, sizes, axioms
```
$ lake build RBM3D.Chain.ExpHierGen RBM3D.Chain.ExpDuhamelGen 2>&1 | tail -1
Build completed successfully (3879 jobs).
$ lake build 2>&1 | tail -2        # whole library with the two import lines; `#assert_rbm_axioms` runs in RBM3D.lean
Build completed successfully (4387 jobs).
exit 0
$ wc -l RBM3D/Chain/ExpHierGen.lean RBM3D/Chain/ExpDuhamelGen.lean     # bottom-up: 990 + 485 = 1,475; stop 2,050
     885 RBM3D/Chain/ExpHierGen.lean
     582 RBM3D/Chain/ExpDuhamelGen.lean
    1467 total
$ lake env lean ax.lean   # `#print axioms` of the 23 public theorems; aggregated: grep -o "depends on axioms: .*" | sort | uniq -c
  23 depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|^axiom|native_decide" <both files> | wc -l
0
```
### Pins (statement diff by compilation, CLAUDE.md §6)
`docs/tickets/checks/T2502-check.lean` on this branch, and a scratch file with the check's Part 2 plus the examples below (`pins.lean`, uncommitted):
```
$ lake env lean docs/tickets/checks/T2502-check.lean > check.out; echo "exit $?"
exit 0; error lines: 0
$ lake env lean pins.lean; echo "exit $?"
exit 0; error lines: 0
186-    T2502_ExpHierAtOf Cm μ H₀ g' E n := stExpHiergL_at Cm μ H₀ g' E n
189-    T2502_ExpDuhamelZAtOf C μ n := stExpDuhamelZgL_at C μ n
193-    T2502_ExpHierAtgL C μ n = STExpHierAtgL C μ n := rfl
195-    T2502_ExpDuhamelZAtgL C μ n = STExpDuhamelZAtgL C μ n := rfl
197-    T2502_ExpDuhamelQAtgL C μ n = STExpDuhamelQAtgL C μ n := rfl
200-    T2502_ExpDuhamelZgL d law Flow mk = STExpDuhamelZgL d law Flow mk := rfl
```
### Target statements (extracted from the files by `extract.py`; section variables `{d} {sz} (Cm : Step2Mat sz) (n : ℕ)`, resp. `(C : FlowFM sz) (μ) (n)`)
```
-- ExpHierGen.lean:397
theorem ExpHierGen_Kloop_hasDerivAt (hK : HierDriftGen_KLoop Cm n) (hLink : HierDriftGen_KLink Cm n) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v : ℝ => Cm.K n v σ a)
      (treeEqRhsS d (sz.L n) (sz.W n) (Cm.S n) (Cm.KI n u) (KLloopOf d (sz.L n) σ a)) u
-- ExpHierGen.lean:409
theorem ExpHierGen_continuousOn_K (hK : HierDriftGen_KLoop Cm n) (hLink : HierDriftGen_KLink Cm n)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun v : ℝ => Cm.K n v σ a) (Set.Ico 0 1)
-- ExpHierGen.lean:500
theorem ExpHierGen_hierarchy_two (E g : ℕ → ℝ) (hL : StepDecompGen_LoopForm Cm E)
    (hS : Cm.S n = SB d (sz.L n) (g n)) (hK : HierDriftGen_KLoop Cm n) (hT : HierDriftGen_KTwo Cm n)
    (hLink : HierDriftGen_KLink Cm n) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hM : M.IsHermitian)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    RBM.Ind.genMatOf d (sz.L n) (sz.W n) (g n) (Cm.m n) (E n) u M (KLloopOf d (sz.L n) σ a) -
        deriv (fun v : ℝ => Cm.K n v σ a) u =
      Step2Gen_ThetaN Cm.toFlowFM n σ u (STLKMg Cm n u M σ) a + STELKLKMg Cm n u M σ a + STEGtMg Cm n u M σ a
-- ExpHierGen.lean:720
theorem stExpHiergL_at {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ) (n : ℕ) :
    CltRepg Cm.toFlowFM μ H₀ g' E → StepDecompGen_LoopForm Cm E → Cm.S n = SB d (sz.L n) (g' n) →
      HierDriftGen_KLoop Cm n → HierDriftGen_KTwo Cm n → HierDriftGen_KLink Cm n →
        STExpHierAtgL Cm.toFlowFM μ n
-- ExpHierGen.lean:797
theorem stExpHiergL_ev {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (hmk : ∀ (sz : Sizes d) (z : ℕ → ℂ), (mkM sz z).toFlowFM = mk sz z)
    (hrep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ StepDecompGen_LoopForm (mkM sz z) E ∧
          ∀ n, (mkM sz z).S n = SB d (sz.L n) (g' n))
    (hcls : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, HierDriftGen_KLoop (mkM sz z) n ∧ HierDriftGen_KTwo (mkM sz z) n ∧
        HierDriftGen_KLink (mkM sz z) n) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, STExpHierAtgL (mk sz z) (law sz) n
-- ExpHierGen.lean:818
theorem stExpHier_of_gL (d : ℕ) : STExpHier d
-- ExpDuhamelGen.lean:279
theorem stExpDuhamelZgL_at (h : Step2Gen_USemigroup C n) (hH : STExpHierAtgL C μ n) : STExpDuhamelZAtgL C μ n
-- ExpDuhamelGen.lean:361
theorem stExpDuhamelQgL_at (h : Step2Gen_USemigroup C n) (hH : STExpHierAtgL C μ n) : STExpDuhamelQAtgL C μ n
-- ExpDuhamelGen.lean:471
theorem stExpDuhamelZ_of_gL (d : ℕ) : STExpDuhamelZ d
-- ExpDuhamelGen.lean:484
theorem stExpDuhamelQ_of_gL (d : ℕ) : STExpDuhamelQ d
-- ExpDuhamelGen.lean:434 stExpDuhamelZgL_ev / :452 stExpDuhamelQgL_ev: the premises of stExpHiergL_ev (law Flow mk mkM hmk hrep hcls) and
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, Step2Gen_USemigroup (mk sz z) n) :
    STExpDuhamelZgL d law Flow mk
-- (the Q form is the same with conclusion `STExpDuhamelQgL d law Flow mk`)
```
### Compiled nonempty instances (script: declaration heads; bodies in the files)
```
-- ExpHierGen.lean:844
theorem stExpHiergL_at_inst : STExpHierAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) 0
-- ExpHierGen.lean:857
theorem stExpHiergL_ev_inst : ∀ (sz : Sizes 3) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → True →
    ∀ᶠ n in atTop, STExpHierAtgL (bandFM sz (fun _ => 1 / 2)) (Sizes.seqP sz) n
-- ExpDuhamelGen.lean:507
theorem stExpDuhamelZgL_at_inst : STExpDuhamelZAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) 0
-- ExpDuhamelGen.lean:510
theorem stExpDuhamelQgL_at_inst : STExpDuhamelQAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) 0
-- ExpDuhamelGen.lean:547
theorem stExpDuhamelZgL_ev_inst : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun _ _ _ _ _ _ => True)
    (fun sz _ => bandFM sz (fun _ => 1 / 2))
-- ExpDuhamelGen.lean:558
theorem stExpDuhamelQgL_ev_inst : STExpDuhamelQgL 3 (fun sz => Sizes.seqP sz) (fun _ _ _ _ _ _ => True)
    (fun sz _ => bandFM sz (fun _ => 1 / 2))
ExpHierGen.lean:851:example : ∃ f' : ℂ, HasDerivAt (fun v : ℝ =>
ExpHierGen.lean:867:example : ∃ n : ℕ, STExpHierAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) n :=
ExpHierGen.lean:871:example : ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u ![true, false] ![0, Pi.single 0 1]) (Set.Ico 0 1) :=
ExpHierGen.lean:877:example : ∃ f' : ℂ, HasDerivAt (fun v : ℝ => ∫ ω : Ω 3 4 32,
ExpDuhamelGen.lean:514:example : zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
ExpDuhamelGen.lean:529:example : ∃ (Cq c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) Cq c ϑ ∧
ExpDuhamelGen.lean:570:example : STExpDuhEqgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) (fun _ => 1 / 4) (fun _ => 1 / 2) :=
ExpDuhamelGen.lean:574:example : ∃ n : ℕ, STExpDuhamelZAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) n :=
ExpDuhamelGen.lean:578:example : STExpDuhamelZ 3 ∧ STExpDuhamelQ 3 := ⟨stExpDuhamelZ_of_gL 3, stExpDuhamelQ_of_gL 3⟩
```
Data of the instances: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`), band carrier at `E = 1/2`, `H₀ = 0`, `g' = sz0.lam`, `[s,t] = [1/4, 1/2]`, `σ = (+,-)`, `a = (0, e₁)`, `A = {0,1}`; plus `ExpHierGen_hasDerivAt_integral` at `M₀ = 1` (≠ 0), `m = i`, `L = 4`, `W = 32`, `u = 1/2`.
### Hypothesis rules, layering, diff
```
$ python3 -I stmts.py <both files> | grep -v "hits=\[\]"      # C1/X1-C1 regex over the statements of every theorem/example
   5 x example  hits=['seqP']
   7 x private  hits=['Lloop']
   4 x private  hits=['PF d']
   2 x public   hits=['Lloop']
   6 x public   hits=['seqP']
$ grep -nE "withLam|\bgK\b" <both files> | cut -d: -f1,2   # all inside the proof of stExpHiergL_at (unpacking CltRepg) and its docstring
716 730 733 734 736 738 739 741 744 757 769 
$ grep -nE '^(noncomputable )?(def|abbrev|structure) ' <both files> | wc -l            # X1-C4: no new def
0
$ grep -c STGridRepNgL <both files> ; grep -nE "∀ \(sz : Sizes d\)" <both files> | cut -d: -f1,2   # TN-C4 ; U5S-C3
RBM3D/Chain/ExpHierGen.lean:0 RBM3D/Chain/ExpDuhamelGen.lean:0 
ExpHierGen.lean:798 ExpHierGen.lean:799 ExpHierGen.lean:800 ExpHierGen.lean:804 ExpHierGen.lean:807 ExpDuhamelGen.lean:435 ExpDuhamelGen.lean:436 ExpDuhamelGen.lean:437 ExpDuhamelGen.lean:441 ExpDuhamelGen.lean:444 ExpDuhamelGen.lean:453 ExpDuhamelGen.lean:454 ExpDuhamelGen.lean:455 ExpDuhamelGen.lean:459 ExpDuhamelGen.lean:462 
  -- every hit is the tuple binders (Flow, mk, mkM, hmk) or a guarded family premise: hrep (rows 9, 10), hcls (rows 11, 12), hU (row 13)
$ python3 -I closure.py RBM3D.Chain.ExpHierGen RBM3D.Chain.ExpDuhamelGen     # transitive imports; forbidden: BA.*, Chain.Step2Kern, QProxy/QDrift/QLevels/QBudget/QEnd, QtNonzero/QtXiRoundLift, Step3/Step4, Iterations*, Graph.BALWOut
modules in closure: 177
forbidden-pattern modules in closure: []
RBM3D.Chain.ExpHierGen direct imports: ['RBM3D.Chain.Step6KitGen', 'RBM3D.Induction.ExpHier', 'RBM3D.Chain.HierDriftGen', 'RBM3D.Chain.StepDecompGen', 'RBM3D.Chain.CltGen']
RBM3D.Chain.ExpDuhamelGen direct imports: ['RBM3D.Chain.ExpHierGen', 'RBM3D.Induction.ExpDuhamel', 'RBM3D.Chain.GridDuhamelGen']
$ grep -rln "Chain.ExpHierGen\|Chain.ExpDuhamelGen" RBM3D RBM3D.lean     # importers
RBM3D.lean RBM3D/Chain/ExpDuhamelGen.lean 
$ git diff main...t/T2502b --stat ; (band dirs and merged Chain/*: name-only)
 RBM3D.lean                     |   2 +
 RBM3D/Chain/ExpDuhamelGen.lean | 582 +++++++++++++++++++++++++++
 RBM3D/Chain/ExpHierGen.lean    | 885 +++++++++++++++++++++++++++++++++++++++++
 3 files changed, 1469 insertions(+)
0 band-dir files in the diff
RBM3D/Chain/ExpDuhamelGen.lean RBM3D/Chain/ExpHierGen.lean 
```
### Name clashes, premise scan, ports
```
$ for each new public theorem: git grep -n -w <name> bd5531ea -- RBM3D | wc -l      # main at the branch point; also t/T2502c, t/T2498b below
23 public theorems, total hits on main bd5531ea: 0
hits on sibling branches: t/T2502c: 0; t/T2498b: 0; t/T2498: 0
$ premise scan (`#assert_rbm_axioms` info line), before = main + no new import, after = this branch
before: axiom audit: 15170 theorems, 4696 definitions, 0 axioms in `RBM` (compiler-gen
before: premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14).
after : axiom audit: 15194 theorems, 4696 definitions, 0 axioms in `RBM` (compiler-gen
after : premises found by scanning: 144 (borrowed 1, owed 65, structural 58, refuted 6, superseded 14).
  -> no new unclassified premise, no `Test/Axioms.lean` edit (row b has no scan hit of its own).
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; diff --stat c9a24cf HEAD -- RBM2D/Evolution/MLExpHier.lean RBM2D/Evolution/MLExpDuhamel.lean
9e0f275
 RBM2D/Evolution/MLExpDuhamel.lean | 126 +++++++-------------------------------
 RBM2D/Evolution/MLExpHier.lean    |  95 +++++-----------------------
 2 files changed, 38 insertions(+), 183 deletions(-)
  (no text copied from RBM1D/RBM2D in this ticket: the files adapt the in-project band files `Induction/ExpHier`, `ExpDuhamel`, which cite MLExpHier/MLExpDuhamel; the ported pieces and their band lines are cited in the docstrings)
```
### Narrative (verdict PASS; every statement below is backed by the script output above or by the files)
- **Delivered:** targets 10-13 in `RBM3D/Chain/ExpHierGen.lean` (885 lines) and `RBM3D/Chain/ExpDuhamelGen.lean` (582 lines): 1,467 against the bottom-up 1,475 (stop 2,050); no stop
  rule fired; the diff has the two new files and the two `RBM3D.lean` import lines only (0 band-dir files).
- **Statements:** `stExpHiergL_at` is `T2502_ExpHierAtOf` and `stExpDuhamelZgL_at` is `T2502_ExpDuhamelZAtOf` (pins block, compiled); `T2502_ExpHierAtgL`, `T2502_ExpDuhamelZAtgL`,
  `T2502_ExpDuhamelQAtgL` are the merged `STExp*AtgL` of row a (`rfl`); `stExpDuhamelZgL_ev` is `T2502_ExpDuhamelZgL`.  Hypotheses are those of the bundles; no pinned signature changed.
- **W2 (target 10)**, `ExpHierGen.lean:58-378` (321 lines; budget 300-450), needs no class beyond `CltRepg` (used through `μ = seqP (sz.withLam g')`, `H₀ n` Hermitian and the loop
  clause; the `G` clause is unused).  The cut form of `Gauss/LoopGenerator` is not used.  Route: `open private` of `Path/OneStep`: `ExpHierGen_hasDerivAt_loopL` (resolvent chain rule
  with `Hf` and `ztOf m E v` moving together, `z' = -m`, from `OneStep_hasDerivAt_Gsig`/`_w0`), `ExpHierGen_hasDerivAt_F_pt` (`(2√u)⁻¹ J1(·,X) + J1(·,m_σ)`),
  `ExpHierGen_hasDerivAt_integral` (one `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `(u/2,(1+u)/2)`, then `OneStep_stein_coord` at `x = √u`, `M = H₀ n`; the factor `(2√u)⁻¹`
  cancels `√u`; result `∫ genMatOf`), `ExpHierGen_genMat_eq_cuts` (`genMatOf = ½ Σ_c gvar_c J2 + J1(·,m_σ)`).  Regularity: band `expHier_Good` (opened) with the new member
  `ExpHierGen_Good_loopL` and the sums `ExpHierGen_Good_STLKM/_STELKLKM/_STEGtM`.
- **Target 11:** `ExpHierGen_Kloop_hasDerivAt`, `ExpHierGen_continuousOn_K` (`K = KI` on `[0,1)` by `KLink`); `ExpHierGen_hierarchy_two` is `hierarchyNg_of` at one index (private
  `ExpHierGen_hierarchyNg_at`, same proof, premises at `n`) plus the `k = 2` reductions; it is stated for `0 < u < 1` where the band `expHier_hierarchy_two` has `0 ≤ u` (`deriv K` is
  `deriv KI` only at interior points).
- **Target 12:** `stExpHiergL_at` writes the carrier loops as the loops of `Mu u ω' = H₀ n + √u X_ω'` at `slice n ω` (`hLrep`, from `CltRepg` and `LoopForm`), transfers the three
  integrals to `PF d L W (g' n)` (band `expHier_integral_slice`, opened, at `sz.withLam g'`), and concludes by `ExpHierGen_continuousOn_STLM`, `_drift`, `ExpHierGen_hasDerivAt_fixed`.
  `stExpHier_of_gL` re-derives the band `STExpHier d` from it at `bandStep2Mat sz (fun _ => E)`, `H₀ = 0`, `g' = sz.lam`.
- **Target 13:** engine `ExpDuhamelGen_duhamel` (FTC); `Step2Gen_USemigroup` gives `uKer v w * thetaKer v = thetaKer w` by the semigroup law at `u = 0, 1`
  (`ExpDuhamelGen_uKer_mul_thetaKer`), and `uKer` is affine in its first time.  Zero mode: `Q^{(A)}` stays **outside** `𝒰`, as pinned; only `zeroModeSet_add/_sum/_smul` are used
  (`ExpDuhamelGen_zeroMode_expand/_integral`).  The commutation `Q^{(A)} 𝒰 = 𝒰 Q^{(A)}` of the ticket text is not used (preflight (a): false for a general carrier).  `𝒬` form: engine at
  `Y = 𝒬 f`, source `STExpQsrcg`; interval integrability needs `Θ_u` continuous on `[0,1)`: `1 - uX` is a unit by `uKer u u = 1` (`Ring.inverse_non_unit`), then
  `hasFDerivAt_ringInverse`.  Band re-derivations: `stExpDuhamelZ_of_gL`, `stExpDuhamelQ_of_gL`; `st6_duhEq_of_ping` (row a) accepts `stExpDuhamelZgL_ev` (example at
  `ExpDuhamelGen.lean:570`).
- **Family theorems** `stExpHiergL_ev`, `stExpDuhamelZgL_ev`, `stExpDuhamelQgL_ev` carry the family table inline: `hrep` = rows 9, 10 in one guarded `∃ (H₀ g' E)` (`E` is shared by
  `CltRepg` and `LoopForm`), `hcls` = rows 11, 12 as `∀ᶠ n` (BA `baHierDrift_classes`: `KLoop`, `KTwo` eventual, `KLink` every `n`), `hU` = row 13 as `∀ᶠ n`; `mk`, `mkM` linked by
  `hmk`.  No `∀ n` hierarchy or drift premise; the pinned `∃` constants (`𝔠d`, `A`, `Cs`, `κm`) do not occur in this row.
- **Instances:** at the band `sz0`, `n = 0`, `E = 1/2`, `H₀ = 0` every deterministic premise is discharged by merged band theorems; the `_ev` instances take `Flow = True`.  `H₀ ≠ 0` at
  carrier level is BA's (`baCltRepg_holds`, `baHierDrift_classes`; no BA import allowed here); the core lemma has an instance at `M₀ = 1`, `m = i` (`ExpHierGen.lean:877`).
- **Rules:** the C1/X1-C1 regex hits only `seqP` (instances), `PF d` (private fixed-size lemmas) and `Lloop` as a substring of `KLloopOf` (the `𝒦` loop index, not the band `Lloop`);
  `sz.withLam` only inside the proof of `stExpHiergL_at` (unpacking `CltRepg`); 0 new `def`; `Test/Axioms.lean` unchanged (the scan finds the same 144 premises).
## (c) Verified Mathlib names (one line each; `#check` in `names.lean`, all compiled in the files)
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` : ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : Measure α}
- `Real.hasDerivAt_sqrt` : ∀ {x : ℝ}, x ≠ 0 → HasDerivAt (fun x => √x) (1 / (2 * √x)) x
- `HasDerivAt.smul_const` : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2}
- `HasDerivAt.congr_of_eventuallyEq` : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2}
- `HasDerivAt.fun_finsetProd` : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {ι : Type u_2}
- `HasDerivAt.fun_sum` : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2} [inst_1 : NormedAddCo
- `Filter.EventuallyEq.deriv_eq` : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {F : Type u_2}
- `Integrable.mono'` : ∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : Measure α}
- `Integrable.of_bound` : ∀ {α : Type u_1} {E : Type u_2} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E]
- `integral_finsetSum` : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G]
- `probReal_univ` : ∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ], μ.re
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
- `intervalIntegral.integral_finsetSum` : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
- `intervalIntegral.integral_mul_const` : ∀ {a b : ℝ} {μ : Measure ℝ} {𝕜 : Type u_1} [inst : RCLike 𝕜] (r : 𝕜) (f : ℝ → 𝕜),
- `IntervalIntegrable.continuousOn_mul` : ∀ {A : Type u_1} [inst : NormedRing A] {a b : ℝ} {μ : Measure ℝ} {f g : ℝ → A},
- `ContinuousOn.intervalIntegrable_of_Icc` : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] {μ : Measure ℝ}
- `Ring.inverse_non_unit` : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] (x : M₀), ¬IsUnit x → Ring.inverse x = 0
- `hasFDerivAt_ringInverse` : ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {R : Type u_2} [inst_1 : NormedRing 
- `Matrix.trace_smul` : ∀ {n : Type u_1} {α : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : AddCommMonoi
- `Matrix.isHermitian_one` : ∀ {α : Type u_1} {n : Type u_2} [inst : NonAssocSemiring α] [inst_1 : StarRing α]
- `one_div_le_one_div_of_le` : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α]
- `Complex.coe_smul` : ∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : Module ℂ E] (x : ℝ) (y : E), ↑x • y =
- absent/deprecated: `intervalIntegral.integral_finset_sum` exists but warns `deprecated: use intervalIntegral.integral_finsetSum` (the file uses the latter).
## (d) Open issues and paper-delta candidates
- Ticket text, target 13: "`zeroModeSet` commutes with `Step2Gen_UN`" is false for a general carrier (preflight (a), rows `commutation`: defect 0.13-0.14 at carrier B) and is not used; dispatcher fix.  Not a paper delta (`6:142-146` is the band, where `X` commutes with the all-ones matrix).
- Premise shapes of the family theorems (merged rows 9-10 existential; rows 11-13 `∀ᶠ n`) are a choice of this row; BA discharges: `baCltRepg_holds`, `baStep2Mat_loopForm`, `baHierDrift_classes`, first conjunct of `baIniTermGen_kerFacts` (V1-BA, V1s2′/V1s3′ consumers).
- No paper-delta candidate (`T2502ba`: none): the targets are the band pins at `H₀ = 0` generalised to `H₀ ≠ 0` (`6:12-21`).  `RBM3D.lean` carries the two import lines on this branch (union at merge); no registry edit.
Report finished: Wed Oct 14 08:16:51 UTC 2026
