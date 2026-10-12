Prover model: claude-sonnet-5-5
## Result (stage 1b, `prover-max`, under Amend 1) — Mon Oct 12 01:13:33 UTC 2026
Branch `t/T2428` at `bed7d4f`; the probe `RBM3D/Probe/T2428Pins.lean` stays on the branch, never merged; `RBM3D.lean` and `RBM3D/Test/Axioms.lean` are untouched (registry: none; the hub adds the two import lines at merge).
- **Final names.** Target 2 (T.8) `BATwistGen`, `BATwistGen_holds`; target 3 (T.9) `BATwistHier`, `BATwistHier_holds`; 4 (a) `BATwistDuhamel`, `BATwistDuhamel_holds`; `BAuKerSemigroup`, `BAuKerSemigroup_holds`, `BAuKer_self`, `BAuKer_comp`; clause (i) of 4 (b) `baTwistGrid_decomp`, `baTwistGrid_decomp_ae`; the six pins `BATwistGridMartAt`, `BATwistGridMart`, `BATwistGridRem`, `BATwistGridTail`, `BATwistGridWTail`, `BATwistGridAssemble` (verbatim from the probe) and `baTwistGridAssemble_holds`.
- **Drift-kernel line (iii).** `twTheta_eq_thetaKer`: `Θ_u M^{(σ₀σ₁)} = Step2Gen_thetaKer (baFM sz lam0 E) n σ₀ σ₁ u`; `twU_eq_uKer`: `Ũ = Step2Gen_uKer` (`TwistGrid.lean:209, 214`, from `Step2Kern_thetaKer_BA`, `Step2Kern_uKer_BA`); the statements read `BATheta`, `BAMss`, `BAuKer`; the diagonal `2mm'(1-umm')⁻¹` occurs nowhere.
- **Clauses (ii)-(iv) of 4 (b): not proved here** (Amend 1; successor rows TL2a2-TL2a4, map in (b)).
- **Line counts** (stop line 2,000 per file): `RBM3D/BA/TwistGrid.lean` 963, `RBM3D/BA/TwistGrid2.lean` 345 (predicted 1,035 and 465).
- **Verdict.** Every target of Amend 1 is built, committed and has a compiled instance; axioms are the standard three; no hypothesis added, nothing weakened, no pinned signature changed. Table (ii) as finally proved and the successor map are in (b).

## (a) Math preflight — Sun Oct 11 22:23:30 UTC 2026
Notation: TP = docs/tickets/T2398-TL-proofs.md; paths relative to RBM3D/; B = L^d blocks, w = W^d; N = (WL)^d; Δ = (t-s)/K. Scripts: scratchpad T2428/ (not in the repository).

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | d, L | d = 3, L_0 = 4 (instance) | Targets 1-4 use no `3 ≤ d`: the inputs `BAflow_real` (BA/GreenSchur:59), `BATheta_isUnit/_resolvent/_hasDerivAt` (BA/KBase:325-347), `BAuKer_eq_one_add` (BA/EKPins:62), `baKsol_two` (BA/KInduct:88) carry `3 ≤ L` / `BAReal` only; `3 ≤ d` occurs in BA/KInduct only at :188, :291, :425 (not used). The band's `3 ≤ d` enters only through `stKbound_of_flow` (Path/DifREP1:36-37); here `K̃` is explicit (`twK`), no `K^{(k)}` bound is needed. | Decision: state target 4 for every d (DifREP2:55 does the same for its tails); add `hd` only if the probe finds a used lemma that carries it |
| 2 | coupling | `S^{(B)}(0) = I`, `S_xy = w⁻¹ 1[[x]=[y]]` (`EMn2BA_SB_zero`, BA/EMn2BA:77) | the walk of `Pp = pathP (sz.withLam 0)`; `H_k = g₀Ψ + pathH` (BA/Step2BA:68-72) | none (exact) |
| 3 | times | 0 ≤ s ≤ u_j ≤ t ≤ T0 < 1; instance s = 1/2, t = 2/3, T0 = 0.693740 | `BATheta_isUnit`, `_resolvent`, `_hasDerivAt` need 0 ≤ u < 1 (BA/KBase:324, :330, :341); `BAt0_lt_one` (BA/MFixedPoint:285) | 1-T0 = 0.3063; T0-t = 0.0271 |
| 4 | `‖M^{(σσ')}‖_{∞→∞}`, `‖Θ_u‖_{∞→∞}` | ≤ 1 and ≤ (1-u)⁻¹ | `BAKBase_norm` (KBase:312-316), Ward row sum; `u < 1` binding at (−,+) (KBase:321-323) | 0: row sum = 1.000000 and `‖Θ_u‖` = 2.0000, 3.0000 at u = 1/2, 2/3 (datum output) |
| 5 | η, (1-T0)⁻¹ | η_u = (1-u) Im m_F ≥ η_{T0} = √T0·Im z ≥ √(κ/(κ+1))·N^{-1+ε} | T0 = Im m/(Im m + Im z) (MFixedPoint:279) ≥ κ/(κ+1) by `BAdom` (MFixedPoint:435: κ ≤ Im m, N^{-1+ε} ≤ Im z ≤ 1); Im m_F = Im m/√T0 (BA/FlowPins:769); needed: η⁻¹ ≤ 16N | instance η_{T0}⁻¹ = 3.267 vs 16N = 3.4e7; in general √((κ+1)/κ)·N^{1-ε} ≤ 16N for all N ≥ 1 at κ = 1/2 |
| 6 | Δ-grid | KΔ = t-s ≤ 1; Δ ≤ N^{-CK} | K_n ≥ N_n^{CK} eventually (hypothesis of the pin, Chain/Step2Gen:863) | — |
| 7 | C₀ (∃, before sz, z, D) | 11 = m+9 at m = 2 (Path/DifREP1:1159) | Rem_k = Σ_{j<k}(E[A_{j+1}|F_j] - A_j - Δ·Drift_j) (DifREP1:62-70): per step ≤ Z₁Δ^{3/2} + 2Z₂Δ², k ≤ K: ≤ N^{C₀}√Δ if Z₁ + 2Z₂√Δ ≤ N^{C₀} (DifREP1:1089-1095). Band m = 2: Z₁ = c₁N^{10}, c₁ = 16·5⁴·32⁶ = 1.0737e13; Z₂ ≤ c₂N^{15}, c₂ = 4.1232e11 (DifREP1:1056-1062). Twist needs Z₁^{tw} ≤ c₁N^{10}, Z₂^{tw} ≤ c₂N^{15}. Hand count (not compiled): Z₁^{tw} = band envelope at k = 2 (`envConst`, Path/OneStep:78) since ‖P_{c1c2}‖ = W^{-d} = ‖E_a‖ (τ partial isometry, TP:22); Z₂^{tw}: time step `6N‖G‖⁴|m_F|²` + `‖∂²_u K̃‖ ≲ 2(1-u)⁻³κ⁻²` + Ũ-mismatch Δ²(1-u)⁻²‖A_j‖, order N⁵ with constants in κ | Z₂: N^{10}; Rem alone needs N ≥ c₁+1, 2c₂: n ≥ 2 along sz0 (N_2 = 8.1e14) |
| 8 | CK (∃, after D) | proposed CK(D) = 3D+40 | Rem 36 = 8m+20 (DifREP1:1159); tail (iii) 2m+2D+16 = 2D+20 (DifREP2:2173); weighted tail (iv) 9m+3D+22 = 3D+40 (DifREP3:37, 1915); one K serves all clauses, so CK = max; any larger CK is allowed (hypothesis `N^{CK} ≤ K n` only strengthens). Hand argument: the twist has one index and one kernel slot, so the band's m = 2 budgets are upper bounds | 3D+4 over the Rem value, D+20 over (iii) |
| 9 | ε', D, exponent 1/2 | free > 0; N^{ε'}(ΣΔ‖QV‖ + N^{-D})^{1/2} | (⌈mN(16N)^{2m+2}N^D⌉+1)·4·exp(-N^{2ε'}/(64m)) ≤ N^{-D}/2 (DifREP2:1961-1964), N ≥ max(c₂, 32cP) (:2190-2192), m = 2 | at ε' = 1/10, D = 1: first n = 9 (N = 2.1e24); fails at n = 8 (thr output) |
| 10 | QV, weights | E\|ξ\|² = Δ Σ_xy S_xy\|∂_xy L̃\|² = Δ·`twEE`(b,b); `Ũ^{(!σ0,!σ1)} = conj Ũ^{(σ0,σ1)}` | (Ũ⊗Ũ)∘(Ẽ⊗Ẽ)(a,a) = Σ_xy S\|Σ_b Ũ(a,b)∂_xy L̃(b)\|² ≥ 0 (M^{(B)} symmetric, `BAMB_symm`) | toy residuals 5.6e-17, 2.2e-16 (toy output) |
| 11 | one-step mismatch | Ũ_{u_j,u_{j+1}} = 1+ΔMΘ_{u_{j+1}} vs 1+ΔΘ_{u_j}M: ‖difference‖ ≤ Δ²(1-u_j)⁻¹(1-u_{j+1})⁻¹ | enters P_j (a), hence Rem of (b); (a) itself is the exact telescope, needs only semigroup + `Ũ_{v,v}=1` for 0 ≤ v,w < 1 | 8.13Δ² vs (1-u)⁻² = 9 at u = 1/2, Δ = 1/30 (duh output) |
| 12 | T.8, T.9 constants | none (identities (D.1), (D.4), (A.3)) | `m` = the `m` of `z_u = E+(1-u)m` (`ztOf`, Loop/GLoopFlow:55) in `Tr(G̊E) = L^{(1)} - m(σ)`; hand derivation: no `S[M] = mI` needed; `L^{(2)}_{(a,b)} = Tr(G(σ0)E_aG(σ1)E_b)` (`loopL`, GLoopFlow:123-124), `a` first | residual 3e-6 (h² scaling), controls 7.1 and 1.06 |

### (ii) One concrete nondegenerate instance
BA datum of `sz0` (Defs/Sizes:260) at n = 0: d = 3, L = 4, W = 32, lam = 1/64, N = 2097152; flow `flow_sz0` (BA/FlowPins:1214) at (κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10), z_0 = zS; window s ≡ 1/2 < t ≡ 2/3 ≤ T0 (`t0_sz0`, :1227); σ = (−,+) and (+,+); K_n = ⌈N_n^{CK}⌉ + 1 (the form of DifREP3:2397-2511). No external hypothesis occurs (TL1 and Steps 1-4 are TL2d's), so no limit computation is owed. The conclusions of target 4 are eventual in n; n_* = 9 for the tail at ε' = 1/10, D = 1 (row 9). K_{n_*} has about 10^{1046} (log10 = 1045.8): this is the pin's own hypothesis `N^{CK} ≤ K n`, passed to the theorem as a function and never evaluated; the band instances do the same.
```
$ python3 datum.py     (BA datum: m_S = L^-d tr(gΨ - 6i/5)^-1, z_S = 6i/5 - m_S, T0, E, g0 = √T0 g, m_F = m/√T0, M^B = (g0Ψ - E - m_F)^-1)
N=(WL)^d=2097152  Im m=0.832488 (kappa=1/2 ok: True)  Im z=0.367512  Im z+Im m=1.200000
N^(-1+eps)=2.044e-06 <= Im z <= 1: True   T0=0.693740 (>=2/3: True)  E=0.00e+00  g0=1.301423e-02 (0<g0<=1/2: True)
mF=m/sqrt(T0)=0.000000+0.999493j: Im mF=0.999493 >= kappa=1/2: True;  self-consistency |mF - tr M^B/L^d| = 2.22e-16
Ward (8.4): max_a |sum_b |M_ab|^2 - 1| = 1.55e-15
sigma=(-,+) u=0.5000: max row sum |M^(ss')|=1.000000 <=1, spectral radius=1.000000, ||Theta_u||_inf=2.0000 <= 1/(1-u)=2.0000
sigma=(-,+) u=0.6667: max row sum |M^(ss')|=1.000000 <=1, spectral radius=1.000000, ||Theta_u||_inf=3.0000 <= 1/(1-u)=3.0000
sigma=(+,+) u=0.5000: max row sum |M^(ss')|=1.000000 <=1, spectral radius=1.000000, ||Theta_u||_inf=0.6671 <= 1/(1-u)=2.0000
sigma=(+,+) u=0.6667: max row sum |M^(ss')|=1.000000 <=1, spectral radius=1.000000, ||Theta_u||_inf=0.6005 <= 1/(1-u)=3.0000
window s=0.5<t=0.6666666666666666<=T0=0.693740; 1-t=0.3333; eta_t=(1-t)Im mF=0.3332; eta_T0=(1-T0)Im mF=0.3061 = sqrt(T0) Im z=0.3061; 1/eta_T0=3.267 <= 16N=33554432
$ python3 duh.py       (U~ semigroup, U~ = 1+(u-v)MΘ_u, ∂Θ = ΘMΘ, discrete Duhamel telescope with random A_j, 64x64, s = 1/2, t = 2/3, K = 5)
sigma=(-,+): semigroup 2.0e-15; U=1+(u-v)M Theta_u 2.4e-15; dTheta=Theta M Theta 7.0e-09; telescope 1.1e-14; one-step Theta_j M vs M Theta_(j+1) mismatch/D^2 = 8.13 (D=0.0333)
sigma=(+,+): semigroup 1.6e-15; U=1+(u-v)M Theta_u 1.0e-15; dTheta=Theta M Theta 3.7e-11; telescope 6.8e-15; one-step Theta_j M vs M Theta_(j+1) mismatch/D^2 = 0.43 (D=0.0333)
$ python3 toy.py       (TP conventions; d = 1 toy: B = 3 blocks, w = 2, N = 6, Hermitian random H, E = 0.3, g = 0.5, m from (self_m), u = 0.55; generator = ∂_u + ½Σ S_xy ∂_xy∂_yx by finite differences h = 2e-4)
(D.1) max rel. residual over 4 charge pairs x 3 (c1,c2) x 3 a: 3.21e-06
(A.3) dK~/du = w sum_b K~(b) K^(2)(a,b), max abs residual: 4.02e-10
(D.4) drift identity max rel. residual: 3.12e-05
(D.2) d_xy L~ formula max rel. residual: 6.59e-10
nondegeneracy: Im m=0.7355, |L~|~1.701e-01, |Z|max~3.004e-01, |EG|~1.989e-02
(iv) |U~^(!s) - conj U~^(s)|max=2.2e-16; |(U(x)U)o(EE) - sum S|sum U d f|^2|max=5.6e-17; value~1.895e-01; EE hermitian err=3.5e-18, min eig=4.15e-02
$ bash neg.sh          (negative controls of (D.1))
control 1 (drop -m(sigma0) in E^G): (D.1) max rel. residual over 4 charge pairs x 3 (c1,c2) x 3 a: 7.11e+00
control 2 (L^(2) index order (b,a)): (D.1) max rel. residual over 4 charge pairs x 3 (c1,c2) x 3 a: 1.06e+00
$ python3 thr.py       (band budgets at m = 2 along sz0; D = 1, ε' = 1/10)
need N >= max(16,c1+1,2c2,c2',32cP) = 9.896e+15
 n= 0 N=2.097e+06 Rem/hbig budgets: False  hZ(eps'=1/10,D=1): False
 n= 2 N=8.125e+14 Rem/hbig budgets: False  hZ(eps'=1/10,D=1): False
 n= 3 N=1.441e+17 Rem/hbig budgets: True  hZ(eps'=1/10,D=1): False
 n= 8 N=3.148e+23 Rem/hbig budgets: True  hZ(eps'=1/10,D=1): False
 n= 9 N=2.097e+24 Rem/hbig budgets: True  hZ(eps'=1/10,D=1): True
n_* (all budgets) = 9  N_* = 2.097e+24; K_n = ceil(N^CK) with CK=3D+40=43.0: log10 K_* = 1045.8
```
Reading: Im m_F = 0.9995 ≥ κ = 1/2 and the self-consistency residual 2e-16 give `BAReal`; the row sums 1.000000 and `‖Θ_u‖ ≤ (1-u)⁻¹` give `BATheta` units for u ∈ {1/2, 2/3}; the window lies below T0 = 0.6937 and every kernel and bound above is nondegenerate (no N = 0, empty index, collapsed window or False premise). The toy has c₁ ≠ c₂ cases ((0,1), (2,1)) and all four charge pairs; |L̃| ≈ 0.17, |Z| ≈ 0.30, |Ẽ^{G̊}| ≈ 0.02.

### Verdicts
- Target 1 (vocabulary, bridges to TL0): PASS (definitions; the conventions of row 12 agree with `loopL`, `twLoopX`, `twK`).
- Target 2 (T.8 `BATwistGen`): PASS. Identity (D.1) and (D.2) hold at a Hermitian H, all σ, a, (c₁,c₂), tested with m from (self_m), z_u = E+(1-u)m; hand derivation: only `S[G]-m = wΣ(L^{(1)}-m)E` is used, so `Im m > 0`, `u < 1` suffice and `m` need not satisfy (self_m) (not tested numerically).
- Target 3 (T.9 (D.4) `BATwistHier`): PASS. Needs `BAReal` and 0 ≤ u < 1 (row 3), uses `K^{(2)} = w⁻¹ΘM^{(σ0σ1)}` (`baKsol_two`); drift identity and (A.3) hold at the toy.
- Target 4(a) (`BATwistDuhamel`): PASS (algebra, rows 3, 11; semigroup law and `Ũ_{v,v} = 1` for 0 ≤ v, w < 1).
- Target 4(b) (`BATwistGridMart`): PASS mathematically, with these open points for the probe: (1) the grid remainder of the twisted functional (Rem clause) is in neither TP nor merged (the merged envelope `OneStepEnvelope`, Path/OneStep:85, is for `loopL`); the route is the same third-order Taylor along the Gaussian step with `‖G‖ ≤ η⁻¹`, exponents as rows 7-8; (2) the tail clauses (iii), (iv) reuse only the abstract `difRep2_peel`, `difRep2_peel_N` (DifREP2:478, :757); `difRepTail_condMGF_Z` (:1404) and the `Y`-tail (`difRepTail_Y_tail` :1790, `difRep3_Y_tail` DifREP3:959) are stated for `ZvecN/YvecN` of loops and must be re-derived for the gradient (D.2); the exponents in rows 8-9 are the band's m = 2 values, an upper bound for one index. Whether this fits the two files is for the probe's item (v), not decided here.
- Overall: PASS. No BLOCKED input: TP:104-117 and TP:157-158 give T.8, T.9 and the martingale step; the merged inputs of rows 1, 4, 12 exist.

## (a″) Probe step — compressed at stage 1b to meet the 250-line limit (written Sun Oct 11 23:13:08 UTC 2026; full text: scratchpad `T2428/w/report_orig.md`, not in the repository)
Probe `RBM3D/Probe/T2428Pins.lean`, commits `6d04203`, `f6c3866` on `t/T2428` (344 lines, never merged); section (a) is not edited, no (a′) correction. `lake env lean RBM3D/Probe/T2428Pins.lean` exit 0, 0 `sorry`/`admit`/`native_decide`/`axiom`, 40 `#check` lines (24 new names, 16 merged declarations). Item (v) stopped before 1b as scoped (clauses (ii)-(iv): 3,445 predicted lines against the stop line 2,000 per file); the split proposed there was accepted by Amend 1 (predicted 1,035 and 465 lines for what is proved here).
Decisions fixed by the probe text (they bound 1b):
1. Names: pins as in (b), proofs `*_holds`, public `BAuKer_self`, `BAuKer_comp`; private helpers `TwistGrid_`, `TwistGrid2_`.
2. Every `d`, no `3 ≤ d`: `baKsol_two`, `BAflow_real`, `BATheta_hasDerivAt` carry `3 ≤ L` / `BAReal` only; the band's Rem needs `3 ≤ d` only through `stKbound_of_flow`, and `K̃ = twK` is explicit.
3. T.8 carries `0 < Im m`, `u < 1`, `H` Hermitian (no `3 ≤ L`, no `0 ≤ u`, `m` not tied to (self_m)); T.9 carries `BAReal`, `0 < g₀`, `0 ≤ u < 1`.
4. Clause (iv) has the band's shape (`STeeUMg` `:983`, `STGridRepNAtgL` `:994`): kernels at `(u_j, u_k)`, while the exact discrete identity 4 (a) has `Ũ_{u_{i+1},u_{j∧τ}}`; since `Ũ_{v,w} = 1 + (w - v) MΘ_w` (`BAuKer_eq_one_add`) the two weighted sums differ by `Δ MΘ_{u_k} Mart_k`: TL2d's.
Convention checks of the probe text (scratch, `d = 1`, `L = 3`, `W = 2`, random Hermitian `H`, `m = 0.37 + 0.81i` not a solution of (self_m), `u = 0.43`):
```
$ python3 t8check.py | grep -E 'worst|control'
worst rel residual 4.5510814467687774e-06
control 1 (drop -m(sigma) in E^G) worst rel residual 6.730e+00
control 2 (L^(2) index order (b,a)) worst rel residual 2.443e-01
```
Monte Carlo (40,000 samples, Δ = 2e-4) of `E|ΔL̃|²/Δ` against `twEEM(b,b)` (`qvcheck.py`): ratios 1.0052, 1.0111, 1.0059, 1.0000 at four (σ, triple) cases, both triples with `c₁ ≠ c₂`.
(iii) At the probe, `grep -c -E "STthetaOpg|STgDriftg|Step2Gen_ThetaN|Step2Gen_UN"` gave 0; `Step2Gen_thetaKer`, `Step2Gen_uKer` occurred only in a section comment and the two bridge `example`s (now `twTheta_eq_thetaKer`, `twU_eq_uKer`).
(iv) What TL2d imports: `BATwistDuhamel_holds`, `baTwistGridAssemble_holds` with the three parts, `BAuKer_self`, `BAuKer_comp`, and the vocabulary `twL2M` .. `twEEUM` with the `*_eq` bridges: the grid-state sources `twB1M`, `twB2M`, `twEGM` and the QV `twEEM` at `(u_j, Hpath j ω)` are TL0's `twB1`, `twB2`, `twEG`, `twEE` at `ω' ↦ sz.seqHflowBA lam0 n u ω'`, so `BATwistSrc1-5`, `BATwKer*` and TL2c's QV bound apply at the flow matrix once the grid statement is moved to the law of TL0. Moving it to `seqP (sz.withLam 0)`: the merged generic lemmas `RBM.Path.gridTransferPT` (`Path/Walk.lean:685`), `RBM.Gauss.Sizes.ST_whp_grid` (`Induction/Step2Core.lean:422`), `ST_pathP_eq_seqP` (`:400`); no BA wrapper is merged; TL2d's: the measurability of the twisted functionals in the matrix and the weights of decision 4.
(vi) Name clashes at the probe stage: 45 planned declaration names, no hit; `TwistGrid` is the stem of this ticket's file in four sibling scans (rerun at 1b in (b)).

## (b) Script output (stage 1b; scripts in scratchpad `T2428/w/`, not in the repository)
```
$ date -u; git log -1 --format="%h %s"; git status --short | wc -l
Mon Oct 12 01:10:53 UTC 2026
bed7d4f T2428: TwistGrid2: example that clause (i) is the first conjunct of BATwistGridRem
0
$ lake build RBM3D.BA.TwistGrid RBM3D.BA.TwistGrid2 2>&1 | grep -E "TwistGrid|error|Build completed"; (same, grep -c "warning: RBM3D/BA/TwistGrid")
Build completed successfully (4013 jobs).
0
$ wc -l RBM3D/BA/TwistGrid.lean RBM3D/BA/TwistGrid2.lean
     963 RBM3D/BA/TwistGrid.lean
     345 RBM3D/BA/TwistGrid2.lean
    1308 total
$ grep -c "sorry\|admit\|native_decide\|^axiom" (both files); grep -c -E "STthetaOpg|STgDriftg|Step2Gen_ThetaN|Step2Gen_UN" (both files); grep -c "RBM1D\|RBM2D" (both files)
RBM3D/BA/TwistGrid2.lean:0 RBM3D/BA/TwistGrid.lean:0 
RBM3D/BA/TwistGrid.lean:0 RBM3D/BA/TwistGrid2.lean:0 
RBM3D/BA/TwistGrid2.lean:0 RBM3D/BA/TwistGrid.lean:0 
$ git diff --stat main...t/T2428
 RBM3D/BA/TwistGrid.lean    | 963 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistGrid2.lean   | 345 ++++++++++++++++
 RBM3D/Probe/T2428Pins.lean | 344 ++++++++++++++++
 3 files changed, 1652 insertions(+)
```
Last build that recompiled (before the cached run above, after the last edit of `TwistGrid2.lean`): `✔ [4013/4013] Built RBM3D.BA.TwistGrid2 (3.4s)`, `Build completed successfully (4013 jobs).`, 0 warnings from either file.
```
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.BA.TwistGrid; import RBM3D.BA.TwistGrid2; #assert_rbm_axioms)
exit: 0
axiom audit: 12241 theorems, 3822 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ lake env lean ax_final.lean   (#print axioms of the 20 public theorems, grouped)
20 theorems with axioms [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2428-check.lean > check.out; echo "exit: $?"
exit: 0
$ bash clash2.sh names_final.txt   (git grep -w of the 52 names, the 50 declarations of the two files and the stems TwistGrid, TwistGrid2, on main and on every other local branch except t/T2428; grep -w in the check files and tickets of T2427, T2429, T2430, T2431)
names: 52; local branches other than main and t/T2428: 430
NONZERO TwistGrid main=0 other-branches=0 sibling-tickets=4
done
```
Pins and vocabulary against the probe, and the compiled instances (each line: the theorem applied at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `n = 0`):
```
$ python3 verb.py   (each `def NAME` block of the probe at f6c3866, from `git show`, against the same block in the two files)
30 blocks IDENTICAL
$ grep -n -o -E "<applications of the targets at sz0 / d = 3>" RBM3D/BA/TwistGrid.lean RBM3D/BA/TwistGrid2.lean   (line: applied theorem)
TwistGrid.lean:907 twL2M_eq sz0;  TwistGrid.lean:913 twL3M_eq sz0;  TwistGrid.lean:914 twEGM_eq sz0;  TwistGrid.lean:915 twB1M_eq sz0;  TwistGrid.lean:916 twB2M_eq sz0;  TwistGrid.lean:917 twDerM_eq sz0;  TwistGrid.lean:918 twEEM_eq sz0;  TwistGrid.lean:926 BATwistGen_holds 3;  TwistGrid.lean:934 BATwistHier_holds 3;  TwistGrid.lean:940 BAuKer_self hrI;  TwistGrid.lean:943 BAuKer_comp hrI;  TwistGrid.lean:949 BAuKerSemigroup_holds 3;  TwistGrid.lean:955 twTheta_eq_thetaKer sz0;  TwistGrid.lean:959 twU_eq_uKer sz0;  
TwistGrid2.lean:302 BATwistDuhamel_holds 3;  TwistGrid2.lean:314 baTwistGrid_decomp sz0;  TwistGrid2.lean:317 baTwistGrid_decomp_ae sz0;  TwistGrid2.lean:331 baTwistGridAssemble_holds 3;  TwistGrid2.lean:336 baTwistGridAssemble_holds 3;  
```
Target statements extracted from the files by script (`stmt.py`; the `d`-pins are `Prop`-valued defs, the `*_holds` theorems prove them for every `d`):
```
-- TwistGrid.lean:775 (def) and TwistGrid.lean:781 (theorem BATwistGen_holds (d : ℕ) : BATwistGen d)
def BATwistGen (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im → ∀ u : ℝ, u < 1 →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
      twGenM sz lam0 E n u H σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, twL2M sz lam0 E n u H σ b c₁ c₂ * (baStep2Mat sz lam0 E).LM n u H σ ![a, b] +
        twEGM sz lam0 E n u H σ a c₁ c₂
-- TwistGrid.lean:849 (def) and TwistGrid.lean:855 (theorem BATwistHier_holds (d : ℕ) : BATwistHier d)
def BATwistHier (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ : ℝ), 0 < κ → 0 < lam0 n → BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
    ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        twGenM sz lam0 E n u H σ a c₁ c₂ - deriv (fun v : ℝ => twK (baFM sz lam0 E) n v σ a c₁ c₂) u = twDriftM sz lam0 E n u H σ a c₁ c₂
-- TwistGrid2.lean:133 (def) and TwistGrid2.lean:143 (theorem BATwistDuhamel_holds (d : ℕ) : BATwistDuhamel d)
def BATwistDuhamel (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz), min j (τ ω) ≤ K n →
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ (min j (τ ω)) ω =
          twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω))) *ᵥ
              twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ 0 ω +
            ∑ i ∈ Finset.range (min j (τ ω)), twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω))) *ᵥ
              (twPredInc sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ i ω + twMartInc sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ c₁ c₂ i ω)
TwistGrid.lean:195  def BAuKerSemigroup (d : ℕ) : Prop :=
TwistGrid.lean:184  theorem BAuKer_self (hr : BAReal d L g κ E m) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (σ₁ σ₂ : Bool) :
TwistGrid.lean:188  theorem BAuKer_comp (hr : BAReal d L g κ E m) {u v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (σ₁ 
TwistGrid.lean:209  theorem twTheta_eq_thetaKer (σ : Fin 2 → Bool) (u : ℝ) :
TwistGrid.lean:214  theorem twU_eq_uKer (σ : Fin 2 → Bool) (v w : ℝ) :
TwistGrid2.lean:169  theorem baTwistGrid_decomp {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
TwistGrid2.lean:182  theorem baTwistGrid_decomp_ae {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
TwistGrid2.lean:260  def BATwistGridAssemble : Prop :=
TwistGrid2.lean:265  theorem baTwistGridAssemble_holds : BATwistGridAssemble := by
```

Proof routes (all three are exact algebra; no `sorry`, nothing assumed):
- T.8 `BATwistGen_holds` (:781): the direct `n = 2` computation at the block-product index, the twisted twin of `DriftAlgebra_loopGen_core` (`Path/DriftAlgebra.lean:429`); no word calculus (`P_{c₁c₂}` is not a letter). `TwistGrid_twLoopX_eq` (:308), `TwistGrid_twL3_eq` (:386) turn `twL2M`, `twL3M` into traces `Tr(X₁E_aX₂P)`, `Tr(X₀E_{a₁}X₁E_{a₂}X₂P)` of `Gres (blockMat H)`; `TwistGrid_second` (:467) is the line Hessian `2(T₁+T₂+T₃)`; `TwistGrid_cov` (:563) the contraction `sum_allCoords_trace_blocks` at `SB d L 0 = 1` (`EMn2BA_SB_zero`); `TwistGrid_deriv_spec` (:544) the spectral derivative `∂_u G(z_u) = -m(σ) G²`; `Σ_p E_p = W^{-d}` turns it into the `-m(σ)` of `Ẽ^{G̊}`.
- T.9 `BATwistHier_holds` (:855): `∂_u K̃` by `BATheta_hasDerivAt` and the explicit `twK` (`TwistGrid_hasDerivAt_twK` :825); `𝒦^{(2)} = W^{-d} Θ M` by `baKsol_two`; then `L̃L - K̃K = K̃(L-K) + ZK + Z(L-K)`, no matrix identity.
- 4 (a) `BATwistDuhamel_holds` (TwistGrid2:143): `duhamel_telescope` (`Path/Kernel.lean`) with the clamped times `u_{min(i,m)}`, its hypotheses from `BAuKer_self`, `BAuKer_comp`; `A_{i+1} - Ũ A_i = P_i + ξ_{i+1}` is `TwistGrid2_twAk_step` (:89).
Table (ii) as finally proved (band `file:lines` ↦ twin `file:line`; `TG` = `TwistGrid.lean`, `TG2` = `TwistGrid2.lean`):
| band source | twin as proved | status |
|---|---|---|
| `LoopGenN` §1, §4, §5 :55-89, :261-481 | none: direct block-level computation | dropped |
| `LoopGenN` §2 :91-120 (second-derivative bridge) | `TwistGrid_second` TG:467, `TwistGrid_cov` TG:563 | changed |
| `LoopGenN` §3 :122-259 (spectral bridge) | `TwistGrid_hasDerivAt_Gsig_spec` TG:517, `TwistGrid_deriv_spec` TG:544 (private copy of :146-183, generic index) | changed |
| `LoopGenN` §6, `loopGenNOf` :483-550, :554-629 | `TwistGrid_gen_core` TG:626, `BATwistGen_holds` TG:781 | changed |
| `HierarchyN` :56-72, `HierAlgebra` :722-760 | `BATwistHier_holds` TG:855, `TwistGrid_hasDerivAt_twK` TG:825 | changed |
| `GridDuhamelN` §1 :56-195 | `BAuKer_self` TG:184, `BAuKer_comp` TG:188 | changed |
| `GridDuhamelN` §4 :264-340 | `twAk`, `twMartInc`, `twPredInc` TG2:59, 62, 65; `TwistGrid2_twAk_duhamel` TG2:98; `BATwistDuhamel_holds` TG2:143 | changed (telescope = public `duhamel_telescope`) |
| `GridDuhamelN` §7-§8 :425-604 | none | dropped |
| `DifREP1` §1-§2 :53-172 | `twMart` TG2:77, `twRem` TG2:79, `baTwistGrid_decomp` TG2:169 | changed |
| `DifREP1` §5 :1238-1309 | `baTwistGridAssemble_holds` TG2:265 | changed |
| `DifREP1` §3-§4, `OneStep` §1-§7, `DifREP2`, `DifREP3` | none | successor rows TL2a2-TL2a4 |
| (new) `Idx` block sums to `Vtx` sums | `TwistGrid_twLoopX_eq` TG:308, `TwistGrid_sum_blk3` TG:347, `TwistGrid_twL3_eq` TG:386 | new |
Successor map (Amend 1 item 3): TL2a2 = clause (ii), the bound `‖twRem‖ ≤ N^{C₀}√Δ` of `BATwistGridRem` (central 1,380 lines, two files; its clause (i) is `baTwistGrid_decomp_ae`, which fits the first conjunct: example TG2:319-327); TL2a3 = clause (iii) `BATwistGridTail` (915); TL2a4 = clause (iv) `BATwistGridWTail` (1,150); each with its own 1a. `baTwistGridMart_holds` is then a three-line corollary of `baTwistGridAssemble_holds` and the three part theorems, written in TL2d (`BATwistGridMart d := ∃ C₀, 0 ≤ C₀ ∧ BATwistGridMartAt d C₀`), which also owns the move to `seqP (sz.withLam 0)` and decision 4 of (a″).
Instances: `d = 3`, `sz0` (`L = 4`, `W = 32`, `N_0 = 2,097,152`), `n = 0`, `σ = (false, true)`, `c₁ = 0 ≠ c₂ = (1,0,0)`, window `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`), `H` the Hermitian flow matrix `seqHflowBA` of an arbitrary sample: no `N = 0`, empty index set, collapsed window or `False` premise. The three part pins stay hypotheses of the instances of `baTwistGridAssemble_holds` (successor rows).
Ports: no text was copied from `../RBM1D` or `../RBM2D` (grep 0 above); the twins are the merged RBM3D files of the table, whose headers cite their RBM2D sources (`Path/DriftAlgebra.lean`: `c9a24cf`), so no RBM1D/RBM2D diff-stat applies.

## (c) Verified Mathlib names (all compile; `#check` run on the final commit, 0 errors)
- `Matrix.submatrix_mul_equiv` (Data/Matrix/Mul.lean:1191); `Matrix.mulVec_add` (:792); `Matrix.mulVec_mulVec` (:889); `Matrix.one_mulVec` (:1003)
- `Matrix.inv_submatrix_equiv` (LinearAlgebra/Matrix/NonsingularInverse.lean:722); `Matrix.conjTranspose_nonsing_inv` (:205); `Matrix.nonsing_inv_eq_ringInverse` (:195)
- `Matrix.trace_mul_comm` (LinearAlgebra/Matrix/Trace.lean:158); `Matrix.traceLinearMap` (:91)
- `Equiv.sum_comp`, `Finset.sum_filter` (Algebra/BigOperators/Group/Finset/Basic.lean:333), `Finset.sum_eq_single` (:355): by `#check`
- `HasDerivAt.fun_sum` (Analysis/Calculus/Deriv/Add.lean:218); `HasDerivAt.const_mul` (Deriv/Mul.lean:345); `HasDerivAt.congr_deriv` (Deriv/Basic.lean:597)
- `HasFDerivAt.comp_hasDerivAt` (Analysis/Calculus/Deriv/Comp.lean:374); `Commute.mul_mul_mul_comm` (Algebra/Group/Commute/Defs.lean:115)
- `Real.rpow_le_rpow_of_exponent_le` (Analysis/SpecialFunctions/Pow/Real.lean:617); `Nat.le_ceil` (Algebra/Order/Floor/Semiring.lean:178); `AddMonoidHom.mk'` (by `#check`)
Names verified absent: none needed. Merged RBM3D declarations used (compiled): `sum_allCoords_trace_blocks`, `hasDerivAt_green_moving`, `OneStep_isHermitian_add_realSmul`, `duhamel_telescope`, `gridTime_last`, `BATheta_hasDerivAt`, `BATheta_resolvent`, `baKsol_two`, `BAflow_real`, `BAMfine_eq`, `EMn2BA_SB_zero`, `Step2Kern_thetaKer_BA`, `Step2Kern_uKer_BA`, `baStep2Data` (`flowOK_T`).

## (d) Open issues and paper-delta candidates
- Open: clauses (ii)-(iv) of 4 (b) (TL2a2-TL2a4, map above); `baTwistGridMart_holds` in TL2d; the move of the grid statement to `seqP (sz.withLam 0)` and the weights of decision 4 (TL2d). The constants of (a) rows 7-9 (`C₀ = 11`, `CK = 3D+40`) are hand counts for the successor rows, not used here.
- T2428a (grid form of (D.5)): the Lean statement is the exact discrete Duhamel identity 4 (a), the canonical decomposition `baTwistGrid_decomp`, and the tails by Azuma on the grid in place of BDG (the convention of `Path/DifREP2.lean`, DECISIONS §7, D90); the paper's (D.1), (D.5) are the stochastic differential and Itô forms.
- T2428b (generality): T.8, T.9, 4 (a) and the semigroup law are stated for every `d` (no `3 ≤ d`); T.8 needs only `0 < Im m`, `u < 1`, `H` Hermitian (no `0 ≤ u`, no `3 ≤ L`, `m` not tied to (self_m)); weaker hypotheses than the paper's setting, no new input.
- T2428c (clause (iv) weights): `Ũ_{u_j,u_k}` in the pin versus `Ũ_{u_{i+1},u_{j∧τ}}` in 4 (a) (decision 4 of (a″)); a Lean-side convention, TL2d's.
