Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 17:45:17 UTC 2026

**Verdicts: target 1 PASS; 2a, 2b, 2c, 2d PASS; 3 PASS; 4 PASS; 5 PASS. No BLOCKED.** Stage 1b may start.

### (i) Exponent table
Notation: `N = sz.size n = (WL)^d`, `Q = N²`, `Xb = 2N²`, `Δ = |u-u'| ≤ 1` (`u,u' ∈ [s_n,t_n] ⊂ [0,1)`), `x = √Δ`. "needs `N ≥ c`" = the `∀ᶠ n` of the pin (`SizeTendsto`). All monomials are `c·N^e`; `N ≥ 1` lets a lower power be absorbed in a higher one.

| # | constant | value | constraint / source | slack |
|---|---|---|---|---|
| 1 | `‖Xmat‖, ‖blockMat Xmat‖` on `contGood` | `≤ 2N²` | `cont_norm_Xmat_le`, `cont_norm_blockMat_Xmat_le` (`ContinuityNet:549,556`), `card Idx = N` (`Defs/Sizes:160`), `Vtx = Zd d L × Fin (W^d)` (`Gauss/Model:60`) so `card Vtx = L^dW^d = N`, coordinates `≤ N` | exact |
| 2 | `(η_t)⁻¹ ≤ Q` | `Q = N²` | `nl2_eta_inv_le` (`NetLift2:203`): `(1-t)⁻¹ ≤ N` (premise), `1/c₁ ≤ N`, `c₁ = √(2κ)/2` (`cont_bulk`, `ContinuityNet:772`); eventually | exponent 2 exact |
| 3 | loop of length `k`, modulus | `Lip_k = N·k·Q^k·Q²(Xb+1) ≤ 3k N^{2k+7}` | `nl2_loop_sub` (`NetLift2:136`) with `nl2_word_norm`/`nl2_word_diff` (`:64,:83`); `STLI`/`loopL` is the trace of the same `nl2Word` of the list `σ.zip a` (`nl2_loopFine_eq :122`), any length | `k=1,2,3,6`: `3N⁹, 6N¹¹, 9N¹³, 18N¹⁹` (script) |
| 4 | loop of length `k`, size | `‖𝓛^{(k)}‖ ≤ N·Q^k = N^{2k+1}` | `nl2_word_norm` + `norm_matrix_trace_le_card_mul` (`FlowCalculus:600`) | `N³, N⁵, N⁷, N¹³` |
| 5 | `𝒦^{(2)}` | Lip `N²`, size `N` | `KLK_two` (`KLTree:211`): `W^{-d}μΘ_{uμ}(a₀,a₁)`, `‖μ‖=1` (`norm_mSigma`, `|E|≤2`); `Θ_ζ-Θ_ξ=(ζ-ξ)Θ_ζSΘ_ξ` (`Theta_sub_Theta`, `Deriv:57`, `norm_SB` `Block:136`); `‖Θ_{uμ}‖ ≤ (1-u)⁻¹ ≤ (1-t)⁻¹ ≤ N` (`norm_Theta_le`, `Props4:218`); `W^{-d} ≤ 1`, `Δ ≤ x` | `W^{-d}(1-t)^{-2}Δ ≤ N²x` |
| 6 | **2a** `STLK2` | `Lip ≤ 6N¹¹+N² ≤ 7N¹¹`; **C = 12**, `N ≥ 7` | reverse triangle `|‖A-K‖-‖A'-K'‖| ≤ ‖A-A'‖+‖K-K'‖` | `7N¹¹ ≤ N¹²` at `N ≥ 7` |
| 7 | **2b** `STELKLK` | size `‖LK₂‖ ≤ 2N⁵`; `N·2·(7N¹¹)(2N⁵) = 28N¹⁷`; **C = 18**, `N ≥ 28` | `W^d Σ_{x,y}|A_x||S_xy||B_y|`, `Σ_y|S_xy| = 1` (`sum_norm_SB_row`, `Block:118`) so `W^dΣ_{x,y}|S_xy| ≤ W^dL^d = N` (cruder than the ticket's `L^{2d} ≤ N²`; any larger `C` is admissible) | `28N¹⁷ ≤ N¹⁸` |
| 8 | **2c** `STEGt` | avg: Lip `3N⁹`, size `≤ 2N³` (`|m|=1`); 3-loop Lip `9N¹³`, size `N⁷`; `2·N·(3N⁹N⁷+2N³·9N¹³) = 42N¹⁷`; **C = 18**, `N ≥ 42` | `STavgM` is a 1-loop minus `STmsig` (`u`-independent) | `42N¹⁷ ≤ N¹⁸` |
| 9 | **2d** `STee` (`m=2`, every `a'`) | `2N·18N¹⁹ = 36N²⁰`; **C = 21**, `N ≥ 36` | `STeeLoop` has length `(3-k)+k+k+(3-k) = 6` for `k = 1,2` (asserted in the script); two cut edges; `Σ_{b,b'}|S_{bb'}| = L^d` | `36N²⁰ ≤ N²¹` |
| 10 | relative continuity of `ρ = 1+(1-t)⁻¹Δ` | `ρ ≤ 1+Nx`; `ρ^j ≤ 1 + j2^{j-1}N^j x`, `j ≤ 6` | `(1-t)⁻¹ ≤ N`, `Δ ≤ x ≤ 1`; powers of `ρ` in the five `R`'s: concl. 1 `R`: `ρ·ρ·ρ² = ρ⁴`; concl. 2 `R₀: ρ³`, `R: ρ⁴`; concl. 3 `R₀: ρ⁵`, `R: ρ⁶` | `C_R = 7`, `N ≥ 192` |
| 11 | **target 4** `C₄` | `C₂ₐ + D + 3 = 15 + D` | chain below | `N ≥ 7` |
| 12 | **(G)** mesh | `A = 2(\|C\|+\|CR\|)+2` (proof needs `A ≥ 2(C+max(CR,1))`) | `δ = N^{C} x ≤ N^{C-A/2} = N^{-CR-1}`: `≤ N^{-CR}` (= `ε`, `hlow`/`hclose` of `cont_core`, `ContinuityNet:142-154`) and `≤ N^{-1}` | slack `N^{-1}` in both; `A ≥ 0` |
| 13 | **(G)** `ζ(u') ≤ 2ζ(u)` | `(1+δ)^{m+1} ≤ 2` | `ζ(u') ≤ (1+δ)R₀(u)+((1+δ)J)^m(1+δ)R ≤ (1+δ)^{m+1}ζ(u)` (`m ≥ 0`, `J ≥ 1`, `rpow` monotone); `δ ≤ 1/N`, `(1+1/N)^{m+1} ≤ e^{(m+1)/N} ≤ e^{1/2} < 2` for `N ≥ 2(m+1)` | `m = 3/2, 2, 3`: `N ≥ 5, 6, 8` (script) |
| 14 | **(G)** `hcard` | `Cv = max(Cv,0)`; for S5-09: `4L^{2d} ≤ 4N² ≤ N³` (concl. 1-3), `4L^{4d} ≤ 4N⁴ ≤ N⁵` (concl. 4, `L^d ≤ N`) | `N ≥ 4` | `Real.rpow` monotone in the exponent for `N ≥ 1` |
| 15 | **floors** (required line) | `R₁ = (1-u)⁻¹(W^d\|1-u\|)⁻¹T ≥ N⁻¹W^{-D}`; `R₂ = (1-u)⁻¹(W^d\|1-u\|)^{-1/2}T ≥ N^{-1/2}W^{-D}`; `R₃ = (1-u)⁻¹(W^d\|1-u\|)^{-1/2}T² ≥ N^{-1/2}W^{-2D}`; **CR = 1+2D** | `0 ≤ u < 1` gives `(1-u)⁻¹ ≥ 1`, `(W^d\|1-u\|)⁻¹ ≥ N⁻¹` (`W^d ≤ N`); `T ≥ W^{-D}` (`tailTD` first term `≥ 0`, `Defs/Tail:173`); `W ≤ N`, `D > 0`; `R₀ ≥ 0` | `CR_i = 1+D, ½+D, ½+2D ≤ 1+2D` (script); `N^{-CR}` decreases in `CR` |
| 16 | chain `(1-t)⁻¹ ≤ N`, regime (iii) | `(1-t)⁻¹ ≤ lam⁻² ≤ W^d ≤ N` | `lam² ≤ 1-t` (`STReg5III`, `Step5Pins:58`); `1 ≤ lam²W^d` (`lam_sq_mul_pow_ge`, `Defs/Sizes:193`, `W^{2𝔡} ≥ 1`, from `WO`); `L ≥ 1` | at `sz0`: `lam²W^d = (2(n+1))³ ≥ 8` |
| 17 | chain, window (i)+(ii) | `(1-t)⁻¹ ≤ L^d lam⁻² ≤ L^dW^d = N` | `lam²/L^d ≤ 1-t` (`STReg5Mid`, `Step5Pins:54`); same `1 ≤ lam²W^d` | same |

**Target 4, chain.** `ρ = 1+(1-t)⁻¹Δ`; relcont (target 3, `u↔u'`) gives `T(u) ≤ ρ²T(u')`. For every `(σ,a)`:
`STLK2(u')/T(u') ≤ ρ²(STLK2(u)+N^{12}x)/T(u) ≤ ρ²(J♯(u) + N^{12}x·N^{D}) ≤ ρ²(1+N^{12+D}x)J♯(u)`
(2a at `C=12`; `T(u) ≥ W^{-D} ≥ N^{-D}` since `W ≤ N`, `D > 0`; `J♯(u) ≥ 1`); the outer `max 1` is `1 ≤ ρ²(1+·)J♯(u)`. Then `ρ ≤ 1+Nx` and `x ≤ 1`: `ρ² ≤ 1+3N²x`, `(1+3N²x)(1+N^cx) ≤ 1+7N^{c+2}x ≤ 1+N^{c+3}x` (`c = 12+D`, `N ≥ 7`): `C₄ = 15+D ≥ 0`.

**Target 3 (L2).** `(1-u')⁻¹ ≤ ρ(1-u)⁻¹`: `cont_inv_add_one_sub_ratio` (`ContinuityNet:676`) at `γ=0`, `u↔u'`, `|1-u| = 1-u > 0`; `(W^d·)⁻¹` multiplies by `(W^d)⁻¹ ≥ 0`; `x ≤ ρy ⇒ x^{1/2} ≤ ρ^{1/2}y^{1/2} ≤ ρy^{1/2}` (`ρ ≥ 1`); `T(u') = ((W^d|1-u'|)⁻¹)²e + W^{-D} ≤ ρ²(…)²e + W^{-D} ≤ ρ²T(u)`; squares: `T(u')² ≤ ρ⁴T(u)²` (`T ≥ 0`). No sign hypothesis on `u,u'` is needed.

### Consumer check (§45 O2, required line)
Conclusions of `STLemDecCalEConcl` (`Step5Pins:161-186`) as `R₀ + J^m R` with `J = J♯`, `ξ = ‖F‖`: (1) `ELKLK`, `m = 2`, `R₀ = 0`, `R = R₁` (pin has `Jst ^ 2`: `Real.rpow_two`/`rpow_natCast`); (2) `EGt`, `m = 3/2`, `R₀ = (1-u)⁻¹𝟙·T`, `R = R₂`; (3) `ee`, `m = 3`, `R₀ = (1-u)⁻¹𝟙·T²`, `R = R₃`; `𝟙` does not depend on `u`. `V n = (Fin 2→Bool)×(Fin 2→Zd d (L n))` makes `TimeIcc × V n` definitionally `STIdx2` (an `abbrev`, `Step5Pins:139`). Concl. 4: `V' n = {r : (Fin 2→Bool)×(Fin 2→Zd)×(Fin 2→Zd) // ∀ i, dist ≤ (log W)^{3/2}}`; the pin's index is `{q : STIdx2 × (Fin 2→Zd) // …}`; `StochDomAt.precomp_param` (`StochDomAt:335`, `h : StochDomAt` on `U`, `φ : V → U`) is applied with `φ : pin index → TimeIcc × V'`, `q ↦ (q.1.1, ⟨(q.1.2, q.2), q.property⟩)`. Rows 6-9, 11, 15 give the `ξ`-Hölder, `J♯`-relative and `R`-relative hypotheses with a common `C = max(C_ξ, 15+D, 7)`: at `D = 42`, `C = 57` for all three, `CR = 85`, `A = 286`, `δ = N^{-86}` (script). S5-13 (`STEtermsMidConcl`, `Step5Pins:257-271`): `ξ = ‖STELKLK‖, ‖STEGt‖` use 2b, 2c; `STEEk` is not covered by 2a-2d, only by the public loop-level helpers (row 3-4); its `ζ` (`STprof`, `etaT⁻¹`, `STAI`) is deterministic and needs its own relative continuity, which T2198 does not give (not a defect of T2198).

### (ii) One concrete nondegenerate instance
Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))⁵`, `lam = (2(n+1))⁻⁶`, `Defs/Sizes:260`), `E ≡ 1/2`, `κ = 1` (`|E| = 1/2 ≤ 1`), `s ≡ 0`, `t ≡ 1/16`, `D = 42`; `TimeIcc = [0,1/16]`, `Fin 2→Bool`, `(Zd 3 L)²` all nonempty. Hypotheses: `3 ≤ d`; `SizeTendsto sz0` (`sz0_tendsto`; limit: `N_n = 2²¹(n+1)¹⁸ → ∞`, asserted below); `0<κ`, `|E| ≤ 2-κ`, `0 ≤ s`, `t < 1`; `(1-t)⁻¹ = 16/15 ≤ N_n` for every `n` (`N_0 = 2097152`); `0 < D`; (G): `s ≤ t`, `t-s = 1/16 ≤ 1`.
```
$ python3 <scratchpad>/T2198/inst1.py
n=0: N=2097152 (1-t)^-1=16/15 lam^2<=1-t:True lam^2/L^d<=1-t:True lam^2W^d=8 chain(iii):True chain(mid):True
n=1: N=549755813888 (1-t)^-1=16/15 lam^2<=1-t:True lam^2/L^d<=1-t:True lam^2W^d=64 chain(iii):True chain(mid):True
n=2: N=812479653347328 (1-t)^-1=16/15 lam^2<=1-t:True lam^2/L^d<=1-t:True lam^2W^d=216 chain(iii):True chain(mid):True
n=3: N=144115188075855872 (1-t)^-1=16/15 lam^2<=1-t:True lam^2/L^d<=1-t:True lam^2W^d=512 chain(iii):True chain(mid):True
n=4: N=8000000000000000000 (1-t)^-1=16/15 lam^2<=1-t:True lam^2/L^d<=1-t:True lam^2W^d=1000 chain(iii):True chain(mid):True
n=5: N=212986666247081951232 (1-t)^-1=16/15 lam^2<=1-t:True lam^2/L^d<=1-t:True lam^2W^d=1728 chain(iii):True chain(mid):True
target 3: five inequalities hold at 6750 exact grid points (t,W,d,u,u',D,e)
float check, 2e5 random points, rpow 1/2 form, true exp(-sqrt r): ok; max lhs/rhs of (3) = 0.999999
target 3 instance (n=1: L=8 W=1024, rho=16/15):
  (1) 16/15 <= 16/15 : True   (2) 9.934e-10 <= 9.934e-10   (3) 3.152e-05 <= 3.255e-05   (4) 2.399e-19 <= 2.399e-19   (5) 5.756e-38 <= 5.756e-38
$ python3 <scratchpad>/T2198/exps.py
2a: Lip <= 7 N^11 sqrt|u-u'|  ->  C = 12, needs N >= 7
2b: Lip <= 28 N^17 sqrt|u-u'|  ->  C = 18, needs N >= 28
2c: Lip <= 42 N^17 sqrt|u-u'|  ->  C = 18, needs N >= 42
2d: Lip <= 36 N^20 sqrt|u-u'|  ->  C = 21, needs N >= 36
R: rho^6 <= 1 + 192 N^6 x  -> C_R = 7, needs N >= 192
J#: C4 = C2a + D + 3 = 15 + D, needs N >= 7
  check (1+Nx)^2 (1+N^c x) <= 1+N^(c+3) x, N>=7, x in [0,1], c in [1,60]: ok (2e5 random points)
concl.1 (ELKLK): m=2 C=57 CR=85 A=286 delta=N^(-86) = N^(-CR-1); (1+1/N)^(m+1)<=2 for N>=6
concl.2 (EGt): m=3/2 C=57 CR=85 A=286 delta=N^(-86) = N^(-CR-1); (1+1/N)^(m+1)<=2 for N>=5
concl.3 (ee): m=3 C=57 CR=85 A=286 delta=N^(-86) = N^(-CR-1); (1+1/N)^(m+1)<=2 for N>=8
floor R1=(1-u)^-1 (W^d|1-u|)^-1 T >= N^-1 W^-D: CR_i = 43 <= CR = 1+2D = 85
floor R2=(1-u)^-1 (W^d|1-u|)^-1/2 T >= N^-1/2 W^-D: CR_i = 85/2 <= CR = 1+2D = 85
floor R3=(1-u)^-1 (W^d|1-u|)^-1/2 T^2 >= N^-1/2 W^-2D: CR_i = 169/2 <= CR = 1+2D = 85
$ python3 <scratchpad>/T2198/check_impl.py && python3 <scratchpad>/T2198/torus.py && python3 <scratchpad>/T2198/jsharp.py
implementation checks vs literal words: ok
N = 216 ; max |G| entries and loop sizes:  max|L2| = 0.13028629454600962 max|K2| = 0.12823695946152483
2a: max|F| = 2.834e-03; max |F(u)-F(u')|/sqrt|u-u'| = 2.768e-02; ratio to N^C (C=12) = 2.684e-30; <=1: True
2b: max|F| = 2.570e-05; max |F(u)-F(u')|/sqrt|u-u'| = 6.075e-04; ratio to N^C (C=18) = 5.800e-46; <=1: True
2c: max|F| = 1.609e-03; max |F(u)-F(u')|/sqrt|u-u'| = 1.287e-02; ratio to N^C (C=18) = 1.229e-44; <=1: True
2d: max|F| = 1.185e-12; max |F(u)-F(u')|/sqrt|u-u'| = 5.409e-10; ratio to N^C (C=21) = 5.124e-59; <=1: True
D=1: J#(0), J#(1/64), J#(1/16) = [1, 1, 1] ; raw max ratio at u=1/16: 0.013366416335632224
D=3: J#(0), J#(1/64), J#(1/16) = [1, 1, 1] ; raw max ratio at u=1/16: 0.048472762742448376
D=42: J#(0), J#(1/64), J#(1/16) = [1, 1, 1] ; raw max ratio at u=1/16: 0.3892968757703095
```
Reading: `inst1` asserts both §29 chains for `n = 0..5` and the five inequalities of target 3 (exact `Fraction`s, `e` standing for `exp(-√r) ∈ [0,1]`, which does not depend on `u`; the `x^{1/2}` form checked as `x ≤ ρ²y` and in floats); at the instance `(n=1, u=0, u'=1/16)` inequality (1) is an equality, so `ρ` is sharp. `exps` computes the monomials of rows 3-15 and the thresholds. `torus`: `d=3, L=3, W=2` (`N=216`), `lam=1/2`, `E=1/2`, one Gaussian sample (Hermitian, sampled with `E|X_{xy}|² = W^{-d}S^B_{ab}`, asserted all coordinates `≤ N`), `u,u' ∈ {0,1/64,1/16}`, 2a-2c over all `σ,a`, 2d over 60 random `(σ,a,a')`; the implementation (`L²`, `L³`, `STee` through `X₁,X₂`) is checked against the literal words first. The proven `C` are far from tight on the sample (ratios `≤ 3·10⁻³⁰`), as expected from the crude `Q = N²`; `J♯ = 1` on this sample for `D ∈ {1,3,42}`, so target 4 is exercised only trivially numerically (its proof is the chain above).
External hypotheses: `SizeTendsto` (targets 2, 4, 5) and the eventual `(1-t)⁻¹ ≤ N` (targets 2, 4) are premises; their limit computation is the `N_n` formula and the `16/15 ≤ N_n` rows above. The consumer's `WO` (`lam²W^d ≥ 1`) is used only in rows 16-17 (to discharge the premise), not by any target.

### Verdicts
- **Target 1 (`J♯`, `_basic`): PASS.** `STtailTD > 0` (`W^{-D} > 0`, `W ≥ 1`), `STLK2 ≥ 0`; `1 ≤ max 1 _`; `STLK2 ≤ J♯·T` from `le_sup'`, `div_le_iff`; `J♯ ≤ X` from `sup'_le`, `max_le`.
- **Targets 2a-2d (L1): PASS**, `C = 12, 18, 18, 21` (rows 6-9); the premises (`3 ≤ d`, `SizeTendsto`, `0<κ`, `|E| ≤ 2-κ`, `0 ≤ s`, `t<1`, eventual `(1-t)⁻¹ ≤ N`) hold at the instance. Note: `STLI` is list-based (`loopL`), so the loop modulus must be restated for the list word of length `ℓ` (`nl2_loop_sub` is stated for `Fin k`; the body goes through `nl2Word` of the zipped lists).
- **Target 3 (L2): PASS.** **Target 4: PASS** (`C₄ = 15+D`). **Target 5 (G): PASS** (rows 12-15; `cont_core` hypotheses `hcard`, `hpt` (= `PrecPT`, definitionally), `hΞ` (`cont_highProbAt_good`), `hlow`, `hclose` all supplied).
- No exponent fails to close; no hypothesis set is unsatisfiable; no missing input.

## (b) Script output (stage 1b) — Mon Oct  5 18:11:52 UTC 2026
Branch `t/T2198`; scratch files (not committed) live in the scratchpad `T2198/`; commands run in the worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2198`.
```
$ date -u
Mon Oct  5 18:10:34 UTC 2026
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2198 log --oneline -1 && git diff --stat main...t/T2198
9c319c0 T2198: S5-09a Induction/LemDecCalELip (J-sharp, Holder-1/2 in u, relative continuity, generic lift)
 RBM3D/Induction/LemDecCalELip.lean | 1365 ++++++++++++++++++++++++++++++++++++
 1 file changed, 1365 insertions(+)
$ lake build RBM3D.Induction.LemDecCalELip 2>&1 | tail -1   # (the uncached run printed: ✔ [3779/3779] Built RBM3D.Induction.LemDecCalELip (8.0s))
Build completed successfully (3779 jobs).
$ lake build 2>&1 | tail -1   # full library; the new module is not yet imported by RBM3D.lean (the hub adds the root import at merge)
Build completed successfully (4000 jobs).
$ lake env lean scratch/registry.lean   # import RBM3D; import RBM3D.Induction.LemDecCalELip; #assert_rbm_axioms; echo exit=$?
exit=0
axiom audit: 5771 theorems, 2055 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
lines of that output mentioning LemDecCalELip: 0
$ grep -c 'sorry\|admit\|native_decide\|axiom' RBM3D/Induction/LemDecCalELip.lean   # in the T2198 worktree
0
$ lake env lean scratch/axioms.lean > axioms.out   # `#print axioms` of the 24 new public declarations; then:
$ grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' axioms.out; grep -vc 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' axioms.out
24
0
$ sed -n "s/^'RBM.Gauss.Sizes.\(LemDecCalELip_[A-Za-z0-9_]*\)' depends.*/\1/p" axioms.out | paste -sd' ' - | fold -s -w 150   # the 24 names
LemDecCalELip_STLI_norm LemDecCalELip_STLI_sub LemDecCalELip_Lloop_eq_STLI LemDecCalELip_Lloop_norm LemDecCalELip_Lloop_sub 
LemDecCalELip_STKloop_two_norm LemDecCalELip_STKloop_two_sub LemDecCalELip_LK_sub LemDecCalELip_LK2_sub LemDecCalELip_LK_norm LemDecCalELip_ELKLK_sub 
LemDecCalELip_EGt_sub LemDecCalELip_ee_sub LemDecCalELip_env LemDecCalELip_LK2 LemDecCalELip_ELKLK LemDecCalELip_EGt LemDecCalELip_ee 
LemDecCalELip_relcont LemDecCalELip_Jsharp LemDecCalELip_tail_pos LemDecCalELip_Jsharp_basic LemDecCalELip_Jsharp_rel LemDecCalELip_lift
$ lake env lean scratch/pincheck.lean; echo exit=$?   # section 1+2 of docs/tickets/checks/T2198-check.lean verbatim + the 8 lines below (RBM.Gauss.Sizes. stripped here)
exit=0
example : LemDecCalELip_Jsharp_basic_pin := @LemDecCalELip_Jsharp_basic
example : LemDecCalELip_LK2_pin := @LemDecCalELip_LK2
example : LemDecCalELip_ELKLK_pin := @LemDecCalELip_ELKLK
example : LemDecCalELip_EGt_pin := @LemDecCalELip_EGt
example : LemDecCalELip_ee_pin := @LemDecCalELip_ee
example : LemDecCalELip_relcont_pin := @LemDecCalELip_relcont
example : LemDecCalELip_Jsharp_rel_pin := @LemDecCalELip_Jsharp_rel
example : LemDecCalELip_lift_pin := @LemDecCalELip_lift
$ python3 scratch/jdiff.py | tail -1   # body of LemDecCalELip_Jsharp vs LemDecCalELip_Jsharp_voc (check file section 1), whitespace-normalised, name stripped
signature equal: True  body equal: True
$ lake env lean scratch/inst2a.lean; echo exit=$?   # the statement of the third example of check-file section 4 (verbatim, as a def) := instance (a) of 2a
exit=0
$ python3 scratch/extract.py stmts   # the def and the 8 target statements, extracted from the file (docstrings stripped, whitespace collapsed)
noncomputable def LemDecCalELip_Jsharp {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) : ℝ := max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _
  => 0)), Finset.mem_univ _⟩ (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) => STLK2 sz n (E n) u p.1 p.2 ω / STtailTD sz n u D p.2))
theorem LemDecCalELip_Jsharp_basic {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) : 1 ≤ LemDecCalELip_Jsharp sz E D n u ω ∧ (∀ (σ : Fin 2 →
  Bool) (a : Fin 2 → Zd d (sz.L n)), STLK2 sz n (E n) u σ a ω ≤ LemDecCalELip_Jsharp sz E D n u ω * STtailTD sz n u D a) ∧ ∀ X : ℝ, 1 ≤ X → (∀ (σ : Fin 2 → Bool) (a : Fin
  2 → Zd d (sz.L n)), STLK2 sz n (E n) u σ a ω ≤ X * STtailTD sz n u D a) → LemDecCalELip_Jsharp sz E D n u ω ≤ X := by
theorem LemDecCalELip_LK2 (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d) (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n) (ht : ∀
  n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ (u u' : TimeIcc s
  t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), |STLK2 sz n (E n) (u : ℝ) σ a ω - STLK2 sz n (E n) (u' : ℝ) σ a ω| ≤ ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ)
  - (u' : ℝ)| := by
theorem LemDecCalELip_ELKLK (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d) (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n) (ht :
  ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ (u u' : TimeIcc
  s t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLK sz n (E n) (u : ℝ) σ a ω - STELKLK sz n (E n) (u' : ℝ) σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt
  |(u : ℝ) - (u' : ℝ)| := by
theorem LemDecCalELip_EGt (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d) (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n) (ht : ∀
  n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ (u u' : TimeIcc s
  t n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGt sz n (E n) (u : ℝ) σ a ω - STEGt sz n (E n) (u' : ℝ) σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ)
  - (u' : ℝ)| := by
theorem LemDecCalELip_ee (sz : Sizes d) (E s t : ℕ → ℝ) (κ : ℝ) (_hd : 3 ≤ d) (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs : ∀ n, 0 ≤ s n) (ht : ∀
  n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ (u u' : TimeIcc s
  t n) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)), ‖STee sz n (E n) (u : ℝ) ω σ a a' - STee sz n (E n) (u' : ℝ) ω σ a a'‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt
  |(u : ℝ) - (u' : ℝ)| := by
theorem LemDecCalELip_relcont (sz : Sizes d) (n : ℕ) (t u u' D : ℝ) (a : Fin 2 → Zd d (sz.L n)) (ht : t < 1) (hut : u ≤ t) (hu't : u' ≤ t) : (1 - u')⁻¹ ≤ (1 + (1 - t)⁻¹ *
  |u - u'|) * (1 - u)⁻¹ ∧ (((sz.W n : ℕ) : ℝ) ^ d * |1 - u'|)⁻¹ ≤ (1 + (1 - t)⁻¹ * |u - u'|) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ∧ (((sz.W n : ℕ) : ℝ) ^ d * |1 -
  u'|)⁻¹ ^ (1 / 2 : ℝ) ≤ (1 + (1 - t)⁻¹ * |u - u'|) * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) ∧ STtailTD sz n u' D a ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 2 *
  STtailTD sz n u D a ∧ STtailTD sz n u' D a ^ 2 ≤ (1 + (1 - t)⁻¹ * |u - u'|) ^ 4 * STtailTD sz n u D a ^ 2 := by
theorem LemDecCalELip_Jsharp_rel (sz : Sizes d) (E s t : ℕ → ℝ) (κ D : ℝ) (hd : 3 ≤ d) (hsize : sz.SizeTendsto) (hκ : 0 < κ) (hD : 0 < D) (hE : ∀ n, |E n| ≤ 2 - κ) (hs :
  ∀ n, 0 ≤ s n) (ht : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz
  n, ∀ u u' : TimeIcc s t n, LemDecCalELip_Jsharp sz E D n (u' : ℝ) ω ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * LemDecCalELip_Jsharp sz E D n
  (u : ℝ) ω := by
theorem LemDecCalELip_lift {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (V : ℕ → Type) [∀ n, Fintype (V n)] (ξ : ∀ n, TimeIcc s t n × V n → sz.SeqΩ → ℝ) (J : ℕ → ℝ → sz.SeqΩ → ℝ)
  (R₀ R : ∀ n, TimeIcc s t n × V n → ℝ) (m Cv C CR : ℝ) : sz.SizeTendsto → (∀ n, s n ≤ t n) → (∀ n, t n - s n ≤ 1) → 0 ≤ m → (∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤
  ((sz.size n : ℕ) : ℝ) ^ Cv) → (∀ n u ω, 1 ≤ J n u ω) → (∀ n p, 0 ≤ R₀ n p) → (∀ᶠ n in atTop, ∀ p, ((sz.size n : ℕ) : ℝ) ^ (-CR) ≤ R n p) → (∀ᶠ n in atTop, ∀ (u u' :
  TimeIcc s t n) (v : V n), R₀ n (u', v) ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * R₀ n (u, v) ∧ R n (u', v) ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C *
  Real.sqrt |(u : ℝ) - (u' : ℝ)|) * R n (u, v)) → (∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz n, ∀ u u' : TimeIcc s t n, (∀ v : V n, |ξ n (u, v) ω - ξ n (u',
  v) ω| ≤ ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) ∧ J n (u' : ℝ) ω ≤ (1 + ((sz.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * J n (u : ℝ) ω)
  → PrecPT sz (U := fun n => TimeIcc s t n × V n) ξ (fun n p ω => R₀ n p + J n (p.1 : ℝ) ω ^ m * R n p) → Prec sz (U := fun n => TimeIcc s t n × V n) ξ (fun n p ω => R₀ n
  p + J n (p.1 : ℝ) ω ^ m * R n p) := by
$ python3 scratch/extract.py inst   # the compiled instances (a)-(d) and the instance of target 4, extracted from section 8 of the file (docstrings stripped)
private theorem lemDecCalELip_inst_tN (n : ℕ) : (1 - tInst n)⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) := by …
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n, ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
  |STLK2 sz0 n (1 / 2) (u : ℝ) σ a ω - STLK2 sz0 n (1 / 2) (u' : ℝ) σ a ω| ≤ ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := LemDecCalELip_LK2 sz0 (fun _
  => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst]) (Eventually.of_forall
  lemDecCalELip_inst_tN)
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n, ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
  ‖STELKLK sz0 n (1 / 2) (u : ℝ) σ a ω - STELKLK sz0 n (1 / 2) (u' : ℝ) σ a ω‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := LemDecCalELip_ELKLK sz0
  (fun _ => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst]) (Eventually.of_forall
  lemDecCalELip_inst_tN)
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n, ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
  ‖STEGt sz0 n (1 / 2) (u : ℝ) σ a ω - STEGt sz0 n (1 / 2) (u' : ℝ) σ a ω‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := LemDecCalELip_EGt sz0 (fun _
  => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst]) (Eventually.of_forall
  lemDecCalELip_inst_tN)
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n, ∀ (u u' : TimeIcc sInst tInst n) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd 3 (sz0.L n)),
  ‖STee sz0 n (1 / 2) (u : ℝ) ω σ a a' - STee sz0 n (1 / 2) (u' : ℝ) ω σ a a'‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)| := LemDecCalELip_ee sz0 (fun
  _ => 1 / 2) sInst tInst 1 (by norm_num) sz0_tendsto one_pos (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst]) (Eventually.of_forall
  lemDecCalELip_inst_tN)
example := LemDecCalELip_relcont sz0 1 (1 / 16) 0 (1 / 16) 42 (fun _ => 0) (by norm_num) (by norm_num) le_rfl
example := LemDecCalELip_Jsharp_basic sz0 (fun _ => 1 / 2) 42 1 0 (fun _ => 0)
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ ω ∈ RBM.Ind.ContinuityNet.contGood sz0 n, ∀ u u' : TimeIcc sInst tInst n, LemDecCalELip_Jsharp sz0 (fun _ => 1 / 2) 42 n (u' :
  ℝ) ω ≤ (1 + ((sz0.size n : ℕ) : ℝ) ^ C * Real.sqrt |(u : ℝ) - (u' : ℝ)|) * LemDecCalELip_Jsharp sz0 (fun _ => 1 / 2) 42 n (u : ℝ) ω := LemDecCalELip_Jsharp_rel sz0 (fun
  _ => 1 / 2) sInst tInst 1 42 (by norm_num) sz0_tendsto one_pos (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [tInst])
  (Eventually.of_forall lemDecCalELip_inst_tN)
example : Prec sz0 (U := fun n => TimeIcc sInst tInst n × Unit) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => 0 + (1 : ℝ) ^ (2 : ℝ) * 1) := LemDecCalELip_lift sz0 sInst tInst (fun
  _ => Unit) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (fun _ _ => (1 : ℝ)) 2 0 0 0 sz0_tendsto (fun _ => by norm_num [sInst, tInst]) (fun _ =>
  by norm_num [sInst, tInst]) (by norm_num) (Eventually.of_forall fun n => by simp) (fun _ _ _ => le_rfl) (fun _ _ => le_rfl) (Eventually.of_forall fun n p => by simp)
  (Eventually.of_forall fun n u u' v => ⟨by simp, by simp⟩) (Eventually.of_forall fun n ω _ u u' => ⟨fun v => by simp, by simp⟩) (precPT_of_le sz0 (fun n p ω => by
  norm_num) (fun n p ω => by norm_num))
$ grep -rln 'LemDecCalELip\|lemDecCalELip' RBM3D   # name-clash grep: T2198 worktree, files other than the new one; then the same in the main worktree
(T2198 worktree: no other file); main worktree RBM3D/: 0 files
$ grep -n 'NetLift2:\|LemDecCalE.lean' RBM3D/Induction/LemDecCalELip.lean | cut -c1-150   # cited sources of the copied helpers
18:(cited `NetLift2:line`) and one application of the merged `ContinuityNet.cont_core`.
51:`nl2Word`, `NetLift2:52`. -/
57:/-- The word of a cons; copy of `nl2Word_cons`, `NetLift2:58`. -/
63:/-- The word is bounded by `Q^length`; copy of `nl2_word_norm`, `NetLift2:64`. -/
80:/-- The `k`-fold telescoping of a resolvent word; copy of `nl2_word_diff`, `NetLift2:83`. -/
142:(`NetLift2:136`), stated for the trace of the word of an arbitrary list (the list loops `STLI`,
223:`‖𝓛_I(u) - 𝓛_I(u')‖ ≤ 3 k N^{2k+7} √|u-u'|`, `k = |I|`; (`nl2_loop_sub`, `NetLift2:136`, with
311:`lemDecCalE_STKloop_two`, `Path/LemDecCalE.lean:1276`. -/
734:`nl2_eta_inv_le`, `NetLift2:203`). -/
$ lake env lean scratch/mathlibnames.lean; echo exit=$?   # 53 `#check @name` lines, the names of section (c)
exit=0
$ lake env lean scratch/absent.lean   # #check @Real.rpow_le_rpow_of_exponent_nonpos
absent.lean:2:8: error(lean.unknownIdentifier): Unknown constant `Real.rpow_le_rpow_of_exponent_nonpos`
```

### Narrative (stage 1b)
- One new file `RBM3D/Induction/LemDecCalELip.lean` (1365 lines), namespace `RBM.Gauss.Sizes`; `Test/Axioms.lean` untouched: no new `Prop`, `LemDecCalELip_Jsharp` is real-valued, every pin is inline.
- Layout: §1 loops in the `L²` operator norm (word telescoping, any list length); §2 `𝒦^{(2)}` in the `ℓ^∞→ℓ^∞` norm (separate section, `Matrix.Norms.Operator`); §3 the four functionals (deterministic);
  §4 (L1) eventual assembly; §5 (L2); §6 `J♯`; §7 (G) via `cont_core`; §8 instances.  The two operator norms never meet in one statement: every public statement is about `ℂ`-norms.
- Copies (merged RBM3D `Path/NetLift2.lean`, itself a port of RBM2D `NetLift` at `c9a24cf`): `nl2Word` `:52`, `nl2Word_cons` `:58`, `nl2_word_norm` `:64`, `nl2_word_diff` `:83`, `nl2_loop_sub` `:136` (restated for the trace of the
  word of an arbitrary list, so that `STLI` and the 6-loop `STeeLoop` are covered), `nl2_eta_inv_le` `:203`, `#Vtx = N` and `‖blockMat X‖ ≤ 2N²` (`nl2_avg_close` `:457-464`), `lemDecCalE_STKloop_two` (`Path/LemDecCalE.lean:1276`).
  Pattern only (not copied): `step2LocalNetLift` `:586-622`.  Not needed: `nl2_STGM_eq`, `nl2_entry_diff`, `nl2_entry_le`, `nl2_loc_close` (they concern `STGM` entries) and `nl2_eventual` (the fixed mesh `A = 40`).  No RBM1D/RBM2D file was read or written, so no diff-stat applies.
- Private helpers carry the prefix `lemDecCalELip_`; public helpers `LemDecCalELip_*`: `STLI_norm/_sub` (any loop), `Lloop_eq_STLI/_norm/_sub` (any `k`), `STKloop_two_norm/_sub`, `LK_sub/_norm`, `LK2_sub`, `ELKLK_sub`, `EGt_sub`, `ee_sub`
  (deterministic, `N` a real with `N = size`), `env` (the eventual facts `M ≤ N`, `1 ≤ N`, `|E_n| < 2`, `(η_t)⁻¹ ≤ N²`, `(1-t)⁻¹ ≤ N`; intended for S5-13, `STEEk`) and `tail_pos`.
- Constants as in (a) rows 6-9, 11, 12: witnesses `7N^{11}`, `28N^{17}`, `42N^{17}`, `36N^{20}` absorbed at `N ≥ 7, 28, 42, 36` (`lemDecCalELip_absorb`), so `C = 12, 18, 18, 21`; target 4 has `C = 15 + D`; (G) has the mesh `A = 2(|C|+|CR|)+2`.
- Differences from (a) (no verdict changes, no (a′)): in the Lean chain of target 4, `STLK2(u') ≤ STLK2(u) + 7N^{11}x`, `ρ² ≤ 1 + 3N²x`, `ρ² + 7N^{11}N^D x ≤ 1 + 10N^{11}N^D x ≤ 1 + N^{15}N^D x` (`N⁴ ≥ 10`),
  i.e. (a)'s chain with `7N^{11}` for `N^{12}`, the same `C₄ = 15 + D`; the hypothesis `3 ≤ d` is used only as `1 ≤ d` (`W ≤ (W L)^d`) in target 4 (`_hd` elsewhere).  In (G): `C, CR, Cv` are arbitrary reals (`|C|`, `|CR|`, `max Cv 0`),
  `δ = N^C N^{-A/2} ≤ N^{-|CR|-1} ≤ min(N^{-CR}, N⁻¹)`, and `(1+δ)^{m+1} ≤ 2` for `N ≥ 2(m+1)` (`1+δ ≤ e^δ`, `e^y ≤ 1/(1-y)`).
- Instances (script output above): (a) 2a-2d at `sz0`, `E ≡ 1/2`, `κ = 1`, `sInst`, `tInst`, premise `(1 - 1/16)⁻¹ = 16/15 ≤ N_n` for every `n` (`N_n ≥ 4`); 2a's statement is the third example of check-file section 4 (`inst2a.lean`, exit 0);
  (b) target 3 at `n = 1`, `t = 1/16`, `u = 0`, `u' = 1/16`, `D = 42`; (c) target 1 at `sz0`; target 4 at `D = 42`; (d) target 5 with `V = Unit`, `ξ ≡ 0`, `J ≡ 1`, `R₀ ≡ 0`, `R ≡ 1`, `m = 2`, `PrecPT` by `precPT_of_le` (the ticket's data; trivial as a statement of `Prec`).

## (c) Verified Mathlib names used (53; each compiles under `#check @name`, script `mathlibnames.lean`, exit 0 above; `zero_le` is written `_root_.zero_le` in the file)
- `Finset.le_sup'` `Finset.sup'_le` `le_max_left` `le_max_right` `max_le` `div_le_iff₀`
- `Real.rpow_pos_of_pos` `Real.rpow_natCast` `Real.rpow_add` `Real.rpow_neg` `Real.rpow_neg_one` `Real.rpow_le_rpow`
- `Real.rpow_le_rpow_of_exponent_le` `Real.rpow_le_rpow_of_nonpos` `Real.one_le_rpow` `Real.mul_rpow` `Real.rpow_nonneg` `Real.rpow_one`
- `Real.sqrt_le_one` `Real.mul_self_sqrt` `Real.sqrt_nonneg` `Real.exp_pos` `Real.add_one_le_exp` `Real.exp_mul`
- `Real.exp_bound_div_one_sub_of_interval` `Matrix.linfty_opNorm_def` `Matrix.trace_sub` `Matrix.smul_apply` `Finset.single_le_sum` `Finset.le_sup`
- `Finset.sum_sub_distrib` `Finset.sum_le_sum` `Finset.sum_const` `Finset.card_univ` `norm_sum_le` `abs_norm_sub_norm_le`
- `norm_sub_le` `norm_add_le` `norm_mul_le` `Nat.le_self_pow` `Nat.le_mul_of_pos_right` `inv_anti₀`
- `inv_le_one_of_one_le₀` `one_le_pow₀` `pow_le_pow_right₀` `pow_le_pow_left₀` `List.ofFn_succ` `nsmul_eq_mul`
- `Complex.norm_natCast` `Complex.norm_real` `Complex.norm_conj` `Complex.conj_im` `zero_le`
- Verified absent: `Real.rpow_le_rpow_of_exponent_nonpos` (unknown constant; the name is `Real.rpow_le_rpow_of_nonpos : 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z`).

## (d) Open issues and paper-delta candidates
- No obstruction: all 8 targets and the def proved, no `sorry`; every pin matches its check-file body (script above); no pin, merged signature or `cont_core` was changed.
- Open for consumers: `STEEk` (S5-13) is not one of 2a-2d; its `𝓛`-factors are covered by the public loop helpers, but its deterministic `ζ` (`STprof`, `etaT⁻¹`, `STAI`) needs its own relative continuity (a note of (a), not a defect here).
  Instance (d) uses the ticket's trivial data; the non-trivial use of `LemDecCalELip_lift` is T2193 step (N).  The file has 1365 lines against the ticket's estimate of 600-900 (the four functionals and their sums are spelled out).
- `T2198a`: the Hölder-1/2 bounds, `J♯` and the lift work on `contGood` (every Gaussian coordinate `≤ N`, probability `≥ 1 - N^{-D}` by `cont_highProbAt_good`) and under the premise `(1-t_n)⁻¹ ≤ N` (eventually), in place of the paper's
  `‖H‖ ≤ N^C` w.h.p. and the standard `N^{-C}`-net (`1_2:1400`); the constants are explicit (`C = 12, 18, 18, 21, 15 + D`).
- `T2198b`: (G) is stated as `PrecPT(ξ ≺ R₀ + J^m R) → Prec(ξ ≺ R₀ + J^m R)` with `m ≥ 0`, deterministic `R₀ ≥ 0`, `R ≥ N^{-CR}`, relative continuity `1 + N^C√|u-u'|` of `R₀, R, J` and Hölder-1/2 of `ξ`; the ticket pins no paper statement for (G); I did not compare it with the paper text.
- `T2198c`: `LemDecCalELip_Jsharp := max(1, max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| / T_{u,D}(|a₁-a₂|))` is a realized random control at the single time `u` (supervisor 1.3), not the deterministic `J*` of `(eq:def_new_J*)`, `3_5:2310` (the ticket expects only `T2193c′` of `docs/tickets/T2193-amend-1.md`, which was not read here).
