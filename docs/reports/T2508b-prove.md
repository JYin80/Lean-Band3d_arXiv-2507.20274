Prover model: claude-sonnet-5-5
## (a) Math preflight — Wed Oct 14 14:52:48 UTC 2026 (row b: targets 9-12)

### (i) Exponent table
Row b only (`main` 57178a34, row a merged). Notation: `N=(WL)^d`, `x=1-u`, `Λ=lam²W^d`, `B=Bctl=W^-d(lam²+x)^-1+(Nx)^-1`, `G=Λ^(-1/5)`, `T=B²(G+B)`, `A=Aof κm`, `K=1/𝔠`, `C₀=6/𝔠` (band `ExpIntIQ:504-507`; `expIntIQ_ini` uses `C₀=3/𝔠`, `:660`), `D₂=D+1+K+1` (`:507`). Regime (i): `lam²/L²≤1-t≤1-s≤lam²`. Sources: band `Induction/QopDecay:340-757,762-880`, `Induction/ExpIntIQ:240-430,492-560,1104-1250`; `Chain/Step5KerGen:188,242`; `Defs/Tail:40-50`; `Defs/Params:32`; pin text `T2508_QopDecayGenOf` (`checks/T2508-check.lean:228-236`).
| # | quantity | value / form | constraint (source) | slack (instance of (ii)) |
|---|---|---|---|---|
| 1 | W-q: `ellT L g u` monotone in `g` (T9) | `ℓ_gK ≤ ℓ_lam` for `0<gK≤lam`; `ℓ=min(max(g/√(1-u),1),L)` (`Params:32`) | only `gK ≤ sz.lam` (ticket W-q); `1-u>0` | `ℓ_(lam/2)=1 ≤ ℓ_lam=1.0005` at `u=t` (ii) |
| 2 | W-q: far-term tail exponent (T9) | far pair `zdistD(b-a_i) ≥ W^(2ε)ℓ_lam/2`; `zdistD ≤ d·zdistInf` (`Lattice:71`, `Sizes:115`) ⇒ `r=zdistInf ≥ W^(2ε)ℓ_lam/(2d)`, `√(r/ℓ_gK) ≥ W^ε/√(2d)` | `c=1/√(2d)=0.4082` (d=3); the generic tail is `exp(-√(r/ℓ))` (`Tail:48`), not the band's `exp(-c r/ℓ)`: growth exponent is `ε` (band `2ε`) | `1291.3 ≥ 1291.0` (tight: `r₀` is the threshold) |
| 3 | W-q: `Bparam ≤ 2(1-t)⁻¹` (T9) | `(g²+|1-t|)⁻¹((r+1)^(d-2))⁻¹ + (L^d|1-t|)⁻¹ ≤ 2(1-t)⁻¹` | `g>0`, `d≥2`, `L≥1` | holds at `r₀`; far tail `≤ 2C₆W^K e^(-W^ε/√(2d))` |
| 4 | near term, row sum (T9) | `Σ_b‖θ‖ ≤ C₆/(1-u) ≤ C₆W^K`; `n·C₆W^(K-D) ≤ Z/2`, `Z=W^(-(D-(K+1)))=W·W^(K-D)` | `W ≥ 2nC₆` (band: constant 1); `C₆` fixed before `(sz,z)` (row 22), `W₀` after `C₆` (pin text order) | n=2: `4C₆ ≤ W₀`; `4000 ≪ 10^7` at `C₆=1000` |
| 5 | growth step (T9) | `2(n+1)·2C₆·W^p ≤ exp(W^ε/√(2d))`, `p=K+C₀+D-1`; `K=6, C₀=36, D=D₂=9` (`ε_IQ=1`, `D=1`) ⇒ `p=50`; output `(2ε, D-(K+1))=(1, 2)` | `W ≥ W₁`; `W ≥ 2^(1/ε)=4`, `W ≥ 2n=4` | `W₀=3.39e6` (`C₆`=1, 10), `3.47e6` (`C₆`=1000); at `W=10^7`: `ln(12 W^50)=808.4 ≤ 1291.0` |
| 6 | side conditions of T9/T10 | `K=1/𝔠=6`: `L^d ≤ N ≤ W^K`, `(1-u)⁻¹ ≤ W^K`; `C₀=36`: `N^6 ≤ W^C₀` (from `W ≥ N^𝔠`) | `Bandwidth 𝔠`, `WO 𝔡` (`Sizes:164-169`) | `log₁₀`: `N=41.86 ≤ 42`, `N^6=251.18 ≤ 252`, `L^d=20.86 ≤ 42` |
| 7 | `(1-v)⁻¹ ≤ N` (W-a, T10) | `(1-v)⁻¹ ≤ L²/lam² ≤ N` via `Λ ≥ 1`, `L² ≤ L^d` (`expIntIQ_inv_le`) | regime (i) lower end; `Λ=lam²W^d ≥ 1` | `log₁₀`: `27.91 ≤ 41.86` |
| 8 | W-a envelope of `f=E𝓛−𝒦` (T10) | `‖E𝓛‖ ≤ η⁻² ≤ N²κm⁻²` (`η=(1-u)Im m`, `κm ≤ Im m`, row 3; `ExpEtermsAGen_norm_L_le`); `‖𝒦^(2)‖ ≤ N^τ B ≤ 2N²` at τ=1 (row 17 `STKboundgL`, `B ≤ 2(1-u)⁻¹`); total `≤ N²κm⁻²+2N² ≤ N³` | `N ≥ κm⁻²+2` (=22.0); cap `W^C₀`, `N³ ≤ N^6 ≤ W^C₀` | `log₁₀`: `85.07 ≤ N³=125.59 ≤ W^36` (252) |
| 9 | W-a drift envelope `D_v` (T10) | `‖D_v‖ ≤ N·x⁻¹(B^(11/5)+B^(5/2)) ≤ N·N·2(2N)³=16N⁵ ≤ N^6`, from `STExpDriftHiConclgL` at τ=1 (hyps `hlk`,`hegt` as `ExpIntIGen:475`) | `N ≥ 16`, `B ≤ 2N`, `B^p ≤ (2N)³` for `p≤3` | `log₁₀`: `210.52 ≤ 251.18` |
| 10 | W-a cap | `‖f‖,‖D‖ ≤ W^C₀` with `C₀=6/𝔠`; `Cs=(1+40d)6^d=26136 ≤ N` (`expIntIQ_star_props`) | `N ≥ max(16,20,Cs,κm⁻²+2)`; `expIntIQ_ini`: `N³ ≤ W^(3/𝔠)=W^18` | `N=7.29e41`; `log₁₀ N³=125.59 ≤ 126` |
| 11 | W-b′ read by T11 (kernel ratio at `gK`) | `ρ=(gK²+1-s)/(gK²+1-v) ≤ 1+A ≤ 2A`, sum-zero branch `ρ² ≤ (1+A)² ≤ 4A²` (R1 `gK² ≤ lam² ≤ A gK²`, `1-s ≤ lam²`) | `A ≥ 1`, `0<gK ≤ 𝔡⁻¹` | A=1: `1.0005 ≤ 2`, widest `2.0000 ≤ 2`; A=4: `1.0008 ≤ 5`, widest `5.0000 ≤ 8` |
| 12 | rates (T11, `ϑ*`-bound) | `B^(11/5)+B^(5/2) ≤ (2^(1/5)+2^(1/2))T=2.563T ≤ 3T`; `B³ ≤ T`; total `≤ 4T`; needs `B ≤ 2/Λ` (`x ≥ lam²/L^d`, true in (i)) and `Λ ≥ 1` | `B^(1/2) ≤ √2 G` | `u=t`: `rates 8.73e-17 ≤ 4T=3.99e-16`; `u=1-lam²/L²`: `4.01e-16 ≤ 1.59e-15` |
| 13 | assembled constant, `log L` (T11) | `4A²·2·4 = 32A²`; `∫(1-v)⁻¹ = ln((1-s)/(1-u)) ≤ 2 ln L`; `32A² ln L ≤ N^(τ/2)` eventually | `N→∞` | A=4: `8.20e3 ≤ N^(1/2)=8.54e20`; `ln(1/ρ)=0.0010 ≤ 32.03`, widest = `2 ln L` (equal) |
| 14 | `(con_st_ind)`, `𝔠d` (T11, T12) | `𝔠d=1/300`, `d𝔠d=0.01<1`; `B_t^𝔠d ≤ (1-t)/(1-s)=ρ<1`; `W⁻¹ ≤ ρ` | `STConStInd` (`Induction/Defs:168`), `st_window` | `0.9455 ≤ 0.999` |
| 15 | row 9′ (T10) | `N^(-1+δ) ≤ 1-T0 ≤ 1-t`, `δ=ε/2=0.05`; only to shorten `η⁻¹` (row 7 + row 3 already close W-a) | `t ≤ T0` | `1-T0=lam²/L²`; `N^(-0.95)` ≪ that (scan below) |
| 16 | W-z (T10) | sum-zero and commutator of `A*_v` (5 pieces): algebraic, no constant; uses `ZeroModeGen_KerSums` (`B45Gen_Facts`, 19′) and `ϑ*` clause 1 `Σϑ=1`; `D_in` of the `θ`-step `D₂=D₁+K+1`, input `ε_IQ/2` | none numerical | n/a |

### (ii) One concrete nondegenerate instance
Family `W=10^k`, `L=⌊0.9W⌋`, `lam=1/W` (not a member of `sz0`: `L=4(n+1)` makes `W^(2ε)ℓ > d⌊L/2⌋` for `ε_IQ=1`, the window empty); instance `k=7`: `d=3`, `W=10^7`, `L=9·10^6`, `lam=10^-7`, `N=7.29e41`, `Λ=10^7`; `𝔠=1/6, 𝔡=κ=ε=1/10, 𝔠d=1/300`, `κm=√(2κ)/2=0.2236`; `1-s=lam²`, `1-t=ρ·lam²`, `ρ=0.999`; `gK=lam` (band, A=1; ThDecay is the merged theorem `step5KerGen_thDecay_band`, `Step5KerGen:242`, for all `sz,E` with `|E|≤2`) and `gK=lam/√A`, `A=4` (BA-shaped; discharge `baStep5KerGen_thDecay`, `BA/Step5KerBA:132`, at `BAflowLam0`; only the size inequalities are checked at A=4, not the pin). T9 hypotheses: `0<gK≤Λ_pin=𝔡⁻¹=10`, `gK≤lam`, `W₀≤W`, `L^d≤W^K`, `(1-u)⁻¹≤W^K`, `‖A‖≤W^C₀` (`A` = indicator of near pairs: norm 1, zero on far pairs), `EKFastDecay` at `ε=1/2`; window pair `a=(0,(x,x,x))`, `x=⌊L/2⌋` (nonempty, not collapsed). T10-12: `STFlow` data of rows 6-10 above, regime (i), R1, `(con_st_ind)`. Command (cwd `/`):
```
python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2508b/inst.py
k=7: d=3 W=1.0e+7 L=9.0e+6 lam=1.0e-7 N=7.29e+41 Lam=lam^2W^d=1.0e+7 K=6.0 C0=36.0 kappa_m=0.2236
   admissible W>=N^c                                              True
   WO W^(-d/2+dd)<=lam<=1/dd                                      True
   lam^2 W^d >= W^(2dd)                                           True
   L^d<=W^K, N<=W^K, N^6<=W^C0                                    True
   STReg5I                                                        True
   con_st_ind B_t^cd<=rho, 1/W<=rho, d*cd<1                       True
   R1+window+ratio A=1                                            True
   R1+window+ratio A=4                                            True
   log int ln((1-s)/(1-t))<=2 ln L                                True
   rates B^(11/5)+B^(5/2)<=3T, +B^3<=4T                           True
   32 A^2 ln L <= N^(1/2) (A=4)                                   True
   N>=max(20,16,Cs=26136,kam^-2+1)                                True
   row9prime N^(-1+delta)<=1-T0<=1-t                              True
   (1-v)^-1<=N at 1-v=lam^2/L^2; <=N^(1-delta) at 1-T0            True
   f<=N^2/kam^2+2N^2<=N^3<=W^C0                                   True
   D<=16N^5<=N^6<=W^C0                                            True
   QopDecay: ell_(lam/2)<=ell_lam, W^(2 eps)ell<=d*floor(L/2)     True
scan W=10^k, L=0.9W, lam=1/W, k=7..200: all checks hold for every k: True (failures: [])
--- QopDecayGen: n=2, eps_in=1/2 (output 2eps=1), K=6.0 C0=36.0 D_in=D2=9.0 p=K+C0+D-1=50.0, tail exponent W^eps/sqrt(2d)=W^(1/2)/2.4495
    C6=1    C=12     W0=max(W1,2^(1/eps),2n,2nC6)=3.389e+06  <= W=1e7: True ; at W=1e7: log C + p ln W = 808.4 <= W^eps/sqrt(2d) = 1291.0
    C6=10   C=120    W0=max(W1,2^(1/eps),2n,2nC6)=3.389e+06  <= W=1e7: True ; at W=1e7: log C + p ln W = 810.7 <= W^eps/sqrt(2d) = 1291.0
    C6=1000 C=12000  W0=max(W1,2^(1/eps),2n,2nC6)=3.468e+06  <= W=1e7: True ; at W=1e7: log C + p ln W = 815.3 <= W^eps/sqrt(2d) = 1291.0
--- tail: r0=W^(2eps) ell_lam/(2d)=1.6675e+06 <= diam_inf=floor(L/2)=4500000.0 ; sqrt(r0/ell_(lam/2))=1291.3 >= W^eps/sqrt(2d)=1291.0 ; Bparam(r0)<=2/(1-t): True
--- window pair: a=(0,(x,x,x)), x=floor(L/2)=4500000.0: zdistD=3x=13500000.0 >= W^(2eps)ell=1.0005e+07 ; (all other hypotheses: A=indicator of near pairs, ||A||=1<=W^C0, A=0 on the far pairs)
--- slacks (log10): N=41.8627 <= W^K=42.0 ; N^6=251.176 <= W^C0=252.0 ; L^d=20.8627 <= W^K ; (1-v)^-1 max L^2/lam^2=27.9085 <= N ; f<=85.0679 <= N^3=125.588 ; 16N^5=210.518 <= N^6=251.176
    Lam=1.0e+7 G=Lam^(-1/5)=0.0398 ; u=t: B=5.003e-08 <= 2/Lam=2.000e-07, 4T=3.985e-16 vs rates=8.730e-17 ; u=1-lam^2/L^2: B=1.000e-07, 4T=1.592e-15 vs rates=4.013e-16
    con_st_ind: B_t^cd=0.9455 <= rho=0.999 ; ln(1/rho)=0.0010 <= 2 ln L=32.03 ; widest window ln(L^2)=32.03 = 2 ln L ; Cs=(1+40d)6^d=26136
    A=1 gK=lam/sqrt(A): ratio(s..t)=1.0005 <= 1+A=2 <= 2A=2 ; widest window ratio=2.0000 ; 32A^2 ln L=5.124e+02 <= N^(1/2)=8.538e+20
    A=4 gK=lam/sqrt(A): ratio(s..t)=1.0008 <= 1+A=5 <= 2A=8 ; widest window ratio=5.0000 ; 32A^2 ln L=8.199e+03 <= N^(1/2)=8.538e+20
```
External hypotheses (TEAM §8 lesson 14): the pins `Step5KerGen_ThDecay` (row 22), `STKboundgL` (17), `IniTermGen_CltFlow` (9′), `B45Gen_Facts` (19′), `STEKSumRes2NALgL`, `STEKSumRes2gL`, `STExpDuhamelQgL`, `STExpLKLKHigL`, `STExpDriftDecaygL`, `STExpWardIgL'`, `STExpIniIgL'`, `STExpIntIgL'` (T12's premise list) stay hypotheses of the examples. The deterministic data they read are checked in the limit by the line "scan W=10^k, L=0.9W, lam=1/W, k=7..200: all 17 checks hold" (every k; `B_t^𝔠d → 0`, `N^𝔠=0.949W ≤ W`, `lam²W^d=W ≥ W^(2𝔡)`, `1-T0=lam²/L² ≥ N^(-0.95)`); `ThDecay` at `gK=lam` is the merged Lean theorem `step5KerGen_thDecay_band` (not a numerical claim).
Limits of the script: size-level inequalities at one family; it does not check Lean statements, the BA discharges, or the probabilistic pins. The explicit `W₀` of row 5 follows the band proof scheme with the sqrt tail; 1b may choose other constants.

### Verdict per target (row b)
- T9 `QopDecayGen_ThetaN_fastDecayg` (= `T2508_QopDecayGenOf`) and its `n=2` form: PASS (rows 1-6). W-q closes with `gK ≤ sz.lam` only (row 1) plus `Bparam ≤ 2/(1-t)` (row 3); the statement as pinned is true: `∃ W₀` after `C₆`, `W₀ ≥ 2nC₆` (row 4). Two points for 1b, neither changes the pin: the tail is `exp(-√(r/ℓ))`, so `c=1/√(2d)` and growth in `W^ε` (row 2); `zdistD ≤ d·zdistInf` is needed (only `zdistInf_le_zdistD` was seen in `Sizes:117`).
- T10 `expIntIQ_src_sumZerog`, `expIntIQ_src_decayg`, envelopes: PASS (rows 6-10, 15-16). W-a closes: row 7 and row 3 give `η⁻¹ ≤ N/κm` without row 9′; row 17 at τ=1 gives `‖𝒦^(2)‖ ≤ 2N²`. W-z: algebraic, no class beyond `QopAlgebra_ThetaN_sumZerog`, `_commutator_ThetaNg`, `_subg`.
- T11 `expIntIQ_inig`, `expIntIQ_star_boundg`, `expIntIQ_backg`, `expIntIQ_conclg`: PASS (rows 11-14; ratio `≤ 2A`, constant `32A²`, rates `≤ 4T`).
- T12 `stExpIntIgL'_of`: PASS (no new exponent; premises = `T2508_RowBOf`).
No row, layout or binding text changes; no watch item needs a class beyond its named text. 1a-audit needed: no. Overall verdict: PASS.
### (a′) Preflight corrections — Wed Oct 14 15:39:17 UTC 2026
Three points, none changes a verdict or a pin:
- Verdict T9 / row 2: `zdistD ≤ d·zdistInf` exists as `zdistD_le_mul_zdistInf` (`RBM3D/Defs/Sizes.lean:122`, used); (a) cites only `zdistInf_le_zdistD`.
- Row 5: 1b uses `c = 1/(2d)` (growth `4(n+1)C₆W^p ≤ exp(W^ε/(2d))`, `W₀ = max W₁ (max (2^(1/ε)) (2nC₆))`), not `1/√(2d)`; (a) allows other constants.
- Rows 8-9: `‖Θ^{(2)}f‖` is bounded through the row sums `K₆/(1-v)` of `B45Gen_Facts` (`B45_norm_ThetaN_leg`): `≤ 2K₆N⁴ ≤ N⁶` for `N ≥ 2K₆`; (a) has no `K₆` there.

## (b) Script output — Wed Oct 14 15:39:17 UTC 2026 (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2508b`, branch `t/T2508b`, from `main` 57178a34)
**(1) Sizes and commits; (2) builds, imports, importers**
```
$ git log --format="%h %s" 57178a34..HEAD | cut -c1-100; wc -l RBM3D/Chain/QopDecayGen.lean RBM3D/Chain/ExpIntIQGen.lean
b173ce5f T2508b: ExpIntIQGen: no ExpEtermsAGen import (private copy of the control lemma, band expIn
8c23f0ba T2508b: QopDecayGen instances for the n=2 form and the band re-derivation
84ea0943 T2508b: ExpIntIQGen band re-derivations, instances, docs; RBM3D.lean imports; registry (STE
2b53b4b2 T2508b: ExpIntIQGen core (targets 10-12): sum-zero, envelopes, decay, ini, star bound, asse
fafd24f3 T2508b: QopDecayGen (target 9, W-q): Theta^(n) decay propagation over the carrier
     341 RBM3D/Chain/QopDecayGen.lean
    1390 RBM3D/Chain/ExpIntIQGen.lean
    1731 total
$ lake build RBM3D.Chain.QopDecayGen RBM3D.Chain.ExpIntIQGen | tail -1
Build completed successfully (3959 jobs).
$ lake build | grep -E "axiom audit|premises found|^registry|Build completed" | cut -c1-175   # exit 0
info: RBM3D.lean:639:0: axiom audit: 15368 theorems, 4727 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 129 (borrowed 1, owed 56, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 122 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4409 jobs).
$ imports and importers
QopDecayGen: Chain.Step5KerGen Chain.Step2Gen Induction.QopDecay 
ExpIntIQGen: Chain.ExpIntIGen Chain.QopDecayGen Induction.ExpIntIQ Chain.ZeroModeGen Chain.B45Gen Chain.KDecayGen Chain.GridDuhamelGen 
import closure of ExpIntIQGen: 247 modules = planned layering imports (245) + ['RBM3D.Chain.ExpIntIQGen', 'RBM3D.Chain.QopDecayGen']; BA/* or Step2Kern in it: []
importers: RBM3D/Chain/ExpIntIQGen.lean RBM3D.lean 
$ #print axioms of the 15 public declarations (lake env lean ax.lean)
declarations printed: 15; with exactly [propext, Classical.choice, Quot.sound]: 15; with sorryAx: 0
QopDecayGen_ThetaN_fastDecayg QopDecayGen_ThetaN2_fastDecayg QopDecayGen_STthetaOp_fastDecay_band expIntIQ_src_sumZerog expIntIQ_f_leg expIntIQ_D_leg expIntIQ_src_decayg expIntIQ_inig expIntIQ_star_boundg expIntIQ_backg expIntIQ_conclg stExpIntIgL'_of ExpIntIQGen_stExpIntIgL'_band ExpIntIQGen_stExpIntI'_band ExpIntIQGen_stStep6I_of_LW_band 
```
**(3) Target statements, conclusions extracted by script** (`extract.py`: header of each declaration up to the top-level `:=`, text after its top-level `:`; hypotheses are in the files):
```
QopDecayGen_ThetaN_fastDecayg : ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ → ∀ k : ℕ, 0 < gK k → gK k ≤ Λ → gK k ≤ sz.lam k → W₀ ≤ ((sz.W k : ℕ) : ℝ) → ((sz.L k : ℕ) : ℝ) ^ d ≤ ((sz.W k : ℕ) : ℝ) ^ K → ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W k : ℕ) : ℝ) ^ K → ∀ (σ : Fin n → Bool) (A : (Fin n → Zd d (sz.L k)) → ℂ), ‖A‖ ≤ ((sz.W k : ℕ) : ℝ) ^ C₀ → EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) ε D A → EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (Step2Gen_ThetaN C k σ u A)
QopDecayGen_ThetaN2_fastDecayg : ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ → ∀ k : ℕ, 0 < gK k → gK k ≤ Λ → gK k ≤ sz.lam k → W₀ ≤ ((sz.W k : ℕ) : ℝ) → ((sz.L k : ℕ) : ℝ) ^ d ≤ ((sz.W k : ℕ) : ℝ) ^ K → ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W k : ℕ) : ℝ) ^ K → ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L k)) → ℂ), ‖A‖ ≤ ((sz.W k : ℕ) : ℝ) ^ C₀ → EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) ε D A → EKFastDecay (sz.lam k) u ((sz.W k : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (Step2Gen_ThetaN C k σ u A)
QopDecayGen_STthetaOp_fastDecay_band : ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λ → W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K → ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ), ‖A‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε D A → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (STthetaOp sz n E u σ A)
expIntIQ_src_sumZerog : EKSumZero (STExpQsrcg C μ n v σ (expIntIQ_star sz n))
expIntIQ_f_leg : (∀ᶠ n in atTop, ∀ v : ℝ, v ≤ t n → (1 - v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) ∧ (∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool, ‖(fun b => STExpErrg C μ n v σ b)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
expIntIQ_D_leg : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool, ‖fun b => STExpDriftg C μ n v σ b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 6
expIntIQ_src_decayg : ∀ᶠ n in atTop, ∀ v : ℝ, s n ≤ v → v ≤ t n → ∀ σ : Fin 2 → Bool, EKFastDecay (sz.lam n) v ((sz.W n : ℕ) : ℝ) ε' D (STExpQsrcg C μ n v σ (expIntIQ_star sz n))
expIntIQ_inig : PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖Step2Gen_UN C n p.2.1.1 (s n) (p.1 : ℝ) (STQop (d := d) (expIntIQ_star sz n) (s n) (fun b => STExpErrg C (law sz) n (s n) p.2.1.1 b)) p.2.2‖) (fun n p _ => F n p + sz.Bctl n (p.1 : ℝ) ^ 3)
expIntIQ_star_boundg : PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖STQop (d := d) (expIntIQ_star sz n) (p.1 : ℝ) (fun b => STExpErrg C (law sz) n (p.1 : ℝ) p.2.1.1 b) p.2.2‖) (fun n p _ => G n p + STExpTarget sz n (p.1 : ℝ))
expIntIQ_backg : PrecL sz μ (U := STIdx2P sz STSigMixed s t) (fun n p _ => ‖STQop (d := d) (ϑ n) (p.1 : ℝ) (fun b => STExpErrg C μ n (p.1 : ℝ) p.2.1.1 b) p.2.2‖) (fun n p _ => G n p + sz.Bctl n (p.1 : ℝ) ^ 3)
expIntIQ_conclg : STExpIntQConclgL' C (law sz) s t
stExpIntIgL'_of : STExpIntIgL' d law Flow mk T0
ExpIntIQGen_stExpIntIgL'_band : STExpIntIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
ExpIntIQGen_stExpIntI'_band : STExpIntI' d
ExpIntIQGen_stStep6I_of_LW_band : STStep6I d
```
**Pin diff** (scratch file outside the repo: the `T2508_*` texts of `docs/tickets/checks/T2508-check.lean` copied by script, plus the `example`s below; `lake env lean`):
```
example (d n : ℕ) : T2508_QopDecayGenOf d n := QopDecayGen_ThetaN_fastDecayg d n
example (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Ker : STEKKer d)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : T2508_RowBOf d law Flow mk T0 Ker gK Aof :=
  fun hBase hKerR1 hTh hB45 hSR hSR2 hDuQ =>
    stExpIntIgL'_of gK hBase.1 hBase.2.2.1 hBase.2.2.2.1 hBase.2.2.2.2 hSR hSR2 hKerR1.1 hKerR1.2 hTh hB45 hDuQ
example (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    T2508_ExpIntIgL' d law Flow mk T0 = STExpIntIgL' d law Flow mk T0 := rfl
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) :
    T2508_ExpIntQConclgL' C μ s t = STExpIntQConclgL' C μ s t := rfl
chk.lean: exit=0 errors=0
T2508-check.lean on this branch: exit=0 errors=0
```
**(4) Compiled nonempty instances** (`example`, `d = 3`, first line of each docstring; files at `c490c2e3`). Target 9 and `expIntIQ_src_decayg`: `sz0` (`L_k = 4(k+1)`, `W_k = (2(k+1))^5`), `bandFM`; the rest: `szB`/`zB`, `(s,t) = (7/8, 15/16)`, `bandFM`.
Note: `szB` (`L = 4`) collapses the decay window (`zdistD ≤ 6 < W^ε ℓ` once `W^ε > 6`), so it is not used for the decay instances.
```
$ python3 inst.py   # lists each `example` with the first 110 characters of its docstring
QopDecayGen.lean:392: Target 9, QopDecayGen_ThetaN_fastDecayg (n = 2) at sz0: the class Step5KerGen_ThDecay is the merged step5KerGe
QopDecayGen.lean:409: The n = 2 form QopDecayGen_ThetaN2_fastDecayg at the same data. -/
QopDecayGen.lean:426: The band re-derivation QopDecayGen_STthetaOp_fastDecay_band at the same data (E = 0): the band operator STthet
ExpIntIQGen.lean:1243: Target 10, expIntIQ_src_sumZerog at the band data: ZeroModeGen_KerSums is zeroModeGen_kerSums_band; no hypothe
ExpIntIQGen.lean:1248: Target 10, the envelopes expIntIQ_f_leg at the band data (no hypothesis) and expIntIQ_D_leg (the drift bounds 
ExpIntIQGen.lean:1253: (second example under the docstring above)
ExpIntIQGen.lean:1279: Target 10, expIntIQ_src_decayg along the band flow (sz0, z0) (L_n = 4(n+1) → ∞, W_n = (2(n+1))^5, lam_n = (2(n
ExpIntIQGen.lean:1311: Target 11, expIntIQ_inig at the band data (σ₁ ≠ σ₂, the family ϑ = ϑ*): the kernel pin stek_sumRes2gL_band, th
ExpIntIQGen.lean:1331: Target 11, expIntIQ_star_boundg at the band data (the family ϑ*): as expIntIQ_inig, with the 𝒬-Duhamel identit
ExpIntIQGen.lean:1360: Target 11, expIntIQ_backg at the band data (ϑ = ϑ*, G = T): the Ward conclusion and the bound on 𝒬*_u f_u stay
ExpIntIQGen.lean:1375: Target 11, expIntIQ_conclg at the band data: every deterministic premise is discharged; the drift bounds, the 
ExpIntIQGen.lean:1397: Target 12, stExpIntIgL'_of applied at the band tuple (ExpIntIQGen_stExpIntIgL'_band: every family premise by i
ExpIntIQGen.lean:1401: (second example under the docstring above)
ExpIntIQGen.lean:1407: The band re-derivations ExpIntIQGen_stExpIntI'_band, ExpIntIQGen_stStep6I_of_LW_band at d = 3, read at the dat
$ sed -n 392,408p RBM3D/Chain/QopDecayGen.lean   # target 9 (the n = 2 form and the band re-derivation, :409, :426, have the same statement shape)
example : ∃ k : ℕ,
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (1 / 10) 5 A) ∧
    (¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1)) A) ∧
    ∀ σ : Fin 2 → Bool,
    EKFastDecay (sz0.lam k) (1 / 2) ((sz0.W k : ℕ) : ℝ) (2 * (1 / 10)) (5 - (3 + 1))
      (Step2Gen_ThetaN (bandFM sz0 (fun _ => (0 : ℝ))) k σ (1 / 2)
        (fun a : Fin 2 → Zd 3 (sz0.L k) => if a = 0 then (1 : ℂ) else 0)) := by
  obtain ⟨C₆, hC₆, hTh⟩ := step5KerGen_thDecay_band 3 1 (by norm_num) one_pos
  obtain ⟨W₀, hW₀, H⟩ := QopDecayGen_ThetaN_fastDecayg 3 2 (by norm_num) 1 3 1 (1 / 10) 5 C₆ one_pos (by norm_num) hC₆
  obtain ⟨hW, hL, hK, hA, hAd⟩ := QopDecayGen_inst_data W₀
  obtain ⟨hl0, hl1⟩ := QopDecayGen_sz0_lam ⌈W₀⌉₊
  have hℓ := QopDecayGen_ellT_le_one (L := sz0.L ⌈W₀⌉₊) hl1 (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  exact ⟨⌈W₀⌉₊, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ, QopDecayGen_sz0_nontriv _ (by norm_num) (by norm_num) hℓ,
    fun σ => H sz0 (bandFM sz0 (fun _ => (0 : ℝ))) sz0.lam (hTh sz0 (fun _ => 0) (fun _ => by norm_num)) ⌈W₀⌉₊
      hl0 (by linarith) le_rfl hW hL (1 / 2) (by norm_num) (by norm_num) hK σ _ hA hAd⟩

/-- **The `n = 2` form** `QopDecayGen_ThetaN2_fastDecayg` at the same data. -/
$ sed -n 1279,1301p RBM3D/Chain/ExpIntIQGen.lean   # expIntIQ_src_decayg
example (hdr : STExpDriftHiConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) (fun _ => 1 / 16))
    (hdd : STExpDriftDecayConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) (fun _ => 1 / 16)) :
    (∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 16 → ∀ σ : Fin 2 → Bool,
      EKFastDecay (sz0.lam n) v ((sz0.W n : ℕ) : ℝ) (1 / 5) 1
        (STExpQsrcg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) n v σ (expIntIQ_star sz0 n))) ∧
    ∀ (n : ℕ) (v : ℝ), 0 ≤ v → v ≤ 1 / 16 →
      ¬ ∀ A : (Fin 2 → Zd 3 (sz0.L n)) → ℂ, EKFastDecay (sz0.lam n) v ((sz0.W n : ℕ) : ℝ) (1 / 5) 1 A := by
  obtain ⟨C₆, hC₆, hTh⟩ := step5KerGen_thDecay_band 3 (1 / 10 : ℝ)⁻¹ (by norm_num) (by norm_num)
  obtain ⟨K₆, hK₆, G⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  obtain ⟨-, -, -, -, hrow⟩ := G sz0 (1 / 10) (1 / 6) (1 / 10) z0 flow_z0
  refine ⟨expIntIQ_src_decayg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (by norm_num) sz0_admissible inferInstance hK₆
    (fun n σ σ' t ht0 ht1 a => (hrow n σ σ' t ht0 ht1).1 a) hC₆ sz0.lam
    (hTh sz0 (STflowE z0) (ExpIntIQGen_flowE_abs sz0 flow_z0)) (step34Gen_band_hg sz0_admissible) (fun n _ => le_rfl)
    (s := fun _ => 0) (t := fun _ => 1 / 16) (fun _ => le_rfl) (fun _ => by norm_num) ExpIntIQGen_sz0Env.1
    ExpIntIQGen_sz0Env.2
    (expIntIQ_D_leg (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) inferInstance sz0_tendsto (s := fun _ => 0)
      (t := fun _ => 1 / 16) (fun _ => by norm_num) hdr ExpIntIQGen_sz0Env.1) hdd (1 / 5) 1 (by norm_num) one_pos, ?_⟩
  intro n v hv0 hv1
  exact QopDecayGen_sz0_nontriv n (le_refl _) one_pos
    (QopDecayGen_ellT_le_one ((QopDecayGen_sz0_lam n).2) (by linarith))

/-- The kernel data at the band flow: `κm`, the class `STEKBandKer` at `gK = lam`, `0 < lam ≤ 𝔡⁻¹`, R1 at `Aof = 1` (merged `Step6KitGen_KerFR1_band`). -/
private theorem ExpIntIQGen_bandKer :
$ sed -n 321,322p RBM3D/Chain/QopDecayGen.lean   # the non-emptiness helper (far pair a = (0, (2(k+1),0,0)), QopDecayGen_sz0_far :293)
private theorem QopDecayGen_sz0_nontriv (k : ℕ) {ε g t D : ℝ} (hε : ε ≤ 1 / 5) (hD : 0 < D) (hℓ : ellT (sz0.L k) g t ≤ 1) :
    ¬ ∀ A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ, EKFastDecay g t ((sz0.W k : ℕ) : ℝ) ε D A := by
```
**(5) Registry and scan.** `RBM3D/Test/Axioms.lean`: the `owedProps` line of `STExpIntIgL'` (added by row a, owner T2508 row b) is removed, the line of `STExpIntIgL` now reads "superseded by `STExpIntIgL'` (T2508 row b, `stExpIntIgL'_of`, `Chain/ExpIntIQGen`); unprimed: no producer". Scan before (imports added, registry as merged), `full1.log`; after, `full4.log` (both builds exit 0):
```
before:
  RBM.BA.STExpIntIgL: 2 [no certificate]
  RBM.BA.STExpIntIgL': 7 [no certificate]
premises found by scanning: 129 (borrowed 1, owed 56, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 123 owed + 141 structural + 7 refuted + 19 superseded; 163 registered premise(s) carry nothing ye
after:
  RBM.BA.STExpIntIgL: 2 [no certificate]
premises found by scanning: 129 (borrowed 1, owed 56, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 122 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing ye
```
**(6) Greps** (name clash of the 15 new public names outside the two files; hypothesis rules; stop-rule counts):
```
$ <for each of the 15 names> grep -rlw --include='*.lean' -- NAME RBM3D RBM3D.lean | grep -v -e Chain/QopDecayGen -e Chain/ExpIntIQGen | sort | uniq -c
   1 RBM3D/Test/Axioms.lean
$ C1/X1-C1/V1L-C1/UBA token scan (`STFlow STflowE Ugen STthetaOp ThetaN d thetaKer d seqHflow STLKM STKloop Lloop lemT etaT mSigma seqP bandFM sz.Prec SB d |E|<2 STGridRepNgL STImproveExpAver st6_expAvgU_of_pin stImproveExpAver_holds hAvg : withLam`), non-comment lines, by section
QopDecayGen.lean: generic sections (lines 1-235): 0 hits; band re-derivation (lines 236-259): 5 hits; instances (lines 260-342): 6 hits
ExpIntIQGen.lean: generic sections (lines 1-1187): 0 hits; band re-derivation (lines 1188-1217): 5 hits; instances (lines 1218-1391): 49 hits
$ grep -nE '^(noncomputable )?(private )?(def|abbrev|structure|instance) ' <2 files>; grep -nE 'sorry|admit|^axiom|native_decide' <2 files>; grep -nE 'import RBM3D\.(BA|Chain\.Step2Kern)' <2 files>
(no output above = 0 hits)
$ grep -nE '∀ \(sz : Sizes d\)' <2 files> | grep -v 'variable\|{Flow\|{law' | cut -d: -f1,2 (U5S-C3: statement hits)
QopDecayGen.lean:74 QopDecayGen.lean:227 QopDecayGen.lean:241 ExpIntIQGen.lean:1136 ExpIntIQGen.lean:1143 ExpIntIQGen.lean:1145 ExpIntIQGen.lean:1147 ExpIntIQGen.lean:1150 
```
**(7) Band and merged files untouched; ports.**
```
       0
RBM3D.lean
RBM3D/Chain/ExpIntIQGen.lean
RBM3D/Chain/QopDecayGen.lean
RBM3D/Test/Axioms.lean
ports from ../RBM1D, ../RBM2D: none (no RBM1D/RBM2D diff-stat applies); every proof is a restatement of the RBM3D band files `Induction/QopDecay.lean`, `Induction/ExpIntIQ.lean` or new.
```
**Narrative** (all figures above are from the tool log; line numbers refer to the files at `b173ce5f`)
- Delivered: targets 9-12 as 15 public declarations: `QopDecayGen_ThetaN_fastDecayg`, `QopDecayGen_ThetaN2_fastDecayg`, band `QopDecayGen_STthetaOp_fastDecay_band` (target 9); `expIntIQ_src_sumZerog`, `expIntIQ_f_leg`, `expIntIQ_D_leg`, `expIntIQ_src_decayg` (target 10); `expIntIQ_inig`, `expIntIQ_star_boundg`, `expIntIQ_backg`, `expIntIQ_conclg` (target 11); `stExpIntIgL'_of` and the three `ExpIntIQGen_*_band` re-derivations (target 12). No `def`, `sorry`, `axiom`; one `set_option maxHeartbeats 400000` (target 9, commented).
- Sizes: 341 + 1,390 = 1,731 against bottom-up 300 + 1,385 = 1,685 (row stop 2,350, file stop 2,000). `wc -l` at the section commits: 330 (`fafd24f3`), 1,135 + 330 (`2b53b4b2`), 1,356 + 330 (`84ea0943`); final 1,390 + 341 (`b173ce5f`).
- Pins: `QopDecayGen_ThetaN_fastDecayg` is `T2508_QopDecayGenOf d n` and `stExpIntIgL'_of` is `T2508_RowBOf` curried (the unpacked premises of `T2508_FamBase`: law, `Step5CasesGen_FlowFacts`, `IniTermGen_CltFlow`, `STKboundgL`; its `Step2EventsGen_Flow` conjunct is not read, as in row a's `stExpWardIIgL_of`); `STExpIntIgL'`, `STExpIntQConclgL'` equal their `T2508_*` texts by `rfl`. No hypothesis added, removed or reordered against the pins.
- W-a: `expIntIQ_f_leg` returns `(1-v)⁻¹ ≤ N` and `‖f_v‖ ≤ N³` from row 9' (private copy `ExpIntIQGen_ctrl` of `ExpEtermsAGen_ctrl`, so `Chain/ExpEtermsAGen` is not imported: `κ' ≤ Im m`, `N^{-1+δ} ≤ 1-t`; the band's `expIntIQ_inv_le` is not needed), `CltRepg` (`ExpIniIGen_envelope`) and row 17 (`stKbound_timeIccgL` at `τ = 1`, `‖K‖ ≤ N B ≤ 2N²`); `expIntIQ_D_leg`: `‖D_v‖ ≤ 16N⁵ ≤ N⁶`. The band's `expIntIQ_theta_le`, `_expErr_le` are `B45_norm_ThetaN_leg` (row sums `K₆/(1-v)`, row 19') and `ExpIniIGen_envelope`, reused by name. No class beyond rows 9', 17, 19'.
- W-b': row a's `expIntI_kernel_unifg`, sum-zero branch (`STEKSumRes2gL`; window, decay class and ratio from R1): constants `4A²` (kernel), `8A²B³` (`expIntIQ_inig`), `32A²` with `log L` (`expIntIQ_star_boundg`), `A = Aof κm ≥ 1`; `A = 1` is the band value.
- W-q: `QopDecayGen_ThetaN_fastDecayg` reads `Step5KerGen_ThDecay` at `0 < gK k ≤ Λ` and `gK k ≤ sz.lam k` only (`QopDecayGen_ellT_mono`); the tail `𝒯_u = B_{u,r} exp(-√(r/ℓ))` gives the far term `2C₆(1-u)⁻¹ exp(-W^ε/(2d))`. No narrow gate, no `Probe/T2508Pins.lean`. W-z: algebraic (`QopAlgebra_ThetaN_sumZerog`, `_commutator_ThetaNg`, `QopAlgebra_Psum_Qop/_deriv`; `ZeroModeGen_KerSums` from row 19'). W-w: row a.
- UBA-C1 as used: `withLam` 0 hits; R1 enters only at `expIntI_kernel_unifg` (window, class, ratio) and, as `gK ≤ lam` through `Step5KerGen_cmp_pos`, at the W-q text; `gK` occurs in targets 9-11 and the pin (rows 16, 22).
- V1L-C1: no row-b statement reads `STExpAvgUgL`, `STImproveExpAvergL` or `st6_expAvgU_of_ping` (token scan, 0 hits in the generic sections); `ExpIntIQGen_stStep6I_of_LW_band` reuses row a's `ST_step6I_of_LW_Int_gen_band`, which recovers the global average through 16b. Average-input table: none in row b.
- Family table as used (file column): row 1 law, row 3 flow facts, row 8 `STExpDuhamelQgL` (`hDuQ` through `st6_duhEqQ_of_ping`), row 9' `IniTermGen_CltFlow`, row 16 `hKer` with R1 and the two `STEKSumRes2*gL`, row 17 `STKboundgL`, row 19' `B45Gen_Facts` (`KerSums`, `K₆`): all `ExpIntIQGen` (`stExpIntIgL'_of`); row 22 `Step5KerGen_ThDecay` (`∃ C₆` after `(𝔡, κ)`): `QopDecayGen`, `ExpIntIQGen`. Rows 2, 5, 19, 21, 23 are not read by row b.
- Greps: the single name-clash hit is the registry line of `STExpIntIgL` (a text mention of `stExpIntIgL'_of`). U5S-C3: the `∀ (sz : Sizes d)` hits of `stExpIntIgL'_of` (`gK`, `hKb`, `hKer`, `hTh`) are family rows 17, 16, 22; those of `QopDecayGen` are the carrier quantifier of the pinned text of target 9 and its two restatements. No hit of the token scan lies in a generic statement.
- Instances: every public declaration has an `example` at `szB`/`zB`, except target 9 and `expIntIQ_src_decayg`, whose examples are at `sz0` since the repair (see (4)). Left as hypotheses (other gates' pins): `STExpDriftHiConclgL`, `STExpDriftDecayConclgL`, `STExpWardIConclgL'` (T2506), the initial-term bounds `hF1`, `hG1` (`PrecL …`, T2506 row b) and `LWtermEXP 3`; everything else by merged band theorems (`iniTermGen_cltFlow_band`, `stKbound_holds`, `stek_sumRes2gL_band`, `step5KerGen_thDecay_band`, `b45Gen_facts_band`, `stExpDuhamelQ_holds`, `conStInd_const`, `szB_*`; for the `sz0` examples `iniTermGen_cltFlow_band`, `flow_z0`, `sixteenth_le_lemT`, `sz0_admissible`, `sz0_tendsto`).
- Name differences from the ticket text: the envelopes `expIntIQ_f_le`, `_D_le` are `expIntIQ_f_leg`, `expIntIQ_D_leg`; `_theta_le`, `_expErr_le` are not restated (reuse above); band `expIntIQ_src_sup`, `expIntIQ_integral_le` are `private` `ExpIntIQGen_src_sup`, `ExpIntIQGen_integral_le`.
## (c) Verified Mathlib names
65 names used by the two files, each `#check`ed by script (`lake env lean names.lean`: 0 errors, 0 unknown); `Real.le_sqrt_of_sq_le` (`Mathlib/Analysis/Real/Sqrt.lean:258`) is the one introduced here; none verified absent:
ContinuousOn.intervalIntegrable ContinuousOn.inv₀ ContinuousOn.mul Filter.Eventually.of_forall Filter.eventually_all Finset.card_univ Finset.sum_add_distrib Finset.sum_const Finset.sum_le_sum
Finset.sum_mul Fintype.card_fin Nat.cast_nonneg Nat.le_ceil Real.exp_add Real.exp_le_exp Real.exp_pos Real.le_sqrt_of_sq_le Real.log_nonneg Real.one_le_rpow Real.rpow_add Real.rpow_le_one
Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_neg_one Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos
Real.sqrt_nonneg Set.uIcc_of_le abs_of_pos div_le_div_iff₀ div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_le_iff₀ eventually_ge_atTop intervalIntegral.integral_const_mul
intervalIntegral.norm_integral_le_of_norm_le inv_anti₀ inv_le_one_of_one_le₀ inv_mul_cancel₀ inv_pow le_div_iff₀ le_mul_of_one_le_left le_mul_of_one_le_right max_le_max_right min_le_min_right
mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right norm_add_le norm_le_pi_norm norm_sub_le norm_sum_le one_div_le_one_div_of_le one_div_pos one_le_inv₀ one_le_mul_of_one_le_of_one_le one_le_pow₀
pi_norm_le_iff_of_nonneg pow_le_pow_left₀ pow_le_pow_right₀ tendsto_rpow_atTop
## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. The only Lean/paper statement difference touched is D725 (the Duhamel identity of the generic pin is eventual, so `STExpIntI'_of_gL'`, row a, is one-way), used by `ExpIntIQGen_stExpIntI'_band`; D727 is not touched.
- For the hub: `RBM3D.lean` (2 import lines after `RBM3D.Chain.ExpIntIGen`) and `RBM3D/Test/Axioms.lean` (1 line edited, 1 removed) are a union with T2509 at merge; row b needs no other file.
- No open issue changes a statement, an instance, the build, an axiom or a paper-delta.

## Repair (audit round 1, `T2508b-audit.md`) — Wed Oct 14 17:15:10 UTC 2026
Prover model: claude-opus-5-5 (repairer). Commit `c490c2e3` on `t/T2508b` (parent `b173ce5f`); only the two `.lean` files of row b changed.
```
$ lake build RBM3D.Chain.QopDecayGen RBM3D.Chain.ExpIntIQGen ; echo exit=$?
Build completed successfully (3959 jobs).
exit=0
$ grep -E "^(warning|error): RBM3D/Chain/(ExpIntIQGen|QopDecayGen)" build2.log | grep -vc "100 character"
0
$ lake env lean ax.lean   # #print axioms
'RBM.BA.QopDecayGen_ThetaN_fastDecayg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QopDecayGen_ThetaN2_fastDecayg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.QopDecayGen_STthetaOp_fastDecay_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.expIntIQ_src_decayg' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ wc -l RBM3D/Chain/QopDecayGen.lean RBM3D/Chain/ExpIntIQGen.lean   (file stop 2,000; row stop 2,350)
     443 RBM3D/Chain/QopDecayGen.lean
    1414 RBM3D/Chain/ExpIntIQGen.lean
    1857 total
$ git diff --stat b173ce5f c490c2e3
 RBM3D/Chain/ExpIntIQGen.lean |  56 ++++++++----
 RBM3D/Chain/QopDecayGen.lean | 198 ++++++++++++++++++++++++++++++++-----------
 2 files changed, 190 insertions(+), 64 deletions(-)
```
- Item 1 (target 9, three examples, now `QopDecayGen.lean:392`, `:409`, `:426`): data `sz0`, `bandFM sz0 (fun _ => 0)`, `gK = lam`, `Λ = 1`, `u = 1/2`, `K = 3`, `C₀ = 1`, `ε = 1/10`, `D = 5` (output `(1/5, 1)`), `k = ⌈W₀⌉₊`. Each example also proves that the input `(1/10, 5)` and the output `(1/5, 1)` conditions are not satisfied by every tensor at `k` (the negation of the audit's `aud_D1`/`aud_D2`), from the far pair `a = (0, (2(k+1),0,0))` with `W_k^{1/5} ℓ = 2(k+1) ≤ zdistD` (`QopDecayGen_sz0_far`, `ℓ_{1/2} ≤ 1` since `lam_k ≤ 1/2`).
- Item 2 (`expIntIQ_src_decayg`, now `ExpIntIQGen.lean:1279`): flow `(sz0, z0)` (`flow_z0`), window `[0, 1/16]`, `ε' = 1/5`, `D = 1`; envelopes by the new private `ExpIntIQGen_sz0Env` (`expIntIQ_f_leg` with `iniTermGen_cltFlow_band` at `(sz0, z0)` and `sixteenth_le_lemT`). The second conjunct proves, for every `n` and `v ∈ [0, 1/16]`, that the `(1/5, 1)` condition is not satisfied by every tensor (negation of `aud_D3` at `ε' = 1/5`). Hypotheses left: `STExpDriftHiConclgL`, `STExpDriftDecayConclgL` at `(sz0, z0, 0, 1/16)` (T2506 rows a, c).
- Item 3: (b)(4) replaced with the new script output and the `szB` note; the instance line of the narrative names the two `sz0` examples. No statement, hypothesis, pin text, registry or import line changed; new helpers are `private` with the file stem (`QopDecayGen_sz0_lam`, `_sz0_W`, `_ellT_le_one`, `_sz0_far`, `_sz0_nontriv`, `ExpIntIQGen_sz0Env`), so no new public name.
- Mathlib names added by the repair, `#check`ed by script (`lake env lean names.lean`: exit=0, errors=0, 15 checked): Real.pow_rpow_inv_natCast Real.rpow_lt_one_of_one_lt_of_neg ZMod.val_natCast Fin.sum_univ_three Nat.mod_eq_of_lt le_self_pow₀ Real.sqrt_sq Real.sqrt_le_sqrt div_le_one mul_le_mul neg_lt_zero max_le min_le_left Matrix.cons_val_one Matrix.cons_val_zero.

