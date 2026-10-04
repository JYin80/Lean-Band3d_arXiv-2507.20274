Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 19:51:46 UTC 2026

Notation: `g = ilambda`, `A = g²W^d`, `|x|_∞ = zdistInf`, `|x|_1 = zdistD`, `ρ = (log W)^4 ℓ_s`, `w = (log W)^3 ℓ_s`, `ℓ_s = ellT L g s`, `D = |a₁-a₂|_∞`,
`B_{b₁b₂} = 𝔼 STLKM(s)` (3_5:2139-2150), `Θ_{xy} = Θ(0,y-x)` (translation, `Theta_apply_add_right_of_three_le`). Scripts: `scratchpad/T2157/{pre,sums,inst,szcl}.py` (python, no Lean).

### (i) Exponent table
| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | exponent of `A` | `Bctl^{1/5}` gives `-1/5`, `W^{-d}B_{s,x}` gives `-1`; total `-6/5` | target `-6/5` (`STCltFarConcl`) | 0 (exact); all losses are `N^τ`, any `τ>0` |
| 2 | `Bctl = W^{-d}B_{s,0} ≤ 2/A` | `B_{s,0}=(g²+1-s)^{-1}+(L^d(1-s))^{-1} ≤ g^{-2}(1+L^{2-d})` | regime (i): `1-s ≥ 1-t ≥ g²/L²`, `L ≥ 3` | factor 2 (`1+L^{2-d} ≤ 4/3` at `d=3,L=3`) |
| 3 | `W^{-d}B_{s,x} ≤ (1+d^{d-2}) A^{-1}(|x|_1+1)^{-(d-2)}` (and `≤ 2A^{-1}(|x|_∞+1)^{-(d-2)}`) | zero-mode term `(L^d(1-s))^{-1} ≤ g^{-2}L^{2-d}`; `|x|_1+1 ≤ dL`, `|x|_∞+1 ≤ L` | `L ≥ 3` | script (sums.py): max ratio 0.6719 over 200000 samples |
| 4 | `(1-s)²g^{-4}ℓ_s^4 ≤ 1` | `ℓ_s ≤ g/√(1-s)` (since `1-s ≤ g²` gives `g/√(1-s) ≥ 1`) | `1-s ≤ g²` | 0 when `ℓ_s = g/√(1-s)` (script max `1.000000000000001`, rounding); `>0` if `ℓ_s = L` |
| 5 | window sum power | `Σ_{|r|≤w₁}|r|²/(|r|_∞^{d-2}+1) ≍ w₁^{d+2-(d-2)} = w₁^4`, all `d ≥ 3` | — | script: constant `6.13` at `w=32`, `d=3` |
| 6 | `b₁`-sum | `Σ_{b₁}(|a₁-b₁|_∞+1)^{-(d-2)}(|a₂-b₁|_∞+1)^{-d} ≤ C_d(1+log L)/(D^{d-2}+1)` | tail exponent `(d-2)+d=2d-2>d` (margin `d-2`); `|a₂-b₁|^{-d}` is critical at `a₂`: log | no slack: factor `1+log L` (paper's `≺`); script: `ratio` 8.8, 17.3, 27.4, 35.2, 44.9 at `L`=5, 9, 15, 21, 31 |
| 7 | BD2 premise `|r|_1 ≤ c|a|_1`, `r=b₁-b₂`, `a=a₂-b₁` | `|r|_1 ≤ d·w`, `|a|_1 ≥ |a|_∞ > ρ` | `d(log W)^3ℓ_s ≤ c(log W)^4ℓ_s`, `c=1/2`: `log W ≥ 2d` | `d=3`: `log W ≥ 6`, `W ≥ 404` (`log 404=6.0014`); at `szCL` `n=0`: `log W=16.64` (2.77×) |
| 8 | `Θ` pins used | `Prop5Decay d Λ` (const `C₅`), `Prop7Diff2 d Λ κ' 1/2` (const `C₇`), `Λ = 𝔡⁻¹ ≥ g` (WO), `‖ξ‖=t<1`, `‖m‖=1` | `κ' ≤ Im mE(E)`: `Im m = √(4-E²)/2 ≥ √(κ(4-κ))/2` for `|E| ≤ 2-κ`; `κ' = min(κ,1/2)` works | `κ(4-κ) ≥ 1` for `κ ∈ [0.27,3.73]`, `κ ≤ 0.8 ⇒ κ ≤ √(κ(4-κ))/2` |
| 9 | factors `(g²+|1-t|)^{-1}` | `≤ g^{-2}` in `Θ_{a₁b₁}` bound and in BD2 | — | `g^{-4}` exactly as `ilambda^{-4}` |
| 10 | `K'` term (beyond window) | `≤ 8C₅² L^{2d} K'`: `|Θ| ≤ C₅Bparam(0) ≤ 2C₅g^{-2}`, `(1-s)²g^{-4} ≤ 1` | caller makes `L^{2d}K' ≤ A^{-6/5}/(L^{d-2})`; with `L ≤ N ≤ W^{1/𝔠}`, `A ≤ 𝔡^{-2}W^d` it suffices `K' = W^{-D}`, `D ≥ 3d/𝔠+2d` | `d=3,𝔠=1/6`: `D ≥ 60` |
| 11 | beyond-window `≺` | `|x|_∞>w`: `exp(-(|x|/ℓ_s)^{1/2}) ≤ exp(-(log W)^{3/2})` | `(log W)^{3/2} ≥ D log W` eventually | super-polynomial |
| 12 | expectation of `≺` | `|𝓑| ≤ η_s^{-2}+|K^{(2)}|` a.s. (`norm_Lloop_le`, `|E|<2`, `s<1`; `STK2decay`), `η_s=(1-s)Im m(E)`, `1-s ≥ g²/L²`, `g ≥ W^{-d/2+𝔡}` (WO) | `(η^{-2}+|K|)·N^{-D'} ≤ A^{-6/5}` for `D'` large | polynomial in `N`, `D'` free |

### (i') The mathematics, as far as (ii) needs
(1) *Identity.* `B(a+c,b+c)=B(a,b)`, `B(a,b)=B(b,a)`. For `x=b₁-b₂`: `B(b₁,2b₁-b₂) = B(0,x)` (translate by `-b₁`) `= B(x,0)` (symmetry) `= B(b₁,b₂)` (translate by `b₂`). `b₂ ↦ 2b₁-b₂` is an involution of `Z_L^d`, so
`Σ_{b₂}B_{b₁b₂}(Θ_{b₂a₂}-Θ_{b₁a₂}) = ½Σ_{b₂}B_{b₁b₂}(Θ_{b₂a₂}+Θ_{2b₁-b₂,a₂}-2Θ_{b₁a₂})`. With `a=a₂-b₁`, `r=b₁-b₂`: `Θ_{b₂a₂}=Θ(0,a+r)`, `Θ_{2b₁-b₂,a₂}=Θ(0,a-r)`, `Θ_{b₁a₂}=Θ(0,a)`: exactly `Prop7Diff2`'s left side. In Lean `B` is `𝔼 STLKM`: `𝔼𝓛` translation invariant and reflection-invariant from `stExpInv_holds` (reflection + translation by `a₁+a₂` gives symmetry); `𝒦^{(2)}` from `KLK_two` (`W^{-d}m₁m₂Θ_{tm₁m₂}(a₁,a₂)`) with `Theta_apply_add_right_of_three_le`, `Theta_transpose_of_three_le`.
(2) *Summation* (`|B| ≤ K/(|x|_∞^{d-2}+1)` for `|x|_1 ≤ w₁`): `|𝔼f^{far}| ≤ (1-s)² Σ*_{b₁} 2C₅(1+d^{d-2})g^{-2}(|a₁-b₁|_∞+1)^{-(d-2)} · ½C₇g^{-2}Σ_{b₂}|B||r|_1²(|a₂-b₁|_∞+1)^{-d} + K'-term` (`(|·|_1+1)^{-k} ≤ (|·|_∞+1)^{-k}`). The `b₂`-sum is `≲ K w₁^4`; the `b₁`-sum is row 6; `(1-s)²g^{-4}ℓ_s^4 ≤ 1` is row 4. Result: `C_d C₅C₇ K (1+log L)(1-s)²g^{-4}w₁^4/(D^{d-2}+1)`. Differences from the ticket's `ℓ_s^4`: `w₁^4` (`w₁=d w`, i.e. extra `(log W)^{12}`) and `1+log L`; both are `≤ N^τ`.
(3) *Core design recommended.* Hypotheses on `Θ` in the core, not `Prop*` pins: `|Θ(0,x)| ≤ K_Θ(|x|_∞+1)^{-(d-2)}`, `|Δ²Θ(a;r)| ≤ K₂|r|_1²(|a|_∞+1)^{-d}` when `|r|_1 ≤ c|a|_1`, `|Θ| ≤ K_∞` (for `K'`); window in `ℓ¹`: `|b₁-b₂|_1 ≤ w₁` with hypothesis `w₁ ≤ c(ρ+1)`. The application uses `w₁ = d w` (`|x|_∞ ≤ w ⇒ |x|_1 ≤ dw`) and row 7. An `ℓ¹` window is what makes `L = 5, d = 3` nondegenerate: an `∞`-window needs `ρ ≥ d w/c` which exceeds `L/2` at `L=5`.
(4) *Exact form S5-25 needs* (`Step5Pins.lean:385-393`, `STCltFarConcl`): `Prec sz (U := {p : {σ // σ 0 ≠ σ 1} × (Fin 2 → Zd d (L n)) // ℓ_t ≥ (log W)^5ℓ_s ∧ |p.2 0 - p.2 1|_∞ ≤ ½(log W)^{3/2}ℓ_t+(log W)^{5/2}ℓ_s}) (‖STfFar …‖) (A^{-6/5}/(|p.2 0-p.2 1|_∞^{d-2}+1))`; `d-2` is a natural exponent. The mean bound needs neither index condition (`exp ≤ 1`, `D` arbitrary) and holds for all `σ₀≠σ₁`, all `a`; state `stMeanFar` as `Prec` on the same `U` with `ξ := ‖∫ ω, STfFar … ∂sz.seqP‖` (deterministic in `ω`) and the same `ζ`, so S5-25 adds it to the fluctuation bound without transport. `STfFar` uses `ξ=t·STmsig σ₀·STmsig σ₁ = t` (`σ₀≠σ₁`); integrability of `Lloop` from `walk_measurable_Lloop` and `norm_Lloop_le`. Inside the window `|𝔼𝓑_{b₁b₂}| ≲ N^τ A^{-6/5}/(|x|_∞^{d-2}+1)` comes from `STGdecayW` (`STStep2Concl`, `u=s`, factor `((1-s)/(1-s))^{C_d}=1`) with rows 2-3, 11-12; beyond it `≤ W^{-D}`.

### (ii) One concrete nondegenerate instance
**Core lemma**, `d=3`, `L=5`, `g=1/2`, `s=4/5`, `t=9/10` (regime (i): `g²/L²=1/100 ≤ 1-t=1/10`, `1-s=1/5 ≤ g²=1/4`, `s<t`), `ρ=1`, `w₁=1`, `c=1/2`, `ξ=t` (`σ₀≠σ₁`), `Θ=(1-tS^{(B)})^{-1}` (exact, `S^{(B)}` of `Defs/Block.lean:38`), `B(x)=K/(|x|_∞+1)` for `|x|_1 ≤ 1`, else `0` (`K'=0`; so `B(0)=K`, `B(±e_i)=K/2`): translation invariant, symmetric, nonzero (`K=1`). The `B=0` instance is `K=K'=0`, LHS `=0`.
```
$ python3 scratchpad/T2157/inst.py        (first 4 lines of its output)
window points |r|_1<=w1: 7 ; nonzero B values: [np.float64(0.5), np.float64(1.0)]
filter points b1 (a2=0): 98 ; BD2 premise |r|_1<=c|b1-a2|_1 on all (b1,r): True ; empirical C7= 2.4267 C5= 0.6324
ell_s=1.1180 (1-s)^2 g^-4 ell_s^4=1.000000; max_a1 |LHS|/(K(1-s)^2g^-4ell^4/(D+1))=0.0087; at a1=a2: LHS=4.105e-03 RHS=1.000e+00
B=0: LHS=0 trivially (K=K'=0)
```
(`S^{(B)}` row sums are asserted `=1` in the script; the filter set is nonempty and the LHS is nonzero.) Identity (1) and a larger-window check (`L=9,11`, windows `w=2,3`, `∞`-ball, no BD2 premise):
```
$ python3 scratchpad/T2157/pre.py
(9, 0.5, 0.8, 0.9, 1, 2) {'ell_s': 1.118, 'pref': 1.0, 'nonempty': True, 'max_abs_first_minus_half': 2.4868995751603507e-14, 'LHS_mean_over_RHS': 0.2421022344100283, 'no_cancel_over_RHS': 0.5464959250825807}
(9, 0.5, 0.8, 0.9, 1, 3) {'ell_s': 1.118, 'pref': 1.0, 'nonempty': True, 'max_abs_first_minus_half': 1.0302869668521453e-13, 'LHS_mean_over_RHS': 0.6082693158508444, 'no_cancel_over_RHS': 1.328744722226643}
(11, 0.7, 0.7, 0.85, 1, 3) {'ell_s': 1.278, 'pref': 1.0, 'nonempty': True, 'max_abs_first_minus_half': 4.263256414560601e-14, 'LHS_mean_over_RHS': 0.4029024138467058, 'no_cancel_over_RHS': 0.8310819682111028}
```
(`max_abs_first_minus_half` = identity (1); `LHS_mean_over_RHS` = `(1-s)²|Σ*Σ Θ B ½Δ²Θ|/(K(1-s)²g^{-4}ℓ_s^4/(D^{d-2}+1))`, max over `a₁`, `a₂=0`; at `w=3` the no-cancellation ratio exceeds 1, the second-difference form `0.61` does not.)
Rows 3, 4, 5, 6, 7 scripted:
```
$ python3 scratchpad/T2157/sums.py
(ii) L, max_a1 S*(D+1)  [rho=0], max with rho=1, log L
5 8.831 2.963 1.609
9 17.261 11.999 2.197
15 27.438 22.773 2.708
21 35.234 30.744 3.045
31 44.939 40.555 3.434
(ii) w, sum_{|r|inf<=w}|r|_inf^2/(|r|^{d-2}+1) / w^4
1 13.0
2 8.9792
4 7.3022
8 6.5878
16 6.2742
32 6.1314
max (1-s)^2 g^-4 ell_s^4 = 1.000000000000001 (<=1)
max Bparam/((1+d^(d-2)) g^-2 (K+1)^-(d-2)) = 0.6719 (<=1)
BD2 window: d*(log W)^3 l <= c (log W)^4 l with c=1/2 iff log W >= 2d = 6 ; W>= 404 log W= 6.0014
```
**Application `stMeanFar`**, `d=3`, the merged sequence `szCL` (`Step5Pins.lean:640-717`: `L=2(n+24)^5`, `W=2^{n+24}`, `lam=1`, `s=0`, `t=1-L^{-2}`, `zCL`, admissible by `szCL_admissible`); stochastic premises of `STIngR5` stay hypotheses (CLAUDE.md §4 step 2):
```
$ python3 scratchpad/T2157/szcl.py
 n=0: L=15925248 W=16777216 N=1.907e+43; regime(i) exact=True; log W=16.64>=2d=6:True; rho=(logW)^4 ell_s=76586 < L/2=7962624:True; d*w=d(logW)^3 ell_s=13811 <= rho/2=38293:True; (1-s)^2 lam^-4 ell_s^4=1.0; A=lam^2 W^d=4.722e+21; W>=N^(1/6):True
 n=1: L=19531250 W=33554432 N=2.815e+44; regime(i) exact=True; log W=17.33>=2d=6:True; rho=(logW)^4 ell_s=90170 < L/2=9765625:True; d*w=d(logW)^3 ell_s=15611 <= rho/2=45085:True; (1-s)^2 lam^-4 ell_s^4=1.0; A=lam^2 W^d=3.778e+22; W>=N^(1/6):True
 n=5: L=41022298 W=536870912 N=1.068e+49; regime(i) exact=True; log W=20.10>=2d=6:True; rho=(logW)^4 ell_s=163265 < L/2=20511149:True; d*w=d(logW)^3 ell_s=24366 <= rho/2=81633:True; (1-s)^2 lam^-4 ell_s^4=1.0; A=lam^2 W^d=1.547e+26; W>=N^(1/6):True
 n=20: L=329832448 W=17592186044416 N=1.954e+65; regime(i) exact=True; log W=30.50>=2d=6:True; rho=(logW)^4 ell_s=865192 < L/2=164916224:True; d*w=d(logW)^3 ell_s=85105 <= rho/2=432596:True; (1-s)^2 lam^-4 ell_s^4=1.0; A=lam^2 W^d=5.445e+39; W>=N^(1/6):True
```
`N` is large only because `szCL` is the merged sequence for which the far-index set (`ρ < L/2`) is nonempty (same data as `inst_cltFar`); the core lemma instance above is small. External hypotheses: none new. `Prop5Decay`, `Prop7Diff2` are proved (`prop5Decay_holds`, `prop7Diff2_holds`); the stochastic premises of `STIngR5` (`STGdecayW` etc.) are other gates' pins and stay hypotheses; their limit data are the `szCL` rows (`W ≥ N^{1/6}`, `lam=1 ≤ 𝔡⁻¹`).

### Verdicts
- Target 1 (deterministic core): **PASS** with the corrections `ℓ_s^4 → w₁^4` and a factor `1+log L` (paper-delta candidate `T2157a`: the paper's `≺` hides `(log W)^{12}` and `log`; the ticket's `C K (1-s)²ilambda^{-4}ℓ_s^4/(…)` is not literally true) and the `ℓ¹` window design (i')(3). BD2's premise is covered by `w₁ ≤ c(ρ+1)`, i.e. `log W ≥ 2d`; no obstruction.
- Target 2 (`stMeanFar`): **PASS**. No moment input is missing: a.s. envelope `norm_Lloop_le` plus the bad event of `STGdecayW` (rows 11-12). The merged `STExpInv` gives the invariance of `𝔼𝓛`, and `KLK_two` with `Theta` translation/symmetry gives that of `𝒦`.

## (a′) Preflight corrections — Sun Oct  4 21:14:09 UTC 2026
Verdicts PASS unchanged; four corrections of detail, none changes a statement of the targets.
1. Row 3 of (i): the zero-mode domination used is `zeroMode_le_of_ge` (`Defs/Tail.lean`), constant `1 + 2^{d-1}` with `|x|_∞`, not `1 + d^{d-2}` with `|x|_1`.
2. (i')(3): `w₁ ≤ c(ρ+1)` does not cover real `ρ` (`|a|_∞ > ρ` gives only `|a|_∞ ≥ ⌊ρ⌋₊+1`); the Lean hypothesis is `2 w₁ ≤ ⌊ρ⌋₊ + 1` (`meanFar_T2`, `c = 1/2`), at the core instance `ρ = w₁ = 1`.
3. Row 12 of (i): the a.s. envelope is `η_s^{-2} + ‖𝒦^{(2)}‖` with `‖𝒦^{(2)}‖ ≤ c₁/A` from `Prop5Decay` (`meanFar_n_K`); `STK2decay` is not used.
4. (i')(2): the Lean bound has `(|a₁-a₂|+1)^{-(d-2)}`; the form `(|a₁-a₂|^{d-2}+1)^{-1}` follows by `pow_add_pow_le`.

## (b) Script output
```
Sun Oct  4 21:07:47 UTC 2026
$ lake build RBM3D.Evolution.MeanFar 2>&1 | tail -4
warning: RBM3D/Evolution/ExpInv.lean:21:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3779 jobs).
$ lake build   # `import RBM3D.Evolution.MeanFar` added to RBM3D.lean in the worktree for this check, then reverted (git status clean); tool log 21:06:46 UTC
Build completed successfully (3926 jobs).   # includes `#assert_rbm_axioms` of RBM3D.lean
$ lake env lean scratchpad/T2157/reg.lean   # import RBM3D + import RBM3D.Evolution.MeanFar + #assert_rbm_axioms
axiom audit: 4698 theorems, 1678 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
...
$ lake env lean RBM3D/Evolution/MeanFar.lean 2>&1 | grep -cE "warning|error"
0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Evolution/MeanFar.lean | wc -l
       0
    2311 RBM3D/Evolution/MeanFar.lean
$ lake env lean scratchpad/T2157/ax.lean   # #print axioms of the public declarations
'RBM.Gauss.Sizes.meanFar_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_Cd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_T1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_T2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.meanFar_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STMeanFarConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STMeanFar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stMeanFar' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean scratchpad/T2157/ax2.lean   # collectAxioms of every theorem/def of the module (163, private ones included)
theorems+definitions of the module checked: 163; with a non-standard axiom (sorryAx etc.): 0 #[]
```
Target statements, extracted by `python3 scratchpad/T2157/stmts.py` (`[:= by ...]` marks a cut proof):
```
-- meanFar_Cd (lines 473-473)
def meanFar_Cd (d : ℕ) : ℝ := (d : ℝ) ^ 2 * meanFar_cs d ^ 2 * 2 ^ (d - 2)
-- meanFar_core (lines 666-681)
theorem meanFar_core (hd : 3 ≤ d)
    (T : Zd d L → ℂ) (B : Zd d L → Zd d L → ℂ)
    (hBtr : ∀ a b c, B (a + c) (b + c) = B a b) (hBsym : ∀ a b, B a b = B b a)
    (ρ w₁ K₁ K₂ K K' : ℝ) (hw₁ : 0 ≤ w₁) (hK₂ : 0 ≤ K₂) (hK' : 0 ≤ K')
    (hT1 : ∀ x : Zd d L, ‖T x‖ ≤ K₁ / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hT2 : ∀ a r : Zd d L, ((zdistD d L r : ℕ) : ℝ) ≤ w₁ → ρ < ((zdistInf d L a : ℕ) : ℝ) →
      ‖T (a + r) + T (a - r) - 2 * T a‖ ≤
        K₂ * ((zdistD d L r : ℕ) : ℝ) ^ 2 / (((zdistInf d L a : ℕ) : ℝ) + 1) ^ d)
    (hB1 : ∀ x : Zd d L, ((zdistD d L x : ℕ) : ℝ) ≤ w₁ →
      ‖B 0 x‖ ≤ K / (((zdistInf d L x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hB2 : ∀ x : Zd d L, w₁ < ((zdistD d L x : ℕ) : ℝ) → ‖B 0 x‖ ≤ K')
    (a : Fin 2 → Zd d L) (S : Finset (Zd d L))
    (hS : ∀ b ∈ S, ρ < ((zdistInf d L (b - a 0) : ℕ) : ℝ) ∧ ρ < ((zdistInf d L (b - a 1) : ℕ) : ℝ)) :
    ‖∑ b₁ ∈ S, ∑ b₂ : Zd d L, T (b₁ - a 0) * B b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁))‖ ≤
      meanFar_Cd d * K₁ * K₂ * K * (1 + Real.log ((L : ℝ) + 1)) * (w₁ + 1) ^ 4 /
          (((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) + 2 * K₁ ^ 2 * K' * ((L : ℝ) ^ d) ^ 2  [:= by ...]
-- meanFar_eventually (lines 1980-1986)
theorem meanFar_eventually {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 Cd : ℝ} (hκ : 0 < κ)
    (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (E s t : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n < 1) (hreg : STReg5I sz s t) (hG : STGdecayW sz E s t Cd) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖∫ ω, STfFar sz n (E n) (s n) (t n) σ a ω ∂(sz.seqP)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1))  [:= by ...]
-- STMeanFarConcl (lines 2088-2097)
def STMeanFarConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
      Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)})
    (fun n p _ => ‖∫ ω, STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω ∂(sz.seqP)‖)
    (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) /
      (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1))
-- STMeanFar (lines 2100-2100)
def STMeanFar (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STMeanFarConcl sz E s t)
-- stMeanFar (lines 2106-2106)
theorem stMeanFar (d : ℕ) : STMeanFar d  [:= by ...]
```
Index set and bound of the pin against `STCltFarConcl` (S5-25's input):
```
$ python3 scratchpad/T2157/cmp.py
index set U identical to STCltFarConcl: True
bound zeta identical to STCltFarConcl : True
STCltFarConcl xi : ‖STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω‖
STMeanFarConcl xi: ‖∫ ω, STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω ∂(sz.seqP)‖
```
Compiled nonempty instances (`python3 scratchpad/T2157/inst.py`).  Also in the file: the far set contains `(2,2,2)`, `B(0,0) = 1`, `B(0,e₁) = 1/2`, the window `|r|₁ ≤ 1` is not collapsed (lines 2220-2240); the zero kernel `B = 0` (2244-2260); `Nonempty` index set of `STMeanFarConcl` at `szCL` (2275-2285); `meanFar_eventually` at `szCL` with `STGdecayW` as hypothesis (2290-2306).
```
-- core instance, nonzero B = meanFar_Binst, K = 1, K' = 0 (lines 2194-2203)
example : ∃ K₁ K₂ : ℝ,
    ‖∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd 3 5 =>
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) : ℕ) : ℝ) ∧
        (1 : ℝ) < ((zdistInf 3 5 (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ)),
      ∑ b₂ : Zd 3 5, meanFar_Tinst (b₁ - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0) * meanFar_Binst b₁ b₂ *
        (meanFar_Tinst ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 - b₂) -
          meanFar_Tinst ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1 - b₁))‖ ≤
      meanFar_Cd 3 * K₁ * K₂ * 1 * (1 + Real.log (((5 : ℕ) : ℝ) + 1)) * ((1 : ℝ) + 1) ^ 4 /
          (((zdistInf 3 5 ((![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 0 - (![0, ![1, 0, 0]] : Fin 2 → Zd 3 5) 1) : ℕ) : ℝ) + 1) ^ (3 - 2) +
        2 * K₁ ^ 2 * 0 * ((((5 : ℕ) : ℝ)) ^ 3) ^ 2 := by
-- stMeanFar at szCL (lines 2266-2271)
example (Cd : ℝ) (hCd : 0 < Cd) :
    Step5Inst.InstIng5Concl (fun sz E s t => STMeanFarConcl sz E s t) Step5Inst.szCL Step5Inst.zCL
      Step5Inst.sCL Step5Inst.tCL Cd :=
  Step5Inst.inst_ing5 STReg5I _ (stMeanFar 3) Step5Inst.szCL Step5Inst.zCL Step5Inst.flow_zCL
    Step5Inst.sCL Step5Inst.tCL (fun _ => le_rfl) Step5Inst.szCL_hst Step5Inst.lemT_zCL
    Step5Inst.szCL_reg5I (fun _ h𝔠 => Step5Inst.szCL_con h𝔠) Cd hCd
```
Name clashes, ports, scope:
```
$ grep -nE "^(theorem|def|example)" RBM3D/Evolution/MeanFar.lean | sed -E "s/^([0-9]+:(theorem|def|example) [^ (:]*).*/\1/" | paste -sd" " -   # the public declarations
473:def meanFar_Cd 666:theorem meanFar_core 762:theorem meanFar_T1 814:theorem meanFar_T2 1980:theorem meanFar_eventually 2088:def STMeanFarConcl 2100:def STMeanFar 2106:theorem stMeanFar 2194:example  2220:example  2244:example  2266:example  2275:example  2290:example 
$ git grep -n -E "meanFar_|STMeanFar|stMeanFar" main -- RBM3D RBM3D.lean | wc -l   # name clash against main
       0
$ grep -n "RBM2D\|RBM1D" RBM3D/Evolution/MeanFar.lean | wc -l   # ports from RBM1D/RBM2D (none: no sister file was read or copied)
       0
$ git diff --stat main...t/T2157
 RBM3D/Evolution/MeanFar.lean | 2311 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2311 insertions(+)
4e072ee Jun Yin <321276894+JYin80@users.noreply.github.com>
```
Narrative.  Route of the proof (all in `RBM3D/Evolution/MeanFar.lean`, 2311 lines; ticket estimate: about 600):
1. Core.  `meanFar_card_shell`: `#{|x|_∞ = k} ≤ 2d(2k+1)^{d-1}`; `meanFar_sum_shell`, `meanFar_sum_ball`; the log sum `∑_x (|x|_∞+1)^{-d} ≤ cs(1+log(L+1))` by `harmonic_le_one_add_log`; `meanFar_pair_sum` by `|x-y| ≤ |b-x|+|b-y|`; `meanFar_identity` (`b₂ ↦ b₁+b₁-b₂`); `meanFar_inner_bound`; `meanFar_core`.
2. `meanFar_T1` (zero-mode term via `zeroMode_le_of_ge`), `meanFar_T2` (`|r|₁ ≤ w₁ ≤ ½|a|₁` from `|a|₁ ≥ |a|_∞ ≥ ⌊ρ⌋₊+1 ≥ 2w₁`).
3. `𝔼𝓑`: `meanFar_B`; translation and symmetry from `stExpInv_holds` and `Θ` properties 1, 2 with `KLK_two` (`meanFar_B_tr`, `meanFar_B_sym`); decay: `meanFar_bad_le` takes the witness `u = (s, σ, (a,b))` in the union inside `Prec` (`STGdecayW`, factor `((1-s)/(1-s))^{Cd} = 1`), `meanFar_B_bound` adds the envelope `|𝓛^{(2)}| ≤ η_s^{-2}` (`norm_Lloop_le`) on the bad event (`P ≤ N^{-D₁}`), `meanFar_n_kernel` gives `(eq:propcalB)` for `𝔼𝓑` with `c₀ A^{-6/5}` from `(W^{-d}B_{s,0})^{1/5} W^{-d}B_{s,x}` (`meanFar_BctlSTWB`).
4. `meanFar_assemble` (integral of `STfFar` = `STfFar` with `𝔼𝓑`, `meanFar_integral_fFar`); `meanFar_numeric_main` uses `(1-s)² ℓ_s⁴ ≤ g⁴` (`meanFar_ell_sq`: `ℓ_s ≤ g/√(1-s)` as `1-s ≤ g²`) and the polylog bound; `meanFar_eps_bound`, `meanFar_eta_bound` give `ε₂ ≤ (c₀+2) N^{-(5d+12)}`, `meanFar_tiny` shows the `ε₁`, `ε₂` terms are `≤ (Λ⁴ 2^{d-2} N^d)⁻¹ ≤ A^{-6/5}(|a₁-a₂|+1)^{-(d-2)}`; `meanFar_at_n` is the fixed-`n` bound.
5. `meanFar_pureN` (`(log N)^{13} ≤ N^{τ/4}`, `2 ≤ N^{τ/2}`, `log W ≥ 𝔠 log N`), `meanFar_eventually` (`κ' = min(κ,1/2) ≤ Im m(E)` for `|E| ≤ 2-κ`; `Q = 5d+11`, `D₁ = 5d+19`, `D_w = (5d+13)/𝔠`; `log W ≥ 2d` gives the `(prop:BD2)` window), `stMeanFar` (`Prec` of a deterministic `ξ`: `badSetAt = ∅`).
6. Stop conditions of the ticket: `(prop:BD2)` covers the window (`2d ≤ log W`, `meanFar_at_n` hypothesis `h2d`, supplied by `W ≥ N^𝔠`); no moment input beyond the a.s. envelope and the bad event is needed.

## (c) Verified Mathlib / project names (checked by compile; `integral_mul_left` verified absent: `#check` gave `Unknown identifier`)
- Mathlib: `harmonic_le_one_add_log` (`NumberTheory/Harmonic/Bounds.lean:33`, import added), `Finset.sum_fiberwise_of_maps_to`, `Fintype.card_piFinset`, `Fintype.mem_piFinset`, `Finset.exists_mem_eq_sup`, `Finset.card_biUnion_le`, `Finset.mul_prod_erase`, `pow_add_pow_le`.
- `Finset.prod_le_prod₀` (semiring, `h0 h1`); `Finset.prod_le_prod` here takes only `h` (monoid version; `prod_le_prod'` deprecated alias).
- Integrals: `MeasureTheory.integral_finsetSum` and `integrable_finsetSum` (`integral_finset_sum` deprecated), `integral_const_mul`, `integral_mul_const`, `integral_indicator_one`, `integral_const`, `integral_mono`, `integral_add`, `integral_sub`, `Integrable.of_bound`, `Measure.real`, `measureReal_def`.
- Reals: `Real.log_le_sub_one_of_pos`, `Real.log_two_lt_d9`, `Real.log_rpow`, `Real.exp_nat_mul`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.one_le_rpow`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Nat.lt_floor_add_one`, `Nat.floor_lt`, `Nat.le_floor`, `Nat.floor_le`.
- Order and limits: `div_le_div₀`, `inv_anti₀`, `inv_le_iff_one_le_mul₀'`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `div_le_div_of_nonneg_left`, `isLittleO_log_rpow_rpow_atTop`, `Real.tendsto_log_atTop`, `tendsto_rpow_atTop`, `Filter.Tendsto.const_mul_atTop`, `Filter.Tendsto.eventually_ge_atTop`.
- Project: `zeroMode_le_of_ge`, `ellT_pos`, `one_le_ellT`, `ellT_le_L`, `card_zdist_le_le`, `card_zdist_eq_le`, `zdistD_le_mul_zdistInf`, `norm_Lloop_le`, `walk_measurable_Lloop`, `stExpInv_holds`, `KLK_two`, `Theta_apply_add_right_of_three_le`, `Theta_transpose_of_three_le`, `prop5Decay_holds`, `prop7Diff2_holds`, `Sizes.lam_sq_mul_pow_ge`, `abs_lemE_le`, `lemT_lt_one`, `norm_mE`, `mE_im`, `norm_mSigma`, `norm_mul_mSigma_lt_one`, `Step5Inst.inst_ing5`, `szCL_*`.

## (d) Open issues and paper-delta candidates
- `T2157a`: the paper's `≺` in `(eq:boundEfar)` hides `(log W)^{12}` and `log L`; Lean: `(d (log W)³ ℓ_s + 1)⁴` (`w₁ = d (log W)³ ℓ_s`) and `1 + log(L+1)` (`meanFar_pair_sum`: `∑_b (|b-a₂|+1)^{-d}` is logarithmic), both `≤ N^{τ/4}` eventually (`hpoly`); the ticket's `C K (1-s)² ilambda^{-4} ℓ_s⁴` is not literally the bound (see (a), Verdicts).
- `T2157b`: window and `(prop:BD2)` in `ℓ¹` (`|r|₁ ≤ w₁`), profiles in `ℓ^∞` (`|x|_1 ≤ d|x|_∞`); premise `2w₁ ≤ ⌊ρ⌋₊+1`, from `log W ≥ 2d`.
- `T2157c`: the mean part holds for every `σ ∈ {±}²` and every `a`; `σ₁ ≠ σ₂`, `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` are only index-set conditions of `STCltFarConcl`, unused in the proof.
- `T2157d`: `≺ ⟹ 𝔼` is proved: a.s. envelope `η_s^{-2} + ‖𝒦^{(2)}‖` on the bad event, `D₁ = 5d+19`, `D_w = (5d+13)/𝔠`; the paper applies `(eq:propcalB)` to `𝔼𝓑` without comment.
- No registry line: `STMeanFarConcl`, `STMeanFar` are proved by `stMeanFar` (the scan of `#assert_rbm_axioms` passes); no new premise.  Consumer: S5-25 adds `stMeanFar` to the fluctuation bound of `STCltFar` on the same index set.
- Instance data: the `stMeanFar` instance is at `szCL` (`N = 1.907e43` at `n = 0`, see (a)); the core instance is at `L = 5`.  Observation: file length 2311 lines against the ticket's estimate 600 (shell counts, the logarithmic sum and the exponent bookkeeping).
