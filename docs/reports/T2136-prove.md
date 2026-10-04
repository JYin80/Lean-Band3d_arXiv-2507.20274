Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 12:48:06 UTC 2026

Notation (merged): `Bctl = W^{-d}B_{u,0}` (`Defs/Sizes.lean:214`), `B_{u,0} = (g²+1-u)⁻¹ + (L^d(1-u))⁻¹` (`Defs/Params.lean:36`), `ℓ_u = min(max(g/√(1-u),1),L)` (`:32`), `η_u = (1-u) Im m_E`, `g = sz.lam`, `N = (WL)^d`, `k = m+1` indices, `X` = the deterministic control (`Ξ̂ ≤ X`, `X ≥ 1`), `K_B := sup_u (ℓ_u^d η_u)⁻¹/B_{u,0}`.

### (i) Exponent table (general `d ≥ 3`; `d = 3` in the last column)

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | Ward factor `κ_W=(2iW^dη_u)⁻¹`, at the last slot (`σ_m = ¬σ_0` for alternating `σ`: `KLK_ward` `KLWard.lean:1123`, both charge orders; 𝓛: `npq_loopL_ward` `NewPQ.lean:211`, private) | `‖κ_W‖=(2W^dη_u)⁻¹`; needs `η_u ≥ (1-u)√κ/2 >0` (`‖E‖ ≤ ‖Re z‖ ≤ 2-κ`, `Im m_E ≥ √κ/2`) | `Im m_E = 0.6614` vs `0.3536` at `E=1.5, κ=1/2` |
| 2 | `STAlternating σ` on `Fin(m+1)` (cyclic `σ_{i+1}≠σ_i`) | needs `m+1` even; `m` even: no `σ` exists, the targets are vacuous (e.g. `m=2`). No rotation, no `k=2` swap: the Ward pattern `σ_0::μ++[¬σ_0]` is the loop itself | instances use `m∈{1,3}` |
| 3 | window count, `R=ℓ_u W^{τ'}`, `τ'=τ₀/(4m)`: `#{(a_1..a_{m-1}): all ‖a_i-a_0‖_∞ ≤ R} ≤ (2R+1)^{d(m-1)} ≤ (3ℓ_u)^{d(m-1)} W^{τ'd(m-1)}` | `W^{τ'd(m-1)} ≤ N^{τ'(m-1)}` (`W^d ≤ N`) `≤ N^{τ₀/4}` | exponent `τ₀(m-1)/(4m) ≤ τ₀/4`; slack `τ₀/(4m)` |
| 4 | far part, `B_f = W^{-D'}`, `D'=(2m+2+D)/𝔠`, `W ≥ N^𝔠` | far/target `≲ η⁻¹·(L^d)^{m-1}·W^{-D'}/Bctl^{m+1} ≤ C N^{1+(m-1)-(2m+2+D)+(m+1)} = C N^{-1-D}`; uses `η⁻¹ ≤ (2/√κ)N` (`1-u ≥ N^{-1+ε/2}`, flow), `L^d ≤ N`, `Bctl ≥ N⁻¹/(𝔡⁻²+1)` (`g ≤ 𝔡⁻¹`) | `N^{-1}` (script row `m=` below: `-2` vs `-D=-1`) |
| 5 | `ϑ`: `|ϑ| ≤ C(ℓ^d)^{-m}`, `|∂_uϑ| ≤ C(1-u)⁻¹(ℓ^d)^{-m}` | `STMollifierProps` (`Step34Pins.lean:510`) with arbitrary `C,c`, `g=sz.lam` | constants carried, none depends on `W,L,g` |
| 6 | `ℓ`-power: `ℓ^{d(m-1)}·ℓ^{-dm} = ℓ^{-d}` (`d=3`: `ℓ^{-3}`). In RBM2D `(W²η)⁻¹=ℓ²M⁻¹` cancels it exactly (`ℓ^{2+2(k-2)-2(k-1)}=1`); at `d≥3` it does not cancel, it is absorbed: `(W^dη)⁻¹ℓ^{-d} ≤ K_B W^{-d}B_{u,0}` | `K_B ≤ 2/Im m_E ≤ 4/√κ`; proof: `ℓ=L`: `(L^dη)⁻¹ ≤ B/Im m` (zero-mode term); `ℓ=1` (`g²≤1-u`): `(1-u)⁻¹ ≤ 2(g²+1-u)⁻¹`; `1<ℓ=g/√(1-u)<L`: `ℓ^{-d}(1-u)⁻¹=g^{-d}(1-u)^{d/2-1} ≤ g^{-2}`, `B ≥ (2g²)⁻¹` (`1-u ≤ g²`; needs `d ≥ 2`) | script: sup `(ℓ^d(1-u))⁻¹/B = 2` over a `d∈{2..5}` scan; `d=3` instance max `2.2631 ≤ 3.0237` |
| 7 | `Bctl` power: `Bctl^m` (from `Ξ̂≤X`) `· (W^dℓ^dη)⁻¹ ≤ K_B Bctl^{m+1}` | exactly `m+1`, no loss in the `B`-exponent | `K_B` vs `4/√κ` above |
| 8 | `ℬ₅`: `(1-u)⁻¹ = Im m_E·η⁻¹ ≤ η⁻¹` | constant `C K_B C_win` | `Im m_E ≤ 1` |
| 9 | `ℬ₄` (`QopAlgebra_commutator_ThetaN` `QopAlgebra.lean:871`): `‖Θ‖_{∞→∞} ≤ (m+1)(1-u)⁻¹` (private `QGridA_norm_ThetaN_le` `QGridA.lean:1408`, copy) and `|P(Θ𝒜)_{a_0}| ≤ (m+1)(1-u)⁻¹ max|P𝒜|` (slots of `QopAlgebra_ThetaN_sumZero`) | `‖ℬ₄‖ ≤ 2(m+1)(1-u)⁻¹ C ℓ^{-dm} max|P𝒜|`, then rows 1-8 | constant `2(m+1)` |
| 10 | stochastic loss: `Ξ̂ ≤ N^{τ₀/4}X` (hyp. at `τ₀/4`) · window `N^{τ₀/4}` · constants `3^{d(m-1)}(m+1)CK_B ≤ N^{τ₀/4}` (eventually) | total `N^{3τ₀/4} ≤ N^{τ₀}`; failure prob `N^{-(D+1)}` (hyp.) `+ N^{-(D+1)}` (far, row 4) `≤ N^{-D}` | `N^{τ₀/4}`; `N^{-D}` factor `1/2` |
| 11 | §29 boundary items | (1) `0≤s<t≤lemT z<1` in `STIngR`; (2) case (i) only, `STCaseI` (`∀ n`: if some `n` has `g²/L² > 1-t`, the premise is false and the pin is vacuous; at the instance `lam ≤ 1`); (3) `L^d ≤ N ≤ W^{1/𝔠}` derived from `Admissible`, not assumed; (4) conclusions are `Prec` (eventual), constants `4/√κ`, `3^{d(m-1)}` independent of `W,L,g` | — |

Finding (row 6): `(ℓ^dη)⁻¹ ≲ B_{u,0}` holds for **all** `u∈[0,1)` with the clipped `ellT` and the zero mode of `Bparam` (`K_B≤2/Im m_E`, `d≥2`); the case-(i) condition `1-u ≥ g²/L²` (ticket, `3_5:1264`) is not needed for this inequality in the Lean definitions (the paper needs it for `B ≍ (g²+1-u)⁻¹`, `(eq:Bu0asymp)`). It is still a hypothesis of the pins (`STCaseI`) and is not used by me. The exponents close; `d ≥ 3` enters only through `d ≥ 2` here.

### Inputs and the one missing bridge (ticket (ii))
- Premises of the pins themselves (not of `STIngR`): `m, C, c, ϑ`, `X ≥ 1`, `Prec Ξ̂^{𝓛-𝒦}_{u,m} ≤ X` (uniform in `u`).
- `STStep2Concl ∋ STGdecayW` (`Step34Pins.lean:208`): `Prec` over `TimeIcc×(Fin 2→Bool)×(Fin 2→Zd)`, uniform in `u`. `STGdecayW ⟹ STStep2DecayPT` (`Step2Defs.lean:287`, identical right side) is uniform ⟹ per time: the merged proof `perTimeDomAt_of_stochDomAt` is `private` (`Green/Pins.lean:703`), 6 lines to copy. Then `stDecayLoopPT_of_step2` (`DecayLoopA.lean:970`) uses `STFlow`, `0≤s`, `s≤t`, `t≤lemT z`, all in `STIngR`.
- **Missing bridge F1.** That gives `STDecayLoopPT`, which is `PrecPT` (union over `u,σ,a` outside `P`). Both targets are `Prec` over `TimeIcc × σ × a` (union over `u` inside `P`), so the far entries needed in row 4 are not supplied uniformly in `u`. No input is missing (`STGdecayW` is uniform), but `DecayLoopA.lean` exports no uniform form and its deterministic steps are private (`DecayLoopA_adjacent:195, _cut:309, _pair:389, _alg:536, _main:713`). Route: copy them into `B45.lean` as `private B45_*` and run them pathwise on the uniform event of `STGdecayW` at `(τ,D)` (steps 1-5 of the header of `DecayLoopA.lean`; step 6, the event inclusion, is then done at the `Prec` level instead of with `perTimeCalc_of_imp`, which is per time). `stKcalDecay_holds` (`KDecay.lean`) is deterministic and merged; `W^{-Q} ≤ g` from `(eq:WO)`.
- `STKbound, STLK, STConStInd, STKward` sit in `STIngR` but the argument above does not use them. `𝓛` Ward at `s=false` needs the conjugate case: copy `npq_loopL_ward` (private, `NewPQ.lean:211`; Hermitian: `gLoopFlow_seqHflow_isHermitian`).

### (ii) Concrete nondegenerate instance
Lean instance data (merged): `sz0` (`Defs/Sizes.lean:260`), `z0`, `flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0` (`Induction/Defs.lean:413,435`), `s≡0`, `t≡1/16` (`:439-440`), `E=lemE z0` (`|E|≤1/2`), case (i) (`lam²/L² ≤ 1.6e-5 ≤ 15/16 ≤ 1-t`), `m=1` (`σ=(+,-)`, 2 indices) and `m=3` (`σ=(+,-,+,-)`, 4 indices), `X≡1`, any `C,c>0`, `ϑ` with `STMollifierProps` kept as hypothesis (`STMollifierEx` is owed; no merged construction). External hypotheses kept: `STStep2Concl`, `STConStInd`, `STLK`, `Prec Ξ̂≤X`. Numeric check at `d=3`, `L=9`, `W=2`, `g=1/2`, `N=5832`, `E=1.5`, `κ=1/2`, `u∈{0.5,0.9,1-g²/L²}`, plus an explicit `m=1` mollifier `ϑ=e^{-|x|_1/ℓ}/Z` (`c=1`), plus `sz0`, `n=0`. The ticket's literal quantity `(W^dη)⁻¹(ℓ^d)^{-m}` vs `(W^{-d}B)^{m+1}` omits the window count `ℓ^{d(m-1)}` and `Bctl^m X`, so it is not the closing criterion (ratios `>1` below are expected); the closing quantity is `full chain/(W^{-d}B)^{m+1} = (ℓ^dη)⁻¹/B_{u,0}`. This single-size run checks the deterministic exponent only (`W=2 < N^{1/6}`).

Limit computation for the external decay input (TEAM §8 lesson 14): the far pair `|c|=ℓW^{τ'}` gives `e^{-W^{τ'/2}}` in `STGdecayW`; it is `≤ W^{-D'}` iff `ln W ≥ 53.08` (`m=3, D=1, 𝔠=1/6, τ'=0.3`, `D'=54`): a threshold of the eventual `≺` (the proof sets `τ'=τ₀/(4m)`, so thresholds depend on `τ₀`), not a hypothesis of the instance.

```
$ cd scratchpad/T2136 && python3 pre.py | grep -v "m=2"
N= 5832 Im m_E=0.6614 2/Im m=3.0237 caseI: 1-t>=g^2/L^2 = 0.0030864197530864196
u=0.5: 1-u=0.500000 ell=1.0000 B0=1.3361 Bctl=0.16701 eta=0.33072 (l^d eta)^-1/B0=2.2631 <=2/Im m: True
   m=1: full chain/(W^-d B)^(m+1)=2.2631; literal (W^d eta)^-1 l^(-dm)=3.7796e-01 vs (W^-d B)^(m+1)=2.7892e-02 ratio=1.3551e+01
   m=3: full chain/(W^-d B)^(m+1)=2.2631; literal (W^d eta)^-1 l^(-dm)=3.7796e-01 vs (W^-d B)^(m+1)=7.7798e-04 ratio=4.8583e+02
u=0.9: 1-u=0.100000 ell=1.5811 B0=2.8709 Bctl=0.35886 eta=0.06614 (l^d eta)^-1/B0=1.3323 <=2/Im m: True
   m=1: full chain/(W^-d B)^(m+1)=1.3323; literal (W^d eta)^-1 l^(-dm)=4.7809e-01 vs (W^-d B)^(m+1)=1.2878e-01 ratio=3.7125e+00
   m=3: full chain/(W^-d B)^(m+1)=1.3323; literal (W^d eta)^-1 l^(-dm)=3.0598e-02 vs (W^-d B)^(m+1)=1.6584e-02 ratio=1.8450e+00
u=1-g^2/L^2: 1-u=0.003086 ell=9.0000 B0=4.3957 Bctl=0.54946 eta=0.00204 (l^d eta)^-1/B0=0.1529 <=2/Im m: True
   m=1: full chain/(W^-d B)^(m+1)=0.1529; literal (W^d eta)^-1 l^(-dm)=8.3992e-02 vs (W^-d B)^(m+1)=3.0190e-01 ratio=2.7821e-01
   m=3: full chain/(W^-d B)^(m+1)=0.1529; literal (W^d eta)^-1 l^(-dm)=1.5805e-07 vs (W^-d B)^(m+1)=9.1146e-02 ratio=1.7340e-06
max (l^d eta)^-1/B0 =2.2631
window u=0.5: R=1.231 2R+1=3.462 vs L=9: window<L True
window u=0.9: R=1.947 2R+1=4.893 vs L=9: window<L True
window u=1-g^2/L^2: R=11.080 2R+1=23.161 vs L=9: window<L False
mollifier u=0.5: Z=9.837 sup|theta|*l^d (=C needed, c=1 incl. exp factor)=0.1017
mollifier u=0.9: Z=29.400 sup|theta|*l^d (=C needed, c=1 incl. exp factor)=0.1345
mollifier u=1-g^2/L^2: Z=358.907 sup|theta|*l^d (=C needed, c=1 incl. exp factor)=2.0312
deriv u=0.5: max_x (1-u)|d_u theta| l^d = 0.0000
deriv u=0.9: max_x (1-u)|d_u theta| l^d = 0.1541
$ python3 scan.py
sup over scan of (ell^d (1-u))^-1 / B_{u,0} = 1.999999999999996 at (5, 1000, 0.001, 1.0000000000000002e-06) (claim: <= 2, all u in [0,1), d>=2)
$ python3 inst.py | grep -E "n=0|^m=|sz0"
sz0 flow instance (Defs.lean:413-440): s=0,t=1/16, E in {0,1/2} (|E|<=|Re z|=1/2<=2-kappa, kappa=1/10)
 n=0 L=4 W=32 N=2097152 g=1.562e-02 E=0.0 u=0.0000: caseI=True ell=1.0 (l^d eta)^-1/B0=0.9849 <= 2/Im m=2.0000: True
 n=0 L=4 W=32 N=2097152 g=1.562e-02 E=0.0 u=0.0625: caseI=True ell=1.0 (l^d eta)^-1/B0=0.9849 <= 2/Im m=2.0000: True
 n=0 L=4 W=32 N=2097152 g=1.562e-02 E=0.5 u=0.0000: caseI=True ell=1.0 (l^d eta)^-1/B0=1.0172 <= 2/Im m=2.0656: True
 n=0 L=4 W=32 N=2097152 g=1.562e-02 E=0.5 u=0.0625: caseI=True ell=1.0 (l^d eta)^-1/B0=1.0172 <= 2/Im m=2.0656: True
m=1: exponent of N in far/target with D'c=2m+2+D: -2 (need <= -D=-1)
m=2: exponent of N in far/target with D'c=2m+2+D: -2 (need <= -D=-1)
m=3: exponent of N in far/target with D'c=2m+2+D: -2 (need <= -D=-1)
m=3: D'=54; exp(-W^(tau'/2)) <= W^(-D') iff ln W >= 53.08  (W >= 1.13e+23); an eventual threshold of the stochastic domination, not a hypothesis
```

### Verdicts
- Target 1 `stWardTypePPin_holds : STWardTypePPin d`: **PASS** (exponents close, rows 1-11; hypotheses satisfiable at the instance), conditional on proving bridge F1 inside `B45.lean` (a proof obligation, not a missing input).
- Target 2 `stB45Pin_holds : STB45Pin d`: **PASS**, same condition; `ℬ₄, ℬ₅` use rows 5, 8, 9 on top of target 1's `P`-bound.
- Prover notes: `m` even is vacuous (row 2); the instance must use `m∈{1,3}`; the `d≥3` change is row 6 (absorption by `K_B`, not cancellation).

## (a′) Preflight corrections — Sun Oct  4 13:41:48 UTC 2026

1. Row 5 (and the ticket's step (c)): `STMollifierProps` (`Step34Pins.lean:510`) bounds `‖ϑ_t(a)‖` by `C (ℓ^{-d})^m exp(-c Σ_{i≥2}|a_i-a_1|/ℓ)` with `c : ℝ` unrestricted (`STWardTypeP`, `STB45`: `∀ (m : ℕ) (C c : ℝ)`), not by `C(ℓ^d)^{-m}`. For `c ≥ 0` the exponential is `≤ 1`; for `c < 0` it is not, so the row-5 bound is false as written. Corrected row 5 (proved as `B45_vth_sup`): `|ϑ| ≤ C(e^{|c|md/2} + 2/(dm) + 2 max(0,-log g))(ℓ^d)^{-m}`; the loss `max(0,-log g) ≤ ½ log N` is absorbed by `N^{τ₁}`. Rows 6-10 hold with `Λ = C(e^{|c|md/2} + 2/(dm) + 2 max(0,-log g))` in place of `C`; the verdicts are unchanged (PASS).
2. Row 9: the private `QGridA_norm_ThetaN_le` is not copied; `B45_norm_ThetaN_le` re-proves it from the public `norm_Theta_le`, `norm_SB`, `sum_norm_row_le`.
3. Bridge F1 is resolved as proposed in (a) (copy of the deterministic steps, run on the uniform event); `P_u ≤ N^{C₀}` is derived from the far premise `1-u ≥ N⁻¹`, so `B45_far` does not use `RangeCond`.

## (b) Script output

Branch `t/T2136`, HEAD 7f5e5e9; this rerun's first `date -u`: Sun Oct  4 14:42:23 UTC 2026; report finished: Sun Oct  4 14:52:32 UTC 2026. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2136`; scratch files in `scratchpad/T2136/`.

```
$ git log --format="%h %ad %s" --date=iso -3 t/T2136
7f5e5e9 2026-10-04 07:48:32 -0700 T2136: B45 module docstring: state the window exponent and D' in the Lean m
d50b5e0 2026-10-04 06:39:50 -0700 T2136: S3-19 Induction/B45 (proves STWardTypePPin, STB45Pin)
549a62d 2026-10-04 05:28:17 -0700 T2132: merge S3-13a Induction/QGridA
$ lake build RBM3D.Induction.B45 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3736 jobs).
$ lake env lean scratchpad/T2136/axmod2.lean   # module-wide: every theorem/def of the module, private ones included
module RBM3D.Induction.B45: 42 public + 42 private theorems/defs checked; bad: []
$ lake env lean scratchpad/T2136/axmod.lean   # #print axioms of the targets and main lemmas
'RBM.Gauss.Sizes.stWardTypePPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stB45Pin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.B45_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.B45_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.B45_vth_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.B45_det2' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/B45.lean | wc -l
       0
$ wc -l RBM3D/Induction/B45.lean
    3065 RBM3D/Induction/B45.lean
$ git diff --stat main...t/T2136
 RBM3D/Induction/B45.lean | 3065 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    2 -
 2 files changed, 3065 insertions(+), 2 deletions(-)
$ git diff main...t/T2136 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STWardTypePPin, -- `(eq:Ward_typeP)` (DECISIONS §25)
-   `RBM.Gauss.Sizes.STB45Pin, -- `(y27kasdfg)` (DECISIONS §25)
$ git diff main...t/T2136 -- RBM3D/Induction/Step34Pins.lean | wc -l
0
$ sed -n 576,580p RBM3D/Induction/Step34Pins.lean   # the pins, merged and unchanged (the diff above is empty)
/-- `(eq:Ward_typeP)`: case (i). -/
def STWardTypePPin (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STWardTypeP sz E s t)

/-- `(y27kasdfg)`: case (i). -/
def STB45Pin (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STB45 sz E s t)
$ sed -n 2935,2950p RBM3D/Induction/B45.lean   # the two targets
theorem stWardTypePPin_holds (d : ℕ) : STWardTypePPin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht _hR _hKb _hKw _hLK _hcon hStep2 m C c hm ϑ hϑ X hX1 hXprec
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (B45_pins hd sz hκ hε hflow hs0 hst ht hStep2 C c ϑ hϑ X hX1 hXprec).1

/-- **`(y27kasdfg)`** (`3_5:1692`): the pin `STB45Pin`, case (i). -/
theorem stB45Pin_holds (d : ℕ) : STB45Pin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht _hR _hKb _hKw _hLK _hcon hStep2 m C c hm ϑ hϑ X hX1 hXprec
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (B45_pins hd sz hκ hε hflow hs0 hst ht hStep2 C c ϑ hϑ X hX1 hXprec).2

end RBM.Gauss.Sizes
$ sed -n 2872,2878p RBM3D/Induction/B45.lean   # B45_pins, the common core (its hypotheses are STStep2Concl, the bound Xi-hat <= X, STMollifierProps; no STKbound/STKward/STLK/STConStInd)
theorem B45_pins (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) {Cd : ℝ} (hStep2 : STStep2Concl sz (STflowE z) s t Cd)
    {m : ℕ} (C c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n))
    (X : ℕ → ℝ → ℝ) (hX1 : ∀ n u, 1 ≤ X n u)
    (hXprec : Prec sz (U := fun n => TimeIcc s t n)
$ sed -n 2972,2996p RBM3D/Induction/B45.lean   # nonempty alternating sigma at 2 and 4 indices; stWardTypePPin_holds at m = 1 (d = 3, sz0, flow_z0, s = 0, t = 1/16, merged mollifier)
example : Nonempty {σ : Fin (1 + 1) → Bool // STAlternating σ} :=
  ⟨⟨![true, false], fun i => by fin_cases i <;> decide⟩⟩

/-- Alternating sign vectors exist at `m + 1 = 4`: `(+,-,+,-)`. -/
example : Nonempty {σ : Fin (3 + 1) → Bool // STAlternating σ} :=
  ⟨⟨![true, false, true, false], fun i => by fin_cases i <;> decide⟩⟩

/-- **`stWardTypePPin_holds` applied at `m = 1`** (two indices) on `(sz0, z0, 0, 1/16)` with the merged mollifier. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKbound sz0 (STflowE z0) → STKward sz0 (STflowE z0) → STLK sz0 (STflowE z0) sInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n)
          (fun n u ω => STXiLK sz0 n (STflowE z0 n) (u : ℝ) 1 ω) (fun n _ _ => 1) →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} ×
            (Fin (1 + 1) → Zd 3 (sz0.L n)))
          (fun n q ω => ‖STPsum (d := 3) (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1)
              (q.2.2 0) * QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n) (q.1 : ℝ) q.2.2‖)
          (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 + 1) * 1)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_WardTypeP (stWardTypePPin_holds 3) Cd hCd
  refine ⟨𝔠d, h0, h1, fun hK hKw hLK h2 hX => ?_⟩
  exact H hK hKw hLK h2 1 _ _ le_rfl (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 1 (sz0.three_le_L n) (B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

$ grep -n "^example\|inst_WardTypeP\|inst_B45\|exact H hK" RBM3D/Induction/B45.lean   # the other three instances have the same shape
2972:example : Nonempty {σ : Fin (1 + 1) → Bool // STAlternating σ} :=
2976:example : Nonempty {σ : Fin (3 + 1) → Bool // STAlternating σ} :=
2980:example (Cd : ℝ) (hCd : 0 < Cd) :
2991:  obtain ⟨𝔠d, h0, h1, H⟩ := inst_WardTypeP (stWardTypePPin_holds 3) Cd hCd
2993:  exact H hK hKw hLK h2 1 _ _ le_rfl (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
2998:example (Cd : ℝ) (hCd : 0 < Cd) :
3009:  obtain ⟨𝔠d, h0, h1, H⟩ := inst_WardTypeP (stWardTypePPin_holds 3) Cd hCd
3011:  exact H hK hKw hLK h2 3 _ _ (by norm_num) (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n))
3016:example (Cd : ℝ) (hCd : 0 < Cd) :
3034:  obtain ⟨𝔠d, h0, h1, H⟩ := inst_B45 (stB45Pin_holds 3) Cd hCd
3036:  exact H hK hKw hLK h2 1 _ _ le_rfl (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
3041:example (Cd : ℝ) (hCd : 0 < Cd) :
3059:  obtain ⟨𝔠d, h0, h1, H⟩ := inst_B45 (stB45Pin_holds 3) Cd hCd
3061:  exact H hK hKw hLK h2 3 _ _ (by norm_num) (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n))
$ lake env lean scratchpad/T2136/odd.lean   # exit 0, no output: no alternating sigma at 3 or 5 indices (decide), one at 4 indices
example : ∀ σ : Fin 3 → Bool, ¬ STAlternating σ := by
  unfold STAlternating; decide
example : ∀ σ : Fin 5 → Bool, ¬ STAlternating σ := by
  unfold STAlternating; decide
example : ∃ σ : Fin 4 → Bool, STAlternating σ := ⟨![true, false, true, false], by unfold STAlternating; decide⟩
$ grep -n "axiom audit:\|Build completed\|premises found\|registry:\|error:" fullbuild3.txt   # full `lake build` in the worktree with `import RBM3D.Induction.B45` added to RBM3D.lean locally (restored afterwards, not committed); Test/Axioms.lean as committed
805:info: RBM3D.lean:183:0: axiom audit: 4158 theorems, 1435 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
885:premises found by scanning: 69 (borrowed 0, owed 54, structural 15).
886:registry: 1 borrowed + 73 owed + 39 structural; 44 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
931:Build completed successfully (3884 jobs).
$ scratchpad/T2136/clash.sh   # git grep -w of every public name of B45.lean in RBM3D/ and RBM3D.lean on main
checked 41 public names (git grep -w, main 549a62d); clashes: 0
$ python3 scratchpad/T2136/overlap.py   # fraction of source lines (stripped length >= 30) that occur verbatim in B45.lean
RBM3D/Induction/DecayLoopA.lean:118-701: 347/384 source lines (len>=30) occur verbatim in B45.lean
RBM3D/Induction/NewPQ.lean:168-253: 44/58 source lines (len>=30) occur verbatim in B45.lean
RBM3D/Induction/QopNorm.lean:36-169: 53/81 source lines (len>=30) occur verbatim in B45.lean
RBM3D/Induction/QopAlgebra.lean:714-781: 33/38 source lines (len>=30) occur verbatim in B45.lean
RBM2D Induction/B45.lean at c9a24cf: 2096 lines; 17/1482 lines (len>=30) occur verbatim in RBM3D B45.lean
RBM2D Induction/B45.lean at 9e0f275: 1149 lines; 14/789 lines (len>=30) occur verbatim in RBM3D B45.lean
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/B45.lean | tail -2
9e0f275
 RBM2D/Induction/B45.lean | 1043 +++-------------------------------------------
 1 file changed, 48 insertions(+), 995 deletions(-)
$ git --no-optional-locks log -1 --format="%h" main -- <file>   # merge commit of each RBM3D port source
RBM3D/Induction/DecayLoopA.lean 6179d8c
RBM3D/Induction/NewPQ.lean f28fd9c
RBM3D/Induction/QopNorm.lean eb6d67a
RBM3D/Induction/QopAlgebra.lean 6b2494e
$ lake env lean scratchpad/T2136/chk2.lean   # 72 Mathlib/core names listed in (c), env.contains
present: 72; missing: []
```

Narrative:
- Runs: stage 1b ran twice. `git reflog` of the worktree: the first run committed e1981d4 at 13:39:50 UTC and amended it to d50b5e0 at 13:43:42 UTC; per the rerun prompt it then ended on a session-limit API error. This rerun (first `date -u` 14:42:23 UTC) found d50b5e0, re-ran every check on this page, and added 7f5e5e9 (14:48:32 UTC, module docstring only: the window exponent and `D'` stated in the Lean `m`). All build, axiom, clash, full-build and overlap output above is from this rerun on 7f5e5e9; the first run's times are from `git reflog`.
- Both targets have the pinned types (`B45.lean:2935, 2943`; `Step34Pins.lean` unchanged) and no added hypothesis. Both are the two projections of `B45_pins` (`:2872`), whose hypotheses are `STStep2Concl` (only its part `STGdecayW`, used by `B45_far`), `Ξ̂ ≺ X` and `STMollifierProps` for every real `C, c`. `STKbound, STKward, STLK, STConStInd` and the case-(i) condition of `STIngR` are bound unused (`_hR _hKb _hKw _hLK _hcon`, lines 2938, 2946).
- `m` convention: `B45_pins` has `Fin (m+1+1)` indices, Lean `m` = pin `m − 1`; the pin's `1 ≤ m` is converted by `obtain ⟨m', rfl⟩` (lines 2939, 2947).
- Bridge F1 of (a): `DecayLoopA.lean` exports only the per-time form, so its deterministic steps (`DecayLoopA.lean:118-701`) are copied as private `B45_*` and run pathwise on the good event of the uniform `STGdecayW` (`B45_far_main` `:1493`, `B45_far` `:1762`).
- Ward step: `B45_alt_last` (`:2527`: alternating ⟹ last label `= ¬σ_0`); `B45_ward_fin` (`:200`): `Σ_x (𝓛-𝒦)_{σ,(a',x)} = (2iW^dη)⁻¹((𝓛-𝒦)_{σ⁺,a'} − (𝓛-𝒦)_{σ⁻,a'})` from `KLK_ward` and the copied `npq_loopL_ward`; window split `B45_Psum_le` (`:304`), `B45_Psum_LK_le` (`:414`): near entries `((2R+2)^d)^m`, far entries `(L^d)^m`.
- Exponents: `B45_scale` (`:459`) `(ℓ_u^d(1−u))⁻¹ ≤ 2B_{u,0}` for every `u < 1` (`d ≥ 2`); `B45_scales` (`:2246`) `(W^dη)⁻¹ℓ^{-d} ≤ 2Γ W^{-d}B_{u,0}`, `Γ = 2/√κ`; `B45_master_real` (`:530`) closes `Pi·ϑb ≤ 3·4^{dm}ΓΛν²·B^{m+2}X`. At `d ≥ 3` the powers of `ℓ` are absorbed, not cancelled as in RBM2D (T2136b).
- Mollifier: `B45_vth_sup` (`:2115`) holds for every real `c` ((a′) 1, T2136a); for `c < 0` it uses `B45_cmp` (`:1805`, the fencing theorem `image_norm_le_of_norm_deriv_right_le_deriv_boundary'`; derivative needed on `(t,T]` only) and the antiderivative `B45_hasDerivAt_Phi` (`:1933`).
- `ℬ₄`: `B45_B4_le` (`:862`) from `QopAlgebra_commutator_ThetaN`, `B45_norm_ThetaN_le`, `B45_Psum_ThetaN_le`; `ℬ₅` from `‖∂_uϑ‖ ≤ C(1−u)⁻¹ℓ^{-dm}` and `(1−u)⁻¹ ≤ η⁻¹`.
- Probability: `B45_prec_assemble` (`:2456`, union bound of the sources `Ξ̂ ≺ X` and the far entries) and `B45_key`, which carries `set_option maxHeartbeats 400000 in` (`:2684`, with the reason in the comment at `:2685`); `τ₁ = min(τ/6, 1/4)`, `τf = τ₁/(m+1)`, `D' = (2m+4)/𝔠` (`:2723-2728`).
- Registry: the two owed lines are removed (diff above); the full build with the root import added locally passes the registry and the axiom audit; `RBM3D.lean` is not committed (the hub adds the import). No theorem of `B45.lean` takes `STGdecayW` as a hypothesis.
- Ports (all private `B45_*` helpers or `B45_`-prefixed lemmas; sources above, none from RBM2D): `DecayLoopA.lean:118-701` (6179d8c), `NewPQ.lean:168-253` (f28fd9c), `QopNorm.lean:36-169` (eb6d67a), `QopAlgebra.lean:714-781` (6b2494e). RBM2D `Induction/B45.lean` is followed in structure only: 17 of 1482 of its lines (at c9a24cf) occur verbatim in B45.lean.
- Instances: four `example`s (`:2980, :2998, :3016, :3041`), `d = 3`, `sz0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `X ≡ 1`, merged mollifier at `m = 1, 3`; `STKbound`, `STKward`, `STLK`, `STStep2Concl` and `Ξ̂ ≺ X` stay hypotheses (other gates' outputs); the flow, `0 ≤ s < t ≤ lemT z`, `STCaseI`, `STConStInd`, `1 ≤ X`, `STMollifierProps` are discharged inside `inst_WardTypeP`/`inst_B45` and the example. At even `m` (odd index count) no alternating `σ` exists (compiled above for 3 and 5 indices), so the instances use `m = 1, 3`.

## (c) Verified Mathlib names (72 checked present by the `env.contains` script above: `present: 72; missing: []`; each occurs in `B45.lean`)

- `image_norm_le_of_norm_deriv_right_le_deriv_boundary'`: fencing theorem used in `B45_cmp`.
- `HasDerivAt.comp_const_sub`, `HasDerivAt.congr_deriv`, `HasDerivAt.const_sub`, `HasDerivAt.neg`, `HasDerivAt.pow`, `HasDerivAt.div_const`, `HasDerivAt.const_mul`, `HasDerivAt.log`, `Real.hasDerivAt_sqrt`: antiderivatives in `B45_hasDerivAt_Phi`, `B45_vth_sup`.
- `Real.log_le_rpow_div`, `Real.log_le_log`, `Real.log_inv`, `Real.log_pow`, `Real.log_nonpos`, `Real.log_nonneg`: `B45_log_le`, `B45_vth_sup`.
- `Fin.snocEquiv`, `Equiv.sum_comp`, `Fintype.sum_prod_type`, `List.ofFn_succ`, `List.ofFn_succ'`, `finRotate_last`: `B45_Psum_snoc`, `B45_ofFn_*`, `B45_alt_last`.
- `Fintype.card_piFinset`, `Fintype.mem_piFinset`, `Finset.sum_nbij'`, `Finset.sum_filter`, `Finset.le_sup'`, `Finset.card_image_le`, `Finset.sum_product'`, `Finset.sum_comm`, `Finset.sum_sub_distrib`: counting and slots.
- `Real.one_le_rpow`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_pos_of_pos`, `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.sqrt_div`, `Real.exp_pos`, `Real.one_le_exp`: exponent bookkeeping.
- `pow_le_pow_left₀`, `pow_le_one₀`, `one_le_pow₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `div_le_iff₀`, `le_div_iff₀`, `div_le_div_of_nonneg_left`, `le_mul_of_one_le_right`, `le_mul_of_one_le_left`, `one_le_mul_of_one_le_of_one_le`, `nonneg_of_mul_nonneg_left`: inequalities.
- `Complex.abs_im_le_norm`, `norm_sub_norm_le`, `norm_le_norm_add_norm_sub'`, `RCLike.norm_conj`: norms.
- `MeasureTheory.measure_union_le`, `ENNReal.ofReal_add`, `tendsto_rpow_atTop`, `Filter.Tendsto.eventually_ge_atTop`, `Ico_mem_nhds`, `DifferentiableOn.differentiableAt`, `DifferentiableOn.continuousOn`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `Nat.ceil_lt_add_one`, `Nat.lt_ceil`: probability and lattice.
- Verified absent: none searched.

## (d) Open issues and paper-delta candidates

- T2136a: the pins quantify the mollifier constants `C, c` over `ℝ` (`STMollifierProps`, `Step34Pins.lean:510`; `STWardTypeP`/`STB45`: `∀ (m : ℕ) (C c : ℝ)`); the paper has `c > 0` (`sed -n 1214p paper/tex/3_5_Loop_Hierarchy.tex`: `along with the following estimates for a constant $c>0$:`; `(eq:derv_Theta)` `3_5:1215`). Lean proves the pins for every real `c`; for `c < 0` the sup bound costs `2 max(0, −log g) ≤ log N` (`B45_vth_sup` signature above), absorbed by `N^{τ₁}`. Restricting to `c > 0` in a later amend would simplify `B45_vth_sup`; it is not needed.
- T2136b: `(ℓ_u^d η_u)⁻¹ ≲ B_{u,0}` (`3_5:1264`, stated there under `1 − u ≥ g²/L²`) holds for every `u < 1` for the Lean `ellT`, `Bparam`, with constant `2/Im m_E ≤ 4/√κ` (`B45_scale`, `d ≥ 2`); the proofs of the two pins do not use the case-(i) condition.
- T2136c: of the Step 2 conclusion the proofs use only `STGdecayW` (with `Ξ̂ ≺ X`): fewer premises than `STIngR` supplies (same shape as T2041i).
- T2136d (observation): for an odd number `m+1` of indices (even pin `m`) `STAlternating` is empty (compiled for 3 and 5 indices, `odd.lean` above), so both pins say nothing at even `m`; the instances use `m = 1, 3`.
- Refactor suggestion (not a blocker): the copy of `DecayLoopA.lean:118-701` (584 source lines) duplicates the deterministic steps of `lem_decayLoop`; publishing a uniform form there would remove it.
- Style: `lake build` prints the header-linter warning `B45.lean:13:0` (module docstring after `set_option`), as it does for `Step34Pins.lean:12:0` in the same build output.
- The hub adds `import RBM3D.Induction.B45` to `RBM3D.lean` after the last `import` line at merge; the full `lake build` passed with that line added locally.
