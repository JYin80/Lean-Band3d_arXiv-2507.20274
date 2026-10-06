Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 02:41:18 UTC 2026

### (i) Exponent table
Notation: `B = sz.Bctl n t = W^{-d}B_{t,0}`, `η = etaT = (1-t) Im m`, `X_a = 𝓛^{(1)}_{+,a} - m`, `m = mE(E)`, `K⁺ = t S^B Θ_{t m²}`, `ĝ = lam`. `SP` = scratchpad `T2243/` of the session. All `≺` lose `N^τ`; constants (`|m|=1`, `0≤t<1`, 10 terms) are absorbed.

| quantity | value / constraint | slack / source |
|---|---|---|
| `t` | `0 ≤ t ≤ lemT z`, `t < 1` (`st5_t_lt_one` Step5Kit:192); `t = 0`: `G = mI`, `X ≡ 0`, so `LWcut = 0` | script `conj.py`: `|LWcut| = 0.0` at `t=0` |
| `E`, `m` | `|E| ≤ 2-κ` (`st6_flowE_le` Step6Kit:535); `‖m‖ = 1`; `z_t + t m = E + m = -m⁻¹` (`zt = E + (1-t)m`, Semicircle:179) for `oe2x_integral` | `|m|-1 ≤ 8e-62` at all instance rows below |
| `η⁻¹ ≤ √(2/κ)(1-t)⁻¹` | `Im m ≥ √(2κ)/2` (`st6_mE_im_ge` Step6Kit:544) | `√(2/κ) = 4.472` at `κ = 1/10`; at instance `η⁻¹(1-t) = 1.033` (col. 8 below) |
| `B³ ≤ B^{5/2}` | iff `B ≤ 1` (eventually; T2236 (a)(i) row 28) | `B = 10^{-4.48}` (n=0, tInst), `10^{-0.76}` (n=0, tEnd); `B^{1/2} = 5.7e-3` resp. `0.42` |
| `I₁, J₁` pins (`LWExpI1K`) | `B³ → (1-t)⁻¹B^{5/2}` | factor `B^{1/2}(1-t)⁻¹ ≤ 1·(1-t)⁻¹` (needs `B≤1`, `1-t ≤ 1`) |
| `I₂,I₃,J₂,J₃` (`LWExpI23K`) | `B²·η⁻¹·B^{1/2}`: `X_{a₁}X_{a'} ≺ B²` (`LWAvgLaw`), `W^{-2d}Σ|G_{xα}G_{αy}G_{xy}| ≺ η⁻¹ B^{1/2}` (Cauchy–Schwarz + Ward `Σ_α|G_{xα}|² = Im G_{xx}/η`; `STLocalEntry`) | exponent `2 + 1/2 = 5/2`, slack 0; `η⁻¹ → √(2/κ)(1-t)⁻¹` |
| `I₄₁, J₄₁` (`LWExpI41K`) | `η⁻¹B³` (`X ≺ B`, `D=(𝓛-𝒦)^{(2)} ≺ B²`, `STLK`; one Ward factor `η⁻¹`) | `η⁻¹B³ ≤ η⁻¹B^{5/2}`, slack `B^{1/2}` |
| `I₄₂, J₄₂` (`LWExpG5'`) | `η⁻¹B^{5/2}` at `x≠y`; `x = y` term `W^{-2d}·W^d·η⁻¹B²` needs `W^{-d} ≤ B^{1/2}` (paper `B:72`, `B:85`; owed LW-14c) | `W^{-3} = 3.05e-5 ≤ B^{1/2}` at n=0, tInst (`B^{1/2} = 5.7e-3`) |
| index set | `ĝ²/L^d ≤ 1-t` carried by `LWExpG5'`, `LWCutExp` only | nonempty at instance (col. 9 below) |
| `LWExpKer SB` | `SB` supported on `zdistD ≤ 1`, entries `≤ 1`: `C = e^c`, any `c` | `zdistInf_le_zdistD` (Defs/Sizes:117) |
| `LWExpKer K⁺` | `lwSplus_decay` (LWSizeClaim:1353) + `lwSpOf_eq` (:165; `K⁺_{ab} = W^d S⁺_{xy}`), `lwBdist = zdistD ≥ zdistInf`; uniform in `u<1`, `|E|≤2-κ`, `0<lam≤Λ` | `0<lam≤Λ` holds only eventually (`KLFinal_flowLam`) while `LWExpKer` is `∀ n`: finite-`n` patch `C := max(C*, max_{n<n₀} …)` (each `K⁺_n` is a finite matrix) |
| `LWExpKer (S^B K⁺)` (**missing from target 3**) | `(S^BK⁺)_{ac} = Σ_{b: |a-b|₁≤1} S^B_{ab}K⁺_{bc}`: `C' = (2d+1)e^c C`, `c` unchanged (triangle inequality) | needed by `J₁–J₃, J₄₁` (kernel `S^BK⁺`, see (ii)); row sums `≤ C' Σ_{a∈Z^d} e^{-c|a|_∞} = 49.98 C'` (`c=1`, `d=3`, uniform in `L`) |
| `t S^BK⁺ = m⁻²(K⁺ - tS^B)` | from `m²K⁺ = Θ - 1`, `S^B`, `Θ` commute; needed only for `J₄₂` (`LWExpG5'` has first kernel `K⁺` or `S^B`) | `mat.py`: errors `≤ 3e-16` at `(E,t) = (0.6,.5), (1.7,.95), (1.9,.999)` |
| `Σ_a|K_{ab}|` for `K⁺` | `|1 - t m²| = 0.624` at `E=1.9, t=0.999` (bounded away from 0 as `t→1`, `|E|≤2-κ`), so `Θ` decays uniformly | max row sum `|K⁺| = 2.38`, `|Θ| = 3.12` (vs `(1-t)⁻¹ = 1000`) |

### (ii) One concrete nondegenerate instance
`d=3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`; Defs/Sizes:260), `z0 n = 1/2 + i N^{-4/5}` (Induction/Defs:413), `t = tInst = 1/16` and `t = tEnd = lemT(z0 n)`; `STFlow` is merged `flow_z0`. The pins `LWAvgLaw, STLK, STLmax, STLocalEntry, STDecay` and the four term pins stay hypotheses (other gates' pins).
```
$ cd $SP/T2243 && python3 pre.py     # mpmath, 60 digits
n N t-case t<=lemT t<1 |E|<=2-k |m|-1 eta^-1(1-t)/sqrt(2/k) lam^2/L^3<=1-t log10(B) B^3<=B^2.5 W^3*B
0 2.097e+06 tInst True True True -7.8e-62 0.2309 True -4.4808 True 1.0830556
0 2.097e+06 tEnd True True True -7.8e-62 0.2309 True -0.76142 True 5675.8551
1 5.498e+11 tInst True True True 0.0 0.2309 True -9.002 True 1.0687499
1 5.498e+11 tEnd True True True 0.0 0.2309 True -1.702 True 21325190.0
2 8.125e+14 tInst True True True 0.0 0.2309 True -11.644 True 1.067284
2 8.125e+14 tEnd True True True 0.0 0.2309 True -2.2497 True 2.6455802e+9
5 2.13e+20 tInst True True True 0.0 0.2309 True -16.16 True 1.0667438
5 2.13e+20 tEnd True True True 0.0 0.2309 True -3.1794 True 1.0194049e+13
50 1.143e+37 tInst True True True 0.0 0.2309 True -30.101 True 1.0666668
50 1.143e+37 tEnd True True True 0.0 0.2309 True -6.0088 True 1.3187518e+24
sqrt(2/kappa) = 4.47214  ; 16/15 = 1.0666667
```
(col. 8 is `η⁻¹(1-t)/√(2/κ) = 0.2309`, i.e. `η⁻¹ = 1.033 (1-t)⁻¹ ≤ 4.472 (1-t)⁻¹`; col. 9 is `ĝ²/L^d ≤ 1-t`, a nonempty index set.) Limit computation for the external `LWAvgLaw` (target `B`): at `tInst`, `W^d B → 1/(0 + 15/16) = 16/15` (`tInst` rows n=1,2,5,50), so `B ~ 1.07 W^{-3} → 0`; `B<1` at every row, so `B³ ≤ B^{5/2}`. Kernel facts at the instance (`ker.py`, `c = 1`, `zdistInf`, `n = 0,1,2`, `L = 4,8,12`): `max|SB|e^{|a-b|} ≤ 1.0`, `max|K⁺|e^{|a-b|} = 0.059` (tInst), `0.516` (tEnd), `max|S^BK⁺|e^{|a-b|} ≤ 0.516`, row sums `≤ 0.516`: `LWExpKer` holds for `SB`, `K⁺`, `S^BK⁺` with `c = 1`, `C = 1` at these `n`.

```
$ python3 ker.py   # sz0, E=lemE(z0 n), K+ = t SB Theta, c=1, |.|=zdistInf
n   L   t-case  c  C_SB=max|SB|e^{c|a-b|}  C_K+  C_SBK+   rowsum|K+|  rowsum|SB K+|  (c=1, |.|=zdistInf)
0 4 tInst 1 0.9985 0.0592 0.0591 0.0592 0.0592
0 4 tEnd 1 0.9985 0.5160 0.5153 0.5164 0.5164
1 8 tInst 1 1.0000 0.0592 0.0592 0.0592 0.0592
1 8 tEnd 1 1.0000 0.5164 0.5164 0.5164 0.5164
2 12 tInst 1 1.0000 0.0592 0.0592 0.0592 0.0592
2 12 tEnd 1 1.0000 0.5164 0.5164 0.5164 0.5164
$ python3 mat.py   # d=3,L=3,W=2,lam=1/2: lift / split / hSp identities, row sums
E=0.6 t=0.5: |m|=1.000000000000000 |1-t m^2|=1.439  lift err 3.3e-16  split err 2.7e-16  hSp err 3.1e-16  m^2K+=Theta-1 err 1.3e-15
    max row sum |K+| = 0.414  |SB K+| = 0.359  |Theta| = 1.111  (1/(1-t)=2)
E=1.7 t=0.95: |m|=1.000000000000000 |1-t m^2|=1.028  lift err 3.6e-16  split err 2.1e-16  hSp err 3.4e-16  m^2K+=Theta-1 err 4.9e-16
    max row sum |K+| = 1.312  |SB K+| = 1.060  |Theta| = 1.959  (1/(1-t)=20)
E=1.9 t=0.999: |m|=1.000000000000000 |1-t m^2|=0.624  lift err 4.5e-16  split err 2.1e-16  hSp err 4.3e-16  m^2K+=Theta-1 err 4.8e-16
    max row sum |K+| = 2.378  |SB K+| = 1.963  |Theta| = 3.116  (1/(1-t)=1000)
```

**Identities (target 5, 6; both `σo = ±`)**, complex Hermitian Gaussian sample `d=3, L=3, W=2`, `lam=1/2`, `E=0.6`, `t=0.5` (`N=216`), exact arithmetic up to rounding; `E|X_xy|² = W^{-d}S^B`. `mat.py`: `lwSpOf = t Lift(S^BΘ)`, `S⁺(1-m²S) = S`, `t S^BK⁺ = m⁻²(K⁺-tS^B)`, all `≤ 4.5e-16`. `path.py` writes each of the eight `(Oe2x)` terms at fine level and each of the ten terms as loops with `W^d, m, t, K⁺` prefactors: `I₁ = m Σ S^B_{a₁ac} X_{a₁} 𝓛^{(2)}_{(+,σo),(ac,ao)}`, `J₁ = m³ Σ (S^BK⁺)_{a₁ac}X_{a₁}𝓛^{(2)}`, `I₂/I₃ = m t W^d Σ S^B S^B X X 𝓛^{(3)}_{(+,+,σo),(ac,ao)}`, `J₂/J₃` the same with kernel `S^BK⁺` and prefactor `m³ t W^d`, `I₄₁ = m t W^d Σ S^BS^B X_{a₁}𝓛^{(2)}_{(σo,+),(ao,a₂)}𝓛^{(2)}_{(σo,+),(a₃,ac)}`, `J₄₁ = m³ t W^d Σ (S^BK⁺)_{a₁a₃}S^B_{a₃a₄}(…)`, `I₄₂ = m t W^d Σ S^BS^B 𝓛^{(5)}_{(+,+,+,+,σo),(a₂,a₁,a₃,ac,ao)}`, `J₄₂ = m W^d Σ (K⁺ - tS^B)_{a₁a₃}S^B_{a₃a₄}𝓛^{(5)}`:
```
$ cd $SP/T2243 && python3 path.py
sigma_o=-: |LWcut|=1.6e-05, rel |block-def - fine-def| = 4.4e-16
   fine term (T_i) vs loop form, abs diff / |term|: I1:1e-16 J1:4e-16 I2:7e-17 J2:4e-15 I3:6e-16 J3:3e-15 I41:2e-15 I42:5e-16 J41:1e-15 J42:9e-16
   rel |sum of the 8 Oe2x terms (fine) - sum of the 10 loop-form terms| = 1.7e-15
sigma_o=+: |LWcut|=2.7e-06, rel |block-def - fine-def| = 6.2e-16
   fine term (T_i) vs loop form, abs diff / |term|: I1:2e-16 J1:4e-15 I2:3e-16 J2:2e-15 I3:7e-16 J3:4e-15 I41:2e-15 I42:2e-16 J41:2e-15 J42:2e-15
   rel |sum of the 8 Oe2x terms (fine) - sum of the 10 loop-form terms| = 9.9e-16
$ python3 triple.py    # pathwise (Oe2x) at 4 triples (x=alpha,y,y'), f = c_alpha G(sigo)_{yy'}, d_h by Leibniz with dh G_ij = -G_{i a}G_{b j}, dh Gbar_ij = -conj(G_{ib}G_{aj})
sigma_o=-: max over 4 triples |(LHS - sum T1..T8) - (-m sum_w (d_xw + m^2 S+_xw) Z_w)| = 2.3e-18 (rel to |LHS| 1.6e-15); |Z|max sample = 1.18e-05
sigma_o=+: max over 4 triples |(LHS - sum T1..T8) - (-m sum_w (d_xw + m^2 S+_xw) Z_w)| = 2.5e-18 (rel to |LHS| 1.3e-15); |Z|max sample = 4.90e-06
$ python3 conj.py
max rel |conj LWcut(false,so,ac,ao) - LWcut(true,!so,ao,ac)| over so, 3 block pairs = 4.9e-16
t=0: |LWcut| = 0.0  |X| max = 1.11e-16
```
Consequences: the `E`-identity `𝔼 LWcut = Σ ten terms` holds because `𝔼 Z_w = 0` (merged `integral_oe2xDefect`); `J₄` needs `LWExpG5'` (first kernel `K⁺`) and `J₁–J₃, J₄₁` need kernel `S^BK⁺` (ticket's (ii) reading confirmed, with the refinement in the table); the orientation `Lloop ![σ…] ![v…] = tr Π G^{σ_i}E_{v_i}` (E-label = column index of `G_i`) gives `p.2 = (ac, ao)` in `LWExpI23K`, `(ao, ac)` in `LWExpI41K`, `LWExpI1K`, and `(a₂,a₁,a₃,p.1.2 1,p.1.2 0)` in `LWExpG5'`.

**Evidence for the new charge case `σo = +` (`s = true`) and for `K⁺`** (MC, 500 samples, same size; evidence only, `L=3` is far from asymptotic): `|𝔼 Q| / bound`, max over block pairs `(ac,ao) ∈ {(4,4),(4,11),(0,13)}`, bounds `B³` (`I₁K`), `η⁻¹B^{5/2}` (`I23K`, `G5'`), `η⁻¹B³` (`I41K`); `Q` with `K = S^B` and `K = S^BK⁺` (`I1K, I23K, I41K`), first kernel `S^B` / `K⁺` (`G5'`):
```
$ python3 mc.py 500
t=0.5: Bctl=0.1759 eta^-1 B^3=1.142e-02 eta^-1 B^2.5=2.722e-02 B^3=5.445e-03  (500 samples, 210s)
  sigma_o=-: |E|/bound max over 3 block pairs: I1K_SB:0.08 I1K_SBKp:0.02 I23K_SB:0.00 I23K_SBKp:0.00 I41K_SB:0.03 I41K_SBKp:0.01 G5_SB:0.01 G5_Kp:0.00
      E[LWcut - sum ten terms]: max z-score over pairs = 1.67
  sigma_o=+: |E|/bound max over 3 block pairs: I1K_SB:0.03 I1K_SBKp:0.01 I23K_SB:0.00 I23K_SBKp:0.00 I41K_SB:0.01 I41K_SBKp:0.00 G5_SB:0.00 G5_Kp:0.00
      E[LWcut - sum ten terms]: max z-score over pairs = 1.10
t=0.9: Bctl=0.4034 eta^-1 B^3=6.884e-01 eta^-1 B^2.5=1.084e+00 B^3=6.567e-02  (500 samples, 203s)
  sigma_o=-: |E|/bound max over 3 block pairs: I1K_SB:0.02 I1K_SBKp:0.01 I23K_SB:0.00 I23K_SBKp:0.00 I41K_SB:0.01 I41K_SBKp:0.00 G5_SB:0.00 G5_Kp:0.00
      E[LWcut - sum ten terms]: max z-score over pairs = 1.61
  sigma_o=+: |E|/bound max over 3 block pairs: I1K_SB:0.00 I1K_SBKp:0.00 I23K_SB:0.00 I23K_SBKp:0.00 I41K_SB:0.00 I41K_SBKp:0.00 G5_SB:0.00 G5_Kp:0.00
      E[LWcut - sum ten terms]: max z-score over pairs = 2.02
$ python3 misc.py   # (+,+) 2-loops are not >= 0; |L2(+,+;(u,v))| <= 1/2 (L2(-,+;(u,v)) + L2(-,+;(v,u))), both >= 0
d=3: sum_(a in Z^3) exp(-1.0|a|_inf) = 49.9790  (bounds row sums of any LWExpKer kernel by C*this, uniformly in L)
d=3: sum_(a in Z^3) exp(-0.5|a|_inf) = 387.9849  (bounds row sums of any LWExpKer kernel by C*this, uniformly in L)
min Re L2(-,+) = 0.00023057371407412636  max|Im L2(-,+)| = 0.0
max_{u,v} |L2(+,+;(u,v))| / (1/2 (L2(-,+;(u,v)) + L2(-,+;(v,u)))) = 0.772979560729296
|L2(+,+)| / L2(-,+) sum rule: max_u sum_v |L2(+,+;(u,v))| = 0.1758926767822206  vs Ward bound max_u Im L1+_u/(W^d eta) = 0.27284981628172966
```
The `(+,+)` case of `LWExpI41K` (`I₄₁ = m t W^d Σ … 𝓛^{(2)}_{(+,+),(ao,a₂)}𝓛^{(2)}_{(+,+),(a₃,ac)}`, since `∂_{βα}G_{yx} = -G_{yβ}G_{αx}`) differs from the merged `s = false` proof only in the factor `A`: `|A| ≤ ½(A⁻ + A⁻ᵀ)` with `A⁻ = Σ|G|² ≥ 0`, then Ward on each (first or last label summed); `STKward`/`STKbound` hold at all charges (`STKward`, Step34Pins:229, `∀ σ : Fin k → Bool`), `KLK_rotate` at `(+,+)`. `LWExpG5'` at `s = true` is not refuted (MC consistent; the paper's argument `B:80-108` uses only edge counts and Cauchy–Schwarz); it is not proved here (LW-14c).

§29 checklist: (1) `0≤t≤lemT z` unchanged, `t<1`, `t=0` separate; (2) `LWExpG5'`, `LWCutExp` carry `ĝ²/L^d ≤ 1-t`, kernel pins none; (3) no `L^d ≤ W^K`; (4) `∀ n` premises as `LWtermEXP`; `LWExpKer` `∀ n` via the finite patch; (5) deterministic left sides; (6) `0<lam≤Λ` eventually only (patch above); (7) scale `N`, control `sz.Bctl n (t n)`.

### Verdicts
- Target 1 (vocabulary): PASS.  Target 2 (four pins): PASS (`I1K, I23K, I41K` at `s=true` by the AM-GM variant above; `G5'` not refuted).
- Target 3 (kernel facts): PASS, but the list is incomplete: `J₁–J₃, J₄₁` need `LWExpKer` of `S^B K⁺` (row `LWExpKer (S^BK⁺)`); the split identity is needed for `J₄₂` only.
- Target 4 (conjugation): PASS (`conj.py`).  Target 5 (expansion, `t=0`): PASS.  Target 6 (identification): PASS (`path.py`).
- Target 7 (assembly): PASS (exponents in the table).  Targets 8, 9: PASS (index maps `p ↦ ((false,false),p)`, `K = S^B`, `s = false`; hypotheses of the pins coincide).  Target 10 (instances): PASS (numbers above).

## (b) Script output (written Tue Oct  6 03:55:27 UTC 2026)
$ lake build RBM3D.Graph.LWExpTerm2 2>&1 | tail -n 2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3856 jobs).
$ lake build 2>&1 | tail -n 1   # whole library, `#assert_rbm_axioms` included
Build completed successfully (4045 jobs).
$ git log --oneline -1; git diff --stat main...t/T2243; grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Graph/LWExpTerm2.lean
7fc8e8e T2243: LW-14b Graph/LWExpTerm2 (expansion side of lem:LWterm_EXP: lwCutExp_of_terms)
 RBM3D/Graph/LWExpTerm2.lean | 2116 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    4 +
 2 files changed, 2120 insertions(+)
0
$ #print axioms <six required declarations>   (scratch file; output lines)
'RBM.Gauss.Sizes.lwCutExp_of_terms' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpG5_of_G5'' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI1_of_K' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpI41_of_K' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_ker_SB' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwExpTerm2_ker_Kp' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm2_inst_ker_Kp' [propext, Classical.choice, Quot.sound]
$ lake env lean pre.lean   # `import RBM3D` + `import RBM3D.Graph.LWExpTerm2` + `#assert_rbm_axioms`
axiom audit: 7104 theorems, 2389 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.LWExpI1K: 4 [no certificate]
  RBM.Gauss.Sizes.LWExpI23K: 2 [no certificate]
  RBM.Gauss.Sizes.LWExpI41K: 4 [no certificate]
  RBM.Gauss.Sizes.LWExpG5': 4 [no certificate]
registry: 2 borrowed + 147 owed + 90 structural + 7 refuted; 114 registered premise(s) carry nothing yet: [RBM
exit=0
$ git diff main...t/T2243 -- RBM3D/Test/Axioms.lean | grep '^+ '   # registered in `owedProps` (none in `structuralProps`; `LWExpKer` is not listed by the pre-check)
+   `RBM.Gauss.Sizes.LWExpI1K, -- `I₁`, `J₁` (`(eq:termI1)`, `B:37-41`) with a decaying first kernel `K`, premise of `
+   `RBM.Gauss.Sizes.LWExpI23K, -- `I₂`, `I₃`, `J₂`, `J₃` (`(eq:termI2)`, `B:43-49`) with a decaying first kernel `K`,
+   `RBM.Gauss.Sizes.LWExpI41K, -- `I₄₁`, `J₄₁` (`(eq:termI41)`, `B:57-70`) with a decaying first kernel `K` and the 2
+   `RBM.Gauss.Sizes.LWExpG5', -- `I₄₂`, `J₄₂` (`(eq;I42inG)`, `(eq;EGxy:x=y)`) with first kernel `S^{(B)}` or `K⁺` an
$ lake env lean sec2check2.lean   # check file section 2 + 6 `Iff.rfl`/`rfl` examples (pins) + `@name` for targets 7-9
exit=0
$ python3 extract.py <targets>   # statements copied from RBM3D/Graph/LWExpTerm2.lean (name, line)
-- lwCutExp_of_terms (line 1956)
theorem lwCutExp_of_terms (d : ℕ) :
    LWExpI1K d → LWExpI23K d → LWExpI41K d → LWExpG5' d → LWCutExp d := by
-- lwExpG5_of_G5' (line 2027)
theorem lwExpG5_of_G5' (d : ℕ) : LWExpG5' d → LWExpG5 d := by
-- lwExpI1_of_K (line 2037)
theorem lwExpI1_of_K (d : ℕ) : LWExpI1K d → LWExpI1 d := by
-- lwExpI41_of_K (line 2043)
theorem lwExpI41_of_K (d : ℕ) : LWExpI41K d → LWExpI41 d := by
-- lwExpTerm2_ker_SB (line 1741)
theorem lwExpTerm2_ker_SB : LWExpKer sz (fun n => SB d (sz.L n) (sz.lam n)) := by
-- lwExpTerm2_ker_Kp (line 1794)
theorem lwExpTerm2_ker_Kp (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) :
    LWExpKer sz (fun n => LWExpKp sz n (STflowE z n) (t n)) := by
-- lwExpTerm2_Kp_split (line 1173)
theorem lwExpTerm2_Kp_split (E t : ℝ) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (t : ℂ) • (SB d (sz.L n) (sz.lam n) * LWExpKp sz n E t) =
      ((mE E) ^ 2)⁻¹ • (LWExpKp sz n E t - (t : ℂ) • SB d (sz.L n) (sz.lam n)) := by
-- lwExpTerm2_cut_conj (line 1627)
theorem lwExpTerm2_cut_conj (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (starRingEnd ℂ) (LWcut sz n E t false σ ac ao ω) = LWcut sz n E t true (!σ) ao ac ω := by
-- lwExpTerm2_cut_expand (line 1516)
theorem lwExpTerm2_cut_expand (hG : GaussIBP sz) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    (σ : Bool) (ac ao : Zd d (sz.L n)) :
    ∫ ω, LWcut sz n E t true σ ac ao ω ∂(sz.seqP) =
      lwExpTerm2_Pa sz n (lwExpTerm2_KK sz n E t) E t σ ac ao +
        (t : ℂ) * lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n E t) E t true σ ac ao +
        (t : ℂ) * lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n E t) E t false σ ac ao +
        mE E * lwExpTerm2_Pd sz n (LWExpKp sz n E t) E t σ ac ao +
        (t : ℂ) * lwExpTerm2_Pc sz n (lwExpTerm2_KK sz n E t) E t σ ac ao := by
$ grep -nE '^(theorem|def) lwExpTerm2_inst_' RBM3D/Graph/LWExpTerm2.lean   # compiled instances, `d = 3`, `sz0`, `z0`, `tInst`, `n = 0` where a size is fixed
2064:theorem lwExpTerm2_inst_cut (h1 : LWExpI1K 3) (h23 : LWExpI23K 3) (h41 : LWExpI41K 3) (h5 : LWExpG5' 3)
2074:theorem lwExpTerm2_inst_ker_SB : LWExpKer sz0 (fun n => SB 3 (sz0.L n) (sz0.lam n)) :=
2077:theorem lwExpTerm2_inst_ker_Kp : LWExpKer sz0 (fun n => LWExpKp sz0 n (STflowE z0 n) (tInst n)) :=
2081:theorem lwExpTerm2_inst_ker_KK : LWExpKer sz0 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n)) :=
2086:theorem lwExpTerm2_inst_expand :
2100:theorem lwExpTerm2_inst_conj (ω : sz0.SeqΩ) :
2105:theorem lwExpTerm2_inst_Kp_split :
2112:theorem lwExpTerm2_inst_G5 (h : LWExpG5' 3) : LWExpG5 3 := lwExpG5_of_G5' 3 h
2113:theorem lwExpTerm2_inst_I1 (h : LWExpI1K 3) : LWExpI1 3 := lwExpI1_of_K 3 h
2114:theorem lwExpTerm2_inst_I41 (h : LWExpI41K 3) : LWExpI41 3 := lwExpI41_of_K 3 h
$ grep -rwFf names.txt RBM3D docs/tickets/checks | <drop LWExpTerm2.lean, T2243-check.lean> | per-file count   # names.txt = the 150 declared names
   4 RBM3D/Test/Axioms.lean
$ # no port from RBM1D/RBM2D (no file copied, no `git -C ../RBM2D` command run); copied within RBM3D: the bounded-measurable section
204:/-! ## 3. Bounded measurable random variables (integrability of every random term) -/
278:end LoopBM
23d83c4
$ grep -nE '^(private )?(noncomputable )?(theorem|def|abbrev) ' RBM3D/Graph/LWExpTerm2.lean   # every declaration (150), name:line; `~` = `lwExpTerm2_`; all `lwExpTerm2_`-prefixed or pinned; `private`: `~vec1` only
LWExpKer:70 LWExpKp:76 LWExpI1K:81 LWExpI23K:96 LWExpI41K:115 LWExpG5':132 ~dw:156 ~dw_sum:160 ~dw_blocks:166
~dw_mul:171 ~dw_mul_self:176 ~lift_sum:183 ~keyQ:194 ~L2:226 ~L3:230 ~L4:234 ~Xv:239 ~sum3_rot:244 ~sum3_rot':249
~sum4_rot':253 ~sum4_rot:260 ~sum3_rev:265 ~L3_cov:271 ~S_sum:281 ~eval1:287 ~eval3:309 ~eval5:338 ~eval7b:378
~eval7a:413 ~Phi:449 ~five:460 ~evalJ:475 ~alg:486 ~Q8:526 ~trace_prod1:582 ~trace_prod2:586 ~trace_prod3:590
~trace_prod4:594 ~trace_prod5:598 ~bl:607 ~gres_blockMat:614 ~Eblk_reindex:627 ~trace_reindex:634 ~loop_eq:641 ~w:662
~Lloop1:665 ~Lloop2:672 ~Lloop3:679 ~Lloop5:687 ~Gsm:719 ~M1:723 ~tame1_Xv:727 ~tame1_Gsm:732 ~dh:741 ~P:784
~lwPoly:789 ~triple:798 ~hc:830 ~hS:841 ~hSp:851 ~Gt_false:862 ~Gt_eq_Gsm:873 ~tame_Gm:883 ~tame_M1:886 ~tame_Phi:891
~integral_sum3:925 ~integral_weighted:936 ~cutRHS:951 ~block:960 ~fiveA:1028 ~kk_collapse:1037 ~assemble:1046 ~BM:1091
~BM_const:1098 ~BM_mul:1101 ~BM_add:1109 ~BM_sub:1115 ~BM_sum:1121 ~BM_integrable:1131 ~BM_Lloop:1143 ~BM_X:1148
~BM_LWcut:1154 ~Kp_split:1173 ~tKK:1199 ~integral_add5:1222 ~integral_wsum1:1232 ~integral_wsum2:1238
~integral_wsum3:1248 ~KK:1263 ~KK_apply:1267 ~Xv_eq:1272 ~fiveL:1284 ~five_eq:1291 ~cutRHS_eq:1300 ~LWcut_true:1308
~BM_fiveL:1320 ~XL3_eq:1334 ~Rtot:1342 ~cut_eq_Rtot:1347 ~e1:1384 ~e3:1388 ~e4:1395 ~e5:1401 ~Rtot_eq:1406 ~Pa:1434
~Pb:1439 ~Pc:1446 ~Pd:1452 ~int_e1:1457 ~int_e3:1469 ~int_e4:1486 ~int_e5:1502 ~cut_expand:1516 ~conj_Gt:1547
~conj_w:1557 ~conj_Lloop1:1562 ~Gt_ct:1569 ~L3_trace:1576 ~conj_Lloop3:1587 ~conj_SB:1621 ~cut_conj:1627
~zdistInf_add_le:1645 ~ker_of_eventually:1655 ~ker_add:1684 ~ker_smul:1709 ~ker_one:1718 ~SB_support:1729 ~ker_SB:1741
~ker_SB_mul:1759 ~ker_Kp:1794 ~ker_KK:1843 ~vec1:1863 ~cut_zero:1869 ~eta_inv_le:1876 ~bound_true:1888
~norm_cut_false:1944 lwCutExp_of_terms:1956 lwExpG5_of_G5':2027 lwExpI1_of_K:2037 lwExpI41_of_K:2043 ~inst_cut:2064
~inst_ker_SB:2074 ~inst_ker_Kp:2077 ~inst_ker_KK:2081 ~inst_expand:2086 ~inst_conj:2100 ~inst_Kp_split:2105
~inst_G5:2112 ~inst_I1:2113 ~inst_I41:2114

### Narrative (every number below is in the script output above or in the file)
- Result: `RBM3D/Graph/LWExpTerm2.lean` (2116 lines, 150 declarations, one `private`), no `sorry`/axiom, builds without warnings; commit 7fc8e8e on `t/T2243`; `git diff main...t/T2243` = the file + 4 registry lines. All ten targets are delivered; the four term pins (`LWExpI1K`, `LWExpI23K`, `LWExpI41K`, `LWExpG5'`) are stated verbatim and stay hypotheses of target 7 (other gates).
- Route (header of the file): (i) block-level algebra with no probability, §2-§4, §8: weights `dw_a(x) = W^{-d} 1[x ∈ [a]]`, loops as nested sums, `lwExpTerm2_keyQ`, the five evaluations `lwExpTerm2_eval1/3/5/7a/7b`; (ii) `Lloop` as nested sums of `G_t(σ)` (`lwExpTerm2_Lloop1/2/3/5`, `blockMat`/`Eblk` bridge); (iii) `(Oe2x)` at one triple `(α,c,o)` for `f = X_a Ĝ_{co}` as `lwPoly` (`lwExpTerm2_triple`: `oe2x_integral` + `lwExpTerm2_dh` + the regrouping `lwExpTerm2_Q8`), summed over `α∈[a₂]`, `c∈[ac]`, `o∈[ao]` (`lwExpTerm2_block`); (iv) linearity of `∫` through bounded-measurable terms (copy of `LWExpTerm.lean:204-278`, private there).
- Deviation from the ticket's ten-term plan (targets 5, 6): `(Oe2x)` is `m Φ_α + m³ Σ_v S⁺_{αv} Φ_v`, so the `I`- and `J`-terms are never separated: all five loop-level terms carry `K = S^{(B)}(m + m³K⁺)` (`lwExpTerm2_KK`). `I₁+J₁ = P_a`, `I₂+J₂ = t P_b(true)`, `I₃+J₃ = t P_b(false)`, `I₄₁+J₄₁ = t P_c`, `I₄₂+J₄₂ = m P_d` (first kernel `K⁺`, by `lwExpTerm2_tKK`: `t S^{(B)}(m + m³K⁺) = m K⁺`, from `lwExpTerm2_Kp_split`). So `LWExpI1K/I23K/I41K` are used at `K = lwExpTerm2_KK` (its `LWExpKer` is `lwExpTerm2_ker_KK`: the row "LWExpKer (S^B K⁺)" of section (a)), and `LWExpG5'` only at `p.1.1.1 = true`; its `S^{(B)}` branch is used by target 8 only.
- `LWExpKer` is `∀ n` but `0 < ĝ ≤ 𝔡⁻¹` holds eventually (`(eq:WO)`, `hz.1.2.2.2.2`): `lwExpTerm2_ker_of_eventually` patches the constant by the finite sum over `n < n₀` (the "finite-n patch" of (a)).
- `t = 0`: `lwExpTerm2_cut_zero` (`Lloop_zero_one`); `σ_c = -`: `lwExpTerm2_cut_conj` (cyclic rotation of the 3-loop, `Matrix.trace_conjTranspose`, `Matrix.trace_mul_comm`), then the pinned bounds at `(σ, ac, ao) := (-σ_o, a_o, a_c)`.
- `≺`-assembly (`lwCutExp_of_terms`): `η_t⁻¹ ≤ (2/√(2κ))(1-t)⁻¹` (`lwExpTerm2_eta_inv_le`, `st6_mE_im_ge`), `B ≤ 1` eventually (`st5_Bctl_le_one`) so `B³ ≤ B^{5/2}`, `N^{τ/2} ≥ 1 + 4c` eventually; bound `N^{τ/2}(1+4c)(1-t)⁻¹B^{5/2} ≤ N^τ(1-t)⁻¹B^{5/2}`. The pins are applied at `((true,![σ,true]),![ao,ac])`, `((sel,σ),![ac,ao])` (both `sel`), `((true,σ),![ao,ac])`, `⟨((true,σ),![ao,ac]),hg⟩` (`hg`: the index set `ĝ²/L^d ≤ 1-t`).
- No hypothesis was added, no pinned signature changed (script: `Iff.rfl` for the six pins, `@name` for targets 7-9). `lwExpTerm2_ker_Kp`/`_KK` take `3 ≤ d`, `0 < κ`, `STFlow`, `0 ≤ t ≤ lemT z` (they need `lwSplus_decay`, `st5_t_lt_one`).
- Instances (`d = 3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `sz0`, `z0`, `tInst = 1/16`; `sz0_values`: `L 0 = 4`, `W 0 = 32`): `lwExpTerm2_inst_cut` (target 7 into `lwTermEXP_of_cut`, `inst_LWtermEXP`; the four pins and the five ST laws are hypotheses), `_ker_SB/_ker_Kp/_ker_KK` (no hypothesis), `_expand`, `_conj`, `_Kp_split` (at `n = 0`, `t = 1/16`, `gaussIBP sz0`), `_G5/_I1/_I41` (targets 8, 9).
- Registry: `LWExpI1K`, `LWExpI23K`, `LWExpI41K` (LW-14d) and `LWExpG5'` (LW-14c) added to `owedProps`; nothing deleted (`LWCutExp`, `LWtermEXP` stay owed); `LWExpKer` is not listed by the pre-check, `structuralProps` untouched.

## (c) Verified Mathlib names (script `names_check.lean`: `present: 29/29; missing among present-list: []`; `absent-list present in env: [] (expected: [])`)
- `Matrix.reindexAlgEquiv`, `Matrix.inv_submatrix_equiv`, `Matrix.trace_conjTranspose`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.diagonal_conjTranspose`, `Matrix.trace_mul_comm`, `Matrix.mul_diagonal`, `Matrix.conjTranspose_mul`, `map_list_prod`, `List.map_ofFn`.
- `MeasureTheory.integral_finsetSum`, `MeasureTheory.integrable_finsetSum`, `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul`, `integral_conj` (root namespace), `Complex.norm_conj`, `Complex.conj_ofReal`.
- `Real.rpow_le_rpow_of_exponent_ge'`, `Real.rpow_natCast`, `Real.rpow_add`, `Real.exp_le_exp`, `inv_anti₀`, `one_le_inv₀`.
- `Finset.sum_comm`, `Finset.sum_eq_single`, `Finset.sum_ite_eq'`, `Finset.single_le_sum`, `Finset.mul_sum`, `Finset.sum_mul`.
- Verified absent (do not use): `norm_add₅_le`, `Nat.pos_pow_of_pos`, `Finset.mul_add`, `MeasureTheory.integral_conj`; `import Mathlib` is not built in this tree (import `RBM3D.*` modules).

## (d) Open issues and paper-delta candidates
- Unproved pins now carried as hypotheses of `lwCutExp_of_terms`: `LWExpI1K`, `LWExpI23K`, `LWExpI41K` (LW-14d: kernel `K` with `LWExpKer`; the application needs only `K = lwExpTerm2_KK`), `LWExpG5'` (LW-14c: only the `p.1.1.1 = true`, `K⁺`, branch is needed for `LWCutExp`; the `S^{(B)}` branch for `LWExpG5`). `LWCutExp`, `LWtermEXP` stay owed. The `s = true` cases (`σ_o = +`) of `LWExpI41K`/`LWExpG5'` are neither proved nor refuted here (MC evidence in (a)).
- T2243a (`B:34`, "the `J_i` can be treated in exactly the same way"): `I_i` and `J_i` combine into one term with the kernel `m(1 - m²S)⁻¹ = m + m³S⁺`; for `i = 4₂` the 5-loop carries `K⁺ = t S^{(B)}Θ_{t m²}` as first kernel (`I₄₂ + J₄₂ = m·𝓛⁽⁵⁾[K⁺, S^{(B)}]`): this is `(eq;EGxy:x=y)` with an `S⁺` edge in place of `S_{γα}`, not a consequence of it as stated.
- T2243b (`B:14`, `σ = +` "analogous"): the 5-loop has charges `(+,+,+,+,+)` (`LWExpG5'` with `p.1.1.2 = true`), outside `σ₅ = (+,+,+,+,-)` of `(eq;EGxy:x=y)`; `I₄₁` has 2-loops of charge `(+,+)`.
- T2243c (`6:83-88`, last step): `η_t⁻¹ ≤ C (1-t)⁻¹` is used with the explicit `C = 2/√(2κ)` (`|E| ≤ 2-κ`); `B ≤ 1` eventually for `B³ ≤ B^{5/2}` (as T2236 rows 27-28).
- T2243d: `LWExpKer` is stated `∀ n` while its source `lwSplus_decay` needs `0 < ĝ ≤ 𝔡⁻¹` (eventually); the pin is true with the finite patch (`lwExpTerm2_ker_of_eventually`).

