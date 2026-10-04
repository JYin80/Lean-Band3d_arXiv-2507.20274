Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 05:05:33 UTC 2026
Notation: `J=univ.erase r` (`|J|=n-1`), `b=δ_r`, `s_j=δ_j-b`, `M=KLmaxDist δ`, `y_j=a_j-b`, `A=g²+(1-t)` (`=g²+|1-t|`, `t<1`), `B=Bparam d L g t 0=A⁻¹+(L^d(1-t))⁻¹`, `τ'=τ/3`, `f_j(x)=Theta(a_j,x)`, `φ^ξ_j(δ)=KLfξ(fun s=>f_j(b+s))(δ_j-b)`. All merged lemmas below are on `main` (`KLIndStepA.lean`, `KLMolecule.lean`); no private merged lemma is needed (no `open private`).
**(i) Exponent table and group bookkeeping** (target = `KLindStep_alt`, then `KLindStepAt_holds`, `KLindStepPin_holds`)
| # | quantity / step | value, constraint, merged lemma | slack |
|---|---|---|---|
| 1 | `d,n,σ,r` | `3≤d`, `3≤n`, `0<κ`, `0<gmax` (pin). Alternating ⇒ `n` even (`KLIndStepA_alt_cases`), so `n≥4`. `KLsumZero_weighted` is stated for **every** alternating `σ` (so `σ_alt` and `¬σ_alt`) and every `r`, `x`: no case split, `KLIndStepA_alt_cases` not needed. Long edge: `thetaEdge σ_i σ_{i+1}=Theta` (`KLIndStepA_thetaEdge_long`, `|E|≤2-κ≤2`); `σ_r≠σ_{r+1}` is automatic | `d-2≥1`, `n-3≥1` |
| 2 | Lean shape of the expansion | **`Finset.prod_add` twice** (no induction on `univ.erase r`): `KLf_split` at `s=δ_j-b` gives `f_j(δ_j)=φ⁰_j+φ¹_j+φ²_j` (`b+(δ_j-b)=δ_j`), `∏_J(φ²+(φ¹+φ⁰))=Σ_{V⊆J}(∏_Vφ²)·Σ_{U⊆J\V}(∏_Uφ¹)(∏_{J\V\U}φ⁰)`; `V`=`f₂`-positions, `U`=`f₁`-positions. `‖Σ_δ Σ(δ)∏_J‖≤Σ_{(V,U)}‖Σ_δ Σ(δ)·term_{V,U}(δ)‖` (`norm_sum_le` after `Finset.mul_sum`/`sum_comm`); then `Σ_b` | `3^{n-1}` pairs `(V,U)` (S1) |
| 3 | group of a pattern `ξ∈{0,1,2}^{n-1}` ⇔ `(V,U)` | `V={ξ=2}`, `U={ξ=1}`. (G0) `V=U=∅` (1 pattern). (G1) `V=∅,|U|=1` (`n-1`). (G2) `V≠∅` (`3^{n-1}-2^{n-1}`). (G3) `V=∅,|U|≥2` (`2^{n-1}-n`). Exactly one group per pattern; counts sum to `3^{n-1}` (S1, `n=4,6,8`). Distinguished factor: G2 any `i∈V` (`Finset.Nonempty`), G3 any two `i≠k∈U` (`Finset.one_lt_card`); no choice rule needed, each `(V,U)` is bounded separately | — |
| 4 | constants | `K`=`KLf_crude_bound`, `K₁₂`=`KLf12_bound` at `τ/3`, `C_s`=`KLsumZero_weighted` (.1), `W_d`, `W_{2d-2}`=`KLsumZero_weighted` (.2) at `Q=d, 2d-2`; `P₁=2^d(1+(d+1)^{τ'}/τ')`, `P₂=2^{2d+2}(1+(d+1)^{τ'}/τ')`. `C = C_s K^{n-2} + (3^{n-1}-2^{n-1}) K^{n-2}K₁₂W_dP₁ + (2^{n-1}-n) K^{n-3}K₁₂²W_{2d-2}P₂`; each constant is an `∃C` before `∀p` in the merged statement, so `C=C(d,n,κ,gmax,τ)`, never `L,g,t,E` (§29, constants clause) | `C>0` |
| 5 | loss split `L^τ` | G0: `L⁰`, uses `1≤L^τ` (`L≥3`). G2: one `KLf12_bound` (`L^{τ'}`) + one `KLlat_pow_dim_rpow` (`L^{τ'}`) = `L^{2τ/3}`. G3: two `KLf12_bound` (`L^{2τ'}`) + one `KLlat_pair_rpow` (`L^{τ'}`) = `L^{τ}`. So **`τ'=τ/3`** (not `τ/n`: only 2 distinguished factors carry a loss; the other factors use no-loss `KLf_crude_bound`); `L^{2τ/3}≤L^τ` (`1≤L`) | G3 exact `3τ'=τ`; G2 slack `τ/3` |
| 6 | `(eq:f12)` forms used | for every `s`: `‖f₁‖≤K₁₂L^{τ'}(g²+|1-t|)⁻¹(|s|+1)^{d-1}/(|y|+1)^{d-1}`, `‖f₂‖≤…(|s|+1)^{d}/(|y|+1)^{d}`; crude `‖f₀‖,‖f₁‖,‖f₂‖≤K B` | `q₁=d-1≥1`, `q₂=d≥2` |
| 7 | weights | only distinguished factors carry `(|s_j|+1)^q`; `|s_j|=zdistD(δ_j-δ_r)≤M` (`KLIndStepA_dist_le_maxDist`), so `Q=d` (G2, one factor), `Q=2(d-1)=2d-2` (G3, two factors); `Σ_{δ_r=b}‖Σ‖(M+1)^Q≤W_Q·A` uniformly in `b` (`x=b`) | `Q=3,4` at `d=3` |
| 8 | (G0) | `Σ_δΣ(δ)∏φ⁰=(∏_Jf_j(b))·Σ_{δ_r=b}Σ(δ)`; `‖slice‖≤C_s(1-t)`; `n-2` factors `≤KB`; one factor `j₀` summed: `Σ_b‖Theta(a_{j₀},b)‖≤(1-t)⁻¹` (`KLlat_sum_norm_Theta_row_le`, `3≤L,0≤t<1`): `≤C_sK^{n-2}B^{n-2}` | no loss; `(1-t)(1-t)⁻¹=1` exact |
| 9 | (G1) | `Σ_δΣ(δ)φ¹_i(δ)·∏_{j≠i}φ⁰_j` is `(∏φ⁰)·Σ_δΣ(δ)KLf1 f (δ_i-b)=0` (`KLslice_f1_vanish`, from `KLSigmaPi_reflect`; `hκ: 0<κ`) | exactly 0 (S2: ≤5e-13) |
| 10 | (G2) | `i∈V`: `≤K^{n-2}K₁₂L^{τ'}A⁻¹(y_i-term)(M+1)^d`; sum over `δ`: `W_dA` cancels `A⁻¹` exactly; `Σ_b(|y_i|+1)^{-d}≤P₁L^{τ'}` (`KLlat_pow_dim_rpow`, `d=k+2`) ⇒ `≤K^{n-2}K₁₂W_dP₁L^{2τ'}B^{n-2}` | `A⁻¹A=1` slack 0; exponent `d` borderline: `log L`, absorbed by `L^{τ'}` |
| 11 | (G3) | `i≠k∈U`: `≤K^{n-3}K₁₂²L^{2τ'}A⁻²(|y_i|+1)^{-(d-1)}(|y_k|+1)^{-(d-1)}(M+1)^{2d-2}`; `δ`-sum gives `W_{2d-2}A`; leftover `A⁻¹≤B` (`KLlat_inv_le_Bparam`) so `B^{n-3}B=B^{n-2}`; `Σ_b≤P₂L^{τ'}` (`KLlat_pair_rpow`, `k=d-2`) ⇒ `≤K^{n-3}K₁₂²W_{2d-2}P₂L^{3τ'}B^{n-2}` | decay `2d-2>d`, slack `d-2=1`; `B-A⁻¹=(L^d(1-t))⁻¹≥0` |
| 12 | `KLindStepAt_holds` | `3≤d`,`3≤n`,`0<κ`,`0<gmax`,`KLPT d κ gmax`; `by_cases ∀j σ_j≠σ_{j+1}`: yes ⇒ `KLindStep_alt`; no ⇒ merged `KLindStep_nonAlt` (it has the `σ_r≠σ_{r+1}` hypothesis of the pin); `C:=C_alt+C_nonAlt`, both terms `≥0` times `L^τB^{n-2}≥0`. `KLShort` from `KLShort_holds d κ gmax hd hκ hg` | `n=3` never alternating |
| 13 | §29 (1) time | `0≤t<1` from `KLPar.ht0/ht1`; the row sum needs both; `|1-t|=1-t` | — |
| 14 | §29 (2),(3),(4) | pin has no `W`, `ilambda`, `N`: (2),(3) do not arise. (2'): regimes `1-t ≷ g²,g²/L²,g²/L^d` all occur in S1 regime list (and the S2 grid); the bound is uniform since `A⁻¹≤B` and `(L^d(1-t))⁻¹` stay inside `B`. (4) `∀n≥3` in the pin: nothing imposed at finitely many `n` | — |
| 15 | external input | only `KLPT d κ gmax` (borrowed, `Test/Axioms.lean:79`); no new hypothesis `Prop`; `KLindStepPin` is proved here. Prover runs the registry pre-check (ticket) | — |
**(ii) One concrete instance and numerical check.** `d=3, κ=gmax=1, L=5, g=1/2, E=0, t=9/10` (`τ_t=1-t=0.1`; the probe `KLinst` data), `n=4`; `σ=KLsigAlt 4=(+,-,+,-)` with root `r=1`, and `¬σ_alt=(-,+,-,+)` with `r=2`; `|J|=3`; `L^τ` at `τ=1/2` is 2.2361 (S1). Scripts in `scratchpad/T2106/` (cwd for all commands; numpy; `Θ=(1-tμS^B)⁻¹` by FFT, `Bparam` as in `T2100/pre2.py` md5 145174ee…): `pre3.py` md5 c06f56d5…, `run_all2.py` ac1715f5…, `inst4.py` 7d198ae9…, `book.py` 83abf3ed…, `chk3.py` 57440ddc…. `Σ^{(∅)}` is exact: all non-crossing same-charge diagonal sets `F` (`TSP`, `Partition.lean:91`; `KLleafPar/KLnodePar`, `KLTree.lean:76-82`), tree contraction batched over `b`; `G0=(slice sum)·∏f₀`, `G1` computed explicitly (config 1 of each `L=9` task), `G2=T_full-T_{01}`, `G3=T_{01}-G0-G1` with `T_{01}` the sum with `f₀+f₁`.
```
$ python3 book.py   # S1: prod_add identity and group counts; regimes; hypotheses at the instance (exponent echo lines omitted here)
n=4 |J|=n-1=3: |prod(x+y+z) - sum_{V,U}| = 3.5e-15; #(V,U)=27=3^(n-1)=27; counts (V,U) {'G0': 1, 'G1': 3, 'G2': 19, 'G3': 4} ; counts xi {'G0': 1, 'G1': 3, 'G2': 19, 'G3': 4} ; formulas G2=3^(n-1)-2^(n-1)=19 G3=2^(n-1)-n=4 G1=n-1=3 G0=1; two distinct U-members in G3: True
n=6 |J|=n-1=5: |prod(x+y+z) - sum_{V,U}| = 3.0e-14; #(V,U)=243=3^(n-1)=243; counts (V,U) {'G0': 1, 'G1': 5, 'G2': 211, 'G3': 26} ; counts xi {'G0': 1, 'G1': 5, 'G2': 211, 'G3': 26} ; formulas G2=3^(n-1)-2^(n-1)=211 G3=2^(n-1)-n=26 G1=n-1=5 G0=1; two distinct U-members in G3: True
n=8 |J|=n-1=7: |prod(x+y+z) - sum_{V,U}| = 4.0e-14; #(V,U)=2187=3^(n-1)=2187; counts (V,U) {'G0': 1, 'G1': 7, 'G2': 2059, 'G3': 120} ; counts xi {'G0': 1, 'G1': 7, 'G2': 2059, 'G3': 120} ; formulas G2=3^(n-1)-2^(n-1)=2059 G3=2^(n-1)-n=120 G1=n-1=7 G0=1; two distinct U-members in G3: True
--- regimes tau vs g^2, g^2/L^2, g^2/L^3 (d=3) ---
L= 9 g=0.05 g2=0.0025 g2/L2=3.09e-05 g2/L3=3.43e-06 | 1:tau>g2 | 0.001:g2/L2<tau<=g2 | 1e-06:tau<=g2/L3
L= 9 g=0.5  g2=0.25 g2/L2=0.00309 g2/L3=0.000343 | 1:tau>g2 | 0.001:g2/L3<tau<=g2/L2 | 1e-06:tau<=g2/L3
L= 9 g=1    g2=1 g2/L2=0.0123 g2/L3=0.00137 | 1:g2/L2<tau<=g2 | 0.001:tau<=g2/L3 | 1e-06:tau<=g2/L3
L=17 g=0.05 g2=0.0025 g2/L2=8.65e-06 g2/L3=5.09e-07 | 1:tau>g2 | 0.001:g2/L2<tau<=g2 | 1e-06:g2/L3<tau<=g2/L2
L=17 g=0.5  g2=0.25 g2/L2=0.000865 g2/L3=5.09e-05 | 1:tau>g2 | 0.001:g2/L2<tau<=g2 | 1e-06:tau<=g2/L3
L=17 g=1    g2=1 g2/L2=0.00346 g2/L3=0.000204 | 1:g2/L2<tau<=g2 | 0.001:g2/L3<tau<=g2/L2 | 1e-06:tau<=g2/L3
--- instance: d=3 n=4 kappa=1 gmax=1 L=5 g=0.5 E=0 t=0.9 tau=1-t=0.1 ---
3<=d True 3<=n True 0<kappa True 0<gmax True 3<=L True 0<g<=gmax True |E|<=2-kappa True 0<=t<1 True sigma_alt alternating True not-sigma_alt alternating True
sigma_alt root r=1: sigma_r!=sigma_{r+1}: True ; erase r = [0, 2, 3] (|J|=n-1=3)
not sigma_alt root r=2: sigma_r!=sigma_{r+1}: True ; erase r = [0, 1, 3] (|J|=n-1=3)
A=g^2+1-t=0.3500 B_{t,0}=A^-1+(L^d(1-t))^-1=2.9371 ; A^-1<=B: True ; B^(n-2)=8.6268 ; L^tau for tau=1/2: 2.2361
$ python3 chk3.py 0; python3 chk3.py 1.5   # S5: validation of the contraction
E=0 n=4 tot vs pre2.lhs: max abs diff of sum_b|inner|/B^2 over 16 (a,r): 1.7e-13
E=1.5 n=4 tot vs pre2.lhs: max abs diff of sum_b|inner|/B^2 over 16 (a,r): 7.9e-14
E=0 n=6 r=0: DP vs brute force over node labels, 18 trees, max abs err 1.8e-16
E=0 n=6 r=3: DP vs brute force over node labels, 18 trees, max abs err 2.3e-16
E=1.5 n=6 r=0: DP vs brute force over node labels, 18 trees, max abs err 7.4e-16
E=1.5 n=6 r=3: DP vs brute force over node labels, 18 trees, max abs err 1.4e-15
$ python3 run_all2.py > run_all2.out; python3 summ.py run_all2.out   # S2: 39 tasks; per row the max over configs a x roots of sum_b|group_b|/B^(n-2); E=0: g in {.05,.5,1} x 1-t in {1,1e-3,1e-6} (9 pts, max over them shown; L=9: 30 configs x every root, L=17: n=4 10 configs x 4 roots, n=6 3 configs x roots {0,1}); E=1.5 (|E|<=2-kappa, kappa=1/2): g=.5, 1-t=1e-6
E=0 n=4 L= 9: 9 (g,1-t) pts, 30 cfg x 4 roots, 3 trees | max tot 7.12 G0 3.98 G1 4e-13 G2 7.43 (g=1,1-t=1e-06) G3 1.27 (g=1,1-t=0.001) | slice/(1-t) 1.000
E=0 n=4 L=17: 9 (g,1-t) pts, 10 cfg x 4 roots, 3 trees | max tot 7.41 G0 4.00 G1 0e+00 G2 7.82 (g=1,1-t=1e-06) G3 1.61 (g=1,1-t=0.001) | slice/(1-t) 1.000
E=0 n=6 L= 9: 9 (g,1-t) pts, 30 cfg x 6 roots, 18 trees | max tot 32.97 G0 15.83 G1 5e-13 G2 32.98 (g=1,1-t=1e-06) G3 5.02 (g=1,1-t=0.001) | slice/(1-t) 1.000
E=0 n=6 L=17: 9 (g,1-t) pts, 3 cfg x 2 roots, 18 trees | max tot 35.17 G0 15.97 G1 0e+00 G2 35.19 (g=1,1-t=1e-06) G3 2.90 (g=1,1-t=0.001) | slice/(1-t) 1.000
E=1.5 n=4 L= 9: 1 (g,1-t) pts, 30 cfg x 4 roots, 3 trees | max tot 5.32 G0 1.14 G1 2e-14 G2 6.37 (g=0.5,1-t=1e-06) G3 0.00 (g=0.5,1-t=1e-06) | slice/(1-t) 1.143
E=1.5 n=4 L=17: 1 (g,1-t) pts, 10 cfg x 4 roots, 3 trees | max tot 5.36 G0 1.10 G1 0e+00 G2 6.39 (g=0.5,1-t=1e-06) G3 0.01 (g=0.5,1-t=1e-06) | slice/(1-t) 1.143
E=1.5 n=6 L= 9: 1 (g,1-t) pts, 30 cfg x 6 roots, 18 trees | max tot 11.25 G0 1.94 G1 4e-14 G2 13.04 (g=0.5,1-t=1e-06) G3 0.01 (g=0.5,1-t=1e-06) | slice/(1-t) 1.959
$ python3 growth.py 1e-6; python3 growth.py 1e-3; python3 growth_tab.py   # S3: n=4, g=1, E=0, 10 configs x 4 roots
n=4 g=1 1-t=1e-6 max_G2 vs L: 5:6.20 7:7.10 9:7.43 11:7.61 13:7.72 15:7.78 17:7.82
n=4 g=1 1-t=1e-3 max_G3 vs L: 5:0.34 7:0.85 9:1.27 11:1.50 13:1.58 15:1.61 17:1.61
$ python3 inst4.py   # S4: the instance; groups sum_b|group_b|/B0^2; limits of the external shapes (TEAM §8 lesson 14)
sigma_alt=(+,-,+,-) r=1 a=[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]: sum_b|inner|/B0^2=0.4451 | G0 0.0409 G1 5.9e-18 G2 0.3649 G3 0.0425 | |slice|/(1-t)=0.5263 B0=2.9371
sigma_alt=(+,-,+,-) r=1 a=[(0, 0, 0), (1, 0, 0), (0, 1, 2), (2, 2, 2)]: sum_b|inner|/B0^2=0.0004 | G0 0.0002 G1 1.0e-18 G2 0.0006 G3 0.0003 | |slice|/(1-t)=0.5263 B0=2.9371
sigma_alt=(+,-,+,-) r=1 a=[(1, 2, 3), (4, 0, 2), (3, 3, 1), (0, 4, 4)]: sum_b|inner|/B0^2=0.0003 | G0 0.0001 G1 7.7e-19 G2 0.0004 G3 0.0001 | |slice|/(1-t)=0.5263 B0=2.9371
not-sigma_alt=(-,+,-,+) r=2 a=[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]: sum_b|inner|/B0^2=0.4451 | G0 0.0409 G1 5.9e-18 G2 0.3649 G3 0.0425 | |slice|/(1-t)=0.5263 B0=2.9371
not-sigma_alt=(-,+,-,+) r=2 a=[(0, 0, 0), (1, 0, 0), (0, 1, 2), (2, 2, 2)]: sum_b|inner|/B0^2=0.0017 | G0 0.0003 G1 1.5e-18 G2 0.0011 G3 0.0006 | |slice|/(1-t)=0.5263 B0=2.9371
not-sigma_alt=(-,+,-,+) r=2 a=[(1, 2, 3), (4, 0, 2), (3, 3, 1), (0, 4, 4)]: sum_b|inner|/B0^2=0.0003 | G0 0.0002 G1 1.2e-18 G2 0.0004 G3 0.0001 | |slice|/(1-t)=0.5263 B0=2.9371
every root, sigma_alt, a=A3[2]: max over r of sum_b|inner|/B0^2 = 0.0003
1-t=1e-01: L^d(1-t)Theta(0,0)=23.2191  (1-t)*rowsum=1.000000  B0=2.937
1-t=1e-06: L^d(1-t)Theta(0,0)=1.0003  (1-t)*rowsum=1.000000  B0=8004
1-t=1e-09: L^d(1-t)Theta(0,0)=1.0000  (1-t)*rowsum=1.000000  B0=8e+06
```
Reading: `G1`=0 to 5e-13 (exact by the antisymmetry); `G0` is the only group that carries the sum-zero (`|slice|/(1-t)` = 0.5 (`n=4`), 0.375 (`n=6`) at small `1-t`, 1.000 at `1-t=1`, 1.143/1.959 at `E=1.5`); `G2` dominates and `G2/(1+log L)` peaks at 2.41 (`L=7`) and falls to 2.10 (`L=15`); `G3` saturates at 1.61 (`L=15,17`): no sign of `log L` growth beyond the loss the proof allows. Contraction matches the independent `pre2.lhs` (n=4) to 1.7e-13 and brute force over node labels (n=6, `L=3`) to 1.4e-15. External `KLPT` at the instance: `L^d(1-t)Θ(0,0)→1` (23.22, 1.0003, 1.0000) and `(1-t)·rowsum=1` (S4); the `BD1/BD2/KLZero/KLDecay/KLShort` shapes at this `(L,g)` and `1-t→0` are in `T2100-prove.md` (a) (the `1-t=1e-1,1e-6,1e-9` lines). `T2106` consumes `KLPT` only through the merged `KLf0_bound`, `KLf_crude_bound`, `KLf12_bound`.
**Verdicts.** Target 1 (`KLindStepAt`, `KLindStepPin` verbatim in `RBM.Loop`; `diff` of `64b58eb:RBM3D/Probe/T2004Pins.lean` lines 845-863 against the pin block of the check file: identical): PASS. Target 2 (`KLindStep_alt`, every alternating `σ`, every `r,a`, shape `∀τ>0,∃C>0,∀p σ r`): PASS (all four groups close, no exponent short; G2 has slack 0 and uses `L^{τ'}`). Target 3 (`KLindStepAt_holds`, `KLindStepPin_holds`): PASS. Hypotheses: only `KLPT d κ gmax` (+ `KLShort` by `KLShort_holds`); no new `Prop`; no private merged lemma needed. Overall: **PASS**.
## (b) Script output (worktree RBM3D-wt/T2106, branch t/T2106; scripts and outputs in scratchpad/T2106/: axioms.lean, axscan.lean, extract.py, extract_inst.py, mkb.sh, mkb_stmts.sh, names_check.lean, pubnames.txt, used.txt)
```
$ date -u; git log --format="%h %cd %s" --date=iso-strict main..t/T2106 | cut -c1-110
Sun Oct  4 05:37:41 UTC 2026
d15d862 2026-10-03T22:32:41-07:00 T2106: KL10b instance with a spread labelling
79729e3 2026-10-03T22:25:38-07:00 T2106: KL10b RBM3D/Loop/KLIndStepB.lean (case (ii) of (eq:ind-step-bound), K
$ git status --short; git diff --stat main...t/T2106; git diff --name-status main...t/T2106
 RBM3D/Loop/KLIndStepB.lean | 947 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 947 insertions(+)
A	RBM3D/Loop/KLIndStepB.lean
$ lake build RBM3D.Loop.KLIndStepB 2>&1 | tail -2   # forced rebuild (the file was changed and restored byte-identical), 05:33:20 UTC; log scratchpad/T2106/build2.log
✔ [3256/3256] Built RBM3D.Loop.KLIndStepB (9.5s)
Build completed successfully (3256 jobs).
$ wc -l RBM3D/Loop/KLIndStepB.lean; grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Loop/KLIndStepB.lean; grep -n "^import\|open private" RBM3D/Loop/KLIndStepB.lean
     947 RBM3D/Loop/KLIndStepB.lean
0
6:import RBM3D.Loop.KLIndStepA
13:`Loop/KLIndStepA.lean` is reused (no `open private` is added).
$ lake env lean scratchpad/T2106/axscan.lean   # every hand-written constant of the module, private included
module RBM3D.Loop.KLIndStepB: 24 hand-written constants (19 theorems, 5 defs, 19 private); axioms used by them: [propext, Classical.choice, Quot.sound]; constants using another axiom: 0
$ lake env lean scratchpad/T2106/axioms.lean   # #print axioms of the 5 public declarations (05:33:37 UTC)
'RBM.Loop.KLindStepAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStepPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStep_alt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStepAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLindStepPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ diff <(sed -n 45,63p docs/tickets/checks/T2106-check.lean) <(sed -n 48,66p RBM3D/Loop/KLIndStepB.lean); diff <(git show 64b58eb:RBM3D/Probe/T2004Pins.lean | sed -n 845,863p) <(sed -n 48,66p RBM3D/Loop/KLIndStepB.lean)
exit=0
exit=0
$ registry pre-check: temporary `import RBM3D.Loop.KLIndStepB` after the last import of RBM3D.lean (reverted, not committed), lake build at the final commit (05:32:41 UTC, log fullbuild_with2.txt); the same without it (baseline of this worktree, 05:27:01 UTC, fullbuild_base.txt)
-- with the import:
576:info: RBM3D.lean:149:0: axiom audit: 3250 theorems, 1184 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
577:All within [propext,
688:premises found by scanning: 83 (borrowed 2, owed 66, structural 15).
689:registry: 5 borrowed + 101 owed + 38 structural; 61 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
751:Build completed successfully (3850 jobs).
-- baseline (no import):
576:info: RBM3D.lean:148:0: axiom audit: 3247 theorems, 1182 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
577:All within [propext,
688:premises found by scanning: 83 (borrowed 2, owed 66, structural 15).
689:registry: 5 borrowed + 101 owed + 38 structural; 61 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
751:Build completed successfully (3849 jobs).
$ diff <(sed -n 577,751p fullbuild_base.txt) <(sed -n 577,751p fullbuild_with2.txt)   # the audit section; only the carrier count of KLPT and the job count differ
9c9
<   RBM.Loop.KLPT: 6 [no certificate]
---
>   RBM.Loop.KLPT: 8 [no certificate]
175c175
< Build completed successfully (3849 jobs).
---
> Build completed successfully (3850 jobs).
$ git status --short; cmp RBM3D.lean <original copy>   # root file restored
(empty status; root file identical to the original)
$ name clash on main (6187713): declarations named like a public name of the file: git grep -nE "^(private |noncomputable )*(theorem|lemma|def|abbrev|structure|instance) (RBM\.Loop\.)?<name>( |$)"; all word occurrences: git grep -nw <name>
KLindStepAt: 0 declaration(s), 1 word occurrence(s) on main
main:RBM3D/Loop/KLIndStepA.lean:1229:/-- **`KLindStep_nonAlt`** (target 1): the pin's inequality (`K
KLindStepPin: 0 declaration(s), 1 word occurrence(s) on main
main:RBM3D/Loop/KLIndStepA.lean:15:and proves the pin `KLindStepPin` from the declarations below.
KLindStep_alt: 0 declaration(s), 0 word occurrence(s) on main
KLindStepAt_holds: 0 declaration(s), 0 word occurrence(s) on main
KLindStepPin_holds: 0 declaration(s), 0 word occurrence(s) on main
$ git grep -n KLIndStepB main -- RBM3D/*.lean | wc -l   # private helper prefix
       0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/KBoundEmpty.lean   # template only (core_alt, :817), nothing ported
9e0f275
 RBM2D/Loop/KBoundEmpty.lean | 210 +++++++-------------------------------------
 1 file changed, 31 insertions(+), 179 deletions(-)
$ grep -c "core_alt\|term_bound\|expand_two\|fiber_exp_pow_le" RBM3D/Loop/KLIndStepB.lean   # identifiers of the RBM2D template in this file
0
```
Target statements, extracted from the file by `python3 extract.py KLindStepAt KLindStepPin KLindStep_alt KLindStepAt_holds KLindStepPin_holds` (docstrings and proofs omitted; `variable {d : ℕ} {κ gmax : ℝ}` is in force for `KLindStep_alt`):
```lean
def KLindStepAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
    σ r ≠ σ (r + 1) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ Finset.univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2)
def KLindStepPin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLindStepAt d n κ gmax
theorem KLindStep_alt (n : ℕ) [NeZero n] (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax) :
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n),
      (∀ j, σ j ≠ σ (j + 1)) → ∀ a : Fin n → Zd d p.L,
      ∑ b : Zd d p.L, ‖∑ δ ∈ univ.filter (fun δ : Fin n → Zd d p.L => δ r = b),
          KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
            ∏ i ∈ univ.erase r,
              thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2)
theorem KLindStepAt_holds (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLindStepAt d n κ gmax
theorem KLindStepPin_holds : KLindStepPin
```
Compiled instances: the 5 `examples` of section 7 (`d = 3`, `L = 5`, `g = 1/2`, `E = 0`, `t = 9/10`, `KLinstPar : KLPar 1 1`; every deterministic hypothesis discharged by `decide`, `norm_num`, `one_pos`; `KLPT 3 1 1` is the only hypothesis left, the other gate's pin).  `python3 extract_inst.py` prints the doc line and the line applying the theorem; the first instance in full (lines 862-871):
```
[1] lines 862-871: Target 2, `KLindStep_alt`: `n = 4`, `σ = σ^{(alt)} = (+,-,+,-)`, root `r = 1`,
      exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3]⟩
[2] lines 875-885: Target 2, the complement `¬σ^{(alt)} = (-,+,-,+)` (also alternating), root `r = 2`, a spread
      exact ⟨C, hC, H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide)
[3] lines 888-897: Target 2 at `n = 6` (`|{j ≠ r}| = 5`): `σ^{(alt)}`, root `r = 3`, `a = (0, 1, 2, 3, 4, 0)`.
      exact ⟨C, hC, H KLinstPar (KLsigAlt 6) 3 (by decide) ![0, 1, 2, 3, 4, 0]⟩
[4] lines 902-926: Target 3, `KLindStepAt_holds` at `(d, n, κ, gmax) = (3, 4, 1, 1)`, unfolded at the data: one
      exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3],
      H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide) ![0, 1, 2, 3],
      H KLinstPar ![true, true, true, false] 2 (by decide) ![0, 1, 2, 3]⟩
[5] lines 930-942: Target 3, `KLindStepPin_holds` applied at `(d, n, κ, gmax) = (3, 4, 1, 1)` and `(3, 3, 1, 1)`,
      refine ⟨KLindStepPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT, ?_⟩
      obtain ⟨C, hC, H⟩ := KLindStepPin_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
      exact ⟨C, hC, H KLinstPar KLinstσ 0 (by decide) KLinsta⟩
--- instance [1], verbatim:
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = b),
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ *
            ∏ i ∈ Finset.univ.erase (1 : Fin 4),
              thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4 i) (KLsigAlt 4 (i + 1))
                (![0, 1, 2, 3] i) (δ i)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2) := by
  obtain ⟨C, hC, H⟩ := KLindStep_alt 4 (by norm_num) (by norm_num) one_pos one_pos hPT 1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3]⟩
--- instance [4] (KLindStepAt_holds, both branches of the case split), verbatim, the statement abbreviated by `...` (three conjuncts: `σ^{(alt)}` root `1`; `¬σ^{(alt)}` root `2`; `σ = (+,+,+,-)` root `2`):
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 1 = b),
      ...
  obtain ⟨C, hC, H⟩ := KLindStepAt_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    1 one_pos
  exact ⟨C, hC, H KLinstPar (KLsigAlt 4) 1 (by decide) ![0, 1, 2, 3],
    H KLinstPar (fun k => !KLsigAlt 4 k) 2 (by decide) ![0, 1, 2, 3],
    H KLinstPar ![true, true, true, false] 2 (by decide) ![0, 1, 2, 3]⟩
```
Narrative (prover stage 1b, claude-sonnet-5-5; first `date -u` of the stage 05:05:40 UTC; the commits are printed above with their git times):
1. Delivered: `RBM3D/Loop/KLIndStepB.lean` (947 lines, the only changed file): the pins `KLindStepAt`, `KLindStepPin` verbatim (diff exit 0 against the check file and the
   probe), `KLindStep_alt` (target 2), `KLindStepAt_holds`, `KLindStepPin_holds` (target 3), 19 private helpers `KLIndStepB_*`. Hypotheses: `KLPT d κ gmax` only
   (`KLShort` is `KLShort_holds`); no new `Prop`, no `open private`, `Test/Axioms.lean` untouched (registry pre-check: 83 premises with and without the import; only the
   carrier count of `KLPT` goes 6 to 8).
2. Lean shape of the expansion (the groups are those of (a) row 3; the arrangement differs from (a) row 2): `Finset.prod_add` on `f₂ + (f₁ + f₀)` with `V` = f₂ positions,
   and a second `Finset.prod_add` on `f₁ + f₀` only for the term `V = ∅` (`U` = f₁ positions) (`KLIndStepB_expand`). For `V ≠ ∅` the factors outside `V` are not expanded
   (crude bound `‖f₁ + f₀‖ ≤ 2 K B_{t,0}`), so (G2) is one lemma for every pattern with an f₂: `2^{n-1}` terms `U` and `2^{n-1} - 1` terms `V` instead of `3^{n-1}`
   patterns; the constant carries `2K` where (a) row 4 has `K`.
3. Groups, the private lemma and the merged input that close each: (G0) `KLIndStepB_G0`: `KLIndStepA_sumZero_signed` (the signed slice estimate, the first part of
   `KLsumZero_weighted`) times the crude bound times `KLlat_sum_norm_Theta_row_le`, no loss, `(1-t)(1-t)⁻¹ = 1`; (G1) `KLslice_f1_vanish`, the term is exactly `0`; (G2)
   `KLIndStepB_G2` and `KLIndStepB_G2sum` (`KLsumZero_weighted` with `Q = d`, `KLlat_pow_dim_rpow`, `(g²+|1-t|)⁻¹ (g²+(1-t)) = 1`); (G3) `KLIndStepB_G3` and
   `KLIndStepB_G3sum` (`Q = 2d-2`, `KLlat_pair_rpow`, `(g²+|1-t|)⁻¹ ≤ B_{t,0}` by `KLlat_inv_le_Bparam`, `B^{n-3} B = B^{n-2}`). Distinguished factors: `i ∈ V`
   (`Finset.Nonempty`) and `i ≠ l ∈ U` (`Finset.one_lt_card`); weights by `|δ_j - b| ≤ KLmaxDist δ` (`KLIndStepA_dist_le_maxDist`).
4. Loss: `τ' = τ/3`, `(L^{τ'})³ = L^τ` (`Real.rpow_natCast`, `Real.rpow_mul`); (G2) uses `L^{2τ'} ≤ L^τ`, (G3) `L^{3τ'}`, (G0) `1 ≤ L^τ`. The constant `C = 2^{n-1}(C_s
   (2K)^{n-2} + K₁₂² (2K)^{n-3} C₃ + K₁₂ (2K)^{n-2} C₂)` is chosen before `∀ p σ r a`, so it depends on `d, n, κ, gmax, τ` only (DECISIONS §29, constants clause).
   Boundary items of §29: time domain `0 ≤ t < 1` is `KLPar.ht0/ht1`; the pin has no `W`, `ilambda`, `N`; every `n ≥ 3`, no `∀ᶠ`; the regimes `1-t ≷ g², g²/L², g²/L^d`
   are absorbed in `B_{t,0}` (`A⁻¹ ≤ B`, `(L^d(1-t))⁻¹` is a summand of `B`).
5. `KLindStepAt_holds`: `by_cases` on alternating `σ`: `KLindStep_alt`, else the merged `KLindStep_nonAlt` (it carries the pin's `σ r ≠ σ (r + 1)`); `C = C_alt +
   C_nonAlt`. `KLindStepPin_holds` is `fun d n _ κ gmax … => KLindStepAt_holds d n κ gmax …`.
6. Instances: 5 examples (listing above); the example of `KLindStepAt_holds` runs through both branches of the case split.
7. RBM2D `core_alt` (`c9a24cf:RBM2D/Loop/KBoundEmpty.lean:817`) was read after the first commit as a template only; no declaration of the module has the name of a
   declaration of the excerpt read (`core_alt`, `term_bound`, `expand_two`, `fiber_exp_pow_le`: count 0 above); nothing is ported.
## (c) Verified Mathlib names used (59 names: the token search of `scratchpad/T2106/used.txt` plus `Finset.eq_empty_or_nonempty`, used by dot notation; `#check` of each after `import RBM3D.Loop.KLIndStepB`: 0 errors)
- `Finset.prod_add`, `Finset.add_sum_erase`, `Finset.mul_prod_erase`, `Finset.card_erase_of_mem`, `Finset.card_sdiff_of_subset`, `Finset.card_le_card`, `Finset.card_pos`, `Finset.one_lt_card`, `Finset.card_eq_one`, `Finset.nonempty_iff_ne_empty`
- `Finset.card_powerset`, `Finset.card_erase_le`, `Finset.mem_powerset`, `Finset.empty_mem_powerset`, `Finset.sdiff_empty`, `Finset.prod_empty`, `Finset.prod_singleton`, `Finset.prod_const`, `Finset.prod_le_prod₀`, `Finset.sum_comm`
- `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.sum_const_zero`, `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_congr`, `Finset.prod_congr`, `Finset.mem_erase`, `Finset.mem_filter`
- `Finset.mem_sdiff`, `Finset.mem_of_mem_erase`, `Finset.card_univ`, `Finset.mem_univ`, `Finset.Nonempty.card_pos`, `norm_sum_le`, `norm_prod`, `norm_mul`, `norm_add_le`, `norm_zero`
- `abs_of_pos`, `inv_mul_cancel₀`, `Real.one_le_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_nonneg`, `pow_le_pow_right₀`, `pow_nonneg`, `mul_pow`, `add_sub_cancel`
- `mul_inv`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `nsmul_eq_mul`, `Nat.cast_nonneg`, `Fintype.card_fin`, `le_of_eq_of_le`, `Finset.eq_empty_or_nonempty`
- verified absent or deprecated: none met in this ticket (`Finset.card_sdiff` has the statement `#(t \ s) = #t - #(s ∩ t)`; `Finset.card_sdiff_of_subset` is the form used)
## (d) Open issues and paper-delta candidates
1. T2106a (leaf type narrower, root more general; inherited from the signed probe pin, not new in this ticket): `KLindStepAt` states `(eq:ind-step-bound)`
   (`A_deterministic_estimates.tex:703`; the leaves `Θ̃_t` at `:682`, `:739`) for the leaves `Θ_t^{(σ_i,σ_{i+1})}` (for alternating `σ`: `Θ_t`) and any root `r` with `σ_r
   ≠ σ_{r+1}`; the paper's claim is for `Θ̃_t ∈ {Θ_t, tS^{(B)}Θ_t^{(+,-)}}` and root `1`. The `tSΘ` leaf is neither stated nor proved here (pin docstring: `tSΘ^{(+,-)} =
   Θ^{(+,-)} - I`). `docs/paper-deltas.md:459` records the `Theta`-propagator and `π = ∅` restriction of the K-loop model; a fixed-string grep for `Θ̃` and `tSΘ` in that
   file finds nothing.
2. T2106b (no statement change, proof budget): the pair sum `Σ_b [(|y_i|+1)(|y_k|+1)]^{-(d-1)}` is `O(1 + log L)` in Lean (`KLlat_pair_rpow`); the paper's last line of
   item 4 (`A_deterministic_estimates.tex:776`) writes `≲ 1`. The log is paid by the loss: (G3) spends `τ/3 + τ/3 + τ/3` with no slack (two `(eq:f12)` losses and the
   lattice sum), (G2) `2τ/3`. T2100 audit §2 Target 5 already judged this no statement delta.
3. `KLindStep_alt` is stated for all `n ≥ 3`; an alternating `σ` forces `n` even (`KLIndStepA_alt_cases`), so for odd `n` it holds vacuously; the non-alternating `σ` are
   covered by `KLindStep_nonAlt`, and `KLindStepAt_holds` ranges over all `n ≥ 3`.
4. For the hub: merge adds `import RBM3D.Loop.KLIndStepB` after the last `import` of `RBM3D.lean` (the pre-check above does exactly this). `KLindStepPin_holds :
   KLindStepPin` discharges the route pin for KL11 (`Kpi_cut`, `KLboundPin`) and KL12; `KLindStepAt_holds` has the binders `(d n : ℕ) [NeZero n] (κ gmax : ℝ)` of the pin.
5. Inherited, unchanged: `KLIndStepA` reaches six private `KLMolecule_*` lemmas by `open private` (T2100 audit O1); this file adds none.
6. The only external hypothesis is `KLPT d κ gmax` (registered borrowed, `Test/Axioms.lean:79`); its limit checks at the instance data are in (a) (`L^d(1-t) Θ(0,0) → 1`,
   `(1-t) · rowsum = 1`).
