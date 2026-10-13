Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct 13 01:51:32 UTC 2026
Stage 1a, design gate E (CONTROL H250 (4), H263); mathematics only, no Lean written. Scratch: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2482/` (`num.py`, `stab.py` = `git show t/T2459:docs/reports/T2459/{num,stab}.py`; new `hs_ba.py sth.py ec.py inst.py cone.py nmin.py digest.py`; outputs `out/`). Notation: `B=W^d`, `τ=(B(1-u))⁻¹`, `T(r)=τ²e^{-√r}+W^{-D}`, `ℓ=ℓ*=(log W)^{3/2}`, `Γ_{ab}=𝓛^{(2)}_{(+,-),(a,b)}`, `x:=log W`. `S=1` is `Cm.S n = (1 : Matrix)` = identity (`BA/FlowPins.lean:327`, `Chain/Carrier.lean:65`).
### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `τ ≤ 1` | `10^-8.73` at the instance | `B(1-u) ≥ lam²B ≥ 1` (`lam²≤1-u`, `1≤lam²W^d`); used as `τ≤τ^{1/2}` | `lam²W^d=64` at n=1; `4.1e9` at n=800 |
| 2 | `J` | `1` | `J≥1` gives `J≤J^{3/2}≤J³`; the cap `J≤W^{1/2}` is read by no step here | cap 32 at n=1 |
| 3 | floors | `W^{-D}L^{2d} ≤ W^{-12d} ≤ τ²` | `(L^dW^{6d})²≤W^D` gives `W^{-D}≤L^{-2d}W^{-12d}` | `W^{10d}`; instance `2^378≤2^400` (n=1), `2^1986≤2^2129` (n=800) |
| 4 | wG ball/indicator | radius `ℓ`, indicator `2ℓ` | `r>2ℓ ⇒ |a_1-x|>r-ℓ>ℓ` (far field is at `ℓ`) | 0 (tight; strict) |
| 5 | dif cuts | near cut `2ℓ`, `c`-ball `3ℓ`, indicator `6ℓ` | `|c-a_1'|>3ℓ-2ℓ=ℓ`; `r>6ℓ ⇒ r-5ℓ>ℓ` | 0 (both tight) |
| 6 | ball counts | `#𝔹_ℓ≤2(2ℓ+1)^d`, `#𝔹_{3ℓ}≤2(6ℓ+1)^d` | `LemDecCalE_e10a`: `(2R+1)^d`. The ticket's `2(3ℓ+1)^d` is no radius used here (F1) | — |
| 7 | shifts | `e^{√(2ℓ)}, e^{√(ℓ/2)}, e^{√ℓ/2}`; `e^{2√(6ℓ)}=e^{4.899√ℓ}`; `e^{(√3+√5+2)√ℓ/2}=e^{2.984√ℓ}`; `e^{(1+√2)√ℓ}` | each `≤ e^{8√ℓ}` (`lossE2`: `8x^{3/4}`) | `≥ e^{3.1√ℓ}` (`√ℓ=x^{3/4}≥2.83`) |
| 8 | `Λ`, `K0` | wG `Λ²`, dif `Λ³` max; `K0` unread | `lossE2`: `K0²Λ⁶`, both `≥1` | `Λ³`; bundle (ii) is read by no step (F2) |
| 9 | constants (d=3) | `2S_d+1=3.85e15`, `C_sq=3.94e19` | `lossE2` const `10^12(1600d⁴)^d=2.18e27`; wG loss `×1000^d(1+log(L^dW^{6d}))^{2d}` | totals in (i-c) |
| 10 | `θ` | `S_θ=Σe^{-(θ/2)√|y|}`, `W^{2θd(Cd+1)}` | `S_θ≤(1+1536d⁴/θ⁴)^d` (`lemDecCalE_sum_zdist_le` at `γ=θ/(2d)`); `W^{1.2}` at `θ=.1,d=3,Cd=1` | `3.7e11 ≪ 1.9e27` (sth.py, in (ii)) |
| 11 | HS | `k≥2` | `|tr X|≤√B‖X‖_F` only (k=1 false: ratio `2.83=√8`, hs_ba.py) | — |

**(i-a) E-a, the HS layer.** `E_a^{1/2}=W^{-d/2}1_{[a]}`, `X_i=E_{a_{i-1}}^{1/2}G(σ_i)E_{a_i}^{1/2}` (`a_{-1}:=a_{k-1}`), so `𝓛^{(k)}_{σ,a}=tr∏G(σ_i)E_{a_i}=tr(X_0⋯X_{k-1})` (cyclicity, `E^{1/2}E^{1/2}=E`). Leg: `‖X_i‖_F²=tr(E_{a_{i-1}}G(σ_i)E_{a_i}G(σ_i)^*)=𝓛^{(2)}_{(σ_i,!σ_i),(a_i,a_{i-1})}` since `G(σ)^*=G(!σ)` for Hermitian `H` (`lwWx_Gres_conjTranspose`, `Graph/LWWeightExp:115`). Swap `𝓛^{(2)}_{(-,+),(a,b)}=𝓛^{(2)}_{(+,-),(b,a)}` (cyclicity): every leg is a `Γ` of an ordered block pair; bundle (ii)/(iii) at `(+,-)` suffices. `k≥2`: `|tr(AB)|≤‖A‖_F‖B‖_F`, `‖AB‖_F≤‖A‖_F‖B‖_F` give `|𝓛^{(k)}|≤∏‖X_i‖_F` (target 2). List form: `loopM_eq_loopL` (`Loop/GLoopFlow:127`). Glue (`k=6`, `q=p+1`): `𝓛^{(6)}=tr(YX)`, `Y=X_pX_q`, `X=` the other four legs cyclically: `|𝓛^{(6)}|≤‖Y‖_F∏_{i∉{p,q}}‖X_i‖_F`, `‖Y‖_F²=𝓛^{(4)}_{(σ_p,σ_q,!σ_q,!σ_p),(a_p,a_q,a_p,a_{p-1})}`. Leg bounds: any pair `Γ≤Λτ` (v); `|a-b|≥ℓ`: `Γ≤W^{-D}+JT≤2JT` (iii),(i), `W^{-D}≤T`, `J≥1`; with (vi) `Γ≤2(α²τ²e^{-θ√|a-b|}+W^{-D})`, `α²=W^{θd(Cd+1)}Λ`.
`STeeLoop` (`Induction/Step34Pins:152`) at `m=2`, `S=1` (`b=b'=c`), hand-run: `k=1` blocks `(a_0,a_1,c,a_1',a_0',c)`, charges `(σ_0,σ_1,σ_0,!σ_0,!σ_1,!σ_0)`, legs `(c,a_0),(a_0,a_1),(a_1,c),(c,a_1'),(a_1',a_0'),(a_0',c)`; `k=2` blocks `(a_1,a_0,c,a_0',a_1',c)`, legs `(c,a_1),(a_1,a_0),(a_0,c),(c,a_0'),(a_0',a_1'),(a_1',c)`. Glue at the two legs meeting at `c` (positions 2 and 5).
**(i-b) E-b, chains (total `N` is the constant to be `≤` the loss; `STELKLKMg`, `STEGtMg`, `STeeMg` at `S=1` are single sums, `Step2Gen:375,368,960`).**
| case | used (bundle) | chain | `N` |
|---|---|---|---|
| lk | (i) | `|𝓔|≤BJ²Σ_xT(x-a_1)T(a_0-x)≤(2S_d+1)J²Bτ²T(r)`, `Bτ²=τ/(1-u)`; `sum_tail_tail`, `A=τ²`, floor 3 | `2S_d+1` |
| wG, any | (iv) | `|𝓔|≤BΛτΣ_x(|𝓛³(x,a_0,a_1)|+|𝓛³(a_0,x,a_1)|)=Λ(1-u)⁻¹Σ_3` | — |
| wG1 `r≤2ℓ`, `x∈𝔹_ℓ` | (v)k=3 | `#𝔹Λτ²≤#𝔹Λe^{√(2ℓ)}T(r)`, `J`-free (indicator term) | `2#𝔹e^{√(2ℓ)}` |
| wG2 `r≤2ℓ`, `x∉𝔹` | (v)k=2, (i),(iii) | `|𝓛³|≤2J(Λτ)^{1/2}√(T T')`; `Σ_x≤C_sqτ√T(r)` (`EwG_sum_sqrt_tail`, floor 3); `τ≤e^{√r/2}√T(r)`: `≤2JΛ^{1/2}C_sqe^{√(ℓ/2)}τ^{1/2}T(r)` | `4C_sqe^{√(ℓ/2)}` |
| wG3 `r>2ℓ`, `x∈𝔹` | (v)k=2, (i),(iii) | one short leg, `(a_0,a_1)` long, far leg `T(r-ℓ)≤e^{√ℓ}T(r)` (`tailT_shift`): `(Λτ)^{1/2}2Je^{√ℓ/2}T(r)` | `4#𝔹e^{√ℓ/2}` |
| wG4 `r>2ℓ`, `x∉𝔹` | (i),(iii) | three long legs: `(2J)^{3/2}√T(r)Σ_x√(T T')≤(2J)^{3/2}C_sqτT(r)`, `τ≤τ^{1/2}` | `2·2^{3/2}C_sq` |
| dif A `r≤6ℓ`, `c∈𝔹_{3ℓ}` | (v)k=6 | `BΛτ⁵=Λ(1-u)⁻¹τ⁴≤Λ(1-u)⁻¹e^{2√(6ℓ)}T(r)²`, `J`-free; `k=1,2` | `4(6ℓ+1)^de^{2√(6ℓ)}` |
| dif B `r≤6ℓ`, `c∉𝔹` | (v)k=2, (iii), (vi) | two short legs `Λτ`; four `c`-legs `>ℓ`: `√Γ_j≤√2(ατe^{-θ√d_j/2}+W^{-D/2})`, `Σ_c∏_4≤16α⁴τ⁴S_θ` (16 terms; floors `W^{-D/2}≤L^{-d}W^{-6d}≤ατ`, `S_θ≥1`), `Bτ⁵=(1-u)⁻¹τ⁴`; `J`-free | `128e^{2√(6ℓ)}` (·`W^{2θd(Cd+1)}S_θ`) |
| dif C `r>6ℓ`, `c∈𝔹_{3ℓ}` | (v)k=4, (i),(iii) | glue: `‖Y‖≤(Λτ³)^{1/2}`; four legs `>ℓ` at distances `≥r,r-3ℓ,r-5ℓ,r-4ℓ`: `(2J)²e^{2.984√ℓ}T(r)²`; `Bτ^{3/2}=(1-u)⁻¹τ^{1/2}` | `8·2(6ℓ+1)^de^{3√ℓ}` |
| dif D `r>6ℓ`, `c∉𝔹` | (i),(iii) | six long legs; `T(c-a_1')≤e^{√(2ℓ)}T(c-a_1)`; `Σ_cT(c-a_1)T(a_0-c)≤(2S_d+1)τ²T(r)`; `Bτ²=(1-u)⁻¹τ≤(1-u)⁻¹τ^{1/2}` | `16e^{(1+√2)√ℓ}(2S_d+1)` |
Rule check: every term at `r≤2ℓ` (wG) or `r≤6ℓ` (dif) with `J` carries `τ^{1/2}`; the indicator terms (wG1, A, B) are `J`-free. No entry bound of `G`, no `|E|<2`, no `M=mI`, no `SB d`, no `𝒦` bound at same charges (swap on the `𝓛` side).
**(i-c) E-c.** `lossE2wG=10^12(1600d⁴)^dK0²Λ⁶(1+log(L^dW^{2d}))⁴(1+x)³e^{8x^{3/4}}·1000^d(1+log(L^dW^{6d}))^{2d}` (`EwG:74`, `LemDecCalE:54`). Need `max(N_lk, ΣN_wG1..4, N_A+N_B, N_C+N_D)≤` loss. Reasons: `5(1+24576d⁴)^d≤5·24577^dd^{4d}≤(1000·1600)^dd^{4d}`; `(6ℓ+1)^d≤(7x^{3/2})^d≤(1+log P)^{2d}` (`log P≥6dx`); shifts row 7. Numerically (`ec.py`, `L=3`, `Λ=K0=1` worst): min over `d∈[3,399]`, `x∈{4..1e5}` of `log10(loss/needed)` = 44.2 (d=3, x=4). No fallback loss needed.

### (ii) Instance and numerics
Instance `d=3`, `sz0` (`Defs/Sizes:260`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^-6`), `u=1/2`, `D=40`, `Λ=K0=J=1`, `θ=1/10`, `Cd=1`. Command `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2482 && python3 digest.py` (reads `out/*`, produced by `python3 {num.py hs|sums|consts|exps, hs_ba.py, sth.py, ec.py, inst.py, cone.py}`); output:
```
[num.py hs] max ratio |Tr| / HS-product over 400 x 20 samples: k=3,4: 0.6849; k=6 all legs: 0.5392; k=6 glue form: 0.6660  (all <= 1 required); max |sum_b L2_ab - Im L1_a/eta|(Ward) = 5.3e-15
[hs_ba.py, 9 rows g in {1/64,1,10} x u in {0,t0/2,t0}, 20 H x 250 loops] max ratios: {'HS k=3': 0.5075, 'HS k=4': 0.4837, 'HS k=6': 0.1743, 'glue k=1': 0.3242, 'glue k=2': 0.3242} (need <= 1+1e-9); max errors: {'Hermitian': '1e-14', 'dense-vs-block': '0e+00', 'leg-identity': '6e-16', 'swap': '1e-16', 'Ward': '7e-16', '||Y||^2-vs-4loop': '7e-17'} (need <= 1e-8)
[sth.py]
theta=0.5: L=16:2243 L=128:3.908e+05 L=4096:2.286e+07 L=1000000:2.359e+07 L=Z^3:2.359e+07 | analytic C(3,theta)=7.888e+18; max S / C = 3.0e-12
theta=0.1: L=16:3629 L=128:1.49e+06 L=4096:1.033e+10 L=1000000:3.686e+11 L=Z^3:3.686e+11 | analytic C(3,theta)=1.926e+27; max S / C = 1.9e-16
theta=0.02: L=16:3998 L=128:1.958e+06 L=4096:4.67e+10 L=1000000:4.08e+15 L=Z^3:5.76e+15 | analytic C(3,theta)=4.702e+35; max S / C = 1.2e-20
[num.py consts] lk constant 2 S_d + 1 = 3.852e+15 (S_d = (1+1536 d^4)^d = 1.926e+15); wG sqrt-sum constant C_sq = 5 (1+24576 d^4)^d = 3.944e+19; sum_(Z^3) e^(-sqrt|y|/2) = 3.7e5 (sums)
[ec.py, values are log10]
d= 3 W=54.6: lk=15.6 wG=21.1 dif<=6l=11.7 dif>6l=19.8 | loss=65.4 margin=44.2
min margin over d in [3,399], log W in {4..1e5}: log10 =44.22 at d=3, logW=4
[inst.py]
n=1: L=8 W=1024 lam=1/4096 log W=6.931 l*=(log W)^1.5=18.25 2l*=36.5 6l*=109.5 torus half-diameter L/2=4 | all BAScalar conjuncts: True [] | lam^2 W^d=64 (>=1) | (L^d W^6d)^2=2^378.0 <= W^D=2^400.0 | tau_u=10^-8.73 <=1 | far windows nonempty: l*<=L/2:False 6l*<=L/2:False
   (iii) at u=0: ceil(l*)=19 > L/2=4: window empty, hypothesis (iii) vacuous at this n
n=800: L=3204 W=1.055e+16 lam=1/16903438991974707264 log W=36.895 l*=(log W)^1.5=224.11 2l*=448.2 6l*=1344.6 torus half-diameter L/2=1602 | all BAScalar conjuncts: True [] | lam^2 W^d=4.111e+09 (>=1) | (L^d W^6d)^2=2^1986.1 <= W^D=2^2129.1 | tau_u=10^-47.77 <=1 | far windows nonempty: l*<=L/2:True 6l*<=L/2:True
   (iii) at u=0: r=ceil(l*)=225<=L/2: log10(W^-d |M_ab|^2) <= -8214 <= log10 W^-D = -641: True
[cone.py] cone of Graph.LWWeightExp: 61 modules; new relative to the 6: 17
[nmin.py] smallest n with 6*l* <= L/2: n=642 (L=2572, W=3.517e+15, l*=214.2)
```
Findings. **F1** the ticket instance `n=1` has `L/2=4<ℓ*=18.25`: both indicators are identically `1`, the far sets and bundle (iii) are empty (a collapsed window). All scalar conjuncts hold there, but target 8 should use `n=800` (all windows nonempty, `6ℓ*≤L/2`) in addition. **F2** bundle (ii) (`K0` bound) and the cap `J≤W^{1/2}` are read by no chain (harmless; `K0` enters only through the loss). **F3** `S_θ` is bounded uniformly in `L` (table above; the `L=∞` value is finite for every `θ>0`).
External hypothesis (the matrix bundle, supplied for `u>0` by U5c's good event): witness at `u=0`, `lam0=g0`, `H=g0Ψ` (Hermitian), where `G=M=(g0Ψ-E-m0)⁻¹` and `𝓛_0=𝒦_0` (`IsKLoopS` clause 2, `Loop/KLTree:832`, premise `BAKexists`; else `𝒦=0`): (i),(vi) `𝓛-𝒦=0`; (iv) `𝓛^{(1)}-m=0` (`self_m`); (ii),(v) `|M_ab|≤1` (Ward `Σ_b|M_ab|²=1`) gives `Λ=K0=1`; (iii) Neumann `|M_ab|≤2ρ^r/(1-ρ)`, `ρ=6g0/|E+m0|≤12lam` (`‖Ψ‖≤6`; `Im m0=Im m/√t0≥Im m≥κ=1/2`: `BAdom`, `flow_sz0` `FlowPins:1214`, `stab.py` `flow_point`), checked above at `n=800` (vacuous at `n=1`). Limit `n→∞`: `lam=(2m)^-6→0`, LHS exponent `≈ -12 ln(2m)(5 ln 2m)^{3/2}/ln10` (`r=ℓ*`, `ρ≈12lam`, `lam^-1=(2m)^6`) against `-5D ln(2m)/ln10` (`W^-D`): the ratio is `12(5 ln 2m)^{3/2}/(5D)→∞`, so (iii) holds for all large `n`.

### Fill-in table (CONTROL H250 (4)) and verdicts
| # | deliverable | line / n/a |
|---|---|---|
| (i) | E-a written; leg identity, swap, HS, list and glue forms | E-a: lines 19-20; numerics `leg-identity 6e-16`, `4-loop 7e-17`. Compiled probe texts and proofs: OPEN, probe step (Lean excluded from 1a) |
| (ii) | E-b chains per case; `STeeLoop` blocks at `m=2`, `k=1,2`, `S=1` | lines 20-34 (block lines at 20) |
| (iii) | E-c loss table, fallback | row 9 (line 15) and line 35; margin `10^44.2`; no fallback needed |
| (iv) | numerics | lines 39-57: `hs`, `sums`, `consts`, `exps` rerun (`out/num_*.out`); BA resolvents (g, u grid), `S_θ`, E-c ratios (`W=e⁴,1e3,1e6,1e12` in `out/ec.out`), no stop-rule value |
| (v) | bundle conjunct → steps; merged lemma → file:line | (i)→lk, wG2-4, dif C,D; (ii)→none; (iii)→long legs; (iv)→wG; (v)k=2→wG2,3, dif B, k=3→wG1, k=4→dif C, k=6→dif A; (vi)→dif B; Hermitian→E-a. Lemmas: `sum_tail_tail LemDecCalE:395`, `sum_zd_le :314`, `e10a :186`, `tailT_shift :527`, `EwG_sum_sqrt_tail EwG:318`, `lemDecCalE_sum_zdist_le :274` (private) |
| (vi) | reuse census | `LemDecCalEdif:93-403` is model-free (0 hits of `E2Hyp\|sz\|STLM`) but is the entry route (`wt`, `α` entry bound): not reused; the cyclic rotation is one `trace_mul_comm`. Gres adjoint: copy the 7 lines of `lwWx_Gres_conjTranspose` under the stem (the import adds 17 modules to a 104-module cone). Bridge `STeeLoop`→`loopM` is new (about 60 lines). `open private` only `lemDecCalE_sum_zdist_le` |
| (vii) | probe diff against `T2482_*` | OPEN, probe step. Math check: the pins of targets 1-7 read consistently with (i-a), (i-b) (indicators `2ℓ*`/`6ℓ*`, near cut `2ℓ*`, `J^{3/2}`/`J³`, `W^{2θd(Cd+1)}S_θ`) |
| (viii) | consumers | U5c: bundle (i)-(vi) as in the pin, (ii) unused; U5d: `dif` gives (H1) of U5a with `p=lossE2wG·W^{2θd(Cd+1)}S_θ(1-u)⁻¹(1+τ^{1/2}J³)` since indicator `≤1`; `S_θ≤(1+1536d⁴/θ⁴)^d`; U5e: instance F1 |
| (ix) | UBA-C1 | not triggered: size level `0<lam, lam²≤1-u, 1≤lam²W^d` only; kernel level `lam0,E` free via bundle; no `lam0≤lam`, no `A`. C1: no chain uses an entry bound, `|E|<2`, `M=mI`, `SB d`, the `BAGbEXP*` family |
| (x) | premise scan, registry | public `Prop`s: `BAStep5IIIEScalar/Matrix`, `BAStep5IIIEdet`; registry none; no unproved route `Prop` as premise |
| (xi) | lines vs 2,000; split | estimate by component: Edet (traces 45, leg identity+HS Fin/list 300, glue 130, bundle 70, leg lemmas 150, lk 130, wG 420, E-c 110, instance 100) ≈ 1,455; Edet2 (`S_θ` 70, bridges 120, A/B 380, C/D 330, combine 100, E-c 130, assembly 50, instance 90) ≈ 1,270. Central ≈ 2,725 > 1,950: pre-signed split U5b-1/U5b-2 (sixth U5 row: notice REQ at the 1a-audit); each file < 1,800 so `Step5IIIEdet3` is not triggered; central ≤ 3,600 so no REQ before 1b; 2.6 × central = 7,085 |
| (xii) | name-clash grep | n/a, because stage 1a is mathematics-only (no name checks); left to the probe step / 1a-audit |

Verdicts. T1 trace bounds PASS; T2 loop bound (HS) PASS; T3 bundle PASS; T4 `lk` PASS; T5 `wG` PASS; T6 `S_θ`, `dif` PASS; T7 assembly PASS; T8 instances PASS with F1 (use `n=800` for the far windows). No stop rule of the ticket fired (HS and glue ratios `≤0.51`, leg/Ward errors `≤7e-16`, `S_θ` bounded in `L`, `lossE2wG` dominates). Overall: PASS, with the pre-signed split.

## (a″) Probe compile — Tue Oct 13 02:45:41 UTC 2026
Probe step of the 1a (ticket Probe line; CONTROL H250 (4), H263), `prover-max` (claude-sonnet-5-5). Section (a) is unchanged and no (a′) is needed: no mistake in (a) was found while writing the probe, and the claims of (a) that the probe touches are confirmed (P1-P7). Probe: `RBM3D/Probe/T2482Pins.lean` on `t/T2482`, commit `0ac2aab8` (one file, 395 lines of the 400 allowed, never merged, no root import): the 11 `def T2482_*` pins of `docs/tickets/checks/T2482-check.lean` copied by script (lines 29-111), two new texts `T2482_LoopHSList`, `T2482_LoopGlue` (113-130), the Hilbert-Schmidt core proved (137-353), the `STeeLoop` blocks (356-360), the instances (363-393). Scratch: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2482/` (`probe/` parts and assembler, `pindiff.py`, `lines.py`, `cone2.py`, `h1cmp.py`, `ev_final.sh`, `ev2.sh`, `ev_final.out`, `ev2.out`, `out2/`).
```
$ date -u; git log -1 --format="%h %an %s" t/T2482; wc -l RBM3D/Probe/T2482Pins.lean; git status --short | wc -l
Tue Oct 13 02:40:59 UTC 2026
0ac2aab8 Jun Yin T2482: probe (U5b design gate E): pins 1-8, leg identity, target 2 (Fin, list, glue forms)
     395 RBM3D/Probe/T2482Pins.lean
       0
$ lake env lean --version; lake env lean RBM3D/Probe/T2482Pins.lean; echo "exit code: $?"
Lean (version 4.34.0, arm64-apple-darwin24.6.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)
exit code: 0
$ the same with -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true (lakefile.toml leanOptions)
exit code: 0
$ the same on a copy without `import Graph.BAAuxGraph2` and without the flow-matrix example (the six imports of the ticket only); grep -c "^import"
exit code: 0
6
$ lake env lean ax.lean   # the probe + 17 lines "#print axioms RBM.BA.<public theorem>"; | sed "s/^.*depends on axioms: //" | sort | uniq -c
exit code: 0
appended lines:       17
  17 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^[[:space:]]*axiom" RBM3D/Probe/T2482Pins.lean; echo "rc=$?"   # then the two C1 greps of the ticket (rc=1: no hit)
rc=1
rc=1
rc=1
$ python3 pindiff.py
check pins 11, probe pins 13; byte-identical blocks 11/11; not identical: []
new in probe (not in the check): ['T2482_LoopGlue', 'T2482_LoopHSList']
T2482_BAScalar vs t/T2459:RBM3D/Probe/T2459Pins.lean:107 (T2459_BAscalar): identical modulo prefix and the binder `{d : ℕ}`: True
T2482_BAMatrix vs t/T2459:RBM3D/Probe/T2459Pins.lean:116 (T2459_BAmatrix): identical modulo prefix and the binder `{d : ℕ}`: True
T2482_BAEdet vs t/T2459:RBM3D/Probe/T2459Pins.lean:134 (T2459_BAEdet): identical modulo prefix and the binder `{d : ℕ}`: True
$ python3 lines.py
pins (the check, copied)                       73 lines: TraceMulLe:29-30 TraceMul3Le:32-33 TraceProdLe:35-37 LoopHS:39-44 SumTheta:46-48 BAScalar:50-53 BAMatrix:55-67 BAEdet:69-84 EdetLk:86-91 EdetWG:93-100 EdetDif:102-111
pins (new: list, glue)                         17 lines: LoopHSList:113-119 LoopGlue:121-130
target 1 (traces) + pin proofs                 33 lines: trace_mul_le:137-152 trace_mul3_le:154-160 trace_prod_le:162-168 TraceMulLe_holds:321-321 TraceMul3Le_holds:322-322 TraceProdLe_holds:323-323
E-a: rotation, legs, target 2 (Fin) + swap    105 lines: frob_sq:170-179 trace_rotate:181-185 tele:187-202 trace_rot:204-214 Es:218-220 Es_herm:222-224 Es_mul_self:225-230 Gres_conj:232-242 sandwich:244-251 leg_identity:253-258 loopM_hs:274-289 LoopHS_holds:326-328 swap:347-353
E-a: list form                                  9 lines: LoopHSList_holds:333-341
E-a: glue form                                 41 lines: glue_identity:260-272 loopM_glue:291-316 LoopGlue_holds:330-331
assembly of 7                                   3 lines: assembly:343-345
instances (scalar, carrier, target 2)          13 lines: scalar_sz0:363-368 C0:370-370 Hf:371-371 LoopHS_sz0:373-377
examples (line ranges): 324-324 356-357 358-359 360-360 378-378 379-379 380-381 383-387 388-393 | sum 21
file lines: 395 | groups 294 | examples 21
$ date -u
Tue Oct 13 02:41:19 UTC 2026
$ git diff --name-status a2f86197 main -- RBM3D RBM3D.lean lakefile.toml lean-toolchain lake-manifest.json   # main = 7205c45a
M	RBM3D.lean
A	RBM3D/Chain/GridEnvelopeGen.lean
A	RBM3D/Chain/GridGoodGen.lean
A	RBM3D/Chain/OptL2Gen.lean
A	RBM3D/Chain/Step2CloseGen.lean
A	RBM3D/Graph/BAMomentExpGen.lean
M	RBM3D/Test/Axioms.lean
$ python3 cone2.py
direct imports of the probe: 7 | import cone: 130 modules | files changed on main since a2f86197: 7 | cone meets them: []
$ python3 h1cmp.py   # (viii)
Step5IIIKer2.lean:347 == probe:107 after a, a' -> b, b' : True
$ open private route (scratch op.lean): import RBM3D.Path.LemDecCalEwG; open private lemDecCalE_sum_zdist_le from RBM3D.Path.LemDecCalE; #check
lemDecCalE_sum_zdist_le : ∀ (L : ℕ) [inst : NeZero L] {γ : ℝ},
  0 < γ → ∑ y, Real.exp (-(γ * √↑(zdist L y))) ≤ 1 + 96 / γ ^ 4
$ [loop over the 491 local branches; per ref] git grep -n -E 'Step5IIIEdet|BAStep5IIIE|baStep5IIIE' $r -- RBM3D, and git grep -c T2482 $r -- RBM3D   # 02:30:35 - 02:31:23 UTC
refs scanned: 491
final names (Step5IIIEdet|BAStep5IIIE|baStep5IIIE) hits:        0
T2482 prefix hits (ref: file:count):
t/T2482: t/T2482:RBM3D/Probe/T2482Pins.lean:93
$ [per ref] git ls-tree --name-only $r RBM3D/BA/Step5IIIEdet.lean RBM3D/BA/Step5IIIEdet2.lean RBM3D/BA/Step5IIIEdet3.lean   # 02:31:31 UTC
refs with a file named Step5IIIEdet*.lean: 0
$ [per worktree in RBM3D-wt/*] grep -rlE 'Step5IIIEdet|BAStep5IIIE|baStep5IIIE' $w/RBM3D; and RBM3D/RBM3D   # uncommitted files included, 02:29:36 UTC
(only worktrees with hits are listed above) -> none listed; main worktree: 0 files
$ git grep -n -E '^(theorem|def|abbrev|lemma) (RBM\.BA\.)?(BAStep5III|baStep5III)' main -- RBM3D   # T2481 is merged (a2f86197); 02:25:16 UTC: 10 hits, names BAStep5IIIKernel, BAStep5IIITailSq(QV), baStep5III_*, baStep5IIIKernel_*, baStep5IIITailSq*_holds: none begins with BAStep5IIIE or baStep5IIIE
$ git rev-parse --short t/T2459; diff <(git show t/T2459:RBM3D/Probe/T2459Pins.lean | sed -n 281,304p | sed "s/T2459_/T2482_/g") <(sed -n 137,160p RBM3D/Probe/T2482Pins.lean)   # Tue Oct 13 02:43:08 UTC 2026
2a6ad6e0
0a1
> /-- Cauchy-Schwarz for the trace (copy of `T2459_trace_mul_le`, `t/T2459:RBM3D/Probe/T2459Pins.lean:281`). -/
17,18c18
< /-- **The Hilbert-Schmidt bound of U5-2**: `|tr(ABC)| ≤ ‖A‖‖B‖‖C‖`.  For `A = E_{c₁}^{1/2} G E_{c₂}^{1/2}` the squared Frobenius norm is the mixed-charge two-loop `𝓛^{(2)}`
< (`num.py hs`), so a `k`-loop is bounded by its legs' two-loops; the glue form `|tr(XY)| ≤ ‖X‖‖Y‖`, `‖X‖ ≤ ∏‖X_i‖` (`Matrix.frobenius_norm_mul`) is the six-loop case. -/
---
> /-- `|tr(ABC)| ≤ ‖A‖‖B‖‖C‖` (copy of `T2459_trace_mul3_le`, `:299`). -/
(only docstrings differ: the declarations and proofs of `T2482_trace_mul_le`, `T2482_trace_mul3_le` are those of the T2459 probe)
$ python3 num.py hs|sums|consts|exps; sth.py; ec.py; inst.py; cone.py; nmin.py; hs_ba.py > out2/*.out   # 02:38:04 - 02:39:01 UTC, fixed seeds
diff out/<f>.out out2/<f>.out for the 10 outputs -> identical (and diff of (a) lines 40-56 against `python3 digest.py` at 02:37:47 UTC -> rc=0)
```
New texts to be signed at the 1a-audit (`sed -n 113,130p`) and the leg identity (`sed -n 253,258p`) of the probe:
```
/-- **Target 2, list form** (new; for `STLIMg`, `STeeLoop` lists): the same bound for the list-indexed loop of `baStep2Mat`. -/
def T2482_LoopHSList (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H.IsHermitian →
    ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), 2 ≤ k →
      ‖STLIMg (baStep2Mat sz lam0 E) n u H ⟨List.ofFn σ, List.ofFn a⟩‖ ≤
        ∏ i : Fin k, Real.sqrt ‖STLIMg (baStep2Mat sz lam0 E) n u H ⟨[σ i, !(σ i)], [a i, a ((finRotate k).symm i)]⟩‖

/-- **Target 2, glue form** (new; the six-loop of `dif`): two adjacent legs `p, p+1` are kept as one factor, the 4-loop
`‖X_p X_{p+1}‖_F² = 𝓛^{(4)}_{(σ_p,σ_{p+1},!σ_{p+1},!σ_p),(a_p,a_{p+1},a_p,a_{p-1})}`; the other four legs are `p+2, ..., p+5`. -/
def T2482_LoopGlue (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H.IsHermitian →
    ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)) (p : Fin 6),
      ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤
        Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ p, σ (p + 1), !(σ (p + 1)), !(σ p)] ![a p, a (p + 1), a p, a (p - 1)]‖ *
          ∏ j ∈ ({2, 3, 4, 5} : Finset (Fin 6)),
            Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ (p + j), !(σ (p + j))] ![a (p + j), a (p + j - 1)]‖
...
/-- **The leg identity** (E-a): `‖E_b^{1/2} G(σ) E_a^{1/2}‖_F² = 𝓛^{(2)}_{(σ,!σ),(a,b)}` for Hermitian `H`. -/
theorem T2482_leg_identity (s : ℝ) (hs : s * s = ((W : ℝ) ^ d)⁻¹) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (a b : Zd d L) :
    loopM d L W H z ![σ, !σ] ![a, b] = (((‖T2482_Es d L W s b * Gres H z σ * T2482_Es d L W s a‖ ^ 2 : ℝ)) : ℂ) := by
  rw [T2482_sandwich s hs, T2482_Gres_conj hH]
  simp [loopM, List.ofFn_succ, Matrix.mul_assoc]
```
**Findings** (probe-derived).
- P1 `T2482_loopM_hs` (274-289) holds for every Hermitian `H` and every `z : ℂ`: no `Im z` hypothesis, no resolvent bound; so target 2 and the list and glue forms are entry-free (C1 greps rc=1).
- P2 The list text is for `⟨List.ofFn σ, List.ofFn a⟩`; its two-element legs `⟨[σ i, !(σ i)], [..]⟩` are converted by `simp [List.ofFn_succ]` (333-341). The glue text is for every `p : Fin 6`; the other four legs are `p+2..p+5`. At `p=5` (scratch `var/glue5.lean`) `simp` gives the 4-loop `![σ 5, σ 0, !σ 0, !σ 5] ![a 5, a 0, a 5, a 4]` and legs 1,2,3,4; at `p=2` the 4-loop `![σ 2, σ 3, !σ 3, !σ 2] ![a 2, a 3, a 2, a 1]` and legs 4,5,0,1 (leg 0 shows `a (-1)`; `(-1 : Fin 6) = 5` by `decide`): the two gluings at `c` of the blocks `(a0,a1,c,a1',a0',c)`.
- P3 `T2482_swap` (347-353, any `H`) maps a `(-,+)` leg to the `(+,-)` pattern at swapped blocks, so the bundle's `(+,-)` 𝒦 conjuncts (ii), (iii) cover every leg ((a) line 19).
- P4 The scalar part holds at the ticket's `n = 1` and at `n = 800` (363-368). At `n = 1` the far windows are empty (`L/2 = 4 < ℓ* = 18.25`, (a) F1), so the 1b's target 8 should use `n = 800` for target 7 in addition (388-393 is that instance, with the matrix part and `T2482_BAEdet 3` as hypotheses).
- P5 E-a is smaller than (a) estimated (row (xi)). No stop rule of the ticket fired. Paper-delta candidates: none new (T2459b, T2459c, T2459f stay).
- P6 One early `lake env lean` ran with the shell outside the worktree (the cwd resets between calls) and made elan install the default toolchain `leanprover/lean4:v4.35.0` under `~/.elan/toolchains`; no repository file changed; every run above is inside the worktree with `v4.34.0`.
- P7 Scratch, not in the probe (`lean/br2.lean`, 32 lines, no `sorry`; `lake env lean` at 02:44:58 UTC: no output, exit 0): `STeeMg (baStep2Mat sz lam0 E) n u H σ a a' = W^d * ∑ c, (LM ![σ 0, σ 1, σ 0, !σ 0, !σ 1, !σ 0] ![a 0, a 1, c, a' 1, a' 0, c] + LM ![σ 1, σ 0, σ 1, !σ 1, !σ 0, !σ 1] ![a 1, a 0, c, a' 0, a' 1, c])` is proved from `S = 1` (`rfl`), the two block lists and `loopM_eq_loopL` (`key` as in 333-341); so the `STeeLoop` bridge of (a) row (vi) is about 25 lines, not 60, and has no obstacle. The `dif` cases then read on explicit six-loops, to which the glue text (121-130) and target 2 (39-44) apply.
- Mathlib names used and compiled: `Matrix.frobenius_norm_def/_mul`, `Matrix.trace_mul_comm`, `Matrix.conjTranspose_mul`, `Matrix.diagonal_conjTranspose`, `Matrix.diagonal_mul_diagonal`, `Matrix.conjTranspose_nonsing_inv`, `Matrix.IsHermitian.submatrix`, `List.norm_prod_le'` (`Mathlib/Analysis/Normed/Ring/Basic.lean:355`, with the scoped Frobenius ring norm), `List.ofFn_succ'`, `List.rotate_eq_drop_append_take_mod`, `List.map_ofFn`, `List.prod_ofFn`, `finRotate_apply`, `finRotate_symm_apply`, `finRotate_last`, `Fin.coeSucc_eq_succ`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Finset.sum_mul_sq_le_sq_mul_sq`. Absent (grep of `.lake/packages/mathlib/Mathlib`): a Frobenius trace Cauchy-Schwarz (`trace_mul_le`, `norm_trace_le`, `abs_trace_mul`, `norm_trace_mul`: no relevant match) and a rotation lemma for `List.ofFn`.

**Fill-in table (CONTROL H250 (4)), final** (rows (i), (vii), (xii) were open in (a); the others are re-listed with their references).
| # | deliverable | line / evidence |
|---|---|---|
| (i) | E-a; probe texts of targets 1-2; leg identity and target 2 proved | E-a: (a) lines 19-20. Probe texts (exit 0): `T2482_TraceProdLe` 35-37, `T2482_LoopHS` 39-44, list 113-119, glue 121-130. Proved: `T2482_trace_prod_le` 162-168; leg identity `T2482_leg_identity` 253-258 (via `T2482_sandwich` 244-251, adjoint copy `T2482_Gres_conj` 232-242); half-edge telescoping and rotation `T2482_tele` 187-202, `T2482_trace_rot` 204-214; target 2 `T2482_loopM_hs` 274-289, `T2482_LoopHS_holds` 326-328; list `T2482_LoopHSList_holds` 333-341; glue identity 260-272, `T2482_loopM_glue` 291-316, `T2482_LoopGlue_holds` 330-331; swap 347-353. Instances 324, 378-380. 17 public theorems: standard axioms only. |
| (ii) | E-b chains; `STeeLoop` blocks at `m=2`, `k=1,2`, `S=1` | Chains: (a) lines 21-34, unchanged. Compiled: `STeeLoop [σ0,σ1] [a0,a1] [a0',a1'] 1 b b' = ⟨[σ0,σ1,σ0,!σ0,!σ1,!σ0],[a0,a1,b',a1',a0',b]⟩` and `... 2 ...= ⟨[σ1,σ0,σ1,!σ1,!σ0,!σ1],[a1,a0,b',a0',a1',b]⟩` by `simp [STeeLoop]` (356-359); `(baStep2Mat sz lam0 E).S n = 1` by `rfl` (360); the assembly of target 7 from 4, 5, 6 (`T2482_assembly` 343-345); the sum-level bridge from `STeeMg` to the explicit six-loops: P7. |
| (iii) | E-c loss table, fallback | (a) row 9 (line 15) and line 35: margin 10^44.2, no fallback needed; `ec.out` rerun identical (above). No Lean for E-c in the probe. |
| (iv) | numerics | (a) lines 39-57; all ten scripts rerun, outputs byte-identical (above); nothing new needed at the probe. |
| (v) | hypothesis table; merged lemmas | (a) line 68. Probe: target 2, list, glue and the legs use only `H.IsHermitian` (no bundle conjunct); merged lemmas used: `loopM_eq_loopL` (`Loop/GLoopFlow:127`) at 333-341, `Eblk_isHermitian` (`Loop/GLoop:66`) at 260-272, `Hermitian.submatrix` for `blockMat` at 326-331. |
| (vi) | reuse census | (a) line 69. The adjoint copy compiles on the six listed imports (no `Graph/LWWeightExp`, exit 0 above). `open private lemDecCalE_sum_zdist_le` resolves (output above: `Σ_y exp(-γ√|y|) ≤ 1 + 96/γ⁴`, so `S_θ ≤ (1+1536 d⁴/θ⁴)^d` at `γ = θ/(2d)`). `LemDecCalEdif` §1 not reused: the glue route (260-272, 291-316) replaces it. Bridge `STeeLoop` to `loopM`: P7. |
| (vii) | probe diff against `T2482_*` | `pindiff.py` above: 11/11 pins byte-identical to the check; `T2482_BAScalar/BAMatrix/BAEdet` identical to `t/T2459:RBM3D/Probe/T2459Pins.lean:107/116/134` modulo prefix and the binder `{d : ℕ}`; `T2482_LoopHSList`, `T2482_LoopGlue` are new: to be added to the check at the 1a-audit. Target 1 (a), (b) are the copies of probe `:281`, `:299` (137-160). |
| (viii) | consumers | (a) line 71. U5d: the near-cut premise of (H1) of merged `BAStep5IIITailSqQV` (`BA/Step5IIIKer2.lean:347`) equals the premise of the `dif` pin (probe 107) modulo renaming (`h1cmp.py` above); its bound shape `p * STtailTD sz n v D b ^ 2` is the dif conjunct with `p` as in (a) row (viii). U5c: bundle texts 50-67. U5e: instances 363-393 (scalar part at `n = 1`, `800`; target 2 at `H = 0`, `k = 3, 6`, and at `seqHflowBA`; `S_θ` at `θ = 1/10`; target 7 `lk` at `n = 800`). |
| (ix) | UBA-C1 table; C1 grep | (a) line 72: not triggered. Probe: both C1 greps of the ticket give rc=1 (no hit); no `lam0 ≤ sz.lam`, no `A`, no `withLam`; `sz.lam` is read only inside the pins `T2482_BAScalar`. |
| (x) | premise scan; registry; `open private`; copies | (a) line 73. Probe: no `Prop` beyond the pins (probe-only names); example hypotheses are this row's pins (`T2482_SumTheta 3`, `T2482_BAEdet 3`) and U5c's `T2482_BAMatrix`; registry none; `open private`: none in the probe, planned one (`lemDecCalE_sum_zdist_le`); copies: `lwWx_Gres_conjTranspose` (232-242), `T2459_trace_mul_le`, `T2459_trace_mul3_le` of `t/T2459` (commit `2a6ad6e0`; identical, diff above) (137-160), the scalar instance re-proved (363-368). |
| (xi) | lines vs 2,000; split; 2.6 x; REQ | Probe lines (`lines.py` above): traces 33, legs/HS/swap 105, list 9, glue 41 = 188 (E-a), against (a)'s 45 + 300 + 130 = 475. At a factor 1.5 for docstrings and stem names (an assumption) the 1b E-a part is about 282: `Step5IIIEdet` about 1,455 - 475 + 282 = 1,262. With P7 the bridges of `Step5IIIEdet2` are about 25 x 1.5 = 38 instead of 120, so `Step5IIIEdet2` about 1,270 - 82 = 1,188; central about 1,262 + 1,188 = 2,450 (2,725 in (a)); 2.6 x central about 6,370. Decisions unchanged: central > 1,950, pre-signed split U5b-1/U5b-2 (notice REQ for the sixth U5 row at the 1a-audit); both files < 1,800, no `Step5IIIEdet3`; central <= 3,600, no REQ before 1b. |
| (xii) | name-clash grep | Above: 491 refs, 0 hits for each of `Step5IIIEdet`, `BAStep5IIIE`, `baStep5IIIE`; 0 refs with a file `Step5IIIEdet.lean`, `Step5IIIEdet2.lean`, `Step5IIIEdet3.lean`; every worktree, uncommitted files included: no file; T2481's merged names contain no `IIIE`; `T2482_*` only in the probe on `t/T2482`. |
Probe step verdict: PASS (probe exit 0, standard axioms, no `sorry`; the leg identity and target 2 are proved; the table is complete). Open for the 1a-audit: sign the two new texts (113-130), the `n = 800` addition (P4), and the split notice (row (xi)).

## (b) Script output - Tue Oct 13 03:39:50 UTC 2026 (stage 1b, U5b-1: targets 1-5, 8 (a))
Stage 1b, `prover-max` (claude-sonnet-5-5; first `date -u` of the stage Tue Oct 13 02:53:38 UTC 2026), branch `t/T2482`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2482`: **U5b-1 only** (the pre-signed split was confirmed at the 1a-audit, `T2482-1a-audit.md` §6 item 3): the new file `RBM3D/BA/Step5IIIEdet.lean` (targets 1-5 and 8 (a)). Targets 6-7 and 8 (b) (`Step5IIIEdet2`, branch `t/T2482b`) are not in this report. Not touched: `RBM3D.lean` (the hub adds the root import at merge), `Test/Axioms.lean`, the probe. The block below is `final_ev.out` (script `final_ev.sh`, scratchpad `T2482/b1/`), run after the last Lean edit; each `$` line states its command.
$ date -u; git log --format=%h a2f86197..t/T2482 (newest first; 0ac2aab8 = the probe commit); wc -l
Tue Oct 13 03:37:01 UTC 2026
e1cfd825 a62eb564 c9cae286 b187c9c3 aa2bec3e e31ec1c1 0ac2aab8 
    1493 RBM3D/BA/Step5IIIEdet.lean
$ lake build RBM3D.BA.Step5IIIEdet 2>&1 | tail -1; ... | grep -c "RBM3D/BA/Step5IIIEdet.lean" (warning/error lines of the file)
build exit 0
Build completed successfully (3850 jobs).
0
$ #print axioms of the 60 public declarations (theorem/def) of the file; sort | uniq -c
60 declarations
  60 [propext, Classical.choice, Quot.sound]
$ python3 stmt.py  (statements of targets 1-5 and the list/glue forms extracted from the file; text-equality with the pins of the check / the 1a-audit probe lines 113-130)
[baStep5IIIE_trace_mul_le  L61] theorem baStep5IIIE_trace_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) : ‖(A * B).trace‖ ≤ ‖A‖ * ‖B‖   ==> text-equal to T2482_TraceMulLe: True
[baStep5IIIE_trace_mul3_le  L79] theorem baStep5IIIE_trace_mul3_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C : Matrix ι ι ℂ) : ‖(A * B * C).trace‖ ≤ ‖A‖ * ‖B‖ * ‖C‖   ==> text-equal to T2482_TraceMul3Le: True
[baStep5IIIE_trace_prod_le  L87] theorem baStep5IIIE_trace_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] (l : List (Matrix ι ι ℂ)) (hl : 2 ≤ l.length) : ‖l.prod.trace‖ ≤ (l.map fun A => ‖A‖).prod   ==> text-equal to T2482_TraceProdLe: True
[baStep5IIIE_loop_hs  L255] theorem baStep5IIIE_loop_hs (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (hk : 2 ≤ k) : ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ ∏ i : Fin k, Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ i, !(σ i)] ![a i, a ((finRotate k).symm i)]‖   ==> text-equal to T2482_LoopHS: True
[baStep5IIIE_loop_hs_list  L275] theorem baStep5IIIE_loop_hs_list (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (hk : 2 ≤ k) : ‖STLIMg (baStep2Mat sz lam0 E) n u H ⟨List.ofFn σ, List.ofFn a⟩‖ ≤ ∏ i : Fin k, Real.sqrt ‖STLIMg (baStep2Mat sz lam0 E) n u H ⟨[σ i, !(σ i)], [a i, a ((finRotate k).symm i)]⟩‖   ==> text-equal to T2482_LoopHSList: True
[baStep5IIIE_loop_glue  L264] theorem baStep5IIIE_loop_glue (d : ℕ) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian) (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)) (p : Fin 6) : ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ p, σ (p + 1), !(σ (p + 1)), !(σ p)] ![a p, a (p + 1), a p, a (p - 1)]‖ * ∏ j ∈ ({2, 3, 4, 5} : Finset (Fin 6)), Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ (p + j), !(σ (p + j))] ![a (p + j), a (p + j - 1)]‖   ==> text-equal to T2482_LoopGlue: True
[BAStep5IIIEScalar  L300] def BAStep5IIIEScalar {d : ℕ} (sz : Sizes d) (n : ℕ) (u D Λ K₀ J : ℝ) : Prop := 3 ≤ d ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧ 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧ 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧ 1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)   ==> text-equal to T2482_BAScalar: True
[BAStep5IIIEMatrix  L308] def BAStep5IIIEMatrix {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop := H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a) ∧ (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧ (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) → ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧ (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧ (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧ (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧ (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))   ==> text-equal to T2482_BAMatrix: True
[baStep5IIIE_lk  L582] theorem baStep5IIIE_lk (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hθ : 0 < θ) (hCd : 0 < Cd) (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a   ==> text-equal to T2482_EdetLk: True
[baStep5IIIE_wG  L1156] theorem baStep5IIIE_wG (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hθ : 0 < θ) (hCd : 0 < Cd) (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)   ==> text-equal to T2482_EdetWG: True
$ lake env lean pins_ex.lean  (pins of the check + probe 113-130 copied by script; examples: T2482_TraceMulLe := @baStep5IIIE_trace_mul_le, TraceMul3Le, TraceProdLe, forall d, T2482_LoopHS/LoopHSList/LoopGlue/EdetLk/EdetWG d := baStep5IIIE_*, and the two bundle defs by rfl)
exit 0
$ lake env lean docs/tickets/checks/T2482-check.lean (on the branch)
exit 0; error lines: 0
$ instances in the file (grep -n): examples and scalar witnesses
1391 1396 1402 1409 1417 1429 1436 1438 1440 1444 1451 1458 1468 1480 
$ C1 grep 1 (BAK_le_small|BAMB_upper_small|BAGbEXP|Mbound_AO|W^(-eps|BAm_im_lower_window); C1 grep 2 (STGridRepNgL|withLam|\|E\||norm_mE|mSigma|SB d|E2Hyp|gexRHS|STGMMg|<= A *); hygiene (sorry|admit|native_decide|axiom)
rc=1
rc=1
rc=1
$ UBA-C1: lines of the file that read sz.lam (size level); crossing grep "lam0 <=|gK" (R1 / guarded form)
sz.lam read at lines: 301 344 
rc=1
$ git diff --stat main...t/T2482; importers of the module
 RBM3D/BA/Step5IIIEdet.lean | 1493 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2482Pins.lean |  395 ++++++++++++
 2 files changed, 1888 insertions(+)
files mentioning the stem outside the file (importers): none
$ pre-check: import RBM3D + import RBM3D.BA.Step5IIIEdet + #assert_rbm_axioms (Test/Axioms.lean unchanged)
pre.lean:3:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:   [RBM.BA.BAStep5IIIEMatrix] Classify each of them: borrowed from the literature, owed by this formalization, a predicate that defines the objects under study, refuted (shown false and superseded), or superseded (not needed). 
$ date -u
Tue Oct 13 03:37:26 UTC 2026
`wc -l` at the section commits (tool log): 663 (e31ec1c1), 973 (aa2bec3e), 1380 (b187c9c3), 1493 (c9cae286, e1cfd825) against the stop line 2,000. By section: header 53 (L1-53), HS core + list/glue + swap 242 (L54-295), bundle 26 (L296-321), scalar facts 156 (L322-477), legs 65 (L478-542), `lk` 125 (L543-667), `wG` 717 (L668-1384), instances 109 (L1385-1493). (a″) row (xi) estimated 1,262 for this file; `Step5IIIEdet3` is not used; with (a″)'s 1,188 for U5b-2 the central is 2,681, below the REQ trigger 3,600.
Name-clash (`clash.sh`, 03:27:23-03:28:02 UTC): `git grep -c -E 'Step5IIIEdet|BAStep5IIIE|baStep5IIIE' <ref> -- RBM3D` over 493 local refs (all but t/T2482, t/T2482b): 0 files with hits (main: 0, T2481 is merged in it); other worktrees (uncommitted files included): none; main worktree `RBM3D/`: none; `docs/tickets/checks/`: only T2482-check.lean (header comment) and T2485-check.lean (comment lines 6, 8, 9, 242). Names added after that scan: none (the later edits are docstrings).
Hypothesis table (script `grep -noE 'hm\.[12](\.[12])*'` on the file): Hermitian `hm.1` L905, 929, 953 (`wG_far2/far3/ball`; target 2 needs only this); (i) `hm.2.1` L500 (`leg_plus`), L616 (`lk`); (iii) `hm.2.2.2.1` L499 (`leg_plus`); (iv) `hm.2.2.2.2.1` L1209-1210 (`wG`); (v) k=2 `hm.2.2.2.2.2.1` L488 (`leg_short`); (v) k=3 `hm.2.2.2.2.2.2.1` L1278-1279 (`wG`, ball with r ≤ 2ℓ*). Unread in U5b-1: (ii) (the `K₀` bound), (v) k=4, k=6, (vi) (all three are for `dif`, U5b-2). Scalar part: every conjunct is read except `0 < sz.lam n` (named at L341, 361, never used) and `J ≤ W^{1/2}` (`-` in every `obtain`, L333-361); `1 ≤ K₀` only through the loss.
Census: merged lemmas read (file:line): `LemDecCalE_sum_tail_tail` LemDecCalE:395, `LemDecCalEwG_sum_sqrt_tail` EwG:318, `LemDecCalE_e10a` :186, `LemDecCalE_e1` :486, `LemDecCalE_e4c` :550, `LemDecCalE_tailT_anti` :515, `lossE2` :54, `lossE2wG` EwG:74, `tailTD_nonneg` Defs/Tail:177, `loopM_eq_loopL` Loop/GLoopFlow:127, `Eblk_isHermitian` Loop/GLoop:66, `BAAuxGraph2_seqHflowBA_herm` Graph/BAAuxGraph2:448. `open private` (L43), 2 names, both from `Path/LemDecCalE`: `lemDecCalE_zdistInf_sub_comm` :131, `lemDecCalE_zdistInf_tri_real` :140. Copies: `lwWx_Gres_conjTranspose` (`Graph/LWWeightExp.lean:115`) as `Step5IIIEdet_Gres_conj` (L159, no import of `Graph/LWWeightExp`); `T2459_trace_mul_le`, `_mul3_le` (`t/T2459:RBM3D/Probe/T2459Pins.lean:281`, `:299`, commit 2a6ad6e0) as targets 1 (a), (b); the HS core, glue and list proofs are the probe's (0ac2aab8, lines 137-353) renamed; `lk` follows `lemDecCalE_lk` (`Path/LemDecCalE:786`) at `S = 1`. Not reused: `LemDecCalEdif` §1. No RBM1D/RBM2D text is ported here, so no diff-stat.
UBA-C1 table: not triggered. `sz.lam` is read at L301 (the bundle: `0 < lam`, `lam² ≤ 1 - u`, `1 ≤ lam² W^d`) and L344 (`Step5IIIEdet_Mu`) only; kernel level is `baStep2Mat sz lam0 E` with `lam0 E` free and 𝒦 only through bundle (i), (iii); no `lam0 ≤ sz.lam`, no `gK`, no `A` (grep above, rc=1). C1 and hygiene greps above: rc=1 (no hit, not even in comments). TN-C4: `STGridRepNgL` 0 hits.
Narrative. Realized E-a/E-b/E-c of (a): (1) §1-2 are the probe's Hilbert-Schmidt core (leg identity, rotation, glue identity, targets 1-2, list and glue forms, swap), proved for every Hermitian `H` and every `z`, no entry bound; `Step5IIIEdet_loop3_legs` is target 2 at `k = 3`. (2) `lk` (L582): `S = 1` collapses the double sum, bundle (i) gives `J T` on both factors, `LemDecCalE_sum_tail_tail` with `A = τ²`, `w = W^{-D}` (floor `Step5IIIEdet_floor_one` from `(L^d W^{6d})² ≤ W^D`), `W^d τ² = (1-u)⁻¹ τ`, and `2 S_d + 1 ≤ lossE2wG` (`Step5IIIEdet_lk_const`). (3) `wG` (L1156): `S = 1` collapse, averages `≤ Λτ` (iv), the sum over x split at the ball `B = {|a₀-x| ≤ ℓ*} ∪ {|a₁-x| ≤ ℓ*}` (`Step5IIIEdet_sum_split`, `#B ≤ 2(2ℓ*+1)^d`); r ≤ 2ℓ*: x ∈ B by (v) k=3 (`J`-free), x ∉ B by `Step5IIIEdet_wG_far2`; r > 2ℓ*: x ∈ B by `_wG_ball` (shift `e^{Y}`, `LemDecCalE_e4c`), x ∉ B by `_wG_far3` (`J^{3/2}`); both 3-loops go through their legs (`loopA_legs`, `loopB_legs`; every leg `≤ Λτ` by (v) or, at distance ≥ ℓ*, `≤ 2 J T` by (i), (iii) and the swap for charge (-,+)); the x-sum is `LemDecCalEwG_sum_sqrt_tail`; `Step5IIIEdet_wG_final_near/_far` are the real-number comparisons (`τ ≤ 1`, `J ≤ J√J`, `τ ≤ √τ`), `Step5IIIEdet_wG_const` the loss (`(8(2ℓ*+1)^d + 6 C_sq) Λ² e^{√2 Y} ≤ lossE2wG`, via `Step5IIIEdet_loss_ge`). The four cases of the (a) table are: wG1 = (v) k=3, wG2 = `_wG_far2`, wG3 = `_wG_ball`, wG4 = `_wG_far3`. (4) Instances (L1391-1480): targets 1 at `2 × 2` matrices; target 3 by the two witnesses `Step5IIIEdet_scalar_sz0_one` (n=1) and `_800` (n=800: every window nonempty, 1a-audit §6.2); target 2 at `H = 0` (k = 3, 6), at `seqHflowBA`, list and glue at `H = 0`; targets 4, 5 at n=800 (and `lk` at n=1) with the matrix part a hypothesis (audit O2). (5) No stop rule fired: no entry-level bound of `G`, `|E|<2`, `M = mI`, `SB d` or equal-charge 𝒦 bound is used (greps), every `J` term of `wG` carries `√τ` (`final_near`, `final_far`), `lossE2wG` dominates (Lean: `lk_const`, `wG_const`), the file is below 2,000 lines.

## (c) Verified Mathlib names (37 `#check`s in `T2482/b1/names.lean`, exit 0, 0 error lines; the earlier-listed names of (a″) stay)
`Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_le_iff`, `Real.sqrt_le_left`, `Real.exp_half`, `Real.sqrt_eq_rpow`, `Real.rpow_add`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_two`, `Real.log_pow`, `Real.log_le_log`, `Real.one_le_exp`, `Real.exp_le_exp`, `Real.rpow_neg`, `Real.rpow_nonneg`, `Real.sqrt_sq`, `Real.mul_self_sqrt`, `Real.sqrt_eq_zero_of_nonpos`, `Finset.sum_ite_mem`, `Finset.univ_inter`, `Finset.card_union_le`, `Finset.card_le_card`, `Finset.sum_const`, `nsmul_eq_mul`, `inv_le_one_of_one_le₀`, `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `Fin.prod_univ_three`, `Matrix.one_apply`, `Matrix.isHermitian_zero`, `Matrix.IsHermitian.submatrix`, `Matrix.frobenius_norm_mul`, `Matrix.frobenius_norm_def`, `List.norm_prod_le'`. Verified absent (probe step, (a″)): a Frobenius trace Cauchy-Schwarz (proved in the file as target 1 (a)).

## (d) Open issues and paper-delta candidates
1. **Registry finding (blocks the merge as the ticket is written).** The pre-check line above fails: `#assert_rbm_axioms` finds the premise `RBM.BA.BAStep5IIIEMatrix` in none of the five lists. Before the two scalar witnesses (L1409, L1417) the same check listed `[RBM.BA.BAStep5IIIEScalar, RBM.BA.BAStep5IIIEMatrix]`; a theorem concluding the predicate satisfies the scan, so `BAStep5IIIEScalar` is cleared by the witnesses. The matrix part has no witness here by design (audit O2: it is U5c's good event), so the ticket's "Registry: none" and "passes with `Test/Axioms.lean` unchanged" cannot both hold; hub rule (A) 5 will set `blocked`. Proposed line for `owedProps` (dispatcher/hub, not a ticket file): `RBM.BA.BAStep5IIIEMatrix, -- matrix part of U5b's premise bundle (BA/Step5IIIEdet.lean:308), hypothesis of baStep5IIIE_lk, baStep5IIIE_wG (T2482); concluded at seqHflowBA by U5c's good event (owner U5c)`. Note for U5c: its check (T2485-check.lean:6-9) uses local copies `T2485_BAScalar/BAMatrix`; the scan compares head constants, so only a theorem concluding `BAStep5IIIEMatrix` itself removes the line.
2. Windows at the ticket instance: at n=1, `L/2 = 4 < ℓ* = 18.25` ((a) F1), so the far sets are empty; the 1a-audit (§6 item 2) asks for an n=800 instance of target 7; the same is done here for 4, 5, and the n=1 instance of `lk` is kept. 3. Bundle conjunct (ii) and `J ≤ W^{1/2}` are read by no step (F2 of (a)); (v) k=4, k=6 and (vi) are read only by U5b-2. 4. For U5b-2 (stacked on this file): reusable public helpers `Step5IIIEdet_leg_short`, `_leg_long`, `_leg_long'`, `_swap`, `_loop3_legs` (the `k = 6` case is `baStep5IIIE_loop_glue`), `_floor`, `_floor_one`, `_tail_eq`, `_tail_ge`, `_tau_sq_le`, `_tau_le`, `_shift_one`, `_near_norm`, `_loss_ge`, `_sum_split`, `_sqrt_le_self`, `_rpow_three_halves`; the `lossE2wG` factorisation is `Step5IIIEdet_loss_ge` (`10¹² (1.6·10⁶ d⁴)^d Λ⁶ e^{8Y} (1+log P)^{2d} ≤ lossE2wG`). 5. Paper-delta candidates: none new. The statements differ from the paper only as already proposed: T2459b (indicator at 2ℓ* in `wG`), T2459c (HS route instead of `lem_GbEXP_BA`, no paper statement); T2459f belongs to U5b-2.
