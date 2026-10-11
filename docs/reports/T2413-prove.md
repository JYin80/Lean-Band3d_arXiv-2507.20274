Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 09:08:35 UTC 2026

Sources: TP = `docs/tickets/T2398-TL-proofs.md`; AN = `T2398-analysis-fable.md`; S52 = `docs/supervisor/2026-10-11-0652.md`; P = `paper/tex/`. Targets restated: TL1 `|Tr(G̊P_{c₂c₁})| ≺ W^{-d}B_{τ,0}`; TL2 `|L̃−K̃| ≺ (W^{-d}B_{τ,0})^{3/2}`; T.12′ (e_s ⇒ TL2 on [s,t]); base case `L̃₀=K̃₀`; `twK_bound`; `twFold`, `twWard`, `twCirc`. `x := W^{-d}B_{u,0}`, `B_{t,K}=(g²+|1−t|)^{-1}(K+1)^{-(d-2)}+L^{-d}|1−t|^{-1}` (P `1_2_Intro_model_result.tex:1105-1113`).

### (i) Exponent table
| # | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | TL1 exponent | 1 (`Bctl¹`, loss `W^ε`) | T3B consumes it at 1 (AN §4 table, T3B row: "no slack"; S52:49-53) | 0 |
| 2 | T.7 Step 4: `|𝒮_i| ≺ x^{3/2+1/2}` | 2 | `L⁽⁴⁾≺x³` (I3, n=4), `L⁽²⁾≺x` (n=2); bootstrap `X²≤αX+β` needs `β∝x²` (TP:83-90) | 0 |
| 3 | T.7 Step 5: `C_M W^ε x ≤ 1/2` | at instance 4.3e-13 .. 1.5e-11 (script [D]) | `ε<𝔡` (TP:90 takes `𝔡/2`) | huge |
| 4 | TL2 pin exponent | 3/2 | I41 (ii) `tr·(L̃−K̃)·K ≺ η⁻¹x^{5/2}` needs exactly 3/2 (S52:51; AN §3.3 (ii)); target (B.1) `η⁻¹x^{5/2}` (P `B_graphical_lemmas.tex:5-10`) | 0 |
| 5 | T.12′ output `γ*=min{γ,2−1/(4p)−1/(2q)}` (TP:153) | γ=3/2: need `1/(4p)+1/(2q) ≤ 1/2` | (p,q)=(1,2): 1/2; (2,2): 3/8; (1,1): 3/4 FAILS (γ*=5/4) | 0 / 1/8 / <0 |
| 6 | T.11(i),(ii) sources | `η⁻¹x²` (→ `x²log W` after ∫) | ≥ γ*=3/2 (TP:138-139, 157) | 1/2 |
| 7 | T.11(iii) `e=4−1/(2p)−1/q`; martingale gives `e/2` | (1,2): e=3; (2,2): 3.25 | `e/2 ≥ 3/2` ⇔ row 5; regime (i) integral needs `e ≥ 2` (derived: `(g²+1−v)^{2−e}≤(g²+1−u)^{2−e}`); TP:165 writes `e−2≥1` | e−2 = 1 / 1.25 (0 vs TP:165 at (1,2)) |
| 8 | T.11(iv) `γ*+1/6` | 5/3 | ≥ 1 (TP:164) | 2/3 |
| 9 | bootstrap `Ξ̃ ≺ 1+x^{1/6}Ξ̃` ((4.16) exponent 1/6, TP:145, 171) | `W^ε x^{1/6}` = 0.0104 at ε=1/200 | < 1/2; crude form via `x≤W^{-𝔡}`: `ε<𝔡/6` = 1/120 | 0.49 (true x) |
| 10 | (2.82) `x_t^{c_d'} ≤ (1−t)/(1−s) <1`, `c_d' ≤ c_d ≤ 10^{-2}` (P `1_2_Intro_model_result.tex:1296`) | ratio 0.95 | admissible `c_d' ∈ [0.00203, 0.01]` at g=1/64; `[0.00185,0.01]` g=1; `[0.00165,0.01]` g=10 | 0.0080 |
| 11 | #steps `≤ (1−ε)/(2𝔡𝔠c_d')` (TP:185) | 3309.6 (𝔠=0.2719, c_d'=1/100) | a finite constant in W | — |
| 12 | regimes: (i) `1−t ≥ g²/L²`, (ii) `1−s ≤ g²/L²` (TP:155-167); T.10(d) needs `(1−v)L²/g² ≤ 1` | g=10, L=8: `g²/L²=1.56 ≥ 1` ⇒ regime (i) empty, (ii) covers all `v∈[0,1)`, `(1−v)L²/g² ≤ 0.64` | holds | 0.36 |
| 13 | T.10(a) `‖Ũ‖_{∞→∞} ≤ (1−v)/(1−u)` | equality for (−,+) at (v,u)=(.9,.95) (script [B]) | sharp | 0 |
| 14 | T.10(c) `C₂` ((+,+), v=0,u=.999, L=8) | 0.501 / 1.256 / 1.416 at g=1/64,1,10 | finite, no smallness of g | — |
| 15 | T.10(d) `‖Q⁽¹⁾Ũ‖` | ≈2.0 (g=1/64,1; L=16,32); g=10: 8.06 (L=16, v=0.61), 2.06 (L=32) | "≺ 1" (TP:126), constant in (d,κ,𝔡) | — |
| 16 | T.1(i) constant `C` in `|K̃| ≤ C x` | observed `max|K̃|/x` = 0.996 / 0.759 / **11.42** at g=1/64,1,10 (L=8) | so `C=1` is false at g=10: `twK_bound` must keep `∃C(d,κ,ε,𝔡)` (it does, probe 360; T2398 audit O2) | — |
| 17 | T.1(ii) `Σ_a|K̃| ≤ W^{-d}(1−u)⁻¹` | `W^d(1−u)Σ|K̃|` = 1.000 (c₂=c₁, all charges) | ≤ 1; Lean form `(W^dη)⁻¹`, `η=(1−u)Im m ≤ 1−u` is weaker | 0 / `Im m` factor |
| 18 | T.12″ `D_u=0` (TP:175) | `|D_u|` ≤ 1.5e-25 vs `|L^{-d}ΣK̃|` ≥ 9.5e-16 | exact | — |
| 19 | constants (C1): `κ=Im m/2`; `Im m` | 0.9993 / 0.4665 / 0.3654 at g=1/64,1,10 (d=3,L=8,E=0; T2398-design.md:116 lists 0.6860/0.6669 at g=1,10 and TP:20 says κ′≈0.044 at g=10: other data, not reconciled); `g²+1` = 1.0002/2/101; `C_M=Σ|M_ab|` = 1.10/15.6/13.4; T.7 `(C.1)` const `2C_M+2√(pC_M)` (p=1) = 4.3/39.2/34.1 | depend on `(d,κ,𝔡)` only; no smallness of g, no scalar m | — |
| 20 | D3: decay `|a−c₁|` for L4b2 terms (iii),(iv) | NOT needed: (iii) uses `|K̃| ≤ C x` and `Σ_{c₂}|K⁽²⁾| ≤ C(W^dη)⁻¹`; (iv) uses TL1 only (AN §3.3 (iii),(iv); S52:52-53); target (B.1) is at fixed `(a,b)` with no `|a−b|` decay (P `B_graphical_lemmas.tex:5-10`) | `twK_bound` (`Bctl` form) suffices; T.1(iii) decay is internal to TL2 (TP:137, T.11(v)) | — |

### (ii) Concrete instance and checks
d=3, L=8, W=10⁴ (N=5.12e14, 𝔠=logW/logN=0.2719), 𝔡=1/20, ε=0.1 (flow domain), g∈{1/64,1,10}, E=0, κ=Im m/2 (BAReal: `κ ≤ Im m`), s,t with 1−s=0.100, 1−t=0.095, p=q=2, γ=3/2, ε_≺=1/200, c_d'=1/100. Hypotheses at once: `W^{-d/2+𝔡}≤g≤𝔡⁻¹` (TP:16, (2.10)), `η_u≥N^{-1+ε}`, (2.82), `Im m ≥ κ`, (8.4), `x ≤ W^{-𝔡}`, `g²/L²` regimes, rows 5-10 above. Base case `(e_s)` at s=0 holds exactly (check [C], all 4 charges, c₁≠c₂). Part [C] uses the probe's own index conventions (`twLoopX`, `twTrP`, `twChg`, `twSq`, copied from `t/T2398:RBM3D/Probe/T2398Pins.lean:276-365`) on a 216×216 fine matrix, G=(H−z)⁻¹ genuine resolvent (nonvacuous `twWard`, `twCirc`: T2398 audit O3/O4). External ≺-hypotheses (`STLKgL`, `STLmaxgL`, `LWAvgLawgL`, `STLocalEntrygL`, `BAGbEXPii`, (e_s)) are asymptotic in W: limit computation in [D] (x→0, x^{3/2}→0, `x^{c_d'}≤ratio`, `W^ε x^{1/6}`→0 as W→∞).

Command: `cd <scratchpad>/T2413 && python3 pre.py` (script is Python, no Lean). Output:
```
[A] d=3 W=10000 L=8 N=5.120e+14 c=logW/logN=0.2719 (W=N^c) frak_d=0.05 eps=0.1
   (2.10)/(8.3): W^(-d/2+fd)=1.585e-06 <= g <= 1/fd=20 for g in 1/64,1,10: True; count constants g^2+1 = 1.0002, 2.0000, 101.0000
   (2.82) at 1-s=0.100, 1-t=0.095 (ratio 0.950<1): W^-d B_t0 = 1.05e-11, 9.34e-13, 3.05e-14; (W^-dB)^c<=ratio iff c>= 0.00203, 0.00185, 0.00165 ; nonempty with c<=c_d<=1e-2: True
   N^(-1+eps)=5.776e-14; W^-fd=0.6310 ; W^-d B_{u,0}<=W^-fd for g in {1/64,1,10}, u in {0,s,t}: True
[A2] exponent rows: (p,q) -> e=4-1/(2p)-1/q | e/2=2-1/(4p)-1/(2q) | 1/(4p)+1/(2q) | gamma*=min(3/2,e/2) | e-2 | eps<fd/6
   p=1,q=2: e=3.000000 e/2=1.500000 loss=0.500000 <=1/2:True gamma*=1.5000 e-2=1.0000
   p=2,q=2: e=3.250000 e/2=1.625000 loss=0.375000 <=1/2:True gamma*=1.5000 e-2=1.2500
   p=1,q=1: e=2.500000 e/2=1.250000 loss=0.750000 <=1/2:False gamma*=1.2500 e-2=0.5000
   p=4,q=4: e=3.625000 e/2=1.812500 loss=0.187500 <=1/2:True gamma*=1.5000 e-2=1.6250
   p=1000000,q=1000000: e=3.999998 e/2=1.999999 loss=0.000001 <=1/2:True gamma*=1.5000 e-2=2.0000
   gamma*+1/6=5/3 >=1; slack 2/3 ; eps<fd/6=1/120 ; (4.16) exponent 1/6 ; W^eps x^(1/6) at eps=1/200, x=W^-d B_t0(g=1)=0.0104 (needs <1/2)
   #steps <= (1-eps)/(2 fd c c_d') = 3309.6 at c=0.2719 c_d'=1/100 (T.12 text)
[B] BA static data d=3, L=8, E=0, W^d=1e12, c1=(0,0,0), c2=(1,1,0), u values in brackets
 g=0.01562: Im m=0.9993 |m|=0.9993 |m-mean(Mhat)|=3.3e-16 sum|M_ab|^2=1.000000000000 C_M=sum|M_ab|=1.101 ||M||_op=1.001<=1/Im m=1.001
   kappa=Im m/2=0.4996; eta_u=(1-u)Im m >= 0.095*Im m=0.0949 >= N^(-1+eps)=5.78e-14: True
   T.1 over u in {.5,.9,.999}, 4 charges, c2 in {c1,(1,1,0)}: max W^d(1-u)sum_a|K|=1.000 (<=1: T.1(ii)); max max_a|K|/(W^-d B_u0)=0.9956 (T.1(i) const, not 1 in general)
   T.12'' (-,+) u=0.999: row sum Theta=1000.000000 vs 1/(1-u)=1000.000000; |D_u|=2.65e-28 vs |L^-d sum K|=9.51e-16
   T.10(a) (-,+) v=0.9,u=0.95: max_a sum_b|U|=2.0000 <= (1-v)/(1-u)=2.0000
   T.10(c) (+,+) v=0,u=0.999: sum_b|U|=0.5010  (C_2 at L=8)
   T.10(d) (-,+) L=16, v=1-g^2/L^2=1.0000, u=1-1e-3 g^2/L^2: ||Q U||_(inf->inf)=2.0018 (U zero mode=1000)
   T.10(d) (-,+) L=32, v=1-g^2/L^2=1.0000, u=1-1e-3 g^2/L^2: ||Q U||_(inf->inf)=2.0015 (U zero mode=1000)
 g=1.00000: Im m=0.4665 |m|=0.4665 |m-mean(Mhat)|=1.8e-16 sum|M_ab|^2=1.000000000000 C_M=sum|M_ab|=15.625 ||M||_op=2.144<=1/Im m=2.144
   kappa=Im m/2=0.2332; eta_u=(1-u)Im m >= 0.095*Im m=0.0443 >= N^(-1+eps)=5.78e-14: True
   T.1 over u in {.5,.9,.999}, 4 charges, c2 in {c1,(1,1,0)}: max W^d(1-u)sum_a|K|=1.000 (<=1: T.1(ii)); max max_a|K|/(W^-d B_u0)=0.7585 (T.1(i) const, not 1 in general)
   T.12'' (-,+) u=0.999: row sum Theta=1000.000000 vs 1/(1-u)=1000.000000; |D_u|=7.59e-26 vs |L^-d sum K|=3.42e-13
   T.10(a) (-,+) v=0.9,u=0.95: max_a sum_b|U|=2.0000 <= (1-v)/(1-u)=2.0000
   T.10(c) (+,+) v=0,u=0.999: sum_b|U|=1.2560  (C_2 at L=8)
   T.10(d) (-,+) L=16, v=1-g^2/L^2=0.9961, u=1-1e-3 g^2/L^2: ||Q U||_(inf->inf)=2.0012 (U zero mode=1000)
   T.10(d) (-,+) L=32, v=1-g^2/L^2=0.9990, u=1-1e-3 g^2/L^2: ||Q U||_(inf->inf)=2.0004 (U zero mode=1000)
 g=10.00000: Im m=0.3654 |m|=0.3654 |m-mean(Mhat)|=3.1e-15 sum|M_ab|^2=1.000000000000 C_M=sum|M_ab|=13.378 ||M||_op=2.737<=1/Im m=2.737
   kappa=Im m/2=0.1827; eta_u=(1-u)Im m >= 0.095*Im m=0.0347 >= N^(-1+eps)=5.78e-14: True
   T.1 over u in {.5,.9,.999}, 4 charges, c2 in {c1,(1,1,0)}: max W^d(1-u)sum_a|K|=1.000 (<=1: T.1(ii)); max max_a|K|/(W^-d B_u0)=11.4196 (T.1(i) const, not 1 in general)
   T.12'' (-,+) u=0.999: row sum Theta=1000.000000 vs 1/(1-u)=1000.000000; |D_u|=1.54e-25 vs |L^-d sum K|=3.45e-13
   T.10(a) (-,+) v=0.9,u=0.95: max_a sum_b|U|=2.0000 <= (1-v)/(1-u)=2.0000
   T.10(c) (+,+) v=0,u=0.999: sum_b|U|=1.4160  (C_2 at L=8)
   T.10(d) (-,+) L=16, v=1-g^2/L^2=0.6094, u=1-1e-3 g^2/L^2: ||Q U||_(inf->inf)=8.0585 (U zero mode=1000)
   T.10(d) (-,+) L=32, v=1-g^2/L^2=0.9023, u=1-1e-3 g^2/L^2: ||Q U||_(inf->inf)=2.0556 (U zero mode=1000)
[C] probe conventions (twLoopX, twTrP, twChg, twSq) at d=3,L=3,W=2 (W^d=8,N=216), g=1, E=0, z=iη, η=0.3, c1!=c2
   M^(B) residual |(gPsi-E-m)M-1|=4.5e-16 (E=0,g=1)
   base case L~_0=K~_0 (G_0=M), all 4 charges, all a, c1=(0, 0, 0), c2=(1, 1, 0): max err=3.5e-18; typical |K~_0|=1.346e-02
   Ward hyp: |G-G*-2i eta G G*|=3.2e-15, |G-G*-2i eta G* G|=3.0e-15
   twWard sigma=True: |lhs-rhs|=2.9e-17, |lhs|=4.957e-02, |Tr(GP)|=1.286e-01 (nonzero, c1!=c2)
   twWard sigma=False: |lhs-rhs|=6.4e-17, |lhs|=4.957e-02, |Tr(GP)|=1.286e-01 (nonzero, c1!=c2)
   twCirc (X1=G*, X2=G, M=Mfine, MB=M^(B)): max_a |lhs-rhs|=4.1e-18
   twFold: max |L~|^2/(sq*sq) over 20 random draws=0.022 (<=1); with X_i=G(sigma_i): 0.134
[D] limit W->inf at fixed d=3,L=8,g=1,1-s=.1,1-t=.095: x=W^-d B_t0 ; x^(3/2) ; x^(c) with c=1/100 vs ratio .95 ; W^eps x^(1/6) at eps=1/200 (<1/2 needed)
   W=1e+02: x=9.338e-07  x^1.5=9.024e-10  x^0.01=0.8704 <=0.95:True  W^eps x^(1/6)=0.1012
   W=1e+03: x=9.338e-10  x^1.5=2.854e-14  x^0.01=0.8123 <=0.95:True  W^eps x^(1/6)=0.0324
   W=1e+04: x=9.338e-13  x^1.5=9.024e-19  x^0.01=0.7581 <=0.95:True  W^eps x^(1/6)=0.0104
   W=1e+05: x=9.338e-16  x^1.5=2.854e-23  x^0.01=0.7075 <=0.95:True  W^eps x^(1/6)=0.0033
   W=1e+06: x=9.338e-19  x^1.5=9.024e-28  x^0.01=0.6602 <=0.95:True  W^eps x^(1/6)=0.0011
   T.7 g=0.01562: C_M=1.101; step-5 need C_M W^eps x<=1/2 (eps=1/200): 1.21e-11; (C.1) const 2C_M+2sqrt(p C_M) = 4.30 (p=1), 5.17 (p=2)
   T.7 g=1.00000: C_M=15.625; step-5 need C_M W^eps x<=1/2 (eps=1/200): 1.53e-11; (C.1) const 2C_M+2sqrt(p C_M) = 39.16 (p=1), 42.43 (p=2)
   T.7 g=10.00000: C_M=13.378; step-5 need C_M W^eps x<=1/2 (eps=1/200): 4.28e-13; (C.1) const 2C_M+2sqrt(p C_M) = 34.07 (p=1), 37.10 (p=2)
```

### Verdicts
- **TL1 (T.7), TL2 (T.12′, T.12, T.13), base case, `twFold`/`twWard`/`twCirc`/`twK_bound` (probe statements): PASS.** Every exponent in rows 1-20 closes at the instance; the three zero-slack rows are 1, 2, 4 (as the consumer needs) and row 5/7 at (p,q)=(1,2). No failing hypothesis set found. Fix p,q with `1/(4p)+1/(2q) ≤ 1/2` ((1,1) fails; (2,2) gives slack 1/8 and `e−2=1.25`).
- Not done at this stage (outside (i)-(ii)): the step-by-step proofs of T.7–T.13 are not re-derived here, only their exponent arithmetic, constants, and the model-free identities. Identity numerics ([B],[C]) used static data (E=0, d=3), not the flow; they check T.1(ii), T.3, T.10(a), T.12″, `twWard`, `twCirc`, `twFold`, `L̃₀=K̃₀`.
- Observations for stage 1b: (1) row 7: TP:165 writes `e−2 ≥ 1`, which holds only with equality at (1,2); the derived need is `e ≥ 2`. (2) row 16: constant `C` in `twK_bound` is not 1 (11.42 at g=10, L=8). (3) row 19: T2398-design.md:116 and TP:20 `Im m` values at g=1,10 differ from the E=0, d=3, L=8 recomputation; not reconciled. (4) row 12: at g=10, L=8 regime (i) is empty (all times are regime (ii)).

## (b) Script output — Sun Oct 11 10:06:16 UTC 2026 (`date -u`)
Probe `RBM3D/Probe/T2413Pins.lean`, branch `t/T2413`, base `c33ef56`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2413`. Scripts (scratchpad `T2413/`, not in the repository): `axgen.py`, `verb.py`, `ext.py`, `chk.py`, `rows.py`, `mkprove.py`.
```
$ lake env lean RBM3D/Probe/T2413Pins.lean; echo "exit=$?"
exit=0
$ lake build RBM3D.Probe.T2413Pins > build.out 2>&1; echo "exit=$?"; tail -2 build.out; grep -c 'T2413Pins.lean:' build.out   # warnings of the probe itself
exit=0
✔ [3997/3997] Built RBM3D.Probe.T2413Pins (5.4s)
Build completed successfully (3997 jobs).
0
$ for c in 69e0c82 40fcc14 a0ca35e 20d7445 5ff560c a77145a fcdfdc0; do git show $c:RBM3D/Probe/T2413Pins.lean | wc -l; done   # stop size 400, checked at each commit
69e0c82 181
40fcc14 259
a0ca35e 327
20d7445 369
5ff560c 370
a77145a 381
fcdfdc0 383
$ git diff --stat main...t/T2413; wc -l RBM3D/Probe/T2413Pins.lean
 RBM3D/Probe/T2413Pins.lean | 383 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 383 insertions(+)
     383 RBM3D/Probe/T2413Pins.lean
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2413Pins.lean | wc -l
       0
```
**Axioms.** `python3 axgen.py` renames each `example` to a `def exNN` in a scratch copy and appends `#print axioms` for the 4 theorems and the 20 examples:
```
[propext, Classical.choice, Quot.sound]: twTr_eq twMB_ba twK_ba twFrame_inst ex01 ex02 ex03 ex04 ex05 ex06 ex07 ex08 ex09 ex10 ex11 ex12 ex13 ex14 ex15 ex16 ex17 ex18 ex19 ex20  (24 declarations)
```
(`exNN` in the order of the probe: 01 T.12', 02-06 T.11 (i)-(v), 07 TL1 producer, 08 base case, 09 `BAMainIndTL`, 10 `BAMLOutTL`, 11 `BAChainTL`, 12 `twK_bound` with `c₂ ≠ c₁`, 13 `twWard`, 14 `twCirc`, 15 `twFold`, 16 T.10 (a), 17 T.10 (c), 18 T.10 (b), 19 T.10 (d), 20 T.12''.)
**Verbatim check** against `t/T2398:RBM3D/Probe/T2398Pins.lean` at `6429bb5` (`python3 verb.py <old> <new>`: the text from the docstring to the end of the body, line by line):
```
name | identical text (docstring + body) | lines | line in T2398 probe | line in T2413 probe
twBlk                  True    3  203   43
twShift                True    4  208   47
twTr                   True    4  213   51
convention docstring   True    3  276   53
twChg                  True    2  281   57
twTrP                  True    3  284   59
twLoopX                True    3  288   62
twTr_eq                True    1  295   64
twL2'                  True    3  298   66
twMB                   True    3  302   69
twK                    True    4  306   72
twMB_ba                True   11  311   76
BATwistAvgLaw          True    4  323   87
BATwistLoopLaw         True    5  328   91
twSq                   True    3  336   96
twFold                 True    4  340   99
twWard                 True    6  345  103
twCirc                 True    7  352  109
twK_bound              True    7  360  116
all identical: True
```
**Target statements extracted by script** (`python3 ext.py <probe> <names>`; probe line first; `BATwistAvgProd`, `BATwistLoopStep`, `BATwFrame`, `BATwistLoopBase`, `BAMainIndTL` are in `T2413-design.md` §1; the copied pins `BATwistAvgLaw`, `BATwistLoopLaw`, `twFold`, `twWard`, `twCirc`, `twK_bound` are at probe 87, 91, 99, 103, 109, 116, verbatim):
```
127: def twSteps (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STStep2ConclgL C μ s t Cd ∧
  (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ τ' D' : ℝ, 0 < τ' → 0 < D' → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')))
172: def BAMLOutTL (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
      STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ BATwistLoopLaw C μ t
178: def BAChainTL (d : ℕ) : Prop :=
  BAMainIndTL d STAny → STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z) →
    STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz → BATwistLoopBase d → BAMLOutTL d
185: def BATwKerA (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ σ₁ σ₂ : Bool, ∀ v u : ℝ, 0 ≤ v → v ≤ u → u < 1 → ∀ A : Zd d L → ℂ,
      ‖BAuKer d L g E m v u σ₁ σ₂ *ᵥ A‖ ≤ (1 - v) / (1 - u) * ‖A‖
191: def BATwKerFar (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D →
    ∀ v u : ℝ, 0 ≤ v → v ≤ u → u ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - u) / (1 - v) → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ σ₁ σ₂ : Bool, ∀ (c₁ : Zd d L) (A : Zd d L → ℂ),
        (∀ b, W ^ ε * ellT L g v ≤ (zdistD d L (b - c₁) : ℝ) → ‖A b‖ ≤ W ^ (-D)) →
        ‖BAuKer d L g E m v u σ₁ σ₂ *ᵥ A‖ ≤ (1 + C₁ * W ^ (2 * ε) * ((g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|))) * ‖A‖ + W ^ (-D + 1)
201: def BATwKerZero (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ σ₁ σ₂ : Bool, ∀ v u : ℝ, 0 ≤ v → (1 - v) * (L : ℝ) ^ 2 ≤ A * g ^ 2 → v ≤ u → u < 1 →
      (open scoped Matrix.Norms.Operator in ‖projMat d L * BAuKer d L g E m v u σ₁ σ₂‖) ≤ C
209: def BATwistZeroMode (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
    (∀ n, t n ≤ BAflowT0 sz z n) → ∀ (n : ℕ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → ∀ c₁ c₂ : Zd d (sz.L n), ∑ a, twK (baFMz sz z) n (t n) σ a c₁ c₂ =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (((baFMz sz z).eta n (t n) : ℝ) : ℂ))⁻¹ *
        (BAMsigma d (sz.L n) (twMB (baFMz sz z) n) true c₂ c₁ - BAMsigma d (sz.L n) (twMB (baFMz sz z) n) false c₂ c₁)
253: def BATwistSrc1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  twSrc C μ s t (fun n v ω σ a c₁ c₂ => ‖twB1 C n v ω σ a c₁ c₂‖) (fun _ _ => 1) 2
255: def BATwistSrc2 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  twSrc C μ s t (fun n v ω σ a c₁ c₂ => ‖twEG C n v ω σ a c₁ c₂‖) (fun _ _ => 1) 2
257: def BATwistSrc3 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  (∀ p q : ℕ, 1 ≤ p → 1 ≤ q → twSrc C μ s t (fun n v ω σ b c₁ c₂ => ‖twEE C n v ω σ b b c₁ c₂‖) (fun _ _ => 1)
    (4 - 1 / (2 * (p : ℝ)) - 1 / (q : ℝ))) ∧
  ∀ n v ω σ b b' c₁ c₂, ‖twEE C n v ω σ b b' c₁ c₂‖ ≤ Real.sqrt (‖twEE C n v ω σ b b c₁ c₂‖ * ‖twEE C n v ω σ b' b' c₁ c₂‖)
261: def BATwistSrc4 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun sz C μ s t =>
  ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → ∀ Ξ : ℕ → sz.SeqΩ → ℝ, (∀ n ω, 1 ≤ Ξ n ω) →
    (∀ n ω (v : ℝ) σ a c₁ c₂, s n ≤ v → v ≤ t n → ‖twL2' C n v ω σ a c₁ c₂ - twK C n v σ a c₁ c₂‖ ≤ Ξ n ω * sz.Bctl n v ^ γ) →
    twSrc C μ s t (fun n v ω σ a c₁ c₂ => ‖twB2 C n v ω σ a c₁ c₂‖) Ξ (γ + 1 / 6)
265: def BATwistSrc5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun sz C μ s t =>
  twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twB1 C n v ω σ a c₁ c₂‖) ∧ twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twB2 C n v ω σ a c₁ c₂‖) ∧
  twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twEG C n v ω σ a c₁ c₂‖) ∧ twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twL2' C n v ω σ a c₁ c₂ - twK C n v σ a c₁ c₂‖) ∧
  ∀ b' : ∀ n, Zd d (sz.L n), twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twEE C n v ω σ a (b' n) c₁ c₂‖)
```
**The compiled nonempty instances** (`d = 3`, `sz0`: `L = 4`, `W = 32`, `λ = 1/64`; `flow_sz0`; `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0`; `STConStInd` by `s1Setup_conStInd_const`; flow point `Pf` of `(L, g) = (4, 1/2)`); every deterministic hypothesis is discharged, the other gates' pins (`twSteps`, `LWAvgLawgL`, `STLmaxgL`, `STG0M`, TL2 at `s`) stay hypotheses:
```
287: theorem twFrame_inst {Q : ∀ sz : Sizes 3, FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (h : BATwFrame 3 STAny Q) {Cd : ℝ} (hC : 0 < Cd)
    (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd) : Q sz0 (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) := by
  obtain ⟨c, hc, -, H⟩ := h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hC
  exact H (1 / 6) sz0 zSeq flow_sz0 _ _ (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) trivial
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) hc) hS
ex01 probe 297: example (h : BATwistLoopStep 3 STAny) := twFrame_inst h hC hS
ex02 probe 298: example (h : BATwistSrc1 3 STAny) := twFrame_inst h hC hS
ex03 probe 299: example (h : BATwistSrc2 3 STAny) := twFrame_inst h hC hS
ex04 probe 300: example (h : BATwistSrc3 3 STAny) := twFrame_inst h hC hS
ex05 probe 301: example (h : BATwistSrc4 3 STAny) := twFrame_inst h hC hS
ex06 probe 302: example (h : BATwistSrc5 3 STAny) := twFrame_inst h hC hS
ex07 probe 306: example (h : BATwistAvgProd 3) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baF
ex08 probe 310: example (h : BATwistLoopBase 3) (hG : STG0M (baFMz sz0 zSeq)) : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _
ex09 probe 312: example (h : BAMainIndTL 3 STAny) (hyp : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STDecaygL (baFMz s
ex10 probe 320: example (h : BAMLOutTL 3) : let C := baFMz sz0 zSeq; STLKgL C μ0 (fun _ => 1 / 2) ∧ STLmaxgL C μ0 (fun _ 
ex11 probe 324: example (h : BAChainTL 3) (hm : BAMainIndTL 3 STAny) (hh : STHorizonG 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ 
ex12 probe 328: example (h : twK_bound 3) : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 (sz0.L 0)) ≠ 0 ∧ ∀ a, ‖twK (baFMz sz0 zSe
ex13 probe 336: example (h : twWard sz0) : ∑ a, twLoopX 0 (twChg (Complex.I • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Id
ex14 probe 342: example (h : twCirc sz0) (X₁ X₂ : Idx 3 (sz0.L 0) (sz0.W 0) → Idx 3 (sz0.L 0) (sz0.W 0) → ℂ) (a c₁ c₂ : Z
ex15 probe 345: example (h : twFold sz0) (X₁ X₂ : Idx 3 (sz0.L 0) (sz0.W 0) → Idx 3 (sz0.L 0) (sz0.W 0) → ℂ) (a c₁ c₂ : Z
ex16 probe 351: example (h : BATwKerA 3 1 Pf.m0.im) (A : Zd 3 4 → ℂ) : ‖BAuKer 3 4 Pf.g0 Pf.E Pf.m0 0 (1 / 2) false true 
ex17 probe 354: example : BAEKSameRow 3 1 Pf.m0.im := baEKSameRow_holds 3 1 Pf.m0.im
ex18 probe 355: example (h : BATwKerFar 3 1 Pf.m0.im) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ A : Zd 3 4 → ℂ, A ≠ 0 ∧ ‖BAuKer 3 4 Pf.g0 Pf
ex19 probe 368: example (h : BATwKerZero 3 1 Pf.m0.im) : ∃ C : ℝ, 0 < C ∧ (open scoped Matrix.Norms.Operator in
ex20 probe 376: example (h : BATwistZeroMode 3) := h le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
```
**Name-clash grep** (public `def`/`theorem` names of the probe against `RBM3D/` and `RBM3D.lean`, probes excluded):
```
$ grep -o '^\(def\|theorem\) [A-Za-z0-9_'"'"']*' RBM3D/Probe/T2413Pins.lean | awk '{print $2}' | sort -u > names.txt; wc -l < names.txt
45
$ while read n; do grep -rnw --include='*.lean' -e "$n" RBM3D RBM3D.lean | grep -v '^RBM3D/Probe/'; done < names.txt | wc -l
0
```
Ports: none from RBM1D or RBM2D (no file of either was read for this ticket or changed); the copied text is from `t/T2398` (never merged), so no `git diff --stat` against a sister project applies.

**Narrative.**
- Design ticket TL-D: the only Lean is the probe `RBM3D/Probe/T2413Pins.lean` (383 lines, stop size 400; never merged) on `t/T2413`; the design is `docs/reports/T2413-design.md` (≤ 300 lines). Both reports live in the main worktree, as `T2398-design.md` did, so `git diff --stat main...t/T2413` is the probe only.
- Section 1 of the probe is 18 declarations and the convention docstring copied from `t/T2398:RBM3D/Probe/T2398Pins.lean` at `6429bb5` (table above); `twL2`, `twTie`, `twTie_ba`, `twTr_diag`, `twL2_eq` are not copied; blank lines between declarations are removed, the one inside the convention docstring is kept. No copied statement was changed, so there is no finding on them.
- New declarations: `twSteps`, `BATwFrame`, `BATwistAvgProd`, `BATwistLoopStep`, `BATwistLoopBase`, `BAMainIndTL`, `BAMLOutTL`, `BAChainTL` (D1, D6); `BATwKerA`, `BATwKerFar`, `BATwKerZero`, `BATwistZeroMode`, `twL3`, `twB1`, `twB2`, `twEG`, `twDer`, `twEE`, `twSrc`, `twDec`, `BATwistSrc1-5` (D2); theorems `twK_ba`, `twFrame_inst`; 20 examples. Statements are `def … : Prop`; besides the copied `twMB_ba`, `twTr_eq` the only proofs are `twK_ba` (from `twMB_ba`), `twFrame_inst` and the examples.
- Decisions that differ from the wording of the ticket (reasons in the design): the producer of TL1 has the two premises `LWAvgLawgL`, `STLmaxgL` (T.7 uses only (I2), (I3)); the ticket's "T.10 (i)-(iii)" is T.10 (a)-(d); T.12' takes Steps 1-4 on `[s,t]` (`twSteps`) as premises, since its proof uses them uniformly in `u`, and concludes per `τ`; T.10 (d) carries a constant `A` because the kernel has the flow coupling `g₀ ≤ g` (F1); `twK_bound` is unchanged (D3).
- Instances: every deterministic hypothesis is discharged at `sz0`, `flow_sz0`, `s ≡ 1/2 < t ≡ 2/3`, `STConStInd` by `s1Setup_conStInd_const`, and at the flow point `Pf` for T.10. What stays a hypothesis: Steps 1-4 on `[s,t]` (`twSteps`), `LWAvgLawgL`, `STLmaxgL`, `STG0M` and the pins of TL-V, and the statements themselves (the producers are not proved).
- Not done: no producer is proved; the grid form of T.8/T.9 is not compiled (probe at 383 lines); the numerics are static (`E = 0`, `d = 3`) and cover the deterministic parts only (design §8).
- Section (a) was not edited and I made no (a′) section: the `Im m` values of its row 19 are reproduced by `chk.py` [A], rows 5 and 7 were re-derived by hand from TP:153, 165, row 12 recomputed (`g²/L² = 100/64`), row 20 re-derived in design §3; the other rows were used as stated. The observations (1)-(4) of its verdict are carried in (d).

## (c) Verified Mathlib names used (all compile in the probe)
- `Real.one_le_rpow` (example 18); `Matrix.conjTranspose_smul`, `smul_smul`, `mul_smul`, `two_smul` (example 13); `Real.sqrt` (`BATwistSrc3`); `Complex.I`, `starRingEnd`, `Matrix.of` (verbatim part).
- `Matrix.Norms.Operator` (scoped instance: the `L∞` operator norm, `.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:33, 480-492`), used in `BATwKerZero` so that `‖projMat * BAuKer‖` is the `∞ → ∞` norm of T.10 (d); `open scoped Matrix` for `*ᵥ`.
- Names verified absent: none searched. Repository names (not Mathlib) used and checked by `#check`/compilation: `STStep2ConclgL`, `STdiamInf`, `BAuKer`, `BAEKSameRow`, `baEKSameRow_holds`, `STHorizonG`, `STBaseG`, `STG0M`, `FlowPt`, `exists_flowPt`, `s1Setup_conStInd_const`, `BAMfine_eq`, `one_le_ellT`, `BAmF_sz0_im_pos`, `t0_sz0`, `half_lt_t0`, `flow_sz0`.

## (d) Open issues and paper-delta candidates
- **Paper-delta candidates `T2413a`: none.** T2398d (supervisor 0652 Q4) stands. F1 (`g₀` against `g`) and F3 (Claim 4.5 at BA) of the design are Lean-side conventions, not paper statements.
- **Rows.** 10 rows (TL-D + 9), flag 15 > 12: a short REQ is due (0853 TLS Q1). TL0 adds `BATwistAvgLaw` and `BATwistLoopLaw` to `owedProps` (`RBM3D/Test/Axioms.lean:102-199`) with the owner texts of design §6; TL-V is a TL row, the step `BAMainIndTL` is BA-V's V2a.
- **Preflight observations carried** (verdict of section (a)): (1) TP:165 writes `e - 2 ≥ 1`, true with equality at `(p,q) = (1,2)`, the derived need is `e ≥ 2` (`(2,2)`: `e - 2 = 1.25`); (2) the constant of `twK_bound` is not 1 (11.42 at `g = 10`, `L = 8`): the `∃ C` form stays (design §3); (3) `Im m` at `g = 1, 10` in `T2398-design.md:116` and `κ' ≈ 0.044` in TP:20 differ from the recomputation at `E = 0`, `d = 3`, `L = 8` (0.4665, 0.3654): not reconciled, constants only; (4) at `g = 10`, `L = 8` regime (i) is empty (`g²/L² = 1.56 ≥ 1`).
- **Inputs that are not merged and enter the TL statements as hypotheses:** the carrier forms of `STLmaxU`, `STLKU` (U3s1) and `STDecayLoopU` (T7-BA); `STG0M` (BA-V `GLoopAtT0`); the carrier forms of Steps 3-6 (U3, U4, V1) for `BAMainIndTL`; `baStep2Mat` (T2415) for the grid form of T.8/T.9; `STContractM` at BA (T2416) for T.11 (iii).
- **Statement-level facts for the audit:** `BATwKerFar` uses `zdistD` (`ℓ¹`), `BATwistSrc5` uses `zdistInf` (`ℓ^∞`); the CS conjunct of `BATwistSrc3` needs `S` nonnegative real (true at `baFMz`, `S = I`); examples 1-6 and 9 are applications of frame statements, not proofs of them; the decay of `(Ẽ⊗Ẽ)` is stated for the first index with the second fixed (`BATwistSrc5`), the second index follows from `|(Ẽ⊗Ẽ)(b,b')| = |(Ẽ⊗Ẽ)(b',b)|`.

## Repair (audit round 1) — Sun Oct 11 10:17:14 UTC 2026 (`date -u`)
Commit `76c586e` on `t/T2413` (probe only). Items 1-3 of the audit's "Required for resubmission".
```
$ wc -l RBM3D/Probe/T2413Pins.lean
     387 RBM3D/Probe/T2413Pins.lean          (stop size 400)
$ lake env lean RBM3D/Probe/T2413Pins.lean; echo exit=$?
exit=0
$ lake build RBM3D.Probe.T2413Pins 2>&1 | tail -1; lake build RBM3D.Probe.T2413Pins 2>&1 | grep -c T2413   # 0: no probe warning
Build completed successfully (3997 jobs).
0
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2413Pins.lean | wc -l
       0
# AxProbe.lean: examples renamed auditEx01..20 (noncomputable def); #print axioms of them and twTr_eq, twMB_ba, twK_ba, twFrame_inst
$ lake env lean $S/AxProbe.lean 2>&1 | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
24
$ lake env lean $S/AxProbe.lean 2>&1 | grep -c "axiom"
24
$ git diff --stat main...t/T2413
 RBM3D/Probe/T2413Pins.lean | 387 +++++++++++++++++++++++++++++++++++++++++++++
$ git diff fcdfdc0 76c586e -U0 -- RBM3D/Probe/T2413Pins.lean | grep '^@@'      # six lines, joined, context text cut
@@ -177 +177,2 @@   @@ -180 +181,2 @@   @@ -325 +327,2 @@   @@ -349 +352 @@   @@ -369 +372,2 @@   @@ -372,3 +376,3 @@
$ sed -n 179,182p RBM3D/Probe/T2413Pins.lean                 # item 1: BAChainTL
def BAChainTL (d : ℕ) : Prop :=
  BAMainIndTL d STAny → STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z) →
    STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz → BATwistLoopBase d →
      (∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) → BAMLOutTL d
$ sed -n 328p RBM3D/Probe/T2413Pins.lean                     # example 11 (326-328): the new hypothesis and the application
    (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) : BAMLOutTL 3 := h hm hh hb ht hG
$ sed -n 371,373p RBM3D/Probe/T2413Pins.lean                 # item 2: example 19 (371-377), T.10 (d), A = 1
example (h : BATwKerZero 3 1 Pf.m0.im) : ∃ C : ℝ, 0 < C ∧ (open scoped Matrix.Norms.Operator in
    ‖projMat 3 4 * BAuKer 3 4 Pf.g0 Pf.E Pf.m0 (1 - Pf.g0 ^ 2 / 16) (1 - Pf.g0 ^ 2 / 32) false true‖) ≤ C ∧
    1 - Pf.g0 ^ 2 / 16 < 1 - Pf.g0 ^ 2 / 32 := by
```
- Item 1: `BAChainTL` takes `STG0M` at `baFMz` for every flow (the form of `Induction/MainIndBase.lean:157`; owed by BA-V `GLoopAtT0`, `RBM3D/Test/Axioms.lean:139`). Example 11 keeps it as a hypothesis (another gate's pin). Design §0 row D6, §6 and §7 are corrected; §2 (T.10 instances) states the new example 19.
- Item 2: example 19 discharges `0 ≤ v`, `(1 - v)·4² ≤ 1·g₀²`, `v ≤ u`, `u < 1` at `Pf`, and proves `v < u` in its conclusion.
- Line numbers: probe lines cited in sections (b)-(d) and in the design refer to `fcdfdc0`, except where marked `76c586e`. At `76c586e`: 1-176 unchanged, 178 → 179, 181-324 → +2, 326-368 → +3, 370-383 → +4.
