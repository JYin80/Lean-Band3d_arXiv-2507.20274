Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 08:06:38 UTC 2026
Notation: Ψ=Ψ_t, η=η_t≍1−t, s=1−t, il=ilambda. size(Γ)=(L^d)^{nM}Ψ^{nS}W^{-d(nW−nV)} (def scaling, 7_8:232), ord=nS+2(nW−nV) (:270).
Scripts (python3+numpy, outside the repo): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad`; no Lean written.

### (i) Exponent table
| quantity | value (d=3 numbers; general d) | constraint | slack |
|---|---|---|---|
| size identity | size=(L^d)^{nM}Ψ^{ord}(W^dΨ²)^{nV−nW}; at Ψ=W^{-d/2}: (L^d)^{nM}W^{-d·ord/2} (d=3: W^{-1.5 ord}) | needs Ψ≥W^{-d/2} | rel.err ≤1.6e-16 (script 2) |
| ord of basic graphs | Ǧ_xx:1; ΣSǦ:1; ΣS⁺SǦǦ:2; unexpanded \|f_xy\|^p: p (nS=3p,nW=p,nV=2p) | after expansion need ord≥2p (lem:localregular(6)) | each of p paths must gain ≥+1 |
| Δord of expansion terms | (Owx) T1–T4: +1; (Oe1x): +1 except pull of G_{αy1}Ḡ_{αy'}: 0 (degree −2 at x, new degree-2 vertex); (Oe2x) R1–R8: +1 | ≥0 always; ratio Ψ^{Δord}, d=3,W=2: 0.3536 (script 2) | Δ=0 terms are structural, not smaller |
| molecule count (eq:MolVW, 7_8:797) | nV(M_i)≤nW(M_i)+1 | used in GtoAG (7_8:926) as W^{-d(nW−nV+q)}≤1 | fig-left: nW−nV+q=4−6+2=0, M1,M2: nV=3=nW+1: tight |
| fig-left graph (p=2,q=2) | nS=8,nW=4,nV=6,nM=2: ord=4=2p; ord_aux=6−2q=2; GtoAG factor Ψ^{4−2}=Ψ² (the 2 short edges G_{β1γ1},G_{β2γ2} inside molecules, 7_8:550) | ord≥2p | slack 0 (tight) |
| bound exponents (lem:Anp→LW_moment) | η^{-q}Ψ^{ord−p}Ψ_c^p ≤ η^{-p}Ψ^pΨ_c^p | q≤p, ord≥2p, η≤1, Ψ≤1 | η^{-(p−q)}Ψ^{ord−2p}; fig-left: 1 (tight) |
| Ψ_t window | W^{-d/2}≤Ψ_t≤W^{-ε0}; instance Ψ_t=(W^{-3}B_{t,0})^{1/2} | literal "Ψ_t=(W^{-d}B_{t,0})^{1/2}≥W^{-d/2}" iff B_{t,0}≥1 | FAILS literally at t=1/2,il=1,L=3: B=0.7407, √B=0.8607 (constant loss); instance t=1−W^{-2}: B≥1 (T2040a) |
| ε0 | 1/4 | Ψ_t²=W^{-3}B≤W^{-2ε0} i.e. B≤W^{2.5} | B=W²/27: slack W^{0.5}·27 |
| (eq:Psi) | C1=1, C2=(d−2)/2 (=1/2); Ψ_t(0)≍Ψ_t(ℓ), ℓ≤C | Ψ(l1)/Ψ(l2)≤C1(l2/l1)^{C2}, B=A/(r+1)^{d−2}+c | max ratio 1.000000 over l1≤l2<200 (tight) |
| ℓ_t, regimes | ℓ_t=min(max(il·s^{-1/2},1),L); =L iff s≤il²/L² (=1/9 at L=3) | LW_exp needs s>il²/L² | t=1/2: ℓ=1.4142, B_{t,0}=0.7407, B_{t,1}=0.4074; t=0.9: ℓ=L=3, B=1.2795 |
| 𝒯 vs sT (7_8:20-22) | W^{-d}T_t(r)/sT_t(r)²=B_{t,r}/first term ≤1+(L²+1)(L+1)^{d−2}/L^d for s≥il²/L², r≤L | ≍ with constant | d=3: 2.4815 (L=3), 2.1110 (10), 2.0010 (1000) |
| LW_exp windows | (log W)^{3/2}ℓ_t ≤ ℓ ≤ (log W)^{10}ℓ_t; T_t(r)≤W^{-D} beyond | e^{-(log W)^5}B≤W^{-D} iff (log W)^4≥D+d | W≥exp((D+3)^{1/4}), e.g. D=10: W≥6.7 |
| molecule radius | far condition \|a−b\|>(log W)^{3/2} (7_8:96), (scalemole) radius W(log W)^{3/2}, (yixi) radius W(log W)^{1+ε1}, ε1<1/10 (7_8:876) | 1+ε1<3/2 | ratio (log W)^{1/2−ε1}≥(log W)^{0.4} |
| expectation upgrade | \|f_xy\|≲Nη^{-3} (‖G‖≤η^{-1}, ΣS=N) | N^{-D'}(CNη^{-3})^p≤W^{-D} | any D' (η^{-1}≤N^C); instance η^{-3}=W^6, N=27W³ |
| Markov | p≥D/τ gives f≺X from E\|f\|^p≺X^p | p fixed per (D,τ) | none needed |
| S⁺=S(1−m²S)^{-1} | needs \|m\|<1; instance \|m\|²=0.9507 | Neumann series | 1−\|m\|²=0.0493; →0 as η→0 (S⁺~1/η, consistent with Θ) |
| regime (Main_DEL_COND, eq:WO) | W≥N^c, N=(WL)^d; W^{-d/2+fd}≤il≤fd^{-1} | instance c=1/4,fd=1/2,il=1 | W≥27 (c=1/4,L=3) |

### (ii) One concrete instance
Part A (d=3, W=2, L=3, il=1, N=216, z=0.3+0.05i, complex Hermitian H of (bandcw0)): p=2 graph value; Stein; (Owx), (Oe2x) with f=\|G_uv\|² resp. f=Ḡ_uv, x=0,u=(1,0,0),v=(0,1,0). The paper's identities are "=_E", so one H cannot satisfy them; the check is the exact per-sample identity LHS−RHS = −mΣ_w(δ_xw+m²S⁺_xw)Z_w (Z_w the Stein defect at row w; "exact4", rounding level) plus E[Z_w]=0 by an exact one-coordinate Gauss–Hermite Stein check ("exact5") and a 30000-sample Monte Carlo (SE≤1% of E\|LHS\|; the derivative terms are below the MC noise, so the MC is a mean-zero check only, not a test of the derivative terms; those are certified by exact2/exact5).
`cd $S && python3 t2040_pre.py 30000`
```
N=216 rowsum(S)=[1.000000000000000,1.000000000000000] |m^2+zm+1|=1.2e-16 m=-0.146208+0.964009j z=(0.3+0.05j)
exact1 resolvent id max|sum_a H_xa G_ax-1-zG_xx| = 3.9e-15 ; Ward max|sum_y|G_xy|^2-ImG_xx/eta| = 2.1e-13
exact2 d_{h_ax}|G_uv|^2 finite-diff -0.0297317221+0.0325670547j  closed form -0.0297317226+0.0325670527j |diff|=2.1e-09
exact3 ValG of (eq:p=2graph): #(al,be)-pairs=11984, 4-index sum 3.540933312540e-02 vs |f_xy|^2 3.540933312540e-02 rel.diff 1.6e-15
exact5 Stein in one coordinate, E[h F] = 2.492329130249e-03-8.636904245663e-04j  vs  S E[d_hbar F] = 2.492329130249e-03-8.636904245663e-04j  |diff|=3.7e-17
exact4 WE: Gc_xx f, f=|G_uv|^2                        |LHS-RHS-defect| = 1.1e-16   (|LHS|=5.92e-02 |LHS-RHS|=5.22e-02)
exact4 GG: G_xy G_y'x f, f=conj G_uv, x,y,y' distinct |LHS-RHS-defect| = 8.3e-17   (|LHS|=1.14e-02 |LHS-RHS|=1.05e-02)
exact4 GG: y=x                                        |LHS-RHS-defect| = 6.9e-17   (|LHS|=8.55e-02 |LHS-RHS|=4.31e-02)
MC samples=30000 (sample-level identity max residual over all samples: {'WE': '2.4e-15', 'GG': '2.1e-15'})
MC WE: Gc_xx f, f=|G_uv|^2                        mean(LHS-RHS)=+3.31e-05-2.57e-04j SE=3.4e-04 |mean|/SE=0.75  (E|LHS|=3.57e-02) | control, derivative terms with flipped sign: |mean|/SE=1.0
MC GG: G_xy G_y'x f, f=conj G_uv, x,y,y' distinct mean(LHS-RHS)=+1.57e-05-1.17e-04j SE=2.5e-04 |mean|/SE=0.47  (E|LHS|=2.80e-02) | control, derivative terms with flipped sign: |mean|/SE=0.5
MC GG: y=x                                        mean(LHS-RHS)=+2.54e-04-3.71e-05j SE=2.8e-04 |mean|/SE=0.91  (E|LHS|=9.36e-02) | control, derivative terms with flipped sign: |mean|/SE=0.9
```
`cd $S && python3 t2040_table.py` (graphs, expansion-term deltas read by hand from (Owx),(Oe1x),(Oe2x) with dM=0, parameter checks)
```
graph                          nS nW nV nM | ord size@Psi=W^-d/2 (=(L^d)^nM W^(-d ord/2)); identity size=(L^d)^nM Psi^ord (W^d Psi^2)^(nV-nW) rel.err
Gc_xx (light-weight, x ext)     1  0  0  0 |   1  3.5355e-01  0.0e+00
sum_a S_xa Gc_aa                1  1  1  0 |   1  3.5355e-01  0.0e+00
sum S+_xa S_ab Gc_aa Gc_bb      2  2  2  0 |   2  1.2500e-01  0.0e+00
|f_xy|^1 unexpanded (p=1)       3  1  2  1 |   1  9.5459e+00  0.0e+00
|f_xy|^2 unexpanded (p=2)       6  2  4  2 |   2  9.1125e+01  1.6e-16
fig. left graph G (p=2, q=2)    8  4  6  2 |   4  1.1391e+01  1.6e-16
aux graph of fig-left G: solid edges between molecules=6, q=2 -> ord_aux=6-2*2=2; ord(G)-ord_aux=2 (the 2 short edges); bound Psi^2*eta^-2*Psi_c^2*Psi^0
expansion terms: (dS,dW,dV,dM) read from (Owx),(Oe1x),(Oe2x); d_ord=dS+2(dW-dV); size ratio=Psi^dS W^{-d(dW-dV)} (L^d)^dM
  (dS,dW,dV,dM)=(1, 1, 1, 0)   d_ord=+1  ratio@(d=3,W=2,Psi=W^-3/2)=0.3536 = Psi^+1 W^(-d*0) (L^d)^0 : Owx-T1, Owx-T3, Oe1x-SGc, Oe1x-Gc^-xx-pull, Oe1x-(k1-1), Oe1x-k4, Oe1x-deriv, Oe2x-R3, Oe2x-R5, Oe2x-R7
  (dS,dW,dV,dM)=(1, 2, 2, 0)   d_ord=+1  ratio@(d=3,W=2,Psi=W^-3/2)=0.3536 = Psi^+1 W^(-d*0) (L^d)^0 : Owx-T2, Owx-T4, Oe2x-R4, Oe2x-R6, Oe2x-R8
  (dS,dW,dV,dM)=(-1, 0, -1, 0) d_ord=+1  ratio@(d=3,W=2,Psi=W^-3/2)=0.3536 = Psi^-1 W^(-d*1) (L^d)^0 : Oe1x-delta, Oe2x-R1
  (dS,dW,dV,dM)=(0, 1, 1, 0)   d_ord=+0  ratio@(d=3,W=2,Psi=W^-3/2)=1.0000 = Psi^+0 W^(-d*0) (L^d)^0 : Oe1x-pull(G,Gbar)
  (dS,dW,dV,dM)=(-1, 1, 0, 0)  d_ord=+1  ratio@(d=3,W=2,Psi=W^-3/2)=0.3536 = Psi^-1 W^(-d*1) (L^d)^0 : Oe2x-R2
t=0.5 1-t=0.50  il^2/L^2=0.1111 regime 1-t>il^2/L^2           ell_t=1.4142 B_{t,0}=0.7407 B_{t,1}=0.4074 B_{t,L}=0.2407 sqrt(B_{t,0})=0.8607 (Psi_t=(W^-d B)^(1/2) >= W^-d/2 iff B>=1)
t=0.9 1-t=0.10  il^2/L^2=0.1111 regime 1-t<=il^2/L^2 (ell=L)  ell_t=3.0000 B_{t,0}=1.2795 B_{t,1}=0.8249 B_{t,L}=0.5976 sqrt(B_{t,0})=1.1311 (Psi_t=(W^-d B)^(1/2) >= W^-d/2 iff B>=1)
(eq:Psi) max over 1<=l1<=l2<200 of Psi(l1)/Psi(l2)/(l2/l1)^((d-2)/2) = 1.000000 <= 1  (C1=1, C2=(d-2)/2=0.5)
L=   3, 1-t=il^2/L^2: max_{r<=L} W^-d T_t(r)/sT_t(r)^2 = 2.4815 <= 1+(L^2+1)(L+1)^(d-2)/L^d = 2.4815
L=  10, 1-t=il^2/L^2: max_{r<=L} W^-d T_t(r)/sT_t(r)^2 = 2.1110 <= 1+(L^2+1)(L+1)^(d-2)/L^d = 2.1110
L= 100, 1-t=il^2/L^2: max_{r<=L} W^-d T_t(r)/sT_t(r)^2 = 2.0101 <= 1+(L^2+1)(L+1)^(d-2)/L^d = 2.0101
L=1000, 1-t=il^2/L^2: max_{r<=L} W^-d T_t(r)/sT_t(r)^2 = 2.0010 <= 1+(L^2+1)(L+1)^(d-2)/L^d = 2.0010
```
Part B (sequence for pins lem:LWterm/lem:LW_moment: d=3, il=1, L=3 fixed, W→∞, t=1−W^{-2}, ℓ_t=L, ε0=1/4, c0=1, c=1/4, Ψ_t=(W^{-3}B_{t,0})^{1/2}, Ψ_t(r)=(W^{-c0}B_{t,r∧K})^{1/2}), and the 1−t>il²/L² regime (lem:LW_exp) at t=1/2. External hypothesis (eq:LW_assm): 𝓛^{(2)}≈W^{-d}Θ^{(+,−)}_{t,ab}, Θ=(1−tS^B)^{-1} (|m|=1 at the flow energy), needs W^{-d}Θ_ab≤W^{-c0}B_{t,|a−b|}: ratio W^{-(d−c0)}·(Θ/B) →0.
`cd $S && python3 t2040_inst.py`
```
hyp check: eq:WO  W^{-d/2+fd}<=il<=1/fd holds with fd=1/2 for W>=1 (il=1);  Main_DEL_COND W>=N^c, N=(WL)^3: c=1/4 needs W>=27
       W          N W>=N^c 1-t<=il^2/L^2   B_{t,0}       Psi_t    W^{-d/2}   W^{-eps0}      ok max Theta_ab/(C B) | LW_assm: W^-d Theta_ab <= Psi(|a-b|)^2 = W^-c0 B_{t,|a-b|}, worst ratio
      32  8.538e+05  True  True 3.804e+01   3.468e-02   5.623e-03   4.217e-01    True     1.007 | 1.01e-03   (row sum Theta = 1.0000e+03 vs 1/(1-t)=1.0000e+03)
     100  2.700e+07  True  True 3.714e+02   1.927e-02   1.000e-03   3.162e-01    True     1.001 | 1.00e-04   (row sum Theta = 1.0000e+04 vs 1/(1-t)=1.0000e+04)
    1000  2.700e+10  True  True 3.704e+04   6.086e-03   3.162e-05   1.778e-01    True     1.000 | 1.00e-06   (row sum Theta = 1.0000e+06 vs 1/(1-t)=1.0000e+06)
   10000  2.700e+13  True  True 3.704e+06   1.925e-03   1.000e-06   1.000e-01    True     1.000 | 1.00e-08   (row sum Theta = 1.0000e+08 vs 1/(1-t)=1.0000e+08)
 1000000  2.700e+19  True  True 3.704e+10   1.925e-04   1.000e-09   3.162e-02    True     1.000 | 1.00e-12   (row sum Theta = 9.9996e+11 vs 1/(1-t)=1.0000e+12)
t=1/2 regime: ell_t=1.4142 (<L), B_{t,0}=0.7407, Psi_t=max(W^-3/2,(W^-3B)^(1/2))/W^-3/2=1.0000; worst Theta_ab/B_{t,|a-b|}=1.516; (log W)^10*ell_t=3.499e+08 >= ell=ell_t
```
### Verdicts
- Target 1 (inventory), 2 (vocabulary), 4 (route/risk), 5 (skeleton), 6 (BA reuse), 7 (split/size), 8 (instances): PASS. No hypothesis set is empty or collapsed; all exponents close (rows above); the two tight rows (fig-left ord=2p, (eq:Psi) C1=1) are exact equalities, not violations.
- Target 3 (pins: lem:LWterm, lem: EWGn2_N, lem:LWterm_EXP, lem:LW_moment, lem:LW_moment_exp, lem:Anp, expansions as value identities): PASS, with two pinning constraints. (1) Ψ_t must be pinned as Ψ_t=max(W^{-d/2},(W^{-d}B_{t,0})^{1/2}) or with a constant: the literal choice violates W^{-d/2}≤Ψ_t at t=1/2,il=1,L=3 (paper-delta candidate T2040a; harmless under ≺). (2) The expansions hold only "=_E": pin them as value identities up to the explicit Stein defect −mΣ_w(δ_xw+m²S⁺_xw)Z_w with E Z_w=0 (merged MD-2 Stein), verified exactly above for (Owx),(Oe2x); (Oe1x) was not numerically checked (T2040b: needs its own check in stage 1b).
- Instance uses L=3 (odd); the paper defines Z_L^d for even L and says odd L "can be treated similarly" (1_2:269): observation, T2040c.
## (a′) Preflight corrections — Sat Oct  3 10:07:37 UTC 2026
No correction changes a verdict; (a) is untouched. (1) T2040b ((Oe1x) unchecked in (a)) is closed by b.7. (2) (eq:Psi) in (a)(i) has C1=1, C2=1/2; the paper needs C1, C2>1 (3_5:390): larger
pairs hold, the probe uses (2,2). (3) (a)(ii) tests G(z) (row sums 1); the pins are the flow versions (S_t=tS, z_t=E+(1-t)m): `owx_defect_identity` holds for row sum s, b.7 checks all three.
## (b) Script output and design — probe `RBM3D/Probe/T2040Graphs.lean` on branch `t/T2040` (commit 9325727); inventory, scripts: `docs/reports/T2040-inventory.md`
**Size headline (item 7, b.9): gate LW = 27 tickets of ~1000 lines (21-39); with the block Anderson additions 33 (27-48). No estimate exceeds 50 (DECISIONS §9 O2): no first-line flag; both
central values lie in 25-40.**
### b.1 Build and hygiene
    $ date -u; cd $WT && git log -1 --format="%h %an <%ae>"; git diff --name-only $(git merge-base HEAD main) HEAD
    Sat Oct  3 10:07:37 UTC 2026
    9325727 Jun Yin <321276894+JYin80@users.noreply.github.com>
    RBM3D/Probe/T2040Graphs.lean
    $ lake build RBM3D.Probe.T2040Graphs 2>&1 | tail -1; time lake env lean RBM3D/Probe/T2040Graphs.lean; echo exit=$?
    Build completed successfully (3318 jobs).
    lake env lean RBM3D/Probe/T2040Graphs.lean  20.52s user 2.64s system 203% cpu 11.375 total
    exit=0
    $ lake build RBM3D 2>&1 | tail -1   # the library at the branch base (the probe is not imported); module axioms; forbidden tokens
    Build completed successfully (3741 jobs).
    declarations of the probe module (not internal): 335; theorems: 116; only the three standard axioms: 335; others: 0
    forbidden tokens: 0; lines:     2141
    $ lake env lean $S/t2040/ax_main.lean   # four targets; all 55 theorems and instances: inventory block 19
    'RBM.Gauss.Sizes.lwterm_of_moment' : [propext, Classical.choice, Quot.sound]
    'RBM.Graph.owx_defect_identity' : [propext, Classical.choice, Quot.sound]
### b.2 Inventory of 7_8:1-1791 and B:1-525 (item 1; all 38 statements with spans, citations and proof location, 86 equations, dependency tree, sketch markers: inventory blocks 1-7)
    $ cd $S && python3 t2040_inv.py classes | cut -c1-400   # statements by class (where the proof is), label (file:span)
    proved:B [2]: lem:LWterm_EXP (6:83-88); lem:localregular (7_8:786-821)
    proved:7_8 [9]: lem:LWterm (3_5:385-404); lem: EWGn2_N (3_5:406-415); lem:LW_moment (7_8:72-77); lem:LW_moment_exp (7_8:78-83); GtoAG (7_8:907-912); lem:Anp (7_8:933-939); lem:Anp_key_gh (7_8:1041-1077); lem:LW_moment_exp_far (7_8:1615-1620); lem:LW_moment_exp_near (7_8:1621-1626)
    def [13]: def_graph1 (7_8:116-147); ValG (7_8:159-164); def_poly (7_8:171-188); defnlvl0 (7_8:196-210); dot-def (7_8:214-225); def scaling (7_8:232-255); def scaling order (7_8:270-284); deflvl1 (7_8:367-386); def: BM2 (7_8:863-869); def_auxgraph (7_8:894-903); def_atom (B:302-314); defn_normalBA (B:329-339); def scalingBA (B:345-356)
    no-proof [3]: claim:size (Gamma << size(Gamma), 7_8:264) (7_8:264-266); claim:xi (eq:Gbyxi2 bounds of xi, 7_8:884) (7_8:884-890); lem:Anp_key (7_8:960-985)
    cited:yang2021delocalization [4]: ssl (7_8:294-306); Oe14 (7_8:309-330); T eq0 (7_8:334-349); lvl1 lemma (7_8:392-399)
    example [1]: example:p=2 (sec:graphs_ideas, 7_8:505) (7_8:505-679)
    proved:A [1]: claim:TTk (7_8:1661-1666)
    strategy [1]: strat_local (B:135-157)
    remark [1]: remark:3p (stronger ord bound, B:280) (B:280-282)
    cited:yang2024Del [3]: lanlw (B:359-372); lem_lweight (B:376-387); GGGamma (BA GG expansion, B:393) (B:393-405)
    $ python3 t2040_inv.py layers | paste -d"|" - - | cut -c1-330   # dependency graph from lem:LWterm, lem: EWGn2_N, lem:LWterm_EXP (longest path), two layers per line
    L0: lem:LWterm_EXP; lem:LWterm|L1: GGGamma (BA GG expansion, B:393); lem:LW_moment_exp
    L2: lem:LW_moment_exp_near; lem:LW_moment_exp_far; lem: EWGn2_N|L3: claim:TTk; lem:LW_moment
    L4: lem:Anp|L5: lem:Anp_key_gh; claim:xi (eq:Gbyxi2 bounds of xi, 7_8:884); GtoAG
    L6: def_graph1; lem:Anp_key; lem:localregular|L7: def_auxgraph; strat_local; lvl1 lemma
    L8: ValG; deflvl1; dot-def; def scaling order; T eq0; Oe14; ssl|L9: def scaling
### b.3 Vocabulary (item 2)
    $ python3 t2040_compare.py $PROBE   # code lines from t2040_stats.py: docstrings, comments, blank lines excluded
    | criterion | A: record `LGraph E I` (probe §1, §3, §4) | B: binder terms `GTerm V` (§2, §4.3) |
    | core vocabulary, code lines | 65 (LData, edges, value, counters, molecules) | 26 (terms, eval; no counters, no molecules) |
    | (Owx) on `Ǧ_xx`: three terms + value theorem, code lines | 30 (incl. the `ord` theorem; unfolds `Fin n → ι` sums) | 19 (structural `eval`; same `owx_defect_identity`) |
    | counters, molecules, ord; expansion at x | from the record by `decide`: p2Graph (6,2,4,2), ord 2; figGraph (8,4,6,2), ord 4; filter `solid` by endpoint | not visible: a flattening to a record is needed; the factors at x sit in a product tree under `Option` shifts |
    | lem:Anp nested bound | `NGraph p q` (edges, p paths), `IsNested` decided on `figAux`; pin `LWAnpKey` | paths are no property of the term: the record is needed again |
Reused (compiled): `Counters`, `ord`. Named, not applied: `hasDerivAt_inverse_apply` (the law `dH` implements), `Case`/`classify` (arithmetic and exhaustiveness of cases (i)-(vi); their
counter relations on a record: LW-10). Choice: A. B has the shorter value proofs, but the statements of §7 and App. B (molecules, ord, paths, nested bound) are about the edge multiset, which
only A exposes; B can be a printing syntax over A. Both graphs: values unfolded by `simp` (`p2Graph_val`, `p2Graph_val_eq`: = |f_xy|², `figGraph_val`).
### b.4 Pins (item 3): one line per pin, extracted from the probe by script
    $ python3 t2040_pins.py $PROBE 430
    | pin | probe lines | paper | binders and hypotheses (<FLOW> = 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →) | conclusion (the scale of every `Prec` is N = sz.size n) |
    | `LWterm` | 949-958 | 3_5:385-404 (eq:LW_conclusion) | <FLOW> ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ), LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc → | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) |
    | `LWtermB` | 964-979 | 3_5:393-397 (eq:LW_conclusion2) | <FLOW> ∀ (ε₀ c₀ C₃ : ℝ) (K : ℕ → ℕ) (Ψ : ℕ → ℝ), 0 < c₀ → (∀ n, K n ≤ sz.L n) → 0 < ε₀ → LWWindow sz ε₀ Ψ → LWInit sz (STflowE z) t ε₀ Ψ → LWClass sz ε₀ C₃ (fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)) → LWLoop2 sz (STflowE z) t (fun n  ... | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0) ^ (1 / 2 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) (min (zdistInf d (sz.L n) (p.2 0 - p.2 1)) (K n)))) |
    | `LWtermExp` | 999-1009 | 3_5:406-415 (eq:LW_conclusion_exp) | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) |
    | `LWtermExpS` | 1406-1417 | regime 1-t > g^2/L^2 of 3_5:406 | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) |
    | `LWtermExpN` | 1421-1432 | regime 1-t <= g^2/L^2 of 3_5:406 (7_8:20) | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // 1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2}) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) |
    | `LWtermEXP` | 1020-1029 | 6:83-88 (eq:ExpLWn=2) | <FLOW> STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t → STLK sz (STflowE z) t → STDecay sz (STflowE z) t → | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n}) (fun n p _ => ‖∫ ω, LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω ∂(sz.seqP)‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) |
    | `LWMoment` | 1034-1045 | 7_8:72-77 (eq:LW_moment) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ), LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C ... | Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖ ^ p ∂(sz.seqP)) (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p) |
    | `LWMomentExp` | 1050-1063 | 7_8:78-83 (eq:LW_moment_exp) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → | Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP)) (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p  ... |
    | `LWAnpKey` | 1084-1097 | 7_8:960-985 (adsuu_orig) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ Φ : ℕ → ℝ →  ... | Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n))) (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q * Φ n 0 ^ (Γ.ordN - p) * ∏ i, Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ))) |
    | `LWAnpKeyGh` | 1101-1115 | 7_8:1041-1077 (adsuu22) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.GhostOK → Γ.IsNested → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ Φ : ℕ → ℝ →  ... | Prec sz (U := fun n => (Fin p → Zd d (sz.L n)) × (Fin p → Zd d (sz.L n))) (fun n ab ω => Γ.val (fun α β => ξ n α β ω) ab.1 ab.2) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q * Φ n 0 ^ (Γ.ordN - Γ.nngh) * ∏ i, (if Γ.noGhostPath i = true then Φ n (c * ((zdistInf d (sz.L n) (ab.1 i - ab.2 i) : ℕ) : ℝ)) else 1)) |
    | `LWAnp` | 1121-1134 | 7_8:933-939 (eq:bddGamma_aux) | 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p q : ℕ), q ≤ p → ∀ Γ : RBM.Graph.NGraph p q, Γ.NoGhost → Γ.IsNested → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ Φ : ℕ → ℝ →  ... | Prec sz (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n ab ω => Γ.val (fun α β => ξ n α β ω) (fun _ => ab.1) (fun _ => ab.2)) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ ^ q * Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (Γ.ordN - p)) |
    | `LWReduceB` | 1140-1153 | 7_8:20-91 reduction (eq:directG1..recoltermwt) | <FLOW> ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ), LWAssm sz (STflowE z) t ε₀ Ψ Φ C₁ C₂ C₃ Cc → Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1 q.2‖) (fun n q _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n ... | Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1 p.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) |
    | `LWReduceT` | 1437-1455 | 7_8:20-58 reduction (eq:directG2..recoltermwt2) | <FLOW> ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D → Prec sz (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n q ω => ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖) (fun n q _ => (etaT (S ... | Prec sz (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) (fun n p ω => ‖LWE sz n (STflowE z n) (t n) p.1.1 p.1.2 ω‖) (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) |
    | `LWweightExp` | 789-799 | 7_8:294-306 (Owx) | ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x : Idx d L W), | ∫ ω, lwGc d L W E t ω x x * lwf d L W E t P ω ∂(PF d L W g) = ∫ ω, (mE E * ∑ α, lwS d L W g t x α * lwGc d L W E t ω x x * lwGc d L W E t ω α α * lwf d L W E t P ω + mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β * lwGc d L W E t ω α α * lwGc d L W E t ω β β * lwf d L W E t P ω - mE E * ∑ α, lwS d L W g t x α * lwG d L W E t ω α x * lwdf d L W E t P ω α x - mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g ... |
    | `LWedgeExp` | 814-843 | 7_8:309-330 (Oe1x) | ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ (k₁ k₂ k₃ k₄ : ℕ) (x : Idx d L W) (y : Fin (k₁ + 1) → Idx d L W) (y' : Fin k₂ → Idx d L W) (w : Fin k₃ → Idx d L W) (w' : Fin k₄ → Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ), | ∫ ω, lwG d L W E t ω x (y 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) ∂(PF d L W g) = ∫ ω, (mE E * (if x = y 0 then 1 else 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω) + mE E * (∑ α, lwS d L W g t x α * lwGc d L W E t ω α α) * (lwG d L W E t ω x (y 0) * (oe1xRest d L W E t ω x y y' w w' Finset.univ Finset.univ * lwf d L W E t P ω)) + ∑ i : Fin k₂, ( ... |
    | `LWggExp` | 847-864 | 7_8:334-349 (Oe2x) | ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g E t : ℝ, |E| < 2 → 0 ≤ t → t < 1 → ∀ (x y y' : Idx d L W) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ), | ∫ ω, lwG d L W E t ω x y * lwG d L W E t ω y' x * lwf d L W E t P ω ∂(PF d L W g) = ∫ ω, (mE E * (if x = y then 1 else 0) * lwG d L W E t ω y' x * lwf d L W E t P ω + mE E ^ 3 * lwSp d L W E g t x y * lwG d L W E t ω y' y * lwf d L W E t P ω + mE E * (∑ α, lwS d L W g t x α * lwGc d L W E t ω α α) * (lwG d L W E t ω x y * lwG d L W E t ω y' x * lwf d L W E t P ω) + mE E ^ 3 * ∑ α, ∑ β, lwSp d L W E g t x α * lwS d L W g t α β  ... |
Conventions: constants (κ ε 𝔡, p, ε₀ C₁ C₂ C₃ Cc, the graph) precede the sequence, `∃ c` follows them and precedes (𝔠, sz, z, t); every `≺` is `Prec` at N=`sz.size n`; |a-b| is `zdistInf`;
regime index sets are subtypes; the expansions are identities of expectations over `PF` at fixed (L,W) with S=tS, S⁺=S(1-m²S)⁻¹, z_t.
### b.5 Skeleton and the proved expansion (item 5)
    $ python3 t2040_extract.py $PROBE lwterm_of_moment lwtermexpS_of_momentexp lwtermexp_of_regimes lwanp_of_key owx_smallest | grep -v "^-- probe" | cut -c1-190
    theorem lwterm_of_moment (hMom : LWMoment d) (hRed : LWReduceB d) (hint : LWInteg d) :
        LWterm d := ...
    theorem lwtermexpS_of_momentexp (hMom : LWMomentExp d) (hRed : LWReduceT d) (hint : LWInteg d) :
        LWtermExpS d := ...
    theorem lwtermexp_of_regimes (hS : LWtermExpS d) (hN : LWtermExpN d) : LWtermExp d := ...
    theorem lwanp_of_key (h : LWAnpKey d) : LWAnp d := ...
    theorem owx_smallest (D : LData ι) (m z s : ℂ) (hm0 : m ≠ 0) (hzm : z + s * m = -m⁻¹)
        (hM : ∀ i j, D.M i j = if i = j then m else 0) (hS : ∀ i, ∑ j, D.S i j = s)
        (hSp : ∀ i j, D.Sp i j - m ^ 2 * ∑ w, D.Sp i w * D.S w j = D.S i j) (x : ι) :
        owxG0.val D (fun _ => x) - ((owxG1 m).val D (fun _ => x) + (owxG2 m).val D (fun _ => x)) =
          -m * ∑ w, ((if x = w then 1 else 0) + m ^ 2 * D.Sp x w) *
            owxDefect z D.G D.S 1 (fun _ _ => 0) w := ...
Proved: LWterm from LW_moment + `LWReduceB` (merged Markov bridge; `stochDomAt_det`, `LWPsiAll.shift` new); EWGn2_N from the strict regime + `LWtermExpN` (`stochDomAt_of_split`); Anp from
Anp_key; (Owx) with the Stein defect: Ǧ_xx (`owx_smallest`), Ǧ_xx G_xy (`owx_second`), in expectation. Left: `LWMoment(Exp)`, `LWReduceB/T`, `LWtermExpN`, `LWInteg`, E Z_w=0.
### b.6 Route and risk (item 4): `t2040_route.py` (lines = size model, b.9; markers = inventory block 5)
    $ python3 t2040_route.py
    | lem:LWterm, lem: EWGn2_N (3_5:385-415; 7_8:1-104) | Markov on LW_moment(_exp) [compiled: lwterm_of_moment, lwtermexpS_of_momentexp]; reduction by (eq:directG1/2), (eq:recolterm*), (eq:recoltermwt*) from merged lem_GbEXP pins and (LW_assm); regimes | all routine (union bound, Markov, (eq:Psi) shift compiled); deterministic T~ vs [sT]^2 comparison | LW-01 1278+LW-15 600+LW-16 500 | low-medium | 7_8:20 "an immediate consequence" (regime 1-t <= g^2/L^2: sub-sequence transfer, T2040k) |
    | lem:LW_moment, lem:LW_moment_exp, assembly (7_8:716-720, 943-950, 1600-1630) | dist(a,b) <= (log W)^{3/2} (_exp: <= (log W)^{3/2} l_t, from LW_moment) by the max-bound (eq:boundfxyGinf) [Ward + Cauchy-Schwarz]; else expand E‖f‖^p to graphs, lvl1, GtoAG, lem:Anp; _exp: cut f = f^{>l} + f^{<=l}; expectation upgrade ‖f‖ <~ N eta^-3 | routine: far/near, upgrade, Markov | LW-02 461 | medium | 7_8:944 "standard" |
    | ssl, Oe14, T eq0: (Owx),(Oe1x),(Oe2x) (7_8:294-349; cited yang2021 Lemmas 3.5, 3.10, 3.14: no proof in the paper) | row Stein identity + resummation S+ = S(1-m^2 S)^-1 [(Owx) proved pathwise: owx_defect_identity; (Oe1x),(Oe2x) checked numerically b.7]; E Z_w = 0 (merged GaussIBP, owed S1-19); derivative of resolvent polynomials (merged hasDerivAt_inverse_apply); each term a graph with counter changes ((a)(i)) | routine algebra; size of the statements (nine and eight terms, k1..k4 generic) | LW-04 1200+LW-05 800+LW-06 1100+LW-07 1000 | medium | whole proofs cited |
    | lvl1 lemma, strat_local, deflvl1 (7_8:367-399; B:135-157) | iterate (Owx), (Oe1x), (Oe2x) with the dot-def normal form until locally standard; discard graphs of size <= W^-D (claim:size) | graph-combinatorial: termination (ord, size), normal-graph normal form | LW-08 1500+LW-03 1400+LW-09 1300 | high | strategy only (B:135-157); claim:size 7_8:264 has no proof; lvl1 cited (Lemma 3.22) |
    | lem:localregular (7_8:786-821; proof B:172-278) | (1) trivial, (2) the number of internal molecules never increases (B:173-177); (3)-(5): paths persist through every expansion (B:178-199, three alternatives); (6) ord >= 3p - n_dv: weight cases (i)-(vi) B:209-263 [arithmetic merged: Graph/ScalingOrder, Graph/Model], edge and GG expansions B:275 | merged: the arithmetic of (i)-(vi); to do: Case.Rel on records, edge/GG case analysis | LW-10 2918 (-393 merged) | high | B:263 "not hard to see"; B:275 "straightforward", "direct check", "omit the details" |
    | GtoAG, def_auxgraph, def: BM2 (7_8:863-932) | block-level auxiliary graph of a locally standard graph; ord(G) - ord(G_aux) >= 0 via (eq:MolVW) (nV(M_i) <= nW(M_i)+1) | graph-combinatorial (molecules, paths) | LW-11 989 | medium | 7_8:915 "as in"; claim:xi 7_8:884 has no proof |
    | lem:Anp_key_gh, lem:Anp_key, lem:Anp (7_8:933-1599) | Anp from Anp_key [compiled: lwanp_of_key]; Anp_key = gh version (7_8:1025 "easy corollary"); gh by induction on internal vertices, ending-edge types A1/A2/B1/B2, cases (I)-(IV), Cauchy-Schwarz with (eq:Gbyxi3), change of summation order | Cauchy-Schwarz sums, order bookkeeping; graph-combinatorial: nested graphs, spanning paths | LW-12 7312 | high (largest item) | 7_8:1142, 1231 "easy to see"; 1154-1413 "without loss of generality"; 1232-1254 "similar"; 1400, 1529 "as in" |
    | lem:LW_moment_exp_far, _near (7_8:1615-1791) | far (f^{>l}, internal vertices in D_{>l}): every path has an ending edge longer than l, T(l) as an A2/ghost edge, rest "exactly the same argument" as Anp_key_gh; near (f^{<=l}): edges bounded by T_t(.^l), internal sums in a fixed order with the key estimate from claim:TTk (merged EKTTk), lem:propT | graph-combinatorial (reuse of LW-12); sums with the exponential tail | LW-13 2511 | high-medium | 7_8:1632, 1647 "similar", "standard"; 1642, 1773 "omit"; 1781 "easy to see" |
    | lem:LWterm_EXP (B:7-121; 6:83-88) | GG expansion at G_xa G_ay: I1..I4 (J1..J4 "exactly the same" with prop:ThfadC_short); I42 = 5-loop -> graphs G_xy, GtoAG, ord >= 4.1_{x=y}+5.1_{x!=y} from (eq:GGraisesord), cases (1)-(4) | Ward, averaged local law, K-loop bounds (merged); ord of every term of (Oe2x) | LW-14 2524 | medium-high | B:34, 49, 105 "exactly the same"; B:102 "easy to see"; B:118 "omit" (BA part) |
    | block Anderson graph layer (B:286-523) | Psi-dotted and M-dotted edges, atoms, scalingBA; lanlw, lem_lweight, GGGamma (cited yang2024Del B.9-B.11); BA lvl1; atomic reduction + auxiliary graph; LWterm_EXP with GGGamma | graph-combinatorial; same shape as LW-03..LW-14 | BA-L1 873+BA-L2 2400+BA-L3 1590+BA-L4 1500 | high | B:409 sketch; B:118 "omit"; "carries over verbatim" |
### b.7 Extreme inputs (t → 1, L large; each pin tried at one)
    $ python3 t2040_expansions_summary.py   # (Owx),(Oe1x),(Oe2x), pathwise identity with the Stein defect, generic f; full output: inventory block 10
    setting (seed E t h)               | |LHS| range              | |LHS-RHS| range          | max resid. | max relative resid.
    7 0.7 0.55 1e-5                    | 6.2e-05 .. 8.2e-02        | 4.4e-05 .. 1.1e-01        | 2.4e-13    | 6.6e-11
    13 0.0 0.001 1e-5                  | 3.1e-07 .. 5.5e-02        | 3.1e-07 .. 5.5e-02        | 1.2e-16    | 4.8e-14
    17 -1.2 0.9 1e-5                   | 2.8e-07 .. 3.3e-02        | 2.7e-07 .. 2.6e-02        | 6.2e-14    | 4.3e-11
    11 1.9 0.999 1e-7                  | 1.6e+03 .. 1.3e+10        | 5.4e+04 .. 1.1e+12        | 2.6e+02    | 2.1e-08
    $ ./t2040_endflow_short.sh   # t = t0 = lemT z_n, n = 0, 5, 500 (L_n = 4, 24, 2004)
      n           N        1-t0     lam^2/L^2     lam^2/L^3 | strict regime 1-t0 > lam^2/L^2     1-t0 >= lam^2/L^3 (LWterm_EXP index set)
      0   2.097e+06  9.0512e-06    1.5259e-05    3.8147e-06 | False                              True
      5   2.130e+20  5.6407e-17    1.9472e-16    8.1132e-18 | False                              True
    500   8.293e+54  1.1996e-44    2.4310e-43    1.2131e-46 | False                              True
    t = 1/16 (tInst): the strict regime lam^2/L^2 < 15/16 holds for every n (lam <= 1/64; Lean: strict_all).
t → 1: at t=0.999 the identities hold to 2.1e-8 relative (h=1e-7). At t=t₀ the deterministic hypotheses of LWterm, LWtermExp, LWMoment, LWAnpKey, LWtermEXP are discharged by the same data
(`inst_*_endT`); the strict regime of LW_moment_exp is empty at the listed n (its instance sits at t=1/16, `strict_all`), so EWGn2_N at t₀ rests on the other regime `LWtermExpN` (T2040k). L
large: L_500=2004; the (a) ratio W^-d T/(sT)² falls from 2.4815 (L=3) to 2.0010 (L=1000).
### b.8 Block Anderson reuse (item 6)
lem:LWterm, lem: EWGn2_N stay valid for BA (7_8:1994). Outside LW, gate BA changes the model (H=V+λΨ, M not scalar: `zztE_BA`, `lem:propM`, `lem_GbEXP_BA`), Step 2 (`eq:MG_conclusion3_BA`)
and the Step 5/6 inputs. In the graph layer (B:286-523) it adds Ψ- and M-dotted edges, atoms with `ord=nS+2(nW-nA)` (the merged `ord` serves both), the expansions `lanlw`, `lem_lweight`,
`GGGamma` (cited, yang2024Del B.9-B.11: proved internally, DECISIONS §5), BA lvl1, the atomic reduction with ζ (`eq:Gbyxi2_BA`), `lem:LWterm_EXP` with GGGamma (B:118, omitted). Reused:
`LData` (M is already a general matrix), Anp* (B:497 "carries over verbatim"), (eq:Psi) lemmas, the regime lemma, the skeleton. Cost: 6.4 tickets (b.9).
### b.9 Split table and size (item 7): `t2040_split.py`; size model `t2040_size.py` = inventory span chars × 151 lines/kchar (measured on merged proofs) × omitted-step multiplier (inventory block 8)
    $ python3 t2040_split.py
    credit: merged Graph/ScalingOrder.lean + Graph/Model.lean = 393 lines (arithmetic and exhaustiveness of the cases (i)-(vi), B:209-263) subtracted from LW-10
    | LW-03 | Vocab | def_graph1 ValG def_poly defnlvl0 dot-def (def scaling, order); records, value, counters, molecules | MD-1..3, merged Counters/ord | prover-hard | 1400/1400/1400 | 1.4 |
    | LW-04 | SteinBridge | E Z_w = 0 for resolvent polynomials; derivative calculus; graph derivative | S1-19 GaussIBP (T2031) | prover-hard | 1200/1200/1200 | 1.2 |
    | LW-05 | ExpOwx | ssl (Owx) as a graph operation, counters per term | LW-03, 04 | prover | 800/800/800 | 0.8 |
    | LW-06 | ExpOe1x | Oe14 (Oe1x), nine terms, k1..k4 generic | LW-03, 04 | prover-hard | 1100/1100/1100 | 1.1 |
    | LW-07 | ExpOe2x | T eq0 (Oe2x), eight terms | LW-03, 04 | prover | 1000/1000/1000 | 1.0 |
    | LW-09 | SizeClaim | claim:size (Gamma << size), S^pm decay (estSpm-W), scalemole | LW-03 | prover-hard | 1300/1300/1300 | 1.3 |
    | LW-08 | Lvl1 | deflvl1, strat_local, lvl1 lemma (termination, Err <= W^-D) | LW-03, 05-07, 09 | prover-max | 1500/1500/1500 | 1.5 |
    | LW-10 | LocalRegular | lem:localregular (1)-(6): paths, molecules, ord through (Owx),(Oe1x),(Oe2x) | LW-03, 05-08 | prover-max | 1552/2525/4470 | 2.5 |
    | LW-11 | AuxGraph | def: BM2, def_auxgraph, GtoAG | LW-10 | prover-hard | 989/989/1979 | 1.0 |
    | LW-12 | Nested, AnpKeyGh, Anp | lem:Anp_key_gh (cases I-IV), lem:Anp_key, lem:Anp (NGraph) | LW-11 | prover-max | 4875/7312/12187 | 7.3 |
    | LW-13 | MomentExp | lem:LW_moment_exp_far, _near (uses merged EKTTk) | LW-12 | prover-max | 1255/2511/3766 | 2.5 |
    | LW-14 | LWtermEXP | lem:LWterm_EXP (B:7-121): I1..I4, J-terms, (eq:GGraisesord), cases (1)-(4) | LW-03, 07, 09, 11 | prover-max | 1683/2524/4207 | 2.5 |
    | LW-15 | LWDet | (eq:Psi) for the B class, W^-d T~ ~ [sT]^2, Psi_t window (T2040a) | merged Defs/Tail | prover | 600/600/600 | 0.6 |
    | LW-02 | LWMoment | lem:LW_moment, lem:LW_moment_exp (far/near split, expectation upgrade) | LW-08, 10-13 | prover-hard | 461/461/922 | 0.5 |
    | LW-16 | LWRegime | regime transfer of lem: EWGn2_N (T2040k) | LW-01 | prover-hard | 500/500/500 | 0.5 |
    | LW-01 | LWterm | lem:LWterm, lem: EWGn2_N from the moments (reduction (eq:directG), recolterm) | LW-02, 15, 16, ST-D2 | prover-hard | 1278/1278/2557 | 1.3 |
    | total | | | | | 21495/27002/39490 | 27.0 |
    tickets of ~1000 lines: lo 21, central 27, hi 39; band 600-1500 lines per ticket: central 18..45
    block Anderson additions (BA-L1..L4: Psi- and M-dotted edges, atoms, scalingBA; lanlw, lem_lweight, GGGamma; BA lvl1/Anp; BA LWterm_EXP): 6.4 tickets (lo 5.8, hi 8.3)
    LW + BA: central 33 tickets (lo 27, hi 48); DECISIONS 9 O2 thresholds 25/40/50: exceeds 50: no (neither central, lo nor hi)
    reduced route R1 (expansions ssl, Oe14, T eq0 and lvl1 lemma = Lemmas 3.5, 3.10, 3.14, 3.22 of yang2021 as external inputs; needs a change of DECISIONS 5): 21 tickets (lo 16, hi 34); gives up LW-04..08
    reduced route R2 (Step 6 only: LW-03,04,07,09,11,14,15): 9 tickets (lo 8, hi 12); gives up lem:LWterm and lem: EWGn2_N (Step 2), which the main theorems need: not a route by itself
No reduced route within DECISIONS §5 was found: Steps 2 and 6 consume lem:LWterm, lem: EWGn2_N, lem:LWterm_EXP with sharp exponents (the figure graph has ord = 2p exactly), so R2 is not a
route; R1 needs Jun to authorize Lemmas 3.5, 3.10, 3.14, 3.22 of yang2021.
### b.10 Compiled nonempty instances at d = 3 (item 8) — repaired at commit eeda441 (audit round 1 items 1–3), `date -u`: Sat Oct  3 10:19:12 UTC 2026
    $ grep -ho "^\(theorem\|def\) inst_[A-Za-z_0-9]*" $PROBE | sed "s/^[a-z]* //" | sort | tr "\n" " "
    inst_Anp inst_AnpKey inst_AnpKey_endT inst_AnpKeyGh inst_chain_Anp inst_chain_LWterm inst_chain_LWtermExp inst_edge inst_figGraph_val inst_gg inst_LWMoment inst_LWMoment_endT inst_LWMomentExp inst_LWterm inst_LWterm_endT inst_LWtermB inst_LWtermExp inst_LWtermEXP inst_LWtermExp_endT inst_LWtermEXP_endT inst_LWtermExpN inst_LWtermExpS inst_owx_second inst_owx_smallest inst_owx_smallest_E inst_owx_smallest_E_unit inst_p2Graph_val_eq inst_shift inst_ssl 
    $ python3 t2040_extract.py $PROBE inst_LWterm inst_owx_smallest | grep -v "^-- probe" | cut -c1-170
    theorem inst_LWterm (h : LWterm 3) (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0)
        (hL : LWLoop2 sz0 (STflowE z0) tInst Φ0) :
        Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖LWE sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
          (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Φ0 n 0 *
            Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) := ...
    theorem inst_owx_smallest (x : Fin 2) :
        owxG0.val D0 (fun _ => x) - ((owxG1 I).val D0 (fun _ => x) + (owxG2 I).val D0 (fun _ => x)) =
          -I * ∑ w, ((if x = w then 1 else 0) + I ^ 2 * D0.Sp x w) *
            owxDefect 0 D0.G D0.S 1 (fun _ _ => 0) w := ...
    $ grep -n "^def ℓT\|ℓ0" $PROBE; grep -c "ℓT tInst\|ℓT tEnd" $PROBE     # window of the lem: EWGn2_N family (1 ≤ ℓT t n: ℓT_one_le)
    1645:def ℓT (t : ℕ → ℝ) : ℕ → ℝ := fun n => ellT (sz0.L n) (sz0.lam n) (t n)
    19
    $ lake build RBM3D.Probe.T2040Graphs 2>&1 | tail -1; lake env lean ax.lean | sed 's/.*depends on axioms: //' | sort | uniq -c
    Build completed successfully (3318 jobs).          # ax.lean: #print axioms of ℓT_one_le ℓT_window assmExpT_of assmExp_of inst_LWtermExp
      10 [propext, Classical.choice, Quot.sound]       #   inst_LWMomentExp inst_LWtermExpS inst_LWtermExp_endT inst_chain_LWtermExp inst_LWtermExpN
    $ awk '/^theorem inst_LWtermExpN/,/D hD$/' $PROBE | sed -n '1,4p;9,10p'
    theorem inst_LWtermExpN (h : LWtermExpN 3) (hI : LWInit sz0 (STflowE z0) tEnd (1 / 20) Ψ0)
        (hL : LWLoopExp sz0 (STflowE z0) tEnd (ℓT tEnd)) (D : ℝ) (hD : 0 < D) :
        Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
            1 - tEnd n ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2})
      h le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
        tEnd tEnd_range.1 tEnd_range.2 (1 / 20) Ψ0 (ℓT tEnd) (assmExpT_of tEnd hI hL) D hD
Data: merged `sz0, z0, flow_z0` (d=3, L_n=4(n+1), W_n=(2(n+1))^5, λ_n=(2(n+1))^-6, κ=ε=𝔡=1/10, 𝔠=1/6), t=1/16 and t=t₀, window ℓ_n=ℓT t n=ellT(L_n,λ_n,t_n) ∈ [1, (log W_n)^10 ℓ_t] (`ℓT_one_le`, `ℓT_window`) in the five lem: EWGn2_N-family instances and `inst_LWtermExpN` (t=t₀; its index set is the regime b.7 shows holds at t₀ for n=0,5,500), `Ψ≡W^-1` or the B-class (c₀=1, K≡1, `classB`); graph pins on `figAux`;
expansions at (d,L,W,g,E,t)=(3,3,2,1,0,1/2); `owx_*` at m=i, z=0, s=1, S=J/2, S⁺=J/4. Every deterministic hypothesis is discharged; left: the stochastic premises (`LWInit`, `LWLoop2`,
`LWLoopExp`, `LWXi`, local laws), E Z_w=0, and pins used as hypotheses. Limit check of (LW_assm) at these data: 𝓛^{(2)} ≈ W^-d Θ_ab ≤ W^-d/(1-t) < W^-2 = Ψ² (Θ=(1-tS^B)⁻¹ with row sums
1/(1-t), (a) Part B).
### b.11 Registry (DECISIONS §16, §20): the pre-check `import RBM3D` + probe + `#assert_rbm_axioms` (inventory block 20); name clashes; ports
    $ lake env lean $S/t2040/precheck.lean 2>&1 | grep "RBM\." | sed "s/RBM.Gauss.Sizes.//; s/[],]//g" | tr "\n" " "   # premises it finds unregistered
      [LWAvgLaw  STLocalEntry  LWtermEXP  LWInteg  LWReduceT  LWMomentExp  LWLoopExp  LWInit  LWLoop2  LWReduceB  LWMoment  LWXi  LWAnpKeyGh  LWAnpKey  LWtermB  LWtermExpN 
Proposed — owed: `LWMoment`, `LWMomentExp`, `LWReduceB/T`, `LWtermExpN`, `LWtermB`, `LWtermEXP`, `LWAnpKey(Gh)`, `LWInteg`, the three expansion Props (not borrowed: DECISIONS §5),
`STLocalEntry`, `LWAvgLaw`; structural: `LWInit`, `LWLoop2`, `LWLoopExp`, `LWXi` (lemma assumptions, proved by the consumer T2039), `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll`,
`LWAssm(Exp)`, `NGraph.{IsNested,NoGhost,GhostOK}`. None borrowed.
    $ lake env lean $S/t2040/clash_final.lean; cd $S && python3 t2040_clash.py | head -2; grep -c "RBM1D\|RBM2D" $PROBE
    probe declarations checked against `import RBM3D` (the library without the probe): 335; already declared there: 0 []
    probe declarations: 335, distinct last components: 222; main worktree HEAD 1c1f5e4, tracked non-probe .lean files scanned: 80
    last components that are also declared (any namespace) in main: 3
    0
No port: nothing copied from RBM1D/RBM2D (grep count 0; no sister project has this layer): no diff-stat. `const`, `mul`, `sum` are `GTerm` constructors.
## (c) Verified Mathlib names (62 `#check`ed, none deprecated; one line each with its type: inventory block 18)
    $ python3 t2040_names.py | tail -n +2 | (join the indented name lines) | fold -s -w 190
    #check elaborates, not deprecated: 62 of 62 names requested:
       Fin.consEquiv Fintype.sum_prod_type Fintype.sum_unique Finset.sum_comm Finset.sum_mul_sum Finset.mul_sum   Finset.sum_mul Finset.sum_congr Finset.sum_add_distrib Finset.sum_sub_distrib 
    Finset.sum_neg_distrib   star_sum star_mul' MeasureTheory.integral_sub MeasureTheory.integral_add MeasureTheory.integral_const_mul   MeasureTheory.integral_finsetSum 
    MeasureTheory.Integrable.add MeasureTheory.Integrable.const_mul   pow_add_pow_le pow_le_pow_left₀ Real.rpow_natCast Real.rpow_mul Real.rpow_add Real.rpow_neg_one   Real.rpow_two 
    Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.one_le_rpow Real.sqrt_eq_rpow   Real.le_sqrt_of_sq_le one_le_div inv_le_comm₀ le_inv_comm₀ inv_anti₀ inv_le_one_of_one_le₀   
    inv_lt_one_of_one_lt₀ div_le_one div_le_self ite_eq_left ite_eq_right ENNReal.one_le_ofReal   ENNReal.ofReal_le_ofReal ENNReal.ofReal_add MeasureTheory.measure_union_le 
    MeasureTheory.measure_mono   MeasureTheory.measure_univ Fintype.card_subtype_le Fintype.card_prod abs_norm MvPolynomial.eval   MvPolynomial.X Matrix.single deriv Nat.floor_zero 
    Even.pow_nonneg not_lt add_pos_of_nonneg_of_pos   Finset.sum_ite_eq lt_of_lt_of_le mul_lt_mul_of_pos_left Equiv.sum_comp
    requested names that are deprecated: none
    deprecated names checked and avoided (replacement used): if_pos -> ite_eq_left, if_neg -> ite_eq_right, if_true -> ite_true, if_false -> ite_false, Set.mem_setOf_eq -> Set.mem_ofPred_eq, 
    MeasureTheory.integral_finset_sum -> MeasureTheory.integral_finsetSum, ite_cond_eq_true -> ite_eq_left_of_eq_true
    error lines: 1 (the tactic `push_neg`, which is not a term; replaced by `push Not`)
## (d) Open issues and paper-delta candidates
T2040a (a): 7_8:65 takes Ψ_t=(W^-d B_{t,0})^{1/2}, violating W^-d/2 ≤ Ψ_t when B_{t,0}<1 (t=1/2, ĝ=1, L=3: 0.7407): pinned with a window hypothesis and a constant C₃. T2040c (a): L=3 odd,
the paper defines Z_L^d for even L (1_2:269); the pins take 3 ≤ L. T2040d: f is a resolvent polynomial (`MvPolynomial` in the entries of G, G*), the paper: "differentiable function of G"
(7_8:295, 310, 335); T2040i: ∂_{h_{αx}} = complex derivative along E_{αx}, undefined in §7; T2040e: the expansions for G_t (7_8:291) are pinned with S_t=tS, S⁺_t=S_t(1-m²S_t)⁻¹,
z_t=E+(1-t)m. T2040f: lem: EWGn2_N says "any t∈[0,1)" (3_5:407), pinned for 0 ≤ t ≤ `lemT z`; T2040g: lem:Anp_key's Ψ_t is Ψ_t(0) (7_8:949); T2040h: "w.l.o.g. Ψ_t decreasing" (3_5:389) is a
hypothesis (the sup-envelope keeps (eq:Psi); not proved). T2040j: `∃ c` precedes the sequence (c depends on p or the graph and the constants only); the Markov step needs `LWInteg` (true:
bounded, measurable). T2040k: lem: EWGn2_N for 1-t ≤ ĝ²/L² is "an immediate consequence" (7_8:20): needs a class from (LW_assm_exp), W^-d T~ ≍ B for r ≤ L and a sub-sequence transfer; pinned
as `LWtermExpN`. T2040l: lem:Anp (7_8:933) is about Γ^aux of a locally standard graph; `LWAnp` is the nested form (`lwanp_of_key`), def_auxgraph and GtoAG are LW-11; T2040m: Anp_key is "an
easy corollary" of the ghost version (7_8:1025); claim:size (7_8:264), claim:xi (7_8:884) have no proof in the paper (LW-09, LW-11). T2040n: the range "(Gt_bound_flow)-(Eq:Gdecay_flow)" of
lem:LWterm_EXP (6:83) is read as `STLocalEntry`, `LWAvgLaw`, `STLmax`, `STLK`, `STDecay` at time t ((Eq:Gdecay_w) is implied by (Eq:Gdecay_flow)). T2040o: the reductions 7_8:20-91
(`LWReduceB/T`) and the regime split (`LWtermExpS/N`) are not numbered statements in the paper; `LWedgeExp` writes k₁+1 for the paper's k₁ ≥ 1. Open: (Oe1x), (Oe2x) checked numerically, not
proved; `LWMomentExp` has no instance at t=t₀; the size model uses one rate (151 lines/kchar, two merged proof sets, 20.6 kchar) and fixed judgments for 9 items (9.4k of 27.0k lines).
