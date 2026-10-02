Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct  2 18:03:09 UTC 2026
**(i) Exponent table.** Notation: g = paper's `\ilambda` (main.tex:199) = the ticket's "λ" (`Bparam` in RBM3D uses `g`); τ=1−t, A=g²+τ, B₀=B_{t,0}=A⁻¹+(L^dτ)⁻¹; paper lines `1_2:` = 1_2_Intro_model_result.tex, `A:` = A_deterministic_estimates.tex. "(derived)" = my reading of the proof, not a paper statement.
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | d | 3 (any d≥3, `ML:Kbound` 1_2:1054); needs 2d−2>d for the pair sum of row 10 | d−2=1 (0 at d=2: not needed) |
| 2 | outer power of W^{-d}B₀ | n−1 (1_2:1054) = prefactor W^{-d(n−1)} of (eq_Ktree) A:370/(eq_K-Kpi) A:621 times B₀^{n−1} of (eq:K-pi-bound) A:675; n=1: \|K⁽¹⁾\|=\|m\|=1 ≤ B₀⁰ (script: \|m\|=1.000000000000) | exact; C₁=1 |
| 3 | B₀-count (derived, A:703–800) | molecule k with e_k attached external/long-internal edges gives B₀^{e_k−2}, the root one gives B₀^{e−1}; Σe_k=n+2(r−1) ⇒ Σ(e_k−2)+1=n−1; \|Z^off_4\|=2 (pairs {1,3},{2,4}); n=4 has 3 trees (star, two H-trees; used in the script) | 0 |
| 4 | free summations | n=2: 0; n=3: 1 (b); n≥4: 1 (b₁∈Z_L^d), the other vertices are held by the molecule decay (eq:molecule-decay) A:691; a free sum of a long edge costs ≤1/τ (‖Θ‖_{∞→∞}≤1/τ, 1_2:1141) | the 1/τ is cancelled by the sum-zero factor O(τ) (A:731): slack 0 |
| 5 | Θ pointwise (1_2:1144) | \|Θ(0,a)\|≤C_dB_{t,\|a\|}≤C_dB₀; limit check (TEAM 8.14): τ·rowsum Θ⁽⁺'⁻⁾=1.000000000 and L^dτΘ(0,0)→1.00026 (τ=10⁻⁶): the zero-mode term of B equals Θ⁽⁺'⁻⁾'s, normalisation consistent | sup\|Θ\|/B_{\|a\|}=0.632 (τ=0.1), 1.000 (τ=10⁻⁶): C_d=1 |
| 6 | molecule sums (A:731) | Σ_{b∖b₁}Σ^∅=O(τ), Σ\|Σ^∅\|=O(A); proofs use pure loop (A:643), (prop:ThfadC_short), Ward (WI_calK) | constants depend on κ,d |
| 7 | difference exponents | f₁≺A⁻¹/(\|x\|^{d−1}+1), f₂≺A⁻¹/(\|x\|^d+1) (A:749; 1_2:1153,1159); zero mode cancels in differences, and Θ̊=Θ−L^{-2d}ΣΘ satisfies (1_2:1165) | script sup\|Θ̊\|·A·(\|a\|+1)=0.622 (τ=0.1), 0.520 (τ=10⁻⁶), ≤1 |
| 8 | lattice sums S_p=Σ_{x∈Z_L^3}(\|x\|+1)^{-p} | p<d: ~L^{3−p}; p=d=3: 24·ln(L/2)+O(1) (shell sizes 24r²+2); p>d: O(1) | script: S₃=24.1,82.2,148.2 (L=17,257,4097); S₄≤8.9 |
| 9 | ξ=2 term (A:768) | Σ_{b₁}(\|x\|^d+1)⁻¹=S_d: the only borderline sum, loss log L (the rest is O(1)) | slack 0; absorbed by ≺ |
| 10 | two-f₁ term | AM–GM 2/(\|x\|^{d−1}\|y\|^{d−1})≤1/(\|x\|^d\|y\|^{d−2})+1/(\|x\|^{d−2}\|y\|^d); Σ_b bounded (total decay 2d−2=4>3) | script: 14.26, 16.39, 17.65 at L=9,17,33 (saturating) |
| 11 | n=2,3 (derived) | n=2: K=W^{-d}m₁m₂Θ(a₁,a₂), no sum, no loss. n=3: Σ_b ΠΘ; non-pure σ has exactly one equal-charge pair (short edge, Σ_b=O(1)) and two long (B₀ each); pure σ has 3 short edges. The paper (A:673) cites only (prop:ThfadC); (prop:ThfadC_short) is also used | no loss; candidate T2004a |
| 12 | candidate constants C_n (n=2,3,4) | max_{σ,a}\|K⁽ⁿ⁾\|/(W^{-d}B₀)^{n−1} ≤ 1.000, 0.5, 0.5 over the 8 tested points with g≤0.5 (n=4 only at L≤5) | tested, not a proof; C_n=1 |
| 13 | upper bound on g | pure loops are O(W^{-d(n−1)}) (A:643), so B₀≳1 is needed: B₀≥(1+g²)⁻¹ (instance ≥0.8). Script g=10: ratios 13.9, 223.6, 4071.7 (n=2,3,4) | the pin needs g≤g_max (paper: g≤𝔡⁻¹, 1_2:363; or g∧1, footnote 1_2:372); C_n=C_n(g_max) |
| 14 | κ, E | \|m\|=1 and \|1−m²\|=√(4−E²) (E=0: 2; E=1: 1.732); constants of (prop:ThfadC_short) depend on κ,d; Ward uses \|m\|=1 (Σ_{a₂}K⁽²⁾=W^{-d}/(1−t\|m\|²)) | E∈[−2+κ,2−κ] |
| 15 | regimes of τ (g=½, L=5) | B₀≍1/max(g²,τ) for τ≥g²/(L^d−1)=0.00202, B₀≍(L^dτ)⁻¹ below; ℓ_t=1 (τ≥g²=0.25), gτ^{-1/2} (g²/L²=0.01≤τ≤g²), L (τ≤0.01); for g²/L^d≤τ≤g²/L² the zero mode overtakes the polynomial term of B_{t,K} at K+1=(L^dτ/g²)^{1/(d−2)}∈[1,L] | instance τ=0.1: ℓ_t=1.5811, B₀=2.9371; τ=10⁻⁴,10⁻⁶ rows are in the zero-mode regime |
| 16 | loss ≺ (1_2:229–234) | deterministic ξ≺ζ iff ξ≤N^τζ ∀τ>0, N=(WL)^d. Lean: loss L^τ ∀τ>0, constant C_{n,τ}(d,κ,g_max) fixed before g,L,W; log L≤C_τL^τ and L^τ≤N^{τ/d}, so it implies the paper's ≺ | the \|s\|-truncation (R≍log L) and the ≺ of (prop:BD1,BD2,ThfadC0) are PT-gate (T2003) inputs: not checked here that they hold with L^τ |
| 17 | (WI_calK), η_t=(1−t)Im m (1_2:720) | n≥2, σ₁=−σ_n; E=0: η=0.1, E=1: η=0.0866; Σ_{a₂}K⁽²⁾=W^{-d}/τ=1.25=(m(+)−m(−))/(2iW^dη_t) | script Ward err ≤2·10⁻¹⁵ (n=2,3,4) |
| 18 | (pro_dyncalK),(eq:initial_K) | K⁽²⁾,K⁽³⁾ (Kn2sol/3sol) and K⁽⁴⁾=(eq_Ktree) satisfy the ODE; t=0 gives M⁽⁴⁾ | finite-difference rel. err ≤1.1·10⁻⁸ (h=10⁻⁵) |
**(ii) One nondegenerate instance.** d=3, L=5 (odd L: block lattice [−2,2]³, 125 blocks; paper footnote 1_2:269), W=2 (N=(WL)^d=1000), g=½ (W^{-3/2}=0.3536≤g≤𝔡⁻¹ for 𝔡≤½), E∈{0,1} (|m|=1), t=9/10 (τ=0.1∈[0,1)), n∈{2,3,4}, all σ∈{±}ⁿ, all a. S^(B): diagonal 0.4, six neighbours 0.1, row sum 1. Θ by exact Fourier sum. PT hypotheses ((prop:ThfadC) etc., shapes of lem_propTH, external) are checked at this data in rows 5, 7. Command (script below saved as T2004_pre.py): `python3 T2004_pre.py`
```python
import numpy as np, itertools as it  # T2004 preflight script
class Mod:  # d, block side L, W, g (paper \ilambda = ticket lambda), E in the bulk; m(+)=m_sc(E+i0), m(-)=conj
    def __init__(s,d,L,W,g,E):
        s.d,s.L,s.W,s.g,s.N=d,L,W,g,L**d; m=(-E+1j*np.sqrt(4-E*E))/2; s.ms={1:m,-1:np.conj(m)}
        k=np.meshgrid(*[2*np.pi*np.arange(L)/L]*d,indexing='ij'); s.sh=(1+2*g*g*sum(np.cos(x) for x in k))/(1+2*d*g*g)  # symbol of S^(B)
        p=np.array(list(it.product(range(L),repeat=d))); D=(p[:,None,:]-p[None,:,:])%L; s.D=tuple(D[...,i] for i in range(d))
        s.S=np.fft.ifftn(s.sh)[s.D].real
    def C(s,a,b,t): return np.fft.ifftn(1/(1-t*s.ms[a]*s.ms[b]*s.sh))[s.D]          # Theta^{(a,b)}_t(x,y), def_Thxi
    def B0(s,t): return 1/(s.g**2+1-t)+1/(s.L**s.d*(1-t))                           # B_{t,0}
    def pm(s,sg): return np.prod([s.ms[x] for x in sg])
    def K(s,sg,t):  # (Kn2sol), (Kn3sol), (eq_Ktree) n=4 (3 trees); full array over (Z_L^d)^n
        n=len(sg); c=[s.C(sg[i],sg[(i+1)%n],t) for i in range(n)]; I=np.eye(s.N); pf=s.W**(-s.d*(n-1))*s.pm(sg); e=lambda q,*o: np.einsum(q,*o,optimize=True)
        if n==2: return pf*c[0]
        if n==3: return pf*e('ib,jb,kb->ijk',*c)
        F31=s.C(sg[2],sg[0],t)-I; F42=s.C(sg[3],sg[1],t)-I   # internal edges (Theta^{(s_k,s_l)}-I), f-internal
        return pf*(e('ib,jb,kb,lb->ijkl',*c)+e('ip,jp,pq,kq,lq->ijkl',c[0],c[1],F31,c[2],c[3])+e('iq,jp,kp,lq,pq->ijkl',c[0],c[1],c[2],c[3],F42))
    def rhs(s,sg,t):  # RHS of (pro_dyncalK) via cutL/cutR index maps (calGonIND)
        n=len(sg); ab='abcdefgh'[:n]; r=0
        for k in range(1,n+1):
            for l in range(k+1,n+1):
                r=r+s.W**s.d*np.einsum(ab[:k-1]+'x'+ab[l-1:]+',xy,'+ab[k-1:l-1]+'y->'+ab,s.K(sg[:k]+sg[l-1:],t),s.S,s.K(sg[k-1:l],t),optimize=True)
        return r
    def ratio(s,n,t):  # max_{sigma,a} |K^(n)| / (W^-d B_0)^(n-1), a_1=0 (translation invariance, lem_propTH 2)
        r=0
        for sg in it.product([1,-1],repeat=n):
            c=[s.C(sg[i],sg[(i+1)%n],t) for i in range(n)]; I=np.eye(s.N); e=lambda q,*o: np.einsum(q,*o,optimize=True)
            if n==2: v=c[0][0]
            if n==3: v=e('b,jb,kb->jk',c[0][0],c[1],c[2])
            if n==4:
                F31=s.C(sg[2],sg[0],t)-I; F42=s.C(sg[3],sg[1],t)-I; U=(c[1]*c[0][0][None,:])@F31
                v=e('q,jq,kq,lq->jkl',c[0][0],c[1],c[2],c[3])+e('jq,kq,lq->jkl',U,c[2],c[3])+e('jkq,q,lq->jkl',e('jp,kp,pq->jkq',c[1],c[2],F42),c[0][0],c[3])
            r=max(r,s.W**(-s.d*(n-1))*abs(s.pm(sg))*np.abs(v).max()/(s.W**(-s.d)*s.B0(t))**(n-1))
        return round(float(r),3)
d,L,W,g,t=3,5,2,0.5,0.9
for E,LL,ns in ((0,5,(2,3)),(1,5,(2,3)),(0,3,(4,)),(1,3,(4,))):  # ODE+Ward at d=3,W=2,g=1/2,t=9/10 (n=4 dense: L=3); |m|=1 needed for Ward
    M=Mod(d,LL,W,g,E); h=1e-5; eta=(1-t)*M.ms[1].imag; out=[]
    for n in ns:
        ode=ward=0
        for sg in it.product([1,-1],repeat=n):
            R=M.rhs(sg,t); ode=max(ode,abs((M.K(sg,t+h)-M.K(sg,t-h))/(2*h)-R).max()/abs(R).max())
            if sg[0]==-sg[-1]:
                k1=lambda x: np.full(M.N,M.ms[x]) if n==2 else M.K((x,)+sg[1:-1],t); lhs=M.K(sg,t).sum(axis=n-1)
                ward=max(ward,abs(lhs-(k1(1)-k1(-1))/(2j*W**d*eta)).max()/abs(lhs).max())
        out.append((n,'ODE %.1e'%ode,'Ward %.1e'%ward))
    print('E=%d L=%d |m|=%.12f S00,S01=%.3f,%.3f rowsum=%.12f'%(E,LL,abs(M.ms[1]),M.S[0,0],np.sort(M.S[0])[-2],M.S[0].sum()),out)
M=Mod(d,3,W,g,0); K0=M.K((1,-1,1,-1),0.0); dg=np.einsum('iiii->i',K0); print('t=0: K4 diag err %.1e, offdiag max %.1e (initial_K, KMloop)'%(abs(dg-W**(-9)*M.pm((1,-1,1,-1))).max(),abs(K0-np.einsum('i,ij,ik,il->ijkl',dg,*[np.eye(27)]*3)).max()))
for (L,g,t,E) in [(5,.5,.9,0),(5,.5,.9,1),(5,.5,1-1e-4,0),(5,.5,1-1e-6,0),(5,.05,.9,0),(5,.05,1-1e-6,0),(5,10.,.9,0),(7,.5,1-1e-6,0),(9,.05,1-1e-5,0)]:
    M=Mod(d,L,W,g,E); print('L=%d g=%g 1-t=%.0e E=%d B0=%.4g'%(L,g,1-t,E,M.B0(t)),{n:M.ratio(n,t) for n in ((2,3,4) if L<=5 else (2,3))})
for tt in (0.9,1-1e-6):  # limit/normalisation check of the PT shapes (TEAM 8.14): row sum 1/tau, zero mode 1/(L^d tau), (prop:ThfadC), (prop:ThfadC0)
    g=0.5; M=Mod(d,5,W,g,0); tau=1-tt; dist=np.max(np.minimum(np.indices((5,)*d),5-np.indices((5,)*d)),axis=0).ravel(); Bk=1/((g*g+tau)*(dist+1.))+1/(125*tau)
    r=[abs(M.C(a,b,tt)[0])/Bk for a in (1,-1) for b in (1,-1)]; z=abs(M.C(1,-1,tt)[0]-1/(125*tau))*(g*g+tau)*(dist+1.)
    print('1-t=%.0e: tau*rowsum(+,-)=%.9f  L^d*tau*Theta(0,0)=%.6f  sup|Th|/B_|a|=%.3f  sup|zTh|(g^2+tau)(|a|+1)=%.3f'%(tau,tau*M.C(1,-1,tt)[0].sum().real,125*tau*M.C(1,-1,tt)[0,0].real,max(x.max() for x in r),z.max()))
Sp=lambda p,L: sum((1 if r==0 else (2*r+1)**d-(2*r-1)**d)*(r+1.)**-p for r in range((L-1)//2+1))   # sum_{x in Z_L^3} (|x|_inf+1)^-p
for L in (17,257,4097): print('Sp L=%d  p=1,2,3,4:'%L,[round(Sp(p,L),1) for p in (1,2,3,4)])
for LL in (9,17,33):  # max_c sum_b 1/((|b|^3+1)(|c-b|+1)) on Z_LL^3: bounded in L (2d-2>d)
    ax=np.minimum(np.arange(LL),LL-np.arange(LL)); ds=np.max(np.meshgrid(ax,ax,ax,indexing='ij'),axis=0).astype(float)
    print('pair sum L=%d: %.3f'%(LL,np.fft.ifftn(np.fft.fftn(1/(ds**d+1))*np.fft.fftn(1/(ds**(d-2)+1))).real.max()),end='; ')
print()
print('instance: B_{t,0}=%.4f  g^2+tau=%.2f L^d tau=%.1f  ell_t=%.4f  g^2/L^2=%.4f g^2/L^d=%.4f  N=%d  W^{-d/2}=%.4f'%(Mod(d,5,W,.5,0).B0(.9),.25+.1,125*.1,min(max(.5/np.sqrt(.1),1),5),.25/25,.25/125,(W*5)**d,W**-1.5))
```
```
E=0 L=5 |m|=1.000000000000 S00,S01=0.400,0.100 rowsum=1.000000000000 [(2, 'ODE 3.1e-09', 'Ward 3.6e-16'), (3, 'ODE 3.8e-09', 'Ward 8.2e-16')]
E=1 L=5 |m|=1.000000000000 S00,S01=0.400,0.100 rowsum=1.000000000000 [(2, 'ODE 3.1e-09', 'Ward 1.2e-15'), (3, 'ODE 3.8e-09', 'Ward 1.2e-15')]
E=0 L=3 |m|=1.000000000000 S00,S01=0.400,0.100 rowsum=1.000000000000 [(4, 'ODE 1.1e-08', 'Ward 1.9e-15')]
E=1 L=3 |m|=1.000000000000 S00,S01=0.400,0.100 rowsum=1.000000000000 [(4, 'ODE 1.1e-08', 'Ward 1.8e-15')]
t=0: K4 diag err 0.0e+00, offdiag max 0.0e+00 (initial_K, KMloop)
L=5 g=0.5 1-t=1e-01 E=0 B0=2.937 {2: 0.632, 3: 0.298, 4: 0.222}
L=5 g=0.5 1-t=1e-01 E=1 B0=2.937 {2: 0.632, 3: 0.324, 4: 0.261}
L=5 g=0.5 1-t=1e-04 E=0 B0=84 {2: 0.977, 3: 0.486, 4: 0.494}
L=5 g=0.5 1-t=1e-06 E=0 B0=8004 {2: 1.0, 3: 0.5, 4: 0.5}
L=5 g=0.05 1-t=1e-01 E=0 B0=9.836 {2: 0.899, 3: 0.429, 4: 0.387}
L=5 g=0.05 1-t=1e-06 E=0 B0=8400 {2: 0.962, 3: 0.463, 4: 0.45}
L=5 g=10 1-t=1e-01 E=0 B0=0.08999 {2: 13.903, 3: 223.559, 4: 4071.724}
L=7 g=0.5 1-t=1e-06 E=0 B0=2919 {2: 0.999, 3: 0.5}
L=9 g=0.05 1-t=1e-05 E=0 B0=535.6 {2: 0.428, 3: 0.092}
1-t=1e-01: tau*rowsum(+,-)=1.000000000  L^d*tau*Theta(0,0)=23.219079  sup|Th|/B_|a|=0.632  sup|zTh|(g^2+tau)(|a|+1)=0.622
1-t=1e-06: tau*rowsum(+,-)=1.000000000  L^d*tau*Theta(0,0)=1.000260  sup|Th|/B_|a|=1.000  sup|zTh|(g^2+tau)(|a|+1)=0.520
Sp L=17  p=1,2,3,4: [720.6, 119.2, 24.1, 6.7]
Sp L=257  p=1,2,3,4: [195188.5, 2876.4, 82.2, 8.7]
Sp L=4097  p=1,2,3,4: [50307260.3, 48824.0, 148.2, 8.9]
pair sum L=9: 14.264; pair sum L=17: 16.391; pair sum L=33: 17.646; 
instance: B_{t,0}=2.9371  g^2+tau=0.35 L^d tau=12.5  ell_t=1.5811  g^2/L^2=0.0100 g^2/L^d=0.0020  N=1000  W^{-d/2}=0.3536
```
**Verdicts.** `Def_Ktza` (+(Kn2sol),(Kn3sol)): PASS. `lem_WI_K`: PASS (needs |m|=1, row 14). `ML:Kbound` (eq:bcal_k) n=1..4 and the general-n exponent count: PASS, with pin requirements: constants may depend on d,κ,g_max,n,τ (rows 13,14,16), loss L^τ (row 16), not on g,L,W. Nothing BLOCKED; PT shapes are local hypotheses.
Paper-delta candidates: T2004a (n=3 case of the `ML:Kbound` proof also uses (prop:ThfadC_short)); T2004b (the statement `ML:Kbound` omits the upper bound g≤g_max that it needs, row 13).

## (a′) Preflight corrections — Fri Oct  2 23:14:07 UTC 2026
1. Row 7 and the `ML:Kbound` verdict do not say for which (a, r) (prop:BD1), (prop:BD2) hold. With the paper's range |r| ≲ |a| both are false at r = −a (|r| = |a|): at t = 0, Θ_0 = I, the left side of (prop:BD1) is 1 and the right side is of order L^τ/|a|; the needed constant grows like L (block `bd` of the script `ext`, in (b)). The pins use |r| ≤ c|a|, c < 1 (T2004c). The proof of (eq:ind-step-bound) needs (eq:f12) for |s_j| ≺ 1 only; for |a_j − b_1| ≲ |s_j| the bounds follow from (prop:ThfadC0) (the zero mode cancels in f_1, f_2) and (|s_j|+1)^d ≺ 1 (derived here, not a paper statement). No verdict changes.
2. Rows 5, 17: Θ_1^{(+,−)} does not exist (row 5: τ·rowsum = 1.000000000, so Θ_t(0,0) ≥ 1/(L^dτ) → ∞) and η_1 = 0; the paper's "t ∈ [0,1]" in `Def_Ktza` (1_2:988–989) and in the definition of Θ_t (1_2:1072) is read as t ∈ [0,1), and (WI_calK) divides by η_t (T2004d). No verdict changes.
## (b) Script output (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2004, branch t/T2004, commands run from its root; X.py = `sed -n "/PY-BEGIN X$/,/PY-END X$/p" RBM3D/Probe/T2004Pins.lean | sed '1d;$d'`, X in inv, consumers, ports, ext, clash, stmts)
$ date -u; git log -1 --format='%h %s'; git status --short   # status empty = clean
Fri Oct  2 23:14:07 UTC 2026
64b58eb T2004: probe: inventory prints the binders of the Prop-valued definitions
$ lake build RBM3D.Probe.T2004Pins > build.txt 2>&1; tail -1 build.txt; grep -c 'warning\|error' build.txt
Build completed successfully (3253 jobs).
0
$ lake env lean RBM3D/Probe/T2004Pins.lean > out.txt 2>&1; echo exit=$?; grep -c "warning\|error" out.txt; grep -v "depends on axioms" out.txt | cut -c1-400 | head -3; tail -2 out.txt | cut -c1-150
exit=0
0
204 constants with prefix RBM.Loop.KL; axioms used: [propext, Classical.choice, Quot.sound]; constants using another axiom: 0
21 constants with prefix RBM.Loop.KLinst_; axioms used: [propext, Classical.choice, Quot.sound]; constants using another axiom: 0
names after the prefix: Kpi, KpiBound, bound_four, bound_one, bound_three, bound_two, indStep, molecule, ode, pure, retire_bound, retire_kTwoFormula, retire_two, scales, sumZero, three, two, unique, ward, wardIneq, ward_two
RBM.Loop.KTreeRep : (d L : ℕ) → [NeZero L] → ℕ → ℝ → (Bool → ℂ) → (ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) → Prop
RBM.ThetaDecay : ℕ → ℝ → ℂ → Prop
$ n=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' out.txt); m=$(grep 'depends on axioms' out.txt | grep -vc '\[propext, Classical.choice, Quot.sound\]'); k=$(grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/Probe/T2004Pins.lean); echo "standard-axiom lines $n, other-axiom lines $m, sorry/admit/native_decide/axiom matches $k"
standard-axiom lines 71, other-axiom lines 0, sorry/admit/native_decide/axiom matches 0
Statements extracted from the file (`python3 stmts.py NAME...`; `A+B` joins two definitions with ||; the theorems of sections Proofs, Proofs2 take the section variables (d L : ℕ) [NeZero L] (g : ℝ) first):
$ python3 stmts.py KLn KLgen KLK   # Def_Ktza, option B: the tree sum (eq_Ktree) is the definition
noncomputable def KLn (W : ℕ) (m : Bool → ℂ) (t : ℝ) (n : ℕ) [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ := (∏ i, m (σ i)) * (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, KLtreeValG d L g m t σ a F
noncomputable def KLgen (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ := if I.length = 1 then m (I.σ.getD 0 false) else if I.length = 2 then kTwo d L W g m t (I.σ.getD 0 false) (I.σ.getD 1 false) (I.a.getD 0 0) (I.a.getD 1 0) else if h : 3 ≤ I.length then haveI : NeZero I.length := ⟨by omega⟩ KLn d L g W m t I.length (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) else 0
noncomputable def KLK (W : ℕ) (E t : ℝ) (I : LoopIdx (Zd d L)) : ℂ := KLgen d L g W (mSigma E) t I
$ python3 stmts.py KLK_two KLK_three KLK_eq_sum_Kpi KLward_two KLBoundAt_two KLBoundAt_three KLBoundAt_prec KLretire_twoLoopBounded KLretire_KLoopBound   # proved here
theorem KLK_two (W : ℕ) (E t : ℝ) (s₁ s₂ : Bool) (a₁ a₂ : Zd d L) : KLK d L g W E t ⟨[s₁, s₂], [a₁, a₂]⟩ = ((W : ℂ) ^ d)⁻¹ * (mSigma E s₁ * mSigma E s₂) * Theta d L g ((t : ℂ) * (mSigma E s₁ * mSigma E s₂)) a₁ a₂
theorem KLK_three (W : ℕ) (E t : ℝ) (s₁ s₂ s₃ : Bool) (a₁ a₂ a₃ : Zd d L) : KLK d L g W E t ⟨[s₁, s₂, s₃], [a₁, a₂, a₃]⟩ = (((W : ℂ) ^ d)⁻¹) ^ 2 * (mSigma E s₁ * mSigma E s₂ * mSigma E s₃) * ∑ b : Zd d L, Theta d L g ((t : ℂ) * (mSigma E s₁ * mSigma E s₂)) a₁ b * Theta d L g ((t : ℂ) * (mSigma E s₂ * mSigma E s₃)) a₂ b * Theta d L g ((t : ℂ) * (mSigma E s₃ * mSigma E s₁)) a₃ b
theorem KLK_eq_sum_Kpi (W : ℕ) (E t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (σ : Fin n → Bool) (a : Fin n → Zd d L) : KLK d L g W E t (KLloopOf d L σ a) = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ π ∈ (diagonals n).powerset, KLKpi d L g (mSigma E) t σ a π
theorem KLward_two (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (a₁ : Zd d L) : ∑ x : Zd d L, KLK d L g W E t ⟨[s, !s], [a₁, x]⟩ = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ * (KLK d L g W E t ⟨[true], [a₁]⟩ - KLK d L g W E t ⟨[false], [a₁]⟩)
theorem KLBoundAt_two {d : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hD : KLDecay d gmax) : KLBoundAt d 2 κ gmax
theorem KLBoundAt_three {k : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hD : KLDecay (k + 2) gmax) (hS : KLShort (k + 2) κ gmax) : KLBoundAt (k + 2) 3 κ gmax
theorem KLBoundAt_prec {d n : ℕ} (hd : 1 ≤ d) {κ gmax : ℝ} (h : KLBoundAt d n κ gmax) : ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ (p : KLPar κ gmax), N₀ ≤ (p.W * p.L) ^ d → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d p.L), ‖KLK d p.L p.g p.W p.E p.t (KLloopOf d p.L σ a)‖ ≤ (((p.W * p.L) ^ d : ℕ) : ℝ) ^ τ * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 1)
theorem KLretire_twoLoopBounded {d L W : ℕ} [NeZero L] {g : ℝ} {m : Bool → ℂ} {K : ℝ → LoopIdx (Zd d L) → ℂ} (hK : IsKLoop d L W g m (Set.Ico 0 1) K) : TwoLoopBounded d L K
theorem KLretire_KLoopBound {d : ℕ} {κ gmax : ℝ} (hall : ∀ n, 1 ≤ n → KLBoundAt d n κ gmax) (p : KLPar κ gmax) : KLoopBound d p.L p.W p.g (fun t I => KLK d p.L p.g p.W p.E t I)
$ python3 stmts.py KLPar KLDecay KLShort KLDiffOne+KLDiffTwo KLZero KLPT   # local hypotheses: parameter range and the shapes of lem_propTH (5), (5'), (6), (7), (8)
structure KLPar (κ gmax : ℝ) where L : ℕ W : ℕ hL : 3 ≤ L hW : 1 ≤ W g : ℝ hg0 : 0 < g hg1 : g ≤ gmax E : ℝ hE : |E| ≤ 2 - κ t : ℝ ht0 : 0 ≤ t ht1 : t < 1
def KLDecay (d : ℕ) (gmax : ℝ) : Prop := ∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L, haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g (t : ℂ) 0 a‖ ≤ Cd * Bparam d L g t (zdistD d L a) * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)
def KLShort (d : ℕ) (κ gmax : ℝ) : Prop := ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s : Bool, ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L, haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g ((t : ℂ) * (mSigma E s * mSigma E s)) 0 a‖ ≤ Cκ * ((if a = 0 then 1 else 0) + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ)))
def KLDiffOne (d : ℕ) (gmax : ℝ) : Prop := ∀ c : ℝ, 0 < c → c < 1 → ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) → haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g (t : ℂ) 0 (a + r) - Theta d L g (t : ℂ) 0 a‖ ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ || def KLDiffTwo (d : ℕ) (gmax : ℝ) : Prop := ∀ c : ℝ, 0 < c → c < 1 → ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) → haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g (t : ℂ) 0 (a + r) + Theta d L g (t : ℂ) 0 (a - r) - 2 * Theta d L g (t : ℂ) 0 a‖ ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹
def KLZero (d : ℕ) (gmax : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L, haveI : NeZero L := ⟨by omega⟩ ‖Theta0 d L g (t : ℂ) 0 a‖ ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹
structure KLPT (d : ℕ) (κ gmax : ℝ) : Prop where decay : KLDecay d gmax short : KLShort d κ gmax diffOne : KLDiffOne d gmax diffTwo : KLDiffTwo d gmax zeroMode : KLZero d gmax
$ python3 stmts.py KLisKLoopPin KLuniquePin KLwardPin KLBoundAt+KLboundPin KLwardIneqAt+KLwardIneqPin KLKpiBoundAt+KLKpiBoundPin KLpureAt+KLpurePin KLmoleculeAt+KLmoleculePin KLsumZeroAt+KLsumZeroPin KLindStepAt+KLindStepPin   # the pins (Prop-valued; proved by the KL tickets)
def KLisKLoopPin : Prop := ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → IsKLoop d L W g (mSigma E) (Set.Ico 0 1) (fun t I => KLK d L g W E t I)
def KLuniquePin : Prop := ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoop d L W g (mSigma E) (Set.Ico 0 1) K → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length → K t I = KLK d L g W E t I
def KLwardPin : Prop := ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 → ∑ x : Zd d L, KLK d L g W E t ⟨s :: μ ++ [!s], a ++ [x]⟩ = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ * (KLK d L g W E t ⟨true :: μ, a⟩ - KLK d L g W E t ⟨false :: μ, a⟩)
def KLBoundAt (d n : ℕ) (κ gmax : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (a : Fin n → Zd d p.L), ‖KLK d p.L p.g p.W p.E p.t (KLloopOf d p.L σ a)‖ ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 1) || def KLboundPin : Prop := ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax → KLBoundAt d n κ gmax
def KLwardIneqAt (d n : ℕ) (κ gmax : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (a : Fin (n - 1) → Zd d p.L), ∑ x : Zd d p.L, ‖KLK d p.L p.g p.W p.E p.t ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖ ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d) * Gauss.etaT p.E p.t)⁻¹ * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 2) || def KLwardIneqPin : Prop := ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax → KLwardIneqAt d n κ gmax
def KLKpiBoundAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d p.L), ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖ ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1) || def KLKpiBoundPin : Prop := ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax → KLKpiBoundAt d n κ gmax
def KLpureAt (d n : ℕ) (κ gmax : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (s : Bool) (a : Fin n → Zd d p.L), ‖KLK d p.L p.g p.W p.E p.t (KLloopOf d p.L (fun _ => s) a)‖ ≤ C * (((p.W : ℝ) ^ d)⁻¹) ^ (n - 1) * Real.exp (-(c * (KLmaxDist d p.L a : ℝ))) || def KLpurePin : Prop := ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax → KLShort d κ gmax → KLpureAt d n κ gmax
def KLmoleculeAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (δ : Fin n → Zd d p.L), ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ C * Real.exp (-(c * (KLmaxDist d p.L δ : ℝ))) || def KLmoleculePin : Prop := ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLShort d κ gmax → KLmoleculeAt d n κ gmax
def KLsumZeroAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (x : Zd d p.L), ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x), KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (1 - p.t) ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ 0 = x), ‖KLSigmaPi d p.L p.g (mSigma p.E) p.t (KLsigAlt n) ∅ δ‖ ≤ C * (p.g ^ 2 + (1 - p.t)) || def KLsumZeroPin : Prop := ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 4 ≤ n → Even n → 0 < κ → 0 < gmax → KLShort d κ gmax → KLsumZeroAt d n κ gmax
def KLindStepAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (r : Fin n), σ r ≠ σ (r + 1) → ∀ a : Fin n → Zd d p.L, ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d p.L => δ r = b), KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ * ∏ i ∈ Finset.univ.erase r, thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖ ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 2) || def KLindStepPin : Prop := ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax → KLindStepAt d n κ gmax
$ python3 stmts.py KLinst_ode KLinst_unique KLinst_ward KLinst_ward_two KLinst_two KLinst_three KLinst_Kpi KLinst_bound_one KLinst_bound_two KLinst_bound_three KLinst_bound_four KLinst_wardIneq KLinst_KpiBound KLinst_pure KLinst_molecule KLinst_sumZero KLinst_indStep   # compiled instances at d=3, L=5, W=2, g=1/2, E=0, t=9/10, kappa=gmax=1 (KLinstPar); hypotheses left: the pin itself and KLPT 3 1 1
theorem KLinst_ode (h : KLisKLoopPin) : HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 KLinstσ KLinsta)) (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I) (KLloopOf 3 5 KLinstσ KLinsta)) (9 / 10) :=
theorem KLinst_unique (hu : KLuniquePin) (K : ℝ → LoopIdx (Zd 3 5) → ℂ) (hK : IsKLoop 3 5 2 (1 / 2) (mSigma 0) (Set.Ico 0 1) K) : K (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩ = KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩ :=
theorem KLinst_ward (h : KLwardPin) : ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false] ++ [!true], [0, 1] ++ [x]⟩ = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ * (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨true :: [false], [0, 1]⟩ - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨false :: [false], [0, 1]⟩)
theorem KLinst_ward_two : ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, x]⟩ = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ * (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false], [0]⟩)
theorem KLinst_two : KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, 1]⟩ = ((2 : ℂ) ^ 3)⁻¹ * (mSigma 0 true * mSigma 0 false) * Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) 0 1
theorem KLinst_three : KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩ = (((2 : ℂ) ^ 3)⁻¹) ^ 2 * (mSigma 0 true * mSigma 0 false * mSigma 0 true) * ∑ b : Zd 3 5, Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) 0 b * Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 false * mSigma 0 true)) 1 b * Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 true)) 2 b
theorem KLinst_Kpi : KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3]) = (((2 : ℂ) ^ 3)⁻¹) ^ 3 * ∑ π ∈ (diagonals 4).powerset, KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, false, true, false] ![0, 1, 2, 3] π
theorem KLinst_bound_one (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true] ![0])‖ ≤ C * (5 : ℝ) ^ τ * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (1 - 1)
theorem KLinst_bound_two (hPT : KLPT 3 1 1) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false] ![0, 1])‖ ≤ C * (5 : ℝ) ^ τ * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 1)
theorem KLinst_bound_three (hPT : KLPT 3 1 1) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 KLinstσ KLinsta)‖ ≤ C * (5 : ℝ) ^ τ * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1)
theorem KLinst_bound_four (hpin : KLboundPin) (hPT : KLPT 3 1 1) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])‖ ≤ C * (5 : ℝ) ^ τ * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)
theorem KLinst_wardIneq (hpin : KLwardIneqPin) (hPT : KLPT 3 1 1) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨List.ofFn KLinstσ, List.ofFn ![0, 1] ++ [x]⟩‖ ≤ C * (5 : ℝ) ^ τ * (((2 : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2)
theorem KLinst_KpiBound (hpin : KLKpiBoundPin) (hPT : KLPT 3 1 1) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, false, true, false] ![0, 1, 2, 3] ∅‖ ≤ C * (5 : ℝ) ^ τ * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)
theorem KLinst_pure (hpin : KLpurePin) (hPT : KLPT 3 1 1) : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 (fun _ => true) KLinsta)‖ ≤ C * (((2 : ℝ) ^ 3)⁻¹) ^ (3 - 1) * Real.exp (-(c * (KLmaxDist 3 5 KLinsta : ℝ)))
theorem KLinst_molecule (hpin : KLmoleculePin) (hPT : KLPT 3 1 1) : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ KLinsta‖ ≤ C * Real.exp (-(c * (KLmaxDist 3 5 KLinsta : ℝ)))
theorem KLinst_sumZero (hpin : KLsumZeroPin) (hPT : KLPT 3 1 1) : ∃ C : ℝ, 0 < C ∧ ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0), KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ ≤ C * (1 - 9 / 10) ∧ ∑ δ ∈ Finset.univ.filter (fun δ : Fin 4 → Zd 3 5 => δ 0 = 0), ‖KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLsigAlt 4) ∅ δ‖ ≤ C * ((1 / 2) ^ 2 + (1 - 9 / 10))
theorem KLinst_indStep (hpin : KLindStepPin) (hPT : KLPT 3 1 1) (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℝ, 0 < C ∧ ∑ b : Zd 3 5, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin 3 → Zd 3 5 => δ 0 = b), KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ δ * ∏ i ∈ Finset.univ.erase 0, thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (KLinstσ i) (KLinstσ (i + 1)) (KLinsta i) (δ i)‖ ≤ C * (5 : ℝ) ^ τ * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 2)
$ python3 clash.py   # name-clash grep of the new public names
new public names in the probe: 101 (prefix KL); files of RBM3D outside Probe/ mentioning any of them: 0; KL-identifiers already in RBM3D outside Probe/: ['KLoopBound']
$ python3 ports.py   # ports from RBM2D (read-only), file:line at c9a24cf
RBM2D/Loop/Kcal.lean @c9a24cf (probe <- RBM2D line): KLwholeP<-wholeP:82 KLInArc<-InArc:86 KLArcLe<-ArcLe:92 KLarcWidth<-arcWidth:98 KLnodes<-nodes:101 KLmem_nodes_of_mem<-mem_nodes_of_mem:106 KLminNode<-minNode:110 KLminNode_mem_or<-minNode_mem_or:113 KLleafPar<-leafPar:121 KLnodePar<-nodePar:125 KLleafPar_mem<-leafPar_mem:128 KLnodePar_mem<-nodePar_mem:133 KLleafPar_empty<-leafPar_empty:140 KLtreeValW<-treeValW:169 KLtreeValG<-treeValG:177 KLn<-Kn:183 KLgen<-Kgen:193 KLK<-Kcal:203 KLloopOf<-loopOf:207 KLFlong<-Flong:248 KLTSPlong<-TSPlong:253 KLsum_TSPlong<-sum_TSPlong:257 KLKpi<-Kpi:269 KLselfW<-selfW:275 KLSigmaPi<-SigmaPi:289 KLmaxDist<-maxDist:314 KLsigAlt<-sigAlt:372 KLtreeValW_empty<-treeValW_empty:419 KLn_cast<-Kn_cast:390 KLgen_loopOf<-Kgen_loopOf:402 KLtreeValW_eq_sum_selfW<-treeValW_eq_sum_selfW:436 KLK_three<-Kcal_three:466 KLward_two<-WI_calK_two:528 KLK_two<-Kcal_two:708 KLK_eq_sum_Kpi<-Kcal_eq_sum_Kpi:733 KLKpi_eq_sum_SigmaPi<-Kpi_eq_sum_SigmaPi:745
RBM2D/Loop/Unique.lean @c9a24cf (probe <- RBM2D line): KLretire_twoLoopBounded<-Unique_two_loop_bound:254
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log --format='%h %s' c9a24cf..HEAD -- RBM2D/Loop/Kcal.lean RBM2D/Loop/Unique.lean | cut -c1-100; git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/Kcal.lean RBM2D/Loop/Unique.lean
99d6fe0 T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)
 RBM2D/Loop/Kcal.lean   | 226 -------------------------------------------------
 RBM2D/Loop/Unique.lean |   2 -
 2 files changed, 228 deletions(-)
$ python3 consumers.py   # where the stochastic layer uses the K-loop statements (file[stage]:line)
eq:bcal_k (ML:Kbound) :: 1_2 [sec:tools]:1051; 3_5 [Steps3-4]:999,1056,1386; 6 [Sec:Step6]:79; B [subsec:pf-LWterm_EXP]:42,66
wardineq_K :: 3_5 [Steps3-4]:1056,1078
WI_calK (lem_WI_K) :: 1_2 [sec:tools]:1032; 3_5 [Steps1-2]:640; 3_5 [Steps3-4]:907,1267,1471,1869; 3_5 [Step5]:2136,2257; 6 [Sec:Step6]:104; B [subsec:pf-LWterm_EXP]:66
Kn2sol,Kn3sol :: 1_2 [Proof of the main results]:1228; 3_5 [Steps1-2]:131,455,519; 7_8 [sec:ext-to-BA]:1835,2002,2090
K2 decay by prop:ThfadC :: 3_5 [Steps1-2]:875
K decay (lem_decayLoop) :: 3_5 [Steps3-4]:1123
eq_Ktree,K-Kpi,K-pi-bound,molecule-Kpi,res_pureKes :: no reference outside A_deterministic_estimates.tex
$ python3 inv.py   # item 1
== RBM3D/Loop/*.lean (main@3c11d7b): lines, #theorem #def, Prop-valued defs with their own binders (section variables d L W g come first) [borrowed|owed = assumed premises, Test/Axioms.lean; structural = defines objects; unreg = in none of the three lists], all public names (* = def)
GLoop       293L  8thm  5def | Prop: - | Eblk*, Eblk_apply, Eblk_isHermitian, etaT*, etaT_eq_zt_im, etaT_pos, Gsig*, gloop*, loopMax*, gsigEblk_apply, norm_Gsig_entry_le, norm_prod_entry_le, norm_gloop_le
KBound      154L  2thm  1def | Prop: KLoopBound (K : ℝ → LoopIdx (Zd d L) → ℂ) [owed] | KLoopBound*, inv_pow_pair_le, not_inv_pow_pair_le_single
Partition   281L 15thm 17def | Prop: IsDiag (n : ℕ) (i j : Fin n) [structural], Crossing {n : ℕ} (e f : Fin n × Fin n) [structural], CrossingFree {n : ℕ} (F : Finset (Fin n × Fin n)) [unreg] | IsDiag*, diagonals*, Crossing*, CrossingFree*, TSP*, crossing_comm, not_crossing_self, mem_TSP, empty_mem_TSP, TSP_three, TSP_four, card_TSP_five, noncrossing_split, isDiag_split_lt, reindexR*, leftPairs*, rightPairs*, length_leftPairs_le, length_rightPairs_le, thetaEdge*, thetaEdge_comm, starGamma*, polyVal*, bdList*, treeVal*, diagList*, treeSum*, GammaN*, GammaSum*, treeVal_nil_eq_polyVal, treeVal_four_nil, GammaSum_eq_sum
Primitive   159L  9thm  2def | Prop: - | kTwo*, Theta_zero, norm_mul_lt_one, hasDerivAt_kTwo, kTwo_zero, kTwoLoop*, hasDerivAt_kTwoLoop, kTwoLoop_zero, kTwoFormula_kTwoLoop, norm_kTwo_le, pureLoop_two_kTwoLoop
PureLoop    290L  5thm  1def | Prop: KTwoFormula (m : Bool → ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) [unreg] | norm_Theta_same_le_exp, sum_exp_decay_conv, sum_exp_decay_centre, norm_sum_prod_le, KTwoFormula*, pureLoop_two
TreeFour    252L  8thm  0def | Prop: - | treeEqRhs_four, treeVal_four_diag02, treeVal_four_diag13, treeSum_four, hasDerivAt_thetaEdge_sub_one, hasDerivAt_starFour, treeVal_four_diag02_as_star, treeVal_four_diag13_as_star
TreeRep     221L  8thm 10def | Prop: IsKLoop (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) [structural], TwoLoopBounded (K : ℝ → LoopIdx (Zd d L) → ℂ) [owed], KTreeRep (m : Bool → ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) [borrowed] | LoopIdx*, WF*, length*, cutGlueL*, cutGlueR*, length_cutGlueL, length_cutGlueR, length_cutGlueL_add_length_cutGlueR, length_cutGlueL_le, length_cutGlueR_le, wf_cutGlueL, wf_cutGlueR, treeEqRhs*, MLoop*, IsKLoop*, TwoLoopBounded*, KTreeRep*, treeEqRhs_two
TreeThree   473L 12thm  2def | Prop: - | treeEqRhs_three, treeVal_three_nil, treeSum_three, kThree*, kThree_zero, sum_sum_mul_SB, sum_SB_starLeft, sum_SB_starRight, hasDerivAt_starThree, hasDerivAt_kThree, kLoop3*, exists_eq_of_length_three, kThree_eq_of_isKLoop, pureLoop_three
Unique      355L 14thm  2def | Prop: - | two_le_length_cutGlueL, two_le_length_cutGlueR, length_cutGlueR_eq_two, length_cutGlueL_eq_two, LoopVec*, LoopVec.toLoop*, LoopVec.wf, LoopVec.length, LoopVec.exists_toLoop, norm_SB_apply_le, norm_mul_mul_sub_le, eq_on_level, isKLoop_unique, exists_eq_of_length_two, kTwoFormula_of_isKLoop, pureLoop_two_of_isKLoop
-- merged names the probe code references (textual match, comments removed): GLoop: etaT | KBound: KLoopBound | Partition: diagonals, TSP, TSP_three, thetaEdge | Primitive: kTwo | PureLoop: sum_exp_decay_centre, KTwoFormula | TreeRep: LoopIdx, WF, length, treeEqRhs, IsKLoop, TwoLoopBounded, KTreeRep | TreeThree: kThree, kThree_eq_of_isKLoop | Unique: LoopVec, LoopVec.exists_toLoop, kTwoFormula_of_isKLoop
== RBM2D/Loop/*.lean at c9a24cf (16475 lines): lines, public thm/def, token counts, class a/b/c/d, main theorems
Cyclic        622L  2thm  0def | Z2=98 zd2=0 sq=6 P56=0 log=0 ell=0 | (a) | Kcal_rotate, Kcal_translate
KBound        577L  4thm  3def | Z2=17 zd2=1 sq=69 P56=28 log=0 ell=34 | (a) induction; (b) Xt/Mt -> B_t0 | Kpi_step, Kpi_bound_prec, Kbound_prec, Kbound_prec_uncond
KBoundCut    2138L  8thm 10def | Z2=169 zd2=0 sq=0 P56=0 log=0 ell=0 | (a) | Kpi_cut
KBoundEmpty  1736L  3thm  0def | Z2=99 zd2=71 sq=194 P56=30 log=2 ell=50 | (c) log-critical sums, Prop6Hyp | Kpi_empty_prec
KBoundInner  1239L  3thm  0def | Z2=57 zd2=63 sq=119 P56=33 log=21 ell=92 | (c) localisation, sum_inv_sq | innerId_sum_prec
Kcal          822L 15thm 42def | Z2=90 zd2=8 sq=35 P56=6 log=0 ell=13 | (b) defs (a); Par/Prop5Hyp/Prop6Hyp/Mt (c)(d) | Kcal_three, WI_calK_two, Kcal_two, Kcal_eq_sum_Kpi, Kpi_eq_sum_SigmaPi
LatticeCount  344L  4thm  0def | Z2=28 zd2=45 sq=23 P56=0 log=4 ell=0 | (c) d=2 counts | sum_inv_sq_le
Molecule      202L  4thm  2def | Z2=16 zd2=0 sq=9 P56=0 log=0 ell=21 | (a) innerId; (c) Xt | innerId_eq_sum
PropHyp       169L  2thm  0def | Z2=0 zd2=24 sq=40 P56=12 log=8 ell=18 | (d) not needed | prop5Hyp_holds, prop6Hyp_holds
PureLoop      934L  2thm  0def | Z2=39 zd2=77 sq=68 P56=17 log=0 ell=14 | (b) Prop5Hyp -> KLShort, zdist2 -> zdistD | SigmaPi_empty_shortRange_prec, Kcal_pure_prec
SumAll        788L  1thm  0def | Z2=32 zd2=0 sq=107 P56=0 log=0 ell=0 | (b) W^2 eta_t -> W^d eta_t | Kcal_sumAll_le
SumZero       914L 14thm  4def | Z2=72 zd2=0 sq=60 P56=0 log=0 ell=0 | (b) L^2 -> L^d | sum_Kpi_closed
SumZeroWard  2085L  6thm  1def | Z2=21 zd2=0 sq=73 P56=0 log=0 ell=0 | (a), laminar/cut API copied: public once | Qlayer_alt_one_eq_zero, SigmaPi_alt_sumZero_le
TreeRep      2587L  1thm  0def | Z2=188 zd2=0 sq=30 P56=0 log=0 ell=0 | (a) | isPrimitive_Kcal
Unique        302L  1thm  0def | Z2=32 zd2=0 sq=4 P56=0 log=0 ell=0 | (a) | isPrimitive_eq_Kcal
Ward         1016L  1thm  0def | Z2=155 zd2=0 sq=28 P56=0 log=0 ell=0 | (a) | Kcal_ward
$ python3 ext.py   # extreme inputs: t -> 1, lambda -> 0, L large, g = gmax (output of the script as committed)
bcal   max|K^(n)|/(W^-d B0)^(n-1), W=1, 41 configs x all sigma, (L,g,1-t,E) in [(17, 0.5, 1e-06, 0), (17, 0.05, 1e-06, 0), (17, 0.5, 1e-06, 1.7), (17, 1.0, 0.1, 0), (17, 1.0, 1e-06, 0)]:  {2: 1.534, 3: 2.224, 4: 4.248}
ward   WI_calK max rel. error, n=3,4, (L,g,1-t,E) in [(9, 0.05, 1e-06, 0), (9, 0.05, 1e-06, 1.7), (9, 1.0, 1e-06, 0)]: 7e-10
short  prop:ThfadC_short, L=33, (E,g,1-t)=(0,.05,1e-6),(0,1,1e-6),(0,2,1e-6),(1.7,.5,1e-6): fitted rate c of max_{|x|=k}|Theta|/g^2, k=1..6: ['5.79', '1.01', '0.64', '1.38']
szero  eq:Sigma-empty-sum-zero, n=4 alternating, L=17, (E,g,1-t) in (0,.5,1e-6),(1.7,.5,1e-6),(0,.05,1e-6),(0,1,1e-6): max l1/(g^2+1-t) = 12.94, max |signed|/(1-t) = 1.802, |signed - closed form| <= 1e-15
ind    eq:ind-step-bound n=4, sigma=(+,-,+,-), root leaf 0, max over 150 configs (a_i within 2 of 0) of sum_x|inner|/B0^2: ['L=9,E=0,g=0.5,1-t=1e-06: 2.91', 'L=17,E=0,g=0.5,1-t=1e-06: 2.88', 'L=33,E=0,g=0.5,1-t=1e-06: 2.42', 'L=17,E=0,g=0.05,1-t=1e-09: 1.51', 'L=17,E=1.7,g=0.5,1-t=1e-06: 8.52', 'L=17,E=0,g=1,1-t=1e-06: 7.33']
bd     L=17 g=1 1-t=1e+00: |r|<=0.5|a|: BD1 0.00 BD2 0.00; |r|<=1.0|a|: BD1 46.10 BD2 48.29; Theta0 2.00; ThfadC(c_d=1/4) 2.00
bd     L=17 g=1 1-t=1e-06: |r|<=0.5|a|: BD1 2.76 BD2 7.77; |r|<=1.0|a|: BD1 39.21 BD2 42.14; Theta0 1.68; ThfadC(c_d=1/4) 1.42
bd     L=17 g=0.5 1-t=1e-06: |r|<=0.5|a|: BD1 0.99 BD2 2.78; |r|<=1.0|a|: BD1 14.00 BD2 15.05; Theta0 0.60; ThfadC(c_d=1/4) 1.42
bd     L=65 g=1 1-t=1e+00: |r|<=0.5|a|: BD1 0.00 BD2 0.00; |r|<=1.0|a|: BD1 190.02 BD2 192.06; Theta0 2.00; ThfadC(c_d=1/4) 2.00
bd     L=65 g=1 1-t=1e-06: |r|<=0.5|a|: BD1 2.82 BD2 7.74; |r|<=1.0|a|: BD1 166.42 BD2 176.77; Theta0 1.74; ThfadC(c_d=1/4) 1.44
bd     L=65 g=0.5 1-t=1e-06: |r|<=0.5|a|: BD1 1.01 BD2 2.76; |r|<=1.0|a|: BD1 59.44 BD2 63.13; Theta0 0.62; ThfadC(c_d=1/4) 1.43
kpi    eq:K-pi-bound n=4, every sigma and pi in {empty,{(0,2)},{(1,3)}}, 41 configs, (L,g,1-t,E) in (17,.5,1e-6,0),(17,.05,1e-6,0),(17,.5,1e-6,1.7),(17,1,1e-6,0): max |K^(pi)|/B0^3 = 1.779
wardineq  max_sigma sum_{a_n}|K^(n)| W^d eta_t/(W^-d B0)^(n-2), W=1, 21 configs, same grid as kpi: {3: 0.504, 4: 0.934}
pure   lem_pureloop: max |K^(n)| W^{d(n-1)} exp(c max|a_i-a_j|), c=1/4, sigma=(s,..,s), s=+-, a_i on a line, L=17, (g,1-t,E) in (.05,1e-6,0),(1,1e-6,0),(.5,1e-6,1.7): {3: 1.139, 4: 1.467}
ode    pro_dyncalK: max_sigma rel. residual |(K(t+h)-K(t-h))/2h - RHS(K(t))|/max|RHS|, W=2, d=3, h=(1-t)/1000: ['(g,1-t,E)=(0.05,1e-06,0): n=3 (L=5) 2.0e-06, n=4 (L=3) 3.9e-06', '(g,1-t,E)=(1,1e-06,0): n=3 (L=5) 2.8e-06, n=4 (L=3) 4.0e-06', '(g,1-t,E)=(0.5,1e-03,1.7): n=3 (L=5) 1.8e-06, n=4 (L=3) 3.2e-06']
$ grep -E '^(DEF|ROW|OLD|PT|BA) ' RBM3D/Probe/T2004Pins.lean   # items 2, 4, 6, 7
DEF Choice: option B (RBM2D's, ROUTES row P6). KLK is the tree sum (eq_Ktree) (KLn, KLgen); (pro_dyncalK) with (calGonIND), (eq:initial_K) and K^(1) = m is the theorem KLisKLoopPin; uniqueness is KLuniquePin.
DEF Cost of B: KL3 (the ODE for the tree sum, about 1000 lines) and KL4 (uniqueness) only; (Kn2sol), (Kn3sol), (eq_K-Kpi) hold by definition (compiled here: KLK_two, KLK_three, KLK_eq_sum_Kpi).
DEF Cost of A (K := the unique solution of IsKLoop, chosen by Classical.choose): the same two theorems are needed (existence is KLisKLoopPin) and every bound still runs through the tree sum; A = B plus an indirection, and (Kn2sol), (Kn3sol), (eq_K-Kpi) become theorems.
DEF Retired: KTreeRep (borrowed; Test/Axioms.lean:75; no theorem takes it) by the definition; TwoLoopBounded (owed; Axioms.lean:85,121; premise of Unique.lean:297,344 and TreeThree.lean:350,411) by KLretire_twoLoopBounded (compiled; continuity on [0,t] in [0,1)); KLoopBound (owed; Axioms.lean:85; no theorem takes it) by KLretire_KLoopBound from the pins KLBoundAt (compiled).
ROW id | file under RBM3D/Loop/ (est. lines) | statements | RBM2D source at c9a24cf | d >= 3 changes | PT pins | start | role, risk
ROW KL1 | KLTree.lean (1150) | laminar API, KLK, KLKpi, KLSigmaPi, (Kn2sol), (Kn3sol), (eq_K-Kpi), molecule 1st stage, WI n=2, SigmaPi_empty_symm | TreeRep.lean:179-540; Kcal.lean:77-210,243-293,376-571,704-778 | Z2 L->Zd d L, W^2->W^d, Theta d L g, m=mSigma E; prod m inside KLKpi, KLSigmaPi (RBM2D: outside); drop Par/Prop5Hyp/Prop6Hyp/Mt | none | now | prover (probe sections 1-5 are the draft), low
ROW KL2 | KLCut.lean (1100) | cut at an internal edge, cut bijection sum_cut (shared by KL3, KL7, KL11) | TreeRep.lean:545-1674 (private copies: KBoundCut.lean:78-1521, SumZeroWard.lean:44-936) | Z2->Zd d L only; public once | none | after KL1 | prover-max, med
ROW KL3 | KLTreeDeriv.lean (1000) | KLisKLoopPin: d/dt of the tree sum = one term per edge; (k,l) classification; initial value | TreeRep.lean:1675-2587 | W^2->W^d in primRhs; (W^d)^-(n'-1) (W^d)^-(n''-1) W^d = (W^d)^-(n-1); dTheta merged (Propagator/Deriv.lean:108) | none | after KL2 | prover-max, med
ROW KL4 | KLUnique.lean (400; one ticket with KL5) | KLuniquePin; TwoLoopBounded dropped (KLretire_twoLoopBounded) | Unique.lean:250-302 | none (merged Loop/Unique.lean:247 isKLoop_unique) | none | after KL3 | prover, low
ROW KL5 | KLCyclic.lean (600; in the KL4 ticket) | Kcal_rotate, Kcal_translate | Cyclic.lean:569,594 | W^2->W^d, Z_L^d | none | after KL4 | prover-max, low
ROW KL6 | KLWard.lean (950) | KLwardPin, every n, both charge orders | Ward.lean:969 (37-962); Kcal.lean:528 | W^2->W^d in primRhs, primInit, kappa_t=(2i W^d eta_t)^-1, c_t=(W^d(1-t))^-1; no L^2 enters; s = false needs the flip lemma KLK(!sigma) = conj KLK(sigma) (new, about 100 lines; RBM2D proves +..- only, and flips only Alayer, SumZeroWard.lean:1369-1395) | none (property 4 merged) | after KL5 | prover-max, med
ROW KL7 | KLSumAll/KLSumZero/KLSumZeroWard.lean (700+800+1100) | total-sum bound; closed forms of fully summed trees; Q(sigma_alt,empty)|_{t=1}=0 => signed sum-zero O(|1-t|) | SumAll.lean:749; SumZero.lean:357-400,700,802; SumZeroWard.lean:1921,2002 | L^2->L^d (SumAll.lean:361, SumZero.lean:139), W^2 eta_t->W^d eta_t; gap gapK(kappa) d-free (Kcal.lean:311) | none | after KL6, KL2 | prover-max x3, med
ROW KL8 | KLPure.lean (800; one ticket with KL9) | KLmoleculePin (eq:molecule-decay); KLpurePin (res_pureKes) optional: RBM2D's Kcal_pure_prec (PureLoop.lean:793) is unreached from the endpoints (RBM2D docs/reports/T2273-dead.md) and was deleted by T2274 (99d6fe0) | PureLoop.lean:747,793 | Prop5Hyp->KLShort (g^2 factor, explicit constants), zdist2->zdistD, merged sum_exp_decay_centre; both charges (merged pureLoop_two/three need 0 < Im m(sigma), DECISIONS 10 T2001i-k) | KLShort | after KL1, KL2 (ticket with KL9: after KL7) | prover-max, med
ROW KL9 | KLSigmaAbs.lean (500; one ticket with KL8) | KLsumZeroPin, 2nd estimate sum|Sigma^0| = O(g^2+|1-t|) | none ([RBSO1D] Claim 4.30 is cited by the paper; RBM1D, RBM2D have S^(B) fixed, i.e. g = 1) | derived: = |signed| + O(g^2), a non-all-equal pattern forces an off-diagonal short edge (5') | KLShort | after KL7 | prover-max, low-med
ROW KL10 | KLIndStep.lean (2 x 900) | KLindStepPin (eq:ind-step-bound): f0+f1+f2 split, sum-zero, AM-GM | template KBoundEmpty.lean:983-1108,1332-1407; KBoundInner.lean:1157 | new: BD1/BD2/Zero (range |r| <= c|a|, c < 1), lattice sums p in {d-2,d-1,d}, inv_pow_pair_le (merged KBound.lean:90) | KLPT (5,5',6,7,8) | after KL7 and the KL8+9 ticket | prover-max, opus on RETURN, HIGH
ROW KL11 | KLInduct.lean (1300) | Kpi_cut, Kpi_step, KLKpiBoundPin, KLboundPin (n>=4); n<=3 = probe section 6 | KBoundCut.lean:1522-2138; KBound.lean:316-577 | X_t^j->B_t0^j; (k-2)+(n''-1)=n-1 is d-free; Kpi_cut gains a factor of modulus 1 (prod m) | via KL10 | after KL2, KL10 | prover-max, med
ROW KL12 | KLWardIneq.lean (600) | KLwardIneqPin (induction as in KL11, base case KL10, property 4) | paper A:809-827; no RBM2D analogue (grep wardineq: none) | new | KLPT via KL10 | after KL10, KL11 | prover-max, med
ROW KL13 | KLDecay.lean (800), optional | decay of K for lem_decayLoop (3_5:1123-1131), not in the ticket's pin list | RBM2D Induction/KcalDecay.lean (913L), pin HierVocab.lean:224 | uses the exp factor of property 5 | KLDecay | after KL1 | prover-max, med
ROW KL14 | cleanup (150) | delete KTreeRep, TwoLoopBounded, KLoopBound; Test/Axioms.lean:75,85,121; Test/InterfaceShape.lean:575-595; compose KLboundPin with the PT proofs | - | - | PT proofs | last | prover, low (Lean deletions go through a ticket, TEAM 9.11)
OLD kept (the probe references them, last line of script inv): GLoop (etaT), Partition (diagonals, TSP, TSP_three, thetaEdge), Primitive (kTwo), PureLoop (sum_exp_decay_centre), TreeRep (LoopIdx, treeEqRhs, IsKLoop), Unique (LoopVec.exists_toLoop, kTwoFormula_of_isKLoop); the KL tickets add Unique.isKLoop_unique (KL4) and KBound.inv_pow_pair_le (KL10); KL14 deletes KTreeRep, TwoLoopBounded, KLoopBound.
OLD superseded (not imported by the KL files, left compiling): Partition list part (polyVal, bdList, treeVal, treeSum, GammaN, GammaSum), TreeThree, TreeFour (n = 3, 4 by hand, KL3 does every n; the probe touches TreeThree only in the check KLretire_kThree), PureLoop KTwoFormula and pureLoop_two (charge + only; KLpurePin has both charges).
PT KL1-KL13 can all start before the PT proofs merge: every PT input is a hypothesis (KLShort in KL8-9, KLPT in KL10-12, KLDecay in KL13); only KL14 needs the PT proofs. Tickets: 13 proof tickets (KL4+5 and KL8+9 merged, KL7 in three, KL10 in two) + optional KL13 + KL14, at most 15 (< 50, DECISIONS 9 O2).
BA carries over: KLtreeValW (generic leaf and edge weights), KL2 cut bijection, KL4 uniqueness (S^(B) = I there), KL11 induction skeleton, the shapes of (eq:bcal_k), (wardineq_K), (WI_calK).
BA changes: IsKLoop and treeEqRhs hard-wire SB d L g (TreeRep.lean:142-145) and MLoop: KL1 should state them once for a kernel S and initial data M (about 30 lines); (Kn2sol) becomes W^-d (Theta M^(s1,s2)) (1_2:1175), M^(s1,s2) 1_2:1070, M^(+,+)_ab = (M^(B)_ab)^2, M^(+,-)_ab = |M^(B)_ab|^2 (1_2:658-664); Ward uses sum_b |M^(B)_ab|^2 = 1 (lem:propM (2), 7_8:1869) instead of |m| = 1.
BA gate BA must add: lem:propM (translation invariance, Im m >~ 1, Combes-Thomas Mbound_AO/AO2, 7_8:1847-1912), the M-graph values Gamma_M (m-loop-tsp A:380, A:552) and the ODE proof of (eq:tree_rep2) A:594 (d/dt Theta = Theta M^(s,s') Theta, S = I), the BA sum-zero estimates ([RBSO1D] 4.29, 4.30), PT constants depending on lambda^-1 (1_2:1150), |E| <= e_lambda - kappa.

Narrative (numbers are taken or summed from the script output above).
1. Verdict: all eight items are delivered in `RBM3D/Probe/T2004Pins.lean` (branch t/T2004, commit 64b58eb): `lake build` and `lake env lean` exit 0 with 0 warnings; the 204 constants `RBM.Loop.KL*` use only the three standard axioms; 21 compiled instances `KLinst_*`; no sorry/admit/axiom/native_decide.
2. Item 1 (`inv`): RBM3D/Loop has 9 files (2478 lines); Prop-valued: `KTreeRep` (borrowed), `TwoLoopBounded` and `KLoopBound` (owed), `IsKLoop`, `IsDiag`, `Crossing` (structural), `CrossingFree`, `KTwoFormula` (unregistered). RBM2D/Loop at c9a24cf has 16 files, 16475 lines: class (c) (d = 2 sums, `log L`, `Prop6Hyp`) is KBoundEmpty + KBoundInner + LatticeCount = 3319 lines, replaced by the new d ≥ 3 estimate KL10; class (d) is PropHyp (169); the other 12987 lines are (a)/(b) ports (`Z2 L` to `Zd d L`, `W²` to `W^d`, `L²` to `L^d`; Molecule is mixed (a)/(c)).
3. Item 2: option B, the tree sum is the definition (`DEF` lines). `KTreeRep` disappears with the definition; `TwoLoopBounded` and `KLoopBound` are retired by the compiled `KLretire_*`; the four merged theorems that took `TwoLoopBounded` as a premise no longer need it (`KLretire_kTwoFormula`, `KLretire_kThree` compile; the other two take the same argument).
4. Items 3, 5: (Kn2sol), (Kn3sol), (eq_K-Kpi) and the first stage of (eq:molecule-Kpi) are proved (`KLK_two`, `KLK_three`, `KLK_eq_sum_Kpi`, `KLKpi_eq_sum_SigmaPi`); (WI_calK) is proved at n = 2 (both charge orders) and pinned for every n; (eq:bcal_k) is proved for n = 1, 2, 3 from `KLPT` (n = 2: `KLDecay`; n = 3: `KLDecay` and `KLShort`) and pinned for every n (`KLboundPin`). Scale: the loss is L^τ for every τ > 0, with constants chosen after (d, κ, g_max, n, τ) and before (L, W, g, E, t, σ, a); `KLBoundAt_prec` converts it to the paper's ≺ with N = (WL)^d.
5. `KLPT` is my formulation of `lem_propTH` (5), (5'), (6), (7), (8) with 0 < g ≤ g_max (g_max plays the 𝔡⁻¹ of DECISIONS §9 O1); it is local and is to be replaced by T2003's pins.
6. Extreme inputs (`ext`: 1−t = 1e-6 and 1e-9; g = 0.05, and g = g_max = 1 at 1−t = 1e-6 in every block; L from 3 to 65): bcal ≤ 4.248; ind ≤ 8.52 (2.91, 2.88, 2.42 at L = 9, 17, 33); kpi ≤ 1.779; wardineq ≤ 0.934; pure ≤ 1.467; szero l1/(g²+1−t) ≤ 12.94; ODE residual ≤ 4.0e-06; WI error ≤ 7e-10. The BD1/BD2 constants stay ≤ 7.77 for |r| ≤ |a|/2 but grow like L for |r| ≤ |a| (BD1 46.10 to 190.02 from L = 17 to 65 at g = 1, t = 0), so the pins carry c < 1 (T2004c, (a′) 1).
7. Consumers (`consumers`): the stochastic layer uses (eq:bcal_k) (Steps 3–4, Step 6, App. B), (wardineq_K) (lem:SEforLn), (WI_calK) (lem:newKLK, Steps 3–5, Step 6, App. B), (Kn2sol), (Kn3sol) (Steps 1–2, proof of the main results, BA extension), K^(2) decay (lem: EMn2_N, 3_5:875) and K decay (lem_decayLoop, 3_5:1123). (eq_Ktree), (eq_K-Kpi), (eq:molecule-Kpi), (eq:K-pi-bound), (res_pureKes) have no reference outside A.5, so `KLKpiBoundPin`, `KLpurePin`, `KLmoleculePin`, `KLsumZeroPin`, `KLindStepPin` are proof-internal pins.
8. Item 7: 13 proof tickets (KL4+5 and KL8+9 merged, KL7 in three, KL10 in two) + optional KL13 + cleanup KL14; KL1–KL13 can start before the PT proofs merge; KL10 (`KLindStepPin`, the new d ≥ 3 estimate) is the risk. The regimes 1−t ≷ g², g²/L², g²/L^d ((a) row 15) are not split in KL3–KL12 (the pins are uniform in t ∈ [0,1), B_{t,0} absorbs them); ℓ_t enters only through `KLDecay`. Limits: the pins for n ≥ 4 are statements; their instances take the pin and `KLPT 3 1 1` (other gates' pins) as hypotheses.

## (c) Verified Mathlib names (`#check` with `import RBM3D`: 27 of 27 found, 0 errors)
Finset.sum_fiberwise_of_maps_to, Finset.exists_min_image, Finset.prod_univ_sum, Fintype.sum_ite_eq', Fintype.piFinset_univ, Equiv.funUnique, IsCompact.exists_bound_of_continuousOn, continuousOn_pi, norm_le_pi_norm
Real.rpow_add', Real.one_le_rpow, Real.rpow_natCast, Real.rpow_mul, Real.rpow_le_rpow, Real.exp_le_one_iff, Nat.le_mul_of_pos_left, Nat.le_ceil, add_halves
inv_le_one_of_one_le₀, one_le_pow₀, pow_le_pow_left₀, div_nonpos_of_nonpos_of_nonneg, Complex.sub_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, List.ext_getElem, List.ofFn_succ

## (d) Open issues and paper-delta candidates
- T2004a (necessary hypothesis): the proof of `ML:Kbound` for n = 3 (A:673) cites only (prop:ThfadC); the sharp bound also needs (prop:ThfadC_short) (the short edge is summed with O(1), not 1/(1−t)); `KLBoundAt_three` uses `KLDecay` and `KLShort`.
- T2004b (necessary condition): `ML:Kbound` holds with constants uniform in g only for g ≤ g_max (paper: λ ≤ 𝔡⁻¹, (eq:WO) 1_2:363); (a) row 13: ratios 13.9, 223.6, 4071.7 at g = 10, n = 2, 3, 4; the pins carry g ≤ gmax and constants C(d, κ, gmax, n, τ).
- T2004c (necessary range): (prop:BD1), (prop:BD2) (1_2:1153, 1159) must read |r| ≤ c|a| with a fixed c < 1 (false at r = −a; block `bd`); constants depend on c. T2003's BD1/BD2 pins need the same range (dispatcher to check).
- T2004d (typo): t ∈ [0,1] in `Def_Ktza` (1_2:988–989) and in the definition of Θ_t (1_2:1072) is t ∈ [0,1): Σ_b Θ_t(0,b) = 1/(1−t), so Θ_1^{(+,−)} and 𝒦^{(2)} do not exist at t = 1, and η_1 = 0 in (WI_calK).
- T2004e (stronger form): the pins read ≺ as the loss L^τ for every τ > 0, uniformly in g ∈ (0, g_max], E in the bulk, t ∈ [0,1), σ, a; `KLBoundAt_prec` gives the paper's ≺ (N = (WL)^d) from it, not conversely.
- DECISIONS §9 O1 check list: `KLDecay` constants (C_d, c_d) depend on (d, gmax); `KLShort` (C_κ, c_κ) on (d, κ, gmax); `KLDiffOne`, `KLDiffTwo`, `KLZero` constants on (c, τ, d, gmax), (τ, d, gmax); all with 0 < g ≤ gmax; the `KLPT` shapes were tried in blocks `bd` (g = 1, 0.5; t = 0 and 1−t = 1e-6; L = 17, 65) and `short` (g = 0.05, 1, 2, 0.5; 1−t = 1e-6; L = 33).
- Not covered: `eq_Ward0`, `eq_Ward` (1_2:1018, 1025; resolvent identities, no 𝒦) are in ROUTES row KL but not among the ticket's targets; the pins for n ≥ 4 (`KLboundPin` and the route pins) are statements here; the split KL3–KL12 proves them.
