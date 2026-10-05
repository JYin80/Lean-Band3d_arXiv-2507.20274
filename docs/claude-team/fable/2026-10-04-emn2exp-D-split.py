#!/usr/bin/env python3
"""
T2118 review: the far sum S~3 of (eq:MG_conclusion3), d = 3, torus L^inf distance.

Profile (W^{-d} dropped, common factor):  P(m) = max(T(min(m,l)), F),  F = W^{-D} the floor,
T(rho) = B(rho) exp(-sqrt(rho/l_t)),  B(rho) = (g^2+u)^{-1}(rho+1)^{-(d-2)} + (L^d u)^{-1},  u = 1-t.
Region Reg (S~3):  l* < |c'-b| <= l,  l* < |c-a| <= l,  |c-c'| <= 1  (a = 0, r = |a-b| > l^dag).

Hoelder route of the preflight (all six legs by (Jhat+eps) P):  bound/target = u * H / P(r),
   H  = sum_{(c,c') in Reg} P(|b-c'|) P(|a-c|).
Split of this report:  A^n = {c' : P(|c'-b|) > P(r)}  (Hoelder, Jhat^3 term),
                       A^f = {c' : P(|c'-b|) <= P(r)} (contraction inequality, Bctl^{1/2} term, no sum).
   Hn = sum over Reg with c' in A^n;  Hf = H - Hn  (what the Hoelder route would need on A^f).
Reported: max over b with |b| > l^dag of  u*H/P(r),  u*Hn/P(r),  u*Hf/P(r).
The claim: u*Hn/P(r) is bounded by a constant depending on d only (TTT2 + sum T <= C/u, no floor-floor
term), while u*Hf/P(r) ~ u |Reg| F / P(r) grows like l^d when the floor F dominates on the region.
"""
import numpy as np, itertools, sys

def run(L, g, u, lstar, ldag, l, floors, d=3, rstep=1):
    lt = min(max(g/np.sqrt(u), 1.0), L)
    idx = np.indices((L,)*d).reshape(d, -1).T            # all sites
    dist = np.min(np.stack([idx % L, (-idx) % L]), axis=0).max(axis=1).astype(float)  # |x|_inf torus
    distgrid = dist.reshape((L,)*d)
    def B(rho): return 1.0/((g*g+u)*(rho+1.0)**(d-2)) + 1.0/(L**d*u)
    def T(rho): return B(rho)*np.exp(-np.sqrt(rho/lt))
    out = []
    for F in floors:
        P = lambda m: np.maximum(T(np.minimum(m, l)), F)
        # A(c) = 1[l* < |c-a| <= l] P(|a-c|), a = 0
        A = np.where((distgrid > lstar) & (distgrid <= l), P(distgrid), 0.0)
        # box convolution: conv(c') = sum_{|c-c'|<=1} A(c)
        conv = np.zeros_like(A)
        for sh in itertools.product((-1, 0, 1), repeat=d):
            conv += np.roll(A, sh, axis=tuple(range(d)))
        convhat = np.fft.fftn(conv)
        # full Hoelder sum H(b) = sum_{c'} Fr(b-c') conv(c'),  Fr(x) = 1[l*<|x|<=l] P(|x|)
        Ffull = np.where((distgrid > lstar) & (distgrid <= l), P(distgrid), 0.0)
        H = np.real(np.fft.ifftn(np.fft.fftn(Ffull)*convhat))
        ratios = []
        for r in range(int(np.floor(ldag))+1, L//2+1, rstep):
            Pr = P(float(r))
            Fn = np.where((distgrid > lstar) & (distgrid <= l) & (P(distgrid) > Pr), P(distgrid), 0.0)
            Hn = np.real(np.fft.ifftn(np.fft.fftn(Fn)*convhat))
            mask = (distgrid == r)
            if not mask.any(): continue
            ratios.append((r, u*H[mask].max()/Pr, u*Hn[mask].max()/Pr, u*(H-Hn)[mask].max()/Pr))
        rH = max(x[1] for x in ratios); rN = max(x[2] for x in ratios); rF = max(x[3] for x in ratios)
        # reference constants (floor-free): R0 = max_b u*sum_{Reg} T(|b-c'|)T(|a-c|)/T(r)  (the TTT2 shape),
        # R1 = 3^d * u * sum_c T(|c|)  (the bound of the W^{-D} sum_c T term); the split's Hoelder part
        # obeys u*Hn/P(r) <= R0 + R1 by the argument of the report, whatever the floor.
        A0 = np.where((distgrid > lstar) & (distgrid <= l), T(distgrid), 0.0)
        conv0 = np.zeros_like(A0)
        for sh in itertools.product((-1, 0, 1), repeat=d):
            conv0 += np.roll(A0, sh, axis=tuple(range(d)))
        H0 = np.real(np.fft.ifftn(np.fft.fftn(A0)*np.fft.fftn(conv0)))
        R0 = max(u*H0[distgrid == r].max()/T(float(r)) for r in range(int(np.floor(ldag))+1, L//2+1, rstep)
                 if (distgrid == r).any())
        R1 = 3**d * u * T(distgrid).sum()
        # where is the floor crossing rho_D (T(rho) = F) ?
        rhos = np.arange(0, L//2+1, dtype=float); cross = rhos[T(rhos) <= F]
        rhoD = cross[0] if len(cross) else np.inf
        nfloor = int(((distgrid > lstar) & (distgrid <= l) & (T(distgrid) <= F)).sum())
        out.append((F, rhoD, nfloor, rH, rN, rF, R0, R1))
        ok = "ok" if rN <= R0 + R1 + 1e-9 else "VIOLATED"
        print(f"  L={L:3d} u={u:g} l_t={lt:.2f} l*={lstar} ldag={ldag} l={l} F={F:7.1e} rho_D={rhoD:3.0f} "
              f"#floor c'={nfloor:6d} | Hoelder route u*H/P(r)={rH:8.1f} | split: u*Hn/P(r)={rN:7.1f} "
              f"<= R0+R1={R0:.1f}+{R1:.1f} {ok} ; u*Hf/P(r)={rF:8.1f} (= what Hoelder needs on A^f)")
    return out

if __name__ == "__main__":
    g = 0.5
    print("# S~3 sums on the torus, d=3, g=1/2; a=0, b ranges over |b|>l^dag; F=W^{-D} the floor.")
    print("# (i) fixed L=40, u=0.05, scan the floor: the Hoelder-route ratio grows when the floor")
    print("#     enters the region; the split's Hoelder part stays bounded.")
    run(40, g, 0.05, 4, 8, 19, [1e-6, 1e-3, 3e-3, 1e-2, 2e-2, 3e-2, 5e-2])
    print("# (ii) floor at the level of T(r) for r in the far zone, growing L with l = L/2-1 (l/l_t grows):")
    for L in (24, 32, 40, 48, 56):
        run(L, g, 0.05, 4, 8, L//2-1, [2e-2])
    print("# (iii) smaller u (l_t larger), the same picture:")
    for L in (32, 48, 64):
        run(L, g, 0.01, 6, 10, L//2-1, [1e-2, 4e-2])
    print("# (iv) regime u >= g^2 (l_t = 1): trivially fine, floor irrelevant")
    run(32, g, 0.5, 3, 6, 15, [1e-2, 1e-1])
    print("# (v) l_t = 1.12 (u = 0.2): L up to 160 so that the TTT2 sums (R0, R1) saturate (tail e^{-sqrt(rho/l_t)}")
    print("#     converges at rho ~ 100 l_t); r sampled every 8th value; Hf grows ~ l^d, Hn and R0+R1 saturate.")
    for L in (64, 96, 128, 160):
        run(L, g, 0.2, 3, 6, L//2-1, [1e-3, 3e-3], rstep=8)
