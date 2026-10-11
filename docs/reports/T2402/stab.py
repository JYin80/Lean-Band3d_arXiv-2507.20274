"""stab.py (T2390 1a, item (v)): the stability constant of the coupled system and the decay rate of M, d = 3, versus L.

Model data (as T2378 moff.py / inst2.py): Psi^(B) = adjacency of Z_L^3, w = 1.2 i, z = w - m_S(w), m solves (self_m),
t0 = Im m/(Im m + Im z), g0 = sqrt(t0) g, E = BAflowE, m0 = m/sqrt(t0), M^(B) = (g0 Psi - E - m0)^-1 (translation invariant).

Stability operator of the coupled system (derived in the report, section G.2):  B[Delta] = Delta - M S[Delta] M, S[R] = t sum_a <R>_a P_a.
Its solution map  K |-> Delta = B^-1[M K]  has the max-norm bound
    Kstab(t) = rho1 * (1 + t * rho2 * ||Theta_t||_{inf->inf}),   rho1 = sum_b |M_0b|,  rho2 = max_a sum_b |M_0b||M_ba|  (<= 1 by Ward + CS),
    Theta_t = (1 - t M o M)^-1  (Hadamard square, = BATheta d L g E m t true true, Prop5Short).
Usage: python3 stab.py table | scan   (both print compact tables)
"""
import sys, math, itertools
import numpy as np

d = 3

def grids(L):
    p = np.arange(L)
    P = np.meshgrid(*([p] * d), indexing='ij')
    psi = sum(2 * np.cos(2 * np.pi * x / L) for x in P)           # eigenvalues of the adjacency of Z_L^d
    q = np.minimum(p, L - p)                                       # periodic coordinate distance
    Q = np.meshgrid(*([q] * d), indexing='ij')
    dist = sum(Q)                                                  # l1 periodic distance (zdistD)
    return psi, dist

def solve_m(g, psi, z, m0=1j, it=60000, tol=1e-15):
    m = m0
    for _ in range(it):
        new = 0.5 * m + 0.5 * np.mean(1 / (g * psi - z - m))
        if abs(new - m) < tol:
            m = new
            break
        m = new
    return m

def flow_point(g, L, w=1.2j):
    psi, dist = grids(L)
    mS = np.mean(1 / (g * psi - w)); z = w - mS
    m = solve_m(g, psi, z)
    t0 = m.imag / (m.imag + z.imag)
    E = (t0 * z.real - (1 - t0) * m.real) / math.sqrt(t0)
    return dict(g=g, L=L, z=z, m=m, t0=t0, g0=math.sqrt(t0) * g, E=E, m0=m / math.sqrt(t0))

def stab_constants(g0, E, m0, L, ts):
    psi, dist = grids(L)
    Mh = 1 / (g0 * psi - E - m0)                                   # Fourier symbol of M^(B)
    M0 = np.fft.ifftn(Mh)                                          # M_{0b}
    out = {}
    out['selfres'] = abs(M0[(0,) * d] - m0)
    out['ward'] = abs(np.sum(np.abs(M0) ** 2) - 1)
    A = np.abs(M0)
    out['rho1'] = A.sum()
    conv = np.real(np.fft.ifftn(np.fft.fftn(A) * np.fft.fftn(A)))   # sum_b |M_0b||M_{0,a-b}|
    out['rho2'] = conv.max()
    sig = np.fft.fftn(M0 ** 2)                                      # symbol of M o M (Hadamard square)
    res = []
    for t in ts:
        den = 1 - t * sig
        gap = np.abs(den).min()
        Th = np.fft.ifftn(1 / den)
        th1 = np.abs(Th).sum()
        K = out['rho1'] * (1 + t * out['rho2'] * th1)
        res.append((t, gap, th1, K))
    out['res'] = res
    # decay of M_{0b}: shells of the periodic l1 distance
    shell = {}
    for s in range(1, dist.max() + 1):
        sel = (dist == s)
        if sel.any(): shell[s] = A[sel].max()
    out['shell'] = shell
    return out

def rate_from_shells(shell, smax=None):
    ks = sorted(k for k, v in shell.items() if v > 1e-300)
    if smax: ks = [k for k in ks if k <= smax]
    k0, k1 = ks[0], ks[-1]
    # empirical exponential rate (log-slope) from the first to the last shell, and the worst ratio |M| e^{c s}
    return (math.log(shell[k0]) - math.log(shell[k1])) / (k1 - k0)

def lean_rate(Lam, kappa):
    return min(math.log(1 + kappa / (4 * d * Lam)), kappa / 2)

def shell_rate(shell, L):
    """log-slope of the shell maxima mu(s) = max_{|b|_1 = s} |M_0b| over 2 <= s <= min(L//2, 40) (isotropic range of the torus), restricted to shells above the FFT noise floor 1e-11."""
    hi = min(L // 2, 40)
    ks = [s for s in range(2, hi + 1) if s in shell and shell[s] > 1e-11]
    if len(ks) < 2: return float('nan')
    return (math.log(shell[ks[0]]) - math.log(shell[ks[-1]])) / (ks[-1] - ks[0])

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'table'
    Lam = 10.0                                                      # = 1/dd, dd = 1/10
    if mode == 'table':
        print("columns: BAdom = (kappa <= Im m(z) and Im z <= 1); ward = max|sum_b|M_0b|^2 - 1|; dec = max_b |M_0b| / (c^-1 e^{-c|b|}) (BAMfine_decay needs <= 1)")
        print("K(t) = Kstab(t) = rho1 (1 + t rho2 ||Theta_t||_1); gap(t) = min_p |1 - t sigma(p)|; rate = observed log-slope of max_{|b|=s}|M_0b|; c = BAct_rate(3, 10, kappa)")
        for g, kap, w, Ls in [(1/64, 0.5, 1.2j, [4, 8, 16, 32, 64]), (1.0, 0.25, 1.2j, [4, 8, 16, 32, 64, 96]), (10.0, 0.04, 1.0j, [4, 8, 16, 32, 64, 128, 256])]:
            c = lean_rate(Lam, kap)
            print(f"--- g = {g:.6g}, w = {w.imag}i, kappa = {kap}, Lean c = {c:.6f} ---")
            for L in Ls:
                fp = flow_point(g, L, w=w)
                t0 = fp['t0']
                r = stab_constants(fp['g0'], fp['E'], fp['m0'], L, [t0 / 2, t0, 1.0])
                (_, g1, th1a, K1), (_, g2, th1b, K2), (_, g3, th1c, K3) = r['res']
                psi, dist = grids(L)
                M0 = np.fft.ifftn(1 / (fp['g0'] * psi - fp['E'] - fp['m0']))
                ratio = (np.abs(M0) / ((1 / c) * np.exp(-c * dist))).max()
                dom = fp['m'].imag >= kap and fp['z'].imag <= 1
                print(f"L={L:3d} BAdom={str(dom):5s} Imz={fp['z'].imag:.3f} Imm={fp['m'].imag:.4f} t0={t0:.4f} g0={fp['g0']:.4f} Imm0={fp['m0'].imag:.4f} ward={r['ward']:.0e} "
                      f"rho1={r['rho1']:7.2f} rho2={r['rho2']:.3f} K(t0)={K2:7.2f} K(1)={K3:8.2f} gap(t0)={g2:.3f} gap(1)={g3:.3f} Th1(1)={th1c:.3f} rate={shell_rate(r['shell'], L):.3f} dec={ratio:.0e}")
    elif mode == 'scan':
        # real-axis data (g0, E) with Im m0 >= kappa_thr: the worst stability data over an E grid, t = 1.
        # m(E+i0) is solved with the histogram of the eigenvalues of Psi^(B) (40000 bins), the constants with the full FFT.
        for g0 in [0.5610, 4.6723, 10.0]:
            for L in [32, 64]:
                psi, dist = grids(L)
                hist, edges = np.histogram(psi.ravel(), bins=40000, range=(-6.0001, 6.0001))
                cen = 0.5 * (edges[1:] + edges[:-1]); wgt = hist / hist.sum(); nz = wgt > 0; cen, wgt = cen[nz], wgt[nz]
                def msolve(E):
                    m = 1j
                    for _ in range(4000):
                        new = 0.5 * m + 0.5 * np.sum(wgt / (g0 * cen - E - m))
                        if abs(new - m) < 1e-14: m = new; break
                        m = new
                    for _ in range(30):                      # Newton polish with the exact spectrum
                        den = g0 * psi - E - m
                        f = np.mean(1 / den) - m; fp = np.mean(1 / den ** 2) - 1
                        step = f / fp; m = m - step
                        if abs(step) < 1e-15: break
                    return m
                Es = np.linspace(-1.95, 1.95, 40) if g0 < 1 else np.linspace(-5.5 * g0, 5.5 * g0, 56)
                data = []
                for E in Es:
                    m = msolve(E)
                    if m.imag < 0.02: continue
                    r = stab_constants(g0, E, m, L, [1.0])
                    data.append((m.imag, r['rho1'], r['res'][0][1], r['res'][0][2], r['res'][0][3], r['ward'], r['selfres']))
                for thr in [0.25, 0.1, 0.05]:
                    sel = [x for x in data if x[0] >= thr]
                    if not sel: print(f"g0={g0:<7} L={L:2d} kappa_thr={thr:<5} (no E with Im m0 >= thr)"); continue
                    print(f"g0={g0:<7} L={L:2d} kappa_thr={thr:<5} #E={len(sel):3d} max rho1={max(x[1] for x in sel):8.2f} min gap(1)={min(x[2] for x in sel):.3f} "
                          f"max ||Th||_1={max(x[3] for x in sel):.3f} max K(1)={max(x[4] for x in sel):9.2f} max ward err={max(x[5] for x in sel):.0e}")
