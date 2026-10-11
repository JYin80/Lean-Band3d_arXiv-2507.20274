"""ravg.py (T2402 1a): the non-scalar term R_uu = Delta_uu + m0 (YG)_uu = -sum_{v != u} M_uv (YG)_vu: pointwise size versus its block-offset average <R>_a = W^-d sum_o R_{(a,o),(a,o)}.
Model: d, L given, flow data of stab.flow_point (L, g given), t = 0.9 t0, X block-diagonal GUE with E|X_uv|^2 = t W^-d; one full inverse per sample (no inner Monte Carlo).
Also the exact algebra  Delta = -M Y G  (residual) and  R_uu = -sum_{v != u} M_uv (YG)_vu  (residual).  Output: RMS over samples and over u (pointwise), RMS over samples of <R>_0, in units of W^-d.
Usage: python3 ravg.py g d L W nsamp"""
import sys, math, itertools
import numpy as np
import stab
g = float(sys.argv[1]); d = int(sys.argv[2]); L = int(sys.argv[3]); W_ = int(sys.argv[4]); ns_ = int(sys.argv[5]); stab.d = d
ns = W_ ** d; nb = L ** d; N = nb * ns
rng = np.random.default_rng(99 + W_)
idx = list(itertools.product(range(L), repeat=d)); ix = {p: i for i, p in enumerate(idx)}
PsiB = np.zeros((nb, nb))
for p in idx:
    for i in range(d):
        for s_ in (1, -1):
            q = list(p); q[i] = (q[i] + s_) % L; PsiB[ix[p], ix[tuple(q)]] = 1
block = np.repeat(np.arange(nb), ns)
def gue(t):
    X = np.zeros((N, N), complex)
    for a in range(nb):
        A = (rng.standard_normal((ns, ns)) + 1j * rng.standard_normal((ns, ns))) / math.sqrt(2 * ns)
        X[a * ns:(a + 1) * ns, a * ns:(a + 1) * ns] = math.sqrt(t) * (A + A.conj().T) / math.sqrt(2)
    return X
fp = stab.flow_point(g, L, w=1.2j if g < 10 else 1.0j)
g0, E, m0, t0 = fp['g0'], fp['E'], fp['m0'], fp['t0']; t = 0.9 * t0; z = E + (1 - t) * m0
D = g0 * np.kron(PsiB, np.eye(ns)); MB = np.linalg.inv(g0 * PsiB - (E + m0) * np.eye(nb)); M = np.kron(MB, np.eye(ns))
pw = []; av = []; dm = []; res1 = 0.0; res2 = 0.0
for _ in range(ns_):
    X = gue(t); G = np.linalg.inv(D + X - z * np.eye(N)); Y = X + t * m0 * np.eye(N); YG = Y @ G; Dl = G - M
    res1 = max(res1, np.abs(Dl + M @ YG).max())
    R = np.diag(Dl) + m0 * np.diag(YG)
    off = M * (1 - np.eye(N))
    res2 = max(res2, np.abs(R + np.einsum('uv,vu->u', off, YG)).max())
    pw.append(np.mean(np.abs(R) ** 2)); av.append(abs(R[block == 0].mean()) ** 2); dm.append(np.abs(Dl).max())
Wd = float(W_) ** (-d)
print(f"g={g:<8.4g} d={d} L={L} W={W_:<3d} N={N:<5d} algebra residuals {res1:.1e} {res2:.1e}  ||Delta||_max={np.mean(dm):.4f}  W^-d={Wd:.3e}  RMS|R_uu|/W^-d = {math.sqrt(np.mean(pw)) / Wd:.3f}  RMS|<R>_a|/W^-d = {math.sqrt(np.mean(av)) / Wd:.3f}  ratio avg/pointwise = {math.sqrt(np.mean(av) / np.mean(pw)):.3f}  (1/sqrt(W^d) = {W_ ** (-d / 2):.3f})")
