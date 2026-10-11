"""rem.py (T2402 1a): finite-size scaling of the BA remainder  KE_{uy} = t sum_{v in [u]} S_uv (E_u[(G_vv - m) G_uy] - M_uy (G_vv - m))  (the display remainder of the report: KE_uy = t sum_{k in [u]} S_uk ibpRem(u,k;y), ibpRem(u,k;y) = E_u[(G_kk - m) G_uy] - M_uy (G_kk - m)) and of ||G - M||_max,
model of ibp.py (d = 3, L = 3, flow data of stab.flow_point at L = 3, t = 0.9 t0), W = 2, 3, 4 (N = 216, 729, 1728).
Row u = site 0 is resampled by the Schur complement; E_u is the mean over the R inner draws (at fixed rest of X); KE is evaluated per draw; we report the RMS over draws and rests.
Usage: python3 rem.py g W_ nrest R"""
import sys, math, itertools
import numpy as np
import stab
g = float(sys.argv[1]); W_ = int(sys.argv[2]); nrest = int(sys.argv[3]); R = int(sys.argv[4])
d, L = 3, 3
ns = W_ ** d; nb = L ** d; N = nb * ns
rng = np.random.default_rng(777 + W_)
idx = list(itertools.product(range(L), repeat=d)); ix = {p: i for i, p in enumerate(idx)}
PsiB = np.zeros((nb, nb))
for p in idx:
    for i in range(d):
        for s_ in (1, -1):
            q = list(p); q[i] = (q[i] + s_) % L; PsiB[ix[p], ix[tuple(q)]] = 1
block = np.repeat(np.arange(nb), ns); same = block[:, None] == block[None, :]
def gue(t):
    X = np.zeros((N, N), complex)
    for a in range(nb):
        A = (rng.standard_normal((ns, ns)) + 1j * rng.standard_normal((ns, ns))) / math.sqrt(2 * ns)
        X[a * ns:(a + 1) * ns, a * ns:(a + 1) * ns] = math.sqrt(t) * (A + A.conj().T) / math.sqrt(2)
    return X
fp = stab.flow_point(g, L, w=1.2j if g < 10 else 1.0j)
g0, E, m0, t0 = fp['g0'], fp['E'], fp['m0'], fp['t0']
t = 0.9 * t0; z = E + (1 - t) * m0
D = g0 * np.kron(PsiB, np.eye(ns))
MB = np.linalg.inv(g0 * PsiB - (E + m0) * np.eye(nb)); M = np.kron(MB, np.eye(ns))
u = 0; keep = np.array([k for k in range(N) if k != u]); pos = {k: i for i, k in enumerate(keep)}
blk = np.where(same[u])[0]; others = [v for v in blk if v != u]
adj = int(np.where(PsiB[0] > 0)[0][0]) * ns
ys = {'y=u': u, 'y same block': others[0], 'y same offset adj block': adj, 'y other offset other block': 2 * ns + 1}
acc = {k: [] for k in ys}; dmax = []
for _ in range(nrest):
    X = gue(t); H = D + X
    Gfull = np.linalg.inv(H - z * np.eye(N)); dmax.append(np.abs(Gfull - M).max())
    Gu = np.linalg.inv(H[np.ix_(keep, keep)] - z * np.eye(N - 1))
    S1 = []; Gy = {k: [] for k in ys}
    done = 0
    while done < R:
        r_ = min(2000, R - done)
        Xr = np.zeros((r_, N - 1), complex)
        for v in others: Xr[:, pos[v]] = (rng.standard_normal(r_) + 1j * rng.standard_normal(r_)) * math.sqrt(t / ns / 2)
        Xuu = rng.standard_normal(r_) * math.sqrt(t / ns)
        r = Xr + D[u, keep]; rc = r.conj()
        b = r @ Gu; a = rc @ Gu.T
        s = Xuu - z - np.einsum('ik,ik->i', b, rc)
        s1 = (1 / s - m0)
        for v in others: s1 = s1 + Gu[pos[v], pos[v]] + a[:, pos[v]] * b[:, pos[v]] / s - m0
        S1.append(s1)
        for k, y in ys.items(): Gy[k].append((1 / s) if y == u else -b[:, pos[y]] / s)
        done += r_
    S1 = np.concatenate(S1)
    for k, y in ys.items():
        gy = np.concatenate(Gy[k]); A = np.mean(S1 * gy)
        f = t / ns * (A - M[u, y] * S1)
        acc[k].append(np.mean(np.abs(f) ** 2))
Wd = float(W_) ** (-d)
print(f"g={g:<8.4g} W={W_} N={N} t={t:.3f} kappa-proxy Im m0={m0.imag:.3f}  W^-d={Wd:.4e}  ||G-M||_max: mean over {nrest} rests = {np.mean(dmax):.4f}; x W^(d/2) = {np.mean(dmax) * W_ ** (d / 2):.3f}")
for k in ys:
    rms = math.sqrt(np.mean(acc[k])); print(f"    {k:<28s} RMS|KE| = {rms:.4e}   RMS|KE| / W^-d = {rms / Wd:.3f}   (|M_uy| = {abs(M[u, ys[k]]):.3f})")
