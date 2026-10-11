"""disp.py (T2402 1a): Monte Carlo check of the exact row-u Stein display of the report, at fixed rest of X, resampling only row u (E_u):
      E_u[(Y G)_{uy}] = - t sum_{k in [u]} S_uk E_u[(G_kk - m) G_uy],   Y = X + t m,   S_uk = W^-d 1([k]=[u]),  all y (y = u and y != u).
Model: d = 3, L and W given, H = D + X, D = g0 Psi (x) I_{W^d}, X block-diagonal GUE (E|X_uv|^2 = t W^-d, X_uu real), z = E + (1-t) m0, flow data of stab.flow_point at L = 3, t = 0.9 t0.
Row u = site 0 is drawn from its law by the Schur complement (G^{(u)} fixed): s = X_uu - z - r G^{(u)} r^*, G_uu = 1/s, G_uy = -(r G^{(u)})_y / s, G_vy = G^{(u)}_vy + a_v b_y / s (a = G^{(u)} r^*, b = r G^{(u)}).
Reports, per g and y-type, the signed Monte Carlo mean of LHS - RHS, its standard error and the z-scores of the real and imaginary parts; and, for contrast, the mean of LHS alone.
Usage: python3 disp.py W nchunk chunk seed L g1,g2,.. t   (t = 0.9t0 or a number, e.g. 0.5)"""
import sys, math, itertools
import numpy as np
import stab
W_ = int(sys.argv[1]); NCH = int(sys.argv[2]); CH = int(sys.argv[3]); seed = int(sys.argv[4])
L = int(sys.argv[5]); GS = [float(x) for x in sys.argv[6].split(",")]; TT = sys.argv[7]   # TT = "0.9t0" or a number
d = 3
ns = W_ ** d; nb = L ** d; N = nb * ns
rng = np.random.default_rng(seed)
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
print(f"L={L} W={W_} N={N} t={TT} draws of row u per g: {NCH * CH}   (columns: y-type | mean LHS | mean(LHS-RHS) | SE | z_Re z_Im)")
for g in GS:
    fp = stab.flow_point(g, L, w=1.2j)      # w = 6/5 i = wI of BA/MFixedPoint.lean:849
    g0, E, m0, t0 = fp['g0'], fp['E'], fp['m0'], fp['t0']
    t = 0.9 * t0 if TT == '0.9t0' else float(TT); z = E + (1 - t) * m0
    print(f"flow data g={g:g}: g0={g0:.6f} E={E:.6f} m0={m0:.6f} |m0|={abs(m0):.4f} Im m0={m0.imag:.4f} t0={t0:.4f}; t={t:.4f} Im z_t={z.imag:.4f}")
    D = g0 * np.kron(PsiB, np.eye(ns)); H = D + gue(t)
    u = 0; keep = np.array([k for k in range(N) if k != u]); pos = {k: i for i, k in enumerate(keep)}
    Gu = np.linalg.inv(H[np.ix_(keep, keep)] - z * np.eye(N - 1))
    blk = np.where(same[u])[0]; others = [v for v in blk if v != u]
    ys = [('y=u', u), ('y in [u], y!=u', others[0]), ('same offset, adjacent block', int(np.where(PsiB[0] > 0)[0][0]) * ns),
          ('other offset, other block', 2 * ns + 3)]
    S1 = {k: [0j, 0j, 0.0, 0.0, 0.0] for k, _ in ys}; n = 0       # sums: lhs, diff, |Re diff|^2, |Im diff|^2, count
    for _c in range(NCH):
        Xr = np.zeros((CH, N - 1), complex)
        for v in others: Xr[:, pos[v]] = (rng.standard_normal(CH) + 1j * rng.standard_normal(CH)) * math.sqrt(t / ns / 2)
        Xuu = rng.standard_normal(CH) * math.sqrt(t / ns)
        r = Xr + D[u, keep]; rc = r.conj()
        b = r @ Gu; a = rc @ Gu.T
        s = Xuu - z - np.einsum('ik,ik->i', b, rc); Guu = 1 / s
        Gd = {u: Guu}
        for v in others: Gd[v] = Gu[pos[v], pos[v]] + a[:, pos[v]] * b[:, pos[v]] / s
        for k, y in ys:
            Guy = Guu if y == u else -b[:, pos[y]] / s
            lhs = Xuu * Guy + t * m0 * Guy
            for v in others:
                Xuv = Xr[:, pos[v]]
                Gvy = (-a[:, pos[v]] / s) if y == u else (Gu[pos[v], pos[y]] + a[:, pos[v]] * b[:, pos[y]] / s)
                lhs = lhs + Xuv * Gvy
            rhs = -t / ns * sum((Gd[v] - m0) * Guy for v in blk)
            df = lhs - rhs
            S1[k][0] += lhs.sum(); S1[k][1] += df.sum(); S1[k][2] += (df.real ** 2).sum(); S1[k][3] += (df.imag ** 2).sum()
        n += CH
    for k, _ in ys:
        ml = S1[k][0] / n; md = S1[k][1] / n
        sre = math.sqrt(max(S1[k][2] / n - md.real ** 2, 0) / n); sim = math.sqrt(max(S1[k][3] / n - md.imag ** 2, 0) / n)
        print(f"g={g:<8.4g} t={t:.4f} Im z_t={z.imag:.3f} {k:<30s} |mean LHS|={abs(ml):.5f}  mean(LHS-RHS)={md.real:+.2e}{md.imag:+.2e}i  SE={sre:.1e},{sim:.1e}  z={md.real / sre:+.2f},{md.imag / sim:+.2f}")
