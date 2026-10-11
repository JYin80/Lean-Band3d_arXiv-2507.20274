"""inst5c.py (T2402 1a, part (ii)): the concrete nondegenerate data of the compiled instances of the G5c targets.
Part A (File 1, the display and the R-algebra): the merged one-point data `szP` of BA/CouplingWindow.lean:849-864 (d = 3, L = 4, W = 2, N = 512, lam = 10, flow point of z_S(4,10), w = 6/5 i),
   t = 1/2 (< 1; the identity needs t < 1, Im z_t > 0, not t <= t0), one GUE sample X (omega).  Prints the hypotheses of the display theorem and the exact identities Delta = -M Y G,
   Delta_uu = -m (YG)_uu + R_uu,  R_uu = -sum_{v != u} M_uv (YG)_vu,  and that R_uu, Delta_uu are non-zero.
Part B (File 2, the endpoint BAIBPDet): the sequence sz0 of Defs/Sizes.lean:260 (L = 4(n+1), W = (2(n+1))^5, lam = (2(n+1))^-6), flow_sz0 (kappa, eps, c, dd) = (1/2, 1/10, 1/6, 1/10), t = 1/2, eps0 = 1/10, Psi = W^-1, delta = W^-1:
   the deterministic hypotheses n = 0..3 (t0 from stab.flow_point at (lam_n, L_n, w = 6/5 i)).
Usage: python3 inst5c.py"""
import math, itertools
import numpy as np
import stab
stab.d = 3
d = 3
def model(L, W, g):
    ns = W ** d; nb = L ** d
    idx = list(itertools.product(range(L), repeat=d)); ix = {p: i for i, p in enumerate(idx)}
    PsiB = np.zeros((nb, nb))
    for p in idx:
        for i in range(d):
            for s_ in (1, -1):
                q = list(p); q[i] = (q[i] + s_) % L; PsiB[ix[p], ix[tuple(q)]] = 1
    return ns, nb, PsiB
print("Part A: d=3 L=4 W=2 (szP), g = lam = 10, t = 1/2")
L, W, g, t = 4, 2, 10.0, 0.5
ns, nb, PsiB = model(L, W, g); N = nb * ns
fp = stab.flow_point(g, L, w=1.2j); g0, E, m0, t0 = fp['g0'], fp['E'], fp['m0'], fp['t0']
z = E + (1 - t) * m0; s = E + m0
D = g0 * np.kron(PsiB, np.eye(ns)); MB = np.linalg.inv(g0 * PsiB - s * np.eye(nb)); M = np.kron(MB, np.eye(ns))
rng = np.random.default_rng(5); X = np.zeros((N, N), complex)
for a in range(nb):
    A = (rng.standard_normal((ns, ns)) + 1j * rng.standard_normal((ns, ns))) / math.sqrt(2 * ns)
    X[a * ns:(a + 1) * ns, a * ns:(a + 1) * ns] = math.sqrt(t) * (A + A.conj().T) / math.sqrt(2)
G = np.linalg.inv(D + X - z * np.eye(N)); Y = X + t * m0 * np.eye(N); Dl = G - M; YG = Y @ G
block = np.repeat(np.arange(nb), ns); offs = np.tile(np.arange(ns), nb); u = 0
S = (block[:, None] == block[None, :]) / ns
Ru = Dl[u, u] + m0 * YG[u, u]; Ru2 = -sum(M[u, v] * YG[v, u] for v in range(N) if v != u)
print(f"  flow data: g0={g0:.6f} E={E:.1e} m0={m0:.6f} |m0|={abs(m0):.4f} t0={t0:.4f} (t=1/2 > t0: outside the flow window, irrelevant for the identity); Im z_t={z.imag:.4f} > 0; 3 <= L: True")
print(f"  hypotheses: D Hermitian residual {np.abs(D - D.conj().T).max():.1e};  (D - s) M = 1 residual {np.abs((D - s * np.eye(N)) @ M - np.eye(N)).max():.1e};  M_uu = m0 residual {np.abs(np.diag(M) - m0).max():.1e};  z = s - t m0: {abs(z - (s - t * m0)):.1e}")
print(f"  S row sum sum_k S_uk = {S[u].sum():.12f}; S_uk = W^-d 1([k]=[u]) support {int((S[u] > 0).sum())} sites = W^d = {ns}; M_ku = 0 for k != u in [u]: max = {max(abs(M[k, u]) for k in range(N) if block[k] == block[u] and k != u):.1e}; M_uv != 0 only at the offset of u: {np.abs(M * (offs[:, None] != offs[None, :])).max():.1e}")
print(f"  identities: |Delta + M Y G|_max = {np.abs(Dl + M @ YG).max():.1e};  |Delta_uu + m0 (YG)_uu - R_uu| = {abs(Dl[u, u] + m0 * YG[u, u] - Ru2):.1e};  R_uu = {Ru:.5f}, Delta_uu = {Dl[u, u]:.5f}, ||Delta||_max = {np.abs(Dl).max():.4f} (all non-zero)")
print("\nPart B: sz0, n = 0..3: kappa=1/2, t=1/2, eps0=1/10, Psi=delta=W^-1, Kenv=B=1")
print("  n   L    W        size       lam       t0     1/2<=t0  delta<=k/2  W^-3/2<=Psi<=W^-eps0  size^-1<=Psi^2  (1/eta+1)^2<=size  Im m0   |m0|")
for n in range(4):
    Ln, Wn = 4 * (n + 1), (2 * (n + 1)) ** 5; lam = (2 * (n + 1.0)) ** -6; size = (Wn * Ln) ** 3
    fpn = stab.flow_point(lam, Ln, w=1.2j); t0n = fpn['t0']; m0n = fpn['m0']; eta = (1 - 0.5) * m0n.imag
    dl = Wn ** -1.0; Ps = Wn ** -1.0
    print(f"  {n}  {Ln:<3d} {Wn:<8d} {size:<10d} {lam:.3e} {t0n:.4f}  {0.5 <= t0n}      {dl <= 0.25}        {Wn ** -1.5 <= Ps <= Wn ** -0.1}              {size ** -1.0 <= Ps ** 2}            {(1 / eta + 1) ** 2 <= size}          {m0n.imag:.4f} {abs(m0n):.4f}")
