#!/usr/bin/env python3
"""
Numerical check of Lemma TailtoTail / estimate (neiwuj) of arXiv:2507.20274
(3_5_Loop_Hierarchy.tex, lines 2344-2362) in dimension d = 3.

Objects (paper's own definitions, random band matrix model, flow framework):
  S^{(B)}_{ab} = (1+2d g^2)^{-1} 1_{a=b} + g^2 (1+2d g^2)^{-1} 1_{a~b}      (eq:variancematrix)
  M^{(+,-)} = m(+)m(-) I = |m|^2 I = I  (|m(E+i0)| = 1 in the bulk)      (eq:Msig)
  Theta_t = (1 - t S)^{-1}                                                   (def_Thxi)
  (U^{(2)}_{s,t} o A)_{a1 a2} = sum_{b1 b2} P_{a1 b1} P_{a2 b2} A_{b1 b2},
       P = (1 - s S)(1 - t S)^{-1}                                           (def_Ustz)
  T_{u,D}(r) = (W^d |1-u|)^{-2} exp(-sqrt r) + W^{-D}                        (def_WTuD, line 2296)
  [team's reading] calT_u(r) = B_{u,r} exp(-sqrt(r/ell_u)),
       B_{u,r} = (g^2+|1-u|)^{-1} (r+1)^{-(d-2)} + (L^d |1-u|)^{-1}          (defTUL, eq_B_param)
  |a| = periodic l^infty distance on Z_L^d                                   (line 274-275)

Everything is translation invariant, so U o A for A_{b1 b2} = f(b1 - b2) is the
convolution P * P * f evaluated at a1 - a2; we compute it by FFT (exact up to
floating point) and cross-check against a dense construction for small L.

Since U has non-negative entries (P >= 0 entrywise), the extremal admissible tensor
is A = T_s(|b1-b2|) itself, so the FFT ratio is the exact worst case.
"""
import numpy as np
import itertools, sys

def lattice(L, d):
    """coordinates in the periodic representative [-L/2+1, L/2]^d and the l^inf, l^1 norms"""
    ax = np.arange(L)
    ax = np.where(ax > L // 2, ax - L, ax)  # periodic representative
    grids = np.meshgrid(*([ax] * d), indexing="ij")
    linf = np.max(np.abs(np.stack(grids)), axis=0)
    l1 = np.sum(np.abs(np.stack(grids)), axis=0)
    return linf, l1

def S_hat(L, d, g):
    p = 2 * np.pi * np.arange(L) / L
    grids = np.meshgrid(*([p] * d), indexing="ij")
    cs = sum(np.cos(G) for G in grids)
    return (1 + 2 * g**2 * cs) / (1 + 2 * d * g**2)

def P_hat(L, d, g, s, t):
    Sh = S_hat(L, d, g)
    return (1 - s * Sh) / (1 - t * Sh)

def conv_UU(f, Ph):
    """(P * P * f) as a function of a1 - a2, via FFT (P symmetric, real)"""
    fh = np.fft.fftn(f)
    return np.real(np.fft.ifftn(Ph**2 * fh))

def ell(L, g, u):
    return min(max(g / np.sqrt(abs(1 - u)), 1.0), L)

def B(L, d, g, u, r):
    return (g**2 + abs(1 - u)) ** (-1) / (r + 1) ** (d - 2) + 1.0 / (L**d * abs(1 - u))

def ratios(L, d, g, s, t, rs, Wd=None):
    """returns dict with the two readings of the tail function"""
    linf, l1 = lattice(L, d)
    Ph = P_hat(L, d, g, s, t)
    rho = (1 - s) / (1 - t)
    # sanity: row sum of P and nonnegativity (P(x) = inverse FFT of Ph)
    P = np.real(np.fft.ifftn(Ph))
    assert abs(P.sum() - rho) < 1e-9 * rho, (P.sum(), rho)
    assert P.min() > -1e-12, P.min()
    # (i) paper's T_{u,D} main part, amplitude (W^d(1-u))^{-2}: W^d cancels in the ratio
    f_s = (1 - s) ** (-2) * np.exp(-np.sqrt(linf))
    f_t = (1 - t) ** (-2) * np.exp(-np.sqrt(linf))
    UUf = conv_UU(f_s, Ph)
    # (ii) team's calT_u = B_{u,r} e^{-sqrt(r/ell_u)}
    g_s = B(L, d, g, s, linf) * np.exp(-np.sqrt(linf / ell(L, g, s)))
    g_t = B(L, d, g, t, linf) * np.exp(-np.sqrt(linf / ell(L, g, t)))
    UUg = conv_UU(g_s, Ph)
    out = {}
    for r in rs:
        idx = (r,) + (0,) * (d - 1)
        out[r] = (UUf[idx] / f_t[idx], UUg[idx] / g_t[idx])
    # also the max over all a of the paper-ratio
    out["max"] = (np.max(UUf / f_t), np.max(UUg / g_t))
    out["rho"] = rho
    out["ell_s"], out["ell_t"] = ell(L, g, s), ell(L, g, t)
    out["Pmin"], out["Pmax_off"] = P.min(), np.sort(P.ravel())[-2]
    out["Pdiag"] = P[(0,) * d]
    return out

def dense_check(L, d, g, s, t, r):
    """dense construction of U^{(2)} acting on 2-tensors, compare with FFT"""
    n = L**d
    pts = list(itertools.product(range(L), repeat=d))
    index = {p: i for i, p in enumerate(pts)}
    S = np.zeros((n, n))
    a0 = 1.0 / (1 + 2 * d * g**2)
    for p in pts:
        i = index[p]
        S[i, i] = a0
        for k in range(d):
            for sgn in (1, -1):
                q = list(p); q[k] = (q[k] + sgn) % L
                S[i, index[tuple(q)]] += g**2 * a0
    assert np.allclose(S.sum(1), 1)
    Theta = np.linalg.inv(np.eye(n) - t * S)
    P = (np.eye(n) - s * S) @ Theta
    assert P.min() > -1e-12
    assert np.allclose(P.sum(1), (1 - s) / (1 - t))
    def dist(p, q):
        return max(min((p[k] - q[k]) % L, (q[k] - p[k]) % L) for k in range(d))
    D = np.array([[dist(p, q) for q in pts] for p in pts])
    A_s = (1 - s) ** (-2) * np.exp(-np.sqrt(D))          # paper's T_{s,D} main part (W^d dropped)
    UA = P @ A_s @ P.T                                    # (U o A)_{a1 a2} = sum P_{a1 b1} P_{a2 b2} A_{b1 b2}
    T_t = (1 - t) ** (-2) * np.exp(-np.sqrt(D))
    R = UA / T_t
    a1 = index[(0,) * d]; a2 = index[(r,) + (0,) * (d - 1)]
    return R[a1, a2], R.max()

if __name__ == "__main__":
    d = 3
    print("=== dense vs FFT cross-check (d=3, L=6) ===")
    for (g, s, t) in [(0.01, 0.5, 0.99), (0.1, 0.5, 0.99), (0.3, 0.2, 0.9)]:
        L = 6
        rd, rmax = dense_check(L, d, g, s, t, 2)
        o = ratios(L, d, g, s, t, [2])
        print(f"g={g} 1-s={1-s:.2f} 1-t={1-t:.2f}: dense ratio r=2 {rd:.6f}, max {rmax:.6f} | FFT {o[2][0]:.6f}, max {o['max'][0]:.6f}")

    print()
    print("=== regime of the lemma: 1-s >= 1-t >= g^2 (ell_s = ell_t = 1) ===")
    print("columns: paper T_{u,D} ratio (U o T_s)(a)/T_t(|a1-a2|) at r=1,2,3,L/2 and max over a;"
          " then the same with the team's calT_u (B_{u,r} e^{-sqrt(r/ell_u)})")
    cases = [
        # (L, g, 1-s, 1-t)
        (16, 0.01, 0.5, 0.01),
        (16, 0.01, 0.1, 0.01),
        (16, 0.01, 0.02, 0.01),
        (16, 0.1, 0.5, 0.01),      # boundary 1-t = g^2
        (16, 0.1, 0.9, 0.01),
        (16, 0.1, 0.999, 0.01),    # s ~ 0
        (16, 0.1, 0.1, 0.01),
        (16, 0.3, 0.9, 0.09),      # boundary 1-t = g^2, moderate g
        (16, 0.3, 0.5, 0.09),
        (16, 0.5, 0.99, 0.25),     # boundary, g=1/2
        (16, 0.5, 0.5, 0.25),
        (16, 1.0, 1.0, 1.0),       # trivial t=s=0 -> identity
        (16, 0.01, 0.5, 0.0001),   # rho = 5000, 1-t = g^2
        (16, 0.001, 0.5, 1e-6),    # rho = 5e5, 1-t = g^2
        (32, 0.1, 0.5, 0.01),
        (32, 0.3, 0.9, 0.09),
        (64, 0.1, 0.5, 0.01),
        (64, 0.3, 0.9, 0.09),
    ]
    for (L, g, oms, omt) in cases:
        s, t = 1 - oms, 1 - omt
        if t <= 0: t = 0.0
        if s < 0: s = 0.0
        rs = [1, 2, 3, L // 2]
        o = ratios(L, d, g, s, t, rs)
        paper = " ".join(f"{o[r][0]:7.3f}" for r in rs) + f" | max {o['max'][0]:7.3f}"
        team = " ".join(f"{o[r][1]:9.2f}" for r in rs) + f" | max {o['max'][1]:9.2f}"
        print(f"L={L:2d} g={g:<5} 1-s={oms:<6} 1-t={omt:<7} rho={o['rho']:9.1f} ell_s={o['ell_s']:.2f} ell_t={o['ell_t']:.2f}\n"
              f"      paper T_{{u,D}}: {paper}\n"
              f"      team  calT_u : {team}   (rho={o['rho']:.1f})")

    print()
    print("=== OUTSIDE the lemma's hypothesis: 1-t < g^2 (ell_t > 1): paper's T_{u,D} ratio grows (expected) ===")
    for (L, g, oms, omt) in [(16, 1.0, 0.5, 0.01), (16, 1.0, 0.1, 0.01), (32, 1.0, 0.5, 0.01), (32, 1.0, 0.5, 0.001)]:
        s, t = 1 - oms, 1 - omt
        rs = [1, 2, 3, L // 2]
        o = ratios(L, d, g, s, t, rs)
        paper = " ".join(f"{o[r][0]:9.2f}" for r in rs) + f" | max {o['max'][0]:9.2f}"
        team = " ".join(f"{o[r][1]:9.2f}" for r in rs) + f" | max {o['max'][1]:9.2f}"
        print(f"L={L:2d} g={g:<5} 1-s={oms:<6} 1-t={omt:<7} rho={o['rho']:9.1f} ell_s={o['ell_s']:.2f} ell_t={o['ell_t']:.2f}\n"
              f"      paper T_{{u,D}}: {paper}\n"
              f"      team  calT_u : {team}")

    print()
    print("=== analytic constant C_d = 1 + sum_{x != 0} q^{|x|_1} e^{sqrt|x|_1}, q = 2d/(2d+1) (d=3) ===")
    q = 6 / 7
    tot = 1.0
    for n in range(1, 2000):
        tot += (4 * n * n + 2) * q**n * np.exp(np.sqrt(n))
    print(f"C_3 = {tot:.4e}, C_3^2 = {tot**2:.4e}  (crude explicit constant for (neiwuj) at d=3)")
