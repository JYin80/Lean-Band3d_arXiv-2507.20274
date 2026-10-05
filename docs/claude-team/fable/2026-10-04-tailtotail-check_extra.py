#!/usr/bin/env python3
"""
Extra checks for (neiwuj), d = 3:
 (1) the elementary Neumann-series bound (1-t) Theta_t(0,a) <= q^{|a|_1}, q = 2d t g^2/(1+2d g^2 - t) <= 2d/(2d+1),
     and the probability-kernel bound  Ptilde_{ab} <= q^{|a-b|_1} (a != b), Ptilde_{aa} <= 1;
 (2) the charge (+,+): |P^{(+,+)}| <= P^{(+,-)} entrywise (m = m_sc(E+i0), |m| = 1);
 (3) the squared profile e^{-2 sqrt r} (martingale / quadratic-variation version): ratio bounded as well;
 (4) the literal statement with W, D: (U o T_{s,D})(a) <= C T_{t,D}(|a1-a2|) + rho^2 W^{-D} with C = 1.4.
"""
import numpy as np
from check_neiwuj import lattice, S_hat, conv_UU

d = 3

def Theta_real(L, g, t):
    Sh = S_hat(L, d, g)
    return np.real(np.fft.ifftn(1.0 / (1 - t * Sh)))

print("=== (1) Neumann bound (1-t)Theta_t(0,a) <= q^{|a|_1}, and Ptilde bounds ===")
for (L, g, s, t) in [(16, 0.1, 0.5, 0.99), (16, 0.3, 0.1, 0.91), (16, 0.5, 0.01, 0.75), (16, 0.01, 0.5, 0.9999)]:
    linf, l1 = lattice(L, d)
    Th = Theta_real(L, g, t)
    q = 2 * d * t * g**2 / (1 + 2 * d * g**2 - t)
    lhs = (1 - t) * Th
    bound = q ** l1
    ok = np.all(lhs <= bound * (1 + 1e-9) + 1e-15)
    P = np.real(np.fft.ifftn((1 - s * S_hat(L, d, g)) / (1 - t * S_hat(L, d, g))))
    rho = (1 - s) / (1 - t)
    Pt = P / rho
    okP = Pt[(0,) * d] <= 1 + 1e-12 and np.all((Pt <= bound * (1 + 1e-9) + 1e-15) | (l1 == 0))
    print(f"L={L} g={g} 1-s={1-s:.2f} 1-t={1-t:.4f}: q={q:.4f} (<= 6/7={6/7:.4f}: {q <= 6/7 + 1e-12}); "
          f"(1-t)Theta <= q^|a|_1 : {ok}; Ptilde bounds: {okP}; Ptilde(0)={Pt[(0,)*d]:.4f}, "
          f"max ratio (1-t)Theta/q^|a|_1 = {np.max(lhs / bound):.4f}")

print()
print("=== (2) charge (+,+): |P^{(+,+)}_{ab}| <= P^{(+,-)}_{ab} entrywise ===")
for E in [0.0, 1.0, 1.9]:
    m = (-E + 1j * np.sqrt(4 - E**2)) / 2      # m_sc(E + i0), |m| = 1
    L, g, s, t = 16, 0.3, 0.1, 0.91
    Sh = S_hat(L, d, g)
    Ppm = np.real(np.fft.ifftn((1 - s * Sh) / (1 - t * Sh)))
    Ppp = np.fft.ifftn((1 - s * m**2 * Sh) / (1 - t * m**2 * Sh))
    print(f"E={E}: |m|={abs(m):.6f}, max(|P++| - P+-) = {np.max(np.abs(Ppp) - Ppm):.3e} (<= 0 expected), "
          f"sum|P++| = {np.sum(np.abs(Ppp)):.4f} vs rho = {(1-s)/(1-t):.4f}")

print()
print("=== (3) squared profile e^{-2 sqrt r} (quadratic variation), amplitude rho^4 (W^d(1-s))^{-4} = (W^d(1-t))^{-4} ===")
for (L, g, oms, omt) in [(16, 0.01, 0.5, 0.01), (16, 0.1, 0.5, 0.01), (16, 0.3, 0.9, 0.09), (32, 0.1, 0.5, 0.01)]:
    s, t = 1 - oms, 1 - omt
    linf, l1 = lattice(L, d)
    Sh = S_hat(L, d, g)
    Ph = (1 - s * Sh) / (1 - t * Sh)
    rho = (1 - s) / (1 - t)
    f = np.exp(-2 * np.sqrt(linf))
    # (U (x) U) acting on A_{b1 b2 b1' b2'} = T_s^2(|b1-b2|) 1_{b'=b}-type profile reduces to the same convolution
    # with the kernel (Ptilde * Ptilde) and amplitude rho^4; we check the normalised spatial factor
    R = conv_UU(f, Ph) / rho**2 / f
    print(f"L={L} g={g} 1-s={oms} 1-t={omt}: max_a (Ptilde*Ptilde*e^{{-2sqrt}})/e^{{-2sqrt}} = {R.max():.4f}, at r=1,2,3: "
          + " ".join(f"{R[(r,)+(0,)*(d-1)]:.4f}" for r in (1, 2, 3)))

print()
print("=== (4) literal (neiwuj) with W, D: (U o T_{s,D})(a) <= 1.4 T_{t,D}(|a1-a2|) + rho^2 W^{-D} ? ===")
for (L, W, D, g, oms, omt) in [(16, 10, 5.0, 0.1, 0.5, 0.01), (16, 10, 8.0, 0.01, 0.5, 0.0001), (16, 100, 12.0, 0.3, 0.9, 0.09)]:
    s, t = 1 - oms, 1 - omt
    linf, l1 = lattice(L, d)
    Sh = S_hat(L, d, g)
    Ph = (1 - s * Sh) / (1 - t * Sh)
    rho = (1 - s) / (1 - t)
    Ts = (W**d * (1 - s)) ** (-2) * np.exp(-np.sqrt(linf)) + W ** (-D)
    Tt = (W**d * (1 - t)) ** (-2) * np.exp(-np.sqrt(linf)) + W ** (-D)
    UT = conv_UU(Ts, Ph)
    rhs = 1.4 * Tt + rho**2 * W ** (-D)
    print(f"L={L} W={W} D={D} g={g} 1-s={oms} 1-t={omt}: holds everywhere: {np.all(UT <= rhs)}; "
          f"max (U T_s)/(T_t + rho^2 W^-D) = {np.max(UT / (Tt + rho**2 * W**(-D))):.4f}")
