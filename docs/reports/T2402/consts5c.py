"""consts5c.py (T2402 1a, ticket item (iv)): the constants G5c uses, at g = 1/64, 1, 10 with kappa uniform in L and Lambda = 1/dd = 10 (d = 3).
Part 1 (stab.py, FFT on Z_L^3, L = 64 / 96 / 128, w = 1.2i / 1.2i / 1.0i as T2390 (a)): flow data, |m0|, Im m0, kappa (design value, <= Im m(z) uniformly in L),
   the minor-replacement constant 2/kappa, rho_off = sum_{b != a}|M_ab| (observed), Ward remainder sum_{b != a}|M_ab|^2 vs 1 - |m0|^2 (BAMB_ward_row).
Part 2: the first-order bound of R_uy = -sum_{v != u} M_uv (YG)_vy:  ||R||_max <= rho_off (3/2 (t delta + A_b^{1/2}) + X_b^{1/2})  with A_b, X_b, R_0 the formulas of GreenCore_Ab/Xb/R0
   (BA/GreenCore.lean:1348-1355), at the T2390 instance data (inst.py: L = 4, W = 4096 / 16384 / 16384, eps0 = 1.4, delta = W^-eps0, Phi = 3, rho = L^d = 64, S = expC(d-2, c0)).
Usage: python3 consts5c.py"""
import math
import numpy as np
import stab
d, Lam = 3, 10.0
def expC(k, c): return 2 ** (k + 2) * (2 * (2 ** (k + 3) * (1 + math.factorial(k + 3) / c ** (k + 3))))
print("part 1: g  L  kappa(design)  Im m(z)  t0  g0  |m0|  Im m0  2/kappa  rho_off  sum_{b!=a}|M_ab|^2  1-|m0|^2  ||m0||<=1  kappa<=|m0|")
for g, kap, w, L in [(1 / 64, 0.5, 1.2j, 64), (1.0, 0.25, 1.2j, 96), (10.0, 0.04, 1.0j, 128)]:
    fp = stab.flow_point(g, L, w=w); g0, E, m0, t0 = fp['g0'], fp['E'], fp['m0'], fp['t0']
    psi, dist = stab.grids(L)
    M0 = np.fft.ifftn(1 / (g0 * psi - E - m0)); A = np.abs(M0)
    rho_off = A.sum() - A[(0,) * d]; wsq = (A ** 2).sum() - A[(0,) * d] ** 2
    print(f"g={g:<8.5g} L={L:<4d} kappa={kap:<5} Im m={fp['m'].imag:.4f}>=kappa {fp['m'].imag >= kap}  t0={t0:.4f} g0={g0:.4f}<=Lam {g0 <= Lam} |m0|={abs(m0):.4f} Im m0={m0.imag:.4f}  "
          f"2/kappa={2 / kap:.1f}  rho_off={rho_off:.4f}  sum|M|^2 off={wsq:.6f} vs 1-|m0|^2={1 - abs(m0) ** 2:.6f}  |m0|<=1 {abs(m0) <= 1} kappa<=|m0| {kap <= abs(m0)}")
print("\npart 2: g  c0  S  rho  Phi  W  eps0  delta  Lm  R0  X_b  A_b  bound=rho(3/2(delta+sqrt A_b)+sqrt X_b)  bound/Psi (Psi = W^-eps0)")
L, Phi, eps0 = 4, 3.0, 1.4
for g, kap, g0, W in [(1 / 64, .5, .0130, 4096), (1.0, .25, .5610, 16384), (10.0, .25, 4.6723, 16384)]:
    c0 = min(math.log(1 + kap / (4 * d * Lam)), kap / 2); S = expC(d - 2, c0); rho = L ** d
    dl = W ** (-eps0); w0 = float(W) ** (-d); Lm = W ** (-2 * eps0)
    R0 = 4 * c0 ** -2 * S * w0 + 16 * rho * Phi / c0 * S * (S * Lm)
    Xb = Phi * (2 + 18 / kap ** 2) * R0
    Ab = 5 * (4 / kap ** 2 * R0 * (13 / 4 * dl ** 2) + Phi * (2 * Lm + 8 / kap ** 2 * R0 * (13 / 4 * dl ** 2)) + Phi * w0 + (2 * d * g0) ** 2 * Xb)
    bound = rho * (1.5 * (dl + math.sqrt(Ab)) + math.sqrt(Xb))
    print(f"g={g:<8.5g} c0={c0:.2e} S={S:.2e} rho={rho} Phi={Phi} W={W} eps0={eps0} delta={dl:.2e} Lm={Lm:.2e}  R0={R0:.2e} X_b={Xb:.2e} A_b={Ab:.2e}  bound={bound:.2e}  bound/Psi={bound / dl:.2e}  (trivial |R| <= rho*(3/2)*(3/2+...) ~ O(rho))")
