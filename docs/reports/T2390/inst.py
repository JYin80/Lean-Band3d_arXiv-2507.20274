import math
d, Lam, L, Phi = 3, 10.0, 4, 3.0
def expC(k, c): return 2 ** (k + 2) * (2 * (2 ** (k + 3) * (1 + math.factorial(k + 3) / c ** (k + 3))))
rho = L ** d                      # row sum of |M_xy|: L^d same-offset sites, |M_xy| <= 1 (BAMfine_norm_le_one)
diam = d * (L // 2)               # l1 diameter of Z_4^3
print("g      kappa g0      c0       mu        c_lam=min(c0/12,mu/6)  rho_hat  K_Th    K_BA     C_A    C_th    W     eps0 delta    window[W^-3/2,delta]  N^(1/6)<=W  Adm  d<=k/2 W^-d<=d^2 (C1)=8*rho*rho_hat*C_th*Phi*d^2  K_BA*d<=1/2")
for g, kap, g0, W, e0 in [(1/64, .5, .0130, 4096, 1.4), (1.0, .25, .5610, 16384, 1.4), (10.0, .25, 4.6723, 16384, 1.4)]:
    c0 = min(math.log(1 + kap / (4 * d * Lam)), kap / 2)
    A = 4 * (16 * d * d / kap ** 3 / c0) ** 2; S = expC(d - 2, c0); eps = kap ** 2 / 4
    mu = min(c0, eps ** 2 * c0 / (2 * A * Lam ** 2 * S)); clam = min(c0 / 12, mu / 6); nu = c0 / 2
    rh = rho * math.exp(nu * diam); KT = 16 / kap ** 4; KBA = rho * (1 + KT)
    CA = 7 + 2 * d * g0 * math.sqrt(2 + 32 / kap ** 2); Cth = CA ** 2 + 8 / kap ** 2
    dl = W ** (-e0); N = (W * L) ** d; c1 = 8 * rho * rh * Cth * Phi * dl ** 2
    print(f"{g:<6.4g} {kap:<5} {g0:<6} {c0:.2e} {mu:.2e} {clam:.2e}  {rh:.2f}  {KT:.0f}  {KBA:.0f}  {CA:.1f}  {Cth:.2e}  {W}  {e0}  {dl:.2e}  [{W**-1.5:.2e},{dl:.2e}] {W**-1.5<=dl}  {N**(1/6):.0f}<={W} {N**(1/6)<=W}  {W**(-d/2+.1)<=g<=Lam}  {dl<=kap/2}  {W**-d<=dl**2}  {c1:.2e} {c1<=1}  {KBA*dl:.3f} {KBA*dl<=.5}")
