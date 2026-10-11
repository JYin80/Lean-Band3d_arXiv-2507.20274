import math
d, L, Phi, W = 3, 4, 3.0, 32
for g, kap, g0 in [(1/64, .5, .0130), (1.0, .25, .5610), (10.0, .25, 4.6723)]:
    c0 = min(math.log(1 + kap / (4 * d * 10.0)), kap / 2); rh = 64 * math.exp(c0 / 2 * 6)
    CA = 7 + 2 * d * g0 * math.sqrt(2 + 32 / kap ** 2); Cth = CA ** 2 + 8 / kap ** 2
    dl = W ** -1.5  # smallest delta allowed by W^-d <= delta^2
    print(f"sz0 W=32 g={g:.4g}: (C1) 8*64*rho_hat*C_th*Phi*delta^2 at delta=W^-3/2 = {8 * 64 * rh * Cth * Phi * dl ** 2:.3g} <= 1: {8 * 64 * rh * Cth * Phi * dl ** 2 <= 1}")
