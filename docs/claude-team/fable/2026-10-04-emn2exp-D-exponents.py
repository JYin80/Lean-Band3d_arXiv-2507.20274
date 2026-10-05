#!/usr/bin/env python3
"""
T2118 review: log_W exponent bookkeeping of the far sum S~3 in the preflight's premise-consistent
regime (polylog factors and d-dependent constants dropped, they are W^{o(1)}):
  l_t = W^lam,  u = 1-t = g^2/l_t^2 -> W^{-2 lam},  eta ~ u,  l = (log W)^10 l_t ~ W^lam,
  |Reg| ~ l^d ~ W^{d lam},  r = 1.01 l^dag:  T(r) ~ W^{-(d-2) lam}  (exp(-sqrt(r/l_t)) = W^{-o(1)}),
  P_D(r) = W^{-d} max(T(r), W^{-D}),  Jhat = W^{-j}  (2-loop profile Y = min(Jhat P_D, P_{D1}), D1 = 100),
  Bctl ~ W^{-d}.   Target (pin RHS): eta^{-1} (Bctl^{1/2} + Jhat^3) P_D(r)^2.
Three bounds of S~3, each as (exponent of bound) - (exponent of target), so <= 0 means "closes":
  [PF]   preflight route, floor-floor sub-cube: W^d |Reg| Y_ab Y_ac Y_bc' with both legs at the floor
         (Y_ac = Y_bc' = min(W^{-j} W^{-d-D}, W^{-d} T) ~ W^{-d-D-j} on the inner shell T ~ W^{-D});
  [SF]   split, floor part A^f = {c' : P_D(|c'-b|) <= P_D(r)}: contraction inequality,
         3^d eta^{-1} y^5 sqrt(P(0)) P_D(r)^2  (no sum, no Jhat);
  [SN]   split, Hoelder part A^n = {c' : P_D(|c'-b|) > P_D(r)}: W^d Jhat^3 P_D(r) * W^{-2d} *
         [C_I u^{-1} T(r) + C_1 u^{-1} W^{-D}]  (TTT2 and sum_c T <= C_1/u; no floor-floor term).
"""
d = 3
def table(lam, Ds, js):
    print(f"# d={d}, lam={lam} (l_t = W^lam), exponents are log_W(bound/target); max over j in last column")
    for D in Ds:
        pr = -d + max(-(d-2)*lam, -D)                       # log_W P_D(r)
        rows = []
        for j in js:
            target = 2*lam + max(-d/2, -3*j) + 2*pr
            y_ab = -d + min(-j + max(-(d-2)*lam, -D), -(d-2)*lam)
            pf = d + d*lam + y_ab + 2*(-d - D - j) - target
            sf = (2*lam - d/2 + 2*pr) - target
            sn = (d - 3*j + pr - 2*d + 2*lam + max(-(d-2)*lam, -D)) - target
            rows.append((j, pf, sf, sn))
        s = "  ".join(f"j={j:<4g} PF{pf:+.3f} SF{sf:+.3f} SN{sn:+.3f}" for j, pf, sf, sn in rows)
        print(f"D={D:<5g}: {s}  | max PF={max(r[1] for r in rows):+.3f} "
              f"max SF={max(r[2] for r in rows):+.3f} max SN={max(r[3] for r in rows):+.3f}")
    print(f"# (d-2)*lam = {(d-2)*lam:.3f}: PF closes iff D >= (d-2) lam (row 7 of the preflight); SF, SN close for every D>0.")

print("# exponent bookkeeping, S~3 far sum, preflight regime W = 10^(10^40) (only exponents matter)")
table(0.3, [0.05, 0.1, 0.2, 0.28, 0.35, 1.0], [0, 0.25, 0.5, 0.75, 1.0, 2.0])
table(1.0, [0.05, 0.5, 0.9, 1.1, 3.0], [0, 0.25, 0.5, 1.0])

# Non-monotonicity of the pin's RHS in D (why "for all D>0" is stronger than "for all large D" here,
# and why STLWT, whose RHS has no Jhat, is not affected): Jhat_D P_D(r) at a maximizing pair s in the
# floor zone of both D and D0 (T(s) <= W^{-D0} < W^{-D}) while r is not: ratio W^{D0-D}.
print("# non-monotonicity in D of Jhat_D^3 P_D(r)^2: maximizer of Jhat at a floor pair s, r not at the floor")
import math
W = 1e6
for (D, D0) in [(0.05, 1.0), (0.1, 2.0), (0.5, 4.0)]:
    LK_s = W**(-d-D0)                 # |(L-K)^2(s)| at a pair s deep in the floor zone (T(s) ~ 0): Jhat_D0 = 1
    Tr = W**(-0.03)                   # T(r) > W^{-D} > W^{-D0}: r is not at the floor for either D
    def Jhat(Dv):
        P_s = W**(-d) * W**(-Dv)      # P_Dv(s) = floor
        P_r = W**(-d) * max(Tr, W**(-Dv))
        return LK_s / P_s, P_r
    J_D, P_D_r = Jhat(D); J_D0, P_D0_r = Jhat(D0)
    rhs_D = J_D**3 * P_D_r**2; rhs_D0 = J_D0**3 * P_D0_r**2
    print(f"  D={D}, D0={D0}: Jhat_D={J_D:.3e} Jhat_D0={J_D0:.3e}; RHS(D0)/RHS(D) = {rhs_D0/rhs_D:.3e} "
          f"= W^{math.log(rhs_D0/rhs_D, W):.2f} (= W^(3(D0-D))): the large-D statement does not imply the small-D one")
# STprof is antitone in D (tailW = max(T, W^{-D}), W >= 1): the large-D statement of STLWT / STStep2Decay
# implies the small-D one.
for Dv in (0.05, 0.5, 2.0):
    print(f"  STprof check: max(T=1e-4, W^-{Dv}) = {max(1e-4, W**(-Dv)):.3e}  (decreasing in D)")
