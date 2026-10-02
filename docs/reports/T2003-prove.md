Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  2 18:10:22 UTC 2026

Notation: e := 1-t, s := S_00 = 1/(1+2dλ²), Λ := upper bound of λ (paper `(eq:WO)`: Λ = 𝔡^{-1}), μ := m(σ1)m(σ2) (|μ| = 1; μ = 1 for σ1 ≠ σ2, μ = m² for σ1 = σ2), ξ = tμ, φ = arg m, c ∈ (0,1) the constant of `|r| ≤ c|a|`. P5, P5s, P6, P7, P8 = `(prop:ThfadC)`, `(prop:ThfadC_short)`, `(prop:BD1)`, `(prop:BD2)`, `(prop:ThfadC0)`. `RBM.ellT`, `RBM.Bparam` (`RBM3D/Defs/Params.lean:32,36`) equal `(eq:ellt)`, `(eq_B_param)` literally (checked by reading; `d - 2` is ℕ-subtraction, harmless for d ≥ 3). Bulk: `m(E+i0) = (-E+i√(4-E²))/2` (`(eq:defmzsc)`), so |E| ≤ 2-κ gives `sin φ ≥ √(4-(2-κ)²)/2`.

### (i) Exponent table (d = 3 numerics; every number is in the script output of (ii) unless a script is named)

| quantity | value | constraint | slack / evidence |
|---|---|---|---|
| ℓ_t | min(max(λ/√e,1),L) | `ℓ_t = 1 ⇔ e ≥ λ²`; `1<ℓ_t<L ⇔ λ²/L² < e < λ²`; `ℓ_t = L ⇔ e ≤ λ²/L²` | table (3): ℓ_t = 1.00, 5.74, 33.00 at e/λ² = 1, 0.0303, 0.000918 (L=33, λ=0.1) |
| c_d (P5) | 0.3 at d=3 | sup_{a,t,λ≤1,L} `|Θ|/(B e^{-c|a|/ℓ_t})` < ∞ | c=0.3: sup ≤ 2.0 for L ≤ 49 (sweep (4)); c=0.5: 2.09 at L=65 but 61423 at (L=65, λ=0.3) (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/explore3.py`), so c_d < 0.5 at d = 3 |
| C_d (P5) | 2.1 | ≥ `1+Λ²` and ≥ 1.55 (far-field, table (3)) | at Λ=1: 2.0 ≤ 2.1; slack 0.1 |
| Λ-dependence (P5–P8) | C ≥ 1+Λ² | at t=0, Θ=I, B_{0,0} = 1/(1+λ²)+L^{-d}, so ratio = 1+λ² exactly | (5): 1.995, 4.966, 16.613 at λ=1,2,4 (L=9). Constants must depend on (d,Λ), not on d alone: candidate T2003a (paper: "constants depend on d" in P5, silent on 𝔡; footnote after `(eq:WO)`: replace λ by λ∧1). Pins quantify Λ before λ, or restrict to λ ∈ (0,1] with d-only constants |
| B_{t,K} two terms | B1(K) = (λ²+e)^{-1}(K+1)^{2-d}, B2 = 1/(L^d e) | B2 ≥ B1(K) ⇔ (K+1)^{d-2}(λ²+e) ≥ L^d e | K=0: e ≲ λ²/L^d; K ≍ L: e ≲ λ²/L². Table (3): B1(0)/B2 = 1 at e/λ² = 2.78e-5 = L^{-3}; B1(48)/B2 = 0.673 at e/λ² = 9.18e-4 = L^{-2} |
| regimes of B | e ≥ λ²: B ≍ e^{-1}(K+1)^{2-d}, ℓ_t = 1; λ²/L² < e < λ²: B1 ≍ λ^{-2}(K+1)^{2-d} dominates for K ≤ ℓ_t; e ≤ λ²/L²: B2 dominates at |a| ≍ L (so `e^{-c|a|/L} ≥ e^{-cd/2}` costs a constant) | `|a| ≤ ℓ_t`: exponential factor ≥ e^{-c}; `|a| > ℓ_t`: B1 term decays exponentially | Θ(0,0)/B(0) = 0.966, 0.512, 0.359, 0.260, 0.282, 0.630, 0.933, 0.999 across the 8 regimes; Θ(far)/(B e^{-c|a|/ℓ}) ≤ 1.547 |
| zero mode | L^{-d}/e | Θ(0,a) = Θ̊(0,a) + L^{-d}/(1-tμ) | P8 removes exactly the k=0 Fourier mode (translation invariance gives `L^{-2d}ΣΣΘ = L^{-d}Σ_bΘ(0,b)`), which is the term B2 for μ = 1 |
| P5s λ² factor | λ² on `a ≠ 0` | Θ(0,e₁) ≈ tμ λ² s/A² (first Neumann term), so λ² is sharp and cannot be dropped | Θ(0,0) = O(1) uniformly in λ → 0 |
| gap (P5s), derived here, no citation | A = |1-tsμ| ≥ sin²φ; ρ = t(1-s)/A ≤ ρ₀ := 1 - s sin²φ/2 | proof: `|1-um²|² = (1-u)²+4u sin²φ` with u = ts, so `A-(1-u) ≥ 2u sin²φ` and `A - t(1-s) ≥ (1-t)+2ts sin²φ ≥ s sin²φ`, `A ≤ 2` | (2): 0 violations, min(ρ₀-ρ) = 0.0672; Neumann series `Θ = Σ_k (1-tμs)^{-(k+1)}(tμλ²s·Adj)^k` gives `|Θ(0,a)| ≤ ρ^{|a|}/(A(1-ρ))` and, for a ≠ 0, `≤ ρ ρ₀^{|a|-1}/(A(1-ρ₀))`, `ρ ≤ 2dλ²/A` |
| c_κ, C_κ (P5s) | c_κ = -ln(1 - s_min sin²φ/2), C_κ = 8d/(s_min sin⁶φ), s_min = 1/(1+2dΛ²) | ρ₀ ≥ 1/2; a=0: `1/(A(1-ρ₀)) ≤ 2/(s sin⁴φ)` | at Λ=1: m=i: c=0.0741, C=168; m=e^{iπ/3}: c=0.0551, C=398; required sup ratio 0.512–0.654 (ok=True in (1)); depends on (d, Λ, κ) |
| P5 for σ1=σ2 | same C_d, c_d, no bulk needed | paper property 4: `|Θ^{(σ1σ2)}_{ab}| ≤ Θ^{(+,-)}_{ab}` (Taylor series with positive majorant, `A_deterministic_estimates.tex:15-19`) | θ-sweep μ=e^{iθ}, θ ∈ {0,1e-4,…,π}: P5 sup 1.99 (L=9), 2.0 (L=33) for all θ (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/mu.py`) |
| `|r| ≤ c|a|` (P6, P7) | **c < 1 required**; take c = 1/2 | for c ≥ 1 the point a+r = 0 is allowed: LHS = |Θ(0,0)-Θ(0,a)| ≍ λ^{-2}, RHS ≍ λ^{-2}|a|^{2-d} | c=1/2: sup P6 ≤ 2.82, P7 ≤ 8.08 flat in L=5…49; c=1: P6 = 16.3, 28.2, 46.1, 90.0, 130.0 and P7 = 19.1, 30.5, 48.3, 92.1, 132.1 for L = 5, 9, 17, 33, 49, linear in L = L^{d-2}. Old D12 ("for each constant c>0") is false: `ThetaDiffOne`/`ThetaDiffTwo` (`Interface.lean:118,133`) are unprovable as written (∀c>0, loss L^τ with τ < d-2 = 1). For c<1, `|a+r|_L ≥ (1-c)|a|` |
| C6, C7, C8 (c=1/2) | 3, 9, 2.1 | ≥ sup ratios | sup 2.82, 8.08, 2.0 (sweep, Λ=1); slack 6%, 10%, 5%; blow-up as c → 1 |
| loss for P6–P8 | none needed numerically; pin `L^τ`, ∀τ>0 (C depends on τ, c, d, Λ, κ) | `L^τ ≥ 1`, so the loss-free statement implies the pinned one | sup ratio flat in L (P6 2.37→2.82, P7 7.21→7.72, P8 1.98→2.0). Consumer scale: L ≤ N = (WL)^d, and N ≤ W^{1/𝔠} from W ≥ N^𝔠, so `L^τ` is absorbed by ≺ at scale N or W. Loss-free pin = optional strengthening for stage 1b if its route yields it |
| μ range for P6–P8 | μ=1, or μ=m² with κ ≤ Im m (paper: via P5s) | numerics suggest all |μ|=1 | θ-sweep: P6 ≤ 2.82, P7 ≤ 8.08, P8 ≤ 2.0 for all θ ∈ [0,π], L ∈ {9,33} (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/mu.py`). Pin keeps the paper's bulk clause; uniform-μ is an optional strengthening |

### (ii) Concrete nondegenerate instance and numeric check

Instance: d = 3, L = 5 (125 sites), λ ∈ {1/2, 1/10} ≤ Λ = 1, t ∈ {0.9, 0.99}, m ∈ {i, e^{iπ/3}} (E = 0, E = -1; κ = 1), charges (+,−) (ξ = t) and (+,+) (ξ = tm²), all 124 nonzero r, c = 1/2. No external hypothesis (DECISIONS §5: nothing cited is an input), so no external limit computation. Hypotheses at the instance: 3 ≤ d, 3 ≤ L, 0 < λ ≤ Λ, t ∈ [0,1), |m| = 1, Im m > 0 for P5s. Candidates tested: C5 = 2.1 (c_d = 0.3), C6 = 3, C7 = 9, C8 = 2.1, P5s with (c_an, C_an).

Command (pure numpy; Θ(0,·) by the Fourier sum, sanity-checked against the inverse of `1-ξ·SB` built from the definition):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2003_pre.py`

Output (verbatim, CPU time 122 s):
```
== (0) Fourier sum vs direct inverse of 1-xi*SB built from the definition (d=3,L=5)
max |inverse - Fourier| = 2.3714374201337736e-16  row sum of S = 0.9999999999999999 1.0000000000000002
== (1) instance d=3 L=5: required constants (sup ratio, all 124 r, c=1/2) vs candidates C5=2.1 (c_d=0.3), C6=3, C7=9, C8=2.1
lam   t     m     chg  P5     P6     P7     P8   | short: sup|Th|/(1_{a=0}+lam^2 e^{-c|a|}) at c=c_an, 0.5; c_an=-ln(1-sin^2(phi)/14), C_an=8d*7/sin^6(phi) (Lambda=1, s>=1/7)
0.5   0.9   i       +-  0.632  0.809  2.427  0.622 | 
0.5   0.9   i       ++  0.257  0.187  0.635  0.263 | 0.605 0.605 (c_an=0.0741, C_an=168, ok=True)
0.5   0.9   e^ipi/3 +-  0.632  0.809  2.427  0.622 | 
0.5   0.9   e^ipi/3 ++  0.278  0.209  0.692  0.284 | 0.654 0.654 (c_an=0.0551, C_an=398, ok=True)
0.5   0.99  i       +-  0.722  0.842  2.526  0.531 | 
0.5   0.99  i       ++  0.159  0.148  0.507  0.191 | 0.592 0.592 (c_an=0.0741, C_an=168, ok=True)
0.5   0.99  e^ipi/3 +-  0.722  0.842  2.526  0.531 | 
0.5   0.99  e^ipi/3 ++  0.172  0.166  0.553  0.207 | 0.641 0.641 (c_an=0.0551, C_an=398, ok=True)
0.1   0.9   i       +-  0.737  0.364  1.091  0.734 | 
0.1   0.9   i       ++  0.059  0.002  0.008  0.059 | 0.536 0.536 (c_an=0.0741, C_an=168, ok=True)
0.1   0.9   e^ipi/3 +-  0.737  0.364  1.091  0.734 | 
0.1   0.9   e^ipi/3 ++  0.068  0.003  0.010  0.068 | 0.618 0.618 (c_an=0.0551, C_an=398, ok=True)
0.1   0.99  i       +-  0.356  0.452  1.356  0.345 | 
0.1   0.99  i       ++  0.010  0.000  0.001  0.010 | 0.512 0.512 (c_an=0.0741, C_an=168, ok=True)
0.1   0.99  e^ipi/3 +-  0.356  0.452  1.356  0.345 | 
0.1   0.99  e^ipi/3 ++  0.012  0.001  0.002  0.012 | 0.591 0.591 (c_an=0.0551, C_an=398, ok=True)
worst: {'P5': 0.737, 'P8': 0.734, 'P6': 0.842, 'P7': 2.526} | all <= candidates: True
== (2) analytic gap (derived here, tolerance 1e-13 abs for FFT noise): u=ts, s=1/(1+2d lam^2), A=|1-u m^2|, rho=t(1-s)/A
   claim: A>=sin^2(phi), rho<=1-s sin^2(phi)/2, |Th(0,a)|<=rho^{|a|}/(A(1-rho)), and for a!=0 also |Th(0,a)|<=rho*rho0^{|a|-1}/(A(1-rho0))
violations: 0  min(rho0-rho)= 0.06715143611541752
== (3) regimes, L=33 lam=0.1: e=1-t; B1(K)=(lam^2+e)^-1 (K+1)^{2-d}, B2=1/(L^d e); Th/B at a=0 and a=far (|a|=48, c=0.3 exponential included)
e/lam^2      ell_t  B1(0)/B2  B1(far)/B2  Th(0)/B(0)  Th(far)/(B e^{-c|a|/ell})
50           1.00   3.52e+04  719         0.966       0.000
3            1.00   2.7e+04   550         0.512       0.000
1            1.00   1.8e+04   367         0.359       0.000
0.0303       5.74   1.06e+03  21.6        0.260       0.085
0.000918     33.00  33        0.673       0.282       0.865
2.78e-05     33.00  1         0.0204      0.630       1.513
2.78e-06     33.00  0.1       0.00204     0.933       1.544
2.78e-08     33.00  0.001     2.04e-05    0.999       1.547
== (4) extreme sweep (lam in {1,.5,.1,.03}, 1-t in lam^2*{1,2,.5,/L,/L^2,/L^3,/L^d/10}, 0.3,0.1,1,1e-9; xi in {t, t m^2: m=i,e^i pi/3,e^i pi/6}); sup ratios by L; c=1/2 and c=1
L=5   {'P5': 1.97, 'P8': 1.98, 'P6': 2.37, 'P7': 7.21} | c=1: P6,P7 = 16.3 19.1
L=9   {'P5': 1.99, 'P8': 2.0, 'P6': 2.67, 'P7': 8.08} | c=1: P6,P7 = 28.2 30.5
L=17  {'P5': 2.0, 'P8': 2.0, 'P6': 2.76, 'P7': 7.77} | c=1: P6,P7 = 46.1 48.3
L=33  {'P5': 2.0, 'P8': 2.0, 'P6': 2.82, 'P7': 7.64} | c=1: P6,P7 = 90.0 92.1
L=49  {'P5': 2.0, 'P8': 2.0, 'P6': 2.82, 'P7': 7.72} | c=1: P6,P7 = 130.0 132.1
== (5) lam range: P5 sup ratio at t=0 equals 1+lam^2 (Th=I, B=1/(1+lam^2)+L^-d), L=9: [1.995, 4.966, 16.613]
```

### Verdicts

- **P5 `(prop:ThfadC)`: PASS.** True at the instance and at every extreme tested (λ = 0.03, 1-t = 1e-9, L = 49); holds for all |μ| = 1. Needs constants (d, Λ) (T2003a candidate) and c_d = 0.3 at d = 3.
- **P5s `(prop:ThfadC_short)`: PASS.** Internal proof via the derived gap (no [bourgade2019random]); constants (d, Λ, κ).
- **P6 `(prop:BD1)`, P7 `(prop:BD2)`: PASS with `|r| ≤ c|a|`, c < 1 fixed, C = C(c, …)**; **the old reading c ≥ 1 is FALSE** (a+r = 0), reported as T2003a candidate with the c=1 sup ratios above; the pins must carry c < 1 (c = 1/2 verified).
- **P8 `(prop:ThfadC0)`: PASS**, C8 = 2.1 at Λ = 1.
- Instance: all candidates hold (`all <= candidates: True`).

## (a′) Preflight corrections — Fri Oct  2 19:47:06 UTC 2026 (items 1, 2); item 3 added Fri Oct  2 22:34:34 UTC 2026
Three statements of (a) are wrong; none changes a verdict (P5–P8 stay PASS; the pins carry ∃C). For d = 3 and every L = 3…40 the candidates C5 = 2.1 (c_d = 0.3), C6 = 3, C8 = 2.1 stand; C7 = 9 does not (item 3).
1. Row "c_d (P5)": "c=0.5 … 61423 at (L=65, λ=0.3), so c_d < 0.5 at d = 3" is a floating-point artifact: it reproduces (first output below) at |a| = 96, where |Θ| = 5.0e-18 is roundoff and the weight is 8.2e-23. With entries of weight below 1e-9·max|Θ| masked, c = 0.5 gives sup 2.03/2.07/2.09 and c = 0.6 gives 2.33/2.39/2.43 (L = 17/33/65): "c_d < 0.5" is not shown.
2. Row "Λ-dependence": "ratio = 1+λ² exactly" holds only as L → ∞; the ratio is (1+λ²)/(1+(1+λ²)L^{-d}) (L = 9: the printed 1.995, 4.966, 16.613).
3. Row "C6, C7, C8 (c=1/2)" (P7 sup 8.08, slack 10%): the preflight swept odd L only (5, 9, 17, 33, 49). At small even L the P7 sup is larger: C7 = 9 fails for L = 4, 6, 8, 10, 12 (exhaustive over all (a, r): 12.51, 10.80, 10.01, 9.56, 9.40). The maximum over L = 3…40 is 12.51 (L = 4); the even-L values decrease (8.12 at L = 64, 8.00 at L = 128), the odd-L values rise to 7.83 (L = 193, b7). C7 = 13 covers every L tested; P5 ≤ 2.00, P6 ≤ 2.82, P8 ≤ 2.00 for all L = 3…40.
$ python3 allL.py   # source: probe Appendix C; run Fri Oct  2 22:30:04 → 22:32:04 UTC 2026 (axis r and 12 random r per L)
d=3, L=3..40, g in (1,.5,.2,.05,.01), all e<=1 incl. t=0; max over L (value, L): P5=2.00(L=40) U1=8.00(L=3) U2s=16.00(L=37) U2m=54.00(L=3) P8=2.00(L=40) P6c0.5=2.82(L=40) P7c0.5=12.51(L=4)
P7c0.5 by L: 3:5.83 4:12.51 5:7.21 6:10.80 7:7.71 8:10.01 9:8.08 10:9.56 11:7.59 12:9.26 13:7.36 14:9.05 15:7.40 16:8.90 17:7.42 18:8.78 19:7.47 20:8.69 21:7.51 22:8.61 23:7.54 24:8.55 25:7.56 26:8.50 27:7.59 28:8.45 29:7.61 30:8.41 31:7.62 32:8.38 33:7.64 34:8.35 35:7.65 36:8.32 37:7.66 38:8.30 39:7.67 40:8.28
$ python3 exhaust.py 4 6 8 10 12   # source: probe Appendix C; run 22:30:04 → 22:30:30 UTC
exhaustive over all (a,r), d=3, g in (1,.5,.2,.05), e as in extreme.py: L=4: P6c0.5=1.87 P7c0.5=12.51; L=6: P6c0.5=2.54 P7c0.5=10.80; L=8: P6c0.5=2.65 P7c0.5=10.01; L=10: P6c0.5=2.69 P7c0.5=9.56; L=12: P6c0.5=2.70 P7c0.5=9.40
$ python3 direct.py   # source: probe Appendix C; no FFT (inverse of 1-ξ·SB built entry by entry from sbKernel); run 22:31:29 → 22:32:12 UTC
direct inversion, d=3, c=1/2, g in (1,.3,.05,.001), e in (1,.5,.1,g^2,g^2/L,g^2/L^2,g^2/L^3,1e-6,1e-9), L=3..6; max over L: P5=1.98 P6=2.54 P7=12.51 P8=1.99 P5s=0.01 (P5s: ratio to C_an(1_{a=0}+g^2 e^{-c_an|a|}), must be <= 1); P7 by L: 3:5.83 4:12.51 5:7.21 6:10.80
$ python3 evenbig.py 64 128   # source: probe Appendix C; run 22:20:03 → 22:28:34 UTC
L= 64: P5=1.73 U1=5.51 U2s=9.63 U2m=33.14 P8=1.74 P6c0.5=2.82 P7c0.5=8.12  (40s)
L=128: P5=1.75 U1=5.51 U2s=9.63 U2m=33.14 P8=1.76 P6c0.5=2.82 P7c0.5=8.00  (471s)
$ python3 artifact.py   # sources: probe Appendix C
unmasked c=0.5, L=65, lam=0.3: max ratio 61423.5 at e=0.09, |a|=96, |Theta|=5.02e-18, weight=8.17e-23, max|Theta|=2.79e+00, |Theta|/max=1.8e-18
$ python3 cdecay.py   # source: probe Appendix C
P5 sup ratio |Th|/(B e^{-c|a|/ell}) at mu=1, FFT noise masked (only entries with weight >= 1e-9 max|Th|); sweep g in {1,.3,.1,.03}, e as in the preflight sweep
L=17: {0.3: 2.0, 0.5: 2.03, 0.6: 2.33, 0.7: 19.19, 0.8: 121.91, 1.0: 1152.08}
L=33: {0.3: 2.0, 0.5: 2.07, 0.6: 2.39, 0.7: 16.72, 0.8: 78.79, 1.0: 552.17}
L=65: {0.3: 2.0, 0.5: 2.09, 0.6: 2.43, 0.7: 6.77, 0.8: 45.94, 1.0: 552.68}

## (b) Script output
Probe `RBM3D/Probe/T2003Pins.lean` (branch t/T2003, base 3c11d7b). RBM2D is read at c9a24cf with `git archive` (read-only); nothing from RBM1D/RBM2D is ported into the probe (b4), so no port diff-stat applies. Appendix A = inventory, B = RBM2D table (87 rows), C = script sources; every Python script run below is in Appendix C, every time is from `date -u`.
### b1 Build, axioms, forbidden tokens — Fri Oct  2 22:47:06 UTC 2026 (git, build, grep); axioms 22:49:44
$ git log --oneline 3c11d7b..HEAD | wc -l; git log -1 --format=%h; git status --short | wc -l
       9
d6e6054
       0
$ lake build RBM3D.Probe.T2003Pins 2>&1 | grep -E '^(warning|error)|Build completed'
Build completed successfully (2432 jobs).
$ lake env lean RBM3D/Probe/T2003Pins.lean 2>&1 | awk '/depends on axioms/{n++; if (index($0,"[propext, Classical.choice, Quot.sound]")) s++; nm=$1; sub(/^.*RBM\./,"",nm); sub(/.$/,"",nm); l=l" "nm; l1=$0; next} {o++; print} END{print "axiom lines:",n," exactly [propext, Classical.choice, Quot.sound]:",s+0," other messages:",o+0; print l; print l1}' | fold -s -w 190; echo exit=${pipestatus[1]}
axiom lines: 25  exactly [propext, Classical.choice, Quot.sound]: 25  other messages: 0
 PropSpin Prop5Decay Prop5Short Prop6Diff1 Prop7Diff2 Prop8ZeroMode Prop5to8 Prop6Old_false Prop7Old_false PropTH_false Prop5_needs_Lambda Prop5Short.thetaDecayShort Prop5Decay.thetaDecay 
Prop8ZeroMode.thetaZeroMode PropThetaQ PropThetaQ_Theta_eq Prop5DecayQ Prop5Decay.toQ probeSkeleton probeInst5 probeInst5s probeInst6 probeInst7 probeInst8 probe_re_ne
'_private.RBM3D.Probe.T2003Pins.0.RBM.probe_re_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2003Pins.lean
0
(`lake env lean` exits 0 with no message other than the 25 `#print axioms` lines, so no warning; 0 forbidden tokens.)
### b2 The pins, extracted from the probe (declaration text joined, wrapped at 190) — Fri Oct  2 22:41:35 UTC 2026
$ awk '/^def Prop(5Decay|5Short|6Diff1|7Diff2|8ZeroMode) |^structure Prop5to8 /{p=1;buf=""} p&&/^$/{print buf;p=0} p&&/^ *\/--/{next} p{sub(/^ +/,"");buf=buf" "$0}' RBM3D/Probe/T2003Pins.lean | fold -s -w 190
 def Prop5Decay (d : ℕ) (Λ : ℝ) : Prop := 3 ≤ d → 0 < Λ → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ 
σ₂ : Bool, ∀ a : Zd d L, haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖ ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) 
/ ellT L g t)
 def Prop5Short (d : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 
1 → κ ≤ m.im → ∀ σ : Bool, ∀ a : Zd d L, haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖ ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp 
(-c * (zdistD d L a : ℝ)))
 def Prop6Diff1 (d : ℕ) (Λ κ c : ℝ) : Prop := 3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ 
= 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) → haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + 
r) - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹
 def Prop7Diff2 (d : ℕ) (Λ κ c : ℝ) : Prop := 3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ 
= 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L, (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) → haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + 
r) + Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a - r) - 2 * Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 
* (((zdistD d L a : ℝ) + 1) ^ d)⁻¹
 def Prop8ZeroMode (d : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im 
→ ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L, haveI : NeZero L := ⟨by omega⟩ ‖Theta0 d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 
2))⁻¹
 structure Prop5to8 (d : ℕ) (Λ κ c : ℝ) : Prop where decay : Prop5Decay d Λ short : Prop5Short d Λ κ diffOne : Prop6Diff1 d Λ κ c diffTwo : Prop7Diff2 d Λ κ c zeroMode : Prop8ZeroMode d Λ κ
### b3 Compiled nonempty instances (d = 3, L = 5, g = 1/2, t = 9/10, Λ = 1, κ = c = 1/2; m = i and m = e^{iπ/3}, Re m = 0 resp. 1/2; all sign pairs) and the item-4 skeleton — Fri Oct  2 22:41:36 UTC 2026
$ { awk '/^private noncomputable abbrev probeTh /{getline n; sub(/^ +/,"",n); print $0" "n}' RBM3D/Probe/T2003Pins.lean; awk '/^private theorem probe(Skeleton|Inst[0-9s]+) /{p=1;buf=""} p{sub(/^ +/,"");buf=buf" "$0} p&&/:= by$/{sub(/ := by$/,"",buf);print buf;p=0}' RBM3D/Probe/T2003Pins.lean; } | fold -s -w 190
private noncomputable abbrev probeTh (m : ℂ) (σ₁ σ₂ : Bool) : Matrix (Zd 3 5) (Zd 3 5) ℂ := Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂))
 private theorem probeSkeleton (d : ℕ) (Λ κ c : ℝ) (h : Prop5to8 d Λ κ c) (hd : 3 ≤ d) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ 
< 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, haveI : NeZero L := ⟨by omega⟩ ‖Theta d L g ((t₀ : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 0‖ ≤ C * Bparam d L g t₀ 0
 private theorem probeInst5 (h : Prop5Decay 3 1) : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ m : ℂ, (m = Complex.I ∨ m = probeE) → ∀ σ₁ σ₂ : Bool, ∀ a : Zd 3 5, ‖probeTh m σ₁ σ₂ 0 a‖ ≤ C * Bparam 
3 5 (1 / 2) (9 / 10) (zdistD 3 5 a) * Real.exp (-c * (zdistD 3 5 a : ℝ) / ellT 5 (1 / 2) (9 / 10))
 private theorem probeInst5s (h : Prop5Short 3 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ m : ℂ, (m = Complex.I ∨ m = probeE) → ∀ σ : Bool, ∀ a : Zd 3 5, ‖probeTh m σ σ 0 a‖ ≤ C * 
((if a = 0 then (1 : ℝ) else 0) + (1 / 2 : ℝ) ^ 2 * Real.exp (-c * (zdistD 3 5 a : ℝ)))
 private theorem probeInst6 (h : Prop6Diff1 3 1 (1 / 2) (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ∀ m : ℂ, (m = Complex.I ∨ m = probeE) → ∀ σ₁ σ₂ : Bool, ‖probeTh m σ₁ σ₂ 0 ((![2, 0, 0] : Zd 3 5) + ![1, 
0, 0]) - probeTh m σ₁ σ₂ 0 (![2, 0, 0] : Zd 3 5)‖ ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹ * (zdistD 3 5 (![1, 0, 0] : Zd 3 5) : ℝ) * (((zdistD 3 5 (![2, 0, 0] : Zd 3 5) : ℝ) + 1) ^ 
2)⁻¹
 private theorem probeInst7 (h : Prop7Diff2 3 1 (1 / 2) (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ∀ m : ℂ, (m = Complex.I ∨ m = probeE) → ∀ σ₁ σ₂ : Bool, ‖probeTh m σ₁ σ₂ 0 ((![2, 0, 0] : Zd 3 5) + ![1, 
0, 0]) + probeTh m σ₁ σ₂ 0 ((![2, 0, 0] : Zd 3 5) - ![1, 0, 0]) - 2 * probeTh m σ₁ σ₂ 0 (![2, 0, 0] : Zd 3 5)‖ ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹ * (zdistD 3 5 (![1, 0, 0] : Zd 
3 5) : ℝ) ^ 2 * (((zdistD 3 5 (![2, 0, 0] : Zd 3 5) : ℝ) + 1) ^ 3)⁻¹
 private theorem probeInst8 (h : Prop8ZeroMode 3 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ∀ m : ℂ, (m = Complex.I ∨ m = probeE) → ∀ σ₁ σ₂ : Bool, ∀ a : Zd 3 5, ‖Theta0 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) 
* (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖ ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹ * (((zdistD 3 5 a : ℝ) + 1) ^ 1)⁻¹
### b4 Name clash, ports — Fri Oct  2 22:37:02 UTC 2026
$ echo "main $(git --no-optional-locks log -1 --format=%h main); changed since the base: $(git --no-optional-locks diff --name-only 3c11d7b main -- RBM3D RBM3D.lean | paste -sd' ' -); diff lines in the 12 inventory files: $(git --no-optional-locks diff --stat 3c11d7b main -- RBM3D/Propagator RBM3D/Test/InterfaceShape.lean RBM3D/Defs/{Params,Block,Tail,RadialSum,Shells,Convolution}.lean | wc -l | tr -d ' ')"
main 709c5c7; changed since the base: RBM3D.lean RBM3D/Defs/SemicircleIntegral.lean; diff lines in the 12 inventory files: 0
$ N=$(sed '/^\/-! ## Appendix A/,$d' RBM3D/Probe/T2003Pins.lean | grep -oE '^(private )?(noncomputable )?(abbrev|def|theorem|structure) [A-Za-z0-9_.]+' | awk '{print $NF}' | sed 's/.*\.//' | sort -u); echo "probe declaration names: $(echo $N | wc -w | tr -d ' '); files containing one: $(for b in main t/T2001 t/T2002 t/T2004 t/T2005; do echo "$b $(for n in $N; do git --no-optional-locks grep -lw -- "$n" $b -- RBM3D RBM3D.lean docs/tickets/checks; done | wc -l | tr -d ' ')"; done | paste -sd, -), $(for P in RBM1D RBM2D; do echo "$P $(for n in $N; do grep -rlw --include='*.lean' -- "$n" /Users/junyin/Lean_proof/$P/$P; done | wc -l | tr -d ' ')"; done | paste -sd, -)"
probe declaration names: 41; files containing one: main 0,t/T2001 0,t/T2002 0,t/T2004 0,t/T2005 0, RBM1D 0,RBM2D 0
$ R=/Users/junyin/Lean_proof/RBM2D; echo "RBM2D HEAD $(git -C $R --no-optional-locks log -1 --format=%h); c9a24cf..HEAD on RBM2D/Propagator:$(git -C $R --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Propagator | tail -1), $(git -C $R --no-optional-locks diff --name-status c9a24cf HEAD -- RBM2D/Propagator | cut -c1 | sort | uniq -c | tr -s ' ' | paste -sd, -)"; diff <(git -C $R --no-optional-locks diff --name-status c9a24cf HEAD -- RBM2D/Propagator | awk '$1=="D"{n=$2;sub(".*/","",n);sub(".lean","",n);print n}' | sort) <(awk '/^\(d\) /{print $2}' RBM3D/Probe/T2003Pins.lean | sort) && echo 'deleted files == class (d) rows of Appendix B'
RBM2D HEAD 79985ee; c9a24cf..HEAD on RBM2D/Propagator: 82 files changed, 2 insertions(+), 7715 deletions(-),  39 D, 43 M
deleted files == class (d) rows of Appendix B
(main differs from the branch base only by T2005's new file and its import line, none of the 12 inventory files. The 41 names are every declaration of the probe's Lean part (public and private, base names); none occurs on main, on the other ticket branches or in RBM1D/RBM2D, so no probe declaration is a port. RBM2D moved after c9a24cf (T2274 deleted exactly the 39 class-(d) files of Appendix B and trimmed 43 others); every RBM2D number in this report is c9a24cf.)
### b5 Item 1 — inventory (full lists: probe Appendices A, B) — Fri Oct  2 UTC 2026: RBM2D check 22:38:23, inv.py 22:38:46, grep 22:39:01
$ python3 inv.py RBM3D/Propagator/*.lean RBM3D/Test/InterfaceShape.lean RBM3D/Defs/{Params,Block,Tail,RadialSum,Shells,Convolution}.lean | sed 's/ lines, / L: /; s/ public decls.*//; s#RBM3D/##' | paste -sd';' - | fold -s -w 190
Propagator/Basic.lean 235 L: 17;Propagator/Deriv.lean 118 L: 5;Propagator/Gap.lean 604 L: 23;Propagator/Interface.lean 178 L: 6;Propagator/Props4.lean 281 L: 28;Test/InterfaceShape.lean 597 
L: 11;Defs/Params.lean 120 L: 8;Defs/Block.lean 141 L: 20;Defs/Tail.lean 169 L: 16;Defs/RadialSum.lean 563 L: 25;Defs/Shells.lean 130 L: 7;Defs/Convolution.lean 252 L: 10
$ grep -nE '^(noncomputable )?(def|theorem) (Theta|Theta0|ellT|Bparam|norm_Theta_apply_le|Theta0_apply_eq|exists_step|sum_Theta_real_row|Theta_eq_tsum_of_three_le|sum_radial_exp_le|card_sphere_le|zeroMode_le_of_ge|ellT_eq_of_le) ' RBM3D/Propagator/*.lean RBM3D/Defs/*.lean | sed 's#RBM3D/##; s/ :=.*//' | cut -c1-185 | sort -t: -k1,1 -k2,2n
Defs/Params.lean:32:noncomputable def ellT (L : ℕ) (g t : ℝ) : ℝ
Defs/Params.lean:36:noncomputable def Bparam (d L : ℕ) (g t : ℝ) (K : ℕ) : ℝ
Defs/RadialSum.lean:163:theorem sum_radial_exp_le (k : ℕ) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 1 ≤ ℓ) :
Defs/Shells.lean:101:theorem card_sphere_le (d r : ℕ) : sphereCard (d + 1) L r ≤ 2 ^ (d + 1) * (r + 1) ^ d
Defs/Tail.lean:119:theorem zeroMode_le_of_ge (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) {r : ℝ}
Defs/Tail.lean:143:theorem ellT_eq_of_le (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
Propagator/Basic.lean:70:noncomputable def Theta (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ
Propagator/Basic.lean:225:noncomputable def Theta0 (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ
Propagator/Gap.lean:88:theorem exists_step (hL : 3 ≤ L) {x : Zd d L} (hx : x ≠ 0) :
Propagator/Props4.lean:118:theorem Theta_eq_tsum_of_three_le (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
Propagator/Props4.lean:188:theorem norm_Theta_apply_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
Propagator/Props4.lean:203:theorem sum_Theta_real_row (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d L) :
Propagator/Props4.lean:243:theorem Theta0_apply_eq (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
$ R=/Users/junyin/Lean_proof/RBM2D; T=$(mktemp -d); git -C $R --no-optional-locks archive c9a24cf RBM2D/Propagator | tar -xf - -C $T; for f in $T/RBM2D/Propagator/*.lean; do echo "$(wc -l < $f | tr -d ' ') $(basename $f .lean)"; done | sort -k2 | diff - <(grep -E '^\([abcd]\) +[A-Za-z0-9]+ +[0-9]+ ' RBM3D/Probe/T2003Pins.lean | awk '{print $3, $2}' | sort -k2) && echo "87 rows of Appendix B == line counts of git archive c9a24cf: $(ls $T/RBM2D/Propagator | wc -l | tr -d ' ') files, $(cat $T/RBM2D/Propagator/*.lean | wc -l | tr -d ' ') lines"
87 rows of Appendix B == line counts of git archive c9a24cf: 87 files, 17266 lines
Class lists = the rows of Appendix B grouped by class (reached by RBM2D endpoints, `T2273-dead.md:357-443` at c9a24cf: 87 − 39 class-(d) files = 48 files, 17266 − 6117 = 11149 lines):
(a) dimension-free: 5 files, 1471 lines
    Basic(235*) Bounds(86*) Cutoff(610) Deriv(88*) GeomSum(452*)
(b) generalizes to Zd d L, exponents change: 32 files, 7663 lines
    AbelSum(126) ContinuumSymbol(251) Contour(353*) Dyadic(171) Elliptic(263) InvSymbolDiff(667) KinfSwap(47) Momentum(284*) PeriodizeConvergence(48) PeriodizeDelta(84)
    PeriodizeDescend(55) PeriodizeFourierDelta(105) PeriodizeImageSum(187*) PeriodizeIntegrand(262) PeriodizeKinfSummable(108) PeriodizeResolventBridge(109) PeriodizeShells(77)
    PeriodizeShift(40) PeriodizeStencil(96) PeriodizeTail(73) PeriodizeTorusStencil(98) ShellCutoff(516) ShellCutoffDiff(571) ShellKernelBound(892) ShellKernelFD(275)
    ShellSBP(596) Shells(224) Symbol(263*) SymbolDiff(382) SymbolReciprocalDiff(71) SymbolShiftAnnulus(227) ZeroMode(142)
(c) d=2-specific (log L, critical sums): 11 files, 2015 lines
    Decay(307) DecayLarge(159) DerivBounds(205) FiniteDiff(253) Harmonic(145) KinfBound(62) KinfBoundFirst(171) LatticeSum(170) LogIntegral(219) Prop5(178) Prop6(146)
(d) not needed (39 files = RBM2D dead code): 39 files, 6117 lines
    CombesThomas* 8 files 669 lines; Normalized* 21 files 3952 lines; PhysicalShell* 2 files 383 lines;
    Symbol{AnnulusNumerator,CutoffShell,DenomAnnulus,LowShell,LowShellE2,ReciprocalAnnulusBound,ReciprocalDiff2,ReciprocalDiff2Bound} 8 files 1113 lines
  * = used by route H (merged already / partly / optional): Basic Bounds Deriv merged; Symbol 46-263, Momentum 146-158, Contour 26-58,231-263, PeriodizeImageSum 25-124, GeomSum optional
### b6 Old interface (merged `Propagator/Interface.lean`): which files take it as a hypothesis — Fri Oct  2 22:39:24 UTC 2026
$ for n in ThetaDecay ThetaDecayShort ThetaZeroMode ThetaDiffOne ThetaDiffTwo PropTH; do echo "$n: $(grep -rlE "\(h[A-Za-z]* : (∀ i, )?$n( |\))" RBM3D --include='*.lean' | grep -v 'Probe/\|Propagator/Interface.lean' | sed 's#RBM3D/##; s#.lean##' | sort | tr '\n' ' ')"; done | paste -sd';' -
ThetaDecay: Kernel/SumDecay ;ThetaDecayShort: Kernel/Evolution Loop/Primitive Loop/PureLoop Loop/TreeThree Loop/Unique ;ThetaZeroMode: Kernel/Evolution ;ThetaDiffOne: ;ThetaDiffTwo: ;PropTH: 
(`ThetaDiffOne`, `ThetaDiffTwo`, `PropTH` have no consumer; they are false for c ≥ 1: `Prop6Old_false`, `Prop7Old_false`, `PropTH_false` compile, b1.)
### b7 Extreme inputs and route evidence (sources: probe Appendix C) — Fri Oct  2 UTC 2026: extreme.py 21:58:20 → 22:34:30, alld.py 22:34:12 → 22:34:24, bigg/laplace/route1d/kappa_sweep 21:58:21 → 21:58:30
$ python3 extreme.py   # d=3,4,5; e ≤ min(1,g²/3) down to 1e-9 and 0.1g²/L^d; g down to 0.001; L up to 193; `time`: 457.83s user, 36:09 wall
sup ratios, regime e <= min(1,g^2/3); P5: c=0.3; U1,U2s,U2m: unit differences; P6c/P7c: paper-literal |r|<=c|a| (axis+random r)
d=3 L= 17 g in (1, 0.5, 0.2, 0.05): P5=1.62 U1=5.51 U2s=9.63 U2m=33.14 P8=1.68 P6c0.5=2.76 P7c0.5=7.42 P6c0.9=7.43 P7c0.9=12.65  (1s)
d=3 L= 65 g in (1, 0.5, 0.2, 0.05): P5=1.73 U1=5.51 U2s=9.63 U2m=33.14 P8=1.74 P6c0.5=2.82 P7c0.5=7.75 P6c0.9=9.26 P7c0.9=16.46  (12s)
d=3 L=193 g in (1, 0.5, 0.2, 0.05): P5=1.75 U1=5.51 U2s=9.63 U2m=33.14 P8=1.76 P6c0.5=2.83 P7c0.5=7.83 P6c0.9=9.39 P7c0.9=17.25  (1304s)
d=3 L= 65 g in (0.005, 0.001): P5=1.56 U1=0.81 U2s=1.26 U2m=4.56 P8=0.27 P6c0.5=0.41 P7c0.5=1.11 P6c0.9=1.32 P7c0.9=2.35  (36s)
d=4 L= 33 g in (1, 0.5, 0.2, 0.05): P5=1.79 U1=10.91 U2s=33.87 U2m=101.15 P8=2.46 P6c0.5=7.15 P7c0.5=33.87 P6c0.9=87.24 P7c0.9=104.22  (578s)
d=5 L= 17 g in (1, 0.5, 0.2, 0.05): P5=2.58 U1=21.65 U2s=179.51 U2m=306.43 P8=11.69 P6c0.5=22.97 P7c0.5=179.51 P6c0.9=833.77 P7c0.9=967.28  (238s)
$ python3 alld.py 4 3 4 5 6 7 8 9 10 11 12 13 14 | tail -1; python3 alld.py 5 3 4 5 6 7 8 9 | tail -1   # all L at d = 4 and d = 5 (g in 1,.5,.2,.05; all e <= 1 incl. t = 0)
max over L: {'P5': (2.0, 'L=14'), 'U1': (16.0, 'L=3'), 'U2s': (57.67, 'L=4'), 'U2m': (162.0, 'L=3'), 'P8': (3.87, 'L=4'), 'P6c0.5': (6.41, 'L=14'), 'P7c0.5': (57.67, 'L=4')}
max over L: {'P5': (3.8, 'L=4'), 'U1': (32.0, 'L=3'), 'U2s': (346.01, 'L=4'), 'U2m': (486.0, 'L=3'), 'P8': (20.94, 'L=4'), 'P6c0.5': (28.11, 'L=4'), 'P7c0.5': (346.01, 'L=4')}
$ python3 bigg.py   # Λ-dependence: g = 1, 2, 4, all e ≤ 1 incl. t = 0
g    L    P5     U1     U2s    P8   | /(1+g^2): P5   U1    U2s   P8
1    17     2.00   8.00  16.00   2.00   |  1.00  4.00  8.00  1.00
2    17     5.49  20.00  40.00   5.99   |  1.10  4.00  8.00  1.20
4    17    19.76  68.00 136.00  23.23   |  1.16  4.00  8.00  1.37
1    33     2.00   8.00  16.00   2.00   |  1.00  4.00  8.00  1.00
2    33     5.86  20.00  40.00   6.15   |  1.17  4.00  8.00  1.23
4    33    21.80  68.00 136.00  23.85   |  1.28  4.00  8.00  1.40
$ python3 laplace.py | tail -1   # Θ(0,a) vs ∫_0^∞ e^{-es} Π_j hk(γs,a_j) ds, d=3, L=5, g∈{.1,.5,1}, t∈{.3,.9,.99}
  worst relative error: 2.20e-08
$ python3 route1d.py | sed -n 1p\;3p\;5p\;6p\;7p\;9p   # 1D kernel h_τ(n) = e^{-2τ}I_n(2τ) (FFT, 2^16 points)
== (R2) 1D bound  h_tau(n) <= C min(1,tau^-1/2) exp(-c min(n^2/tau,|n|)), n>=1 (n=0 separately: sup_tau h_tau(0) sqrt(1+tau) = 0.999 )
  c=0.15: sup C = 0.282 at (tau,n)=(5011.872, 1)
  c=0.25: sup C = 0.403 at (tau,n)=(87.916, 87)
  c=0.3: sup C = 17.156 at (tau,n)=(76.095, 76)
== (R3) first difference |h(n+1)-h(n)| <= C1 min(1,1/tau) exp(-c(..)),  second difference |h(n+1)+h(n-1)-2h(n)| <= C2 min(1,tau^-3/2) exp(-c(..)), n>=1
  c=0.15: C1 = 0.997 (n>=1 part 0.190 at (5011.872, 157)),  C2 = 1.994 (n>=1 part 1.157 at (0.001, 1))
$ python3 kappa_sweep.py | sed -n 2p\;5p\;7p   # σ₁=σ₂, μ = e^{2iφ}, κ = sin φ, L = 65
phi      kappa    P5     P5s(c=.1)   U1      U2s     P8     | kappa^2*P5s  kappa^2*P8  kappa^2*U1
 0.300   0.296   2.00       3.16    8.00   16.00    2.00 |      0.28       0.17       0.70
 0.050   0.050   2.00     107.26    8.00   16.00    2.00 |      0.27       0.00       0.02
### b8 Route and split tables (items 3, 7); evidence for S2–S4 is the b7 output
RBM2D at c9a24cf (ROUTES.md rows P3, P4): P5 closed with constants 180·40002², c = 1/20000 and a (1+log L) loss; P6 closed by route B2 with C₀ = 10^14 and a (1+log L) loss — the d = 2 logarithms that d ≥ 3 does not have.
Route per property (item 3).  P5 (any unit μ): route H below for μ = 1, other μ by merged `norm_Theta_apply_le` (Props4.lean:188).  P5s: gap + Neumann series (S7).  P6, P7: unit
differences from S4–S5 + path lemma (S8); σ₁ = σ₂ from P5s (|a+r| ≠ 0 since c < 1).  P8: `Θ̊(0,a) = ∫ e^{-es}(K_s(a) − L^{-d}) ds` (S4–S5, merged `Theta0_apply_eq`, Props4.lean:243).
H = the paper's random-walk route made exact: Θ = Σ_k t^k S^k is Poissonised, `1 − tS = e + γ Σ_j Δ_j` (γ = t g²/(1+2dg²), Δ_j the 1D Laplacian) so Θ(0,a) = ∫_0^∞ e^{-es} Π_j hk(γ s, a_j) ds with a 1D torus kernel.
Not the paper's Fourier summation by parts (P6–P8) and not RBM2D's contour/dyadic route F: RBM2D's P5 has no factor (|a|+1)^{-(d-2)} (d−2 = 0, `Prop5.lean:29-60`), so F's P5 would need an extra polynomial-decay argument (route B2's dyadic summation by parts is the one available).
| step | statement | reuse: RBM3D merged / RBM2D@c9a24cf file:lines / new | est. lines | risk |
| S1 | hk τ n := L⁻¹ Σ_{k ∈ 2πZ_L/L} e^{ikn − 2τ(1−cos k)} ≥ 0, Σ_n hk = 1, series e^{-2τ}Σ_j τ^j/j!·#{ε∈{±1}^j: Σε ≡ n} (Poisson weights) | `Zd`, `zdist`; Symbol.lean:46-176 (`chr`, orthogonality :152), 2D→1D; Mathlib `poissonMeasure` | 700 | M |
| S2 | Θ(0,a) = ∫_0^∞ e^{-es} Π_j hk(γs, a_j) ds via `1/x = ∫_0^∞ e^{-sx}ds`, Fourier rep of Θ in d dims | `Theta`, `SB_apply`, `eq_Theta_of_mul`; Symbol.lean:178-263 (`Theta_apply_fourier`), 2D→d | 450 | M |
| S3 | 1D on ℤ: h(n) ≤ C min(1,τ^{-1/2}) e^{-c min(n²/τ,n)} (Esscher tilt ν = min(n/4τ,1) + Gaussian bound of the tilted Fourier integral), first/second differences; torus: images (τ ≤ L²), gap hk − 1/L ≤ (C/L)e^{-cτ/L²} and differences L⁻², L⁻³ | `zdist_add_le`; Momentum.lean:146-158 (1−cos), Contour.lean:26-58,231-263, PeriodizeImageSum.lean:25-124; Mathlib `integral_gaussian`, `Real.mul_le_sin`, `Real.cosh_le_exp_half_sq` | 2200 | M–H |
| S4 | K_s(a) = Π_j hk: K_s ≤ C^d min(1,τ^{-d/2})e^{-c min(|a|²/τ,|a|)} (τ ≤ L²), ≤ (C/L)^d (τ ≥ L²); unit and second differences (Leibniz), K_s − L^{-d} | `Theta0_apply_eq`, `sum_Theta_real_row` | new | 600 | L–M |
| S5 | Laplace–Gauss integrals ∫e^{-es}F(s)ds, F ≲ min(1,(γs)^{-m/2})e^{-c(|a|²/γs ∧ |a|)}, m = d, d+1, d+2, regimes e ≥ γ, γ/L² ≤ e < γ, e < γ/L²; d ≥ 3 makes ∫^∞ s^{-d/2} converge | `Bparam`, `ellT`, `Bparam_mul_ellT_sq_le`, `ellT_eq_of_le`, `zeroMode_le_of_ge`, `sum_radial_exp_le`; (d=2 analogue LogIntegral.lean is class c) | new | 1100 | M–H |
| S6 | assembly P5 (t,g,L regimes of the preflight table) and P8 | `norm_Theta_apply_le`, `Theta_real_nonneg`; shape of Prop5.lean:29-60 | 700 | M |
| S7 | P5s: A = \|1−t s m²\| ≥ sin²φ, ρ = t(1−s)/A ≤ 1 − s sin²φ/2, Θ = Σ_k (1−tμs)^{-(k+1)}(tμg²s·Adj)^k, Adj^k(0,a) = 0 for k < \|a\| | `SB_apply`, `sbKernelR`, `norm_SB`; paper A.1 (BA-model argument, tex:40-55) | new | 450 | L |
| S8 | P6, P7: unit pins ⇒ \|r\| ≤ c\|a\| by a unit-step path (all points ≥ (1−c)\|a\| from 0), constant (1−c)^{-(d-1)} resp. (1−c)^{-d}; σ₁ = σ₂ from P5s | `exists_step` (Gap.lean:88), `zdistD_add_le`, `zdistD_neg`; shape of Dyadic.lean:95-135 | new | 800 | L–M |
| S9 | final `Prop5to8`, retire false `ThetaDiffOne/Two`, `PropTH`; update Test/Axioms.lean lists | probe bridges | none | 400 | L |
Total ≈ 7.4k lines.  Fallback F (RBM2D route generalised): classes (b) + (c) + Cutoff = 10.3k lines (Basic, Bounds, Deriv are merged; GeomSum optional), ×1.3 for `Fin d` bookkeeping, + 1.5k for P5's polynomial factor ≈ 15k lines, 14–17 tickets (estimates).
| ticket | file(s) under RBM3D/Propagator/ | main statements | sources | after | role (suggested) | lines |
| A | `Pins.lean`, `Prop5Short.lean` | pins of the probe (promoted, namespace RBM); bridges to `ThetaDecay/ThetaDecayShort/ThetaZeroMode`; `prop5Short_holds : ∀ d Λ κ, Prop5Short d Λ κ` | probe; paper A.1 BA-model argument (tex:40-55) | — | prover-hard | 700 |
| B1 | `HeatKernel1D.lean` | `hk`, `hk_nonneg`, `hk_sum`, series = Fourier sum, MGF `Σ_n hk e^{νn} = e^{2τ(cosh ν−1)}` on ℤ | RBM2D Symbol.lean:46-176 (1D) | — | prover-max, **pilot** | 700 |
| B2 | `HeatBounds1D.lean` | `hk_le`, `hk_diff1_le`, `hk_diff2_le` on ℤ (Esscher + local Fourier bound) | new; Mathlib Gaussian integral, Jordan | B1 | prover-max | 1100 |
| C | `HeatTorus1D.lean` | `hkL = Σ_y hk(· + Ly)`, `hkL_le` (τ ≤ L²), `hkL_sub_inv_le`, torus differences (τ ≥ L²) | RBM2D PeriodizeImageSum.lean:25-124 | B2 | prover-hard | 1100 |
| D | `HeatProduct.lean` | `Theta_eq_laplace_prod`, `Kprod` bounds, unit/second differences, zero-mode removed | RBM2D Symbol.lean:178-263 (2D→d) | C | prover-hard | 1050 |
| E | `LaplaceGauss.lean` | `laplace_gauss_5/6/7/8` from abstract kernel bounds (no `Theta`) | new | — | prover-hard | 1100 |
| F | `Prop5Hold.lean` | `prop5Decay_holds`, `prop8ZeroMode_holds` (μ = 1 core, other μ by property 4), unit pins | merged Props4 | C, D, E | prover-max | 700 |
| G | `Prop6Hold.lean` | path lemma, `prop6Diff1_holds`, `prop7Diff2_holds`, `prop5to8_holds`; retire false `ThetaDiffOne/Two`, `PropTH`; `Test/Axioms.lean` | merged `exists_step`; A, F | A, F | prover-hard | 950 |
Critical path B1 → B2 → C → D → F → G (6 sequential); A and E run in parallel from the start; ≈ 7.4k lines, 8 tickets (+ audits, rework) against DECISIONS §9 O2 (25/40/50); route F would be 14–17.
### b9 Narrative (pins, findings, decisions)
N1 Pins (b2): P5 = (prop:ThfadC), P5s = (prop:ThfadC_short), P6 = (prop:BD1), P7 = (prop:BD2), P8 = (prop:ThfadC0). Constants: `∃` after (d, Λ, κ, c), before L, g, t, m, σ, a, r — never a fixed λ: g ∈ (0, Λ]; t ∈ [0,1); `Θ_t^{(σ₁,σ₂)} = Theta d L g (t·m(σ₁)m(σ₂))`, m(+) = m, m(−) = m̄ (paper `def_mtzk`), ‖m‖ = 1, the bulk clause κ ≤ Im m is in P5s, P6, P7, P8 (idle for σ₁ ≠ σ₂, where Θ does not involve m) and not in P5; ℓ_t, B_{t,K} are `ellT`, `Bparam` (literal match of (eq:ellt), (eq_B_param); ℕ-subtraction d−2 harmless for d ≥ 3). 𝔡 must enter the constants: `Prop5_needs_Lambda` (compiled: no C works for all g > 0; at t = 0, Θ = 1, so C ≥ (1+g²)/(1+(1+g²)L^{-d}) → 1+Λ²; b7: at Λ = 1, 2, 4 sup P5, P8 ≈ (1+Λ²)·(1.0–1.4), U1, U2s = 4(1+Λ²), 8(1+Λ²)): T2003a.
N2 |r| ≲ |a|: pins carry |r| ≤ c|a|, 0 < c < 1 (parameter; constants blow up as c → 1). c = 1 is false: `Prop6Old_false`, `Prop7Old_false` refute the merged `ThetaDiffOne`, `ThetaDiffTwo` (hence `PropTH`) for every d ≥ 3, g > 0, ‖m‖ = 1 (t = 0, Θ = 1, r = −a); no merged theorem takes them as a hypothesis (b6).
N3 Loss: none for P6–P8 (stronger than ≺; (a) listed L^τ as the default and the loss-free pin as the optional strengthening). The route's sums converge for d ≥ 3 (the d = 2 log is ∫^∞ ds/s, absent here); b7: at d = 3 U1, U2s, U2m are identical for L = 17, 65, 193 and every other ratio changes by ≤ 5% from L = 65 to 193; d = 4, 5: see N5. The old L^τ form is derivable (`Prop8ZeroMode.thetaZeroMode`, `1 ≤ L^τ`, compiled). Scale: nothing to absorb, so the pins do not depend on T2002's scale parameter; were it N = (WL)^d or W, then L^τ ≤ N^{τ/d} and L ≤ W^{1/(d𝔠)} (W ≥ N^𝔠) would absorb the old L^τ. T2002's ticket and report are not on this ticket's reading list; nothing here depends on them.
N4 Merged consumers (`Loop/{PureLoop,Unique,TreeThree,Primitive}`, `Kernel/{Evolution,SumDecay}`) assume `ThetaDecayShort/ThetaDecay/ThetaZeroMode` (constants after g, m; loss L^τ); `Prop5Short.thetaDecayShort`, `Prop5Decay.thetaDecay`, `Prop8ZeroMode.thetaZeroMode` compile, so a proved pin feeds them unchanged.
N5 Extremes (b7; U1 := max_{x,j} |Θ(0,x+e_j) − Θ(0,x)|·(g²+e)(|x|+1)^{d−1}, U2s := max |Θ(x+e)+Θ(x−e)−2Θ(x)|·(g²+e)(|x|+1)^d, U2m the mixed second difference: the unit pins of S8). d = 3, g ∈ {1,.5,.2,.05}, t → 1 (e = 1e-9 and 0.1g²/L^d), L = 193: P5 ≤ 1.75 (c = 0.3), U1 ≤ 5.5, U2s ≤ 9.6, P8 ≤ 1.8, paper-literal P6, P7 at c = 1/2 ≤ 2.83, 7.83 and at c = 0.9 ≤ 9.4, 17.3, saturating in L; λ → 0 (g = 0.005, 0.001; L = 65): every ratio smaller (P5 1.56, P7c0.5 1.11). All L = 3…40, both parities: (a′) item 3 (P7c0.5 ≤ 12.51, at L = 4; falling along even L). d = 4, 5 (alld.py) the constants are larger and depend on the parity of L: P7c0.5 at d = 4 is 57.7 at L = 4, falling to 41.4 along even L ≤ 14, and 17.4 rising to 30.8 along odd L ≤ 13 (33.9 at L = 33); at d = 5, 346.0 at L = 4 falling to 274.2 at L = 8, and 70.4 rising to 152.2 along odd L ≤ 9 (179.5 at L = 17); no divergence at these sizes. At the bulk edge the P5s constant is ≈ 0.27κ^{-2} while U1, U2s, P8 stay ≤ 8, 16, 2 down to κ = 0.05. No tested input violates a pin.
N6 Route: H = the paper's random-walk route made exact (Poissonisation + tensorisation, S1–S5) for P5, P6–P8, gap/Neumann for P5s (S7). Not the paper's Fourier summation by parts (P6–P8), not RBM2D's contour/dyadic route F. H is new (neither in the paper nor in RBM2D): a route-level choice, reported to Jun in (d) (DECISIONS §7); S1 and the ℤ-line part of S3 (tickets B1, B2) are the go/no-go pilot; fallback F is priced under the route table.
BA reuse (item 6).  Shape: `PropThetaQ`, `Prop5DecayQ`, `PropThetaQ_Theta_eq`, `Prop5Decay.toQ` (probe): the five statements keep their form for any family `Q = M^{(σ₁,σ₂)} S^{(B)}` (BA: `S^{(B)} = 1`,
`M^{(σ₁,σ₂)}_{ab} = M^{(B)}_{ba}(σ₁) M^{(B)}_{ab}(σ₂)`); the RBM pin is the instance `Q = (m(σ₁)m(σ₂)) • SB`.  Reusable by gate BA unchanged: tickets A (shape, bridges), E (if stated on abstract kernel bounds),
the path lemma and σ₁ = σ₂ bookkeeping of G, and the gap argument of S7 (it needs only `Σ_{a≠0}|M'_{0a}| ≤ (1−ε)|1−t m²|`, the paper's (eq:off_diagM)).  Must be redone by BA: B1–D.  Tensorisation needs a nearest-neighbour
`S`; `M^{(+,−)}` is a general doubly stochastic kernel with exponential tails (`Mbound_AO`), so BA needs kernel bounds `K_s(a) ≲ …` from its symbol (Esscher tilt of `M^{(+,−)}` and `1 − M̂(θ) ≳ g²|θ|²`) or a perturbative
reduction; the paper adds `λ⁻¹`-dependence of the constants for `1 ≤ λ ≤ 𝔡⁻¹`.  BA-D1 prices this; it is not claimed here.

## (c) Mathlib names (verified: compiled in the probe, or `#check`ed / grepped in .lake/packages/mathlib/Mathlib)
Used in the probe: Complex.norm_exp_ofReal_mul_I, Complex.exp_ofReal_mul_I_re/_im, Real.cos_pi_div_three, Real.sin_pi_div_three, Complex.norm_I, Complex.norm_mul_exp_arg_mul_I, Complex.exp_add, Real.sqrt_eq_rpow, Real.sq_sqrt, Real.one_le_rpow, ZMod.val_natCast_of_lt, Matrix.one_apply/_eq/_ne, Finset.sum_eq_single, inv_le_one_of_one_le₀, inv_anti₀, pow_le_pow_left₀, pow_le_pow_right₀, div_le_iff₀, le_div_iff₀, exists_nat_ge.
Route, present: integral_gaussian (Gaussian/GaussianIntegral.lean:211); Real.mul_le_sin = Jordan (Trigonometric/Bounds.lean:83); Real.one_sub_sq_div_two_le_cos (:124); Real.cosh_le_exp_half_sq (Series.lean:154); Complex.integral_boundary_rect_eq_zero_of_differentiableOn (Complex/CauchyIntegral.lean:296);
  Complex.tsum_exp_neg_mul_int_sq (Gaussian/PoissonSummation.lean:117); integral_exp_neg_Ioi (ImproperIntegrals.lean:57); Real.integral_rpow_mul_exp_neg_mul_Ioi (Gamma/Basic.lean:465); MeasureTheory.integral_tsum (DominatedConvergence.lean:88); Finset.prod_univ_sum (BigOperators/Ring/Finset.lean:157);
  NormedSpace.exp_add_of_commute (Normed/Algebra/Exponential.lean:520); hasSum_fourier_series_of_summable (Fourier/AddCircle.lean:494); ProbabilityTheory.poissonMeasure (Poisson/Basic.lean:41; `poissonPMFReal` is deprecated); ProbabilityTheory.measure_ge_le_exp_mul_mgf (Probability/Moments/Basic.lean:429, Chernoff); MeasureTheory.Measure.tilted (MeasureTheory/Measure/Tilted.lean:42).
Absent (grep): Bessel I_n, heat kernel on ℤ^d or the torus, local limit theorem, the sharp central-binomial bound (only `Nat.centralBinom_le_four_pow`).
$ python3 mathlib_check.py   # source: probe Appendix C; run Fri Oct  2 22:44:24 → 22:44:34 UTC 2026 (cited file:line of the "Route, present" list and the absent names)
15/15 cited (name, file:line) pairs match, mismatches: []; files mentioning: modified Bessel / Bessel function 0, 'local limit' 0, 'heat kernel' 0; centralBinom_le_four_pow: 1 file

## (d) Open issues and paper-delta candidates
- T2003a: constants of properties 5–8 depend on (d, Λ), Λ = 𝔡⁻¹ ≥ λ (paper: "depending on d"); necessary: `Prop5_needs_Lambda`. T2003b: `|r| ≲ |a|` of 6, 7 means `|r| ≤ c|a|`, fixed 0 < c < 1, C = C(c, …); c ≥ 1 false (`Prop6Old_false`, `Prop7Old_false`).
- T2003c: `≺` of 6–8 replaced by explicit loss-free bounds (stronger than the paper). T2003d: (prop:ThfadC_short) from the explicit gap |1−t s m²| ≥ sin²φ (no [bourgade2019random]); bulk written κ ≤ Im m (|E| ≤ 2−κ₀ gives Im m ≥ (√3/2)√κ₀). T2003e: P5 pinned for every ‖m‖ = 1 (paper: bulk m; true by property 4, stronger). T2003f: |a| is the periodic ℓ¹ distance (old delta D2, `docs/paper-deltas.md:12`; `zdistD`, `Defs/Lattice.lean:70`).
- Old D11–D13: D11 kept (`Prop5Short` is σ₁ = σ₂ with κ); D12 superseded (false as written); D13 superseded (constants after g, m are unusable for λ → 0 and weaker than `lem_propTH`).
- For Jun (DECISIONS §7): route H is a route-level choice; confirm, with tickets B1+B2 as pilot (fallback F ≈ 15k lines, 14–17 tickets). Nothing here proves a pin: P5–P8 rest on numerics (b7) and the sketched route; the pilot is where the route can still fail.
- Dispatcher: T2004's local PT assumption must have constants before λ and λ ≤ Λ (DECISIONS §9 O1); the merged `thetaEdge` takes `m : Bool → ℂ` (`Loop/Partition.lean:166`), the pins take `m : ℂ` + `PropSpin`: they agree when `m false = conj (m true)`. Retire `ThetaDiffOne/Two`, `PropTH` (ticket G): `Test/Axioms.lean:74-75,116-120` lists them with fixed-L "certificates", which cannot see the failure as L → ∞. PT = 8 tickets (+ audits, rework) against DECISIONS §9 O2. Propose to `docs/mathlib-api.md`: the (c) lists.
- Result: items 1–7 delivered (inventory b5 and Appendices A, B; pins b2; route and split tables b8; skeleton and instances b3; BA reuse b9); the probe builds with the three standard axioms only; no tested input violates a pin; one open decision for Jun (route H pilot, above).
