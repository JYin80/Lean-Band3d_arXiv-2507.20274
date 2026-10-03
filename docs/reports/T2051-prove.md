Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 15:19:08 UTC 2026

Notation (paper `(eq_B_param)`, `1_2:1107`; merged `RBM.Bparam`, `RBM.BparamR`, `RBM.tailT`, `RBM.ellT`): `g = lam n`, `u = 1-t`, `A = (g²+|u|)⁻¹`,
`B_{t,m} = A (m+1)^{-(d-2)} + (L^d|u|)⁻¹` (non-increasing in `m`, `A ≥ 0`), `Φ(r) = (W^{-c₀} B_{t,min(⌊r⌋,K)})^{1/2}`, `0 ≤ K ≤ L`, `0 ≤ t ≤ 1`, `g ∈ (0,Λ]`.
`[s𝒯_t(r)]² = W^{-d} A (r+1)^{-(d-2)} e^{-√(r/ℓ_t)}` (`3_5:406-415`, `7_8:15-70`). Targets: (T1) verbatim copy of the probe definitions (no mathematics);
(T2a) `(eq:Psi)` for the B class; (T2b) the window; (T2c) `W^{-d}𝒯̃ ≍ [s𝒯]²`.

### (i) Exponent table
| Quantity | Value | Constraint it must satisfy | Slack |
|---|---|---|---|
| `d` | `≥ 3` (instance 3) | `2 ≤ d` suffices for `zeroMode_le_of_ge`; all constants below are explicit in `d` | none needed |
| `m(ℓ) = min(⌊ℓ⌋,K)` ratio | `(m(ℓ₂)+1)/(m(ℓ₁)+1) ≤ (ℓ₂+1)/ℓ₁ ≤ 2ℓ₂/ℓ₁` for `ℓ₂ ≥ ℓ₁ ≥ 1` | `⌊ℓ₁⌋+1 > ℓ₁`; `x ↦ min(x,K)+1` monotone with `(min(a,K)+1)/(min(b,K)+1) ≤ (a+1)/(b+1)` for `a ≥ b` | exact |
| `Φ(ℓ₁)/Φ(ℓ₂)` | `≤ (2ℓ₂/ℓ₁)^{(d-2)/2}` | `B_{m₁}/B_{m₂} ≤ ((m₂+1)/(m₁+1))^{d-2}` (`A (m₁+1)^{-(d-2)} + B₀ ≤ ρ[A (m₂+1)^{-(d-2)} + B₀]`, `ρ ≥ 1`) | uniform in `g,t,L,W,K,c₀` |
| `(C₁,C₂)` of `(eq:Psi)` | general `d`: `(2^d, d)`; `d = 3`: `(2, 2)` (ticket); also `d = 4`: `(2,2)` | `C₁,C₂ > 1` and `(2x)^{(d-2)/2} ≤ C₁ x^{C₂}` for `x ≥ 1`; `d=3`: `√2·x^{1/2} ≤ 2x²` | `d=3` grid: max `q/(2x²) = 0.5`; random d=3..6: max `q/(2^d x^d) ≤ 0.145` |
| `Cc(C)` (`Φ(0) ≤ Cc(C)Φ(ℓ)`, `0 ≤ ℓ ≤ C`, any `C>1`) | `(C+1)^{(d-2)/2}` | `B_0/B_m ≤ (m+1)^{d-2} ≤ (C+1)^{d-2}`, `m ≤ ⌊C⌋` | random max ratio over d=3..6 `0.9915-0.9965`; grid `0.9986` |
| shift constant `K_c` (`Φ(cr) ≤ K_c Φ(r)`) | `max(C₁c^{-C₂}, Cc(max(2,c⁻¹)))`; `d=3,(2,2)`: `c=1/4`: 32; `c=1/2`: 8; `c=2`: 1 (antitone) | `c ≥ 1` antitone; `c<1, cr ≥ 1` ratio bound; `cr < 1` the `Cc` clause | actual max `Φ(cr)/Φ(r)`: 1.996 (c=1/4), 1.413 (c=1/2), 1.0 (c=2) |
| `c₀` (B class) | `0 < c₀ ≤ d` (instance `c₀ = d = 3`) | `W^{-d/2} ≤ W^{-c₀/2}` needs `W ≥ 1`, `c₀ ≤ d` | `c₀ = d` is the endpoint |
| `C₃` (`LWClass`: `W^{-d/2} ≤ C₃ Φ(0)`) | `(1+Λ²)^{1/2}`, `Λ = 1`: `√2 = 1.4142` | `B_{t,0} ≥ A ≥ (g²+1)⁻¹ ≥ (1+Λ²)⁻¹` for `0 ≤ t ≤ 1`; then `Φ(0) ≥ W^{-c₀/2}(1+Λ²)^{-1/2} ≥ W^{-d/2}/C₃` | tightest tested ratio `W^{-3/2}/Φ(0) = 1.390` at `g=1` (grid below) |
| literal `Ψ=(W^{-d}B_{t,0})^{1/2} ≥ W^{-d/2}` | holds iff `B_{t,0} ≥ 1` | `B_{t,0}` can be `<1` when `g²+|1-t| > 1` (e.g. `g=1, t=1/16, L=3`: `0.556`) | FAILS literally (T2040a); fixed by `C₃` or `Ψ := max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})` |
| window of `Ψ=max(..)`: `LWWindow ε₀` | lower `W^{-d/2} ≤ Ψ` trivial; upper: `ε₀ ≤ d/2` and `W^{-d} B_{t,0} ≤ W^{-2ε₀}` eventually (data hypothesis) | the second is not deterministic: grid `W=2, g=0.1, t=1-g²/(4L²)` has `Ψ(0) = 5.37 > 1` | at `sz0`, `ε₀ = 1/5`: see (ii) |
| `ε₀` for B class `Φ ≤ W^{-ε₀}` | `ε₀ > 0`; by antitone only `Φ(0)` matters: `W^{-c₀}B_{t,0} ≤ W^{-2ε₀}` eventually | `ε₀ ≤ (c₀ - log_W B_{t,0})/2` | `sz0`, `c₀ = 3`, `ε₀ = 1/5`: best `ε₀` at n=0 is `1.4885` (t=1/16) and `0.5294` (`1-W^{-2}`), vs `0.2`: slack `≥ 0.33` |
| (c1) constant, `g²/L² ≤ 1-t`, `t<1`, `1 ≤ L`, `0 ≤ r' ≤ L` | `[s𝒯(r')]² ≤ W^{-d}𝒯_t(r') ≤ (1+2^{d-1})[s𝒯(r')]²` (`d=3`: 5) | `B₀ ≤ 2^{d-1} A (r'+1)^{-(d-2)}` = merged `zeroMode_le_of_ge`; independent of `g,W` | grid ratio in `[1.0014, 1.8916]` |
| (c1′) with truncation, `r' = r∧ℓ ≤ r ≤ L` | `W^{-d} tailW_D(r)` vs `[s𝒯(r')]² + W^{-d-D}`: `1/2 ≤ ratio ≤ 1+2^{d-1}` (`max ≤ sum ≤ 2 max`) | the paper's `W^{-D}` is `W^{-D-d}` here; same for all `D>0` after `D ↦ D+d` | grid `[0.5287, 1.8899]` |
| (c2) constant, `1-t ≤ g²/L²` (`ℓ_t = L`) | `e⁻¹ B_{t,r'} ≤ 𝒯_t(r') ≤ B_{t,r'}`, `0 ≤ r' ≤ L` | merged `ellT_eq_of_le`, `exp_tail_ge`; `[s𝒯]²` is NOT comparable here (zero-mode `(L^d|u|)⁻¹` unbounded as `t→1`) | grid ratio in `[0.3679, 1.0]` (`e⁻¹ = 0.3679`) |
| positivity | `B_{t,m} > 0` | `g > 0` (or `t ≠ 1`); `sz0`: `lam n > 0` | n/a |

### (ii) Concrete nondegenerate instance
Instance: merged `sz0` (`d=3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `RBM3D/Defs/Sizes.lean:260`), `n=0`: `L=4, W=32, g=1/64`;
`Λ = 1`, `c₀ = 3`, `ε₀ = 1/5`, `K = L`, `t ≡ 1/16` and `t = 1 - W^{-2}`. Both have `1-t ≥ g²/L²` for all `n` (regime (c1)); regime (c2) is covered on the grid only.
Hypotheses discharged: `0<c₀≤d`; `0≤t≤1`; `g∈(0,Λ]`; `g>0`; upper window `W^{-3}B_{t,0} ≤ W^{-2/5}` for all `n` (analytic limit: `t=1/16`: `B₀ ≤ 16/15+16/(15·64) < 1.1`, so
`W^{-3}B₀ ≤ 1.1 W^{-3} ≤ W^{-0.4}`; `t=1-W^{-2}`: `(g²+W^{-2})⁻¹ ≤ W²`, `(L^dW^{-2})⁻¹ = W²/L³ ≤ W²/64`, so `W^{-3}B₀ ≤ 1.016 W^{-1} ≤ W^{-0.4}` for `W ≥ 2`, and `eps0* → 1/2`).
Command (scripts in the scratchpad `T2051/`, no Lean) and verbatim output (`R1: t=1/16; R2: t=1-W^-2; R3: t=1-g²/(4L²)`; `1-t>` is `1-t ≥ g²/L²`, `ell_` is `ℓ_t = L`; `eps0* = -log_W max(W^{-3/2},(W^{-3}B₀)^{1/2})`, the best `ε₀`; `literal` says whether `max` equals the literal `(W^{-d}B₀)^{1/2}`):
```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2051 && (python3 chk.py; python3 gen.py)
W=2 L=3 g=0.1 R1 1-t> B0=   1.095 eps0*= 1.4346 literal=True  W^-1.5/PhiB(0)=0.956
W=2 L=3 g=0.1 R2 1-t> B0=   3.994 eps0*= 0.5010 literal=True  W^-1.5/PhiB(0)=0.500
W=2 L=3 g=0.1 R3 ell_ B0= 230.631 eps0*=-2.4247 literal=True  W^-1.5/PhiB(0)=0.066
W=2 L=3 g=1.0 R1 1-t> B0=   0.556 eps0*= 1.5000 literal=False W^-1.5/PhiB(0)=1.342
W=2 L=3 g=1.0 R2 1-t> B0=   0.948 eps0*= 1.5000 literal=False W^-1.5/PhiB(0)=1.027
W=2 L=3 g=1.0 R3 ell_ B0=   2.306 eps0*= 0.8972 literal=True  W^-1.5/PhiB(0)=0.658
W=2 L=9 g=0.1 R1 1-t> B0=   1.057 eps0*= 1.4601 literal=True  W^-1.5/PhiB(0)=0.973
W=2 L=9 g=0.1 R2 1-t> B0=   3.852 eps0*= 0.5273 literal=True  W^-1.5/PhiB(0)=0.510
W=2 L=9 g=0.1 R3 ell_ B0= 144.137 eps0*=-2.0856 literal=True  W^-1.5/PhiB(0)=0.083
W=2 L=9 g=1.0 R1 1-t> B0=   0.518 eps0*= 1.5000 literal=False W^-1.5/PhiB(0)=1.390
W=2 L=9 g=1.0 R2 1-t> B0=   0.805 eps0*= 1.5000 literal=False W^-1.5/PhiB(0)=1.114
W=2 L=9 g=1.0 R3 ell_ B0=   1.441 eps0*= 1.2363 literal=True  W^-1.5/PhiB(0)=0.833
W=8 L=3 g=0.1 R1 1-t> B0=   1.095 eps0*= 1.4782 literal=True  W^-1.5/PhiB(0)=0.956
W=8 L=3 g=0.1 R2 1-t> B0=  41.395 eps0*= 0.6048 literal=True  W^-1.5/PhiB(0)=0.155
W=8 L=3 g=0.1 R3 ell_ B0= 230.631 eps0*= 0.1918 literal=True  W^-1.5/PhiB(0)=0.066
W=8 L=3 g=1.0 R1 1-t> B0=   0.556 eps0*= 1.5000 literal=False W^-1.5/PhiB(0)=1.342
W=8 L=3 g=1.0 R2 ell_ B0=   3.355 eps0*= 1.2089 literal=True  W^-1.5/PhiB(0)=0.546
W=8 L=3 g=1.0 R3 ell_ B0=   2.306 eps0*= 1.2991 literal=True  W^-1.5/PhiB(0)=0.658
W=8 L=9 g=0.1 R1 1-t> B0=   1.057 eps0*= 1.4867 literal=True  W^-1.5/PhiB(0)=0.973
W=8 L=9 g=0.1 R2 1-t> B0=  39.112 eps0*= 0.6184 literal=True  W^-1.5/PhiB(0)=0.160
W=8 L=9 g=0.1 R3 ell_ B0= 144.137 eps0*= 0.3048 literal=True  W^-1.5/PhiB(0)=0.083
W=8 L=9 g=1.0 R1 1-t> B0=   0.518 eps0*= 1.5000 literal=False W^-1.5/PhiB(0)=1.390
W=8 L=9 g=1.0 R2 1-t> B0=   1.072 eps0*= 1.4832 literal=True  W^-1.5/PhiB(0)=0.966
W=8 L=9 g=1.0 R3 ell_ B0=   1.441 eps0*= 1.4121 literal=True  W^-1.5/PhiB(0)=0.833
cases 72 violations of (2,2)-ratio: 0
max ratios: {'shift1/4': 1.9958595292376382, 'shift1/2': 1.4132356204174794, 'shift2': 1.0, 'ratio/(2x^2)': 0.5, 'Phi0/Phil/sqrt(C+1)': 0.9986184137976946, 'lowwin C3-need': 1.3899722455264858}  C3=sqrt(1+Lam^2)= 1.4142135623730951
--- (c)
(c1) 1-t>=g^2/L^2: W^-d T / [sT]^2 in [1.0014,1.8916] over 90 pts; allowed [1, 1+2^(d-1)=5]
(c2) 1-t<=g^2/L^2: T/B_r in [0.3679,1.0000] over 54 pts; allowed [e^-1=0.3679,1]
W^-d tailW vs [sT(r^l)]^2+W^-(D+d): ratio range [0.5287,1.8899] allowed [1/2, 1+2^(d-1)=5]
--- sz0 (d=3): eps0=1/5, c0=3, n=0..2000
t=1/16 (u=15/16) : W^-3 B0 <= W^-2/5 all n: True | min rhs/lhs 7563.785 | 1-t>=g^2/L^2 all n: True
t=1-W^-2 (u=W^-2) : W^-3 B0 <= W^-2/5 all n: True | min rhs/lhs 9.808 | 1-t>=g^2/L^2 all n: True
n=0 t=1/16: B0=1.0831, W^-3 B0=3.305e-05 <= W^-0.4=2.500e-01; Psi=max(W^-1.5,(W^-3 B0)^.5)=0.0057; eps0*=1.4885
n=0 t=1-W^-2: B0=835.2000, W^-3 B0=2.549e-02 <= W^-0.4=2.500e-01; Psi=max(W^-1.5,(W^-3 B0)^.5)=0.1597; eps0*=0.5294
d=3: max q/(2x)^((d-2)/2)=0.8513  max q/(2^d x^d)=0.1448  max Phi0/Phil/(C+1)^((d-2)/2)=0.9962
d=4: max q/(2x)^((d-2)/2)=0.7374  max q/(2^d x^d)=0.0896  max Phi0/Phil/(C+1)^((d-2)/2)=0.9965
d=5: max q/(2x)^((d-2)/2)=0.6351  max q/(2^d x^d)=0.0544  max Phi0/Phil/(C+1)^((d-2)/2)=0.9915
d=6: max q/(2x)^((d-2)/2)=0.5616  max q/(2^d x^d)=0.0350  max Phi0/Phil/(C+1)^((d-2)/2)=0.9938
```
Reading: `violations of (2,2)-ratio: 0` over 72 (W,L,g,regime,K) cases and a real-`ℓ` grid; `Φ(cr)/Φ(r)` for `c ∈ {1/4,1/2,2}` max `1.996, 1.413, 1.0`; the window lower side holds with `C₃ = √2`
(`lowwin` need `1.390 ≤ 1.414`); the literal `Ψ` fails (`literal=False`, `W^{-1.5}/Φ_B(0) > 1`) at `g=1` in R1/R2, as in T2040a. `eps0* < 0` at `W=2, g=0.1, R3`: the upper window is a data
hypothesis, not a theorem (it holds at `sz0` and `n ≥ 0`, line `sz0 ... all n: True`). `R2`/`W=8,L=3,g=1` is in the `ℓ_t=L` regime (`1-t = 1/64 ≤ 1/9`).

### Verdicts
- Target 1 (verbatim copy of `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll`, `classB` text): PASS (no mathematics; hypotheses of the later targets are exactly those of these predicates).
- Target 2(a) `(eq:Psi)` for the B class, with `(C₁,C₂) = (2^d, d)` (and `(2,2)` at `d=3`), `Cc(C) = (C+1)^{(d-2)/2}`, shift constant as above, uniform in `g,t,L,W,K,c₀`: PASS.
- Target 2(b) window: PASS with the two pinning constraints of T2040a: lower side `C₃ = (1+Λ²)^{1/2}` (B class, `c₀ ≤ d`) or `Ψ = max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})`; upper side is the data hypothesis `W^{-c₀}B_{t,0} ≤ W^{-2ε₀}` (eventually) with `ε₀ ≤ d/2` for the `max` form; the literal `(W^{-d}B_{t,0})^{1/2} ≥ W^{-d/2}` is false in general.
- Target 2(c) `W^{-d}𝒯̃ ≍ [s𝒯]²` for `r' ≤ L`: PASS in two regimes with constants `(1, 1+2^{d-1})` (`g²/L² ≤ 1-t`; truncated form `[1/2, 1+2^{d-1}]` against `[s𝒯]²+W^{-d-D}`) and `(e⁻¹, 1)` against `B_{t,r'}` (`1-t ≤ g²/L²`); no single `≍ [s𝒯]²` holds in the second regime. Paper-delta candidates for T2040a, h, k: cite only (DECISIONS §24).

## (b) Script output — Sat Oct  3 15:32:14 UTC 2026

### Build, registry pre-check, hygiene (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2051`, branch `t/T2051`, commit `d8f8bd3`)
```
$ lake build RBM3D.Graph.LWPsi 2>&1 | grep -v "^trace" | tail -3
Build completed successfully (3313 jobs).
$ lake build 2>&1 | tail -1
Build completed successfully (3777 jobs).
$ cat pre.lean   # not committed, in the scratchpad
import RBM3D
import RBM3D.Graph.LWPsi
#assert_rbm_axioms
$ lake env lean pre.lean > pre.out; echo exit $?; grep -E "^axiom audit|^premises found|^registry: [0-9]+ borrowed" pre.out | cut -c1-110
exit 0
axiom audit: 1963 theorems, 834 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 47 (borrowed 2, owed 32, structural 13).
registry: 5 borrowed + 43 owed + 25 structural; 26 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/LWPsi.lean; echo grep-exit $?
grep-exit 1
$ git diff --stat main...t/T2051
 RBM3D/Graph/LWPsi.lean | 813 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 813 insertions(+)
```

### `#print axioms` (ax.lean: one `#print axioms` per public target and per `inst_*` theorem)
```
$ grep -c "^#print axioms" ax.lean
35
$ lake env lean ax.lean 2>&1 | sed -E "s/^.* depends on axioms: //" | sort | uniq -c
  35 [propext, Classical.choice, Quot.sound]
```

### The copied definitions equal the probe (`eeda441:RBM3D/Probe/T2040Graphs.lean`)
```
$ git show eeda441:RBM3D/Probe/T2040Graphs.lean > probe.lean; python3 cmp.py   # exact multi-line substring test of the probe lines
LWWindow probe lines 918-920 (with docstring): verbatim in LWPsi.lean = True
LWClass probe lines 928-932 (with docstring): verbatim in LWPsi.lean = True
LWPsiRel probe lines 934-941 (with docstring): verbatim in LWPsi.lean = True
LWPsiAll probe lines 1076-1078 (with docstring): verbatim in LWPsi.lean = True
```

### Target statements, extracted by script (`extract.py`) from `RBM3D/Graph/LWPsi.lean`
```lean
def LWPhiB (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) : ℕ → ℝ → ℝ :=
  fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
    Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)

theorem LWPhiB_psiRel (hd : 2 ≤ d) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) :
    LWPsiRel ((2 : ℝ) ^ d) (d : ℝ) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t) := by

theorem LWPhiB_psiRel_three (hd : d = 3) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) :
    LWPsiRel 2 2 (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t) := by

theorem LWPhiB_shift (hd : 2 ≤ d) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
      LWPhiB sz c₀ K t n (c * r) ≤ Kc * LWPhiB sz c₀ K t n r := by

theorem LWPsiAll.shift {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h : LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ n (c * r) ≤ K * Φ n r := by

theorem LWWindow_max {ε₀ : ℝ} (hε : ε₀ ≤ (d : ℝ) / 2) {Φ₀ : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, Φ₀ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) :
    LWWindow sz ε₀ (fun n => max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ₀ n)) := by

theorem LWWindow_max_Bctl {ε₀ : ℝ} (hε : ε₀ ≤ (d : ℝ) / 2) (t : ℕ → ℝ)
    (h : ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWWindow sz ε₀ (fun n => max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) := by

theorem LWPsiMax_asymp {ε₀ C₃ : ℝ} {Φ : ℕ → ℝ → ℝ} (h : LWClass sz ε₀ C₃ Φ) :
    ∀ᶠ n in atTop, Φ n 0 ≤ max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ n 0) ∧
      max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ n 0) ≤ max 1 C₃ * Φ n 0 := by

theorem LWClass_B {ε₀ c₀ Λ : ℝ} (K : ℕ → ℕ) (t : ℕ → ℝ) (hc₀ : c₀ ≤ (d : ℝ))
    (hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1)
    (hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWClass sz ε₀ (Real.sqrt (1 + Λ ^ 2)) (LWPhiB sz c₀ K t) := by

theorem LWPhiB_psiAll (hd : 2 ≤ d) {ε₀ c₀ Λ : ℝ} (K : ℕ → ℕ) (t : ℕ → ℝ) (hε : 0 < ε₀)
    (hc₀ : c₀ ≤ (d : ℝ)) (hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1)
    (hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWPsiAll sz ε₀ ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + Λ ^ 2))
      (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t) :=

theorem tailT_regime1_bounds {d L : ℕ} {W g t : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1)
    (hW : 0 < W) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    sfT d L W g t r ^ 2 ≤ (W ^ d)⁻¹ * tailT d L g t r ∧
      (W ^ d)⁻¹ * tailT d L g t r ≤ (1 + 2 ^ (d - 1)) * sfT d L W g t r ^ 2 := by

theorem tailW_regime1_bounds {d L : ℕ} {W g t ℓ D : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1)
    (hW : 0 < W) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    (1 / 2) * (sfT d L W g t (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) ≤
        (W ^ d)⁻¹ * tailW d L g t ℓ W D r ∧
      (W ^ d)⁻¹ * tailW d L g t ℓ W D r ≤
        (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) := by

theorem tailT_regime2_bounds {d L : ℕ} {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    Real.exp (-1) * BparamR d L g t r ≤ tailT d L g t r ∧ tailT d L g t r ≤ BparamR d L g t r := by

theorem tailW_regime2_bounds {d L : ℕ} {W g t ℓ D : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    max (Real.exp (-1) * BparamR d L g t (min r ℓ)) (W ^ (-D)) ≤ tailW d L g t ℓ W D r ∧
      tailW d L g t ℓ W D r ≤ max (BparamR d L g t (min r ℓ)) (W ^ (-D)) := by
```

### Compiled nonempty instances (`RBM.Gauss.LWPsiInst`: 23 theorems `inst_*`, lines 652-813; two shown, extracted by `extract2.py`)
```lean
theorem inst_psiRel_three_tInst : LWPsiRel 2 2 (fun C => Real.sqrt ((C + 1) ^ (3 - 2)))
    (LWPhiB sz0 3 (fun n => sz0.L n) tInst) :=
  LWPhiB_psiRel_three sz0 rfl 3 _ tInst

theorem inst_tail1_tInst (n : ℕ) :
    sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n) 2 ^ 2 ≤
        (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailT 3 (sz0.L n) (sz0.lam n) (tInst n) 2 ∧
      (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailT 3 (sz0.L n) (sz0.lam n) (tInst n) 2 ≤
        (1 + 2 ^ (3 - 1)) * sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n) 2 ^ 2 :=
  tailT_regime1_bounds (by norm_num) (by have := L_ge_4 n; linarith) (by simp [tInst]; norm_num)
    (W_pos' n) (hgt_tInst n) (by norm_num) (by have := L_ge_4 n; linarith)
```

### Name-clash grep
```
$ bash clash.sh | grep -vc "= *0$"   # 22 names, grep -rnE "(def|theorem|lemma|abbrev|namespace|structure) NAME" RBM3D RBM3D.lean --include=*.lean, LWPsi.lean excluded; count of names with a hit
0
$ bash clash.sh | wc -l   # names checked
      22
```

### Narrative (what the file proves; every line below is checkable in the script output above or in the file)
- One new file `RBM3D/Graph/LWPsi.lean` (813 lines, commit above); `RBM3D/Test/Axioms.lean` is not edited: the pre-check exits 0 with no unclassified premise (the four class predicates are `Prop` definitions that this file proves for the B class, `LWWindow_max`, `LWClass_B`, `LWPhiB_psiRel`, `LWPhiB_psiAll`).
- Target 1: `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll` are probe text with docstrings (four `True` above). The probe has no definition called `classB`: `classB` (probe :1939) is a theorem about `ΦB` (probe :1906, `c₀ = 1`, `K ≡ 1`); the B-class definition used by `LWtermB` is the lambda at probe :970-973, here `LWPhiB sz c₀ K t` (new name, same term).
- Target 2(a): `LWPhiB_psiRel` proves `(eq:Psi)` for `LWPhiB` for every `n`, with no hypothesis on `t, g, L, W, K, c₀` (only `2 ≤ d`): antitone, `Cc C = ((C+1)^{d-2})^{1/2}`, `(C₁, C₂) = (2^d, d)`. `LWPhiB_psiRel_three` gives `(2, 2)` at `d = 3` (the ticket's constants; for general `d` the exponent `d` is what the argument gives, so `(2, 2)` is stated only at `d = 3`).
- `LWPsiAll.shift` has the probe's statement (probe :1200) and is proved through the private `LWPsi_shift_aux`, which needs only `Ψ_t ≥ 0`; the probe's proof text was not copied. `LWPhiB_shift` is the unconditional B-class version (`Kc` independent of `n`).
- Target 2(b): `LWWindow_max_Bctl`: `Ψ_t = max(W^{-d/2}, √Bctl)` has `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` iff `Bctl ≤ W^{-2ε₀}` eventually (sufficient direction proved; hypotheses `ε₀ ≤ d/2` and that bound). `LWClass_B`: for `c₀ ≤ d`, `0 ≤ t ≤ 1`, `0 < g ≤ Λ` and `W^{-c₀}B_{t,0} ≤ W^{-2ε₀}` (all eventually), `LWClass` holds with `C₃ = √(1+Λ²)`; `LWPsiMax_asymp` gives `max(W^{-d/2}, Φ(0)) ≤ max(1, C₃) Φ(0)`. The upper window is a data hypothesis, not a theorem (preflight (a): negative values of `eps0*` at `W = 2`, `g = 0.1`, `t = 1 - g²/(4L²)`).
- Target 2(c): `tailT_regime1_bounds` (`1 - t ≥ g²/L²`, `0 ≤ r ≤ L`): `[s𝒯]² ≤ W^{-d}𝒯 ≤ (1 + 2^{d-1})[s𝒯]²`, via the merged `zeroMode_le_of_ge`; `tailW_regime1_bounds`: the truncated form against `[s𝒯(r∧ℓ)]² + W^{-d}W^{-D}`, constants `1/2` and `1 + 2^{d-1}`. `tailT/tailW_regime2_bounds` (`1 - t ≤ g²/L²`): `e⁻¹ B ≤ 𝒯 ≤ B`, via merged `exp_tail_ge`; `[s𝒯]²` is not comparable there (preflight (a) row (c2)).
- Instances (`RBM.Gauss.LWPsiInst`, `sz0`, `d = 3`, `c₀ = 3`, `ε₀ = 1/5`, `Λ = 1`, `K = L`): each target at `tInst ≡ 1/16` and at `tW = 1 - W^{-2}`, every deterministic hypothesis proved for all `n` (`upper_core`: `W^{-3}B_{t,0} ≤ W^{-2/5}` from `B_{t,0} ≤ 2W²`, `W ≥ 32`). Regime 2 is empty at both ticket times (`hgt_tInst`, `hgt_tW` give `1 - t ≥ g²/L²` for all `n`; strict by the formulas `lam² = (2(n+1))^{-12}`, `W^{-2} = (2(n+1))^{-10}`, `L² ≥ 16`), so `inst_tail2`, `inst_tailW2` use `n = 0` (`L = 4`, `g = 1/64` via `sz0_values`) and `t = 1 - 1/131072`.
- Section (a) needed no correction: its constants `(2^d, d)`, `(2, 2)`, `Cc`, `C₃`, `(1, 1+2^{d-1})`, `(e⁻¹, 1)`, `(1/2, 1+2^{d-1})` are the ones proved; no (a′).
- Not done by this ticket (as the ticket says): the sequence-level pins `LWterm`, `LWtermB`, `LWtermExp`, ...; no blueprint edit.

## (c) Verified Mathlib names (all compiled in `LWPsi.lean`)
- `Real.sqrt_le_left`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul`, `Real.sqrt_eq_rpow`, `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.sqrt_nonneg`, `Real.le_sqrt_of_sq_le`
- `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_two`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`
- `Real.exp_pos`, `Real.exp_add`, `Real.exp_le_one_iff`
- `Nat.floor_mono`, `Nat.floor_le`, `Nat.floor_zero`, `Nat.lt_floor_add_one`, `Nat.one_le_cast`, `Nat.zero_min`
- `inv_anti₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `one_lt_pow₀`, `one_le_div`, `div_le_div₀`, `div_le_iff₀`, `mul_max_of_nonneg`, `mul_inv_cancel₀`, `max_le_max`, `inv_pow`, `inv_inv`, `abs_of_nonneg`, `abs_of_pos`
- Merged RBM names used: `Bparam`, `BparamR`, `tailT`, `tailW`, `ellT`, `sfT`, `Sizes.Bctl`, `zeroMode_le_of_ge`, `exp_tail_ge`, `BparamR_nonneg`, `SizesInst.sz0`, `sz0_values`, `InductionDefsInst.tInst`, `W_ge_32`.
- Verified absent: none searched.

## (d) Open issues and paper-delta candidates
- T2040a, T2040h, T2040k: cited, not re-proposed (DECISIONS §24). The proofs of this file are the deterministic parts they need (`LWWindow_max_Bctl`/`LWClass_B`; `LWPsiRel` as a predicate on `Φ`; `tailT_regime1_bounds`/`tailT_regime2_bounds`).
- T2051a (new): the paper's `W^{-d}wT^ℓ_{t,D}(r) ≍ [sT_t(r∧ℓ)]² + W^{-D}` (`7_8:21`, regime `1-t > ĝ²/L²`) holds in Lean with `W^{-d}W^{-D}` in place of `W^{-D}` (`tailW` = `max(𝒯, W^{-D})` has no factor `W^{-d}`); a lower bound with `W^{-D}` is false for `W^{-d-D} ≪ W^{-D}`. Same for all `D > 0` after `D ↦ D + d`, so the paper's "for any large `D`" is unaffected. Proposed as T2051a.
- Open: the upper window `Ψ_t ≤ W^{-ε₀}` is a hypothesis of `LWWindow_max(_Bctl)` and `LWClass_B`; it must be supplied by the ST chain's size/time facts (at `sz0` and the two times it is proved by `upper_core`).
- Open (ticket vs. fact): the ticket asks every theorem at `t = 1 - W^{-2}`; the regime-2 theorems cannot be applied there (empty hypothesis), see the instance paragraph above.
