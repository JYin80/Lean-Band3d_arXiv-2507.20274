Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 04:15:51 UTC 2026

Notation: `e = 1-t`, `γ = lgGam d g t = t g²/(1+2dg²)`, `ε = e/γ`, `n = zdistD d L a ≤ dL/2`, `ℓ = ellT L g t`,
`μ = PropSpin m σ₁ · PropSpin m σ₂`. Upstream constants (all merged theorems, none a hypothesis; read from the sources):
`kProd_le`: `K_τ ≤ C_K min(1,τ^{-d/2}) e^{-c_K min(n²/τ,n)}` for `τ ≤ L²` (`C_K = A^d, c_K = c_f/d`, HeatProduct.lean:446);
`kProd_gap`: `|K_τ-L^{-d}| ≤ C_G L^{-d} e^{-c_Gτ/L²}` for `τ ≥ L²` (`C_G = d(1+Cg)^d, c_G = cg`, :640);
`lg_bulk (m=d, c=c_K)`: `C_B = (d-1)!(2/c_K)^{d-1} + Γ(d/2-1)(c_K/2)^{-(d-2)/2}`, `c' = min(c_K/2,1)`;
`lg_zero`: `C_0 = 1+2/(d-2) ≤ 3`; `lg_convA`: `C_A = 3+4dΛ²+2Λ²` (LaplaceGauss.lean:213); `lg_convB, lg_convC`: constants 1 and `d/2`.
Auxiliary: `M(b) = sup_{x≥0}(1+x)^{d-2}e^{-bx} = max(1,((d-2)/(be))^{d-2}e^{b})` (checked below); `P_d = (d/2+1)^{d-2}`.

### (i) Exponent / constant table

| step (regime) | statement used | constant | constraint / slack |
|---|---|---|---|
| reduction | `‖Θ_{tμ}(0,a)‖ ≤ Re Θ_t(0,a)` (`norm_Theta_apply_le`), `μ=m m̄=1` iff `σ₁≠σ₂` | none | slack in numerics: max `|Θ_{tμ}|-ReΘ_t` = 8e-17 (output 1) |
| `t = 0` (P5) | `Θ=1_{a=0}`, `γ=0`: no `τ=γs`, separate case | `C ≥ Λ²+1` | `B(0) ≥ 1/(g²+1) ≥ 1/(Λ²+1)`; `a≠0`: `Θ=0` |
| `t = 0` (P8) | `Θ̊ = 1_{a=0}-L^{-d}`, `|Θ̊| ≤ 1` | `C ≥ (Λ²+1)P_d` | `L^{-d} ≤ L^{-(d-2)} ≤ P_d (n+1)^{-(d-2)}` (`n+1 ≤ (d/2+1)L`) |
| split `(0,L²] ∪ (L²,∞)` | `Θ_t(0,a)=γ⁻¹∫e^{-ετ}K_τ dτ` (`Theta_eq_laplace_prod`, `0<t<1`) | exact | head+tail = Θ to 1e-7 (output 2 assert) |
| tail, all regimes | `K_τ ≤ (1+C_G)L^{-d}`, `lg_tail` (κ=0): `γ⁻¹(1+C_G)L^{-d}e^{-εL²}/ε` | `1+C_G` | `= (1+C_G)e^{-εL²}/(L^d e)`; realised `L^dK_{L²}(0) = 1.0000` (L=3..17) |
| (R1) `ε ≥ 1`, `n ≥ 1` | `lg_bulk` 2nd: head `≤ C_K γ⁻¹(2/ε)e^{-c'n} = 2C_K e^{-c'n}/e`; `1/e ≤ C_A/(g²+e)` (`lg_convA` 1st); `e^{-c'n} ≤ M(c'/2)(n+1)^{-(d-2)}e^{-(c'/2)n/ℓ}` (`ℓ≥1`) | `2C_K C_A M(c'/2)` | `ε≥1 ≥ L^{-2}` so zero mode: `e^{-εL²} ≤ e^{-(2/d)n/ℓ}` (`lg_convC`) |
| (R2) `L^{-2} ≤ ε < 1`, `n≥1` | `lg_bulk` 1st: head `≤ C_K C_B γ⁻¹ n^{-(d-2)}e^{-c'n√ε}`; `γ⁻¹ ≤ C_A/(g²+e)` (`lg_convA` 2nd); `1/ℓ ≤ √ε` (`lg_convB`); `n^{-(d-2)} ≤ 2^{d-2}(n+1)^{-(d-2)}` | `C_K C_B C_A 2^{d-2}` | exponent `c'` ≥ target `c`; zero mode as R1 via `lg_convC` |
| (R3) `ε < L^{-2}` | `ℓ = L` (`lg_convB` 2nd), `n/ℓ ≤ d/2`; head as R2 with `e^{-c'n√ε} ≤ 1 ≤ e^{cd/2}e^{-cn/L}`; tail `e^{-εL²} ≤ 1` | `C_K C_B C_A 2^{d-2}e^{cd/2}`, `(1+C_G)e^{cd/2}` | `L^{-2}<1` (`L≥3`) so `ε<1`, `lg_convA` 2nd applies; `ε>0` since `t<1` |
| (R4) `n = 0` | `lg_zero`: `min(C_0,1/ε)`: `ε<1`: `γ⁻¹C_0 ≤ C_0C_A/(g²+e)`; `ε≥1`: `γ⁻¹/ε = 1/e ≤ C_A/(g²+e)` | `C_K C_0 C_A` | `e^{-0}=1`; tail `(1+C_G)/(L^d e)` |
| **P5 final** | one `c`, one `C` after `(d,Λ)`; all regimes `ε>0` covered by R1–R4 | `c = min(c'/2, 2/d)`; `C = max(Λ²+1, head consts above, (1+C_G)e^{cd/2})` | head and tail bound the two summands of `B` separately, so `max`, not sum |
| P8 `σ₁≠σ₂`, head K | as R1–R4 without the exponential (`≤ C_K C_A max(C_0, 2M(c'), C_B2^{d-2})(g²+e)⁻¹(n+1)^{-(d-2)}`) | as left | `(0,L²]`: `|K-L^{-d}| ≤ K+L^{-d}` |
| P8 `σ₁≠σ₂`, `L^{-d}` head | keep `e^{-ετ}`: `γ⁻¹L^{-d}∫_0^{L²}e^{-ετ} ≤ L^{-d}min(L²/γ,1/e)` (`lg_tail` 3rd) `≤ C_A L^{-(d-2)}/(g²+e)`; `ε<1`: `γ⁻¹`, `ε≥1`: `1/e` | `C_A P_d` | numeric ratio `zhead/(L^{-d}min(L²/γ,1/e)) ≤ 1.000` (output 2); without `e^{-ετ}` the bound fails as `g→0` (Fable F5 (d)) |
| P8 `σ₁≠σ₂`, tail | `|K-L^{-d}| ≤ C_G L^{-d}e^{-c_Gτ/L²}`; `lg_tail` 1st+2nd: `C_G L^{-d}min(1/e, L²/(c_Gγ))` | `C_G C_A max(1,1/c_G) P_d` | no `(L^de)⁻¹` survives (target has none); numeric tail max 0.000 |
| P8 `σ₁=σ₂`, `t>0`, bulk `κ≤Im m` | `Θ̊ = Θ - L^{-d}(1-tμ)⁻¹`; `prop5Short_holds` (consts `C_s,c_s` of `(d,Λ,κ)`); `|1-tμ|² = (1-t)²+4t sin²φ ≥ κ⁴` (`κ ≤ 1`, `μ=m²` or `m̄²`) | `C_s(Λ²+1)(1+Λ²M(c_s)) + κ⁻²(Λ²+1)P_d` | `1_{a=0} ≤ (Λ²+1)/(g²+e)`; `g² ≤ Λ²(Λ²+1)/(g²+e)`; `κ>1` impossible (`Im m ≤ 1`), vacuous; grid min `|1-tμ|²/κ⁴ = 1.0` (output 2) |
| P8 final | `C = max(t=0 row, σ≠ sum, σ= row)`, depends on `(d,Λ,κ)` only | explicit | pin quantifies `∃C` after `(d,Λ,κ)`, as here |

Dimension: `d ≥ 3` is used only in `lg_bulk/lg_zero` (`m=d ≥ 3`, `Γ(d/2-1)` finite, `C_0 = 1+2/(d-2)`); `Bparam`'s exponent `d-2` is ℕ-subtraction, equal to the paper's for `d ≥ 3`.
Slack in the pins: none of the three exponents is tight (the exact Θ ratios below are ≤ 2 for `Λ=1`, `c=0.3`), only the constants `C_K, C_G, C_B` are large.

### (ii) Concrete instance

Data: `d=3, Λ=1, κ=1/2, L=5, g=1/2, t=9/10, m=I, σ₁=true, σ₂=false, a=0` (`μ = m m̄ = 1`, `ε = 10/9 ≥ 1`: regime R1/R4 at `n=0`;
`C_A = 3+12+2 = 17`). Every hypothesis: `3≤d`, `0<Λ`, `0<κ`, `3≤L`, `0<g≤Λ`, `0≤t<1`, `‖m‖=1`, `κ ≤ Im m = 1`. Upstream limit
computations: not needed, all inputs are merged theorems (`kProd_le, kProd_gap, lg_*, Theta_eq_laplace_prod, prop5Short_holds`), none is a hypothesis of a target.
Scripts (numpy, exact Fourier sum `Θ(0,·) = ifftn 1/(1-ξλ_k)`, `λ_k = (1+2g²Σcos k_j)/(1+2dg²)`), in
`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/`.

Command 1: `python3 pf.py` — ticket grid `d=3, L∈{3,5,9,17}, g∈{.05,.5,1}, t∈{0,.5,1-g²,1-g²/L²,1-g²/L³}`, all `a`, `μ ∈ {1,m²,m̄²}`, `sinφ ∈ {1,.5}`;
P5 ratio uses `c=0.3`, P8 ratio is `|Θ̊|(g²+e)(n+1)^{d-2}`:
```
regime counts (t>0 rows): {'eps>=1': 20, 'Linv2<=eps<1': 14, 'eps<Linv2': 10}
max (|Theta_{t mu}|-Re Theta_t) over all rows (property 4, want <=1e-12): 8.071566291162673e-17
max P5 ratio |Theta|/(B e^{-0.3 n/ell}) over all (L,g,t,phi,mu,a): 1.999
max P8 ratio (sigma1!=sigma2, mu=1) |Theta0|(g^2+e)(n+1)^(d-2): 2.0
max P8 ratio (sigma1==sigma2, mu=m^2/mbar^2, bulk): 2.0
```
Command 2: `python3 pf2.py` — exact head/tail split at `τ=L²` (Fourier: head `= L^{-d}Σe^{ika}(1-e^{-(ε+μ_k)L²})/(e+γμ_k)`), per-regime ratios (`c=0.1`),
`M(c'/2)` closed form vs brute force, `|1-tμ|²/κ⁴` grid; regimes A/B/C = R1/R2/R3 above:
```
L=3  L^d*K_{L^2}(0) = 1.0000 ; L^2*(2-2cos(2pi/L)) = 27.000
L=5  L^d*K_{L^2}(0) = 1.0000 ; L^2*(2-2cos(2pi/L)) = 34.549
L=9  L^d*K_{L^2}(0) = 1.0000 ; L^2*(2-2cos(2pi/L)) = 37.901
L=17  L^d*K_{L^2}(0) = 1.0000 ; L^2*(2-2cos(2pi/L)) = 39.031
A:eps>=1 rows=20  P5 head/shape(c=0.1) max=1.685  P5 tail/(L^d e)^-1 shape max=0.000  P8 head max=1.678  P8 tail max=0.000  zhead/(L^-d min(L^2/gam,1/e)) max=1.000
B:Linv2<=eps<1 rows=14  P5 head/shape(c=0.1) max=5.315  P5 tail/(L^d e)^-1 shape max=0.417  P8 head max=1.658  P8 tail max=0.000  zhead/(L^-d min(L^2/gam,1/e)) max=1.000
C:eps<Linv2 rows=10  P5 head/shape(c=0.1) max=8.973  P5 tail/(L^d e)^-1 shape max=1.085  P8 head max=1.675  P8 tail max=0.000  zhead/(L^-d min(L^2/gam,1/e)) max=0.971
c'=0.05 sup_x (1+x)^1 e^{-(c'/2)x} = 15.0877  closed form max(1,(k/(b e))^k e^b)=15.0877
c'=0.10 sup_x (1+x)^1 e^{-(c'/2)x} = 7.7348  closed form max(1,(k/(b e))^k e^b)=7.7348
c'=0.50 sup_x (1+x)^1 e^{-(c'/2)x} = 1.8895  closed form max(1,(k/(b e))^k e^b)=1.8895
min over grid of |1-t mu|^2/kappa^4 (want >=1): 1.0
```
Command 3: `python3 pf3.py` — the ticket instance, all `a ∈ Z_5³`:
```
e=0.1000 gamma=0.0900 eps=1.1111 (regime eps>=1) ell_t=1.5811 L^-2=0.040
mu=PropSpin m true * PropSpin m false = (1+0j)
lg_convA first part at instance: 1/e=10.000 <= C_A/(g^2+e)=48.571
a=0: n=0  Theta_{t mu}(0,0)=1.857526  Re Theta_t(0,0)=1.857526  B=2.937143  ratio=0.6324
a=0: |Theta0(0,0)|=1.777526  (g^2+e)^-1 (n+1)^-(d-2)=2.857143 ratio=0.6221
all a (L=5): max P5 ratio (c=0.3) 0.6324 ; max P8 ratio 0.6221 ; max n=6 (<= dL/2=7.5)
row sum Theta_t = 10.000000 vs 1/e = 10.000000 ; sum Theta0 = 2.22e-15
```
Not covered by the compiled instance (the ticket's instance has `μ=1`): the branch `σ₁=σ₂` of P8 (needs `μ=m²`); the scan above covers it numerically.

### Verdicts
- `prop5Decay_holds` (`Prop5Decay d Λ`): PASS. Hypotheses satisfiable at the instance; exponents close in all regimes R1–R4 and `t=0`, constants depend on `(d,Λ)` only; no unproved input.
- `prop8ZeroMode_holds` (`Prop8ZeroMode d Λ κ`): PASS. Both sign branches close; the `σ₁≠σ₂` branch needs the `e^{-ετ}`-kept `L^{-d}` piece (row above) and a separate `t=0` case; the `σ₁=σ₂` branch needs `prop5Short_holds` and `|1-tμ| ≥ κ²`.
- Notes for 1b (no pin change): `t=0` is outside `Theta_eq_laplace_prod`'s usable range for `τ=γs` (`γ=0`); `κ ≤ Im m` forces `κ ≤ 1` in the `σ₁=σ₂` branch.

## (b) Script output — Sat Oct  3 04:54:30 UTC 2026
Each block shows the command as run (output redirected to a log and filtered with `grep` where the command line says so) in `/Users/junyin/Lean_proof/RBM3D-wt/T2023`; times are `date -u` of the same session.

### b1–b2. Commit, scope, build, merge-time audit
```
$ date -u; git rev-parse --short HEAD; git status --short; git diff --stat main...t/T2023; wc -l RBM3D/Propagator/Prop5Hold.lean
Sat Oct  3 04:54:21 UTC 2026
3a5a579
 RBM3D/Propagator/Prop5Hold.lean | 1399 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 1399 insertions(+)
    1399 RBM3D/Propagator/Prop5Hold.lean

$ lake build RBM3D.Propagator.Prop5Hold > log 2>&1; echo exit=$? >> log; grep -E "Prop5Hold|Build completed|exit=" log
# run Sat Oct  3 04:48:27 UTC 2026, HEAD 3a5a579, clean tree, the module's .trace removed first so that it is recompiled; no line mentions a warning in the new file
✔ [3408/3408] Built RBM3D.Propagator.Prop5Hold (10s)
Build completed successfully (3408 jobs).
lake build RBM3D.Propagator.Prop5Hold  28.99s user 5.79s system 228% cpu 15.246 total
exit=0

$ lake build > log 2>&1; echo exit=$? >> log; grep -E "premises found|Prop5Decay:|Prop8ZeroMode:|Build completed|exit=" log
# full library, Sat Oct  3 04:46:14 UTC 2026; root RBM3D.lean does not import the new module yet
  RBM.Prop5Decay: 0 [no certificate]
  RBM.Prop8ZeroMode: 0 [no certificate]
premises found by scanning: 12 (borrowed 5, owed 1, structural 6).
Build completed successfully (3715 jobs).
exit=0

$ lake env lean audit_scratch.lean > out 2>&1; echo exit=$? >> out; grep -E "axiom audit|premises found|Prop5Decay|Prop8ZeroMode|exit=" out
# audit_scratch.lean = import RBM3D; import RBM3D.Propagator.Prop5Hold; #assert_rbm_axioms   (simulates the hub's merge-time check), Sat Oct  3 04:46:25 UTC 2026
axiom audit: 987 theorems, 378 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Prop5Decay: 1 [no certificate]
  RBM.Prop8ZeroMode: 1 [no certificate]
premises found by scanning: 10 (borrowed 3, owed 1, structural 6).
 RBM.Prop5Decay,
 RBM.Prop8ZeroMode,
exit=0
```

### b3–b4. Axioms, types, public declarations, pins untouched
```
$ lake env lean axchk.lean   # import RBM3D.Propagator.Prop5Hold; #print axioms and #check of the targets; Sat Oct  3 04:47:05 UTC 2026
'RBM.prop5Decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.prop8ZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.prop5Decay_holds : ∀ (d : ℕ) (Λ : ℝ), RBM.Prop5Decay d Λ
RBM.prop8ZeroMode_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.Prop8ZeroMode d Λ κ
RBM.Prop5Decay : ℕ → ℝ → Prop
RBM.Prop8ZeroMode : ℕ → ℝ → ℝ → Prop

$ grep -n "^theorem\|^lemma\|^def\|^noncomputable def\|^abbrev\|^structure\|^instance" RBM3D/Propagator/Prop5Hold.lean   # public declarations
784:theorem prop5Decay_holds (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := by
1266:theorem prop8ZeroMode_holds (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ := by
$ git diff --stat main...t/T2023 -- RBM3D/Propagator/Pins.lean RBM3D/Test/Axioms.lean RBM3D.lean   # prints nothing
$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Propagator/Prop5Hold.lean; echo exit=$?
exit=1
```

### b5–b6. Instances, name clashes, ports
```
$ sed -n 1317,1325p RBM3D/Propagator/Prop5Hold.lean   # prop5Decay_holds 3 1 at L=5, g=1/2, t=9/10, m=I, σ₁=true, σ₂=false, a=0
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
        0 0‖
      ≤ C * Bparam 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (0 : Zd 3 5))
        * Real.exp (-c * (zdistD 3 5 (0 : Zd 3 5) : ℝ) / ellT 5 (1 / 2) (9 / 10)) := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Decay_holds 3 1 (by norm_num) (by norm_num)
  exact ⟨C, hC, c, hc, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10)
    (by norm_num) (by norm_num) Complex.I Complex.norm_I true false 0⟩

$ sed -n 1337,1345p RBM3D/Propagator/Prop5Hold.lean   # prop8ZeroMode_holds 3 1 (1/2), same data
example : ∃ C : ℝ, 0 < C ∧
    ‖Theta0 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (PropSpin Complex.I true * PropSpin Complex.I false))
        0 0‖
      ≤ C * ((1 / 2 : ℝ) ^ 2 + |1 - (9 / 10 : ℝ)|)⁻¹
        * (((zdistD 3 5 (0 : Zd 3 5) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds 3 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
    (by norm_num) Complex.I Complex.norm_I (by norm_num) true false 0⟩

$ grep -n "^example" RBM3D/Propagator/Prop5Hold.lean | cut -c1-96   # all compiled instances (the build above compiled them)
1304:example (d : ℕ) (Λ : ℝ) : Prop5Decay d Λ := prop5Decay_holds d Λ
1306:example (d : ℕ) (Λ κ : ℝ) : Prop8ZeroMode d Λ κ := prop8ZeroMode_holds d Λ κ
1317:example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
1326:example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 5) ≠ 0 ∧
1337:example : ∃ C : ℝ, 0 < C ∧
1346:example : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 5) ≠ 0 ∧
1357:example : ∃ C : ℝ, 0 < C ∧
1368:example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ zdistD 3 5 (![2, 1, 0] : Zd 3 5) = 3 ∧
1377:example : ∃ C : ℝ, 0 < C ∧
1388:example (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2)) (h7 : Prop7Diff2 3 1 (1 / 2) (1 / 2)) :
1393:example : ThetaDecay 3 (1 / 2) Complex.I := (prop5Decay_holds 3 (1 / 2)).thetaDecay Complex
1395:example : ThetaZeroMode 3 (1 / 2) (PropSpin Complex.I true * PropSpin Complex.I false) :=
```
```
$ grep -rn "prop5Decay_holds\|prop8ZeroMode_holds" RBM3D RBM3D.lean --include='*.lean' | grep -v Prop5Hold.lean; echo exit=$?
exit=1
$ grep -rln "p5h_\|p5hCh" RBM3D RBM3D.lean --include='*.lean'   # private helper prefix
RBM3D/Propagator/Prop5Hold.lean
$ grep -n "RBM1D\|RBM2D" RBM3D/Propagator/Prop5Hold.lean; echo exit=$?   # no port from the sister projects
exit=1
```
```
$ grep -rln "prop5Decay_holds\|prop8ZeroMode_holds" RBM3D/RBM3D RBM3D/RBM3D.lean RBM3D-wt/*/RBM3D | sort -u   # main tree (HEAD 9187a77) and all worktrees
RBM3D-wt/T2023/RBM3D/Propagator/Prop5Hold.lean
```

### b7. The constants (extracted by script)
```
$ sed -n 553,557p RBM3D/Propagator/Prop5Hold.lean; sed -n 802,803p RBM3D/Propagator/Prop5Hold.lean; sed -n 1281,1287p RBM3D/Propagator/Prop5Hold.lean   # the constants
private noncomputable def p5hCh (d : ℕ) (CK CA CB c' : ℝ) : ℝ :=
  CK * (CA * ((1 + 2 / ((d : ℝ) - 2)) + 1
    + 2 * (((d - 2).factorial : ℝ) * (1 / (c' / 2)) ^ (d - 2) * Real.exp (c' / 2))
    + CB * 2 ^ (d - 2) * Real.exp (c' * d / 2)))

  refine ⟨p5hCh d CK CA CB c' + (1 + CG) * Real.exp (c * d / 2) + (Λ ^ 2 + 1), by positivity, c,
    hc0, ?_⟩
  refine ⟨(p5hCh d CK CA CB c' + CA * ((d : ℝ) / 2 + 1) ^ (d - 2)
      + CG * (CA * (1 + 1 / cG)) * ((d : ℝ) / 2 + 1) ^ (d - 2))
    + (Λ ^ 2 + 1) * (1 + ((d : ℝ) / 2 + 1) ^ (d - 2))
    + (Cs * (Λ ^ 2 + 1)
      + Cs * (Λ ^ 2 * (Λ ^ 2 + 1)) * (((d - 2).factorial : ℝ) * (1 / cs) ^ (d - 2) * Real.exp cs)
      + (κ ^ 2)⁻¹ * ((d : ℝ) / 2 + 1) ^ (d - 2) * (Λ ^ 2 + 1)), by linarith, ?_⟩
  intro L hL g hg hgΛ t ht0 ht1 m hm hκm σ₁ σ₂ a
```

### Narrative (b8)
1. Both targets are proved in the new file `RBM3D/Propagator/Prop5Hold.lean` (1399 lines, commit `3a5a579` on `t/T2023`). Their types are the merged pins
   (b3; the file also elaborates `example (d Λ) : Prop5Decay d Λ := prop5Decay_holds d Λ` and the P8 analogue, lines 1304, 1306 in b5). No hypothesis was
   added; `Pins.lean`, `Axioms.lean`, `RBM3D.lean` are untouched (b3). The two theorems are the only public declarations; every helper is `private` with prefix
   `p5h_`/`p5hCh` (CLAUDE.md §3 (E)). No unproved `Prop` is a hypothesis of either theorem.
2. P5. Reduction by `norm_Theta_apply_le` (property 4; `μ = PropSpin m σ₁ · PropSpin m σ₂`, `‖μ‖ = 1`) to real `t`. `t = 0` is `p5h_zero5` (`Θ = 1`,
   `B_{0,0} ≥ (Λ²+1)⁻¹`). For `0 < t < 1`, `p5h_theta_eq`: `Theta_eq_laplace_prod` and `integral_comp_mul_left_Ioi` (`τ = γ s`) give
   `Θ_t(0,a) = γ⁻¹ ∫_{(0,∞)} e^{-ετ} K_τ(a) dτ`; integrability from `0 ≤ K ≤ 1` (`hkT_mass`) and continuity of `τ ↦ K_τ`; the integral is split at `τ = L²`.
3. Head `(0, L²]`: `kProd_le` gives `e^{-ετ} K_τ ≤ C_K · lgIntegrand d c_K n ε τ`; `lg_bulk` (`n ≥ 1`) and `lg_zero` (`n = 0`) bound the integral;
   `p5h_shape_zero/big/small` (regimes `n = 0`, `ε ≥ 1`, `ε < 1`, by `ε = e/γ`) are merged in `p5h_head_shape`/`p5h_head5` with `lg_convA` (first part for
   `ε ≥ 1`, second for `ε < 1`; this is where `Λ` enters), `lg_convB` (`ℓ⁻¹ ≤ √ε` or `ℓ = L`, in `p5h_exp_bulk`), `n^{-(d-2)} ≤ 2^{d-2}(n+1)^{-(d-2)}` and
   `(n+1)^k e^{-bn} ≤ k! b^{-k} e^b` (`p5h_poly_exp_le`).
4. Tail `(L², ∞)`: `kProd_gap` gives `K_τ ≤ (1+C_G) L^{-d}`; `∫_{(L²,∞)} e^{-ετ} = e^{-εL²}/ε`; `γε = e` gives `(1+C_G) e^{-εL²} (L^d e)⁻¹`; the zero-mode
   factor `e^{-εL²} ≤ e^{cd/2} e^{-cn/ℓ}` (for `cd ≤ 2`) is `p5h_exp_zero` (`lg_convC` if `ε ≥ L⁻²`, `ℓ = L` otherwise).
5. P5 constants: `c = min (c'/2) (2/d)` (`c'` the exponent of `lg_bulk d hd c_K`); `C = p5hCh d C_K C_A C_B c' + (1+C_G) e^{cd/2} + (Λ²+1)` (b7). Both depend on
   `(d, Λ)` only and are fixed before `L, g, t, m, σ₁, σ₂, a`, as the pin quantifies.
6. P8, `σ₁ ≠ σ₂` (`μ = 1`, `p5h_mu_one`): `t = 0` is `p5h_zero8`. For `0 < t < 1`, `p5h_theta0_eq` (`Theta0_apply_eq`, `∫ e^{-ετ} = 1/ε`) gives
   `Θ̊ = γ⁻¹ ∫ e^{-ετ}(K_τ − L^{-d}) dτ`; head `|·| ≤ ∫ e^{-ετ}K + L^{-d} ∫_{(0,L²]} e^{-ετ}` (`p5h_head0_le`; the `K` part is the P5 head at `c = 0`);
   tail `|K − L^{-d}| ≤ C_G L^{-d} e^{-c_Gτ/L²}` with `lg_tail` (`p5h_tail0_le`); `e^{-ετ}` is kept on both `L^{-d}` pieces (`p5h_Ld_piece`, `lg_convA`,
   `L^{-(d-2)} ≤ (d/2+1)^{d-2}(n+1)^{-(d-2)}`). The bulk condition `κ ≤ Im m` is not used in this branch.
7. P8, `σ₁ = σ₂`: `p5h_sigma_eq` from `prop5Short_holds` (`C_s, c_s` of `(d,Λ,κ)`), `Θ̊ = Θ − L^{-d}(1−tμ)⁻¹`, `‖1−tμ‖ ≥ κ²` (`p5h_gap_lower`:
   `‖1−tμ‖² = (1−t)² + 4t (Im m)²`, `κ ≤ Im m ≤ ‖m‖ = 1`), `1 ≤ (Λ²+1)(g²+e)⁻¹`, `g² ≤ Λ²(Λ²+1)(g²+e)⁻¹`. The P8 constant is a sum of three explicit constants (b7).
8. `d ≥ 3` enters through `lg_bulk d`/`lg_zero d` (`m = d ≥ 3`), `Fin d` nonempty (first conjunct of `kProd_gap`) and `2 ≤ d` for the ℕ-subtraction `d - 2` (`p5h_rpow_eq`).
9. Differences from (a)'s table (constants only; no verdict changes): R2 and R3 share `p5h_exp_bulk`, so the head factor is `e^{c'd/2}` (table: `e^{cd/2}`);
   `C` is a sum, not a max; the P8 `t = 0` constant is `(Λ²+1)(1+P_d)` (table: `(Λ²+1)P_d`), `P_d = (d/2+1)^{d-2}`.
10. No port from RBM1D/RBM2D (b6). Private lemmas copied or adapted from merged RBM3D files (file:line; last commit of the file): `p5h_norm_spin`, `p5h_gap_sq` ←
   `Prop5Short.lean:325,329` (`b20c658`); `p5h_kProd_nonneg_le_one` ← `HeatProduct.lean:946` (`cf8e79e`; `kProd_continuous` `:943` is re-proved with `fun_prop` and
   `continuous_finsetProd`); `p5h_lg_nonneg` ← `LaplaceGauss.lean:496`, `p5h_integral_exp` ← `:280`, `p5h_poly_exp_le` adapts `:574` (`315e65e`); `p5h_Theta_zero` ← `Pins.lean:119` (`b20c658`).
11. Audit scan (b2): with the module imported `#assert_rbm_axioms` exits 0; scanned premises drop from 12 to 10 (`Prop5Decay`, `Prop8ZeroMode` are proved; the two bare lines
   ` RBM.Prop5Decay,` ` RBM.Prop8ZeroMode,` are entries of the registry's "carry nothing yet" list); "theorems resting on each premise" counts 1 for each (`usageOf` in
   `Axioms.lean` counts any theorem whose type mentions the pin, so it counts the new theorems; informational).

## (c) Verified Mathlib names used (resolved in the build above; module from `env.getModuleIdxFor?`, `lake env lean names.lean`, Sat Oct  3 04:47:05 UTC 2026)
- `MeasureTheory.integral_comp_mul_left_Ioi` — MeasureTheory.Integral.IntegralEqImproper
- `integrableOn_exp_mul_Ioi` — Analysis.SpecialFunctions.ImproperIntegrals
- `integral_exp_mul_Ioi` — Analysis.SpecialFunctions.ImproperIntegrals
- `MeasureTheory.setIntegral_union` — MeasureTheory.Integral.Bochner.Set
- `MeasureTheory.setIntegral_mono_set` — MeasureTheory.Integral.Bochner.Set
- `MeasureTheory.setIntegral_mono_on` — MeasureTheory.Integral.Bochner.Set
- `MeasureTheory.setIntegral_nonneg` — MeasureTheory.Integral.Bochner.Set
- `MeasureTheory.integral_sub` — MeasureTheory.Integral.Bochner.Basic
- `MeasureTheory.integral_const_mul` — MeasureTheory.Integral.Bochner.Basic
- `MeasureTheory.integral_congr_ae` — MeasureTheory.Integral.Bochner.Basic
- `MeasureTheory.norm_integral_le_of_norm_le` — MeasureTheory.Integral.Bochner.Basic
- `MeasureTheory.Integrable.mono'` — MeasureTheory.Function.L1Space.Integrable
- `MeasureTheory.IntegrableOn.mono_set` — MeasureTheory.Integral.IntegrableOn
- `MeasureTheory.IntegrableOn.congr_fun` — MeasureTheory.Integral.IntegrableOn
- `MeasureTheory.Integrable.sub` — MeasureTheory.Function.L1Space.Integrable
- `MeasureTheory.Integrable.const_mul` — MeasureTheory.Function.L1Space.Integrable
- `Continuous.integrableOn_Ioc` — MeasureTheory.Function.LocallyIntegrable
- `Set.Ioc_union_Ioi_eq_Ioi` — Order.Interval.Set.LinearOrder
- `Set.Ioc_disjoint_Ioi_same` — Order.Interval.Set.Disjoint
- `Set.Ioc_subset_Ioi_self` — Order.Interval.Set.Basic
- `Set.Ioi_subset_Ioi` — Order.Interval.Set.Basic
- `continuous_finsetProd` — Topology.Algebra.Monoid
- `Real.pow_div_factorial_le_exp` — Analysis.Complex.Exponential
- `Real.rpow_neg` — Analysis.SpecialFunctions.Pow.Real
- `Real.rpow_natCast` — Analysis.SpecialFunctions.Pow.Real
- `Complex.mul_conj` — Basic.Complex.Basic
- `Complex.normSq_eq_norm_sq` — Analysis.Complex.Norm
- `Complex.im_le_norm` — Analysis.Complex.Norm
- `Complex.norm_real` — Analysis.Complex.Norm
- `Complex.norm_natCast` — Analysis.Complex.Norm
- `Complex.sq_norm` — Analysis.Complex.Norm
- `Complex.normSq_apply` — Basic.Complex.Basic
- `Real.one_le_exp` — Analysis.Complex.Exponential
- `Real.exp_le_one_iff` — Analysis.Complex.Exponential
- `pow_le_pow_left₀` — Algebra.Order.GroupWithZero.Basic
- `pow_le_one₀` — Algebra.Order.GroupWithZero.Basic
- `pow_le_pow_right₀` — Algebra.Order.GroupWithZero.Basic
- `inv_anti₀` — Algebra.Order.GroupWithZero.Basic
- `inv_mul_le_iff₀` — Algebra.Order.GroupWithZero.Basic
- `le_div_iff₀` — Algebra.Order.GroupWithZero.Basic
- `div_le_iff₀` — Algebra.Order.GroupWithZero.Basic
- `div_le_div_of_nonneg_right` — Algebra.Order.GroupWithZero.Basic
- `Finset.prod_le_one₀` — Algebra.Order.BigOperators.GroupWithZero.Finset
- `Finset.single_le_sum` — Algebra.Order.BigOperators.Group.Finset
- `abs_add_le` — Algebra.Order.Group.Unbundled.Abs
- `norm_sub_le` — Analysis.Normed.Group.Basic
- `Nat.cast_sub` — Data.Int.Cast.Basic
- `Matrix.one_apply_ne` — Data.Matrix.Diagonal
- `Real.sqrt_nonneg` — Analysis.Real.Sqrt
- Verified absent / renamed (tool log of this session): `Complex.le_abs_self` (Unknown constant, `Prop5Hold.lean:1169` while writing); `continuous_finset_prod` is deprecated, use `continuous_finsetProd` (linter message while writing).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new. The Lean statements are the merged pins (b3), so the Lean/paper differences they carry are those of T2003 (T2003a, the `Λ`-dependence, signed in DECISIONS §13; used here through `lg_convA`).
- Observation (no statement difference): the branch `σ₁ ≠ σ₂` of P8 holds without the bulk condition and with `κ`-free constants (`p5h_core8`, `p5h_zero8` take no `κ`); the pin keeps `κ` and `κ ≤ Im m`, as the paper does.
- For PT-G (not this ticket): `Axioms.lean` still lists `RBM.Prop5Decay`, `RBM.Prop8ZeroMode` in `borrowedProps` (the registry then reports them under "carry nothing yet", b2); `Prop5to8` still needs `Prop6Diff1`, `Prop7Diff2` (T2024): the instance at line 1388 builds `Prop5to8 3 1 (1/2) (1/2)` from three proved fields and those two hypotheses.
- No obstruction met; no pin, frozen or pinned signature changed; no `(a′)` section: section (a) has no mistake (its constants differ from the proof's only as in item 9).
