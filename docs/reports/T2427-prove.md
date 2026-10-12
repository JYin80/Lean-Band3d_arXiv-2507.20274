Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 22:28:09 UTC 2026 (`date -u`)

Scripts (python/numpy, no Lean) are in the scratchpad `T2427/`: `inst.py`, `mc2.py`, `mir.py`, `mc_det.py`; each command is run there.
Conventions: `E_a = W^{-d}1_{[a]}` (`Loop/GLoop.lean:55`), `Bctl n t = W^{-d} B_{t,0}` (`Defs/Sizes.lean:214`), `PrecL` = `StochDomAt`; `p ∈ ℕ`, `p ≥ 1` (`Φ = T̃^{p-1} conj(T̃)^p` needs it).
Index convention: Lean `twTr c₁ c₂ = W^{-d}Σ_o Ǧ_{(c₁,o),(c₂,o)} = Tr(Ǧ P_{c₂c₁}) = T̃_{(c₂,c₁)}` (`TwistPins.lean:57-60`; script line `twTr c1 c2 = ... max err 0.00e+00` below). The pin's right side contains only `X_{c₁c₂}` and the global `X = max`, so the relabeling `(c₁,c₂) ↔ (c₂,c₁)` of TP:86-89 is harmless.

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | (I2): `‖L^{(1)}_c − m‖ ≺ Bctl^1` (`LWAvgLawgL`, `Chain/LWGen.lean:48`); `Tr(Ǧ E_c) = L^{(1)}_c − m` since `M^{(B)}_{cc} = m` (`BAMB_diag_eq`, `BA/Ward.lean:89`) | exponent 1 | first display needs `B^1` | 0 (sharp) |
| 2 | (I3): `STLmaxgL`, `k = 4`: `Bctl^3`; `k = 2`: `Bctl^1` (`Chain/Carrier.lean:87-91`) | 3, 1 | Step 4 needs `(L⁽⁴⁾L⁽²⁾)^{1/2} ≺ Bctl^{(3+1)/2}` | — |
| 3 | `‖𝒮₁‖+‖𝒮₂‖ ≺ C_M Bctl^{3/2+1/2}` | exponent 2 | the term `2p W^{ε'} B² X^{2p−2}` needs 2 | **0** (equality `3/2+1/2 = 2`; no loss in CS: the square root halves `3` and `1` exactly) |
| 4 | coefficient of the `B²` term: `(p−1)+p = 2p−1` (from `u(p−1)𝒮₁`, `u p 𝒮₂`) | `2p−1` | pinned `2p` | 1 |
| 5 | flow time `u = t n ∈ [0, BAflowT0)` multiplies every term | `u ≤ 1` | pin has no `u` | `1−u` (`= 1/2` at `t ≡ 1/2`) |
| 6 | `‖M‖`-facts: `|M^{(B)}_{c₂c}| ≤ 1` (from `Σ_b|M_{ab}|² = 1`), `Σ_c|M_{cc₁}| ≤ C_M` (`BAMB_row_l1`, `BA/GreenSchur.lean:139`) | instance `max|M_{ab}| = 0.9995`, `C_M = 1.083` | `≤ 1`, finite | 5e-4 for the first |
| 7 | `C_M` numerics (d=3, L=8, E=0; g = 1/64, 1, 10) | 1.101, 15.625, 13.378 (T2413 values 1.10, 15.6, 13.4 reproduced) | depends on `(d,κ,𝔡)` only | no smallness of `g` |
| 8 | `C_M` of `BAMB_row_l1` at `d=3, Λ=𝔡⁻¹=10, κ=1/2`: `c⁻¹ expC(1,c)`, `c = min(log(1+κ/(4dΛ)), κ/2)` (`BA/CombesThomas.lean:45`, `Defs/RadialSum.lean:271`) | `c = 0.004158`, `C_M = 4.943e15` | a constant in `(d,κ,𝔡)` | proved constant ≫ numerics (constants only) |
| 9 | `≺ → W^{ε'}`: `N^{ε_≺} ≤ W^{ε'/2}` using `W ≥ N^𝔠` | `ε_≺ = 𝔠ε'/2` (`= 0.00417` at `𝔠=1/6, ε'=0.05`) | `ε_≺ ≤ 𝔠ε'/2` | 0 |
| 10 | T.6 floor `Y' = Bctl > N^{-C₁}`: `Bctl ≥ N^{-1}/|1−t|` | `C₁ = 1` (instance: `Bctl ≥ N^{-1}` all `n ≤ 3`) | `Bctl > N^{-C₁}` | factor `≥ 100` at `n=0` (6.2e-5 vs 4.8e-7) |
| 11 | T.6 deterministic envelope `|T̃|, |𝒮ᵢ| ≤ N^{C₀}`: `‖G‖+‖M‖ ≤ 1/η_t + 1/Im m₀` | `C₀ = 1` (instance `4.27 ≤ N`) | `≤ N^{C₀}` | huge |
| 12 | `N^{-D}` term: `Σ_c (EY²)^{1/2} N^{-D'} ≤ L^d N^{C₀(2p)}N^{-D'}`, `D'` free | `D' = D + 2pC₀ + 1` | `D'` arbitrary | none needed |

**Decision on `C_M` (target 1).** Keep it as `∃ C > 0` fixed before `𝔠, sz, z`, `C = C(d,κ,𝔡)` (the form of `twK_bound`, `TwistPins.lean`, O2). The absorbed form (`C_M ≤ W^{ε'/2}`) needs `W^{ε'} ≥ C_M` (script: `log10 W ≥ 314` at `ε'=0.05`, with row 8): still true eventually but a threshold of astronomical size, and it costs a `W → ∞` step. The kept form is what TL1b's absorption `C W^{ε'}B ≤ 1/2` uses (script: holds from `n = 6` along `sz0` at `ε'=0.05` with `C = 4.943e15`). Pin:
`X_{c₁c₂}^{2p} ≤ C W^{ε'}B(X_{c₁c₂}^{2p−1} + X·X_{c₁c₂}^{2p−1}) + 2p C W^{ε'}B² X_{c₁c₂}^{2p−2} + N^{−D}`.

**Form of (C.3)–(C.5) (both routes; exponent count identical).** Orientation TP (`Ǧ = −G(V+um)M`): `E[T̃Φ] = uE[Tr(G S[Ǧ] M P)Φ] + u(p−1)E[𝒮₁T̃^{p−2}T̄^p] + upE[𝒮₂|T̃|^{2p−2}]`, with `Tr(G S[Ǧ] M P) = Σ_c Tr(ǦE_c)M_{cc₁}(M_{c₂c}+T̃_{(c,c₂)})`, `𝒮₁ = Σ S_{xw}(MPG)_{wx}(GPG)_{xw}`, `𝒮₂ = Σ S_{xw}(MPG)_{wx}conj((GPG)_{wx})`, `|𝒮₂| ≤ Σ_c|M_{cc₁}|(L⁽⁴⁾_{(+−+−),(c,c₂,c,c₂)}L⁽²⁾_{(+−),(c₁,c)})^{1/2}`, `|𝒮₁| ≤ Σ_c|M_{cc₁}|(L⁽⁴⁾_{(++−−),(c,c₁,c,c₂)}L⁽²⁾_{(+−),(c,c₂)})^{1/2}`.
Mirror orientation (`Ǧ = −M(V+um)G`, the form `lanlw` has per the ticket): same with `Tr(S[Ǧ] G P M) = Σ_c Tr(ǦE_c)M_{c₂c}(M_{cc₁}+T̃_{(c₁,c)})` and `𝒮'₁ = ΣS_{xw}(GPM)_{wx}(GPG)_{xw}`, `𝒮'₂ = ΣS_{xw}(GPM)_{wx}conj((GPG)_{wx})`; hand-derived CS: `|𝒮'₂| ≤ Σ_c|M_{c₂c}|(Tr(G*E_cGE_{c₁}G*E_cGE_{c₁})·Tr(GE_cG*E_{c₂}))^{1/2}`, `|𝒮'₁| ≤ Σ_c|M_{c₂c}|(L⁽⁴⁾_{(++−−),(c,c₁,c,c₂)}L⁽²⁾_{(+−),(c₁,c)})^{1/2}` (row sums of `M^{(B)}` symmetric, `BAMB_transpose`): exponent `3/2+1/2 = 2` again, so the route choice does not affect any row above. All four displays are checked numerically below.

### (ii) One concrete nondegenerate instance (Lean datum of the ticket)

`d=3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`, `Defs/Sizes.lean:260`), `(κ,ε,𝔡,𝔠) = (1/2, 1/10, 1/10, 1/6)`, `t ≡ 1/2`; `z_n = w − m_S` with `w = 6i/5`, `m_S = L^{-d}Σ_k(λΛ_k − w)^{-1}` (`FlowPins.lean:1181-1189`, `MFixedPoint.lean:849-868`); `g₀ = √t₀ λ`, `E = 0`.
Hypotheses checked at `n = 0..3`: `BAdom` (`κ ≤ Im m`, `N^{-1+ε} ≤ Im z ≤ 1`), `t ≤ t₀`, `(eq:WO)` and `W ≥ N^𝔠` (`Admissible`), `(self_m)` at `(E,g₀)` with `m₀ = m_S/√t₀`, plus the rows 6, 10, 11, 7, 8, 9, 3.
Command: `cd scratchpad/T2427; python3 inst.py`. Output (verbatim):
```
n  L  W  lam  N  | Im m_S  Im z  t0  | kappa<=Im m  N^(-1+eps)<=Im z<=1  t<=t0 | WO: W^(-d/2+dd)<=lam<=1/dd  W>=N^cc | Bctl  N^-1 | eta_t=(1-t)Im m0
0 4 32 1.562e-02 2.097e+06 | 0.8325 0.3675 0.6937 E=+3.1e-18 | (np.True_, np.True_, np.True_) | (True, True) | 6.196e-05 4.768e-07 | 0.4997  [selfm res 1.1e-16]
1 8 1024 2.441e-04 5.498e+11 | 0.8333 0.3667 0.6944 E=+2.4e-20 | (np.True_, np.True_, np.True_) | (True, True) | 1.866e-09 1.819e-12 | 0.5000  [selfm res 1.1e-16]
3 16 32768 3.815e-06 1.441e+17 | 0.8333 0.3667 0.6944 E=+1.5e-21 | (np.True_, np.True_, np.True_) | (True, True) | 5.686e-14 6.939e-18 | 0.5000  [selfm res 1.1e-16]
n=0: m_S=-0.000000+0.832488j, z_0=0.000000+0.367512j, t0=0.693740 (>=2/3), Im z in [11/30,7/10]=0.3667,0.7: True, N=(W L)^3=2097152, N^(-0.9)=2.04e-06
n=0 M^(B)(E=0,g0=0.01301): max_a sum_b|M_ab| = 1.0828, max_a sum_b|M_ab|^2 = 1.000000, max|M_ab| = 0.9995, Im m0 = 0.9995 >= kappa
BAct_rate(3,10,1/2) = 0.004158; C_M^Lean = c^-1 expC(1,c) = 4.943e+15
```
Rows 7-12 of the same output (verbatim):
```
g=0.01562: Im m=0.9993  C_M=sum_b|M_ab|=1.101  sum|M|^2=1.000000 max|M_ab|=0.999
g=1.00000: Im m=0.4665  C_M=sum_b|M_ab|=15.625  sum|M|^2=1.000000 max|M_ab|=0.466
g=10.00000: Im m=0.3654  C_M=sum_b|M_ab|=13.378  sum|M|^2=1.000000 max|M_ab|=0.365
eps'=0.05: first n (<400) with C_M^Lean W_n^eps' Bctl_n <= 1/2: n=6; absorbed form needs W^eps' >= C_M^Lean, i.e. log10 W >= 314 (astronomical); kept form `exists C` needs none
eps'=0.05: eps_prec = cc eps'/2 = 0.00417;  N^eps_prec <= W^(eps_prec/cc) = W^0.0250 = W^(eps'/2)
STLmaxgL k=4: Bctl^(k-1) = Bctl^3
STLmaxgL k=2: Bctl^(k-1) = Bctl^1
Step 4: (L4 * L2)^(1/2) = Bctl^((3+1)/2) = Bctl^2; needed: Bctl^2 (the term 2p W^eps' B^2 X^(2p-2)) slack 0
coefficients: (p-1) + p = 2p-1 <= 2p (pin) : slack 1; factor t <= 1 : slack 1-t = 1/2 at t=1/2
n=0: eta_(t0)=0.3061; 1/eta+1/Im m0 = 4.267 <= N=2.10e+06 (C0=1); Bctl(t=1/2) 6.196e-05 >= N^-1 4.768e-07: True; Bctl(t0) 1.011e-04 >= N^-1: True
n=3: eta_(t0)=0.3056; 1/eta+1/Im m0 = 4.273 <= N=1.44e+17 (C0=1); Bctl(t=1/2) 5.686e-14 >= N^-1 6.939e-18: True; Bctl(t0) 9.304e-14 >= N^-1: True
```
(rows `n=2` of the first table and `n=1,2` of the last block omitted here for length; all `True` in `inst.out`.)

**External hypotheses (`LWAvgLawgL`, `STLmaxgL`, other gates' pins) — limit computation along `sz0`.** They are asymptotic in `n`; nothing in the instance contradicts them: `Bctl_n → 0` (`6.2e-5, 1.9e-9, 4.3e-12, 5.7e-14` at `n = 0..3`, `~ 2W^{-3}`), the floor `Bctl_n ≥ N_n^{-1}` holds (row 10), and the consumer need `C W^{ε'} Bctl_n ≤ 1/2` is met from `n = 6` (`C = 4.943e15`, `ε' = 0.05`) and tends to 0 (`W^{ε'}Bctl_n ~ W^{ε'-3}`, `ε' < 3`).

**Monte Carlo of the moment identity (TP:86-87), `d=3`, `L=3`, `W=2` (`N=216`; the Lean datum `n=0` has `N=2.1e6`, not simulable), `g₀ = 1/2`, `E = 0.2`, `u = 0.6`, `Im m = 0.7332`, `c₁ = (0,0,0)`, `c₂ = (1,0,0)`, complex Hermitian block-diagonal `V`, `E|V_{xy}|² = u W^{-d}1([x]=[y])`, 10⁵ samples.** `E|T̃|^{2p}` against the right side `u E[Tr(GS[Ǧ]MP)Φ] + u(p−1)E[𝒮₁…] + upE[𝒮₂…]`; the last column flips the signs of the `𝒮` terms (power check). Commands: `python3 mc2.py 100000 7` and `python3 mir.py 100000 8` (mirror form); output:
```
seed=7 samples=100000 time=354s  Im m=0.7332  rms|T|=0.0275  W^-d=0.125
p=1: LHS E|T|^2 = 7.564953e-04 +- 2.4e-06 | RHS = 7.564013e-04 +- 5.5e-07 (Im part mean 5.5e-07) | paired LHS-RHS = 9.40e-08 +- 2.8e-06 (z=0.03) | S-terms sign-flipped: z=616.9
p=2: LHS E|T|^4 = 1.140840e-06 +- 8.0e-09 | RHS = 1.150959e-06 +- 3.3e-09 (Im part mean 1.0e-09) | paired LHS-RHS = -1.01e-08 +- 5.7e-09 (z=-1.76) | S-terms sign-flipped: z=199.1
mirror p=1: samples=100000 LHS=7.549925e-04 RHS=7.553316e-04  paired diff = -3.39e-07 +- 2.8e-06 (z=-0.12)
mirror p=2: samples=100000 LHS=1.139810e-06 RHS=1.145422e-06  paired diff = -5.61e-09 +- 5.9e-09 (z=-0.95)
```
Both orientations agree within `2σ` (`|z| ≤ 1.76`), while the wrong signs are rejected at `z = 617, 199`. Deterministic per-sample checks (20 samples; `python3 mc_det.py 20 3` and `python3 mir.py 20 3 det`):
```
(C.4) max |Tr(G S[G°] M P) - sum_c ...| over 20 samples = 1.10e-17
T~ = Tr(GP) - M^B_(c2,c1): max err 2.78e-17
Step 4 loop forms: max|S2 - S2_loop| = 1.52e-18, max|S1 - S1_loop| = 6.55e-19
CS bounds |S2| <= sum_c|M_cc1|(L4 L2)^(1/2), |S1| <= ...: min slack = 1.11e-03, 1.59e-03 (>= 0 required); ratios |S|/bound: 0.587, 0.196
twTr c1 c2 (TwistPins.lean:57) = Tr(G° P_(c2,c1)): max err 0.00e+00
mirror (C.4'): max |Tr(S[G°] G P M) - sum_c Tr(G°E_c) M_(c2,c)(M_(c,c1)+T_(c1,c))| = 1.64e-17
mirror CS bounds |S2'| <= sum_c|M_(c2,c)|(L4 L2)^(1/2), same for S1': min slack 1.08e-03, 1.61e-03 (>= 0 required)
```

### Verdicts
- **Target 1** (`BATwistAvgRec`, `baTwistAvgRec_holds`): **PASS.** Hypotheses are satisfiable at the instance; exponent 2 closes with equality (row 3), every other row has slack. Form: `∃ C = C(d,κ,𝔡)` before `𝔠, sz, z`, `p : ℕ`, `p ≥ 1`; the constant `N^{-D}` (not `N^{-D}X^{2-2p}`: S1 stays in TL1b).
- **Target 2** (public lemmas (i)-(iv)): **PASS.** (i) moment identity and `𝒮₁, 𝒮₂` as in the display above (both orientations verified); (ii) rows 2-3; (iii) T.6 at `μ`: rows 9-12; (iv) envelope row 11. Needs `M^{(B)}_{cc} = m` (`BAMB_diag_eq`) and `E_a` normalized (`Loop/GLoop.lean:55`), both present.
- **Target 3** (instances): **PASS** at the data above; the identity at `n=0`, `p = 1, 2`, `c₂ ≠ c₁` is exact at every size (checked at `L=3, W=2`).
- Observation (no verdict impact): the proved `C_M = 4.94e15` (row 8) is 10¹⁴ above the numerics (row 7); a constant only.

## (a″) Probe compile — Sun Oct 11 22:59:47 UTC 2026 (`date -u`)   [condensed by the 1b stage to keep the report within the line cap; what was judged is in `docs/reports/T2427-1a-audit.md`]

Probe `RBM3D/Probe/T2427Pins.lean` (275 lines, never merged) at commit `d60d13d` on `t/T2427` (two commits on `0a8176c`, `6d1b327` then `d60d13d`; each touches only this file). Section (a) is unchanged (no (a′)); the probe follows its decisions: `∃ K` before `𝔠, sz, z`, `p ∈ ℕ, p ≥ 1`, the `twTr` index convention, the pin is TP:89 with `K`.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2427 && lake env lean RBM3D/Probe/T2427Pins.lean      # run at Sun Oct 11 22:59:28 UTC 2026 on `d60d13d`, working tree clean
exit=0   (output: the 15 `#check` lines of the probe names `twAvgGPM` ... `T2427_TL1b`, then `∀ d, BATwistAvgRec d`; no error, no warning)
```
Names (each pin `P` is proved as `P_holds : ∀ d, P d`, `twAvgT6_holds : twAvgT6`): target 1 `BATwistAvgRecAt`, `BATwistAvgRec`, `baTwistAvgRec_holds`; target 2 (i) `twAvgMomentAt`, `twAvgMoment` with the public `twAvgS1`, `twAvgS2` (factors `twAvgGPM`, `twAvgGPG`), (ii) `twAvgSCS` (pathwise CS), `twAvgSPrec` (`≺ B²`), (iii) `twAvgT6`, (iv) `twAvgReg`; interface `T2427_TL1b`. Files: `TwistAvgA` = Steps 1–3 + `BATwistAvgRec(At)` + defs + (i) + (iv); `TwistAvgA2` = (ii), (iii), Hölder, `baTwistAvgRec_holds`, instances.

**(ii) IBP route: (R-a)**, `baLanlw_holds` with `f = Φ_p = T^{p−1}T̄^p`, transported to `μ = seqP (sz.withLam 0)` as `BAExp14a_lanlw_diag`. Reasons: `lanlw` is proved for every resolvent polynomial and every `d` and contains the pathwise algebra and the Stein step; in the `twTr` convention the sum is `Σ_c|M_{c₁c}|`, the form of `BAMB_row_l1` (no transposition); R-b would re-derive that algebra (basis `Green/IBP.lean` 112–440 + 675–760 = 329 + 86 lines). Form obtained, `T = twTr c₁ c₂ = T̃_{(c₂,c₁)}`, `P = P_{c₂c₁}`, `S_{αβ} = t S°_{αβ}`, `S°_{αβ} = W^{-d}1([α]=[β])` (`twAvgS1/2` use `S°`; `t` stands outside), `Ǧ = −M(V+tm)G`:
```
(C.3') E[TΦ] = t E[AΦ] − E[W^-d Σ_{w∈[c₁]} Σ_{α,β} M_wα S_αβ G_{β,Π_c₂ w} ∂_{h_βα}Φ],  A = Σ_c M^B_{c₁c} X_c (M^B_{cc₂} + twTr c c₂),  X_c = 𝓛¹_c − m
(C.4') the lanlw first term is tA   (Σ_β S_αβ Ǧ_ββ = t X_[α]; M_wα = 1[offsets] M^B)
(C.5') ∂_{h_βα}T = −(GPG)_αβ, ∂_{h_βα}T̄ = −conj((GPG)_βα); W^-d Σ_w Σ_{α,β} M_wα S_αβ G_{β,Π_c₂ w} ∂_{h_βα}Φ = −t[(p−1)𝒮₁T^{p−2}T̄^p + p 𝒮₂|T|^{2p−2}],  𝒮₁ = ΣS°(GPM)_βα(GPG)_αβ, 𝒮₂ = ΣS°(GPM)_βα conj((GPG)_βα)
|𝒮₁| ≤ Σ_c|M_{c₁c}| (|𝓛⁴_{(++−−),(c,c₂,c,c₁)}| |𝓛²_{(+−),(c₂,c)}|)^(1/2),  |𝒮₂| ≤ Σ_c|M_{c₁c}| (|𝓛⁴_{(−+−+),(c,c₂,c,c₂)}| |𝓛²_{(+−),(c,c₁)}|)^(1/2)   (mirror of TP:83; (B³B)^(1/2) = B²)
```
So `𝒮₁`, `𝒮₂` fold into loop pairs of the mirror form (TP:83 has `(+−+−),(c,c₂,c,c₂)` with `(+−),(c₁,c)` and `(++−−),(c,c₁,c,c₂)` with `(+−),(c,c₂)` in the labelling `T̃_{(c₁,c₂)}`): paper-delta candidate T2427a. (Script checks of this form by the probe step, `lean_conv.py` in the scratchpad `T2427/`, are not repeated here; the Lean proof in (b) supersedes them.)

**(iv) TL1b plan** (`T2427_TL1b`, `BATwistAvgRec d → BATwistAvgProd d`; no net, T2413 §5): 1. fix `τ, D > 0` (`PrecL` = `StochDomAt`, `Chain/Carrier.lean:51`); `p ≥ (D+4)/τ`, `ε' ≤ dτ/2` small, `D' = 2p+2`; apply the pin. 2. Eventually `K W^{ε'} Bctl ≤ 1/2` (`Bctl ≤ W^{-2𝔡} + (N(1−t))⁻¹`: `Sizes.lam_sq_mul_pow_ge`, and `1−t ≥ 1−T₀ = Im z_n/(Im m + Im z_n)`). 3. Take `(c₁,c₂)` attaining `twAvgXmax` (`Finset.exists_mem_eq_sup'`): `X^{2p} ≤ 2K W^{ε'}B X^{2p−1} + 4pK W^{ε'}B² X^{2p−2} + 2N^{-D'}`. 4. S1: if `X ≤ B` done; else `X > B ≥ N⁻¹/(𝔡⁻²+1)` (`W^{-d} ≥ N⁻¹`, `λ ≤ 𝔡⁻¹`), so `N^{-D'}X^{2−2p} ≤ cN⁻⁴`, and `X ≤ α + √β ≤ C'W^{ε'}B`. 5. Markov per pair (`mul_meas_ge_le_integral_of_nonneg`, `Integrable` from `twAvgReg`): `μ{N^τB < ‖twTr‖} ≤ (C'W^{ε'}/N^τ)^{2p} ≤ C'^{2p}N^{-pτ}` (`Sizes.W_rpow_le`: `W^{ε'} ≤ N^{ε'/d} ≤ N^{τ/2}`). 6. Union over `|Zd × Zd| = L^{2d} ≤ N²` pairs (`measure_iUnion_fintype_le`): `≤ N^{-D}`, i.e. `BATwistAvgLaw`. Not proved here (statement only).

**(v) Predicted lines** (own estimates; basis `wc -l`: `Graph/BAExp14aB.lean` 733–870 = 138, `Graph/LWExpTerm.lean` 140–200 = 61, `Induction/EMn2Poly.lean` 63–300 = 238). Bottom-up. `TwistAvgA`: statements ≈ 95 (probe §1, 2, 5, 6), `Φ_p` polynomial + explicit `BAlwdf` ≈ 250, `lanlw` at `(w, Π_{c₂}w)` summed over `[c₁]` + transport (twice the 138) ≈ 280, twist algebra + identity ≈ 250, (iv) ≈ 330: ≈ 1,200. `TwistAvgA2`: CS (≈ 1.6 × 238) ≈ 380, `twAvgSPrec` ≈ 200, T.6 (≈ 2 × 61) ≈ 130, Hölder ≈ 150, pin proof ≈ 350, instances ≈ 70: ≈ 1,280. Top-down check: T2413 §7 row TL1a central 1,036, plus T.6 ≈ 150 and Hölder ≈ 100, = 1,286, × 1.5–2.1 (ticket) = 1,930–2,700 in total; the bottom-up total ≈ 2,480 lies inside this band, and the top of the band split evenly is ≈ 1,350 per file. Both files stay below the boundary-move threshold 1,700 (also at +30% on the bottom-up numbers: 1,560 and 1,660) and the stop line 2,000: T.6 stays in `TwistAvgA2`, the fallback (pin ends at (i)+(ii)) is not needed.

**Name clash** (`grep -rn --include='*.lean' -e twAvg -e BATwistAvgRec -e T2427_TL1b -e baTwistAvgRec RBM3D` outside the probe; same names in `RBM3D.lean` and in `docs/tickets/T2428–T2431.md`): 0 matches in each.
**Paper-delta candidates:** T2427a mirror form (above; plus `twTr c₁ c₂ = T̃_{(c₂,c₁)}`). T2427b `twAvgT6` is at the scale `N` and has no floor hypothesis `Y' > N^{-C₁}` (the bad-event term `N^{-D}(𝔼Y²)^{1/2}` does not involve `Y'`; `R ≥ 0` is assumed); the paper's `W^ε` is recovered in the pin by `N^{𝔠ε'} ≤ W^{ε'}` (`Bandwidth 𝔠`). T2427c the pin keeps `C_M` as `K = C_M + 1` fixed before `𝔠, sz, z` (the paper absorbs it into `W^ε`), as decided in (a).
**Open points for the 1a-audit:** `twAvgReg` (iv) contains the new fact `η_t⁻¹ + 1 ≤ N` eventually, uniformly in `t ≤ T₀` (`η_{T₀} = √T₀ Im z_n`; (a) prints `eta_(t0)=0.3061` at `n = 0`, equal to `√0.6937 · 0.3675`); the explicit `∂_{h_βα}Φ_p` (product rule through `lwWx_hasDerivAt_Gres`) is not an existing lemma; `T2427_TL1b` is statement-only.

## (a‴) Probe recompile (1a-audit repair) — Sun Oct 11 23:14:17 UTC 2026 (`date -u`)   [condensed by the 1b stage]

Rule (B) repair of the 1a-audit RETURN (`docs/reports/T2427-1a-audit.md`, "Required for resubmission" items 1-2), probe only, commit `73b3a8d` (parent `d60d13d`; clean tree): `twAvgReg` gets `0 < ε →` between `0 < κ →` and `BAFlow` (probe line 138); its two applications (lines 224, 235) get one more `(by norm_num)`. Recompile `lake env lean RBM3D/Probe/T2427Pins.lean` run Sun Oct 11 23:13:33 UTC 2026 .. 23:13:36 UTC: exit=0, no line with error or warning. Negative control (scratch copy with the old example lines): exit=1, first error at `224:83` (`flow_sz0` is expected to have type `0 < 1 / 10`).
```
$ git diff -U0 d60d13d 73b3a8d -- RBM3D/Probe/T2427Pins.lean   # the whole repair: 3 changed lines (138, 224, 235); lines 224, 235 only add `(by norm_num)`
-  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
+  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
```
The frames of `twAvgSPrec`, `BATwistAvgRec` (probe) and `BATwistAvgProd` (`BA/TwistPins.lean:154-155`) carry `0 < ε` already; the final `twAvgReg` states `0 < ε` in its statement and docstring (`BA/TwistAvgA.lean`). Paper-delta candidates: none new (T2427a-c stand).

## (b) Script output and narrative (stage 1b, `prover-max`, branch `t/T2427`; times from `date -u` or `git log` in the output)

**IBP route and form of (C.3)-(C.4) used.** Route **R-a**, mirror form, as chosen in (a″): `baLanlw_holds` (`Graph/BAExpand.lean:744`) with the resolvent polynomial `Φ_p = T^{p-1} conj(T)^p`, `T = twTr c₁ c₂` (`TwistAvgA_Phi`, `TwistAvgA_f_Phi`), at `(x, Π_{c₂}x)`, `x ∈ [c₁]`; `∂_{h_{βα}}Φ_p` is computed with `lwWx_hasDerivAt_Gres` (`TwistAvgA_dH_Phi`); the transport to `μ = seqP (sz.withLam 0)` follows `BAExp14a_lanlw_diag` (`Graph/BAExp14aB.lean:733`; `TwistAvgA_lanlw`, `TwistAvgA_lanlw_carrier`); the sum over `x ∈ [c₁]` is done in offset coordinates `x = (c,o)` (`TwistAvgA_M_pt`, `TwistAvgA_sum_M`): `TwistAvgA_algA` is (C.4′) (`Σ_β S_{αβ}Ǧ_{ββ} = tX_{[α]}` by `BAExp14a_sumS_GM`), `TwistAvgA_algB`, `TwistAvgA_algB2` are (C.5′), and `TwistAvgA_moment` assembles them into `twAvgMoment_holds`: `𝔼|T|^{2p} = t Σ_c M_{c₁c} 𝔼[X_c (M_{cc₂} + twTr c c₂) Φ] + t(p−1) 𝔼[𝒮₁ T^{p−2} T̄^p] + t p 𝔼[𝒮₂ |T|^{2p−2}]`, `X_c = 𝓛¹_c − m`, `Φ = T^{p−1}T̄^p`, `Ǧ = −M(V+tm)G`, `S° = W^{-d}1([α]=[β])` in `twAvgS1/2` with `t` outside (the Lean text of `twAvgMomentAt` is identical to the probe, diff below): paper-delta candidate T2427a. Step 4 is `twAvgSCS_holds` (Cauchy-Schwarz in the offsets, `TwistAvgA2_cs`, `TwistAvgA2_key1/key2`).

**Merged text of the pins against the probe** (script `diffprobe.py`: the `def` block of each pinned name in `RBM3D/Probe/T2427Pins.lean` at `73b3a8d` against `TwistAvgA.lean`/`TwistAvgA2.lean`, docstrings excluded):
```
identical (text of the `def` block, docstrings excluded): twAvgGPM twAvgGPG twAvgS1 twAvgS2 twAvgX twAvgXmax twAvgMomentAt twAvgMoment twAvgSCS twAvgSPrec twAvgT6 twAvgReg BATwistAvgRecAt BATwistAvgRec T2427_TL1b
different: none
diff probe vs merged BATwistAvgRec: empty
```
**Line counts against the stop line, builds, axioms, checks, greps** (script `evidence4.sh`, one run, output verbatim):
```
$ date -u; git rev-parse --short HEAD; git status --short | wc -l
Mon Oct 12 00:52:32 UTC 2026
fdb7420
       0
$ per commit of 0a8176c..HEAD touching RBM3D/BA: hash, commit time (UTC), `wc -l` of TwistAvgA.lean, TwistAvgA2.lean at that commit (stop line 2000 per file, boundary move 1700)
0c2ebd6 Sun Oct 11 23:57:44 UTC A=1084 A2=0 T2427: TwistAvgA, Steps 1-3 of Lemma T.7 (twAvgMoment_holds), 
d31af09 Mon Oct 12 00:16:17 UTC A=1084 A2=737 T2427: TwistAvgA2 (partial), Step 4 (twAvgSCS_holds, twAvgSPre
39a82a8 Mon Oct 12 00:24:55 UTC A=1084 A2=1228 T2427: TwistAvgA2, baTwistAvgRec_holds (Step 5 first display),
3e4b094 Mon Oct 12 00:42:34 UTC A=1084 A2=1228 T2427: module docstrings, helpers carry the stem (not private)
fdb7420 Mon Oct 12 00:45:27 UTC A=1085 A2=1228 T2427: twAvgReg docstring, the envelopes used (Kenv = 1 and 5)
$ git diff --stat main...t/T2427   # the probe is on the branch and is never merged
 RBM3D/BA/TwistAvgA.lean    | 1085 ++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistAvgA2.lean   | 1228 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2427Pins.lean |  275 ++++++++++
 3 files changed, 2588 insertions(+)
$ lake build RBM3D.BA.TwistAvgA RBM3D.BA.TwistAvgA2 | tail -1 ; lake build | tail -1
Build completed successfully (4007 jobs).
Build completed successfully (4242 jobs).
$ lake env lean axchk.lean   # imports RBM3D + both modules: #print axioms of the six theorems, then #assert_rbm_axioms
exit=0
'RBM.BA.twAvgMoment_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgReg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgSCS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgSPrec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twAvgT6_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistAvgRec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 12336 theorems, 3818 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean docs/tickets/checks/T2427-check.lean
exit=0 error-lines=0
$ grep -c -E "sorry|admit|native_decide|^axiom" ; grep -c -E "Step2Gen_|STthetaOpg" ; grep -c "^private "   (TwistAvgA.lean, TwistAvgA2.lean)
RBM3D/BA/TwistAvgA.lean:0 RBM3D/BA/TwistAvgA2.lean:0
RBM3D/BA/TwistAvgA.lean:0 RBM3D/BA/TwistAvgA2.lean:0
RBM3D/BA/TwistAvgA.lean:0 RBM3D/BA/TwistAvgA2.lean:0
$ rule (E): declarations (theorem|def|abbrev|instance|lemma) in the two files without the stem TwistAvgA_ / TwistAvgA2_ (the pins and the targets), and counts
twAvgGPM twAvgGPG twAvgS1 twAvgS2 twAvgX twAvgXmax twAvgMomentAt twAvgMoment twAvgReg BATwistAvgRecAt BATwistAvgRec twAvgReg_holds twAvgMoment_holds twAvgSCS twAvgSPrec 
twAvgT6 twAvgSCS_holds twAvgSPrec_holds twAvgT6_holds baTwistAvgRec_holds T2427_TL1b
all:      136; with stem: 115; without stem: 21
$ name clash: grep -rn --include=*.lean -e twAvg -e BATwistAvgRec -e T2427_TL1b -e baTwistAvgRec -e TwistAvgA RBM3D RBM3D.lean | wc -l   (main worktree; then git grep -l per sibling branch)
main edeea3d
       0
t/T2420:0 t/T2421:0 t/T2422:0 t/T2423:0 t/T2424:0 t/T2425:0 t/T2426:0 t/T2428:0 t/T2429:0 t/T2430:0 t/T2431:0 t/T2432:0 
```
**Target statements** (extracted from the files by script: the six theorem lines, then the def blocks of `BATwistAvgRecAt` (conclusion of target 1) and `BATwistAvgRec`; the other pins are in the diff above):
```
$ grep -n -E "^theorem (twAvg[A-Za-z0-9]*_holds|baTwistAvgRec_holds)" RBM3D/BA/TwistAvgA.lean RBM3D/BA/TwistAvgA2.lean
TwistAvgA.lean:613: theorem twAvgReg_holds (d : ℕ) : twAvgReg d := by
TwistAvgA.lean:1050: theorem twAvgMoment_holds (d : ℕ) : twAvgMoment d := fun κ ε 𝔠 𝔡 sz z hκ hflow n t ht0 ht p hp c₁ c₂ =>
TwistAvgA2.lean:460: theorem twAvgSCS_holds (d : ℕ) : twAvgSCS d := by
TwistAvgA2.lean:490: theorem twAvgSPrec_holds (d : ℕ) : twAvgSPrec d := by
TwistAvgA2.lean:574: theorem twAvgT6_holds : twAvgT6 := by
TwistAvgA2.lean:1040: theorem baTwistAvgRec_holds (d : ℕ) : BATwistAvgRec d := by
$ awk (the def block of each pin up to the blank line): BATwistAvgRecAt, BATwistAvgRec   [TwistAvgA.lean]
def BATwistAvgRecAt (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ c₁ c₂ : Zd d (sz.L n),
    twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p) ≤
      K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n)) * (twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 1) + twAvgXmax C μ n (t n) p * twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 1)) +
      2 * (p : ℝ) * K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n) ^ 2) * twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 2) + ((sz.size n : ℕ) : ℝ) ^ (-D)
def BATwistAvgRec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ K : ℝ, 0 < K ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgRecAt (baFMz sz z) μ t K
```
**Compiled nonempty instances** (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, `t ≡ 1/2`; `n = 0` (`L = 4`, `W = 32`), `p = 1, 2`, `c₁ = 0`, `c₂ = (1,0,0) ≠ c₁`). Per index: TwistAvgA 1061, 1065 (i) at `p = 1, 2`; 1069 `(1,0,0) ≠ 0`; 1075 (iv); TwistAvgA2 1167, 1174 target 1 (the second at a pair `c₂ ≠ c₁`); 1189 (ii) pathwise; 1193 (ii) `≺`; 1202 (iii) at `Y ≡ 1`; 1222 the TL1b interface. Only the other gates' pins `LWAvgLawgL`, `STLmaxgL` stay hypotheses (1167, 1174, 1193, 1202).
```
$ grep -n "^example" RBM3D/BA/TwistAvgA.lean RBM3D/BA/TwistAvgA2.lean | cut -d: -f1,2 | paste -sd" " -
TwistAvgA:1061 TwistAvgA:1065 TwistAvgA:1069 TwistAvgA:1075 TwistAvgA2:1167 TwistAvgA2:1174 TwistAvgA2:1189 TwistAvgA2:1193 TwistAvgA2:1202 TwistAvgA2:1222
$ the two instances of target 2 (i) (TwistAvgA.lean) and the first instance of target 1 (TwistAvgA2.lean), extracted by awk
example : twAvgMomentAt sz0 zSeq 0 (1 / 2) 1 0 ![1, 0, 0] :=
  twAvgMoment_holds 3 (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0 0 (1 / 2) (by norm_num) (half_lt_t0 0).le 1 le_rfl 0 ![1, 0, 0]
example : twAvgMomentAt sz0 zSeq 0 (1 / 2) 2 0 ![1, 0, 0] :=
  twAvgMoment_holds 3 (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0 0 (1 / 2) (by norm_num) (half_lt_t0 0).le 2 (by norm_num) 0 ![1, 0, 0]
example (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    ∃ K : ℝ, 0 < K ∧ BATwistAvgRecAt (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) K := by
  obtain ⟨K, hK, H⟩ := baTwistAvgRec_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨K, hK, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM⟩
```
**Ports.** None from `../RBM1D`, `../RBM2D`: `grep -n -i -E 'RBM1D|RBM2D'` on the two files gives 0 matches, and the tool log of this stage has no read, grep, build or git command on them (a scan of the log finds the two names only in this report's own drafting and checking commands); no diff-stat. Inside RBM3D, patterns rewritten here (not copied): `BAExp14a_lanlw_diag` (`Graph/BAExp14aB.lean:733`) for `TwistAvgA_lanlw`; `lwExpTerm_prec_integral`, `lwExpTerm_first_moment` (`Graph/LWExpTerm.lean:143`, `:113`; the T.6 basis named in the ticket) for `twAvgT6_holds`; for `TwistAvgA2_cs` the idea of `sum_pair_le` (`Induction/EMn2Poly.lean:91`, private there).

**Narrative.**
1. `TwistAvgA` (1085 lines): §1 pins (text of the probe at `73b3a8d`); §2 offset coordinates `pt c o`; §3 `Φ_p`, `∂Φ_p` at the level of one size (`Ω d L W`); §4 `lanlw` with `f = Φ_p` at the BA law; §5 bounded continuous functions; §6 `twAvgReg_holds` (continuity; `‖twTr‖ ≤ η⁻¹+1`, `‖𝒮_i‖ ≤ N(η⁻¹+1)³`; eventually `η⁻¹+1 ≤ N` from `η_t ≥ (Im z_n/2)κ` and `N^ε → ∞`); §7 twist algebra; §8 `twAvgMoment_holds`; §9 instances.
2. `TwistAvgA2` (1228 lines): §1 loops of the carrier as traces on the fine lattice (`TwistAvgA2_loop_eq`) and Hilbert-Schmidt sums (`TwistAvgA2_HS`, `L2`, `L4a`, `L4b`); §2 `𝒮₁`, `𝒮₂` in offsets, `key1/key2`; §3 `twAvgSCS_holds`, `twAvgSPrec_holds` (`StochDomAt.of_subset_union` with `STLmaxgL` at `k = 4` (`B³`) and `k = 2` (`B`); `C_M = c⁻¹ expC k c` from `BAMB_row_l1` at `Λ = 𝔡⁻¹`, eventually by `BAflow_lam0_window`); §4 `twAvgT6_holds`; §5 Hölder, Lyapunov; §6 `TwistAvgA2_F1`, `G23`, `core`, `err` and `baTwistAvgRec_holds`; §7 instances.
3. `baTwistAvgRec_holds`: `K = C_M + 1` fixed before `𝔠, sz, z`; T.6 is applied at `ε₁ = 𝔠ε'`, `D₁ = D + 2p + 1`, with `Kenv = 1` for `ξ_c = ‖𝓛¹_c − m‖` and `Kenv = 5` for `‖𝒮₁‖ + ‖𝒮₂‖`; `N^{𝔠ε'} ≤ W^{ε'}` from `Bandwidth 𝔠`; the error terms are absorbed by `TwistAvgA2_err` for `N ≥ 2C_M + 2p`; for `p = 1` the `𝒮₁` term has the factor `p − 1 = 0` (case split `p < 2` in `TwistAvgA2_core`).
4. No hypothesis was added and no signature changed (the 15 pins are textually those of the probe, diff above). The exponent count of (a) is used as stated: `(B³·B)^{1/2} = B²` (sharp), coefficients `(p−1) + p = 2p−1 ≤ 2p`. Lines 1085 and 1228 against the predicted ≈ 1,200 and ≈ 1,280 ((a″) (v)): neither file reached the boundary-move threshold 1,700 or the stop line 2,000 (per-commit table above).

## (c) Verified Mathlib names (44 `#check`-ed; 43 occur in the compiled declarations of the two modules, script output below)
```
$ lake env lean names.lean     # one `#check @<name>` line per name
exit=0; #check lines: 44; output lines containing 'error': 0
$ lake env lean used.lean      # constants in the types/values of all declarations of RBM3D.BA.TwistAvgA, RBM3D.BA.TwistAvgA2
declarations scanned: 193; names: 44; occurring in them: 43; not occurring: #[Set.mem_ofPred_eq]
$ grep -rn --include='*.lean' -w -e trace_submatrix_equiv -e trace_reindex -e trace_reindexAlgEquiv Mathlib | wc -l; then the existing/deprecated names:
       0
LinearAlgebra/Matrix/Trace.lean:182:lemma trace_submatrix_succ {n : ℕ} [AddCommMonoid R]
MeasureTheory/Integral/Bochner/Basic.lean:253:@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum
Data/Set/Operations.lean:81:@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq
```
- Matrix and lists: `Matrix.submatrix_diagonal_equiv` (`(diagonal d).submatrix e e = diagonal (d ∘ e)`), `Matrix.submatrix_mul_equiv`, `Matrix.submatrix_one_equiv`, `Matrix.conjTranspose_mul`, `Matrix.mul_diagonal`, `Matrix.diagonal_conjTranspose`, `List.ofFn_eq_map` (`List.ofFn f = List.map f (List.finRange n)`)
- Sums and Cauchy-Schwarz: `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Finset.sum_mul_sq_le_sq_mul_sq`, `Real.abs_le_sqrt` (`x ^ 2 ≤ y → |x| ≤ √y`), `Real.sqrt_mul`, `Finset.le_sup'`; derivatives: `HasDerivAt.fun_sum`, `HasDerivAt.pow`, `HasDerivAt.mul`, `HasDerivAt.const_mul`, `HasDerivAt.sub_const`
- Hölder and `L^p`: `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` (with `p.HolderConjugate q`), `Real.HolderConjugate`, `Real.HolderConjugate.two_two`, `MeasureTheory.MemLp.of_bound`, `MeasureTheory.MemLp.indicator`, `MeasureTheory.memLp_const`, `MeasureTheory.memLp_two_iff_integrable_sq`, `MeasureTheory.Integrable.of_bound`
- Integrals and measures: `integral_complex_ofReal` (`∫ ↑(f x) = ↑(∫ f x)`), `MeasureTheory.integral_finsetSum`, `MeasureTheory.integral_mono_of_nonneg`, `MeasureTheory.integral_indicator_const`, `MeasureTheory.probReal_univ`, `MeasureTheory.measure_toMeasurable`, `MeasureTheory.measurableSet_toMeasurable`, `ENNReal.toReal_le_of_le_ofReal`
- Reals: `norm_add₃_le`, `Complex.mul_conj'` (`z * conj z = ↑‖z‖ ^ 2`), `Nat.cast_pred`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`, `Real.sqrt_eq_rpow` (`√x = x ^ (1/2)`), `tendsto_rpow_atTop`
- Named in a `simp only` list without effect on the term: `Set.mem_ofPred_eq`. Deprecated in this Mathlib (aliases, last grep block): `integral_finset_sum` → `integral_finsetSum`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`. Verified absent (0 matches): `Matrix.trace_submatrix_equiv`, `Matrix.trace_reindex`, `Matrix.trace_reindexAlgEquiv` (only `trace_submatrix_succ` exists); `TwistAvgA2_trace_submatrix` is proved from `Equiv.sum_comp`.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates (proposed in (a″), now proved; none new at 1b): **T2427a** mirror form (`Ǧ = −M(V+tm)G`, `twTr c₁ c₂ = T̃_{(c₂,c₁)}`); **T2427b** `twAvgT6` is stated at the scale `N` and has no floor hypothesis `Y' > N^{-C₁}` (row 10 of (a) is not used); **T2427c** the pin keeps `K = C_M + 1` fixed before `𝔠, sz, z`.
- Hub: `RBM3D.lean` is unchanged on the branch (the diff stat above lists 3 files); at merge add `import RBM3D.BA.TwistAvgA` then `import RBM3D.BA.TwistAvgA2` after the last import line. `RBM3D/Probe/T2427Pins.lean` stays on `t/T2427` and is not merged. Registry: none (ticket; `RBM3D/Test/Axioms.lean` is not in the diff stat).
- Observation (rule (E)): the helpers are public and stem-prefixed (115 of 136 declarations; the other 21 are the 15 pins and the 6 targets, list above); none is `private`. The dispatcher may ask for `private` if the surface is unwanted.
- Interface to TL1b: `T2427_TL1b` (statement only) with its `Iff.rfl` check; per the plan in (a″) (iv), TL1b needs `baTwistAvgRec_holds` and, for the Markov step, the integrability part of `twAvgReg_holds`.
- Process: (a″), (a‴) were condensed by this stage to stay within the line cap; section (a) is unchanged and no (a′) was needed. After the last proof commit `39a82a8` two comment-only commits: `3e4b094` (module docstrings: "helpers", not "private helpers") and `fdb7420` (`twAvgReg` docstring: `Kenv = 1` and `5`, as used); the `def` blocks of the pins are unchanged (diff above).
