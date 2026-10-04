Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 21:50:25 UTC 2026

Notation: `g = sz.lam n`, `L = sz.L n`, `W = sz.W n`, `A = g²W^d`, `ρ = (1-s)/(1-u)`, `|x| = zdistInf`, `Θ = Theta (u·1)` (σ₁≠σ₂: `μ = m(σ₁)m(σ₂) = |m|² = 1`), `Θ̊ = Theta0 = Θ - 1/((1-u)L^d)`, `T_v(r) = tailT` at time `v`, `λ = Bctl_s^{1/5}`. Core data: `|X_b| ≤ λ W^{-d}T_s(|b₁-b₂|) + F` (this is `STDecay` at `s`, `F = W^{-D'}`). Routes: `step5Kernel_UN_decompU` (Step5Kernel:74), `step5Kernel_profile_explicit_holds` (:199), `prop8ZeroMode_holds` (Prop5Hold:1261), `prop5Decay_holds` (:784), `prop5Short_holds` (Prop5Short:400), `sum_norm_Theta_row_le` (Props4:210), `st5_Bctl_ge` (Step5Kit:120), `st5_prec_mono` (:45), `abs_lemE_le` (Semicircle:309).

### (i) Exponent table

| # | quantity | value / form | constraint, slack |
|---|---|---|---|
| 1 | kernel, `uKer = (1-sμS)Θ_{uμ}` | `(s/u)·1 + ((u-s)/u)Θ_u` for `u>0` (decompU) | `u = 0` forces `s = u = 0`, `uKer = 1`: separate (trivial) case; script (2) |
| 2 | `Q^{(1)}∘𝒰^{(2)}X` (ticket (i)) | exact: `Σ_b (QU)(a₁,b₁) U(a₂,b₂) X_b`, `QU = (s/u)(I-J/L^d) + ((u-s)/u)Θ̊_u`, `U = (s/u)I + ((u-s)/u)Θ_u`; **not** the single term `(1-s)²Θ̊XΘ` but 4 terms (as `3_5:2080-2085`) | `Û(0) = ρ`, `Θ` row sum `= 1/(1-u)` (`sum_norm_Theta_row_le`); identity residual `2.2e-16`, script (2) |
| 3 | `(u-s)/u` | `≤ 1-s` exactly (`u-s ≤ u(1-s) ⇔ s(1-u) ≥ 0`) | slack `s(1-u)/u`; at `(15/16,31/32)`: `1/31 ≤ 1/16`. Paper's `(1-s)` is right, no factor 2 |
| 4 | regime upper `1-s ≤ g²/L²` | used in steps 2, 4: `(1-s)g^{-2}L² ≤ 1`; and `1-s ≤ g²` so `(g²+1-s)^{-1} ∈ [1/(2g²), 1/g²]` | slack: `1/16` vs `1/16` (instance A, equality), `1/32` vs `1/16` (B) |
| 5 | regime lower `1-u ≥ g²/L^d` (`≥ 1-t`) | gives `B_{s,0} ≤ 2/g²` (zero mode `(L^d(1-s))^{-1} ≤ g^{-2}`) and `ρ ≤ L^{d-2}` | `B_{s,0}g² ∈ [1.08, 2.0)` in script (3). Hence `λ ≤ 2^{1/5}(W^{-d}g^{-2})^{1/5} = 2^{1/5}A^{-1/5}`; only the upper bound is needed (`st5_Bctl_ge` is the lower one, not used) |
| 6 | time monotonicity of the profile | `T_s(K) ≤ T_u(K)` for `s ≤ u`: `(g²+1-s)^{-1} ≤ (g²+1-u)^{-1}`, `(L^d(1-s))^{-1} ≤ (L^d(1-u))^{-1}`, `ℓ_s ≤ ℓ_u` | script (5): 0 violations. Handles the identity-term and the `X` factor; `e^{-√(r/ℓ)} ≥ e^{-1}` for `r ≤ L` when `ℓ_u = L` (`1-u ≤ g²/L²`) so `tailW`'s `min(r,L)` is inactive (`|x| ≤ L`) |
| 7 | zero-mode average of the profile | `L^{-d}Σ_c(|c-a₂|+1)^{-(d-2)} ≤ C_d L^{2-d}`, `C_3 ≈ 3` | script: `Σ_c 1/(|c|+1)/L² = 2.06, 2.30, 2.57, 2.75` at `L = 7,11,21,41` (→3). `g^{-2}L^{2-d} ≤ (L^d(1-u))^{-1}` by row 4, so `Q`'s average term `≲ (L^d(1-u))^{-1} ≲ T_u(|a|)` (here `ℓ_u = L`) |
| 8 | the four `≲` of `3_5:2275-2281` (kernel time `u`, not `t`) | S1 = `(1-s)²Σ m₁Φ'm₃` → S2 = `(1-s)Σ_{b₁}m₁(g^{-2}(r+1)^{-1}+(L^d(1-u))^{-1})` → S3 = `(1-s)g^{-4}L²/(r+1) + (1-s)g^{-2}L²/(L^d(1-u))` → S4 = `g^{-2}/(r+1) + (L^d(1-u))^{-1} ≤ 2B_{u,r}` → `≲ T_u(r)`; `m₁ = g^{-2}(r+1)^{-1}` (prop8, `zdistD ≥ zdistInf` direction ok), `Φ' = g^{-2}(r+1)^{-1} + (L^d(1-s))^{-1}`, `m₃` = same with `1-u` | steps 1→2: `Σ_{b₂}` convolution `≲ L/(…)≤L²/(r+1)` and `Σ_{b₂}Θ = 1/(1-u)` for the zero-mode piece; 3→4 is exactly row 4. None fails; measured ratios script (5): `3.8, 2.8, 1.0, 2.0` at `L=51`, saturating |
| 9 | constants | `C = C(d,Λ,κ_m)`, `Λ = 𝔡⁻¹` (`lam ≤ 𝔡⁻¹`, `WO`), `κ_m = √(κ(4-κ))/2` (`|E| ≤ |Re z| ≤ 2-κ` by `abs_lemE_le`; `Im m(E) = √(4-E²)/2 ≥ κ_m`) | from `STFlow` only; `g > 0` from `WO`; `t ≤ lemT z < 1` (`lemT_lt_one`); measured `sup|Θ̊|/[(g²+1-u)^{-1}(r+1)^{-1}] ≤ 1.74`, `sup|Θ|/T_u ≤ 1.94` (`L=51`) |
| 10 | floor `F` | `Σ_b|QU||U| ≤ Cρ` (row sums; `R2/ρ ∈ [1.0, 2.1]` at `g ≤ 1`) so floor `≤ C ρ F`, `ρ ≤ L^{d-2} ≤ N ≤ W^{1/𝔠}` (Bandwidth `N^𝔠 ≤ W`) | take `D' = D + 1/𝔠 + 1` (`STDecay` is `∀D`): `CρW^{-D'} ≤ CW^{-D-1} ≤ W^{-D}` once `W ≥ C` (`N → ∞`). Paper's `W^{-D}` kept only after this shift (cf. D364 for the neighbouring display) |
| 11 | `σ₁=σ₂` (`Q = ∅`) | `U = (s/u)I + ((u-s)/u)Θ_{uμ}`, `|Θ_{uμ}(0,x)| ≤ C(1_{x=0}+g²e^{-c|x|₁})` (`prop5Short_holds`) | regime not needed beyond `s ≤ u` (row 6) and `Σ|U| ≤ C`; `R1/(W^{-d}T_u) ≤ 1.0` in script (3). Dimension-specific: polynomial `B_{u,0} ≤ (r+1)^{d-2}B_{u,r}` absorbs `e^{-c m}` |
| 12 | `Prec` lift (target 3) | bad set of `QUX` at `(τ, D)` ⊂ bad set of `STDecay_s` at `(τ/2, D')` once `C ≤ N^{τ/2}` (`st5_prec_mono`, `c = C`); union over `(σ,b)` is inside `P`, so no polynomial index count is needed; `u` enters only via the kernel (`X` at `s` is `u`-free) | 4 sign classes covered by `st5_prec_cover`; eventual `n` for `WO`, `Bandwidth`, `N → ∞` |

### (ii) One concrete nondegenerate instance (command `cd <scratchpad>/T2163 && python3 report.py`, scratch files `ratio.py`, `chain.py`, `report.py`; output verbatim)

```
== (1) instances: hypotheses of the core (E=1, Lam=1, kappa=1; Im m = sqrt(3)/2 = sqrt(kappa(4-kappa))/2)
A szB-data         L=4 g=1 s=15/16 u=31/32 1-s=1/16 g^2/L^2=1/16 1-u=1/32 g^2/L^d=1/64 all_hold=True failing=[]
   mixed max_a R1/(W^-d T_u)=3.313  R2/rho=1.992  total(D=2,W=2)=3.919  B0*g^2=1.191
   same  max_a R1/(W^-d T_u)=0.828  R2/rho=1.077  total(D=2,W=2)=1.042  B0*g^2=1.191
B interior         L=4 g=1 s=31/32 u=125/128 1-s=1/32 g^2/L^2=1/16 1-u=3/128 g^2/L^d=1/64 all_hold=True failing=[]
   mixed max_a R1/(W^-d T_u)=2.504  R2/rho=1.975  total(D=2,W=2)=2.643  B0*g^2=1.470
   same  max_a R1/(W^-d T_u)=0.900  R2/rho=1.019  total(D=2,W=2)=1.005  B0*g^2=1.470
ticket L=3,g=1/2   L=3 g=1/2 s=15/16 u=31/32 1-s=1/16 g^2/L^2=1/36 1-u=1/32 g^2/L^d=1/108 all_hold=False failing=['reg_s']
== (2) identity, row sums, coefficient (L=4,g=1,s=15/16,u=31/32)
max|QU-[(s/u)(I-J/L^d)+((u-s)/u)Theta0]|=2.2e-16  Uhat(0)=2.000000 (1-s)/(1-u)=2.000000  rowsum Theta=32.000000 1/(1-u)=32.000000
(u-s)/u=0.03226 <= 1-s=0.06250 ;  max over grid 0<=s<=u<1 of ((u-s)/u)/(1-s) = 1.0000
== (3) ticket grid: d=3, L in {7,11}, g in {1/2,1}, (1-s,1-u) in {g2/L2,g2/L3}^2 with u>=s, D in {2,4}, W=2: worst over D and ends
sign  L  g   max R1/(W^-d T_u)   max R2/rho   max total   B0*g^2 range   lam/A^-1/5 range
mixed  7 0.5     5.186           2.005        9.404    [1.123,1.997]   [1.023,1.148]
mixed  7 1.0     5.324           2.058       12.827    [1.123,1.997]   [1.023,1.148]
mixed 11 0.5     6.163           2.009       14.046    [1.083,1.999]   [1.016,1.149]
mixed 11 1.0     6.389           2.083       20.222    [1.083,1.999]   [1.016,1.149]
same   7 0.5     1.000           1.003        1.138    [1.123,1.997]   [1.023,1.148]
same   7 1.0     1.000           1.046        1.108    [1.123,1.997]   [1.023,1.148]
same  11 0.5     1.000           1.001        1.139    [1.083,1.999]   [1.016,1.149]
same  11 1.0     1.000           1.020        1.108    [1.083,1.999]   [1.016,1.149]
== (4) trend of the worst mixed ratio, 1-s=g^2/L^2, 1-u=g^2/L^3, g=1 (saturation in L)
L= 7 max ratio 5.324; L=15 max ratio 7.029; L=31 max ratio 8.184; L=51 max ratio 8.710; 
== (5) the four steps of 3_5:2275-2281 with majorants (kernel time u), mixed, g=1, 1-s=g^2/L^2, 1-u=g^2/L^3
L   S1/S2   S2/S3   S3/S4   S4/T_u   sup|Theta0|/[(g^2+1-u)^-1 (r+1)^-1]   sup|Theta|/T_u
 7  3.075   2.140   1.000   1.926         1.541                                  1.553
11  3.316   2.388   1.000   1.963         1.623                                  1.680
21  3.582   2.644   1.000   1.994         1.693                                  1.824
51  3.805   2.841   1.000   2.014         1.738                                  1.937
violations of T_s(K) <= T_u(K) for s<=u: 0
```

Reading: instance A is the merged `szB`/`(15/16, 31/32)` data (`L = 4`, `g = 1`; `1-s = g²/L²` is the boundary of regime (ii), `s < u`, `W = 2`, `D = 2`, `E = 1`, `Λ = 1`, `κ = 1`); instance B is interior (`1-s = 1/32 < 1/16`, `1-u = 3/128 ∈ [1/64, 1/32]`). All hypotheses of the core hold and both signs have nonzero data. No external hypothesis: every input (`prop8ZeroMode_holds`, `prop5Short_holds`, `prop5Decay_holds`) is a merged theorem; the only hypothesis left open is the `STDecay`/`STIngR5` premise, which the instance `inst_iniTermII` (`Step5Pins:980`, `szB`, premises `szB_reg5II` compiled) already discharges. Limit check (not an external hypothesis, but the uniformity in `L`): worst mixed ratio `5.3, 7.0, 8.2, 8.7` at `L = 7, 15, 31, 51`, successive increments `1.7, 1.2, 0.5` per doubling of `L`, i.e. saturating.

### Verdicts

- **Target 1** `stIniTermII_holds`: **PASS** (both conjuncts close with `C = C(d,Λ,κ_m)`, floor shifted by `D' = D + 1/𝔠 + 1`).
- **Target 2** (core): **PASS** with three corrections to the ticket text. (1) The core must carry the regime hypotheses `1-s ≤ g²/L²` and `g²/L^d ≤ 1-u` (and `0 ≤ s ≤ u < 1`, `0 < g ≤ Λ`, `|E| ≤ 2-κ`); (2) the floor coefficient is `Cρ`, `ρ = (1-s)/(1-u)` (not `W^{-D}` alone); (3) the correct kernel form is the exact four-term expansion of row 2 with `(u-s)/u ≤ 1-s` (paper's `(zYU2)` second term is the `Θ̊XΘ` part; the other three are covered by `(uwp2-92kj)` = `step5Kernel_profile_explicit_holds` with `(u,t) → (s,u)` and row 7).
- **Ticket instance defect.** The ticket's compiled instance `d=3, L=3, g=1/2, W=2, s=15/16, u=31/32, D=2` violates `1-s ≤ g²/L²` (`1/16 > 1/36`, script (1), `failing=['reg_s']`): not an instance of the core. Use `L = 4, g = 1` (instance A) or instance B. (Not a RETURN of the pin: the sequence-level instance `szB` is fine.)
- **Target 3** (`Prec` lift to `STIniTermConcl`): **PASS** (row 12; needs `SizeTendsto`, `Bandwidth`, `WO` from `STFlow`).
- Paper-delta candidates: `T2163a` (`(zYU2)` second term is one of four, exact coefficients `((u-s)/u)²`, `(u-s)/u ≤ 1-s`); `T2163b` (kernel time is `u`, not `t`, in `3_5:2275-2281`; floor `Cρ W^{-D'}`, `D' = D + 1/𝔠 + 1`); `T2163c` (ticket instance `L=3, g=1/2` outside regime (ii)).

section-a verdict: PASS

## (b) Script output — Sun Oct  4 22:34:02 UTC 2026

```
$ git log --oneline -3; git diff --stat main...t/T2163; git status --short
fc3a463 T2163: S5-27 initial term of Step 5, case (ii): stIniTermII_holds
543fb92 T2163: WIP IniTermII (core, lift, pin)
88183f4 T2160: merge ST2-35 Induction/AzumaProxyN2
 RBM3D/Induction/IniTermII.lean | 1804 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    1 -
 2 files changed, 1804 insertions(+), 1 deletion(-)

$ lake build RBM3D.Induction.IniTermII 2>&1 | tail -2; (same build) 2>&1 | grep -c "IniTermII.lean:"   # warnings/errors from this file
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3778 jobs).
0

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/IniTermII.lean; wc -l RBM3D/Induction/IniTermII.lean
    1804 RBM3D/Induction/IniTermII.lean

$ lake env lean <scratchpad>/T2163/axioms_all.lean   (#print axioms of every public declaration)
'RBM.Gauss.Sizes.stIniTermII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermII_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermII_core_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.iniTermII_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermII_core_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermII_core_same_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.iniTermII_concl_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_iniTermII_proved' depends on axioms: [propext, Classical.choice, Quot.sound]

$ registry pre-check (CLAUDE.md §20; temp file, not committed): import RBM3D; import RBM3D.Induction.IniTermII; #assert_rbm_axioms
exit=0
axiom audit: 4831 theorems, 1711 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).

$ full lake build with the root import added temporarily after the last import line of RBM3D.lean (reverted; the commit does not touch RBM3D.lean)
exit=0
1849:info: RBM3D.lean:210:0: axiom audit: 4831 theorems, 1711 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3932 jobs).
$ git status --short   # after the revert
(clean)

$ python3 check_inst.py   # numerical check at the Lean instance data (scratch file <scratchpad>/T2163/check_inst.py)
mixed: max|Q^(1)(K x K) X - (K - rho L^-d J) x K X| = 2.16e-15 ; column sums of K: min 2.000000 max 2.000000 ; rho = 2.000000
mixed: max_a |Q^(1) U X|(a) / [lam W^-d T_u(|a1-a2|) + rho W^-D] = 0.1596   (the constant C of the Lean bound, M=1)
same : max_a |U X|(a) / [lam W^-d T_u(|a1-a2|) + W^-D] = 0.9175
alpha=s/u=0.96774 beta=(u-s)/u=0.03226 <= 1-s=0.06250 ; alpha+beta/(1-u)=2.000000 = rho=2.000000
```
```
$ sed -n 331,333p RBM3D/Induction/Step5Pins.lean     # the pin as merged
def STIniTermII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t =>
    STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)

$ python3 extract.py stIniTermII_holds iniTermII_core iniTermII_core_same iniTermII_concl    # targets 1, 2, 3, statements as in the file
RBM3D/Induction/IniTermII.lean:1718-1718
theorem stIniTermII_holds (d : ℕ) : STIniTermII d

RBM3D/Induction/IniTermII.lean:1051-1059
theorem iniTermII_core (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖zeroModeSet d L {0} (RBM.Ind.Ugen d L g E σ s u X) a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D))

RBM3D/Induction/IniTermII.lean:1378-1385
theorem iniTermII_core_same (d : ℕ) (Λ κm : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκm : 0 < κm) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E s u M lam : ℝ), 0 < g → g ≤ Λ → 0 < W →
        |E| ≤ 2 → κm ≤ (mE E).im → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d L) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d L g s (zdistInf d L (b 0 - b 1) : ℕ) + W ^ (-D))) →
          ∀ a, ‖RBM.Ind.Ugen d L g E σ s u X a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d L g u (zdistInf d L (a 0 - a 1) : ℕ) + W ^ (-D))

RBM3D/Induction/IniTermII.lean:1664-1667
theorem iniTermII_concl {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5II sz s t) (hDec : STDecay sz (STflowE z) s) :
    STIniTermConcl sz {0} STSigMixed (STflowE z) s t ∧ STIniTermConcl sz ∅ STSigSame (STflowE z) s t

$ python3 extract.py iniTermII_core_inst iniTermII_core_same_inst iniTermII_concl_inst inst_iniTermII_proved   # the compiled nonempty instances (§12 of the file; proofs omitted)
RBM3D/Induction/IniTermII.lean:1751-1756
theorem iniTermII_core_inst : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
    ‖zeroModeSet 3 4 {0} (RBM.Ind.Ugen 3 4 1 1 ![true, false] (15 / 16) (31 / 32)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (15 / 16) (zdistInf 3 4 (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ))) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (31 / 32) (zdistInf 3 4 (a 0 - a 1) : ℕ) +
        (1 - 15 / 16) / (1 - 31 / 32) * (2 : ℝ) ^ (-(2 : ℝ)))

RBM3D/Induction/IniTermII.lean:1771-1776
theorem iniTermII_core_same_inst : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
    ‖RBM.Ind.Ugen 3 4 1 1 ![true, true] (15 / 16) (31 / 32)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (15 / 16) (zdistInf 3 4 (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 4 1 (31 / 32) (zdistInf 3 4 (a 0 - a 1) : ℕ) +
        (2 : ℝ) ^ (-(2 : ℝ)))

RBM3D/Induction/IniTermII.lean:1792-1794
theorem iniTermII_concl_inst (hDec : STDecay szB (STflowE zB) (fun _ => 15 / 16)) :
    STIniTermConcl szB {0} STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
      STIniTermConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)

RBM3D/Induction/IniTermII.lean:1799-1801
theorem inst_iniTermII_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)
      szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd

$ name-clash grep of the new public names (main worktree sources and sister projects, read-only)
$ grep -rn --include="*.lean" "stIniTermII_holds\|iniTermII\|inst_iniTermII_proved" RBM3D ../RBM1D ../RBM2D | grep -v "RBM3D/Induction/IniTermII.lean"
RBM3D/Induction/Step5Pins.lean:980:theorem inst_iniTermII (h : STIniTermII 3) (Cd : ℝ) (hCd : 0 < Cd) :
$ grep -c "^theorem" ...IniTermII.lean; grep -c "^private theorem\|^private def" ...IniTermII.lean   # public / private (all private helpers carry the prefix iniTermII_)
8
56
$ grep -c "^private theorem iniTermII_\|^private def iniTermII_" ...   # private helpers with the prefix
56
$ §29 (6): sources of the parameter bounds in iniTermII_concl
1668:  obtain ⟨⟨h𝔠, h𝔡, hsz, hBand, hWO⟩, hloc⟩ := hflow
1669:  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz ⟨⟨h𝔠, h𝔡, hsz, hBand, hWO⟩, hloc⟩ ht
1673:    exact (abs_lemE_le him).trans (hloc n).1
1682:    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
$ grep -rn --include="*.lean" "theorem zdistInf_add_le\|theorem zdistInf_neg\|theorem zdistD_neg" RBM3D | grep -v IniTermII.lean | cut -c1-100   # names of (c) found absent / private / present
RBM3D/Green/Pins.lean:501:private theorem zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
RBM3D/Defs/Lattice.lean:103:theorem zdistD_neg (d L : ℕ) [NeZero L] (x : Zd d L) : zdistD d L (-x) =
$ lake env lean names.lean; echo exit=$?   # every Mathlib/RBM name of (c) via #check
exit=0
     142
$ ports: grep -n "RBM2D\|RBM1D" RBM3D/Induction/IniTermII.lean   # no port from RBM1D/RBM2D; no RBM1D/RBM2D diff-stat applies
(no matches: exit 1)
$ git diff main...t/T2163 -- RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STIniTermII, -- initial term `(zYU2)`, case (ii); S5-01 (T2138, DECISIONS §40: owed)
```

### Narrative (all statements below are read off the file `RBM3D/Induction/IniTermII.lean` and the outputs above)

1. Delivered: target 1 `stIniTermII_holds` (the pin `STIniTermII` as merged, both conjuncts); target 2 as two public cores `iniTermII_core`
   (`σ₁ ≠ σ₂`, `Q^{(1)} = zeroModeSet {0}`) and `iniTermII_core_same` (`σ₁ = σ₂`); target 3 `iniTermII_concl` (the `Prec` lift). Axioms: the three standard
   ones. The registry line of `STIniTermII` (`Test/Axioms.lean:174`) is deleted; the registry pre-check and the full build (root import added temporarily) exit 0.
2. Route of the core, every step Lean-checked: `step5Kernel_UN_decompU` gives `𝒰 = K ⊗ K`, `K = (s/u) I + ((u-s)/u) Θ_u` (`iniTermII_Ugen_rep`; `u = 0` forces `s = 0` and
   `𝒰 = id`, `GridDuhamelN_Ugen_self`); the column sums of `K` are `ρ = (1-s)/(1-u)`, so `Q^{(1)}(K ⊗ K) = (K - ρ L^{-d} J) ⊗ K` (`iniTermII_zms_rep`) and
   `K - ρ L^{-d} J = α (I - L^{-d} J) + β Θ̊_u`, `α = s/u`, `β = (u-s)/u ≤ 1-s` (the displayed `(1-s)² Θ̊ X Θ` of `(zYU2)` is the `β²` term of four).
3. The four `≲` of `3_5:2275-2281` in Lean: (1→2) the `b₂`-sum is `iniTermII_ZA`, i.e. `(uwp2-92kj)` = `step5Kernel_profile_explicit_holds` at `(u,t) ↦ (s,u)` with the
   floor sent to `0` (`iniTermII_stageA`), plus the identity term and the row sum `(1-u)⁻¹` of `Θ_u` for the floor; (2→3) the `b₁`-sum with `|Θ̊_{ab}| ≤ C (g²)⁻¹ (|a-b|+1)^{-(d-2)}`
   (`prop8ZeroMode_holds`) and the convolution `Σ_b P(a₁-b) P(b-a₂) ≤ C L² P(a₁-a₂)` (`sum_conv_le`; `iniTermII_S3`); (3→4) `β L² ≤ g²` (`1-s ≤ ilambda²/L²`),
   `(g²)⁻¹ P ≤ 2e 𝒯_u`, `(L^d(1-u))⁻¹ ≤ e 𝒯_u` for `ℓ_u = L` (`iniTermII_T_lower`). `B_{s,0} ≍ ilambda⁻²` is used only as `Bctl ≤ 2 A⁻¹` (`iniTermII_Bctl_le`).
   None of the four `≲` fails as written; the corrections are the kernel form (T2163a), the kernel time and the floor (T2163b).
4. `σ₁ = σ₂`: `prop5Short_holds`, row sums bounded by exponential decay; the loss `B_{s,|b₁-b₂|} ≤ (m+1)^{d-2} B_{u,|a₁-a₂|}` is absorbed (`iniTermII_Ts_le`, `iniTermII_sum_poly_exp`).
   The regime `1-s ≤ g²/L²` is used in this proof only through `ℓ_u = L`; (a) row 11 says it is not needed mathematically; not pursued (the pin has it).
5. `Prec` lift: premise `STDecay` at `D' = D + 1/𝔠`; the bad set of the conclusion (index `(u,σ,a)`) lies in the bad set of the premise (index `(σ,b)`) at `τ/2`
   (`iniTermII_of_subset`); constants are absorbed by `N^{τ/2}` (`2C ≤ N^{τ/2}` eventually) and `ρ W^{-D'} ≤ W^{-D}` since `ρ ≤ N ≤ W^{1/𝔠}`
   (`iniTermII_rho_le`, `iniTermII_N_le_W`). (a) row 10 proposes `D + 1/𝔠 + 1`; the `+ 1` is not needed.
6. §29 (5): `STDecay` is per time at `s`; `X = (𝓛-𝒦)^{(2)}_{s,σ}` is `u`-free; `u` enters only through `Ugen … s u` and the scale `STprof sz n u D L` at the index time `u` (7);
   the union over `(u,σ,a)` sits inside the premise's union over `(σ,b)`. §29 (6): nothing is added: `iniTermII_concl` takes `hd, hκ, hflow, hs0, ht, hR, hDec` only;
   `0 < lam` (eventually) and `lam ≤ 𝔡⁻¹` from `WO`, `|E| ≤ 2-κ` from `locDomain` and `abs_lemE_le`, `t < 1` from `st5_t_lt_one`, `W` large from `Bandwidth`, `SizeTendsto`.
7. Instances (§12 of the file): the ticket data `L = 3`, `g = 1/2`, `s = 15/16` violates `1-s ≤ g²/L²` (`1/16 > 1/36`), as (a) says; the compiled instances use `L = 4`, `g = 1`
   (`1-s = 1/16 = g²/L²`), `W = 2`, `D = 2`, `E = 1`, `s = 15/16 < u = 31/32`, `M = λ = 1`, the nonzero profile tensor; `check_inst.py` gives `C_needed = 0.16` (mixed), `0.92` (same).

## (c) Verified Mathlib names (all `#check`ed by `names.lean`, exit 0, see (b)); used in `IniTermII.lean`

- `Finset.sum_ite_eq (s) (a) : ∑ j ∈ s, (if a = j then f j else 0) = if a ∈ s then f a else 0`; `Finset.sum_comm`; `Finset.sum_add_distrib`; `Finset.mul_sum`, `Finset.sum_mul`; `Finset.sum_eq_single`
- `Finset.sum_mul_sum : (∑ i ∈ s, f i) * (∑ j ∈ t, g j) = ∑ i ∈ s, ∑ j ∈ t, f i * g j`
- `Finset.toList_singleton (a) : ({a} : Finset α).toList = [a]` (unfolds `zeroModeSet {0}`)
- `piFinTwoEquiv (α : Fin 2 → Type _) : (∀ i, α i) ≃ α 0 × α 1` with `Fintype.sum_equiv`, `Fintype.sum_prod_type` (sum over `Fin 2 → Zd d L` as a double sum)
- `Fin.prod_univ_two`; `Equiv.subRight` (translation of lattice sums); `norm_sum_le`; `le_of_forall_pos_le_add` (floor `w → 0` in `iniTermII_stageA`)
- `Real.rpow_neg_one (x) : x ^ (-1) = x⁻¹`; `Real.sqrt_eq_rpow (x) : √x = x ^ (1/2)`; `Real.one_le_sqrt : 1 ≤ √x ↔ 1 ≤ x`; `Real.exp_le_one_iff : exp x ≤ 1 ↔ x ≤ 0`
- `Real.mul_rpow`, `Real.inv_rpow`, `Real.rpow_neg`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`
- `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`, `Complex.norm_real` (`m * conj m = ‖m‖² = 1`)
- `inv_anti₀`, `div_le_div_iff₀`, `div_le_iff₀`, `le_div_iff₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `le_mul_of_one_le_right`, `Nat.eq_zero_of_le_zero`
- Changed signature: `add_le_add_right h c` gives `c + a ≤ c + b` here (elaboration error in this ticket); use `add_le_add h le_rfl`.
- Names verified absent / private / present (grep in (b)): no declaration named exactly `zdistInf_add_le` (private copies `pti_zdistInf_add_le`, `Evolution/PropTInf.lean:43`, and others with prefixes); `zdistInf_neg` only private (`Green/Pins.lean:501`); `zdistD_neg` public (`Defs/Lattice.lean:103`).
- Merged project names used (all `#check`ed): `sum_radial_pow_le`, `sum_conv_le`, `sum_radial_exp_decay_le`, `pow_mul_exp_neg_le`, `exp_tail_ge`, `ellT_mono`, `Theta0_apply_eq`, `sum_norm_Theta_row_le`, `Theta_apply_add_right_of_three_le`, `Theta_transpose_of_three_le`, `sum_Theta_row_of_three_le`, `Ind.GridDuhamelN_Ugen_self`, `step5Kernel_UN_decompU`, `step5Kernel_profile_explicit_holds`, `prop8ZeroMode_holds`, `prop5Short_holds`, `st5_eventually_A_ge_one`, `st5_t_lt_one`, `st5_zeroModeSet_empty`, `st_Bctl_pos`, `UnifDetDom.rpow_half_mul_rpow_half`, `eventually_le_rpow`, `abs_lemE_le`, `mE_im`.

## (d) Open issues and paper-delta candidates — Sun Oct  4 22:36:47 UTC 2026

- Hub, at merge: add `import RBM3D.Induction.IniTermII` after the last `import` line of `RBM3D.lean` (checked in (b): full `lake build` exit 0 with that import, reverted afterwards; the commit touches only `IniTermII.lean` and one deleted line of `Test/Axioms.lean`).
- `T2163a`: the second term of `(zYU2)`, `(1-s)² (Θ̊_t (𝓛-𝒦)_s Θ_t)_a`, is the `β²` term of the exact expansion `Q^{(1)} 𝒰^{(2)}_{s,u} X = [(s/u)(I - L^{-d}J) + ((u-s)/u) Θ̊_u] ⊗ [(s/u) I + ((u-s)/u) Θ_u] X`; the other three terms are bounded in Lean (`iniTermII_bil`); `(u-s)/u ≤ 1-s` exactly (no factor 2).
- `T2163b`: in `3_5:2275-2281` the propagator time is the running time `u ∈ [s,t]` of the index (the paper writes `t`); the output floor is `((1-s)/(1-u)) W^{-D'}`, not `W^{-D}`; it is `≤ W^{-D}` for the `STDecay` input at `D' = D + 1/𝔠` (`ρ ≤ N ≤ W^{1/𝔠}`, `Bandwidth`), which the pin allows (`STDecay` is `∀ D`).
- `T2163c`: the ticket's compiled-instance data `d = 3, L = 3, g = 1/2, s = 15/16, u = 31/32` is outside regime (ii) (`1-s = 1/16 > g²/L² = 1/36`); instances use `L = 4, g = 1` (`1/16 = g²/L²`).
- `T2163d`: the constants of the cores depend on `(d, Λ, κ_m)` with `Λ = 𝔡⁻¹`, `κ_m = √(κ(4-κ))/2` for `|E| ≤ 2-κ` (from `prop8ZeroMode_holds`, `prop5Short_holds`): the paper's `C(d)` (same kind as D362).
- Observations (no statement affected): section (a) contains no mistake that changes a verdict, so no `(a′)`; the private `iniTermII_zdistD_neg` duplicates the public `zdistD_neg`; the same-sign core uses the regime only through `ℓ_u = L` (a regime-free proof is not attempted).
