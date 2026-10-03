Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 04:44:48 UTC 2026

Notation: `k = d-2 ≥ 1`, `|x| = zdistD d L x` (ℓ¹ torus distance, `≤ d·L`, `Defs/RadialSum.lean:44`), `ℓ_t = min(max(g/√|1-t|,1),L)`,
`B_{t,K} = (g²+|1-t|)⁻¹(K+1)^{-k} + (L^d|1-t|)⁻¹` (`Defs/Params.lean:32,36`), `‖·‖` = Mathlib `Matrix.Norms.Operator` = L^∞→L^∞ norm
(`Mathlib/Analysis/Matrix/Normed.lean:33`), `S = SB` (row sums of `|·|` = 1, `norm_SB`, support `|a-c| ≤ 1`, `Block.lean:136,SB_apply_eq_zero_of_one_lt`).
Hypothesis of all three: `Prop5Decay d Λ` (EKXiDecay, EKXiBall) / none (EKSameRow, uses proved `prop5Short_holds`). `Prop5Decay` is an
external hypothesis (PT-F1 in flight): `∃ Cd cd >0`, uniform in `L ≥ 3`, `g ∈ (0,Λ]`, `t ∈ [0,1)`, `‖m‖=1`, all `σ₁,σ₂`:
`‖Θ_{t·m(σ₁)m(σ₂)}(0,a)‖ ≤ Cd B_{t,|a|} e^{-cd|a|/ℓ_t}` (`Propagator/Pins.lean:35`).

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| spectral parameter of `Ξ` | `ξ = tμ`, `‖μ‖=1` | `‖tμ‖ = t < 1` (`norm_t_mul_lt_one`) | `1-t > 0`, enters only via `g²/L² ≤ 1-t` |
| reduction of unit `μ` to the pin | `m = e^{i arg μ/2}`, `σ₁=σ₂=true`: `PropSpin m true * PropSpin m true = m·m = μ` (def of `PropSpin`, `Pins.lean:31`) | `Prop5Decay` quantifies all unit `m`, all `σ₁,σ₂`, no bulk condition | none needed. Ticket's alternative (`σ₁≠σ₂`, `m=1`, `norm_Theta_apply_le`: `‖Θ_{tμ}(a,b)‖ ≤ Re Θ_t(a,b)`) also closes; both numerically checked below (assert `|Θ_{tμ}|≤Θ_t`) |
| translation | `Θ(c,b) = Θ(0,b-c)` (`Theta_apply_add_right_of_three_le`, needs `L≥3`) | `‖ξ‖<1` | exact |
| entry bound | `‖Ξ(a,b)‖ ≤ (t-s)Σ_c ‖S(a,c)‖‖Θ_{tμ}(c,b)‖`, `‖(t-s)μ‖ = t-s ≤ 1-s` | `s ≤ t` | factor `(1-s)/(t-s) ≥ 1` dropped; `Σ_c ‖S(a,c)‖ = 1` exact |
| shift of `|a-b|` by one step | for `|a-c| ≤ 1`, `r=|b-c|`, `R=|a-b|`: `R ≤ 1+r` | triangle (`zdistD_add_le`) | exact |
| power shift | `(r+1)^{-k} ≤ 2^k (R+1)^{-k}` | `R+1 ≤ r+2 ≤ 2(r+1)` | constant `2^{d-2}`; `=2` at `d=3` |
| exponential shift | `e^{-cd r/ℓ} ≤ e^{cd} e^{-cd R/ℓ}` | `(R-r)/ℓ_t ≤ 1/ℓ_t ≤ 1` since `ℓ_t ≥ 1` (`one_le_ellT`, `L≥1`) | constant `e^{cd}`; `ℓ_t ≥ 1` has slack `ℓ_t-1` |
| zero-mode absorption | `(L^d|1-t|)⁻¹ ≤ 2(2m)^k (g²+|1-t|)⁻¹(n+1)^{-k}` for `n ≤ mL`, `m=d` (`zeroMode_le_of_ge_mul`, `PropT.lean:89`; `zdistD_le`: `|x| ≤ dL`) | `g²/L² ≤ 1-t`, `t<1` | merged lemma gives `2(2d)^{d-2}` (=12 at `d=3`), NOT the ticket's `2d^{d-2}`; `2d^{d-2}` (=6) is also true here (`|x| ≤ dL/2`, `n+1 ≤ dL`) but needs a new proof; the true max ratio at `d=3` is 1.456–1.482 (output (2)). Use the merged form |
| decay constant of `Ξ` (EKXiDecay) | `C_Ξ = Cd(1+2(2d)^{d-2})2^{d-2}e^{cd}` (`d=3`, `cd=.25`: factor `33.4·Cd`), `c_Ξ = cd` | `Cd, cd` from `Prop5Decay d Λ`, uniform in `g ≤ Λ` | depends on `(d,Λ)` only; empirical `max ratio ≤ 1.91` vs `33.4·0.774 = 25.9` (output (1)): slack `≈13.5×` |
| `(1-s)ℓ_s² ≤ g²+|1-s|` | constant 1 (`one_sub_mul_ellT_sq_le`, `Params.lean:80`) | `s<1`, `g ≥ 0` | equality when `g/√(1-s) ∈ [1,L]`: `(1-s)ℓ²=g²` ≤ `g²+|1-s|` with slack `|1-s|` |
| ball sum of the polynomial factor | `Σ_{b∈D}(|a-b|+1)^{-k} ≤ Σ_{b∈D}(min(|a-b|,R)+1)^{-k} ≤ ballC(k)R²`, `ballC(k) = 2e·2^{k+2}·radC 1`, `radC 1 = 32·721 = 23072` (`RadialSum.lean:356,97`, `sum_ball_min_pow_le`, hyp. `|ctr-b| ≤ R`, `R ≥ 1`) | `R ≤ Λ'ℓ_s`, `Λ' ≥ 1` | `ballC(1) = 1.003e6`; centre `ctr ≠ a` allowed by the `min` truncation. `R² ≤ Λ'²ℓ_s²` exact |
| ball constant (EKXiBall) | `C_ball = 4 C_Ξ ballC(d-2)` (`d=3`: `1.04e8` at `Cd=.774`); target `≤ C_ball Λ'² (g²+|1-s|)/(g²+|1-t|)` | `(1-s)ℓ_s² ≤ g²+|1-s|` and `(g²+|1-t|)⁻¹` factor kept | the factor 4 is slack (the chain gives `C_Ξ ballC`); empirical `Cball ≤ 1.91` vs `1.04e8` |
| `Prop5Short` constants (EKSameRow) | `Cκ, cκ >0` depend on `(d,Λ,κ)` (existential from `prop5Short_holds`; docstring values `Cκ=883.2, cκ=0.03279` at `d=3,Λ=1,κ=.5` are a lead only, not used by the target) | `Σ_b|Θ(0,b)| ≤ Cκ(1+g²Σ_b e^{-cκ|b|})`, `Σ_b e^{-cκ|b|} ≤ expC(k,cκ)` uniformly in `L` (`sum_radial_exp_decay_le`, `expC k c = 2^{k+2}·2·2^{k+3}(1+(k+3)!/c^{k+3})`) | `C_same = 1 + Cκ(1+Λ² expC(d-2,cκ))` using `g² ≤ Λ²`; exact `‖uKer‖ ≤ 3.50` over the scan vs `4.7e12` |
| same-sign row | `uKer = 1 + Ξ` (`uKer_eq_one_add`), `‖Ξ‖ ≤ (t-s)‖S‖‖Θ‖ ≤ ‖Θ‖`; ticket's `‖1-sμS‖ ≤ 2` route gives `2‖Θ‖`, also valid | `s ≤ t`, `‖μ‖=1`, `μ = m²` (σ=true) or `m̄²` (σ=false), both covered by `Prop5Short` (`κ ≤ Im m`) | the merged `hmi : 0<m.im` is not needed; `κ ≤ m.im` implies it |
| side conditions | `d = k+2`, `3 ≤ d` ⇒ `k ≥ 1`; `L ≥ 3 ⇒ L ≥ 1`; `NeZero L` | | `d-2` natural subtraction equals `k` exactly |

### (ii) Concrete nondegenerate instance
Data: `d=3, Λ=1, κ=1/2, L=5, g=1/2, s=1/2, t=9/10, μ=1, Λ'=1, R=1, m=i (σ=true, μ=m²=-1)`; exact `Θ = (1-tμS)⁻¹` by FFT
(`S = (1+2g²Σcos k_i)/(1+2dg²)`, `Defs/Block.lean:30-44`). Scripts (python, no Lean) in the session scratchpad:
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad && python3 inst.py`
```
hyp checks: 3<=d True  3<=L True  0<g<=Lambda=1 True  0<=s<=t<1 True  g^2/L^2=0.0100 <= 1-t=0.1000
ell_t=1.5811 ell_s=1.0000 ; R=1 in [1, Lambda'*ell_s]=[1,1.0000] ; 1-s=0.50 g^2+|1-t|=0.35
Cd_emp(cd=.25)=0.6324
|x|=0 Xi(0,x)=0.38112 Theta(0,x)=1.85753
|x|=1 Xi(0,x)=0.15540 Theta(0,x)=0.34966
|x|=2 Xi(0,x)=0.04127 Theta(0,x)=0.09287
|x|=3 Xi(0,x)=0.02421 Theta(0,x)=0.05446
ball size 7
max ball sum=1.31355 ; (g^2+|1-s|)/(g^2+|1-t|)=2.14286
same-row: m=i, mu=-1: ||uKer||=1.09322
```
Reading: all hypotheses hold at once (`7`-point ball, `ℓ_s = 1`, `R=1` in `[1,Λ'ℓ_s]`, `g²/L² = 0.01 ≤ 0.1`); `Cd_emp = 0.632` is the
exact constant `Prop5Decay` must dominate at `cd=.25` here; `Σ_ball|Ξ| = 1.314 ≤ C_ball·2.143`; `‖uKer‖ = 1.093 ≤ C_same`.
Grid scan required by the ticket (`d=3`, `L∈{5,9}`, `g∈{.1,.5}`, `s=.5`, `t∈{.9, 1-g²/L²}`, `μ∈{1,i,e^{.3i}}`; the full script asserts the Ξ
bound with the table constant, `|Θ_{tμ}| ≤ Θ_t`, the absorption constants, `Prop5Short` pointwise; rows for `μ=i,e^{.3i}` filtered from the print only):
`python3 pf2026.py | grep -v "mu=i \|mu=e"`
```
== (1) decay ratio Cd_emp, Xi ratio, ball ratio; cd=0.25
L=5 g=0.1 t=0.9      mu=1      ell_t=1.000 Cd_emp=0.737 Xi:max ratio=0.563 (<= Cd*33.4=24.6) ball:Cball_emp=0.777
L=5 g=0.1 t=1-g2/L2  mu=1      ell_t=5.000 Cd_emp=0.746 Xi:max ratio=1.833 (<= Cd*33.4=24.9) ball:Cball_emp=1.909
L=5 g=0.5 t=0.9      mu=1      ell_t=1.581 Cd_emp=0.632 Xi:max ratio=0.267 (<= Cd*33.4=21.1) ball:Cball_emp=0.613
L=5 g=0.5 t=1-g2/L2  mu=1      ell_t=5.000 Cd_emp=0.680 Xi:max ratio=1.652 (<= Cd*33.4=22.7) ball:Cball_emp=1.557
L=9 g=0.1 t=0.9      mu=1      ell_t=1.000 Cd_emp=0.742 Xi:max ratio=0.563 (<= Cd*33.4=24.8) ball:Cball_emp=0.777
L=9 g=0.1 t=1-g2/L2  mu=1      ell_t=9.000 Cd_emp=0.774 Xi:max ratio=1.906 (<= Cd*33.4=25.8) ball:Cball_emp=1.381
L=9 g=0.5 t=0.9      mu=1      ell_t=1.581 Cd_emp=0.644 Xi:max ratio=0.264 (<= Cd*33.4=21.5) ball:Cball_emp=0.599
L=9 g=0.5 t=1-g2/L2  mu=1      ell_t=9.000 Cd_emp=0.707 Xi:max ratio=1.735 (<= Cd*33.4=23.6) ball:Cball_emp=1.334
{'Cd': np.float64(0.7743027666162341), 'CXi': np.float64(1.9063125590845684), 'Cball': np.float64(1.908652506948339)}
ballC(1)=1.003e+06 ; 4*C_Xi(formula, Cd=worst)*ballC=1.038e+08
== (2) zero-mode absorption: max_n (L^d w)^-1 / ((g^2+w)^-1 (n+1)^-k), w=1-t>=g^2/L^2, n<=d*floor(L/2)
L=5 g=0.1: max ratio=1.4560  <= 2 d^k=6  <= 2(2d)^k=12
L=5 g=0.5: max ratio=1.4560  <= 2 d^k=6  <= 2(2d)^k=12
L=5 g=1.0: max ratio=1.4560  <= 2 d^k=6  <= 2(2d)^k=12
L=9 g=0.1: max ratio=1.4623  <= 2 d^k=6  <= 2(2d)^k=12
L=9 g=0.5: max ratio=1.4623  <= 2 d^k=6  <= 2(2d)^k=12
L=9 g=1.0: max ratio=1.4623  <= 2 d^k=6  <= 2(2d)^k=12
L=25 g=0.1: max ratio=1.4824  <= 2 d^k=6  <= 2(2d)^k=12
L=25 g=0.5: max ratio=1.4824  <= 2 d^k=6  <= 2(2d)^k=12
L=25 g=1.0: max ratio=1.4824  <= 2 d^k=6  <= 2(2d)^k=12
== (3) cd stability of Prop5Decay (external hyp.): max ratio |Theta|/(B e^{-cd|a|/ell}), cd=.25, wide scan
sup ratio over scan = 1.9997 (Prop5Decay constant must dominate; finite & stable in L,t->1)
== (4) same-sign row: ||uKer||_inf vs C=1+Ck(1+g^2 expC); d=3,Lambda=1,kappa=.5
Prop5Short consts: C_kappa=883.2000 c_kappa=0.03279 ; expC=5.315e+09 ; C_same(Lambda=1)=4.694e+12
max over scan of ||uKer||_{inf->inf} = 3.4991 <= C_same=4.694e+12 ; pin5s pointwise holds in scan
```
External hypothesis `Prop5Decay` (TEAM §8 lesson 14), concrete limit computation: line `== (3)` above scans `L∈{5,9,15,25}`, `g∈{.05,.1,.5,1}`,
`t∈{0,.5,.9,1-g²/L²,1-10⁻³,1-10⁻⁶}`, `μ∈{1,i,e^{.3i},-1}`: the ratio `|Θ_{tμ}(0,a)|/(B_{t,|a|}e^{-.25|a|/ℓ_t})` stays `≤ 2.0` as `t→1`
(zero mode `Θ_t(0,a) ⊇ (L^d(1-t))⁻¹` is exactly the second term of `B`) and as `L` grows, so the hypothesis is satisfiable with `cd=.25`, `Cd=2`,
and is not vacuous. `Prop5Decay` stays a hypothesis in the Lean examples (allowed, CLAUDE.md §4 step 2).

### Verdicts
- `EKXiDecay` (`ekXiDecay_holds`): PASS. Constants close, uniform in `g ≤ Λ`; probe lemma `ek_norm_XiKer_apply_le` gives it from `hbd`, discharged by `Prop5Decay` at `m = e^{i arg μ/2}`, `σ₁=σ₂=true` (or property 4); zero-mode constant is `2(2d)^{d-2}` (not `2d^{d-2}`), harmless.
- `EKXiBall` (`ekXiBall_holds`): PASS. Same hypothesis; `ek_sum_ball_norm_XiKer_le` applied to `EKXiDecay`'s output; `C_ball = 4C_Ξ ballC(d-2)`, depends on `(d,Λ)` only.
- `EKSameRow` (`ekSameRow_holds`): PASS. Port of `exists_norm_uKer_same_le` (`Kernel/Evolution.lean:445-510`) with `prop5Short_holds d Λ κ`; `C_same = 1+Cκ(1+Λ² expC(d-2,cκ))`, both `σ`.

## (b) Script output — Sat Oct  3 04:50:58 UTC 2026
```
$ date -u
Sat Oct  3 04:50:14 UTC 2026
$ git log --oneline -1 t/T2026; git diff --name-only main...t/T2026
0ff7fcc T2026: EK-2 bounds of the one-index kernel Xi and the same-sign row on the PT pins
RBM3D/Evolution/XiPins.lean
$ lake build RBM3D.Evolution.XiPins   (tail)
Build completed successfully (2545 jobs).
$ lake build   (whole library as of main; XiPins is not yet in the root imports)
Build completed successfully (3725 jobs).
$ lake env lean RootWithXi.lean   (copy of RBM3D.lean with `import RBM3D.Evolution.XiPins` added, #assert_rbm_axioms last; exit code, first line)
exit 0
axiom audit: 1037 theorems, 398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
error lines: 0
$ lake env lean ax.lean   (#print axioms of the three targets and the two copied lemmas; #check of targets)
'RBM.ekXiDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekXiBall_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekSameRow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_norm_XiKer_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_sum_ball_norm_XiKer_le' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.ekXiDecay_holds : ∀ (d : ℕ) (Λ : ℝ), RBM.EKXiDecay d Λ
RBM.ekXiBall_holds : ∀ (d : ℕ) (Λ : ℝ), RBM.EKXiBall d Λ
RBM.ekSameRow_holds : ∀ (d : ℕ) (Λ κ : ℝ), RBM.EKSameRow d Λ κ
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Evolution/XiPins.lean
exit 1 (1 = no match)
```
```
$ grep -rn <8 public + 4 private new names> RBM3D RBM3D.lean --include=*.lean | grep -v XiPins.lean   (this worktree = main + 1 file)
exit 1 (1 = no match outside XiPins.lean)
$ same grep in ../RBM1D ../RBM2D (read-only, count of matching lines)
RBM1D:        0
RBM2D:        0
$ git --no-optional-locks show c961e62:RBM3D/Probe/T2016Pins.lean | sed -n 210,447p   vs XiPins lemma block (diff, exit)
diff exit 0  (     238 lines each)
$ diff of the three pinned defs: docs/tickets/checks/T2026-check.lean (from "/-- (eq:decayXi), uniform" to before "end RBM.T2026Check") vs XiPins.lean (same start to before "### The proofs")
diff exit 0  (      33 lines each)
$ git --no-optional-locks log -1 --format=%h -- RBM3D/Kernel/Evolution.lean  (source of the port of exists_norm_uKer_same_le, :445-510)
ff8d36d
$ RBM1D/RBM2D text copied: none (diff --stat not applicable)
```
Target statements (script: `sed -n 280,312p` and `grep -n "^theorem ek.*_holds" XiPins.lean`):
```
/-- `(eq:decayXi)`, uniform in `g ∈ (0, Λ]` and in the unit `μ`, from pin 5 (`Prop5Decay`). -/
def EKXiDecay (d : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 0 < Λ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ μ : ℂ, ‖μ‖ = 1 →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
          haveI : NeZero L := ⟨by omega⟩
          ∀ a b : Zd d L,
            ‖XiKer d L g μ s t a b‖
              ≤ C * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L (a - b) : ℝ) + 1) ^ (d - 2))⁻¹
                * Real.exp (-(c * (zdistD d L (a - b) : ℝ)) / ellT L g t)

/-- Ball sums of `Ξ` over any set within distance `R ≤ Λ' ℓ_s` of a centre (pin 5 again). -/
def EKXiBall (d : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ μ : ℂ, ‖μ‖ = 1 →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
          ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
          haveI : NeZero L := ⟨by omega⟩
          ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
            ∑ b ∈ D, ‖XiKer d L g μ s t a b‖ ≤ C * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))

/-- `(eq:samecolor)`: at a same-sign index the one-index factor `(1 − sμS)Θ_{tμ}`, `μ = m(σ)²`, is bounded in
the `∞ → ∞` norm, uniformly in `L, g ≤ Λ, s, t`; bulk `κ ≤ Im m`. -/
def EKSameRow (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im →
        ∀ σ : Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
          haveI : NeZero L := ⟨by omega⟩
          ‖uKer d L g (PropSpin m σ * PropSpin m σ) s t‖ ≤ C

328:theorem ekXiDecay_holds (d : ℕ) (Λ : ℝ) : EKXiDecay d Λ := by
346:theorem ekXiBall_holds (d : ℕ) (Λ : ℝ) : EKXiBall d Λ := by
357:theorem ekSameRow_holds (d : ℕ) (Λ κ : ℝ) : EKSameRow d Λ κ := by
```
Compiled nonempty instances (`sed -n 428,483p XiPins.lean`; all three are inside the module built above):
```lean
/-! ### Compiled instances at `d = 3`, `Λ = 1`, `κ = 1/2`, `L = 5`, `g = 1/2`, `s = 1/2`, `t = 9/10`, `μ = 1`

`g² / L² = 1/100 ≤ 1 - t = 1/10`.  `Prop5Decay 3 1` (external, PT-F1 in flight) is the only
hypothesis of the first two instances; every deterministic hypothesis is discharged. -/

section Instances

/-- the lattice ball of radius `1` around `0` in `Z_5^3` (7 points) -/
private def xpBall : Finset (Zd 3 5) := Finset.univ.filter fun b => zdistD 3 5 (0 - b) ≤ 1

private theorem xp_zero_mem : (0 : Zd 3 5) ∈ xpBall := by
  simp [xpBall, zdistD, zdist]

private theorem xp_ball_dist : ∀ b ∈ xpBall, (zdistD 3 5 (0 - b) : ℝ) ≤ 1 := fun b hb => by
  exact_mod_cast (Finset.mem_filter.1 hb).2

/-- instance of `ekXiDecay_holds` at `L = 5`, `g = 1/2`, `s = 1/2`, `t = 9/10`, `μ = 1`. -/
example (h5 : Prop5Decay 3 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      haveI : NeZero 5 := ⟨by norm_num⟩
      ∀ a b : Zd 3 5,
        ‖XiKer 3 5 (1 / 2 : ℝ) 1 (1 / 2) (9 / 10) a b‖
          ≤ C * (1 - 1 / 2) * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
              * (((zdistD 3 5 (a - b) : ℝ) + 1) ^ (3 - 2))⁻¹
              * Real.exp (-(c * (zdistD 3 5 (a - b) : ℝ)) / ellT 5 (1 / 2 : ℝ) (9 / 10)) := by
  obtain ⟨C, c, hC, hc, H⟩ := ekXiDecay_holds 3 1 h5 le_rfl one_pos
  refine ⟨C, c, hC, hc, fun a b => ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1 (by simp) (1 / 2) (9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) a b

/-- instance of `ekXiBall_holds` at the 7-point ball `D` around `ctr = 0`, `a = 0`, `Λ' = 1`,
`R = 1 ≤ ℓ_s`. -/
example (h5 : Prop5Decay 3 1) :
    ∃ C : ℝ, 0 < C ∧ (0 : Zd 3 5) ∈ xpBall ∧
      haveI : NeZero 5 := ⟨by norm_num⟩
      ∑ b ∈ xpBall, ‖XiKer 3 5 (1 / 2 : ℝ) 1 (1 / 2) (9 / 10) 0 b‖
        ≤ C * 1 ^ 2 * (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) := by
  obtain ⟨C, hC, H⟩ := ekXiBall_holds 3 1 h5 le_rfl one_pos
  refine ⟨C, hC, xp_zero_mem, ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1 (by simp) (1 / 2) (9 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 le_rfl 1 le_rfl
    (by rw [one_mul]; exact one_le_ellT (by norm_num)) 0 0 xpBall xp_ball_dist

/-- instance of `ekSameRow_holds` at `m = i` (`Im m = 1 ≥ 1/2`), both signs. -/
example :
    ∃ C : ℝ, 0 < C ∧
      haveI : NeZero 5 := ⟨by norm_num⟩
      ∀ σ : Bool,
        ‖uKer 3 5 (1 / 2 : ℝ) (PropSpin Complex.I σ * PropSpin Complex.I σ) (1 / 2) (9 / 10)‖
          ≤ C := by
  obtain ⟨C, hC, H⟩ := ekSameRow_holds 3 1 (1 / 2) le_rfl one_pos (by norm_num)
  refine ⟨C, hC, fun σ => ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by rw [Complex.I_im]; norm_num) σ (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)

end Instances
```

### Narrative (≤ 40 lines)
- File `RBM3D/Evolution/XiPins.lean` (485 lines, branch `t/T2026`, commit `0ff7fcc`, the only file in `git diff --name-only main...t/T2026`).
  Imports: `RBM3D.Evolution.Pins`, `RBM3D.Kernel.SumDecay`, `RBM3D.Kernel.Evolution`, `RBM3D.Propagator.Prop5Short`.
- The probe lemmas `ek_norm_XiKer_apply_le`, `ek_sum_ball_norm_XiKer_le` are copied from `c961e62:RBM3D/Probe/T2016Pins.lean` lines 210-447
  (the ticket says 211-372; the second lemma ends at 447, line 210 is the docstring); the diff above is empty. They are the only probe text used
  (`ek_ellT_sq_ge` and the following counting steps are not needed). The three `def`s equal the check file's text (diff exit 0).
- `ekXiDecay_holds`: `d = k + 2`; `Prop5Decay` gives `Cd, cd`; `hbd` of the probe lemma at the given `μ` comes from `Prop5Decay` at `m` with `m * m = μ`,
  `σ₁ = σ₂ = true` (`PropSpin m true = m`), `m = exp(log μ / 2)` (`xp_exists_sqrt`; `IsAlgClosed.exists_eq_mul_self` is unknown in this import closure).
  The property-4 route of the ticket is not used. Constants: `C = Cd (1 + 2 (2 (k+2))^k) 2^k e^{cd}`, `c = cd`: independent of `g ≤ Λ`, `L`, `μ`, `s`, `t`.
- `ekXiBall_holds`: `C = 4 C₀ ballC k` with `C₀` from `ekXiDecay_holds`; `ek_sum_ball_norm_XiKer_le` applied at each `g, μ`; depends on `(d, Λ)` only.
- `ekSameRow_holds`: port of `exists_norm_uKer_same_le` (`RBM3D/Kernel/Evolution.lean:445-510`, last commit touching that file `ff8d36d`) with
  `prop5Short_holds (k+2) Λ κ` instead of `ThetaDecayShort`; `μ := PropSpin m σ * PropSpin m σ` (both `σ`; `‖μ‖ = 1` by `ek_norm_spin`);
  the constant is `1 + Cκ (1 + Λ² expC k cκ)` (`g² ≤ Λ²` replaces `g²`), depends on `(d, Λ, κ)` only; the hypothesis `0 < m.im` of the merged lemma
  is not needed (`κ ≤ m.im` is only passed to `Prop5Short`).
- The zero-mode constant inside `ek_norm_XiKer_apply_le` is `2 (2d)^{d-2}` (merged `zeroMode_le_of_ge_mul`), as stated in section (a); it is not pinned.
- No theorem takes an unproved `Prop` as a hypothesis; `Prop5Decay` is the antecedent inside `EKXiDecay`/`EKXiBall` (DECISIONS §16), and `h5 : Prop5Decay 3 1`
  is a hypothesis of the first two examples (PT-F1 not merged); the third example has none.
- `lake build` of the library does not contain `XiPins` yet (root import is the hub's); the axiom audit of the whole library with the module added to a scratch copy
  of `RBM3D.lean` has exit 0 and no error line (output above).
- No RBM1D/RBM2D text copied; no pin changed; no obstruction.

## (c) Verified Mathlib names (`#check` in `lake env lean`, new uses only; the rest come from the copied probe text)
- `Complex.exp_log : x ≠ 0 → cexp (log x) = x`; `Complex.exp_add : cexp (x + y) = cexp x * cexp y`; `add_halves : a / 2 + a / 2 = a`
- `Complex.norm_I : ‖I‖ = 1`; `Complex.I_im : I.im = 1`; `pow_le_pow_left₀ : 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`
- `norm_smul_le`, `norm_mul_le`, `Finset.sum_nonneg`, `Real.exp_pos` (as in the merged proof being ported)
- Absent from this import closure: `IsAlgClosed.exists_eq_mul_self` (`Unknown identifier`; the Mathlib file `FieldTheory/IsAlgClosed/Basic.lean:90` declares it, not imported here)

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (T2016f, DECISIONS §18, is cited, not re-proposed).
- `Prop5Decay` (external, PT-F1 in flight) stays the antecedent of `EKXiDecay`, `EKXiBall`; section (a) (3) scans `|Θ|/(B e^{-cd|a|/ℓ_t}) ≤ 2.0` (script output there).
- Hub at merge: add `import RBM3D.Evolution.XiPins` after the last `import` line of `RBM3D.lean`.
- No section (a′): nothing in section (a) was found wrong; the `2(2d)^{d-2}` vs `2 d^{d-2}` remark is already in (a).
