Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 13:11:48 UTC 2026

Notation: `x = a_i − a_1 ∈ Z_L^d`, `|x| = zdistD d L x = Σ_j zdist L (x_j)` (ℓ¹ torus distance), `ℓ_t = ellT L g t = min(max(g/√|1−t|,1),L)`, `S = Σ_{i≥2}|a_i−a_1|`, `m+1` = number of tensor indices. Pin: `STMollifierEx d` (`Step34Pins.lean:518`) = `∃ C c >0` (depending on `d,m,Λ`) such that for every `L≥3`, `0<g≤Λ` a `ϑ` has `STMollifierProps g C c`.

### (i) Exponent table

Construction (new): `y_t = 1 + g(1−t)^{-1/2}`, smoothed scale `ℓ̃_t = (1/y_t + 1/L)^{-1} = yL/(L+y)`; `φ_t(x) = exp(−|x|/ℓ̃_t)`; `Z_t = Σ_x φ_t(x) = z₁^d` with `z₁ = Σ_{y∈Z_L} e^{−zdist(y)/ℓ̃_t}` (the ℓ¹ norm splits over coordinates); `ϑ_{t,a} = Π_{i≥2} φ_t(a_i−a_1) / Z_t^m`.

| item | value / statement | constraint | slack / proof |
|---|---|---|---|
| `ℓ̃_t` vs `ℓ_t` | `ℓ_t/2 ≤ ℓ̃_t ≤ 2ℓ_t` | needed to turn `ℓ̃` bounds into `ℓ_t` bounds | `max(x,1) ≤ 1+x ≤ 2max(x,1)`, `min(y,L)/2 ≤ (1/y+1/L)^{-1} ≤ min(y,L)`, `min(2a,L) ≤ 2min(a,L)`; numeric range of `ℓ̃/ℓ` below: [0.526,1.636] |
| `ℓ̃_t` lower bound | `ℓ̃_t ≥ 3/4` | used in `1+ℓ̃ ≤ (7/3)ℓ̃` | `y≥1`, `L≥3` ⇒ `ℓ̃ ≥ (1+1/3)^{-1}` |
| smoothness of `ℓ̃` | `C^∞` on `t<1` (`√(1−t)>0`) | `DifferentiableOn ℝ _ (Ico 0 1)` | `y' = (y−1)/(2(1−t))` |
| `∂_tℓ̃` | `ℓ̃' = ℓ̃² y'/y²`, so `|ℓ̃'| ≤ ℓ̃/(2(1−t))` | `≲ ℓ̃/(1−t)` | constant 1/2 (uses `ℓ̃ ≤ y`, `y'≤ y/(2(1−t))`); numeric max of `(1−t)|ℓ̃'|/ℓ̃` ≤ 0.260 |
| sum one | `Σ_{a: a₀=a₁} ϑ = Π_i Σ_{a_i}φ(a_i−a_1)/Z = 1` (translation invariance of the sum over the torus) | `Z>0` | exact; `m=0` gives the empty product 1 |
| `Z` lower bound | `z₁ ≥ ℓ̃/(2e)`, `Z ≥ (ℓ/(4e))^d` | `ℓ̃ ≤ L` | the points `y=0..k`, `k=⌊min(ℓ̃,L/2)⌋`, have `zdist(y)=y≤ℓ̃`, term `≥ e^{-1}`, count `k+1 ≥ ℓ̃/2` |
| sup bound | `\|ϑ\| ≤ C₁ (ℓ_t^d)^{-m} e^{-cS/ℓ_t}`, `c = 1/2`, `C₁ = (4e)^{dm}` | `c>0` | `φ ≤ e^{-|x|/(2ℓ)}` from `ℓ̃ ≤ 2ℓ`; `Z^{-m} ≤ (4e/ℓ)^{dm}`; numeric max of ratio at `d=3`: 3.6 (m=1), 13.2 (m=2) vs 1285, 1.65e6 |
| `E_φ|x|` | `E|x| = d·E₁ zdist ≤ K ℓ̃`, `K = d·4e(7/3)²≈ 177.6` (d=3) | `ℓ̃ ≥ 3/4` | `Σ_y zdist e^{-zdist/ℓ̃} ≤ 2Σ_k k e^{-k/ℓ̃} ≤ 2(1+ℓ̃)²` (`1−e^{-u} ≥ u/(1+u)`), divided by `z₁ ≥ ℓ̃/(2e)` |
| `∂_tϑ` | `∂_t log ϑ = (ℓ̃'/ℓ̃²)(S − m E_φ\|x\|)`, so `\|∂_tϑ\| ≤ (1/(2(1−t)))(u + mK) ϑ`, `u = S/ℓ̃` | | `(u+mK)e^{-u} ≤ 1+mK` ⇒ `\|∂_tϑ\| ≤ C₂ (1−t)^{-1}(ℓ_t^d)^{-m}`, `C₂ = (1+mK)(4e)^{dm}/2`; numeric max of `(1−t)\|∂ϑ\|ℓ^{dm}`: 0.91 (m=1), 6.6 (m=2) vs 1.1e5, 2.9e8 |
| constants | `C = max(C₁,C₂)`, `c = 1/2` | depend on `(d,m)` only | `Λ` is not needed (all bounds uniform in `g>0`, `L≥3`); `g ≤ Λ` is an unused hypothesis |
| differentiability of `ϑ` | `t ↦ ϑ_{t,a}` differentiable on `t<1` | `Z_t>0` finite sum | `exp(−|x|/ℓ̃)` and finite sums of differentiable maps; `deriv` taken in `ℝ` at `t∈[0,1)` is the two-sided derivative (formula uses `1−t>0` near `t=0`) |

Operator algebra (`P = STPsum`, `Q_t = STQop ϑ t`, `ϑ` any family with `Σϑ_t≡1`):
1. `P(Q_tA)_{a₁} = PA_{a₁} − PA_{a₁}·Σϑ = 0` (needs only `STMollifierProps` clause 1 at that `t`).
2. `Q_tA = A` if `PA=0`.
3. Column sums: `Σ_a thetaKer(μ,t)(a,b) = μ/(1−tμ)`, `Σ_a uKer(μ,s,t)(a,b) = (1−sμ)/(1−tμ)` (constants in `b`), because `SB` is symmetric with row sum 1 (`sum_SB_row`), so `1ᵀSB = 1ᵀ`, `1ᵀ(1−ξSB) = (1−ξ)1ᵀ`, `‖ξ=tμ‖<1`, hence `1ᵀΘ_ξ = (1−ξ)^{-1}1ᵀ`.
4. `PA=0 ⇒ P(ThetaN m t A)=0` (slot 0: `Σ_b K(a₁,b)(PA)_b`; slot `i≥1`: constant column sum times `(PA)_{a₁}`), and `P(UN m s t A)=0` (slot 0 as above, slots `i≥1` the constant column sums of `uKer`). Hypotheses: `3≤L`, `0≤t<1`, `‖m i‖=1` (so `‖tμ_i‖<1`). Note RBM3D's `ThetaN` is the sum over slots of one-index kernels (`Evolution.lean:60`), as in RBM2D `thetaSig`.
5. Commutator (pure linearity): `Q_tΘA − ΘQ_tA = Θ((PA)_{b₀}ϑ_t) − P(ΘA)_{a₀}ϑ_t`; and for a `t`-independent `A`: `∂_t(Q_tA) = −(PA)_{a₀}∂_tϑ_t`, `P(∂_tϑ_t)=0` (derivative of the constant `Σϑ≡1` on `t<1`, using clause 1 for all `t` near the point).
6. Registry: `STMollifierEx` is registered owed at `RBM3D/Test/Axioms.lean:127`; after `stMollifierEx_holds` that line can go (cleanup ticket).

### (ii) Concrete nondegenerate instance (d=3, L∈{5,9}, g∈{0.1,1}, m∈{1,2}, Λ=1)

Scripts (python3/numpy, no Lean): `cd .../scratchpad/T2055 && python3 pf.py` (scale and four properties; `t` grid = {0,.25,.5,.75,1−g²,1−g²/L² and ±1e-3 of the kinks,.99,.999,.99999}; kinks of `ℓ_t` at `t=1−g²` (g<1; at g=1 it is `t=0`) and `t=1−g²/L²`; full enumeration of `x ∈ (Z_L^3)^m`; ∂_t by central differences, relative step `1e-7(1−t)`):
```
L g m | max th/(l^-dm e^{-S/2l}) vs C1 | max (1-t)|dth|l^dm vs C2 | sum(th) | l~/l range | max (1-t)|dl~|/l~ | FD-vs-analytic dl~ | rel err dth
5 0.1 1 | 3.335e+00 <= 1.285e+03 | 6.866e-01 <= 1.148e+05 | 1.000000000000 | [0.545,1.429] | 0.210<=0.5 | 2.9e-06 | 2.3e-05
5 0.1 2 | 1.112e+01 <= 1.652e+06 | 4.579e+00 <= 2.943e+08 | 1.000000000000 | [0.545,1.429] | 0.210<=0.5 | 2.9e-06 | 2.3e-05
5 1.0 1 | 3.335e+00 <= 1.285e+03 | 6.866e-01 <= 1.148e+05 | 1.000000000000 | [0.545,1.429] | 0.208<=0.5 | 3.4e-07 | 2.3e-05
5 1.0 2 | 1.112e+01 <= 1.652e+06 | 4.579e+00 <= 2.943e+08 | 1.000000000000 | [0.545,1.429] | 0.208<=0.5 | 3.4e-07 | 2.3e-05
9 0.1 1 | 3.638e+00 <= 1.285e+03 | 9.119e-01 <= 1.148e+05 | 1.000000000000 | [0.526,1.636] | 0.260<=0.5 | 4.6e-06 | 2.2e-05
9 0.1 2 | 1.324e+01 <= 1.652e+06 | 6.635e+00 <= 2.943e+08 | 1.000000000000 | [0.526,1.636] | 0.260<=0.5 | 4.6e-06 | 2.3e-05
9 1.0 1 | 3.638e+00 <= 1.285e+03 | 9.119e-01 <= 1.148e+05 | 1.000000000000 | [0.526,1.636] | 0.250<=0.5 | 6.1e-07 | 3.7e-05
9 1.0 2 | 1.324e+01 <= 1.652e+06 | 6.635e+00 <= 2.943e+08 | 1.000000000000 | [0.526,1.636] | 0.250<=0.5 | 6.1e-07 | 3.2e-05
```
(`C1 = (4e)^{dm}`, `C2 = (1+mK)(4e)^{dm}/2`, `K = 3·4e·49/9`; the "rel err dth" column is `|analytic − FD|/|FD|` of the formula in (i) over entries with `|∂ϑ|>1e-12`.)

`python3 pf2.py` (`P∘Q_t = 0`, `Pϑ=1`; `L=3`: `ThetaN`, `UN`, commutator, `∂_t`-commutator, with `SB` the circulant of `sbKernel`, `μ_i = m(σ_i)m(σ_{i+1})`, `|μ_i|=1`, `t=0.6`, `s=0.2`; `m=2` at `L=9` omitted: `729³` entries too large; `A` random complex; `t∈{0,0.3,1−g²/L²−1e-3,0.99}`):
```
P Q=0 and P th=1: d=3 L=5 m=1 g=0.1  max|P th-1|=4.4e-16  max|P Q A|/|A|=3.0e-15
P Q=0 and P th=1: d=3 L=5 m=1 g=1  max|P th-1|=4.4e-16  max|P Q A|/|A|=2.3e-15
P Q=0 and P th=1: d=3 L=5 m=2 g=0.1  max|P th-1|=8.9e-16  max|P Q A|/|A|=8.8e-14
P Q=0 and P th=1: d=3 L=5 m=2 g=1  max|P th-1|=4.4e-16  max|P Q A|/|A|=7.4e-14
P Q=0 and P th=1: d=3 L=9 m=1 g=0.1  max|P th-1|=3.3e-16  max|P Q A|/|A|=5.9e-15
P Q=0 and P th=1: d=3 L=9 m=1 g=1  max|P th-1|=3.3e-16  max|P Q A|/|A|=6.2e-15
d=3 L=3 g=0.1 n=2: |P ThetaN A0|=2.9e-14 |P UN A0|=3.7e-14 commutator err=1.4e-14  |dt Q A + (PA)dth|=2.0e-10 |P dth|=1.1e-10
d=3 L=3 g=0.1 n=3: |P ThetaN A0|=1.8e-13 |P UN A0|=2.1e-13 commutator err=9.3e-15  |dt Q A + (PA)dth|=2.6e-10 |P dth|=2.1e-10
d=3 L=3 g=1 n=2: |P ThetaN A0|=1.2e-14 |P UN A0|=1.2e-14 commutator err=1.1e-15  |dt Q A + (PA)dth|=1.7e-10 |P dth|=1.0e-10
d=3 L=3 g=1 n=3: |P ThetaN A0|=8.1e-14 |P UN A0|=9.8e-14 commutator err=2.0e-15  |dt Q A + (PA)dth|=2.6e-10 |P dth|=2.1e-10
```
Instance for the Lean example: `d=3`, `m∈{1,2}`, `Λ=1`, `L=3` (or 5), `g=1`, `t∈[0,1)`; the pin has no external hypothesis (no limit computation needed).

### Verdicts
- Target 1 (`STMollifierEx d`; `3 ≤ d` is a premise only): **PASS**. Constants `c = 1/2`, `C = max((4e)^{dm}, (1+mK)(4e)^{dm}/2)`, `K = d·4e(7/3)²`; every bound is uniform in `0<g`, `L≥3`; all four properties of `STMollifierProps` close with large numeric slack.
- Target 2 (operator algebra: `PQ=0`, `Q=id` on sum-zero, `ThetaN`/`UN` preserve sum-zero, commutators, `Pϑ̇=0`): **PASS**. No missing input; `ThetaN`/`UN` are already defined in `Kernel/Evolution.lean` and `P`, `Q` in `Step34Pins.lean`.

## (b) Script output — Sat Oct  3 13:35:23 UTC 2026
`$SP` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2055` (scratch scripts; their output is pasted below).

### b.1 Build, hygiene
$ lake build RBM3D.Induction.QopAlgebra 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3704 jobs).
$ lake env lean RBM3D/Induction/QopAlgebra.lean; echo "exit $?"
exit 0
$ echo "forbidden-token count: $(grep -c "sorry\|admit\|native_decide\|axiom" RBM3D/Induction/QopAlgebra.lean); lines: $(wc -l < RBM3D/Induction/QopAlgebra.lean)"
forbidden-token count: 0; lines:      978

### b.2 `#print axioms` of every public declaration (`$SP/ax.lean`)
$ lake env lean ax.lean  # 18 `#print axioms` lines + 1 `#check`
declarations printed: 18; distinct axiom sets: ['[propext, Classical.choice, Quot.sound]']
names: stMollifierEx_holds, QopAlgebra_mollifier_props, QopAlgebra_mollifier_sum, QopAlgebra_mollifier_differentiableAt, QopAlgebra_Psum_Qop, QopAlgebra_Qop_of_sumZero, QopAlgebra_Psum_mollifier, QopAlgebra_Psum_deriv, QopAlgebra_Qop_hasDerivAt, QopAlgebra_Qop_hasDerivAt_const, QopAlgebra_col_sum_thetaKer, QopAlgebra_col_sum_uKer, QopAlgebra_ThetaN_sumZero, QopAlgebra_UN_sumZero, QopAlgebra_ThetaN_sub, QopAlgebra_UN_sub, QopAlgebra_commutator_ThetaN, QopAlgebra_commutator_UN
stMollifierEx_holds : ∀ (d : ℕ), STMollifierEx d

### b.3 Target statements, extracted from the file by script
QopAlgebra.lean:573: theorem stMollifierEx_holds (d : ℕ) : STMollifierEx d
QopAlgebra.lean:345: def QopAlgebra_mollifier (d L m : ℕ) [NeZero L] (g : ℝ) (t : ℝ) (a : Fin (m + 1) → Zd d L) : ℂ
QopAlgebra.lean:511: theorem QopAlgebra_mollifier_props (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) : STMollifierProps (d := d) g ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m)) (1 / 2) (QopAlgebra_mollifier d L m g)
QopAlgebra.lean:349: theorem QopAlgebra_mollifier_sum (d L m : ℕ) [NeZero L] (g t : ℝ) (a₁ : Zd d L) : ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), QopAlgebra_mollifier d L m g t a = 1
QopAlgebra.lean:601: theorem QopAlgebra_Psum_Qop (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) {t : ℝ} (hϑ : ∀ a₁, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ t a = 1) (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) : STPsum (d := d) (STQop (d := d) ϑ t A) a₁ = 0
QopAlgebra.lean:617: theorem QopAlgebra_Qop_of_sumZero (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ) {A : (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) : STQop (d := d) ϑ t A = A
QopAlgebra.lean:786: theorem QopAlgebra_ThetaN_sumZero (g : ℝ) (hL : 3 ≤ L) {μs : Fin (m + 1) → ℂ} (hμ : ∀ i, ‖μs i‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A : (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) (a₁ : Zd d L) : STPsum (d := d) (ThetaN d L g μs t A) a₁ = 0
QopAlgebra.lean:821: theorem QopAlgebra_UN_sumZero (g : ℝ) (hL : 3 ≤ L) {μs : Fin (m + 1) → ℂ} (hμ : ∀ i, ‖μs i‖ = 1) {s t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A : (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ a₁, STPsum (d := d) A a₁ = 0) (a₁ : Zd d L) : STPsum (d := d) (UN d L g μs s t A) a₁ = 0
QopAlgebra.lean:629: theorem QopAlgebra_Psum_deriv {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hsum : ∀ τ a₁, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ τ a = 1) {t : ℝ} {ϑ' : (Fin (m + 1) → Zd d L) → ℂ} (hd : ∀ a, HasDerivAt (fun τ => ϑ τ a) (ϑ' a) t) (a₁ : Zd d L) : STPsum (d := d) ϑ' a₁ = 0
QopAlgebra.lean:643: theorem QopAlgebra_Qop_hasDerivAt {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} {A : ℝ → (Fin (m + 1) → Zd d L) → ℂ} {t : ℝ} {A' ϑ' : (Fin (m + 1) → Zd d L) → ℂ} (hA : ∀ a, HasDerivAt (fun τ => A τ a) (A' a) t) (hϑ : ∀ a, HasDerivAt (fun τ => ϑ τ a) (ϑ' a) t) (a : Fin (m + 1) → Zd d L) : HasDerivAt (fun τ => STQop (d := d) ϑ τ (A τ) a) (STQop (d := d) ϑ t A' a - STPsum (d := d) (A t) (a 0) * ϑ' a) t

### b.4 The merged pin (`Step34Pins.lean:518-522`)
$ sed -n '518,522p' RBM3D/Induction/Step34Pins.lean
def STMollifierEx (d : ℕ) : Prop :=
  3 ≤ d → ∀ (m : ℕ) (Λ : ℝ), 0 < Λ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      haveI : NeZero L := ⟨by omega⟩
      ∃ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ
(the theorem `stMollifierEx_holds (d : ℕ) : STMollifierEx d` is typed exactly as the pin, see b.2 `#check`)

### b.5 Compiled nonempty instances (`QopAlgebra.lean:900-925`: mollifier; `:930-978`: algebra at `d = 3`, `L = 3`)
$ sed -n '900,925p' RBM3D/Induction/QopAlgebra.lean
/-- `stMollifierEx_holds` at `d = 3`, `m = 1` (two indices), `Λ = 1`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 1 →
    haveI : NeZero L := ⟨by omega⟩
    ∃ ϑ : ℝ → (Fin (1 + 1) → Zd 3 L) → ℂ, STMollifierProps (d := 3) g C c ϑ :=
  stMollifierEx_holds 3 (by norm_num) 1 1 one_pos

/-- `stMollifierEx_holds` at `d = 3`, `m = 2` (three indices), `Λ = 1`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 1 →
    haveI : NeZero L := ⟨by omega⟩
    ∃ ϑ : ℝ → (Fin (2 + 1) → Zd 3 L) → ℂ, STMollifierProps (d := 3) g C c ϑ :=
  stMollifierEx_holds 3 (by norm_num) 2 1 one_pos

/-- The same, unpacked at the data `L = 5`, `g = 1`, `m = 2`: the constants and a mollifier. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∃ ϑ : ℝ → (Fin (2 + 1) → Zd 3 5) → ℂ, STMollifierProps (d := 3) (1 : ℝ) C c ϑ := by
  obtain ⟨C, c, hC, hc, h⟩ := stMollifierEx_holds 3 (by norm_num) 2 1 one_pos
  exact ⟨C, c, hC, hc, h 5 (by norm_num) 1 one_pos le_rfl⟩

/-- The mollifier itself at `d = 3`, `L = 3`, `m = 1`, `g = 1`: the four properties of `STMollifierProps`
with the explicit constants `C = (1 + 40·3·1) 6^{3·1}`, `c = 1/2`. -/
example : STMollifierProps (d := 3) (L := 3) (m := 1) (1 : ℝ) ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1)) (1 / 2)
    (QopAlgebra_mollifier 3 3 1 1) :=
  QopAlgebra_mollifier_props 3 3 1 le_rfl one_pos

/-- Data of the algebra instances: `d = 3`, `L = 3`, two indices (`m = 1`), `g = 1`, the mollifier `ϑ`. -/
private abbrev qaTheta : ℝ → (Fin (1 + 1) → Zd 3 3) → ℂ := QopAlgebra_mollifier 3 3 1 1
$ sed -n '930,978p' RBM3D/Induction/QopAlgebra.lean | grep -n '^example\|^  QopAlgebra' | cut -c1-110
3:example (A : (Fin (1 + 1) → Zd 3 3) → ℂ) (a₁ : Zd 3 3) :
5:  QopAlgebra_Psum_Qop qaTheta (qaTheta_sum (1 / 2)) A a₁
8:example : STQop (d := 3) qaTheta (1 / 2) (STQop (d := 3) qaTheta (1 / 2) (fun _ => (1 : ℂ)))
10:  QopAlgebra_Qop_of_sumZero qaTheta (1 / 2) fun a₁ => QopAlgebra_Psum_Qop qaTheta (qaTheta_sum (1 / 2)) _ a
13:example (a₁ : Zd 3 3) :
16:  QopAlgebra_ThetaN_sumZero 1 (le_refl 3) (fun _ => norm_one) (by norm_num) (by norm_num)
20:example (a₁ : Zd 3 3) :
23:  QopAlgebra_UN_sumZero 1 (le_refl 3) (fun _ => norm_one) (by norm_num) (by norm_num)
27:example (A : (Fin (1 + 1) → Zd 3 3) → ℂ) (a : Fin (1 + 1) → Zd 3 3) :
33:  QopAlgebra_commutator_ThetaN 1 _ qaTheta (1 / 2) A a
36:example (a₁ : Zd 3 3) : STPsum (d := 3) (fun a => deriv (fun τ => qaTheta τ a) 0) a₁ = 0 :=
37:  QopAlgebra_Psum_deriv qaTheta_sum
41:example (a : Fin (1 + 1) → Zd 3 3) :
44:  QopAlgebra_Qop_hasDerivAt_const

### b.6 Name-clash grep (new public names in other RBM3D files; private helpers `qa*`)
$ for each of the 19 public names: grep -rwn NAME RBM3D --include='*.lean' | grep -v QopAlgebra.lean | wc -l   # total hits = 0
$ grep -rnwE 'qaZ1|qaZ2|qaY|qaU|qaS|qaPhi|qaTheta|qa_[A-Za-z0-9_]+' RBM3D --include='*.lean' | grep -v '^RBM3D/Induction/QopAlgebra.lean' | wc -l
       0
$ grep -c '^private' RBM3D/Induction/QopAlgebra.lean
39

### b.7 Ports (RBM2D `Induction/SumZeroQ.lean` at `c9a24cf`, read-only `git show`)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/SumZeroQ.lean | tail -2
 RBM2D/Induction/SumZeroQ.lean | 140 ++++++++++--------------------------------
 1 file changed, 31 insertions(+), 109 deletions(-)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log --oneline c9a24cf..HEAD -- RBM2D/Induction/SumZeroQ.lean
bcc2c11 T2275: merge comment clean-up (Induction)
99d6fe0 T2274: merge dead-code deletion (82 modules removed, 328 files trimmed)
(ports below are compared against `git show c9a24cf:RBM2D/Induction/SumZeroQ.lean`, the version the ticket names)
portdiff.py: EQUAL after renaming (3): SumZeroQ_sum_filter_prod, SumZeroQ_slot_zero, SumZeroQ_slot_succ
portdiff.py: DIFFERS (7): SumZeroQ_Qop_of_sumZero, SumZeroQ_SB_mul_Theta_symm, SumZeroQ_col_sum, SumZeroQ_Psum_Qop, SumZeroQ_SumZero_thetaSig, SumZeroQ_commutator, SumZeroQ_Psum_varthetaDot
(`DIFFERS` rows are the adapted statements, differences by design: `SB L`,`Theta L` -> `SB d L g`,`Theta d L g` (+ argument `g`); `thetaSig L E σ` -> `ThetaN d L g μs` with `‖μs i‖ = 1`; `SumZero L A` -> `∀ a₁, STPsum A a₁ = 0`; `Qop L`/`vartheta L` -> `STQop ϑ`/abstract `ϑ` with hypothesis clause 1 of `STMollifierProps`.)

### b.8 Registry pre-check (DECISIONS §20): temporary file `import RBM3D` + `import RBM3D.Induction.QopAlgebra` + `#assert_rbm_axioms`
$ lake env lean precheck.lean > precheck.out 2>&1; echo $?
0
$ sed -n '1,3p' $SP/precheck.out
axiom audit: 1675 theorems, 637 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
$ grep -n 'STMollifierEx' $SP/precheck.out RBM3D/Test/Axioms.lean | sed 's#$SP/##' | cut -c1-150
precheck.out:51:  RBM.Gauss.Sizes.STMollifierEx: 2 [no certificate]
precheck.out:66: RBM.Gauss.Sizes.STMollifierEx,
RBM3D/Test/Axioms.lean:127:   `RBM.Gauss.Sizes.STMollifierEx, -- `rmk:choosechi`: existence of the mollifier (DECISIONS §25)
$ grep -n 'STMollifierEx\|premises found by scanning' $SP/precheck0.out | sed 's#$SP/##'
51:  RBM.Gauss.Sizes.STMollifierEx: 1 [no certificate]
55:premises found by scanning: 50 (borrowed 2, owed 36, structural 12).
(`precheck0.out` = the same check without `import RBM3D.Induction.QopAlgebra`)

### b.9 Full build, branch
$ lake build 2>&1 | tail -1
Build completed successfully (3750 jobs).
$ git log --oneline -1; git diff --stat main...t/T2055 | cat; git status --short | wc -l
74b1073 T2055: S3-04 QopAlgebra: prove STMollifierEx (smoothed-scale mollifier) and the algebra of P, Q_t, Theta, U
 RBM3D/Induction/QopAlgebra.lean | 978 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 978 insertions(+)
       0

### b.10 Numeric cross-check of the Lean definitions with the final constants (`$SP/chk.py`, `d = 3`)
L g m | max th/(l^-dm e^{-S/2l}) <= C | max (1-t)|dth| l^dm <= C | max u z2/z1 <= 40 | sum over (x_1..x_m) of th, x_i = a_i - a_1 (t=.5) | |sum_x e^{-u|x|} - z1^d|
9 0.1 1 | 3.638e+00 <= 2.614e+04 | 9.119e-01 <= 2.614e+04 | 0.81 <= 40 | 1.000000000000 | 1.8e-15
9 0.1 2 | 1.324e+01 <= 1.124e+07 | 6.635e+00 <= 1.124e+07 | 0.81 <= 40 | 1.000000000000 | 1.8e-15
9 1.0 1 | 3.638e+00 <= 2.614e+04 | 9.119e-01 <= 2.614e+04 | 0.76 <= 40 | 1.000000000000 | 0.0e+00
9 1.0 2 | 1.324e+01 <= 1.124e+07 | 6.635e+00 <= 1.124e+07 | 0.76 <= 40 | 1.000000000000 | 0.0e+00

### b.11 Narrative (facts as in b.1-b.10)
- Target 1: `stMollifierEx_holds (d : ℕ) : STMollifierEx d` is proved for every `d` (the pin's premises `3 ≤ d` and `g ≤ Λ` are not used).
  The mollifier is the construction of (a)(i): `y_t = 1 + g/√(1-t)`, `u_t = y_t⁻¹ + L⁻¹ (= 1/ℓ̃_t)`,
  `ϑ_{t,a} = exp(-u_t S(a)) / z(u_t)^{d m}`, `S(a) = Σ_{i≥2} zdistD(a_i - a₀)`, `z(u) = Σ_{y : ZMod L} exp(-u zdist y)`.
- The four clauses of `STMollifierProps` (constants `C = (1 + 40 d m) 6^{d m}`, `c = 1/2`, independent of `g`, `L ≥ 3`, `Λ`):
  clause 1 `QopAlgebra_mollifier_sum` (any real `t`): filter factorisation `qa_sum_filter_prod` and `Σ_x e^{-u|x|} = z^d` (`qaZ1_pow`);
  clause 2: `qaU_lb` (`u ≥ 1/(2ℓ_t)`), `qaZ1_ge` (`z ≥ (e u)⁻¹`, counting `⌊1/u⌋+1 ≤ L` points), `qaU_ub` (`ℓ_t u ≤ 2`), hence `z⁻¹ ≤ 6/ℓ_t`;
  clauses 3-4: `qaU_deriv` (`|∂_t u_t| ≤ u_t/(2(1-t))`), `qaPhi_hasDerivAt` (`Φ' = Φ(-S + d m z₂/z)`), `qa_u_Z2_le`
  (`u z₂ ≤ 40 z`, from `Σ k r^k = r/(1-r)²` and `z ≥ (e u)⁻¹`), `qa_core` (uses `x e^{-x} ≤ 1`).
- Differences from (a)(i), none changes a verdict, so no (a′): (a) uses `z ≥ ℓ̃/(2e)` and `E|x| ≤ Kℓ̃`; the proof uses `z ≥ ℓ̃/e`, `ℓ ≤ 2ℓ̃`
  and `u z₂ ≤ 40 z` (so `C` differs from (a)'s `max((4e)^{dm}, ...)`; b.10 re-checks the final constants numerically).
- `ℓ_t` of the pin is `ellT` (kinks at `1-t = g²`, `g²/L²`); only the smoothed `u_t` is differentiated (T2041b).
  `deriv` at `t = 0` is two-sided: `QopAlgebra_mollifier_differentiableAt` holds at every `t < 1` (the formula is defined for all real `t`).
- Target 2 (algebra, b.3): `𝒫𝒬_t = 0` needs only clause 1 at the given `t`; `Θ^{(m+1)}` (`ThetaN`) and `U^{(m+1)}` (`UN`) preserve sum-zero for
  `3 ≤ L`, `0 ≤ t < 1`, `‖μ_i‖ = 1` (no condition on `s`), via the column sums `μ(1-tμ)⁻¹` and `(1-sμ)(1-tμ)⁻¹` (`QopAlgebra_col_sum_*`);
  commutators are linearity; `QopAlgebra_Psum_deriv` (`𝒫 ∂_tϑ = 0`) and `QopAlgebra_Qop_hasDerivAt(_const)` give `[∂_t, 𝒬_t]` in terms of `∂_tϑ`.
- `zeroModeSet` and `projMat` (named in the ticket) are not used: no statement of target 2 needs them (sum-zero is `STPsum A = 0`).
- Ports (b.7): three statements are equal to RBM2D `c9a24cf` after renaming; the other seven are adapted for the RBM3D operators `ThetaN`, `UN`, `SB d L g`, `Theta d L g`.
- Registry: `RBM3D/Test/Axioms.lean` is not edited (the module adds no `Prop`-valued definition). b.8: with this module the scan finds 49 premises
  against 50 without it and lists `STMollifierEx` among the registered premises that carry nothing, so its line (`Axioms.lean:127`) can go; the cleanup ticket removes it.
  (The count `STMollifierEx: 1 -> 2` is the type of `stMollifierEx_holds` mentioning it.)  The full `lake build` (b.9) does not see this module (the hub adds the
  root import at merge), the registry pre-check (b.8) does.

## (c) Verified Mathlib names (each by `#check` in `$SP/names.lean`, exit 0; signatures in the tool log)
`Finset.sum_bij` (bijection `ZMod L ≃ range L` via `val`); `ZMod.val_injective`; `ZMod.val_natCast_of_lt`; `Nat.floor_le`; `Nat.lt_floor_add_one`;
`inv_lt_comm₀`; `inv_anti₀`; `le_div_iff₀`; `Finset.sum_le_sum_of_subset_of_nonneg`; `hasSum_coe_mul_geometric_of_norm_lt_one` (`HasSum (n r^n) (r/(1-r)^2)`);
`sum_le_hasSum`; `Real.exp_lt_one_iff`; `Real.exp_le_one_iff`; `Real.add_one_le_exp`; `Real.exp_one_lt_d9`; `Real.exp_nat_mul`; `Real.exp_sum`;
`Finset.sum_range_reflect`; `Finset.sum_range_succ'`; `Fintype.prod_sum`; `Finset.mul_prod_erase`; `Finset.sum_fiberwise`; `Finset.sum_nbij'`; `Finset.sum_product'`;
`Fintype.sum_equiv`; `HasDerivAt.sqrt`; `HasDerivAt.inv`; `HasDerivAt.div`; `HasDerivAt.comp`; `HasDerivAt.pow`; `HasDerivAt.exp`; `HasDerivAt.fun_sum`;
`HasDerivAt.ofReal_comp`; `HasDerivAt.unique`.
Verified absent: `Real.exp_lt_one` (tool log: `error(lean.unknownIdentifier): Unknown constant `Real.exp_lt_one``); `Real.exp_lt_one_iff` is used instead.
Merged RBM3D declarations used (resolved by compile): `thetaKer`, `uKer`, `ThetaN`, `UN`, `cycProd`, `norm_cycProd`, `norm_t_mul_lt_one`, `Theta_transpose_of_three_le`,
`Theta_commute_SB_of_three_le`, `sum_Theta_row_of_three_le`, `sum_SB_row`, `SB_transpose`, `ellT`, `ellT_pos`, `ellT_le_L`, `one_le_ellT`, `zdist`, `zdistD`, `Zd`.

## (d) Open issues and paper-delta candidates
- No open issue; every target of the ticket is built, committed on `t/T2055` (b.9) and instantiated (b.5).
- Paper-delta candidates: none new.  `T2041b` (signed) is realised by the smoothed scale `ℓ̃_t = 1/u_t` (`ℓ_t/2 ≤ ℓ̃_t ≤ 2ℓ_t`: `qaU_lb`, `qaU_ub`); the pin
  `STMollifierProps` is unchanged, so no statement differs from the paper beyond T2041b.
- Observation: the constants of `STMollifierEx` come out independent of `Λ` and the proof never uses `3 ≤ d`; the pin allows a dependence, so nothing to change.
- Observation: RBM2D `SumZeroQ.lean` changed after `c9a24cf` (b.7); the ports follow `c9a24cf`, as the ticket names it.

## Repair — Sat Oct  3 13:41:44 UTC 2026 (repairer, claude-opus-5-5; addresses T2055-audit.md round 1, "Required for resubmission" 1-3)
Supersedes b.5 for the two new instances; no statement changed. Commit on `t/T2055`:
$ git log --oneline -1; git diff --name-only main...t/T2055
f734825 T2055: repair round 1 — compiled instances of QopAlgebra_commutator_UN and the general QopAlgebra_Qop_hasDerivAt
RBM3D/Induction/QopAlgebra.lean
$ lake build RBM3D.Induction.QopAlgebra 2>&1 | tail -1; grep -cE 'sorry|admit|native_decide|axiom' RBM3D/Induction/QopAlgebra.lean
Build completed successfully (3704 jobs).
0
$ lake env lean $SP/rep_ax.lean  # #print axioms of the 18 public theorems + QopAlgebra_mollifier
$ tr -s '\n' ' ' < $SP/rep_ax.out | grep -o 'depends on axioms: \[[^]]*\]' | sort | uniq -c
  19 depends on axioms: [propext, Classical.choice, Quot.sound]
$ for n in QopAlgebra_commutator_UN QopAlgebra_Qop_hasDerivAt; do echo "$n $(sed -n '899,1000p' RBM3D/Induction/QopAlgebra.lean | grep -cw $n)"; done
QopAlgebra_commutator_UN 1
QopAlgebra_Qop_hasDerivAt 1
$ sed -n '976,996p' RBM3D/Induction/QopAlgebra.lean
/-- The commutator `[𝒬_t, U^{(2)}_{s,t,σ}]` at `μ_i = 1`, `g = 1`, `s = 1/4`, `t = 1/2`. -/
example (A : (Fin (1 + 1) → Zd 3 3) → ℂ) (a : Fin (1 + 1) → Zd 3 3) :
    STQop (d := 3) qaTheta (1 / 2) (UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2) A) a
        - UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2)
            (STQop (d := 3) qaTheta (1 / 2) A) a =
      UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2)
          (fun b => STPsum (d := 3) A (b 0) * qaTheta (1 / 2) b) a -
        STPsum (d := 3) (UN 3 3 (1 : ℝ) (fun _ : Fin (1 + 1) => (1 : ℂ)) (1 / 4) (1 / 2) A) (a 0) *
          qaTheta (1 / 2) a :=
  QopAlgebra_commutator_UN 1 _ qaTheta (1 / 4) (1 / 2) A a

/-- The general `[∂_t, 𝒬_t]` identity at `t = 0` with the `t`-dependent tensor `𝒜_τ ≡ τ`, `∂_t𝒜 ≡ 1`. -/
example (a : Fin (1 + 1) → Zd 3 3) :
    HasDerivAt (fun τ : ℝ => STQop (d := 3) qaTheta τ (fun _ => (τ : ℂ)) a)
      (STQop (d := 3) qaTheta 0 (fun _ => (1 : ℂ)) a -
        STPsum (d := 3) (fun _ : Fin (1 + 1) → Zd 3 3 => ((0 : ℝ) : ℂ)) (a 0) *
          deriv (fun τ => qaTheta τ a) 0) 0 :=
  QopAlgebra_Qop_hasDerivAt (A := fun τ _ => (τ : ℂ)) (A' := fun _ => 1)
    (fun _ => by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp)
    (fun a => (QopAlgebra_mollifier_differentiableAt 3 3 1 le_rfl one_pos (by norm_num) a).hasDerivAt) a


Data: `d = 3`, `L = 3`, `m = 1`, `g = 1`, `μ_i = 1`, `ϑ = qaTheta = QopAlgebra_mollifier 3 3 1 1`; item 1 at `s = 1/4`, `t = 1/2`;
item 2 at `t = 0` with the `t`-dependent tensor `A τ ≡ τ`, `A' ≡ 1`; `hA` from `hasDerivAt_id`/`HasDerivAt.ofReal_comp`, `hϑ` from
`QopAlgebra_mollifier_differentiableAt`. Both are the auditor's probe (audit section 3), now compiled in the module.
