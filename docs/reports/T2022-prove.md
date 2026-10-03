Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 04:25:24 UTC 2026

Notation: `ρ = W^ε`, `ℓ_t = min(max(g/√|1−t|,1),L)` (`Defs/Params.lean:32`), `|a|` = periodic `ℓ¹` distance `zdistD`, `Λ = 𝔡⁻¹` (`g ∈ (0,Λ]`) except in `EKTTk` where `Λ` is the multiplier of `ℓ ≤ Λ ℓ_t`. `ratio = (g²+|1−s|)/(g²+|1−t|)`. Paper sources (files under `paper/tex/`): `3_5_Loop_Hierarchy.tex:328` (`lem:propT`), `:1620–1672` (`lem:sum_Ndecay`, `lem:sum_decay`, `lem:sum_decay_nonzero`), `7_8_light_weight.tex:1661` (`claim:TTk`). Statements: probe `c961e62:RBM3D/Probe/T2016Pins.lean` lines 44–198 (line 44 `namespace RBM`, line 197 `ring`, the last line of `ekTTk_holds`); T2016 report b2, b8.

### (i) Exponent table: the seven pins, the vocabulary, the three bridges

| # | declaration (paper label, line) | what it states | order of constants | hypotheses and regimes | bridge / proof |
|---|---|---|---|---|---|
| 1 | `EKsgn m σ` | `i ↦ PropSpin m (σ i)`, `m(+)=m`, `m(−)=m̄`; `UN d L g (EKsgn m σ)` is `U^{(n)}_{s,t,σ}` of `(def_Ustz)` | — | `‖m‖=1` | `ek_norm_spin` (helper, cases on `Bool`) |
| 2 | `EKFastDecay g s W ε D A` = `(deccA0)` (`3_5:1634`) | `‖A_a‖ ≤ W^{−D}` whenever `∃ i j, W^ε ℓ_s ≤ |a_i−a_j|` | — | window `R = W^ε ℓ_s` (`ℓ_s = ellT L g s`) | def only |
| 3 | `EKSumZero A` = `(sumAzero)` (`3_5:1655`) | `Σ_{b : b_{i₀}=x} A_b = 0` for all `x`, `i₀` the index of value 0 (first index) | — | `[NeZero L]` | def only |
| 4 | `EKSumNdecay d n` = `(sum_res_Ndecay)` (`3_5:1622`) | `‖U^{(n)}_{s,t,σ}∘A‖_∞ ≤ ((1−s)/(1−t))^n ‖A‖_∞` | no constant (factor 1, no `L^τ`) | `3≤d`, `2≤n`, `3≤L`, `0<g`, `‖m‖=1`, any `σ`, `0≤s≤t<1` (no upper limit on `t` below 1) | PROVED by merged `norm_UN_le` (`Kernel/Evolution.lean:157`, `{m : Fin n → ℂ}` with `∀ i, ‖m i‖=1`; `ekSumNdecay_holds`, 3 lines) |
| 5 | `EKSumDecay1 d n Λ` = `(sum_res_1)` (`3_5:1639`) | `‖U A‖ ≤ W^{Cε}(ℓ_t²/ℓ_s²) ratio^n ‖A‖ + W^{−D+C}` | `C = C(d,n,Λ)` after `(d,n,Λ)`, before `L,g,W,ε,D,s,t,m,σ,A`; independent of `ε,D` | antecedent `Prop5Decay d Λ`; `3≤d`, `2≤n`, `0<Λ`; `0<g≤Λ`, `1<W`, `0<ε<1`, `1<D`, `4≤W^ε` (T2016b); `0≤s≤t≤1−g²/L²`; `W⁻¹ ≤ (1−t)/(1−s)`; `EKFastDecay` | pin only (EK-3) |
| 6 | `EKSumDecayNAL d n Λ κ` = `(sum_res_2_NAL)` (`3_5:1649`) | `‖U A‖ ≤ W^{Cε} ratio^{n−1}‖A‖ + W^{−D+C}` (no `ℓ_t²/ℓ_s²`) | `C(d,n,Λ,κ)`, same order | row 5 plus `Prop5Short d Λ κ`, `0<κ≤Im m`, non-alternating `σ` (`∃ k, σ k = σ (k+1)`) | pin only (EK-3) |
| 7 | `EKSumDecay2 d n Λ κ` = `(sum_res_2)` (`3_5:1659`) | for sum-zero `A`: `‖U A‖ ≤ W^{Cε} ratio^n ‖A‖ + W^{−D+C}` | `C(d,n,Λ,κ)`, same order | row 6 plus `Prop6Diff1 d Λ κ (1/2)`, `EKSumZero A`, `log L ≤ W^ε` (T2016a), any `σ` | pin only (EK-4) |
| 8 | `EKSumDecayNonzero d n Λ κ` = `(sum_res_Ndecay_nonzero)` (`3_5:1666–1671`) | `‖Q^{(A)} U A‖_∞ ≤ C ‖A‖_∞` (paper `≺` made loss-free; `zeroModeSet d L A`) | `C(d,n,Λ,κ)` | `Prop5Short`, `Prop8ZeroMode d Λ κ`; `1−g²/L² ≤ s ≤ t < 1`; `κ ≤ Im m`; `A ⊇ I_diff(σ)` (`σ_i ≠ σ_{i+1} → i ∈ A`) | pin only (EK-5) |
| 9 | `EKPropT d` = `(TTT2)` (`3_5:328–338`) | `Σ_c 𝒯_u(|a−c|) 𝒯_t(|c−b|) ≤ C_d/(1−u) · 𝒯_t(|a−b|)` | `C = C_d` after `d`, before `L,g,u,t,a,b`; no `L^τ` | `3≤d`, `0<g`, `0≤u≤t<1`, regime (i) `g²/L² ≤ 1−t` or (ii) `1−u ≤ g²/L²` | PROVED by merged `propT k` (`Kernel/PropT.lean:409`, `d = k+2`; `ekPropT_holds`: `d = k+2` by `obtain`, apply `propT k`) |
| 10 | `EKTTk d n` = `(eq:key_T_reudce)` (`7_8:1661`) | `Σ_{α∈D} ∏_i 𝖳_t(|x_i−α|∧ℓ) 𝖳_t(|y_i−α|∧ℓ) ≤ C Λ² (W^d(1−t))⁻¹ Ψ_t^{n−2} ∏_i 𝖳_t(|x_i−y_i|∧ℓ)` | `C = C(d,n)` after `(d,n)` | `3≤d`, `2≤n`, `0<W`, `0≤g`, `t<1`, `g² ≤ L²(1−t)` (regime `1−t ≥ g²/L²`), `1 ≤ ℓ ≤ Λ ℓ_t`, `D` a finset of the `ℓ`-ball around `a` | PROVED by merged `key_T_reduce_absorbed` (`Kernel/PropT.lean:1056`, has `3Λ²` and `keyC k n`); `ekTTk_holds` takes `C = 3·keyC k n` (`keyC = (√2^k)^n·4·ballC k > 0`) and closes by `ring` |

Slack of the order-of-constants and regime constraints (all strict at the instance in (ii)):

| quantity | value at the instance | constraint | slack |
|---|---|---|---|
| `1−t` vs `g²/L²` | `0.1` vs `0.01` | `EKPropT` (i), `EKTTk`, `t ≤ 1−g²/L²` (`0.9 ≤ 0.99`) | factor 10 |
| `W^ε` | `5` (`W=25, ε=1/2`) | `4 ≤ W^ε`, `log L = 1.609 ≤ W^ε` | `1.25×`, `3.1×` |
| `(1−t)/(1−s)` | `0.2` | `≥ W⁻¹ = 0.04` | `5×` |
| `ℓ_s, ℓ_t` | `1.0, 1.5811` | `ℓ_s ≤ ℓ_t ≤ L`; `EKTTk` `ℓ=1 ≤ Λℓ_t` | `1.58×` |
| `R = W^ε ℓ_s` | `5.0` | torus `ℓ¹` diameter `= 6` (so far pairs exist) | pair at distance 5 |
| nonzero window | `s'=0.995, t'=0.999` | `1−g²/L² = 0.99 ≤ s' ≤ t' < 1` (`lem:sum_decay_nonzero` has no admissible `s` at `t=0.9`) | `0.005` |
| `‖Θ‖`-parameter | `‖tμ‖ = 0.9 < 1` | `Theta` is `Ring.inverse (1 − ξ S^{(B)})` (`Propagator/Basic.lean:70`), a genuine inverse for `‖ξ‖<1` | `0.1` |

Statement of record (not re-proposed, DECISIONS §18): paper-delta candidates `T2016a` (`log L ≤ W^ε` in `(sum_res_2)`), `T2016b` (`4 ≤ W^ε`), `T2016c` (`lem:propT` only in regimes (i),(ii)), `T2016d` (`claim:TTk` `D` ⊂ `ℓ`-ball, `ℓ ≥ 1`, explicit `Λ²`), `T2016e` (`lem:sum_decay_nonzero` loss-free, both charges), `T2016f` (constants uniform in `g ∈ (0,Λ]`, `ℓ¹` distances).

### (ii) One concrete nondegenerate instance (`d=3, L=5, n=2, g=1/2, s=1/2, t=9/10, m=i, κ=1/2, Λ=1, W=25, ε=1/2, D=2`)

Command (exact `Θ = (1−ξ S^{(B)})⁻¹`, `ξ = tμ`, 125×125 matrix; `S^{(B)} = (1+2dg²)⁻¹(δ + g² 1_{|x|=1})` as in `Defs/Block.lean`; `μ_i = m(σ_i)m(σ_{i+1})`; the `ℓ^∞→ℓ^∞` norm of the product kernel is `∏_i` (row-sum of `|K_i|`) maximised over the row):
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2022 && python3 pre.py`
```
row sums S in 0.9999999999999999 1.0000000000000002
hyp: 3<=d True 2<=n True 3<=L True 0<g True 0<=s<=t<1 True |m|=1 True
sigma (True, False) mu [(1+0j), (1+0j)] ||U^(2)||_inf= 25.0 <= ((1-s)/(1-t))^2 = 25.00000000000001 : True
sigma (True, True) mu [(-1+0j), (-1+0j)] ||U^(2)||_inf= 1.195123 <= ((1-s)/(1-t))^2 = 25.00000000000001 : True
sigma (False, False) mu [(-1-0j), (-1-0j)] ||U^(2)||_inf= 1.195123 <= ((1-s)/(1-t))^2 = 25.00000000000001 : True
sigma (False, True) mu [(1+0j), (1+0j)] ||U^(2)||_inf= 25.0 <= ((1-s)/(1-t))^2 = 25.00000000000001 : True
max over sweep of ||U^(1)||/((1-s)/(1-t)) = 1.0 (<=1 required)
propT hyp: 0<g True 0<=u<=t<1 True g2/L2<=1-t True ( 0.01 <= 0.09999999999999998 )
propT: max_{a,b} (1-u) sum_c T_u T_t / T_t = 8.9772
TTk hyp: 0<W True 0<=g True t<1 True g2<=L2(1-t) True 1<=ell True ell<=Lam*ell_t True (ell_t=1.5811)
TTk: |D|= 7 LHS/(Lam^2 (W^d(1-t))^-1 Psi^0 prod sfT) = 0.8939 (needs <= C, bridge C=3*keyC)
```
(The sweep line is over `g ∈ {0.1,0.5,1}`, `m = e^{iθ}`, `θ ∈ {0.3, π/2, 2, π}`, `(s,t) ∈ {(0,.5),(.5,.9),(.5,.99),(.9,.9)}`, `L=5`; the value 1.0 is the equality case of the opposite-charge pair, `μ=1`, where `U` is a positive kernel with row sum exactly `(1−s)/(1−t)`.) `EKSumNdecay` at the ticket's data: LHS `25.0` against RHS `((1−s)/(1−t))^n = 25`: equality for `σ=(+,−)` (`μ=1`), `1.195` for `σ=(+,+)` (`μ=−1`); the bound is sharp, no slack in the opposite-charge case.

Command for the remaining hypotheses (vocabulary and the four non-proved pins, which stay hypotheses in their instances):
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2022 && python3 hyp.py`
```
EKSumDecay*: 0<g<=Lam True 1<W True 0<eps<1 True 1<D True 4<=W^eps True (W^eps=5) log L<=W^eps True (1.6094)
  0<=s<=t<=1-g2/L2 True (1-g2/L2=0.99) W^-1<=(1-t)/(1-s) True (0.040<=0.200) kappa<=Im m True |m|=1 True
  ell_s=1.0000 ell_t=1.5811 W^eps*ell_s=5.0000
  far-pair exists (EKFastDecay premise nonvacuous): pair (0,0,0),(1, 2, 2) dist=5 >= 5.0, #points at dist>=R: 32
  EKSumZero for A=delta0 x (delta0-delta_e): max_x |sum_{b1=x} A| = 0
EKSumDecayNonzero: 0<=s' True 1-g2/L2<=s'<=t'<1 True
EKSumNdecay/PropT/TTk hyps: see pre.py output
```
External-hypothesis limit computation (TEAM §8 lesson 14): the pins `Prop5Decay`, `Prop5Short`, `Prop6Diff1`, `Prop8ZeroMode` are antecedents of rows 5–8, which this ticket only states (no theorem takes them as a hypothesis); their numerical limit checks are in T2016 report (a) block (B) (`C5 ≤ 1.43` to `L=65`, `C5s ≤ .99`, `C8 ≤ 1.25`, `C6 ≤ .99`, `t` down to `1−g²/L³`), and `Prop5Short` is proved on `main` (`Propagator/Prop5Short.lean:400 prop5Short_holds`). The arity of the four merged pins matches the probe text: `Prop5Decay d Λ`, `Prop5Short d Λ κ`, `Prop6Diff1 d Λ κ c`, `Prop8ZeroMode d Λ κ` (`Propagator/Pins.lean:35, 47, 58, 88`).

### Verdicts
- Target 1 (vocabulary, seven pins, three bridges, copied from probe lines 44–198): PASS. Every hypothesis set is satisfiable at the instance; the three bridge theorems close from merged `norm_UN_le`, `propT`, `key_T_reduce_absorbed` with `d = k+2` (`3 ≤ d` gives `k = d−2`); the instance of `EKSumNdecay` at the ticket's data holds with equality for `σ=(+,−)`.
- Target 2 (instances for the three bridges and the vocabulary, probe lines 871–1076, only items mentioning item-1 declarations): PASS. Instance data above (`EKPropT` at `(u,t)=(1/2,9/10)`, `EKTTk` at `W=25, ℓ=1, Λ=1`, vocabulary: far pair and sum-zero tensor `δ₀⊗(δ₀−δ_e)`) satisfy every deterministic hypothesis.
- Overall: PASS.

## (b) Script output — Sat Oct  3 04:28:28 UTC 2026

### Build, scope, commit
```
$ cd RBM3D-wt/T2022 && lake build RBM3D.Evolution.Pins | tail -3
Build completed successfully (2544 jobs).
$ git log -1 --format="%h %s" t/T2022 ; git diff --stat main...t/T2022
62fe565 T2022: EK vocabulary, seven EK pins, three bridges (ekSumNdecay_holds, ekPropT_hol
 RBM3D/Evolution/Pins.lean | 414 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 414 insertions(+)
$ full build, with `import RBM3D.Evolution.Pins` temporarily inserted after the last import of RBM3D.lean (reverted; RBM3D.lean not committed): lake build | tail -3
 RBM.Gauss.Sizes.locDomain].
non-vacuity certificates: 6 of 13 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3725 jobs).
$ git status --short RBM3D.lean   (after revert)
(empty)
```

### Axioms (`lake env lean ax.lean`: `#print axioms` of every public declaration)
```
'RBM.ekSumNdecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekPropT_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekTTk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_norm_spin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ek_sum_fin_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKsgn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKFastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKSumZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKSumNdecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKSumDecay1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKSumDecayNAL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKSumDecay2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKSumDecayNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKPropT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.EKTTk' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Script diff of the pinned text against the probe (`git show c961e62:RBM3D/Probe/T2016Pins.lean` lines 44-198 vs Pins.lean, header comment and file placement excluded)
```
$ diff <(sed -n 44,198p probe) <(sed -n "<Vocabulary header-2>,+154p" Pins.lean)
no difference (155 lines identical)
```

### Target statements (extracted by script from Pins.lean; docstrings omitted, proof bodies of bridges cut at `:= by`)
```
noncomputable def EKsgn {n : ℕ} (m : ℂ) (σ : Fin n → Bool) : Fin n → ℂ := fun i => PropSpin m (σ i)
def EKFastDecay {d L n : ℕ} (g s W ε D : ℝ) (A : (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ a : Fin n → Zd d L, (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (a i - a j) : ℝ)) →
    ‖A a‖ ≤ W ^ (-D)
def EKSumZero {d L n : ℕ} [NeZero L] (A : (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ i₀ : Fin n, i₀.val = 0 → ∀ x : Zd d L,
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → Zd d L => b i₀ = x), A b = 0
def EKSumNdecay (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n →
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin n → Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
        ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          ‖UN d L g (EKsgn m σ) s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖
def EKSumDecay1 (d n : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 2 ≤ n → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * (ellT L g t ^ 2 / ellT L g s ^ 2)
                * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
def EKSumDecayNAL (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Decay d Λ → Prop5Short d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, (∃ k, σ k = σ (finRotate n k)) →
        ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (n - 1) * ‖A‖ + W ^ (-D + C)
def EKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Decay d Λ → Prop5Short d Λ κ → Prop6Diff1 d Λ κ (1 / 2) →
    3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A → EKSumZero A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
def EKSumDecayNonzero (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Short d Λ κ → Prop8ZeroMode d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ s t : ℝ, 0 ≤ s → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s → s ≤ t → t < 1 →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : Finset (Fin n),
          (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) →
          ∀ 𝒜 : (Fin n → Zd d L) → ℂ,
            haveI : NeZero L := ⟨by omega⟩
            ‖zeroModeSet d L A (UN d L g (EKsgn m σ) s t 𝒜)‖ ≤ C * ‖𝒜‖
def EKPropT (d : ℕ) : Prop :=
  3 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
        (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
        ∀ a b : Zd d L,
          ∑ c : Zd d L, tailT d L g u (zdistD d L (a - c)) * tailT d L g t (zdistD d L (c - b))
            ≤ C / (1 - u) * tailT d L g t (zdistD d L (a - b))
def EKTTk (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
        ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
        ∀ (D : Finset (Zd d L)) (a : Zd d L), (∀ α ∈ D, (zdistD d L (a - α) : ℝ) ≤ ℓ) →
        ∀ x y : Fin n → Zd d L,
          ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistD d L (x i - α) : ℝ) ℓ)
                * sfT d L W g t (min (zdistD d L (y i - α) : ℝ) ℓ))
            ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
                (PsiT d L W g t ^ (n - 2) *
                  ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))
theorem ekSumNdecay_holds (d n : ℕ) : EKSumNdecay d n := by
theorem ekPropT_holds (d : ℕ) : EKPropT d := by
theorem ekTTk_holds (d n : ℕ) : EKTTk d n := by
```

### Compiled instances (private named checks in the same file, every deterministic hypothesis discharged; `EKSumDecay1` skeleton instance left to EK-2)
```
private theorem ekInstNdecay :
    ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekA0‖
    ≤ ((1 - 1 / 2) / (1 - 9 / 10)) ^ 2 * ‖ekA0‖ :=
  ekSumNdecay_holds 3 2 (by norm_num) le_rfl 5 (by norm_num) (1 / 2) (by norm_num) Complex.I
    Complex.norm_I ![true, false] (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) ekA0
private theorem ekInstPropT : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (zdistD 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (c - ekE))
      ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (0 - ekE)) := by
  obtain ⟨C, hC, H⟩ := ekPropT_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (by norm_num)) 0 ekE⟩
private theorem ekInstTTk : ∃ C : ℝ, 0 < C ∧
    ∑ α ∈ Finset.univ.filter (fun α : Zd 3 5 => (zdistD 3 5 (0 - α) : ℝ) ≤ 1),
        ∏ i, (sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistD 3 5 (![0, ekE] i - α) : ℝ) 1)
          * sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistD 3 5 (![ekE, 0] i - α) : ℝ) 1))
      ≤ C * (1 ^ 2 * (((25 : ℝ) ^ 3)⁻¹ / (1 - 9 / 10))) *
          (PsiT 3 5 25 (1 / 2) (9 / 10) ^ (2 - 2) *
            ∏ i, sfT 3 5 25 (1 / 2) (9 / 10)
              (min (zdistD 3 5 (![0, ekE] i - ![ekE, 0] i) : ℝ) 1)) := by
  obtain ⟨C, hC, H⟩ := ekTTk_holds 3 2 (by norm_num) le_rfl
  exact ⟨C, hC, H 5 25 (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 1
    le_rfl (by simpa using one_le_ellT (L := 5) (g := 1 / 2) (t := 9 / 10) (by norm_num)) _ 0
    (fun α hα => (Finset.mem_filter.mp hα).2) _ _⟩
```
The vocabulary instances `ek_fastDecay_A0`, `ek_fastDecay_Az`, `ek_sumZero_Az`, `ek_far_point_exists` (Pins.lean:276, 288, 316, 268) and the instances `ekInstNAL`, `ekInstDecay2`, `ekInstNonzero` (hypotheses `EKSumDecayNAL/2/Nonzero`, `Prop5Decay`, `Prop6Diff1`, `Prop8ZeroMode` kept as hypotheses: other gates pins; `prop5Short_holds` discharges `Prop5Short`) are in the file and compile.

### Name-clash grep (new public names vs the rest of RBM3D and RBM3D.lean, excluding Pins.lean)
```
$ for n in EKsgn EKFastDecay EKSumZero EKSumNdecay EKSumDecay1 EKSumDecayNAL EKSumDecay2 EKSumDecayNonzero EKPropT EKTTk ekSumNdecay_holds ekPropT_holds ekTTk_holds ek_norm_spin ek_sum_fin_two; do grep -rnw $n RBM3D RBM3D.lean | grep -v Evolution/Pins.lean | wc -l; done
0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Evolution/Pins.lean | wc -l
       0
```

Port citation: not a RBM1D/RBM2D port. Source is the compiled probe `RBM3D/Probe/T2016Pins.lean` at `c961e62` (branch `t/T2016`, read with `git show`, never checked out). Ported from the probe: lines 44-198, 507-514 (`ek_sum_fin_two`, helper of `ek_sumZero_Az`), 860-1076 minus the `EKSumDecay1` skeleton instance (probe lines 999-1010). Not copied: skeleton (208-762), BA reuse (774-859), appendices.

### Narrative
- Pins.lean = probe text copied; only the file header docstring is rewritten (it no longer mentions the skeleton or the block Anderson reuse), `set_option linter.style.longLine false` added before `namespace RBM`.
- No proof was changed: the three bridges and all instances compiled on current `main` unchanged.
- No theorem takes an EK pin or `Prop6Diff1` as a hypothesis; the instances `ekInstNAL`, `ekInstDecay2`, `ekInstNonzero` take pins as hypotheses but are `private` named checks, not public theorems.
- Full build with the root import inserted reported no unclassified premise (Test/Axioms ledger output tail above).

## (c) Verified Mathlib / merged names used
`Real.sqrt_eq_rpow`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`, `Real.log_le_sub_one_of_pos`, `Fintype.sum_prod_type'`, `Fintype.sum_equiv`, `finTwoArrowEquiv`, `finRotate`, `Finset.sum_filter`, `Finset.sum_ite_eq'`, `Finset.sum_sub_distrib`, `Fin.forall_fin_two`, `Complex.norm_I`, `Complex.I_im`: all resolve (Pins.lean builds). Merged: `norm_UN_le`, `propT`, `keyC`, `ballC_pos`, `key_T_reduce_absorbed`, `prop5Short_holds`, `one_le_ellT`, `UN`, `zeroModeSet`, `tailT`, `sfT`, `PsiT`, `ellT`, `PropSpin`, `zdistD`, `zdistD_neg`.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: T2016a-f (DECISIONS §18), not re-proposed. No new candidate.
- Root import `import RBM3D.Evolution.Pins` is for the hub (not committed here). `ek_sum_fin_two` is public (ek-prefixed) and unused outside the instances; EK-2 may reuse it.
- The three instances for the proved bridges are `private theorem` named checks, not `example`s; they compile and discharge all deterministic hypotheses.
