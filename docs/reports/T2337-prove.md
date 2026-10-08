Prover model: claude-sonnet-5-5
## (a) Math preflight — Thu Oct  8 13:56:20 UTC 2026

Notation: `e = 1-t`, `γ = t g²` (BA; band: `lgGam = t g²/(1+2dg²)`), `ε = e/γ`, `n = |a|`, `ℓ = ellT L g t`, `K = BAK` (real, row sums 1, `BAMss_pm_eq`/`BAMss_mp_eq`: `Θ = PropThetaQ (map K ofReal) t` for both mixed charges).

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | Laplace rep. | `Θ_t(0,a) = γ⁻¹∫₀^∞ e^{-ετ} kBA(τ,a)dτ`, `τ = γu`, `γε = e` (`BATheta_eq_laplace_kBA`, `BA/KHeat.lean:540`: `kBA(t g² u)`) | needs `0<t<1`, `3≤L`, `BASelf`; `γ>0` iff `t>0`, so `t = 0` is separate (`Θ = 1`, `PropThetaQ _ 0`) | exact (numeric check below: 0.0006633342 both sides) |
| 2 | head `(0,L²]` | `kBA ≤ CK·min(1,τ^{-d/2})·e^{-cK min(n²/τ,n)}` (`kBA_le`, `BA/KHeatTail.lean:631`), same shape as `kProd_le`; `CK,cK` depend on `(d,Λ,κ)` | `2 ≤ d`, `0<Λ`, `0<κ`, `BAReal d L g κ E m`, `g ≤ Λ` | `d ≥ 3` gives `d-2 ≥ 1` |
| 3 | tail `(L²,∞)` | `|kBA - L^{-d}| ≤ CG L^{-d} e^{-cG τ/L²}` (`kBA_gap`, `KHeat.lean:989`), so `kBA ≤ (1+CG)L^{-d}`; `∫_{L²}^∞ e^{-ετ} = e^{-εL²}/ε` | `0<d`, same data; `CG>0`, `cG>0` | `cG ≥ 0` is all `p5h_tail5` needs |
| 4 | `lg_bulk`, `lg_zero`, `lg_tail`, `lg_key` (`LaplaceGauss.lean:692/541/295`) | Θ-free (file header `:20`: "Nothing here mentions Θ"); `lg_bulk d hd cK hcK ↦ (CB, c')`; `lg_zero` const `1+2/(d-2)` | `3 ≤ d`, `cK>0` | `d=3`: `1+2/(d-2) = 3` |
| 5 | `LGConvA'` (γ = t g²) | `ε≥1 ⇒ 1/e ≤ CA/(g²+e)`; `ε<1 ⇒ 1/γ ≤ CA/(g²+e)`, `CA = 3+2Λ²`. Proof: `ε≥1`: `t≥1/2 ⇒ g² ≤ 2e ⇒ g²+e ≤ 3e`; `t<1/2 ⇒ e>1/2 ⇒ g²+e ≤ Λ²+1 ≤ 2(Λ²+1)e`. `ε<1`: `e<tg² ⇒ t>1/(1+Λ²)`, `g²+e<2g² ≤ 2(1+Λ²)·t g²` | `CA ≥ max(3, 2Λ²+2)` | factor ≈ 2 (grid max 101.77 vs 203.0 at Λ = 10, below) |
| 6 | `LGConvB'`, `LGConvC'` | `ε ≥ L⁻² ⇒ ℓ⁻¹ ≤ √ε`; `ε<L⁻² ⇒ ℓ=L`; `ε≥L⁻² ⇒ n/ℓ ≤ (d/2)εL²` for `n ≤ dL/2` | band proofs (`LaplaceGauss.lean:100-195`) use only `γ>0` and `γ ≤ g²` (`lg_gam_le`); `t g² ≤ g²` holds, so the proofs transfer verbatim | C' tight: ratio `(n/ℓ)/((d/2)εL²)` max = 1.0000 (equality case `n = dL/2`, `ε = L⁻²`; allowed) |
| 7 | use of `1+2dg²` in `Prop5Hold.lean` | exactly one place: `unfold lgGam` at `:84` (`p5h_gam_pos`); `:88`, `:94` unfold only `lgEps`. `grep -c "1 + 2 \* ("` = 1, and that hit (`:393`) is `C₀+1+2*(k!…)`, unrelated | everything else uses `γε = e` (`p5h_gam_mul_eps :91`) | `LGConvB/C` unchanged, only `LGConvA` is re-proved |
| 8 | substitution lines | `Theta_eq_laplace_prod` (`:105`, `:822-829`) ↦ `BATheta_eq_laplace_kBA`; `kProd_le` (`:786,:1268`) ↦ `kBA_le`; `kProd_gap` (`:787,:1269`) ↦ `kBA_gap`; `lg_convA` (`:789,:1271`) ↦ restated `CA = 3+2Λ²`; `lg_convB` (`:603,:677`), `lg_convC` (`:678`) ↦ restated, same proofs; `kProd d L τ a` (`:49-77, 452-1051`) ↦ `kBA d L g E m τ a` (extra args `g E m`, hypotheses `BAReal`); `Theta0_apply_eq` (`:829,:1076`) ↦ own identity (row 10). Not needed: `norm_Theta_apply_le` (`:809`), `p5h_norm_mu` (`:692`), `prop5Short` branch (`:1125-1264`, `σ₁=σ₂`), `p5h_mu_one` (`:1251`) | | |
| 9 | exponent `c` of P5 | `c = min(c'/2, 2/d)` | `c ≤ c'/2` (`p5h_head_shape`), `c·d ≤ 2` (`p5h_exp_zero`, zero mode) | `d=3`: `c ≤ 2/3`; `c ≥ 0` needed only |
| 10 | P8 identity | `BATheta0 = Θ - L^{-d}(1-t)⁻¹` entrywise: `L^{-2d}ΣΣ Θ = L^{-d}(1-t)⁻¹` since every row sum of `Θ = Σ tⁿKⁿ` is `(1-t)⁻¹` (`BAK_row_sum`, `KKernel.lean:124`, `Kⁿ` row sums 1 as `:169`); then `Θ̊ = γ⁻¹∫e^{-ετ}(kBA - L^{-d})dτ` (`e^{-ετ}` kept on the `L^{-d}` piece) | `t∈(0,1)`; `t=0`: `Θ̊ = 1_{a=0} - L^{-d}` | numeric id. error ≤ 5.3e-14 (below) |
| 11 | P8 shape | `(g²+e)⁻¹(n+1)^{-(d-2)}`, no exponential factor; `L^{-d} ≤ L^{-(d-2)} ≤ (d/2+1)^{d-2}(n+1)^{-(d-2)}` (`p5h_Linv_le :178`, `p5h_Linv_d_le :192`) | `|a| ≤ dL/2` (`p5h_zdistD_le :167`) | `d=3`: `(d/2+1)^{d-2} = 2.5` |
| 12 | constants at `t=0` | P5: `C ≥ Λ²+1`; P8: `C ≥ (Λ²+1)(1+(d/2+1)^{d-2})` (`p5h_zero5 :700`, `p5h_zero8 :1070`); `BATheta … 0 = 1` | | `d=3, Λ=10`: `101 · 3.5 = 353.5` |
| 13 | ε-regimes | `ε≥1`, `L⁻²≤ε<1`, `ε<L⁻²`, `n=0` (`p5h_head_shape :384`) | by `ε`, not by `e ≷ g²` (Fable F5); `ε → ∞` as `t→0` is in regime `ε≥1` | all three `ε` regimes occur in the instance below |
| 14 | dependence | `C,c` on `(d,Λ,κ)` only; `L,g,E,m,t` after | `kBA_le`, `kBA_gap` uniform in `L≥3`, `g≤Λ`, `E`, `m` with `BAReal` | no `W`, no `ilambda`, no flow window |
| 15 | DECISIONS §29 (1) | statement has `0 ≤ t < 1`; `t=0` separate; `t>0` for `γ>0` | | ok |
| 16 | §29 (2) | no window `1 - ilambda²/L²` appears (deterministic, `g ≤ Λ` fixed) | | n/a |
| 17 | §29 (3) | no `W`; only `3 ≤ L`; no `L^d ≤ W^K` | | n/a |
| 18 | §29 (4) | `∀ L ≥ 3` (not `∀ᶠ`), constants uniform; `kBA_le/gap` are `∀ L ≥ 3` | | ok |

### (ii) One concrete nondegenerate instance

Data (`BA/MFixedPoint.lean:849-900`): `d=3`, `w = 1.2i`, `m_S = L⁻³tr(gΨ - w)⁻¹`, `z_S = w - m_S`, `t₀ = Im m_S/(Im m_S + Im z_S)`, `E = (t₀ Re z_S - (1-t₀) Re m_S)/√t₀`, `m₀ = m_S/√t₀`, `g₀ = √t₀ g` (the flow point `P`; `(L,g)=(4,10)` is the ticket's instance, `(6,1)` the preflight one). `Ψ` = adjacency of `Z_L³`. Then `κ = Im m₀`, `Λ ≥ g₀`. Hypotheses checked numerically: `3 ≤ d`, `3 ≤ L`, `0<g₀≤Λ`, `BAReal` (self_m residual), `0 ≤ t < 1`, `σ₁≠σ₂`, `K` doubly stochastic. Bounds: `Θ_t(0,a) = [(1-tK)⁻¹]_{0a}`, `Bparam`, `ellT`, P8 right side `(g₀²+1-t)⁻¹(n+1)^{-(d-2)}`; the "max ratio" columns are the best constants `C` over all `a` (P5 for `c = 0.1, 0.5, 2/d`), so the witnesses `C` are about 3 to 30 (L=6) and 4 to 185 (L=4, Λ=10), not astronomical. Script: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2337/pf.py` (numpy 2.0.2, scipy 1.13.1; dense `Z_L³` matrices, `quad` for the Laplace check, grids for `LGConv*'`).

Command: `cd .../scratchpad/T2337 && python3 pf.py`. Output (verbatim):

```
== L=4, g(flow)=10.0: g0=4.672337, E=0.000000, m0=0.000000+0.560680j, kappa=Im m0=0.560680, self_m residual=1.11e-16
   K row sum err=9.99e-16, symmetric err=5.00e-16, K_00=|m0|^2 err=1.67e-16, min K=7.89e-05
   t=0.500000 eps=(1-t)/(t g0^2)=0.04581 L^-2=0.0625 ell=4 Th(0,a=(1,0,0))=6.633342e-04 Bparam=5.364067e-02 | max ratio P5 (c=.1,.5,2/d)=(16.205,16.205,16.516) | P8: max|Th0|/bound=30.8708, Th0 id err=6.9e-18
   t=0.900000 eps=(1-t)/(t g0^2)=0.00509 L^-2=0.0625 ell=4 Th(0,a=(1,0,0))=1.596973e-02 Bparam=1.790491e-01 | max ratio P5 (c=.1,.5,2/d)=(8.987,10.508,13.492) | P8: max|Th0|/bound=100.0332, Th0 id err=4.4e-16
   t=0.937500 eps=(1-t)/(t g0^2)=0.003054 L^-2=0.0625 ell=4 Th(0,a=(1,0,0))=3.870113e-02 Bparam=2.728381e-01 | max ratio P5 (c=.1,.5,2/d)=(6.867,8.452,10.853) | P8: max|Th0|/bound=118.6471, Th0 id err=6.7e-16
   t=0.984375 eps=(1-t)/(t g0^2)=0.0007271 L^-2=0.0625 ell=4 Th(0,a=(1,0,0))=4.278783e-01 Bparam=1.022887e+00 | max ratio P5 (c=.1,.5,2/d)=(3.073,4.643,5.961) | P8: max|Th0|/bound=184.6364, Th0 id err=1.5e-14
== L=6, g(flow)=1.0: g0=0.529967, E=0.000000, m0=0.000000+0.635960j, kappa=Im m0=0.635960, self_m residual=2.22e-16
   K row sum err=1.89e-15, symmetric err=2.84e-16, K_00=|m0|^2 err=3.89e-16, min K=4.35e-07
   t=0.500000 eps=(1-t)/(t g0^2)=3.56 L^-2=0.02778 ell=1 Th(0,a=(1,0,0))=3.025260e-02 Bparam=6.495751e-01 | max ratio P5 (c=.1,.5,2/d)=(0.976,6.156,27.591) | P8: max|Th0|/bound=0.9760, Th0 id err=0.0e+00
   t=0.900000 eps=(1-t)/(t g0^2)=0.3956 L^-2=0.02778 ell=1.676 Th(0,a=(1,0,0))=1.240420e-01 Bparam=1.359099e+00 | max ratio P5 (c=.1,.5,2/d)=(0.613,2.493,6.101) | P8: max|Th0|/bound=0.6059, Th0 id err=6.9e-17
   t=0.972222 eps=(1-t)/(t g0^2)=0.1017 L^-2=0.02778 ell=3.18 Th(0,a=(1,0,0))=2.637977e-01 Bparam=1.786665e+00 | max ratio P5 (c=.1,.5,2/d)=(0.542,1.457,2.335) | P8: max|Th0|/bound=0.5180, Th0 id err=9.4e-16
   t=0.995370 eps=(1-t)/(t g0^2)=0.01656 L^-2=0.02778 ell=6 Th(0,a=(1,0,0))=1.104455e+00 Bparam=2.751349e+00 | max ratio P5 (c=.1,.5,2/d)=(0.867,1.579,2.027) | P8: max|Th0|/bound=0.4879, Th0 id err=5.3e-14
Laplace (L=4,t=1/2,a=(1,0,0)): gamma^-1 int e^(-eps tau) kBA = 0.0006633342; (1-tK)^-1_0a = 0.0006633342
LGConvA' Lambda=0.5: max (1/min(e,gamma) in its regime)*(g^2+e) = 2.2470 <= C=3+2L^2=3.500
LGConvA' Lambda=1.0: max (1/min(e,gamma) in its regime)*(g^2+e) = 2.9952 <= C=3+2L^2=5.000
LGConvA' Lambda=3.0: max (1/min(e,gamma) in its regime)*(g^2+e) = 10.9760 <= C=3+2L^2=21.000
LGConvA' Lambda=10.0: max (1/min(e,gamma) in its regime)*(g^2+e) = 101.7677 <= C=3+2L^2=203.000
LGConvB/C' violations=0; max (n/ell)/((d/2) eps L^2) over eps>=L^-2 = 1.0000 (<=1 required)
```

Reading of the output (every figure above): the ticket's instance (`d=3`, `L=4`, `g₀ = 4.672337`, `E = 0`, `κ = Im m₀ = 0.560680`, `Λ = 10` or any `Λ ≥ 4.68`, `t = 1/2`, `a = (1,0,0)`, `n = 1`, `σ=(+,-)`): `Θ_{1/2}(0,a) = 6.633342e-04 ≤ C·5.364067e-02·e^{-c/4}` already for `C = 0.0124·e^{c/4}`; the regime is `ε = 0.04581 < L⁻² = 0.0625` (so `ℓ = L = 4`, the zero-mode regime). The `L=6` rows cover `ε = 3.56 ≥ 1` (`t = 0.5`), `L⁻² ≤ ε < 1` (`t = 0.9, 0.972`) and `ε < L⁻²` (`t = 0.995`). Laplace representation and the P8 identity `Θ̊ = Θ - L^{-d}(1-t)⁻¹` agree with the definitional double sum to 5.3e-14. `Λ`-dependence of P8 (`185` at `g₀² = 21.8`) is real, as in the `BA/FlowPins.lean` section-3 header remark (numerics (b.4)).

External hypotheses: none (route is unconditional; `kBA_le`/`kBA_gap`/`BATheta_eq_laplace_kBA` are merged theorems; `BAProp5mixed/8mixed` are proved, not assumed).

### Verdicts
- `BAProp5mixed` / `baProp5mixed_holds`: PASS (exponents close; `CA = 3+2Λ²` for `γ = t g²`; `c = min(c'/2, 2/d)`).
- `BAProp8mixed` / `baProp8mixed_holds`: PASS (identity row 10 exact; `t=0` constants row 12).
- Overall: PASS. Lean-side points for 1b (not obstacles): (1) `BATheta … false true` needs `unfold BATheta; rw [BAMss_mp_eq]` since only `BATheta_pm_eq` (true,false) exists (`KKernel.lean:107`); (2) `Θ̊` needs row sums of `Θ` for every row (`BAK_row_sum` for all `a`, or `BAK_shift`); (3) `LGConvA` is re-proved with `CA = 3+2Λ²` (the merged `lg_convA` is stated with `lgGam` and cannot be reused); `lg_convB/C` likewise restated for generic `γ` with `0<γ ≤ g²`.

## (b) Script output — stage 1b (written Thu Oct  8 14:17:48 UTC 2026)

```
$ git log --oneline main..t/T2337 ; git status --short ; git rev-parse --short HEAD
002430d T2337: BA/Prop5 section 3 (instances, docstrings)
419be51 T2337: BA/Prop5 section 2 (property 8, mixed charges)
0c46bf3 T2337: BA/Prop5 section 1 (property 5, mixed charges)
002430d

$ wc -l RBM3D/BA/Prop5.lean   (stop size 1600)
    1479 RBM3D/BA/Prop5.lean

$ git diff --stat main...t/T2337
 RBM3D/BA/Prop5.lean | 1479 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1479 insertions(+)

$ lake build RBM3D.BA.Prop5 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3743 jobs).

$ lake env lean RBM3D/BA/Prop5.lean ; echo exit=$?   (no output = no warnings or errors)
exit=0

$ tail -3 fullbuild.log   (full `lake build` in the worktree, run before the last commit; RBM3D.lean there does not yet import Prop5)
non-vacuity certificates: 0 of 130 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4145 jobs).
exit=0

$ lake env lean ax.lean   (import RBM3D.BA.Prop5; #print axioms of the targets and instances)
'RBM.BA.baProp5mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProp8mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop5_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop8' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop8_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop8_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0

$ registry pre-check: lake env lean reg.lean   (import RBM3D; import RBM3D.BA.Prop5; #assert_rbm_axioms), head and tail
exit=0
axiom audit: 10136 theorems, 3015 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
   [...]
premises found by scanning: 141 (borrowed 1, owed 80, structural 41, refuted 6, superseded 13).
registry: 2 borrowed + 128 owed + 106 structural + 7 refuted + 14 superseded; 116 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
non-vacuity certificates: 0 of 130 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ same without Prop5 (reg0.lean: import RBM3D; #assert_rbm_axioms), diff of the outputs except the first audit line
exit=0
diff: empty
reg0.out:axiom audit: 10128 theorems, 3013 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
reg1.out:axiom audit: 10136 theorems, 3015 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).

$ check-file equality (a): the two pins, whitespace-normalised, check file vs RBM3D/BA/Prop5.lean
BAProp5mixed equal: True
BAProp8mixed equal: True

$ check-file equality (b): lake env lean scratch_check.lean | tail -1 ; exit   (check file + import RBM3D.BA.Prop5 + the two examples)

example : RBM.BA.T2337Check.T2337_baProp5mixed_holds := RBM.BA.baProp5mixed_holds
example : RBM.BA.T2337Check.T2337_baProp8mixed_holds := RBM.BA.baProp8mixed_holdsexit=0
0

$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/BA/Prop5.lean
grep exit=1 (1 = none)

$ name-clash grep outside Probe/ (files other than RBM3D/BA/Prop5.lean)
grep exit=1 (1 = no clash)
$ public declarations of RBM3D/BA/Prop5.lean (all others are private, prefix baP5)
49:namespace RBM.BA
56:def BAProp5mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
66:def BAProp8mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
928:theorem baProp5mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp5mixed d Λ κ := by
959:example (d : ℕ) (Λ κ : ℝ) : BAProp5mixed d Λ κ := baProp5mixed_holds d Λ κ
1389:theorem baProp8mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp8mixed d Λ κ := by
1414:example (d : ℕ) (Λ κ : ℝ) : BAProp8mixed d Λ κ := baProp8mixed_holds d Λ κ
1422:namespace Prop5Inst
1428:theorem inst_prop5 : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
1441:theorem inst_prop5_large_eps : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ zdistD 3 4 (![2, 1, 0] : Zd 3 4) = 3 ∧
1452:theorem inst_prop8 : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
1462:theorem inst_prop8_large_eps : ∃ C : ℝ, 0 < C ∧
1470:theorem inst_prop8_zero : ∃ C : ℝ, 0 < C ∧

$ git log -1 --format=%h (source of the port, in-project files): Prop5Hold.lean, LaplaceGauss.lean, KHeat.lean
f40d8ca
315e65e
8a6c908
```

Section-commit sizes (stop rule: over 1600 at a section boundary), each from `wc -l` run in the same command as the commit (same file content):
```
0c46bf3 (14:05:40 UTC, `date -u`)  section 1, property 5:  961 RBM3D/BA/Prop5.lean
419be51 (14:07:57 UTC, `date -u`)  section 2, property 8:  1416 RBM3D/BA/Prop5.lean
002430d (14:13:12 UTC, `date -u`)  section 3, instances:   1479 RBM3D/BA/Prop5.lean
```

Target statements, extracted from `RBM3D/BA/Prop5.lean` by script (`python3 -I extract.py`):
```lean
def BAProp5mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ a : Zd d L,
          ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

def BAProp8mixed (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, σ₁ ≠ σ₂ → ∀ a : Zd d L,
          ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

theorem baProp5mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp5mixed d Λ κ

theorem baProp8mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp8mixed d Λ κ

-- instance (P5)
theorem inst_prop5 : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![1, 0, 0]‖
      ≤ C * Bparam 3 4 P.g0 (1 / 2) (zdistD 3 4 (![1, 0, 0] : Zd 3 4))
        * Real.exp (-c * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 2)) := by
  obtain ⟨C, hC, c, hc, H⟩ :=
    baProp5mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, c, hc, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0]⟩

-- instance (P8)
theorem inst_prop8 : ∃ C : ℝ, 0 < C ∧ (![1, 0, 0] : Zd 3 4) ≠ 0 ∧
    zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 ∧
    ‖BATheta0 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![1, 0, 0]‖
      ≤ C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (((zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := baProp8mixed_holds 3 10 P.m0.im (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, by decide, by decide,
    H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num)
      true false (by decide) ![1, 0, 0]⟩
```

Regime of the instances (python, `g0 = 4.672337` from the preflight output above, `L = 4`):
```
t=0.5 eps=(1-t)/(t g0^2)=0.0458  L^-2=0.0625
t=0.01 eps=(1-t)/(t g0^2)=4.5349  L^-2=0.0625
```

Narrative (facts from the files and the tool log above).
- Port. `RBM3D/BA/Prop5.lean` ports the merged band file `RBM3D/Propagator/Prop5Hold.lean` (last commit touching it: f40d8ca) with the ticket's substitutions: `kProd d L τ a ↦ kBA d L g E m τ a`, `lgGam d g t ↦ baP5Gam g t = t * g ^ 2`, `lgEps ↦ baP5Eps = (1-t)/baP5Gam`, `Theta_eq_laplace_prod ↦ BATheta_eq_laplace_kBA` (`baP5_theta_eq`), `kProd_le ↦ kBA_le`, `kProd_gap ↦ kBA_gap`. The generic real-algebra lemmas (`shape_*`, `head_shape`, `exp_bulk`, `exp_zero`, `Ld_piece`, ...) were copied by `sed` renames (`p5h_ ↦ baP5_`); the kernel-dependent lemmas take hypotheses specialised to `(L, g, E, m, a, t)` and `BASelf d L g E m` instead of the band's `∀ L` hypotheses. No RBM1D or RBM2D file was read or imported for this port, so there is no RBM1D/RBM2D diff-stat.
- Restated conversions. `baP5_convA` is proved afresh for `γ = t g²` with `C_A = 3 + 2Λ²` (preflight row 5). `baP5_sqrt_eps_inv_le`, `baP5_ell_inv_le`, `baP5_convB`, `baP5_convC` are `LaplaceGauss.lean:124-204` (last commit 315e65e) with `lgGam ↦ baP5Gam` by `sed`; they use only `0 < γ ≤ g²` (`baP5_gam_le`), as preflight rows 6, 7 said.
- Mixed charges. `baP5_Theta_mixed`: `BATheta … σ₁ σ₂ = BATheta … true false` for `σ₁ ≠ σ₂` (`BAMss_pm_eq`, `BAMss_mp_eq`; the `false true` case is `unfold BATheta; rw [BAMss_mp_eq, BAMss_pm_eq]`, preflight Lean-side point (1)). For `0 < t < 1`, `Θ_t(0,a)` is the real number `γ⁻¹ ∫ e^{-ετ} kBA ≥ 0` (`BATheta_eq_laplace_kBA`, `kBA_basic`), so `‖Θ‖ = Θ` and the band's reduction `norm_Theta_apply_le` is not used. `t = 0`: `baP5_Theta_zero` (`BATheta … 0 = 1`).
- Property 8. `Θ̊_t(0,a) = Θ_t(0,a) - L^{-d}(1-t)⁻¹` (`baP5_Theta0_apply_eq`) needs the row sums of `Θ` for every row. Preflight Lean-side point (2) named `BAK_row_sum`/`BAK_shift`; the file instead copies the private Neumann-series lemmas of `BA/KHeat.lean` (`KHeat_pow_le_one`, `KHeat_summable_t`, `KHeat_neumann`, `KHeat_Theta_eq`, here `baP5_pow_le_one`, `baP5_summable_t`, `baP5_neumann`, `baP5_Theta_eq`) and sums `Σ_b Σ_n tⁿ (Kⁿ)_{ab}` with `BAK_pow_row_sum`; no translation invariance of `Θ` is used. The rest (`theta0_eq`, `head0_le`, `tail0_le`, `core8`, `zero8`) is the band's structure.
- Constants. P5: `C = baP5Ch + (1+C_G) e^{cd/2} + (Λ²+1)`, `c = min(c'/2, 2/d)` (`c ≤ c'/2`, `c d ≤ 2`), with `(C_K, c_K)` from `kBA_le`, `(C_G, c_G)` from `kBA_gap`, `(C_B, c')` from `lg_bulk`, so `(C, c)` depend on `(d, Λ, κ)` only. P8: `C = baP5Ch + C_A (d/2+1)^{d-2} + C_G C_A (1+1/c_G)(d/2+1)^{d-2} + (Λ²+1)(1+(d/2+1)^{d-2})`.
- Instances (`Prop5Inst`): `d = 3`, `L = 4`, `Λ = 10`, `κ = P.m0.im`, `(g, E, m) = (P.g0, P.E, P.m0)` with `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0` and `P.g0_le : P.g0 ≤ 10` (`MFixedPointInst`, the data of `KKernelInst`); `t = 1/2` (`ε = 0.0458 < L⁻² = 0.0625`, the zero-mode regime), `t = 1/100` (`ε = 4.5349 ≥ 1`), `t = 0` (P8). Both charge orders `(true,false)` and `(false,true)` occur; `a = ![1,0,0]` (`|a| = 1`) and `![2,1,0]` (`|a| = 3`) are proved by `decide`. `C`, `c` stay existential as in the statements. No other gate's pin is a hypothesis.
- Special cases. `baProp5mixed_holds`, `baProp8mixed_holds` are the `σ₁ ≠ σ₂` cases only, not `BAProp5`/`BAProp8`; those stay owed (registry output identical with and without this file, see (b)). No merged file and not `RBM3D.lean` changed; the hub adds `import RBM3D.BA.Prop5` after the last import line.

## (c) Verified Mathlib names (`#check` in this session on `import RBM3D.BA.Prop5`; one line each, cut at 118 columns)
```
integral_comp_mul_left_Ioi : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (g : ℝ → E)
integrableOn_exp_mul_Ioi : ∀ {a : ℝ}, a < 0 → ∀ (c : ℝ), IntegrableOn (fun x => Real.exp (a * x)) (Set.Ioi c) volume
integral_exp_mul_Ioi : ∀ {a : ℝ}, a < 0 → ∀ (c : ℝ), ∫ (x : ℝ) in Set.Ioi c, Real.exp (a * x) = -Real.exp (a * c) / a
setIntegral_union : ∀ {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]
setIntegral_nonneg : ∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : Measure X} {f : X → ℝ} {s : Set X},
setIntegral_mono_on : ∀ {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]
setIntegral_mono_set : ∀ {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]
Set.Ioc_union_Ioi_eq_Ioi : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α},
Summable.tsum_finsetSum : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCommMonoid α]
tsum_geometric_of_lt_one : ∀ {r : ℝ}, 0 ≤ r → r < 1 → ∑' (n : ℕ), r ^ n = (1 - r)⁻¹
summable_geometric_of_lt_one : ∀ {r : ℝ}, 0 ≤ r → r < 1 → Summable fun n => r ^ n
Complex.ofReal_sum : ∀ {α : Type u_1} (s : Finset α) (f : α → ℝ), ↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)
Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
Finset.card_univ : ∀ {α : Type u_1} [inst : Fintype α], Finset.univ.card = Fintype.card α
ZMod.card : ∀ (n : ℕ) [inst : Fintype (ZMod n)], Fintype.card (ZMod n) = n
div_le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : CommGroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀]
div_lt_one : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α},
le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}
Ring.inverse_mul_cancel : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] (x : M₀), IsUnit x → Ring.inverse x * x = 1
mul_eq_one_comm : ∀ {M : Type u_1} [inst : MulOne M] [IsDedekindFiniteMonoid M] {a b : M}, a * b = 1 ↔ b * a = 1
Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N}
Real.pow_div_factorial_le_exp : ∀ (x : ℝ), 0 ≤ x → ∀ (n : ℕ), x ^ n / ↑n.factorial ≤ Real.exp x
integral_sub : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G]
norm_integral_le_of_norm_le : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G]
```
Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates
- T2337a (Lean/paper, by design of the ticket): `BAProp5mixed`/`BAProp8mixed` restrict `lem_propTH` properties 5 and 8 (`1_2:1124-1167`) to `σ₁ ≠ σ₂`; the paper states them for all charges. `σ₁ = σ₂` (`BAProp5s` branch) and the bundle `BAProp5to8` are the P8 ticket's work.
- T2337b (note, not a Lean/paper difference): the BA diffusion constant is `γ = t g²` (`kBA` is the heat kernel in time `τ = g² s`); the band file has `γ = t g²/(1 + 2dg²)`. The `1 + 2dg²` factor enters the band through the unfolds of `lgGam` (`p5h_gam_pos`, `Prop5Hold.lean:84`; `lg_gam_pos`, `lg_gam_le`, `lg_convA` in `LaplaceGauss.lean`); `C_A = 3 + 2Λ²` replaces the band's `3 + 4dΛ² + 2Λ²`.
- Open: the `Λ`-dependence of the P8 constant is real (preflight numerics: 185 at `g₀² = 21.8`); no action for this ticket.
- No `(a′)` section: no mistake in section (a) was found that changes a verdict.
