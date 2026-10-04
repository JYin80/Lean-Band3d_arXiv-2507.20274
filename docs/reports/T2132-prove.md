Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 11:49:24 UTC 2026

Scratch scripts: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2132/*.py` (`S=` that directory). Notation: `k=m+1`, `n=dm`, `u=u_j`, `v=u+Δ=u_{j+1}`, `β=(1-v)^{-1}`, `Lp=(L^d)^{m}`, `X=A_j`, `Θ=ThetaN_{u,σ}`, `R_U=𝒰_{u,v}-1-ΔΘ`.

### (i) Exponent table
| # | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `Lp` = #terms of `𝒫` | `(L^d)^m`; d=3,L=5,k=2: 125; instance L=4,k=4: 262144 | `card{a : a 0 = x}`; `Lp ≤ N^m`, `N=(WL)^d`, `W≥1` | equality |
| 2 | mollifier consts `C,c` | `C=(1+40dm)6^{dm}`, `c=1/2` (merged `QopAlgebra_mollifier_props`, `QopAlgebra.lean:511`); m=1: 26136; m=3: 3638048256 | clause 2 `‖ϑ‖≤C(ℓ^d)^{-m}≤C` (`ellT≥1`, `Defs/Params.lean:39`); clause 4 `‖ϑ̇_τ‖≤C(1-τ)^{-1}(ℓ^d)^{-m}` | empirical `sup(1-t)‖ϑ̇‖ℓ^{dm}`=1.21 (d=3,m=1), 9.52 (m=2): slack >10³ |
| 3 | Lipschitz `Vd` | `‖ϑ_u-ϑ_v‖ ≤ CβΔ` | clause 4 + mean-value on `[u,v]⊂[0,1)` (differentiable on `Ico 0 1`), `(1-τ)^{-1}≤β` | instance max ratio `3.1e-4` vs `C` |
| 4 | **Taylor const `C₂`** | `‖ϑ_v-ϑ_u-Δϑ̇_u‖ ≤ C₂β²Δ²`, `C₂=C₂''/2`, `(1-t)²‖ϑ̈‖≤C₂''ℓ^{-dm}≤C₂''` | **not a clause of `STMollifierProps`** (clauses: sum, sup, differentiable, `‖ϑ̇‖`). Merged ϑ: `ϑ=φ_a(U(t))`, `‖U'‖≤U/(2(1-t))` (merged `qaU_deriv`), `‖U''‖≤(5/4)U/(1-t)²` (r=y-1, y'=r/(2(1-t)), y''=3r/(4(1-t)²), r≤y), `φ''=φ[(S-n m₁)²-n(z₃/z-m₁²)]`, `m₁=z₂/z`, `u‖φ'‖≤(1+40n)/z^n` (merged `qa_core`), `1/z^n≤6^nℓ^{-n}` (merged `qa_Zinv_le`). So `C₂''≤(Ĉ/4+5(1+40n)/4)6^n`, `Ĉ=8/e²+2n²K₁²+nK₃`, `K₁=sup u z₂/z` (Lean has 40), `K₃=sup u²z₃/z` (**new lemma**) | empirical `sup(1-t)²‖ϑ̈‖ℓ^{dm}`: 0.345 (d=3,m=1), 1.36 (m=2), 0.593 (d=4,m=1); `K₁`=1.0, `K₃`=2.0 (numeric) |
| 5 | `Ust=uStepC k Δ v` (merged `GridDriftN.lean:283`) | `kΔ²β²+((1+Δβ)^k-1-kΔβ)`, `O(Δ²β²)` | `0≤u`, `v<1`, `‖A‖≤Mk` (`gdn_Ugen_step_le`) | exact |
| 6 | `S=stepErrN` (merged) | `envConst Δ^{3/2}+kStepC Δ²+Ust(η^{-k}W^{-d(k-1)}+Bk)`, `kStepC` counted `W^dk²L^d` | enters `qStepErrN` times `(1+C·Lp)`; `Lp≤N^m`, poly in `N` | order `Δ^{3/2}` dominates |
| 7 | `qStepErrN d L k u Δ Mk Dm S` (to define) | `(1+C·Lp)S+ΔLp·Dm·CβΔ+2C·Lp·Ust·Mk+Lp·Mk·C₂β²Δ²+ΔLp(kβMk)CβΔ` | terms T1–T4 below; `Mk=lkEnvN`, `Dm=driftEnvN` | order `Δ^{3/2}` (S) and `Δ²` (rest) |
| 8 | `driftEnvN` | `W^dL^d(k·2k²(B_F Bk)+k²B_F²+k(η⁻¹+1)η^{-(k+1)})`, `B_F=η^{-k}+Bk` | `norm_primBil_le` (`HierAlgebra.lean:254`: `W^d n²L^d B_F B_G`), `η≤1`, `W≥1`, `Σ_l≤k` terms, `egt` sum over `L^d` points | RBM2D shape with `W²L²→W^dL^d` |
| 9 | sign of `ℬ₅` | Lean drift `dGridQN=𝒬_uD+[𝒬_u,Θ]X-(𝒫X)ϑ̇_u` | paper `ℬ₅:=-[𝒫∘(𝓛-𝒦)]∂_uϑ` already carries `-` (`3_5:1345`, last term of `zjuii1` `3_5:1315`); merged `QopAlgebra_Qop_hasDerivAt` has `-𝒫(A)ϑ'`. RBM2D #122 fixes the 2D paper's `+`; the 3D paper prints `-`, so no sign delta | — |
| 10 | DECISIONS §29 | (1) `0≤s≤t<1`, `u_j∈[s,t]`, `v=u_{j+1}≤t<1` (merged `gdn_time_facts`); clauses 2,4 and differentiability need `τ∈[0,1)` ✓. (2) `ilambda`: not used. (3) `L^d≤W^K`: not used (only in S3-13b/`STQopNorm`). (4) `_at` forms: hypotheses at size index `n` only. `|E n|<2`. `NeZero k`: avoided by `Fin (m+1)`, `1≤m` (`STQop`/`STPsum` are `m+1`-indexed) | `gridDriftN_at`, `stoppedDuhamelN_at` pattern | — |

Term-by-term algebra (verified numerically below). With `X=A_j`, `𝔼[A_{j+1}|F_j]=𝒰X+ΔD+e`, `‖e‖≤S`, `𝔼[𝒬_vA_{j+1}|F_j]=𝒬_v𝔼[A_{j+1}|F_j]` (linear; integrability from merged `gdn_integrable_loopL`). `𝒬_v𝒰X-𝒰𝒬_uX=𝒰((𝒫X)ϑ_u)-𝒫(𝒰X)ϑ_v` (definition of `𝒬`). With `𝒰=1+ΔΘ+R_U`, `ℬ₄=Θ((𝒫X)ϑ_u)-𝒫(ΘX)ϑ_u` (merged `QopAlgebra_commutator_ThetaN`), `ℬ₅=-(𝒫X)ϑ̇_u`:
`𝒬_v𝔼[A_{j+1}|F_j]-𝒰𝒬_uX-Δ(𝒬_uD+ℬ₄+ℬ₅) = (e-𝒫e ϑ_v) + Δ𝒫D(ϑ_u-ϑ_v) + T1+T2+T3+T4`,
T1=`(𝒫X)(ϑ_u-ϑ_v+Δϑ̇_u)` (**second order**: `Lp·Mk·C₂β²Δ²`), T2=`Δ𝒫(ΘX)(ϑ_u-ϑ_v)` (clause 4: `ΔLp·kβMk·CβΔ`), T3=`R_U((𝒫X)ϑ_u)`, T4=`-𝒫(R_UX)ϑ_v` (clause 2: `C·Lp·Ust·Mk` each). `ℬ₅`'s `∂_uϑ` enters only through T1; `ℬ₄` from the `Θ`-part of `𝒰`. `‖ΘX‖≤kβ_uMk` (row sums of `SΘ`, copy of private `gdn_row_thetaGenMat`). Counts: `𝒫` has `(L^d)^m` terms; drift `W^dk²L^d`.

**Time-regularity decision.** (a) first order only: T1 `≤ Lp·Mk·2CβΔ` per step, so `Σ_{j<K}` = `Lp·Mk·2Cβ(t-s)`, **independent of `K`** (script below: ≥33.05 at the instance for every K), cannot reach `N^{-D_t}`; (a) fails. (b) closes: row 4, remainders `Δ^{3/2}` (S) and `Δ²` (rest), sums `O(Δ^{1/2})`, `O(Δ)` with poly(`N`) prefactors `(1+C·Lp)`. Recommended form: targets 2–3 take explicit `ϑ` with `STMollifierProps g C c ϑ` and an explicit hypothesis `QGridA_Taylor2 C₂ ϑ` (the Taylor bound of row 4), plus a discharge lemma for `QopAlgebra_mollifier`; the example discharges it. No change to `STMollifierProps` is needed.

### (ii) Concrete instance
Command: `python3 $S/onestep.py` (d=3, L=5, W=1, k=2, g=1, σ=(+,-), μ_i=1, merged mollifier m=1, `A` random 125×125, `Mk=‖A‖_max`; `ok` = `‖R‖_max ≤ qStepErrN` with C=26136, `C₂=0.35`≥ the 0.345 sup, `S=0,D=0`)
```
N=125 Lp=125.0 C=(1+40dm)6^dm=26136 Mk=3.934
u=0.5 D=0.01: |exact|=6.825e-03 |D(B4+B5)|=6.636e-03 |R|=1.970e-04 |R|/D^2=1.970 | sumzero A: |exact|=1.6e-15 PA0=1.2e-14 | ok=True
u=0.5 D=0.001: |exact|=6.654e-04 |D(B4+B5)|=6.636e-04 |R|=1.927e-06 |R|/D^2=1.927 | sumzero A: |exact|=1.7e-15 PA0=1.2e-14 | ok=True
u=0.9 D=0.01: |exact|=4.043e-02 |D(B4+B5)|=3.572e-02 |R|=4.707e-03 |R|/D^2=47.067 | sumzero A: |exact|=6.7e-16 PA0=1.0e-14 | ok=True
u=0.9 D=0.001: |exact|=3.615e-03 |D(B4+B5)|=3.572e-03 |R|=4.264e-05 |R|/D^2=42.641 | sumzero A: |exact|=7.2e-16 PA0=1.0e-14 | ok=True
identity u=0.5 D=0.01: |R-(T1+T2+T3+T4)|=8.8e-15; max|T1|=6.9e-05 |T2|=2.1e-04 |T3|=2.8e-04 |T4|=7.4e-04
identity u=0.5 D=0.001: |R-(T1+T2+T3+T4)|=6.5e-15; max|T1|=6.8e-07 |T2|=2.1e-06 |T3|=2.8e-06 |T4|=7.3e-06
identity u=0.9 D=0.01: |R-(T1+T2+T3+T4)|=7.3e-15; max|T1|=7.4e-04 |T2|=2.7e-03 |T3|=3.3e-03 |T4|=1.1e-02
identity u=0.9 D=0.001: |R-(T1+T2+T3+T4)|=7.0e-15; max|T1|=7.0e-06 |T2|=2.6e-05 |T3|=3.0e-05 |T4|=1.0e-04
```
(`exact=𝒬_{u+Δ}𝒰A-𝒰𝒬_uA`, `R=exact-Δ(ℬ₄+ℬ₅)`: `R/Δ²` is stable under Δ→Δ/10, so `R=O(Δ²)`; `ℬ₄+ℬ₅` carries the whole first-order part (`|exact|-|Δ(ℬ₄+ℬ₅)|`=O(Δ²)); for sum-zero `A=𝒬_uA`, `𝒫A=0`, so `ℬ₄=ℬ₅=0` and `exact=0`, as `QopAlgebra_UN_sumZero` predicts.) Same run, Taylor and Lipschitz maxima of the mollifier (`grep -o` of the same output):
```
u=0.5 D=0.01 Taylor max=2.25e-06 Lip max=3.26e-04
u=0.5 D=0.001 Taylor max=2.23e-08 Lip max=3.24e-05
u=0.9 D=0.01 Taylor max=2.42e-05 Lip max=8.79e-04
u=0.9 D=0.001 Taylor max=2.31e-07 Lip max=8.57e-05
```
(Taylor `∝Δ²`, Lipschitz `∝Δ`: row 4 is needed, rows 3,4 hold.) Constants: `python3 $S/taylor2.py` (analytic `ϑ̈` checked against finite differences; sup over g∈[1e-3,100], L∈[3,300], 1-t∈[1e-8,0.9], all S), `python3 $S/uderiv.py`, `python3 $S/zmom.py`:
```
fd check d1: 0.0009437297411943324 0.0009437297381937273  d2: 0.0009919502719224482 0.0009919490285275803
d=3 m=1: sup (1-t)|th'|/ell^-dm=1.21  sup (1-t)^2|th''|/ell^-dm=0.3446  sup (1-t)^2|th''|=0.0293  C=(1+40dm)6^dm=26136
d=3 m=2: sup (1-t)|th'|/ell^-dm=9.522  sup (1-t)^2|th''|/ell^-dm=1.356  sup (1-t)^2|th''|=0.01108  C=(1+40dm)6^dm=11244096
d=4 m=1: sup (1-t)|th'|/ell^-dm=2.547  sup (1-t)^2|th''|/ell^-dm=0.5926  sup (1-t)^2|th''|=0.02198  C=(1+40dm)6^dm=208656
sup (1-t)|U'|/U = 0.4664  (claim <= 1/2);  sup (1-t)^2|U''|/U = 0.28  (claim <= 5/4)
sup u*z2/z = 0.9999915025750584  sup u^2*z3/z = 1.9999884582723073
```
(these are grid values, evidence not proof.) **Endpoint instance** for targets 2–3: merged `sz0` (`sz0_values`: d=3, L_0=4, W_0=32, lam_0=1/64, size_0=2097152) with `GridDriftNCheck` data E≡0, s≡1/10, t≡1/2, K≡4, n=0, j=0, k=4 (m=3), σ=(+,-,+,-) alternating, mollifier `QopAlgebra_mollifier 3 4 3 (1/64)`, `Bk` from merged `GridDriftN_exists_envelope`. Command `python3 $S/instance.py`:
```
Delta,u_j,u_{j+1} = 0.1 0.1 0.2
{'E_lt_2': True, 's_ge_0': True, 's_le_t': True, 't_lt_1': True, 'K_ne_0': True, 'j_lt_K': True, 'two_le_k': True, 'u_ge_0': True, 'v_lt_1': True, 'L_ge_3': True, 'g_pos': True, 'W_ge_1': True, 'alternating': True, 'size': True}
m=k-1= 3  n=dm= 9  C=(1+40dm)6^dm= 3638048256  c=1/2   Lp=(L^d)^(k-1)= 262144
instance mollifier: max |th_v-th_u-D th'_u|/(beta^2 D^2)=2.060e-04;  max |th_v-th_u|/(beta D)=3.148e-04 (clause-4 allows C=3638048256);  sup (1-t)^2|th''| on [u,v]=4.993e-04
K=         4: K*Lp*Mk_low*2*C*1*Delta = 33.0505  (= Lp*Mk_low*2*C*(t-s), independent of K; Mk_low=4.332e-14)
K=      4000: K*Lp*Mk_low*2*C*1*Delta = 33.0505  (= Lp*Mk_low*2*C*(t-s), independent of K; Mk_low=4.332e-14)
K=4000000000: K*Lp*Mk_low*2*C*1*Delta = 33.0505  (= Lp*Mk_low*2*C*(t-s), independent of K; Mk_low=4.332e-14)
```
(`Mk_low=(1-s)^{-k}W^{-d(k-1)}` is a valid lower bound of `lkEnvN` at every grid step, `β≥1`, so the first-order-only sum is ≥33.05 for every K.) No hypothesis is external: the mollifier clauses are the proved `QopAlgebra_mollifier_props`, `Bk` is proved to exist; the Taylor hypothesis is discharged by the new lemma for the merged ϑ, so no limit computation applies.

### Verdicts
- **Target 1 (definitions): PASS.** Index `Fin (m+1)` (no `NeZero k`); `Lp=(L^d)^m`, `W^d` in `lkEnvN/driftEnvN`, `qStepErrN` as row 7. Sign of `ℬ₅`: Lean `-(𝒫X)ϑ̇`, equal to the paper's `ℬ₅` as printed; no #122-type delta. Paper-delta candidates: T2132a (drift in split form `𝒬_uD+ℬ₄+ℬ₅` vs the paper's `𝒬_u(ΣB_k)`; equal since `𝒫ℬ₄=0` by `QopAlgebra_ThetaN_sumZero`, `𝒫ℬ₅=0` by `QopAlgebra_Psum_deriv`), T2132b (second-order Taylor of ϑ used; paper's `eq:derv_Theta` gives first order only), T2132c (`Fin (m+1)` indexing).
- **Target 2 (`gridDriftQN`): PASS under route (b)** (explicit `QGridA_Taylor2` hypothesis, discharged for `QopAlgebra_mollifier`); **FAIL under route (a)** (first-order MVT remainder is K-independent, ≥33.05 at the instance). Needs new lemmas: `K₃`-type bound `u²z₃≤c z`, `‖ϑ̈‖` bound for the merged ϑ.
- **Target 3 (`stoppedDuhamelQN`): PASS** (pure algebra: merged `GridDuhamelN_Ugen_duhamel_telescope`, `GridDuhamelN_Ugen_comp`, `GridDuhamelN_Ugen_add`; needs `|E|≤2`, `0≤u_i<1` for `i≤m∧τ≤K`, `u_K=t<1`).

## (a′) Preflight corrections — Sun Oct  4 12:22:56 UTC 2026
Two refinements of rows 3–4 of (a); no verdict changes (all three verdicts stand).
1. Row 3: `STMollifierProps` clause 3 is `DifferentiableOn ℝ _ (Set.Ico 0 1)`, but clause 4 bounds `deriv` (two-sided); at `t = 0` the one-sided derivative can differ, so the Lipschitz step needs `DifferentiableAt` at every `t ∈ [0,1)`: hypothesis `hdiff` of `QGridA_gridDriftQN_of`, supplied for the merged `ϑ` by the public `QopAlgebra_mollifier_differentiableAt`.
2. Row 4: Lean does not use `1/z^n ≤ 6^n ℓ^{-n}` but `z ≥ 1` (the `y = 0` term); `u z₂ ≤ 40 z`, `u² z₃ ≤ 160 z` follow from `x e^{-x} ≤ 2 e^{-x/2}`, `x² e^{-x} ≤ 8 e^{-x/2}` and `z(u/2) ≤ 20 z(u)`; `|u_t''| ≤ (3/4) u_t (1-t)⁻²` (not `5/4`); the Taylor constant is `C₂ = 1000 (1 + d m)²`.

## (b) Script output
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2132`, branch `t/T2132`, commit `b28c8be`, `RBM3D/Induction/QGridA.lean` (2318 lines); `date -u` when this section was generated: Sun Oct  4 12:22:56 UTC 2026.
**b.1** `lake build RBM3D.Induction.QGridA 2>&1 | tail -1`; then `lake env lean RBM3D/Induction/QGridA.lean` (the file ends with `#print axioms` of every target), grouped by axiom set:
```
Build completed successfully (3769 jobs).
[propext, Classical.choice, Quot.sound]: aTrueQN, dGridQN, aFrozQN, martIncQN, rGridQN, lkEnvN, driftEnvN, qStepErrN, qErrQN, QGridA_Taylor2, QGridA_mollifier_taylor2, QGridA_condExp_aTrueQN, QGridA_gridDriftQN_of, gridDriftQN, stoppedDuhamelQN, QGridACheck.lam_pos, QGridACheck.gridDriftQN_instance, QGridACheck.stoppedDuhamelQN_instance, QGridACheck.taylor2_instance
[propext]: QGridACheck.sigma4
[propext, Quot.sound]: QGridACheck.sigma4_alternating
```
**b.2 Target 1 (definitions)**, extracted from the file (docstrings omitted; signatures only for `aTrueQN`, `aFrozQN`, `martIncQN`, `rGridQN`, `driftEnvN`; `qErrQN` takes `C C₂ Bk`):
```
def aTrueQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
def dGridQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a =>
    STQop (d := d) ϑ (gridTime s t K n j)
        (fun b => ∑ l ∈ Finset.Icc 3 (m + 1), sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ b) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ b)) a +
      (STQop (d := d) ϑ (gridTime s t K n j)
          (ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) (gridTime s t K n j)
            (AvecN sz E s t K n j σ ω)) a -
        ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma (E n) (σ i)) (gridTime s t K n j)
          (STQop (d := d) ϑ (gridTime s t K n j) (AvecN sz E s t K n j σ ω)) a) -
      STPsum (d := d) (AvecN sz E s t K n j σ ω) (a 0) * deriv (fun τ => ϑ τ a) (gridTime s t K n j)
def aFrozQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
def martIncQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
def rGridQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool) (j : ℕ) (ω : PathΩ sz) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
def lkEnvN (d W : ℕ) (E : ℝ) (k : ℕ) (u Bk : ℝ) : ℝ :=
  (etaT E u)⁻¹ ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) + Bk
def driftEnvN (d L W : ℕ) (E : ℝ) (k : ℕ) (u Bk : ℝ) : ℝ :=
def qStepErrN (d L m : ℕ) (C C₂ u Δ Mk Dm S : ℝ) : ℝ :=
  (1 + C * ((L : ℝ) ^ d) ^ m) * S +
    (Δ * (((L : ℝ) ^ d) ^ m * Dm) * (C * (1 - (u + Δ))⁻¹ * Δ) +
      2 * (C * (((L : ℝ) ^ d) ^ m * (uStepC (m + 1) Δ (u + Δ) * Mk))) +
      ((L : ℝ) ^ d) ^ m * Mk * (C₂ * ((1 - (u + Δ))⁻¹) ^ 2 * Δ ^ 2) +
      Δ * (((L : ℝ) ^ d) ^ m * (((m : ℝ) + 1) * (1 - (u + Δ))⁻¹ * Mk)) *
        (C * (1 - (u + Δ))⁻¹ * Δ))
def qErrQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (C C₂ Bk : ℝ) (j : ℕ) : ℝ :=
  qStepErrN d (sz.L n) m C C₂ (gridTime s t K n j) (gridStep s t K n)
    (lkEnvN d (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk)
    (driftEnvN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) Bk)
    (stepErrN d (sz.L n) (sz.W n) (E n) (m + 1) (gridTime s t K n j) (gridTime s t K n (j + 1))
      (gridStep s t K n) Bk)
```
**b.3 Targets 2–3 and the Taylor hypothesis**, extracted from the file (statements up to `:=`):
```
theorem gridDriftQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (hj : j < K n)
    (hlam : 0 < sz.lam n) {m : ℕ} (hm : 1 ≤ m) (σ : Fin (m + 1) → Bool) (Bk : ℝ) (hBk : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) (gridTime s t K n (j + 1)), ∀ J : LoopIdx (Zd d (sz.L n)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 1 →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) w J‖ ≤ Bk) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Fin (m + 1) → Zd d (sz.L n),
      ‖(pathP sz)[fun ω' => aTrueQN sz E s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n))
            σ (j + 1) ω' a | filt sz j] ω -
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
            (aTrueQN sz E s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω) a -
          (gridStep s t K n : ℂ) *
            dGridQN sz E s t K n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω a‖ ≤
        qErrQN sz E s t K n m ((1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m))
          (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) Bk j :=
theorem stoppedDuhamelQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {m : ℕ}
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool)
    (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hj : j ≤ K n) :
    aFrozQN sz E s t K n ϑ σ τ j ω =
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n j)
          (aTrueQN sz E s t K n ϑ σ 0 ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1)) (gridTime s t K n j)
            ((gridStep s t K n : ℂ) • dGridQN sz E s t K n ϑ σ i ω +
              martIncQN sz E s t K n ϑ σ i ω + rGridQN sz E s t K n ϑ σ i ω) := by
def QGridA_Taylor2 {d m L : ℕ} [NeZero L] (C₂ : ℝ)
    (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) : Prop :=
theorem QGridA_mollifier_taylor2 (d L m : ℕ) [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) :
    QGridA_Taylor2 (d := d) (1000 * (1 + ((d * m : ℕ) : ℝ)) ^ 2) (QopAlgebra_mollifier d L m g) := by
```
**b.4 Compiled nonempty instances** (`namespace QGridACheck`, `sz0` = `L_0 = 4, W_0 = 32, lam_0 = 1/64`; `GridDriftNCheck` data `E ≡ 0, s ≡ 1/10, t ≡ 1/2, K ≡ 4`, `Δ = 1/10`; `k = 4`, `σ = (+,-,+,-)`; merged mollifier; every hypothesis discharged, none left open):
```
def sigma4 : Fin (3 + 1) → Bool := ![true, false, true, false]
theorem sigma4_alternating : STAlternating sigma4 := by
  unfold STAlternating sigma4
  decide
theorem gridDriftQN_instance :
    STAlternating sigma4 ∧
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ᵐ ω ∂(pathP sz0), ∀ a : Fin (3 + 1) → Zd 3 (sz0.L 0),
      ‖(pathP sz0)[fun ω' => aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 (0 + 1) ω' a | filt sz0 0] ω -
          Ugen 3 (sz0.L 0) (sz0.lam 0) (E0 0) sigma4 (gridTime s0 t0 K0 0 0)
            (gridTime s0 t0 K0 0 (0 + 1)) (aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω) a -
          (gridStep s0 t0 K0 0 : ℂ) * dGridQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω a‖ ≤
        qErrQN sz0 E0 s0 t0 K0 0 3 ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3))
          (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2) Bk 0 := by
  obtain ⟨_, _, _, hv1, _⟩ := QGridA_time_facts s0 t0 K0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Bk, hB0, hB⟩ := GridDriftN_exists_envelope (d := 3) (L := sz0.L 0) (W := sz0.W 0)
    (g := sz0.lam 0) (sz0.three_le_L 0) (sz0.W_pos 0) (E := E0 0) (by norm_num)
    (v := gridTime s0 t0 K0 0 (0 + 1)) (by rw [data.2.2]; norm_num) hv1 (3 + 1)
  exact ⟨sigma4_alternating, Bk, hB0, gridDriftQN sz0 E0 s0 t0 K0 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) lam_pos (m := 3) (by norm_num) sigma4 Bk
    hB0 hB⟩
theorem stoppedDuhamelQN_instance (ω : PathΩ sz0) :
    STAlternating sigma4 ∧
    aFrozQN sz0 E0 s0 t0 K0 0 moll sigma4 (fun _ => 3) 4 ω =
      Ugen 3 (sz0.L 0) (sz0.lam 0) (E0 0) sigma4 (gridTime s0 t0 K0 0 0) (gridTime s0 t0 K0 0 4)
          (aTrueQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (E0 0) sigma4 (gridTime s0 t0 K0 0 (i + 1))
            (gridTime s0 t0 K0 0 4)
            ((gridStep s0 t0 K0 0 : ℂ) • dGridQN sz0 E0 s0 t0 K0 0 moll sigma4 i ω +
              martIncQN sz0 E0 s0 t0 K0 0 moll sigma4 i ω +
              rGridQN sz0 E0 s0 t0 K0 0 moll sigma4 i ω) :=
  ⟨sigma4_alternating, stoppedDuhamelQN sz0 E0 s0 t0 K0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) moll sigma4 (fun _ => 3) 4 ω (by norm_num)⟩
theorem taylor2_instance :
    QGridA_Taylor2 (d := 3) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2) moll :=
  QGridA_mollifier_taylor2 3 (sz0.L 0) 3 (sz0.three_le_L 0) lam_pos
```
**b.5 Name clashes**: `grep -rnw <name> RBM3D RBM3D.lean` (main worktree at `a871db4` and this worktree), count outside `QGridA.lean`:
```
main/worktree counts: aTrueQN 0/0, dGridQN 0/0, aFrozQN 0/0, martIncQN 0/0, rGridQN 0/0, lkEnvN 0/0, driftEnvN 0/0, qStepErrN 0/0, qErrQN 0/0, gridDriftQN 0/0, stoppedDuhamelQN 0/0, QGridA_Taylor2 0/0, QGridA_mollifier_taylor2 0/0, QGridA_condExp_aTrueQN 0/0, QGridA_gridDriftQN_of 0/0, QGridACheck 0/0
```
**b.6 Registry and full build**: scratch file `import RBM3D` + `import RBM3D.Induction.QGridA` + `#assert_rbm_axioms`: `lake env lean` exit 0 (no unregistered premise; `Test/Axioms.lean` not changed). `lake build` (whole library, worktree): `Build completed successfully (3877 jobs)`.
**b.7 Port** (read-only): RBM2D `RBM2D/Induction/AltGridQ.lean` sections 1–9, 11 at `c9a24cf` (HEAD `9e0f275`); no RBM1D file used.
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/AltGridQ.lean
 RBM2D/Induction/AltGridQ.lean | 272 ++++++++++--------------------------------
 1 file changed, 63 insertions(+), 209 deletions(-)
```
**b.8 Narrative**
- All three targets are in `RBM3D/Induction/QGridA.lean` (only file of `git diff --stat main...t/T2132`); axioms are the three standard ones (b.1); registry pre-check and full `lake build` pass (b.6).
- Target 1: tensors of `m + 1` indices (`Fin (m+1)`, no `[NeZero k]`), `ϑ` an explicit argument; the drift is `𝒬_u D + [𝒬_u, Θ_{u,σ}] X − (𝒫X)_{a₁} ∂_uϑ` (`ℬ₄`, `ℬ₅`). `ℬ₄` is the expression of the pin `STB45`: a scratch `example` (compiled without error) checks `EKsgn (mE E) σ = fun i => mSigma E (σ i)`.
- Sign of `ℬ₅`: paper `3_5:1345` has `ℬ₅ := −[𝒫∘(𝓛−𝒦)]∂_uϑ` and `3_5:1315` has `−[…]∂_tϑ` in `zjuii1`; the Lean last term is `− STPsum X (a 0) * deriv ϑ`, i.e. `+ℬ₅` with the paper's sign. RBM2D `docs/paper-deltas.md` #122 corrects a `+` printed in the 2D paper; the 3D text prints `−`: no sign delta.
- Target 2 = merged `gridDriftN_at` (`stepErrN`) + `QGridA_condExp_aTrueQN` (`𝔼[·|F_j]` commutes with `𝒬_{u_{j+1}}`) + the exact six-term identity `QGridA_qstep_algebra` (RBM2D §6; linearity via `QopAlgebra_UN_sub`, `QopAlgebra_ThetaN_sub`; the merged commutator lemmas are not needed because `ℬ₄` is defined as the commutator) + the drift envelope `QGridA_norm_drift_le` (`norm_primBil_le`, `W^d L^d`) + `#{a : a 0 = x} = (L^d)^m` (`QGridA_card_filter`).
- Time regularity, route (b) of the ticket: `STMollifierProps` gives `‖ϑ‖ ≤ C` (`QGridA_vartheta_sup`) and, with `DifferentiableAt`, the Lipschitz bound (`QGridA_vartheta_lip`); the second-order bound `QGridA_Taylor2` is proved for the merged mollifier (`QGridA_mollifier_taylor2`, `C₂ = 1000 (1 + d m)²`; sections 4a–4d, lines 557–1252). Route (a) fails (a): the per-step bound of `T1` is `Lp Mk 2 C β Δ`, whose sum over the grid is `K`-independent. No change of `STMollifierProps`.
- Forms: hypotheses at the size index `n` only (DECISIONS §29 (4)); `1 ≤ m` (`k ≥ 2`), `0 < sz.lam n` for the merged mollifier; `stoppedDuhamelQN` is pure algebra (merged `GridDuhamelN_Ugen_duhamel_telescope`, `_comp`, `_add`), valid for every `ϑ` and `m`. `QGridA_gridDriftQN_of` is the version for any `ϑ` with `STMollifierProps`, `DifferentiableAt` on `[0,1)` and `QGridA_Taylor2 C₂ ϑ`.
- Copied private helpers (prefix `QGridA_`): tensor step, `𝒰` step bound, time facts, integrability and `AvecN` unfolding of `GridDriftN.lean`; the 1-D masses and `u_t` of `QopAlgebra.lean`; `cutGlue` length/WF of `Path/OneStep.lean`; the `S` row sum of `HierAlgebra.lean`.
- Instances (b.4): `sz0`, `Δ = 1/10`, `σ = (+,-,+,-)` alternating, `Bk` from `GridDriftN_exists_envelope`; the conclusion of `gridDriftQN_instance` has constants `C = (1 + 40·9)·6^9`, `C₂ = 1000·10²` (the statement's own constants; the hypotheses are all true at the concrete data).

## (c) Verified Mathlib names (script: `env.getModuleIdxFor?` in a scratch file importing `RBM3D`; none of the used names is absent)
```
Real.quadratic_le_exp_of_nonneg: Mathlib.Analysis.Complex.Exponential
norm_image_sub_le_of_norm_deriv_le_segment': Mathlib.Analysis.Calculus.MeanValue
HasDerivAt.sqrt: Mathlib.Analysis.SpecialFunctions.Sqrt
HasDerivAt.fun_inv: Mathlib.Analysis.Calculus.Deriv.Inv
HasDerivAt.fun_div: Mathlib.Analysis.Calculus.Deriv.Inv
HasDerivAt.fun_pow: Mathlib.Analysis.Calculus.Deriv.Pow
HasDerivAt.fun_sum: Mathlib.Analysis.Calculus.Deriv.Add
HasDerivAt.congr_deriv: Mathlib.Analysis.Calculus.Deriv.Basic
HasDerivAt.ofReal_comp: Mathlib.Analysis.Complex.RealDeriv
hasSum_geometric_of_lt_one: Mathlib.Analysis.SpecificLimits.Basic
sum_le_hasSum: Mathlib.Topology.Algebra.InfiniteSum.Order
Finset.card_bij': Mathlib.Data.Finset.Card
one_add_mul_le_pow: Mathlib.Algebra.Order.Ring.Pow
MeasureTheory.condExp_sub: Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
MeasureTheory.condExp_smul: Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
MeasureTheory.condExp_finsetSum: Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
Real.exp_one_lt_d9: Mathlib.Analysis.Complex.ExponentialBounds
inv_anti₀: Mathlib.Algebra.Order.GroupWithZero.Basic
```

## (d) Open issues and paper-delta candidates
- `T2132a` (drift form): Lean `dGridQN = 𝒬_u D + ℬ₄ + ℬ₅`; the paper's `int_K-L+Q` (`3_5:1337–1346`) writes `𝒰∘𝒬_u∘Σ_{k=1}^5 ℬ_k`. They agree because `𝒫ℬ₄ = 0` (`QopAlgebra_ThetaN_sumZero`) and `𝒫ℬ₅ = 0` (`QopAlgebra_Psum_deriv`), so `𝒬_uℬ_k = ℬ_k` (as in RBM2D #130); the bridge is not proved here.
- `T2132b` (time regularity): Lean uses the second-order bound `‖ϑ_v − ϑ_u − Δ∂_uϑ_u‖ ≤ C₂(1−v)⁻²Δ²`; the paper's `eq:derv_Theta` is first order. Proved for the merged mollifier (smoothed scale, T2041b), not part of `STMollifierProps`.
- `T2132c` (indexing): tensors of `m + 1` indices, `m ≥ 1`, in place of `n ≥ 2`; no `[NeZero k]`.
- `T2132d` (statement form): hypotheses at the size index `n` only; `0 < sz.lam n` (the mollifier scale); the general theorem needs `DifferentiableAt` of `t ↦ ϑ_t(a)` on `[0,1)`, while `STMollifierProps` gives `DifferentiableOn` on `Ico 0 1`.
- Open for S3-13b (not done here): the summation of `qErrQN` needs `sum_weighted_stepErrN_le` (ST2-31) and the envelope `Bk` (`hB`, as in `gridDriftN_at`; asymptotically `exists_norm_Kcal_le_win` with the owed pin `STKbound`). RBM2D's section 10 (`AltGridQ:1680–1687`, read-only) counts, for `d = 2`, the first term of `qStepErrN` at decay exponent `D_t + k` (`Lp ≤ N^{k-1}`) and the `Δ²` terms by `k + 2τ_K + (3k+2)(1−τ') + D_t < C_K`; with `Lp = (L^d)^m ≤ N^m` the same shape is expected here; not re-verified.
