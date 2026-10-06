Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 08:42:00 UTC 2026

Notation: `x = 2(n+1)`; `sz0` (`Defs/Sizes.lean:260`): `W = x^5`, `L = 4(n+1) = 2x`, `lam = x^-6`, `N = (W L)^3 = 8 x^18` (`Sizes.size`, `Sizes.lean:157`).
Tensors have `m+2` indices, `k = m+2`; the mollifier/`STQopNorm` rank is `m+1`; `m = 2` gives `k = 4 = 3+1` (`zero_mem_inst`, `QDriftB.lean:604`).

### (i) Exponent table (instance data `d=3, m=2, Λg=1, K=2, κ=1, E=0, u_j∈{0,1/8,..}, τ'=1/10, ε'=1/5, D'=40, (Γ,Λ,Φ)=(4,100,1)`)

| quantity | value | constraint (target) | slack |
|---|---|---|---|
| `C` (mollifier, `QopAlgebra.lean:511`) | `(1+40·d(m+1))·6^{d(m+1)} = 361·6^9 = 3638048256` | `C>0` (T3-5) | — |
| `c` | `1/2` | `c>0` | — |
| `C_n` (`stQopNorm_holds`, `QopNorm.lean:261`, rank `m+1`) | `C + 2d(m+1) + K(m+1) = 3638048280` | `C_n>0`, depends on `(d,m,Λg,K,C,c)` only | `log10(C_n ε') = 8.86` (bound is huge: the instance tests hypotheses/application, not tightness) |
| `W` | `x^5` (`x=10`: `10^5`) | `1<W` (T3-5) | `x^5-1` |
| `ε'` | `1/5` | `0<ε'<1`, `4 ≤ W^{ε'} = x` | `x/4 = 2.5` at `x=10` |
| `τ'` | `1/10` | `0 ≤ τ'`; `d W^{τ'} ≤ W^{ε'}` ⇔ `3√x ≤ x` ⇔ `9x ≤ x²` | `x ≥ 9`; slack `x/9 = 1.11` at `x=10` |
| `D'` | `40` | `1<D'`; `W^{-D'} ≤ ν N^{-(2m+4)}` ⇔ `N^8 ≤ ν x^{200}` | `log10`: `151.2 ≤ 205.0` at `x=10, ν=W` |
| `K` | `2` | `L^d ≤ W^K`: `8x³ ≤ x^{10}` | `x^7/8` (`1.25·10^6` at `x=10`) |
| `Λg`, `lam` | `1`, `x^-6` | `0<lam≤Λg` | `x^6` |
| `κ`, `E` | `1`, `0` | `0<κ`, `|E| ≤ 2-κ` (`0 ≤ 1`); T6: `|E|<2` | `1` |
| `s,v,Kg,u_j` | `0, 1/2, 4`, `u_j=j/8` | `0 ≤ s ≤ v < 1`, `0 ≤ u_j < 1` (`ST_gridTime_mem`, `j<Kg`) | `1/2` |
| case (i) | `N^{-1}` | `N⁻¹ ≤ 1-v = 1/2` (⇒ `≤ 1-u_j`) | `~10^{-19}` vs `1/2` |
| `(Γ,Λ,Φ)` | `(4,100,1)` | `1 ≤ ΓΦ` (T1); `0 ∈ GoodSetN` via `zero_mem_goodSetN_of_levels`: `k(1+lam²)^{2k} ≤ Γ(ΓΛ)`, `k=4` | `4(1+lam²)^8 ≤ 1024 ≤ 1600` (`AzumaProxyN.lean:924`, used as `zero_mem_inst`) |
| `ν`, `X` (choice A, ticket) | `ν=W=x^5`, `X=1` | `1≤ν`, `1≤X`, `ΓΦ=4 ≤ νX`, `(W^{τ'})^{dm}=x^3 ≤ ν`, `ν ≤ N` | `ΓΦ`: `x^5/4`; `ν ≤ N`: `N/ν = 8x^{13}` |
| `ν`, `X` (choice B, S3-18a natural) | `ν=max(1,W^{τ'dm})=x^3`, `X=ΓΦ=4` | same | `ΓΦ=4 ≤ νX = 4x^3`; `x^3 ≤ ν` with equality; `ν ≤ N`: `x^3 ≤ 8x^18` |
| `τN` | `2` (`x=10`) or `1` (`x ≥ 58`, choice A; `x ≥ 16`, choice B) | `(2m+5)·3·4^{dm}·(2/√κ)·C·ν² ≤ N^{τN}`: LHS `=8.05·10^{14}ν²` | `x=10, A, τN=2`: `10^{24.91} ≤ 10^{37.81}` |
| existential `n` | no eventual threshold in T1-T6 (no crude sup, no `W₀`); concrete `n=4` (`x=10 ≥ 10`, as `numeric`, `QDriftB.lean:494`) with `τN=2`; for `τN=1` `n=29` (`x=60`) | `x ≥ 10` (numeric); τN-row above | ticket's expected `x ≳ 60` is for `τN=1`, choice A only |
| `σ` | `![true,false,true,false]` | `σ(last) = !σ 0` (`false = !true`) | — |
| `dDriftAltQN` summands (§45 O2) | 1st `W^{C_nε'}Γ(ΓΦ)(B^{m+2}/η)((m+1)+(m+2)ΓΦ)`, 3rd `N^{τN}η⁻¹B^{m+2}X` (`X=ΓΦ` in B) | both are `(factor)·B_u^{m+2}/η_u`: one budget line serves both | — |
| `hdDrift0` (T6) | `0 ≤ Γ,Φ,X`; `η>0` (`etaT_pos`, `|E|<2`, `u<1`); `B>0` (`STBctl_pos`, `u<1`); `k-1 = m+1 ≥ 1` | all three summands are products of nonnegatives (`rpow` of `W≥0`) | — |

Boundary items (§29): `m=0` gives `k=2`, `Icc 3 2 = ∅`, `driftTensorN_norm_le_of_goodSet` needs `2 ≤ k` (holds); `1<W`, `0<ε'<1`, `1<D'`, `0≤τ'`, `0<lam≤Λg`, `0 ≤ u < 1`, `|E| ≤ 2-κ` all in the rows above; per matrix, no `Prec`.
External hypotheses: none. `GoodSetN` membership is the only pathwise hypothesis; it is discharged at `H=0` by the merged `zero_mem_goodSetN_of_levels` (no limit statement needed).

### (ii) One concrete nondegenerate instance

Data: `d=3, m=2, K=2, Λg=1, κ=1, E≡0, s≡0, v≡1/2, Kg≡4, τ≡1, j=0, n=4 (x=10, W=10^5, L=20, N=8·10^18), ν=W, X=1, τN=2, ε'=1/5, τ'=1/10, D'=40, (Γ,Λ,Φ)=(4,100,1), H=0, σ=![T,F,T,F]`, label type `Fin 4 → Zd 3 20` nonempty.
Check of every numeric hypothesis of targets 1-6 (exact integer/rational arithmetic; script `scratchpad/T2272/inst.py`, 44 lines; `rpow` hypotheses rewritten with `W^{1/5}=x`, `W^{1/10}=√x`, `(W^{1/10})^6=x^3`, `W^{-40}=x^{-200}`):

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2272/inst.py
A: nu=W, X=1 tauN=1 minimal n (x=2(n+1)>=10): 28 x= 58
A: nu=W, X=1 tauN=2 minimal n (x=2(n+1)>=10): 4 x= 10
B: nu=x^3=W^(3/5), X=GammaPhi=4 tauN=1 minimal n (x=2(n+1)>=10): 7 x= 16
B: nu=x^3=W^(3/5), X=GammaPhi=4 tauN=2 minimal n (x=2(n+1)>=10): 4 x= 10
C= 3638048256  Cn= 3638048280  log10(Cn*eps')= 8.861898453887449
n=4 x=10 W=100000 L=20 N=8000000000000000000 nu=x^5 X=1 tauN=2 ALL=True
    True 1<W
    True 4<=W^(1/5)=x
    True L^3<=W^K (K=2)
    True d*W^(1/10)<=W^(1/5) <=> 9x<=x^2
    True 0<lam<=Lg=1
    True N^-1<=1-v=1/2
    True 1<=nu,1<=X
    True G*Phi<=nu*X
    True (W^tau')^(dm)=x^3<=nu
    True nu<=N
    True W^-D'<=nu N^-(2m+4)  <=> N^8<=nu x^200
    True hMLam: (2m+5)3*4^(dm)*2*C*nu^2<=N^tauN
    True zero_mem level: 4(1+lam^2)^8<=G^2*Lam=1600
    True hdDrift: 0<=Gam,Phi,X
   log10 LHS hMLam=24.91 log10 N^tauN=37.81 ; log10 N^8=151.2 log10 nu x^200=205.0
n=29 x=60 W=777600000 L=120 N=812479653347328000000000000000000 nu=x^5 X=1 tauN=1 ALL=True
n=4 x=10 W=100000 L=20 N=8000000000000000000 nu=x^3 X=4 tauN=2 ALL=True
u_j = ['0', '1/8', '1/4', '3/8', '1/2'] ; 0<=u_j<1: True
sigma last = !sigma 0: True | |E|=0<=2-kappa=1: True | 1<D'=40, 0<eps'=1/5<1, 0<=tau'=1/10
```

Targets 1-2 at this data: `H=0 ∈ GoodSetN` (levels `(4,100,1)`), `j ∈ {1,2,3}` (T1: `1 ≤ ΓΦ=4`, `‖STLKM‖ ≤ 4B^j`; T2: `j ≤ 2k+2=10`, window `ℓ_0 W^{1/10} = √10` (`ℓ_0 = 1`, `lam ≤ 1`), attained by the tuple `(0,x⃗,0,0)` with `diam_∞ = x = 10` (`QDriftB.lean:579`)). At `H=0` entries may vanish: the instance tests hypotheses and application, not tightness.

### Verdicts
- T1 `goodSetN_LKM_le`: PASS (`STXiLKM = 1 + STmaxLKM/B^j`, `STmaxLKM ≥ 0` as a `sup'` of norms, `B>0` by `STBctl_pos` for `u<1`; `STLKM = STLM - STKloop` is the summand of `STmaxLKM`, `Step2Defs.lean:68`, `GridGoodN.lean:68`).
- T2 `goodSetN_LKM_far`: PASS ((Dec) clause of `GoodSetN`, `GridGoodN.lean:128-132`: `‖loopFine‖ + ‖loopFine - STKloop‖ ≤ W^{-D'}` for `1 ≤ j ≤ 2k+2`, second summand).
- T3 `qopB13N_levelM`: PASS (`stQopNorm_holds` at rank `m+1`, `C_n = C+2d(m+1)+K(m+1)`; decay `drift13_fastDecay` needs only `d W^{τ'} ≤ W^{ε'}`; sup `driftTensorN_norm_le_of_goodSet` with `2 ≤ m+2`; bound ≥ 0 at any label).
- T4 `dFlowQN_levelM`: PASS (`dFlowQN` first summand is the text of `driftTensorN` at `k=m+2`, `Icc 3 (m+2)` in both; `altB45N_levelM` hypotheses: `hY` from T1 with `ΓΦ ≤ νX`, `hF` from T2 with `ωf = W^{τ'} ≥ 1`, `hϑ`,`hϑ'` from `STMollifierProps` clauses 2, 4 with `exp(−…) ≤ 1`, `Λ=C`; `hMΛ` as stated).
- T5 `alt_hdriftQN`: PASS (`dGridQN_eq_dFlowQN`, `ST_gridTime_mem` for `j<Kg n` gives `u_j ∈ [s,v]`, `N⁻¹ ≤ 1-v ≤ 1-u_j`; `QopAlgebra_mollifier_props` with `m:=m+1`, `3 ≤ L` from `sz.three_le_L`; same `Dr`, `hτG` as `alt_hDclsQN` at `m+1`, `QDriftB.lean:379-396`).
- T6 `dDriftAltQN_nonneg`: PASS (row `hdDrift0`).
No pinned shape fails; no missing input.

## (b) Script output — stage 1b, Tue Oct  6 08:52:54 UTC 2026

### Build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2272, branch t/T2272, commit 4e80637)
```
$ lake build RBM3D.Induction.QLevelsB 2>&1 | tail -3 ; exit 0

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3858 jobs).
$ grep "QLevelsB.lean" build.out | grep -c warning   (all five are the module-docstring longLine lines 15-30, as in QLevelsA)
5
$ grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats" RBM3D/Induction/QLevelsB.lean | wc -l
       0
$ wc -l RBM3D/Induction/QLevelsB.lean
     586 RBM3D/Induction/QLevelsB.lean
$ git diff --stat main...t/T2272
 RBM3D/Induction/QLevelsB.lean | 586 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 586 insertions(+)
```

### Registry pre-check (`import RBM3D` + `import RBM3D.Induction.QLevelsB` + `#assert_rbm_axioms`, `lake env lean`)
```
exit 0, no error lines; head of output:
axiom audit: 7918 theorems, 2610 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ grep -c "QLevelsB\|dDriftAltQN\|T2272" reg.out
0
```

### `#print axioms` (lake env lean ax.lean)
```
'RBM.Ind.dDriftAltQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.goodSetN_LKM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.goodSetN_LKM_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.qopB13N_levelM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.dFlowQN_levelM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.alt_hdriftQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.dDriftAltQN_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.goodSetN_LKM_le_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.goodSetN_LKM_far_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.qopB13N_levelM_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.dFlowQN_levelM_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.alt_hdriftQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.dDriftAltQN_nonneg_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Statement diff against the check file (script `diff.py`: whitespace-normalised text of each `T2272_*` Prop body vs the theorem statement; and the §2 definition)
```
goodSetN_LKM_le IDENTICAL 322
goodSetN_LKM_far IDENTICAL 389
qopB13N_levelM IDENTICAL 859
dFlowQN_levelM IDENTICAL 1109
alt_hdriftQN IDENTICAL 1293
dDriftAltQN_nonneg IDENTICAL 162
dDriftAltQN def IDENTICAL
```

### Extracted statements (script `stm.py`, whitespace-normalised, one per paragraph: the §2 definition, targets 1-6, then the six compiled instances)
```
def dDriftAltQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ) : ℝ := ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ + ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) + ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

theorem goodSetN_LKM_le : ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → u < 1 → ∀ j : ℕ, 1 ≤ j → j < k → 1 ≤ Γ * Φ ∧ ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)), ‖sz.STLKM n E u H σ' a'‖ ≤ Γ * Φ * sz.Bctl n u ^ j

theorem goodSetN_LKM_far : ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)), ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')

theorem qopB13N_levelM : ∀ (d m : ℕ) (Λg K C c : ℝ), 3 ≤ d → 0 < Λg → 0 < K → 0 < C → 0 < c → ∃ Cn : ℝ, 0 < Cn ∧ ∀ (sz : Sizes d) (n : ℕ) (E u Γ Λ Φ τ' ε' D' : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ), 0 < sz.lam n → sz.lam n ≤ Λg → 1 < ((sz.W n : ℕ) : ℝ) → 0 < ε' → ε' < 1 → 1 < D' → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → STMollifierProps (d := d) (sz.lam n) C c ϑ → 0 ≤ u → u < 1 → H ∈ sz.GoodSetN n E u (m + 1 + 1) Γ Λ Φ τ' D' → ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n), ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b) a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ + ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn)

theorem dFlowQN_levelM : ∀ (d m : ℕ) (Λg K C c : ℝ), 3 ≤ d → 0 < Λg → 0 < K → 0 < C → 0 < c → ∃ Cn : ℝ, 0 < Cn ∧ ∀ (sz : Sizes d) (n : ℕ) (E u κ Γ Λ Φ τ' ε' D' ν X τN : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ), 0 < κ → |E| ≤ 2 - κ → 0 ≤ u → u < 1 → 0 < sz.lam n → sz.lam n ≤ Λg → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u → 1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → 1 ≤ ν → 1 ≤ X → Γ * Φ ≤ ν * X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) → ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ → (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * C * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN → STMollifierProps (d := d) (sz.lam n) C c ϑ → H ∈ sz.GoodSetN n E u (m + 1 + 1) Γ Λ Φ τ' D' → σ (Fin.last (m + 1)) = !σ 0 → ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n), ‖dFlowQN sz n E u ϑ σ H a‖ ≤ dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X

theorem alt_hdriftQN : ∀ (d m : ℕ) (Λg K : ℝ), 3 ≤ d → 0 < Λg → 0 < K → ∃ Cn : ℝ, 0 < Cn ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (κ τ' ε' D' ν X τN : ℝ) (τ : PathΩ sz → ℕ), 0 < κ → |E n| ≤ 2 - κ → 0 < sz.lam n → sz.lam n ≤ Λg → 0 ≤ s n → s n ≤ v n → v n < 1 → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n → 1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' → 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → 1 ≤ ν → 1 ≤ X → Γ n * Φ n ≤ ν * X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) → ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ → (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN → σ (Fin.last (m + 1)) = !σ 0 → (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈ sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1 + 1) (Γ n) (Λ n) (Φ n) τ' D') → ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω b‖ ≤ dDriftAltQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ n) Cn ε' D' τN X

theorem dDriftAltQN_nonneg : ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ), |E| < 2 → u < 1 → 0 ≤ Γ → 0 ≤ Φ → 0 ≤ X → 0 ≤ dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X

theorem goodSetN_LKM_le_instance (j : ℕ) (hj1 : 1 ≤ j) (hj : j < 3 + 1) : 1 ≤ (4 : ℝ) * 1 ∧ ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd 3 (sz0.L 4)), ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ 4 * 1 * sz0.Bctl 4 0 ^ j

theorem goodSetN_LKM_far_instance : (∃ b : Fin (3 + 1) → Zd 3 (sz0.L 4), ellT (sz0.L 4) (sz0.lam 4) 0 * ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf b : ℝ)) ∧ ∀ (σ' : Fin (3 + 1) → Bool) (a' : Fin (3 + 1) → Zd 3 (sz0.L 4)), ellT (sz0.L 4) (sz0.lam 4) 0 * ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf a' : ℝ) → ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ))

theorem qopB13N_levelM_instance (σ : Fin (2 + 1 + 1) → Bool) (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) : ∃ Cn : ℝ, 0 < Cn ∧ ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 4) 3 (sz0.lam 4)) 0 (fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4) => driftTensorN sz0 4 0 0 H0 σ b) a‖ ≤ ((sz0.W 4 : ℕ) : ℝ) ^ (Cn * (1 / 5)) * dDriftNonAltN sz0 4 0 0 (2 + 1 + 1) 4 1 + ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ) + Cn)

theorem dFlowQN_levelM_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) : ∃ Cn : ℝ, 0 < Cn ∧ ‖dFlowQN sz0 4 0 0 (QopAlgebra_mollifier 3 (sz0.L 4) 3 (sz0.lam 4)) σalt H0 a‖ ≤ dDriftAltQN sz0 4 0 0 2 4 1 Cn (1 / 5) 40 2 1

theorem alt_hdriftQN_instance : ∃ Cn : ℝ, 0 < Cn ∧ ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)), ‖dGridQN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4 (QopAlgebra_mollifier 3 (sz0.L 4) 3 (sz0.lam 4)) σalt 0 ω b‖ ≤ dDriftAltQN sz0 4 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4 0) 2 4 1 Cn (1 / 5) 40 2 1

theorem dDriftAltQN_nonneg_instance : 0 ≤ dDriftAltQN sz0 4 0 0 2 4 1 1 (1 / 5) 40 2 1

```

### Name-clash grep (new public names, over /Users/junyin/Lean_proof/RBM3D/RBM3D/ excluding QLevelsB.lean)
```
$ for n in dDriftAltQN goodSetN_LKM_le goodSetN_LKM_far qopB13N_levelM dFlowQN_levelM alt_hdriftQN dDriftAltQN_nonneg QLevelsBInst QLevelsB_; do grep -rn -F "$n" RBM3D/ | grep -v QLevelsB.lean | wc -l; done
dDriftAltQN:        0
goodSetN_LKM_le:        0
goodSetN_LKM_far:        0
qopB13N_levelM:        0
dFlowQN_levelM:        0
alt_hdriftQN:        0
dDriftAltQN_nonneg:        0
QLevelsBInst:        0
QLevelsB_:        0
```
Ports: RBM2D `AltLevelsQ` (`c9a24cf`) used as the route only (`AltLevelsQ_B123/_Qop_le/_final123/_B45`); no RBM1D/RBM2D text copied, no RBM1D/RBM2D diff-stat needed. Numeric helpers of the instance section are copies of private helpers of the merged RBM3D `QDriftBInst` (`QDriftB.lean`, c01b292) and of `QLevelsA.norm_STLKM_le_of_XiLKM` (`QLevelsA.lean`, f515695).

### Narrative (<= 40 lines)
- File: `RBM3D/Induction/QLevelsB.lean`, namespace `RBM.Ind`; the check file's §2 definition `dDriftAltQN` and the six §3 statements are proved with exactly that text (diff above: IDENTICAL). No hypothesis added, no pin changed, no `set_option maxHeartbeats`.
- Targets 1-2 (`goodSetN_LKM_le`, `goodSetN_LKM_far`): clause (G2) via `Finset.le_sup'` on the summand of `STmaxLKM` and `STBctl_pos`; clause (Dec) by dropping the first (nonnegative) summand.
- Target 3 (`qopB13N_levelM`): `Cn` is the `C_n` of `stQopNorm_holds d hd (m+1) Λg K C c` (existential, before `sz`); `drift13_fastDecay` (at `m+1`) gives `EKFastDecay`; sup from `driftTensorN_norm_le_of_goodSet` via `pi_norm_le_iff_of_nonneg`, nonnegativity of the bound from the pointwise bound at the label `fun _ => 0`; entry bound from `norm_le_pi_norm`.
- Target 4 (`dFlowQN_levelM`): `dFlowQN = STQop(block) + altB4N + altB5N` is `rfl` (preflight (i) confirmed); `altB45N_levelM` at `Γ := 2/√κ`, `Λ := C`, `ωf := W^{τ'}`, `Fv := W^{-D'}`; `hY` from target 1 with `ΓΦ ≤ νX`; `hF` from target 2; `hϑ` from clause 2 of `STMollifierProps` with `exp(-c·S/ℓ) ≤ 1` (general `c > 0`); `hϑ'` is clause 4 verbatim; sum by `norm_add₃_le`. The level is a sum, as the ticket's Design (d).
- Target 5 (`alt_hdriftQN`): `dGridQN_eq_dFlowQN`, `ST_gridTime_mem` (`j < Kg n`), `N⁻¹ ≤ 1 - v ≤ 1 - u_j`, target 4 at `C = (1+40d(m+1))6^{d(m+1)}`, `c = 1/2`, `QopAlgebra_mollifier_props` at `m+1`. The only walk hypothesis is `hτG` (pathwise, the same as `alt_hDclsQN` at `m+1`).
- Target 6: `etaT_pos`, `STBctl_pos`, `Real.rpow_nonneg`, positivity.
- Instances: `n = 4` (`x = 10`), `d = 3`, `m = 2` (`k = 4 = 3+1`), `K = 2`, `Λg = 1`, `E = 0`, `u = 0`, `κ = 1`, `H = 0 ∈ GoodSetN` at `(4,100,1)`, `τ' = 1/10`, `ε' = 1/5`, `D' = 40`, `ν = W = 10^5`, `X = 1`, `τ_N = 2`, `N = 8·10^18`, explicit mollifier, `σ = ![T,F,T,F]`; the walk `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4`, `τ ≡ 1`, `j = 0`, every `ω`. This is the preflight (a) instance (choice A, `τN = 2`). No crude sup is a hypothesis of any target, so `n` is concrete and no existential `n` is needed. Every deterministic hypothesis is discharged; the far window of target 2 is attained (`window4`, tuple `(0,x⃗,0,0)`).
- Instances test hypotheses and application, not tightness: at `H = 0` entries may vanish (T2268 (d) 6).
- Case (i) only: `N⁻¹ ≤ 1 - u` (targets 4, 5), as `altB45N_levelM`; recorded for S3-18a (preflight (iv)).

## (c) Verified Mathlib / project names used
All compile in `QLevelsB.lean` (Lean 4.34.0 / Mathlib v4.34.0): `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `Finset.le_sup'`, `Finset.mem_univ`, `Real.one_le_rpow`, `Real.rpow_nonneg`, `Real.exp_le_one_iff`, `div_nonpos_of_nonpos_of_nonneg`, `div_le_iff₀`, `Real.sqrt_one`, `Real.sq_sqrt`, `Real.sqrt_le_left`, `Real.sqrt_eq_rpow`, `Real.rpow_two`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_one`, `Real.le_sqrt'`, `Real.mul_self_sqrt`, `pow_le_pow_left₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `Finset.sup_const`, `ZMod.val_natCast`. Project: `norm_add₃_le`, `stQopNorm_holds`, `drift13_fastDecay`, `driftTensorN_norm_le_of_goodSet`, `altB45N_levelM`, `dGridQN_eq_dFlowQN`, `ST_gridTime_mem`, `ST_gridTime_zero`, `STBctl_pos`, `etaT_pos`, `ellT_pos`, `QopAlgebra_mollifier_props`, `zero_mem_goodSetN_of_levels`, `azumaProxy_pathH_zero_of_s_zero`. Names verified absent: none needed.

## (d) Open issues and paper-delta candidates
- `T2272a` (as the ticket's expected entry): the drift level of the alternating chain `‖𝒬_u(ℬ₁+ℬ₂+ℬ₃) + ℬ₄ + ℬ₅‖ ≤ dDriftAltQN` holds per matrix `H ∈ GoodSetN` with deterministic levels, `(normQA)` (`3_5:1284-1289`) and `(y27kasdfg)` (`3_5:1692-1706`), losses `W^{C_nε'}` and `N^{τ_N}` in place of `≺` (§64 (4)/(5)); the level is a sum of the three summands, not a max.
- `T2272b`: no extra side condition beyond those of `altB45N_levelM` (case (i) `N⁻¹ ≤ 1 - u`, `1 ≤ ν`, `1 ≤ X`, `ν ≤ N`, `ωf^{dm} ≤ ν`, `hMΛ`) and `STQopNorm` (`1 < D'`, `4 ≤ W^{ε'}`, `L^d ≤ W^K`, `d W^{τ'} ≤ W^{ε'}`) was needed: none proposed.
- Open for S3-18a: its good-set family must carry (G2) and (Dec) at rank `m+1+1` (`GoodSetN … (m+1+1)`), as `hτG`; the numeric facts `ΓΦ ≤ νX`, `W^{τ'dm} ≤ ν ≤ N`, `W^{-D'} ≤ νN^{-(2m+4)}`, `hMΛ`, `4 ≤ W^{ε'}`, `N⁻¹ ≤ 1 - v_n` are hypotheses of targets 4-5 and go to its `ev_nums`.
- Preflight (a) needed no correction (no (a′)); the (a) instance data (n=4, x=10, ν=W, X=1, τN=2) is the one compiled.
- Registry: no new `Prop` is public and none was added to `RBM3D/Test/Axioms.lean`; the registry pre-check output lists no `QLevelsB`/`T2272` entry.
