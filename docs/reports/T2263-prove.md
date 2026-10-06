Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 06:38:05 UTC 2026

### (i) Exponent table
Notation: `W = W_n`, `C = (1+40dm)6^{dm}` (mollifier constant, `QopAlgebra_mollifier_props`), `c = 1/2`, `A = STLKM`, `C₁` an internal crude-sup exponent.
Source of every row: the hypotheses of the merged statements read in the files (`QopNorm.lean:378`, `QopDecay.lean:514,762`, `B45.lean:304,671`, `QDriftA.lean:59-93,234,403`, `GridGoodN.lean:124-148`).

| quantity | value / choice | constraint | slack |
|---|---|---|---|
| target 2 block, `δ` | `W^{-D'}` (clause (Vb), `norm_add_le`) | `δ ≤ W^{-D'}`, `d W^{τ'} ≤ W^{ε'}` (hyp.) | 0 (equality); no threshold |
| `‖A−𝒬A‖` crude (T3), `A−𝒬A = (𝒫A)ϑ` | `≤ C(2^{dm}+(L^d)^m)W^{C₀} ≤ W^{C₀+Km+1}` (`B45_Psum_le`, `R=0`; `‖ϑ‖ ≤ C` since `ℓ ≥ 1`) | `W ≥ C(2^{dm}+1)` (`K>0` is forced: `27 ≤ L^d ≤ W^K`, `W>1`) | `d=3,m=3`: `C(2^9+1) = 1.87e12`; `m=1`: `2.35e5`; `m=2`: `7.3e8`; `m=5`: `9.3e18` |
| `‖ΘA‖` crude (T3), `B45_norm_ThetaN_le` | `≤ (m+1)(1−u)⁻¹W^{C₀} ≤ (m+1)W^{C₀+K}` | `W ≥ m+1` gives `≤ W^{C₀+K+1}`; this is `≤ W^{C₀+Km+1}` iff `Km−K+1 ≥ 1`, i.e. `m ≥ 1` | **ticket gap at `m = 0`, `K>1`**: `Km−K+1 = 1−K < 0`. Use `C₁ := C₀+K(m+1)+1` for all crude sups of T3, or a separate exponent for `ΘA`. Statement unaffected (`W₀` existential) |
| `‖𝒫A‖` crude (T4), `B = −𝒫A` | `≤ (2^{dm}+(L^d)^m)W^{C₀} ≤ W^{C₀+Km+1}` | `W ≥ 2^{dm}+1`: `d=3`: `m=1`: 9, `m=2`: 65, `m=5`: 32769 | no `C` here |
| `K, C₀` in the absorptions | cancel (`W^{C₀}`, `W^{Km}` on both sides) | — | table independent of `K ∈ {1,3,10}`, `C₀ ∈ {1,7,30}` |
| depth chain (T3) | `A−𝒬A` at `(ε'/2, D'+K+2)` → `Θ` → `(2·ε'/2, D'+K+2−(K+1)) = (ε', D'+1)`; `ΘA−𝒬ΘA` at `(ε', D'+1)` | `2W^{-(D'+1)} ≤ W^{-D'}` iff `W ≥ 2` | factor `W/2` |
| `δ = 4W^{-D'}` (T5, T6) | `2` (`𝒬`block, `Qop_fastDecay`) `+1+1` (`ℬ₄,ℬ₅`) | exactly 4 | 0 (pinned constant, no loss) |
| `hDD`: `4W^{-D'} ≤ W^{-Dc}` | `D'=6, Dc=3` | `W^{D'−Dc} ≥ 4` | factor `W³/4` |
| `hdW`: `d W^{τ'} ≤ W^{ε'}` | `τ'=1/10, ε'=1/5, d=3` | `3√x ≤ x` (`W=x⁵`) | `x ≥ 9` |
| `L^d ≤ W^K` | `K=2`: `8x³ ≤ x^{10}` | `x ≥ 2` | huge |
| `(1−u)⁻¹ ≤ W^K` (T6: `u_j ≤ v`) | `(1−v)⁻¹ = 2` | `2 ≤ W²` | huge |
| index shift (T6) | `ℓ_{u_j} ≤ ℓ_{u_{j+1}}`: `ellT_mono` needs `0 ≤ g`, `u_j ≤ u_{j+1}` (`ST_gridTime_mono`), `u_{j+1} ≤ v < 1` (`ST_gridTime_mem`, `j+1 ≤ Kg`, `Kg ≠ 0` from `j<Kg`) | all follow from `0 ≤ s ≤ v < 1` | — |
| `W₀` (T3) order of choice | constants `d,m,Λg,K,C,c,C₀,ε',D'` first; `W₀ := max(`stQop_sub_fastDecay`@`(C₁,ε'/2,D'+K+2)`, `@(C₁,ε',D'+1)`, `QopDecay_ThetaN_fastDecay`@`(m+1,Λg,K,C₁,ε'/2,D'+K+2)`, `C(2^{dm}+1)`, `m+1`, `2)` | each depends on those constants only | see growth rows below |
| `W₀` (T4) | `max(`QopDecay_deriv_fastDecay`@`(K,C₀+Km+1,ε',D')`, `2^{dm}+1`, `2)` | idem | idem |
| `W₀` (T6) | `max(QDriftA_W0 d m K Cm (1/2) C₀ ε' D', W₀(T3), W₀(T4))`, `Cm = (1+40dm)6^{dm}` | idem (also `Λg`) | idem |
| growth proxy of each `qn_growth`/`qdec_growth` (`QopNorm.lean:343`, `QopDecay.lean:349`): `C W^p ≤ exp(c W^e/2)`, `d=3,m=3,K=2,C₀=7,D'=6` | rows C of the output below | last crossing `log₁₀ W*` | `ε'=1/5`: 17.5 to 40.5; `ε'=1/50`: 230 and 515. Not Lean's `W₀` (existential), the inequality its proof reduces to. The `ΘN` threshold has existential kernel constants (`QopDecay_thetaKer_decay`); only its explicit part `2^{2/ε'}` (1024 at `ε'=1/5`) is known |

### (ii) One concrete instance (the T2250 data; `W₀` existential as in the merged instances `QDriftA.lean:1218,1276`)
Data: `sz0` (`W = x⁵`, `L = 2x`, `λ = x⁻⁶`, `x = 2(n+1)`; `QDriftA.lean:737`), `d=3, m=3` (`k=4`), `K=2`, `E=0`, `u=0`, `ε'=1/5`, `τ'=1/10`, `D'=6`, `Dc=3`, `Λg=1`, `C₀=7`, `ϑ = QopAlgebra_mollifier`, `C = Cmol3 = 3638048256`, `c=1/2`; `H = 0 ∈ GoodSetN` at levels `(Γ,Λ,Φ) = (4,100,1)` (every `τ', D'`, `QDriftA.lean:1152`); walk `s≡0`, `v≡1/2`, `Kg≡4`, `τ≡1`, `j=0` (`H_0 = 0`, `u_j = j/8`); `i = 1`, `uu = gridTime`. Crude sups: `‖A‖ ≤ W⁷` at `H=0` by the merged `crude_sup` (`QDriftA.lean:1167`); block `≤ Γ(ΓΦ)(B⁴/η)(3+kΓΦ)` (`driftTensorN_norm_le_of_goodSet`, `B = W⁻³(Bparam)`, `Bparam(t=0,K=0) = (g²+1)⁻¹ + (L³)⁻¹`, `η = 1`). `W ≥ W₀` is met by `n ≥ ⌈W₀⌉` (device of the merged instances); the script takes `n = 7·10⁷` above all growth proxies. No external hypothesis: every upstream input is merged; `STMollifierProps` is the merged `QopAlgebra_mollifier_props`; the limit computation is the growth rows (`W_n = x⁵ → ∞`, exponential beats power, each proxy holds from a finite `x*`).
Commands (scripts in the scratchpad `T2263/`, no Lean):
`python3 .../T2263/pre.py` (absorptions, depth chain, growth proxies):
```
A. absorption thresholds (K, C0 cancel), d=3
 m=1: C=(1+40dm)6^dm=26136; A-QA=(PA)theta: W>=C(2^dm+1)=235224; PA (target4): W>=2^dm+1=9; ThetaA: W>=m+1=2; depth sum: W>=2
 m=2: C=(1+40dm)6^dm=1.12441e+07; A-QA=(PA)theta: W>=C(2^dm+1)=7.30866e+08; PA (target4): W>=2^dm+1=65; ThetaA: W>=m+1=3; depth sum: W>=2
 m=5: C=(1+40dm)6^dm=2.82581e+14; A-QA=(PA)theta: W>=C(2^dm+1)=9.2599e+18; PA (target4): W>=2^dm+1=32769; ThetaA: W>=m+1=6; depth sum: W>=2
 ThetaA exponent test (m+1)W^(C0+K) <= W^(C0+K*m+1) needs W^(K*m-K+1)>=m+1:
  m=0 K=1: exponent K*m-K+1=0 (FAILS for large W)
  m=0 K=3: exponent K*m-K+1=-2 (FAILS for large W)
  m=0 K=10: exponent K*m-K+1=-9 (FAILS for large W)
  m=1 K=1: exponent K*m-K+1=1 (ok for W>=m+1)
  m=1 K=3: exponent K*m-K+1=1 (ok for W>=m+1)
  m=1 K=10: exponent K*m-K+1=1 (ok for W>=m+1)
  m=2 K=1: exponent K*m-K+1=2 (ok for W>=m+1)
  m=2 K=3: exponent K*m-K+1=4 (ok for W>=m+1)
  m=2 K=10: exponent K*m-K+1=11 (ok for W>=m+1)
B. depth chain D'+K+2 -> (Theta: -(K+1)) -> D'+1 -> 2*W^-(D'+1) <= W^-D' iff W>=2; D'=6
  K=1: 9 - 2 = 7 (= D'+1 = 7); radius 2*(eps'/2)=eps'
  K=3: 11 - 4 = 7 (= D'+1 = 7); radius 2*(eps'/2)=eps'
  K=10: 18 - 11 = 7 (= D'+1 = 7); radius 2*(eps'/2)=eps'
C. growth-proxy thresholds C*W^p <= exp(c*W^e/2) (qn_growth QopNorm:343 / qdec_growth QopDecay:349), W=x^5; value = log10 W of last crossing
  stQop_sub A-QA  (C1=14,eps'/2,D'+K+2=10) eps'=1/5: x*=e^18.663, log10 W* = 40.53
  stQop_sub ThA-QThA (C1=14,eps',D'+1=7)  eps'=1/5: x*=e^8.445, log10 W* = 18.34
  deriv_fastDecay (C0'=14,K=2,D'=6,c=1/4) eps'=1/5: x*=e^9.000, log10 W* = 19.54
  QDriftA_W0=Qop_fastDecay (C0=7,D'=6) eps'=1/5: x*=e^8.055, log10 W* = 17.49
  stQop_sub A-QA  eps'=1/50 (e=1/100): x*=e^237.341, log10 W* = 515.38
  QDriftA_W0 eps'=1/50 (e=1/50): x*=e^106.064, log10 W* = 230.32
   (d=3,m=3,K=2,C0=7,D'=6; Cmol3 = 361*6^9 = 3638048256; ThetaN_fastDecay constants C_ker,c_ker are existential: no explicit proxy; its explicit part 2^(1/eps)=2^10 at eps=eps'/2... : 2^(2/eps')=1024 (eps'=1/5), 2^100 (eps'=1/50)
```
`python3 .../T2263/inst.py` (hypotheses at `n = 7·10⁷`, and the `m=1` algebra of `ℬ₄,ℬ₅`: random one-slot kernels on `Z_3`):
```
n=7e7: x=1.4e+8, log10 W=40.73, L=2.8e+8, lam=1.3281e-49
  1<W0 growth proxies (all four eps'=1/5 proxies): C W^p<=exp(c W^e/2): True
  W >= C(2^dm+1) (A-QA crude absorption): True
  W >= 2^dm+1, W>=m+1, W>=2: True
  L^3 <= W^K, K=2: True
  d W^tau' <= W^eps' (3 W^(1/10)=35496.5 <= W^(1/5)=1.4e+8): True
  4 W^-D' <= W^-Dc (D'=6,Dc=3): True
  0<lam<=Lambda_g=1; |E|=0<=2; s=0<=v=1/2<1; (1-v)^-1=2<=W^K: True
  ell_{u_j}=1 (j=0..4) and ell_{u_0}<=ell_{u_1}: True
  j=0<Kg=4, j+1<=Kg; u_j in [s,v], (1-u_0)^-1=1<=W^K: True
  block crude sup Gamma(Gamma Phi)(B^4/eta)(k-1+k Gamma Phi)=5.19028e-487 <= W^C0 (C0=7): True
  A crude sup W^7 (merged crude_sup QDriftA:1169, W>=17): True
  Cmol3 = (1+40*9)*6^9 = 3638048256 ; window: ell_0 W^eps' = x = 1.4e+8 <= diam_inf max = floor(L/2)= 1.4e+8
ID. m=1 algebra: B4 := QThA - ThQA vs Theta(A-QA)-(ThA-QThA), B5 sign (random 1-slot kernels, d=1,L=3, tensors Fin 2 -> Z_3)
  max|B4-[Th(A-QA)-(ThA-QThA)]| = 4.577566798522237e-16 ; max|B5-(-PA)(a0)dtheta| = 0.0
```
Window nonempty: `ℓ_0 W^{ε'} = x ≤ ⌊L/2⌋ = x` (`diam_∞` attained, as `window_linf` in the merged instance); non-alternating `σ` allowed (no `σ` hypothesis in T2–T6).

### Verdicts
- T1 (copies of `QDriftA_window_of_diamInf`, `QDriftA_W0_spec`; both read at `QDriftA.lean:389,409`): PASS.
- T2 `drift13_fastDecay`: PASS. (Vb) at `k = m+1` bounds the three norms by `W^{-D'}` on `ℓ_uW^{τ'} ≤ diam_∞`; `fastDecay_of_diamInf` needs `0<d`, `1 ≤ L`, `dW^{τ'} ≤ W^{ε'}`.
- T3 `altB4N_fastDecay`: PASS, with the `m = 0` exponent note in the table (use `C₁ = C₀+K(m+1)+1`). Identity `ℬ₄ = Θ(A−𝒬A) − (ΘA−𝒬ΘA)` checked above (`QopAlgebra_commutator_ThetaN :871`).
- T4 `altB5N_fastDecay_moll`: PASS (`ℬ₅ a = (−𝒫A)(a 0)·∂ϑ`, sign checked above).
- T5 `dFlowQN_clsQN`: PASS (`2+1+1 = 4`; window `ℓ_uW^{ε'} ≤ ℓ_{uu i}W^{ε'} ≤ diam_∞`).
- T6 `alt_hDclsQN`: PASS (`W₀` depends only on `d,m,Λg,K,C₀,ε',D'`).
- Caveat for the dispatcher: witnesses are huge (`log₁₀W ≈ 40.7` at `ε'=1/5`) because each decay step reduces to `C W^p ≤ exp(cW^{ε}/2)`; this is the existential `∃ W₀` shape of the merged `QDriftA_W0`/`stQop_sub_fastDecay`, not a defect of the targets.

## (b) Script output — Tue Oct  6 07:00:01 UTC 2026

### Build, hygiene, scope
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2263 && lake build RBM3D.Induction.QDriftB   # log of the build after the last edit of the file
✔ [3856/3856] Built RBM3D.Induction.QDriftB (5.9s)
Build completed successfully (3856 jobs).
$ lake build RBM3D.Induction.QDriftB 2>&1 | grep -E "QDriftB.lean|Build completed|error|sorry"   # re-run, file unchanged
Build completed successfully (3856 jobs).
$ grep -n "sorry\|admit\|native_decide\|^axiom\|maxHeartbeats" RBM3D/Induction/QDriftB.lean; echo "grep exit=$?"
grep exit=1
$ git diff --name-only main...t/T2263; git log -1 --format="%h %an <%ae>"; wc -l RBM3D/Induction/QDriftB.lean
RBM3D/Induction/QDriftB.lean
f812c4d Jun Yin <321276894+JYin80@users.noreply.github.com>
     951 RBM3D/Induction/QDriftB.lean
```

### `#print axioms` (script `axioms.lean`: `import RBM3D.Induction.QDriftB`, ten `#print axioms`; exit 0)
```
'RBM.Ind.drift13_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altB4N_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altB5N_fastDecay_moll' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.dFlowQN_clsQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.alt_hDclsQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.drift13_fastDecay_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.altB4N_fastDecay_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.altB5N_fastDecay_moll_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.dFlowQN_clsQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QDriftBInst.alt_hDclsQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Statements against the pinned check-file Props (`python3 extract.py diff`; whitespace-normalised text equality)
```
drift13_fastDecay Lean statement == check-file Prop (whitespace-normalised): True
altB4N_fastDecay Lean statement == check-file Prop (whitespace-normalised): True
altB5N_fastDecay_moll Lean statement == check-file Prop (whitespace-normalised): True
dFlowQN_clsQN Lean statement == check-file Prop (whitespace-normalised): True
alt_hDclsQN Lean statement == check-file Prop (whitespace-normalised): True
$ lake env lean stmt.lean   # = docs/tickets/checks/T2263-check.lean (unchanged) + `import RBM3D.Induction.QDriftB` + the five lines below
example : RBM.Ind.T2263Check.T2263_x := @RBM.Ind.x     -- x = drift13_fastDecay, altB4N_fastDecay, altB5N_fastDecay_moll, dFlowQN_clsQN, alt_hDclsQN
exit=0, error lines: 0
```

### Target statements, extracted from `RBM3D/Induction/QDriftB.lean` (whitespace-collapsed; `python3 extract.py stmt`)
```
== drift13_fastDecay (Lean, whitespace-collapsed):
∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {m n : ℕ} {E u Γ Λ Φ τ' ε' D' : ℝ} {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (σ : Fin (m + 1) → Bool), (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → H ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D' → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b)
== altB4N_fastDecay (Lean, whitespace-collapsed):
∀ (d m : ℕ) (Λg K C c C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < C → 0 < c → 0 < ε' → ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool), |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K → STMollifierProps (d := d) (sz.lam n) C c ϑ → ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4N sz n E u ϑ σ H)
== altB5N_fastDecay_moll (Lean, whitespace-collapsed):
∀ (d m : ℕ) (K C₀ ε' D' : ℝ), 0 < ε' → ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1) → Bool), 0 < sz.lam n → W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K → ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB5N sz n E u (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ H)
== dFlowQN_clsQN (Lean, whitespace-collapsed):
∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ (m : ℕ) (K C c C₀ ε' D' : ℝ), 0 < C → 0 < c → 0 < ε' → ∀ {n : ℕ} {E u Γ Λ Φ τ' Dc : ℝ} {uu : ℕ → ℝ} {i : ℕ}, QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) → |E| ≤ 2 → 0 < sz.lam n → 0 ≤ u → u < 1 → ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) (uu i) → ∀ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}, H ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D' → ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), STMollifierProps (d := d) (sz.lam n) C c ϑ → (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) → ∀ (σ : Fin (m + 1) → Bool), ‖fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4N sz n E u ϑ σ H) → EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB5N sz n E u ϑ σ H) → altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc uu i (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (dFlowQN sz n E u ϑ σ H)
== alt_hDclsQN (Lean, whitespace-collapsed):
∀ (d m : ℕ) (Λg K C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' → ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ), |E n| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K → 0 ≤ s n → s n ≤ v n → v n < 1 → (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K → (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → 4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) → (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈ sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1) (Γ n) (Λ n) (Φ n) τ' D') → (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) → (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → ‖fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) → ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω)
```

### Compiled nonempty instances (namespace `RBM.Ind.QDriftBInst`; statements extracted by script, proofs in the file; each is a theorem, exit 0, standard axioms above)
```
-- drift13_fastDecay_instance (QDriftB.lean:760):
∃ n : ℕ, (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈ sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) 6 ∧ (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧ ∀ σ : Fin (3 + 1) → Bool, EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 6 (fun b : Fin (3 + 1) → Zd 3 (sz0.L n) => driftTensorN sz0 n 0 0 (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) σ b)
-- altB4N_fastDecay_instance (QDriftB.lean:781):
∃ n : ℕ, (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧ ∀ σ : Fin (3 + 1) → Bool, EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 6 (altB4N sz0 n 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
-- altB5N_fastDecay_moll_instance (QDriftB.lean:804):
∃ n : ℕ, (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧ ∀ σ : Fin (3 + 1) → Bool, EKFastDecay (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) 6 (altB5N sz0 n 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
-- dFlowQN_clsQN_instance (QDriftB.lean:828):
∃ n : ℕ, (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈ sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) 6 ∧ (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf b : ℝ)) ∧ ∀ σ : Fin (3 + 1) → Bool, altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (fun _ => 0) 1 (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ))) (dFlowQN sz0 n 0 0 (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
-- alt_hDclsQN_instance (QDriftB.lean:878):
∃ n : ℕ, (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (0 + 1)) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf b : ℝ)) ∧ ∀ (σ : Fin (3 + 1) → Bool) (ω : PathΩ sz0), altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n) (0 + 1) (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ))) (dGridQN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ 0 ω)
```

### Level-free check (ticket preflight (iii)), `python3 level.py`
```
drift13_fastDecay: forbidden-name hits=[]; standalone Γ/Λ/Φ tokens=6; left after removing GoodSetN memberships and binders=0
altB4N_fastDecay: forbidden-name hits=[]; standalone Γ/Λ/Φ tokens=0; left after removing GoodSetN memberships and binders=0
altB5N_fastDecay_moll: forbidden-name hits=[]; standalone Γ/Λ/Φ tokens=0; left after removing GoodSetN memberships and binders=0
dFlowQN_clsQN: forbidden-name hits=[]; standalone Γ/Λ/Φ tokens=6; left after removing GoodSetN memberships and binders=0
alt_hDclsQN: forbidden-name hits=[]; standalone Γ/Λ/Φ tokens=6; left after removing GoodSetN memberships and binders=0
whole file, comments stripped, occurrences: {'STXiLK': 0, 'STXiLKM': 0, 'STsupXiLK': 0, 'STNQConcl': 0, 'STXiBoot': 0, 'goodExitTauN': 0, 'STAlternating': 0, 'Prec': 0, 'Lift': 0}
```

### Name clashes and registry pre-check
```
$ (main worktree) grep -rn -F -e drift13_fastDecay -e altB4N_fastDecay -e altB5N_fastDecay_moll -e dFlowQN_clsQN -e alt_hDclsQN -e QDriftBInst -e QDriftB_ RBM3D RBM3D.lean --include='*.lean' | wc -l
       0
$ (branch) the same grep on RBM3D/Induction/QDriftB.lean | wc -l      # sanity: the grep sees the names
      56
$ lake env lean registry.lean   # import RBM3D; import RBM3D.Induction.QDriftB; #assert_rbm_axioms
axiom audit: 7730 theorems, 2573 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
exit=0; last line of output: non-vacuity certificates: 0 of 159 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
```
No port from `../RBM1D` or `../RBM2D`: `grep -n "RBM2D\|RBM1D" QDriftB.lean` has one hit (line 18, a comment citing the pattern `AltEnd.lean:254-264` at `c9a24cf`, read with `git show c9a24cf:RBM2D/Induction/AltEnd.lean`); no diff-stat. The copies of target 1 and of the instance helpers come from the merged `QDriftA.lean` (88ee6fd).

### Narrative
File: `RBM3D/Induction/QDriftB.lean` (new, 951 lines), on `t/T2263` (hash above); the only file in `git diff --name-only main...t/T2263`. `RBM3D/Test/Axioms.lean` is untouched: the five public statements take no new `Prop` and the registry pre-check above exits 0. I did not run the full `lake build` (the root import is added by the hub at merge, CLAUDE.md §2 (A) 5).
Layout: §1 copies of the two private helpers (lines 49-81); §2 private bookkeeping (82-146); targets 2-6 (147-437); §8 instances (438-947). All five target statements equal the check-file Props after whitespace normalisation (script above) and `example : T2263_x := @x` compiles for each.
Section (a) is not edited and there is no (a′): I found no mistake that changes a verdict. Its remark that `C₀+Km+1` does not dominate the `ΘA` crude sup at `m = 0` does not arise: target 3 uses two exponents, `C₀+K·m+1` for `A−𝒬A` (line 212, the input of `QopDecay_ThetaN_fastDecay`, line 187) and `C₀+K+1` for `ΘA` (line 228, the input of `stQop_sub_fastDecay`, line 186), so no argument `K ≥ 0` is needed.
Target 1: `QDriftB_window_of_diamInf` and `QDriftB_W0_spec` are copies of `QDriftA_window_of_diamInf` (`QDriftA.lean:389`) and `QDriftA_W0_spec` (`:409`) of the merged file (88ee6fd).
Target 2 (`drift13_fastDecay`): `fastDecay_of_diamInf` applied to the merged `driftTensorN_far_of_goodSet` (`NQGood1.lean:131`), which uses the 8th component of `GoodSetN` (`GridGoodN.lean:142-146`, the clause the ticket calls (Vb)); no threshold.
Target 3 (`altB4N_fastDecay`): `W₀ = max(Wa, Wb, Wc, C(2^{dm}+1), m+1, 2)`, with `Wa`, `Wb` the thresholds of `stQop_sub_fastDecay` at `(C₀, ε'/2, D'+K+2)` and `(C₀+K+1, ε', D'+1)`, `Wc` that of `QopDecay_ThetaN_fastDecay` at `(m+1, Λg, K, C₀+Km+1, ε'/2, D'+K+2)`. The identity `ℬ₄ = Θ(A−𝒬A) − (ΘA−𝒬ΘA)` is `QopAlgebra_ThetaN_sub` plus the definition of `altB4N` (line 255); `‖𝒫A‖ ≤ ((2^d)^m+(L^d)^m)W^{C₀}` is `B45_Psum_le` at `R = 0` (private `QDriftB_Psum_crude`); `‖ϑ‖ ≤ C` follows from clause 2 of `STMollifierProps` with `ℓ ≥ 1` (private `QDriftB_mollifier_norm_le`); `‖ΘA‖ ≤ (m+1)(1−u)⁻¹W^{C₀}` is `B45_norm_ThetaN_le`; the last step is `2W^{-(D'+1)} ≤ W^{-D'}` for `W ≥ 2`.
Target 4 (`altB5N_fastDecay_moll`): `B = −𝒫A`, `‖B‖ ≤ W^{C₀+Km+1}` (same absorption, `W₀ = max(Wd, (2^d)^m+1)`), then `QopDecay_deriv_fastDecay` (line 289); the statement needs no `3 ≤ d`.
Target 5 (`dFlowQN_clsQN`): sum-zero from `dFlowQN_sumZero`; `ℓ_{uu i}W^{ε'} ≤ diam_∞ b` gives `ℓ_uW^{ε'} ≤ diam_∞ b` by `hℓ`, then a pair by the window copy; `|𝒬_u block| ≤ 2W^{-D'}` from the `QDriftA_W0_spec` copy with target 2; `|ℬ₄|, |ℬ₅| ≤ W^{-D'}` are hypotheses; total `4W^{-D'}`.
Target 6 (`alt_hDclsQN`): `W₀ = max(QDriftA_W0 d m K Cm (1/2) C₀ ε' D', W₃, W₄)`, `W₃`, `W₄` from targets 3, 4 at `Cm = (1+40dm)6^{dm}`; `dGridQN_eq_dFlowQN` (line 415), index shift `ℓ_{u_j} ≤ ℓ_{u_{j+1}}` by `ellT_mono`, `ST_gridTime_mono`, `ST_gridTime_mem` (line 422), `(1−u_j)⁻¹ ≤ (1−v_n)⁻¹ ≤ W^K` (line 425), then target 5 (line 430).
Instances (namespace `QDriftBInst`; data of the merged `QDriftAInst`: `sz0`, `d = 3`, `m = 3`, `K = 2`, `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 6`, `Dc = 3`, `E = 0`, `u = 0`, `H = 0 ∈ GoodSetN` at levels `(4,100,1)`, explicit mollifier): every hypothesis is discharged, none is left open. The private numeric helpers are copies from `QDriftA.lean:715-806, 808-857, 864-869, 891-892, 1150-1209`; new are `ellT_eq_one`, `crude_block` (lines 680-716: the block crude sup `≤ 304·B⁴ ≤ W⁷` from `driftTensorN_norm_le_of_goodSet`, discharged), `inst_data`, `x_le_W`, `hDD_inst`. Every instance is stated `∀ σ`, so alternating and non-alternating sign vectors are both covered. The window of `EKFastDecay`/`altClsQN` is shown to be attained by a tuple (not vacuous).
Instance for target 6: the walk `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4`, `τ ≡ 1` at `j = 0` (so `H_0 = 0`, `u_1 = 1/8`), every path `ω`.

## (c) Verified Mathlib names used (all `#check`ed in `names.lean`, exit 0; no name checked and found absent)
```
pi_norm_le_iff_of_nonneg : ∀ {ι : Type u_1} {G : ι → Type u_2} [inst : Fintype ι] [inst_1 :
norm_le_pi_norm : ∀ {ι : Type u_1} {G : ι → Type u_2} [inst : Fintype ι] [inst_1 :
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_one : ∀ (x : ℝ), x ^ 1 = x
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_two : ∀ (x : ℝ), x ^ 2 = x ^ 2
Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Real.exp_le_one_iff : ∀ {x : ℝ}, Real.exp x ≤ 1 ↔ x ≤ 0
Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.le_sqrt' : ∀ {x y : ℝ}, 0 < x → (x ≤ √y ↔ x ^ 2 ≤ y)
pow_le_one₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder 
inv_le_one_of_one_le₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrd
one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder 
pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder 
le_mul_of_one_le_right : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b :
div_nonpos_of_nonpos_of_nonneg : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrd
inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrd
norm_add₃_le : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] {a b c : E}, ‖a +
norm_sub_le : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a b : E), ‖a - b
norm_neg : ∀ {E : Type u_1} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ = ‖
norm_mul : ∀ {α : Type u_1} [inst : Norm α] [inst_1 : Mul α] [NormMulClass 
le_self_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder 
div_le_one : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] 
max_eq_right : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → max a
min_eq_left : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → min a
mul_le_mul_of_nonneg_left : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preo
mul_le_mul_of_nonneg_right : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preo
mul_le_mul : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preo
Finset.exists_mem_eq_sup : ∀ {α : Type u_1} {ι : Type u_2} [inst : LinearOrder α] [inst_1 :
Finset.sum_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1
Filter.eventually_ge_atTop : ∀ {α : Type u_1} [inst : Preorder α] (a : α), ∀ᶠ (x : α) in Filt
Nat.le_ceil : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [i
dite_eq_left_of_eq_true : ∀ {α : Sort u_1} {c : Prop} {x : Decidable c} {t : c → α} {e : ¬
Classical.choose_spec : ∀ {α : Sort u_1} {p : α → Prop} (h : ∃ x, p x), p (Classical.cho
Nat.one_le_iff_ne_zero : ∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
Pi.sub_apply : ∀ {ι : Type u_1} {G : ι → Type u_2} [inst : (i : ι) → Sub (G i)]
Real.log_two_lt_d9 : Real.log 2 < 0.6931471808
Real.sqrt_one : √1 = 1 
```

## (d) Open issues and paper-delta candidates
1. The crude sups of `𝒜 = (𝓛-𝒦)_{u_j,σ}(H_j)` and of the block on `{j < τ}` are hypotheses of targets 5-6 (ticket Open 1, T2250 Open 1). The instances discharge both at `H = 0` (`crude_sup`, `crude_block`); S3-18a must supply them from its levels.
2. S3-18a must also supply `L^d ≤ W^K`, `(1−v_n)⁻¹ ≤ W^K`, `W_n ≥ W₀`, `d W^{τ'} ≤ W^{ε'}` and `4W^{-D'} ≤ W^{-Dc}` as hypotheses of `alt_hDclsQN`; with `D' = 6`, `Dc = 3` the last one holds for `W ≥ 4` (`hDD_inst`).
3. Witnesses are astronomically large: each `W₀` is the existential threshold of the merged `stQop_sub_fastDecay`, `QopDecay_*`, `QDriftA_W0`; section (a) puts the last growth crossing at `log₁₀ W ≈ 40.5` for `ε' = 1/5`. The instances therefore take an existential `n` with `W_n ≥ W₀` (the device of `QDriftAInst`); this is the shape of the merged statements, not a defect of the five targets.
4. Naming: the clause the ticket calls (Vb) (8th component of `GoodSetN`, `GridGoodN.lean:142-146`) is bound as `hVa` in `driftTensorN_far_of_goodSet` (`NQGood1.lean:131`) and called (Va) in the docstring of `GoodSetN`; the same clause, no effect on any statement.
5. Paper-delta candidate `T2263a`: the decay of `ℬ₄` needs only the crude sup of `(𝓛−𝒦)` (commutator form `Θ(𝒫A·ϑ) − (𝒫ΘA)ϑ`; `(𝒫X)ϑ` decays super-polynomially, `Θ^{(n)}` transfers decay: S6-09c). Paper `(y27kasdfg)`/`(A4)` (`3_5:1692-1706`, read) gives the sup norm only, while `(eq:alternatecase2)` (`3_5:1711-1714`) applies `(sum_res_2)`, which needs decay. Cf. D556 = T2239a (ticket).
6. `T2263b`: the drift class radius is the initial-term radius `ε'` of `goodSetN_A0clsQN`, with `δD = 4W^{-D'}` (`2` from `𝒬_u(ℬ₁₋₃)`, `1+1` from `ℬ₄`, `ℬ₅`); only `ℬ₁₋₃` uses the good set (`3_5:1337-1346` defines `ℬ₀,…,ℬ₅`).
7. `T2263c`: targets 3 and 4 carry `L^d ≤ W^K` (already T2059a in the docstring of `stQop_sub_fastDecay`) and `(1−u)⁻¹ ≤ W^K` as hypotheses, and every threshold is an existential `W₀` chosen before `W`.

Tue Oct  6 07:00:05 UTC 2026 — end of report
