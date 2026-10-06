Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 04:11:15 UTC 2026

Notation: `k = m+1 ≥ 2`, `W = sz.W n`, `g = sz.lam n`, `r_{s,t} = (g²+|1−s|)/(g²+|1−t|)`, `B = sz.Bctl = W^{-d}Bparam(·,0)` (`Defs/Sizes.lean:214`, `Bparam` `Defs/Params.lean:36`), `C = (1+40dm)6^{dm}`, `c = 1/2` (`QopAlgebra_mollifier_props`, `QopAlgebra.lean:511`), `C₄ = qProxy4C` (`QProxy.lean:444`). Tables use `d = 3`, `W = L = N^{1/6}` (`𝔠 = 1/6`, `K = 1/𝔠 = 6`), `g = Λg = 1`; `ε₀ = 0.1` is an illustrative total loss chosen for the tables only.

### (i) Exponent table

| constant | value / source | constraint | slack |
|---|---|---|---|
| `C₄` | `Classical.choose` of `ekSumDecay2_holds` at `(d,k,Λg,κ',K)`, `3 ≤ d`, `2 ≤ k`; conclusion `W^{C₄ε} r^k ‖A‖ + W^{-D+C₄}` (`Evolution/Pins.lean` `EKSumDecay2`, exponent `n = k`) | fixed before `ε`; occurs only in conclusions (5a, 5b, `kappaAltQN`, `epsAltQN`), in no hypothesis | exponent of `r` is `k` (not `k−1`, the non-alt EK-6 value) |
| `C`, `C_n` | `C = 2.6136e4 / 1.1244e7 / 2.8258e14` at `m = 1/2/5`; `C_n = C+2dm+Km` (`QopNorm.lean:259-261`) | before `ε', D'`; enters only `W₀` | table E |
| `ε` | `ε = 1.5ε₀/C₄` makes `W^{C₄ε} = N^{ε₀/4}`; `0<ε<1`, `4 ≤ W^ε`, `log L ≤ W^ε` | `N ≥ N*` | table A, `log10 N*` for `4 ≤ W^ε` (`N*` huge for `C₄ ≥ 5`: eventual in `n`, as T2194) |
| `ε', τ'` | `τ' < ε' < ε`; `ε' = ε/2`, `τ' = ε/4` | `d W^{τ'} ≤ W^{ε'}` (4c; (Dec) radius `τ'` → `ℓ¹` window `ε'`), `d W^{ε'} ≤ W^{ε}` (5b with class radius `ε'`) | table A, last two `log10 N*` columns; binding: `W^{ε/4} ≥ d`, i.e. `log10 N* = 24 log10 3/ε` |
| `K` | `K = 1/𝔠 = 6` | `L^d ≤ W^K` (4b, 5a, 5b, 6) | `W=L=N^{1/6}`: `L³ = W³ ≤ W⁶`, slack `W³` |
| `C₀` | crude sup exponent of target 6, any real | chosen after `C₄, ε'`, before `D', W₀`; enters only `W₀` through `p = C₀+Km+D'` | not in the budget (table D) |
| `D', Dc` | `Dc > 1` (5b); `2W^{-D'} ≤ W^{-Dc}` | `D' > Dc`, `W ≥ 2^{1/(D'−Dc)}`; budget `ε_{0,j}·2W^{-D'} = 2W^{C₄−D'} ≤ B_{u_j}^k` iff `D' ≥ C₄+dk+log_W(2(1+Λg²)^k)` (`B_{u,0} ≥ 1/(1+g²)` since `|1−u| ≤ 1`) | table B; `D'` is free, chosen after `C₄` |
| `W₀` | `W₀(d,m,K,C,c,C₀,ε',D')` of `stQop_sub_fastDecay` (`QopNorm.lean:378`), via `C W^p ≤ exp(cW^{ε'}/2)`, `p = C₀+Km+D'` | `W ≥ W₀` last (existential: only the explicit growth inequality can be checked) | table E: `log10 W₀ ≈ 6.3–7.5` at `ε' = 0.5` |
| `κ_{0,j}M₀` | `M₀ = Λ₀ B_{u_0}^k` (level, S3-16a/18a): `W^{C₄ε} r^k Λ₀ B_{u_0}^k ≤ W^{C₄ε} Λ₀ B_{u_j}^k` | `r_{u_0,u_j} B_{u_0} ≤ B_{u_j}` (`nqGood2_ratio_mul_Bctl_le`), exponent `k` on both sides | table C: `B_{u_j}/(r B_{u_0}) ≥ 1`, `= 1.0010` at `N = 10⁶` |
| crude `M = W^{C₀}` | hypothesis of target 6, used only for 4b | **cannot** be the `M` of `hker` in the budget: `κ_{0,j}W^{C₀}/B^k ≥ N^{(C₀+C₄ε)/6 + k/2}` | table D, ratio `> 0` in `log_N` (finding for S3-18a/S3-16a) |
| window class | `ℓ_{u_i} W^{ε'} ≤ ⌊L/2⌋` for a nonvacuous radius | `ℓ_u = min(max(g/√(1−u),1),L)` (`Defs/Params.lean:32`); at `u = 1−g²/L²` `ℓ = L`, the class is vacuous (sum-zero only) | instance below |
| boundary (iv) | `0 ≤ s`, `t ≤ 1−g²/L²` (5a/5b; case (i) only), `W⁻¹ ≤ (1−t)/(1−s)`, `κ' ≤ Im mE`, `|E| ≤ 2`, `4 ≤ W^ε`, `log L ≤ W^ε`; `0 ≤ u_i < 1` (4b, 6, 3) | per matrix / per grid time, no `Prec`, no lift; the class radius changes `τ' → ε'` across `𝒬_{u_0}` (for S3-15b, S3-18a) | instance below |

The `DifferentiableAt` hypothesis of target 3 is harmless but not needed: if `t ↦ ϑ_{t,a}` is not differentiable at `u`, Lean's `deriv` is `0`, so `ℬ₅ = 0` and `𝒫ℬ₅ = 0` anyway.

```
$ python3 $S/tab.py   (abridged: selected rows, verbatim)
A: eps0=0.1, W=L=N^(1/6) (W>=N^c minimal), eps=1.5*eps0/C4 so log_N W^(C4 eps)=eps0/4; eps'=eps/2, tau'=eps/4
 C4    eps   log_N W^(C4 eps)  log10N*(4<=W^eps)  log10N*(d<=W^(eps/2))  log10N*(d W^tau'<=W^eps')  W^eps(N=1e6)
 0.5   0.3000 0.0250                 12.0               19.1                 38.2              1.9953
 20    0.0075 0.0250                481.6              763.4               1526.8              1.0174
B: min_j B_{u_j}^k >= (W^-d/(1+g^2))^k ; D'_min = C4 + d*k + log_W(2(1+g^2)^k) so that eps_{0,j}*2W^-D' = 2W^(C4-D') <= (W^-d/(1+g^2))^k
 N     W     m k  C4=0.5   1      5      20   (D'_min)
 10        1.468 1 2    11.9    12.4    16.4    31.4
 1000000  10.000 5 6    20.6    21.1    25.1    40.1
C: ratio B_{u_j}/(r_{u0,uj} B_{u0}) >=1 (nqGood2_ratio_mul_Bctl_le), d=3,g=1,W=L=N^(1/6)
 N=10       W=L= 1.468  (0,0.5): 1.19371  (0.5,0.9): 2.29822  (0,0.99): 20.17758
 N=1000000  W=L=10.000  (0,0.5): 1.00100  (0.5,0.9): 1.00798  (0,0.99): 1.09880
D: crude M=W^C0 in the budget does not close: log_N[ W^(C4 eps) W^C0 / B_0^k ] = (C0+C4 eps)/6 + k/2 + k ln(1/(W^3 B_0))/ln N, u=0, g=1, W=L=N^(1/6)
 N=1000000  m=1 k=2 C0=6 C4=5: log_N ratio = 2.125 (>0 means crude M cannot enter the budget)
 N=1000000  m=5 k=6 C0=6 C4=5: log_N ratio = 4.325 (>0 means crude M cannot enter the budget)
E: W0 = largest root of  ln C + p ln W = c W^eps'/2 (qn_growth, c=1/2, eps'=0.5), C=(1+40dm)6^(dm), p=C0+K m+D', C0=6, D'=C4+3k+5
 m=1 k=2 C=2.6136e+04 C4=0.5  D'= 11.5 p=  23.5  log10 W0 = 6.294
 m=5 k=6 C=2.8258e+14 C4=20   D'= 43.0 p=  79.0  log10 W0 = 7.494
```
Reading: at `N ≤ 10⁶` (`W ≤ 10`) `4 ≤ W^ε` fails for the tied `ε` (`W^ε = 1.0174..1.9953` at `N = 10⁶`), so every target is an eventual-in-`n` statement at fixed `ε`; the order `C₄, C_n → ε → ε', τ' → C₀ → D', Dc → W₀` has no circularity (`C₄` is in no hypothesis, `W₀` is last).

Verdicts: T2 (`dGridQN = dFlowQN`: unfold, `ring`; `ℬ₅`'s sign is inside `altB5N`) PASS. T3 (`𝒫ℬ₄ = 0` by `QopAlgebra_Psum_Qop` + `QopAlgebra_ThetaN_sumZero` with `‖mSigma‖ = 1`, `0 ≤ u < 1`; `𝒫ℬ₅ = 0` by `QopAlgebra_Psum_deriv`) PASS. T4a/4b/4c PASS (4b: `𝒬A = A − (A−𝒬A)`, `stQop_sub_fastDecay` at `(C₀, ε', D')`, bound `‖A b‖ + ‖(A−𝒬A) b‖ ≤ 2W^{-D'}`). T5a/5b PASS (EK-4 needs only `EKSumZero` + `EKFastDecay`, `‖mE‖ = 1`; `δ>0`: `D'' = −log_W δ ≥ D`, `δ = 0`: limit). T6 PASS with radius `ε'` (not `τ'`) and the crude-sup hypothesis. T7 PASS (finite sums of measurable `loopFine` terms, `ϑ` fixed; the private `gridGood_meas_*` exist at `GridGoodN.lean:255-346`). No target FAIL, none BLOCKED.

### (ii) One concrete nondegenerate instance

`d=3, m=3 (k=4), g=Λg=1, E=0 (Im mE = 1), κ'=1/2, K=6, L=10⁶, W=10⁷ (N=(WL)^d=10³⁹, W ≥ N^{1/6}), ε=0.9, ε'=0.6, τ'=0.3, C₀=6, D'=3, Dc=2, grid u=(0, 0.5, 0.99), Kg=2, s=0, t=0.99`; class `X = e_{(x,y,…)} − e_{(x,y',…)}` (sum-zero, supported at `diam_∞ < ℓ W^{ε'}`, `M = 1`, `δ = W^{-Dc}`), `σ` alternating and non-alternating (no `σ` hypothesis).
```
$ python3 $S/inst.py
OK   3<=d, 2<=k (k=m+1), 3<=L, 1<W: d=3 m=3 k=4 L=1e+06 W=1e+07
OK   0<Lg, 0<kappa', 0<K, 0<g<=Lg
OK   |E|<=2 and kappa'<=Im mE: E=0.0 Im mE=1.0
OK   0<eps<1, 4<=W^eps: W^eps=1.995e+06
OK   log L <= W^eps: 13.82 <= 1.995e+06
OK   L^d <= W^K (K=6=1/c): log10 L^d=18 <= log10 W^K=42
OK   W >= N^c, c=1/6 (N=(WL)^d): log10 N=39.0, log10 N^c=6.50 <= 7.00
OK   d W^tau' <= W^eps' (4c, 6): 377.7 <= 1.585e+04
OK   d W^eps' <= W^eps (5b at class radius eps', 6->5b): 4.755e+04 <= 1.995e+06
OK   tau'<eps'<eps<1
OK   grid: 0<=u_i, u monotone, u_Kg<=1-g^2/L^2: u=[0.0, 0.5, 0.99]
OK   W^-1 <= (1-u_Kg)/(1-u_0): 1e-07 <= 0.01
OK   5a: s<=t<=1-g^2/L^2, W^-1<=(1-t)/(1-s)
OK   5a: 1<D (D=Dc), 0<=delta<=W^-D, M>=0: delta=1e-14<=W^-Dc=1e-14
OK   Cls window nonvacuous at u=0.0: ell_u W^eps' <= floor(L/2): ell=1 radius=1.585e+04 <= 500000
OK   Cls window nonvacuous at u=0.5: ell_u W^eps' <= floor(L/2): ell=1.41 radius=2.241e+04 <= 500000
OK   Cls window nonvacuous at u=0.99: ell_u W^eps' <= floor(L/2): ell=10 radius=1.585e+05 <= 500000
OK   6: 2 W^-D' <= W^-Dc, 1<Dc: 2e-21 <= 1e-14
OK   6: 0<=u_i<1 for all grid times
OK   6: 1<=m, mollifier consts C=(1+40dm)6^dm, c=1/2: C=3.638048e+09 c=0.5
OK   4b/6: explicit growth C W^p <= exp(c W^eps'/2), p=C0+Km+D'  (sufficient condition used by qn_growth; W0 itself is existential): p=27.0: ln(C W^p)=457.2 <= c W^eps'/2=3962
OK   growth holds for all W>=W1 with log10 W1 < log10 W: log10 W1=5.238 < 7
ALL OK
```
The `W ≥ W₀` hypothesis is existential in 4b/6; the line "explicit growth" is the inequality `W₀` is built from (`qn_growth`), holding at `W = 10⁷` and for every larger `W`. External hypotheses: none (EK-4 pins are merged theorems; `C₄` is in no hypothesis).

Sum-zero of `ℬ₄, ℬ₅` at `k = 2` by hand: `ℬ₄(a) = Θ((𝒫A)(b₀)ϑ)(a) − (𝒫Θ𝒜)(a₀)ϑ(a)` (`QopAlgebra_commutator_ThetaN`). Sum over `a₁` using `Σϑ = 1`: slot 0 gives `Σ_c K₀(a₀,c)(𝒫A)(c)`, slot 1 gives `(𝒫A)(a₀)κ₁` with the constant column sum `κ₁ = μ₁/(1−tμ₁)`; `𝒫Θ𝒜(a₀)` is the same two terms, so `𝒫ℬ₄ = 0` for every `u ∈ [0,1)`, including `u = 0` (no derivative in `ℬ₄`). `𝒫ℬ₅(a₀) = −(𝒫A)(a₀) ∂_u Σ_{a₁}ϑ = 0`. Numerically (random `A`, definitions `SB`, `Theta = (1−ξSB)⁻¹`, `thetaKer`, `ThetaN`, `STQop` transcribed; `ϑ` an explicit family smooth across `u = 0`; `|P B5| ~ 1e-9` is the central-difference error):
```
$ python3 $S/alg.py | cut -c1-230   (rows 1, 3, 4)
d=3 L=3 k=2 sigma=[True, False] E=0.5 u=0.0: |A|=3.79 max|P th-1|=4.5e-16 |P B4|=3.8e-15 |P B5|=1.7e-09 |P drift|=1.7e-09 |B4|=0.30 |B5|=0.55 |Q B4-B4|=1.9e-16 |Q B5-B5|=8.5e-11
d=3 L=3 k=2 sigma=[True, True] E=0.5 u=0.6: |A|=3.51 max|P th-1|=3.3e-16 |P B4|=5.1e-15 |P B5|=1.6e-09 |P drift|=1.6e-09 |B4|=0.18 |B5|=0.57 |Q B4-B4|=2.2e-16 |Q B5-B5|=7.5e-11
d=1 L=5 k=3 sigma=[True, False, True] E=-1.2 u=0.0: |A|=3.09 max|P th-1|=2.2e-16 |P B4|=4.3e-15 |P B5|=5.4e-10 |P drift|=5.4e-10 |B4|=0.16 |B5|=0.30 |Q B4-B4|=2.3e-16 |Q B5-B5|=3.0e-11
```
Level-free check (iii) on the check file's §3 statements (no level, no `STAlternating`, no `Γ Λ Φ` binder; `Λg` is the coupling bound):
```
$ sed -n '/^\/-! ## 3/,$p' docs/tickets/checks/T2250-check.lean | grep -v '^--\|^/--' | grep -nE "STXiLK|STXiLKM|STsupXiLK|STNQConcl|STXiBoot|goodExitTauN|STAlternating|Prec |GoodSetN|[ (]Γ[ )]|[ (]Λ[ )]|[ (]Φ[ )]|∀ᶠ"; echo "exit=$?"
exit=1
```
`STAlternating` is needed by no target (EK-4 needs none); it occurs in the pins `STWardTypeP`, `STB45` (`Step34Pins.lean:549,560`), so only a consumer of those needs it.

### (a′) Preflight corrections — Tue Oct  6 04:38:54 UTC 2026

One sentence of (a) is wrong, and it changes no verdict and no pinned statement: "The `DifferentiableAt` hypothesis of
target 3 is harmless but not needed: if `t ↦ ϑ_{t,a}` is not differentiable at `u`, Lean's `deriv` is `0`, so `ℬ₅ = 0`".
That holds only if the whole fibre `{a : a₀ = a₁}` is non-differentiable.  In the mixed case, e.g. a fibre with
`ϑ = (t, |t|, 1 - t - |t|)` at `u = 0` (sum `1`), the junk values give `Σ deriv = 1 ≠ 0` (by hand, not compiled), so
`𝒫ℬ₅ ≠ 0` can occur.  The hypothesis is used by `dFlowQN_sumZero` (`QopAlgebra_Psum_deriv` needs `HasDerivAt` for every `a`).

## (b) Script output — Tue Oct  6 04:42:43 UTC 2026

```
$ git log -2 --format='%h %an: %s' ; git diff --stat main...t/T2250
51c7e4a Jun Yin: T2250: discharge STKbound in the target-6 instances (stKbound_holds)
c08a0c0 Jun Yin: T2250: S3-15a Induction/QDriftA (drift and initial term of the Q-process, alternating chain, d >= 3)
 RBM3D/Induction/QDriftA.lean | 1341 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1341 insertions(+)
$ lake build RBM3D.Induction.QDriftA 2>&1 | grep -E 'QDriftA|Build completed|error'     (warnings in QDriftA.lean: 0)
Build completed successfully (3846 jobs).
$ printf 'import RBM3D\nimport RBM3D.Induction.QDriftA\n#assert_rbm_axioms\n' > precheck.lean ; lake env lean precheck.lean   (registry pre-check; first and last output line)
axiom audit: 7500 theorems, 2522 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 157 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceSha
exit=0   (Test/Axioms.lean untouched: registry diff empty)
$ lake env lean ax.lean   # `#print axioms` of the 41 public declarations of QDriftA.lean, grouped
40 declarations: [propext, Classical.choice, Quot.sound]
1 declarations: [propext, Quot.sound]
sorryAx in output: False
```
`#print axioms` of the 41 public declarations (6 vocabulary, 7 pinned targets, `QDriftA_W0`, `QDriftA_W0_gt_one`, targets 6 (2) and 7 (4),
20 in `QDriftAInst`): all `[propext, Classical.choice, Quot.sound]` except `QDriftAInst.sigma_alt_and_nonalt` (`[propext, Quot.sound]`).
Targets 2-5, pinned statements:

```
$ (scratch file: `import RBM3D.Induction.QDriftA`; check file lines 141-229 (the 7 `T2250_*` Props); then:)
$ grep 'theorem chk_' chk_statements.lean ; lake env lean chk_statements.lean ; echo exit=$?
theorem chk_dGridQN_eq_dFlowQN : T2250_dGridQN_eq_dFlowQN := @dGridQN_eq_dFlowQN
theorem chk_dFlowQN_sumZero : T2250_dFlowQN_sumZero := @dFlowQN_sumZero
theorem chk_aTrueQN_sumZero : T2250_aTrueQN_sumZero := @aTrueQN_sumZero
theorem chk_Qop_fastDecay : T2250_Qop_fastDecay := @Qop_fastDecay
theorem chk_fastDecay_of_diamInf : T2250_fastDecay_of_diamInf := @fastDecay_of_diamInf
theorem chk_hker_altQN : T2250_hker_altQN := @hker_altQN
theorem chk_alt_hkerQN : T2250_alt_hkerQN := @alt_hkerQN
exit=0
$ diff <(sed -n 90,139p docs/tickets/checks/T2250-check.lean) <(sed -n 56,105p RBM3D/Induction/QDriftA.lean) ; echo exit=$?
exit=0      (the six §2 definitions are verbatim)
```
Targets 6, 7 (shape free by the ticket; extracted by `python3 stmts.py print ...` from the file, docstrings dropped; 7a-7c have the
shape of 7d with `altB4N` / `altB5N` / `STQop … (Σ_l 𝒦∼(𝓛-𝒦) + ℰ^{LK×LK} + ℰ^{G̃})` in place of `dFlowQN`):
```
  theorem QDriftA_W0_gt_one (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
      1 < QDriftA_W0 d m K C c C₀ ε' D' :=
  theorem goodSetN_A0clsQN {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (m : ℕ)
      (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε')
      {n : ℕ} {E Γ Λ Φ τ' Dc : ℝ} {u : ℕ → ℝ} {i : ℕ}
      (hW : QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
      (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
      (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
      (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
      (hlam : 0 < sz.lam n) (hu0 : 0 ≤ u i) (hu1 : u i < 1)
      {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
      (hM : M ∈ sz.GoodSetN n E (u i) (m + 1) Γ Λ Φ τ' D')
      (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
      (σ : Fin (m + 1) → Bool)
      (hcrude : ‖fun a => sz.STLKM n E (u i) M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
      altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc u i
        (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
        (STQop (d := d) ϑ (u i) (fun a => sz.STLKM n E (u i) M σ a))
  theorem alt_hA0clsQN {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (m : ℕ)
      (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε')
      {n : ℕ} (σ : Fin (m + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
      (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ)
      (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
      (hW : QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ))
      (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K)
      (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε')
      (hDD : 2 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc))
      (hlam : 0 < sz.lam n) (hs0 : 0 ≤ s n) (hs1 : s n < 1)
      (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
      (hτG : ∀ ω j, j < τ ω → pathH sz s v Kg n j ω ∈ sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1)
        (Γ n) (Λ n) (Φ n) τ' D')
      (hcrude : ∀ ω, 0 < τ ω → ‖AvecN sz E s v Kg n 0 σ ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
      ∀ ω, 0 < τ ω →
        altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) 0
          (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (aTrueQN sz E s v Kg n ϑ σ 0 ω)
  theorem measurable_altB4N (E u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
      (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        altB4N sz n E u ϑ σ H a
  theorem measurable_dFlowQN (E u : ℝ) {m : ℕ} (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
      (σ : Fin (m + 1) → Bool) (a : Fin (m + 1) → Zd d (sz.L n)) :
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        dFlowQN sz n E u ϑ σ H a
```
Level-free check (iii), run on all target statements above (everything before `§7`):
```
$ grep -nE 'STXiLK|STXiLKM|STsupXiLK|STNQConcl|STXiBoot|goodExitTauN|STAlternating|Prec |∀ᶠ' stmts_all.txt ; echo exit=$?
exit=1
$ grep -nE 'Γ|Λ [^g]|Φ' stmts_all.txt        (all hits: the binders and the `GoodSetN` membership of targets 6a, 6b; none elsewhere)
75:    {n : ℕ} {E Γ Λ Φ τ' Dc : ℝ} {u : ℕ → ℝ} {i : ℕ}
82:    (hM : M ∈ sz.GoodSetN n E (u i) (m + 1) Γ Λ Φ τ' D')
93:    (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ)
102:      (Γ n) (Λ n) (Φ n) τ' D')
```
Compiled nonempty instances (`§7`, namespace `RBM.Ind.QDriftAInst`):
```
$ grep -n '^theorem [A-Za-z0-9_]*_instance\|^theorem sigma_alt_and_nonalt' RBM3D/Induction/QDriftA.lean
666:theorem dGridQN_eq_dFlowQN_instance :
675:theorem dFlowQN_sumZero_instance :
691:theorem aTrueQN_sumZero_instance : EKSumZero (aTrueQN sz0 E0 s0 t0 K0 0
696:theorem measurable_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
899:theorem Qop_fastDecay_instance :
944:theorem fastDecay_of_diamInf_instance :
1073:theorem hker_altQN_instance :
1110:theorem alt_hkerQN_instance :
1140:theorem sigma_alt_and_nonalt :
1218:theorem goodSetN_A0clsQN_instance :
1276:theorem alt_hA0clsQN_instance :
  theorem hker_altQN_instance :
      ∃ n : ℕ, Xsz n ≠ 0 ∧ (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
          ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
        ∀ (σ : Fin (3 + 1) → Bool) (a : Fin (3 + 1) → Zd 3 (sz0.L n)),
          ‖Ugen 3 (sz0.L n) (sz0.lam n) 0 σ 0 (1 / 2) (Xsz n) a‖ ≤
            ((sz0.W n : ℕ) : ℝ) ^ (qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * (1 / 5 : ℝ)) *
                (((sz0.lam n) ^ 2 + |1 - 0|) / ((sz0.lam n) ^ 2 + |1 - 1 / 2|)) ^ (3 + 1) * 1 +
              ((sz0.W n : ℕ) : ℝ) ^ qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * 0
  theorem goodSetN_A0clsQN_instance :
      ∃ n : ℕ,
        (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
          sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) 3 ∧
        (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
          ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
        ∀ σ : Fin (3 + 1) → Bool,
          altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 2 (fun _ => 0) 0
            (2 * ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)))
            (STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0
              (fun a => sz0.STLKM n 0 0 0 σ a))
  theorem dFlowQN_sumZero_instance :
      H1.IsHermitian ∧ H1 ≠ 0 ∧ STAlternating sigma4 ∧
      (∀ a₁ : Zd 3 (sz0.L 0), STPsum (d := 3) (altB4N sz0 0 0 (1 / 10) moll sigma4 H1) a₁ = 0) ∧
      (∀ a₁ : Zd 3 (sz0.L 0), STPsum (d := 3) (altB5N sz0 0 0 (1 / 10) moll sigma4 H1) a₁ = 0) ∧
      STQop (d := 3) moll (1 / 10) (altB4N sz0 0 0 (1 / 10) moll sigma4 H1) =
        altB4N sz0 0 0 (1 / 10) moll sigma4 H1 ∧
      STQop (d := 3) moll (1 / 10) (altB5N sz0 0 0 (1 / 10) moll sigma4 H1) =
        altB5N sz0 0 0 (1 / 10) moll sigma4 H1 ∧
      EKSumZero (dFlowQN sz0 0 0 (1 / 10) moll sigma4 H1)
```
Name clashes and ports:
```
$ for n in <the 21 new top-level names and QDriftAInst>; do grep -rnw --include='*.lean' "$n" RBM3D RBM3D.lean; done   (main worktree, HEAD 24b85cd)
(no name with a hit; 22 names checked)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git ... diff --stat c9a24cf HEAD -- RBM2D/Induction/AltDriftQ.lean
RBM2D HEAD 9e0f275
 RBM2D/Induction/AltDriftQ.lean | 1091 +++-------------------------------------
 1 file changed, 69 insertions(+), 1022 deletions(-)
```
Ports cited (source `RBM2D/Induction/AltDriftQ.lean` at `c9a24cf`, read with `git show`): `dFlowQ` `:86` (→ `dFlowQN`), `AltDriftQ_Psum_add/sub` `:95-102`
(→ private `QDriftA_Psum_add/sub`); `dGridQN_eq_dFlowQ` `:119-180` (target 2, an unfolding); `altQ_hker` `:203` (targets 5a, 5b);
`AltDriftQ_meas_*` `:407-513` (copies of the private `gridGood_meas_*`, `GridGoodN.lean:255-346`, prefix `QDriftA_`).  Other copies:
`nqGood1_fast_of_cls` (`NQGood1.lean:278`, target 4c), `hker_of_case1N` (`NQGood1.lean:310-376`, target 5a), `qProxy4C_spec`
(`QProxy.lean:519`), `nonAlt_hkerN` (`NQGood2.lean:252-282`, target 5b), `goodSetN_A0clsN` (`NQGood2.lean:284`, used in target 6),
`qProxyW0` (`QProxy.lean:456`, pattern of `QDriftA_W0`), the numeric/window lemmas of `QProxyInst` (`QProxy.lean:1634-1962`, instances).

Narrative.
* Proofs: target 2 unfolds `dGridQN`, `dFlowQN`, `altB4N`, `altB5N` and closes by `sub_eq_add_neg` (`AvecN` is defeq).  Target 3: `𝒫ℬ₄ = 0` from
  `QopAlgebra_Psum_Qop` and `QopAlgebra_ThetaN_sumZero` (`‖mSigma E b‖ = 1`, `0 ≤ u < 1`); `𝒫ℬ₅ = 0` from `QopAlgebra_Psum_deriv`; `𝒬_uℬ = ℬ` from
  `QopAlgebra_Qop_of_sumZero`; `EKSumZero` by the private `QDriftA_ekSumZero_of_Psum`.  4a: `QopAlgebra_Psum_Qop`.  4b: `𝒬A = A - (A - 𝒬A)` and `stQop_sub_fastDecay`.
  5a is the `δ`-argument of `hker_of_case1N` with EK-4 (`QDriftA_qProxy4C_spec`, `Ugen = UN (EKsgn (mE E) σ)` by `rfl`), exponent `k`, no `σ` hypothesis.
* Target 6 (shape chosen here): the threshold is the constant `QDriftA_W0` (`Classical.choose` of `Qop_fastDecay`), not an `∃ W₀` in the statement.  Reason from
  the tool log: with `∃ W₀` first, the registry scan reported `[RBM.Ind.altClsQN]` unclassified, because no theorem concluded with `altClsQN`; with the
  constant, `goodSetN_A0clsQN`, `alt_hA0clsQN` conclude with `altClsQN` (as `goodSetN_A0clsN` does for `nonAltClsN`) and the pre-check passes with no registry line.
* Hypotheses of 6a: `hd : 3 ≤ d`, `0 < sz.lam n` (not a `Sizes` field), `0 ≤ u i < 1`, the crude sup `‖A‖ ≤ W^{C₀}` (the ticket's hypothesis), `L^d ≤ W^K`,
  `d W^{τ'} ≤ W^{ε'}`, `2W^{-D'} ≤ W^{-Dc}`, `W ≥ QDriftA_W0`.  The ticket's `1 ≤ m` is not needed (`k = m+1`) and is omitted.  The class radius is `ε'`.
* Instances.  Targets 2, 3, 4a, 7 at `n = 0` (`QGridACheck` data; target 3 at `H = 1`, Hermitian and non-zero).  Targets 4b, 6 at an `n` with `W_n ≥` the
  threshold, 4c, 5a, 5b at `n = 9`: `x = 2(n+1)`, `W = x^5`, `L = 2x`, `ε = 1/5` (`W^ε = x`), `τ' = 1/10`, windows attained by `farb`, `K = 2`
  (`L^3 ≤ W^2`).  5a, 5b are stated for every `σ` (`sigma_alt_and_nonalt`: `(+,-,+,-)` alternating, `(+,+,+,+)` not), with `X = 1_0 - 1_{(0,e,0,0)}` (non-zero,
  sum-zero, support of `L^∞`-spread `≤ 1 < W^{τ'} ≤ ℓ W^{τ'}`), `M = 1`, `δ = 0`.
* Hypotheses of the instances: none open.  The instances of target 6 need `sz0.STKbound E0`, which is the proved `stKbound_holds` (`Loop/KLFinal.lean:243`,
  `κ = 1`, `gmax = 10`, `sz0_tendsto`); from it and `norm_loopFine_crudeN` they derive the crude sup `‖(𝓛-𝒦)_0(0)‖ ≤ 1 + 16 W^6 ≤ W^7`.  The values of `ℬ₄`, `ℬ₅`
  at `H = 1` are not computed (target 3's instance shows the structure, not a non-zero value).
* Not done and not claimed: the decay class of the drift (`hDcls`, S3-15b) and the levels (S3-16); `ℬ₄`, `ℬ₅` are only sum-zero and measurable here.

## (c) Mathlib names used (verified by the build; 26 of 30 found by a declaration grep in `.lake/packages/mathlib`, the other four by `#check`)

`Finset.exists_mem_eq_sup`, `Finset.sum_ite_eq'`, `Finset.sum_sub_distrib` (`#check`), `Finset.measurable_sum` (`#check`), `pi_norm_le_iff_of_nonneg`
(`#check`), `norm_le_pi_norm` (`#check`), `Real.rpow_logb`, `Real.logb_le_iff_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_natCast`,
`Real.rpow_add`, `Real.rpow_neg_one`, `Real.log_two_lt_d9`, `Real.log_le_sub_one_of_pos`, `Real.sqrt_eq_rpow`, `Real.le_sqrt'`, `Real.mul_self_sqrt`,
`le_self_pow₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `div_le_iff₀`, `Filter.eventually_ge_atTop`, `exists_nat_ge`,
`Matrix.isHermitian_one`, `Matrix.isHermitian_zero`, `Nat.le_ceil`, `le_of_forall_pos_le_add`, `ZMod.val_natCast`.  Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates

* `T2250a`: at `d ≥ 3` the drift `𝒬_u(ℬ₁+ℬ₂+ℬ₃) + ℬ₄ + ℬ₅` and the initial term `𝒬_{u_0}(𝓛-𝒦)` need no `ℚ/𝔼` split: `(sum_res_2)` needs only `EKSumZero` and `EKFastDecay`,
  for every `σ`, and the drift is sum-zero pathwise (`dFlowQN_sumZero`); RBM2D uses Case 3 (local forms) for the centred part and Case 4 with `AltExpSymm` for the mean.
* `T2250b`: the alternating `hker` weight is `W^{C₄ε} r^k` (exponent `k`, EK-4 constant `qProxy4C`, shared with S3-14) and `W^{C₄}` for the additive term (`hker_altQN`).
* `T2250c`: the class radius grows from `τ'` to `ε'` across `𝒬_{u_0}` (`L^∞` window of `GoodSetN` → `ℓ¹` window via `d W^{τ'} ≤ W^{ε'}`, then `stQop_sub_fastDecay`); the crude
  sup `‖(𝓛-𝒦)_{u_0}‖ ≤ W^{C₀}` is an input of `goodSetN_A0clsQN`, `alt_hA0clsQN`; the threshold `W₀` is a function of `(d, m, K, C, c, C₀, ε', D')` (`QDriftA_W0`) and needs `L^d ≤ W^K` (inherited from `T2059a`).
* `T2250d`: target 3 keeps the `DifferentiableAt` hypothesis (see (a′)): without it `𝒫ℬ₅ = 0` can fail in a mixed fibre.
* Open 1 (dispatcher, ticket Open issue 1): the source of the crude sup for a consumer (`η^{-k}`-type bound for Hermitian `H`, plus a bound on `𝒦` from `stKbound_holds` or
  S3-16a's levels) is still S3-16a/S3-18a's choice; the instances use `stKbound_holds` (its hypotheses `|E n| ≤ 2 - κ`, `0 < lam n ≤ gmax` are discharged at `sz0`).
* Open 2: the instance of target 3 does not exhibit a non-zero `ℬ₄` or `ℬ₅` (`H = 1` is Hermitian and non-zero; the value was not computed).
* Open 3 (for S3-18a): the `Cls` of `GridAssemblyHypN` is `altClsQN … ε' …` (radius `ε'`, from `goodSetN_A0clsQN`), so `alt_hkerQN` is applied with its `τ' := ε'`,
  which needs `d W^{ε'} ≤ W^{ε}` (its hypothesis `hdW`), as in the preflight table (row `ε', τ'`).
* Registry: expected and found diff empty (`altClsQN` is concluded by `goodSetN_A0clsQN`); full `lake build` is the hub's merge step.
