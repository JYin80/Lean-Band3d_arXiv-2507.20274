Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 16:21:11 UTC 2026

Notation: `k = m+1 ≥ 2`, `r = r_{v,w} = (g²+|1−v|)/(g²+|1−w|)`, `B = sz.Bctl`, `η_u = (1−u) Im m(E)` (`GLoop.lean:75`), `M_ee = Γ(ΓΛ)B_v^{2k}/η_v` (clause (D4) of `GoodSetN`, `GridGoodN.lean`), `δ` = level of clause (Vb).

### (i) Exponent table

| constant | value / source | constraint | slack |
|---|---|---|---|
| `C_n` | `C+2dm+Km` (`QopNorm.lean:260`); mollifier `C=(1+40dm)6^{dm}`, `c=1/2` (`QopAlgebra_mollifier_props`) | before `ε, D` | table C: `C_n = 3.6e9` at `m=3` (the grid `C_n ∈ {1/2,…,20}` of the ticket is unreachable for this mollifier) |
| `C₄` | `ekSumDecay2_holds` at `(d,k,Λg,κ',K)`, `k ≥ 2` | before `ε`; `κ₄ = W^{C₄ε} r^k` | abstract (appears only in conclusions) |
| `C_Q` | `2C_n+2` (derivation below) | depends on `(d,m,K,C)` only; before `ε, D` | needs `D > C_n+2` and `W ≥ 3` |
| order | `C_n, C₄, C_Q` → `ε` → `C₀, D` → `W₀` | `W₀ = W₀(d,m,K,C,c,C₀,ε,D)` (`stQop_sub_fastDecay`) | table C gives `log10 W₀` |
| T4 (i) | inner copy: `M₁ = W^{C_nε}M_ee + W^{-D+C_n}`; the whole slice of a spread `c` is `≤ δ ≤ W^{-D}` hence `EKFastDecay`, so `stQopNorm` gives block level `δ₁ ≤ 2W^{-D+C_n}`; outer `stQopNorm` at `D₁ = D−C_n−1` (`δ₁ ≤ W^{-D₁}` for `W ≥ 2`; `D₁>1` iff `D>C_n+2`) | `‖(𝒬⊗𝒬̄)T‖ ≤ W^{2C_nε}M_ee + W^{C_nε−D+C_n} + W^{−D+2C_n+1} ≤ W^{2C_nε}M_ee + W^{−D+C_Q}` | `W ≥ 2` (the sum of the two additive terms is `≤ W^{-D+2C_n+2}`) |
| T4 (iii) | `𝒬A = A − (A−𝒬A)`: `|A(b)| ≤ δ₁`, `A−𝒬A` is `EKFastDecay` at `(ε, D−C_Q+1)` by `stQop_sub_fastDecay` if `‖A‖ ≤ M₁ ≤ W^{C₀+C_n+1}` | `≤ 2W^{-D+C_n} + W^{-(D−C_Q)−1} ≤ W^{-D+C_Q}` | the pinned factor `(2+M_ee)` is weaker than needed (true, not needed) |
| T4 (ii) | `𝒬_b`, `𝒬̄_{b'}` commute (finite sums), so (ii) is (iii) with the roles swapped; exponent `D−C_Q` | `d W^{τ'} ≤ W^ε` converts the `L^∞` window of (Vb) to the `ℓ¹` window of `EKFastDecay` | — |
| T5 stages | one level `δ'` for slice decay (b') and block decay (b) (`δ' ≥ W^{-(D−C_Q)}`); `δ' ≤ W^{-D₂}`, `D₂ > k+1` | stage 1: `≤ κ₄M' + W^{C₄}δ'`; stage 2 far level `W^kδ'` (`norm_UN_apply_le`, `(1−s)/(1−t) ≤ W`), `D₃ = D₂−k > 1` | total `κ₄(κ₄M'+W^{C₄}δ') + W^{C₄}W^kδ'` (ticket formula confirmed) |
| row (1) | `κ₄²W^{2C_nε}M_ee = W^{2(C₄+C_n)ε}Γ²Λ (rB_v)^{2k}/η_v ≤ W^{2(C₄+C_n)ε}Γ²ΛB_w^{2k}/η_v` | `rB_v ≤ B_w` (`nqGood2_ratio_mul_Bctl_le`) with exponent `2k` on both sides: exact, no spare power needed | table E; the ticket's `Γ³Λ` overcounts by one `Γ` (D4 is `Γ(ΓΛ)`), harmless |
| row (2) | `Σ_{j<K}Δ/η_{u_{j+1}}`: left sum `≤ (Im m)⁻¹ log N` (`sum_gridStep_div_etaT_le`), right sum adds `Δ/η_{u_K}` | the `+1` needs `Δ ≤ (1−v) Im m`; `W ≤ N^{1/d}`: `W^{ε₀/4} ≤ N^{ε₀/12}`, `log N ≤ N^{ε₀/4}` | table F: `0.0333 ≤ ε₀/2 = 0.05` |
| row (3) | far terms `W^{C₄}W^kδ_Q`, `δ_Q = W^{-D+C_Q}(2+M_ee)`, `M_ee ≤ W^{C₀}` vs `N^{-D_t}` | `D ≥ D_t + C_Q + C₄ + k + C₀ + 2` (D after `C₀`) | free (D arbitrary) |
| row (4) | pinned route `(1+C)W^{Km}` on a slice, or `2W^{-D+C_n}` by `stQopNorm` (used above) | both `≤ W^{-D+C_Q}` | — |
| row (5) | `Σ_c‖κ'_c‖ ≤ (1+C(L^d)^m)Σ_b‖κ_b‖` (needs `c ≥ 0`: `e^{-cS/ℓ} ≤ 1`, `ℓ ≥ 1`), `L^d ≤ N`; `C_P = 11+(4k+4)max(0,1−τ')+2m+2` | `(1+C(L^d)^m)² ≤ N^{2m+2}` iff `N ≥ 1+C` | table D |
| boundary | `L^d ≤ W^K`, `log L ≤ W^ε`, `4 ≤ W^ε`, `dW^{τ'} ≤ W^ε`, `0 ≤ v ≤ w ≤ 1−g²/L²`, `W⁻¹ ≤ (1−w)/(1−v)` (endpoint implies all grid pairs), `κ' ≤ Im m` | per grid time, no `Prec` | instance below |

```
(abridged: selected lines, verbatim)
$ S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2194; python3 $S/tab2.py
A: s=C4+Cn, eps=eps0/(8s), W=N^c: log10 N* for 4<=W^eps; W^eps at N=1e6; log_N W^(2s*eps) (<=eps0/2)
 s=1  eps=0.01250 log10N*=   289.0 W^eps(N=1e6)=1.0292 log_N=0.00417
 s=6  eps=0.00208 log10N*=  1733.9 W^eps(N=1e6)=1.0048 log_N=0.00417
 s=40 eps=0.00031 log10N*= 11559.6 W^eps(N=1e6)=1.0007 log_N=0.00417
C: C=(1+40dm)6^(dm), Cn=C+2dm+Km (K=6), CQ=2Cn+2; log10 W0 of the growth C W^p<=exp(cW^eps/2)
 m=1 k=2 C=2.6136e+04 Cn=2.6148e+04 CQ=5.2298e+04 log10W0(eps=.9)=6.91 log10W0(eps=.5)=12.99
 m=2 k=3 C=1.1244e+07 Cn=1.1244e+07 CQ=2.2488e+07 log10W0(eps=.9)=10.02 log10W0(eps=.5)=18.57
 m=3 k=4 C=3.6380e+09 Cn=3.6380e+09 CQ=7.2761e+09 log10W0(eps=.9)=12.93 log10W0(eps=.5)=23.80
 m=5 k=6 C=2.8258e+14 Cn=2.8258e+14 CQ=5.6516e+14 log10W0(eps=.9)=18.54 log10W0(eps=.5)=33.89
D: C_P=11+(4k+4)max(0,1-tau')+2m+2 vs merged 11+(4k+4)max(0,1-tau'); needs N>=1+C
 m=1 tau'=.5: merged 17.0 new 21.0 log10(1+C)=4.42
 m=3 tau'=.5: merged 21.0 new 29.0 log10(1+C)=9.56
E: B_w/(r_{v,w}B_v)>=1, W=L=N^(1/6), g=1, d=3, pairs (v,w)=(0,.5),(.5,.9),(0,.99)
 N=1e1 L=W=1.47(<3): 1.19371 w>1-g2/L2 w>1-g2/L2
 N=1e3 L=W=3.16: 1.02974 1.23106 w>1-g2/L2
 N=1e6 L=W=10.00: 1.00100 1.00798 1.09880
F: W<=N^(1/d): W-part 0.00833 + log-part 0.02500 (ln N>=215) = 0.03333 <= eps0/2=0.05
```
Reading of A: with `ε = ε₀/(8(C₄+C_n))` the hypothesis `4 ≤ W^ε` fails at every `N ≤ 10⁶` (and `L<3` at `N ≤ 10²`); the targets are eventual in `N` at fixed `ε`, so the instance below takes `ε = 0.9`, not the tied `ε`.

### (ii) One concrete nondegenerate instance

`d=3, m=3 (k=4), σ` alternating, `g=Λg=1, E=0 (Im m = 1), κ'=1/2, K=6 (=1/𝔠), L=10¹³, W=10¹⁴, ε=0.9, τ'=0.5 (window), C₀=6, D=C_Q+C₀+k+3`, mollifier of `QopAlgebra_mollifier_props` (`C=3.6e9, c=1/2`), `v=s=0`, `w=t=0.99`, `M_ee` from `Γ=Λ=10`.
```
(abridged: the line `C=3.638048e+09 Cn=3.638048e+09 CQ=7.276097e+09 D=7.276097e+09` is omitted)
$ python3 $S/inst.py
OK   3<=d, m>=1, 3<=L, 1<W: d=3 m=3 k=4 L=1e13 W=1e14
OK   L^d <= W^K (K=1/c=6): log10 L^d=39 <= log10 W^K=84
OK   W >= N^c, c=1/6: log10 N=81.0, log10 N^c=13.50 <= 14
OK   0<eps<1, 4<=W^eps: log10 W^eps=12.60
OK   d W^tau' <= W^eps: log10 lhs=7.48
OK   log L <= W^eps: 29.9
OK   0<=s<=t<=1-g^2/L^2: s=0,t=0.99
OK   W^-1 <= (1-t)/(1-s): 1e-14 <= 0.01
OK   kappa' <= Im m(E=0): 0.5 <= 1.0
OK   r_{v,w} B_v <= B_w: ratio B_w/(r B_v)-1=9.900e-38
OK   (r B_v)^(2k) <= B_w^(2k): log10 B_w^2k=-336.0
OK   M_ee=G(G L)B^2k/eta <= W^C0: log10 M_ee=-335.4, log10 W^C0=84
OK   D>Cn+2 and D2=k+2>k+1: D=7.27610e+09
OK   delta_Q <= W^-(k+2): log_W delta_Q=-12.978
OK   EKFastDecay window nonvacuous at time v: W^eps*ell_v=3.981e+12 <= max l1 spread=1.500e+13
OK   (Vb) window ell_v W^tau' <= max Linf diam: 1.000e+07 <= 5.000e+12
OK   W >= W0 (growth C W^p <= exp(c W^eps/2)): p=3.6380e+09; margin at W=1e14: 8.780e+11; f(1e13)=1.640e+10; f(1e12)=-8.475e+10
OK   RangeCond tau'=1/2: N^(-1+tau') <= 1-t: log10 N^-1/2=-40.5 <= -2
OK   |E|<=2-kappa_E with kappa_E=1 (target 8): E=0
ALL OK
left=4.6051 right=4.6052 log((1-s)/(1-w))=4.6052 right<=left+Dl/(1-w)=4.6052 (Im m)^-1 log N=186.5
```
Sum-zero bookkeeping (T3, T5 stage 2), random complex `ϑ` with `Σ_{a:a₀=x}ϑ=1`, random kernels, `qqTensorN` computed from its definition, `k=2` (`d=3,L=3`) and `k=3` (`d=1,L=5`):
```
$ python3 $S/alg.py
d=3 L=3 k=2: |qq-QAQ*|=3.8e-13 sumzero_b=1.1e-12 sumzero_b'=1.8e-12 (A itself: 22.49) stage2 S sumzero=2.7e-11 pairform=126545.070 |k'-transport|=1.6e-13 |qv identity|=6.1e-10 rowsum 8186.94<=118244.70
d=1 L=5 k=3: |qq-QAQ*|=2.3e-13 sumzero_b=3.6e-13 sumzero_b'=2.9e-13 (A itself: 22.36) stage2 S sumzero=8.3e-12 pairform=65006.505 |k'-transport|=8.0e-14 |qv identity|=8.5e-11 rowsum 1695.49<=29520.55
```
External hypotheses: none new (EK-4 inputs `prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds` are merged theorems; `EKSumDecay2` is used through `ekSumDecay2_holds`).

### Verdicts
- T1 vocabulary: PASS (definitions as in the check file).
- T2 `martIncQN_ae_eq`: PASS. `QGridA_condExp_aTrueQN` needs only `|E n| < 2`, `gridTime(j+1) < 1` (`QGridA.lean:1906`); `YvecN = martIncN − ZvecN` is the definition (`StepDecompN.lean:192`); `STQop` is linear.
- T3a `qv_at_propagatorQ`: PASS (`Σ_b κ_b(𝒬A)_b = Σ_c κ'_c A_c`, then `qvPropagatedN` at `κ'`; no hypothesis on `ϑ` or `w`; `|qv identity|`, `|k'-transport|` above). T3b `qqTensorN_sumZero`: PASS (needs `Σ_{a:a₀=x}ϑ_t a = 1` only; above).
- T4 two-copy `lem_+Q`: PASS (derivation in the table; `C_Q = 2C_n+2`; (ii),(iii) with the same `ε`, (iii)'s `(2+M_ee)` factor is implied).
- T5 pair kernel: PASS. Shape: the hypotheses of `nqGood1_ugenPairN_le_of_bounds` with `hσ` replaced by `EKSumZero` of both fibres, plus `Real.log L ≤ W^ε`, `L^d ≤ W^K`; slice decay and block decay at one level `δ'`, `δ' ≤ W^{-D₂}`, `D₂ > k+1`; any `σ`.
- T6 (a),(b): PASS; `Φ` occurs only in the `GoodSetN` membership (D4 and Vb carry no `Φ`).
- T7 (a),(b): PASS (no new mathematics beyond T3a).
- T8 `yMomentsQUnifN`: **BLOCKED** as pinned. The check file's `T2194_yMomentsQUnifN` has `c : ℝ` with only `0 < C`; the bound `Σ_c‖κ'_c‖ ≤ (1+C(L^d)^m)Σ_b‖κ_b‖` uses `exp(−cS/ℓ) ≤ 1`, i.e. `0 ≤ c`. For `c < 0` clause 2 of `STMollifierProps` allows `‖ϑ‖` up to `C e^{|c|S/ℓ}` (and `sz.lam` is unconstrained in `Sizes`, `Defs/Sizes.lean:138-146`), so no polynomial `C_P` follows from the stated hypotheses; I did not decide falsity. Required: the dispatcher adds `0 ≤ c` (every consumer has `c = 1/2`) to the pin and its check-file text; with it T8 is PASS (`C_P` above).
- Overall: BLOCKED (T8 pin gap). Targets 1–7 are PASS. Size/split not estimated (stage-1a rule); the dispatcher decides it.
- Paper-delta candidates for the report (d): `T2194a`, `T2194b` as in the ticket; `T2194c` constants `C_n = C+2dm+Km` (3.6e9 at `m=3`), `C_Q = 2C_n+2`; `T2194d` `C_P` gains `2m+2` (needs `0 ≤ c`).

## (a′) Preflight corrections — Mon Oct  5 17:52:45 UTC 2026
- T8 (BLOCKED in 1a, pin gap): resolved by amend 1 (`0 ≤ c` in the pin and the check file). The 1a route then holds as written:
  `Σ_c‖κ'_c‖ ≤ (1 + C(L^d)^m) Σ_b‖κ_b‖` (`qProxy_sum_norm_wts_le`; uses `‖ϑ‖ ≤ C`, i.e. `c ≥ 0`), `(1 + C(L^d)^m)² ≤ N^{2m+2}` for `N ≥ 1 + C`,
  `C_P = 11 + (4(m+1)+4) max 0 (1−τ') + 2m + 2` (row (5)).  The pin has no `1 ≤ m`; the proof does not use it.
- Row T4 (iii): the decay clause `stQop_sub_fastDecay` is applied once, at `(C₀ + C_n + 1, ε, D − C_n)`, for (ii) and (iii) (1a: `D − C_Q + 1` for (iii)); (ii) is proved
  from the slice decay, not by the `b ↔ b'` swap of 1a.  (iii) holds without the factor `(2 + M_ee)` (1a: "true, not needed"); 6a uses `δ_Q = W^{-D+C_Q}`.
- Row (3): the only condition on `D` in Lean is `D > m + 2 + C_Q` (6a); `C₀` enters through `W₀` and `M_ee ≤ W^{C₀}`, `C₄` through the size of the bound only; the sum
  `D_t + C_Q + C₄ + k + C₀ + 2` of 1a is the consumer's budget, not a hypothesis.  1a's instance is numeric (`L = 10^13`); the Lean instances are listed in (b).

## (b) Script output — Mon Oct  5 17:52:45 UTC 2026

```
$ cd RBM3D-wt/T2194 && lake build RBM3D.Induction.QProxy        # Mon Oct  5 17:51:25 UTC 2026 .. 17:51:42 UTC 2026, exit 0
ℹ [3843/3843] Built RBM3D.Induction.QProxy (13s)
Build completed successfully (3843 jobs).
$ grep -E "QProxy.lean.*depends on axioms" build.log | sed 's/.*depends on axioms: //' | sort | uniq -c   # the 44 public declarations of the file
  44 [propext, Classical.choice, Quot.sound]
$ grep -cE "(warning|error).*QProxy.lean" build.log   # warnings or errors from QProxy.lean   -> 0
$ grep -cE "sorryAx|does not depend" build.log   -> 0
$ grep -nE "\bsorry\b|\badmit\b|^axiom|native_decide" RBM3D/Induction/QProxy.lean | wc -l   -> 0
$ wc -l RBM3D/Induction/QProxy.lean   -> 2261   (targets 1-8: lines 72-1486; instances 1488-2212; `#print axioms` 2218-2261)
$ for h in 12aa23a 72ce46c fec932a; do echo "$h $(date -u -r $(git log -1 --format=%ct $h))"; done   # the three commits on t/T2194 (base d783ee3)
12aa23a Mon Oct  5 17:36:06 UTC 2026
72ce46c Mon Oct  5 17:44:52 UTC 2026
fec932a Mon Oct  5 17:52:19 UTC 2026
```

Targets 4, 5, 6a, 6b (Lean shape fixed in 1b; extracted by `extract.py` from `RBM3D/Induction/QProxy.lean`, docstrings dropped, whitespace collapsed):
```
--- qqTensorBoundsN (1170 chars; file line 623)
theorem qqTensorBoundsN {d m : ℕ} (hd : 3 ≤ d) (Λg K C c : ℝ) (hΛ : 0 < Λg) (hK : 0 < K) (hC : 0 < C) (hc : 0 < c) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg) {W ε τ' C₀ D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε) (hLK : (L : ℝ) ^ d ≤ W ^ K) (hdW : (d :
  ℝ) * W ^ τ' ≤ W ^ ε) (hC₀ : 0 ≤ C₀) (hD : qProxyCn d m Λg K C c + 2 < D) (hW₀ : qProxyW0 d m Λg K C c C₀ ε D ≤ W) {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hϑ : STMollifierProps (d := d) g C c ϑ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (T : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ) {Mee : ℝ}
  (hMee : Mee ≤ W ^ C₀) (hT : ∀ b b', ‖T b b'‖ ≤ Mee) (hTfar : ∀ b b' : Fin (m + 1) → Zd d L, ellT L g t * W ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖T b b'‖ ≤ W ^ (-D)) : (∀ b b' : Fin (m + 1) → Zd d L, ‖qqTensorN ϑ t T b b'‖ ≤ W ^ (2 * qProxyCn d m Λg K C c * ε) * Mee + W ^ (-D + qProxyCQ d m
  Λg K C c)) ∧ (∀ b : Fin (m + 1) → Zd d L, EKFastDecay g t W ε (D - qProxyCQ d m Λg K C c) (fun b' => qqTensorN ϑ t T b b')) ∧ (∀ b' b : Fin (m + 1) → Zd d L, (∃ i j, W ^ ε * ellT L g t ≤ (zdistD d L (b i - b j) : ℝ)) → ‖qqTensorN ϑ t T b b'‖ ≤ W ^ (-D + qProxyCQ d m Λg K C c))
--- ugenPairQN_le_of_bounds (1274 chars; file line 919)
theorem ugenPairQN_le_of_bounds {d k : ℕ} (Λg κ' K : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg) (hκ' : 0 < κ') (hK : 0 < K) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg) {W ε D₂ : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε) (hlog : Real.log L ≤ W ^ ε) (hLK :
  (L : ℝ) ^ d ≤ W ^ K) (hD : (k : ℝ) + 1 < D₂) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2) (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) {M' δ' : ℝ} (hδ : 0 ≤ δ') (hδD : δ' ≤
  W ^ (-D₂)) (hT : ∀ b b', ‖T b b'‖ ≤ M') (hz1 : ∀ b' : Fin k → Zd d L, EKSumZero (fun b => T b b')) (hz2 : ∀ b : Fin k → Zd d L, EKSumZero (fun b' => T b b')) (hslice : ∀ b b' : Fin k → Zd d L, (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b' i - b' j) : ℝ)) → ‖T b b'‖ ≤ δ') (hblock : ∀ b b' : Fin k →
  Zd d L, (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (b i - b j) : ℝ)) → ‖T b b'‖ ≤ δ') (a : Fin k → Zd d L) : ‖UgenPairN d L g E σ s t T a‖ ≤ (W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ k) * ((W ^ (qProxy4C d k Λg κ' K * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^
  k) * M' + W ^ qProxy4C d k Λg κ' K * δ') + W ^ qProxy4C d k Λg κ' K * (W ^ k * δ')
--- qvFormQN_le_of_bounds (1990 chars; file line 1102)
theorem qvFormQN_le_of_bounds {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (Λg κ' K C c : ℝ) (hΛ : 0 < Λg) (hκ' : 0 < κ') (hK : 0 < K) (hC : 0 < C) (hc : 0 < c) (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' C₀ D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4
  ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hC₀ : 0 ≤ C₀) (hD : (m : ℝ) + 2 + qProxyCQ d m Λg K C c < D) (hW₀ : qProxyW0 d m Λg K
  C c C₀ ε D ≤ ((sz.W n : ℕ) : ℝ)) {ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - v)) {E : ℝ} (hE : |E| ≤ 2) (hκm
  : κ' ≤ (mE E).im) {σ : Fin (m + 1) → Bool} (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {Mee : ℝ} (hMee : Mee ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (hT : ∀ b b' : Fin (m + 1) → Zd d (sz.L n), ‖sz.STeeM n E v M σ b b'‖ ≤ Mee) (hTfar : ∀ b b' : Fin (m + 1) → Zd d (sz.L n), ellT (sz.L n)
  (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖sz.STeeM n E v M σ b b'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) (a : Fin (m + 1) → Zd d (sz.L n)) : qvFormQN sz n ϑ E v w σ M a ≤ (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 +
  |1 - w|)) ^ (m + 1)) * ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) * (((sz.W n : ℕ) : ℝ) ^ (2 * qProxyCn d m Λg K C c * ε) * Mee + ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m
  + 1) Λg κ' K * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1) Λg κ' K * (((sz.W n : ℕ) : ℝ) ^ (m + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c))
--- qvFormQN_le_of_goodSetN (1880 chars; file line 1167)
theorem qvFormQN_le_of_goodSetN {d m : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (Λg κ' K C c : ℝ) (hΛ : 0 < Λg) (hκ' : 0 < κ') (hK : 0 < K) (hC : 0 < C) (hc : 0 < c) (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' C₀ D : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε :
  4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hLK : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hC₀ : 0 ≤ C₀) (hD : (m : ℝ) + 2 + qProxyCQ d m Λg K C c < D) (hW₀ : qProxyW0 d m Λg
  K C c C₀ ε D ≤ ((sz.W n : ℕ) : ℝ)) {ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ) {u w : ℝ} (hu0 : 0 ≤ u) (huw : u ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - u)) {E : ℝ} (hE : |E| ≤ 2)
  (hκm : κ' ≤ (mE E).im) {σ : Fin (m + 1) → Bool} {Γ Λ Φ : ℝ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D) (hMee : Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1)) / etaT E u) ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (a : Fin (m + 1) → Zd d (sz.L
  n)) : qvFormQN sz n ϑ E u w σ M a ≤ (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) * ((((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1) Λg κ' K * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (m + 1)) * (((sz.W n :
  ℕ) : ℝ) ^ (2 * qProxyCn d m Λg K C c * ε) * (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * (m + 1)) / etaT E u)) + ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1) Λg κ' K * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c)) + ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m +
  1) Λg κ' K * (((sz.W n : ℕ) : ℝ) ^ (m + 1) * ((sz.W n : ℕ) : ℝ) ^ (-D + qProxyCQ d m Λg K C c))
```

Pinned targets 1, 2, 3a, 3b, 7a, 7b, 8 against the check file (`docs/tickets/checks/T2194-check.lean`, §2-§3):
```
$ python3 cmp.py    # §2 definition block of the check file vs QProxy.lean:74-104
lines check: 31  lines file: 31
IDENTICAL (modulo the keyword `noncomputable`)
$ lake env lean chk.lean   # check file + `import RBM3D.Induction.QProxy` + before `end RBM.Ind.T2194Check`:
    example : @RBM.Ind.qqTensorN = @qqTensorN := rfl   (same for qvFormQN, zVecQN, yVecQN)
    example : T2194_martIncQN_ae_eq := @RBM.Ind.martIncQN_ae_eq   (same for qv_at_propagatorQ, qqTensorN_sumZero,
              azumaSubGQ_ugenN, azumaSubGQ_gridExitN, yMomentsQUnifN)
  exit 0, error lines: 0
```

Preflight (iii), by script over the target statements (`chk3.py`):
```
statements scanned (10): qqTensorBoundsN, ugenPairQN_le_of_bounds, qvFormQN_le_of_bounds, qvFormQN_le_of_goodSetN, azumaSubGQ_ugenN, azumaSubGQ_gridExitN, yMomentsQUnifN, martIncQN_ae_eq, qv_at_propagatorQ, qqTensorN_sumZero
forbidden tokens STXiLK STXiLKM STsupXiLK STNQConcl goodExitTauN STXiL Prec Ξ ≺ : occurrences 0 0 0 0 0 0 0 0 0
6b: Φ occurs 2 x in the statement (binder + GoodSetN term of hM), in the conclusion 0 x, elsewhere 0 x
6b: `^ 2` occurrences, preceding token: ['n', 'ℝ)', 'n', 'n', 'n', 'n'] ; `^ 2` of a level (Γ Λ Φ Mee B η): 0
7a, 7b, 8: Γ/Λ/Φ among the binders: []
```

Compiled nonempty instances (all in the module build above; `QProxyInst`, file:line):
```
 1506 martIncQN_ae_eq_instance: sz0, QGridACheck data (E0,s0,t0,K0), n=0, j=0, sigma4 (alternating, 4 indices), moll; no open hypothesis
 1518 qv_at_propagatorQ_instance: sz0, n=0, E=1/2, u=1/3, w=1/2, non-scalar Hermitian M = X_(0,0,true), sigma4, moll; none open
 1551 qqTensorN_sumZero_instance: L=5, m=1, QopAlgebra_mollifier (clause 1 of _props), delta tensor; Adelta_ne, Adelta_not_sumZero (A itself is not sum-zero)
 1562 azumaSubGQ_ugenN_instance: sz0, E=1/2, s=0, v=1/32, K=4 (Δ=1/128), tau≡K, G0={0}, Gj={Hermitian}, Q = exact form at M=0; none open
 1582 azumaSubGQ_gridExitN_instance: G_j = GoodSetN(u_j) (measurableGoodSetN), any Γ Λ Φ τ' D'; hQ kept as hypothesis (S3-15/S3-18, as the merged azumaSubGN_goodExit_instance)
 1597 azumaSubGQ_gridExitN_instance_zero: G_j = {0} (measurable), Q = exact form at M=0: hQ discharged
 1641 yMomentsQUnifN_instance_pos: sz0, m=3, E=1/2, κ=1, τ'=1/2, s=0, t=1/32, K=4, ϑ_n = QopAlgebra_mollifier, n from the filter, P > 0 (private qProxy_yMomentsQPos)
 1658 yMomentsQUnifN_instance: the public statement at the same data (0 ≤ P)
 1823 ugenPairQN_le_of_bounds_instance: d=3,k=2,L=5,g=1/2,W=25,ε=1/2,D2=4,s=1/2<t=9/10,E=0,sigma=(+,-), T=w⊗w (sum-zero, T≠0), M'=1, δ'=0; window attained (spread 6 ≥ 5)
 2109 qvFormQN_le_of_goodSetN_instance: sz0, n with W_n ≥ qProxyW0 (exists_nat_ge), d=3,m=3,Λg=1,κ'=1/2,K=2,ε=1/5,τ'=1/10,C0=4,D=C_Q+6,E=0,u=0,w=1/2, M=0 ∈ GoodSetN(4,100,1); L∞ window attained
 2130 qvFormQN_le_of_bounds_instance: same data; hT, hTfar are clauses (D4), (Vb) of 0 ∈ GoodSetN; all hypotheses discharged
 2156 qqTensorBoundsN_instance: same sz0, n, t=0 (ℓ_0=1), delta tensor ≠ 0 (M_ee=1); ℓ¹ window attained; all hypotheses discharged
```
Time windows are not collapsed (`[0,1/2]` in item 6, `[1/2,9/10]` in item 5, `Δ = 1/128` in items 5, 6); index sets are `Fin 2` / `Fin 4` tuples over `Z_L^3`.  The delta tensor and `w ⊗ w` carry no
far mass, so the decay hypotheses on `T` hold with `δ' = 0`; the windows are attained inside the torus (`window_l1`, `window_linf`, `window_five`, conjuncts of the instance statements).

Registry pre-check and name clash:
```
$ cat assert.lean   # import RBM3D / import RBM3D.Induction.QProxy / #assert_rbm_axioms
$ lake env lean assert.lean   # run after the final build (Mon Oct  5 17:51:53 UTC 2026), exit 0;   diff against the same run without the new import (assert0.out):
1c1
< axiom audit: 5651 theorems, 2031 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 5684 theorems, 2044 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  (premise/registry lines identical: `premises found by scanning: 109 (borrowed 1, owed 85, structural 23)`; no `Test/Axioms.lean` edit)
$ python3 clash.py <main worktree> <branch worktree>   # last name component of every new public name vs every declaration in RBM3D/
RBM3D: 44 new public names, declaration-name collisions with existing RBM3D declarations: 0 []
RBM3D-wt/T2194: 44 new public names, declaration-name collisions with existing RBM3D declarations: 0 []
$ grep -rnw --include=*.lean yMomentsQUnifN RBM3D | grep -v QProxy.lean    # the ticket's one hit (comment)
RBM3D/Induction/AzumaProxyN2.lean:1001:row: the consumer is RBM2D `Induction/AltProxyQ.lean` (`yMomentsQUnifN`), where
$ git diff --stat main...t/T2194 | tail -2
 RBM3D/Induction/QProxy.lean | 2261 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2261 insertions(+)
```

Ports (RBM2D `Induction/AltProxyQ.lean` at `c9a24cf`, read-only; `git -C ../RBM2D --no-optional-locks log -1 --format=%h` = 9e0f275):
```
AltProxyQ:93,98,107,112 -> qqTensorN, qvFormQN, zVecQN, yVecQN | :122-213 -> qProxy_Qop_*, qProxy_wts, qProxy_sum_Qop, qProxy_sum_qq | :227 -> martIncQN_ae_eq
:258,281 -> qProxy_qv_aux, qv_at_propagatorQ | :303 -> qqTensorN_sumZero | :852 -> qProxy_qvFormQN_eq_re | :882,933 -> qvFormQN_le_of_bounds, _of_goodSetN (re-derived on EK-4)
:972 -> azumaSubGQ_ugenN | :1053,1093,1137,1272 -> qProxy_sum_norm_wts_le, qProxy_stronglyMeasurable_yVecQN, qProxy_yMomentsQPos, yMomentsQUnifN
not ported: :1027 azumaSubGQ_goodExit (replaced by azumaSubGQ_gridExitN); :336-:384 (|ϑ| ≤ 1, slot bounds); :386-:482 (distances, cross case); :517-:780 (core, QQTensorBoundsN, qqTensorBoundsN: re-derived block-wise)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/AltProxyQ.lean
 RBM2D/Induction/AltProxyQ.lean | 530 +++++------------------------------------
 1 file changed, 64 insertions(+), 466 deletions(-)
(HEAD differs from c9a24cf by the RBM2D clean-up commits bcc2c11, 99d6fe0; the ports were read at c9a24cf via `git show c9a24cf:RBM2D/Induction/AltProxyQ.lean`; no RBM1D file used.)
```

Narrative (stage 1b):
- One new file `RBM3D/Induction/QProxy.lean` on `t/T2194` (base `d783ee3`, HEAD `fec932a`), 2261 lines; targets 1-8 end at line 1486 (the 2000-line stop rule of amend 1 applies before targets 7-8: not triggered). `Test/Axioms.lean` untouched.
  Imports: `QGridA`, `QopNorm`, `AzumaProxyN2`, `NQGood2`, `Evolution/SumDecayZero` (not T2186's files). No pinned signature changed; no new `Prop` definition (one theorem `qqTensorBoundsN` for target 4).
- Constants `qProxyCn` (of `stQopNorm_holds`), `qProxyCQ = 2 qProxyCn + 2`, `qProxy4C` (of `ekSumDecay2_holds`), `qProxyW0` (of `stQop_sub_fastDecay` at `(C₀ + C_n + 1, ε, D − C_n)`, `max 2`) are
  `Classical.choose` extractions as `nqGood1C`; the proofs use only their private specs (`qProxyCn_spec`, `qProxy4C_spec`, `qProxyW0_spec`). No external input: EK-4 is `ekSumDecay2_holds` with `prop5Decay_holds`,
  `prop5Short_holds`, `prop6Diff1_holds … (1/2)`.
- Target 4: inner copy slice by slice: `c' ↦ conj T_{c,c'}` is `EKFastDecay` from (Vb) (`qProxy_spread_diam`, `d W^{τ'} ≤ W^ε`), so `stQopNorm_holds` bounds `𝒬 S_c`; a spread `c` makes the whole slice `≤ W^{-D}`;
  the outer copy is `EKFastDecay` at `D − C_n − 1` (`2 ≤ W`), so (i) is two uses of `(normQA)`; (ii), (iii) use `stQop_sub_fastDecay` (`W ≥ qProxyW0`, `‖F‖ ≤ W^{C₀+C_n+1}`). No concatenated window.
- Target 5: `qProxy_hker` is `hker_of_case1N` with `ekSumDecay2_holds` (`EKSumZero`, `log L ≤ W^ε`, `L^d ≤ W^K`, factor `r^k`); stage 1 on the `b'`-block with `σ̄ = !σ`; stage 2 on `b ↦ (𝒰_σ̄ T_{b,·})(a)`, sum-zero
  because the `b`-fibre sum commutes with `𝒰_σ̄`, far level `W^kδ'` by `norm_UN_apply_le` and `(1−s)/(1−t) ≤ W`; no hypothesis on `σ`.
- Target 6: `qvFormQN = Re 𝒰_σ⊗𝒰_σ̄ ((𝒬⊗𝒬̄)(𝓔⊗𝓔))` (`qProxy_qvFormQN_eq_re`, private copies of `nqGood1_{SB_conj,Theta_star,conj_uKer,mSigma_not}`), `Re ≤ ‖·‖`, then targets 3b, 4, 5 with `δ' = W^{-D+C_Q}`, `D₂ = D − C_Q`;
  6b takes (D4), (Vb) from `GoodSetN`; `Φ` is not used.  Target 7: `azumaSubGN` at the weights `κ'` (`qProxy_sum_Qop`) and `qv_at_propagatorQ`; 7b adds `gridExitTauN_measurableSet`, `mem_of_lt_gridExitTauN`.
  Target 8: `qProxy_sum_norm_wts_le` and the merged `AzumaProxyN_YfieldsW`; the body is the private `qProxy_yMomentsQPos` (`P > 0`).
- Differences from the ticket text: `δ_Q = W^{-D+C_Q}` and (iii) without the factor `(2 + M_ee)`; explicit hypotheses `hW₀ : qProxyW0 … ≤ W`, `hC₀ : 0 ≤ C₀`, `M_ee ≤ W^{C₀}` in 4-6. In the instances of 4, 6a, 6b the `n` with `W_n ≥ qProxyW0`
  comes from `exists_nat_ge` (the theorem's own hypothesis; no numerical value of `W₀` is computed).

## (c) Verified Mathlib names
- All 130 names used in the code of `QProxy.lean` that come from Mathlib (qualified `Real./Finset./Fin./Nat./ZMod./Complex./Matrix./Set./Classical.` names and the unqualified lemmas below) elaborate under `#check @name`
  (`names_check.lean`, `lake env lean`, exit 0, 0 error lines):
```
Classical.choose Classical.choose_spec Complex.conj_conj Complex.conj_ofReal Complex.norm_real Complex.re Complex.re_le_norm Fin.addCases Fin.append Fin.append_left Fin.append_right Fin.castAdd Fin.cons Fin.cons_self_tail Fin.ext Fin.forall_fin_two Fin.isValue Fin.natAdd Fin.sum_univ_three Fin.tail
Finset.card_bij' Finset.card_univ Finset.le_sup Finset.mem_filter Finset.mem_univ Finset.mul_sum Finset.prod_congr Finset.sum_add_distrib Finset.sum_comm Finset.sum_congr Finset.sum_const Finset.sum_eq_zero Finset.sum_filter Finset.sum_ite_eq' Finset.sum_le_sum Finset.sum_mul Finset.sum_nonneg
Finset.sum_sub_distrib Finset.sup_const Finset.sup_eq_bot_iff Finset.sup_le Finset.univ Finset.univ_nonempty Matrix.cons_val Matrix.cons_val_one Matrix.cons_val_zero Matrix.map_apply Matrix.map_mul Matrix.mul_apply Matrix.one_apply Matrix.smul_apply Matrix.sub_apply Nat.cast_le Nat.cast_nonneg
Nat.cast_pos Nat.cast_zero Nat.le_mul_of_pos_left Nat.mod_eq_of_lt Nat.mul_le_mul_left Nat.mul_pos Nat.pos_of_ne_zero Nat.pow_le_pow_left Pi.zero_apply Real.exp Real.exp_le_one_iff Real.le_coe_toNNReal Real.le_sqrt' Real.log Real.log_le_sub_one_of_pos Real.log_mul Real.log_two_lt_d9 Real.logb
Real.logb_le_iff_le_rpow Real.mul_self_sqrt Real.one_le_rpow Real.rpow_add Real.rpow_add_one Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_logb Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_nonneg Real.rpow_one
Real.rpow_pos_of_pos Real.rpow_two Real.sqrt Real.sqrt_eq_rpow Real.sqrt_nonneg Real.sqrt_one Real.sqrt_pos Real.sqrt_sq Real.toNNReal Set.indicator_of_mem Set.indicator_of_notMem Set.mem_singleton_iff ZMod.val_natCast ZMod.val_zero abs_of_pos abs_one continuous_finsetSum continuous_pi
dite_eq_left_of_eq_true div_le_iff₀ div_le_one eq_true exists_nat_ge inv_anti₀ inv_le_of_inv_le₀ inv_le_one_of_one_le₀ le_of_forall_pos_le_add le_self_pow₀ le_sub_comm map_mul map_sum measurableSet_singleton mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right norm_le_pi_norm norm_mul
norm_sub_le norm_sum_le not_or one_le_pow₀ pi_norm_le_iff_of_nonneg pow_le_one₀ pow_le_pow_left₀
```
- Deprecated at this Mathlib (warnings seen in the tool log; replaced by `simp only [...]`, `dite_eq_left_of_eq_true`, `rw [not_or]`, explicit `calc`): `if_pos`, `if_neg`, `dif_pos`, `push_neg`, `mul_le_one₀`.
  Signature note: `Finset.sup_eq_bot_iff` takes `(f) (S)` explicitly; no name was found absent.

## (d) Open issues and paper-delta candidates
Paper-delta candidates (proposed; the dispatcher assigns the numbers):
- `T2194a` (7b): the sub-Gaussian input of the `𝒬`-process is stated at the exit time `gridExitTauN … G` of ANY measurable family `G` (7a: any stopping family); RBM2D `azumaSubGQ_goodExit` hard-wires `goodExitTauN` at one level `Φ`
  of `GoodSetN`. No statement has a level of the current length (§62 (4)).
- `T2194b` (5): the variance proxy of the alternating martingale is two uses of `(sum_res_2)` (EK-4) on `(𝒬_v⊗𝒬̄_v)(𝓔⊗𝓔)`: block-wise sum-zero, block-wise `ℓ¹` decay, every `σ`; inherits `log L ≤ W^ε`, `L^d ≤ W^K` (T2016a, T2042a).
  RBM2D used Case 5 of the `d = 2` evolution kernel with the concatenated window `3ρ`, alternating `σ` only.
- `T2194c` (4, 6): two-copy `lem_+Q` at `d ≥ 3` with additive term `W^{-D+C_Q}`, `C_Q = 2C_n + 2`; `C_n` is the `stQopNorm_holds` constant (formally a function of `(d, m, Λ_g, K, C, c)`: the pin quantifies `Λ, c`
  before `∃ C_n`; the proof gives `C + 2dm + Km`); the threshold `W₀` of `stQop_sub_fastDecay` is an explicit hypothesis (T2059a); (iii) and `δ_Q` need no factor `(2 + M_ee)`.
- `T2194d` (8): `C_P` gains `2m + 2` from the row sum `1 + C(L^d)^m ≤ N^{m+1}` of `𝒬_u` (`‖ϑ‖ ≤ C`, not `≤ 1`); the proof needs `c ≥ 0` (amend 1); for `c < 0` not decided.
Open issues:
1. 6b has `M_ee ≤ W^{C₀}` as a hypothesis: a consumer chooses `C₀`, then `D > m + 2 + C_Q`, then `W ≥ qProxyW0`.
2. The shift `u_j → u_{j+1}` is not in this ticket: 6a is at one time `v` (that of `ϑ_v` and of `𝓔⊗𝓔`); S3-18a combines it with `norm_STeeM_shiftN_le` through `M_ee` and `δ = W^{-D''}`.
3. `azumaSubGQ_gridExitN_instance` keeps `hQ` as a hypothesis (the S3-15/S3-18 majorant); `azumaSubGQ_gridExitN_instance_zero` discharges it at `G = {0}`.
4. The file has 2261 lines against the ticket's estimate 1350 / 1600 / 1900; all eight targets are in this one file, so no split is proposed.
