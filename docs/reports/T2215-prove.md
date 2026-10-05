Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 21:23:31 UTC 2026
Notation (ticket, `Defs/Tail.lean:173`): `α_u=((W^d|1-u|)^{-1})²`, `T_{u,D}(r)=α_u e^{-√r}+W^{-D}`, `ρ=(1-v)/(1-w)`, `ℓ*=(log W)^{3/2}`, `K^σ_i=uKer(cycProd(mSigma E ∘ σ) i; v,w)`, `K^σ̄_i` the same with `!σ`.
Target 7g (any tensor `X`) and target 7 (`X=STeeM`, same data at `L_n, lam_n, W_n`) have the same mathematics; 7 = 7g by `rfl` (`STeeUM` `Step2Defs.lean:797-802`, `STtailTD` `Step5Pins.lean:151`).

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | weight `c` | `1/(4d+1)` (`1/13` at d=3) | `d(e^c-1) ≤ 1/4` (merged `tailtoTail_hec`, `TailtoTail.lean:346`) | `0.2399 ≤ 0.25` at d=3; `sup_{d≤10^5} = 0.2499997 <1/4` |
| 2 | squared tail weight | `e^{2√r} ≤ e^{4d+1} e^{c r}` | `c r+1/c-2√r=(c√r-1)²/c ≥ 0` | equality at `√r=1/c=13` |
| 3 | `Σ_b‖K(a,b)‖e^{2√|a-b|}` | `≤ 3e^{4d+1}ρ` | row 1, 2 and `Σ_b‖K‖e^{c|a-b|} ≤ 3ρ` (`ker_wt`, needs `g²≤1-w`, `0≤v≤w<1`) | none needed |
| 4 | `C₇` | `2·(3e^{4d+1})² = 18e^{8d+2}` (`3.5231e12` at d=3) | `2` (from `T_v² ≤ 2α_v²e^{-2√r}+2(W^{-D})²`) `×9e^{8d+2}` (two weighted rows) `×ρ²` (b′ row) | the `W^{-2D}` term needs only `2 ≤ C₇`: slack factor `~10^{12}` |
| 5 | amplitude | `ρ⁴α_v² = α_w²` | exact (`ρ²α_v=W^{-2d}(1-w)^{-2}`); script: ratio `1.0000000000000004` at instance | exact |
| 6 | `ℓ*` | `≥ 8` from `log W ≥ 4` (`4^{3/2}=8`) | far range `ℓ*/2-1 ≥ ℓ*/8` iff `ℓ* ≥ 8/3` | `3` vs `1` at `ℓ*=8` |
| 7 | `ℓ_w` | `ellT L g w = 1` | `g² ≤ 1-w`, `1 ≤ L` (`st5_ellT_one`, `Step5Cases.lean:84`) | exact; so `(1/8)(ℓ*·ℓ_w)=ℓ*/8` |
| 8 | far entry | `‖K(a,b)‖ ≤ (w-v)Σ_y S(a-y)Θ_w(y,b).re ≤ W^{-D₂}` if `|a-b|>ℓ*/2` | `S(a-y)≠0 ⇒ |a-y|_∞ ≤ 1` (`Block.lean:74-76`, `zdistInf_le_zdistD`); `|y-b| ≥ ℓ*/2-1 ≥ ℓ*/8` (row 6, 7); `a=b` excluded since `ℓ*/2 ≥ 4>0`; `w-v ≤ 1`; `Σ_y S=1` (`sum_sbKernelR`) | `w-v=1/32` at instance |
| 9 | far multiplicity | `4` events (`i∈{0,1}` × kernel on `b` or on `b′`) × `L^d` far points × `ρ` (other `b` row) × `ρ²` (`b′` rows) | a far pair has some `|b_i-b′_i|>ℓ*`, so `|a_i-b_i|>ℓ*/2` or `|a_i-b′_i|>ℓ*/2` (`zdistInf` triangle + `neg`) | far term `4YL^dρ³W^{-D₂}` as pinned |
| 10 | `D, D₂, p, Y, E, L` | free reals / `L≥3` / `|E|≤2` | `D₂` only enters through (H3); no `L`–`W` relation used; `g>0` not used | — |

Truth, near part (`‖X(b,b′)‖ ≤ p T_v(|b₀-b₁|)²` on near pairs; terms nonnegative so the sum extends to all pairs; `T_v²` does not depend on `b′`): `Σ_{b,b′}Π_i‖K^σ_i(a_i,b_i)‖Π_i‖K^σ̄_i(a_i,b′_i)‖ T_v² ≤ ρ²·Σ_b Π_i‖K^σ_i(a_i,b_i)‖(2α_v²e^{-2√|b₀-b₁|}+2(W^{-D})²)` (`b′` rows `≤ρ` each by `norm_uKer_le`, `sum_norm_row_le`). The `W^{-2D}` part gives `2pρ⁴(W^{-D})²`. For the other, `√|a₀-a₁| ≤ √|a₀-b₀|+√|b₀-b₁|+√|a₁-b₁|` (`zdistInf` triangle, `√(x+y) ≤ √x+√y`; the doubled `tailtoTail_exp_tri`, `TailtoTail.lean:425`) gives `e^{-2√|b₀-b₁|} ≤ e^{-2√|a₀-a₁|}e^{2√|a₀-b₀|}e^{2√|a₁-b₁|}`; the sum over `b` factorises over `i` (as `tailtoTail_main` `hsum2`, `:485`) into `(3e^{4d+1}ρ)²`; total `18e^{8d+2}pρ⁴α_v²e^{-2√|a₀-a₁|} = 18e^{8d+2}pα_w²e^{-2√|a₀-a₁|} ≤ 18e^{8d+2}p T_w(|a₀-a₁|)²` (row 5; `T_w ≥ α_we^{-√r} ≥ 0`). Near total `≤ 18e^{8d+2}p(T_w²+ρ⁴(W^{-D})²)`.
Truth, far part: pointwise `‖X‖ ≤ 1_near pT_v²+1_far Y`, so the far pairs contribute `Y·Σ_{far}ΠΠ ≤ Y·Σ_{4 events}` and each event is bounded by row 9 with the far entry of row 8 (`ker_entry`, `Theta_real_nonneg`, `norm_Theta_apply_le`, `re ≤ ‖·‖`). Sum of the two parts is the pinned right side. No `D₂`-versus-`D` coupling and no hypothesis beyond (H1)-(H3), `g² ≤ 1-w`, `4 ≤ log W`, `0 ≤ v ≤ w < 1`, `L ≥ 3`, `W>0`.

Scalar and constant script (`table.py` in `T2215/` of the scratchpad):
```
$ python3 table.py
row1 d(e^c-1) at d=3: 0.23987699828455988  <=1/4; max over d=1..10^5 of d(e^{1/(4d+1)}-1): 0.24999968750769908
row2 min over r of c*r+1/c-2*sqrt(r) (r=(1/c)^2=169): 0.0
row3 C7=18e^{8d+2} at d=3: 3523132969719.098  ; 2*(3e^{4d+1})^2 = 3523132969719.0977
row4 4^{3/2}= 8.0  ; ell*/2-1 at ell*=8: 3.0  >= ell*/8= 1.0  ; threshold ell*>=8/3= 2.6666666666666665
row5 rho^4 alpha_v^2 / alpha_w^2 at instance: 1.0000000000000004
row6 far term 4*L^d*rho^3*W^-D2 at L=20,D2=5: 3.288299949080857e-05  ; 4 events (i in {0,1}) x (b or b' kernel)
row7 w-v= 0.03125 <=1
```

### Consumer check (line (0)) and (P1)-(P3)
- (H1) = `lemDecCalEPrec_Bounds` conjunct 3 (`LemDecCalEPrec.lean:847-852`): same near condition `∀ i, zdistInf(a_i-a′_i) ≤ (log W)^{(3/2:ℝ)}`, same `STee = STeeM` argument order; its right side `N^τ((1-u)⁻¹·1_{|a₀-a₁|≤4ℓ*}·T² + J♯³(1-u)⁻¹(W^d|1-u|)^{-1/2}T²)` (`:829`, `:834`) is `≤ p T_v²` with `p = N^τ(1-u)⁻¹[1+J♯³(W^d(1-u))^{-1/2}] ≥ 0` (indicator `≤ 1`; (H1) is only for `≤ ℓ*` pairs, the weaker range is irrelevant). (H1) at `u=v`, `D` the level.
- (H2) = `difRep2_norm_STeeM_le_N` (`DifREP2.lean:1277`): `‖STeeM‖ ≤ Y := m N(16N)^{2m+2} ≥ 0` for every `b,b′`, Hermitian `H`, `|E|<2`, `v<1`, `η_v ≥ 1/(16N)`; `Y ≥ 0` is the pin's premise.
- (H3) = `hkell` of `lemDecCalEPrec_goodDet` (`:868-871`) = conclusion of `lemDecCalEPrec_kell` (`:979`) at `u=w`, `D=D₂`: `(1/8)(log W^{(3:ℝ)/2}·ellT L lam w) ≤ zdistInf(x-y) → ‖Theta d L lam (w:ℂ) x y‖ ≤ W^{-D₂}`; character-for-character the pin's (H3) (P2). Under `g²≤1-w` it is `|x-y| ≥ ℓ*/8` (row 7), exactly what row 8 consumes (`‖Θ‖`, then `re ≤ ‖·‖`; no conversion).
- Left side = summand of `STGridRepNAt` conjunct 4 (`Step2Defs.lean:839-851`): `STeeUM sz n (STflowE z n) (gridTime…j) (gridTime…k) (pathH…j ω) i.1 i.2`, i.e. `v=u_j`, `w=u_k`; `σ`-kernel on `b` (`mSigma E (σ i)`), `!σ`-kernel on `b′`; `STeeM` carries the same `v` as the `T_v` of (H1). No conjugation mismatch.
- Martingale line of the T2209 report (a) (3): `T_{w,D_j}²+ρ_j⁴(W^{-D_j})² ≤ 2T̂_w²` with `D_j=D_{u_j}`: `W^{-D_{u_j}}=(1-u_j)^{-2}W^{-D*}`, `ρ_j²W^{-D_{u_j}}=(1-u_k)^{-2}W^{-D*}=W^{-D_{u_k}} ≤ T̂_w`, and `(1-u_j)^{-2} ≤ (1-u_k)^{-2}` gives `T_{u_k,D_{u_j}} ≤ T_{u_k,D_{u_k}}`. The constants `C₇=18e^{8d+2}` (row 4) and `4YL^dρ³W^{-D₂}` (row 9) are what that line uses.
- (P1) 7g/7: same statement (`rfl`), no consumer loses a step (S5-11 applies 7 with `X=STeeM` at fine `H`). (P2) token-for-token (above). (P3) `0<g` dropped: not used in rows 1-9 (kernel rows, `Θ`, `sbKernelR_nonneg` need only `g²≤1-w`); `L≥3`, `W>0` come from `Sizes` in 7 (`three_le_L`, `W_pos`); `W^{-2D}` written `(W^{-D})²` (equal); `C₇` explicit. Each is the same truth; no consumer loses a step.

### (ii) One concrete nondegenerate instance (target 7g at instance (c); `inst_tailtoTailSq_c`)
Data: `d=3, L=20, W=64, g=1/64, E=0, v=1/32, w=1/16, D=8, D₂=5, p=Y=1`, `X(b,b′)=T_{v,D}(|b₀-b₁|)²` on near pairs, `1` on far pairs. `m^{(0)}=i`, so `μ=m(σ₀)m(σ₁)=∓1` (σ equal: `-1`; σ different: `+1`), and the `σ̄` kernel has `μ̄`. Kernels by FFT of the symbol `(1-vμŜ)/(1-wμŜ)`, `Ŝ=(1+2g²Σcosθ_i)/(1+2dg²)`; `X ≥ 0`, so `Σ‖K‖‖K′‖X` (computed) bounds the true `‖LHS‖` from above; the ratio is `(near+far)/RHS` of the pin.
`cd <scratchpad>/T2215 && python3 inst_c2.py | grep -Ev "\(-,|\(10, 10, 10\)" | cut -c1-230` (the full run also lists σ=(-,±) and `a₁=(10,10,10)`: all ratios below `5.7e-10`)
```
scalars: 3<=d,3<=L: True; 0<W; |E|<=2; 0<=v<=w<1: True; g^2=2.441e-04<=1-w=0.9375: True; log64=4.1589>=4: True; ellT=1.0
ell*=(log W)^1.5=8.4814; (1/8)(ell* ellT)=1.0602; far pairs exist (max zdist=10 > ell*): True; ell*/2-1=3.2407 >= ell*/8: True
H3 (hypothesis of the instance, numerically): max_{|x|_inf>=ell*/8} Theta_w = 2.817e-10 <= 64^-5 = 9.313e-10: True
H2 at Y=1: max_r T_{v,D}(r)^2 = 2.405e-22 <= 1: True
sigma=(+,+) mu=-1+0j a1-a0=(0, 0, 0) |a0-a1|=0: (near+far)/(RHS)=3.579e-10 near/RHSnear=2.210e-13 far/RHSfar=3.579e-10 rowsum|K|=0.970669<=rho=1.033333
sigma=(+,+) mu=-1+0j a1-a0=(10, 0, 0) |a0-a1|=10: (near+far)/(RHS)=3.545e-10 near/RHSnear=2.211e-13 far/RHSfar=3.545e-10 rowsum|K|=0.970669<=rho=1.033333
sigma=(+,-) mu=1-0j a1-a0=(0, 0, 0) |a0-a1|=0: (near+far)/(RHS)=5.672e-10 near/RHSnear=2.838e-13 far/RHSfar=5.672e-10 rowsum|K|=1.033333<=rho=1.033333
sigma=(+,-) mu=1-0j a1-a0=(10, 0, 0) |a0-a1|=10: (near+far)/(RHS)=5.605e-10 near/RHSnear=2.840e-13 far/RHSfar=5.605e-10 rowsum|K|=1.033333<=rho=1.033333
max ratio LHS-upper-bound/RHS over sigma, |a0-a1|: 5.671988366238014e-10  <=1: True
```
Hypotheses of 7g at once: `3≤3`, `3≤20`, `0<64`, `|0|≤2`, `0≤1/32≤1/16<1`, `(1/64)²≤15/16`, `4≤log 64=4.1589`, `p,Y≥0` (all scalar lines); (H1) with equality on near pairs (`‖(r:ℂ)‖=r`); (H2) `T²≤2.4e-22≤1` near, `1≤1` far; both near and far pairs occur (`max zdist 10 > ℓ*=8.48`, `ℓ*>8`). Row sums reach `ρ` (σ different: `1.033333=ρ`), so row 3's `ρ` is attained, not slack. The ratio is `≪1` because `X` is far from the extremal (a sign-structured `X` is not needed for truth, which is the proof above).
External hypothesis (H3) stays a hypothesis of the instance (another gate's pin, `lemDecCalEPrec_kell`); concrete check: true at the instance (line `H3`, slack factor `3.3`). Limit computation along `sz0` (`W=(2m)^5, L=4m, lam=(2m)^{-6}, d=3, w=1/16`): `S=a(I+g²A)`, `a≤1`, `A` the `2d`-regular adjacency, so `Θ_w(x) ≤ (1-w)⁻¹Σ_{j≥n}q^j ≤ q^n/((1-w)(1-q))`, `q=2dg²w/(1-w)`, `n=⌈ℓ*/8⌉ ≤ zdistInf(x) ≤ zdistD(x)` (walks of length `<zdistD(x)` miss `x`). Script `h3_analytic.py`, `-log_W(bound)` against `D₂=5`:
```
m=1: W=3.200e+01 ... n=1 q=9.77e-05  -log_W(bound)=2.65  >=5: False
m=2: W=1.024e+03 ... n=3 q=2.38e-08  -log_W(bound)=7.59  >=5: True
m=5: W=1.000e+05 ... n=5 q=4.00e-13  -log_W(bound)=12.39  >=5: True
m=100: W=3.200e+11 ... n=18 q=9.77e-29  -log_W(bound)=43.82  >=5: True
m=1000000: W=3.200e+31 ... n=78 q=9.77e-77  -log_W(bound)=188.18  >=5: True
```
So (H3) at `D₂=5` holds from `m=2` on and the exponent tends to infinity (`n~(log W)^{3/2}/8`); the `m=1` failure is the small-`W` regime, not an obstruction (the instance is `W=64`, where the direct check above passes).

### Verdicts
- Target 7g `tailtoTailSq_kernelGen`: PASS (statement true; every exponent of the table closes; hypotheses simultaneously satisfiable at the instance).
- Target 7 `tailtoTailSq_kernel`: PASS (7g at `X=STeeM`; (H1)-(H3) match the merged suppliers token for token; no consumer step lost).
- Instance `inst_tailtoTailSq_c`: PASS (all scalar hypotheses and (H1), (H2) discharged by numbers; (H3) the only hypothesis, true at the data).
- Stop rule (file `> 1500` lines): not triggered by this preflight; the proof uses exactly the ticket's step list (copies, doubled `e^{2√}` weight, near, far, assembly), no step beyond it.

## (b) Script output (stage 1b; ticket role `prover-hard`, model claude-sonnet-5-5; written Mon Oct  5 21:42:32 UTC 2026)
Branch `t/T2215`, commit `407e366`, sole file `RBM3D/Induction/TailtoTailSq.lean` (imports `RBM3D.Induction.TailtoTail`, `RBM3D.Induction.Step5Cases` only).
```
$ lake build RBM3D.Induction.TailtoTailSq 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3778 jobs).
$ (date -u; lake build) > fullbuild.out   # whole library in the worktree, started Mon Oct  5 21:39:32 UTC 2026
non-vacuity certificates: 0 of 150 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4018 jobs).
$ lake env lean axioms.lean   # #print axioms of the 3 public declarations
'RBM.Gauss.Sizes.tailtoTailSq_kernelGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.tailtoTailSq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst_tailtoTailSq_c' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/TailtoTailSq.lean | wc -l
0
$ wc -l RBM3D/Induction/TailtoTailSq.lean
    1043 RBM3D/Induction/TailtoTailSq.lean
$ git diff --stat main...t/T2215
 RBM3D/Induction/TailtoTailSq.lean | 1043 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1043 insertions(+)
407e366 T2215: S5-10a Induction/TailtoTailSq (squared-profile TailtoTail, near/far kernel bound for STeeUM)
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Induction.TailtoTailSq; #assert_rbm_axioms
exit code: 0
axiom audit: 6395 theorems, 2217 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Registry (DECISIONS §16, §20): no `Prop` defined or assumed, `Test/Axioms.lean` untouched, pre-check above exit 0.
```
$ python3 stmtdiff.py   # theorem statement vs pin body in docs/tickets/checks/T2215-check.lean (binder line and name stripped)
== tailtoTailSq_kernelGen vs TailtoTailSq_kernelGen_pin: pin body 19 lines, theorem body 19 lines, diff lines: 0
== tailtoTailSq_kernel vs TailtoTailSq_kernel_pin: pin body 18 lines, theorem body 18 lines, diff lines: 0
== inst_tailtoTailSq_c vs TailtoTailSq_instC_pin: pin body 13 lines, theorem body 13 lines, diff lines: 0
$ awk (statement of each target, lines of RBM3D/Induction/TailtoTailSq.lean)
theorem tailtoTailSq_kernelGen (d : ℕ) :
  3 ≤ d → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₂ E v w p Y : ℝ), 0 < W → |E| ≤ 2 →
    0 ≤ v → v ≤ w → w < 1 → g ^ 2 ≤ 1 - w → 4 ≤ Real.log W → 0 ≤ p → 0 ≤ Y →
    ∀ (σ : Fin 2 → Bool) (X : (Fin 2 → Zd d L) → (Fin 2 → Zd d L) → ℂ),
      (∀ b b' : Fin 2 → Zd d L,
        (∀ i : Fin 2, ((zdistInf d L (b i - b' i) : ℕ) : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ)) →
        ‖X b b'‖ ≤ p * tailTD d W v D ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) ^ 2) →
      (∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤ Y) →
      (∀ x y : Zd d L,
        (1 / 8 : ℝ) * (Real.log W ^ ((3 : ℝ) / 2) * ellT L g w) ≤ (zdistInf d L (x - y) : ℝ) →
        ‖Theta d L g (w : ℂ) x y‖ ≤ W ^ (-D₂)) →
      ∀ a : Fin 2 → Zd d L,
        ‖∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L,
            (∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
              (∏ i, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
                X b b'‖ ≤
          18 * Real.exp (8 * (d : ℝ) + 2) * p *
              (tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
                ((1 - v) / (1 - w)) ^ 4 * (W ^ (-D)) ^ 2) +
            4 * Y * (L : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * W ^ (-D₂) := by

theorem tailtoTailSq_kernel {d : ℕ} (sz : Sizes d) :
  3 ≤ d → ∀ (n : ℕ) (E v w D D₂ p Y : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool),
    |E| ≤ 2 → 0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w →
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
    (∀ b b' : Fin 2 → Zd d (sz.L n),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E v H σ b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
    (∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeM sz n E v H σ b b'‖ ≤ Y) →
    (∀ x y : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) w) ≤
        (zdistInf d (sz.L n) (x - y) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
    ∀ a : Fin 2 → Zd d (sz.L n),
      ‖STeeUM sz n E v w H σ a‖ ≤
        18 * Real.exp (8 * (d : ℝ) + 2) * p *
            (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
          4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) := by

theorem inst_tailtoTailSq_c :
  (∀ x y : Zd 3 20,
      (1 / 8 : ℝ) * (Real.log 64 ^ ((3 : ℝ) / 2) * ellT 20 (1 / 64) (1 / 16)) ≤ (zdistInf 3 20 (x - y) : ℝ) →
      ‖Theta 3 20 (1 / 64) ((1 / 16 : ℝ) : ℂ) x y‖ ≤ (64 : ℝ) ^ (-(5 : ℝ))) →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 20),
      ‖∑ b : Fin 2 → Zd 3 20, ∑ b' : Fin 2 → Zd 3 20,
          (∏ i, uKer 3 20 (1 / 64) (cycProd (fun i => mSigma 0 (σ i)) i) (1 / 32) (1 / 16) (a i) (b i)) *
            (∏ i, uKer 3 20 (1 / 64) (cycProd (fun i => mSigma 0 (!σ i)) i) (1 / 32) (1 / 16) (a i) (b' i)) *
              (((if (∀ i : Fin 2, ((zdistInf 3 20 (b i - b' i) : ℕ) : ℝ) ≤ Real.log 64 ^ (3 / 2 : ℝ)) then
                  tailTD 3 64 (1 / 32) 8 ((zdistInf 3 20 (b 0 - b 1) : ℕ) : ℝ) ^ 2 else 1 : ℝ)) : ℂ)‖ ≤
        18 * Real.exp (8 * ((3 : ℕ) : ℝ) + 2) * 1 *
            (tailTD 3 64 (1 / 16) 8 ((zdistInf 3 20 (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
              ((1 - 1 / 32) / (1 - 1 / 16)) ^ 4 * ((64 : ℝ) ^ (-(8 : ℝ))) ^ 2) +
          4 * 1 * ((20 : ℕ) : ℝ) ^ 3 * ((1 - 1 / 32) / (1 - 1 / 16)) ^ 3 * (64 : ℝ) ^ (-(5 : ℝ)) := by
$ sed -n '958p;1018,1019p;1036,1041p' RBM3D/Induction/TailtoTailSq.lean   # the two instances of target 7 (hypotheses H1-H3 of the second are the suppliers' statements)
example := tailtoTailSq_kernel SizesInst.sz0
example (H : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1))
      (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ) (σ : Fin 2 → Bool)
        4 * 1 * ((SizesInst.sz0.L 1 : ℕ) : ℝ) ^ 3 * ((1 - 1 / 32) / (1 - 1 / 16)) ^ 3 *
          ((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ (-(5 : ℝ)) := by
  refine tailtoTailSq_kernel SizesInst.sz0 le_rfl 1 0 (1 / 32) (1 / 16) 8 5 1 1 H σ (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [SizesInst.sz0]) ?_ (by norm_num)
    (by norm_num) hH1 hH2 hH3 a
  exact tailtoTailSq_four_le_log64.trans (Real.log_le_log (by norm_num) (by norm_num [SizesInst.sz0]))
```
Name clash, copies:
```
$ grep -rnw tailtoTailSq_kernelGen / tailtoTailSq_kernel / inst_tailtoTailSq_c in RBM3D RBM3D.lean of the main worktree and all other worktrees except T2215
tailtoTailSq_kernelGen: 0 hits
tailtoTailSq_kernel: 0 hits
inst_tailtoTailSq_c: 0 hits
$ grep -rn "TailtoTailSq" RBM3D RBM3D.lean   # main worktree, any spelling
RBM3D/Induction/PfStep5Alg.lean:21:(`Induction/TailtoTailSq`).  Targets, with the pins of the check file
$ python3 copycheck.py   # citation and verbatim check of the copied private helpers
copied private declarations: 16
names match source declaration: 16 of 16
diff of copied sections 1-3 (Weight, Theta, Kernel) vs TailtoTail.lean:44-338, after prefix: 0 lines
```
No RBM1D/RBM2D file was read or ported for this ticket (ticket: "no RBM2D counterpart"); the copied helpers come from RBM3D's own `TailtoTail.lean` (cited per declaration in the file, `-- copy of TailtoTail.lean:N`), so there is no `git diff --stat` against a sister project.

Narrative.
- Preflight (a) read, not edited; I found no error in it, so no (a′). Ticket line estimate 850/1000/1250; actual 1043 lines, below the stop rule of 1500.
- Preflight line (0) (consumer check) is in (a) "Consumer check". The three statements in the file equal the check-file pins (script diff above: 0 lines each), so (H1)-(H3), `STeeUM` and `STtailTD` are as in that check.
- Structure of the file: section Weight/Theta/Kernel = verbatim copy of `TailtoTail.lean:44-338` (diff after the prefix: 0 lines) plus `hec`, `sqrt_add_le`, `ker_row`, `zdistInf_neg` (`:346`, `:368`, `:413`, `:419`); section Sqrt (new): `exp_sqrt_le` (`e^{2√r} ≤ e^{4d+1} e^{cr}`, `(√r-K)²/K ≥ 0`), `ker_exp` (`Σ_b|K|e^{2√|a-b|} ≤ 3e^{4d+1}ρ`), `exp_tri` (doubled), `sb_support`, `far_entry`, `far_split`, `card_Zd`; section Main: `sum_pair`, `sum_split`, `near_alg`, `final`, `ell_ge`, `main` (target 7g at a fixed `a`); then the two targets and the instances.
- Near part: `‖X‖ ≤ p T_v² + Y·(four far indicators)` pointwise; `Σ_b'` of the `σ̄` rows is `≤ ρ²` (`ker_row`); `T_v² ≤ 2α_v² e^{-2√r} + 2(W^{-D})²`; `ρ²α_v = α_w` (`hamp`); constant `2·(3e^{4d+1})² = 18e^{8d+2}` and `2 ≤ 18e^{8d+2}` for the `W^{-2D}` term, as in the ticket.
- Far part: far pair gives `|a_i-b_i| > ℓ*/2` or `|a_i-b'_i| > ℓ*/2` (`far_split`); entry bound `‖K(a,b)‖ ≤ (w-v)Σ_y S(a-y)Re Θ_w(y,b) ≤ W^{-D₂}` from (H3) at `|y-b| ≥ ℓ*/2-1 ≥ ℓ*/8` with `ℓ* ≥ 8` (`ell_ge`) and `ellT = 1` (`st5_ellT_one`); `Σ_x ≤ L^d W^{-D₂}`; four events give `4 Y L^d ρ³ W^{-D₂}`.
- Differences from the ticket's step list: none in the statement. The far entry uses `ker_entry` plus `Complex.re_le_norm` and (H3) directly (no `Theta_real_nonneg` needed); the real-number finish is split into the private lemmas `near_alg` and `final`. No hypothesis was added or weakened; `3 ≤ d` is used as `1 ≤ d`, `0 < g` is not used (P3), `L ≥ 3` and `0 < W` are hypotheses of 7g.
- Instance `inst_tailtoTailSq_c` (target 7g, `d=3, L=20, W=64, g=1/64, E=0, v=1/32, w=1/16, D=8, D₂=5, p=Y=1`): the tensor `X = T_v²` on near pairs, `1` on far pairs; every scalar premise, (H1) and (H2) are discharged in the proof (`4 ≤ log 64` from `log 2 > 0.6931471803`, `T_{1/32,8}(r)² ≤ 1` by `norm_num`); (H3) stays the hypothesis of the theorem (another gate's pin `lemDecCalEPrec_kell`; numerical check in (a)).
- Target 7: `example := tailtoTailSq_kernel SizesInst.sz0` as the ticket asks, and a second example at `sz0`, `n = 1` (`L = 8`, `W = 1024`, `lam = 1/4096`), `E = 0`, `v = 1/32`, `w = 1/16`, `D = 8`, `D₂ = 5`, `p = Y = 1`, any `H`, `σ`, `a`: the scalar premises (`lam² ≤ 15/16`, `4 ≤ log 1024`, ...) are discharged, (H1)-(H3) are hypotheses (statements of `lemDecCalEPrec_Bounds` conj. 3, `difRep2_norm_STeeM_le_N`, `lemDecCalEPrec_kell`: other gates).
- Special case / conditional adapter (CLAUDE.md §5.6): 7g and 7 are conditional on (H1)-(H3); they are not a statement of the paper (paper-delta candidates below).

## (c) Verified Mathlib names (`#check` in `names.lean`, tool log of this run; none checked absent)
```
Real.rpow_le_rpow : 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
Real.rpow_add : 0 < x → ∀ y z, x ^ (y + z) = x ^ y * x ^ z
Real.rpow_one : x ^ 1 = x
Real.sqrt_eq_rpow : √x = x ^ (1 / 2)
Real.sqrt_mul_self : 0 ≤ x → √(x * x) = x
Real.rpow_neg : 0 ≤ x → x ^ (-y) = (x ^ y)⁻¹
Real.rpow_ofNat : x ^ OfNat.ofNat n = x ^ OfNat.ofNat n (n.AtLeastTwo)
Real.exp_le_one_iff : Real.exp x ≤ 1 ↔ x ≤ 0
Real.one_le_exp : 0 ≤ x → 1 ≤ Real.exp x
Real.log_pow : Real.log (x ^ n) = ↑n * Real.log x
Real.log_two_gt_d9 : 0.6931471803 < Real.log 2
Real.log_le_log : 0 < x → x ≤ y → Real.log x ≤ Real.log y
Complex.re_le_norm : z.re ≤ ‖z‖
Complex.norm_real : ‖↑r‖ = ‖r‖
Fintype.sum_equiv : (e : ι ≃ κ) (f g) → (∀ x, f x = g (e x)) → ∑ x, f x = ∑ x, g x
Fintype.sum_prod_type' : ∑ x : α₁ × α₂, f x.1 x.2 = ∑ x, ∑ y, f x y
Finset.sum_mul_sum : (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j
Fin.forall_fin_two : (∀ i : Fin 2, p i) ↔ p 0 ∧ p 1
piFinTwoEquiv : ((i : Fin 2) → α i) ≃ α 0 × α 1
one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n        pow_le_one₀ : 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
ZMod.card : Fintype.card (ZMod n) = n
```
Deprecated in this Mathlib (warnings in the first compile of this run): `if_pos`, `if_neg` (suggested `ite_eq_left`, `ite_eq_right`), `push_neg` (suggested `push Not`); the file uses `simp only [eq_true h, ↓reduceIte]` and `push Not`.

## (d) Open issues and paper-delta candidates
- **T2215a** (= T2209c): the squared-profile `TailtoTail` for the quadratic variation with near/far split at `(log W)^{3/2}`, constant `18e^{8d+2}` (paper: BDG with `(res_deccalE_dif)`, `3_5:2364-2383`, no statement). **T2215b**: the far remainder is `4YL^dρ³W^{-D₂}` with a separate exponent `D₂` and the crude `Y` (paper: `W^{-D+C}` with one `D`). **T2215c**: none (no statement difference found beyond the ticket's (P1)-(P3)).
- For S5-11: premises to supply per grid index are `0 ≤ v ≤ w < 1`, `lam² ≤ 1 - w`, `4 ≤ log W`, `p, Y ≥ 0`, (H1)-(H3); the absorption of `4YL^dρ³W^{-D₂}` (choice of `D₂`, `L`-`W` relation) is S5-11's (ticket §29 (3)).
- From (a) (script `h3_analytic.py` of the preflight, not re-run here): (H3) at `D₂ = 5` along `sz0` fails at `m = 1` (`W = 32`) and holds from `m = 2`; relevant to S5-11's choice of `D₂`, not to this ticket.
- Observation: the full `lake build` in the worktree does not import the new module (the hub adds the root import at merge); the registry pre-check above is the check that covers it.
