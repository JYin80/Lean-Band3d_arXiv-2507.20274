Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 15:27:36 UTC 2026

Notation: `Q = M^{(σ₁σ₂)} = BAMss d L (BAMB d L g E m) σ₁ σ₂`, `Θ_t = BATheta ..`, `Ξ := BAuKer − 1 = (t−s) Q Θ_t` (`BAuKer_eq_one_add`, probe `t/T2378:RBM3D/Probe/T2378Pins.lean:253`), `k = d−2`, `A_t := (g²+|1−t|)⁻¹`. Paper: `A:100-103` (decomp, `Xi_infint`), `A:115-118` (`eq:decayXi`), `A:209` (`eq:samecolor`).

### (i) Exponent table

Pin text (probe 208-250) against `Evolution/Pins.lean:64-140`; one line per binder that differs:

| pin | difference to the band pin | reason |
|---|---|---|
| all five | `(d n)` -> `(d n Λ κ)` for `BAEKSumNdecay`; `Λ κ` already present in the other four; `m : ℂ, ‖m‖=1` -> `E : ℝ, m : ℂ, BAReal d L g κ E m`; `UN d L g (EKsgn m σ)` -> `BAUN d L g E m σ` | BA data `(g,E,m)`; `BAReal = BASelf ∧ κ ≤ Im m` (`MFixedPoint.lean:432`) |
| `Ndecay` | adds `g ≤ Λ` (band: none); no `0<Λ`, `0<κ`, no constant | `g ≤ Λ` and `κ` are unused by the proof (only `BAReal.1` enters `BATheta_resolvent`); kept for uniformity |
| `Decay1` | drops antecedent `Prop5Decay d Λ →` | merged `baProp5_holds` (`Prop6Path.lean:850`) |
| `NAL` | drops `Prop5Decay`, `Prop5Short`; `κ ≤ m.im` now inside `BAReal` | `baProp5_holds`, `baProp5s_holds` (`Prop5Short.lean:667`) |
| `Decay2` | drops `Prop5Decay`, `Prop5Short`, `Prop6Diff1 (1/2)`; `∀ K` and `log L ≤ W^ε`, `L^d ≤ W^K` unchanged | `baProp6_holds` at `c = 1/2` (`BAProp6` needs `0<c<1`) |
| `Nonzero` | drops `Prop5Short`, `Prop8ZeroMode`; `κ ≤ m.im` inside `BAReal` | `baProp5s_holds`, `baProp8_holds` |
| `Decay1/NAL/Decay2` | quantifier order identical: `(d n Λ κ[,K]) ∃C ∀ L g W ε D s t E m σ A`; `E m` placed after `s t` as the band's `m` | same position as band `m` |
| `EKFastDecay`, `EKSumZero`, `zeroModeSet` | unchanged (class R) | — |

Constants and thresholds (instance values from (ii); `d=3`, `k=1`):

| quantity | value / formula | constraint | slack |
|---|---|---|---|
| `Λ, κ` | `1, 1/2` | `g₀ ≤ Λ`, `κ ≤ Im m` | `g₀=0.013014`, `Im m = 0.9995` |
| per-factor bound (Ndecay) | `(1−s)/(1−t)` | `‖Ξ‖ ≤ (t−s)‖Θ‖ ≤ (t−s)/(1−t)`, `‖Q‖_{∞→∞} ≤ 1`, `‖Θ‖(1−t) ≤ 1` from `Θ = 1+tQΘ` | sharp: `σ=(+,−)`, `s=0,t=1/2` gives `‖Θ‖=2.0000=1/(1−t)`, `‖uKer‖=2.0000` |
| `t<1` | binding | `‖M^{(+,−)}‖_{∞→∞}=1` (`KBase.lean:322`) | none |
| convex weight | `1−s/t ≤ 1−s` (`t>0`) | `s ≥ 0, t ≤ 1` | `s(1−t)/t ≥ 0` (0 at `s=0`) |
| `t = 0` | forces `s=0`, `Ξ=0` by `BAuKer_eq_one_add` (convex form needs `t>0`) | separate case in `XiDecay` | — |
| `C_B` (zero mode) | `1+2(2(k+2))^k` (`zeroMode_le_of_ge_mul`, `Kernel/PropT.lean:89`, `m=k+2`, `n≤ mL` by `zdistD_le`) | `g²/L² ≤ 1−t` | at instance `1.06e-5 ≤ 0.5` |
| `XiDecay` const | `c=c₅`, `C_Ξ = C₅ C_B + Λ²+1` (no distance shift: Θ entry used directly) | `a≠b`: `C₅C_B`; `a=b`: `|Θ_aa−1| ≤ C₅C_B A_t + 1`, `1 ≤ (Λ²+1)A_t` as `g²+|1−t| ≤ Λ²+1` | `Λ²+1` |
| `XiBall` const | `4 C_Ξ ballC k` (shape of `ek_sum_ball_norm_XiKer_le`), `Λ'≥1, R≥1, R ≤ Λ'ℓ_s` | `(1−s)ℓ_s² ≤ g²+|1−s|` (`one_sub_mul_ellT_sq_le`, `Params.lean:80`) | instance: `Σ|Ξ_{0b}|=1.0000` vs `1.9997` |
| `SameRow` const | `1 + C₅(1+Λ² expC k c₅)` | `‖uKer^{σσ}‖ ≤ 1+(t−s)‖Q‖‖Θ‖`, `‖Θ‖ ≤ Σ_b|Θ(0,b)|` (translation), `BAProp5s`, `Σ e^{-c|b|} ≤ expC` | instance `‖uKer^{σσ}‖=0.6671` |
| `W, ε, D` | `16, 1/2, 2` | `1<W, 0<ε<1, 1<D, 4 ≤ W^ε` | `W^ε = 4` (slack 0) |
| `W⁻¹ ≤ (1−t)/(1−s)` | `1/16 ≤ 1/2` | pin range | `7/16` |
| `t ≤ 1−g²/L²` | `1/2 ≤ 1−1.06e-5` | pin range (implies `t<1` as `g>0`) | `≈ 0.5` |
| `log L ≤ W^ε`, `L^d ≤ W^K` | `1.386 ≤ 4`; `64 ≤ 16^2=256`, `K=2` | `Decay2`; min `K=3/2` | `2.6`; factor 4 |
| `EKFastDecay` window | `W^ε ℓ_s = 4 ≤` ℓ¹-diameter `6` | nonvacuous: `a=(0,(2,2,0))` has `|a₀−a₁|=4` | window not collapsed |
| `Nonzero` window | `s=1−g²/L²`, `t=1−g²/(2L²)` | `1−g²/L² ≤ s ≤ t < 1` | width `5.3e-6`; `‖uKer^{(+,−)}‖=2.0000=(1−s)/(1−t)` |

(iii) `BATheta_resolvent` (`BA/KBase.lean:330`) takes `hr : BAReal d L g κ E m`, `0 ≤ t`, `t < 1`, any `σ₁ σ₂`; it uses only `hr.1`. Pin ranges give `t ≥ s ≥ 0`, and `t<1` (`Ndecay`, `Nonzero` directly; `Decay1/NAL/Decay2` from `t ≤ 1−g²/L²`, `g>0`). `BAuKer_eq_one_add` needs `0 ≤ t`; `BAuKer_convex` needs `0<t`. Hypotheses match; no gap.

### (ii) Band proof, what reads `‖m‖=1`, `M = mI`, `S^{(B)}`, and the BA replacement

| target | band proof | steps reading `‖μ‖=1` / `S^{(B)}` | BA replacement (merged) |
|---|---|---|---|
| 3 `Ndecay` | `Kernel/Evolution.lean:98-115` (`norm_Xi_le`, `norm_uKer_le`), `:119-155` (`norm_UN_apply_le`, `norm_UN_le`) | `norm_cycProd` (`:137`), `‖(t−s)μ‖=t−s` (`:103`), `norm_Theta_le` (`Props4.lean:218`), `norm_SB` | `Q`: row sums `Σ_b|Q_ab| = Σ_b BAK_ab = 1` (`BAMss_norm_eq_BAK`, `KKernel.lean:102`; `BAK_row_sum`, `:124`) gives `‖Q‖ ≤ 1` (`Matrix.linfty_opNNNorm_def`, as private `BAKBase_norm_le`, `KBase.lean:151`); `‖Θ‖ ≤ 1/(1−t)` from `BATheta_resolvent`; `BAuKer_eq_one_add`; the tensor-row product step is generic (copy `:119-155`) |
| 4 `XiDecay` | `Evolution/XiPins.lean:36-174` (`ek_norm_XiKer_apply_le`), `:316-349` (`xp_exists_sqrt`, `ekXiDecay_holds`) | `norm_t_mul_lt_one` (`:54`), `Theta_apply_add_right_of_three_le` (`:69`), `sum_norm_SB_row`/`SB_apply_eq_zero_of_one_lt` (`:139,147`: hop to neighbours), `hcoef` (`:153`), `xp_exists_sqrt` (`:316`) | `BAuKer_convex` (probe 264): `Ξ_ab = ((t−s)/t)Θ_ab` for `a≠b`, no hop; translation: copy of private `KInduct_theta_shift` (`KInduct.lean:147`, via `BAMsigma_shift`, `KSolve.lean:558`); decay from `baProp5_holds`; zero mode by `zeroMode_le_of_ge_mul`; no `Mbound_AO`, no `μ = m²` |
| 4 `XiBall` | `XiPins.lean:176-270` (`ek_sum_ball_norm_XiKer_le`) | none: the proof reads only the pointwise bound on `‖Ξ_ab‖` | private twin of `:176-270` over an abstract entry function, with `sum_ball_min_pow_le`, `ballC`, `one_sub_mul_ellT_sq_le` |
| 4 `SameRow` | `XiPins.lean:355-424` (`ekSameRow_holds`) | `ek_norm_spin` (`:372`), `norm_t_mul_lt_one` (`:374`), `‖SB‖` (`:419`) | `baProp5s_holds` (bundled in `baProp5to8_holds`), `norm_le_sum_row_zero` (`Kernel/Evolution.lean:307`, public), `sum_radial_exp_decay_le`/`expC` (`Defs/RadialSum.lean:271-276`), `‖Q‖ ≤ 1`; `M^{(σσ)}` is the matrix `Q`, no `m²`, no `S` |

### (ii) One concrete nondegenerate instance (all hypotheses at once)

Data: `d=3`, `L=4`, flow datum `n=0` of `sz0` (`λ=1/64`, `w=6i/5`, `m_S`, `z_S=w−m_S`, `t₀=Im m_S/(Im m_S+Im z_S)`, `E=(t₀ Re z_S−(1−t₀)Re m_S)/√t₀`, `g₀=√t₀ λ`; defs `FlowPins.lean:406-412`, `MFixedPoint.lean:279-280, 865-868`), `Λ=1`, `κ=1/2`, `n=2`, `σ=(+,−)`, `s=0`, `t=1/2`, `W=16`, `ε=1/2`, `D=2`, `K=2`, `A=δ_0`. Script: numerics for `Ψ` = adjacency of `Z_4^3` (`Adj`: `zdistD=1`), solves `(self_m)` at `(g₀,E)`, builds `Q`, `Θ`, `uKer`. No external hypothesis occurs (`baProp5_holds` etc. are proved); the four open pins enter only as the hypothesis of the instance, checked here at the data.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2388/inst.py`
```
t0=0.693740 E=0.000e+00 g0=0.013014  m=0.000000+0.999493i  self-resid=1.11e-16  Im m=0.9995 (kappa=1/2)
g^2/L^2=1.059e-05 <= 1-t=0.50: True
sig=(1,0): max|rowsum|Q|-1|=1.8e-15  |Th|_inf=2.0000<=1/(1-t)=2.0  |uKer|_inf=2.0000<=(1-s)/(1-t)=2.0  convex-resid=0.0e+00
   max_ab |Xi_ab| / [(1-s)(g^2+|1-t|)^-1 (|a-b|+1)^-(d-2)] = 0.4992  (C,c with c->0 form)
sig=(1,1): max|rowsum|Q|-1|=1.3e-15  |Th|_inf=0.6671<=1/(1-t)=2.0  |uKer|_inf=0.6671<=(1-s)/(1-t)=2.0  convex-resid=0.0e+00
   max_ab |Xi_ab| / [(1-s)(g^2+|1-t|)^-1 (|a-b|+1)^-(d-2)] = 0.1666  (C,c with c->0 form)
   same-sign |uKer|_inf = 0.6671 (pin 'samecolor' C)
sig=(0,0): max|rowsum|Q|-1|=1.3e-15  |Th|_inf=0.6671<=1/(1-t)=2.0  |uKer|_inf=0.6671<=(1-s)/(1-t)=2.0  convex-resid=0.0e+00
   max_ab |Xi_ab| / [(1-s)(g^2+|1-t|)^-1 (|a-b|+1)^-(d-2)] = 0.1666  (C,c with c->0 form)
   same-sign |uKer|_inf = 0.6671 (pin 'samecolor' C)
ball |D|=7, sum|Xi_0b|=1.0000 vs ((g^2+|1-s|)/(g^2+|1-t|))=1.9997 (Lam'=1,R=1<=ell_s=1.000)
W^eps=4.000>=4: True; W^-1=0.0625 <= (1-t)/(1-s)=0.500; g0<=Lam=1: True; log L=1.386<=W^eps; L^d=64<=W^K=256
ell_s=1.000, window W^eps*ell_s=4.000, torus l1-diameter=6, exists a with a_i-a_j at dist>=window: True
|BAUN delta_0|_inf=3.9919 <= Ndecay bound ((1-s)/(1-t))^2*|A|=4.0
Decay1 RHS at C=1: 16.0571 (>= LHS: True)
Nonzero window: 1-g^2/L^2=0.999989414 <= s=0.999989414 <= t=0.999994707 < 1: True
  sig=(1,1) at window: |uKer|_inf=1.0000 (bound (1-s)/(1-t)=2.000)
  sig=(1,0) at window: |uKer|_inf=2.0000 (bound (1-s)/(1-t)=2.000)
```
Reading: `BAReal` holds (residual `1e-16`, `Im m = 0.9995 ≥ 1/2`); `t₀=0.69374 ∈ [17/25, 25/36]` (`Step1Fam.lean:748,753`). The Ward row sums of `|Q|` are 1 for all four charge pairs; the convex identity holds to `0.0`; `‖Θ‖`, `‖uKer‖` are `≤ 1/(1−t)`, `≤ (1−s)/(1−t)` (equality at `(+,−)`); `‖BAUN δ_0‖_∞ = 3.9919 ≤ 4`; `Decay1` RHS at `C=1` is `16.06` (the pin asserts some `C`, not this one). Ξ-decay ratio (exponential dropped) `≤ 0.5`; ball sum `1.0000 ≤ 1.9997`.

### Verdicts
- Target 1 (vocabulary, `BAuKer_eq_one_add`, `BAuKer_convex`): PASS (identities check numerically; proofs use `BATheta_resolvent` only).
- Target 2 (five pins): PASS (hypotheses satisfiable at the instance above; `Nonzero` at its own window).
- Target 3 (`baEKSumNdecay_holds`): PASS (sharp constant, no gap; `‖Θ‖ ≤ 1/(1−t)` and `‖Q‖ ≤ 1` are re-derived from merged names because the `BAKBase_*` lemmas are private).
- Target 4 (`Ξ` pins): PASS. Two points beyond the probe: the diagonal `a=b` needs `Θ_aa − 1` with `1 ≤ (Λ²+1)A_t` (constant depends on `Λ`; allowed, constants follow `(d,Λ,κ)`), and `t=0` is a separate trivial case.
- Target 5/6 (instances, registry): no mathematical obstruction. The pin shapes of `BAEKXiDecay`, `BAEKXiBall`, `BAEKSameRow` are not in the probe; the prover fixes them as the band forms (`XiPins.lean:281-357`) with `(d Λ κ)`, `BAReal`, `σ₁ σ₂` (`σ₁=σ₂` for `SameRow`), and `Ξ_ab := BAuKer − 1`.
- (iv) Not given here: the stage-1a rules exclude size estimates; the stop line (2,000 lines, split at 1,500 into E1a = targets 1-3, E1b = target 4) is the ticket's.

Overall verdict: PASS.

## (b) Script output and narrative — Sat Oct 10 15:49:16 UTC 2026

Commands run in the worktree /Users/junyin/Lean_proof/RBM3D-wt/T2388 (branch t/T2388); `extract.py` prints a declaration's statement from the file; `names.txt`, `top.txt`, `pre.lean`, `ax_all.out` are in the scratchpad T2388/.

### B.1 size against the stop line (script, Sat Oct 10 15:46:52 UTC 2026)
wc -l RBM3D/BA/EKPins.lean:      856 (stop line 2,000; split point 1,500); HEAD b9ac5cf; uncommitted files:        0
sorry/admit/native_decide/axiom words in the file: 0
### B.2 builds (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2388)
$ lake build RBM3D.BA.EKPins | tail -1
Build completed successfully (3756 jobs).
$ lake build | grep -E "axiom audit|Build completed|error"
info: RBM3D.lean:433:0: axiom audit: 11077 theorems, 3257 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4201 jobs).
$ lake env lean docs/tickets/checks/T2388-check.lean; echo exit $?
exit 0
$ lake env lean pre.lean  (import RBM3D; #assert_rbm_axioms)
axiom audit: 11077 theorems, 3257 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).|RBM.BA.BAEKSumDecay1: 1 [no certificate]|RBM.BA.BAEKSumDecayNAL: 1 [no certificate]|RBM.BA.BAEKSumDecay2: 1 [no certificate]|RBM.BA.BAEKSumDecayNonzero: 1 [no certificate]
### B.3 #print axioms (50 new public declarations printed by script; names in scratchpad names.txt)
'RBM.BA.BAuKer_eq_one_add' [propext, Classical.choice, Quot.sound]
'RBM.BA.BAuKer_convex' [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSumNdecay_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKXiDecay_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKXiBall_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSameRow_holds' [propext, Classical.choice, Quot.sound]
all 50 declarations: outside the standard three = []
### B.4 statements (extract.py)
$ five pins, BAuKer, BAUN, BAuKer_eq_one_add, BAuKer_convex: statement text in t/T2378:RBM3D/Probe/T2378Pins.lean vs EKPins.lean
diff: IDENTICAL (47 lines)
-- EKPins.lean:58
def BAXi (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (s t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((t : ℂ) - s) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂)
-- EKPins.lean:218
theorem baEKSumNdecay_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumNdecay d n Λ κ
-- EKPins.lean:240
def BAEKXiDecay (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
        ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
          ‖BAXi d L g E m s t σ₁ σ₂ a b‖
            ≤ C * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L (a - b) : ℝ) + 1) ^ (d - 2))⁻¹
              * Real.exp (-(c * (zdistD d L (a - b) : ℝ)) / ellT L g t)
-- EKPins.lean:250
def BAEKXiBall (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
        ∀ σ₁ σ₂ : Bool, ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
          ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
            ∑ b ∈ D, ‖BAXi d L g E m s t σ₁ σ₂ a b‖
              ≤ C * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))
-- EKPins.lean:261
def BAEKSameRow (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ σ : Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
        ‖BAuKer d L g E m s t σ σ‖ ≤ C
-- EKPins.lean:545
theorem baEKXiDecay_holds (d : ℕ) (Λ κ : ℝ) : BAEKXiDecay d Λ κ
-- EKPins.lean:556
theorem baEKXiBall_holds (d : ℕ) (Λ κ : ℝ) : BAEKXiBall d Λ κ
-- EKPins.lean:568
theorem baEKSameRow_holds (d : ℕ) (Λ κ : ℝ) : BAEKSameRow d Λ κ
### B.5 compiled nonempty instances (EKPinsInst; d = 3, L = sz0.L 0 = 4, s = 0, t = 1/2, κ = 1/2, Λ = 1, A = δ_0)
-- EKPins.lean:690
theorem inst_baEKSumNdecay :
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AI‖ ≤ ((1 - 0) / (1 - 1 / 2)) ^ 2 * ‖AI‖
690:theorem inst_baEKSumNdecay;704:theorem inst_baEKXiDecay;713:theorem inst_baEKXiBall;723:theorem inst_baEKSameRow;738:theorem inst_BAEKSumDecay1 (h;748:theorem inst_BAEKSumDecayNAL (h;758:theorem inst_BAEKSumDecayNonzero (h;843:theorem inst_BAEKSumDecay2 (h
### B.6 name clash and scope
top-level names (18) outside EKPins.lean in worktree:    4 RBM3D/Test/Axioms.lean  ; on main:        0; EKPinsInst on main:        0
$ git diff --stat main...t/T2388
 RBM3D.lean             |   1 +
 RBM3D/BA/EKPins.lean   | 856 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   4 +
 3 files changed, 861 insertions(+)
### B.7 provenance of copied text (RBM3D's own files; no RBM1D/RBM2D text copied, so no RBM1D/RBM2D diff-stat applies)
EKPins_sum_ball_le <- ek_sum_ball_norm_XiKer_le, Evolution/XiPins.lean:176-272 @3dc4f1c; EKPins_theta_absorb <- hprof/hzm, XiPins.lean:63-137 @3dc4f1c
baEKSameRow_holds <- ekSameRow_holds, XiPins.lean:357-426 @3dc4f1c; EKPins_Mss_shift, EKPins_Theta_shift <- baP8_BAMss_shift, baP8_BATheta_shift, BA/Prop6Path.lean:483-513 @83847ef
AzI, AzI_fastDecay, AzI_sumZero, zdistD_eI, zero_ne_eI <- ekAz, ek_fastDecay_Az, ek_sumZero_Az, ek_zdistD_E, ek_zero_ne_E, Evolution/Pins.lean:222-333 @d9de66f

### Narrative
- Delivered: targets 1-6. `RBM3D/BA/EKPins.lean` has 856 lines (stop line 2,000, split point 1,500: no E1a/E1b split); `RBM3D.lean` +1 import line (after `RBM3D.BA.KWardIneq`); `Test/Axioms.lean` +4 owed lines. Commits ed19b61 (15:37:14 by `date -u`) and b9ac5cf (15:42:50). The branch base is b7efc3b; `main` was at e67bfbd (T2385 merged) at session start, so the hub's rebase-union of `RBM3D.lean` and `Test/Axioms.lean` (ticket: H23 (b)) applies.
- Target 1: `BAuKer`, `BAUN`, `BAuKer_eq_one_add`, `BAuKer_convex` are the probe text (B.4 diff). Added: public def `BAXi` (`Ξ = (t-s) M Θ_t`, `A:98`) and `BAuKer_eq_one_add_Xi : BAuKer = 1 + BAXi`, so the Ξ pins can name Ξ.
- Target 2: the five pins are the probe text (B.4); `BAEKSumNdecay` carries `g ≤ Λ` and `BAReal`, of which the proof uses only `BAReal.1`.
- Target 3: `BAUN` is `tensorKer` (definitionally); merged `norm_tensorKer_le` (`Kernel/Evolution.lean:420`) plus the per-factor bound `(1-s)/(1-t)` from private `EKPins_norm_Q_le` (`‖M^(σσ')‖_(∞→∞) ≤ 1`: `BAMss_norm_eq_BAK`, `BAK_row_sum`) and `EKPins_norm_Theta_le` (`Θ = 1 + tMΘ`, `BATheta_resolvent`).
- Target 4: the pin shapes of `BAEKXiDecay`, `BAEKXiBall`, `BAEKSameRow` are not in the probe; they are the band forms (`Evolution/XiPins.lean:281-357`) with `(d Λ κ)`, `E m` and `BAReal` after `g`, and `σ₁ σ₂` (`σ` for the same-sign row) in place of `‖μ‖ = 1`. Proof of `(eq:decayXi)`: `BAXi = ((t-s)/t)(Θ - 1)` for `t > 0` (private `EKPins_Xi_eq`), `t = 0` forces `s = 0` and `Ξ = 0`; `Θ(a,b) = Θ(0,b-a)` (`EKPins_Theta_shift`); `baProp5_holds` with the zero mode absorbed by `zeroMode_le_of_ge_mul` (`EKPins_theta_absorb`); the diagonal uses `1 ≤ (Λ²+1)(g²+|1-t|)⁻¹`. Constants: Xi decay `C = C₅(1+2(2(k+2))^k) + Λ² + 1`, `c = c₅`; ball `4 C ballC k`; same-sign `1 + C_s(1 + Λ² expC k c_s)` (`baProp5s_holds`, `norm_le_sum_row_zero`). No `Mbound_AO`, no smallness hypothesis on `g` or `‖M - m₀ I‖`.
- Deviation from (a)(ii) (no verdict change, so no (a′)): the translation lemma is a copy of the private `baP8_BATheta_shift` (`Prop6Path.lean:497`), not of `KInduct_theta_shift`; both are private.
- Target 5: instances at `d = 3`, `L = sz0.L 0 = 4` (`LI_real`), `g₀ = gI ≤ 1/64` (`gI_le`), `BAReal` by `BAflow_real` (`hrI`), `κ = 1/2`, `Λ = 1`, `n = 2`, `s = 0`, `t = 1/2` (`gI_sq_le`), `A = δ_0` (`AI_zero : AI 0 = 1`). The proved theorems (Ndecay, XiDecay, XiBall, SameRow) are applied with every hypothesis discharged. The ticket asked for one open-pin instance (`inst_BAEKSumDecay1`, an implication from the pin); three more are added: `…NAL` (`σ = (+,+)`), `…Nonzero` (`s = 1-g₀²/L²`, `t = 1-g₀²/(2L²)`, `A = Finset.univ`) and `…Decay2` (sum-zero `AzI`, `AzI_vals`, `K = 2`, `L³ = 64 ≤ 16²`).
- Target 6: four `owedProps` lines (Decay1, NAL, Decay2: owner BA-E2; Nonzero: owner BA-E3); `BAEKSumNdecay` and the Ξ pins are not registered. B.2 shows the pre-check and the full build pass, with the four pins listed as `1 [no certificate]`.

## (c) Verified Mathlib names (all present in the environment of `RBM3D.BA.EKPins`; script output `present 36/36; absent: []`)
Matrix.linfty_opNNNorm_def Matrix.inv_submatrix_equiv Matrix.nonsing_inv_eq_ringInverse Finset.prod_le_prod₀ Finset.prod_const Fintype.card_fin Finset.sum_filter Fin.forall_fin_two Real.log_le_sub_one_of_pos Real.rpow_two Real.sqrt_eq_rpow Real.sqrt_sq div_le_iff₀ le_div_iff₀ one_le_div pow_le_pow_left₀ inv_anti₀ norm_smul_le norm_mul_le norm_add_le norm_sub_le Complex.norm_real Real.norm_of_nonneg Complex.ofReal_sub Matrix.one_apply_eq Matrix.one_apply_ne NNReal.coe_sum NNReal.coe_le_coe Real.sqrt_pos Real.rpow_pos_of_pos Finset.sum_add_distrib Finset.mul_sum Real.exp_le_one_iff div_nonpos_of_nonpos_of_nonneg sub_eq_of_eq_add' Complex.ofReal_ne_zero
Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- Open pins (registered as owed; instances only as implications): `BAEKSumDecay1`, `BAEKSumDecayNAL`, `BAEKSumDecay2` (BA-E2), `BAEKSumDecayNonzero` (BA-E3).
- T2388a: `lem:sum_Ndecay` at BA (`BAEKSumNdecay`) carries `BAReal d L g κ E m` and `g ≤ Λ`; the paper states no hypothesis and uses `(eq:WardM)` (`BASelf`) at BA. `κ` and `g ≤ Λ` are unused by the proof.
- T2388b: `(eq:decayXi)` at BA is proved for every `(a,b)` including `a = b`, from `Ξ = ((t-s)/t)(Θ - 1)` and `baProp5_holds`, not through `Mbound_AO` (paper `A:114`); the constant depends on `Λ` through the diagonal unit.
- T2388c: new public vocabulary `BAXi` (the paper's `Ξ^(i)`, `A:98`) and `BAuKer_eq_one_add_Xi`.
- Added by the repairer (claude-opus-5-5), Sat Oct 10 15:54:32 UTC 2026, per `docs/reports/T2388-audit.md` §7 items 1-2 (no Lean change; branch head b9ac5cf):
- T2388d: `BAEKSameRow` (`EKPins.lean:261`) states `‖BAuKer d L g E m s t σ σ‖ = ‖1 + Ξ^{(σσ)}‖_{∞→∞} ≤ C` for `0 ≤ s ≤ t < 1`. The paper's `(eq:samecolor)` (`A:209`) is `‖Ξ^{(i)}‖_{∞→∞} ≲ t - s` and `‖Proj_{e⊥} Ξ^{(i)}‖_{∞→∞} ≲ t - s` at `σ_i = σ_{i+1}`. The Lean form is weaker in two ways: it has no factor `t - s` and no `Proj_{e⊥}` part. It is the consequence that `A:227` uses for `i ∉ A` ("(eq:decompUalt) and the first bound in (eq:samecolor) give `‖1+Ξ^{(i)}‖_{∞→∞} ≲ 1`"), since `‖1 + Ξ‖ ≤ 1 + C(t-s)`. The paper uses the projected half at `A:220-223` for `i ∈ A`. It follows the band pin `EKSameRow` (`Evolution/XiPins.lean:305`). Consumers: in the band, `ekSameRow_holds` is used only as `‖uKer …‖ ≤ C_s`, at `Evolution/Nonzero.lean:149,174` (`lem:sum_decay_nonzero`, factors `i ∉ A`) and `Evolution/SumDecay.lean:423` (`(sum_res_2_NAL)`). So the BA-E3 consumer (`BAEKSumDecayNonzero`) needs only this form if it follows the band proof (`Nonzero.lean:12-22`). The `Proj_{e⊥}` half is not needed there: for `i ∉ A` no projection is applied, and for `i ∈ A` the band uses `Prop8ZeroMode`.
- T2388e: `BAEKXiBall` (`EKPins.lean:250`) is a Lean-only form that the paper does not state. For every `Λ' ≥ 1`, `1 ≤ R ≤ Λ' ℓ_s`, centre `ctr`, row `a` and any finite `D` with `|ctr - b| ≤ R` for all `b ∈ D`, it gives `∑_{b∈D} ‖Ξ_{ab}‖ ≤ C Λ'² (g²+|1-s|)/(g²+|1-t|)`, with `C = C(d,Λ,κ)`. In the paper this is an inline step of `A:131-149`: there the window is the cutoff `1(|b_i - a_1| ≤ W^ε ℓ_s)` (resp. `|b_i - b_1| ≤ W^ε ℓ_s`), the factor is `W^{2ε}`, and the sum is bounded through `(eq:decayXi)` and `(eq:1-sells2)`. The Lean form makes the window parameter `Λ'` explicit (`Λ' = W^ε` or `W^{2ε}` at the use sites, as in the band `Evolution/SumDecay.lean:20` `ρ = W^ε` and `Evolution/SumDecayZero.lean:21` `Λ' = W^{2ε}`). It allows any `D` in the ball, not only the `W^ε ℓ_s` cutoff set. It follows the band pin `EKXiBall` (`XiPins.lean:293`).
