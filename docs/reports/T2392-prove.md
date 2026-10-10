Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct 10 21:36:11 UTC 2026

Notation: `ρ = W^ε`, `r = (g²+|1-s|)/(g²+|1-t|)`, `P = (1-s)/(1-t)`, `q = ℓ_t²/ℓ_s²`, `Q = (t-s)/(1-t)`; paper `A:111-198`; band = `Evolution/SumDecay.lean` (SD), `Evolution/SumDecayZero.lean` (SZ); EK = `BA/EKPins.lean`.

### (i) Exponent table

| row | value | constraint | slack |
|---|---|---|---|
| `C_X` (ball) | `baEKXiBall_holds` EK:556, depends on `(d,Λ,κ)` | `Σ_{b∈D}‖Ξ‖ ≤ C_X Λ'² r`, `1≤R≤Λ'ℓ_s` | used at `Λ'=ρ` (Decay1, NAL), `Λ'=ρ²` (Decay2 near part) |
| `C_s` (same sign) | `baEKSameRow_holds` EK:568, `(d,Λ,κ)` | `‖BAuKer σ σ‖ ≤ C_s`; anchor `k` with `σ_k=σ_{k+1}` gives the pair `(σ_k,σ_k)` | none |
| `C_D, c` (decay) | `baEKXiDecay_holds` EK:545 | pointwise `(eq:decayXi)`, needs `g²/L² ≤ 1-t` (from `t ≤ 1-g²/L²`) | none |
| `C_6` (BD1) | `baProp6_holds` Prop6Path:891 at `c=1/2`, `(d,Λ,κ)` | `|r| ≤ ½|a|` | `2|y-b|+1 ≤ |a-b| ⇒ |y-b| ≤ ½|b-a|`, `a≠y`: 0 violations on 1300 triples (script) |
| `C_lat` | `latC(d-3)`, `Kernel/SumDecay.lean:50,149` (`(eq:latticesum_d3)`) | `1≤R`, `3≤L` | `log L ≤ ρ` absorbs the log |
| `4 ≤ ρ` | pin hypothesis | `ρ^{m} ≥ 4^{m}`; `W ≥ ρ` since `ε<1`, `W>1` | 0 at the instance (`W=16, ε=½`) |
| `P ≤ W` | from `W⁻¹ ≤ (1-t)/(1-s)` | tail `W^{-D}P^{n}` | at instance `P=2 ≤ 16` |
| `P ≤ 2qr` | `ek_ratio_le` (SD:67, public) | `g² ≤ L²(1-t)` | instance `2 ≤ 2qr = 3.9993` |
| **Decay1** `C = m'+2n` | `m'` least with `2(1+C_X)^{n-1} < 4^{m'}` | main `P(1+C_Xρ²r)^{n-1} ≤ ρ^{m'+2(n-1)} q r^n` (`ek_arith_res1`, SD:210, public); `ρ^{m'+2(n-1)} ≤ W^{(m'+2n)ε}` | slack `2ε` in the exponent; tail `W^{-D}P^n ≤ W^{-D+n} ≤ W^{-D+C}`, slack `m'+n` |
| **NAL** `C = m''+2n-2` | `m''` least with `C_s(1+C_X)^{n-1} < 4^{m''}` | `C_s(1+C_Xρ²r)^{n-1} ≤ ρ^{m''+2(n-1)} r^{n-1}` (`ek_arith_nal`, SD:231, public); `C_s ≤ W^{m''}` | tail `W^{-D}C_sW^{n-1} ≤ W^{-D+m''+n-1}`, slack `n-1 ≥ 1` |
| **Decay2** `C = (m₁+2n+2)+(m₂+n+4+K(n-1))` | `a₁=3^d(C_D+C₆)`, `a₂=3^d C₆ C_D C_lat`; `m₁` least with `(1+nC_X)(1+C_X)^{n-1}+2^{n-1}a₁^{n-2}a₂ < 4^{m₁}`; `m₂` least with `3+nC_X < 4^{m₂}` | (SZ:1411-1520); `log L ≤ ρ`, `L^d ≤ W^K` | complement term `W^{-D}(…)L^{d(n-1)}`: `K(n-1)` is exactly the `L^d ≤ W^K` cost |
| all `C` | functions of `(d,n,Λ,κ[,K])` only: `C_X,C_s,C_D,c,C_6` are the merged existentials of `(d,Λ,κ)` | fixed before `L g W ε D s t E m σ A` | quantifier order of the pins matches |

Sample constants (illustrative; `C_X=3, C_s=2, C_D=3, C_6=1`) in the script below: `n=2`: Decay1 `C=6`, NAL `C=4`, Decay2 (`K=2`) `C=26`.

**The steps that read `‖m‖=1`, a scalar `μ`, `UN`/`EKsgn` or the pin antecedents, and the BA replacement.**

| target | band (file:line) | band reads | BA replacement |
|---|---|---|---|
| Decay1 | SD:325-418 (`ek_UN_anchor_bound` SD:257-317) | antecedent `Prop5Decay` (:326); `hm`,`hμ`,`cycProd (EKsgn m σ)` (:276); `norm_t_mul_lt_one`, `uKer_eq_one_add_XiKer` (:289-293); `ekXiBall_holds` over `‖μ‖=1` (:298); row `‖uKer‖ ≤ P` via `norm_uKer_le` (:306,399) | no antecedent (`baProp5_holds`); factor `i` is `BAuKer (σ i) (σ (finRotate n i))`, no `μ`; `BAuKer_eq_one_add_Xi` EK:72; `baEKXiBall_holds` EK:556; row sum: `‖BAuKer‖ ≤ P` = private `EKPins_norm_uKer_le` EK:185 (with `_Q_le` :151, `_Theta_le` :161), **not importable: copy**, from `BAK_row_sum` + `BAMss_norm_eq_BAK`; `sum_norm_row_le` (Kernel/Evolution:78) |
| NAL | SD:420-518 | antecedents `Prop5Decay`, `Prop5Short` (:421); `hκm` (:428,473); `hcyc : cycProd = PropSpin σ_k · PropSpin σ_k` (:465-468) | `κ ≤ Im m` is inside `BAReal`; `hσ : σ k = σ (finRotate n k)` rewrites the pair to `(σ k, σ k)`; `baEKSameRow_holds` EK:568 (`baProp5s_holds`, Prop5Short:667) |
| Decay2 | SZ:1411-1520; `ekSZ_concrete` SZ:821-1159; `ekSZ_dXi_le` SZ:663-733 | antecedents `Prop5Decay, Prop5Short, Prop6Diff1` (:1412); `hμ` (:1475); `XiKer`, `Theta(tμ)`, `SB` (nearest-neighbour `S^{(B)}`) and `Theta_apply_add_right_of_three_le` (Props4:100, used SZ:663-733); `uKer_eq_one_add_XiKer`, `norm_Xi_le` (:898,922) | `BAXi`; `BAuKer_eq_one_add_Xi`; `‖BAXi‖ ≤ Q` from `Ξ=(t-s)QΘ`, `‖Q‖≤1`, `‖Θ‖≤(1-t)⁻¹` (copies of EK:151,161); **ΔΞ twin**: `Ξ = ((t-s)/t)(Θ_t-1)` for `t>0` (private `EKPins_Xi_eq` EK:314, copy), so `ΔΞ_{a;yb} = ((t-s)/t)(Θ_t(a,y)-Θ_t(a,b))` for `a≠y,a≠b`, shift `Θ(a,y)=Θ(0,y-a)` (private `EKPins_Theta_shift/_apply` EK:289,308, copy), `baProp6_holds` at `a'=b-a`, `r=y-b`; **`(t-s)/t = 1-s/t ≤ 1-s`** replaces the band factor `(t-s)` (the band consumer weakens `t-s ≤ 1-s` at SZ:1017), so `C₆` is unchanged; `t=0` forces `s=t=0`, `Ξ=0`; no `Mbound_AO`, no smallness of `g` or `‖M-m₀I‖` |

Reuse facts (script `grep`/`sed` counts): SZ has 44 `private` helpers and 1 public theorem; band lines (all `private`, so **not importable**, to be copied): Part I `ekSZ_core` SZ:44-601 = 558 (no `μ`/`Xi`/`uKer` token: 0 hits), lattice SZ:610-662 = 53 and SZ:734-820 = 87 (0 hits), Part III SZ:1161-1397 = 237 (0 hits). Public and importable: `ek_anchor_sum_le`, `ek_core_bound`, `ek_arith_res1`, `ek_arith_nal`, `ek_ratio_le` (SD:41-250), `latticesum_d3`, `latC_pos`. The design `T2378-design.md` §3 table calls Parts I, III "R reuse (802 lines)": reuse is by copy into `BA/EKSum.lean`.

### (ii) Concrete nondegenerate instance (all three targets)

Data: `d=3`, `n=2`, `Λ=1`, `κ=½`, flow datum `n=0` of `sz0` (`sz0_values`, Defs/Sizes:267: `L=4, λ=1/64`), `g=g₀=√t₀·λ` with `t₀∈[17/25, 25/36]` (Step1Fam:748,753) (`g₀ ≤ 1/64` is EK:656), `BAReal 3 4 g₀ ½ E m₀` is `hrI` (EK:668, compiled `BAflow_real`); `W=16, ε=½, D=2, K=2, s=0, t=½`; Decay1/Decay2 `σ=(+,-)`, NAL `σ=(+,+)`; `A=δ₀` (Decay1, NAL), `A=δ₀⊗(δ₀-δ_e)`, `e=(1,0,0)` (Decay2, `EKSumZero`). No external hypothesis: the antecedents of the band pins are merged theorems here, and `BAReal` is discharged by `hrI`; the concrete limit computation of lesson 14 does not arise.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2392/pre.py`
```
g=0.012885 ell_s=1 ell_t=1.0000 r=1.999668 q=1.0000 P=2.0 W^eps=4.0 logL=1.3863 L^d=64 W^K=256.0 1-t-g^2/L^2=0.499990
  all hypotheses: True []
g=0.013021 ell_s=1 ell_t=1.0000 r=1.999661 q=1.0000 P=2.0 W^eps=4.0 logL=1.3863 L^d=64 W^K=256.0 1-t-g^2/L^2=0.499989
  all hypotheses: True []
delta0 support points with |a0-a1|>=4: 0 | (sumAzero) over a1 for every a0: False | ||A||_inf = 1
delta0 x (delta0-delta_e) support points with |a0-a1|>=4: 0 | (sumAzero) over a1 for every a0: True | ||A||_inf = 1
identities hold: True | max ||Xi||/((t-s)/(1-t)) = 0.9869 | max ||u||/((1-s)/(1-t)) = 1.0 | max ((t-s)/t)/(1-s) = 1.0
grid max of ((t-s)/t)/(1-s) over 0<=s<=t<1: 1.0 (<=1 needed)
Z_5^3 triples (a=0,b,y) with 2|y-b|+1<=|a-b|: 1300 violations of (|y-b|<=|b-a|/2 and a!=y): 0
n=2: Decay1 C=m'+2n=6 (m'=2); NAL C=m''+2n-2=4 (m''=2); Decay2 (K=2) m1=10 m2=2 C=26.0
n=3: Decay1 C=m'+2n=9 (m'=3); NAL C=m''+2n-2=7 (m''=3); Decay2 (K=2) m1=14 m2=2 C=35.0
Decay1 main term  P(1+CX rho^2 r)^(n-1) = 193.968  <= rho^(m'+2(n-1)) q r^n = 1023.66 True | W^{(m'+2n)eps}= 4096.0  >= rho^(m'+2(n-1)): True
```
Reading: both extreme `t₀` give `1-t-g²/L² ≈ 0.49999 > 0`, `ℓ_s=ℓ_t=1`, `4 ≤ W^ε = 4` (tight, allowed), `log 4 = 1.386 ≤ 4`, `L^d = 64 ≤ W^K = 256`, `W⁻¹ = 1/16 ≤ 1/2`. `δ₀` meets `EKFastDecay` (no support pair at distance `≥ 4`); `δ₀⊗(δ₀-δ_e)` meets `EKFastDecay` and `EKSumZero`; `δ₀` alone is not sum-zero, hence not used for Decay2. The algebra lines check `u=(1-sQ)Θ=1+Ξ`, `Ξ=((t-s)/t)(Θ-1)`, `‖Ξ‖_{∞→∞} ≤ (t-s)/(1-t)`, `‖u‖_{∞→∞} ≤ (1-s)/(1-t)` on random complex `Q` with `‖Q‖_{∞→∞}<1`, and `(t-s)/t ≤ 1-s` on a grid (max ratio 1.0, attained at `s=0`).

### Verdicts

- `baEKSumDecay1_holds`: **PASS**. Hypotheses satisfiable (instance), exponents close with slack `2ε` (main) and `m'+n` (tail); no missing input.
- `baEKSumDecayNAL_holds`: **PASS**. Same; tail slack `n-1 ≥ 1`.
- `baEKSumDecay2_holds`: **PASS**. Needs the ΔΞ twin through `Ξ=((t-s)/t)(Θ-1)` and `baProp6_holds` (no `S^{(B)}` nearest-neighbour support in BA); the constant `(t-s)/t ≤ 1-s` costs nothing; `log L ≤ W^ε` and `L^d ≤ W^K` as pinned.
- Finding for 1b: the ticket's "reuse the band helpers" for Parts I, III is impossible by import (all `ekSZ_*` are `private`); they are copied verbatim (`ekSZ_` renamed to `EKSum_`). Totals of the band blocks to be copied or twinned are listed above.

### (a′) Preflight corrections: none (constants, ΔΞ route and copy-not-import finding of (a) used as written).

## (b) Script output — Sat Oct 10 21:56:41 UTC 2026
Branch `t/T2392` at `2177c1a`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2392`.

### b.0 Line count against the stop line (ticket: 2,000 binding; split mark 1,500)
```
$ wc -l RBM3D/BA/EKSum.lean
    1929 RBM3D/BA/EKSum.lean
$ for c in <section commits>; do git show $c:RBM3D/BA/EKSum.lean | wc -l; done
5969950       388 lines  T2392: BA/EKSum section 1-3: baEKSumDecay1_holds, baEKSumDecayNAL_holds
28631d8       947 lines  T2392: BA/EKSum section 4: Part I combinatorics (copy of band EKSum core)
10fb6d4      1521 lines  T2392: BA/EKSum section 5: Part II lattice estimates, first difference of Xi fro
60d46e5      1894 lines  T2392: BA/EKSum sections 6-7: Part III constants, baEKSumDecay2_holds
d6ad8f2      1929 lines  T2392: BA/EKSum section 8: instances; registry: remove three owedProps lines; RB
```

### b.1 Builds, hygiene, registry
```
$ lake build RBM3D.BA.EKSum 2>&1 | tail -1   (exit 0)
Build completed successfully (3758 jobs).
$ lake build 2>&1 | tail -1   (full library incl. #assert_rbm_axioms at the end of RBM3D.lean; exit 0)
Build completed successfully (4205 jobs).
$ lake env lean registry.lean   [import RBM3D; #assert_rbm_axioms; three owedProps lines removed]   exit 0
  output lines naming BAEKSumDecay1/NAL/2: 0; naming BAEKSumDecayNonzero: 1 (stays owed, BA-E3)
$ lake env lean docs/tickets/checks/T2392-check.lean   exit 0, output lines containing "error": 0
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/EKSum.lean   (no output)
$ git diff --stat main...t/T2392
 RBM3D.lean             |    1 +
 RBM3D/BA/EKSum.lean    | 1929 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |    3 -
 3 files changed, 1930 insertions(+), 3 deletions(-)
$ git diff main...t/T2392 -- RBM3D/BA/EKPins.lean | wc -l   (the pins are unchanged)
       0
```

### b.2 `#print axioms` (targets and instances)
```
'RBM.BA.baEKSumDecay1_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSumDecayNAL_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSumDecay2_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.EKSumInst.inst_baEKSumDecay1' [propext, Classical.choice, Quot.sound]
'RBM.BA.EKSumInst.inst_baEKSumDecayNAL' [propext, Classical.choice, Quot.sound]
'RBM.BA.EKSumInst.inst_baEKSumDecay2' [propext, Classical.choice, Quot.sound]
```

### b.3 Target statements (script: `#check @…`, `grep -n`); the pins are `BAEKSumDecay1/NAL/2`, `BA/EKPins.lean:103-131`, unchanged
```
RBM.BA.baEKSumDecay1_holds : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.BA.BAEKSumDecay1 d n Λ κ
RBM.BA.baEKSumDecayNAL_holds : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.BA.BAEKSumDecayNAL d n Λ κ
RBM.BA.baEKSumDecay2_holds : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.BA.BAEKSumDecay2 d n Λ κ
200:theorem baEKSumDecay1_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecay1 d n Λ κ := by
290:theorem baEKSumDecayNAL_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecayNAL d n Λ κ := by
1772:theorem baEKSumDecay2_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumDecay2 d n Λ κ := by
```

### b.4 Compiled nonempty instances (file lines 1902-1925)
Data: `d = 3`, flow datum `n = 0` of `sz0` (`L = 4`, `g₀ ≤ 1/64`, `BAReal` by `hrI`), `κ = 1/2`, `Λ = 1`, `n = 2`, `s = 0`, `t = 1/2`, `W = 16`, `ε = 1/2`, `D = 2`, `K = 2`.
```
theorem inst_baEKSumDecay1 : ∃ C : ℝ, 0 < C ∧
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) *
      (ellT (sz0.L 0) gI (1 / 2) ^ 2 / ellT (sz0.L 0) gI 0 ^ 2) *
        ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ 2 * ‖AI‖ + (16 : ℝ) ^ (-2 + C) :=
  inst_BAEKSumDecay1 (baEKSumDecay1_holds 3 2 1 (1 / 2))
theorem inst_baEKSumDecayNAL : ∃ C : ℝ, 0 < C ∧
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, true] 0 (1 / 2) AI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) *
      ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ (2 - 1) * ‖AI‖ + (16 : ℝ) ^ (-2 + C) :=
  inst_BAEKSumDecayNAL (baEKSumDecayNAL_holds 3 2 1 (1 / 2))
theorem inst_baEKSumDecay2 : ∃ C : ℝ, 0 < C ∧
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AzI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) *
      ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ 2 * ‖AzI‖ + (16 : ℝ) ^ (-2 + C) :=
  inst_BAEKSumDecay2 (baEKSumDecay2_holds 3 2 1 (1 / 2))
```
No hypothesis is left open. `AI = δ₀` (`EKFastDecay`), `AzI = δ₀ ⊗ (δ₀ - δ_e)`, `e = (1,0,0)` (`EKFastDecay`, `EKSumZero`) are E1's tensors (`EKPins.lean:648, 777`); E1's wrappers `inst_BAEKSumDecay*` (`EKPins.lean:737-850`) apply the pin at these data.

### b.5 Name-clash grep (new public names; private stem `EKSum_`)
```
$ grep -rn "baEKSumDecay1_holds\|baEKSumDecayNAL_holds\|baEKSumDecay2_holds\|EKSumInst\|inst_baEKSumDecay\|EKSum_" RBM3D RBM3D.lean docs/tickets/checks | grep -v "^RBM3D/BA/EKSum.lean"
(no output)
```

### b.6 Ports (source: band files of this project, last commits SumDecayZero `d9de66f`, SumDecay `1678ea4`, EKPins `76458c2`; no RBM1D/RBM2D text read or copied, so no sister `diff --stat`). Diff after `ekSZ_`→`EKSum_`, `ekSZU`→`EKSum_U`:
```
band SumDecayZero.lean:46-601 (Part I)            -> EKSum.lean:390-945   changed lines after rename: 0
band SumDecayZero.lean:609-656 (card_ball/win)    -> EKSum.lean:953-1001   changed lines: 1  (blank line only)
band SumDecayZero.lean:733-814 (ar_win/ar_psi/lattice) -> EKSum.lean:1117-1198  changed lines: 0
band SumDecayZero.lean:1163-1397 (Part III)       -> EKSum.lean:1523-1757   changed lines: 0
band SumDecayZero.lean:821-1157 (ekSZ_concrete)   -> EKSum.lean:1205-1517  adapted (abstract in Ξ): changed lines 50 in 17 hunks
band SumDecayZero.lean:1411-1520 (ekSumDecay2_holds) -> EKSum.lean:1772-1890 adapted: changed lines 65 in 12 hunks
BA/EKPins.lean:275-325 (private Mss_shift/Theta_shift/Theta_apply/Xi_eq) -> EKSum.lean:1003-1052   changed lines (EKPins_→EKSum_): 7  (docstrings)
Rewritten, no diff: SumDecay.lean:253-518 -> EKSum.lean:119-386; EKPins.lean:149-208 -> EKSum.lean:42-117 (+ EKSum_norm_Xi_le)
```

### b.7 Narrative
- Size: `BA/EKSum.lean` has 1,929 lines against the binding stop line 2,000. The 1,500 split mark was crossed at the section-5 commit (`10fb6d4`, 1,521 lines); I went on to the end because the ticket marks only 2,000 as binding and Parts III, IV and the instances fitted (final 1,929). See (d).
- Sections 1-3 (`EKSum.lean:42-386`): `EKSum_UN_anchor_bound` is the BA twin of `ek_UN_anchor_bound` (`SumDecay.lean:253`): the factor `i` is `BAuKer (σ i) (σ (finRotate n i))`, the ball sums are `baEKXiBall_holds` at both charges, the row bound is `EKSum_norm_uKer_le` (the private `EKPins_norm_uKer_le` re-proved from `EKSum_norm_Xi_le`), `ek_core_bound`, `ek_arith_res1`, `ek_arith_nal`, `ek_ratio_le` are the public band lemmas. NAL rewrites the anchor pair `(σ k, σ (k+1))` to `(σ k, σ k)` by `hk : σ k = σ (finRotate n k)` and uses `baEKSameRow_holds`.
- Section 4 (Part I, 556 lines), the card/lattice helpers (131 lines) and Section 6 (Part III, 235 lines) are verbatim copies of the band after the rename (b.6): the band `ekSZ_*` are private, so import was impossible (as (a) found).
- Section 5: `EKSum_concrete` is `ekSZ_concrete` made abstract in `Ξ : Fin n → Zd → Zd → ℂ` (hypotheses `hball`, `hdec`, `hdΞ`, `hrowΞ` replace `μ`, `XiKer`, `Theta`, `‖μ‖ = 1`); `EKSum_dXi_le` is new: for `t > 0`, `Ξ = ((t-s)/t)(Θ_t - 1)` (copy of `EKPins_Xi_eq`), so `ΔΞ_{a;yb} = ((t-s)/t)(Θ_t(a,y) - Θ_t(a,b))` for `a ≠ y, a ≠ b`, `Θ_t(a,y) = Θ_t(0,y-a)` (copied shift lemmas), and `baProp6_holds` at `c = 1/2`, `a' = b - a`, `r = y - b`; `(t-s)/t ≤ 1-s` replaces the band factor `t-s ≤ 1-s`; `t = 0` forces `Ξ = 0`.
- Section 7: `baEKSumDecay2_holds` is the band pin with `baEKXiBall_holds`, `baEKXiDecay_holds`, `baProp6_holds` for `CB`, `CD, c`, `C6`; the constant is `(m₁+2n+2)+(m₂+n+4+K(n-1))` as in (a); `BAUN = ∏ (1 + BAXi)` by `BAuKer_eq_one_add_Xi`.
- Section 8: the three instances apply E1's `inst_BAEKSum*` wrappers to the theorems (b.4). Only `BAReal` and the merged `baProp5/5s/6` enter; no smallness of `g` or of `‖M - m₀ I‖`, no `‖m‖ = 1`.
- Registry: three `owedProps` lines deleted in `Test/Axioms.lean`; `import RBM3D.BA.EKSum` added after the last import of `RBM3D.lean`.

## (c) Verified names
Present (`env.contains`, script `names.lean`): Mathlib/core, 46: `Matrix.linfty_opNNNorm_def, Matrix.one_apply_ne, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, norm_smul_le, norm_mul_le, norm_add_le, norm_le_pi_norm, pi_norm_le_iff_of_nonneg, pow_unbounded_of_one_lt, inv_le_of_inv_le₀, inv_div, Real.rpow_le_rpow_of_exponent_le, Real.rpow_natCast, Real.rpow_mul, Real.rpow_add, Real.rpow_nonneg, Real.rpow_one, one_le_pow₀, pow_le_pow_left₀, pow_le_pow_right₀, inv_anti₀, div_le_iff₀, le_div_iff₀, div_le_div_iff₀, Complex.norm_real, Complex.ofReal_sub, Real.norm_of_nonneg, Nat.cast_sub, Finset.sum_ite_eq, Finset.sum_add_distrib, Finset.sum_le_sum, Finset.sum_congr, Finset.prod_congr, Finset.mul_prod_erase, Finset.prod_le_prod₀, Finset.sum_le_sum_of_subset_of_nonneg, Finset.sum_le_card_nsmul, Finset.prod_add, Finset.card_powerset, Nat.floor_le, Nat.le_floor, Nat.lt_floor_add_one`.
Present, project (`RBM.`), 22: `sum_norm_row_le, ek_core_bound, ek_ratio_le, ek_arith_res1, ek_arith_nal, latticesum_d3, latC_pos, card_Zd, zdistD_neg, zdistD_zero, one_le_ellT, ellT_mono, one_sub_mul_ellT_sq_le, BA.baEKXiBall_holds, BA.baEKXiDecay_holds, BA.baEKSameRow_holds, BA.baProp6_holds, BA.BAuKer_eq_one_add_Xi, BA.BATheta_resolvent, BA.BAMss_norm_eq_BAK, BA.BAK_row_sum, BA.BAMB_shift`.
Verified absent as public names (`env.contains` false): `RBM.BA.BATheta_shift`, `RBM.BA.BATheta_apply` (only private copies, `EKPins.lean:289,308`, `Prop6Path.lean:495`), `RBM.BA.EKPins_Xi_eq` (private, `EKPins.lean:314`), `RBM.ek_UN_anchor_bound_BA`.

## (d) Open issues and paper-delta candidates
- **Process finding for the dispatcher:** the file crossed the ticket's 1,500 split mark (1,521 at section 5) and ends at 1,929 < 2,000. I continued because the ticket calls only 2,000 binding; if the 1,500 mark was meant as a hard stop, the stop would have been at the section-5 boundary (1,521 lines: Decay1 and NAL complete, Decay2 Parts III-IV and the instances missing).
- **Duplication:** 922 lines are verbatim copies of private band helpers (Part I 556, Part III 235, card/lattice helpers 131; b.6). A refactor ticket that makes those band helpers non-private (outside this ticket's files) would remove them.
- **Paper-delta candidate T2392a:** for the first difference of `Ξ` (`A:177-182`) the paper uses `(prop:BD1)` together with `(Mbound_AO)`/`(Mbound_AO2)`; the Lean BA proof uses `Ξ = ((t-s)/t)(Θ_t - 1)` and `baProp6_holds` only (no `Mbound_AO`, no nearest-neighbour `S^{(B)}`); the factor is `(t-s)/t ≤ 1-s`.
- **Note T2392b (no new difference):** the proved exponents are `m'+2n`, `m''+2n-2` and `(m₁+2n+2)+(m₂+n+4+K(n-1))`; the pins' `C` is existential and the complement of `(sum_res_2)` carries `L^d ≤ W^K` (D45, T2042a, already registered), against the paper's `(n+5)ε` and `W^{-D+n}` (`A:190-191`).
- **Merge notes:** `RBM3D.lean` and `Test/Axioms.lean` are edited on the branch as the ticket allows (one import line, three deletions); the hub's rebase-union (H23 (b)) applies. E1's `EKPinsInst.inst_BAEKSumDecay1/NAL/2` still take the pin as a hypothesis and compile unchanged.
