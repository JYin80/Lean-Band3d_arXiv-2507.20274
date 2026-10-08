Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 01:06:05 UTC 2026

Notation: `k = m+2` is the loop length (`n_ = k`); `m = 0` is the new case `n_ = 2`. `e2 = min(ε₀,1)/2`. `C₁ = (1+40d(m+1))·6^{d(m+1)}`. `C₄ = qProxy4C`, `C_n = qProxyCn` are `Classical.choose` constants, positive but with no numeric value, so the script treats them as free parameters.

### (i) Exponent table (all quantities as in `QEndGrid.lean` `AltGridArith` :1183-1222 and `altGrid_arith` :1224-1320)

| quantity | value (new, `m ≥ 0`) | constraint | slack |
|---|---|---|---|
| `τ'` | `min(ε/4, e2/(40·d·(m+1)))` (the old `d·m` is replaced by `d·(m+1)`; the old value is `0` in the denominator at `m=0`) | `0<τ'`, `τ' ≤ ε/4` (`hdW1`), `τ'·(d·m) ≤ ε₁` (field `hτ'dm` :1196, used at :1482 for `hνt`) | `τ'·d·m ≤ e2·m/(40(m+1)) < e2/40 = ε₁`; at `m=0` the left side is `0`. The field `hτ'dm` keeps its type, so `AltGridArith` is unchanged. |
| `ε` | `min(e2/(8 max(C₄,C_n)), 1/2)` | `C₄ε, C_nε ≤ e2/8` | unchanged, no `m` |
| `ε'` | `ε/2` | `C_nε' ≤ e2/8` | unchanged |
| `ε₁ = ε_q` | `e2/40` | `ε₁ ≤ e2`, `2ε₁ < τ_N` | `τ_N − 2ε₁ = e2(1/8−1/20) = 3e2/40 > 0` |
| `τ_N` | `e2/8` | `τ_N ≤ e2` | `7e2/8` |
| `D''` | `2C_n+2+2C₄+k+(4k+1)/𝔠` | `0<D''`; `hD`: `(m+1)+2+2C_n+2 < D''+1` | `D''+1−LHS = 2C₄ + (4k+1)/𝔠 > 0` for every `m ≥ 0` |
| `D'`, `D_c` | `D''+2`, `D''+1` | `1<D'`, `1<D_c`; `hFv`: `2m+4 ≤ 𝔠D'` | `𝔠D' ≥ 4k+1 = 4m+9 ≥ 2m+4`, slack `2m+5` |
| `C_K` | `D₁+2C_max+8k+20+D''` | `hCKa`: `D₁+1+4(k+1)+k+2C_max+8 ≤ C_K`; `hCKb`: `D''+1+2k+5 ≤ C_K`; `hCKθ` (6 inequalities, affine in `θ∈[0,1]`, strict) | `hCKa`: `3k+7+D'' > 0`. Only `k ≥ 0` and `D'' > 0` are used; `3 ≤ k` is NOT needed (the only use of `hk3`, :1238, is `0<k`). |
| budget `altBudgetExpQN` at `k=m+2`, `ξ=−(2k+1)`, `D_Y=D_t=k+1` | 20 conjuncts; the theorem `altBudgetExpQN_of_choice` (QBudgetB.lean:711) has no lower bound on `k` | hypotheses `C₄ε, C_nε ≤ ε₀/8`, `D' ≥ C₄+C_n+(2k+1)/𝔠`, `D'' ≥ …` | holds at `m=0` (script below, all 20 conjuncts) |
| `hνt` | `(W^{τ'})^{dm} ≤ N^{ε₁}` | follows from `τ'dm ≤ ε₁`, `W ≤ N` (:1471-1482) | trivial at `m=0` (exponent `0`) |
| `hMΛ` (eventual) | `(2m+5)·3·4^{dm}·(2/√κ)·C₁·N^{2ε₁} ≤ N^{τ_N}` | exponent gap `τ_N−2ε₁=3e2/40` | at `m=0, d=3, κ=1`: constant `5·3·1·2·26136 = 784080`, gap `3/800` at `ε₀=1/10`: `N ≥ 10^{1571.8}` (eventual, see (ii)) |
| `altQFlow_initQ` window | `e = min(ε₁,1)`, `τ'' = e/(8·d·m)` at :539 | `0<τ''` (:536 `hdm`, needs `1 ≤ m`), `ωf^{dm} = W^{τ''dm} ≤ ν = N^{e/8}` | **the old formula fails at `m=0`**; replace by `τ'' = e/(8d(m+1))`, then `τ''·d·m = e·m/(8(m+1)) ≤ e/8`, and `ωd` at :583 changes from `=` to `≤` (slack `e/(8(m+1))`) |
| `startLevelQN` (QLevelsA.lean:421), `altYGridN` (QEndA.lean:194), `gridDriftQN` (QGridA.lean:2114) | called at `m`, `m+1`, `m+1` | `startLevelQN`, `altYGridN`: no lower bound on `m`; `gridDriftQN`: `1 ≤ m` at the mollifier index `m+1` | all satisfied at `m=0` (`1 ≤ 0+1`). `hm : 1 ≤ m` of `gridDriftQN_envelope` (QEndA.lean:247) is unused in the body (the call is `gridDriftQN … (m := m+1) (by omega)`). |
| `STbootRHS` lower index | pin uses `lo=1`; `altQFlow_core` concludes with `lo=2` and `altQFlow_Ylow_le_bootRHS` needs `3 ≤ k` (:426) | `XLK(k−1) ≤ STbootRHS lo …` | at `k=2` this is FALSE for `lo=2` (the sum `Icc 2 1` is empty; script below). It holds for `lo=1` because `Icc 1 (k−1) ∋ k−1`. Hence the core at `m=0` must conclude with `STbootRHS 1`. Chain: `STbootRHS 2 ≤ STbootRHS 1` (:418) is already available. |

Other lower-bound uses of `m`/`k` that are fine at `m=0`: `2 ≤ k` in `GridGoodNConcl`/`NQLinConcl`, `altQFlow_phi3_le`, `altQFlow_level_le` (all `2 ≤ k`); `1 ≤ 2k−1`; `altQFlow_nq_half` has `2 ≤ n_`; `hLK (m+1)`, `hDecay (m+1)` need `1 ≤ m+1`.

Dependency finding (the ticket's file list is incomplete as a mathematical matter): the `hm : 1 ≤ m` hypothesis is consumed not only by `altGrid_arith` but also by the private `altGrid_assembly` (QEndGrid.lean:831, call at :925 and :1613), `altQFlow_initQ` (QEndB1.lean:523), `altQFlow_core` (:721), `altQFlow_section` (:1001), and the destructuring `n_ = m+1+1` with `(by omega)` for `1 ≤ m` at :1232. The `m=0` case of the round therefore needs primed versions of all of these (the mathematics is unchanged except for `τ'`, `τ''`, `lo=1` above).

### (ii) Concrete nondegenerate instance

Data of the endpoint (as in `altGrid_instance`, QEndGrid.lean:1950-1958, with `m=0` in place of `m ≥ 1`): `d=3`, `κ=1`, `𝔠=1/6` (`d𝔠=1/2<1`), `τ=1/2`, `𝔡=1/10`, `E≡0`, `(s,t)=(0,1/2)`, `ε₀=1/10`, `D₁=1`, `sz0` (`d=3`, `L=4(n+1)`, `W=(2(n+1))^5`). Data of the round (as `inst_OeqQtRoundPT'`, QEndB1.lean:1251, whose docstring gives `s≡0`, `t≡1/16`, `κ=ε=𝔡=1/10`, `C_d=1`), with `n_=2` (`m=0`), `p=1`, `XL≡XLK≡1` in place of `n_=3,4`.

```
$ python3 -I .../scratchpad/T2313/inst.py     (exact Fractions; C4, Cn, Cmax free; sweeps m = 0,1,2,5)
m=0 k=2 C4=10 Cn=10 e2=1/20 eps=1/1600 tau'=1/6400 eps1=1/800 C_K=141.0 fails=[]
m=0 k=2 C4=1/100 Cn=1/100 e2=1/20 eps=1/2 tau'=1/2400 eps1=1/800 C_K=95.04 fails=[]
m=0 k=2 C4=1000000 Cn=5 e2=1/20 eps=1/160000000 tau'=1/640000000 eps1=1/800 C_K=2000305.0 fails=[]
m=1 k=3 C4=10 Cn=10 e2=1/20 eps=1/1600 tau'=1/6400 eps1=1/800 C_K=174.0 fails=[]
m=1 k=3 C4=1/100 Cn=1/100 e2=1/20 eps=1/2 tau'=1/4800 eps1=1/800 C_K=128.04 fails=[]
m=1 k=3 C4=1000000 Cn=5 e2=1/20 eps=1/160000000 tau'=1/640000000 eps1=1/800 C_K=2000338.0 fails=[]
m=2 k=4 C4=10 Cn=10 e2=1/20 eps=1/1600 tau'=1/7200 eps1=1/800 C_K=207.0 fails=[]
m=2 k=4 C4=1/100 Cn=1/100 e2=1/20 eps=1/2 tau'=1/7200 eps1=1/800 C_K=161.04 fails=[]
m=2 k=4 C4=1000000 Cn=5 e2=1/20 eps=1/160000000 tau'=1/640000000 eps1=1/800 C_K=2000371.0 fails=[]
m=5 k=7 C4=10 Cn=10 e2=1/20 eps=1/1600 tau'=1/14400 eps1=1/800 C_K=306.0 fails=[]
m=5 k=7 C4=1/100 Cn=1/100 e2=1/20 eps=1/2 tau'=1/14400 eps1=1/800 C_K=260.04 fails=[]
m=5 k=7 C4=1000000 Cn=5 e2=1/20 eps=1/160000000 tau'=1/640000000 eps1=1/800 C_K=2000470.0 fails=[]
C1= 26136 hMΛ const= 784080 gap exponent= 3/800 N>= 10^1571.8
$ python3 -I .../scratchpad/T2313/boot.py     (STbootRHS transcribed from Step34Pins.lean:402-406; XL≡1, XLK(1)=100, B=1/2, p=1)
k=2 lo=1 STbootRHS=104.1892  XLK(k-1)=100.0  XLK(k-1)<=RHS: True
k=2 lo=2 STbootRHS=4.1892  XLK(k-1)=100.0  XLK(k-1)<=RHS: False
k=3 lo=1 STbootRHS=105.1892  XLK(k-1)=1.0  XLK(k-1)<=RHS: True
k=3 lo=2 STbootRHS=5.1892  XLK(k-1)=1.0  XLK(k-1)<=RHS: True
```

The `fails=[]` field lists every checked conjunct that failed. Checked per row: `τ'>0`, `τ'≤ε/4`, `τ'dm≤ε₁`, `2ε₁<τ_N`, `τ_N≤e2`, `ε₁≤e2`, `hCKa`, `hCKb`, `hCKθ` at `θ∈{0,1}` (the six inequalities are affine in `θ`), `hD`, `hFv`, the 20 conjuncts of `altBudgetExpQN`, and `initQ` with `τ''=e/(8d(m+1))`: `τ''>0`, `τ''dm ≤ e/8`.

Eventual hypotheses: every `hMΛ`-type, `hdW1`, `hFv`, `hW0a/b` statement of `altGrid_assembly` is `∀ᶠ n`, so the instance needs no explicit `N`. The threshold above (`N ≥ 10^{1571.8}` for `hMΛ` at `ε₀=1/10`) is a bound on the eventually-quantified `n`, as in the existing m≥1 instance `altGrid_instance` (obtained by `.exists` on `∀ᶠ`). The Lean example takes `∃ n` from the eventual statement; no concrete `n` is exhibited. Nonemptiness of the index set of the pin (pairs `(w,u)`, `w<u`, and `w=u`) is the `QEndB1Inst` examples headed (3), file lines 1293-1303.

External hypotheses: none are added. The hypotheses of `STIngR` (`STLK s`, `STStep2Concl`, the pair controls `Ξ̂ ≺ XL, XLK`) stay as hypotheses of the example, as in the m≥1 instance (:1256-1290). The deterministic data are discharged by `inst_ing` at `sz0, z0, sInst, tInst` (:1251). For `n_=2` the pair hypotheses are `STlenL 2 1 m` (`m ≤ 3 ∨ m=3 ∨ m=4`) and `1 ≤ m ≤ 2` (`STlenL` def: Step34Pins.lean:391).

### Verdicts

- `altGridEndQN'` (with `τ' = e2/(40d(m+1))`, `m ≥ 0`) and its private `altGrid_arith'`/`altGrid_assembly'`: **PASS**. Every `AltGridArith` field holds at `m=0` (script). No field needs `1 ≤ m` beyond the `τ'` formula (the answer to the ticket's request). `hm` of `altGrid_assembly` is used only in the call to `gridDriftQN_envelope`.
- `gridDriftQN_envelope'`: **PASS** (statement identical with `hm` dropped; `hm` is unused in the body).
- `STXiRoundPT''` / `stOeqQtRoundPT''_holds`: **PASS**, with the two corrections to the ticket's sketch recorded above (not a failure of the statement): (1) `altQFlow_initQ`, `altQFlow_core`, `altQFlow_section` also carry `hm : 1 ≤ m` and need `m=0` copies, with `τ'' = e/(8d(m+1))`; (2) at `k=2` the core must conclude with `STbootRHS 1` (not `2`), since `XLK 1 ≤ STbootRHS 2 …` is false (script). The ticket's remark that `XLK 1 ≤ STbootRHS 1 … 2 p` is "trivial" is correct, but `altQFlow_Ylow_le_bootRHS` (lo=2, `3 ≤ k`) cannot be reused.

## (b) Script output (stage 1b, `prover-hard`, claude-sonnet-5-5; the first `date -u` of the stage printed Thu Oct  8 01:08:55 UTC 2026)

No correction to section (a) was needed, so there is no (a′). All commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2313` (branch `t/T2313`).

```
$ date -u
Thu Oct  8 01:22:24 UTC 2026
$ git log --oneline main..t/T2313
5a73635 T2313: STXiRoundPT'', stOeqQtRoundPT''_holds (n_ >= 2) with instances
0488c39 T2313: gridDriftQN_envelope' and altGridEndQN' (m >= 0) with instances
$ git diff --patience --stat main...t/T2313
 RBM3D/Induction/QEndA.lean    |  89 +++++
 RBM3D/Induction/QEndB1.lean   | 712 +++++++++++++++++++++++++++++++++
 RBM3D/Induction/QEndGrid.lean | 897 ++++++++++++++++++++++++++++++++++++++++++
 3 files changed, 1698 insertions(+)
$ git diff --patience main...t/T2313 | grep -c '^-[^-]'
0
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/QEndA.lean RBM3D/Induction/QEndGrid.lean RBM3D/Induction/QEndB1.lean
RBM3D/Induction/QEndA.lean:0
RBM3D/Induction/QEndGrid.lean:0
RBM3D/Induction/QEndB1.lean:0
```

#### Builds
```
$ lake build RBM3D.Induction.QEndA > log 2>&1; echo exit=$?; grep -E 'error|sorry|Build completed' log
exit=0
Build completed successfully (3864 jobs).
$ lake build RBM3D.Induction.QEndGrid > log 2>&1; echo exit=$?; grep -E 'error|sorry|Build completed' log
exit=0
Build completed successfully (3865 jobs).
$ lake build RBM3D.Induction.QEndB1 > log 2>&1; echo exit=$?; grep -E 'error|sorry|Build completed' log
exit=0
Build completed successfully (3870 jobs).
$ lake build > log 2>&1; echo exit=$?; tail -1 log     # whole library incl. #assert_rbm_axioms (worktree RBM3D.lean)
exit=0
Build completed successfully (4123 jobs).
```

#### Axioms of the new public declarations (Lean prints the name in quotes, so `STXiRoundPT''` shows as `...STXiRoundPT'''`)
```
$ lake build RBM3D.Induction.QEndA RBM3D.Induction.QEndGrid RBM3D.Induction.QEndB1 2>&1 | grep -F -e <8 exact quoted names> | sed 's/^info: //'
RBM3D/Induction/QEndA.lean:2026:0: 'RBM.Ind.gridDriftQN_envelope'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndA.lean:2027:0: 'RBM.Ind.QEndAInst.gridDriftQN_envelope'_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndGrid.lean:3043:0: 'RBM.Ind.altGridEndQN'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndGrid.lean:3044:0: 'RBM.Ind.QEndGridInst.altGrid_instance'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2034:0: 'RBM.Gauss.Sizes.STXiRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2035:0: 'RBM.Gauss.Sizes.STOeqQtRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2036:0: 'RBM.Ind.stOeqQtRoundPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2037:0: 'RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### Target statements (extracted from the files by script)
```
$ awk <def STXiRoundPT'' .. blank line> RBM3D/Induction/QEndB1.lean
def STXiRoundPT'' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2)
          (sz.Bctl n (s n)) n_ p)
$ awk <def STOeqQtRoundPT'' .. blank line> RBM3D/Induction/QEndB1.lean
def STOeqQtRoundPT'' (d : ℕ) : Prop :=
  STIngR d STCaseI (fun sz E s t => STXiRoundPT'' sz E s t)
$ awk <theorem stOeqQtRoundPT''_holds, first line> RBM3D/Induction/QEndB1.lean
1841:theorem stOeqQtRoundPT''_holds : ∀ d : ℕ, STOeqQtRoundPT'' d := by
$ awk <theorem gridDriftQN_envelope' .. ':= by'> RBM3D/Induction/QEndA.lean
theorem gridDriftQN_envelope' {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ)
    (τK : ℝ) (hτK : 0 < τK) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : sz.STKbound E) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n)
    (σ : Fin (m + 1 + 1) → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n → ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖rGridQN sz E s v K n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω a‖ ≤
        qErrQN sz E s v K n (m + 1) ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)))
          (1000 * (1 + ((d * (m + 1) : ℕ) : ℝ)) ^ 2)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j := by
```

#### Statement diffs against the merged originals and against the check-file pin
```
$ diff <(statement of gridDriftQN_envelope) <(statement of gridDriftQN_envelope')
1c1
< theorem gridDriftQN_envelope {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m)
---
> theorem gridDriftQN_envelope' {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ)
$ diff <(statement of altGridEndQN) <(statement of altGridEndQN')
1c1
< theorem altGridEndQN :
---
> theorem altGridEndQN' :
8c8
<     ∀ m : ℕ, 1 ≤ m →
---
>     ∀ m : ℕ,
$ diff <(def STXiRoundPT' ) <(def STXiRoundPT'')   # the T2310 pin vs the new pin
1c1
<   ∀ n_ p : ℕ, 3 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
---
>   ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
$ diff <(check-file def STXiRoundPT''_pin, sed 's/_pin//') <(def STXiRoundPT''), bodies after the docstrings
(empty diff output above = identical)
$ lake env lean <scratch copy of docs/tickets/checks/T2313-check.lean + 2 examples: stOeqQtRoundPT''_holds_pin := RBM.Ind.stOeqQtRoundPT''_holds ; STXiRoundPT''_pin = STXiRoundPT'' by rfl> ; grep -c error
exit=0
0
```

#### Compiled nonempty instances
```
$ awk <theorem inst_OeqQtRoundPT'' .. blank> RBM3D/Induction/QEndB1.lean
theorem inst_OeqQtRoundPT'' :
    InstIngConcl (fun sz E s t => STXiRoundPT'' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STXiRoundPT'' sz E s t) (stOeqQtRoundPT''_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos
$ awk <first 'example (hLK' after the '(6) with the conclusion applied' docstring .. blank> RBM3D/Induction/QEndB1.lean
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 2 1 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 2 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    PrecPT sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 2 ω)
      (fun n q _ => sz0.Bctl n q.1.2 ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 2 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqQtRoundPT''
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 2 1 le_rfl le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp
$ grep -n -e "^example := altGrid_instance' 0" -e "^theorem altGrid_instance' " RBM3D/Induction/QEndGrid.lean ; first 6 lines of its proof (it is stated for every m : ℕ, so m = 0 is a specialization)
2879:example := altGrid_instance' 0
2845:theorem altGrid_instance' (m : ℕ) :
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := altGridEndQN' sz0 1 (1 / 6) (1 / 2) (1 / 10)
    agE agS agT (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    sz0_bandwidth sz0_WO agE_abs agS_nonneg agS_le_agT agT_lt_one agCaseI rangeCond_half agWt m
    agOne agOne agOne agOne agOne (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) agV
    agS_le_agV agV_le_agT (1 / 10) (by norm_num) 1 one_pos
$ last 4 lines of the proof of gridDriftQN_envelope'_instance (RBM3D/Induction/QEndA.lean)
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  exact (gridDriftQN_envelope' sz0 1 one_pos 0 1 one_pos sz0_tendsto hKb
    (fun _ => by norm_num [E0]) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (Filter.Eventually.of_forall lam_pos_n) σalt0).exists
$ the index set of the pin is nonempty (pairs w<u and w=u, existing examples (3), RBM3D/Induction/QEndB1.lean)
1949:example (n : ℕ) : ∃ q : STPair sInst tInst n, q.1.1 < q.1.2 :=
1952:example (n : ℕ) : ∃ q : STPair sInst tInst n, q.1.1 = q.1.2 :=
```

#### Name-clash grep (declarations with the new public names; whole RBM3D tree)
```
$ grep -rnF -e <7 declaration heads 'theorem gridDriftQN_envelope\'' ...> RBM3D RBM3D.lean | cut -c1-96
RBM3D/Induction/QEndB1.lean:100:def STXiRoundPT'' (E s t : ℕ → ℝ) : Prop :=
RBM3D/Induction/QEndB1.lean:121:def STOeqQtRoundPT'' (d : ℕ) : Prop :=
RBM3D/Induction/QEndB1.lean:1841:theorem stOeqQtRoundPT''_holds : ∀ d : ℕ, STOeqQtRoundPT'' d :=
RBM3D/Induction/QEndB1.lean:1975:theorem inst_OeqQtRoundPT'' :
RBM3D/Induction/QEndA.lean:313:theorem gridDriftQN_envelope' {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ 
RBM3D/Induction/QEndA.lean:1535:theorem gridDriftQN_envelope'_instance :
RBM3D/Induction/QEndGrid.lean:2176:theorem altGridEndQN' :
RBM3D/Induction/QEndGrid.lean:2845:theorem altGrid_instance' (m : ℕ) :
$ date -u
Thu Oct  8 01:22:38 UTC 2026
```

#### Narrative
- Scope: only the three sole writable files changed; the diff has no deleted line, so the originals (`gridDriftQN_envelope`, `altGridEndQN`,
  `altGrid_arith`, `altGrid_assembly`, `altQFlow_*`, `stOeqQtRoundPT'_holds`) are untouched. No new hypothesis, no weakened target.
- Public additions: `gridDriftQN_envelope'` (QEndA, `hm : 1 ≤ m` dropped), `altGridEndQN'` (QEndGrid, `∀ m : ℕ, 1 ≤ m →` ↦ `∀ m : ℕ,`),
  `STXiRoundPT''`, `STOeqQtRoundPT''`, `stOeqQtRoundPT''_holds` (QEndB1) and one instance theorem per file (listed above).
- Private additions (as section (a) predicted): `altGrid_assembly'` (calls `gridDriftQN_envelope'`), `altGrid_arith'` (QEndGrid);
  `altQFlow0_initQ`, `altQFlow0_Ylow_le_bootRHS`, `altQFlow0_core`, `altQFlow0_section` (QEndB1); `σalt0` (QEndA, instance data).
- Changes against the copied text, all of them: (1) `τ' = min (ε/4) (e₂/(40 d (m+1)))`; the field `hτ'dm : τ' * (d * m) ≤ ε₁` keeps its type
  and follows from `τ' d m ≤ τ' d (m+1) ≤ e₂/40`; `hk3 : 3 ≤ k` became `2 ≤ k`; the rest of `altGrid_arith'` is the text of `altGrid_arith` and compiles
  with `hmR : 0 ≤ m` in place of `1 ≤ m`. (2) `altQFlow0_initQ`: far-decay window `τ'' = e/(8 d (m+1))`, `hωd` from `τ'' d m ≤ e/8`. (3) `altQFlow0_core` concludes with
  `STbootRHS 1`; the level bound is `altQFlow_level_le` (lo 2) plus `altQFlow_bootRHS_two_le_one`, and `XLK (k-1) ≤ STbootRHS 1` is
  `altQFlow0_Ylow_le_bootRHS` (`2 ≤ k`; with lo 2 it is false at `k = 2`, script in (a)). (4) `altQFlow0_section`: alternating part with lo 1,
  non-alternating part (`altQFlow_nq_half`, lo 2) lifted by `STbootRHS 2 ≤ STbootRHS 1`.
- Statement checks: the body of `STXiRoundPT''` equals the check-file pin (empty diff); a scratch copy of the check file plus two examples
  (`stOeqQtRoundPT''_holds_pin := RBM.Ind.stOeqQtRoundPT''_holds`; `STXiRoundPT''_pin = STXiRoundPT''` by `rfl`) compiles (exit 0, 0 errors). `altGridEndQN'` implies the
  pin `T2302_altGridEndQN` (compiled `example : T2302_altGridEndQN := fun … => altGridEndQN' …` in QEndGrid.lean).
- Instances: `altGrid_instance' (m : ℕ)` (QEndGrid) is `altGrid_instance` with `1 ≤ m` dropped, at `sz0`, `κ = 1`, `𝔠 = 1/6`, `τ = 1/2`, `𝔡 = 1/10`,
  `(s,t) = (0,1/2)`, `v ≡ 1/2` (`s < v`), `ε₀ = 1/10`, `D₁ = 1`; `example := altGrid_instance' 0` is the loop length 2. `gridDriftQN_envelope'_instance`
  (QEndA) is at `m = 0`, `K ≡ 4`, `v ≡ 1/2`. Example (6) of `QEndB1Inst` applies `stOeqQtRoundPT''_holds` at `n_ = 2`, `p = 1`, `XL ≡ XLK ≡ 1`; (6') the
  same at `n_ = 3`. Every deterministic hypothesis is discharged by `inst_ing`; `STLK s`, `STStep2Concl` and the pair controls `Ξ̂ ≺ 1` stay hypotheses
  of the examples (Step 3-4 conclusions, other gates' pins), as in the T2310 examples (1), (2).
- `stOeqQtRoundPT''_holds` is the per-time (`PrecPT`) form for every `n_ ≥ 2`, not the `Prec` form; the lift is T2314. No port from RBM1D/RBM2D
  (all copies are of RBM3D text), so there is no RBM1D/RBM2D diff-stat.

## (c) Verified Mathlib names (each `#check`ed by `lake env lean` on a scratch file importing `RBM3D.Induction.QEndB1`; no name was found absent)
`Nat.cast_nonneg`; `mul_le_mul_of_nonneg_left`; `mul_le_mul_of_nonneg_right`; `Real.rpow_natCast`; `Real.rpow_mul`; `Real.rpow_le_rpow`;
`Real.rpow_le_rpow_of_exponent_le`; `Nat.mul_le_mul_left`; `Nat.le_succ`; `Nat.mul_pos`; `Finset.single_le_sum`; `Finset.mem_Icc`; `Finset.sum_nonneg`.

## (d) Open issues and paper-delta candidates
- `T2313a`: `STXiRoundPT''` is `STXiRoundPT'` with `3 ≤ n_` ↦ `2 ≤ n_` (diff above); the paper states `n ≥ 2` (`paper/tex/3_5_Loop_Hierarchy.tex:1365`);
  the `PrecPT` per-time form of `T2310a` applies unchanged. At `n_ = 2` the third sum of `STbootRHS` runs over `Icc 2 1 = ∅`.
- `T2313b` (ticket text vs Lean, no change of any statement): the ticket expected one-line substitutions in three declarations; the Lean proof needs the
  private copies listed above, `altQFlow0_core` at `n_ = 2` concludes with `STbootRHS 1` (the pin already has lo 1), and the field `hτ'dm` is not rephrased.
- Open: QEndGrid.lean gained 897 lines, mostly near-duplicate of `altGrid_assembly`/`altGridEndQN`; deriving the originals from the primed versions
  would change frozen text and was not done.
- Open: the examples keep `STLK s`, `STStep2Concl` and the pair controls as hypotheses (other gates' pins); T2314 consumes `stOeqQtRoundPT''_holds`.
