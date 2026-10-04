Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 10:58:36 UTC 2026

### (i) Exponent table
Sources read: ticket; `Loop/KLTree.lean` (`KLDecay` :269, `KLShort` :278, `KLPar` :250, `KLmaxDist` :372, `KLK_three`); `Loop/KLFinal.lean:243,260`; `Induction/Defs.lean:168,174`; `Induction/Step34Pins.lean:208,229`; `Defs/{Params,Tail,RadialSum}.lean`; paper `3_5:1069`; RBM2D `Induction/KcalDecay.lean:692-841`, `HierVocab.lean:205-240` (`9e0f275`, ticket cites `c9a24cf`).

| # | Quantity | Value / source | Constraint | Slack |
|---|---|---|---|---|
| 1 | `c_d, C_d` (edge, opposite charge) | `KLPT_holds.decay` (`KLDecay`): `‖Θ_t(0,a)‖ ≤ C_d B_{t,|a|} e^{-c_d|a|/ℓ_t}`, `l¹`, existential, depends on `(d,gmax)` | `0<g≤gmax`, `0≤t<1`, `L≥3` | not explicit (RBM2D has numerals 20000, 40002²; here `∃`) |
| 2 | `c_κ, C_κ` (edge, equal charge `ξ=t m²`) | `KLPT_holds.short` (`KLShort`): `≤ C_κ(1_{a=0}+g²e^{-c_κ|a|})`, depends on `(d,κ,gmax)` | `|E| ≤ 2-κ` (the only place `κ` enters), `g ≤ gmax` | `ℓ_t ≥ 1` turns `e^{-c_κ|a|}` into `e^{-c_κ|a|/ℓ_t}` |
| 3 | rate `c` | `min(c_d, c_κ)`, edges `≤ B* e^{-c|x-y|/ℓ_u}` | `>0` | none needed |
| 4 | `B_{u,0}` in the far region | premise `ℓ_u W^τ ≤ maxDist ≤ dL` and `W^τ>d` (eventually) force `ℓ_u<L`, i.e. `g²<L²(1-u)`; so `(L^d(1-u))⁻¹ < L^{2-d}g⁻² ≤ g⁻²`; `B_{u,r} ≤ B_{u,0} ≤ 2g⁻²` | `W^τ>d` iff `N^{𝔠τ}>d` suffices | `N` threshold only |
| 5 | **lower bound on `g`** | `B* ≤ C_B g⁻²`, `C_B = 2C_d + (C_κ(1+gmax²)+1)·max(1,gmax²)`; needs `W^{-Q} ≤ g` (`Q>0` fixed before `∀ᶠ N`); `WO` gives `lam ≥ W^{-d/2+𝔡}`, so `Q = d/2` works | `g⁻² ≤ W^{2Q}` | `Q = 3/2` at `d=3`: `lam_n = W_n^{-6/5}` for `sz0`, margin `W^{-3/2} ≤ W^{-6/5}` |
| 6 | tree counts | `|TSP k| ≤ 2^{k²}`; labels of internal nodes `≤ (L^d)^{k²}` (`nodes ⊆ Fin k × Fin k`); edge factor `B*^{k+|F|} ≤ B*^{k+k²}`; `W^{-d(k-1)} ≤ 1` | `k ≥ 3`; `k=2` direct from `KLK_two`; `k=1` vacuous (`maxDist=0`) | crude, as RBM2D `A = 2^{k²}C₀^{k+k²}` |
| 7 | path bound | `maxDist ≤ Σ_leaf|a_v-b_{par v}| + Σ_F|b_J-b_{par J}|` (tree path; `KLMolecule_path_le` is `private` there: port needed) | triangle inequality | exact |
| 8 | final power of `N` | `‖𝒦‖ ≤ A N^{P} e^{-c W^τ}`, `A = 2^{k²}(2C_B)^{k+k²}`, `P = k² + (k+k²)·2Q/d` (`L^d ≤ N`, `W^{2Q} ≤ N^{2Q/d}`) | `W^τ ≥ N^{𝔠τ}`, `W^D ≤ N^{D/d}` | needs `A N^{P+D/d} e^{-cN^{𝔠τ}} ≤ 1` eventually (true, `𝔠τ>0`). At `k=3,d=3,Q=3/2,τ=D=1`: `P+D/d = 9+12+1/3` |
| 9 | quantifier order of `STKcalDecay` | `0<κ, gmax, 𝔠, k≥1, τ, D, Q` then `∀ᶠ N`; threshold depends on these only | DECISIONS §29 (1)-(4): `u∈[0,1)` in pin; case (ii) boundary not used; `L^d ≤ W^K` not used (`L^d ≤ N`); `∀ᶠ N` | none |
| 10 | `Σ_a 𝒯_t(|a|_∞)` constant | `≤ C_∞/(1-t)`, `C_∞ = d^{d-2}2^d radC(d^{-1/2}) + 1` (`|a|_∞ ≥ |a|_1/d`, `𝒯_t` antitone, `B_{t,r/d} ≤ d^{d-2}B_{t,r}`; `sum_radial_exp_le` already in `Defs/RadialSum.lean:163`, so the ticket's "add the radial sum" is not needed); `l¹` version `C_1 = 2^d radC(1)+1` | `ℓ_t ≥ 1`; `(1-t)ℓ_t² ≤ g²+(1-t)` (`one_sub_mul_ellT_sq_le`); zero-mode term `≤ L^d(L^d(1-t))⁻¹` | `d=3`: `C_1 = 184577`, `C_∞ = 1.493e7`; table max `40.04`, `223.9` |
| 11 | `(eq:sumtwoloop)` exponents | `ρ=(1-s)/(1-t) ≤ B⁻^{𝔠d}` from `STConStInd` (`B := Bctl n t <1`); `ρ^{C_d} B^{1/5} ≤ B^{1/5-𝔠d C_d}`, want `≤ B^{1/6}` | `𝔠d C_d ≤ 1/30` i.e. `𝔠d ≤ 1/(30 C_d)`; `1/(1-t) ≤ η_t⁻¹` (`η_t=(1-t) Im m`, `Im m ≤ 1`) | T2039: `𝔠d = min(1/100,1/(60C_d),𝔠₀)` gives `𝔠d C_d ≤ 1/60`: slack factor 2; `C_d=4,𝔠d=1/240`: `1/5-1/60 = 0.1833 ≥ 0.1667` |
| 12 | uniform in time (T2) | `stKbound_holds`/`stKward_holds` have no `τ`-hypothesis other than `0 ≤ τ n<1`; for `u n ∈ [s n,t n]` need `0 ≤ s n`, `t n<1`, `s ≤ t`; `perTime_timeIcc_of_forall_seq` | hypotheses `SizeTendsto`, `∀ᶠ|E n| ≤ 2-κ`, `∀ᶠ 0<lam≤gmax` as in `stKbound_holds` | none |

Consumers (RBM2D, read): `DecayLoop.lean:540-541,633` calls `hK hκ c hc k hk τ' D'` with `hsize.eventually`, then at each `n` supplies `(L,W)`, `N=(WL)^d` (size), `N^𝔠 ≤ W` (`Bandwidth`), `|E n| ≤ 2-κ`, `u∈[0,1)`, `σ,a`, and the premise `ℓ_u W^τ' ≤ maxDist` (the indicator of the far set); `BcalE.lean:1589` (`bcalE_conj_i`) uses it the same way (`D'=(k+2)/c`). In `d ≥ 3` the consumers must also supply `g = lam n ≤ gmax` (`WO`: `lam ≤ 𝔡⁻¹`) and `W^{-Q} ≤ lam n` (`WO`, `Q=d/2`).

### (ii) Concrete instance and checks
Scripts (python3/numpy, no Lean) in `scratchpad/T2129/`: `k3.py`, `sumT.py`, `inst.py`; `d=3`; `Θ_ξ=(1-ξS^{(B)})⁻¹`, `𝒦^{(3)}` from `KLK_three`, `m=mE E`.

`python3 k3.py A` (`L=9,W=2,g=1/2,E=0`, max over all `σ`, all `(a₁,a₂,a₃=0)` by translation invariance, grouped by `maxDist`):
```
u=0.5  ellT=1.000 r=0:2.16e-02 r=1:1.34e-03 r=2:1.74e-04 r=3:3.35e-05 r=4:4.37e-06 r=6:1.37e-07 r=8:3.61e-09 r=10:1.30e-10 r=12:6.27e-12
u=0.99 ellT=5.000 r=0:6.10e-02 r=1:1.65e-02 r=2:9.68e-03 r=3:7.11e-03 r=4:4.82e-03 r=6:3.20e-03 r=8:2.48e-03 r=10:2.17e-03 r=12:2.00e-03
```
(log-slope in `r`: `-1.714` at `u=0.5` (`ℓ=1`), `-0.158` at `u=0.99` (`ℓ=5`, `-1/ℓ=-0.2`): decay at rate `c/ℓ_u` with `c<1`.)

**Finding 1 (target 1 is false as pinned): `python3 k3.py B`** (`L=9,W=2,E=0,u=1-g²`, so `ℓ_u=1`; premise `ℓ_uW^τ=2 ≤ maxDist`; `τ=D=1`, `W^{-D}=0.5`; `g` is any value in `(0,gmax]`):
```
g=0.3  max_(maxDist>=2)|K3|=3.790e-03  g^4*max=3.070e-05  W^-D=0.5 violated=False
g=0.1  max_(maxDist>=2)|K3|=1.772e-01  g^4*max=1.772e-05  W^-D=0.5 violated=False
g=0.03 max_(maxDist>=2)|K3|=2.009e+01  g^4*max=1.627e-05  W^-D=0.5 violated=True
g=0.01 max_(maxDist>=2)|K3|=1.614e+03  g^4*max=1.614e-05  W^-D=0.5 violated=True
```
Mechanism: at `1-u=g²` the opposite-charge propagator is `≈ g⁻²(2d+1-A)⁻¹` (entries `>0`), the equal-charge one stays bounded, so `|𝒦^{(3)}| ≈ c(L,W,a) W^{-6} g⁻⁴ → ∞` as `g→0` at fixed `(L,W,a)` (the data show `g⁴|𝒦|` constant). For every large `N` take `L=W=N^{1/6}` (`N^{1/10} ≤ W`), `a` with `maxDist ≥ W` (`3⌊L/2⌋ ≥ L`): all premises hold, and `g` small violates `≤ W^{-D}`. So `STKcalDecay` with `∀ g ∈ (0,gmax]` is false (RBM2D's `KcalDecay` has no `g`; its `B ≈ 180·40002²(1+log L)` is `g`-free). **Repair (hypothesis necessary, row 5):** add `Q>0` before `∀ᶠ N` and the premise `(W:ℝ)^(-Q) ≤ g`; then rows 1-9 close. The paper has it from `(eq:WO)` (`lam ≥ W^{-d/2+𝔡}`).

**Instance of the corrected target 1** (`python3 inst.py`; sequence `L_n=W_n=n+3`, `g=1/2,E=0,u=1/2,k=3,κ=1/10,gmax=1,𝔠=1/10,τ=D=1,Q=3/2`, `a=(0,(h,h,h),0)`, `h=⌊L/2⌋`, `ℓ_u=1`):
```
n= 0 N=7.290e+02 N^0.1=1.933 W=3 ellT*W=3.0 maxDist=3 W^-1.5=0.1925  all hyps: True
n= 5 N=2.621e+05 N^0.1=3.482 W=8 ellT*W=8.0 maxDist=12 W^-1.5=0.0442  all hyps: True
n=50 N=2.216e+10 N^0.1=10.828 W=53 ellT*W=53.0 maxDist=78 W^-1.5=0.0026  all hyps: True
sz0 (L=4(n+1), W=(2(n+1))^5): tau=1 premise ellT*W <= maxDist <= d*floor(L/2):
  n=0 W=32 max possible maxDist=6  premise satisfiable=False   (n=1,2,3 likewise False)
```
The merged `sz0` has `W ≫ L`, so at `τ=1` the premise is false there (vacuous); the instance must be the sequence above (`N=(n+3)^6 → ∞`), `∀ᶠ N` extracted by `Filter.Eventually.exists`/`tendsto`. The explicit threshold is not numerical (constants `c,C_B` are `∃`): this is the `∃`-extraction the ticket allows, not an astronomically large literal.

**Target 3 (`python3 sumT.py`)**, `d=3`, `(1-t)Σ_a 𝒯_t`, table over `L∈{9,33,129}`, `g∈{0.1,1}`, `1-t∈{10⁻¹,10⁻³,g²/L²}` (18 rows computed; summary):
```
constants: C_l1 = 2^d radC(1)+1 = 1.846e+05;  C_linf = d^(d-2) 2^d radC(d^-1/2)+1 = 1.493e+07
L=5 g=1 t=1/2 (target-3 instance): (1-t)*sum_a T_t(|a|_inf)=5.8541, l1=2.9168
max over table: l1 40.0440 <= 1.846e+05;  linf 223.9215 <= 1.493e+07
```
(e.g. `L=129,g=0.1,1-t=0.1`: `l¹ 40.04`, `l^∞ 223.9`; `L=129,g=1,1-t=6e-5`: `1.15`, `2.21`; rows grow with `L` and saturate, uniform bound holds.)

**`(eq:sumtwoloop)` deterministic inequality** (`inst.py`, merged `sz0`, `s=0`, `t=1/16`, `C_d=4`, `𝔠d=1/240`, `E=1/2`, `η=(1-t)Im m`):
```
exponent: c_d*C_d=0.01667 <= 1/30=0.03333; 1/5-c_d*C_d=0.18333 >= 1/6=0.16667
  n=0 L=4 W=32 g=1.56e-02 Bctl=3.305e-05 con_st_ind(c_d=1/240)=False  LHS=1.593e+00 (W^-d B)^(1/6)/eta=1.974e-01 ratio=8.073e+00
  n=1 L=8 W=1024 g=2.44e-04 Bctl=9.954e-10 con_st_ind(c_d=1/240)=True  LHS=6.150e-01 (W^-d B)^(1/6)/eta=3.481e-02 ratio=1.767e+01
  n=2 L=12 W=7776 g=2.14e-05 Bctl=2.270e-12 con_st_ind(c_d=1/240)=True  LHS=3.210e-01 (W^-d B)^(1/6)/eta=1.263e-02 ratio=2.542e+01
  n=3 L=16 W=32768 g=3.81e-06 Bctl=3.032e-14 con_st_ind(c_d=1/240)=True  LHS=1.926e-01 (W^-d B)^(1/6)/eta=6.152e-03 ratio=3.131e+01
```
(`B` in the printed headers is `Bctl`; `STConStInd` holds eventually (`n ≥ 1`), ratio `= ρ^{C_d} B^{1/5-1/6} η Σ_a𝒯_t`, which is `≤ ρ^{C_d}(1-t)Σ_a𝒯_t`, uniformly bounded by row 10; `ρ^{C_d}=(16/15)^4=1.29`.) Target 2 instance: `sz0`, `E=STflowE z0` (`|E n|=1/2 ≤ 2-1/10`), `0<lam_n≤1/64≤gmax=10`, `SizeTendsto` (merged `sz0_tendsto`), window `sInst=0 ≤ u ≤ tInst=1/16 <1` (`Green/Pins.lean:1453` already instantiates the same bridge at this window).

### Verdicts
* Target 1 (`STKcalDecay`, `stKcalDecay_holds`): **FAIL as pinned** (false: `g→0` at fixed `(L,W,a)`, Finding 1). PASS for the repaired pin with `Q` and `W^{-Q} ≤ g` (rows 1-9; edge bounds, counts, absorption close; `3 ≤ d` from `KLPT_holds`, §36 conditions: consumers are `lem_decayLoop`/`lem_BcalE`/`GridGoodEvent` under `3 ≤ d`). The dispatcher must amend the ticket pin before stage 1b (paper-delta candidate `T2129a`: pin needs `W^{-Q} ≤ g`, paper has it from `(eq:WO)`).
* Target 2 (`stKbound_timeIcc`, `stKward_timeIcc`): PASS (row 12), conditional on `0 ≤ s n`, `t n<1`, `s ≤ t`, and the hypotheses of `stKbound_holds`.
* Target 3 (lattice sum, `(eq:sumtwoloop)`): PASS; exponents close with `𝔠d C_d ≤ 1/30` (row 11). The radial sum with `e^{-√(r/ℓ)}` exists (`sum_radial_exp_le`); what is new is the `l^∞` reduction and the zero-mode term. `T2129b`: the sum is taken in `|·|_∞` (as `STGdecayW`, `zdistInf`), constant `C_∞`.

## (b) Script output, stage 1b (prover-hard continuation, Amend 1: pin of target 1 amended per ticket) — Sun Oct  4 11:38:47 UTC 2026

Last commit efd240c on t/T2129 (code commit f34c966; b4621fa and efd240c only reflow or reword docstrings); the only file written is RBM3D/Induction/KDecay.lean (RBM3D/Test/Axioms.lean and RBM3D.lean untouched).
```
$ git -C RBM3D --no-optional-locks diff --stat main...t/T2129 ; git log --oneline -3 t/T2129
 RBM3D/Induction/KDecay.lean | 1435 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1435 insertions(+)
efd240c T2129: KDecay docstring of stKcalDecay_holds: consumers are not yet in the library
b4621fa T2129: KDecay module docstring reflowed to 100 columns
f34c966 T2129: S3-06 Induction/KDecay (STKcalDecay proved, STKbound/STKward over TimeIcc, tail lattice sum and (eq:sumtwoloop))
$ lake build RBM3D.Induction.KDecay 2>&1 | tail -1   (worktree RBM3D-wt/T2129; warnings in its output for KDecay.lean: 0)
Build completed successfully (3715 jobs).
$ lake env lean axioms.lean   (#print axioms of the 16 new public declarations; filtered)
16 of 16 read [propext, Classical.choice, Quot.sound]: STKcalDecay stKcalDecay_holds stKbound_timeIcc stKward_timeIcc KDecay_tailC KDecay_one_le_tailC KDecay_sum_tailT_le stSumTwoLoop stSumTwoLoop_exists inst_stKcalDecay inst_stKcalDecay_admissible inst_stKbound_timeIcc inst_stKward_timeIcc inst_KDecay_sum_tailT_le inst_stSumTwoLoop inst_stSumTwoLoop_exists 
$ lake env lean precheck.lean  (import RBM3D; import RBM3D.Induction.KDecay; #assert_rbm_axioms; not committed)
exit 0
axiom audit: 3934 theorems, 1363 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 76 (borrowed 1, owed 60, structural 15).
grep -c STKcalDecay precheck.out: 0
$ lake build   (whole library incl. root #assert_rbm_axioms; root RBM3D.lean does not import KDecay yet, the hub adds it at merge), tail -1
Build completed successfully (3876 jobs).
$ for NAME in <the 16 new public names, KDecayInst>: grep -rn "\bNAME\b" RBM3D (worktree); git grep -n "\bNAME\b" main -- RBM3D   (outside KDecay.lean)
17 names: total matches outside KDecay.lean (worktree + main) = 0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git ... diff --stat c9a24cf HEAD -- RBM2D/Induction/{KcalDecay,HierVocab}.lean
9e0f275
 RBM2D/Induction/HierVocab.lean | 392 ++++++++---------------------------------
 RBM2D/Induction/KcalDecay.lean | 118 ++-----------
 2 files changed, 93 insertions(+), 417 deletions(-)
$ python3 portcheck.py  (non-comment lines of the ported ranges of KcalDecay.lean, c9a24cf vs 9e0f275)
path+dist_bounds: c9a24cf == 9e0f275 (non-comment lines): True
tree_bound: c9a24cf == 9e0f275 (non-comment lines): True
card_TSP,Kcal_far: c9a24cf == 9e0f275 (non-comment lines): True
Kcal_two_far: c9a24cf == 9e0f275 (non-comment lines): True
eventually: c9a24cf == 9e0f275 (non-comment lines): True
```

Ports (RBM2D RBM2D/Induction/KcalDecay.lean at c9a24cf line : RBM3D KDecay.lean line), each re-checked against this paper (Z2 L -> Zd d L, zdist2 -> zdistD, W^2 -> W^d, KLoop names -> merged KL names):
zdist2_symm 75 : KDecay_zdistD_symm 62; zdist2_tri 78 : 65; anc_step 213 : 88; path_aux 236 : 111; path_le 286 : 161; dist_bounds 294 : 168 (pairs part only);
kcalDecay_tree_bound 336 : KDecay_tree_bound 202; kcalDecay_card_TSP 549 : 474; kcalDecay_Kcal_far 560 : KDecay_Kn_far 485 (leaf/internal bounds are hypotheses);
kcalDecay_maxDist_two_le 611 : 525; kcalDecay_Kcal_two_far 619 : KDecay_Kn_two 532; kcalDecay_eventually 660 : KDecay_eventually 569 (real exponent P, c as free constant); kcalDecay 692 : stKcalDecay_holds 798.
Not ported (replaced): kcalDecay_theta_bound/leaf_bound/internal_bound (RBM2D property 5, numerals 20000, 40002^2, d = 2): here KDecay_edge_bound/KDecay_internal_bound from KLPT_holds (decay, short).

### Targets, extracted from the file by script (python3 extract.py NAME...: the declaration up to :=)
```lean
-- STKcalDecay (KDecay.lean:782)
def STKcalDecay (d : ℕ) : Prop :=
  ∀ κ gmax : ℝ, 0 < κ → 0 < gmax → ∀ 𝔠 : ℝ, 0 < 𝔠 → ∀ k : ℕ, 1 ≤ k → ∀ τ D : ℝ, 0 < τ → 0 < D →
    ∀ Q : ℝ, 0 < Q →
    ∀ᶠ N : ℕ in atTop, ∀ (L W : ℕ) [NeZero L] [NeZero W], (W * L) ^ d = N →
      (N : ℝ) ^ 𝔠 ≤ (W : ℝ) → 3 ≤ L →
      ∀ g : ℝ, 0 < g → g ≤ gmax → ((W : ℕ) : ℝ) ^ (-Q) ≤ g →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d L),
        ellT L g u * ((W : ℕ) : ℝ) ^ τ ≤ (KLmaxDist d L a : ℝ) →
          ‖KLK d L g W E u (KLloopOf d L σ a)‖ ≤ ((W : ℕ) : ℝ) ^ (-D)
-- stKcalDecay_holds (KDecay.lean:798)
theorem stKcalDecay_holds {d : ℕ} (hd : 3 ≤ d) : STKcalDecay d
-- stKbound_timeIcc (KDecay.lean:1062)
theorem stKbound_timeIcc (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) :
    ∀ k : ℕ, 1 ≤ k →
      sz.Prec (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
        (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))
-- stKward_timeIcc (KDecay.lean:1081)
theorem stKward_timeIcc (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) :
    ∀ k : ℕ, 2 ≤ k →
      sz.Prec (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖STKI sz n (E n) (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (p.1 : ℝ))⁻¹ *
          (sz.Bctl n (p.1 : ℝ)) ^ (k - 2))
-- KDecay_tailC (KDecay.lean:1119)
def KDecay_tailC (d : ℕ) : ℝ := (d : ℝ) ^ (d - 2) * 2 ^ d * radC (1 / (d : ℝ)) + 1
-- KDecay_sum_tailT_le (KDecay.lean:1241)
theorem KDecay_sum_tailT_le {d L : ℕ} [NeZero L] (hd : 2 ≤ d) {g t : ℝ} (hg : 0 ≤ g)
    (ht : t < 1) :
    ∑ a : Zd d L, tailT d L g t (zdistInf d L a : ℝ) ≤ KDecay_tailC d / (1 - t)
-- stSumTwoLoop (KDecay.lean:1262)
theorem stSumTwoLoop (hd : 2 ≤ d) {𝔠d Cd : ℝ} (h𝔠 : 0 < 𝔠d) (hCd : 0 ≤ Cd)
    (hcc : 𝔠d * Cd ≤ 1 / 30) {s t : ℕ → ℝ} (hcon : sz.STConStInd 𝔠d s t)
    (ht1 : ∀ᶠ n in atTop, t n < 1) {E : ℕ → ℝ} (hE : ∀ᶠ n in atTop, |E n| < 2)
    (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) :
    ∀ᶠ n in atTop, ∀ a₁ : Zd d (sz.L n),
      ((1 - s n) / (1 - t n)) ^ Cd * (sz.Bctl n (t n)) ^ (1 / 5 : ℝ) *
          ∑ a₂ : Zd d (sz.L n),
            tailT d (sz.L n) (sz.lam n) (t n) (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤
        KDecay_tailC d * (sz.Bctl n (t n)) ^ (1 / 6 : ℝ) * (etaT (E n) (t n))⁻¹
-- stSumTwoLoop_exists (KDecay.lean:1339)
theorem stSumTwoLoop_exists (hd : 2 ≤ d) {Cd : ℝ} (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (sz : Sizes d) (s t E : ℕ → ℝ), sz.STConStInd 𝔠d s t → (∀ᶠ n in atTop, t n < 1) →
        (∀ᶠ n in atTop, |E n| < 2) → (∀ᶠ n in atTop, 0 ≤ sz.lam n) →
        ∀ᶠ n in atTop, ∀ a₁ : Zd d (sz.L n),
          ((1 - s n) / (1 - t n)) ^ Cd * (sz.Bctl n (t n)) ^ (1 / 5 : ℝ) *
              ∑ a₂ : Zd d (sz.L n),
                tailT d (sz.L n) (sz.lam n) (t n) (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤
            C * (sz.Bctl n (t n)) ^ (1 / 6 : ℝ) * (etaT (E n) (t n))⁻¹
```

### Compiled nonempty instances (named theorems, same file; every deterministic hypothesis discharged in the proof; extracted the same way)
```lean
-- inst_stKcalDecay (KDecay.lean:940)
theorem inst_stKcalDecay : ∀ᶠ n : ℕ in atTop,
    ellT (n + 3) (1 / 2) (3 / 4) * (((n + 3 : ℕ) : ℝ)) ^ (1 : ℝ) ≤
        (KLmaxDist 3 (n + 3) (instA n) : ℝ) ∧
      ‖KLK 3 (n + 3) (1 / 2) (n + 3) 0 (3 / 4)
          (KLloopOf 3 (n + 3) ![true, false, true] (instA n))‖ ≤ (((n + 3 : ℕ) : ℝ)) ^ (-1 : ℝ)
-- inst_stKcalDecay_admissible (KDecay.lean:976)
theorem inst_stKcalDecay_admissible {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {𝔠 𝔡 : ℝ}
    (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {k : ℕ} (hk : 1 ≤ k) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ ≤ (KLmaxDist d (sz.L n) a : ℝ) →
          ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E u (KLloopOf d (sz.L n) σ a)‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D)
-- inst_stKbound_timeIcc (KDecay.lean:1384)
theorem inst_stKbound_timeIcc : ∀ k : ℕ, 1 ≤ k →
    sz0.Prec (U := fun n => TimeIcc sInst tInst n × (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
      (fun n p _ => ‖STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => (sz0.Bctl n (p.1 : ℝ)) ^ (k - 1))
-- inst_stKward_timeIcc (KDecay.lean:1393)
theorem inst_stKward_timeIcc : ∀ k : ℕ, 2 ≤ k →
    sz0.Prec (U := fun n => TimeIcc sInst tInst n × (Fin k → Bool) × (Fin (k - 1) → Zd 3 (sz0.L n)))
      (fun n p _ => ∑ x : Zd 3 (sz0.L n),
        ‖STKI sz0 n (STflowE z0 n) (p.1 : ℝ) ⟨List.ofFn p.2.1, List.ofFn p.2.2 ++ [x]⟩‖)
      (fun n p _ => (((sz0.W n : ℕ) : ℝ) ^ 3 * etaT (STflowE z0 n) (p.1 : ℝ))⁻¹ *
        (sz0.Bctl n (p.1 : ℝ)) ^ (k - 2))
-- inst_KDecay_sum_tailT_le (KDecay.lean:1405)
theorem inst_KDecay_sum_tailT_le : ∑ a : Zd 3 5, tailT 3 5 1 (1 / 2) (zdistInf 3 5 a : ℝ) ≤ KDecay_tailC 3 / (1 - 1 / 2)
-- inst_stSumTwoLoop (KDecay.lean:1410)
theorem inst_stSumTwoLoop : ∀ᶠ n in atTop, ∀ a₁ : Zd 3 (sz0.L n),
    ((1 - sInst n) / (1 - tInst n)) ^ (4 : ℝ) * (sz0.Bctl n (tInst n)) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd 3 (sz0.L n),
          tailT 3 (sz0.L n) (sz0.lam n) (tInst n) (zdistInf 3 (sz0.L n) (a₁ - a₂) : ℝ) ≤
      KDecay_tailC 3 * (sz0.Bctl n (tInst n)) ^ (1 / 6 : ℝ) * (etaT (STflowE z0 n) (tInst n))⁻¹
-- inst_stSumTwoLoop_exists (KDecay.lean:1423)
theorem inst_stSumTwoLoop_exists :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ a₁ : Zd 3 (sz0.L n),
      ((1 - sInst n) / (1 - tInst n)) ^ (4 : ℝ) * (sz0.Bctl n (tInst n)) ^ (1 / 5 : ℝ) *
          ∑ a₂ : Zd 3 (sz0.L n),
            tailT 3 (sz0.L n) (sz0.lam n) (tInst n) (zdistInf 3 (sz0.L n) (a₁ - a₂) : ℝ) ≤
        C * (sz0.Bctl n (tInst n)) ^ (1 / 6 : ℝ) * (etaT (STflowE z0 n) (tInst n))⁻¹
```

### Narrative (b), facts from the file and the logs above
1. Target 1, chain: `k = 1` is vacuous (`KLmaxDist = 0`). For `k ≥ 2`: `KLmaxDist ≤ d L` (`zdistD_le`) and `d < N^{𝔠τ} ≤ W^τ` (eventually) force `ellT L g u < L` (else `L W^τ ≤ d L`), hence `g² < L²(1-u)`, `Bparam d L g u 0 ≤ 2 g⁻²` (`KDecay_B0_le`) and `g⁻² ≤ W^{2Q}` from `W^{-Q} ≤ g`.
2. Constants and sources: `c = min c_d c_κ`, with `(C_d, c_d)` from `(KLPT_holds hd hκ hg).decay` (`KLDecay`, `Loop/KLTree.lean:269`) and `(C_κ, c_κ)` from `.short` (`KLShort`, :278); both are `∃` (no numerals; they depend on `(d,gmax)`, resp. `(d,κ,gmax)`). Edge bound `B = (2C_d + C_κ(1+gmax²) + 1) W^{2Q}` for leaves and internal edges (`KDecay_edges_far`): opposite charges have `m(+)m(-) = 1`, so `ξ = u` and `KLDecay` applies; equal charges use `KLShort`; `B_{u,r} ≤ B_{u,0}`, `ℓ_u ≥ 1`; `Θ - 1` adds `1`.
3. Counts: `|TSP k| ≤ 2^{k²}`, `(L^d)^{|nodes F|}` labels, `|nodes F|, |F| ≤ k²`, `maxDist ≤` total edge length (`KDecay_dist_bounds`): `‖𝒦‖ ≤ A N^{P_k} e^{-c W^τ}`, `A = 2^{k²}C₁^{k+k²}`, `P_k = k² + 2Q(k+k²)`, then `A N^{P_k+D} e^{-c N^{𝔠τ}} ≤ 1` eventually (`KDecay_eventually`), from `W ≤ N`, `L^d ≤ N` (`N = (W L)^d`), `W^τ ≥ N^{𝔠τ}`.
4. Hypotheses: `|E| ≤ 2-κ` enters only through `KLShort` (equal-charge edges; elsewhere `|E| ≤ 2`, `‖m‖ = 1`); `g ≤ gmax` through the constants of `KLPT_holds` and `C_κ(1+g²) ≤ C_κ(1+gmax²)`; `u < 1` for `‖ξ‖ = u < 1`; `3 ≤ L` for translation invariance (`KLIndStepA_Theta_apply_sub`).
5. Distances: merged `KLDecay`, `KLShort` and `KLmaxDist` are all `zdistD` (`l¹`) with `ellT L g u` and an explicit `g`: no `l¹`/`l^∞` conversion in target 1. Target 3 is in `zdistInf` and uses `zdistInf ≤ zdistD ≤ d·zdistInf` (`Defs/Sizes.lean`).
6. Consumer form (Amend 1): `inst_stKcalDecay_admissible` derives, from `sz.Admissible 𝔠 𝔡` alone, `W^{-d/2} ≤ W^{-d/2+𝔡} ≤ lam n` (`WO`, so `Q = d/2`), `lam n ≤ 𝔡⁻¹ = gmax`, `N^𝔠 ≤ W` (`Bandwidth`), `N → ∞` (`SizeTendsto`), `N = (W L)^d` (`rfl`), and applies `stKcalDecay_holds`.
7. Target 2: `stKbound_holds`/`stKward_holds` at every section `u n ∈ [s n, t n]` → `Green.perTime_timeIcc_of_forall_seq` (per time over `TimeIcc`) → `KDecay_prec_of_perTime_det` (deterministic family: each bad event is `∅` or the whole space, `P univ = 1 > N^{-1}`, so eventually empty), which gives the `Prec` with the union over `(u,σ,a)` inside `P`.
8. Target 3: `KDecay_sum_tailT_le`: first term of `B_{t,r}` by `sum_radial_exp_le` with `κ = 1/d` (`(|a|_∞+1)^{-(d-2)} ≤ d^{d-2}(|a|_1+1)^{-(d-2)}`, `e^{-√(r_∞/ℓ)} ≤ e^{-(1/d)√(r_1/ℓ)}`) and `(1-t)ℓ_t² ≤ g² + 1-t` (`one_sub_mul_ellT_sq_le`); zero-mode term: `L^d` points times `(L^d(1-t))⁻¹`. The exponents of `(eq:sumtwoloop)` close: `ρ = (1-s)/(1-t) ≤ B^{-𝔠d}`, `B = Bctl n (t n) < 1` (from `STConStInd`), `ρ^{C_d} B^{1/5} ≤ B^{1/5-𝔠d C_d} ≤ B^{1/6}` iff `𝔠d C_d ≤ 1/30`; `(1-t)⁻¹ ≤ η_t⁻¹` since `Im m ≤ 1`. The ticket's "add a radial sum for `e^{-√(r/ℓ_t)}`" was not needed (`sum_radial_exp_le`, (a) row 10).
9. DECISIONS §29: (1) `0 ≤ u < 1` in the pin; `0 ≤ s`, `t < 1` in target 2; `t < 1` in target 3. (2) no case-(ii) boundary (`grep -c "ilambda\|STCaseI\|STCaseII\|lam n ^ 2 /" KDecay.lean` = 0). (3) `L^d ≤ W^K` not used, only `L^d ≤ N`. (4) `∀ᶠ N` in the pin and `∀ᶠ n` for `t < 1`, `|E| < 2`, `0 ≤ lam` in target 3; target 2 keeps `∀ n` for the window, as `STKbound` itself and `STStep3R` (`∀ n, 0 ≤ s n`, `s n < t n`) do.
10. DECISIONS §36 for `stKcalDecay_holds (hd : 3 ≤ d)`: (i) input `KLPT_holds` is stated for `d ≥ 3`; (ii) its consumers `lem_decayLoop`, `lem_BcalE`, `GridGoodEvent` are not yet in the library (grep: only mentions in `Step34Pins.lean`); the pins above them, `STMainInd`, `STStep3R`, `STStep4R`, begin with `3 ≤ d →`; (iii) `inst_stKcalDecay_admissible (hd : 3 ≤ d)` and `inst_stKcalDecay` (`d = 3`).
11. Registry: `STKcalDecay` is concluded by `stKcalDecay_holds` and no theorem takes it as a hypothesis; the scan above lists no unregistered premise (exit 0): no line added to `RBM3D/Test/Axioms.lean`. The verdict "FAIL as pinned" for target 1 in (a) concerns the original pin; this report proves the Amend-1 pin.
12. Instances: `inst_stKcalDecay`: `L = W = n+3`, `N = ((n+3)(n+3))^3`, `g = 1/2`, `u = 3/4` (`ellT = 1`, `inst_ellT`), loop `(+,-,+)` with `a = (0,(h,h,h),0)`, `h = ⌊L/2⌋`: premise `ℓ_u W ≤ maxDist` proved for every `n` (`instA_far`), conclusion eventually in `n`. `sz0` has `W ≫ L` (as (a) found), so its premise is false at `τ = 1`; another family is used. Targets 2, 3 at `sz0`, `z0`, `(sInst, tInst) = (0, 1/16)`, `κ = 1/10`, `gmax = 10`; lattice sum at `d = 3, L = 5, g = 1, t = 1/2`; `stSumTwoLoop` at `C_d = 4`, `𝔠d = 1/240` (`sz0_con`).

## (c) Verified Mathlib names (all compile in `KDecay.lean`)
`Real.rpow_natCast/rpow_mul/rpow_add/rpow_neg/rpow_neg_one/rpow_one/rpow_le_rpow/rpow_le_rpow_of_exponent_le/rpow_le_rpow_of_exponent_ge/one_le_rpow/rpow_pos_of_pos/rpow_nonneg`, `tendsto_rpow_atTop`, `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, `Filter.Tendsto.eventually_gt_atTop`, `Real.le_sqrt_of_sq_le`, `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.exp_le_exp`, `Real.exp_le_one_iff`, `Real.exp_sum`, `tendsto_atTop_mono`.
`Finset.sup_le/le_sup/sum_pair/sum_coe_sort/card_powerset/card_le_univ/sum_nonneg`, `Fintype.card_fun`, `Fintype.card_coe`, `ZMod.val_natCast_of_lt`, `Equiv.sum_comp`, `Equiv.subLeft`, `MeasureTheory.measure_univ`, `measure_mono`, `ENNReal.ofReal_lt_one`.
`inv_anti₀`, `div_le_div_iff₀`, `div_le_div_of_nonneg_right`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `le_self_pow₀`, `one_le_mul_of_one_le_of_one_le`, `inv_lt_one_of_one_lt₀`, `Nat.le_self_pow`, `Nat.le_mul_of_pos_left/right`, `Nat.pow_le_pow_left`, `Complex.im_le_norm`, `Complex.mul_conj`, `Complex.normSq_eq_norm_sq`.
Deprecated in this Mathlib (compiler warnings from `lake env lean` during development): `if_false` (use `ite_false`), `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`), `push_neg` (use `push Not`). No name was found absent.

## (d) Open issues and paper-delta candidates
* `T2129a` (target 1): `STKcalDecay` carries the premise `W^{-Q} ≤ g` (`Q > 0` before `∀ᶠ N`), forced by (a) Finding 1 (false without it); the paper has it from `(eq:WO)`, `W^{-d/2+𝔡} ≤ ilambda`, i.e. `Q = d/2` (compiled in `inst_stKcalDecay_admissible`).
* `T2129b` (target 3): the lattice sum of `𝒯_t` is in the block `l^∞` distance `zdistInf`, with the explicit `C_∞(d) = d^{d-2} 2^d radC(1/d) + 1`, uniform in `L ≥ 1`, `g ≥ 0`, `t < 1`. At `d = 3` (`python3`): `C_∞(3) = 403108609.0000002` (`κ = 1/d`), against (a) row 10's `14930689.000000006` (`κ = d^{-1/2}`) and its table maximum `223.9` (from (a)); (a) is not wrong, the Lean constant is just cruder (avoids `√d`).
* `T2129c` (`(eq:sumtwoloop)`, second `≺`): `stSumTwoLoop` is a deterministic inequality with explicit `C = C_∞(d)`, eventually in `n`, under `𝔠d · C_d ≤ 1/30` (`stSumTwoLoop_exists`: `𝔠d = min (1/100) (1/(30 C_d))`, T2041e) and `∀ᶠ t n < 1`, `∀ᶠ |E n| < 2`, `∀ᶠ 0 ≤ lam n`; the first `≺` (with `+ W^{-D}`) is the Step-2 pin `STGdecayW`, not proved here.
* `T2129d` (target 2): `stKbound_timeIcc`, `stKward_timeIcc` need `0 ≤ s n ≤ t n < 1` for all `n` (the pins `STKbound`, `STKward` are `∀ n`), plus the hypotheses of `stKbound_holds`/`stKward_holds`; the paper's "uniformly in `u ∈ [s,t]`" has no such statement.
* `T2129e`: `stKcalDecay_holds`, `stKbound_timeIcc`, `stKward_timeIcc` take `3 ≤ d` (§36 conditions above); `KDecay_sum_tailT_le`, `stSumTwoLoop` take `2 ≤ d`.
* Constants differ from (a) rows 5, 8 (not errors): here `C₁ = 2C_d + C_κ(1+gmax²) + 1`, `A = 2^{k²}C₁^{k+k²}`, `P = k² + 2Q(k+k²) + D` (uses `W ≤ N`, cruder than row 8's `2Q/d`).
* The `∀ᶠ N` threshold of `STKcalDecay` is not numerical (`C_d, c_d, C_κ, c_κ` are `∃` in `KLPT_holds`); `inst_stKcalDecay` is therefore stated `∀ᶠ n`, not at one `n`.
* Not done / not claimed: the Step-3 skeleton's own use of `stKbound_timeIcc` (S3-27), `lem_decayLoop`, `lem_BcalE`, `GridGoodEvent` (consumers); `RBM3D.lean` import is added by the hub.
