Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 21:57:43 UTC 2026

Notation (d ≥ 3, regime (iii), one time u): x=1−u, Mu=W^d x (replaces RBM2D `M_u=W²ℓ_u²η_u`; ℓ_u=1 since x ≥ lam², `3_5:2287`), A=Mu⁻² (amplitude of `T_{u,D}`, `3_5:2297`), P=x⁻¹Mu⁻¹=W^d A (the prefactor of `res_deccalE_lk`, `Step5Pins.lean:167-170`). Scripts: scratchpad `T2164/{consts,consts2,lkchain2,instance,checks}.py` (python3), outputs below.

### (i) Exponent table

| item | value / constraint | slack |
|---|---|---|
| neighbour count of `gexRHS` (`Green/Pins.lean:101`, `zdistInf ≤ 1`) | 3^d per side = 27 (L ≥ 3), pairs 9^d = 729. NOT the portmap's (1+2d)²=49 (`T2134-portmap.md:405`; that is `zdistD ≤ 1`, 7 per side) | script `checks.py` (below) |
| (e7) constant | `‖G_pq‖² ≤ 9^d Λ (W^{-D}+J T_u(r−2))`, r ≥ ℓ*_u/8+2, ℓ*_u=(log W)^{3/2} (ℓ_u=1) | 25 → 729 |
| (e8) constant | `9^d(K₀/Mu+2J/Mu²)+W^{-d} ≤ 2·9^d K₀ Mu⁻¹(1+J/Mu)` (uses W^{-d} ≤ Mu⁻¹, K₀ ≥ 1) | 50 → 1458 |
| (e2) scale | 1 ≤ Mu ≤ W^d (x ≤ 1; Mu ≥ lam²W^d ≥ W^{2𝔡} ≥ 1) | at instance Mu=2^30 |
| (e10) ball counts | `#{|z|∞ ≤ R} ≤ (2R+1)^d`; sharp R=1: 3^d | exact (script) |
| shift (e4b) | `e^{-√max(r−1,0)} ≤ e·e^{-√r}` (SB support `zdistD=1 ⇒ zdistInf=1`, `Defs/Block.lean:44`) | factor e |
| convolution | `Σ_x e^{-√p−√q} ≤ 2 S_d e^{-√r}`, p+q ≥ r, S_d=Σ_{z∈Z^d}e^{-√|z|∞/2} (from √p+√q−√(p+q) ≥ ½√min(p,q)); no `log L`, no ℓ_u | S_3=3.687e5 (exact), S̄_3=2^d e^{1/2}Σ_j j^{2d}e^{-j/2}=1.216e6 ≥ S_3 |
| `lk` constant | `‖ELKLK‖ ≤ e(2S_d+1) P J² T_{u,D}` (main `2eS` P J² A e^{-√r}; cross `2eS` P J² W^{-D}; floor term `e` P J² W^{-D}·F, F=L^dW^{2d}x²/W^D ≤ 1) | c_lk(3)=2.004e6 (exact S_3), 6.61e6 (S̄_3); d=4: 2.96e9 |
| `lossE2` base | RBM2D shape `10^12 K₀²Λ⁶(1+log·)⁴(1+log W)³e^{8(log W)^{3/4}}` ≥ 10^12·5³=1.25e14 under K₀,Λ ≥ 1, log W ≥ 4 | 1.25e14/6.61e6 = 1.9e7 at d=3; fails for d ≥ 6 (c_lk 2.3e15): leading constant must carry d, e.g. `2^{3d+2}(2d)! ≥ S̄_d` (checked d=3..8, `consts2.py`) |
| floor (C3), d form | `L^d W^{2d} ≤ W^D` (RBM2D `L²W¹² ≤ W^{D/2}`); implies D > 2d, `W^{-D} ≤ A` (T ≤ 2A), and is implied by `W^D ≥ N²`, N=(WL)^d | instance: 2^69 ≤ 2^80 |
| `W ≥ e⁴` | log W ≥ 4 ⇒ (1+log W)³ ≥ 125, `e^{8(log W)^{3/4}} ≥ 1` | sz0 n=1: log 1024 = 6.93; sz0 n=0 (W=32, log=3.47) FAILS |
| 𝒦 bound | `‖K_σ(a,b)‖=W^{-d}‖Θ_{u m₁m₂}(a,b)‖ ≤ W^{-d}/x = Mu⁻¹` (Neumann, SB stochastic, |m|=1): K₀=1 is provable (`KLK_two`, `Loop/KLTree.lean:211`) | K₀=1 sharp at a=b, u=0 |
| (Kell*) | `‖K(a,b)‖ ≤ W^{-D}` for `zdistInf ≥ ℓ*/8` (`KellStarEv` δ=1/8, `Path/KellStar.lean:54`); needs RangeCond τ: `N^{-1+τ} ≤ lam² ≤ 1−t`, τ=min(2𝔡/d,½) from `lam ≥ W^{-d/2+𝔡}` | equality at τ=2𝔡/d |
| (e6) / (e9) | `|G_xy−δm| ≤ Λ Mu^{-1/4} ≤ Λ` (Mu ≥ 1) ⇒ `‖G‖ ≤ 2Λ`; `|avgErr| ≤ Λ Mu⁻¹` (factor (ℓ_u/ℓ_s)²=1) | instance 0 ≤ Λ |
| J* | `jStar = sup_{σ,a,b}‖LK‖/T + 1`; hypothesis `‖LK‖ ≤ Jst T` gives jStar ≤ 2Jst (factor 4 in `J²`, inside c_lk slack) | — |

Dropped from RBM2D's `E2Hyp`: `s`, `v` (ℓ_s=ℓ_u=1, `M_v≥1` replaced by Mu ≥ 1; conclusion is at u, `Step5Pins.lean:161-191`); `hJ` (`jStar ≤ W`) is destructured but never used in RBM2D (`grep -nw hJ` below: only `obtain` lines), so `lemDecCalE_lk` does not need it.

**Uses of `goodSet` in RBM2D `LemDecCalE.lean` (script `grep`) and the explicit d ≥ 3 premise replacing each:**
```
$ git -C ../RBM2D show c9a24cf:RBM2D/Path/LemDecCalE.lean > src2d; grep -nE "goodSet|hgood" src2d | grep -vE "obtain ⟨hL3|^[0-9]+:(/--|`|signs|refers|From)" | cut -c1-100
64:    M ∈ goodSet L W E s u Λ ∧ jStarMat L W E D u M ≤ W ∧
654:theorem LemDecCalE_e6_err (hM : M ∈ goodSet L W E s u Λ) (σ : Bool) (p q : BlockIndex L W) :
691:    (hM : M ∈ goodSet L W E s u Λ) (σ : Bool) (p q : BlockIndex L W) :
715:  exact LemDecCalE_e6 hE.le hΛ (hMv.trans h2.2.1) hgood σ p q
743:  have hgex := hgood.2.2.2.1 p q hpq
798:  have hgex := hgood.2.2.2.1 p q hpq
830:theorem LemDecCalE_e9 (hM : M ∈ goodSet L W E s u Λ) (σ : Bool) (a : Z2 L) :
1137:private theorem zero_mem_goodSet {E : ℝ} (hE : |E| < 2) :
$ grep -nE "obtain ⟨hH, -|hgood\.2" src2d | cut -c1-90
657:  obtain ⟨hH, -, hll, -⟩ := hM          
743:  have hgex := hgood.2.2.2.1 p q hpq     (e7: clause 4, GijGEX)
798:  have hgex := hgood.2.2.2.1 p q hpq     (e8: clause 4)
832:  obtain ⟨hH, -, -, -, -, hav⟩ := hM    (e9: clauses 1, 6 (avgErr))
$ grep -nw hJ src2d | cut -c1-8            -> 129 138 271 316 330 379 714 730 793, each "  obtain ⟨hL3, ..." (hJ is bound, never used)
```
Clauses 2 (`loopAbs`, k=3,4,6) and 5 (`GiiGEX`) are never projected: not needed here. Replacement premises (all on the fine matrix `M`, spectral `zt E u`):
(P-H) `M.IsHermitian` (clause 1); (P-e6) `∀ x y, ‖G_xy − δ_xy m‖ ≤ Λ Mu^{-1/4}` (clause 3); (P-e7/8) `∀ p ≠ q, ‖G_pq‖² ≤ Λ gexRHS(blk q, blk p)` (clause 4, swapped pair as `GijGEXPTSwap`, `Green/Pins.lean:283`); (P-e9) `∀ σ a, ‖avgErr σ a‖ ≤ Λ Mu⁻¹` (clause 6 with (ℓ_u/ℓ_s)²=1).
Also premises: `3 ≤ d`, `3 ≤ L`, `|E|<2`, `0 ≤ u < 1`, `0 < lam`, `lam² ≤ 1−u`, `1 ≤ lam²W^d`, `4 ≤ log W`, `1 ≤ Λ`, `1 ≤ K₀`, floor, K bound, (Kell*), and `‖LK_σ(a,b)‖ ≤ Jst·T_{u,D}(|a−b|)` for the J* of the conclusion.

**d = 2 tokens of the source (`grep -c`, lines) → d ≥ 3:** `Z2` 57 → `Zd d L`; `zdist2` 91 → `zdistInf d L` (ℓ∞; ≤1 ball 5 → 3^d); `scaleM` 61 / `etaT` 8 / `ellT` 36 → `W^d(1−u)` (no Im m, ℓ=1); `ellStar` 12 → `(log W)^{3/2}`; `25` (33 lines containing it) → 9^d / 2·9^d where it is the pair count, `2500` (conv.) → 2S_d; `Idx L W`, `BlockIndex` (28, 25) → `Idx d L W`, `STblk` (fine-lattice entries, `Green/Pins.lean` R2); `tailT L W E D u ℓ` 51 → `tailTD d W u D r` (`Defs/Tail.lean:173`); `W²` → `W^d`; `L²W¹²≤W^{D/2}` → floor above.

**Premise → `STIngR5` source (S5-09 obligations; `STIngR5` = `Step5Pins.lean:82-92`, `R = STReg5III` `:58`, hypothesis `Prec STLK2 ≤ Jst·T` `:164-166`):**
| premise | source (file:line) | status |
|---|---|---|
| 3 ≤ L; Hermitian | `Sizes.three_le_L` `Defs/Sizes.lean:145`; `seqHflow_isHermitian` `Gauss/FineModel.lean:531` | ok |
| \|E\|<2; 0 ≤ u < 1 | `STFlow`/`locDomain` + `abs_lemE_le` `Defs/Semicircle.lean:309`; `TimeIcc`, `lemT_lt_one` `:209` | ok |
| lam>0; lam² ≤ 1−u | `STReg5III` `Step5Pins.lean:58` (u ≤ t); `WO` `Defs/Sizes.lean:164` | ok |
| 1 ≤ lam²W^d; log W ≥ 4 | `lam_sq_mul_pow_ge` `Defs/Sizes.lean:193`; `Admissible` `:177` (eventually) | ok |
| (P-e6) | `STLocalEntryU` `Step34Pins.lean:199` (in `STStep2Concl` `:221`), `Bctl ≤ (1+L^{-d})/(W^d x)` (`Defs/Sizes.lean:214`) | ok (Λ=√2·N^ε) |
| (P-e9) | `STAvgU` `Step34Pins.lean:192` / `STLKU` k=1 `:184` | ok |
| K bound (K₀) | Neumann + `KLK_two` (K₀=1), or `STKbound` `Induction/Defs.lean:174` | ok |
| (Kell*) | `kellStarEv` `Path/KellStar.lean:173` + RangeCond (derived: row (Kell*)) | ok |
| `‖LK‖ ≤ Jst T` | hypothesis of the conclusion, `Step5Pins.lean:164-166` | ok |
| **floor** `L^dW^{2d} ≤ W^D` | only `∀ᶠ n, size n ≤ W^D` (`Step5Pins.lean:163`), i.e. `W^D ≥ L^dW^d` | **missing** (needs `W^D ≥ N²`) |
| **(P-e7/8)** Gij clause | `GijGEXPTSwap` `Green/Pins.lean:283` / `STGijGEX` `Induction/Defs.lean:210` are not among the hypotheses of `STIngR5` | **missing** |
| **jStar ≤ W** (unused by lk) | `Jst` is an arbitrary function ≥ 1 (`Step5Pins.lean:162`) | **missing** (S5-06..08 decide) |
| STKward, STLmaxU, STStep1Loop | not needed by the premises above | unused here |

### (ii) One concrete nondegenerate instance (and the floor mismatch)

`d=3, L=8, W=1024, lam=1/4096` (= `sz0` n=1, `Defs/Sizes.lean:260-265`), `E=1/2, u=0, D=8, Λ=K₀=1, M=0, 𝔡=1/10`. At M=0, u=0: G=m·I (`z_0=E+m`, m(m+E)=−1), so llErr=0, avgErr=0, off-diagonal G=0, LK=0 (J*=1), K=W^{-d}δ_ab. No N=0, no empty index; u=0 is the boundary of the allowed range and is forced (M=0 is the matrix of time 0 only).
```
$ python3 T2164/instance.py
instance: d=3 L=8 W=1024 N=549755813888=2^39 lam=1/4096 E=0.5 u=0 D=8 Lam=1 K0=1 M=0
Mu=W^d(1-u)=2^30  A=Mu^-2=2^-60  W^D=2^80  L^dW^2d=2^69
premises checked: 17, true: 17; failing: []
  checked: 3<=d; 3<=L; |E|<2; 0<=u<1; 0<lam; lam^2<=1-u; 1<=lam^2 W^d; W>=e^4 (log W>=4); 1<=Mu; floor L^d W^2d <= W^D; N<=W^D (STLemDecCalEConcl hyp); W^-D<=A (T<=2A); |m|=1, m(m+E)=-1; K0=1: W^-d Theta_u(a,b)<=Mu^-1 at a=b,u=0; WO: W^(-d/2+dd)<=lam<=1/dd (dd=0.1); RangeCond tau=2dd/d at 1-t=lam^2: N^(-1+tau)<=lam^2; lk bound constant: c_lk=e(2S_3+1)=2.004e6 <= lossE2 floor 1.25e14
sz0 n=0: W= 32  log W=3.4657 <4 -> premise W>=e^4 fails at n=0
  n=    1 L=8 W=1024: floor True  lam^2W^d>=1 True  logW>=4 True  N<=W^8 True
  n=  100 L=404 W=336323216032: floor True  lam^2W^d>=1 True  logW>=4 True  N<=W^8 True
  n= 1000 L=4004 W=32160320320160032: floor True  lam^2W^d>=1 True  logW>=4 True  N<=W^8 True
  sz0 n=1 D=4: N<=W^D True  floor False   N^2<=W^D False
  sz0 n=1 D=7: N<=W^D True  floor True   N^2<=W^D False
```
(n=2,3,10 also True in the full output.) Limit computation for the asymptotic premises along `sz0`: with D=8, `L^dW^{2d} = 64(n+1)³(2(n+1))^{30} = 8(2(n+1))^{33} ≤ (2(n+1))^{40} = W^8` for every n ≥ 0; `lam²W^d = (2(n+1))^{3}` ≥ 1; `log W = 5 log(2(n+1)) ≥ 4` iff n ≥ 1; RangeCond: `N^{-1+τ}` = 2^{-36.4} ≤ lam² = 2^{-24} at n=1.

Supporting checks (the inequalities of the `lk` chain and the counts):
```
$ python3 T2164/checks.py
  L=3: zdistInf<=1: 27,27 (3^d=27, pairs 729=9^d=729)   zdistD<=1: 7 (1+2d=7, pairs 49)     [same for L=4,5,8]
conv lemma Z_21^3: max_b sum_x e^(-sqrt|x-0|-sqrt|x-b|) e^(sqrt|b|) = 1035.5572  <= 2*S_3=7.3731e+05
SB row sums: 0.9999999999999999 1.0  support within zdistInf<=1: True
  u=0.99: max Theta_u=7.5375 <= 1/(1-u)=100.0000 ; Theta_0=I: True
e^{-sqrt(max(r-1,0))} <= e * e^{-sqrt r} for r=0..1999: True
sqrt x+sqrt y-sqrt(x+y) >= (1/2) sqrt(min(x,y)), x,y<60: True
$ python3 T2164/consts.py     d=3: S_d=3.686561e+05  c_lk=e(2S_d+1)=2.004225e+06  9^d=729  2*9^d=1458
$ python3 T2164/lkchain2.py   (saturated |lk|=J·T on Z_5^3, W=55; ratio ELKLK/(P J² T) ≈ F+39, F=L^dW^{2d}x²/W^D)
L=5 W=55 D=8 u=0.0: N<=W^D:True floor:True  F=4.132e-02 max ratio=3.9008e+01
L=5 W=55 D=5 u=0.0: N<=W^D:True floor:False F=6.875e+03 max ratio=6.9134e+03
```
The last two lines show the floor is necessary for the chain: with only `W^D ≥ N` (D=5: 5.0e8 ≥ N=2.1e7) the saturated bound has ratio 6.9e3 and grows with L like F; with the floor, ratio 39 ≪ c_lk. (Saturation is a statement about the pointwise hypothesis `‖LK‖ ≤ J T`, not about an actual `M`.)

### Verdicts
- Target 1 (`lossE2`, `E2Hyp` with explicit premises): **PASS** (premise list above; every premise holds at the instance; d-dependence of the leading constant of `lossE2` required for d ≥ 6, fine at d = 3).
- Target 2 ((e1)–(e10) at d ≥ 3): **PASS** (counts 3^d/9^d, constants 9^d and 2·9^d).
- Target 3 (`lemDecCalE_lk`): **PASS** with the floor `L^dW^{2d} ≤ W^D` as a premise; constant `e(2S_d+1)` ≤ `lossE2`.
- Flags for the dispatcher (do not block S5-05; they decide S5-09): (M1) floor not implied by `STLemDecCalEConcl`'s `size ≤ W^D`; needs `size² ≤ W^D` (harmless downstream since `T_{u,D}` decreases in D) — paper-delta candidate T2164a (the paper's "W^D ≥ N" at `3_5:2314` is too weak for `res_deccalE_lk`). (M2) the Gij clause is not an `STIngR5` hypothesis (`GijGEXPTSwap` needs the `lem_GbEXP` route). (M3) `jStar ≤ W` has no source. Candidates: T2164b (portmap `(1+2d)²=49` vs merged `zdistInf` count 3^{2d}=729), T2164c (`Mu=W^d(1−u)` without Im m; `s`, `v` dropped).

## (b) Script output — Sun Oct  4 22:23:22 UTC 2026

```
$ lake build RBM3D.Path.LemDecCalE 2>&1 | tail -1
Build completed successfully (3780 jobs).
$ lake build RBM3D.Path.LemDecCalE 2>&1 | grep -c "LemDecCalE.lean:.*\(warning\|error\)"
0
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Path/LemDecCalE.lean ; wc -l RBM3D/Path/LemDecCalE.lean
0
    1477
$ git diff --stat main...t/T2164 ; git log -1 --format=%h
 RBM3D/Path/LemDecCalE.lean | 1477 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1477 insertions(+)
53bfb7b
$ #print axioms of every non-private declaration (31), grouped by axiom list
31 decls with axioms [propext, Classical.choice, Quot.sound]: lossE2 E2Hyp LemDecCalE_lk LemDecCalE_e10a_nat LemDecCalE_e10a LemDecCalE_e10b LemDecCalE_sum_zd_le LemDecCalE_exp_conv LemDecCalE_sum_tail_tail LemDecCalE_e1 LemDecCalE_e1_rpow LemDecCalE_tailT_anti LemDecCalE_tailT_shift LemDecCalE_e4c LemDecCalE_tailT_mono_scale LemDecCalE_e2 LemDecCalE_floor LemDecCalE_floor_A LemDecCalE_tailT_le_two_inv_sq LemDecCalE_lk_const_le_lossE2 lemDecCalE_lk LemDecCalE_lk_le LemDecCalE_loopPM_eq LemDecCalE_loopPM_le LemDecCalE_e6_err LemDecCalE_e6 LemDecCalE_e7 LemDecCalE_e8 LemDecCalE_e9 LemDecCalE_e2Hyp_zero LemDecCalE_inst

$ awk (extract) lossE2, E2Hyp, LemDecCalE_lk, lemDecCalE_lk from RBM3D/Path/LemDecCalE.lean
def lossE2 (d L W : ℕ) (Λ K₀ : ℝ) : ℝ :=
  10 ^ 12 * (1600 * (d : ℝ) ^ 4) ^ d * K₀ ^ 2 * Λ ^ 6 *
    (1 + Real.log ((L : ℝ) ^ d * (W : ℝ) ^ (2 * d))) ^ 4 *
    (1 + Real.log W) ^ 3 * Real.exp (8 * Real.log W ^ ((3 : ℝ) / 4))
def E2Hyp {d : ℕ} (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  3 ≤ d ∧ |E| < 2 ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧
    1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
    ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (2 * d) ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    M.IsHermitian ∧
    (∀ x y : Idx d (sz.L n) (sz.W n),
      ‖Gres M (zt E u) true x y - (if x = y then mE E else 0)‖ ≤
        Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ ((1 : ℝ) / 4)) ∧
    (∀ p q : Idx d (sz.L n) (sz.W n), p ≠ q →
      ‖Gres M (zt E u) true p q‖ ^ 2 ≤
        Λ * gexRHS d (sz.L n) (sz.W n) E u M (STblk sz n q) (STblk sz n p)) ∧
    (∀ (σ : Bool) (a : Zd d (sz.L n)),
      ‖avgErr d (sz.L n) (sz.W n) E u M σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
    1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STLKM sz n E u M σ a‖ ≤ J * STtailTD sz n u D a) ∧
    (∀ a b : Zd d (sz.L n),
      ‖STKloop sz n E u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
    (∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
          (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖STKloop sz n E u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
def LemDecCalE_lk (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D Λ K₀ J : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    E2Hyp sz n E u D Λ K₀ J M → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖STELKLKM sz n E u M σ a‖ ≤ lossE2 d (sz.L n) (sz.W n) Λ K₀ *
        ((1 - u)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2) * STtailTD sz n u D a
786:theorem lemDecCalE_lk (d : ℕ) : LemDecCalE_lk d := by
$ awk (extract) the compiled instance and its application
theorem LemDecCalE_inst :
    E2Hyp sz0 1 (1 / 2) 0 8 1 1 1
      (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ) := by
example :
    ‖STELKLKM sz0 1 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 1) (sz0.W 1)) (Idx 3 (sz0.L 1) (sz0.W 1)) ℂ)
        ![true, false] ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1]‖ ≤
      lossE2 3 (sz0.L 1) (sz0.W 1) 1 1 *
        ((1 - (0 : ℝ))⁻¹ * (((sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ * (1 : ℝ) ^ 2) *
          STtailTD sz0 1 0 8 ![(0 : Zd 3 (sz0.L 1)), Pi.single 0 1] :=
  lemDecCalE_lk 3 sz0 1 (1 / 2) 0 8 1 1 1 0 LemDecCalE_inst _ _

$ name-clash: declarations of the 31 new public names on main (git grep -nE "(def|theorem|...) NAME", 0 expected)
declaration hits: 0
$ git grep -nw -e lossE2 -e E2Hyp -e LemDecCalE_lk -e lemDecCalE_lk main -- RBM3D RBM3D.lean   (mentions, not declarations)
main:RBM3D/Induction/Step5Pins.lean:160:(`Path/LemDecCalE*.lean`, `lossE2`, `E2Hyp`), the 
$ git -C ../RBM2D log -1 --format=%h ; diff --stat c9a24cf HEAD -- RBM2D/Path/LemDecCalE.lean   (port source = c9a24cf)
9e0f275
 1 file changed, 35 insertions(+), 452 deletions(-)
$ source declaration lines at c9a24cf (name:line)
lossE2:53 E2Hyp:61 LemDecCalE_lk:72 LemDecCalE_e1:85 LemDecCalE_e2:127 LemDecCalE_floor:135 LemDecCalE_tailT_anti:183 LemDecCalE_tailT_shift:200 LemDecCalE_e4c:235 LemDecCalE_tailT_mono_scale:242 LemDecCalE_tailT_le_two_inv_sq:267 LemDecCalE_loopPM_le:310 LemDecCalE_six_thousand_le_lossE2:328 lemDecCalE_lk:375 LemDecCalE_e10a:505 LemDecCalE_e10b:547 gexRHS_le_near:589 LemDecCalE_e6_err:654 LemDecCalE_e6:690 LemDecCalE_e7:724 LemDecCalE_e8:784 LemDecCalE_e9:830 LemDecCalE_e2HypWitness:1190 
$ python3 consts_b.py   (S_d bound proved, lk constant, lossE2 lower bound under K0,Lam>=1, log W>=4)
d=3: S_d<=1.926e+15  e(2S_d+1)=1.047e+16  lossE2_min=2.721e+29  ok=True  9^d=729 3^d=27
d=4: S_d<=2.391e+22  e(2S_d+1)=1.300e+23  lossE2_min=3.518e+36  ok=True  9^d=6561 3^d=81
d=8: S_d<=2.455e+54  e(2S_d+1)=1.335e+55  lossE2_min=4.254e+68  ok=True  9^d=43046721 3^d=6561

$ registry pre-check (DECISIONS §20): scratch file = import RBM3D; import RBM3D.Path.LemDecCalE; #assert_rbm_axioms; lake env lean <file>; echo exit=$?
exit=0
axiom audit: 4851 theorems, 1714 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 83 (borrowed 0, owed 64, structural 19).
$ grep -c "E2Hyp" precheck.out  (E2Hyp is not scanned as an unregistered premise)
0
$ lake build 2>&1 | tail -1   (worktree, whole library without the root import, which the hub adds at merge)
Build completed successfully (3931 jobs).

$ premise -> source: file:line of each cited declaration (grep -n -m1)
STIngR5 (hyps, 3 <= d)             RBM3D/Induction/Step5Pins.lean:82
STReg5III (lam^2 <= 1-t)           RBM3D/Induction/Step5Pins.lean:58
Jst>=1, size<=W^D, Prec LK<=J*T    RBM3D/Induction/Step5Pins.lean:162
STFlow (|E|<2, Admissible)         RBM3D/Induction/Defs.lean:286
STKbound                           RBM3D/Induction/Defs.lean:174
STLocalEntryU (P-e6)               RBM3D/Induction/Step34Pins.lean:199
STAvgU (P-e9)                      RBM3D/Induction/Step34Pins.lean:192
STLKU                              RBM3D/Induction/Step34Pins.lean:184
Sizes.WO                           RBM3D/Defs/Sizes.lean:164
Sizes.lam_sq_mul_pow_ge            RBM3D/Defs/Sizes.lean:193
Sizes.Admissible                   RBM3D/Defs/Sizes.lean:177
Sizes.Bctl                         RBM3D/Defs/Sizes.lean:214
seqHflow_isHermitian               RBM3D/Gauss/FineModel.lean:531
abs_lemE_le (|E| <= |z.re|)        RBM3D/Defs/Semicircle.lean:309
lemT_lt_one                        RBM3D/Defs/Semicircle.lean:209
kellStarEv                         RBM3D/Path/KellStar.lean:173
KellStarEv (needs RangeCond)       RBM3D/Path/KellStar.lean:54
Sizes.RangeCond                    RBM3D/Green/Pins.lean:55
GijGEXPTSwap (not an STIngR5 hyp)  RBM3D/Green/Pins.lean:283
KLK_two                            RBM3D/Loop/KLTree.lean:211
private kellStar_bparam_le         RBM3D/Path/KellStar.lean:68
$ STIngR5 hypotheses list contains GijGEX / STGijGEX ? (grep -c, 0 expected)
0
```

Premise of `E2Hyp` (20 conjuncts, in order) -> `STIngR5` source (S5-09 obligation; `STIngR5` = `Step5Pins.lean:82`):
| conjunct | source (lines in the output above) | status |
|---|---|---|
| `3 ≤ d`; `\|E\|<2`; `0 ≤ u < 1` | hyp `3 ≤ d` of `STIngR5`; `STFlow` (`locDomain`: `|z.re| ≤ 2-κ`) with `abs_lemE_le`; `s ≥ 0`, `t ≤ lemT`, `lemT_lt_one` | ok |
| `0 < lam`, `lam² ≤ 1-u`, `1 ≤ lam²W^d`, `4 ≤ log W` | `STReg5III` (`lam² ≤ 1-t`); `WO`, `lam_sq_mul_pow_ge`, `Admissible` (eventually) | ok |
| `1 ≤ Λ`, `1 ≤ K₀` | constants chosen by S5-09 | ok |
| floor `L^d W^{2d} ≤ W^D` | only `size ≤ W^D` (`Step5Pins.lean:163`), `size = (WL)^d` | **missing** (M1) |
| Hermitian | `seqHflow_isHermitian` | ok |
| (P-e6) | `STLocalEntryU` (in `STStep2Concl`), `Bctl ≤ 2 M_u⁻¹` (`Bparam ≤ 2(1-u)⁻¹`, `kellStar_bparam_le`) | ok |
| (P-e7/8) Gij clause | `GijGEXPTSwap` is not an `STIngR5` hypothesis (grep count 0) | **missing** (M2) |
| (P-e9) | `STAvgU` (`STLKU` at `k = 1`) | ok |
| `1 ≤ J`; `‖STLKM‖ ≤ J T` | `Jst ≥ 1` and `Prec STLK2 ≤ Jst·STtailTD` (`Step5Pins.lean:162-166`) | ok |
| `J ≤ W` | none (`Jst` arbitrary); not used by any proof here (`hJW` is only destructured) | **missing** (M3) |
| `𝒦` bound | `STKbound` at `k = 2`, or `KLK_two` (`K₀ = 1`) | ok |
| (`Kell*`) | `kellStarEv` (needs `RangeCond`, not an `STIngR5` hyp: derived from `WO` per (a)) | ok per (a), not re-verified |

Narrative.
- File `RBM3D/Path/LemDecCalE.lean`, 31 non-private declarations, standard axioms only, no warning from the file; one commit `53bfb7b`; `Test/Axioms.lean` untouched.
- `E2Hyp sz n E u D Λ K₀ J M` is stated for the model `sz : Sizes d` at size index `n` (the form of `STELKLKM`, `STLKM`, `STtailTD`); the class-(c) `goodSet` of RBM2D is replaced by conjuncts (Hermitian, (P-e6), (P-e7/8), (P-e9)); RBM2D's `s`, `v` are dropped (conclusion at the single time `u`); `jStarMat` is a real `J` with the pointwise bound `‖STLKM σ a‖ ≤ J T_{u,D}`.
- d-dependent counts (target 1): the cube `{|z|_∞ ≤ 1}` of `Z_L^d` has `≤ 3^d` points (`LemDecCalE_e10b`), so `gexRHS` has `9^d` pairs (RBM2D: `5·5 = 25`): (e7) `9^d Λ`, (e8) `2·9^d Λ K₀`.
- `lemDecCalE_lk`: `S1` norm and `norm_sum_le`; `SB x y ≠ 0 ⇒ |x-y|_∞ ≤ 1` (`sbKernel`, `zdistInf ≤ zdistD`) and `Σ_y ‖SB x y‖ = 1` (`sum_norm_SB_row`); the shift (e4) with `c = 1` gives `e`; `LemDecCalE_sum_tail_tail`: `Σ_x T(|x-a₂|) T(|a₁-x|) ≤ (2S_d+1) M_u⁻² T(|a₁-a₂|)` with `S_d = (1+1536 d⁴)^d` (product bound `e^{-½√max} ≤ Π e^{-(2d)⁻¹√·}`, one-dimensional sum `≤ 1 + 96/γ⁴` from `e^y ≥ y⁴/24`, `Σ j⁻² ≤ 2`, uniform in `L`) and the floor `W^{-D} L^d ≤ M_u⁻²`; (e1) turns `W^d M_u⁻²` into `(1-u)⁻¹ M_u⁻¹`; `e(2S_d+1) ≤ lossE2` (`LemDecCalE_lk_const_le_lossE2`).
- Deviation from (a): (a) used the exact `S_3 = 3.687e5` and kept RBM2D's base `10^12`; the bound proved here is `S_3 ≤ 1.9e15` (`consts_b.py`), so `lossE2` has the extra leading factor `(1600 d⁴)^d` (it also dominates `9^d`, `2·9^d`); (a)'s floor, `9^d`, instance data and flags M1-M3 are used as written, no (a′) needed.
- Instance: `LemDecCalE_inst` is `E2Hyp` at `d = 3`, `sz0` at `n = 1` (`L = 8`, `W = 1024`, `lam = 1/4096`), `E = 1/2`, `u = 0`, `D = 8`, `Λ = K₀ = J = 1`, `M = 0`, via the reusable `LemDecCalE_e2Hyp_zero` (every conjunct; `G = m I`, `𝓛 = 𝒦 = W^{-d} m₁m₂ δ_{a₁a₂}` at time `0`, `lemDecCalE_STLKM_zero_time`); `u = 0` because `M = 0` is the matrix of time `0` (per (a)). The `example` applies `lemDecCalE_lk`; its left side is `0`, the second `example` proves the right side `> 0`.
- Changed against RBM2D: (e5) first part is the projection `LemDecCalE_lk_le`; (e9) is the projection of (P-e9); (e6) is stated for the fine entries `Gres M (zt E u) σ x y` (σ = − via `G(−) = G(+)ᴴ`); `six_thousand_le_lossE2` is `LemDecCalE_lk_const_le_lossE2`; `convTailT` is replaced by `LemDecCalE_sum_tail_tail`; (e3) is split into `floor`, `floor_A`, `tailT_le_two_inv_sq`, `tailT_mono_scale`.

## (c) Verified Mathlib names (`#check` in `names_c.lean`, this session)
- present: `Real.pow_div_factorial_le_exp`; `sum_Ioo_inv_sq_le` (root namespace, needs `import Mathlib.Analysis.PSeries`); `Finset.prod_univ_sum`; `Fintype.piFinset_univ`; `Fintype.card_piFinset`; `Finset.sum_range_reflect`; `Finset.sum_Ico_add'`; `ZMod.val_cast_of_lt`; `Int.card_Icc`; `Nat.floor_le`; `Matrix.conjTranspose_nonsing_inv`; `Real.rpow_lt_rpow_left_iff`; `Real.exp_one_lt_d9`; `Finset.prod_le_prod` (one argument `∀ i ∈ s, f i ≤ g i` in this Mathlib; `Finset.prod_le_prod'` is deprecated).
- absent: `Finset.sum_Ioo_inv_sq_le`; `ST_Gres_false` (exists in `Induction/Step2Iterate.lean:1198` but is not in the import closure of `Step5Pins`; its text is copied as the private `lemDecCalE_Gres_false`).

## (d) Open issues and paper-delta candidates
- (M1) floor: `E2Hyp` needs `L^d W^{2d} = size·W^d ≤ W^D`; `STLemDecCalEConcl` supplies only `size ≤ W^D`; `size² ≤ W^D` suffices. The paper says "large enough `D` (such that `W^D ≥ N`)" (`3_5:2317`). The dispatcher decides before S5-09.
- (M2) the Gij premise (P-e7/8) has no source among the `STIngR5` hypotheses; (M3) `J ≤ W` has no source and is unused (a primed `E2Hyp'` without it can be added when S5-06..08 do not need it).
- `lemDecCalE_lk` is deterministic at one time `u`; S5-09 must turn the premises into a high-probability event uniform in `u ∈ [s,t]`.
- T2164a: paper `W^D ≥ N` (`3_5:2317`) is too weak for `res_deccalE_lk` as proved here; the floor `L^d W^{2d} ≤ W^D` is used (see (a), `lkchain2.py`).
- T2164b: the neighbour pairs of `gexRHS` (`zdistInf ≤ 1`) number `9^d = 729` at `d = 3`, not the portmap's `(1+2d)² = 49` (`T2134-portmap.md:405`).
- T2164c: `M_u = W^d(1-u)` (no `Im m`, `ℓ_u = 1`); the tail is `tailTD` (amplitude `M_u⁻²`); `E2Hyp` has no `s`, `v`.
- T2164d: `lossE2` has the leading constant `10^12 (1600 d⁴)^d` and `log(L^d W^{2d})`; the convolution constant is `S_d = (1+1536 d⁴)^d` (not optimal).
