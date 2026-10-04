Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 11:57:34 UTC 2026

### (i) Exponent table
Notation: `d=3`, `N=(WL)^d`, `g=lam n`, `ℓ_u=ellT L g u`, `R=diam_∞ a`, `K=zdistInf(c₀−c₁)`, `η_u=(1−u)Im m(E)`; `Admissible 𝔠 𝔡` = `W≥N^𝔠`, `W^{-d/2+𝔡}≤g≤𝔡⁻¹`, `N→∞`. Route of target 1 (`k≥2`; `k≤1`: `diam_∞=0<ℓ_uW^{τ'}` since `ℓ_u≥1`, vacuous, no `NeZero k` needed with the ℕ-valued `sup` definition):
(1) adjacent pair: `R ≤ (k−1)·max_{m<k−1}|a_m−a_{m+1}|_∞` (triangle inequality for `zdistInf` along the chain); (2) rotate so the pair is (first,last), cut as `A=` one `G`, `B=` `(k−1)` `G`'s: `|𝓛_{σ,a}|² ≤ |𝓛^{(2)}_{(s,¬s),(b',b)}|·|symB|` (`norm_sq_gloop_le_symIdx`), `|symB| ≤ η_u^{-2(k−1)}(W^{-d})^{2k−3} ≤ η_u^{-2(k−1)}` (`norm_gloop_le_of_le_abs_im`; `H=seqHflow` Hermitian, `|Im z_u|=η_u`); (3) `|𝓛^{(2)}_c| ≤ ‖𝒦^{(2)}_c‖+‖(𝓛−𝒦)^{(2)}_c‖`, first term by `STKcalDecay` at length 2, second by the decay input on the event `‖(𝓛−𝒦)_c‖ ≤ N·ζ_c` (`τ₁=1`); (4) `‖𝓛−𝒦‖≤‖𝓛‖+‖𝒦‖`, `‖𝒦_{σ,a}‖≤W^{-(D'+1)}` by `STKcalDecay` at length `k`; (5) pointwise implication `N^ε W^{-D'}<ξ ⟹ N^{1}ζ_c<ξ_c` into `perTimeCalc_of_imp`. No entry bound of `G` and no `GbEXP` hypothesis enter.

| # | Quantity | Value / supplier | Constraint | Slack |
|---|---|---|---|---|
| 1 | `Q` of `STKcalDecay` | `Q=d/2=3/2`; `W^{-d/2}≤W^{-d/2+𝔡}≤g` from `WO` (compiled: `inst_stKcalDecay_admissible`, merged `KDecay.lean:976`, applies both calls below from `Admissible` alone) | `W^{-Q}≤g` | `sz0`: `W^{-3/2}` vs `g=W^{-6/5}` |
| 2 | `gmax` | `𝔡⁻¹=10` (`WO`) | `0<g≤gmax` | `sz0`: `g≤1.6e-2` |
| 3 | adjacent-pair loss | `K ≥ R/(k−1) ≥ ℓ_uW^{τ'}/(k−1) ≥ ℓ_uW^{τ'/2}` | `W^{τ'/2} ≥ k−1` eventually | `sz0, k=3, τ'=1/10`: holds for `n≥7` (script) |
| 4 | `l¹` vs `l^∞` | `KLmaxDist ≥ zdistD(c₀−c₁) ≥ K` and `KLmaxDist a ≥ diam_∞ a` (`zdistInf≤zdistD`, merged `Defs/Sizes.lean`); premises of `STKcalDecay` at length 2 (`τ'/2`) and `k` (`τ'`) | `ℓ_uW^{τ} ≤ KLmaxDist` | as row 3 |
| 5 | `1−u` lower bound (not a hypothesis; from the far premise) | `zdist L x ≤ L/2` ⟹ `R ≤ L/2` ⟹ `ℓ_u ≤ L/(2W^{τ'}) < L` ⟹ `g/√(1−u)<L` ⟹ `1−u > g²/L² ≥ W^{-d}L^{-2} ≥ N⁻¹` (`g²≥W^{-d}`, `L^{d-2}≥1`) | `W^{τ'}>1/2`, `d≥2` | `sz0`: `1−u=1/2` vs `g²/L²=1.5e-5` (n=0) |
| 6 | `η_u⁻¹` | `Im m(E) ≥ √κ/2` (merged `ST_mE_im_ge`, `Step2Events.lean:555`), so `η_u⁻¹ ≤ (2/√κ)(1−u)⁻¹ ≤ (2/√κ)N` | row 5 | `sz0`, `E=0`, `u=1/2`: `η⁻¹=2` vs `2N` |
| 7 | `STWB` in the far regime | `STWB(u,K) ≤ Bctl ≤ W^{-d}g⁻²+N⁻¹(1−u)⁻¹ ≤ W^{-2𝔡}+L^{2−d} ≤ 2` (`lam_sq_mul_pow_ge`, row 5) | none | `Bctl(t₀)=0.17` at `n=0` (table below) |
| 8 | exp factor | `exp(−√(K/ℓ_u)) ≤ exp(−W^{τ'/2}/√(k−1)) ≤ W^{-Q*}` | `W^{τ'/2}/√(k−1) ≥ Q* ln W` eventually | `sz0, τ'=1/10`: from `ln n≥35.8` (`ln W=182.5`) |
| 9 | total exponent `Q*` (`= Q₁ = D₁`: decay input at `D=Q*`, `STKcalDecay` length 2 at `D=Q*`) | `Q* = 2D'+3+(2(k−1)+1+C₀)/𝔠`; chain `|𝓛|² ≤ (C_κN)^{2(k−1)}[W^{-Q*}+2N^{1+C₀}e^{-…}+NW^{-D₁}]`, `N≤W^{1/𝔠}`, `C_κ=2/√κ`; need `|𝓛|² ≤ W^{-2D'-2}` (then `2‖𝓛‖+‖𝒦‖ ≤ 3W^{-D'-1} ≤ W^{-D'}`, `W≥3`) | `Q* ≥ 2D'+2+(2(k−1)+1+C₀)/𝔠` | extra `+1` absorbs `4C_κ^{2(k−1)}` eventually; `sz0, D'=1,k=3,𝔠=1/6,C₀=0`: `Q*=35` |
| 10 | prefactor, target 2 | `P_u=((1−s)/(1−u))^{Cd}Bctl(u)^{1/5}`; `lemma28_quant`: `1/16≤lemT z`, `|lemE z|≤2−κ`; `(1−t₀)Im m=√t₀ Im z` (`zt_im_lemma28`, `zt_im`), `√t₀≥1/4`, `Im m≤1`, `Im z≥N^{-1+ε}` ⟹ `1−u ≥ 1−t₀ ≥ N^{-1+ε}/4` for `u≤t≤lemT z` | `Cd≥0` | ratio `≤4N^{1−ε}` |
| 11 | `Bctl(u)` | `≤ W^{-2𝔡}+N⁻¹(1−u)⁻¹ ≤ W^{-2𝔡}+4N^{-ε} ≤ 1` eventually | `ε>0` | `sz0` table below |
| 12 | `C₀` of target 2 | `P_u ≤ (4N^{1−ε})^{Cd}·1 ≤ N^{Cd}` eventually (`4^{Cd}≤N^{εCd}`): `C₀=Cd` | `N→∞` | `sz0,n=0,Cd=4`: `P=1.0e20` vs `N^{Cd}=1.9e25` |
| 13 | lower bound `1 ≤ P` of the pin | FALSE for `P_u` at `u=s` (`Bctl^{1/5}<1`); repair without changing the pin: apply target 1 with `P'=max(P_u,1)` (`1≤P'≤N^{max(Cd,0)}`), the decay input for `P_u` implies that for `P'` pointwise (`STWB·exp≥0`, `perTimeCalc_of_imp`). The proof of 1 never uses `P≥1` (only `P≤N^{C₀}`), so `0≤P` would also do | `STWB·exp≥0` | none |

DECISIONS §29: (1) pin has `0≤u<1`; target 2 has `0≤s≤u≤t≤lemT z<1` (`lemT_lt_one`). (2) no case-(ii) boundary (`1−ilambda²/L²`) used; the paper places the claim in the case-(i) subsection but its hypotheses are only `(Gt_bound_flow)`, `(Eq:Gdecay_w)` (`3_5:1126`). (3) `L^d≤W^K` not used, only `L^d≤N`, `N≤W^{1/𝔠}`. (4) every inequality is `∀ᶠ n` (after `SizeTendsto`), none `∀ n`; `∀ᶠ N` of `STKcalDecay` pulled back by `inst_stKcalDecay_admissible`. §36: `3≤d` is needed by `stKcalDecay_holds`; consumers (`STMainInd`, `STStep3R`, `STStep4R`) begin `3≤d →`.

### (ii) Concrete instance (`d=3`)
Target 1 on merged `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `Admissible (1/6)(1/10)` = `sz0_admissible`), `κ=1`, `E≡0`, `u≡1/2` (`ℓ_u=1`), `P≡1`, `C₀=0`, `k=3`, `τ'=1/10`, `D'=1`. Nonvacuous: `W^{τ'}≤max diam_∞=⌊L/2⌋` for every `n`; for `τ'>1/5` the far set is empty at `sz0` (`W^{τ'}>L/2`), so `τ'=1/10` is the instance. Thresholds below are the `∀ᶠ`, not data.
`cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2133 && python3 table.py` (exponent table rows 1-9 at `sz0`; thresholds in `ln n`):
```
Q*=2D'+3+(2(k-1)+1+C0)/c = 35.0
--- hypotheses of stKcalDecay_holds / stDecayLoopAt on sz0, d=3, c=1/6, dd=1/10, kappa=1, E=0, u=1/2 (checked per n)
n=0: L=4 W=32 lam=1.562e-02 N=2.097e+06 N^c<=W:True Wd-lowerbound W^(-d/2+dd)<=lam:True W^(-3/2)<=lam:True lam<=1/dd:True
     ell_u=1 W^tau'=1.414 max diam_inf=2 far set nonempty(tau'=1/10):True; tau'=1/4 nonempty:False; 1-u=0.5>lam^2/L^2:True; 1/(1-u)=2<=N:True; W^(tau'/2)>=k-1:False
n=1: L=8 W=1024 lam=2.441e-04 N=5.498e+11 N^c<=W:True Wd-lowerbound W^(-d/2+dd)<=lam:True W^(-3/2)<=lam:True lam<=1/dd:True
     ell_u=1 W^tau'=2.000 max diam_inf=4 far set nonempty(tau'=1/10):True; tau'=1/4 nonempty:False; 1-u=0.5>lam^2/L^2:True; 1/(1-u)=2<=N:True; W^(tau'/2)>=k-1:False
n=7: L=32 W=1048576 lam=5.960e-08 N=3.778e+22 N^c<=W:True Wd-lowerbound W^(-d/2+dd)<=lam:True W^(-3/2)<=lam:True lam<=1/dd:True
     ell_u=1 W^tau'=4.000 max diam_inf=16 far set nonempty(tau'=1/10):True; tau'=1/4 nonempty:False; 1-u=0.5>lam^2/L^2:True; 1/(1-u)=2<=N:True; W^(tau'/2)>=k-1:True
n=100: L=404 W=336323216032 lam=1.472e-14 N=2.509e+42 N^c<=W:True Wd-lowerbound W^(-d/2+dd)<=lam:True W^(-3/2)<=lam:True lam<=1/dd:True
     ell_u=1 W^tau'=14.213 max diam_inf=202 far set nonempty(tau'=1/10):True; tau'=1/4 nonempty:False; 1-u=0.5>lam^2/L^2:True; 1/(1-u)=2<=N:True; W^(tau'/2)>=k-1:True
threshold W^(tau'/2)>=k-1: ln n >= 2.0  (n ~ e^2.0), ln W = 14.1
threshold exp(-sqrt(K/ell))<=W^-Q*: ln n >= 35.8  (n ~ e^35.8), ln W = 182.5
threshold |L|^2<=W^-(2D'+2)/16 (full chain): ln n >= 33.7  (n ~ e^33.7), ln W = 172.0
full chain and exp-bound hold for all grid points ln n in [35.8,400]: True
```
Cut inequality and adjacent-pair inequality, random Hermitian `H` (`d=3,L=5,W=1`, `N=125`, spectrum in `[−1.9,1.9]`, `z=E+iη`, `G^±=(H−z^{(±)})^{-1}`, `𝓛=Tr∏G^{σ_i}E_{a_i}`, 200 random `(σ,a)` times all `k` rotations; the cut is exactly `norm_sq_gloop_le_symIdx` with `symIdx`): `python3 cut.py`
```
d=3 L=5 W=1 k=3 E=0.3 eta=0.05: max |L|^2/(|symA||symB|) - 1 = 2.96e-13 (<=0 up to rounding); max |symB|*eta^(2(k-1)) = 0.0000 (<=1); max diam/((k-1)adj)=0.500 (<=1)
d=3 L=5 W=1 k=3 E=-1.0 eta=0.2: max |L|^2/(|symA||symB|) - 1 = 2.09e-14 (<=0 up to rounding); max |symB|*eta^(2(k-1)) = 0.0001 (<=1); max diam/((k-1)adj)=1.000 (<=1)
d=3 L=5 W=1 k=4 E=0.3 eta=0.05: max |L|^2/(|symA||symB|) - 1 = 1.86e-13 (<=0 up to rounding); max |symB|*eta^(2(k-1)) = 0.0000 (<=1); max diam/((k-1)adj)=0.667 (<=1)
d=3 L=5 W=1 k=4 E=-1.0 eta=0.2: max |L|^2/(|symA||symB|) - 1 = 3.00e-14 (<=0 up to rounding); max |symB|*eta^(2(k-1)) = 0.0000 (<=1); max diam/((k-1)adj)=0.667 (<=1)
```
(`≤0` up to rounding `3e-13`: Cauchy–Schwarz is attained, so the inequality is tight.) Target 2 at the merged flow `z0=(1/2, N^{-4/5})` on `sz0` (`STFlow` with `κ=ε=1/10`, `Admissible`, `locDomain`), window `[0,1/16]` (`1/16 ≤ lemT z0`), and the extreme `u=t₀=lemT z0`, `Cd=4`: `python3 t2.py` (columns as in the header line)
```
n  N  ImZ  t0=lemT  (1-t0)  sqrt(t0)ImZ/Imm  1/(1-t0)<=4N^(1-eps)  Bctl(t0)<=W^-2dd+4N^-eps  P(t0)=(1/(1-t0))^Cd Bctl^(1/5)<=N^Cd  |lemE|<=2-kap
0 2.097e+06 8.764e-06 0.999990948752 9.051e-06 9.051e-06 True True (B=1.732e-01) True (P=1.049e+20, N^Cd=1.93e+25) True (E=0.5000)
1 5.498e+11 4.054e-10 0.999999999581 4.187e-10 4.187e-10 True True (B=1.986e-02) True (P=1.486e+37, N^Cd=9.13e+46) True (E=0.5000)
2 8.125e+14 1.181e-12 0.999999999999 1.219e-12 1.219e-12 True True (B=5.627e-03) True (P=1.605e+47, N^Cd=4.36e+59) True (E=0.5000)
3 1.441e+17 1.875e-14 1.000000000000 1.937e-14 1.932e-14 True True (B=2.309e-03) True (P=2.111e+54, N^Cd=4.31e+68) True (E=0.5000)
window [0,1/16]: (1-0)/(1-1/16) = 1.0666666666666667 ; 1/16<=lemT z0 for all n (lemma28_quant):  True
```
External hypothesis: the only non-deterministic hypothesis is the decay input `STStep2DecayPT Cd sz E s t` (Step 2 output, another gate; `Step2Defs.lean:287`); it stays a hypothesis of the example in both targets. Its consistency with the instance is not computed here (no limit computation is possible without the Step-2 proof); what is computed is that its right side `P·STWB·e^{-√(K/ℓ)}+W^{-D}` tends to `0` at far pairs (row 7: `STWB≤2`, row 8) and that the conclusion's threshold (`ln n≥35.8`) is a threshold of `≺`, not a hypothesis.

### Verdicts
* Target 1 (`STDecayLoopAt`, `stDecayLoopAt_holds (hd : 3 ≤ d)`): **PASS**. All rows close with `Q*=2D'+3+(2(k−1)+1+C₀)/𝔠`; the pin's `1≤P` is harmless (row 13); `η_u⁻¹≤(2/√κ)N` is derived from the far premise (row 5-6), not assumed. Paper-delta candidates: `T2133a` (proof by the Cauchy–Schwarz cut from the `(+,−)` 2-loop decay only; paper's route uses `(GijGEX)`; weaker hypothesis, `k≥1` any), `T2133b` (`3 ≤ d` from `stKcalDecay_holds`, §36).
* Target 2 (`STDecayLoopPT`, `stDecayLoopPT_of_step2`): **PASS**, conditional on `0≤Cd` (for `Cd<0` use `C₀=0`), `0<κ,ε`, `0≤s≤t≤lemT z`, `STFlow`; must apply target 1 with `P'=max(P_u,1)` (row 13), `C₀=max Cd 0` (row 12); `E=STflowE z` (`|E|≤2−κ` by `lemma28_quant`). Prefactor bound from `locDomain` (`Im z≥N^{-1+ε}`), not from `STConStInd` (not needed).

## (b) Script output (stage 1b) -- written Sun Oct  4 12:20:09 UTC 2026

(`scratch/` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2133/`, run from `RBM3D-wt/T2133`)

```
$ git log -1 --format="%h %an <%ae> %s" ; git diff --name-only main...t/T2133   (worktree RBM3D-wt/T2133, branch t/T2133)
cc56e20 Jun Yin <321276894+JYin80@users.noreply.github.com> T2133: S3-07a Induction/DecayLoopA (STDecayLoopAt, STDecayLoopPT; proves lem_decayLoop at a single time and over a window)
RBM3D/Induction/DecayLoopA.lean

$ lake build RBM3D.Induction.DecayLoopA 2>&1 | grep "DecayLoopA\|error\|Build"   (warnings of other modules filtered out; none from DecayLoopA.lean)
Build completed successfully (3732 jobs).

$ lake build   (RBM3D.lean temporarily imports RBM3D.Induction.DecayLoopA after the last import; reverted afterwards, not committed)
683:info: RBM3D.lean:180:0: axiom audit: 3980 theorems, 1363 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
765:premises found by scanning: 71 (borrowed 0, owed 56, structural 15).
766:registry: 1 borrowed + 75 owed + 39 structural; 44 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
811:Build completed successfully (3881 jobs).
(grep -c "STDecayLoop" of that build log: 0)

$ lake env lean scratch/axioms.lean   (#print axioms of every new public declaration; file imports RBM3D.Induction.DecayLoopA)
'RBM.Gauss.Sizes.stDecayLoopAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDecayLoopPT_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.DecayLoopA_diam_le_KLmaxDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.DecayLoopAInst.sz0_far_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STdiamInf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STDecayLoopAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STDecayLoopPT' depends on axioms: [propext, Classical.choice, Quot.sound]

$ python3 scratch/extract.py   (target statements extracted from the file; proofs omitted)
-- RBM3D/Induction/DecayLoopA.lean:71
def STdiamInf {d L k : ℕ} (a : Fin k → Zd d L) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin k => zdistInf d L (a p.1 - a p.2)

-- RBM3D/Induction/DecayLoopA.lean:84
def STDecayLoopAt (sz : Sizes d) (κ 𝔠 𝔡 C₀ : ℝ) (E u P : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → sz.Admissible 𝔠 𝔡 → (∀ n, 0 ≤ u n) → (∀ n, u n < 1) →
  (∀ᶠ n : ℕ in atTop, 1 ≤ P n ∧ P n ≤ ((sz.size n : ℕ) : ℝ) ^ C₀) →
  (∀ D : ℝ, 0 < D →
    PrecPT sz (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω - STKloop sz n (E n) (u n) p.2.1 p.2.2‖)
      (fun n p _ => P n * STWB sz n (u n) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (u n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))) →
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPT sz (U := fun n => Unit × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (u n) p.2.1 p.2.2 ω - STKloop sz n (E n) (u n) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (u n) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

-- RBM3D/Induction/DecayLoopA.lean:105
def STDecayLoopPT (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

-- RBM3D/Induction/DecayLoopA.lean:936
theorem stDecayLoopAt_holds (hd : 3 ≤ d) (sz : Sizes d) (κ 𝔠 𝔡 C₀ : ℝ) (E u P : ℕ → ℝ) :
    STDecayLoopAt sz κ 𝔠 𝔡 C₀ E u P := by

-- RBM3D/Induction/DecayLoopA.lean:968
theorem stDecayLoopPT_of_step2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n)) (Cd : ℝ)
    (hD : STStep2DecayPT sz Cd (STflowE z) s t) : STDecayLoopPT sz (STflowE z) s t := by

$ python3 scratch/inst.py   (compiled nonempty instances: `sz0` at d = 3, all in the same file; hdec / hD = decay input, another gate)
-- DecayLoopA.lean:1106
theorem sz0_far_nonempty (n : ℕ) :
    ∃ a : Fin 3 → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
        (STdiamInf a : ℝ) := by

-- DecayLoopA.lean:1174
example (hdec : ∀ D : ℝ, 0 < D →
      PrecPT sz0 (U := fun n => Unit × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
        (fun n p ω => ‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω - STKloop sz0 n 0 (1 / 2) p.2.1 p.2.2‖)
        (fun n p _ => 1 * STWB sz0 n (1 / 2) (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1)) *
            Real.exp (-(((zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
              ellT (sz0.L n) (sz0.lam n) (1 / 2)) ^ (1 / 2 : ℝ)) +
          ((sz0.W n : ℕ) : ℝ) ^ (-D))) :
    PrecPT sz0 (U := fun n => Unit × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω =>
        (‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz0 n 0 (1 / 2) p.2.1 p.2.2 ω - STKloop sz0 n 0 (1 / 2) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (1 / 2) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
            (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  stDecayLoopAt_holds (d := 3) (by norm_num) sz0 1 (1 / 6) (1 / 10) 0 (fun _ => 0)
    (fun _ => 1 / 2) (fun _ => 1) (by norm_num) (fun n => by norm_num) sz0_admissible
    (fun _ => by norm_num) (fun _ => by norm_num)
    (Filter.Eventually.of_forall fun n => ⟨le_rfl, by simp⟩) hdec 3 (by norm_num) (1 / 10)
    (by norm_num) 1 (by norm_num)

-- DecayLoopA.lean:1197
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STDecayLoopPT sz0 (STflowE z0) sInst tInst :=
  stDecayLoopPT_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
    (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) Cd hD

-- DecayLoopA.lean:1204
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω =>
        (‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (p.1 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
            (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have h : STDecayLoopPT sz0 (STflowE z0) sInst tInst :=
    stDecayLoopPT_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
      (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
      (fun n => sixteenth_le_lemT n) Cd hD
  exact h 3 (by norm_num) (1 / 10) (by norm_num) 1 (by norm_num)

$ grep -rn "STdiamInf\|STDecayLoopAt\|STDecayLoopPT\|stDecayLoopAt_holds\|stDecayLoopPT_of_step2\|DecayLoopA_diam_le_KLmaxDist\|sz0_far_nonempty\|DecayLoopAInst" RBM3D --include="*.lean" | grep -v "RBM3D/Induction/DecayLoopA.lean"
(main worktree, main HEAD a871db4)
exit=1 (1 = no match)
(T2133 worktree)
exit=1 (1 = no match)

$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/DecayLoop.lean RBM2D/Induction/HierVocab.lean
9e0f275
 RBM2D/Induction/DecayLoop.lean | 149 ++--------------
 RBM2D/Induction/HierVocab.lean | 392 ++++++++---------------------------------
 2 files changed, 89 insertions(+), 452 deletions(-)

$ python3 scratch/check_inst.py   (numbers at the instance: sz0, d=3, E=0, u=1/2, kappa=1; these are lemmas used by the proof, not hypotheses)
n=0 L=4 W=32 g=1.562e-02 ell_u=1.0 1-u>=1/N:True g^2*W^d>=1:True STWB(K=0)=6.196e-05 STWB(K=2)=2.129e-05 (<=2) Bctl^(1/5)=0.144 (<=P=1) eta^-1=2.000 <= (2/sqrt(kappa))N=4.194e+06 far_set_nonempty(tau'=1/10)=True W^(1/10)=1.414 L/2=2
n=1 L=8 W=1024 g=2.441e-04 ell_u=1.0 1-u>=1/N:True g^2*W^d>=1:True STWB(K=0)=1.866e-09 STWB(K=2)=6.245e-10 (<=2) Bctl^(1/5)=0.018 (<=P=1) eta^-1=2.000 <= (2/sqrt(kappa))N=1.100e+12 far_set_nonempty(tau'=1/10)=True W^(1/10)=2.000 L/2=4
n=2 L=12 W=7776 g=2.143e-05 ell_u=1.0 1-u>=1/N:True g^2*W^d>=1:True STWB(K=0)=4.256e-12 STWB(K=2)=1.420e-12 (<=2) Bctl^(1/5)=0.005 (<=P=1) eta^-1=2.000 <= (2/sqrt(kappa))N=1.625e+15 far_set_nonempty(tau'=1/10)=True W^(1/10)=2.449 L/2=6
n=3 L=16 W=32768 g=3.815e-06 ell_u=1.0 1-u>=1/N:True g^2*W^d>=1:True STWB(K=0)=5.686e-14 STWB(K=2)=1.896e-14 (<=2) Bctl^(1/5)=0.002 (<=P=1) eta^-1=2.000 <= (2/sqrt(kappa))N=2.882e+17 far_set_nonempty(tau'=1/10)=True W^(1/10)=2.828 L/2=8

$ lake env lean scratch/names.lean   (the Mathlib names used, `env.contains`, see (c))
names present: 62   names missing: 0

$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/DecayLoopA.lean ; wc -l RBM3D/Induction/DecayLoopA.lean
exit=1 (1 = no match)
    1221 RBM3D/Induction/DecayLoopA.lean
```

### Narrative (b)
1. Result: `STdiamInf`, `STDecayLoopAt`, `STDecayLoopPT` are defined and `stDecayLoopAt_holds (hd : 3 ≤ d)`, `stDecayLoopPT_of_step2` are proved in `RBM3D/Induction/DecayLoopA.lean`, on branch `t/T2133` at `cc56e20`, the only file of `git diff main...t/T2133`; axioms are the three standard ones (output above); `RBM3D/Test/Axioms.lean` is not modified.
2. Pin 1 (`STDecayLoopAt sz κ 𝔠 𝔡 C₀ E u P`): hypotheses `0 < κ`, `|E n| ≤ 2 - κ`, `Admissible 𝔠 𝔡`, `0 ≤ u n < 1`, eventually `1 ≤ P n ∧ P n ≤ N^{C₀}`, and the decay input in the shape of a section of `STStep2DecayPT` (prefactor `P n * STWB * exp`); conclusion for every `k ≥ 1`, `τ'`, `D' > 0` as in the ticket, with `diam_∞ = STdiamInf`. Unlike RBM2D's `DecayLoopAt` there is no `0 ≤ C₀` hypothesis (`max C₀ 0` is used inside) and `1 ≤ P` is never used.
3. Route: ported from RBM2D `Induction/DecayLoop.lean` (809 lines at `9e0f275`; the ticket cites `c9a24cf`, the file changed since: diff-stat above) as private lemmas with the prefix `DecayLoopA_`: `adjacent`, `cut`, `pair`, `loopL_rotate(_iter)`, `loopL_two_sign`, `alg`, `exp_small`, `real_geom`. Replacements: `Z2 L ↦ Zd d L`, `zdist2 ↦ zdistInf`, `maxDist ↦ STdiamInf`, `gloop ↦ loopL`, `BlockIndex ↦ Vtx`, `KcalDecay ↦ STKcalDecay` (via `inst_stKcalDecay_admissible`), `scaleM⁻² ↦ STWB`.
4. New in `d ≥ 3`: `DecayLoopA_one_sub_u` derives `1 - u ≥ N⁻¹` from the far premise (`ℓ_u ≤ L/2 < L` gives `g² < L²(1-u)`, with `g² ≥ W^{-d}` from `(eq:WO)` and `L² ≤ L^d`); `η_u⁻¹ ≤ (2/√κ) N` follows from `Im m(E) ≥ √κ/2` (private copy of `ST_mE_im_ge`, `Step2Events` not imported); `DecayLoopA_STWB_le` gives `STWB ≤ (W^d g²)⁻¹ + (N(1-u))⁻¹ ≤ 2`, so `DecayLoopA_alg` has the constant `Θ = 2` in place of `(2/κ)²`.
5. Not used: `GbEXPHypV3`, `GijGEX`, any entry bound of `G`, `STConStInd`. Probability: only the decay-input event at the pair `c(σ,a)` with `τ₁ = 1`, `D = Q` (`perTimeCalc_of_imp`); `STKcalDecay` at `(2, τ'/2, Q)` and `(k, τ', D'+1)`.
6. Exponents in the Lean proof: `Q = 2D' + (2(k-1)+1+C₀)/𝔠 + 1` with the eventual threshold `W ≥ 16 Γ^{2(k-1)}(2+Θ)`, `Γ = 2/√κ`. Section (a) row 9 has `2D'+3+…`; the Lean proof uses the smaller exponent together with that threshold on `W`: a difference of constants, not a correction of (a).
7. Pin 2 (`STDecayLoopPT sz E s t`) and `stDecayLoopPT_of_step2` for `E = STflowE z` (forced by the flow): sections `u ∈ [s,t]` via `perSeq_of_perTime_timeIcc`; `1 - u ≥ N^{-1+ε/2}` from `v3_premises_of_stFlow`; `|E| ≤ 2 - κ` from `abs_lemE_le` and `locDomain`; `P_u' = max P_u 1`, `C₀ = max Cd 0 + 1` (`1 ≤ (1-s)/(1-u) ≤ N`, `Bctl = STWB .. 0 ≤ 2`, `N ≥ 2` eventually): valid for every real `Cd`; (a) row 12 and its verdict have `C₀ = Cd` / `max Cd 0` and need `0 ≤ Cd` and `Bctl ≤ 1` eventually, the Lean proof needs only `Bctl ≤ 2`: again a difference of constants, not a correction.
8. Instances: example 1 is target 1 at `sz0`, `κ = 1`, `E ≡ 0`, `u ≡ 1/2`, `P ≡ 1`, `C₀ = 0`, `k = 3`, `τ' = 1/10`, `D' = 1`, every deterministic hypothesis discharged; `hdec` (the Step-2 `(Eq:Gdecay_w)` at `s = u`, owed through `STStep2DecayPT`) stays a hypothesis. `sz0_far_nonempty` proves for every `n` a label vector with `ℓ_u W^{τ'} ≤ diam_∞ a`, so the indicator is not identically `0`. The check script shows `Bctl^{1/5} ≤ 1 = P` at `n = 0..3`, i.e. `P ≡ 1` dominates the paper's prefactor `Bctl^{1/5}` there; this is a numerical check only. Examples 2-3 are target 2 at `z0`, `flow_z0`, `[0, 1/16]`, any `Cd`, with `hD : STStep2DecayPT` as hypothesis.
9. Registry pre-check: with the temporary root import the full `lake build` ran `#assert_rbm_axioms` to the end (exit 0; 3980 theorems, 0 axioms). `STDecayLoopAt`/`STDecayLoopPT` are the conclusion heads of the two theorems, so they need no `owedProps` line; the build log has no line mentioning `STDecayLoop`.

## (c) Verified Mathlib names (all 62 present by `env.contains`, script above; one line per group)
- `Real.sqrt_eq_rpow`, `Real.sqrt_sq`, `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.sqrt_le_sqrt`, `Real.le_sqrt_of_sq_le`: `√x = x^(1/2)` turns the pin's `exp(-(x^(1/2)))` into `exp(-√x)`.
- `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_neg_one`, `Real.rpow_one`, `Real.rpow_def_of_pos`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.log_le_rpow_div`, `Real.exp_le_exp`.
- `div_lt_iff₀`, `div_le_iff₀`, `le_div_iff₀`, `div_le_div_iff₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_one₀`, `pow_lt_pow_left₀`, `sq_le_sq₀`, `one_div_le_one_div_of_le`, `mul_inv_cancel₀`, `le_of_mul_le_mul_right`, `le_mul_of_one_le_right`, `le_mul_of_one_le_left`.
- `tendsto_rpow_atTop`, `Filter.tendsto_atTop_mono'`, `Filter.Tendsto.eventually_ge_atTop`; `norm_le_norm_add_norm_sub'`, `norm_sub_le`.
- `Finset.exists_mem_eq_sup`, `Finset.sup_le`, `Finset.le_sup`, `Finset.mem_univ`; `List.getElem?_rotate`, `List.rotate_cons_succ`, `List.length_rotate`, `List.zip_append`, `List.getLast?_concat`, `List.getLast?_eq_getElem?`, `List.eq_nil_or_concat'`; `ZMod.val_natCast_of_lt`; `Matrix.trace_mul_comm`, `Matrix.IsHermitian.submatrix`; `min_lt_iff`.
- Absent: `tendsto_atTop_mono'` in the root namespace (`Unknown constant`, the name is `Filter.tendsto_atTop_mono'`). Deprecated in this Mathlib: `push_neg` (build warning "Prefer `push Not`"; not used in the file).

## (d) Open issues and paper-delta candidates
- The decay input is the only non-deterministic hypothesis in both targets (`STStep2DecayPT`, owed, Step 2 chain ST2-04); no limit computation of it is possible here (see (a)); the instance only uses its right side `P·STWB·exp + W^{-D}` at the far pair.
- The pin carries `0 < κ` (as RBM2D's `DecayLoopAt`); the proof uses it for `Im m(E) ≥ √κ/2` (`η_u⁻¹ ≤ (2/√κ) N`).
- `STDecayLoopPT` is the per-time form (union over `(σ, a)` outside `P`, as the ticket specifies); the uniform-in-`(σ,a)` form would follow by `stochDomAt_of_perTimeDomAt` (polynomially many labels) and is not proved here.
- `T2133a`: the paper (`3_5:1113`) obtains the decay of general `G`-loops "With `(GijGEX)`" and `lem_decayLoop` (`3_5:1126-1127`) lists `(Gt_bound_flow)` and `(Eq:Gdecay_w)` as hypotheses; Lean proves it by the Cauchy-Schwarz cut from the `(+,-)` 2-loop decay only (no `(GijGEX)`, no `(Gt_bound_flow)`), a weaker hypothesis set.
- `T2133b`: `3 ≤ d` is a hypothesis of `stDecayLoopAt_holds` and of `stDecayLoopPT_of_step2` (from `stKcalDecay_holds`, DECISIONS §36); the paper's setting is `d ≥ 3` throughout, so this restricts only the Lean parameter.
- `T2133c`: `res_decayLK` (`3_5:1128`) bounds `|𝓛| + |𝒦|`; the Lean conclusion bounds `|𝓛| + |𝓛-𝒦|` (each controls the other up to a factor 2, absorbed by `≺`); `k = 1` is included (vacuous: `diam_∞ = 0 < ℓ_u W^{τ'}`), the paper has `n ≥ 2`; `τ' = ε`, and the probability statement is the per-time `≺` with `W^{-D'}`.
- `T2133d`: the prefactor of `(Eq:Gdecay_w)` is carried as `P` with `C₀`: `P' = max(((1-s)/(1-u))^{Cd} Bctl^{1/5}, 1)`, `C₀ = max Cd 0 + 1`; the paper does not track it (RBM2D `decayLoopWindow` uses `P = (η_s/η_u)^4`, `C₀ = 4`; `decayLoopFromML` uses `P ≡ 1`, `C₀ = 0`).
- Downstream: consumers can take `STDecayLoopPT sz E s t` as a hypothesis or apply `stDecayLoopPT_of_step2` (then `STStep2DecayPT` is the owed premise).
