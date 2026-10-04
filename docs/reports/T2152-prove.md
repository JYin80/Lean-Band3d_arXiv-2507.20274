Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 18:31:18 UTC 2026

Notation: `N = (WL)^d = card Idx`, `w := (log W)^3 ℓ_s` (`ℓ_s = ellT L lam s`), `E = STflowE z`, `κ' = κ/2`, `c_κ' = √(κ'(4-κ'))/2`. Sources: merged RBM3D (`main` 4f4612b), RBM2D `CltStep.lean`/`CltDecorrelation.lean` (HEAD 9e0f275 differs from `c9a24cf` in comments only: `git diff c9a24cf HEAD` touches docstrings and `#print` lines of `CltStep.lean`).

### (i) Route and exponent table

**Route (merged statement used at each step; file:line).** Item 1: `STcltB` (`Step5Pins:399`) `= scale · STLKM … (seqHflow n s ω)`, `STLKM = loopFine − STKloop` (`Step2Defs:68`), `loopFine = tr(G(σ₀)E_{b₀}G(σ₁)E_{b₁}) = Σ_{x∈[b₀],y∈[b₁]} G(σ₀)_{yx}G(σ₁)_{xy}` (`GLoopFlow:110`, `Eblk` `Loop/GLoop:55`), `seqHflow` is `Hflow ∘ slice` up to defeq (`seqHflow_isHermitian`, `FineModel:533`, is proved by `Hflow_isHermitian … (slice sz n ω)`; to be confirmed by `rfl` in 1b). So `STcltB = cltEvalAt F (slice ω) b + const` with `F : LocalForm 3 L W 2 2` (`CltResolvent:70`; `cltEvalAt` `CltPath:60`): `coef b 2 q = scale · [q = ((y,x,σ₀),(x,y,σ₁)), [x]=b₀, [y]=b₁]` if `|b₀−b₁|_∞ ≤ w` else `0`; `coef b 0 _ = −scale·𝔼𝓛_b` (the `𝒦` part cancels in `STcltX`: `B − ∫B`). `Local ρ` (`CltResolvent:87`) holds at `ρ = w+1`. Item 2: `cltFarGeomHalf` (`:746`) on the first labels at `R = 10w`; `cltPathMulti_bound` (`CltPath:281`, `k = 2` labels, hypothesis `∀ m, R'/2 ≤ |[c.1]−b_m|`); `cltCoord_adj` (`:805`); `cltGood_whp` (`CltGood:561`, `CltGoodWhp :125`) and `cltCoord_tail` (`:323`); `cltEval_detMulti_le` (`CltResolvent:694`) with `cltEta_lower` (`:610`) on the bad event; `cltHyb`, `cltHyb_succ`, `cltHyb_eq_update_succ`, `measurePreserving_cltSplit`, `integral_eq_zero_of_cltSwap_neg`, `update_cltSwap_fst` (`CltSwap:70,108,124,232,299,191`). Item 3: `HClt` at `τ = s` (`CltGood:64`; the premises of `STIngR5` `Step5Pins:82` give `STFlow`, `0≤s<t≤lemT`, `STStep2Concl`), `v3_premises_of_stFlow` (`Green/Pins:1049`: `|E|<2−κ/2`, `t<1`, `RangeCond (ε/2) t`), `cltTransfer` (`CltSwap:323`), `cltTelescope` (`:94`), step count `card CoordF = 2N²`.
Per-step proof (port of RBM2D `CltStep.lean:579-600`): `‖X_m(ω)−X_m(ω')‖ = ‖Y_m(ω)−Y_m(ω')‖` (centring and `conj` cancel, `cltstep_Xo_sub`), so no conjugate local form is needed. Case A: path bound on `X_i` from `T_k` to `ω'c`; case B: path bound on each `X_m`, `m≠i`, from `ω` to `0`, product-difference `|∏f−∏g| ≤ #s X^{#s} δ`, and `cltSwap c` kills `∫(X_i(T_k)−X_i(T_{k+1}))Γ_i(ω^{c→0})`. **No product local form `Γ_i` is needed** (the path bound is applied factor by factor, as in RBM2D); `F` has `k = 2` labels, `K = 2`.

| # | Quantity | Value / constraint | Slack |
|---|---|---|---|
| 1 | locality radius `ρ` | `x∈[b_m]`: `d(blk x,b_m)+d(blk y,b_m) ≤ |b₀−b₁| ≤ w < ρ := w+1` (script 2: max sum `= 2 = w` at `w=2`) | strict by 1 |
| 2 | separation `R'` | dichotomy at `R = 10w` on first labels: `5w ≤ |a−b_{i0}|`, then `|a−b_{i1}| ≥ 5w−w = 4w`; likewise for every `k≠i`. So `R'/2 = 4w`, `R' = 8w` (not `R = 10w` as in RBM2D) | `5w` vs `4w` |
| 3 | far threshold `θ` | `θ ≤ R'/2−ρ−1 = 3w−2` (`cltFarGeomNear`); use `θ_n := max(3w_n−2, w_n)` (so the `∀ n` hypothesis `c·w ≤ θ n` of `cltGood_whp` holds at `c = 1` for every `n`; `= 3w−2` once `w ≥ 1`, i.e. `W ≥ 3`) | `θ−w = 2w−2 ≥ 0` for `w ≥ 1` |
| 4 | `c` of `STFarEntryAtLog` | `c = 1` suffices (ticket/T2144 said `c ≤ 2`, which needs `w ≥ 2`); any `c ≤ (3w−2)/w` | `c = 1` ok at `w ≥ 1` |
| 5 | step length | `|ω c|,|ω'c| ≤ W^{-1/2}` (bad event `cltCoord_tail`: `2e^{−W^{d−1}/2} ≤ N^{-D''}`), `|s−ω₀c| ≤ 2W^{-1/2}`, `16W^{-1/2} ≤ 1` iff `W ≥ 256` | `W=1024`: `0.5` |
| 6 | `η` lower bound | `RangeCond (ε/2)`: `N^{-1+ε/2} ≤ 1−t ≤ 1−s`, `δ = ε/2`; `|E| < 2−κ/2`; `cltEta_lower`: `Im z_s ≥ c_κ'/N`. The regime `STReg5I` is **not used** by the proof | script 3 |
| 7 | coefficient bound `C'` | `scale = (λ²W^d)^{6/5} ≤ 𝔡^{-12/5}W^{3.6}` (`WO`: `λ ≤ 𝔡⁻¹`); `|𝓛_b| ≤ W^{2d}N²/c_κ'²` (all `G`-entries `≤ N/c_κ'`), so `|coef| ≤ 𝔡^{-12/5}c_κ'^{-2}N^{5.2} ≤ N^{C'}`, `C' = 6`, eventually (`N^{0.8} ≥ 𝔡^{-12/5}c_κ'^{-2}`) | measured exponent `3.47` (`W=1024`), `3.63` (`szCL`) vs `6` |
| 8 | `a`, `D''`, `D'` | `K=2`: `a = C'+3K+2 = 14`; `D'' = a(2p+2)+D+4` (`p=1`: `60+D`); `D' = D''/𝔠`, `W^{-D'} ≤ N^{-D''}` by `Bandwidth` (`N^𝔠 ≤ W`) | equality in `Bandwidth` step |
| 9 | bad-event moments | `‖X_m‖ ≤ 2(K+1)N^{C'}(2N³/c_κ')^K ≤ N^a`; bad pair set `A₁∪A₂∪A₃∪A₄` (coordinate tails at `ω,ω'`; `¬cltGoodAt` at `ω` and at `T_k`, law `P` by `measurePreserving_cltSplit`): `≤ 4N^{-D''}` (one `cltGood_whp` event, not E2∪E3: `4ε`, RBM2D `6ε`); `∫ ≤ 4pX^{2p+1}·N^aW^{-D'} + 4X^{2p+1}·4ε ≤ (4p+16)N^{-D-4} ≤ N^{-D-3}` iff `N ≥ 4p+16` | `N ≥ 20` at `p=1` |
| 10 | assembly | `‖∫∏X_k‖ ≤ card CoordF·N^{-D-3} = 2N^{-D-1} ≤ N^{-D} ≤ W^{-D}` (needs `N ≥ 2`, `W ≤ N`) | factor `N` |
| 11 | `σ₀ ≠ σ₁` | not used (the form exists for every `σ`) | — |
| 12 | eventual conditions (one `filter_upwards`) | `N ≥ max(C₁,C₂,4p+16,2)`, `Bandwidth`, `RangeCond`, `WO` (`λ ≤ 𝔡⁻¹`), `W ≥ 256`, `W ≥ 3`, `cltCoord_tail`, `cltGood_whp` at `(c,θ,D',D'')`; uniform in the 4 sign vectors `σ` | — |

**Findings (for 1b, no merged statement changes).** (F1) `coef` must vanish outside the window `|b₀−b₁| ≤ w` (`Local` quantifies over all `b`); (F2) the coefficient bound is only eventual in `n` (constants `𝔡⁻¹`, `c_κ'⁻¹`): state the step per `n` with `∀ᶠ n` coefficient hypothesis; (F3) `szCL_cltIso_witness` (`Step5Pins:927`) has window `0`; the instance for item 2 should use a window `⌊w⌋ > 0` (below); (F4) `v3_premises_of_stFlow` gives `κ/2` not `κ` in `cltEta_lower`; (F5) merged statements serve the two-label and log-scale use: no stop.

### (ii) One concrete nondegenerate instance

`d=3`, `λ=1`, `s=0` (`ℓ_s = 1`), `p=1`, `D=1`, `K=2`, `κ=ε=𝔡=𝔠=1/10`, `C'=6`, `t=1−L^{-2}`, regime (i) `λ²/L² = 1−t ≤ 1−s = λ² = 1`. Labels `b^{(1)} = ((0,0,0),(⌊w⌋,0,0))` (window `⌊w⌋ > 0`), `b^{(2)} = ((⌈10w⌉,0,0),(⌈10w⌉,0,0))`; case A coordinate `a = (−⌈5w⌉,0,0)`, case B `a = (1,0,0)`. Instance M: `W=1024`, `L=6700` (`L ≥ 2⌈10w⌉ = 6662`); instance S: `szCL`, `n=0` (`W=2^24`, `L=2·24^5`; the Lean instances are on `szCL`, flow `flow_zCL`, `STStep2Concl` stays the only hypothesis of item 2).
Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2152/inst.py` (instance M, full output; instance S abridged by `grep -E "==|ALL|window|isolation|Bandwidth|final"`):
```
== minimal-ish: W=1024 L=6700 N=(WL)^3 ln N=47.22  ell_s=1.0  w=(log W)^3 ell_s=333.02
  16 W^-1/2 <= 1                                          True  0.5
  w>=1 (theta>=w, c=1)                                    True  333.02465198892946
  theta=3w-2 >= w                                         True  664.0493039778589
  window |b_k0-b_k1|<=w, positive                         True  333
  isolation 10w<=|b_i0-b_j0|                              True  3331
  case A: 4w<=|a-b_i m| both m                            True  [1666, 1999]
  case B: 4w<=|a-b_j m| both m                            True  [3330, 3330]
  monomial block x=b_i m vs a (A): >= theta               True  1666
  Local rho: sum <= w < rho=w+1                           True  333
  coef bound exponent <= C'=6                             True  3.472777290031662
  a=C'+3K+2                                               True  14
  D''=a(2p+2)+D+4                                         True  61
  D'=D''/c                                                True  610.0
  Bandwidth N^c<=W                                        True  (4.722400383293553, 6.931471805599453)
  W^-D' <= N^-D'' (ln)                                    True  (-4228.197801415667, -2880.6642338090674)
  coord tail ln(2exp(-W^2/2)) <= -D'' lnN                 True  (-524288.0, -2880.6642338090674)
  N>=4p+16 (per-step absorb)                              True  322941812211712000000
  final 2N^2 N^(-D-3) <= W^-D (ln)                        True  (-93.75486048531111, -6.931471805599453)
  per-step bad part 16 N^(a(2p+1)-D'') <= N^(-D-4)        True  None
  ALL True
== szCL n=0: W=16777216 L=15925248 N=(WL)^3 ln N=99.66  ell_s=1.0  w=(log W)^3 ell_s=4603.73
  window |b_k0-b_k1|<=w, positive                         True  4603
  isolation 10w<=|b_i0-b_j0|                              True  46038
  Bandwidth N^c<=W                                        True  (9.96568459972151, 16.635532333438686)
  final 2N^2 N^(-D-3) <= W^-D (ln)                        True  (-198.62054481387023, -16.635532333438686)
  ALL True
minimal-ish regime(i): lam^2/L^2 = 1-t <= 1-s = lam^2 = 1; RangeCond ln: -2lnL = -17.62 <=? -(1-eps/2) lnN = -44.86  (RangeCond means N^(-1+eps/2) <= 1-t): True
szCL n=0 regime(i): lam^2/L^2 = 1-t <= 1-s = lam^2 = 1; RangeCond ln: -2lnL = -33.17 <=? -(1-eps/2) lnN = -94.67  (RangeCond means N^(-1+eps/2) <= 1-t): True
```
The size is forced: isolation `10w ≤ L/2` with `w ≥ (log W)^3` and `W ≥ 256` gives (at `W=256`, `w=170.5`, `L=3412`) `N = 6.66·10^{17}`, `ln N = 41.04`; so no case with `N < 10^{17}` satisfies the hypotheses of item 2. The slacks above are `e^{-87}` (M) and `e^{-182}` (S) in the final bound.
**Limit computations (external/eventual inputs).** `STStep2Concl`: premise of `STIngR5`/`HClt`, no limit to compute here (T2149 (a) did the `N^{τ'}STWB ≤ 1` computation). Coordinate tail: `−W²/2 = −524288 ≤ −61 ln N = −2881` (M), `−1.4·10^{14}` vs `−6079` (S); `Bandwidth` and `RangeCond` above; `N^{0.8} ≥ 𝔡^{-12/5}c_κ'^{-2}`: exponent `3.47 ≤ 6` measured.

**Script 1** `geom.py` (two-label geometry, periodic `L^∞` on `Z_L^3`; random configs `p = 1,2,3`, `L = 61…201`, plus exhaustive `L=19, w=2`):
```
configs 32000 caseA 29004 caseB 24502 violations 0
exhaustive L=19 w=2: triples 11758500 violations 0 theta 4
```
(violations = configs with neither case A nor B at `R'/2 = 4w`, plus entries local to a label (`d<w+1`) at distance `< 3w−2` from `a` or `a'`.)
**Script 2** `form.py` (`d=3, L=5, W=2`, `N=1000`, random Hermitian `H`, `z = 0.3+0.4i`, three `σ`, 15 label pairs within window `w=2`): loop vs `LocalForm` j=2 part, `Local`, conjugation:
```
label pairs within window 15 | max |loop - form| = 2.673771110915334e-15
max Local-sum over monomials = 2 < rho = 3
pair at distance 2 > w=1 exists: 2
max |conj G(+)_{xy} - G(-)_{yx}| = 6.27944979129416e-15
```
(`W=1`, `L=5` is degenerate: `log 1 = 0`, `w = 0`; `W=2` has `N = 1000`, blocks of `8` points.)

### Verdicts
* Target 1 (local forms, coefficient bound `N^6`, `Local (w+1)`): **PASS**.
* Target 2 (per-step bound, two labels, `R'=8w`, `ρ=w+1`, `θ=3w−2`, `c=1`): **PASS**.
* Target 3 (`stCltIso_holds 3`, `2N²·N^{-D-3} ≤ W^{-D}`): **PASS**.

### (a′) Preflight corrections — Sun Oct  4 19:08:35 UTC 2026

Two numbers of (a) were wrong; neither changes a verdict (targets 1-3 stay PASS); nothing else in (a) was changed.
* Rows 7-8, the coefficient. (a) has `coef b 2 q = scale·[…]`, `C' = 6`, `a = 14`. The loop carries `Eblk = W^{-d}·1_{[a]}` twice (`RBM3D/Loop/GLoop.lean:55`;
  Lean: `cltStep_loopFine_two`, `loopFine = (W^d)^{-2} Σ_{y∈[b₂],x∈[b₁]} G(σ₁)_{yx}G(σ₂)_{xy}`), so `coef = scale·W^{-2d}·[…]`, `‖coef‖ ≤ scale ≤ N^2` (`cltStep_scale_le`):
  `C' = 2`, `a = C'+3K+2 = 10`, `D'' = a(2p+2)+D+4` (`44+D` at `p = 1`; (a) says `60+D`).
* Row 12 also needs `N ≥ 𝔡^{-3}` (for `scale ≤ N^2`, from `ilambda ≤ 𝔡⁻¹`, `W^d ≤ N`).

### (b) Script output

Build (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2152`, branch `t/T2152`, commit `80b1692`):
```
$ lake build RBM3D.Evolution.CltStep > build.out 2>&1; echo $?                      # Sun Oct  4 19:04:33 UTC 2026
0
$ grep -c 'CltStep.lean.*\(warning\|error\)' build.out
0
$ tail -n 1 build.out
Build completed successfully (3809 jobs).
$ grep 'CltStep.lean' build.out | grep 'depends on axioms' | grep -c '\[propext, Classical.choice, Quot.sound\]$'
12   (of 12 `#print axioms` lines, for:)
  cltStep_pairForm_eval, cltStep_loopForm_eval, cltStep_loopForm_local, cltStep_loopForm_coef_le, cltStep_loopForm_coef_le_eventually, cltStep_loopForm_stcltB, cltStep_scale_le, cltStep, Sizes.stCltIso_holds, Step5Inst.cltStep_zdistInf_yCL, Step5Inst.cltStep_szCL_witness, Step5Inst.cltStep_szCL_coef
```
Registry pre-check and whole-library builds (DECISIONS §16, §20; the pre-check file is outside the worktree, never committed):
```
Sun Oct  4 19:05:24 UTC 2026
$ lake build   (whole library, with a temporary uncommitted root import `import RBM3D.Evolution.CltStep` in RBM3D.lean)
exit code: 0
Build completed successfully (3917 jobs).
lines starting with error: 0
registry line of the audit: registry: 1 borrowed + 88 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Sun Oct  4 19:05:43 UTC 2026
$ lake env lean precheck.lean   # precheck.lean = import RBM3D; import RBM3D.Evolution.CltStep; #assert_rbm_axioms
exit code: 0
axiom audit: 4659 theorems, 1657 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
lines mentioning STCltIso: 0; lines containing 'error': 0
Sun Oct  4 19:05:05 UTC 2026
$ lake build   (committed RBM3D.lean, without the root import of CltStep)
exit code: 1
error: RBM3D.lean:198:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Gauss.Sizes.STCltIso]
```
Branch content (`git`), registry diff:
```
Sun Oct  4 19:06:39 UTC 2026
$ git status --short | wc -l; git log -1 --format="%h %an %s"; git diff --stat main...t/T2152
       0
80b1692 Jun Yin <321276894+JYin80@users.noreply.github.com> T2152: S5-21 Evolution/CltStep (proves STCltIso)
 RBM3D/Evolution/CltStep.lean | 1594 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    1 -
 2 files changed, 1594 insertions(+), 1 deletion(-)
$ grep -c -E "sorry|admit|native_decide|^axiom " RBM3D/Evolution/CltStep.lean; wc -l RBM3D/Evolution/CltStep.lean
0
    1594 RBM3D/Evolution/CltStep.lean
$ git diff main...t/T2152 -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-110
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STCltIso, -- `(eq:bound_isolated)`; proved internally (DECISIONS §40); S5-01 (T2138, DECI
```

Target statements, extracted from the file by script (`extract.py`: declaration line to `:= by` or the first blank line; `d` and `sz : Sizes d` are section variables):
```
-- CltStep.lean:1312
theorem stCltIso_holds (d : ℕ) : STCltIso d := by
-- CltStep.lean:748
theorem cltStep (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ)
    (hH : HClt sz κ ε 𝔠 𝔡 z s s t Cd) (K : ℕ) (C' : ℝ) (hC' : 0 ≤ C')
    (F : ∀ n, LocalForm d (sz.L n) (sz.W n) 2 K)
    (hcoef : ∀ᶠ n in atTop, ∀ b j q, ‖(F n).coef b j q‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C')
    (hloc : ∀ n, (F n).Local (cltStep_win sz n (s n) + 1))
    (p : ℕ) (hp : 1 ≤ p) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n in atTop,
      ∀ (b : Fin (2 * p) → Fin 2 → Zd d (sz.L n)) (i : Fin (2 * p)),
        (∀ m, ((zdistInf d (sz.L n) (b m 0 - b m 1) : ℕ) : ℝ) ≤ cltStep_win sz n (s n)) →
        (∀ m, m ≠ i →
          10 * cltStep_win sz n (s n) ≤ ((zdistInf d (sz.L n) (b i 0 - b m 0) : ℕ) : ℝ)) →
        ∀ (e : CoordF d (sz.L n) (sz.W n) ≃ Fin (Fintype.card (CoordF d (sz.L n) (sz.W n))))
          (j : ℕ), j < Fintype.card (CoordF d (sz.L n) (sz.W n)) →
          ‖∫ q, (cltStep_Xo (F n) (sz.lam n) (STflowE z n) (s n) b i
                  (cltHyb d (sz.L n) (sz.W n) e j q.1 q.2) -
                cltStep_Xo (F n) (sz.lam n) (STflowE z n) (s n) b i
                  (cltHyb d (sz.L n) (sz.W n) e (j + 1) q.1 q.2)) *
              cltStep_Gamma (F n) (sz.lam n) (STflowE z n) (s n) b i q.1
            ∂((PF d (sz.L n) (sz.W n) (sz.lam n)).prod (PF d (sz.L n) (sz.W n) (sz.lam n)))‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ (-D - 3) := by
-- CltStep.lean:1031
def cltStep_loopForm (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) : LocalForm d (sz.L n) (sz.W n) 2 2 :=
  cltStep_pairForm (cltStep_c2 sz n σ (cltStep_win sz n s)
    ((cltStep_scale sz n * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 : ℝ) : ℂ))
-- CltStep.lean:1195
theorem cltStep_loopForm_stcltB (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n))
    (hb : (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ cltStep_win sz n s) (ω : sz.SeqΩ) :
    STcltB sz n E s σ b ω =
      cltEvalAt (cltStep_loopForm sz n s σ) E s (sz.slice n ω) b -
        ((cltStep_scale sz n : ℝ) : ℂ) * STKloop sz n E s σ b := by
-- CltStep.lean:1096
theorem cltStep_loopForm_local (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) :
    (cltStep_loopForm sz n s σ).Local (cltStep_win sz n s + 1) := by
-- CltStep.lean:1131
theorem cltStep_loopForm_coef_le (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n))
    (j : Fin (2 + 1)) (q : Fin j → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) :
    ‖(cltStep_loopForm sz n s σ).coef b j q‖ ≤ cltStep_scale sz n := by
```
Compiled nonempty instances (same file, section 8; `d = 3`, `Step5Inst.szCL`, every `n`; `STStep2Concl`, another gate's pin, stays a hypothesis of the `cltStep` instance; statements as in the file, proofs omitted):
```
-- CltStep.lean:1432
theorem cltStep_szCL_witness (n : ℕ) :
    ∃ b : Fin (2 * 1) → (Fin 2 → Zd 3 (szCL.L n)),
      (∀ k, ((zdistInf 3 (szCL.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤ cltStep_win szCL n (sCL n)) ∧
      0 < zdistInf 3 (szCL.L n) ((b 0) 0 - (b 0) 1) ∧
      (∀ j, j ≠ 0 → 10 * cltStep_win szCL n (sCL n) ≤
        ((zdistInf 3 (szCL.L n) ((b 0) 0 - (b j) 0) : ℕ) : ℝ)) := by
-- CltStep.lean:1509
example : InstIng5Concl (fun sz E s t => STCltIsoConcl sz E s t) szCL zCL sCL tCL 1 :=
  inst_cltIso (stCltIso_holds 3) 1 one_pos
-- CltStep.lean:1527
example : STCltIso 3 := stCltIso_holds 3
-- CltStep.lean:1533
example (n : ℕ) (E : ℝ) (ω : szCL.SeqΩ) :
    ∃ b : Fin 2 → Zd 3 (szCL.L n), 0 < zdistInf 3 (szCL.L n) (b 0 - b 1) ∧
      STcltB szCL n E (sCL n) ![true, false] b ω =
        cltEvalAt (cltStep_loopForm szCL n (sCL n) ![true, false]) E (sCL n) (szCL.slice n ω) b -
          ((cltStep_scale szCL n : ℝ) : ℂ) * STKloop szCL n E (sCL n) ![true, false] b ∧
      (cltStep_loopForm szCL n (sCL n) ![true, false]).Local (cltStep_win szCL n (sCL n) + 1) ∧
      ∀ b' j q, ‖(cltStep_loopForm szCL n (sCL n) ![true, false]).coef b' j q‖ ≤
        cltStep_scale szCL n := by
-- CltStep.lean:1567
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :=
  (cltStep szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL tCL 1 (cltGood_hclt_szCL hStep2) 2 2
    (by norm_num) (fun n => cltStep_loopForm szCL n (sCL n) ![true, false])
    (cltStep_szCL_coef ![true, false])
    (fun n => cltStep_loopForm_local szCL n (sCL n) ![true, false]) 1 le_rfl 1 one_pos).mono
    fun n hn => hn (cltStep_szCL_witness n).choose 0 (cltStep_szCL_witness n).choose_spec.1
      (cltStep_szCL_witness n).choose_spec.2.2
-- inferred type of the last example (`#check` on a scratch copy, `lake env lean t4.lean`; first 5 lines, the rest elided):
instItem2 : szCL.STStep2Concl (STflowE zCL) sCL tCL 1 →
  ∀ᶠ (x : ℕ) in atTop,
    ∀ (e : CoordF 3 (szCL.L x) (szCL.W x) ≃ Fin (Fintype.card (CoordF 3 (szCL.L x) (szCL.W x)))),
      ∀ j < Fintype.card (CoordF 3 (szCL.L x) (szCL.W x)),
```
Name-clash grep of the 20 new public names against main (`a438a51`): `grep -rn -w -E "<name>" RBM3D RBM3D.lean --include="*.lean"` run in `/Users/junyin/Lean_proof/RBM3D` at Sun Oct  4 19:03:08 UTC 2026: names with at least one hit: `[]`.
Ports from RBM2D (read-only, source commit `c9a24cf`; source file:line -> target):
```
RBM2D/Evolution/CltStep.lean:64-259 -> cltStep_*_meas/_Xo_sub/_Xo_le/_Gamma_le/_coefSum_*/_prod_sub_le/_norm_integral_le/_pull_le/_ae_zero;  :261-544 -> cltStep_core;
RBM2D/Evolution/CltStep.lean:546-560 -> cltStep_ck_pos, cltStep_absorb;  :573-716 -> cltStep;  CltDecorrelation.lean:110-217 -> cltStep_Xo_integral, cltStep_assembly;
RBM2D/Evolution/CltDecorrelation.lean:229-266 -> cltStep_exponent, cltStep_card_coord;  :305-368 -> stCltIso_holds (assembly).  No RBM2D source: cltStep_geom, *_pairForm*, *_loopForm*,
cltStep_loopFine_two, cltStep_gres_blockMat, cltStep_scale_le, cltStep_STcltX_eq, section 8.  RBM1D: none.
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   # -> 9e0f275 (HEAD)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/CltStep.lean RBM2D/Evolution/CltDecorrelation.lean
 RBM2D/Evolution/CltDecorrelation.lean | 75 +++++++++++++----------------------
 RBM2D/Evolution/CltStep.lean          | 47 +++++++---------------
 2 files changed, 42 insertions(+), 80 deletions(-)
$ python3 portdiff.py   # strip comments/docstrings/#check/#print from both versions, compare
RBM2D/Evolution/CltStep.lean code lines at c9a24cf: 618 at HEAD: 618 identical after dropping comments/docstrings/#check/#print: True
RBM2D/Evolution/CltDecorrelation.lean code lines at c9a24cf: 296 at HEAD: 296 identical after dropping comments/docstrings/#check/#print: True
```

**Narrative** (all facts are in the file or in the output above).
1. Item 1. `cltStep_loopForm` is `cltStep_pairForm` of `cltStep_c2`: the monomial `G(σ₁)_{yx}G(σ₂)_{xy}`, `x ∈ [b₁]`, `y ∈ [b₂]`, supported on the window
   `|b₁−b₂|_∞ ≤ w_n = (log W)^3 ℓ_s` (`cltStep_win`). `cltStep_loopFine_two` expands `loopFine`; `cltStep_loopForm_eval`: `eval = scale·loopFine` in the window;
   `cltStep_loopForm_stcltB`: `STcltB = cltEvalAt − scale·STKloop` (`seqHflow = Hflow ∘ slice` is `rfl`, used by `change`, as (a) conjectured).
2. Item 2. `cltStep_core` (private) is RBM2D `cltstep_core` for `k` labels: case A is `cltPathMulti_bound` on `X_i` from `T_j` to `ω'c`; case B is `cltPathMulti_bound` on each
   `X_m`, `m ≠ i`, from `ω` to `0`, the product-difference bound and `integral_eq_zero_of_cltSwap_neg`. The geometry is the hypothesis `hgeom` (`R/2 = 4w`), proved by
   `cltStep_geom` from `cltFarGeomHalf` on the first labels (`10w ⇒ 5w`) and the window (`5w − w`). Parameters: `ρ = w+1`, `R = 8w`, `θ_n = max(3w_n−2, w_n)`, which is
   `≤ R/2−ρ−1 = 3w−2` once `w ≥ 1` (`W ≥ 3`, `ℓ_s ≥ 1`); the good event is the single event of `cltGood_whp` at `c = 1`, `D' = D''/𝔠`, so the bad pair set has measure
   `≤ 4N^{-D''}` (RBM2D: `6`); the step is `≤ (4p+16) N^{-D-4} ≤ N^{-D-3}` for `N ≥ 4p+16`. Eventual conditions: `N`, `W^{1/2} ≥ 16`, `W ≥ 3`, `Bandwidth`, `RangeCond`, `hcoef`.
3. Item 3. `𝔠_d := 1/100`; `HClt` at `τ = s` from the premises `STFlow`, `STStep2Concl` of `STIngR5`; `Filter.eventually_all` over the four `σ`; per `σ`: `cltStep` for
   `F = cltStep_loopForm` (`hcoef` from `cltStep_loopForm_coef_le_eventually`), `cltStep_STcltX_eq` (the centring cancels `scale·STKloop`; `cltTransfer`), `cltStep_assembly`
   (centring of `X_i`, `cltTelescope` over `card CoordF = 2N²`), `cltStep_exponent` (`2N²·N^{-D-3} ≤ W^{-D}`, `N ≥ 2`, `W ≤ N`). `STReg5I` and `σ₁ ≠ σ₂` are not used.
4. Registry and root import. The `STCltIso` line of `Test/Axioms.lean` is deleted (diff above) and the pre-check passes (exit 0). The branch alone does not pass the whole-library
   `lake build` (output above: without the root import no visible theorem proves `STCltIso`); with `import RBM3D.Evolution.CltStep` in `RBM3D.lean` it passes (exit 0). The
   hub adds that import (CLAUDE.md §3 (A) step 4) before its full build; I did not commit `RBM3D.lean` (restored: `git status --short` empty).
5. Hygiene. No new `Prop`-valued definition (so the registry scan has no new premise). Helpers are `private` or prefixed `cltStep_`; the other public names are `cltStep`,
   `stCltIso_holds`. No `sorry`/`admit`/`native_decide`/`axiom`; 12 of 12 `#print axioms` are standard.
6. Instances (section 8). `inst_cltIso (stCltIso_holds 3)` (merged `Step5Inst`); the label configuration `cltStep_szCL_witness` (window `m² > 0`, isolated; the merged
   `szCL_cltIso_witness` has window `0`); item 1 at it; `cltStep` at `szCL` with only `STStep2Concl` open, specialised at the witness for every `e`, `j`. The conclusion's type is
   inferred, not written (T2141 (d) 3: no `Idx 3 (szCL.L n) …` in statements).

### (c) Verified Mathlib names (each checked by `#check` in `names.lean`, `lake env lean`; output in the tool log)
`piFinTwoEquiv : ((i : Fin 2) → α i) ≃ α 0 × α 1`; `Fintype.sum_prod_type'`; `Fintype.sum_equiv`; `Finset.sum_eq_single`; `Finset.mul_prod_erase`; `Finset.measurable_sum`
`Real.exp_one_lt_three : exp 1 < 3`; `Real.log_two_gt_d9 : 0.6931471803 < log 2`; `Real.le_log_iff_exp_le`; `Real.rpow_le_rpow_of_nonpos`; `Real.rpow_add_one`; `Real.one_le_rpow`
`Real.rpow_le_rpow_of_exponent_le`; `Nat.le_self_pow`; `Nat.pow_le_pow_left`; `one_le_mul_of_one_le_of_one_le`; `Finset.card_insert_of_notMem`; `Equiv.sum_comp`
`MeasureTheory.integral_fun_fst`; `integral_prod_mul`; `integral_conj`; `integral_finsetSum`; `Measure.le_map_apply`; `Measure.infinitePi_map_eval`; `ae_dirac_iff`; `gaussianReal_zero_var`
`Filter.eventually_all : (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x` (`[Finite ι]`); `tendsto_atTop_mono'`; `tendsto_rpow_atTop`; `measurable_update'`
`Matrix.inv_submatrix_equiv`; `Matrix.mul_diagonal`; `ZMod.val_cast_of_lt`; `Set.mem_ofPred_eq` (replaces the deprecated `Set.mem_setOf_eq`, build warning seen).
Verified absent: `Equiv.piFinTwo` (`#check` fails: unknown identifier; the name is `piFinTwoEquiv`).

### (d) Open issues and paper-delta candidates
* O1 (hub). The registry deletion forces the root import into the same merge (narrative 4): without `import RBM3D.Evolution.CltStep` the root build fails, as pasted.
* O2. `STStep2Concl` (another gate's pin) stays a hypothesis of the `cltStep` instance; the instance is a bare `example` (type inferred, elaboration trap).
* O3. The constants `C' = 2` and `N ≥ 𝔡^{-3}` (coefficient bound) are Lean choices; the paper does not state them. The preflight numbers corrected in (a′).
* O4. `lake build` replays a pre-existing style warning `CltGood.lean:19:100` (not this ticket).
* T2152a: `(eq:bound_isolated)` (`3_5:2245-2248`) is proved in Lean by the i.i.d.-copy and coordinate-telescoping route of RBM2D (`CltFar`), not cited from [DYYY25, (7.39)],
  [RBSO1D, (A.112)]; the route and the log-scale constants (`ρ = w+1`, `R = 8w`, `θ = 3w−2`, `w = (log W)^3 ℓ_s`) are not in the paper.
* T2152b: `stCltIso_holds` holds for every `σ ∈ {±}²` (the pin has `σ 0 ≠ σ 1`) and without the regime `STReg5I`: only `STFlow` and `STStep2Concl` are used.
* T2152c: `𝗕_b` is encoded as a local form with coefficient `scale·W^{-2d}` on the monomials `G(σ₁)_{yx}G(σ₂)_{xy}` (`E_a = W^{-d}1_{[a]}`, `Loop/GLoop.lean:55`),
  vanishing outside the window `|b₁−b₂|_∞ ≤ w_n`; the paper has no local-form statement for `𝗕`.
