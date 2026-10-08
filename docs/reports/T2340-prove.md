Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 18:55:18 UTC 2026

Targets (mathematics): the assembly `STMainInd` (one step `s -> t`, paper `lem:main_ind`, `1_2:1256-1305`) + base case `t = 0` (`1_2:1240-1243`, `G_0 = M`, `L_0 = K_0`) + chain of times `1 - p_k = (1-t)^{k/K}` (`stChainSteps`) + mixing on the class `t_n = 0` give `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` at every time sequence `0 <= t_n <= lemT z_n` (`UNMLOut`; `1_2:1194-1218, 1309-1311`). Data: `d=3`, sizes `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^d`), `z_n = 1/2 + i N_n^{-4/5}` (`RBM3D/Defs/Sizes.lean:260`, `RBM3D/Induction/Defs.lean:413`). `Bctl n t = W^{-d} B_{t,0}` with `B_{t,0} = (g^2+(1-t))^{-1} + (L^d(1-t))^{-1}` (`Defs/Params.lean:36`, `Defs/Sizes.lean:214`).

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `d` | 3 | `3 <= d` (`STMainInd`, `STBaseG`, `STMLOutG` premise) | 0 (used at the minimum) |
| 2 | `kappa, eps, dd` (`𝔡`) | 1/10 each | all `> 0` | open constraint (no upper bound used) |
| 3 | `c` (`𝔠`, bandwidth) | 1/6 | `W >= N^c`; at `sz0` `W^6 >= W^3 L^3` iff `W >= L` | `W/L = 8` (`n=0`), `128` (`n=1`) |
| 4 | `(eq:WO)` with `dd=1/10` | `W^{-d/2+dd}=m^{-7} <= lam=m^{-6} <= 1/dd=10`, `m=2(n+1)` | `W^{-d/2+dd} <= lam <= 1/dd` | factor `m >= 2` below, `10/lam >= 640` above |
| 5 | `c_d` (`𝔠_d`) | 1/100 (largest allowed; the theorem's `𝔠_d` is existential, fixed before `c, sz, z`) | `0 < c_d <= 1/100` | 0 at the max; smaller `c_d` only enlarges `K` |
| 6 | `tau = eps/2` | 1/20 | horizon `N^{-1+tau} <= 1-T0` | see row 9 |
| 7 | `mu = min(2 c dd, tau)` | `min(1/30, 1/20) = 1/30` | `Bctl(u) <= 2 N^{-mu}` for `u <= T0` (`scaleFacts_R1`) | `tau - 2c dd = 1/60` |
| 8 | `K = ceil(2/(c_d mu))` | 6000 | `K c_d mu >= 2`; `K` depends on `(c_d,c,dd,eps)` only, never on `n`, `t` | 0 (`K c_d mu = 2` exactly) |
| 9 | horizon `N^{-1+eps/2} <= 1 - lemT z_n`, `0 < lemT < 1` | `1-lemT >= Im z/(1+|z|) >= N^{-4/5}/2.12` | `N^{0.15} >= 2.12` | holds iff `N >= 149`; at `n=0` (`N=2^21`): `9.05e-6` vs `9.87e-7` (x9.2) |
| 10 | locDomain `|Re z|=1/2 <= 2-kappa=1.9`, `N^{-0.9} <= Im z=N^{-0.8} <= 1` | | `1_2:380` | `1.4` in `|Re z|`; `N^{0.1}` in `Im z` |
| 11 | per-step ratio `(1-p_{k+1})/(1-p_k) = (1-t)^{1/K}` | `<1` iff `t>0` | `(con_st_ind)` `1_2:1296`: `Bctl(p_{k+1})^{c_d} <= ratio < 1` | proof chain `(2N^{-mu})^{c_d} <= N^{-1/K} <= (N^{-1+tau})^{1/K} <= (1-t)^{1/K}`: `mu c_d = 1/3000` vs `2/K=1/3000` (equal); needs `2^{c_d} <= N^{1/K}` iff `N >= 2^{c_d K} = 2^60` (sufficient only; the exact inequality at `n=0`, `t=lemT`: `0.98262 <= 0.998066`) |
| 12 | class `t_n = 0`: `t'_n = lemT z_n/2` | `1/32 <= t'_n = lemT/2 < lemT < 1` | `s_k<p_{k+1}<=t'<=lemT`, `lemT >= 1/16` (`lemma28_quant`) | `t'` is half of the allowed maximum |
| 13 | mixing: `bad_t(n) ⊆ bad_0(n) ∪ bad_{t'}(n)` | set inclusion (`t_n=0`: `t_n=0`; else `t_n=t'_n`) | no numerics | none needed |
| 14 | base case `t=0`: `Bctl(0) <= 2N^{-mu}` (`STLmax` from `ML:Kbound`) | `3.1e-5 <= 1.23` at `n=0` | | see output |

External hypotheses (carried, not proved here): `STMainInd d` / `STMainIndG` (target statements `unMLOut_of_mainInd`, `stMLOutG_of_mainIndG`), `LWterm d`, `LWtermExp d` (`stMainInd_of_LW`, `unMLOut_of_LW`), BA pins (`unMLOutBA_of_pins`). Limit computation for the chain hypothesis `(con_st_ind)` (the only one with an eventual-in-`n` quantifier used by the chain): row 11 (exponent comparison, `mu c_d = 2/K`, sufficient `N >= 2^60`) and the per-`n` numerical check below (`n=0,1,3,4,10`, `N` from `2^21` to `2^83.3`; `n=4`, `N=2^62.8`, is above `2^60`). The LW pins are statements about paper lemmas that cannot be instantiated numerically; the nonempty instance keeps them (and `STMainInd 3`) as hypotheses (CLAUDE.md §4 step 2).

### (ii) Concrete nondegenerate instance
`d=3`, `kappa=eps=dd=1/10`, `c=1/6`, `c_d=1/100`, `K=6000`, sizes `sz0`, `z_n` as above; time sequences `t = lemT z/2` (also the class `t_n=0` replaced by `t'`) and the boundary `t = lemT z`; chain checked at **all** `K=6000` steps (`p_k` strictly increasing, ratio `<1`, `Bctl(p_{k+1})^{c_d} <= ratio`). Floating point: `1-lemT` computed from `Im z |m|^2 = Im m (1-|m|^2)` (no cancellation).

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2340 && python3 -I inst.py
tau=eps/2=0.05; mu=min(2*c*dd,tau)=0.03333; K=ceil(2/(c_d*mu))=6000; K*c_d*mu=2.0000>=2:True; 2^(2/mu)=2^60
n  log2N  sz-admissible: L<=W, W>=N^c, lam>=W^(-d/2+dd), lam<=1/dd | locDomain: N^(-1+eps)<=Im z<=1 | horizon N^(-1+eps/2)<=1-lemT, 
 0   21.0 (True, True, True, True) True (True, True) 1-lemT=9.051e-06 N^(-1+eps/2)=9.873e-07
 1   39.0 (True, True, True, True) True (True, True) 1-lemT=4.187e-10 N^(-1+eps/2)=7.028e-12
 2   49.5 (True, True, True, True) True (True, True) 1-lemT=1.219e-12 N^(-1+eps/2)=6.850e-15
 3   57.0 (True, True, True, True) True (True, True) 1-lemT=1.937e-14 N^(-1+eps/2)=5.003e-17
 4   62.8 (True, True, True, True) True (True, True) 1-lemT=7.790e-16 N^(-1+eps/2)=1.102e-18
10   83.3 (True, True, True, True) True (True, True) 1-lemT=9.134e-21 N^(-1+eps/2)=1.537e-24
all deterministic hypotheses: True
analytic horizon threshold: N^0.15 >= 1+|z| (|z|<=sqrt(1.25)) iff N >= 149
chain at every one of K steps, t=lemT/2 (class t_n=0 -> t'=lemT/2) and t=lemT (boundary):
n= 0 log2N= 21.0 t=lemT/2: max_k Bctl(p_(k+1))^c_d=0.907655 <= (1-t)^(1/K)=0.999884; strict ratio<1, all 6000 steps: True
n= 0 log2N= 21.0 t=lemT: max_k Bctl(p_(k+1))^c_d=0.982620 <= (1-t)^(1/K)=0.998066; strict ratio<1, all 6000 steps: True
n= 1 log2N= 39.0 t=lemT/2: max_k Bctl(p_(k+1))^c_d=0.817918 <= (1-t)^(1/K)=0.999884; strict ratio<1, all 6000 steps: True
n= 1 log2N= 39.0 t=lemT: max_k Bctl(p_(k+1))^c_d=0.961568 <= (1-t)^(1/K)=0.996407; strict ratio<1, all 6000 steps: True
n= 3 log2N= 57.0 t=lemT/2: max_k Bctl(p_(k+1))^c_d=0.737136 <= (1-t)^(1/K)=0.999884; strict ratio<1, all 6000 steps: True
n= 3 log2N= 57.0 t=lemT: max_k Bctl(p_(k+1))^c_d=0.941096 <= (1-t)^(1/K)=0.994751; strict ratio<1, all 6000 steps: True
n= 4 log2N= 62.8 t=lemT/2: max_k Bctl(p_(k+1))^c_d=0.712871 <= (1-t)^(1/K)=0.999884; strict ratio<1, all 6000 steps: True
n= 4 log2N= 62.8 t=lemT: max_k Bctl(p_(k+1))^c_d=0.934638 <= (1-t)^(1/K)=0.994219; strict ratio<1, all 6000 steps: True
n=10 log2N= 83.3 t=lemT/2: max_k Bctl(p_(k+1))^c_d=0.633355 <= (1-t)^(1/K)=0.999884; strict ratio<1, all 6000 steps: True
n=10 log2N= 83.3 t=lemT: max_k Bctl(p_(k+1))^c_d=0.912306 <= (1-t)^(1/K)=0.992339; strict ratio<1, all 6000 steps: True
class t_n=0: Bctl(0)^c_d vs ratio at t'=lemT/2 covered above; Bctl(0) <= 2N^-mu:
0 3.099e-05 <= 1.231e+00 True
1 9.331e-10 <= 8.123e-01 True
3 2.843e-14 <= 5.359e-01 True
4 1.000e-15 <= 4.687e-01 True
10 7.306e-21 <= 2.921e-01 True
```

### Verdicts
- **R1 base (`STLK0`, `STG0M`, `stBaseG_of_init`, `stBase_band`)**: PASS. Hypotheses `3<=d`, `kappa,eps,dd>0`, `STFlow` hold at the instance (rows 1-4, 10); the conclusions at `tau = 0` are the deterministic identities `L_0 = K_0`, `G_0 = M` (`1_2:1240-1243`) plus `ML:Kbound` for `STLmax` (row 14).
- **R2 chain (`stChainSteps`, `STLocalMaxgL_of_STLocalEntrygL`, `stPosConclG_of_mainIndG`, `stHorizon_band`)**: PASS. Exponents close (rows 5-9, 11): `K c_d mu = 2`, `mu c_d = 2/K`; horizon holds at all tested `n` and analytically for `N >= 149`; the chain check passes at all 6000 steps for all tested `n`.
- **R3 output (`stMLOutG_of_mainIndG`, `unMLOut_of_mainInd`, `unMLOutBA_of_pins`, `stMainInd_of_LW`, `unMLOut_of_LW`)**: PASS. Class `t_n=0` handled by the mixing inclusion (row 13) with `t' = lemT/2 > 0` (row 12); `STMainInd` requires `s_n < t_n` for every `n`, which is why `t_n = 0` cannot start a chain. External pins (`STMainInd`, `LWterm`, `LWtermExp`, BA pins) stay hypotheses.
- No FAIL or BLOCKED item: every hypothesis set is satisfiable at the instance, the only zero-slack constants (`d=3`, `c_d=1/100`, `K c_d mu=2`) are consistent with their constraints.

## (b) Script output (stage 1b, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2340`, branch `t/T2340`, commits f3c170a, 32c6d07, f0a3277, 5d07707 on base 74cdcb9)

```
$ date -u; git rev-parse --short HEAD; git status --short | wc -l; git merge-base --is-ancestor 7154d50 HEAD && echo ancestor
Thu Oct  8 19:26:08 UTC 2026
5d07707
       0
7154d50 is an ancestor of HEAD
$ lake build RBM3D.Induction.MainIndBase 2>&1 | tail -1
Build completed successfully (3910 jobs).
$ lake build RBM3D.Induction.MainIndChain 2>&1 | tail -1
Build completed successfully (3912 jobs).
$ lake build RBM3D.Induction.MainIndOut 2>&1 | tail -1
Build completed successfully (4039 jobs).
$ lake build RBM3D.Induction.MainIndOut 2>&1 | grep -c "^(warning|error): RBM3D/Induction/MainInd(Base|Chain|Out).lean"   # warnings/errors of the three files
0
$ lake build 2>&1 | tail -3   (full library, run 19:25:56-19:25:58 UTC after commit 5d07707; the root RBM3D.lean does not import the new modules, the hub adds them at merge)
Build completed successfully (4151 jobs).
exit 0
0
$ wc -l RBM3D/Induction/MainInd{Base,Chain,Out}.lean
     164 RBM3D/Induction/MainIndBase.lean
     251 RBM3D/Induction/MainIndChain.lean
     223 RBM3D/Induction/MainIndOut.lean
     638 total
$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Induction/MainInd{Base,Chain,Out}.lean | wc -l
       0
$ git diff --stat main...t/T2340
 RBM3D/Induction/AzumaProxyN.lean  |   2 +-
 RBM3D/Induction/MainIndBase.lean  | 164 +++++++++++++++++++++++++
 RBM3D/Induction/MainIndChain.lean | 251 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/MainIndOut.lean   | 223 +++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean            |  10 ++
 5 files changed, 649 insertions(+), 1 deletion(-)
$ git diff 74cdcb9 HEAD -- RBM3D/Induction/AzumaProxyN.lean | grep "^[+-]"
--- a/RBM3D/Induction/AzumaProxyN.lean
+++ b/RBM3D/Induction/AzumaProxyN.lean
-private theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m)
+theorem azumaProxy_loopFine_sub_STKloop {E : ℝ} (hE : |E| < 2) {m : ℕ} (hm : 1 ≤ m)
```
**Axioms** (`lake env lean ax.lean`: `import RBM3D.Induction.MainIndOut` + `#print axioms` of 14 declarations: the 6 required, `stHorizon_band`, `stBaseG_of_init`, `stChainSteps`, `STLocalMaxgL_of_STLocalEntrygL`, `stPosConclG_of_mainIndG`, `unMLOut_iff`, `stChainTime_facts`, `azumaProxy_loopFine_sub_STKloop`):
```
Thu Oct  8 19:26:17 UTC 2026
declarations printed: 14; distinct axiom sets:
  14 [propext, Classical.choice, Quot.sound]
declarations: RBM.BA.stMLOutG_of_mainIndG RBM.BA.stBase_band RBM.Univ.unMLOut_of_mainInd RBM.Univ.unMLOutBA_of_pins RBM.Gauss.Sizes.stMainInd_of_LW RBM.Univ.unMLOut_of_LW RBM.BA.stHorizon_band RBM.BA.stBaseG_of_init RBM.BA.stChainSteps RBM.BA.STLocalMaxgL_of_STLocalEntrygL RBM.BA.stPosConclG_of_mainIndG RBM.Univ.unMLOut_iff RBM.BA.stChainTime_facts RBM.Ind.azumaProxy_loopFine_sub_STKloop 
```

**Check-file equality** (scratch = check file with `import RBM3D.Induction.MainIndOut` after its imports, plus the 14 lines below):
```
$ date -u; lake env lean checkeq.lean; echo "exit $?"
Thu Oct  8 19:32:55 UTC 2026
exit 0
example : @RBM.T2340Check.T2340_STConclgL = @RBM.BA.STConclgL := rfl
example : @RBM.T2340Check.T2340_STLK0 = @RBM.BA.STLK0 := rfl
example : @RBM.T2340Check.T2340_STG0M = @RBM.BA.STG0M := rfl
example : @RBM.T2340Check.T2340_STBaseG = @RBM.BA.STBaseG := rfl
example : @RBM.T2340Check.T2340_STHorizonG = @RBM.BA.STHorizonG := rfl
example : @RBM.T2340Check.T2340_STMLOutG = @RBM.BA.STMLOutG := rfl
example : @RBM.T2340Check.T2340_stChainTime = @RBM.BA.stChainTime := rfl
example : RBM.T2340Check.T2340_stBase_band := RBM.BA.stBase_band
example : RBM.T2340Check.T2340_stHorizon_band := RBM.BA.stHorizon_band
example : RBM.T2340Check.T2340_stMLOutG_of_mainIndG := RBM.BA.stMLOutG_of_mainIndG
example : RBM.T2340Check.T2340_unMLOut_of_mainInd := RBM.Univ.unMLOut_of_mainInd
example : RBM.T2340Check.T2340_unMLOutBA_of_pins := RBM.Univ.unMLOutBA_of_pins
example : RBM.T2340Check.T2340_stMainInd_of_LW := RBM.Gauss.Sizes.stMainInd_of_LW
example : RBM.T2340Check.T2340_unMLOut_of_LW := RBM.Univ.unMLOut_of_LW
```
**Target statements** (`python3 -I extract.py NAME...`: signature text of each declaration, up to `:=`; the bodies of the definitions are the check pins, equal by the `rfl` lines above):
```
def STConclgL {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
def STLK0 {sz : Sizes d} (C : FlowFM sz) : Prop :=
def STG0M {sz : Sizes d} (C : FlowFM sz) : Prop :=
def STBaseG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
def STHorizonG (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
def STMLOutG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
noncomputable def stChainTime (t : ℕ → ℝ) (K k : ℕ) : ℕ → ℝ :=
theorem stBaseG_of_init {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
    {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} (hprob : ∀ sz, IsProbabilityMeasure (law sz))
    (hL : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STLK0 (mk sz z))
    (hG : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STG0M (mk sz z))
    (hK : 3 ≤ d → ∀ κ ε 𝔠 𝔡 sz z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) : STBaseG d law Flow mk :=
theorem stChainSteps (sz : Sizes d) {𝔠 𝔡 τ 𝔠d : ℝ} (h𝔠 : 0 < 𝔠) (h𝔡 : 0 < 𝔡) (hτ : 0 < τ) (h𝔠d : 0 < 𝔠d)
    {K : ℕ} (hK : 2 ≤ (K : ℝ) * (𝔠d * min (2 * 𝔠 * 𝔡) τ)) (hB : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hsz : sz.SizeTendsto) {T : ℕ → ℝ} (hT1 : ∀ n, T n < 1)
    (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) ≤ 1 - T n)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (htT : ∀ n, t n ≤ T n) {k : ℕ} (hk : k < K) :
    sz.STConStInd 𝔠d (stChainTime t K k) (stChainTime t K (k + 1)) :=
theorem STLocalMaxgL_of_STLocalEntrygL {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ)
    (h : STLocalEntrygL C μ τ) : STLocalMaxgL C μ τ :=
theorem stPosConclG_of_mainIndG (hmain : STMainIndG d law Flow mk T0) (hhor : STHorizonG d Flow T0)
    (hbase : STBaseG d law Flow mk) :
    3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 < t n) → (∀ n, t n ≤ T0 sz z n) → STConclgL (mk sz z) (law sz) t :=
theorem stMLOutG_of_mainIndG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hmain : STMainIndG d law Flow mk T0)
    (hhor : STHorizonG d Flow T0) (hbase : STBaseG d law Flow mk) : STMLOutG d law Flow mk T0 :=
theorem stBase_band (d : ℕ) :
    STBaseG d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) :=
theorem stHorizon_band (d : ℕ) :
    STHorizonG d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun _ z n => lemT (z n)) :=
theorem unMLOut_iff (d : ℕ) : UNMLOut d ↔ STMLOutG d (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
theorem unMLOut_of_mainInd (d : ℕ) (hmain : STMainInd d) : UNMLOut d :=
theorem unMLOutBA_of_pins (d : ℕ)
    (hmain : STMainIndG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0)
    (hhor : STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0)
    (hbase : STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) :
    UNMLOutBA d :=
theorem stMainInd_of_LW (d : ℕ) (hLW : LWterm d) (hLWE : LWtermExp d) : STMainInd d :=
theorem unMLOut_of_LW (d : ℕ) (hLW : LWterm d) (hLWE : LWtermExp d) : UNMLOut d :=
```

**Compiled nonempty instances** (all inside the three files, namespace `RBM.Gauss.MainIndInst`, `d = 3`, merged data `sz0`, `z0`, `zSeq`, `flow_z0`, `flow_sz0`; they are `example`s of the build above):
```
$ grep -n "^example" RBM3D/Induction/MainInd{Base,Chain,Out}.lean | cut -c1-110
RBM3D/Induction/MainIndBase.lean:150:example : STConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 
RBM3D/Induction/MainIndBase.lean:156:example (hL : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STLK0 (ba
RBM3D/Induction/MainIndChain.lean:212:example : stChainTime (fun _ => 1 / 2) 2 0 = fun _ => 0 := stChainTime_z
RBM3D/Induction/MainIndChain.lean:214:example : stChainTime (fun _ => 1 / 2) 2 2 = fun _ => 1 / 2 := stChainTi
RBM3D/Induction/MainIndChain.lean:216:example (n : ℕ) : 0 ≤ stChainTime (fun _ => (1 / 2 : ℝ)) 2 1 n ∧
RBM3D/Induction/MainIndChain.lean:222:example : sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, 0 < lemT (z0 n) ∧ lemT
RBM3D/Induction/MainIndChain.lean:228:example : sz0.STConStInd (1 / 100) (stChainTime (fun n => lemT (z0 n) / 
RBM3D/Induction/MainIndChain.lean:238:example : STLocalMaxgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _
RBM3D/Induction/MainIndChain.lean:245:example (hmain : STMainInd 3) :
RBM3D/Induction/MainIndOut.lean:186:example (hmain : STMainInd 3) : STLKgL (bandFM sz0 (STflowE z0)) (Sizes.se
RBM3D/Induction/MainIndOut.lean:198:example (hmain : STMainInd 3) : sz0.STLK (STflowE z0) (fun n => lemT (z0 n
RBM3D/Induction/MainIndOut.lean:205:example
RBM3D/Induction/MainIndOut.lean:216:example (hLW : LWterm 3) (hLWE : LWtermExp 3) : STMainInd 3 := stMainInd_o
RBM3D/Induction/MainIndOut.lean:218:example (hLW : LWterm 3) (hLWE : LWtermExp 3) : sz0.STLK (STflowE z0) (fun
$ sed -n 228,235p RBM3D/Induction/MainIndChain.lean      # stChainSteps at K = 6000, t = lemT z0/2, step k = 5999
example : sz0.STConStInd (1 / 100) (stChainTime (fun n => lemT (z0 n) / 2) 6000 5999)
    (stChainTime (fun n => lemT (z0 n) / 2) 6000 6000) := by
  obtain ⟨⟨-, -, hsz, hbw, hWO⟩, hT, hr⟩ :=
    stHorizon_band 3 (1 / 10) (1 / 10) (1 / 6) (1 / 10) sz0 z0 (by norm_num) (by norm_num) flow_z0
  exact stChainSteps sz0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (K := 6000)
    (by norm_num [min_def]) hbw hWO hsz (fun n => (hT n).2) hr (fun n => half_pos (hT n).1)
    (fun n => by linarith [(hT n).1]) (by norm_num)

$ sed -n 198,201p RBM3D/Induction/MainIndOut.lean       # unMLOut_of_mainInd at sz0, z0, t = lemT z0/2
example (hmain : STMainInd 3) : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2) :=
  (RBM.Univ.unMLOut_of_mainInd 3 hmain (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num)
    (by norm_num) sz0 z0 flow_z0 _ (fun n => (half_pos (lemT_pos (z0_im_pos n))).le)
    (fun n => by linarith [lemT_pos (z0_im_pos n)])).1
```
Hypotheses left in the examples (other gates pins): `STMainInd 3` (lem:main_ind, owed by LW-01 via R4), `LWterm 3`, `LWtermExp 3`, the three BA pins at BA data, the three BA carrier facts `hL hG hK` of `stBaseG_of_init` at BA data (BA-V).  Every other premise is discharged at the concrete data; `t = 0` in the first `stMLOutG_of_mainIndG` example is the class `t_n = 0` handled by the mixing.
**Name-clash grep** (24 new names: the 6 defs, `stChainTime`, `_zero`, `_top`, `_facts`, `stChainSteps`, `STLocalMaxgL_of_STLocalEntrygL`, `stPosConclG_of_mainIndG`, `stMLOutG_of_mainIndG`, `stBaseG_of_init`, `stBase_band`, `stHorizon_band`, `mainIndBase_bctl_nonneg`, `unMLOut_iff`, `unMLOut_of_mainInd`, `unMLOutBA_of_pins`, `stMainInd_of_LW`, `unMLOut_of_LW`, `MainIndInst`):
```
$ for n in <24 names>; do grep -rwn $n RBM3D RBM3D.lean | grep -v "MainInd(Base|Chain|Out).lean|Probe/|Test/Axioms" ; done   # worktree HEAD 5d07707, then main 84cd789 by git grep
Thu Oct  8 19:33:03 UTC 2026
names checked:       24
worktree: total hits outside the new files = 0
main 84cd789: total hits = 0
$ grep -rn azumaProxy_loopFine_sub_STKloop RBM3D | grep -v "Induction/AzumaProxyN.lean|Induction/MainIndBase.lean|Test/Axioms.lean" | wc -l   # clash for the de-privatised name
       0
```
**Registry pre-check** (temporary uncommitted scratch file `reg.lean` = `import RBM3D` / `import RBM3D.Induction.MainIndOut` / `#assert_rbm_axioms`):
```
$ date -u; lake env lean reg.lean > reg.out; echo "exit $?"
Thu Oct  8 19:33:13 UTC 2026
exit 0
axiom audit: 10251 theorems, 3044 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
52:  RBM.BA.STLK0: 1 [no certificate]
53:  RBM.BA.STG0M: 1 [no certificate]
54:  RBM.BA.STBaseG: 5 [no certificate]
55:  RBM.BA.STHorizonG: 4 [no certificate]
56:  RBM.BA.STMainIndG: 4 [no certificate]
57:  RBM.BA.STLocalEntrygL: 4 [no certificate]
registry: 2 borrowed + 132 owed + 108 structural + 7 refuted + 14 superseded; 123 registered premise(s) carry 
```
**Port citation** (idea of `chainTime` only, no RBM2D text copied): `git -C ../../RBM2D --no-optional-locks log -1 --format=%h` gives 9e0f275 (HEAD); cited commit c9a24cf:
```
def chainTime (t : ℕ → ℝ) (n₀ k : ℕ) (n : ℕ) : ℝ :=
  1 - (1 - t n) ^ ((k : ℝ) / n₀)
```

**Narrative.**
1. Three new files, `MainIndBase`/`MainIndChain`/`MainIndOut` (R1/R2/R3), 164/251/223 = 638 lines (ticket sizes 650/900/1100; stop rule 1200 not reached: `wc -l` totals at the section commits were 509 at f3c170a, 632 at 32c6d07 and f0a3277, 638 at 5d07707), the one-token edit at `AzumaProxyN.lean:597` and 10 lines in `Test/Axioms.lean`. Nothing else is touched (`git diff --stat` above).
2. Source: probe `RBM3D/Probe/T2338Pins.lean` at 854aa29 (read with `git show t/T2338:...`): probe 42-59, 81-139, 344-355 -> R1; 61-67, 78-79, 175-254, 262-287, 319-336 -> R2; 69-76, 140-174, 289-313, 357-380 -> R3; instances 382-392 -> R2/R3. The proof text is moved unchanged except for the points in item 3.
3. Differences from the probe: (i) `stBase_band` has no hypothesis: the probe's `hpriv : STLoopZeroId d` is replaced by `azumaProxy_loopFine_sub_STKloop sz n hE hk σ a` (public after the edit); `STLoopZeroId` is not a library definition. (ii) The target binders are explicit as in the check pins (`d law Flow mk T0` for `stMLOutG_of_mainIndG`, `d` for the six band/BA/LW targets), which the `example : T2340_t := name` lines need. (iii) `stMainInd_of_LW` is the probe example 373-380 as a theorem, with `stDuhamelII_holds d` instead of the hypothesis `STDuhamelII d` (merged by T2339). (iv) CLAUDE.md §3 (E): the zero lemmas, `precL_of_zero` and the five mixing lemmas are `private`; the one shared helper is public as `mainIndBase_bctl_nonneg`.
4. Instances: the first `stMLOutG_of_mainIndG` example is at `t ≡ 0` (the class `t_n = 0` that the mixing handles, `t'_n = lemT z_n/2`); the others are at `t = lemT z0/2`, the chain step `k = 5999` of `K = 6000` (`stChainSteps`), the band base case and horizon at `sz0`, `z0`, and the BA data `sz0`, `zSeq` (`flow_sz0`, `t0_sz0`, merged in `BA/FlowPins.lean`). The examples keep only other gates' pins as hypotheses (list above the name-clash block); no `N = 0`, empty index set or `False` premise.
5. Imports: each file imports what it uses. By single-drop compile tests, then greedy, the following imports were transitive and are not repeated: `Loop.KLFinal` (R1), `Induction.ScaleFacts` and `Induction.Step2Iterate` (R2), `Universality.Pins` (R3). From the check list, R3 does not repeat `DuhamelI` (line 6 of `DuhamelII.lean` imports it) nor `AzumaProxyN` (R3 gets it through `MainIndBase`), and does not import `Main.FixedZ` (no name used). Imports run one way R1 -> R2 -> R3, never `RBM3D`.
6. Registry: the pre-check first FAILED (run 19:08:57 UTC, `lake env lean reg.lean`, exit 1): `axiom audit: 2 premise(s) that no theorem of this development proves are in none of ...: [RBM.BA.STMainIndG, RBM.BA.STLocalEntrygL]` (hypotheses of `stMLOutG_of_mainIndG` and `STLocalMaxgL_of_STLocalEntrygL`). I classified both as owed (like `STMainInd`, `STLocalEntry`): 10 lines are added to `Test/Axioms.lean` (the ticket's 6 classes, these 2 names, 2 comment lines); the pre-check exits 0 afterwards. This goes beyond the six names of the ticket and needs the dispatcher's sign-off (d.1).
7. Ticket preflight: (i) the moved text compiles on 74cdcb9 (7154d50 is an ancestor; T2336, T2339 merged); the probe file itself was not rebuilt. (ii) name-clash grep above: 0; the diff is the one keyword, the private lemmas of its proof stay private. (iii) split and sizes: above. (iv) §29, one line each: (1) time domain: `stChainTime_facts` needs `0 < t < 1`, given by `0 < t_n ≤ T0 < 1` (`STHorizonG`); `t_n = 0` goes only through `STBaseG` and the mixing, never through `STMainInd`. (2) the case-(ii) boundary `1 - ilambda²/L²`: not used, the regimes are inside `STMainInd`. (3) `L^d ≤ W^K`: not used by the new files; `STHorizonG` takes `sz.Admissible 𝔠 𝔡` and `stChainSteps` reads exactly `0 < 𝔠`, `SizeTendsto`, `Bandwidth 𝔠`, `WO 𝔡` from it. (4) `∀ n` vs `∀ᶠ n`: `(con_st_ind)` and the horizon are `∀ᶠ n` (`stChainSteps`, `stHorizon_band` use `filter_upwards`); `STLK0`, `STG0M`, `0 < T0 < 1` are `∀ n` and hold at every `n` for the band.
8. Not claimed: `STMainInd` is not proved here (owed, R4 after LW-01); `unMLOut_of_mainInd` is `STMainInd d -> UNMLOut d`, `unMLOut_of_LW` is conditional on `LWterm`, `LWtermExp`, and `unMLOutBA_of_pins` on three BA pins that nothing here proves. Section (a) is not edited and needs no (a′): `stHorizon_band` proves `N^{ε/2} ≥ 4` eventually (`N ≥ 2^40` at `ε = 1/10`, cruder than the `N ≥ 149` of row 9 of (a); both are eventual statements, and the Lean statement needs no threshold).

## (c) Verified Mathlib names

```
$ date -u; lake env lean mnames.lean   # `import RBM3D.Induction.MainIndOut`; `env.contains` of 47 names
Thu Oct  8 19:34:12 UTC 2026
present: 47; absent: []
```
Names checked (all present): `Real.rpow_nonneg`, `Real.exp_pos`, `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_sub`, `Real.rpow_lt_one`, `Real.rpow_le_one`, `Real.rpow_lt_rpow_of_exponent_gt`, `Real.self_le_rpow_of_le_one`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_natCast`, `Real.sqrt_eq_rpow`, `Real.sq_sqrt`, `Real.rpow_pos_of_pos`, `pow_lt_pow_left₀`, `pow_nonneg`, `mul_pow`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `div_le_div_of_nonneg_left`, `div_lt_div_of_pos_right`, `div_le_one`, `div_le_iff₀`, `div_self`, `div_nonneg`, `exists_nat_ge`, `tendsto_rpow_atTop`, `tendsto_natCast_atTop_iff`, `Filter.Tendsto.eventually_ge_atTop`, `Filter.Eventually.of_forall`, `Complex.norm_le_abs_re_add_abs_im`, `MeasureTheory.integral_const`, `Nat.cast_ne_zero`, `Nat.pos_of_ne_zero`, `Nat.cast_nonneg`, `half_pos`, `lt_min`, `sub_eq_zero`, `abs_of_pos`, `lt_of_le_of_ne`, `Set.mem_empty_iff_false`, `mul_pos`, `zero_lt_one`, `MeasureTheory.IsProbabilityMeasure`. Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates

1. **Registry sign-off.** Beyond the ticket's six classes, `RBM.BA.STMainIndG` and `RBM.BA.STLocalEntrygL` are now in `owedProps` (item 6 of the narrative): the pre-check fails without a class for them once `MainIndOut` is imported. Owed vs structural is the dispatcher's call; the hub's full `lake build` at merge runs the same check.
2. `STBaseG` and `STHorizonG` are in `owedProps` as the ticket says, but the scan lists them (and `STConclgL`, `STMLOutG`) under "registered premise(s) carry nothing yet" (`reg.out` lines 166-167, 242-243). By the rule of `scanPremises` (`Test/Axioms.lean`: a premise is found if some theorem assumes it and no theorem concludes it) the public `stBase_band`, `stHorizon_band` (conclusion heads `STBaseG`, `STHorizonG`) explain this; the BA instances of the two pins stay owed to BA-V and are not visible in the scan. `STLK0`, `STG0M` are found (assumed by `stBaseG_of_init`).
3. `main` moved to 84cd789 (T2342: merge LW-16 `Graph/LWTermExpN`) after the branch base; `git diff --stat 74cdcb9 main -- RBM3D RBM3D.lean` lists only `RBM3D.lean` and `RBM3D/Graph/LWTermExpN.lean`, so `Test/Axioms.lean` and `AzumaProxyN.lean` do not conflict. `stMainInd_of_LW` keeps the pinned hypothesis `LWtermExp d`; whether LW-16 changes what R4 needs is for the dispatcher.
4. Paper-delta candidates: `T2338a`-`T2338d` carried unchanged (uniform grid chain instead of the paper's two phases; `lem:main_ind` needs `s < t` so `t = 0` is the base case; "uniformly in `t`" read per time sequence; the base case needs `ML:Kbound`). No new candidate `T2340a`.
