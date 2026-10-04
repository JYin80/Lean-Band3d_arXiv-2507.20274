# T2134 portmap (ST-D4, Step 5 of `lem:main_ind`): inventory, pins, exponent tokens, routes, split, registry, instances, findings, scripts
Written Sun Oct  4 15:23:18 UTC 2026 (`date -u`).  Probe `RBM3D/Probe/T2134Pins.lean` on branch `t/T2134`, commit `36fbd3c`, base `3389d24` (T2130), 2061 lines.  Companion of `docs/reports/T2134-prove.md` (section (b) points here as P.1-P.9).  All outputs below are verbatim from `final_run.sh` (P.9); RBM2D is read at `c9a24cf` (T2002 O1), kept lines at `0c1330a`; main is read at `250a118` (a clean `git archive`; T2131-T2133 and T2135 merged after the branch base).

## P.1 Inventory (item 1)
### P.1a the 17 ST-4 files of the T2002 rule (`mkportmap.py` GROUPS: `Evolution/*` minus `Step61`, `MLExp*`), the 3 `Path/LemDecCalE*` files moved from ST-2 by DECISIONS §28, and `Induction/Step45` (d = 2 Step 5)
`python3 inv4.py` (columns: lines at `c9a24cf`, kept lines at `0c1330a`, class, exponent tokens recomputed with the portmap regexes, #public/#private declarations, public names referenced by ST-5/ST-6 files)
```
ST-4 files (rule of mkportmap.py): 17; lines 16772; kept 15101; classes {'b': 17}
moved/reference files: Path/LemDecCalE.lean 1258/857/b; Path/LemDecCalEdif.lean 1691/1664/b; Path/LemDecCalEwG.lean 1402/1385/b; Induction/Step45.lean 1445/1318/b
--- table (file | lines | kept | class | tokens | #pub/#priv | consumed by ST-5/ST-6 (script)):
Evolution/Bridge | 461 | 425 | b | 11 | 8/11 | precMono:370→6; sumDecayDetPrec:413→5/6; sumDecayCase5Prec:418→6
Evolution/Case3 | 4275 | 3828 | b | 68 | 3/221 | sumDecayCase3Prec:3861→6
Evolution/Case3Defs | 182 | 147 | b | 0 | 8/0 | cCase3:121→6; UpstreamSteps34Prec:145→6
Evolution/Case4 | 1891 | 1732 | b | 72 | 10/75 | -
Evolution/Case5 | 1562 | 1439 | b | 63 | 6/74 | -
Evolution/CltDecorrelation | 403 | 392 | b | 4 | 6/12 | -
Evolution/CltGood | 697 | 615 | b | 14 | 7/20 | -
Evolution/CltMoments | 2281 | 2094 | b | 3 | 10/82 | -
Evolution/CltPath | 320 | 283 | b | 0 | 5/13 | -
Evolution/CltResolvent | 977 | 728 | b | 16 | 20/41 | -
Evolution/CltStep | 737 | 730 | b | 1 | 4/17 | -
Evolution/CltSwap | 385 | 329 | b | 3 | 20/5 | -
Evolution/Defs | 219 | 145 | b | 6 | 13/1 | ratioR:33→5; cPrec:55→5/6; oneLoopExpErr:109→5; expLoopErr:115→5/6; Step61Concl:120→5/6; DecayLoopPT:127→5/6; MLExpConcl:138→5/6
Evolution/FarEntry | 895 | 817 | b | 19 | 6/24 | -
Evolution/KernelExpand | 612 | 581 | b | 19 | 14/11 | -
Evolution/LatticeSums | 92 | 82 | b | 0 | 2/2 | -
Evolution/XiBounds | 783 | 734 | b | 32 | 13/25 | xiMat:66→5; cProp5:71→5; cShortRow:74→5; xiRowBoundShort:509→5
Path/LemDecCalE | 1258 | 857 | b | 110 | 26/28 | -
Path/LemDecCalEdif | 1691 | 1664 | b | 81 | 2/63 | -
Path/LemDecCalEwG | 1402 | 1385 | b | 80 | 2/43 | -
Induction/Step45 | 1445 | 1318 | b | 5 | 4/57 | step4:1188→6; step5:1258→6
```
### P.1b where each file stands for d >= 3 (`python3 map4.py`; `[ok]` = the named string occurs in the named RBM3D file of main)
```
RBM2D file (c9a24cf)         lines  kept  tok group         disposition (check)
Evolution/Bridge               461   425   11 sum_decay     d=2 bridges D1-D3 -> contract pins: d>=3 counterpart merged, EK-6 `Evolution/Prec.lean` (scale N) [ok]
Evolution/Case3               4275  3828   68 sum_decay     d=2 `sum_res_3` + `clt-lemma` (7:100, 7:363-418): no d>=3 counterpart (paper has no `sum_res_3`) [`sum_res_3` in 0 paper files]
Evolution/Case3Defs            182   147    0 sum_decay     d=2 vocabulary of Case 3 / `clt-lemma` (`CltCase1Prec`, `CltCase2Prec`): not needed [absent in RBM3D]
Evolution/Case4               1891  1732   72 sum_decay     d=2 alternating sigma, sum-zero: d>=3 counterpart merged, EK-4 `Evolution/SumDecayZero.lean` [ok]
Evolution/Case5               1562  1439   63 sum_decay     d=2 `2k`-kernel (`eq:double_sum_zero_tensor`, 7:119): no d>=3 counterpart [`double_sum_zero` in 0 paper files]
Evolution/Defs                 219   145    6 sum_decay     vocabulary: `DecayLoopPT` -> merged S3-07a/b `Induction/DecayLoop{A,B}.lean`; Step-6 `MLExpConcl` etc. -> ST-5 [ok]
Evolution/KernelExpand         612   581   19 sum_decay     anchored window bound: merged EK-3 `Evolution/SumDecay.lean` `ek_anchor_sum_le` (independent proof) [ok]
Evolution/LatticeSums           92    82    0 sum_decay     d=2 mixed lattice sum: replaced by merged `(eq:latticesum_d3)` `Kernel/SumDecay.lean` [ok]
Evolution/XiBounds             783   734   32 sum_decay     kernel `Xi` bounds: merged EK-2 `Evolution/XiPins.lean` [ok]
Evolution/CltSwap              385   329    3 CLT           source of S5-17 (replacement of one real coordinate)
Evolution/CltPath              320   283    0 CLT           source of S5-17 (resolvent path)
Evolution/CltResolvent         977   728   16 CLT           source of S5-18 (resolvent expansion)
Evolution/FarEntry             895   817   19 CLT           source of S5-19 (entry bounds of the far decorrelation)
Evolution/CltGood              697   615   14 CLT           source of S5-20 (good event)
Evolution/CltStep              737   730    1 CLT           source of S5-21 (per-step bound)
Evolution/CltDecorrelation     403   392    4 CLT           source of S5-21 (`CltFarThm` = (eq:bound_isolated))
Evolution/CltMoments          2281  2094    3 CLT           partial source of S5-23/S5-24 (moment counting, d=2 balls)
Path/LemDecCalE               1258   857  110 lem_dec_calE  source of S5-05 (= T2039 ST2-36, moved to ST-4 by DECISIONS 28)
Path/LemDecCalEdif            1691  1664   81 lem_dec_calE  source of S5-06, S5-07 (= ST2-37, ST2-38)
Path/LemDecCalEwG             1402  1385   80 lem_dec_calE  source of S5-08 (= ST2-39)
Induction/Step45              1445  1318    5 Step 5 d=2    d=2 Step 5 = Step 4 at k=2 + (53): replaced by `stStep5IV_holds` (case (iv)) and cases (i)-(iii)
-- per group (files, lines, kept): {'sum_decay': (9, 10077, 9113), 'CLT': (8, 6695, 5988), 'lem_dec_calE': (3, 4351, 3906), 'Step 5 d=2': (1, 1445, 1318)}
-- the 17 ST-4 files (T2002 rule): files 17 lines 16772 kept 15101
```
Reading: of the 17 ST-4 files (15101 kept lines) the 9 `sum_decay` rows are the RBM2D forms of `lem:sum_decay` (P7c, `7_Evolution_kernel_estimates.tex`); their d >= 3 counterpart is the merged EK gate (EK-2 `Evolution/XiPins`, EK-3 `SumDecay`, EK-4 `SumDecayZero`, EK-5 `Nonzero`, EK-6 `Prec`, `Kernel/SumDecay`) or does not exist (`sum_res_3` and the double-sum-zero tensor occur in no file of the d >= 3 paper).  The sources of Step 5 are the 8 CLT rows (S5-17..S5-24) and the 3 `LemDecCalE*` rows (S5-05..S5-08 = T2039 ST2-36..39).

## P.2 The pins (item 2)
### P.2a the 18 pins: line, first paper cite of the docstring, registry class, proof ticket, compiled consumers and instance (`python3 pins.py`)
```
 line pin            paper        class     ticket         compiled consumers (skeleton/bridge theorems) | instance
L463  STStep5I       1_2:1379-1388 owed      S5-02          ST_step5_caseI_of_pins | inst_step5I
L466  STStep5II      1_2:1379-1388 owed      S5-03          ST_step5_caseII_of_pins | inst_step5II
L468  STStep5III     1_2:1379-1388 owed      S5-03          ST_step5_caseIII_of_pf | inst_step5III
L470  STStep5IV      1_2:1379-1388 proved    S5-02          stStep5IV_holds | inst_step5IV
L473  STStep5        3_5:1939     owed      S5-29          - | inst_step5
L285  STEtermsMid    3_5:1968-1979 owed      S5-13          ST_step5_caseI_of_pins ST_step5_caseII_of_pins | inst_etermsMid inst_skeletonI inst_skeletonII
L327  STDuhamelI     3_5:2067     owed      S5-15          ST_step5_caseI_of_pins | inst_duhamelI inst_skeletonI
L332  STIniTermI     3_5:2072     owed      S5-16          ST_step5_caseI_of_pins | inst_iniTermI inst_skeletonI
L408  STCltFar       3_5:2173-2176 owed      S5-25          - | inst_cltFar
L438  STCltIso       3_5:2245     borrowed  S5-17..S5-21   - | inst_cltIso
L453  STExpInv       3_5:2196-2200 owed      S5-22          - | inst_expInv
L337  STDuhamelII    3_5:2263-2277 owed      S5-15,S5-26    ST_step5_caseII_of_pins | inst_duhamelII inst_skeletonII
L343  STIniTermII    3_5:2275-2281 owed      S5-27          ST_step5_caseII_of_pins | inst_iniTermII inst_skeletonII
L358  STWardII       3_5:2257-2262 owed      S5-28          ST_step5_caseII_of_pins | inst_wardII inst_skeletonII
L133  STTailtoTail   3_5:2344-2362 owed      S5-04          - | inst_tailtoTail
L203  STLemDecCalE   3_5:2314     borrowed  S5-05..S5-09   - | inst_lemDecCalE
L221  STPfStep5      3_5:2380     borrowed  S5-10,S5-11    ST_step5_caseIII_of_pf | inst_pfStep5 inst_skeletonIII
L257  STNewKLKL      3_5:628-651  owed      S5-12          - | inst_newKLKL
-- 18 pins; namespaces: ['Sizes']
```
### P.2b statements, extracted from the probe by script (`python3 statements.py <names>`; docstrings stripped; the docstrings carry the paper cites and the registry class)
```lean
-- L56 RBM.Gauss.Sizes.STReg5I
def STReg5I {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∧ 1 - s n ≤ sz.lam n ^ 2
-- L60 RBM.Gauss.Sizes.STReg5II
def STReg5II {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n ∧
    1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2
-- L66 RBM.Gauss.Sizes.STReg5Mid
def STReg5Mid {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n ∧ 1 - s n ≤ sz.lam n ^ 2
-- L70 RBM.Gauss.Sizes.STReg5III
def STReg5III {d : ℕ} (sz : Sizes d) (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 ≤ 1 - t n
-- L75 RBM.Gauss.Sizes.STReg5IV
def STReg5IV {d : ℕ} (sz : Sizes d) (s _t : ℕ → ℝ) : Prop :=
  ∀ n, 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d
-- L42 RBM.tailTD
def tailTD (d : ℕ) (W u D r : ℝ) : ℝ :=
  ((W ^ d * |1 - u|)⁻¹) ^ 2 * Real.exp (-Real.sqrt r) + W ^ (-D)
-- L81 RBM.Gauss.Sizes.STDecayStrongU
def STDecayStrongU (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖Lloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - STKloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1.1 : ℝ)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2.2 0 - p.1.2.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))
-- L94 RBM.Gauss.Sizes.STIngR5
def STIngR5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STDecayStrong sz (STflowE z) s →
          STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t →
            Concl sz (STflowE z) s t
-- L109 RBM.Gauss.Sizes.STStep5Concl
def STStep5Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  STGdecayW sz E s t 0 ∧ STDecayStrongU sz E s t
-- L113 RBM.Gauss.Sizes.STStep5R
def STStep5R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR5 d R (fun sz E s t => STStep5Concl sz E s t)
-- L463 RBM.Gauss.Sizes.STStep5I
def STStep5I (d : ℕ) : Prop := STStep5R d STReg5I
-- L466 RBM.Gauss.Sizes.STStep5II
def STStep5II (d : ℕ) : Prop := STStep5R d STReg5II
-- L468 RBM.Gauss.Sizes.STStep5III
def STStep5III (d : ℕ) : Prop := STStep5R d STReg5III
-- L470 RBM.Gauss.Sizes.STStep5IV
def STStep5IV (d : ℕ) : Prop := STStep5R d STReg5IV
-- L473 RBM.Gauss.Sizes.STStep5
def STStep5 (d : ℕ) : Prop := STStep5R d STAny
-- L133 RBM.Gauss.Sizes.STTailtoTail
def STTailtoTail (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (_hL : 3 ≤ L) (g W D s t : ℝ), 0 < g → 0 < W → 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin 2 → Bool, ∀ A : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) →
        haveI : NeZero L := ⟨by omega⟩
        ∀ a, ‖UN d L g (EKsgn m σ) s t A a‖ ≤
          C * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D)
-- L173 RBM.Gauss.Sizes.STLemDecCalEConcl
def STLemDecCalEConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ Jst : ℕ → ℝ → ℝ → ℝ, (∀ n u D, 1 ≤ Jst n u D) →
    ∀ D : ℝ, 0 < D → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
        (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2) →
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ * Jst n (p.1 : ℝ) D ^ 2 *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (p.1 : ℝ) D ^ (3 / 2 : ℝ)) *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      Prec sz
        (U := fun n => {q : STIdx2 sz s t n × (Fin 2 → Zd d (sz.L n)) //
          ∀ i : Fin 2, ((zdistInf d (sz.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)})
        (fun n q ω => ‖STee sz n (E n) (q.1.1.1 : ℝ) ω q.1.1.2.1 q.1.1.2.2 q.1.2‖)
        (fun n q _ => (1 - (q.1.1.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (q.1.1.2.2 0 - q.1.1.2.2 1) : ℕ) : ℝ) ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (q.1.1.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (q.1.1.1 : ℝ) D ^ (3 : ℝ)) *
          STtailTD sz n (q.1.1.1 : ℝ) D q.1.1.2.2 ^ 2)
-- L203 RBM.Gauss.Sizes.STLemDecCalE
def STLemDecCalE (d : ℕ) : Prop := STIngR5 d STReg5III (fun sz E s t => STLemDecCalEConcl sz E s t)
-- L212 RBM.Gauss.Sizes.STPfConcl
def STPfConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => STLK2 sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1.1 : ℝ) D p.1.2.2)
-- L221 RBM.Gauss.Sizes.STPfStep5
def STPfStep5 (d : ℕ) : Prop := STIngR5 d STReg5III (fun sz E s t => STPfConcl sz E s t)
-- L245 RBM.Gauss.Sizes.STNewKLKLAt
def STNewKLKLAt (d : ℕ) (κ 𝔡 C δ₀ : ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLKM sz n E u H σ a‖ ≤
          C / (1 - u) * (STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H ^ 2 *
              STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
            STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D))
-- L257 RBM.Gauss.Sizes.STNewKLKL
def STNewKLKL (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKLAt d κ 𝔡 C δ₀
-- L269 RBM.Gauss.Sizes.STEtermsMidConcl
def STEtermsMidConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := STIdx2 sz s t)
      (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    Prec sz (U := STIdx2 sz s t)
      (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    Prec sz (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEk sz n (E n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2)
-- L285 RBM.Gauss.Sizes.STEtermsMid
def STEtermsMid (d : ℕ) : Prop := STIngR5 d STReg5Mid (fun sz E s t => STEtermsMidConcl sz E s t)
-- L290 RBM.Gauss.Sizes.STIniTermConcl
def STIniTermConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
-- L307 RBM.Gauss.Sizes.STDuhamelConcl
def STDuhamelConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (fun a' => STLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 a') p.2.2‖)
      (fun n p _ => F n p + (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
-- L327 RBM.Gauss.Sizes.STDuhamelI
def STDuhamelI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t)
-- L332 RBM.Gauss.Sizes.STIniTermI
def STIniTermI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t)
-- L337 RBM.Gauss.Sizes.STDuhamelII
def STDuhamelII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t => STEtermsMidConcl sz E s t →
    STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t)
-- L343 RBM.Gauss.Sizes.STIniTermII
def STIniTermII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t =>
    STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)
-- L350 RBM.Gauss.Sizes.STWardIIConcl
def STWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigMixed s t)
    (fun n p ω => ‖STLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 p.2.2 -
      zeroModeSet d (sz.L n) {0}
        (fun a' => STLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 a') p.2.2‖)
    (fun n p _ => (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT (E n) (p.1 : ℝ))⁻¹)
-- L358 RBM.Gauss.Sizes.STWardII
def STWardII (d : ℕ) : Prop := STIngR5 d STReg5II (fun sz E s t => STWardIIConcl sz E s t)
-- L374 RBM.Gauss.Sizes.STfFar
def STfFar (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ : Zd d (sz.L n),
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
        STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1))
-- L397 RBM.Gauss.Sizes.STCltFarConcl
def STCltFarConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
      Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)})
    (fun n p ω => ‖STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω‖)
    (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) / (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1))
-- L408 RBM.Gauss.Sizes.STCltFar
def STCltFar (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STCltFarConcl sz E s t)
-- L411 RBM.Gauss.Sizes.STcltB
def STcltB (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) : ℝ) : ℂ) *
    STLKM sz n E s (sz.seqHflow n s ω) σ b
-- L416 RBM.Gauss.Sizes.STcltX
def STcltX (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (cj : Bool) (ω : sz.SeqΩ) : ℂ :=
  if cj then (starRingEnd ℂ) (STcltB sz n E s σ b ω - ∫ ω', STcltB sz n E s σ b ω' ∂(sz.seqP))
  else STcltB sz n E s σ b ω - ∫ ω', STcltB sz n E s σ b ω' ∂(sz.seqP)
-- L427 RBM.Gauss.Sizes.STCltIsoConcl
def STCltIsoConcl (E s _t : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
    ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
      (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n)) →
      (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
        ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p), STcltX sz n (E n) (s n) σ (b k) (decide (p ≤ k.val)) ω ∂(sz.seqP)‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D)
-- L438 RBM.Gauss.Sizes.STCltIso
def STCltIso (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STCltIsoConcl sz E s t)
-- L453 RBM.Gauss.Sizes.STExpInv
def STExpInv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
      (∫ ω, Lloop sz n E u σ (fun i => a i + c) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) ∧
      (∫ ω, Lloop sz n E u σ (fun i => -a i) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP))
-- L523 RBM.Gauss.Sizes.ST_step5_assembly
theorem ST_step5_assembly {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STStep5Concl sz E s t) :
    STDecay sz E t ∧ STDecayStrong sz E t :=
-- L1001 RBM.Gauss.Sizes.stStep5IV_holds
theorem stStep5IV_holds (d : ℕ) : STStep5IV d :=
-- L744 RBM.Gauss.Sizes.ST_step5_caseI_of_pins
theorem ST_step5_caseI_of_pins (hE : STEtermsMid d) (hD : STDuhamelI d) (hI : STIniTermI d) : STStep5I d :=
-- L1546 RBM.Gauss.Sizes.ST_step5_caseII_of_pins
theorem ST_step5_caseII_of_pins (hE : STEtermsMid d) (hD : STDuhamelII d) (hI : STIniTermII d) (hWd : STWardII d) :
    STStep5II d :=
-- L1315 RBM.Gauss.Sizes.ST_step5_caseIII_of_pf
theorem ST_step5_caseIII_of_pf (hPf : STPfStep5 d) : STStep5III d :=
-- L659 RBM.Gauss.Sizes.st5_compare_I
theorem st5_compare_I (n : ℕ) (hlam : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) {u D : ℝ} (hu : u < 1)
    (hx : 1 - u ≤ sz.lam n ^ 2) (a : Fin 2 → Zd d (sz.L n)) :
    ((STAI sz n) ^ (-(1 / 5) : ℝ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) +
        (STAI sz n) ^ (-(1 / 5) : ℝ) * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
      4 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
-- L896 RBM.Gauss.Sizes.st5_compare_IV
theorem st5_compare_IV (n : ℕ) (hlam : 0 < sz.lam n) (hd : 2 ≤ d) {u D : ℝ} (hu : u < 1)
    (hΔ : sz.Bctl n u ≤ 1) (hx : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) (a : Fin 2 → Zd d (sz.L n)) :
    (sz.Bctl n u) ^ 2 ≤ 6 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
-- L1150 RBM.Gauss.Sizes.st5_compare_IIIa
theorem st5_compare_IIIa (n : ℕ) {u D : ℝ} (hu : u < 1) (hx : sz.lam n ^ 2 ≤ 1 - u) (a : Fin 2 → Zd d (sz.L n)) :
    STtailTD sz n u D a ≤
      4 * ((sz.Bctl n u) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
-- L1179 RBM.Gauss.Sizes.st5_compare_IIIb
theorem st5_compare_IIIb (n : ℕ) {u D : ℝ} (hD : 0 < D) (hu : u < 1) (hx : sz.lam n ^ 2 ≤ 1 - u)
    (hy1 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ 1)
    (hcond : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ^ (1 / 5 : ℝ)) ^ 4 *
      ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) ≤ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STtailTD sz n u D a ≤
      4 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) :=
-- L1442 RBM.Gauss.Sizes.st5_compare_IIward
theorem st5_compare_IIward (n : ℕ) (hlam : 0 < sz.lam n) (hA1 : 1 ≤ STAI sz n) {u E : ℝ} (hu : u < 1)
    (hx : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) {c : ℝ} (hc : 0 < c) (hIm : c ≤ (mE E).im)
    (a : Fin 2 → Zd d (sz.L n)) :
    (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT E u)⁻¹ ≤
      (6 / c) * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) :=
```

## P.3 Exponent table (item 3)
The table with the d = 3 values per case is section (a) of the prove report (rows: `ρ` window, `A`, case-(i) amplitude, `ρ`-losses, Step-2 inputs, initial term, CLT counting and gain, `(eq:assmtlarge)`, `(eq:ells_to_ellt)`, case (ii) zero mode and Ward term, case (iv), case (iii) amplitude, strong versus weak estimate, `tailtoTail`, closure in `ε`).  The d = 2 tokens that each row replaces (`python3 tokens2.py`: `file:line: text <- what it is and its d >= 3 replacement`; the script asserts that every regex matches):
```
Path/Scales.lean:38: def etaT (E u : ℝ) : ℝ := (1 - u) * (spectralM E).im  <-  eta_u = (1-u) Im m (same in d>=3, loop.etaT)
Path/Scales.lean:41: def ellT (L : ℕ) (u : ℝ) : ℝ := min (1 / Real.sqrt (1 - u)) (L : ℝ)  <-  ell_u = min((1-u)^{-1/2}, L): no g (d>=3: min(max(g(1-u)^{-1/2},1),L), 1_2:1121)
Path/Scales.lean:44: def scaleM (L W : ℕ) (E u : ℝ) : ℝ := (W : ℝ) ^ 2 * ellT L u ^ 2 * etaT E u  <-  M_u = W^2 ell_u^2 eta_u  (d>=3: Delta_u = W^{-d}B_{u,0}, B from eq_B_param 1_2:1107)
Path/Scales.lean:48: def tailT (L W : ℕ) (E D u ℓ : ℝ) : ℝ :=  <-  T_{u,D}(l) = M_u^{-2} exp(-sqrt(l/ell_u)) + W^{-D}  (d>=3 case (iii): (W^d(1-u))^{-2} e^{-sqrt r} + W^{-D}, ell_u=1)
Path/Scales.lean:52: def ellStar (L W : ℕ) (u : ℝ) : ℝ := Real.log (W : ℝ) ^ ((3 : ℝ) / 2) * ellT L u  <-  ell*_u = (log W)^{3/2} ell_u  (near/far threshold 6 ell*_u of Step 5; d>=3: (log W)^{3/2}, 4(log W)^{3/2} in res_deccalE_*)
Path/Step2PropsV3.lean:41: (if (zdist2 (d.L n) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (d.L n) (d.W n) p.1  <-  Step-5 near-region split 6 ell*_u (d=2 Step 5 = Step 4 at k=2 + (53))
Path/Step2Props.lean:116: def CondStInd (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=  <-  con_st_ind: M_s^{-1} <= ((1-t)/(1-s))^{30}  (d>=3: Delta_t^{c_d} <= (1-t)/(1-s), c_d <= 1/100, 1_2:1295)
Induction/Step45.lean:1223: Real.exp (Real.sqrt 6 * Real.log (d.W n : ℝ) ^ ((3 : ℝ) / 4)) ≤  <-  Step 5 d=2: loss exp(sqrt 6 (log W)^{3/4}) absorbed in N^eps (d>=3: (log W)^{10}, eq:assmtlarge 3_5:1954)
Induction/Step45.lean:1258: theorem step5 (κ c τ : ℝ) (E s t : ℕ → ℝ) : Step5TargetV3 d κ c τ E s t := by  <-  Step 5 d=2 theorem (Step 4 at k=2 + eq 53; not the d>=3 cases (i)-(iii))
Path/LemDecCalE.lean:53: def lossE2 (Λ K₀ : ℝ) : ℝ :=  <-  lem_dec_calE d=2 loss: Lambda^6 (1+log(L^2 W^12))^4 (1+log W)^3 exp(8 (log W)^{3/4})
Path/LemDecCalE.lean:61: def E2Hyp (E s u v D Λ K₀ : ℝ) (M : Matrix (Idx L W) (Idx L W) ℂ) : Prop :=  <-  lem_dec_calE d=2 hypotheses: floor L^2 W^12 <= W^{D/2}, M_v >= 1
Path/LemDecCalE.lean:72: def LemDecCalE_lk : Prop :=  <-  lem_dec_calE d=2 res_deccalE_lk: eta_u^{-1} M_u^{-1} (J*)^2 T_{v,D}  (d>=3: (1-u)^{-1}(W^d|1-u|)^{-1}(J*)^2 T_{u,D})
Path/LemDecCalE.lean:24: and E.2c reuse (the constants of (e7), (e8) recomputed for the `5 × 5 = 25` neighbour pairs of  <-  lem_dec_calE d=2: neighbour pairs 5 x 5 = 25 (d>=3: (1+2d)^2 = 49)
Evolution/CltDecorrelation.lean:263: (Fintype.card (Coord (d.L n) (d.W n)) : ℝ) = 2 * ((d.size n : ℕ) : ℝ) ^ 2 := by  <-  CLT d=2: replacement over 2 N^2 real coordinates, N = (WL)^2 (d>=3: N = (WL)^d)
Evolution/CltDecorrelation.lean:277: def CltFarThm (κ 𝔠 δ : ℝ) : Prop :=  <-  CLT d=2: far decorrelation CltFarThm (= eq:bound_isolated, DYYY25 (7.39))
Evolution/Case3Defs.lean:72: def CltCase1Prec (κ 𝔠 δ : ℝ) (C : ℝ) : Prop :=  <-  CLT d=2: Case 1 conclusion W^{C tau} ell_t ell_u Lambda max|Z|, one-label local form Y_b, no decay in |a1-a2|
Evolution/Case3Defs.lean:98: def CltCase2Prec (κ 𝔠 δ : ℝ) (C : ℝ) : Prop :=  <-  CLT d=2: Case 2 conclusion W^{C tau} ell_u Lambda + W^-D (|Z_ab| <~ (1+|a-b|)^-1)
Evolution/CltDecorrelation.lean:278: ∀ (K : ℕ) (C' τ : ℝ) (E s₀ t₀ u t : ℕ → ℝ) (F : ∀ n, LocalForm (d.L n) (d.W n) 1 K),  <-  CLT d=2: CltFarThm takes ONE common one-label form F : LocalForm L W 1 K
Evolution/CltMoments.lean:155: def CltMoments.ball (L : ℕ) [NeZero L] (R : ℝ) (β : Z2 L) : Finset (Z2 L) :=  <-  CLT d=2: moment counting over balls of Z2 L (d>=3: balls of Zd d L, Defs/Shells, Defs/RadialSum)
Loop/LatticeCount.lean:174: theorem card_ball_le : ∀ (L : ℕ) [NeZero L] (a : Z2 L) (R : ℝ), 0 ≤ R →  <-  CLT d=2: ball cardinality card <= (2R+1)^2 (d>=3: (2R+1)^d; the d=2 count behind the moment sums)
Induction/Defs.lean:151: structure LocalForm (L W k K : ℕ) where  <-  LocalForm (vocabulary of the d=2 CLT, not merged in RBM3D)
Evolution/MLExpInv.lean:729: theorem expInvariant : ExpInvariant d := by  <-  MLExpInv: translation/negation invariance of the expected tensors (S2.4 of ML:exp)
```
| d = 3 exponent / object (section (a) row) | d = 2 token (file:line at `c9a24cf`) | what changes |
|---|---|---|
| `ℓ_u = min(max(g(1-u)^{-1/2},1),L)` (1_2:1121); `ℓ_u ≡ 1` for `1-u ≥ g²` | Path/Scales.lean:41 `ellT` | the factor `g` and the lower cutoff 1; case (iii) has `ℓ_u = 1` (`3_5:2287`) |
| `Δ_u = W^{-d}B_{u,0}`, `B_{u,K}` of `(eq_B_param)` (1_2:1107); case (iii) `Δ_u ≍ (W^d(1-u))^{-1}` | Path/Scales.lean:44 `scaleM = W² ℓ_u² η_u` | `M_u^{-1}` becomes `Δ_u`; they agree only when `ℓ_u = 1`, `1-u ≥ g²` (preflight row (iii) amplitude) |
| `T_{u,D}(r) = (W^d|1-u|)^{-2} e^{-√r} + W^{-D}` (`def_WTuD`) | Path/Scales.lean:48 `tailT = M_u^{-2} exp(-√(l/ℓ_u)) + W^{-D}` | same amplitude `η_u^{-2}`, `ℓ_u = 1`; NOT the `𝒯_u` of `def: TTfunc` (DECISIONS §33 correction) |
| thresholds `(log W)^{3/2}`, `4 (log W)^{3/2}` in `(res_deccalE_*)` | Path/Scales.lean:52 `ellStar`, Path/Step2PropsV3.lean:41 (`6 ℓ*_u`) | d = 2 near/far split at `6ℓ*_u` is not used: no `|a₁-a₂| ≥ ℓ*_t` restriction at d >= 3 (Fable §2 remark (iii)) |
| `(con_st_ind)`: `Δ_t^{𝔠_d} ≤ (1-t)/(1-s)`, `𝔠_d ≤ 10^{-2}` (1_2:1296) | Path/Step2Props.lean:116 `M_s^{-1} ≤ ((1-t)/(1-s))^{30}` | exponent 30 against `𝔠_d`; the `ρ`-losses of case (i) close for `ρ ≤ (2A)^{𝔠_d}`, `𝔠_d ≤ 1/100 < 1/60` |
| `(eq:assmtlarge)`: `ρ > (log W)^{10} ⟹ t ≥ 1-(log W)^{-10}` | Induction/Step45.lean:1223 `exp(√6 (log W)^{3/4}) ≤ N^ε` | d = 2 absorbs a stretched-exponential loss in `N^ε`; d >= 3 absorbs `ρ^{C_d} ≤ (log W)^{10 C_d}` or uses `t ≳ 1` |
| Step 5 in cases (i)-(iii) (this probe) | Induction/Step45.lean:1258 `step5` | d = 2 Step 5 = Step 4 at `k = 2` + Step2Eq53PTV3 (docstring :1255-1257); at d >= 3 only case (iv) is that argument (`stStep5IV_holds`) |
| `lem_dec_calE` without loss, `Prec` form with `J*`; hypothesis `W^D ≥ N` | Path/LemDecCalE.lean:53 `lossE2`, :61 `E2Hyp` (floor `L²W^{12} ≤ W^{D/2}`) | d = 2 loss `Λ^6 (1+log(L²W^{12}))^4 (1+log W)^3 exp(8 (log W)^{3/4})` is not in the d >= 3 statement |
| `(res_deccalE_lk)`: `(1-u)^{-1}(W^d|1-u|)^{-1}(J*)² T_{u,D}` | Path/LemDecCalE.lean:72 `LemDecCalE_lk` (`η_u^{-1} M_u^{-1}`) | amplitudes `M_u` ↔ `W^d(1-u)` |
| neighbour pairs of the Ward step `(1+2d)² = 49` at d = 3 | Path/LemDecCalE.lean:24 (`5 × 5 = 25`) | constants of `(e7)`, `(e8)` recomputed |
| CLT replacement over the real coordinates of the `N × N` Hermitian matrix, `N = sz.size n = (WL)^d` | Evolution/CltDecorrelation.lean:263 (`card Coord = 2 N²`, `N = (WL)²`) | the same count `2 N²` with `N = (WL)^d` |
| `(eq:bound_isolated)` for `2p` per-label two-label forms `𝗕_{b^{(k)}}` | Evolution/CltDecorrelation.lean:277-278 `CltFarThm` (one common one-label form `F : LocalForm L W 1 K`) | genuinely new interface (S5-21) |
| `lem;CLT`: `f^{far} ≺ A^{-6/5}/(|a₁-a₂|^{d-2}+1)`, `Σ_b (|b|^{d-1}+1)^{-k} < ∞` iff `(d-1)k > d` | Evolution/Case3Defs.lean:72, :98 (`CltCase1Prec`, `CltCase2Prec`: bounded kernels, no decay in `|a₁-a₂|`); Evolution/CltMoments.lean:155, Loop/LatticeCount.lean:174 (`(2R+1)²` balls in `Z2 L`) | balls in `Zd d L` with `(2R+1)^d`, `Defs/Shells`, `Defs/RadialSum`; cluster exponent `d-(d-2)k+(d+2)(k-1)+2 = 4k` |
| mean part `E f^{far}`: translation and reflection invariance of `E 𝓛^{(2)}`, second difference `prop:BD2` | Evolution/MLExpInv.lean:729 `expInvariant` (class c at T2002, Step 6) | shared with Step 6 (ST-5) |
| two-label loops `𝓑_{b₁b₂}`, k labels | Induction/Defs.lean:151 `structure LocalForm` | not merged in RBM3D; vocabulary replaced by the probe's `STcltB`, `STcltX` |

## P.4 Route per pin (item 4)
`python3 route.py` (RBM2D file:line at `c9a24cf` by regex on the scratch archive; merged declarations resolved in main `250a118`: `name@file:line`, `NOT FOUND` would mark a wrong row; none occurs).  Columns: pin (proof tickets) | paper lines | RBM2D source | merged RBM3D declarations reused | risk.
```
pin (ticket)                                     paper | RBM2D source (c9a24cf) | merged RBM3D declarations reused (main 250a118) | risk
STStep5R/I..IV, STStep5 (S5-02, S5-03, S5-29) | 1_2:1379-1388; 3_5:1939-1940 | Induction/Step45.lean:1258 (d=2: from Step 4 at k=2 and Step2Eq53PTV3, docstring :1255-1257; only the analogue of case (iv)) | STGdecayW@Induction/Step34Pins.lean:208, STDecay@Induction/Defs.lean:121, STDecayStrong@Induction/Defs.lean:134, STLKU@Induction/Step34Pins.lean:184, STConStInd@Induction/Defs.lean:168, STFlow@Induction/Defs.lean:286, precomp_param@Defs/StochDomAt.lean:335, of_eventually_empty@Defs/StochDom.lean:129, of_subset@Defs/StochDom.lean:103, of_subset_union@Defs/StochDom.lean:112, conStInd_const@Induction/Step34Pins.lean:825 | medium
STTailtoTail (S5-04) | 3_5:2344-2362; Fable 2026-10-04 section 2 | Path/UTransport.lean:422 (d=2 form; false at d>=3 with tailT, DECISIONS 33) | UN@Kernel/Evolution.lean:65, EKsgn@Evolution/Pins.lean:45, ukerNonneg@Path/UBounds.lean:388, ukerRowSum@Path/UBounds.lean:409, prop5Decay_holds@Propagator/Prop5Hold.lean:784, norm_Theta_le@Propagator/Props4.lean:218, Theta@Propagator/Basic.lean:70, zdistInf@Defs/Sizes.lean:115 | medium
STLemDecCalE (S5-05..S5-09) | 3_5:2310-2340 | Path/LemDecCalE.lean:72; Path/LemDecCalEdif.lean:1632; Path/LemDecCalEwG.lean:1276 | STELKLKM@Induction/Step2Defs.lean:110, STEGt@Induction/Step2Defs.lean:312, STee@Induction/Step34Pins.lean:159, STEEk@Induction/Step2Defs.lean:316, STGdecayW@Induction/Step34Pins.lean:208, stK2decay_holds@Induction/Step2K2.lean:132, STJhatM@Induction/Step2Defs.lean:81 | medium
STPfStep5 (S5-10, S5-11) | 3_5:2369-2383; Fable section 4(3) | none in RBM2D (Induction/Step45.lean derives step5 from Step 4 and Step2Eq53PTV3); the paper cites [YY_25, section 5.3] | stoppedDuhamel105@Path/Expansion.lean:159, grid_expansion_all@Path/Expansion.lean:1003, StoppedAzumaN@Induction/GridDuhamelN.lean:531, STGridMart@Induction/Step2Defs.lean:537, STGridRepN@Induction/Step2Defs.lean:854, Ugen@Induction/GridDuhamelN.lean:65, STLmaxU@Induction/Step34Pins.lean:176, STLKU@Induction/Step34Pins.lean:184 | high
STNewKLKL (S5-12) | 3_5:628-654, 1968 | none | stNewKLK_holds@Induction/NewKLK.lean:1198, nkl_bound2@Induction/NewKLK.lean:840, STNewKLKAt@Induction/Step2Defs.lean:363, STJhatM@Induction/Step2Defs.lean:81, STprof@Induction/Step2Defs.lean:75 | medium
STEtermsMid (S5-13) | 3_5:1961-1979 | none | STLWT@Induction/Step2Defs.lean:421, stEMn2Exp_holds@Induction/EMn2Exp2.lean:1090, stEMn2Poly_holds@Induction/EMn2Poly.lean:838, stK2decay_holds@Induction/Step2K2.lean:132, STNewKLK@Induction/Step2Defs.lean:377, STprof@Induction/Step2Defs.lean:75 | medium
STDuhamelI (S5-14, S5-15) | 3_5:1941-2070 | none (RBM2D Path/Expansion.lean has the d=2 grid Duhamel expansion, ST2-26) | Ugen@Induction/GridDuhamelN.lean:65, STEKSumNdecay@Induction/Step34Pins.lean:613, STGridRepN@Induction/Step2Defs.lean:854, STGridMart@Induction/Step2Defs.lean:537, StoppedAzumaN@Induction/GridDuhamelN.lean:531, norm_Theta_le@Propagator/Props4.lean:218, tailT_natCast@Kernel/PropT.lean:49 | high
STIniTermI (S5-16) | 3_5:2072-2172 | none | Theta@Propagator/Basic.lean:70, prop5Decay_holds@Propagator/Prop5Hold.lean:784, STKward@Induction/Step34Pins.lean:229, tailT_natCast@Kernel/PropT.lean:49, STAvgU@Induction/Step34Pins.lean:192 | medium
STCltIso (S5-17..S5-21) | 3_5:2245-2248; DYYY25 (7.39), RBSO1D (A.112) | Evolution/CltDecorrelation.lean:277; Evolution/CltSwap.lean:90; Evolution/CltPath.lean:262; Evolution/CltResolvent.lean:156; Evolution/FarEntry.lean:632; Evolution/CltGood.lean:530; Evolution/CltStep.lean:600 | STGbEXPij@Induction/Defs.lean:315, STGdecayW@Induction/Step34Pins.lean:208, STLocalEntryU@Induction/Step34Pins.lean:199, Gres@Loop/GLoopFlow.lean:74, seqP@Gauss/FineModel.lean:169 | medium
STExpInv (S5-22) | 3_5:2196-2200 | Evolution/MLExpInv.lean:729 (class c at T2002, Step 6) | seqP@Gauss/FineModel.lean:169, Lloop@Loop/GLoopFlow.lean:158, STKloop@Induction/Defs.lean:64, Theta@Propagator/Basic.lean:70 | medium
STCltFar (S5-23..S5-25) | 3_5:2173-2249 (eq:2p_product_pair 2226-2235) | Evolution/CltMoments.lean:914 (d=2 balls: Evolution/CltMoments.lean:155) | Theta@Propagator/Basic.lean:70, prop5Decay_holds@Propagator/Prop5Hold.lean:784, sum_radial_pow_le@Defs/RadialSum.lean:192, radC@Defs/RadialSum.lean:97 | high
STDuhamelII, STIniTermII, STWardII (S5-26..S5-28) | 3_5:2251-2283 | none | zeroModeSet@Kernel/Evolution.lean:199, STEKNonzero@Induction/Step34Pins.lean:666, Prop8ZeroMode@Propagator/Pins.lean:87, KLK_ward@Loop/KLWard.lean:1123, norm_zeroModeSet_UN_le@Kernel/Evolution.lean:629 | medium
```

## P.5 Split table (item 6)
`python3 split.py`.  Estimates: `m` measured on the probe (the line ranges named), `p` port = kept lines x 1.15 rounded to 10, `n` new work = lines of the nearest merged analogue rounded to 50, `T2039` = the row of T2039 P.5 (ST2-36..39).  Dependencies on other gates: ST-2/ST-3 tickets (`STGridRepN`, `STGridMart`, `STLWT`, `STEMn2*`, `STK2decay`: merged or in the ST-2 queue), LW (`STLWT`), EK (merged EK-2..EK-6).
```
| id | new file (RBM3D/) | statements | source | deps | est lines | basis | role | risk |
|---|---|---|---|---|---|---|---|---|
| S5-01 | Induction/Step5Pins | tailTD, regimes, STIngR5, STStep5R/Concl, every ingredient pin of this report, their instances | probe 1-476, 1704-1815, 1853-1908, 1929-1986 | merged only (Defs, Step34Pins, Step2Defs, Kernel/Evolution) | 702 | m | prover | low |
| S5-02 | Induction/Step5Kit | Prec kit, assembly STDecay/STDecayStrong at t, comparisons, case (i) from pins, case (iv) PROVED | probe 477-1039, 1816-1852, 1909-1928 | S5-01 | 620 | m | prover | low |
| S5-03 | Induction/Step5Cases | case (iii) from pf_step5, case (ii) from pins, skeleton instances | probe 1040-1702 | S5-01, S5-02 | 663 | m | prover | low |
| S5-04 | Induction/TailtoTail | STTailtoTail (neiwuj), T_{u,D}, every sigma, C=C_d^2 | new: 3_5:2344-2362 + docs/claude-team/fable/2026-10-04-tailtotail.md; analogue Induction/ContractPt 638 | Propagator (Theta, rows, signs), Kernel/Evolution (UN, EKsgn), Defs/Tail | 800 | n | prover-hard | medium |
| S5-05 | Path/LemDecCalE | lem_dec_calE: res_deccalE_lk, GijGEX / def_ELKLK inputs (= T2039 ST2-36) | RBM2D Path/LemDecCalE.lean (kept 857) | S5-01 (T2039 ST2-01) | 860 | T2039 | prover | medium |
| S5-06 | Path/LemDecCalEdif | res_deccalE_dif part 1 (= ST2-37) | RBM2D Path/LemDecCalEdif.lean (kept 1664, half) | S5-05 | 830 | T2039 | prover | medium |
| S5-07 | Path/LemDecCalEdif | res_deccalE_dif part 2 (= ST2-38) | RBM2D Path/LemDecCalEdif.lean (other half) | S5-06 | 830 | T2039 | prover | medium |
| S5-08 | Path/LemDecCalEwG | res_deccalE_wG (= ST2-39) | RBM2D Path/LemDecCalEwG.lean (kept 1385) | S5-05 | 1390 | T2039 | prover | medium |
| S5-09 | Induction/LemDecCalEPrec | STLemDecCalE: the three bounds as Prec, uniform in u in [s,t], J* control | new interface over S5-05..08 (RBM2D deterministic E2Hyp/lossE2); analogue Induction/QVN 874 | S5-05..S5-08, S5-01, STGdecayW | 700 | n | prover-hard | medium |
| S5-10 | Induction/PfStep5Alg | lem:pf_step5 part 1: closure algebra J*_{t^T} <~ C + log W + W^{2eps-d/2} < W^eps in 3 terms | new: 3_5:2369-2383, Fable 2026-10-04 section 4(3) | S5-04, S5-09 | 700 | n | prover-hard | high |
| S5-11 | Induction/PfStep5 | lem:pf_step5 part 2: stopping time T of (eq:def_TTT), the Prec conclusion STPfStep5 | new: 3_5:2369-2383 (paper: "analogous to (2.76) of [YY_25 5.3]", no proof); analogue Induction/GridDuhamelN 778 + StoppedAzumaN | S5-10, STGridMart, StoppedAzumaN | 900 | n | prover-max | high |
| S5-12 | Induction/NewKLKL | STNewKLKL: sharp lem:newKLK at ell=L, floor kept (paper-delta T2134a) | adapt merged Induction/NewKLK.lean (nkl_bound2, 1332 lines) | S5-01, merged STNewKLK | 600 | n | prover-hard | medium |
| S5-13 | Induction/EtermsMid | STEtermsMid: (S5WG+M000), (S5WG+M) for E^{LKxLK}, E^{G~}, (E x E)^{M} | new: 3_5:1961-1979; analogue Induction/Step2Core 1771 (part) | S5-12, STLWT (LW), STEMn2Exp/Poly (ST-2), STK2decay, STGdecayW | 900 | n | prover-hard | medium |
| S5-14 | Induction/Step5Kernel | kernel facts of (iois-mtx): ||Theta^{(+,-)}||_{inf->inf}=1/(1-t), (uwp2-92kj), (uwftgwesj), rho-losses | new: 3_5:1983-2065; analogue Evolution/SumDecayZero 1746 (part) | EK pins STEKSum*, Propagator, Kernel/Evolution | 700 | n | prover-hard | medium |
| S5-15 | Induction/DuhamelI | STDuhamelConcl engine and STDuhamelI: Duhamel + Azuma on the grid, exponent closure rho A^{-1/3}, rho A^{-1/2}, rho^3 A^{-1/4} <= A^{-1/5} | new: 3_5:1941-2070; analogue Induction/GridDuhamelN 778 + GridDriftN 1261 | S5-01, S5-12, S5-13, S5-14, STGridRepN, STGridMart | 1400 | n | prover-max | high |
| S5-16 | Induction/IniTermI | STIniTermI: sigma1=sigma2 short range, regime reduction, f^{near}, Ward term g_a; f^{far} from S5-25 | new: 3_5:2072-2172, 2176-2181 | S5-14, S5-25 | 1100 | n | prover-hard | medium |
| S5-17 | Evolution/CltSwapPath | CltSwap (replacement of one real coordinate) + CltPath (resolvent path), LocalForm vocabulary with k labels (RBM2D Induction/Defs.lean:151, not merged) | RBM2D Evolution/CltSwap.lean (kept 329) + CltPath.lean (kept 283) | merged Gauss/Model, Gauss/Envelope | 700 | p | prover | low |
| S5-18 | Evolution/CltResolvent | CltResolvent: resolvent expansion along a Gaussian coordinate | RBM2D Evolution/CltResolvent.lean (kept 728) | S5-17, merged Gauss/LoopEnvelope; Case3Defs replaced by S5-01 vocabulary | 840 | p | prover | medium |
| S5-19 | Evolution/FarEntry | FarEntry: entry bounds for the far decorrelation (needs GbEXP, KellStar, PerTimeCalc) | RBM2D Evolution/FarEntry.lean (kept 817) | merged Green pins (STGbEXPij), Induction/PerTimeCalc | 940 | p | prover-hard | medium |
| S5-20 | Evolution/CltGood | CltGood: good event, sub-Gaussian tail of the swap error | RBM2D Evolution/CltGood.lean (kept 615) | S5-19 | 710 | p | prover | medium |
| S5-21 | Evolution/CltStep | CltStep + CltDecorrelation: per-step bound, telescoping; STCltIso = (eq:bound_isolated), generalising CltFarThm (one common one-label form, CltDecorrelation.lean:277-284) to 2p per-label two-label forms | RBM2D Evolution/CltStep.lean (kept 730) + CltDecorrelation.lean (kept 392) | S5-17, S5-18, S5-20 | 1290 | p | prover-hard | medium |
| S5-22 | Evolution/ExpInvMean | STExpInv (translation/reflection of E L^{(2)}) + mean part of f^{far}: first difference -> second difference, BD2 | RBM2D Evolution/MLExpInv.lean (kept 818, shared with ST-5) + new: 3_5:2184-2210 | S5-01, merged Propagator Prop5*/BD1, BD2 | 1200 | n | prover-hard | medium |
| S5-23 | Evolution/CltMoments1 | moment counting of f^{far} at d>=3, part 1: clusters, two-label loops, BD1 weights, k>=2 | partial port RBM2D Evolution/CltMoments.lean (kept 2094, 199 Z2/zdist2 uses) + new counting (preflight table row 7) | S5-21, Defs/Shells, Defs/RadialSum (Loop.LatticeCount replaced) | 1300 | p/2 + new | prover-hard | high |
| S5-24 | Evolution/CltMoments2 | moment counting part 2: 2p-th moment sum over clusters (eq:2p_product_pair), isolation removal of singletons | as S5-23 | S5-23 | 1300 | p/2 + new | prover-hard | high |
| S5-25 | Evolution/CltFar | STCltFar: assembly of f^{far} <~ A^{-6/5}/(|a1-a2|^{d-2}+1) from isolation, counting, mean part | new: 3_5:2173-2249 | S5-21, S5-22, S5-24 | 900 | n | prover-max | high |
| S5-26 | Induction/DuhamelII | STDuhamelII: Q^{(1)} = zeroModeSet {0} for mixed signs, Q empty for same sign (paper-delta T2134g) | new: 3_5:2251-2283 (paper: "similar argument"); merged Induction/ZeroModeCalc 820 | S5-15, S5-14 | 700 | n | prover-hard | medium |
| S5-27 | Induction/IniTermII | STIniTermII: (zYU2) absolute values, prop:ThfadC0, 1-s <= g^2/L^2 | new: 3_5:2275-2281 | S5-14 | 600 | n | prover-hard | medium |
| S5-28 | Induction/WardII | STWardII (zYU1): Ward identities WI_calL, WI_calK, Gt_avgbound_flow | new: 3_5:2257-2262 | merged KLWard (Loop), STKward | 600 | n | prover | medium |
| S5-29 | Induction/Step5Chain | STStep5 general: cases (i)-(iv) glued by intermediate times, the assembly at t | new: 3_5:1939 ("by adding intermediate times"); no RBM2D counterpart (RBM2D step5 = Induction/Step45.lean:1258) | S5-02, S5-03, S5-15, S5-16, S5-26, S5-27, S5-28 | 900 | n | prover-hard | medium |
probe lines 2061; moved by S5-01..03: 1985; section 9 (print-axioms block, not moved): lines 1988-2061 = 74; unassigned blank/separator lines: 2
tickets 29 (of which 4 are T2039 ST2-36..39, counted in ST-4 by DECISIONS 28); est lines 25675; mean 885; min 600; max 1400
role count: {'prover': 11, 'prover-hard': 15, 'prover-max': 3} | risk: {'high': 6, 'low': 4, 'medium': 19}
O2 (DECISIONS 9): band 25/40/50: in 25-40 -> question to Jun: no
tickets outside 600-1500: []
```

## P.6 Registry classes (DECISIONS §16, §20)
Classes follow `RBM3D/Test/Axioms.lean`: borrowed = the paper cites it, owed = the paper proves it, structural = a data condition.  The three paper-cited pins are borrowed in the ledger sense of §16 and are proved internally (§5: only LSY may stay external).  Proposed (the dispatcher decides): owed: `STStep5I/II/III`, `STStep5`, `STEtermsMid`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`, `STNewKLKL`, `STCltFar`, `STExpInv`, `STTailtoTail`; borrowed: `STCltIso` ([DYYY25 (7.39)], [RBSO1D (A.112)], `3_5:2248`), `STLemDecCalE` ([YY_25, Lemma 5.7], `3_5:2338`), `STPfStep5` ([YY_25, 5.3], `3_5:2380`); structural: `STReg5I/II/III/IV/Mid` (regimes of the time sequences, like `STCaseI/II`); proved in the probe: `STStep5IV`.  Premises of `STIngR5` already in the registry of main (`python3 reg.py`, `RBM_ROOT` = clean copy of `250a118`; `not listed` = no merged theorem assumes it as a hypothesis, or it is proved: `stNewKLK_holds`, `stEMn2Exp_holds`, `stEMn2Poly_holds`, `stK2decay_holds`, `stek_*_holds`):
```
registry of main: 1 borrowed, 76 owed, 39 structural names
STFlow           structural
STKbound         not listed
STKward          not listed
STLK             owed
STDecay          owed
STDecayStrong    owed
STConStInd       structural
STStep1Loop      not listed
STStep2Concl     not listed
STGdecayW        owed
STLocalEntryU    not listed
STAvgU           owed
STLmaxU          owed
STLKU            owed
STNewKLK         not listed
STLWT            owed
STEMn2Exp        not listed
STEMn2Poly       not listed
STGridMart       not listed
STGridRepN       owed
STK2decay        not listed
STEKSumNdecay    not listed
STEKSumRes1      not listed
STEKSumRes2NAL   not listed
STEKSumRes2      not listed
STEKNonzero      not listed
STGbEXPij        not listed
STOptL2          owed
STDecayLoopPT    not listed
```

## P.7 Instances (item 7)
### P.7a the 28 `inst_*` theorems by data and the data/regime lemmas, with the `szCL` data of the repair (re-run at `7b2b789`, Sun Oct  4 15:49:05 UTC 2026: `python3 repair/inst_groups_r1.py`, `python3 repair/instances_r1.py`; the two scripts differ from `inst_groups.py`, `instances.py` of P.9 only by the `szCL` names and the import path, P.10)
```
28 instance theorems (RBM.Gauss.T2134Inst), by data
generic shape (any data): inst_ing5
data (szB, zB, 7/8, 15/16): inst_ing5_I inst_step5I inst_etermsMid inst_duhamelI inst_iniTermI inst_skeletonI
data (szB, zB, 15/16, 31/32): inst_ing5_II inst_step5II inst_duhamelII inst_iniTermII inst_wardII inst_skeletonII
data (sz0, z0, 0, 1/16): inst_ing5_III inst_step5III inst_step5 inst_assembly inst_lemDecCalE inst_pfStep5 inst_skeletonIII
data (szG, zB, 5/8, 3/4): inst_ing5_IV inst_step5IV inst_step5IV_proved
data (szCL, zCL, 0, 1 - L_n^{-2}): inst_cltFar inst_cltIso
deterministic pin, own data: inst_tailtoTail inst_newKLKL inst_expInv
```
```
namespace RBM.Gauss.T2134Inst: 71 declarations; instances (inst_*): 28; data/regime lemmas: 11; szCL data (repair): 32 declarations, listed: the 10 below
L1724  szG                    The third size sequence: `szB` with the coupling `ilambda = 5` (`W^{-d/2+𝔡} ≤ 5 ≤ 𝔡⁻¹ = 10`).
L1726  szG_WO                 theorem szG_WO : szG.WO (1 / 10) :=
L1738  flow_zG                theorem flow_zG : STFlow szG (1 / 10) (1 / 10) (1 / 6) (1 / 10) zB :=
L1740  szG_reg4               theorem szG_reg4 : STReg5IV szG (fun _ => 5 / 8) (fun _ => 3 / 4) :=
L1743  szB_reg5I              theorem szB_reg5I : STReg5I szB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
L1746  szB_reg5II             theorem szB_reg5II : STReg5II szB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
L1749  sz0_reg5III            theorem sz0_reg5III : STReg5III sz0 sInst tInst :=
L1774  inst_ing5              The common shape of the instances: the constant `𝔠_d` of the pin, then deterministic data with the regime `R` and `(con_st_ind)`.
L1786  inst_ing5_I            Data of case (i) and of the window of cases (i)+(ii): `(szB, zB, 7/8, 15/16)`.
L1795  inst_ing5_II           Data of case (ii): `(szB, zB, 15/16, 31/32)`.
L1804  inst_ing5_III          Data of case (iii) and of the general statement: `(sz0, z0, 0, 1/16)`.
L1811  inst_ing5_IV           Data of case (iv): `(szG, zB, 5/8, 3/4)`.
L1822  inst_step5I            **Step 5, case (i)** applied at `(szB, zB, 7/8, 15/16)`: `1/16 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`.
L1827  inst_step5II           **Step 5, case (ii)** applied at `(szB, zB, 15/16, 31/32)`: `1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/16 ≤ 1/16`.
L1832  inst_step5III          **Step 5, case (iii)** applied at `(sz0, z0, 0, 1/16)`: `ilambda_n² ≤ 15/16 = 1-t`.
L1837  inst_step5IV           **Step 5, case (iv)** applied at `(szG, zB, 5/8, 3/4)`: `1-t = 1/4 ≤ 1-s = 3/8 ≤ ilambda²/L^3 = 25/64`.
L1842  inst_step5IV_proved    Case (iv) is a theorem (`stStep5IV_holds`): the instance of the proved statement.
L1847  inst_step5             **Step 5, general** applied at `(sz0, z0, 0, 1/16)`.
L1852  inst_assembly          **The assembly** `STDecay ∧ STDecayStrong` at `t` from the uniform Step-5 conclusion, at `(sz0, z0, 0, 1/16)`.
L1859  inst_lemDecCalE        `lem_dec_calE` at `(sz0, z0, 0, 1/16)`.
L1864  inst_pfStep5           `lem:pf_step5` at `(sz0, z0, 0, 1/16)`.
L1869  inst_etermsMid         `(S5WG+M000)`, `(S5WG+M)` at `(szB, zB, 7/8, 15/16)` (window of cases (i)+(ii)).
L1874  inst_duhamelI          `(iois-mtx2)` at `(szB, zB, 7/8, 15/16)`.
L1880  inst_iniTermI          `(iksjuwjx0)` at `(szB, zB, 7/8, 15/16)`.
L1905  szCL                   def szCL : Sizes 3 where
L1978  sCL                    def sCL : ℕ → ℝ := fun _ => 0
L1980  tCL                    def tCL : ℕ → ℝ := fun n => 1 - (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹
L1982  zCL                    def zCL (n : ℕ) : ℂ := ⟨1 / 2, (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ / 2⟩
L2017  flow_zCL               theorem flow_zCL : STFlow szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL :=
L2019  lemT_zCL               theorem lemT_zCL (n : ℕ) : tCL n ≤ lemT (zCL n) :=
L2056  szCL_reg5I             theorem szCL_reg5I : STReg5I szCL sCL tCL :=
L2111  szCL_con               theorem szCL_con {𝔠d : ℝ} (h𝔠 : 0 < 𝔠d) : STConStInd szCL 𝔠d sCL tCL :=
L2163  szCL_cltFar_index_nonempty **The index set of `STCltFarConcl` is nonempty** at `(szCL, sCL, tCL)`, for every `n`: the type `U n` of the pin (copied from `STCltFarConcl`) has the
L2192  szCL_cltIso_witness    **A label configuration satisfying the premises of `STCltIsoConcl`** at `(szCL, sCL)`, `p = 1`, every `n`: `b^{(1)} = (x_n, x_n)`, `b^{(2)} = (0, 0)` 
L2226  inst_cltFar            `lem;CLT` at `(szCL, zCL, 0, 1 - L_n^{-2})` (case (i); index set nonempty: `szCL_cltFar_index_nonempty`).
L2232  inst_cltIso            `(eq:bound_isolated)` at `(szCL, zCL, 0, 1 - L_n^{-2})` (premises satisfiable: `szCL_cltIso_witness`).
L2238  inst_duhamelII         The integrated hierarchy with `Q^{(1)}` at `(szB, zB, 15/16, 31/32)` (case (ii)).
L2245  inst_iniTermII         The initial term of case (ii).
L2251  inst_wardII            `(zYU1)` at `(szB, zB, 15/16, 31/32)`.
L2259  inst_skeletonI         Case (i) from its ingredients, at `(szB, zB, 7/8, 15/16)`: the three ingredient pins give the target pin, which is then instantiated.
L2264  inst_skeletonII        Case (ii) from its ingredients, at `(szB, zB, 15/16, 31/32)`.
L2270  inst_skeletonIII       Case (iii) from `lem:pf_step5`, at `(sz0, z0, 0, 1/16)`.
L2286  inst_tailtoTail        **`TailtoTail`, instantiated** at `d = 3`, `L = 5`, `g = 1/2`, `W = 25`, `D = 2`, `s = 1/2`, `t = 3/4` (`1-t = 1/4 = g²`: the boundary of the hypothes
L2303  inst_newKLKL           **`lem:newKLK` at `ℓ = L`, instantiated** at `n = 0`, `E = 1/2`, `u = 0`, `D = 1`, `ℓ = L = 4` and the matrix `H = 0` (Hermitian, `‖G_0 - M‖_max = 0 ≤
L2325  inst_expInv            **Translation and reflection invariance of `𝔼 𝓛^{(2)}`, instantiated** at `n = 0`, `E = 1/2`, `u = 1/2` (`H_u = √u X`, nondegenerate), `σ = (+,-)`.
```
### P.7b the regime inequalities of the data recomputed in exact fractions, boundaries hit, and `(eq:WO)` at n = 0..3 (`python3 extreme.py`)
```
szB      g^2=1 L=4 (s,t)=(7/8,15/16): g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/16 1-s=1/8 | regimes holding ['(i)'] | boundary hit: ['1-t = g^2/L^2']
szB      g^2=1 L=4 (s,t)=(15/16,31/32): g^2/L^2=1/16 g^2/L^3=1/64 1-t=1/32 1-s=1/16 | regimes holding ['(ii)'] | boundary hit: ['1-s = g^2/L^2']
szG      g^2=25 L=4 (s,t)=(5/8,3/4): g^2/L^2=25/16 g^2/L^3=25/64 1-t=1/4 1-s=3/8 | regimes holding ['(iv)'] | boundary hit: none
sz0 n=0  g^2=1/4096 L=4 (s,t)=(0,1/16): g^2/L^2=1/65536 g^2/L^3=1/262144 1-t=15/16 1-s=1 | regimes holding ['(iii)'] | boundary hit: ['s = 0']
sz0 n=1  g^2=1/16777216 L=8 (s,t)=(0,1/16): g^2/L^2=1/1073741824 g^2/L^3=1/8589934592 1-t=15/16 1-s=1 | regimes holding ['(iii)'] | boundary hit: ['s = 0']
sz0 n=3  g^2=1/68719476736 L=16 (s,t)=(0,1/16): g^2/L^2=1/17592186044416 g^2/L^3=1/281474976710656 1-t=15/16 1-s=1 | regimes holding ['(iii)'] | boundary hit: ['s = 0']
(eq:WO), fd=1/10: W^{-d/2+fd} <= g <= 10
szB [(0, 0.14359, 1.0, True), (1, 0.10506, 1.0, True), (2, 0.08139, 1.0, True), (3, 0.06559, 1.0, True)]
szG [(0, 0.14359, 5.0, True), (1, 0.10506, 5.0, True), (2, 0.08139, 5.0, True), (3, 0.06559, 5.0, True)]
sz0 [(0, 0.00781, 0.015625, True), (1, 6e-05, 0.000244140625, True), (2, 0.0, 2.143347050754458e-05, True), (3, 0.0, 3.814697265625e-06, True)]
```
### P.7c what the instances discharge (index sets added in the repair, Sun Oct  4 15:49:05 UTC 2026)
`inst_ing5` applies a Step-5 pin `STIngR5 3 R Concl` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6` (the merged `Admissible` data of `szB`), the flow `STFlow` (`flow_zB`, `flow_zG`, `flow_z0`, `flow_zCL`), `0 ≤ s < t ≤ lemT z` (`szB_flow_ht`, `sz0_ht`, `szCL_hst`, `lemT_zCL`), the regime `R` (`szB_reg5I`, `szB_reg5II`, `szG_reg4`, `sz0_reg5III`, `szCL_reg5I`) and `(con_st_ind)` for every `𝔠_d > 0` (`conStInd_const`, `sz0_con`, `szCL_con`); what stays a hypothesis of the instance conclusion `InstIng5Concl` are the stochastic premises `STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong` at `s`, `STStep1Loop`, `STStep2Concl`, `STLmaxU`, `STLKU` (pins of other gates).  `inst_tailtoTail`: `d = 3`, `L = 5`, `g = 1/2`, `W = 25`, `D = 2`, `s = 1/2`, `t = 3/4` (`1-t = 1/4 = g²`, the boundary of `g² ≤ 1-t`), `m = i`, `σ = (+,-)`, the extremal tensor `A_b = T_{s,D}(|b₁-b₂|)` (nonzero), `a = (0, e₁)`.  `inst_newKLKL`: `n = 0`, `E = 1/2`, `u = 0`, `D = 1`, `ℓ = L = 4`, `H = 0` (`‖G_0 - M‖_max = 0`, `STGMM_zero`): the constant `δ₀` of the pin is existential, so only exact `G = M` data discharge `‖G-M‖ ≤ δ₀`; the left side is `0` (same as T2039 audit O3).  `inst_expInv`: `n = 0`, `E = 1/2`, `u = 1/2` (the random model at `H_u = √u X`, nondegenerate).
**Index set of each instance conclusion at its data** (compiled: `IndexCheck.lean` and `szCL_cltFar_index_nonempty`, `szCL_cltIso_witness`, P.10):
- `inst_step5III`, `inst_step5`, `inst_skeletonIII` (sz0): `STGdecayW` (`TimeIcc [0, 1/16]` × `σ` × `a`) and `STDecayStrongU` (`g_n² ≤ 15/16`): both nonempty; `inst_assembly`: `STDecay` (`σ, a`) and `STDecayStrong` (`g_n² ≤ 15/16`): nonempty; `inst_pfStep5`: `STIdx2` with `g_n² ≤ 15/16`: nonempty; `inst_lemDecCalE`: `STIdx2` and the pair index (`a' = a`): nonempty.
- `inst_step5I`, `inst_skeletonI` (szB, `7/8, 15/16`), `inst_step5II`, `inst_skeletonII` (szB, `15/16, 31/32`), `inst_step5IV`, `inst_step5IV_proved` (szG, `5/8, 3/4`): `STGdecayW` nonempty; `STDecayStrongU` **empty** (`g² = 1 > 1/16`, `1 > 1/32`; `g² = 25 > 1/4`), as in the paper, where `(Eq:Gdecay+s<g_flow)` is stated for `1-t ≥ g²` only.
- `inst_etermsMid`, `inst_duhamelI`, `inst_iniTermI` (szB, `7/8, 15/16`), `inst_duhamelII`, `inst_iniTermII`, `inst_wardII` (szB, `15/16, 31/32`): `STIdx2`, `STIdx2 × Fin 2`, `STIdx2P` with `STSigAll`, `STSigMixed`, `STSigSame`: nonempty.
- `inst_cltFar`, `inst_cltIso` (szCL: `L_n = 2(n+24)^5`, `W_n = 2^{n+24}`, `g = 1`, `s = 0`, `1-t_n = L_n^{-2}`, `z_n = 1/2 + i/(2L_n²)`): `U n` of `STCltFarConcl` nonempty at every `n` (`σ = (+,-)`, `a = (x_n, 0)`, `|x_n| = (n+24)^5 = L_n/2`); `STCltIsoConcl`: `σ₀ ≠ σ₁` nonempty and, for `p = 1`, `b = ((x_n, x_n), (0, 0))` meets the window and isolation premises at every `n`.  At szB (`L = 4`, the data before the repair) both were empty (audit round 1 §4).
- `inst_newKLKL`, `inst_expInv`: all `(σ, a)` (and `c`): nonempty; `inst_tailtoTail`: one inequality at `a = (0, e₁)`, no index set; `inst_ing5`, `inst_ing5_I..IV`: generic `Concl`.

## P.8 Findings (carried into section (d) of the prove report)
- (F-A) Only the 8 CLT files (5988 kept lines) and the 3 `LemDecCalE*` files (3906) are sources of Step 5; 9 of the 17 ST-4 files (9113 kept lines) are the d = 2 `lem:sum_decay` forms: merged EK-2..EK-6 at d >= 3, or no counterpart (P.1b).  The ST-4 sub-gate of T2002 (17 files / 15.1k kept) is therefore 5988 + 3906 kept lines of sources plus new work.
- (F-B) The d = 2 CLT is one-label (`LocalForm L W 1 K`, bounded kernels `Z_{ab}`) and its conclusion carries no decay in `|a₁-a₂|`; the d >= 3 `lem;CLT` is two-label (`𝓑_{b₁b₂}` with first differences `Θ_{b₂a₂} - Θ_{b₁a₂}`) and keeps `1/(|a₁-a₂|^{d-2}+1)`: S5-21 (interface), S5-23/S5-24 (moment counting at `(d-1)k > d`, `k ≥ 2`) are new work on a ported skeleton (high risk).
- (F-C) The printed `lem:newKLK` (`(juwo=Lklk)`, merged `STNewKLK`, `Ĵ + Ĵ² 1_{ℓ ≥ 1}`) is too weak for case (i): with `Ĵ ≺ A^{-1/6}` the linear term costs `ρ A^{1/30}` against the target `A^{-1/5}`; the sharp form at `ℓ = L` (first two index sets empty, `3_5:1968`) is `STNewKLKL` (T2134a).
- (F-D) `lem_dec_calE`, `lem:pf_step5` and `(eq:bound_isolated)` are cited, not proved, in the paper (`3_5:2338`, `2380`, `2248`); the closure of `lem:pf_step5` at d = 3 is Fable's sketch (`J* ≺ C + log W + W^{2ε-𝔡/2} < W^ε`, `ε < 𝔡/4`; confidence 85%) and the stopped hierarchy `(int_K-L_ST)` is the ST2-26/27 material (`stoppedDuhamel105`, `StoppedAzumaN`).
- (F-E) `(eq:assmtlarge)` cannot be instantiated at a concrete `W`: its branch `ρ > (log W)^{10}` needs `ρ ≤ (W^d(1+g²))^{𝔠_d}`, i.e. `log W ≳ 1.26·10^4` at `𝔠_d = 1/400` (preflight).  No pin assumes it; the proofs must treat both branches (`ρ ≤ (log W)^{10}`: Step 2 with the loss absorbed; else `t ≥ 1-(log W)^{-10}`).
- (F-F) The case-(ii) closure is not printed (`3_5:2268`: "a similar argument"): `(1-s)² ‖Θ̊‖ ‖Θ‖ ≤ ρ (1-s) L²/g² ≤ ρ` (one `ρ`, not `ρ²`; preflight (a) row (ii) zero mode); the pins `STDuhamelII`, `STIniTermII`, `STWardII` fix the statements (T2134g).
- (F-G) (iii) strong ⟹ weak holds only up to the polylogarithm: `T_{u,D}(r) ≤ 4(Δ_u^{1/5} W^{-d}B_{u,r} e^{-√r} + W^{-D})` needs `y^{4/5}((D log W)²+1)^{d-2} ≤ 1`, `y = (W^d(1-u))^{-1}`; at the extreme `1-u = g²` that condition holds only for `W ≳ 2^{102}` (`strongweak.py`: threshold `log2 W = 101.8` at `D = 4`, `𝔡 = 1/10`; condition value 6.9 at `W = 2^80`, and `T/target` reaches 51.9 at `W = 2^5`, `L = 400`); the polylogarithm is absorbed by `≺` (`st5_compare_IIIb`, `st5_polylog_le_W`).
- (F-H) `STIniTermI ⟸ STCltFar` is not compiled: the regime reduction `(eq:ells_to_ellt2)` (`3_5:2119-2128`, otherwise `W^{-D}`), the decomposition `f + g` (`2130-2135`), the Ward term `g_a` (`2136-2146`) and `f^{near}` (`2160-2171`) are proof obligations of S5-16; likewise `STPfStep5 ⟸ STLemDecCalE, STTailtoTail` (S5-10/11, the paper omits the proof).
- (F-I) Main moved after the branch base: T2131-T2133 and T2135 added `Graph/LWSymm`, `Induction/DecayLoopA`, `DecayLoopB` (`STDecayLoopPT` at `DecayLoopA.lean:106`, `STDecayLoopU` at `DecayLoopB.lean:792`), `Induction/QGridA`; the probe imports only `KDecay`, `NewKLK`, `GridDuhamelN` and does not use them.  The clash check and P.4 use `250a118`.
- (F-J) `STExpInv` is shared with Step 6 (RBM2D `Evolution/MLExpInv.lean` is class c, ST-5): S5-22 or the Step-6 ticket, whichever lands first.

### P.8a Numeric checks of the new statements (d = 3), moved verbatim from prove report b.9 (Sun Oct  4 15:49:05 UTC 2026; pasted there at 15:23:05 UTC)
```
$ python3 newklkl.py | tail -4   (STNewKLKL, W=2, L=3, N=216: max R_sharp = (1-u)|E|/(Ĵ² prof + Ĵ W^{-d-D}) over samples and (σ,a); R_old with the printed (Ĵ+Ĵ²) prof)
 0.3 1/L^2    0 |      0.387      0.242     2.792  3.00
 0.3 1/L^2    3 |      0.358      0.212     3.231  3.00
 0.3 1/L^3    0 |      0.592      0.345    16.355  3.00
 0.3 1/L^3    3 |      0.636      0.344     7.410  3.00
$ python3 ttt2.py | grep "^(+,-)"   (STTailtoTail: exact U, A = T_{s,D}, L=16: max_a (U∘A)/T_{t,D}; the other charges give ≤ 0.001)
(+,-)     L=16 g=0.03  1-s=0.9   1-t=0.0009  rho= 1000.0 sum|p|=  1000.00 (rho for xi=1) | max_a R=1.3590 at r=8 | R(r=0,1,2,3)=0.266,0.659,0.854,0.974 | W^-D part factor sum|p|^2/rho^2=1.000
(+,-)     L=16 g=0.1   1-s=1     1-t=0.01    rho=  100.0 sum|p|=   100.00 (rho for xi=1) | max_a R=1.3460 at r=8 | R(r=0,1,2,3)=0.272,0.672,0.865,0.981 | W^-D part factor sum|p|^2/rho^2=1.000
(+,-)     L=16 g=0.05  1-s=0.5   1-t=0.0025  rho=  200.0 sum|p|=   200.00 (rho for xi=1) | max_a R=1.3560 at r=8 | R(r=0,1,2,3)=0.267,0.662,0.856,0.975 | W^-D part factor sum|p|^2/rho^2=1.000
$ python3 strongweak.py | tail -1   (case (iii): the polylog of strong ⟹ weak)
threshold at x=g^2, D=4, fd=0.1: ln W = 70.53, log2 W = 101.8 (the hypothesis y^(4/5)((D log W)^2+1) <= 1 of st5_compare_IIIb fails below it, and the ratio T/target exceeds 4 for large L, see the table; it holds above it)
```

## P.9 Scripts (verbatim; run in this order by `final_run.sh`)
### final_run.sh
```bash
#!/bin/bash
# T2134: every command whose output the reports paste; outputs in out/final/.  Run from anywhere.
S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2134
S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2134
WT=/Users/junyin/Lean_proof/RBM3D-wt/T2134
O=$S/out/final
mkdir -p $O; cd $S
export RBM_ROOT=$S/main250
{ date -u; git -C $WT log --oneline 3389d24..HEAD; git -C $WT rev-parse --short HEAD; git -C $WT diff --name-only 3389d24 HEAD; git -C $WT status --short | wc -l; wc -l < $WT/RBM3D/Probe/T2134Pins.lean; } > $O/git.txt 2>&1
( cd $WT && time lake build RBM3D.Probe.T2134Pins ) > $O/build.out 2>&1; echo "exit=$?" >> $O/build.out
( cd $WT && time lake env lean RBM3D/Probe/T2134Pins.lean ) > $O/lean.out 2>&1; echo "exit=$?" >> $O/lean.out
cp $O/lean.out $S/out/lean_env.txt
( cd $WT && grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2134Pins.lean; grep -c "^import RBM3D" RBM3D/Probe/T2134Pins.lean; grep "^import RBM3D" RBM3D/Probe/T2134Pins.lean | tr '\n' ';' ) > $O/hygiene.txt 2>&1
python3 axioms.py > $O/axioms.txt 2>&1
python3 pins.py > $O/pins.txt 2>&1
python3 instances.py > $O/instances.txt 2>&1
python3 clash.py > $O/clash.txt 2>&1
python3 split.py > $O/split.txt 2>&1
python3 inv4.py > $O/inv.txt 2>&1
python3 map4.py > $O/map.txt 2>&1
python3 tokens2.py > $O/tokens.txt 2>&1
python3 reg.py > $O/reg.txt 2>&1
( cd $WT && lake env lean $S/uses_mathlib.lean ) > $S/uses_mathlib.out 2>&1; python3 mathlib_names.py > $O/mathlib.txt 2>&1
python3 newklkl.py > $O/num_newklkl.txt 2>&1
python3 ttt2.py > $O/num_ttt2.txt 2>&1
python3 strongweak.py > $O/num_strongweak.txt 2>&1
( cd /Users/junyin/Lean_proof/RBM2D && git --no-optional-locks log -1 --format=%h; git --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution RBM2D/Path/LemDecCalE.lean RBM2D/Path/LemDecCalEdif.lean RBM2D/Path/LemDecCalEwG.lean RBM2D/Induction/Step45.lean | tail -3 ) > $O/rbm2d_diff.txt 2>&1
ls -la $O | awk '{print $5, $9}'
python3 inst_groups.py > $O/inst_groups.txt 2>&1
python3 extreme.py > $O/extreme.txt 2>&1
RBM_ROOT=$S/main250 python3 route.py > $O/route.txt 2>&1
python3 check_a.py > $O/check_a.txt 2>&1
python3 clash2d.py > $O/clash2d.txt 2>&1
```
### graph.py
```python
#!/usr/bin/env python3
# T2134: import graph of RBM2D at c9a24cf (scratch copy `rbm2d`, from `git archive`); sub-gate rule of the T2002 portmap (mkportmap.py GROUPS).
import re, os, glob, collections, sys
R=os.path.join(os.path.dirname(os.path.abspath(__file__)),'rbm2d')
files=sorted(glob.glob(R+'/RBM2D/**/*.lean',recursive=True))
rel=lambda f: os.path.relpath(f,R)
text={rel(f):open(f,encoding='utf-8').read() for f in files}
mod=lambda p: p[:-5].replace('/','.')
file_of={mod(p):p for p in text}
imps={p:[file_of[m] for m in re.findall(r'^import\s+(RBM2D\.[A-Za-z0-9_.]+)',t,re.M) if m in file_of] for p,t in text.items()}
def grp(p):
    pats=[('MD',r'RBM2D/(Defs/(Model|StochDom)|Gauss/(Model|Domination|MomentBridge|LinearForm|Envelope|SteinMatrix)|Path/(PerTime|Walk|Transfer|Markov|Stop|Azuma|Step2Props)|Hierarchy/(Loops|Operations|OperationsPairWord))\.lean'),
     ('ST-1',r'RBM2D/(Gauss/.*|Green/.*|Hierarchy/.*|Induction/(Continuity|ConArg|ConArgDet|Step1))\.lean'),
     ('ST-2',r'RBM2D/(Path/.*|Induction/(Grid.*|AzumaProxyN|StepDecompN|LoopC2N|LoopGenN|QVN|Step2TargetV3|StoppedEndDefs))\.lean'),
     ('ST-3',r'RBM2D/Induction/(?!(MainInd|Defs))[A-Za-z0-9]*\.lean'),
     ('ST-5',r'RBM2D/Evolution/(Step61|MLExp.*)\.lean'),
     ('ST-4',r'RBM2D/Evolution/.*\.lean'),
     ('ST-6',r'RBM2D/(Induction/(MainInd|Defs)|Main/(?!BUniv).*)\.lean'),
     ('UN',r'RBM2D/(Universality/.*|Main/BUniv.*)\.lean')]
    for g,pt in pats:
        if re.match(pt,p): return g
    return 'other'
if __name__=='__main__':
    c=collections.Counter(grp(p) for p in text); print(c)
    st4=sorted(p for p in text if grp(p)=='ST-4')
    print(len(st4),'ST-4 files; lines',sum(text[p].count('\n') for p in st4))
```
### inv4.py
```python
#!/usr/bin/env python3
"""T2134 item 1: inventory of the RBM2D ST-4 files at c9a24cf.
Rows: the 17 `Evolution/*` files of the sub-gate ST-4 (T2002 portmap E, rule of mkportmap.py), plus the 3 `Path/LemDecCalE*` files that
DECISIONS 28 moved from ST-2 to ST-4 (lem_dec_calE) and, for reference only, `Induction/Step45.lean` (d=2 Step 5, DECISIONS 26: Step-5 part to ST-6).
Columns: lines at c9a24cf (git archive copy), kept lines at 0c1330a (git show), class/labels/tokens from the T2002 portmap row of the same file,
exponent tokens recomputed with the portmap's stats.py regexes, public declarations, and the public names referenced by ST-5/ST-6 files
(textual references, comments stripped, names defined in exactly one file)."""
import re, os, sys, subprocess, collections, json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from graph import text, grp, imps
REPO='/Users/junyin/Lean_proof/RBM2D'
PORT='/Users/junyin/Lean_proof/RBM3D/docs/reports/T2002-portmap.md'
def git(*a):
    r=subprocess.run(['git','-C',REPO,'--no-optional-locks',*a],capture_output=True,text=True)
    return r.stdout if r.returncode==0 else None
# portmap rows by (directory, file)
pm={}; cur=None
for l in open(PORT,encoding='utf-8'):
    m=re.match(r'^### (\w+) -> RBM3D/',l)
    if m: cur=m.group(1); continue
    if cur and l.startswith('| ') and '.lean |' in l:
        c=[x.strip() for x in l.strip().strip('|').split('|')]
        if len(c)>=7 and re.match(r'^[A-Za-z0-9_]+\.lean$',c[0]): pm[(cur,c[0])]=c
rows_files=sorted(p for p in text if grp(p)=='ST-4')
extra=['RBM2D/Path/LemDecCalE.lean','RBM2D/Path/LemDecCalEdif.lean','RBM2D/Path/LemDecCalEwG.lean','RBM2D/Induction/Step45.lean']
TOK=[('pow2',r'(\(W : ℝ\)|\(L : ℝ\)|\bW\b|\bL\b|\(W \* L\)|\(W : ℂ\)⁻¹|\(W : ℝ\)⁻¹|\(W : ℂ\)|\(\(W \* L\) \^ 2 : ℕ\)|size)\)?\s*\^\s*2\b'),
     ('sup2',r'(W|L|N)[⁻]?²|⁻²|\bd = 2\b|Z_L\^2|Z_\{WL\}\^2|\(W L\)²'),('five',r'\b5⁻¹|\(1 / 5\)|1/5\b')]
def strip_comments(t):
    t=re.sub(r'/-.*?-/','',t,flags=re.S)
    return re.sub(r'--[^\n]*','',t)
declre=re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:protected\s+|private\s+|noncomputable\s+|unsafe\s+)*)(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)\s+([^\s({:\[]+)',re.M)
alldecl=collections.defaultdict(set)
for q,t in text.items():
    for m in declre.finditer(t): alldecl[m.group(3).split('.')[-1]].add(os.path.basename(q))
ctext={p:strip_comments(t) for p,t in text.items()}
idre=re.compile(r"[A-Za-z_][\w']*")
toks={p:set(idre.findall(t)) for p,t in ctext.items()}
STOP={'with','mono','sqrt_of','finset_sum_of','log_nonneg','zeroF','norm_T_le'}
def refs(name,groups_,self_file):
    short=name.split('.')[-1]
    if len(short)<5 or short in STOP or len(alldecl.get(short,()))!=1: return {}
    res=collections.defaultdict(list)
    for q,tk in toks.items():
        g=grp(q)
        if g in groups_ and short in tk and q!=self_file: res[g].append(os.path.basename(q)[:-5])
    return res
rows=[]
for p in rows_files+extra:
    b=os.path.basename(p); d=p.split('/')[1]; t=text[p]; n=t.count('\n')
    k=git('show',f'0c1330a:{p}'); kept=k.count('\n') if k is not None else -1
    r=pm.get((d,b)); cls=r[3] if r else '?'; basis=r[5] if r else ''; labs=r[6] if r else ''
    tok=sum(len(re.findall(rg,t)) for _,rg in TOK)
    decls=[(m.group(2),m.group(3),t.count('\n',0,m.start())+1,'private' in m.group(1)) for m in declre.finditer(t)]
    pub=[(k_,nm,ln) for (k_,nm,ln,pr) in decls if not pr]
    used=[]
    for (k_,nm,ln) in pub:
        rr=refs(nm,['ST-5','ST-6'],p)
        if rr: used.append((nm,ln,{g:sorted(set(v)) for g,v in rr.items()}))
    rows.append(dict(path=p,file=b,dir=d,lines=n,kept=kept,cls=cls,tok=tok,basis=basis,labels=labs,npub=len(pub),npriv=len(decls)-len(pub),used=used,
                     main=(p in rows_files)))
json.dump(rows,open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'inv4.json'),'w'),ensure_ascii=False,indent=1)
if __name__=='__main__':
    m=[r for r in rows if r['main']]
    print(f'ST-4 files (rule of mkportmap.py): {len(m)}; lines {sum(r["lines"] for r in m)}; kept {sum(r["kept"] for r in m)}; classes {dict(collections.Counter(r["cls"] for r in m))}')
    e=[r for r in rows if not r['main']]
    print('moved/reference files: '+'; '.join(f'{r["dir"]}/{r["file"]} {r["lines"]}/{r["kept"]}/{r["cls"]}' for r in e))
    print('--- table (file | lines | kept | class | tokens | #pub/#priv | consumed by ST-5/ST-6 (script)):')
    for r in rows:
        us='; '.join(f"{nm}:{L}→{'/'.join(sorted(g[3:] for g in c))}" for nm,L,c in r['used'])
        print(f"{r['dir']}/{r['file'][:-5]} | {r['lines']} | {r['kept']} | {r['cls']} | {r['tok']} | {r['npub']}/{r['npriv']} | {us or '-'}")
```
### map4.py
```python
#!/usr/bin/env python3
"""T2134 item 1, second part: where each RBM2D ST-4 file stands for d >= 3.  Rows from inv4.json (inv4.py); the disposition is a hand
classification, and every disposition carries a check that a named string occurs in a named RBM3D file of main (clean copy of 250a118,
RBM_ROOT) or in the paper TeX, printed as `ok`/`MISSING`.  usage: map4.py [--short]"""
import json,os,sys,re
HERE=os.path.dirname(os.path.abspath(__file__))
ROOT=os.environ.get('RBM_ROOT','/Users/junyin/Lean_proof/RBM3D')
PAPER='/Users/junyin/Lean_proof/RBM3D/paper/tex'
rows={r['dir']+'/'+r['file'][:-5]:r for r in json.load(open(os.path.join(HERE,'inv4.json')))}
def has(path,pat):
    p=os.path.join(ROOT,path) if not path.startswith('paper/') else os.path.join(PAPER,path[6:])
    if '*' in path:
        import glob
        ok=False
        for q in glob.glob(p):
            if re.search(pat,open(q,encoding='utf-8').read()): ok=True
        return ok
    return re.search(pat,open(p,encoding='utf-8').read()) is not None
D=[ # key, group, disposition, [(file,pattern)...]
 ('Evolution/Bridge','sum_decay','d=2 bridges D1-D3 -> contract pins: d>=3 counterpart merged, EK-6 `Evolution/Prec.lean` (scale N)',[('RBM3D/Evolution/Prec.lean',r'EK-6.*ticket T2053')]),
 ('Evolution/Case3','sum_decay','d=2 `sum_res_3` + `clt-lemma` (7:100, 7:363-418): no d>=3 counterpart (paper has no `sum_res_3`)',[('paper/*.tex',r'(?!)')]),
 ('Evolution/Case3Defs','sum_decay','d=2 vocabulary of Case 3 / `clt-lemma` (`CltCase1Prec`, `CltCase2Prec`): not needed',[('RBM3D/Induction/Defs.lean',r'(?!)')]),
 ('Evolution/Case4','sum_decay','d=2 alternating sigma, sum-zero: d>=3 counterpart merged, EK-4 `Evolution/SumDecayZero.lean`',[('RBM3D/Evolution/SumDecayZero.lean',r'EK-4')]),
 ('Evolution/Case5','sum_decay','d=2 `2k`-kernel (`eq:double_sum_zero_tensor`, 7:119): no d>=3 counterpart',[('paper/*.tex',r'(?!)')]),
 ('Evolution/Defs','sum_decay','vocabulary: `DecayLoopPT` -> merged S3-07a/b `Induction/DecayLoop{A,B}.lean`; Step-6 `MLExpConcl` etc. -> ST-5',[('RBM3D/Induction/DecayLoopA.lean',r'def STDecayLoopPT')]),
 ('Evolution/KernelExpand','sum_decay','anchored window bound: merged EK-3 `Evolution/SumDecay.lean` `ek_anchor_sum_le` (independent proof)',[('RBM3D/Evolution/SumDecay.lean',r'KernelExpand\.lean')]),
 ('Evolution/LatticeSums','sum_decay','d=2 mixed lattice sum: replaced by merged `(eq:latticesum_d3)` `Kernel/SumDecay.lean`',[('RBM3D/Kernel/SumDecay.lean',r'latticesum_d3')]),
 ('Evolution/XiBounds','sum_decay','kernel `Xi` bounds: merged EK-2 `Evolution/XiPins.lean`',[('RBM3D/Evolution/XiPins.lean',r'EK-2')]),
 ('Evolution/CltSwap','CLT','source of S5-17 (replacement of one real coordinate)',[]),
 ('Evolution/CltPath','CLT','source of S5-17 (resolvent path)',[]),
 ('Evolution/CltResolvent','CLT','source of S5-18 (resolvent expansion)',[]),
 ('Evolution/FarEntry','CLT','source of S5-19 (entry bounds of the far decorrelation)',[]),
 ('Evolution/CltGood','CLT','source of S5-20 (good event)',[]),
 ('Evolution/CltStep','CLT','source of S5-21 (per-step bound)',[]),
 ('Evolution/CltDecorrelation','CLT','source of S5-21 (`CltFarThm` = (eq:bound_isolated))',[]),
 ('Evolution/CltMoments','CLT','partial source of S5-23/S5-24 (moment counting, d=2 balls)',[]),
 ('Path/LemDecCalE','lem_dec_calE','source of S5-05 (= T2039 ST2-36, moved to ST-4 by DECISIONS 28)',[]),
 ('Path/LemDecCalEdif','lem_dec_calE','source of S5-06, S5-07 (= ST2-37, ST2-38)',[]),
 ('Path/LemDecCalEwG','lem_dec_calE','source of S5-08 (= ST2-39)',[]),
 ('Induction/Step45','Step 5 d=2','d=2 Step 5 = Step 4 at k=2 + (53): replaced by `stStep5IV_holds` (case (iv)) and cases (i)-(iii)',[]),
]
short='--short' in sys.argv
tot={}
print(f"{'RBM2D file (c9a24cf)':<28}{'lines':>6}{'kept':>6}{'tok':>5} {'group':<13} disposition (check)")
for key,g,disp,chk in D:
    r=rows[key]
    ok=''
    if chk:
        res=[]
        for f,pat in chk:
            if pat=='(?!)':
                # absence check: label strings of the d=2 file do not occur in the d>=3 paper
                lab={'Evolution/Case3':r'sum_res_3','Evolution/Case5':r'double_sum_zero','Evolution/Case3Defs':r'CltCase1Prec'}[key]
                if key=='Evolution/Case3Defs':
                    import subprocess
                    n=subprocess.run(['grep','-rlw',lab,os.path.join(ROOT,'RBM3D')],capture_output=True,text=True).stdout.strip()
                    res.append('absent in RBM3D' if not n else 'PRESENT')
                else:
                    import glob
                    n=sum(1 for q in glob.glob(PAPER+'/*.tex') if re.search(lab,open(q,encoding='utf-8').read()))
                    res.append(f'`{lab}` in {n} paper files')
            else:
                res.append('ok' if has(f,pat) else 'MISSING')
        ok=' ['+'; '.join(res)+']'
    tot.setdefault(g,[0,0,0]); tot[g][0]+=1; tot[g][1]+=r['lines']; tot[g][2]+=r['kept']
    print(f"{key:<28}{r['lines']:>6}{r['kept']:>6}{r['tok']:>5} {g:<13} {disp}{ok}")
print('-- per group (files, lines, kept):',{k:tuple(v) for k,v in tot.items()})
st4=[v for k,v in tot.items() if k in ('sum_decay','CLT')]
print('-- the 17 ST-4 files (T2002 rule): files',sum(v[0] for v in st4),'lines',sum(v[1] for v in st4),'kept',sum(v[2] for v in st4))
```
### tokens2.py
```python
#!/usr/bin/env python3
"""T2134 item 3: the d = 2 tokens of RBM2D (git archive of c9a24cf) behind each exponent of the d = 3 table: `file:line: text`
(first line where the regex matches in the named file; an assertion fails if there is none)."""
import re,os
R=os.path.join(os.path.dirname(os.path.abspath(__file__)),'rbm2d','RBM2D')
rows=[
 ('eta_u = (1-u) Im m (same in d>=3, loop.etaT)','Path/Scales.lean',r'^def etaT'),
 ('ell_u = min((1-u)^{-1/2}, L): no g (d>=3: min(max(g(1-u)^{-1/2},1),L), 1_2:1121)','Path/Scales.lean',r'^def ellT'),
 ('M_u = W^2 ell_u^2 eta_u  (d>=3: Delta_u = W^{-d}B_{u,0}, B from eq_B_param 1_2:1107)','Path/Scales.lean',r'^def scaleM'),
 ('T_{u,D}(l) = M_u^{-2} exp(-sqrt(l/ell_u)) + W^{-D}  (d>=3 case (iii): (W^d(1-u))^{-2} e^{-sqrt r} + W^{-D}, ell_u=1)','Path/Scales.lean',r'^def tailT'),
 ('ell*_u = (log W)^{3/2} ell_u  (near/far threshold 6 ell*_u of Step 5; d>=3: (log W)^{3/2}, 4(log W)^{3/2} in res_deccalE_*)','Path/Scales.lean',r'^def ellStar'),
 ('Step-5 near-region split 6 ell*_u (d=2 Step 5 = Step 4 at k=2 + (53))','Path/Step2PropsV3.lean',r'6 \* ellStar'),
 ('con_st_ind: M_s^{-1} <= ((1-t)/(1-s))^{30}  (d>=3: Delta_t^{c_d} <= (1-t)/(1-s), c_d <= 1/100, 1_2:1295)','Path/Step2Props.lean',r'^def CondStInd'),
 ('Step 5 d=2: loss exp(sqrt 6 (log W)^{3/4}) absorbed in N^eps (d>=3: (log W)^{10}, eq:assmtlarge 3_5:1954)','Induction/Step45.lean',r'Real\.sqrt 6'),
 ('Step 5 d=2 theorem (Step 4 at k=2 + eq 53; not the d>=3 cases (i)-(iii))','Induction/Step45.lean',r'^theorem step5'),
 ('lem_dec_calE d=2 loss: Lambda^6 (1+log(L^2 W^12))^4 (1+log W)^3 exp(8 (log W)^{3/4})','Path/LemDecCalE.lean',r'^def lossE2'),
 ('lem_dec_calE d=2 hypotheses: floor L^2 W^12 <= W^{D/2}, M_v >= 1','Path/LemDecCalE.lean',r'^def E2Hyp'),
 ('lem_dec_calE d=2 res_deccalE_lk: eta_u^{-1} M_u^{-1} (J*)^2 T_{v,D}  (d>=3: (1-u)^{-1}(W^d|1-u|)^{-1}(J*)^2 T_{u,D})','Path/LemDecCalE.lean',r'^def LemDecCalE_lk'),
 ('lem_dec_calE d=2: neighbour pairs 5 x 5 = 25 (d>=3: (1+2d)^2 = 49)','Path/LemDecCalE.lean',r'5 × 5 = 25'),
 ('CLT d=2: replacement over 2 N^2 real coordinates, N = (WL)^2 (d>=3: N = (WL)^d)','Evolution/CltDecorrelation.lean',r'2 \* \(\(d\.size n'),
 ('CLT d=2: far decorrelation CltFarThm (= eq:bound_isolated, DYYY25 (7.39))','Evolution/CltDecorrelation.lean',r'^def CltFarThm'),
 ('CLT d=2: Case 1 conclusion W^{C tau} ell_t ell_u Lambda max|Z|, one-label local form Y_b, no decay in |a1-a2|','Evolution/Case3Defs.lean',r'^def CltCase1Prec'),
 ('CLT d=2: Case 2 conclusion W^{C tau} ell_u Lambda + W^-D (|Z_ab| <~ (1+|a-b|)^-1)','Evolution/Case3Defs.lean',r'^def CltCase2Prec'),
 ('CLT d=2: CltFarThm takes ONE common one-label form F : LocalForm L W 1 K','Evolution/CltDecorrelation.lean',r'F : ∀ n, LocalForm \(d\.L n\) \(d\.W n\) 1 K'),
 ('CLT d=2: moment counting over balls of Z2 L (d>=3: balls of Zd d L, Defs/Shells, Defs/RadialSum)','Evolution/CltMoments.lean',r'^def CltMoments\.ball'),
 ('CLT d=2: ball cardinality card <= (2R+1)^2 (d>=3: (2R+1)^d; the d=2 count behind the moment sums)','Loop/LatticeCount.lean',r'^theorem card_ball_le'),
 ('LocalForm (vocabulary of the d=2 CLT, not merged in RBM3D)','Induction/Defs.lean',r'^structure LocalForm'),
 ('MLExpInv: translation/negation invariance of the expected tensors (S2.4 of ML:exp)','Evolution/MLExpInv.lean',r'^theorem expInvariant'),
]
for label,f,rx in rows:
    L=open(os.path.join(R,f),encoding='utf-8').read().split('\n')
    hit=[(i+1,l) for i,l in enumerate(L) if re.search(rx,l)]
    assert hit,(f,rx)
    i,l=hit[0]
    print(f"{f}:{i}: {l.strip()[:110]}  <-  {label}")
```
### probeparse.py
```python
"""Shared parser of the probe: top-level declarations with namespace, line, docstring and statement text."""
import re
PROBE='/Users/junyin/Lean_proof/RBM3D-wt/T2134/RBM3D/Probe/T2134Pins.lean'
def load():
    L=open(PROBE,encoding='utf-8').read().split('\n')
    if L and L[-1]=='': L.pop()
    return L
STARTERS=('/--','/-!','theorem ','def ','abbrev ','namespace ','end ','open ','variable','section','set_option','noncomputable','#print','private ','@[','instance ','lemma ','example')
def decls():
    L=load(); ns=[]; out=[]; i=0
    while i<len(L):
        l=L[i]
        m=re.match(r'^namespace (\S+)',l)
        if m: ns.append(m.group(1)); i+=1; continue
        m=re.match(r'^end (\S+)',l)
        if m and ns and ns[-1]==m.group(1): ns.pop(); i+=1; continue
        m=re.match(r'^(theorem|def|abbrev)\s+(\S+)',l)
        if m and not l.startswith('theorem of'):
            kind,name=m.group(1),m.group(2)
            # docstring: walk back over lines to a '/--' start if the preceding non-empty line ends a docstring
            j=i-1
            while j>=0 and L[j]=='' : j-=1
            doc=None
            if j>=0 and L[j].rstrip().endswith('-/'):
                k=j
                while k>=0 and not L[k].startswith('/-'): k-=1
                if k>=0 and L[k].startswith('/--'): doc=(k+1,j+1)
            # statement
            if kind=='theorem':
                e=i
                while e<len(L) and ':=' not in L[e]: e+=1
                stmt=L[i:e+1]
                stmt[-1]=stmt[-1][:stmt[-1].index(':=')+2]
            else:
                e=i+1
                while e<len(L) and not L[e].startswith(STARTERS) and not (L[e]=='' and (e+1>=len(L) or L[e+1].startswith(STARTERS))): e+=1
                stmt=L[i:e]
                while stmt and stmt[-1]=='': stmt.pop()
            out.append(dict(kind=kind,short=name,full='.'.join(ns)+'.'+name if ns else name,ns='.'.join(ns),line=i+1,doc=doc,stmt=stmt))
        i+=1
    return out
```
### statements.py
```python
#!/usr/bin/env python3
"""Print the statement (docstring stripped) of the named declarations of the probe, with their line numbers.
usage: statements.py [--oneline] [--max N] name1 name2 ...   (--oneline joins the lines with one space; --max truncates with ' ...')"""
import sys,os,re
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from probeparse import decls
D={d['short']:d for d in decls()}
a=sys.argv[1:]; one='--oneline' in a; mx=None
if '--max' in a: i=a.index('--max'); mx=int(a[i+1]); del a[i:i+2]
names=[x for x in a if not x.startswith('--')]
for n in names:
    d=D[n]
    if one:
        t=re.sub(r'\s+',' ',' '.join(x.strip() for x in d['stmt'])).strip()
        if mx and len(t)>mx: t=t[:mx]+' ...'
        print(f"L{d['line']}: {t}")
    else:
        print(f"-- L{d['line']} {d['full']}")
        print('\n'.join(d['stmt']))
```
### pins.py
```python
#!/usr/bin/env python3
"""T2134 item 2: the pins of the probe, one row each: line, name, paper cite (first `1_2:`/`3_5:` cite of the docstring), registry class and
proof ticket (the `Registry class: **X** (...)` sentence of the docstring), compiled consumers (theorems of the probe whose statement or proof
mentions the pin; the instance `inst_*` of the pin itself is listed last).  Everything is read from the probe by script."""
import re,sys,os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from probeparse import decls,load
L=load(); D=decls()
PINS=['STStep5I','STStep5II','STStep5III','STStep5IV','STStep5','STEtermsMid','STDuhamelI','STIniTermI','STCltFar','STCltIso','STExpInv',
      'STDuhamelII','STIniTermII','STWardII','STTailtoTail','STLemDecCalE','STPfStep5','STNewKLKL']
byshort={d['short']:d for d in D}
# body range of every declaration: from its line to the line before the next declaration/docstring start at column 0
starts=sorted((d['doc'][0] if d['doc'] else d['line']) for d in D)
def body(d):
    i=d['line']-1
    j=len(L)
    for s in starts:
        if s>d['line']: j=s-1; break
    return '\n'.join(L[i:j])
def doc(d):
    if not d['doc']: return ''
    a,b=d['doc']; return ' '.join(x.strip() for x in L[a-1:b])
rows=[]
CONCL={'STStep5I':'STStep5Concl','STStep5II':'STStep5Concl','STStep5III':'STStep5Concl','STStep5IV':'STStep5Concl','STStep5':'STStep5Concl',
       'STEtermsMid':'STEtermsMidConcl','STDuhamelI':'STDuhamelConcl','STIniTermI':'STIniTermConcl','STCltFar':'STCltFarConcl',
       'STCltIso':'STCltIsoConcl','STDuhamelII':'STDuhamelConcl','STIniTermII':'STIniTermConcl','STWardII':'STWardIIConcl',
       'STLemDecCalE':'STLemDecCalEConcl','STPfStep5':'STPfConcl','STNewKLKL':'STNewKLKLAt'}
for p in PINS:
    d=byshort[p]; t=doc(d)
    tc=doc(byshort[CONCL[p]]) if p in CONCL else ''
    cite=re.search(r'`?((?:3_5|1_2):\d+(?:[-–]\d+)?)',t+' '+tc)
    cls=re.search(r'Registry class:?\s*\*\*(\w+)\*\*',t+' '+tc,re.I)
    if cls is None and p=='STStep5IV': cls=re.search(r'(proved)',t)
    full=t+' '+tc
    k=re.search(r'Registry class',full,re.I)
    ids=re.findall(r'S5-\d\d(?:\.\.S5-\d\d)?',full[k.start():] if k else '')
    def num(x): return [int(v) for v in re.findall(r'\d\d',x)]
    rng=[num(x) for x in ids if '..' in x]
    out=[]
    for x in ids:
        n=num(x)
        if '..' not in x and any(a<=n[0]<=b for a,b in rng): continue
        if any(x==y or ('..' in y and '..' in x and num(x)[0]>=num(y)[0] and num(x)[1]<=num(y)[1] and x!=y) for y in out): continue
        out.append(x)
    ids=out
    if p=='STStep5IV': ids=['S5-02']
    cons=[]
    for e in D:
        if e['kind']!='theorem' or e['short'].startswith('inst_') : continue
        if re.search(r'\b'+p+r'\b',body(e)): cons.append(e['short'])
    inst=[e['short'] for e in D if e['short'].startswith('inst_') and re.search(r'\b'+p+r'\b',' '.join(e['stmt']))]
    rows.append((d['line'],p,d['ns'].replace('RBM.Gauss.','').replace('RBM.',''),cite.group(1) if cite else '-',cls.group(1) if cls else '?',','.join(sorted(set(ids))) or '-',cons,inst))
print(f"{'line':>5} {'pin':<14} {'paper':<12} {'class':<9} {'ticket':<14} compiled consumers (skeleton/bridge theorems) | instance")
for r in rows:
    print(f"L{r[0]:<4d} {r[1]:<14} {r[3]:<12} {r[4]:<9} {r[5]:<14} {' '.join(r[6]) or '-'} | {' '.join(r[7]) or '-'}")
print(f"-- {len(rows)} pins; namespaces: {sorted(set(r[2] for r in rows))}")
```
### instances.py
```python
#!/usr/bin/env python3
"""T2134 item 7: the compiled nonempty instances (namespace RBM.Gauss.T2134Inst): name, line, the pin it instantiates, and the data
(first sentence of the docstring when there is one; the signature head otherwise).  Verbatim from the probe by script."""
import sys,os,re
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from probeparse import decls,load
L=load()
ds=[d for d in decls() if d['ns']=='RBM.Gauss.T2134Inst']
names={'szG','szG_WO','szG_admissible','szG_W_tendsto','flow_zG','szG_reg4','szB_reg5I','szB_reg5II','sz0_reg5III','InstIng5Concl','tailTD_nonneg'}
print(f"namespace RBM.Gauss.T2134Inst: {len(ds)} declarations; instances (inst_*): {sum(1 for d in ds if d['short'].startswith('inst_'))}; data/regime lemmas: {sum(1 for d in ds if d['short'] in names)}")
for d in ds:
    if not (d['short'].startswith('inst_') or d['short'] in ('szG','szG_WO','flow_zG','szG_reg4','szB_reg5I','szB_reg5II','sz0_reg5III')): continue
    doc=''
    if d['doc']:
        a,b=d['doc']; doc=' '.join(x.strip() for x in L[a-1:b]).replace('/--','').replace('-/','').strip()
        doc=re.sub(r'\s+',' ',doc)
    head=d['stmt'][0].strip()
    print(f"L{d['line']:<5d} {d['short']:<22s} {(doc or head)[:150]}")
```
### inst_groups.py
```python
#!/usr/bin/env python3
"""T2134 item 7, grouped: the `inst_*` theorems of namespace RBM.Gauss.T2134Inst grouped by the data tuple named in their docstring
(`(sz, z, s, t)`), the instance data (flow, time sequences) being the last two arguments of the instance theorem.  Read from the probe."""
import sys,os,re,collections
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from probeparse import decls,load
L=load(); D=[d for d in decls() if d['ns']=='RBM.Gauss.T2134Inst' and d['short'].startswith('inst_')]
def doc(d):
    if not d['doc']: return ''
    a,b=d['doc']; return ' '.join(x.strip() for x in L[a-1:b])
G=collections.OrderedDict()
for d in D:
    t=doc(d)
    m=re.search(r'\((sz0|szB|szG), (z0|zB), (\S+?), (\S+?)\)',t)
    st=' '.join(d['stmt'])
    m2=re.search(r'\b(sz0|szB|szG) (z0|zB) (sInst|\(fun _ => [\d /]+\)) (tInst|\(fun _ => [\d /]+\))',st)
    def nm(x): return {'sInst':'0','tInst':'1/16'}.get(x, x.replace('(fun _ => ','').rstrip(')').replace(' ',''))
    if m: key=f"data ({m.group(1)}, {m.group(2)}, {m.group(3)}, {m.group(4)})"
    elif m2: key=f"data ({m2.group(1)}, {m2.group(2)}, {nm(m2.group(3))}, {nm(m2.group(4))})"
    elif d['short']=='inst_ing5': key='generic shape (any data)'
    else: key='deterministic pin, own data'
    G.setdefault(key,[]).append(d['short'])
print(f"{len(D)} instance theorems (RBM.Gauss.T2134Inst), by data")
for k,v in G.items(): print(f"{k}: {' '.join(v)}")
```
### extreme.py
```python
#!/usr/bin/env python3
"""T2134 item 7: the regime inequalities of the four compiled data sets, recomputed in exact fractions (an independent check of what the Lean
instances `szB_reg5I`, `szB_reg5II`, `sz0_reg5III`, `szG_reg4` prove), the boundary hit by each, and (eq:WO) `W^{-d/2+fd} <= g <= 1/fd` at n = 0..3
(fd = 1/10).  Sizes (from the probe): szB: L=4, W_n=n+4, g=1; szG: szB with g=5; sz0: L_n=4(n+1), W_n=(2(n+1))^5, g_n=(2(n+1))^-6; d=3."""
from fractions import Fraction as F
d=3
def line(name,g2,L,s,t):
    a,b=g2/L**2,g2/L**d
    x,y=1-t,1-s
    r={'(i)':a<=x<=y<=g2,'(ii)':b<=x<=y<=a,'(iii)':y>=x>=g2,'(iv)':x<=y<=b}
    hit=[k for k,v in r.items() if v]
    eq=[]
    if x==a: eq.append('1-t = g^2/L^2')
    if y==a: eq.append('1-s = g^2/L^2')
    if x==g2: eq.append('1-t = g^2')
    if y==b: eq.append('1-s = g^2/L^3')
    if s==0: eq.append('s = 0')
    print(f"{name:<8} g^2={g2} L={L} (s,t)=({s},{t}): g^2/L^2={a} g^2/L^3={b} 1-t={x} 1-s={y} | regimes holding {hit} | boundary hit: {eq or 'none'}")
line('szB',F(1),4,F(7,8),F(15,16))
line('szB',F(1),4,F(15,16),F(31,32))
line('szG',F(25),4,F(5,8),F(3,4))
for n in (0,1,3):
    g=F(1,(2*(n+1))**6); line(f'sz0 n={n}',g*g,4*(n+1),F(0),F(1,16))
print('(eq:WO), fd=1/10: W^{-d/2+fd} <= g <= 10')
for nm,Wf,gf in (('szB',lambda n:n+4,lambda n:1.0),('szG',lambda n:n+4,lambda n:5.0),('sz0',lambda n:(2*(n+1))**5,lambda n:(2*(n+1))**-6.0)):
    print(nm,[ (n, round(Wf(n)**(-d/2+0.1),5), gf(n), (Wf(n)**(-d/2+0.1)<=gf(n)<=10)) for n in (0,1,2,3)])
```
### clash.py
```python
#!/usr/bin/env python3
"""Name-clash check of the new public names of the probe against RBM3D/ (main worktree, Probe excluded) and RBM3D.lean:
 (1) full-name clash: a merged declaration whose short name equals a new short name (namespace-insensitive, hence conservative);
 (2) textual grep -w of each new short name in RBM3D/ outside Probe (count of files)."""
import sys,os,re,subprocess
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from probeparse import decls
import os as _os
ROOT=_os.environ.get('RBM_ROOT','/Users/junyin/Lean_proof/RBM3D')
D=decls()
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(def|theorem|lemma|abbrev|structure|class|instance|inductive)\s+([^\s({:\[]+)')
merged={}      # short -> list of (file:line, full name, private?)
for dp,dn,fn in os.walk(os.path.join(ROOT,'RBM3D')):
    if '/Probe' in dp: continue
    for f in sorted(fn):
        if f.endswith('.lean'):
            p=os.path.join(dp,f); ns=[]
            for i,l in enumerate(open(p,encoding='utf-8'),1):
                m=re.match(r'^namespace (\S+)',l)
                if m: ns.append(m.group(1)); continue
                m=re.match(r'^end (\S+)',l)
                if m and ns and ns[-1]==m.group(1): ns.pop(); continue
                m=decl.match(l)
                if m:
                    nm=m.group(2)
                    merged.setdefault(nm.split('.')[-1],[]).append((f'{os.path.relpath(p,ROOT)}:{i}','.'.join(ns+[nm]),'private' in l.split(m.group(1))[0]))
shorts=sorted({d['short'] for d in D})
newfull={d['full'] for d in D}
same=[(s,w) for s in shorts for w in merged.get(s,[]) if w[1] in newfull]      # identical full name
sameshort=[(s,w) for s in shorts for w in merged.get(s,[])]                    # identical short name, any namespace
clash=same
print(f'new public declarations in the probe: {len(D)} ({sum(1 for d in D if d["kind"]=="def")} def, {sum(1 for d in D if d["kind"]=="abbrev")} abbrev, {sum(1 for d in D if d["kind"]=="theorem")} theorem); distinct short names {len(shorts)}')
print('namespaces:',sorted({d['ns'] for d in D}))
print(f'(1a) merged declarations with the same FULL name as a new one: {len(same)}'+(' -> '+'; '.join(f'{w[1]} @ {w[0]}' for s_,w in same) if same else ''))
print(f'(1b) merged declarations with the same SHORT name (other namespace): {len(sameshort)}'+(' -> '+'; '.join(f'{w[1]} @ {w[0]}{" (private)" if w[2] else ""}' for s_,w in sameshort) if sameshort else ''))
# (2) grep -w over RBM3D/ and RBM3D.lean excluding Probe
pat='|'.join(re.escape(s) for s in shorts)
r=subprocess.run(['grep','-rlwE',pat,'RBM3D','RBM3D.lean','--include=*.lean'],cwd=ROOT,capture_output=True,text=True)
files=[f for f in r.stdout.split('\n') if f and not f.startswith('RBM3D/Probe/')]
print(f'(2) grep -rlwE <{len(shorts)} new short names> RBM3D RBM3D.lean (Probe excluded): {len(files)} files'+(' -> '+', '.join(files[:8]) if files else ''))
```
### route.py
```python
#!/usr/bin/env python3
"""T2134 item 4: route per pin.  Every merged declaration named in a row is resolved in the clean copy of main (RBM_ROOT = 250a118) to `name@file:line`;
an unresolved name prints `NOT FOUND` (the row is then wrong).  RBM2D sources are `file:line` at c9a24cf of the scratch archive (a line check is run)."""
import re,os,sys
ROOT=os.environ.get('RBM_ROOT','/Users/junyin/Lean_proof/RBM3D')
HERE=os.path.dirname(os.path.abspath(__file__))
R2=os.path.join(HERE,'rbm2d','RBM2D')
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(def|theorem|lemma|abbrev|structure|class|instance)\s+([^\s({:\[]+)')
where={}
for dp,dn,fn in os.walk(os.path.join(ROOT,'RBM3D')):
    if '/Probe' in dp: continue
    for f in sorted(fn):
        if not f.endswith('.lean'): continue
        p=os.path.join(dp,f); ns=[]
        for i,l in enumerate(open(p,encoding='utf-8'),1):
            m=decl.match(l)
            if m: where.setdefault(m.group(2).split('.')[-1],[]).append((os.path.relpath(p,os.path.join(ROOT,'RBM3D')),i))
def loc(n):
    w=where.get(n)
    return f"{n}@{w[0][0]}:{w[0][1]}" if w else f"{n}@NOT FOUND"
def src2(f,pat):
    L=open(os.path.join(R2,f),encoding='utf-8').read().split('\n')
    for i,l in enumerate(L,1):
        if re.search(pat,l): return f"{f}:{i}"
    return f"{f}:NOT FOUND"
ROWS=[
 ('STStep5R/I..IV, STStep5 (S5-02, S5-03, S5-29)','1_2:1379-1388; 3_5:1939-1940',[src2('Induction/Step45.lean',r'^theorem step5')+' (d=2: from Step 4 at k=2 and Step2Eq53PTV3, docstring :1255-1257; only the analogue of case (iv))'],
  ['STGdecayW','STDecay','STDecayStrong','STLKU','STConStInd','STFlow','precomp_param','of_eventually_empty','of_subset','of_subset_union','conStInd_const'],'medium'),
 ('STTailtoTail (S5-04)','3_5:2344-2362; Fable 2026-10-04 section 2',[src2('Path/UTransport.lean',r'^theorem tailtoTail')+' (d=2 form; false at d>=3 with tailT, DECISIONS 33)'],
  ['UN','EKsgn','ukerNonneg','ukerRowSum','prop5Decay_holds','norm_Theta_le','Theta','zdistInf'],'medium'),
 ('STLemDecCalE (S5-05..S5-09)','3_5:2310-2340',[src2('Path/LemDecCalE.lean',r'^def LemDecCalE_lk'),src2('Path/LemDecCalEdif.lean',r'^theorem lemDecCalE_dif'),src2('Path/LemDecCalEwG.lean',r'^theorem lemDecCalE_wG')],
  ['STELKLKM','STEGt','STee','STEEk','STGdecayW','stK2decay_holds','STJhatM'],'medium'),
 ('STPfStep5 (S5-10, S5-11)','3_5:2369-2383; Fable section 4(3)',['none in RBM2D (Induction/Step45.lean derives step5 from Step 4 and Step2Eq53PTV3); the paper cites [YY_25, section 5.3]'],
  ['stoppedDuhamel105','grid_expansion_all','StoppedAzumaN','STGridMart','STGridRepN','Ugen','STLmaxU','STLKU'],'high'),
 ('STNewKLKL (S5-12)','3_5:628-654, 1968',['none'],['stNewKLK_holds','nkl_bound2','STNewKLKAt','STJhatM','STprof'],'medium'),
 ('STEtermsMid (S5-13)','3_5:1961-1979',['none'],['STLWT','stEMn2Exp_holds','stEMn2Poly_holds','stK2decay_holds','STNewKLK','STprof'],'medium'),
 ('STDuhamelI (S5-14, S5-15)','3_5:1941-2070',['none (RBM2D Path/Expansion.lean has the d=2 grid Duhamel expansion, ST2-26)'],
  ['Ugen','STEKSumNdecay','STGridRepN','STGridMart','StoppedAzumaN','norm_Theta_le','tailT_natCast'],'high'),
 ('STIniTermI (S5-16)','3_5:2072-2172',['none'],['Theta','prop5Decay_holds','STKward','tailT_natCast','STAvgU'],'medium'),
 ('STCltIso (S5-17..S5-21)','3_5:2245-2248; DYYY25 (7.39), RBSO1D (A.112)',[src2('Evolution/CltDecorrelation.lean',r'^def CltFarThm'),src2('Evolution/CltSwap.lean',r'^theorem cltTelescope'),src2('Evolution/CltPath.lean',r'^theorem cltPath_bound'),src2('Evolution/CltResolvent.lean',r'^theorem cltFarGeomHalf'),src2('Evolution/FarEntry.lean',r'^theorem farEntryDecayPT '),src2('Evolution/CltGood.lean',r'^theorem cltFarEntry_whp'),src2('Evolution/CltStep.lean',r'^theorem cltStep')],
  ['STGbEXPij','STGdecayW','STLocalEntryU','Gres','seqP'],'medium'),
 ('STExpInv (S5-22)','3_5:2196-2200',[src2('Evolution/MLExpInv.lean',r'^theorem expInvariant')+' (class c at T2002, Step 6)'],['seqP','Lloop','STKloop','Theta'],'medium'),
 ('STCltFar (S5-23..S5-25)','3_5:2173-2249 (eq:2p_product_pair 2226-2235)',[src2('Evolution/CltMoments.lean',r'^theorem cltMomentBound')+' (d=2 balls: '+src2('Evolution/CltMoments.lean',r'^def CltMoments\.ball')+')'],
  ['Theta','prop5Decay_holds','sum_radial_pow_le','radC'],'high'),
 ('STDuhamelII, STIniTermII, STWardII (S5-26..S5-28)','3_5:2251-2283',['none'],
  ['zeroModeSet','STEKNonzero','Prop8ZeroMode','KLK_ward','norm_zeroModeSet_UN_le'],'medium'),
]
print(f"{'pin (ticket)':<48} paper | RBM2D source (c9a24cf) | merged RBM3D declarations reused (main 250a118) | risk")
for pin,paper,s2,names,risk in ROWS:
    print(f"{pin} | {paper} | {'; '.join(s2)} | {', '.join(loc(n) for n in names)} | {risk}")
```
### split.py
```python
#!/usr/bin/env python3
"""T2134 item 6: split table of sub-gate ST-4 (Step 5) and the count against DECISIONS 9 O2 (25/40/50).
Estimates: (m) measured on the probe (lines of the probe ranges listed), (p) port: kept lines (inv4.json, RBM2D 0c1330a) x 1.15 rounded to 10,
(n) new work: lines of the nearest merged analogue (wc -l, main) rounded to 50.  `kept` of a port is read from inv4.json, not typed."""
import json,os,sys
HERE=os.path.dirname(os.path.abspath(__file__))
inv={ (r['dir']+'/'+r['file'][:-5]):r for r in json.load(open(os.path.join(HERE,'inv4.json')))}
K=lambda f: inv[f]['kept']
P=lambda n: int(round(n*1.15/10.0))*10
PROBE='/Users/junyin/Lean_proof/RBM3D-wt/T2134/RBM3D/Probe/T2134Pins.lean'
PL=open(PROBE,encoding='utf-8').read().split('\n')
if PL and PL[-1]=='': PL.pop()
probe_total=len(PL)
def mark(prefix,after=0):
    for i,l in enumerate(PL,1):
        if i>after and l.startswith(prefix): return i
    raise SystemExit('marker not found: '+prefix)
S7=mark('/-! ## 7.'); C3=mark('/-! ### Case (iii)'); C2=mark('/-! ### Case (ii)'); E7=mark('end RBM.Gauss.Sizes',C2)
S8=mark('/-! ## 8.'); T4=mark('/-! ### The four targets'); ING=mark('/-! ### The ingredients'); SK=mark('/-! ### The skeletons at the data')
DP=mark('/-! ### The deterministic pins'); E8=mark('end RBM.Gauss.T2134Inst'); S9=mark('/-! ## 9.')
def rng(*r): return sum(b-a+1 for a,b in r)
RA1=((1,S7-1),(S8,T4-1),(ING,SK-1),(DP,E8)); RA2=((S7,C3-1),(T4,ING-1),(SK,DP-1)); RA3=((C3,E7),)
A1,A2,A3=rng(*RA1),rng(*RA2),rng(*RA3)
fmt=lambda R: ', '.join(f'{a}-{b}' for a,b in R)
rows=[
# id, file, statements, source, deps, est, basis, role, risk
('S5-01','Induction/Step5Pins','tailTD, regimes, STIngR5, STStep5R/Concl, every ingredient pin of this report, their instances','probe '+fmt(RA1),
 'merged only (Defs, Step34Pins, Step2Defs, Kernel/Evolution)',A1,'m','prover','low'),
('S5-02','Induction/Step5Kit','Prec kit, assembly STDecay/STDecayStrong at t, comparisons, case (i) from pins, case (iv) PROVED','probe '+fmt(RA2),
 'S5-01',A2,'m','prover','low'),
('S5-03','Induction/Step5Cases','case (iii) from pf_step5, case (ii) from pins, skeleton instances','probe '+fmt(RA3),
 'S5-01, S5-02',A3,'m','prover','low'),
('S5-04','Induction/TailtoTail','STTailtoTail (neiwuj), T_{u,D}, every sigma, C=C_d^2','new: 3_5:2344-2362 + docs/claude-team/fable/2026-10-04-tailtotail.md; analogue Induction/ContractPt 638',
 'Propagator (Theta, rows, signs), Kernel/Evolution (UN, EKsgn), Defs/Tail',800,'n','prover-hard','medium'),
('S5-05','Path/LemDecCalE','lem_dec_calE: res_deccalE_lk, GijGEX / def_ELKLK inputs (= T2039 ST2-36)','RBM2D Path/LemDecCalE.lean (kept %d)'%K('Path/LemDecCalE'),
 'S5-01 (T2039 ST2-01)',860,'T2039','prover','medium'),
('S5-06','Path/LemDecCalEdif','res_deccalE_dif part 1 (= ST2-37)','RBM2D Path/LemDecCalEdif.lean (kept %d, half)'%K('Path/LemDecCalEdif'),'S5-05',830,'T2039','prover','medium'),
('S5-07','Path/LemDecCalEdif','res_deccalE_dif part 2 (= ST2-38)','RBM2D Path/LemDecCalEdif.lean (other half)','S5-06',830,'T2039','prover','medium'),
('S5-08','Path/LemDecCalEwG','res_deccalE_wG (= ST2-39)','RBM2D Path/LemDecCalEwG.lean (kept %d)'%K('Path/LemDecCalEwG'),'S5-05',1390,'T2039','prover','medium'),
('S5-09','Induction/LemDecCalEPrec','STLemDecCalE: the three bounds as Prec, uniform in u in [s,t], J* control','new interface over S5-05..08 (RBM2D deterministic E2Hyp/lossE2); analogue Induction/QVN 874',
 'S5-05..S5-08, S5-01, STGdecayW',700,'n','prover-hard','medium'),
('S5-10','Induction/PfStep5Alg','lem:pf_step5 part 1: closure algebra J*_{t^T} <~ C + log W + W^{2eps-d/2} < W^eps in 3 terms','new: 3_5:2369-2383, Fable 2026-10-04 section 4(3)',
 'S5-04, S5-09',700,'n','prover-hard','high'),
('S5-11','Induction/PfStep5','lem:pf_step5 part 2: stopping time T of (eq:def_TTT), the Prec conclusion STPfStep5','new: 3_5:2369-2383 (paper: "analogous to (2.76) of [YY_25 5.3]", no proof); analogue Induction/GridDuhamelN 778 + StoppedAzumaN',
 'S5-10, STGridMart, StoppedAzumaN',900,'n','prover-max','high'),
('S5-12','Induction/NewKLKL','STNewKLKL: sharp lem:newKLK at ell=L, floor kept (paper-delta T2134a)','adapt merged Induction/NewKLK.lean (nkl_bound2, 1332 lines)',
 'S5-01, merged STNewKLK',600,'n','prover-hard','medium'),
('S5-13','Induction/EtermsMid','STEtermsMid: (S5WG+M000), (S5WG+M) for E^{LKxLK}, E^{G~}, (E x E)^{M}','new: 3_5:1961-1979; analogue Induction/Step2Core 1771 (part)',
 'S5-12, STLWT (LW), STEMn2Exp/Poly (ST-2), STK2decay, STGdecayW',900,'n','prover-hard','medium'),
('S5-14','Induction/Step5Kernel','kernel facts of (iois-mtx): ||Theta^{(+,-)}||_{inf->inf}=1/(1-t), (uwp2-92kj), (uwftgwesj), rho-losses','new: 3_5:1983-2065; analogue Evolution/SumDecayZero 1746 (part)',
 'EK pins STEKSum*, Propagator, Kernel/Evolution',700,'n','prover-hard','medium'),
('S5-15','Induction/DuhamelI','STDuhamelConcl engine and STDuhamelI: Duhamel + Azuma on the grid, exponent closure rho A^{-1/3}, rho A^{-1/2}, rho^3 A^{-1/4} <= A^{-1/5}','new: 3_5:1941-2070; analogue Induction/GridDuhamelN 778 + GridDriftN 1261',
 'S5-01, S5-12, S5-13, S5-14, STGridRepN, STGridMart',1400,'n','prover-max','high'),
('S5-16','Induction/IniTermI','STIniTermI: sigma1=sigma2 short range, regime reduction, f^{near}, Ward term g_a; f^{far} from S5-25','new: 3_5:2072-2172, 2176-2181',
 'S5-14, S5-26',1100,'n','prover-hard','medium'),
('S5-17','Evolution/CltSwapPath','CltSwap (replacement of one real coordinate) + CltPath (resolvent path), LocalForm vocabulary with k labels (RBM2D Induction/Defs.lean:151, not merged)','RBM2D Evolution/CltSwap.lean (kept %d) + CltPath.lean (kept %d)'%(K('Evolution/CltSwap'),K('Evolution/CltPath')),
 'merged Gauss/Model, Gauss/Envelope',P(K('Evolution/CltSwap')+K('Evolution/CltPath')),'p','prover','low'),
('S5-18','Evolution/CltResolvent','CltResolvent: resolvent expansion along a Gaussian coordinate','RBM2D Evolution/CltResolvent.lean (kept %d)'%K('Evolution/CltResolvent'),
 'S5-17, merged Gauss/LoopEnvelope; Case3Defs replaced by S5-01 vocabulary',P(K('Evolution/CltResolvent')),'p','prover','medium'),
('S5-19','Evolution/FarEntry','FarEntry: entry bounds for the far decorrelation (needs GbEXP, KellStar, PerTimeCalc)','RBM2D Evolution/FarEntry.lean (kept %d)'%K('Evolution/FarEntry'),
 'merged Green pins (STGbEXPij), Induction/PerTimeCalc',P(K('Evolution/FarEntry')),'p','prover-hard','medium'),
('S5-20','Evolution/CltGood','CltGood: good event, sub-Gaussian tail of the swap error','RBM2D Evolution/CltGood.lean (kept %d)'%K('Evolution/CltGood'),'S5-19',P(K('Evolution/CltGood')),'p','prover','medium'),
('S5-21','Evolution/CltStep','CltStep + CltDecorrelation: per-step bound, telescoping; STCltIso = (eq:bound_isolated), generalising CltFarThm (one common one-label form, CltDecorrelation.lean:277-284) to 2p per-label two-label forms','RBM2D Evolution/CltStep.lean (kept %d) + CltDecorrelation.lean (kept %d)'%(K('Evolution/CltStep'),K('Evolution/CltDecorrelation')),
 'S5-17, S5-18, S5-20',P(K('Evolution/CltStep')+K('Evolution/CltDecorrelation')),'p','prover-hard','medium'),
('S5-22','Evolution/ExpInvMean','STExpInv (translation/reflection of E L^{(2)}) + mean part of f^{far}: first difference -> second difference, BD2','RBM2D Evolution/MLExpInv.lean (kept 818, shared with ST-5) + new: 3_5:2184-2210',
 'S5-01, merged Propagator Prop5*/BD1, BD2',1200,'n','prover-hard','medium'),
('S5-23','Evolution/CltMoments1','moment counting of f^{far} at d>=3, part 1: clusters, two-label loops, BD1 weights, k>=2','partial port RBM2D Evolution/CltMoments.lean (kept %d, 199 Z2/zdist2 uses) + new counting (preflight table row 7)'%K('Evolution/CltMoments'),
 'S5-21, Defs/Shells, Defs/RadialSum (Loop.LatticeCount replaced)',1300,'p/2 + new','prover-hard','high'),
('S5-24','Evolution/CltMoments2','moment counting part 2: 2p-th moment sum over clusters (eq:2p_product_pair), isolation removal of singletons','as S5-23',
 'S5-23',1300,'p/2 + new','prover-hard','high'),
('S5-25','Evolution/CltFar','STCltFar: assembly of f^{far} <~ A^{-6/5}/(|a1-a2|^{d-2}+1) from isolation, counting, mean part','new: 3_5:2173-2249',
 'S5-21, S5-22, S5-24',900,'n','prover-max','high'),
('S5-26','Induction/DuhamelII','STDuhamelII: Q^{(1)} = zeroModeSet {0} for mixed signs, Q empty for same sign (paper-delta T2134g)','new: 3_5:2251-2283 (paper: "similar argument"); merged Induction/ZeroModeCalc 820',
 'S5-15, S5-14',700,'n','prover-hard','medium'),
('S5-27','Induction/IniTermII','STIniTermII: (zYU2) absolute values, prop:ThfadC0, 1-s <= g^2/L^2','new: 3_5:2275-2281',
 'S5-14',600,'n','prover-hard','medium'),
('S5-28','Induction/WardII','STWardII (zYU1): Ward identities WI_calL, WI_calK, Gt_avgbound_flow','new: 3_5:2257-2262',
 'merged KLWard (Loop), STKward',600,'n','prover','medium'),
('S5-29','Induction/Step5Chain','STStep5 general: cases (i)-(iv) glued by intermediate times, the assembly at t','new: 3_5:1939 ("by adding intermediate times"); no RBM2D counterpart (RBM2D step5 = Induction/Step45.lean:1258)',
 'S5-02, S5-03, S5-15, S5-16, S5-26..S5-28',900,'n','prover-hard','medium'),
]
# S5-16 depends on S5-25 (STCltFar), fix the ids used in the rows above
rows=[list(r) for r in rows]
for r in rows:
    if r[0]=='S5-16': r[4]='S5-14, S5-25'
    if r[0]=='S5-29': r[4]='S5-02, S5-03, S5-15, S5-16, S5-26, S5-27, S5-28'
    if r[0]=='S5-26': r[4]='S5-15, S5-14'
tot=sum(r[5] for r in rows)
if __name__=='__main__':
    print('| id | new file (RBM3D/) | statements | source | deps | est lines | basis | role | risk |')
    print('|---|---|---|---|---|---|---|---|---|')
    for r in rows: print('| '+' | '.join(str(x) for x in r)+' |')
    n=len(rows)
    print(f'probe lines {probe_total}; moved by S5-01..03: {A1+A2+A3}; section 9 (print-axioms block, not moved): lines {S9}-{probe_total} = {probe_total-S9+1}; unassigned blank/separator lines: {probe_total-(A1+A2+A3)-(probe_total-S9+1)}')
    print(f'tickets {n} (of which 4 are T2039 ST2-36..39, counted in ST-4 by DECISIONS 28); est lines {tot}; mean {tot//n}; min {min(r[5] for r in rows)}; max {max(r[5] for r in rows)}')
    print('role count:',{k:sum(1 for r in rows if r[7]==k) for k in sorted(set(r[7] for r in rows))},'| risk:',{k:sum(1 for r in rows if r[8]==k) for k in sorted(set(r[8] for r in rows))})
    print('O2 (DECISIONS 9): band 25/40/50:', 'below 25' if n<25 else ('in 25-40' if n<=40 else ('in 41-50' if n<=50 else 'OVER 50')), '-> question to Jun:', 'yes' if n>50 else 'no')
    print('tickets outside 600-1500:',[(r[0],r[5]) for r in rows if not 600<=r[5]<=1500])
```
### reg.py
```python
#!/usr/bin/env python3
"""T2134 registry classes (DECISIONS 16, 20): for every `Prop` the pins of the probe take as a hypothesis (the premises of `STIngR5` and the
pins used as hypotheses by the skeletons), the class under which `RBM3D/Test/Axioms.lean` of main (clean copy of 250a118) already lists it
(borrowedProps / owedProps / structuralProps), or `not listed`; plus the proof ticket of the pin when the premise is one of this report's pins."""
import re,os,sys
ROOT=os.environ.get('RBM_ROOT','/Users/junyin/Lean_proof/RBM3D')
t=open(os.path.join(ROOT,'RBM3D/Test/Axioms.lean'),encoding='utf-8').read()
def block(name):
    m=re.search(r'def '+name+r' : List Name :=(.*?)\n\n',t,re.S)
    names=set()
    for line in m.group(1).split('\n'):
        mm=re.match(r"^\s*\[?`(RBM\.[A-Za-z0-9_.']+)",line)
        if mm: names.add(mm.group(1))
    return names
cls={'borrowed':block('borrowedProps'),'owed':block('owedProps'),'structural':block('structuralProps')}
prem=['STFlow','STKbound','STKward','STLK','STDecay','STDecayStrong','STConStInd','STStep1Loop','STStep2Concl','STGdecayW','STLocalEntryU','STAvgU',
      'STLmaxU','STLKU','STNewKLK','STLWT','STEMn2Exp','STEMn2Poly','STGridMart','STGridRepN','STK2decay','STEKSumNdecay','STEKSumRes1','STEKSumRes2NAL',
      'STEKSumRes2','STEKNonzero','STGbEXPij','STOptL2','STDecayLoopPT']
print(f"registry of main: {len(cls['borrowed'])} borrowed, {len(cls['owed'])} owed, {len(cls['structural'])} structural names")
for p in prem:
    where=[k for k,v in cls.items() if any(n.split('.')[-1]==p for n in v)]
    print(f"{p:<16} {','.join(where) if where else 'not listed'}")
```
### axioms.py
```python
#!/usr/bin/env python3
"""Group the `#print axioms` lines of `lake env lean RBM3D/Probe/T2134Pins.lean` (captured in out/lean_env.txt) by axiom set; compare with the
theorems declared in the probe (probeparse)."""
import re,sys,os,collections
HERE=os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0,HERE)
from probeparse import decls
txt=open(os.path.join(HERE,'out','lean_env.txt'),encoding='utf-8').read().split('\n')
rx=re.compile(r"'(.+?)' depends on axioms: \[([^\]]*)\]")
g=collections.OrderedDict(); order=[]
for l in txt:
    m=rx.search(l)
    if m: g.setdefault(m.group(2),[]).append(m.group(1)); order.append(m.group(1))
thms={d['full'] for d in decls() if d['kind']=='theorem'}
print(f"print-axioms lines: {len(order)}; theorems declared in the probe: {len(thms)}; theorems without a line: {sorted(thms-set(order))}; lines without a theorem: {sorted(set(order)-thms)}")
for k,v in g.items():
    print(f"[{k}] : {len(v)} declarations")
    short=[x.replace('RBM.Gauss.Sizes.','S.').replace('RBM.Gauss.T2134Inst.','I.') for x in v]
    line=''
    for x in short:
        if len(line)+len(x)+2>140: print('   '+line); line=''
        line+=x+', '
    if line: print('   '+line.rstrip(', '))
```
### mathlib_names.py
```python
#!/usr/bin/env python3
"""Mathlib/core theorems that the probe's declarations use directly AND that appear by name in the probe source (comments stripped).
Input: uses_mathlib.out (metaprogram uses_mathlib.lean: constants referenced by the declarations of RBM3D.Probe.T2134Pins, kind theorem,
module Mathlib*/Init*/Std*/Batteries*).  Output: `name <TAB> defining module`, one per line."""
import re,sys,os
HERE=os.path.dirname(os.path.abspath(__file__))
src=open('/Users/junyin/Lean_proof/RBM3D-wt/T2134/RBM3D/Probe/T2134Pins.lean',encoding='utf-8').read()
src=re.sub(r'/-.*?-/','',src,flags=re.S); src=re.sub(r'--[^\n]*','',src)
toks=set(re.findall(r"[A-Za-z_][A-Za-z_0-9'₀-₉.]*",src))
rows=[]
for l in open(os.path.join(HERE,'uses_mathlib.out'),encoding='utf-8'):
    if '\t' not in l: continue
    n,m=l.rstrip('\n').split('\t'); parts=n.split('.')
    if any('.'.join(parts[k:]) in toks for k in range(len(parts))) and not n.startswith('Mathlib.Meta') and not n.startswith('Mathlib.Tactic'):
        rows.append((n,m))
for n,m in rows: print(f'{n}\t{m}')
print(f'-- {len(rows)} names (verified present: they are constants of the elaborated environment of RBM3D.Probe.T2134Pins)')
```
### uses_mathlib.lean
```lean
import Lean
import RBM3D.Probe.T2134Pins
open Lean Elab Command

/-- Mathlib theorems referenced directly by the declarations of the probe module. -/
run_cmd do
  let env ← getEnv
  let some midx := env.getModuleIdx? `RBM3D.Probe.T2134Pins | throwError "module not found"
  let mut used : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some midx then
      match ci with
      | .thmInfo v => for c in v.value.getUsedConstants do used := used.insert c
      | .defnInfo v => for c in v.value.getUsedConstants do used := used.insert c
      | _ => pure ()
  let mut out : Array (String × String) := #[]
  for c in used.toList do
    if let some ci := env.find? c then
      if let some m := env.getModuleIdxFor? c then
        let mn := env.header.moduleNames[m.toNat]!
        let s := mn.toString
        if (s.startsWith "Mathlib" || s.startsWith "Init" || s.startsWith "Std" || s.startsWith "Batteries") && ci.isTheorem then
          let nm := c.toString
          unless (nm.splitOn "match_").length > 1 || (nm.splitOn "_private").length > 1 || (nm.splitOn "proof_").length > 1 do
            out := out.push (s, nm)
  let sorted := out.qsort (fun a b => a.2 < b.2)
  for (m, n) in sorted do
    logInfo m!"{n}\t{m}"
```
### newklkl.py
```python
import numpy as np, itertools, sys
# STNewKLKL check, d=3, W=2, L=3 (N=216), E=0 (m=i), flow H_u = sqrt(u) X, z_u = i(1-u).  X complex Hermitian, E|X_xy|^2 = W^-d S^B_[x][y] (diag real).
# For every sigma in {+,-}^2 and block labels (a1,a2):  LK = L^{(2)} - K^{(2)},  L^{(2)}_{s,(a,b)} = W^{-2d} sum_{x in a, y in b} G(s1)_{xy} G(s2)_{yx},
# K^{(2)}_{s,(a,b)} = W^{-d} m1 m2 Theta_{t m1 m2}(a,b);  E^{LKxLK}_{a1,a2} = W^d sum_{x,y} LK_{(x,a2)} S^B_{xy} LK_{(a1,y)};
# J^ = max |LK| / prof,  prof(r) = W^-d max(T_u(r), W^-D),  T_u(r) = B_{u,r} exp(-sqrt(r/l_u))  (r<=1 here, l=L).
# printed: max over samples and (sigma,a) of  R_sharp = (1-u)|E| / (J^2 prof + J^ W^{-d-D})   [STNewKLKL],   R_old = (1-u)|E| / ((J^+J^2) prof)  [merged STNewKLK].
d=3; W=2; L=3; N=(W*L)**d
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
blocks=list(itertools.product(range(L),repeat=3)); bidx={b:i for i,b in enumerate(blocks)}
sites=list(itertools.product(range(W*L),repeat=3))
sblock=np.array([bidx[tuple(c//W for c in s)] for s in sites])
order=np.argsort(sblock,kind='stable'); sites=[sites[i] for i in order]; sblock=sblock[order]
nb=L**3
def dist(a,b): return max(min((x-y)%L,(y-x)%L) for x,y in zip(a,b))
def l1(a,b): return sum(min((x-y)%L,(y-x)%L) for x,y in zip(a,b))
def SBmat(g):
    S=np.zeros((nb,nb))
    for i,a in enumerate(blocks):
        for j,b in enumerate(blocks):
            if i==j: S[i,j]=1/(1+2*d*g*g)
            elif l1(a,b)==1: S[i,j]=g*g/(1+2*d*g*g)
    return S
Dm=np.array([[dist(a,b) for b in blocks] for a in blocks])
def run(g,xfrac,Dexp,nsamp=20):
    SB=SBmat(g); x=g*g*xfrac; u=1-x
    ell=min(max(g/np.sqrt(x),1.0),L)
    B=lambda r:(1/((g*g+x)*(r+1.0)**(d-2))+1/(L**d*x))
    Tu=lambda r:B(r)*np.exp(-np.sqrt(r/ell))
    prof=W**-d*np.maximum(Tu(Dm.astype(float)),W**(-Dexp))
    m=1j; xi={}
    Th=lambda xi_: np.linalg.inv(np.eye(nb)-xi_*SB)
    Kk={}
    for s1 in (1,-1):
        for s2 in (1,-1):
            m1=m if s1==1 else np.conj(m); m2=m if s2==1 else np.conj(m)
            Kk[(s1,s2)]=W**-d*m1*m2*Th(u*m1*m2)
    # variance profile on the fine lattice
    Sx=np.array([[SB[sblock[i],sblock[j]]/W**d for j in range(N)] for i in range(N)])
    best_sharp=0; best_old=0; Jmax=0
    for _ in range(nsamp):
        A=rng.normal(size=(N,N))*np.sqrt(Sx/2)+1j*rng.normal(size=(N,N))*np.sqrt(Sx/2)
        X=np.triu(A,1); X=X+X.conj().T+np.diag(np.diag(A).real*np.sqrt(2))   # diagonal real with variance S_xx
        H=np.sqrt(u)*X; z=1j*x
        Gp=np.linalg.inv(H-z*np.eye(N)); Gm=Gp.conj().T
        Gs={1:Gp,-1:Gm}
        LK={}
        for s1 in (1,-1):
            for s2 in (1,-1):
                Mx=Gs[s1]*Gs[s2].T                     # G(s1)_{xy} G(s2)_{yx}
                T=np.zeros((nb,nb),dtype=complex)
                for bi in range(nb):
                    for bj in range(nb):
                        T[bi,bj]=Mx[np.ix_(sblock==bi,sblock==bj)].sum()
                LK[(s1,s2)]=T*W**(-2*d)-Kk[(s1,s2)]
        J=max((np.abs(LK[k])/prof).max() for k in LK); Jmax=max(Jmax,J)
        for k in LK:
            M=LK[k]; E=W**d*(M@SB@M)               # E[a1,a2] = W^d sum M[a1,y] S[x,y] M[x,a2]
            rs=(1-u)*np.abs(E)/(J**2*prof+J*W**(-d-Dexp))
            ro=(1-u)*np.abs(E)/((J+J**2)*prof)
            best_sharp=max(best_sharp,rs.max()); best_old=max(best_old,ro.max())
    return best_sharp,best_old,Jmax,ell
print("   g  x/g^2   D |  max R_sharp  max R_old   J^max   l_u")
for g in (0.7,0.3):
    for xf,lab in ((1.0,'1'),(1/9,'1/L^2'),(1/27,'1/L^3')):
        for Dexp in (0.0,3.0):
            rs,ro,J,ell=run(g,xf,Dexp,nsamp=20)
            print(f"{g:4.1f} {lab:6s} {Dexp:3.0f} | {rs:10.3f} {ro:10.3f} {J:9.3f} {ell:5.2f}",flush=True)
```
### ttt2.py
```python
import numpy as np, sys
# tailtoTail (STTailtoTail), every charge: worst case |U^sigma o A|(a) over |A_b|<=T_{s,D}(|b1-b2|) is (|p|*|p|*T_s)(a1-a2) with p = FFT^-1[(1-s xi S)/(1-t xi S)],
# xi = m(sigma1) m(sigma2): xi = 1 for sigma=(+,-); xi = m^2 for (+,+); xi = conj(m)^2 for (-,-).  d=3, periodic l_inf distance, T_{u,D}(r)=(W^d(1-u))^-2 e^-sqrt r
# (the W^-D part contributes exactly rho^2 W^-D for xi=1 and at most rho'^2 W^-D with rho' = sum|p| otherwise: reported).
d=3
def dist(L):
    i=np.indices((L,L,L)); i=np.minimum(i,L-i); return i.max(axis=0)
def run(L,W,g,xs,xt,xi,label):
    s,t=1-xs,1-xt
    D=dist(L)
    k=2*np.pi*np.arange(L)/L; K=np.meshgrid(k,k,k,indexing='ij')
    S=(1+2*g*g*sum(np.cos(x) for x in K))/(1+2*d*g*g)
    Pk=(1-s*xi*S)/(1-t*xi*S); p=np.fft.ifftn(Pk); ap=np.abs(p)
    Ts=(W**d*xs)**-2*np.exp(-np.sqrt(D)); Tt=(W**d*xt)**-2*np.exp(-np.sqrt(D))
    F=np.fft.fftn
    UT=np.real(np.fft.ifftn(F(ap)*F(ap)*F(Ts)))
    R=UT/Tt
    rho2=(ap.sum())**2; rho=xs/xt
    print(f"{label:9s} L={L} g={g:<5g} 1-s={xs:<5g} 1-t={xt:<7g} rho={rho:7.1f} sum|p|={ap.sum():9.2f} (rho for xi=1) | max_a R={R.max():.4f} at r={D.flat[R.argmax()]} | R(r=0,1,2,3)={R[0,0,0]:.3f},{R[1,0,0]:.3f},{R[2,0,0]:.3f},{R[3,0,0]:.3f} | W^-D part factor sum|p|^2/rho^2={rho2/rho**2:.3f}")
    return R.max()
m=lambda th: np.exp(1j*th)
for (g,xs,xt) in ((0.03,0.9,9e-4),(0.1,1.0,1e-2),(0.05,0.5,2.5e-3)):   # last: 1-t = g^2 exactly
    run(16,10,g,xs,xt,1.0,'(+,-)')
    for th in (0.3,np.pi/2,2.9):
        run(16,10,g,xs,xt,m(th)**2,f'(+,+) th={th:.2f}')
```
### strongweak.py
```python
import numpy as np
# Case (iii): ratio  T_{u,D}(r) / [ Delta_u^{1/5} W^{-d}B_{u,r} e^{-sqrt r} + W^{-D} ]   (l_u = 1 for 1-u >= g^2),  d=3,
# T_{u,D}(r) = (W^d(1-u))^-2 e^{-sqrt r} + W^-D ,  Delta_u = W^-d B_{u,0},  B_{u,r} = (g^2+x)^-1 (r+1)^{2-d} + (L^d x)^-1,
# worst r over 0..L//2 (periodic L^inf distance).  Lean: st5_compare_IIIb  (ratio <= 4  iff  y^{4/5}((D log W)^2+1)^{d-2} <= 1, y = (W^d x)^-1).
d=3; fd=0.1
def ratio(W,L,x,D,g):
    r=np.arange(0,L//2+1,dtype=float)
    Bt=lambda rr: 1/((g*g+x)*(rr+1)**(d-2))+1/(L**d*x)
    Delta=W**-d*Bt(0.0)
    tgt=Delta**0.2*W**-d*Bt(r)*np.exp(-np.sqrt(r))+W**-D
    T=(W**d*x)**-2*np.exp(-np.sqrt(r))+W**-D
    R=T/tgt; y=1/(W**d*x)
    cond=y**0.8*((D*np.log(W))**2+1)**(d-2)
    return R.max(), int(r[R.argmax()]), cond
print("W        L      g          x         D |  max_r T/target  at r | y^{4/5}((D logW)^2+1)^{d-2} (<=1 => Lean constant 4)")
for W in (2.0**5,2.0**10,2.0**20,2.0**40,2.0**80):
    g=W**(-d/2+fd)
    for L in (4,400,40000):
        for x in (g*g,0.3):
            D=4.0
            Rm,rm,c=ratio(W,L,x,D,g)
            print(f"2^{int(np.log2(W)):<3d} {L:6d} {g:9.3e} {x:9.3e} {D:3.0f} | {Rm:12.4g} {rm:6d} | {c:10.4g}")
# threshold of the Lean constant 4 at the extreme x = g^2 (y = W^{-2 fd}): (D log W)^2 + 1 <= W^{(4/5) 2 fd}, d = 3 (d-2 = 1), D = 4
import math
fdd=0.1; Dd=4.0
f=lambda w: math.exp(0.8*2*fdd*w)-((Dd*w)**2+1)
lo,hi=1.0,400.0
for _ in range(200):
    mid=(lo+hi)/2
    if f(mid)<0: lo=mid
    else: hi=mid
print(f"threshold at x=g^2, D={Dd:g}, fd={fdd:g}: ln W = {lo:.2f}, log2 W = {lo/math.log(2):.1f} (the hypothesis y^(4/5)((D log W)^2+1) <= 1 of st5_compare_IIIb fails below it, and the ratio T/target exceeds 4 for large L, see the table; it holds above it)")
```
### check_a.py
```python
#!/usr/bin/env python3
"""Replay of section (a)'s four script blocks against the report: compares the output of seq.py, exps.py, clt.py, ttt.py (same pipes as in (a)) with the fenced blocks."""
import subprocess,sys,os
HERE=os.path.dirname(os.path.abspath(__file__))
rep=open('/Users/junyin/Lean_proof/RBM3D/docs/reports/T2134-prove.md',encoding='utf-8').read().split('\n')
blocks=[];cur=None
for l in rep:
    if l.startswith('```'):
        if cur is None: cur=[]
        else: blocks.append(cur); cur=None
    elif cur is not None: cur.append(l)
cmds=[('seq.py | awk',['bash','-c',f"python3 {HERE}/seq.py | awk 'NR<=2 || /^ +(0|9|999) /'"]),
      ('exps.py | grep -v',['bash','-c',f"python3 {HERE}/exps.py | grep -v 'r=1:\\|r=2:'"]),
      ('clt.py',['python3',HERE+'/clt.py']),('ttt.py',['python3',HERE+'/ttt.py'])]
for (n,c),b in zip(cmds,blocks[:4]):
    out=subprocess.run(c,capture_output=True,text=True).stdout.rstrip('\n').split('\n')
    print(f"{n:<18} block {len(b):>2} lines, rerun {len(out):>2} lines: {'identical' if out==b else 'DIFFERENT'}")
```
### seq.py
```python
import math
d,cd,dd,eps=3,1/400,0.1,0.1
print("sz0_n: L=4(n+1) W=(2(n+1))^5 g=(2(n+1))^-6 (Defs/Sizes.lean sz0); pair (s,t) per case with rho=Delta_t^-cd (extremal con_st_ind)")
print("   n      A=g^2W^d  WO:g>=W^(-d/2+fd)  case:  Delta_t      rho    1-t        1-s<=bound  N(1-t)>=N^eps  s>=0,t<1")
for n in (0,1,9,99,999):
    m=2*(n+1); L=4*(n+1); W=m**5; g=m**-6.; g2=g*g; N=(W*L)**d; A=g2*W**d
    wo = g>=W**(-d/2+dd) and g<=1/dd
    B=lambda x:(g2+x)**-1+(L**d*x)**-1
    for nm,xt,ub in (("(i) ",g2/2,g2),("(ii)",g2/L**2*0.33,g2/L**2),("(iii)",0.3,1.0)):
        lo={"(i) ":g2/L**2,"(ii)":g2/L**d,"(iii)":g2}[nm]
        Dl=W**-d*B(xt); rho=Dl**-cd; xs=xt*rho
        ok=(lo<=xt<=xs<=ub) if nm!="(iii)" else (g2<=xt<=xs<=1)
        print(f"  {n:4d}  {A:11.4g}  {wo!s:5}  {nm:5}  {Dl:.4e}  {rho:.5f}  {xt:.3e}  {ok!s:5}  {N*xt>=N**eps!s:5} ({N*xt:.3g}>={N**eps:.3g})  {xs<=1 and xt>0}")
```
### exps.py
```python
import math
d,L,W,g,dd,cd=3,4,32,1/64,0.1,1/400
N=(W*L)**d; g2=g*g; A=g2*W**d
B=lambda x,K:(g2+x)**-1*(K+1)**-(d-2)+(L**d*x)**-1
ell=lambda x:min(max(g/math.sqrt(x),1),L)
Dl=lambda x:W**-d*B(x,0)
print(f"sz0: d={d} L={L} W={W} g=1/64 N={N} g^2={g2:.4e} g^2/L^2={g2/L**2:.4e} g^2/L^d={g2/L**d:.4e} A=g^2W^d={A} W^(2fd)={W**(2*dd):.3f} cd={cd}")
cases=[("(i)  g2/L2<=1-t<=1-s<=g2",1e-4,lambda xs:g2/L**2<=1e-4 and xs<=g2),
       ("(ii) g2/Ld<=1-t<=1-s<=g2/L2",5e-6,lambda xs:g2/L**d<=5e-6 and xs<=g2/L**2),
       ("(iii) 1-s>=1-t>=g2",0.3,lambda xs:xs>=0.3 and 0.3>=g2)]
for name,xt,ok in cases:
    rho=Dl(xt)**-cd; xs=xt*rho
    print(f"--- case {name}: 1-t={xt:g} rho=Delta_t^-cd={rho:.5f} 1-s={xs:.6g} case-ok={ok(xs)}  Delta_t={Dl(xt):.4g} Delta_s={Dl(xs):.4g}")
    print(f"    B_t0*g^2={B(xt,0)*g2:.3f} B_t0*(1-t)={B(xt,0)*xt:.4f}  ell_t={ell(xt):.3f} ell_s={ell(xs):.3f} sqrt(rho)={rho**.5:.4f}  (1-s)^2 ell_s^4/g^4={(xs**2)*ell(xs)**4/g**4:.4f}")
    for r in (0,1,2):
        tgtI=Dl(xt)**.2*W**-d*B(xt,r)*math.exp(-(r/ell(xt))**.5)
        tgtIII=Dl(xt)**2*math.exp(-r**.5)
        print(f"    r={r}: (Gdecay_flow) Delta^(1/5)W^-d B_tr e^-(r/ell)^.5={tgtI:.4e} | (Gdecay+s<g) Delta^2 e^-sqrt r={tgtIII:.4e} | ratio(iii)/(i)={tgtIII/tgtI:.3f}")
print("--- case (i) closure of rho-losses vs target A^-1/5 (rho<=Delta_t^-cd, Delta_t>=1/(2A)):")
rho=Dl(1e-4)**-cd
for nm,val in (("rho*A^-1/3 / A^-1/5 [L-K x L-K]",rho*A**(-1/3+1/5)),("rho*A^-1/2 / A^-1/5 [G-circ]",rho*A**(-1/2+1/5)),("rho^3*A^-1/4 / A^-1/5 [martingale, uuwmskiow x uwftgwesj]",rho**3*A**(-1/4+1/5))):
    print(f"    {nm} = {val:.4f} <=1 {val<=1}")
print(f"    max rho allowed by rho^3 A^-1/20<=1: A^(1/60)={A**(1/60):.4f}; (2A)^cd={(2*A)**cd:.4f}<=A^(1/60) {(2*A)**cd<=A**(1/60)}")
print("--- case (ii): Ward term (zYU1): A^-1 (L^d x)^-1 vs A^-1/5 B_tr e^-(r/L)^.5, r=L/2, x=5e-6")
x=5e-6;r=L//2
print(f"    ratio={A**-1*(L**d*x)**-1/(A**-.2*B(x,r)*math.exp(-(r/L)**.5)):.4f}  (A^-4/5={A**-.8:.4f})")
print(f"    (1-s)L^2/g^2 = {x*1.003*L**2/g2:.4f}<=1")
print("--- (eq:assmtlarge) crossover: W^(d cd) = (log W)^10 ; x=log W")
f=lambda x:d*cd*x-10*math.log(x)
lo,hi=100,1e6
for _ in range(200):
    m=(lo+hi)/2
    (lo:=m) if f(m)<0 else (hi:=m)
print(f"    at sz0 W^(d cd)={W**(d*cd):.4f} <= (log W)^10={math.log(W)**10:.3e}; crossover log W ~ {hi:.0f} (W=e^{hi:.0f})")
print("--- case (iii) closure exponents (derived from Fable/YY25 sketch), per eps; closure iff each exponent <= eps:")
for nm,a,b in (("E^{LK x LK}: 2eps-2fd",2,2),("E^{G~}: 1.5eps-fd",1.5,1),("mart: 1.5eps-fd/2",1.5,.5)):
    print(f"    {nm}: <=eps iff eps<={b/(a-1):.3g}*fd -> eps<={b/(a-1)*dd:.3f} at fd={dd}")
print("--- (iii) => (Gdecay_flow): needs (r+1)Delta^(4/5)<~1 for r<=(D log W)^2 (else e^-sqrt r<=W^-D)")
print(f"    sz0 x=0.3: Delta^(-4/5)={Dl(.3)**-.8:.1f}; x=g2: Delta^(-4/5)={Dl(g2)**-.8:.1f}; L/2+1={L//2+1}")

print("--- CLT cluster exponent (eq:2p_product_pair): d-(d-2)k+(d+2)(k-1)+2 == 4k for all d>=3,k>=1:",all(d_-(d_-2)*k_+(d_+2)*(k_-1)+2==4*k_ for d_ in range(3,12) for k_ in range(1,9)))
print("--- (|x|^(d-1)+1)^-k summable on Z^d iff (d-1)k>d: d=3:",[(k_,(3-1)*k_>3) for k_ in (1,2,3)],"; d=2 k=2:",(2-1)*2>2)
```
### clt.py
```python
import numpy as np, itertools, sys
d=3
def theta(L,g,t):
    k=2*np.pi*np.arange(L)/L
    K=np.meshgrid(k,k,k,indexing='ij')
    S=(1+2*g*g*sum(np.cos(x) for x in K))/(1+2*d*g*g)
    return np.real(np.fft.ifftn(1/(1-t*S)))
def dist(L):
    x=np.arange(L); x=np.minimum(x,L-x)
    return np.maximum.reduce(np.meshgrid(x,x,x,indexing='ij'))
def run(L,g,s_x,t_x,R,r0,ks):
    Th=theta(L,g,1-t_x); D=dist(L); ls=max(g/np.sqrt(s_x),1); lt=min(max(g/np.sqrt(t_x),1),L)
    Bp=np.where(D<=R,1/(D+1.0),0.0)          # unit-amplitude profile 1/(|x|^{d-2}+1)
    ys=[y for y in itertools.product(range(-R,R+1),repeat=3) if max(abs(v) for v in y)<=R]
    assert abs(Th.sum()*t_x-1)<1e-9
    for k in ks:
        a2=np.array([k,0,0]); idx=np.indices((L,L,L))
        dA1=np.maximum.reduce([np.minimum(idx[i]%L,(L-idx[i])%L) for i in range(3)])
        dA2=np.maximum.reduce([np.minimum((idx[i]-a2[i])%L,(L-(idx[i]-a2[i]))%L) for i in range(3)])
        far=(np.minimum(dA1,dA2)>r0)
        Ta1=Th; Ta2=np.roll(Th,tuple(a2),axis=(0,1,2))        # Ta2[b]=Theta[b-a2]
        trv=np.zeros_like(Th); G=np.zeros_like(Th); G2=np.zeros_like(Th); V=np.zeros_like(Th)
        for y in ys:
            w=Bp[tuple(v%L for v in y)]
            sh=np.roll(Ta2,tuple(-v for v in y),axis=(0,1,2)); shm=np.roll(Ta2,tuple(v for v in y),axis=(0,1,2))
            df=sh-Ta2
            trv+=w*np.abs(df)*Ta1; G+=w*df; G2+=w*0.5*np.abs(sh+shm-2*Ta2); V+=(w*df*Ta1)**2
        c=(s_x**2)*(k+1)
        qt=c*trv[far].sum(); qe=c*abs((Ta1*G)[far].sum()); qb=c*(Ta1*G2)[far].sum(); qf=c*np.sqrt(V[far].sum()); qf1=c*np.sqrt(((trv)[far]**2).sum())
        print(f"{L:3d} {lt:5.2f} {s_x/t_x:6.1f} {k:3d} {int(far.sum()):5d} {qt:8.3f}  {qe:8.3f}  {qb:8.3f}  | {qf:8.4f}  {qf1:8.4f} | {qt/qe:7.1f} {qt/qf1:7.1f}")
if __name__=="__main__":
    print("  L  ell_t   rho   k  far#  Q_triv  Q_mean-exact Q_mean-BD2 | Q_fl(y-indep) Q_fl(b1-indep,y-coh) | triv/Q_mean triv/Q_fl(b1)   [g=0.3, 1-s=g^2, R=r0=2 (L=5: R=r0=1)]")
    run(5,0.3,0.09,0.0144,1,1,[2])
    for lt in (3,6,12):
        run(31,0.3,0.09,0.09/lt**2,2,2,[4,8] if lt==12 else [4])
```
### ttt.py
```python
import numpy as np
from clt import theta, dist
d=3; L=16; W=10; Dexp=8
D=dist(L)
def run(g,xs,xt):
    s,t=1-xs,1-xt
    k=2*np.pi*np.arange(L)/L; K=np.meshgrid(k,k,k,indexing='ij')
    S=(1+2*g*g*sum(np.cos(x) for x in K))/(1+2*d*g*g)
    Pk=(1-s*S)/(1-t*S); P=np.real(np.fft.ifftn(Pk)); rho=xs/xt
    Th=theta(L,g,t)
    ok=dict(Pnonneg=P.min()>=-1e-12, rowsum=abs(P.sum()-rho)<1e-9*rho, cond=(g*g<=xt+1e-15 and 0<=s<=t<1))
    q=2*d*t*g*g/(1+2*d*g*g-t)
    l1=np.indices((L,L,L)); l1=sum(np.minimum(l1[i],L-l1[i]) for i in range(3))   # periodic l1
    nb=np.where(l1>0,(xt*Th)/np.maximum(q,1e-300)**l1,0).max()                    # (1-t)Theta(0,x)<=q^{|x|_1}
    Pt=P/rho; off=np.where(D>0,Pt-xt*Th,-1).max()                                # Ptilde_{0x}<=(1-t)Theta(0,x), x!=0
    Ts=(W**d*xs)**-2*np.exp(-np.sqrt(D)); Tt=lambda r:(W**d*xt)**-2*np.exp(-np.sqrt(r))
    F=np.fft.fftn
    UT=np.real(np.fft.ifftn(F(P)*F(P)*F(Ts)))                                      # (U o T_s)(a1-a2)=(P*P*f)(a1-a2)
    R=UT/Tt(D)
    sel=[(0,0,0),(1,0,0),(2,0,0),(3,0,0),(8,8,8)]
    # exact worst-case constant C_d' := sum_x Ptilde_{0x} e^{sqrt|x|} ; (neiwuj) holds with C_d'^2 (periodic sqrt-triangle)
    Cd=(Pt*np.exp(np.sqrt(D))).sum()
    # W^-D part: const profile -> (P*P*c) = rho^2 c exactly
    print(f"g={g:<5g} 1-s={xs:<6g} 1-t={xt:<7g} rho={rho:7.1f} | P>=0 {ok['Pnonneg']} rowsum=rho {ok['rowsum']} g2<=1-t {ok['cond']} | q={q:.4f} max(1-t)Th/q^|x|1={nb:.3f} offdiag Pt-(1-t)Th<=0 {off<=1e-12} | R(r=0,1,2,3)={R[0,0,0]:.3f},{R[1,0,0]:.3f},{R[2,0,0]:.3f},{R[3,0,0]:.3f} max_a R={R.max():.4f} C'^2={Cd**2:.2f}")
    # calT-profile contrast (B_{u,r}e^{-sqrt(r/ell)}) NOT recomputed; amplitude ratio would be rho
    return R.max()
print(f"d=3 L={L} periodic l_inf; tail T_{{u,D}}(r)=(W^d(1-u))^-2 e^-sqrt r (+W^-D part contributes exactly rho^2 W^-D)")
for g,xs,xt in ((0.03,0.9,9e-4),(0.01,0.9,9e-4),(0.01,0.5,5e-4),(0.1,1.0,1e-2)):
    run(g,xs,xt)
```

## P.10 Repair, audit round 1 (Sun Oct  4 15:49:05 UTC 2026; probe commit `7b2b789`; scripts in `repair/` of the T2134 scratch directory)
### P.10a the `szCL` data at `n = 0, 1` (`python3 repair/szcl.py`)
```
szCL n=0 L=15925248 W=2^24: g^2/L^2 = 1-t = 1/253613523861504, 1-s = 1 | (i): True | (log W)^5 l_s = 1274041 <= l_t = 15925248: True | L/2 = 7962624 >= 10 (log W)^3 l_s = 46037: True
szCL n=1 L=19531250 W=2^25: g^2/L^2 = 1-t = 1/381469726562500, 1-s = 1 | (i): True | (log W)^5 l_s = 1562526 <= l_t = 19531250: True | L/2 = 9765625 >= 10 (log W)^3 l_s = 52035: True
```
### P.10b the index-set checks (`lake env lean repair/IndexCheck.lean`, exit 0, no error or warning; its `#check` output omitted)
```lean
import RBM3D.Probe.T2134Pins
/-! T2134 repair: the index sets of the instance conclusions at their data (compiled; scratch, not in the repo). -/
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.T2134Inst RBM.Path

-- TimeIcc s t n (index of STGdecayW, STIdx2, STIdx2P) at the five data: nonempty for every n
example (n : ℕ) : Nonempty (TimeIcc (fun _ => (7 / 8 : ℝ)) (fun _ => 15 / 16) n) := ⟨⟨7 / 8, by norm_num, by norm_num⟩⟩
example (n : ℕ) : Nonempty (TimeIcc (fun _ => (15 / 16 : ℝ)) (fun _ => 31 / 32) n) := ⟨⟨15 / 16, by norm_num, by norm_num⟩⟩
example (n : ℕ) : Nonempty (TimeIcc sInst tInst n) := ⟨⟨0, le_rfl, by simp [tInst]⟩⟩
example (n : ℕ) : Nonempty (TimeIcc (fun _ => (5 / 8 : ℝ)) (fun _ => 3 / 4) n) := ⟨⟨5 / 8, by norm_num, by norm_num⟩⟩
example (n : ℕ) : Nonempty (TimeIcc sCL tCL n) := ⟨⟨0, le_rfl, (szCL_hst n).le⟩⟩
-- sign classes of STIdx2P: nonempty
example : Nonempty {σ : Fin 2 → Bool // STSigAll σ} := ⟨⟨![true, false], trivial⟩⟩
example : Nonempty {σ : Fin 2 → Bool // STSigMixed σ} := ⟨⟨![true, false], fun h => by simp at h⟩⟩
example : Nonempty {σ : Fin 2 → Bool // STSigSame σ} := ⟨⟨![true, true], rfl⟩⟩
-- the condition `ilambda² ≤ 1 - t` of STDecayStrongU, STPfConcl, STDecayStrong: holds at sz0, fails at szB and szG
example (n : ℕ) : sz0.lam n ^ 2 ≤ 1 - tInst n := sz0_reg5III n
example (n : ℕ) : ¬ (szB.lam n ^ 2 ≤ 1 - (15 / 16 : ℝ)) := by simp [szB]
example (n : ℕ) : ¬ (szB.lam n ^ 2 ≤ 1 - (31 / 32 : ℝ)) := by simp [szB]
example (n : ℕ) : ¬ (szG.lam n ^ 2 ≤ 1 - (3 / 4 : ℝ)) := by simp [szG]; norm_num
-- the pair index of the third bound of STLemDecCalEConcl at sz0 (a' = a): nonempty
example (n : ℕ) : Nonempty {q : STIdx2 sz0 sInst tInst n × (Fin 2 → Zd 3 (sz0.L n)) //
    ∀ i : Fin 2, ((zdistInf 3 (sz0.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤
      Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)} :=
  ⟨⟨((⟨0, le_rfl, by simp [tInst]⟩, ![true, false], 0), 0), fun i => by
    have h0 : zdistInf 3 (sz0.L n) (0 : Zd 3 (sz0.L n)) = 0 := by simp [zdistInf]
    simp only [sub_zero, Pi.zero_apply]
    rw [h0, Nat.cast_zero]
    exact Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (sz0.W_pos n))) _⟩⟩
-- the CLT data (szCL): the index set of STCltFarConcl and the premises of STCltIsoConcl (p = 1)
#check @szCL_cltFar_index_nonempty
#check @szCL_cltIso_witness
```
### P.10c `repair/pinmatch.py` (the witness types of the probe against the pin text)
```python
import re
s=open('/Users/junyin/Lean_proof/RBM3D-wt/T2134/RBM3D/Probe/T2134Pins.lean').read()
def norm(x): return re.sub(r'\s+',' ',x).strip()
# STCltFarConcl index type
d=s[s.index('def STCltFarConcl'):]; u=d[d.index('(U := fun n => {')+len('(U := fun n => {'):d.index('})')]
pin=norm(u).replace('(sz.','(szCL.').replace(' d (',' 3 (').replace('(s n)','(sCL n)').replace('(t n)','(tCL n)')
w=s[s.index('theorem szCL_cltFar_index_nonempty'):]; w=w[w.index('Nonempty {')+len('Nonempty {'):w.index('} := by')]
print('STCltFarConcl U (sz,d,s,t := szCL,3,sCL,tCL) == szCL_cltFar_index_nonempty:', pin==norm(w))
# STCltIsoConcl premises (window, isolation) at p = 1
d=s[s.index('def STCltIsoConcl'):]; pr=d[d.index('(∀ k,'):d.index(') →\n      ‖∫')+1]
pin=norm(pr).replace('(sz.','(szCL.').replace(' d (',' 3 (').replace('(s n)','(sCL n)')
w=s[s.index('theorem szCL_cltIso_witness'):]; w=w[w.index('(∀ k,'):w.index(' := by')]
print('STCltIsoConcl premises (p := 1) == szCL_cltIso_witness:', pin.replace(') → (∃ i',') ∧ (∃ i')==norm(w))
```
### P.10d `repair/szcl.py`
```python
#!/usr/bin/env python3
"""T2134 repair: the szCL data at n = 0, 1 (m = n+24, L = 2m^5, W = 2^m, g = 1, s = 0, 1-t = L^-2): regime (i) in exact fractions,
(eq:ells_to_ellt) (log W)^5 l_s <= l_t (l_s = 1, l_t = L) and the isolation L/2 >= 10 (log W)^3 l_s, in floats."""
from fractions import Fraction as F
import math
for n in (0,1):
    m=n+24; L=2*m**5; W=2**m; g2=F(1); s=F(0); t=1-F(1,L*L)
    a=g2/L**2; x,y=1-t,1-s
    lw=math.log(W)
    print(f"szCL n={n} L={L} W=2^{m}: g^2/L^2 = 1-t = 1/{L*L}, 1-s = 1 | (i): {a<=x<=y<=g2} | (log W)^5 l_s = {lw**5:.0f} <= l_t = {L}: {lw**5<=L} | L/2 = {L//2} >= 10 (log W)^3 l_s = {10*lw**3:.0f}: {L//2>=10*lw**3}")
```
### P.10e `diff inst_groups.py repair/inst_groups_r1.py; diff instances.py repair/instances_r1.py`
```
5c5
< sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
---
> sys.path.insert(0,os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
14c14
<     m=re.search(r'\((sz0|szB|szG), (z0|zB), (\S+?), (\S+?)\)',t)
---
>     m=re.search(r'\((sz0|szB|szG|szCL), (z0|zB|zCL), ([^,]+?), ([^,]+?)\)',t)
5c5
< sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
---
> sys.path.insert(0,os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
10c10,11
< print(f"namespace RBM.Gauss.T2134Inst: {len(ds)} declarations; instances (inst_*): {sum(1 for d in ds if d['short'].startswith('inst_'))}; data/regime lemmas: {sum(1 for d in ds if d['short'] in names)}")
---
> CL={'szCL','sCL','tCL','zCL','flow_zCL','lemT_zCL','szCL_reg5I','szCL_con','szCL_cltFar_index_nonempty','szCL_cltIso_witness'}
> print(f"namespace RBM.Gauss.T2134Inst: {len(ds)} declarations; instances (inst_*): {sum(1 for d in ds if d['short'].startswith('inst_'))}; data/regime lemmas: {sum(1 for d in ds if d['short'] in names)}; szCL data (repair): {sum(1 for d in ds if d['short'].startswith(('szCL','sCL','tCL','zCL','flow_zCL','lemT_zCL','xCL','zdistInf_xCL')))} declarations, listed: the {len(CL)} below")
12c13
<     if not (d['short'].startswith('inst_') or d['short'] in ('szG','szG_WO','flow_zG','szG_reg4','szB_reg5I','szB_reg5II','sz0_reg5III')): continue
---
>     if not (d['short'].startswith('inst_') or d['short'] in ('szG','szG_WO','flow_zG','szG_reg4','szB_reg5I','szB_reg5II','sz0_reg5III') or d['short'] in CL): continue
```
### P.10f Mathlib/core names used by the repair, added to (c) of the prove report (`lake env lean uses_mathlib.lean` at `7b2b789`, `python3 mathlib_names.py`: 150 names; the 35 not in its run on the `36fbd3c` output)
```
abs_one div_le_iff₀ div_lt_iff₀ Filter.tendsto_add_atTop_nat Filter.tendsto_atTop_mono Finset.le_sup Finset.mem_univ gt_mem_nhds inv_inv inv_lt_one_of_one_lt₀ inv_mul_eq_div le_antisymm max_self min_self Nat.cast_le Nat.le_induction Nat.le_mul_of_pos_right Nat.le_self_pow Nat.lt_two_pow_self Nat.mul_le_mul_left Nat.mul_le_mul_right Nat.one_le_pow Nat.pow_le_pow_left Pi.single_eq_same Real.le_sqrt Real.log_pow Real.log_two_gt_d9 Real.log_two_lt_d9 Real.one_lt_rpow Real.pow_rpow_inv_natCast Real.rpow_pow_comm Real.sqrt_inv Real.sqrt_one tendsto_pow_const_div_const_pow_of_one_lt ZMod.val_cast_of_lt
```
