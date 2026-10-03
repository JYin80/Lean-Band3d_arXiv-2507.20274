# T2041 port map and design tables (ST-D3: Steps 3–4 of `lem:main_ind`) — companion of `docs/reports/T2041-prove.md`

Written Sat Oct  3 10:04:52 UTC 2026.  Probe `RBM3D/Probe/T2041Pins.lean` on branch `t/T2041` at `80162ae` (base `64bdfd3`); RBM2D read at `c9a24cf` (kept lines at `0c1330a`); paper cited `1_2:line`, `3_5:line`.  Tables marked (script) are the verbatim output of the scripts of P.10; tables marked (hand) are my reading, with the evidence cited.

## P.1 Inventory of the RBM2D ST-3 files (item 1; script `inv.py`, `inv_table.py`)

Rule of the T2002 portmap (E): ST-3 = `Induction/*` minus (`MainInd`, `Defs`) minus the ST-1 files (`Continuity ConArg ConArgDet Step1`) minus the ST-2 files (`Grid* AzumaProxyN StepDecompN LoopC2N LoopGenN QVN Step2TargetV3 StoppedEndDefs`) minus class d (`Region`); T2015 (DECISIONS §19) moved `ScaleFacts PerTimeCalc Split` to ST-1.  Columns: `lines` at `c9a24cf`, `kept` at `0c1330a` (`-1`: absent), `cl` = T2002 class, `tok` = exponent tokens (portmap regex, `W^2 L^2 (WL)^2 size^2 W⁻² d = 2 5⁻¹`), labels cited in the file that exist in this paper (T2002 rows), the public names that a textual search finds in the ST-4/ST-5/ST-6 files (names of ≥ 5 characters declared once in RBM2D, small stoplist), and the files of other groups that import it (import graph).

```
files=41 lines=50307 kept=38991; moved to ST-1 by T2015: 3 files, kept=1745
token check (recomputed vs portmap): ScaleFacts:2!=0
classes {'b': 37, 'a': 2, 'd': 1, 'c': 1}
```

| file | lines | kept | cl | tok | #pub/#priv | labels cited (this paper) | public names used by ST-4/ST-5/ST-6 files (script) | imported by (files, other groups; import graph) |
|---|---|---|---|---|---|---|---|---|
| AltAbsorb | 1048 | 983 | b | 52 | 48/0 |  | — | ST-6:P7FromSTO |
| AltBudget | 788 | 674 | b | 11 | 7/23 |  | — | — |
| AltBudgetTerms | 698 | 281 | b | 18 | 29/9 |  | — | — |
| AltDriftQ | 2865 | 1950 | b | 69 | 63/28 | int_K-L+QE@6:109; jywiiwsoks@3_5:1271 | — | — |
| AltEnd | 1873 | 975 | b | 8 | 74/3 | int_K-L+QE@6:109; jywiiwsoks@3_5:1271; lem:STOeq_Qt@3_5:1364 | AltLevelsE→6; AltAbsorb→6 | — |
| AltEndCompose | 1072 | 1072 | b | 11 | 44/9 |  | — | — |
| AltGridQ | 2384 | 2275 | b | 66 | 19/75 | Def:QtPt@3_5:1204; int_K-L+Q@3_5:1337; zjuii2@3_5:1318 | — | — |
| AltLevelsE | 551 | 454 | b | 0 | 10/13 | int_K-L+QE@6:109; lem:STOeq_NQ@3_5:1136; lem:STOeq_Qt@3_5:1364 | stoeqTargetV2→6 | ST-6:Endpoints |
| AltLevelsQ | 1043 | 946 | b | 14 | 8/18 | jywiiwsoks@3_5:1271; lem:STOeq_Qt@3_5:1364; lem_+Q@3_5:1285; normQA… | — | — |
| AltLevelsQ0 | 791 | 737 | b | 34 | 5/15 |  | — | — |
| AltProxyQ | 1632 | 1265 | b | 51 | 33/35 | Def:QtPt@3_5:1204; lem_+Q@3_5:1285; normQA@3_5:1287 | — | — |
| AltSymm | 483 | 407 | b | 6 | 8/27 | Kn2sol@1_2:1175 | — | — |
| B45 | 2095 | 1196 | b | 106 | 12/73 | jywiiwsoks@3_5:1271; lem_WI_K@1_2:1034; prop:ThfadC@1_2:1144; res_d… | — | ST-2:StoppedEndDefs |
| BcalE | 2214 | 2044 | b | 51 | 2/71 | DefKsimLK@3_5:89; GavLGEX@3_5:33; def:CALE@3_5:169; def_ELKLK@3_5:9… | — | ST-2:GridGoodN |
| BcalEDecay | 1314 | 1153 | b | 66 | 25/39 | Def_decay@3_5:1115; lem_decayLoop@3_5:1126 | BcalEDecay_sum_sum_norm_SB→5; norm_sum_SB_le_left→5; norm_sum_SB_le_right→5 | ST-5:MLExpDrift |
| Chain | 454 | 424 | b | 3 | 4/18 | ML:GLoop@1_2:1193; ML:GLoop_expec@1_2:1203; ML:GtLocal@1_2:1217; le… | initAtZero→6; chainTarget→6 | ST-2:GoodEvent, ST-6:MainInd |
| DecayLoop | 934 | 816 | b | 4 | 3/23 | GijGEX@3_5:24; lem_decayLoop@3_5:1126; res_decayLK@3_5:1128; Kn2sol… | decayLoopFromML→6 | ST-2:StoppedEndDefs |
| HierAlgebra | 787 | 704 | b | 37 | 17/27 | DefKsimLK@3_5:89; DefTHUST@3_5:109; def_ELKLK@3_5:97; pro_dyncalK@1… | — | ST-2:GridDriftN |
| HierVocab | 664 | 444 | b | 25 | 47/11 | Def:QtPt@3_5:1204; DefKsimLK@3_5:89; DefTHUST@3_5:109; def:CALE@3_5… | vartheta→5; varthetaDot→5; thetaSig→5; elklkN→5; lkTensor→5 … | ST-2:GridDuhamelN/LoopGenN/QVN, ST-5:MLExpVocab, ST-6:MainInd, UN:Generator |
| HierarchyN | 76 | 38 | a | 0 | 1/0 |  | hierarchyN→5 | ST-2:GridDriftN, ST-5:MLExpVocab |
| KcalDecay | 913 | 841 | b | 23 | 1/36 | eq:bcal_k@1_2:1056; lem_decayLoop@3_5:1126; Kn2sol@1_2:1175 | kcalDecay→5/6 | ST-2:GridGoodEvent, ST-5:MLExpDrift |
| LocalFormCalc | 3861 | 3340 | b | 116 | 191/10 | Def:QtPt@3_5:1204; lem:sum_decay@3_5:1632; eq:bcal_k@1_2:1056 | — | — |
| LocalFormCuts | 2296 | 2120 | b | 40 | 154/1 | res_decayLK@3_5:1128 | — | — |
| LocalFormLin | 547 | 498 | b | 25 | 4/6 | Def:QtPt@3_5:1204 | — | — |
| NonAltBudget | 1475 | 852 | b | 14 | 65/20 |  | — | — |
| NonAltEnd | 1690 | 1287 | b | 16 | 73/0 | lem:STOeq_NQ@3_5:1136; example@A:548 | — | — |
| NonAltGood | 2308 | 830 | b | 87 | 110/40 | alu9_STime@3_5:229; int_K-L+Q@3_5:1337; lem:STOeq_NQ@3_5:1136 | — | — |
| PPClosure | 1159 | 1070 | b | 57 | 8/27 |  | ppDriftSumN→6; ppQVSumN→6; ppArithN→6 | ST-6:P7FromSTO |
| PPCondVar | 519 | 413 | b | 46 | 8/7 | alu9_STime@3_5:229; def:CALE@3_5:169 | ppCondVarN→6 | ST-6:P7FromSTO |
| PPDrift | 887 | 513 | b | 65 | 6/33 | def_ELKLK@3_5:97; def_EwtG@1_2:961; example@A:548 | ppDriftN→6 | ST-6:P7FromSTO |
| PPGoodEvent | 1033 | 946 | b | 7 | 6/29 | GavLGEX@3_5:33; lem_GbEXP@3_5:14; lem_decayLoop@3_5:1126; example@A… | gridGoodPPN→6 | ST-6:P7FromSTO |
| PPKernel | 346 | 313 | b | 4 | 4/11 | def_Ustz@3_5:116; prop:ThfadC@1_2:1144 | ppKernelN→6 | ST-6:P7FromSTO |
| PPVocab | 2026 | 1199 | b | 15 | 95/6 | alu9_STime@3_5:229; int_K-L_ST@3_5:136; lRB1@1_2:1321 | ppTargetV2_of_ppPins→6 | — |
| PerTimeCalc (→ST-1) | 1434 | 615 | a | 0 | 46/66 |  | perTimeCalc_of_imp→4; perTimeCalc_of_imp_union→4; perTimeCalc_mono→4; mono_right_eventually→4; stochDom_of_le_left_eventually→4 … | ST-1:ConArg/CondStable/EntryDom/Step1, ST-4:FarEntry, UN:BootstrapAt/DuhamelC/HypB |
| QopBounds | 747 | 673 | b | 42 | 6/30 | lem_+Q@3_5:1285; normQA@3_5:1287 | qopNorm→5; qopDecay→5 | ST-5:MLExpVocab |
| Region | 104 | -1 | d | 0 | 2/2 |  | — | — |
| ScaleFacts (→ST-1) | 419 | 312 | c | 2 | 8/14 | con_st_ind@1_2:1296, eq:ellt@1_2:1121, eq_B_param@1_2:1107; con_st_… | chainStepCond→6 | ST-1:Step1 |
| Split (→ST-1) | 952 | 818 | b | 24 | 56/3 |  | norm_gloop_le_opNorm→5 | ST-1:ConArgDet/FlucAvg/Step1, UN:AuxCarrier/DuhamelA/EMCTE2/GUELocalBootstrap/Proc/RandomLayerA/UnivMain/ZeroModeProfile |
| Step3 | 1925 | 1805 | b | 10 | 2/121 | Eq:Gdecay_w@1_2:1349; Eq:LGxb@1_2:1361; Gt_bound+IND@1_2:1276; Gt_b… | step3→6 | ST-6:MainInd |
| Step45 | 1445 | 1318 | b | 5 | 4/57 | Eq:Gdecay_flow@1_2:1380; Eq:L-KGt-flow@1_2:1371; GavLGEX@3_5:33; le… | step4→6; step5→6 | ST-2:StoppedEndDefs, ST-6:MainInd |
| SumZeroQ | 455 | 390 | b | 2 | 17/6 | Def:QtPt@3_5:1204 | SumZeroQ_Psum_vartheta→5; SumZeroQ_Psum_Qop→5; SumZeroQ_hasDerivAt_vartheta→5; SumZeroQ_varthetaDot_eq→5; SumZeroQ_commutator→5 | ST-5:MLExpVocab |

Reading (hand, from the table): ST-4 (Step 5, `Evolution/*` files other than `Step61`, `MLExp*`) consumes **no** public name of the 37 files (only `PerTimeCalc`, now ST-1); ST-5 (Step 6, `MLExp*`, `Step61`) consumes the operator vocabulary (`vartheta`, `varthetaDot`, `thetaSig`, `elklkN`, `lkTensor`, `HierarchyN`, `KcalDecay`, `Alternating`), `qopNorm`, `qopDecay`, `SumZeroQ_*`, `kcalDecay`, `hierarchyN`; ST-6 consumes `step3`, `step4`, `step5`, `stoeqTargetV2`, `chainTarget`, `initAtZero`, `chainStepCond`, `decayLoopFromML`, `ppTargetV2_of_ppPins` and the `PP*` pins.  **ST-2 imports nine ST-3 files** (`HierVocab HierAlgebra HierarchyN KcalDecay BcalE DecayLoop B45 Chain Step45`): see the findings in P.9.

## P.2 The pins (items 2, 6; statements extracted by script `extract.py`, docstrings omitted; line numbers of the probe)

```lean
-- line 55
abbrev STPair (s t : ℕ → ℝ) (n : ℕ) : Type := {q : ℝ × ℝ // s n ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ t n}
-- line 70
def STXiL (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ := 1 + STmaxL sz n E v k ω / (sz.Bctl n v) ^ (k - 1)
-- line 75
def STXiLK (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ := 1 + STmaxLK sz n E v k ω / (sz.Bctl n v) ^ k
-- line 83
def STPsi (A r : ℝ) (n k : ℕ) : ℝ := A ^ (3 / 4 : ℝ) + r ^ (n - 1) * A ^ (1 - (k : ℝ) / 8)
-- line 94
def STPsum {m L : ℕ} [NeZero L] (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) : ℂ := ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), A a
-- line 99
def STQop {m L : ℕ} [NeZero L] (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ) (A : (Fin (m + 1) → Zd d L) → ℂ) : (Fin (m + 1) → Zd d L) → ℂ := fun a => A a - STPsum (d := d) A
  (a 0) * ϑ t a
-- line 104
def STIdiff {k : ℕ} (σ : Fin k → Bool) : Finset (Fin k) := Finset.univ.filter (fun i => σ i ≠ σ (finRotate k i))
-- line 228
def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop := STLocalEntryU sz E s t ∧ STAvgU sz E s t ∧ STGdecayW sz E s t Cd
-- line 183
def STLmaxU (E s t : ℕ → ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖Lloop sz n (E n) (p.1 :
  ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))
-- line 191
def STLKU (E s t : ℕ → ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ)
  p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)
-- line 199
def STAvgU (E s t : ℕ → ℝ) : Prop := Prec sz (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
  STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 1)
-- line 206
def STLocalEntryU (E s t : ℕ → ℝ) : Prop := Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ)
  ω p.2.1 p.2.2‖ ^ 2) (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))
-- line 215
def STGdecayW (E s t : ℕ → ℝ) (Cd : ℝ) : Prop := ∀ D : ℝ, 0 < D → Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p ω => ‖Lloop sz n (E
  n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) * STWB sz n
  (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) * Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
  ((sz.W n : ℕ) : ℝ) ^ (-D))
-- line 236
def STKward (E : ℕ → ℝ) : Prop := ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → ∀ k : ℕ, 2 ≤ k → Prec sz (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n))) (fun n
  p _ => ∑ x : Zd d (sz.L n), ‖STKI sz n (E n) (τ n) ⟨List.ofFn p.1, List.ofFn p.2 ++ [x]⟩‖) (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (τ n))⁻¹ * (sz.Bctl n (τ n)) ^
  (k - 2))
-- line 244
def STCaseI (_s t : ℕ → ℝ) : Prop := ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n
-- line 248
def STCaseII (s _t : ℕ → ℝ) : Prop := ∀ n, 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2
-- line 257
def STStep3R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 /
  100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → R sz s t → STKbound sz
  (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz
  (STflowE z) s t
-- line 268
def STStep4R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 /
  100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) → R sz s t → STKbound sz
  (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz
  (STflowE z) s t → STLKU sz (STflowE z) s t
-- line 282
def STStep3 (d : ℕ) : Prop := STStep3R d STAny
-- line 283
def STStep4 (d : ℕ) : Prop := STStep4R d STAny
-- line 284
def STStep3I (d : ℕ) : Prop := STStep3R d STCaseI
-- line 285
def STStep3II (d : ℕ) : Prop := STStep3R d STCaseII
-- line 286
def STStep4I (d : ℕ) : Prop := STStep4R d STCaseI
-- line 287
def STStep4II (d : ℕ) : Prop := STStep4R d STCaseII
-- line 314
def STContract (d : ℕ) : Prop := ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ ω : sz.SeqΩ, (∀ (m k : ℕ), 1 ≤ k → k + 1 ≤ m → ∀ (σ : Fin m → Bool) (a : Fin
  (m - 1) → Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * (STmaxL sz n E τ (2 * k - 1) ω *
  STmaxL sz n E τ (2 * m - 2 * k - 1) ω) ^ (1 / 2 : ℝ)) ∧ (∀ (m k l p : ℕ) (j : Fin (m - 1)) (C : ℝ), 4 ≤ m → 1 ≤ p → 1 ≤ k → k < j.val + 1 → j.val + 1 < l → l + 1 ≤ m → 0 ≤ C
  → ∀ (𝒜 : Zd d (sz.L n) → Finset (Zd d (sz.L n))), (∀ x, ((𝒜 x).card : ℝ) ≤ C) → ∀ (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ∑ y ∈ 𝒜 x, ‖STLI
  sz n E τ ω ⟨List.ofFn σ, List.ofFn (Function.update a j y) ++ [x]⟩‖ ≤ C * (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ * (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * m - 2
  * l - 1) ω) ^ (1 / 2 : ℝ) * STmaxL sz n E τ (2 * (l - k) * p) ω ^ (1 / (2 * (p : ℝ))))
-- line 337
def STNewPQ (d : ℕ) : Prop := ∀ (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)), ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) →
  Fin m) (A' : ∀ α, Finset (Fin (k α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧ ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω :
  sz.SeqΩ) (a : Fin m → Zd d (sz.L n)), (zeroModeSet d (sz.L n) A (fun a' => Lloop sz n E τ σ a' ω) a = zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => Lloop sz n E τ σ a'
  ω) a + ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) * zeroModeSet d (sz.L n) (A' α) (fun a' => Lloop sz n E τ (σ' α) a' ω)
  (a ∘ ι α)) ∧ (zeroModeSet d (sz.L n) A (fun a' => STKloop sz n E τ σ a') a = zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => STKloop sz n E τ σ a') a + ∑ α : Fin ℓ, ((ξ α
  : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) * zeroModeSet d (sz.L n) (A' α) (fun a' => STKloop sz n E τ (σ' α) a') (a ∘ ι α))
-- line 370
def STSEforLnConcl (E s t : ℕ → ℝ) : Prop := ∀ k : ℕ, 2 ≤ k → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖STegt sz n (E n)
  (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖) (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) * (STXiL sz n (E n) (p.1 : ℝ) (STn12E k).1 ω * STXiL sz n (E
  n) (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ)) ∧ (∀ l : ℕ, 3 ≤ l → l ≤ k → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω =>
  ‖STksimLK sz n (E n) (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖) (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) * STXiLK sz n (E n) (p.1 : ℝ) (k - l +
  2) ω)) ∧ Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖STelklk sz n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
  (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) * (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1), STXiLK sz n (E n) (p.1 : ℝ) (k + 2 - n') ω * (STXiL sz n (E n)
  (p.1 : ℝ) (STn12 n').1 ω * STXiL sz n (E n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) + (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz n (E n) (p.1 : ℝ) k ω)) ∧ (∀ q : ℕ, 1 ≤
  q → Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖STee sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2.1
  p.2.2.2‖) (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / etaT (E n) (p.1 : ℝ) * (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1
  : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ))))))
-- line 463
def STSEforLn (d : ℕ) : Prop := STIngR d STAny (fun sz E s t => STSEforLnConcl sz E s t)
-- line 409
def STbootRHS (lo : ℕ) (XL XLK : ℕ → ℝ) (B : ℝ) (n_ p : ℕ) : ℝ := B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * n_ - 1) ^ (1 / 2 : ℝ) * XL (4 * p) ^ (1 / (4 * (p : ℝ))) + (∑ m ∈
  Finset.Icc lo (n_ - 1), XLK m + ∑ m ∈ Finset.Icc (n_ - 1) (n_ + 1), XL m + ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1), XLK (n_ + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2)
  ^ (1 / 2 : ℝ))
-- line 421
def STXiBoot (E s t : ℕ → ℝ) : Prop := ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ, (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) → (∀ m, 1 ≤ m → STlenL n_ p m
  → Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) → (∀ m, 1 ≤ m → m + 1 ≤ n_ → Prec sz (U := STPair s t) (fun n q ω =>
  STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) → Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω) (fun n q _ => STbootRHS 1 (fun m => XL m n
  q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n q.1.2) n_ p)
-- line 435
def STNQConcl (E s t : ℕ → ℝ) : Prop := ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ, (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) → (∀ m, 1 ≤ m → STlenL n_ p m
  → Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) → (∀ m, 1 ≤ m → m + 1 ≤ n_ → Prec sz (U := STPair s t) (fun n q ω =>
  STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) → Prec sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d
  (sz.L n))) (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_) (fun n q ω => (sz.Bctl n
  (q.1 : ℝ)) ^ (1 / 6 : ℝ) * STsupXiLK sz n (E n) (s n) (q.1 : ℝ) n_ ω + STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)
-- line 452
def STIngR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ →
  0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n <
  t n) → (∀ n, t n ≤ lemT (z n)) → R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep2Concl sz (STflowE z) s t
  Cd → Concl sz (STflowE z) s t
-- line 466
def STOeqNQ (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConcl sz E s t)
-- line 469
def STOeqQt (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STXiBoot sz E s t)
-- line 472
def STOeqQtNZ (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STXiBoot sz E s t)
-- line 476
def STIterHyp (E s t : ℕ → ℝ) (A : ℕ → ℝ) (r l : ℕ) : Prop := Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 r ω) (fun n q _ => STPsi (A n) (etaT (E n) (s n)
  / etaT (E n) q.1.2) r l)
-- line 485
def STIterR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀
  Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤
  lemT (z n)) → R sz s t → STKbound sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
  STXiBoot sz (STflowE z) s t → ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t (Aof sz s) r k) → (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz
  (STflowE z) s t (Aof sz s) r (k - 1)) → STIterHyp sz (STflowE z) s t (Aof sz s) n_ k
-- line 504
def STIterations (d : ℕ) : Prop := STIterR d STRegIterI (fun sz _ n => STAI sz n)
-- line 507
def STIterationsII (d : ℕ) : Prop := STIterR d STCaseII (fun sz s n => STAII sz s n)
-- line 517
def STMollifierProps {m L : ℕ} [NeZero L] (g C c : ℝ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) : Prop := (∀ t a₁, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 =
  a₁), ϑ t a = 1) ∧ (∀ t, 0 ≤ t → t < 1 → ∀ a, ‖ϑ t a‖ ≤ C * (((ellT L g t) ^ d)⁻¹) ^ m * Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) :
  ℝ)) / ellT L g t)) ∧ (∀ a, DifferentiableOn ℝ (fun t => ϑ t a) (Set.Ico 0 1)) ∧ (∀ t, 0 ≤ t → t < 1 → ∀ a, ‖deriv (fun τ => ϑ τ a) t‖ ≤ C * (1 - t)⁻¹ * (((ellT L g t) ^
  d)⁻¹) ^ m)
-- line 525
def STMollifierEx (d : ℕ) : Prop := 3 ≤ d → ∀ (m : ℕ) (Λ : ℝ), 0 < Λ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → haveI : NeZero L := ⟨by omega⟩
  ∃ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ
-- line 535
def STQopNorm (d : ℕ) : Prop := 3 ≤ d → ∀ (m : ℕ) (Λ K C c : ℝ), 0 < Λ → 0 < K → 0 < C → 0 < c → ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ,
  1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K → haveI : NeZero L := ⟨by omega⟩ ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ → ∀
  t : ℝ, 0 ≤ t → t < 1 → ∀ 𝒜 : (Fin (m + 1) → Zd d L) → ℂ, EKFastDecay g t W ε D 𝒜 → ‖STQop (d := d) ϑ t 𝒜‖ ≤ W ^ (Cn * ε) * ‖𝒜‖ + W ^ (-D + Cn)
-- line 556
def STWardTypeP (E s t : ℕ → ℝ) : Prop := ∀ (m : ℕ) (C c : ℝ), 1 ≤ m → ∀ ϑ : (∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), (∀ n, STMollifierProps (d := d) (sz.lam n) C c
  (ϑ n)) → ∀ X : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ X n u) → Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n u _ => X n (u : ℝ)) → Prec sz (U :=
  fun n => TimeIcc s t n × {σ : Fin (m + 1) → Bool // STAlternating σ} × (Fin (m + 1) → Zd d (sz.L n))) (fun n q ω => ‖STPsum (d := d) (STLKtensor sz n (E n) (q.1 : ℝ) ω
  q.2.1.1) (q.2.2 0) * ϑ n (q.1 : ℝ) q.2.2‖) (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (m + 1) * X n (q.1 : ℝ))
-- line 567
def STB45 (E s t : ℕ → ℝ) : Prop := ∀ (m : ℕ) (C c : ℝ), 1 ≤ m → ∀ ϑ : (∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n))
  → ∀ X : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ X n u) → Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n u _ => X n (u : ℝ)) → Prec sz (U := fun n
  => TimeIcc s t n × {σ : Fin (m + 1) → Bool // STAlternating σ} × (Fin (m + 1) → Zd d (sz.L n))) (fun n q ω => ‖(STQop (d := d) (ϑ n) (q.1 : ℝ) (ThetaN d (sz.L n) (sz.lam n)
  (EKsgn (mE (E n)) q.2.1.1) (q.1 : ℝ) (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1)) - ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) q.2.1.1) (q.1 : ℝ) (STQop (d := d) (ϑ n)
  (q.1 : ℝ) (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ + ‖STPsum (d := d) (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) * deriv (fun τ => ϑ n τ q.2.2) (q.1 :
  ℝ)‖) (fun n q _ => (etaT (E n) (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ (m + 1) * X n (q.1 : ℝ))
-- line 584
def STWardTypePPin (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STWardTypeP sz E s t)
-- line 587
def STB45Pin (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STB45 sz E s t)
-- line 291
theorem STLmax_of_STLmaxU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLmaxU sz E s t) : STLmax sz E t
-- line 298
theorem STLK_of_STLKU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLKU sz E s t) : STLK sz E t
```

Hierarchy-term definitions (`STLI STKI STLKI STksimLK STelklk STavgErr STegt STeeLoop STee`, probe lines 107-170) are the port of RBM2D `Induction/HierVocab.lean:150-203` at `c9a24cf` (`LLf LKf ksimLK elklkN egtN eeLoop eeN`) with `Z2 L ↦ Zd d L`, `W^2 ↦ W^d`, `SB L ↦ SB d L g`, `gloop ↦ loopL`, `Kcal ↦ KLK`; only definitions.

## P.3 EK-6 consumer form (item 3)

Which evolution-kernel statements Steps 3–4 use (script `ekuse.py`; occurrences of `\eqref/\Cref/\ref{label}` in `3_5:900-1934`, outside the kernel lemmas `3_5:1615-1673`):
```
lem:sum_Ndecay               no occurrence
sum_res_Ndecay               [1439]
sum_res_1                    no occurrence
sum_res_2_NAL                [1133, 1153, 1159, 1166]
sum_res_2                    [1261, 1358, 1681, 1711]
lem:sum_decay                [1133, 1439]
lem:sum_decay_nonzero        [1557, 1559, 1902, 1908]
sum_res_Ndecay_nonzero       [1440]
lem:propT                    no occurrence
claim:TTk                    no occurrence
eq:latticesum_d3             no occurrence
eq:THETAINFTINF              no occurrence
prop:ThfadC                  [1123]
prop:ThfadC0                 [1440]
```
So Steps 3–4 consume `(sum_res_2_NAL)` (`lem:STOeq_NQ`, `3_5:1153-1166`), `(sum_res_2)` (`lem:STOeq_Qt`, `3_5:1681-1711`) and `lem:sum_decay_nonzero` (`lem:STOeq_Qt_nonzero`, `3_5:1557-1559`); `(sum_res_Ndecay)` occurs once, in the discussion of case (ii) (`3_5:1439`), not in a proof; `(sum_res_1)`, `lem:sum_Ndecay`, `lem:propT`, `claim:TTk`, `(eq:latticesum_d3)` do not occur.  `claim:TTk` is `7_8:1661` (light-weight terms): the `Λ = (log W)^{10}`-type choice is not needed here.  The derivation steps are: `W^{Cε} ≤ N^{τ}` (`W ≤ N^{1/d}`: merged `Sizes.W_rpow_le`; `ε = min(1/2, τ d/(4C))`), `W^{-D₀+C} ≤ N^{-D}` (`W ≥ N^𝔠`, `D₀ = C + 1 + D/𝔠`), `4 ≤ W^ε` and `log L ≤ W^ε` eventually, `L^d ≤ N ≤ W^{1/𝔠}` (`K = 1/𝔠`, DECISIONS §21), `g ≤ 𝔡⁻¹` from `(eq:WO)`, then the merged `StochDomAt.of_highProbAt_add_rpow_neg`.

Statements (script; the consumer forms `STEK*` are `Prop`s on the model measure at the scale `N`; EK-6 proves each from the merged `EK*` pin):
```lean
-- line 602
def STEKDecay {m : ℕ} (s t : ℕ → ℝ) (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) : Prop := ∀ ε D : ℝ, 0 < ε → 0 < D → Whp sz (fun n => {ω | ∀ v : TimeIcc s
  t n, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D (𝒜 n v ω)})
-- line 609
def STEKLow (s t : ℕ → ℝ) (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) : Prop := ∃ b : ℝ, Whp sz (fun n => {ω | ∀ v : TimeIcc s t n, ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω})
-- line 614
def STEKWin (s t : ℕ → ℝ) : Prop := (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ t n) ∧ (∀ n, t n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) ∧ (∀ n, t n < 1) ∧ ∀ᶠ n in atTop, ((sz.W n : ℕ)
  : ℝ)⁻¹ ≤ (1 - t n) / (1 - s n)
-- line 620
def STEKSumNdecay (d : ℕ) : Prop := 3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1)
  → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → ∀ σ : Fin n_ → Bool, ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), (∀ n v
  ω, 0 ≤ X n v ω) → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m
  n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖) (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * X n v ω)
-- line 632
def STEKSumRes1 (d : ℕ) : Prop := 3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → ∀ σ
  : Fin n_ → Bool, ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t 𝒜 → ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X → Prec
  sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜
  n v ω)‖) (fun n v ω => (ellT (sz.L n) (sz.lam n) (t n) ^ 2 / ellT (sz.L n) (sz.lam n) (v : ℝ) ^ 2) * ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_ * X n
  v ω)
-- line 644
def STEKSumRes2NAL (d : ℕ) : Prop := 3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m
  n‖ = 1) → (∀ n, κ ≤ (m n).im) → ∀ σ : Fin n_ → Bool, (∃ k, σ k = σ (finRotate n_ k)) → ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t
  𝒜 → ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X → Prec sz (U := fun n => TimeIcc s t n)
  (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖) (fun n v ω => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) * X
  n v ω)
-- line 658
def STEKSumRes2 (d : ℕ) : Prop := 3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖
  = 1) → (∀ n, κ ≤ (m n).im) → ∀ σ : Fin n_ → Bool, ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t 𝒜 → (∀ n v ω, EKSumZero (𝒜 n v ω)) →
  ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X → Prec sz (U := fun n => TimeIcc s t n) (fun n
  v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖) (fun n v ω => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_ * X n v ω)
-- line 672
def STEKNonzero (d : ℕ) : Prop := 3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ s t : ℕ → ℝ, (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) :
  ℝ) ^ 2 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → (∀ n, κ ≤ (m n).im) → ∀ σ : Fin n_ → Bool, ∀ A : Finset (Fin n_), (∀ i, σ i ≠ σ
  (finRotate n_ i) → i ∈ A) → ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), (∀ n v ω, 0 ≤ X n v ω) → Prec sz
  (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X → Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖zeroModeSet d (sz.L n) A (UN d (sz.L n) (sz.lam n) (EKsgn (m
  n) σ) (v : ℝ) (t n) (𝒜 n v ω))‖) X
```
Compiled derivations (`#print axioms`: the three standard axioms): 
```lean
-- line 691
theorem stek_sumNdecay (d : ℕ) : STEKSumNdecay d
-- line 718
theorem stek_sumRes2NAL (d : ℕ) : STEKSumRes2NAL d
```
The other consumer forms stay `Prop`s: `STEKSumRes1` (merged `ekSumDecay1_holds` proves its pin; not consumed by Steps 3–4), `STEKSumRes2` (pin `EKSumDecay2`, EK-4 = T2042, amended by DECISIONS §21), `STEKNonzero` (pin `EKSumDecayNonzero`, EK-5 = T2035).  Their instances (`inst_ekRes1`, `inst_ekRes2`, `inst_ekNonzero`) apply the pin as a hypothesis at concrete data.

## P.4 Exponent table with the d = 2 tokens (item 4) (hand; values at `d = 3` are section (a)(i) of the prove report; every RBM2D `file:line` is checked by `cites.py` at `c9a24cf`)

Regimes, `x = 1-t`, `g = ilambda`: R1 `x ≥ g²`; R2 `g²/L² ≤ x ≤ g²`; R3 `g²/L^d ≤ x ≤ g²/L²`; R4 `x ≤ g²/L^d` (the paper's cases are (i) `1-t ≥ g²/L²` = R1 ∪ R2 and (ii) `1-s ≤ g²/L²` ⊂ R3 ∪ R4 at `t`).  Values of `W^{-d}B_{t,0}`, `(W^{-d}B)^{n-1}`, `(W^{-d}B)^n`, `Ψ(n,k;s,t)`, `A`, the iteration count, the zero-mode share and the Gronwall absorption at one point per regime: (a)(i) rows 6, 12–18, (a)(ii).

| quantity | RBM2D `d = 2` token (`c9a24cf`) | `d ≥ 3` (paper; pin) | change |
|---|---|---|---|
| scale `W^{-d}B_{u,0}` | `scaleM` `Path/Scales.lean:44` `= W² ℓ² η`, used as `M^{-k}` in `HierVocab.lean:295-310` | `1_2:1107`; merged `Sizes.Bctl` | min of two scales → sum of two terms with `g`; `x B(x) = x/(g²+x) + L^{-d}` nondecreasing |
| `Ψ(n,k;s,t)` | `Step3.lean:294` `step3_Psi As R n k = As^{1/2} + R^{n-1} As^{1-k/4}`, `R = (ℓ_t/ℓ_s)²` (`Step3.lean:59-62`) | `STPsi A r n k = A^{3/4} + r^{n-1} A^{1-k/8}`, `r = η_s/η_t` (`3_5:1396`); `A = g² W^d` (case (i)), `A = (W^{-d}B_{s,0})⁻¹` (`3_5:1577`) | exponents `1/2 → 3/4`, `k/4 → k/8`; `R → η`-ratio; `A` depends on the case |
| iteration depth | final `k = n + 1` (`Step3.lean:63`) | `k > 2 + 8 𝔠_d (n-1)`, `O(1)` (`3_5:1427`; (a) row 14) | `n + 1 → O(1)` |
| splitting `(5.118)` | `Step3.lean:440` `Ξ_{2n+2} ≤ Ξ_{2l₁} Ξ_{2l₂} M_u`; block weight `W⁻²` `Split.lean:176,615` (`loopXi_le` `Split.lean:569`) | `3_5:1842` `(eq:boundtwochains)`: `≤ (g² W^d) Ξ_{2l₁} Ξ_{2l₂}` (`L^{(2n-1)}`, not `2n+2`) | `W⁻² → W^{-d}`; `M_u → g² W^d`; loop length `2n+2 → 2n-1` |
| martingale term | `Defs.lean:247` `STOeqPT`: control `Ξ_{2k+2} ≺ Λ`, `Ξ_k ≺ Λ^{1/2} + Φ` | `(am;asoi222)` `3_5:1366`: `B^{-1/(4p)} (Ξ_{2n-1})^{1/2} (Ξ_{4p})^{1/(4p)}`, contraction `(u2jzooi-2)` `3_5:929` | new: loss `B^{-1/(2p)}`, two controls; `p ≥ 4` |
| `ℰ^{G̃}`, `[𝒦∼(𝓛-𝒦)]` | `HierVocab.lean:284` `BcalEPT` (iii) `Ξ_{k+1} M^{-k} η⁻¹`, (i) `Σ_{m<k} Ξ^{LK}_m M^{-k} η⁻¹` | `3_5:1022` `B^k η⁻¹ (Ξ_{n₁} Ξ_{n₂})^{1/2}`, `3_5:1028` `B^k η⁻¹ Ξ^{LK}_{n-l+2}` | single loop `→` geometric mean of two; sum `→` single term; the `ℓ^d` factor `→` contraction `3_5:925` |
| sum over a label | none: `Σ_a |𝓛| ≤ ℓ^d max` | `3_5:925` `(yi2oslxj2)`: `Σ_{a_n} |𝓛^{(n)}| ≤ (W^d η)⁻¹ (max max)^{1/2}` | new at `d ≥ 3` (`3_5:906`: excess `ℓ^{d-2}`); numeric check P.8 |
| mollifier `ϑ` | `HierVocab.lean:66` `vartheta = (1-t)^{k-1} Π Θ_t(a₁,a_i)` | bump `f_t` (`rmk:choosechi` `3_5:1250`), `(eq:derv_Theta)` `3_5:1215`: `ϑ ≺ (ℓ_t^d)^{-(n-1)}` | `(1-t) Θ_t(a,a) ≍ ℓ_t^{-2}` against `ℓ_t^{-d}` at `d ≥ 3`: the `Θ`-based `ϑ` violates the sup bound (numeric, P.8) |
| `(+,+)` base | `Defs.lean:268` `PPTwoLoopPT`, six `PP*` files | none: `(Eq:Gdecay_w)` is stated for all four charges `σ ∈ {±}²` (`1_2:1349`); `lem:iterations` starts at `n = 2` (`3_5:1407-1410`) | not ported (4454 kept lines) |
| `(con_st_ind)` | `Path/Step2Props.lean:116` `CondStInd`, exponent `30` | `1_2:1297` `B_t^{𝔠_d} ≤ (1-t)/(1-s)`, `𝔠_d ≤ 10^{-2}` (and `d 𝔠_d < 1` for the kernel window, (a) F1) | `1/30 → 𝔠_d`; ratio `r ≤ B_t^{-𝔠_d}` |
| zero modes | none (`d = 2` has `ℓ_t^d = ℓ_t^2`, no regime R3) | `Q^{(A)}` (`3_5:1444`), `lem: newPQ` (`3_5:1482`), `lem:sum_decay_nonzero` (`3_5:1666`); `A = Δ_s⁻¹` in case (ii); zero-mode share of `B_{t,0}` 0.015, 0.051, 0.438, 0.563 in R1..R4 ((a) row 18) | new regime, no RBM2D source (T2002 E.3) |
| `Ξ^{𝓛} ≲ 1 + B Ξ^{𝓛-𝒦}` | `Step3.lean:438-439` (5.107) `1 + M_u⁻¹ Ξ` | `3_5:1387` `(rela_XILXILK)` | `M_u⁻¹ → B ≍ A⁻¹` |

## P.5 Route per pin (item 5) (hand; RBM2D file:line at `c9a24cf`; merged declarations of `main` at `64bdfd3`; tickets are P.7)

| pin | RBM2D source | merged declarations reused | tickets; est lines | risk |
|---|---|---|---|---|
| vocabulary `STXiL STXiLK STPsi STPsum STQop` and the hierarchy terms | `Defs.lean:76,83` (`xiL`, `xiLK`), `HierVocab.lean:150-193` (port), `HierVocab.lean:62-80` (`Psum`, `Qop`) | `Prec`, `Lloop`, `loopL`, `blockMat`, `seqHflow`, `KLK`, `LoopIdx.cutGlue{,L,R}`, `SB`, `Bctl`, `zeroModeSet` | S3-01: 890 | low |
| `STStep3R`, `STStep4R` (both cases) | `Defs.lean:277,284` (`Step3PT`, `Step4PT`), `Step3.lean:1777` (`step3`), `Step45.lean:105,1188` (`Step4TargetV3`, `step4`) | `STLK`, `STLmax`, `STStep1Loop`, `STConStInd`, `STKbound` (merged `Induction/Defs`) | S3-25, S3-26, S3-27: 680 + 860 + 700; compiled skeletons `st_step3_skeleton`, `st_step4_skeleton` | low / medium (regime assembly) |
| `STContract` | none (new at `d ≥ 3`; `grep` of RBM2D finds no `yi2oslxj2`, `ygdhmsgq`) | `STmaxL`, merged Ward algebra of `Gres` (S1) | S3-02: 700 | medium |
| `STNewPQ` | none (paper `3_5:1482-1507`, `1871-1886`) | `zeroModeSet` (`zeroModeOp`, `avgOp`), `KLK_ward` (T2036) | S3-03: 600 | medium |
| `STSEforLn` (1)-(4) | `HierVocab.lean:284` `BcalEPT`; proofs `BcalE.lean` (2044 kept), `BcalEDecay.lean` (1153), `DecayLoop.lean` (816), `KcalDecay.lean` (841) | `KLK`, `STKbound`, `STKward`; `Defs/RadialSum` (`sum_radial_exp_decay_le`) for `(eq:sumtwoloop)` | S3-06, 07a, 07b, 08, 09: 1170 + 940 + 1330 + 1420 + 1320 | medium; (4) high |
| `STOeqNQ` | `HierVocab.lean:504` `STOeqTargetV2`, `Defs.lean:247` `STOeqPT`; proof `NonAltGood/Budget/End` (2969 kept; RBM1D `Lemma514NonAlt`) | `ekSumDecayNAL_holds` (merged), `STEKSumRes2NAL`, grid pins of T2039 | S3-10, 11, 12: 950 + 980 + 1480 | medium / high (endpoint) |
| `STOeqQt` | `AltLevelsE.lean:446` `stoeqTargetV2`; proof `Alt*` (12808 kept): `AltGridQ AltProxyQ AltDriftQ AltLevels{Q,Q0,E} AltBudget{,Terms} AltAbsorb AltEnd{,Compose} B45` | `STEKSumRes2` (EK-4), `zeroModeSet`, `STQop`, grid pins of T2039 | S3-13a .. S3-19 (12 tickets): 14820 | high (alternating endpoint) |
| `STOeqQtNZ` | none (case (ii); paper `3_5:1435-1601`); T2002 E.3 | `zeroModeSet`, `STNewPQ`, `STEKNonzero` (EK-5), `ThetaN`, `UN` | S3-20, 21, 22: 1200 + 1500 + 1500 | high |
| `STIterations`, `STIterationsII` | `Step3.lean:294` (`step3_Psi`), `:421` (`step3Lemma514`); `Split.lean:569` `loopXi_le` (ST-1 S1-09) | `st_iterate`, `st_prec_one_add_sup`, `st_prec_of_xi` (probe, to be merged with S3-01) | S3-23, 24a, 24b: 800 + 1100 + 1210 | medium; case (ii) high (proof omitted in the paper, `3_5:1594`) |
| `STMollifierEx`, `STQopNorm` | `HierVocab.lean:66,117` (`vartheta` not admissible), `QopBounds.lean:525,622` (`qopNorm`, `qopDecay`), `SumZeroQ.lean:102` | `projMat`, `norm_zeroModeSet_*` (merged `Kernel/Evolution`), `EKFastDecay` | S3-04, S3-05: 900 + 770 | medium / low |
| `STWardTypePPin`, `STB45Pin` | `HierVocab.lean:365` `B45PT`; `B45.lean` (1196 kept) | `ThetaN`, `KLK_ward`, `EKsgn` | S3-19: 1380 | medium |
| `STKward` | KL12: `KLwardIneqAt` (`64b58eb:RBM3D/Probe/T2004Pins.lean:788`), `KLwardIneqPin` (`:795`) | `KLK_ward` (T2036) | bridge in S3-06 | low |
| `STEK*` consumer forms | new (`7_Evolution` of RBM2D: `Evolution/Bridge.lean`, per T2016 b5) | `ekSumNdecay_holds`, `ekSumDecayNAL_holds` (merged), `StochDomAt.of_highProbAt_add_rpow_neg` | EK-6 (separate gate): 2 derivations compiled here | low (NAL, Ndecay), medium (Res2: `L^d ≤ W^K`) |

## P.6 Block Anderson reuse (item 7) (hand; the paper says (`7_8:2101`, under the heading `7_8:2100`): "The proofs in Sec:Steps34, Sec:Step5, Sec:Step6 extend verbatim to the block Anderson model, except for sec:Step5_larget and the proof of lem:LWterm_EXP")

| piece | carries over | BA gate adds |
|---|---|---|
| `Prec` calculus lemmas (`st_prec_one_add_sup`, `st_prec_of_xi`, `st_iterate`), the logic of `st_step3_skeleton`, `st_step4_skeleton` | verbatim: they use only `Prec` and the finite maximum `Ξ̂ = 1 + max/B^k` over the labels; BA re-instantiates `STXiL`, `STXiLK` with the BA loop (merged `seqHflowBA`, `Gt_BA`, T2013) | nothing |
| pins `STStep3R`, `STStep4R`, `STOeq*`, `STIterations*`, `STSEforLn` | same shapes, flow `STFlowBA` (T2015 b.8: `zztE_BA`, `7_8:1796`), `STKbound_BA`, `STKward_BA`, the BA Step-2 conclusions | `m(z,λ)`, `M^{(B)}`, `e_λ` (DECISIONS §11) |
| contraction `STContract`, `STNewPQ` | verbatim: `G(+) - G(-) = 2iη G(+)G(-)` and `Σ_a E_a = W^{-d} I`; `S^{(B)} = I` for BA (`1_2:955`) does not enter | none |
| `ϑ`, `𝒬_t`, `Q^{(A)}`, `lem_+Q` | `S^{(B)}` and `M^{(σ_i,σ_{i+1})}` are translation invariant, constant vector `e(a) = L^{-d/2}` (`3_5:1542`): `P^{(i)}` commutes with `Θ`, `𝒰` | decay of the entries of the one-index kernel `M^{(σ,σ')} S` (`Mbound_AO`) instead of nearest-neighbour support |
| kernel pins | `EKuKerQ`, `ek_sumNdecayQ` (T2016 b10); consumer forms with `UN` replaced by `tensorKerQ` | the five PT pins for `M^{(B)}`, `(eq:WardM)`, `(eq:off_diagM)`, `lem:propM` |
| not covered | Step 5 (`sec:Step5_larget`), `lem:LWterm_EXP` | BA gate (ST-4 / LW) |

## P.7 Split table (item 8; script `splitcalc.py`: ports `kept × 1.15 × share`, new work by paper lines)

| id | new file `RBM3D/Induction/…` | statements | RBM2D sources (kept lines × share) | est lines | after | role | risk |
|---|---|---|---|---|---|---|---|
| S3-01 | Step34Pins.lean | vocabulary `STXiL..STee`, pins of probe sections 2-4, registry lines, instances | HierVocab (444×1) | 890 | S1-07 (merged), T2041 probe | prover | low |
| S3-02 | Contract.lean | `STContract` (ygdhmsgq; new at d>=3) | new (paper lines) | 700 | S3-01 | prover-hard | medium |
| S3-03 | NewPQ.lean | `STNewPQ` (lem: newPQ; Ward for L and K) | new (paper lines) | 600 | S3-01, S3-02, KLK_ward (merged) | prover-hard | medium |
| S3-04 | QopAlgebra.lean | `STMollifierEx`, algebra of `P, vartheta, Q_t` (P Q = 0, Theta preserves sum-zero, commutator) | SumZeroQ (390×1.15) | 900 | S3-01, PT pins (merged) | prover-hard | medium |
| S3-05 | QopNorm.lean | `STQopNorm` (lem_+Q, K = 1/c) | QopBounds (673×1.15) | 770 | S3-04 | prover | low |
| S3-06 | KDecay.lean | K-loop fast decay, `STKward` bridge (KL12), lattice sum of the tail 𝒯 (eq:sumtwoloop) | KcalDecay (841×1.15) | 1170 | KL7, KL12, merged RadialSum | prover-hard | medium |
| S3-07a | DecayLoopA.lean | lem_decayLoop (decay of L-loops beyond W^eps l_u) | DecayLoop (816×1.15) | 940 | T2039 (Step 2 pins), S1 GbEXP | prover-hard | medium |
| S3-07b | DecayLoopB.lean | decay through cuts, label decay of the E terms | BcalEDecay (1153×1.15) | 1330 | S3-07a | prover-hard | medium |
| S3-08 | SEforLn1.lean | lem:SEforLn (1), (2) | BcalE (2044×0.55) | 1420 | S3-02, S3-06, S3-07b | prover-hard | medium |
| S3-09 | SEforLn2.lean | lem:SEforLn (3), (4) (contraction (u2jzooi-2) for the martingale term) | BcalE (2044×0.45) | 1320 | S3-02, S3-06, S3-08 | prover-hard | high |
| S3-10 | NQGood.lean | NQ: good events and inputs | NonAltGood (830×1.15) | 950 | T2039 grid pins, EK-6, S3-09 | prover-hard | medium |
| S3-11 | NQBudget.lean | NQ: budget arithmetic at d>=3 exponents | NonAltBudget (852×1.15) | 980 | S3-10 | prover-hard | medium |
| S3-12 | NQEnd.lean | `STNQConcl`: endpoint assembly | NonAltEnd (1287×1.15) | 1480 | S3-10, S3-11 | prover-max | high |
| S3-13a | QGridA.lean | Q-process on the grid: stopped Duhamel | AltGridQ (2275×0.6) | 1360 | T2039 grid pins, S3-04 | prover-hard | medium |
| S3-13b | QGridB.lean | Q-process on the grid: drift | AltGridQ (2275×0.55) | 1250 | S3-13a | prover-hard | medium |
| S3-14 | QProxy.lean | martingale part with Q (x) Q (variance proxy) | AltProxyQ (1265×1.15) | 1450 | S3-13b, S3-09 | prover-hard | high |
| S3-15a | QDriftA.lean | Q/E split of the drift and of the initial term (1) | AltDriftQ (1950×0.6) | 1170 | S3-13b | prover-hard | medium |
| S3-15b | QDriftB.lean | Q/E split of the drift and of the initial term (2) | AltDriftQ (1950×0.6) | 1170 | S3-15a | prover-hard | medium |
| S3-16a | QLevelsA.lean | levels of Q_u B_m, m = 0, 5 (Q0), start level | AltLevelsQ0 (737×1.15), AltLevelsE (454×1.15) | 1370 | S3-15b | prover-hard | medium |
| S3-16b | QLevelsB.lean | levels of Q_u B_m, m = 1..5 | AltLevelsQ (946×1.15) | 1090 | S3-16a | prover-hard | high |
| S3-17a | QBudgetA.lean | budget terms of the alternating assembled bound | AltBudgetTerms (281×1.15), AltBudget (674×1.15) | 1100 | S3-16b | prover-hard | medium |
| S3-17b | QBudgetB.lean | absorption pin (13 eventual inequalities at d>=3 exponents) | AltAbsorb (983×1.15) | 1130 | S3-17a | prover | medium |
| S3-18a | QEndA.lean | alternating endpoint, vocabulary and compositions C1-C5 | AltEndCompose (1072×1.15) | 1230 | S3-17b | prover-hard | medium |
| S3-18b | QEndB.lean | alternating endpoint, assembly C6 -> `STXiBoot` (alternating part) | AltEnd (975×1.15) | 1120 | S3-18a | prover-max | high |
| S3-19 | B45.lean | `STWardTypePPin`, `STB45Pin` (B4, B5, eq:Ward_typeP) | B45 (1196×1.15) | 1380 | S3-04, S3-05, S3-06 | prover-hard | medium |
| S3-20 | ZeroModeCalc.lean | Q^(A), P^(i) calculus; commute with Theta, U; (iisuwjyys) | new (paper lines) | 1200 | S3-03, S3-04, EK-5 | prover-max | high |
| S3-21 | QtNonzero.lean | `STOeqQtNZ`: kernel sum_decay_nonzero, SEforLn, martingale (case (ii)) | new (paper lines) | 1500 | S3-20, S3-09, EK-5, T2039 grid pins | prover-max | high |
| S3-22 | QtNonzeroEnd.lean | `STOeqQtNZ`: grid endpoint and budget (case (ii)) | new (paper lines) | 1500 | S3-21 | prover-max | high |
| S3-23 | ScaleFacts3.lean | scale facts of Steps 3-4: hscale, hBA, window, k_min, regimes | new (paper lines) | 800 | S1-08 (merged by then), S3-01 | prover-hard | medium |
| S3-24a | IterationsA.lean | Psi-calculus and the chain bound (xiu2n+2psi) with (5.118) | Step3 (1805×0.5) | 1100 | S3-23, S1-09 (Split) | prover-hard | medium |
| S3-24b | IterationsB.lean | `STIterations`, `STIterationsII` (one step); case (ii) is new | Step3 (1805×0.45) | 1210 | S3-24a, S3-18b, S3-22 | prover-max | high |
| S3-25 | Step3.lean | `STStep3R` both cases (probe `st_step3_skeleton`) | Step3 (1805×0.1) | 680 | S3-24b | prover | low |
| S3-26 | Step4.lean | `STStep4R` (probe `st_step4_skeleton`) | Step45 (1318×0.5) | 860 | S3-12, S3-18b, S3-22 | prover | low |
| S3-27 | Step34.lean | general (s,t): middle time, net lift, `STLmax`/`STLK` at t | new (paper lines) | 700 | S3-25, S3-26, ST-1 net lift (S1-34) | prover-hard | medium |

tickets: 34; estimated lines total 37820; mean 1112; min/max per ticket: 600 1500
RBM2D ST-3 files used as sources: 24 (25261 kept lines)
not ported / elsewhere: 17 files, 13730 kept lines (script rows below)
  PPVocab: kept 1199 — (+,+) base: not on the d>=3 route
  PPKernel: kept 313 — (+,+) base
  PPGoodEvent: kept 946 — (+,+) base
  PPCondVar: kept 413 — (+,+) base
  PPDrift: kept 513 — (+,+) base
  PPClosure: kept 1070 — (+,+) base
  LocalFormCalc: kept 3340 — a-local-form: replaced by EK-4 (sum_res_2)
  LocalFormCuts: kept 2120 — a-local-form
  LocalFormLin: kept 498 — a-local-form
  AltSymm: kept 407 — symmetry for d=2 Case4: replaced by EK-4
  Region: kept 0 — class d (RBM2D unreachable)
  Chain: kept 424 — ST-6 chain (initAtZero, chainTarget)
  HierAlgebra: kept 704 — shared with ST-2 (drift algebra, T2039)
  HierarchyN: kept 38 — shared with ST-2 (drift identity)
  ScaleFacts: kept 312 — moved to ST-1 (S1-08)
  PerTimeCalc: kept 615 — moved to ST-1 (S1-07..09)
  Split: kept 818 — moved to ST-1 (S1-09)
all ST-3 files: 41 (incl. Region), kept total 38991; check mapped+notported = 38991
roles {'prover': 5, 'prover-hard': 23, 'prover-max': 6}
risk {'low': 4, 'medium': 21, 'high': 9}

Order and cuts (hand): `S3-01..05` have no ST-2 dependency and can start now (S3-01 after this report is merged); ST-2 (T2039) needs `HierVocab`, `HierAlgebra`, `HierarchyN`, `KcalDecay` first (RBM2D imports, P.1), so S3-01 and S3-06 should precede the ST-2 grid proof tickets; S3-10..22 need the grid pins of T2039 and the consumer forms of EK-6; S3-24b needs S3-18b and S3-22 for `STXiBoot` in both cases; S3-12, S3-18b, S3-22 and S3-24b are the prover-max tickets on the critical path.  EK-6 and KL12 are outside ST-3.

## P.8 Instances, extreme inputs, numeric checks (items 6, 9; hand + scripts)

Compiled instances (`theorem inst_*`, probe section 7; every deterministic hypothesis is discharged, stochastic premises stay hypotheses): `inst_step3`, `inst_step3I`, `inst_step3II`, `inst_step4`, `inst_step4I`, `inst_step4II`, `inst_SEforLn`, `inst_OeqNQ`, `inst_OeqQt`, `inst_OeqQtNZ`, `inst_WardTypeP`, `inst_B45`, `inst_iterations`, `inst_iterationsII`, `inst_contract`, `inst_newPQ`, `inst_mollifier`, `inst_qopNorm`, `inst_ekNdecay`, `inst_ekNAL`, `inst_ekRes1`, `inst_ekRes2`, `inst_ekNonzero`, `inst_step4_skeleton`, `inst_step4_skeletonB`, `inst_step3_skeleton`.  Data: `sz0` (merged; `d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6} → 0`, `z0`, `s ≡ 0`, `t ≡ 1/16`, `𝔠 = 1/6`, `𝔡 = κ = ε = 1/10`) and `szB` (new: `L = 4`, `W_n = n + 4`, `ilambda = 1`, `zB = 1/2 + i/64`, `lemT zB ≥ 31/32` proved from the merged `zt_im_lemma28`).  Regimes: case (i) `1-t = 15/16 ≥ g²/L²`; case (ii) `(s,t) = (15/16, 31/32)`: `1-s = g²/L²` (boundary of (ii)), `1-t = g²/(2L²)` (`g²/L^3 = 1/64 ≤ 1-t`, regime R3); `lem:iterations` `(7/8, 15/16)`: `1-s = 1/8 ≤ g²`, `1-t = g²/L²` (boundary of (i)); `(con_st_ind)` is discharged for **every** `𝔠_d > 0` at constant times (`conStInd_const`).

Extreme inputs tried (TEAM §8 lesson 25): `1-s → g²/L²` and `1-t → g²/L²` exactly (compiled: `inst_step3II`, `inst_iterations`); `n` large: the double induction `st_iterate` holds for all `(r,k)`, and `k_min(n) = ⌊2 + 8𝔠_d (n-1)⌋ + 1` closes for `n ≤ 300` ((a) closure script); `L` large: `sz0` has `L_n → ∞`; `g → W^{-d/2+𝔡}`: merged `sz1` instances of T2015; the deep regime R4 `1-t < g²/L^d` is numeric only ((a)(ii): the R4 point and the `m = 999` row of the limit table), because a compiled instance needs `lemT z ≥ 1-t` with `1-t ≈ N^{-1+ε}`, a proof about `msc` at `N`-dependent `Im z`.

Numeric checks of new statements (scripts `contract.py`, `vartheta.py`; `d = 3`, `W = 2`, `L = 3`, `N = 216`, `g = 1/2`, `E = 0`, six samples, `H_u = √u H`, `z_u = i(1-u) m(0)`, `E_a = W^{-d} 1_{I_a}`):
```
d,W,L,g,N= 3 2 3 0.5 216 ; samples 6
regime                          1-u      eta | contraction n=3: max over (sigma,a1,a2) of sum_a3|L3| / RHS(k=1), RHS(k=2) | Ward n=2: max|P1 L2 - (L1+ - L1-)/(2iN eta)|
1-u=0.5                         0.5      0.5 | max ratio k=1: 0.938  k=2: 0.938 (must be <= 1) | 6.94e-18
1-u=g^2/L^2                  0.0278   0.0278 | max ratio k=1: 0.818  k=2: 0.818 (must be <= 1) | 7.49e-16
1-u=g^2/(2L^3)              0.00463  0.00463 | max ratio k=1: 0.854  k=2: 0.854 (must be <= 1) | 2.86e-14
1-u=g^2/(10L^3)            0.000926 0.000926 | max ratio k=1: 0.437  k=2: 0.437 (must be <= 1) | 1.44e-12

d=3 g=0.50 L=48: Theta_t(0,0)=L^-d sum_k 1/(1-t Shat(k))
       1-t    ell_t (1-t)Theta(0,0)         ell^-2         ell^-d  ratio to ell^-d
   1.0e-01     1.58      1.849e-01      4.000e-01      2.530e-01             0.73
   1.0e-02     5.00      2.288e-02      4.000e-02      8.000e-03             2.86
   1.0e-03    15.81      2.450e-03      4.000e-03      2.530e-04             9.68
   3.0e-04    28.87      7.490e-04      1.200e-03      4.157e-05            18.02
   1.0e-04    48.00      2.566e-04      4.340e-04      9.042e-06            28.38
   3.0e-05    48.00      8.341e-05      4.340e-04      9.042e-06             9.22
```
First block: `max Σ_{a_3} |𝓛^{(3)}| / ((W^d η)⁻¹ (max|𝓛^{(1)}| max|𝓛^{(3)}|)^{1/2})` is below 1 in all four regimes (`(yi2oslxj2)`, `n = 3`, `k = 1, 2`), and the Ward step of `lem: newPQ` `P^{(1)} 𝓛^{(2)} = (𝓛^{(1)}_+ - 𝓛^{(1)}_-)/(2iNη)`, `N = (WL)^d`, holds to rounding.  Second block: `(1-t) Θ_t(0,0) ℓ_t^d` grows like `ℓ_t` (0.73 → 28.4), so the `Θ`-based `ϑ` of RBM2D has sup norm above `C ℓ_t^{-d}` at `d = 3`.

## P.9 Findings, paper-delta candidates, registry classes, Mathlib names (hand)

**Findings.** (F-A) 10 of the 37 files (`PP*` six files 4454 kept lines; `LocalForm*` three files 5958; `AltSymm` 407) are not on the `d ≥ 3` route: `(Eq:Gdecay_w)` covers all four charges (`1_2:1349`), and `(sum_res_2)` needs only sum-zero and decay (EK-4), not the `a-local-form` of the `d = 2` paper; 10819 kept lines are not ported.  (F-B) the `Θ`-based `ϑ` of RBM2D is not a valid mollifier at `d ≥ 3` (P.8); `ϑ` must be differentiable in `t` (`ℓ_t` has kinks): `STMollifierProps`.  (F-C) `(yi2oslxj2)` and `(u2jzooi-2)` are new at `d ≥ 3`.  (F-D) ST-2 imports nine ST-3 files in RBM2D (P.1): ST-3 tickets S3-01, S3-06 (and the drift algebra `HierAlgebra`, `HierarchyN`, 742 kept lines, which I leave to the ST-2 design T2039) must precede the ST-2 grid proofs.  (F-E) `lem:propT`, `claim:TTk`, `(sum_res_1)`, `(eq:latticesum_d3)` are not consumed by Steps 3–4 (P.3); `(eq:sumtwoloop)` needs the lattice sum `W^d Σ_{a₂} 𝒯_t(|a₁-a₂|) ≺ η_t⁻¹` of the tail function, which is not an EK pin (route: merged `RadialSum`, S3-06).  (F-F) the case-(ii) iteration (`eq:psipara_smalletacase`, `3_5:1577`) has no proof in the paper ("we omit the details", `3_5:1594`): `STIterationsII` is a new proof obligation with `A = (W^{-d}B_{s,0})⁻¹`.  (F-G) `lem:iterations` uses `(5.118)` of [YY_25] (`3_5:1841`), an external step; RBM2D has it as `loopXi_le` (ST-1, S1-09).  (F-H) `STKbound`/`STKward` are per time sequence; the uniform-in-`u` form needed in `st_step3_skeleton` follows because the `𝒦`-bounds are deterministic (choose the maximizing `u_n`): one small lemma in S3-06.  (F-I) the regimes are properties of the whole sequence (`∀ n`); the footnote of `3_5:1105` (middle time `u = 1-g²/L²`) is handled for general `(s,t)` by S3-27, by modifying the sequences off the set of `n` where a regime fails.

**Paper-delta candidates (`T2041a`…).** `T2041a`: `(am;asoi222)` is pinned with control parameters constant in `v ∈ [s,u]` (depending on the endpoint `u`), the maxima over `O(1)` terms written as sums, and only the lengths that occur controlled; `lem:STOeq_NQ` has the supremum of the hatted self-term on the right.  `T2041b`: the mollifier of `rmk:choosechi` is pinned by its properties (`STMollifierProps`: sum one, sup bound, differentiable, `∂_t` bound) and an existence pin; the scale in `f_t` must be smoothed (kinks of `ℓ_t`).  `T2041c`: `lem_+Q` carries `4 ≤ W^ε` and `L^d ≤ W^K` (same defect as T2016b, T2042a).  `T2041d`: Steps 3–4 are pinned per regime `R ∈ {STAny, STCaseI, STCaseII}`; the general statement is an assembly pin (S3-27).  `T2041e`: the quantifier order `∀ C_d ∃ 𝔠_d` (`(eq:sumtwoloop)`, `3_5:1070`: "sufficiently small depending on `C_d`"), consistent with `STMainInd` when `C_d` is the Step-2 exponent.  `T2041f`: case-(ii) `A = (W^{-d}B_{s,0})⁻¹` (the printed `Ψ`); case (i) `A = g² W^d`.  `T2041g`: `lem:SEforLn` (4) is pinned for `(ℰ⊗ℰ)^{M,(n)} = Σ_k (ℰ⊗ℰ)^{M,(n;k)}` (`defEOTE`, `3_5:176-180`); the paper states it for each `(n;k)`, which implies the sum up to the factor `n`.  `T2041h`: `lem_wardineq_K` is pinned at the scale `N` (`STKward`), from the `L^τ`-loss form of KL12.

**Registry classes (DECISIONS §16, §20) of the `Prop`s the pins take as hypotheses.**  Nothing is left without a proving ticket.  `STKbound` (KL7), `STLK` (ST-6 chain induction), `STStep1` (S1-36; its output `STStep1Loop` is a hypothesis here): merged, in `owedProps` of `RBM3D/Test/Axioms.lean`; `STConStInd`, `STFlow`: merged, in `structuralProps`.  `STKward`: owed (KL12, bridge in S3-06).  `STStep2Concl` and its three parts, `STGdecayW`: owed (ST-2, T2039).  `STLmaxU` (hypothesis of Step 4), `STXiBoot` (hypothesis of `STIterR`), `STIterHyp`: owed (S3-25, S3-18b/S3-22).  `STContract`, `STNewPQ`, `STSEforLn`, `STOeq*`, `STIterations*`, `STMollifierEx`, `STQopNorm`, `STWardTypePPin`, `STB45Pin`: owed when used as hypotheses.  `STEK*` consumer pins: owed (EK-6).  `STMollifierProps`, `STCaseI`, `STCaseII`, `STAny`, `STRegIterI`, `STEKDecay`, `STEKLow`, `STEKWin`, `STAlternating`: structural (properties of an object, regimes, data conditions).  The probe is never imported, so `RBM3D/Test/Axioms.lean` is not touched.

**Verified Mathlib names** (script `origin.lean`: each identifier of the probe resolved with `resolveGlobalConstNoOverload`, module read from the environment; names of the `Real.*`, `Finset.*`, `Nat.*`, `Fintype.*`, `ZMod.*`, `Matrix.*`, `Filter.*` families and the order/field lemmas used; the tactics `by_cases`, `by_contra`, `norm_num`, which also resolve, are omitted):
```
abs_le abs_of_pos abs_pos add_le_add Complex.I div_le_div_iff₀ div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_le_iff₀ div_lt_iff₀ div_lt_one div_nonneg
div_nonpos_of_nonpos_of_nonneg div_pos exists_nat_gt Filter.eventually_ge_atTop Filter.Eventually.of_forall Filter.tendsto_atTop_mono Filter.tendsto_pow_atTop Fin.ext
Fin.sum_univ_three Finset.exists_mem_eq_sup' Finset.Icc Finset.Ioc Finset.le_sup' Finset.mem_univ Finset.sum_filter Finset.sum_ite_eq' Finset.sum_sub_distrib Finset.univ
Finset.univ_nonempty Fintype.sum_equiv Fintype.sum_prod_type' Function.update gt_mem_nhds inv_anti₀ inv_le_one_of_one_le₀ inv_one inv_pos ite_false le_of_eq le_rfl
le_trans List.ofFn lt_div_iff₀ lt_min lt_of_le_of_lt lt_of_lt_of_le Matrix.cons_val_zero MeasureTheory.measure_mono min_le_left min_le_right mul_comm mul_le_mul
mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_neg_of_pos_of_neg mul_nonneg mul_one mul_pos Nat.cast_nonneg Nat.le_add_right Nat.le_mul_of_pos_right
Nat.le_self_pow Nat.lt_or_ge Nat.pow_le_pow_left Nat.strong_induction_on Nat.succ_pos norm_nonneg norm_zero not_or one_le_div one_le_pow₀ one_pos Or.inr
pi_norm_le_iff_of_nonneg Pi.zero_apply pow_le_pow_left₀ pow_nonneg pow_pos Real.exp Real.one_le_rpow Real.one_lt_rpow Real.one_rpow Real.pow_rpow_inv_natCast
Real.rpow_add Real.rpow_le_one Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_mul
Real.rpow_natCast Real.rpow_neg Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.sqrt Real.sqrt_eq_rpow Real.sqrt_le_sqrt Real.sqrt_one Real.sqrt_sq
Real.zero_rpow Set.Icc Set.Ico Set.mem_univ Set.univ sq_nonneg sub_zero tendsto_const_nhds tendsto_natCast_atTop_atTop tendsto_natCast_atTop_iff
tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_rpow_atTop two_pos zero_le_one zero_sub ZMod.val_one'' ZMod.val_zero
```

## P.10 Scripts (verbatim; all read RBM2D through a `git archive` copy of `c9a24cf` in the scratch directory or through `git show`; none writes in `../RBM1D` or `../RBM2D`)

Commands: `git -C ../RBM2D --no-optional-locks archive c9a24cf RBM2D | tar -x -C $S/rbm2d`; then `python3 inv.py`, `inv_table.py`, `splitcalc.py`, `ekuse.py`, `clash.py <probe> <worktree>`, `cites.py`, `extract.py <probe> NAMES --wrap 175`, `decls.py <probe>`, `contract.py`, `vartheta.py`; `lake env lean origin.lean` (names), `mkportmap.py`, `mkreport.py` (these two assemble the files).
### graph.py
```python
#!/usr/bin/env python3
# Import graph of RBM2D at c9a24cf (scratch copy); who imports Induction files, grouped by the portmap sub-gate rule.
import re, os, glob, collections, sys
R='/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2041/rbm2d'
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
    ind=[p for p in text if p.startswith('RBM2D/Induction/')]
    c=collections.Counter(grp(p) for p in ind); print(c)
    st3=sorted(p for p in text if grp(p)=='ST-3')
    print(len(st3),'ST-3 files')
    # who outside ST-3 imports ST-3 files
    imported_by=collections.defaultdict(list)
    for p,l in imps.items():
        for q in l: imported_by[q].append(p)
    for f in st3:
        ext=[x for x in imported_by[f] if grp(x)!='ST-3']
        print(os.path.basename(f), 'ext-importers:', sorted(set((grp(x),os.path.basename(x)) for x in ext)))
```
### inv.py
```python
#!/usr/bin/env python3
"""T2041 item 1: inventory of the RBM2D ST-3 files at c9a24cf (read from a git-archive copy in the scratch dir; kept lines at
0c1330a by `git show`); class and labels from the T2002 portmap rows; exponent tokens recomputed with the portmap's stats.py regexes;
public declarations and their textual references from ST-4/ST-5/ST-6 files (and, for the dependency order, ST-1/ST-2/UN)."""
import re, os, sys, subprocess, collections, json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from graph import text, grp, imps
REPO='/Users/junyin/Lean_proof/RBM2D'
PORT='/Users/junyin/Lean_proof/RBM3D/docs/reports/T2002-portmap.md'
def git(*a):
    r=subprocess.run(['git','-C',REPO,'--no-optional-locks',*a],capture_output=True,text=True)
    return r.stdout if r.returncode==0 else None
# portmap rows
pm={}
for l in open(PORT,encoding='utf-8'):
    if l.startswith('| ') and '.lean |' in l:
        c=[x.strip() for x in l.strip().strip('|').split('|')]
        if len(c)>=7 and re.match(r'^[A-Za-z0-9_]+\.lean$',c[0]):
            pm.setdefault(c[0],[]).append(c)
st3=sorted(p for p in text if grp(p)=='ST-3')
ST3_MOVED={'ScaleFacts','PerTimeCalc','Split'}   # T2015 (DECISIONS 19): moved to ST-1 (S1-07..S1-09)
def strip_comments(t):
    t=re.sub(r'/-.*?-/','',t,flags=re.S)
    return re.sub(r'--[^\n]*','',t)
TOK=[('pow2',r'(\(W : ℝ\)|\(L : ℝ\)|\bW\b|\bL\b|\(W \* L\)|\(W : ℂ\)⁻¹|\(W : ℝ\)⁻¹|\(W : ℂ\)|\(\(W \* L\) \^ 2 : ℕ\)|size)\)?\s*\^\s*2\b'),
     ('sup2',r'(W|L|N)[⁻]?²|⁻²|\bd = 2\b|Z_L\^2|Z_\{WL\}\^2|\(W L\)²'),('five',r'\b5⁻¹|\(1 / 5\)|1/5\b')]
declre=re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:protected\s+|private\s+|noncomputable\s+|unsafe\s+)*)(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)\s+([^\s({:\[]+)',re.M)
alldecl=collections.defaultdict(set)
for q,t in text.items():
    for m in declre.finditer(t):
        alldecl[m.group(3).split('.')[-1]].add(os.path.basename(q))
decls={}
for p in st3:
    t=text[p]; out=[]
    for m in declre.finditer(t):
        mods,kind,name=m.group(1),m.group(2),m.group(3)
        line=t.count('\n',0,m.start())+1
        out.append((kind,name,line,'private' in mods))
    decls[p]=out
cons_groups=['ST-4','ST-5','ST-6']
others=['ST-1','ST-2','UN']
ctext={p:strip_comments(t) for p,t in text.items()}
idre=re.compile(r"[A-Za-z_][\w']*")
toks={p:set(idre.findall(t)) for p,t in ctext.items()}
grpof={p:grp(p) for p in text}
STOP={'with','mono','sqrt_of','finset_sum_of','log_nonneg','zeroF','norm_T_le'}
def refs(name,groups_):
    short=name.split('.')[-1]
    if len(short)<5 or short in STOP or len(alldecl.get(short,()))!=1: return {}
    res=collections.defaultdict(list)
    for q,tk in toks.items():
        g=grpof[q]
        if g in groups_ and short in tk: res[g].append(os.path.basename(q)[:-5])
    return res
rows=[]
tsv=[]
for p in st3:
    b=os.path.basename(p); t=text[p]; n=t.count('\n')
    k=git('show',f'0c1330a:{p}'); kept=k.count('\n') if k is not None else -1
    cls=pm[b][0][3] if b in pm else '?'
    tok=sum(len(re.findall(rg,t)) for _,rg in TOK)
    pmtok=re.search(r'exponent tokens (\d+)',pm[b][0][5]).group(1) if b in pm and 'exponent tokens' in pm[b][0][5] else ('0' if b in pm else '?')
    labs=pm[b][0][6] if b in pm else ''
    pub=[(k_,nm,ln) for (k_,nm,ln,pr) in decls[p] if not pr]
    # names referenced from outside this file by groups
    byg=collections.defaultdict(set)
    used=[]
    for (k_,nm,ln) in pub:
        r=refs(nm,cons_groups+others)
        for g,fs in r.items():
            for f in fs:
                if f!=b[:-5]: byg[g].add(f)
        c456={g:fs for g,fs in r.items() if g in cons_groups and fs}
        if c456: used.append((nm,ln,{g:sorted(f for f in fs) for g,fs in c456.items()}))
    rows.append(dict(file=b,lines=n,kept=kept,cls=cls,tok=tok,pmtok=pmtok,labels=labs,ndecl=len(pub),npriv=len(decls[p])-len(pub),
                     moved=b[:-5] in ST3_MOVED,used=used,byg={g:sorted(v) for g,v in byg.items()}))
json.dump(rows,open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'inv.json'),'w'),ensure_ascii=False,indent=1)
if __name__=='__main__':
    tl=sum(r['lines'] for r in rows); tk=sum(max(r['kept'],0) for r in rows)
    print(f'files={len(rows)} lines={tl} kept={tk}; moved to ST-1 by T2015: {sum(1 for r in rows if r["moved"])} files, kept={sum(r["kept"] for r in rows if r["moved"])}')
    print(f'token check (recomputed vs portmap): '+'; '.join(f'{r["file"][:-5]}:{r["tok"]}!={r["pmtok"]}' for r in rows if str(r['tok'])!=str(r['pmtok'])) or 'all equal')
    cc=collections.Counter(r['cls'] for r in rows); print('classes',dict(cc))
```
### inv_table.py
```python
#!/usr/bin/env python3
"""Markdown inventory table of the 41 RBM2D ST-3 files at c9a24cf (T2041 item 1) from inv.json."""
import json,os,sys,collections
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from graph import imps, grp
impby=collections.defaultdict(list)
for f,l in imps.items():
    for q in l: impby[q].append(f)
rows=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'inv.json')))
MOVED={'ScaleFacts','PerTimeCalc','Split'}
print('| file | lines | kept | cl | tok | #pub/#priv | labels cited (this paper) | public names used by ST-4/ST-5/ST-6 files (script) | imported by (files, other groups; import graph) |')
print('|---|---|---|---|---|---|---|---|---|')
for r in rows:
    nm=r['file'][:-5]
    used=[u for u in r['used']]
    uu='; '.join(f"{n}→{'/'.join(sorted(g[3:] for g in c))}" for n,l,c in used[:5])+(' …' if len(used)>5 else '')
    labs=r['labels'].replace('|','/')
    if len(labs)>70: labs=labs[:67]+'…'
    pth='RBM2D/Induction/'+r['file']
    byg=collections.defaultdict(set)
    for q in impby[pth]:
        g=grp(q)
        if g!='ST-3': byg[g].add(os.path.basename(q)[:-5])
    by=', '.join(f"{g}:{'/'.join(sorted(v))}" for g,v in sorted(byg.items()))
    tag=' (→ST-1)' if nm in MOVED else ''
    print(f"| {nm}{tag} | {r['lines']} | {r['kept']} | {r['cls']} | {r['tok']} | {r['ndecl']}/{r['npriv']} | {labs} | {uu or '—'} | {by or '—'} |")
```
### splitcalc.py
```python
#!/usr/bin/env python3
"""Split table of ST-3 (T2041 item 8): the RBM2D files (kept lines at 0c1330a, inv.json) mapped to RBM3D proof tickets.
Estimated lines: ports `kept * 1.15` (class b, d-changes) times the share of the file, new work by paper lines."""
import json,os,collections
rows={r['file'][:-5]:r for r in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'inv.json')))}
kept=lambda f: max(rows[f]['kept'],0)
# (id, new file under RBM3D/Induction, statements, sources [(file,factor)], new lines, deps, role, risk)
T=[
('S3-01','Step34Pins','vocabulary `STXiL..STee`, pins of probe sections 2-4, registry lines, instances',[('HierVocab',1.0)],450,'S1-07 (merged), T2041 probe','prover','low'),
('S3-02','Contract','`STContract` (ygdhmsgq; new at d>=3)',[],700,'S3-01','prover-hard','medium'),
('S3-03','NewPQ','`STNewPQ` (lem: newPQ; Ward for L and K)',[],600,'S3-01, S3-02, KLK_ward (merged)','prover-hard','medium'),
('S3-04','QopAlgebra','`STMollifierEx`, algebra of `P, vartheta, Q_t` (P Q = 0, Theta preserves sum-zero, commutator)',[('SumZeroQ',1.15)],450,'S3-01, PT pins (merged)','prover-hard','medium'),
('S3-05','QopNorm','`STQopNorm` (lem_+Q, K = 1/c)',[('QopBounds',1.15)],0,'S3-04','prover','low'),
('S3-06','KDecay','K-loop fast decay, `STKward` bridge (KL12), lattice sum of the tail 𝒯 (eq:sumtwoloop)',[('KcalDecay',1.15)],200,'KL7, KL12, merged RadialSum','prover-hard','medium'),
('S3-07a','DecayLoopA','lem_decayLoop (decay of L-loops beyond W^eps l_u)',[('DecayLoop',1.15)],0,'T2039 (Step 2 pins), S1 GbEXP','prover-hard','medium'),
('S3-07b','DecayLoopB','decay through cuts, label decay of the E terms',[('BcalEDecay',1.15)],0,'S3-07a','prover-hard','medium'),
('S3-08','SEforLn1','lem:SEforLn (1), (2)',[('BcalE',0.55)],300,'S3-02, S3-06, S3-07b','prover-hard','medium'),
('S3-09','SEforLn2','lem:SEforLn (3), (4) (contraction (u2jzooi-2) for the martingale term)',[('BcalE',0.45)],400,'S3-02, S3-06, S3-08','prover-hard','high'),
('S3-10','NQGood','NQ: good events and inputs',[('NonAltGood',1.15)],0,'T2039 grid pins, EK-6, S3-09','prover-hard','medium'),
('S3-11','NQBudget','NQ: budget arithmetic at d>=3 exponents',[('NonAltBudget',1.15)],0,'S3-10','prover-hard','medium'),
('S3-12','NQEnd','`STNQConcl`: endpoint assembly',[('NonAltEnd',1.15)],0,'S3-10, S3-11','prover-max','high'),
('S3-13a','QGridA','Q-process on the grid: stopped Duhamel',[('AltGridQ',0.60)],0,'T2039 grid pins, S3-04','prover-hard','medium'),
('S3-13b','QGridB','Q-process on the grid: drift',[('AltGridQ',0.55)],0,'S3-13a','prover-hard','medium'),
('S3-14','QProxy','martingale part with Q (x) Q (variance proxy)',[('AltProxyQ',1.15)],0,'S3-13b, S3-09','prover-hard','high'),
('S3-15a','QDriftA','Q/E split of the drift and of the initial term (1)',[('AltDriftQ',0.60)],0,'S3-13b','prover-hard','medium'),
('S3-15b','QDriftB','Q/E split of the drift and of the initial term (2)',[('AltDriftQ',0.60)],0,'S3-15a','prover-hard','medium'),
('S3-16a','QLevelsA','levels of Q_u B_m, m = 0, 5 (Q0), start level',[('AltLevelsQ0',1.15),('AltLevelsE',1.15)],0,'S3-15b','prover-hard','medium'),
('S3-16b','QLevelsB','levels of Q_u B_m, m = 1..5',[('AltLevelsQ',1.15)],0,'S3-16a','prover-hard','high'),
('S3-17a','QBudgetA','budget terms of the alternating assembled bound',[('AltBudgetTerms',1.15),('AltBudget',1.15)],0,'S3-16b','prover-hard','medium'),
('S3-17b','QBudgetB','absorption pin (13 eventual inequalities at d>=3 exponents)',[('AltAbsorb',1.15)],0,'S3-17a','prover','medium'),
('S3-18a','QEndA','alternating endpoint, vocabulary and compositions C1-C5',[('AltEndCompose',1.15)],0,'S3-17b','prover-hard','medium'),
('S3-18b','QEndB','alternating endpoint, assembly C6 -> `STXiBoot` (alternating part)',[('AltEnd',1.15)],0,'S3-18a','prover-max','high'),
('S3-19','B45','`STWardTypePPin`, `STB45Pin` (B4, B5, eq:Ward_typeP)',[('B45',1.15)],0,'S3-04, S3-05, S3-06','prover-hard','medium'),
('S3-20','ZeroModeCalc','Q^(A), P^(i) calculus; commute with Theta, U; (iisuwjyys)',[],1200,'S3-03, S3-04, EK-5','prover-max','high'),
('S3-21','QtNonzero','`STOeqQtNZ`: kernel sum_decay_nonzero, SEforLn, martingale (case (ii))',[],1500,'S3-20, S3-09, EK-5, T2039 grid pins','prover-max','high'),
('S3-22','QtNonzeroEnd','`STOeqQtNZ`: grid endpoint and budget (case (ii))',[],1500,'S3-21','prover-max','high'),
('S3-23','ScaleFacts3','scale facts of Steps 3-4: hscale, hBA, window, k_min, regimes',[],800,'S1-08 (merged by then), S3-01','prover-hard','medium'),
('S3-24a','IterationsA','Psi-calculus and the chain bound (xiu2n+2psi) with (5.118)',[('Step3',0.50)],200,'S3-23, S1-09 (Split)','prover-hard','medium'),
('S3-24b','IterationsB','`STIterations`, `STIterationsII` (one step); case (ii) is new',[('Step3',0.45)],400,'S3-24a, S3-18b, S3-22','prover-max','high'),
('S3-25','Step3','`STStep3R` both cases (probe `st_step3_skeleton`)',[('Step3',0.10)],500,'S3-24b','prover','low'),
('S3-26','Step4','`STStep4R` (probe `st_step4_skeleton`)',[('Step45',0.50)],200,'S3-12, S3-18b, S3-22','prover','low'),
('S3-27','Step34','general (s,t): middle time, net lift, `STLmax`/`STLK` at t',[],700,'S3-25, S3-26, ST-1 net lift (S1-34)','prover-hard','medium'),
]
notported={'PPVocab':'(+,+) base: not on the d>=3 route','PPKernel':'(+,+) base','PPGoodEvent':'(+,+) base','PPCondVar':'(+,+) base','PPDrift':'(+,+) base','PPClosure':'(+,+) base',
 'LocalFormCalc':'a-local-form: replaced by EK-4 (sum_res_2)','LocalFormCuts':'a-local-form','LocalFormLin':'a-local-form','AltSymm':'symmetry for d=2 Case4: replaced by EK-4',
 'Region':'class d (RBM2D unreachable)','Chain':'ST-6 chain (initAtZero, chainTarget)','HierAlgebra':'shared with ST-2 (drift algebra, T2039)','HierarchyN':'shared with ST-2 (drift identity)',
 'ScaleFacts':'moved to ST-1 (S1-08)','PerTimeCalc':'moved to ST-1 (S1-07..09)','Split':'moved to ST-1 (S1-09)'}
used=collections.defaultdict(float)
tot_est=0; tot_src=0
print('| id | new file `RBM3D/Induction/…` | statements | RBM2D sources (kept lines × share) | est lines | after | role | risk |')
print('|---|---|---|---|---|---|---|---|')
for (i,f,st,srcs,new,deps,role,risk) in T:
    sl=[]; sk=0
    for (s,fac) in srcs:
        sl.append(f'{s} ({kept(s)}×{fac:g})'); used[s]+= fac if s in ('BcalE','Step3','Step45','AltGridQ','AltDriftQ') else 1.0
        if fac>=1.0 or s in ('HierVocab','SumZeroQ','QopBounds'): sk+=kept(s)*fac
        else: sk+=kept(s)*fac
    est=int(round(sk+new,-1)) if (sk+new)>0 else 0
    tot_est+=est
    print(f'| {i} | {f}.lean | {st} | {", ".join(sl) if sl else "new (paper lines)"} | {est} | {deps} | {role} | {risk} |')
print()
n=len(T); print(f'tickets: {n}; estimated lines total {tot_est}; mean {tot_est//n}; min/max per ticket: ',end='')
ests=[]
for (i,f,st,srcs,new,deps,role,risk) in T:
    ests.append(int(round(sum(kept(s)*fac for s,fac in srcs)+new,-1)))
print(min(ests),max(ests))
mapped=sorted(set(s for t in T for s,_ in t[3]))
srck=sum(kept(s) for s in mapped)
print(f'RBM2D ST-3 files used as sources: {len(mapped)} ({srck} kept lines)')
npk=sum(kept(s) for s in notported)
print(f'not ported / elsewhere: {len(notported)} files, {npk} kept lines (script rows below)')
for s,why in notported.items(): print(f'  {s}: kept {kept(s)} — {why}')
allk=sum(kept(s) for s in rows)
print(f'all ST-3 files: {len(rows)} (incl. Region), kept total {allk}; check mapped+notported = {srck+npk}')
cnt=collections.Counter(t[6] for t in T); print('roles',dict(cnt)); print('risk',dict(collections.Counter(t[7] for t in T)))
```
### ekuse.py
```python
#!/usr/bin/env python3
"""Which evolution-kernel statements do Steps 3-4 (3_5:900-1934, outside the kernel lemmas 1615-1673) use?  Occurrences of \\eqref/\\Cref/\\ref of each label."""
import re
tex=open('/Users/junyin/Lean_proof/RBM3D/paper/tex/3_5_Loop_Hierarchy.tex',encoding='utf-8').read().split('\n')
labels=['lem:sum_Ndecay','sum_res_Ndecay','sum_res_1','sum_res_2_NAL','sum_res_2','lem:sum_decay','lem:sum_decay_nonzero','sum_res_Ndecay_nonzero','lem:propT','claim:TTk','eq:latticesum_d3','eq:THETAINFTINF','prop:ThfadC','prop:ThfadC0']
for lab in labels:
    hits=[]
    for i,l in enumerate(tex,1):
        if not (900<=i<=1934) or 1615<=i<=1673: continue
        if l.lstrip().startswith('%'): continue
        if re.search(r'\\(?:eqref|Cref|cref|ref)\{[^}]*\b'+re.escape(lab)+r'\}',l): hits.append(i)
    print(f'{lab:28s} {hits if hits else "no occurrence"}')
```
### clash.py
```python
#!/usr/bin/env python3
"""Name-clash check: full qualified names (and short names) of the probe's declarations vs every .lean file of RBM3D/ on main (Probe excluded)."""
import re,sys,subprocess,glob,os,collections
probe=sys.argv[1]; main_root=sys.argv[2]
def decls(path,skip_priv=True):
    ns=[]; out=[]
    for l in open(path,encoding='utf-8'):
        m=re.match(r'^namespace\s+(\S+)',l)
        if m: ns.append(m.group(1)); continue
        m=re.match(r'^end\s+(\S+)',l)
        if m and ns and ns[-1]==m.group(1): ns.pop(); continue
        m=re.match(r'^(?:@\[[^\]]*\]\s*)?((?:noncomputable\s+|protected\s+|private\s+|partial\s+)*)(theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+([^\s({:\[]+)',l)
        if m and not (skip_priv and 'private' in m.group(1)):
            nm=m.group(3)
            full='.'.join(ns+[nm]) if not nm.startswith('_root_.') else nm[7:]
            out.append(full)
    return out
mine=decls(probe)
lib=collections.defaultdict(list)
for f in glob.glob(main_root+'/RBM3D/**/*.lean',recursive=True):
    if '/Probe/' in f: continue
    for n in decls(f,skip_priv=False): lib[n].append(os.path.relpath(f,main_root))
shortlib=collections.defaultdict(set)
for n,fs in lib.items(): shortlib[n.split('.')[-1]].update(fs)
full=[n for n in mine if n in lib]
short=sorted(set(n.split('.')[-1] for n in mine if n.split('.')[-1] in shortlib and n not in lib))
print(f'probe public declarations: {len(mine)}; library files scanned: {len(set(f for fs in lib.values() for f in fs))}')
print(f'full-name clashes (probe vs library): {len(full)}',full[:10])
print(f'same short name, different namespace: {len(short)}',short[:20])
```
### cites.py
```python
#!/usr/bin/env python3
"""Check every RBM2D file:line cite used in the T2041 report/portmap against `git show c9a24cf:RBM2D/<file>` (line contains the token)."""
import subprocess,sys
repo='/Users/junyin/Lean_proof/RBM2D'; ref='c9a24cf'
C=[('Induction/Step3.lean',294,'step3_Psi'),('Induction/Step3.lean',59,'R = (ℓ_t/ℓ_s)²'),('Induction/Step3.lean',63,'k = n + 1'),
 ('Induction/Step3.lean',440,'(5.118)'),('Induction/Step3.lean',421,'step3Lemma514'),('Induction/Step3.lean',1777,'theorem step3'),
 ('Induction/Step45.lean',105,'def Step4TargetV3'),('Induction/Step45.lean',1188,'theorem step4'),('Induction/Step45.lean',1258,'theorem step5'),
 ('Induction/HierVocab.lean',66,'def vartheta'),('Induction/HierVocab.lean',117,'def QopNorm'),('Induction/HierVocab.lean',150,'def LLf'),
 ('Induction/HierVocab.lean',159,'def ksimLK'),('Induction/HierVocab.lean',170,'def elklkN'),('Induction/HierVocab.lean',176,'def egtN'),
 ('Induction/HierVocab.lean',183,'def eeLoop'),('Induction/HierVocab.lean',190,'def eeN'),('Induction/HierVocab.lean',224,'def KcalDecay'),
 ('Induction/HierVocab.lean',236,'def DecayLoopAt'),('Induction/HierVocab.lean',284,'def BcalEPT'),('Induction/HierVocab.lean',365,'def B45PT'),
 ('Induction/HierVocab.lean',504,'def STOeqTargetV2'),('Induction/HierVocab.lean',511,'def PPTargetV2'),
 ('Induction/Defs.lean',76,'def xiL'),('Induction/Defs.lean',83,'def xiLK'),('Induction/Defs.lean',247,'def STOeqPT'),('Induction/Defs.lean',268,'def PPTwoLoopPT'),
 ('Induction/Defs.lean',277,'def Step3PT'),('Induction/Defs.lean',284,'def Step4PT'),
 ('Induction/Split.lean',569,'theorem loopXi_le'),('Induction/Split.lean',176,'⁻¹ ^ 2'),('Induction/Split.lean',615,'⁻¹ ^ 2'),
 ('Path/Scales.lean',44,'def scaleM'),('Path/Step2Props.lean',116,'def CondStInd'),
 ('Induction/KcalDecay.lean',692,'theorem kcalDecay'),('Induction/DecayLoop.lean',786,'theorem decayLoopFromML'),
 ('Induction/QopBounds.lean',525,'theorem qopNorm'),('Induction/QopBounds.lean',622,'theorem qopDecay'),
 ('Induction/SumZeroQ.lean',102,'SumZeroQ_Psum_vartheta'),('Induction/AltLevelsE.lean',446,'theorem stoeqTargetV2'),
 ('Induction/Chain.lean',274,'theorem initAtZero'),('Induction/Chain.lean',368,'theorem chainTarget'),
 ('Induction/AltEnd.lean',650,'def AltAbsorb'),('Induction/AltEnd.lean',418,'def AltLevelsE'),
 ('Induction/HierVocab.lean',62,'def Psum'),('Induction/HierVocab.lean',75,'def Qop'),('Induction/HierVocab.lean',295,'scaleM'),('Induction/HierVocab.lean',193,'LLf'),
 ('Induction/Step3.lean',438,'(5.107)')]
cache={}
ok=0; bad=[]
for f,l,tok in C:
    if f not in cache:
        r=subprocess.run(['git','-C',repo,'--no-optional-locks','show',f'{ref}:RBM2D/{f}'],capture_output=True,text=True)
        cache[f]=r.stdout.split('\n') if r.returncode==0 else None
    lines=cache[f]
    if lines is None: bad.append((f,l,tok,'file missing')); continue
    window=' '.join(lines[max(l-1,0):l+1]) if l<=len(lines) else ''
    if tok in window: ok+=1
    else: bad.append((f,l,tok,'token not at line'))
R3='/Users/junyin/Lean_proof/RBM3D'
for cm,f,l,tok in [('64b58eb','RBM3D/Probe/T2004Pins.lean',788,'def KLwardIneqAt'),('64b58eb','RBM3D/Probe/T2004Pins.lean',795,'def KLwardIneqPin'),('c961e62','RBM3D/Probe/T2016Pins.lean',507,'theorem ek_sum_fin_two')]:
    r=subprocess.run(['git','-C',R3,'--no-optional-locks','show',f'{cm}:{f}'],capture_output=True,text=True)
    lines=r.stdout.split('\n') if r.returncode==0 else []
    window=' '.join(lines[max(l-1,0):l+1]) if l<=len(lines) else ''
    C.append((f'{cm}:{f}',l,tok))
    if tok in window: ok+=1
    else: bad.append((f'{cm}:{f}',l,tok,'token not at line'))
print(f'cites checked (RBM2D at {ref}, RBM3D commits as named): {len(C)}; token found on the cited line (or the next): {ok}; failures: {len(bad)}')
for b in bad: print('  FAIL',b)
```
### extract.py
```python
#!/usr/bin/env python3
"""Print the statement text (docstrings omitted) of named declarations of the probe, with the line numbers.
usage: extract.py probe.lean NAME [NAME ...] [--wrap N] [--oneline]"""
import re,sys,textwrap
p=sys.argv[1]; args=sys.argv[2:]
wrap=None; oneline='--oneline' in args
args=[a for a in args if a!='--oneline']
if '--wrap' in args:
    i=args.index('--wrap'); wrap=int(args[i+1]); args=args[:i]+args[i+2:]
src=open(p,encoding='utf-8').read().split('\n')
for name in args:
    pat=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+'+re.escape(name)+r'(?=[\s({:\[])')
    for i,l in enumerate(src):
        m=pat.match(l)
        if m:
            kind=m.group(1); buf=[l]; j=i+1
            if kind in('theorem','lemma'):
                # up to the line containing ':=' (end of statement)
                k=i
                while ':=' not in src[k] and k<i+60: k+=1
                buf=src[i:k+1]
                buf[-1]=buf[-1].split(':=')[0].rstrip()
            else:
                k=i
                while k+1<len(src) and src[k+1].strip()!='' and not re.match(r'(def|theorem|lemma|abbrev|instance|/--|/-!|@\[|end |namespace |section |open |variable )',src[k+1]): k+=1
                buf=src[i:k+1]
            txt=' '.join(x.strip() for x in buf)
            txt=re.sub(r'\s+',' ',txt)
            if oneline: print(f'L{i+1}: '+txt)
            else:
                print(f'-- line {i+1}')
                print(textwrap.fill(txt,width=wrap,subsequent_indent='  ') if wrap else txt)
            break
    else:
        print(f'-- NOT FOUND {name}')
```
### decls.py
```python
#!/usr/bin/env python3
"""List the public declarations of the probe: kind, full name, line (namespace-aware)."""
import re,sys
p=sys.argv[1]
ns=[]; out=[]
for i,l in enumerate(open(p,encoding='utf-8'),1):
    m=re.match(r'^namespace\s+(\S+)',l)
    if m: ns.append(m.group(1)); continue
    m=re.match(r'^end\s+(\S+)',l)
    if m and ns and ns[-1]==m.group(1): ns.pop(); continue
    m=re.match(r'^(?:@\[[^\]]*\]\s*)?((?:noncomputable|private|protected)\s+)*(theorem|lemma|def|abbrev|structure|instance)\s+([^\s({:\[]+)',l)
    if m:
        kind=m.group(2); name=m.group(3); priv='private' in (l.split(kind)[0])
        out.append((kind,'.'.join(ns+[name]) if ns else name,i,priv))
for k,n,i,pr in out: print(f'{k}\t{n}\t{i}\t{"private" if pr else "public"}')
```
### contract.py
```python
# Numeric check at d=3, W=2, L=3 (N=216), g=1/2, E=0: (i) the contraction inequality (yi2oslxj2) for n=3, k=1,2;
# (ii) the Ward-averaging identity behind `lem: newPQ` (y2ussz) at n=2: P^{(1)} L^{(2)}_{(+,-),(a1,a2)} = (L^{(1)}_{+,a2}-L^{(1)}_{-,a2})/(2 i N eta).
import numpy as np, itertools, math
rng=np.random.default_rng(20261003)
d,W,L=3,2,3; g=0.5; E=0.0; n=W*L; N=n**d; NS=6; w=W**d
pts=list(itertools.product(range(n),repeat=d))
blk=lambda p: tuple(c//W for c in p)
def zd(a,b,m): t=(a-b)%m; return min(t,m-t)
bl=[blk(p) for p in pts]
blocks=sorted(set(bl)); bidx={b:i for i,b in enumerate(blocks)}; nb=len(blocks)
def SB(a,b):
    dist=sum(zd(a[i],b[i],L) for i in range(d))
    return (1.0 if dist==0 else (g*g if dist==1 else 0.0))/(1+2*d*g*g)
S=np.array([[SB(bl[i],bl[j])/W**d for j in range(N)] for i in range(N)])
m=(-E+1j*math.sqrt(4-E*E))/2
pos=[[i for i in range(N) if bidx[bl[i]]==a] for a in range(nb)]
perm=np.array([i for a in range(nb) for i in pos[a]])
def sample():
    X=rng.standard_normal((N,N))+1j*rng.standard_normal((N,N))
    X=np.triu(X,1)/math.sqrt(2); X=X+X.conj().T
    X=X+np.diag(rng.standard_normal(N))
    return X*np.sqrt(S)
Hs=[sample() for _ in range(NS)]
def blocksG(G,sg):
    Gp=G[np.ix_(perm,perm)].reshape(nb,w,nb,w).transpose(0,2,1,3)   # [a,b,i,j]
    return Gp if sg==0 else np.conj(Gp).transpose(1,0,3,2)          # sigma=+ : G ; sigma=- : G^*
def L1(G,s1):
    A=blocksG(G,s1); return np.einsum('aaii->a',A)/w                  # tr(G E_a) = w^-1 sum_i G[(a,i),(a,i)]
def L2(G,s1,s2):
    A,B=blocksG(G,s1),blocksG(G,s2)
    # tr(G1 E_a G2 E_b) = w^-2 sum_{i in a, j in b} G1[i,j] G2[j,i]
    return np.einsum('abij,baji->ab',A,B)/w**2
def L3(G,s1,s2,s3):
    A1,A2,A3=blocksG(G,s1),blocksG(G,s2),blocksG(G,s3)
    return np.einsum('abij,bcjk,caki->abc',A1,A2,A3,optimize=True)/w**3
print("d,W,L,g,N=",d,W,L,g,N,"; samples",NS)
print("%-26s %8s %8s | %-44s | %s"%("regime","1-u","eta","contraction n=3: max over (sigma,a1,a2) of sum_a3|L3| / RHS(k=1), RHS(k=2)","Ward n=2: max|P1 L2 - (L1+ - L1-)/(2iN eta)|"))
for name,x in [("1-u=0.5",0.5),("1-u=g^2/L^2",g*g/L**2),("1-u=g^2/(2L^3)",g*g/L**d/2),("1-u=g^2/(10L^3)",g*g/L**d/10)]:
    z=E+x*m.real+1j*x*m.imag; u=1-x; eta=x*m.imag
    r1=r2=0.0; wd=0.0
    for H in Hs:
        G=np.linalg.inv(math.sqrt(u)*H-z*np.eye(N))
        # max loops
        mx={1:max(np.abs(L1(G,s)).max() for s in (0,1))}
        mx[3]=max(np.abs(L3(G,*s)).max() for s in itertools.product((0,1),repeat=3))
        for s in itertools.product((0,1),repeat=3):
            T=np.abs(L3(G,*s)).sum(axis=2).max()                      # max over (a1,a2) of sum_{a3} |L3|
            rhs1=(mx[1]*mx[3])**0.5/(w*eta)                            # k=1: (2k-1,2n-2k-1)=(1,3)
            rhs2=(mx[3]*mx[1])**0.5/(w*eta)                            # k=2: (3,1)
            r1=max(r1,T/rhs1); r2=max(r2,T/rhs2)
        # Ward-averaging at n=2: P^(1) L2_{(+,-)}(a1,a2) = L^{-d} sum_{a1} L2 ; N=(WL)^d
        for (s1,s2) in ((0,1),(1,0),(0,0)):
            P1=L2(G,s1,s2).sum(axis=0)/L**d
            if s1!=s2:
                # vertex 1 summed: tr(G1 G2 E_b) w^-1 ... (L1_{+,b}-L1_{-,b})/(2 i eta) with sign by order
                lhs=P1
                rhs=(L1(G,0)-L1(G,1))/(2j*N*eta)    # G(+)G(-) = G(-)G(+): same value for both orders
                wd=max(wd,np.abs(lhs-rhs).max())
    print("%-26s %8.3g %8.3g | max ratio k=1: %.3f  k=2: %.3f (must be <= 1)%s | %.2e"%(name,x,eta,r1,r2,"" if max(r1,r2)<=1+1e-9 else " VIOLATION",wd))
```
### vartheta.py
```python
# The Theta-based mollifier of RBM2D (HierVocab.lean:66, vartheta = (1-t)^{k-1} prod_i Theta_t(a_1,a_i)) at d=3:
# its sup norm for k=2 is (1-t) Theta_t(0,0); (eq:derv_Theta) requires <= C (l_t^d)^{-1}, l_t = min(max(g/sqrt(1-t),1),L).
import numpy as np
d=3; g=0.5; L=48
ks=2*np.pi*np.arange(L)/L
K=np.meshgrid(ks,ks,ks,indexing='ij')
Shat=(1+2*g*g*sum(np.cos(k) for k in K))/(1+2*d*g*g)
print("d=3 g=%.2f L=%d: Theta_t(0,0)=L^-d sum_k 1/(1-t Shat(k))"%(g,L))
print("%10s %8s %14s %14s %14s %16s"%("1-t","ell_t","(1-t)Theta(0,0)","ell^-2","ell^-d","ratio to ell^-d"))
for x in (1e-1,1e-2,1e-3,3e-4,1e-4,3e-5):
    t=1-x; th=np.mean(1/(1-t*Shat)); ell=min(max(g/np.sqrt(x),1),L)
    print("%10.1e %8.2f %14.3e %14.3e %14.3e %16.2f"%(x,ell,x*th,ell**-2,ell**-d,x*th*ell**d))
```
### origin.lean (head; one `#origin NAME` per candidate)
```lean
import RBM3D.Probe.T2041Pins
open Lean Meta Elab Command
open MeasureTheory ProbabilityTheory Filter Matrix
elab "#origin " id:ident : command => do
  let env ← getEnv
  try
    let n ← resolveGlobalConstNoOverload id
    match env.getModuleIdxFor? n with
    | some i => logInfo m!"{id.getId} → {n} : {env.header.moduleNames[i]!}"
    | none => logInfo m!"{id.getId} → {n} : (this file)"
  catch _ => pure ()
```
