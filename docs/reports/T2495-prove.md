Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 07:23:43 UTC 2026

Setting: `(law, Flow, carrier, T0) = (seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, `d = 3`, `sz0`, `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`).
Check file: `lake env lean docs/tickets/checks/T2495-check.lean` on main 0a68e61d: exit 0, 0 error lines (393 output lines, all `#check`).
Paper: `lem_decayLoop` = claim at `3_5_Loop_Hierarchy.tex:1126-1131` (hypotheses `Gt_bound_flow`, `Eq:Gdecay_w`); Lean `k ≥ 1` (`k = 1` trivial, `DecayGen.lean:587-589`), `L^∞` diameter (existing delta T2002b).

### (i) Exponent table

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `κ` (target 1, 3, 4; `κm = κ`) | 1/2 | `0 < κ`; `κ ≤ Im m_n` (`EMn2BA_mF_data`, `EMn2BA.lean:125`) | `Im mS ≥ 4/5` (`flow_sz0` proof, `mS_im_half`): 3/10 |
| 2 | `ε` (target 2 (a),(b),4) | 1/10 | `0 < ε`; range uses `ε/2 = 1/20` | `ε/2 > 0` strict; no upper bound used |
| 3 | `𝔠, 𝔡` | 1/6, 1/10 | `Admissible` (`Defs/Sizes.lean:177`), `BAFlow.1` | `N ≤ W^6` (`sz0_size_le_W_pow`, `Defs/Sizes.lean:280`) so `W ≥ N^{1/6}`, not tight (`L < W` at every `n`: 4 < 32, 8 < 1024); target 4 `𝔠d ≤ 1/100` is a constant of `baStep2_holds`, not read |
| 4 | `N^{ε/2}` vs 2 (`baFlow_premises`, `NetLiftBA.lean:65-83`) | `N^{1/20} ≥ 2` iff `N ≥ 2^20` | holds eventually | `N_0 = 2^21`: factor 2 at `n = 0`, all `n` after |
| 5 | range (target 2 (a)) | `N^{-1} ≤ N^{-1+ε/2} ≤ 1 - t` | `1 ≤ N`, `-1 ≤ -1+ε/2` (needs `0 < ε`); `RangeCond (ε/2) t` from `baFlow_premises` | at `n = 0`: `N^{-0.95} = 9.9e-7 ≤ 11/60` |
| 6 | `1 - t₀` at `sz0` | in `[11/60, 1/3]` | lower: `Im z ≥ 11/30` (`zSeq_im_ge`) and `1-t₀ ≥ Im z/2` (`EMn2BA_one_sub_T0`); upper: `t₀ ≥ 2/3` (`t0_sz0`) | window `[s,t] = [1/10,1/2] ⊂ [0,t₀]` with `t₀ - 1/2 ≥ 1/6` |
| 7 | `t < 1` (targets 1, 2 (b)) | `t ≤ T0 < 1` | `EMn2BA_T0_lt_one` | `1 - 1/2 = 1/2` |
| 8 | cutoff `ellT L lam u` (statements 1–4) | 1 at `u ∈ {1/10, 1/2}` | `min (max (lam/√|1-u|, 1), L)`, `lam ≤ 1/64`, `L ≥ 4` | `√2·lam ≤ 0.023 < 1` |
| 9 | far-set threshold `ℓ_u W^{τ'}` vs `diam_∞ a` | `τ' ∈ {1/20, 1/5}` | `ℓ W^{τ'} ≤ STdiamInf a`; `a = (0,(h,h,h),0)`, `h = L/2 = 2(n+1)`, `W^{1/5} = 2(n+1)` | `τ' = 1/5`: equality (slack 0, allowed); `τ' = 1/20`: `W^{1/20} ≤ h` strict from `n = 0` (1.19 ≤ 2) |
| 10 | R1 / UBA-C1 | no R1 text in any statement | `TwistStep2_lam0_sq` stays inside `baKcalDecay_holds` | not applicable (table in ticket: crossing only inside merged result) |
| 11 | `Cd, 𝔠d` (target 4) | from `baStep2_holds d hLW hLWE` | `Cd > 0`, constants before `(𝔠, sz, z)` (`STStep2G`, `Step2Gen.lean:591`) | uniform in `(sz, z)`; target 1 is applied with this `Cd` |

### (i) bis. Hypothesis ledger per target (conclusion shape = check pin)

| target | route (merged names, file:line) | premises supplied | remaining input |
|---|---|---|---|
| 1 `baDecayLoopU_of` | `stDecayLoopUgL_of_step2` (`DecayGen.lean:583`), instance already elaborated in `DecayGenTw.lean:71-76` with `hK` open | `DecayGen_Spec` = `⟨hκ, EMn2BA_mF_data.1, rfl⟩`; `Admissible` = `hflow.1`; `t<1` = `(ht n).trans_lt (EMn2BA_T0_lt_one …)`; Ward = `DecayGenTw_baWardPair` (no hypotheses); `hK = baKcalDecay_holds d hd sz κ ε 𝔠 𝔡 z hκ hflow` (`KDecayBA.lean:692`) | `STGdecayWgL` only; no `0 < ε`, no `0 < g₀ n` (G1) |
| 2 (a) `baFlow_sizeInv_le` | `baFlow_premises` (`NetLiftBA.lean:65`) + `Real.rpow_le_rpow_of_exponent_le` | `RangeCond (ε/2) t`, `1 ≤ N` (`sz.one_le_size`) | none; `0 < ε` used |
| 2 (b) `baDecayLoopPT_of` | `stDecayLoopPTgL_of_step2` (`DecayGen.lean:461`) | as 1, plus `hst` (hypothesis of pin), `hrange` from 2 (a) | `STStep2DecayPTgL` |
| 3 `baDecayLoopAt_holds` | `stDecayLoopAtgL_of` (`DecayGen.lean:444`), needs only `hd`, Ward, `hK` | `hK` as 1; its own premises (`DecayGen_Spec`, `Admissible`, decay input) are premises of the merged body | none |
| 4 `baStep2Decay_holds` | `baStep2_holds` (`Step2CloseBA.lean:181`) `.2.2` of `STStep2ConclgL` (= `STLocalEntryUgL ∧ STAvgUgL ∧ STGdecayWgL`, `Step2Gen.lean:514`) feeds target 1 | `0 ≤ s`, `t ≤ T0`, `BAFlow`, `0 < κ` all binders of `STStep2G` | `BALWterm d`, `BALWtermExp d`; Step 1 and induction binders are binders of the frame |
| 5 `baSTLWB_of`, `baSTLWT_of` | `stLWBgL_of_LWtermG` (`Step2EventsGen.lean:1005`), `stLWTgL_of_LWtermExpG` (:1080), with `fun _ _ _ _ _ _ h => h.1`, `Step2EventsGenTw_baRot3 sz _ _`; the `d = 3` examples `Step2EventsGenTw.lean:144-150` use `by norm_num` for `3 ≤ 3`, here `hd` | `3 ≤ d`, F1, F7 | `BALWterm d` / `BALWtermExp d` |

Findings (verified by reading):
- G1: `STKcalDecaygL` is `∀ᶠ n` in its own body (`DecayGen.lean:83-88`); `DecayGenTw_baWardPair` and `EMn2BA_mF_data` hold at every `n`; no `0 < g₀ n` enters.
- G3: `Step2EventsGenTw_toFlowFM` is `rfl` (`Step2EventsGenTw.lean:81-82`); the `hU` of `baEtermDecaygL` (`SEforLnBA.lean:274`) is `STDecayLoopUgL` at `(baStep2Mat …).toFlowFM`, equal to target 1's conclusion.
- G4: `STStep2DecayPTgL` (`Step2Gen.lean:542-550`) and `STGdecayWgL` (:503-511) have the same `ξ ζ` text; `PrecL = StochDomAt` (`Carrier.lean:51`), `PrecPTL = PerTimeDomAt` (`Step2Gen.lean:78`); `perTimeOfStochDomAt` (`Defs/StochDomAt:195`; `SeqΩ : Type`, `FineModel.lean:160`) gives the private helper.
- Paper citation (finding, no target affected): `7_8_light_weight.tex:1994` lists `lem:newKLK, lem:LWterm, lem: EWGn2_N, lem: EMn2_N` as remaining valid at BA; `lem_decayLoop` is not named there and occurs in `7_8` nowhere (`grep decayLoop`: only `3_5:1126, 1153`). The BA reading holds by the generic proof (T7a) with the BA inputs; candidate T2495a: citation only, not a statement difference.

### (ii) Concrete instance and numerics

```
$ cd scratchpad/T2495 && python3 -I num.py
N(0)= 2097152 =2^21: True
0 N^-1=4.768e-07 N^(-1+eps/2)=9.873e-07 <=1-t(=1/2): True <=lower bound 11/60 of 1-t0: True N^(eps/2)>=2: True
1 N^-1=1.819e-12 N^(-1+eps/2)=7.028e-12 <=1-t(=1/2): True <=lower bound 11/60 of 1-t0: True N^(eps/2)>=2: True
2 N^-1=1.231e-15 N^(-1+eps/2)=6.850e-15 <=1-t(=1/2): True <=lower bound 11/60 of 1-t0: True N^(eps/2)>=2: True
3 N^-1=6.939e-18 N^(-1+eps/2)=5.003e-17 <=1-t(=1/2): True <=lower bound 11/60 of 1-t0: True N^(eps/2)>=2: True
first n with N^(-0.95)<=11/60: 0
N>=2^20 first n: 0
n=0 u=1/10 ellT=1
n=0 u=1/2 ellT=1
n=1 u=1/10 ellT=1
n=1 u=1/2 ellT=1
n=5 u=1/10 ellT=1
n=5 u=1/2 ellT=1
n=0 h=diam_inf=2  l*W^0.05=1.1892  far(L^inf):True  maxDist(l1)=6 >= 3h: True
n=0 h=diam_inf=2  l*W^0.20=2.0000  far(L^inf):True  maxDist(l1)=6 >= 3h: True
n=1 h=diam_inf=4  l*W^0.05=1.4142  far(L^inf):True  maxDist(l1)=12 >= 3h: True
n=1 h=diam_inf=4  l*W^0.20=4.0000  far(L^inf):True  maxDist(l1)=12 >= 3h: True
n=5 h=diam_inf=12  l*W^0.05=1.8612  far(L^inf):True  maxDist(l1)=36 >= 3h: True
n=5 h=diam_inf=12  l*W^0.20=12.0000  far(L^inf):True  maxDist(l1)=36 >= 3h: True
```

Instance (every hypothesis at once): `d = 3`, `sz0`, `zSeq`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)`, `s ≡ 1/10`, `t ≡ 1/2`, `t ≤ t₀` (`half_lt_t0`), `s < t`. Target 1: `0<κ`, `BAFlow` (`flow_sz0`), `0 ≤ s`, `t ≤ T0`; input `STGdecayWgL` stays a hypothesis (registry). Target 2 (a): `N_0 = 2^21`, `N^{-1} = 4.8e-7 ≤ 1/2` (eventual from `n = 0`). Target 2 (b): adds `s ≤ t`; input `STStep2DecayPTgL` (from `STGdecayWgL` by G4). Target 3: any `C₀, u, P`. Target 4: constants `Cd, 𝔠d` from `baStep2_holds 3 hLW hLWE`; binders `STLKgL, STDecaygL, STConStInd, STStep1LoopgL, STStep1WeakgL` and `BALWterm 3, BALWtermExp 3` stay hypotheses. Target 5: `d = 3`. Far set (target 1 body): at `k = 3`, `τ' ∈ {1/20, 1/5}`, `a = (0,(h,h,h),0)` is in the indicator support at `n = 0, 1, 5` (rows above; exact: `diam_∞ = 2(n+1) = W^{1/5}`), so the far set is nonempty; `STKcalDecaygL` far set nonempty at `τ = 1/20` by `inst_baKcalDecay_far` (`KDecayBA.lean:875`).
External-hypothesis limit check: none (no cited-from-other-work input; `BALWterm`, `BALWtermExp` are stage-L pins whose nonvacuity is T2494's; band readings merged: `band_LWtermG`, `band_LWtermExpG`, `LWPinsBA.lean:57-58`).

### Line estimate against the pre-signed split (1,950)

Own count (statements from the check, proof lines read off the routes above): header, imports, docstrings 40; target 1: 6 stmt + 12 = 18; 2 (a): 4 + 21 = 25; 2 (b) + private PT helper (G4): 6 + 15 + 8 = 29; 3: 4 + 8 = 12; 4: 13 + 18 = 31; 5: 2 × 9 = 18; instances (target 6, ~9 examples) ~80. Total ~253 lines (ticket: 140 / 215 / 360). TLC-4 factor 2.6: ~660. Peers read: `DecayGenTw.lean` 80, `Step2EventsGenTw.lean` 171, `Step2CloseBA.lean` 259. Both ~660 and the ticket's 2.6x reference 560 are far below the central 1,950 and the stop line 2,000: **the split does not apply**; no reserve `DecayLoopBA2`; one file, one branch `t/T2495`.

### Registry (`Test/Axioms.lean`, 646 lines; scan = Prop-valued defs in binders of theorems, not concluded by any theorem)

Premise constants of the new public theorems and their lines: `STGdecayWgL :197` (target 1), `STStep2DecayPTgL :196` (2 (b)), `BALWterm :221`, `BALWtermExp :222` (4, 5), `STLKgL :135`, `STDecaygL :217`, `STConStInd :272`, `STStep1LoopgL :239`, `STStep1WeakgL :146` (4). `BAFlow` is concluded by `flow_sz0` (proved, not in registry). `STDecayLoopUgL/PTgL/AtgL`, `BASTLWB/BASTLWT` occur only as conclusions: no line needed (0 grep hits in registry; `baSTLWB_of` makes `BASTLWB` proved). `grep -n "T7-BA\|T7 /"` = 0 hits. Lines to edit (comment text only): 196, 197. Lines 221-222 untouched (T2494, state `proving` at 07:13:50 UTC, not merged).

### Verdicts

- Target 1 `baDecayLoopU_of`: PASS (elaboration of `DecayGenTw.lean:71-76` with `hK` closed by `baKcalDecay_holds`).
- Target 2 (a) `baFlow_sizeInv_le`: PASS (one `rpow` monotonicity step on a merged result; elementary, no new mathematics).
- Target 2 (b) `baDecayLoopPT_of`: PASS.
- Target 3 `baDecayLoopAt_holds`: PASS (applies at every `C₀, u, P`; `DecayGen_Spec`, `Admissible` stay inside the merged body).
- Target 4 `baStep2Decay_holds`: PASS (conditional on `BALWterm`, `BALWtermExp`, exact type).
- Target 5 `baSTLWB_of`, `baSTLWT_of`: PASS (conditional on `BALWterm d`, `BALWtermExp d`).
- Target 6 instances: PASS (numerics above; every deterministic premise dischargeable; unproved inputs are registered).
- Every target is a composition of merged public results (dispatcher answer (2) holds); no BLOCKED. Split: not applicable.

**Overall verdict: PASS.**

## (b) Script output (stage 1b, prover claude-sonnet-5-5; split decision: the pre-signed split is not applied, all targets 1-6 delivered in one file)

```
$ git log --oneline -3 (branch t/T2495)
add74cd9 T2495: rewrap DecayLoopBA module docstring
a168aecf T2495: BA/DecayLoopBA (T7-BA: loop decay readings at BA, Step 2 decay closure, L-bridges)
b3ead83b T2492: merge BA-T T5-BA BA/GridDriftBA, GridGoodBA
$ wc -l RBM3D/BA/DecayLoopBA.lean   (stop line 2000, predicted central 215, 1a own count ~253)
     228 RBM3D/BA/DecayLoopBA.lean
$ lake build RBM3D.BA.DecayLoopBA | tail -2
Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (4104 jobs).
$ lake build (whole library, with import RBM3D.BA.DecayLoopBA in RBM3D.lean) | tail -2; grep -c DecayLoopBA full.log
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4359 jobs).
DecayLoopBA lines in full build log: 0
$ #print axioms (7 public declarations)
'RBM.BA.baDecayLoopU_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFlow_sizeInv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baDecayLoopPT_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baDecayLoopAt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep2Decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTLWB_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSTLWT_of' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" $F
(0 hits)
```

Statement diff against the pins: scratch copy of the check file (docs/tickets/checks/T2495-check.lean plus import of the new module and
`example (d : ℕ) : T2495_X d := @name d` for the seven public results) compiled:
```
238:example (d : ℕ) : T2495_DecayLoopU d := @baDecayLoopU_of d
239:example (d : ℕ) : T2495_SizeInv d := @baFlow_sizeInv_le d
240:example (d : ℕ) : T2495_DecayLoopPT d := @baDecayLoopPT_of d
241:example (d : ℕ) : T2495_DecayLoopAt d := @baDecayLoopAt_holds d
242:example (d : ℕ) : T2495_Step2Decay d := @baStep2Decay_holds d
243:example (d : ℕ) : T2495_STLWB d := @baSTLWB_of d
244:example (d : ℕ) : T2495_STLWT d := @baSTLWT_of d
lake env lean pincheck.lean: exit 0
```

Target statements, extracted from the file (first lines of each theorem):
```
60:theorem baDecayLoopU_of (d : ℕ) :
61-    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
72:theorem baFlow_sizeInv_le (d : ℕ) :
73-    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
91:theorem baDecayLoopPT_of (d : ℕ) :
92-    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z →
104:theorem baDecayLoopAt_holds (d : ℕ) :
105-    3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
114:theorem baStep2Decay_holds (d : ℕ) :
115-    BALWterm d → BALWtermExp d → 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
135:theorem baSTLWB_of (d : ℕ) : 3 ≤ d → BALWterm d → BASTLWB d := fun hd h =>
136-  stLWBgL_of_LWtermG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz hd
140:theorem baSTLWT_of (d : ℕ) : 3 ≤ d → BALWtermExp d → BASTLWT d := fun hd h =>
141-  stLWTgL_of_LWtermExpG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz hd
```

Compiled nonempty instances (target 6), names of the `example`s in section 4 of the file (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/10 < t ≡ 1/2 < t₀`):
```
$ grep -nE "^example|^  baDecayLoop|^  baFlow_sizeInv|^  baSTLW|baStep2Decay_holds 3|KDecayBAInst" RBM3D/BA/DecayLoopBA.lean
157:example (Cd : ℝ) (hG : STGdecayWgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) :
159:  baDecayLoopU_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 _ _ Cd (fun _ => by norm_num)
163:example : ∀ᶠ n in atTop, (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (1 / 2 : ℝ) :=
164:  baFlow_sizeInv_le 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) (by norm_num) flow_sz0 (fun _ => 1 / 2)
168:example (Cd : ℝ) (hG : STGdecayWgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) :
170:  baDecayLoopPT_of 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) (by norm_num) flow_sz0 _ _ Cd
176:example (hdec : ∀ D : ℝ, 0 < D →
187:  baDecayLoopAt_holds 3 le_rfl sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 0 (fun _ => 1 / 2) (fun _ => 1)
193:example (hLW : BALWterm 3) (hLWE : BALWtermExp 3) : ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
200:  obtain ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h⟩ := baStep2Decay_holds 3 hLW hLWE le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
207:example (h : BALWterm 3) : BASTLWB 3 := baSTLWB_of 3 le_rfl h
209:example (h : BALWtermExp 3) : BASTLWT 3 := baSTLWT_of 3 le_rfl h
213:example (Cd : ℝ) (hG : STGdecayWgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) :
222:example := KDecayBAInst.inst_baKcalDecay_far
```

Greps on the new file (acceptance criteria):
```
$ grep -n withLam F | grep -v "seqP (sz.withLam 0)\|seqP (sz0.withLam 0)"   (the one hit is the module docstring, where the wrap split `seqP` from `(sz.withLam 0)`)
17:(sz.withLam 0), BAFlow, baFMz, BAflowT0)`.
$ grep -nE STGridRepNgL|baStep1_holds|\|E\||2 - κ|mE|zt E|STFlow|lemT|‖m‖ = 1
(0 hits)
$ grep -nE "^(noncomputable )?(def|abbrev|structure|class) "
(0 hits)
$ grep -nE "≤ A \*|\(κ \+ 1\) / κ"
(0 hits; no R1 text)
$ git grep -n "DecayLoopBA" -- RBM3D RBM3D.lean | grep import
RBM3D.lean:588:import RBM3D.BA.DecayLoopBA
$ name clash: git grep -w -l NAME REF -- 'RBM3D/*.lean' 'RBM3D.lean' | wc -l   (files containing NAME at REF)
main baDecayLoopU_of:        0
main baFlow_sizeInv_le:        0
main baDecayLoopPT_of:        0
main baDecayLoopAt_holds:        0
main baStep2Decay_holds:        0
main baSTLWB_of:        0
main baSTLWT_of:        0
main DecayLoopBA_PT_of_U:        0
t/T2489b (7 public names):        0
t/T2491 (7 public names):        0
t/T2492 (7 public names):        0
t/T2493 (7 public names):        0
t/T2494 (7 public names):        0
$ git diff --stat b3ead83b..t/T2495
 RBM3D.lean                |   1 +
 RBM3D/BA/DecayLoopBA.lean | 228 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |   4 +-
 3 files changed, 231 insertions(+), 2 deletions(-)
$ git diff b3ead83b..t/T2495 -- RBM3D.lean RBM3D/Test/Axioms.lean | cut -c1-110 | grep "^[+-]"
--- a/RBM3D.lean
+++ b/RBM3D.lean
+import RBM3D.BA.DecayLoopBA
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.BA.STStep2DecayPTgL, -- `(Eq:Gdecay_w)` per time over a flow carrier (`Chain/Step2Gen.lean:542`): hyp
-   `RBM.BA.STGdecayWgL, -- `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]` over a flow carrier (`Chain/Step2Gen.lean
+   `RBM.BA.STStep2DecayPTgL, -- `(Eq:Gdecay_w)` per time over a flow carrier (`Chain/Step2Gen.lean:542`): hyp
+   `RBM.BA.STGdecayWgL, -- `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]` over a flow carrier (`Chain/Step2Gen.lean
$ git diff --stat b3ead83b..t/T2495 -- RBM3D/Chain RBM3D/Induction RBM3D/Path | wc -l
       0
$ "T7-BA" owner texts in merged docstrings
RBM3D/BA/LWPinsBA.lean:20:* The BA readings `BALWterm`, `BALWtermExp`, `BALWtermEXP` (owner: BA-L6) and `BASTLWB`, `BASTLWT` (owner: T1-BA / T7-BA) ar
RBM3D/BA/LWPinsBA.lean:50:/-- `STLWB` at the block Anderson data (owed: T1-BA / T7-BA, through L5). -/
RBM3D/BA/LWPinsBA.lean:52:/-- `STLWT` at the block Anderson data (owed: T1-BA / T7-BA, through L5). -/
RBM3D/BA/SEforLnBA.lean:270:consumer's input (T7-BA proves it at BA from `STGdecayWgL` and target 1). -/
RBM3D/BA/SEforLnBA.lean:307:that stay hypotheses are the Step 2 conclusions `STStep2ConclgL` (T1-BA's pin) and the consumer's `STDecayLoopUgL` (T7-BA)
RBM3D/Chain/DecayGen.lean:581:through `0 ≤ s`, `t < 1`.  The conclusion is `STDecayLoopUgL C μ s t`, conjunct 4 of `twSteps` (T7-BA's BA instance of t
```

### Narrative (stage 1b)

- Section (a) confirms that no split is needed (own count ~253 lines against the stop line 2000); the file has 228 lines, so the stop rule is not triggered and the reserve `DecayLoopBA2` is not created. All targets 1-6 are delivered on `t/T2495`.
- Every target is a composition of merged public results (route table in (a) `(i) bis`); no statement needed a hypothesis beyond the pin (stop rules 2-6 not triggered). No section (a) correction is needed, so there is no `(a′)`.
- Target 1: `stDecayLoopUgL_of_step2` with the elaboration of `Chain/DecayGenTw.lean:71-76` and `hK := baKcalDecay_holds`. Target 2 (a): `baFlow_premises` plus `Real.rpow_le_rpow_of_exponent_le` and `Real.rpow_neg_one`. Target 2 (b): private `DecayLoopBA_PT_of_U` (G4: `perTimeOfStochDomAt`) is used only in the instance; the public theorem takes `STStep2DecayPTgL` as input, as pinned. Target 3: `stDecayLoopAtgL_of` with `κm = κ`. Target 4: `baStep2_holds` then target 1 on `.2.2` of the conclusion. Target 5: `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG` with `hd`, `h.1`, `Step2EventsGenTw_baRot3`.
- Inputs that remain hypotheses: `STGdecayWgL` (target 1), `STStep2DecayPTgL` (2 (b)), `BALWterm d`, `BALWtermExp d` (4, 5) and the `STStep2G` binders in the instance of 4. Everything else is discharged at `d = 3`, `sz0`, `zSeq`, `flow_sz0`.
- The instance of the `hU` of `baEtermDecaygL` applies `baEtermDecaygL` to target 1 at the data (the conclusion is only discarded: the example concludes `True`, so it checks that the premises fit, not the ℰ-term decay itself). The far set of target 1 is shown nonempty by `KDecayBAInst.inst_baKcalDecay_far` (U2-BA).
- Layering: `BA/DecayLoopBA` is imported only by `RBM3D.lean`. No merged file is edited; the `git diff --stat` above lists three files, the `Chain`/`Induction`/`Path` diff is empty.
- Registry: the two comment texts at `Test/Axioms.lean` lines 196-197 (`STStep2DecayPTgL`, `STGdecayWgL`) got the consumer text; lines 221-222 (T2494's) are untouched; no line added or removed. The text in the registry has "BA reader: `baDecayLoopPT_of` ..." and "BA reader: `baDecayLoopU_of`, `baStep2Decay_holds` (T2495)".
- "T7-BA" docstring map (not edited, listed above): `LWPinsBA.lean:20, 50, 52` -> target 5 (`baSTLWB_of`, `baSTLWT_of`); `SEforLnBA.lean:270` -> target 1 (`baDecayLoopU_of`, hU of `baEtermDecaygL`); `SEforLnBA.lean:307` -> targets 1 and 4; `DecayGen.lean:581` -> target 1.
- UBA-C1 table as used: no R1 text enters a statement (grep above: 0 hits of `≤ A *`, `(κ + 1) / κ`); the size level (`sz.lam`) and the kernel level (`g₀`) cross only inside the merged `baKcalDecay_holds`. G1: no `0 < g₀ n` appears in any statement or proof. G2: no private copy of a generic skeleton. G3: the `hU` example uses target 1 directly (`toFlowFM` is `rfl`). G4: private helper, two lines.
- Base: the worktree branch starts at `b3ead83b` (`git log` above); the check file and (a) were computed on main `0a68e61d`. The full `lake build` above is on the branch.

## (c) Verified Mathlib names

- `Real.rpow_le_rpow_of_exponent_le` (used, compiled); `Real.rpow_neg_one` (used, compiled); `Filter.Eventually.of_forall` (used, compiled).
- RBM names used (compiled): `perTimeOfStochDomAt`, `stDecayLoopUgL_of_step2`, `stDecayLoopPTgL_of_step2`, `stDecayLoopAtgL_of`, `baKcalDecay_holds`, `baStep2_holds`, `baFlow_premises`, `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG`, `DecayGenTw_baWardPair`, `Step2EventsGenTw_baRot3`, `EMn2BA_mF_data`, `EMn2BA_T0_lt_one`, `baEtermDecaygL`, `KDecayBAInst.inst_baKcalDecay_far`.

## (d) Open issues and paper-delta candidates

- Open inputs (registered, other gates): `STGdecayWgL` (registry line 197, owner T1: proved inside `baStep2_holds`), `STStep2DecayPTgL` (line 196), `BALWterm`, `BALWtermExp` (lines 221-222, T2494). T2494 had not merged when the 1b started; no unconditional reading was added (dispatcher answer (7), `no new public name`).
- T2495a (citation only, from (a)): `lem_decayLoop` is not named in `7_8_light_weight.tex:1994` (which names `lem:newKLK, lem:LWterm, lem: EWGn2_N, lem: EMn2_N`); the BA reading holds by the generic proof (T7a) with the BA inputs. Not a statement difference.
- G1 remark (T2495a if the auditor asks): the BA statements carry no per-index window `0 < g₀ n`; `STKcalDecaygL` is eventual in its own body.
- No other Lean/paper statement difference.
