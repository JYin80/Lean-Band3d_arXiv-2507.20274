Prover model: claude-sonnet-5-5

## (a) Math preflight: the stage-1a material of T2480
`docs/reports/T2480b-prove.md` did not exist when stage 1b started (`wc -l` on it failed in the tool log); the 1a for this row is `docs/reports/T2480-prove.md`
(a) (rows 7-9 of its verdict table PASS; (iii) hypothesis table, (iv) bridge table, (vii), (viii) were left to 1b) and (a′).  Not repeated here.

## (a′) Preflight corrections (stage 1b) — Tue Oct 13 02:26:15 UTC 2026
The pinned class `T2480_B45Facts` (check file `:302-309`) lacks two facts the proof of target 9 needs; both have a named band discharge, which the ticket
allows for a class (`T2480.md` target 7: "binding up to fields added or dropped ... with a named band discharge"):
1. `∀ n, ZeroModeGen_KerSums (mk sz z) n` (merged, U1s1; band `zeroModeGen_kerSums_band`).  Slot `i ≥ 1` of `𝒫(Θ𝒜)_{a₁}` is `Σ_{a∈F(a₁)} (Σ_c K_i(c,a_i)) 𝒜(a)`;
   it equals `κ_i (𝒫𝒜)_{a₁}` only if the column sum of `Step2Gen_thetaKer` is constant in the column.  The pinned text bounds `‖Σ_a thetaKer a b‖` for each `b` only.
   Constancy is `ZeroModeGen_thetaKer_colConst` (private, `open private`) from `KerSums`; the modulus bound of the pinned text then applies to the constant.
2. `∀ n, (m n).im ≤ 1` (band `norm_mE`; the same text as field 9 of `SEforLnGen_Facts`).  `ℬ₅` carries `(1-u)⁻¹`, the target has `η_u⁻¹`, `η_u = (1-u) Im m`:
   `(1-u)⁻¹ ≤ η_u⁻¹` needs `Im m ≤ 1`; `DecayGen_Spec` and `Step5CasesGen_FlowFacts` give only `κm ≤ Im m`.
No negative statement was compiled (a counterexample needs a `FlowFM` instance with `Im m > 1`).  Dispatcher: confirm the two added fields (see (d) 1).

## (b) Script output
### B1. Lines, builds (all commands run in `../RBM3D-wt/T2480b`)
$ date -u; wc -l RBM3D/Chain/B45Gen.lean   # (ev.sh run, before the builds below)
Tue Oct 13 02:19:56 UTC 2026
    1244 RBM3D/Chain/B45Gen.lean
$ lake build RBM3D.Chain.B45Gen | tail -1
Build completed successfully (3799 jobs).
$ lake build | tail -1   # whole library; RBM3D.lean imports the module and runs #assert_rbm_axioms
Build completed successfully (4333 jobs).
$ lake env lean docs/tickets/checks/T2480-check.lean; echo exit code $?
exit code 0
Stop size 2,000 per file, reserve rule 1,800: `B45Gen` 1,244; the reserve `B45Gen2` is not created.  Row total: 244 + 1,718 + 975 (T2480-prove.md B1) + 1,244 = 4,181.

### B2. `#print axioms` of the 16 new public declarations (ax_b45.lean: one line each)
$ lake env lean ax_b45.lean | sed 's/.*depends on axioms: //' | sort | uniq -c
  16 [propext, Classical.choice, Quot.sound]
$ grep -c 'depends on axioms' → 16; grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Chain/B45Gen.lean → 0
Names: B45Gen_Facts, b45Gen_facts_band, B45_ward_fing, B45_norm_kappag, B45_Psum_LK_leg, B45_norm_ThetaN_leg, B45_B4_leg, B45_scalesg, B45_detg, B45_det2g,
stWardTypePgL_of, stB45gL_of, stWardTypePPingL_of, stB45PingL_of, stWardTypePPin_gen_band, stB45Pin_gen_band.

### B3. Target statements, extracted by script from the file (whitespace collapsed)
B45Gen_Facts (B45Gen.lean):
def B45Gen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop := ∀ κ : ℝ, 0
  < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (mk sz z) ∧ DecayGen_WardPair (mk sz
  z) ∧ (∀ n : ℕ, ((mk sz z).m n).im ≤ 1) ∧ (∀ n : ℕ, ZeroModeGen_KerSums (mk sz z) n) ∧ ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → (∀ a : Zd d
  (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)) ∧ ∀ b : Zd d (sz.L n), ‖∑ a : Zd d (sz.L n),
  Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)
stWardTypePgL_of (B45Gen.lean):
theorem stWardTypePgL_of (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) {κm 𝔠 𝔡 C₆ Cd : ℝ} (hspec : DecayGen_Spec C κm) (him1 : ∀
  n, (C.m n).im ≤ 1) (hA : sz.Admissible 𝔠 𝔡) (hward : ZeroModeGen_WardCls sz C) (hpair : DecayGen_WardPair C) (hker : ∀ n, ZeroModeGen_KerSums C n)
  (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 -
  t)) (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n), ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1
  - t)) (hKcal : STKcalDecaygL C) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n)
  (hD : STGdecayWgL C μ s t Cd) : STWardTypePgL C μ s t
stB45gL_of (B45Gen.lean):
theorem stB45gL_of (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) {κm 𝔠 𝔡 C₆ Cd : ℝ} (hspec : DecayGen_Spec C κm) (him1 : ∀ n, (C.m
  n).im ≤ 1) (hA : sz.Admissible 𝔠 𝔡) (hward : ZeroModeGen_WardCls sz C) (hpair : DecayGen_WardPair C) (hker : ∀ n, ZeroModeGen_KerSums C n) (hrow : ∀
  (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t)) (hcol :
  ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n), ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t)) (hKcal
  : STKcalDecaygL C) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hD :
  STGdecayWgL C μ s t Cd) : STB45gL C μ s t
stWardTypePPingL_of (B45Gen.lean):
theorem stWardTypePPingL_of (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes
  d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hlaw : ∀ sz : Sizes
  d, IsProbabilityMeasure (law sz)) (hflow : Step5CasesGen_FlowFacts d Flow mk T0) (hfacts : B45Gen_Facts d Flow mk) (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠
  𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) : STWardTypePPingL d R law Flow mk T0
stB45PingL_of (B45Gen.lean):
theorem stB45PingL_of (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ
  ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hlaw : ∀ sz : Sizes d,
  IsProbabilityMeasure (law sz)) (hflow : Step5CasesGen_FlowFacts d Flow mk T0) (hfacts : B45Gen_Facts d Flow mk) (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 :
  ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) : STB45PingL d R law Flow mk T0

### B4. Statements against the `T2480_*` pins (check file, Part 2)
Scratch pins3.lean = check-file lines 298-329 verbatim + the `T2480_*PinOf` texts with `T2480_B45Facts` replaced by `B45Gen_Facts` (sed) + `example : T2480_WardTypePPinOf_x := fun d law Flow mk T0 => stWardTypePPingL_of d STCaseI law Flow mk T0`,
`example : T2480_B45PinOf_x := ... stB45PingL_of d STCaseI ...`, and `example : B45Gen_Facts d Flow mk → T2480_B45Facts d Flow mk`.
$ lake env lean pins3.lean | grep -c error
0
Class diff (conjuncts of `T2480_B45Facts` against `B45Gen_Facts`, whitespace-normalised, script classdiff.py):
only in T2480_B45Facts: []
only in B45Gen_Facts  : ['(∀ n : ℕ, ((mk sz z).m n).im ≤ 1)', '(∀ n : ℕ, ZeroModeGen_KerSums (mk sz z) n)']
conjunct counts: 5 7
The conclusions `STWardTypePPingL d R law Flow mk T0`, `STB45PingL d R law Flow mk T0` and every other hypothesis of the two pins are those of the check file; `R` is an argument (the proofs read no regime).

### B5. Compiled nonempty instances (`d = 3`, `sz0`, `z0`, `[0, 1/16]`, `m = 1`; the Step 2 output `STGdecayWgL` and the induction bound `Ξ̂ ≺ X` stay hypotheses)
B45Gen.lean:1095 The index set of the instances is nonempty at every size index: the wi
B45Gen.lean:1100 Target 7 (`B45Gen_Facts`) at the band flow `(sz0, z0)`: all five facts
B45Gen.lean:1111 Target 8 (a), `stWardTypePgL_of` at `(sz0, z0, [0, 1/16])`: the band `
B45Gen.lean:1122 Target 8 (a), `stB45gL_of` at `(sz0, z0, [0, 1/16])`: the band `STB45`
B45Gen.lean:1134 `stWardTypePgL_of` applied at `m = 1` (two indices) on `(sz0, z0, [0,
B45Gen.lean:1154 `stB45gL_of` applied at `m = 1` (two indices) on `(sz0, z0, [0, 1/16])
B45Gen.lean:1181 Target 9 (`stWardTypePPingL_of`) at the band family, `d = 3`, regime `
B45Gen.lean:1188 The same pin at the regime `STAny` (the proof reads no regime).
B45Gen.lean:1195 Target 9 (`stB45PingL_of`) at the band family, `d = 3`, regime `STCase
B45Gen.lean:1203 `stWardTypePPin_gen_band` applied at `(sz0, z0, 0, 1/16)`, `m = 1` (th
B45Gen.lean:1222 Target 8 (b): `B45_ward_fing` at the band carrier is the band `B45_war
B45Gen.lean:1231 `B45_scalesg` at the band carrier (second half of the previous example's docstring): the conclusion of the band `B45_scales`

### B6. Greps
$ grep -n '^import RBM3D.BA' RBM3D/Chain/B45Gen.lean
exit 1
$ importers of KDecayGen / B45Gen
RBM3D/Chain/SEforLnGen.lean:6:import RBM3D.Chain.KDecayGen
RBM3D/Chain/B45Gen.lean:6:import RBM3D.Chain.KDecayGen
RBM3D.lean:555:import RBM3D.Chain.KDecayGen
RBM3D.lean:562:import RBM3D.Chain.B45Gen
$ U-C4: grep -nE '^(noncomputable )?(private )?def' RBM3D/Chain/B45Gen.lean   # a Prop class and one ℝ-valued function; no kernel
61:def B45Gen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
637:private def B45Gen_farXi {sz : Sizes d} (C : FlowFM sz) (s t : ℕ → ℝ) (k : ℕ) (τf : ℝ) (n : ℕ)
$ TN-C4 grep -cE 'STGridRepNgL|ST_gridMart_of_repN' → 0;  UBA-C1 grep -c gK → 0;  C6 grep KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP in B45Gen.lean → 0
$ X1-C1 grep (ticket pattern) on B45Gen.lean, hits classified by region (script mkreport.py): band discharge 9, band instance 61, band re-derivation 6, doc 6; no hit in a generic statement or proof (the local name `hlam0` was renamed `hlpos`: substring hit)
$ name clash: grep -rnw of the 16 new names over RBM3D/ and RBM3D.lean outside B45Gen.lean, and git grep -w over the 490 branches t/*:
RBM3D/Test/Axioms.lean:195:   `RBM.BA.STKcalDecaygL, -- the 
t/T2480b:RBM3D/Test/Axioms.lean
(the only hits are my registry comment `Test/Axioms.lean:195`; no declaration of that name outside the new file).  Ports: none from RBM1D/RBM2D; the restated proofs are from `RBM3D/Induction/B45.lean` (cited per declaration).
open private: 43:open private B45_slot_zero B45_slot_succ B45_norm_colsum from RBM3D.Induction.B45 | 44:open private ZeroModeGen_thetaKer_colConst from RBM3D.Chain.ZeroModeGen

### B7. Diff, G1, registry
$ git diff --stat main...t/T2480b   # the sole writable files: B45Gen.lean, RBM3D.lean (import line), Test/Axioms.lean (registry lines)
 RBM3D.lean              |    1 +
 RBM3D/Chain/B45Gen.lean | 1244 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |    8 +-
 3 files changed, 1249 insertions(+), 4 deletions(-)
$ G1: git diff main...t/T2480b -- RBM3D/Induction RBM3D/Loop RBM3D/BA <merged Chain files, KDecayGen, SEforLnGen*> | wc -l → 0
$ git diff main...t/T2480b -- RBM3D.lean RBM3D/Test/Axioms.lean | grep '^[+-][^+-]' | cut -c1-100
+import RBM3D.Chain.B45Gen
-   `RBM.BA.STKcalDecaygL, -- the far decay of `𝒦` over a flow carrier, without the energy (`Chain/D
+   `RBM.BA.STKcalDecaygL, -- the far decay of `𝒦` over a flow carrier, without the energy (`Chain/D
-   `RBM.BA.STSEforLnConclgL, -- the four estimates of the `ℰ` terms (`lem:SEforLn`) over a carrier,
-   `RBM.BA.STSEforLngL, -- the family form of `lem:SEforLn` over `(law, Flow, mkM, T0)` (`Chain/Ste
-   `RBM.BA.STEKDecaygL, -- `EKFastDecay` of an `ℰ`-term label function with coupling `sz.lam`, with
+   `RBM.BA.STSEforLnConclgL, -- the four estimates of the `ℰ` terms (`lem:SEforLn`) over a carrier,
+   `RBM.BA.STSEforLngL, -- the family form of `lem:SEforLn` over `(law, Flow, mkM, T0)` (`Chain/Ste
+   `RBM.BA.STEKDecaygL, -- `EKFastDecay` of an `ℰ`-term label function with coupling `sz.lam`, with
Premise scan (`lake env lean RBM3D.lean`): no error; "premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14)"; no new registry line was needed.

### B8. Hypothesis and bridge tables as used (band fact → class field or premise → band discharge)
| band fact (B45.lean) | generic form | band discharge |
|---|---|---|
| `B45_ward_fin` :200 (`KLK_ward`, `B45_loopL_ward`) | `ZeroModeGen_WardCls` → `B45_ward_fing` | `zeroModeGen_wardCls_band` |
| Ward pair of `lem_decayLoop` (`B45_far`) | `DecayGen_WardPair`, `STKcalDecaygL`, `STGdecayWgL` → T7a `stDecayLoopUgL_of_step2` | `DecayGen_bandWardPair`, `bandFM_STKcalDecay` |
| `B45_row_thetaKer` :657 | row sums ≤ `C₆/(1-t)` (class) | `B45_row_thetaKer`, `Step2Kern_thetaKer_band`, `norm_mSigma` |
| `QopAlgebra_col_sum_thetaKer`, `B45_norm_colsum` | `ZeroModeGen_KerSums` (added) + column modulus ≤ `C₆/(1-t)` | `zeroModeGen_kerSums_band`, `QopAlgebra_col_sum_thetaKer`, `B45_norm_colsum` |
| `norm_mE` (`η ≤ 1-u`) | `Im m ≤ 1` (added) | `norm_mE`, `Complex.im_le_norm` |
| `B45_mE_im_ge`, `Γ = 2/√κ` | `κm ≤ Im m`, `η = (1-t) Im m` (`Step5CasesGen_FlowFacts`), `Γ = κm⁻¹` | `step5CasesGen_flowFacts_band` (`κm = √(2κ)/2`) |
| `hrange` (`v3_premises_of_stFlow`) | hypothesis `N⁻¹ ≤ 1 - t_n` (targets 8 (a)); in the pins from `STConStInd 𝔠d` (`𝔠d = 1/100`) | `B45Gen_invN_of_conStInd` |
| `QopAlgebra_commutator_ThetaN` | `QopAlgebra_commutator_ThetaNg` (U1s1) | reused |
Bridges: `bandFM_STWardTypeP` (`Iff.rfl`), `bandFM_STB45` (proved), `bandFM_STWardTypePPin`, `bandFM_STB45Pin` (U3s1), used in the examples B5 and in `stWardTypePPin_gen_band`, `stB45Pin_gen_band`.

### Narrative
- Delivered: U2b = targets 7-9 and their part of 10-11, in one new file `Chain/B45Gen.lean` (1,244 lines); `RBM3D.lean` (one import after the last import line) and three owner texts + one reader list in `Test/Axioms.lean`.
- Method: the deterministic cores of `B45` are restated over `C : FlowFM sz`: Ward at the last label from `ZeroModeGen_WardCls` (`B45_ward_fing`), the window split, the kernel norms with the constant `K₆ = max C₆ 1`,
  the scales with `Γ = κm⁻¹`, `B45_detg`/`B45_det2g`, the assembly at a law `μ` (`B45Gen_prec_assemble`), `B45Gen_key`, `B45Gen_pins`.  Model-free band lemmas are reused by name or `open private`.
- The far entries are `stDecayLoopUgL_of_step2` (T7a); nothing of `DecayLoopA` is copied.  `QopAlgebra_commutator_ThetaNg` gives `ℬ₄`.  The mollifier is read at `sz.lam` (size level); no kernel coupling, no `gK`.
- The pins do not read the regime, `STKbound`, `STKward`, `STLK` (the proof ignores them as the band proof does); `STConStInd` is used only for `N⁻¹ ≤ 1 - t_n`.  `hlaw` is unused.
- C6 (this half): the file contains no class-(t) segment of `KDecay`; the grep above is 0.  `Chain.KDecayGen` is imported by the ticket's layout; no declaration of it is read.
- Registry: the three owner texts that T2473 added (merged after U2a) are rewritten to "generic: <names> (T2480); BA: U2-BA"; the `STKcalDecaygL` reader list names the two pins; the scan needs no new line.
- Stop rules of the ticket: none triggered (1,244 < 1,800 lines; no `BA/*` import; no band or merged `Chain/*` file edited, G1 diff 0; no new kernel, `FlowFM` field, `STGridRepNgL` premise or T5s2/T1 name).
- Eterm-decay alignment with T2473 (item (viii)) is U2a's (T2480-prove.md B5); not in this half.

## (c) Verified Mathlib names (`#check`ed on the branch)
names2.lean, 10 of 10 resolve: `inv_mul_cancel₀`, `mul_lt_mul_of_pos_left`, `one_le_inv₀`, `div_le_div_of_nonneg_right`, `Real.one_le_rpow`, `inv_anti₀`, `Complex.im_le_norm`, `tendsto_natCast_atTop_iff`, `le_add_of_nonneg_left`, `Finset.sum_nonneg`.  Verified absent: none needed.

## (d) Open issues and paper-delta candidates
1. **Two fields added to the pinned class** (a′): `ZeroModeGen_KerSums` and `Im m ≤ 1`.  The pins `stWardTypePPingL_of`, `stB45PingL_of` therefore take `B45Gen_Facts`, not `T2480_B45Facts`; the class diff (B4) shows the two conjuncts and nothing else.
   `Iff.rfl` between the classes fails; the implication `B45Gen_Facts → T2480_B45Facts` compiles.  U2-BA must discharge both at BA (the ticket's BA list for target 3 names `BAm_norm_le_one` for `Im m ≤ 1`; `KerSums` at BA is not in the ticket's list).  Dispatcher decision needed.
2. Target 8 (a) takes the hypothesis `N⁻¹ ≤ 1 - t_n` eventually (the band gets it from `STFlow`); the pins derive it from `STConStInd` with `𝔠d = 1/100`.
3. REQ test of the ticket (this row + U2-BA twin 937 against 3,375): 4,181 + 937 = 5,118; the notice REQ `REQ-2026-10-13-0129-U2` exists on main and blocks nothing (CONTROL H265).
4. Paper-delta candidate `T2480c`: `(eq:Ward_typeP)` (`3_5:1264`) and `(y27kasdfg)` (`3_5:1692`) over the carrier, with the constant column sums of the `Θ`-kernel, `η_u ≍ 1-u` (`Im m ≤ 1`) and `N⁻¹ ≤ 1-t_n` as carrier inputs, the mollifier at `sz.lam`.
