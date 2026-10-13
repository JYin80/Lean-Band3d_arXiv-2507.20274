Prover model: claude-sonnet-5-5

# T2493b (U5d-2): `BA/Step5IIIWalk2.lean` -- targets 6-8, stage 1b, branch `t/T2493b`

## (a) Math preflight

Stage 1a of U5d is `docs/reports/T2493-prove.md` section (a) (verdict PASS; rows 1-17, verdicts for targets 6-8) with its (a′); not repeated here.

### (a′) Preflight corrections -- Tue Oct 13 09:33:37 UTC 2026

Stage 1b of T2493b (model claude-sonnet-5-5), base `2b96ec9a` = `t/T2493` b430f3c2 merged with main ac7eba4f; later `4f21ab26` = second merge of main c72bc745.  None changes a verdict.
1. θ and τ'.  (a) rows 7, 9, 10 take the ticket's `θ = ε₀/(8d(Cd+1))` and `τ' = τ/24`.  Not used: as in `T2493-prove.md` (a′)4, `Step5IIIWalk_hQ` needs `12τ' ≤ τ/4` and `2θ(Cd+1) ≤ τ/4` for the closure exponent `τ`; the walk takes `τ' = τ/48`, `θ = min(1/2, τ/(8(Cd+1)))` after `ε₀` and `τ`.  The band's `D*τ' ≤ 1/2` is not used in the compiled proof (`baStep5III_walkLevel` and `Step5IIIWalk_pertime` take `0 ≤ τ'` only).
2. Registry.  (a) predicted one `owedProps` line for `STDecayStronggL`: confirmed by the first full build (quoted in (b)); the line approved in CONTROL H278 (3) is added.  Its approved comment names `baStep5IIIWalk_at`; the declaration is `baStep5III_walk_at` (the ticket's name), so the comment names that.  `BAStep5IIIGood` needs no line (T2493-prove.md (a′)1).  `BAStep5IIIWalkConcl` needs none (the build passes).
3. Lift floor.  (a) Verdicts, target 7, says floor `W^{-D} ≥ N^{-D/𝔠}`; the lift uses the simpler `N^{-D} ≤ W^{-D}` (`W ≤ N`), `ε n = N^{-D}`.  The lift is 196 lines (`Step5IIIWalk2_PT` l.778-862, 85; `Step5IIIWalk2_lift` l.863-973, 111), not ~280: `NetLiftBA_decay_close` (first conjunct, `C_d = 0`) replaces the direct use of `NetLiftBA_L_diff`/`NetLiftBA_K_diff`.

## (b) Script output -- Tue Oct 13 09:33:37 UTC 2026

```
$ git log --reverse --grep='^T2493: U5d-2' --format='%h %cI(time) %s'   (commit times are -07:00 local = UTC-7; lines = `wc -l` of the new file at that commit)
3763a65f 02:04:09 T2493: U5d-2 Step5IIIWalk2, section 1-2: vocabulary (grid conclusion, walk pin, lift pin) and th lines=351
d38e7116 02:06:19 T2493: U5d-2 Step5IIIWalk2, section 3: the union bound at one size index lines=565
c0deeb0a 02:09:50 T2493: U5d-2 Step5IIIWalk2, section 4: the walk (constants, closure, union bound, baStep5III_wal lines=748
8e0a6d7d 02:13:40 T2493: U5d-2 Step5IIIWalk2, sections 5-6: the walk pin baStep5IIIWalk_holds and the lift baStep5 lines=981
74c562b2 02:15:12 T2493: U5d-2 Step5IIIWalk2, section 7: compiled nonempty instances of targets 6-7 at d = 3 lines=1052
38358ce7 02:18:35 T2493: U5d-2 Step5IIIWalk2: root import line, owedProps line for STDecayStronggL (CONTROL H278 ( lines=1053
f856d25f 02:23:11 T2493: U5d-2 Step5IIIWalk2: U5e consumer-shape example, docstring lines=1062
e14e341b 02:24:55 T2493: U5d-2 Step5IIIWalk2: set_option lines before the module docstring lines=1062
2ac4d0ad 02:27:13 T2493: U5d-2 Step5IIIWalk2: header docstring rewrapped, accurate section numbers lines=1067
$ git log --reverse --merges --format='%h %cI %s'   (the two merges of main)
2b96ec9a 2026-10-13T01:52:14-07:00 Merge main into t/T2493b (stacked on t/T2493, U5d-2)
4f21ab26 2026-10-13T02:30:55-07:00 Merge main into t/T2493b (second merge: T2491c, T2494b; RBM3D.lean and Test/Axioms.lean by union)
$ lake build RBM3D.BA.Step5IIIWalk RBM3D.BA.Step5IIIWalk2     (tail)
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4106 jobs).
EXIT 0
$ lake build     (full library, runs `#assert_rbm_axioms`; after the second merge of main)
info: RBM3D.lean:602:0: axiom audit: 14876 theorems, 4612 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
Build completed successfully (4370 jobs).
EXIT 0
$ the first full build (before the registry line was added), error lines
error: RBM3D.lean:598:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.BA.STDecayStronggL]
$ git diff --stat main...t/T2493b
 RBM3D.lean                  |    1 +
 RBM3D/BA/Step5IIIWalk2.lean | 1067 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    1 +
 3 files changed, 1069 insertions(+)
$ lake env lean docs/tickets/checks/T2493-check.lean   -> exit 0, 0 errors
```

**Axioms** (`#print axioms`, all 6 public declarations of the file: 3 defs, 3 theorems; the 8 helpers (1 structure, 5 theorems, 2 defs) are `private`):
```
'RBM.BA.BAStep5IIIWalkConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_walk_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep5IIIWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIWalk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep5IIIFromWalk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIFromWalk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Target statements** (extracted by script `extract.py`, whitespace normalized, folded at 175; `l.` = line in the file):
```
-- 63: def BAStep5IIIWalkConcl
   def BAStep5IIIWalkConcl {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop := ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ D : ℝ, 0 < D → ∃ Dst : ℝ, D + 2 * (d
   : ℝ) ≤ Dst ∧ ∀ tt : ∀ n, TimeIcc s t n, ∀ D' : ℝ, 0 < D' → ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧ ∀ᶠ n in atTop, (baStep2Mat sz lam0 E).Pp {ω | ∀ k, k ≤ K n → BAStep5IIIJsharp sz lam0
   E n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s (fun m => (tt m : ℝ)) K n k)) (gridTime s (fun m => (tt m : ℝ)) K n k) ((baStep2Mat sz lam0 E).Hpath s (fun m => (tt
   m : ℝ)) K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))
-- 73: def BAStep5IIIWalk
   def BAStep5IIIWalk : Prop := STIngR5gL 3 STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 (fun sz z s t =>
   BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t)
-- 79: def BAStep5IIIFromWalk
   def BAStep5IIIFromWalk : Prop := ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
   (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t → BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t → STPfConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t
-- 582: theorem baStep5III_walk_at
   theorem baStep5III_walk_at : ∀ (κ ε 𝔡 Cd : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → ∀ (𝔠 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀
   n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t → (STDecayStronggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s ∧ STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam
   0)) s t ∧ STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧ STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧ STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam
   0)) s t) → BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t
-- 763: theorem baStep5IIIWalk_holds
   theorem baStep5IIIWalk_holds : BAStep5IIIWalk
-- 977: theorem baStep5IIIFromWalk_holds
   theorem baStep5IIIFromWalk_holds : BAStep5IIIFromWalk
```

**Statement diff** (`stmtdiff2.py`: the `T2493_*` body of `docs/tickets/checks/T2493-check.lean` against the file, `T2493_ReadPremises` unfolded inline in `T2493_WalkAt`; then the probe `t/T2459:RBM3D/Probe/T2459Pins.lean` defs `:199, :213, :218` after the labelled renames `T2459_BAJsharp -> BAStep5IIIJsharp`, `T2459_law 3 -> seqP (sz.withLam 0)`, `T2459_Flow 3 -> BAFlow`):
```
T2493_BAWalkConcl vs BAStep5IIIWalkConcl                  : IDENTICAL (normalized whitespace) [618 / 618 chars]
T2493_BAWalk vs BAStep5IIIWalk                            : IDENTICAL (normalized whitespace) [224 / 224 chars]
T2493_BAFromWalk vs BAStep5IIIFromWalk                    : IDENTICAL (normalized whitespace) [343 / 343 chars]
T2493_WalkAt (ReadPremises inline) vs baStep5III_walk_at  : IDENTICAL (normalized whitespace) [565 / 565 chars]
ALL IDENTICAL

probe T2459_BAWalkConcl vs BAStep5IIIWalkConcl: IDENTICAL after the labelled substitutions
probe T2459_BAWalk vs BAStep5IIIWalk: IDENTICAL after the labelled substitutions
probe T2459_BAfromWalk vs BAStep5IIIFromWalk: 1 difference(s)
   insert: probe ``  ->  merged `→ 0 < ε → 0 < 𝔡`
$ auditor's examples (copy of the check + `example : T2493_X := name` for pins 1-7, `T2493_WalkAt := baStep5III_walk_at`, `T2493_BAWalk := baStep5IIIWalk_holds`, `T2493_BAFromWalk := baStep5IIIFromWalk_holds`, and `Iff.rfl` for the three defs; 13 examples)
lake env lean auditor_examples.lean  -> exit 0, 0 errors
```

**Compiled nonempty instances** (section 7, `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀`, `Cd = 1`; flow, horizon, regime `Step5IIIGood_reg_sz0` and `(con_st_ind)` `s1Setup_conStInd_const` discharged; the carrier predicates of Steps 1-4 stay hypotheses):
```
997:private def Step5IIIWalk2_instRead : Prop :=
1005:private def Step5IIIWalk2_instPrem : Prop :=
1018:example (hread : Step5IIIWalk2_instRead) :
1027:private theorem Step5IIIWalk2_inst_walk (hp : Step5IIIWalk2_instPrem) :
1036:example (hp : Step5IIIWalk2_instPrem) :
1042:example (hw : BAStep5IIIWalkConcl SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)
1050:example (hp : Step5IIIWalk2_instPrem) :
1058:example : STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
```
Text of two of the instances (`sed -n '1016,1023p;1041,1047p'`):
```
/-- **Target 6 (b) at the instance**: `baStep5III_walk_at` at `d = 3`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `Cd = 1`, `s ≡ 1/10 < t ≡ 1/2 ≤ t₀`; the flow, the
horizon and the regime are discharged, the five read premises stay a hypothesis. -/
example (hread : Step5IIIWalk2_instRead) :
    BAStep5IIIWalkConcl SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)
      (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) :=
  baStep5III_walk_at (1 / 2) (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num) one_pos (1 / 6) SizesInst.sz0
    FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun n => by norm_num)
    (fun n => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le) Step5IIIGood_reg_sz0 hread
/-- **Target 7 at the instance**: `baStep5IIIFromWalk_holds` at the same data, from the grid conclusion. -/
example (hw : BAStep5IIIWalkConcl SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)
      (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ))) :
    STPfConclgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) :=
  baStep5IIIFromWalk_holds (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq (by norm_num) (by norm_num) (by norm_num)
    FlowPinsInst.flow_sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun n => by norm_num) (fun n => by norm_num)
    (fun n => (FlowPinsInst.half_lt_t0 n).le) Step5IIIGood_reg_sz0 hw
```
l.1018 `baStep5III_walk_at` (hypothesis `Step5IIIWalk2_instRead` = the five read premises); l.1027-1040 `baStep5IIIWalk_holds` via the `STIngR5gL` route (hypothesis `Step5IIIWalk2_instPrem` = the nine carrier predicates); l.1042 `baStep5IIIFromWalk_holds` (hypothesis: the grid conclusion); l.1050 the chain walk then lift to `STPfConclgL`; l.1058 `STPfStep5gL 3 …` at BA from the two inputs (U5e's reading).  Targets 1-5 and the per-time layer have their instances in `BA/Step5IIIWalk.lean` section 11 (merged).

**Name clash** (`git grep -w -E 'BAStep5IIIWalkConcl|BAStep5IIIWalk|BAStep5IIIFromWalk|baStep5III_walk_at|baStep5IIIWalk_holds|baStep5IIIFromWalk_holds|Step5IIIWalk2_[A-Za-z_]+'`):
```
main@c72bc745 (RBM3D, RBM3D.lean; the same result on main@bde392e4 and ac7eba4f's descendants checked earlier): one hit, RBM3D/BA/Step5IIIWalk.lean:23 (the docstring of file 1 names `BAStep5IIIWalk`, `BAStep5IIIFromWalk` as the future second-half names; no declaration)
511 branches t/* (excluding t/T2493*): hits only t/T2491c, t/T2494b, t/T2496, each RBM3D/BA/Step5IIIWalk.lean (the same docstring line, from main)
```

**Greps on `RBM3D/BA/Step5IIIWalk2.lean`** (output of `greps.out`; each hit labelled):
```
$ C1 pattern on the new file
1009:    STDecaygL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) (fun _ => (1 / 10 : ℝ)) ∧
$ statement-level forbidden forms
$ withLam not inside seqP/pathP (sz.withLam 0)
864:`contGood (sz.withLam 0)`, as `NetLiftBA_decay`): `V n = {±}² × (Z_L^d)²`, `A = 4 D + 40`, `#V ≤ N³`, `ε = N^{-D}`; the loop and `𝒦^{(2)}` moduli are
942:    (cont_highProbAt_good (sz.withLam 0) hsizeN)
$ X1-C4 defs
$ hygiene
$ lam0_le_lam in file 2: 0
```
Hit labels: l.1009 = the carried premise `STDecaygL` of `STIngR5gL` in the instance bundle `Step5IIIWalk2_instPrem` (a hypothesis supplied to the pin, never read); l.942 = `cont_highProbAt_good (sz.withLam 0)`, whose statement is `HighProbAt (seqP (sz.withLam 0)) …` (same text as the merged `NetLiftBA_decay`); l.864 = docstring.

**Ports** (all sources are RBM3D band files, not edited; commits `git log -1 --format=%h -- file`; nothing from `../RBM1D`/`../RBM2D`, so no diff-stat):
- `open private` from `Induction/PfStep5.lean` (e2ec919c): `pfStep5_fl` :1984, `pfStep5_Rm` :2014, `pfStep5_hKD` :2065, `pfStep5_hlabel` :2086, `pfStep5_gridStep_le` :2121, `pfStep5_W2_le` :1313, `pfStep5_tailTD_nonneg` :522, `pfStep5_sizes` :375, `pfStep5_Wev` :2438, `pfStep5_Lab` :1778; from `BA/GridMartBA.lean` (ad52b370) `GridMartBA_Hpath_herm` :74; from `BA/NetLiftBA.lean` (a55ef846) `NetLiftBA_decay_close` :490; from `Path/NetLift2.lean` (efeda82d) `nl2_evR` :567.
- Copies adapted to BA: `pfStep5_path` :1525 -> `Step5IIIWalk2_path` :116; `pfStep5_fixedN` :1785 -> `Step5IIIWalk2_fixedN` :365; `pfStep5_walk` :2129 -> `baStep5III_walk_at` :582; `pfStep5_PT_of_walk` :2320 -> `Step5IIIWalk2_PT` :782; `pfStep5_lift` :2398 with the template `NetLiftBA_decay` :653 -> `Step5IIIWalk2_lift` :866.

**Narrative** (ticket report order):
(1) Lines: file 2 is 1067 lines against the stop line 2000 (`Step5IIIWalk3` not used); `wc -l` at the section commits 351 / 565 / 748 / 981 / 1052 (above).  File 1 is unchanged.  Sections: 1 vocabulary l.57, 2 path l.84, 3 union bound l.358, 4 walk l.572, 5 walk pin l.755, 6 lift l.772, 7 instances l.987.
(2) Numerics are those of T2493-prove.md (a) rows 1-16 and its (a′)4.  Compiled: closure `pfStep5Alg_closure` at `Step5IIIWalk_Ctot 3 Cc Cq` (`ε₀ < 𝔡/4`), `Step5IIIWalk_hQ` (`12τ' ≤ τ/4`, `2θ(Cd+1) ≤ τ/4`), `hfl` (`pfStep5_fl`, `D*-2d ≥ D₀`), `hRm` (`pfStep5_Rm`), `hKD`, `hlabel`.
(3) Route.  T6 `baStep5III_walk_at`: constants in the order `ε₀ → τ → D* → τ', θ → D₂` (`Step5IIIWalk_xx`) `→ C₀, Dg, CK` (clauses of `baGridRepNAt2_holds 3` at `D = Dg = max(D', 2D*)+4`) `→ K = ⌈N^{max(CK, 2(C₀+D*+14))}⌉+1`; `Cc` (`baStep5IIIKernel_at_flow`) and `Cq` come from `κ, 𝔡` only.  `Step5IIIWalk2_fixedN`: the complement of `∀ k ≤ K, J♯ < W^{ε₀}` lies in E1 (the matrix part fails at a grid time: `Step5IIIWalk_good_of_flow` -> `baStep5IIIGood_bundle` -> `Step5IIIWalk_good_transfer`, `(K+1)N^{-D₁}`, `D₁ = D'+cK+3`), E2 (initial term: `STDecayStronggL` at `s` through `Step2EventsGenTw_baLaw` at `k = 0`), E4 (clause 4, `ε' = τ/2`, `#labels N^{-Dg}`), E3 (clauses 1-2, null); `3N^{-(D'+1)} ≤ N^{-D'}`.  Off these, `Step5IIIWalk2_path` (strong induction on `k`, no stopping index): `Step5IIIWalk_pertime` (target 4 + `baStep5IIIEdet_holds`), `Step5IIIWalk_apriori`, `Step5IIIWalk_xx`, `Step5IIIWalk_mart_real`, `Step5IIIWalk_assemble`, then `hclos`.
    T6 (c) `baStep5IIIWalk_holds`: `𝔠d = 1/100`; the five read premises are `hDecS`, `hStep2.2.1`, `hStep2.2.2`, `hLmax`, `hLKU`.  T7 `baStep5IIIFromWalk_holds`: `Step5IIIWalk2_PT` (section `tt`, `ε₀ = min(ε₁, τ)/2`, descent `D_u ≥ D*-2d ≥ D`, `gridTime_last`, `Step2EventsGenTw_baLaw`, `Step2EventsGen_PT_of_sections`), `Step5IIIWalk2_lift` (`cont_core`, `A = 4D+40`, `#V ≤ N³`; ξ-modulus `NetLiftBA_decay_close` .1 at `C_d = 0`; `T_{u'} ≤ 2T_u` from `LemDecCalELip_relcont`), `StochDomAt.precomp_param` to the sizes with `lam² ≤ 1-t`.
(4) Statement diff: identical to the pins up to whitespace and the renames of the script; against the probe only the merged `J♯` name and correction (a) (`0 < ε → 0 < 𝔡`).
(5) Premises.  Read: `STDecayStronggL` at `s` (initial term), `STAvgUgL`, `STGdecayWgL` (conjuncts 2-3 of `STStep2ConclgL`), `STLmaxUgL`, `STLKUgL` (the inline Steps 3-4 premises); the last four go to `Step5IIIWalk_good_of_flow`.  Carried unread: `STKboundgL`, `STKwardgL`, `STLKgL`, `STDecaygL`, `STConStInd`, `STStep1LoopgL`, `STLocalEntryUgL` (conjunct 1 of `STStep2ConclgL`).  No copy and no `open private` of a file-1 lemma (every file-1 lemma used here is public); the `open private` list is above.
(6) UBA-C1.  File 2 adds no comparison text and no crossing: `grep -c lam0_le_lam` = 0.  The row-6 crossing (`lam0 ≤ lam` at `0 < g₀`) is inside the merged `baStep5IIIKernel_at_flow` and file 1's `Step5IIIWalk_xx`; the lift uses the window `0 < g₀` (`BAflow_lam0_window`) and `lam ≤ 𝔡⁻¹` (`WO`) only.  C1: no entry-level bound, no `|E|`, no `M = mI` (greps above); TN-C4 `STGridRepNgL` 0 hits; F1: every kernel, drift and window fact enters per index (`filter_upwards` outputs `hTTn`, `hxxn`, `hptn`, `happn`); no public statement carries a `∀ n` hypothesis.
(7) Paper-delta candidates: none new (see (d)).

## (c) Verified Mathlib names

Constants of Mathlib/core named in the file that resolve (script `names.lean`: each candidate token resolved in the file's `open` scope, origin module `Mathlib`/`Init`; definitions and tactic keywords that also resolve removed: `ENNReal.ofReal`, `Fintype.card`, `Finset.range`, `Real.exp`, `Real.log`, `Real.sqrt`, `Set.Icc`, `by_contra`, `norm_num`, `not_or`).  Names verified absent: none to report.
```
ENNReal.ofReal_add, ENNReal.ofReal_le_ofReal, ENNReal.ofReal_mul, ENNReal.ofReal_natCast, Filter.Eventually.of_forall, Finset.card_range, Finset.card_univ,
Finset.sum_const, Finset.sum_le_sum, Finset.sup'_lt_iff, Fintype.card_bool, Fintype.card_fin, Fintype.card_fun, Fintype.card_prod, MeasurableSet.iUnion,
MeasureTheory.ae_iff, MeasureTheory.measure_biUnion_finset_le, MeasureTheory.measure_iUnion_fintype_le, MeasureTheory.measure_mono, MeasureTheory.measure_union_le,
Nat.cast_le, Nat.cast_nonneg, Nat.le_ceil, Nat.lt_succ_of_le, Nat.strong_induction_on, Nat.succ_ne_zero, Real.log_nonpos, Real.one_le_rpow, Real.one_lt_rpow,
Real.rpow_add, Real.rpow_le_rpow, Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow_of_nonpos, Real.rpow_mul, Real.rpow_natCast, Real.rpow_neg_one, Real.rpow_nonneg,
Real.rpow_one, Real.rpow_pos_of_pos, Real.rpow_zero, Real.sqrt_eq_rpow, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_union, ZMod.card, abs_nonneg, abs_zero, add_le_add,
add_nonneg, add_zero, div_eq_mul_inv, div_le_one, div_nonneg, inv_le_iff_one_le_mul, le_max_left, le_max_right, le_mul_of_one_le_left, le_of_eq, le_rfl, le_trans, lt_min,
lt_of_le_of_lt, lt_of_lt_of_le, max_lt, measurableSet_le, measurableSet_lt, measurable_const, min_le_left, min_le_right, mul_le_mul, mul_le_mul_of_nonneg_left,
mul_le_mul_of_nonneg_right, mul_lt_mul_of_pos_right, mul_nonneg, nsmul_eq_mul, one_pos, pow_nonneg, zero_add, zero_le_one
```

## (d) Open issues and paper-delta candidates

1. Registry: `Test/Axioms.lean` gains one `owedProps` line, `RBM.BA.STDecayStronggL` (CONTROL H278 (3)), after the `STAvgUgL` entry; `RBM3D.lean` gains `import RBM3D.BA.Step5IIIWalk2` after the last import line.  Both were merged by union with main c72bc745 in `4f21ab26` and the full build passes there.
2. Interface for U5e: `baStep5IIIWalk_holds : BAStep5IIIWalk` and `baStep5IIIFromWalk_holds : BAStep5IIIFromWalk`, defined here only; `STPfStep5gL 3 …` at BA follows from them (example l.1058); U5e keeps the public `main_of_parts`.
3. The approved registry comment names `baStep5IIIWalk_at`; the file's theorem is `baStep5III_walk_at` (the ticket's name): the comment was written with the real name (the dispatcher may keep or restate it).
4. Paper-delta candidates: none new.  Equivalent restatements already covered by T2459a-f: the omitted BA proof (T2459a), near cut `2ℓ*` (T2459b), the J-free factor of the quadratic variation (T2459f), `D_u ≥ D*-2d` read at `d = 3`.  Correction (a) (`0 < ε`, `0 < 𝔡`) is a probe-versus-merged difference; the paper assumes both.
