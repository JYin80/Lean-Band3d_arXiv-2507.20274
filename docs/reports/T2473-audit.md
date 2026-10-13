Auditor model: claude-opus-5-5
# T2473 audit, round 1: T4s2a as delivered (targets 1-5; Amend 1, Amend 2) (Tue Oct 13 01:35:37 UTC 2026)
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2473-audit1`, detached at `t/T2473` = de1b76b7. Scratch: session scratchpad `T2473/`
(`aud_stmt.lean`, `aud_ax.lean`, `root_check.lean`, `sigscan.py`). Scope: `Chain/GridGoodGen` (targets 1-4), `Chain/GridEnvelopeGen`
(target 5). T4s2b (target 7) and T4s2c (targets 8-10) are later rows (Amend 1 S1) and not audited. No source edited.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Chain.GridGoodGen RBM3D.Chain.GridEnvelopeGen
✔ [3835/3836] Built RBM3D.Chain.GridEnvelopeGen (8.4s)
✔ [3836/3836] Built RBM3D.Chain.GridGoodGen (13s)
Build completed successfully (3836 jobs).            exit=0   (0 warnings from the two files)
$ lake env lean aud_ax.lean        (#print axioms of the 44 public declarations of the two files)   exit=0
  44 depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D; lake env lean root_check.lean   (import RBM3D + the two modules; #assert_rbm_axioms)
Build completed successfully (4325 jobs).  build-exit=0
axiom audit: 14273 theorems, 4509 definitions, 0 axioms in `RBM` ...   root-exit=0
  RBM.BA.STSEforLnConclgL: 2 [no certificate]
  RBM.BA.STSEforLngL: 2 [no certificate]
  RBM.BA.STEKDecaygL: 3 [no certificate]
$ grep -nwE "sorry|admit|native_decide|axiom" (both files)                                  exit=1 (no hit)
$ grep -nE "InitMem|zero_mem_goodSet|STGridRepNgL|def .*[Kk]er\b|def Ugen" (both files)      exit=1 (no hit)
$ grep -n "^import" (both files)
GridGoodGen.lean: Chain.GridDuhamelGen, Chain.Step34Gen, Chain.DecayGen, Chain.StepDecompGen, Chain.Step2EventsGen, Induction.GridGoodN
GridEnvelopeGen.lean: Chain.HierDriftGen, Chain.DecayGen, Induction.GridEnvelopeN          (no BA/*, no Probe)
$ git grep -lE "import RBM3D\.(Chain\.GridGoodGen|Chain\.GridEnvelopeGen|Probe\.T2473Pins)" HEAD   exit=1 (no importer)
$ git diff --name-only main...HEAD
RBM3D/Chain/GridEnvelopeGen.lean  RBM3D/Chain/GridGoodGen.lean  RBM3D/Probe/T2473Pins.lean  RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,DecayGen,
    Step34Gen,StepDecompGen,Step2EventsGen,HierDriftGen}.lean RBM3D.lean | wc -l
       0
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean   → +4 owedProps lines (comment + STSEforLnConclgL, STSEforLngL, STEKDecaygL), +1 structuralProps line (STAny)
$ wc -l (both files)   1037 GridGoodGen.lean, 360 GridEnvelopeGen.lean   (stop line 2,000)
$ git grep -lw <each of the 44 public names> main(650a122d) -- RBM3D, minus the two files   → checked 44 names, 0 hits
```
`RBM3D/Probe/T2473Pins.lean` (never merged) compiles on the branch: `lake env lean RBM3D/Probe/T2473Pins.lean` exit=0, 0 errors.
The check file compiles on the branch: `lake env lean docs/tickets/checks/T2473-check.lean` exit=0, 0 errors.

## 2. Statements against the pins (script)
`aud_stmt.lean` = the check-file pins `T2473_GoodSetNg`, `T2473_GoodExitMeasNg`, `T2473_GridGoodNConclg`, `T2473_GridGoodNgL`
(check file lines 166-231, renamed `AudPin_*` by `sed`) + the 1a-audit probe texts of target 5 and target 4 (a) (probe lines 256-287,
293-305, renamed `AudProbe_*`), then:
```
(A) GoodSetNg Cm n u k Γ Λ Φ τ' D' H ↔ AudPin_GoodSetNg …        := Iff.rfl
    GoodExitMeasNg Cm s v K ↔ AudPin_GoodExitMeasNg Cm s v K      := Iff.rfl
    GridGoodNConclg Cm μ s t ↔ AudPin_GridGoodNConclg Cm μ s t    := Iff.rfl
    GridGoodNgL d law Flow mkM T0 ↔ AudPin_GridGoodNgL …          := Iff.rfl
(B) AudProbe_gridDriftNg_envelope_stmt Cm μ        := @fun k hk τK hτK _ _ _ hsize … => gridDriftNg_envelope Cm μ k hk τK hτK hsize …
    AudProbe_sum_gridStep_div_etaNg_le_stmt Cm     := @fun _ _ _ _ _ hspec … => sum_gridStep_div_etaNg_le Cm hspec …
    SumWeightedStepErrNg_Stmt ↔ AudProbe_SumWeightedStepErrNg_Stmt := Iff.rfl
(C) probe text of 4 (a) + `StepDecompGen_WalkForm Cm lam' Ψ` (Amend 2) := … => gridGoodNConclg_of Cm E μ Hf lam' Ψ … hL hW hLaw hC …
(D) GoodSetNg (baStep2Mat sz lam0 E) …; GridGoodNgL 3 (seqP (sz.withLam 0)) BAFlow (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 : Prop
$ lake env lean aud_stmt.lean        exit=0 (only unused-variable linter warnings)
```
Reading. Targets 2-4 pins: definitional equality with the check file. Target 5: equal to (or the theorem is exactly) the probe texts
passed at the 1a-audit; `SumWeightedStepErrNg_Stmt` carries `∀ n, (Cm.m n).im ≤ 1` next to `DecayGen_Spec` (Amend 1 S2, admitted).
Target 4 (a): premises = probe text + `hW` (Amend 2), minus the unused `3 ≤ d` (the theorem is stronger). Target 4 (a)/(b) read
`StepDecompGen_LoopForm`, `StepDecompGen_WalkForm`, `Step2EventsGen_Law`, `Step34Gen_LCompat` (Amend 1 S3, Amend 2); no `KCompat`.
Target 4 (b) (`gridGoodNgL_of`): conclusion `GridGoodNgL d law Flow mkM T0` (= pin by (A)); per-flow premises `0 < κ → Flow … →`
for `∃ κm, DecayGen_Spec`, LoopForm, WalkForm, `STKcalDecaygL`, the Eterm family; `hLaw`, `hC`, `hWard` are unconditional in `(sz, z)`;
BA sources exist unconditionally: `Step2EventsGenTw_baLaw (sz) (l E : ℕ → ℝ)`, `DecayGenTw_baWardPair (sz) (lam0 E : ℕ → ℝ)` (main).
Target 1: the four `_Hf` lemmas take the LM compat inline; `GridGoodGen_LM_eq_L` derives it from `LoopForm` + `Step34Gen_LCompat`.
Target 3: `goodExitMeasNg` under `LoopForm` (measurability of `GoodSetNg`) and `WalkForm` (adaptedness via `pathH_measurable_filt`).
Band bridges present: `bandStep2_STmaxLM/STmaxLKM/STXiLM/STXiLKM` (`rfl`), `bandStep2_GoodSetN`, `_GoodExitMeasN`, `_GridGoodNConcl`
(`Iff.rfl`), `_gridExitTauN`, `_goodExitTauN` (`rfl`), `_MeasurableGoodSetN`, `bandStep2_GridGoodN` (through `bandFM_STIngR`).

Hypothesis-rule scan of the public signatures (`sigscan.py`: text from the keyword to `:=`, ticket pattern and UBA-C1 pattern):
```
GridGoodGen.lean bandStep2_GridGoodN bridge hyp-rule: ['STFlow', 'STflowE', 'lemT'] UBA: []
GridEnvelopeGen.lean GridEnvelopeGen_mE_im_Ep generic hyp-rule: ['mE'] UBA: []
GridEnvelopeGen.lean GridEnvelopeGen_abs_Ep_le generic hyp-rule: ['2 - κ'] UBA: []
scan done
```
The first is the band bridge. The other two are stem-prefixed real-number lemmas (`(mE (2√(1-y²))).im = y`, `|2√(1-y²)| ≤ 2 - κ²`)
on no carrier: the E′ reduction of target 5, admitted by Amend 1 S2 ("The E′ reduction of the port stays"). No carrier statement
reads `|E|`, `zt`, `etaT`, `mE`, `pathH`, `seqHflow` or `withLam`; `withLam` occurs only in proofs reading `hW` (prove report (b)).

## 3. Hidden hypotheses, vacuity, cycles
- No `structure`/`class` is declared in the two files; every premise is a merged `def … : Prop` read in the signature. Upstream
  definitions on `main` (all `def`, no fields): `StepDecompGen_LoopForm` (StepDecompGen:60), `StepDecompGen_WalkForm` (:73),
  `Step2EventsGen_Law` (Step2EventsGen:90), `Step34Gen_LCompat` (Step34Gen:164), `DecayGen_Spec` (DecayGen:91), `GridDriftNg`,
  `stepErrNg` (HierDriftGen:630, :619), `exists_norm_KI_le_wing` (:1083, theorem).
- Joint satisfiability: band, all of LoopForm/WalkForm/Law/LCompat/Spec/Admissible are discharged together in the §4 instances.
  BA: WalkForm is `rfl` at `baStep2Mat` (probe `baStep2Mat_walkForm`, probe compiles exit=0); LoopForm up to `0 < Im m` (probe);
  Law and WardPair merged. BA discharges of LoopForm/WalkForm/LCompat are owed to T4-BA (ticket "Not here").
- No cycle: imports are merged modules only; the probe is imported by nothing; `hU` of 4 (b) is produced by the merged
  `stDecayLoopUgL_of_step2` from `STStep2ConclgL` inside the pin (route `GridGoodN:930-956`).
- Supervisor 2351 T4S2-C2/C3: no initial-membership statement in either file (grep above, no hit), so no `∀ n` form of target 9;
  `open private` lists name only band model-free helpers of `Induction/GridGoodN` and `Induction/GridEnvelopeN`;
  `grep -A3 "open private" (both files) | grep -c ConArg_self_of_im_pos` → `0`. No S2/LoopForm BA reading is written here.
- External premise limit check (`∀ n, Im m ≤ 1`, the one new inline premise; TEAM §8 lesson 14):
```
$ python3 -I -c '…'     (Im m(E) = √(4-E²)/2; E′ = 2√(1-(Im m)²))
band E=0.5: Im m=0.9682 <=1 True; E'=2sqrt(1-Im m^2)=0.5000; Im m(E')=0.9682
band E=0.0: Im m=1.0000 <=1 True; E'=2sqrt(1-Im m^2)=0.0000; Im m(E')=1.0000
```
  BA: `Im m ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`), owed to T4-BA (Amend 1 S2); prove report (a‴) gives Im m = 0.83249 at BA n = 0.

## 4. Compiled nonempty instances (namespaces `GridGoodGenCheck`, `GridEnvelopeGenCheck`; compiled by the module build above)
| target | instance (file:line) | data | open hypotheses |
|---|---|---|---|
| 1 `_Hf` lemmas, bridges | GridGoodGen:931, :940 | `bandStep2Mat sz0 (1/2)`, `seqHflow sz0`; hLM from `GridGoodGen_LM_eq_L hL1 (bandStep34_LCompat …)` | none |
| 2 `GoodSetNg` bridge | :946 | n=0 (L=4, W=32, N=2097152), u=1/32, k=2, Γ=4, Λ=3, Φ=1, τ'=1/2, D'=1 | none |
| 3 measurability, exit lemmas | :951, :955, :959, :963-977, :979 | same data, s≡0, v≡1/32, K≡4 (Δ=1/128) | none |
| 4 (a) `gridGoodNConclg_of` | :1002 | sz0, E≡1/2, κm=1/2, 𝔠=1/6, 𝔡=1/10, s≡0 (`sInst`), t≡1/16 (`tInst`); LoopForm, WalkForm (λ′=sz0.lam, Ψ=0), Law, LCompat, Spec, Admissible, B≤1, Eterm decays discharged | `STSEforLnConclgL`, `STDecayLoopUgL` (U2, T1 pins; registered) |
| 4 (b) `gridGoodNgL_of` | :1016 | band family (seqP, STFlow, bandStep2Mat·(STflowE·), lemT), d=3; concludes `GridGoodNgL …` and `GridGoodN 3` | none |
| 5 envelope | GridEnvelopeGen:307 | sz0, E≡0, k=3, τK=1/2, s≡1/10, t≡1/2, K≡4; `GridDriftNg` by T2474's `gridDriftNg` with band classes | `STKboundgL` (KL7, registered) |
| 5 `sum_gridStep_div_etaNg_le` | :331 | τ'=2/3, s≡0, K≡4, t_n = 1 − N_n^{-1/3} | none |
| 5 `sum_weighted_stepErrNg_le` | :340 | k=3, τ'=τK=1/2, C_K=21, D_t=1, s≡0, t≡1/2, K_n=N_n^{21} (forced by the pin's `N^{C_K} ≤ K`) | none |
No `N = 0`, empty index set, collapsed window or `False` premise; every deterministic hypothesis is discharged.

## 5. Paper deltas
Prove report (d) proposes T2473a (inline LM compat of target 1), T2473b (`Im m ≤ 1` of target 5), T2473c (Hermitian clause from
`WalkForm`), T2473d (`GoodExitMeasNg` through `goodExitTauNg`), T2473e (dropped `3 ≤ d` of 4 (a)). These cover every Lean/paper
statement difference found in §2. The LoopForm/Law reading of target 4 is the dispatcher's Lean design (DECISIONS §281, §283).

## 6. Observations (no RETURN)
- O1. The 4 (a) instance keeps `STSEforLnConclgL`/`STDecayLoopUgL` open, and the envelope instance keeps `STKboundgL` open. All
  three are registered pins of other gates. The 4 (b) instance discharges everything at the band.
- O2. The `structuralProps` line for `STAny` (`def STAny … : Prop := True`, Step34Pins:272) is correct as a class. The prover flags
  it for dispatcher confirmation. It does not change the verdict.
- O3. The hub must merge only `Chain/GridGoodGen`, `Chain/GridEnvelopeGen`, the `Test/Axioms.lean` lines and the two root imports.
  `Probe/T2473Pins.lean` stays on the branch. `main` (650a122d) has moved past the branch's merge base, so the hub reconciles
  `Test/Axioms.lean` as a union of lines.
- O4. `GridEnvelopeGen_mE_im_Ep` and `GridEnvelopeGen_abs_Ep_le` are public. They are stem-prefixed (§3 (E)) and state no carrier
  fact.

## Verdicts
| target | verdict |
|---|---|
| 1 matrix controls `STmaxLMg` … `STXiLKMg`, `_Hf`, bridges | PASS |
| 2 `GoodSetNg` (= `T2473_GoodSetNg`, Iff.rfl) | PASS |
| 3 exit times, `MeasurableGoodSetNg`, `GoodExitMeasNg` (= pin), `goodExitMeasNg` | PASS |
| 4 `GridGoodNConclg`, `GridGoodNgL` (= pins), `gridGoodNConclg_of`, `gridGoodNgL_of` (Amend 2) | PASS |
| 5 `gridDriftNg_envelope`, `sum_gridStep_div_etaNg_le`, `SumWeightedStepErrNg_Stmt`, `sum_weighted_stepErrNg_le` | PASS |
**Overall: PASS** (T4s2a). Dispatcher sign-off is not needed.
