Auditor model: claude-opus-5-5

# T2491c audit, round 2 (U3s2c: targets 11-15, `Chain/NQEndLinGen`, `Chain/NQEndFlowGen`)
Written Tue Oct 13 09:22:17 UTC 2026 (`date -u`). Branch `t/T2491c` 38e89b0f (repair commit on 5545bcf1), `main` bde392e4
(035c4b84 + H282, docs only). Detached worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2491c-audit2`; scratch in scratchpad `T2491c/`
(`pins.lean` = check file + `import RBM3D.Chain.NQEndFlowGen` + the lines of §2; `full.log`).

**Verdict: PASS** (all targets 11-15). The round-1 defect (band re-derivation of `stOeqNQPT''_holds` only at `d = 3`) is repaired.

## 1. Diff, build, axioms
```
$ git diff --stat main...t/T2491c
 RBM3D.lean                    |    2 +
 RBM3D/Chain/NQEndFlowGen.lean |  888 +++
 RBM3D/Chain/NQEndLinGen.lean  | 1022 +++
 RBM3D/Probe/T2491Pins.lean    |  397 +++
$ git diff t/T2491 HEAD -- RBM3D/Probe | wc -l                                         ->  0   (inherited probe, never merged)
$ git diff main...HEAD -- RBM3D.lean      ->  +import RBM3D.Chain.NQEndLinGen / +import RBM3D.Chain.NQEndFlowGen  (#assert_rbm_axioms stays last)
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Test | wc -l       ->  0
$ git diff main...HEAD -- RBM3D/Chain ":!RBM3D/Chain/NQEndLinGen.lean" ":!RBM3D/Chain/NQEndFlowGen.lean" | wc -l   ->  0
$ git diff --stat 5545bcf1 38e89b0f       ->  RBM3D/Chain/NQEndFlowGen.lean | 41 +++---  (only file of the repair)
$ lake build RBM3D.Chain.NQEndLinGen RBM3D.Chain.NQEndFlowGen     (09:18:59-09:19:21 UTC)
Build completed successfully (3889 jobs).   exit 0
$ lake build                                                      (09:19:26-09:20:36 UTC, full library incl. #assert_rbm_axioms)
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
non-vacuity certificates: 0 of 122 premises in the two ledgers; ...
Build completed successfully (4367 jobs).   exit 0          (grep "error:" full.log: none)
$ lake env lean pins.lean   ->  exit 0, error lines 0
'RBM.BA.stOeqNQPTgL''_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.nqGridEndLinNg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.nqEndFlowGen_kLip_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stOeqNQPT''_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.nqGridEndLinN_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridDriftNg_envelope_ev' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridDriftNgAt_of_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridDriftNg_envelope_of_merged' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gridDriftNg_iff_at' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Greps (both files):
```
grep -cE "sorry|admit|native_decide|^axiom|withLam"                     NQEndFlowGen:0  NQEndLinGen:0
grep -nE "^(private )?(structure|class|instance)"                       NQEndFlowGen.lean:358:private structure NQEndFlowGen_Facts ...
grep -n "^import RBM3D.BA"                                              (none)
grep -cE "def .*[Kk]er\b|def Ugen|STGridRepNgL|ST_gridMart_of_repN"     0, 0
grep -nE "HierarchyNg|\(h[A-Za-z]* : GridDriftNg "                      NQEndLinGen.lean:165 (gridDriftNg_envelope_of_merged: D5's band recovery)
git grep -l -E "import RBM3D.Chain.NQEnd(Lin|Flow)Gen"                  RBM3D.lean, RBM3D/Chain/NQEndFlowGen.lean
wc -l                                                                   1022 + 888 = 1910 (both < 2,000)
git grep -F "stOeqNQPTgL''_band" main / t/T2496 -- RBM3D | wc -l        0 / 0   (new public name of the repair)
```
`NQEndFlowGen_Facts` is private and built inside `stOeqNQPTgL''_of` from its own hypotheses (`NQEndFlowGen:759 have F : NQEndFlowGen_Facts ...`):
not a hidden hypothesis of a public statement.

## 2. Statements against the pins (`pins.lean`, exit 0)
```
example : @T2491_XiBootgL' = @STXiBootgL' := rfl                example : @T2491_NQConclgL'' = @STNQConclgL'' := rfl
example : @T2491_NQConclPTgL'' = @STNQConclPTgL'' := rfl        example : @T2491_OeqNQgL'' = @STOeqNQgL'' := rfl
example : @T2491_OeqNQPTgL'' = @STOeqNQPTgL'' := rfl            example : @T2491_OeqQtgL' = @STOeqQtgL' := rfl
example : @T2491_OeqQtNZgL' = @STOeqQtNZgL' := rfl              example : @T2491_IterRgL' = @STIterRgL' := rfl
example : @T2491_IterationsgL' = @STIterationsgL' := rfl        example : @T2491_IterationsIIgL' = @STIterationsIIgL' := rfl
example : @T2491_KLip = @NQEndFlowGen_KLip := rfl               example : @T2491_KLipFam = @NQEndFlowGen_KLipFam := rfl
example : @T2491_KerNAL = @NQGoodGen_KerNAL := rfl              example : @T2491_KerNALFam = @NQGoodGen_KerNALFam := rfl
example (d law Flow mkM T0) (h : STOeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0) :
    T2491_OeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := h            -- target 14 conclusion = binding pin
example : type_of% @RBM.Ind.stOeqNQPT''_holds := stOeqNQPT''_holds_of_gen          -- compiles (round-1 defect: now ∀ d)
example : type_of% @RBM.Ind.nqGridEndLinN := @nqGridEndLinN_of_gen                 -- compiles (band statement, all d)
example : ∀ d, T2491_KLipFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  fun d => nqEndFlowGen_kLip_band d                                                -- compiles
#check output:  stOeqNQPT''_holds_of_gen : ∀ (d : ℕ), STOeqNQPT'' d
                NQEndFlowGenCheck.stOeqNQPTgL''_band : ∀ (d : ℕ), 3 ≤ d → STOeqNQPTgL'' d (fun sz => sz.seqP) ... (bandStep2Mat ...) ...
```
The repaired proof (`NQEndFlowGen:833-836`): `by_cases hd : 3 ≤ d`; positive case `(bandFM_STOeqNQPT'' d).2 (stOeqNQPTgL''_band d hd)`,
negative case `fun h => absurd h hd` (`STIngRgL` starts with `3 ≤ d →`). `stOeqNQPTgL''_band d hd` is `stOeqNQPTgL''_of d` at the band family
with every row discharged by merged band lemmas at general `d` (`bandFM_STKcalDecay hd`, `stEtermDecay hd`, `nqGoodGen_kerNAL_band d`,
`stSEforLn_holds d`, `Step2EventsGen_bandFlow d`); `stOeqNQPTgL''_band3 := stOeqNQPTgL''_band 3 le_rfl`. Docstrings no longer claim `d = 3` band theorems.

Target-by-target:
- **11** (regime facts, exit-time assembly, collapsed window): private `NQEndLinGen_*` helpers, consumed by target 12 only; band originals
  are private too. Nothing public to pin. PASS (through 12).
- **12** `nqGridEndLinNg` (`NQEndLinGen:600`): per carrier `Cm`, `μ`; carrier hypotheses (`LoopForm`, `WalkForm`, `DecayGen_Spec`,
  `‖Cm.m n‖ ≤ 1`, `S = SB`, row sums, `GridRepTailGen_Ker`, link, `STKboundgL`, drift classes `hExp hKL hKT hU : ∀ᶠ n`), then the band's
  hypotheses in the band's order, R1 `hcmp`, `hA`; then `∀ k ≥ 2, ∀ Ck Cv`, D1 `∀ᶠ n, NQGoodGen_KerNAL … gK k Ck n`, levels, `v ∈ [s,t]`,
  `ε₀`, `D₁`, `∃ ε₁ τ' D' C_K` (after the carrier), grid `N^{C_K} ≤ K ≤ ⌈N^{C_K}⌉`, event on `GoodSetNg ∩ GoodLinNg` with `Cm.Hpath`,
  `Cm.Pp`, `STLKMg`; final bound `N^{ε₀}(Λ^{1/2}+Φ₁+Φ₂+Φ₃) B_v^k` (compared line by line with `Induction/NQEndLin` `nqGridEndLinN`).
  No `GridDriftNg`/`HierarchyNg` premise (DECISIONS §294 (3) (9)). Band statement recovered for all `d` (above). PASS.
- **13** ten R2* texts: `rfl` against the binding pins; band bridges `bandFM_*` compile. PASS.
- **14** `stOeqNQPTgL''_of` (`NQEndFlowGen:673`): conclusion = binding pin; premises = family table rows 1-12 (`hSE hFlow hSpec hL hW
  hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU hKerFam hR1 hT0`), guards as in the table; flow-needing premises guarded,
  drift classes `∀ᶠ n`. `hR1` omits the window conjunct of `T2491_R1Fam`, `hT0` carries an extra `0 < ε →` guard: both weaker premises.
  Pinned `∃`: `𝔠d` inside `hSE`, `Ck` inside `NQGoodGen_KerNALFam`, `Aof` a datum before the family; none after `(sz, z)`. Band
  re-derivation now at the band's generality `∀ d`. PASS.
- **15** D2 `NQEndFlowGen_KLip(Fam)`: `rfl` against `T2491_KLip(Fam)`; band discharge `nqEndFlowGen_kLip_band d` from `stKloop_lip`. PASS.

## 3. Compiled nonempty instances (in the files; compiled by the module build above)
- 12: `NQEndLinGenCheck.nqEndLinNg_instance` (`NQEndLinGen:917`), applied at `k = 2, 3, 4` (`:1008-1014`): carrier `bandStep2Mat sz0 Einst`
  (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`, `lam = 1/64`), `s ≡ 0`, `t ≡ 1/16`, `v ≡ 1/32`, `Λ = 3`, `Φ = (1, 12, 1)`, `ε₀ = 1/10`, `D₁ = 1`,
  `A = 1`, `Cv = Ck = nqGood1C 3 k 10 κ'`; every hypothesis discharged by band lemmas (`stKbound_holds`, `hierDriftGen_*_band`, ...);
  conclusion exhibited at an index with `s n < v n ∧ 0 < gridStep` (`window_nondegenerate`). D5 instances `:974-1006` at `K ≡ 4`.
- 14: `NQEndFlowGen:855` example: `stOeqNQPTgL''_band3` (all 22 premises discharged at the band family) evaluated at `(sz0, z0)`,
  `(κ, ε, 𝔡) = (1/10, 1/10, 1/10)`, window `[0, 1/16]`, `C_d = 1`; open hypotheses only `STKboundgL`, `STKwardgL`, `STLKgL s`,
  `STStep2ConclgL` (other gates' pins inside `STIngRgL`, allowed). `:864` applies `stOeqNQPT''_holds_of_gen 3` through the merged `inst_ing`.
- 15: `:869`, `:874` at `(szB, zB)`, `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`, `t ≡ 15/16`, `k = 2, 3`. 13: `:879` band bridge at `d = 3`.
No `N = 0`, empty index, collapsed window, `False` premise, or astronomically large witness.

## 4. Paper deltas
Report (d): T2491c1 (D3 / spectral data and carrier classes in the endpoint), c2 (D5, eventual per-index drift), c3 (constants `Ck`, `Cv`,
`Aof`, `Ck < Cv ∨ A = 1`), c4 (flow window `∃ τ > 0, RangeCond τ T0`, guard `0 < ε`). c5 withdrawn: both band re-derivations now have the
band statements' generality (verified in §2). These cover the Lean/paper differences of targets 12-15 seen in §2.

## Observations (no verdict effect)
- O1. The probe `RBM3D/Probe/T2491Pins.lean` is in `git diff main...t/T2491c` (inherited from `t/T2491`, unchanged); the hub merges only
  the two `Chain/` files and the two import lines (sole writable files; the probe is `t/T2491`-only and never merged).
- O2. Section (b) of the prove report quotes pre-repair line numbers/`STOeqNQPT'' 3`; its Repair section states this and gives the current text.
- O3. The target-12 instance exercises only the `A = 1`, `Cv = Ck` branch; `Ck < Cv` (`Cv = Ck + 1`) is exercised through `stOeqNQPTgL''_band3`.

## Verdict per target
11 PASS; 12 PASS; 13 PASS; 14 PASS; 15 PASS. No dispatcher sign-off needed.
