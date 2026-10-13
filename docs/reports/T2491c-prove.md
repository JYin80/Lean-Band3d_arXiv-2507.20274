Prover model: claude-sonnet-5-5

## (a) Math preflight (stage 1a of T2491, not repeated)
Section (a) of this row is `docs/reports/T2491-prove.md` (a) lines 3-92, (a″) lines 94-177 and `docs/reports/T2491-1a-audit.md` (verdict PASS; rows U3s2a 1,634 / U3s2b 1,909 / U3s2c 1,817).
Row context: `docs/reports/T2491b-prove.md`. Row U3s2c = `Chain/NQEndLinGen` + `Chain/NQEndFlowGen`, targets 11-15 (D5 rides in `NQEndLinGen`, D2 in `NQEndFlowGen`).
No mistake found in (a) for these targets; no (a′).

## (b) Script output
Branch `t/T2491c` (stacked on `t/T2491b`); `main` c2542930 merged in at `b056d428` (Tue Oct 13 08:20:45 UTC; the `RBM3D.lean` import-line conflict resolved with main's lines). Commits: `58bc3101`, `3888217a` (NQEndLinGen),
`9932eae1`, `201a44ca` (NQEndFlowGen, root imports), `5545bcf1` (pruned `open private` names; HEAD). Scratch scripts: scratchpad `T2491c/rep/`.
```
$ date -u; lake build RBM3D.Chain.NQEndLinGen RBM3D.Chain.NQEndFlowGen | tail -1; date -u; wc -l RBM3D/Chain/NQEndLinGen.lean RBM3D/Chain/NQEndFlowGen.lean
Tue Oct 13 09:02:36 UTC 2026
Build completed successfully (3889 jobs).
Tue Oct 13 09:02:38 UTC 2026
    1022 RBM3D/Chain/NQEndLinGen.lean
     881 RBM3D/Chain/NQEndFlowGen.lean
    1903 total
$ lake build   (full library, both import lines in RBM3D.lean, HEAD 5545bcf1: the compiling run was 09:01:13-09:02:28 (Build completed successfully, 4367 jobs); below, the cached re-run with its exit code; the first full build, 08:52:56-08:54:08 at 201a44ca, was also exit 0)
Tue Oct 13 09:07:17 UTC 2026
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
non-vacuity certificates: 0 of 122 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4367 jobs).
exit code: 0
Tue Oct 13 09:07:20 UTC 2026
$ lake env lean axioms.lean   # collectAxioms over the 33 public theorem/def/abbrev of the two files (names.txt)
declarations checked: 33; exactly the three standard axioms: 33; a proper subset: 0 []; outside the three: []
$ git diff main...HEAD --stat | tail -5
 RBM3D.lean                    |    2 +
 RBM3D/Chain/NQEndFlowGen.lean |  881 +++++++++++++++++++++++++++++++++++
 RBM3D/Chain/NQEndLinGen.lean  | 1022 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2491Pins.lean    |  397 ++++++++++++++++
 4 files changed, 2302 insertions(+)
$ git diff main...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Chain ":!RBM3D/Chain/NQEndLinGen.lean" ":!RBM3D/Chain/NQEndFlowGen.lean" | wc -l
       0
$ grep -cE "sorry|admit|native_decide|^axiom|withLam"  (both files)   ->  0, 0        $ lake env lean docs/tickets/checks/T2491-check.lean   -> exit 0, error lines 0
```
Public statements by script (`stmts.py`: line, name, conclusion with whitespace collapsed, cut at 205 characters; the ten R2* texts and the two D2 texts are `: Prop` and are in the pin diff; full text in the files):
```
NQEndLinGen:
NQEndLinGen:58 GridDriftNgAt : Prop
NQEndLinGen:75 gridDriftNg_iff_at : GridDriftNg Cm s t K ↔ ((∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) → ∀ n, GridDriftNgAt Cm s t K n)
NQEndLinGen:81 gridDriftNgAt_of_classes : GridDriftNgAt Cm s t K n
NQEndLinGen:93 gridDriftNg_envelope_ev : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n), ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) * (∑ l ∈ Finset.Icc 3 k, STksimLK ...
NQEndLinGen:158 gridDriftNg_envelope_of_merged : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Cm.Pp, ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n), ‖predIncNg Cm s t K n j σ ω a - (gridStep s t K n : ℂ) * (∑ l ∈ Finset.Icc 3 k,  ...
NQEndLinGen:600 nqGridEndLinNg : ∀ k : ℕ, 2 ≤ k → ∀ Ck Cv : ℝ, 0 < Ck → Ck ≤ Cv → (Ck < Cv ∨ A = 1) → (∀ᶠ n : ℕ in atTop, NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n) → ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) →  . ...
NQEndLinGen:831 nqGridEndLinN_of_gen : ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ), 3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 → sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 → (∀ n, |E n| ≤ 2 - κ) → (∀  ...
NQEndFlowGen:
NQEndFlowGen:156 bandFM_STXiBoot' : STXiBoot' sz E s t ↔ STXiBootgL' (bandFM sz E) (Sizes.seqP sz) s t
NQEndFlowGen:157 bandFM_STNQConcl'' : STNQConcl'' sz E s t ↔ STNQConclgL'' (bandFM sz E) (Sizes.seqP sz) s t
NQEndFlowGen:158 bandFM_STNQConclPT'' : STNQConclPT'' sz E s t ↔ STNQConclPTgL'' (bandFM sz E) (Sizes.seqP sz) s t
NQEndFlowGen:164 bandFM_STOeqNQ'' : STOeqNQ'' d ↔ STOeqNQgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
NQEndFlowGen:169 bandFM_STOeqNQPT'' : STOeqNQPT'' d ↔ STOeqNQPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
NQEndFlowGen:174 bandFM_STOeqQt' : STOeqQt' d ↔ STOeqQtgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
NQEndFlowGen:179 bandFM_STOeqQtNZ' : STOeqQtNZ' d ↔ STOeqQtNZgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
NQEndFlowGen:184 bandFM_STIterR' : STIterR' d R Aof ↔ STIterRgL' d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun s ...
NQEndFlowGen:189 bandFM_STIterations' : STIterations' d ↔ STIterationsgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
NQEndFlowGen:193 bandFM_STIterationsII' : STIterationsII' d ↔ STIterationsIIgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT  ...
NQEndFlowGen:222 nqEndFlowGen_kLip_band : NQEndFlowGen_KLipFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
NQEndFlowGen:673 stOeqNQPTgL''_of : STOeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0   (conclusion line 726; data Hf E lam' gK Ψ Aof, then 22 hypotheses = rows 1-12)
NQEndFlowGen:794 stOeqNQPTgL''_band3 : STOeqNQPTgL'' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n))
NQEndFlowGen:829 stOeqNQPT''_holds_of_gen : STOeqNQPT'' 3
```
Pins (script `pindiff.py`: normalized text of the check defs against the file defs, cross references renamed; the probe's D5 text against `GridDriftNgAt`; `pins.lean` = the 12 check defs + the probe's `T2491_GridDriftNgAt`,
`T2491_EnvConcl`, `T2491_EnvelopeEv` copied verbatim by script, then `example : @T2491_X = @X := rfl` for the 12 pairs and the three lines below; compile: exit 0, error lines 0):
```
T2491_XiBootgL'        vs STXiBootgL'             : check  9 lines, mine  9 lines, normalized text equal: True
T2491_NQConclgL''      vs STNQConclgL''           : check 12 lines, mine 12 lines, normalized text equal: True
T2491_NQConclPTgL''    vs STNQConclPTgL''         : check 12 lines, mine 12 lines, normalized text equal: True
T2491_OeqNQgL''        vs STOeqNQgL''             : check  4 lines, mine  4 lines, normalized text equal: True
T2491_OeqNQPTgL''      vs STOeqNQPTgL''           : check  4 lines, mine  4 lines, normalized text equal: True
T2491_OeqQtgL'         vs STOeqQtgL'              : check  4 lines, mine  4 lines, normalized text equal: True
T2491_OeqQtNZgL'       vs STOeqQtNZgL'            : check  4 lines, mine  4 lines, normalized text equal: True
T2491_IterRgL'         vs STIterRgL'              : check 15 lines, mine 15 lines, normalized text equal: True
T2491_IterationsgL'    vs STIterationsgL'         : check  4 lines, mine  4 lines, normalized text equal: True
T2491_IterationsIIgL'  vs STIterationsIIgL'       : check  4 lines, mine  4 lines, normalized text equal: True
T2491_KLip             vs NQEndFlowGen_KLip       : check  4 lines, mine  4 lines, normalized text equal: True
T2491_KLipFam          vs NQEndFlowGen_KLipFam    : check  4 lines, mine  4 lines, normalized text equal: True
GridDriftNgAt vs probe T2491_GridDriftNgAt: bodies equal: True
example : @T2491_GridDriftNgAt = @GridDriftNgAt := rfl
example : T2491_EnvelopeEv := fun d sz Cm μ _ k hk τK hτK s t K => gridDriftNg_envelope_ev Cm μ k hk τK hτK (s := s) (t := t) (K := K)
example (h : STOeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0) : T2491_OeqNQPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := h
```
Compiled nonempty instances (same files; `index.py`; band carrier `bandStep2Mat sz0 Einst`, `d = 3`; data in the section docstrings):
```
NQEndLinGen §7 (from line 897): 917 nqEndLinNg_instance (target 12 at sz0, Einst, s≡0, t≡1/16, v≡1/32; k = 2, 3, 4 by the three `example`s 1008/1011/1014; Λ=3, Φ1=Φ3=1, Φ2=12, ε0=1/10, D1=1; window nondegenerate)
  974 gridDriftNgAt_of_classes  982 gridDriftNg_envelope_ev  993 gridDriftNg_envelope_of_merged  1003 gridDriftNg_iff_at   (D5 at the band carrier, k=3, K≡4)
  band re-derivation (a theorem with no open hypothesis): nqGridEndLinN_of_gen (line 831; target 12, all d ≥ 3)
NQEndFlowGen §5-§6 (from line 774): 794 stOeqNQPTgL''_band3 (theorem: the generic pin at the band family, d = 3, no open hypothesis; every row of the table discharged by band lemmas)  829 stOeqNQPT''_holds_of_gen
  848 target 14 at (sz0, z0), window [0, 1/16], C_d = 1 (only the four stochastic pins of STIngRgL stay hypotheses)  857 the same through the merged inst_ing
  862, 867 D2 at (szB, zB), t≡15/16, k = 2, 3   872 band bridge of target 13 at d = 3
```
Name-clash grep (`git grep -h -w -F -f short.txt <ref> -- RBM3D`, minus the two files and `Probe`; `short.txt` = the 33 public names + `NQEndLinGen_assembly`, `NQEndFlowGen_core`, `NQEndFlowGen_section`, `NQEndFlowGen_Facts`):
```
refs checked: 513 (main + local t/* except t/T2491c); total hits: 0
```
Greps and layering (`greps.sh`; hypothesis rules of the ticket):
```
$ grep -cE "def .*[Kk]er\b|def Ugen" (NQEndLinGen, NQEndFlowGen)
RBM3D/Chain/NQEndLinGen.lean:0
RBM3D/Chain/NQEndFlowGen.lean:0
$ grep -cE "STGridRepNgL|ST_gridMart_of_repN"
RBM3D/Chain/NQEndLinGen.lean:0
RBM3D/Chain/NQEndFlowGen.lean:0
$ grep -cE "(def|abbrev|structure) (GoodSetNg|GridGoodNConclg|qvFormNg|STXiLg|STXiLKg|STNQConclgL|STXiBootgL|STIterRgL|STIngRgL|StepDecompGen_LoopForm|GridRepTailGen_Ker|DecayGen_Spec|stepErrNg)\b"
RBM3D/Chain/NQEndLinGen.lean:0
RBM3D/Chain/NQEndFlowGen.lean:3
$ grep -n "^import RBM3D.BA" RBM3D/Chain/NQ*Gen*.lean
(no output above = none)
$ grep -n "^import" (both files)
RBM3D/Chain/NQEndLinGen.lean:6:import RBM3D.Chain.NQLinGen
RBM3D/Chain/NQEndLinGen.lean:7:import RBM3D.Chain.HierDriftGen
RBM3D/Chain/NQEndLinGen.lean:8:import RBM3D.Induction.NQEndLin
RBM3D/Chain/NQEndFlowGen.lean:6:import RBM3D.Chain.NQEndLinGen
RBM3D/Chain/NQEndFlowGen.lean:7:import RBM3D.Induction.NQEndFlowLift
$ importers of the two modules
RBM3D/Chain/NQEndFlowGen.lean
RBM3D.lean
$ grep -nE "∀ \(sz : Sizes d\)" (both files)
  NQEndLinGen: no hit.  NQEndFlowGen: lines 100-149 (the ten R2* texts: `STIngRgL`-shaped binders `Flow`, `mk`, `T0`), 216-218 (`NQEndFlowGen_KLipFam`, guarded, premise of no target),
  675-725 (the premises of `stOeqNQPTgL''_of`: rows 1-12 of the family table, listed below).
$ sorry/admit/native_decide/axiom/withLam
RBM3D/Chain/NQEndLinGen.lean:0
RBM3D/Chain/NQEndFlowGen.lean:0
```
X1-C4 note: with `\b` the pattern also hits the three primed target-13 defs `STXiBootgL'`, `STNQConclgL''`, `STIterRgL'` (3 hits); with `( |$)` after the name it prints 0, so no merged pin is restated.
X1-C1/C1 regex on the two files (`x1c1.py` and a line listing; 42 hits in NQEndLinGen, 48 in NQEndFlowGen). NQEndLinGen: docs/comments 9; `Lloop` as a substring of `KLloopOf` (the D5 text, the link) 13; the `open RBM.Ind (… nqGood1C …)` line 1; the private regime lemmas that apply the band lemmas at `E'` (`NQEndLinGen_Ep`, `_eeShiftErrNg_eq`, `_ev_hδ`: label W) 4;
the band re-derivation (statement and proof) 7; the instances 8. NQEndFlowGen: docs/comments 8; the band bridges 17; the D2 band discharge 3; `hlam0` (a local name) 1; `KLloopOf` (lines 370, 712: the link text) 2; the band-family discharge (`flow_abs_le`, `stOeqNQPTgL''_band3`) 7; the instances 10. No hit in a public generic statement.
`open private` (no `private` deleted): NQEndLinGen: `nqEnd_ev_rpow_le nqEnd_one_le_size nqEnd_ev_ha1 nqEnd_ev_ha2 nqEnd_ev_ha3 nqEnd_ev_he1 nqEnd_ev_he4 nqEnd_he2_bound nqEnd_he2_final nqEnd_ev_W_rpow_ge nqEnd_step_le nqEnd_K_mul_step nqEnd_ev_hη nqEnd_hΔη nqEnd_ev_hδ nqEnd_arith nqEnd_gridTime_nonneg nqEnd_gridTime_le nqEnd_rangeCond_mono nqEnd_ev_union nqEnd_stepErrN_nonneg`
(NQEndLin, 21; the band lemmas that read `etaT (E n)`/`mE (E n)` are used at `E'`), `gridEnv_gridTime_le gridEnv_gridTime_nonneg` (GridEnvelopeN); NQEndFlowGen: `GridGoodGen_one_le_STXiLg` (GridGoodGen), `nqFlow_level_le nqFlow_phi_nonneg nqFlow_phiC_ge nqFlow_phiC_one_le nqFlow_K nqFlow_K_ne_zero nqFlow_K_low nqFlow_K_up nqFlow_K_card nqFlow_four_pow_le nqFlow_union4 nqFlow_bootRHS_one_le nqFlow_conStInd_exp_mono` (NQEndFlow, 13),
`nqEnd_rangeCond_mono` (NQEndLin). Regenerated, not opened: `nqEnd_he2` (explicit constant), `nqEnd_assembly`, `nqEnd_collapse`, `nqEnd_pathH_collapse`, `nqEnd_yMomentsMax`, `nqFlow_hQ`, `nqFlow_prec_of_le_right`, `nqFlow_restrict_pair`, `nqFlow_step2_restrict`, `nqFlow_core`, `nqFlow_section`.
Registry (`Test/Axioms.lean`): no line changed or added (`grep -n "OeqNQ''" RBM3D/Test/Axioms.lean` finds only line 405, the note on `STOeqNQ'`, which does not name the lift). Premise scan (`scan2.lean`, `RBM.Audit.scanPremises`): `scan: 126; with this row's 33 public theorems withheld: 127; newly listed: [RBM.BA.GridDriftNgAt]`,
i.e. the premise `GridDriftNgAt` of `gridDriftNg_envelope_ev` is concluded here by `gridDriftNgAt_of_classes`; no name of this row is listed by the unwithheld scan. The full build's `#assert_rbm_axioms` passed (126 premises, in the log above).
Scope of the band public declarations (script, before the instance sections): NQEndLin 1 (`nqGridEndLinN`: target 12, re-derived `nqGridEndLinN_of_gen`); NQEndFlow 17 = 10 texts regenerated (target 13) + `nqFlowLam`, `nqFlowPhiC` reused by name + 4 §2 bridges band only (`stXiBoot'_of_stXiBoot`, `stOeqNQ''_of_stOeqNQ'`, `stOeqQt'_of_stOeqQt`, `stOeqQtNZ'_of_stOeqQtNZ`) + `stOeqNQPT''_holds` (target 14, re-derived at d = 3); NQEndFlowLift 3 (`stKloop_lip`: D2 band discharge; `nqFlowSharp` not needed; `stOeqNQ''_holds`, the lift: dropped, DECISIONS §294 (3) (2)); unmapped or missing: 0.
Tables as used. **D1** (`NQGoodGen_KerNAL`, row a): enters `nqGridEndLinNg` as `hKer : ∀ᶠ n, NQGoodGen_KerNAL Cm.toFlowFM gK k Ck n` (assembly: `subGaussStop_linNg`, `nonAlt_hkerNg`) and `stOeqNQPTgL''_of` as `hKerFam`, instantiated at `k = n_` inside the proof (the `∃ Ck` stays before `(sz, z)`); band `nqGoodGen_kerNAL_band_at` (instance) / `nqGoodGen_kerNAL_band` (family); BA `baEKSumDecayNAL_holds` (U3-BA).
**D2** (`NQEndFlowGen_KLip(Fam)`): premise of no target here; band `nqEndFlowGen_kLip_band` (`stKloop_lip`, `v3_premises_of_stFlow`), instances at `(szB, zB)`; BA twin U3-BA (`BAKsol_isKLoopS`, `baKbound_holds`). **D3** (inline `∀ n, ‖Cm.m n‖ ≤ 1`): `hm` of `nqGridEndLinNg` (gives `Im m ≤ 1`, `η ≤ 1 - u`) and of the family (guarded); band `norm_mE`; BA `BAm_norm_le_one` + `BAflow_real`.
**D5** (`GridDriftNgAt`, `gridDriftNg_envelope_ev`, `gridDriftNgAt_of_classes`): the endpoint takes `hExp hKL hKT hU : ∀ᶠ n` (`hExp` uniform in `(s, t, K)`) and the link `hKK`; band `hierDriftGen_*_band`; BA T2492's per-index classes.
Family-premise rows as used by `stOeqNQPTgL''_of` (guard `0 < κ → Flow … →` unless stated; band discharge in `stOeqNQPTgL''_band3`; BA sources as in the ticket table): 1 `hSE` (pin); 2 `hFlow`; 3 `hL`; 4 `hW`; 5 `hLaw`, `hC` (unguarded); 6 `hSpec` (`∃ κm`), `hm`; 7 `hSeq`, `hS` (unguarded); 8 `hRow`; 9 `hExp`, `hKL`, `hKT`, `hU` (guarded, `∀ᶠ n`), `hKK` (unguarded);
10 `hKerFam` (D1, `∃ Ck` after `(k, κ, ε, 𝔡)`), `hR1` (`1 ≤ Aof κ`, `gK² ≤ lam² ≤ Aof κ · gK²`); 11 `hT0` (guard `0 < κ → 0 < ε →`: the band needs `ε > 0` for `v3_premises_of_stFlow`; `∃ τ > 0, RangeCond τ (T0 sz z)`); 12 `hWard` (unguarded), `hKcal`, `hEK` (guarded). Pinned `∃`: `𝔠d` (inside `hSE`, before the family), `Ck`, `Aof κ`; the exponents `ε₁ τ' D' C_K` are chosen after `(sz, z)` inside `nqGridEndLinNg`. No premise takes `GridDriftNg` or `HierarchyNg`.
UBA-C1 as used: R1 (`hcmp`, `hA`, `hdW` with `√A`, `hAk`, `Ck ≤ Cv`, `Ck < Cv ∨ A = 1`) enters `nqGridEndLinNg` only through `NQEndLinGen_assembly` (`subGaussStop_linNg`, `nonAlt_hkerNg`); the family passes `Aof κ` (row 10) and takes `Cv = Ck + 1`; regimes `STCaseI`, `STConStInd` as in the table; `step34Gen_` and `withLam` do not occur (grep: 0).
Narrative.
1. Size: NQEndLinGen 1,022 and NQEndFlowGen 881 lines (1,903; the 1a-audit row estimate was 1,817, +86); `wc -l` at the section commits: 827 and 1,024 (NQEndLinGen), 737 and 882 (NQEndFlowGen), before the last prune; both under the 2,000 stop line, no reserve file. C6: the D2 text and band discharge are 39 lines of NQEndFlowGen (lines 199-237; `stKloop_lip` itself is the merged 250-line theorem, reused); with the BA twin (about 350, U3-BA) the figure is 389, below 6,150. No RBM1D/RBM2D port: the ported proofs are the band files `Induction/NQEndLin`, `NQEndFlow` of this project (cited in the docstrings), so no RBM1D/RBM2D file:line, commit or diff-stat is due.
2. Method: the band regime lemmas that read `etaT (E n)`, `mE (E n)` are applied at the energy `E'_n = 2 √(1 - (Im m_n)²)` (`GridEnvelopeGen_mE_im_Ep`), for which `etaT E' = Cm.eta` and `eeShiftErrN … E' = eeShiftErrNg`; (he2) is re-proved with the explicit constant; the assembly (`NQEndLinGen_assembly`), the collapsed window (the walk of a `WalkForm` carrier is a constant shift of the band walk, `StepDecompGen_Hpath_eq`), the `Y`-moment constant (`yMomentsUnifNg`) and `NQEndFlowGen_core/_section` are line-by-line ports with `Cm.Pp`, `Cm.Hpath`, `STLKMg`, `GoodSetNg ∩ GoodLinNg`, `GridAssemblyHypNg`; the transfers are the law `Step2EventsGen_Law`.
3. `nqGridEndLinNg` keeps the band order after the carrier (`k`, then `Ck Cv` and D1, then the levels, `v`, `ε₀`, `D₁`, then `∃ ε₁ τ' D' C_K`). The vocabulary constant `Cv ≥ Ck` carries the exponent `ε = min (ε₀'/(8 Cv)) (1/2)`; `Ck < Cv ∨ A = 1` makes `A^(k-1) ≤ W^((Cv-Ck) ε)` eventual. The family takes `Cv = Ck + 1`, so the conclusion `STOeqNQPTgL''` does not mention `Cv`.
4. The law of the model, `law sz`, is a probability measure by `NQEndFlowGen_isProb` (the law `Step2EventsGen_Law` at the full set), so no premise is added for it; `Cm.Pp` is one by `WalkForm`.
5. Band re-derivations: `nqGridEndLinN_of_gen` (all `d ≥ 3`, the statement of `nqGridEndLinN` copied, no open hypothesis: `Cv = Ck = nqGood1C d k 𝔡⁻¹ (min κ (4/5))`, `A = 1`); `stOeqNQPT''_holds_of_gen : ∀ d, STOeqNQPT'' d` (Repair: through `stOeqNQPTgL''_band d (hd : 3 ≤ d)`, with `bandFM_STKcalDecay hd`, `stEtermDecay hd`; `d < 3` is vacuous), the band statement for every `d`.
6. Stop rules: none fired (files under 2,000; no BA import; no band or merged file edited, G1 diff 0 lines; no private deleted; no new kernel, carrier field or `STGridRepNgL` premise; no `sz.withLam`; no comparison other than R1; the one new `Prop` premise, `GridDriftNgAt`, is concluded here: scan above). The pin bundle `NQEndFlowGen_Facts` is private. `main` is 035c4b84 at the end (only `docs/` changed since c2542930); the hub's merge brings the two files and the two import lines; `RBM3D/Probe/T2491Pins.lean` is on the branch and must not be merged.
7. Observations: the module docstrings carry long-line warnings in the build log (as the merged `Induction/NQGood2.lean`). The first full build ran on HEAD 201a44ca after the commit (not before); the final full build above ran on the final HEAD 5545bcf1.

## (c) Mathlib names (resolved by script from the identifiers of the two files, modules `Mathlib`/`Init`/`Std`/`Batteries`; lemmas only)
Classical.choose, Classical.choose_spec, ENNReal.ofReal_le_ofReal, Filter.Eventually.of_forall, Fin.castAdd, Fin.natAdd, Finset.le_sup', Finset.mem_univ, Finset.sum_le_sum, Finset.sup'_le, Finset.univ_nonempty, Fintype.card_subtype_le, MeasurableSet.iUnion, MeasurableSet.univ, Nat.cast_nonneg, Nat.cast_one, Nat.cast_sub, Real.mul_rpow, Real.one_le_rpow, Real.rpow_add', Real.rpow_le_rpow, Real.rpow_le_rpow_of_exponent_le, Real.rpow_natCast, Real.rpow_neg, Real.rpow_nonneg, Real.rpow_one, Real.rpow_pos_of_pos, Set.compl_iInter, Set.compl_univ, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_union, Set.mem_univ, Set.ofPred_true, abs_nonneg, div_le_div_of_nonneg_left, div_le_div_of_nonneg_right, div_le_iff₀, div_le_one, div_nonneg, Filter.eventually_ge_atTop, half_pos, inv_anti₀, le_antisymm, le_max_left, le_max_right, le_mul_of_one_le_right, lt_div_iff₀, lt_min, lt_of_le_of_ne, measurableSet_lt, measurable_const, MeasureTheory.measureReal_empty, MeasureTheory.measureReal_iUnion_fintype_le, MeasureTheory.measure_mono, MeasureTheory.measure_ne_top, min_le_left, min_le_right, min_self, mul_div_assoc, mul_le_mul, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, mul_le_of_le_one_right, mul_nonneg, mul_pos, mul_pow, mul_self_nonneg, MeasureTheory.ofReal_measureReal, one_mul, one_ne_zero, one_pos, one_pow, pow_le_pow_left₀, pow_nonneg, pow_pos, smul_eq_mul.
Names verified absent: none needed (no name was invented; every Mathlib name above resolved in the environment). Deprecated names met and replaced during the stage: `Set.setOf_true` (now `Set.ofPred_true`), `Set.mem_setOf_eq` (now `Set.mem_ofPred_eq`).

## (d) Open issues and paper-delta candidates
1. **T2491c1** (Lean/paper, D3 in the endpoint): `|E n| ≤ 2 - κ` and `κ' = min κ (4/5)` are replaced by `DecayGen_Spec Cm.toFlowFM κm` (the gap is `κm`) and the inline `‖Cm.m n‖ ≤ 1`; `STKbound` is the pin `STKboundgL`; the endpoint additionally needs `S n = SB d (L n) (lam' n)`, the row sums, `GridRepTailGen_Ker`, the link and the four drift classes. Same content as T2491b of row a.
2. **T2491c2** (D5, §294 (3) (9)): the drift enters per index and eventually (`GridDriftNgAt`, `gridDriftNg_envelope_ev`); the merged `gridDriftNg_envelope` is `gridDriftNg_envelope_of_merged`.
3. **T2491c3** (constants): kernel constant `Ck` (D1) and vocabulary constant `Cv ≥ Ck` with `Ck < Cv ∨ A = 1` and `d √A W^{τ'} ≤ W^ε`; band `A = 1`, `Cv = Ck`; the family takes `Cv = Ck + 1`. Continues T2491a/b.
4. **T2491c4** (row 11): the flow window is `∃ τ > 0, RangeCond τ (T0 sz z)` with guard `0 < κ → 0 < ε`; the band flow gives `τ = ε/2` (`v3_premises_of_stFlow`). `RangeCond` passes to the windows `[s, t]`, `[s, v]` by `nqEnd_rangeCond_mono`.
5. **T2491c5**: withdrawn (Repair): both band re-derivations, `stOeqNQPT''_holds_of_gen` and `nqGridEndLinN_of_gen`, now have the band statements' generality; no Lean/paper difference.
6. For the hub: the merge brings `Chain/NQEndLinGen.lean`, `Chain/NQEndFlowGen.lean` and their two import lines in `RBM3D.lean` (after the last `import`); `Test/Axioms.lean` unchanged. Downstream: U3s3 reads `stOeqNQPTgL''_of`, `hQ_nonAltNg`, `nqLinGoodgL_of`, `budgetNonAltLinNg`; U3s4 reads `nqGridEndLinNg`, `NQEndFlowGen_KLipFam`, the R2* texts.

## Repair (audit round 1, `docs/reports/T2491c-audit.md` §4; written Tue Oct 13 09:18 UTC 2026, `date -u`)
Prover model of the repair: claude-opus-5-5. Commit `38e89b0f` on `t/T2491c` (parent 5545bcf1); only `RBM3D/Chain/NQEndFlowGen.lean` changed. Lines of (b) that cite NQEndFlowGen line numbers 794/829 and `STOeqNQPT'' 3` describe 5545bcf1; the current text is below.
```
$ git diff --stat 5545bcf1 HEAD
 RBM3D/Chain/NQEndFlowGen.lean | 41 ++++++++++++++++++++++++-----------------
 1 file changed, 24 insertions(+), 17 deletions(-)
$ lake build RBM3D.Chain.NQEndFlowGen        (Tue Oct 13 09:15:43 - 09:15:54 UTC 2026)
Build completed successfully (3889 jobs).
$ lake build                                  (full library, both import lines; Tue Oct 13 09:16:26 - 09:17:36 UTC 2026)
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
non-vacuity certificates: 0 of 122 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4367 jobs).
exit code: 0
$ wc -l RBM3D/Chain/NQEndFlowGen.lean
     888 RBM3D/Chain/NQEndFlowGen.lean
$ grep -nE "^(private )?theorem (flow_abs_le|stOeqNQPTgL''_band|stOeqNQPTgL''_band3|stOeqNQPT''_holds_of_gen)" RBM3D/Chain/NQEndFlowGen.lean
788:private theorem flow_abs_le {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
794:theorem stOeqNQPTgL''_band (d : ℕ) (hd : 3 ≤ d) : STOeqNQPTgL'' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
825:theorem stOeqNQPTgL''_band3 : STOeqNQPTgL'' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
833:theorem stOeqNQPT''_holds_of_gen (d : ℕ) : STOeqNQPT'' d := by
$ sed -n '/^theorem stOeqNQPT.._holds_of_gen/,/absurd/p' RBM3D/Chain/NQEndFlowGen.lean
theorem stOeqNQPT''_holds_of_gen (d : ℕ) : STOeqNQPT'' d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STOeqNQPT'' d).2 (NQEndFlowGenCheck.stOeqNQPTgL''_band d hd)
  · exact fun h => absurd h hd
$ cat holds.lean   (scratchpad T2491c/rep2/)
import RBM3D.Chain.NQEndFlowGen
open RBM.BA
#print axioms RBM.BA.stOeqNQPT''_holds_of_gen
#print axioms RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band
#print axioms RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band3
#check @RBM.BA.stOeqNQPT''_holds_of_gen
#check @RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band
example : type_of% @RBM.Ind.stOeqNQPT''_holds := stOeqNQPT''_holds_of_gen
$ lake env lean holds.lean; echo "exit: $?"
'RBM.BA.stOeqNQPT''_holds_of_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.NQEndFlowGenCheck.stOeqNQPTgL''_band3' depends on axioms: [propext, Classical.choice, Quot.sound]
stOeqNQPT''_holds_of_gen : ∀ (d : ℕ), RBM.Gauss.Sizes.STOeqNQPT'' d
NQEndFlowGenCheck.stOeqNQPTgL''_band : ∀ (d : ℕ),
  3 ≤ d →
    STOeqNQPTgL'' d (fun sz => sz.seqP) (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z)
      (fun sz z => (bandStep2Mat sz (RBM.Gauss.Sizes.STflowE z)).toFlowFM) fun x z n => RBM.lemT (z n)
exit: 0
$ name-clash grep of the new public name stOeqNQPTgL''_band (git grep -h -w -F over refs/heads except t/T2491c, -- RBM3D)
refs:      513 hits: 0
```
Changes: `flow_abs_le` is stated for `Sizes d`; `stOeqNQPTgL''_band d hd` is the former proof with `3 ↦ d`, `le_rfl ↦ hd` (`bandFM_STKcalDecay hd`, `stEtermDecay hd`,
`nqGoodGen_kerNAL_band d`, `stSEforLn_holds d`, `Step2EventsGen_bandFlow d`); `stOeqNQPTgL''_band3 := stOeqNQPTgL''_band 3 le_rfl` keeps the §6 instances at
`(sz0, z0)` unchanged; the second target-14 instance (line 865) applies `stOeqNQPT''_holds_of_gen 3`. The docstrings of §5 and of `stOeqNQPT''_holds_of_gen`
no longer claim that the band discharges are `d = 3` theorems. Narrative 5 and candidate T2491c5 corrected in place (T2491c5 withdrawn).
