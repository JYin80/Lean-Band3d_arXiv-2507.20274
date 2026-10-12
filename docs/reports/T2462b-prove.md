Prover model: claude-sonnet-5-5


# T2462b (U4s1b) prove report, stage 1b
Ticket `docs/tickets/T2462.md` with Amend 1 (`docs/tickets/T2462-amend-1.md`, DECISIONS §273 (1)-(2), item 6: split confirmed). This run: U4s1b = targets 8-11 in `RBM3D/Chain/Step5KerGen.lean` and `RBM3D/Chain/NewKLKLGen.lean`, branch `t/T2462b` from `main` c9f69dba, worktree `RBM3D-wt/T2462b`. U4s1a (`Chain/Step5CasesGen`, targets 1-7, merged c9f69dba) is not touched; no registry line (Amend 1 item 6). Commits: `72fbac2b` (18:57:27 UTC, Step5KerGen 403 lines), `cddf0367` (18:59:52 UTC, Step5KerGen 550), `763208b4` (19:02:26 UTC, NewKLKLGen 377); stop line 2,000 per file, `wc -l` taken at each (git log + `git show <commit>:<file> | wc -l`). First command of the run printed `Mon Oct 12 18:51:09 UTC 2026`.

## (a) Math preflight
`docs/reports/T2462b-prove.md` did not exist at the start of this run (the first `wc -l` of the run reported `open: No such file or directory`). The mathematics is `docs/reports/T2462-prove.md` section (a) lines 3-89 (exponent table, instance, D1-D4), (a″) lines 91-168 (probe, fill-in table), (a‴) lines 170-187 (Amend 1), and `docs/reports/T2462-1a-audit.md` (PASS, D1-D3, F2-F4 stand, split confirmed). Not repeated here; not edited.

## (a′) Preflight corrections (Mon Oct 12 19:24:19 UTC 2026, `date -u`)
No verdict changes. Supersessions already in (a‴): the comparison text E1 of (a) line 4 and the probe instance `probeSz1 := sz0.withLam …` are replaced by R1 and by Amend 1 item 5. Two differences between (a) and the delivered text, both inside the verdicts: (a) row 8 writes `Cp = max(C₆ A C_T, C₆)`, delivered `Cp = C₆ A C_T + C₆` (larger, as the probe); (a″) lines 114-115 count 97 copied helper lines, delivered helper section is lines 86-178 of `Step5KerGen.lean` (copies of `newKLKL_tailT_shift`, `newKLKL_zdistInf_add_le/_tri`, `newKLKL_SB_support`, `B45_row_thetaKer`). Paper check of target 8: `paper/tex/A_deterministic_estimates.tex:100` reads `(1 - sX)/(1 - tX) = 1 + Ξ`, `Ξ = (t-s) M^{(σ_i,σ_{i+1})} S^{(B)} Θ…` (`eq:decompUalt`), the form of `Step5KerGen_uKer_eq`.

## (b) Script output
All blocks are produced by `evidence.sh` in the scratchpad subdirectory `T2462b/` (one run, 19:15:09-19:21:39 UTC by its own `date -u` lines). Each `$` line is the command.


**E1 build, size, hygiene, imports, diff**
```
$ date -u -> Mon Oct 12 19:15:09 UTC 2026
$ lake build RBM3D.Chain.Step5KerGen RBM3D.Chain.NewKLKLGen > build.txt; tail -1 build.txt; grep -c "Chain/Step5KerGen.lean:\|Chain/NewKLKLGen.lean:" build.txt
exit=0
Build completed successfully (3802 jobs).
0
$ wc -l (stop line 2,000 per file; 1a central 427 / 651, high 555 / 800)
     550 RBM3D/Chain/Step5KerGen.lean
     377 RBM3D/Chain/NewKLKLGen.lean
     927 total
$ grep -cE "sorry|admit|native_decide|^axiom"
RBM3D/Chain/Step5KerGen.lean:0
RBM3D/Chain/NewKLKLGen.lean:0
$ grep -n "^import"
RBM3D/Chain/Step5KerGen.lean:6:import RBM3D.Chain.Step5Gen
RBM3D/Chain/Step5KerGen.lean:7:import RBM3D.Induction.Step5Kernel
RBM3D/Chain/NewKLKLGen.lean:6:import RBM3D.Chain.Step5Gen
RBM3D/Chain/NewKLKLGen.lean:7:import RBM3D.Chain.NewKLKGen
RBM3D/Chain/NewKLKLGen.lean:8:import RBM3D.Induction.NewKLKL
$ git log --oneline main..t/T2462b
763208b4 T2462b: Chain/NewKLKLGen target 10 (lem:newKLK at l = L over the carrier, band result, instances)
cddf0367 T2462b: Step5KerGen instances (band and non-band profile, UN decomposition, TailtoTail band)
72fbac2b T2462b: Chain/Step5KerGen targets 8, 9, 11 (decomposition, decay and profile under R1, band TailtoTail)
$ git diff --name-only main...t/T2462b
RBM3D/Chain/NewKLKLGen.lean
RBM3D/Chain/Step5KerGen.lean
$ git diff --stat main...t/T2462b -- <Induction, Carrier, Step2Gen, Step2Kern, GridDuhamelGen, NewKLKGen, Step5Gen, BA> | wc -l
       0
$ python3 -I cones.py
modules in graph: 525
RBM3D.Chain.Step5KerGen direct imports: ['RBM3D.Chain.Step5Gen', 'RBM3D.Induction.Step5Kernel']
  closure size 97 | direct BA/* imports: [] | transitive BA/*: []
  stop-rule modules in closure: []
  files importing it (reverse cone): []
RBM3D.Chain.NewKLKLGen direct imports: ['RBM3D.Chain.Step5Gen', 'RBM3D.Chain.NewKLKGen', 'RBM3D.Induction.NewKLKL']
  closure size 103 | direct BA/* imports: [] | transitive BA/*: ['RBM3D.BA.FlowPins', 'RBM3D.BA.MFixedPoint']
  stop-rule modules in closure: []
  files importing it (reverse cone): []
certificate cone (forward closure of 6 LWExpCert* modules): 168
  in certificate cone: RBM3D.Chain.Step5KerGen False
  in certificate cone: RBM3D.Chain.NewKLKLGen False
  in certificate cone: RBM3D.Chain.NewKLKGen False
  in certificate cone: RBM3D.Induction.Step5Kernel False
  in certificate cone: RBM3D.Induction.NewKLKL False
  in certificate cone: RBM3D.Induction.Step5Kit True
$ clash.sh (git grep -F -w of 22 new names over main + every branch t/*; git ls-tree for the module files)
refs scanned: 466 (main + branches t/*, except t/T2462b itself)
TOTAL hits over all refs: 0
```

**E2 axioms of the nine public declarations**
```
$ lake env lean axclosure.lean
'RBM.BA.Step5KerGen_uKer_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5KerGen_UN_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5KerGen_ThDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.step5KerGen_thDecay_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.step5KerGen_profile_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stTailtoTailgL'_holds_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKLAtgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKLgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKLgL'_holds_band' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

**E3 pins**
```
$ python3 -I pins.py (check-file blocks of 8 pins verbatim + typed examples); lake env lean pins_u4s1b.lean
exit=0; pins=8 typed examples=9
$ python3 -I defdiff.py (statement text after the binder colon vs the pin body after "Prop :=", whitespace-normalized, T2462_ThDecayK -> Step5KerGen_ThDecay)
T2462_uKerDecomp -> Step5KerGen_uKer_eq: statement identical=True (150 chars)
T2462_UNDecomp -> Step5KerGen_UN_decomp: statement identical=True (304 chars)
T2462_ThDecayK -> Step5KerGen_ThDecay: binders identical=True body identical=True
T2462_ThDecayK_band -> step5KerGen_thDecay_band: statement identical=True (148 chars)
T2462_ProfileK -> step5KerGen_profile_holds: statement identical=True (725 chars)
T2462_stNewKLKLgL'_of -> stNewKLKLgL'_of: statement identical=True (78 chars)
T2462_NewKLKL_band -> stNewKLKLgL'_holds_band: statement identical=True (46 chars)
T2462_TailtoTail_band -> stTailtoTailgL'_holds_band: statement identical=True (43 chars)
$ python3 -I extract.py (line: statement)
57: theorem Step5KerGen_uKer_eq (C : FlowFM sz) (n : ℕ) : Step2Gen_USemigroup C n → ∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → Step2Gen_uKer C n σ σ' s t = 1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n σ σ' t
71: theorem Step5KerGen_UN_decomp (C : FlowFM sz) (n : ℕ) : Step2Gen_USemigroup C n → ∀ {k : ℕ} (σ : Fin k → Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ (A : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)), Step2Gen_UN C n σ s t A a = ∑ b : Fin k → Zd d (sz.L n), (∏ i, (1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t) (a i) (b i)) * A b
188: def Step5KerGen_ThDecay {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (Λ C₆ : ℝ) : Prop
242: theorem step5KerGen_thDecay_band : ∀ (d : ℕ) (Λ : ℝ), 3 ≤ d → 0 < Λ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| ≤ 2) → Step5KerGen_ThDecay (bandFM sz E) sz.lam Λ C₆
308: theorem step5KerGen_profile_holds (d : ℕ) : 3 ≤ d → ∀ Λ C₆ A : ℝ, 0 < Λ → 0 < C₆ → 1 ≤ A → ∃ Cp : ℝ, 0 < Cp ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ → (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) → ∀ (n : ℕ) (σ σ' : Bool) (W D u t : ℝ), 0 < gK n → gK n ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 → (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) → ∀ a₁ a₂ : Zd d (sz.L n), (1 - u) * ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ * tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) W D ((zdistInf d (sz.L n) (b - a₂) : ℕ) : ℝ) ≤ Cp * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) + Cp * ((1 - u) / (1 - t) * W ^ (-D))
398: theorem stTailtoTailgL'_holds_band (d : ℕ) : STTailtoTailgL' d (fun sz E => bandFM sz E)
190: theorem stNewKLKLAtgL'_of (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) (hyp : NewKLKGenHyp d κ 𝔡 mk) : ∃ C : ℝ, 0 < C ∧ STNewKLKLAtgL' d κ 𝔡 C (κ / 2) mk
301: theorem stNewKLKLgL'_of (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : (3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → NewKLKGenHyp d κ 𝔡 mk) → STNewKLKLgL' d mk
313: theorem stNewKLKLgL'_holds_band (d : ℕ) : STNewKLKLgL' d (fun sz E => bandStep2Mat sz E)
```

**E4 instances**
```
$ grep -nE "^example" (first 100 chars)
RBM3D/Chain/Step5KerGen.lean:412:example : Step2Gen_uKer (bandFM sz0 (fun _ => (0 : ℝ))) 0 true false (1 / 4) (1 / 2) =
RBM3D/Chain/Step5KerGen.lean:418:example (A : (Fin 2 → Zd 3 (sz0.L 0)) → ℂ) (a : Fin 2 → Zd 3 (sz0.L 0)) :
RBM3D/Chain/Step5KerGen.lean:429:example {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| ≤ 2) (σ σ' : Bool) {s t : ℝ} (ht0 
RBM3D/Chain/Step5KerGen.lean:461:example : ∃ Cp : ℝ, 0 < Cp ∧ ∀ a₁ a₂ : Zd 3 (sz0.L 0),
RBM3D/Chain/Step5KerGen.lean:499:example : ∃ Cp : ℝ, 0 < Cp ∧ ∀ a₁ a₂ : Zd 3 (sz0.L 0),
RBM3D/Chain/Step5KerGen.lean:523:example : ∃ Cc : ℝ, 0 < Cc ∧ ∀ a : Fin 2 → Zd 3 (sz0.L 0),
RBM3D/Chain/NewKLKLGen.lean:329:example : STNewKLKLgL' 3 (fun sz E => bandStep2Mat sz E) :=
RBM3D/Chain/NewKLKLGen.lean:334:example (d : ℕ) : STNewKLKLgL' d (fun sz E => bandStep2Mat sz E) := stNewKLKLgL'_band d (stNewKLKL
RBM3D/Chain/NewKLKLGen.lean:337:example : ∃ C : ℝ, 0 < C ∧ STNewKLKLAtgL' 3 (1 / 10) (1 / 10) C (1 / 20) (fun sz E => bandStep2Mat
RBM3D/Chain/NewKLKLGen.lean:353:example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
$ lake env lean inst_*.lean (each example renamed to a theorem, #print axioms)
6 examples renamed
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
4 examples renamed
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
1 x   'RBM.BA.scratchInstN' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**E5 greps of target 12**
```
$ grep -nE "withLam|lam0|BAflowLam0|seqHflowBA" (Step5CasesGen, Step5KerGen, NewKLKLGen)
exit=1 (1 = no hit)
$ grep -nE "Cmp|A \* gK|sz.lam n \^ 2 ≤ A" (three files)
RBM3D/Chain/Step5KerGen.lean:305:`∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`.
RBM3D/Chain/Step5KerGen.lean:310:      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
$ python3 -I gk.py (declarations that read gK; R1 literal in the statement)
Step5KerGen.lean: def Step5KerGen_ThDecay: reads gK; R1 literal in statement: False
Step5KerGen.lean: theorem step5KerGen_profile_holds: reads gK; R1 literal in statement: True
$ grep -nE "<R1-like second forms>" i.e. per-index forms without gK:
263:private theorem Step5KerGen_cmp_pos {g l A : ℝ} (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hg : 0 < g) :
276:    (h2 : g₂ ^ 2 ≤ A * g₁ ^ 2) (hA : 1 ≤ A) (ht : t < 1) (hr : 0 ≤ r) :
$ label.py (b) X1-C1 pattern, hits by enclosing declaration
Step5CasesGen.lean: total hits 27
   theorem Step5CasesGen_prec_scale                     lines 138-139 (2)
   def Step5CasesGen_FlowFacts                          lines 147 (1)
   theorem Step5CasesGen_flow_dom                       lines 149-154 (2)
   theorem step5CasesGen_flowFacts_band                 lines 157-163 (4)
   def Step5CasesGen_WardIdent                          lines 197 (1)
   theorem step5CasesGen_wardIdent_band                 lines 201 (1)
   theorem ST_step5_caseIII_of_pfgL                     lines 509 (1)
   theorem Step5CasesGen_compare_IIward                 lines 519-523 (3)
   example@718                                          lines 718-720 (3)
   example@725                                          lines 729 (1)
   theorem Step5CasesGen_wardIIgL_band                  lines 731-736 (4)
   example@773                                          lines 774-780 (4)
Step5KerGen.lean: total hits 25
   theorem Step5KerGen_SB_support                       lines 153 (1)
   theorem Step5KerGen_row_thetaKer                     lines 170-176 (4)
   theorem Step5KerGen_theta_decay_band                 lines 206-235 (8)
   theorem step5KerGen_thDecay_band                     lines 249-250 (2)
   example@429                                          lines 431-446 (8)
   example@523                                          lines 535-536 (2)
NewKLKLGen.lean: total hits 3
   open private                                         lines 36 (1)
   example@353                                          lines 366-367 (2)
$ grep -nE "Ring.inverse|Matrix.of|cycProd"
exit=1 (1 = no hit)
$ grep -nE "(def|theorem|lemma|abbrev) [A-Za-z_']*Ugen"
exit=1 (1 = no hit)
$ label.py (c) RBM\.UN|\bUN d|uKer d|Theta d|thetaKer d|Ugen
Step5CasesGen.lean: total hits 0
Step5KerGen.lean: total hits 16
   theorem Step5KerGen_row_thetaKer                     lines 167-171 (4)
   theorem Step5KerGen_theta_decay_band                 lines 200-234 (7)
   example@429                                          lines 431-446 (5)
NewKLKLGen.lean: total hits 0
```

**E6 pre-check of the root audit (import RBM3D + both modules)**
```
$ lake env lean precheck.lean | grep "axiom audit\|premises found\|unregistered\|error"
axiom audit: 13498 theorems, 4283 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 63, structural 45, refuted 6, superseded 13).
exit=0
$ date -u -> Mon Oct 12 19:21:39 UTC 2026
```

**Hypothesis table** (premise of a public result here | band discharge | BA source or owning row).
- `Step2Gen_USemigroup C n` (target 8) | `step2Gen_USemigroup_band sz E n (hE : |E n| ≤ 2)`, used in the examples at `Step5KerGen.lean:412, 418, 429` | `BAuKer_self/_comp` through `Step2Kern_uKer_BA`: U4-BA.
- `Step5KerGen_ThDecay C gK Λ C₆` (target 9) | `step5KerGen_thDecay_band` (`gK = sz.lam`, `Step5KerGen.lean:242`), used at `:453-476` | decay at the BA coupling: U4-BA (a).
- R1 `∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (target 9) | band `gK = sz.lam`, `A = 1` (`mul_self_nonneg`, `le_rfl`, `one_mul`, `:461-476`); non-band `gK = sz0.lam/2`, `A = 4` (`:499-519`) | BA `gK = BAflowLam0 sz z`, `A = (κ+1)/κ`, `TwistStep2_lam0_sq` (Amend 1 item 1): U4-BA (a); not checked here.
- `NewKLKGenHyp d κ 𝔡 mk` (target 10) | `newKLKGenHyp_band` (merged `Chain/NewKLKGen`) | `baNewKLKGenHyp` (merged): U4-BA (b).
- Target 11 has no premise beyond the merged `stTailtoTail_holds`; the generic proof is U5's.

**Band re-derivations** (band original | where re-derived).
- 8: `step5Kernel_decompU` `Step5Kernel:57`, `_UN_decompU` `:74` | `Step5KerGen.lean:429` (any band data, from target 8 and `mul_Theta_of_three_le`); instances `:412, :418`.
- 9: `step5Kernel_theta_decay` `:135`, `_profile_explicit_holds` `:199` | `step5KerGen_thDecay_band` `:242`; profile at `gK = sz.lam` `:461`.
- 10: `stNewKLKL_holds` `NewKLKL:836` | `stNewKLKLgL'_holds_band` `NewKLKLGen.lean:313`; `:329` (through target 10) and `:334` (U6's route, `stNewKLKLgL'_band d (stNewKLKL_holds d)`).
- 11: `stTailtoTail_holds` `TailtoTail:582` | `stTailtoTailgL'_holds_band` `Step5KerGen.lean:398`; instance `:523`.

**`open private` and copies.** `Step5KerGen.lean:39`: `step5Ker_tailW_eq`, `step5Ker_zdistInf_sub_comm` from `Induction.Step5Kernel`. `NewKLKLGen.lean:35-36`: `newKLKL_Cs_ge_one`, `_tailT_le_tailW`, `_tailW_eq_of_near`, `_tailW_of_far`, `_zdistInf_le_L`, `_mE_zero`, `_STGMM_zero` from `Induction.NewKLKL`; `:37`: `NewKLKGen_conv_two`, `NewKLKGen_ward_LKM` from `Chain.NewKLKGen`. Copies under the stem: `Step5KerGen_tailT_shift` (`NewKLKL:56`), `_zdistInf_tri` (`NewKLKL:127-141`), `_SB_support` (`NewKLKL:145`), `_row_thetaKer` (`B45:656`), `NewKLKLGen_bound2` (`NewKLKL:606`, generic kernel). Last commits of the sources (`git log -1 --format=%h -- <file>`): Step5Kernel 19a2b090, NewKLKL 7388d136, B45 1ef8fa7e, NewKLKGen ef345e15, TailtoTail 37f3a22e. No text from RBM1D or RBM2D: the RBM1D/RBM2D diff-stat is not applicable. Registry: no `owedProps` line (ticket, Amend 1 item 6); `Test/Axioms.lean` and `RBM3D.lean` are not in `git diff --name-only`.

**Narrative.**
- Targets 8-11 are delivered with the statements of the amended check (E3: 8 pin defs compile verbatim from `docs/tickets/checks/T2462-check.lean`, 9 typed examples elaborate, the statement text equals the pin body for all 8). Target 9 reads R1 once: `Step5KerGen_cmp_pos` (`:263`, the per-index lemma of Amend 1 item 3, on variables `g l A`) and `Step5KerGen_tailT_cross` (`:275`) are used inside `step5KerGen_profile_holds` (`:308`); in declaration text (statement or proof, docstrings excluded) `gK` occurs only in `Step5KerGen_ThDecay` and `step5KerGen_profile_holds` (E5, `gk.py`).
- Profile constant `Cp = C₆ A C_T + C₆` (`C_T` of `ekPropTInf_holds`); the floor comes from the row sum `C₆/(1-t)` as the pin states it. Band decay `C₆ = max(C₁ C_s, 1)` with `C_s = 2^(d-2) e`.
- Target 10: `C = 2(4 + C_K) + C_s C_T`, `δ₀ = κ/2`; at the band `C_K = 1` (`newKLKGenHyp_band`), so `C = 10 + C_s C_T` as in `newKLKL_at`. F6 and F7 of `NewKLKGenHyp` are not read. The route differs from the ticket text (copies of `newKLKL_conv_two`, `_ward_LKM`): the generic `NewKLKGen_conv_two` and `NewKLKGen_ward_LKM` are reached by `open private`; `NewKLKGen_bound2` is not usable because it bounds the far pairs by `tailW` at the pair distance, while the sharp form needs the floor `W^(-D)` (`NewKLKL` docstring, route); only `NewKLKLGen_bound2` is copied.
- Instances (E4, `d = 3`, `sz0`: `L = 4`, `W = 32`, `lam = 1/64` at `n = 0` by `sz0_values`): target 8 (`s = 1/4`, `t = 1/2`, charges `(+,-)`; `k = 2` tensor form); target 9 band (`gK = sz0.lam`, `A = 1`, `u = 0`, `t = 1/2`, `W = 32`, `D = 2`, window `lam²/L² = 1/65536 ≤ 1/2`) and non-band (kernel built at `lam/2` through `Step5KerGen_szH`/`Step5KerGen_carrierH`, `gK = sz0.lam/2 ≠ sz0.lam`, `A = 4`, equality in the last clause of R1; `0 ≤ sz0.lam n` is discharged by `positivity`); target 10 (`κ = 𝔡 = 1/10`, `E = 0` so `Im m = 1`, `u = 1/32`, `D = 1`, `H = 0`, `‖G_u - M‖_max ≤ 1/31 ≤ 1/20`, so `G_u ≠ M`); target 11 (`E = 0`, `D = 2`, `s = 1/2`, `t = 3/4`, extremal tensor). Every deterministic hypothesis is discharged; no hypothesis of any example is an undischarged pin; no `N = 0`, empty index set or collapsed window.
- Layout: imports are exactly the Layout list; no direct `BA/*` import; `NewKLKLGen` reaches `BA.FlowPins`, `BA.MFixedPoint` only through `Chain/NewKLKGen` (E1 `cones.py`); `Chain/NewKLKGen` is outside the certificate cone and the leaf move (1a-audit F4, not taken) was not needed. Reverse cones of both new modules are empty.
- Not run in this stage: the full `lake build` (the hub's merge step, CLAUDE.md §3 (A) 5); the root `import` lines of `RBM3D.lean` (hub step, not edited). Run: `import RBM3D` plus both modules plus `#assert_rbm_axioms` (E6).

## (c) Verified Mathlib names
Each name resolves in the environment of the two modules (`run_cmd` over `env.contains` / `env.getModuleIdxFor?`, module root `Mathlib`, `Init` or `Batteries`; script `names.lean`) and occurs verbatim in the two files (comments and docstrings removed); the files build. Names verified absent: none looked up.
Complex.norm_real Finset.le_sup Finset.le_sup' Finset.mem_univ Finset.mul_sum Finset.prod_congr Finset.sum_add_distrib Finset.sum_comm Finset.sum_congr Finset.sum_le_sum Finset.sum_mul Finset.sup_le Matrix.isHermitian_zero Matrix.mul_apply Matrix.smul_apply Nat.add_le_add Nat.cast_nonneg Real.exp Real.exp_add Real.exp_pos Real.norm_of_nonneg Real.rpow_nonneg Real.rpow_pos_of_pos Real.sq_sqrt Real.sqrt Real.sqrt_le_sqrt Real.sqrt_nonneg Real.sqrt_sq absurd add_le_add_left add_mul div_le_div_iff₀ div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_le_iff₀ div_mul_cancel₀ div_nonneg finRotate inv_eq_one_div le_add_of_nonneg_left le_add_of_nonneg_right le_max_left le_max_right le_rfl le_total le_trans lt_of_lt_of_le lt_trichotomy max_le mul_add mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_nonneg mul_one_div mul_pos mul_pow mul_self_nonneg neg_le_neg norm_mul norm_mul_le norm_nonneg norm_pow norm_smul_le norm_sum_le one_le_pow₀ one_mul one_pos pow_le_pow_left₀ pow_nonneg pow_pos smul_eq_mul smul_mul_assoc smul_smul sq_le_sq₀ sq_nonneg sub_add_sub_cancel sub_eq_iff_eq_add sub_mul zero_le_one

## (d) Open issues and paper-delta candidates
1. **Private-name dependency (dispatcher).** `NewKLKLGen` opens the private `NewKLKGen_conv_two`, `NewKLKGen_ward_LKM` of `Chain/NewKLKGen` (`NewKLKLGen.lean:37`). An edit of `Chain/NewKLKGen` that renames or removes them (for example the leaf move of its BA example, 1a-audit F4) breaks `NewKLKLGen`.
2. **BA readings are not checked here (U4-BA).** R1 at BA (`gK = BAflowLam0 sz z`, `A = (κ+1)/κ`) and `Step5KerGen_ThDecay` at the BA carrier are the shapes of the check file only; the 1a-audit O1 (`Sizes.lam` has no sign) is covered by R1's first clause `0 ≤ gK n * sz.lam n`, which holds at every `n` at both models by Amend 1 item 1 (not re-proved here).
3. Paper-delta `T2462b·a`: the paper writes `(uwp2-92kj)` with one coupling `lam`; Lean reads the decay of the carrier kernel at `gK` and the profile and windows at `sz.lam`, joined by R1 (band `gK = sz.lam`, `A = 1`); the constants `Cp(d, Λ, C₆, A)` are explicit (the paper's `≲`).
4. Paper-delta `T2462b·b`: target 8 states `(eq:decompUalt)` (`1 + Ξ`, `A_deterministic_estimates.tex:100`) for the carrier kernel under the semigroup law `Step2Gen_USemigroup`; the form `(eq:decompU)` of `3_5:1983` (`s/t + ((t-s)/t) Θ_t`) is only re-derived at the band (`Step5KerGen.lean:429`), since the kit defines no propagator (U-C4).
5. Paper-delta `T2462b·c`: `lem:newKLK` at `ℓ = L` over the carrier takes `NewKLKGenHyp` (F5, F8, F9 read; F6, F7 not) as the hypothesis, with `δ₀ = κ/2` and `C = 2(4 + C_K) + C_s C_T`; the paper's `≺` is explicit.
6. Observation: the transitive `BA.FlowPins` / `BA.MFixedPoint` import of `NewKLKLGen` (T2462 note (9)) stands; consumers of target 10 inherit it.
