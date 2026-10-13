Prover model: claude-sonnet-5-5

# T2484b (U4s2b: targets 5-9 of T2484 and their part of 10-11): prove report
## (a) Math preflight (stage 1a): not repeated
Stage 1a of this row is `docs/reports/T2484-prove.md` (a) (lines 3-97, tables (i)-(xiii)) and (a″) (lines 99-227), audited PASS in `docs/reports/T2484-1a-audit.md` ("Split confirmed as pre-signed"; target 1 = the probe text with E1, target 5 = the check text). I read both and found no mistake in them, so there is no (a′). U4s2a (`Chain/IniTermIIGen`, targets 1-4) is on `main` (ba7e559e) and is not part of this report.

## (b) Script output, Tue Oct 13 05:28:11 UTC 2026 (stage 1b of U4s2b; branch `t/T2484b` HEAD c61ae3b4 on base `main` 12f5d1ba; scripts `final.sh`, `stmts.py`, `pins_check.lean`, `axioms.lean` in the scratchpad subdirectory `T2484b/`)
### (1) Lines per file and the split (stop rule 2,000 per file, H134)
Section commits, UTC (`git log`; `git show <c>:<file> | wc -l`): 2771e3e7 04:30:50 `CltFarUGen` 693; e386770b 04:48:19 `IniTermIGen` 1211; 3fbda54b 05:11:04 `IniTermIGen2` 765; 32f51d48 05:12:59 `Test/Axioms.lean`; 27850c3d 05:21:44 `CltFarUGen` 715, `IniTermIGen2` 787; c61ae3b4 05:24:22 `IniTermIGen` 1210 (header comment only).
```
$ wc -l
     715 RBM3D/Chain/CltFarUGen.lean
    1210 RBM3D/Chain/IniTermIGen.lean
     787 RBM3D/Chain/IniTermIGen2.lean
    2712 total
$ lake build RBM3D.Chain.CltFarUGen RBM3D.Chain.IniTermIGen RBM3D.Chain.IniTermIGen2 | tail -2
Build completed successfully (3855 jobs).
```
1a prediction (T2484-prove.md l.78): `CltFarUGen` 549 + `IniTermIGen` 1,190 = 1,739 (2.6x: 4,520). Actual 715 + 1,997 (= 1,210 + 787) = 2,712, i.e. 1.56x. The 1,800-line reserve rule applies to `IniTermIGen` (content 1,997): `IniTermIGen2` imports `IniTermIGen` (precedent `SEforLnGen2`) and holds target 8 (d) (Ward step, real-level estimates) and target 9 (`iniTermIGen_concl`, the pin, the band re-derivation), so `IniTermIGen` keeps 8 (a)-(c).
### (2) Layout, importers, cone
```
$ git diff --stat main...t/T2484b
 RBM3D/Chain/CltFarUGen.lean   |  715 ++++++++++++++++++++++++
 RBM3D/Chain/IniTermIGen.lean  | 1210 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/IniTermIGen2.lean |  787 +++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    2 +-
 4 files changed, 2713 insertions(+), 1 deletion(-)
$ G1: git diff main...t/T2484b -- Induction Evolution BA and the merged Chain files | wc -l
       0
$ layering: grep -n '^import RBM3D.BA' the 3 files | wc -l
       0
$ imports
RBM3D/Chain/CltFarUGen.lean:6:import RBM3D.Chain.IniTermIIGen
RBM3D/Chain/CltFarUGen.lean:7:import RBM3D.Chain.Step34Gen
RBM3D/Chain/CltFarUGen.lean:8:import RBM3D.Evolution.CltFarG
RBM3D/Chain/CltFarUGen.lean:9:import RBM3D.Induction.IniTermI
RBM3D/Chain/IniTermIGen.lean:6:import RBM3D.Chain.CltFarUGen
RBM3D/Chain/IniTermIGen.lean:7:import RBM3D.Chain.ZeroModeGen
RBM3D/Chain/IniTermIGen.lean:8:import RBM3D.Chain.B45Gen
RBM3D/Chain/IniTermIGen2.lean:6:import RBM3D.Chain.IniTermIGen
$ importers of the new modules in RBM3D (outside the 3 files)
       0
```
`git merge-tree --write-tree main t/T2484b` (main 36f8163a at 05:21 UTC): a tree hash, no conflict line. Cone: `CltFarUGen` is the only new module that imports a band file (`Induction.IniTermI`, model-free names); nothing imports the new modules yet. `RBM3D.lean` is unchanged on the branch (as for U4s2a): the hub adds `import RBM3D.Chain.CltFarUGen`, `IniTermIGen`, `IniTermIGen2` at merge (§3 (A) 4); I ran the full build with those three lines added for the run only (not committed).
Name clash: `git grep -n` of the new public and stem names (`IniTermGen_CltFlow`, `iniTermGen_cltFlow_band`, `STCltFarUConclgL`, `bandFM_STCltFarUConcl`, `stIngR5gL_hyps_restrict`, `stCltFarUgL_of`, `iniTermGen_cltFarU_band`, `stIniTermIgL_of`, `iniTermIGen_`, `IniTermIGen_`, `CltFarUGen_`) outside the three files:
```
refs scanned: 102 (main and every t/T24*); refs with a hit: t/T2484(8162591d): hits 5, module files 0;
   5 RBM3D/Probe/T2484Pins.lean
```
The 5 hits on `t/T2484` are in the probe `RBM3D/Probe/T2484Pins.lean` (never merged, no root import); it defines its own `iniTermGen_cltFlow_band` in the same namespace, so the probe must not be imported together with the new modules.
### (3) Statements against the pins (check `docs/tickets/checks/T2484-check.lean`, `T2484_KerFacts` read as the 1a-audit text `IniTermGen_KerFacts`)
```
== class IniTermGen_CltFlow vs check T2484_CltFlow: check 13 lines, mine 13 lines, diff lines: 0
== def STCltFarUConclgL vs check T2484_CltFarUConclgL: check 4 lines, mine 4 lines, diff lines: 0
$ lake env lean pins_check.lean ; echo "exit: $?"   (05:30:00 UTC)
  [pins_check.lean = the defs of the check T2484_CltFlow, _CltFarUConclgL, _BandCltFarU, _CltFarUOf, _IniTermIOf and its restrict and band-family shapes,
   copied by script as Chk_* with T2484_KerFacts read as IniTermGen_KerFacts, then: Chk_CltFlow = IniTermGen_CltFlow := rfl; Chk_CltFarUConclgL = STCltFarUConclgL := rfl;
   example : Chk_BandCltFarU := @bandFM_STCltFarUConcl; Chk_CltFarUOf := stCltFarUgL_of; Chk_IniTermIOf := stIniTermIgL_of; Chk_restrict := @stIngR5gL_hyps_restrict;
   Chk_band15 (targets 1, 5), Chk_band49 (targets 4, 9) at the band family; #print axioms of the three theorems]
'bandFM_STCltFarUConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'stCltFarUgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'stIniTermIgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
exit: 0
```
Target statements extracted from the files by `stmts.py` (whitespace collapsed; `[file:line]` then the declaration up to `:=`):
```
CltFarUGen.lean:62: def IniTermGen_CltFlow (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop
CltFarUGen.lean:83: theorem iniTermGen_cltFlow_band (d : ℕ) : IniTermGen_CltFlow d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
CltFarUGen.lean:135: def STCltFarUConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop
CltFarUGen.lean:142: theorem bandFM_STCltFarUConcl : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.STCltFarUConcl E s t ↔ STCltFarUConclgL (bandFM sz E) (Sizes.seqP sz) s t
CltFarUGen.lean:161: theorem stIngR5gL_hyps_restrict {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t t' : ℕ → ℝ) (𝔠d Cd : ℝ) (h𝔠d : 0 < 𝔠d) (hst' : ∀ n, s n < t' n) (ht' : ∀ n, t' n ≤ t n) (ht1 : ∀ n, t n < 1) (hR : STReg5I sz s t) (hCon : sz.STConStInd 𝔠d s t) (hS1 : STStep1LoopgL C μ s t) (hS2 : STStep2ConclgL C μ s t Cd) (hLmax : STLmaxUgL C μ s t) (hLKU : STLKUgL C μ s t) : STReg5I sz s t' ∧ sz.STConStInd 𝔠d s t' ∧ STStep1LoopgL C μ s t' ∧ STStep2ConclgL C μ s t' Cd ∧ STLmaxUgL C μ s t' ∧ STLKUgL C μ s t'
CltFarUGen.lean:479: theorem stCltFarUgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) → Step5CasesGen_FlowFacts d Flow mk T0 → IniTermGen_KerFacts d Flow mk gK → IniTermGen_CltFlow d law Flow mk T0 → STIngR5gL d STReg5I law Flow mk T0 (fun sz z s t => STCltFarUConclgL (mk sz z) (law sz) s t)
CltFarUGen.lean:622: theorem iniTermGen_cltFarU_band (d : ℕ) : STIngR5 d STReg5I (fun sz E s t => sz.STCltFarUConcl E s t)
IniTermIGen.lean:537: theorem iniTermIGen_core_same (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam → ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ, (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + W ^ (-D))) → ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a‖ ≤ C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + W ^ (-D))
IniTermIGen.lean:617: theorem iniTermIGen_core_mixed (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ, (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + W ^ (-D))) → ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a - (c : ℂ) * ((((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n), STThg (mk sz z) n (σ 0) (σ 1) u (a 0) b₁ * STThg (mk sz z) n (σ 0) (σ 1) u (a 1) b₂ * X ![b₁, b₂])‖ ≤ C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D))
IniTermIGen.lean:667: theorem iniTermIGen_core_lossy (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 → sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u → 0 ≤ M → 0 ≤ lam → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ, (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + W ^ (-D))) → ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a‖ ≤ C * M * ((1 - s) / (1 - u) * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D)))
IniTermIGen2.lean:707: theorem stIniTermIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) → Step5CasesGen_FlowFacts d Flow mk T0 → IniTermGen_KerFacts d Flow mk gK → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ZeroModeGen_WardCls sz (mk sz z)) → IniTermGen_CltFlow d law Flow mk T0 → STIniTermIgL d law Flow mk T0
IniTermIGen2.lean:730: theorem iniTermIGen_band_holds (d : ℕ) : STIniTermI d
```
### (4) D1-D3 as used; `open private`; copies
- **D1** (`IniTermGen_KerFacts`, merged U4s2a): `USemigroup` -> `CltFarUGen_Theta_sub/_Th_entry/_Th_lip` (CltFarUGen:196-266) and `IniTermIIGen_UN_rep` (via `IniTermIGen_core_data`, IniTermIGen:583); `ThDecay` at `gK` -> `IniTermIGen_Th_decay` (:65), `IniTermIGen_stageA` (:211, profile), row sums in `stCltFarUgL_of` (CltFarUGen:479); R1 -> `Th_decay` (crossing), `iniTermIGen_core_same` (:537), `CltFarUGen_guard` (:466); E1 -> `hpair` of `UN_rep` for `σ₁ ≠ σ₂` (IniTermIGen:608); short range -> `iniTermIGen_core_same`; column sum and zero mode: not read in case (i).
- **D2** (`IniTermGen_CltFlow`): `CltFarUGen_cltFar_of` (:113) assembles `HCltOf` at `t' ∈ (s,t]` from the `t`-free fields, `FlowFacts` and the restricted Step-2 premises (`stIngR5gL_hyps_restrict`, :161) and applies `stCltFargL_holds`; `STThPropsg` also feeds `IniTermIGen_theta_far` (:129) and the symmetry used in `IniTermIGen_concl` (IniTermIGen2:400); band discharge `iniTermGen_cltFlow_band` (CltFarUGen:83).
- **D3**: `B45_ward_fing` (`Chain/B45Gen.lean:117`, on `main`) from `ZeroModeGen_WardCls`: `IniTermIGen_ward` (IniTermIGen2:329), `IniTermIGen_ward_bound` (:357); no inline copy, no conjugation, no second Ward text.
- `open private` (3 files): `IniTermIIGen_ZA`, `IniTermIIGen_Kf_norm_le` (IniTermIIGen), `CltFarUGen_fSum`, `CltFarUGen_guard` (CltFarUGen), `Step5KerGen_cmp_pos`, `Step5KerGen_tailT_cross` (Step5KerGen), and the nine `IniTermIGen_*` privates opened by `IniTermIGen2` (`mixed_bound`, `mixed_tail`, `Sfull`, `Kf`, `Th_decay`, `theta_pi`, `theta_far`, `theta_conv`, `core_data`).
- Copies (regenerated for the carrier, band source in the docstring): `IniTermIGen_stageA` (IniTermIIGen_stageA with the window `Or.inl`), `CltFarUGen_prec_restrict`, `U0`, `bil_lossy`, `Sfull_decomp`, `tail`, `mixed_bound`, `mixed_tail`, `theta_pi/far/conv`, `ward`, `ward_bound`, `rl_same/lossy/tail/in/all` (real-valued, core bounds as hypotheses), `IniTermIGen_concl`. Private defs (scalar or `Set` valued, no kernel): `CltFarUGen_fSum`, `CltFarUGen_bad`, `IniTermIGen_Kf`, `IniTermIGen_Sfull`, `IniTermIGen_Gward`.
### (5) Reader table (object <- feeder)
- IniTermI:306 `(1-s)Σ_b‖Θ_u(a₁,b)‖𝒯_s(b-a₂) ≤ C𝒯_u` <- `step5KerGen_profile_holds` on `θ` with `Θ = 1 + uθ`, window `Or.inl (lam²/L² ≤ 1-u)`: `IniTermIGen_stageA` (IniTermIGen:211).
- IniTermI:487 `𝒰^{(2)} = K ⊗ K` <- `Step5KerGen_UN_decomp` + E1: `IniTermIIGen_UN_rep` (merged), used in `IniTermIGen_core_data` (:583).
- IniTermI:2139 `‖Θ_u(x,y)‖ ≤ C(g²)⁻¹PI` <- ThDecay at `gK`, crossing, `1 ≤ (AΛ²+1)𝒯^{lam}_u(0)`: `IniTermIGen_Th_decay` (:65), `IniTermIGen_theta_pi` (:110).
- IniTermI:2201 `Σ_b‖Θ‖‖Θ‖ ≤ C(1-u)⁻¹𝒯_u` <- `Th_decay` twice and `ekPropTInf_holds`: `IniTermIGen_theta_conv` (:172). IniTermII:332, :940 belong to U4s2a (merged).
### (6) UBA-C1 as used
| statement | size level (`sz.lam`) | kernel (`gK`) | where R1 enters |
|---|---|---|---|
| 6-7 | `ellT`, `STfFarg`, `STThPropsg` | row sums of `θ` (no coupling) | only the guard (g), `CltFarUGen_guard` (CltFarUGen:466), used at CltFarUGen:545 |
| 8 | `STReg5I`, `ellT`, tails | `ThDecay`, short range | crossing `𝒯^{gK} ≤ A𝒯^{lam}` in `IniTermIGen_Th_decay` (IniTermIGen:75), profile in `stageA` (:222), `lam ≤ A𝔡⁻¹` and `gK² ≤ lam²` in `core_same` (:555-561, :571); guard (g) (`0 < gK` from `0 < lam`) in `core_data` (:609) and `IniTermIGen_concl` (IniTermIGen2:477) |
| 4, 9 | regimes, `Bctl`, `STAI` | through 2, 8 | only inside them |
No second comparison form and no `sz.withLam` (grep below).
### (7) Registry and premise scan
```
$ git diff --stat main...t/T2484b -- RBM3D/Test/Axioms.lean   (the one changed line is the owner text of STIniTermIgL: + generic: `stIniTermIgL_of` (T2484, `Chain/IniTermIGen2.lean`))
 RBM3D/Test/Axioms.lean | 2 +-
$ lake build (whole library; RBM3D.lean with the three import lines added for the run only; 05:18:18 -> 05:21:36 UTC, on 27850c3d)
info: RBM3D.lean:576:0: axiom audit: 14516 theorems, 4540 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 125 (borrowed 1, owed 58, structural 46, refuted 6, superseded 14).
Build completed successfully (4344 jobs).
```
The scan found no unregistered premise (the audit passed), so no new registry line was needed; `STCltFarUConclgL` is never a hypothesis (the private `IniTermIGen_concl` spells the `PrecL` out). `STIniTermIgL` now appears under "registered premises that carry nothing yet" (concluded by `stIniTermIgL_of`), as `STIniTermIIgL` after U4s2a.
### (8) Greps
```
$ U-C4: grep -nE '^(noncomputable )?def' (public defs)
RBM3D/Chain/CltFarUGen.lean:62:def IniTermGen_CltFlow (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
RBM3D/Chain/CltFarUGen.lean:135:def STCltFarUConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
$ private defs
RBM3D/Chain/CltFarUGen.lean:276:private def CltFarUGen_fSum {d L : ℕ} [NeZero L] (Th : Zd d L → Zd d L → ℂ) (s : ℝ) (X : (Fin 2 →
RBM3D/Chain/CltFarUGen.lean:461:private def CltFarUGen_bad {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (s : ℕ → ℝ) (τ : ℝ) (n : ℕ) (v :
RBM3D/Chain/IniTermIGen.lean:298:private def IniTermIGen_Kf {d L : ℕ} [NeZero L] (Th : Zd d L → Zd d L → ℂ) (α β : ℝ) (a b : Zd d
RBM3D/Chain/IniTermIGen.lean:705:private def IniTermIGen_Sfull (Th : Zd d L → Zd d L → ℂ) (s : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a :
RBM3D/Chain/IniTermIGen.lean:709:private def IniTermIGen_Gward (Th : Zd d L → Zd d L → ℂ) (s : ℝ) (X : (Fin 2 → Zd d L) → ℂ) (a :
$ TN-C4: grep -cE 'STGridRepNgL|ST_gridMart_of_repN'
RBM3D/Chain/CltFarUGen.lean:0
RBM3D/Chain/IniTermIGen.lean:0
RBM3D/Chain/IniTermIGen2.lean:0
$ X1-C4: grep -cE '(def|abbrev|structure) (STCltFargL|HCltOf|CltRepg|STThPropsg|STKpropsg|STExpInvgL|STfFarg|STIniTermIgL|STIniTermIIgL|STIniTermConclgL|Step5KerGen_ThDecay|ZeroModeGen_WardCls|Step5CasesGen_FlowFacts)'
RBM3D/Chain/CltFarUGen.lean:0
RBM3D/Chain/IniTermIGen.lean:0
RBM3D/Chain/IniTermIGen2.lean:0
$ UBA-C1: grep -c withLam
RBM3D/Chain/CltFarUGen.lean:0
RBM3D/Chain/IniTermIGen.lean:0
RBM3D/Chain/IniTermIGen2.lean:0
$ sorry|admit|native_decide|^axiom
RBM3D/Chain/CltFarUGen.lean:0
RBM3D/Chain/IniTermIGen.lean:0
RBM3D/Chain/IniTermIGen2.lean:0
```
X1-C1 (`grep -nE` with the ticket pattern), hit lines per file: `CltFarUGen` 61, 76-107, 140, 143, 621-704; `IniTermIGen` 38, 1138-1193; `IniTermIGen2` 555-696 and 728-776. Classification by `x1c1.py`: CltFarUGen 61-107 docstring and the band discharge `iniTermGen_cltFlow_band` (STFlow, STflowE, cltCk, lemT, seqP); 140-143 the band bridge (`seqP`); 621-704 the band re-derivation and instances; IniTermIGen 38 docstring (`Ugen_rep`), 1138-1193 instances; IniTermIGen2 555-696 are the substring `lam0` inside the hypothesis name `hlam0` of the private `IniTermIGen_concl` (no band object), 728-776 the band re-derivation and instances. No hit in a generic statement or proof body.
### Axioms of the public declarations (`axioms.lean`, `#print axioms`, prefix `RBM.BA.` dropped)
```
IniTermGen_CltFlow [propext, Classical.choice, Quot.sound]
iniTermGen_cltFlow_band [propext, Classical.choice, Quot.sound]
CltFarUGen_cltFar_of [propext, Classical.choice, Quot.sound]
STCltFarUConclgL [propext, Classical.choice, Quot.sound]
bandFM_STCltFarUConcl [propext, Classical.choice, Quot.sound]
stIngR5gL_hyps_restrict [propext, Classical.choice, Quot.sound]
CltFarUGen_Theta_sub [propext, Classical.choice, Quot.sound]
CltFarUGen_Th_entry [propext, Classical.choice, Quot.sound]
CltFarUGen_Th_lip [propext, Classical.choice, Quot.sound]
stCltFarUgL_of [propext, Classical.choice, Quot.sound]
iniTermGen_cltFarU_band [propext, Classical.choice, Quot.sound]
iniTermIGen_core_same [propext, Classical.choice, Quot.sound]
iniTermIGen_core_mixed [propext, Classical.choice, Quot.sound]
iniTermIGen_core_lossy [propext, Classical.choice, Quot.sound]
stIniTermIgL_of [propext, Classical.choice, Quot.sound]
iniTermIGen_band_holds [propext, Classical.choice, Quot.sound]
```
### Instances (compiled `example`s, `d = 3`, `szB` (L = 4, W_n = n + 4, lam = 1), `zB = 1/2 + i/64`, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6, `n = 0`, `(s,u) = (7/8, 15/16)`: lam²/L² = 1/16 = 1-u ≤ 1-s = 1/8 ≤ lam² = 1)
- CltFarUGen:636 target 5 (every field, window (7/8,15/16)); :654 `CltFarUGen_cltFar_of` (the two restricted Step-2 premises are hypotheses); :662 bridge; :668 `stIngR5gL_hyps_restrict` at `t' = 29/32` (regime and `(con_st_ind)` discharged, five Step 1-4 premises hypotheses); :685 target 7 through the band shape (`inst_ing5_I`, `iniTermGen_cltFarU_band`); :692 target 7 applied directly: `stCltFarUgL_of` with its four hypotheses discharged by the band results, `flow_zB`, `szB_reg5I`, `conStInd_const`; the Step 1-4 premises (other gates' pins) are hypotheses.
- IniTermIGen:1137, :1158, :1186: `iniTermIGen_core_same`, `_core_mixed`, `_core_lossy` at `W = D = 2`, `M = lam = 1`, `X_b = W^{-d}𝒯_s(|b₁-b₂|) + W^{-D}` (nonzero); IniTermIGen2:746 (pin through the band shape), :757 (band re-derivation), :762 (`stIniTermIgL_of` applied directly, the Ward class by `zeroModeGen_wardCls_band`).

**Narrative.**
- Delivered: all of targets 5-9 and their part of 10-11. `CltFarUGen` = targets 5-7 (class `IniTermGen_CltFlow`, `STCltFarUConclgL`, bridge, `stIngR5gL_hyps_restrict`, `stCltFarUgL_of`, `iniTermGen_cltFarU_band`); `IniTermIGen` = 8 (a)-(c) (Θ bounds, the three cores, `Sfull`/`fSum` decomposition, mixed bound and tail); `IniTermIGen2` = 8 (d), 9 (Ward, real-level estimates, `stIniTermIgL_of`, `iniTermIGen_band_holds`). Target 6 (definition and bridge), 7 and 9 equal their `T2484_*` pins and target 5 equals the check text (section (3)); target 4 is U4s2a's. G1 is empty.
- The generic lemmas are stated over an abstract propagator `Th : Zd d L → Zd d L → ℂ` with explicit constants (`CR = 1 + C₆` for the row sums of `Θ = 1 + uθ`, `CΘ = C₆A + (AΛ²+1)` for the decay, `c* = C₆(1+C₆)²` for the Lipschitz bound); `STfFarg` is `CltFarUGen_fSum` at `Θ^{(σ₀σ₁)}_u` by `rfl`. The real-level lemmas (`rl_*`) are stated for reals with the core bounds as hypotheses.
- Not in the band: the resolvent identity `Θ_w - Θ_v = (w-v)θ_wΘ_v` from the semigroup law at `(0,v,w)` (`CltFarUGen_Theta_sub`); the mixed tail carries a factor `CR²` that `IniTermIGen_concl` absorbs into `K₃ = CR²(2C_f(2c₀+1)+2c₀+2)`; `κ_m` is the datum of `FlowFacts` (`κm ≤ Im m`, `η = (1-t) Im m`), not `√(κ(4-κ))/2`.
- `IniTermIGen_concl` is private and takes `hCLT` as the spelled-out `PrecL`, so `STCltFarUConclgL` is never a premise of a public theorem.
- Stop rules: none fired (largest file 1,210 lines; no band or merged file edited; no `BA/*` or U4s3/U5/V import; no new `FlowFM` field; no restated merged pin; premise scan clean).

## (c) Verified Mathlib names (compiled in this tree)
`Finset.exists_max_image`, `Finset.sum_filter_not_add_sum_filter`, `Finset.single_le_sum`, `measure_biUnion_finset_le`, `measure_union_le`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`, `mul_self_le_mul_self`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_add_one'`, `pow_add_pow_le`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `Matrix.mul_apply`, tactic `module`. Deprecated in this Mathlib (warnings observed in the build): `if_pos`, `if_neg`, `if_true`, `if_false` (replaced by `ite_true`, `ite_false` under `simp only`).

## (d) Open issues and paper-delta candidates
- `T2484a`, `T2484b` as in T2484-prove.md (a) (initial terms over the carrier with the kernel facts at `gK`; E1). New `T2484c`: X1's far pin is applied at every grid time `t' ∈ (s,t]`; the Lean class `IniTermGen_CltFlow` carries the `t`-free fields of `HCltOf` and the paper's Step-2 bounds are restricted to `[s,t']`. `T2329b` (CLT uniform in `u`) carries over unchanged.
- Owed to U4-BA: the BA discharge of `IniTermGen_KerFacts` and `IniTermGen_CltFlow` (shapes in the check, not compiled here), the BA flow facts and Ward class (UN-C3 owner).
- Hub: add the three import lines at merge; U4s2b is stacked on U4s2a (base 12f5d1ba contains `IniTermIIGen` and `B45Gen`).
