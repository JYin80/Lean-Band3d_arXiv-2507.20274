Auditor model: claude-opus-5-5

# T2484b (U4s2b of T2484: targets 5-9 and their part of 10-11) — audit, round 1
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2484b-audit1`, detached at `t/T2484b` c61ae3b4; merge base 12f5d1ba; `main` 36f8163a. Written Tue Oct 13 05:37:01 UTC 2026 (`date -u`). Scratch: `<scratchpad>/T2484b/` (`stmtdiff.py`, `audit_pins.lean`, `root_merged.lean`, `greps.sh`, `band_core.lean`; none committed).

## 1. Diff, G1, layering
```
$ git diff --name-only main...t/T2484b
RBM3D/Chain/CltFarUGen.lean
RBM3D/Chain/IniTermIGen.lean
RBM3D/Chain/IniTermIGen2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2484b -- RBM3D/Test/Axioms.lean   (one line, owner text of STIniTermIgL)
-   ... owner U4s2 (`IniTermI`), BA: U4-BA (b) (T2462)
+   ... generic: `stIniTermIgL_of` (T2484, `Chain/IniTermIGen2.lean`); BA: U4-BA (b) (T2462)
$ G1: git diff main...t/T2484b --stat -- RBM3D/Induction RBM3D/Evolution RBM3D/BA Chain/{Carrier,Step2Gen,GridDuhamelGen,Step5Gen,Step5CasesGen,Step5KerGen,CltGen,ZeroModeGen,Step34Gen,IniTermIIGen,B45Gen}.lean | wc -l
       0
$ git merge-tree --write-tree main t/T2484b
a14a3ea86672420a14cfb060f4a17aa62df55bea        (no conflict line)
$ wc -l: CltFarUGen 715, IniTermIGen 1210, IniTermIGen2 787   (all < 2,000; IniTermIGen content 1,997 > 1,800 -> reserve used, as allowed)
$ bash greps.sh
grep -nwE "sorry|admit|native_decide|axiom" | wc -l          0
grep -n "^import RBM3D.BA" | wc -l                            0
U4s3/U5/V imports (Duhamel|EtermsMid|LemDecCalE|PfStep5|Step6|MainInd)   0
U-C4 public defs: CltFarUGen.lean:62 def IniTermGen_CltFlow (Prop); CltFarUGen.lean:135 def STCltFarUConclgL (Prop)
private defs: CltFarUGen_fSum:276, CltFarUGen_bad:461, IniTermIGen_Kf:298, IniTermIGen_Sfull:705, IniTermIGen_Gward:709 (scalar/Set-valued; no kernel)
TN-C4 (STGridRepNgL|ST_gridMart_of_repN): 0 / 0 / 0
X1-C4 (def|abbrev|structure of a merged pin):  0 / 0 / 0
UBA-C1 withLam: 0 / 0 / 0
structure|class|instance decls: 0
X1-C1 hit lines: CltFarUGen 61,76-107 (docstring + band discharge), 140,143 (bridge), 621-704 (band re-derivation, instances)
                 IniTermIGen 38 (docstring), 1138-1193 (instances); IniTermIGen2 555-696 (all `hlam0`, a hypothesis name), 728-776 (band, instances)
$ importers of the new modules: only each other (RBM3D.lean unchanged; hub adds the three import lines at merge)
```
Imports: `CltFarUGen` <- IniTermIIGen, Step34Gen, Evolution.CltFarG, Induction.IniTermI (already in IniTermIIGen's cone); `IniTermIGen` <- CltFarUGen, ZeroModeGen, B45Gen (D3, note (5)); `IniTermIGen2` <- IniTermIGen. No BA/U4s3/U5/V import.

## 2. Statements against the pins
Check `docs/tickets/checks/T2484-check.lean`; target 1 is the 1a-audit text `IniTermGen_KerFacts` (merged U4s2a), which is the check's `T2484_KerFacts` plus E1:
```
$ diff <(check 178-194, renamed) <(IniTermIIGen.lean def IniTermGen_KerFacts)
7a8,9
>       (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool,
>         STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t) ∧
$ python3 -I stmtdiff.py T2484-check.lean CltFarUGen.lean
== IniTermGen_CltFlow vs check T2484_CltFlow: 13 / 13 lines, diff lines: 0
== STCltFarUConclgL vs check T2484_CltFarUConclgL: 4 / 4 lines, diff lines: 0
```
Auditor scratch `audit_pins.lean`: the check's imports + the three new modules; check lines 164-259 copied by `sed` with `T2484_ -> Chk_` and the hypothesis `Chk_KerFacts d Flow mk gK ->` read as `IniTermGen_KerFacts` (1a-audit); then
```
example : Chk_CltFlow = IniTermGen_CltFlow := rfl
example : @Chk_CltFarUConclgL = @STCltFarUConclgL := rfl
example : Chk_BandCltFarU := @bandFM_STCltFarUConcl
example : Chk_CltFarUOf := stCltFarUgL_of
example : Chk_IniTermIOf := stIniTermIgL_of
example : <check shape l.265-270, restriction> := @stIngR5gL_hyps_restrict
example : ∀ d, Chk_CltFlow d seqP STFlow (bandFM ∘ STflowE) lemT := iniTermGen_cltFlow_band      (check l.273-276, target 5 half)
example : ∀ d, STIniTermIgL d seqP STFlow (bandFM ∘ STflowE) lemT := fun d => (STIniTermI_iff_gL d).1 (iniTermIGen_band_holds d)
example : ∀ d, STIngR5 d STReg5I (fun sz E s t => sz.STCltFarUConcl E s t) := iniTermGen_cltFarU_band  (= type of stCltFar_uniform)
example : ∀ d, Sizes.STIniTermI d := iniTermIGen_band_holds
$ lake env lean audit_pins.lean > pins.out; echo "exit $?"; grep -c ": error" pins.out   (05:33:12 UTC)
exit 0
0
stCltFar_uniform : ∀ (d : ℕ), STIngR5 d (fun {d} => STReg5I) fun {d} sz E s t => sz.STCltFarUConcl E s t
```
- Target 5 `IniTermGen_CltFlow`: equals the check text (= 1a-audit text). PASS.
- Target 6 `STCltFarUConclgL` = pin by `rfl` and text; bridge = `T2484_BandCltFarU`; `stIngR5gL_hyps_restrict` = check shape. PASS.
- Target 7 `stCltFarUgL_of`: conclusion `STIngR5gL d STReg5I law Flow mk T0 (… STCltFarUConclgL …)` = pin; hypotheses = pin shape with target 1's 1a-audit text. Quantifier order (fixed `κ ε 𝔡`, `Cd`, then `∃ 𝔠d`, then flow members) is that of `STIngR5gL` (merged). PASS.
- Target 8 (a) cores against the band (`#check iniTermI_core_same/_mixed/_lossy`, `band_core.lean`): same hypotheses with `0 < g ≤ Λ`, `|E| ≤ 2`, `κm ≤ Im mE` replaced by `Flow sz κ ε 𝔠 𝔡 z`, `0 < gK n ≤ 𝔡⁻¹`; same window `lam²/L² ≤ 1-u`, same losses (`W^{-D}`; mixed `(1-s)/(1-u) W^{-D}`; lossy `(1-s)/(1-u)` overall), `iniTermI_Sfull` spelled out as `(1-s)² Σ Θ X Θ` with `STThg` at `u`. 8 (b)-(d) are private (shapes not pinned). PASS.
- Target 9 `stIniTermIgL_of`: conclusion head `STIniTermIgL d law Flow mk T0` = pin; hypotheses = pin shape (probability, FlowFacts, target 1, Ward class per flow member under `0 < κ`, target 5). PASS.

## 3. Hidden hypotheses, vacuity, cycles
- No structure/class/instance declared; the two public defs are `Prop`s appearing as explicit premises. `IniTermGen_CltFlow` is non-vacuous: `iniTermGen_cltFlow_band` proves it at the band family for every `d` (instance at `szB, zB` in §4). `STCltFarUConclgL` is never a premise of a public theorem (only conclusion; `IniTermIGen_concl` is private).
- Dependencies are merged: `stCltFargL_holds` (X1b), `IniTermGen_KerFacts`/`iniTermGen_kerFacts_band` (U4s2a ba7e559e), `B45_ward_fing` (`Chain/B45Gen.lean:117`, 78f4cc14), `ZeroModeGen_WardCls`/`zeroModeGen_wardCls_band` (U1s1/U6). No cycle: nothing outside the three files imports them.
- D3: `IniTermIGen_ward` (IniTermIGen2:338) is `B45_ward_fing … (m := 0)` with `ZeroModeGen_WardCls` as hypothesis; no second Ward text.
- No new external hypothesis (no DECISIONS-level input): the remaining premises are other gates' pins (Steps 1-4 inside `STIngR5gL`) and the classes of targets 1/5, discharged at the band.

## 4. Compiled nonempty instances (all in the build of §5)
Data: `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `lam = 1`), `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, window `(s,t) = (7/8, 15/16)` (`szB_reg5I`, `flow_zB`, `szB_flow_ht`), `Cd > 0`.
- Target 5: `CltFarUGen.lean:636` example (all fields except `Σ|M|² ≤ 1`, which is discharged but not restated; the whole class is `iniTermGen_cltFlow_band 3`, used at :692).
- Target 6: :662 bridge at `szB`; :668 restriction at `t' = 29/32`, regime and `(con_st_ind)` (`conStInd_const`) discharged; Steps 1-4 premises as hypotheses (other gates' pins).
- Target 7: :692 `stCltFarUgL_of` applied directly; probability (`inferInstance`), FlowFacts, KerFacts, CltFlow discharged by band results; flow, window, `con_st_ind` discharged; `STKboundgL`, `STKwardgL`, `STLKgL`, `STDecaygL`, `STDecayStronggL`, `STStep1LoopgL`, `STStep2ConclgL`, `STLmaxUgL`, `STLKUgL` are hypotheses (other gates' pins). Also :685 through `inst_ing5_I`.
- Target 8 (a): IniTermIGen:1137/:1158/:1186, `n = 0`, `W = D = 2`, `M = lam = 1`, `σ = (+,+)`/`(+,-)`, nonzero `X_b = W^{-3} 𝒯_{7/8}(|b₀-b₁|) + W^{-2}`, guard `0 < lam 0 = 1 ≤ 10`, window `1/16 ≤ 1/16` discharged.
- Target 9: IniTermIGen2:762 `stIniTermIgL_of` applied directly, Ward class by `zeroModeGen_wardCls_band`, same discharges and same Step 1-4 hypotheses as target 7; :746, :757 through `inst_iniTermI`.
None degenerate (no `N = 0`, empty index, collapsed window or `False` premise; `s < t`, `L = 4`, `W_n → ∞`). PASS.

## 5. Build and axioms
```
$ lake build RBM3D.Chain.CltFarUGen RBM3D.Chain.IniTermIGen RBM3D.Chain.IniTermIGen2 | grep -E ": error|Build"; echo exit
Build completed successfully (3855 jobs).
exit 0          (error lines: 0)
$ lake build      (branch root, new modules not yet imported)
info: RBM3D.lean:573:0: axiom audit: 14502 theorems, 4538 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 59, structural 46, refuted 6, superseded 14).
Build completed successfully (4341 jobs).
exit 0
$ lake env lean root_merged.lean   (all `import` lines of RBM3D.lean + the three new modules + #assert_rbm_axioms; 05:34:26 UTC)
exit 0
axiom audit: 14516 theorems, 4540 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]
premises found by scanning: 125 (borrowed 1, owed 58, structural 46, refuted 6, superseded 14).
$ #print axioms (audit_pins.lean)
'RBM.BA.iniTermGen_cltFlow_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STCltFarUConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stIngR5gL_hyps_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stCltFarUgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.iniTermGen_cltFarU_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.iniTermIGen_core_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.iniTermIGen_core_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.iniTermIGen_core_lossy' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stIniTermIgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.iniTermIGen_band_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.CltFarUGen_cltFar_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry: with the new modules the scan passes; owed drops 59 -> 58 (`STIniTermIgL` now concluded by `stIniTermIgL_of`); no new premise, so no new registry line (ticket: "expected none"). The one `Test/Axioms.lean` change is the owner text the ticket prescribes.
Name clash (`git grep -lw <name> main -- RBM3D`): all 16 new public names (`IniTermGen_CltFlow`, `iniTermGen_cltFlow_band`, `CltFarUGen_cltFar_of`, `STCltFarUConclgL`, `bandFM_STCltFarUConcl`, `stIngR5gL_hyps_restrict`, `CltFarUGen_Theta_sub/_Th_entry/_Th_lip`, `stCltFarUgL_of`, `iniTermGen_cltFarU_band`, `iniTermIGen_core_same/_mixed/_lossy`, `stIniTermIgL_of`, `iniTermIGen_band_holds`): 0 files each. Unpinned public helpers carry the stem `CltFarUGen_` (§3 (E)).

## 6. Paper deltas
Lean/paper differences of this row: (i) the initial terms over the carrier with kernel facts at `gK` -> `T2484a` (T2484-prove.md (a)); (ii) E1 as carrier datum -> `T2484b` (idem; used in `IniTermGen_core_data`); (iii) X1's far pin applied at every grid time `t' ∈ (s,t]` with the class carrying the `t`-free fields of `HCltOf` and Step-2 premises restricted to `[s,t']` -> new candidate `T2484c` (T2484b-prove.md (d)); (iv) CLT uniform in `u` -> `T2329b` (carried over). All proposed; numbering at merge. Coverage complete.

## 7. Observations (no RETURN)
1. The target-5 instance at `CltFarUGen:636` does not restate the field `Σ_y |M_xy|² ≤ 1`; the full class is discharged by `iniTermGen_cltFlow_band 3` inside the target-7 instance (:692), so the instance requirement is met.
2. `CltFarUGen` imports `Induction.IniTermI` directly (not in the ticket's import list); it is already in the cone of `Chain/IniTermIIGen`, so the cone is unchanged.
3. The probe `RBM3D/Probe/T2484Pins.lean` on `t/T2484` defines a second `iniTermGen_cltFlow_band`; it is never merged, so no clash on `main`.
4. Prove report line 7 cites "Tue Oct 13 05:28:11 UTC" for section (b) while its full-build line says it ran on 27850c3d, not on HEAD c61ae3b4; c61ae3b4 changes only a header comment, and this audit rebuilt HEAD.

## Verdict
- Target 5 PASS; target 6 PASS; target 7 PASS; target 8 PASS; target 9 PASS; targets 10-11 (U4s2b part) PASS.
- **T2484b: PASS.** No dispatcher sign-off needed. Hub at merge: add `import RBM3D.Chain.CltFarUGen`, `RBM3D.Chain.IniTermIGen`, `RBM3D.Chain.IniTermIGen2` after the last `import` line of `RBM3D.lean` and run the full `lake build`.
