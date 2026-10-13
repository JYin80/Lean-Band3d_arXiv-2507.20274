Auditor model: claude-opus-5-5
# T2479 audit, round 1 (X1b-1 of the pre-signed split: targets 1-4) — Tue Oct 13 00:23:33 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2479-audit1`, detached at `t/T2479` = `03f828ee`. Scratch: `scratchpad/T2479/`.
Scope. The 1a central (2141) exceeds 1,950, so the ticket's pre-signed split applies: this branch is X1b-1 = `CltMoments2G` +
`MeanFarG` (targets 1-4). Targets 5-9 (`CltFarG`, the pin `STCltFargL`, `T2479_ThPropsBand/KPropsBand/BandFar`) belong to
X1b-2 on `t/T2479b`; they are not audited here and their absence is not a defect of this row.

## 1. Diff scope, imports, G1, forbidden tokens
```
$ git diff --name-only main...HEAD
RBM3D.lean
RBM3D/Evolution/CltMoments2G.lean
RBM3D/Evolution/MeanFarG.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- <4 band files> RBM3D/Chain RBM3D/Induction RBM3D/BA | wc -l
       0
$ grep -n "^import" <2 new files>
RBM3D/Evolution/CltMoments2G.lean:6:import RBM3D.Evolution.CltMoments2
RBM3D/Evolution/CltMoments2G.lean:7:import RBM3D.Chain.CltGen
RBM3D/Evolution/MeanFarG.lean:6:import RBM3D.Evolution.MeanFar
RBM3D/Evolution/MeanFarG.lean:7:import RBM3D.Chain.CltGen
$ wc -l <2 new files>          (stop line 2,000)
     729 RBM3D/Evolution/CltMoments2G.lean
     869 RBM3D/Evolution/MeanFarG.lean
$ grep -rnE "sorry|admit|native_decide|^axiom|^\s*axiom " <2 new files> | wc -l
       0
```
`RBM3D.lean`: two import lines added after the last import, `#assert_rbm_axioms` stays last. `Test/Axioms.lean`: 5 `owedProps` lines only.
All files are sole writable files. Band files byte-identical to `main`, so the 97 Part 3 names are unchanged (G1).

## 2. Builds, check file, axioms
```
$ lake build RBM3D.Evolution.CltMoments2G RBM3D.Evolution.MeanFarG
errors: 0   warnings in the 2 files: 28, of which not line-length: 0
Build completed successfully (3822 jobs).
$ lake build            (whole library, #assert_rbm_axioms + registry scan)
exit=0; errors: 0
5857:registry: 2 borrowed + 111 owed + 122 structural + 7 refuted + 18 superseded; ...
5983:Build completed successfully (4320 jobs).
$ lake env lean docs/tickets/checks/T2479-check.lean      (on the branch; includes Part 3 #check of the 97 band names)
exit=0, error lines 0
$ lake env lean scratchpad/T2479/audit_check.lean          (auditor file, §3; #print axioms of every new public theorem)
'RBM.BA.cltMom1_weight_a1g' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom1_weight_a2g' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom2_decompg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom2_norm_stcltBg_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom2_weightg_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom2_moment_fixedg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom2_tail_eventuallyg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.cltMom2G_lenv_of_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.meanFarG_lenv_of_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.meanFar_eventuallyg' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```

## 3. Statements (target 4 against the check text; targets 1-3 against the ticket's mathematics and the band texts)
Auditor file `audit_check.lean` (imports the two new modules; `T2479_MeanFarg` copied from the check by `awk`, unchanged):
```
example : T2479_MeanFarg := by
  intro d κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t hH hreg hTh hKp hX τ hτ
  obtain ⟨hd, hκ, -, -, hAdm, hm, hs0, hst, ht1, -, hrep, -, -, -, hG, -, -⟩ := hH
  exact meanFar_eventuallyg C μ hd hκ hAdm hm s t hs0 hst ht1 hrep hreg hG hTh hKp hX τ hτ
example : ∀ {d} {sz : Sizes d} (C : FlowFM sz), 3 ≤ d → STThPropsg C → ∃ C₀, 0 < C₀ ∧ ∀ᶠ n in atTop, ... (1a text) :=
  fun C hd hTh => cltMom1_weight_a1g C hd hTh
-> both compile (exit 0 above)
```
Statement extraction (`python3 -I stm.py`, 20 public declarations; full text in the prove report b4, re-extracted here and read):
- **T1 weights.** `cltMom1_weight_a1g`: `lam² ‖STThg C n σ₀ σ₁ t a b‖ ≤ C₀(1+2^{d-1})/(|a-b|_∞^{d-2}+1)` for `σ 0 ≠ σ 1`, `0 ≤ t < 1`,
  regime `lam²/L² ≤ 1-t`; `cltMom1_weight_a2g`: BD1 weight `≤ C₀ d w/(|a₂-b₁|_∞^{d-1}+1)` under `2dw ≤ ρ < |a₂-b₁|`, `|b₁-b₂| ≤ w`.
  Exponents `d-2`, `d-1` as the ticket and band (`CltMoments1:938, 973`). Only premise `STThPropsg C` (+`3 ≤ d`). Difference from
  band: constant `∃ C₀, ∀ᶠ n` from the pin instead of uniform in `(L, g ≤ Λ)` — candidate `T2479a`.
- **T2 vocabulary.** `Zg, flucg, offg, BYg, DomHypg, IsoHypg, rhsg` are the band `CltMoments2:84-160` with the substitutions the ticket
  lists (`STThg` for `Theta`, `C.L - C.K` for `STLKM`, `STcltBg/STcltXg`, `μ` for `seqP`, `etaOf (C.m n)` for `etaT`, `C.K` for
  `STKloop`): side-by-side read, no other change. Compiled check `Zg (bandFM …) = CltMom2.Z szCL …` (`CltMoments2G:650`).
- **T3 moment layer.** `decompg`, `norm_stcltBg_le` take the envelope `cltMom2G_LEnv C n s` (explicit def: measurability and
  `‖C.L‖ ≤ η⁻²`), supplied for every `u < 1` from `CltRepg` + `κ ≤ Im (C.m n)` by `cltMom2G_lenv_of_rep` (ticket: "loop envelope
  comes from `CltRepg` and `κ ≤ Im (C.m n)`"). `weightg_le` = band `WeightStmt` with `|E| ≤ 2, κ ≤ Im mE, lam ≤ Λ` replaced by
  `STThPropsg`. `moment_fixedg` takes the weight bound as an explicit hypothesis `hW` at `M₀` (conclusion at `4^d M₀`) instead of
  the band's internal `∃ M`; `hW` is exactly `weightg_le`'s conclusion at one `n` (discharged so in example 3d). `tail_eventuallyg`
  = band `TailStmt` with `STCltIsoConcl` -> `STCltIsoConclgL C μ s`, `|E n|<2 ∧ κ ≤ Im mE` -> `κ ≤ Im (C.m n)`, no `lam ≤ Λ`.
  Quantifier order (`∃ M, ∀ p ≥ 1, ∀ D > 0, ∀ᶠ n, ∀ σ mixed, ∀ a …`) identical to the band.
- **T4 mean part.** `meanFar_eventuallyg`: `∀ τ > 0, ∀ᶠ n, ∀ σ (σ0≠σ1), ∀ a, ‖∫ STfFarg‖ ≤ N^τ · A^{-6/5}/(|a₀-a₁|^{d-2}+1)`;
  premises are 7 fields of `HCltOf` + `STReg5I`, `STThPropsg`, `STKpropsg`, `STExpInvgL` (a weakening of the proposal's premise
  block; the typed example above shows `T2479_MeanFarg` follows). Energy only through `κ ≤ Im (C.m n)` — candidate `T2479b`.
Verdict on statements: no hypothesis dropped from the mathematics, no special case passed off as general, mixed-charge range as fixed by the ticket.

## 4. Hidden hypotheses, vacuity, cycles; greps of target 10 (statement text of the 20 public declarations, `stm.out`)
```
X1-C1 pattern hits: 0     UBA-C1 (gK|withLam|lam0|BAflowLam0|seqHflowBA): 0     TN-C4 STGridRepNgL (whole files): 0 / 0
X1-C4 (def|abbrev|structure) of the 10 CltGen pin names in new files: 0
U-C4 whole-file Ring.inverse|Matrix.of|Theta d: CltMoments2G:210, MeanFarG:72 (Matrix.of inside the measurability proof of
  H₀ + seqHflow in *_lenv_of_rep; no def body); CltMoments2G:619-622, MeanFarG:749-805 (Theta d in the private band producers
  of the instance sections, band lines)
```
- No structure is introduced; the new `def`s are plain Props/values with all content in the signature. `cltMom2G_LEnv` /
  `meanFarG_LEnv` are explicit hypotheses, produced by the public `*_lenv_of_rep` (not hidden). `meanFarG_KInv` is read only by privates.
- No cycle: new modules import only `CltMoments2`/`MeanFar` + `CltGen`; 0 importers other than `RBM3D.lean`; no `BA/*`, `IniTerm*` import.
- Dependencies are merged: `STThPropsg`, `STKpropsg`, `STExpInvgL`, `STCltIsoConclgL`, `CltRepg`, `STGdecayWgL`, `STReg5I` from
  `Chain/CltGen` / band files on `main`; `stCltIsogL_holds`, `stExpInvgL_band`, `cltGood_hCltOf_szCL` merged (X1a).
- Name clash: `git grep` of the 20 names + stems: main 0, t/T2478 0, t/T2473 0, t/T2474 0.
- External-hypothesis limit check: no new external hypothesis; the pins read are X1a's (their checks are in T2455).

## 5. Compiled nonempty instances (`d = 3`, `szCL`, `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL`, `tCL`; all compile, §2)
| target | location | data / hypotheses left open |
|---|---|---|
| 1a, 1b | `CltMoments2G:644, 647` | `STThPropsg` closed by private band producer `cltMom2G_chk_Th0`; none open |
| 2 | `CltMoments2G:650` | `Zg` at band = band `CltMom2.Z`, every `n, s, t, σ, a, β` |
| 3a, 3b | `CltMoments2G:660, 672` | `n = 0`, `sCL 0`, `tCL 0`; envelope from `cltGood`-`HCltOf`; open: `STLocalEntryUgL`, `STGdecayWgL` |
| 3c | `CltMoments2G:680` | as 1a |
| 3d | `CltMoments2G:684` | `∃ n ≥ 34`, `σ = (+,-)`, `p = 1`, `q₁ = 1`, `εf = W^{-1}` (from `stCltIsogL_holds`); open: Step-2 pins |
| 3e | `CltMoments2G:712` | `κ = 1/2`, `STCltIsoConclgL` by `stCltIsogL_holds`; open: Step-2 pins |
| 4 | `MeanFarG:838` | `κ=1/2, 𝔠=1/6, 𝔡=1/10, Cd=1, τ=1/2`; `szCL_admissible`, `κ ≤ Im m`, `0 ≤ sCL < tCL < 1`, `cltRepg_band`, `szCL_reg5I`, `STThPropsg`/`STKpropsg` by private band producers, `stExpInvgL_band`; open: `STGdecayWgL` only |
No `N = 0`, empty index, collapsed window or `False` premise; the index set at `szCL` is nonempty (`szCL_cltFar_index_nonempty`, X1a).
The only open hypotheses are the other gate's Step-2 pins `STLocalEntryUgL`, `STGdecayWgL` (allowed, §4 step 2).

## 6. Paper deltas
Report (d) proposes `T2479a` (constants of weights/mean part from the pin `STThPropsg`, eventual in `n`, not from `(d, Λ, κ)`)
and `T2479b` (`κ ≤ Im (C.m n)` replaces `|E| ≤ 2 - κ`). These cover the differences found in §3. The mixed-charge restriction and the
carrier propagator are the ticket's fixed design (X1-C2, `STThPropsg` range). `moment_fixedg`'s `hW` is a Lean-internal
restructuring of the band statement (no paper statement changes). Coverage complete.

## 7. Observations (no effect on statements, instances, build, axioms or delta coverage)
- O-a. Registry: 5 `owedProps` lines vs the ticket's expected 2; the extra `STCltIsoConclgL`, `CltMom2.DomHypg`, `CltMom2.IsoHypg`
  are binders of new public theorems; whole build and registry pass. Dispatcher may prune at X1b-2.
- O-b. Target-7 producers exist here as privates (`cltMom2G_chk_Th`, `meanFarG_chk_Th`, `meanFarG_chk_K`); X1b-2 will duplicate them
  publicly (prove report O1, a dispatcher choice, not a defect of this row).
- O-c. `cltMom2G_LEnv`/`meanFarG_LEnv` and the two `*_lenv_of_rep` are textual duplicates (files do not import each other);
  `meanFarG_lenv_of_rep` (helper, not a target) has no example of its own; it is used in `meanFar_eventuallyg`'s proof.
- O-d. 28 warnings in the new files, all line length. `f_sem` max 0.283 (`MeanFar:1977-2082`) < 0.30 (prove b10).

## Verdict
| target | verdict |
|---|---|
| 1 `cltMom1_weight_a1g`, `cltMom1_weight_a2g` | PASS |
| 2 vocabulary `CltMom2.Zg … rhsg` | PASS |
| 3 `cltMom2_decompg`, `_norm_stcltBg_le`, `_weightg_le`, `_moment_fixedg`, `_tail_eventuallyg` | PASS |
| 4 `meanFar_eventuallyg` (`T2479_MeanFarg` follows, typed example) | PASS |
| 5-9 | not in this row (X1b-2, `t/T2479b`, pre-signed split) |
Overall: **PASS** for X1b-1. No dispatcher sign-off needed for this verdict; X1b-2 may start stacked on `t/T2479` per the ticket.
