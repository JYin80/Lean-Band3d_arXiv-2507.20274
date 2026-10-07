Auditor model: claude-opus-5-5

# T2309 audit (UN-24, `Universality/UnivMain`), round 1 — Wed Oct  7 06:14:00 UTC 2026

Branch `t/T2309` at 34f43ca; main at 1d19466. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2309-audit1` (detached, build cache cloned).

## 1. Diff scope (sole writable files)

```
$ git diff --stat main...t/T2309
 RBM3D/Test/Axioms.lean           |   3 -
 RBM3D/Universality/UnivMain.lean | 690 +++++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2309 -- RBM3D/Test/Axioms.lean   (only '-' lines)
-   `RBM.Univ.UNUnivMainRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNClaimRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNClaimRowk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
```
Exactly the two sole writable files; registry = exactly the three ticketed deletions, nothing added. No merged file or frozen signature touched.

## 2. Statements against the pin (check file `docs/tickets/checks/T2309-check.lean`, sections 2-3)

Script: the check file's sections 2-3 (the `T2309_*` Prop defs, verbatim) plus `import RBM3D.Universality.UnivMain` and:
```
example : T2309_unClaim417C_of_rows := @RBM.Univ.unClaim417C_of_rows
example : T2309_unClaimRowk := @RBM.Univ.unClaimRowk
example : T2309_unClaimRow := @RBM.Univ.unClaimRow
example : T2309_unDens_rho_bounds := @RBM.Univ.unDens_rho_bounds
example : T2309_univMain_transfer := @RBM.Univ.univMain_transfer
example : T2309_univMainRow := @RBM.Univ.univMainRow
example : T2309_unCore'_holds := @RBM.Univ.unCore'_holds
example : T2309_inst_univMain_band_zero := RBM.Univ.UnivMainInst.inst_univMain_band_zero
example : T2309_inst_claim417_core := RBM.Univ.UnivMainInst.inst_claim417_core
example : T2309_inst_claimAll_band_zero := RBM.Univ.UnivMainInst.inst_claimAll_band_zero
example : T2309_inst_rho_bounds_zero := RBM.Univ.UnivMainInst.inst_rho_bounds_zero
$ lake env lean <scratch>/T2309-auditcheck.lean > out.txt; echo lean_exit=$?; grep -c error out.txt
lean_exit=0
0
```
All 7 targets and the 4 pinned instances have exactly the pinned types (definitional check by Lean, no coercion
or restatement). Targets 2, 3, 6, 7 are the merged `Prop`s `UNClaimRowk` (∀ K), `UNClaimRow`, `UNUnivMainRow`,
`UNCore'` by name, so hypotheses, quantifier order (`∃ τ₀, ∀ τU ≤ τ₀, ∀ O` in `UNUnivMainRow`), `c' = 𝔠𝔡/30`,
`C_n' = C_n + C + 1`, windows and dimensions are those of the pins. Target 1 is stated for every `K : UNKind d`
(model-generic, not a band special case).

Public declarations (script):
```
$ grep -nE '^(theorem|def) ' RBM3D/Universality/UnivMain.lean | grep -v private
393:theorem unClaim417C_of_rows {d : ℕ} (K : UNKind d) (sz : Sizes d) (hsize : sz.SizeTendsto)
466:theorem unClaimRowk : ∀ K : ∀ d, UNKind d, UNClaimRowk K := by
476:theorem unClaimRow : UNClaimRow := UNClaimRowk_band.1 (unClaimRowk _)
486:theorem unDens_rho_bounds (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (h : UNDens m E ρ δ) :
509:theorem univMain_transfer {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n k : ℕ)
533:theorem univMainRow : UNUnivMainRow := by
557:theorem unCore'_holds : UNCore' := un_core'_of_univMainRow univMainRow
578-661: inst_nondegenerate, inst_univMain_band_zero, inst_claim417_core, inst_claimAll_band_zero,
         inst_rho_bounds_zero, inst_transfer_band_zero, inst_unClaimRowk_band_zero, inst_core'_band_zero
```
All other declarations are `private` with prefix `UnivMain_` (§3 (E)).
## 3. Hidden hypotheses, vacuity, cycles

- No new structure, no new `def` of a `Prop`: every premise is either a binder of a merged pin or a plain
  inequality (`0 < τU`, `sz.SizeTendsto`).
- Proof of target 6 (lines 533-550) uses only: `hGC` (the pin's own premise `UNGreenCorrAll`), `hClaim`
  (`UNClaimAll`, pin premise), `unApriori_of_trLocal` (merged, from the pin premises `hD`, `hT`),
  `unDens_rho_bounds` (target 4), `univMain_transfer` (target 5). `τ₀ := min τ' (inf'_{range (k+1)} τ0)` is
  chosen before `τU` and `O` (line 543-544): pin order met.
- Target 1 (lines 393-461): `UNEMCTE2k`/`UNJakk`/`UNUywk` at slack `τU/4`, `filter_upwards` with the eventual
  `4 ≤ N^{τU/2}` from `hsize`; constants `B = 4 N^{τU/4} N^{1-c'+Cτ}`, exponent identity by `ring`.
- No cycle: `UnivMain.lean` imports Apriori, GreenCorr, EigenMeasurable, PinsK, GUETranslation, Path.Walk, EMCTE2,
  Uyw (all merged); nothing on main imports it; no `BA/*`, `Graph/*`, `RBM3D` import.
- External hypotheses: none new (UNGreenCorrAll is discharged by the merged `greenCorrAll` in the instances).

Registry pre-check (all 346 root imports of `RBM3D.lean` + `import RBM3D.Universality.UnivMain` + `#assert_rbm_axioms`;
the bare branch root build fails as expected without the new import — the hub adds it at merge):
```
$ lake env lean <scratch>/reg.lean > reg.out; echo reg_exit=$?
reg_exit=0
axiom audit: 8725 theorems, 2867 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
$ grep -nE 'UNUnivMainRow|UNClaimRow|error' reg.out
132:  RBM.Univ.UNClaimRowBA: 4 [no certificate]
```
`UNUnivMainRow`, `UNClaimRow`, `UNClaimRowk` no longer appear as premises; `UNClaimRowBA` stays owed as ticketed.

## 4. Compiled nonempty instances (namespace `RBM.Univ.UnivMainInst`, data `d = 3`, `sz0`: `N(0) = 2^21`)

| target | instance | deterministic hyps discharged | kept (other gates' pins) |
|---|---|---|---|
| 1 `unClaim417C_of_rows` | (b) `inst_claim417_core` (band kind, `E=0`, `nf=2`, `τU=1/4`, `c'=1/1800`, `Cn=C=1`) | `sz0_tendsto`, `0 < 1/4` | `UNEMCTE2k`, `UNJakk`, `UNUywk` |
| 2 `unClaimRowk` | (f) `inst_unClaimRowk_band_zero` | `3 ≤ 3`, `sz0_adm`, `κ=1/2`, bulk `|0| ≤ 3/2` | `UNLocAvgBand`, `UNOUClaims` (row premise via merged `unEMCTE2Rowk_band`, `jakUywRow`) |
| 3 `unClaimRow` | (c) `inst_claimAll_band_zero` | same | `UNLocAvgBand`, `UNOUClaims` |
| 4 `unDens_rho_bounds` | (d) `inst_rho_bounds_zero` | `UNDens` by `un_dens_msc_zero` | none |
| 5 `univMain_transfer` | (e) `inst_transfer_band_zero` (`n=0`, `k=1`, bump) | all | none |
| 6 `univMainRow` | (a) `inst_univMain_band_zero` (`msc`, `E=0`, `ρ=ρ_sc(0)`, `δ=1/2`, `k=1`, bump) | `greenCorrAll`, `sz0_adm`, `UNDens`, `IsTestFun bump` | `UNTrLocal`, `UNClaimAll` |
| 7 `unCore'_holds` | (g) `inst_core'_band_zero` | `greenCorrAll`, `UNDens'`, `|0|<2`, `1 ≤ 1`, bump | `UNL32`, `UNGUELocal`, `UNTrLocal`, `UNNormBound`, `UNClaimAll` |

Nondegeneracy: `inst_nondegenerate` (bump 0 = 1, bump 3 = 0, `sz0.size 0 = 2097152`, `0 < ρ_sc 0`). No `N = 0`, no
empty index, no `False` premise. `UNClaimAll` at `sz0` is itself derived from the owed `UNLocAvgBand`, `UNOUClaims`
by instance (c), so (a)/(g)'s kept premise is not an extra assumption.

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.Universality.UnivMain 2>&1 | grep -Ev '^(✔|⣿)' | tail
ℹ [3410/3410] Built RBM3D.Universality.UnivMain (3.0s)
info: RBM3D/Universality/UnivMain.lean:674:0: 'RBM.Univ.unClaim417C_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:675:0: 'RBM.Univ.unClaimRowk' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:676:0: 'RBM.Univ.unClaimRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:677:0: 'RBM.Univ.unDens_rho_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:678:0: 'RBM.Univ.univMain_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:679:0: 'RBM.Univ.univMainRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:680:0: 'RBM.Univ.unCore'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ...:681-688: the 8 instances, each [propext, Classical.choice, Quot.sound]
Build completed successfully (3410 jobs).
$ lake env lean RBM3D/Universality/UnivMain.lean 2>&1 | grep -E 'error|warning|sorry'; echo exit
exit=0          (fresh elaboration, no stale olean: main has no UnivMain olean)
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/UnivMain.lean; echo forbidden_hits=$?
forbidden_hits=1   (no match)
```
No warnings from `UnivMain.lean` (only pre-existing longLine warnings of merged `Uyw.lean`).

Name clash (`grep -rnw` on main, `RBM3D/` + `RBM3D.lean`): `unClaim417C_of_rows` 0, `unClaimRowk` 0, `unClaimRow` 0,
`unDens_rho_bounds` 0, `univMain_transfer` 0, `univMainRow` 1 (`Pins.lean:562`, a docstring citing RBM2D), `unCore'_holds` 0,
`UnivMainInst` 0.

## 6. Paper deltas

Targets 2, 3, 6, 7 are the merged pins (no new Lean/paper difference). Targets 1, 4, 5 are internal lemmas whose
mathematics is the ticket's (`C_n' = C_n + C + 1`; `c/π ≤ ρ_n ≤ C/π`; law transfer at `t = 0`). The design notes are
proposed as **T2309a** in the prove report (d) (model-generic `UNClaimRowk` → `UNClaimRowBA` follow-up; `UNDens` used
only through the `ρ` range; `UNCore'` unconditional). No `T2309c` needed: no statement difference found by this audit.

## 7. Verdicts

| target | verdict |
|---|---|
| 1 `unClaim417C_of_rows` | PASS |
| 2 `unClaimRowk` | PASS |
| 3 `unClaimRow` | PASS |
| 4 `unDens_rho_bounds` | PASS |
| 5 `univMain_transfer` | PASS |
| 6 `univMainRow` | PASS |
| 7 `unCore'_holds` | PASS |
| 8 instances (a)-(d) (+ (e)-(g)) | PASS |

Observations (no RETURN): the bare `lake build RBM3D` on the branch fails at `#assert_rbm_axioms` (3 unregistered
premises) until the hub adds `import RBM3D.Universality.UnivMain` at merge; with that import it passes (§3).
**Overall: PASS.** No dispatcher sign-off needed.
