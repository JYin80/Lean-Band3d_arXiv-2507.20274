Auditor model: claude-opus-5-5

# T2485 audit, round 1 (U5c: `BA/Step5IIIGood`, `BA/Step5IIIGood2`): Tue Oct 13 04:10:59 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2485-audit1`, detached at `t/T2485` 10152ee4 (merge base 4efcae69).
Split: not triggered. Both files are delivered on `t/T2485` (704 + 198 lines; stop line 2,000), so targets 1-5 are all audited here.
`$S` = scratchpad `T2485/`.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.Step5IIIGood RBM3D.BA.Step5IIIGood2 ; echo rc   (warnings/errors in the two files: grep -c)
Build completed successfully (3900 jobs).
rc=0
       0
$ lake build RBM3D        # branch root (imports at 4efcae69), runs #assert_rbm_axioms
rc=0
Build completed successfully (4337 jobs).
$ lake env lean $S/assert.lean   # import RBM3D + import RBM3D.BA.Step5IIIGood2 + #assert_rbm_axioms; vs assert0 (import RBM3D only)
rc1=0  rc0=0
axiom audit: 14434 theorems, 4535 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff a0 a1:  1c1  < ... 14412 theorems, 4532 definitions ...  > ... 14434 theorems, 4535 definitions ...   (no new premise line, no error)
$ #print axioms (in $S/audit_pins.lean)
'RBM.BA.baStep5IIIJsharp_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_matrix_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIGoodThm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_scalar_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5IIIGood_reg_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5IIIGood2_sz0_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nwE 'sorry|admit|native_decide|axiom' <two files>; echo rc        ->  rc=1 (0 hits)
$ git diff --stat main...t/T2485
 RBM3D/BA/Step5IIIGood.lean  | 704 ++++
 RBM3D/BA/Step5IIIGood2.lean | 198 ++++
 2 files changed, 902 insertions(+)
$ git grep -lE 'import RBM3D\.BA\.Step5IIIGood' -- RBM3D RBM3D.lean
RBM3D/BA/Step5IIIGood2.lean          (the named second file of this ticket; no other importer)
```
No merged file is edited, so no frozen signature is touched. `RBM3D.lean` and `Test/Axioms.lean` are unchanged: the hub adds the two imports at merge, and the premise scan shows no new line.

## 2. Statements against the pins (Lean, by elaboration)
`$S/audit_pins.lean` = the imports and Part 2 of `docs/tickets/checks/T2485-check.lean`, plus `import RBM3D.BA.Step5IIIGood2`, plus these auditor lines:
```
example : ∀ d, T2485_JsharpSpec d := baStep5IIIJsharp_spec
example : ∀ d, T2485_MatrixLevel d := baStep5III_matrix_level
example : T2485_BAGoodThm := baStep5IIIGoodThm_holds
example : T2485_ScalarFlow := baStep5III_scalar_flow
example : T2485_BAGoodThm = BAStep5IIIGoodThm := rfl
example (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ) : T2485_BAGood sz z s t D Cd = BAStep5IIIGood sz z s t D Cd := rfl
$ lake env lean $S/audit_pins.lean 2>&1 | grep -v '^warning\|^Note\|^$'; echo rc   -> (only the #print axioms lines above) rc=0
$ lake env lean $S/audit_neg.lean     # negative control: `example : T2485_ScalarFlow := baStep5III_matrix_level 3`
audit_neg.lean:180:30: error: Type mismatch
```
Each target is therefore its binding `T2485_*` pin up to definitional unfolding. `BAStep5IIIJsharp` is the inline `J♯` of the pins (by `rfl` above), and `(((3:ℕ):ℝ) * (Cd+1))` in (vi) is the pin's `d * (Cd+1)` at `d = 3`.
The pin carries the probe corrections of note (2) (a)-(d): merged `STLmaxUgL`/`STLKUgL`; `0 < ε`, `0 < 𝔡`, `0 < Cd`; no `STKboundgL`. The prover's script diff against probe `:170/:186/:191` agrees (prove report (b), (A)-(D)).
The Lean statement equals the check, so I did not diff it against the probe again.

The bundle copies against T2482's frozen text (whitespace-normalised text compare, names canonicalised; `$S/bodydiff.py`):
```
T2482_BAScalar == Step5IIIGood2_Scalar: True
T2482_BAMatrix == Step5IIIGood2_Matrix: True
T2482_BAEdet == Step5IIIGood2_Edet[EdetConcl inlined]: True
T2485_BAMatrix == Step5IIIGood_Mat: True
T2482_BAScalar == T2485_BAScalar: True
T2482_BAMatrix == T2485_BAMatrix: True
```
`BA/Step5IIIEdet` is not on `main` (`ls RBM3D/BA/Step5IIIEdet*`: no match; T2482 state `blocked`). The inline copy is the form the ticket requires, and the bridge goes to U5d (answer (1)).

## 3. Hypotheses, vacuity, cycles
- Target 1 (`baStep5IIIJsharp_spec`, every `d`): no hypotheses. `STtailTD > 0` is proved (`Step5IIIGood_tail_pos`).
- Target 2 (`baStep5III_matrix_level`, every `d`): its only hypotheses are `D' ≤ D` and the matrix part. Hermitian, (ii), (iv) and (v) pass through unchanged; (iii) and (vi) use `W^{-D} ≤ W^{-D'}`; (i) is target 1 at `D'`.
- Target 3 (`baStep5IIIGoodThm_holds : BAStep5IIIGoodThm`):
  - Hypotheses are `0<κ, 0<ε, 0<𝔡, 0<Cd`, the merged `BAFlow`, `0 ≤ s < t ≤ BAflowT0`, and the merged `STReg5III` (`∀ n, lam² ≤ 1 - t n`, `Step5Pins:58`).
  - It also takes the four carrier predicates `STAvgUgL`, `STLmaxUgL`, `STLKUgL` (`Step2Gen:491`, `Step34Gen:58/65`) and `STGdecayWgL` (`Step2Gen:503`). They are taken exactly at `(baFMz sz z, seqP (sz.withLam 0), s, t[, Cd])`.
  - They match the premises `STStep2ConclgL … s t Cd` (`STAvgUgL ∧ STGdecayWgL` are its conjuncts 2-3) and the `STLmaxUgL`/`STLKUgL` readings of `STIngR5gL` (`Step5Gen:191-205`). Their owners are T1/T1-BA and U3-BA, and the premise scan registers them unchanged.
  - No hypothesis is a new structure field. `STKboundgL`, the far field and `𝒦^{(1)}` come from the merged `baKbound_holds`, `baEMn2ExpHK` and `baKsol_one`, used by name (proof lines 453, 467, 471).
  - No cycle: the files import only merged modules.
- Target 4 (`baStep5III_scalar_flow`): its hypotheses are `BAFlow`, `0 ≤ s < t`, `STReg5III`, `0 ≤ τ'` and the eventual floor `(L³W¹⁸)² ≤ W^D`, exactly as pinned. It uses no Steps 2-4 input.
- External-hypothesis limit check: the four predicates are not new in this ticket (they are other gates' pins, already registered). The 1a still checked `STAvgUgL`/`STLmaxUgL` (k=2) numerically at `u = 0` (prove report (ii), `ext_limit.py`).
- No C1/forbidden input. The ticket greps on the two files:
```
C1 (BAK_le_small|…|STDecayStronggL): rc=1 (0)   statement words (STGridRepNgL|\|E\||…|≤ A \*): rc=1 (0)
withLam outside seqP ((sz|SizesInst.sz0).withLam 0): rc=1 (0)  [withLam occurrences: Good2 5, Good 17]
X1-C4 (def|abbrev|structure) BAStep5IIIE*/STLmaxUgL/STLKUgL: rc=1 (0)   R1/Step 1 (lam0_le_lam|baStep1): rc=1 (0)
```
- Rule (E): every helper outside the pinned names carries the stem `Step5IIIGood_`/`Step5IIIGood2_` (decl grep: 17 stem theorems, 5 `private def` copies). The pinned names are as in the ticket.

## 4. Compiled nonempty instances (all in the files, all built above)
| target | where | data | deterministic premises | left as hypotheses |
|---|---|---|---|---|
| 3 | `Step5IIIGood.lean:631` | `sz0`, `zSeq`, `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`, `s≡1/10<t≡1/2`, `D=40`, `Cd=1` | `flow_sz0`, `0≤s`, `s<t`, `t ≤ T0` (`half_lt_t0`), `STReg5III` (`Step5IIIGood_reg_sz0`), positivity | the 4 Steps 2-4 predicates |
| 1 | `Step5IIIGood.lean:641` | `n=1` (`L=8`, `W=1024`), `u=1/2`, `H=0`, `D=30` | none needed | none |
| 2 | `Step5IIIGood.lean:671` | target 3's event at `τ'=D₁=1`, `θ=1/10`, `u=1/2`; a sample `ω ∈ G` (`G ≠ ∅` from `P(Gᶜ) ≤ N⁻¹ < 1`, `N ≥ 2`); `D=40 → D'=30` | the matrix premise is discharged by target 3 | the 4 Steps 2-4 predicates |
| 4 | `Step5IIIGood2.lean:154` | `sz0`, flow as above, `D=40`, any `τ' ≥ 0` | the floor `(L³W¹⁸)² ≤ W⁴⁰` for every `n` (`Step5IIIGood2_sz0_floor`), regime, flow | none |
| 5(b) | `Step5IIIGood2.lean:165` | composed: targets 3 + 4 on `G ∩ {J♯ ≤ W^{1/2}}`, `θ=1/10`, `Cd=1`, `D=40` | as above; `1 ≤ J♯` from target 1 | the 4 predicates and `Step5IIIGood2_Edet 3` (= `T2482_BAEdet 3`, text-equal above) |
None of these instances is degenerate: no `N = 0`, no `False` premise and no empty index set. The `sz0` widths are `W = (2(n+1))^5` and `L = 4(n+1)`.

## 5. Paper deltas
- The prove report (d) proposes three candidates:
  - T2485a: the good event carries the `J`-free decay (vi), which `3_5:2364-2383` does not list (the design's F2b).
  - T2485b: `0<ε`, `0<𝔡`, `0<Cd`, `0<θ<1` are stated.
  - T2485c: targets 3 and 4 are stated at `d = 3` only.
- T2459a (BA `7_8:2101`, "omit the details") is pending in `docs/paper-deltas.md:1598` and will be numbered at row merge.
- I checked the paper text at `3_5:2364-2383`. The `∃ G` per `u` form and the law `seqP (sz.withLam 0)` are covered by the open item in the report's (d) (the measurable form goes to U5d) and by the merged carrier conventions. I found no uncovered Lean/paper statement difference.

## 6. Observations (not RETURN: no statement, instance, build, axiom or delta effect)
- O1. Target 2's instance is not at `n = 1`, `H = 0` as ticket 5(c) asks. It is composed with target 3 at an `n` taken from `Eventually.exists`, which does not control the `(iii)` window (`(log W)^{3/2} ≤ L/2` only from `n ≥ 57` at `sz0`).
  - This is still nondegenerate: the premise is the full matrix part on a nonempty event, not vacuous.
  - The deviation is stated in the report. The check's 5(c) shape instances target 1 only.
- O2. The files import two modules beyond the ticket's list: `BA/GreenSchur` and `Path/LemDecCalEwG`. Both are merged and declared in the report.
- O3. The prove report does not follow the section order (1)-(7) of the ticket's acceptance list. Its content is present.

## Verdict
- Target 1 `BAStep5IIIJsharp`/`baStep5IIIJsharp_spec`: **PASS**.
- Target 2 `baStep5III_matrix_level`: **PASS**.
- Target 3 `BAStep5IIIGood`/`BAStep5IIIGoodThm`/`baStep5IIIGoodThm_holds`: **PASS**.
- Target 4 `baStep5III_scalar_flow`: **PASS**.
- Target 5 instances (a)-(c): **PASS**.

Ticket T2485: **PASS**. No dispatcher sign-off is needed.
