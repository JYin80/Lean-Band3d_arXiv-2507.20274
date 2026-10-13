Auditor model: claude-opus-5-5

# T2493 audit, round 1 (U5d-1: `RBM3D/BA/Step5IIIWalk.lean`, targets 1-5 and the per-time layer)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2493-audit1`, detached at `t/T2493` = b430f3c2 (merge-base with main 5fbefff2). Written `date -u` = Tue Oct 13 07:57:54 UTC 2026.
Scope: the pre-signed split was confirmed in section (a) row 17 (central 3050 > 1950). Only U5d-1 is delivered here; targets 6-8(c) (`Step5IIIWalk2`) belong to U5d-2 on `t/T2493b` and are not audited.

## 1. Diff scope
```
$ git diff --stat main...t/T2493
 RBM3D.lean                 |    1 +
 RBM3D/BA/Step5IIIWalk.lean | 1799 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    1 -
$ git diff main...t/T2493 -- RBM3D.lean RBM3D/Test/Axioms.lean     (abridged to the changed lines)
+import RBM3D.BA.Step5IIIWalk                       (after the last import line; #assert_rbm_axioms stays last)
-   `RBM.BA.BAStep5IIIEMatrix, -- the matrix part of the U5b bundle ...   (owedProps; ticket note (6), registry (i))
```
All three are sole writable files (`Test/Axioms.lean` for note (6) only). No merged file edited; no frozen signature touched.

## 2. Statements against the pins (Lean-checked, not text-diffed)
Auditor file `scratchpad/T2493/audchk.lean`: `import RBM3D.BA.Step5IIIWalk`, then the check file's lines 177-266 (the seven `T2493_*` pins verbatim), then:
```
example : T2493_EMatrixLevel 3 := baStep5III_EMatrix_level 3
example (d : ℕ) : T2493_EMatrixLevel d := baStep5III_EMatrix_level d
example : T2493_GoodBundle := baStep5IIIGood_bundle
example (d : ℕ) : T2493_JsharpMeas d := baStep5IIIJsharp_measurable d
example (d : ℕ) : T2493_GoodMeas d := baStep5III_goodMeas d
example (d : ℕ) : T2493_CrudeQV d := baStep5III_crudeQV d
example : T2493_WalkLevel := baStep5III_walkLevel
example (d : ℕ) : T2493_Duhamel d := baStep5III_duhamel d
#print axioms ... (seven names)
$ cd .../T2493-audit1 && lake env lean $S/audchk.lean
'RBM.BA.baStep5III_EMatrix_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIGood_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIJsharp_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_goodMeas' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_crudeQV' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_walkLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT 0   (one unused-variable lint warning on the auditor's own trivial example; no errors)
```
All seven targets elaborate as their pins, with the pins copied verbatim from the check file (the prover's whitespace diff in (b) agrees: ALL IDENTICAL).
Per-target reading against the ticket's mathematics:
- T1 (a) `D' ≤ D`, the matrix part at `(D, J)` gives it at `(D', J♯(D'))`. The conclusion head is `BAStep5IIIEMatrix` (registry (i)). Every `d`. (b) The quantifier order is `τ' D₁ θ` and then `∀ᶠ n`, `∀ u`, `∃ G`, `seqP (sz.withLam 0) Gᶜ ≤ N^{-D₁}`, as U5c.
- T2 `J♯` is measurable in `H`. The matrix-part set at `J♯(H)` is measurable. Both hold for every `d` and every parameter, with no hypotheses.
- T3 (H2): `0<κ`, `0<ε`, `BAFlow`, `t ≤ t₀`, `∀ᶠ n`, `u ≤ t n`, Hermitian `H`. Conclusion `‖STeeMg‖ ≤ 2N(16N)^6` (the band's `Y`).
- T4: fixed parameters `Dst τ' θ Cd ε₀` come before `∀ᶠ n`; then `ε₀ ≤ 1/2`, the floor premise is eventual, `D_u = PfStep5Grid_level W Dst u`, `Λ = K₀ = N^{τ'}`. Both bundle parts hold at `D_u`.
- T5: `∃ Cdu > 0` comes before `(sz, lam0, E, n, κ)`. `BAReal` replaces `|E| ≤ 2`. The kernel is `Step2Gen_UN (baFM ..)`. Exponent 7. The martingale is the increment sum `Mart(j+1) − Mart j` under `U_{u_j,u_k}`.
- Ticket answer (4) accepts T5 as an equivalent BA restatement of the band `pfStep5Grid_duhamel`. Section (a) row 13 fixed `Cdu = 64` and exponent 7, and the proof uses them (`pfStep5Grid_abs`).

## 3. Vacuity, hidden hypotheses, cycles
```
$ grep -cE "^(structure|class) " RBM3D/BA/Step5IIIWalk.lean            -> 0
$ grep -nE '(def|abbrev|structure) (BAStep5IIIEScalar|BAStep5IIIEMatrix|BAStep5IIIJsharp|BAStep5IIIGood|STLmaxUgL|STLKUgL|STGridRepNAtgL)' -> 0
$ grep -nE "^import" (new file)  -> BA/Step5IIIGood2, BA/Step5IIIEdet2, BA/Step5IIIKer2, BA/GridRepTailBA, BA/Step2IterBA,
                                    Chain/Step2CloseGen, Chain/Step2EventsGenTw, Induction/PfStep5   (all merged on main)
```
- The premises of T1-T5 are merged `def`s only: `BAStep5IIIEMatrix`, `BAStep5IIIGood`, `BAFlow`, `STReg5III`, `BAReal`, `BAflowT0`. No new structure carries fields.
- `BAStep5IIIGood` (T1 (b)) is concluded by the public `Step5IIIWalk_good_of_flow` (l.102). It is `baStep5IIIGoodThm_holds` re-read, with the premises of `BAStep5IIIGoodThm`. The four carrier predicates `STAvgUgL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL` stay hypotheses: they are the pins of Steps 2-4.
- No cycle: the file imports only merged modules, and its only importer is `RBM3D.lean`.
- No external hypothesis is introduced.
- The (a′)2 fix inlines `STTailtoTailConclgL` into `hTT` of `Step5IIIWalk_ugenSum`/`_assemble`. Those are per-time-layer helpers, not targets. The last instance feeds `hTT` from the merged `baStep5IIIKernel_at_flow`, so the hypothesis is satisfiable.

## 4. Compiled nonempty instances (section 11, l.1521-1799; all compile in the module build below)
All instances use `sz0`, `zSeq`, `flow_sz0`, `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`, `s≡1/10 < t≡1/2 ≤ t₀` (`half_lt_t0`), `Cd=1`.

| target | line | data | deterministic premises discharged | hypotheses left |
|---|---|---|---|---|
| T1 (a), (b) | 1546 | `D=40`, then `D'=30`, `τ'=D₁=1`, `θ=1/10`; produces `∃ n u ω` with `ω ∈ G` | flow, regime `Step5IIIGood_reg_sz0`, `t≤t₀`, `0<D`; `G ≠ ∅` from `seqP Gᶜ ≤ N^{-1} < 1` (`Step5IIIWalk_good_nonempty`, `N ≥ 2` eventually) | `STAvgUgL`, `STLmaxUgL`, `STLKUgL`, `STGdecayWgL` (other gates' pins) |
| T2 (a) | 1572, 1577 | `n=1` (`L=8`, `W=1024`), `u=1/2`, `D=40`; plus the stopping set `{J♯ < W^{1/100}}` | none needed | none |
| T2 (b) | 1583 | `n=1`, `u=1/2`, `D=40`, `Λ=K₀=1`, `θ=1/10`, `Cd=1` | none needed | none |
| T3 | 1590 | `t≡1/2` | `0<κ`, `0<ε`, flow, `t≤t₀` | none |
| T4 | 1608 | `D*=46`, `τ'=1/100`, `θ=1/10`, `ε₀=1/100` | flow, `0≤s<t`, regime, `0≤τ'`, `ε₀≤1/2`, floor (`Step5IIIWalk_sz0_floor46` from `Step5IIIGood2_sz0_floor`) | none |
| T5 | 1642 | `n=1`, `σ=(+,−)`, `k=2`, `Δ=1/10`, `u_j=1/10+j/10` (`u_2=3/10<1`), `A_j ≡ j+1 ≠ 0`, `M=3`, `R=0`, `F` read from the increments | `0<κ`, `BAReal` (from `BAflow_real`), `0≤Δ`, `0≤u₀`, grid, `u_k<1`, `‖A‖≤M`, `‖Rem‖≤R`, the decomposition (proved) | none |

The per-time layer is also instantiated: l.1694 (per-time bounds on the good event), 1734 (a priori bound), 1743 (`xx`), 1758 (loss budget), 1768 (`ugenSum`, with `hTT` from `baStep5IIIKernel_at_flow`).
No instance uses `N = 0`, an empty index set, a collapsed window, a `False` premise, or an astronomically large witness. The `∀ᶠ` conclusions are kept as `∀ᶠ`.

## 5. Build, axioms, hygiene
```
$ lake build RBM3D.BA.Step5IIIWalk            (audit worktree)
Build completed successfully (4105 jobs).   EXIT 0
  errors: 0; warnings in RBM3D/BA/Step5IIIWalk.lean: 16, all "This line exceeds the 100 character limit"
$ lake build                                  (whole library, branch root imports, registry check)
info: RBM3D.lean:588:0: axiom audit: 14712 theorems, 4566 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4356 jobs).   EXIT 0
$ lake env lean docs/tickets/checks/T2493-check.lean     (on the branch)   -> 0 errors, EXIT 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/BA/Step5IIIWalk.lean | wc -l   -> 0
```
- Axioms of the seven targets: see §2. All seven show exactly `[propext, Classical.choice, Quot.sound]`.
- The full build's `#assert_rbm_axioms` passes with the `owedProps` line `BAStep5IIIEMatrix` removed and no new registry line. So the scan finds no unregistered premise: T1 (a) concludes `BAStep5IIIEMatrix` and `Step5IIIWalk_good_of_flow` concludes `BAStep5IIIGood`.
- Ticket greps on the new file:
  - C1: 0 hits.
  - `STGridRepNgL|\|E\||norm_mE|mSigma|SB d|E2Hyp|gexRHS|STGMMg|≤ A \*`: 0 hits.
  - `withLam` outside `seqP/pathP (sz.withLam 0)` (and the `SizesInst.sz0` form): 0 hits.
- Every public declaration (32) carries a pinned name or the stem `Step5IIIWalk_`, which satisfies §3 (E).
- `open private` reaches only band files of this repository (`PfStep5Grid`, `PfStep5`). Nothing is ported from RBM1D/RBM2D.

## 6. Paper deltas
- T5 is the discrete grid Duhamel form with the deterministic remainder `Cdu(1−u_k)^{-7}(R+ΔM)`. It is the BA analogue of D543 (`docs/paper-deltas.md:1502`, band: `64(1−u_k)^{-7}(R+ΔM)`, time-dependent level `D_u`) and of D162/D243 (grid telescoping, not the continuous `(int_K-L_ST)`).
- T4's `D_u` is D543's level.
- Ticket answer (4) calls T5 an equivalent restatement.
- T2 (measurability) and T3 (a crude a-priori bound) are Lean-only auxiliary facts, as in the band. The paper has no corresponding statement.
- T1 is a definitional repackaging of U5c.
- The prover proposes no new candidate. The pending T2459a-f (numbered at row merge, `paper-deltas.md:1598`) cover the omitted BA argument.
- Coverage: adequate.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The new file has 16 lines over 100 characters (linter warnings only).
- O2. `git merge-tree main t/T2493` reports a content conflict in `RBM3D.lean` only. Main has moved since 5fbefff2 and the conflict is in the import-line union. Under rule (A) step 4 the hub adds `import RBM3D.BA.Step5IIIWalk` itself. `Test/Axioms.lean` merges cleanly, and main still has the `BAStep5IIIEMatrix` line at :240.
- O3. The T5 instance takes `Rem = Mart = 0`, `R = 0`. It is nondegenerate (`A ≠ 0`, `k = 2`, `Δ > 0`, right side `Cdu·(10/7)^7·3/10 > 0`), but the remainder and martingale slots are exercised only at zero.
- O4. Section (a) row 7 flagged the ticket's `θ = ε₀/(8d(Cd+1))` as giving equality in `W^{2θ'} < W^{ε₀/4}`. (a′)4 replaces it by the `Step5IIIWalk_hQ` budget (`2θ(Cd+1) ≤ τ/4`). This concerns U5d-2's closure. It is no defect of targets 1-5, and the U5d-2 audit must check it.

## Verdict
- T1 (a) `baStep5III_EMatrix_level`: PASS
- T1 (b) `baStep5IIIGood_bundle`: PASS
- T2 (a) `baStep5IIIJsharp_measurable`: PASS
- T2 (b) `baStep5III_goodMeas`: PASS
- T3 `baStep5III_crudeQV`: PASS
- T4 `baStep5III_walkLevel`: PASS
- T5 `baStep5III_duhamel`: PASS
- T8 (a), (b) instances of targets 1-5: PASS
- Targets 6, 7, 8 (c): not in this delivery (U5d-2, `t/T2493b`, after the short REQ). They are not audited here.

Overall U5d-1: **PASS**. No dispatcher sign-off is needed for U5d-1. The seventh-row REQ is already the dispatcher's, per ticket answer (7).
