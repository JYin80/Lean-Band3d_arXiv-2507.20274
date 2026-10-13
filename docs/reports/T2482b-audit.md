Auditor model: claude-opus-5-5
# T2482b audit, round 1 (U5b-2: `RBM3D/BA/Step5IIIEdet2.lean`, targets 6-7, 8 (b)), written Tue Oct 13 05:36:16 UTC 2026
Branch `t/T2482b` at 49b2de45, `main` at 36f8163a; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2482b-audit1` (detached, clean).
Scratch: `.../scratchpad/T2482b/` (`aud.lean`, `aud.out`, `sdiff.py`, `build_mod.out`, `build_full.out`).

## 0. Diff
```
$ git diff --stat main...t/T2482b
 RBM3D.lean                  |    1 +
 RBM3D/BA/Step5IIIEdet2.lean | 1277 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2482Pins.lean  |  395 +++++++++++++
$ git diff --stat t/T2482...t/T2482b -- RBM3D/Probe        (empty: the probe is unchanged since the 1a)
$ git diff main...t/T2482b -- RBM3D.lean
@@ -571,6 +571,7 @@ import RBM3D.BA.Step5IIIGood2
 import RBM3D.BA.Step2CloseBA
+import RBM3D.BA.Step5IIIEdet2
 /-! Hard axiom audit of the whole library: see `RBM3D.Test.Axioms`. -/
 #assert_rbm_axioms
$ grep -rn "Step5IIIEdet2" RBM3D RBM3D.lean | grep import
RBM3D.lean:574:import RBM3D.BA.Step5IIIEdet2
```
All three paths are sole writable files of the ticket. The probe is 1a-only and never merged. No merged file is edited, so no frozen signature changes.

## 1. Statements against the pins (`docs/tickets/checks/T2482-check.lean`)
Text diff (`sdiff.py`, whitespace-normalised; for the bundle names `T2482_BAScalar/BAMatrix -> BAStep5IIIEScalar/Matrix`):
```
$ python3 -I sdiff.py RBM3D/BA/Step5IIIEdet2.lean docs/tickets/checks/T2482-check.lean
BAStep5IIIEdet vs T2482_BAEdet body equal: True
baStep5IIIE_dif conclusion vs T2482_EdetDif conclusion equal: True
baStep5IIIE_sumTheta conclusion vs T2482_SumTheta equal: True
```
Exact-type check. `aud.lean` is check lines 1-226 plus `import RBM3D.BA.Step5IIIEdet2` and the following auditor additions:
```
example : ∀ d, T2482_SumTheta d := fun d => baStep5IIIE_sumTheta d
example : ∀ d, T2482_EdetDif d := fun d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm =>
  baStep5IIIE_dif d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm
example : ∀ d, T2482_BAEdet d := baStep5IIIEdet_holds
example : ∀ d, T2482_EdetLk d := ... baStep5IIIE_lk ...      example : ∀ d, T2482_EdetWG d := ... baStep5IIIE_wG ...
example (d : ℕ) : BAStep5IIIEdet d = T2482_BAEdet d := rfl
example ... : BAStep5IIIEScalar sz n u D Λ K₀ J = T2482_BAScalar sz n u D Λ K₀ J := rfl
example ... : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H = T2482_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H := rfl
example : SizesInst.sz0.L 800 = 3204 ∧ SizesInst.sz0.W 800 = 1602 ^ 5 := ⟨rfl, rfl⟩
$ lake env lean aud.lean > aud.out 2>&1; echo "exit $?"; grep -cE "error" aud.out
exit 0
0
```
Mathematical reading against `3_5:2317-2336` (`res_deccalE_dif`):
- Hypotheses: `3 ≤ d`, `0 < θ`, `0 < Cd`, the scalar and matrix bundles (U5b-1, merged), and the near cut `max_i |a_i - a_i'|_∞ ≤ 2ℓ*`. The paper's cut is `ℓ*`, so Lean's hypothesis is weaker.
- Conclusion: `(1-u)^{-1}(1(r ≤ 6ℓ*) + (W^d|1-u|)^{-1/2} J³) T²(r)`, times `lossE2wG · W^{2θd(Cd+1)} S_θ` in place of `≺`. The paper's indicator is at `4ℓ*`.
- The time `u`, the charges `σ ∈ {±}²` and the blocks `a, a'` are all universally quantified. Dimension `d` is general, `3 ≤ d`.
- Target 6 (a): `∃ C > 0` comes after `d, θ` and before `sz, n`, so the bound is uniform in `L`, as pinned.
- Target 7 is the conjunction of `lk`, `wG` (U5b-1) and `dif`, as pinned. It is not a special case or a conditional adapter of the pin.

## 2. Vacuity, hidden hypotheses, cycles
- The file adds no `structure` or `class`. Its only public `def` is `BAStep5IIIEdet` (a `Prop`, proved by `baStep5IIIEdet_holds`). The premises are the two bundle `def`s of the merged U5b-1, which are `rfl`-equal to the pins (§1).
- No cycle: the file imports only `RBM3D.BA.Step5IIIEdet`, which is merged on main. The `open private` (L41) targets the merged `Path/LemDecCalE` and deletes no `private`.
- Public declarations other than the pinned four are stem-prefixed (`Step5IIIEdet2_`), plus 4 `private`:
```
$ grep -nE "^(theorem|lemma|def|abbrev|structure|class|instance)" RBM3D/BA/Step5IIIEdet2.lean | grep -v "Step5IIIEdet2_"
92:theorem baStep5IIIE_sumTheta ...   1066:theorem baStep5IIIE_dif ...   1153:def BAStep5IIIEdet ...   1171:theorem baStep5IIIEdet_holds ...
```
- External hypothesis: only the matrix bundle `BAStep5IIIEMatrix`, an `owedProps` premise registered at U5b-1. U5c concludes it from its good event (dispatcher answer (4), audit O2). No new premise is introduced (§4).

## 3. Compiled nonempty instances (target 8 (b)), `RBM3D/BA/Step5IIIEdet2.lean` L1178-1275
Instance data: `d = 3`, `sz0`, `n = 800`, `u = 1/2`, `D = 40`, `Λ = K₀ = J = 1`, `θ = 1/10`, `Cd = 1`. The scalar part is discharged by the merged `Step5IIIEdet_scalar_sz0_800`; `0 < θ` and `0 < Cd` by `norm_num`. Window check:
```
$ python3 -I -c "...W=1602**5; L=3204; ls=log(W)**1.5 ..."
L 3204 W 10551460044928032 logW 36.895 l* 224.11 2l* 448.21 6l* 1344.63 L/2 1602 far pt 1500 in (6l*, L/2]: True
```
| example | target | data | open hypotheses |
|---|---|---|---|
| L1185 | 6 (a) | `d = 3`, `θ = 1/10`, all `n` of `sz0` | none |
| L1191 | 6 (a) | general (pin shape) | none |
| L1197 | 6 (b) | `n = 800`, generic `σ, a, a'` | `hmat`, `hnear` (an antecedent of the statement) |
| L1207 | 6 (b) | `n = 800`, `a' = a` | `hmat` only (near cut discharged by `Step5IIIEdet2_near_self`) |
| L1247 | 6 (b) | `σ = (+,-)`, `a = a' = (0, (1500,0,0))`, `r = 1500 > 6ℓ*` (`_pt_dist` by `decide`, `_pt_far`) | `hmat` only |
| L1268 | 7 | `n = 800` | `hmat` only |

- Every deterministic hypothesis is discharged at concrete nondegenerate data: `N > 0`, both indicator regimes reachable (the far point is concrete), and the windows `2ℓ*, 6ℓ* < L/2` are nonempty.
- `hmat` is the matrix bundle, kept as a hypothesis as the ticket prescribes (target 8 (b), audit O2).
- All six examples compile as part of the module build (§4).

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Step5IIIEdet2
✔ [3851/3851] Built RBM3D.BA.Step5IIIEdet2 (12s)
Build completed successfully (3851 jobs).
exit 0      (grep "error|warning: .*Step5IIIEdet2|sorry": no lines)
$ lake build   (full, branch RBM3D.lean with the import line; Tue Oct 13 05:34:18 - 05:35:33 UTC 2026)
info: RBM3D/Test/AuditNegative.lean:30:0: audit reverse test: an unclassified premise is caught (RBM.Audit.Fixture.FakePremise).
info: RBM3D.lean:577:0: axiom audit: 14559 theorems, 4546 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.BAStep5IIIEMatrix: 21 [no certificate]
Build completed successfully (4345 jobs).
exit 0
$ grep "depends on axioms" aud.out
'RBM.BA.baStep5IIIE_sumTheta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIE_dif' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5IIIEdet_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/BA/Step5IIIEdet2.lean; echo rc=$?
rc=1
$ grep -nE 'BAK_le_small|BAMB_upper_small|BAGbEXP|Mbound_AO|W\^\(-eps|BAm_im_lower_window' <file>; echo rc=$?
rc=1
$ grep -nE 'STGridRepNgL|withLam|\|E\||norm_mE|mSigma|SB d|E2Hyp|gexRHS|STGMMg|≤ A \*' <file>; echo rc=$?
rc=1
```
- Registry: `#assert_rbm_axioms` passes and `Test/Axioms.lean` is untouched. The only premise the new theorems read beyond the scalar bundle is `BAStep5IIIEMatrix`, already registered (owed). No unregistered premise.

## 5. Paper deltas
Lean/paper differences in this half, each covered by a pending candidate (numbered at merge, §269 (8)):
| difference | candidate |
|---|---|
| near cut `2ℓ*` (paper `ℓ*`), indicator `6ℓ*` (paper `4ℓ*`) | T2459b (`T2459-design.md:264`) |
| Hilbert-Schmidt loop-level route, the bundle in place of `(Gt_bound_flow)`-`(Eq:L-KGt-flow)` | T2459c (`:265`) |
| factor `W^{2θd(Cd+1)} S_θ` in `dif`; target 6 (a) `S_θ ≤ C(d, θ)` (no paper counterpart) | T2459f (`:268`) |
| cap `J ≤ W^{1/2}` in the scalar bundle (unread) | T2482a (`T2482-audit.md:116`) |
| explicit loss `lossE2wG` in place of `≺` | D437 (`docs/paper-deltas.md:1396`) |
No uncovered difference found.

## 6. Verdicts
| target | verdict |
|---|---|
| 6 (a) `baStep5IIIE_sumTheta` (= `T2482_SumTheta`) | PASS |
| 6 (b) `baStep5IIIE_dif` (= `T2482_EdetDif`) | PASS |
| 7 `BAStep5IIIEdet` (= `T2482_BAEdet`, `rfl`), `baStep5IIIEdet_holds` | PASS |
| 8 (b) instances | PASS |
Overall: **PASS**. No dispatcher sign-off needed.

## 7. Observations (non-blocking)
1. Merge: `git diff main...t/T2482b` includes the probe `RBM3D/Probe/T2482Pins.lean`, which is never merged. Bring in only `RBM3D/BA/Step5IIIEdet2.lean`. The import line `RBM3D.lean:574` is already on the branch, so do not add it a second time under rule (A) 4.
2. Whether `BAStep5IIIEMatrix` holds at the instance (good event ⇒ bundle ⇒ ℰ-bounds) is still unverified. It is U5c's acceptance, as the ticket and dispatcher answer (4) assign.
3. `W(800) ≈ 1.06·10¹⁶` is the scale the floor `(L^dW^{6d})² ≤ W^D` and the nonempty far window `6ℓ* < L/2` require (fixed at the 1a-audit). No bound in the proofs holds only because `W` is large.
