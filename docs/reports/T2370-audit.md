Auditor model: claude-opus-5-5
# T2370 audit (round 1) — Sat Oct 10 07:14:30 UTC 2026

Branch `t/T2370` at `d8bc699`, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2370-audit1` (detached), cwd = that worktree.
`S=<scratchpad>/T2370/audit` holds `AuditT2370.lean` (the check file's Part 1 in `RBM.BA.T2370Check`, then the auditor's equalities) and `Registry*.lean`; nothing in the repository.

## 1. Build, diff, forbidden tokens
```
$ lake build RBM3D.BA.KTreeDeriv 2>&1 | grep -E "error|warning|sorry|Build completed"; echo exit=$?
  (warnings only in other modules: Defs/Tail, Propagator/*, Loop/KLUnique, Path/*, BA/Ward, Induction/*)
Build completed successfully (3741 jobs).
exit=0
$ grep -c KTreeDeriv <build output>
0
$ git diff --stat main...HEAD; git diff main...HEAD --name-only
 RBM3D/BA/KTreeDeriv.lean | 612 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 612 insertions(+)
RBM3D/BA/KTreeDeriv.lean
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option (maxHeartbeats|debug)|@\[implemented_by|unsafe|opaque" RBM3D/BA/KTreeDeriv.lean; echo "forbidden-token hits: $?"
forbidden-token hits: 1        (grep exit 1 = no match)
$ wc -l RBM3D/BA/KTreeDeriv.lean
     612 RBM3D/BA/KTreeDeriv.lean      (stop line 2000)
```
Only the sole writable file is touched; it is new, so no frozen signature is changed. Imports `BA/KCactus, BA/KBase, BA/Ward, Loop/KLTree, Loop/TreeRep`; all on `main` and in `RBM3D.lean` (script below); not `RBM3D`, not `BA/KSolve`.
```
$ for f in BA/KCactus BA/KBase BA/Ward Loop/KLTree Loop/TreeRep BA/MFixedPoint; do ... git cat-file -e main:RBM3D/$f.lean; git show main:RBM3D.lean | grep -c "import RBM3D.${f//\//.}$"; done
RBM3D/BA/KCactus.lean on main: yes; in RBM3D.lean: 1
RBM3D/BA/KBase.lean on main: yes; in RBM3D.lean: 1
RBM3D/BA/Ward.lean on main: yes; in RBM3D.lean: 1
RBM3D/Loop/KLTree.lean on main: yes; in RBM3D.lean: 1
RBM3D/Loop/TreeRep.lean on main: yes; in RBM3D.lean: 1
RBM3D/BA/MFixedPoint.lean on main: yes; in RBM3D.lean: 1
```

## 2. Statements against the pins (target 1)
Textual diff (Part 1 of `docs/tickets/checks/T2370-check.lean` vs section 0 of the file):
```
$ python3 (split check file at namespace/end RBM.BA.T2370Check; split file at "## 0. The pins" .. "## 1."; compare whitespace-normalised)
check Part 1 == file section 0 (whitespace-normalised): True
```
Lean equalities and statement checks (tail of `$S/AuditT2370.lean`):
```
example : @RBM.BA.BASplicedFam = @RBM.BA.T2370Check.BASplicedFam := rfl
example : @RBM.BA.BAGammaDerivRHS = @RBM.BA.T2370Check.BAGammaDerivRHS := rfl
example : @RBM.BA.BAGammaDerivStmt = @RBM.BA.T2370Check.BAGammaDerivStmt := rfl
example : @RBM.BA.BALeafPairsStmt = @RBM.BA.T2370Check.BALeafPairsStmt := rfl
example (d : ℕ) : RBM.BA.T2370Check.BAGammaDerivStmt d := RBM.BA.baGamma_hasDerivAt d
example (d : ℕ) : RBM.BA.T2370Check.BALeafPairsStmt d := RBM.BA.baLeafPairs d
example (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) :
    RBM.BA.T2370Check.BASplicedFam d L W g E m (RBM.BA.BAKcac d L W g E m) := RBM.BA.BAKcac_spliced
```
```
$ lake env lean $S/AuditT2370.lean 2>&1 | cut -c1-200; echo "exit=$?"
MFixedPointInst.P : MFixedPointInst.FlowPt 4 10
BAReal : ℕ → (L : ℕ) → [NeZero L] → ℝ → ℝ → ℝ → ℂ → Prop
'RBM.BA.baGamma_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLeafPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKcac_spliced' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KLloopOf_cutGlueL_leaf' depends on axioms: [propext, Quot.sound]
'RBM.BA.KLloopOf_cutGlueR_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KLloopOf_cutGlueL_wrap' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KLloopOf_cutGlueR_wrap' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2370-check.lean >/dev/null 2>&1; echo "check-file exit=$?"
check-file exit=0
```
Target 1: the four pins are definitionally the check file's (`rfl`). PASS.

Statements of the other targets (from the file):
- `theorem baGamma_hasDerivAt (d : ℕ) : BAGammaDerivStmt d` (line 249), `theorem baLeafPairs (d : ℕ) : BALeafPairsStmt d` (line 463): exactly the pins, no extra hypothesis.
- `theorem BAKcac_spliced : BASplicedFam d L W g E m (BAKcac d L W g E m)` (line 411; `variable (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)`): unconditional.
- `BAKcac` (line 379): `if σ.length = a.length then` length 1 `PropSpin m σ₀`, length 2 `W^{-d}(Θ^{(σ₀σ₁)} M^{(σ₀σ₁)})(a₀,a₁)`, length `≥ 3` `W^{-d(n-1)} Σ_{F∈TSP n} BAGamma … (getD view)`, else `0`. Matches ticket target 4 and `(Kn2sol)` (`1_2:1175`: `W^{-d}(Θ^{(σ₁σ₂)}M^{(σ₁σ₂)})_{a₁a₂}`).
- `KLloopOf_cutGlue{L,R}_{leaf,wrap}` (lines 308-357): the four list facts of target 3, at `(k,l) = (v+1,v+2)` and `(1,n)`; the 2-pieces are `⟨[σ v, σ (v+1)], [a v, x]⟩` and `⟨[σ 0, σ v], [x, a v]⟩` (`v+1 = n`), as the ticket lists. `cutGlueL_leaf` carries no hypothesis on `v` (stronger than needed; correct since `cutGlueL` with `l-1 = v+1` re-inserts at position `v`).

Mathematics vs the ticket (read of the pins, which the auditor does not re-design):
- `treeEqRhsS S K I = W^d Σ_{k∈[1,|I|]} Σ_{l∈(k,|I|]} Σ_{a,b} K(cutGlueL k l a) S_{ab} K(cutGlueR k l b)` (`Loop/KLTree.lean:809-813`); at `S = 1` the `(k,l)` summand is `W^d Σ_x K(cutL x) K(cutR x)`, which is the RHS summand of `BALeafPairsStmt` for `(v+1,v+2)` / `(1,n)`. The `n` pairs are distinct for `n ≥ 3`.
- Chord weight: `BACactusValEdgeW … (Sum.inl J) = (t:ℂ) • BAThetaOf M t (σ i) (σ j)` (`BA/KCactus.lean:459`), whose derivative `Θ + tΘMΘ = Θ·Θ` is the pin's replaced weight; `M`-edges `M(BAMcharge …)` are constant. Leaf weight `BAThetaOf M t (σ v)(σ (v+1))` (`KCactus.lean:452`) = `Θ^{(σ_v,σ_{v+1})}` of `(f-external2)` (`A:556`).
- Unused pin hypotheses: `3 ≤ n` and `KLIsTSP F` in `BAGammaDerivStmt` are not used by the proof (prove report (b) narrative). The pinned statement is therefore weaker than what is proved; not a defect.

## 3. Vacuity, hidden hypotheses, cycles
- Hypotheses of `BAGammaDerivStmt`: `NeZero L/n`, `3 ≤ n`, `BAReal d L g κ E m` (= `BASelf d L g E m ∧ κ ≤ Im m`, `BA/MFixedPoint.lean:432`, merged), `KLIsTSP F`, `0 ≤ t < 1`. Of `BALeafPairsStmt`: `BAReal`, `BASplicedFam … K`, `3 ≤ n`, `0 ≤ t < 1`. No structure carries a hidden hypothesis; `BASplicedFam` is a `Prop` pin discharged unconditionally by `BAKcac_spliced`, and `BAReal` by the merged `MFixedPointInst.P.real` (`FlowPt.real : BAReal 3 L g0 m0.im E m0`, `MFixedPoint.lean:877-893`, a structure field filled by the proved `exists_flowPt`).
- No external hypothesis is introduced (no limit check owed). No cycle: the file imports only merged modules (§1); nothing on `main` imports it.
- Registry pre-check: the prover's full-root run (`import RBM3D` + `import RBM3D.BA.KTreeDeriv` + `#assert_rbm_axioms`) is pasted in the prove report (b) 7 (exit 0, 0 lines naming a new name). The auditor's rerun of that file stopped on an uncached root dependency (`object file …/RBM3D/Graph/LWExpCertS1.olean … does not exist`); `lake build RBM3D` was started and was still compiling `Graph/LWExpCertBS0`, `LWExpCertS1` after more than 30 CPU-minutes each when this report was written. Narrower rerun over the file's own import closure:
```
$ printf 'import RBM3D.Test.Axioms\nimport RBM3D.BA.KTreeDeriv\n\n#assert_rbm_axioms\n' > $S/Registry2.lean; lake env lean $S/Registry2.lean > $S/reg2.txt 2>&1; echo "exit=$?"
exit=1
$ grep -c 'BASplicedFam\|BAGammaDeriv\|BALeafPairs\|KTreeDeriv\|BAKcac\|KLloopOf_cutGlue' $S/reg2.txt
0
```
  The 34 names flagged in the narrow run are existing `RBM.Gauss.Sizes.ST*`, `RBM.Univ.UN*Row`, `RBM.BA.BAProp5..8`, `RBM.Gauss.MomentDom`. They are proved or registered in modules that this closure does not import, so they are artefacts of the narrow import. None is a T2370 name. The hub's full `lake build` at merge runs `#assert_rbm_axioms` over the whole library.

## 4. Compiled nonempty instances (in the file, section 7, lines 525-610; compiled by the build in §1)
- Datum: `P := MFixedPointInst.P : FlowPt 4 10` (merged; `(d,L) = (3,4)`, `g0 > 0`, `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`), `W = 2`, `t = 1/2`, labels distinct blocks.
- Target 2: `baGamma_hasDerivAt 3 4 3 … (le_refl 3) P.real ∅ BAKTreeDeriv_isTSP_empty _ _ (1/2) (by norm_num) (by norm_num)` at `n = 3`, `σ = (+,+,-)`, `a = (0,1,2)·e₁`; and at `n = 4`, `F = {(0,2)}` (`KLisTSP_of_mem_TSP`, `TSP_four`), so the chord term is present. Every hypothesis is discharged.
- Target 3: `baLeafPairs 3 4 2 … P.real (BAKcac 3 4 2 …) BAKcac_spliced 3 (le_refl 3) ![+,+,-] … (1/2) …` and the same at `n = 4`. `BASplicedFam` is discharged by `BAKcac_spliced` (not left as a hypothesis).
- Target 4: `BAKcac_spliced` at the data, plus each of its three clauses applied at `t = 1/2` (length 1, length 2, length 4).
- List identities at `n = 4` (`d = 1`, `L = 3`, `σ = (+,-,+,+)`, `a = (0,1,2,0)`, `x = 1`) by `decide` (lines 583-596), and the four public list facts applied at the same data (599-608).
None is degenerate (no `N = 0`, empty index, collapsed window or `False` premise; `L^d = 64`, `n ∈ {3,4}`).

## 5. Axioms
§2 output: all targets and public list facts use only `propext`, `Classical.choice`, `Quot.sound` (`KLloopOf_cutGlueL_leaf` uses a subset).

## 6. Paper deltas
- `T2370a` (proposed in prove report (d)): `BALeafPairsStmt` has `W : ℕ` with no `0 < W`. At `W^d = 0` both sides vanish (`BAKTreeDeriv_scalar`, `n - 1 ≥ 2`). Covered.
- Chord `tΘ` at `S^{(B)} = I` → existing D633; `n ≥ 3` vs `A:593` `n ≥ 4` → existing D634; the 2-loop closed form is `(Kn2sol)` (`1_2:1175`) itself, no delta.
- The derivative identities (the argument of `A:552-583`; `tree-representation_BA` is the TeX gap of design §3 (a)) are not stated in the TeX; the Lean pins are the dispatcher's, and the prove report (d) records that no other deviation arises. No uncovered Lean/paper statement difference found.

## 7. Observations (no RETURN)
- O1: `BAKcac` is `0` on loops with `σ.length ≠ a.length`. This is a Lean convention, not a paper statement (prove report (d) notes it). K05b must make sure `IsKLoopS` never evaluates `BAKcac` on such indices.
- O2: The pin `BAGammaDerivStmt` carries `3 ≤ n` and `KLIsTSP F`, which the proof does not use. The dispatcher may relax them in a primed successor if K05b needs `n = 2` or general `F`.
- O3: The registry pre-check was not rerun at full-root scope in the audit worktree (§3: uncached `LWExpCert*` modules). The prover's pasted run and the hub's merge build cover it.

## Verdicts
| target | verdict |
|---|---|
| 1. pins `BASplicedFam`, `BAGammaDerivRHS`, `BAGammaDerivStmt`, `BALeafPairsStmt` | PASS (`rfl` vs check file) |
| 2. `baGamma_hasDerivAt : ∀ d, BAGammaDerivStmt d` | PASS |
| 3. `baLeafPairs : ∀ d, BALeafPairsStmt d` + four `KLloopOf_cutGlue*` facts | PASS |
| 4. `BAKcac`, `BAKcac_spliced` | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
