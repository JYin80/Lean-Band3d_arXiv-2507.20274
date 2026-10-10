Auditor model: claude-opus-5-5
# T2374 (BA-K05b) — stage 2 audit, round 1 — Sat Oct 10 08:44:43 UTC 2026

Inputs: ticket `docs/tickets/T2374.md`; check file `docs/tickets/checks/T2374-check.lean`; prove report `docs/reports/T2374-prove.md`
(target-2 pin = lines 70-81, approved by `docs/reports/T2374-1a-audit.md`); branch `t/T2374` at edaa2ec; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2374-audit1` (detached at edaa2ec). Scratch: `$S=…/scratchpad/T2374/aud/`.

## 1. Diff scope
```
$ git diff --name-only main...t/T2374
RBM3D/BA/KTreeRep.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2374 -- RBM3D/Test/Axioms.lean | grep '^[-+]' | cut -c1-60
-   `RBM.BA.BAKsolve, -- existence of the BA `𝒦` on `[0,1)`
$ git show main:RBM3D/Test/Axioms.lean | grep -n "RBM.BA.BAKsolve,"      # main 0aafa2c (moved since base e004671: T2373 deleted 2 UN lines)
141:   `RBM.BA.BAKsolve, -- existence of the BA ...
$ wc -l < RBM3D/BA/KTreeRep.lean
    1763                                   # stop line 2000: under
```
Only the two sole writable files; the one-line deletion re-applies on current `main` (H23 (b)). No frozen signature touched (new file + one registry line).

## 2. Build, hygiene, axioms (audit worktree)
```
$ lake build RBM3D.BA.KTreeRep 2>&1 | grep -E "KTreeRep|error|Build"
Build completed successfully (3743 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option" RBM3D/BA/KTreeRep.lean
36:set_option linter.style.longLine false
1278:set_option synthInstance.maxSize 512 in
1391:set_option synthInstance.maxSize 512 in
1670:set_option synthInstance.maxSize 512 in
```
(from `lake env lean $S/aud.lean`, exit 0; file contents in §3)
```
'RBM.BA.baChordPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKcac_isKLoopS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baKsolve' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTreeRep' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pins (compiled by `rfl`)
`$S/aud.lean` = the check file Part 1 verbatim (namespace `RBM.BA.T2374Check`) with `import RBM3D.BA.KTreeRep` added, plus
`namespace RBM.BA.T2374Aud` holding prove-report lines 70-81 (the 1a-approved target-2 pin) pasted verbatim by `sed -n 70,81p`, then:
```
example : @RBM.BA.BATreeRep = @RBM.BA.T2374Check.BATreeRep := rfl
example : @RBM.BA.BAChordPairsStmt = @RBM.BA.T2374Aud.BAChordPairsStmt := rfl
example : ∀ d, RBM.BA.BAKsolve d := RBM.BA.baKsolve
example : ∀ d, RBM.BA.BATreeRep d (@RBM.BA.BAGamma d) := RBM.BA.baTreeRep
example : ∀ d, RBM.BA.BAChordPairsStmt d := RBM.BA.baChordPairs
$ lake env lean $S/aud.lean; echo exit=$?
exit=0
```
Relevant `#print`/`#check` output from the same run:
```
def RBM.BA.BAKsolve : ℕ → Prop := fun d => ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ →
  ∀ (E : ℝ) (m : ℂ), BA.BAReal d L g κ E m → ∃ K, IsKLoopS d L W 1 (PropSpin m) (BA.BAMLoop d L W (BA.BAMsigma d L (BA.BAMB d L g (↑E) m)))
    (Set.Ico 0 1) K ∧ ∀ t ∈ Set.Ico 0 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L), K t { σ := [σ.1, σ.2], a := [a₁, a₂] } =
      (↑W ^ d)⁻¹ * (BA.BATheta d L g E m t σ.1 σ.2 * BA.BAMss d L (BA.BAMB d L g (↑E) m) σ.1 σ.2) a₁ a₂
@BA.baKcac_isKLoopS : ∀ {d L W : ℕ} [inst : NeZero L] {g κ E : ℝ} {m : ℂ}, BA.BAReal d L g κ E m →
    IsKLoopS d L W 1 (PropSpin m) (BA.BAMLoop d L W (BA.BAMsigma d L (BA.BAMB d L g (↑E) m))) (Set.Ico 0 1) (BA.BAKcac d L W g E m)
@BA.BAKcac_spliced : ∀ {d L W : ℕ} [inst : NeZero L] {g E : ℝ} {m : ℂ}, BA.BASplicedFam d L W g E m (BA.BAKcac d L W g E m)
```
- Target 1 `BATreeRep`: definitionally equal to the check-file pin (`rfl`). PASS.
- Target 2 `BAChordPairsStmt` / `baChordPairs`: definitionally equal to the 1a pin (`rfl`); `n ≥ 3`, all `σ, a`, `0 ≤ t < 1`,
  any `K` with `BASplicedFam`; left side is the chord part `Function.update … (Sum.inl J) (Θ·Θ)` of `BAGammaDerivRHS`, right side the
  `(i+1, j+1)` summands of `treeEqRhsS` at `S = 1` over `diagonals n`, with `W^d` and `(W^d)⁻¹^(n-1)`. `BAReal`, `0 ≤ t < 1` are
  unused (kept as pinned; a stronger theorem than needed, not a weaker one). PASS.
- Target 3 `baKcac_isKLoopS`: exactly the ticket's statement (`BAReal` only; `S = 1`, `PropSpin m`, `BAMLoop`, `Ico 0 1`, `BAKcac`). PASS.
- Target 4 `baKsolve : ∀ d, BAKsolve d`: the merged pin `BAKsolve` (`BA/KSolve.lean`), unconditional. PASS.
- Target 5 `baTreeRep : ∀ d, BATreeRep d (@BAGamma d)`: `Γ = @BAGamma d`, `3 ≤ n`, unconditional. PASS.

## 4. Hidden hypotheses, vacuity, cycles
- No structure carries a hypothesis: `BASplicedFam` (printed above: clauses 1-3, the defining equations of `K`) is a hypothesis of
  target 2 only, and is discharged at the instance by `BAKcac_spliced` (merged K05a, unconditional). `BAReal` = `BASelf ∧ κ ≤ Im m`
  (`MFixedPoint.lean:432`), satisfied at the flow point.
- `baKsolve` is proved with witness `BAKcac` (`baKcac_isKLoopS`, `BAKcac_spliced.2.1`); `baTreeRep` uses `BAKsol_isKLoopS (baKsolve d)`,
  `baK_unique`, `baKcac_isKLoopS`, `BAKcac_spliced.2.2` (file lines 1699-1720). `baKcac_isKLoopS` does not use `baKsolve`/`BAKsol`: no cycle.
- Dependencies are merged on `main` (`git ls-tree main RBM3D/BA/KTreeDeriv.lean` → blob 258ba66; `KSolve`, `KCactus`, `KLCut` merged).
- No external hypothesis is introduced (the owed premise `BAKsolve` is discharged, not assumed); no limit check owed.

## 5. Compiled nonempty instances (namespace `KTreeRepInst`, file lines ~1722-1761; compiled by the module build in §2)
Datum: `P : FlowPt 4 10` (`MFixedPoint.lean:893`, `P := (exists_flowPt 4 …).some`; `FlowPt` fields `g0_pos : 0 < g0`, `g0_le`,
`real : BAReal 3 L g0 m0.im E m0`), `(d, L) = (3, 4)`, `W = 2`, `Λ = 10`, `κ = Im m₀`, `t = 1/2`, `n = 4`,
`σ = ![true,true,false,true]`, `a = ![![0,0,0],![1,0,0],![2,0,0],![3,0,0]]` (four distinct sites).
```
example := KTreeRep_cut (d := 3) (L := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) (J := ((0 : Fin 4), (2 : Fin 4))) KTreeRep_isTSP_F02 (by norm_num) (Finset.mem_singleton_self _) … (1 / 2) σ a
example := baChordPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 4 (by norm_num) σ a (1 / 2) (by norm_num) (by norm_num)
example : IsKLoopS 3 4 2 1 (PropSpin P.m0) (BAMLoop 3 4 2 …) (Set.Ico 0 1) (BAKcac 3 4 2 P.g0 P.E P.m0) := baKcac_isKLoopS P.real
example := baKsolve 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real
example := baTreeRep 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) ⟨by norm_num, by norm_num⟩ 4 (by norm_num) σ a
```
Every hypothesis is discharged at concrete data; none is left open. Nondegenerate: `n = 4` (`TSP_four : TSP 4 = {∅, {(0,2)}, {(1,3)}}`,
two diagonals, so both sides of target 2 are nonempty sums), `F ∋ J = (0,2)` as the ticket requires (target 6), `L = 4 ≥ 3`,
`W = 2 ≠ 0`, `t = 1/2` interior of `[0,1)`, `0 < g0 ≤ 10`, `κ = Im m₀ > 0` from `BASelf`. Not a `False` premise (P is built from
`exists_flowPt`, a proved `Nonempty`). PASS for target 6.

## 6. Registry pre-check (target 7)
```
$ { grep "^import" RBM3D.lean; echo "import RBM3D.BA.KTreeRep"; echo "#assert_rbm_axioms"; } > $S/precheck2.lean   # 418 import lines
$ lake env lean $S/precheck2.lean; echo exit=$?
exit=0
axiom audit: 10917 theorems, 3210 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ grep -o "RBM.BA.BAKsolve\|unregistered\|none of" $S/precheck2_out.txt | sort | uniq -c      # (no output)
```
Control (expected): `lake build RBM3D` in the audit worktree *without* the new import fails with
```
error: RBM3D.lean:420:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, …:
  [RBM.BA.BAKsolve]
```
i.e. the deleted line and the root import `import RBM3D.BA.KTreeRep` must land together at merge (CLAUDE.md §3 (A) step 4 does this). PASS.

## 7. Paper deltas
`BATreeRep` is the pin from the probe at `3 ≤ n` (paper `A:592-598` for `n ≥ 4`, `(Kn3sol)` `1_2:1176` for `n = 3`; supervisor 0350 Q1).
`BAChordPairsStmt` is an internal identity (no paper statement). `baKsolve`/`baKcac_isKLoopS` instantiate the merged pins
`BAKsolve`/`IsKLoopS` without change. No Lean/paper statement difference arises; the report proposes none (`T2374a` not needed). PASS.

## Observations (no effect on verdict)
- O1. Stop line: 1763 lines < 2000; Q4 (C5): 612 + 1763 = 2375 < 3.3k (report §(b), confirmed by `wc -l` above).
- O2. `synthInstance.maxSize 512` is scoped by `in` to three declarations; not a hygiene issue.
- O3. Merge note: `Test/Axioms.lean` on `main` changed since the base (two `RBM.Univ` lines removed by T2373); the deletion is at
  `main` line 141 and must be re-applied there; root `lake build` passes only with the `KTreeRep` import added (§6 control).

## Verdict
| target | verdict |
|---|---|
| 1 `BATreeRep` pin | PASS |
| 2 `baChordPairs` (`BAChordPairsStmt`) | PASS |
| 3 `baKcac_isKLoopS` | PASS |
| 4 `baKsolve` | PASS |
| 5 `baTreeRep` | PASS |
| 6 instances | PASS |
| 7 registry line | PASS |

**T2374: PASS.** No dispatcher sign-off needed.
