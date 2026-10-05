Auditor model: claude-opus-5-5

# T2189 audit (round 1) — BA/MFixedPoint (BA-D1a + BA-D2)

Mon Oct  5 15:10:37 UTC 2026 (`date -u`).  Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2189-audit1`, detached at `t/T2189` = d397b09 (base fbaa460; main = 2a42f07).
Scratch: `scratchpad/T2189/` (`diff.py`, `audit_check.lean`, `probe.lean` = `git show 82e72b3:RBM3D/Probe/T2161Pins.lean`).

## 1. Statements (script diff)

`python3 diff.py` (library file vs `docs/tickets/checks/T2189-check.lean` vs probe at 82e72b3; whitespace-normalised text; section `variable` contexts also compared below):
```
(A) definitions/pins: library vs check file (whitespace-normalised full text)
  equal 22/22
(B) new theorems: library statement vs check _stmt body
  equal 8/8
(C) 17 copied theorems: library statement vs probe 82e72b3
  equal 17/17
  baMExists_holds (line 795): theorem baMExists_holds (d : ℕ) : BAmExists d
  baMUniqReal_holds (line 803): theorem baMUniqReal_holds (d : ℕ) : BAmUniqReal d
```
(per-name lines elided: every one of the 22 + 8 + 17 rows reads `EQUAL`.)  Section contexts: library `variable (d L : ℕ) [NeZero L]` in Det/DetPins/Bulk/Thetas, `variable {d L}` before the Bulk theorems, `variable (d : ℕ)` in DetPins2 — same as the probe (`:184`, `:376`, `:439`, `:462`, `:528`, `:566`) and the check file.

Semantic check (`lake env lean audit_check.lean` in the audit worktree; the file imports `RBM3D.BA.MFixedPoint`, contains check sections 2-3 verbatim in `RBM.BA.T2189Check`, then 22 `example : @RBM.BA.X = @RBM.BA.T2189Check.X := rfl`, 8 `example (d L) [NeZero L] : T2189Check.X_stmt d L := X d L`, and `example (d) : T2189Check.BAmExists d := baMExists_holds d`, same for `BAmUniqReal`):
```
exit 0
```
So every definition equals the check's pinned definition, every new theorem inhabits exactly the pinned `…_stmt`, and 4e concludes exactly the pinned `BAmExists d`, `BAmUniqReal d`.

Mathematics against the ticket and paper (`1_2:626-633`, `:715`): `BASelf` is `(self_m)` on the block lattice with `L^{-d} tr M^{(B)}` (paper: `N^{-1} tr` of `M = M^{(B)} ⊗ I_{W^d}`, equal normalised traces; proposed as T2189b).  4b is `freeConv_existsUnique`'s predicate at `t = 1`; 4d covers every `0 ≤ Im z`, real axis included; 4a-4d, 4f hold for every `d`, `L` with `NeZero L`, every real `g` — strictly more general than the pins' range (`3 ≤ L`, `0 < g`), which 4e instantiates; the pins are unchanged, as the ticket instructs.  No special case or conditional adapter: the 10 targets are the general statements pinned.

## 2. Hidden hypotheses, vacuity, cycles

```
$ grep -n 'BAmBoundary\|BAWard\b\|BAPropM\|BAoffDiag\|BAImmLower' MFixedPoint.lean  (outside the pin defs :531-602)
388:summed over `a`; the row-wise identity is the pin `BAWard`). -/
478:`BAPropM`, `BAProp5`-`BAProp8` apply at `(g₀, E, m₀)`. -/
```
Docstring mentions only: no theorem assumes an owed pin.  No target has a structure-typed hypothesis; the only structure, `MFixedPointInst.FlowPt`, is instance data (fields `g0_pos`, `g0_le`, `real : BAReal …`) built by `exists_flowPt` from the proved `BAzztE_data`, `BAg0_le`.  Dependencies: `BASelf_exists` ← `freeConv_existsUnique` (merged T2176) + 4b; 4d ← `BAward_avg` + private `MFixedPoint_HS`; 4e/4f ← 4c, 4d, `BAm_spec`, `isFreeConv51_freeConvST` (merged).  No cycle (Lean accepts the file in order).  No external hypothesis is introduced, so no limit check is required.  Not vacuous: `BASelf` is inhabited at `Im z > 0` (`(4,10,i)`) and on the real axis (`P.real.1 : BASelf 3 4 P.g0 P.E P.m0`, with `0 < P.m0.im`).

## 3. Compiled nonempty instances (`RBM.BA.MFixedPointInst`, file `:838-994`)

`d = 3`, `L = 4` (`card (Zd 3 4) = 64`, example `:958`), `g = 10`, `z = Complex.I`; `zS 4 10` (`Im > 0`, `zS_im_pos`); `P : FlowPt 4 10` (real energy `P.E`, `P.g0 > 0`, `Im P.m0 > 0`).  Every hypothesis of every example is discharged (no `variable`/binder left on any example; `(by simp)`, `(by norm_num)`, `zS_im_pos`, `P.real.1`, `P.g0_pos`, `div_pos P.real.1.1 Real.pi_pos`).
| target | example line | data |
|---|---|---|
| `baMExists_holds` | 898 | `3 4 (3≤4) 10 (0<10) I (0<Im I)` → `∃! m, BASelf 3 4 10 I m` |
| `baMUniqReal_holds` | 902 | `3 4 _ P.g0 P.g0_pos P.E` at the real-axis solution `P.m0` |
| `BASelf_exists`, `BAm_self`, `BAm_eq_freeConvST` | 907, 909, 911 | `(4, 10, I)` |
| `BAMB_trace_eq_sum` | 915 | `m = BAm 3 4 10 I`, `(I+m).im ≠ 0` proved |
| `BASelf_iff_freeConv` | 923 | `(4, 10, I)`, `.mp` of `BAm_self` |
| `BASelf_unique` | 929, 934 | `z = zS 4 10` (`Im > 0`); `(P.g0, P.E)` (`Im z = 0`) |
| `BAm_real_eq_of_self` | 937 | `P` |
| `BAbulk_iff_exists` | 940 | `P`, `κ = P.m0.im/π > 0`; concludes `BAbulk 3 4 P.g0 κ P.E`, no uniqueness hypothesis |
| 17 copied theorems | 946-992 | `wI = 6i/5`, `(zS, mS) 4 10`, `P` |
None is degenerate (`L = 4`, 64 sites, `g = 10 ≠ 0`, `Im z ∈ {1, Im zS > 0, 0}` with an actual solution in each case).

## 4. Build, axioms, scope

```
$ lake build RBM3D.BA.MFixedPoint   (audit worktree; error/warning lines)
✔ [3331/3331] Built RBM3D.BA.MFixedPoint (4.5s)
Build completed successfully (3331 jobs).
$ lake env lean audit_check.lean  (#print axioms: 10 targets, 17 copied theorems, 6 instance names)
lines: 33; exactly [propext, Classical.choice, Quot.sound]: 33; other lines: 0
'RBM.BA.BAMB_trace_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BASelf_iff_freeConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BASelf_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BASelf_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMExists_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMUniqReal_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_eq_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_real_eq_of_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAbulk_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE 'sorry|admit|native_decide|^\s*axiom ' RBM3D/BA/MFixedPoint.lean
0
$ grep -c 'seqP\|Prec\|SeqΩ\|Sizes' RBM3D/BA/MFixedPoint.lean     (§57 (3))
0
$ git diff --name-status main...t/T2189
A	RBM3D/BA/MFixedPoint.lean
$ git grep -c "namespace RBM.BA\|RBM.BA.MFixedPointInst" main -- RBM3D RBM3D.lean | wc -l
0
$ git diff --stat fbaa460 main -- RBM3D/Gauss RBM3D/Loop/GLoopFlow.lean RBM3D/Universality/FreeConv.lean RBM3D/Analysis/Resolvent.lean RBM3D/Propagator/Pins.lean RBM3D/Defs | wc -l
0
```
Only the sole writable file `RBM3D/BA/MFixedPoint.lean` is touched (new); `RBM3D/Test/Axioms.lean` untouched (no registry line needed: no theorem assumes a pin); no frozen signature touched; imports are the four allowed modules plus Mathlib, never `RBM3D`.  Upstream files unchanged between the branch base and main.

## 5. Paper deltas

Lean/paper differences and their coverage:
- Real-axis uniqueness of `(self_m)` (proved, not stated in the paper, which uses `m(E) = m(E+i0)`, `1_2:715`), `BAm = 0` when no solution, existence/uniqueness for every `L ≥ 1`, `g ∈ ℝ`: candidate **T2189a** (prove report (d)).
- `(self_m)` stated with `L^{-d} tr M^{(B)}` instead of `N^{-1} tr` of the `N × N` matrix (`1_2:615`, `:626-631`; verified in TeX: `M = M^{(B)} ⊗ I_{W^d}`): candidate **T2189b**.
- Bulk set `κ ≤ ρ_N(E)` instead of `|E| ≤ e_λ − κ`: existing D403 (T2161b), `docs/paper-deltas.md:1362`.
- Identification `BAm(E) = m(E + i0)`: owed pin `BAmBoundary` (BA-D6), stated, not assumed.
All differences are covered.

## 6. Observations (no effect on verdict)

- O1. Prove report b.5 name-clash grep is against main = 2a42f07 while the branch base is fbaa460; the intervening merge (T2184, `Graph/LocalRegular6a`) touches no `RBM.BA` name (grep above: 0).
- O2. The pins `BAmExists`, `BAmUniqReal` carry `3 ≤ L`, `0 < g` that the proofs do not need (reported in prove (d); pins unchanged per ticket).

## Verdict

| target | verdict |
|---|---|
| 1 vocabulary (14 defs + `BAspec`) | PASS |
| 2 seven pins (stated only) | PASS |
| 3 seventeen copied theorems | PASS |
| 4a `BAMB_trace_eq_sum` | PASS |
| 4b `BASelf_iff_freeConv` | PASS |
| 4c `BASelf_exists` | PASS |
| 4d `BASelf_unique` | PASS |
| 4e `baMExists_holds`, `baMUniqReal_holds` | PASS |
| 4f `BAm_self`, `BAm_eq_freeConvST`, `BAm_real_eq_of_self`, `BAbulk_iff_exists` | PASS |

**T2189: PASS.**  No dispatcher sign-off needed.
