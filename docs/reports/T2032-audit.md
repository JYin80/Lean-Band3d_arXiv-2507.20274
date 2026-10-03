Auditor model: claude-opus-5-5

# T2032 audit (round 1) — S1-03 `RBM3D/Hierarchy/ContractionBasic.lean`

Audit time: Sat Oct  3 05:58:43 UTC 2026 (`date -u`). Branch `t/T2032` at `8de0ca4` (merge-base with main `c8bedf7`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2032-audit1` (detached). RBM2D source `c9a24cf`.

## 1. Statements (script diff: RBM2D `c9a24cf` signature, renamed by ST1-COMMON R1-R4, vs the new file)
Script `sdiff.sh` (scratchpad): awk-extracts `theorem NAME` up to `:= by`, applies sed renames (`Z2 L→Zd d L`, `BlockIndex→Vtx d`, `Idx/Coord/gvar/coordinateMatrix/Eblk/SB/blockRelabel/usedCoords/split/cut*Chain/gloopProd` with `d` (and `g`), `gloop→loopL`, `Gsig→Gres`, `^ 2→^ d`), word-diffs.
```
$ bash sdiff.sh   (one line per target; diff output joined)
=== ContractionBasic:sum_Svar_diag_mul  (2D 7 lines, 3D 7 lines) :: 2a3,4 > [NeZero > W] 31c33,34 < Svar --- > ((svar > d 33a37 > g 35a40,43 > : > ℝ) > : > ℂ)
=== ContractionDirections:weighted_trace_coordinate_diag  (2D 6 lines, 3D 6 lines) :: 57c57,58 < Spaper --- > ((svarF > d 59a61 > g 61a64,67 > : > ℝ) > : > ℂ)
=== ContractionSum:sum_usedCoords_trace_blocks  (2D 8 lines, 3D 8 lines) ::
=== ContractionUnused:sum_allCoords_trace_blocks  (2D 8 lines, 3D 8 lines) ::
=== ContractionCutWords:sum_coordinate_cutChains  (2D 22 lines, 3D 22 lines) :: 89c89 < Gauss.CoordF --- > CoordF 93c93 < (((Gauss.gvarF --- > (((gvarF 107c107 < Gauss.coordinateMatrix --- > coordinateMatrix 115c115 < Gauss.coordinateMatrix --- > coordinateMatrix
=== ContractionDrift:neg_trace_scalarDrift_cutGlue_split  (2D 12 lines, 3D 12 lines) ::
```
All public declarations of the six source files (script `alldiff.sh`, same renames plus `Gauss.` stripped):
```
EQUAL ContractionBasic:trace_mul_single_mul_single
DIFF  ContractionBasic:trace_mul_Eblk
DIFF  ContractionBasic:sum_Svar_diag_mul
DIFF  ContractionDirections:coordinateMatrix_real_eq
DIFF  ContractionDirections:coordinateMatrix_imag_eq
EQUAL ContractionDirections:coordinateMatrix_diag_eq
DIFF  ContractionDirections:trace_coordinate_real
DIFF  ContractionDirections:trace_coordinate_imag
EQUAL ContractionDirections:trace_coordinate_diag
DIFF  ContractionDirections:weighted_trace_coordinate_offDiag
DIFF  ContractionDirections:weighted_trace_coordinate_offDiag_blocks
DIFF  ContractionDirections:weighted_trace_coordinate_diag
EQUAL ContractionSum:usedCoords
DIFF  ContractionSum:sum_usedCoords_trace
EQUAL ContractionSum:blockRelabel
EQUAL ContractionSum:blockRelabel_apply_split
DIFF  ContractionSum:sum_Spaper_diag_mul_relabel
EQUAL ContractionSum:sum_usedCoords_trace_blocks
EQUAL ContractionUnused:coordinateMatrix_diag_imag_zero
DIFF  ContractionUnused:coordinateMatrix_lower_zero
EQUAL ContractionUnused:coordinateMatrix_zero_of_not_mem_usedCoords
EQUAL ContractionUnused:sum_allCoords_trace_eq_usedCoords
EQUAL ContractionUnused:sum_allCoords_trace_blocks
EQUAL ContractionCutWords:cutLeftChain
EQUAL ContractionCutWords:cutRightChain
EQUAL ContractionCutWords:trace_cutLeftChain_Eblk
EQUAL ContractionCutWords:trace_cutRightChain_Eblk
EQUAL ContractionCutWords:blockRelabel_submatrix_split
EQUAL ContractionCutWords:sum_coordinate_cutChains
DIFF  ContractionDrift:sum_gloop_cutGlue_split
EQUAL ContractionDrift:trace_scalarDrift_cutGlue_split
EQUAL ContractionDrift:neg_trace_scalarDrift_cutGlue_split
```
Residual DIFF tokens (full output inspected): `> d > d` = `idxKey d L W` (rename not in sed list); `((W:ℂ)⁻¹)^2 → ((W:ℂ)^d)⁻¹` (the merged `Eblk` weight); `Fin W × Fin W → Fin (W ^ d)`; `Svar/Spaper → ((svar|svarF d L W g · · : ℝ) : ℂ)`; `[NeZero W]` explicit in `sum_Svar_diag_mul` (2D had it in the binder list stripped by the sed). No MISSING: all 32 RBM2D public declarations are ported (`sum_Spaper_diag_mul_relabel` renamed `sum_svarF_diag_mul_relabel`), plus 1 new (`blockRelabel_eq_blockMat`, `rfl` to merged `blockMat`): 33 public declarations; none dropped.

Replacement of `Svar`/`Spaper` checked against definitions:
```
RBM2D Defs/Model.lean:39  Svar L W (a, α) (b, β) = SB L a b * (W : ℂ)⁻¹ ^ 2 := rfl
RBM2D Defs/Model.lean:190 Spaper i j := SB L (blk i) (blk j) * (W : ℂ)⁻¹ ^ 2
RBM3D Gauss/Model.lean:63      svar (x y : Vtx d L W) : ℝ := ((W : ℝ) ^ d)⁻¹ * SBR d L g x.1 y.1
RBM3D Gauss/FineModel.lean:47  svarF (i j) : ℝ := ((W : ℝ) ^ d)⁻¹ * SBR d L g (split i).1 (split j).1
RBM3D Propagator/Props4.lean:52 SB_eq_map_SBR : SB d L g = (SBR d L g).map (↑)
RBM3D Loop/GLoop.lean:55       Eblk a := diagonal fun x => if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0
```
Paper: `(eq:variancematrix)` `1_2:303-305` `S_xy = W^{-d} S^(B)_ab(λ)`; `(Eq:defGLoop)` `1_2:823-824` `(E_a)_xy = W^{-d} 1(x=y∈[a])`. The `W^d` coefficient is forced: `W^d·(W^{-d})^2 = W^{-d}`.
`cutGlue`, `cutGlueL`, `cutGlueR` (merged `GLoopFlow.lean:317`, `TreeRep.lean:84,89`) have the same `σ`/`a` fields verbatim as RBM2D `Operations.lean:27`, `OperationsPair.lean:23,28`.

Per target: `sum_Svar_diag_mul` = RBM2D up to `Svar → cast svar` and `W^2 → W^d`; `weighted_trace_coordinate_diag` up to `Spaper → cast svarF`; `sum_usedCoords_trace_blocks`, `sum_allCoords_trace_blocks`, `sum_coordinate_cutChains`, `neg_trace_scalarDrift_cutGlue_split` EQUAL after renaming. Hypotheses: only `[NeZero L] [NeZero W]` and the length equalities `h₁ h₂`, identical to RBM2D. No added or dropped hypothesis, no weakening; these are unconditional finite-matrix identities (no general loop-hierarchy statement is claimed).

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -cE "^(structure|class) " RBM3D/Hierarchy/ContractionBasic.lean
0
$ grep -n "^import" RBM3D/Hierarchy/ContractionBasic.lean
6:import RBM3D.Loop.GLoopFlow
7:import RBM3D.Gauss.FineModel
```
No structure fields, no `Prop`-valued definitions (`usedCoords` Finset, `blockRelabel`/`cutLeftChain`/`cutRightChain` matrices), so no registry line due (Amend 1); `RBM3D/Test/Axioms.lean` untouched. No external hypothesis, so no limit check applies. Dependencies are merged modules only; no ST-2..ST-6 import.

## 3. Compiled nonempty instances (file lines 884-932, `namespace ContractionInst`)
Data: `d = 3, L = 3, W = 2, g = 1/2` (216 sites, 27 blocks); matrices `1`, `Eblk 3 3 2 (lab 1)`; `H = 1`, `z = Complex.I` (so `H - z` invertible); chains `σ₁=[+,-] σ₂=[-,+] σ₃=[+]`, labels nonempty, `h₁ h₂` by `rfl`; `m = 7/10 - i/5`. One `example` per target (6/6), each applying the target with every hypothesis discharged; `sum_Svar_diag_mul` instance states its conclusion in full. Compiled as part of the module build (§4). Nondegenerate: no `N = 0`, no empty index, no `False` premise, no large witness.

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Hierarchy.ContractionBasic 2>&1 | grep -E "error|warning|sorry|Build completed"
Build completed successfully (3294 jobs).
rc=0
$ lake env lean ax.lean   (#print axioms of all 33 public theorems/defs of the file)
exit=0; lines with [propext, Classical.choice, Quot.sound]: 33; other lines: 0
'RBM.Gauss.sum_Svar_diag_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.weighted_trace_coordinate_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.sum_usedCoords_trace_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.sum_allCoords_trace_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.sum_coordinate_cutChains' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.neg_trace_scalarDrift_cutGlue_split' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Hierarchy/ContractionBasic.lean; echo rc=$?
rc=1
$ git diff --stat main...t/T2032
 RBM3D/Hierarchy/ContractionBasic.lean | 934 ++++++++++++++++++++++++++++++++++
 1 file changed, 934 insertions(+)
$ lake env lean reg.lean   (import RBM3D; import RBM3D.Hierarchy.ContractionBasic; #assert_rbm_axioms)
exit=0
axiom audit: 1196 theorems, 423 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 12 (borrowed 2, owed 0, structural 10).
```
Only the sole writable file is touched; no frozen signature changed.

## 5. Paper deltas
Lean/paper (and RBM2D) differences and their candidates in the prove report (d): `Svar/Spaper` replaced by casts of the real `svar/svarF` with the coupling `g` (T2032a); all declarations in `RBM.Gauss` rather than `RBM` (T2032b, a citation-prefix matter for later tickets); coefficient `W^d`, weight `((W:ℂ)^d)⁻¹`, fibre `Fin (W^d)` (T2032c). The `g` (paper `λ`) of `SB d L g` is merged MD-layer vocabulary, not introduced here. Coverage complete.

## Observations (no statement/instance/build/axiom/delta effect)
- ST1-COMMON item 7 names the MD-1 sequence or `sz0`/`sz1` for instances; the file uses `d=3, L=3, W=2`, which the ticket's preflight text itself specifies. The targets take no `Sizes`, so this does not affect nondegeneracy.
- Prove report registry counts (1088 theorems) differ from this run (1196) because the audit worktree caches a newer main build; both exit 0.

## Verdict
| target | statement | instance | build/axioms | verdict |
|---|---|---|---|---|
| sum_Svar_diag_mul | = RBM2D after R1-R4 + T2032a | yes | ok | PASS |
| weighted_trace_coordinate_diag | = RBM2D after R1-R4 + T2032a | yes | ok | PASS |
| sum_usedCoords_trace_blocks | EQUAL | yes | ok | PASS |
| sum_allCoords_trace_blocks | EQUAL | yes | ok | PASS |
| sum_coordinate_cutChains | EQUAL | yes | ok | PASS |
| neg_trace_scalarDrift_cutGlue_split | EQUAL | yes | ok | PASS |

Ticket verdict: **PASS**. No dispatcher sign-off needed.
