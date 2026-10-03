Auditor model: claude-opus-5-5

# T2061 audit (round 1) — Sat Oct  3 19:53:45 UTC 2026

Ticket `docs/tickets/T2061.md` (+ Amend 1, DECISIONS §30); branch `t/T2061` at `00aa135`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2061-audit1` (detached). No statement pin in `docs/tickets/checks/T2061-check.lean` (it only `#check`s upstream names), so statements are checked against RBM2D `c9a24cf` after the ST1-COMMON item 2 renaming (item 6) and against Amend 1 for the bounded weight.

## 1. Statements

### 1.1 Script diff, RBM2D `c9a24cf` (CondRow+GreenDeriv+FlucVanish) vs `RBM3D/Green/FlucVanish.lean`

RBM2D side renamed by R1–R4 (`(d : Sizes)`→`(sz : Sizes d)`, `Idx (`→`Idx d (`, `Z2 L`→`Zd d L`, `SeqΩ d`→`SeqΩ sz`); RBM3D side drops `{d : ℕ}`; signatures up to `:=`/`where`, whitespace-normalised.
```
$ python3 scratchpad/T2061/sig.py all2d.lean FV.3d.lean <names>
EQUAL greenMinorMat_eq_minorGreen
EQUAL continuous_green_comp
DIFF  flucVanish_blockAvg2_eq_blkCoef2
  2D: theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Zd d L) (k : Idx d L W) : (if (blk L W k.1, blk L W k.2) = a then (W : ℝ)⁻¹ ^ 2 else 0) = blkCoef2 L W a (splitEquiv L W k)
  3D: theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Zd d L) (k : Idx d L W) : (if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0) = blkCoef2 d L W a (splitEquiv d L W k)
EQUAL greenMinorMat
EQUAL condRow
EQUAL rowSplit
EQUAL FinDepOffRow
EQUAL flucDiag
EQUAL flucAvg
EQUAL UniformWeight
DIFF  uniformWeight_blockAvg2
  2D: theorem uniformWeight_blockAvg2 (a : Zd d L) : UniformWeight (fun k : Idx d L W => if (blk L W k.1, blk L W k.2) = a then (W : ℝ)⁻¹ ^ 2 else 0) ((W : ℝ)⁻¹ ^ 2) ((univ : Finset (Idx d L W)).filter fun k => (blk L W k.1, blk L W k.2) = a)
  3D: theorem uniformWeight_blockAvg2 (a : Zd d L) : UniformWeight (fun k : Idx d L W => if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0) (((W : ℝ) ^ d)⁻¹) ((univ : Finset (Idx d L W)).filter fun k => (split d L W k).1 = a)
```
Reading: the two key CondRow/GreenDeriv targets and the definitions they rest on (`greenMinorMat`, `condRow`, `rowSplit`, `FinDepOffRow`, `flucDiag`, `flucAvg`, `UniformWeight`) are textually equal. The two DIFF lines are exactly R3 plus the block map: `(blk L W k.1, blk L W k.2)` → `(split d L W k).1`, `(W:ℝ)⁻¹ ^ 2` → `((W:ℝ)^d)⁻¹`; `blkCoef2` is the merged T2057 one (`EntryDom.lean`). Bodies checked by reading: `IsRowCoord c := c ∈ rowSet sz n k` (merged `RowIndep`, `isRowCoord_mk : … ↔ i = k ∨ j = k`), `greenMinorMat` = inverse of the `{a // a ≠ k}` submatrix of `H_u − z`, same as RBM2D.

### 1.2 Amend 1 targets (bounded weight), extracted
```
$ sed -n "941,952p;954,955p;1070,1071p;1169,1172p" RBM3D/Green/FlucVanish.lean   # doc-comment lines removed
structure BoundedWeight [Fintype κ] (t : κ → ℝ) (c : ℝ) (A : Finset κ) : Prop where
  nonneg_c : 0 ≤ c
  nonneg : ∀ k, 0 ≤ t k
  le : ∀ k ∈ A, t k ≤ c
  not_mem : ∀ k ∉ A, t k = 0
  sum_le : ∑ k, t k ≤ 1
theorem UniformWeight.toBoundedWeight [Fintype κ] {t : κ → ℝ} {c : ℝ} {A : Finset κ}
    (h : UniformWeight t c A) : BoundedWeight t c A where
def flucVanish_sbSupport (d L : ℕ) [NeZero L] : Finset (Zd d L) :=
  insert 0 (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1)
theorem boundedWeight_svarF (hL : 3 ≤ L) (g : ℝ) (i : Idx d L W) :
    BoundedWeight (fun j : Idx d L W => svarF d L W g i j) (((W : ℝ) ^ d)⁻¹)
      ((univ : Finset (Idx d L W)).filter fun j =>
        (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L) := by
```
Against Amend 1: fields `0 ≤ t k`, `t k ≤ c` on `A`, `t k = 0` off `A` present; `c = (W^d)⁻¹`; `A = {j : blk j − blk i ∈ {0} ∪ {zdistD = 1}}` (orientation `blk j − blk i` as pinned); `#A = (2d+1) W^d` (`flucVanish_card_svarSupport_eq`, `3 ≤ L`). Support set matches `sbKernelR` (`Defs/Block.lean:74-76`: nonzero only at `x = 0` or `zdistD x = 1`), `card_nbhd : #{zdistD x = 1} = 2d` (`Defs/Neighbours.lean:158`), `zdistD = Σ_i zdist` (`Defs/Lattice.lean:71`). The sum field is `∑ t ≤ 1`, not `= 1`; Amend 1 asks for the sum "if the consumers use it; say which": the report (a) round 2 names `hw.mass` (FlucIter:1018) as the only sum use, and `= 1` would make the also-required `UniformWeight.toBoundedWeight` false (`UniformWeight.mass` is `c·#A ≤ 1`). Extra field `nonneg_c : 0 ≤ c` is a conclusion field here, derivable whenever `A ≠ ∅`. Both recorded in paper-delta candidate T2061a. No loss, exponent or quantifier change; hypotheses `hL : 3 ≤ L`, `[NeZero L] [NeZero W]` only.

### 1.3 Dropped / renamed public declarations and their consumers
```
$ git -C ../RBM2D --no-optional-locks grep -n -E "flucVanish_card_filter_blk2_mem|flucVanish_card_sbSupport_le|uniformWeight_svar\b|flucVanish_card_svarSupport|flucVanish_card_filter_sub_mem_sbSupport" c9a24cf -- RBM2D | grep -v Green/FlucVanish.lean
c9a24cf:RBM2D/Green/FlucAvg.lean:47:  `flucVanish_card_blockSupport`, `flucVanish_card_svarSupport_eq`.
c9a24cf:RBM2D/Green/FlucAvg.lean:363:elements (RBM1D `card_Sblk_support` has `3W`); the merged `flucVanish_card_svarSupport_eq` at
c9a24cf:RBM2D/Green/FlucAvg.lean:370:  flucVanish_card_svarSupport_eq (d.L n) (d.W n) (d.three_le_L n) i
c9a24cf:RBM2D/Green/FlucIter.lean:1630:  have hA := flucVanish_card_svarSupport_eq (flucIterCheckSizes.L 0) (flucIterCheckSizes.W 0)
$ git -C ../RBM2D --no-optional-locks grep -n "uniformWeight_svar" c9a24cf -- RBM2D   # code lines outside FlucVanish shown; doc-comment hits FlucAvg:348, FlucAvgDet:448, FlucIter:22,58 omitted
c9a24cf:RBM2D/Green/FlucAvgDet.lean:474:      (fun n i => uniformWeight_svar (d.L n) (d.W n) i)
c9a24cf:RBM2D/Green/FlucAvgDet.lean:590:    (fun n i => uniformWeight_svar (sizes.L n) (sizes.W n) i)
c9a24cf:RBM2D/Green/FlucIter.lean:1634:    (uniformWeight_svar (flucIterCheckSizes.L 0) (flucIterCheckSizes.W 0) (0, 0)) ?_) ?_
```
Dropped `flucVanish_card_sbSupport_le` and renamed `flucVanish_card_filter_blk2_mem` have no consumer outside FlucVanish. `uniformWeight_svar` is replaced by `boundedWeight_svarF` by Amend 1 / DECISIONS §30, which already instructs S1-18/S1-20/S1-30. `flucVanish_card_svarSupport_eq` keeps its name; its filter orientation is the pinned `blk j − blk i` (consumer FlucAvg:370 adapts, listed in prove report (d)). No dispatcher decision outstanding.

## 2. Vacuity, hidden hypotheses, cycles

- Endpoint hypotheses: `greenMinorMat_eq_minorGreen`: `hdet : IsUnit det(H_u − z)`, `hGkk : G_kk ≠ 0` (deterministic, discharged in §3); `continuous_green_comp`: `Continuous f`, `∀ v, (f v).IsHermitian`, `z.im ≠ 0`; `flucVanish_blockAvg2_eq_blkCoef2`: none beyond `NeZero`; `boundedWeight_svarF`: `3 ≤ L`. No structure-field hypothesis: `BoundedWeight`/`UniformWeight` occur only as conclusions (or as the input of the conversion lemma). No external hypothesis, so no limit check is needed.
- Imports (all merged on `main`): `Gauss.FlowCalculus` (T2030), `Green.{EntryCore,EntryDom,LDEQuad,RowIndep}` (T2029/T2057/T2031/T2038), `Hierarchy.ContractionBasic` (T2032), Mathlib. None is `RBM3D` or an ST-2…ST-6 file; no cycle (module builds, §4).
- Registry line `RBM.Green.IsRowCoord` (structural): a membership predicate `c ∈ rowSet sz n k`, hypothesis of `rowSplit_apply_of_isRowCoord`; class is correct per ST1-COMMON item 8.

## 3. Compiled nonempty instances (same file, `namespace RBM.Green.FlucVanishInst`)

`sz0` = `SizesInst.sz0` (ST1-COMMON item 7): `d = 3`, `L = 4`, `W = 32`, `lam = 1/64`, `n = 0`; `zI = 1/2 + i/2`.
```
theorem greenMinorMat_eq_minorGreen_sz0 (ω : Sizes.SeqΩ sz0) :
    greenMinorMat sz0 0 (1 / 2) zI (0 : Idx 3 (sz0.L 0) (sz0.W 0)) ω
      = minorGreen (green (Sizes.seqHflow sz0 0 (1 / 2) ω) zI) 0 :=
  greenMinorMat_eq_minorGreen sz0 0 (1 / 2) zI 0 ω
    (flucVanish_isUnit_det (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im)
    (flucVanish_green_diag_ne_zero (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im 0)
theorem continuous_green_comp_sz0_time (ω : Sizes.SeqΩ sz0) :
    Continuous fun u : ℝ => green (Sizes.seqHflow sz0 0 u ω) zI :=
  continuous_green_comp (Sizes.continuous_seqHflow_time sz0 0 ω)
    (fun u => Sizes.seqHflow_isHermitian sz0 0 u ω) zI_im
theorem flucVanish_blockAvg2_eq_blkCoef2_sz0 (k : Idx 3 (sz0.L 0) (sz0.W 0)) :
    (if (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0 then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0)
      = blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 (splitEquiv 3 (sz0.L 0) (sz0.W 0) k) :=
  flucVanish_blockAvg2_eq_blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 k
theorem boundedWeight_svarF_sz0 :
    BoundedWeight
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) =>
        svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j)
      ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹)
      ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun j =>
        (split 3 (sz0.L 0) (sz0.W 0) j).1 - (split 3 (sz0.L 0) (sz0.W 0) 0).1
          ∈ flucVanish_sbSupport 3 (sz0.L 0)) :=
  boundedWeight_svarF 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (sz0.lam 0) 0
```
Every deterministic hypothesis is discharged at every `ω`: `hdet`, `hGkk` by the private Hermitian lemmas `flucVanish_isUnit_det`, `flucVanish_green_diag_ne_zero` (proved, no hypothesis beyond `IsHermitian`, `z.im ≠ 0`); continuity and Hermitian-ness by `Sizes.continuous_seqHflow_time`, `Sizes.seqHflow_isHermitian`; `3 ≤ L` by `sz0.three_le_L 0`. Nondegeneracy is proved: block of `0` has `32768 = W^d` sites with weight `1/32768` (`flucVanish_blockAvg2_nondegenerate_sz0`), the `boundedWeight_svarF` support has `229376 = 7·32^3` sites (`boundedWeight_svarF_card_sz0`); `g = 1/64 ≠ 0`. `UniformWeight.toBoundedWeight` is applied at `sz0` (`boundedWeight_blockAvg2_sz0`). Not `N = 0`, not an empty index, no `False` premise.

## 4. Build, axioms, hygiene, diff
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2061-audit1 && lake build RBM3D.Green.FlucVanish 2>&1 | grep -E "error|warning: RBM3D/Green/FlucVanish|Build completed"
warning: RBM3D/Green/FlucVanish.lean:1004:0: `prod_epsHom_sum_eq` does not use the following hypothesis in its type:
Build completed successfully (3330 jobs).
$ lake build RBM3D 2>&1 | grep -E "^error|Build completed" | tail -3
Build completed successfully (3782 jobs).
$ lake env lean scratchpad/T2061/audit_axioms.lean   # import RBM3D, import RBM3D.Green.FlucVanish, #print axioms ×10, #assert_rbm_axioms
exit=0
'RBM.Green.greenMinorMat_eq_minorGreen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.continuous_green_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.flucVanish_blockAvg2_eq_blkCoef2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.boundedWeight_svarF' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.UniformWeight.toBoundedWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucVanishInst.greenMinorMat_eq_minorGreen_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucVanishInst.continuous_green_comp_sz0_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucVanishInst.flucVanish_blockAvg2_eq_blkCoef2_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]   # output reflowed to one line
'RBM.Green.FlucVanishInst.boundedWeight_svarF_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucVanishInst.boundedWeight_svarF_card_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 2262 theorems, 905 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 47 (borrowed 2, owed 32, structural 13).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|@\[implemented_by|unsafe" RBM3D/Green/FlucVanish.lean; echo $?
1
$ git diff --name-only main...HEAD
RBM3D/Green/FlucVanish.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.Green.IsRowCoord,     -- the coordinate `c` is a coordinate of row `k`: a membership predicate defining `E_k = condRow`, hypothesis of `rowSplit_apply_of_isRowCoord` (S1-17 FlucVanish, T2061)
$ python3 scratchpad/T2061/clash (97 public names outside FlucVanishInst vs declarations in main RBM3D/)
public decls checked: 97 | same-name declarations in main RBM3D/: 0
```
Only the two sole writable files are touched; `Axioms.lean` gets one registry line (in `structuralProps`); no frozen signature is modified (new file only). The pre-check imports `RBM3D` together with the new module and exits 0, so there is no full-name clash.

## 5. Paper deltas

`grep -n T2061 docs/paper-deltas.md` → no lines (not yet appended). Prove report (d) proposes **T2061a**: the row weight `j ↦ S_ij` as `BoundedWeight` (`0 ≤ t ≤ W^{-d}` on `(2d+1)W^d` sites, `0` elsewhere, `Σ t ≤ 1`) instead of RBM2D `UniformWeight`, false at `d ≥ 3` for `g² ≠ 1` (`not_uniformWeight_svarF`). This covers the only Lean/paper statement difference (the paper states no uniform-weight lemma; `greenMinorMat_eq_minorGreen` is the minor/Schur formula, `continuous_green_comp` and the block-average identity have no paper delta).

## 6. Verdicts

| target | verdict |
|---|---|
| `greenMinorMat_eq_minorGreen` (CondRow:358) | PASS |
| `continuous_green_comp` (GreenDeriv:354) | PASS |
| `flucVanish_blockAvg2_eq_blkCoef2` (FlucVanish:472) | PASS |
| Amend 1: `BoundedWeight`, `UniformWeight.toBoundedWeight`, `boundedWeight_svarF`, `#A = (2d+1)W^d` | PASS |

Observations (no RETURN): (i) imports go beyond the four named modules to `Gauss.FlowCalculus` and `Hierarchy.ContractionBasic`, both merged ST-1 dependencies in the ticket header; (ii) `BoundedWeight.sum_le` is `≤ 1` and `boundedWeight_svarF` does not export `Σ_j S_ij = 1` (only a private copy `flucVanish_sum_svarF_row`); a downstream ticket needing the equality must re-prove it or the dispatcher makes `RowIndep.sum_svarF_row` public; (iii) lemmas naming `IsRowCoord` at concrete sizes are checked at `szS` (`d=3, L=3, W=1`, 27 sites) because `sz0` hits max recursion depth (prove report b.4), not endpoint targets.

Overall: **PASS**. No dispatcher sign-off needed.
