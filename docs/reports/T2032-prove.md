Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:43:35 UTC 2026

Sources: RBM2D `c9a24cf` (`Hierarchy/Contraction{Basic,Directions,Sum,Unused,CutWords,Drift}.lean`, read by `git show`); paper `1_2_Intro_model_result.tex` (cited `1_2:line`): `(eq:variancematrix)` `1_2:303-305` `S_xy = W^{-d} S^(B)_ab(ilambda)`, `(Eq:defGLoop)` `1_2:823-824` `(E_a)_xy = W^{-d} 1(x=y in [a])`.
Mathematics of the six files: for the matrix directions `X_c` of the product Gaussian model, `sum_c gvar_c tr(A X_c C X_c)` equals `sum_{i,j} S_ij A_ii C_jj`; with `S_ij = W^{-d} SB_{blk i,blk j}` and `tr(A E_a) = W^{-d} sum_{x in [a]} A_xx` this is `W^d sum_{a,b} tr(A E_a) SB_ab tr(C E_b)` (Basic:47, Sum:201, Unused:110); applied to the two open chains of a two-edge cut it is the cut-and-glue loop pairing (CutWords:87); `sum_b E_b = W^{-d} I` gives the scalar-drift identity `tr(...G_s (mI) G_s E_a ...) = m W^d sum_b L(cutGlue_k^b I)` (Drift:66). No hypothesis beyond `NeZero L`, `NeZero W` and, for the cut words, `|sigma_i| = |a_i|`; no `3 <= d`, `3 <= L`, no `Sizes`.

### (i) Exponent table (every dimension-dependent quantity; no threshold, `ellT`, `Bparam`, `1/5` appears: scal tokens 0 in all six files)
| quantity | d=2 (RBM2D) | d (RBM3D) | constraint (why it must be this) | slack | at d=3,W=2,L=3 |
|---|---|---|---|---|---|
| contraction coefficient (Basic:51, Sum:206, Unused:115, CutWords:99; Drift:52 as `m*W^d`) | `W^2` | `W^d` | `W^d * (W^{-d})^2 = W^{-d}`: two `E` factors of weight `W^{-d}` against one variance `W^{-d}` | none: exact identity; wrong exponent is off by `W^(d-2)` (script: 2.0) | 8 |
| `E_a` weight; `sum_b E_b = W^{-d} I` (Basic:35 `trace_mul_Eblk`, Drift:33) | `(W:C)⁻¹^2` | `((W:C)^d)⁻¹` (merged `Eblk` def, `GLoop.lean:55`) | must be the merged `Eblk` weight so the merged `trace_Eblk = 1` holds | exact | 1/8 |
| fibre of a block (Basic:35,55,63 sums over `Fin W × Fin W`) | `W^2` sites | `Fin (W^d)` (merged `Vtx = Zd d L × Fin (W^d)`, `Model.lean:60`) | `Fintype.sum_prod_type` split and card `W^d` | exact | 8 |
| block count; fine lattice `N` | `L^2`; `(WL)^2` | `L^d`; `(WL)^d = L^d W^d` (`split_bijective`, `Sizes.lean:79`) | `N = |Vtx|` for `blockRelabel`/`splitEquiv` | exact | 27; 216 |
| site variance `S_ij` (Directions:157,182,194; Sum:108) | `Spaper = Svar∘split`, `SB L a b * W⁻²` | `(svarF d L W g i j : C) = W^{-d} SB d L g (blk i)(blk j)` (`FineModel.lean:47`, real-valued, cast to C) | `(SBR a b : C) = SB a b` (`SB_eq_map_SBR`, `Props4.lean:52`) | exact | 1/8 * SB |
| `SB` kernel (only entered through `SB d L g`) | five-point, no `g` | `a0 = 1/(1+2dg^2)` at 0, `g^2 a0` at `zdistD = 1` | row sum `a0 + 2d g^2 a0 = 1` (not used by the identities; they hold for any `g`) | `3 <= L` not needed | 0.4, 0.1 x6, sum 1 |
| coordinate variance `gvarF d L W g (i,j,b)` | `gvar` | `S_ii` if `i=j`, `S_ij/2` else | Directions:162-168, Sum:122-128; used lemmas `gvar_diag/gvar_offDiag` are **private** in `FineModel.lean:251,259` | re-prove (`rfl`+`simp`, 3 lines) | - |
| orientation key, upper-triangular sum (Sum:22) | injective `idxKey` | merged `idxKey`, `idxKey_injective` (`FineModel.lean:73-75`) | dimension-free | - | - |

d=2 tokens of the portmap (columns `W2`,`inv2`,`Z2`), recounted on the sources by `grep -o` (equal to P.7 rows 61-64, 78-79), and their replacement:
| file | W2 | inv2 | Z2/zdist2 | replacement (ST1-COMMON item 2) |
|---|---|---|---|---|
| ContractionBasic | 1 (:51) | 4 (:14,35,45,46) | 4 (:33,51 x2,63) | `W^d`; `((W:C)^d)⁻¹`; `Zd d L`; `Fin W × Fin W` (4 uses) -> `Fin (W^d)`; two docstring "two-dimensional" |
| ContractionDirections | 0 | 2 (:172,182) | 0 | `((W:C)^d)⁻¹` in `_blocks`; the other 8 theorems are dimension-free |
| ContractionSum | 1 (:206) | 0 | 2 (:206 x2) | `W^d`; `Zd d L`; `Z2` also hidden in `BlockIndex`/`Idx` -> `Vtx d L W`/`Idx d L W` |
| ContractionUnused | 1 (:115) | 0 | 2 (:115 x2) | same; first four theorems dimension-free |
| ContractionCutWords | 1 (:99) | 0 | 16 | `W^d`; `Z2 L` -> `Zd d L`; `LoopIdx (Z2 L)` -> `Loop.LoopIdx (Zd d L)` |
| ContractionDrift | 2 (:52,68) | 2 (:12,33) | 12 | `m * W^d`; `((W:C)^d)⁻¹`; `Zd d L` |

Residual statement differences to list in (b) (each a renaming, none changes a loss): R1-R4 as in ST1-COMMON; `Svar L W i j`/`Spaper L W i j` (complex, no merged analogue: `grep -rnw Svar\|Spaper RBM3D` = 0) -> `((svar d L W g i j : R) : C)` (Basic) / `((svarF d L W g i j : R) : C)` (Directions, Sum); `SB L a b` -> `SB d L g a b`; `gvar L W`/`Coord L W` -> `gvarF d L W g`/`CoordF d L W`; `Gsig H z s` -> `Gres H z s`; list `gloop L W H z I` -> `loopL d L W H z I` (`loopL` is `trace (gloopProd ..)` by `rfl`, `GLoopFlow.lean:123`); `Eblk`, `Gres`, `gloopProd`, `blockMat` live in `RBM.Gauss` (RBM2D: `RBM`), so the new file is in `namespace RBM.Gauss`.
Inputs absent from main (all provable inside the sole file, hence not BLOCKED; `grep -rnw` count 0 for each): `sum_Eblk` (Drift:33 uses it; 4-line `ext` proof, RBM2D `Defs/Model.lean:83`); `Svar_apply` (replaced by `svar` unfolding); `coordinateMatrix_apply` (`rfl`, RBM2D `Gauss/Model.lean:280`); `cutGlue_split` and `gloopProd_cutGlue_split` (RBM2D `Operations.lean:40,83`; main has `cutGlue` `GLoopFlow.lean:317` but only the two-edge splits); `gloopProd_cons`/`gloopProd_append` exist but are **private** (`GLoopFlow.lean:394,401`): copy as private, file-stem-prefixed. `blockRelabel` (Sum:156, referenced by ST-2) equals merged `blockMat` (`GLoopFlow.lean:105`) by `rfl`; keep the name `blockRelabel` as the portmap lists it. Name clash grep of all 32 public RBM2D names against `RBM3D RBM3D.lean`: 0 hits each. Drop none of the 32 public declarations (P.7 marks as unreferenced only for ST-2..ST-6; the others are ST-1 internal).

### (ii) One concrete nondegenerate instance
`d=3, L=3, W=2, g=1/2`; `N=(WL)^d=216=27*8`; random complex dense `A, C` (216x216), random Hermitian `H/sqrt(N)`, `z=0.3+0.2i`, `m=0.7-0.2i`. Loops: (3) `sigma_1=(+,-), a_1=(4,17), sigma_2=(-,+), a_2=(9,22), s=+, a=5`; (4) `sigma_1=(+,-), sigma_2=(-), sigma_3=(+), s=+, t=-` (so `k=3, l=5`, loop length 7, lengths equal as `h_1,h_2` require). Blocks, `SB`, `E_a`, `X_c` (from `Xentry`, all 2*216^2 coordinates), `cutGlue/cutGlueL/cutGlueR` (`TreeRep.lean:84-95`, `GLoopFlow.lean:317`) implemented from their definitions. Checks: (1) `sum_Svar_diag_mul`; (2) `sum_allCoords_trace_blocks` (honest sum over all coordinates, including unused ones); (3) `neg_trace_scalarDrift_cutGlue_split`; (4) `sum_coordinate_cutChains` (full coordinate sum of the two chains).
Command (script `sha256` prefix 0cf3d55c9bf29931, 86 lines, python3+numpy; not Lean): `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2032_check.py`
```
(1) sum_Svar_diag_mul   |lhs-rhs|/|lhs| = 7.698707714965962e-15  |lhs| = 1.209379789862584
    d=2 coefficient W^2 in place of W^d: lhs/rhs_with_W^2 = 2.000000000000011 (= W^(d-2) = 2 )
(2) sum_allCoords_trace_blocks |lhs-rhs|/|lhs| = 2.6788049766420597e-15  |lhs| = 4.527917838893143
(3) neg_trace_scalarDrift_cutGlue_split |lhs-rhs|/|lhs| = 4.469665889549424e-16  |lhs| = 4.88348345856419e-07
(4) sum_coordinate_cutChains |lhs-rhs|/|lhs| = 1.7249596282331235e-15  |lhs| = 3.810446339050524e-09
params: d=3 L=3 W=2 g=0.5 N=(WL)^d=216 W^d=8 blocks=27
```
All four hold to 1e-15 relative; with `W^2` in place of `W^d` (1) fails by the factor `W^(d-2) = 2`. No external hypothesis enters, so no limit computation applies. Lean instances (stage 1b) can use these data (`d=3,L=3,W=2`, `NeZero` by `inferInstance`/`⟨by norm_num⟩`, nonempty lists above, `A=C=1` or `H=1,z=i` for the matrix arguments); the statements are unconditional matrix identities, so the `sz0` data (`L=4,W=32`, `N=2097152`) are only needed if the ticket insists on them.

### Verdict
- sum_Svar_diag_mul (Basic:47): PASS. weighted_trace_coordinate_diag (Directions:189): PASS. sum_usedCoords_trace_blocks (Sum:201): PASS. sum_allCoords_trace_blocks (Unused:110): PASS. sum_coordinate_cutChains (CutWords:87): PASS. neg_trace_scalarDrift_cutGlue_split (Drift:66): PASS.
- Hypotheses hold simultaneously (numbers above), the only exponent change is `W^2 -> W^d` (with `W^{-2} -> W^{-d}`, fibre `Fin (W^d)`), slack none (exact identities). Dimension-free: Directions (8 of 9 theorems), Unused (first four), the upper-triangular sum, all trace/chain algebra.

## (b) Script output — stage 1b, commits `8112e75`, `8de0ca4` (docstring line citations only) on `t/T2032`, Sat Oct  3 05:54 UTC 2026

New file: `RBM3D/Hierarchy/ContractionBasic.lean` (934 lines). Ports the six files `RBM2D/Hierarchy/Contraction{Basic,Directions,Sum,Unused,CutWords,Drift}.lean` at RBM2D `c9a24cf`; the line of each ported declaration is in its docstring.

### Build (`lake build RBM3D.Hierarchy.ContractionBasic`) and the full `lake build` before the commit
```
$ lake build RBM3D.Hierarchy.ContractionBasic | tail -2
Build completed successfully (3294 jobs).
full lake build: "Build completed successfully (3729 jobs)." (root `#assert_rbm_axioms` passed)
```

### No `sorry`/`admit`/`native_decide`/`axiom` in the file
```
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Hierarchy/ContractionBasic.lean; echo rc=$?
rc=1
```

### `#print axioms` of the six key targets
```
'RBM.Gauss.sum_Svar_diag_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.weighted_trace_coordinate_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.sum_usedCoords_trace_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.sum_allCoords_trace_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.sum_coordinate_cutChains' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.neg_trace_scalarDrift_cutGlue_split' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All 33 public declarations print `[propext, Classical.choice, Quot.sound]` (script: `#print axioms` over every `theorem`/`def` name of the file; 0 occurrences of `sorryAx`).

### Registry pre-check (DECISIONS §20; scratch file outside the repository: `import RBM3D`, `import RBM3D.Hierarchy.ContractionBasic`, `#assert_rbm_axioms`)
```
$ lake env lean <scratch>/reg.lean   (full output is 40 lines; the lines with counts and the exit code)
axiom audit: 1088 theorems, 404 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
premises found by scanning: 8 (borrowed 3, owed 0, structural 5).
registry: 11 borrowed + 2 owed + 13 structural; 18 registered premise(s) carry nothing yet: [RBM.ThetaDecay,
exit 0
```
The file defines no `Prop`-valued predicate, so no registry line is appended (`RBM3D/Test/Axioms.lean` untouched).

### Target statements (extracted by script from the file: `theorem NAME` up to `:= by`)
```lean
theorem sum_Svar_diag_mul [NeZero W]
    (A C : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ i : Vtx d L W, ∑ j : Vtx d L W,
        ((svar d L W g i j : ℝ) : ℂ) * (A i i * C j j) =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        Matrix.trace (A * Eblk d L W a) * SB d L g a b *
          Matrix.trace (C * Eblk d L W b) := by
theorem weighted_trace_coordinate_diag
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) (i : Idx d L W) :
    (((gvarF d L W g (i, i, true) : ℝ) : ℂ) *
      Matrix.trace (A * coordinateMatrix d L W (i, i, true) * C *
        coordinateMatrix d L W (i, i, true))) =
      ((svarF d L W g i i : ℝ) : ℂ) * (A i i * C i i) := by
theorem sum_usedCoords_trace_blocks
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c ∈ usedCoords d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        Matrix.trace (blockRelabel d L W A * Eblk d L W a) * SB d L g a b *
          Matrix.trace (blockRelabel d L W C * Eblk d L W b) := by
theorem sum_allCoords_trace_blocks
    (A C : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∑ c : CoordF d L W,
        (((gvarF d L W g c : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W c * C * coordinateMatrix d L W c)) =
      (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
        Matrix.trace (blockRelabel d L W A * Eblk d L W a) * SB d L g a b *
          Matrix.trace (blockRelabel d L W C * Eblk d L W b) := by
theorem sum_coordinate_cutChains [NeZero W]
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c : Zd d L)
    (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) :
    let A := (cutLeftChain d L W H z σ₁ σ₃ a₁ a₃ s t c).submatrix
      (split d L W) (split d L W)
    let C := (cutRightChain d L W H z σ₂ a₂ s t a).submatrix
      (split d L W) (split d L W)
    ∑ γ : CoordF d L W,
        (((gvarF d L W g γ : ℝ) : ℂ) *
          Matrix.trace (A * coordinateMatrix d L W γ * C *
            coordinateMatrix d L W γ)) =
      (W : ℂ) ^ d * ∑ u : Zd d L, ∑ v : Zd d L,
        loopL d L W H z
          ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
              a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
            (σ₁.length + 1) (σ₁.length + σ₂.length + 2) u) *
          SB d L g u v *
        loopL d L W H z
          ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
              a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
            (σ₁.length + 1) (σ₁.length + σ₂.length + 2) v) := by
theorem neg_trace_scalarDrift_cutGlue_split [NeZero W]
    (σ₁ σ₂ : List Bool) (a₁ a₂ : List (Zd d L))
    (s : Bool) (a : Zd d L) (m : ℂ)
    (h₁ : σ₁.length = a₁.length) :
    -Matrix.trace (gloopProd d L W H z ⟨σ₁, a₁⟩ *
      (Gres H z s * (m • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
        (Gres H z s * Eblk d L W a * gloopProd d L W H z ⟨σ₂, a₂⟩))) =
      -(m * (W : ℂ) ^ d) *
        ∑ b : Zd d L,
          loopL d L W H z
            ((⟨σ₁ ++ s :: σ₂, a₁ ++ a :: a₂⟩ : Loop.LoopIdx (Zd d L)).cutGlue
              (σ₁.length + 1) b) := by
```

### Compiled nonempty instances (section 7 of the file, `namespace ContractionInst`, docstrings omitted), d = 3, L = 3, W = 2, g = 1/2
```lean
namespace ContractionInst
private def lab (n : ℕ) : Zd 3 3 := fun i => ((n + i.val : ℕ) : ZMod 3)
example :
    ∑ i : Vtx 3 3 2, ∑ j : Vtx 3 3 2,
        ((svar 3 3 2 (1 / 2) i j : ℝ) : ℂ) *
          ((1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) i i *
            (Eblk 3 3 2 (lab 1) : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) j j) =
      (2 : ℂ) ^ 3 * ∑ a : Zd 3 3, ∑ b : Zd 3 3,
        Matrix.trace ((1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) * Eblk 3 3 2 a) * SB 3 3 (1 / 2) a b *
          Matrix.trace (Eblk 3 3 2 (lab 1) * Eblk 3 3 2 b) := by
  have h := sum_Svar_diag_mul 3 3 2 (1 / 2) (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)
    (Eblk 3 3 2 (lab 1))
  exact_mod_cast h
example :=
  weighted_trace_coordinate_diag 3 3 2 (1 / 2)
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) 0
example :=
  sum_usedCoords_trace_blocks 3 3 2 (1 / 2)
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
example :=
  sum_allCoords_trace_blocks 3 3 2 (1 / 2)
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
example :=
  sum_coordinate_cutChains 3 3 2 (1 / 2) (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
    [true, false] [false, true] [true] [lab 4, lab 17] [lab 9, lab 22] [lab 0]
    true false (lab 5) (lab 2) rfl rfl
example :=
  neg_trace_scalarDrift_cutGlue_split 3 3 2 (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
    [true, false] [false, true] [lab 4, lab 17] [lab 9, lab 22] true (lab 5)
    ((7 : ℂ) / 10 - Complex.I / 5) rfl
end ContractionInst
```

### Statement diff against RBM2D (`c9a24cf`), by script: RBM2D signature text, renamed by R1-R4, against the new file; only differing declarations are shown
```
22 declarations are EQUAL after renaming. Differing ones (2D->3D token changes):
DIFF  trace_mul_Eblk
     2D->3D: (d L W : ℕ) [NeZero L] => 
DIFF  sum_Svar_diag_mul
     2D->3D: (d L W : ℕ) [NeZero L] => 
     2D->3D: 2 => d
     2D->3D:  => g
NEW   blockRelabel_eq_blockMat
NEW   sum_svarF_diag_mul_relabel
DIFF  sum_usedCoords_trace_blocks
     2D->3D: 2 => d
     2D->3D:  => g
DIFF  sum_allCoords_trace_blocks
     2D->3D: 2 => d
     2D->3D:  => g
DIFF  trace_cutLeftChain_Eblk
     2D->3D: gloop => loopL
DIFF  trace_cutRightChain_Eblk
     2D->3D: gloop => loopL
DIFF  sum_gloop_cutGlue_split
     2D->3D: gloop => loopL
DIFF  trace_scalarDrift_cutGlue_split
     2D->3D: 2) => d)
     2D->3D: gloop => loopL
DIFF  neg_trace_scalarDrift_cutGlue_split
     2D->3D: 2) => d)
     2D->3D: gloop => loopL
```
Explanation of every residual: `(d L W : ℕ) [NeZero L]` is a `variable` of the section in the new file (the script extracts only the statement); `2 => d` is `(W : ℂ) ^ 2` becoming `(W : ℂ) ^ d` (the script rename list only covers `W^2` without spaces); `=> g` is the new argument `g` of `svar`, `svarF`, `gvarF`, `SB`; `gloop => loopL` is the list-based loop (`loopL` is `trace (gloopProd ..)` by `rfl`); `2) => d)` is `m * W^2` to `m * W^d`. Two NEW names: `blockRelabel_eq_blockMat` (`rfl` to merged `blockMat`) and `sum_svarF_diag_mul_relabel` (RBM2D `sum_Spaper_diag_mul_relabel`, renamed because `Spaper` has no analogue).

### Name-clash grep (33 public names against `RBM3D RBM3D.lean`, excluding the new file)
```
$ for x in <33 public names>; do grep -rnw "$x" RBM3D RBM3D.lean | grep -v ContractionBasic.lean | wc -l; done  (printing only nonzero)
checked 33 public names; no name had a hit
```

### RBM2D diff-stat (ports; `git -C ../RBM2D --no-optional-locks`, RBM2D HEAD `9e0f275`)
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Hierarchy/Contraction{Basic,Directions,Sum,Unused,CutWords,Drift}.lean
 RBM2D/Hierarchy/ContractionDirections.lean | 17 -----------------
 RBM2D/Hierarchy/ContractionUnused.lean     |  3 +--
 2 files changed, 1 insertion(+), 19 deletions(-)
```
The port is from `c9a24cf` as the ticket says; RBM2D HEAD has dropped `weighted_trace_coordinate_offDiag_blocks` from Directions and reworded a Unused docstring since. Dropped from the port: none (the ticket lists `sum_Spaper_diag_mul_relabel` among the others; it is ported renamed).

### `d = 2` tokens of the portmap (section (a) table), where each went
```
$ grep -c "Z2\|W\^2\|d = 2" RBM3D/Hierarchy/ContractionBasic.lean  ->  3 (docstring lines 15, 16, 879 that name the renaming; no code token)
```
W2 and inv2 tokens became `W^d`, `((W:ℂ)^d)⁻¹`; Z2 tokens became `Zd d L`, `Idx d L W`, `Vtx d L W`; the fibre `Fin W × Fin W` became `Fin (W ^ d)` (in `trace_mul_Eblk` and `sum_Svar_diag_mul`). Dimension-free as claimed in (a): the eight direction theorems except `_blocks`, the first four of `Unused`, the upper-triangular sum, all chain algebra.

### Narrative
- All six files are in one namespace `RBM.Gauss` (RBM2D: `RBM` for Basic, CutWords, Drift and one lemma of Sum; `RBM.Gauss` for Directions, Unused and the rest of Sum), because the merged `Eblk`, `Gres`, `gloopProd`, `blockMat` live in `RBM.Gauss`.
- The proofs are RBM2D's with `d`, `g` inserted; the only changed proof steps are: `Svar_apply` replaced by the private `contraction_svar_apply` (entrywise `W^{-d} SB` through `SB_eq_map_SBR`); `svar_cast_eq_Spaper`/`Spaper_eq`/`Spaper_transpose` replaced by `svarF`, `svarF_comm`, `SB_eq_map_SBR`; `gvar_diag`, `gvar_offDiag`, `coordinateMatrix_apply` re-proved as private `contraction_*` (the merged copies `fineModel_gvarF_*` are private).
- Private helpers (file-stem prefix `contraction_`): `svar_apply`, `coordinateMatrix_apply`, `gvarF_diag`, `gvarF_offDiag`, `sum_orderedPairs_from_upper`, `sum_Eblk`, `loopL_eq`, `gloopProd_cons`, `gloopProd_append`, `cutGlue_split`, `gloopProd_cutGlue_split`. `gloopProd_cons`, `gloopProd_append` are private in `GLoopFlow.lean:394,401`; `sum_Eblk` (`RBM2D/Defs/Model.lean:83`), `cutGlue_split`, `gloopProd_cutGlue_split` (`RBM2D/Hierarchy/Operations.lean:40,83`) are absent from `main`: copied from RBM2D, not imported.
- `blockRelabel` keeps RBM2D's name (the portmap lists it for ST-2); it is the merged `blockMat` by `rfl` (`blockRelabel_eq_blockMat`).
- `set_option linter.unusedSectionVars false` is set for the file: the section variables `[NeZero L] [NeZero W]` are needed for the `Fintype` instances of `Idx d L W`, `Vtx d L W` even where the statement text does not mention them.
- No hypothesis was added; no statement was weakened. Statements are unconditional matrix identities (only `[NeZero L] [NeZero W]` and, for the cut words, `|σ_i| = |a_i|`), as in (a). No `3 ≤ d`, `3 ≤ L`.
- These are matrix-algebra lemmas, not the general loop-hierarchy statement: no generator, expectation or derivative is asserted (the docstrings of RBM2D say the same).
- Instances: every target applied at `d = 3, L = 3, W = 2` with nonempty chains of length 7; the matrix arguments are `1` and `Eblk`/`Complex.I`, not zero. The identity `sum_Svar_diag_mul` is instantiated with `A = 1`, `C = Eblk 3 3 2 (lab 1)` and the conclusion is stated in full in the example.

## (c) Verified Mathlib names used (all by compilation of the file)
`Matrix.single`, `Matrix.single_apply`, `Matrix.trace_mul_comm`, `Matrix.trace_add`, `Matrix.trace_sum`, `Matrix.trace_smul`, `Matrix.mul_diagonal`, `Matrix.diagonal_apply`, `Matrix.sum_apply`, `Matrix.one_apply`, `Fintype.sum_prod_type`, `Fintype.sum_equiv`, `Fintype.sum_bool`, `Finset.sum_subset`, `Finset.sum_filter`, `Finset.sum_comm`, `Finset.sum_mul_sum`, `Finset.sum_add_distrib`, `Finset.sum_ite_eq`, `sum_ite_irrel`, `List.take_append`, `Complex.I_mul_I`. Names verified absent from `main` (grep `-rnw` over `RBM3D RBM3D.lean`, 0 hits): `sum_Eblk`, `cutGlue_split`, `gloopProd_cutGlue_split`, `coordinateMatrix_apply`, `Svar`, `Spaper`.

## (d) Open issues and paper-delta candidates
- T2032a: RBM2D's complex `Svar`, `Spaper` (and `svar_cast_eq_Spaper`, `Spaper_eq`) have no analogue; statements use `((svar d L W g i j : ℝ) : ℂ)` (Basic) and `((svarF d L W g i j : ℝ) : ℂ)` (Directions, Sum) and `SB d L g a b`; `sum_Spaper_diag_mul_relabel` is named `sum_svarF_diag_mul_relabel`. Renaming only, no loss changes.
- T2032b: the Basic, Sum-lemma, CutWords and Drift theorems of RBM2D sit in namespace `RBM`; here all are in `RBM.Gauss` (names `RBM.Gauss.sum_Svar_diag_mul`, `RBM.Gauss.neg_trace_scalarDrift_cutGlue_split`, `RBM.Gauss.blockRelabel`, ...). Later tickets must cite them with that prefix.
- T2032c: the contraction coefficient is `W^d` (RBM2D `W^2`), the `E_a` weight `((W:ℂ)^d)⁻¹`; the fibre of a block is `Fin (W^d)`; exact identities, checked in (a) at `d = 3, W = 2, L = 3` (relative error 1e-15; the 2D coefficient fails by `W^(d-2)`).
- No open issues. Nothing in this file is an external input or a Prop-valued hypothesis.
