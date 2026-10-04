Auditor model: claude-opus-5-5

# T2091 audit (S1-23, `Green/IBP.lean`), round 1 — Sun Oct  4 01:16:57 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2091-audit1`, detached at `t/T2091` = `e667488`.
No pinned statement text (check file is `#check`-only): statements are judged by ST1-COMMON item 6
(equality with RBM2D `Green/IBP.lean` at `c9a24cf` after R1–R4) and the ticket's `gaussIBP sz` rule.

## 1. Diff scope
```
$ git diff --name-only main...t/T2091
RBM3D/Green/IBP.lean
$ grep -nE "^import" RBM3D/Green/IBP.lean
6:import RBM3D.Green.IBPPoly
7:import RBM3D.Green.FlucVanish
8:import RBM3D.Green.LDE
```
Only the sole writable file (new); `RBM3D/Test/Axioms.lean` untouched; no frozen signature touched; no `RBM3D`/ST-2+ import.

## 2. Statements (independent script diff, auditor's own renaming)
`adiff.py`: every public `theorem/def` header up to `:=`, RBM2D lines 1–1346 vs RBM3D lines 1–1389;
renaming: drop `(hG : GaussIBP d)`; word `d`→`sz`; `Sizes`→`Sizes d`; `Idx/Bmat/usedCoords`→`… d`;
`Coord`→`CoordF d`; `svar (sz.L n) (sz.W n)`→`svarF d (sz.L n) (sz.W n) (sz.lam n)`; `spectralZ/M`→`zt/mE`.
```
$ python3 adiff.py rbm2d_ibp.lean RBM3D/Green/IBP.lean
RBM2D public decls (1-1346): 27  RBM3D public decls (1-1389): 27
== DIFF IBP_sum_svar_row
  2D(ren): theorem IBP_sum_svarF_row {L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (i : Idx d L W) : ∑ k : Idx d L W, svarF d L W g i k = 1
  3D     : theorem IBP_sum_svarF_row {L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L) (i : Idx d L W) : ∑ k : Idx d L W, svarF d L W g i k = 1
extra in RBM3D: []
differing: 1
```
- 26/27 identical after renaming; none dropped, none added. The one residual difference is the coupling
  `g` that the merged `svarF d L W g` needs (D130); RBM2D's `svar L W` had no `g`. Statement content is
  `Σ_k svarF(i,k) = 1` for every `g`, `3 ≤ L`: the d-dimensional row sum. Accepted.
- Key target `ibpRem_eq_add` (IBP.lean:1344) and `ibpRem` (1331): identical to RBM2D IBP:1311/1298
  after renaming, minus `hG`. Mathematics: `E_i[G_ii(G_kk−m)] − m(G_kk−m) = E_i[(G_ii−m)(G_kk−m)] + m(E_i(G_kk−m) − (G_kk−m))`;
  hypotheses `|E| < 2`, `t < 1` (tameness), `i k ω` arbitrary. Quantifier order and index ranges unchanged.
- `condExpDiag_eq_sum_Sblk` (1227): weight is `svarF d (sz.L n) (sz.W n) (sz.lam n)` (the merged D129–D130
  profile), factor `t·m`, no error term — same as RBM2D.
- `GaussIBP` dropped from the 10 statements that took it (`hG`); the ticket says to discharge it with
  `gaussIBP sz` "unless a later pin keeps it". Grep of tickets/checks for later pins:
```
$ grep -rnE "ibpRem|condExpDiag_eq_sum_Sblk|IBP_sum_svar" docs/tickets/*.md docs/tickets/checks/ | grep -v T2091
docs/tickets/QUEUE.md:9:| T2091 | S1-23 | 证明（Green/IBP：ibpRem_eq_add） | prover-hard | 同上 |
```
  No pin keeps it; the statements without the premise are stronger. Merged `gaussIBP`:
```
@RBM.Green.gaussIBP : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d), RBM.Green.GaussIBP sz
```
- Variance profile used (merged, not redefined here):
```
def RBM.Gauss.svarF : (d L W : ℕ) → ℝ → [NeZero W] → RBM.Gauss.Idx d L W → RBM.Gauss.Idx d L W → ℝ :=
fun d L W g [NeZero W] i j => (↑W ^ d)⁻¹ * RBM.SBR d L g (RBM.Gauss.split d L W i).1 (RBM.Gauss.split d L W j).1
RBM.Gauss.svarF_diag : ... RBM.Gauss.svarF d L W g i i = (↑W ^ d)⁻¹ * (1 + 2 * ↑d * g ^ 2)⁻¹
```
- `d = 2` tokens / §30 scales in the RBM2D source (code lines ≤ 1346) and in the port:
```
$ grep -cE "UniformWeight|BoundedWeight|scaleM|ellT|ellStar|tailT|Meta|ellz" rbm2d_ibp.lean
0
$ grep -nE "W ?\^ ?2|W²|\(W \* L\) \^ 2|Z2|zdist2|1 ?/ ?5" rbm2d_ibp.lean | awk -F: '$1<=1346'
51:  on the fine index `Idx L W = Z2 (W L)` (DECISIONS §58).  ...      (module docstring)
53:  variance is `svar ≤ (5 W²)⁻¹`.  ...                                 (module docstring)
$ grep -nE "W ?\^ ?2|W²|Z2|zdist2|1 ?/ ?5" RBM3D/Green/IBP.lean
17:(item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L`/`Idx L W` become `Zd d L`/`Idx d L ...  (docstring)
```
No `d = 2` exponent in any declaration; no BoundedWeight step needed (DECISIONS §30 not triggered).

## 3. Hidden hypotheses, vacuity, cycles
- No new structure, class or `Prop` predicate in the file. The only structure argument is the merged
  `Sizes d` (`#print`: fields `L W : ℕ → ℕ`, `lam : ℕ → ℝ`, `three_le_L`, `W_pos`), instantiated below.
- No external hypothesis remains (`GaussIBP` is discharged by the merged theorem), so no limit check is due.
- No cycle: imports are three merged `Green/*` modules; no merged file consumes the new names.

## 4. Compiled nonempty instances (`section Checks`, IBP.lean:1390–1685)
Data `ckS : Sizes 3`: `L = 3`, `W = 2`, `lam = 1/2` (`three_le_L := le_rfl`, `W_pos` by `norm_num`),
slice `n = 0`, `E = t = u = 1/2`, sites `x0 = (0,0,0)`, `x1 = (1,0,0)`, `x2 = (0,1,0)` of `Z_6^3`.
Every hypothesis discharged by a closed proof (`ck_hE`, `ck_hE2`, `ck_ht`, `ck_ht0` by `norm_num`;
`ckp0_used`, `ckp1_used`, `ck_offDiag`, `ck_x01/x20/x21` proved). Key endpoint:
```
1618 example (ω : Sizes.SeqΩ ckS) :=
1619   ibpRem_eq_add (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht ckx0 ckx1 ω
1621 example (ω : Sizes.SeqΩ ckS) :=
1622   ibpRem_eq_add (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht ckx0 ckx0 ω
1604   condExpDiag_eq_sum_Sblk (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_hE2 ck_ht0 ck_ht ckx0 ω
1661 example : ∑ k : ckI, svarF 3 (ckS.L 0) (ckS.W 0) (ckS.lam 0) ckx0 k = 1 :=
1662   IBP_sum_svarF_row (ckS.lam 0) (ckS.three_le_L 0) ckx0
```
Compiled nondegeneracy: `card ckI = 216` (1670), `svarF(x0,x0) = 1/20` (1664), `seqGvar = 1/20` (1674).
All 27 public names are applied in some `example` (lines 1463–1662 inspected); no `False` premise.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Green.IBP 2>&1 | tail -1      (IBP.olean absent from main's cache; fresh compile)
Build completed successfully (3335 jobs).
$ grep -E "^(warning|error)" build.log | awk -F: '{print $2}' | sort | uniq -c
   1  RBM3D/Green/FlucVanish.lean
  14  RBM3D/Green/IBPPoly.lean
  18  RBM3D/Green/LDEQuad.lean
  20  RBM3D/Green/LDEQuadMom.lean
```
(0 warnings/errors in `Green/IBP.lean`; the 53 are linter warnings in merged files.)
```
$ grep -nE "sorry|admit|native_decide|^\s*axiom\b|implemented_by|extern" RBM3D/Green/IBP.lean
grep_exit=1
$ lake env lean Ax.lean     (#print axioms of all 27 public declarations)
exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
27
'RBM.Green.IBP_sum_svarF_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.condExpDiag_eq_sum_Sblk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.ibpRem' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.ibpRem_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (ST1-COMMON item 8):
```
$ lake build RBM3D 2>&1 | tail -1
Build completed successfully (3833 jobs).
$ printf 'import RBM3D\nimport RBM3D.Green.IBP\n#assert_rbm_axioms\n' > Pre.lean; lake env lean Pre.lean
exit=0
axiom audit: 2973 theorems, 1137 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
14:  RBM.Green.GaussIBP: 23 [no certificate]
```
Same `GaussIBP` dependent count as main (23, prove report baseline); no registry line needed.

## 6. Paper deltas
- `T2091a` (proposed in prove report (d)): the file proves the dimension-independent identity behind
  `(GavLGEX)`, which `paper/tex/3_5_Loop_Hierarchy.tex` leaves to `[YY_25]` Lemma 4.1:
```
These estimates have been proven as Lemma 4.1 in \cite{YY_25} for 1D random band matrices. However, their proofs are dimension-independent ...
```
- Cited signed entries exist: `docs/paper-deltas.md:5` D1 (`3 ≤ L`), `:523` D129, `:527` D130, `:635` D157.
- The `hG` drop and the extra `g` of `IBP_sum_svarF_row` are port differences relative to RBM2D, not
  Lean/paper differences; both are listed in the prove report (narrative 3–4). Coverage complete.

## Observations (no verdict effect)
- O1. S1-24 (`CondDom`) / S1-29 (`IBPRem`) ports must call these theorems without RBM2D's `hG` argument.
- O2. The example at IBP.lean:1589 concludes `True` (redundant; the theorem is applied at 1577–1583).

## Verdict
| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `ibpRem_eq_add` (+ `ibpRem`) | = RBM2D after renaming, `hG` discharged | none | 1618, 1621 | ok | T2091a | **PASS** |
| `condExpDiag_eq_sum_Sblk` | = RBM2D, `svarF` profile | none | 1597 | ok | T2091a | **PASS** |
| `IBP_sum_svarF_row` | + `g` (D130), d-dim row sum | none | 1661 | ok | D1, D130 | **PASS** |
| other 23 public ported decls | identical after renaming | none | 1463–1587 | ok | — | **PASS** |

**T2091: PASS.** No dispatcher sign-off needed.
