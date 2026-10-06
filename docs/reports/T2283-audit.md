Auditor model: claude-opus-5-5

# T2283 audit (round 1): BA-D3 `RBM3D/BA/Ward.lean`. Written Tue Oct  6 11:17:15 UTC 2026 (`date -u`)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2283-audit1`, detached at `t/T2283` = 2056e33; merge-base with `main` f3e7c74.

## 1. Scope, hygiene, imports (§4 item 4)

```
$ git diff --name-status main...t/T2283
A	RBM3D/BA/Ward.lean
$ git diff --stat main...t/T2283
 RBM3D/BA/Ward.lean | 427 +++++
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/BA/Ward.lean
0
$ grep -c "seqP\|Prec\|SeqΩ\|Sizes" RBM3D/BA/Ward.lean      # §57 (3)
0
$ grep -n "^import" RBM3D/BA/Ward.lean
6:import RBM3D.BA.MFixedPoint
$ grep -nE "^(theorem|def|private theorem)" RBM3D/BA/Ward.lean   (abridged)
39/44/49: private theorem Ward_BAMB_eq / Ward_adj_symm / Ward_adj_shift
53 BAMB_shift  74 BAMB_transpose  83 BAMB_symm  89 BAMB_diag_eq  108 BAMB_ward_row  125 BAMB_row_sq_real
136 BAm_norm_le_one  158 baWard_holds  172 def BAPropM12  183 baPropM12_holds  193 BAnorm_one_sub_tm2_sq
202 BAoffDiag_scalar  267 BAMss_pp_apply  275 BAoffDiag_row_sum  289 BAoffDiag_of_real  303 baOffDiag_holds
394 WardInst.ward_scalar_inst_norm  401 WardInst.ward_scalar_inst_im
$ for n in ward_scalar_inst_norm ward_scalar_inst_im BAPropM12 baWard_holds baOffDiag_holds BAMB_shift WardInst; do git grep -lw $n main -- RBM3D | wc -l; done
0 0 0 0 0 0 0
```
Only the sole writable file is touched; `MFixedPoint.lean` (frozen pins `BAWard`, `BAPropM`, `BAoffDiag`) unchanged. Imports exactly `RBM3D.BA.MFixedPoint`.

## 2. Build and axioms

```
$ lake build RBM3D.BA.Ward
⚠ [3332/3332] Built RBM3D.BA.Ward (14s)
warning: RBM3D/BA/Ward.lean:16:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3332 jobs).
exit 0          (0 lines starting with "error")
```
`#print axioms` of the 15 public theorems + 2 instance theorems (scratch file of §3, same `lake env lean` run, exit 0):
```
$ grep "depends on axioms" eq.out | sed 's/.*depends on axioms: //' | sort | uniq -c
  17 [propext, Classical.choice, Quot.sound]
$ grep "depends on axioms" eq.out | sed "s/' depends.*//; s/^'RBM.BA.//" | tr '\n' ' '
baWard_holds BAMB_shift BAMB_transpose BAMB_symm BAMB_diag_eq BAMB_ward_row BAMB_row_sq_real BAm_norm_le_one
baPropM12_holds BAnorm_one_sub_tm2_sq BAoffDiag_scalar BAMss_pp_apply BAoffDiag_row_sum BAoffDiag_of_real
baOffDiag_holds WardInst.ward_scalar_inst_norm WardInst.ward_scalar_inst_im
```
Registry pre-check (`import RBM3D` + `import RBM3D.BA.Ward` + `#assert_rbm_axioms`, `lake env lean`):
```
exit 0
axiom audit: 8228 theorems, 2669 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms ...
```
No registry line needed (no file outside Ward.lean touched; matches ticket Targets 3).

## 3. Statements against the pins (script, compiled)

Scratch file = check file lines 16-20 (imports) + `import RBM3D.BA.Ward` + check file lines 21-end + 16 equality
examples + the `#print axioms` lines above:
```
example : RBM.BA.T2283Check.BAPropM12 = RBM.BA.BAPropM12 := rfl
example : RBM.BA.T2283Check.<Y>_pin := @RBM.BA.<Y>      -- Y ∈ {BAMB_shift, BAMB_transpose, BAMB_symm,
   BAMB_diag_eq, BAMB_ward_row, baWard_holds, BAMB_row_sq_real, BAm_norm_le_one, baPropM12_holds,
   BAnorm_one_sub_tm2_sq, BAoffDiag_scalar, BAMss_pp_apply, BAoffDiag_row_sum, BAoffDiag_of_real, baOffDiag_holds}
$ grep -c "^example : RBM.BA.T2283Check" eqcheck.lean
16
$ lake env lean eqcheck.lean ; echo "exit $?"
exit 0          (no line containing "error")
```
So every public theorem has exactly the pinned type, `BAPropM12` is definitionally the pinned body, and
`baWard_holds : ∀ d, BAWard d`, `baOffDiag_holds : ∀ d Λ κ, BAoffDiag d Λ κ` close the merged frozen pins
(`MFixedPoint.lean` `BAWard`, `BAoffDiag`, read in this worktree) with no added hypothesis.

Mathematics (read from the signatures):
- `BAWard`: translation invariance, `M_aa = m`, `(Im m + Im z) Σ_b|M_ab|² = Im m` for `0 ≤ Im z`, `BASelf`.
  At `Im z = 0` this is `lem:propM` (1) and `(eq:WardM)` (`7_8:1853, 1864-1869`); for `Im z > 0` a strict generalization.
- `BAPropM12`: the first four conjuncts of `BAPropM` verbatim (`MFixedPoint.lean` `BAPropM`), under `BASelf` at real
  `E` (weaker than `BAReal`, so the conclusion is at least as strong as needed by BA-D4). Not a special case:
  quantifiers `∀ L ≥ 3, g > 0, E, m` as in `BAPropM`. `BAPropM` itself is not claimed (correct per ticket).
- `BAoffDiag`: `∃ ε > 0` quantified before `L, g, E, m, t` (§18; `ε = κ²/4` depends on `κ` only), conclusion
  `ε ≤ |1−tm²|` and `Σ_{a≠0}|M^{(+,+)}_{0a}| ≤ (1−ε)|1−tm²|` for all `t ∈ [0,1]`, matching `A:32-34`
  ("`|1−tm²| ≥ ε` and `Σ_{a≠0}|M'_{0a}| = 1−|m|² ≤ (1−ε)|1−tm²|, ∀ t ∈ [0,1]`"; off-diagonal entries of `M'` equal
  those of `M^{(+,+)}`). The equality `= 1−|m|²` is proved separately as `BAoffDiag_row_sum`.
Result: PASS for all statements.

## 4. Hidden hypotheses, vacuity, cycles

- No new structure; hypotheses are `BASelf` (`0 < Im m ∧ m = L^{-d} tr M`), `BAReal` (`BASelf ∧ κ ≤ Im m`), and
  scalar bounds, all in the signatures. Both are inhabited by merged data: `selfS 4 10` (`BASelf 3 4 10 (zS 4 10) (mS 4 10)`)
  and `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0` (`FlowPt` field, merged T2189), used in §5.
- Dependencies: only merged `RBM3D.BA.MFixedPoint` names (`BAimInv_diag`, `BAPsi_isHermitian`, `BAcard_Zd`, `BAMB`,
  `Mres`, `PsiB`, `Adj`, `zdistD_neg`) and Mathlib (`Matrix.inv_submatrix_equiv`, `Matrix.transpose_nonsing_inv`,
  `Matrix.nonsing_inv_eq_ringInverse`, `Finset.add_sum_erase`, `Complex.sq_norm`). No owed pin is a hypothesis of any
  theorem; no cycle (Ward.lean imports only MFixedPoint; MFixedPoint does not import Ward).
- Unused pin premises (`3 ≤ d`, `0 < Λ`, `g ≤ Λ`, `0 < g`; `3 ≤ L` only through `NeZero L`) are visible in
  `baWard_holds`/`baOffDiag_holds` (`intro _ _ hκ`, `hg`, `hgΛ` unused): stronger results, as the ticket states.

## 5. Compiled nonempty instances (`RBM.BA.WardInst`, Ward.lean:314-423; compiled in the build of §2)

| endpoint | instance (line) | data | open hypotheses |
|---|---|---|---|
| `baWard_holds` | 319, 327 | `d=3, L=4, g=10, (zS 4 10, mS 4 10)` (`Im z>0`); `P` (`g=P.g0`, real `P.E`) | none |
| `baPropM12_holds` | 334 | `P`, `P.g0_pos`, `P.real.1` | none |
| `BAMB_shift/_transpose/_symm/_diag_eq/_row_sq_real`, `BAm_norm_le_one` | 341-358 | `P` | none (`a b r : Zd 3 4` bound) |
| `BAMB_ward_row` | 361 | `(zS 4 10, mS 4 10)`, `zS_im_pos` | none |
| `BAoffDiag_row_sum` | 366 | `P` | none |
| `BAoffDiag_of_real` | 371 | `P`, `κ = Im P.m0 > 0` (`P.real.1.1`), `t = 1/2` | none |
| `baOffDiag_holds` | 379 | `d=3, Λ=10, κ=Im P.m0`, `L=4`, `P.g0 ≤ 10` (`P.g0_le`), `t=1/2` | none |
| `BAnorm_one_sub_tm2_sq` | 388 | `t=1/2, m=(3/5)i` | none |
| `BAoffDiag_scalar` | 405, 411 | `κ=1/2, m=(3/5)i, t ∈ {0,1}` (`ward_scalar_inst_im/_norm`) | none |
| `BAMss_pp_apply` | 418 | `P` | none |

All nondegenerate: `card (Zd 3 4) = 64`, `Im m > 0` at every lattice point used, `t` interior or endpoint of `[0,1]`,
no `False` premise, no large witness. Matches the ticket's instance list.

## 6. Paper deltas

Prove report (d): "Paper-delta candidates: none." Lean/paper differences found here:
- `BAWard`/`BAm_norm_le_one` at `0 ≤ Im z` with factor `Im m + Im z`: a generalization; at `Im z = 0` equal to
  `(eq:WardM)`. Fixed by the merged pin (T2189), documented in `BAward_avg`'s docstring; the ticket directs
  "cite, do not re-propose". No weakening.
- `BAPropM12` omits `Im m ≳ 1`: carried by `BAReal`'s `κ ≤ Im m` / `BAImmLower` (ticket, DECISIONS §51; T2161b).
- `BASelf` on the block lattice `L^{-d} tr`: existing D472 (T2189b).
- `ε = κ²/4` explicit: a specification of the paper's "constant `ε`", within §18.
No uncovered statement difference.

## 7. Observations (no effect on verdict)

- O1: lint warning `Ward.lean:16:100` (module docstring line > 100 chars; the `set_option linter.style.longLine false`
  comes after it). Cosmetic.
- O2: the ticket text says "17 public declarations: 1 definition, 16 theorems" but lists 15 theorem names; the check
  file has 15 `*_pin`s, all matched. The two extra public theorems `WardInst.ward_scalar_inst_norm/_im` are instance
  helpers in `RBM.BA.WardInst`, allowed by the ticket ("instance theorems, if any, in `RBM.BA.WardInst`"); 0 name clashes.
- O3: for the hub at merge: the "Owed: BA-D3" docstrings of `MFixedPoint.lean` (`BAWard`, `BAPropM`, `BAoffDiag`)
  become stale for BA-D3 (`BAPropM` remains owed to BA-D4); not edited here per §57 (1).

## Verdict

| target | statement | hidden/vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `BAMB_shift`, `BAMB_transpose`, `BAMB_symm`, `BAMB_diag_eq`, `BAMB_ward_row` | PASS | PASS | PASS | PASS | PASS | PASS |
| `baWard_holds` (`BAWard`) | PASS | PASS | PASS | PASS | PASS | PASS |
| `BAMB_row_sq_real`, `BAm_norm_le_one` | PASS | PASS | PASS | PASS | PASS | PASS |
| `BAPropM12`, `baPropM12_holds` | PASS | PASS | PASS | PASS | PASS | PASS |
| `BAnorm_one_sub_tm2_sq`, `BAoffDiag_scalar` | PASS | PASS | PASS | PASS | PASS | PASS |
| `BAMss_pp_apply`, `BAoffDiag_row_sum`, `BAoffDiag_of_real` | PASS | PASS | PASS | PASS | PASS | PASS |
| `baOffDiag_holds` (`BAoffDiag`) | PASS | PASS | PASS | PASS | PASS | PASS |

**T2283: PASS.** No dispatcher sign-off needed.
