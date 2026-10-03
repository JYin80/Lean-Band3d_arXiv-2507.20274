Auditor model: claude-opus-5-5

# T2018 audit (round 1) — Sat Oct  3 03:26:55 UTC 2026

Branch `t/T2018` at `8eda4cd`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2018-audit1` (detached).
Sole writable files: `RBM3D/Path/Walk.lean` (new); `RBM3D/Test/Axioms.lean` (conditional, untouched).

## 1. Diff scope
```
$ git diff --stat main...t/T2018
 RBM3D/Path/Walk.lean | 949 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 949 insertions(+)
```

## 2. Build and axioms
```
$ lake build RBM3D.Path.Walk 2>&1 | grep -E "error|warning|Build|sorry"
warning: RBM3D/Path/Walk.lean:599:5: Variable name `hK` is not explicitly referenced.
Build completed successfully (3307 jobs).
$ lake env lean ax_audit_tmp.lean | sed 's/^.*depends on axioms: //' | sort | uniq -c
  # #print axioms of 31 public decls: pathP filt gridStep gridTime pathH TransferLaw IndepIncr
  # isProbabilityMeasure_pathP pathH_isHermitian PrecGrid precGrid_of_le gridTime_last measurable_pathH
  # pathH_adapted indep_incr map_incr indepIncr map_pathH_eq transferLaw GridTransferPT gridTransferPT
  # walk_measurable_{Gres_apply,loopL,blockMat,loopFine,Gt_apply,Lloop} transferLaw_sz0 indepIncr_sz0
  # gridRes_prec gridTransferPT_sz0
     31 [propext, Classical.choice, Quot.sound]
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom ' RBM3D/Path/Walk.lean; echo "grep exit $?"
grep exit 1
```
Full `lake build` (root `#assert_rbm_axioms`, premise scan) is run by the hub at merge.

## 3. Statements

### Item 1 — pinned text, probe `5d2a4a8` lines 937–1035
```
$ git show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean | sed -n '937,1035p' > probe.txt
$ sed -n '43,141p' RBM3D/Path/Walk.lean > walk1.txt
$ diff probe.txt walk1.txt && echo IDENTICAL
IDENTICAL
```
(probe.txt line 1 `/-! ## 8. The flow carrier ...`, last line `end RBM.Gauss.Sizes`: the whole section 8.)
`PathΩ`, `pathP`, `filt`, `gridStep`, `gridTime`, `pathH`, `TransferLaw`, `IndepIncr`,
`isProbabilityMeasure_pathP`, `pathH_isHermitian`, `PrecGrid`, `precGrid_of_le`: verbatim. PASS.

### Item 2 — RBM2D `Path/Walk.lean` at `c9a24cf` (gridTime_last … transferLaw), renamed, docstrings stripped
Rename script `rn.pl`: `Idx (d.L n) (d.W n)`→`Idx d (sz.L n) (sz.W n)`, `d.{L,W,size}`→`sz.*`,
`<name> d`→`<name> sz` for the path/Sizes names. Region RBM2D 85..581 vs RBM3D 160..638.
```
$ diff -w r2part.txt r3part.txt   (summary of all hunks)
7,21d6     pathH_isHermitian (RBM2D proof) absent here: the pinned probe version is in item 1
23,24c8,9  Sizes.SeqΩ d → Sizes.SeqΩ sz ; measurable_Xentry (L) (W) → measurable_Xentry d (L) (W)
57..90     Sizes.SeqΩ d → Sizes.SeqΩ sz (restrictLe, iIndepFun_infinitePi, comap lines)  [8 hunks]
110..131   variable {d} → variable {sz}; SeqΩ d → SeqΩ sz; Xlinear (L) (W) → Xlinear d (L) (W)
214..239   variable {d} → variable {sz}; SeqΩ d → SeqΩ sz
253,257    private def pathP'/swapEquiv (d : Sizes) → {d : ℕ} (sz : Sizes d)
341..383   SeqΩ d → SeqΩ sz; one line re-wrapped (infinitePi_map_pi)
exit 1
```
Every hunk is the R1 rename `d : Sizes` → `sz : Sizes d` (index type, sample space) or a line wrap; no
hypothesis, quantifier, or conclusion changed. Public signatures checked in particular:
```
theorem gridTime_last (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) :
    gridTime s t K n (K n) = t n
theorem map_pathH_eq (s t) (K) (n k) (hs : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) :
    (pathP sz).map (pathH sz s t K n k) = (Sizes.seqP sz).map (Sizes.seqHflow sz n (gridTime s t K n k))
theorem transferLaw : TransferLaw sz := fun s t K n k hs hst hK => map_pathH_eq sz s t K n k hs hst hK
theorem indepIncr : IndepIncr sz := fun k => (indep_incr sz k).symm
```
`transferLaw` and `indepIncr` have exactly the pinned types `TransferLaw sz`, `IndepIncr sz` (item 1),
which match the ticket's mathematics: law of `√s X₀ + √Δ Σ_{i≤k} X_i` = law of `√(t_k) X` under
`0 ≤ s ≤ t`, `K ≠ 0`; draw `k+1` independent of `filt k`. PASS.

### Item 3 — RBM2D `Path/Transfer.lean` at `c9a24cf`, `GridTransferPT` … `gridTransferPT` (lines 35–78)
```
$ sed -n '35,78p' r2tr.lean | perl -p rn.pl | strip > t2.txt
$ sed -n '662,705p' RBM3D/Path/Walk.lean | strip > t3.txt
$ diff t2.txt t3.txt; echo "transfer exit $?"
transfer exit 0          (39 code lines)
```
`GridTransferPT` (hypotheses `0 ≤ s`, `s ≤ t`, `K ≠ 0`, measurability of `F`; iff of `PerTimeDomAt`
on `pathP` and on `seqP` over `Fin (K n + 1) × V n` at scale `sz.size`) identical after renaming. PASS.
Measurability helpers (RBM2D 84–150, re-expressed for MD-3 objects, stem-prefixed public names, rule (E)):
```
theorem walk_measurable_Gres_apply (z : ℂ) (σ : Bool) (i j : n) : Measurable fun M => Gres M z σ i j
theorem walk_measurable_loopL / walk_measurable_blockMat / walk_measurable_loopFine   (in the matrix)
theorem Sizes.walk_measurable_Gt_apply (n) (E t) (σ) (i j) : Measurable fun ω => Gt sz n E t σ ω i j
theorem Sizes.walk_measurable_Lloop (n) (E t) (σ) (a) : Measurable fun ω => Lloop sz n E t σ a ω
```
These carry no hypotheses beyond `NeZero L`, `NeZero W` (type-class, from `Sizes`). Lines 155–212
(error matrices) not ported, as the ticket requires.

## 4. Hidden hypotheses, vacuity, cycles
- `TransferLaw`, `IndepIncr` are proved (`transferLaw`, `indepIncr`), not premises. No new `structure`;
  `Sizes` (merged) has fields `L W lam three_le_L W_pos` only.
- `StochDomAt`, `PerTimeDomAt` (merged `RBM3D/Defs/StochDomAt.lean:61,105`) are `∀ τ>0, ∀ D>0, ∀ᶠ l, P{…} ≤ size^{-D}`:
  not vacuous at `sz0` (`size 0 = 2097152`, grows).
- Imports: `RBM3D.Gauss.FineModel`, `RBM3D.Defs.StochDomAt`, `RBM3D.Loop.GLoopFlow` (merged) + Mathlib. No cycle.
- No external hypothesis introduced.
```
$ git grep -nwE "(def|theorem|lemma|abbrev|instance) (PathΩ|pathP|…|walk_measurable_\w+|Fres|Zres|gridRes_prec)" main -- RBM3D
exit 1   (no clash)
```

## 5. Compiled nonempty instances (same file, `namespace RBM.Path.WalkInst`, built above)
Data: `sz0` (`Defs/Sizes.lean:260`: `d = 3`, `L n = 4(n+1)`, `W n = (2(n+1))^5`, `size 0 = 2097152`).
| Endpoint | Instance | Data / hypotheses discharged |
|---|---|---|
| `transferLaw` | `transferLaw_sz0` | `s = 1/10`, `t = 1`, `K = 4`, `n = 0`, `k = 2`; `0≤s`, `s≤t`, `K≠0` by `norm_num`; grid time `11/20` |
| `transferLaw` (pin) | `transferLaw_pin_sz0 : TransferLaw sz0` | — |
| `indepIncr` | `indepIncr_sz0` (`k = 2`), `indepIncr_pin_sz0 : IndepIncr sz0` | no hypotheses |
| `precGrid_of_le` | `gridRes_prec` | `ξ = ‖Gres(pathH … n 2 ω)(zt ½ ½) true 0 0‖`, `ζ = η⁻¹ > 0` (`etaT_pos`); `ξ ≤ ζ` by Ward bound `norm_inverse_entry_le` |
| `gridTransferPT` | `gridTransferPT_sz0` | `s = 1/10`, `t = 1/2`, `K = 4`, `V = Unit`; `0≤s`, `s≤t`, `K≠0`, `Fres_measurable` discharged; `U n = Fin 5 × Unit`; RHS proved by `precPT_of_le` + Ward bound, `η_u > 0` on grid (`gridTime_le_half`) |
| `gridTime_last` | `gridTime_last_sz0` | `K = 4 ≠ 0` |
No `N = 0`, empty index, collapsed window (`t − s = 9/10` resp. `2/5`, five grid times) or `False` premise.
No unproved-gate hypothesis remains in any instance. PASS.

## 6. Paper deltas
Lean/paper differences: grid Gaussian walk on `pathP` in place of `(MBM)` (1_2:686), single-time law,
one product space over sizes, per-time `≺` with the union over `u` outside `P`. All covered by **D21**
(`docs/paper-deltas.md:228`), which names `pathH`/`pathP`, independent increments and the per-time
convention. `GridTransferPT` is a statement about Lean objects with no paper counterpart beyond D21.
No uncovered difference; no new candidate needed.

## 7. Observations (no RBM-statement effect)
- O1. Linter warning `hK` unused at `Walk.lean:599` (`map_pathH_eq`): the hypothesis is kept to match the
  pinned `TransferLaw` and RBM2D; harmless, reported in the prove report (d).
- O2. Public helpers `walk_measurable_*` have no separate instance; they are not ticket endpoints and
  `walk_measurable_Gres_apply` is exercised by `Fres_measurable` → `gridTransferPT_sz0`.
- O3. `RBM3D/Test/Axioms.lean` untouched; the prover reports no unclassified premise in its full build;
  the hub's merge build is the check.

## Verdict
| Target | Verdict |
|---|---|
| Item 1 (pinned section 8, incl. `PrecGrid`, `precGrid_of_le`) | PASS |
| Item 2 (`transferLaw`, `indepIncr` and ported Walk lemmas) | PASS |
| Item 3 (`GridTransferPT`, `gridTransferPT`, measurability helpers) | PASS |

**T2018: PASS.** No dispatcher sign-off needed.
