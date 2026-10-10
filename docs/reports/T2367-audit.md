Auditor model: claude-opus-5-5
# T2367 audit (round 1): BA-K04, the cactus, `RBM3D/BA/KCactus.lean`. Written Sat Oct 10 03:18:01 UTC 2026
Worktree `RBM3D-wt/T2367-audit1`, detached at `t/T2367` = `a72fdbe`. Scratch: session scratchpad `T2367/audit_*`.

## 1. Build, diff, hygiene, axioms (script output)
```
$ lake build RBM3D.BA.KCactus 2>&1 | tail   (started Sat Oct 10 03:14:01 UTC 2026)
✔ [3740/3740] Built RBM3D.BA.KCactus (7.6s)
Build completed successfully (3740 jobs).          (warnings in the log: other merged modules only; KCactus lines: 1, the "Built" line)
$ git diff --name-status main...t/T2367
A	RBM3D/BA/KCactus.lean                                   (sole writable file; no frozen file touched)
$ grep -nwE 'sorry|admit|native_decide|axiom' KCactus.lean | wc -l  ->  0
$ grep -cE '^(structure|class) ' KCactus.lean  ->  0       (no hypothesis can hide in a structure field)
$ grep -n '^import' KCactus.lean  ->  RBM3D.BA.KBase, RBM3D.Loop.KLCut, RBM3D.Loop.KLTree, RBM3D.Loop.Partition
$ wc -l KCactus.lean -> 1263   (stop line 1300)
$ git grep -nE '(BAMssOf|BAThetaOf|BAslot*|BAnextSlot*|BAMcharge|BACactusVal*|BAGamma*)' main -- RBM3D | wc -l  ->  0
$ lake env lean AuditAx.lean   (#print axioms of every public declaration, 53 names from grep of the file)
53 x [propext, Classical.choice, Quot.sound]   (1 error line: a docstring line "lemmas, ..." caught by my grep, not a name)
names: BAMssOf BAMssOf_BAMsigma BAMssOf_isSymm BAThetaOf BAThetaOf_BAMsigma BAThetaOf_isSymm BAslot BAslotLeaf
 BAslotOut BAslotIn BAslot_card BAslotStart(+_leaf/_out/_in) BAslotNode(+_leaf/_out/_in) BAslotNode_mem_nodes
 BAslot_start_inj BAnextSlot BAslotNode_nextSlot BAnextSlot_spec BAnextSlot_eq_of_above BAnextSlot_eq_of_wrap
 BAnextSlot_injective BAnextSlot_bijective BAnextSlotPerm BAnextSlot_orbit BAnextSlot_sameCycle_iff BAMcharge
 BAMcharge_def BACactusValLeafW/EdgeW/Src/Tgt BACactusVal BAGamma BAGamma_eq BAGamma_of_mem_TSP BACactusVal_congr
 BAnextSlot_empty BAMcharge_empty BACactusVal_empty BACactusVal_three BACactusVal_orient BAThetaOf_zero
 BACactusVal_zero_of_nonempty BACactusVal_empty_zero BACactusVal_sum_zero BACactusVal_sum_zero_BAMLoop
 BACactusVal_three_BAMLoop
$ lake env lean AuditPin.lean   (docs/tickets/checks/T2367-check.lean + `import RBM3D.BA.KCactus` + the two pin examples)
example (d : ℕ) : Prop := RBM.BA.T2367Check.BATreeRep d (@RBM.BA.BAGamma d)
noncomputable example (d : ℕ) : RBM.BA.T2367Check.BAGammaType d := @RBM.BA.BAGamma d
exit 0, error lines 0
```

## 2. Statements against the ticket (file lines; read from `KCactus.lean` at `a72fdbe`)
```
 50 def BAMssOf M σ₁ σ₂ := Matrix.of fun a b => M σ₁ b a * M σ₂ a b                  -- ticket 1: (BAMssOf M σ₁ σ₂) a b = M σ₁ b a * M σ₂ a b  ✓
 70 def BAThetaOf M t σ₁ σ₂ := PropThetaQ (BAMssOf M σ₁ σ₂) t                        -- ticket 1 ✓
 55/77 BAMssOf_BAMsigma, BAThetaOf_BAMsigma := rfl  (at BAMsigma d L (BAMB d L g E m))  -- bridge ✓
100 abbrev BAslot F := Fin n ⊕ ↥F ⊕ ↥F ; 113 BAslot_card F : card = n + 2 * F.card  (no hypothesis; stronger) ✓
137 BAslotNode: leaf v ↦ KLleafPar F v, out J ↦ KLnodePar F J, in J ↦ J                  -- ticket 2 ✓
120 BAslotStart: leaf v ↦ v, out J ↦ J.1, in J ↦ J.2   (first vertex of the edge's range)
347 BAnextSlot F s := successor by BAslotStart inside the fibre of BAslotNode (wrap to min)  -- ticket 3
394 BAnextSlot_bijective (hF : KLIsTSP F) (hn : 2 ≤ n) ; 398 BAnextSlotPerm ; 351 BAslotNode_nextSlot (no hyp)
403 BAnextSlot_orbit hF hn : BAslotNode F s = BAslotNode F t ↔ ∃ k, (BAnextSlot F)^[k] s = t
414 BAnextSlot_sameCycle_iff hF hn : (BAnextSlotPerm hF hn).SameCycle s t ↔ BAslotNode F s = BAslotNode F t
434 BAMcharge F σ s := σ (BAslotStart F (BAnextSlot F s))                                  -- D633 rule
477 BACactusVal := KLgval d L (Nd := BAslot F) (Lf := Fin n) a (leaf v ↦ BAThetaOf M t (σ v) (σ (v+1)))
      (BAslotLeaf F) (Sum.elim (J ↦ (t:ℂ) • BAThetaOf M t (σ J.1) (σ J.2)) (s ↦ M (BAMcharge F σ s)))
      (src: J ↦ in J, s ↦ s) (tgt: J ↦ out J, s ↦ BAnextSlot F s)                            -- ticket 4 weights ✓
488 BAGamma d L n M t F σ a := BACactusVal d L M t F σ a   (same formula for every F, stated; T2367a)
511 BACactusVal_congr (eN : BAslot F ≃ Nd') (eE : (↥F ⊕ BAslot F) ≃ Ed') ... := KLgval_congr ...   -- 5(a) ✓
578 BACactusVal_empty (hn : 2 ≤ n) : Γ(∅) = ∑ b, (∏ v, Θ^{(σ v,σ(v+1))}(a v)(b v)) * ∏ v, M (σ (v+1)) (b v) (b (v+1))  -- 5(b) ✓
628 BACactusVal_three : Γ(∅) at n=3 = ∑ b₀b₁b₂ Θ^{(σ0σ1)}(a0,b0)Θ^{(σ1σ2)}(a1,b1)Θ^{(σ2σ0)}(a2,b2)·M(σ0)_{b2b0}M(σ1)_{b0b1}M(σ2)_{b1b2}
664 BACactusVal_orient (hM : ∀ σ, (M σ)ᵀ = M σ) (o : ↥F ⊕ BAslot F → Bool) : any set of edges reversed   -- 5(c) ✓
```
Hypotheses used anywhere: `KLIsTSP F`, `2 ≤ n` (weaker than the ticket's `3 ≤ n`), symmetric `M` for 5(c). No other hypothesis (ticket's binding clause holds). No structure, no circularity: only merged modules imported; `BAGamma` is a `def`, not an assumption.

**Paper check (my reading, `A:325-335, 552-575`, `1_2:1003, 1069-1076, 1176`).** Region `R_k` holds side `(a_{k-1},a_k)` with charge `σ_k`; vertex `a_k` lies in `R_k, R_{k+1}`; external edge `Θ^{(σ_k,σ_{k+1})}(a_k,b)` = Lean leaf weight. The chord with arc `[i,j)` has the leftmost leaf `i` and rightmost `j-1`, so it borders `R_i`, `R_j`: `tΘ^{(σ_i,σ_j)}` (`(f-internal2)`, `S^{(B)}(0)=I` for BA per `1_2:1076`; D633). `A:571`: the M-edge `b_{i,j-1}→b_{i,j}` gets the charge of its region; between consecutive legs (by start) the region is `R_x`, `x` = start of the next leg: `σ_x` = `BAMcharge`. Checked case by case: leaf→leaf `σ_{v+1}`; into `out J` `σ_i`; out of `out J` `σ_{x(next)}`; inside `J`, into `in J` `σ_j`, `in J`→first child `σ_i`; root wrap `σ_0` (side `(a_{n-1},a_0)`). `(Kn3sol)`: `tr(M(σ1)E_{b1}M(σ2)E_{b2}M(σ3)E_{b3})` = `M(σ1)_{b3b1}M(σ2)_{b1b2}M(σ3)_{b2b3}` 1-indexed = Lean 628, 0-indexed. Lean 736 (`BACactusVal_sum_zero_BAMLoop`, all `n ≥ 2`) proves the `t = 0` case of the pin against K00's `BAMLoop`.

**Numerical mirror re-run by the auditor** (`mirror.py` read against the Lean definitions above: slots, `slot_start`, `next_slot` = next larger start else min, `charge = σ[start(next)]`, chord `t·Θ(σ_i,σ_j)` in→out, M-edge `s→next s`; identical):
```
$ cd $S; python3 compare.py > audit_compare.txt   (finished Sat Oct 10 03:17:54 UTC 2026)
--- q=5 g=0.8 E=0.3 t=0.5 (d=1, W=1)   n #trees (alpha) (alpha-a) (beta) max|K| worst-sigma
 3       1  0.00e+00   2.78e-17   6.08e-14   6.42e-01   ++-
 4       3  5.56e-17   2.79e-17   9.32e-13   7.60e-01   -+-+
 5      11  1.67e-16   3.18e-17   1.73e-12   7.34e-01   +--+-
--- q=4 g=0.6 E=-0.4 t=0.7
 3       1  0.00e+00   2.22e-16   8.21e-12   1.83e+00   ++-
 4       3  8.88e-16   4.45e-16   2.11e-10   3.81e+00   -+-+
 5      11  1.81e-15   1.78e-15   6.76e-10   5.96e+00   --+-+
--- q=3 g=1.1 E=0.0 t=0.6
 3       1  0.00e+00   0.00e+00   1.84e-12   1.45e+00   ++-
 4       3  4.97e-16   2.22e-16   4.54e-11   2.98e+00   +-+-
 5      11  6.28e-16   4.58e-16   1.58e-10   5.07e+00   +--+-
 6      45  1.91e-15   8.88e-16   1.24e-09   1.12e+01   +-+-+-
elapsed 137s
```
(α) max 1.91e-15 ≤ 1e-12; (β) max 6.76e-10 (n ≤ 5), 1.24e-9 (n = 6) ≤ 1e-8; tree counts 1, 3, 11, 45. Identical to the prove report's table. Stop line not triggered.

## 3. Compiled nonempty instances (namespace `KCactusInst`, 38 `example`s, all compiled in the build above)
```
 800 card (BAslot {(0,2)} : n=4) = 6                                                 -- ticket instance ✓
 810 ∑ F ∈ TSP 3, BACactusVal 1 3 BAMLoop_witM 0 F ![+,+,-] ![0,1,2] = 15             -- n=3, witM
 820 BACactusVal 1 3 witM 0 ∅ (n=4) ![+,+,-,+] ![0,1,2,1] = 10                        -- ≠ 0 ✓
 833/837 BAGamma 1 3 4 witM 0 {(0,2)} / {(1,3)} ... = 0 ; 841 ∑ F ∈ TSP 4, BAGamma ... = 10   -- each n=4 tree
 930-950 BAnextSlot table and the six charges of {(0,2)} (= draw.py, A:552-583); 1048 same for {(1,3)}
 954/963 two cycles: orbit / SameCycle true for (leaf0,in), false for (leaf0,leaf2); 972/1064/1180 bijective/injective
 974 BAslot_start_inj at {(0,2)};  1168/1171/1178 BAslotNode_nextSlot, BAnextSlot_spec, BAslotNode_mem_nodes
 1070/1073 bridges at the merged flow point P (d,L)=(3,4), t=1/2; 1087 BAThetaOf_isSymm at P (hM proved, BAMB_symm)
 1095 BACactusVal_orient at P, {(0,2)}, all edges reversed; 1105 at witM, t=1/10, M-edges reversed
 1114 BACactusVal_congr with eN : slots ≃ Fin 6, eE : edges ≃ Fin 7
 1128 BACactusVal_empty n=4, t=1/10; 1135 BACactusVal_three t=1/10; 1144 _three_BAMLoop; 1151 BAGamma_of_mem_TSP
 1157-1163 BAnextSlot_empty, BAMcharge_empty; 1183/1185 BAThetaOf_zero, Γ(∅,n=3,t=0)=15
 1253/1256 chord tree at t = 1/2: BACactusVal 1 3 Msh (1/2) {(0,2)} ![+,+,-,+] ![0,1,0,1] = 1/2, BAGamma ... ≠ 0
```
Every public theorem is applied at concrete data with every hypothesis (`KLIsTSP F` via `KLisTSP_of_mem_TSP`/`TSP_four`, `2 ≤ n` by `norm_num`, symmetry via `witM_symm`/`BAMB_symm`) discharged. No `N = 0`, empty index, or `False` premise; `n = 3, 4`, `L = 3, 4`.

## 4. Paper-delta coverage
- Charge rule: D633 (verbatim content of `BAMcharge`); `n ≥ 3`: D634 (pin). No new rule difference.
- `T2367a` (proposed): `BAGamma` total, junk off `TSP n`. Covers the only `Γ` domain difference.
- `T2367b` (proposed): combinatorial slots; "counterclockwise order" = order by `BAslotStart`; chord oriented in→out, M-edges `s→next s` (paper leaves chord orientation open, `A:561-563`); immaterial for symmetric `M` (`BACactusVal_orient`).
- `W` factor: `Γ` uses `∏ M(σ)` (block level); `W^{(k-1)d}𝓜^{(k)} = ∏ M` is the merged K00 `BAMLoop_apply` / pin `BATreeRep` convention, not introduced here (Lean 736 checks it at `t = 0`).
All statement differences are covered.

## 5. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The chord-tree instances at the K00 witness are at `t = 0` (value 0); the nonzero chord-tree value in Lean uses a directed, non-symmetric datum (`Msh`, `Θ ≡ 1`). The ticket's "at least one value ≠ 0" is met (820, 1256); exact `t = 1/10` witM values exist only in `instance.py`.
- O2. "Every node of `KLnodes F` carries a slot" is not a stated lemma; it is immediate from the definitions (`in J` for `J ∈ F`, leaf `n-1` for the root via `KLleafPar_root`) and checked at both `n = 4` chord trees (954/963).
- O3. `BAnextSlot` is noncomputable (choice); K05 must use `_eq_of_above`/`_eq_of_wrap` to evaluate it, as the instances do.
- O4. Auditor scratch: my build log was written to the shared scratchpad name `T2367/build.log`, overwriting the prover's scratch file of that name (not a repository file; the prove report quotes its own run, not that file).

## 6. Verdict
| target | verdict |
|---|---|
| 1 `BAMssOf`, `BAThetaOf`, bridges | PASS |
| 2 `BAslot`, `BAslotNode`, `BAslot_card` (Fintype, DecidableEq instances 795/797) | PASS |
| 3 `BAnextSlot` permutation, node-preserving, one cycle per node; `BAMcharge` (D633) | PASS |
| 4 `BACactusVal` = `KLgval` instance; `BAGamma : BAGammaType d`, fits `BATreeRep` | PASS |
| 5 (a) `_congr`, (b) `_empty`, `_three` = `(Kn3sol)`, (c) `_orient` | PASS |
| 6 mirror (α) 1.9e-15, (β) 1.24e-9, re-run by the auditor | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
