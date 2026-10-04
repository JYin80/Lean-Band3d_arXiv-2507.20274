Auditor model: claude-opus-5-5

# T2096 audit (round 2) — S1-21 `Green/FlucIterGain.lean`

Written Sun Oct  4 02:40:10 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2096-audit2`,
detached at `t/T2096` = `e16dab6` (repair of round-1 RETURN). Scratch: `<scratchpad>/T2096/` (`sdiff2.py`, `ax2.lean`).

## 1. Diff scope, hygiene
```
$ git diff --name-only main...HEAD
RBM3D/Green/FlucIterGain.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]" | cut -c1-110
-   `RBM.Gauss.Sizes.STLocalEntry] -- local law for the entries, a hypothesis of `lem:LWterm_EXP`: first used
+   `RBM.Gauss.Sizes.STLocalEntry, -- local law for the entries, a hypothesis of `lem:LWterm_EXP`: first used
+   `RBM.Green.FlucGainUpTo'] -- gain interface of the higher-order minor expansion `(GavLGEX)` (`3_5:33`): hyp
$ grep -n -E "sorry|admit|native_decide|^\s*axiom|set_option|^import" RBM3D/Green/FlucIterGain.lean
6:import RBM3D.Green.FlucIter
$ git merge-tree --write-tree main HEAD; echo $?     # main = 5bef95c moved past the branch base 9bb2cbe
aebadbe41a180855e1d44efe421e8b020c5dd0ab
0
$ git show aebadbe:RBM3D/Test/Axioms.lean | grep -n -E "FlucGainUpTo'|UkerFar" | cut -c1-50
192:   `RBM.Green.FlucGainUpTo'] -- gain interface of the
236:   `RBM.Path.UkerFar] -- the far-kernel condition `‖
```
Only the two sole writable files; the registry change is one appended line plus the list separator. No frozen
signature touched. Imports: `RBM3D.Green.FlucIter` only (merged T2089); no ST-2…ST-6 import, no cycle.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Green.FlucIterGain; echo exit $?
✔ [3333/3333] Built RBM3D.Green.FlucIterGain (6.2s)
exit 0
$ grep warning build.txt | sed 's/:[0-9]*:[0-9]*:.*//' | sort | uniq -c      # none in the new file
   1 warning: RBM3D/Green/FlucVanish.lean
  18 warning: RBM3D/Green/LDEQuad.lean
$ lake build; echo exit $?          # full library, branch's Test/Axioms.lean
Build completed successfully (3841 jobs).   exit 0
$ lake env lean ax2.lean; echo exit $?   # import RBM3D, the module; 36 x #print axioms; #assert_rbm_axioms
exit 0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax2.txt; grep -v "<that>" ax2.txt | grep -E ...
36
axiom audit: 3152 theorems, 1154 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Green.FlucGainUpTo': 2 [no certificate]
premises found by scanning: 84 (borrowed 2, owed 67, structural 15).
$ grep -E "iter_budget|sum_prod_abs_card_image_le|sum_weighted_le|moment_|_row'" ax2.txt
'RBM.Green.sum_prod_abs_card_image_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.sum_weighted_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.integral_norm_flucAvg_pow_le_iter_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucIterGainInst.sum_prod_abs_card_image_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucIterGainInst.sum_weighted_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucIterGainInst.moment_row_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucIterGainInst.moment_row_p2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.FlucIterGainInst.moment_block_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pin (RBM2D `c9a24cf:819-1877` after ST1-COMMON item 2 renaming; DECISIONS §30)
Independent script `sdiff2.py` (my own, not the prover's): each declaration header up to its first `:=` in RBM2D
Part 2, renamed (`d`→`sz`, `(sz : Sizes)`→`(sz : Sizes d)`, `Idx (sz.L`→`Idx d (sz.L`, `spectralZ/M`→`zt/mE`),
token diff against the branch file (checks `flucIter_check_*` excluded: they are RBM2D's instances).
```
$ python3 sdiff2.py r2d_part2.lean RBM3D/Green/FlucIterGain.lean
DIFFER sum_prod_abs_card_image_le (2D :966, 3D :371)
    replace 2D: UniformWeight | 3D: BoundedWeight
    replace 2D: (hs | 3D: (_hs
DIFFER sum_weighted_le (2D :1024, 3D :395)
    replace 2D: UniformWeight | 3D: BoundedWeight
DIFFER integral_norm_flucAvg_pow_le_iter_budget (2D :1453, 3D :823)
    replace 2D: UniformWeight | 3D: BoundedWeight
SAME (16): loneSlots, mem_loneSlots, image_loneSlots_eq, two_mul_card_image_le_add_card_loneSlots,
 card_filter_card_image_le, bddMeas_epsHom_flucDiag, OpsOkOut.length_le, norm_integral_prod_applyOps_le_graded,
 norm_integral_prod_qRow_le_graded, FlucGainUpTo', FlucGainUpTo'.B_nonneg, FlucGainUpTo'.rho_nonneg,
 FlucGainUpTo'.gain, norm_integral_prod_epsHom_flucDiag_le_budget, flucIter_integral_prod_norm_applyOps_le_crude,
 flucIter_flucGainUpTo'_of_crude
differences: 3
```
Section `variable` lines (implicit context of the headers) match RBM2D one for one (2D `:830,:963,:1122,:1132,
:1153,:1186,:1388` vs 3D `:77,:211,:492,:502,:523,:556,:758`; only `{d : Sizes}`→`{d : ℕ} {sz : Sizes d}`).
`BoundedWeight` (`Green/FlucVanish.lean:941`): `nonneg_c`, `nonneg`, `le : ∀ k ∈ A, t k ≤ c`, `not_mem`, `sum_le`.
- **`integral_norm_flucAvg_pow_le_iter_budget`** (key, :823): RBM2D `:1453` with only `UniformWeight → BoundedWeight`
  (DECISIONS §30, weaker premise, same conclusion `(2p+1)(2p)^{2p}(2^{2p-1}ρB)^{2p}`); quantifiers, `hM hK : 2p ≤ M,K`,
  `hρ1`, `hcρ : c ≤ ρ²`, `hp : 2p ≤ #A` unchanged; `d` generic. **PASS.**
- **`sum_prod_abs_card_image_le`** (:371): round-1 defect repaired — `hc1 : c ≤ 1` removed, `hs` restored in RBM2D's
  position (as `_hs`, unused binder name only). Proof (`:377-389`) applies the private `…_of_le_one` at `min c 1`
  (`t k ≤ ∑ t ≤ 1` via `Finset.single_le_sum`, `hw.sum_le`) and `gcongr` with `min_le_left`. **PASS.**
- **`sum_weighted_le`** (:395): only the weight swap. **PASS.**
- The 16 other declarations: SAME. **PASS.**

## 4. Hidden hypotheses, vacuity, cycles
- `FlucGainUpTo'` (:727) is a `Prop` definition (RBM2D's verbatim, SAME) taken as hypothesis `hg` of the budget and
  key statements; it is the owed interface proved by S1-22 and registered owed in `Test/Axioms.lean` (scan: 2 users).
  Not vacuous: discharged at concrete data by private `flucGainUpTo'_szG_half/one` (:997, :1006) through the
  gain-free `flucIter_flucGainUpTo'_of_crude` (RBM2D :1563). It is a hypothesis the paper proves (not an external
  input), so no limit check is needed.
- `BoundedWeight` fields are all discharged at the instances (`boundedWeight_svarF`, merged; `uniformWeight_blockAvg2
  … .toBoundedWeight`, merged). No other structure-packed hypothesis.

## 5. Compiled nonempty instances (namespace `RBM.Green.FlucIterGainInst`, :972-:1286; compiled in §2)
`szG : Sizes 3`, `L = 3`, `W = 2`, `lam = 1/2` (constant), slice 0, `E = 0`, `t = 1/2` (`eta_eq : Im zt = 1/2`).
```
$ sed -n 1126,1135p RBM3D/Green/FlucIterGain.lean          # (moment_row_p2, moment_block_p1 analogous)
theorem moment_row_p1 (u : ℝ) :
    ∫ ω, ‖flucAvg szG 0 u (zt 0 (1 / 2)) (mE 0) rowW ω‖ ^ (2 * 1) ∂(Sizes.seqP szG)
      ≤ 110592 := by
  refine le_trans (integral_norm_flucAvg_pow_le_iter_budget (p := 1) (E := 0) (t := 1 / 2)
    hE0 ht0 (flucGainUpTo'_szG_half u) le_rfl le_rfl (by norm_num) ?_ rowW_bounded ?_) ?_
  · norm_num [szG]
  · rw [rowA_card]; norm_num
  · norm_num
$ sed -n 1101,1107p RBM3D/Green/FlucIterGain.lean
theorem sum_prod_abs_card_image_row :
    ∑ v ∈ (Finset.univ : Finset (Fin 2 → Idx 3 (szG.L 0) (szG.W 0))).filter
        (fun v => ((Finset.univ : Finset (Fin 2)).image v).card ≤ 1), ∏ i, |rowW (v i)|
      ≤ 1 / 8 := by
  refine le_trans (sum_prod_abs_card_image_le (ι := Fin 2) (s := 1) (n := 2) rowW_bounded
    (by rw [rowA_card]; norm_num) (by norm_num) (by simp)) ?_
  norm_num [szG]
```
| Endpoint | Instance | Data |
|---|---|---|
| key statement | `moment_row_p1`, `moment_row_p2`, `moment_block_p1` | true row `rowW = svarF 3 3 2 (1/2) 0 ·`, `#A = 56` (`rowA_card`), `c = 1/8`, `c·#A = 7`; p = 1 `(96,1/2,2,2)`, p = 2 `(96,1,4,4)`; block `#A = 8` |
| `sum_prod_abs_card_image_le` | `sum_prod_abs_card_image_row` (new call, repaired) | row, `ι = Fin 2`, `s = 1`, `n = 2`, `1 ≤ 56` |
| `sum_weighted_le` | `sum_weighted_row` | row, `ρ = 1/2`, `K = B = 1`, `n = 2 ≤ 56` |
| counting / graded / budget lemmas | `counting_*`, `iter_epsHom_budget`, `opsOkOut_length_le_szG`, `iter_graded`, `iter_qRow`, `iter_comm` | `v = (0,0,1,2)`, sites `(0,0,0)`,`(0,0,1)` |

Every deterministic hypothesis (`|E|<2`, `t<1`, `ρ ≤ 1`, `c ≤ ρ²`: `1/8 ≤ 1/4` and `≤ 1`, `2p ≤ #A`, `2p ≤ M,K`, the
weight, the gain interface) is discharged; nothing left as an example hypothesis. Nondegenerate (`N = 216`, `p ≥ 1`,
non-uniform row). Budget arithmetic: `3·4·(2·½·96)² = 110592`, `5·4⁴·(8·96)⁴ = 445302209249280`. **PASS.**

## 6. Paper deltas
The paper does not state these lemmas (`3_5:37` cites `[YY_25]` Lemma 4.1). The only statement difference from the
pin is the weight hypothesis, covered by D107 (= `T2061a`, DECISIONS §30), cited in the report (d). `T2096a` is
proposed as a proof-only difference (mass step RBM2D `:1017`, `c·#A ≤ 1`, false for the row at d ≥ 3; replaced by
the labelling argument at `min c 1`). Coverage complete.

## 7. Observations (no verdict effect)
- O1. Merge note for the hub: `main` (5bef95c) appended `RBM.Path.UkerFar` to `Test/Axioms.lean` after the branch
  base 9bb2cbe. Bringing in the branch's copy verbatim would drop that line; a 3-way merge is clean (`git merge-tree`
  exit 0, both lines present, §1).
- O2. Registry class `owed` for `FlucGainUpTo'` (proved by S1-22) is the prover's proposal for the dispatcher.

## Verdict
| Target | Verdict |
|---|---|
| `integral_norm_flucAvg_pow_le_iter_budget` (key) | PASS |
| `sum_prod_abs_card_image_le` | PASS (round-1 defect repaired) |
| `sum_weighted_le`, the 16 SAME declarations | PASS |
| instances, build, axioms, registry pre-check, paper deltas | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed.
