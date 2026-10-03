Auditor model: claude-opus-5-5

# T2021 audit (round 1), MD-5: Path/Markov, Path/Stop, Path/Azuma (RBM2D c9a24cf port)

Written Sat Oct  3 04:18:11 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2021-audit1`, detached at `t/T2021` = `23e5021`.

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2021
 RBM3D/Path/Azuma.lean  | 382 ++++++++++++++++++++++
 RBM3D/Path/Markov.lean | 836 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Path/Stop.lean   | 238 ++++++++++++++
 3 files changed, 1456 insertions(+)
$ grep -nE "sorry|admit|native_decide|^\s*axiom|set_option|unsafe|opaque" RBM3D/Path/{Markov,Stop,Azuma}.lean ; echo exit=$?
exit=1                      (no match)
$ grep -nE "^(structure|class|axiom|opaque)" RBM3D/Path/{Azuma,Stop,Markov}.lean ; echo exit=$?
exit=1                      (no new structure/class: no hypothesis can hide in a field)
```
Only new files; no frozen signature touched. Imports: Stop <- Path.Walk; Markov <- Path.Walk, Gauss.LinearForm; Azuma <- Path.Markov (instance only). No cycle (Markov does not import Azuma).

## 2. Statements against the pin (RBM2D `c9a24cf`, renaming R1-R4), by script
Pin: ticket items 1-3, "statements and proofs ... verbatim" up to R1-R4. Script: `git -C ../RBM2D show c9a24cf:RBM2D/Path/<f>.lean`,
renamed by a perl script (`RBM2D.`->`RBM3D.`; `(d : Sizes)`->`{d : ℕ} (sz : Sizes d)`; `Idx (d.L n) (d.W n)`->`Idx d (sz.L n) (sz.W n)`;
`d.L/d.W`->`sz.L/sz.W`; `PathΩ/filt/pathH/pathP/map_incr/indep_incr/Sizes.* d`->`… sz`; `Coord`->`CoordF d`; `Xmat_add/Xmat_smul/Xmat (`->`… d (`),
comments and `#print` lines stripped, then `diff`.
```
$ diff 2d_Azuma.lean RBM3D/Path/Azuma.lean          (no renaming needed)
6a7      > import RBM3D.Path.Markov
12,13c13,15 / 15c17,18   header comment only
333c336, 335,339c338,382   RBM2D `#print axioms` lines -> the sz0 instance section (new)
== Stop: diff lines (code only) 28     hunks: 158,162c158,168 ; 164,175d169   (RBM2D stopCheckSizes check -> sz0 example)
== Markov: diff lines (code only) 130  hunks:
204c204     proof term `map_sum_const_mul_coord d` (continuation line my rename missed; proof only)
262a263,266 + private instance StandardBorelSpace (PathΩ sz) (proof-level; StandardBorelSpace is a Prop class)
590,595d593 / 597,613c595,596 / 650,654c638,658  RBM2D markovSizes checks removed -> sz0 instances
624,625c607,610 / 638,641c623,629  proof of markov_linTrVar_one_pos (now public, stem-prefixed) uses merged svarF_diag
655a660,663 / 656a665,715 / 660d718   new instance helpers (markov_*, private linTr_smul_left, linTrVar_smul)
```
No hunk touches the statement of any target. Target statements (verbatim after renaming, so as in RBM2D):
- `azuma_two_sided`: `StronglyAdapted ℱ Y`, `HasSubgaussianMGF (Y 0) (c 0) μ`, `∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) … (Y (i+1)) (c (i+1)) μ`, `0 ≤ ε` ⊢ `μ.real {ε ≤ |Σ_{i<n} Y i|} ≤ 2 exp(-ε²/(2 Σ_{i<n} c i))`.
- `azuma_complex`: same for Re/Im, bound `4 exp(-ε²/(4 Σ c))`.
- `doob_L2_max`: `Martingale M ℱ μ`, `M 0 = 0` (unused), `∀ k, MemLp (M k) 2 μ`, `0 < x` ⊢ `μ.real {x ≤ max_{k≤K} |M k|} ≤ E[M_K²]/x²` (weak type; see §5).
- `isStoppingTime_firstHit_grid`: `∀ j, Measurable (F j)` ⊢ `IsStoppingTime (filt sz) (firstHit (F j ∘ pathH sz s t K n j) θ K')`.
- `hasCondSubgaussianMGF_linear`: `Measurable[filt sz k] A`, `MeasurableSet[filt sz k] E`, `0 ≤ c`, `∀ ω ∈ E, gridStep s t K n * linTrVar n (A ω) ≤ c` ⊢ cond. sub-Gaussian with parameter `c`.
- `linTrVar n A = linVar (Sizes.seqGvar sz) (c ↦ linTr n A (seqXmat sz n (Pi.single c 1)))`; merged normalisation:
```
RBM3D/Gauss/FineModel.lean:47:def svarF (i j : Idx d L W) : ℝ :=  ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1
RBM3D/Gauss/FineModel.lean:164:def seqGvar (c : SeqCoord sz) : ℝ≥0 := gvarF d (sz.L c.1) (sz.W c.1) (sz.lam c.1) c.2
```
So the `W^{-d}` normalisation enters through MD-1 as the ticket requires; no exponent is restated in these files.
Quantifier order, index ranges (`range n`, `i < n - 1`, `range (K+1)`), dimension `d` generic: as in the pin.

## 3. Vacuity / hidden hypotheses / cycles
- No `Prop`-valued hypothesis definition added; no structure. All hypotheses are explicit standard measure-theory predicates.
- Full-library premise registry with and without the three modules (scratch files outside the repo, `lake env lean`):
```
$ lake build RBM3D 2>&1 | grep -E "error|Build completed" | tail -1
Build completed successfully (3715 jobs).
$ diff full_main.out full_new.out      # 'import RBM3D; #assert_rbm_axioms' vs '+ import RBM3D.Path.Azuma, RBM3D.Path.Stop'
1c1
< axiom audit: 985 theorems, 378 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 1017 theorems, 385 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -ciE "error|unclassified" full_new.out
0
```
The registry/non-vacuity lines are identical: no new premise. No external hypothesis (no limit check needed).
Dependencies are merged MD-1/MD-4 declarations (`seqXmat`, `seqGvar`, `PathΩ`, `pathP`, `filt`, `pathH`, `gridStep`).

## 4. Compiled nonempty instances (in the same files; ticket "Instances to compile")
MD-1 instance sequence `RBM.Gauss.SizesInst.sz0` (merged in `0a873f1` "T2006: merge MD-1"):
```
RBM3D/Defs/Sizes.lean:260 def sz0 : Sizes 3 where L := fun n => 4*(n+1); W := fun n => (2*(n+1))^5; lam := fun n => ((2*((n:ℝ)+1))^6)⁻¹
theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64
```
- `isStoppingTime_firstHit_grid`: Stop.lean `example` at `sz0`, `d = 3`, `s = 1/10`, `t = 1`, `K = 4`, `n = 0`, `F j M = ‖M 0 0‖` (measurability proved),
  `θ = 1/2`, `K' = 4`. Nondegenerate: `filt sz0` on the nontrivial product path space, horizon 4.
- `hasCondSubgaussianMGF_linear`: Markov.lean `markov_hasCondSubgaussianMGF_linear_sz0` (`A = 1`, `E = univ`, `c = Δ·linTrVar 0 1`,
  `Δ = 9/40` by `instGridStep`), with `markov_instance_c_pos : 0 < c` (via `markov_linTrVar_one_pos`, uses `svarF_diag`); and
  `markov_cond_subgaussian_unit_sz0` with `c = 1`, `A = markov_instA = (1/(1+ΔV))•1`, `markov_instA_bound : 0 < Δ·linTrVar 0 A ≤ 1`.
- `azuma_two_sided`: Azuma.lean `example` at `c_k = 1`, `n = 100`, `ε = 20`; `Y 0 = 0`, `Y (k+1) = √(9/40)·linTr 0 markov_instA (seqXmat sz0 0 (ω (k+1)))`;
  `StronglyAdapted` proved (`azumaInstY_adapted`), `h0` proved (`Y 0 = 0` is sub-G with proxy 1), `h_subG` = `markov_cond_subgaussian_unit_sz0`. Increments have
  positive variance (`markov_instA_bound.1`): not degenerate. Every hypothesis discharged; no hypothesis left.
All three compile in the build of §6. No `N = 0`, empty index, collapsed window or `False` premise; witness sizes are small (`L = 4`, `W = 32`).

## 5. Paper deltas
- BDG -> Azuma + Doob on the grid walk: covered by D21 (`docs/paper-deltas.md:228`, "BDG 换成 Azuma 与 Doob").
- `doob_L2_max` is the weak-type tail bound `P(max_{k≤K}|M_k| ≥ x) ≤ E M_K²/x²`, not `E max|M_k|² ≤ 4E M_n²` (ticket preflight text):
  proposed as `T2021a` in the prove report (d). The statement equals the pinned RBM2D statement, so this is a coverage item, not a defect.
- `T2021b` (instance remark) proposed; no other Lean/paper statement difference (ports are verbatim after R1-R4).
Coverage complete.

## 6. Build and axioms (audit worktree)
```
$ lake build RBM3D.Path.Markov RBM3D.Path.Stop RBM3D.Path.Azuma 2>&1 | grep -E "Built RBM3D.Path|error|Build completed"
⚠ [3313/3315] Built RBM3D.Path.Stop (4.2s)
⚠ [3314/3315] Built RBM3D.Path.Markov (6.5s)
✔ [3315/3315] Built RBM3D.Path.Azuma (3.4s)
Build completed successfully (3315 jobs).      exit=0
warnings (21): 17 linter "line exceeds 100 characters" (Markov 16, Stop 1); Markov.lean:456 unused `hc`; Walk.lean:599 unused `hK` (pre-existing)
$ lake env lean Ax.lean | sed 's/.*depends on axioms: //' | sort | uniq -c     # #print axioms RBM.Path.<n> for all 39 public names
  39 [propext, Classical.choice, Quot.sound]
```
Public names (39): adapted_of_measurable_pathH azuma_complex azuma_two_sided condExp_freeze condExp_linear_eq_zero coordFinset doob_L2_max firstHit
firstHit_le hasCondSubgaussianMGF_linear integral_linTr_seqXmat isStoppingTime_firstHit isStoppingTime_firstHit_grid isStoppingTime_min_firstHit
isStoppingTime_min_firstHit_grid linTr linTr_seqXmat_eq_sum linTrVar linTrVar_nonneg lt_firstHit_grid_measurableSet lt_firstHit_imp
lt_firstHit_measurableSet lt_min_firstHit_grid_measurableSet lt_min_firstHit_imp lt_min_firstHit_measurableSet map_linTr_seqXmat
markov_cond_subgaussian_unit_sz0 markov_hasCondSubgaussianMGF_linear_sz0 markov_instA markov_instA_bound markov_instance_c_pos markov_instOne
markov_instScale markov_linTrVar_one_pos markov_measurable_linTr_seqXmat_sz0 martingale_sq_eq_sum pathH_measurable_filt stopped_martingale sum_stopped
```
$ for n in <39 names>; do git grep -nwE "(theorem|lemma|def|abbrev) $n" main -- 'RBM3D/*.lean' | wc -l; done   -> 0 for every name (no clash)
```
Unpinned helpers are `private` or `markov_`-prefixed (CLAUDE.md §3 (E)).

## 7. Verdicts
| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| Azuma.lean (`azuma_two_sided`, `azuma_complex`, `doob_L2_max`, `martingale_sq_eq_sum`, `stopped_martingale`) | verbatim | none | `azuma_two_sided` at `c_k = 1` | ok | D21, T2021a | PASS |
| Stop.lean (`firstHit` lemmas, 5 grid lemmas) | verbatim after R1 | none | `isStoppingTime_firstHit_grid` at sz0 | ok | D21 | PASS |
| Markov.lean (`condExp_freeze` … `hasCondSubgaussianMGF_linear`) | verbatim after R1-R4 | none | `hasCondSubgaussianMGF_linear` at sz0 (c>0 and c=1) | ok | D21 | PASS |

Overall: **PASS**. No dispatcher sign-off needed for merge.

## 8. Observations (no effect on statement, instance, build, axioms or coverage)
- O1. The ticket asks the prove report to cite D21; it does not (`grep -n D21 docs/reports/T2021-prove.md` -> no match). Coverage holds via D21 itself.
- O2. Instances exist only for the three theorems the ticket lists; the other ported theorems (`azuma_complex`, `doob_L2_max`, `martingale_sq_eq_sum`,
  `stopped_martingale`, `condExp_freeze`, …) have none. The ticket's instance list is followed; their hypotheses are standard
  (`Martingale`, `MemLp`, `IsStoppingTime`, measurability) and are not vacuous.
- O3. For ST-2: `doob_L2_max` gives probability bounds on the running maximum, not an `L²` bound (T2021a); whether ST-2 needs the strong form is a downstream question.
- O4. Azuma.lean imports Markov.lean only for its instance; downstream importers of Azuma pull Markov transitively.
