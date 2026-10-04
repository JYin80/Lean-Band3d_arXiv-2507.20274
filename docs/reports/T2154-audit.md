Auditor model: claude-opus-5-5

# T2154 audit (round 1) — ST2-33 `Induction/GridAssemblyN` — Sun Oct  4 19:55:56 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2154-audit1`, detached at `t/T2154` = `20bd020`. Scripts in `scratchpad/T2154/` (outside the repository).

## 0. Diff scope
```
$ git diff --name-only main...t/T2154 ; git merge-base main t/T2154
RBM3D/Induction/GridAssemblyN.lean
2f246bfe7e49b59e462921536c31c765dc744b3b
$ git diff main...t/T2154 -- RBM3D/Test/Axioms.lean | wc -l
       0
```
Only the sole writable file is touched; no frozen signature changed (no other file in the diff).

## 1. Statements: pins against RBM2D `Induction/GridGoodN.lean:290-528` at `c9a24cf` (ticket's pin source)
`python3 pindiff.py`: extracts each `def`/`structure` from both texts (docstrings removed), applies the ticket dictionary (`d ↦ sz`, `Z2 (d.L n) ↦ Zd d (sz.L n)`, `Idx ↦ Idx d`, `Coord ↦ CoordF d`, `gvar ↦ gvarF d … (sz.lam n)`, `coordinateMatrix ↦ coordinateMatrix d`, `Ugen (d.L n) ↦ Ugen d (sz.L n) (sz.lam n)`, `SizeTendsto d ↦ sz.SizeTendsto`, `RangeCond d ↦ sz.RangeCond`, drop `[NeZero k] `), then token-diffs.
```
== StoppedAzumaZN RBM2D(dict) 220 RBM3D 220 hunks 0
== qvFormN RBM2D(dict) 121 RBM3D 131 hunks 14
   replace (L W -> (n
   delete [NeZero L] [NeZero W] ->
   replace L W) -> d (sz.L n) (sz.W n))          (x2)
   replace Z2 L) / Z2 L, -> Zd d (sz.L n)) / Zd d (sz.L n),   (x3)
   replace ukerMat L (KLoop.mSig -> uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma   (x2)
   insert  -> i))                                  (x2)
   delete * KLoop.mSig E (σ (i + 1))) ->           (x2)
   replace eeN L W -> sz.STeeM n
== AzumaSubGN RBM2D(dict) 203 RBM3D 203 hunks 0
== YMomentBoundsN RBM2D(dict) 278 RBM3D 278 hunks 0
== YMomentsConclN RBM2D(dict) 137 RBM3D 135 hunks 1
   delete [NeZero k] ->                (line-final binder, missed by my regex; dictionary item)
== YMomentsN RBM2D(dict) 91 RBM3D 91 hunks 0
== GridAssemblyHypN RBM2D(dict) 546 RBM3D 546 hunks 0
== AssembledN RBM2D(dict) 444 RBM3D 491 hunks 1
   insert -> N^ε * √(Σ c) + N^(-D) + Σ (1+(1-u m)⁻¹)^k * stepErr j
```
The `AssembledN` hunk is an artefact of my extract (cut at RBM2D line 525); the RBM2D lines 526-528 are
```
            ((d.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) +
            ((d.size n : ℕ) : ℝ) ^ (-D) +
            ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j
```
identical to RBM3D after the dictionary. `qvFormN`: the `ukerMat L (mSig E σ_i * mSig E σ_{i+1})` ↦ `uKer d L g (cycProd (fun i => mSigma E (σ i)) i)` hunks are the dictionary: merged `cycProd m i = m i * m (finRotate n i)` (`Kernel/Evolution.lean:49`), i.e. the cyclic successor, as RBM2D's `σ (i + 1)` in `Fin k`. Hypotheses, quantifier order (`k, ε, D, D₁, C_P, C_K` fixed before `∀ᶠ n`), the exponent count `D₁+4D+k+2C_P+8 ≤ C_K`, losses (`N^ε`, `N^{-D}`, `N^{-D₁}`), index ranges (`m ≤ K`, `j < m`, `min m (τ ω)`) are unchanged. `d` enters only through `Zd d`, `N = (WL)^d` (`sz.size`): the label count `(L^d)^k ≤ N^k` keeps the exponent `k` (checked by the proved helper `gridAsm_card_label`). `[NeZero k]` dropped: strictly stronger (T2154a).

Targets (signatures from the file):
```
theorem stoppedAzumaZN (E s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedAzumaZN sz E s t K      -- line 1014, {d} (sz : Sizes d)
theorem assembledN : AssembledN sz                                                  -- line 1605, {d} (sz : Sizes d)
example : ∀ (E s t : ℕ → ℝ) (K : ℕ → ℕ), StoppedAzumaZN sz E s t K := stoppedAzumaZN sz   -- line 2277
example : AssembledN sz := assembledN sz                                                  -- line 2279
```
Both targets are the general pins for every `d` and `sz : Sizes d`; no special case, no extra hypothesis.

## 2. Hidden hypotheses, vacuity, cycles
- `GridAssemblyHypN` is itself a pinned structure (0 hunks vs RBM2D); its fields are premises of `AssembledN`, not hidden: all are discharged at concrete data in `gridAsm_bundle` (§3).
- `AzumaSubGN`, `YMomentsN`/`YMomentsConclN` are statements only (owed to ST2-34/35); no declaration of the file takes them as a hypothesis:
```
$ grep -nwE 'AzumaSubGN|YMomentsN|YMomentsConclN' GridAssemblyN.lean | grep -E '^[0-9]+:(def|theorem|  \(h|    \(h|.*→)'
122:def AzumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
159:def YMomentsConclN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
173:def YMomentsN (κ τ' : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
176:  ∀ (k : ℕ) (σ : Fin k → Bool), YMomentsConclN sz E s t K k σ
```
- Imports: merged `Induction/{GridGoodN,StepDecompN,GridDuhamelN,LoopC2N}` only; no cycle (the module builds as a leaf).
- External hypothesis `sz.SizeTendsto` (premise of `AssembledN`, as RBM2D): limit check is the merged `sz0_tendsto`, used in the instance (`assembledN sz0 sz0_tendsto …`).

## 3. Compiled nonempty instances (d = 3, `sz0`)
- `assembledN`: `gridAsm_assembledN_instance_random` (line 2137) = `gridAsm_assembledN_instance_gen 1 one_pos 1 1 0 (by norm_num) le_rfl` → `assembledN sz0 sz0_tendsto 3 1 _ 1 1 0 17`. Data: `k = 3`, `σ = (+,+,-)`, `E ≡ 1/2`, window `(sInst, tInst) = (0, 1/16)`, `K_n = N_n^{17} ≥ 1`, `Δ = 1/(16 K_n) ≤ N^{-17}`, `KΔ = 1/16`, `P = 1`, `τ ≡ K_n > 0`, `A_0 ≡ 1`, `Z_j = √Δ · Re tr X_{j+1}`, proxy `78 Δ linTrVar + 1 > 0`. Every hypothesis is discharged, including `SubGaussStopN` (`gridAsm_witSubGaussStop`, no hypothesis), `hZmeas`, and the full `GridAssemblyHypN` bundle (`gridAsm_bundle`; `hker` via the new coarse bound `gridAsm_norm_Ugen_coarse`). Nondegeneracy is proved: `gridAsm_witZ_ne_zero` (`∃ ω, Z_j ω ≠ 0`) and `gridAsm_witA_ne` (the bounded process takes two different values). `K_n = N^{17}` is forced by the pin (`Δ ≤ N^{-C_K}`, `C_K ≥ 8 + k`, window `1/16`), not a size trick; RBM2D used `C_K = 138`.
- `stoppedAzumaZN`: `gridAsm_stoppedAzumaZN_instance` (1671) and `…_instance_concrete` (1711) at `n = 0` (`L=4, W=32, N=2^21`), merged grid `(sInst, vg, Kg)` (`Kg 0 = 4`), `k = 3`, `τ ≡ m ≡ 4`, `x = 4√(4C)`; all deterministic hypotheses (`|E|<2`, `0 ≤ s ≤ t < 1`, `K ≠ 0`, `{j<τ} ∈ F_j`, `m ≤ K`) discharged; the right side is `4e^{-4} < 1` (`gridAsm_stoppedAzumaZN_bound_lt_one`). Only `hsub : SubGaussStopN … ZvecN …` (the output of the owed pin `AzumaSubGN`, ST2-34/35) stays a hypothesis, as CLAUDE.md §4 step 2 allows.
- `gridAsm_assembledN_instance_zvec` (2244): same with `Z = ZvecN` (`hZmeas` from `gridAsm_stronglyMeasurable_ZvecN`); only `SubGaussStopN` for `ZvecN` stays.
No `N = 0`, empty index, collapsed window or `False` premise.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.GridAssemblyN
ℹ [3784/3784] Built RBM3D.Induction.GridAssemblyN (12s)
Build completed successfully (3784 jobs).
exit 0          (0 warning/error lines in GridAssemblyN.lean)
$ python3 (parse "GridAssemblyN.lean:<l>: '<name>' depends on axioms: [...]", wrapped lines joined)
2290 stoppedAzumaZN OK            2299 gridAsm_witAzuma OK
2291 assembledN OK                2300 gridAsm_bundle OK
2292 gridAsm_stronglyMeasurable_ZvecN OK   2301 gridAsm_assembledN_instance_gen OK
2293 gridAsm_stronglyMeasurable_YvecN OK   2302 gridAsm_assembledN_instance_random OK
2294 gridAsm_stoppedAzumaZN_instance OK    2303 gridAsm_witZ_ne_zero OK
2295 gridAsm_stoppedAzumaZN_bound_lt_one OK  2304 gridAsm_witZ_zero OK
2296 gridAsm_stoppedAzumaZN_instance_concrete OK  2305 gridAsm_witA_ne OK
2297 gridAsm_grid_data OK         2306 gridAsm_assembledN_instance_zvec OK
2298 gridAsm_witSubGaussStop OK
(OK = exactly [propext, Classical.choice, Quot.sound])
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom" RBM3D/Induction/GridAssemblyN.lean | wc -l
0
$ lake build RBM3D | grep -E "error|Build completed|axiom audit:|premises found"
axiom audit: 4659 theorems, 1662 definitions, 0 axioms in `RBM` ...
premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
Build completed successfully (3918 jobs).
$ lake env lean reg.lean    # import RBM3D; import RBM3D.Induction.GridAssemblyN; #assert_rbm_axioms
axiom audit: 4709 theorems, 1677 definitions, 0 axioms in `RBM` ...
premises found by scanning: 86 (borrowed 0, owed 66, structural 20).
exit 0
```
Premise count unchanged with the module: no registry line needed (`Test/Axioms.lean` untouched is correct).

Name clashes (public declarations of the file vs `git grep main -- RBM3D`, main = `3013163`, which is ahead of the branch base `2f246bf`):
```
44 public names
declaration clashes on main: none
non-gridAsm public names: ['StoppedAzumaZN', 'qvFormN', 'AzumaSubGN', 'YMomentBoundsN', 'YMomentsConclN', 'YMomentsN', 'GridAssemblyHypN', 'AssembledN', 'stoppedAzumaZN', 'assembledN']
```
All other public names carry the `gridAsm_` prefix (§3 (E)); the ten others are pinned names.

## 5. Paper deltas
- Azuma instead of BDG, grid walk instead of stopping times: existing D21, D90 (DECISIONS §7, §10).
- Sub-Gaussian input of the stopped Azuma as a premise: same shape as D205 (`StoppedAzumaN`).
- `[NeZero k]` dropped (strictly stronger): candidate `T2154a` (report (d) 5).
- `YMomentsN` fixes `∃ C_P` after `K` (verbatim RBM2D; unusable by `AssembledN`): candidate `T2154b`.
- `GridAssemblyHypN`/`AssembledN` are Lean-only intermediate forms of `alu9_STime` (`3_5:218-240`) with the D90 losses; no further statement difference found.
Coverage complete.

## 6. Observations (no effect on verdict)
- O1. Report (d) 2 / T2154b: `YMomentsN` as pinned (`C_P` may depend on `K`) cannot feed `AssembledN` (`C_P` before `C_K`); RBM2D bridged with `YMomentsUnifN` (`AzumaProxyN.lean:2042` at `c9a24cf`). This concerns the scope of ST2-34/35, not this ticket's statements: the dispatcher should note it when writing ST2-34/35.
- O2. Report (d) 3: `ellT_mono` needs `0 ≤ sz.lam n` (not a `Sizes` field) for S3-10's `hDcls`; a consumer issue.
- O3. The 2D constant `729` became `78 ≥ ((31/15)^3)^2 = 77.915` (instance-only, `k`/`u_m`-dependent, not `d`-dependent); it appears only in the instance witness proxy, not in any pin.
- O4. The `stoppedAzumaZN` instance keeps `hsub` (output of the owed `AzumaSubGN`); the merged `StepDecompN_subGaussStopN_zvecN` (`StepDecompN.lean:1317`) would discharge it only from pathwise `linTrVar` bounds of the loop gradients, which is ST2-34/35 work.

## Verdicts
- Target 1 (pins `StoppedAzumaZN`, `qvFormN`, `AzumaSubGN`, `YMomentBoundsN`, `YMomentsConclN`, `YMomentsN`, `GridAssemblyHypN`, `AssembledN`): **PASS**.
- Target 2 (`stoppedAzumaZN`, `assembledN`): **PASS**.
- Target 3 (instances at `d = 3`, `sz0`): **PASS**.

Ticket T2154: **PASS**. No dispatcher sign-off needed for the merge (O1 is input for ST2-34/35).
