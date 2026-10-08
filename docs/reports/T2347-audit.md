Auditor model: claude-opus-5-5

# T2347 audit (round 1), Thu Oct  8 22:28:51 UTC 2026

Branch `t/T2347` at `30a4956`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2347-audit1` (detached). Scratch scripts: scratchpad `T2347/` (`privcheck.py`, `stmt.py`, `axioms.lean`).

## 1. Statements vs the ticket's pin (source statements + port map), by script

```
$ python3 -I T2347/stmt.py   (extract the 5 targets from RBM2D EntryGrid.lean @9e0f275 and RBM3D EntryGrid.lean;
                              regex port map: d.L/d.W/d.size->sz., Idx->Idx d, Coord->CoordF d, Xmat->Xmat d,
                              ouP (L)(W)->ouP (UNModel.band sz) n, mixMat (L)(W)->mixMat sz n, X d->X sz,
                              spectralZ/M->zt/mE, ^ 2)⁻¹ -> ^ d)⁻¹; token diff)
## EntryGrid_var: RBM2D :395 -> RBM3D :76
   identical after port map
## EntryGrid_map_gueH: RBM2D :402 -> RBM3D :83
   identical after port map
## map_gueH_eq_mixMat: RBM2D :437 -> RBM3D :118
   identical after port map
## EntryGrid_pgue_preimage: RBM2D :480 -> RBM3D :162
   identical after port map
## gueGrid_entry_bound: RBM2D :812 -> RBM3D :518
   insert: - (none)  + (hd : 3 ≤ d)
   insert: - (none)  + 𝔡
   delete: - (h𝔠 : 0 < 𝔠)  + (none)
   replace: - Admissible  + sz.Admissible
   replace: - d)  + 𝔡)
```

The residual `gueGrid_entry_bound` differences are forced by the merged dependency (signatures read in the worktree):
```
RBM3D/Defs/Sizes.lean:177   def Admissible (𝔠 𝔡 : ℝ) : Prop := 0 < 𝔠 ∧ 0 < 𝔡 ∧ sz.SizeTendsto ∧ sz.Bandwidth 𝔠 ∧ sz.WO 𝔡
RBM3D/Universality/GUEPhase/EntryTail.lean:94   def GUEEntryMix (d : ℕ) : Prop := ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ, 0 < κ → ...
     ... ((sz.size n : ℕ) : ℝ) ^ τ * (maxLoopPM ... + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) < ... ≤ ENNReal.ofReal (N ^ (-D))
RBM3D/Universality/GUEPhase/EntryTailMain.lean:545   theorem gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d
```
`h𝔠 : 0 < 𝔠` is the first conjunct of `sz.Admissible 𝔠 𝔡` (not lost); `hd : 3 ≤ d` and `𝔡` are the inputs of `gueEntryMix`; `W^{-2} ↦ W^{-d}` matches `GUEEntryMix`. Quantifier order (fixed `𝔠 𝔡 κ n0 E t1 t0 δ c₀` before `StochDomAt`, i.e. before `∀ τ D, ∀ᶠ n`), hypotheses `hE ht1 ht10 ht0 hδ0` (`∀ n`) and `hδ` (`∀ᶠ n`), the index range `Fin (gueGridK sz n0 n + 1) × Idx × Idx`, the size scale `sz.size`, the 2-loop maximum `gueLmax _ 2` and the error term are as in the source. All statement differences are covered by the report's candidate `T2347a`. Verdict on statements: as pinned.

## 2. Hidden hypotheses, vacuity, cycles

- No target takes a structure or a `Prop` pin as hypothesis; `sz.Admissible` is the conjunction above (shown), discharged in the instance by the merged proof `sz0_admissible`.
- Dependencies are merged results on `main`: `gueEntryMix` (theorem, EntryTailMain:545), `Pgue`, `gueH`, `gueLmax`, `gridTime`, `gueGridK`, `mixMat`, `mixSample_law`, the 8 reused `GUEPhaseGrid_` lemmas. Imports: only the two pinned modules:
```
$ grep -n "^import" RBM3D/Universality/GUEPhase/EntryGrid.lean
6:import RBM3D.Universality.GUEPhase.EntryTailMain
7:import RBM3D.Universality.GUEPhase.Proc
```
- No cycle (new leaf module, imports only merged modules). No external hypothesis is introduced (none needs a limit check); the `Admissible` limits (`N → ∞`, `W ≥ N^𝔠`, `(eq:WO)`) are proved at `sz0` by the merged `sz0_admissible`.
- Non-vacuity: the conclusion `StochDomAt` is a real tail bound; the instance below has every premise true at nondegenerate data.

## 3. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.EntryGridInst`, file :617-724)

Data (checked in the audit worktree):
```
$ lake env lean T2347/axioms.lean   (excerpt)
RBM.Gauss.SizesInst.sz0_admissible : RBM.Gauss.SizesInst.sz0.Admissible (1 / 6) (1 / 10)
GridCheck.t1_pos : 0 ≤ (1 - RBM.Univ.ouZeta (1 / 20)) * (9 / 10)
def RBM.Gauss.SizesInst.sz0 : RBM.Gauss.Sizes 3 :=
{ L := fun n => 4 * (n + 1), W := fun n => (2 * (n + 1)) ^ 5, lam := fun n => ((2 * (↑n + 1)) ^ 6)⁻¹, ... }
```
- `map_gueH_eq_mixMat` (ticket-required): `example` :648-656 at `sz0`, `n = 0` (`L = 4`, `W = 32`, `N = 2097152`), `t0 = 9/10`, `t1 = e^{-1/20}·9/10`, `K ≡ 4`, `k = 2`; and :659-667 for all `n k`. Hypotheses `ht1` (`GridCheck.t1_pos`), `ht10` (`t1_le`, proved :624) discharged. Nondegenerate (`t0 - t1 > 0`, `k` interior).
- `gueGrid_entry_bound` (ticket-required): named theorem `gueGrid_entry_bound_sz0` :698-722 at `d = 3`, `sz0`, `(𝔠,𝔡) = (1/6,1/10)`, `κ = 1`, `E ≡ 0`, `n0 = 1`, `δ_n = N^{-1/4}`, `c₀ = 1/4`; every hypothesis discharged (`le_rfl : 3 ≤ 3`, `sz0_admissible`, `one_pos`, `|0| ≤ 1` by `simp`, `t1_pos`, `t1_le`, `9/10 < 1`, `rpow_nonneg`, `1/4 > 0`, `hδ` by `le_rfl` for all `n`). No pin left as hypothesis. Not degenerate (no `N = 0`, nonempty index, `t0 < 1`, `δ > 0`).
- `EntryGrid_var` (:630-635), `EntryGrid_map_gueH` (:638-645), `EntryGrid_pgue_preimage` (:682-693, `B = {∀ i, ‖M i i‖ ≤ 1}` measurable by :670-680): instances also present at the same data.
All compile (module build below).

## 4. Build, axioms, hygiene, file scope

```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2347-audit1 && lake build RBM3D.Universality.GUEPhase.EntryGrid 2>&1 | grep -E "error|Build"
Build completed successfully (3759 jobs).
(0 error lines; warnings only in other, merged modules: longLine / unused-variable linters)
$ lake env lean T2347/axioms.lean   (excerpt)
'RBM.Univ.GUEPhase.EntryGrid_var' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.EntryGrid_map_gueH' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.map_gueH_eq_mixMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.EntryGrid_pgue_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueGrid_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.EntryGridInst.gueGrid_entry_bound_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b" EntryGrid.lean Grid.lean | wc -l
       0
$ git diff --name-only main...t/T2347
RBM3D/Universality/GUEPhase/EntryGrid.lean
RBM3D/Universality/GUEPhase/Grid.lean
```
Both are the ticket's sole writable files. Main has advanced since the branch base `0e53fe5` (to `168c9fd`):
```
$ git diff --stat 0e53fe5 main -- RBM3D/
 RBM3D/Universality/GUEPhase/DuhamelA1.lean | 1266 ++++++++++++++++++++++++++
 RBM3D/Universality/GUEPhase/DuhamelA2.lean | 1334 ++++++++++++++++++++++++++++
$ git grep -nE "(theorem|lemma|def) (map_gueH_eq_mixMat|gueGrid_entry_bound|EntryGrid_|GUEPhaseGrid_seqXmat|...|GUEPhaseGrid_measurable_Xmat)" main -- RBM3D | grep -v GUEPhase/Grid.lean | wc -l
       0
```
No overlap with the files merged since, no name clash on `main`.

**CONTROL H143: `Grid.lean` diff is keyword deletions only.**
```
$ git diff main...t/T2347 -- RBM3D/Universality/GUEPhase/Grid.lean   (-U0, via T2347/privcheck.py)
$ python3 -I T2347/privcheck.py
removed 8 added 8 all pairs = removed minus leading 'private ': True
   lemma GUEPhaseGrid_seqXmat_add
   lemma GUEPhaseGrid_seqXmat_smul
   lemma GUEPhaseGrid_seqXmat_sum
   lemma GUEPhaseGrid_real_smul_matrix
   lemma GUEPhaseGrid_map_combined_eq_mixed
   lemma GUEPhaseGrid_Pgue_eq_mixed :
   lemma GUEPhaseGrid_map_slice_infinitePi
   lemma GUEPhaseGrid_measurable_Xmat
```
Each of the 8 un-privated declarations is used by the new file, and none exists elsewhere:
```
GUEPhaseGrid_seqXmat_add uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_seqXmat_smul uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_seqXmat_sum uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_real_smul_matrix uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_map_combined_eq_mixed uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_Pgue_eq_mixed uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_map_slice_infinitePi uses_in_EntryGrid=1 defs_elsewhere=0
GUEPhaseGrid_measurable_Xmat uses_in_EntryGrid=2 defs_elsewhere=0
```
The list matches the prove report's reuse list. No signature in `Grid.lean` changed (visibility only), so nothing frozen was touched. The full `lake build` / `#assert_rbm_axioms` is the hub's step at merge.

## 5. Paper-delta coverage

- `T2347a` (prove report (d)): the `gueGrid_entry_bound` changes against RBM2D (`hd`, `𝔡`, `h𝔠` folded into `sz.Admissible`, `W^{-2} ↦ W^{-d}`). This covers every residual in §1.
- `T2347b`: the grid statements (`map_gueH_eq_mixMat`, `gueGrid_entry_bound`) are Lean-side scaffolding with no counterpart in the paper (the paper's `1_2:566-570` says it is "essentially identical" to [YY_25]). The candidate is recorded.
- No other Lean/paper difference found. `docs/paper-deltas.md` has no T2347 entries yet (expected; the dispatcher numbers them).

## Observations (not defects)

- O1. `GUEPhaseGrid_Pgue_eq_mixed` and `GUEPhaseGrid_map_combined_eq_mixed` are now public, but their statements mention the still-private `GUEPhaseGrid_mixedStepMeasure`. The build passes. A downstream user outside these modules cannot name that def, though; a cleanup ticket could make it public.
- O2. `EntryGrid_maxLoopPM_le` and `EntryGrid_gres_zero_true` duplicate the private twins `Proc_maxLoopPM_le_loopMax` and `gres_zero_true`. The report says so; this changes no statement.

## Verdicts

| target | verdict |
|---|---|
| `EntryGrid_var` | PASS |
| `EntryGrid_map_gueH` | PASS |
| `map_gueH_eq_mixMat` | PASS |
| `EntryGrid_pgue_preimage` | PASS |
| `gueGrid_entry_bound` | PASS (statement delta T2347a, forced by merged `gueEntryMix`) |

Overall: **PASS**. No dispatcher sign-off needed.
