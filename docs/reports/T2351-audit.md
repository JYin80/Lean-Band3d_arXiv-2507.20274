Auditor model: claude-opus-5-5

# T2351 audit (round 1): UN-39/40 `Universality/GUEPhase/DuhamelC`

Audit time: Fri Oct  9 00:20:14 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2351-audit1`, detached at `t/T2351` = `a2e6b55`, merge-base with `main` = `bb0dc24`.
Target (ticket): `RBM.Univ.GUEPhase.gueGrid_loop_duhamel`, port of RBM2D `Universality/GUEPhase/DuhamelC.lean:1495`.

## 1. Statement against the pin (source plus ticket port map, diffed by script)

The ticket pins the statement as the source's with the port map (`sz : Sizes d`, `Z2`->`Zd d`, `gloop .. (blockMat M)`->`loopL d .. (blockMat d .. M)`, `genMatGUE d`, `spectralZ`->`zt`). The map is applied by the auditor's own script to the source lines, then diffed against the port:
```
$ sed -n 1495,1516p RBM2D/.../GUEPhase/DuhamelC.lean > src.lean
$ sed -n 1485,1506p RBM3D-wt/T2351-audit1/RBM3D/Universality/GUEPhase/DuhamelC.lean > port.lean
$ cat map.pl
  s/\bd\.L n\b/sz.L n/g; s/\bd\.W n\b/sz.W n/g; s/\bd\.size\b/sz.size/g; s/\bd\b/sz/g;
  s/\(sz : Sizes\)/{d : ℕ} (sz : Sizes d)/g; s/Z2 \(sz\.L n\)/Zd d (sz.L n)/g;
  s/gloop \(sz\.L n\) \(sz\.W n\) \(blockMat/loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)/g;
  s/genMatGUE \(sz\.L n\)/genMatGUE d (sz.L n)/g; s/\bspectralZ\b/zt/g;
$ perl map.pl < src.lean > src_mapped.lean; diff src_mapped.lean port.lean && echo "IDENTICAL (22 lines)"
IDENTICAL (22 lines)
```
So the hypotheses (`hκ`, `hτU`, `hsize`, `hE`, `ht1`, `ht10`, `ht0`, `hscale`, `_hm1`, `hm`), their order, the index set `Fin (gueGridK sz n0 n + 1) × (Fin m → Bool) × (Fin m → Zd d (sz.L n))`, the size scale `sz.size`, the bound (`√(t−t₁)·sup_j √(N⁻¹η⁻²·gueLmax(2m)) + (gueScale)⁻ᵐ`) and the loss exponents are the source's, with exactly the ticket's renames. No `hd : 3 ≤ d` is added, nothing weakened. The `d`-dependent steps (`(L^d)^m ≤ N^m`; `2 ≤ N` taken eventually from `hsize` instead of `9 ≤ (WL)^2`) are inside private lemmas and do not touch the public statement.

## 2. Hidden hypotheses, vacuity, cycles

```
$ grep -nE "^(private )?(noncomputable )?(def|abbrev|structure|class|instance|axiom|opaque|theorem|lemma|example)|^variable" DuhamelC.lean | grep -v "private theorem\|private lemma"
92/145/350:variable {d : ℕ} {sz : Sizes d} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {e : ℝ} {I : LoopIdx (Zd d (sz.L n))}
911/1065/1257:variable {d : ℕ} (sz : Sizes d)
914:private def DuhamelC_lam0 (n0 N : ℕ) : ℝ := ((N : ℝ) ^ (40 * n0 + 80))⁻¹
917:private def DuhamelC_epsY (n0 N : ℕ) : ℝ := ((N : ℝ) ^ (2 * n0 + 2))⁻¹
1485:theorem gueGrid_loop_duhamel ...
1527:private abbrev DuhamelCInst_t1 : ℕ → ℝ := fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)
1528:private abbrev DuhamelCInst_t0 : ℕ → ℝ := fun _ => 9 / 10
1547:theorem hscale_check :
1568:theorem gueGrid_loop_duhamel_check :
$ grep -cE "^private (theorem|lemma|def)" DuhamelC.lean
42
```
- No new structure or class; `variable`s carry no hypotheses (only data). The only structure in the signature is the merged `Sizes d` (fields `L`, `W`, `lam`, `three_le_L`, `W_pos`; `Defs/Sizes.lean`), no hypothesis field.
- All objects in the statement (`StochDomAt`, `Pgue`, `gueH`, `gueGridK`, `gridTime`, `gridStep`, `gueScale`, `gueLmax`, `genMatGUE`, `loopL`, `blockMat`, `etaT`, `zt`) are merged definitions, none defined in this file.
- No external hypothesis: the statement is unconditional except for its deterministic/limit hypotheses, which the instance discharges (`hsize`, `hscale` are limit statements on the size sequence and are proved at `sz0`).
- Cycle: imports are `DuhamelA2, DuhamelB, Markov, Proc, Induction.PerTimeCalc, Green.Pins` (all merged on `main`); nothing imports the new file. `Markov` and `DuhamelA2` are beyond the ticket's four named imports; both are merged and used (`MarkovInst.sz0_size_tendsto_nat`, DuhamelA2 bounds), allowed by "only what a lemma needs". Not `import RBM3D`.

## 3. Compiled nonempty instance

`RBM.Univ.GUEPhase.DuhamelCInst.gueGrid_loop_duhamel_check` (`DuhamelC.lean:1568`) is the term
```
gueGrid_loop_duhamel sz0 (κ := 1) (τU := 1 / 2) one_pos (by norm_num) 1
  (E := fun _ => (0 : ℝ)) (t1 := DuhamelCInst_t1) (t0 := DuhamelCInst_t0)
  MarkovInst.sz0_size_tendsto_nat (fun n => by norm_num) (fun _ => GridCheck.t1_pos)
  DuhamelCInst_t1_le_t0 (fun _ => by norm_num) hscale_check 2 (by norm_num) (by norm_num)
```
Data: `sz0 : Sizes 3` (`Defs/Sizes.lean:260`: `L n = 4(n+1)`, `W n = (2(n+1))^5`, `sz0.size 0 = 2097152` by `sz0_values`), `d = 3`, `κ = 1`, `τU = 1/2`, `n₀ = 1`, `m = 2`, `E = 0`, `t₀ = 9/10`, `t₁ = (1 − ouZeta(1/20))·9/10`. Every hypothesis is discharged by a proof term: `hsize` by merged `Markov.lean:1122 sz0_size_tendsto_nat`; `hE : |0| ≤ 1`, `ht0`, `1 ≤ 2`, `2 ≤ 2·1` by `norm_num`; `ht1` by merged `Grid.lean:800 GridCheck.t1_pos`; `ht10` by `DuhamelCInst_t1_le_t0` (`exp(−1/20) ≤ 1`); `hscale` by `hscale_check` (proved: `etaT 0 (9/10) = 1/10` from `(mE 0).im = 1`, then `10/N ≤ N^{-1/2}` for `N ≥ 100`, eventually). Nondegenerate: `N ≥ 2097152`, label set `Fin (K+1) × (Fin 2 → Bool) × (Fin 2 → Zd 3 (4(n+1)))` nonempty, window `t₀ − t₁ > 0`, no `False` premise, no hypothesis left open. It compiles (section 4).

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Universality.GUEPhase.DuhamelC      (audit worktree)
✔ [3796/3796] Built RBM3D.Universality.GUEPhase.DuhamelC (12s)
Build completed successfully (3796 jobs).
exit=0      (grep of "error" / "warning.*DuhamelC.lean" in the log: no lines)
$ lake env lean ax.lean     # import ...DuhamelC; #print axioms of the three public theorems
'RBM.Univ.GUEPhase.gueGrid_loop_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelCInst.hscale_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.DuhamelCInst.gueGrid_loop_duhamel_check' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean reg.lean    # import RBM3D; import ...DuhamelC; #assert_rbm_axioms
exit=0
axiom audit: 10473 theorems, 3076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ grep -nE "sorry|admit|native_decide|^axiom|implemented_by|extern" DuhamelC.lean
1519:of the target is discharged; there is no external hypothesis. -/      (docstring word "discharged"; no forbidden token)
$ git diff --name-status main...t/T2351
A	RBM3D/Universality/GUEPhase/DuhamelC.lean
$ name-clash grep (RBM3D/, outside Probe/ and the new file): gueGrid_loop_duhamel 0, DuhamelCInst 0, hscale_check 0
```
Only the sole writable file is added; no existing file (hence no frozen signature) is touched. File length 1602 (below the ticket's 1800 and the stop size 2100; no split required).

## 5. Paper deltas

The target is an internal lemma of the RBM2D-style GUE-phase universality chain (design UN-D1); the paper's universality argument is cited to other work and has no statement of this Duhamel bound:
```
$ grep -c "GUE" paper/tex/{3_5,6,7_8,A,B}*.tex
6_Step6_two_loop.tex:0  7_8_light_weight.tex:0  3_5_Loop_Hierarchy.tex:0  A_deterministic_estimates.tex:0  B_graphical_lemmas.tex:0
```
(`GUE` occurs only in `1_2_Intro_model_result.tex`, in the model definition and the universality theorem statement, not in a Duhamel/grid lemma.) The Lean statement equals the source's under the ticket's port map (section 1), so there is no Lean/paper statement difference to cover; "no candidate" in prove report (d) is correct.

## Observations (no effect on statement, instance, build, axioms or deltas)
- Imports `Markov` and `DuhamelA2` in addition to the ticket's four named modules; both merged and used.
- The instance is a named theorem rather than an `example`; allowed by CLAUDE.md §4 step 2 ("or a named check").

## Verdict

| Target | Verdict |
|---|---|
| `RBM.Univ.GUEPhase.gueGrid_loop_duhamel` | **PASS** |

Ticket T2351: **PASS**. No dispatcher sign-off needed.
