Auditor model: claude-opus-5-5

# T2353 audit (round 1) — Fri Oct  9 00:50:47 UTC 2026

Branch `t/T2353` at `c924852` (main `d525990`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2353-audit1` (detached).
Source: RBM2D `RBM2D/Universality/GUEPhase/OneLoop.lean`, RBM2D HEAD `9e0f275`.

## 1. Statements against the pin (source statement under the ticket's port map), by script
```
$ python3 -I sdiff.py ../RBM2D/RBM2D/Universality/GUEPhase/OneLoop.lean RBM3D/Universality/GUEPhase/OneLoop.lean
  # map: d.L n/d.W n/d.size -> sz.*, Z2 -> Zd d, Coord ( -> CoordF d (, gloop .. (blockMat ( -> loopL d .. (blockMat d L W (,
  #      spectralZ/M -> zt/mE, Xmat ( -> Xmat d (, (Pgue d)/PathΩ d/SeqΩ d/SeqCoord d/olComb d/olVar d/slice d n/gueH d/gueScale d -> sz
=== olComb IDENTICAL
=== olComb_measurable IDENTICAL
=== olVar IDENTICAL
=== ol_map_comb IDENTICAL
=== ol_map_comb_slice IDENTICAL
=== ol_gueH_eq IDENTICAL
=== gueGrid_expect_oneLoop DIFF
  replace src: {κ | port: (hd : 3 ≤ d) {Λ κ
  insert src:  | port: (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
```
Port statement of the main target (file:1308):
```
theorem gueGrid_expect_oneLoop (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) {E t1 t0 : ℕ → ℝ} {K : ℕ → ℕ}
    (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1) (hK : ∀ n, K n ≠ 0)
    (h1 : StochDomAt (Pgue sz) sz.size (fun n (p : Fin (K n + 1) × Zd d (sz.L n)) ω => ‖loopL … ⟨[true], [p.2]⟩ - mE (E n)‖)
      (fun n p _ => (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p, ‖(∫ ω, loopL … ∂(Pgue sz)) - mE (E n)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale …)⁻¹ ^ 2
```
Assessment of the two added hypotheses (the only deviation from the port map):
- `hd : 3 ≤ d`: the paper's standing assumption (d ≥ 3); required by the merged `Green.stable_svar_bulk_vtx`.
- `hlam`: the d = 2 source has no coupling parameter in its variance profile; RBM3D's `Sizes d` carries `lam`
  (`Defs/Sizes.lean:144`), and the `L`-uniform `d ≥ 3` stability constant needs `0 < g ≤ Λ`:
```
$ grep -n "theorem stable_svar_bulk_vtx" -A2 RBM3D/Green/Stability.lean
320:theorem stable_svar_bulk_vtx (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ κ E t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
321-    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
322-    Stable (svar d L W g) ((t : ℂ) * mE E ^ 2) (Kstab3 d Λ κ) := by
$ sed -n 163,165p RBM3D/Defs/Sizes.lean
/-- `(eq:WO)` (`1_2:363`): `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡^{-1}`, eventually along the sequence. -/
def WO (𝔡 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹
$ grep -n "label{eq:WO}" paper/tex/1_2_Intro_model_result.tex
363:\be\label{eq:WO} W^{-d/2+\fd}\le \ilambda \le \fd^{-1}.\ee
```
  `hlam` is implied by the paper's `(eq:WO)` with `Λ = 𝔡⁻¹` (lower bound `W^{…} > 0`), so it is a paper assumption
  made explicit, not a strengthening beyond the paper. The `log L` constant of the d = 2 source is replaced by
  `Kstab3 d Λ κ` (no `L`), which is the `d ≥ 3` replacement the ticket asked for. Quantifier order (fixed
  `κ, Λ, E, t1, t0, K` before `∀ ε, ∀ᶠ n, ∀ p`), loss `N^ε`, exponent `-2`, time/energy windows: unchanged vs source.
  Covered by paper-delta candidates `T2353a` (hypotheses) and `T2353b` (constant) of the prove report (d).

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "^\s*(private )?(structure|class|axiom|opaque)|: Prop" RBM3D/Universality/GUEPhase/OneLoop.lean
152:  classical   (and 221, 630, 864, 971, 1140: the tactic `classical` only)
```
No new structure, class or `Prop` definition; no hypothesis in a structure field. The only non-deterministic
hypothesis is `h1` (`StochDomAt`, merged definition; the §7.2 pathwise one-loop bound = another gate's output),
identical to the source's. Limit check (TEAM §8 lesson 14) is in the prove report (a)(ii): `Λ_n = (N_n η)⁻¹ → 0`,
conclusion/hypothesis ratio `N^ε Λ → 0` for `ε < 1`, so the conclusion is a strict improvement, not contradictory.
Dependencies are merged modules (imports: `Universality.GUEPhase.Grid`, `Gauss.SteinMatrix`, `Green.Stability`,
`Hierarchy.ContractionSecondLoop`, `Gauss.LoopFlowStein`, `Loop.KLSumZero`; no `import RBM3D`); a new file cannot be
imported by them, so no cycle.

## 3. Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.OneLoopInst`, file:1378-1528)
```
$ grep -c "^example" RBM3D/Universality/GUEPhase/OneLoop.lean
11
$ sed -n 1471,1478p RBM3D/Universality/GUEPhase/OneLoop.lean     # hlam at sz0
private theorem OneLoopInst_lam_window : ∀ᶠ n : ℕ in atTop, 0 < sz0.lam n ∧ sz0.lam n ≤ 10 := by
  refine Eventually.of_forall fun n => ?_
  ...
```
Data: `SizesInst.sz0` (`d = 3`, `L 0 = 4`, `W 0 = 32`, `N 0 = 2097152`, `lam n = (2(n+1))^{-6}`, satisfies
`sz0_WO : sz0.WO (1/10)`, `Defs/Sizes.lean:311`), `t₀ = 9/10`, `t₁ = e^{-1/20}·9/10`, `K = 4`, `E = 1`, `κ = 1/2`, `Λ = 10`.
- `olComb`, `olVar`: concrete evaluations at `a=1/2, b=1/3, k=0,4`, diagonal and off-diagonal coordinate, positivity.
- `olComb_measurable`, `ol_map_comb`, `ol_map_comb_slice`, `ol_gueH_eq`: applied at `sz0`, `k = 4`, `n = 0` and all `n`.
- `gueGrid_expect_oneLoop`: `OneLoopInst_main` (file:1484-1505) applies it with `hd` (`norm_num`), `hκ`, `hsize`
  (`sz0_tendsto`), `hlam` (`OneLoopInst_lam_window`), `hE`, `ht1`, `ht10`, `ht0`, `hK` all discharged; only `h1`
  remains a hypothesis (allowed: another gate's pin). The final `example` specialises to `ε = 1/2` and concludes
  `∃ n, ∀ p, …` via `Filter.Eventually.exists`. Nondegenerate: `d = 3`, `N ≥ 2^21`, 5 grid times, nonempty `Zd 3 4`.
All compile (module build below).

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Universality.GUEPhase.OneLoop > abuild.log 2>&1; echo exit=$? >> abuild.log; tail -3 abuild.log
✔ [3743/3743] Built RBM3D.Universality.GUEPhase.OneLoop (11s)
Build completed successfully (3743 jobs).
exit=0
$ grep -n "OneLoop.lean" abuild.log | grep -ci "warning\|error"      # warnings in the log are all in upstream modules
0
$ lake env lean ax.lean   # ax.lean = OneLoop.lean + #print axioms lines (scratch copy, not in repo)
'RBM.Univ.GUEPhase.olComb_measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ol_map_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ol_map_comb_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.ol_gueH_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueGrid_expect_oneLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private…OneLoopInst.OneLoopInst_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private…OneLoopInst.OneLoopInst_lam_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.olComb' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.olVar' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom\b|set_option maxHeartbeats" RBM3D/Universality/GUEPhase/OneLoop.lean | wc -l
       0
$ git diff --stat main...t/T2353
 RBM3D/Universality/GUEPhase/OneLoop.lean | 1528 ++++++++++++++++++++++++++++++
 1 file changed, 1528 insertions(+)
```
Only the sole writable file (new) is touched; no frozen signature changed. 1528 lines (< 2300 stop line).
Full `lake build` is the hub's at merge (the prove report b.1 shows it and the registry pre-check, exit 0).

## 5. Paper deltas
Lean/paper (and Lean/source) statement differences and their coverage in the prove report (d):
| difference | candidate |
|---|---|
| added `3 ≤ d`, `∀ᶠ n, 0 < lam n ≤ Λ` vs d = 2 source | `T2353a` |
| `1 + cShortRow κ (1 + log L)` ↦ `Kstab3 d Λ κ` (no `log L`) | `T2353b` |
| Lean target is the GUE-phase-grid form `N^ε (Nη_u)^{-2}`, paper states only band-flow `lem:improve_exp_aver` and "essentially identical" for the GUE phase | `T2353c` |
All differences covered.

## 6. Verdict per target
| target | verdict |
|---|---|
| `olComb` | PASS |
| `olComb_measurable` | PASS |
| `olVar` | PASS |
| `ol_map_comb` | PASS |
| `ol_map_comb_slice` | PASS |
| `ol_gueH_eq` | PASS |
| `gueGrid_expect_oneLoop` | PASS (two added hypotheses, both paper assumptions — `d ≥ 3` and `(eq:WO)`; covered by `T2353a`) |

Observations (no effect on statements, instances, build, axioms or delta coverage):
- O1. The consumer UN-47 (`Eq729A`/`Eq729B`) must supply `hd` and `hlam`; `Sizes.WO 𝔡` gives `hlam` with `Λ = 𝔡⁻¹`.
- O2. The `#print axioms` of private declarations display as `_private…` names when the file is read as a copy; same axiom set.

Overall: **PASS**. No dispatcher sign-off needed.
