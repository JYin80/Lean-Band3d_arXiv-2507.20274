Auditor model: claude-opus-5-5

# T2097 audit (round 1) — ST2-25 Path/UBounds, Path/UTransport, Path/KellStar

Written: Sun Oct  4 02:33:10 UTC 2026 (`date -u`). Branch `t/T2097` at `8587022`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2097-audit1` (detached). Targets per ticket + Amend 1 (`tailtoTail`
removed): `thetaGenMat`, `thetaGen`, `normSqSpectralMOne`, `ukerNonneg`, `ukerRowSum`, `sumNdecay`,
`sumNdecayEta`, `uopBack`, `uopOneStep`, `uopLocalMax`, `uopPairLocalMax`, `kellStarEv`.

## 1. Statement vs pin (script diff against RBM2D `c9a24cf` after the ST1-COMMON renaming)
The ticket has no pinned text (check file only `#check`s upstream names); the pin is the RBM2D statement
with the class-b `d` replacements. Script: extract every `def [A-Z]…` block of RBM2D `Path/UBounds` and
`Path/UTransport` (up to `TailtoTail`), apply `Z2 L→Zd d L`, `zdist2 L→zdistInf d L`,
`(ukerMat|Uop|thetaGenMat|thetaGen|SB|Theta) L→… d L g`, `spectralM→mE`, `(L:ℝ)^2→(L:ℝ)^d`,
`UkerFar L W→UkerFar d L W g`, then `diff` with the RBM3D blocks:
```
pins: 10 vs 10
1c1  < def UopOneStep : Prop :=            > def UopOneStep (d : ℕ) (g : ℝ) : Prop :=
8c8  < def UkerNonneg : Prop :=            > def UkerNonneg (d : ℕ) (g : ℝ) : Prop :=
11c11 < def UkerRowSum : Prop :=           > def UkerRowSum (d : ℕ) (g : ℝ) : Prop :=
14c14 < def SumNdecay : Prop :=            > def SumNdecay (d : ℕ) (g : ℝ) : Prop :=
18c18 < def SumNdecayEta : Prop :=         > def SumNdecayEta (d : ℕ) (g : ℝ) : Prop :=
22c22 < def UopBack : Prop :=              > def UopBack (d : ℕ) (g : ℝ) : Prop :=
26c26 < def UkerFar (L W : ℕ) [NeZero L] (u v R D' : ℝ) : Prop :=
      > def UkerFar (d L W : ℕ) [NeZero L] (g u v R D' : ℝ) : Prop :=
28c28 < def UopLocalMax : Prop :=           > def UopLocalMax (d : ℕ) (g : ℝ) : Prop :=
36c36 < def UopPairLocalMax : Prop :=       > def UopPairLocalMax (d : ℕ) (g : ℝ) : Prop :=
```
(condensed side by side; no body line differs; `thetaGenMat`/`thetaGen` bodies identical after renaming).
- Bodies identical after renaming: same windows (`0 ≤ v ≤ w`, `wξ < 1`; `0 ≤ u ≤ t < 1`; `u + Δ < 1`;
  `|E| < 2`, `w < 1`), same constants `1, 4, 3`, same factor `(η_v/η_w)²`. `g` is universally
  quantified (outside the pin), so each theorem `(d g) : Pin d g` is the general form for every real `g`.
- `L²→L^d` in `UopLocalMax`/`UopPairLocalMax` (far count `card (Zd d L) = L^d`): the correct d-form.
- `KellStarEv` (KellStar:54-64) vs RBM2D `KellStar:53` (read side by side): `d : Sizes`→`sz : Sizes d`;
  `Tendsto d.size`→`sz.SizeTendsto`; `Bandwidth d c`→`sz.Bandwidth 𝔠`; `RangeCond`; `zdist2`→`zdistInf`;
  `ellStar L W u`→`(log W)^{3/2} * ellT L (lam n) u` inline. Added hypotheses: `3 ≤ d`, `0 < Λ`,
  `∀ᶠ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ` (window of `Prop5Decay`, Amend 1). Quantifier order unchanged
  (fixed `𝔠 Λ τ δ D t` before `∀ᶠ n`, then `∀ s u`, `0 ≤ s ≤ u ≤ t n`, `∀ a b`); `D` arbitrary.
- Dropped and justified: `KpmBoundProp5`/`kpmBoundProp5` (ticket), `ThetaMaxNorm`/`thetaMaxNorm`
  (portmap P.1 row 24 lists only `kellStarEv`: `| 24 | Path/KellStar | … | kellStarEv [ST-4] |`),
  `tailtoTail` + `uT_scalar`, `uT_zdist_neg`, `uT_near_far` (Amend 1).
- `EKSumNdecay`: not a hypothesis of any RBM2D statement in these files:
```
$ git -C ../RBM2D show c9a24cf:RBM2D/Path/$f.lean | grep -c 'EKSumNdecay\|SumNdecayHyp'
UBounds: 0   UTransport: 0   KellStar: 0
```
- `Prop5Decay` is discharged inside the proof, not taken as a hypothesis:
```
RBM3D/Path/KellStar.lean:175:  obtain ⟨C, hC, c, hc, hP⟩ := prop5Decay_holds d Λ hd hΛ
```
Statement verdict: every target matches the RBM2D pin up to the forced `d ≥ 3` changes. **PASS.**
## 2. Vacuity, hidden hypotheses, cycles
- No new structure. `Sizes d` (merged, `Defs/Sizes.lean:138`) has only `L W lam three_le_L W_pos`.
- External-hypothesis limit check for the added `∀ᶠ n, 0 < lam n ≤ Λ`: it follows from the paper's
  standing hypothesis `(eq:WO)`:
```
RBM3D/Defs/Sizes.lean: def WO (𝔡 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹
```
  (`W^{…} > 0` gives `0 < lam`; take `Λ = 𝔡⁻¹`). The bridge lemma is not in Lean (prove report b.9
  says so); it is a one-line consequence, so not a defect of this ticket.
- `prop5Decay_holds` (`Propagator/Prop5Hold.lean:784`, merged) and `RangeCond` (`Green/Pins.lean:55`),
  `Bandwidth`, `SizeTendsto` (`Defs/Sizes.lean:168,173`) are merged; the three new files import only
  merged modules (`Path/Kernel`, `Propagator/{Deriv,Prop5Hold}`, `Loop/GLoop`, `Green/Pins`,
  `Defs/Sizes`) and each other (UBounds ← UTransport, KellStar). No cycle.
- `UkerFar` is a data condition registered in `Test/Axioms.lean` `structuralProps` (registry-line diff
  only, §4). **PASS.**

## 3. Compiled nonempty instances (read in the files; compiled by the build in §4)
- UBounds (`d = 3, L = 3, g = 1/2`), lines 641-740: `ukerNonneg`, `ukerRowSum`, `sumNdecay`,
  `sumNdecayEta` at `ξ = 1` / `E = 0`, `v = 1/2 < w = 3/4`; `uopBack` at `u = 1/4, t = 3/4`;
  `uopOneStep` at `u = 1/4`, `Δ ∈ {1/4, 1/2}`; nonconstant `instA` (`1` at `(0,0)`, `1/2` else, `α = 1`);
  boundaries `v = w = 0`, `w = 999/1000`, `u = t = 0`, `Δ = 0`, `Δ = 999/1000`. All hypotheses by
  `norm_num`/`le_rfl`. `normSqSpectralMOne` at `E = 0`. `thetaGenMat`/`thetaGen` are defs, used inside
  the `uopOneStep` examples.
- UTransport, lines 349-406: `uopLocalMax`, `uopPairLocalMax` at `d = L = 3`, `W = 2`, `(u,v) = (1/2,3/4)`,
  `R = 1` (far set per slot = 26 sites, near set `{a}`), `β = 1/2 ≠ α = 1`, `UkerFar` proved
  (`uT_inst_far`); boundary `u = v = 0`.
- KellStar, `kellStarEv_instance` (line 409): `kellStarEv 3 sz0 (1/6) 1 (1/2) (1/200) 1 (fun _ => 3/4)`
  with `sz0_tendsto`, `sz0_bandwidth`, `ks_rangeCond`, `ks_lam_ev` (all proved, every `n`), then applied
  at a witness `n` to the far pair `a = (L/2,L/2,L/2) ≠ b = 0` (far condition `ks_far` proved) at
  `(s,u) = (1/4,1/2)` and the boundary `(0,0)`.
No `N = 0`, empty index, collapsed window or `False` premise. **PASS** (see observation O1).

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Path.UBounds RBM3D.Path.UTransport RBM3D.Path.KellStar RBM3D.Test.Axioms
warning: RBM3D/Path/UTransport.lean:15:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Path/UTransport.lean:21:100: This line exceeds the 100 character limit, please shorten it!
✔ [3693/3693] Built RBM3D.Path.KellStar (8.2s)
Build completed successfully (3693 jobs).
exit 0
```
```
$ lake env lean scratchpad/T2097/ax.lean    # #print axioms of the 13 targets
'RBM.Path.thetaGenMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.thetaGen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.normSqSpectralMOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.ukerNonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.ukerRowSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.sumNdecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.sumNdecayEta' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.uopBack' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.uopOneStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.uopLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.uopPairLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.kellStarEv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.kellStarEv_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -n -E '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' <3 files>; echo "grep exit $?"
grep exit 1
$ git diff --stat main...t/T2097
 RBM3D/Path/KellStar.lean   | 434 ++++++++++++++++++++++++++
 RBM3D/Path/UBounds.lean    | 746 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Path/UTransport.lean | 412 +++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   3 +-
 4 files changed, 1594 insertions(+), 1 deletion(-)
$ git diff main...t/T2097 -- RBM3D/Test/Axioms.lean    # one list entry appended (`RBM.Path.UkerFar`)
$ name-clash: git grep "^(private )?(noncomputable )?(def|theorem|lemma|abbrev|structure) <name>( |$)" main
  -> 0 hits for each of the 24 new public names (main = 2b7cab5)
$ git merge-base main t/T2097 → c5bbae7; files changed on main since: RBM3D/Path/Expansion.lean, RBM3D/Test/Axioms.lean
```
Only the sole writable files are touched; new files only, so no frozen signature changes. **PASS.**

## 5. Paper deltas
Lean/paper differences and their coverage (prove report (d)):
- `ℓ*_u = (log W)^{3/2} ℓ_u` (Lean) vs the paper's commented line `3_5:2313` `ℓ^*_u := (log W)^{3/2}`;
  added hypotheses `3 ≤ d`, `0 < Λ`, `0 < lam ≤ Λ` eventually; distance `zdistInf` → **T2097b**.
- far count `L^d` (vs RBM2D `L²`) in `UopLocalMax`/`UopPairLocalMax` → **T2097c**.
- `neiwuj` (`3_5:2351-2362`) not uniform at `d ≥ 3` (`tailtoTail` dropped) → **T2097a**.
UBounds: no difference beyond RBM2D's. Coverage complete. **PASS.**

## Observations (no verdict effect)
- O1. The compiled `UkerFar` instances use `D' = -1` / `D' = 0` (`W^{-D'} = 2` / `1` = the row sum), so
  the instantiated conclusion of `uopLocalMax` is weaker than the trivial bound; the data are
  nondegenerate and every hypothesis is discharged, as §4 step 2 requires. Prove report b.9 states it.
- O2. Prove report b.1 says `lake env lean` of the three files gives empty output; the module build
  prints two `longLine` warnings at `UTransport.lean:15,21` (module docstring, before the
  `set_option linter.style.longLine false` at line 32). Cosmetic.
- O3. Branch base `c5bbae7`; `RBM3D/Test/Axioms.lean` also changed on `main` since; the hub merges the
  registry line by union (DECISIONS §20) and runs the full build. The bridge `WO → 0 < lam ≤ 𝔡⁻¹` is
  a consumer-side one-liner.

## Verdict
| target | verdict |
|---|---|
| `thetaGenMat`, `thetaGen`, `normSqSpectralMOne` | PASS |
| `ukerNonneg`, `ukerRowSum`, `sumNdecay`, `sumNdecayEta`, `uopBack`, `uopOneStep` | PASS |
| `uopLocalMax`, `uopPairLocalMax` | PASS |
| `kellStarEv` | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
