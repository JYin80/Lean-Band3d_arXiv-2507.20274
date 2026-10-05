Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 05:53:29 UTC 2026

Target (mathematics only): for `N = (W L)^d`, the GUE law `gueP d L W` on `Ω d L W` (independent real Gaussians, one per coordinate `(i,j,b)`, `Xmat` reading only the slots `idxKey i < idxKey j` (b either) and `i = j` (b = true)) is invariant under `H ↦ U H U*` for every unitary `U` on `Idx d L W = Zd d (W L)`. Hypotheses: `[NeZero L] [NeZero W]`, `U ∈ unitaryGroup`.

### (i) Exponent table

| quantity | value (d general; instance d=3, L=3, W=1) | constraint | slack |
|---|---|---|---|
| `N = card (Idx d L W)` | `(W L)^d`; 27 (`Defs/Sizes.lean:107` `card_Idx`, proved by `simp [Idx, Zd, ZMod.card]`) | `N = (WL)^d`, was `(WL)^2` in RBM2D (`GUE_card_idx`, source `:70-73`, via `Fintype.card_prod`) | the only dimension-dependent step; `Zd d (WL) = Fin d → ZMod (WL)`, card by `ZMod.card` |
| `gueVar` diagonal `(i,i,b)` | `1/N = 1/27` (`Universality/Pins.lean:61`) | `E h_ii² = 1/N` | equal to RBM2D `Endpoints.lean:190` with `^2 → ^d` |
| `gueVar` off-diagonal `(i,j,b)`, `i ≠ j` | `1/(2N) = 1/54` per real coordinate | `E|h_ij|² = 2·1/(2N) = 1/N` | equal to RBM2D with `^2 → ^d` |
| slot count `|GUESlot|` | `N + N(N-1) = N²` = 729 | equals the real dimension of Hermitian `N×N` matrices | exact |
| key identity constant | `Σ_slots (extr K)²/wt = N·Re Tr(K²)` | RHS unitarily invariant (`Tr((UKU*)²)=Tr(K²)`) | exact |
| `d` | any `d : ℕ` (no `3 ≤ d` needed) | none: nothing in the route uses `d` except `card_Idx` | no constraint; ticket instance `d = 3` |
| `L, W` | `NeZero L`, `NeZero W` | `N > 0` so `wt > 0` (`GUEWt_pos`) | instance `L = 3, W = 1` |
| decay/threshold exponents | none | the statement is exact (no `N → ∞`, no `κ`, `𝔠`, `𝔡`) | n/a |

Dimension-specific tokens in the source (`grep -n "\^ 2\|Z2\|ZMod\|Fin 2"` of `RBM2D/Universality/GUEInvariance.lean` at `c9a24cf`): only `GUE_card_idx` (`:70-73`: `change Fintype.card (ZMod (W*L) × ZMod (W*L)) = (W*L)^2` ... `sq`) plus the check instances `Idx 3 3` (`:1010-1078`). All other `^ 2` hits are real squares (`x ^ 2`, `‖z‖ ^ 2`, `sqrt(wt) ^ 2`). No F1–F5 dependence found (the proof is coordinate-free in `Idx`: it uses only `Fintype`, `DecidableEq`, `idxKey`, `card`). The route (slots, `GUEReconSlot`/`GUEExtractSlot`, `stdGaussian_map`, `map_infinitePi_infinitePi_of_inj`) is dimension-free.

### (ii) Concrete instance (d = 3, L = 3, W = 1, N = 27) and script

`U = diag(e^{ik}) · P`, `P` the cyclic-shift permutation matrix on the 27 indices, `k = 0..26` (nonscalar, unitary). The script builds the real-slot to `vec(H)` map `A` (exactly as `Xentry`: `x(i,j,true) + i x(i,j,false)` above the key order, conjugate below, real on the diagonal), the slot covariance `D = diag(gueVar)`, the complex covariance `E[h_ab conj h_cd] = A D A*` and pseudo-covariance `E[h_ab h_cd] = A D A^T`, compares with the GUE values `δ_ac δ_bd / N` and `δ_ad δ_bc / N`, transports by `U ⊗ conj U`, and checks the key identity at a random Hermitian `K`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2175/chk.py`

```
N 27 slots 729 N^2 729 var diag 0.037037037037037035 var offdiag coord 0.018518518518518517
cov==GUE 0.0 pseudo==GUE 0.0
unitary err 2.220446049250313e-16 nonscalar True
cov(UHU*)-cov(H) 1.4304896245381992e-17 pseudo diff 1.5515838457795457e-17
sum x^2/wt 80059.76051640832 N Tr K^2 80059.76051640829 2.9103830456733704e-11
Tr invariance 0.0
```

Reading: `cov==GUE` and `pseudo==GUE` are `0.0` (the `gueVar` normalisation gives exactly the GUE moments with `N = 27`); after conjugation by the nonscalar unitary both covariance and pseudo-covariance change by `~1e-17` (rounding); `Σ x²/wt = N Tr K²` agrees to `3e-11` at value `8.0e4`; trace invariance holds. All hypotheses hold simultaneously (`L = 3`, `W = 1` give `NeZero`; `U` unitary to `2e-16`; `U` not scalar; 729 slots; no collapsed window or empty index). No external hypothesis occurs, so no limit computation is needed.

Instance for the Lean file: `gueP_map_unitary_conj` at `d = 3, L = 3, W = 1`, `U = 1` and a diagonal phase `Matrix.diagonal (fun k => exp (φ k · I))` (unitary by `Matrix.mem_unitaryGroup_iff'`; nonscalar for `φ = idxKey`), as in the RBM2D source check namespace `:1010-1078`.

### Verdict

- `gueP_map_unitary_conj` (and the port of the whole file): **PASS**. Hypotheses are satisfiable at the instance above; the only `d`-dependence is `card_Idx` (`(W L)^d`), already merged at `RBM3D/Defs/Sizes.lean:107`; no exponent to close; the second-moment check at the instance agrees, and the proof route is dimension-free.

## (b) Script output — Mon Oct  5 05:57:28 UTC 2026

Commit on t/T2175: `cbe8c80`; `git diff --stat main...t/T2175`:
```
 RBM3D/Universality/GUEInvariance.lean | 1084 +++++++++++++++++++++++++++++++++
 1 file changed, 1084 insertions(+)
```
`cd ../RBM3D-wt/T2175 && lake build RBM3D.Universality.GUEInvariance` (lines other than warnings/notes; the only warnings are 3 long-line lints in the module docstring, lines 16/22/35, and pre-existing ones in imports):
```
⚠ [3304/3345] Replayed RBM3D.Defs.Tail
⚠ [3345/3345] Replayed RBM3D.Universality.GUEInvariance
info: RBM3D/Universality/GUEInvariance.lean:1073:0: 'RBM.Univ.gueP_map_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1074:0: 'RBM.Univ.GUEInvarianceCheck.phaseU_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1075:0: 'RBM.Univ.GUEInvarianceCheck.phaseU_not_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1076:0: 'RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1077:0: 'RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1078:0: 'RBM.Univ.GUEInvarianceCheck.isProbabilityMeasure_map_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3345 jobs).
```
Sorry/axiom grep (`grep -n 'sorry\|admit\|native_decide\|^axiom' RBM3D/Universality/GUEInvariance.lean`): 0 hits.

Target statement (extracted by `sed -n 1001,1003p`):
```lean
theorem gueP_map_unitary_conj (U : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Idx d L W) ℂ) :
    (gueP d L W).map (fun ω => U * Xmat d L W ω * star U) = (gueP d L W).map (Xmat d L W) := by
```
Compiled nonempty instances (d = 3, L = 3, W = 1, N = 27):
```lean
theorem gueP_map_unitary_conj_one : (gueP 3 3 1).map (fun ω =>
    (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) * Xmat 3 3 1 ω * star (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)) =
    (gueP 3 3 1).map (Xmat 3 3 1) :=
  gueP_map_unitary_conj 3 3 1 1 (one_mem _)

theorem gueP_map_unitary_conj_phase : (gueP 3 3 1).map (fun ω =>
    phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)) * Xmat 3 3 1 ω *
      star (phaseU (fun k => ((idxKey 3 3 1 k : ℕ) : ℝ)))) = (gueP 3 3 1).map (Xmat 3 3 1) :=
  gueP_map_unitary_conj 3 3 1 _ (phaseU_mem _)

1018:theorem phaseU_mem (φ : Idx 3 3 1 → ℝ) : phaseU φ ∈ Matrix.unitaryGroup (Idx 3 3 1) ℂ := by
1032:theorem phaseU_not_scalar (c : ℂ) :
1069:theorem isProbabilityMeasure_map_Xmat : IsProbabilityMeasure ((gueP 3 3 1).map (Xmat 3 3 1)) := by
```
Discharged: `1 ∈ unitaryGroup` (`one_mem`); `phaseU φ ∈ unitaryGroup` (`phaseU_mem`) with `phaseU_not_scalar` for φ = idxKey. No other hypotheses (NeZero 3, NeZero 1 by instance).

`#print axioms` (build output):
```
info: RBM3D/Universality/GUEInvariance.lean:1073:0: 'RBM.Univ.gueP_map_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1074:0: 'RBM.Univ.GUEInvarianceCheck.phaseU_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1075:0: 'RBM.Univ.GUEInvarianceCheck.phaseU_not_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1076:0: 'RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_one' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1077:0: 'RBM.Univ.GUEInvarianceCheck.gueP_map_unitary_conj_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GUEInvariance.lean:1078:0: 'RBM.Univ.GUEInvarianceCheck.isProbabilityMeasure_map_Xmat' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3345 jobs).
```

Name-clash grep on main (`grep -rn '<name>' RBM3D RBM3D.lean` in /Users/junyin/Lean_proof/RBM3D) for gueP_map_unitary_conj, GUEInvarianceCheck, phaseU, gueP_map_unitary_conj_one, gueP_map_unitary_conj_phase, isProbabilityMeasure_map_Xmat, GUE_Xmat_apply: 0 hits each (checked before commit). Private declarations in file: 97.

Port citation: RBM2D `RBM2D/Universality/GUEInvariance.lean` at `c9a24cf` (1082 lines; endpoint `:999`); RBM1D origin `c06b103:RBM1D/Flow/GUEUnitaryInvariance.lean` (cited in source). RBM2D HEAD `9e0f275`; the source file changed after `c9a24cf`:
```
 RBM2D/Universality/GUEInvariance.lean | 112 ++++------------------------------
 1 file changed, 13 insertions(+), 99 deletions(-)
```
Statement comparison against the c9a24cf source: source rewritten by perl (`s/d L W/L W/g; s/d L/L/g`) on the RBM3D file, then `diff` against the source (`git show c9a24cf:RBM2D/Universality/GUEInvariance.lean`). Non-comment, non-instance differences, complete list:
```
1:< import RBM2D.Universality.Pins
2:> import RBM3D.Universality.Pins
3:> import Mathlib.Analysis.Real.Pi.Bounds
5:< open RBM.Gauss RBM.Gauss.Sizes RBM.Endpoints
6:> open RBM RBM.Gauss RBM.Gauss.Sizes
8:<     Fintype.card (Idx L W) = (W * L) ^ 2 := by
9:<   change Fintype.card (ZMod (W * L) × ZMod (W * L)) = (W * L) ^ 2
10:<   rw [Fintype.card_prod, ZMod.card, sq]
11:>     Fintype.card (Idx L W) = (W * L) ^ d := by
12:>   simp [Idx, Zd, ZMod.card]
14:> private theorem GUE_Xmat_apply (ω : Ω L W) (i j : Idx L W) :
16:<     simp [Xmat_apply, Xentry, h]
17:>     simp [GUE_Xmat_apply, Xentry, h]
18:<     simp [Xmat_apply, Xentry]
19:>     simp [GUE_Xmat_apply, Xentry]
20:<     simp [Xmat_apply, Xentry, h, asymm h]
21:>     simp [GUE_Xmat_apply, Xentry, h, asymm h]
22:<     rw [GUE_T_eq_Tpp]
23:<     congr 1
24:<     show GUE_Tpp L W U (GUEDvInv L W (GUEDv L W ((WithLp.linearEquiv 2 ℝ _) z))) = _
25:<     rw [GUEDvInv_GUEDv]
26:>     rw [GUE_T_eq_Tpp, GUEDvInv_GUEDv]
33:<   have ha := congrFun (congrFun h ((Fintype.equivFin (Idx 3 3)).symm ⟨0, by decide⟩))
35:<   have hb := congrFun (congrFun h ((Fintype.equivFin (Idx 3 3)).symm ⟨1, by decide⟩))
37:>   have ha := congrFun (congrFun h ((Fintype.equivFin (Idx 3 3 1)).symm ⟨0, by simp [Idx, Zd, ZMod.card]⟩))
38:>     ((Fintype.equivFin (Idx 3 3 1)).symm ⟨0, by simp [Idx, Zd, ZMod.card]⟩)
39:>   have hb := congrFun (congrFun h ((Fintype.equivFin (Idx 3 3 1)).symm ⟨1, by simp [Idx, Zd, ZMod.card]⟩))
40:>     ((Fintype.equivFin (Idx 3 3 1)).symm ⟨1, by simp [Idx, Zd, ZMod.card]⟩)
```
Reading: all other changed lines are in the check namespace (`Idx 3 3` -> `Idx 3 3 1`, `gueP 3 3` -> `gueP 3 3 1`) or docstrings. Every statement of the source (all private except `gueP_map_unitary_conj`) is unchanged modulo the renaming `L W` -> `d L W`; `GUE_card_idx` now states `(W*L)^d`.

Narrative:
- Mechanical port: `variable (L W)` -> `(d L W)`, every `L W` argument -> `d L W`, `Idx`/`Ω`/`Xmat`/`idxKey`/`gueVar`/`gueP` are the RBM3D ones.
- `GUE_card_idx` (the only d-dependent step): `simp [Idx, Zd, ZMod.card]` gives `(W*L)^d`.
- RBM3D has no `Xmat_apply`; a private rfl lemma `GUE_Xmat_apply` replaces it. In `GUE_muI_invariant` the `congr 1; show` step timed out at 200000 heartbeats, replaced by `rw [GUE_T_eq_Tpp, GUEDvInv_GUEDv]; rfl` (same statement).
- Added `import Mathlib.Analysis.Real.Pi.Bounds` (without it `Real.pi_gt_three` in `phaseU_not_scalar` was an unknown constant in this build).
- `open RBM.Endpoints` dropped (no such namespace used); `open RBM` added.

## (c) Verified Mathlib names
- `Real.pi_gt_three` : 3 < π (`Mathlib/Analysis/Real/Pi/Bounds.lean:151`; module must be imported).
- Names used unchanged from the RBM2D source (compile in this build): `ProbabilityTheory.stdGaussian_map`, `MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj`, `Matrix.mem_unitaryGroup_iff`, `Matrix.mem_unitaryGroup_iff'`, `Complex.exp_eq_one_iff`, `WithLp.linearEquiv`.
- Verified absent in RBM3D: `Xmat_apply`.

## (d) Open issues and paper-delta candidates
- No statement difference from the paper beyond the `d`-replacement; no paper-delta candidate.
- RBM2D source at HEAD differs from `c9a24cf` (diff-stat above); the port follows `c9a24cf` as ticketed.
- Dispatcher note: the docstring of `gueP_map_unitary_conj` and the module docstring cite RBM2D positions at `c9a24cf`.
