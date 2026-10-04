Auditor model: claude-opus-5-5

# T2111 audit (round 1): ST2-29 `Induction/LoopC2N`, `Induction/GridDriftN`
Time: Sun Oct  4 06:34:13 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2111-audit1`, detached at `t/T2111` = `3fc1018`.
Targets: `HermTestFunLoopN`/`hermTestFunLoopN`; `kStepC`, `uStepC`, `stepErrN`, `GridDriftN`/`gridDriftN` (+ `gridDriftN_at`); `exists_norm_Kcal_le_win`.

## 1. Statement vs pin (RBM2D `c9a24cf`, renamed by script, token diff)
Pins move with the proofs (ticket): `HermTestFunLoopN` = 2D `GridGoodN.lean:365`; `kStepC`, `uStepC`, `stepErrN`, `GridDriftN` = 2D `HierVocab.lean:421–440`. Script `pd.py` (renames `Z2 (d.L n)→Zd d (sz.L n)`, `gloop→loopL`, `spectralZ→zt`, `KLoop.Kcal→KLK d … (sz.lam n) …`, `ksimLK/elklkN/egtN→sz.STksimLKM/STelklkM/STegtM n`, `blockMat M→blockMat d L W M`, `d→sz`):
```
$ python3 pd.py
== def HermTestFunLoopN
  delete 2D: [ NeZero k ] | 3D: -
== def GridDriftN
  delete 2D: [ NeZero k ] | 3D: -
  insert 2D: - | 3D: d
== def stepErrN
  insert 2D: - | 3D: d          (x3: stepErrN d, envConst d, kStepC d)
  insert 2D: - | 3D: (
  insert 2D: - | 3D: ^ d )
  delete 2D: ^ 2 | 3D: -        ((W⁻¹)^2)^(k-1)  ->  ((W^d)⁻¹)^(k-1)
== def kStepC
  insert 2D: - | 3D: d
  replace 2D: 2 | 3D: d         (x8: W^2, L^2 -> W^d, L^d; c = W^d k^2 L^d = N k^2)
== def uStepC
  (no difference)
```
- `HermTestFunLoopN`: identical up to renaming; `[NeZero k]` dropped (strictly stronger). Constant `k(k+1)·N·η_u^{-(k+2)}`, `N = Sizes.size sz n = (W L)^d`; hypotheses `|E|<2`, `0≤u`, `u<1` (§29 boundaries kept). PASS.
- `GridDriftN`: identical up to renaming and `d`; `∀ n` hypotheses as pinned (§29 (4)); envelope on `[0, u_{j+1}]`, `2 ≤ |J| ≤ k`; `[NeZero k]` dropped. `gridDriftN_at` is the single-index form (dispatcher note F2). PASS.
- `stepErrN`/`kStepC`: exactly the `d`-dimensional replacement asked in the ticket (`W^{-2}→W^{-d}`, `W²k²L²→W^d k² L^d`). PASS.
- `exists_norm_Kcal_le_win`: changed form vs 2D (2D `GridDriftN.lean:792`):
```
2D: ∀ κ>0, m, τ>0, ∀ᶠ N, ∀ L W, 3≤L → 1≤W → W^2*L^2 = N → ∀ E, |E| ≤ 2-κ → ∀ u v, 0≤u → u≤v → v<1 →
      ∀ J WF, 2≤|J|≤m → ‖Kcal L W E u J‖ ≤ N^τ η_v^{-m}          (proved from Kbound_prec_uncond)
3D: (sz) SizeTendsto → ∀ E, STKbound sz E → (∀n,|E n|<2) → ∀ v, (∀n,0≤v n) → (∀n,v n<1) → ∀ m τ, 0<τ →
      ∀ᶠ n, ∀ w ∈ [0, v n], ∀ J WF, 2≤|J|≤m → ‖KLK d (L n) (lam n) (W n) (E n) w J‖ ≤ N_n^τ η_{v n}^{-m}
```
  This is the sequence-level form conditional on the owed, registered pin `STKbound` that the dispatcher accepted in the ticket note (V1, 06:20 UTC, flag F1). It is the accepted target, not a silent special case. Paper-delta candidate T2111a covers it. PASS (form accepted by the dispatcher).

## 2. Vacuity, hidden hypotheses, cycles
```
$ lake env lean audit.lean   (excerpt)
def RBM.Gauss.Sizes.STKbound : {d : ℕ} → Sizes d → (ℕ → ℝ) → Prop :=
fun {d} sz E => ∀ (τ : ℕ → ℝ), (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → ∀ (k : ℕ), 1 ≤ k →
  sz.Prec (fun n p x => ‖sz.STKloop n (E n) (τ n) p.1 p.2‖) fun n x x_1 => sz.Bctl n (τ n) ^ (k - 1)
def RBM.Gauss.Sizes.SizeTendsto : {d : ℕ} → Sizes d → Prop := fun {d} sz => Tendsto (fun n => ↑(sz.size n)) atTop atTop
def RBM.Gauss.Sizes.Bctl : … := fun {d} sz n t => (↑(sz.W n) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) t 0
$ grep -n STKbound RBM3D/Test/Axioms.lean
91:   `RBM.Gauss.Sizes.STKbound,  -- `ML:Kbound` (`1_2:1056`), hypothesis of `STStep1`: proved by KL7 (T2028, DECISIONS §19)
```
- There are no new structures. The only hypothesis-type input is `STKbound` (an owed pin of another gate, already registered, so no new registry line is needed). `HermTestFunLoopN` and `GridDriftN` are proved here and no theorem takes them as hypotheses, so `Test/Axioms.lean` correctly has no new registry line (DECISIONS §20).
- `STKbound` limit check: prove report (a) `check2.py`: ratio `max|𝒦^{(k)}|/Bctl^{k-1}` = 0.9645 (k=2) and 0.9267 (k=3) at W=16, and stays bounded as g→0. This is consistent with the `≺` pin (the `N^τ` slack).
- Imports: only merged modules (`Path/StepDecomp`, `Path/StepDecompLoop`, `Gauss/FlowCalculus`, `Loop/GLoopFlow`, `Defs/Sizes`; `Induction/{LoopGenN,HierAlgebra,GridDuhamelN,Split}`, `Path/{LoopStep,UBounds,Stop}`). The cut files `GridGoodN`, `Path/GoodEvent`, `Path/ScalesBridge` and `Loop/KBound` are not imported. There is no cycle.

## 3. Compiled nonempty instances (same files, `sz0`: d=3, L₀=4, W₀=32, N₀=2097152)
| endpoint | instance | data | open hypotheses |
|---|---|---|---|
| `hermTestFunLoopN` | `LoopC2NCheck.hermTestFunLoopN_k3_instance`, `_k3_same_instance`, `_k1_instance` | n=0, E=0, u=1/2, k=3 σ=(+,−,+) b=(0,1,2) and (0,0,0); k=1; M=0, y=1 | none |
| `gridDriftN` | `GridDriftNCheck.gridDriftN_instance` | n=0, E≡0, s≡1/10, t≡1/2, K≡4 (Δ=1/10, u₀=1/10, u₁=1/5), j=0, k=3, σ=(+,−,+); `Bk` from `GridDriftN_exists_envelope` | none |
| `exists_norm_Kcal_le_win` | `GridDriftNCheck.exists_norm_Kcal_le_win_instance` | E≡0, v≡1/2, m=3, τ=1, `sz0_tendsto` | `STKbound sz0 E0` (owed pin; allowed) |

None of these is degenerate: no `N = 0`, no empty index, no collapsed window, no `False` premise. In the `gridDriftN` instance the envelope `Bk` is obtained (∃), not chosen large. The theorem holds for every valid `Bk`.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Induction.LoopC2N RBM3D.Induction.GridDriftN     (audit worktree)
ℹ [3767/3768] Built RBM3D.Induction.LoopC2N (7.9s)
ℹ [3768/3768] Built RBM3D.Induction.GridDriftN (12s)
Build completed successfully (3768 jobs).
exit 0
(no error/warning line mentioning the two files; 33 "depends on axioms: [propext, Classical.choice, Quot.sound]" lines, no other axiom line)
$ lake env lean audit.lean   (#print axioms)
'RBM.Ind.hermTestFunLoopN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridDriftN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridDriftN_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.exists_norm_Kcal_le_win' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.GridDriftN_exists_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.GridDriftNCheck.gridDriftN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.LoopC2NCheck.hermTestFunLoopN_k3_same_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\b(sorry|admit|native_decide)\b|^axiom " RBM3D/Induction/LoopC2N.lean RBM3D/Induction/GridDriftN.lean | wc -l
       0
$ git diff --name-only main...t/T2111
RBM3D/Induction/GridDriftN.lean
RBM3D/Induction/LoopC2N.lean
```
The diff touches only sole writable files, both new, so no frozen signature is touched.

Public declarations, 2D `c9a24cf` vs 3D (script):
```
2D LoopC2N:   hermTestFunLoopN instance_data hermTestFunLoopN_k3_instance hermTestFunLoopN_k3_same_instance hermTestFunLoopN_k1_instance hΦ_of_hermTestFunLoopN_instance
3D LoopC2N:   HermTestFunLoopN hermTestFunLoopN instance_data hermTestFunLoopN_k3_instance hermTestFunLoopN_k3_same_instance hermTestFunLoopN_k1_instance
2D GridDriftN: gridDriftN exists_norm_Kcal_le_win sizes E0 s0 t0 K0 gridDriftN_check
3D GridDriftN: kStepC uStepC stepErrN GridDriftN gridDriftN_at gridDriftN GridDriftN_exists_envelope exists_norm_Kcal_le_win E0 s0 t0 K0 data gridDriftN_instance envelope_instance exists_norm_Kcal_le_win_instance
```
The prove report (b) lists and explains the dropped declarations: `hΦ_of_hermTestFunLoopN_instance` (its consumer is in the cut `GridGoodN`), and `sizes`/`gridDriftN_check` (replaced by the `sz0` instances).

## 5. Paper deltas
`docs/paper-deltas.md` has no T2111 entry yet (`grep -n T2111` gives no output). The prove report (d) proposes:
- T2111a: `exists_norm_Kcal_le_win` in sequence form, conditional on `STKbound` and `SizeTendsto`;
- T2111b: `[NeZero k]` dropped;
- T2111c: the new `GridDriftN_exists_envelope`;
- T2111d: `d`-dimensional `stepErrN`/`kStepC`.

These cover every difference found in §1. Covered.

## Observations (no verdict effect)
- O1. The Lean docstrings of `HermTestFunLoopN` (LoopC2N.lean:451) and `GridDriftN` (GridDriftN.lean:661) cite the `[NeZero k]` drop as "T2111a", but report (d) numbers it T2111b (T2111a is `exists_norm_Kcal_le_win`). The dispatcher should use the report's numbering.
- O2. Consumer ST2-31 must use the conditional sequence form of `exists_norm_Kcal_le_win` (needs `STKbound sz E` and `SizeTendsto`), not 2D's uniform-in-`(L,W,E)` form.
- O3. The `hermTestFunLoopN` proof bounds `‖E_b‖ ≤ 1` and drops the `W^{-dk}` gain. This is the same as the 2D pin and does not change the pinned statement.

## Verdicts
| target | verdict |
|---|---|
| `HermTestFunLoopN` / `hermTestFunLoopN` | PASS |
| `kStepC`, `uStepC`, `stepErrN`, `GridDriftN` / `gridDriftN` (`gridDriftN_at`) | PASS |
| `exists_norm_Kcal_le_win` | PASS (form F1 accepted by the dispatcher note in the ticket) |

**Ticket T2111: PASS.** No dispatcher sign-off needed: the one form change was already decided in the ticket note.
