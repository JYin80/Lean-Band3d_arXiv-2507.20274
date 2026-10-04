Auditor model: claude-opus-5-5

# T2124 audit (round 1) — LW-09 `Graph/LWSizeClaim` — Sun Oct  4 10:22:08 UTC 2026
Branch `t/T2124` = `ddcbbcd`, base `main` = `471b643`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2124-audit1` (detached).
The ticket pins no Lean text (check file has `#check` of upstream names only), so statements are compared with the ticket's mathematics and `7_8_light_weight.tex:104-118, 185-266`.

## 1. Diff, build, hygiene, axioms
```
$ git diff --name-status main...t/T2124
A	RBM3D/Graph/LWSizeClaim.lean
$ lake build RBM3D.Graph.LWSizeClaim; echo exit=$?      # error/LWSizeClaim lines only
✔ [3346/3346] Built RBM3D.Graph.LWSizeClaim (5.6s)
Build completed successfully (3346 jobs).
exit=0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Graph/LWSizeClaim.lean | wc -l
       0
$ lake env lean axioms.lean | sed 's/ depends on axioms://'
'RBM.Graph.lwSpOf_decay' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSpOf_decay_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwKBound_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWPins_lwSp_decay' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSplus_decay' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwForest_sum_le' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.exists_forest' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.waved_sum_le' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwKernel_tail' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwTail_log32' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSpOf_tail_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSize' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSizeG' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSize_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwClaimSizeG_E' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scalingSize_mul' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwSpOf_eq' [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.Graph.LWSizeClaim\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean; echo exit=$?
axiom audit: 3915 theorems, 1361 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0      (grep -c "error\|LWKBound\|lwClaim\|unregistered" precheck.out: 0)
$ # name clash: 37 public theorem/def names of the new file vs `git grep` on main
37 names, CLASH lines: none
```
`RBM3D/Test/Axioms.lean` unchanged (allowed: registry lines only; the only new `Prop` def `LWKBound` is a conclusion of `lwKBound_E`/`lwKBound_of_decay`, and the registry scan reports no new premise). Only a new file: no frozen signature touched.

## 2. Target 1 — `(eq:estSpm-W)`: PASS
Lean (`:461`, `lwSpOf_decay_E`; aliases `LWPins_lwSp_decay :1341`, `lwSplus_decay :1353` rewrite by `LWPins_lwSp_eq`, `lwSplus_eq` (`rfl`) to it):
```
∃ C c, 0<C ∧ 0<c ∧ ∀ L W [NeZero L] [NeZero W], 3 ≤ L → ∀ g t E, 0<g → g≤Λ → 0≤t → t<1 → |E| ≤ 2-κ →
  (∀ x y, ‖lwSmat d L W g t x y‖ ≤ C*(W^d)⁻¹*exp(-(c*lwBdist x y))) ∧
  ∀ x y, ‖lwSpOf d L W g t (mE E) x y‖ ≤ C*(W^d)⁻¹*exp(-(c*lwBdist x y))
```
| item | ticket / paper | Lean | verdict |
|---|---|---|---|
| matrix | `S=t·svarF`, `S^±` (`eq:def-Spm`, `7_8:110`), merged `LWPins_lwSp`, `lwSplus` | `lwSmat`, `lwSpOf = S·Ring.inverse(1-m²S)`; equal to the merged defs (`LWPins_lwSp_eq`, `lwSplus_eq`) | match; `S^-` enters `WEdge.val` as `star (D.Sp y x)` (LWVocab:120), same entry bound since `lwBdist_comm` |
| distance | "block distance" (ticket); paper `|x-y|/W` | `lwBdist` = periodic `ℓ¹` distance of blocks | ticket form; paper form up to `e^{cd}`, not formalized (delta T2124d) |
| constants | `(d, κ, gmax)` | `∃ C c` before `∀ L W g t E`; depend on `(d, Λ, κ)` | match |
| ranges | `0≤t<1`, `L≥3`, `W≥1`, "every g", `|E|<2` | `0<g≤Λ`, `|E|≤2-κ` | paper bulk setting (`1_2:14,381,407`: `|E|≤2-κ`; `prop:ThfadC_short` constants `C_κ`, merged `Prop5Short` needs `0<g`); preflight script 3 shows `E`-uniformity on `|E|<2` fails; delta T2124c |
Dependency: merged `prop5Short_holds` (`Propagator/Prop5Short.lean:400`, `Prop5Short` at `Pins.lean:47`), no external hypothesis.

## 3. Target 2 — `scalemole`: PASS
Ticket: "state the exact form". Lean gives (2a) `lwForest_sum_le :637` (peeling over a ranked forest; generic `f ≥ 0`, `f ≤ a`, row/col sums `≤ K`), `LGraph.exists_forest :725`, and the molecule form
```
LGraph.waved_sum_le (Γ) (hN : Γ.Normal) (D) (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) ℓe :
  ∑ ℓi, ∏_{waved} ‖WEdge.val D (Sum.elim ℓe ℓi) e‖ ≤ |ι|^{nM} * K₁^{nV-nM} * a^{nW-(nV-nM)}
```
and (2b) the confinement tail `lwKernel_tail :1248` (`Σ_{d_B≥R}|K_xy| ≤ C expC(d-2,c/2) e^{-cR/2}`), `lwSpOf_tail_E :1316`, `lwTail_log32 :1285` (`R=(log W)^{3/2}` gives `≤ W^{-D}` for `W ≥ W₀(c,D)`, `∃ W₀` before `∀ W`). The `L¹` peeling bound replaces the `W(log W)^{3/2}` confinement in `claim:size` with no `W^{-D}` error and no polylog: stronger than the ticket's "type" bound; delta T2124a. `LWKBound` is a `def … : Prop` (conjunction of entry and row/column bounds), not a structure field; it is discharged for the model by `lwKBound_E :475`.

## 4. Target 3 — `claim:size`: PASS
Lean (`:1118`):
```
lwClaimSize (Γ) (hN : Γ.Normal) (D : LData (Idx d L W)) {m Ψ K₀ K₁}
  (hM : ∀ x y, D.M x y = if x = y then m else 0) (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
  (hS : LWKBound D.S (K₀*(W^d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀*(W^d)⁻¹) K₁) ℓe :
  ‖Γ.val D ℓe‖ ≤ Γ.sizeConst K₀ K₁ * Γ.scalingSize Ψ W d L
```
`lwClaimSize_E :1196`: `∃ K₀ K₁ > 0` (from `lwKBound_E`, depending on `d, Λ, κ`) before `∀ L W g t E Γ D Ψ ℓe`, with `D.S = lwSmat…`, `D.Sp = lwSpOf … (mE E)`, `M = mE E · I`, entry bounds as hypotheses. General form `lwClaimSizeG :1162`/`lwClaimSizeG_E :1213` via `val_eq_partition`, `partition_normal`, bound `sizeConstG m K₀ K₁ * scalingSizeG m Ψ W d L`.
| item | ticket / paper (`7_8:243-266`) | Lean | verdict |
|---|---|---|---|
| size | `(L^d)^{nM} Ψ^{nS} W^{-d(nW-nV)}` (`eq_defsize`) | merged `Counters.scalingSize` (LWVocab:1619), same formula | match |
| entry bound | hypothesis `|G_xy-mδ_xy| ≤ Ψ` (owed `STGbEXPii/ij`) | `hG`, `hGd`, `hM` (M = m I, the paper's `M`) | match |
| loss | `C_Γ N^τ size` | `C_Γ size`, no `N^τ`, any `Ψ` | stronger; `≺` recovered by `LGraph.scalingSize_mul`; delta T2124b |
| constants | depend on `Γ, d, κ, gmax`, not `L,W,t,E` | `sizeConst = ‖coeff‖ K₁^{nV-nM} K₀^{nW-(nV-nM)}`, `K₀,K₁` from `(d,Λ,κ)` | match |
| general graph | via `scalingSizeG` (`eq_defsizemax`) | `(Σ_P C_P)·max_P size(P)` | match up to `O(1)` constant (`≺` absorbs it) |
No hidden hypothesis: `LData` (LWVocab:73) has data fields only; `Normal` is a plain `Prop` def, decided by `decide` on `p2Graph`. No cycle: imports only merged `Graph/{LWVocab,LWStein,LWPins}`, `Propagator/Prop5Short`, `Defs/{RadialSum,Sizes}`.

## 5. Compiled nonempty instances (same file, compiled by the build above)
| endpoint | instance | data | discharged |
|---|---|---|---|
| T1 `LWPins_lwSp_decay`, `lwSplus_decay` | `example :1367` | `d=3,L=4,W=32,g=1/64` (= merged `sz0`, n=0), `E=0`, `t=1/2`, `Λ=1,κ=1/2` | all by `norm_num`/`sz0_values` |
| T1 `lwSpOf_decay_E` | `example :1403` | `d=3,L=4,W=2,g=t=1/2,E=0`; plus `lwSmat … 0 0 ≠ 0` | all |
| T3 `lwClaimSize_E` (→ `lwClaimSize`) | `example :1430` | `p2Graph` (`nS,nW,nV,nM = 6,2,4,2` proved), `lwSizeD0`: `G = mE0·I + J/100` dense, `Ψ=1/100`, `ℓe = (0, 1)` | `Normal` by `decide`, `hG/hGd` lemmas, `hS/hSp/hM` by `rfl` |
| T3 `lwClaimSizeG_E` (→ `lwClaimSizeG`) | `example :1444` | same; `0 < scalingSizeG` proved | all |
| T2 `waved_sum_le` (→ `lwForest_sum_le`, `exists_forest`) | `example :1459` | `p2Graph`, `lwSizeD0`, `K` from `lwKBound_E` | all |
| T2 `lwSpOf_tail_E` (→ `lwKernel_tail`), `lwTail_log32` | `example :1474` | `d=3,L=4,W=2`, `R=1`; `c=1, D=3` | all |
No `N=0`, empty index, collapsed window or `False` premise (`N = 8^3 = 512`).

## 6. Paper-delta coverage
`grep -c T2124 docs/paper-deltas.md` = 0 (not yet appended); the prove report (d) proposes `T2124a` (peeling replaces `scalemole` confinement), `T2124b` (deterministic, no `N^τ`, entry bounds as hypotheses, no `Ψ` window), `T2124c` (`0<g≤Λ`, `|E|≤2-κ`), `T2124d` (block `ℓ¹` distance vs `|x-y|/W`). Every Lean/paper difference found in §§2–4 is in this list.

## 7. Observations (no verdict effect)
- O1. `sizeConstG (mE E) K₀ K₁` is written as a function of `m`; its terms are `‖coeff·m^k m̄^j‖`-type (`splitWeights`, LWVocab:1246), so its value does not depend on `E` when `‖mE E‖ = 1`, but that is not stated as a lemma. A consumer needing an `E`-free constant for the general form must prove it.
- O2. The paper's `e^{-c|x-y|/W}` form (T2124d) is only argued in prose in the report; not formalized.
- O3. The prove report's narrative note says `RBM3D/Test/Axioms.lean` is unchanged; confirmed by the diff above.

## Verdict
T1 PASS, T2 PASS, T3 PASS. Overall: **PASS**. No dispatcher sign-off needed beyond appending deltas T2124a–d.
