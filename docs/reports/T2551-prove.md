Prover model: claude-sonnet-5-5


## (b) Script output — Sat Oct 17 09:20:35 UTC 2026

$ git diff --stat main...t/T2551
 RBM3D/Main/FinalShape.lean | 10 ++++++----
 1 file changed, 6 insertions(+), 4 deletions(-)

$ git diff main...t/T2551 (code lines)
--- a/RBM3D/Main/FinalShape.lean
+++ b/RBM3D/Main/FinalShape.lean
-`λ = g₀`), `(𝔠, 𝔡) = (1/6, 1/10)`, and at `d = 4` four of the five conjuncts (decol, locSC, QUE,
+`λ = g₀`), `(𝔠, 𝔡) = (1/6, 1/10)`, and at `d = 4` all five conjuncts (decol, locSC, QUE, BUniv,
-(decol, locSC, QUE, QDiff) are applied over it. -/
+(decol, locSC, QUE, BUniv, QDiff) are applied over it, `BUniv` at `k = 1`, `E' = 0`, `𝒪 = UNInst.bump`. -/
-**nonempty bulk** `BAbulk 4 4 g₀ κ E` (every `n`) and nonempty end domains, and four of the five conjuncts of
-`(final_shape h32).2 4` (decol, locSC, QUE, QDiff) applied at it; `UNL32` is the only hypothesis. -/
+**nonempty bulk** `BAbulk 4 4 g₀ κ E` (every `n`) and nonempty end domains, and all five conjuncts of
+`(final_shape h32).2 4` (decol, locSC, QUE, BUniv, QDiff) applied at it; `UNL32` is the only hypothesis. -/
+  have _ := h.2.2.2.1 (by norm_num) (1 / 8) (1 / 10) (FinalShape_cls4 g0) hadm 1 le_rfl κ hκ E (Eventually.of_forall fun _ => hb) 0
+    (by norm_num) UNInst.bump UNInst.bump_testFun

$ lake build (tail)
info: RBM3D.lean:655:0: axiom audit: 24150 declarations in `RBM`, all within [propext, Classical.choice, Quot.sound]
Build completed successfully (4425 jobs).

$ lake env lean scratch/ax.lean  (import RBM3D; #print axioms RBM.Endpoints.final_shape)
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]

$ lake env lean docs/tickets/checks/T2551-check.lean ; exit 0 (only the three #check outputs, no errors)

$ grep -n "sorry\|admit\|native_decide" RBM3D/Main/FinalShape.lean
(no match)

Compiled instance: the d = 4 example (section D4Instance) in RBM3D/Main/FinalShape.lean now applies h.2.2.2.1 (BUniv) at k = 1, E' = 0, O = UNInst.bump, over the same nonempty bulk hb; unchanged statements: Thm27, Thm27_of_L32, final_shape (check file compiles).

## (c) Verified Mathlib names
None new.

## (d) Open issues / paper-delta candidates
None.

## Repair — Sat Oct 17 09:22:53 UTC 2026 (repairer: claude-opus-5-5; audit round 1 RETURN item 1–2)

$ git log --oneline -1   (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2551)
3b9ebf4a T2551: repair: section docstring of D4Instance says all five conjuncts

$ git diff --stat main...t/T2551
 RBM3D/Main/FinalShape.lean | 12 +++++++-----
 1 file changed, 7 insertions(+), 5 deletions(-)

$ lake build RBM3D.Main.FinalShape 2>&1 | grep -E "FinalShape|error|Build completed" | tail -5
⚠ [4420/4420] Built RBM3D.Main.FinalShape (6.5s)
warning: RBM3D/Main/FinalShape.lean:10:0: The module doc-string for a file should be the first command after the imports.
Build completed successfully (4420 jobs).

$ lake env lean T2551/ax.lean   (scratchpad; import RBM3D.Main.FinalShape)
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]

$ grep -n -i "four\|five" RBM3D/Main/FinalShape.lean
20:* `Thm27 := ∀ d, 3 ≤ d → BAThm27L d`: Theorem 2.7 at every `d ≥ 3`, the five bullets in the order of
25:The instances at the end apply the conjuncts at concrete data.  At `d = 3` all five block Anderson
27:`λ = g₀`), `(𝔠, 𝔡) = (1/6, 1/10)`, and at `d = 4` all five conjuncts (decol, locSC, QUE, BUniv,
37:/-- **Theorem 2.7 (`MR:decol_BA`) at every `d ≥ 3`**: `BAThm27L d` for each `d ≥ 3`, the five bullets in
52:The band conjuncts are applied at `Inst.inst_*` (the instances section of `Main/BandTerminal.lean`) on `sz0`.  The five
86:/-- The five block Anderson conjuncts of `(final_shape h32).2 3 le_rfl` applied at `S0`, `κ_* = clsκ 4`, `E_*` in the bulk; the QUE
128:into `BAbulk 4 4 g₀ κ E` with `κ = Im m₀ / π > 0`, for every `n`.  All five conjuncts of `Thm27 4`
215:**nonempty bulk** `BAbulk 4 4 g₀ κ E` (every `n`) and nonempty end domains, and all five conjuncts of
