Auditor model: claude-opus-5-5

# T2412 audit (stage 2, round 1): Sun Oct 11 09:12:29 UTC 2026

Inputs: ticket `docs/tickets/T2412.md`, its check file `docs/tickets/checks/T2412-check.lean`, `docs/reports/T2412-prove.md`, the 1a-audit `docs/reports/T2412-1a-audit.md` (PASS), and branch `t/T2412` at `d858b0b`.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2412-audit1` (detached at `d858b0b`). Scratch: `$S` = `<scratchpad>/T2412`; all `aud_*` files there are mine.

**Verdict: PASS for all targets T1–T5.** No dispatcher sign-off is needed. Observations O1–O4 are below; none of them changes a statement, an instance, the build, the axioms or the paper-delta coverage.

## 1. Diff scope, sizes, hygiene
```
$ git diff --name-only main...t/T2412
RBM3D.lean
RBM3D/Graph/BASizeClaim.lean
RBM3D/Graph/BASizeClaim2.lean
RBM3D/Probe/T2412Pins.lean            # 1a probe, sole-writable, never merged
$ git diff main...HEAD -- RBM3D.lean   # two import lines after the last import, #assert_rbm_axioms stays last
+import RBM3D.Graph.BASizeClaim
+import RBM3D.Graph.BASizeClaim2
$ wc -l RBM3D/Graph/BASizeClaim.lean RBM3D/Graph/BASizeClaim2.lean      # stop line 2,000 per file
    1167 RBM3D/Graph/BASizeClaim.lean
     825 RBM3D/Graph/BASizeClaim2.lean
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Graph/BASizeClaim.lean RBM3D/Graph/BASizeClaim2.lean; echo grep=$?
grep=1
$ for each import line: git cat-file -e main:<path>
LWSizeClaim, BAVocab, BAExpandW, BA.GreenSchur, BA.Prop5Short, BA.KBase: on main;  BASizeClaim2 imports BASizeClaim (same ticket)
```
No existing file is modified apart from the `RBM3D.lean` imports, so no frozen signature is touched. Nothing on the branch imports the new modules, so there is no cycle. The public names are the pinned names, the `BASizeClaim_`-stem names, and instance data in the `BASizeClaimInst`/`BASizeClaimInst2` namespaces. 54 helpers are `private`.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Graph.BASizeClaim RBM3D.Graph.BASizeClaim2 > $S/build.txt 2>&1; echo exit=$?
exit=0
$ grep -E "^error" $S/build.txt | wc -l; grep -c "warning: RBM3D/Graph/BASizeClaim" $S/build.txt; tail -1 $S/build.txt
0
0
Build completed successfully (3793 jobs).
$ lake build > $S/full.txt 2>&1; echo exit=$?; grep -E "^error|axiom audit|Build completed" $S/full.txt     # registry pre-check
exit=0
info: RBM3D.lean:455:0: axiom audit: 11551 theorems, 3512 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4223 jobs).
$ lake env lean $S/aud_axioms.lean    # import BASizeClaim2 + 19 `#print axioms` lines, grouped by result
[propext, Classical.choice, Quot.sound] <- baClaimSize_E baClaimSize baClaimSizeG_E baClaimSizeG BAGraph.counters_le
  BAGraph.edgeEnds BAGraph.exists_forest BAGraph.Jx BAGraph.sizeConst baKBound_E baMTail_E BASizeClaim_fibre_sum
  BASizeClaim_forest_sum_le BASizeClaimInst2.D0_hG BASizeClaimInst2.D0 baSp_eq baSpDecay baSpTail_E baTail_log
$ lake env lean docs/tickets/checks/T2412-check.lean > $S/check.txt 2>&1; echo exit=$?; grep -c error $S/check.txt
exit=0
0
```

## 3. Statements against the audited pins (script)
`$S/aud_pincheck.lean` imports `RBM3D.Graph.BASizeClaim2`. It copies sections 2–5 of the probe verbatim (`sed -n '/## 2\./,/## 6\./'`, 13 pin `Prop`s) into the namespace `RBM.Graph.AudPins` and then has 13 lines of the form `example : X_pin := @X`:
```
$ lake env lean $S/aud_pincheck.lean; echo exit=$?
exit=0
$ # the vocabulary in the pins: text of the definitions in the branch files vs the probe
^def BAGraph.sizeConst: diff lines 0, 3 lines
^abbrev BAGraph.Jx: diff lines 0, 2 lines
^def BAGraph.edgeEnds: diff lines 0, 4 lines
```
All 13 proved theorems have exactly the types of the 1a-audited pins.

Against the ticket's mathematics, and the paper `B_graphical_lemmas.tex:286-360` and `7_8:255-266` as I read them:
- **T1 `baSp_eq`, `baSpDecay`, `baKBound_E`** (ticket (ii), `(eq:estSpm-W)`). `S⁺ = S·W = t·lwLift(Θ^{(+,+)})`. The bound is `‖S_xy‖, ‖(SW)_xy‖ ≤ C W^{-d} e^{-c d_B}`. In the Lean statement `∃ C c` comes before `∀ L W g0 E t m`, so the constants depend only on `(d, Λ, κ)`. There is no smallness hypothesis on `g0` (`0 < g0 ≤ Λ`). The paper's `|x−y|/W` is replaced by the block distance `lwBdist` (D268).
- **T2 `BASizeClaim_forest_sum_le`, `BAGraph.exists_forest`, `BAGraph.counters_le`** (ticket (i)). The peeling uses per-edge constants `(a_j, K_j)`, and the forest runs over `J = waved ⊕ mdot ⊕ psi` with `|C| + n_M = |I|` and `#waved tree edges + n_M = n_A`. The counters satisfy `n_M ≤ n_A` and `n_A − n_M ≤ n_W`. The only hypothesis is "no `=`-dotted edge", which is the `Normal` (ii) of `defn_normalBA`. Reuse: `BASizeClaim.lean:955` derives the peeling from the public `lwForest_sum_le` (the R/reuse rule), and `lwForest_core` is not twinned.
- **T3 `baClaimSize`** (ticket (iii)). Hypotheses: `Γ.Normal`, `∀ x y, ‖G−M‖ ≤ Ψ`, and `LWKBound` for `S`, `S⁺` (`K₀W^{-d}`, `K₁`) and for `M`, `gΨ` (`Kd`, `Kd`). There is no `hM : M = m·I`. The conclusion is `‖Γ.val‖ ≤ sizeConst · scalingSize`, where `scalingSize = (L^d)^{n_M} Ψ^{n_S} W^{-d(n_W−n_A)}` (`Counters.scalingSize`, `LWVocab.lean:1619-1620`, with the slot `nV := n_A` from `BAGraph.counters`, `BAVocab.lean:141-153`). This is exactly `(eq_defsize_BA)`. **`baClaimSizeG`** covers general graphs through `BAGraph.partition` with `Σ_P C_P · max_P size` (`scalingSizeG = foldr max 0`), which is `(eq_defsizemax)`.
- **T4 `baClaimSize_E`, `baClaimSizeG_E`** take `D.S, D.Sp, D.M, D.gPsi` to be the BA model matrices, with `∃ K₀ K₁ Kd` ahead of all of `L W g0 E t m Γ D Ψ ℓe`, and `G` arbitrary with `‖G−M‖ ≤ Ψ`. **`baSpTail_E`, `baMTail_E`** give the row tails beyond block distance `R`, `≤ C₂e^{-c₂R}`; this is the block spread of `(scaleatom)`. **`baTail_log`** gives `e^{-c(log W)^p/2} ≤ W^{-D}` for `W ≥ W₀`, `p > 1`, which with `p = 1+ε₁` is the paper's `e^{-c(log W)^{1+ε₁}}` error.
- None of these is a special case of the target. The deterministic form is the agreed reading of `Γ ≺ size(Γ)` (D265/D266, as in the band twin `lwClaimSize`).

## 4. Hidden hypotheses, vacuity
```
$ grep -n "structure LData" -A5 RBM3D/Graph/LWVocab.lean; sed -n 39,40p RBM3D/Graph/BAVocab.lean
73:structure LData (ι : Type*) where
74-  G : Matrix ι ι ℂ
75-  M : Matrix ι ι ℂ
76-  S : Matrix ι ι ℂ
77-  Sp : Matrix ι ι ℂ
39:structure BALData (ι : Type*) extends RBM.Graph.LData ι where
40:  gPsi : Matrix ι ι ℂ
$ grep -n "def LWKBound" -A1 RBM3D/Graph/LWSizeClaim.lean
388:def LWKBound {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) (a K₁ : ℝ) : Prop :=
389-  (∀ x y, ‖K x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖K x y‖ ≤ K₁) ∧ (∀ y, ∑ x, ‖K x y‖ ≤ K₁)
$ grep -n "def BAReal" RBM3D/BA/MFixedPoint.lean
432:def BAReal (g κ E : ℝ) (m : ℂ) : Prop := BASelf d L g (E : ℂ) m ∧ κ ≤ m.im
```
No structure has a `Prop` field. The `LWKBound` hypotheses of T3 are discharged for the BA matrices by the proved `baKBound_E` (T1), and §5 applies them at the data. Every hypothesis is a merged definition or a merged theorem, so there is no external hypothesis (TEAM §8 lesson 14 does not apply).

## 5. Compiled nonempty instances (every endpoint theorem)
The data are `d = 3`, `L = 4`, `W = 2` (`N = 512`), `t = 1/2`, and `P : FlowPt 4 10` (merged `MFixedPoint.lean:877-893`: `0 < P.g0 ≤ 10`, `BAReal 3 4 P.g0 (Im P.m0) P.E P.m0`), with `Λ = 10` and `κ = Im P.m0 > 0` (`P.real.1.1`).
| theorem | instance (file:line) | deterministic hypotheses discharged |
|---|---|---|
| `baSp_eq`, `baSpDecay`, `baKBound_E` | `BASizeClaim.lean:1065` | `3 ≤ 4`, `0 ≤ 1/2 < 1`, `P.g0_pos`, `P.g0_le`, `P.real`; the example also proves `S 0 0 ≠ 0` |
| `BAGraph.exists_forest`, `counters_le` | `:1093` (`baLWT1`), `:1113` (`baGGT1`) | no `=`-dotted edge by `decide`; it concludes `|C| = 2` / `3` and one waved tree edge |
| `BASizeClaim_forest_sum_le` | `:1141` | `ι = Fin 3`, 2 internal vertices, per-edge `a = (1/3, 1)`, `K = (1, 3)`; all 7 hypotheses proved by `fin_cases`/`simp` |
| `baClaimSize`, `baClaimSizeG` | `BASizeClaim2.lean:766` (`baLWT1`) | `Normal` by `decide`; `D0_hG` (`G − M ≡ 1/100`); `hS hSp hM hP` from `baKBound_E` at `P`; `0 < size` |
| `baClaimSize_E`, `baClaimSizeG_E` | `:784` (`baGGT1`, external labels `0`, `2`: same offset, different blocks) | `D.S … D.gPsi` by `rfl`, `hG = D0_hG`, `0 < size` |
| `baSpTail_E`, `baMTail_E`, `baTail_log` | `:807` | `R = 1`, `c = 1`, `p = 3/2`, `D = 3` |

None of the data is degenerate: there is no `N = 0`, no empty index set, no `False` premise and no huge witness. All of these compile in the §2 build, which has 0 errors and 0 warnings in either file.

## 6. Paper-delta coverage
- Proposed in the report (d): `T2412a` (Combes–Thomas decay of `M` for all `g₀ ≤ Λ` instead of `(Mbound_AO)/(Mbound_AO2)`), `T2412b` (no `(log W)^{1+ε₁}` atom-spread loss; the spread is the separate tail), `T2412c` (`S⁺ = SW`, `W = (1−M⁺S)⁻¹`), `T2412d` (one entrywise `‖G−M‖ ≤ Ψ`, diagonal included), and `T2412e` (explicit, very large constants).
- Already in `docs/paper-deltas.md`:
```
$ grep -n "^## D26[568]" docs/paper-deltas.md | cut -c1-60
1071:## D265 · `claim:size` 里 `scalemole` 换成确定性的 `L¹` 剥树界（20
1075:## D266 · `claim:size` 是确定性的（2026-10-04，T2124b；LW-09，dd
1083:## D268 · 衰减用块 `ℓ¹` 距离（2026-10-04，T2124d；LW-09，dd1748c）
```
  Also already listed are atoms and `×`-dotted edges (T2287a–b), the missing paper proof of `claim:size` (T2040m), and `BAReal` with `(d, Λ, κ)` constants (D626 precedent). I found no Lean/paper difference that is not covered.

## 7. Observations (no RETURN)
- **O1 (instance data).** Ticket item 5 names "the flow datum of `sz0`" (`g = 1/64`, `κ = 1/2`; `BA/FlowPins.lean:1130-1147`). The instances use `MFixedPointInst.P : FlowPt 4 10` instead. The 1a probe also used this point, and the 1a-audit accepted it (its §4 (iv)). The instance is concrete and nondegenerate and discharges every hypothesis, so criterion 3 is met.
- **O2 (report length).** The ticket limits the report to 200 lines; `T2412-prove.md` has 284. The report says so itself at (b) line 264. It stays within CLAUDE.md §6's 300 lines.
- **O3 (constants vs table).** The proved constants are `K₀ = (1+Λ²)C₅ + 1` and `Kd = K_M + 2dΛ`. They differ from the table of (a) R8/R9, and the report states this at (b) line 262. The statements are existential in the constants, so the pins are unchanged.
- **O4 (real energy).** The `_E` forms hold at real `E` (`BAReal`, `BASelf … (E:ℂ) m`), as the merged `BAlwW`/`baProp5s_holds` inputs require. The deterministic `baClaimSize`/`baClaimSizeG` hold for arbitrary data.

## 8. Verdict per target
- T1 kernel edges (`baSp_eq`, `baSpDecay`, `baKBound_E`): **PASS**
- T2 peeling and atomic forest (`BASizeClaim_forest_sum_le`, `BAGraph.exists_forest`, `BAGraph.counters_le`): **PASS**
- T3 `baClaimSize`, `baClaimSizeG`: **PASS**
- T4 `baClaimSize_E`, `baClaimSizeG_E`, `baSpTail_E`, `baMTail_E`, `baTail_log`: **PASS**
- T5 instances: **PASS**. T6 registry pre-check (full `lake build`, `#assert_rbm_axioms`): **PASS**.
- **Ticket T2412: PASS.** At merge, bring in `RBM3D/Graph/BASizeClaim.lean`, `RBM3D/Graph/BASizeClaim2.lean` and the two `RBM3D.lean` import lines. The probe `RBM3D/Probe/T2412Pins.lean` is not merged.
