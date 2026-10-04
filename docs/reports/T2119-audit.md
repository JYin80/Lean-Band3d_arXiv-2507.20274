Auditor model: claude-opus-5-5

# T2119 audit (round 1): LW-06 `Graph/LWEdgeExp` (`(Oe1x)`, lemma `Oe14`, `7_8:309-330`)
Time: Sun Oct  4 07:55:07 UTC 2026 (`date -u`). Branch `t/T2119` = 3b7fd46, merge-base f4cc46d, main now 5c69cb4.
Worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2119-audit1` (detached at 3b7fd46).

## Verdict
- Target 1 `lwEdgeExp_holds : LWedgeExp d`: **PASS**
- Target 2 `(Oe1x)` as a graph operation (`oe1x_graph_E`, `oe1x_graph_Ed`, `oe1x_graph_E_loop`, counters/`ord`): **PASS**
- Overall: **PASS**. No dispatcher sign-off needed.

## 1. Files touched
```
$ git diff main...t/T2119 --name-only
RBM3D/Graph/LWEdgeExp.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2119 -- RBM3D/Test/Axioms.lean   (the only changed line)
-   `RBM.Graph.LWedgeExp, -- `(Oe1x)` (`7_8:309-330`): LW-06
```
Both are the sole writable files; no merged file (pin `Graph/LWPins.lean`, `LWStein`, `LWVocab`, `LWWeightExp`) is changed.

## 2. Statements
Target 1 against the pin (by elaboration, `lake env lean ax.lean` in the audit worktree):
```
lwEdgeExp_holds : ∀ (d : ℕ), LWedgeExp d
example : ∀ d, LWedgeExp d := lwEdgeExp_holds      -- compiles
```
The pin `LWedgeExp` (`LWPins.lean:131`) is unmodified, so the statement is the pin verbatim: every `L ≥ 3`, `W ≥ 1`
(`NeZero`), every `g`, `|E| < 2`, `0 ≤ t < 1`, every `k₁…k₄ : ℕ` (empty products allowed), every `x, y, y', w, w', P`.
The proof splits `t = 0` (`oe1x_lwG_zero`, `lwWx_lwS_zero`) and `0 < t` (`oe1x_pin_pos`). No extra hypothesis.

Target 2 (from the file, `sed -n 1298,1310p`):
```
theorem oe1x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹) (Sp M : Matrix …) (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p …) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hx : p.1 = ⟨true, false, Sum.inr x, v⟩) (hv : v ≠ Sum.inr x) (ℓe : E → Idx …) :
    ∫ Γ.val = ∫ (oe1xT1 m Γ p x v hv).val + ∫ (owxT1 m Γ x).val
      + ((lwSplit p.2).map fun q => ((oe1xDs m Γ x v q).map fun T => ∫ T.val).sum).sum
```
plus `oe1x_graph_Ed` (unmerged dotted term 1, any `v`) and `oe1x_graph_E_loop` (`v = inr x`). `oe1xDs q` is
`[oe1xP5, oe1xP3]` for a red out-edge of `x` (terms 5, 3), `[oe1xP6, oe1xP4]` for a blue in-edge (terms 6, 4),
`[oe1xD]` otherwise (terms 7, 8, 9, one graph per edge). Counters (statements read in the file):
```
oe1xT1_counters : nS+1 = Γ.nS ∧ nW = Γ.nW ∧ nV+1 = Γ.nV ∧ nM ≤ Γ.nM        oe1xT1_ord : ord = ord Γ + 1
owxT1_counters / owxT1_ord (merged T2107)                                   (ord + 1)
oe1xDs_counters : ∀ T ∈ oe1xDs …, nW = Γ.nW+1 ∧ nV = Γ.nV+1 ∧ nM = Γ.nM ∧ (nS = Γ.nS+1 ∨ (nS = Γ.nS ∧ [red out ∨ blue in]))
oe1xDs_ord      : ∀ T ∈ oe1xDs …, ord = ord Γ + 1 ∨ (ord = ord Γ ∧ [red out ∨ blue in])
oe1xT1loop_counters : (nS, nW, nV, nM) = (Γ.nS-1, Γ.nW, Γ.nV, Γ.nM)
```
Hypotheses of target 2 are all in the signature: `GaussIBP` (merged and proved, `gaussIBP sz`), `Im z > 0`, `u > 0`,
`m ≠ 0`, the self-consistent equation `z + u m = -m⁻¹`, `M_{aa} = m`; `Sp` arbitrary (no `S⁺`, as the ticket asks).
No structure carries a hidden field; nothing is cycled (the file imports only merged `Graph/*`, `Gauss/FineModel`,
`Green/IBPPoly`; target 1 does not use any owed pin). No definition outside `LWVocab` was needed (ticket item 2 stop
condition not triggered).

## 3. Compiled nonempty instances (all compile: build in §4)
Target 1 (`LWEdgeExp.lean:1376-1393`):
```
example := lwEdgeExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  0 1 1 0 (0 : Idx 3 3 1) ![Pi.single 0 1] ![Pi.single 0 1] ![0] ![] 1
```
= the ticket's instance: `d = 3, L = 3, W = 1, g = 1/2, E = 0, t = 1/2, (k₁..k₄) = (0,1,1,0), P = 1`
(`lwWx_inst_hE : |(0:ℝ)| < 2`). Further examples: `(1,1,1,1)` with `y₁ = x`, `P = X(false,0,0)`; `t = 0`; `W = 2, g = 1`.
Target 2 (`:1418`): `oe1x_graph_E` at `lwWxInstSz`, `n = 0` (N = 27), `z = zt 0 (1/2)`, `M = lwWxInstM`, on the
graph `oe1xInstGraph` (`E = Fin 4`, `I = Fin 2`, 6 solid edges: `e₀ = G_{xa}`, a blue out-, red out-, blue in-,
red in-edge of `x`, one edge of `f`; one waved edge), `y₁ = inl 0 ≠ inr 0`; every hypothesis discharged by merged
lemmas (`gaussIBP`, `lwWx_inst_im`, `lwWx_mE_ne`, `lwWx_flow`, `lwWx_inst_hM`, `oe1xInst_mem`, `rfl`, `oe1xInst_hv`).
Also `oe1x_graph_Ed` (`:1425`), `oe1x_graph_E_loop` (`:1525`). Counter theorems applied at the instance with
every membership discharged (`:1484-1493`, T2107 audit O1), for the red out-edge, blue in-edge and `f`-edge cases;
computed counters by `decide` (`:1464`, `:1497`, `:1535`). None is degenerate (no empty index, `N = 27`, `t = 1/2`).

## 4. Build, axioms, forbidden tokens
```
$ lake build RBM3D.Graph.LWEdgeExp            (audit worktree)
✔ [3362/3362] Built RBM3D.Graph.LWEdgeExp (8.4s)
Build completed successfully (3362 jobs).      exit 0
$ grep -c LWEdgeExp build.log  → 1   (the ✔ line only: no warning/error in the new file)
$ lake env lean ax.lean
'RBM.Graph.lwEdgeExp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1x_graph_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1x_graph_Ed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1x_graph_E_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1xT1_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1xT1_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1xDs_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1xDs_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1xT1loop_counters' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.oe1x_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Graph/LWEdgeExp.lean ; echo $?
1
$ lake build RBM3D                             (branch as is)
Build completed successfully (3866 jobs).
$ lake env lean reg.lean   # import RBM3D; import RBM3D.Graph.LWEdgeExp; #assert_rbm_axioms
registry: 5 borrowed + 102 owed + 39 structural; …   exit 0 (no error)
```
Names: 61 `theorem`/`def` in the file; all but the pinned `lwEdgeExp_holds` start with `oe1x` (rule (E), ticket).
`git grep -w <name> main -- 'RBM3D/*.lean'` for all 61: no hit (current main 5c69cb4, which includes LW-07).

## 5. Paper deltas
The pin is the paper's `(Oe1x)` with `k₁ ↦ k₁ + 1` (D103, already recorded). Lean/design differences proposed in the
prove report (d): `T2119a` (term 1 `Δn_M ≤ 0`, not `= 0` as in T2040's table; `-1` when `x` merges into another
molecule), `T2119b` (terms 7, 8 one graph per edge instead of coefficient `k₁ m`, `k₄ m`), `T2119c` (split of the
loops at `x`, classification by `(σ, src, dst)`), `T2119d` (`y₁ = x`: `oe1xT1loop`, `Δord = -1`), `T2119e` (scope:
`e₀` blue uncircled). Every difference I found is covered.

## 6. Observations (no RETURN)
- O1 (merge, for the hub): main moved after the base; main's 5c69cb4 already deleted the adjacent registry line
  `RBM.Graph.LWggExp` (LW-07). The branch's `RBM3D/Test/Axioms.lean` still contains that line, so copying the
  branch file wholesale would re-add `LWggExp` to `owedProps`. Apply only the one-line deletion of
  `RBM.Graph.LWedgeExp` to main's file.
- O2: target 2 is proved on the sequence space for flow time `u > 0` (as T2107's `owxT*`); `t = 0` is covered only at
  the pin level (target 1). The ticket does not ask for `t = 0` at the graph level.
- O3: `oe1xT1_counters` needs `y₁ ≠ x` (`hv`); the `y₁ = x` case is the separate `oe1x_graph_E_loop` with `ord - 1`
  (T2119d). LW-08 (`lvl1`) must treat it (a weight `G_{xx}`, which the paper's `(Oe1x)` does not expand).
