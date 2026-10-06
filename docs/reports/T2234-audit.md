Auditor model: claude-opus-5-5

# T2234 audit (LW-12a, `RBM3D/Graph/AnpKey.lean`), round 1, Tue Oct  6 01:24:14 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2234-audit1`, detached at `t/T2234` = `50e0550` (merge-base `3a58663`).

## 1. Diff scope, build, hygiene
```
$ git diff main...t/T2234 --stat
 RBM3D/Graph/AnpKey.lean | 945 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   1 +
$ git diff main...t/T2234 -- RBM3D/Test/Axioms.lean   (only added line)
+   `RBM.Graph.AnpDetGhStep, -- induction step of `lem:Anp_key_gh`, cases (I)-(IV) after the A2 replacement (`7_8:1110-1599`): LW-12b-f (T2234, DECISIONS §24)
$ git diff main...HEAD -- RBM3D/Graph/LWPins.lean RBM3D/Graph/LWVocab.lean RBM3D.lean | wc -l
0
$ lake build RBM3D.Graph.AnpKey 2>&1 | grep -E 'error|Build completed'
Build completed successfully (3346 jobs).
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom |decide \+native|ofReduceBool|implemented_by|extern' RBM3D/Graph/AnpKey.lean
59:path without a ghost edge is a walk through external vertices only, its longest edge has length   (docstring "external": false positive)
$ grep -cE 'decide \+kernel' RBM3D/Graph/AnpKey.lean
5        (kernel reduction, no axiom: see printed axioms)
$ grep -nE '^(theorem|lemma|def|abbrev|structure|class|instance|@\[reducible\] def)' AnpKey.lean | grep -vE ' (anpKey_|AnpDetGh|anpDetGh|lwAnp|NGraph\.ghostify)'
(no output)   -> every public name is pinned or carries the `anpKey_` prefix (NGraph.ghostify* named by the ticket)
```
Imports: `RBM3D.Graph.LWPins`, `Mathlib.Algebra.Order.BigOperators.Ring.Finset` (not `RBM3D`, not `AuxGraph*`), as the ticket requires.

Registry pre-check (after `lake build RBM3D.Test.Axioms`, 2 jobs; file `import RBM3D` / `import RBM3D.Graph.AnpKey` / `#assert_rbm_axioms`):
```
$ lake env lean regcheck.lean ; exit 0
axiom audit: 6934 theorems, 2340 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```
(Run against the stale `Test/Axioms` olean copied from main, the same file listed exactly `[RBM.Graph.AnpDetGhStep]` as unregistered, so the one registry line is what is needed. `AnpDetGh` was not listed, so leaving it unregistered is consistent with the ticket's "only if listed" rule.)

## 2. Statements against the pins (script)
Script `scratchpad/T2234/audit_pins.lean`: check-file section 2 copied verbatim by `awk` (namespace `RBM.Graph.T2234Check`), then:
```
example (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : AnpDetGhAtPin d Γ ↔ RBM.Graph.AnpDetGhAt d Γ := Iff.rfl
example (d : ℕ) : AnpDetGhPin d ↔ RBM.Graph.AnpDetGh d := Iff.rfl
example (d : ℕ) : AnpDetGhZeroPin d ↔ RBM.Graph.AnpDetGhZero d := Iff.rfl
example (d : ℕ) : AnpDetGhStepPin d ↔ RBM.Graph.AnpDetGhStep d := Iff.rfl
example : ∀ d, AnpDetGhZeroPin d := @RBM.Graph.anpDetGh_zero
example : AnpDetGhOfStepPin := @RBM.Graph.anpDetGh_of_step
example : LwAnpKeyGhOfDetPin := @RBM.Graph.lwAnpKeyGh_of_det
example : LwAnpKeyOfGhPin := @RBM.Graph.lwAnpKey_of_gh
example : LwAnpOfKeyPin := @RBM.Graph.lwAnp_of_key
-- check-file section 3 shapes
def oneEdge : NGraph 1 0 where            -- copied from the check file
  es := [⟨false, .inl (.inl 0), .inl (.inr 0)⟩]
  path := fun _ => [(0, .inl (.inr 0))]
example : oneEdge = RBM.Graph.anpKey_oneEdge := rfl
example : AnpDetGhStepPin 3 → LWAnp 3 := fun hs => RBM.Graph.lwAnp_of_key 3 (RBM.Graph.lwAnpKey_of_gh 3
  (RBM.Graph.lwAnpKeyGh_of_det 3 (RBM.Graph.anpDetGh_of_step 3 (RBM.Graph.anpDetGh_zero 3) hs)))
example : figAux.GhostOK → figAux.IsNested → (AnpDetGhPin 3 → AnpDetGhAtPin 3 figAux) :=
  fun _ _ h => RBM.Graph.anpKey_inst_figAux h
$ lake env lean audit_pins.lean ; echo $?
...: warning: The namespaces `RBM`, `Graph`, and `T2234Check` are duplicated in ... oneEdge   (script artefact, harmless)
exit 0
```
Targets 4 and 5 are discharged against the merged, unchanged pins `LWAnpKeyGh`, `LWAnpKey`, `LWAnp` (0-line diff of `LWPins.lean`), with no added hypothesis.

Mathematics of target 1 against `7_8:1041-1050` (`(adsuu22)`) and `:963-966` (`(eq:Gbyxi3)`): `(W^dη_t)^{-q}` becomes `θ^q`, `Ψ_t` becomes a positive `ψ` that is antitone on `[0,∞)`, `≺` becomes `≤` with `C`, and the ghost exponent `ψ(0)^{ord−n_ngh}` and the `1(𝔓_i has no ghost)` product are as in the paper. `C, c` are quantified before `L, ψ, θ, ξ, a, b`. The hypotheses `GhostOK`/`IsNested` correspond to the paper's properties (1)–(3) plus the ghost-ending condition (merged LW-03 vocabulary). `q ≤ p` is not assumed; it follows from IsNested (3) at `A = univ`. The extra `c ≤ 1` is harmless because `ψ` is antitone. The deterministic form is a strengthening that the lift turns into the merged `≺` pin. This difference is covered by candidate `T2234a`.

## 3. Hidden hypotheses, vacuity, cycles
- `NGraph` (`LWVocab.lean:311-313`) has the fields `es`, `path` only and no Prop field. `AnpDetGhAt*` are plain Props. Nothing is hidden in a structure.
- Dependencies: only merged modules (`LWPins` and its imports). `AnpDetGhStep` is a hypothesis of `anpDetGh_of_step` and is registered as owed (LW-12b–f). There is no cycle: no theorem of the file assumes its own conclusion, and `AnpDetGh` is derived from `AnpDetGhZero` (proved) plus `AnpDetGhStep`.
- Non-vacuity of `AnpDetGhStep`/`AnpDetGh`: the preflight numerics (`figAux`, `q = 2`, ratio ≤ 0.18 at `c = 1/4`; 44 random nested graphs with `q ≥ 1`, ratio ≤ 1) are evidence, not proof. Whether it holds is LW-12b–f's job. The lift's premise is deterministic, so no external-limit check applies (TEAM §8 lesson 14 concerns external hypotheses; `AnpDetGhStep` is an owed internal pin).
- Lift (`lwAnpKeyGh_of_det`, l.689): it uses `STFlow` to get `η_t > 0` (`etaT_pos` via `lemT_lt_one`, `abs_lemE_lt_two`) and `Sizes.tendsto_size`. The pin's `0 ≤ t` and `q ≤ p` are carried and not used. No new hypothesis.

## 4. Compiled nonempty instances (in `AnpKey.lean`)
| endpoint | instance | data | open hypotheses |
|---|---|---|---|
| `anpDetGh_zero` | `anpKey_inst_zero` l.865 | `d = L = 3`, `anpKey_oneEdge` (`p = 1`, one solid edge; `IsNested`, `GhostOK` by `decide +kernel`), `ψ r = (1+r)⁻¹`, `θ = 1`, `ξ ≡ 1/6`, `a ≡ 0`, `b ≡ 1` | none. Antitone, positivity, `ξ ≤ ψ(zdistInf)` (via `zdistInf ≤ 1` on `Z_3^3`) and `Σ_β ξ² = 27/36 ≤ 1` are all discharged |
| `anpDetGh_of_step`, `lwAnpKeyGh_of_det`, `lwAnpKey_of_gh`, `lwAnp_of_key` | `anpKey_inst_anp` l.894 | the chain used as the `h` of merged `inst_Anp` at `sz0`, `z0`, `tInst`, `Φ0`, `figAux` (`p = q = 2`) | `hs : AnpDetGhStep 3` (LW-12b–f pin) and `hξ : LWXi …` (owed random premise, registered `Axioms.lean:158`, proved by LW-11b's `lwXiClaim_holds` in `AuxGraph2`, which this file may not import). Both are other gates' pins |
| `anpDetGh_of_step` at `q = 2` | `anpKey_inst_figAux(_step)` l.908/912 | `figAux`, `GhostOK` from `figAux_nested.2` and `anpKey_ghostOK_of_noGhost` | `AnpDetGh 3` / `AnpDetGhStep 3` only |
| lemma (c′) `ghostify` | `anpKey_inst_ghostify` l.918 | `figAux` with its first step ghosted: `GhostOK`, `IsNested`, `nSolid = 5`, `nngh = 1`, `ordN − nngh = 0` | none |

None is degenerate: no `N = 0`, no empty index, no `False` premise. The `sz0` sizes are the merged instance data.

## 5. Axioms (`#print axioms`, same script)
```
'RBM.Graph.anpDetGh_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGh_of_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAnpKeyGh_of_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAnpKey_of_gh' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAnp_of_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey_inst_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey_inst_anp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey_inst_figAux' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey_inst_figAux_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey_inst_ghostify' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey_ghostify_ghostOK' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Paper-delta coverage
The prove report §(d) proposes:
- `T2234a`: deterministic form plus a one-event `≺`-lift, with no union bound over pairs.
- `T2234b`: base case `q = 0` uses the triangle inequality along a walk, `c = 1/max path length`, `C = 1`.
- `T2234c`: A2 replacement as `NGraph.ghostify`.
- `T2234d`: `q ≤ p` and `0 ≤ t` are unused; `η_t > 0` is derived from `STFlow`.

These cover every Lean/paper statement difference of targets 1–5. Both deltas the ticket expected, (a) and (b), are present.

## 7. Per-target verdicts
- Target 1 (`AnpDetGhAt`, `AnpDetGh`, `AnpDetGhZero`, `AnpDetGhStep`): **PASS** (`Iff.rfl` with the pins).
- Target 2 (`anpDetGh_zero`, with lemma (c′) `anpKey_ghostify_*`): **PASS**.
- Target 3 (`anpDetGh_of_step`): **PASS**.
- Target 4 (`lwAnpKeyGh_of_det`): **PASS**.
- Target 5 (`lwAnpKey_of_gh`, `lwAnp_of_key`): **PASS**.

Overall: **PASS**. No dispatcher sign-off needed.

## 8. Observations (not RETURN)
- The paper's induction hypothesis (`7_8:1107`) is "k ≤ q−1 internal vertices **and at most K solid edges**". `AnpDetGhStep` gives the IH for every graph with `k < q`, with any number of edges and paths. This is a stronger IH, so the assembly is sound. LW-12b–f will consume it. The dispatcher may fold this remark into `T2234a`.
- `T2234b` cites `7_8:1117` for the "trivial in the case q=0" sentence. In this TeX that sentence is at `:1117`, and the ticket says `:1110`. The difference is citation only.
- The lift takes the route of preflight (iii), using `Prec.whp` + `HighProbAt.inter` with the union inside `badSetAt`, not the ticket's union bound over `L^{2d}` pairs. The statement is unchanged, and the change is recorded in `T2234a`.
- The pre-check needs `Test/Axioms` rebuilt first, because a stale olean lists `AnpDetGhStep`. The hub's full `lake build` at merge does this.
