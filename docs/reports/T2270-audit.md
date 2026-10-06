Auditor model: claude-opus-5-5

# T2270 audit (round 1): LW-12f, `RBM3D/Graph/AnpKey6.lean`

Started Tue Oct  6 09:05:45 UTC 2026 (`date -u`). Branch `t/T2270` at `a9fee57`, merge base `f515695`. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2270-audit1` (detached at `a9fee57`). Scratch: `<scratchpad>/T2270/` (`conf.lean`, `precheck.lean`, `neg.lean`).

**Verdict: PASS for all eleven targets** (`anpKey6_order`, `anpKey6_sum`, `anpKey6_union`, `anpDetGh_holds`, `anpDetGhCaseIV_holds`, `anpDetGhStep_holds`, `anpIH_holds`, `anpDetGhRegStep_holds`, `lwAnpKeyGh_holds`, `lwAnpKey_holds`, `lwAnp_holds`). No dispatcher sign-off needed.

## 1. Diff scope

```
$ git diff --stat main...t/T2270
 RBM3D/Graph/AnpKey6.lean | 1136 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |    8 -
$ git diff main...t/T2270 -- RBM3D/Test/Axioms.lean   (hunk @@ -158,14 +158,6 @@, deleted lines only)
-   `RBM.Gauss.Sizes.LWAnpKey, ...      -   `RBM.Gauss.Sizes.LWAnpKeyGh, ...   -   `RBM.Gauss.Sizes.LWAnp, ...
-   `RBM.Graph.AnpDetGhStep, ...        -   `RBM.Graph.AnpDetGhCaseI, ...      -   `RBM.Graph.AnpDetGhCaseIII, ...
-   `RBM.Graph.AnpDetGhCaseIV, ...      -   `RBM.Graph.AnpIH, ...
(context lines LWMomentExp before and LWReduceB after unchanged; list syntax intact; nothing added, nothing to supersededProps)
$ git merge-tree --write-tree main t/T2270 >/dev/null; echo $?      # main = b2529ba
0
$ grep -n "^import" RBM3D/Graph/AnpKey6.lean
6:import RBM3D.Graph.AnpKey5   7:import RBM3D.Graph.AnpKey4   8-13: six Mathlib modules (no `import RBM3D`)
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom' RBM3D/Graph/AnpKey6.lean
0
```
Only the two sole writable files; exactly the eight pinned registry lines deleted; no merged file or frozen signature touched. (`decide +kernel` appears once, in `anpKey6_inst_union`; kernel reduction, not `native_decide`; axioms below.)

## 2. Statements against the pins (script)

`conf.lean` = `import RBM3D.Graph.AnpKey6` + check-file section 2 (`T2270-check.lean:134-214`, namespace `RBM.Graph.T2270Check`) + T2264's interface (`T2264-check.lean:100-205`) + `audit_sumCert_iff` (T2264 audit §1) + the lines below + `#print axioms`.
```
example : T2270Check.AnpKey6OrderPin := @anpKey6_order
example : T2270Check.AnpKey6SumPin := @anpKey6_sum
example : T2270Check.AnpKey6UnionPin := @anpKey6_union
example : T2270Check.AnpKey6DirectPin := @anpDetGh_holds
example : T2270Check.AnpKey6IVPin := @anpDetGhCaseIV_holds
example : T2270Check.AnpKey6StepPin := @anpDetGhStep_holds
example : T2270Check.AnpKey6IHPin := @anpIH_holds
example : T2270Check.AnpKey6RegStepPin := @anpDetGhRegStep_holds
example : T2270Check.AnpKey6KeyGhPin := @lwAnpKeyGh_holds
example : T2270Check.AnpKey6KeyPin := @lwAnpKey_holds
example : T2270Check.AnpKey6AnpPin := @lwAnp_holds
example : T2264Check.AnpKey6SumPin := fun d p q n E h => @anpKey6_sum d p q n E ((audit_sumCert_iff n E).1 h)
example : T2264Check.AnpKey6DirectPin := @anpDetGh_holds
example : T2264Check.AnpKey6IVPin := @anpDetGhCaseIV_holds
-- check-file section 3 shapes (1)-(5), each closed by the file's instance theorem:
example : AnpDetGhAt 3 figAux ∧ AnpDetGhAt 3 anpKey5_figIVext ∧ AnpDetGhAt 3 anpKey2_figAuxGh := anpKey6_inst_det
example : LWAnpKeyGh 3 ∧ LWAnpKey 3 ∧ LWAnp 3 := anpKey6_inst_lw
example : AnpDetGhCaseI 3 ∧ AnpDetGhCaseIII 3 ∧ AnpDetGhCaseIV 3 ∧ AnpDetGhRegStep 3 ∧ AnpDetGhStep 3 ∧ AnpIH 3 2 := ⟨…projections of anpKey6_inst_cases…⟩
example : ∃ 𝓜 : Finset (Finset (Fin figAux.es.length)), (𝓜.card : ℝ) ≤ 9 ∧ ∀ M ∈ 𝓜, anpKey5_perPath figAux M :=
  let ⟨𝓜, h1, h2, _⟩ := anpKey6_inst_union; ⟨𝓜, h1, fun M hM => (h2 M hM).1⟩
-- shape (4) is the statement of anpKey6_inst_sum verbatim (AnpKey6.lean:1086-1091 vs check :233-240)
$ lake env lean conf.lean; echo exit=$?
exit=0          (axiom lines in §4)
```
Every target states its pin by `@name` with no added hypothesis, no reordering. `AnpKey6DirectPin`/`IVPin` are `∀ d, AnpDetGh d` / `∀ d, AnpDetGhCaseIV d`: the merged pins, unchanged; `AnpDetGhAt` (`AnpKey.lean:41-51`) has `∃ C c` before `∀ L ψ θ ξ a b` (uniform in `a, b`, §29 (5)); `C = Π_j max 1 |𝔓_j|`, `c = (1 + Σ_j |𝔓_j|)⁻¹` are explicit (`AnpKey6.lean:869-870`). The ≺ corollaries are general (`∀ d`), not a special case.

## 3. Hidden hypotheses, vacuity, cycles

- Hypotheses of the targets: `AnpSumOrder`/`AnpSumCert` (merged decidable data conditions, `AnpKey5.lean:86,95`), `GhostOK`, `IsNested` (merged Props), and the analytic ones (`AntitoneOn ψ`, `ψ > 0`, `θ > 0`, `0 ≤ ξ`, symmetric, `ξ ≤ ψ(|α-β|)`, row sum). `NGraph`/`NEdge` (`LWVocab.lean:304-312`) are data-only structures, no Prop fields.
- `anpDetGhCaseIV_holds`, `anpDetGhStep_holds`, `anpIH_holds` take the merged case/IH binders and do not use them (`intro d q _ _ p Γ π hG hN _ _ _`, `:925`): the conclusion holds without them, which is stronger, as the ticket's route 5 states.
- Dependencies: only merged `AnpKey5`/`AnpKey4` (and their imports); `anpDetGhRegStep_holds := anpDetGhRegStep_of_cases d (anpDetGhCaseI_holds d) (anpDetGhCaseIII_holds d) (anpDetGhCaseIV_holds d)`; `anpDetGhCaseIV_holds` uses `anpDetGh_holds`, not the region step: no cycle.
- No external hypothesis is introduced; `LWXi`, `STFlow`, `LWPsiAll` stay inside the merged `≺` pins (unchanged), so no new limit check is owed.
- Non-vacuity of `GhostOK ∧ IsNested`: discharged at `figAux`, `anpKey5_figIVext`, `anpKey2_figAuxGh` (instances below).

## 4. Build and axioms (audit worktree)

```
$ lake build RBM3D.Graph.AnpKey6 > build.log 2>&1; echo exit=$?
exit=0
$ grep -c error build.log; tail -1 build.log
0
Build completed successfully (3351 jobs).
$ lake env lean conf.lean   (the #print axioms part)
'RBM.Graph.anpKey6_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGh_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhCaseIV_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhStep_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpIH_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpDetGhRegStep_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAnpKeyGh_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAnpKey_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAnp_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_det_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_lw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_anp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.anpKey6_inst_union' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (all 311 root-imported modules + `AnpKey6` built in the audit worktree first; `precheck.lean` = the 311 `import` lines of `RBM3D.lean` + `import RBM3D.Graph.AnpKey6` + `import RBM3D.Test.Axioms` + `#assert_rbm_axioms`):
```
$ xargs lake build < mods.txt > mods.log 2>&1; echo exit=$?; tail -1 mods.log
exit=0
Build completed successfully (4076 jobs).
$ lake env lean precheck.lean > precheck.out 2>&1; echo exit=$?
exit=0
$ grep -n "^premises found\|^registry:\|error" precheck.out | cut -c1-120
156:premises found by scanning: 151 (borrowed 1, owed 93, structural 40, refuted 6, superseded 11).
157:registry: 2 borrowed + 147 owed + 103 structural + 7 refuted + 12 superseded; 120 registered premise(s) carry
$ for n in <8 deleted names>; grep -oE "\.$n([,:]|\])" precheck.out | wc -l
LWAnpKey 0 / LWAnpKeyGh 0 / LWAnp 0 / AnpDetGhStep 0 / AnpDetGhCaseI 0 / AnpDetGhCaseIII 0 / AnpDetGhCaseIV 0 / AnpIH 0
# negative control: same file without `import RBM3D.Graph.AnpKey6`
$ lake env lean neg.lean; echo exit=$?
error: axiom audit: 2 premise(s) that no theore…  [RBM.Graph.AnpDetGhCaseIV, RBM.Graph.AnpIH]
exit=1
```
So the hub must add `import RBM3D.Graph.AnpKey6` to `RBM3D.lean` at merge (CLAUDE.md §3 (A) 4); with it the registry is consistent. Full `lake build` is the hub's.

Name clash (new public names on current `main` b2529ba, which includes T2271):
```
$ for n in anpKey6_ anpDetGh_holds anpDetGhCaseIV_holds anpDetGhStep_holds anpIH_holds anpDetGhRegStep_holds lwAnpKeyGh_holds lwAnpKey_holds lwAnp_holds; git grep -c "$n" main -- RBM3D | wc -l
0 0 0 0 0 0 0 0 0
```
All public helpers carry the `anpKey6_` prefix (§3 (E)); two `private` helpers (`:960`, `:964`).

## 5. Compiled nonempty instances (Section 6, `AnpKey6.lean:960-1134`)

Concrete data `anpKey6_inst_data` (`:969`): `d = L = 3`, `ψ r = (1+r)⁻¹`, `θ = 1`, `ξ ≡ 1/6`; it proves every analytic hypothesis (antitone, `ψ > 0`, `θ > 0`, `0 ≤ ξ`, symmetry, `1/6 ≤ ψ(|α-β|)` via `zdistInf 3 3 x ≤ 1`, `Σ_β (1/6)² = 27/36 ≤ 1`). External labels `a ≡ 0`, `b ≡ 1` (distinct).
| target | instance applying it at concrete data | graphs (p, q) |
|---|---|---|
| `anpDetGh_holds` | `anpKey6_inst_det`, `anpKey6_inst_det_eval` (bound evaluated at the data) | `figAux` (2,2), `anpKey5_figIVext` (2,1), `anpKey2_figAuxGh` (2,2) |
| `anpKey6_order` | `anpKey6_inst_order` (order `[0]`, merged `anpKey5_inst_figIVext`) | rest of `figIVext` (2,1) |
| `anpKey6_sum` | `anpKey6_inst_sum` (depth-1 AM-GM certificate `anpKey5_inst_resAux.2.2`) | `figAux` minus `resAux` (2,2) |
| `anpKey6_union` | `anpKey6_inst_union` (`card ≤ 9` proved, `perPath`, bound at the data) | `figAux` |
| `anpDetGhCaseIV_holds`, `anpDetGhStep_holds`, `anpDetGhRegStep_holds`, `anpIH_holds` | `anpKey6_inst_apply` (all binders discharged by merged `anpKey5_inst_figIVext`, `anpKey2_inst_figAuxGh`, `figAux_nested`), `anpKey6_inst_cases` | `figIVext`, `figAux`, `figAuxGh` |
| `lwAnpKeyGh/Key/Anp_holds` | `anpKey6_inst_lw`; `anpKey6_inst_anp` = merged `anpKey_inst_anp`, `inst_AnpKey` with only `ξ`, `hξ : LWXi …` left (owed pin) | merged `sz0`, `z0`, `tInst`, `Φ0` |
No `N = 0`, empty index, collapsed window or `False` premise; all compile (build above, axioms above).

## 6. Paper deltas

Prove report (d) proposes `T2270a` (direct proof of `lem:Anp_key_gh` without induction on `q`/regions/cases, `7_8:1105-1384`), `T2270b` (explicit `C`, `c`), `T2270c` (AM-GM re-rooting as a finite binary tree; Lean has `∃ n`, no depth bound). These cover the ticket's expected (a)–(c). The intermediate pins (`(kwuyayw_ng)` exponent `ψ(0)^{|E|-2q}` with `ℤ` exponent, the union bound) are formal intermediate statements, not paper-statement changes; the case/IH binders being unused is the content of `T2270a`. Coverage complete.

## Observations (no verdict effect)

- Prove report line 1 is `Prover model: claude-sonnet-5-5`; report 242 lines (≤ 300).
- Instances are named `theorem`s rather than `example`s (allowed: "or a named check").
