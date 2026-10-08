Auditor model: claude-opus-5-5

# T2297 audit (round 1): LW-02 `lem:LW_moment`, `RBM3D/Graph/LWMoment.lean`

Started Thu Oct  8 19:18:50 UTC 2026, finished Thu Oct  8 19:21:47 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2297-audit1`, detached at `t/T2297` = a94212e (merge base with main 3f750b6; main at 84cd789).
Inputs: ticket T2297, Amend 1 (engine `lw_localregularX`, F2 near pairs by the max bound), Amend 2 (stop size 2000; instance (3) superseded by the engine conjunct `nWS ≥ p`), check file `docs/tickets/checks/T2297-check.lean` section 2.

## 1. Diff scope and frozen files
```
$ git diff --stat main...t/T2297
 RBM3D/Graph/LWMoment.lean | 1872 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    4 +-
$ git diff main...t/T2297 -- RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.LWMoment, -- `lem:LW_moment` (`7_8:72-77`): LW-02
-   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-02, LW-13
+   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-13b
+   `RBM.Gauss.Sizes.LWMomentCtx, -- the hypotheses of `lem:LW_moment` for one choice of the constants and sequences, bundled as the binder of the internal lemmas of `LWMoment.lean` (fields = the pin's hypotheses, nothing else; LW-02, T2297, DECISIONS §20: structural)
$ git diff main...t/T2297 -- RBM3D/Graph/LWPins.lean RBM3D/Graph/LWEngine.lean | wc -l
       0
$ git diff --stat 3f750b6 main -- RBM3D/ | tail -1      (main since the branch base)
 4 files changed, 3279 insertions(+), 1 deletion(-)   (new modules + Axioms.lean: 1 line `STDuhamelII` removed at :179, disjoint from this ticket's lines)
```
Only the two sole writable files; one owed line deleted, one comment edited, one `structuralProps` line added (the ticket allows a structural line for a new Prop-valued binder). No merged signature changed.

## 2. Build, forbidden tokens, axioms
```
$ lake build RBM3D.Graph.LWMoment 2>&1 | grep -E "^error|Build completed"
Build completed successfully (3894 jobs).
$ ls -la .lake/build/lib/lean/RBM3D/Graph/LWMoment.olean   (absent from main's cache; built now)
-rw-r--r--@ 1 junyin  staff  5508016 Oct  8 12:18 .../LWMoment.olean      (12:18 local = 19:18 UTC)
$ grep -c -w -E 'sorry|admit|native_decide|axiom' RBM3D/Graph/LWMoment.lean
0
$ wc -l RBM3D/Graph/LWMoment.lean
    1872 RBM3D/Graph/LWMoment.lean      (Amend 2 stop size 2000)
```
`pin.lean` (import `RBM3D.Graph.LWMoment`; check-file section 2 `namespace T2297Check … end T2297Check` copied verbatim by `sed`; then):
```
example : T2297Check.LWMomentPin := @RBM.Gauss.Sizes.lwMoment_holds
example : T2297Check.LWMomHomPin := @RBM.Graph.lwMoment_val_smul
example : T2297Check.LWfBridgePin := @RBM.Graph.lwMoment_fxy_bridge
example : T2297Check.LWMomentPin = ∀ d, RBM.Gauss.Sizes.LWMoment d := rfl
$ lake env lean pin.lean; echo "exit $?"
'RBM.Gauss.Sizes.lwMoment_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMoment_val_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwMoment_fxy_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwMoment_inst_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwMoment_inst_moment_endT' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
The three `example`s elaborate with the term `@target` and no extra argument: each target states its pin exactly, with no added hypothesis.

## 3. Registry pre-check (branch imports + LWMoment + Axioms) and negative control
```
$ lake build RBM3D.Test.Axioms 2>&1 | grep -E "^error|Build completed"
Build completed successfully (2 jobs).
$ { grep "^import RBM3D\." RBM3D.lean; echo "import RBM3D.Graph.LWMoment"; echo "import RBM3D.Test.Axioms"; echo "#assert_rbm_axioms"; } > reg.lean; grep -c '^import' reg.lean
380
$ lake env lean reg.lean > reg.out 2>&1; echo "exit $?"
exit 0
$ grep -c 'Sizes.LWMoment,' reg.out
0
$ grep -n "LWMoment\|^axiom audit\|^premises found\|error" reg.out | cut -c1-160
1:axiom audit: 10293 theorems, 3044 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
57:  RBM.Gauss.Sizes.LWMomentExp: 1 [no certificate]
135:premises found by scanning: 140 (borrowed 1, owed 78, structural 42, refuted 6, superseded 13).
$ grep -v "import RBM3D.Graph.LWMoment" reg.lean > regneg.lean; lake env lean regneg.lean > regneg.out 2>&1; echo "exit $?"
exit 1
$ grep -n "error\|\[RBM.Gauss.Sizes.LWMoment\]" regneg.out | cut -c1-120
1:.../regneg.lean:380:0: error: axiom audit: 1 premise(s) that no theorem of this development p
2:  [RBM.Gauss.Sizes.LWMoment]
```
So the deleted owed line is justified exactly by `lwMoment_holds`, and the root `RBM3D.lean` needs `import RBM3D.Graph.LWMoment` at merge (hub step (A) 4). The full build is the hub's at merge.

## 4. Statements (extracted by `sed` from the branch file)
```
$ sed -n 57,60p RBM3D/Graph/LWMoment.lean
theorem lwMoment_val_smul :
    ∀ {E I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
      (Γ : LGraph E I) (D : LData ι) (s : ℂ) (ℓe : E → ι),
      Γ.val { D with S := s • D.S } ℓe = s ^ (Γ.waved.countP (fun e => !e.col)) * Γ.val D ℓe := by
$ sed -n 79,84p RBM3D/Graph/LWMoment.lean
theorem lwMoment_fxy_bridge :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ)
      (Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ω : sz.SeqΩ)
      (x y : Idx d (sz.L n) (sz.W n)),
      fxyVal (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) Sp ω) x y =
        (t : ℂ) * RBM.Gauss.Sizes.LWf sz n E t ω x y := by
$ sed -n 1785,1789p RBM3D/Graph/LWMoment.lean
theorem lwMoment_holds : ∀ d : ℕ, LWMoment d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 p hp2 ε₀ C₁ C₂ C₃ Cc
  refine ⟨1, one_pos, ?_⟩
  intro 𝔠 sz z hflow t ht0 ht1 Ψ Φ hassm
  ...
  let S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₀ C₁ C₂ C₃ Cc Ψ Φ := ⟨hd, hκ, hε, h𝔡, hflow, ht0, ht1, hassm⟩
```
`LWMoment` (`LWPins.lean:325`, unchanged): `3 ≤ d → ∀ κ ε 𝔡 > 0, ∀ p, 2 ∣ p → ∀ ε₀ C₁ C₂ C₃ Cc, ∃ c > 0, ∀ 𝔠 sz z, STFlow … → ∀ t, 0 ≤ t ≤ lemT z → ∀ Ψ Φ, LWAssm … → Prec (∫‖LWf‖^p) ((η_t⁻¹ Φ(0) Φ(c·zdistInf(blocks)))^p)`. Parameter order (`c` before `𝔠, sz, z, t`), exponent `p`, losses `η⁻¹ Φ(0) Φ(c|a−b|)` and the `t`-range are those of `7_8:72-77`. Proof takes `c = 1` uniformly (proposed `T2297e`).
`LWMomentCtx` (`:160-169`): fields `hd, hκ, hε, h𝔡, flow, t0, t1, assm` = the pin's hypotheses, nothing else; it is built inside `lwMoment_holds` from the intro'd hypotheses (line above), never a hypothesis of a target. `LWMomFar`/`LWMomNear` (`:1233`, `:1546`) are index `Type`s (pair subtypes), joined by `by_cases` on `K (log W)² < lwBdist` (`:1806-1808`), covering every pair.

## 5. Hidden hypotheses, vacuity, cycles
- No target has a hypothesis beyond its pin (section 2 `example`s). `lwMoment_holds` has no hypothesis at all, so every internal lemma premise is discharged; the only open premises are inside the pin (`LWAssm`'s `LWInit`, `LWLoop2`: owed registry lines; `LWWindow`, `LWClass`, `LWPsiRel`: structural), unchanged from the merged pin.
- Imports: `LocalRegular6d`, `AnpKey6`, `AuxGraph2`, `LWExpTerm2`, `LWEngine` (all merged on main, `RBM3D.lean` imports them); no import of `RBM3D`; new module, so no cycle.
- Name clash: `67` public names (`theorem|def|structure` at column 0), `grep -rlw` over main `RBM3D/` and `docs/tickets/T2296.md`: `total hits: 0`. Unpinned helpers carry the file-stem prefix `lwMoment_`/`LWMom…` (§3 (E)).

## 6. Compiled nonempty instances
Examples (1), (2) of the file (`:1824-1828`, `:1836-1839`) recompiled as named theorems `auditInst1`, `auditInst2` (`inst.lean`, bodies copied by `sed`):
```
'RBM.Graph.auditInst1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.auditInst2' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Graph.auxGraph_instD : RBM.Graph.LData (RBM.Gauss.Idx 3 4 2)
RBM.Gauss.SizesInst.sz0 : RBM.Gauss.Sizes 3
```
- (1) `lwMoment_val_smul` at `fxyPowGraph 2`, `auxGraph_instD` (`d = 3`, `L = 4`, `W = 2`), `s = 1/2`, `nWS = 2` by `lwEngine_fxy_nWS 2`: factor `1/4`. Nondegenerate.
- (2) `lwMoment_fxy_bridge` at `sz0` (`Sizes 3`), `n = 0`, `E = 0`, `t = 1/2`, `Sp = lwSplus …`, `x = 0`, `y = 1`, every `ω`. Nondegenerate.
- (3) superseded by the engine conjunct `nWS ≥ p` of `lw_localregularX` (Amend 2).
- (4) `lwMoment_inst_moment := inst_LWMoment (lwMoment_holds 3) 2 (dvd_refl 2) hI hL`, `lwMoment_inst_moment_endT := inst_LWMoment_endT (lwMoment_holds 3) 2 …` (`:1851`, `:1861`). The merged consumers (`LWPins.lean:638`, `:794`) discharge every deterministic premise at concrete data (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `flow_z0`, `tInst ≡ 1/16` / `tEnd = lemT z0`, `ε₀ = 1/20`, `C₁ = C₂ = 2`, `C₃ = 1`, `Cc = 1`, `Ψ0 = Φ0 = W⁻¹`, `window0`, `class0`, `psiRel0`); only `hI : LWInit …`, `hL : LWLoop2 …` stay, other gates' owed pins (allowed, CLAUDE.md §4 step 2). `p = 2 > 0`, so the instance exercises the main (non-`p = 0`) branch.

## 7. Paper deltas
The Lean statement is the merged pin unchanged, so no new statement delta; the route differences are proposed in the prove report (d): `T2297a` (S1: `S^{(t)} = tS`, homogeneity and `nWS ≥ p`, `t = 0` apart), `T2297b` (`(eq:far_ab)` only for far `𝓜_x = 𝓜_y` outputs), `T2297c` (upgrade by `lwExpTerm_prec_integral` with polynomial envelope/floor, not `N η_t^{-3}`; `LWInteg` unused), `T2297d` (F2: near pairs by the max bound at `Ψ' = max(Φ(0), W^{-d/2})`, polylog loss absorbed in `N^τ`), `T2297e` (`c = 1`). These cover the ticket's expected (a)–(c) and both amendments. `grep -n "T2297" docs/paper-deltas.md`: no hits (not yet numbered; dispatcher's step).

## 8. Observations (no RETURN)
- O1: On the branch a full `lake build` fails only at the root `#assert_rbm_axioms` with `[RBM.Gauss.Sizes.LWMoment]` (section 3 negative control), because `RBM3D.lean` lacks `import RBM3D.Graph.LWMoment` until the hub adds it (§3 (A) 4). Expected; not a defect.
- O2: `Test/Axioms.lean` on main changed since the branch base (`STDuhamelII` line removed). The hub must apply this ticket's three registry edits to main's file by text, not check out the branch's file (which would restore `STDuhamelII`).
- O3: The prove report's registry pre-check uses the import lines of `RBM3D.lean` rather than `import RBM3D`; reproduced here with the same result, plus a negative control.

## Verdicts
| target | statement vs pin | hidden hyp / vacuity / cycle | instance | build / axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `lwMoment_val_smul : LWMomHomPin` | exact (`example … := @…`) | none | (1) compiled | OK / 3 std | `T2297a` | PASS |
| `lwMoment_fxy_bridge : LWfBridgePin` | exact | none | (2) compiled | OK / 3 std | `T2297a` | PASS |
| `lwMoment_holds : LWMomentPin` | exact (`∀ d, LWMoment d`) | none; no hypothesis | (4) compiled, only owed pins `LWInit`, `LWLoop2` open | OK / 3 std | `T2297a`–`e` | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
