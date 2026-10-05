Auditor model: claude-opus-5-5

# T2170 audit (round 1) — LW-11a `GtoAG` deterministic part (`Graph/AuxGraph`)

Audited: branch `t/T2170` at `8c94145`, detached worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2170-audit1`; written Mon Oct  5 04:34:28 UTC 2026 (`date -u`).
Scratch files: `scratchpad/T2170/` (`ext.py`, `PinEq.lean`, `Ax.lean`, `Reg.lean`, `build.log`).

## 1. Diff scope

```
$ git diff --stat main...t/T2170
 RBM3D/Graph/AuxGraph.lean | 1847 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean    |    1 +
$ git diff main...t/T2170 -- RBM3D/Test/Axioms.lean | grep '^+ '
+   `RBM.Graph.LGraph.IsExtMol, -- an external molecule: a molecule containing an external vertex (`def_poly`, `7_8:172`): a defining predicate of the auxiliary graph, hypothesis of the nested-form lemmas of `Graph/AuxGraph` (T2170)
```
Only the two sole writable files; `Axioms.lean` change is one `structuralProps` registry line (allowed by the ticket's registry rule; `IsExtMol` is a structural predicate, used as `¬ Q.g.IsExtMol c` in `auxGraph_nodeV_int`). `AuxGraph.lean` imports only `RBM3D.Graph.LocalRegular2`, `RBM3D.Graph.LWSizeClaim` (merged); no merged file touched.

## 2. Statements against the pin (check file `docs/tickets/checks/T2170-check.lean`)

Text diff (each `def`/`abbrev` block of the check file against the branch file):
```
$ python3 scratchpad/T2170/ext.py docs/tickets/checks/T2170-check.lean RBM3D/Graph/AuxGraph.lean
abbrev LGraph.AuxIMol check: True file: True IDENTICAL
def LGraph.auxLab check: True file: True IDENTICAL
def LGraph.auxVal check: True file: True IDENTICAL
def LGraph.auxOrd check: True file: True IDENTICAL
def LWGtoAG check: True file: True IDENTICAL
def LWScalemole check: True file: True IDENTICAL
def LWAuxNested check: True file: True IDENTICAL
```
Elaboration check: section 2 of the check file (its own `T2170Check` vocabulary, `AuxOrdPin`, the three `Prop`s) copied verbatim into a scratch file that imports `RBM3D.Graph.AuxGraph`, followed by
```
example : ∀ d, T2170Check.LWGtoAG d = LWGtoAG d := fun _ => rfl
example : ∀ d, T2170Check.LWScalemole d = LWScalemole d := fun _ => rfl
example : T2170Check.LWAuxNested = LWAuxNested := rfl
theorem auditPin : T2170Check.AuxOrdPin := fun Γ =>
  ⟨Γ.scalingOrder_sub_auxOrd, Γ.molSolid_length_le, Γ.auxOrd_le_scalingOrder⟩
theorem auditG : ∀ d, T2170Check.LWGtoAG d := lwGtoAG_holds
theorem auditS : ∀ d, T2170Check.LWScalemole d := lwScalemole_holds
theorem auditN : T2170Check.LWAuxNested := lwAuxNested_holds
```
```
$ lake env lean scratchpad/T2170/PinEq.lean ; echo exit=$?
'auditPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditG' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditS' depends on axioms: [propext, Classical.choice, Quot.sound]
'auditN' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
So the three proved theorems prove exactly the dispatcher's independently elaborated pins, and the three target-2 theorems together prove `AuxOrdPin` (identity for every `Γ`, `|𝒢_ℳ| ≤ n_S`, `Normal → auxOrd ≤ scalingOrder`).
```
$ lake env lean scratchpad/T2170/Ax.lean    # #check lines
lwGtoAG_holds : ∀ (d : ℕ), LWGtoAG d
lwScalemole_holds : ∀ (d : ℕ), LWScalemole d
lwAuxNested_holds : LWAuxNested
```
Target-1 extras (unpinned text, ticket-described): `LGraph.auxVal_nonneg (hξ : ∀ u v, 0 ≤ ξ u v) : 0 ≤ Γ.auxVal ξ be`; helper `auxGraph_auxLab_ext (hext …) : auxLab Γ be b (molOf (inl a)) = be a`, both as the ticket says.

Mathematics (ticket targets 3–5): hypotheses, order (`3 ≤ d → ∀ L W … Γ, Normal → hext → ∀ D m Ψ C c r R ξ, …`), the window `W^{-d/2} ≤ Ψ`, `|E ⊕ I| r ≤ R`, `hξ` on `zdistD`-balls of radius `R`, both constants `K₁ = C·expC(d−2) c`, `K₁' = C·expC(d−2)(c/2)`, the tail `e^{-cr/2}` and the power `Ψ^{ord Γ − auxOrd Γ}` are as in the ticket's text; no `L^d ≤ W^K`, `Ψ ≤ 1` or `LocReg6`:
```
$ grep -nE "LocReg6|L \^ d ≤ W|Ψ ≤ 1" RBM3D/Graph/AuxGraph.lean ; echo $?
1
```

## 3. Vacuity, hidden hypotheses, cycles

- Every hypothesis of `LWGtoAG`, `LWScalemole`, `LWAuxNested` is inline in the pin; the structures involved (`LData`, `LGraph`, `PGraph`, `NGraph`) are data. `auxGraph_Data` (target 5) is an internal structure built inside the proof, never a hypothesis of a target.
- `hext` of `LWGtoAG` is unused by the proof (the report says so and proposes `T2170f`): the theorem is the pinned statement and at least as strong; no defect.
- No cycle: imports are merged modules only; no consumer pin is assumed.
- External hypotheses: none. The sample premises (entry bounds, decay, window, `hξ`) are deterministic premises by ticket design (§29 (5)); each is discharged at concrete data below (decay by the merged `lwSpOf_decay_E`).

## 4. Compiled nonempty instances (same file, `d = 3`, `L = 4`, `W = 2`)

| Endpoint | Instance (line) | Data | Verdict |
|---|---|---|---|
| target 2 (3 theorems) | `example` `:1710` | `figGraph` (`auxOrd = 2`, `ord = 4`) and `localReg2_inst_Q` (`2 ≤ 2`), normality by `decide` | nondegenerate |
| `lwGtoAG_holds` | `example` `:1743` | `figGraph`, `auxGraph_instD` (`G = m(0)I + ½J`, `M = m(0)I`, `S = lwSmat`, `S⁺ = lwSpOf`), `Ψ = ½`, `(C,c)` from `lwSpOf_decay_E`, `r = 1`, `R = 8`, `ξ ≡ ½`, `ℓe = lwSizeEll`; `hext` by `decide +kernel`; also proves `auxVal = 64` | all hypotheses discharged |
| `lwScalemole_holds` | `example` `:1785` | `auxGraph_instXY : LGraph (Fin 2) (Fin 0)` (normal, `x`,`y` one molecule, both by `decide`), `ℓe = ![0, fun _ => 4]`, `lwBdist = 6 > 2`, `r = 1` | all hypotheses discharged |
| `lwAuxNested_holds` | `example` `:1818` | `localReg2_inst_Q.pack`, `p = 2`, `LocReg345` merged, `𝓜_x ≠ 𝓜_y` proved (`auxGraph_inst_Q_hxy`); gives `NoGhost`, `IsNested`, `ordN = 2`, `n_M ≤ 2`, value `= 4` at `ξ ≡ ½` | nondegenerate |
| consumer chain | `example` `:1833` | `localReg2_inst_expansion` outputs: `Normal`, `hext`, nested `Γa` | supplementary |

`LGraph.auxVal_nonneg` and `auxGraph_auxLab_ext` are exercised through these instances (used at `:1045` in `lwGtoAG_holds` and `:1543-1545` in target 5). Graph facts use `decide`/`decide +kernel` only.

## 5. Build, axioms, hygiene

```
$ lake build RBM3D.Graph.AuxGraph      # audit worktree
✔ [3386/3386] Built RBM3D.Graph.AuxGraph (9.4s)
Build completed successfully (3386 jobs).
$ grep -c "AuxGraph.lean" build.log     # warnings/errors in the new file
0
$ lake env lean scratchpad/T2170/Ax.lean
'RBM.Graph.lwGtoAG_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwScalemole_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwAuxNested_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.auxOrd_le_scalingOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.scalingOrder_sub_auxOrd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.molSolid_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.LGraph.auxVal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.auxGraph_auxLab_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |@\[implemented_by|@\[extern|unsafe" RBM3D/Graph/AuxGraph.lean ; echo $?
1
```
Registry pre-check (no source edited: scratch file `import RBM3D` + `import RBM3D.Graph.AuxGraph` + `#assert_rbm_axioms`):
```
$ lake build RBM3D | grep -E "^error|Build completed"
Build completed successfully (3941 jobs).
$ lake env lean scratchpad/T2170/Reg.lean ; echo exit=$?
axiom audit: 5135 theorems, 1773 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0
```
Name clashes against current `main` (`7738afa`; the branch base is `87f617a`):
```
$ git grep -nE "auxGraph_|AuxIMol|auxLab|auxVal|auxOrd|LWGtoAG|LWScalemole|LWAuxNested|lwGtoAG_holds|lwScalemole_holds|lwAuxNested_holds|scalingOrder_sub_auxOrd|molSolid_length_le" 7738afa -- RBM3D | grep -v "LWVocab.lean\|LWPins.lean"
(empty)
$ git merge-tree --write-tree main t/T2170 >/dev/null; echo $?
0
```
Pinned names are as pinned; unpinned helpers carry the prefix `auxGraph_` (§3 (E)). No frozen signature touched.

## 6. Paper-delta coverage

Prove report (d) proposes `T2170a`–`T2170g`. Ticket-expected (a)–(e) map one-to-one to `T2170a`–`T2170e` (deterministic `GtoAG` with explicit tail and no `log W` loss; aux graph for normal graphs with `hext`, `(eq:MolVW)` summed; `ξ` any dominating block function; nested form needs `𝓜_x ≠ 𝓜_y`, `p ≥ 1`, symmetric `ξ`, walks, unused edges at `a_0`,`b_0`; deterministic `scalemole`). Extra: `T2170f` (`hext` unused), `T2170g` (target-4 instance uses `S⁺_{xy}`). Every statement difference found in §2 is covered.

## 7. Observations (no verdict effect)

- O1. The target-4 instance uses the waved edge `S⁺_{xy}` (`⟨true, true, …⟩`) instead of the ticket's `S_{xy}` (report: with `S` the value is exactly 0 at block distance 6). The theorem is applied with every hypothesis discharged at nondegenerate data either way; the nonzero value (1.08e-7) is numerical only, not in Lean. Recorded as `T2170g`.
- O2. The prove report's pin-diff paste shows only the `AuxIMol` and `auxLab` lines; §2 above covers all seven blocks.
- O3. For the hub at merge: `main` added two `structuralProps` lines to `RBM3D/Test/Axioms.lean` after the branch base (T2168). Do not copy the branch's `Axioms.lean` over `main`'s; bring in only the branch's one added line (3-way merge is clean, `merge-tree` exit 0).
- O4. The consumer-chain `example` (`:1833`) is existential in `outs` (could hold with `outs = []`); it is supplementary. The endpoint instances in §4 do not depend on it.

## 8. Verdict

| Target | Verdict |
|---|---|
| 1 vocabulary (`AuxIMol`, `auxLab`, `auxVal`, `auxOrd`, `auxVal_nonneg`, `auxGraph_auxLab_ext`) | PASS |
| 2 `scalingOrder_sub_auxOrd`, `molSolid_length_le`, `auxOrd_le_scalingOrder` (= `AuxOrdPin`) | PASS |
| 3 `LWGtoAG` / `lwGtoAG_holds` | PASS |
| 4 `LWScalemole` / `lwScalemole_holds` | PASS |
| 5 `LWAuxNested` / `lwAuxNested_holds` | PASS |

**T2170: PASS.** No dispatcher sign-off needed.
