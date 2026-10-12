Auditor model: claude-opus-5-5
# T2472 audit, round 1: L3d4a `Graph/BAProv` (targets 1-4, 5 (a), 9), written Mon Oct 12 22:24:42 UTC 2026
Inputs: ticket `docs/tickets/T2472.md`; check `docs/tickets/checks/T2472-check.lean`; prove report (a), (a″), (b)-(d); 1a-audit `T2472-1a-audit.md` §3 (texts fixed), §8 (split confirmed, instance condition).
Branch `t/T2472` e7ada40a; audit worktree `RBM3D-wt/T2472-audit1` (detached, own `.lake/build` clone); scratch `<scratchpad>/T2472/audit1/`.
Scope: the pre-signed split was confirmed at the 1a-audit (§8), so this round audits L3d4a only. Targets 5 (b), 6, 7, 8, 10 are L3d4b (`BAProvB`, stacked branch) and are not judged here.

## 1. Diff, build, axioms, hygiene (script output)
```
$ git diff --stat main...t/T2472          # main ae791953
 RBM3D/Graph/BAProv.lean    | 877 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2472Pins.lean | 399 +++++++++++++++++++++
 2 files changed, 1276 insertions(+)
RBM3D/Graph/BAProv.lean: 0 removed lines ; RBM3D/Probe/T2472Pins.lean: 0 removed lines
$ lake build RBM3D.Graph.BAProv           # audit worktree; error lines: none
Build completed successfully (3950 jobs).
exit=0
$ lake env lean axioms.lean               # import RBM3D.Graph.BAProv + #print axioms of all 67 public theorem/def/abbrev/structure names (grep-generated)
67 output lines; 67 = "depends on axioms: [propext, Classical.choice, Quot.sound]"; 0 other
$ lake env lean assert.lean               # import RBM3D; import RBM3D.Graph.BAProv; #assert_rbm_axioms
axiom audit: 13957 theorems, 4423 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
assert exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^inductive|maxHeartbeats" RBM3D/Graph/BAProv.lean | wc -l
0
$ grep -nE "sz\.lam|withLam|Sizes|gK|BAShapeLL|BAFrameStepTN|T2472_Binder" RBM3D/Graph/BAProv.lean | wc -l     # UBA-C1, binder
0
$ git grep -l -E "$PAT" main -- RBM3D RBM3D.lean | wc -l ; (77 branches t/T24* other than t/T2472)   # PAT = new public names, as in (b)
0          branches with hits: none
$ git grep -l "Graph.BAProv\|Probe.T2472Pins" t/T2472 -- RBM3D.lean RBM3D | grep -v "BAProv.lean\|T2472Pins.lean"
(no output: no importer)
```
Both touched files are sole writable files (ticket :69). No merged file edited, no frozen signature touched. `open private` only (BAProv.lean:40-42), no `private` deleted.

## 2. Statements against the pins and the fixed texts
Binding pins (check Part 2) applied to the delivered theorems, in one scratch file = the check's Part 2 + `import RBM3D.Graph.BAProv`:
```
# pins.lean, lines appended after the check's Part 2 (excerpt; the three shape statements abbreviated as <...>)
example : T2472_FxyDUniv := @fxyValD_univ
example : T2472_FxyDUnion := @fxyValD_union
example : T2472_Bridge := @baProv_bridge
example : <check shape "target 1 at weight 1"> := fun Γ D ℓe => BAGraph.valW_one Γ D ℓe
example : <check shape "start of target 4"> := by intro p P0 hP0; obtain ⟨o, rfl, hE, -, hC⟩ := BAProv_start p P0 hP0; exact ⟨o.π, hE, hC⟩
example : <check shape "root map L3d2b reads"> := by ... BACoverBy.rep ...
$ lake env lean pins.lean ; echo exit=$?
exit=0                                     # no error lines
$ lake env lean docs/tickets/checks/T2472-check.lean   # in the audit worktree (acceptance: the check compiles on the branch)
check exit=0
$ diff -B <(T2472_FxyDUniv/FxyDUnion/Bridge bodies from the check) <(BAProv.lean:847-870 example bodies)
pin bodies identical (blank lines ignored) to BAProv.lean:847-870
```
Texts fixed at the 1a-audit (§3: targets 1, 2, 3, 9 (a)) against the delivered file (`stmtdiff.py`: docstrings stripped, whitespace normalised; theorem statements up to `:=`):
```
$ python3 -I stmtdiff.py RBM3D/Probe/T2472Pins.lean RBM3D/Graph/BAProv.lean
SAME BACoverBy  SAME BACoverBy.comp  SAME BACoverBy.rep  SAME BAGraph.valW  SAME BAGraph.valW_one  SAME BAPGraph.valW  SAME BAProvOut
SAME BAProvOut.ExtOK  SAME BAProvOut.Molecular  SAME BAProvOut.Molecular.comp  SAME BAProvOut.comp  SAME BAProvOut.ofTerm  SAME BAProvOut.twist
SAME BAWExp  SAME BAWExp.refl  SAME fxyValD  SAME BAProv_exists_append  SAME BAProv_merge_reach  SAME BAProv_provOuts  SAME BAProv_reach_map
DIFF BAProv_cover_term / BAProv_ofTerm_good / BAProv_outsOf_exists   # stem helpers: the probe's Boolean test `BAProv_chk` replaced by the Prop `BAProv_Ext` (stronger: all parents)
DIFF BAProv_twist_mol_iff                                            # section variables only
probe-only: BAEngineProv BAProvStepPos baEngineProv_imp_localregularX ... (L3d4b) and the probe instances
```
`.comp`/`.prod` (1a-audit §3: diff against the band twins). Read side by side with `LWProv.lean:82-130`: `BAWExp.comp` = `WExp.comp` and `BAWExp.prod` = `WExp.prod` with `WExp m` → `BAWExp d`, `ProvOut` → `BAProvOut`, `pvalW` → `BAPGraph.valW`, `(fxyPowGraph p).pack` → `baPG (BAGraph.ofLGraph (fxyPowGraph p))`, and the nine band data premises (`GaussIBP`, `M = mI`, flow fixed point) → `3 ≤ L`, `BASelf d L g0 Em m`, `0 ≤ t`, `t < 1` at `BAlwData`, law `PF d L W 0` (C1, ticket :22, :30). Weights, `ℓe`, list shape and `π`-reading identical.

Per target (ticket :20-28, mathematics):
| target | Lean | verdict on the statement |
|---|---|---|
| 1 | `BAGraph.valW` (:52), `BAPGraph.valW` (:57, packing literal of `BAPGraph.val`), `valW_one` (both), `BAPGraph.valW_of_factor`/`_of_not` (:72, :81) | = ticket formula; twin of `valW`, `pvalW`, `lwProv_pvalW_of_factor/_of_not` |
| 2 | `BAProvOut` (data fields `Q`, `π` only), `ExtOK`, `Molecular` (both conjuncts on `.g.shadow`), `comp`, `Molecular.comp`, `ExtOK.comp`, `BACoverBy` (over `LGraph.AuxIMol P.g.shadow`), `BACoverBy.comp`, `BACoverBy.rep` | as fixed (§275 (5)); no tags; no Prop field in the structure |
| 3 | `BAWExp d P outs` (:145), `.refl`, `.comp`, `.prod` | C1 exactly; every real `Wt`; see above |
| 4 | `BAProv_frameStep_pos` (:474, all five `BAFrameStep` kinds by `cases`), `BAProv_twist_pos`, `BAProv_locStep_pos` (`BALocStep P L → P.g.Normal → BAProvPos P L`), `BAProv_outsOf_exists` (`splitG`, `merge`/`packMerge`, `outsOf`), `BAProv_start p` (all `p`: `o.Q = P0`, `ExtOK`, `Molecular`, `BACoverBy (π ∘ inr ∘ localReg_fxyBeta)`) | general (every parent with `=`-free dotted edges, implied by `Normal`: `hN'.1` at :513); not a special case. `BAProvPos` = `∃ ps, ps.map (·.Q) = L ∧ ∀ o ∈ ps, ExtOK ∧ Molecular` (a conclusion, not a premise) |
| 5 (a) | `BAGraph.valW_partition` (:668): `Γ.valW D Wt ℓe = Σ_{Δ ∈ splitG} Δ.packMerge.valW D (Wt ∘ (· ∘ vmap_Δ)) ℓe` | per labelling, any `D : BALData`, no data hypothesis (band needs `hM`); twin of `lwProv_valW_partX` :809 |
| 9 (a)-(c) | `fxyValD`, `fxyValD_univ`, `fxyValD_union`, `baProv_bridge` | = binding pins (exit 0 above). Domain on `[β]` = `a₁` of `7_8:1607-1611` (`β ∈ [a₁]`, restriction on `a₁`) |

## 3. Vacuity, hidden hypotheses, cycles
- Structure fields: `BAProvOut` has `Q : BAPGraph (Fin 2)`, `π` only. Prop-valued defs (`ExtOK`, `Molecular`, `BACoverBy`, `BAWExp`, `BAProvPos`) are concluded by theorems of the file (`BAProv_start`, `BAProv_*_pos`, `BAWExp.refl/.comp`); the only Prop premises of public results are closure premises of the same kind (`Molecular.comp`, `BACoverBy.comp`, `BAWExp.comp/.prod`), as in the band.
- Deterministic premises: `hD : ∀ e ∈ P.g.dotted, e.eq = false` (discharged by `decide` at the instances and by `Normal` in `BAProv_locStep_pos`), `Even p`, `Disjoint D₁ D₂`, `3 ≤ L`, `BASelf`, `0 ≤ t < 1` (from `flowP_data`). No external hypothesis, no registry entry, no `T2472_Binder`.
- Cycle: imports `BAEngine`, `BAAtom`, `LWProv` (all on `main`); no import of the probe, of `BAProvB`, or of unmerged branches.

## 4. Compiled nonempty instances (BAProv.lean §7, built above; `d = 3`, `L = 4`, `W = 2`, flow point, `ℓ0` with `x`, `y` in different blocks)
| target | line | data |
|---|---|---|
| 9 (a), (b), (c) | 767 | `univ = {0} ⊔ (univ \ {0})`; bridge at `p = 2`, `Dm = {0}` (proper, nonempty), every `ω` |
| 9 (c) at `univ`, 1 (`valW_one`) | 780 | recovers the pointwise form of `ba_fxyPow_integral_eq` |
| 5 (a) | 786 | `splitG.length = 16` (`decide +kernel`) and the weighted partition at weight `Π_k 1_{0}` |
| 4 start, 2 (`BACoverBy`) | 795 | `partition.length = 16`, `BAProv_start 2`, control: `β₀` alone does not cover (`decide +kernel`) |
| 3 `.prod`, `.comp` | 806, 814 | flow point, `w_k = 1` at `ℓ0 0`, `1/2` elsewhere; hypothesis discharged by `BAWExp.refl` |
| 4 frame kinds, twist | 821-843 | `gg` at `P_A` (31 outputs), `within` `P_B`, `ggSplit` `P_C`, `edge` `P_E`, `weight` at the first start term, `locStepB`/`normalB`; lists nonempty |
This meets the 1a-audit §8 instance condition for L3d4a (9 (c) at `univ` and `{0}`, `BACoverBy` at the 16 start terms, `BAWExp.prod` at the flow point).
`Molecular.comp`, `ExtOK.comp`, `BACoverBy.comp`, `BACoverBy.rep` have no example in the file (observation O1); audit scratch check that they apply at concrete data:
```
$ lake env lean comp_inst.lean   # import RBM3D.Graph.BAProv; at each of the 16 start terms P0 of fxyPowGraph 2: o from BAProv_start 2, o' = ⟨o.Q, id⟩;
                                 # (o.comp o').ExtOK by ExtOK.comp, .Molecular by Molecular.comp, BACoverBy.comp, then BACoverBy.rep gives rep, k
exit=0                           # no error lines
```

## 5. Paper deltas
Lean/paper differences of this row and their coverage in the prove report (d):
- "every internal vertex of the auxiliary graph in `D`" (`7_8:1631-1650`, `B:522-524`) as the weight `Π_k 1_{Dm}([β^{(k)}])` on the start graph carried by provenance maps, roots = images of `β^{(k)}`, no `(log W)^{1+ε₁}` shift: **T2472a**.
- molecules read on `BAGraph.shadow` (waved, `=`, `Ψ`, `M` edges join): **T2472b**.
- `BAWExp`, `fxyValD`, bridge at the data level `BAlwData`/`PF d L W 0`, every real weight, no `m`-partition/tags: **T2472c**.
- `p` even in the bridge and `fxyValD` with `Ǧ = G − M` on the diagonal are the band's (`lwProv_bridge`, `fxyVal` LWVocab:217); no new delta. No difference found without a candidate.

## 6. Observations (no RETURN)
- O1 The target-2 closure lemmas (`Molecular.comp`, `ExtOK.comp`, `BACoverBy.comp`, `BACoverBy.rep`) are unused in this file and have no in-file example; the ticket's instance list (target 10) and the 1a-audit §8 condition do not name them, and §4's scratch shows they apply at the 16 concrete start terms. Their consumers are L3d4b (recursion) and L3d2b (`rep`).
- O2 The `BAWExp.prod` instance uses the trivial one-output list (`BAWExp.refl`); every deterministic premise is discharged at the flow point. A `BAWExp` for an actual step (5 (b), 6) is L3d4b's.
- O3 `RBM3D/Probe/T2472Pins.lean` is on the branch (sole writable, "1a only, never merged", ticket :69): at merge bring in `RBM3D/Graph/BAProv.lean` only, plus the `import RBM3D.Graph.BAProv` line in `RBM3D.lean`.
- O4 Prove report (b) says "67 public declarations"; the audit's grep-generated list has 67 names, all standard axioms. Consistent.

## Verdict
T2472 / L3d4a (`RBM3D/Graph/BAProv.lean`): targets 1, 2, 3, 4, 5 (a), 9 (a)-(c): **PASS**.
The binding pins `T2472_FxyDUniv`, `T2472_FxyDUnion`, `T2472_Bridge` are proved by the delivered theorems. The texts fixed at the 1a-audit are unchanged. The module builds and prints only the standard three axioms, and every endpoint has a compiled nondegenerate instance. The diff touches only sole writable files, and paper deltas T2472a-c are proposed. Targets 5 (b), 6-8, 10 are out of scope (L3d4b). No dispatcher sign-off needed.
