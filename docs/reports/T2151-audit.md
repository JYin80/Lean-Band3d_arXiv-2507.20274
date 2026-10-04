Auditor model: claude-opus-5-5

# T2151 audit (round 1): LW-10b `Graph/LocalRegular2`, property (4) and assembly `lw_localregular_upto5`

Time: Sun Oct  4 23:29:22 UTC 2026 (`date -u`). Audit worktree `../RBM3D-wt/T2151-audit1`, detached at `bf3add3` (t/T2151); main `04aedec`, merge base `4f4612b`.
Scope after Amend 1 (DECISIONS §47): target 1 (property (4)) and target 3' `lw_localregular_upto5`; property (6) / `LocReg6` moved to LW-10c, not audited here.

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.LocalRegular2 2>&1 | grep -E "^error|LocalRegular2|Build completed"
Build completed successfully (3384 jobs).
(0 lines matching "error"; the only warnings printed are linter/deprecation warnings replayed from the merged LWLvl1.lean)
$ lake env lean scratchpad/T2151/ax.lean        # #print axioms
'RBM.Graph.fxyPowGraph_pathInv2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.pathInv2_locStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.PGraph.PathInv2.locReg345' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_localregular_upto5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg2_inst_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg2_inst_Q_locReg345' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg2_inst_step1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.localReg2_inst_R_not_pathInv2' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/LocalRegular2.lean
(no output)
$ git diff --stat main...HEAD ; git diff main...HEAD --name-only
 RBM3D/Graph/LocalRegular2.lean | 2068 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2068 insertions(+)
RBM3D/Graph/LocalRegular2.lean
$ grep -n "^import" RBM3D/Graph/LocalRegular2.lean
6:import RBM3D.Graph.LocalRegular
$ for n in PathInv2 pathInv2_locStep fxyPowGraph_pathInv2 lw_localregular_upto5 localReg2_ LocalRegular2; do git grep -l "$n" main -- RBM3D RBM3D.lean | wc -l; done
0 0 0 0 0 0
```
Only the sole writable file is touched (new); `RBM3D/Test/Axioms.lean` untouched (none expected); no merged file or frozen signature changed; imports only `RBM3D.Graph.LocalRegular`, not `RBM3D`.

## 2. Statements

### Target 1 — property (4): `PathInv2`, `fxyPowGraph_pathInv2`, `pathInv2_locStep`, `PGraph.PathInv2.locReg345`
```
1577: def PGraph.PathInv2 (p : ℕ) (Q : PGraph (Fin 2)) : Prop := Q.g.localReg2_PathFam p (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1))
 612: def LGraph.localReg2_PathFam (Γ) (p) (x y) : Prop := localReg2_Fam p (Γ.molOf x) (Γ.molOf y) (fun c => ¬ Γ.IsExtMol c) Γ.localReg2_edgeMS
 147: def localReg2_Fam (p : ℕ) (u v : N) (Int : N → Prop) (B : Multiset (Bool × Sym2 N)) : Prop :=
        ∃ (W : Fin p → List (N × N)) (col : Fin p → Bool),
          (∀ i, localReg_StepWalk u v (W i)) ∧
          localReg2_offDiag (localReg2_stepMS col W) = localReg2_offDiag B ∧
          (∀ A : Finset N, (∀ c ∈ A, Int c) → A.card ≤ (Finset.univ.filter fun i : Fin p => ∃ c ∈ A, localReg_StepWalk.Visits u (W i) c).card) ∧
          (∀ C σ, localReg2_present B C σ → ∃ i, col i = σ ∧ localReg_StepWalk.Visits u (W i) C)
1707: theorem fxyPowGraph_pathInv2 (p : ℕ) : (fxyPowGraph p).pack.PathInv2 p
1582: theorem pathInv2_locStep {m : ℂ} {P : PGraph (Fin 2)} {outs : List (PGraph (Fin 2))} (hst : LocStep m P outs) {k : ℕ}
          (hP : P.PathInv2 k) : ∀ B ∈ outs, B.PathInv2 k
1784: theorem PGraph.PathInv2.locReg345 {Q : PGraph (Fin 2)} {p : ℕ} (hL : Q.LocStd) (h : Q.PathInv2 p) : Q.LocReg345 p
```
Merged target predicate (LocalRegular.lean, unchanged): `PGraph.LocReg345 Q p := ∃ W, Q.LocReg3 p W ∧ Q.LocReg4 p W ∧ Q.LocReg5 p W`, with
`LocReg4 Q p W := ∀ c, ¬ Q.g.IsExtMol c → ∃ i j : Fin p, i ≠ j ∧ Visits (W i) c ∧ Visits (W j) c` = paper (4) `7_8:805-807` ("at least two paths
P_k ≠ P_l passing through it"). Checks against the ticket:
- "true at `(fxyPowGraph p).pack`": `fxyPowGraph_pathInv2`, for every `p` (no hypothesis; covers the paper's even `p`).
- "preserved by every `LocStep` output": `pathInv2_locStep`, only hypotheses `hst : LocStep m P outs` and `hP`; no premise on the step kind.
- "giving at a locally standard graph: every internal molecule is visited by two different walks": `PathInv2.locReg345` yields `LocReg4` together
  with `LocReg3`, `LocReg5` for one common `W` (ticket: one common walk family for (3)–(5)); only premise `Q.LocStd` = merged `LocReg1`
  (`PGraph.LocStd P := P.g.LocStd`, LWLvl1.lean:3215).
- The invariant is a `def` of `Prop` (no structure, no hidden field); not vacuous: proved at the start graphs and at `localReg2_inst_Q`, and refuted at
  the locally standard `localReg2_inst_R` for `p = 1` (negative control, §3). The labelled correspondence of `B:178-199` is replaced by colours, as the
  ticket allows ("e.g."); recorded as candidate `T2151d`.
Verdict target 1: **PASS**.

### Target 3' — `lw_localregular_upto5` (Amend 1)
Script diff against the merged `lw_localregular_expansion` (names normalized to `NAME`):
```
$ sed -n '/^theorem lw_localregular_expansion/,/:= by/p' LocalRegular.lean > old.txt ; sed -n '/^theorem lw_localregular_upto5/,/:= by/p' LocalRegular2.lean > new.txt ; diff old.txt new.txt
17,18c17
<       (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg35 p) ∧
<       (∀ Q ∈ outs ++ errs, Q.PathInv p) := by
---
>       (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p) := by
```
Ticket pin (Amend 1): `(eq:local_Gs)` (expectation identity, errors `≤ W^{−D}`) and, for every `Q ∈ outs`, `Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p`;
no `LocReg6`, no `M_x ≠ M_y` premise. The statement is the merged expansion statement (same parameters `p m c hc K0 d D`, same order, same error
regime `1 ≤ W, 1 ≤ L, L^d ≤ W^K0, W^{-d/2} ≤ Ψ ≤ W^{-c}`, same identity hypotheses) with `LocReg35 → LocReg345` and the auxiliary `PathInv`
conjunct dropped (not part of the pin). The proof uses merged `lvl1_lemma_size`, `lvl1_induction` and target 1; no new hypothesis; no cycle (the
module imports only the merged `Graph/LocalRegular`). Verdict target 3': **PASS**.

## 3. Compiled nonempty instances (same file, all compiled in the build above)
```
1896: example : (fxyPowGraph 2).pack.PathInv2 2 := fxyPowGraph_pathInv2 2
1898: example : (fxyPowGraph 4).pack.PathInv2 4 := fxyPowGraph_pathInv2 4
1902: theorem localReg2_inst_step1 : ∀ B ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false), B.PathInv2 2 :=
        pathInv2_locStep lvl1_inst_locStep_weight (fxyPowGraph_pathInv2 2)
1941: theorem localReg2_inst_Q_locStd : localReg2_inst_Q.LocStd := by decide
1945: theorem localReg2_inst_Q_pathInv2 : localReg2_inst_Q.pack.PathInv2 2 := by ...
2036: theorem localReg2_inst_Q_locReg345 : localReg2_inst_Q.pack.LocReg345 2 :=
        PGraph.PathInv2.locReg345 localReg2_inst_Q_locStd localReg2_inst_Q_pathInv2
2049: theorem localReg2_inst_R_not_pathInv2 : ¬ localReg2_inst_R.pack.PathInv2 1      -- negative control
1909: theorem localReg2_inst_expansion : ∃ outs errs, ... ∧ (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg345 2) := by
        obtain ⟨outs, errs, h1, h2, -, hid, h5⟩ := lw_localregular_upto5 2 (mE 0) (1 / 4) (by norm_num) 1 3 10
        ... h2 Q hQ 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_ (le_refl _)
        ... hid lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) (lwWx_mE_ne 0 lwWx_inst_hE)
              (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 lwSymmInstL
$ grep -rn "def lwWxInstSz" RBM3D/      # the merged instance data, also used by merged localReg_inst_expansion (LocalRegular.lean:2226)
RBM3D/Graph/LWWeightExp.lean:1382:def lwWxInstSz : Sizes 3 := lwWxSizes 3 3 1 (1 / 2) (le_refl 3)
```
- `fxyPowGraph_pathInv2`: at `p = 2` and `p = 4` (ticket: items at `fxyPowGraph 2`, `fxyPowGraph 4`).
- `pathInv2_locStep`: at a real merged `LocStep` (`lvl1_inst_locStep_weight`, weight step on `fxyPowGraph 2`), hypothesis `hP` discharged.
- `PathInv2.locReg345`: at `localReg2_inst_Q` (two external, two internal vertices, one internal molecule `{α, β}`, `p = 2`), both hypotheses
  discharged (`decide`, explicit walks); nondegenerate (the internal molecule exists, so `LocReg4` is not vacuous there).
- `lw_localregular_upto5`: at `p = 2`, `d = 3`, `c = 1/4`, `K0 = 1`, `D = 10`; error regime at `W = 27`, `L = 3`, `Ψ = 27^{-1/4}` with all five
  inequalities discharged; identity at the merged data `lwWxInstSz` (`d = 3`, `L = 3`, `W = 1`, 27 lattice sites), every deterministic hypothesis
  discharged; `GaussIBP` by the merged `gaussIBP`. No external hypothesis remains.
No `N = 0`, empty index, collapsed window or `False` premise.

## 4. Paper deltas
Lean/paper differences of the delivered statements and their coverage:
| difference | coverage |
|---|---|
| (3)–(5) are walks in the molecular multigraph (each edge occurrence once), not simple paths; no `(eq:far_ab)` assumption (`7_8:792`) | D338 (`T2142a`, in `docs/paper-deltas.md:1297`); restated in candidate `T2151d` |
| (4) proved via the coloured exact invariant instead of the labelled correspondence of `B:178-199` (proof route, statement unchanged) | candidate `T2151d` |
| pulled edge inside a molecule / weight case of `B:197` (closed detour; clause (c) for diagonal edges) | candidate `T2151e` |
| `lem:localregular` (6) and `(eq:deg_mole)` not stated here | Amend 1 (DECISIONS §47): (6) is LW-10c; `(eq:deg_mole)` is a stated consequence, not a target |
| `p` arbitrary in `ℕ` (paper `p ∈ 2ℕ`) | generalization, no weakening; observation |
Candidates `T2151a`–`T2151c` (about (6)) are carried for LW-10c as Amend 1 says. Coverage complete.

## 5. Observations (no effect on verdict)
1. In `localReg2_inst_expansion` the error regime is evaluated at `W = 27` while the identity is at the sample data with `W = 1`; this is the same
   arrangement as the merged `localReg_inst_expansion` (data named by the ticket), and each conjunct is discharged at concrete nondegenerate data.
2. The instance of `lw_localregular_upto5` does not exhibit a nonempty `outs`; the endpoint is an existential, and `LocReg345`/(4) is separately
   instantiated at a nondegenerate locally standard graph (`localReg2_inst_Q_locReg345`).
3. The prove report's statement extract for `localReg2_Fam` and the target signatures match the file (checked above).

## Verdict
- Target 1 (property (4): `PGraph.PathInv2`, `fxyPowGraph_pathInv2`, `pathInv2_locStep`, `PGraph.PathInv2.locReg345`): **PASS**.
- Target 3' (`lw_localregular_upto5`): **PASS**.
- Ticket T2151: **PASS**. No dispatcher sign-off needed.
