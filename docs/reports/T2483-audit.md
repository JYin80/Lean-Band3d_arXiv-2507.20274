Auditor model: claude-opus-5-5

# T2483 audit, round 1: L3d2b-1 (`RBM3D/Graph/BAMomentExpGen.lean`, targets 1-5; instances 10 (iv), (v)), Tue Oct 13 02:34:03 UTC 2026

Scope: under the pre-signed split, this delivery is L3d2b-1 only. Targets 6-10 (`BAMomentExpGenB`, instance (i) of target 9) are L3d2b-2 on `t/T2483b` and are not audited here.
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2483-audit1` (detached at `t/T2483` = 77f7be5b). Scratch: `$S` = `<scratchpad>/T2483/audit/`.

## 1. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Graph.BAMomentExpGen > $S/build.out 2>&1 ; echo exit=$? ; tail -1 ; grep -c error ; grep -c BAMomentExpGen.lean
exit=0
Build completed successfully (4066 jobs).
0          # error lines
0          # warning lines in the new file
$ lake env lean $S/audit_ax.lean | sed 's/^.* depends on axioms: //' | sort | uniq -c    # 16 public theorems incl. every target
  16 [propext, Classical.choice, Quot.sound]
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Graph/BAMomentExpGen.lean ; echo exit=$?
exit=1
$ git diff --stat main...t/T2483
 RBM3D/Graph/BAMomentExpGen.lean | 1147 +++++++++++++++++++++++++++++++++++++++
 1 file changed, 1147 insertions(+)
$ git diff --name-status $(git merge-base main t/T2483) main -- RBM3D | grep -v '^A'    # merged files changed since the base
M	RBM3D/Test/Axioms.lean        # not imported by the new file; everything else on main since the base is new files
```
Only a sole writable file is touched (1,147 lines, below the 2,000 stop line). No merged file is edited, so no frozen signature changes. `RBM3D.lean` is left for the hub.

## 2. Statements against the pins (script: check file Part 1+2 + `import RBM3D.Graph.BAMomentExpGen` + term-mode matches)
`$S/audit_match.lean` = `docs/tickets/checks/T2483-check.lean` lines 1-464, with the new import added and these theorems appended:
```
theorem a_1a : T2483_LWfgDBand := @LWfgD_bandFM
theorem a_1b : T2483_LWfgDUniv := @LWfgD_univ
theorem a_1c : T2483_LWfgDUnion := fun C n t ω D₁ D₂ h x y => LWfgD_union C n t ω h x y
theorem a_2a : T2483_LWMomentExpG = LWMomentExpG := rfl
theorem a_2b : T2483_MomentExpBand := LWMomentExp_iff_bandPin
theorem a_2c : T2483_BALWMomentExp = BALWMomentExp := rfl
theorem a_3 : T2483_MomentClosed := baLWMomentOfAnp_closed
theorem a_4a : T2483_ValWScale := BAMomentExp_valW_scale
theorem a_5eq : T2483_GtoAGRooted = BAGtoAGTRooted := rfl
theorem a_5 : ∀ d, T2483_GtoAGRooted d := baGtoAGTRooted_holds
theorem a_1d : <shape of 1 (d), verbatim from the check> := @LWfgD_baFMz
theorem a_4c : <shape of 4 (c), verbatim from the check> := fun hd Γ hN D Ψ C c r hG hC hc hS hSp hMP hoff hr Wt hWt ℓe a b hab hfar => BAMomentExp_scalemole ...
$ lake env lean $S/audit_match.lean > $S/match.out 2>&1 ; echo exit=$? ; grep -c error $S/match.out
exit=0
0
```
- The definitions `LWMomentExpG` and `BAGtoAGTRooted` are **`rfl`-equal** to the binding pins `T2483_LWMomentExpG` and `T2483_GtoAGRooted`, so hypotheses, quantifier order, constants, ranges and dimensions are identical. `BALWMomentExp` is `rfl`-equal to `T2483_BALWMomentExp`.
- Targets 1 (a)-(c), 2 (bridge), 3 and 4 (a) are proved in term mode against the pinned `Prop`s, with only `LWfgD` unfolded by defeq. The non-binding shapes 1 (d) and 4 (c) are met verbatim.
- Target 5: the order is `3 ≤ d → ∀ Λ κ > 0 → ∃ K₀ K₁ Kd C c` before `∀ L W g0 E t m`. So the constants depend on `(d, Λ, κ)` only and hold uniformly in `0 < g0 ≤ Λ` and `0 ≤ t < 1` (stop rule L40-C2 not fired). There is no `hext`. The roots `rep` have only the hypothesis `molOf (inr (rep c)) = c.1`, and the weight has `|Wt| ≤ 1` together with "`Wt ≠ 0` → root blocks in `Dm`", as pinned.
- Target 1 (e) `LWfg_split` and 4 (b)-(d) (no pin; names proposed by the ticket) have the band twin's shape: an exact three-way split; `|Wt| ≤ 1` weighted `L¹` bound, size claim and packed claim; the weight `Π_k 1_{Dm}` over `BAProvOut.π`, with `_abs` and `BAMomentExpGen_rep` from `BACoverBy.rep`.

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE '^(example|theorem|def|abbrev).*(BAAnpAuxG|BAShapePath)' RBM3D/Graph/BAMomentExpGen.lean
982:example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
$ grep -n "def BALWMomentOfAnp\|theorem baLWMoment_of_anp" -A2 RBM3D/Graph/BAMomentGenB.lean
362:def BALWMomentOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMoment d
370:theorem baLWMoment_of_anp
371-    (hb : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
```
- No new structure, class or inductive. The only statement defs are `LWfgD`, `LWMomentExpG`, `BALWMomentExp`, `BAMomentExp_wt` and `BAGtoAGTRooted`, and none of them hides an unproved premise.
- Target 3 discharges T2470's path binder `hb` with the merged `baPathBinder_holds` (T2469). Its residual antecedent `BAAnpAuxG d` is the ticket's authorized exact-type hypothesis (L3d1's pin), carried inside T2470's statement def.
- `BAShapePath` occurs in no statement here. `BAAnpAuxG` occurs only in the instance at line 982.
- No cycle: every dependency (`baLWMoment_of_anp`, `baPathBinder_holds`, `BAMomentGen_consts`, `BAAtom_*`, `BASizeClaim_*`) is merged. The `open private` uses read merged private lemmas and edit nothing.
- Target 5 is the general pinned statement, not a special case. Its proof (`baGtoAGTRooted_holds`, lines 887-896) is `BAMomentGen_consts` followed by the deterministic `BAMomentExpGen_G3Rooted` over the copied, rooted atom-first forest.
- External/eventual hypotheses: none in part A. The only `Eventually` in the file is `Eventually.of_forall` in the instance data (prove report (b)).

## 4. Compiled nonempty instances (all `example`s in the file; they compile in the build above)
```
$ grep -n "^example" RBM3D/Graph/BAMomentExpGen.lean | cut -c1-100
943:example (ω : sz0.SeqΩ) :
956:example (ω : sz0.SeqΩ) : LWfgD (bandFM sz0 (fun _ => 0)) 0 (1 / 2) ω {0} 0 1 = LWfD sz0 0 0 (1 / 2) ω {0} 0 1 :=
959:example (ω : sz0.SeqΩ) : LWfg (baFMz sz0 zSeq) 0 (1 / 2) ω 0 1 =
968:example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
974:example (h : BALWMomentExp 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
982:example (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
1075:example (ω : Ω 3 4 2) : ∃ o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2))),
1086:example (ω : Ω 3 4 2) : ∃ C c Kd : ℝ, ∃ o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2))),
1100:example (ω : Ω 3 4 2) : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
1117:example (ω : Ω 3 4 2) : ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
```
| target | instance | data | hypotheses left |
|---|---|---|---|
| 1 (a)-(e) | 943, 956, 959 | `d=3`, `sz0` at `n=0` (`L=4`, `W=32`), `t=1/2`, `x=0`, `y=1`; `Dm=univ`, `{0}`, `univ\{0}` (disjoint, both nonempty); `ℓ=1` split | none |
| 2 bridge | 968 | `lwMomentExp_holds 3` at band §12 data, `p=2`, `flow_z0` | `LWInit`, `LWLoopExp` (stochastic pins) |
| 2 BA reading | 974 | `flow_sz0`, `zSeq`, `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀=1/10`, window and `ℓ` bounds discharged | the pin `BALWMomentExp 3` (part B), `STInitialGT2gL`, `LWLoopExpgL` |
| 3 | 982 | `d=3`, `p=2`, `flow_sz0`, `LWPsiAll` at `(1/10,2,2,1,1)` discharged | `BAAnpAuxG 3` (L3d1), `STInitialGT2gL`, `LWLoop2gL` |
| 4 (a), (d) | 1075 | flow point `g0P, EP, t0P, m0P` (`L=4`, `W=2`, `flowP_real`, `0<t0P<1`), start term of `fxyPowGraph 2`, `Wt=Π_k 1_{0}` taking the values 1 and 0 | none |
| 4 (b) | 1086 | same, constants `BAMomentGen_consts 3 _ 10 (Im m_S)` | none |
| 4 (c) | 1100 | `G0` (BASymm1), `ℓ0` at block distance 1 > 5·(1/10) | none |
| 5 (v) | 1117 | `baGtoAGTRooted_holds 3`, `Λ=10`, start term, `rep` from `BACoverBy.rep`, `Dm={0}`, `A=1/8`, `r=1`, `R=card·r`, `ξ≡Ψ ≥ 1` | none |

Every deterministic hypothesis is discharged at concrete data. There is no `N = 0`, no `False` premise and no collapsed window. What stays a hypothesis is another gate's pin, as the ticket allows.

**Check of the root index of 5 (v), from the definitions** (the prover's report records that `0 < n_M` is not asserted in Lean): the start term is the head of the partition list, `BAGraph.partition = splitG.map packMerge`.
```
BAVocab:165-167  baSplitSolid (e :: es) = (baSplitSolid es).flatMap fun r => if e.circ then [(e :: r.1, r.2)] else [(Ǧ-edge :: r.1, r.2), (r.1, M-edge :: r.2)]
LocalRegular:1357 dotted := ... [⟨false, α_i, x⟩, ⟨false, α_i, y⟩]      LWVocab:157-159 adj = waved edge, or dotted edge with e.eq
BAAtom:65        shadow.waved = waved ++ mdot.map .. ++ psi.map ..
```
Element 0 is the all-`Ǧ` term, so it has no `M`-dotted edge. Every dotted edge has `eq = false`, so the merge is trivial. The shadow molecules are therefore `{x}, {y}, {α_1,β_1}, {α_2,β_2}`: `n_M = 2` internal molecules, and `rep` has a nonempty domain. The instance is not vacuous in the roots. This was derived by hand from the definitions and is not compiled; see observation O1.

## 5. Paper deltas
The two Lean/paper differences in part A have proposed entries in prove report (d):
- `T2483a` (rooted, weighted G3 at BA against `B:486-490` "repeat the argument of GtoAG");
- `T2483b` (the atom-first forest for every choice of roots).

Inherited forms that need no new entry:
- the deterministic G3 in place of `≺` (from `BAGtoAGT`, T2466);
- the band pin vocabulary of `LWMomentExpG` (from `LWMomentExp`, `LWtermExpG`).

Targets 1 (a)-(e), 3, 4 (a)-(d) are carrier and bookkeeping identities, with no paper statement difference.

## 6. Verdict per target
| target | verdict |
|---|---|
| 1 `LWfgD`, (a)-(e) | PASS |
| 2 `LWMomentExpG`, `LWMomentExp_iff_bandPin`, `BALWMomentExp` | PASS |
| 3 `baLWMomentOfAnp_closed` | PASS |
| 4 (a)-(d) weighted lemmas | PASS |
| 5 `BAGtoAGTRooted`, `baGtoAGTRooted_holds` | PASS |
| 10 (iv), (v) (and the instances of 2, 3, 4) | PASS |
| 6-10 | not in this delivery (L3d2b-2, `t/T2483b`) |

**Overall: PASS for L3d2b-1.** No dispatcher sign-off is needed for this part.

## 7. Observations (no RETURN)
- O1: instance 5 (v) does not state `0 < n_M` in Lean. §4 derives `n_M = 2` for the head partition term from the definitions. A compiled `Nonempty (LGraph.AuxIMol o.Q.g.shadow)` would make this machine-checked. Suggested for part B or a later tidy; it changes no statement.
- O2: the 4 (b) results `BAMomentExp_valW_norm_le`, `_claimSize` and `_pvalW_claim` use the ticket's `BAMomentExp_` naming pattern rather than the file stem `BAMomentExpGen_`. They are target-4 results that the ticket left unnamed, not helpers, and the name scan finds 0 hits on main 1e73b1b8 for all 25 public names.
- O3: the branch base is 650a122d. Since then main has only added new files and changed `Test/Axioms.lean`, which the new file does not import. The hub's full `lake build` at merge settles the rest.
