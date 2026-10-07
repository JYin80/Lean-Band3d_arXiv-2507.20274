Auditor model: claude-opus-5-5

# T2311 audit (round 1): LW-14e-3 simulation bridge, `RBM3D/Graph/LWExpSim.lean`

Written Wed Oct  7 09:41:04 UTC 2026 (`date -u`). Branch `t/T2311` = `2464793`, merge-base with `main` = `df14991`
(main is at `ed2bea2`; the extra commit touches only `docs/` and `docs/tickets/checks/T2310-check.lean`).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2311-audit1` (detached at `2464793`). Scratch files: scratchpad `T2311/`.

## 1. Build, forbidden tokens, files touched

```
$ lake build RBM3D.Graph.LWExpSim          # in the audit worktree
✔ [3884/3884] Built RBM3D.Graph.LWExpSim (8.0s)
Build completed successfully (3884 jobs).
$ grep -c '^error' build.log; grep LWExpSim build.log | grep -v 'depends on axioms'
0
✔ [3884/3884] Built RBM3D.Graph.LWExpSim (8.0s)
$ grep -n 'sorry\|admit\|native_decide\|^axiom\|^\s*axiom ' RBM3D/Graph/LWExpSim.lean; echo grep_exit=$?
grep_exit=1
$ git diff --name-only main...HEAD ; git diff main...HEAD -- RBM3D/Test/Axioms.lean | wc -l
RBM3D/Graph/LWExpSim.lean
       0
$ sed -n 6,7p RBM3D/Graph/LWExpSim.lean      # imports
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.LWExpCert
```
Only the sole writable file is touched; imports are exactly the two allowed merged modules
(`3c11598` T2307, `8096694` T2306); no `LWExpCertS0/S1`, no `RBM3D`, no `Probe`. No frozen signature touched (new file).

## 2. Statements against the pins

(a) Text check: every code block of the ticket, whitespace-normalised, occurs in the file.
```
$ python3 -I pintext.py docs/tickets/T2311.md RBM3D/Graph/LWExpSim.lean
True | def MNode.toP (N : MNode) (h : Function.Surjective N.ext) :
True | def Rel (N : MNode) (P : PGraph (Fin 2)) : Prop :=
True | def Cand.toR (N : MNode) (h : Function.Surjective N.ext) (c
True | def cPartitionX {a b : ℕ} (Γ : LGraph (Fin (a+1)) (Fin b)) (
True | def famsX {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin b)) (c : Ca
True | theorem fams_eq_famsX {a b : ℕ} (g : LGraph (Fin (a+1)) (Fin
True | def childrenX (N : MNode) (c : Cand N.a N.b) : List ((ℕ × ℕ)
True | def PartitionSim : Prop :=
True | def ChildrenSim : Prop :=
```
(b) Probe check: every declaration of `t/T2288:RBM3D/Probe/T2288Cert.lean` 455-612 (docstrings/comments stripped) in the file.
```
$ python3 -I probecmp.py probe.txt RBM3D/Graph/LWExpSim.lean
True | def MNode.toP ...            True | def Rel ...                  True | theorem Rel.scalingOrder_eq ...
True | theorem Rel.tgt_eq ...       True | theorem Rel.leaf_iff ...     True | theorem cands_spec ...
True | theorem lwSplit_map ...      True | theorem Rel.cand ...         True | def Cand.toR ...
True | theorem lwG5Cand_of_cands .. True | def cPartitionX ...          True | def famsX ...
True | theorem fams_eq_famsX ...    True | def childrenX ...            True | def PartitionSim ...
True | def ChildrenSim ...
False | def RelInvariance : Prop :=     (ticket 4, not a T2311 target)
False | def LeafOK (P : PGraph (Fin 2)) : Prop :=   (ticket 4, not a T2311 target)
```
(c) Lean check: section 2 of the dispatcher's `docs/tickets/checks/T2311-check.lean` (lines 57-120, the `axiom Cand.toR`
stub removed and replaced by the file's `RBM.Graph.LWCert.Cand.toR`) copied into `namespace RBM.Graph.T2311Audit`, then:
```
example : @T2311Audit.MNode.toP = @RBM.Graph.LWCert.MNode.toP := rfl
example : @T2311Audit.Rel = @RBM.Gauss.Sizes.Rel := rfl
example : @T2311Audit.cPartitionX = @RBM.Gauss.Sizes.cPartitionX := rfl
example : @T2311Audit.famsX = @RBM.Gauss.Sizes.famsX := rfl
example : @T2311Audit.childrenX = @RBM.Gauss.Sizes.childrenX := rfl
example : T2311Audit.PartitionSim = RBM.Gauss.Sizes.PartitionSim := rfl
example : T2311Audit.ChildrenSim = RBM.Gauss.Sizes.ChildrenSim := rfl
example : T2311Audit.PartitionSim := RBM.Gauss.Sizes.partitionSim
example : T2311Audit.ChildrenSim := RBM.Gauss.Sizes.childrenSim
$ lake env lean AuditPin.lean 2>&1 | grep -v 'depends on axioms'; echo exit=${pipestatus[1]}
RBM.Graph.LWCert.Cand.toR : (N : RBM.Graph.LWCert.MNode) →
  (h : Function.Surjective N.ext) →
    (c : RBM.Graph.LWCert.Cand N.a N.b) → c ∈ RBM.Graph.LWCert.cands N.g → RBM.Gauss.Sizes.RCand (N.toP h)
exit=0
```
Target theorems (file lines 1093, 1143, 1157): `theorem partitionSim : PartitionSim`, `theorem childrenSim : ChildrenSim`,
`theorem rel_self (N : MNode) (h : Function.Surjective N.ext) : Rel N (N.toP h)`. Both bridges are proved for all
arguments with no extra hypothesis; quantifier order and the `Forall₂` relations are the pinned ones (rfl above).

## 3. Hidden hypotheses, vacuity, cycles

- `MNode` (`LWExpCert.lean:46-50`) has data fields `a b g ext` only; `Rel` is a plain `∃ eE eI, …` with four list/ext
  equalities (pinned text); no structure carries a proof obligation beyond merged `PGraph.ext_surj`.
- `PartitionSim`/`ChildrenSim` are `∀`-statements whose hypotheses (`Function.Surjective N.ext`, `c ∈ cands N.g`) are
  satisfiable (instances in §4); the conclusion is a `Forall₂` between lists of length 163 / 550 at the instances,
  so it is not vacuous. `Rel` is not trivially true (it fixes the solid and dotted lists up to a vertex bijection).
- No cycle: imports are merged T2306/T2307 modules only; targets are theorems, not hypotheses. No external input
  (no `[YY_25]`, no `Θ`), so no limit check is required.
- Pinned design notes (not defects): `Rel` does not compare waved colours or `g.coeff`; `ChildrenSim` relates exponents and
  `Rel`, not coefficients. This is the pinned text (§2(c) rfl).

## 4. Compiled nonempty instances (file §10, built in §1)

- `partitionSim` at `lwExpSim_rootN := ⟨1, 3, LWG5Graph false false, ![0, 1]⟩` (`ext` onto by `decide`),
  `m = ⟨1/2, 1/3⟩` (non-real), with `example : (cPartitionX lwExpSim_rootN.g lwExpSim_rootN.ext).length = 163 := by decide +kernel`.
- `childrenSim` at `lwExpSim_instN := ⟨1, 1, lwExpTerm3_instGraph, ![0, 1]⟩` (`lwExpTerm3_instGraph : LGraph (Fin 2) (Fin 1)`,
  `LWExpTerm3.lean:2191`), `c := (cands _)[0]`, `hc := List.getElem_mem _`, with
  `example : (cands _).length = 1 ∧ (famsX _ _).length = 11 ∧ (childrenX _ _).length = 550 := by decide +kernel`.
- `rel_self` at `lwExpSim_rootN`.
Every hypothesis is discharged at concrete data; `a = 1`, `b ∈ {1, 3}`, no `N = 0`, empty index, or `False` premise.
Nondegenerate: PASS.

## 5. Axioms and registry

```
$ lake env lean AuditPin.lean | grep 'depends on axioms'
'RBM.Gauss.Sizes.partitionSim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.childrenSim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.rel_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.cands_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Rel.cand' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Rel.scalingOrder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Rel.tgt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.Rel.leaf_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwG5Cand_of_cands' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.fams_eq_famsX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwSplit_map' depends on axioms: [propext, Quot.sound]
'RBM.Graph.LWCert.Cand.toR' depends on axioms: [propext, Classical.choice, Quot.sound]
$ printf 'import RBM3D\nimport RBM3D.Graph.LWExpSim\n#assert_rbm_axioms\n' > Pre.lean; lake env lean Pre.lean; echo exit=$?
premises found by scanning: 148 (borrowed 1, owed 89, structural 41, refuted 6, superseded 11).
exit=0
```
The registry pre-check lists nothing for the new module, so leaving `RBM3D/Test/Axioms.lean` unchanged is what the
ticket asks for ("if pre-check lists none, add nothing").

## 6. Paper deltas

No paper content: both sides of each bridge are merged Lean definitions (ticket: "No paper delta"). No Lean/paper
statement difference arises; none proposed, none needed.

## 7. Observations (no statement, instance, build, axiom or paper-delta effect)

1. Namespaces: `MNode.toP` and `Cand.toR` are `RBM.Graph.LWCert.*`, everything else `RBM.Gauss.Sizes.*`. The ticket's
   targets line says `RBM.Gauss.Sizes`; the check file's comment says `RBM.Graph`. The `LWCert` placement is forced by the
   pinned field notation `N.toP h` (`N : RBM.Graph.LWCert.MNode`); the targets `partitionSim`, `childrenSim` are in
   `RBM.Gauss.Sizes` as ticketed. Ticket 4 should cite these full names.
2. `RBM.Gauss.Sizes.Rel` is ambiguous with Mathlib's `_root_.Rel` in bare-name commands under `open RBM.Gauss.Sizes`
   (prove report (d) 2); terms elaborate. Ticket 4 should write the full name where needed.
3. File length 1211 lines (estimate 650/800/1100, cap 1500): within cap.

## Verdict

| target | statement | hidden hyp / vacuity / cycle | instance | build / axioms | paper delta | verdict |
|---|---|---|---|---|---|---|
| `partitionSim : PartitionSim` | = pin (rfl) | none | root, 163 terms | ok / std 3 | none needed | PASS |
| `childrenSim : ChildrenSim` | = pin (rfl) | none | instGraph, 550 children | ok / std 3 | none needed | PASS |
| `rel_self` (optional) | as ticketed | none | root node | ok / std 3 | none needed | PASS |

Ticket T2311: **PASS**. No dispatcher sign-off needed.
