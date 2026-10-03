Auditor model: claude-opus-5-5

# T2008 audit (round 1) — KL1 `RBM3D/Loop/KLTree.lean`

Time: Sat Oct  3 00:14:50 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2008-audit1`, detached at `t/T2008` = `ee4c726`.
`$S` = the auditor's scratchpad directory.

## 1. Statements

### Item 1: pinned text (probe `64b58eb:RBM3D/Probe/T2004Pins.lean` lines 41-501)
```
$ git show 64b58eb:RBM3D/Probe/T2004Pins.lean > $S/probe.lean; sed -n 41,501p $S/probe.lean > $S/p41.lean
$ awk '/^namespace RBM.Loop/{f=1} f' RBM3D/Loop/KLTree.lean | sed -n 1,461p > $S/mine.lean; diff $S/p41.lean $S/mine.lean; echo "diff exit=$?"
diff exit=0
```
Imports are `RBM3D.Loop.Primitive`, `RBM3D.Loop.GLoop` (probe: `RBM3D`); the pinned text compiles unchanged under them (build, §4).
`KLward_two` covers both charge orders via `(s : Bool)` and the loop `⟨[s, !s], [a₁, x]⟩` (file line 459). Pinned verbatim: **PASS**.

### Instances against the probe's section 9 (statement and proof blocks)
```
KLinstPar        probe: 13 new: 13 identical
KLinstσ          probe:  1 new:  1 identical
KLinsta          probe:  1 new:  1 identical
KLinst_scales    probe: 10 new: 10 identical
KLinst_two       probe:  5 new:  5 identical
KLinst_three     probe:  8 new:  8 identical
KLinst_ward_two  probe:  6 new:  6 identical
KLinst_Kpi       probe:  6 new:  6 identical
```

### Item 2: ports from RBM2D `c9a24cf`
RBM2D `SigmaPi_empty_symm` (`Kcal.lean:759-763`):
```
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E : ℝ, |E| < 2 → ∀ t ∈ Set.Ico (0 : ℝ) 1,
    ∀ (n : ℕ) [NeZero n] (σ : Fin n → Bool) (d₁ : Z2 L) (s : Fin n → Z2 L), s 0 = 0 →
      SigmaPi L (mSig E) t σ ∅ (fun i => d₁ + s i)
        = SigmaPi L (mSig E) t σ ∅ (fun i => d₁ - s i)
```
Lean (`KLTree.lean:776-780`):
```
theorem KLSigmaPi_empty_symm (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (σ : Fin n → Bool) (d₁ : Zd d L)
    (s : Fin n → Zd d L) (_ : s 0 = 0) :
    KLSigmaPi d L g (mSigma E) t σ ∅ (fun i => d₁ + s i)
      = KLSigmaPi d L g (mSigma E) t σ ∅ (fun i => d₁ - s i)
```
Same hypotheses and quantifier order after `Z2 L → Zd d L`, `mSig → mSigma`, `Θ → Theta d L g`. **PASS**.
Laminar API: the 27 declarations of RBM2D `TreeRep.lean:185-413` (all `private` there) appear as `KL`-prefixed public declarations at `KLTree.lean:506-728` (plus `KLwholeP_mem_nodes`, line 503, from `Kcal.lean:103`) (names listed by `grep -n '^theorem'`; same binders, `IsTSP → KLIsTSP`). These are API, not endpoint theorems.
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Loop/TreeRep.lean RBM2D/Loop/Kcal.lean | tail -1
 2 files changed, 63 insertions(+), 317 deletions(-)
```

### Item 3: kernel-generic successors (ticket mathematics)
```
noncomputable def treeEqRhsS (S : Matrix (Zd d L) (Zd d L) ℂ) (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  ((W : ℂ) ^ d) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a, ∑ b, K (I.cutGlueL k l a) * S a b * K (I.cutGlueR k l b)
noncomputable def MLoopM (m : Bool → ℂ) (R : List Bool → List (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) * (I.σ.map m).prod * R I.σ I.a
def IsKLoopS (S) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I, I.WF → 2 ≤ I.length → HasDerivAt (fun s => K s I) (treeEqRhsS d L W S (K t) I) t) ∧
  (∀ I, I.WF → 2 ≤ I.length → K 0 I = M I) ∧ (∀ t ∈ T, ∀ s a, K t ⟨[s], [a]⟩ = m s)
theorem treeEqRhs_eq_treeEqRhsS (K) (I) : treeEqRhs d L W g K I = treeEqRhsS d L W (SB d L g) K I := rfl
theorem KLMLoop_eq_MLoopM (m : Bool → ℂ) : MLoop d L W m = MLoopM d L W m (KLallEq d L) := rfl
theorem IsKLoop_iff_IsKLoopS (m) (T) (K) :
    IsKLoop d L W g m T K ↔ IsKLoopS d L W (SB d L g) m (MLoopM d L W m (KLallEq d L)) T K := Iff.rfl
```
(abridged from `KLTree.lean:809-848`; binder types elided only where shown in the line above.)
`S` arbitrary; `IsKLoopS` takes arbitrary initial data `M` (`LoopIdx` has exactly the fields `σ : List Bool`, `a : List α`, `TreeRep.lean:65-69`, so `R I.σ I.a` is also an arbitrary function of `I`); the three equalities hold definitionally, so the merged frozen `treeEqRhs`, `MLoop`, `IsKLoop` are recovered exactly. `git diff main...HEAD -- RBM3D/Loop/TreeRep.lean | wc -l` → `0` (frozen file untouched). **PASS**.

## 2. Vacuity, hidden hypotheses, cycles
- No `structure` declared in the new code except the pinned `KLPar` (verbatim probe text, parameter range only; no target takes `KLPar`/`KLPT`/`KLDecay`..`KLZero` as a hypothesis).
- Every target's hypotheses are explicit binders (`3 ≤ L`, `1 ≤ W`, `|E| < 2`, `t ∈ [0,1)`, `3 ≤ n`, `s 0 = 0`), all discharged in §3.
- No external hypothesis; dependencies are merged modules only (`import RBM3D.Loop.Primitive`, `RBM3D.Loop.GLoop`); no cycle (new leaf module).

## 3. Compiled nonempty instances (d = 3, L = 5 (125 blocks), W = 2, g = 1/2, E = 0, t = 9/10)
| target | instance (`KLTree.lean`) | data / discharged hypotheses |
|---|---|---|
| `KLK_two` | `KLinst_two` | `(+,-)`, labels `0,1` |
| `KLK_three` | `KLinst_three` | `(+,-,+)`, labels `0,1,2` |
| `KLward_two` | `KLinst_ward_two` | `hL, hW, hE, ht` by `norm_num`; `s = true`, `a₁ = 0` |
| `KLK_eq_sum_Kpi` | `KLinst_Kpi` | `n = 4` (`3 ≤ 4` by `norm_num`), `(+,-,+,-)`, labels `0..3` |
| `KLKpi_eq_sum_SigmaPi` | `KLinst_Kpi_SigmaPi` | `n = 4`, `π = ∅` |
| `KLSigmaPi_empty_symm` | `KLinst_SigmaPi_symm` | `hL, hE, ht` by `norm_num`, `s 0 = 0` by `rfl`; `d₁ = 1`, `s = (0,1,2)` |
| `KLK_one`, `KLK_two_eq_kTwo` | `KLinst_one_two_kTwo` | `(+)`; `(+,-)`, labels `0,1` |
| `KLgen_loopOf` | `KLinst_gen_loopOf` | `n = 4` |
| `KLPar` | `KLinstPar : KLPar 1 1` | every field by `norm_num` |
| `treeEqRhs_eq_treeEqRhsS` | `KLinst_treeEqRhsS` | `K = KLK`, 3-loop `(+,-,+)` |
| `KLMLoop_eq_MLoopM` | `KLinst_MLoopM` | 3-loop |
| `IsKLoop_iff_IsKLoopS` | `KLinst_IsKLoopS` | `K = KLK`, `T = [0,1)`, `m = mSigma 0` |
Every instance is a `theorem`/`def` with no hypotheses, compiled in the module (build §4). No `N = 0`, empty index, collapsed window or `False` premise. The ticket's required list (five probe instances + two for item 3) is complete.

## 4. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Loop.KLTree 2>&1 | grep -E "error|warning|Build completed"; echo exit=$?
Build completed successfully (3236 jobs).
exit=0
$ # names: every `theorem|def|lemma|structure|abbrev|instance` head of the file (98 entries; one is the
$ # anonymous `instance (J …)` head, which produced the 2 parse-error lines of $S/Ax.lean, not a declaration)
$ lake env lean $S/Ax.lean | sed -E 's/.*depends on axioms: //' | sort | uniq -c
  82 [propext, Classical.choice, Quot.sound]
   9 [propext, Quot.sound]
   1 [propext]
   5 '<name>' does not depend on any axioms   (KLArcLe, KLarcWidth, KLInArc, KLloopOf, KLsigAlt)
$ grep -E "\.(IsKLoop_iff_IsKLoopS|treeEqRhs_eq_treeEqRhsS|KLMLoop_eq_MLoopM|KLK_one|KLK_two|KLK_three|KLK_two_eq_kTwo|KLgen_loopOf|KLK_eq_sum_Kpi|KLKpi_eq_sum_SigmaPi|KLtreeValW_eq_sum_selfW|KLSigmaPi_empty_symm|KLward_two)'" ax.txt
'RBM.Loop.IsKLoop_iff_IsKLoopS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLgen_loopOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_eq_sum_Kpi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_two_eq_kTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLKpi_eq_sum_SigmaPi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLMLoop_eq_MLoopM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLSigmaPi_empty_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLtreeValW_eq_sum_selfW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLward_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.treeEqRhs_eq_treeEqRhsS' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^private axiom" RBM3D/Loop/KLTree.lean; echo "grep exit=$?"
grep exit=1
$ git diff --name-status main...HEAD
A	RBM3D/Loop/KLTree.lean
$ # name clash: each of the 97 public names grepped (-w) in every other RBM3D .lean file and RBM3D.lean
clashes=0 of 97
$ # public names without the KL/KLTree_ prefix
IsKLoop_iff_IsKLoopS  IsKLoopS  MLoopM  treeEqRhs_eq_treeEqRhsS  treeEqRhsS     (all five named by the ticket)
```
**PASS**.

## 5. Paper deltas
- `KLK` defined by the tree sum `(eq_Ktree)` (also at `n = 3`, the star, equal to `(Kn3sol)` by `KLK_three`): definition choice decided in DECISIONS §15 (line 139, option B); `(pro_dyncalK)` and uniqueness are later theorems (KL3, KL4), so no statement of this ticket differs from the paper.
- `KLDiffOne`/`KLDiffTwo` range `|r| ≤ c|a|`: T2004c; `KLPar` `g ≤ gmax`: T2004b; `t ∈ [0,1)`: T2004d (all signed, DECISIONS §15 line 141). Cited, not re-proposed: covered.
- Item 3 successors generalise merged Lean definitions (no paper statement); `KLSigmaPi_empty_symm` is the RBM2D port with identical hypotheses. No new candidate needed.

## 6. Observations (no RETURN)
- O1. Prove report (d) says T2004a-e "cover the definition choice"; per DECISIONS §15 the definition choice is the decision at line 139, not one of T2004a-e. Coverage is unaffected.
- O2. RBM2D `TreeRep.lean:415-540` (`gval`, `gval_congr`, `sum_perm4`, `gval_split`, `treeValW_eq_gval`; all `private` helpers) is inside the design row's line range but not ported. The ticket's item 2 sentence names "the laminar API, the molecule first stage and `SigmaPi_empty_symm`", and no pinned statement depends on them. KL3 (ODE for the tree sum) will need to port them.
- O3. `KLtreeValW_eq_sum_selfW` has no separate `example`; it has no hypotheses (identity for all `F, a, M, E`) and is applied at `KLTree.lean:443` inside `KLKpi_eq_sum_SigmaPi`, whose instance `KLinst_Kpi_SigmaPi` compiles. It is not on the ticket's instance list.
- O4. `KLinst_ward_two` instantiates `s = true` only; the theorem is universally quantified in `s`, so `s = false` is the same statement.

## Verdict
| target | verdict |
|---|---|
| Item 1 (probe sections 1-5, verbatim incl. `KLK`, `KLK_one/two/three`, `KLK_two_eq_kTwo`, `KLgen_loopOf`, `KLPar`, `KLPT` shapes, molecule layer, `KLK_eq_sum_Kpi`, `KLtreeValW_eq_sum_selfW`, `KLKpi_eq_sum_SigmaPi`, `KLward_two`) | PASS |
| Item 2 (laminar API port, `KLTheta_reflect`, `KLselfW_reflect`, `KLSigmaPi_empty_symm`) | PASS |
| Item 3 (`treeEqRhsS`, `MLoopM`, `IsKLoopS` and the three equalities) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
