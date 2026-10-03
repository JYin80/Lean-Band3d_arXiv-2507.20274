Auditor model: claude-opus-5-5

# T2020 audit (round 1) — KL3 `KLK_isKLoop`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2020-audit1`, detached at `t/T2020` = `1133530`; merge base with `main` = `5d3b282`; `main` = `58bedae`. Audit time: Sat Oct  3 04:21:47 UTC 2026 (from `date -u`, axioms run).

## Target `RBM.Loop.KLK_isKLoop` — verdict PASS

### 1. Statement against the pin (script diff)
```
$ sed -n '/^def KLisKLoopPin : Prop :=/,/fun t I => KLK/p' docs/tickets/checks/T2020-check.lean | tail -n +2 | sed 's/^ *//' > pin.txt
$ sed -n '/^theorem KLK_isKLoop :/,/:= by$/p' RBM3D/Loop/KLTreeDeriv.lean | tail -n +2 | sed 's/ := by$//; s/^ *//' > thm.txt
$ diff pin.txt thm.txt && echo IDENTICAL; cat thm.txt
IDENTICAL
∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
IsKLoop d L W g (mSigma E) (Set.Ico 0 1) (fun t I => KLK d L g W E t I)
```
The merged (frozen) definitions the statement unfolds to, `RBM3D/Loop/TreeRep.lean:142-162`:
```
treeEqRhs K I = (W:ℂ)^d * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a, ∑ b,
                  K (I.cutGlueL k l a) * SB d L g a b * K (I.cutGlueR k l b)
MLoop m I     = ((W:ℂ)^d)⁻¹ ^ (I.length - 1) * (I.σ.map m).prod * (if ∀ x ∈ I.a, ∀ y ∈ I.a, x = y then 1 else 0)
IsKLoop m T K = (∀ t ∈ T, ∀ I, I.WF → 2 ≤ I.length → HasDerivAt (fun s => K s I) (treeEqRhs d L W g (K t) I) t)
              ∧ (∀ I, I.WF → 2 ≤ I.length → K 0 I = MLoop d L W m I)
              ∧ (∀ t ∈ T, ∀ s a, K t ⟨[s], [a]⟩ = m s)
```
Against the paper (`paper/tex/1_2_Intro_model_result.tex:986-1011`, `Def_Ktza`): `(pro_dyncalK)` sums `1 ≤ k < l ≤ n` with factor `W^d` — Lean `k ∈ [1,n]`, `l ∈ (k,n]`, factor `(W:ℂ)^d`: same. `(eq:initial_K)` with the RBM simplification `W^{-(k-1)d} ∏ m(σ_i) 1(a_1=…=a_k)` — `MLoop`: same; `k = 1` is covered by clause 3 at `t = 0 ∈ Ico 0 1` (`M^{(1)} = m(σ)`). `𝒦^{(1)} = m(σ)`: clause 3. Time set: paper `[0,1]`, Lean `Set.Ico 0 1` (paper-delta candidate, §5). Clause 1 is a two-sided `HasDerivAt` (stronger than the one-sided derivative at `t = 0`). Parameters `d` free (no `3 ≤ d`: more general), `3 ≤ L`, `1 ≤ W`, `|E| < 2`, `g` free; parameter order as pinned. The paper's "unique solution" is the separate pin KL4 (`KLuniquePin`); this ticket's target is the existence half, exactly as pinned.

### 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "^(noncomputable )?(def|abbrev|structure|class).*Prop" RBM3D/Loop/KLTreeDeriv.lean; echo exit=$?
exit=1
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev|instance)" RBM3D/Loop/KLTreeDeriv.lean | grep -v private
1049:theorem KLK_isKLoop :
1080:theorem KLTreeDerivInst_isKLoop :
1085:theorem KLTreeDerivInst_ode_two :
1092:theorem KLTreeDerivInst_ode_three :
1101:theorem KLTreeDerivInst_ode_four :
1110:theorem KLTreeDerivInst_ode_zero :
1119:theorem KLTreeDerivInst_init_const :
1129:theorem KLTreeDerivInst_init_nonconst :
1144:theorem KLTreeDerivInst_one :
$ grep -n "^import" RBM3D/Loop/KLTreeDeriv.lean
6:import Mathlib.Data.List.GetD
7:import RBM3D.Loop.KLCut
```
No new `Prop`, no structure; the theorem has only the three numeric hypotheses of the pin. `IsKLoop` is the registered structural definition (DECISIONS §16), not an assumed hypothesis. Only merged modules are imported (KLCut → KLTree → TreeRep), so no cycle. Non-vacuity: `KLTreeDerivInst_init_const` evaluates `𝒦_0` to `i/64 ≠ 0` and clause 1 is instantiated at `t ∈ {0, 9/10}` for loops of length 2, 3, 4. No external hypothesis, so no limit check is needed.

### 3. Compiled nonempty instance (file lines 1080-1149)
```
theorem KLTreeDerivInst_isKLoop :
    IsKLoop 3 5 2 (1 / 2) (mSigma 0) (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) :=
  KLK_isKLoop 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
theorem KLTreeDerivInst_ode_two : HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s ⟨[true, false], [0, 1]⟩)
      (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I) ⟨[true, false], [0, 1]⟩) (9 / 10) :=
  KLTreeDerivInst_isKLoop.1 (9 / 10) ⟨by norm_num, by norm_num⟩ _ rfl (le_refl 2)
theorem KLTreeDerivInst_init_const :
    KLK 3 5 (1 / 2) 2 0 0 ⟨[true, false, true], [0, 0, 0]⟩ = Complex.I / 64
theorem KLTreeDerivInst_one : KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ = Complex.I
```
Data are the ticket's (`d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`): 125 blocks, `W^d = 8`, every hypothesis (`3 ≤ 5`, `1 ≤ 2`, `|0| < 2`) is discharged by `norm_num`, and no example keeps a hypothesis. Each of the three clauses is applied at a nondegenerate point: `t = 9/10` and `t = 0`, loops of length 2/3/4 with distinct labels, constant and non-constant labels at `t = 0`. Not degenerate.

### 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Loop.KLTreeDeriv 2>&1 | grep -E "error|warning|sorry|Build completed|✔|✖"
✔ [3239/3239] Built RBM3D.Loop.KLTreeDeriv (7.7s)
Build completed successfully (3239 jobs).
$ lake env lean RBM3D/Loop/KLTreeDeriv.lean; echo exit=$?      # direct re-elaboration, no output
exit=0
$ lake env lean ax.lean     # #print axioms of all 9 public names
'RBM.Loop.KLK_isKLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_isKLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_ode_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_ode_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_ode_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_ode_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_init_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_init_nonconst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLTreeDerivInst_one' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|unsafe|implemented_by|extern" RBM3D/Loop/KLTreeDeriv.lean
67:set_option linter.style.longLine false
$ git diff --stat main...t/T2020; git log --oneline main..t/T2020
 RBM3D/Loop/KLTreeDeriv.lean | 1153 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1153 insertions(+)
1133530 T2020: KLK_isKLoop, the tree sum solves Def_Ktza (KL3)
$ for n in <9 public names>; do git grep -c "\b$n\b" main -- RBM3D | wc -l; done   # name clash on main
0 0 0 0 0 0 0 0 0   (every name: 0 files on main)
```
Only the sole writable file is touched (new), so no frozen signature changes. The `set_option` is a style linter only. Public names besides the pinned `KLK_isKLoop` carry the file-stem prefix `KLTreeDerivInst_` (§3 (E)); every other declaration is `private`.

### 5. Paper deltas
```
$ grep -n "T2020a" docs/reports/T2020-prove.md | cut -c1-120
220:- `T2020a` (typo, the same as `T2004d`, signed in `docs/DECISIONS.md:142` and absent from `docs/paper-deltas.md`: ...
$ grep -n "T2004d" docs/DECISIONS.md | cut -c1-40
142:- **签字接受的 paper-delta 候选**：T2004a（...   (contains "T2004d（笔误：`Def_Ktza` 与 `Θ_t` 定义里的 `t ∈ [0,1]` 应为 `[0,1)`）")
$ grep -n "^## D6" docs/paper-deltas.md
50:## D6 · 只形式化随机带状矩阵模型的传播子
```
Lean/paper differences: (i) `t ∈ [0,1]` → `Set.Ico 0 1`: proposed as `T2020a` (and already signed off as T2004d, DECISIONS:142). (ii) The `M`-loop in its RBM-simplified form: covered by the existing D6 and by the `MLoop` docstring of the merged frozen definition. (iii) General `d` and two-sided derivative at `t = 0`: stronger than the paper, not a restriction. (iv) Uniqueness is not part of this pin (KL4). Coverage is complete.

## Observations (no effect on the verdict)
- O1. The branch base is `5d3b282`; `main` has since moved to `58bedae` (T2021 merge and the dispatcher commit). The diff touches one new file and does not conflict. The hub's full `lake build` at merge is the binding check; the prover's report (b1) shows a full build exit 0 on the branch base.
- O2. The audit build reports "Built" in 7.7 s on the cloned cache; a direct `lake env lean` re-elaboration of the file also exits 0 with no output (above), so acceptance does not rest on a stale olean.
- O3. I did not repeat the port-fidelity diff against RBM2D `c9a24cf` (report b6). The audit is statement-centred, and the only public ported statement is `KLK_isKLoop`, which is checked against the pin directly (§1).

## Verdict
| Target | Verdict |
|---|---|
| `RBM.Loop.KLK_isKLoop` | PASS |

No dispatcher sign-off needed.
