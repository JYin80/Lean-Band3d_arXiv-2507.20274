Auditor model: claude-opus-5-5

# T2313 audit (round 1) — S3-18b2a, `stOeqQtRoundPT''_holds` (n_ ≥ 2)

Written Thu Oct  8 01:24:53 UTC 2026 (`date -u`). Audited commit `5a73635` (branch `t/T2313`), detached worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2313-audit1`. Merge base with `main`: `e5f819c`.

## 1. Scope, frozen signatures, hygiene
```
$ git diff --patience --stat main...t/T2313
 RBM3D/Induction/QEndA.lean    |  89 +++++
 RBM3D/Induction/QEndB1.lean   | 712 +++++++++++++++++++++++++++++++++
 RBM3D/Induction/QEndGrid.lean | 897 ++++++++++++++++++++++++++++++++++++++++++
 3 files changed, 1698 insertions(+)
$ git diff --patience main...t/T2313 | grep -E '^\+' | grep -nE '\b(sorry|admit|native_decide)\b|^\+axiom ' ; echo hygiene-grep-exit=$?
hygiene-grep-exit=1
$ git diff --patience main...t/T2313 | grep -E '^\+(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance) ' | cut -c1-80   # output condensed: same-file private helpers joined with ' / '
theorem gridDriftQN_envelope' {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ
private abbrev σalt0 : Fin (0 + 1 + 1) → Bool := ![true, false]
theorem gridDriftQN_envelope'_instance :
def STXiRoundPT'' (E s t : ℕ → ℝ) : Prop :=
def STOeqQtRoundPT'' (d : ℕ) : Prop :=
private theorem altQFlow0_initQ ... / altQFlow0_Ylow_le_bootRHS / altQFlow0_core / altQFlow0_section
theorem stOeqQtRoundPT''_holds : ∀ d : ℕ, STOeqQtRoundPT'' d := by
theorem inst_OeqQtRoundPT'' :
private theorem altGrid_assembly' ... / altGrid_arith'
theorem altGridEndQN' :
theorem altGrid_instance' (m : ℕ) :
```
Only the three sole writable files; additions only (0 deleted lines), so every frozen signature (`altGridEndQN`,
`gridDriftQN_envelope`, `STXiRoundPT'`, `stOeqQtRoundPT'_holds`, ...) is untouched. Unpinned helpers are `private`; the
public instance theorems sit in the file-stem namespaces `QEndAInst`/`QEndGridInst`/`QEndB1Inst` (§3 (E)).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.QEndA RBM3D.Induction.QEndGrid RBM3D.Induction.QEndB1 > build.log 2>&1; echo exit=$?
exit=0
$ grep -E 'error|Build completed' build.log
Build completed successfully (3870 jobs).
$ grep -E '^warning' build.log | grep -v '100 character limit' | (QEndA|QEndGrid|QEndB1)   # none in the three files; only linter warnings elsewhere
$ grep -F 'depends on axioms' build.log | grep -E 'QEnd(A|Grid|B1)\.lean' | grep -F "''"   (new declarations)
RBM3D/Induction/QEndA.lean:2026:0: 'RBM.Ind.gridDriftQN_envelope'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndA.lean:2027:0: 'RBM.Ind.QEndAInst.gridDriftQN_envelope'_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndGrid.lean:3043:0: 'RBM.Ind.altGridEndQN'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndGrid.lean:3044:0: 'RBM.Ind.QEndGridInst.altGrid_instance'' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2034:0: 'RBM.Gauss.Sizes.STXiRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2035:0: 'RBM.Gauss.Sizes.STOeqQtRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2036:0: 'RBM.Ind.stOeqQtRoundPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM3D/Induction/QEndB1.lean:2037:0: 'RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT''' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statement against the pin (script)
Scratch file = `docs/tickets/checks/T2313-check.lean` (sections 1–4 verbatim) plus, inside `RBM.Gauss.Sizes.T2313Check`:
```
example (E s t : ℕ → ℝ) : STXiRoundPT''_pin sz E s t = RBM.Gauss.Sizes.STXiRoundPT'' sz E s t := rfl
example (d' : ℕ) : STOeqQtRoundPT''_pin d' = RBM.Gauss.Sizes.STOeqQtRoundPT'' d' := rfl
example : stOeqQtRoundPT''_holds_pin := RBM.Ind.stOeqQtRoundPT''_holds
#print axioms RBM.Ind.stOeqQtRoundPT''_holds / RBM.Ind.altGridEndQN' / RBM.Ind.gridDriftQN_envelope'
```
```
$ lake env lean pincheck.lean 2>&1 | grep -ciE error ; (exit code of lake env lean)
0
pincheck exit=0
'RBM.Ind.stOeqQtRoundPT''_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.altGridEndQN'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridDriftQN_envelope'' depends on axioms: [propext, Classical.choice, Quot.sound]
```
So `STXiRoundPT''`, `STOeqQtRoundPT''` are definitionally the pins and `stOeqQtRoundPT''_holds` has the pinned type
`∀ d, STOeqQtRoundPT'' d`. Textual diff against the frozen T2310 pin (only the threshold changes, as the ticket says):
```
$ diff <(def STXiRoundPT' body) <(def STXiRoundPT'' body)        # QEndB1.lean:83-95 vs :99-111
1c1
<   ∀ n_ p : ℕ, 3 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
---
>   ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
```
Primed successors 1–2 of the ticket (statements extracted from `theorem ... ` to `:= by`):
```
$ diff old(altGridEndQN) new(altGridEndQN')
1c1
< theorem altGridEndQN :
---
> theorem altGridEndQN' :
8c8
<     ∀ m : ℕ, 1 ≤ m →
---
>     ∀ m : ℕ,
$ diff old(gridDriftQN_envelope) new(gridDriftQN_envelope')
1c1
< theorem gridDriftQN_envelope {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m)
---
> theorem gridDriftQN_envelope' {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ)
```
Each successor is the original with exactly the `1 ≤ m` premise removed: strictly more general, same quantifier order,
same losses (`N^{ε₀}`, `(1+40d(m+1))6^{d(m+1)}`, `1000(1+d(m+1))²`), same windows and dimensions. The ticket's `τ'` formula is
internal (existential `τ'` in the conclusion); the ticket's suggested rephrasing of `hτ'dm` is a proof sketch, not a pin.
A compiled `example : T2302_altGridEndQN := ... altGridEndQN' ...` (QEndGrid) confirms the old pin follows.

## 4. Hidden hypotheses, vacuity, cycles
- `STXiRoundPT''`/`STOeqQtRoundPT''` are `def`s of `Prop` (no structure fields). `STIngR` (Step34Pins.lean:445) is the merged
  ingredient shape of T2310; its premises (`STKbound`, `STKward`, `STLK`, `STStep2Concl`) are other gates' pins.
- `stOeqQtRoundPT''_holds : ∀ d, ...` has no hypothesis; it depends only on merged modules plus the private copies in the
  same three files (Lean accepted the build, so no cycle). No external hypothesis is added.
- Non-vacuity of the pair index (`q.1.1 < q.1.2`, `q.1.1 = q.1.2`) is witnessed by the existing examples at QEndB1.lean:1949,1952.

## 5. Compiled nonempty instances (each endpoint)
| endpoint | instance | data | deterministic hypotheses |
|---|---|---|---|
| `stOeqQtRoundPT''_holds` | `inst_OeqQtRoundPT''` (QEndB1.lean:1975) + example (6) :1985 at `n_ = 2`, `p = 1`, `XL ≡ XLK ≡ 1`; (6') :2001 at `n_ = 3` | `d = 3`, `sz0`, `z0`, `s ≡ 0`, `t ≡ 1/16`, `C_d = 1` | all discharged via `inst_ing` (flow, `0 ≤ s < t ≤ lemT z`, `STCaseI`, `(con_st_ind)`); `STKbound`/`STKward` from the flow; `STLK`, `STStep2Concl`, pair controls `Ξ̂ ≺ 1` stay (other gates' pins) |
| `altGridEndQN'` | `altGrid_instance' (m)` (QEndGrid.lean:2845) and `example := altGrid_instance' 0` (:2879) | `sz0`, `κ = 1`, `𝔠 = 1/6`, `τ = 1/2`, `𝔡 = 1/10`, `E ≡ 0`, `(s,t) = (0,1/2)`, `v ≡ 1/2`, levels `≡ 1`, `ε₀ = 1/10`, `D₁ = 1`, `m = 0` | all discharged; grid `agK C_K` with its bounds; `.exists` on the eventual conclusion |
| `gridDriftQN_envelope'` | `gridDriftQN_envelope'_instance` (QEndA.lean:1535) | `sz0`, `κ = 1`, `τ_K = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `m = 0`, `σ = (true,false)` | all discharged; `STKbound` from merged `stKbound_holds` |
None is degenerate: `m = 0` is the new nondegenerate case (loop length 2, `d = 3`, `K ≡ 4 ≠ 0`, `s < v < 1`, `s < t`).
The example (6) applies the conclusion at the concrete `n_ = 2`, the case the ticket adds. Same shape as the accepted T2310 instances.

## 6. Paper deltas
| Lean/paper difference | coverage |
|---|---|
| per-time `PrecPT` over pairs, constant controls `XL, XLK`, `B_u^{1/6}` (paper `lem:STOeq_Qt`, `3_5_Loop_Hierarchy.tex:1364-1365`, sup over `v`) | `T2310a` (T2310 report (d), audit line 106-107), unchanged |
| threshold: paper `n ≥ 2`; Lean now `2 ≤ n_` (closes the T2310 `3 ≤ n_` gap) | `T2313a` (prove report (d)) |
| ticket sketch vs proof (private `m = 0` copies, `STbootRHS 1`) — no statement change | `T2313b` (informational) |
```
$ grep -n -o 'label{lem:STOeq_Qt}\|for any fixed $n\\ge 2$ and $p\\ge 1$' paper/tex/3_5_Loop_Hierarchy.tex | head -2
1364:label{lem:STOeq_Qt}
1365:for any fixed $n\ge 2$ and $p\ge 1$
```

## 7. Observations (no RETURN)
- The prove report's section (a) lists lower-bound uses beyond the ticket's file plan (`altQFlow_initQ/core/section`); the
  prover handled them by private copies in the sole writable files; no statement affected.
- QEndGrid.lean grows by 897 lines of near-duplicate text (originals frozen); maintenance only.
- The ticket's formula hint "`τ' * d * (m + 1) - τ' * d ≤ ε₁`" was not used; the field keeps its type `τ' * (d * m) ≤ ε₁`,
  internal to `altGrid_arith'`, no pinned statement involved.

## 8. Verdicts
| target | verdict |
|---|---|
| `STXiRoundPT''` (def, pin) | PASS |
| `STOeqQtRoundPT''` (def, pin) | PASS |
| `stOeqQtRoundPT''_holds` | PASS |
| `altGridEndQN'` (primed successor) | PASS |
| `gridDriftQN_envelope'` (primed successor) | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
