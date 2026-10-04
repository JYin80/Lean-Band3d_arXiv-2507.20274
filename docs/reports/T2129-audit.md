Auditor model: claude-opus-5-5

# T2129 audit, round 1 (S3-06 `Induction/KDecay`): Sun Oct  4 11:42:59 UTC 2026

Audited commit `efd240c` (detached worktree `RBM3D-wt/T2129-audit1`). Pin: ticket target 1 as amended by Amend 1
(DECISIONS §37); targets 2 and 3 as in the ticket body and Amend 1. There is no Lean pin text in
`docs/tickets/checks/T2129-check.lean` (only `#check` lines), so target 1 is diffed against the ticket's mathematics, written as
RBM2D `KcalDecay` at `c9a24cf` with the ticket's `d`-dimensional substitutions plus Amend 1.

## 1. Statements

```
$ python3 scratchpad/T2129/pindiff.py   # RBM2D HierVocab.lean@c9a24cf KcalDecay -> {κ,gmax>0; Z2 L->Zd d L; (W*L)^d=N, N^𝔠≤W, 3≤L
                                        #  (ticket order); ∀ g, 0<g≤gmax; ellT L g u; KLmaxDist d L; KLK d L g W E u (KLloopOf d L σ a);
                                        #  Amend 1: ∀ Q>0 before ∀ᶠ N, ((W:ℕ):ℝ)^(-Q) ≤ g next to g ≤ gmax}  vs  KDecay.lean:782
RBM2D KcalDecay@c9a24cf + ticket substitutions + Amend 1  vs  Lean STKcalDecay: token diff lines = 0
```
Signatures used (merged): `KLK (W) (E t) (I)` with section variables `d L g` (`Loop/KLTree.lean:145`), `KLloopOf σ a` (:149),
`KLmaxDist a = sup zdistD (a i - a j)` (:372, the `l¹` distance of DECISIONS §15), `ellT L g t` (`Defs/Params.lean:32`).
Quantifier order: `κ gmax 𝔠 k τ D Q` all before `∀ᶠ N`; `L W g E u σ a` after. Matches the ticket.

`stKcalDecay_holds {d} (hd : 3 ≤ d) : STKcalDecay d` (KDecay.lean:798): exactly the pinned conclusion; `3 ≤ d` is §36's form.
Its proof opens `(KLPT_holds hd hκ hg).decay/.short` (merged T2125, `Loop/KLFinal.lean:143`) and no other hypothesis.

Target 2 (KDecay.lean:1062, :1081), against the merged pins `STKbound` (`Induction/Defs.lean:174`), `STKward` (`Step34Pins.lean:229`)
and `stKbound_holds`/`stKward_holds` (`Loop/KLFinal.lean:243,260`):
- Same hypotheses as `st*_holds` (`3 ≤ d`, `0<κ`, `0<gmax`, `SizeTendsto`, `∀ᶠ |E n| ≤ 2-κ`, `∀ᶠ 0 < lam ≤ gmax`), plus the
  window `∀ n, 0 ≤ s n`, `s n ≤ t n`, `t n < 1`.
- The conclusion is the same `Prec` with the index `U n` extended by `TimeIcc s t n`, and `τ n` replaced by `(p.1 : ℝ)` on both
  sides. This is `Prec` (the union over `u` is inside `P`), which is at least as strong as the per-time form `PrecPT`.
- Matches the ticket ("forms over `TimeIcc s t`, `u ∈ [s n, t n]`").

Target 3:
- `KDecay_sum_tailT_le` (:1241) states `Σ_{a : Zd d L} tailT d L g t (zdistInf a) ≤ KDecay_tailC d / (1 - t)` for
  `2 ≤ d`, `[NeZero L]`, `0 ≤ g`, `t < 1`. That is the ticket's `C_d (1-t)⁻¹`, uniform in `L, g, t`, over a larger range
  (`g ≥ 0`, any `t < 1`, `d ≥ 2`). The distance is `|·|_∞` as Amend 1 fixes (T2129b).
- `stSumTwoLoop` (:1262) and `stSumTwoLoop_exists` (:1339) give the second `≺` of `(eq:sumtwoloop)` (`3_5:1069`) as a deterministic
  inequality: `ρ^{C_d} Bctl^{1/5} Σ_{a₂} 𝒯_t(|a₁-a₂|_∞) ≤ C Bctl^{1/6} η_t⁻¹`, eventually in `n` and uniform in `a₁`.
  - `Bctl n t = W^{-d} Bparam … t 0` (`Defs/Sizes.lean:214`), so `Bctl` is the paper's `W^{-d}B_{t,0}`.
  - `_exists` has the order `∀ C_d > 0, ∃ 𝔠d ∈ (0, 1/100], ∃ C > 0, ∀ sz s t E`, which is T2041e's `∀ C_d ∃ 𝔠_d`.
  - Extra eventual hypotheses: `t n < 1`, `|E n| < 2`, `0 ≤ lam n`. They are covered by T2129c.
  - The paper's `+W^{-D}` and first `≺` are not in this ticket (T2129c).

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom |set_option|opaque|structure|class " RBM3D/Induction/KDecay.lean
47:set_option linter.style.longLine false
48:set_option linter.unusedSectionVars false
$ grep -n "^import" RBM3D/Induction/KDecay.lean
6:import RBM3D.Loop.KLTree     7:import RBM3D.Loop.KLIndStepA   8:import RBM3D.Loop.KLFinal   9:import RBM3D.Defs.Tail
10:import RBM3D.Defs.RadialSum  11:import RBM3D.Defs.Params      12:import RBM3D.Induction.Defs 13:import RBM3D.Induction.Step34Pins
14:import RBM3D.Green.Pins
```
- No new structure or class, so no hypothesis is hidden in a field. Every import is a merged module (no cycle; the module is not
  imported by any of them).
- `STKcalDecay` is a `def … : Prop`, concluded by `stKcalDecay_holds`; no theorem in the file takes it as a hypothesis.
- Target 1's premises are jointly satisfiable at a nondegenerate point (instance below, with the far premise proved for every
  `n`), so the pin is not vacuous.
- No external hypothesis is introduced. The Amend-1 premise `W^{-Q} ≤ g` is discharged from `sz.Admissible` (`WO`) in
  `inst_stKcalDecay_admissible`, with `Q = d/2`.

## 3. Compiled nonempty instances (same file; all compile, see §4)
| endpoint | instance | data | deterministic hypotheses |
|---|---|---|---|
| `stKcalDecay_holds` | `inst_stKcalDecay` (:940) | `d=3`, `κ=1/10`, `gmax=1`, `𝔠=1/10`, `k=3`, `τ=D=1`, `Q=3/2`; `L=W=n+3`, `N=((n+3)²)³`, `g=1/2`, `E=0`, `u=3/4`, `σ=(+,-,+)`, `a=(0,(h,h,h),0)`, `h=⌊L/2⌋` | all discharged in the proof (`hbw : N^{1/10} ≤ W`, `3 ≤ L`, `W^{-3/2} ≤ 1/2`, `|0| ≤ 19/10`, `0 ≤ 3/4 < 1`); the far premise `ellT·W ≤ maxDist` is proved for **every** `n` (`instA_far`: `ellT=1`, `maxDist = 3⌊(n+3)/2⌋ ≥ n+3`); the conclusion holds eventually in `n` (`∀ᶠ` extracted along `N → ∞`) |
| `stKcalDecay_holds` (consumer form, Amend 1) | `inst_stKcalDecay_admissible` (:976) | any `sz` with `sz.Admissible 𝔠 𝔡`, `3 ≤ d` | `W^{-d/2} ≤ lam`, `lam ≤ 𝔡⁻¹`, `N^𝔠 ≤ W`, `N → ∞`, `N=(WL)^d` (rfl) |
| `stKbound_timeIcc`, `stKward_timeIcc` | `inst_stKbound_timeIcc` (:1384), `inst_stKward_timeIcc` (:1393) | `sz0`, `E = STflowE z0`, `κ=1/10`, `gmax=10`, window `[0, 1/16]` | `sz0_tendsto`, `z0_abs_le`, `sz0_lam_bounds` (from `sz0_WO`), `0 ≤ 0 ≤ 1/16 < 1` |
| `KDecay_sum_tailT_le` | `inst_KDecay_sum_tailT_le` (:1405) | `d=3`, `L=5`, `g=1`, `t=1/2` | `2 ≤ 3`, `0 ≤ 1`, `1/2 < 1` |
| `stSumTwoLoop` | `inst_stSumTwoLoop` (:1410) | `sz0`, `(s,t)=(0,1/16)`, `C_d=4`, `𝔠d=1/240` | `𝔠d C_d = 1/60 ≤ 1/30`, `sz0_con`, `t<1`, `|E|<2`, `0 ≤ lam` |
| `stSumTwoLoop_exists` | `inst_stSumTwoLoop_exists` (:1423) | `sz0`, `C_d=4` | as above, with the `𝔠d` it produces |

None of these instances is degenerate: no `N = 0`, empty index, collapsed window, `False` premise or numeric literal witness.
The `∀ᶠ` threshold of `inst_stKcalDecay` is not numerical, because the constants of `KLPT_holds` are existential. This is the
extraction the ticket allows.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.KDecay 2>&1 | grep -E "error|warning:.*KDecay|Build completed"; echo exit $?
Build completed successfully (3715 jobs).
exit 0
$ lake env lean scratchpad/T2129/ax.lean   # #print axioms, names abbreviated
Gauss.Sizes.STKcalDecay: [propext, Classical.choice, Quot.sound]
Gauss.Sizes.stKcalDecay_holds: [propext, Classical.choice, Quot.sound]
Gauss.Sizes.stKbound_timeIcc: [propext, Classical.choice, Quot.sound]
Gauss.Sizes.stKward_timeIcc: [propext, Classical.choice, Quot.sound]
Loop.KDecay_tailC: [propext, Classical.choice, Quot.sound]
Loop.KDecay_sum_tailT_le: [propext, Classical.choice, Quot.sound]
Gauss.Sizes.stSumTwoLoop: [propext, Classical.choice, Quot.sound]
Gauss.Sizes.stSumTwoLoop_exists: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_stKcalDecay: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_stKcalDecay_admissible: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_stKbound_timeIcc: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_stKward_timeIcc: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_KDecay_sum_tailT_le: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_stSumTwoLoop: [propext, Classical.choice, Quot.sound]
Gauss.KDecayInst.inst_stSumTwoLoop_exists: [propext, Classical.choice, Quot.sound]
$ git diff --name-status main...t/T2129
A	RBM3D/Induction/KDecay.lean
$ git diff main...t/T2129 | grep -cE "^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom "
0
$ for n in STKcalDecay stKcalDecay_holds stKbound_timeIcc stKward_timeIcc KDecay_tailC KDecay_one_le_tailC KDecay_sum_tailT_le stSumTwoLoop stSumTwoLoop_exists KDecayInst; do git grep -nw $n main -- RBM3D | wc -l; done
0 (each of the 10 names)
```
- The branch touches only the sole writable file. `Test/Axioms.lean` is unchanged, which is allowed: the prover's registry
  scan reports `STKcalDecay` as concluded.
- No merged file changed, so no frozen signature changed.

## 5. Paper-delta coverage
| Lean/paper difference | candidate |
|---|---|
| `STKcalDecay` premise `W^{-Q} ≤ g`, `Q>0` before `∀ᶠ N` (paper: from `(eq:WO)`, `Q=d/2`) | T2129a (also Amend 1) |
| tail lattice sum in `zdistInf` (`|·|_∞`), explicit `C_∞(d) = d^{d-2}2^d radC(1/d)+1` | T2129b |
| `(eq:sumtwoloop)` second `≺` as a deterministic inequality, `𝔠d C_d ≤ 1/30`, extra `∀ᶠ t<1, |E|<2, 0≤lam`; `+W^{-D}`/first `≺` not here | T2129c |
| uniform-in-time forms need `0 ≤ s n ≤ t n < 1` for all `n` | T2129d |
| `3 ≤ d` on targets 1, 2; `2 ≤ d` on target 3 | T2129e |
Every difference found in §1 has a candidate. `docs/paper-deltas.md` has no T2129 entries yet (the dispatcher appends them).

## Observations (no effect on statements, instances, build, axioms, deltas)
- O1. Public unpinned names `stSumTwoLoop`, `stSumTwoLoop_exists` and `inst_*` carry neither the `KDecay` stem nor `private`
  (CLAUDE.md §3 (E)). They are the ticket's target-3 statement and the required instances; none clashes with a name on `main`.
- O2. `STKcalDecay` and `stKcalDecay_holds` are in `RBM.Gauss.Sizes`. The ticket suggests `RBM.Loop` for fixed-size facts.
  Consumers must use the full name `RBM.Gauss.Sizes.STKcalDecay`.
- O3. Ticket required reading cites RBM2D `c9a24cf`. The report's port check shows the ported ranges are identical at `9e0f275`.

## Verdicts
- Target 1 (`STKcalDecay` amended pin, `stKcalDecay_holds`): **PASS**
- Target 2 (`stKbound_timeIcc`, `stKward_timeIcc`): **PASS**
- Target 3 (`KDecay_sum_tailT_le`, `stSumTwoLoop`, `stSumTwoLoop_exists`): **PASS**

Overall: **PASS**. No dispatcher sign-off needed.
