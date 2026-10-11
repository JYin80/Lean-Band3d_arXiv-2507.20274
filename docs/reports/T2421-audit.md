Auditor model: claude-opus-5-5
# T2421 audit (round 1): BA-TL TL0, `RBM3D/BA/TwistPins.lean`; ticket + Amend 1 — Sun Oct 11 12:20:24 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2421-audit1`, detached at `t/T2421` = 6e83091; merge-base with main 913f555. Scratch: `T2421/` in the auditor scratchpad.

## 1. Scope, build, axioms
```
$ git diff main...t/T2421 --stat
 RBM3D.lean              |   1 +
 RBM3D/BA/TwistPins.lean | 962 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean  |   3 +
 3 files changed, 966 insertions(+)
$ git diff main...t/T2421 | grep -c "^-[^-]"                         # deleted lines (frozen signatures)
0
$ git diff main...t/T2421 | grep -E "^\+" | grep -cE "sorry|admit|native_decide|^\+axiom|Step2Gen_|STthetaOpg"
0
$ lake build RBM3D.BA.TwistPins > build.log 2>&1; grep -E "error|TwistPins|^exit|Build completed" build.log
✔ [3997/3997] Built RBM3D.BA.TwistPins (7.6s)
Build completed successfully (3997 jobs).
exit 0
$ grep -c "BA/TwistPins.lean" build.log                               # warnings/errors in the file
0
$ lake env lean docs/tickets/checks/T2421-check.lean; echo $?
0
$ lake env lean ax.lean   # import RBM3D.BA.TwistPins; #print axioms / #check
'RBM.BA.twTr_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twMB_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twK_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twWard_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twCirc_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twK_bound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
twK_bound_holds : ∀ (d : ℕ), twK_bound d
@twFold_holds : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d), twFold sz
@twWard_holds : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d), twWard sz
@twCirc_holds : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d), twCirc sz
```
The four `_holds` theorems take no hypotheses: the pins are proved outright, not as conditional adapters. Unpinned helpers: 28 `private` declarations, all with stem `TwistPins_` (`grep -nE "^private (theorem|def|lemma) " | grep -v TwistPins_` → no line). `RBM3D.lean`: one import after the last `import`, before `#assert_rbm_axioms`. Full `lake build` not run here (hub at merge).

## 2. Statements against the pin (target 1): verbatim copy of probe §1–§3
```
$ git show 76c586e:RBM3D/Probe/T2413Pins.lean > probe.lean; git show t/T2421:RBM3D/BA/TwistPins.lean > file.lean
$ grep -n "^open RBM\|^end Twist" probe.lean file.lean
probe.lean:36:open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph      probe.lean:280:end Twist
file.lean:40:open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph       file.lean:286:end Twist
$ sed -n 36,280p probe.lean > p.txt; sed -n 40,286p file.lean > f.txt; diff p.txt f.txt | cut -c1-120
80c80,82
< /-- **`twK_bound`** (proofs T.1 (i)-(ii); from `BAProp5`, `BAProp5mixed`, `BATheta_row_sum_pm`, `BAMB_row_l1`): a
---
> /-- **`twK_bound`** (proofs T.1 (i)-(ii); from `BAProp5`, `BAProp5mixed`, `BATheta_row_sum_pm`, `BAMB_row_l1`): a
> **Eventual in `n`** (T2421 Amend 1, paper-delta candidate T2421a; the probe `T2413Pins.lean:116-121` has `∀ n`): the
> `0 < g₀_n ≤ 𝔡⁻¹` that `BAProp5` and `BAMB_row_l1` need holds only eventually along `BAFlow` (`BAflow_lam0_window`, `
84c86
<       ∀ (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
---
>       ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
```
Imports: identical to the probe's seven lines (`head -40 | grep import`, both files lines 6–12). Every declaration of §1–§3 (`twBlk` … `twK_ba`) is byte-identical to the probe except `twK_bound`, whose only change is the quantifier `∀ n` → `∀ᶠ n in atTop` ordered by Amend 1 item 1 (constant `∃ C` still after `3 ≤ d, κ ε 𝔡` and before `𝔠 sz z`, i.e. O2 kept; conclusions unchanged; Bctl form kept, as T2413 D3 requires).

## 3. Per-target verdicts

**twTr_eq, twMB_ba, twK_ba** (target 2, verbatim proofs). Statements identical to the probe (diff above). Instances `:821`, `:823`, `:825` at `sz0`, `n = 0`, `Im m_F > 0` discharged by `BAmF_sz0_im_pos 0`, `c₂ = (1,0,0) ≠ c₁ = 0`. **PASS.**

**twFold_holds : ∀ sz, twFold sz** (T.2, (B.2) squared, `T2398-TL-proofs.md:41-43`). `‖twLoopX‖² ≤ twSq X₁ c₂ a · twSq X₂ a c₁` for all `n, X₁, X₂, a, c₁, c₂`: exactly (B.2) with `Tr(E_{c2}X₁E_aX₁^*)`, `Tr(E_aX₂E_{c1}X₂^*)`; no hypothesis. Instance `:897`: pairwise distinct blocks `0, (1,0,0), (2,0,0)` (`decide`), nonzero twisted datum, LHS `= W^{-d} > 0`, applies `twFold_holds sz0 0`. **PASS.**

**twWard_holds** (T.3, `n = 2`, `:49`). Hypotheses `η ≠ 0` and both identities (2.53) `G − G^* = 2iη GG^* = 2iη G^*G`; both charges `σ`; factor `(2iW^dη)⁻¹`, matching T.3. Instance (O4) `:842`: `G = i·1` (= `(H−z)⁻¹` at `H = 0`, `z = i`), `η = 1`, both identities proved in the example, both charges, sum `= W^{-d} ≠ 0`. Hypotheses satisfiable and conclusion nonzero: non-vacuous. **PASS.**

**twCirc_holds** (A.2). Hypothesis = the offset tie of `BAMfine_eq`; conclusion linear identity with the subtracted term `W^{-d} MB_{ac₁} Tr(X₁P_{ac₂})`. Instance `:870` discharges the tie by `BAMfine_eq sz0 _ _ 0 (BAmF_sz0_im_pos 0)` at the carrier's `M`; `:911` shows the correction term `≠ 0` (`W^{-d} m_F`, `Im m_F > 0`). **PASS.**

**twK_bound_holds : twK_bound d** (T.1 (i)-(ii), Amend 1 form). Quantifiers: `3 ≤ d → ∀ κ ε 𝔡 > 0, ∃ C > 0, ∀ 𝔠 sz z, BAFlow … → ∀ t, 0 ≤ t ≤ T0 → ∀ᶠ n, ∀ σ c₁ c₂, (∀ a, ‖K̃‖ ≤ C·Bctl n (t n)) ∧ Σ_a ‖K̃‖ ≤ C (W^d η)⁻¹` — matches Amend 1 item 1 and ticket O2. `Bctl n t = (W^d)⁻¹ Bparam d L (lam n) t 0` (`Defs/Sizes.lean:214`) = `W^{-d}B_{t,0}` at the model coupling. Constant (proof `:701`): `Cd·CM·((κ+1)/κ) + CM`, `Cd` from `baProp5_holds (k+2) 𝔡⁻¹ κ`, `CM` from `BAct_rate (k+2) 𝔡⁻¹ κ`: depends on `(d, κ, 𝔡)` only, no `g` smallness (C1). Dependencies are merged theorems (`BAflow_lam0_window`, `BAflow_real`, `baProp5_holds`, `BAMB_row_l1`, `BAself_im_le_one`, `GreenSchur.lean:59,72`), no hypothesis taken: no cycle, no hidden structure field (`BAFlow = Admissible ∧ ∀ n BAdom`, `FlowPins.lean:389`, the stage's standard premise). Instance (O3) `:810`: `twK_bound_holds 3` at `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `Defs/Sizes.lean:260-262`), `flow_sz0`, `t ≡ 1/2 ≤ T0` by `half_lt_t0`, `σ = (−,+)`, `c₁ = 0 ≠ c₂ = (1,0,0)` for every `n` of the eventual set; `atTop` on `ℕ` is `NeBot` (`example : (atTop : Filter ℕ).NeBot := inferInstance` compiles in `ax.lean`), so the eventual set is a nonempty tail. Every deterministic hypothesis discharged. **PASS.**

**Statement-level definitions** (`twSteps`, `BATwFrame`, `BATwistAvgProd`, `BATwistLoopStep`, `BATwistLoopBase`, `BAMainIndTL`, `BAMLOutTL`, `BAChainTL`, `BATwKer*`, `BATwistZeroMode`, `twSrc`, `twDec`, `BATwistSrc1-5`): verbatim (diff §2); statement-level examples `:776-805`, `:929-956` apply each at concrete data (`sz0`, `flow_sz0`, `t0_sz0`, `half_lt_t0`, `s1Setup_conStInd_const`; `TwistPins_Pf` with `L = 4`, `W = 16`), other gates' pins as hypotheses (ticket item 5). **PASS.**

**Registry (target 4, Amend 1 item 2).**
```
$ git diff main...t/T2421 -- RBM3D/Test/Axioms.lean | grep "^+" | cut -c1-90
+   -- T2421 (BA-TL TL0, DECISIONS §234, §236): the twisted-loop pins of stage TL (`RBM3D/BA/
+   `RBM.BA.BATwistAvgLaw, -- TL1: `|Tr(G̊ P_{c₂c₁})| ≺ W^{-d} B_{τ,0}` for every ordered pai
+   `RBM.BA.BATwistLoopLaw, -- TL2: `|L̃ − K̃| ≺ (W^{-d} B_{τ,0})^{3/2}` for the twisted 2-loo
$ python3 -I reg.py docs/tickets/T2421-amend-1.md RBM3D/Test/Axioms.lean   # owner text = Amend 1 text, verbatim
RBM.BA.BATwistAvgLaw text in amend: True | line in Axioms.lean ends with owner text: True
RBM.BA.BATwistLoopLaw text in amend: True | line in Axioms.lean ends with owner text: True
```
Both lines carry `(B.1)`, Theorem 8.2, T2398d, as the neighbouring format. Additions only. **PASS.**

## 4. Paper deltas
- `twK_bound` `∀ n` → `∀ᶠ n in atTop` (difference from the T2413 probe and from T.1's "for all `u`"): proposed as **T2421a** (prove report (d)); not yet in `docs/paper-deltas.md` (`grep -n "T2421\|twK_bound\|twist" docs/paper-deltas.md` → no line). Covered.
- No other Lean/paper statement difference introduced by this ticket (§1–§3 verbatim from the probe; the Bctl form without the decay factor of T.1 (i) is the ticket's pin per T2413 D3, and twisted loops are not statements of the paper: `grep -rn -i twist paper/tex/ | wc -l` → 1; covered by T2398d).

## 5. Observations (no effect on statement, instance, build, axioms, deltas)
- O1. The `twK_bound` docstring keeps "`C = 1` in the proofs" (the probe's text); the Lean constant is `Cd·CM·(κ+1)/κ + CM`. The report says so ((d)). Harmless: the statement is `∃ C`.
- O2. Section header `:42` reads "Verbatim from `t/T2398:…T2398Pins.lean`"; the text actually comes from the T2413 probe, which carries the same header. Doc-only.
- O3. The prove report is 259 lines: within CLAUDE.md §6 (300) but over the ticket's 150 (report states this, (d)).
- O4. `twK_bound`'s constant does not use `ε`; the pin allows `C(d,κ,ε,𝔡)`, so this is stronger, not a defect.

## 6. Verdict
| target | verdict |
|---|---|
| definitions §1–§3 (verbatim; `twK_bound` per Amend 1) | PASS |
| `twTr_eq`, `twMB_ba`, `twK_ba` | PASS |
| `twFold_holds`, `twWard_holds` (O4), `twCirc_holds` | PASS |
| `twK_bound_holds` (O2 constant order, O3 `c₂ ≠ c₁`, eventual form) | PASS |
| registry lines (Amend 1 item 2) | PASS |
| build / axioms / scope | PASS |

**Overall: PASS.** No dispatcher sign-off needed (the one statement change is the dispatcher's Amend 1).
