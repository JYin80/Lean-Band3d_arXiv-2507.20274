Auditor model: claude-opus-5-5
# T2392 audit (round 1) — Sat Oct 10 22:03:12 UTC 2026

Branch `t/T2392` at `2177c1a`, audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2392-audit1` (detached).
Targets: `baEKSumDecay1_holds`, `baEKSumDecayNAL_holds`, `baEKSumDecay2_holds` (`RBM3D/BA/EKSum.lean`).

## 1. Diff scope and stop line

```
$ git diff --stat main...t/T2392
 RBM3D.lean             |    1 +
 RBM3D/BA/EKSum.lean    | 1929 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |    3 -
$ git diff main...HEAD -- RBM3D/BA/EKPins.lean | wc -l      # pins untouched
       0
$ wc -l RBM3D/BA/EKSum.lean                                 # stop line 2,000 (binding)
    1929 RBM3D/BA/EKSum.lean
```
Only the three sole writable files. `RBM3D.lean`: one line `+import RBM3D.BA.EKSum`, after the last import, before
`#assert_rbm_axioms`. `Test/Axioms.lean`: exactly the three `owedProps` lines `BAEKSumDecay1`, `BAEKSumDecayNAL`,
`BAEKSumDecay2` removed; `BAEKSumDecayNonzero` stays (verified in `git diff main...HEAD -- RBM3D/Test/Axioms.lean`).

## 2. Statements against the pins

The pins are the dispatcher-pinned Props `BAEKSumDecay1/NAL/2` (`BA/EKPins.lean:103-131`, merged by T2388, unchanged
on the branch). Script (`lake env lean Ax.lean` in the audit worktree):
```
baEKSumDecay1_holds : ∀ (d n : ℕ) (Λ κ : ℝ), BAEKSumDecay1 d n Λ κ
baEKSumDecayNAL_holds : ∀ (d n : ℕ) (Λ κ : ℝ), BAEKSumDecayNAL d n Λ κ
baEKSumDecay2_holds : ∀ (d n : ℕ) (Λ κ : ℝ), BAEKSumDecay2 d n Λ κ
```
plus three `example : ∀ d n Λ κ, BAEK… d n Λ κ := baEK…_holds` that elaborate (exit 0). Each target is the pin itself,
for all `d n Λ κ`, with no extra hypothesis: not a special case or adapter. Quantifier order of the pins (`∃ C` after
`d n Λ κ` [and `K` for Decay2], before `L g W ε D s t E m σ A`) is inherited. In the proofs, `C` is chosen from
`baEKXiBall_holds`/`baEKSameRow_holds`/`baEKXiDecay_holds`/`baProp6_holds` constants (functions of `d,Λ,κ`),
`latC (d-3)`, `n`, `K` (`EKSum.lean:206-208, 296-299, 1773-1795`): fixed before `L`, as ticket (ii) requires.
Ticket item 4 (supervisor C1): the proofs read `BAReal`, `BAuKer_eq_one_add_Xi`, `EKSum_norm_uKer_le`/`_Xi_le`
(row sums from `BAReal`), the four merged `_holds` theorems, and the band's public abstract helpers
(`ek_core_bound`, `ek_arith_res1`, `ek_arith_nal`, `ek_ratio_le`); no `‖m‖ = 1`, scalar `μ`, or smallness of `g`
beyond the pin's `g ≤ Λ`.

## 3. Vacuity, hidden hypotheses, cycles

- The targets have no hypotheses beyond the pinned Props; no structure-field hypotheses are introduced.
- Upstream inputs are merged theorems (`baEKXiBall_holds`, `baEKXiDecay_holds`, `baEKSameRow_holds` in
  `BA/EKPins.lean`, `baProp6_holds` in `BA/Prop6Path.lean`), not pins taken as hypotheses; `EKSum.lean` imports only
  `RBM3D.BA.EKPins` and `RBM3D.Evolution.SumDecay`; no module imports `EKSum` except the root: no cycle.
- No external hypothesis is added.

## 4. Compiled nonempty instances (`EKSum.lean:1902-1925`)

`EKSumInst.inst_baEKSumDecay1/NAL/2` apply the merged E1 wrappers `EKPinsInst.inst_BAEKSumDecay1/NAL/2`
(`BA/EKPins.lean:737-850`) to the three theorems, so no hypothesis is left open. The wrappers discharge every
deterministic hypothesis at concrete data (read in `EKPins.lean`): `d = 3`, `n = 2`, `L = sz0.L 0 = 4` (`LI_real`),
`g = gI ∈ (0, 1/64]` (`gI_pos`, `gI_le`), `Λ = 1`, `κ = 1/2`, `BAReal` by `hrI` (`BAflow_real`), `W = 16`,
`ε = 1/2` (`16^{1/2} = 4`, `sixteen_rpow_half`), `D = 2`, `s = 0`, `t = 1/2 ≤ 1 - g²/L²` (`half_le_one_sub`),
`W⁻¹ ≤ (1-t)/(1-s)` (norm_num); `σ = (+,-)` / `(+,+)` with `⟨0, by decide⟩` for NAL; `A = δ_0` (`AI_zero : AI 0 = 1`,
`AI_fastDecay`); Decay2: `K = 2`, `log 4 ≤ 4` (`log_le_half`), `4³ ≤ 16²`, `A = δ_0 ⊗ (δ_0 - δ_e)`
(`AzI_vals : AzI ![0,0] = 1 ∧ AzI ![0,e] = -1`, `AzI_fastDecay`, `AzI_sumZero`). Nondegenerate: `L = 4`, nonzero
tensors, open window `0 = s < t = 1/2`, `n = 2`; no `False` premise, no astronomically large witness.
```
'RBM.BA.EKSumInst.inst_baEKSumDecay1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKSumInst.inst_baEKSumDecayNAL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKSumInst.inst_baEKSumDecay2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Build, axioms, hygiene

```
$ lake build RBM3D.BA.EKSum                 (audit worktree)
✔ [3758/3758] Built RBM3D.BA.EKSum (17s)
Build completed successfully (3758 jobs).
exit 0
$ grep -n error <build log>                 (no lines)
$ lake env lean Ax.lean
'RBM.BA.baEKSumDecay1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSumDecayNAL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSumDecay2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "\bsorry\b|\badmit\b|^axiom|^\s*axiom |native_decide" RBM3D/BA/EKSum.lean
grep exit 1   (no match)
$ lake env lean docs/tickets/checks/T2392-check.lean   (on the branch)
check exit 0
$ lake build                                 (full library incl. #assert_rbm_axioms and the owedProps registry)
Build completed successfully (4205 jobs).
exit 0
```
Public names added: the three targets and `EKSumInst.inst_baEKSumDecay{1,NAL,2}`; `git grep` on `main` for these
names finds nothing. All other declarations are `private` with stem `EKSum_`. No frozen signature is touched.

## 6. Paper deltas

The Lean statements equal the T2388 pins; their statement differences from the paper are already in
`docs/paper-deltas.md` (T2388a-e at lines 185-190; D33 `log L ≤ W^ε`, line 287; the `L^d ≤ W^K` far remainder,
line 337, carried over from the band pin of the same shape). The proof-route difference (first difference of `Ξ`
via `Ξ = ((t-s)/t)(Θ_t - 1)` and `baProp6_holds` instead of `(prop:BD1)` + `(Mbound_AO)`) is proposed as
candidate T2392a in the prove report (d). No uncovered statement difference.

## 7. Observations (no verdict effect)

- The file is 1,929 lines: under the binding stop line 2,000 but above the 1,500 split mark of the ticket; the
  ticket's split mark is a process instruction and changes no statement, instance, build or axiom.
- The instances reuse E1's wrapper theorems (hypothesis = pin) instead of restating the data inline; since the
  wrapper is applied to the proved theorem, the composite has no open hypothesis, which meets ticket item 5.

## Verdicts

| Target | Verdict |
|---|---|
| `baEKSumDecay1_holds` | PASS |
| `baEKSumDecayNAL_holds` | PASS |
| `baEKSumDecay2_holds` | PASS |

Ticket T2392: **PASS**. No dispatcher sign-off needed.
