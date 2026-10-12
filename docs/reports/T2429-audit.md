Auditor model: claude-opus-5-5
# T2429 audit (round 1) — Mon Oct 12 00:20:27 UTC 2026
Branch `t/T2429` HEAD `1f23fe8`, merge base `0a8176c` (no Lean change on `main` since: `git diff --stat 0a8176c main -- RBM3D/ RBM3D.lean` empty). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2429-audit1` (detached). Scratch: `<scratchpad>/T2429/`.

## 1. Diff scope and keyword deletions
```
$ git diff --stat main...t/T2429
 RBM3D/BA/EKNonzero.lean    |   12 +-
 RBM3D/BA/EKPins.lean       |    6 +-
 RBM3D/BA/TwistKer.lean     | 1599 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistKer2.lean    | 1442 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2429Pins.lean |  119 ++++
 5 files changed, 3169 insertions(+), 9 deletions(-)
$ git diff -U0 main...t/T2429 -- RBM3D/BA/EKPins.lean RBM3D/BA/EKNonzero.lean | python3 -I <check: every + line = its - line minus "private ">
removed 9 added 9
all + == - minus "private ": True
  EKNonzero_E EKNonzero_E_pos EKNonzero_projMat_comm EKNonzero_Mss_shift EKNonzero_projMat_mul_Theta EKNonzero_Theta0_shift EKPins_norm_Q_le EKPins_norm_Theta_le EKPins_norm_uKer_le
$ for n in <the 9 names>; do cat TwistKer.lean TwistKer2.lean | grep -cw $n; done
EKPins_norm_Q_le 3, EKPins_norm_Theta_le 4, EKPins_norm_uKer_le 3, EKNonzero_E 11, EKNonzero_E_pos 2, EKNonzero_projMat_comm 1, EKNonzero_Mss_shift 1, EKNonzero_projMat_mul_Theta 1, EKNonzero_Theta0_shift 1
$ wc -l RBM3D/BA/TwistKer.lean RBM3D/BA/TwistKer2.lean      # stop line 2,000 per file
    1599 RBM3D/BA/TwistKer.lean
    1442 RBM3D/BA/TwistKer2.lean
```
Files touched: the sole writable files only (`TwistPins.lean`, `Test/Axioms.lean`, `RBM3D.lean` untouched; the probe is the allowed non-merged file). The EKNonzero deletions are `:50, :53, :102, :110, :123, :143`, all in the ticket's allowed range "helpers of `:50-189` that its `A`-form uses", fixed by the probe step (prove report (a″)(iv)); each name is used by the new files. `EKNonzero_norm_projMat_mul_uKer_le` stays `private` (allowed, not required). No frozen signature changes (only the `private ` keyword).

## 2. Statements (elaborated types, compiled against the pins)
Audit file `<scratchpad>/T2429/Audit.lean` (imports the two modules): `#check` of each target; `example`s that type each target as the check file's §2 shape (`∀ d Λ κ, BATwKerX d Λ κ`, `∀ d R, BATwistSrcN d R`, plus `BATwistSrc1 3 STCaseI`, `BATwistSrc5 3 STCaseII`); `(∀ d, BATwKDecay d) ↔ <the ticket's intended shape typed out by the auditor> := Iff.rfl`; `#print axioms`.
```
$ lake env lean <scratchpad>/T2429/Audit.lean; echo exit=$?
baTwKerA_holds : ∀ (d : ℕ) (Λ κ : ℝ), BATwKerA d Λ κ
baTwKerFar_holds : ∀ (d : ℕ) (Λ κ : ℝ), BATwKerFar d Λ κ
baTwKerZero_holds : ∀ (d : ℕ) (Λ κ : ℝ), BATwKerZero d Λ κ
baTwKDecay_holds : ∀ (d : ℕ), BATwKDecay d
baTwistSrc1_holds : ∀ (d : ℕ) (R : {d : ℕ} → Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistSrc1 d fun {d} => R
baTwistSrc2_holds : ∀ (d : ℕ) (R : {d : ℕ} → Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistSrc2 d fun {d} => R
baTwistSrc4_holds : ∀ (d : ℕ) (R : {d : ℕ} → Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistSrc4 d fun {d} => R
baTwistSrc5_holds : ∀ (d : ℕ) (R : {d : ℕ} → Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistSrc5 d fun {d} => R
'RBM.BA.baTwKerA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwKerFar_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwKerZero_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwKDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistSrc1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistSrc2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistSrc4_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistSrc5_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistKer_twEG_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistKer_entry_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistKer_twEE_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistKer_twEG_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Pin text of `BATwKDecay` (`TwistKer.lean:447-452`; `diff` against `Probe/T2429Pins.lean`'s text: identical):
```lean
def BATwKDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ ε₁ D : ℝ, 0 < ε₁ → 0 < D →
      ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ BAflowT0 sz z n → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) →
        ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

```
```
$ lake env lean docs/tickets/checks/T2429-check.lean (copy, in the audit worktree); echo exit; grep -c error
check-exit=0, errors 0
$ lake env lean RBM3D/Probe/T2429Pins.lean; echo exit; grep -c error
probe-exit=0, errors 0
```

Statement findings (per target):
- **T.10 (a), (b), (d)**: the theorem types are literally the TL0 pins `BATwKerA/Far/Zero d Λ κ` (`TwistPins.lean:193, 199, 209`, file unchanged), quantified as `baEKSameRow_holds`. (d) is proved for every `A > 0` (pin), not only the merged `A = 1`. Matches TP T.10 (D.6) and F1 (kernel's own `g`).
- **T.1 (iii) `BATwKDecay`**: equal (`Iff.rfl`) to the ticket's intended shape: `twK_bound` prefix without `∃ C`, `∀ ε₁ D > 0, ∀ᶠ n, ∀ v ∈ [0, BAflowT0 n], ∀ σ a c₁ c₂`, cut `W^{ε₁} ellT(L, lam, v) ≤ zdistInf (a - c₁)`, bound `W^{-D}`. Against TP:37-38: `W ≥ W₀(ε,D)` → `∀ᶠ n`; cut at the model `ℓ_v(lam) ≥ ℓ_v(g₀)` and in `zdistInf ≤ zdistD` (both make the hypothesis weaker relative to the kernel scale/periodic distance only in the direction F1 allows: the conclusion is the consumer `twDec`'s cut); `v` restricted to `[0, t₀]`. All covered by candidate T2429a-1.
- **T.11 (i), (ii), (iv), (v)**: types are the TL0 pins `BATwistSrc{1,2,4,5} d R` for every regime `R` (`TwistPins.lean:261-277`); `twSteps`, `STConStInd` are pin premises of `BATwFrame` by design (TL2d supplies them).

## 3. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "^(structure|class|instance|axiom|opaque)" TwistKer.lean TwistKer2.lean | wc -l; grep -n "^include" both files
0
RBM3D/BA/TwistKer2.lean:1390:include hC hS        # section Inst only (the instance examples), after every target
$ grep -h "^import" TwistKer.lean TwistKer2.lean | sort -u; each checked with git cat-file -e main:<path>
CombesThomas EKNonzero EMn2BA GreenSchur KInduct Prop6Path TwistPins Induction.KDecay: on main;  BA.TwistKer: this ticket (TwistKer → TwistKer2)
$ grep -cE "sorry|admit|native_decide|^axiom|Step2Gen_|STthetaOpg" TwistKer.lean TwistKer2.lean
RBM3D/BA/TwistKer2.lean:0
RBM3D/BA/TwistKer.lean:0
$ git grep -cE "<9 target names>|TwistKer_*|TwistKer2_*" <ref> -- RBM3D   # name clash
main hits: 0;  t/T2427: 0;  t/T2428: 0;  t/T2430: 0;  t/T2423: 0;  t/T2431: absent
```
The elaborated types in §2 show no section variable in any target. No new structure, no sibling-branch import, no cycle. Public unpinned helpers carry the stem `TwistKer_` (§3 (E)).

## 4. Compiled nonempty instances (in the same files; all compile: build §5)
| target | file:line | data | deterministic hypotheses |
|---|---|---|---|
| T.10 (a) | TwistKer:542 | `d=3, L=4`, flow point `Pf` of `FlowPt 4 (1/2)`, `Λ=1`, `κ=Im m₀`, `v=0<u=1/2`, `A=δ₀≠0` | all discharged (`Pf.real`, `g0_pos`, `g0_le`) |
| T.10 (b) | TwistKer:548 | same `Pf`, `W=16, ε=1/2, D=2`, `c₁=0`, `A=δ₀≠0` | regime `u ≤ 1-g²/L²`, `W⁻¹ ≤ (1-u)/(1-v)`, far-set smallness proved |
| T.10 (d) | TwistKer:564, 576 | `A=2` with `¬((1-v)L² ≤ 1·g₀²)` proved (outside the merged `A=1` regime); `A=(κ+1)/κ` | all discharged |
| T.1 (iii) | TwistKer:589 | `sz0, zSeq, flow_sz0`, `ε₁=1/10, D=2`, every `v∈[0,1/2]`, `a=(2(n+1),0,0), c₁=0` proved in the cut for every `n` | all discharged; no hypothesis on the example |
| T.11 (i),(ii) | TwistKer2:1393, 1396 | `sz0`, `s≡1/2<t≡2/3≤t₀`, `STAny`, `STConStInd` via `s1Setup_conStInd_const` (stem frame instance :1382) | `twSteps` (other gates' pins) and `0<Cd` remain hypotheses |
| T.11 (iv) | TwistKer2:1400 | as above, every `γ∈[1,2]`; `Ξ_n=32N_n⁴≥1` and the a-priori `‖Z_v‖ ≤ Ξ B^γ` proved | as above |
| T.11 (v) | TwistKer2:1431 | as above, all five `twDec` conjuncts, every `b'` | as above |
None has `N=0`, an empty index set, a collapsed window (`s<t` strict) or a `False` premise. `twSteps` is exactly the hypothesis the ticket allows (item 5).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.EKPins RBM3D.BA.EKNonzero RBM3D.BA.TwistKer RBM3D.BA.TwistKer2   # tail; grep -ci error
✔ [4008/4012] Built RBM3D.BA.EKPins (7.4s)
✔ [4009/4012] Built RBM3D.BA.EKNonzero (3.6s)
✔ [4010/4012] Built RBM3D.BA.TwistPins (8.6s)
✔ [4011/4012] Built RBM3D.BA.TwistKer (10s)
✔ [4012/4012] Built RBM3D.BA.TwistKer2 (9.7s)
Build completed successfully (4012 jobs).
exit 0
error lines: 0
```
Warnings are lint only (line length, unused simp args) in other modules. Axioms of the 8 targets and of 4 public stem helpers: `[propext, Classical.choice, Quot.sound]` (§2 output). The full `lake build` with the two root imports is the hub's merge step.

## 6. Paper-delta coverage
- `BATwKDecay` vs TP T.1 (iii): `∀ᶠ n` for `W ≥ W₀`, cut at `ellT (sz.L n) (sz.lam n) v` (model scale; kernels at `g₀ ≤ lam`), in `zdistInf`, `v ∈ [0, BAflowT0 n]`, no constant: proposed as **T2429a-1** (prove report (a″) and (d)).
- T.11 (v) by entry decay instead of T.5 3-/6-loops: route only, statement unchanged: **T2429a-2**.
- T.10 (a), (b), (d) and T.11 (i), (ii), (iv), (v): the statements are the merged TL0 pins (T2421) unchanged; their Lean/paper differences (e.g. (d)'s `A`-regime and constant `C` for `≺ 1`) belong to TL0's coverage, not new here.
No uncovered statement difference introduced by this ticket.

## 7. Observations (no verdict effect)
- O1. The (iv) instance uses the crude `Ξ_n = 32 N_n⁴`; it discharges the a-priori hypothesis honestly (`TwistKer2_Z_crude`, `_eta_inv_le`, `_Bctl_rpow_ge`) and the pin is `∀ Ξ`, so the target is not weakened; a sharper `Ξ` would only make a stronger example.
- O2. `lake build` reported `Built RBM3D.BA.TwistKer (10s)`, `TwistKer2 (9.7s)` in the audit worktree; the targets were in addition elaborated against the built oleans by `Audit.lean` (exit 0).
- O3. The ticket's literal EKNonzero expectation (:50, :53, :102, plus :191) differs from the landed list (:50, :53, :102, :110, :123, :143; :191 stays private). Both are within the ticket's permission ("helpers of :50-189 that its A-form uses"; the probe fixes the list); recorded for the dispatcher's ledger, not a defect.

## Verdict
| target | verdict |
|---|---|
| `baTwKerA_holds` (T.10 a) | PASS |
| `baTwKerFar_holds` (T.10 b) | PASS |
| `baTwKerZero_holds` (T.10 d, every `A > 0`) | PASS |
| `BATwKDecay` / `baTwKDecay_holds` (T.1 iii) | PASS |
| `baTwistSrc1_holds` (T.11 i) | PASS |
| `baTwistSrc2_holds` (T.11 ii) | PASS |
| `baTwistSrc4_holds` (T.11 iv) | PASS |
| `baTwistSrc5_holds` (T.11 v) | PASS |

**Ticket T2429: PASS.** No dispatcher sign-off needed. Merge note for the hub: bring in `TwistKer.lean`, `TwistKer2.lean`, `EKPins.lean`, `EKNonzero.lean`; add `import RBM3D.BA.TwistKer`, `import RBM3D.BA.TwistKer2` after the last import of `RBM3D.lean`; do not merge `RBM3D/Probe/T2429Pins.lean`.
