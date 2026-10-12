Auditor model: claude-opus-5-5

# T2441 audit, round 1 (BA-TL TL2d: `BATwistStepFixed`, `baTwistGridMart_holds`, `baTwistZeroMode_holds`)

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2441-audit1`, detached at `t/T2441`; scratch files in the scratchpad `T2441/`.
```
$ date -u; git rev-parse --short HEAD; git rev-parse --short main
Mon Oct 12 10:46:50 UTC 2026
bc7ebc2
30c6d7a
```

## 1. Build, axioms, hygiene, diff
```
$ lake build RBM3D.BA.TwistStep RBM3D.BA.TwistStep2 ; echo exit=$?
✔ [4059/4059] Built RBM3D.BA.TwistStep2 (23s)
Build completed successfully (4059 jobs).
exit=0
$ grep -E "^(warning|error)" build.log | grep -c TwistStep ; grep -c "^error" build.log
0
0
$ lake env lean ax.lean     (imports RBM3D.BA.TwistStep2)
'RBM.BA.BATwistStepFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistGridMart_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistZeroMode_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistStepFixed_caseI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistStepFixed_caseII' depends on axioms: [propext, Classical.choice, Quot.sound]
BATwistGridMart : ℕ → Prop
BATwistZeroMode : ℕ → Prop
exit=0
```
`ax.lean` also elaborates, without error, the ticket's acceptance checks: `example : ∀ d, BATwistGridMart d := baTwistGridMart_holds`, `example : ∀ d, BATwistZeroMode d := baTwistZeroMode_holds`, and `example : ∀ d, BATwistStepFixed d STCaseI := baTwistStepFixed_caseI` (the same for `STCaseII`).
```
$ lake env lean docs/tickets/checks/T2441-check.lean ; echo check_exit=$? ; grep -c error
check_exit=0
0
$ lake env lean RBM3D/Probe/T2441Pins.lean ; echo probe_exit=$? ; grep -c error
probe_exit=0
0
$ grep -nE "sorry|admit|native_decide|^axiom|Step2Gen_|STthetaOpg" RBM3D/BA/TwistStep.lean RBM3D/BA/TwistStep2.lean | wc -l
       0
$ git diff --stat main...HEAD
 RBM3D/BA/TwistStep.lean    | 1795 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistStep2.lean   | 1564 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2441Pins.lean |  332 ++++++++
 3 files changed, 3691 insertions(+)
$ public names without the stems TwistStep_/TwistStep2_ (grep of theorem|def|abbrev|structure|instance)
baTwistStepFixed_caseI
baTwistStepFixed_caseII
BATwistStepFixed
baTwistGridMart_holds
baTwistZeroMode_holds
$ git grep -nw <each of the 5 names> main -- RBM3D RBM3D.lean | wc -l
0 0 0 0 0
$ wc -l RBM3D/BA/TwistStep.lean RBM3D/BA/TwistStep2.lean      (stop line 2,000 per file)
    1795 RBM3D/BA/TwistStep.lean
    1564 RBM3D/BA/TwistStep2.lean
```
Every touched file is a sole writable file. The probe (`RBM3D/Probe/T2441Pins.lean`) is on the branch and must not be merged; it is not a deliverable (hub: bring in only `BA/TwistStep.lean`, `BA/TwistStep2.lean` and the two root imports). No merged file is edited, so no frozen signature changes. Only the five pinned names are public without a stem; every other helper has a stem prefix or is `private` (§3 (E)).

## 2. Target 1 `baTwistGridMart_holds (d : ℕ) : BATwistGridMart d`: PASS
- Statement: its type is the merged pin `BATwistGridMart d` (`TwistGrid2:223`, `∃ C₀, 0 ≤ C₀ ∧ BATwistGridMartAt d C₀`), for every `d`. The proof (`TwistStep:73-76`) is exactly the ticket's three lines: `baTwistGridRem_holds`, then `baTwistGridAssemble_holds … (baTwistGridTail_holds d) (baTwistGridWTail_holds d)`, all merged.
- Instance: `TwistStep2:1441` applies it at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/2`, `t ≡ 2/3`, `D = 1` and `K_n = ⌈N^{CK}⌉ + 1`, with every hypothesis discharged. It compiles.

## 3. Target 2 `baTwistZeroMode_holds (d : ℕ) : BATwistZeroMode d`: PASS
- Statement: its type is the merged pin `BATwistZeroMode d` (`TwistPins:217-221`). The pin covers `σ 0 ≠ σ 1`, every `n`, `t ∈ [0, T0]` and all `c₁, c₂`, and the identity has the factor `(2i W^d η_t)⁻¹`.
- Route (Lean-checked): `TwistStep_ward_mat` (new, `M^*−M = −2i Im m M^*M` and the `MM^*` form), the row sums of `Θ`, and `BATheta_swap` for `(−,+)`. This corrects the ticket's `BATheta_conj`; (a) row 15 explains why.
- Instance: `TwistStep2:1452` uses `n = 0`, `t ≡ 1/2`, `σ = (false,true)`, `c₁ = 0`, `c₂ = (1,1,0)`, with `c₂ ≠ 0` compiled at `:1459`. The ticket's `c₂ = (1,0,0)` makes both sides zero ((a) [T]: `|Im M_{c₂c₁}| = 0`). The point actually used has `|rhs| = 2.06e-8`, so it is nondegenerate, and this deviation from the ticket makes it more so, not less.

## 4. Target 3 `BATwistStepFixed`, `baTwistStepFixed_caseI`, `baTwistStepFixed_caseII`: PASS
Merged pin text against the probe (the 1a-audit decided this form, `T2441-1a-audit.md:54`, "ACCEPTED"):
```
$ awk '/^def BATwistStepFixed/{f=1} f&&/^$/{f=0} f' <probe> > p; <same> RBM3D/BA/TwistStep.lean > m; wc -l p m; diff p m; echo diff_exit=$?
      10 pin_probe.txt
      10 pin_merged.txt
diff_exit=0
```
Statement against ticket item 3 (`TwistStep:59-68`):
- Frame: `BATwFrame d R` gives `3 ≤ d`, `κ ε 𝔡 Cd`, then `∃ 𝔠d ≤ 1/100`, then `𝔠 sz z`, `BAFlow`, `0 ≤ s < t ≤ T0`, `R sz s t`, `STConStInd`, `twSteps` (`TwistPins:146-151`). Fixed parameters come before the sizes.
- Hypotheses: `BATwistLoopLaw C μ s`, then `∀ Ξ : ℕ → ℝ, (∀ n, 1 ≤ Ξ n)`. The bootstrap is `‖twL2'−twK‖ ≺ Ξ_n Bctl_v^{3/2}` over `TimeIcc s t n × (Fin 2→Bool) × Zd³`, the `≺` form at a deterministic level that the ticket allowed and the 1a-audit chose.
- Conclusion: `∀ τ, s ≤ τ ≤ t`, then `‖twL2' τ − twK τ‖ ≺ Bctl_τ^{3/2}(1 + Bctl_τ^{1/6} Ξ_n)` over `(Fin 2→Bool) × Zd³`. This is all four charges in one statement, with exponent 3/2 in and out and `+1/6` on the `Ξ` term, as TP:171 has it for fixed `u`.
- Not trivial: at `Ξ ≫ 1` the conclusion is strictly stronger than the hypothesis restricted to `τ`, because of the factor `Bctl^{1/6}` and `Bctl < 1`.
- Both regime theorems are the general `R`-free pin at `R := STCaseI` and `R := STCaseII`. Each is `TwistStep2_pin d R (TwistStep2_ker_caseX d)`. Here `TwistStep2_Ker d R` (`TwistStep2:597`) is a `def` hypothesis of the generic assembly, and it is discharged by the theorems `TwistStep2_ker_caseI` (`:1015`) and `_caseII` (`:1312`). So no hypothesis is hidden in a structure field, and none is left open.

Charge cases (ticket item 4), from the files:
```
$ grep -n <merged input> RBM3D/BA/TwistStep*.lean   (first code hit)
baEKSameRow_holds   TwistStep2:762  (kerA; case A, used by ker_caseI :1031 and ker_caseII :1323, both regimes)
baTwKerFar_holds    TwistStep2:837  (kerB; case B, ker_caseI :1032, σ0 ≠ σ1)
baTwKerZero_holds   TwistStep2:780  (kerC; case C, ker_caseII :1327, σ0 ≠ σ1, Pr = projMat)
twWard_holds        TwistStep2:1092 ; baTwistZeroMode_holds TwistStep2:1100 ; baTwistAvgProd_holds TwistStep2:1145 (zero mode, case C)
baTwistSrc1..5_holds TwistStep2:637-641 ; st5_conStInd_mono TwistStep2:658 ; baTwistGridRem/WTail_holds TwistStep2:444,446
ST_grid_whp_of_sections TwistStep:654 ; ST_model_le_path TwistStep:1699
```
- All three cases of TP T.12′ are in this row, as the ticket requires.
- TL1 at `τ` comes from the parts `twSteps.1.2.1` and `twSteps.2.1` (`ker_caseII :1328`). Nothing is assumed beyond the frame, so the stop rule does not fire.

Dependencies: all are merged results. There is no cycle: the new files import only merged modules, and the targets use none of the pins that TL2e owes.

Instances (`TwistStep2:1467`, `:1509`; both compile):
- `STCaseI` at `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/2 < t ≡ 2/3 ≤ T0` (`t0_sz0`). `STCaseI` is proved (`lam²/L² ≤ 1/3`) and so is `STConStInd` (`s1Setup_conStInd_const`). `τ` is any sequence in `[1/2, 2/3]`.
- `STCaseII` at the new datum `TwistStep2_szII`: `L ≡ 4`, `W_n = n+25`, `lam ≡ 5`, `w = (5003/5000)i`, `κ = 3/5000`, `ε = 1/2`, `𝔠 = 1/9`, `𝔡 = 1/10`. `BAFlow` is proved in `TwistStep2_flowII` (`:1353`), as are `T0 ≥ 1/2000`, `s ≡ 0 < t ≡ 1/2000`, `STCaseII` (`1 ≤ 25/16`) and `STConStInd`.
- Why a new datum: `sz0` has no `STCaseII` window, and `TwistStep2_no_caseII_sz0` (`:1547`) is a compiled theorem saying so. The ticket's fallback (keep `STCaseII` as a hypothesis on `sz0`) would therefore have been a `False` premise.
- In both instances `twSteps` and `BATwistLoopLaw` at `s` stay hypotheses. These are other gates' pins, as ticket item 5 allows. Every deterministic hypothesis is discharged. The bootstrap hypothesis, which item 5 allowed to stay a hypothesis, is also discharged, at the a priori level `Ξ_n = 2(2/κ)²N_n⁴` (`TwistStep_zcrude`). Neither instance has `N = 0`, an empty index set or a collapsed window.

## 5. Paper deltas
- `T2441a` (prove report (a″), (d)): the paper's random `Ξ̃_u = sup_{v≤u} max|Z_v| B_v^{-γ*}` (TP:171) is replaced by a deterministic level `Ξ_n`, which TL2e iterates. This is the only Lean/paper difference at the statement level. It is proposed in the report and is not yet in `docs/paper-deltas.md` (`grep -n T2441 docs/paper-deltas.md`: no hit). The dispatcher appends it.
- The other deviations are not paper deltas. `𝔠d` including `1/(2d)` is inside the `∃ 𝔠d` of the frame. The `ε′` factor `d` (F1) is proof-internal. The instance data (`c₂ = (1,1,0)`, `TwistStep2_szII`) are witnesses.

## 6. Observations (no RETURN)
- O1. `BATwistDuhamel_holds`, `BATwistHier_holds` and `baTwKDecay_holds`, which ticket item 4 names as route ingredients, are not cited by name in either file. The grid identity is re-derived (`baTwistGrid_decomp`, `TwistStep_identity`). This is a route difference. The statements are proved with the standard axioms, so no statement, instance, build or delta is affected.
- O2. Both target-3 instances discharge the bootstrap at the crude a priori `Ξ ≍ N⁴`, where the conclusion is weaker than the a priori bound (1a-audit O4). They show that the premises are consistent at concrete data. Ticket item 5 allowed the bootstrap to stay a hypothesis, so this exceeds the requirement.
- O3. The `STCaseII` datum (`κ = 3/5000`, window `[0, 1/2000]`) is a witness, not a physical regime, as the prove report states in (a″) F1 and (d). No smallness of `g` is used (`lam ≡ 5`).
- O4. `RBM3D.lean` is not edited on the branch. The hub adds the two imports at merge and runs the full `lake build` with `#assert_rbm_axioms`. The prove report (b) says a full build with the imports added passed; I did not re-run it here.

## Verdict
- Target 1 `baTwistGridMart_holds`: **PASS**.
- Target 2 `baTwistZeroMode_holds`: **PASS**.
- Target 3 `BATwistStepFixed`, `baTwistStepFixed_caseI`, `baTwistStepFixed_caseII`: **PASS**.
- Ticket T2441: **PASS**. No dispatcher sign-off is needed.
- Merge only `RBM3D/BA/TwistStep.lean` and `RBM3D/BA/TwistStep2.lean`, plus the two root imports. Do not merge `RBM3D/Probe/T2441Pins.lean`.
