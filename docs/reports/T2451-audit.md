Auditor model: claude-opus-5-5

# T2451 audit (round 1): BA-TL TL2e, `BATwistLoopStep` from `BATwistStepFixed`; `BATwKcircBound`
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2451-audit1`, detached at `t/T2451` = 9d96189. Scratch files in the scratchpad `T2451/`.

## 1. Diff and file
```
$ git diff --stat main...t/T2451
 RBM3D/BA/TwistLoop.lean | 904 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 904 insertions(+)
$ git diff --stat main...t/T2451 -- RBM3D/BA/TwistPins.lean RBM3D/BA/TwistStep.lean RBM3D/BA/TwistStep2.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ grep -nE "sorry|admit|native_decide|^axiom| axiom " RBM3D/BA/TwistLoop.lean      (no output)
$ grep -nE "Step2Gen_|STthetaOpg" RBM3D/BA/TwistLoop.lean | wc -l
       0
$ for n in baTwistLoopStep_of_fixed baTwistLoopStep_caseI baTwistLoopStep_caseII BATwKcircBound baTwKcircBound_holds; do git grep -c "$n" main -- RBM3D | wc -l; done
       0 (each of the five)
```
Only the sole writable file `RBM3D/BA/TwistLoop.lean` is touched (the reserve `TwistLoop2.lean` is unused; `RBM3D.lean` is left for the hub's merge step). 904 lines, below the 2,000 stop line. The public declarations are exactly the five target names (lines 696, 705, 709, 725, 758). Every other declaration is `private` with the stem `TwistLoop_`.

## 2. Build and axioms
```
$ lake build RBM3D.BA.TwistLoop; echo exit=$?
✔ [4061/4061] Built RBM3D.BA.TwistLoop (10s)
Build completed successfully (4061 jobs).
exit=0
$ grep -c "TwistLoop.lean" build2.txt        (warnings/errors located in the new file)
0
```
The scratch file `Audit.lean` contains the whole check file `docs/tickets/checks/T2451-check.lean` with `import RBM3D.BA.TwistLoop` added, plus these lines:
```
example : T2451_TL2e := baTwistLoopStep_of_fixed
example : T2451_TL2e = (∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R) := rfl
example : ∀ d, T2451_TwKcircBound d = BATwKcircBound d := fun _ => rfl
example (d : ℕ) : T2451_TwKcircBound d := baTwKcircBound_holds d
#print axioms (the four theorems)
$ lake env lean Audit.lean; echo exit=$?       (errors: none)
exit=0
'RBM.BA.baTwistLoopStep_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistLoopStep_caseI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistLoopStep_caseII' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwKcircBound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The registry check, run with `Test/Axioms.lean` unchanged:
```
$ printf 'import RBM3D\nimport RBM3D.BA.TwistLoop\n#assert_rbm_axioms\n' > Assert.lean; lake env lean Assert.lean   exit=0
axiom audit: 13274 theorems, 4162 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.BATwistAvgLaw: 1 [no certificate]
  RBM.BA.BATwistLoopLaw: 0 [no certificate]
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
$ (same, `import RBM3D` only)  axiom audit: 13270 theorems, 4161 definitions, 0 axioms ...
$ diff <(grep -v "axiom audit:" assert0_out.txt) <(grep -v "axiom audit:" assert_out.txt) && echo identical
premise/registry lines identical
```
The new file adds 4 theorems and 1 definition. Premise and registry lines are unchanged, and both owed lines are still present.

## 3. Statements against the pins (script diff)
```
$ diff <(sed -n '/^def T2451_TwKcircBound/,/eta n (t n))⁻¹$/p' check.lean | sed 's/T2451_TwKcircBound/X/') \
       <(sed -n '/^def BATwKcircBound/,/eta n (t n))⁻¹$/p' TwistLoop.lean | sed 's/BATwKcircBound/X/')
target 3: identical up to name (10 lines)
check :   ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R
lean  : theorem baTwistLoopStep_of_fixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : BATwistStepFixed d R) :
            BATwistLoopStep d R
```
The `rfl` equalities in §2 also confirm target 1 = `T2451_TL2e` (binders as arguments) and target 3 = `T2451_TwKcircBound`.

- **Target 1** `baTwistLoopStep_of_fixed`. It holds for every `d` and every `R`, with no added premise. The conclusion `BATwistLoopStep d R` (`TwistPins:160`, frozen, untouched) has the following shape:
  - the frame `BATwFrame` (`TwistPins:146`) puts `3 ≤ d`, `κ ε 𝔡 > 0` and `Cd > 0` before `∃ 𝔠d ∈ (0,1/100]`, and this before `∀ 𝔠 sz z`, `BAFlow`, `0 ≤ s < t ≤ T₀`, `R`, `STConStInd 𝔠d` and `twSteps`;
  - the step is `BATwistLoopLaw C μ s → ∀ τ ∈ [s,t], BATwistLoopLaw C μ τ`, at exponent 3/2.

  The proof takes `𝔠d` from `h` at the same `(κ, ε, 𝔡, Cd)` and passes `h`'s per-`Ξ` conclusion to the private `TwistLoop_core` (net plus bootstrap). Parameter order and windows are the pin's. **PASS.**
- **Target 2** `baTwistLoopStep_caseI/II (d) : BATwistLoopStep d STCaseI / STCaseII`. These are target 1 at the merged `baTwistStepFixed_caseI/II`. The statement is the check-file Prop `∀ d, BATwistLoopStep d STCaseI ∧ BATwistLoopStep d STCaseII`, and the acceptance `example` compiles (line 715). **PASS.**
- **Target 3** `BATwKcircBound` / `baTwKcircBound_holds`. Its structure matches `twK_bound` (`TwistPins:122`):
  - `∃ C > 0` depends only on `(d, κ, ε, 𝔡)` and comes before `𝔠, sz, z`;
  - the `t` window is `[0, T₀]`;
  - `∀ᶠ n` comes before `∀ σ c₁ c₂`;
  - both conjuncts are present: `‖K̃^∘‖ ≤ C·Bctl` and `Σ_a‖K̃^∘‖ ≤ C(W^dη)⁻¹`.

  The `M`-term is `W^{-d}·M^{(B)}(σ 1)_{a c₁}·M^{(B)}(σ 0)_{c₂ a}` through `twMB`/`BAMsigma`, as the pin requires. **PASS.**

## 4. Vacuity, hidden hypotheses, cycles
- No new structure. `BATwKcircBound` is a `def` of a plain `Prop` with no fields. The private `def`s `TwistLoop_Unif`, `TwistLoop_Pt` and `TwistLoop_Step` (lines 388, 394, 532) appear in no public statement.
- No public theorem takes `twSteps` or a good-event `Prop` as an explicit hypothesis. The only hypotheses are those inside the merged `BATwFrame`/`BATwistLoopStep`, as the ticket requires.
- No cycle. The new file imports only merged modules (`TwistStep2`, `TwistFold2`, `TwistKer2`, `TwistKer`, `EMn2BA`, `EKPins`, `KBase`, `Step1Setup`, `Induction/ContinuityNet`), and nothing on `main` imports `TwistLoop`.
- `open private` (lines 59-61) only reads merged private lemmas. No merged file is edited.
- External hypotheses: none new. `twSteps` (owners U3s1, T7-BA) and `BATwistLoopLaw` at `s` (owed, BA-V) are frame premises that were already merged.

## 5. Compiled nonempty instances (in `RBM3D/BA/TwistLoop.lean`, all compiled in the build of §2)
| endpoint | line | concrete data | discharged | left as hypotheses |
|---|---|---|---|---|
| T1 | 712, 718 | `d = 3`, `R = STCaseI` | `h := baTwistStepFixed_caseI 3` | none |
| T2, `STCaseI` | 841 | `sz0`, `zSeq`, `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `s ≡ 1/2 < t ≡ 2/3` | `flow_sz0`, `t0_sz0`, `STCaseI` (proved: `λ²/L² ≤ 1/3`, `L_n = 4(n+1)`), `s1Setup_conStInd_const` | `twSteps … Cd`, TL2 at `s`, `Cd > 0`, `τ ∈ [s,t]` |
| T2, `STCaseII` | 869 | `TwistStep2_szII`, `TwistStep2_zII`, `κ=3/5000`, `ε=1/2`, `𝔡=1/10`, `𝔠=1/9`, `s ≡ 0 < t ≡ 1/2000` | `TwistStep2_flowII`, `STCaseII` (`1 ≤ 25/16`), `conStInd_const` (with `W_n = n+25 → ∞` proved) | same |
| T3 | 889 | `sz0`, `zSeq`, `t ≡ 1/2`, `σ = ![false,true]`, `c₁ = 0`, `c₂ = ![1,1,0]` | `flow_sz0`, `half_lt_t0`, `0 ≤ 1/2` | none |

- Every deterministic hypothesis is discharged.
- The ones left open are other gates' pins or owed lines, as the ticket's item 4 allows: `twSteps` (Steps 1-4) and `BATwistLoopLaw` at `s`.
- No degenerate data: `s < t` strictly, `L_n ≥ 4`, `W_n ≥ 25`, no `False` premise, and `c₁ ≠ c₂` in T3.
- The conclusions have the check-file shapes: `BATwistLoopLaw … τ` for every `τ ∈ [s,t]`, and both conjuncts of T3.

## 6. Paper deltas
- The prove report `(d)` gives "none new (`T2451a`: none)". The deterministic level `Ξ_n` iterated by the bootstrap is the existing candidate `T2441a`, which the ticket names. Target 1 adds no statement difference beyond `T2441a`, since `BATwistLoopLaw` is the merged pin at exponent 3/2.
- Target 3 states the `Bctl` form `‖K̃^∘‖ ≤ C W^{-d}B_{u,0}`, weaker than TP T.13 (ii) `C W^{-d}B_{u,|a−c₁|}`, which has decay in `|a − c₁|` (`T2398-TL-proofs.md:189`). This is the binding pin the dispatcher chose (design D3, `T2413-design.md:56-57`; check-file docstring). T.13 is a project derivation (TP); the paper's TeX has no twisted-loop statement (`grep -n twist paper/tex/*.tex`: only a commented remark at `3_5:1772`). So it is not a Lean/paper statement difference, and the coverage criterion is met. See O1.

## 7. Observations (no RETURN)
- **O1.** The dispatcher may want to record target 3's dropped decay in `|a − c₁|` next to `twK_bound`'s identical `Bctl` form (design D3), since target 3 is TL's output to L4b2. Neither the ticket nor the prove report lists it as a candidate; D3 records it as a design decision.
- **O2.** The prove report's axiom list includes `#print axioms BATwKcircBound`, which is a `def`. This is harmless.

## Verdict
| target | verdict |
|---|---|
| 1 `baTwistLoopStep_of_fixed` | PASS |
| 2 `baTwistLoopStep_caseI`, `baTwistLoopStep_caseII` | PASS |
| 3 `BATwKcircBound`, `baTwKcircBound_holds` | PASS |
| 4 instances | PASS |

**T2451: PASS.** No dispatcher sign-off is needed for the merge. The closing REQ of stage TL (C1-C6) is the dispatcher's own follow-up under the ticket.
