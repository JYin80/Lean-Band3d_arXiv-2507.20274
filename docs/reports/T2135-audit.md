Auditor model: claude-opus-5-5

# T2135 audit (round 1): S3-07b `Induction/DecayLoopB`. Written Sun Oct  4 14:55:02 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2135-audit1`, detached at `t/T2135` = `7f58247`; merge-base with `main` = `549a62d` (= main HEAD).
Scratch files: `scratchpad/T2135/` (`audit.lean`, `build.log`, `pt*.txt`, `u*.txt`).

## 1. Build, hygiene, diff scope

```
$ lake build RBM3D.Induction.DecayLoopB
✔ [3766/3766] Built RBM3D.Induction.DecayLoopB (19s)
Build completed successfully (3766 jobs).
exit 0          (0 warning lines mention DecayLoopB.lean)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/DecayLoopB.lean | wc -l
       0
$ grep -nE "^(structure|class|instance|axiom|opaque)" RBM3D/Induction/DecayLoopB.lean | wc -l
       0
$ grep -n "^import" RBM3D/Induction/DecayLoopB.lean | cut -d' ' -f2 | tr '\n' ' '
RBM3D.Induction.DecayLoopA RBM3D.Induction.KDecay RBM3D.Induction.Step34Pins RBM3D.Induction.HierAlgebra RBM3D.Induction.Split
$ git diff --name-only main...HEAD
RBM3D/Induction/DecayLoopB.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep "^[+-]"      (one registry line)
+   `RBM.Gauss.Sizes.STGdecayW, -- `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]` (...): hypothesis of `stDecayLoopU_of_step2` (T2135 Amend 1, DECISIONS §39); proved by the Step 2 chain ST2-04 (DECISIONS §20 rule: owed)
```
The diff touches only the two sole writable files. No merged file and no frozen signature is touched. Every import is a merged module, so there is no cycle.

Axioms (`lake env lean scratchpad/T2135/audit.lean`, exit 0):
```
'RBM.Gauss.Sizes.stEtermDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDecayLoopU_of_step2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STDecayLoopU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.far_cutGlueL_or_far_cutGlueR' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.norm_glueTerm_le_of_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.norm_sum_SB_le_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.eeLoop_WF' depends on axioms: [propext, Quot.sound]
'RBM.Gauss.DecayLoopBInst.DecayLoopB_sz0_far_nonempty_EK' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Target 3 (Amend 1): `STDecayLoopU`, `stDecayLoopU_of_step2`

Pin: `STDecayLoopPT` with `Prec` in place of `PrecPT`, and the hypotheses of `stDecayLoopPT_of_step2` with `STGdecayW sz E s t Cd` in place of `STStep2DecayPT`. Script diff against the merged forms:
```
$ diff <(sed -n 106,116p DecayLoopA.lean) <(sed -n 792,800p DecayLoopB.lean)   [STDecayLoopPT vs STDecayLoopU]
1c1
< def STDecayLoopPT (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
> def STDecayLoopU (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
3c3
<     PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
>     Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
10,11d9   (< blank line, < `end RBM.Gauss.Sizes`: outside the def)
$ diff <(sed -n 970,973p DecayLoopA.lean) <(sed -n 1637,1640p DecayLoopB.lean)
1c1
< theorem stDecayLoopPT_of_step2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
> theorem stDecayLoopU_of_step2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
4c4
<     (hD : STStep2DecayPT sz Cd (STflowE z) s t) : STDecayLoopPT sz (STflowE z) s t := by
>     (hD : STGdecayW sz (STflowE z) s t Cd) : STDecayLoopU sz (STflowE z) s t := by
```
`STGdecayW` (`Step34Pins.lean:208`) and `STStep2DecayPT` (`Step2Defs.lean:287`) have the same bound text, with `Prec` and `PrecPT` respectively (read side by side). `Prec` is `StochDomAt`, uniform; `PrecPT` is `PerTimeDomAt` (`StochDomAt.lean:121,125`). The statement therefore matches Amend 1 exactly.
- External hypothesis: `STGdecayW` is the merged Step-2 pin, owed (ST2-04) and registered in `owedProps`. It is not new to this ticket.
- Non-vacuity: `DecayLoopB_sz0_far_nonempty_U` (line 2360, compiled) shows that the far set of `STDecayLoopU` is nonempty at `sz0` for every `n`.
- Special case: the theorem covers the flow energy `E = STflowE z` with `t ≤ lemT z`, as in the merged PT form. The report (d) says so.
- Instances (lines 2399 and 2406, compiled): `sz0`, `z0`, `flow_z0`, window `[0,1/16]`, any `Cd`, and the application at `k=3, τ'=1/10, D'=1`. `STGdecayW` is the only hypothesis left; every deterministic hypothesis is discharged. Nondegenerate.

**Verdict target 3: PASS.**

## 3. Target 2: `stEtermDecay`

Statement (lines 2209-2224, quoted in prove report (b)):
- Hypotheses: `3 ≤ d`, `0 < κ`, `|E n| ≤ 2-κ`, `sz.Admissible 𝔠 𝔡`, `0 ≤ s n ≤ t n < 1`, and `STDecayLoopU sz E s t` (as Amend 1 requires); then `∀ k ≥ 2, ∀ σ`.
- Conclusion: a conjunction of `STEKDecay sz s t` for `a ↦ STegt …⟨ofFn σ, ofFn a⟩`, for `∀ l, a ↦ STksimLK … l …`, for `a ↦ STelklk …`, and (with `m := k+k`) for `b ↦ STee … σ (b ∘ castAdd) (b ∘ natAdd)`.

Comparison with the ticket and the consumers:
- The tensor type `∀ n, TimeIcc s t n → SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ` is exactly the `𝒜` argument of `STEKSumRes1/Res2NAL/Res2` (`Step34Pins.lean:628,641,655`, read). `m = k ≥ 2`, and `2k ≥ 2` for `STee`, so the consumers' `2 ≤ n_` is met.
- `STEKDecay` uses `Whp{∀ v ∈ TimeIcc, EKFastDecay … (v:ℝ) …}`. The terms are evaluated at `τ = v`, so the time of `ℓ_v` and the time of the term agree.
- `STKbound` and `STKcalDecay` are not hypotheses: they are derived from the merged `stKbound_timeIcc` and `inst_stKcalDecay_admissible`, which matches the ticket's "crude bounds" route.
- The `l¹ → l^∞` adjustment (`τ' = ε/2`) is internal and is stated in report (a) row 1.
- The quantification over `l` for `STksimLK` is stronger than the paper's range `3 ≤ l ≤ n`. This is a valid strengthening, and it is covered by T2135c.

No hidden hypothesis (the file has no structure or class) and no cycle. The input `STDecayLoopU` is this ticket's target 3. The chained example at line 2446 reduces it to `STGdecayW`.

Instances (compiled, in the file):
- Line 2425: `sz0`, `κ=1/10`, `𝔠=1/6`, `𝔡=1/10`, `E = STflowE z0` (`inst_hE` proves `|E| ≤ 2-1/10`), window `[0,1/16]`, `k=2`, `σ=(+,-)`. The only hypothesis left is `hU : STDecayLoopU …`.
- Line 2446: targets 3 and 2 chained at `k=3`; the only hypothesis is `STGdecayW`.
- `DecayLoopB_sz0_far_nonempty_EK` (line 2459) shows that the `EKFastDecay` far premise (`ε=1/10`) is nonempty for every `n`. The conclusion is therefore not vacuously true at the instance.

**Verdict target 2: PASS.**

## 4. Target 1: deterministic decay through cuts (namespace `RBM.Ind`)

Statements (prove report (b) extraction, re-read in the file at lines 55, 61, 67, 96, 105, 177, 303, 346, 370, 437, 461-481):
- `LoopDecay` is as pinned (WF loops with length `≤ N` and two labels at `zdistInf ≥ R` give `‖F J‖ ≤ δ`); `.mono` and `.sub` are present.
- `far_cutGlueL_or_far_cutGlueR` has hypotheses `2R+1 ≤ |x-y|_∞` and `|α-β|_∞ ≤ 1`, as pinned.
- The window sums use the merged `SB d L g` (the ticket asks which `S`; the answer is `SB`, not `svar`). The bound is `(2R+1)^d M + L^d δ`.
- `glueTerm`, `norm_glueTerm_le_of_far`, and the anchors `exists_anchor_cutGlueL/R` (built on the merged `LoopIdx.cutGlueL/R`) are present.
- The `STeeLoop` lemmas are `length_eeLoop` (`= 2·|a|+2`), `eeLoop_WF`, and `mem_eeLoop_left/right`.
- Extra hypothesis `3 ≤ L` on the window and glue lemmas: covered by T2135a.

Instances in the file, at `d=3`, `L=5`, loop `σ=(+,-,+)`, `a=(0,(2,2,2),0)`, `R=1/2`, `|0-(2,2,2)|_∞ = 2 = 2R+1`:
- line 2283: `norm_glueTerm_le_of_far`;
- line 2288: `norm_sum_SB_le_left`;
- line 2303: `length_eeLoop`, `eeLoop_WF`, `mem_eeLoop_right`;
- line 2311: the anchors.

All are nondegenerate, and every hypothesis is discharged (the module builds).

Auditor's independent non-vacuity check. The following have no direct `example` in the file, so I compiled them in `scratchpad/T2135/audit.lean` (exit 0, output in §1) at the same concrete data:
- `far_cutGlueL_or_far_cutGlueR` (cut `(1,2)`, `α=0`, `β=(1,1,1)`, `|α-β|_∞=1`, `x=0`, `y=(2,2,2)`, `R=1/2`);
- `norm_sum_SB_le_right`;
- `mem_eeLoop_left`;
- `LoopDecay.sub` followed by `.mono` (`N: 6→4`, `R: 1→2`, `δ: 1/5→1/2`);
- a concrete `LoopDecay 3 5 6 1 (1/10)` witness.

**Verdict target 1: PASS.**

## 5. Paper-delta coverage

The report (d) proposes:
- T2135a: target 1 has no paper pin; `3 ≤ L`.
- T2135b: a uniform-in-`u` input, `STDecayLoopU`/`STGdecayW` (`Prec`), instead of the per-time `STDecayLoopPT` (`1_2:1371`).
- T2135c: the following differences in `stEtermDecay`:
  - `STksimLK` is stated for every `l` (paper `3 ≤ l ≤ n`);
  - `STee` is stated as a tensor of the `2k` labels;
  - `ε → ε/2` (`l¹/l^∞`);
  - the extra hypotheses `0 ≤ s ≤ t < 1`, `|E| ≤ 2-κ`, `Admissible`.

The special case `E = STflowE z` of `stDecayLoopU_of_step2` is stated in (d) and is inherited from the merged `stDecayLoopPT_of_step2`. Every Lean/paper difference I found is covered.
```
$ grep -c "T2135" docs/paper-deltas.md
0          (candidates only, as required; the dispatcher numbers them)
```

## 6. Observations (no RETURN)

- O1. Some target-1 lemmas have no direct `example` in the file: `far_cutGlueL_or_far_cutGlueR` (it is exercised inside the line-2283 instance), `norm_sum_SB_le_right`, `LoopDecay.mono/.sub` and `mem_eeLoop_left`. The ticket asks for "target 1 on concrete loops", and the line-2283/2288/2303/2311 examples meet that. The auditor's scratch compile (§4) confirms that each of these lemmas holds at nondegenerate data.
- O2. Report (b) uses the cruder degree `D'' = D + 1 + (2k+4)/𝔠`, not row 10's `D + (m+2)/𝔠 + 1`. This is internal to the proof (`STDecayLoopU` holds for every `D'`), so no statement changes.

## Verdict

| Target | Verdict |
|---|---|
| 1 deterministic cuts (`LoopDecay`, anchors, `far_cutGlueL_or_far_cutGlueR`, `norm_sum_SB_le_left/right`, `glueTerm`, `norm_glueTerm_le_of_far`, `eeLoop` lemmas) | PASS |
| 2 `stEtermDecay` | PASS |
| 3 `STDecayLoopU`, `stDecayLoopU_of_step2` | PASS |

**T2135: PASS.** No dispatcher sign-off needed.
