Auditor model: claude-opus-5-5

# T2275 audit (round 1): UN-18b `Universality/Apriori`. Verdict: PASS

Written Tue Oct  6 09:21:43 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2275-audit1`, detached at `c05917a` (= `t/T2275`); merge-base with `main` = `e2703ec` = `main` HEAD.

## 1. Diff scope (`git diff --stat main...t/T2275`; registry diff)
```
 RBM3D/Test/Axioms.lean          |   1 -
 RBM3D/Universality/Apriori.lean | 407 ++++++++++++++++++++++++++++++++++++++++
 2 files changed, 407 insertions(+), 1 deletion(-)
@@ -194,7 +194,6 @@ def owedProps : List Name :=
-   `RBM.Univ.UNApriori, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```
Only the two sole writable files. The registry change is exactly the one deletion the ticket asks for; no merged file or frozen signature is touched. `grep -c UNApriori` on Axioms.lean: main 1, branch 0.

## 2. Build (`lake build RBM3D.Universality.Apriori`, audit worktree)
```
✔ [3334/3334] Built RBM3D.Universality.Apriori (5.6s)
Build completed successfully (3334 jobs).
exit=0
```
The only warnings are long-line warnings in merged upstream files (`Defs/Tail.lean`, `Universality/InjSum.lean`). None are in `Apriori.lean`.
`grep -nE "variable|structure|class |instance|attribute|axiom|sorry|admit|native_decide|maxHeartbeats" Apriori.lean` gives one hit, `346:` (a doc comment containing "instances"). So there are no `variable` binders, no new structures or classes, and no forbidden tokens.

## 3. Statements against the ticket's pins (script)
Script: the ticket check file `docs/tickets/checks/T2275-check.lean` with `import RBM3D.Universality.Apriori` added, plus these lines before `end RBM.Univ.T2275Check`. Each line elaborates only if the library statement is definitionally the pinned `Prop`.
```
example : T2275_apriori_im_bounds := @RBM.Univ.apriori_im_bounds
example : T2275_apriori_im_le_of_near := @RBM.Univ.apriori_im_le_of_near
example : T2275_apriori_ouMat_zero_integral := @RBM.Univ.apriori_ouMat_zero_integral
example : T2275_apriori_bctl_le := @RBM.Univ.apriori_bctl_le
example : T2275_unApriori_of_trLocal := @RBM.Univ.unApriori_of_trLocal
example : T2275_unApriori_band_of_rows := @RBM.Univ.unApriori_band_of_rows
example : T2275_inst_unApriori_band_zero := RBM.Univ.AprioriInst.inst_unApriori_band_zero
example : T2275_inst_unApriori_band_one := RBM.Univ.AprioriInst.inst_unApriori_band_one
example : T2275_inst_im_le_of_near := RBM.Univ.AprioriInst.inst_im_le_of_near
example : T2275_inst_bctl_le := RBM.Univ.AprioriInst.inst_bctl_le
```
`lake env lean $S/check.lean`: `check_exit=0`, 0 `error` lines.

Library signatures (from `Apriori.lean:149-151, 337-339`):
```
theorem unApriori_of_trLocal (d : ℕ) (hd : 3 ≤ d) (𝔠 𝔡 : ℝ) (sz : Sizes d)
    (hA : sz.Admissible 𝔠 𝔡) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ)
    (hD : UNDens m E ρ δ) (hT : UNTrLocal sz M m E δ) : UNApriori sz M E
theorem unApriori_band_of_rows (hT : UNTrLocalBandRow) (hD : UNDensBandRow) (hL : UNLocAvgBand)
    (d : ℕ) (hd : 3 ≤ d) (𝔠 𝔡 : ℝ) (sz : Sizes d) (hA : sz.Admissible 𝔠 𝔡) (κ : ℝ) (hκ : 0 < κ)
    (E : ℝ) (hE : |E| ≤ 2 - κ) : UNApriori sz (UNModel.band sz) E
```
Consumer binders (`Pins.lean:745-749`, `UNUnivMainRow`):
```
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens m E ρ δ → UNTrLocal sz M m E δ → UNClaimAll sz M E →
```
- Target 5's conclusion is the merged pin `UNApriori sz M E` (`Pins.lean:522-525`) with nothing restated: it keeps `∀ p, ∀ ε > 0, ∀ᶠ n`, the scale `N = Nsz sz n`, `z₀ = E + i N⁻¹`, and the `ouP` expectation of `ouMat M n 0`. It holds for every `M : UNModel sz` (model-generic, §57 (2)), so it is not a band-only special case. Its premises are exactly `UNUnivMainRow`'s `hA`, `UNDens`, `UNTrLocal`, with one `m` and one `δ` shared by both, as the ticket requires (vii).
- Target 6 feeds `UNDensBandRow`'s `δ ≤ κ/2` and `UNDens.1 : 0 < δ` into `UNTrLocalBandRow` (`Pins.lean:842-845`), matching the ticket's band-row design.
- Targets 1-4 match pins 2.1-2.4: same hypotheses, `0 < η₀ ≤ η₁`, the WO lower half `W^{-d/2+𝔡} ≤ lam n`, `η > 0`, and target 3 for every `g` with no measurability assumption.
- Quantifier order is the paper's: fixed `p, ε` come before `∀ᶠ n`. The proof uses one `filter_upwards` threshold, `[hev, hbig, hN1', hdens, hA.2.2.2.2]` (`Apriori.lean:172`). It sets `τ = min (ε/(4(p+1))) (1/2)` and `D = p+1` (`:154`, `:167`), as the ticket's §29 checklist specifies.

Target 1 `apriori_im_bounds`: PASS. Target 2 `apriori_im_le_of_near`: PASS. Target 3 `apriori_ouMat_zero_integral`: PASS. Target 4 `apriori_bctl_le`: PASS. Target 5 `unApriori_of_trLocal`: PASS. Target 6 `unApriori_band_of_rows`: PASS.

## 4. Vacuity, hidden hypotheses, cycles
- None of the six targets has a hypothesis inside a structure field. The premises are registered `Prop`s: `UNTrLocal` (owed), `UNDens` and `Admissible` (structural), and `UNTrLocalBandRow`, `UNDensBandRow`, `UNLocAvgBand` (owed). The rest are plain inequalities.
- No cycle: the imports are `RBM3D.Universality.OU`, `RBM3D.Universality.InjSum` and `Mathlib.MeasureTheory.Integral.Prod`, all merged on `main`. `UNApriori` is not assumed anywhere in the file.
- External/owed hypothesis `UNTrLocal`: it is an owed MA/BA pin (`Pins.lean:447`), not a new external input. Concrete limit check at the band model, `m = msc`:
  - its error `W^τ Bctl n (1-η)` is at least `W^τ (Nη)⁻¹`, the standard averaged-law error, and `Bctl n 0 ≥ W^{-d}`;
  - its bad-event bound `N^{-D}` tends to 0 because `N = (WL)^d → ∞` (`SizeTendsto`).
  So the hypothesis is not a `False` premise at `sz0`. The preflight's numeric table (prove report (a)(ii)) confirms `Bctl n (1-η₁) ≤ W^{-2𝔡} + N^{-τ'} ≤ 2` at `n = 0`.
- Registry pre-check: scratch `$S/ax.lean` = `import RBM3D` + `import RBM3D.Universality.Apriori` + `#print axioms …` + `#assert_rbm_axioms`, run after `lake build RBM3D.Test.Axioms`. Result: `ax_exit=0`. The output contains no `UNApriori`, `none of the ledgers` or `unregistered` (`grep -c` = 0). Owed count from the output: `registry: 2 borrowed + 148 owed + 103 structural + 7 refuted + 12 superseded`.

## 5. Compiled nonempty instances (same file, `RBM.Univ.AprioriInst`)
Each instance discharges every deterministic hypothesis at concrete data:

| target | instance | data and discharged hypotheses | kept hypothesis (owed pin) |
|---|---|---|---|
| 5 | `inst_unApriori_band_zero` (`:355`) | `d = 3`, `le_rfl`, `𝔠 = 1/6`, `𝔡 = 1/10`, `sz0`, `UNInst.sz0_adm`, band model, `msc`, `E = 0`, `ρ = rhoSC 0`, `δ = 1/2`, `un_dens_msc_zero` | `UNTrLocal sz0 band msc 0 (1/2)` |
| 6 | `inst_unApriori_band_one` (`:363`) | `sz0`, `κ = 1/2` (`norm_num`), `E = 1` (`abs_one; norm_num`) | `UNTrLocalBandRow`, `UNDensBandRow`, `UNLocAvgBand` |
| 2 | `inst_im_le_of_near` (`:370`) | `H = 0 : Matrix (Fin 1) (Fin 1) ℂ`, `isHermitian_zero`, `η₀ = 1/2 < η₁ = 1`, `w = m(i)`, `ζ = 0` (`by simp`) | none |
| 4 | `inst_bctl_le` (`:379`) | `sz0`, `n = 0`, `𝔡 = 1/10`, `η = 1/2`; the WO premise is proved from `sz0_values` (`32^{-7/5} = 2^{-7} ≤ 1/64`) | none |
| 1 | `inst_im_bounds` (`:392`) | `1×1` zero matrix (nonempty index), `η = 1` | none |
| 3 | `inst_ouMat_zero_integral` (`:400`) | `sz0`, band, `n = 0`, `g ≡ 1` | none |

None of them uses `N = 0` (`N = 2^21` at `sz0`, `n = 0`), an empty index, a collapsed window, a `False` premise or an astronomically large witness. Instances (a), (b), (c) and (d) also elaborate against the check file's pins 2.7 (§3 above).

## 6. Axioms (`lake env lean $S/ax.lean`, verbatim)
```
'RBM.Univ.apriori_im_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.apriori_im_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.apriori_ouMat_zero_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.apriori_bctl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unApriori_of_trLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unApriori_band_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_unApriori_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_unApriori_band_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_im_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_bctl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_im_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_ouMat_zero_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 7994 theorems, 2619 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Name-clash grep: `grep -rnw --include='*.lean'` for the six target names and `AprioriInst` in `RBM3D` and `RBM3D.lean`, excluding the new file, gives `0` hits.

## 7. Paper deltas
- The Lean statement of `UNApriori` is the merged pin; it is not changed. The only difference from the source is a design difference: the pin is proved for every model, conditionally on `UNTrLocal`, with `Bctl`/`(eq:WO)` in place of RBM2D's `Meta`. The report proposes this as **T2275a** (prove report (d)). Coverage is complete.
- No `T2275c` candidate. None is needed: the statements equal the check file (§3).

## 8. Observations (no effect on the verdict)
1. On the branch alone, the root `#assert_rbm_axioms` reports `UNApriori` as unledgered until the hub adds `import RBM3D.Universality.Apriori` to `RBM3D.lean` at merge (rule (A) step 4). The prove report records this in (b) and (d). The pre-check in §4 above, with that import, passes.
2. Prove report (b), "Port": a parenthetical remark sits inside the fenced `diff --stat` output block. This is formatting only.

## Verdict
T2275: **PASS**, all six targets and all six instances. No repair list; no dispatcher sign-off needed.
