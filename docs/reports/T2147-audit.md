Auditor model: claude-opus-5-5

# T2147 audit (round 1) — S5-04 `Induction/TailtoTail` (`STTailtoTail`, `(neiwuj)`)

Date: Sun Oct  4 17:51:48 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2147-audit1`, detached at `t/T2147` = `58abe97`.

## 1. Statement (target 1: `stTailtoTail_holds (d : ℕ) : STTailtoTail d`)

The ticket pins the merged statement unchanged. Type as elaborated, and the pin is untouched by the branch:
```
$ lake env lean scratchpad/T2147/ax.lean      # import RBM3D.Induction.TailtoTail; #check ...
stTailtoTail_holds : ∀ (d : ℕ), STTailtoTail d
$ git diff main...t/T2147 -- RBM3D/Induction/Step5Pins.lean | wc -l
       0
$ sed -n 582,588p RBM3D/Induction/TailtoTail.lean
theorem stTailtoTail_holds (d : ℕ) : STTailtoTail d := by
  intro hd
  refine ⟨(3 * Real.exp ((4 * (d : ℝ) + 1) / 4)) ^ 2, by positivity, ?_⟩
  intro L hL g W D s t hg hW hs hst ht hgt m hm σ A hA
  have : NeZero L := ⟨by omega⟩
  intro a
  exact tailtoTail_main hL (by omega) hW hs hst ht hgt hm σ A hA a
```
The pin (`Step5Pins.lean:121-128`, merged T2138) against the paper (`3_5_Loop_Hierarchy.tex` lemma `TailtoTail`, `(neiwuj)`):
```
def STTailtoTail (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (_hL : 3 ≤ L) (g W D s t : ℝ), 0 < g → 0 < W → 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin 2 → Bool, ∀ A : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) →
        haveI : NeZero L := ⟨by omega⟩
        ∀ a, ‖UN d L g (EKsgn m σ) s t A a‖ ≤
          C * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D)
paper: "Suppose 1-s ≥ 1-t ≥ ilambda^2 and |A_a| ≤ T_{s,D}(|a_1-a_2|) ... for some constant D>0. Then
        (U^{(2)}_{s,t,σ} ∘ A)_a ≲ T_{t,D}(|a_1-a_2|) + (|1-s|/|1-t|)^2 W^{-D}."
```
- Hypotheses: `0 ≤ s ≤ t < 1`, `g² ≤ 1−t` match `1−s ≥ 1−t ≥ ilambda²`; all four charges `σ : Fin 2 → Bool`; `|m| = 1`; `C` chosen before `L, g, W, D, s, t, m, σ, A, a` (quantifier order correct, `C` depends on `d` only: `C = (3e^{(4d+1)/4})²`).
- Loss: the floor term is exactly `((1−s)/(1−t))² W^{−D}`, not weakened; `T_{u,D}` is `tailTD` (`Defs/Tail.lean`, `((W^d|1−u|)⁻¹)² e^{−√r} + W^{−D}`, `def_WTuD`).
- `D` ranges over all reals (paper: `D > 0`): stronger than the paper, not a special case.
- Distances `zdistInf` (paper `|·|`): DECISIONS §33 correction, recorded as D316.
Verdict on statement: matches the pin exactly; general, not a special case or conditional adapter.

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*structure|^\s*class |set_option maxHeartbeats" RBM3D/Induction/TailtoTail.lean
(no output)
$ grep -n "^import" RBM3D/Induction/TailtoTail.lean
import RBM3D.Induction.Step5Pins
import RBM3D.Kernel.Evolution
import RBM3D.Evolution.Pins
import RBM3D.Propagator.Props4
```
- No structure/class introduced; the theorem has no hypotheses beyond the pin's own (`3 ≤ d` is the pin's antecedent). `UN`, `uKer`, `EKsgn`, `cycProd` are plain merged `def`s (`Kernel/Evolution.lean:49,56,65`, `Evolution/Pins.lean:45`): `UN` is the full kernel sum `Σ_b ∏_i uKer(cycProd m i) s t (a i)(b i) · A b` with `uKer μ s t = (1 − sμS)Θ_{tμ}`, so the conclusion is not trivial.
- No external hypothesis (no `ThetaDecay`/`Step2LocalPT`/owed pin) enters: the axiom print below lists only the three standard axioms and the theorem is unconditional. No limit check needed.
- No cycle: imports are merged upstream modules only; `Step5Pins` is not modified.

## 3. Compiled nonempty instances (same file, lines 593-627)
```
$ sed -n 593p RBM3D/Induction/TailtoTail.lean
example : STTailtoTail 3 := stTailtoTail_holds 3
$ grep -nE "^(theorem|example)" RBM3D/Induction/TailtoTail.lean
582:theorem stTailtoTail_holds (d : ℕ) : STTailtoTail d := by
593:example : STTailtoTail 3 := stTailtoTail_holds 3
597:theorem inst_tailtoTail_zero :
612:theorem inst_tailtoTail_extremal :
```
`inst_tailtoTail_zero` (ticket instance) applies `stTailtoTail_holds 3 (by norm_num)` at `L = 3`, `g = 1/2`, `W = 2`, `D = 2`, `s = 0`, `t = 1/2`, `m = Complex.I`, `σ = ![true, false]`, `A = 0`, `a = ![0, ![1,0,0]]`; every hypothesis is discharged in the term (`by norm_num` for `3 ≤ 3`, `0 < 1/2`, `0 < 2`, `0 ≤ 0`, `0 ≤ 1/2`, `1/2 < 1`, `(1/2)² ≤ 1 − 1/2`; `by simp` for `‖I‖ = 1`; `tailTD_nonneg` for the `A` bound). `inst_tailtoTail_extremal` repeats it with the nonzero `A_b = T_{0,2}(|b₀−b₁|) ≥ 2^{−2}`. Nondegenerate: 27 lattice points, `0 < t < 1`, `ρ = 2`, `g² = 1/4 < 1/2`, `a₀ ≠ a₁`. Both compile (module build below) with standard axioms. Ticket instance requirement (`stTailtoTail_holds 3` and the bound at the listed data, `A = 0`) is met.

## 4. Build, axioms, diff scope
```
$ lake build RBM3D.Induction.TailtoTail 2>&1 | grep -E "error|sorry|Build completed"
Build completed successfully (3775 jobs).
$ lake env lean scratchpad/T2147/ax.lean
'RBM.Gauss.Sizes.stTailtoTail_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst_tailtoTail_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.inst_tailtoTail_extremal' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --name-only main...t/T2147
RBM3D/Induction/TailtoTail.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2147 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Gauss.Sizes.STTailtoTail, -- `(neiwuj)`, `tailtoTail` with the tail `T_{u,D}`: S5-04; S5-01 (T2138, DECISIONS §40: owed)
$ git -C /Users/junyin/Lean_proof/RBM3D grep -n "stTailtoTail_holds\|inst_tailtoTail_zero\|inst_tailtoTail_extremal" main -- RBM3D | wc -l
       0
```
- Only the two sole writable files are touched; the registry change is exactly the deletion of the `STTailtoTail` owed line (ticket: "delete ... add nothing"). No frozen signature changed.
- Registry pre-check / full `lake build` with the root import: run by the prover (report §(b): exit 1 without the import, listing exactly `[RBM.Gauss.Sizes.STTailtoTail]`; exit 0 with it). Not re-run here; the hub runs the full build at merge (rule (A) step 5).

## 5. Paper deltas
| Lean/paper difference | coverage |
|---|---|
| `T_{u,D}` of `def_WTuD`, `zdistInf`, explicit `C_d² T_{t,D} + ρ² W^{−D}`, `g² ≤ 1−t`, all charges | `docs/paper-deltas.md:1274` D316 (T2134b) |
| every real `D` (paper: `D > 0`); explicit `C = (3e^{(4d+1)/4})²` | candidate T2147a in the prove report |
| proof route (weighted resolvent bound instead of `prop:ThfadC` + continuum fact) | candidate T2147b (route only, no statement change) |
All statement differences are covered.

## 6. Observations (no effect on verdict)
- O1. Prove report (a) table states `C = 4e^{(4d+1)/2}`; the committed constant is `9e^{(4d+1)/2}`; corrected in (a′). No statement effect.
- O2. Public instance names `inst_tailtoTail_zero`/`_extremal` are not pinned; they carry the file-stem token `tailtoTail` and do not clash on `main` (grep 0). Acceptable under §3 (E).
- O3. `git diff main t/T2147` (two-dot) also shows `Evolution/CltPath`/`CltResolvent` because `main` advanced (T2144 merged after the branch point); the three-dot diff (merge scope) touches only the two writable files.

## Verdict
- Target 1 `stTailtoTail_holds`: **PASS** (statement = merged pin, unconditional, standard axioms, nonempty compiled instances at `d = 3`).
- No dispatcher sign-off needed.
