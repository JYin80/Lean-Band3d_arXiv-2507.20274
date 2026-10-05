Auditor model: claude-opus-5-5
# T2225 audit (round 1) — MA-03 `RBM3D/Main/FixedZ.lean`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2225-audit1`, detached at `t/T2225` = a1575d4; merge-base with `main` = f2766db (= `main` HEAD). `date -u`: Mon Oct  5 23:24:45 UTC 2026.

## 1. Scope of the diff
```
$ git diff --stat main...t/T2225
 RBM3D/Main/FixedZ.lean | 851 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   3 +-
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep -E "^[+-]"
-   `RBM.Gauss.Sizes.STExpIniIConcl'] -- conclusion of the initial term, ... (T2223, DECISIONS §20: structural)
+   `RBM.Gauss.Sizes.STExpIniIConcl', -- conclusion of the initial term, ... (T2223, DECISIONS §20: structural)
+   `RBM.Endpoints.locBad1] -- the bad event of `(G_bound)` in `locSC` (MA-01, `Endpoints.lean:136`); `¬ locBad1` is a hypothesis of the deterministic `decol_core` (MA-03, T2225, DECISIONS §20: structural)
```
Only the sole writable files; Axioms.lean change is the one registry line of Targets 3 (`]` moved). No merged file (`Endpoints.lean`, `ZTransfer.lean`, `Green/*`) touched.

## 2. Verbatim move (script, probe `git show 97d958e:RBM3D/Probe/T2192Pins.lean`)
```
C 1061-1092 lines 32 in text: True after previous: True
C 1131-1862 lines 732 in text: True after previous: True
C 2206-2234 lines 29 in text: True after previous: True
C 2453-2458 lines 6 in text: True after previous: True
$ diff blocks.txt FixedZ.lean | grep -E "^[0-9]" ; ... | grep -c "^<"
0a1,41
32a74
764a807,811
793a841
799a848,851
0
$ non-blank, non-comment added lines (diff "> " lines):
> Copyright (c) 2026 Jun Yin. ... / Released under Apache 2.0 ... / Authors: Jun Yin
> import RBM3D.Main.ZTransfer
> import RBM3D.Green.LDE
> (module docstring lines: MA-03, probe 97d958e, namespace mapping, D500/D502/D503 notes, consumers)
> set_option linter.style.longLine false / linter.unusedSectionVars false / linter.unusedVariables false
> noncomputable section
> open MeasureTheory ProbabilityTheory Filter Matrix Topology
> open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
> open scoped NNReal ENNReal
> namespace RBM.Endpoints
> namespace Inst
> open RBM.Gauss.SizesInst RBM.Univ.UNInst
> end Inst
> end RBM.Endpoints
$ sed -n 36,46p probe | diff - <(sed -n 30,41p FixedZ.lean)
11c11,12
< namespace RBM.Probe.T2192
---
> namespace RBM.Endpoints
>
```
Only the lines allowed by Targets 1; imports exactly the two of Targets 2, none added.

## 3. Statements against the pins (check file, compiled) and the paper
Scratch file = `docs/tickets/checks/T2225-check.lean` + `import RBM3D.Main.FixedZ` + 26 examples
(`X_pin = RBM.Endpoints.X := rfl` for the 4 pins; `Y_pin := @RBM.Endpoints.Y` for the 18 theorems, `zdistInf_neg_pin` for `zdistInf_neg'`; `Inst.T2225Check.Z_pin := @RBM.Endpoints.Inst.Z` for the 4 instances) + 22 `#print axioms`:
```
$ grep -c "^example : RBM.Endpoints" eq.lean
26
$ lake env lean eq.lean ; echo exit $?
exit 0
$ grep -c error eq.out
0
```
Declarations (script):
```
51:def locSCFixed : Prop :=            59:def QDiffFixed : Prop :=
73:def MAFixed : Prop := (∀ d : ℕ, UNMLOut d) → locSCFixed ∧ QDiffFixed
100:theorem locSCFixed_of_ML (hML : ∀ d, UNMLOut d) : locSCFixed := by
419:theorem QDiffFixed_of_ML (hML : ∀ d, UNMLOut d) : QDiffFixed := by
538:theorem fixed_of_ML : MAFixed := fun hML => ⟨locSCFixed_of_ML hML, QDiffFixed_of_ML hML⟩
787:def MADecol : Prop := locSC → decol
789:theorem decol_of_locSC : MADecol := by
813:theorem inst_decol_of_locSC (h : locSC) :          821:theorem inst_locSCFixed (hML : ∀ d : ℕ, UNMLOut d) :
830:theorem inst_QDiffFixed (hML : ∀ d : ℕ, UNMLOut d) : 843:theorem inst_decol_scalars :
```
Paper comparison (auditor's reading of `paper/tex/1_2_Intro_model_result.tex` and the merged definitions `Endpoints.lean:58-175`):
- `locSCFixed` vs `(G_bound)` `1_2:388`, `(G_bound_ave)` `1_2:391` "at each fixed z" (`1_2:1228`): `∀ d ≥ 3, 𝔠 𝔡, sz, Admissible` → `∀ κ ε τ D > 0` → `∀ᶠ n` → `∀ z ∈ 𝐃_{κ,ε}` → `P(locBad1z) ≤ N^{-D} ∧ P(locBad2z) ≤ N^{-D}`. `locBad1z`: `∃ x y, W^τ 𝓑_{η,distB} < |G_xy − M_xy|²` (squared, η = `z.im`); `locBad2z`: `∃ a, W^τ 𝓑_{η,0} < |W^{-d}∑_{x∈[a]} G_xx − m|` (not squared). Union over `x,y`/`a` inside, `z` outside, `N₀` uniform in `z` (stronger than "fixed z"; D500 reading, D501 `L^∞` block distance, D504 explicit form). PASS.
- `QDiffFixed` vs `(eq:diffu1,2)` `1_2:494,498`, `(Meq:QdS1,2)` `1_2:504,507`: probability halves via `qd1Badz/qd2Badz` (`∃ a b` inside, D503; bound `qdBound` = `W^τ min(𝓑_0^{1/5}𝓑_{W|a-b|}, 𝓑_0²)`); expectation halves `∀ a b, ‖∫ avg2(|G|²) − |m|²Θ^{+-}_{ab}/W^d‖ ≤ W^τ 𝓑_0²((λ²W^d)^{-1/5}+𝓑_0)` and the `GG` analogue with `m²Θ^{++}`; `N₀` uniform in `z, a, b` (D500). PASS.
- `MAFixed` = the paper's `1_2:1228` step with `ML:GtLocal`, `ML:GLoop` (n=1), `ML:GLoop_expec` as the owed hypothesis `∀ d, UNMLOut d` (registered owed, `Axioms.lean:192`). PASS (proved by `fixed_of_ML`).
- `MADecol := locSC → decol`: `decol` (merged MA-01) matches Thm 2.1 `1_2:357-370` (`∀ k, |μ_k| ≤ 2−κ`, `∀ x`, `|ψ_k(x)|² ≤ N^{-1+τ}`, prob `≥ 1−N^{-D}`, `∀ᶠ n` after `κ τ D`). It is an implication, not `decol`; `decol`/`locSC` stay owed (`Axioms.lean:239-240`), as the ticket states. Proof uses `η = N^{-1+min(τ/2,1/2)}` (D502). PASS.
All four pins and the 18 theorem statements equal the dispatcher's compiled pins (rfl / exact `@` term above).

## 4. Hidden hypotheses, vacuity, cycles
- The four pins are `def … : Prop` with every hypothesis in the binder list; no structure field carries a hypothesis. `Admissible`, `locDomain` are merged structural (`Axioms.lean:262-263`).
- External/owed hypotheses: `UNMLOut` (ST-6 pin, owed) and `locSC` (MA-04 pin, owed) only. Limit check for `locSC` along `sz0` is in the prove report (a) (`W^{τ_L}𝓑_{η,0}` = 0.788, 0.178, 0.0555, 0.00498 at n = 0, 10, 100, 10⁴); `UNMLOut` is a merged pin of another gate, not introduced here.
- `locSCFixed_of_ML`/`QDiffFixed_of_ML` split off `κ > 2`, `ε > 1` (empty domain, `locDomain_empty_*`); the main case is the nondegenerate one (`hne : ∀ n, Nonempty {z // locDomain κ ε n z}`).
- No cycle: imports are merged `Main.ZTransfer`, `Green.LDE`; `locSC`/`decol` appear only as the hypothesis/conclusion of `MADecol`. Axiom output below has no `sorryAx`.

## 5. Compiled nonempty instances (in `FixedZ.lean`, namespace `RBM.Endpoints.Inst`)
Data: `d = 3`, `sz0` (n = 0: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `sz0_admissible` at `𝔠 = 1/6`, `𝔡 = 1/10`.
- `inst_locSCFixed (hML)`, `inst_QDiffFixed (hML)`: `κ = 1/10`, `ε = 1/20`, `τ = 1/10`, `D = 2`; args `3 le_rfl (1/6) (1/10) sz0 sz0_admissible … (by norm_num)×4`.
- `inst_decol_of_locSC (h : locSC)`: `κ = τ = 1/10`, `D = 1`; deterministic args by `le_rfl`, `sz0_admissible`, `norm_num`.
- `inst_decol_scalars`: no hypothesis, `τ = 1/10`.
- `fixed_of_ML` is covered by `inst_locSCFixed`/`inst_QDiffFixed` (its two components). Remaining open hypotheses: only the owed pins `UNMLOut`, `locSC`. Domain `𝐃_{1/10,1/20}` nonempty (`z = i`, merged `locDomain_nonempty`). Nondegenerate. All four compile (build §6) and equal their check-file pins (§3).

## 6. Build, axioms, forbidden tokens, registry
```
$ lake build RBM3D.Main.FixedZ   (error/sorry lines + tail)
Build completed successfully (3349 jobs).
$ lake build RBM3D
Build completed successfully (4027 jobs).
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" eq.out ; grep -c "depends on axioms" eq.out
22
22
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^ *axiom " RBM3D/Main/FixedZ.lean | wc -l
0
$ printf 'import RBM3D\nimport RBM3D.Main.FixedZ\n#assert_rbm_axioms\n' > pre.lean; lake env lean pre.lean; echo exit $?
exit 0
axiom audit: 6573 theorems, 2241 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 93, structural 26, refuted 6).
```
(22 = the 18 theorems + 4 instances; the full build with the root import is the hub's at merge.)

## 7. Paper deltas
Statement differences: `N₀` uniform over `𝐃` and `a,b` (D500), `L^∞` block distance (D501), `η = N^{-1+min(τ/2,1/2)}` in the decol proof (D502), `a,b` inside the probability (D503), explicit `W^τ`/`N^{-D}` (D504), loop indices `(b,a)` (D506): all already in `docs/paper-deltas.md:1459-1465`. No new difference found; no `T2225a` needed.

## 8. Observations (no verdict effect)
- O1. D500's text names only `(Meq:QdS1,2)`; `locSCFixed` and the probability halves of `QDiffFixed` also carry `N₀` uniform over `𝐃_{κ,ε}`. This is a strengthening of the paper's proof-internal "at each fixed z" (`1_2:1228`), signed in design T2192; the dispatcher may widen D500's wording.
- O2. The prove report's `#print axioms` paste has stray quote line breaks; content matches §6.

## Verdict
| Target | Verdict |
|---|---|
| `locSCFixed` (pin) | PASS |
| `QDiffFixed` (pin) | PASS |
| `MAFixed` / `fixed_of_ML` | PASS |
| `MADecol` / `decol_of_locSC` | PASS |
| `locSCFixed_of_ML`, `QDiffFixed_of_ML` and the 14 helper theorems | PASS |
| instances `inst_*` (4) | PASS |
| registry line (`locBad1`, structural) | PASS |
Overall: **PASS**. No dispatcher sign-off needed.
