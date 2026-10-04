Auditor model: claude-opus-5-5

# T2094 audit (round 1): ST2-08 `Induction/ContractPt.lean`, target `stContractPt_holds`

Written Sun Oct  4 01:15:27 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2094-audit1`,
detached at `f271fb0` (`t/T2094`).

## 1. Diff scope and frozen signatures

```
$ git diff --name-only main...t/T2094
RBM3D/Induction/ContractPt.lean
$ git diff main...t/T2094 -- RBM3D/Induction/Step2Defs.lean RBM3D/Test/Axioms.lean RBM3D.lean | wc -l
       0
$ grep -n "^theorem\|^lemma\|^def\|^noncomputable def" RBM3D/Induction/ContractPt.lean
463:theorem stContractPt_holds (d : ℕ) : STContractPt d := by
$ grep -rn "stContractPt_holds" RBM3D/      # on main: no clash
(no output)
```
One file, a sole writable file. The pin `STContractPt` (`Step2Defs.lean:391`) is untouched. Every other
declaration of the file is `private` (§3 (E)).

## 2. Statement against the pin (target `stContractPt_holds`)

```
$ cat Stmt.lean
import RBM3D.Induction.ContractPt
open RBM.Gauss.Sizes
#check @stContractPt_holds
example : ∀ d, STContractPt d := stContractPt_holds
$ lake env lean Stmt.lean; echo "exit $?"
stContractPt_holds : ∀ (d : ℕ), STContractPt d
exit 0
```
The type is literally the merged pin `STContractPt d`, for every `d` (the ticket's `theorem stContractPt_holds
(d : ℕ) : STContractPt d`). The pin (`Step2Defs.lean:391-400`) reads, deterministic, for all `L W` (`NeZero`),
Hermitian `H` on `Idx d L W`, `0 < z.im`, `σ : Fin 2 → Bool`, `a b`, `𝒜`, `M ≥ 0` with
`‖𝓛⁽⁴⁾_{(σ₁,-σ₁,σ₁,-σ₁),(c',b,c',b)}‖^{1/2} ≤ M` on `𝒜`:
`Σ_{c'∈𝒜} Σ_{zdistInf(c-c')≤1} ‖𝓛⁽⁶⁾_{(σ₁,σ₂,σ₁,-σ₁,-σ₂,-σ₁),(a,b,c',b,a,c)}‖ ≤ 3^d/(W^d Im z) · M · max_{σ'} ‖𝓛⁽³⁾_{(σ',σ₂,-σ₂),(a,b,a)}‖`.

Against the paper (`3_5:751-756`, `(eq_sym_loop_bound)`): same set `𝒜` (arbitrary), same neighbour relation
`c ∼ c'`, same alternating four-loop (`max_{c'∈𝒜}` replaced by the equivalent "`≤ M` on `𝒜`" hypothesis), same
three-loop max over `σ ∈ {+,-}`, `≲` made explicit as `3^d/(W^d η)` (sharp, no `N^ε` loss). Left side uses norms
(`|𝓛⁽⁶⁾| ≥ 𝓛⁽⁶⁾`), so it is at least as strong as the paper's. Quantifiers: all deterministic, no `∀ᶠ`; no
`3 ≤ d`, `3 ≤ L` needed (the proof uses `#{c : |c-c'|∞ ≤ 1} ≤ 3^d` for every `L`, `card_ball_le`).
The general target is proved, not a special case. The companion `(eq_sym_loop_bound2)` (`3_5:758`) is not a
target of this ticket (the pin covers `(eq_sym_loop_bound)` only); the report says so.

## 3. Vacuity, hidden hypotheses, cycles

- The theorem has no hypotheses beyond `d`; the pin's hypotheses are `IsHermitian`, `0 < z.im`, `0 ≤ M` and
  the `M`-bound, all plain Props, no structure fields, no other gate's pin.
- Imports: `RBM3D.Induction.Step2Defs`, `RBM3D.Induction.ConArgDet` (both merged on `main`). No external input
  (Ward's identity is re-proved in-file, `Gres_ward_left`, for both signs of `σ₁`). No cycle: nothing on `main`
  imports `ContractPt`.
- Proof route matches `3_5:765-795`: `𝓛⁽⁶⁾ = W^{-6d} tr(Ψ_c A_{c'} Ψ_c^*)` (`loop6_eq`),
  `|tr(ΨAΨ*)| ≤ ‖A‖_HS ‖Ψ‖²_HS`, `𝓛⁽⁴⁾_alt = W^{-4d}‖A‖²_HS` (`loop4_eq`, `hs_Amat`), `Σ_c ‖Ψ_c‖²_HS` by
  `Σ_c P_c = 1` and Ward (`trace_Kmat`), neighbour count `3^d` (`sum_neighbours_le`).

## 4. Compiled nonempty instance

In the same file (`ContractPt.lean:579-634`), compiled by the module build below:
```
private noncomputable def ptH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.of fun i j => (((i 0).val + (j 0).val : ℕ) : ℂ)        -- Hermitian: ptH_herm
private def ptZ : ℂ := ⟨1 / 2, 1 / 4⟩                            -- Im = 1/4 > 0: ptZ_im
private def ptB : Zd 3 3 := fun _ => 1
private noncomputable def ptM (σ0 : Bool) (𝒜 : Finset (Zd 3 3)) : ℝ :=
  ∑ c' ∈ 𝒜, ‖loopFine 3 3 2 ptH ptZ ![σ0, !σ0, σ0, !σ0] ![c', ptB, c', ptB]‖ ^ (1 / 2 : ℝ)
example : Fintype.card (Idx 3 3 2) = 216 := by rw [RBM.Gauss.card_Idx]; norm_num
example : ... :=
  stContractPt_holds 3 3 2 ptH ptZ ptH_herm ptZ_im ![true, false] 0 ptB {0, ptB}
    (ptM true {0, ptB}) (ptM_nonneg _ _) (ptM_bound true {0, ptB})
example : ... :=
  stContractPt_holds 3 3 2 ptH ptZ ptH_herm ptZ_im ![false, true] 0 ptB Finset.univ
    (ptM false Finset.univ) (ptM_nonneg _ _) (ptM_bound false Finset.univ)
```
`d = 3`, `L = 3`, `W = 2` (`N = 216`), nonzero non-diagonal Hermitian `H`, `η = 1/4`, `a = 0 ≠ b = (1,1,1)`,
`𝒜 = {0, b}` (2 blocks) and `𝒜 = Z_3^3` (27 blocks), both sign patterns `(+,-)` and `(-,+)`. Every hypothesis
(Hermitian, `Im z > 0`, `0 ≤ M`, `M`-bound) is discharged by a proof term; `M` is a finite sum of the actual
loop square roots, not an astronomically large witness. Nondegenerate: PASS.

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.ContractPt 2>&1 | grep -E "error|warning|Build completed"
warning: RBM3D/Propagator/LaplaceGauss.lean:36:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/HeatProduct.lean:218:0: `abs_prod_sub_prod_le` does not use the following hypothesis in its type:
warning: RBM3D/Propagator/PropUnit.lean:37:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Propagator/PropUnit.lean:59:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/Step34Pins.lean:12:0: The module doc-string for a file should be the first command after the imports.
warning: RBM3D/Path/Walk.lean:599:5: Variable name `hK` is not explicitly referenced.
warning: RBM3D/Path/Stop.lean:161:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Induction/Step2Defs.lean:922:13: `if_true` has been deprecated: Use `ite_true` instead
warning: RBM3D/Induction/Step2Defs.lean:978:22: `simp at hc'` is a flexible tactic modifying `hc'`. ...
Build completed successfully (3721 jobs).
$ cat Ax.lean   # import RBM3D.Induction.ContractPt; #print axioms RBM.Gauss.Sizes.stContractPt_holds
$ lake env lean Ax.lean
'RBM.Gauss.Sizes.stContractPt_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom|native_decide" RBM3D/Induction/ContractPt.lean; echo "grep exit $?"
grep exit 1
```
No error; no warning from `ContractPt.lean` (all listed warnings are in merged upstream files). Only the three
standard axioms; no `sorry`/`admit`/`axiom`/`native_decide`.

## 6. Paper deltas

```
$ grep -n "STContractPt" docs/paper-deltas.md
404:- **D91（T2039i）**：`STContractPt` 带显式常数 `3^d` 与依赖标号的最大值（合并的 `STContract` 是 Step 3 形式）。
```
The Lean/paper differences (explicit `3^d/(W^d η)` for `≲`; `‖·‖` on the left; `max_{c'}` as hypothesis `≤ M`)
all live in the merged pin, are covered by D91, and are restated in the prove report as candidate `T2094a`.
The theorem adds no difference beyond the pin. Coverage: complete.

## 7. Observations (no effect on the verdict)

- O1. The pin's docstring (`Step2Defs.lean:388-389`) quotes the T2039 ratio `0.39`; the prove report's numeric
  checks give smaller ratios (T2094b). Docstrings are not evidence (§5.7); the statement is unaffected.
- O2. The ticket's import list names `RBM3D.Induction.Contract`; the file does not import it (re-proves the
  needed helpers privately, since those in `Contract.lean` are private). No effect on statement or build.
- O3. `RBM3D/Test/Axioms.lean:134` still lists `STContractPt` as owed. The ticket allows removing it
  ("can go once this merges (say so)"); the prover left it and reports a full build with the line removed
  (prove report (d)). Retiring the line is a registry follow-up for the dispatcher/hub, consistent with
  T2086/T2093, which also left their owed lines.
- O4. Prove report: line 1 `Prover model: claude-sonnet-5-5`, 293 lines (≤ 300).

## Verdict

| Target | Statement | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|
| `stContractPt_holds : ∀ d, STContractPt d` | exact pin | compiled, nondegenerate (`d=3,L=3,W=2`) | pass / 3 std | D91 + T2094a | **PASS** |

T2094: **PASS**. No dispatcher sign-off needed.
