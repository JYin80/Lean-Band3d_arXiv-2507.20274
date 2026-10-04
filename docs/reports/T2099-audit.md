Auditor model: claude-opus-5-5
# T2099 audit (round 1): ST2-07 `lem:newKLK`, `stNewKLK_holds`

Written Sun Oct  4 03:10:32 UTC 2026 (`date -u`). Branch `t/T2099` at `8b43795`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2099-audit1` (detached at `8b43795`).
Target: `theorem stNewKLK_holds (d : ℕ) : STNewKLK d` in `RBM3D/Induction/NewKLK.lean`.

## 1. Statement against the pin
```
$ grep -o 'theorem stNewKLK_holds (d : ℕ) : STNewKLK d' docs/tickets/T2099.md > pin.txt
$ sed -n 1198p RBM3D/Induction/NewKLK.lean | sed 's/ := by$//' > lean.txt ; diff pin.txt lean.txt
diff exit 0
$ git diff main...HEAD -- RBM3D/Induction/Step2Defs.lean | wc -l      # pin definitions untouched
       0
$ lake env lean scratch/ax.lean
'RBM.Gauss.Sizes.stNewKLK_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
stNewKLK_holds : ∀ (d : ℕ), STNewKLK d
```
`ax.lean` also elaborates, without error, `example : ∀ d, STNewKLK d := stNewKLK_holds` and
`example : (∀ d, STNewKLK d) = (∀ d : ℕ, 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAt d κ 𝔡 C δ₀) := rfl`.

The pin body (`Step2Defs.lean:363-378`, merged, unchanged) against the paper `3_5:371-378`
(`(juwo2=klk)`, `(juwo=Lklk)`): both bounds with `C/(1-u)`, `Ĵ` (`STJhatM` = `(defCALJ)`, max over
`σ ∈ {±}²`, all `a`), `Ĵ + Ĵ² 1_{ℓ≥1}`, profile `W^{-d} 𝒯̃^ℓ_{u,D}(|a-b|)`, range `0 ≤ ℓ ≤ L`; `0 ≤ u < 1`;
`C, δ₀` chosen after `(d, κ, 𝔡)` and before `(sz, n, E, u, D, ℓ, H)` (constants cannot depend on
`W, L, lam`, DECISIONS §29). The paper's "weak local law, with high probability" is the explicit
deterministic `‖G_u − M‖_max ≤ δ₀` for every Hermitian `H`: already paper-delta **D83 (T2039a)**.
§29 checks: (1) `0 ≤ u`, `u < 1` are hypotheses; (2) not applicable (time is `u` only); (3) no
`L^d ≤ W^K` hypothesis, and the proof needs none (it holds for all `sz`); (4) `∀ sz n`, no `∀ᶠ`.
The proved type is the general pin, not a special case or conditional adapter.
**Statement: PASS.**

## 2. Vacuity, hidden hypotheses, cycles
- The only binder of the theorem is `d : ℕ`; no structure argument, no new `Prop` premise.
- `STNewKLK d` is `3 ≤ d → …`; `3 ≤ d` is the paper's setting, satisfiable (instance below, `d = 3`).
- Dependencies (from `nkl_at`, `NewKLK.lean:993-996`): `prop5Decay_holds d 𝔡⁻¹`, `ekPropTInf_holds d`,
  merged lemmas (`Ind.Gres_mul_conjTranspose`, `Ind.half_le_mE_im`, `sum_norm_Theta_row_le`, …); all
  merged theorems, standard axioms only (printed above). No dependence on a downstream ST2 pin.
- Constants: `δ₀ = κ/2`, `C = 2(C₁C_sC_T + C_s) + 10C_s + C_sC_T` with `C₁` from `Prop5Decay d 𝔡⁻¹`,
  `C_s = 2^{d-2}e`, `C_T` from `(TTT2)`: functions of `(d, κ, 𝔡)` only.
- No external hypothesis is introduced, so no limit check is required.
**PASS.**

## 3. Compiled nonempty instance
```
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev|structure|instance|example)" RBM3D/Induction/NewKLK.lean
1198:theorem stNewKLK_holds (d : ℕ) : STNewKLK d := by
1258:example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
1292:example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
$ grep -rn "def sz0" -A4 RBM3D/Defs/Sizes.lean
260:def sz0 : Sizes 3 where
261-  L := fun n => 4 * (n + 1)
262-  W := fun n => (2 * (n + 1)) ^ 5
263-  lam := fun n => ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
$ grep -n "private theorem nkl_STGMM_zero" -A3 RBM3D/Induction/NewKLK.lean
1231:private theorem nkl_STGMM_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
1232-    (hu1 : u < 1) (x y : Idx d (sz.L n) (sz.W n)) :
1233-    ‖STGMM sz n 0 u (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) x y‖ ≤
1234-      u / (1 - u) := by
```
Example 1 (`:1258`) applies `stNewKLK_holds 3` itself at `κ = 𝔡 = 1/10`, `sz0`, `n = 0`
(`L = 4`, `W = 32`, `lam = 1/64`, index set `Z_4^3 × [32]^3` nonempty), `E = 0`, `D = 1`, `ℓ = 2`
(indicator `1_{ℓ≥1}` on, `ℓ ≤ L` nontrivial), `H = 0` (Hermitian), `u = δ₀/(1+δ₀) ∈ (0,1)`, and all
`σ`, `a`. Every hypothesis is discharged in the proof term: `0 < lam`, `lam ≤ 10`, `|0| ≤ 2 − 1/10`,
`0 ≤ u < 1`, `0 ≤ D`, `0 ≤ ℓ ≤ L`, `IsHermitian 0`, and the weak law via `nkl_STGMM_zero` with
`u/(1−u) = δ₀`. No `N = 0`, no empty index, no `False` premise, no large witness. Example 2 (`:1292`)
repeats this with explicit `u = 1/32` through the private `nkl_at`. Both compile in the module build
below. **PASS.**

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Induction.NewKLK        # in the audit worktree
✔ [3723/3723] Built RBM3D.Induction.NewKLK (15s)
Build completed successfully (3723 jobs).
exit 0
$ grep -n "NewKLK" build.log | grep -iE "warning|error"     # (no output)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/NewKLK.lean ; echo "grep exit $?"
grep exit 1
$ grep -nE "unsafe|opaque|implemented_by|extern|set_option" RBM3D/Induction/NewKLK.lean
55:set_option linter.style.longLine false
$ grep -nE "^private (theorem|lemma|def)" RBM3D/Induction/NewKLK.lean | awk '{print $3}' | grep -v '^nkl' ; echo "exit $?"
exit 1
$ sed -n 1,30p RBM3D/Induction/NewKLK.lean | grep import
import RBM3D.Induction.Step2K2
import RBM3D.Evolution.PropTInf
import RBM3D.Loop.KLWard
import RBM3D.Induction.ConArgDet
$ git diff --name-only main...HEAD
RBM3D/Induction/NewKLK.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep '^[-+] ' | cut -c1-110
-   `RBM.Gauss.Sizes.STNewKLK, -- `lem:newKLK` (`3_5:371-378`): ST2-07 (+ST2-06b) (T2066, DECISIONS §28)
-   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise in `(n, E, u, D, ℓ, H)`, the f
+   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise in `(n, E, u, D, ℓ, H)`, the f
```
Only the two sole writable files are touched; `Test/Axioms.lean` changes registry lines only (the
`STNewKLK` owed line removed, the `STNewKLKAt` line kept with an edited comment). Imports are the four
named by the ticket (no `import RBM3D`). Only public declaration: the pinned name; all 38 helpers are
`private` with prefix `nkl`. Axioms: the three standard ones. The full `lake build` is the hub's
step at merge. **PASS.**

## 5. Paper deltas
The Lean statement is the merged pin unchanged; its one difference from `3_5:371-378` (deterministic,
explicit `δ₀` in place of "weak local law, w.h.p.") is D83 (T2039a). The report proposes
`T2099a` (cut `K` replaced by near/far split; `ℓ ≤ L` unused), `T2099b` (`δ₀ = κ/2` explicit,
Ward factor absorbed in `C`), `T2099c` (entrywise Ward bound for `𝓛`, no Ward for `𝒦`): proof-route
notes, no statement change. Coverage complete. **PASS.**

## Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The ticket says both owed lines `STNewKLK` and `STNewKLKAt` "can go"; the commit removes only
  `STNewKLK`. The prove report (b) gives the registry pre-check output: removing `STNewKLKAt` fails the
  axiom audit because no theorem concludes `STNewKLKAt` itself (it is a hypothesis of
  `ST_good_engine`). Keeping it is correct; the dispatcher may want a one-line corollary
  `∃ C δ₀, STNewKLKAt …` later, or to leave the line as is.
- O2. Section (a) of the prove report fixes `δ₀ = c_κ = √(κ(4−κ))/2`; the Lean proof uses `δ₀ = κ/2`.
  The narrative in (b) states this; no (a′) entry was written. Both are admissible (`∃ δ₀`).
- O3. The ticket's ingredients `stK2decay_holds`, `KLK_ward` and the Ward lemmas for `𝓛` are not used
  (the report states this; `RBM3D.Loop.KLWard` stays imported, unused). Allowed by the ticket.
- O4. The instances take `H = 0`; this is legitimate data (weak law discharged by `‖G_u − M‖_max ≤ u/(1−u) = δ₀`
  in example 1), but it is a special Hamiltonian. Not a degeneracy in the sense of CLAUDE.md §4.

## Verdict
`stNewKLK_holds (d : ℕ) : STNewKLK d` — **PASS**. No dispatcher sign-off needed.
After merge the hub adds `import RBM3D.Induction.NewKLK` after the last import of `RBM3D.lean`.
