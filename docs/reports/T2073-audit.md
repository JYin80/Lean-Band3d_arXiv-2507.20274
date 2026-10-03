Auditor model: claude-opus-5-5

# T2073 audit (round 1) — ST2-22 `Path/StepDecomp` — Sat Oct  3 20:39:00 UTC 2026

Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2073-audit1` (detached at `1790985` = tip of `t/T2073`).
Pin: the ticket has no statement text; it pins "port RBM2D `Path/StepDecomp` at `c9a24cf` under ST1-COMMON renaming R1–R4"
(check file `docs/tickets/checks/T2073-check.lean` only `#check`s `seqHflow`, `seqGvar`, `CoordF`, `Xmat`).
So the statement check is a script diff against RBM2D `c9a24cf` after renaming, plus the `d ≥ 3` reading.

## 1. Files touched
```
$ git diff main...t/T2073 --stat
 RBM3D/Path/StepDecomp.lean | 1602 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |    1 +
$ git diff main...t/T2073 -- RBM3D/Test/Axioms.lean | grep '^+ '
+   `RBM.Path.HermTestFun,      -- the class of observables `Φ` (`C²` and bounded at Hermitian points): a data condition on `Φ`, hypothesis of `stepDecomp` (T2073, ST2-22; DECISIONS §20)
```
Both are sole writable files; Axioms.lean change is one registry line. No frozen signature touched (no existing file edited besides the registry).

## 2. Statement diff (own script `scratchpad/T2073/adiff.py`)
Renaming applied to the RBM2D text: word `d`→`sz`, `(sz : Sizes)`→`{d : ℕ} (sz : Sizes d)`, `Z2`→`Zd d`, `Idx`→`Idx d`,
`Sizes.size sz n`→`sz.size n`, `Coord/svar/gvar`→`CoordF/svarF/gvarF`; whitespace-normalised signature up to `:=`/`where`.
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Path/StepDecomp.lean > old.lean ; git show t/T2073:RBM3D/Path/StepDecomp.lean > new.lean
$ python3 adiff.py      # the 19 "SAME <name>" output lines are joined into two lines here for length
old public: 19 new public: 19
dropped: []
added: []
SAME: gradMat, fderiv_eq_trace_gradMat, HermTestFun, integrable_normSq_incr, integrable_normPow4_incr, integral_normSq_incr_le, integral_normPow4_incr_le, Ab, stepZ, stepXi
SAME: stepY, lin_eq_fderiv, stepDecomp, stepDecomp_Y_sq, stepDecomp_Z_subG, stepDecomp_integrable_stepZ, StepDecomp_check_stepDecomp, StepDecomp_check_Z_subG, StepDecomp_check_trace_not_hermTestFun
$ python3 bodies.py     # full bodies of the definitions and the structure fields
SAME gradMat (full body)
SAME HermTestFun (full body)
SAME Ab (full body)
SAME stepZ (full body)
SAME stepXi (full body)
SAME stepY (full body)
```
`HermTestFun` fields (new file l.186–189): `contDiffAt : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Φ M`,
`bdd₀ : ∃ C₀, ∀ M, M.IsHermitian → ‖Φ M‖ ≤ C₀` — regularity data on `Φ`, not a hidden analytic conclusion.
`d`-dimensional reading: no target statement carries a `d`-power. The only `N`-dependent constants are in the
moment bounds `16 * (sz.size n)^4`, `768 * (sz.size n)^8` with `sz.size n = (W L)^d` (proved, compiled);
`stepDecomp_Z_subG` takes the proxy `c` with `hbound : Δ · linTrVar n (Ab ω) ≤ c` on `E`, exactly the hypothesis
of the merged `hasCondSubgaussianMGF_linear` (`Path/Markov.lean:636`); `linTrVar` is built from `Sizes.seqGvar`
(`Markov.lean:238`). Quantifier order: fixed `sz s t K n j`, no `∀ᶠ`; time window only `hΔ : 0 ≤ gridStep s t K n`.
Vocabulary is merged MD layer only:
```
$ grep -rnE "def (linTrVar|linTr|gridStep|pathP|filt|pathH) " RBM3D --include='*.lean'
RBM3D/Path/Walk.lean:58:def pathP ...   RBM3D/Path/Walk.lean:62:def filt ...   RBM3D/Path/Walk.lean:67:def gridStep ...
RBM3D/Path/Walk.lean:75:def pathH ...   RBM3D/Path/Markov.lean:134:def linTr ...   RBM3D/Path/Markov.lean:238:def linTrVar ...
```
Imports: `RBM3D.Path.Markov`, `RBM3D.Path.Stop`, `RBM3D.Gauss.Stein` + Mathlib (no `import RBM3D`, no ST-3+ file).

## 3. Vacuity / hidden hypotheses / cycles
- Hypotheses of `stepDecomp`: `hΦ` (class), `hReal`, `hC₂`, `hΔ`, `hIntReal` — all explicit, all deterministic,
  all discharged at concrete data (§4). `stepDecomp_Z_subG`: `hΦ`, `hE`, `hc`, `hbound` — discharged at `E = univ`.
- No external/owed hypothesis; dependencies are merged files (`Walk`, `Markov`, `Stop`, `Stein`, `Sizes`). No cycle
  (new module, imports only merged modules).
- `HermTestFun` registered as structural (a `Prop` data condition on `Φ`); pre-check below accepts it.

## 4. Compiled nonempty instances (in the file, `section Instances`, l.1519–1577)
Data: merged `sz0 : Sizes 3` (`Defs/Sizes.lean:260`; `sz0_values : L 0 = 4 ∧ W 0 = 32 ∧ size 0 = 2097152 ∧ lam 0 = 1/64`),
`s = 1/4`, `t = 3/4`, `K = 2` (Δ = 1/4 > 0), `n = j = 0`, `b = 0`, `Φ_a = sin (Re tr ·)` (private `StepDecomp_checkΦ`),
`U b a = if a = b then 1 else 0`, `C₂ = ‖Re tr‖²`.
```
example :=
  stepDecomp sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0
    (Φ := StepDecomp_checkΦ sz0 0) (StepDecomp_check_class sz0 0)
    (fun a A _ => Complex.ofReal_im _)
    (C₂ := ‖StepDecomp_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2)
    (fun a M y _ _ => StepDecomp_check_hC₂ sz0 0 a M y) (by norm_num [gridStep])
    (StepDecomp_diag sz0 0) 0
    (stepDecomp_integrable_stepZ sz0 ... 0)
example : HasCondSubgaussianMGF (filt sz0 0) ((filt sz0).le 0)
      (fun ω => (Set.univ : Set (PathΩ sz0)).indicator (fun ω => stepZ sz0 ... (StepDecomp_checkΦ sz0 0) (StepDecomp_diag sz0 0) 0 ω) ω)
      ⟨gridStep ... 0 * linTrVar 0 (1 : Matrix ..), mul_nonneg (by norm_num [gridStep]) (linTrVar_nonneg 0 _)⟩ (pathP sz0) :=
  StepDecomp_check_Z_subG sz0 (fun _ => 1 / 4) (fun _ => 3 / 4) (fun _ => 2) 0 0 (by norm_num [gridStep]) 0
example : HermTestFun sz0 0 (StepDecomp_checkΦ sz0 0 0) := StepDecomp_check_class sz0 0 0
example : gradMat (StepDecomp_checkΦ sz0 0 0) (0 : Matrix ..) = (1 : Matrix ..)      -- nonzero gradient
example : ∫ ω, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 2 ∂(pathP sz0) ≤ 16 * (sz0.size 0 : ℝ) ^ 4
example : ∫ ω, ‖Sizes.seqXmat sz0 0 (ω (0 + 1))‖ ^ 4 ∂(pathP sz0) ≤ 768 * (sz0.size 0 : ℝ) ^ 8
```
(elided `..` = same arguments as the file; text read from `new.lean` l.1527–1574.) `StepDecomp_check_Z_subG` proves
`hbound` inside (`Ab ω = cos(Re tr H_j)•1`, `linTrVar (r•A) = r²·linTrVar A`, `cos² ≤ 1`), with no open hypothesis
besides `hΔ`. Every deterministic hypothesis is discharged; no `N = 0`, empty index, collapsed window or `False` premise.
`d = 3`, nonzero `Δ`, nonzero `U`, nonzero gradient. Endpoints covered: `gradMat`, `HermTestFun`, `stepDecomp`,
`stepDecomp_Z_subG` (+ both moment bounds).

## 5. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Path.StepDecomp 2>&1 | grep -E "error|StepDecomp|Build completed"; echo exit=$?
⚠ [3316/3316] Built RBM3D.Path.StepDecomp (6.5s)
warning: RBM3D/Path/StepDecomp.lean:33:100: This line exceeds the 100 character limit, please shorten it!
warning: RBM3D/Path/StepDecomp.lean:52:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (3316 jobs).
exit=0
$ grep -cwE 'sorry|admit|native_decide|axiom' RBM3D/Path/StepDecomp.lean
0
$ lake env lean scratchpad/T2073/ax.lean
'RBM.Path.gradMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.HermTestFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_Z_subG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_Y_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.stepDecomp_integrable_stepZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.StepDecomp_check_stepDecomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.StepDecomp_check_Z_subG' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build RBM3D 2>&1 | grep -E "error:|Build completed"
Build completed successfully (3792 jobs).
$ cat precheck.lean   # import RBM3D / import RBM3D.Path.StepDecomp / #assert_rbm_axioms
$ lake env lean scratchpad/T2073/precheck.lean | grep -nE "error|premises found|registry:"; echo exit
98:premises found by scanning: 82 (borrowed 2, owed 66, structural 14).
99:registry: 5 borrowed + 86 owed + 36 structural; 45 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
exit=0
```

## 6. Paper deltas
Lean/paper differences: (i) observables enter through the class `HermTestFun` + `hC₂` (paper: Taylor expansion of
resolvent polynomials, no such class) — proposed as **T2073a**; (ii) the moment bounds `16 N⁴`, `768 N⁸` are
Lean-only integrability lemmas — **T2073b**; (iii) the sub-Gaussian proxy `c` is an input bounded by `Δ·linTrVar(Ab)`
rather than a computed constant — same form as merged `hasCondSubgaussianMGF_linear`, recorded in report (d) "Open".
All covered as candidates in prove report (d).

## 7. Observations (no verdict impact)
- O1. `linTrVar n 1 = L^d/(1+2dg²)` (the `d`-dimensional constant the ticket asks to "give") is given numerically in
  (a) row 8 and is not a Lean theorem; the target statement does not need it (c is an input). Consumers
  (ST2-23/24, ST-3) must bound `linTrVar` themselves; the prove report flags this in (d).
- O2. Positivity `0 < linTrVar 0 1` at `sz0` is not proved in Lean, so the instance's proxy `c` is shown `≥ 0` only;
  this does not make the instance degenerate (all hypotheses hold at nonzero data; the conclusion is nontrivial).
- O3. Prove report b.5 "every hypothesis is discharged" — confirmed.

## Verdict
| Target | Statement | Vacuity/hidden/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| `gradMat` | SAME (sig + body) | none | compiled, `= 1 ≠ 0` at `M = 0` | ok | n/a | PASS |
| `HermTestFun` | SAME (fields) | registered structural | `sin ∘ Re tr` at `sz0` | ok | T2073a | PASS |
| `stepDecomp` | SAME | none | compiled at `sz0`, all hyps discharged | ok | T2073a/b | PASS |
| `stepDecomp_Z_subG` | SAME | none | compiled at `sz0`, `E = univ` | ok | (iii) noted | PASS |

Overall: **PASS**. No dispatcher sign-off needed.
