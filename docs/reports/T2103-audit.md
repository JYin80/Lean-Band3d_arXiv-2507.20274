Auditor model: claude-opus-5-5

# T2103 audit, round 1 (ST2-28: `Induction/LoopGenN`, `Induction/QVN`)

Written Sun Oct  4 03:27:46 UTC 2026 (`date -u`). Branch `t/T2103` at `94131ca`; audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2103-audit1` (detached at `94131ca`, build cache cloned from main).

## 1. Scope, hygiene, frozen files

```
$ git diff --name-status main...t/T2103
A	RBM3D/Induction/LoopGenN.lean
A	RBM3D/Induction/QVN.lean
$ git diff --stat main...t/T2103 -- RBM3D/Induction/HierarchyN.lean RBM3D/Path RBM3D/Induction/Step2Defs.lean RBM3D/Induction/HierAlgebra.lean RBM3D/Test/Axioms.lean
(empty)
$ for f in LoopGenN QVN; do git show t/T2103:RBM3D/Induction/$f.lean | grep -nwE "sorry|admit|axiom|native_decide" | grep -v "#print axioms"; done
(no output)
$ name clash on current main (grep -rnwE "(def|theorem|lemma|abbrev) <name>" RBM3D | wc -l)
loopGenN 0, stLoopGenNForm_holds 0, hierarchyN_holds 0, loopDerivN 0, QVPropagatedN 0, qvPropagatedN 0,
LoopGenN_check_stLoopGenNForm_sz0 0, LoopGenN_check_hierarchyN_sz0 0, QVN_check_sz0_one 0, QVN_check_sz0_two 0
```
Only sole writable files touched (`Test/Axioms.lean` untouched, allowed). All other new declarations are
`private` with prefix `LoopGenN_` / `QVN_` (§3 (E)). Main has moved since the merge base `c4c1f80`
(T2099 `NewKLK.lean`, T2101): no overlap with these files.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.LoopGenN RBM3D.Induction.QVN 2>&1 | tail   (warnings: longLine linter notes only)
ℹ [3761/3762] Built RBM3D.Induction.LoopGenN (4.7s)
info: RBM3D/Induction/LoopGenN.lean:718:0: 'RBM.Ind.loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:719:0: 'RBM.Ind.stLoopGenNForm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/LoopGenN.lean:720:0: 'RBM.Ind.hierarchyN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
ℹ [3762/3762] Built RBM3D.Induction.QVN (12s)
info: RBM3D/Induction/QVN.lean:873:0: 'RBM.Ind.qvPropagatedN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QVN.lean:874:0: 'RBM.Ind.loopDerivN' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3762 jobs).
exit 0
$ printf 'import RBM3D\nimport RBM3D.Induction.LoopGenN\nimport RBM3D.Induction.QVN\n#assert_rbm_axioms\n' > precheck.lean
$ lake env lean precheck.lean 2>&1 | tail -2
non-vacuity certificates: 4 of 106 premises in the two ledgers; the rest are not known to be satisfiable (...)
exit 0
```

## 3. Target A: `stLoopGenNForm_holds`, `hierarchyN_holds` (DECISIONS §32)

```
$ (ticket pin, RBM.Ind. stripped) vs (branch line) -- diff
stLoopGenNForm_holds: identical to ticket pin    [theorem stLoopGenNForm_holds (d : ℕ) : STLoopGenNForm d]
hierarchyN_holds: identical to ticket pin        [theorem hierarchyN_holds (d : ℕ) : HierarchyN d := hierarchyN_of_loopGenN d (stLoopGenNForm_holds d)]
$ git diff main...t/T2103 -- RBM3D/Induction/HierarchyN.lean   -> empty (pin `STLoopGenNForm`, HierarchyN.lean:42, unchanged)
$ sed -n 615,617p RBM3D/Induction/LoopGenN.lean
theorem stLoopGenNForm_holds (d : ℕ) : STLoopGenNForm d := by
  intro sz n E hE u hu0 hu1 M hM k hk σ a
  exact loopGenN d (sz.L n) (sz.W n) (sz.lam n) E (sz.three_le_L n) hE u hu1 M hM σ a
```
- **Statement.** The type is the merged owed pin verbatim (`∀ sz n E, |E|<2 → ∀ u, 0≤u → u<1 → ∀ M Hermitian
  → ∀ k ≥ 2, σ, a, genMat = STllPairN + STegtM`). The supporting public `loopGenN` (LoopGenN.lean:548) is
  stated for all `d L W g` with `3 ≤ L`, Hermitian `M`, `|E|<2`, `u<1`, any `k`; its right side is the
  unfolded body of `STllPairN` (HierAlgebra.lean:693, `W^d Σ_{k<l} Σ_{a,b} 𝓛 S^{(B)} 𝓛`) and `STegtM`
  (Step2Defs.lean:750, `W^d Σ_k Σ_{a,b} (𝓛_{(σ_k),(a)} - m(σ_k)) S^{(B)} 𝓛`), accepted by the kernel at
  `g = sz.lam n`. Compared with RBM2D `LoopGenN` (`HierVocab:548` at `c9a24cf`): `W^2 → W^d`, `Z2 → Zd d`,
  `0 ≤ u` and `2 ≤ k` dropped (stronger), `3 ≤ L` kept and discharged by `Sizes.three_le_L`
  (field `three_le_L : ∀ n, 3 ≤ L n`, Defs/Sizes.lean:145; a size condition of the setting).
- **Hidden hypotheses / cycle.** No hypothesis at all on `stLoopGenNForm_holds`/`hierarchyN_holds`.
  Dependencies are merged (`hierarchyN_of_loopGenN`, `loopDrift_sub_K_deriv_n`, T2095; Gauss/Hierarchy
  contraction lemmas); none depends on these new files.
- **Instances.** `LoopGenN_check_loopGenN` (private, :657): `loopGenN` at `d=3, L=3, W=2, g=1/2, E=1/2, u=1/2`,
  non-scalar Hermitian `M0 = X_{(0,1,+)} + X_{(1,0,+)}` with `M0 0 1 = 1` proved, loop `(+,-,+)`,
  `a=(0,1,2)`. `LoopGenN_check_stLoopGenNForm_sz0` (:682) and `LoopGenN_check_hierarchyN_sz0` (:695):
  merged `sz0` (`d=3`), `n=0`, `E=0`, `u=1/2`, `M=1`, `k=3`, `σ=(+,-,+)`, `a=(0,1,2)`; every hypothesis
  discharged (`norm_num`, `Matrix.isHermitian_one`). Compiled (build above). Nondegenerate.
- **Verdict A: PASS.**

## 4. Target B: `QVPropagatedN` / `qvPropagatedN` (QVN.lean:799, :813)

```
$ sed -n 799,810p RBM3D/Induction/QVN.lean
def QVPropagatedN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ (k : ℕ), 2 ≤ k → ∀ (σ : Fin k → Bool) (κ : (Fin k → Zd d (sz.L n)) → ℂ),
        ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
            ‖∑ b : Fin k → Zd d (sz.L n), κ b *
              loopDerivN d (sz.L n) (sz.W n) E u M
                (coordinateMatrix d (sz.L n) (sz.W n) c) σ b‖ ^ 2 ≤
          (k : ℝ) * (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
            κ b * (starRingEnd ℂ) (κ b') * sz.STeeM n E u M σ b b').re
theorem qvPropagatedN (d : ℕ) : QVPropagatedN d := by
  intro sz n E hE u _ hu M hM k _ σ κ
  exact QVN_core (g := sz.lam n) E u hE hu hM σ κ
$ RBM2D c9a24cf HierVocab:486 QVPropagatedN (abridged): ∀ L W E u, 3 ≤ L → |E|<2 → 0≤u → u<1 → ∀ M Herm,
  ∀ k ≥ 2, σ κ, Σ_c gvar c * ‖Σ_b κ b * loopDerivN … σ b‖^2 ≤ k * (Σ_{b,b'} κ b conj κ b' * eeN … σ b b').re
$ RBM3D Path/QVIdentity.lean:410 QVPropagated (merged n=2 shape): … ≤ 2 * (Σ κ conj κ * EE …).re
```
- **Statement.** Shape required by the ticket: `∀ sz n`, `g = sz.lam n`, merged `STeeM` (Step2Defs.lean:757),
  inequality form with the cut-count factor (`k`, = `2` in the merged `QVPropagated`). Matches RBM2D
  `QVPropagatedN` with `W^2 → W^d` (inside `STeeM`), `gvar → gvarF … (sz.lam n)`, `3 ≤ L` supplied by
  `Sizes`. `loopDerivN` (:62) is the derivative at `y=0` of `𝓛(M + yX)`, the RBM2D definition with
  `Zd d`. The private core `QVN_core` holds for all `d L W g`; the public pin is the sz-restricted
  form the ticket asks for. The factor `k` is Cauchy–Schwarz over `k` cuts (dimension-free); not an
  exponent issue at `d ≥ 3`.
- **Hidden hypotheses / cycle.** `QVPropagatedN` is a plain `Prop` def proved unconditionally by
  `qvPropagatedN`; no structure fields, no hypotheses beyond the pin. Dependencies merged only
  (`Step34Pins`, `Step2Defs`, `Path/QVIdentity`).
- **Instances.** `QVN_check_sz0_one` (:830): `sz0`, `n=0`, `E=0`, `u=1/2`, `M=1`, `k=3`, `σ=(+,-,+)`, `κ≡1`.
  `QVN_check_sz0_two` (:846): `E=1/2`, `u=1/3`, non-scalar Hermitian `M = X_{(0,0,+)}`, `σ=(+,+,-)`,
  non-constant `κ_b = 1(b₀=b₁)`. All hypotheses discharged; compiled. Nondegenerate.
- **Verdict B: PASS.**

## 5. Paper deltas

```
$ grep -n "T2103[a-z]" docs/reports/T2103-prove.md
297:- `T2103a`: `qvPropagatedN` carries the factor `k` (the number of cuts), not `1`: ... repeats T2084c / D152-D155 for general `n`
298:- `T2103b`: coupling `g` of `S^{(B)}(g)` is a parameter of `loopGenN`, `QVN_core` ...; `W^2` of RBM2D is `W^d` ...
```
Differences found by this audit and their coverage:
- `QVPropagatedN` is an inequality with factor `k`, not the identity of `def_diffakn_k`/`defEOTE`: T2103a.
- `loopGenN`/`STLoopGenNForm` is the drift part of `eq:mainStoflow` only (generator `genMat`, no
  martingale part): already the merged pin's shape (D149, T2095); no new delta.
- `loopGenN` carries `3 ≤ L` (for `Σ_a S^{(B)}_{ab} = 1`) and the free coupling `g`: T2103b covers `g`;
  `3 ≤ L` is a standing size condition supplied by `Sizes` (not a paper difference).
Coverage complete.

## 6. Observations (no verdict effect)

- O1. Prove report notes the owed registry line `RBM.Ind.STLoopGenNForm` (`Test/Axioms.lean`) can be removed
  after merge (ticket asks "say so": done, report line 289/299). `QVPropagatedN` is unregistered; it is a
  proved pin, not a hypothesis of any theorem here, and the pre-check passes (exit 0).
- O2. The prove report is at exactly 300 lines (limit 300).
- O3. Instances at `sz0` use `M = 1` for the two `LoopGenN` checks; the non-scalar `M` appears in the
  concrete `loopGenN` check, which is the theorem the pin reduces to.

## Verdict

| Target | Verdict |
|---|---|
| `stLoopGenNForm_holds` (+ `loopGenN`) | PASS |
| `hierarchyN_holds` | PASS |
| `QVPropagatedN` / `qvPropagatedN` | PASS |

**T2103: PASS.** No dispatcher sign-off needed. At merge the hub adds `import RBM3D.Induction.LoopGenN`
and `import RBM3D.Induction.QVN` after the last import line of `RBM3D.lean` and runs the full build.
