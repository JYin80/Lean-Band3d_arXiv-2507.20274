Auditor model: claude-opus-5-5

# T2316 audit (round 1): Thu Oct  8 02:26:28 UTC 2026

Branch `t/T2316` at b163e85, audited in the detached worktree `../RBM3D-wt/T2316-audit1`. Scratch files are in the scratchpad dir `T2316/`.

## 1. Scope, diff, build
```
$ git diff --stat main...HEAD
 RBM3D/Test/Axioms.lean                |   1 +
 RBM3D/Universality/GUEPhase/Grid.lean | 897 ++++++++++++++++++++++++++++++++++
$ git merge-base --is-ancestor main t/T2316 && echo ok      # main = 66fd97e
main is ancestor of t/T2316
$ git diff main...HEAD -- RBM3D/Test/Axioms.lean | grep '^+ '
+   `RBM.Univ.GUEPhase.GUEPathBounds, -- output of the §7.2 random layer ... (T2316, UN-27: owed by the §20 rule,
    class unsure; owner UN-33 `BoundsA` `pathBounds_of_forall_highProbAt`; hypothesis of UN-44/47/50/51)   [abridged]
$ lake build RBM3D.Universality.GUEPhase.Grid ; echo exit $? ; grep -c "GUEPhase/Grid.lean" build.out
exit 0
Build completed successfully (3738 jobs).
0                                   # no warning or error line in Grid.lean
$ lake build ; echo exit $?         # full library, includes the modified Test/Axioms.lean
exit 0
Build completed successfully (4123 jobs).
$ grep -nE "sorry|admit|native_decide|^\s*axiom\b" RBM3D/Universality/GUEPhase/Grid.lean | wc -l
0
$ head -6 Grid.lean | grep ^import
import RBM3D.Universality.ZeroModeProfile
```
Registry pre-check (`areg.lean` = `import RBM3D` / `import RBM3D.Universality.GUEPhase.Grid` / `#assert_rbm_axioms`):
```
$ lake env lean areg.lean ; echo exit $? ; grep -nE "GUEPathBounds|^premises found|error" areg.out
exit 0
135:  RBM.Univ.GUEPhase.GUEPathBounds: 0 [no certificate]
150:premises found by scanning: 149 (borrowed 1, owed 90, structural 41, refuted 6, superseded 11).
```

## 2. Axioms
```
$ lake env lean aax.lean | sed … | awk '{group by axiom set}'   # 16 #print axioms lines
 [propext, Quot.sound]: GridCheck.gueGridK_size_le
 [propext, Classical.choice, Quot.sound]: gueUnit_isProbabilityMeasure gueStepMeasure_isProbabilityMeasure
   Pgue_isProbabilityMeasure gueH_isHermitian gueH_adapted gueH_measurable gueGridK_ne_zero map_gueH_zero map_gueH_last
   GUEPhaseGrid_gloop_smul_lemT_eq GUEPhaseGrid_gloop_two_smul_lemT_eq GUEPathBounds Pgue gueH GridCheck.t1_pos   [wrapped]
```

## 3. Statements against the pins (my own scratch file, independent of the prover's)
`apins.lean`: `import RBM3D.Universality.GUEPhase.Grid`, then check-file lines 153-331 copied verbatim with
`sed -n '153,331p' docs/tickets/checks/T2316-check.lean` (vocabulary `…V`, the 9 pin `def`s, and the dispatcher's
8 Prop-shape examples). After that come 9 examples `example : T2316_<pin> := fun … => <target> …`, the 6 vocabulary
equalities (`rfl`, and `congrArg Measure.infinitePi (funext fun k => by cases k <;> rfl)` for `Pgue`), and
`GUEPathBounds … ↔ GUEPathBoundsLkV … ∧ GUEPathBoundsLocalLawV …` (`⟨fun h => ⟨h.lk, h.localLaw⟩, fun h => ⟨h.1, h.2⟩⟩`).
```
$ lake env lean apins.lean ; echo exit $? ; grep -c "^example" apins.lean
<only 'unused variable d/L/W/z' linter warnings at the binders of my fun-examples>
exit 0
24
```
So every target has exactly the pinned type: hypotheses `0 ≤ t1 n` (zero); `0 ≤ t0 n`, `0 ≤ τ n`, `K n ≠ 0` (last);
`[NeZero L] [NeZero W]`, `0 < z.im` (homogeneity). Quantifier order: `d sz` first, then the parameters. The scale is
`N = sz.size n = (W L)^d`, the loop power is `(σ.zip a).length`, and the 2-loop factor is `lemT z`. The body of
`GUEPathBounds` (both fields, scales `(N η)^{-m}` and `(N η)^{-1/2}`, `StochDomAt (Pgue sz) sz.size`) equals the pin.

Source comparison (RBM2D `c9a24cf:RBM2D/Universality/GUEPhase/Grid.lean`, read with `git show`):
```
$ sed -n '577,582p;751,758p;766,773p' Grid2D.lean      # source statements (abridged to the type lines)
theorem map_gueH_last (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ht0 : 0 ≤ t0 n) (hτ : 0 ≤ τ n) (hK : K n ≠ 0) :
    (Pgue d).map (gueH d (fun n => (1 - ouZeta (τ n)) * t0 n) t0 K n (K n)) =
      (ouP (d.L n) (d.W n)).map (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (d.L n) (d.W n) (τ n) ω)
theorem GUEPhaseGrid_gloop_smul_lemT_eq (M : Matrix (BlockIndex L W) (BlockIndex L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ : List Bool) (a : List (Z2 L)) : gloop L W M z ⟨σ, a⟩ = ((Real.sqrt (lemT z) : ℝ) : ℂ) ^ (σ.zip a).length * …
theorem GUEPhaseGrid_gloop_two_smul_lemT_eq (M : …) {z : ℂ} (hz : 0 < z.im) (σ₂ : Bool) (a b : Z2 L) :
    gloop L W M z (loopOf ![true, σ₂] ![a, b]) = ((lemT z : ℝ) : ℂ) * gloop L W (…• M) (spectralZ (lemE z) (lemT z)) …
```
After the ticket's import map (`d ↦ sz`, `ouP (d.L n) (d.W n) ↦ ouP (UNModel.band sz) n`, `BlockIndex ↦ Vtx d`,
`Z2 ↦ Zd d`, `gloop ↦ loopL d`, `spectralZ ↦ zt`), these are the port's statements (prover report (b) L559, L758,
L772, which match the file). I also ran a sed-normalised `diff -w` of the vocabulary block (source `:52-129`, port
`:49-108`). The only remaining hunks are docstrings (`(W L)²` ↦ `(W L)^d`), the `LoopIdx d` ↦ `Loop.LoopIdx` namespace,
and places my sed did not normalise (`Idx d (d.L n)`); `GUEFlow`/`loopG` are absent (dead code, ticket "Not targets").
- No `3 ≤ d`: `grep -c "3 ≤ d" Grid.lean` gives 0. No condition on `sz.lam`: it appears only at `:626` (`ouVar … (sz.lam n)`) and
  `:662` (`hseq … := rfl`).

## 4. Hidden hypotheses, vacuity, cycles
- No theorem of the file takes a structure or `Prop` hypothesis. `GUEPathBounds` is a two-field `Prop` interface that
  no target consumes (its producer is UN-33). The registry scan shows `0` theorems resting on it.
- Dependencies: one import, `RBM3D.Universality.ZeroModeProfile` (merged). The file does not import the unmerged sibling files.
  `Induction.ConArg*` is not imported: `GUEPhaseGrid_Gres_eq_green` is a private unfolding through
  `Matrix.nonsing_inv_eq_ringInverse`. No cycle.
- No external hypothesis in any target, so no limit check is owed.

## 5. Compiled nonempty instances (file `:795-895`, namespace `RBM.Univ.GUEPhase.GridCheck`, built in §1)
```
$ sed -n 840,895p Grid.lean | grep -nE "map_gueH|GUEPhaseGrid_gloop|by |t1_pos"
7:  map_gueH_last SizesInst.sz0 (fun _ => 9 / 10) (fun _ => 1 / 20) (fun _ => 4) 0
8:    (by norm_num) (by norm_num) (by norm_num)
18:  map_gueH_last SizesInst.sz0 (fun _ => 9 / 10) (fun _ => 1 / 20) (fun _ => 4) n
19:    (by norm_num) (by norm_num) (by norm_num)
31:  exact Nat.le_self_pow (by omega) _
43:  GUEPhaseGrid_gloop_two_smul_lemT_eq _ (by simp) false 0 0
54:  GUEPhaseGrid_gloop_smul_lemT_eq _ (by simp) _ _
```
| target | instance data | hypotheses discharged |
|---|---|---|
| `Pgue_isProbabilityMeasure` | `Pgue sz0` (`d=3`, `L=4`, `W=32`, `N=2097152`) | `inferInstance` |
| `gueH_isHermitian` | `sz0`, `t₁=(1-ζ(1/20))·9/10`, `t₀=9/10`, `K≡4`, `(n,k)=(0,4)` and all `n k ω` | none needed |
| `gueH_adapted` / `gueH_measurable` | `sz0`, `n=0`, `k=4`, all `i j` | none needed |
| `gueGridK_ne_zero` | `sz0`, `n0=n=0` | none needed |
| `map_gueH_zero` | `sz0`, `n=0`, `t₁>0` | `t1_pos` (proved) |
| `map_gueH_last` | `sz0`, `t₀=9/10`, `τ=1/20`, `K≡4`, `n=0` and all `n` | `norm_num` ×3 |
| `GUEPhaseGrid_gloop_two_smul_lemT_eq` | `d=3`, `L=3`, `W=2`, `M=blockMat(diag 2)`, `z=I`, `σ₂=false`, `a=b=0` | `0 < I.im` by `simp` |
| `GUEPhaseGrid_gloop_smul_lemT_eq` | same `M`, `z=I`, loop `⟨[true,false],[0,0]⟩` (length 2) | `by simp` |

None is degenerate: `N ≥ 1`, index sets nonempty, `K = 4 ≠ 0`, `t₁ < t₀` (window `[t₁, t₀]` not collapsed), no `False` premise,
no large witness (the instance uses `K = 4`, not `gueGridK`). The preflight's hand check (`1/40 = 1/40` at `z = i`)
shows the homogeneity instance says something nontrivial.

## 6. Name clashes, paper deltas
```
$ for n in <20 new public names incl. GridCheck>; do git grep -nw -- $n main -- RBM3D | wc -l; done | sum
main hits over 20 names: 0
```
Paper-delta candidates in the prove report (d): `T2316a` (`N=(WL)²→(WL)^d` in `gueH`, `gueScale`, `gueGridK`, (7.26)),
`T2316b` (`sz.lam` cancels in (7.26)), `T2316c` (OU carrier `ouP (UNModel.band sz) n`, bridged by `ouMatC_toC`), and `T2316d`
(`GUEFlow`/`loopG` not ported). These cover the ticket's required list. I found no other Lean/paper statement difference.

## 7. Observations (no RETURN)
- O1: The ticket's registry paragraph expected no `Axioms.lean` line. The scan does flag the `Prop` structure
  `GUEPathBounds` (prover Finding F1), so the prover added one `owedProps` line. That follows the ticket's own fallback ("any flagged
  name by §20's rule (unsure: owed), listed in the report"), and Axioms.lean is a sole writable file. The dispatcher may still want
  to confirm owed vs structural. This is not a sign-off condition: the line changes no statement.
- O2: The `(_ht1 : 0 ≤ t1 n)` hypothesis of `map_gueH_zero` is unused, as in the source and the pin.

## Verdict
| target | verdict |
|---|---|
| vocabulary (`gueUnitVar`, `gueUnit`, `gueStepMeasure`, `Pgue`, `gueH`, `gueScale`, `gueGridK`, `GUEPathBounds`) | PASS |
| `Pgue_isProbabilityMeasure` (+ the two step instances) | PASS |
| `gueH_isHermitian`, `gueH_adapted`, `gueH_measurable` | PASS |
| `gueGridK_ne_zero` | PASS |
| `map_gueH_zero` | PASS |
| `map_gueH_last` | PASS |
| `GUEPhaseGrid_gloop_smul_lemT_eq`, `GUEPhaseGrid_gloop_two_smul_lemT_eq` | PASS |

Overall: **PASS**. No dispatcher sign-off is required (O1 is a registry-class confirmation only).
