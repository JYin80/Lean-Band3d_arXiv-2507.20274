Auditor model: claude-opus-5-5

# T2075 audit (round 1): ST2-06b `EKPropTInf` / `ekPropTInf_holds`

Written Sat Oct  3 20:31:13 UTC 2026 (`date -u`). Branch `t/T2075` at `ae86da8`, `main` at `092aaf0`.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2075-audit1` (detached at `t/T2075`). Scratch: `scratchpad/T2075/`.

## 1. Statement

Pin (ticket target 1): `EKPropT` (`RBM3D/Evolution/Pins.lean:142`) with `zdistInf d L` in place of `zdistD d L` in all three places.
```
$ awk '/^def EKPropT \(d/,/^$/' RBM3D/Evolution/Pins.lean | sed 's/zdistD d L/Gauss.zdistInf d L/g; s/EKPropT /EKPropTInf /' | tr -s ' \n' ' ' > pin.txt
$ awk '/^def EKPropTInf/,/^$/' RBM3D/Evolution/PropTInf.lean | tr -s ' \n' ' ' > lean.txt
$ diff pin.txt lean.txt && echo IDENTICAL
IDENTICAL
```
Hypotheses `3 ≤ d`, `∃ C > 0` before `∀ L g u t` (C depends on `d` only), `0 < g`, `0 ≤ u ≤ t < 1`,
(i) `g²/L² ≤ 1-t` or (ii) `1-u ≤ g²/L²`, all `a b : Zd d L`: identical to the pin.
Distance (`RBM3D/Defs/Sizes.lean:115`): `def zdistInf (d L : ℕ) (x : Zd d L) : ℕ := Finset.univ.sup fun i => zdist L (x i)`.
Paper (`paper/tex/1_2_Intro_model_result.tex:274`): "we use the $L^\infty$-metric to define (periodic) distances"; `lem:propT`
(`paper/tex/3_5_Loop_Hierarchy.tex:328`, `(TTT2)`): `C_d` depending only on `d`; `0≤u≤t<1` with (i) `1-u ≥ 1-t ≥ λ²/L²` or (ii)
`1-t ≤ 1-u ≤ λ²/L²`; `Σ_c 𝒯_u(|a-c|)𝒯_t(|c-b|) ≤ C_d/(1-u)·𝒯_t(|a-b|)`. The Lean statement is the paper's `(TTT2)` with the paper's norm.

Target 2: `theorem ekPropTInf_holds (d : ℕ) : EKPropTInf d` (file line 534): the full pin, no extra hypothesis, not a special case.

## 2. Vacuity, hidden hypotheses, cycles

- `EKPropTInf` is a plain `Prop` (no structure, no bundled fields); `ekPropTInf_holds` has no argument but `d`.
- Proof: regime (i) `pti_i`, regime (ii) `pti_ii`, both private with explicit hypotheses
  (`hg hut ht h a b`), constant `ptiConstI k + ptiConstII k`, `d = k+2`: free of `L, g, u, t`.
- Dependencies: only merged modules (`import RBM3D.Evolution.Pins`, `import RBM3D.Defs.Sizes`); the new file is imported by nothing; no cycle.
- No external hypothesis introduced (no limit check needed).

## 3. Compiled nonempty instances (in the same file, lines 580–660)

Data `d = 3`, `L = 5` (and `L = 7`), `a = 0`, `b = ptiB = ![2,2,2]`; every hypothesis discharged by `norm_num`/`le_rfl`:
```
$ grep -n "private theorem ptiInst\|H 5\|H 7" RBM3D/Evolution/PropTInf.lean   (summary)
ptiInst_i        H 5 (1/2) (1/2) (9/10)      Or.inl   case (i)
ptiInst_ii       H 5 (1/2) (199/200) (999/1000) Or.inr case (ii)
ptiInst_bdry_t   H 5 (1/2) 0 (99/100)        Or.inl   1-t = g²/L² exactly, u = 0
ptiInst_bdry_ut  H 5 (1/2) (99/100) (99/100) Or.inl   u = t
ptiInst_bdry_u   H 5 (1/2) (99/100) (995/1000) Or.inr 1-u = g²/L² exactly
ptiInst_gL       H 5 10 0 (1/2)              Or.inr   g > L
ptiInst_uniform  one C at L = 5 (case i) and L = 7 (g = 8, case ii, a = ![1,0,0], b = ![1,2,3])
pti_inst_dist    zdistInf 3 5 (0 - ptiB) = 2 ∧ zdistD 3 5 (0 - ptiB) = 6   (decide +kernel)
```
Nondegenerate: `N`-torus `Z_5^3` nonempty, both regimes, all DECISIONS §29 boundaries, `a ≠ b`, distances differ between the
two norms. The instances conclude `∃ C > 0, …` (the same form as the merged `ekInstPropT`); `ptiInst_uniform` exhibits
one `C` across two torus sizes. Compiled in the module build below.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Evolution.PropTInf
✔ [3189/3189] Built RBM3D.Evolution.PropTInf (8.7s)
Build completed successfully (3189 jobs).
exit=0
$ lake env lean scratchpad/T2075/ax.lean   # #print axioms; `open private … from RBM3D.Evolution.PropTInf` for the instances
'RBM.ekPropTInf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_i' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_bdry_t' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_bdry_ut' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_bdry_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_gL' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.ptiInst_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.RBM3D.Evolution.PropTInf.0.RBM.pti_inst_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|^axiom| axiom |native_decide|set_option" RBM3D/Evolution/PropTInf.lean; echo grep-exit=$?
grep-exit=1
$ printf 'import RBM3D\nimport RBM3D.Evolution.PropTInf\n\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean   # registry pre-check
exit=0
axiom audit: 2511 theorems, 1057 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 81 (borrowed 2, owed 66, structural 13).
$ git diff --name-only main...t/T2075
RBM3D/Evolution/PropTInf.lean
$ git diff main...HEAD -- RBM3D/Evolution/Pins.lean RBM3D/Defs RBM3D/Test | wc -l
       0
```
Only the sole writable file is touched (`RBM3D/Test/Axioms.lean` unchanged; pre-check exit 0, so no registry row needed).
Frozen signatures untouched. Public names added: `EKPropTInf`, `ekPropTInf_holds` (pinned); all helpers `private`.

## 5. Paper deltas

The Lean statement equals the paper's `(TTT2)` with the paper's `L^∞` distance (§1); no Lean/paper difference
introduced. The prove report (d) proposes none; agreed. (The merged `EKPropT` uses `ℓ¹`; that is not this ticket's delta.)

## Observations (no statement/instance/build/axiom/delta effect)

- O1. The ticket says the file imports `RBM3D.Evolution.Pins` and Mathlib; the file also imports `RBM3D.Defs.Sizes`, which is
  required because `Gauss.zdistInf` is not in `Pins`' import closure (prove report F1). It does not import the root `RBM3D`.
  The ticket's check file imports the root `RBM3D`, which hid this. Dispatcher may record it; not a defect.
- O2. The ticket's first-route request ("state the doubling lemma … prove or refute it") is answered numerically in
  section (a) (doubling constant `c_d(L) → 0` as `L → ∞`), not by a Lean lemma; the direct route was taken. Not a target.
- O3. Registry counts in the prove report (2474/80) differ from this audit's (2511/81) because the copied build cache
  holds modules merged on `main` since; both exits are 0.

## Verdict

| target | verdict |
|---|---|
| `EKPropTInf` | PASS |
| `ekPropTInf_holds` | PASS |

Ticket T2075: **PASS**. No dispatcher sign-off needed.
