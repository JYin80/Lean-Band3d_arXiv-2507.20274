Auditor model: claude-opus-5-5

# T2301 audit (UN-29, `Universality/GUEPhase/KPrim`), round 1

Written: Tue Oct  6 14:14:23 UTC 2026. Branch `t/T2301` at `c3204a2`; worktree `RBM3D-wt/T2301-audit1` (detached); scratch `<scratchpad>/T2301/`.

## 1. Diff scope and forbidden tokens

```
$ git diff --stat main...t/T2301
 RBM3D/Universality/GUEPhase/KPrim.lean | 930 +++++++++++++++++++++++++++++++++
 1 file changed, 930 insertions(+)
$ git diff main...t/T2301 | grep -nE "^\+.*\b(sorry|admit|native_decide|axiom)\b" ; echo "forbidden-token hits: $?"
forbidden-token hits: 1          # grep exit 1 = no match
$ git diff main...t/T2301 -- RBM3D/Test/Axioms.lean | wc -l
       0                         # no registry line, as the ticket expects
```
Only the sole writable file is touched; it is new, so no merged/frozen signature changes.
Imports (file `:6-10`): `GUEPhase.Bootstrap`, `ZeroModeProfile`, `Loop.KLTree`, `Defs.Semicircle`, `Mathlib.Analysis.ODE.ExistUnique` -- all merged; no cycle.

## 2. Build (audit worktree)

```
$ lake build RBM3D.Universality.GUEPhase.KPrim ; echo exit=$?
exit=0
$ grep -E "KPrim|error|Build completed" build.log
Build completed successfully (3745 jobs).
```
(no warning or error line on `KPrim.lean`; the remaining warnings are on merged upstream files.)

## 3. Statements against the pins (script)

`PinCheck.lean` = imports `KPrim`, `OUInterfaceK`, `Mathlib.Analysis.ODE.ExistUnique`, then section 2 of
`docs/tickets/checks/T2301-check.lean` copied verbatim by `awk`, then one
`example : T2301Check.<pin> := fun … => <target> …` per pin, the three vocabulary `rfl` examples, and `#print axioms`.

```
$ awk '/^namespace RBM.Univ.GUEPhase.T2301Check/{p=1} p && /^\/-! Shape checks/{exit} p' T2301-check.lean > pin_from_check.txt
$ diff pin_from_check.txt pin_in_scratch.txt && echo "pins verbatim: identical"
pins verbatim: identical (     106 lines)
```
Appended checks (excerpt, all 11 pins + 3 rfl):
```
example : T2301_kTwoGUE_eq_ThetaTilde := fun d L _ W g hL m ζ t0 σ₁ σ₂ hT h0 h1 a b =>
  kTwoGUE_eq_ThetaTilde d L W hL g m σ₁ σ₂ hT h0 h1 a b
example : T2301_hasDerivAt_kTwoGUE := fun d L W _ _ g m t1 t σ₁ σ₂ hL h1 h2 a₁ a₂ =>
  hasDerivAt_kTwoGUE d L W hL g m σ₁ σ₂ h1 h2 a₁ a₂
example : T2301_lemT_mul_kTwoGUE_pm_eq_profPMTilde := fun d sz n z hz ζ h0 h1 a b =>
  lemT_mul_kTwoGUE_pm_eq_profPMTilde sz n hz h0 h1 a b
example : T2301_gueK_exists := fun d L _ W _ g E t1 t0 n0 hL hE ht1 ht10 ht0 =>
  gueK_exists d L W hL g hE ht1 ht10 ht0 n0
example (d L μ t1 t) : gueShift d L μ t1 t = gueShiftV d L μ t1 t := rfl
example (d L : ℕ) [NeZero L] (W g m t1 t σ₁ σ₂ a b) :
    kTwoGUE d L W g m t1 t σ₁ σ₂ a b = kTwoGUEV d L W g m t1 t σ₁ σ₂ a b := rfl
example (d L : ℕ) [NeZero L] (W g m t1 t) (I : LoopIdx (Zd d L)) :
    kTwoGUELoop d L W g m t1 t I = kTwoGUELoopV d L W g m t1 t I := rfl
```
```
$ lake env lean PinCheck.lean ; echo exit=$?
<only linter.unusedVariables warnings on the lambda binders of the scratch examples; no error>
'RBM.Univ.GUEPhase.gueK_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE_eq_ThetaTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.primRhsGUE_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE_deriv_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.hasDerivAt_kTwoGUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.hasDerivAt_kTwoGUELoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pm_eq_profPMTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pp_eq_profPPTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Every pin is inhabited by its target applied argument-for-argument (only positional order of `hL`/`g` and
implicit/explicit status differ; no hypothesis added, none dropped). The three definitions are `rfl` to the
pinned vocabulary, so `W^{-d}`, `L^d`, `Θ(g)` with free real `g`, and argument order `d L W g` match the pin.
No `3 ≤ d`, no condition on `g`; `3 ≤ L`, `NeZero W`, `|E| < 2`, `0 < z.im`, `0 ≤ t₁ ≤ t₀ < 1`,
`0 ≤ ζ ≤ 1` exactly as in the ticket's §29 checklist.

## 4. Registry pre-check

```
$ printf 'import RBM3D\nimport RBM3D.Universality.GUEPhase.KPrim\n#assert_rbm_axioms\n' > Reg.lean
$ lake env lean Reg.lean ; echo exit=$?
axiom audit: 8639 theorems, 2828 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
exit=0
```

## 5. Hidden hypotheses, vacuity, cycles

- No new `structure`/`class`/`Prop`-valued `def`: the declaration list (`grep -nE "^(theorem|def|private|example|structure|class)"`)
  shows 3 `def`s (`gueShift`, `kTwoGUE`, `kTwoGUELoop`, all `ℂ`-valued), 11 public theorems, private helpers
  (`KPrim_…`, §3 (E)), and 13 `example`s. The only structure used is the merged `RBM.Gauss.Sizes` (targets 9–10 use
  only `sz.L`, `sz.W`, `sz.lam`, `sz.three_le_L`).
- No external hypothesis: every hypothesis is a scalar/size condition, so no limit check is needed.
- Dependencies: merged modules only (§1).

Name-clash grep (`git grep -lw <name> main -- RBM3D | wc -l`):
```
gueShift 0;kTwoGUE 0;kTwoGUELoop 0;kTwoGUE_self 0;kTwoGUE_eq_ThetaTilde 0;primRhsGUE_two 0;kTwoGUE_deriv_identity 0;
hasDerivAt_kTwoGUE 0;hasDerivAt_kTwoGUELoop 0;lemT_mul_kTwoGUE_pm 0;lemT_mul_kTwoGUE_pp 0;
lemT_mul_kTwoGUE_pm_eq_profPMTilde 0;lemT_mul_kTwoGUE_pp_eq_profPPTilde 0;gueK_exists 0;
```

## 6. Compiled nonempty instances (namespace `KPrimCheck`, `KPrim.lean:786-928`, compiled in §2)

| Target | Instance data (file line) | Hypotheses discharged |
|---|---|---|
| `kTwoGUE_self` | `:802` d=3, L=3, W=2, g=1, m=mSigma 0, t₁=7/20, all σ, all a b | none needed |
| `kTwoGUE_eq_ThetaTilde` | `:810` ζ=1/2, t₀=7/10, all σ, a, b; `:818` same at g=1/2 | `3≤3`, `‖t₀μ‖<1` (merged `norm_mul_mSigma_lt_one`), `0≤ζ≤1` by `norm_num` |
| `hasDerivAt_kTwoGUELoop` | `:828` t₁=7/20, t=1/2, all σ, a | `‖t₁μ‖<1`, `tμ≠1` (from `‖tμ‖<1`) |
| `gueK_exists` | `:838` E=0, [7/20, 7/10], n₀=3; `:850` loop `⟨[t,f,t],[0,![1,0,0],![2,0,0]]⟩` at t=1/2 | `3≤L`, `|0|<2`, `0≤7/20≤7/10<1`; WF by `rfl`, length bounds by `decide` |
| `primRhsGUE_two` | `:860` K=kTwoGUELoop, (+,−), (0, ![1,0,0]) | none needed |
| `kTwoGUE_deriv_identity` | `:869` d=3, W=2, μ=1, p=13/20, q=1/2, s=3/20, L=3 | `q+sμ=p`, `p,q,L≠0` by `norm_num` |
| `hasDerivAt_kTwoGUE` | `:879` (+,+), (0, ![1,0,0]), t=1/2 | as `:828` |
| `lemT_mul_kTwoGUE_pm/pp` | `:891`, `:901` z=I, ζ=1/2, all a b | `0<I.im` by `simp`, `0≤ζ≤1` |
| targets 9–10 (profile bridges) | `:910`, `:920` `SizesInst.sz0`, n=0, z=I, ζ=1/2, all a b | as above; `3≤L` from `sz` |

All data nondegenerate (L=3 so `Zd 3 3` has 27 points, nonempty window `[7/20, 7/10]`, n₀=3 ≥ 2, no `False`
premise, small witnesses). Every endpoint theorem has at least one instance; every deterministic hypothesis is
discharged; no hypothesis is left open in any example.

## 7. Paper deltas

Prove report `(d)` lines 257–259 propose `T2301a` (band coupling `g` through `Θ(g)`, `Θ̃(g)`; holds for all real
`g`), `T2301b` (`W⁻² ↦ W^{-d}`, `L² ↦ L^d`; no `3 ≤ d`), `T2301c` (class T: band here, BA in BA-C3; ODE generic;
profile bridges 9–10 new, not a paper statement) -- the three the ticket asks for. The Lean statements differ from
§7.2 of [YY_25] only in these respects (checked against the pins in §3); `gueK_exists` is existence only, as in the
RBM2D source and as the ticket states ("uniqueness ... not in the source"), recorded in the `hasDerivAt_kTwoGUE`
docstring. Coverage complete.

## Verdict

| Target | Verdict |
|---|---|
| `gueShift`, `kTwoGUE`, `kTwoGUELoop` (defs) | PASS (`rfl` to pinned vocabulary) |
| `kTwoGUE_self` | PASS |
| `kTwoGUE_eq_ThetaTilde` | PASS |
| `primRhsGUE_two` | PASS |
| `kTwoGUE_deriv_identity` | PASS |
| `hasDerivAt_kTwoGUE` | PASS |
| `hasDerivAt_kTwoGUELoop` | PASS |
| `lemT_mul_kTwoGUE_pm`, `lemT_mul_kTwoGUE_pp` | PASS |
| `lemT_mul_kTwoGUE_pm_eq_profPMTilde`, `lemT_mul_kTwoGUE_pp_eq_profPPTilde` | PASS |
| `gueK_exists` | PASS |

**T2301: PASS.** No dispatcher sign-off needed.
