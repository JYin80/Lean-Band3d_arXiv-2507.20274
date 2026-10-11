Auditor model: claude-opus-5-5
# T2409 audit (round 1) — Sun Oct 11 05:06:44 UTC 2026
Branch `t/T2409` at 88cc0fa; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2409-audit1` (detached). Scratch: scratchpad `T2409/`.
Targets: (1) pin copy `ba_W_sub_one`, `BAGGGammaL`, `BAGGGammaR`, `BAGGGamma`; (2) `baGGGamma_holds : ∀ d, BAGGGamma d`; (3) C1/L5; (4) instances + numeric script; (5) registry none.

## 1. Statement: pin copy against the probe (`fe433f2:RBM3D/Probe/T2387Pins.lean`)
```
$ git show fe433f2:RBM3D/Probe/T2387Pins.lean > probe.lean
$ diff <(sed -n 286,293p probe.lean; sed -n 324,348p probe.lean) <(sed -n 50,57p BAGGExp.lean; sed -n 59,83p BAGGExp.lean) && echo IDENTICAL
IDENTICAL
```
Elaboration check (open contexts differ: probe `open RBM RBM.Gauss RBM.BA`, branch adds `RBM.Green`, `Matrix`, `ProbabilityTheory`).
The probe text was re-elaborated in its own open context in namespace `RBM.Graph.AuditProbe` (scratch `pincheck.lean`):
```
$ lake env lean pincheck.lean    # contains: example : BAGGGamma = AuditProbe.BAGGGamma := rfl  (and the same for
                                 #   BAGGGammaL, BAGGGammaR, @ba_W_sub_one), then #print axioms / #check below
'RBM.Graph.baGGGamma_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_W_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Graph.baGGGamma_holds : ∀ (d : ℕ), RBM.Graph.BAGGGamma d
exit=0
```
Target 2 is stated as `theorem baGGGamma_holds (d : ℕ) : BAGGGamma d`, i.e. for every `d`, all `L W` with `[NeZero L] [NeZero W]`,
`3 ≤ L`, all `g0 E t m` with `BASelf d L g0 E m`, `0 ≤ t < 1`, every resolvent polynomial `P` and every `x y y'`. This is the
ticket's statement, unconditional (no `gaussIBP` or other hypothesis). Shape matches merged siblings `BAlanlw` (`BAExpand.lean:117`)
and `BAlweight` (`BAExpandW.lean:82`): same binders, same law `PF d L W 0`.

Against the paper (`paper/tex/B_graphical_lemmas.tex:393-405`, label `GGGamma`):
```
$ sed -n 393,404p paper/tex/B_graphical_lemmas.tex   (excerpt)
\Gc _{y'x}\Gc _{xy} f(G) =_\E \sum_\beta S^+ _{x\beta } M _{\beta y}M_{y'\beta}f(G)
+ \sum_{ \beta}S^+_{x\beta}\left(\Gc _{\beta y}M_{y'\beta}+M_{\beta y}\Gc _{y'\beta}\right)f(G)
 +\sum_{w,\al,\beta}\left(1+M^+S^+\right)_{xw}M_{w\al} S_{\al \beta}\left( \Gc_{\beta\beta} G _{\al y} \Gc _{y'w}f(G)
 + \Gc _{\al w}G _{\beta y}G_{y'\beta} f(G) -  G _{\beta y} \Gc _{y'w} \partial_{h_{ \beta\al}}   f(G)\right)
```
Term by term against `BAGGGammaR` (`BAGGExp.lean:67-75`):
| paper | Lean | status |
|---|---|---|
| L: `Ǧ_{y'x}Ǧ_{xy} f` | `BAlwGc ω y' x * BAlwGc ω x y * BAlwf P ω` | same |
| sum 1 coeff `S⁺_{xβ}` | `(BAlwW - 1) x β` | D402 (corrected) |
| sum 1 summand `M_{βy}M_{y'β} f` | `BAlwM β y * BAlwM y' β * BAlwf` | same |
| sum 2 coeff `S⁺_{xβ}` | `(BAlwW - 1) x β` | D402 |
| sum 2 summand `(Ǧ_{βy}M_{y'β}+M_{βy}Ǧ_{y'β}) f` | same order, `BAlwGc`/`BAlwM` | same |
| sum 3 coeff `(1+M⁺S⁺)_{xw}` | `BAlwW x w`, `BAlwW := Ring.inverse (1 - M⁺S)` (`BAExpand.lean:82`) | equal (`1+M⁺S⁺ = W` by `ba_W_sub_one`) |
| sum 3 `M_{wα}S_{αβ}(ǦββGαyǦy'w f + ǦαwGβyGy'β f − GβyǦy'w ∂_{βα}f)` | `BAlwM w α * BAlwS α β * (…)`, `BAlwdf P ω β α` | same (index order `β α` matches `∂_{h_{βα}}`) |
| `=_E`, "differentiable `f`" | `∫ … ∂(PF d L W 0)`, `f = BAlwf P` | covered by D79, D64 (as for `BAlanlw`) |

## 2. Vacuity, hidden hypotheses, cycles
- `BASelf` is a `def` (`BA/MFixedPoint.lean:193`: `0 < m.im ∧ m = L^{-d} tr M^{(B)}`), no structure fields. No new hypotheses beyond the pin.
- Dependencies are merged results on `main`: `baLanlw_holds` (`Graph/BAExpand.lean:744`), `baW_mul`, `baW_isUnit` (`Graph/BAExpandW.lean`).
  The new file imports only `RBM3D.Graph.BAExpandW`; nothing on `main` imports it (new module), so no cycle.
- No external hypothesis (`gaussIBP` discharged inside `baLanlw_holds`); no limit check needed.
- C1/L5: external names used by the file (grep of identifiers, counts):
```
$ grep -oE "\b(ba[A-Z][A-Za-z_']*|BAExpand[A-Za-z_']*|lwWx[A-Za-z_']*|baM_[a-z_]*|gaussIBP[A-Za-z_]*)\b" BAGGExp.lean | sort | uniq -c    # output condensed to name count
  baLanlw_holds 3, baW_mul 3, baW_isUnit 2, baM_symm 1, baM_row_sq 1, baLweight_holds 1, baWx_baPoly 1, baWx_dh 2,
  lwWx_hasDerivAt_Gres 1, lwWxSizes 27, lwWxSec 3, lwWx_slice_sec 2, lwWx_continuous_sec 1, lwWxRename 4,
  BAExpand_bridge_hasDerivAt 1, BAExpand_tame_baG 1, BAExpand_Gc_zero 2, BAExpand_Hm_isHermitian 1, gaussIBP 3, baSelf_zero 7, …
$ lake env lean hyps.lean
@baW_mul : … 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (↑E) m → 0 ≤ t → t < 1 →
  BAlwW d L W g0 E t m * (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) = 1
baW_isUnit : … 3 ≤ L → … BASelf … → 0 ≤ t → t < 1 → IsUnit (1 - BAlwMp … * Matrix.of (BAlwS d L W t))
```
  No smallness of `g`, of `‖M − m₀I‖`, no `(Cλ)^{|a−b|}`, no `3 ≤ d`. (`baLweight_holds`, `baM_*`, `gaussIBP` appear in
  comments/docstrings or through `baW_isUnit`.)

## 3. Compiled nonempty instances (`RBM.Graph.BAGGExpInst`, `BAGGExp.lean:475-529`)
```
(I1) baGGGamma_holds 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I baSelf_zero (by norm_num) (by norm_num) _ _ _ _
     at P = 1, x = 0, y = e0, y' = e1                                   (d=3, L=3, W=1: 27 sites, t=1/2)
(I2) same data, P = X (true, e0, 0)                                     (nonconstant f = G_{e0 0})
(I3) same data, P = X (true,0,0) * X (false,e0,e0), x = e1, y = 0, y' = e0
(I4) W = 2 (216 sites), P = X (true,0,0), t = 1/2
(I5) t = 0 boundary (not counted as a witness)    (I6) ba_W_sub_one at d=3, L=3, W=1, t=1/2
```
`baSelf_zero : RBM.BA.BASelf 3 3 0 ((0 : ℝ) : ℂ) Complex.I` (`BAExpand.lean:865`). Every deterministic hypothesis
(`3 ≤ L`, `BASelf`, `0 ≤ t`, `t < 1`) is discharged; none is left open; `N = 27`/`216`, three distinct sites, `t = 1/2`
inside `[0,1)`. The ticket's `W = 1 or 2`, `t = 1/2`, `P = 1` and a nonconstant `P` are all present. Nondegenerate.

Numeric sanity check (ticket target 4; T2387 B10), rerun by the auditor:
```
$ python3 gg_pf.py      (sha256 3a66aaa22a77ee08593022b3fcd9a15883d258c4ca971bf0d6759982cac63d0e, same as the prove report)
N=1 (E=.3,t=.5,g=0)        printed   max|E[LHS]-E[RHS]| over 1 index tuples = 4.794e-01
N=1 (E=.3,t=.5,g=0)        corrected max|E[LHS]-E[RHS]| over 1 index tuples = 7.473e-17
N=1 f=1 (P=1)              printed   max|E[LHS]-E[RHS]| over 1 index tuples = 7.776e-01
N=1 f=1 (P=1)              corrected max|E[LHS]-E[RHS]| over 1 index tuples = 1.415e-16
N=2 coupled (g=.35,t=.6)   printed   max|E[LHS]-E[RHS]| over 32 index tuples = 8.572e-01
N=2 coupled (g=.35,t=.6)   corrected max|E[LHS]-E[RHS]| over 32 index tuples = 3.255e-16
N=27 Lean instance fill=0.0 printed   max|E[LHS]-E[RHS]| over 16 index tuples = 8.603e-01
N=27 Lean instance fill=0.0 corrected max|E[LHS]-E[RHS]| over 16 index tuples = 2.431e-11
N=27 Lean instance fill=1.3 printed   max|E[LHS]-E[RHS]| over 16 index tuples = 8.603e-01
N=27 Lean instance fill=1.3 corrected max|E[LHS]-E[RHS]| over 16 index tuples = 2.431e-11
N=2 coupled f=1 (P=1)      printed   max|E[LHS]-E[RHS]| over 8 index tuples = 7.606e-01
N=2 coupled f=1 (P=1)      corrected max|E[LHS]-E[RHS]| over 8 index tuples = 1.717e-16
```

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.BAGGExp 2>&1 | grep -E "error|BAGGExp|Build completed"
Build completed successfully (3782 jobs).
$ lake build 2>&1 | grep -E "^error|BAGGExp|Build completed"      # whole library incl. #assert_rbm_axioms (registry pre-check)
Build completed successfully (4216 jobs).
$ lake env lean docs/tickets/checks/T2409-check.lean >/dev/null 2>&1; echo "check exit=$?"
check exit=0
$ grep -n "sorry\|admit\|native_decide\|^axiom\|^@\[implemented_by\|^unsafe" RBM3D/Graph/BAGGExp.lean | wc -l
       0
$ git diff --name-status main...t/T2409
M	RBM3D.lean
A	RBM3D/Graph/BAGGExp.lean
$ git diff main...t/T2409 | grep -c "^-[^-]"        # removed lines (frozen signatures untouched)
0
$ git diff main...t/T2409 -- RBM3D.lean | grep "^+[^+]"
+import RBM3D.Graph.BAGGExp                          # after the last import, before #assert_rbm_axioms
$ wc -l RBM3D/Graph/BAGGExp.lean                     # stop line 1,300
     533 RBM3D/Graph/BAGGExp.lean
```
Axioms (section 1 output): `baGGGamma_holds`, `ba_W_sub_one`: `[propext, Classical.choice, Quot.sound]`.
Public declarations: `ba_W_sub_one`, `BAGGGammaL`, `BAGGGammaR`, `BAGGGamma` (pinned), `baGGGamma_holds` (pinned),
`BAGGExpInst.e0`, `BAGGExpInst.e1` (instance abbrevs in the ticket-named namespace); all helpers are `private BAGGExp_*`.

## 5. Paper deltas
- Coefficient of sums 1-2 (`S⁺_{xβ}` printed, `(W−1)_{xβ} = (M⁺S⁺)_{xβ}` in Lean): **D402** already in `docs/paper-deltas.md:1361`.
  The report's T2409a proposes recording it as proved in Lean (status update; numerics confirmed above).
- `f` resolvent polynomial vs "differentiable function of `G`": D64 (`paper-deltas.md:371`); `=_E` as equality of integrals
  over `PF`: D79 (`:389`). The report's T2409b restates both for this lemma. No uncovered difference.

## Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The ticket's merge note says the cone of `Graph/BAExpandW` is "2 modules"; the prove report's script gives 93 (94 for
  `BAGGExp`), none `LWExpCert*`. Ticket wording, not a branch defect; the lane conclusion stands.
- O2. The Lean instances use `g₀ = 0` (`M = iI`, scalar); the nonscalar-`M` case is exercised only by the numeric script
  (`N=2 coupled`, `|M_01| = 0.349`). The ticket allowed this data; the theorem is unconditional in `g₀`.
- O3. `ba_W_sub_one` is not used in the proof of `baGGGamma_holds` (only in (I6)); the proof uses `W·M⁺S = W − 1` from `baW_mul`.

## Verdicts
| target | verdict |
|---|---|
| 1 pin copy (`ba_W_sub_one`, `BAGGGammaL/R`, `BAGGGamma`) | PASS (text identical, definitionally equal to the probe) |
| 2 `baGGGamma_holds : ∀ d, BAGGGamma d` | PASS (unconditional, standard axioms) |
| 3 C1/L5 | PASS |
| 4 instances + numeric script | PASS |
| 5 registry none / merge lane | PASS (full build with `#assert_rbm_axioms` passes) |

**Overall: PASS.** No dispatcher sign-off needed.
