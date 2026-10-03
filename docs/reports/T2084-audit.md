Auditor model: claude-opus-5-5
# T2084 audit (round 2) — Sat Oct  3 23:11:19 UTC 2026

Branch `t/T2084` at `c626bdf` (no Lean change since round 1; the round-1 repair edited only prove report (d)).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2084-audit2` (detached). Scratch: `scratchpad/T2084/` (`pin.py`, `ax.lean`, `build.out`).
Targets: `EECutIdentity` (proved by `eeCutIdentity`), `QVPropagated` (`qvPropagated`), `EEShift` (`eeShift`), `v_gradMat_eq_quadVar`.

## 1. Statements against the pin
The check file only `#check`s `gradMat`, `HermTestFun`, `stepDecomp`. So the pin is RBM2D's text at `c9a24cf`, with the ST1-COMMON renaming plus `W^2 → W^d`, `Z2 → Zd d` and the coupling `g`.
`pin.py` extracts each declaration up to `:=` (for defs, the whole body), normalises whitespace, renames the **RBM2D side only** (`Z2 L→Zd d L`, `Idx L W→Idx d L W`, `Coord→CoordF d`, `gvar L W c→gvarF d L W g c`, `(L W : ℕ)→(d L W : ℕ) (g : ℝ)`, `(W*L)^2→(W*L)^d`, `(W:ℂ)^2→(W:ℂ)^d`, `SB L→SB d L g`, `(d : Sizes)→{d : ℕ} (sz : Sizes d)`, `gvar (d.L n) (d.W n) c→gvarF d (sz.L n) (sz.W n) (sz.lam n) c`) and compares the result word by word:
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Path/{QVIdentity,QVForm,Step2Vocab}.lean > r2_*.lean
$ python3 pin.py r2_QVIdentity.lean EECutIdentity,QVPropagated,EEShift
EECutIdentity: IDENTICAL
QVPropagated: IDENTICAL
EEShift: IDENTICAL
$ python3 pin.py r2_QVForm.lean v_gradMat_eq_quadVar
v_gradMat_eq_quadVar: IDENTICAL
$ python3 pin.py r2_Step2Vocab.lean EE,cutDeriv1,cutDeriv2,loopDeriv
EE: IDENTICAL
cutDeriv1: IDENTICAL
cutDeriv2: IDENTICAL
loopDeriv: IDENTICAL
```
`loop6` changes only its vocabulary. RBM2D has `gloop L W (blockMat M) (spectralZ E u) (loopOf σ a)`; RBM3D has `loopFine d L W M (zt E u) σ a` (merged `Loop/GLoopFlow.lean`, `Defs/Semicircle.lean`).
**`EE` against the paper** (`defEOTE`, `paper/tex/3_5_Loop_Hierarchy.tex:176-190`, `def_diffakn_k`):
- At `n = 2`, `k = 1`, the paper's string is `(a1,a2,b,a'2,a'1,b')` with `σ⊗σ̄ = (σ1,σ2,σ1,−σ1,−σ2,−σ1) = (+,−,+,−,+,−)`.
- At `k = 2` it is `(a2,a1,b,a'1,a'2,b')` with `(−,+,−,+,−,+)`.
- Lean (file:368) has `![a.1,a.2,b',a'.2,a'.1,b]`/`![T,F,T,F,T,F]` and `![a.2,a.1,b',a'.1,a'.2,b]`/`![F,T,F,T,F,T]`, with weight `SB d L g b b'` and prefactor `(W:ℂ)^d`.
- `b ↔ b'` is a relabelling of the double sum, and `SB` is symmetric (`SB_transpose`). So `EE = (𝓔⊗𝓔)^{M,(2)}_{u,(+,−),a,a'}`.

The hypotheses, the quantifier order (fixed `d L W g`, then `E u (Δ)`, then `M`, then labels) and the window `0 ≤ u`, `0 ≤ Δ`, `u+Δ<1`, `u<1` are RBM2D's. The constants `2` (QVPropagated) and `16 N² η_{u+Δ}^{-7} Δ` with `N = (WL)^d` (EEShift) are RBM2D's.
All four targets are unconditional: no `Prop` hypothesis, so none is a conditional adapter or a special case.
Every public declaration of RBM2D `QVForm`/`QVIdentity` is ported (none dropped):
```
$ for each RBM2D public def/theorem n: grep -cE "^(def|theorem|...) n\b" r3.lean
vB:1 vB_self:1 vB_nonneg_diag:1 v_sum_eq:1 abs_vB_le:1 v_gradMat_eq_quadVar:1 QVForm_check_v_gradMat_eq_quadVar:1
EECutIdentity:1 QVPropagated:1 EEShift:1 eeCutIdentity:1 qvPropagated:1 eeShift:1
```
Class b (`d`-exponents): `d` enters only through `(W:ℂ)^d` in `EE` and `N = (WL)^d` in `EEShift`. `EEShift` is proved at general `d`, so no statement is false at `d ≥ 3`.
**Statement: PASS for all four targets.**

## 2. Vacuity, hidden hypotheses, cycles
```
$ git grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|implemented_by|unsafe|^\s*(structure|class) " t/T2084 -- RBM3D/Path/QVIdentity.lean; echo "grep exit=$?"
grep exit=1
$ grep -n "^import" RBM3D/Path/QVIdentity.lean ; for m in ...; grep -c "^import RBM3D.$m$" RBM3D.lean (main)
6:import RBM3D.Path.StepDecomp   7:import RBM3D.Green.Pins   8:import RBM3D.Gauss.FlowCalculus   9:import RBM3D.Induction.ConArgDet
Path.StepDecomp root=1  Green.Pins root=1  Gauss.FlowCalculus root=1  Induction.ConArgDet root=1
```
- There is no structure or class, so no hypothesis can hide in a field.
- The three pins are `Prop` defs (file:398, 410, 421) proved in the same file by `eeCutIdentity : EECutIdentity` (795), `qvPropagated : QVPropagated` (917) and `eeShift : EEShift` (1115).
- No theorem takes a pin as a hypothesis, and every import is a merged module, so there is no cycle.
- There is no external hypothesis, so no limit check is needed. PASS.

## 3. Compiled nonempty instances (file:1229-1304, `section Instances`; they compile, §4)
```
1234 example : EE 3 4 32 (1/64) 1 (1/2) 1 (0,1) (1,0) = ∑ c : CoordF 3 4 32, gvarF.. * (cutDeriv1.. * conj .. + cutDeriv2.. * conj ..) :=
       eeCutIdentity 3 4 32 (1/64) 1 (1/2) (by norm_num) ×4 1 Matrix.isHermitian_one (0,1) (1,0)
1244 example : ∑ c, gvarF.. * ‖∑ b, 1 * loopDeriv ..‖^2 ≤ 2 * (∑ b, ∑ b', 1 * conj 1 * EE ..).re :=
       qvPropagated 3 4 32 (1/64) 1 (1/2) (by norm_num) ×4 1 Matrix.isHermitian_one (fun _ => 1)
1254 example : ‖EE..(1/2+1/1000).. - EE..(1/2)..‖ ≤ 16 * ((32*4)^3)^2 * (etaT 1 (1/2+1/1000))⁻¹^7 * (1/1000) := eeShift 3 4 32 (1/64) 1 (1/2) (1/1000) ...
1261 eeShift at u = 0 (0 ≤ u by le_rfl);  1268 eeShift at u = 998/1000, u + Δ = 999/1000
1276 example : linTrVar (sz := sz0) 0 (gradMat (fun A => ↑(sin (Re tr A))) 1) = ∑ c, gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c * ‖fderiv ..‖^2 :=
       QVForm_check_v_gradMat_eq_quadVar sz0 0 Matrix.isHermitian_one
336  QVForm_check_v_gradMat_eq_quadVar := v_gradMat_eq_quadVar sz n (QVForm_check_differentiable sz n M) (fun _ _ => Complex.ofReal_im _) hM
```
- The data are `d = 3`, `L = 4`, `W = 32` (merged `sz0`), `g = 1/64`, `N = 128^3`, `|E| = 1 < 2`, `u = 1/2`, `Δ = 10⁻³`, `M = 1` (Hermitian), and labels `(0,1) ≠ (1,0)`.
- Every hypothesis is discharged: `3 ≤ L`, `|E| < 2`, `0 ≤ u`, `u < 1`, `0 ≤ Δ`, `u+Δ < 1`, Hermitian `M`, and differentiability and reality of `Φ`.
- The data are nondegenerate: no `N = 0`, no empty index, no collapsed window, no `False` premise. Both ends of the window are exercised. PASS for all four targets.

Observation (not a RETURN): at `M = 1` the resolvents are scalar, so for `a ≠ a'` both sides of the 1234 example are probably `0`. The theorems are universal identities, and every hypothesis is discharged at concrete data. Prove report (a)(ii) has the nonzero numerical checks.

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Path.QVIdentity          # audit worktree, output in build.out
✔ [3340/3340] Built RBM3D.Path.QVIdentity (7.5s)
Build completed successfully (3340 jobs).
exit=0
$ grep -nE "^(warning|error)" build.out | grep -c QVIdentity
0                                            # warnings only in merged Path/Walk, Path/Markov (linter)
$ lake env lean ax.lean     # #print axioms RBM.Path.<n> for the 18 public names, grouped by axiom set
 [propext, Classical.choice, Quot.sound] <- vB vB_self vB_nonneg_diag v_sum_eq abs_vB_le v_gradMat_eq_quadVar QVForm_check_v_gradMat_eq_quadVar loop6 EE cutDeriv1 cutDeriv2 loopDeriv EECutIdentity QVPropagated EEShift eeCutIdentity qvPropagated eeShift
exit=0
$ git diff --name-only main...t/T2084
RBM3D/Path/QVIdentity.lean
$ git merge-base main t/T2084; git log -1 --format=%h main
6e7bb9c
7f9bfa1
$ for n in <18 public names>; do git grep -nE "(def|theorem|lemma|abbrev) +$n\b" main -- RBM3D | wc -l; done   # against current main 7f9bfa1
loop6=0 EE=0 cutDeriv1=0 cutDeriv2=0 loopDeriv=0 EECutIdentity=0 QVPropagated=0 EEShift=0 eeCutIdentity=0 qvPropagated=0 eeShift=0 vB=0 vB_self=0 vB_nonneg_diag=0 v_sum_eq=0 abs_vB_le=0 v_gradMat_eq_quadVar=0 QVForm_check_v_gradMat_eq_quadVar=0
```
- The branch changes one new sole-writable file and no frozen signature.
- `RBM3D/Test/Axioms.lean` is unchanged. No pin is used as a hypothesis, so DECISIONS §20 requires no registry line.
- No public name clashes with current `main` (after the T2079/T2080 merges). The hub's full build at merge is still required. PASS.

## 5. Paper-delta coverage
```
$ grep -n "T2084[a-z]" docs/reports/T2084-prove.md | cut -c1-90
255:- `T2084a`: the coupling `g` of `S^{(B)}(g)` is a parameter of `EE`, `EECutIdentity`, `QV
256:- `T2084b` (process, for the dispatcher): `loop6`, `EE`, `cutDeriv1`, `cutDeriv2`, `loopD
257:- `T2084c` (added Sat Oct  3 23:08:40 UTC 2026, audit round 1 item 1): `(𝓔⊗𝓔)` (`defEOTE`
270:- `T2084d` (added Sat Oct  3 23:08:40 UTC 2026, audit round 1 item 2): `EE` is `defEOTE` o
$ grep -nE "T2084|EECut|QVPropagated|EEShift" docs/paper-deltas.md; echo "exit=$?"
exit=1                                        # not yet appended; candidates suffice
$ python3 -c "g=1/(0-1j); gs=g.conjugate(); c1=-(g*g*gs); c2=-(g*gs*gs); print(c1,c2,c1+c2)"   # M=0,E=0,u=0: z=i, scalar G
(-0-1j) (-0+1j) (-0+0j)
```
Each Lean/paper difference and the candidate that covers it:
- (i) The coupling `g` and `gvarF` at `sz.lam n`: covered by `T2084a`.
- (ii) `(𝓔⊗𝓔)` is not literally the QV (`3_5:166`). Lean proves the per-cut identity and `QV ≤ 2 Re Σκκ̄(𝓔⊗𝓔)`. Covered by `T2084c`.
  - The candidate's witness checks out. At `z = i` the two cut coefficients are `−i` and `+i` (above), so `loopDeriv = cutDeriv1 + cutDeriv2 = 0` and the QV is `0`, while `EE(a,a) > 0` (prover's `qvwit.py` output).
  - The candidate cross-references D54 and RBM2D delta #22 (T2049e).
- (iii) `EE` covers only `n = 2`, `σ = (+,−)`, while the paper uses general `(n, σ)` and `max_σ` (`eq:MG_nloop`, `3_5:1043`). `EEShift` is Lean-only. Covered by `T2084d`.
- No other difference was found. PASS.

## Verdict
| target | statement | vacuity/cycle | instance | build/axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `EECutIdentity` / `eeCutIdentity` | PASS | PASS | PASS | PASS | `T2084a`, `T2084c`, `T2084d` | **PASS** |
| `QVPropagated` / `qvPropagated` | PASS | PASS | PASS | PASS | `T2084a`, `T2084c` | **PASS** |
| `EEShift` / `eeShift` | PASS | PASS | PASS (window ends) | PASS | `T2084a`, `T2084d` | **PASS** |
| `v_gradMat_eq_quadVar` | PASS | PASS | PASS | PASS | `T2084a` | **PASS** |

**Overall: PASS.** No dispatcher sign-off needed.
Observations:
- (1) The `M = 1` instances are probably `0 = 0` / `0 ≤ 0` for `a ≠ a'`. This does not affect the verdict.
- (2) `T2084b` asks the dispatcher to name `loop6`, `EE`, `cutDeriv1`, `cutDeriv2`, `loopDeriv` (public in `RBM.Path`) in the downstream tickets ST2-26 and ST2-28.
