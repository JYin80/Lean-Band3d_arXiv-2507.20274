Auditor model: claude-opus-5-5
# T2072 audit (round 1) — Sat Oct  3 20:54:00 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2072-audit1` (detached at `4d70e54`). Ticket pin: port of RBM2D `Path/OneStep` + `Path/DriftLip` at `c9a24cf` with the d-dimensional replacements (no pinned text in `docs/tickets/checks/T2072-check.lean`, which only `#check`s upstream names). Targets: `genMat`, `envConst`, `OneStepEnvelope`/`oneStepEnvelope`, `norm_loopDrift_sub_le` (+ ported `norm_green_sub_le_of_herm`, `DriftLip_eGterm`, `loopDrift`, `loopDrift_eq`, `driftLip`).

## 1. Statement vs the RBM2D source (independent script `ext.py`: extract each declaration from RBM2D `c9a24cf` and RBM3D, apply the ticket renames, word diff)
```
$ python3 ext.py; git diff --no-index --word-diff=plain a_<n>.txt b_<n>.txt
## genMat
[-{L-]{+(d+} {+L+} [-ℕ}-]{+ℕ)+} {+(g+} {+:+} {+ℝ)+} 
## envConst
[-(L-]{+(d+} {+L+} 
## OneStepEnvelope
[-(L-]{+(d+} {+L+} {+(g+} {+:+} {+ℝ)+} {+d+} {+L+} {+W+} {+g+} {+d+} 
## norm_green_sub_le_of_herm

## DriftLip_eGterm
[-(L-]{+(d+} {+L+} {+(g+} {+:+} {+ℝ)+} 
## loopDrift
{+d+} {+g+} 
## loopDrift_eq
{+d+} {+L+} {+W+} {+g+} {+d+} {+g+} 
## driftLip
[-(L-] [-W-] [-n-]{+(n+} 
## norm_loopDrift_sub_le
{+d+} {+L+} {+W+} {+g+} {+d+} {+L+} {+W+} {+g+} {+d+} 
```
Renames applied before the diff: `Z2 L→Zd d L`, `BlockIndex L W→Vtx d L W`, `Gsig→Gres`, `gloop L W→loopL d L W`, `spectralZ→zt`, `KLoop.mSig→mSigma`, `KLoop.primRhs L W→Loop.treeEqRhs d L W g`, `Coord/gvar/P→CoordF/gvarF/PF d L W g`, `(W*L)^2→(W*L)^d`, `(W:ℂ)^2→(W:ℂ)^d`. Residual differences are only the new explicit parameters `d`, `g` (and `driftLip`'s `d L W` coming from a section `variable`). Hypotheses, quantifier order (`d L W g` fixed, then `E`, `|E|<2`, `I`, `I.WF`, `u Δ`, window `0≤u`, `0≤Δ`, `u+Δ<1`, `M` Hermitian), loss `Δ^{3/2}`, and the constants are RBM2D's with `N=(WL)^d`.

d-dimensional exponents (checked against the source and the paper): weight of `DriftLip_eGterm` is `W^d`, as in `(pro_dyncalK)`:
```
$ sed -n 991,993p paper/tex/1_2_Intro_model_result.tex
       \partial_t{\cal K}^{(n)}_{t, \bsig, \ba} 
       =  
       W^d \sum_{1\le k < l \le n} \sum_{a, b} \left( \cutL^{(a)}_{k, l} \circ \mathcal{K}^{(n)}_{t, \bsig, \ba} \right) S^{(\sB)}_{ab} \left( \cutR^{
```
Merged vocabulary used by the statements (`#check`/`#print` in the audit worktree, scratch `ax.lean`):
```
PF : (d L W : ℕ) → ℝ → [NeZero W] → MeasureTheory.Measure (Ω d L W)
gvarF : (d L W : ℕ) → ℝ → [NeZero W] → CoordF d L W → NNReal
svarF : (d L W : ℕ) → ℝ → [NeZero W] → Idx d L W → Idx d L W → ℝ
Xmat : (d L W : ℕ) → [NeZero L] → [NeZero W] → Ω d L W → Matrix (Idx d L W) (Idx d L W) ℂ
coordinateMatrix : (d L W : ℕ) → [NeZero L] → [NeZero W] → CoordF d L W → Matrix (Idx d L W) (Idx d L W) ℂ
blockMat : (d L W : ℕ) → [NeZero L] → [NeZero W] → Matrix (Idx d L W) (Idx d L W) ℂ → Matrix (Vtx d L W) (Vtx d L W) ℂ
loopL : (d L W : ℕ) → [NeZero L] → Matrix (Vtx d L W) (Vtx d L W) ℂ → ℂ → Loop.LoopIdx (Zd d L) → ℂ
Loop.treeEqRhs : (d L : ℕ) → [NeZero L] → ℕ → ℝ → (Loop.LoopIdx (Zd d L) → ℂ) → Loop.LoopIdx (Zd d L) → ℂ
mSigma : ℝ → Bool → ℂ
zt : ℝ → ℝ → ℂ
etaT : ℝ → ℝ → ℝ
SB : (d L : ℕ) → ℝ → Matrix (Zd d L) (Zd d L) ℂ
@Loop.LoopIdx.WF : {α : Type u_1} → Loop.LoopIdx α → Prop
def RBM.zt : ℝ → ℝ → ℂ :=
fun E t => ↑E + (1 - ↑t) * mE E
def RBM.Gauss.etaT : ℝ → ℝ → ℝ :=
fun E t => (1 - t) * (mE E).im
def RBM.Loop.LoopIdx.WF.{u_1} : {α : Type u_1} → Loop.LoopIdx α → Prop :=
fun {α} x => x.σ.length = x.a.length
```
`zt E u = E+(1-u)m(E)`, `etaT = (1-u) Im m(E)`, `WF` = equal list lengths: the time window and `hz` are the source's. **Statement: PASS** for all targets (the `d`, `g` generalisation is a strengthening of a uniform-in-`g` port, not a special case; no `3 ≤ L` was added).

## 2. Vacuity, hidden hypotheses, cycles
- `OneStepEnvelope : Prop` is a plain `∀`-statement (no structure), proved unconditionally by `oneStepEnvelope : OneStepEnvelope`; `norm_loopDrift_sub_le` has only the deterministic hypotheses `hz`, Hermitian, `I.WF`, `1 ≤ I.a.length`. No external hypothesis, no structure field.
- Imports are all merged modules listed in `main:RBM3D.lean`:
```
RBM3D.Loop.GLoopFlow in root: 1
RBM3D.Loop.TreeRep in root: 1
RBM3D.Gauss.FlowCalculus in root: 1
RBM3D.Gauss.FineModel in root: 1
RBM3D.Gauss.DominationAt in root: 1
RBM3D.Green.EntryCore in root: 1
RBM3D.Analysis.Resolvent in root: 1
```
- Public RBM2D declarations at `c9a24cf` (names) and the RBM3D public declarations:
```
$ grep -hE '^(noncomputable )?(def|theorem) ' r2_os.lean r2_dl.lean | awk '{ if ($1=="noncomputable") print $3; else print $2 }' | tr '\n' ' '
norm_green_sub_le_of_herm DriftLip_eGterm loopDrift loopDrift_eq driftLip norm_loopDrift_sub_le DriftLip_check_L3_W1 genMat envConst OneStepEnvelope oneStepEnvelope OneStep_check_L3_W1 
$ grep -hE '^(noncomputable )?(def|theorem|lemma|abbrev|instance|structure) ' RBM3D/Path/OneStep.lean | awk '{ if ($1=="noncomputable") print $3; else print $2 }' | tr '\n' ' '
genMat envConst OneStepEnvelope norm_green_sub_le_of_herm DriftLip_eGterm loopDrift loopDrift_eq driftLip norm_loopDrift_sub_le oneStepEnvelope 
```
All public declarations ported; the two RBM2D `*_check_L3_W1` theorems are replaced by the `example`s of §3. No cycle (the module imports only merged modules; no target is used as its own hypothesis). **PASS.**

## 3. Compiled nonempty instances (section `Instances`, compiled by the build in §4)
```
$ grep -nE '^example|oneStepEnvelope [0-9]|norm_loopDrift_sub_le [0-9]|norm_green_sub_le_of_herm Matrix|OneStep_instLoop \(d L|WF := rfl' RBM3D/Path/OneStep.lean
2368:private def OneStep_instLoop (d L : ℕ) : Loop.LoopIdx (Zd d L) := ⟨[true, false], [0, 0]⟩
2370:private theorem OneStep_instLoop_wf (d L : ℕ) : (OneStep_instLoop d L).WF := rfl
2374:example :
2384:  oneStepEnvelope 3 3 2 (1 / 2) 0 (by norm_num) (OneStep_instLoop 3 3) (OneStep_instLoop_wf 3 3)
2389:example :
2399:  oneStepEnvelope 3 4 32 (1 / 64) 0 (by norm_num) (OneStep_instLoop 3 4) (OneStep_instLoop_wf 3 4)
2403:example : 0 < envConst 3 3 2 0 2 (1 / 2 + 1 / 1000) := by
2410:example :
2418:  exact norm_loopDrift_sub_le 3 3 2 (1 / 2) hz Matrix.isHermitian_zero Matrix.isHermitian_one
2422:example :
2425:  norm_green_sub_le_of_herm Matrix.isHermitian_zero Matrix.isHermitian_one (by simp)
  have hz : (zt 0 (1 / 2)).im ≠ 0 := by
    rw [spectralZ_im]
```
- `oneStepEnvelope`: applied at `d=3, L=3, W=2` (`N=216`), `g=1/2`, `E=0`, loop `([+,-],[0,0])` (length 2, `WF` by `rfl`), `u=1/2`, `Δ=1/1000`, `M=1`; and at `(L,W,g)=(4,32,1/64)`, `u=0`. Every hypothesis (`|E|<2`, `WF`, `0≤u`, `0≤Δ`, `u+Δ<1`, Hermitian) is discharged by `norm_num`/`rfl`/`Matrix.isHermitian_one`. Nondegenerate (no `N=0`, open window, `Δ>0`).
- `norm_loopDrift_sub_le`: at `d=3, L=3, W=2, g=1/2, E=0, u=1/2`, `M₁=0`, `M₂=1` (`‖M₁-M₂‖≠0`), `hz` discharged from `spectralZ_im` and `spectralM_im_pos`, `1 ≤ I.a.length` by `simp`.
- `norm_green_sub_le_of_herm`: `2×2`, `0` vs `1`, `z=i`. `genMat`/`envConst`/`loopDrift`/`driftLip` are definitions used inside these examples (plus `0 < envConst 3 3 2 0 2 (1/2+1/1000)`). **PASS.**

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Path.OneStep   # Sat Oct  3 20:51:59 UTC 2026
  Build completed successfully (3325 jobs).
  exit 0
$ lake env lean ax.lean   (#print axioms of every public declaration)
'RBM.Path.genMat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.envConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.OneStepEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.oneStepEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.norm_green_sub_le_of_herm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.DriftLip_eGterm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.loopDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.loopDrift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.driftLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Path.norm_loopDrift_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Path.OneStep; #assert_rbm_axioms
axiom audit: 2531 theorems, 1070 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 5 borrowed + 86 owed + 36 structural; 45 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
exit 0
$ grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Path/OneStep.lean
0
$ git diff --stat main...t/T2072
 RBM3D/Path/OneStep.lean | 2429 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2429 insertions(+)
```
Only the sole writable file `RBM3D/Path/OneStep.lean` (new) is touched; `RBM3D/Test/Axioms.lean` unchanged (pre-check exits 0); no frozen signature touched. **PASS.**

## 5. Paper deltas
Lean/source differences: (i) new parameters `d`, `g` (`S^(B)(g)`, constants `g`-free) — candidate `T2072a`; (ii) `treeEqRhs d L W g` (weight `W^d`) and `mSigma` replace RBM2D `KLoop.primRhs` (`W^2`) and `KLoop.mSig` — candidate `T2072b`; (iii) no `3 ≤ L` hypothesis, the unit-sphere count `≤ 2d` proved for every `L` — candidate `T2072c`. All differences found in §1 are covered by the prove report's candidates (section (d)). **PASS.**

## Observations (no effect on statement, instance, build, axioms or delta coverage)
- Prove report (a) verdict 2 names the `3 ≤ L` delta `T2072b`, while (d) uses `T2072b` for the `treeEqRhs` replacement and `T2072c` for `3 ≤ L`; the dispatcher should take the labels from (d).
- `envConst`, `driftLip` are deliberately loose closed-form constants (preflight ratios ≥ 1e2–1e13); consumers needing sharp `N`-powers must not rely on them being optimal.

## Verdict
| target | verdict |
|---|---|
| `genMat`, `envConst` | PASS |
| `OneStepEnvelope` / `oneStepEnvelope` | PASS |
| `norm_loopDrift_sub_le` (with `loopDrift`, `loopDrift_eq`, `driftLip`, `DriftLip_eGterm`, `norm_green_sub_le_of_herm`) | PASS |

Ticket T2072: **PASS**. No dispatcher sign-off needed.
