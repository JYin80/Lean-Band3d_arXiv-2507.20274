Auditor model: claude-opus-5-5

# T2121 audit (round 1) — ST2-30 `Induction/StepDecompN` — Sun Oct  4 08:08:42 UTC 2026

Branch `t/T2121` at `e15ef7f`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2121-audit1` (detached). Verdict: **PASS** (all targets).

## 1. Diff scope (sole writable files)
```
$ git diff --name-only main...t/T2121
RBM3D/Induction/StepDecompN.lean
$ git diff --stat main...t/T2121 | tail -1
 1 file changed, 1588 insertions(+)
```
Only the new file; `RBM3D/Test/Axioms.lean` untouched (allowed: registry lines only if needed; pre-check §4 passes). No existing (frozen) file modified.

## 2. Statements vs the pin (RBM2D `Induction/StepDecompN.lean` and `GridGoodN.lean:241-290` at `c9a24cf`)
Script `sigdiff.py` (scratchpad): extracts each declaration header up to `:=`, renames RBM2D `d`→`sz`, `(sz : Sizes)`→`{d : ℕ} (sz : Sizes d)`, `Z2 (`→`Zd d (`, `Idx (`→`Idx d (`, whitespace-normalised, token diff.
```
SAME AbCN
SAME stepZCN_re
SAME stepZCN_im
SAME stepZCN
SAME stepXiCN
SAME stepYCN
SAME StepDecompCN_Stmt
SAME loopFamN
NEW dirDerivN
NEW ZfamN
NEW ZvecN
NEW YvecN
NEW stoppedEdgeN
NEW SubGaussFormN
NEW SubGaussStopN
SAME stepDecompCN
SAME stepDecompCN_Z_subG
SAME integrable_stepZCN_re_of_hermTestFun
SAME integrable_stepZCN_im_of_hermTestFun
SAME stepDecompCN_Y_sq
SAME ZvecN_eq_stepZCN
DIFF Ugen_stepZCN: delete [NeZero k]; insert `d`, `(sz.lam n)` in Ugen; ukerMat (L) (KLoop.mSig (E n) (σ i) * KLoop.mSig (E n) (σ (i + 1))) -> uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma (E n) (σ i)) i); rest identical
    (Ugen_stepYCN: same 9 opcodes as Ugen_stepZCN)
DIFF StepDecompN_subGaussStopN_zvecN: [NeZero k] deleted; ukerMat/KLoop.mSig(σ i)*mSig(σ(i+1)) -> uKer d .. (sz.lam n) (cycProd (fun i => mSigma ..) i) in hboundRe/hboundIm; rest identical
RBM2D public not in RBM3D: []
```
Vocabulary (`dirDerivN, ZfamN, ZvecN, YvecN, stoppedEdgeN, SubGaussFormN, SubGaussStopN`) compared by hand with `git show c9a24cf:RBM2D/Induction/GridGoodN.lean` lines 241-290: bodies identical after renaming, except `Idx d`/`Zd d`, `loopDerivN d …`, `Ugen d (sz.L n) (sz.lam n)`, and `[NeZero k]` dropped from `stoppedEdgeN`/`SubGaussStopN` (ticket: "without `[NeZero k]` (D204)"). Nothing else of `GridGoodN` ported (`StoppedAzumaZN` etc. absent: grep). `dirDerivN` authorized by Amend 1.

Residual differences, all forced by merged RBM3D vocabulary:
- `Ugen` is the merged `GridDuhamelN.lean:65` `Ugen (E) (σ) (v w) (A) := UN d L g (fun i => mSigma E (σ i)) v w A`; the merged `martIncN`/`AvecN` use the same `Ugen d (sz.L n) (sz.lam n)` (GridDuhamelN.lean:287, 298, 301). The kernel in `Ugen_stepZCN/YCN` and `StepDecompN_subGaussStopN_zvecN` is `∏ i, uKer d L (sz.lam n) (cycProd …) …`, i.e. the kernel of `UN`; the theorems prove the identity, so a wrong kernel could not compile.
- `[NeZero k]` dropped: the statements are strictly more general.
- `loopFamN` body = the merged pin `HermTestFunLoopN` observable (LoopC2N.lean:456-457: `loopL d L W (blockMat d L W M) (zt E u) (loopOf σ b)`) at `u = gridTime … (j+1)`; `ZvecN` uses merged `loopDerivN` (QVN.lean:62-64), same body.
- Dimension: the only `d`-dependent constant is `C₂ = k(k+1)·Sizes.size·η^{-(k+2)}` supplied by `hermTestFunLoopN`; `stepDecompCN`, `_Z_subG`, `_Y_sq` are `ι`-generic with `C₂` a hypothesis `hC₂`; no `W^2`/`L^2`/`Z2` left:
```
$ grep -nE "Z2|W \^ 2|L \^ 2|NeZero k" RBM3D/Induction/StepDecompN.lean | grep -v "`" | wc -l   # code lines; docstring mentions excluded
       0
```
- §29 hypotheses: identification theorems carry per-`n` `|E n|<2`, `0≤s n`, `s n≤t n`, `t n<1`, `j+1≤K n` exactly as RBM2D; no `∀ᶠ`, so no `_at` form needed.
- `k = 2` reduction to merged `Path/StepDecomp.stepDecomp`: given as an argument in the prove report (a) row 13 / b.8, not compiled; the ticket asks to "say how", not to prove. Observation only.

**Per target (statement):** `stepDecompCN`, `stepDecompCN_Z_subG`, `integrable_stepZCN_re/im_of_hermTestFun`, `stepDecompCN_Y_sq`, `ZvecN_eq_stepZCN`, `martIncN_eq_stepXiCN`, `YvecN_eq_stepYCN` identical to the pin after renaming; `Ugen_stepZCN`, `Ugen_stepYCN`, `StepDecompN_subGaussStopN_zvecN` differ only by the merged-`Ugen` kernel and dropped `[NeZero k]`. Pinned defs `AbCN … StepDecompCN_Stmt, loopFamN` identical; vocabulary as above. All PASS.

## 3. Hidden hypotheses / vacuity / cycles
- `StepDecompCN_Stmt` is a `def … : Prop` with explicit premises (HermTestFun, `hC₂`, `0 ≤ Δ`, two `Integrable`), same as the pin; the integrability premises are discharged by the file's own `integrable_stepZCN_re/im_of_hermTestFun` in the instances. No new structure, no structure-field hypothesis.
- No external hypothesis: `HermTestFun` and `C₂` come from the merged theorem `hermTestFunLoopN` (LoopC2N.lean:469, no hypothesis beyond `|E|<2, 0≤u<1`).
- Imports: `Induction/{LoopC2N,GridDuhamelN,QVN}`, `Path/{LoopStep,StepDecomp}`, all on `main`; no import of `RBM3D` root; no cycle (module builds).

## 4. Compiled nonempty instances (`section Instances`, namespace `StepDecompNCheck`, lines 1373-1564)
Data: merged `sz0` (`sz0_values`: `L 0 = 4, W 0 = 32, size 0 = 2097152, lam 0 = 1/64`, Sizes.lean:267), `d = 3`, `E ≡ 0`, `s ≡ 0`, `t ≡ 1/2`, `K ≡ 4` (`Δ = 1/8`, `u_1 = 1/8`, `u_2 = 1/4`, private theorem `data`), `k = 3`, `σ = (+,-,+)`, `b = (0,0,0)`, kernels `δ3` and the genuine propagator `U3 j m`; `C₂3 j = 12·2097152·η^{-5} > 0` (`C₂3_pos`). Steps `j = 0` and `j = 1` (random `H_1`).
```
$ grep -nE "^example|^  (stepDecompCN|integrable|Ugen|ZvecN|martInc|YvecN)|exact StepDecompN_subGauss" StepDecompN.lean | awk -F: "$1>1440"  (empty "example :=" lines removed)
1445: stepDecompCN sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3
1451: stepDecompCN sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3
1459: integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3
1462: integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3
1465: integrable_stepZCN_re_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3
1468: integrable_stepZCN_im_of_hermTestFun sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3
1471: stepDecompCN_Y_sq sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ δ3 b3
1473: stepDecompCN_Y_sq sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (hC₂3 0 hj0) hΔ (U3 0 1) b3
1508: stepDecompCN_Z_subG sz0 s0 t0 K0 0 0 (hΦ3 0 hj0) (U3 0 1) b3 Set.univ
1513: : SubGaussStopN sz0 (E0 0) σ3 (gridTime s0 t0 K0 0) (fun _ => K0 0)
1520: exact StepDecompN_subGaussStopN_zvecN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3
1524: (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :=
1525: ZvecN_eq_stepZCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 b ω
1527: martIncN_eq_stepXiCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3
1529: YvecN_eq_stepYCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3
1532: (a : Fin 3 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
1533: Ugen_stepZCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 1 a ω
1535: Ugen_stepYCN sz0 E0 s0 t0 K0 0 0 hE0 hs00 hst0 ht10 hj0 σ3 1
1542: stepDecompCN sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ (U3 1 2) b3
1548: stepDecompCN_Y_sq sz0 s0 t0 K0 0 1 (hΦ3 1 hj1) (hC₂3 1 hj1) hΔ (U3 1 2) b3
1550: (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :=
1551: ZvecN_eq_stepZCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 b ω
1553: martIncN_eq_stepXiCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3
1555: YvecN_eq_stepYCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3
1557: (a : Fin 3 → Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
1558: Ugen_stepZCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 2 a ω
1560: Ugen_stepYCN sz0 E0 s0 t0 K0 0 1 hE0 hs00 hst0 ht10 hj1 σ3 2
```
Every endpoint theorem is applied: `stepDecompCN` (δ3, U3 0 1, U3 1 2), `integrable_*` (both kernels), `stepDecompCN_Y_sq` (3), `stepDecompCN_Z_subG` (`E = univ`, proxy `c3` with bounds proved by `le_max_left/right` after `H_0 = 0`), `StepDecompN_subGaussStopN_zvecN` (`τ ≡ 4`, `hτ` proved), identification theorems at `j = 0, 1`. All deterministic hypotheses discharged by `norm_num`/merged theorems; no hypothesis left on any example; no `N = 0`, empty index, collapsed window, or `False` premise. Compiled in the build of §5 (no StepDecompN error).

## 5. Build, axioms, hygiene (audit worktree)
```
$ lake build RBM3D.Induction.StepDecompN
Sun Oct  4 08:06:11 UTC 2026
Build completed successfully (3763 jobs).
exit: 0
$ grep -cE "StepDecompN.lean.*(warning|error)" build.out
0
$ grep "StepDecompN.lean.*depends on axioms" build.out | sed "s/.*RBM.Ind.//" 
loopFamN: [propext, Classical.choice, Quot.sound]
dirDerivN: [propext, Classical.choice, Quot.sound]
ZfamN: [propext, Classical.choice, Quot.sound]
ZvecN: [propext, Classical.choice, Quot.sound]
YvecN: [propext, Classical.choice, Quot.sound]
stoppedEdgeN: [propext, Classical.choice, Quot.sound]
SubGaussFormN: [propext, Classical.choice, Quot.sound]
SubGaussStopN: [propext, Classical.choice, Quot.sound]
stepDecompCN: [propext, Classical.choice, Quot.sound]
stepDecompCN_Z_subG: [propext, Classical.choice, Quot.sound]
integrable_stepZCN_re_of_hermTestFun: [propext, Classical.choice, Quot.sound]
integrable_stepZCN_im_of_hermTestFun: [propext, Classical.choice, Quot.sound]
stepDecompCN_Y_sq: [propext, Classical.choice, Quot.sound]
ZvecN_eq_stepZCN: [propext, Classical.choice, Quot.sound]
Ugen_stepZCN: [propext, Classical.choice, Quot.sound]
martIncN_eq_stepXiCN: [propext, Classical.choice, Quot.sound]
YvecN_eq_stepYCN: [propext, Classical.choice, Quot.sound]
Ugen_stepYCN: [propext, Classical.choice, Quot.sound]
StepDecompN_subGaussStopN_zvecN: [propext, Classical.choice, Quot.sound]
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Induction/StepDecompN.lean | grep -v "#print axioms" | wc -l
       0
$ lake build RBM3D && lake env lean precheck.lean   # import RBM3D; import RBM3D.Induction.StepDecompN; #assert_rbm_axioms
axiom audit: 3681 theorems, 1301 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
exit: 0
```

## 6. Paper deltas
Lean/pin differences: `[NeZero k]` dropped; `Ugen` is merged `Ugen d L g` with `g = sz.lam n`, cyclic `cycProd`/`uKer` kernel; `dirDerivN` added as vocabulary. Proposed as candidate **T2121a** in prove report (d) (covers the first two; `dirDerivN` is a vocabulary definition with no paper statement). The `ξ = Z + Y` split itself is a Lean device (BDG→Azuma, DECISIONS §10), as stated in the module docstring; no further statement difference found. Covered.

## 7. Observations (no effect on verdict)
- Ticket's import list named `GridDriftN`, `HierAlgebra`, `Path/{StepDecompLoop,Walk,Stop}`; the file imports `QVN` (where `loopDerivN` actually lives) and not the unused ones; private helpers copied from merged `Path/StepDecomp`/`GridDuhamelN` are private there, so copying is unavoidable.
- `k = 2` reduction stated as an argument only (report (a) row 13).
- Prove report (a) line 29 instance data superseded by (a′) — correctly recorded.

## Verdict
All targets **PASS**. No dispatcher sign-off needed.
