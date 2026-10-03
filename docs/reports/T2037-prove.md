Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 15:16:30 UTC 2026

Sources read: ticket `docs/tickets/T2037.md`; RBM2D `c9a24cf` files `Gauss/{LoopCoordinateDerivative (234 lines), LoopCoordinateSecondDerivative (176), GreenCoordinateSecondDerivative (90), LoopCoordinateDerivativeBounds (252), LoopCoordinateIntegrability (158)}`; `RBM3D/Gauss/FlowCalculus.lean`, `Gauss/FineModel.lean`, `Loop/GLoop.lean`, `Loop/GLoopFlow.lean`. (The ticket's line counts 163/134/58/252/113 are the portmap's "kept" counts at `0c1330a`; at `c9a24cf` the files are longer, and the targets `hasDerivAt_deriv_green_HflowBlock_update`, `measurable_integrable_actual_...` are only in the longer text.)

### (i) Exponent table

Notation: `B = √u · coordinateBlock c` (`‖B‖` is the only place the coordinate enters; no dimension), `G = Gres H z σ`, `η ≤ |Im z|`, `A = η⁻¹ W^{-d}`, `D = η⁻¹‖B‖η⁻¹ W^{-d}`, `S = 2 η⁻³‖B‖² W^{-d}`.

| item | RBM2D (`c9a24cf`) | RBM3D value | constraint | slack / check |
|---|---|---|---|---|
| `Eblk` factor per edge (`coordA`, `coordD`, `coordS` all carry it) | `(W⁻¹)^2` (Bounds:24,28,33,94,96,100,110,126: 8 tokens) | `((W:ℝ)^d)⁻¹` = `norm_Eblk_le_inv_W_sq d L W` bound (FlowCalculus:663) | one factor `W^{-d}` per `G·E` block; `‖Eblk‖ ≤ W^{-d}` (volume factor: R3) | diagonal entries are `W^{-d}` or `0`, so the bound is sharp; W=2: `1/8` (d=2 was `1/4`) |
| trace factor in `norm_gloop_coordinate_derivatives_le` | `(((L*W)^2 : ℕ):ℝ)` (Bounds:222,225; Integrability:103,108: 4 tokens) | `(((L*W)^d : ℕ):ℝ)` = `Fintype.card (Vtx d L W)` (`card_BlockIndex d L W`, FlowCalculus:701) | `\|tr M\| ≤ card·‖M‖` (`norm_matrix_trace_le_card_mul`) | exact card, no slack lost; L=3,W=2: `216` (d=2: `36`) |
| first-derivative envelope of a word of length n | `n·D·A^{n-1}` (recursion `coordinateFirstWordBound`, no `d`) | same recursion with the new `A, D` | `‖(G'E)·tail‖+‖GE·D1(tail)‖` | recursion = closed form `n D A^{n-1}` (script asserts) |
| second-derivative envelope | `n S A^{n-1} + n(n-1) D² A^{n-2}` | same recursion with the new `A, D, S` | Leibniz: `S A^{n-1} + 2D·First(n-1) + A·Second(n-1)` | closed form asserted by script (n=2,3) |
| powers of `η⁻¹` | `η⁻¹`, `η⁻²`, `η⁻³` in `A, D, S` | unchanged | `‖Gres‖ ≤ η⁻¹` (`norm_Gsig_le_inv_eta`, FlowCalculus:644) needs `0<η≤\|Im z\|` | `A^n` is the product of `n` resolvent bounds; the instance has `η = \|Im z\| = 1/2` (equality, allowed) |
| `‖B‖ = √u‖coordinateBlock c‖` | dimension-free | unchanged; for a used coordinate `‖Xmat(e_c)‖ = 1` (off-diag and diag) | not bounded by a `d`-dependent constant | script: `\|B\| = 0.707 = √(1/2)` |
| probability measure of the integrability target | `P L W` (no parameter) | `PF d L W g` — an **extra real parameter `g`** (coupling of `svarF`) | integrability from a bounded continuous function needs only a probability measure; `isProbabilityMeasure_PF d L W g` has no hypothesis on `g` | statement gains `(g : ℝ)`: paper-delta candidate `T2037a`; no hypothesis on `g` needed |
| index types | `Z2 L` (Derivative 6, Second 5, Bounds 3, Integrability 7 tokens), `BlockIndex L W`, `Coord L W`, `Gsig`, `green`, `gloop`, `gloopProd` | `Zd d L`, `Vtx d L W`, `CoordF d L W`, `Gres H z σ`, `Gres H z true` (for `green`), `loopL`, `gloopProd d L W` | `d` a plain `ℕ`; the RBM2D sources have no `d`-dependent hypothesis and the merged `FlowCalculus` statements take `d` with no `3 ≤ d` | token counts below agree with portmap P.1 rows 5-8, row 2 has none |
| `d = 2` literals elsewhere | none; `Green…SecondDerivative` has `green`: 8 tokens, no `Z2`/`W^2` | `Gres … true` (the merged `FlowCalculus` already states `hasDerivAt_green_moving` for `Gres … true`) | `Gres H z true = Ring.inverse (H - z•1)` equals `green H z` for the invertible matrices used | derivative formula `-GBG` and `2GBGBG` unchanged |
| spectral/hierarchy scales (`scaleM, ellT, tailT, ellStar, Meta, ellz`) | not used in these five files | n/a | — | nothing to replace |

Token counts at `c9a24cf` (`git show` + regex, verbatim output):
```
LoopCoordinateDerivative W^2 [(L*W)^2]: 0  W⁻¹^2: 0  Z2: 6  green: 3  P L W: 0  lines: 234
LoopCoordinateSecondDerivative W^2 [(L*W)^2]: 0  W⁻¹^2: 0  Z2: 5  green: 0  P L W: 0  lines: 176
GreenCoordinateSecondDerivative W^2 [(L*W)^2]: 0  W⁻¹^2: 0  Z2: 0  green: 8  P L W: 0  lines: 90
LoopCoordinateDerivativeBounds W^2 [(L*W)^2]: 2  W⁻¹^2: 8  Z2: 3  green: 0  P L W: 0  lines: 252
LoopCoordinateIntegrability W^2 [(L*W)^2]: 2  W⁻¹^2: 0  Z2: 7  green: 0  P L W: 4  lines: 158
```
Key statements (mathematics): `hasDerivAt_gloop_update`: `t ↦ loop(H_u(ω[c:=t]))` has derivative `tr(Σ_k G_1E_1…(-G_kBG_k)E_k…G_nE_n)` at `ω c` (affine dependence `H(ω[c:=t]) = H(ω) + √u (t-ω c)·coordinateBlock c`, `d/dt G = -GBG`); `hasDerivAt_deriv_gloop_update`: second derivative = `tr` of the Leibniz sum with `G'' = 2GBGBG` (diagonal terms `S`) and the mixed terms `2·G'E·D1(tail)`; `hasDerivAt_deriv_green_HflowBlock_update`: `d²/dt² G = 2GBGBG`; `norm_gloop_coordinate_derivatives_le`: `‖D1‖ ≤ (LW)^d·nDA^{n-1}`, `‖D2‖ ≤ (LW)^d(nSA^{n-1}+n(n-1)D²A^{n-2})`; `measurable_integrable_actual_…`: `D1, D2` (traces of the recursive words, by `deriv = recursive formula`) are continuous in `ω`, hence measurable, and bounded by the constants above, hence integrable under `PF d L W g`. The dimension enters only through `W^{-d}` (per edge), `(LW)^d` (trace) and the index types.

### (ii) One concrete nondegenerate instance

`d = 3, W = 2, L = 3` (`N = (WL)^d = 216`, `(LW)^d = 216`, `W^d = 8`), `u = 1/2`, `z = 0.3 + 0.5 i` (`Im z ≠ 0`), `η = 1/2 = |Im z|`, `η > 0`; loop `I = ([true,false], [![0,0,0], ![1,2,0]])` (WF: 2 = 2; the block labels are two distinct blocks of `Z_3^3`) and also the 3-loop `([true,false,true], [![0,0,0], ![1,2,0], ![2,1,1]])`; coordinates `c` = `(i,j,false)`, `(i,j,true)` with `key i < key j` (`i` in block `(0,0,0)`, `j` in block `(1,2,0)`) and the diagonal `(i,i,true)`; sample `ω` all coordinates i.i.d. `N(0, 0.07²)` (the derivative formulas and bounds are deterministic and hold for every `ω`); law `PF 3 3 2 g` with any `g` (e.g. `g = 1`; probability measure for every `g`). Every hypothesis of the five targets (`z.im ≠ 0`; `0 < η ≤ |z.im|`; `I.WF`; `NeZero L, NeZero W`) holds at this data. No target has an external or pin hypothesis, so the concrete limit computation of TEAM §8 lesson 14 does not apply (script check of the exponents: `A = 0.25, D = 0.3536, S = 1.0`, bounds `216·2DA = 38.18`, `216(2SA+2D²) = 162`, matching the printed bounds).

The script (`…/scratchpad/T2037/check.py`, python3 + numpy 2.0.2, no Lean) builds `Xentry/Xmat` exactly as `FineModel.lean:105-114` on `Z_6^3` (any total order for `idxKey`), `coordinateMatrix c = Xmat(Pi.single c 1)`, checks `Xmat_update` (affine dependence), `Eblk a = diag(W^{-d} 1[blk x = a])` (conjugate to the `Vtx` version by `splitEquiv`, same trace), `Gres H z σ = (H - (z or z̄))⁻¹`, evaluates the recursions `coordinateWordDeriv`/`coordinateSecondWordDeriv` from the RBM2D definitions and compares with central finite differences (`h = 1e-4` first, `h = 1e-3` second) of the actual loop along `t ↦ ω[c:=t]`, asserts the closed forms of the two envelopes, and checks `|D_k| ≤ (LW)^d · bound`.

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2037/check.py
offdiag-false n=2 |B|=0.707 formula D1=3.866846e-04+4.048817e-19j fd=3.866846e-04+7.276013e-15j | D2=5.352115e-03+3.970467e-18j fd=5.352111e-03+3.320369e-12j | |D1|=3.867e-04<=3.818e+01 |D2|=5.352e-03<=1.620e+02 ok=True
offdiag-true  n=2 |B|=0.707 formula D1=-1.157489e-03-1.112154e-18j fd=-1.157489e-03-3.218725e-15j | D2=4.928769e-03+3.580408e-18j fd=4.928766e-03+7.691059e-13j | |D1|=1.157e-03<=3.818e+01 |D2|=4.929e-03<=1.620e+02 ok=True
diag-true     n=2 |B|=0.707 formula D1=9.891361e-05-3.371191e-19j fd=9.891361e-05+3.311899e-15j | D2=-4.444234e-04-2.632155e-19j fd=-4.444232e-04+4.094557e-12j | |D1|=9.891e-05<=3.818e+01 |D2|=4.444e-04<=1.620e+02 ok=True
offdiag-false n=3 |B|=0.707 formula D1=-1.520588e-06+1.263181e-05j fd=-1.520588e-06+1.263181e-05j | D2=1.828643e-06-1.758585e-05j fd=1.828640e-06-1.758583e-05j | |D1|=1.272e-05<=1.432e+01 |D2|=1.768e-05<=8.100e+01 ok=True
Green d2: max|fd - 2GBGBG| = 1.4563943724571287e-07
ALL OK
```
(for `n=3` the bounds are `216·3DA² = 14.32` and `216(3SA²+6D²A) = 81.0`.)

Observed slack: formula and finite difference agree to 7 digits (first) and 6 digits (second); the bound is crude by a factor `≥ 10^4` on this sample (the `(LW)^d` trace factor and `η⁻¹` are worst-case); the second derivative is not zero and not equal to the first (so the second-derivative formula is tested non-vacuously).

Dimension comparison (W=2, L=3, η=1/2, n=2; script output): `d=2: W^-d=0.25 A=0.5 D=0.7071 S=2.0 (LW)^d=36 first=25.4558 second=108.0`; `d=3: W^-d=0.125 A=0.25 D=0.3536 S=1.0 (LW)^d=216 first=38.1838 second=162.0`.

### Verdicts

- `hasDerivAt_gloop_update` (LoopCoordinateDerivative:150): PASS.
- `hasDerivAt_deriv_gloop_update` (LoopCoordinateSecondDerivative:138): PASS.
- `hasDerivAt_deriv_green_HflowBlock_update` (GreenCoordinateSecondDerivative:59): PASS.
- `norm_gloop_coordinate_derivatives_le` (LoopCoordinateDerivativeBounds:218): PASS (`W^{-d}` per edge, trace factor `(LW)^d`).
- `measurable_integrable_actual_gloop_coordinate_derivatives` (LoopCoordinateIntegrability:131): PASS; the statement needs the extra parameter `g` of `PF d L W g` (paper-delta candidate `T2037a`).

Overall verdict: PASS.

## (b) Script output — stage 1b, Sat Oct  3 15:23:48 UTC 2026

### Build, branch, scope
```
$ git log -1 --format="%h %s" t/T2037; git diff --name-only main...t/T2037; wc -l RBM3D/Gauss/LoopCoordinate.lean
639a4f5 T2037: port Gauss/LoopCoordinate (coordinate derivatives of the G-loops, bounds, integrability)
RBM3D/Gauss/LoopCoordinate.lean
     936 RBM3D/Gauss/LoopCoordinate.lean
$ lake build RBM3D.Gauss.LoopCoordinate 2>&1 | grep -v '^trace' | tail -3
Build completed successfully (3297 jobs).
$ lake build 2>&1 | grep -v '^trace' | tail -1   (full library)
Build completed successfully (3776 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Gauss/LoopCoordinate.lean
0
```

### Axioms of the five targets (`#print axioms`, scratch file)
```
'RBM.Gauss.hasDerivAt_gloop_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.hasDerivAt_deriv_gloop_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.hasDerivAt_deriv_green_HflowBlock_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_gloop_coordinate_derivatives_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.measurable_integrable_actual_gloop_coordinate_derivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Registry pre-check (ST1-COMMON item 8): scratch file `import RBM3D`, `import RBM3D.Gauss.LoopCoordinate`, `#assert_rbm_axioms`
```
$ lake env lean <scratch>/precheck.lean ; echo exit=$?
axiom audit: 1948 theorems, 835 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
premises found by scanning: 48 (borrowed 2, owed 33, structural 13).
registry: 5 borrowed + 43 owed + 25 structural; 25 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
exit=0
```
No registry line was added: the five targets take no new `Prop`-valued premise (hypotheses: `z.im ≠ 0`, `η ≤ |z.im|`, `I.WF`, `0 < η`); `RBM3D/Test/Axioms.lean` is unchanged.

### Target statements (extracted from the file by script `extract.py`; proofs elided)
```lean
theorem hasDerivAt_gloop_update (u : ℝ) (ω : Ω d L W) (c : CoordF d L W)
    {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => loopL d L W (HflowBlock d L W u (Function.update ω c t)) z I)
      (Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))) (ω c) := …

theorem hasDerivAt_deriv_gloop_update (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ =>
        loopL d L W (HflowBlock d L W u (Function.update ω c s)) z I) t)
      (Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a)))
      (ω c) := …

theorem hasDerivAt_deriv_green_HflowBlock_update (u : ℝ) (ω : Ω d L W)
    (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ =>
        Gres (HflowBlock d L W u (Function.update ω c s)) z true) t)
      (let G := Gres (HflowBlock d L W u ω) z true;
       let B := Real.sqrt u • coordinateBlock d L W c;
       (2 : ℝ) • (G * B * G * B * G)) (ω c) := …

theorem norm_gloop_coordinate_derivatives_le {η u : ℝ} (hη : 0 < η)
    (c : CoordF d L W) {z : ℂ} (hz : η ≤ |z.im|)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) (ω : Ω d L W) :
    ‖Matrix.trace (coordinateWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) *
          coordinateFirstWordBound d L W u η c I.a.length ∧
    ‖Matrix.trace (coordinateSecondWordDeriv d L W u ω c z (I.σ.zip I.a))‖ ≤
        (((L * W) ^ d : ℕ) : ℝ) *
          coordinateSecondWordBound d L W u η c I.a.length := …

theorem measurable_integrable_actual_gloop_coordinate_derivatives
    (g u : ℝ) (c : CoordF d L W) {z : ℂ} (hz : z.im ≠ 0)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    let D₁ : Ω d L W → ℂ := fun ω => deriv (fun t : ℝ =>
      loopL d L W (HflowBlock d L W u (Function.update ω c t)) z I) (ω c)
    let D₂ : Ω d L W → ℂ := fun ω => deriv (fun t : ℝ => deriv (fun s : ℝ =>
      loopL d L W (HflowBlock d L W u (Function.update ω c s)) z I) t) (ω c)
    Measurable D₁ ∧ Integrable D₁ (PF d L W g) ∧
      Measurable D₂ ∧ Integrable D₂ (PF d L W g) := …
```

### Statement diff against RBM2D `c9a24cf` (script `stmtdiff.py`: RBM2D headers renamed by R1-R4 and the merged vocabulary, compared with the RBM3D headers)
```
DIFF: integrable_gloop_coordinate_derivatives
DIFF: measurable_integrable_actual_gloop_coordinate_derivatives
identical 39 different 2 RBM2D decls 41 RBM3D decls 45
only in RBM3D: ['loopCoordinateLoop', 'loopCoordinateLoop_wf', 'loopCoordinateOff', 'loopCoordinateDiag']
```
Residual differences: exactly two statements (`integrable_gloop_coordinate_derivatives`, `measurable_integrable_actual_gloop_coordinate_derivatives`) gain the explicit argument `(g : ℝ)` (law `PF d L W g`, RBM2D `P L W` has none); see (d) `T2037a`.

### Name-clash grep (script `clash.py`, `git grep` of `main` under `RBM3D/`, 32 public new names)
```
total clash hits on main: 0
```

### Compiled nonempty instances (section 5 of the file, doc comments removed; `d = 3, L = 3, W = 2`, `N = 216`)
```lean
/-! ## 5. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = (W L)^d = 216`) -/
section Instances
private def loopCoordinateLoop : Loop.LoopIdx (Zd 3 3) :=
  ⟨[true, false], [![0, 0, 0], ![1, 2, 0]]⟩
private theorem loopCoordinateLoop_wf : loopCoordinateLoop.WF := rfl
private def loopCoordinateOff : CoordF 3 3 2 := (![0, 0, 0], ![1, 0, 0], true)
private def loopCoordinateDiag : CoordF 3 3 2 := (![0, 0, 0], ![0, 0, 0], true)
example : coordinateBlock 3 3 2 loopCoordinateDiag
    (splitEquiv 3 3 2 ![0, 0, 0]) (splitEquiv 3 3 2 ![0, 0, 0]) = 1 := by
  simp [coordinateBlock, blockMat, coordinateMatrix, Xmat, Xentry, loopCoordinateDiag]
example (ω : Ω 3 3 2) :
    (HasDerivAt
      (fun t : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2)
        (Function.update ω loopCoordinateOff t)) Complex.I loopCoordinateLoop)
      (Matrix.trace (coordinateWordDeriv 3 3 2 (1 / 2) ω loopCoordinateOff Complex.I
        (loopCoordinateLoop.σ.zip loopCoordinateLoop.a))) (ω loopCoordinateOff) ∧
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2)
        (Function.update ω loopCoordinateOff s)) Complex.I loopCoordinateLoop) t)
      (Matrix.trace (coordinateSecondWordDeriv 3 3 2 (1 / 2) ω loopCoordinateOff Complex.I
        (loopCoordinateLoop.σ.zip loopCoordinateLoop.a))) (ω loopCoordinateOff)) ∧
    (HasDerivAt
      (fun t : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2)
        (Function.update ω loopCoordinateDiag t)) Complex.I loopCoordinateLoop)
      (Matrix.trace (coordinateWordDeriv 3 3 2 (1 / 2) ω loopCoordinateDiag Complex.I
        (loopCoordinateLoop.σ.zip loopCoordinateLoop.a))) (ω loopCoordinateDiag) ∧
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2)
        (Function.update ω loopCoordinateDiag s)) Complex.I loopCoordinateLoop) t)
      (Matrix.trace (coordinateSecondWordDeriv 3 3 2 (1 / 2) ω loopCoordinateDiag Complex.I
        (loopCoordinateLoop.σ.zip loopCoordinateLoop.a))) (ω loopCoordinateDiag)) :=
  ⟨⟨hasDerivAt_gloop_update 3 3 2 (1 / 2) ω loopCoordinateOff (by norm_num) _
      loopCoordinateLoop_wf,
    hasDerivAt_deriv_gloop_update 3 3 2 (1 / 2) ω loopCoordinateOff (by norm_num) _
      loopCoordinateLoop_wf⟩,
   ⟨hasDerivAt_gloop_update 3 3 2 (1 / 2) ω loopCoordinateDiag (by norm_num) _
      loopCoordinateLoop_wf,
    hasDerivAt_deriv_gloop_update 3 3 2 (1 / 2) ω loopCoordinateDiag (by norm_num) _
      loopCoordinateLoop_wf⟩⟩
example (ω : Ω 3 3 2) :
    HasDerivAt
      (fun t : ℝ => Gres (HflowBlock 3 3 2 (1 / 2) (Function.update ω loopCoordinateOff t))
        Complex.I true)
      (-(Gres (HflowBlock 3 3 2 (1 / 2) ω) Complex.I true *
        (Real.sqrt (1 / 2) • coordinateBlock 3 3 2 loopCoordinateOff) *
        Gres (HflowBlock 3 3 2 (1 / 2) ω) Complex.I true)) (ω loopCoordinateOff) ∧
    HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ =>
        Gres (HflowBlock 3 3 2 (1 / 2) (Function.update ω loopCoordinateOff s))
          Complex.I true) t)
      ((2 : ℝ) • (Gres (HflowBlock 3 3 2 (1 / 2) ω) Complex.I true *
        (Real.sqrt (1 / 2) • coordinateBlock 3 3 2 loopCoordinateOff) *
        Gres (HflowBlock 3 3 2 (1 / 2) ω) Complex.I true *
        (Real.sqrt (1 / 2) • coordinateBlock 3 3 2 loopCoordinateOff) *
        Gres (HflowBlock 3 3 2 (1 / 2) ω) Complex.I true)) (ω loopCoordinateOff) :=
  ⟨hasDerivAt_green_HflowBlock_update 3 3 2 (1 / 2) ω loopCoordinateOff (by norm_num),
    hasDerivAt_deriv_green_HflowBlock_update 3 3 2 (1 / 2) ω loopCoordinateOff
      (by norm_num)⟩
example (ω : Ω 3 3 2) :
    ‖Matrix.trace (coordinateWordDeriv 3 3 2 (1 / 2) ω loopCoordinateOff Complex.I
        (loopCoordinateLoop.σ.zip loopCoordinateLoop.a))‖ ≤
      (((3 * 2) ^ 3 : ℕ) : ℝ) *
        coordinateFirstWordBound 3 3 2 (1 / 2) 1 loopCoordinateOff
          loopCoordinateLoop.a.length ∧
    ‖Matrix.trace (coordinateSecondWordDeriv 3 3 2 (1 / 2) ω loopCoordinateOff Complex.I
        (loopCoordinateLoop.σ.zip loopCoordinateLoop.a))‖ ≤
      (((3 * 2) ^ 3 : ℕ) : ℝ) *
        coordinateSecondWordBound 3 3 2 (1 / 2) 1 loopCoordinateOff
          loopCoordinateLoop.a.length :=
  norm_gloop_coordinate_derivatives_le 3 3 2 one_pos loopCoordinateOff (by simp)
    loopCoordinateLoop loopCoordinateLoop_wf ω
example :
    (let D₁ : Ω 3 3 2 → ℂ := fun ω => deriv (fun t : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) (Function.update ω loopCoordinateOff t))
        Complex.I loopCoordinateLoop) (ω loopCoordinateOff)
    let D₂ : Ω 3 3 2 → ℂ := fun ω => deriv (fun t : ℝ => deriv (fun s : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) (Function.update ω loopCoordinateOff s))
        Complex.I loopCoordinateLoop) t) (ω loopCoordinateOff)
    Measurable D₁ ∧ Integrable D₁ (PF 3 3 2 1) ∧ Measurable D₂ ∧ Integrable D₂ (PF 3 3 2 1)) ∧
    (let D₁ : Ω 3 3 2 → ℂ := fun ω => deriv (fun t : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) (Function.update ω loopCoordinateDiag t))
        Complex.I loopCoordinateLoop) (ω loopCoordinateDiag)
    let D₂ : Ω 3 3 2 → ℂ := fun ω => deriv (fun t : ℝ => deriv (fun s : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) (Function.update ω loopCoordinateDiag s))
        Complex.I loopCoordinateLoop) t) (ω loopCoordinateDiag)
    Measurable D₁ ∧ Integrable D₁ (PF 3 3 2 1) ∧ Measurable D₂ ∧ Integrable D₂ (PF 3 3 2 1)) :=
  ⟨measurable_integrable_actual_gloop_coordinate_derivatives 3 3 2 1 (1 / 2)
      loopCoordinateOff (by norm_num) _ loopCoordinateLoop_wf,
    measurable_integrable_actual_gloop_coordinate_derivatives 3 3 2 1 (1 / 2)
      loopCoordinateDiag (by norm_num) _ loopCoordinateLoop_wf⟩
end Instances
end RBM.Gauss
```

### RBM2D port source
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the five files>   (HEAD = 9e0f275)
(empty output: the five files are unchanged between c9a24cf and HEAD, rc=0)
```

### Narrative
- Ported all 32 public declarations of the five RBM2D files at `c9a24cf` into `RBM3D/Gauss/LoopCoordinate.lean`; none dropped (RBM2D's 9 private helpers stay `private`; four private instance helpers added in section 5). Every docstring cites the RBM2D `file:line` (lines checked by script against `git show c9a24cf:`). The compiled proofs are RBM2D's after renaming.
- Renaming (ST1-COMMON R1-R4 and the merged vocabulary): `Z2 L` -> `Zd d L`; `BlockIndex L W` -> `Vtx d L W`; `Coord`/`Ω`/`P` -> `CoordF`/`Ω d L W`/`PF d L W g`; `green H z` -> `Gres H z true`; `Gsig` -> `Gres`; `gloop` -> `loopL`; `LoopIdx (Z2 L)` -> `Loop.LoopIdx (Zd d L)`; the coordinate matrix `(coordinateMatrix c).submatrix …` is the merged `blockMat d L W (coordinateMatrix d L W c)`.
- `d = 2` tokens of the portmap (P.1 rows 5-8, GreenCoordinateSecondDerivative): the 8 tokens `(W⁻¹)^2` of `LoopCoordinateDerivativeBounds` became `((W : ℝ) ^ d)⁻¹` (`norm_Eblk_le_inv_W_sq`, volume factor `W^{-d}`, rule R3); the 2 + 2 tokens `((L * W) ^ 2 : ℕ)` (Bounds, Integrability) became `((L * W) ^ d : ℕ)` = `Fintype.card (Vtx d L W)` (`card_BlockIndex`); the `Z2` tokens (6+5+3+7) became `Zd d L`; the 8 `green` tokens of GreenCoordinateSecondDerivative became `Gres … true`. Nothing else in the five files depends on the dimension (`‖B‖`, `η⁻¹`, the recursions `coordinateFirstWordBound`/`coordinateSecondWordBound` carry no dimension except through `W^{-d}`).
- The `d`-dependence of the bound is exactly the preflight table (a)(i): `W^{-d}` per `G E` block, `(L W)^d` for the trace; no `3 ≤ d` hypothesis is needed anywhere.
- `RBM2D`'s `LoopCoordinateDerivative` ends with an `example` for `L = W = 1`; it is not ported (not a declaration); section 5 gives `d = 3` instances instead, with the diagonal direction checked nonzero (entry `1` at the vertex of `(0,0,0)`).
- Instances (section 5): 2-loop `([+,-], [(0,0,0), (1,2,0)])` in `Z_3^3` (WF by `rfl`), `u = 1/2`, `z = i`, `η = |Im z| = 1`, every sample `ω`, off-diagonal and diagonal coordinate; the integrability instance is under `PF 3 3 2 1`. No target has a pin or external hypothesis; all hypotheses are discharged (`norm_num`/`simp`).
- No `(a′)` corrections were needed; the preflight (a) statement set and exponent table matched what compiled.

## (c) Verified Mathlib names (all used by the compiled file; no name was invented)
`HasDerivAt.mul`, `HasDerivAt.mul_const`, `HasDerivAt.neg`, `HasDerivAt.smul_const`, `HasDerivAt.const_mul`, `HasDerivAt.const_add`, `HasDerivAt.sub_const`, `HasDerivAt.congr_of_eventuallyEq`, `HasDerivAt.deriv`, `hasDerivAt_const`, `hasDerivAt_id`, `Function.update_idem`, `Function.update_eq_self`, `Matrix.traceLinearMap`, `LinearMap.toContinuousLinearMap`, `ContinuousLinearMap.hasFDerivAt`/`HasFDerivAt.comp_hasDerivAt`, `MeasureTheory.Integrable.of_bound`, `Continuous.measurable`, `Matrix.submatrix_apply`, tactic `noncomm_ring`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- `T2037a`: `integrable_gloop_coordinate_derivatives` and `measurable_integrable_actual_gloop_coordinate_derivatives` take an explicit `(g : ℝ)` and are stated under `PF d L W g` (RBM2D: the parameterless `P L W`). The proof uses only that `PF d L W g` is a probability measure (`isProbabilityMeasure_PF`, no hypothesis on `g`), so any `g` is allowed; the merged one-size law `PF d L W g` of `FineModel.lean` carries `g` (via `svarF`).
- No other deviation. No hypothesis was added, weakened or removed; no frozen or pinned signature changed.
- Verdict: all five targets and all 32 public declarations are built, committed on `t/T2037` (commit `639a4f5`), with compiled nonempty instances.
