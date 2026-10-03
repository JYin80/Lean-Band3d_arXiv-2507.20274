Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 19:46:14 UTC 2026

Targets (RBM2D at `c9a24cf`, files `Gauss/{LoopFlowCoordinateChain,LoopFlowDerivativeEnvelope,LoopFlowSteinExpectation,LoopExpectationDerivative}.lean`, 819 lines read by `git show`): with `F_v(ω) = loopL(H_v(ω), z_v, I)`, `H_v = √v X`, `z_v = E + (1-v) m(E)`,
(T1) `F_u' = (1/(2u)) Σ_c ω_c ∂_c F + tr(spectral drift)` (coordinate chain, `loop_flow_derivative_actual_coordinate_chain`);
(T2) `|F_v'(ω)| ≤ Env(ω)` for `v ∈ [u/2,(1+u)/2]` (`norm_samplewise_loop_flow_derivative_le_envelope`);
(T3) `E[F_u'] = (1/(2u)) E[Σ_c gvar_c ∂_c² F] + E[tr spectral]` (`expected_samplewise_loop_flow_derivative`);
(T4) `d/du E[F_u] = ` the same right side (`deriv_integral_gloop_HflowBlock_spectralZ`, differentiation under `∫` by T2).
Hypotheses of all four: `|E|<2`, `0<u<1`, `I.WF`, `NeZero L`, `NeZero W` (no `3 ≤ d`, no `3 ≤ L` needed; no external hypothesis, so no limit computation).

### (i) Exponent table (merged names from `RBM3D/Gauss/{FlowCalculus,FineModel,LoopCoordinate}.lean`)

| # | RBM2D token (file:line at c9a24cf) | d ≥ 3 replacement | constraint it must satisfy | value at d=3,L=3,W=2 | slack |
|---|---|---|---|---|---|
| 1 | `(W:ℝ)⁻¹ ^ 2`: Envelope 57,60,62; SteinExp 25 (`driftA`), 28 (`driftD`), 99, 114, 118; LoopExpDer 59 | `((W:ℝ)^d)⁻¹` (merged `norm_Eblk_le_inv_W_sq`, FlowCalculus:663; `coordA`, LoopCoordinate:425) | `‖Eblk d L W a‖ ≤ W^{-d}`; must be the literal merged form so `coordinateFirstWordBound`, `norm_foldr_Gsig_Eblk_le` unify | `1/8` | 0 (`Eblk = W^{-d}·1_block`; `(W⁻¹)^2 = 1/4` is a valid but non-matching bound) |
| 2 | `(((L*W)^2 : ℕ):ℝ)`: Envelope 73,75,92,94,132,143,152,160,181,183,194,196; SteinExp 234,239,263,323; LoopExpDer 58 | `(((L*W)^d : ℕ):ℝ)` (= `Fintype.card (Vtx d L W)`, `card_BlockIndex` FlowCalculus:701) | trace bound `|tr M| ≤ card(Vtx)·‖M‖` | `216 = N` | 0 (`tr 1 = 216`); `(LW)^2 = 36` would be too small, so this one is forced |
| 3 | `Z2 L` (Chain 40,64×2,81,111,142,153,168,181,195; Env 69,79,107; SteinExp 71,86,123,169,209,250,297; LoopExpDer 27,89) | `Zd d L`, `Loop.LoopIdx (Zd d L)`; `BlockIndex L W → Vtx d L W`, `Coord L W → CoordF d L W`, `Ω L W → Ω d L W` | index types only; `Fin (W^d)` fibre | `|Vtx| = 27·8 = 216` | none (dimension-free) |
| 4 | variance `gvar L W c` (SteinExp 200,212,243,244,253,270,273,280,286,289,303; Env 88; LoopExpDer 93) | `gvarF d L W g c` (diag `S_ii = W^{-d}(1+2dg²)⁻¹`, off-diag `S_ij/2`; `svarF_diag` FineModel:61) | Stein needs only `v ≥ 0`; `svarF ≥ 0` for every real `g` | `S_ii = 1/56 = 0.017857` (g=1) | the ticket's "variance `W^{-d}`" holds only as `S_ii ≤ W^{-d}` (equality iff `g=0`); the statements carry `gvarF` abstractly, no exponent appears |
| 5 | law `P L W` | `PF d L W g` (extra real argument `g`, as T2037 `integrable_gloop_coordinate_derivatives (g u)`) | `PF` (FineModel:97) and `GaussianProduct.law` (DominationAt:500) are the same `Measure.infinitePi` term, as RBM2D `hlaw : P L W = law (gvar L W) := rfl` (SteinExp 244) | `g = 1` | none; the extra `g` is a residual statement difference (candidate `T2064a`) |
| 6 | `‖spectralM E‖` in `driftD` (SteinExp 28) | `‖mE E‖` | `|mE E| = 1` for `|E|<2` (`4-E²+E²=4`) | `1.0` | 0 (script `abs(m)`) |
| 7 | `η = (1-(1+u)/2)·Im mE E` (Env 70) | unchanged | `η>0`, `η ≤ |Im zt E v|` on `[u/2,(1+u)/2]` (`spectralZ_im_gap`, FlowCalculus:60, `t=(1+u)/2<1`) | `η = 0.24717`; `Im zt = 0.7415` at `v=u/2`, `0.4943` at `v=u`, `0.2472` at `v=(1+u)/2` | 0 at right end, factor 3 at `v=u/2` |
| 8 | window `[u/2,(1+u)/2] ⊂ (0,1)` | unchanged | `0<u<1` | `[0.25, 0.75]` | `0.25` from `0`, `0.25` from `1` |
| 9 | `|1/(2v)| ≤ 1/u` (Env hcoef) | unchanged | `v ≥ u/2` | `2 ≤ 2` at `v=0.25` | 0 at `v = u/2` |
| 10 | `‖√v B_c‖ ≤ ‖√1 B_c‖` (`coordinateFirstWordBound_le_one`) | unchanged | `v ≤ 1`; `‖B_c‖_op = 1` for all three coordinate types | `[1,1,1]` | 0 |
| 11 | integrable majorant `Σ_c E|ω_c| < ∞` (`integrable_flowDerivativeEnvelope`) | `CoordF d L W` finite, `PF`-marginals `gaussianReal 0 (gvarF c)` | finite coordinate set, `integrable_id_gaussianReal` | `46656 = N²` coordinates | n/a |
| 12 | tokens `d = 2`, `1/5`, `scale`, `ell`, `zdist2`, `N2`, `inv2` | none occur in the four files (grep of the `c9a24cf` texts: only the hits in rows 1-3; `hscaled` matches `scale` and is a local name) | portmap row S1-05 columns `d=2`,`1/5`,`scal` are `-` | n/a | n/a |

Name map for the port (all verified in the files above): `Gsig→Gres`, `gloop→loopL`, `spectralZ→zt`, `spectralM→mE`, `Xmat → blockMat d L W (Xmat d L W ω)` (= the `submatrix` form), `gsigFlowDeriv`, `loopWordDeriv`, `hasDerivAt_gloop_HflowBlock_spectralZ`, `coordinateWordDeriv`, `coordinateSecondWordDeriv`, `coordinateFirstWordBound`, `norm_gloop_coordinate_derivatives_le`, `GaussianProduct.stein` (DominationAt:559) all exist merged. `RBM2D LoopCoordinateSteinSum` is imported by `LoopFlowSteinExpectation` but none of its two declarations (`integrable_coord_smul_gloop`, `stein_gloop_HflowBlock_sum`) is used in the four files (grep count 0). The new names `spectralWordBound`, `flowWindow`, `flowDerivativeEnvelope`, `gsigDirectionMap`, `wordDirectionMap`, `gsigSpectralFlowDeriv`, `spectralWordDeriv`, `integrable_coord_smul_of_bounded` have no hit in `RBM3D/` (`grep -rln`). `spectralWordBound`, `driftA`, `driftD` need `d` as an explicit argument.

### (ii) One nondegenerate instance and numeric check (d=3, L=3, W=2, N=(WL)^d=216, g=1, E=0.3, u=0.5, loop σ=(+,−), a=((0,0,0),(1,2,0)))

All hypotheses hold: `|E|=0.3<2`, `0<0.5<1`, `I.WF` (two charges, two labels), `NeZero 3`, `NeZero 2`; `Im z_u = 0.49434`, `η=0.24717>0`; 46656 real coordinates; `Σ_y S_xy = 1`. Script (Python/numpy, no Lean; model of `FineModel.lean`: `S_xy = W^{-d} sbKernelR(blk x − blk y)`, `X_ij = ω_re + iω_im` for key `i<j`, real diagonal), scratch path `scratchpad/T2064/check_t2064.py`:

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2064/check_t2064.py 6000
row sums of S (stochastic): 0.9999999999999998 1.0  S_ii= 0.017857142857142856  W^-d/7= 0.017857142857142856
number of real coordinates: 46656 | max |sum_c v_c B_c A B_c - diag(S diag A)| = 1.4033044459902308e-16
chain: actual dL/du = (0.015253477325086367+3.1679032227310826e-14j)
       (1/2u) sum_c w_c d_cL + tr spectral = (0.015253477316259215+3.9085820097276346e-18j)
       |difference| = 8.827209381482534e-12
Euler check: d/ds L(H_u((1+s)w)) = (0.00191669207994221-8.250100906256884e-14j)  vs sum_c w_c d_cL = (0.0019166920797865613+5.966429740409376e-20j)  |diff| = 1.761617116074948e-13
40 random coordinates: max |FD d_c L - sqrt(u) tr(B_c K)| = 1.0646009715573905e-13
E[dL/du]  (LHS)          mean = +1.422e-02  SE(re) = 2.62e-05 | Im mean = +2.8e-16  (n=6000)
RHS Stein                mean = +1.419e-02  SE(re) = 8.46e-06 | Im mean = -4.4e-20  (n=6000)
LHS-RHS                  mean = +3.444e-05  SE(re) = 2.24e-05 | Im mean = +2.8e-16  (n=6000)
LHS-RHS(wrong var x2)    mean = -1.591e-03  SE(re) = 4.16e-05 | Im mean = +2.8e-16  (n=6000)
z-score of LHS-RHS: 1.5351721055733316 | z-score control: 38.26342591653198
op norms of B_c (diag, re, im): [1. 1. 1.] | eta = 0.24717149916606487 | first(2) = 2.069449564907104 | spec(2) = 2.069449564907104 | (LW)^d = 216.0
max over 20 samples x 5 times of |dL/dv| / envelope = 9.73004440651299e-08 (must be <= 1); envelope example = 815427.9683795623
same envelope with the d=2 constants (W^-2,(LW)^2):  543618.6455863748
```

Reading: (T1) chain identity holds on one sample to `9e-12`, with `Σ_c ω_c ∂_c F` summed over all 46656 coordinates and `∂_c F` checked by finite differences on 40 random coordinates (`1e-13`) and by the Euler derivative; the closed form `Σ_c v_c B_c A B_c = diag(S diag A)` used for the second derivatives is verified against the brute-force coordinate sum (`1.4e-16`). (T3)/(T4) Stein: `E[F_u'] − RHS = 3.4e-5 ± 2.2e-5` (z = 1.5, n = 6000), while the control with variance doubled is at z = 38, so the check discriminates. (T2) the envelope with the `d=3` constants dominates `|F_v'|` on `[u/2,(1+u)/2]` (ratio `9.7e-8`).

### Verdict
- T1 `loop_flow_derivative_actual_coordinate_chain`: PASS.
- T2 `norm_samplewise_loop_flow_derivative_le_envelope`: PASS (constants `((W:ℝ)^d)⁻¹`, `(L*W)^d`, rows 1, 2).
- T3 `expected_samplewise_loop_flow_derivative`: PASS (extra argument `g` through `PF d L W g`, `gvarF d L W g`, rows 4, 5).
- T4 `deriv_integral_gloop_HflowBlock_spectralZ`: PASS (same `g`).
No statement is false at `d ≥ 3` as ported; no dropped declaration is needed (all four files port in full, 819 source lines).

## (b) Script output — Sat Oct  3 20:03:16 UTC 2026 (worktree RBM3D-wt/T2064, branch t/T2064, commit 0285caf)

```
$ lake build RBM3D.Gauss.LoopFlowStein   (cwd RBM3D-wt/T2064, branch t/T2064, commit 0285caf)
Build completed successfully (3303 jobs).
$ lake env lean RBM3D/Gauss/LoopFlowStein.lean   (Sat Oct  3 20:04:01 UTC 2026)
exit=0, no output lines (no error, no warning)
$ lake build   (full library; the root does not import the new module yet)
full lake build exit=0 | Build completed successfully (3785 jobs).
$ registry pre-check, scratch file outside the repo: import RBM3D; import RBM3D.Gauss.LoopFlowStein; #assert_rbm_axioms; lake env lean
registry precheck exit=0; first output line: axiom audit: 2225 theorems, 950 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 4 of 64 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
$ git diff --name-only main...t/T2064; wc -l LoopFlowStein.lean; grep -cE "sorry|admit|native_decide|^axiom" LoopFlowStein.lean
RBM3D/Gauss/LoopFlowStein.lean
1008 lines; grep count 0
```

`#print axioms` (scratch `axioms_check.lean`, exit 0) of the four targets; all 34 public declarations print the same line:
```
'RBM.Gauss.loop_flow_derivative_actual_coordinate_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.norm_samplewise_loop_flow_derivative_le_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.expected_samplewise_loop_flow_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.deriv_integral_gloop_HflowBlock_spectralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
34 of 34 public declarations: [propext, Classical.choice, Quot.sound] only
```

Target statements, extracted by script (T1 chain rule, T2 envelope, T3 Stein expectation, T4 derivative of the expectation):
```
-- RBM3D/Gauss/LoopFlowStein.lean:240-249
theorem loop_flow_derivative_actual_coordinate_chain (ω : Ω d L W)
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u =
      (1 / (2 * u)) • ∑ c : CoordF d L W,
        (ω c) • deriv (fun t : ℝ =>
          loopL d L W (HflowBlock d L W u (Function.update ω c t))
            (zt E u) I) (ω c) +
      Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
-- RBM3D/Gauss/LoopFlowStein.lean:706-712
theorem norm_samplewise_loop_flow_derivative_le_envelope
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF)
    {v : ℝ} (hv : v ∈ flowWindow u) (ω : Ω d L W) :
    ‖deriv (fun t : ℝ =>
      loopL d L W (HflowBlock d L W t ω) (zt E t) I) v‖ ≤
      flowDerivativeEnvelope d L W E u I ω
-- RBM3D/Gauss/LoopFlowStein.lean:551-564
theorem expected_samplewise_loop_flow_derivative
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    Integrable (fun ω : Ω d L W => deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u) (PF d L W g) ∧
    (∫ ω : Ω d L W, deriv (fun v : ℝ =>
      loopL d L W (HflowBlock d L W v ω) (zt E v) I) u ∂(PF d L W g)) =
      (1 / (2 * u)) • ∫ ω : Ω d L W,
        ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv d L W u ω c
            (zt E u) (I.σ.zip I.a)) ∂(PF d L W g) +
      ∫ ω : Ω d L W,
        Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
          ∂(PF d L W g)
-- RBM3D/Gauss/LoopFlowStein.lean:875-886
theorem deriv_integral_gloop_HflowBlock_spectralZ
    {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1)
    (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) :
    deriv (fun v : ℝ => ∫ ω : Ω d L W,
      loopL d L W (HflowBlock d L W v ω) (zt E v) I ∂(PF d L W g)) u =
      (1 / (2 * u)) • ∫ ω : Ω d L W,
        ∑ c : CoordF d L W, (gvarF d L W g c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv d L W u ω c
            (zt E u) (I.σ.zip I.a)) ∂(PF d L W g) +
      ∫ ω : Ω d L W,
        Matrix.trace (spectralWordDeriv d L W ω E u (I.σ.zip I.a))
          ∂(PF d L W g)
```

Compiled nonempty instances of the four targets (extracted by script; d = 3, L = 3, W = 2, N = (WL)^d = 216, E = 3/10, u = 1/2, g = 1; every hypothesis discharged, no pin left open):
```
-- RBM3D/Gauss/LoopFlowStein.lean:900-903 (data)
private def loopFlowSteinLoop : Loop.LoopIdx (Zd 3 3) :=
  ⟨[true, false], [![0, 0, 0], ![1, 2, 0]]⟩

private theorem loopFlowSteinLoop_wf : loopFlowSteinLoop.WF := rfl
-- RBM3D/Gauss/LoopFlowStein.lean:908-921
example (ω : Ω 3 3 2) :
    deriv (fun v : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (3 / 10) v)
      loopFlowSteinLoop) (1 / 2) =
      (1 / (2 * (1 / 2 : ℝ))) • ∑ c : CoordF 3 3 2,
        (ω c) • deriv (fun t : ℝ =>
          loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) (Function.update ω c t))
            (zt (3 / 10) (1 / 2)) loopFlowSteinLoop) (ω c) +
      Matrix.trace (spectralWordDeriv 3 3 2 ω (3 / 10) (1 / 2)
        (loopFlowSteinLoop.σ.zip loopFlowSteinLoop.a)) :=
  loop_flow_derivative_actual_coordinate_chain 3 3 2 ω (E := 3 / 10) (u := 1 / 2)
    (by norm_num [abs_lt]) (by norm_num) (by norm_num) loopFlowSteinLoop
    loopFlowSteinLoop_wf
-- RBM3D/Gauss/LoopFlowStein.lean:923-932
example (ω : Ω 3 3 2) :
    ‖deriv (fun t : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 t ω) (zt (3 / 10) t)
      loopFlowSteinLoop) (3 / 4)‖ ≤
      flowDerivativeEnvelope 3 3 2 (3 / 10) (1 / 2) loopFlowSteinLoop ω :=
  norm_samplewise_loop_flow_derivative_le_envelope 3 3 2 (E := 3 / 10) (u := 1 / 2)
    (by norm_num [abs_lt]) (by norm_num) (by norm_num) loopFlowSteinLoop
    loopFlowSteinLoop_wf (v := 3 / 4) (by simp only [flowWindow, Set.mem_Icc]; norm_num) ω
-- RBM3D/Gauss/LoopFlowStein.lean:940-958
example :
    Integrable (fun ω : Ω 3 3 2 => deriv (fun v : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (3 / 10) v) loopFlowSteinLoop) (1 / 2))
      (PF 3 3 2 1) ∧
    (∫ ω : Ω 3 3 2, deriv (fun v : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (3 / 10) v) loopFlowSteinLoop) (1 / 2)
        ∂(PF 3 3 2 1)) =
      (1 / (2 * (1 / 2 : ℝ))) • ∫ ω : Ω 3 3 2,
        ∑ c : CoordF 3 3 2, (gvarF 3 3 2 1 c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv 3 3 2 (1 / 2) ω c
            (zt (3 / 10) (1 / 2)) (loopFlowSteinLoop.σ.zip loopFlowSteinLoop.a))
          ∂(PF 3 3 2 1) +
      ∫ ω : Ω 3 3 2,
        Matrix.trace (spectralWordDeriv 3 3 2 ω (3 / 10) (1 / 2)
          (loopFlowSteinLoop.σ.zip loopFlowSteinLoop.a)) ∂(PF 3 3 2 1) :=
  expected_samplewise_loop_flow_derivative 3 3 2 1 (E := 3 / 10) (u := 1 / 2)
    (by norm_num [abs_lt]) (by norm_num) (by norm_num) loopFlowSteinLoop
    loopFlowSteinLoop_wf
-- RBM3D/Gauss/LoopFlowStein.lean:960-976
example :
    deriv (fun v : ℝ => ∫ ω : Ω 3 3 2,
      loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (3 / 10) v) loopFlowSteinLoop
        ∂(PF 3 3 2 1)) (1 / 2) =
      (1 / (2 * (1 / 2 : ℝ))) • ∫ ω : Ω 3 3 2,
        ∑ c : CoordF 3 3 2, (gvarF 3 3 2 1 c : ℝ) •
          Matrix.trace (coordinateSecondWordDeriv 3 3 2 (1 / 2) ω c
            (zt (3 / 10) (1 / 2)) (loopFlowSteinLoop.σ.zip loopFlowSteinLoop.a))
          ∂(PF 3 3 2 1) +
      ∫ ω : Ω 3 3 2,
        Matrix.trace (spectralWordDeriv 3 3 2 ω (3 / 10) (1 / 2)
          (loopFlowSteinLoop.σ.zip loopFlowSteinLoop.a)) ∂(PF 3 3 2 1) :=
  deriv_integral_gloop_HflowBlock_spectralZ 3 3 2 1 (E := 3 / 10) (u := 1 / 2)
    (by norm_num [abs_lt]) (by norm_num) (by norm_num) loopFlowSteinLoop
    loopFlowSteinLoop_wf
```

Statement diff against RBM2D `c9a24cf` (`scratchpad/T2064/stmtdiff.py`: theorem = text up to `:=`, definition in full, comments stripped; renaming `Coord→CoordF`, `BlockIndex→Vtx d`, `Z2 L→Zd d L`, `LoopIdx→Loop.LoopIdx`, `Gsig→Gres`, `gloop→loopL`, `spectralZ→zt`, `spectralM→mE`, `gvar L W→gvarF d L W g`, `P L W→PF d L W g`, `(W:ℝ)⁻¹^2→((W:ℝ)^d)⁻¹`, `(L*W)^2→(L*W)^d`, `L W→d L W`, `.submatrix→blockMat d L W`):
```
--- 34 identical of 34 RBM2D public declarations; RBM3D-only public declarations: []
34 SAME, 0 DIFF, 0 MISSING
```

Name-clash grep, `d = 2` token grep, RBM2D source status:
```
$ for n in <the 34 new public names>: grep -rnw -- "$n" RBM3D/ RBM3D.lean   (main worktree, main = 40f70b9)
hits for the 34 public names: 0
hits for the 10 private names: 0
$ git grep -qw over all t/* branches for the 34 public names, other than t/T2064:
hits: 0
$ (code lines only, docstrings/comments blanked) grep -nE "Z2|zdist2|N2|inv2|1/5|scale|ellT|d = 2|\^ 2|W⁻¹|BlockIndex|spectralZ E|spectralM E" LoopFlowStein.lean
596: have hscaled : Integrable (fun ω : Ω d L W => (1 / (2 * u)) •
603: exact hscaled.add hspec
604: · rw [hfun, integral_add hscaled hspec, integral_smul]
774: _ = _ := by rw [card_BlockIndex, hlen]
  (hscaled is a local name; card_BlockIndex is the merged lemma name; no other d = 2 token in code)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf  ->  c9a24cf
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the four files>   (RBM2D HEAD 9e0f275)
 RBM2D/Gauss/LoopFlowCoordinateChain.lean    | 43 +++--------------------------
 RBM2D/Gauss/LoopFlowDerivativeEnvelope.lean |  5 ----
 RBM2D/Gauss/LoopFlowSteinExpectation.lean   | 14 ++--------
 3 files changed, 6 insertions(+), 56 deletions(-)
(no RBM1D file was used)
```

Narrative.
- File `RBM3D/Gauss/LoopFlowStein.lean`, commit 0285caf, the only file of `git diff main...t/T2064`; it ports RBM2D `c9a24cf` `Gauss/{LoopFlowCoordinateChain,LoopFlowSteinExpectation,LoopFlowDerivativeEnvelope,LoopExpectationDerivative}` in the order chain, Stein expectation, envelope, expected derivative. All 34 public declarations of the four files are ported; none dropped.
- `RBM2D LoopCoordinateSteinSum` (imported by RBM2D `LoopFlowSteinExpectation`) is not ported: neither of its declarations occurs in the four files ((a)). RBM2D's private `spectralWordBound_nonneg` is not ported: it has no use (1 occurrence at `c9a24cf`, its definition).
- Imports: `RBM3D.Gauss.{LoopCoordinate,Stein,SteinMatrix,DominationAt}` and `Mathlib.Analysis.Calculus.ParametricIntegral`. `DominationAt` is the MD file that holds `GaussianProduct.stein`. No ST-2 to ST-6 file, never `RBM3D`.
- Reused, not copied: `coordinateBlock`, `HflowBlock_update`, `gsigCoordinateDeriv`, `coordinateWordDeriv`, `coordinateSecondWordDeriv`, `coordinateFirstWordBound`, `norm_gloop_coordinate_derivatives_le`, `integrable_gloop_coordinate_derivatives` (T2037), `GaussianProduct.stein`, `RBM.integrable_id_gaussianReal`.
- d-dependent exponents: the only `d = 2` exponents in the four files are `(W⁻¹)^2` (now `((W:ℝ)^d)⁻¹`, in `driftA`, `driftD`, `coordinateFirstWordBound_le_one`, and the crude bound of `hasDerivAt_integral_gloop_HflowBlock_spectralZ`) and `(L*W)^2` (now `(L*W)^d`: envelope, trace constants). Both are the merged forms of `norm_Eblk_le_inv_W_sq`, `card_BlockIndex`, `coordinateFirstWordBound`. The token grep above lists no other `d = 2` token in code ((a) row 12).
- Statements: the diff above shows all 34 equal to RBM2D's after the stated renaming. Residual differences, none changing the mathematics: (R1) the 7 statements about the law (`integrable_trace_spectralWordDeriv`, `stein_gloop_first_coordinate_derivative`, `..._sum`, `expected_samplewise_loop_flow_derivative`, `integrable_flowDerivativeEnvelope`, `hasDerivAt_integral_gloop_HflowBlock_spectralZ`, `deriv_integral_gloop_HflowBlock_spectralZ`) carry an extra explicit real argument `g` (variable `(g : ℝ)` after `[NeZero W]`; law `PF d L W g`), RBM2D `P L W` has none (T2064a); (R2) `blockMat d L W (Xmat d L W ω)` replaces the `submatrix` form (definitional, `example … := rfl` at file line 116); (R3) `spectralWordBound d W` and the private `driftA`, `driftD` take `d` explicitly and (by `omit`) no `[NeZero W]` argument; (R4) in the Stein lemma the local functions `g g'` are named `f f'` because `g` is the parameter.
- Proof differences from RBM2D: in `norm_spectral_head_le` the step `‖G*M*G‖ ≤ ‖G‖*‖M‖*‖G‖` is an explicit `norm_mul_le`/`mul_le_mul_of_nonneg_right` term instead of `gcongr`; the rest is the RBM2D text under the renaming.
- No declaration of the file is a `Prop`-valued predicate on samples, matrices or parameters, and no theorem takes one as hypothesis, so `RBM3D/Test/Axioms.lean` is unchanged (ST1-COMMON item 8); the pre-check above exits 0.
- Every deterministic hypothesis of the four targets (`|E| < 2`, `0 < u < 1`, `I.WF`, `v ∈ flowWindow u`) is discharged in the instances; the targets have no pin-type hypothesis (a). Further instances in the file: `integrable_flowDerivativeEnvelope` and `flowWindow_mem`, `hasDerivAt_integral_gloop_HflowBlock_spectralZ`, `stein_gloop_first_coordinate_derivative` at the off-diagonal coordinate `(![0,0,0], ![1,0,0], true)`.
- No `(a′)` section: the name map, the constants (rows 1-2) and the argument `g` (rows 4-5) of (a) are the ones used in the compiled file.

## (c) Verified Mathlib names used (`#check @name` in `scratchpad/T2064/mathlib_names.lean`, exit 0, no error)
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
- `MeasureTheory.Integrable.of_bound`
- `MeasureTheory.integrable_map_measure`
- `MeasureTheory.integral_finsetSum`
- `MeasureTheory.integrable_finsetSum`
- `MeasureTheory.Integrable.bdd_mul`
- `MeasureTheory.Integrable.ofReal`
- `MeasureTheory.integral_add`
- `MeasureTheory.integral_smul`
- `Matrix.trace_add`
- `Matrix.trace_smul`
- `Matrix.trace_sum`
- `ContinuousLinearMap.mulLeftRight`
- `ContinuousLinearMap.mulLeftRight_apply`
- `div_le_div_iff₀`
- `Real.sqrt_le_sqrt`
- `Real.sq_sqrt`
- `norm_sum_le`
- `Matrix.traceLinearMap`
- `LinearMap.toContinuousLinearMap`
- `HasFDerivAt.comp_hasDerivAt`
- `Filter.mem_of_superset`
- `IsOpen.mem_nhds`
- `isOpen_Ioo`
- `List.length_zip`
- also checked, exit 0: `Integrable.smul`, `.abs`, `.const_mul`, `.add`, `integrable_const`, `Filter.Eventually.of_forall`, `measurable_pi_apply`, `Finset.smul_sum`, `Finset.sum_le_sum`, `Real.sqrt_pos`, `Real.sqrt_one`, `Real.norm_eq_abs`, `Complex.real_smul`, `Matrix.submatrix_apply`, `Matrix.sum_apply`. No name was found absent.

## (d) Open issues and paper-delta candidates
- **T2064a** (statement difference to RBM2D, same reason as D68 = T2037a, `docs/paper-deltas.md:378`): the seven statements about the law carry the extra argument `g` and are stated under `PF d L W g` (list in the narrative, R1); the proofs use only that `PF d L W g` is a probability measure with Gaussian marginals `gaussianReal 0 (gvarF d L W g c)` for every `g`.
- **T2064b** (notational): `blockMat d L W (Xmat d L W ω)` for RBM2D's `(Xmat ω).submatrix (splitEquiv).symm (splitEquiv).symm` (equal by `rfl`, file line 116); `spectralWordBound d W`, `driftA`, `driftD` carry `d` explicitly (R2, R3).
- **Observation (no action for this ticket)**: RBM2D `HEAD` (`9e0f275`, commit `99d6fe0` "T2274: merge dead-code deletion") deleted `loop_flow_derivative_actual_coordinate_chain`, `wordDirectionMap_nil`, `wordDirectionMap_cons`, `flowWindow_mem` and `spectralWordBound_nonneg` from these files (diff-stat above). As the ticket instructs, the port follows `c9a24cf`; the first is target T1 and is kept; `flowWindow_mem` is kept and used in an instance.
- No exponent, hypothesis or target was weakened, no frozen or pinned signature changed, no declaration outside the sole writable file touched; no owed or structural predicate introduced.
