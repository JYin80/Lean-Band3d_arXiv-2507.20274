Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 20:30:39 UTC 2026

Sources: RBM2D `Path/OneStep.lean` (1692 lines) and `Path/DriftLip.lean` (693 lines) at `c9a24cf` (`git show c9a24cf:...`); paper `1_2_Intro_model_result.tex:990` (`pro_dyncalK`, weight `W^d`). Script: `scratchpad/T2072/check.py`.

### (i) Exponent table (every `W²`/`Z2`/`5` token class of the two files; counts by script over the `c9a24cf` texts)

| token class (RBM2D lines; count) | d ≥ 3 replacement | why it holds | slack at d=3, L=3, W=2 (script) |
|---|---|---|---|
| `Z2 L`, `Z2 3` (OneStep 32 lines, e.g. 70, 87, 558; DriftLip 32, e.g. 142, 324; check 1675) | `Zd d L`; loop index = merged `Loop.LoopIdx (Zd d L)` | type renaming (ST1-COMMON R2); `card_Zd`: `L^d` points | 27 labels |
| `N=(W*L)^2 : ℕ` (OneStep 79, 904, 951, 961, 1191, 1647-1660; DriftLip 276, 282, 294, 303, 318, 326, 341, 350, 366, 411, 529) | `N=(W*L)^d = card Idx = card Vtx` (`card_Idx`, `split_bijective`) | every use is `card` of the index type or `N≥1`; no use of `d=2` beyond the value | N=216 |
| `envConst = 16(k+3)^4 N^4 (1+η⁻¹)^{k+4}` (OneStep 79) | same formula, `N=(WL)^d`, `η=etaT E v` | closure `(32/3)N^4 k(k+1)(k+2)q^{k+3} + N k(k+1) q^{k+2}(1/2+4N²) ≤ 16(k+3)^4 N^4(1+q)^{k+4}` (OneStep 1446-1450) uses only `N≥1`, `q≥0`; g-free, W-free, L-free apart from N | proof bound 5.697e8 vs envConst·D^{3/2} 5.058e11 (ratio ≈ 8.9e2), k=2,g=1,u=1/2 |
| `driftLip = 2N³n²(n+2)(K+‖m‖)K^{n+1}η⁻²` (DriftLip 410-413) | same, `N=(LW)^d` | derivation: `W^d·L^d = N` (DriftLip 636-643 with `W^d`), `(n+n²) ≤ 2n²`, `‖G‖ ≤ η⁻¹`, `‖gloop‖ ≤ N K^k` (card of `Vtx`) | RHS/LHS ≥ 5e12 in all four runs below |
| `(W:ℂ)^2` weight of `eGterm`, `primRhs` (DriftLip 386, 428, 472, ...: 11 lines) | `(W:ℂ)^d` | paper `pro_dyncalK` 1_2:990 has `W^d`; merged `treeEqRhs d L W g` (TreeRep.lean:142) already carries `W^d` | W^d=8 |
| `(L:ℝ)^2` label count in summation lemmas (DriftLip 164, 174, 428, 441, ...: 17 lines) | `(L:ℝ)^d` (`card_Zd`) | `Σ_{a,b} |SB_ab| ≤ L^d` from row sums ≤ 1 | L^d=27 |
| `(W:ℝ)⁻¹ ^ 2 ≤ 1`, `‖E_a‖ ≤ 1` (OneStep 649, 824; DriftLip 192) | `(W:ℝ)⁻¹^d ≤ 1` | `W ≥ 1` (`NeZero W`) | W^{-d}=1/8 |
| `sbSupport L`, `5⁻¹`, `card_le_five`: `‖SB a b‖ = 5⁻¹` on the support, row sum ≤ 1 (OneStep 839-854; DriftLip 143-157) | **argument replaced**: kernel is `a=(1+2dg²)⁻¹` at 0, `b=g²a` at `|x|₁=1`, not uniform (DECISIONS §30); row sum = `a + #{|x|₁=1}·b`, `#≤2d`, so ≤ 1 | `#{|x|₁=1}=2d` at `L≥3`, ≤ 2d for every `L` (merged `sum_norm_SB_row` and `card_nbhd` need `3≤L`: see verdict note 2) | row sums = 1 at L=3 (g=1, 1/2); L=1: 0.1706, L=2: 0.5853 (g=0.9) |
| `Svar` complex block variance, `Fin W × Fin W` offsets (OneStep 861-876; `svar_cast_eq_Spaper`) | no complex `Svar` in RBM3D (ST1-COMMON 11): `svarF d L W g i j = W^{-d} SBR`, offsets `Fin (W^d)`; `Σ_β svar = SBR` (`W^d·W^{-d}`) | `card Fin (W^d)=W^d` | — |
| `svar ≤ 1`, `gvar ≤ 1` (OneStep 810-835) | `svarF ≤ W^{-d}·max(a,b) ≤ 1`, `b ≤ 1/(2d)` for every real `g` | `a,b ≤ 1`, `W^{-d} ≤ 1` | max svarF = 0.01786 (g=1), 0.05 (g=1/2) |
| `Σ_c gvar_c ≤ 2N` (OneStep 886-905) | same: `Σ_c gvar_c = Σ_{ij}svarF_ij + Σ_i svarF_ii = N(1 + W^{-d}/(1+2dg²))` at `L≥3` | row sums ≤ 1, `svarF_ii ≤ 1` | 219.857 (g=1), 226.8 (g=1/2) ≤ 2N=432 |
| `#Coord = 2·card(Idx)²` (OneStep 963-964), `E‖X‖ ≤ 4N²` (951) | same in `card Idx` (the 2 is the Bool pair, not a dimension) | `E|ω_c| ≤ (1+gvar)/2 ≤ 1` | #Coord=93312, 4N²=186624 |
| `‖X‖ ≤ 2Σ_c|ω_c|`, `‖B_c‖ ≤ 2`, `|m_σ|=1` (OneStep 797-816, 1195, 1404) | unchanged | only `Xentry` structure and `|E|<2`; `blockMat` is a reindexing | — |
| `(32/3)`-term, `Λ = 32 N³ N k(k+1)(k+2) η^{-(k+3)}` (OneStep 1237) | unchanged in `N` | `card Idx = card Vtx = N` | — |
| other `^2`: `η⁻¹^2`, `K^2`, `τ^2=Δ`, `Δ^2` (OneStep 174, 223, 1330, 1517...) | none: Taylor/resolvent exponents | no `d` | — |
| time window: `|E|<2`, `0≤u`, `0≤Δ`, `u+Δ<1` (DECISIONS §29) | unchanged; `η_v=(1-v)Im m>0`; `g:ℝ` arbitrary, `1+2dg²>0` | `k`-loops, `z_v` off the real axis for `v<1`; no relation between L and W, no `∀ᶠ n` | runs below at u=0, 1/2, 0.998 |
| `genMat` (OneStep 69-75), `OneStepEnvelope` (86-93): extra parameters `d`, `g` | `coordinateMatrix d L W c`, `gvarF d L W g`, `loopL d L W (blockMat ·) (zt E u) I`, `PF d L W g`, `Xmat`, `etaT` (merged) | `spectralZ E u = E+(1-u)m = zt E u` (RBM2D `Gauss/SpectralWindow.lean` `spectralZ`; merged Semicircle.lean:179) | — |

### (ii) One concrete nondegenerate instance (d=3, L=3, W=2, E=0, one Hermitian sample M = 0.7·X, X ~ PF, Δ = 1e-3)

Hypotheses of the targets, all true at the data: `NeZero 3`, `NeZero 2`, `|E|=0<2`, `I.WF` (σ, a of equal length k=2, 3), `1 ≤ k`, `0 ≤ u`, `0 ≤ Δ`, `u+Δ<1` (u ∈ {0, 1/2, 0.998}), `M₁, M₂` Hermitian, `(spectralZ E u).im = (1-u)·Im mE = 1-u ≠ 0` (Im mE = 1 at E=0). N=216, 27 blocks, 8 points per block. Both sides of `norm_loopDrift_sub_le` are the exact values (loopDrift = W^d(Ẽ + primRhs) with merged cut-glue conventions, TreeRep.lean:84-92, GLoopFlow.lean:317); `genMat` is exact (resolvent jets `R'=-RXR`, `R''=2RXRXR`, `∂_vR=-m R²`, Wick `E tr(UXVX)=Σ_{bc}S_bc U_bb V_cc`); the `Hessian-formula check` compares it with Monte Carlo; the left side of the envelope has an expectation over X, estimated with antithetic Monte Carlo (ns=60 pairs, standard error printed).

Command: `cd scratchpad/T2072 && python3 check.py > out.txt` (numpy 2.0.2). Output, verbatim:
```
d=3 L=3 W=2 N=(WL)^d=216 blocks=27 E=0.0 |E|<2:True 1+2dg^2>0
g=1.0: SB row sums=1..1; max svar=0.01786<=1; sum_c gvar=219.857 <= 2N=432; #Coord=2N^2=93312; E|omega_c|<=(1+gvar)/2<=1
g=0.5: SB row sums=1..1; max svar=0.05<=1; sum_c gvar=226.8 <= 2N=432; #Coord=2N^2=93312; E|omega_c|<=(1+gvar)/2<=1
  L=1: #{x:|x|_1=1}=0 <= 2d=6; row sum a+nb*b = 0.170648 <= 1
  L=2: #{x:|x|_1=1}=3 <= 2d=6; row sum a+nb*b = 0.585324 <= 1
  L=3: #{x:|x|_1=1}=6 <= 2d=6; row sum a+nb*b = 1.000000 <= 1
  L=4: #{x:|x|_1=1}=6 <= 2d=6; row sum a+nb*b = 1.000000 <= 1
[env] g=1.0 k=2 u=0.5 Delta=0.001 v=u+D=0.501 eta_v=0.499
   genMat(exact) = 0.048358-1.0842e-18j; Hessian-formula check: 0.5*E Hess = -0.139068-1.0842e-18j vs MC -0.139209+0j (se 7.9e-04, 10*ns samples)
   LHS_est = |E Phi_v(M+sqrt(D)X) - Phi_u(M) - D*gen| = 2.141e-06 (MC se 2.3e-06, ns=60) ; sharp-proof bound 5.697e+08 ; RHS envConst*D^1.5 = 5.058e+11 ; LHS+3se <= RHS: True
[env] g=0.5 k=3 u=0.5 Delta=0.001 v=u+D=0.501 eta_v=0.499
   genMat(exact) = -2.92487e-05+0.00564976j; Hessian-formula check: 0.5*E Hess = -0.000319266-0.00132515j vs MC -0.000319972-0.0012946j (se 4.0e-05, 10*ns samples)
   LHS_est = |E Phi_v(M+sqrt(D)X) - Phi_u(M) - D*gen| = 1.436e-07 (MC se 1.2e-07, ns=60) ; sharp-proof bound 2.854e+09 ; RHS envConst*D^1.5 = 3.151e+12 ; LHS+3se <= RHS: True
[env] g=1.0 k=2 u=0.0 Delta=0.001 v=u+D=0.001 eta_v=0.999
   genMat(exact) = 0.0306794+0j; Hessian-formula check: 0.5*E Hess = -0.0533057+0j vs MC -0.0533016+0j (se 1.5e-04, 10*ns samples)
   LHS_est = |E Phi_v(M+sqrt(D)X) - Phi_u(M) - D*gen| = 1.872e-08 (MC se 4.8e-07, ns=60) ; sharp-proof bound 1.772e+07 ; RHS envConst*D^1.5 = 4.419e+10 ; LHS+3se <= RHS: True
[env] g=0.5 k=3 u=0.998 Delta=0.001 v=u+D=0.999 eta_v=0.001
   genMat(exact) = -1881.11+1800.58j; Hessian-formula check: 0.5*E Hess = -1271.35+1811.87j vs MC -1167.52+2050.7j (se 1.5e+02, 10*ns samples)
   LHS_est = |E Phi_v(M+sqrt(D)X) - Phi_u(M) - D*gen| = 4.647e+00 (MC se 1.7e+00, ns=60) ; sharp-proof bound 4.405e+25 ; RHS envConst*D^1.5 = 1.437e+30 ; LHS+3se <= RHS: True
[drift] g=1.0 k=2 u=0.5 eta=0.5 |M1-M2|=1.919e-02: LHS=5.369e-05 RHS=driftLip*|M1-M2|=2.674e+09 holds=True ratio RHS/LHS=4.98e+13
[drift] g=0.5 k=3 u=0.5 eta=0.5 |M1-M2|=1.955e-02: LHS=9.801e-06 RHS=driftLip*|M1-M2|=2.298e+10 holds=True ratio RHS/LHS=2.35e+15
[drift] g=1.0 k=2 u=0.0 eta=1 |M1-M2|=1.947e-02: LHS=3.496e-06 RHS=driftLip*|M1-M2|=1.507e+08 holds=True ratio RHS/LHS=4.31e+13
[drift] g=0.5 k=3 u=0.998 eta=0.002 |M1-M2|=1.939e-02: LHS=2.170e+00 RHS=driftLip*|M1-M2|=1.391e+26 holds=True ratio RHS/LHS=6.41e+25
```
Reading: `LHS_est` has the size of its Monte Carlo error (`≈ Δ²`, third order cancels by symmetry); the inequality holds with slack ≥ 1e13 in the four envelope and four drift runs (including `u+Δ=0.999`, `η=1e-3`). The closed-form constants are far from tight; the check confirms nondegeneracy and the d=3 counts, not sharpness.

### Verdicts

1. **`OneStepEnvelope` (with `genMat`, `envConst`)**: PASS. Every `d=2` token is `N=(WL)^d`, `W^d`, `L^d` or the SB row sum; all exponents close as in the table; no statement is false at d ≥ 3. Statement gains the parameters `d`, `g` (paper-delta candidate `T2072a`: RBM2D has no `g`; true for every real `g`, constants `g`-free).
2. **Row sum of SB for every `L`**: RBM2D's `OneStepEnvelope` has no hypothesis on `L`. The port needs `Σ_b ‖SB a b‖ ≤ 1` for all `L ≥ 1`: true (`#{|x|₁=1} ≤ 2d`; L=1,2 rows above), but the merged lemmas (`sum_norm_SB_row`, `card_nbhd`) assume `3 ≤ L`. Prover proves `#{|x|₁=1} ≤ 2d` for all `L`, or states with `3 ≤ L` (paper-delta `T2072b`; `Sizes.three_le_L`, Sizes.lean:145, gives `3 ≤ L n`, so consumers lose nothing).
3. **`norm_loopDrift_sub_le`**: PASS (statement true at d=3: constant `driftLip` with `N=(LW)^d`, weight `W^d`, `L^d` labels; four runs above). Source note: `norm_loopDrift_sub_le`, `loopDrift`, `driftLip`, `DriftLip_eGterm` exist only at `c9a24cf` (DriftLip 384, 396, 410, 654); the kept-lines version `0c1330a` (91 lines) and RBM2D HEAD keep only `norm_green_sub_le_of_herm` (RBM2D T2274 dead-code deletion; OneStep:49 says it is "not used"). Only `norm_green_sub_le_of_herm` is used by OneStep. Porting the target needs DriftLip `c9a24cf` lines 90-663 (the resolvent lemma at 50 is the only theorem of the "91 kept") and the vocabulary `mSigma E` (= RBM2D `KLoop.mSig`), `treeEqRhs d L W g` (= `primRhs`), `loopL`, `Gres`, `Eblk`, `LoopIdx.cutGlue` (GLoopFlow:317), `cutGlueL/R` (TreeRep:84-92). Not BLOCKED: all inputs exist.

## (b) Script output — Sat Oct  3 20:51:14 UTC 2026

### b.1 Builds (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2072`, branch `t/T2072`)
```
$ lake build RBM3D.Path.OneStep   # (scratch `build.out`)
Sat Oct  3 20:48:45 UTC 2026
Build completed successfully (3325 jobs).
exit 0
$ lake env lean RBM3D/Path/OneStep.lean   # (scratch `leanenv.out`)
Sat Oct  3 20:48:59 UTC 2026
exit 0
$ lake build   # whole library, root #assert_rbm_axioms included (tail -2)
Sat Oct  3 20:48:56 UTC 2026
non-vacuity certificates: 4 of 89 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3791 jobs).
exit 0
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Path.OneStep; #assert_rbm_axioms (DECISIONS §20 registry pre-check)
Sat Oct  3 20:49:09 UTC 2026
exit 0
axiom audit: 2479 theorems, 1059 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
97:registry: 5 borrowed + 84 owed + 35 structural; 45 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
```

### b.2 Axioms of every public declaration (`#print axioms`, scratch `ax.lean`)
```
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
```

### b.3 Public declarations, hygiene
```
$ grep -nE "^(noncomputable )?(def|theorem|lemma|abbrev|instance|structure) " RBM3D/Path/OneStep.lean
68:def genMat (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E u : ℝ)
78:def envConst (d L W : ℕ) (E : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
85:def OneStepEnvelope : Prop :=
111:theorem norm_green_sub_le_of_herm {M₁ M₂ : Matrix n n ℂ}
524:noncomputable def DriftLip_eGterm (d L W : ℕ) (g : ℝ) [NeZero L] (m : Bool → ℂ)
536:noncomputable def loopDrift (E u : ℝ) (I : Loop.LoopIdx (Zd d L))
542:theorem loopDrift_eq (E u : ℝ) (I : Loop.LoopIdx (Zd d L)) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
551:noncomputable def driftLip (n : ℕ) (η : ℝ) (m : Bool → ℂ) : ℝ :=
797:theorem norm_loopDrift_sub_le {E u : ℝ} (hz : (zt E u).im ≠ 0)
2205:theorem oneStepEnvelope : OneStepEnvelope := by
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Path/OneStep.lean   # count
0
$ wc -l RBM3D/Path/OneStep.lean
    2429 RBM3D/Path/OneStep.lean
$ git diff --stat main...t/T2072
 RBM3D/Path/OneStep.lean | 2429 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 2429 insertions(+)
$ git log -1 --format="%h %an <%ae> %s" t/T2072
4d70e54 Jun Yin <321276894+JYin80@users.noreply.github.com> T2072: ST2-20 port RBM2D Path/OneStep and Path/DriftLip (genMat, envConst, OneStepEnvelope, norm_loopDrift_sub_le)
```

### b.4 Target statements: `#check` (scratch `ax.lean`) and the source text of the `Prop` pin
```
genMat : (d L W : ℕ) →
  ℝ →
    [NeZero L] →
      [NeZero W] → ℝ → ℝ → Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ
envConst : ℕ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ
OneStepEnvelope : Prop
oneStepEnvelope : OneStepEnvelope
@norm_green_sub_le_of_herm : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {M₁ M₂ : Matrix n n ℂ},
  M₁.IsHermitian → M₂.IsHermitian → ∀ {z : ℂ}, z.im ≠ 0 → ‖RBM.green M₁ z - RBM.green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖
DriftLip_eGterm : (d L W : ℕ) →
  ℝ →
    [NeZero L] →
      (Bool → ℂ) → Matrix (RBM.Gauss.Vtx d L W) (RBM.Gauss.Vtx d L W) ℂ → ℂ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ
loopDrift : (d L W : ℕ) →
  ℝ →
    [NeZero L] →
      [NeZero W] → ℝ → ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ → ℂ
driftLip : ℕ → ℕ → ℕ → ℕ → ℝ → (Bool → ℂ) → ℝ
norm_loopDrift_sub_le : ∀ (d L W : ℕ) (g : ℝ) [inst : NeZero L] [inst_1 : NeZero W] {E u : ℝ},
  (RBM.zt E u).im ≠ 0 →
    ∀ {M₁ M₂ : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ},
      M₁.IsHermitian →
        M₂.IsHermitian →
          ∀ {I : RBM.Loop.LoopIdx (RBM.Zd d L)},
            I.WF →
              1 ≤ I.a.length →
                ‖loopDrift d L W g E u I M₁ - loopDrift d L W g E u I M₂‖ ≤
                  driftLip d L W I.σ.length |(RBM.zt E u).im| (RBM.mSigma E) * ‖M₁ - M₂‖
$ python3 extract.py RBM3D/Path/OneStep.lean OneStepEnvelope   # source text, whitespace-normalised
def OneStepEnvelope : Prop := ∀ (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : Loop.LoopIdx (Zd d L)), I.WF → ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 → ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian → ‖(∫ ω', loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω')) (zt E (u + Δ)) I ∂(PF d L W g)) - loopL d L W (blockMat d L W M) (zt E u) I - (Δ : ℂ) * genMat d L W g E u M I‖ ≤ envConst d L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2)
```

### b.5 Statement diff against RBM2D `c9a24cf` (script `stmtdiff.py`: RBM2D text after the rename script `port.py`, word diff `[-RBM2D-]{+RBM3D+}`; section `variable` binders are not part of the extracted text)
```
## genMat
def genMat [-{L-]{+(d L+} W : [-ℕ}-]{+ℕ) (g : ℝ)+} [NeZero L] [NeZero … L)) : ℂ

## envConst
def envConst [-(L-]{+(d L+} W : ℕ) … ℝ) : ℝ

## OneStepEnvelope
def OneStepEnvelope : Prop := ∀ [-(L-]{+(d L+} W : ℕ) [--]{+(g : ℝ)+} [NeZero L] [NeZero … ℂ) * genMat [--]{+d L W g+} E u M I‖ ≤ envConst [--]{+d+} L W E … ℝ) / 2)

## norm_green_sub_le_of_herm
theorem norm_green_sub_le_of_herm {M₁ … ‖M₁ - M₂‖

## DriftLip_eGterm
noncomputable def DriftLip_eGterm [-(L-]{+(d L+} W : ℕ) [--]{+(g : ℝ)+} [NeZero L] (m … L)) : ℂ

## loopDrift
noncomputable def loopDrift … ℂ) : ℂ

## loopDrift_eq
theorem loopDrift_eq (E … ℂ) : loopDrift [--]{+d L W g+} E u I M = DriftLip_eGterm [--]{+d+} L W [--]{+g+} (mSigma E) (blockMat … u) I + [-treeEqRhs-]{+Loop.treeEqRhs+} d L W … E u)) I

## driftLip
noncomputable def driftLip [-(L W n-]{+(n+} : ℕ) (η … ℂ) : ℝ

## norm_loopDrift_sub_le
theorem norm_loopDrift_sub_le {E … I.a.length) : ‖loopDrift [--]{+d L W g+} E u I M₁ - loopDrift [--]{+d L W g+} E u I M₂‖ ≤ driftLip [--]{+d+} L W I.σ.length … ‖M₁ - M₂‖
```

### b.6 Compiled nonempty instances (section `Instances`, `RBM3D/Path/OneStep.lean`; all compile in b.1)
```
/-- `oneStepEnvelope` at `d = 3`, `L = 3`, `W = 2` (`N = (W L)^3 = 216`), `g = 1/2`, `E = 0`,
`u = 1/2`, `Δ = 1/1000`, `M = 1`, the two-loop `(+,-; 0,0)`. -/
example :
    ‖(∫ ω', loopL 3 3 2 (blockMat 3 3 2 ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
          + (Real.sqrt (1 / 1000) : ℂ) • Xmat 3 3 2 ω')) (zt 0 (1 / 2 + 1 / 1000))
          (OneStep_instLoop 3 3) ∂(PF 3 3 2 (1 / 2))) -
        loopL 3 3 2 (blockMat 3 3 2 (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)) (zt 0 (1 / 2))
          (OneStep_instLoop 3 3) -
        ((1 / 1000 : ℝ) : ℂ) * genMat 3 3 2 (1 / 2) 0 (1 / 2)
          (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (OneStep_instLoop 3 3)‖ ≤
      envConst 3 3 2 0 (OneStep_instLoop 3 3).length (1 / 2 + 1 / 1000) *
        (1 / 1000 : ℝ) ^ ((3 : ℝ) / 2) :=
  oneStepEnvelope 3 3 2 (1 / 2) 0 (by norm_num) (OneStep_instLoop 3 3) (OneStep_instLoop_wf 3 3)
    (1 / 2) (1 / 1000) (by norm_num) (by norm_num) (by norm_num) 1 Matrix.isHermitian_one

/-- `norm_loopDrift_sub_le` at `d = 3`, `L = 3`, `W = 2`, `g = 1/2`, `E = 0`, `u = 1/2`, the two-loop
`(+,-; 0,0)` and the Hermitian matrices `0` and `1`. -/
example :
    ‖loopDrift 3 3 2 (1 / 2) 0 (1 / 2) (OneStep_instLoop 3 3) 0
        - loopDrift 3 3 2 (1 / 2) 0 (1 / 2) (OneStep_instLoop 3 3) 1‖
      ≤ driftLip 3 3 2 (OneStep_instLoop 3 3).σ.length |(zt 0 (1 / 2)).im| (mSigma 0) *
          ‖(0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) - 1‖ := by
  have hz : (zt 0 (1 / 2)).im ≠ 0 := by
    rw [spectralZ_im]
    exact (mul_pos (by norm_num) (spectralM_im_pos (E := 0) (by norm_num))).ne'
  exact norm_loopDrift_sub_le 3 3 2 (1 / 2) hz Matrix.isHermitian_zero Matrix.isHermitian_one
    (OneStep_instLoop_wf 3 3) (by simp [OneStep_instLoop])
```

### b.7 Name clashes, `d = 2` tokens, port diff-stat
```
$ grep -rnw "genMat\|envConst\|OneStepEnvelope\|oneStepEnvelope\|norm_green_sub_le_of_herm\|DriftLip_eGterm\|loopDrift\|loopDrift_eq\|driftLip\|norm_loopDrift_sub_le" /Users/junyin/Lean_proof/RBM3D/RBM3D | wc -l   # main worktree, all new public names
       0
$ grep -cE "Z2|Idx L W|BlockIndex|W \^ 2|L \^ 2|\(W \* L\) \^ 2|sbSupport|Svar|Spaper|5⁻¹|Coord L W|gloop L W" RBM3D/Path/OneStep.lean   # 4 lines: docstring rename table (lines 24-25) and two uses of the merged lemma name `card_BlockIndex`
4
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/OneStep.lean RBM2D/Path/DriftLip.lean
 RBM2D/Path/DriftLip.lean | 639 +----------------------------------------------
 RBM2D/Path/OneStep.lean  |  81 ++----
 2 files changed, 27 insertions(+), 693 deletions(-)
```

### b.8 Narrative (<= 40 lines)
- Source and size: `RBM3D/Path/OneStep.lean` (one file, as the ticket says) ports RBM2D `Path/OneStep.lean` lines 69-1664 (pins and proofs; its check section 1666-1684 is replaced) and `Path/DriftLip.lean` lines 42-664 (check section 666-683 replaced) at `c9a24cf` (the 91 "kept" lines of DriftLip are only `norm_green_sub_le_of_herm`; `loopDrift`, `driftLip`, `DriftLip_eGterm`, `norm_loopDrift_sub_le` exist only at `c9a24cf`, as (a) verdict 3 says; RBM2D `Path/OneStep.lean:49` states that `norm_loopDrift_sub_le` is not used there, the ticket names it as a key statement, so it is ported). Only that file is committed (`4d70e54`); `Test/Axioms.lean` is unchanged because the pre-check (b.1) exits 0.
- Method: a rename script (`Z2 L`->`Zd d L`, `BlockIndex`->`Vtx d L W`, `Gsig`->`Gres`, `gloop L W`->`loopL d L W`, `spectralZ`->`zt`, `KLoop.mSig`->`mSigma`, `KLoop.primRhs`->`Loop.treeEqRhs d L W g`, `Coord/Ω/P/gvar/svar`->`CoordF/Ω/PF/gvarF/svarF d L W g`, `(W*L)^2`->`(W*L)^d`, `W^2`/`L^2` weights -> `^d`), then hand fixes. `OneStep:95-506` (jets of resolvent words) needed no change.
- Public statements: 10 public declarations (b.3). Differences from RBM2D after renaming are only the new parameters `d` and `g` (b.5); `genMat`, `loopDrift`, `DriftLip_eGterm`, `norm_loopDrift_sub_le` take `d L W g` explicitly, `envConst`, `driftLip` take `d L W` (no `g`: the constants are `g`-free).
- d >= 3 exponents (table (a)(i) followed): `envConst` = `16 (k+3)^4 N^4 (1+eta^-1)^(k+4)` with `N = (W L)^d`; `driftLip` = `2 N^3 n^2 (n+2) (K+|m|) K^(n+1) eta^-2` with `N = (L W)^d`; weight of `DriftLip_eGterm` is `W^d`; label counts `L^d` (`DriftLip_sum_sub_le`). The proofs close with the same closure inequality as RBM2D (`OneStep_closure`, unchanged: it uses only `N >= 1`). The remaining `^ 2` in the file are `N^2`, `n^2`, `g^2`, `eta^-2`, Taylor and square exponents (b.7), none a dimension.
- Replaced arguments (RBM2D facts false or absent at d >= 3, DECISIONS §30 / ST1-COMMON 11): the five-point `sbSupport` row sum (`OneStep:839`, `DriftLip:142`) became `OneStep_sum_norm_SB_row`: row sum of `S^(B)(g)` is `<= 1` for every `L >= 1` and every real `g`, via `OneStep_card_sphere_le` (`#{|x|_1 = 1} <= 2d`, no `3 <= L`; the merged `card_nbhd` needs `3 <= L`). `OneStep_svar_le_one` and `OneStep_sum_svar_row` (`OneStep:818-882`) are rewritten on `svarF = W^-d * SBR` (no complex `Svar`, `Spaper`).
- Resolvent bound: RBM2D `norm_green_le` is not in RBM3D; `OneStep_norm_green_le` derives it from the merged `norm_Gsig_le_inv_eta` and `OneStep_green_eq` (`green H z = Gres H z true`). `norm_green_sub_le_of_herm` keeps RBM2D's statement with `RBM.green` (`Green/EntryCore.lean:34`).
- Dropped or merged: RBM2D `OneStep_check_L3_W1` and `DriftLip_check_L3_W1` (replaced by the five examples at d = 3, b.6); the `#print axioms` trailers; `DriftLip_norm_Gsig_sub_le`, `DriftLip_norm_Eblk_le_one`, `DriftLip_sum_norm_SB_row` (duplicates of the `OneStep_` versions, kept once). Nothing else of the two files is dropped.
- DECISIONS §29 checks for `OneStepEnvelope`: (1) time window: hypotheses `0 <= u`, `0 <= Delta`, `u + Delta < 1` are in the statement as in RBM2D, instances at `u = 1/2` and `u = 0` with `Delta = 10^-3` compile (b.6); (2) no `ilambda`, `lemT` or case (ii) occurs; (3) no relation between `L` and `W` is used: the statement is for every `L, W >= 1` (`NeZero`), the instance `L = 3`, `W = 2` has `W^d = 8 < L^d = 27`; (4) fixed `d, L, W, g`, no `forall n` or `forall^f n`; the constants depend on `W, L` only through `N = (W L)^d`.
- Instances: five `example`s in section `Instances` at `d = 3` (b.6): `oneStepEnvelope` at `(L, W, g) = (3, 2, 1/2)` and at the `sz0` data `(4, 32, 1/64)` with `M = 1`; positivity of `envConst`; `norm_loopDrift_sub_le` at `(3, 2, 1/2)` with `M_1 = 0`, `M_2 = 1`; `norm_green_sub_le_of_herm` at `2 x 2`. No hypothesis is left open: Hermitian, `|E| < 2`, `I.WF`, `1 <= I.a.length`, `(zt E u).im != 0` are all discharged. The numeric check of (a)(ii) (script `check.py` of the preflight) is not repeated.

## (c) Verified names

Mathlib (each `#check` resolves in scratch `names.lean`, output `names.out`, first line, cut at 110 chars):
```
@ZMod.natCast_zmod_val : ∀ {n : ℕ} [NeZero n] (a : ZMod n), ↑a.val = a
ZMod.natCast_self : ∀ (n : ℕ), ↑n = 0
@Nat.cast_sub : ∀ {R : Type u_1} [inst : AddGroupWithOne R] {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
@Finset.card_le_card : ∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.card ≤ t.card
@Finset.card_image_le : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {f : α → β} [inst : DecidableEq β],
@Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι 
@one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀
@inv_le_one_of_one_le₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflect
@div_le_one : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α},
@Fintype.sum_equiv : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ]
@Equiv.subLeft : {G : Type u_1} → [AddGroup G] → G → G ≃ G
@Finset.add_sum_erase : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] (s :
@hasDerivAt_integral_of_dominated_loc_of_deriv_le : ∀ {α : Type u_1} [inst : MeasurableSpace α]
@image_norm_le_of_norm_deriv_right_le_deriv_boundary : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
@norm_image_sub_le_of_norm_deriv_right_le_segment : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
@NonUnitalStarAlgHom.norm_map : ∀ {F : Type u_1} {A : Type u_2} {B : Type u_3} [inst : NonUnitalCStarAlgebra A
@Matrix.isHermitian_one : ∀ {α : Type u_1} {n : Type u_2} [inst : NonAssocSemiring α] [inst_1 : StarRing α]
```
Project names used from the merged library (all resolved by the build in b.1): `RBM.Gauss.{Idx, Vtx, split, splitEquiv, card_Idx, card_BlockIndex, Eblk, Gres, loopL, gloopProd, blockMat, svarF, svarF_nonneg, gvarF, CoordF, Ω, PF, Xmat, Xentry, Xmat_isHermitian, Xmat_update, Xmat_eq_sum_coordinates, continuous_Xmat, coordinateMatrix, coordinateMatrix_isHermitian, integrable_sq_coord, integral_sq_coord, P_map_eval, etaT, zt, spectralZ_im, spectralZ_im_gap, spectralM_im_pos, hasDerivAt_spectralZ, spectralMSign, hasDerivAt_green_moving, continuous_green_of_isHermitian, continuous_matrixTrace, norm_Gsig_le_inv_eta, norm_Eblk_le_inv_W_sq, norm_gloop_le_crude, norm_matrix_trace_le_card_mul, GaussianProduct.stein, GaussianProduct.law}`, `RBM.{SB, SB_apply, sbKernelR, sbKernel_eq_ofReal, sbKernelR_nonneg, SBR, unitVec, zdist, zdistD, zdist_eq_zero_iff, zdistD_zero, card_Zd, green, mSigma, isUnit_sub_smul_of_isHermitian, integrable_id_gaussianReal}`, `RBM.Loop.{LoopIdx, LoopIdx.cutGlueL, LoopIdx.cutGlueR, LoopIdx.cutGlue, LoopIdx.length_cutGlueL, LoopIdx.length_cutGlueR, LoopIdx.wf_cutGlueL, LoopIdx.wf_cutGlueR, treeEqRhs}`.
Verified absent from RBM3D (grep of `theorem|lemma|def` heads over `RBM3D/RBM3D`, 0 hits): `norm_green_le`, `hasDerivAt_line`, `isHermitian_add_realSmul`, `LoopIdx.length_cutGlue`, `LoopIdx.WF.cutGlue` (ported as private `OneStep_hasDerivAt_line`, `OneStep_isHermitian_add_realSmul`, `OneStep_length_cutGlue`, `OneStep_wf_cutGlue`, `OneStep_norm_green_le`), and `sbSupport`, `Svar`, `Spaper` (not needed, see b.8).

## (d) Open issues and paper-delta candidates

- No open mathematical issue; all targets are proved, no `sorry`, no new axiom or registry line.
- Interface note for later consumers (ST-3, ST-5, ST2-21): the ported names carry explicit parameters `d L W g` (b.4). `OneStepEnvelope` is a `Prop` with `oneStepEnvelope : OneStepEnvelope` proved here, so a later hypothesis `OneStepEnvelope` can be discharged by it.
- `genMat` keeps RBM2D's definition by `deriv`; its identification with the jets `OneStep_g + OneStep_J1` is the private step `hgen` inside `oneStepEnvelope`, not exported.
- Paper-delta candidate `T2072a`: parameters `d` and `g` are added to `genMat`, `OneStepEnvelope`, `loopDrift`, `DriftLip_eGterm`, `norm_loopDrift_sub_le`, and `d` to `envConst`, `driftLip` (RBM2D has implicit `L W` and a fixed five-point variance profile without `g`); the statement holds for every real `g` with `g`-free constants.
- Paper-delta candidate `T2072b`: `Loop.treeEqRhs d L W g` (weight `W^d`, `S^(B)(g)`, paper `1_2:990` `(pro_dyncalK)`) replaces RBM2D `KLoop.primRhs` (weight `W^2`), and `mSigma` replaces `KLoop.mSig`; same statements after renaming.
- Paper-delta candidate `T2072c`: no hypothesis `3 <= L` is added (RBM2D has none); the d >= 3 proof needs the unit sphere of `Z_L^d` to have at most `2d` points for every `L >= 1`, proved here privately (`OneStep_card_sphere_le`), whereas the merged neighbour count is for `3 <= L`.
