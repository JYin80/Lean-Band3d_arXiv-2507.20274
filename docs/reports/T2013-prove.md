Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 01:25:20 UTC 2026

### (i) Exponent table
Notation: `η = η_t`, `m = m^{(E)} = (-E + i√(4-E²))/2` (so `m(m+E) = -1`), `rank` = matrix rank. Values at the instance of (ii) (d=3, W=2, L=3, N=216, E=0.3, t=0.5) unless stated.

| quantity | value | constraint | slack |
|---|---|---|---|
| `m^{(E)}` | `-0.15 + 0.98869 i`; `|m(m+E)+1| = 2.2e-16` | `|E| < 2` gives `Im m > 0` | `2-|E| = 1.7`, `Im m = 0.98869` |
| `z_t = E + (1-t) m` | `0.225 + 0.49434 i` | `t < 1` (`t = 1`: `z_1 = E` real, resolvent may not exist) | `1-t = 0.5` |
| `η_t = (1-t) Im m = Im z_t` | `0.49434`, `η^{-1} = 2.02289` | `η > 0` iff `|E|<2, t<1` (merged `etaT_pos`) | `η = 0.49434 > 0` |
| flow `H_t = √t X` | `H_0 = 0`; `‖G_t‖op = 2.02289 ≤ η^{-1}` | `t ∈ [0,1)`; `G_t(-) = G_t(+)^*` | `‖G_t‖op` vs `η^{-1}`: equal to 6 digits (bound sharp) |
| `Gsig` (merged) vs `G_t` | `Gsig = Gres(Hmat, z_t)` uses `H` (time 1) | agrees with `G_t = Gres(√t H, z_t)` only at `t = 1`, where `η_1 = 0` | none: different matrices for every `t < 1`; `Gres H z σ` must take the flow matrix (pin) |
| `E_a = W^{-d} 1_{[a]}` | `tr E_a = 1`, `‖E_a‖op = W^{-d} = 0.125`, `rank E_a = W^d = 8` | `tr E_a = W^{-d}·W^d = 1` (needs `W ≥ 1`) | equality |
| envelope (5.2), `n ≥ 1` | `max|𝓛^{(n)}|`: n=1 `1.0801`, n=2 `0.17974`, n=3 `0.00159` (n=3 over 300 random `(σ,a)`) | `|𝓛^{(n)}| ≤ W^{d(1-n)} η^{-n} ≤ η^{-n}`; proof: `X = Y E_{a_n}` so `rank X ≤ W^d`, `‖X‖ ≤ (η^{-1} W^{-d})^n`, so `|tr X| ≤ rank·‖X‖ ≤ W^d (η^{-1}W^{-d})^n` | vs `W^{d(1-n)}η^{-n}`: n=1 2.0229 (x1.87), n=2 0.5115 (x2.85), n=3 0.1293; vs `η^{-n}`: 2.0229, 4.0921, 8.2778 |
| envelope, `n = 0` | `tr I = N = 216` | false for `(η^{-1})^0 = 1`: statement needs `n ≥ 1` (merged form `n+1`) | n/a |
| envelope hypotheses | `H` Hermitian, `z` with `|Im z| = η > 0` | merged `norm_gloop_le` is stated for `Hmat ω`, `|E|<2`, `t<1` only | to cover arbitrary `H`: replace `etaT E t` by `η := |Im z|`, `Hmat ω` by any Hermitian `H`; the entry bound `‖G_{xz}‖ ≤ η^{-1}` and the block-average step use nothing else |
| `zztE` third clause | `z = 0.2+0.5i`: `m_sc(z) = -0.07564+0.77620 i`, `t₀ = lemT z = 0.60821`, `E₀ = lemE z = 0.19397` | `Im z > 0` gives `0 < t₀ < 1`, `|E₀| < 2`; `z_{t₀}(E₀) = √t₀ z` | `|z_{t₀} - √t₀ z| = 1.2e-16`; `‖√t₀ G_{t₀} - G(z)‖max = 1.1e-15`; `1-t₀ = 0.3918`, `2-|E₀| = 1.806` |
| BA `S^{(B)}(0)` | `S^{(B)}(0) = I_{L^d}` (script: True); `V` block diagonal | `g = 0` in `sbKernel` | exact |
| BA flow `H_t = λ₀Ψ + √t V`, `λ₀ = √t₀ λ` | at `t=0` `H_0 = λ₀Ψ` (not `0`); `Ψ = Ψ^{(B)} ⊗ I_{W^d}`, Hermitian | `λ₀` is constant along the flow, `m = m(E,λ₀)` data | `H_{t₀} - z_{t₀} = √t₀ (H - z)` iff `λ₀ = √t₀ λ` and `z_{t₀} = √t₀ z` |
| BA data `m, M` (small instance, `λ = 0.3`, `z = 0.2+0.5i`) | `m(z,λ) = -0.06690+0.66315 i`, `t₀ = 0.57013`, `E = 0.18910`, `λ₀ = 0.22652`, `m(E,λ₀) = -0.08860+0.87827 i` | `(1/N) tr(λΨ - z - m)^{-1} = m`, `Im m > 0`; `√t₀ m₀ = m`; `√t₀ M(E,λ₀) = M(z,λ)` | residual `1.4e-17`; `|√t₀ m₀ - m| = 3.0e-10` (limit `E + i1e-9`); `‖√t₀ M₀ - M‖max = 2.0e-10`; `‖√t₀ G_{t₀} - G‖max = 2.4e-10` (Gt_BA) |
| dimension `d` | no target uses `3 ≤ d`; `three_le_L` from `Sizes`, `NeZero W` from `W_pos` | as in the probe | n/a |

External hypothesis of `Gt_BA` (`hlam0`, `hzt`: data `m0` from the deterministic layer, `(eq:t0E0_BA)`, `(eq:zztE_BA)`, `7_8:1798-1801`): concrete limit computation at the compiled sequence `sz0` (`L=4, W=32, N=2097152, lam=1/64`, `z0 = 1/2 + i N^{-4/5}`; spectrum of `Ψ^{(B)}` by Fourier on `Z_4^3`, script 2 below): `m(z0,λ) = -0.24963+0.96758 i`, `t₀ = 0.99999094 ∈ (0,1)`, `λ₀ = √t₀ λ` holds, `m₀ = m/√t₀` has `Im m₀ > 0` and `self_m` residual `5.6e-17` at `(E, λ₀)`, and `|z_{t₀} - √t₀ z0| = 5.9e-17`. So both clauses hold simultaneously with `0 < t₀`, `0 < Im z0`.

### (ii) One concrete nondegenerate instance
Instance A (d=3, W=2, L=3, N=216, `g = 0.5`, S^{(B)} rows sum to 1): one sampled `H` (seed 2013), `E = 0.3`, `t = 0.5`; all loops over all `a ∈ Z_3^3` (27 blocks) and `σ ∈ {±}^n`; n = 1, 2 exhaustive, n = 3 sampled.
Command: `python3 pre2013.py`  (scratchpad `.../scratchpad/pre2013.py`, python3 + numpy 2.0.2; no Lean)
```
d,W,L,N = 3 2 3 216
S^B row sum = 1.0000000000000002  S^B(0)=I: True
H Hermitian: True  spec range: [-1.90092406  1.87996085]
tr E_a = [np.float64(1.0), np.float64(1.0), np.float64(1.0)]  |E_a|op = 0.125  W^-d = 0.125
m^(E) = (-0.15+0.9886859966642595j)  m(m+E)+1 = 2.223188599257471e-16  Im m>0: True
z_t = (0.22499999999999998+0.49434299833212975j)  eta_t = 0.49434299833212975  Im z_t == eta_t: True  1/eta = 2.0228869496966944
G_t(-) = G_t(+)^* : True  ||G_t||op = 2.022886537088808  <= 1/eta: True
n=1: max|L| = 1.080082  <= W^(d(1-n)) eta^-n = 2.022887: True   <= eta^-n = 2.022887: True
n=2: max|L| = 0.179738  <= W^(d(1-n)) eta^-n = 0.511509: True   <= eta^-n = 4.092072: True
n=3: max|L| = 0.001590  <= W^(d(1-n)) eta^-n = 0.129341: True   <= eta^-n = 8.277798: True
rank(G E_a G* E_b) = 8  <= W^d = 8 ; |tr X| = 0.0013862991240856711  <= rank*||X||op = 0.03641774930862057
t=0, sigma = + : L^(1) = (-0.14999999999999997+0.9886859966642593j)  m(sigma) = (-0.15+0.9886859966642595j)  err = 2.237726045655905e-16
t=0, sigma = - : L^(1) = (-0.14999999999999997-0.9886859966642593j)  m(sigma) = (-0.15-0.9886859966642595j)  err = 2.237726045655905e-16
cutGlue word identity G_s E_a -> G_s E_b G_s E_a (k=1,2,3): True
zztE: msc(z) = (-0.07563835867963292+0.7762034347866033j)  t0 = lemT = 0.6082129334782694  E0 = lemE = 0.19397433265437772  |E0|<2: True  0<t0<1: True
z_t0(E0) = (0.15597601526879323+0.3899400381719827j)  sqrt(t0) z = (0.15597601526879312+0.38994003817198275j)  err = 1.2412670766236366e-16
Gt_lemT: ||sqrt(t0) G_t0 - G(z)||max = 1.1121782877960056e-15
BA: V block-diagonal: True  Psi Hermitian: True
BA m(z,lam) = (-0.0668963600508152+0.6631539214601015j)  res = 1.3877787807814457e-17  Im m>0: True
t0 = 0.570134278211131  E = 0.18909883890673665  lam0 = sqrt(t0) lam = 0.22652170986243633
BA m(E,lam0) = (-0.08859595848766694+0.8782653833416119j)  sqrt(t0) m0 - m = 3.0418586204886555e-10  Im m0>0: True
z_t0 = (0.15101447326385903+0.37753618293231966j)  sqrt(t0) z = (0.15101447324162423+0.37753618310406056j)  err = 1.731742552978842e-10
sqrt(t0) M(E,lam0) - M(z,lam) max = 2.0332357431338367e-10
Gt_BA: ||sqrt(t0) G_t0 - G||max = 2.430017890509227e-10
BA at t=0: S^B(0)=I so H_0 = lam0 Psi; Gres(H_0, z_0) trace avg vs m0: (-0.08859595863006207+0.8782653839946862j) (-0.08859595848766694+0.8782653833416119j)
```
Instance B (the compiled sequence `sz0` of the probe, `Gt_BA` hypotheses): `python3 pre2013b.py`
```
sz0: N = 2097152  lam = 0.015625  z0 = (0.5+8.763872947670244e-06j)
m(z0,lam) = (-0.24963381675265855+0.9675806388702384j)  self_m residual = 1.1443916996305594e-16  Im m>0: True
t0 = 0.9999909425703477  (0<t0<1: True )  E = 0.49999999668843337  lam0 = 0.015624929238670612  = sqrt(t0)*lam: True
m0 := m/sqrt(t0) = (-0.24963494728070537+0.96758502079679j)  self_m residual at (E, lam0): 5.551115123125783e-17  Im m0>0: True
z_t0 = (0.49999773563745964+8.76383325847912e-06j)  sqrt(t0) z0 = (0.4999977356374596+8.76383325849902e-06j)  |diff| = 5.897037862482831e-17
```
The `cutGlue` line: `cutGlue k b (σ,a) = (σ[:k] ++ σ[k-1:], a[:k-1] ++ b :: a[k-1:])` (one-based `k`, `RBM2D/Hierarchy/Operations.lean:27`), word identity `... G_s E_a ... -> ... G_s E_b G_s E_a ...` checked at k=1,2,3 with `|σ'| = |σ|+1`.

### Source findings for item 2 (script output)
```
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Path/Step2Props.lean | grep -c "Gt_lemT\|lemT\|zztE"
0
$ (same file, count of "norm_gloop\|envelope\|opNorm") over Hierarchy/Loops, Operations, OperationsPairWord, Path/Step2Props at c9a24cf
Hierarchy/Loops: 0
Hierarchy/Operations: 0
Hierarchy/OperationsPairWord: 0
Path/Step2Props: 0
$ git -C ../RBM2D --no-optional-locks grep -n "^theorem norm_gloop" c9a24cf -- RBM2D
c9a24cf:RBM2D/Gauss/LoopCoordinateDerivativeBounds.lean:218:theorem norm_gloop_coordinate_derivatives_le {η u : ℝ} (hη : 0 < η)
c9a24cf:RBM2D/Gauss/LoopEnvelope.lean:97:theorem norm_gloop_le_crude {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
c9a24cf:RBM2D/Gauss/LoopEnvelope.lean:120:theorem norm_gloop_HflowBlock_le_crude_on_Icc {s t η : ℝ} (hη : 0 < η)
c9a24cf:RBM2D/Gauss/LoopEnvelopeSharp.lean:73:theorem norm_gloop_le_sharp {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
c9a24cf:RBM2D/Hierarchy/LoopHierarchyCutContinuity.lean:53:theorem norm_gloop_any_window_le {s t η : ℝ} (hη : 0 < η)
c9a24cf:RBM2D/Hierarchy/LoopHierarchyCutNormBounds.lean:26:theorem norm_gloop_fixed_le (u : ℝ) (ω : Ω L W) {z : ℂ} {η : ℝ}
c9a24cf:RBM2D/Induction/ConArgDet.lean:967:theorem norm_gloop_symIdx_le_tilde (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im)
c9a24cf:RBM2D/Induction/NonAltGood.lean:245:theorem norm_gloop_zshiftN_le {H : Matrix (BlockIndex L W) (BlockIndex L W) ℂ}
c9a24cf:RBM2D/Induction/NonAltGood.lean:439:theorem norm_gloop_crudeN {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx L W) (Idx L W) ℂ}
c9a24cf:RBM2D/Induction/Split.lean:385:theorem norm_gloop_symIdx_split_le (hH : H.IsHermitian) {σ₁ σ₂ : List Bool}
c9a24cf:RBM2D/Induction/Split.lean:451:theorem norm_gloop_le_loopMax {n : ℕ} (I : LoopIdx (Z2 L)) (hσ : I.σ.length = n)
c9a24cf:RBM2D/Induction/Split.lean:473:theorem norm_gloop_symIdx_le_loopMax {σ : List Bool} {a : List (Z2 L)}
c9a24cf:RBM2D/Induction/Split.lean:480:theorem norm_gloop_symIdx_le_loopMax_mul (hH : H.IsHermitian) {l₁ l₂ : ℕ} (h₁ : 1 ≤ l₁)
c9a24cf:RBM2D/Induction/Split.lean:494:theorem norm_gloop_le_of_symIdx_le (hH : H.IsHermitian) {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
c9a24cf:RBM2D/Induction/Split.lean:678:theorem norm_gloop_le_opNorm (hH : H.IsHermitian) (hz : z.im ≠ 0) (I : LoopIdx (Z2 L))
c9a24cf:RBM2D/Induction/Split.lean:692:theorem norm_gloop_le_of_le_abs_im (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η)
$ grep -n "^theorem norm_gloop_le\|^theorem norm_prod_entry_le\|^theorem norm_Gsig_entry_le" RBM3D/Loop/GLoop.lean
128:theorem norm_Gsig_entry_le (ω : Omega d L W) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
156:theorem norm_prod_entry_le (ω : Omega d L W) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
245:theorem norm_gloop_le (ω : Omega d L W) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {n : ℕ}
```

### Verdicts
* Targets 1 (pinned probe text, `GLoopFlow` + `BlockAnderson`): **PASS**. Every identity in the pinned text holds numerically at instances A and B (`G_t(-) = G_t(+)^*`, `tr E_a = 1`, `𝓛^{(1)}_{0,σ,a} = m(σ)`, `zztE` / `Gt_lemT`, `Gt_BA`); hypotheses `0 < Im z`, `0 < t₀`, `λ₀ = √t₀ λ`, `z_{t₀} = √t₀ z` are jointly satisfiable at nondegenerate data (B: `t₀ ∈ (0,1)`, `Im z0 = 8.8e-6 > 0`).
* Target 2 cutGlue / `gloop_cutGlueL_split`, `gloop_cutGlueR_split`: **PASS** (word identity true at k=1,2,3). Sources at `c9a24cf`: `RBM2D/Hierarchy/Operations.lean:27` (`cutGlue`) and `RBM2D/Hierarchy/OperationsPairWord.lean:113` (`gloop_cutGlueL_split`), `:128` (`gloop_cutGlueR_split`).
* Target 2 envelope `(5.2)`: **PASS** mathematically, with a **source finding**: none of the four named RBM2D files at `c9a24cf` contains an envelope (counts 0 above); RBM2D's loop envelope is `Gauss/LoopEnvelope.lean:97` (`norm_gloop_le_crude`), whose constant is the full dimension `(LW)^2` (trace bound by `card`), a factor `L^d` weaker than `(5.2)` and not the pinned `rank W^d`. The correct closing constant is `W^d · (η^{-1}W^{-d})^n = W^{d(1-n)} η^{-n} ≤ η^{-n}` (table; verified numerically), obtained either from `rank X ≤ W^d` (last factor `E_{a_n}`) or by generalising the merged `norm_gloop_le`/`norm_prod_entry_le` (GLoop.lean:245/156) from `Hmat ω` to an arbitrary Hermitian `H` with `η = |Im z|`. The statement needs `n ≥ 1`. Paper-delta candidate `T2013a`: none for the statement; the difference to report is the source (the ported file is the merged RBM3D proof generalised, not an RBM2D port).
* Target 2 `zztE` for `Gt_lemT`: **PASS**; `Step2Props.lean` at `c9a24cf` has no `zztE`/`lemT` (count 0). The pointwise identity needs only the merged `eq_inv_sqrt_mul_zt` (Defs/Semicircle, `z_{t₀}(E₀) = √t₀ z`) already used by the pinned proof; `RBM2D/Defs/Semicircle.lean:185` (`eq:zztE`) is the RBM2D counterpart.
* Instances: `Lloop_zero_one` (`𝓛^{(1)}_{0,σ,a} = m(σ)`, err `2.2e-16` both signs), `Gt_lemT`, `Gt_BA` at `sz0`: hypotheses satisfiable (B), none vacuous.

Overall: **PASS**.

## (a′) Preflight corrections — Sat Oct  3 02:12:28 UTC 2026
Two corrections to section (a); neither changes a verdict. `$SP` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/t2013` holds every script named below (`final_run.sh` runs them).
```
$ git -C ../RBM2D --no-optional-locks grep -n "theorem norm_gloop_le_sharp\|theorem norm_gloop_le_crude" c9a24cf -- RBM2D | cut -c1-110
c9a24cf:RBM2D/Gauss/LoopEnvelope.lean:97:theorem norm_gloop_le_crude {H : Matrix (BlockIndex L W) (BlockIndex 
c9a24cf:RBM2D/Gauss/LoopEnvelopeSharp.lean:73:theorem norm_gloop_le_sharp {H : Matrix (BlockIndex L W) (BlockI
$ python3 $SP/p52.py   # PyMuPDF text of paper/2507.20274-inventiones-submission.pdf, first "(5.2)" and the count
p44: ..., we always assume that |1 −s|/|1 −t| > (log W)10 =⇒t ≥1 −(log W)−10. (5.2) 5.1. The case g2/L2 ≤1 −
3 occurrences of "(5.2)" in the PDF text
```
* (a) names only `norm_gloop_le_crude` (constant `(LW)^2`) as RBM2D's envelope. RBM2D at `c9a24cf` also has the sharp one, `Gauss/LoopEnvelopeSharp.lean:73` `norm_gloop_le_sharp`: `η⁻¹^n (W⁻²)^(n-1)` = `W^d (η⁻¹ W^{-d})^n` after R3, from `|tr (M E_b)| ≤ ‖M‖` (a diagonal entry is at most the operator norm), not from `rank`. It is ported (section 6c).
* The label "(5.2)" of the ticket, of (a) and of merged `GLoop.lean` is not an equation of this paper: the paper's (5.2) is `t ≥ 1 − (log W)^{-10}` (p. 44). The loop bound follows from `‖G_t‖ ≤ η_t⁻¹` (`7_8:949`) and the block structure of `E_a`; no statement of this ticket depends on the label.

## (b) Script output (commands run Sat Oct  3 02:11:51 UTC 2026 .. Sat Oct  3 02:12:28 UTC 2026; composed Sat Oct  3 02:12:28 UTC 2026; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2013`, branch `t/T2013`, commit `e40d210`)
### b.1 Build, audit, axioms, hygiene
```
$ lake build RBM3D.Loop.GLoopFlow RBM3D.Gauss.BlockAnderson 2>&1 | grep -v '^trace' | tail -3
Build completed successfully (3294 jobs).
$ lake build 2>&1 | grep -v '^trace' | tail -1   # whole library, root `#assert_rbm_axioms` included
Build completed successfully (3691 jobs).
$ lake env lean $SP/FullAudit.lean   # `import RBM3D` + both modules + `#assert_rbm_axioms`; first line and the premise scan
axiom audit: 779 theorems, 310 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 12 (borrowed 5, owed 1, structural 6).
$ lake env lean $SP/BaseAudit.lean   # the same with `import RBM3D` only
axiom audit: 731 theorems, 286 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 12 (borrowed 5, owed 1, structural 6).
$ python3 $SP/names.py FILE; lake env lean $SP/Ax.lean   # one `#print axioms` per public declaration (66), grouped
exit=0
public declarations printed: 66 | sorryAx lines: 0
   64 with axioms [Classical.choice, Quot.sound, propext]
    2 with axioms [(none)]
$ grep -nE "sorry|admit|native_decide|^ *axiom " RBM3D/Loop/GLoopFlow.lean RBM3D/Gauss/BlockAnderson.lean; echo "grep exit=$? (1 = no match)"
grep exit=1 (1 = no match)
$ grep the target names in the output of Ax.lean   # `#print axioms` of every target, one line each
RBM.Gauss.Sizes.Gt_lemT : [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.Lloop_zero_one : [propext, Classical.choice, Quot.sound]
RBM.Loop.LoopIdx.cutGlue does not depend on any axioms
RBM.Gauss.gloopProd : [propext, Classical.choice, Quot.sound]
RBM.Gauss.gloop_cutGlueL_split : [propext, Classical.choice, Quot.sound]
RBM.Gauss.gloop_cutGlueR_split : [propext, Classical.choice, Quot.sound]
RBM.Gauss.norm_loopM_le : [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.norm_Lloop_le : [propext, Classical.choice, Quot.sound]
RBM.Gauss.norm_gloop_le_sharp : [propext, Classical.choice, Quot.sound]
RBM.Gauss.norm_loopM_le_sharp : [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.Gt_BA : [propext, Classical.choice, Quot.sound]
```
### b.2 Item 1: the pinned text against the probe (`git show 5d2a4a8:RBM3D/Probe/T2002Vocab.lean`, lines 448-791)
```
$ python3 $SP/verbatim.py FILE a-b ...   # each probe block must occur contiguously, line for line, in the file
GLoopFlow.lean: probe lines => file lines: 503-598=>48-143, 600-623=>145-168, 630-654=>178-202, 699-742=>206-249, 744-791=>251-298
  all blocks identical; 237 verbatim lines
BlockAnderson.lean: probe lines => file lines: 448-484=>35-71, 486-501=>73-88, 656-668=>94-106, 670-695=>108-133
  all blocks identical; 92 verbatim lines
probe lines of 448-791 in no verbatim block and not in the renamed 624-628: 485 '', 502 '', 599 '', 629 '', 655 '', 669 '', 696 '', 697 'end Sizes', 698 '', 743 ''
probe 624-628 (seqHflow_isHermitian) vs gLoopFlow_seqHflow_isHermitian, name normalised: diff exit=0
ProbeTypes.lean (probe lines 1-793 + #check of the 34 pinned names): exit=0 lines=      92
MineTypes.lean (import BlockAnderson + the same #check): exit=0 lines=      92
diff of the elaborated types: exit=0
```
### b.3 Item 2: the ports against RBM2D `c9a24cf`, after the renaming R1-R4 (`docs/reports/T2002-prove.md` b.9)
```
$ python3 $SP/portdiff.py /Users/junyin/Lean_proof/RBM3D-wt/T2013   # `git show c9a24cf:FILE` vs GLoopFlow.lean, statements up to `:=`, whitespace-normalised
cutGlue Ops:27→317 S= W=                                    cutGlueL_split OpsPW:24→324 S= W=
cutGlueR_split OpsPW:59→361 S= W=                           gloopProd Loops:86→384 S= W=
gloopProd_nil Loops:99→391 S= W=                            gloopProd_cons Loops:102→394 S= W=
gloopProd_append Loops:117→401 S= W~                        gloopProd_cutGlueL_split OpsPW:78→428 S= W~
gloopProd_cutGlueR_split OpsPW:95→446 S= W~                 gloop_cutGlueL_split OpsPW:113→466 S= W~
gloop_cutGlueR_split OpsPW:128→482 S= W~                    norm_matrix_entry_le_opNorm LEnv:24→729 S= W=
norm_green_le→norm_resolvent_le Env:116→741 S= W~           norm_Gsig_le_inv_eta→norm_Gres_le_inv_eta LEnv:55→773 S= W~
norm_Eblk_le_inv_W_sq→norm_Eblk_le_inv_W_pow LEnv:45→788 S= W=  norm_foldr_Gsig_Eblk_le→norm_foldr_Gres_Eblk_le LEnv:65→797 S= W=
norm_trace_mul_Eblk_le LEnvS:55→826 S= W~                   norm_gloop_le_sharp LEnvS:73→866 S= W~
legend: Ops/OpsPW/Loops = RBM2D Hierarchy/{Operations,OperationsPairWord,Loops}, LEnv/LEnvS/Env = RBM2D Gauss/{LoopEnvelope,LoopEnvelopeSharp,Envelope}; RBM2D line -> GLoopFlow.lean line
S = statement identical after renaming: 18/18; W = whole declaration identical (~ proof adapted): 9/18
```
### b.4 Target statements (the pinned ones are compared in b.2; the ported ones in b.3)
```
$ python3 $SP/extract2.py 118 FILE NAME...   # statement up to `:=`, whitespace collapsed, wrapped at 118
GLoopFlow.lean:181 Gt_lemT (n : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : SeqΩ sz) : (Real.sqrt (lemT z) : ℂ) • Gt sz n (lemE z)
    (lemT z) true ω = Gn sz n z ω
GLoopFlow.lean:260 Lloop_zero_one (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) (a : Zd d (sz.L n)) (ω : SeqΩ sz) : Lloop
    sz n E 0 (fun _ : Fin 1 => σ) (fun _ => a) ω = mSigma E σ
GLoopFlow.lean:466 gloop_cutGlueL_split (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L)) (s t : Bool) (a c b : Zd d
    L) (h₁ : σ₁.length = a₁.length) (h₂ : σ₂.length = a₂.length) : loopL d L W H z ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃, a₁ ++
    a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
    Matrix.trace (gloopProd d L W H z ⟨σ₁, a₁⟩ * (Gres H z s * Eblk d L W b * (Gres H z t * Eblk d L W c * gloopProd d
    L W H z ⟨σ₃, a₃⟩)))
GLoopFlow.lean:642 norm_loopM_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 <
    η) (hz : η ≤ |z.im|) {n : ℕ} (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Zd d L) : ‖loopM d L W H z σ a‖ ≤ η⁻¹ ^
    (n + 1)
GLoopFlow.lean:700 norm_Lloop_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {k : ℕ} (σ : Fin (k + 1) → Bool) (a :
    Fin (k + 1) → Zd d (sz.L n)) (ω : SeqΩ sz) : ‖sz.Lloop n E t σ a ω‖ ≤ (etaT E t)⁻¹ ^ (k + 1)
GLoopFlow.lean:866 norm_gloop_le_sharp [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) (hn : 1 ≤ I.a.length) : ‖loopL d L
    W H z I‖ ≤ η⁻¹ ^ I.a.length * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1)
GLoopFlow.lean:903 norm_loopM_le_sharp [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ}
    {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {n : ℕ} (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Zd d L) : ‖loopM d L W
    H z σ a‖ ≤ η⁻¹ ^ (n + 1) * (((W : ℝ) ^ d)⁻¹) ^ n
BlockAnderson.lean:112 Gt_BA (lam0 : ℕ → ℝ) (n : ℕ) {z m0 : ℂ} {E t0 : ℝ} (hz : 0 < z.im) (ht0 : 0 < t0) (hlam0 : lam0
    n = Real.sqrt t0 * sz.lam n) (hzt : ztOf m0 E t0 = (Real.sqrt t0 : ℂ) * z) (ω : SeqΩ sz) : (Real.sqrt t0 : ℂ) •
    Gres (seqHflowBA sz lam0 n t0 ω) (ztOf m0 E t0) true = Gres (seqHBA sz n ω) z true
```
### b.5 Compiled nonempty instances (`d = 3`, `sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`; target `z0 = 1/2 + i N^{-4/5}`)
```
$ python3 $SP/inst.py   # target -> instance, line numbers found by script (all compile in the builds of b.1)
Gt_lemT -> GLoopFlowInst.z0_Gt [GLoopFlow.lean:955]
Lloop_zero_one -> GLoopFlowInst.Lloop_sz0 [GLoopFlow.lean:976]
Gt_BA -> BlockAndersonInst.Gt_BA_sz0 [BlockAnderson.lean:209]
gloop_cutGlueL_split, gloop_cutGlueR_split -> two examples (6-loop, cut k=2 < l=4) [GLoopFlow.lean:1027, :1075]
cutGlue -> examples (decide at k=2; word at k=1) [GLoopFlow.lean:1012, :1018]
norm_loopM_le -> norm_loop_sz0, norm_loop_BA_sz0 [GLoopFlow.lean:1045, BlockAnderson.lean:231]
Sizes.norm_Lloop_le -> GLoopFlowInst.norm_Lloop_sz0 [GLoopFlow.lean:1054]
norm_gloop_le_sharp, norm_loopM_le_sharp -> norm_gloop_sharp_sz0, norm_loop_BA_sharp_sz0 [GLoopFlow.lean:1062, BlockAnderson.lean:240]
loopM_eq_loopL, Mres_zero_msc -> loopL_sz0, Mres_sz0 [GLoopFlow.lean:962, :969]
trace_Eblk, blockMat_zero, Gsig_eq_Gres, gloop_eq_loopM, ztOf_im, ... -> one example [GLoopFlow.lean:984]
ring_inverse_smul_one; gLoopFlow_seqHflow_isHermitian -> two examples [GLoopFlow.lean:1001, :1006]
PsiB/PsiI/seqHBA_isHermitian; seqHflowBA at t=0 -> three examples [BlockAnderson.lean:159, :226, :216]
$ python3 $SP/extract2.py 118 RBM3D/Gauss/BlockAnderson.lean t0 E0 lam0 m0 Gt_BA_sz0   # the data of the block Anderson instance
BlockAnderson.lean:170 t0 : ℝ := 1 / 4
BlockAnderson.lean:173 E0 : ℝ := 1 / 4
BlockAnderson.lean:176 lam0 : ℕ → ℝ := fun n => (1 / 2) * sz0.lam n
BlockAnderson.lean:180 m0 : ℂ := ⟨0, (2 / 3) * z0.im⟩
BlockAnderson.lean:209 Gt_BA_sz0 (ω : Sizes.SeqΩ sz0) : (Real.sqrt t0 : ℂ) • Gres (sz0.seqHflowBA lam0 0 t0 ω) (ztOf
    m0 E0 t0) true = Gres (sz0.seqHBA 0 ω) z0 true
```
### b.6 Name clash, diff-stat, port-source drift
```
$ python3 $SP/clash.py   # `git grep` in `main` of `(def|theorem|...) [ns.]NAME` for every new public short name, and for the pinned `seqHflow_isHermitian`
66 new public declarations, 66 distinct short names; declaration lines of the same short name in main: 0
pinned name seqHflow_isHermitian in main: ['main:RBM3D/Gauss/FineModel.lean:531:theorem seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :']
$ git diff --stat main...t/T2013
 RBM3D/Gauss/BlockAnderson.lean |  246 +++++++++
 RBM3D/Loop/GLoopFlow.lean      | 1097 ++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1343 insertions(+)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the six RBM2D files of b.3>; cat-file of LoopEnvelopeSharp.lean at HEAD
RBM2D HEAD: 9e0f275, pinned: c9a24cf
 RBM2D/Gauss/Envelope.lean          | 175 ++++---------------------------------
 RBM2D/Gauss/LoopEnvelope.lean      |  12 ---
 RBM2D/Gauss/LoopEnvelopeSharp.lean | 116 ------------------------
 RBM2D/Hierarchy/Loops.lean         |   8 --
 RBM2D/Hierarchy/Operations.lean    |  18 ----
 5 files changed, 17 insertions(+), 312 deletions(-)
RBM2D/Gauss/LoopEnvelopeSharp.lean present at HEAD: no
```
### Narrative (at most 40 lines)
1. Delivered: commit `e40d210` on `t/T2013` adds `RBM3D/Loop/GLoopFlow.lean` (1097 lines) and `RBM3D/Gauss/BlockAnderson.lean` (246 lines) and nothing else (b.6). Item 1: 237 + 92 probe lines occur verbatim; the one pinned declaration that is not verbatim is `seqHflow_isHermitian` (probe 624-628), declared as `Sizes.gLoopFlow_seqHflow_isHermitian` with the same proof, because T2006 merged the same statement under that name (`RBM3D/Gauss/FineModel.lean:531`, b.6); the other lines of 448-791 in no block are blank lines and one `end Sizes` (b.2). The elaborated types of the 34 pinned names equal the probe's (b.2). No probe item is forced across the two files: `BlockAnderson` imports `GLoopFlow`, and no `GLoopFlow` item uses a block Anderson item.
2. Evidence: both modules and the whole library build; the root audit with both modules imported reports 0 axioms and the same 12 scanned premises as without them, so no unclassified premise (b.1); the 66 public declarations print only `propext`, `Classical.choice`, `Quot.sound` (two print none); the files contain no `sorry`, `admit`, `native_decide` or `axiom` (b.1).
3. Ports (b.3): 18 declarations of six RBM2D files at `c9a24cf`, 5 public (`cutGlue`, `gloopProd`, `gloop_cutGlueL_split`, `gloop_cutGlueR_split`, `norm_gloop_le_sharp`) and 13 `private`. All 18 statements are identical after R1-R4; the script injects the section variables RBM2D declares outside the declaration (`[NeZero W]`; `{n} [Fintype n] [DecidableEq n]`, renamed `ι`), `norm_Gres_le_inv_eta` is generalised from `BlockIndex L W` to any index type, and `norm_resolvent_le` is stated for `Ring.inverse (H - z • 1)` = `Gres H z true` (paper-delta D22). 9 declarations are identical including the proof; 9 have an adapted proof (explicit `d L W`, `change` to unfold `loopL`, a direct diagonal sum in `norm_trace_mul_Eblk_le`).
4. The envelope: the ticket names `RBM2D/Hierarchy/Loops.lean` as its source, which has none ((a): count 0); the sources are `Gauss/LoopEnvelope.lean`, `Gauss/Envelope.lean`, `Gauss/LoopEnvelopeSharp.lean` (the last is absent at RBM2D HEAD, b.6). Two bounds are delivered. `norm_loopM_le`: `|𝓛^{(n)}| ≤ (η⁻¹)^n` for `H` Hermitian and `η ≤ |Im z|`, the proof of the merged `norm_gloop_le` with `Gres H z` in place of `Gsig`, no `NeZero W`; the merged theorem is recovered by an `example` in section 7. `norm_gloop_le_sharp` / `norm_loopM_le_sharp`: `(η⁻¹)^n (W^{-d})^{n-1}` = `W^d (η⁻¹ W^{-d})^n`, the constant of (a), with `[NeZero W]`. `Sizes.norm_Lloop_le` is the flow case of the first.
5. `zztE`: nothing to port. `Gt_lemT` is the pointwise third clause and its pinned proof uses the merged `eq_inv_sqrt_mul_zt`; `RBM2D/Path/Step2Props.lean` has no `zztE`/`lemT` ((a)).
6. Instances (b.5): every target has one, at `d = 3`, `sz0`, `n = 0`, with `z0` in `𝐃_{1/10,1/10}` (`z0_mem` is the merged `sz0_locDomain`). `Gt_BA_sz0` discharges both scalar clauses of `Gt_BA` with `t₀ = 1/4`, `E = 1/4`, `λ₀ = λ/2`, `m₀ = i (2/3) Im z0` (`Im m₀ > 0`); these are not the deterministic layer's values, for which (a), instance B, checks the clauses numerically. `z0`, `z0_zztE`, `z0_Gt`, `loopL_sz0`, `Mres_sz0`, `Lloop_sz0` are the probe's section 9 instances for these sections.
7. Hypotheses: no new hypothesis and no new `Prop`; `[NeZero W]` appears only on the sharp envelopes; the instances discharge every deterministic hypothesis.
8. Limits: the envelopes are deterministic facts, not paper equations ((a′)); `gloop_cutGlueL_split` and `gloop_cutGlueR_split` keep RBM2D's names (rule R4) but are statements about `loopL`; the single-edge matrix word of `RBM2D/Hierarchy/Operations.lean:71` is an `example`; everything else in the four RBM2D files waits for the ST tickets (ticket).

## (c) Verified Mathlib names used by the new code (script `$SP/Names2.lean`: `#names` prints the type of each constant, first 96 characters); names verified absent last
```
Matrix.l2_opNorm_mulVec : ∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst
Matrix.l2_opNorm_diagonal : ∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype 
Matrix.cstar_norm_def : ∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [
Matrix.toEuclideanCLM : {𝕜 : Type u_1} → {n : Type u_3} → [inst : RCLike 𝕜] → [inst_1 : Fintype 
Matrix.coe_toEuclideanCLM_eq_toEuclideanLin : ∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] 
Matrix.mul_nonsing_inv : ∀ {n : Type u'} {α : Type v} [inst : Fintype n] [inst_1 : DecidableEq n
Matrix.IsHermitian.submatrix : ∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} [inst : Star α] {A
ContinuousLinearMap.opNorm_le_bound : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4} {F : Type 
EuclideanSpace.single : {ι : Type u_1} → {𝕜 : Type u_3} → [RCLike 𝕜] → [DecidableEq ι] → ι → 𝕜 →
PiLp.norm_single : ∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4) [hp : Fact (1 ≤ p)] [inst :
PiLp.norm_apply_le : ∀ {p : ENNReal} {ι : Type u_2} {β : ι → Type u_4} [hp : Fact (1 ≤ p)] [inst
pi_norm_le_iff_of_nonneg : ∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [inst_1 : (i :
inv_anti₀ : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflec
le_div_iff₀ : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosRefl
inv_mul_eq_div : ∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α), a⁻¹ * b = b / a
List.eq_nil_or_concat' : ∀ {α : Type u} (l : List α), l = [] ∨ ∃ L b, l = L ++ [b]
List.eq_nil_of_length_eq_zero : ∀ {α : Type u_1} {l : List α}, l.length = 0 → l = []
List.drop_append_length : ∀ {α : Type u_1} {l₁ l₂ : List α}, List.drop l₁.length (l₁ ++ l₂) = l₂
Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
Complex.norm_natCast : ∀ (n : ℕ), ‖↑n‖ = ↑n
Matrix.l2_opNorm_one : ABSENT
norm_list_prod_le : ABSENT
Complex.ofNat_re : ABSENT
Complex.ofNat_im : ABSENT
```

## (d) Open issues and paper-delta candidates
* **O1 `gloopProd` is public.** CLAUDE.md §3 (E) asks private or stem-prefixed names for unpinned helpers, but `gloopProd` occurs in the statements of `gloop_cutGlueL_split` and `gloop_cutGlueR_split`, so it cannot be private; it keeps RBM2D's name (rule R4). If the dispatcher wants the stem, the rename is `gLoopFlow_gloopProd`, local to `GLoopFlow.lean`.
* **O2 `(5.2)` label and a stale module doc.** See (a′). `RBM3D/Loop/GLoop.lean` lines 36-43 ("What is missing") say the envelope is not proved, while `norm_gloop_le` (`:245`) proves it for `Hmat ω`; the note on `Gsig` in lines 20-23 was corrected by DECISIONS §12, the "What is missing" section was not. Doc-fix candidate for the dispatcher (the file is not writable here).
* **O3 port source pin.** RBM2D HEAD `9e0f275` no longer has `Gauss/LoopEnvelopeSharp.lean` (b.6); a later port of the sharp envelope needs `c9a24cf` (CLAUDE.md §5.2).
* **O4 block Anderson data.** `Gt_BA` keeps `λ₀ = √t₀ λ` and `z_{t₀}(E, λ₀) = √t₀ z` as hypotheses (data of the deterministic layer, DECISIONS §11); that layer (`m(z, λ)`, `M^{(B)}`, `e_λ`) is not part of this ticket.
* Paper-delta candidates: none (no `T2013a`). Signed entries cited, not re-proposed: D19 (blocks numbered from 0), D21 (single-time flow, hence `Gt`, `Lloop`), D22 (`Ring.inverse`, hence `Gres`, `Mres`).
