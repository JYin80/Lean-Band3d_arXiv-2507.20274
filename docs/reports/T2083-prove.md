Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 22:46:31 UTC 2026

Targets (mathematics only): `condExp_loop_step`, `condExp_loop_drift` (RBM2D `Path/LoopStep.lean` at `c9a24cf`, 429 lines) and `kpmODE`, `loopGenN2`, `hierarchyN2` (RBM2D `Path/DriftAlgebra.lean` at `c9a24cf`, 634 lines), at `d` general (`3 ≤ L`, `g : ℝ`, `N = (WL)^d`).
Laws: `seqP_map_slice` gives the one-size law `PF d (sz.L n) (sz.W n) (sz.lam n)`, so `g = sz.lam n` throughout.

### (i) Exponent table: every `W²`, `Z2`, `d = 2` occurrence (counted by `grep` on the `c9a24cf` sources)

| source (c9a24cf) | d = 2 token | d >= 3 replacement | why it holds / slack |
|---|---|---|---|
| LoopStep:140-173,206,308,391-403 | `Z2 L` (index type of `I`) | `Zd d L` | dimension-free (list fold, no count used) |
| LoopStep:176 and 237-238 (`LoopStep_norm_Phi_le`, `hFbdd`) | `(L W)^2 · (\|Im z\|⁻¹ (W⁻¹)^2)^len` | `(L W)^d · (\|Im z\|⁻¹ (W^d)⁻¹)^len` | `#Vtx = (LW)^d`, `‖E_a‖ = W^{-d}`; only used for integrability (finite bound). At the instance: 216·(2.004·1/8)^2 = 13.554 (env.py) |
| LoopStep:213,214,298 (`P (d.L n) (d.W n)`, `Xmat`) | fixed `P` | `PF d (sz.L n) (sz.W n) (sz.lam n)` | `Sizes.seqP_map_slice`; `g` of `genMat` and of `PF` are the same `sz.lam n` |
| LoopStep:317-318 (`envConst … * gridStep^(3/2)`) | `envConst` of RBM2D | `envConst d L W E k v` of T2072: `16(k+3)^4 N^4 (1+η_v⁻¹)^{k+4}`, `N=(WL)^d` | merged pin `OneStepEnvelope` (every `d`, `g`); instance: envConst = 1.600e16, Δ^{3/2} = 3.162e-5, envelope 5.058e11 (large, but it is the conclusion bound, not a hypothesis) |
| LoopStep:216-218 (`hz`: `(spectralZ E u).im ≠ 0`) | `(1-u) Im m` | `zt E u`, `(1-u)·Im mE E > 0` from `u < 1`, `\|E\| < 2` | dimension-free; slack `1-u_{k+1} = 0.499` at the instance |
| DriftAlgebra:58 (`KpmODE`) | `W^2 Σ K S K`, `Z2 L` | `W^d Σ_{c,e} K_{ac} SB_{ce} K_{eb}` with `SB d L g` | `K = W^{-d} Θ_u` (`\|m\|=1` for `\|E\|≤2`, so `ξ = u·\|m\|² = u`, `‖ξ‖ = u < 1`); `∂_u Θ = ΘSΘ`; needs `‖SB‖ = 1` (`3 ≤ L`, any `g`) |
| DriftAlgebra:90,109,113,555 (`Kpm = (W⁻¹)^2 …`) | `(W⁻¹)^2` | `(W^d)⁻¹` = merged `kTwo d L W g (mSigma E) u true false` (`Kn2sol`, `1_2:1175`) | `KLK_two_eq_kTwo` identifies `STKloop` at `σ=(+,-)` with it |
| DriftAlgebra:286 (`DriftAlgebra_cov`) | `W^2 Σ_{p,q} tr(X E_p) SB tr(Y E_q)` | `W^d` | merged `sum_allCoords_trace_blocks`: the coordinate sum `Σ_c gvarF · tr(X C_c Y C_c)`, variance `S_xy = W^{-d} SB_{[x][y]}` |
| DriftAlgebra:319 (`trace_insert`) | `1 = W^2 Σ_p E_p` | `1 = W^d Σ_p E_p` | `(E_a)_{xx} = W^{-d} 1_{[x]=a}`, so `Σ_a E_a = W^{-d}·1` |
| DriftAlgebra:451,459,468-478,501-503,512 (`LoopGenN2`, `EGt`, `LLpair`, `ELKLK`, `w`) | `W^2` | `W^d` | the same two facts; the sum algebra `DriftAlgebra_sum_algebra` uses `SB` symmetric and column sums `= 1` (`sum_SB_col`, `3 ≤ L`); it is dimension-free |
| DriftAlgebra:84 (`normSq (spectralM E) = 1`) | `normSqSpectralMOne` | `norm_mE`, `\|E\| ≤ 2` | `‖mE E‖ = 1` |
| DriftAlgebra:556-560 (`w·c = 1`) | `W^2 (W⁻¹)^2 = 1` | `W^d (W^d)⁻¹ = 1` | `W ≠ 0` |
| DriftAlgebra:568-572 (`Theta_commute_SB`, `Theta_transpose`) | `L` only | `Theta d L g`, `3 ≤ L` | `Theta_commute_SB_of_three_le`, `Theta_transpose_of_three_le` need `‖ξ‖ < 1`, here `u < 1` |
| DriftAlgebra:603-621 (checks at `L=3, W=1`) | `Z2 3`, `W=1` | replaced by an instance at `d = 3` (below) | `W = 1` would make `W^d = W^2`; use `W = 2` |

Scalars unchanged (dimension-free): the matrix calculus (`word1`, `word2`, `deriv2_line`, `deriv_spec`), the freezing lemma, the Hermitian part `½(A+Aᴴ)`, the `3/2` power of `Δ`, the bound `Δ^{3/2}` itself, `|E| < 2`.
Boundary checks (DECISIONS §29): (1) `condExp_loop_step` needs only `u_{k+1} < 1` (so `Im zt > 0`), no `s` hypothesis; `condExp_loop_drift` adds `0 ≤ s n ≤ t n` (so `Δ ≥ 0`, `u_k ≥ 0`) and `u_{k+1} < 1` implies `u_k < 1`; at `K n = 0` `Δ = (t-s)/0 = 0` in Lean and the inequality reads `0 ≤ 0`, so `K n ≠ 0`, `k < K n` are unused. (2) not used: no `ilambda` boundary appears (`g` enters only through `SB` and `PF`, any real). (3) no relation `L^d ≤ W^K` is used (`envConst` has `N^4` explicitly). (4) per fixed `n`: no `∀ᶠ n`.

| constant | value | constraint | slack |
|---|---|---|---|
| `W^d` (contraction coefficient) | 8 at `d=3, W=2` | `= #points per block`, `ΣE_a = W^{-d}` | d=2 value `W²=4` differs: wrong value gives error 5.4e-3 against 4.9e-5 (below) |
| `(WL)^d` | 216 | `= card (Idx d L W)` | exact |
| `‖SB‖`, row/col sums | 1 | `3 ≤ L` | `L = 3` is the boundary case; `#nbrs = 2d = 6` for `L = 3` |
| `u_{k+1}` | 0.501 | `< 1` | 0.499 |
| `Δ` | 1e-3 | `≥ 0` | — |
| `\|E\|` | 0 | `< 2` | 2 |

Findings that change the port (not blockers):
* RBM3D has no `Kpm`, `lkMat`, `LLpair`, `EGt`, `ELKLK`, `loop3`, `thetaGen`, `LoopGenN2`, `HierarchyN2` (grep below). The merged vocabulary of the same objects is `kTwo`/`STKloop`, `STLM`, `STLKM`, `STEGtM`, `STELKLKM`, `STthetaOp` (`Induction/Step2Defs.lean`); `loopPM`, `greenBlk`, `avgErr` exist in `Green/Pins.lean`. RBM2D `thetaGen` is in `UBounds` (ST2-25, a later ticket): at `σ=(+,-)` it equals `(SΘ)D + D(SΘ)` (DriftAlgebra:585-592), i.e. `STthetaOp` with `m₁m₂ = 1`. The statement shape of `HierarchyN2` must be fixed by the prover; no 3D pin text exists in the tree.
* RBM2D's `LoopGenN2/HierarchyN2` have no `d` and no `g`; the 3D forms quantify `∀ d L W g`, with `3 ≤ L`.

Grep (command and output):
```
$ grep -rln "Kpm\|LLpair\|EGt\b\|ELKLK\|lkMat\|thetaGen\|loop3\b\|HierarchyN2\|LoopGenN2" RBM3D
RBM3D/Path/NetLift1.lean        (comment only: "NetLift:707 (netLift_Kpm_diff)")
RBM3D/Induction/Step2Defs.lean  (STELKLKM, STEGtM)
RBM3D/Induction/Step2Core.lean  (STELKLKM)
RBM3D/Induction/Step34Pins.lean (def_ELKLK comment)
RBM3D/Induction/QopAlgebra.lean (comment "thetaGenMat ↦ thetaKer")
$ grep -rn "HierarchyN2\|LoopGenN2\|hierarchyN2" docs RBM3D | grep -v archive   # only T2083.md and T2039-portmap.md
```

### (ii) One concrete nondegenerate instance

Data: `d=3`, `L=3`, `W=2`, `g=1/2` (`sz.lam n = 1/2`), `N = 216`, `E = 0`, `s = 1/2`, `K = 1`, `t = 0.501` (`Δ = 1e-3`), `k = 0`, so `u_0 = 0.5`, `u_1 = 0.501`; loop `pmLoop a₁ a₂` with `a₁ = (0,0,0)`, `a₂ = (1,0,2)`; `M = H_0 = √s X_0` one sample, Hermitian (asserted).
Hypotheses, all true at once: `3 ≤ L`; `|E| = 0 < 2`; `0 ≤ s`; `s ≤ t`; `K ≠ 0`; `k = 0 < 1 = K`; `u_1 = 0.501 < 1`; `0 ≤ u_0 < 1`; `I.WF` (`2 = 2`); `M` Hermitian; `a₁ ≠ a₂`.
Model: `X` Hermitian, `E|X_xy|² = W^{-d} SB_{[x][y]}(g)`, `SB`: `0.4` on the diagonal, `0.1` on the `2d = 6` neighbours, row sums 1 (asserted in the script).
Checks (script `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2083/check.py`, sha256 prefix 31e405ca50e319d3; numpy 2.0.2):
(A) both sides of `condExp_loop_step`: LHS = `E[Φ_{u1}(H_0 + √Δ X_1)]` over fresh draws of `ω(1)` with `ω(0)` fixed (seed 1, 3000 draws); RHS = the integral over `PF` of `Φ_{u1}(H_0 + √Δ X)` (seed 2, antithetic ±X, 3000 pairs).
(B) `condExp_loop_drift`: `genMat` computed by the closed form of `loopGenN2` (coefficient `W^d`, and the d = 2 coefficient `W²` for contrast) against `(E Φ_{u1}(H_0+√ΔX) - Φ_{u0}(H_0))/Δ` (antithetic, 6000 pairs); `∂_uΦ` by central difference.
(C) `kpmODE` by central difference; `hierarchyN2` as `genMat - ∂_u K = (SΘ)D + D(SΘ) + ELKLK + EGt`.
```
$ python3 check.py
N = 216  u0 = 0.5  u1 = 0.501  Delta = 0.001
LHS condExp  = 0.001707+0.000000i  (SE 4.2e-07)
RHS integral = 0.001708+0.000000i  (SE 3.0e-08)
|LHS-RHS| = 8.79e-07   3*SE = 1.27e-06   agree: True
d_u Phi (finite diff) = 0.009380+0.000000i
genMat closed form, coefficient W^d=8 : 0.010647-0.000000i
genMat closed form, d=2 coefficient W^2=4: 0.005323-0.000000i
MC (E Phi_{u1}(H0+sqrtDelta X) - Phi_{u0}(H0))/Delta = 0.010696+0.000000i (SE 2.0e-05)
   minus genMat(W^d)  = 4.91e-05 ;  minus genMat(W^2) = 5.37e-03
KpmODE: max|dK/du - W^d K S K| = 2.63e-11
HierarchyN2: |LHS-RHS| = 7.11e-12  (LHS=-0.000217-0.000000i)
$ python3 env.py
N=216 eta_u1=0.499 envConst=1.600e+16 Delta^(3/2)=3.162e-05 envelope=5.058e+11
crude bound |Phi|<= N*(|Im z|^-1 W^-d)^len: 13.554
```
Reading: (A) the two sides agree within `3 SE`. (B) the one-step increment matches the `W^d` closed form (difference 4.9e-5, `2.5 SE`; the remaining `O(Δ)` term is expected), and misses the `W²` form by 5.4e-3. (C) both identities hold to rounding at `d = 3`. No external hypothesis occurs (the only imported pin is the merged, proved `oneStepEnvelope`, and the `Sizes`-level facts `seqP_map_slice`, `pathH` adaptedness are merged), so no limit computation is needed.

### Verdicts

* `condExp_loop_step`: PASS (hypotheses `|E|<2`, `I.WF`, `u_{k+1}<1`; statement true at `d=3`, check (A)).
* `condExp_loop_drift`: PASS (envelope is the merged `oneStepEnvelope`; check (B)).
* `kpmODE`, `loopGenN2`, `hierarchyN2` (at `W^d`, `Zd d L`, `SB d L g`, `3 ≤ L`): PASS (checks (B), (C)); the statement shape of `LoopGenN2`/`HierarchyN2` is the prover's to choose (see findings), the mathematics does not change.

## (a′) Preflight corrections — Sat Oct  3 23:06:05 UTC 2026

* (a) finding line 41 says the 3D forms of `LoopGenN2`/`HierarchyN2` quantify `∀ d L W g` with `3 ≤ L`. The file states them as `∀ sz : Sizes d, ∀ n`, with `L = sz.L n`, `W = sz.W n`, `g = sz.lam n` (`3 ≤ L` is `sz.three_le_L n`), in the merged vocabulary `STLM`, `STKloop`, `STLKM`, `STEGtM`, `STELKLKM`, `STthetaOp` (the (a) finding that `Kpm`, `LLpair`, ... have no RBM3D definition stands). (a) leaves the shape to the prover; no verdict changes.
* (a)(ii) uses `L = 3`, `W = 2`, `g = 1/2`; the compiled instances use `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), as the ticket's acceptance criteria say. This stage did not rerun `check.py`.

## (b) Script output

Evidence block (one script; commands and verbatim output):
```
$ date -u
Sat Oct  3 23:04:08 UTC 2026
$ git diff --stat main...t/T2083
 RBM3D/Path/DriftAlgebra.lean | 765 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Path/LoopStep.lean     | 428 ++++++++++++++++++++++++
 2 files changed, 1193 insertions(+)
$ lake build RBM3D.Path.LoopStep RBM3D.Path.DriftAlgebra 2>&1 | tail -1
Build completed successfully (3749 jobs).
$ lake env lean RBM3D/Path/LoopStep.lean; lake env lean RBM3D/Path/DriftAlgebra.lean   (no output = no error, no warning)
exit 0
exit 0
$ lake build 2>&1 | tail -1   (full library; root does not import the new modules yet)
Build completed successfully (3822 jobs).
$ lake env lean precheck.lean   (import RBM3D + both new modules + #assert_rbm_axioms; head)
axiom audit: 2667 theorems, 1097 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
precheck exit 0
$ grep -nE "sorry|admit|native_decide|axiom" the two files
grep rc=1 (1 = no match)
$ lake env lean axioms.lean   (#print axioms of every public declaration)
'RBM.Path.pathH_succ' : std3
'RBM.Path.condExp_loop_step' : std3
'RBM.Path.condExp_loop_drift' : std3
'RBM.Path.kpmODE' : std3
'RBM.Path.loopGenN2' : std3
'RBM.Path.hierarchyN2' : std3
'RBM.Path.LoopStep_check_step_sz0' : std3
'RBM.Path.LoopStep_check_drift_sz0' : std3
'RBM.Path.DriftAlgebra_check_kpmODE_sz0' : std3
'RBM.Path.DriftAlgebra_check_loopGenN2_sz0' : std3
'RBM.Path.DriftAlgebra_check_hierarchyN2_sz0' : std3
'RBM.Path.LoopStep_check_labels_sz0' : std3
'RBM.Path.DriftAlgebra_check_labels_sz0' : std3
$ wc -l
     428 RBM3D/Path/LoopStep.lean
     765 RBM3D/Path/DriftAlgebra.lean
    1193 total
$ name-clash grep over RBM3D (new public names, excluding the two files)
RBM3D/Path/StepDecomp.lean:779:`Gauss/GridStepDecomp.lean:532`; RBM2D `pathH_succ`, `Path/LoopStep.lean`, is not imported). -/
```

Registry pre-check scan lines (`grep -E "axiom audit|premises found|^registry"` of the pre-check output; no line of `RBM3D/Test/Axioms.lean` was added: `KpmODE`, `LoopGenN2`, `HierarchyN2` are proved by `kpmODE`, `loopGenN2`, `hierarchyN2` and are hypotheses of no theorem):
```
axiom audit: 2667 theorems, 1097 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 84 (borrowed 2, owed 67, structural 15).
registry: 5 borrowed + 89 owed + 37 structural; 47 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
```

Target statements, extracted from the files by script (`extract.py`: text from the keyword to `:= by`; the `variable {d : ℕ} (sz : Sizes d)` of `LoopStep.lean` supplies `sz`):
```
theorem pathH_succ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    pathH sz s t K n (k + 1) ω
      = pathH sz s t K n k ω
        + (Real.sqrt (gridStep s t K n) : ℂ) • Sizes.seqXmat sz n (ω (k + 1))

theorem condExp_loop_step (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (hE : |E| < 2)
    {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF) (hu1 : gridTime s t K n (k + 1) < 1) :
    (pathP sz)[fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (k + 1) ω))
          (zt E (gridTime s t K n (k + 1))) I | filt sz k]
      =ᵐ[pathP sz] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n k ω
            + (Real.sqrt (gridStep s t K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          (zt E (gridTime s t K n (k + 1))) I ∂(PF d (sz.L n) (sz.W n) (sz.lam n))

theorem condExp_loop_drift (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (hE : |E| < 2)
    {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (_hK : K n ≠ 0) (_hk : k < K n) (hu1 : gridTime s t K n (k + 1) < 1) :
    ∀ᵐ ω ∂(pathP sz),
      ‖(pathP sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (k + 1) ω'))
              (zt E (gridTime s t K n (k + 1))) I | filt sz k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n k ω))
              (zt E (gridTime s t K n k)) I
          - (gridStep s t K n : ℂ) *
              genMat d (sz.L n) (sz.W n) (sz.lam n) E (gridTime s t K n k)
                (pathH sz s t K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) E I.length (gridTime s t K n (k + 1))
            * gridStep s t K n ^ ((3 : ℝ) / 2)

def KpmODE (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ a b : Zd d (sz.L n),
      HasDerivAt (fun v : ℝ => sz.STKloop n E v ![true, false] ![a, b])
        ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ e : Zd d (sz.L n),
          sz.STKloop n E u ![true, false] ![a, c] * SB d (sz.L n) (sz.lam n) c e *
            sz.STKloop n E u ![true, false] ![e, b]) u

def LoopGenN2 (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ a₁ a₂ : Zd d (sz.L n),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M ⟨[true, false], [a₁, a₂]⟩ =
          (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
              sz.STLM n E u M ![true, false] ![a₁, b₁] * SB d (sz.L n) (sz.lam n) b₁ b₂ *
                sz.STLM n E u M ![true, false] ![b₂, a₂] +
            sz.STEGtM n E u M ![true, false] ![a₁, a₂]

def HierarchyN2 (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| < 2 → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, M.IsHermitian →
      ∀ a₁ a₂ : Zd d (sz.L n),
        genMat d (sz.L n) (sz.W n) (sz.lam n) E u M ⟨[true, false], [a₁, a₂]⟩ -
            deriv (fun v : ℝ => sz.STKloop n E v ![true, false] ![a₁, a₂]) u =
          sz.STthetaOp n E u ![true, false] (sz.STLKM n E u M ![true, false]) ![a₁, a₂] +
            sz.STELKLKM n E u M ![true, false] ![a₁, a₂] +
            sz.STEGtM n E u M ![true, false] ![a₁, a₂]

theorem kpmODE (d : ℕ) : KpmODE d

theorem loopGenN2 (d : ℕ) : LoopGenN2 d

theorem hierarchyN2 (d : ℕ) : HierarchyN2 d
```

Compiled nonempty instances at `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`; `n = 0`, `E = 0`, `M = 1` Hermitian, `u = 1/2` resp. grid `s = 1/10`, `t = 1/2`, `K = 4`, `k = 0`, labels `0 ≠ 1`; the first `by norm_num` arguments are `|E| < 2`, `0 ≤ u`, `u < 1`, `0 ≤ s`, `s ≤ t`, `K ≠ 0`, `k < K`; `I.WF` is `rfl`; `*_check_labels_sz0` proves `0 ≠ 1`).  Statement text is in the files at the given lines; the proof terms (extracted by `inst.py`):
```
RBM3D/Path/LoopStep.lean:375  theorem LoopStep_check_step_sz0 :
   ... (statement, lines 376-388)
          (LoopStep_instLoop (sz0.L 0) 0 1) ∂(PF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0)) :=
  condExp_loop_step sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 0
    (by norm_num) (LoopStep_instLoop_wf _ 0 1) LoopStep_inst_gridTime_lt

RBM3D/Path/LoopStep.lean:393  theorem LoopStep_check_drift_sz0 :
   ... (statement, lines 394-411)
          * gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 ^ ((3 : ℝ) / 2) :=
  condExp_loop_drift sz0 (fun _ => (1 / 10 : ℝ)) (fun _ => 1 / 2) (fun _ => 4) 0 0 0
    (by norm_num) (LoopStep_instLoop_wf _ 0 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) LoopStep_inst_gridTime_lt

RBM3D/Path/DriftAlgebra.lean:713  theorem DriftAlgebra_check_kpmODE_sz0 :
   ... (statement, lines 714-718)
          sz0.STKloop 0 0 (1 / 2) ![true, false] ![e, 1]) (1 / 2) :=
  kpmODE 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 0 1

RBM3D/Path/DriftAlgebra.lean:723  theorem DriftAlgebra_check_loopGenN2_sz0 :
   ... (statement, lines 724-735)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] :=
  loopGenN2 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 0 1

RBM3D/Path/DriftAlgebra.lean:740  theorem DriftAlgebra_check_hierarchyN2_sz0 :
   ... (statement, lines 741-754)
          ![true, false] ![(0 : Zd 3 (sz0.L 0)), 1] :=
  hierarchyN2 3 sz0 0 0 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one 0 1
```
Also `example : KpmODE 3 ∧ LoopGenN2 3 ∧ HierarchyN2 3 := ⟨kpmODE 3, loopGenN2 3, hierarchyN2 3⟩` (`DriftAlgebra.lean`, last line before `end Instances`) and `example (ω) : pathH ... = ... := pathH_succ sz0 _ _ _ 0 0 ω` (`LoopStep.lean`).

Script diff of the ported statements against RBM2D `c9a24cf` (`diff2d.py`: RBM2D statement text, renamed by R1-R4 and the merged vocabulary, token diff against the RBM3D text; empty = equal):
```
== pathH_succ ratio=1.000
== condExp_loop_step ratio=1.000
== condExp_loop_drift ratio=1.000
```
Port sources (CLAUDE.md §5.2):
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h   (HEAD of RBM2D; the port source is the pinned c9a24cf)
9e0f275
$ git -C $R2 --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/LoopStep.lean RBM2D/Path/DriftAlgebra.lean
 RBM2D/Path/DriftAlgebra.lean |  73 +++++----------------
 RBM2D/Path/LoopStep.lean     | 151 +++++++------------------------------------
 2 files changed, 41 insertions(+), 183 deletions(-)
(empty = no change since c9a24cf)
$ wc -l of the two RBM2D sources at c9a24cf
LoopStep:      429
DriftAlgebra:      634
```
(RBM2D's `HEAD` has moved since the pinned `c9a24cf`; the port reads `c9a24cf` as ticketed. RBM1D sources cited in the docstrings (`GridLoopStep.lean` at `86573b9`: `H_succ` 74, `condExp_freezeC` 229, `condExp_loop_step` 300, `condExp_loop_drift` 892) were checked with `grep -n` against that commit.)

Narrative.
* `LoopStep.lean` ports RBM2D `Path/LoopStep` line by line (RBM2D `:48` `pathH_succ`, `:68` freezing lemma, `:119-179` Hermitian-part observable, `:189-195` instance and adaptedness, `:205` `condExp_loop_step`, `:307` `condExp_loop_drift`). The three public statements equal RBM2D's after renaming (diff above is empty); the hypotheses are RBM2D's, nothing added. `Sizes.seqP_map_slice` gives the one-size law `PF d (sz.L n) (sz.W n) (sz.lam n)`; `genMat` of T2072 is taken at `g = sz.lam n`; `oneStepEnvelope` is applied pointwise at `M = pathH k ω`.
* `d` replacements in `LoopStep` (rows of (a)(i)): `Z2 L` is `Zd d L`; the bound `LoopStep_norm_Phi_le` is `norm_gloop_le_crude` with `(L W)^d` and `((W:ℝ)^d)⁻¹` (it is used only for integrability); `envConst d L W E k v` is the merged one with `N = (W L)^d`. No other `d = 2` token occurs.
* `DriftAlgebra.lean` ports `:55-69` (the three pins), `:103` `kpmODE`, `:396` `loopGenN2`, `:546` `hierarchyN2` and their helpers. The three pins are `Prop`s in `d`, quantified over `sz` and `n`. `kpmODE` is `hasDerivAt_kTwo` after `STKloop = kTwo` (`KLK_two_eq_kTwo`) and `m(+)m(-) = 1`. `loopGenN2` is the matrix-level core `DriftAlgebra_loopGen_core` at `(d L W g)` (coefficient `W^d` from `sum_allCoords_trace_blocks`, `1 = W^d Σ_p E_p` from `Eblk = W^{-d} 1_{[x]=a}`), applied at `(sz.L n, sz.W n, sz.lam n)` by defeq. `hierarchyN2` is `loopGenN2` and `kpmODE` plus the matrix identity `D, T, S` (`TS = ST`, `wc = 1`), as RBM2D.
* Vocabulary: RBM2D `Kpm`, `lkMat`, `LLpair`, `EGt`, `ELKLK`, `loop3`, `thetaGen` are not ported; they are `STKloop`, `STLKM`, the `STLM` double sum, `STEGtM`, `STELKLKM`, `STLM` at length three, `STthetaOp` of the merged `Induction/{Defs,Step2Defs}`. `STELKLKM` sums `LK(x,a₂) S_{xy} LK(a₁,y)`; RBM2D's `ELKLK` sums `LK(a₁,b₁) S LK(b₂,a₂)`; they agree by `SB` symmetry (proved in `hLK`). `STthetaOp` at `σ = (+,-)` is `(SΘ)D + D(SΘ)` (proved in `hmm`).
* Dropped (nothing a later ticket is marked as consuming): RBM2D `LoopStep_check_T2005_n0_k0` and its private data `LoopStep_example*` (the RBM2D size family has no 3D analogue) and the three `example`s of RBM2D `DriftAlgebra` (`:603`, `:609`, `:615`) at `L = 3, W = 1` (`W = 1` makes `W^d = W^2`); replaced by the `sz0` instances above. Private helpers renamed: `DriftAlgebra_normSq_one` is `DriftAlgebra_mSigma_mul`, `DriftAlgebra_gloop_*` are `DriftAlgebra_loopL_pm`, `DriftAlgebra_loopFine_*`, `DriftAlgebra_avgErr` is replaced by `DriftAlgebra_loopFine_one`.
* Boundary checks (DECISIONS §29): `condExp_loop_step` uses only `u_{k+1} < 1`; `condExp_loop_drift` uses `0 ≤ s n ≤ t n`, `u_{k+1} < 1` (`_hK`, `_hk` unused; at `K n = 0` the step is `0` in Lean and the bound reads `0 ≤ 0`); the three pins use `|E| < 2`, `0 ≤ u < 1`; no `∀ᶠ`, no relation `L^d ≤ W^K`.
* No obstruction: every ported statement is true at `d ≥ 3` as ported; no hypothesis added, no target weakened, only the two sole writable files are touched (`git diff --stat main...t/T2083` above). The root import is the hub's at merge; the full `lake build` above does not see the new modules, the pre-check does.

## (c) Verified Mathlib names (`#check` in a scratch file, output verbatim in the tool log)

* `Complex.mul_conj : ∀ (z : ℂ), z * (starRingEnd ℂ) z = ↑(Complex.normSq z)`
* `Complex.normSq_eq_norm_sq : ∀ (z : ℂ), Complex.normSq z = ‖z‖ ^ 2`
* `Fin.sum_univ_two`, `mul_inv_cancel₀ : a ≠ 0 → a * a⁻¹ = 1`
* `ContinuousLinearMap.comp_condExp_comm`, `integral_re`, `integral_im` (root namespace, `RCLike`), `MeasureTheory.memLp_top_of_bound`
* `Matrix.submatrix_mul_equiv`, `Matrix.isHermitian_add_transpose_self`, `Matrix.trace_mul_comm`, `HasFDerivAt.comp_hasDerivAt`
* `MeasureTheory.integral_re` does not exist (`#check` gave `Unknown identifier`); the name is the root `integral_re`.
* RBM3D names used (all `#check`ed by the build): `hasDerivAt_kTwo`, `KLK_two_eq_kTwo d L g W E t s₁ s₂ a₁ a₂`, `norm_SB d L g hL`, `Theta_commute_SB_of_three_le`, `Theta_transpose_of_three_le`, `sum_SB_row d L g hL`, `SB_transpose d L g`, `sum_allCoords_trace_blocks d L W g`, `blockRelabel_submatrix_split d L W`, `norm_gloop_le_crude d L W`, `continuous_matrixTrace d L W`, `continuous_green_of_isHermitian`, `hasDerivAt_green_moving`, `hasDerivAt_spectralZ`, `spectralZ_im`, `spectralM_im_pos`, `Sizes.seqP_map_slice`, `condExp_freeze`, `oneStepEnvelope`.

## (d) Open issues and paper-delta candidates

* **T2083a** (special case, CLAUDE.md §5.6): `KpmODE`, `LoopGenN2`, `HierarchyN2` are the `n = 2`, `σ = (+,-)` case of (`pro_dyncalK`), (`eq:mainStoflow`), (`LK_SDE`), not the general-`n`, general-`σ` statements; and they are stated at `g = sz.lam n` (the matrix-level core `DriftAlgebra_loopGen_core` is private and holds for every real `g`). ST2-28a (`HierAlgebra`, `HierarchyN`) must take this `sz`/`n` shape (`∀ sz n`, merged `ST*` vocabulary).
* **T2083b** (statement shape, no mathematical difference): RBM2D's `Kpm`, `lkMat`, `LLpair`, `EGt`, `ELKLK`, `thetaGen` are replaced by the merged `ST*` terms (see narrative); `STELKLKM` has the index order `LK(x,a₂) S_{xy} LK(a₁,y)`.
* **T2083c**: `condExp_loop_drift` is bounded by `envConst · Δ^{3/2}` (merged `oneStepEnvelope`), not by RBM1D's `loopDrift`/`zMotionLip`/`genPtLip` (as RBM2D); hypotheses `_hK`, `_hk` are unused.
* Registry: none needed (`kpmODE`, `loopGenN2`, `hierarchyN2` are theorems; the pre-check scan lists no new premise).
* Not done here: the root import (hub), the blueprint, `docs/mathlib-api.md` (names in (c)).
