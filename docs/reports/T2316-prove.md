Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 02:05 UTC 2026

Targets (ticket `docs/tickets/T2316.md` "Targets", pins in `docs/tickets/checks/T2316-check.lean` §2): `Pgue` probability,
`gueH` Hermitian / adapted / measurable, `map_gueH_zero`, `map_gueH_last`, `gueGridK_ne_zero`,
`GUEPhaseGrid_gloop_smul_lemT_eq`, `GUEPhaseGrid_gloop_two_smul_lemT_eq`; `GUEPathBounds` is a `Prop` structure that no target takes as a hypothesis.

### (i) Exponent table

| quantity | value | constraint it must satisfy | slack |
|---|---|---|---|
| `N = sz.size n` | `(W L)^d` (`Defs/Sizes.lean:157`); `d=3`, `n=0`: `4*32=128`, `N = 2097152` | `gueGridK`/`gueH`/`gueScale` use `N`; `gueVar` uses `(W*L)^d` (`Universality/Pins.lean:61-62`); both must be the same exponent `d` | identity (no slack): exponent `2` instead of `d=3` gives rel. error `1.0e-1 / 9.7e+1` (script below) |
| unit-step variance `gueUnitVar_c` | `1` (diag), `1/2` (off, per real component) | `gueUnitVar_c / N = gueVar_c` (`1/N`, `1/(2N)`), `N=(WL)^d` | equality, exact for every `d`, every `lam` |
| `ζ(τ) = 1 - e^{-τ}` (`ouZeta`, `ZeroModeProfile.lean:55`) | `τ = 1/20`: `ζ = 0.048771` | `τ ≥ 0` (hyp. of `map_gueH_last`) so that `ζ ∈ [0,1)` | `τ = 0.05 > 0`, margin `0.05` |
| `t₁ = (1-ζ) t₀ = e^{-τ} t₀` | `0.856106` | `t₁ ≥ 0` (needs `0 ≤ t₀`, `ζ ≤ 1`); in `map_gueH_zero` the hyp `0 ≤ t1 n` is not used by the math (both sides use `Real.sqrt (t1 n)`: `gueHV` pin and `seqHflow`, `FineModel.lean:225-227`) | `0.856106 > 0` |
| `Δ = (t₀ - t₁)/K` (`gridStep`, `Walk.lean:67`) | `0.010973` (`t₀=0.9`, `K=4`) | `K n ≠ 0`; `Δ ≥ 0` iff `t₁ ≤ t₀` iff `τ ≥ 0` (needed for `√(Δ/N)² = Δ/N`) | `t₀ - t₁ = 0.043894 > 0`; `gridTime t₁ t₀ K n K = t₁ + KΔ = t₀` exactly (script) |
| variance of `H_K` coord | `t₁ S_c + K (Δ/N) gueUnitVar_c = t₀ (e^{-τ} S_c + (1-e^{-τ}) gueVar_c)` | = coord. variance of `√t₀ 𝐇_τ` (`ouVar`, `OU.lean:56`); identity in `S_c`, i.e. for every `sz.lam` | rel. error `≤ 3.6e-16` at 4 `(d,L,W,lam)` (script) |
| `√t₀` factor | `√0.9 = 0.948683` | `0 ≤ t₀` (`√t₀² = t₀`) | `t₀ = 0.9` |
| `lemT z = ‖msc z‖²` | `z = i`: `((√5-1)/2)² = 0.381966` | `0 < lemT z < 1` for `0 < z.im` (`lemT_pos`, `lemT_lt_one`, `Semicircle.lean:204,209`) | margins `0.382` / `0.618` |
| `lemE z` | `z = i`: `0` | `|lemE z| < 2` (`abs_lemE_lt_two`, `Semicircle.lean:229`) | `2` |
| Lemma 2.8 scaling (2.37) | `z = (√t)⁻¹ zt(lemE z, t)`, `t = lemT z` | `Gres(rH, rz, σ) = r⁻¹ Gres(H, z, σ)` for real `r = √t ≠ 0` (`σ=false`: `conj(rz) = r conj z`) | `|z - zt/r| = 2.2e-16` (script) |
| loop-length power | `L(H,z) = r^{len} L(rH, zt)`, `len = (σ.zip a).length`; 2-loop: `len = 2`, `r² = t` | `loopOf ![true,σ₂] ![a,b] = ⟨[true,σ₂],[a,b]⟩` (`GLoopFlow.lean:117-118`, `List.ofFn`), `len = 2` | exact; the pin writes `(lemT z : ℂ)` for `r²` |
| `gueScale = N η_u`, `η_u = (1-u) Im mE(E)` (`GLoop.lean:75`) | `E=0`: `u = t₁`: `301766.6`; `u = t₀`: `209715.2` | `η_u > 0` iff `u < 1`, `|E|<2`; used only inside `GUEPathBounds` fields | `u ≤ t₀ = 0.9 < 1` |
| `gueGridK = (N+1)^{32 n₀ + 64}` | `n₀=0`: `(N+1)^64`, 405 digits | `≠ 0` (`N+1 ≥ 1`); `N+1 ≤ gueGridK` (`64 ≥ 1`); proof device only | holds for all `n₀,n`; never used as a witness (instance uses `K = 4`) |
| `GUEPathBounds` exponents | `(N η_u)^{-m}`, `1 ≤ m ≤ n₀`; `(N η_u)^{-1/2}` | none for the targets (hypothesis-free) | n/a |

Hypotheses of the targets (no `3 ≤ d`, no condition on `sz.lam`, no `L`-`W` relation): `map_gueH_zero`: `0 ≤ t1 n`;
`map_gueH_last`: `0 ≤ t0 n`, `0 ≤ τ n`, `K n ≠ 0`; homogeneity: `[NeZero L] [NeZero W]`, `0 < z.im`; the others: none.
Coordinate-law step (mathematics): `H_K = √t₁ X + √(Δ/N) Σ_{i=1}^K Y_i` with `X ~ seqP` (independent centred Gaussians, variance `S_c = seqGvar`), `Y_i ~ gueUnit` independent of `X` and of each other; the coordinate is a centred Gaussian of variance `t₁ S_c + K(Δ/N) gueUnitVar_c`; the target side `√t₀ (e^{-τ/2} X + √(1-e^{-τ}) Y)` (`ouSample`, `OU.lean:50-52`, second factor of law `gueP`, variance `gueVar`) has variance `t₀ ouVar`. With `t₁ = e^{-τ}t₀`, `KΔ = t₀(1-e^{-τ})`, `gueUnitVar_c/N = gueVar_c` they agree term by term.
No external hypothesis occurs in any target (`GUEPathBounds` is only a structure, proved elsewhere by UN-33), so no limit computation is owed.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`Defs/Sizes.lean:260,267`: `L 0 = 4`, `W 0 = 32`, `lam 0 = 1/64`, `size 0 = 2097152`), `n = 0`, `τ = 1/20`, `t₀ = 9/10`,
`t₁ = (1-ζ(1/20))·9/10`, `K ≡ 4`, `k = 4`; homogeneity at `d = 3`, `L = 3`, `W = 2` (`Vtx` = `Zd 3 3 × Fin (2^3)`, dimension `27·8 = 216`),
`M = blockMat (diagonal 2) = 2·1`, `z = i`, `σ = ![true,false]`, `a = b = 0`. All hypotheses above hold at once: `0 ≤ t₁ = 0.856`, `0 ≤ t₀`, `0 ≤ τ = 0.05`, `K = 4 ≠ 0`, `0 < Im i = 1`,
`NeZero 3`, `NeZero 2`; no `N = 0`, no empty index, `gridTime(K) = t₀ > t₁`.
Hand check of homogeneity: `LHS = tr(Gres(2,i,true) E_0 Gres(2,i,false) E_0) = 8·(1/8)²/((2-i)(2+i)) = 1/40`;
`RHS = t·(1/8)/(4t + (1-t)²) = (1/8) t/(1+t)² = 1/40` for `t = ((√5-1)/2)²` (`t/(1+t)² = 1/5`).

Command (Python 3.9.6 with numpy 2.0.2; script `T2316/chk.py` in the scratchpad; variance rows use `S_xx = (W^d)⁻¹ (1+2d g²)⁻¹`, `S_xy = (W^d)⁻¹ g² (1+2d g²)⁻¹` from `Gauss/FineModel.lean:623-630`):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2316/chk.py`
Output (verbatim):
```
d,L,W,lam= (3, 4, 32, 0.015625) rel.err diag/off: ['0.00e+00', '3.64e-16']
d,L,W,lam= (3, 4, 32, 1.0) rel.err diag/off: ['0.00e+00', '0.00e+00']
d,L,W,lam= (3, 3, 2, 0.5) rel.err diag/off: ['1.61e-16', '0.00e+00']
d,L,W,lam= (4, 3, 2, 0.5) rel.err diag/off: ['1.94e-16', '0.00e+00']
WRONG-EXPONENT control N=(WL)^2, d=3: (3, 4, 32, 0.015625) ['1.02e-01', '9.74e+01']
WRONG-EXPONENT control N=(WL)^2, d=3: (3, 3, 2, 0.5) ['2.36e-02', '9.32e-02']
d=2 control (2,4,32,1/64): ['0.00e+00', '5.88e-16']
N= 2097152 W^d= 32768
zeta=0.048771 t1=0.856106 (>0) t0=0.900 tau=0.050 K=4 Delta=0.010973  gridTime(K)=0.900000000000
u=0.8561 eta=(1-u)Im mE=0.143894 gueScale=N*eta=301766.6
u=0.9000 eta=(1-u)Im mE=0.100000 gueScale=N*eta=209715.2
size+1 <= gueGridK at n0=0 : True ; digits of (N+1)^(32*0+64): 405
msc check m(m+z)+1 = 2.220446049250313e-16
lemT=0.381966 (<1) lemE=-0.000 zt=0.6180339887498948j  z - zt/r = 2.220446049250313e-16
dim= 216  LHS= (0.025000000000000005+0j)  RHS= (0.025000000000000005+0j)  |diff|= 0.0  closed form 1/40= 0.025
```
The "WRONG-EXPONENT" and "d=2 control" lines are controls (exponent `2` fails at `d = 3`; `d = 2` passes), as the ticket asked.

### Verdicts
- `Pgue_isProbabilityMeasure`, `gueH_isHermitian`, `gueH_adapted`, `gueH_measurable`, `gueGridK_ne_zero`: PASS (hypothesis-free, no exponent involved beyond `N ≥ 0`).
- `map_gueH_zero`: PASS (hyp `0 ≤ t1 n` holds at `0.856`; the law identity needs only the step-0 marginal `seqP`).
- `map_gueH_last`: PASS (variance identity exact for every `d`, every `lam`; checked at `d = 3`, with wrong-exponent control failing).
- `GUEPhaseGrid_gloop_smul_lemT_eq`, `GUEPhaseGrid_gloop_two_smul_lemT_eq`: PASS (scaling exponent `r^{len}`; instance `1/40 = 1/40`).
- Overall: PASS.

## (b) Script output — Thu Oct  8 02:22 UTC 2026

Worktree `../RBM3D-wt/T2316`, branch `t/T2316`; commands run there; scratch files (`axioms.lean`, `pins.lean`, `registry.lean`, `consumers.lean`, `stmts.py`, `stmtdiff.py`, `Grid2D.lean`) are in the scratchpad dir `T2316/` and not committed.
```
$ git log -1 --format="%h" ; git diff --stat main...t/T2316
b163e85
 RBM3D/Test/Axioms.lean                |   1 +
 RBM3D/Universality/GUEPhase/Grid.lean | 897 ++++++++++++++++++++++++++++++++++
 2 files changed, 898 insertions(+)
$ lake build RBM3D.Universality.GUEPhase.Grid > build.out ; echo $? ; tail -1 build.out ; grep -c "GUEPhase/Grid.lean" build.out   # warnings/errors of the file
0
Build completed successfully (3738 jobs).
0
$ lake build   # full library incl. root #assert_rbm_axioms (the root does not import Grid yet; the hub adds that)
Build completed successfully (4123 jobs).
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/Grid.lean
0
$ grep -c "3 ≤ d" Grid.lean ; grep -n "sz\.lam" Grid.lean | awk -F: '$1 > 100'   # hypotheses on d / on the coupling
0
626:            ouVar d (sz.L n) (sz.W n) (sz.lam n) (τ n) c)).map
662:      = (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) := rfl
$ lake env lean T2316/axioms.lean   # #print axioms of the 19 public declarations and the 2 GridCheck lemmas; grouped by axiom set
[propext, Classical.choice, Quot.sound]: gueUnitVar gueUnit gueStepMeasure Pgue gueH gueScale GUEPathBounds gueUnit_isProbabilityMeasure gueStepMeasure_isProbabilityMeasure Pgue_isProbabilityMeasure gueH_isHermitian gueH_adapted gueH_measurable gueGridK_ne_zero map_gueH_zero map_gueH_last GUEPhaseGrid_gloop_smul_lemT_eq GUEPhaseGrid_gloop_two_smul_lemT_eq GridCheck.t1_pos
[propext]: gueGridK
[propext, Quot.sound]: GridCheck.gueGridK_size_le
```

**Target statements, extracted from the file by script** (`python3 -I T2316/stmts.py Grid.lean <names>`: header up to `:=`; the file has `variable {d : ℕ} (sz : Sizes d)`, and in the homogeneity section `variable {L W : ℕ} [NeZero L] [NeZero W]`; vocabulary `def`s and the `GUEPathBounds` fields are compared with the check file by the `rfl`/`Iff` examples below):
```
L164: theorem gueH_isHermitian (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    (gueH sz t1 t0 K n k ω).IsHermitian
L181: theorem gueH_adapted (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (i j : Idx d (sz.L n) (sz.W n)) :
    StronglyMeasurable[filt sz k] (fun ω : PathΩ sz => gueH sz t1 t0 K n k ω i j)
L205: theorem gueH_measurable (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (gueH sz t1 t0 K n k)
L108: theorem gueGridK_ne_zero (n0 n : ℕ) : gueGridK sz n0 n ≠ 0
L542: theorem map_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (_ht1 : 0 ≤ t1 n) :
    (Pgue sz).map (gueH sz t1 t0 K n 0) = (Sizes.seqP sz).map (Sizes.seqHflow sz n (t1 n))
L559: theorem map_gueH_last (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (ht0 : 0 ≤ t0 n) (hτ : 0 ≤ τ n)
    (hK : K n ≠ 0) :
    (Pgue sz).map (gueH sz (fun n => (1 - ouZeta (τ n)) * t0 n) t0 K n (K n)) =
      (ouP (UNModel.band sz) n).map
        (fun ω => ((Real.sqrt (t0 n) : ℝ) : ℂ) • ouMat (UNModel.band sz) n (τ n) ω)
L758: theorem GUEPhaseGrid_gloop_smul_lemT_eq
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ : List Bool) (a : List (Zd d L)) :
    loopL d L W M z ⟨σ, a⟩
      = ((Real.sqrt (lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        loopL d L W (((Real.sqrt (lemT z) : ℝ) : ℂ) • M)
          (zt (lemE z) (lemT z)) ⟨σ, a⟩
L772: theorem GUEPhaseGrid_gloop_two_smul_lemT_eq
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ₂ : Bool) (a b : Zd d L) :
    loopL d L W M z (loopOf ![true, σ₂] ![a, b])
      = ((lemT z : ℝ) : ℂ) *
        loopL d L W (((Real.sqrt (lemT z) : ℝ) : ℂ) • M)
          (zt (lemE z) (lemT z)) (loopOf ![true, σ₂] ![a, b])
```

**Compiled nonempty instances** (file lines 795-895, namespace `RBM.Univ.GUEPhase.GridCheck`, part of the module built above; `sed -n 795,895p Grid.lean | grep -v "^\s*$" | grep -v "^\s*--" | grep -v "^/--"`; `sz0`: `d = 3`, `L 0 = 4`, `W 0 = 32`, `N = 2097152`; `t0 = 9/10`, `tau = 1/20`, `K = 4`; homogeneity at `d = 3, L = 3, W = 2, z = i`):
```lean
namespace RBM.Univ.GUEPhase.GridCheck
open MeasureTheory ProbabilityTheory Matrix RBM RBM.Gauss RBM.Path RBM.Univ
theorem t1_pos : 0 ≤ (1 - ouZeta (1 / 20)) * (9 / 10 : ℝ) := by
  unfold ouZeta
  have := Real.exp_pos (-(1 / 20 : ℝ))
  nlinarith
example (ω : PathΩ SizesInst.sz0) :
    (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) 0 4 ω).IsHermitian :=
  gueH_isHermitian SizesInst.sz0 _ _ _ 0 4 ω
example (n k : ℕ) (ω : PathΩ SizesInst.sz0) :
    (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) n k ω).IsHermitian :=
  gueH_isHermitian SizesInst.sz0 _ _ _ n k ω
example (i j : Idx 3 (SizesInst.sz0.L 0) (SizesInst.sz0.W 0)) :
    StronglyMeasurable[filt SizesInst.sz0 4]
      (fun ω : PathΩ SizesInst.sz0 =>
        gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
          (fun _ => 4) 0 4 ω i j) :=
  gueH_adapted SizesInst.sz0 _ _ _ 0 4 i j
example : Measurable
    (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10)) (fun _ => 9 / 10)
      (fun _ => 4) 0 4) :=
  gueH_measurable SizesInst.sz0 _ _ _ 0 4
example :
    (Pgue SizesInst.sz0).map
        (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) 0 0) =
      (Sizes.seqP SizesInst.sz0).map
        (Sizes.seqHflow SizesInst.sz0 0 ((1 - ouZeta (1 / 20)) * (9 / 10))) :=
  map_gueH_zero SizesInst.sz0 _ _ _ 0 t1_pos
example :
    (Pgue SizesInst.sz0).map
        (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) 0 4) =
      (ouP (UNModel.band SizesInst.sz0) 0).map
        (fun ω => ((Real.sqrt (9 / 10) : ℝ) : ℂ) • ouMat (UNModel.band SizesInst.sz0) 0 (1 / 20) ω) :=
  map_gueH_last SizesInst.sz0 (fun _ => 9 / 10) (fun _ => 1 / 20) (fun _ => 4) 0
    (by norm_num) (by norm_num) (by norm_num)
example (n : ℕ) :
    (Pgue SizesInst.sz0).map
        (gueH SizesInst.sz0 (fun _ => (1 - ouZeta (1 / 20)) * (9 / 10))
          (fun _ => 9 / 10) (fun _ => 4) n 4) =
      (ouP (UNModel.band SizesInst.sz0) n).map
        (fun ω => ((Real.sqrt (9 / 10) : ℝ) : ℂ) •
          ouMat (UNModel.band SizesInst.sz0) n (1 / 20) ω) :=
  map_gueH_last SizesInst.sz0 (fun _ => 9 / 10) (fun _ => 1 / 20) (fun _ => 4) n
    (by norm_num) (by norm_num) (by norm_num)
example : IsProbabilityMeasure (Pgue SizesInst.sz0) := inferInstance
example : gueGridK SizesInst.sz0 0 0 ≠ 0 := gueGridK_ne_zero SizesInst.sz0 0 0
theorem gueGridK_size_le {d : ℕ} (sz : Sizes d) (n0 n : ℕ) :
    sz.size n + 1 ≤ gueGridK sz n0 n := by
  unfold gueGridK
  exact Nat.le_self_pow (by omega) _
example :
    loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
        Complex.I (loopOf ![true, false] ![(0 : Zd 3 3), 0]) =
      ((lemT Complex.I : ℝ) : ℂ) *
        loopL 3 3 2
          (((Real.sqrt (lemT Complex.I) : ℝ) : ℂ) •
            blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (zt (lemE Complex.I) (lemT Complex.I)) (loopOf ![true, false] ![(0 : Zd 3 3), 0]) :=
  GUEPhaseGrid_gloop_two_smul_lemT_eq _ (by simp) false 0 0
example :
    loopL 3 3 2 (blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
        Complex.I ⟨[true, false], [(0 : Zd 3 3), 0]⟩ =
      ((Real.sqrt (lemT Complex.I) : ℝ) : ℂ) ^ (([true, false] : List Bool).zip [(0 : Zd 3 3), 0]).length *
        loopL 3 3 2
          (((Real.sqrt (lemT Complex.I) : ℝ) : ℂ) •
            blockMat 3 3 2 (Matrix.diagonal fun _ : Idx 3 3 2 => (2 : ℂ)))
          (zt (lemE Complex.I) (lemT Complex.I)) ⟨[true, false], [(0 : Zd 3 3), 0]⟩ :=
  GUEPhaseGrid_gloop_smul_lemT_eq _ (by simp) _ _
end RBM.Univ.GUEPhase.GridCheck
```
**Pin examples** (scratch `T2316/pins.lean`: `import RBM3D.Universality.GUEPhase.Grid`, check-file lines 153-279 copied by `sed -n 153,279p`, then `example : T2316Check.<pin> := fun .. => <target> ..` for the 9 pins, 6 vocabulary `rfl`/`congrArg` examples, and `GUEPathBounds <-> LkV /\ LocalLawV`):
```
$ lake env lean T2316/pins.lean > pins.out 2>&1 ; echo "exit code $?" ; wc -c < pins.out ; grep -c "^example" T2316/pins.lean
exit code 0
0
16
```
**Registry pre-check** (`T2316/registry.lean` = `import RBM3D` / `import RBM3D.Universality.GUEPhase.Grid` / `#assert_rbm_axioms`, uncommitted):
```
$ lake env lean T2316/registry.lean > registry.out 2>&1 ; echo "exit code $?" ; grep -n "GUEPathBounds\|^premises found" registry.out
exit code 0
135:  RBM.Univ.GUEPhase.GUEPathBounds: 0 [no certificate]
150:premises found by scanning: 149 (borrowed 1, owed 90, structural 41, refuted 6, superseded 11).
$ git diff HEAD~1 HEAD -- RBM3D/Test/Axioms.lean | grep "^[+-][^+-]" | cut -c1-72
+   `RBM.Univ.GUEPhase.GUEPathBounds, -- output of the §7.2 random layer
```
**Consumer shapes** (scratch `T2316/consumers.lean`: `IsProbabilityMeasure (Pgue (sz.withLam 0))` by `inferInstance`; `map_gueH_last (sz.withLam 0) t0 τ K n h0 hτ hK` (BA step-0 carrier); `unfold gueH; rfl` to the two-summand body; `(gueUnit sz).map (fun ω => ω c) = gaussianReal 0 (gueUnitVar sz c)` by `unfold gueUnit; rw [Measure.infinitePi_map_eval]`; `gueUnitVar sz c = if c.2.1 = c.2.2.1 then 1 else 1 / 2 := rfl`):
```
$ lake env lean T2316/consumers.lean > consumers.out 2>&1 ; echo "exit code $?" ; wc -c < consumers.out
exit code 0
0
```
**Name-clash grep** (`git --no-optional-locks grep -nw -- <name> main -- RBM3D | grep -v GUEPhase/Grid.lean | wc -l` at main 66fd97e for each of the 19 public names, `GridCheck`, `T2316Check`, `t1_pos`, `gueGridK_size_le`):
```
names checked: 23, total hits: 0
```

**Port citation and statement comparison** (source: `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/GUEPhase/Grid.lean`, saved as `T2316/Grid2D.lean`; `stmtdiff.py` normalises the import map and the d >= 3 list (`d : Sizes -> sz`, `Z2 -> Zd d`, `BlockIndex -> Vtx d`, `gloop L W -> loopL d L W`, `spectralZ/M -> zt/mE`, `Coord/Xmat/Ω` get `d`) and compares declaration headers up to `:=`):
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/Grid.lean
9e0f275
 1 file changed, 24 insertions(+), 160 deletions(-)
$ python3 -I T2316/stmtdiff.py Grid2D.lean Grid.lean | grep "^source\|^---" | tr newline space
source decls 51 port decls 51 identical after normalization 41  GUEPathBounds  GUEFlow  loopG  GUEPhaseGrid_measurable_seqXmat  GUEPhaseGrid_measurable_swapEquiv  map_gueH_last  GUEPhaseGrid_Gsig_smul_mul  GUEPhaseGrid_gloopProd_smul_mul  GUEPhaseGrid_gloop_smul_mul  GUEPhaseGrid_spectralZ_eq  GUEPhaseGrid_inv_smul  GUEPhaseGrid_green_smul_mul  GUEPhaseGrid_Gres_eq_green  GUEPhaseGrid_Gres_smul_mul  GUEPhaseGrid_foldr_smul_mul  GUEPhaseGrid_loopL_smul_mul  GUEPhaseGrid_zt_eq 
```

**Narrative.**
- Delivered: the new file `RBM3D/Universality/GUEPhase/Grid.lean` (897 lines; one import, `RBM3D.Universality.ZeroModeProfile`; no `Induction.ConArgDet`, no `Induction.ConArg`) plus one registry line in `RBM3D/Test/Axioms.lean`; commit b163e85 on `t/T2316`; `git diff --stat main...t/T2316` lists exactly these two files. Vocabulary, the instances, `GUEPathBounds` (two fields `lk`, `localLaw`), the 8 target theorems are those of the ticket (statements as in the check file); each of the 9 pins of the check file is applied by an `example` (16 examples in `pins.lean`, exit 0, empty output).
- Source: RBM2D `c9a24cf:RBM2D/Universality/GUEPhase/Grid.lean:1-781` minus the dead `GUEFlow`, `loopG` (`:111-123`) and the unused private `GUEPhaseGrid_measurable_seqXmat`; the instance section `:783-862` is rewritten at `d = 3`. By `stmtdiff.py`, 41 of 51 declaration headers are identical after the import map; the other 10 are `GUEPathBounds` (`gloop` -> `loopL d`, `blockMat d`, `Loop.LoopIdx`), `map_gueH_last` (right side `ouP (UNModel.band sz) n`), `GUEPhaseGrid_measurable_swapEquiv` (a script artefact: the header is cut at `(d := d)` / `(sz := sz)`), the three dead/unported ones, and the homogeneity helpers (4 source lemmas -> 7 private lemmas: copies of `Induction/ConArg.lean:386,400,409,422,435` with `Gsig` -> `Gres`, `GUEPhaseGrid_zt_eq` for the source's `spectralZ_eq`, and `GUEPhaseGrid_Gres_eq_green`, which is not in the ticket's list).
- Proof changes: `Sizes.size_eq` does not exist (`size` is a `def`), so `hMpos` uses `Sizes.one_le_size`; `hsz` is `rfl` at `^ d`; `hunit` has the source text with `RBM.Univ.gueVar`; `hseq` is `rfl` through `seqGvar`, so the coupling `sz.lam n` meets itself in `ouVar d _ _ (sz.lam n)` and `gvarF d _ _ (sz.lam n)` and cancels (the two code occurrences, lines 626, 662); the file has no `3 ≤ d` and no condition on `sz.lam`. `GUEPhaseGrid_Gres_eq_green` unfolds `Gres`/`green` through `Matrix.nonsing_inv_eq_ringInverse` (the content of `Gres_eq_green_zSig`, without the import).
- I found no mistake in section (a) (no `(a')`); its homogeneity data (`d = 3, L = 3, W = 2, M = blockMat 3 3 2 (diagonal 2), z = i, sigma_2 = false, a = b = 0`) is the data of the `GridCheck` example, which applies the theorem.
- **Finding F1 (ticket text, DECISIONS §20).** The ticket's registry paragraph expected no line. The first registry pre-check (tool log, before the line was added) failed with (abridged): `axiom audit: 1 premise(s) that no theorem of this development proves are in none of borrowedProps, owedProps, structuralProps, refutedProps, supersededProps: [RBM.Univ.GUEPhase.GUEPathBounds]`. The scan reports a `Prop`-valued structure of the library even when no theorem takes it as a hypothesis. I added one line to `owedProps` (inserted after `RBM.Univ.UNNormBARow`, so no existing line changes); the pre-check then exits 0 and lists it with `0` theorems resting on it. The class is the §20 default "unsure: owed" (owner UN-33 `BoundsA`); the dispatcher confirms or changes it (structural would be the alternative).
- The port keeps both private `isProbabilityMeasure` instances of the source at `c9a24cf` (`GUEPhaseGrid_mixedRawStep_isProbabilityMeasure` `:265`, `GUEPhaseGrid_mixedStepMeasure_isProbabilityMeasure` `:274`); `GUEPhaseGrid_measurable_seqXmat` (`:174`) has no use in the source and is not ported.

## (c) Verified Mathlib names (all by the compile of the module)
- `MeasureTheory.Measure.infinitePi`, `.infinitePi_map_eval`, `.eq_infinitePi`, `.infinitePi_pi`, `.infinitePi_map_pi`, `.infinitePi_map_curry`, `.infinitePi_map_curry_symm`, `.infinitePi_map_piCongrLeft`; `ProbabilityTheory.iIndepFun_infinitePi`, `iIndepFun.indepFun_finsetSum_of_notMem`, `gaussianReal_map_const_mul`, `gaussianReal_add_gaussianReal_of_indepFun`, `gaussianReal_zero_var`; `MeasureTheory.HasLaw`.
- `MeasurableEquiv.curry`, `.piCongrLeft`, `.piCongrLeft_apply_apply`, `.coe_curry`, `.coe_curry_symm`; `Preorder.restrictLe`.
- `Matrix.inv_smul`, `Matrix.nonsing_inv_apply_not_isUnit`, `Matrix.nonsing_inv_eq_ringInverse`, `Matrix.det_smul`, `Matrix.trace_smul`, `Matrix.conjTranspose_sum`; `Real.sq_sqrt`, `Real.exp_le_one_iff`, `Real.sqrt_pos`.
- `if_true`, `if_false` are deprecated in this Mathlib (first build log: "Use `ite_true` instead"); the file uses `ite_true`, `ite_false`. No name was checked as absent.

## (d) Open issues and paper-delta candidates
- `T2316a` (bookkeeping, not a mathematical change): `N = (W L)^2 -> (W L)^d` in `gueH`, `gueScale`, `gueGridK` and in the variance identity of (7.26); the preflight (a) checked it numerically at `d = 3` with a wrong-exponent control.
- `T2316b` (Lean structure): the band coupling `sz.lam` enters the step-0 field (`seqGvar`) and `ouVar`, and cancels in (7.26); the GUE-phase flow is model-free beyond its initial field.
- `T2316c` (Lean structure): the OU carrier of (7.26) is `ouP (UNModel.band sz) n` on `SeqΩ sz × Ω d L W` (the merged `UNModel` form), bridged to the model-generic interface by `ouMatC_toC`.
- `T2316d` (Lean structure): `GUEFlow`, `loopG` not ported (dead in RBM2D).
- `GUEPathBounds` is not instantiated (its producer is UN-33, ticket); it has a registry line (F1).
