Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 21:57:23 UTC 2026

Scope: port of RBM2D `Universality/GUEPhase/DuhamelA.lean:1041-1985` (HEAD 9e0f275; `git -C ../RBM2D log -1` = 9e0f275). No paper statement is proved here: these are the device lemmas of the GUE-phase grid walk (paper: GUE phase of Thm 2.4, `paper/tex/1_2_Intro_model_result.tex:566-570`). Statements below: `N = sz.size n = (W L)^d`, `v = Δ/N`, `X = seqXmat sz n y`, `R = Φ(M+h) - Φ(M) - DΦ(M)[h]`, `h = √v X`, `Good = {y : ∀ i l, ‖X_il‖ ≤ N}`, `T = 1_Good R`, `B = ∫ 1_{Good^c} R dgueUnit`.

### (i) Exponent table

| # | Quantity | Value | Constraint / source | Slack |
|---|---|---|---|---|
| 1 | `N` (truncation threshold, `card Idx`) | `(W L)^d`; `d=2` source `(W L)²` | `card Idx = N` is `Sizes.card_Idx` (`Defs/Sizes.lean:160`) | exact |
| 2 | `‖T‖ ≤ (C₂/2) v N⁴` (src `:1484`) | `4 = 2·2`: `‖X‖ ≤ card(Idx)·N = N²`, then squared | needs `card Idx = N` and threshold `N` only (d-free once row 1 holds) | exact |
| 3 | `card Coord` (src `:1755`) | `2 N²` (`Coord = Idx×Idx×Bool`, `CoordF` abbrev, `Fintype.card_prod`) | script below: `2N² = |Idx|·|Idx|·2` | exact |
| 4 | tail threshold `N/4` (src `:1630-1645`) | `4` raw coordinates per entry (`|X_il| ≤ |a|+|b|+|c|+|e|`) | `|X_il| > N` ⇒ some raw coord `> N/4` | strict, slack 0 (all four `≤ N/4` ⇒ entry `≤ N`; contrapositive is strict) |
| 5 | `y² ≤ 2 e^{|y|}` and `2 e^{|y|}e^{|y'|-N/4} ≤ e^{-N/4} ψ` | `ψ = Σ_{±} e^{±2y_t}+e^{±2y_{t'}}` | `exp(2|x|) ≤ e^{2x}+e^{-2x}`, `2ab ≤ a²+b²` | exact |
| 6 | MGF of a unit-GUE coordinate at `c = ±2` | `E e^{c y} = e^{var c²/2} ≤ e^{2}`, `var ∈ {1, 1/2}` | `gueUnitVar ≤ 1` (def: `1` diag, `1/2` off) | factor `e^{2(1-var)} ≥ 1` slack (`var=1/2`: `e^{1}` vs `e^{2}`) |
| 7 | `E ψ ≤ 4e²`, `Σ_{t,t'} E ψ ≤ (2N²)²·4e² = 16 e² N⁴` | | row 3, 6; `‖X‖² ≤ Σ|X_ij|² ≤ 2 Σ_c y_c²` (each raw coord in ≤ 2 entries, d-free) | exact |
| 8 | `‖B‖ ≤ 16 e² C₂ v N⁴ e^{-N/4}` (src `:1709`) | `(C₂/2) v · 2 · e^{-N/4} · (2N²)²·4e²`, i.e. `(1/2)·2·4·4 = 16` times `e² C₂ v N⁴ e^{-N/4}` | `0 ≤ C₂` forced by `hC₂` at `M=0`, `y=E_{00}` | exact |
| 9 | `∫ DΦ[h] dgueUnit = 0`, integrable | Gaussian law of `linTr` (`gueMap_lin_Xmat`, `Markov.lean:298`, mean 0) | `Re Z = √v lin(A,X)`, `Im Z = √v lin(-iA,X)` (`gradMat`) | exact |
| 10 | `Δ`-exponent of drift remainder | `3/2`; constant `envConst d L W e m u_{k+1} = 16(m+3)⁴N⁴(1+η⁻¹)^{m+4}` (`OneStep.lean:78`) | passes unchanged from `condExp_loop_drift_gue` (`Drift.lean:1318`) | exact |
| 11 | time: `u_{k+1} = t₁+(k+1)Δ < 1` | `Δ=(t₀-t₁)/K`, `KΔ = t₀-t₁` | `0 ≤ Δ`, `k+1 ≤ K n`, `t₀ < 1` ⇒ `u_{k+1} ≤ t₀ < 1` | at instance: `1-t₀ = 0.1`, `1-u_1 = 0.1329` |
| 12 | `Im z₁ = (1-u_{k+1}) Im m(E) > 0` | `zt_im` (`Semicircle.lean:182`), `mE_im_pos` (`:56`, `|E|<2`) | replaces `spectralZ_im`, `spectralM_im_pos` | at instance `0.1329` |
| 13 | crude loop bound used only for boundedness of `F` | `(L W)^d (|Im z|⁻¹ (W^d)⁻¹)^{len}` (src `(L W)²(…W⁻¹²)`) | `norm_gloop_le_crude d L W` (`FlowCalculus.lean:708`), as `Drift.lean:1034-1038` | any finite bound suffices |

`d`-lines of source §5–§7 and replacement (all other lines: `d : Sizes`→`sz : Sizes d`, `d.L n`→`sz.L n`, `Idx (..)`→`Idx d (..)`, `gueUnit d`→`gueUnit sz`, `Pgue d`→`Pgue sz`, `Z2 L`→`Zd d L`, `BlockIndex L W`→`Vtx d L W`, `gloop L W (blockMat M)`→`loopL d L W (blockMat d L W M)`, `Gsig`/`green`→`Gres`, `spectralZ`→`zt`, `envConst L W`→`envConst d L W`, `genMatGUE L W`→`genMatGUE d L W`; no statement needs `3 ≤ d`):
- `:1069` truncation threshold `(W L)²`→`(W L)^d`; `:1445-1446` `Duhamel_card_Idx` (`simp [Idx,Z2,ZMod.card,pow_two]`)→ merged `Sizes.card_Idx sz n`, not re-proved; `:1492,1500-1505` `N⁴` d-free; `:1744-1759` `card Coord = 2N²` d-free (row 3).
- `:1418-1437` `Duhamel_measurable_loop`: `unfold gloop gloopProd`→`unfold loopL`; `Gsig/green` is `Ring.inverse (H - w•1)` (`Gres`, `GLoopFlow.lean:74`), measurable via `Matrix.nonsing_inv_eq_ringInverse` (used in source `:689`) and `Matrix.inv_def`.
- `:1883-1897` bound row 13; `:1905-1931` signature renames, `hz1ne` by rows 11-12.
- `Sizes.seqHflow sz n u y = (√u:ℂ) • seqXmat sz n y` is the RBM3D definition (`FineModel.lean:225-227`, `seqHflow_eq_smul` is `rfl`); the source's was `Hflow ∘ slice` via `Hflow_eq_realSmul`. Affects `Duhamel_Z_re_im` (`:1131`), `Duhamel_norm_R_le` (`:1283`), `Duhamel_measurable_R`: replace by the `ℂ`-smul = `ℝ`-smul conversion; no mathematical change.
- `Duhamel_gueH_succ` (`:1806`) is not ported: merged `gueH_succ sz t1 t0 K n k ω` (`Drift.lean:925`) is `gueH(k+1) = gueH k + (√(Δ/N):ℂ) • seqXmat (ω(k+1))`, which is `gueH k + seqHflow n (Δ/N) (ω(k+1))` by `rfl`.

Route for `Duhamel_contDiffAt_loop` (single use, src `:1890`; chain `:557-570, 673-717`): no public `C²` loop lemma exists. Grep of `ContDiffAt` in `RBM3D/` (non-Probe): the only loop versions are `private` (`Induction/LoopC2N.lean:313-372` takes `loopOf σ b`; `Path/StepDecompLoop.lean:339-371` is the two-loop `obs`); `Path/StepDecomp.lean`, `Universality/OUHessian.lean`, `Gauss/` have none for `loopL`. Decision: private chain `DuhamelA2_{blockCLM,trCLM,contDiffAt_green,contDiffAt_Gsig,contDiffAt_word,contDiffAt_loop}` for `I : LoopIdx (Zd d L)`, word `I.σ.zip I.a` (so `loopL` unfolds with no `loopOf`), copying `LoopC2N.lean:83-90, 116-120, 129-133, 313-372` (about 80 lines; `Gres` false case: `Gres H z false = Ring.inverse (H - conj z • 1)`, `conj z` has `Im ≠ 0`); public input `isUnit_sub_smul_of_isHermitian` (`Analysis/Resolvent.lean:132`).
Other merged-private items that must be re-copied (private in `Drift.lean`): `Drift_condExp_freezeC` (`:948`, uses public `gueCondExp_freeze`, `Markov.lean:109`), the `StandardBorelSpace` matrix instance (`:1190`), `Drift_herm*`/`Drift_Phi`/`Drift_continuous_Phi` (`:1002-1034`), `Drift_measurable_gueH_filt` (`:1196`, uses public `gueH_adapted`, `Grid.lean`); prefix `DuhamelA2_`.

Signatures vs source uses: `gueMap_lin_Xmat sz n A` (`Markov.lean:298`, `vGue sz n A : ℝ≥0`), `fderiv_eq_trace_gradMat M hX` (`StepDecomp.lean:123`), `HermTestFun sz n Φ` (fields `contDiffAt`, `bdd₀`, `StepDecomp.lean:186`), `condExp_loop_drift_gue sz t1 t0 K n k E hE hwf ht1 ht10 hK hk hu1` (same argument order as source's `condExp_loop_drift_gue d t1 t0 K n k e he hwf ht1 hst _ hk hu1lt`), `norm_gloop_le_crude d L W hH hη hz I hwf`: all consistent. The truncation event of `gue_highProb_incr_le` (`Markov.lean:863`) is the set `Good` entrywise at steps `k≥1`; no target uses `Tendsto`.

§29 items: (1) `0 ≤ t₁`, `t₁ ≤ t₀ < 1`, `k<K n` are hypotheses of the drift target, row 11; (2) n/a (no case (ii), no `lam`); (3) no `L^d ≤ W^K` used; (4) all targets are pointwise in `n` (`∀ n`, no `∀ᶠ n`), nothing imposed at small `n`; (5) n/a; (6) no `(eq:WO)`/`SizeTendsto`/`lam` lower bound used; `N ≥ 1` holds since `W,L ≥ 1`; (7) scale is `N = (W L)^d` throughout, matches `gueH`, `gueScale`. No external hypothesis occurs in any target, so no limit computation is owed.

### (ii) One concrete nondegenerate instance

Data: `GridCheck` of `Grid.lean:795-895`: `sz0 : Sizes 3`, `n = 0` (`L=4`, `W=32`, `N=2097152`), `t₀ = 9/10`, `t₁ = (1-ζ(1/20))·9/10 = e^{-1/20}·9/10`, `K = 4`, `k = 0`, `e = 0`, loop `(+,-;0,1)` (`I.WF` by `rfl`, labels `0 ≠ 1` in `Z_4^3`, as `DriftInst.labels_sz0`). Hypotheses of `Duhamel_drift_remainder_ae`: `|e|<2`, `I.WF`, `0 ≤ t₁ n`, `t₁ n ≤ t₀ n`, `t₀ n < 1`, `k < K n`, all hold; the measure `Pgue sz0` is a probability measure, so `∀ᵐ` is not vacuous. `Duhamel_measurableSet_good`: no hypothesis; at `sz0`, `n=0` the set `Good` contains `y=0` and excludes a `y` with `y⟨0,(i,i,true)⟩ = N+1`. For `Duhamel_norm_T_le`, `Duhamel_norm_B_le`, `Duhamel_integral_step`: `Φ A = sin(Re tr A)` (HermTestFun: `C²`, `|Φ| ≤ 1`; as `StepDecomp.lean:1413-1418`, private there) with `C₂ = ‖Re tr‖² = N²` (`y = 1` gives `(Re tr 1)² = N²`; `|tr y| ≤ N‖y‖` gives `≤`), `v = Δ/N`, `M = 0`. (The ticket pins instances for the first two only; this third is optional.)

Command (script in scratchpad, Python stdlib only): `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2346/inst2.py`
```
d,L,W,N = 3 4 32 2097152  N==2097152: True
t1,t0,Delta: 0.8561064820506427 0.9 0.010973379487339341
u_k, u_{k+1}: 0.8561064820506427 0.867079861537982  u_{k+1}<1: True  u_K==t0: True
Im zt(E,u_{k+1}) = 0.132920138462018
labels distinct: True  card Vtx=(L*W)^d = 2097152  Idx card = 2097152
card Coord = 2N^2 = 8796093022208 = |Idx|*|Idx|*2: True
envConst(m=2) = 7.416016822215481e+34  times Delta^(3/2) = 8.524743177064572e+31
T bound (C2/2) v N^4 = 2.225665774985257e+29
log10 of B bound 16 e^2 C2 v N^4 e^{-N/4} = -227663.66412920243
N/4 = 524288.0   (truncation tail e^{-N/4} nonvacuous: bound < 1: True )
(sumSq<=2 sum w^2, entries-good, notgood-bound): [(True, True, True), (True, True, True), (True, False, True), (True, False, True)]
c=2: exp(c^2/2)=e^2=7.389056; E psi <= 4e^2 = 29.556224
c=-2: exp(c^2/2)=e^2=7.389056; E psi <= 4e^2 = 29.556224
(2N^2)^2*4e^2 == 16 e^2 N^4 (N=27): True
```
The last three lines are a random check at toy size `N=27` (`Z_3^3`) of the `d`-free combinatorics (`Σ|X_ij|² ≤ 2Σ y_c²`; for `|X_35| = 28.3 > 27` the bound `Σ y² ≤ e^{-N/4} Σψ`); the instance numbers above are the exact `sz0` values (bounds `T`, `B`, `envConst` are exact, not witnesses).

### Verdicts
- `DuhamelGood`, `DuhamelZ`, `DuhamelR`, `DuhamelT`, `DuhamelB`, `Duhamel_measurableSet_good`, `Duhamel_Z_re_im`, `Duhamel_measurable_R`, `Duhamel_integral_step`, `Duhamel_measurable_loop`, `Duhamel_norm_T_le`, `Duhamel_norm_B_le`, `Duhamel_measurable_coord`, `Duhamel_gueH_measurable_filt`, `Duhamel_drift_remainder_ae`: PASS (every exponent closes exactly as at `d=2` once `card Idx = N = (W L)^d`; all hypotheses hold at the instance; no input missing).
- Note for 1b: the private `Duhamel_contDiffAt_loop` chain and the four private `Drift.lean` helpers must be re-derived (no public twin); the `seqHflow` smul form differs from the source (rows above).

## (b) Script output — Thu Oct  8 22:16:13 UTC 2026 (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2346, branch t/T2346)

$ lake build RBM3D.Universality.GUEPhase.DuhamelA2 2>&1 | tail -1;  ... | grep -c "DuhamelA2.lean"   # lines naming the module (warnings/errors)
Build completed successfully (3776 jobs).   0
$ lake build   # whole library as on the branch (root `RBM3D.lean` unchanged; the hub adds the import at merge)
Build completed successfully (4158 jobs).   EXIT=0
$ lake env lean registry.lean   # scratch outside the repo: import RBM3D / import RBM3D.Universality.GUEPhase.DuhamelA2 / #assert_rbm_axioms
axiom audit: 10399 theorems, 3064 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.   EXIT=0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/Universality/GUEPhase/DuhamelA2.lean   ->  0;   wc -l -> 1334 (stop rule: over 1500 at a section boundary)
$ git log --format="%h %s" main..t/T2346; git diff --stat main...t/T2346; git status --short | wc -l
a372a42 T2346: DuhamelA2 section 7 (grid, drift remainder) and compiled instances
e623813 T2346: DuhamelA2 sections 1-6 (one step, truncation bias, loop smoothness)
 RBM3D/Universality/GUEPhase/DuhamelA2.lean | 1334 ++++++++++++++++++++++++++++
 1 file changed, 1334 insertions(+)
       0
$ #print axioms (axioms.lean), the 15 targets and 11 instance theorems:  26 declarations, all [propext, Classical.choice, Quot.sound]: DuhamelGood, DuhamelZ, DuhamelR, DuhamelT, DuhamelB, Duhamel_measurableSet_good, Duhamel_Z_re_im, Duhamel_measurable_R, Duhamel_integral_step, Duhamel_measurable_loop, Duhamel_norm_T_le, Duhamel_norm_B_le, Duhamel_measurable_coord, Duhamel_gueH_measurable_filt, Duhamel_drift_remainder_ae, DuhamelA2Inst.measurableSet_good_check, DuhamelA2Inst.drift_remainder_ae_check, DuhamelA2Inst.labels_sz0, DuhamelA2Inst.Z_re_im_check, DuhamelA2Inst.measurable_R_check, DuhamelA2Inst.integral_step_check, DuhamelA2Inst.norm_T_le_check, DuhamelA2Inst.norm_B_le_check, DuhamelA2Inst.measurable_loop_check, DuhamelA2Inst.measurable_coord_check, DuhamelA2Inst.gueH_measurable_filt_check
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h;  git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/DuhamelA.lean | wc -l
9e0f275  0
(RBM1D not used.  Merged RBM3D copy source: RBM3D/Induction/LoopC2N.lean:313-372, last commit 14137ce)
$ name-clash grep -rnw <name> RBM3D/ (outside Probe/ and DuhamelA2.lean; plain -rn for the two prefixes):
DuhamelGood:0 DuhamelZ:0 DuhamelR:0 DuhamelT:0 DuhamelB:0 Duhamel_measurableSet_good:0 Duhamel_Z_re_im:0 Duhamel_measurable_R:0 Duhamel_integral_step:0 Duhamel_measurable_loop:0 Duhamel_norm_T_le:0 Duhamel_norm_B_le:0 Duhamel_measurable_coord:0 Duhamel_gueH_measurable_filt:0 Duhamel_drift_remainder_ae:0 DuhamelA2_:0 DuhamelA2Inst:0 
$ (a) citations re-checked by grep -n (line of the declaration): seqHflow 225 (FineModel), Sizes.card_Idx 160, gueH_succ 925, gueMap_lin_Xmat 298, fderiv_eq_trace_gradMat 123, HermTestFun 186, norm_gloop_le_crude 708, zt_im 182, mE_im_pos 56, gue_highProb_incr_le 863, isUnit_sub_smul_of_isHermitian 132, envConst 78, condExp_loop_drift_gue 1318: all as in (a)

### Target statements (stmt.py: declaration line to the first `:=`; defs to the blank line)
-- DuhamelA2.lean:166
def DuhamelGood : Set (Sizes.SeqΩ sz) :=
-- DuhamelA2.lean:170
def DuhamelZ (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
-- DuhamelA2.lean:175
def DuhamelR (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
-- DuhamelA2.lean:180
def DuhamelT (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (y : Sizes.SeqΩ sz) : ℂ :=
-- DuhamelA2.lean:185
def DuhamelB (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ) (v : ℝ)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℂ :=
-- DuhamelA2.lean:202
theorem Duhamel_measurableSet_good : MeasurableSet (DuhamelGood sz n) := by
-- DuhamelA2.lean:219
theorem Duhamel_Z_re_im (Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    {v : ℝ} (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (y : Sizes.SeqΩ sz) :
    (DuhamelZ sz n Φ v M y).re = Real.sqrt v * linTr n (gradMat Φ M) (Sizes.seqXmat sz n y) ∧
      (DuhamelZ sz n Φ v M y).im
        = Real.sqrt v * linTr n (-Complex.I • gradMat Φ M) (Sizes.seqXmat sz n y) := by
-- DuhamelA2.lean:408
theorem Duhamel_measurable_R
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ} (hΦm : Measurable Φ)
    (v : ℝ) :
    Measurable (fun p : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ ×
        Sizes.SeqΩ sz => DuhamelR sz n Φ v p.1 p.2) := by
-- DuhamelA2.lean:462
theorem Duhamel_integral_step
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (_hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    (v : ℝ) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) :
    ∫ y, Φ (M + Sizes.seqHflow sz n v y) ∂(gueUnit sz)
      = Φ M + ∫ y, DuhamelT sz n Φ v M y ∂(gueUnit sz) + DuhamelB sz n Φ v M := by
-- DuhamelA2.lean:523
theorem Duhamel_measurable_loop (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    Measurable (fun M : Matrix (Idx d L W) (Idx d L W) ℂ => loopL d L W (blockMat d L W M) z I) := by
-- DuhamelA2.lean:594
theorem Duhamel_norm_T_le
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) (y : Sizes.SeqΩ sz) :
    ‖DuhamelT sz n Φ v M y‖ ≤ C₂ / 2 * v * ((sz.size n : ℕ) : ℝ) ^ 4 := by
-- DuhamelA2.lean:818
theorem Duhamel_norm_B_le
    {Φ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : HermTestFun sz n Φ)
    {C₂ : ℝ} (hC₂ : ∀ M y : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → y.IsHermitian → ‖fderiv ℝ (fderiv ℝ Φ) M y y‖ ≤ C₂ * ‖y‖ ^ 2)
    {v : ℝ} (hv : 0 ≤ v) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : M.IsHermitian) :
    ‖DuhamelB sz n Φ v M‖ ≤ 16 * Real.exp 2 * C₂ * v * ((sz.size n : ℕ) : ℝ) ^ 4
      * Real.exp (-((sz.size n : ℕ) : ℝ) / 4) := by
-- DuhamelA2.lean:891
theorem Duhamel_measurable_coord {i k : ℕ} (h : i ≤ k) :
    Measurable[filt sz k] (fun ω : PathΩ sz => ω i) := by
-- DuhamelA2.lean:906
theorem Duhamel_gueH_measurable_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable[filt sz k] (gueH sz t1 t0 K n k) :=
-- DuhamelA2.lean:1008
theorem Duhamel_drift_remainder_ae (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (e : ℝ)
    (he : |e| < 2) {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) :
    ∀ᵐ ω ∂(Pgue sz),
      ‖(∫ y, loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω
              + Sizes.seqHflow sz n (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) y))
            (zt e (gridTime t1 t0 K n (k + 1))) I ∂(gueUnit sz))
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
              (zt e (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) *
              genMatGUE d (sz.L n) (sz.W n) e (gridTime t1 t0 K n k) (gueH sz t1 t0 K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) e I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by

### Translation table: RBM2D source statement -> RBM3D statement (trans.py: source text, whitespace-collapsed, rewritten by the port map, compared with ours)
Port map applied: `Idx (d.L n) (d.W n)`->`Idx d (sz.L n) (sz.W n)`; `Coord (..)`->`CoordF d (..)`; `d.size/L/W n`->`sz.size/L/W n`; `Sizes.{seqXmat,seqHflow,SeqΩ} d`->`.. sz`; `gueUnit/Pgue/PathΩ/HermTestFun/Duhamel* d`->`.. sz`; `filt d k`,`gueH d`->`sz`; `LoopIdx (Z2 L)`->`Loop.LoopIdx (Zd d L)`; `gloop L W (blockMat M)`->`loopL d L W (blockMat d L W M)`; `spectralZ`->`zt`; `envConst/genMatGUE (..)`->`.. d (..)`; binder `{d : Sizes}`->`{d : ℕ} {sz : Sizes d}` (`(d : Sizes)`->`(sz : Sizes d)`).
DuhamelGood: RBM2D DuhamelA.lean:1071 -> RBM3D DuhamelA2.lean:166 : EQUAL after port map
DuhamelZ: RBM2D DuhamelA.lean:1075 -> RBM3D DuhamelA2.lean:170 : EQUAL after port map
DuhamelR: RBM2D DuhamelA.lean:1080 -> RBM3D DuhamelA2.lean:175 : EQUAL after port map
DuhamelT: RBM2D DuhamelA.lean:1085 -> RBM3D DuhamelA2.lean:180 : EQUAL after port map
DuhamelB: RBM2D DuhamelA.lean:1090 -> RBM3D DuhamelA2.lean:185 : EQUAL after port map
Duhamel_measurableSet_good: RBM2D DuhamelA.lean:1106 -> RBM3D DuhamelA2.lean:202 : EQUAL after port map
Duhamel_Z_re_im: RBM2D DuhamelA.lean:1122 -> RBM3D DuhamelA2.lean:219 : EQUAL after port map
Duhamel_measurable_R: RBM2D DuhamelA.lean:1309 -> RBM3D DuhamelA2.lean:408 : EQUAL after port map
Duhamel_integral_step: RBM2D DuhamelA.lean:1360 -> RBM3D DuhamelA2.lean:462 : EQUAL after port map
Duhamel_measurable_loop: RBM2D DuhamelA.lean:1418 -> RBM3D DuhamelA2.lean:523 : EQUAL after port map
Duhamel_norm_T_le: RBM2D DuhamelA.lean:1486 -> RBM3D DuhamelA2.lean:594 : EQUAL after port map
Duhamel_norm_B_le: RBM2D DuhamelA.lean:1710 -> RBM3D DuhamelA2.lean:818 : EQUAL after port map
Duhamel_measurable_coord: RBM2D DuhamelA.lean:1783 -> RBM3D DuhamelA2.lean:891 : EQUAL after port map
Duhamel_gueH_measurable_filt: RBM2D DuhamelA.lean:1798 -> RBM3D DuhamelA2.lean:906 : EQUAL after port map
Duhamel_drift_remainder_ae: RBM2D DuhamelA.lean:1904 -> RBM3D DuhamelA2.lean:1008 : EQUAL after port map
15 of 15 equal after the port map
negative control (same script without the rule `d.size n`->`sz.size n`): `11 of 15 equal after the port map` (the 4 statements that use the threshold turn DIFF)

### Compiled nonempty instances (namespace RBM.Univ.GUEPhase.DuhamelA2Inst; collapse_full.py: statement and proof term, whitespace-collapsed; file line first)
data: sz0 (d=3, L_0=4, W_0=32, N=2097152), n=0; drift: t0=9/10, t1=(1-ouZeta(1/20))*9/10, K=4, k=0, e=0, loop (+,-;0,1) (labels differ: `labels_sz0`); others: Φ=sin(Re tr), C₂=‖Re tr‖², v=1/4, M=0
1137: measurableSet_good_check : MeasurableSet (DuhamelGood sz0 0) ∧ (0 : Sizes.SeqΩ sz0) ∈ DuhamelGood sz0 0 ∧ ∃ y : Sizes.SeqΩ sz0, y ∉ DuhamelGood sz0 0 := ⟨Duhamel_measurableSet_good, zero_mem_good, exists_not_mem_good⟩
1172: drift_remainder_ae_check : ∀ᵐ ω ∂(Pgue sz0), ‖(∫ y, loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 ω + Sizes.seqHflow sz0 0 (gridStep DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 / ((sz0.size 0 : ℕ) : ℝ)) y)) (zt 0 (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 (0 + 1))) (DuhamelA2Inst_loop2 (sz0.L 0) 0 1) ∂(gueUnit sz0)) - loopL 3 (sz0.L 0) (sz0.W 0) (blockMat 3 (sz0.L 0) (sz0.W 0) (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 ω)) (zt 0 (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0)) (DuhamelA2Inst_loop2 (sz0.L 0) 0 1) - (gridStep DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 : ℂ) * genMatGUE 3 (sz0.L 0) (sz0.W 0) 0 (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0) (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 ω) (DuhamelA2Inst_loop2 (sz0.L 0) 0 1)‖ ≤ envConst 3 (sz0.L 0) (sz0.W 0) 0 (DuhamelA2Inst_loop2 (sz0.L 0) 0 1).length (gridTime DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 (0 + 1)) * gridStep DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 ^ ((3 : ℝ) / 2) := Duhamel_drift_remainder_ae sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 0 0 (by norm_num) (DuhamelA2Inst_loop2_wf _ 0 1) DuhamelA2Inst_t1_nonneg DuhamelA2Inst_t1_le_t0 (by norm_num [DuhamelA2Inst_t0]) (by norm_num [DuhamelA2Inst_K])
1269: Z_re_im_check (y : Sizes.SeqΩ sz0) : (DuhamelZ sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y).re = Real.sqrt (1 / 4) * linTr 0 (gradMat (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) 0) (Sizes.seqXmat sz0 0 y) ∧ (DuhamelZ sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y).im = Real.sqrt (1 / 4) * linTr 0 (-Complex.I • gradMat (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) 0) (Sizes.seqXmat sz0 0 y) := Duhamel_Z_re_im _ 0 y
1280: measurable_R_check : Measurable (fun p : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ × Sizes.SeqΩ sz0 => DuhamelR sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) p.1 p.2) := Duhamel_measurable_R (by exact (DuhamelA2Inst_continuous_Φ _).measurable) (1 / 4)
1288: integral_step_check : ∫ y, DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0)) (0 + Sizes.seqHflow sz0 0 (1 / 4) y) ∂(gueUnit sz0) = DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0)) 0 + ∫ y, DuhamelT sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y ∂(gueUnit sz0) + DuhamelB sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 := Duhamel_integral_step (DuhamelA2Inst_class 0 sz0) (C₂ := ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2) (fun M y _ _ => DuhamelA2Inst_hC₂ M y) (1 / 4) Matrix.isHermitian_zero
1299: norm_T_le_check (y : Sizes.SeqΩ sz0) : ‖DuhamelT sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0 y‖ ≤ ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2 / 2 * (1 / 4) * ((sz0.size 0 : ℕ) : ℝ) ^ 4 := Duhamel_norm_T_le (DuhamelA2Inst_class 0 sz0) (C₂ := ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2) (fun M y _ _ => DuhamelA2Inst_hC₂ M y) (by norm_num) Matrix.isHermitian_zero y
1308: norm_B_le_check : ‖DuhamelB sz0 0 (DuhamelA2Inst_Φ (Idx 3 (sz0.L 0) (sz0.W 0))) (1 / 4) 0‖ ≤ 16 * Real.exp 2 * ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2 * (1 / 4) * ((sz0.size 0 : ℕ) : ℝ) ^ 4 * Real.exp (-((sz0.size 0 : ℕ) : ℝ) / 4) := Duhamel_norm_B_le (DuhamelA2Inst_class 0 sz0) (C₂ := ‖DuhamelA2Inst_g (Idx 3 (sz0.L 0) (sz0.W 0))‖ ^ 2) (fun M y _ _ => DuhamelA2Inst_hC₂ M y) (by norm_num) Matrix.isHermitian_zero
1317: measurable_loop_check : Measurable (fun M : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ => loopL 3 2 2 (blockMat 3 2 2 M) Complex.I ⟨[true, false], [(0 : Zd 3 2), 1]⟩) := Duhamel_measurable_loop Complex.I ⟨[true, false], [(0 : Zd 3 2), 1]⟩
1323: measurable_coord_check : Measurable[filt sz0 1] (fun ω : PathΩ sz0 => ω 0) := Duhamel_measurable_coord sz0 (by norm_num)
1327: gueH_measurable_filt_check : Measurable[filt sz0 4] (gueH sz0 DuhamelA2Inst_t1 DuhamelA2Inst_t0 DuhamelA2Inst_K 0 4) := Duhamel_gueH_measurable_filt sz0 _ _ _ 0 4
1115: theorem zero_mem_good : (0 : Sizes.SeqΩ sz0) ∈ DuhamelGood sz0 0;   1123: theorem exists_not_mem_good : ∃ y : Sizes.SeqΩ sz0, y ∉ DuhamelGood sz0 0   (the set is neither empty nor full)

### Narrative
1. All fifteen targets are in the one new file `RBM3D/Universality/GUEPhase/DuhamelA2.lean` (1334 lines, the only file on the branch). Two section commits: e623813 at `wc -l` 883 (sections 1-6) and a372a42 at `wc -l` 1334 (section 7 and the instances); the stop size 1500 was not reached.
2. Source: RBM2D `DuhamelA.lean:1041-1985` at 9e0f275 (the source file did not change: `diff --stat 9e0f275 HEAD` is empty). Proofs are the source's with the ticket's port map (rename list in the module docstring); the departures are listed in 3 and 4.
3. Proof-level departures (statements unchanged: 15 of 15 equal after the port map, with a negative control):
   a. `Sizes.seqHflow sz n v y` is `(√v : ℂ) • seqXmat sz n y` (a definition), so `Duhamel_Z_re_im`, `DuhamelA2_norm_R_le`, `Duhamel_measurable_R` rewrite with `Sizes.seqHflow_eq_smul, Complex.coe_smul` instead of `Hflow_eq_realSmul`.
   b. `Duhamel_card_Idx` is the merged `Sizes.card_Idx` (`Duhamel_norm_T_le`, `Duhamel_norm_B_le`); `card CoordF = 2 N^2` by `Fintype.card_prod`, as in the source.
   c. `Duhamel_measurable_loop`: `Gres H z σ = Ring.inverse (H - w • 1)` is rewritten to `(H - w • 1)⁻¹` with `Matrix.nonsing_inv_eq_ringInverse`; `loopL` is unfolded instead of `gloop`/`gloopProd`.
   d. `Duhamel_drift_remainder_ae`: `hz1ne` from `zt_im`, `mE_im_pos`; the one-step recursion is the merged `gueH_succ` (`Duhamel_gueH_succ` is not ported); `condExp_loop_drift_gue sz .. (by omega) hk hu1lt` gets `K n ≠ 0` from `k < K n`.
4. `Duhamel_contDiffAt_loop` (the one use of source §1-§4) is the private chain `DuhamelA2_{blockCLM,trCLM,contDiffAt_Gres,contDiffAt_Gsig,contDiffAt_word,contDiffAt_loop}` for a list-based `Loop.LoopIdx` (copy of `LoopC2N.lean:313-372`, word `I.σ.zip I.a`); nothing of T2345 is imported. Other private copies (private in `Drift.lean`): `DuhamelA2_condExp_freezeC`, `DuhamelA2_standardBorelMatrix`, `DuhamelA2_herm*`, `DuhamelA2_Phi`, `DuhamelA2_continuous_Phi`, `DuhamelA2_norm_Phi_le`.
5. `d`-lines: the truncation threshold `sz.size n = (W L)^d` (`DuhamelGood`, `Duhamel_norm_T_le`, `Duhamel_norm_B_le`) and the crude bound `(L W)^d (|Im z|⁻¹ (W^d)⁻¹)^len` (`DuhamelA2_norm_Phi_le`). No statement uses `3 ≤ d`; no hypothesis was added, weakened or moved; no frozen or pinned signature was changed.
6. Instances: every one of the fifteen targets has a compiled application (the ticket pins two: `measurableSet_good_check`, `drift_remainder_ae_check`). Deterministic hypotheses are all discharged (`|e|<2`, `I.WF`, `0 ≤ t1`, `t1 ≤ t0`, `t0 < 1`, `k < K` in the drift instance; `hΦ`, `hC₂`, `hv`, `hM` in the other three). The observable is `sin (Re tr)` (copy of the private `StepDecomp_check_*`).
7. Section (a) was not edited and no (a′) section is needed: the citations listed in (b) above hold.

## (c) Verified Mathlib names (module of the declaration; `#where` script over the compiled environment, `where.lean`)
Analysis.Calculus.ContDiff.Operations: contDiffAt_ringInverse
LinearAlgebra.Matrix.NonsingularInverse: Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_def
Algebra.GroupWithZero.Units.Basic: Ring.inverse_eq_inv'
Topology.Instances.Matrix: Continuous.matrix_det, Continuous.matrix_adjugate, Continuous.matrix_trace, Continuous.matrix_submatrix, Continuous.matrix_conjTranspose
LinearAlgebra.Complex.Module: Complex.coe_smul
Basic.Complex.Basic: Complex.re_ofReal_mul, Complex.im_ofReal_mul
Analysis.Calculus.FDeriv.Measurable: measurable_fderiv_apply_const
MeasureTheory.Function.ConditionalExpectation.Basic: ContinuousLinearMap.comp_condExp_comm
Analysis.Calculus.MeanValue: norm_image_sub_le_of_norm_deriv_right_le_segment, image_norm_le_of_norm_deriv_right_le_deriv_boundary
Analysis.Complex.Exponential: Real.quadratic_le_exp_of_nonneg
Probability.Distributions.Gaussian.Real: ProbabilityTheory.integrable_exp_mul_gaussianReal, ProbabilityTheory.mgf_gaussianReal, ProbabilityTheory.integral_id_gaussianReal, ProbabilityTheory.memLp_id_gaussianReal
Probability.ProductMeasure: MeasureTheory.Measure.infinitePi_map_eval
Order.Restriction: Preorder.restrictLe
MeasureTheory.MeasurableSpace.Basic: comap_measurable
Algebra.Group.Indicator: Set.indicator_self_add_compl_apply
Algebra.Order.BigOperators.Ring.Finset: Finset.sum_mul_sq_le_sq_mul_sq
Analysis.CStarAlgebra.Matrix: Matrix.cstar_norm_def, Matrix.ofLp_toEuclideanCLM
MeasureTheory.Function.LpSeminorm.Basic: MeasureTheory.memLp_top_of_bound
Data.Set.Operations: Set.mem_ofPred_eq
LinearAlgebra.Matrix.Hermitian: Matrix.isHermitian_zero, Matrix.isHermitian_add_transpose_self
Names verified absent: `isSelfAdjoint_add_transpose_self` (not in the environment; used `Matrix.isHermitian_add_transpose_self`); `integrable_exp_mul_gaussianReal` at root (only `ProbabilityTheory.integrable_exp_mul_gaussianReal` exists).

## (d) Open issues and paper-delta candidates
- No open issue; no external hypothesis occurs in any target, so no limit check is owed.
- Paper-delta candidates: none (`T2346a` not used). The fifteen declarations are device lemmas of the GUE-phase grid walk with no paper statement; each is the RBM2D statement under the port map, with the truncation scale `N = (W L)^d`.
- Follow-up (not required by the ticket): once T2345 merges, `DuhamelA2_contDiffAt_loop` could be replaced by the public `Duhamel_contDiffAt_loop` of `DuhamelA1`.
