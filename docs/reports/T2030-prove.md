Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 05:38:26 UTC 2026

Sources read: ticket T2030; `docs/tickets/ST1-COMMON.md`; RBM2D `c9a24cf` (the ten files, `Gauss/MomentTimeCont`, `Gauss/LoopMomentCont`) and `0c1330a` ("kept" text); `RBM3D/Loop/GLoopFlow.lean`, `RBM3D/Gauss/{FineModel,Model}.lean`, `RBM3D/Defs/{Semicircle,Sizes}.lean`, `RBM3D/Analysis/Resolvent.lean`.

### (i) Exponent table

Dimension-free files (no `d`, `W`, `L` enters the statement or proof; `E`, `u`, `z`, `H` and the matrix index type are generic): SpectralAlgebra, SpectralDerivative, FlowTimeCont, GreenTimeCont, GreenDerivative, and the spectral-path part of SpectralWindow. Only index-type renaming R1-R4 applies there. The portmap lists no `W2/L2/N2/inv2/d=2/scal/1/5` token for them (P.1 rows 1, 3, 4, 24, 25 show `-`).

| # | Constant / statement (RBM2D `c9a24cf` file:line) | d = 2 value | d = 3 value (this port) | Constraint | Slack at the instance (E=0.5, u=0.5, s=0.2, t=0.6, n=3, d=3, W=2, L=3) |
|---|---|---|---|---|---|
| 1 | `card (BlockIndex L W)`, LoopEnvelope:92 `card_BlockIndex` (`Vtx d L W = Zd d L × Fin (W^d)`) | `(L*W)^2` | `(L*W)^d` | equals `Fintype.card (Idx d L W) = (W*L)^d = N` | 216 = 216 (d=2 formula would give 36) |
| 2 | `‖Eblk a‖`, LoopEnvelope:45 `norm_Eblk_le_inv_W_sq` | `(W⁻¹)^2` | `((W:ℝ)^d)⁻¹` | `‖E_a‖ ≤ W^{-d}` (`Eblk_apply`: diagonal entries `(W^d)⁻¹` on the block) | 1/8 = 1/8 (equality) |
| 3 | per-edge factor, LoopEnvelope:65, :97 | `η⁻¹ (W⁻¹)^2` | `η⁻¹ ((W:ℝ)^d)⁻¹` | `‖G(σ)‖ ≤ η⁻¹` for `η ≤ |Im z|`, times row 2 | 1/(0.3873·8) = 0.3227 |
| 4 | crude loop envelope, LoopEnvelope:97 `norm_gloop_le_crude` and :120 `norm_gloop_HflowBlock_le_crude_on_Icc` | `(LW)^2 (η⁻¹ W⁻²)^n` | `(LW)^d (η⁻¹ W^{-d})^n` (card × per-edge^n; trace ≤ card·opNorm) | `‖loop‖ ≤` this for all `n ≥ 0`, WF, `η ≤ |Im z|`, every sample | measured max 1.5e-2 ≤ 7.26 |
| 5 | merged sharp envelope `norm_gloop_le_sharp` (GLoopFlow:866), `n ≥ 1` | — | `η^{-n} (W^{-d})^{n-1}` | crude/sharp = `(LW)^d W^{-d} = L^d` (algebra) | 0.2690 ≤ 7.262, ratio 27 = 3^3 |
| 6 | spectral gap, SpectralWindow:44 `spectralZ_im_gap`, :51 | same | same | `t < 1`, `|E| < 2` (or `|E| ≤ 2-κ`, `κ>0`); gap `(1-t) Im m ≤ |Im z_u|` on `[s,t]` | `1-t = 0.4`, `Im m = 0.9682`, gap 0.3873 > 0 |
| 7 | `|m(E)| = 1`, `m(m+E) = -1`, SpectralAlgebra:27, :43 | same | same (merged `mE_mul`, `norm_mE` carry `|E| ≤ 2`) | `|E| ≤ 2` | `|E| = 0.5`, slack 1.5 |
| 8 | Green derivative, GreenDerivative:82 and LoopDerivative:114 | same | same (Leibniz sum, trace is continuous linear) | `|E| < 2`, `0 < u < 1` (`√u` differentiable only for `u > 0`; `Im z_u ≠ 0` only for `u < 1`) | `u = 0.5`: slack 0.5 on each side |
| 9 | samplewise time/sample continuity (FlowTimeCont, GreenTimeCont, LoopTimeCont, LoopSampleCont) | same | same | `Im z ≠ 0` only; `√·` is continuous at 0, so `u = 0` is allowed; `Hflow` has no `g` (g enters only `PF d L W g`) | none needed |
| 10 | Gaussian moment continuity, SpectralWindow:64 (via LoopMomentCont:26, :51 + MomentTimeCont:26, dominated convergence) | `P L W` | `PF d L W g` (probability measure) | window `s ≤ t < 1`, `|E| ≤ 2-κ`, envelope row 4 constant `C`, `q : ℕ` | `C = 7.26` finite for fixed `d, L, W` |

Dimension roles: `W^d` = block size and `L^d` = number of blocks, entering only rows 1-5 (and `N = (WL)^d = card Idx`). `Zd d L`/`Idx d L W` replace `Z2 L`/`Idx L W` (R2). Merged `Vtx d L W = Zd d L × Fin (W^d)` plays the role of `BlockIndex L W`; `blockMat d L W (Hflow d L W u ω)` equals RBM2D's `HflowBlock L W u ω` (`GLoopFlow:105`).

`d = 2` token accounting (portmap P.1 rows 9, 10, 21, 23, 26) against the `c9a24cf` text (grep in the tool log):
- LoopEnvelope, `W^2`/`W⁻²` (rows 2, 3, 4): `(W:ℝ)⁻¹ ^ 2` at lines 46, 70, 82, 83, 87, 88, 102, 111, 114, 126 become `((W:ℝ)^d)⁻¹`. `(L*W)^2` at lines 92, 101, 113, 125 becomes `(L*W)^d`. `pow_two` and `Z2` at line 93 (`simp [BlockIndex, Z2, pow_two]`) are replaced by `Fintype.card_prod`, `ZMod.card`, `Fintype.card_fin`, `mul_pow`.
- `Z2 L` becomes `Zd d L` at SpectralWindow:68, LoopTimeCont:64, 77, 90, LoopSampleCont:47, 59, 65, 72, LoopDerivative:64, 76, 107, 116, LoopEnvelope:45, 67, 99, 122. Examples with `Z2 3`, `Z2 1`, `Idx 3 1`, `BlockIndex 1 1` (L = 1 is a single-block collapsed index) must be re-instanced at `d = 3`, `L = 3`, `W = 2` (or `sz0`), not copied.
- FlowTimeCont etc.: no token; `Sizes d` becomes `Sizes d` with `sz : Sizes d`; `seqHflow` is `Hflow ∘ slice` and merged `Sizes.seqHflow` is that definition (`FineModel:225`).
- Name bridge (merged vocabulary differs from RBM2D in form): RBM2D `Gsig H z σ` is the merged `Gres H z σ`; RBM2D `gloop L W H z I` is the merged `loopL d L W H z I`; the merged `Gsig`/`gloop` (GLoop.lean, arguments `ω E t`) are different objects; RBM2D `green H z` has no merged counterpart (merged `Gres` uses `Ring.inverse`; invertibility is `Resolvent.isUnit_sub_smul_of_isHermitian`, entry bound `norm_inverse_entry_le`). RBM2D `Envelope:47/116` (`isUnit_sub_smul_one_of_im_ne_zero`, `norm_green_le`) must therefore be bridged to these.
- `spectralM E` has the same formula as merged `mE E` (`Semicircle:38`), `spectralZ E u` the same as `zt E u` (`Semicircle:179`), `spectralZ_im` is `zt_im` (`:182`), `spectralM_im`/`spectralM_im_pos`/`spectralM_mul`/`norm_spectralM` are `mE_im`/`mE_im_pos`/`mE_mul`/`norm_mE`. Not in Semicircle: `spectralM_sqrt_sq`, `spectralM_quadratic`, `continuous_spectralZ`, `spectralZ_im_gap`, `spectralZ_window_gap_of_bulk`.

Finding F1 (key-statement status, from the tool log): at `0c1330a` (kept text) the following statements named in the ticket's key list are deleted dead code: SpectralWindow:51 and :64 (`spectralZ_window_gap_of_bulk`, `continuousOn_integral_norm_gloop_pow_spectralZ`), LoopEnvelope:120, SpectralDerivative:33, FlowTimeCont:29, 35, 47, 53, GreenTimeCont:74, 88, LoopTimeCont:88, 96, and the examples. `git grep` at `0c1330a` finds no user of `continuousOn_integral_norm_gloop_pow`, `spectralZ_window_gap_of_bulk`, `norm_gloop_HflowBlock_le_crude_on_Icc`, `hasDerivAt_spectralZ_im`, `continuous_seqHflow_entry_time`, `continuous_gloop_Hflow_time`. The portmap P.3 marks all of them unreferenced by ST-2..ST-6. `continuousOn_integral_norm_gloop_pow_spectralZ` imports `LoopMomentCont` (85 lines at `c9a24cf`; theorems `continuousOn_gloop_HflowBlock_window` :26, `continuousOn_integral_norm_gloop_pow` :51) and `MomentTimeCont` (78 lines; `continuousOn_integral_abs_pow_of_envelope` :26): both are outside the ticket's ten files and outside the P.1 inventory (no ticket owns them). Mathematically the statement closes (dominated convergence with the row-4 constant, measurability from `continuous_gloop..._sample`, continuity from the window clamp); porting it needs those two sources copied as `private` helpers (about 25 + 50 + 20 proof lines, dimension-free), or dropping it with a stated reason. Everything else the portmap marks used (28 declarations of P.3 for S1-01) must be ported.

### (ii) One concrete nondegenerate instance and script

Data: `d = 3`, `W = 2`, `L = 3`, `N = (WL)^3 = 216`, 27 blocks of 8 sites, `g = 1`, `E = 0.5` (so `|E| = 0.5 < 2`), derivative time `u = 0.5` in `(0,1)`, window `[s,t] = [0.2, 0.6]`, `t < 1`, loop of length `n = 3` with `σ = (+,-,+)` and the same nonzero block `a` three times (`WF`: equal lengths, nonempty), `X` a Hermitian sample with the block variance profile `S_xy = W^{-d} S^B_ab` (`svarF`, merged `Defs`/`FineModel`). Checked: card = `(LW)^d`; `|m| = 1` and `m(m+E) = -1`; `‖E_a‖ = W^{-d}`; envelope rows 3-5 on the whole window; and the Leibniz derivative `d/du tr ∏ G(σ_i)E_{a_i}` (row 8, from `hasDerivAt_gloop_HflowBlock_spectralZ`, `H_u = √u X`, `z_u = E + (1-u) m`, `dG(σ) = -G (X/(2√u) + m_σ) G`) against a central finite difference.

Command (python3 with numpy 2.0.2; the script is mathematics only, no Lean):
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/chk.py`

Output (verbatim):
```
N=(WL)^d = 216 ; card Vtx = L^d*W^d = 216 ; blocks L^d = 27 ; |block| = 8 = W^d = 8
row sum of S: 0.9999999999999999
|m|= 1.0  m(m+E)= (-1+0j)
||E_a|| = 0.125  W^{-d} = 0.125  (d=2 value W^-2 = 0.25 )
eta=(1-t)Im m= 0.3872983346207417
max_u |loop| on [0.2,0.6] = 0.015138764207649522
sharp (eta^-n W^{-d(n-1)}) = 0.2689571768199595   crude (LW)^d (eta^-1 W^-d)^n = 7.261843774138907
max<=sharp: True   sharp<=crude: True
d/du loop (finite diff) = (-0.0009905905592327846+0.0002819846465704212j)  trace(loopWordDeriv) = (-0.0009905905604787185+0.00028198464827452227j)  rel.err = 2.0496235210573823e-09
hypotheses: |E|=0.5<2, 0<u=0.5<1, s=0.2<=t=0.6<1, eta>0, n=3, WF equal lengths, L>=3, d>=3
```
Hypotheses of all targets hold together at this data (`η = 0.3873 > 0`, window nonempty `0.2 < 0.6`, `u` interior, `|E| < 2`, `n = 3` with WF index, `N = 216`, no collapsed block); the crude/sharp ratio `7.2618/0.26896 = 27 = L^d` agrees with row 5. No external hypothesis is introduced by this ticket (all targets are deterministic; the Gaussian moment statement uses only the probability measure `PF d L W g`), so no limit computation is needed.

### Verdicts
- Targets in the dimension-free files (SpectralWindow spectral part, SpectralAlgebra, SpectralDerivative, FlowTimeCont, GreenTimeCont, LoopTimeCont, LoopSampleCont, GreenDerivative, LoopDerivative): PASS.
- LoopEnvelope (rows 1-4, exponent change `2 -> d` in `W^{-2}` and `(LW)^2`): PASS; `norm_gloop_HflowBlock_le_crude_on_Icc` is stated with `(LW)^d (η⁻¹ W^{-d})^n`.
- `continuousOn_integral_norm_gloop_pow_spectralZ`: PASS as mathematics; needs two out-of-list private helper copies (finding F1) or an explicit drop.

Overall verdict: PASS.

## (b) Script output — Sat Oct  3 05:48:15 UTC 2026

### b.1 Build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2030, branch t/T2030, commit 9894147)
```
$ lake build RBM3D.Gauss.FlowCalculus 2>&1 | tail -3
Build completed successfully (3296 jobs).
$ lake build 2>&1 | tail -1     # full library (root RBM3D.lean does not yet import the module; the hub adds the import)
Build completed successfully (3728 jobs).
$ lake env lean root.lean   # import RBM3D; import RBM3D.Gauss.FlowCalculus; #assert_rbm_axioms   -> error lines:
0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Gauss/FlowCalculus.lean | wc -l
       0
$ git diff --stat main...t/T2030
 RBM3D/Gauss/FlowCalculus.lean | 962 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 962 insertions(+)
```

### b.2 Axioms of every public declaration of the file (56: 52 theorems, 4 defs)
```
$ lake env lean ax.lean   # `#print axioms` for each of the 56 public names (list: grep of theorem/def lines)
  56 depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Target statements (extracted from the file by script; `d L W : ℕ` `[NeZero L] [NeZero W]` and `g` come from `variable`s)
```
theorem continuousOn_integral_norm_gloop_pow_spectralZ (g : ℝ) {E κ s t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hst : s ≤ t) (ht : t < 1) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) (q : ℕ) : ContinuousOn (fun u : ℝ => ∫ ω : Ω d L W, ‖loopL d L W (HflowBlock d L W u ω) (zt E u) I‖ ^ q ∂(PF d L W g)) (Set.Icc s t)

theorem norm_spectralM {E : ℝ} (hE : |E| ≤ 2) : ‖mE E‖ = 1

theorem hasDerivAt_spectralZ_im (E u : ℝ) : HasDerivAt (fun v : ℝ => (zt E v).im) (-(mE E).im) u

theorem continuous_seqHflow_entry_time (n : ℕ) (ω : SeqΩ sz) (i j : Idx d (sz.L n) (sz.W n)) : Continuous fun u : ℝ => seqHflow sz n u ω i j

theorem hasDerivAt_green_HflowBlock_spectralZ (ω : Ω d L W) {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) : HasDerivAt (fun v : ℝ => Gres (HflowBlock d L W v ω) (zt E v) true) (-(Gres (HflowBlock d L W u ω) (zt E u) true * ((1 / (2 * Real.sqrt u)) • blockMat d L W (Xmat d L W ω) + mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Gres (HflowBlock d L W u ω) (zt E u) true)) u

theorem hasDerivAt_gloop_HflowBlock_spectralZ (ω : Ω d L W) {E u : ℝ} (hE : |E| < 2) (hu : 0 < u) (hu1 : u < 1) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) : HasDerivAt (fun v : ℝ => loopL d L W (HflowBlock d L W v ω) (zt E v) I) (Matrix.trace (loopWordDeriv d L W ω E u (I.σ.zip I.a))) u

theorem norm_gloop_HflowBlock_le_crude_on_Icc [NeZero W] {s t η : ℝ} (hη : 0 < η) {z : ℝ → ℂ} (hz : ∀ u ∈ Set.Icc s t, η ≤ |(z u).im|) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) : ∀ u ∈ Set.Icc s t, ∀ ω : Ω d L W, ‖loopL d L W (HflowBlock d L W u ω) (z u) I‖ ≤ (((L * W) ^ d : ℕ) : ℝ) * (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ I.a.length

theorem continuous_green_of_isHermitian_moving {V : Type*} [TopologicalSpace V] {f : V → Matrix n n ℂ} (hf : Continuous f) (hherm : ∀ v, (f v).IsHermitian) {z : V → ℂ} (hzcont : Continuous z) (hzim : ∀ v, (z v).im ≠ 0) : Continuous fun v => Gres (f v) (z v) true

theorem continuous_gloop_Hflow_time (ω : Ω d L W) {z : ℝ → ℂ} (hzcont : Continuous z) (hzim : ∀ u, (z u).im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (_hwf : I.WF) : Continuous fun u : ℝ => loopL d L W (HflowBlock d L W u ω) (z u) I

theorem measurable_gloop_HflowBlock_sample (u : ℝ) {z : ℂ} (hz : z.im ≠ 0) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF) : Measurable fun ω : Ω d L W => loopL d L W (HflowBlock d L W u ω) z I

```

### b.4 Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`; docstrings stripped by script; every deterministic hypothesis discharged; section 6 of the file, lines 857-962)
```
/-! ## 6. Compiled nonempty instances (`d = 3`, `L = 3`, `W = 2`, `N = (W L)^d = 216`) -/

section Instances

private def flowCalculusLoop : Loop.LoopIdx (Zd 3 3) :=
  ⟨[true, false, true], [![1, 0, 2], ![0, 1, 0], ![2, 2, 1]]⟩

private theorem flowCalculusLoop_wf : flowCalculusLoop.WF := rfl

example : |(1 / 2 : ℝ)| < 2 ∧ ‖mE (1 / 2)‖ = 1 ∧ 0 < (mE (1 / 2)).im ∧
    HasDerivAt (fun v : ℝ => (zt (1 / 2) v).im) (-(mE (1 / 2)).im) (1 / 2) ∧
    HasDerivAt (zt (1 / 2)) (-(mE (1 / 2))) (1 / 2) ∧
    (mE (1 / 2)) ^ 2 + ((1 / 2 : ℝ) : ℂ) * mE (1 / 2) + 1 = 0 :=
  have h2 : |(1 / 2 : ℝ)| < 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  ⟨h2, norm_spectralM h2.le, spectralM_im_pos h2, hasDerivAt_spectralZ_im _ _,
    hasDerivAt_spectralZ _ _, spectralM_quadratic h2.le⟩

example : 0 < (1 - 3 / 5 : ℝ) * (mE (1 / 2)).im ∧
    ∀ u ∈ Set.Icc (1 / 5 : ℝ) (3 / 5), (1 - 3 / 5 : ℝ) * (mE (1 / 2)).im ≤ |(zt (1 / 2) u).im| :=
  spectralZ_window_gap_of_bulk (κ := 1) (s := 1 / 5) (t := 3 / 5) one_pos
    (by rw [abs_of_pos (by norm_num)]; norm_num) (by norm_num)

example (ω : Ω 3 3 2) (ω' : Sizes.SeqΩ SizesInst.sz0) :
    Continuous (fun u : ℝ => Hflow 3 3 2 u ω 0 0) ∧
      Continuous (fun u : ℝ => SizesInst.sz0.seqHflow 0 u ω' 0 0) :=
  ⟨continuous_Hflow_entry_time 3 3 2 ω 0 0,
    Sizes.continuous_seqHflow_entry_time SizesInst.sz0 0 ω' 0 0⟩

example (ω : Ω 3 3 2) :
    Continuous (fun u : ℝ => Gres (Hflow 3 3 2 u ω) Complex.I true 0 0) ∧
    Continuous (fun u : ℝ => Gres (Hflow 3 3 2 u ω) ((u : ℂ) + Complex.I) true) ∧
    Continuous (fun u : ℝ =>
      loopL 3 3 2 (HflowBlock 3 3 2 u ω) ((u : ℂ) + Complex.I) flowCalculusLoop) := by
  have hz : Continuous fun u : ℝ => (u : ℂ) + Complex.I :=
    Complex.continuous_ofReal.add continuous_const
  have him : ∀ u : ℝ, ((u : ℂ) + Complex.I).im ≠ 0 := fun u => by simp
  exact ⟨(continuous_apply _).comp ((continuous_apply _).comp
      (continuous_green_Hflow_time 3 3 2 ω (z := Complex.I) (by norm_num))),
    continuous_green_Hflow_moving_time 3 3 2 ω hz him,
    continuous_gloop_Hflow_time 3 3 2 ω hz him flowCalculusLoop flowCalculusLoop_wf⟩

example :
    Continuous (fun ω : Ω 3 3 2 =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I flowCalculusLoop) ∧
    Measurable (fun ω : Ω 3 3 2 =>
      loopL 3 3 2 (HflowBlock 3 3 2 (1 / 2) ω) Complex.I flowCalculusLoop) :=
  ⟨continuous_gloop_HflowBlock_sample 3 3 2 (1 / 2) (by norm_num) _ flowCalculusLoop_wf,
    measurable_gloop_HflowBlock_sample 3 3 2 (1 / 2) (by norm_num) _ flowCalculusLoop_wf⟩

example (ω : Ω 3 3 2) :
    HasDerivAt (fun v : ℝ => Gres (HflowBlock 3 3 2 v ω) (zt (1 / 2) v) true)
      (-(Gres (HflowBlock 3 3 2 (1 / 2) ω) (zt (1 / 2) (1 / 2)) true *
        ((1 / (2 * Real.sqrt (1 / 2)) : ℝ) • blockMat 3 3 2 (Xmat 3 3 2 ω) +
          mE (1 / 2) • (1 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ)) *
        Gres (HflowBlock 3 3 2 (1 / 2) ω) (zt (1 / 2) (1 / 2)) true)) (1 / 2) ∧
    HasDerivAt (fun v : ℝ => loopL 3 3 2 (HflowBlock 3 3 2 v ω) (zt (1 / 2) v) flowCalculusLoop)
      (Matrix.trace (loopWordDeriv 3 3 2 ω (1 / 2) (1 / 2)
        (flowCalculusLoop.σ.zip flowCalculusLoop.a))) (1 / 2) := by
  have hE : |(1 / 2 : ℝ)| < 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  exact ⟨hasDerivAt_green_HflowBlock_spectralZ 3 3 2 ω hE (by norm_num) (by norm_num),
    hasDerivAt_gloop_HflowBlock_spectralZ 3 3 2 ω hE (by norm_num) (by norm_num)
      flowCalculusLoop flowCalculusLoop_wf⟩

example : ∀ u ∈ Set.Icc (1 / 5 : ℝ) (3 / 5), ∀ ω : Ω 3 3 2,
    ‖loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (1 / 2) u) flowCalculusLoop‖ ≤
      (((3 * 2) ^ 3 : ℕ) : ℝ) *
        (((1 - 3 / 5 : ℝ) * (mE (1 / 2)).im)⁻¹ * (((2 : ℕ) : ℝ) ^ 3)⁻¹) ^ 3 := by
  have hE : |(1 / 2 : ℝ)| ≤ 2 - 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  obtain ⟨hη, hgap⟩ := spectralZ_window_gap_of_bulk (s := 1 / 5) (t := 3 / 5) one_pos hE
    (by norm_num)
  exact norm_gloop_HflowBlock_le_crude_on_Icc 3 3 2 hη hgap flowCalculusLoop flowCalculusLoop_wf

example :
    ContinuousOn (fun u : ℝ => ∫ ω : Ω 3 3 2,
      ‖loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (1 / 2) u) flowCalculusLoop‖ ^ 2 ∂(PF 3 3 2 1))
      (Set.Icc (1 / 5 : ℝ) (3 / 5)) :=
  continuousOn_integral_norm_gloop_pow_spectralZ 3 3 2 1 (κ := 1) (s := 1 / 5) (t := 3 / 5)
    one_pos (by rw [abs_of_pos (by norm_num)]; norm_num) (by norm_num) (by norm_num)
    flowCalculusLoop flowCalculusLoop_wf 2

example : Fintype.card (Vtx 3 3 2) = 216 ∧ Fintype.card (Vtx 3 3 2) = Fintype.card (Idx 3 3 2) ∧
    ‖Eblk 3 3 2 (![1, 0, 2] : Zd 3 3)‖ ≤ (((2 : ℕ) : ℝ) ^ 3)⁻¹ :=
  ⟨by rw [card_BlockIndex]; norm_num, by rw [card_BlockIndex, card_Idx, mul_comm],
    norm_Eblk_le_inv_W_sq 3 3 2 _⟩

end Instances

end RBM.Gauss

```

### b.5 Name-clash grep of the 56 new public names against `RBM3D/` (script `clash.sh`: `grep -rnE "(theorem|lemma|def|abbrev|instance|structure) (private )?(RBM\.)?(Gauss\.)?(Sizes\.)?<name>( |$)" RBM3D`, excluding the new file)
```
RBM3D/Loop/GLoopFlow.lean:729:private theorem norm_matrix_entry_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
names checked: 56
```
The one hit is a `private` theorem of `RBM3D/Loop/GLoopFlow.lean`; private names are not visible from other modules and the file builds with the import (b.1). No public clash.

### b.6 Statement diff against RBM2D `c9a24cf` after renaming (script `stmtdiff.py`: statement text of each public `theorem`/`def` of the ten files, RBM2D side renamed `spectralM->mE, spectralZ->zt, Z2 L->Zd d L, LoopIdx->Loop.LoopIdx, (X L W)->(X d L W), gloop->loopL, Gsig->Gres, green A B->Gres A B true, BlockIndex->Vtx, P->PF d L W g, W^-2->W^-d, (LW)^2->(LW)^d, d.L->sz.L`)
```
RBM2D public theorem/def in the 10 files: 61  identical after renaming: 42  differing: 13  not ported: 6
NOT PORTED SpectralWindow spectralM
NOT PORTED SpectralWindow spectralZ
NOT PORTED FlowTimeCont continuous_Hflow_nonzero_index_example
NOT PORTED GreenTimeCont continuous_green_Hflow_nonzero_index_example
NOT PORTED LoopTimeCont continuous_gloop_Hflow_one_edge_example
NOT PORTED LoopSampleCont measurable_gloop_HflowBlock_one_edge_example
--- DIFF SpectralWindow continuousOn_integral_norm_gloop_pow_spectralZ
--- DIFF LoopTimeCont HflowBlock
--- DIFF LoopTimeCont continuous_Gsig_Hflow_time
--- DIFF LoopSampleCont continuous_Gsig_HflowBlock_sample
--- DIFF LoopDerivative hasDerivAt_Gsig_HflowBlock_spectralZ
--- DIFF LoopDerivative loopWordDeriv
--- DIFF LoopDerivative hasDerivAt_loopWord_HflowBlock_spectralZ
--- DIFF LoopDerivative hasDerivAt_gloopProd_HflowBlock_spectralZ
--- DIFF LoopDerivative hasDerivAt_gloop_HflowBlock_spectralZ
--- DIFF LoopEnvelope norm_Gsig_le_inv_eta
--- DIFF LoopEnvelope norm_foldr_Gsig_Eblk_le
--- DIFF LoopEnvelope norm_gloop_le_crude
--- DIFF LoopEnvelope norm_gloop_HflowBlock_le_crude_on_Icc
```
Residual differences (all read off the diff; the "DIFF" lines of `Gsig` names and of `d L W` after `gsigFlowDeriv`/`loopWordDeriv` are artefacts of the renaming regex: the declaration names are kept, RBM2D `gsigFlowDeriv L W` is `gsigFlowDeriv d L W`; the double parenthesis `(((W:ℝ)^d)⁻¹)` of the regex is the same term as `((W:ℝ)^d)⁻¹`). Genuine ones:
- `continuousOn_integral_norm_gloop_pow_spectralZ`: `(L W : ℕ) [NeZero L] [NeZero W]` become the section variables `d L W`, plus the explicit `(g : ℝ)` of `PF d L W g` (RBM2D `P L W` has no coupling).
- `HflowBlock`: body `blockMat d L W (Hflow d L W u ω)` (= RBM2D `(Hflow …).submatrix (splitEquiv).symm (splitEquiv).symm`, `GLoopFlow:105`).
- `norm_Gsig_le_inv_eta`: stated for every `Matrix n n ℂ` (RBM2D: for `BlockIndex L W` only); it contains the RBM2D statement.
- `norm_foldr_Gsig_Eblk_le`, `norm_gloop_le_crude`, `norm_gloop_HflowBlock_le_crude_on_Icc`: the local binder `[NeZero W]` (RBM2D has it as a global `variable`; needed for `‖1‖ ≤ 1`).
- `hasDerivAt_green_HflowBlock_spectralZ` and `hasDerivAt_gloop…`: `(Xmat ω).submatrix (splitEquiv).symm (splitEquiv).symm` is written `blockMat d L W (Xmat d L W ω)` (same term).
- `norm_Eblk_le_inv_W_sq` keeps its RBM2D name but states `W^{-d}` (not a square); `card_BlockIndex` states `(L*W)^d` for `Vtx d L W`.
- Not ported: `spectralM`, `spectralZ` (merged `mE`, `zt`, `Defs/Semicircle:38,179`); the four `*_example` theorems of RBM2D (`L = 3, W = 1` / `L = 1, W = 1` collapsed data), replaced by the `d = 3, L = 3, W = 2` examples of b.4.

### b.7 `d = 2` token accounting (portmap P.1 rows 9, 10, 21, 23, 26; ticket item 8)
```
$ grep -nE "Z2|zdist2|pow_two|W2|L2|inv2|scal|\^ ?2" RBM3D/Gauss/FlowCalculus.lean  | cut -c1-110
22:`(·).submatrix (splitEquiv L W).symm (splitEquiv L W).symm` is `blockMat d L W`, `LoopIdx (Z2 L)` is
36:open scoped Matrix.Norms.L2Operator
45:theorem spectralM_im (E : ℝ) : (mE E).im = Real.sqrt (4 - E ^ 2) / 2 := mE_im E
81:    Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := sq_sqrt_four_sub hE
90:    mE E ^ 2 + E * mE E + 1 = 0 := by
698:/-- The block-product index has `(L W)^d = N` points (RBM2D: `(L W)^2`); `N = (W L)^d` is the
873:    (mE (1 / 2)) ^ 2 + ((1 / 2 : ℝ) : ℂ) * mE (1 / 2) + 1 = 0 :=
947:      ‖loopL 3 3 2 (HflowBlock 3 3 2 u ω) (zt (1 / 2) u) flowCalculusLoop‖ ^ 2 ∂(PF 3 3 2 1))
```
Lines 22 and 698 are docstring text naming the RBM2D form; line 36 is `Matrix.Norms.L2Operator`; the others are `E ^ 2` (`4 - E^2`, `m^2 + E m + 1`) and the exponent `2` of the moment in the instance (lines 873, 947). All `Z2 L` became `Zd d L` (loop types: LoopTimeCont, LoopSampleCont, LoopDerivative, LoopEnvelope, SpectralWindow), `(W⁻¹)^2` became `((W:ℝ)^d)⁻¹`, `(L*W)^2` became `(L*W)^d`, `simp [BlockIndex, Z2, pow_two]` became `simp only [Vtx, Zd, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]; rw [mul_pow]`.

### b.8 Ports: RBM2D `c9a24cf` (`git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf` = c9a24cf; RBM2D HEAD 9e0f275)
```
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Gauss/{SpectralWindow,SpectralAlgebra,SpectralDerivative,FlowTimeCont,GreenTimeCont,LoopTimeCont,LoopSampleCont,GreenDerivative,LoopDerivative,LoopEnvelope,MomentTimeCont,LoopMomentCont}.lean
 RBM2D/Gauss/FlowTimeCont.lean       | 35 +--------------
 RBM2D/Gauss/GreenDerivative.lean    | 44 -------------------
 RBM2D/Gauss/GreenTimeCont.lean      | 16 +------
 RBM2D/Gauss/LoopDerivative.lean     | 75 --------------------------------
 RBM2D/Gauss/LoopEnvelope.lean       | 12 ------
 RBM2D/Gauss/LoopMomentCont.lean     | 85 -------------------------------------
 RBM2D/Gauss/LoopSampleCont.lean     | 11 +----
 RBM2D/Gauss/LoopTimeCont.lean       | 19 ---------
 RBM2D/Gauss/MomentTimeCont.lean     | 78 ----------------------------------
 RBM2D/Gauss/SpectralAlgebra.lean    |  9 ----
 RBM2D/Gauss/SpectralDerivative.lean | 17 --------
 RBM2D/Gauss/SpectralWindow.lean     | 33 +-------------
 12 files changed, 5 insertions(+), 429 deletions(-)
```

### b.9 Narrative
- Scope: `RBM3D/Gauss/FlowCalculus.lean` (962 lines, one new file; `git diff --stat main...t/T2030` above) ports the ten RBM2D files at `c9a24cf`. 56 public declarations (52 theorems, 4 defs: `HflowBlock`, `spectralMSign`, `gsigFlowDeriv`, `loopWordDeriv`) and 6 private declarations (4 helpers `flowCalculus_…`, the instance loop `flowCalculusLoop` and its WF proof). 42 of the 61 RBM2D `theorem`/`def` statements are equal after the renaming of b.6; 13 differ as listed there; 6 are not ported (b.6).
- Vocabulary (merged, not duplicated): `spectralM = mE`, `spectralZ = zt` (`Defs/Semicircle`); the identities `spectralM_im`, `spectralM_im_pos`, `spectralZ_im`, `spectralM_sqrt_sq`, `spectralM_mul`, `norm_spectralM` are one-line bridges to `mE_im`, `mE_im_pos`, `zt_im`, `sq_sqrt_four_sub`, `mE_mul`, `norm_mE` (RBM2D names kept for later tickets); `spectralM_quadratic`, `continuous_spectralZ`, `spectralZ_im_gap`, `spectralZ_window_gap_of_bulk`, `hasDerivAt_spectralZ(_im)` are new in RBM3D. RBM2D `green H z` is `Gres H z true` (`Ring.inverse`; RBM2D used `⁻¹`), `Gsig` is `Gres`, `gloop`/`gloopProd` are `loopL`/`gloopProd` (GLoopFlow), `HflowBlock d L W u ω := blockMat d L W (Hflow d L W u ω)`.
- Dimension: only the envelope changes (`W^{-d}` per block insertion, `card (Vtx d L W) = (L*W)^d`, constant `(L W)^d (η⁻¹ W^{-d})^n`); everything else is dimension-free, as predicted in (a) rows 1-9. The envelope is the crude one (costs `L^d` against the merged `norm_gloop_le_sharp`, which has `n ≥ 1`); the crude one holds for every `n ≥ 0` and is what ST-2 uses (P.3).
- `continuousOn_integral_norm_gloop_pow_spectralZ` (finding F1 of (a): dead code at the kept RBM2D text, listed as a key statement by the ticket) is ported with private copies of `RBM2D/Gauss/MomentTimeCont.lean:26` (`continuousOn_integral_abs_pow_of_envelope`) and `RBM2D/Gauss/LoopMomentCont.lean:26, 51` (the window clamp and the moment), named `flowCalculus_…`. The other F1 statements (SpectralWindow:51, SpectralDerivative:33, FlowTimeCont:29-53, GreenTimeCont:74-88, LoopTimeCont:88-96, LoopEnvelope:120) are public, as the ticket lists them. Nothing from the ten files was dropped except the six items of b.6.
- Imports: `RBM3D.Loop.GLoopFlow` (MD layer) and three Mathlib modules; no ST-2..ST-6 file, no `RBM3D`.
- Instances (b.4): `d = 3`, `L = 3`, `W = 2` (`N = 216`, 27 blocks of 8 sites), `E = 1/2`, window `[1/5, 3/5]`, `κ = 1`, `u = 1/2`, a loop of length 3 with charges `(+,-,+)` and distinct nonzero blocks, `g = 1`, `q = 2`, plus `sz0` for `continuous_seqHflow_entry_time`. All deterministic hypotheses are discharged; the preflight script (a) checked the same data numerically.
- Not done / not needed: no `sorry`, no new hypothesis, no weakened target, no frozen signature touched; RBM2D untouched (read with `git show` / `git diff --stat` only).

## (c) Verified Mathlib names (all used in the compiled file; checked by the build of b.1)
`hasFDerivAt_ringInverse`, `Ring.inverse_unit`, `Matrix.nonsing_inv_eq_ringInverse`, `Real.hasDerivAt_sqrt`, `Real.continuous_sqrt`, `Continuous.matrix_submatrix`, `LinearMap.continuous_of_finiteDimensional`, `Matrix.traceLinearMap`, `HasDerivAt.star`, `HasDerivAt.smul_const`, `HasFDerivAt.comp_hasDerivAt`, `ContinuousLinearMap.mulLeftRight_apply`, `MeasureTheory.continuousOn_of_dominated`, `l2_opNorm_mulVec`, `l2_opNorm_diagonal`, `PiLp.norm_single`, `PiLp.norm_apply_le`, `Matrix.cstar_norm_def`, `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`, `pi_norm_le_iff_of_nonneg`, `ContinuousLinearMap.opNorm_le_bound`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- Open: none blocking. The theorems `norm_Eblk_le_inv_W_sq` (`W^{-d}`, not a square) and `continuous_Gsig_*`, `norm_Gsig_le_inv_eta` (`Gres`, not the merged `Gsig d L W ω E t σ`) keep RBM2D's names so that later tickets can grep them; their statements are about `Gres`/`W^{-d}`.
- `RBM3D/Loop/GLoopFlow.lean:729` has a private `norm_matrix_entry_le_opNorm` with the same short name as the new public one; harmless (b.5), recorded for the hub.
- Paper-delta candidates: T2030a: none. No new Lean/paper statement difference is introduced by this file beyond the single-time flow `Hflow` already in the merged `FineModel`.
