Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct  9 00:11:25 UTC 2026

Notation: `N = sz.size n = (W L)^d` (`Defs/Sizes.lean:157`), `η_u = (1-u) Im mE`, `Δ = (t0-t1)/K`, `λ(u) = N η_u` (`gueScale`), `τ' = min(τ,τU)/2`. Source: RBM2D `Universality/GUEPhase/HypA.lean` (1010 lines, RBM2D HEAD 9e0f275), 13 targets.

### (i) Exponent table

**A. The `d = 2` token table** (counts and line numbers are in the RBM2D source file)
| token (source lines) | replacement at `d` | constraint | slack / remark |
|---|---|---|---|
| `Z2 L` (47 lines), `BlockIndex L W` (15: 308-414), `Idx L W` (5: 369-373, 853) | `Zd d L`, `Vtx d L W`, `Idx d L W` | none (types) | `Vtx` fibre is `Fin (W^d)` (`trace_mul_Eblk`, `Hierarchy/ContractionBasic.lean:52`) |
| `((W:ℂ)⁻¹)^2` (308, 324, 336-339, 348, 350) | `((W:ℂ)⁻¹)^d` (weight of `E_a`) | `∑_p (E_a)_pp = W^d · W^{-d} = 1` | equality; public `trace_Eblk` (`Loop/GLoopFlow.lean:231`) |
| `((W*L)^2 : ℕ)` (548, 555, 657, 660, 661, 762, 768, 778, 802-808) | `((W*L)^d : ℕ) = sz.size n` (`rfl`) | `hsmall: M³ N Δ ≤ 1` | n=0: `N = 2097152` (`(WL)^2` would be 16384), see (ii) |
| outer square of `N` in `3 M⁶ N² (v-u)²` (660, 686, 714, 726, 743-744, 768-808) | stays `N^2`, `(v-u)^2` | from three terms `M³ S e`, `e = M³ S (v-u)`; matches merged `norm_primBilGUE_le` (`n² N ∑ B B'`, `Bootstrap.lean:228`) | no `d` in the exponent; only `N = (WL)^d` |
| `(d.L n)^2 (1 - t1 n) ≤ 1` (`hell`: 470, 513, 598) | `L^d (1 - t1) ≤ lam²` (merged `ProcK.lean:418`, DECISIONS §141, §142 O4) | gives `Bctl ≤ 2 (N η)⁻¹` via `(lam²+x)⁻¹ ≤ (L^d x)⁻¹` | n=0: `4.69e-5 ≤ 2.44e-4` (×5.2); n=1 ×40.8; n=2 ×133 |
| other `^ 2` (76 `√` concavity; 635, 640, 641 loop-count `n²`; 894, 899, 967, 992 `η⁻¹^2`) | unchanged | `n² ≤ M²`; resolvent factor `η⁻²` as in merged `Proc.lean` | no `d` |
| `log L` | 0 occurrences in the file | – | nothing to replace |
| `spectralZ/M` (13), `Gsig` (3), `gloop` (11), `blockMat` (10), `d.L/d.W/d.size` (82) | `zt/mE`, `Gres`, `loopL d L W (blockMat d L W ·)`, `sz.L/sz.W/sz.size` | – | renaming only |

**B. Twins of RBM2D names without an RBM3D namesake (by content)**
| RBM2D name | RBM3D twin (file:line) or re-derive | remark |
|---|---|---|
| `Kcal`, `Kgen` (`Loop/Kcal.lean:192,182`), `mSig` (`:148`) | `KLK`, `KLgen` (`Loop/KLTree.lean:145,135`), `STKloop` (`Induction/Defs.lean:64`), `mSigma` (`Defs/Semicircle.lean:85`); `KLK_one` (`KLTree.lean:206`) | `hKinit` as in merged `ProcK.lean:418`: `Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a` |
| `Mt`, `Par`, `scaleM`, `kloop_Mt_eq`, `Kbound_prec_uncond` | none by content; replaced (DECISIONS §141) by the pin `sz.STKbound E` (`Induction/Defs.lean:174`) + conversion `Bctl ≤ 2 (N η)⁻¹` | `Loop/KBound.lean` (154 lines) only has `KLoopBound`; not needed by any target. Re-derive the private block of `ProcK.lean` (286-546: `size_pos, etaT_nonneg/anti, im_le_one, gueScale_pos, ofFn_getD, loopOf_eq, stKbound_eventually, Bctl_le, initial, hbase`): 236 lines by script, ≤ 300, so no FAIL |
| `LLf` (`Induction/HierVocab.lean:130`) | `loopL d L W (blockMat d L W M) (zt E u)` (the argument of `primRhsGUE` in merged `loopGenGUE`, `Generator.lean:1229`) | content-identical |
| `length_cutGlue`, `WF.cutGlue` | re-derive (≈ 6 lines each; private twins `Path/OneStep.lean:318,325`); `norm_gloop_le_loopMax` public (`Induction/Split.lean:520`) | `cutGlue k b I` argument order, dot notation unchanged |
| `gloopProd_nil/cons`, `Gsig_conjTranspose`, `norm_trace_Eblk_le` | re-derive (≈ 5, 10, 15 lines; twins private: `GLoopFlow.lean:391,394`, `Split.lean:250`, `GLoopFlow.lean:826`) | `Hyp_trace_Eblk` has the public `trace_Eblk` |
| `avgErr`, `greenBlk`, `mixEntry_greenBlk_eq` | public (`Green/Pins.lean:89,83`, `GUEPhase/EntryTail.lean:842`) | – |

**C. Constants and thresholds the targets depend on**
| quantity | value | constraint | slack |
|---|---|---|---|
| `eq736` (`Bootstrap.lean:442`): `4 n³ A ε < 1`, loop bound `2n0 = 4`, `A = N^{τ'}`, `ε = N^{-τU}`, `τ=τU=1/1000` | n=0: `254.1` (violated) | holds eventually: `N^{τU-τ'} ≥ 8·4³+1 = 513` | `log10 N_* = 5420`: only the `∀ᶠ n` conclusion of `Hyp_Kt_detDom` is eventual, hypotheses hold for all `n` |
| `eq736` `hsmall`: `N (u-t1) ≤ ε λ(u)` from `h730` | `t0-t1 = ½ N^{-τU} η_{t0}` | `h730: t0-t1 ≤ N^{-τU} η_{t0}` | factor 2 |
| `hlam` constant of `Hyp_interp_bound`: `λ(u_k) ≤ C λ(t)` for `u_k ≤ t+Δ` | minimal `C = (1-t1)/(1-t0) = 1.49277`; `C = 2` used | `C ≥ 1+(t0-t1)/(1-t0)`, `≤ 1+N^{-τU} = 1.9856` | 0.507 below 2 |
| `Hyp_Kt_disc` smallness `M³ N Δ ≤ 1`, `K = 64` | `M=2: 0.0634`; `M=4: 0.5073` | `≤ 1` | ×15.8; ×1.97 |
| `Hyp_Kt_disc` error `3 M⁶ N² Δ (t0-t1)` | `0.772` (M=2), `49.4` (M=4) at `K=64` | at `K = (N+1)^{32 n0+64}` (`gueGridK`): `log10 err = -803.9`, smallness slack `10^{806.8}` | downstream choice, not a hypothesis |
| conversion `Bctl(t1) ≤ 2 (N η_{t1})⁻¹` | `0.7753 ≤ 1.3013` | uses `hell` | ×1.68 |
| (7.36) base scale `(N η_{t0})⁻¹ = N^{-1/500}` | `0.9713` | `< 1` | 2.9% |

**D. §29 (one line each)** (1) time domain: `0 ≤ t1 n`, `t0 n < 1` are targets' hypotheses; instance `0 < t1 < t0 < 1` (script asserts n=0..2; Lean proofs `ProcK.lean:854-880`, `t1_nonneg`, `t1_le_t0`, `t0_lt_one`). (2) boundary of `hell`: `1-t1 ≤ lam²/L^d`: n=0 `7.33e-7 ≤ 3.81e-6`; if `lam² > L^d` the bound only restricts `t1 ≥ 1 - lam²/L^d < 0`, covered by `0 ≤ t1`. (3) no `L^d ≤ W^K` relation is used by any target (only `N=(WL)^d`, fibre `W^d`). (4) `ht1, ht10, ht0, hE` are `∀ n` as in merged `ProcK.lean:553`; `h730, hell, hsz` are `∀ᶠ n`; the `∀ n` ones hold at every `n` of the instance.

### (ii) One concrete nondegenerate instance
Data: `d = 3`, merged `SizesInst.sz0` at `n = 0` (`L=4, W=32, lam=1/64, N=(WL)^3=2097152`; `Defs/Sizes.lean:260-275`), `E ≡ 0` (`mE 0 = i`), `κ=1/10`, `τU=1/1000`, `n0=2`; window `1-t0 = N^{1/500}/N = 4.909e-7`, `t0-t1 = N^{-τU}(1-t0)/2 = 2.419e-7` (the merged `ProcKInst` window, `ProcK.lean:825-830`), `K ≡ 64` (`Δ = 3.78e-9`), `m = 2`, `k = 40`, `σ = 40`, loop `⟨[+,-],[0,1]⟩`, `M ∈ {2,4}`.
Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2352/inst.py`
```
d=3 n=0: (4, 32, 0.015625, 2097152)  (W L)^2 would be 16384
n=0: N=2.097e+06 1-t0=4.909e-07 t0-t1=2.419e-07 h730 2.42e-07<=4.84e-07 True; hell L^d(1-t1)=4.69e-05<=lam^2=0.0002441 True ratio 5.21
n=1: N=5.498e+11 1-t0=1.92e-12 t0-t1=9.344e-13 h730 9.34e-13<=1.87e-12 True; hell L^d(1-t1)=1.461e-09<=lam^2=5.96e-08 True ratio 40.78
n=2: N=8.125e+14 1-t0=1.318e-15 t0-t1=6.661e-16 h730 6.66e-16<=1.29e-15 True; hell L^d(1-t1)=3.453e-12<=lam^2=4.594e-10 True ratio 133.03
Bctl(t1)=0.7753 <= 2(N eta_t1)^-1=1.3013; k=1: |mE|=1 <= N^eps*Bctl^0 ; (N eta_t0)^-1=0.9713
M=2 K=64 Delta=3.78e-09  M^3 N Delta=0.0634<=1 True  err=3M^6N^2 Delta(t0-t1)=0.7722
M=4 K=64 Delta=3.78e-09  M^3 N Delta=0.5073<=1 True  err=3M^6N^2 Delta(t0-t1)=49.42
K=gueGridK=(N+1)^128: log10 K=809.2 ; M^3 N Delta<=1 slack log10=806.8 ; log10 err=-803.9
eq736: 4 n^3 A eps<1 with n=2n0=4, A=N^tau', eps=N^-tauU: at n=0 value 254.1 (>1: only eventual); threshold log10 N_*=5420
  t-t1=0: hlam True hgrid True interp=7.618e-13<=4.074      (float noise: exact value 0)
  t-t1=8.95e-08: hlam True hgrid True interp=0.0002992<=3.699
  t-t1=1.21e-07: hlam True hgrid True interp=0.0003478<=3.567
  t-t1=1.52e-07: hlam True hgrid True interp=0.0003888<=3.435
  t-t1=2.42e-07: hlam True hgrid True interp=0.0003888<=3.06
C=2 used; minimal C=(1-t1)/(1-t0)=1+(t0-t1)/(1-t0)=1.49277 <= 1+N^-tauU=1.98555
eps_le_dev: M=0, |G-m|=1.36456e+06, u/(1-u)=1.36456e+06, avgErr=<(G-m)E_a>=1.36456e+06*1 (tr E_a=1) -> |avgErr|=c
cutGlue k=1: sigma=[True, True, False] a=[0, 0, 0] len=3=len+1=3, WF True
cutGlue k=2: sigma=[True, False, False] a=[0, 0, 0] len=3=len+1=3, WF True
loop at M=0 of length 3 same label: |L|=eta^-3 W^-2d = 2366340884.408524 =loopMax(3); (W^d)^-1 per E_a, tr(E^3)=W^-2d
exists_loopOf: WF True x length 3
Hyp_grid core k=40: |a_k-b_k|=50.36 <= bound=50.59: True  (err=49.4)
ALL OK
```
(Doubles; `n ≥ 3` loses precision at `1-t0 ~ 1e-18`, the Lean proofs `ProcK.lean:854-900` cover all `n`.)

Hypotheses per target at these data:
- `Hyp_step_nonneg/time_ge/time_le/time_mem`: `t1 ≤ t0`, `K = 64 ≠ 0`, `k ≤ K`. `Hyp_interp_bound`: `σ = 40 ≤ K`, `t ∈ [t1,t0]`, `lam = λ`, `P=Q=A=B=1`, `f_k = √(u_k-t1)`, `hlam` with `C = 2`, `hgrid` (all asserted above).
- `Hyp_exists_loopOf`, `Hyp_cutGlue_le` (`I` WF, `k ∈ [1,2]`), `Hyp_eps_le_dev`, `Hyp_trace_eq_gloop_one` (`M = 0` Hermitian, `u = t1`, `c = u/(1-u)`, sharp equality): above.
- `Hyp_Kt_detDom`, `Hyp_Kt_one`, all `n`: `hE, ht1, ht10, ht0, h730, hell` by script (n=0..2) and `ProcK.lean:854-900` (all n); `hsz`: `N_n = 2^21 (n+1)^18 → ∞` (`Sizes.tendsto_size sz0 sz0_tendsto`, as `ProcK.lean:948`). External hypothesis `hKb : sz.STKbound E`: dischargeable by merged `stKbound_holds` (`Loop/KLFinal.lean:243`) whose hypotheses `3 ≤ d`, `0 < κ`, `0 < gmax = 1`, `SizeTendsto`, `|E| ≤ 2-κ`, `0 < lam n = (2(n+1))^{-6} ≤ 1` hold at `sz0`; limit check (lesson 14): `k = 1`: `|mE 0| = 1 ≤ N^ε`; conversion `Bctl(t1) = 0.7753 ≤ 2 (Nη)⁻¹ = 1.3013`; the pin is false for bounded `N` (`KLFinal.lean`, `N ≡ 27`), here `N → ∞`. `Kt n`, `hKinit`, `hK` (`1 ≤ |I| ≤ 4 n0 = 8`): from merged `gueK_exists` (`GUEPhase/KPrim.lean:749`; needs `3 ≤ L`, `|E|<2`, `0 ≤ t1 ≤ t0 < 1`: all hold), `Kt t1 = KLgen (mSigma E) t1 = STKloop`.
- `Hyp_Kt_disc` (`M=4`, `K=64`): `hsmall` `0.507 ≤ 1`; `Kt` = the toy solution (`m(σ)` on 1-loops, `0` on loops of length ≥ 2; both factors of a cut have length ≥ 2, so `primRhsGUE = 0` and `hK`, `hbd` hold); for the real `K̃` the hypothesis `hbd` (`‖K̃‖ ≤ 1`) is an output of `Hyp_Kt_detDom` (eventual in `n`, not checked at `n = 0`), so it is not part of this instance.
- `Hyp_grid`: deterministic data `|E n| < 2`, `0 ≤ t1`, `t0 < 1`, `m = 2 ≥ 1`, `c, Cf, Ce ≥ 0`, `g1, g3, g4` constant (nonneg, continuous), `t ∈ [t1,t0]`, `hkt`: asserted; `hdisc` from `Hyp_Kt_disc` (err = 49.4 at M=4). The pathwise estimates `h0, hM, hq, hF, heG` and `k ≤ gueStop` for `k ≥ 1` (the random `ω`: `gueStop` needs `gueDev < δ` at a typical GUE point; at `H = 0` `gueDev = u/(1-u)` is huge) stay hypotheses of the example (inputs of UN-49 `HypB`); they are satisfiable: the quantifiers are over finite sets, the constants are free, and the right side of `hM` contains `λ(u_k)^{-m} > 0`. The numeric core above checks the discrete Duhamel inequality with synthetic data at the extreme of every hypothesis (`50.36 ≤ 50.59`).

### Verdicts
- `Hyp_step_nonneg`, `Hyp_time_ge`, `Hyp_time_le`, `Hyp_time_mem`, `Hyp_interp_bound`, `Hyp_exists_loopOf`, `Hyp_eps_le_dev`, `Hyp_trace_eq_gloop_one`, `Hyp_cutGlue_le`, `Hyp_Kt_one`, `Hyp_Kt_disc`, `Hyp_grid`: PASS (every exponent closes with equality or the slack above; `d` enters only through `N=(WL)^d`, the fibre `W^d`, and `hell`).
- `Hyp_Kt_detDom`: PASS, with a statement departure to be recorded as paper-delta candidate `T2352a`: no RBM3D `Kbound_prec_uncond`; the statement carries `hKb : sz.STKbound E`, `hKinit` with `STKloop`, and `hell : L^d (1-t1) ≤ lam²` instead of `L² (1-t1) ≤ 1` (as merged `gueKproc_detDom`, DECISIONS §141). `Hyp_Kt_one` carries the same `hKinit` form and `mSigma` for `mSig`.
- Overall verdict: PASS (the missing layers have twins by content or re-derive in 236 + about 60 lines, below the 300-line FAIL line).

## (b) Script output (written Fri Oct  9 00:33:37 UTC 2026)
### Build, hygiene, registry pre-check
$ git diff --stat main...t/T2352; wc -l RBM3D/Universality/GUEPhase/HypA.lean; git log --format='%h %s' -4 | cut -c1-80
 RBM3D/Universality/GUEPhase/HypA.lean | 1419 +++++++++++++++++++++++++++++++++
 1 file changed, 1419 insertions(+)
    1419 RBM3D/Universality/GUEPhase/HypA.lean
e7b62ba T2352: HypA part 4 (compiled instances HypAInst for every target)
254e794 T2352: HypA part 3 (Hyp_Kt_disc, discrete Duhamel formula Hyp_grid)
dced3b8 T2352: HypA part 2 (deterministic K-tilde: Hyp_Kt_detDom, Hyp_Kt_one, on
60654ee T2352: HypA part 1 (real-analysis and loop-level helpers)
$ grep -c -E 'sorry|admit|native_decide|^axiom' HypA.lean   (hits)
0
$ lake build RBM3D.Universality.GUEPhase.HypA > build2.log; grep -n 'Built\|Build completed' build2.log
253:✔ [3762/3762] Built RBM3D.Universality.GUEPhase.HypA (6.9s)
254:Build completed successfully (3762 jobs).
$ lake build RBM3D.Universality.GUEPhase.HypA 2>&1 | tail -1   (rerun)
Build completed successfully (3762 jobs).
$ lake build 2>&1 | tail -1   (full library; HypA not yet in the root import: the hub adds it at merge)
Build completed successfully (4163 jobs).
$ registry.lean = `import RBM3D` + `import RBM3D.Universality.GUEPhase.HypA` + `#assert_rbm_axioms` (scratch, uncommitted); lake env lean registry.lean > registry.out; echo $?
axiom audit: 10483 theorems, 3076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).   [exit 0; registry.out 265 lines, 0 `error`]
$ #print axioms of the 13 targets (`import RBM3D.Universality.GUEPhase.HypA`, `lake env lean ax.lean`)
Hyp_step_nonneg: [propext, Classical.choice, Quot.sound]
Hyp_time_ge: [propext, Classical.choice, Quot.sound]
Hyp_time_le: [propext, Classical.choice, Quot.sound]
Hyp_time_mem: [propext, Classical.choice, Quot.sound]
Hyp_interp_bound: [propext, Classical.choice, Quot.sound]
Hyp_exists_loopOf: [propext, Quot.sound]
Hyp_eps_le_dev: [propext, Classical.choice, Quot.sound]
Hyp_trace_eq_gloop_one: [propext, Classical.choice, Quot.sound]
Hyp_cutGlue_le: [propext, Classical.choice, Quot.sound]
Hyp_Kt_detDom: [propext, Classical.choice, Quot.sound]
Hyp_Kt_one: [propext, Classical.choice, Quot.sound]
Hyp_Kt_disc: [propext, Classical.choice, Quot.sound]
Hyp_grid: [propext, Classical.choice, Quot.sound]

### Target statements (script `stmt.sh`: from `theorem NAME` to the `:=` line, whitespace joined, folded at 200 columns; section variables below)
66:variable {d : ℕ} (sz : Sizes d)
84:variable {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
theorem Hyp_step_nonneg (ht10 : t1 n ≤ t0 n) : 0 ≤ gridStep t1 t0 K n
theorem Hyp_time_ge (ht10 : t1 n ≤ t0 n) (k : ℕ) : t1 n ≤ gridTime t1 t0 K n k
theorem Hyp_time_le (ht10 : t1 n ≤ t0 n) (hK : K n ≠ 0) {k : ℕ} (hk : k ≤ K n) : gridTime t1 t0 K n k ≤ t0 n
theorem Hyp_time_mem (ht10 : t1 n ≤ t0 n) (hK : K n ≠ 0) {k : ℕ} (hk : k ≤ K n) : gridTime t1 t0 K n k ∈ Set.Icc (t1 n) (t0 n)
theorem Hyp_interp_bound (f : ℕ → ℝ) {σ : ℕ} (hσ : σ ≤ K n) (hK : K n ≠ 0) (ht10 : t1 n ≤ t0 n) {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) (lam : ℝ → ℝ) {P Q A B C : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hB : 
0 ≤ B) (hlam : ∀ k ≤ K n, gridTime t1 t0 K n k ≤ t + gridStep t1 t0 K n → lam (gridTime t1 t0 K n k) ≤ C * lam t) (hgrid : ∀ k ≤ σ, (∀ j < k, gridTime t1 t0 K n j ≤ t) → f k ≤ P + Q * lam (gridTime 
t1 t0 K n k) + A * (gridTime t1 t0 K n k - t1 n) + B * Real.sqrt (gridTime t1 t0 K n k - t1 n)) : gueInterp t1 t0 K n (fun k => f (min k σ)) t ≤ P + Q * (C * lam t) + A * (t - t1 n) + B * Real.sqrt 
(t - t1 n)
theorem Hyp_exists_loopOf {d L : ℕ} [NeZero L] (J : RBM.Loop.LoopIdx (Zd d L)) (hJ : J.WF) : ∃ x : (Fin J.length → Bool) × (Fin J.length → Zd d L), loopOf x.1 x.2 = J
theorem Hyp_eps_le_dev {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (E u : ℝ) {c : ℝ} (hc : ∀ i : Idx d L W, ‖(green M (zt E u) - mE E • (1 : Matrix 
(Idx d L W) (Idx d L W) ℂ)) i i‖ ≤ c) (σ : Bool) (a : Zd d L) : ‖RBM.Green.avgErr d L W E u M σ a‖ ≤ c
theorem Hyp_trace_eq_gloop_one {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (m : Bool → ℂ) (σ : Bool) (a : Zd d L) : Matrix.trace ((Gres H z σ - m σ • (1 : Matrix 
(Vtx d L W) (Vtx d L W) ℂ)) * Eblk d L W a) = loopL d L W H z ⟨[σ], [a]⟩ - m σ
theorem Hyp_cutGlue_le {d L W : ℕ} [NeZero L] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} {I : RBM.Loop.LoopIdx (Zd d L)} (hI : I.WF) {k : ℕ} (hk : k ∈ Finset.Icc 1 I.length) (b : Zd d L) : ‖loopL 
d L W H z (I.cutGlue k b)‖ ≤ RBM.Ind.loopMax d L W H z (I.length + 1)
theorem Hyp_Kt_detDom {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (hsz : Tendsto 
sz.size atTop atTop) (h730 : ∀ᶠ n : ℕ in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n)) (hell : ∀ᶠ n : ℕ in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) (hKb : 
sz.STKbound E) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a) (hK 
: ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) 
(Set.Icc (t1 n) (t0 n)) t) : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 2 ≤ I.length → I.length ≤ 2 * n0 → ‖Kt n t I‖ ≤ ((sz.size n 
: ℕ) : ℝ) ^ ε * (gueScale sz E n t)⁻¹ ^ (I.length - 1)
theorem Hyp_Kt_one {E t1 t0 : ℕ → ℝ} (n0 : ℕ) (hn0 : 1 ≤ n0) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) 
(loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a) (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n 
s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (t1 n) (t0 n)) (s : Bool) (a : Zd d (sz.L n)) : Kt n u ⟨[s], [a]⟩ = mSigma (E n) s
theorem Hyp_Kt_disc {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {n M : ℕ} (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (ht10 : t1 n ≤ t0 n) (hK0 : K n ≠ 0) (hK : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : 
RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ M → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) (hbd : ∀ t ∈ Set.Icc 
(t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ M → ‖Kt n t J‖ ≤ 1) (hsmall : (M : ℝ) ^ 3 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1) {k : ℕ} 
(hk : k ≤ K n) (I : RBM.Loop.LoopIdx (Zd d (sz.L n))) (hI : I.WF) (hI1 : 1 ≤ I.length) (hIM : I.length ≤ M) : ‖Kt n (gridTime t1 t0 K n k) I - Kt n (gridTime t1 t0 K n 0) I - (gridStep t1 t0 K n : ℂ) 
* ∑ j ∈ Finset.range k, primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) I‖ ≤ 3 * (M : ℝ) ^ 6 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 2 * gridStep t1 t0 K n * (t0 n - t1 n)
theorem Hyp_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m : ℕ) (ω : PathΩ sz) (g1 g3 g4 : ℝ → ℝ) {c Cf Ce err Λ0 : ℝ} (ht10 : t1 n ≤ t0 n) 
(hE : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht0 : t0 n < 1) (hm : 1 ≤ m) (hc : 0 ≤ c) (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce) (hg1 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g1 u) (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) 
(hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u) (hg1c : ContinuousOn g1 (Set.Icc (t1 n) (t0 n))) (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n))) (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n))) (h0 : 
∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω)) (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) - Kt n (gridTime 
t1 t0 K n 0) (loopOf x.1 x.2)‖ ≤ c * Λ0) (hM : ∀ k ≤ K n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω)) (zt (E n) 
(gridTime t1 t0 K n k)) (loopOf x.1 x.2) - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n 0 ω)) (zt (E n) (gridTime t1 t0 K n 0)) (loopOf x.1 x.2) - (gridStep t1 t0 K n : 
ℂ) * ∑ j ∈ Finset.range k, genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤ c * (Real.sqrt (gridTime t1 t0 K n k - t1 n) * (⨆ j : Fin k, 
Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 
K n j)) (2 * m))) + (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m)) (hq : ∀ j < gueStop sz E t1 t0 K δ n ω, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 K n j))⁻¹ ^ 2 * 
RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)) (2 * m)) ≤ g4 (gridTime t1 t0 K n j)) (hF : ∀ j < gueStop sz E t1 t0 K δ n 
ω, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ‖primRhsGUE d (sz.L n) (sz.W n) (loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j))) 
(loopOf x.1 x.2) - primRhsGUE d (sz.L n) (sz.W n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ Cf * g1 (gridTime t1 t0 K n j)) (heG : ∀ j < gueStop sz E t1 t0 K δ n ω, ∀ x : (Fin m → Bool) × 
(Fin m → Zd d (sz.L n)), ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 K n j)) (hdisc : ∀ k ≤ K n, ∀ x : (Fin m → Bool) 
× (Fin m → Zd d (sz.L n)), ‖Kt n (gridTime t1 t0 K n k) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 K n 0) (loopOf x.1 x.2) - (gridStep t1 t0 K n : ℂ) * ∑ j ∈ Finset.range k, primRhsGUE d (sz.L n) (sz.W 
n) (Kt n (gridTime t1 t0 K n j)) (loopOf x.1 x.2)‖ ≤ err) {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) {k : ℕ} (hkσ : k ≤ gueStop sz E t1 t0 K δ n ω) (hkt : ∀ j < k, gridTime t1 t0 K n j ≤ t) : gueDmax 
sz E t1 t0 K Kt n m k ω ≤ (c * Λ0 + err) + c * (gueScale sz E n (gridTime t1 t0 K n k))⁻¹ ^ m + (Cf * supOn g1 (t1 n) t + Ce * supOn g3 (t1 n) t) * (gridTime t1 t0 K n k - t1 n) + (c * supOn g4 (t1 
n) t) * Real.sqrt (gridTime t1 t0 K n k - t1 n)

### Translation table (RBM2D `Universality/GUEPhase/HypA.lean` 1010 lines, HEAD 9e0f275 -> port)
Token map (source -> port): `d : Sizes`, `d.L n`, `d.W n`, `d.size n` -> `sz : Sizes d`, `sz.L n`, `sz.W n`, `sz.size n`; `Z2 L` -> `Zd d L`; `LoopIdx` -> `RBM.Loop.LoopIdx`;
`BlockIndex L W` -> `Vtx d L W`; `Idx L W` -> `Idx d L W`; `spectralZ`/`spectralM` -> `zt`/`mE`; `Gsig` -> `Gres`; `gloop L W (blockMat M) z` -> `loopL d L W (blockMat d L W M) z`;
`RBM.Ind.LLf L W E u M` -> `loopL d L W (blockMat d L W M) (zt E u)`; `KLoop.mSig` -> `mSigma`; `RBM.Ind.loopMax L W` -> `RBM.Ind.loopMax d L W`; `primRhsGUE/genMatGUE/egtNGUE L W` -> `... d L W`;
`avgErr` -> `RBM.Green.avgErr d L W`; `(((W*L)^2:ℕ):ℝ)` (12 lines) -> `(((W*L)^d:ℕ):ℝ)` (12 lines); `((W:ℂ)⁻¹)^2` (the `E_a` weight, 4 lines) -> `((W:ℂ)^d)⁻¹`, through the public `trace_mul_Eblk`, `trace_Eblk`;
`(d.L n)^2 (1 - t1 n) ≤ 1` (`hell`) -> `L^d (1 - t1 n) ≤ ilambda^2` (departure, below); no `log L` in the source; the other `^ 2` are `n²`, `η⁻²`, `S²`, `√` concavity (no `d`).
Residual d=2 tokens (`Z2|d.L|d.W|d.size|spectralZ|spectralM|gloop|BlockIndex|Gsig|KLoop|LLf`) in source / port, then port lines past the docstring (line 90):
182
331:the merged private `Gres_conjTranspose`, `Induction/Split.lean:250`; RBM2D `Gsig_conjT
383:theorem Hyp_trace_eq_gloop_one {d L W : ℕ} [NeZero L] [NeZero W]
418:  exact RBM.Ind.norm_gloop_le_loopMax _ (by rw [hwf]; exact hlen) hlen
1170:example := Hyp_trace_eq_gloop_one (0 : Matrix (Vtx 3 3 2) (Vtx 3 3 2) ℂ) Complex.I
Target source:port line: Hyp_step_nonneg 82:86; Hyp_time_ge 98:102; Hyp_time_le 102:106; Hyp_time_mem 107:111; Hyp_interp_bound 199:203; Hyp_exists_loopOf 294:298; Hyp_eps_le_dev 370:352; Hyp_trace_eq_gloop_one 401:383; Hyp_cutGlue_le 413:411; Hyp_Kt_detDom 593:689; Hyp_Kt_one 612:711; Hyp_Kt_disc 754:863; Hyp_grid 870:980
Changes per target: `Hyp_step_nonneg`..`Hyp_interp_bound` verbatim (no `d` token); `Hyp_exists_loopOf` types; `Hyp_eps_le_dev` types, `zt/mE`, `RBM.Green.avgErr`; `Hyp_trace_eq_gloop_one` `Vtx/Gres/loopL`; `Hyp_cutGlue_le` `loopL`, `loopMax d`;
`Hyp_Kt_disc`, `Hyp_grid` renaming only (`N = (WL)^d`, `loopL`, `zt`, `PathΩ sz`); `Hyp_Kt_detDom`, `Hyp_Kt_one`: renaming + the departure of (d) T2352a (`hKb`, `hKinit` on `loopOf σ a`, `hell`, `mSigma`).

### Compiled instances (`HypAInst`, same file; `grep -n '^example'` line numbers) and the main target's instances
1144 1145 1146 1147 1152 1168 1170 1173 1208 1346 1357 1391 1399   (at e7b62ba; current numbers in `## Repair`)
Numbers of the window at `sz0`, `n = 0` (`python3 -I numbers.py`; exact `Fraction`s):
N = 2097152  0 < t1 < t0 < 1: True
1-t1 = 3.8147e-06  t0-t1 = 1.8190e-12  Delta = 2.8422e-14
hell: L^d (1-t1) = lam^2: True
hsmall: M^3 N Delta = 3.8147e-06 <= 1: True
err = 3 M^6 N^2 Delta (t0-t1) = 2.7940e-09
`Hyp_Kt_detDom` and `Hyp_grid` instances: superseded by the repair (commit 336dec3); the current text and line numbers are in `## Repair` below.

### Name clash, imports, ports
$ grep -rn target names and HypAInst in RBM3D/ outside Probe/ and outside HypA.lean | wc -l  ->        0
$ git -C ../RBM2D log -1 --format=%h; ... diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/HypA.lean | wc -l; ... status --short -- (same file) | wc -l
9e0f275
       0
       0
$ git log -1 --format=%h -- ProcK.lean (source of the copied initial-data block); grep -c '^private theorem' HypA.lean; grep -c '^theorem Hyp_' HypA.lean
ba2ddf3
49
13
$ HypA.lean without the `import RBM3D.Loop.KBound` line: lake env lean | wc -l   (0 = compiles, no message)
       0
$ declarations named Kbound_prec_uncond|Kcal|Kgen|mSig|scaleM|kloop_Mt_eq|LLf|length_cutGlue in RBM3D/ (outside Probe/) | wc -l
       0

### Narrative (prover, claude-sonnet-5-5)
1. (At e7b62ba; after the repair 1499 lines, see `## Repair`.) One new file, 1419 lines (ticket sizes 900 / 1050 / 1300; the stop line 1500 was not reached): lines 61-1116 port RBM2D `HypA.lean` (1010 lines), lines 1118-1417 are `HypAInst` (300 lines). Four section commits (424, 860, 1118, 1419 lines).
2. Section `HypReal` (port 67-291, source 63-287) is byte-identical to the source: `diff` is 0 lines; it contains no `d`-dependent token (preflight (a)(i)A).
3. `HypLoop`: the source's `Hyp_sum_Eblk_diag`, `Hyp_trace_mul_Eblk`, `Hyp_trace_Eblk` are replaced by the merged public `trace_mul_Eblk` (`Hierarchy/ContractionBasic.lean:52`) and `trace_Eblk` (`Loop/GLoopFlow.lean:231`);
   `Hyp_norm_trace_Eblk_le` is re-proved from `trace_mul_Eblk` (fibre `Fin (W^d)`, weight `(W^d)⁻¹`); `Hyp_Gres_conjTranspose`, `Hyp_length_cutGlue`, `Hyp_wf_cutGlue` are private re-derivations
   (the twins in the imported files are private: `Induction/Split.lean:250`, `Path/OneStep.lean:318,325`); `gloopProd_nil/cons` is replaced by `simp [loopL]` in `Hyp_trace_eq_gloop_one`.
4. `HypKt`: the initial-data block (`Hyp_size_pos`, `Hyp_etaT_anti`, `Hyp_im_le_one`, `Hyp_gueScale_pos`, `Hyp_ofFn_getD`, `Hyp_loopOf_eq`, `Hyp_stKbound_eventually`, `Hyp_Bctl_le`, `Hyp_initial`, `Hyp_hbase`) is a private copy of merged
   `ProcK.lean:286-293,306-545` (prefix `ProcK_` -> `Hyp_`), the re-derivation planned in (a)(i)B (no FAIL). `Hyp_Kt_step`, `Hyp_card_bound`, `Hyp_Kt_disc`, `Hyp_grid`: the source proofs with the port map; `Hyp_genMat_split` uses `loopGenGUE` (`m ≥ 2`) and `loopGenGUE_one`.
5. Departure (as the merged `gueKproc_detDom`, DECISIONS §141): `Hyp_Kt_detDom` carries `hKb : sz.STKbound E`, `hKinit` for `loopOf σ a` with `STKloop`, and `hell : L^d (1 - t1) ≤ ilambda^2`; `Hyp_Kt_one` carries the same `hKinit` and concludes `mSigma (E n) s`. Paper-delta candidate T2352a in (d).
6. Instances (`HypAInst`, 13 `example`s, one per target): time facts and `Hyp_interp_bound` at the window [1/4, 1/2], `K = 64`; loop-level helpers at `d = 3`, `L = 3`, `W = 2` (`Hyp_eps_le_dev` at `M = 0`, `E = 0`, `u = 1/2`, `c = 1`, `G - m = i`, sharp);
   `Hyp_Kt_detDom`, `Hyp_Kt_one`, `Hyp_Kt_disc`, `Hyp_grid` at the `Grid.lean` §`GridCheck` sizes `sz0` (`d = 3`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `E = 0`, `κ = 1/10`, `τ_U = 1/1000`, `n₀ = 2`, `K = 64`, all `n` for the window lemmas.
7. The window of the instances differs from (a)(ii): `1 - t1 = ilambda²/L^d` (the boundary of `hell`, equality), `t0 - t1 = y/(N+1)`, `y = 1 - t1`, so `h730` reduces to `1 ≤ N^{1-τ_U}` and every window lemma is algebraic (script numbers above: `0 < t1 < t0 < 1`, `hell` equality, `M³ N Δ = 3.8e-6`). This is a choice of data, not a correction of (a).
8. `Hyp_Kt_detDom` instance: `hE`, `ht1`, `ht10`, `ht0`, `hsz` (`Sizes.tendsto_size sz0 sz0_tendsto`), `h730`, `hell`, `hKinit`, `hK` are discharged; `Kt` comes from `gueK_exists` (`choose`, `g = ilambda_n`, loops up to length `4 n₀ = 8`); `hKb : STKbound` is discharged by the merged `Sizes.stKbound_holds`
   (`Loop/KLFinal.lean:243`, imported by the repair; private `hKb0`): the instance has no hypothesis (repair, `## Repair`).
9. `Hyp_Kt_disc` and `Hyp_grid` use the stationary solution `Kt0 = m_σ` on `1`-loops, `0` on longer loops (`toyK_primRhs`: the left factor of a cut has length `≥ 2`, so every summand vanishes); `hsmall` is proved for the window (`M³ N Δ = N y/(N+1) ≤ y ≤ 1`); `hdisc` of `Hyp_grid` is `Hyp_Kt_disc`.
10. `Hyp_grid` instance (repair): at the concrete path `ω₀ = 0` every hypothesis is discharged, including `h0, hM, hq, hF, heG` and `40 ≤ gueStop` (`gueStop = 64`); see `## Repair`.
11. Imports as the ticket lists (`Proc`, `EntryTailMain`, `Loop/KBound`), plus `Loop/KLFinal` (repair, for `stKbound_holds`); `Loop/KBound` is not needed: the file compiles without that line (script above, 0 messages). Root import `RBM3D.lean` untouched (the hub adds it at merge).

## (c) Verified names
Script: `import RBM3D.Universality.GUEPhase.HypA` + `#check @NAME` for each of the 60 names below, `lake env lean names.lean`: exit 0, 0 `error` lines (Mathlib and RBM3D names used by this file).
norm_sum_le Finset.sum_le_sum Finset.sum_const Finset.card_univ Fintype.card_fin nsmul_eq_mul norm_inv norm_pow Complex.norm_natCast Matrix.inv_eq_right_inv Matrix.smul_mul Matrix.mul_smul smul_smul
mul_inv_cancel₀ Real.rpow_add_one Real.one_le_rpow pow_le_one₀ one_le_pow₀ inv_le_one_of_one_le₀ Nat.one_le_cast mul_le_of_le_one_right mul_div_cancel₀ Matrix.isHermitian_zero hasDerivWithinAt_const
Finset.sum_eq_zero mul_eq_zero_of_right Real.sqrt_sq inv_eq_of_mul_eq_one_right continuousOn_const Complex.I_sq div_le_one Matrix.conjTranspose_nonsing_inv Matrix.nonsing_inv_eq_ringInverse
norm_image_sub_le_of_norm_deriv_le_segment' Real.sq_sqrt Real.sqrt_le_sqrt Real.le_sqrt Nat.floor_le Nat.lt_floor_add_one Real.iSup_le ciSup_le le_ciSup Filter.eventually_all_finset
Real.rpow_pos_of_pos pow_le_pow_left₀ pow_le_pow_right₀ Real.rpow_add inv_anti₀ RBM.Gauss.trace_mul_Eblk RBM.Gauss.trace_Eblk RBM.Ind.norm_gloop_le_loopMax RBM.Univ.mixEntry_greenBlk_eq
RBM.Loop.KLK_one RBM.Univ.GUEPhase.gueK_exists RBM.Univ.GUEPhase.loopGenGUE RBM.Univ.GUEPhase.loopGenGUE_one RBM.Univ.GUEPhase.eq736 RBM.Univ.GUEPhase.supOn RBM.Gauss.Sizes.tendsto_size
RBM.Loop.LoopIdx.length_cutGlueL
Verified absent (RBM3D declarations, script above, 0 hits): `Kbound_prec_uncond`, `Kcal`, `Kgen`, `mSig`, `scaleM`, `kloop_Mt_eq`, `LLf`, `length_cutGlue`; content twins used: `KLK`/`KLgen` (`Loop/KLTree.lean`), `STKloop`, `mSigma`, `loopL`, `Gres`, `STKbound`.

## (d) Open issues and paper-delta candidates
- **T2352a** (statement differences to RBM2D `Hyp_Kt_detDom`/`Hyp_Kt_one`; the same three as T2323a, `docs/reports/T2323-prove.md:235`): (1) `hell : ∀ᶠ n, L^d (1 - t₁) ≤ ilambda²` for `L² (1 - t₁) ≤ 1`; (2) new hypothesis `hKb : sz.STKbound E` (RBM2D has `Kbound_prec_uncond`); (3) `hKinit` identifies `Kt n t₁` with `STKloop` only on `loopOf σ a` (RBM2D: every `I`, with `Kcal`). `Hyp_Kt_one` carries (3) only and concludes `mSigma (E n) s`.
- No other statement difference: the other 11 targets are the source statements under the port map (translation table); instance data is not a statement difference (the window of (b) item 7).
- Open 1: `Hyp_Kt_detDom` takes `hKb`; at the instance it is discharged by `stKbound_holds` (`Loop/KLFinal.lean:243`, imported by the repair); a consumer's `t₁` must satisfy `hell` (zero-mode regime, DECISIONS §142 (5)).
- Open 2 (closed by the repair): the instance of `Hyp_grid` discharges `h0, hM, hq, hF, heG` and `k ≤ gueStop` at `ω₀ = 0` with constants that are finite sums of the left sides; in UN-49 these remain pathwise inputs at `δ = gueDelta`.
- Open 3: file size 1499 lines after the repair (1419 before) against the ticket's 900 / 1050 / 1300 (stop line 1500 not exceeded; the instance part `HypAInst` is lines 1132-1497); the `Loop/KBound` import named by the ticket is unused (compiles without it).

## Repair (round 1, audit `docs/reports/T2352-audit.md`; written Fri Oct  9 00:48:00 UTC 2026)
Repairer model: claude-opus-5-5. Commit 336dec3 on `t/T2352` (parent e7b62ba). Items 1-3 of "Required for resubmission".
```
$ git diff --stat main...t/T2352; wc -l HypA.lean; grep -c -E 'sorry|admit|native_decide|^axiom' HypA.lean; grep -n '^import' HypA.lean
 RBM3D/Universality/GUEPhase/HypA.lean | 1499 +++++++++++++++++++++++++++++++++
 1 file changed, 1499 insertions(+)
    1499 RBM3D/Universality/GUEPhase/HypA.lean
0
6:import RBM3D.Universality.GUEPhase.Proc
7:import RBM3D.Universality.GUEPhase.EntryTailMain
8:import RBM3D.Loop.KBound
9:import RBM3D.Loop.KLFinal
$ lake build RBM3D.Universality.GUEPhase.HypA 2>&1 | grep -E 'HypA|Build completed' | grep -v trace
Build completed successfully (3779 jobs).
$ lake env lean ax.lean   (#print axioms of the 13 targets): all 13 lines identical to (b) above:
  12 x [propext, Classical.choice, Quot.sound]; Hyp_exists_loopOf: [propext, Quot.sound]
$ reg.lean = import RBM3D + import RBM3D.Universality.GUEPhase.HypA + #assert_rbm_axioms; lake env lean reg.lean; echo exit=$?
axiom audit: 10483 theorems, 3076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).   [exit=0]
$ grep -n '^example' HypA.lean   (line numbers only, joined on one line)
1145 1146 1147 1148 1153 1169 1171 1174 1209 1355 1366 1400 1459
$ HypA.lean without the KBound import line: lake env lean | wc -l
       0
$ grep -rn -E '^(private )?(theorem|def|abbrev) (stop0|hKb0|le_dsum|scj_pos|c0_nonneg|ω0|δ0|S0|c0|X2|uj|Hj|Lj|scj|AMj|AFj|AEj|Qj|S0_nonneg|AMsc_nonneg)\b' RBM3D | grep -v GUEPhase/HypA.lean   (condensed; namespace by `grep '^namespace'`)
RBM3D/Path/DifREP1.lean:1339:def ω0 (namespace RBM.Ind.DifREP1Inst)   RBM3D/Graph/LWStein.lean:1907:def S0 (RBM.Graph.LWInstOwx)
RBM3D/Gauss/DominationAt.lean:803:def c0 (RBM.Gauss.DominationAtInst)  RBM3D/Induction/QDriftA.lean:654:def ω0 (QDriftAInst)
```
All new declarations of the repair are `private` in `RBM.Univ.GUEPhase.HypAInst` (no public name added; the four hits are other namespaces).

Item 1, `Hyp_Kt_detDom` instance (HypA.lean:1343-1363): no hypothesis left.
```
private theorem hKb0 : sz0.STKbound Ei :=
  Sizes.stKbound_holds sz0 (le_refl 3) (κ := 1 / 10) (gmax := 1) (by norm_num) one_pos sz0_tendsto ...
example : ∃ Kt : (n : ℕ) → ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ,
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (tw1 n) (tw0 n), ... := by
  obtain ⟨Kt, h1, h2⟩ := exists_Kt
  exact ⟨Kt, Hyp_Kt_detDom sz0 ... (Eventually.of_forall hell_at) hKb0 Kt h1 h2⟩
```
Item 2, `Hyp_grid` instance (HypA.lean:1404-1495): `example := Hyp_grid sz0 Ei tw1 tw0 K64 δ0 Kt0 0 2 ω0 ...`, a closed term
(no binder). Data: `ω0 = fun _ _ => 0` (1405); `δ0 n = 1 + ∑_{k<65} |gueDev .. k ω0|` (1406); `stop0 : gueStop .. δ0 0 ω0 = 64` (1408,
`hittingBtwn` takes its `else` branch since every `gueDev k ω0 < δ0`); `k = 40 ≤ 64` by `rw [stop0]`; `t = t₀`, `m = 2`;
`g1 = g3 ≡ 1`, `g4 ≡ ∑_{j<65} Q_j`, `Λ0 = 1`; `c = c0 = ∑_x |L_0 - K̃_0| + ∑_{k<65} ∑_x A^M_{k,x} / (gueScale_k)⁻¹²`,
`Cf = ∑_{j<65} ∑_x A^F_{j,x}`, `Ce = ∑_{j<65} ∑_x A^E_{j,x}` (the left sides of `h0, hM, hF, heG`, `hq`). `h0, hq, hF, heG`: each left side
is a summand (`Finset.single_le_sum`, private `le_dsum`); `hM`: `A^M_{k,x} = (A^M/s_k) s_k ≤ c0 s_k ≤ c0 (√(u_k-t₁)·sup + s_k)` with
`s_k = (gueScale_k)⁻¹² > 0` (`scj_pos`, `u_k ≤ t₀ < 1`) and `Real.iSup_nonneg`; `hdisc` by `Hyp_Kt_disc` as before. Nondegenerate:
`N = 2097152`, `k = 40 ≥ 1`, `gueStop = K = 64`, `0 < t₀ - t₁`.
Item 3: 1499 lines ≤ 1500 (stop line not exceeded); build, axioms and instance lines re-pasted above.
Verified names added (`lake build` above): `RBM.Gauss.Sizes.stKbound_holds`, `MeasureTheory.hittingBtwn`, `Finset.single_le_sum`,
`Real.iSup_nonneg`, `div_mul_cancel₀`, `le_add_of_nonneg_left`, `le_add_of_nonneg_right`, `Nat.lt_succ_of_le`.
No new paper-delta candidate (instance data only; no statement changed).
