Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 19:17:02 UTC 2026

Sources: RBM2D `Universality/GUEPhase/Drift.lean` (HEAD 9e0f275, 2067 lines); merged `RBM3D/Path/OneStep.lean`; `docs/tickets/checks/T2343-check.lean` (CONTROL: compile exit 0, 19:02:36 UTC).
Targets (mathematics): for Hermitian M, X ~ gueP, |E|<2, WF loop of length k, 0<=u, 0<=Δ, u+Δ<1:
(T1) ‖E Φ_{u+Δ}(M+√Δ X) − Φ_u(M) − Δ·genMatGUE‖ ≤ envConst·Δ^{3/2};  (T2) H_{k+1}=H_k+√(Δ/N)·X_{k+1};
(T3) E[Φ(H_{k+1})|filt k] = ∫Φ(H_k+√Δ X)dgueP;  (T4) drift of T3 vs T1 along the grid (T1 at u=u_k, Δ=gridStep).

### (i) Exponent table  (N := (W L)^d = |Idx d L W| = |Vtx d L W|; k := I.length; η := etaT E (u+Δ); q := η⁻¹)

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | N | (W L)^d (source: (W L)^2) | N >= 1 (L,W NeZero); only this is used, no L–W relation, no d >= 3 | N=1 equality in row 8 (h6) |
| 2 | gueVar_c | diag 1/N, offdiag 1/(2N) (Pins.lean:61, same as RBM2D) | <= 1/N <= 1 | factor N (>= 1) |
| 3 | Σ_c gueVar_c | exactly N+1 (diagonal: 2N coordinates · 1/N = 2; off-diagonal: 2N(N−1) coordinates · 1/(2N) = N−1) | <= 2N (used) | N−1 |
| 4 | E‖blockMat X‖ | <= 2·Σ_c E|ω_c| <= 2·|Coord|·1 = 4N², |Coord| = 2N² | E|ω_c| <= (1+gueVar_c)/2 <= 1 | none claimed (not sharp) |
| 5 | Δ vs τ=√Δ | Δ^{3/2}=τ³ | Δ<=τ and Δ² <= Δτ: from 0<=u, u+Δ<1 ⇒ Δ<1 | 1−Δ |
| 6 | space step | ‖E Φ(M+τX)−Φ(M)−τ² g(M)‖ <= (Λ/3)τ³, Λ=32 N³·N·k(k+1)(k+2)·q^{k+3} (card Idx³·card Vtx) | uses row 3 (2N) · row 4 (4N²) · C₃=4N·k(k+1)(k+2)q^{k+3}: 2N·4N²·4N=32N⁴ | exact product |
| 7 | time step | <= c₁τ³(1/2+4N²), c₁ = N·k(k+1)·q^{k+2} | Taylor (B=c₁) + Lipschitz of J1 (c₁τ‖X‖) + row 4, row 5 | exact |
| 8 | closure | 32N⁴k(k+1)(k+2)q^{k+3}/3 + N k(k+1)q^{k+2}(1/2+4N²) <= 16(k+3)⁴N⁴(1+q)^{k+4} (= envConst d L W E k (u+Δ)) | N>=1, q>=0; steps: N³<=N⁴, N(1/2+4N²) <= (9/2)N⁴ (equality at N=1), k(k+1)(k+2),k(k+1) <= (k+3)³, q^{k+2},q^{k+3} <= (1+q)^{k+3}, (32/3+9/2)(k+3)³ <= 16(k+3)⁴ | coefficient ratio (32/3+9/2)/(16(k+3)) <= 0.316 (k>=0); scan min RHS/LHS = 577 (out below). d enters only through N, so the band constant N⁴ (N=(W L)^d) is kept unchanged |
| 9 | envConst exponent | N^4, N=(W L)^d | statement uses merged `envConst d L W` (OneStep.lean:78) | closure holds for every N>=1, hence every d |
| 10 | crude bound (integrability of Φ on the unit slice) | ‖Φ‖ <= (L W)^d (η⁻¹ (W^d)⁻¹)^k [source: (L W)^2 (η⁻¹ (W⁻¹)²)^k; `W⁻¹^2 ↦ (W^d)⁻¹`] | only boundedness is used (`LoopStep_norm_Phi_le`, LoopStep.lean:172, states exactly this form) | any finite constant |
| 11 | unit-slice law transfer | s=N^{-1/2}: gueUnitVar/N = gueVar (diag 1/N; off 1/(2N)); s² = 1/N; √(Δ/N)·seqXmat = √Δ·Xmat(s·slice) | needs N>0 (W>0, L>=3 from `Sizes`), N=(W L)^d in `Sizes.size` | equality |
| 12 | grid hypotheses of T4 | u_k=t1+kΔ_g >= 0, Δ_g=(t0−t1)/K >= 0, u_{k+1}=u_k+Δ_g<1 | 0<=t1, t1<=t0 (K≠0), gridTime(k+1)<1; `k<K n`, `K n≠0` appear in the statement but the source proof does not use them (binders `_hK _hk`, docstring Drift.lean:2033 "not used by the proof") | 1−u_{k+1} > 0 |

§29 (one line each): (1) time domain: 0<=u, u+Δ<1 (T1); 0<=t1, t1<=t0, gridTime(k+1)<1 (T4) are all stated as hypotheses — closed. (2) case-(ii) boundary 1−ilambda²/L²: not present (no ilambda; GUE grid uses only `Sizes`, no `lam`) — N/A. (3) no polynomial relation L^d<=W^K is used; only N>=1 — closed. (4) all four targets are `∀ n`/`∀ sz`, no `∀ᶠ n` — closed.
External hypotheses: none (the four targets have only deterministic hypotheses; no pin such as Step2LocalPT), so no limit computation is owed.

#### Reuse table (source Drift_ ↦ merged `OneStep_` in RBM3D/Path/OneStep.lean; all 19 are `private` at the lines shown; script `reuse.py`, count 23 as the ticket says)
Reuse (19): norm_one_le 851; w1Lin 1179; continuous_w0 1188, _w1 1194, _w2 1204; J1 1278; J2 1283; Dsp 1288; hasDerivAt_line0 1305, _line1 1314; hasDerivAt_spec0 1336, _spec1 1344; norm_J1_le 1379; norm_J2_le 1391; norm_J1_sub_le 1418; norm_J2_sub_le 1435; norm_blockMat_Xmat_le 1507; card_Idx 1597 (`(W L)^d`); continuous_blockMat 1625.
GUE-specific, port (4): sum_gueVar_le (twin is `OneStep_sum_gvar_le`, g-law), gueP_map_eval (no `OneStep_` twin of that name), integrable_normX 1634 and integral_normX_le 1643 (twins take `PF d L W g`, not `gueP`).
Not in the 23 but needed, outside the `:809-1666` window (port by copy): card_Block (OneStep:1883), norm_Cb_le (:1888), continuous_gloop (:1722), and the §5–§7 helpers. Un-privating may also be needed for `OneStep_w0/w1/w2` (:819/:832/:839) if a proof names them; stage 1b lists the final set in `git diff`. Source `Gsig H z σ` is `Gres H z σ` in RBM3D (`OneStep_J1` body, :1278).

#### d = 2 token table (source §4–§13, script `tok.py`; replacement `d`)
- `(W * L) ^ 2` ↦ `(W * L) ^ d`: source lines 784, 788, 789, 800, 805, 810, 816, 828, 831, 911, 921, 1151, 1617, 1618, 1626, 1629, 1630, and `(d.W n * d.L n) ^ 2` :1843 (↦ `sz.size n` / `(sz.W n * sz.L n) ^ d`).
- `Z2 L` ↦ `Zd d L`: lines 785 (`simp [Idx, Z2, pow_two]` ↦ `card_Idx`), 986, 1005, 1044, 1168, 1172, 1374, 1454, 1475, 1740, 1744, 1751, 1925, 2036.
- crude bound `((L*W)^2) * (η⁻¹ * (W⁻¹)^2)^k`: lines 1754, 1961-1962 ↦ `((L*W)^d) * (η⁻¹ * ((W:ℝ)^d)⁻¹)^k`.
- `^ 2` that stay: `card Idx ^ 2` = N² in |Coord| = 2·|Idx|² (12 lines: 923, 1216, 1234, 1263, 1269, 1273, 1275, 1281, 1527, 1594, 1596, 1598 in the scan; d-free because |Coord|=2·|Idx|²), analytic squares (τ², Δ², y², (b−a)², s², (ω c)², 25 lines), no change.

### (ii) Concrete nondegenerate instances (hypotheses of all four targets)

**Instance A (T1, `DriftInst`):** d=3, L=W=2 (N=64), E=0, u=0, Δ=1/4, M=0 (Hermitian), loop ⟨[true],[a]⟩ (k=1, WF: len σ = len a = 1). Hypotheses: |E|<2, 0<=u, 0<=Δ, u+Δ=1/4<1, WF. η=(3/4)·Im mE(0)=3/4 (mE_im: √(4−E²)/2), q=4/3.
**Instance B (T3, T4, T2):** `SizesInst.sz0` (d=3, L_0=4, W_0=32, N=2097152; `Grid.lean` §GridCheck data), n=0, k=0, E=0, t1=(1−ouZeta(1/20))·9/10=e^{−1/20}·9/10, t0=9/10, K=4, loop (+,−;0,1) (k=2, labels 0≠1 in Z_4³). T2 holds at the same data for every n,k (pure algebra). No `N=0`, no empty index, no collapsed window (Δ_g>0).

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2343/inst.py`  (exact rationals for A; floats for B)
```
N=(W L)^d = 64  |Idx|=(W L)^d, |Coord|=2N^2 = 8192
hyps: |E|<2 True  0<=u True  0<=Delta True  u+Delta<1 True  I=([+],[a]) WF: len sigma=len a=1
eta_v=(1-v)*Im mE(0)= 3/4  q=1/eta= 4/3
tau=sqrt(Delta)= 0.5  Delta<=tau: True
sum_c gueVar = 65 = N+1: True  <= 2N: True  max gueVar = 1/64 = 1/N <=1: True
E||X|| <= 2*sum_c E|w_c| <= 2*|Coord|*1 = 16384  = 4N^2: True
closure k=1: LHS= 3398525585.382716  RHS= 4752955742806.387  RHS/LHS= 1398.5346360931237
envConst*Delta^(3/2) = 594119467850.7983
min RHS/LHS over scan (k=1..7,N in {1,2,64,2097152}, q in {.01,4/3,7.5,1000}) = 577.1003998791375
k=0: LHS = 0  (closure trivial); coefficient bound (32/3+9/2)/(16*3) = 0.3159722222222222
h6 at N=1: N(1/2+4N^2)= 9/2  9/2 N^4= 9/2  (equality: slack 0)
sz0: L= 4 W= 32 N= 2097152 three_le_L: True
t1= 0.8561064820506427  t0= 0.9  0<=t1 True  t1<=t0 True  K!=0 True  k=0<K True
gridStep= 0.010973379487339341  gridTime(1)= 0.867079861537982  <1: True
eta_v= 0.132920138462018  q= 7.523314462132843 ; loop (+,-;0,1): len sigma=len a=2, labels 0!=1 in Z_4^3
envConst*Delta^1.5 = 8.5247e+31  N^4=1.934e+25
Delta<=sqrt(Delta): True
```
Reading: A: N=64, Σ_c gueVar=65<=2N=128, closure RHS/LHS=1398 (>1), envelope·Δ^{3/2} ≈ 5.94e11; B: Δ_g≈0.01097, u_1≈0.8671<1, η_1≈0.1329 (q≈7.52), envelope ≈8.5e31 (N⁴-driven, as in the band `LoopStep_check_drift_sz0`; hypotheses hold, the conclusion is the statement itself).

### Verdicts
- `oneStepEnvelopeGUE` (T1): PASS — every hypothesis holds at A; the exponent closure (row 8) holds for all N>=1, so the band `envConst` (N⁴) is valid with N=(W L)^d; only the d-dependent lines of the token table change.
- `gueH_succ` (T2): PASS — algebra (split `Finset.Icc 1 (k+1)`), no hypothesis; holds at B.
- `condExp_loop_step_gue` (T3): PASS — hypotheses |E|<2, WF, gridTime(k+1)<1 hold at B; law transfer (row 11) is an equality at every N>0.
- `condExp_loop_drift_gue` (T4): PASS — all seven hypotheses hold at B (row 12); T1 applies at u=u_k, Δ=Δ_g because u_{k+1}=u_k+Δ_g.
- (iii) merged `genMatGUE` (Generator.lean:89), `Pgue`/`gueH`/`gueUnit` (Grid.lean:61/77/52), `gueCondExp_freeze` (Markov.lean:109, real-valued, `Y`-frozen against `gueUnit sz`, step k+1) have the shapes the source uses (`gueVar ↦ RBM.Univ.gueVar d L W`, `spectralZ ↦ zt`); no adaptation beyond the token table.

## (a′) Preflight corrections — Thu Oct  8 20:35:34 UTC 2026

The reuse table of (a) lists 19 twins; the port also calls two more twins of `RBM3D/Path/OneStep.lean` inside the `:809-1666` window:
`OneStep_sum_coord` (:1498) and `OneStep_isHermitian_add_realSmul` (:1264); final set 21 (diff below). `OneStep_w0/w1/w2` stay private (not named). No verdict changes.

## (b) Script output (stage 1b), written Thu Oct  8 20:35:34 UTC 2026

### Build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2343, branch t/T2343, HEAD d577e3b)
$ lake build RBM3D.Universality.GUEPhase.Drift 2>&1 | tail -n 2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3773 jobs).
$ lake build   # full library, started 19:26:27 UTC at commit 6fe322f; log mtime (UTC) 20:31:03; tail -n 2 of the log
Build completed successfully (4152 jobs).
EXIT=0
$ grep -c "GUEPhase.Drift" RBM3D.lean   # root import is the hub step at merge
0
(Drift is not in the root, so the full build does not compile it; it was built by the first command after the last edit, a comment-only change of 3 docstring lines.)
$ grep -c error fullbuild.log; grep -nE "sorry|admit|native_decide|^axiom" Drift.lean | wc -l; wc -l < Drift.lean
error lines in full-build log: 0; sorry/admit/native_decide/axiom lines in Drift.lean:        0; Drift.lean lines:     1474
$ grep -o "Built RBM3D.Graph.LWExpCert[A-Za-z0-9]* ([0-9.]*s)" fullbuild.log | tail -n 4   # these are the four slowest modules of the build (checked: sort -rn of all "Built ... (Ns)": 1794, 1741, 749, 611, then 110)
Built RBM3D.Graph.LWExpCertS0 (749s)
Built RBM3D.Graph.LWExpCertS1 (611s)
Built RBM3D.Graph.LWExpCertBS0 (1741s)
Built RBM3D.Graph.LWExpCertBS1 (1794s)
$ section-commit sizes (wc -l printed before each commit): eaf836d 878; 7cd59e5 1309; 6fe322f 1474  (stop size 1900)

### OneStep.lean edit (keyword deletions only)
$ git diff -U0 main...t/T2343 -- RBM3D/Path/OneStep.lean   # checked by script
removed 21 added 21 ; each added line = removed line minus the keyword "private ": True
hunk start lines: 851 1179 1188 1194 1204 1264 1278 1283 1288 1305 1314 1336 1344 1379 1391 1418 1435 1498 1507 1597 1625 ; outside 809-1666: 0
declarations: OneStep_norm_one_le OneStep_w1Lin OneStep_continuous_w0 OneStep_continuous_w1 OneStep_continuous_w2 OneStep_isHermitian_add_realSmul OneStep_J1 OneStep_J2 OneStep_Dsp OneStep_hasDerivAt_line0 OneStep_hasDerivAt_line1 OneStep_hasDerivAt_spec0 OneStep_hasDerivAt_spec1 OneStep_norm_J1_le OneStep_norm_J2_le OneStep_norm_J1_sub_le OneStep_norm_J2_sub_le OneStep_sum_coord OneStep_norm_blockMat_Xmat_le OneStep_card_Idx OneStep_continuous_blockMat
$ git diff --stat main...t/T2343
 RBM3D/Path/OneStep.lean                |   42 +-
 RBM3D/Universality/GUEPhase/Drift.lean | 1474 ++++++++++++++++++++++++++++++++
 2 files changed, 1495 insertions(+), 21 deletions(-)

### Axioms (scratch check_eq.lean = check file + import Drift + 4 equality examples + #print axioms)
$ lake env lean check_eq.lean
oneStepEnvelopeGUE : [propext, Classical.choice, Quot.sound]
gueH_succ : [propext, Classical.choice, Quot.sound]
condExp_loop_step_gue : [propext, Classical.choice, Quot.sound]
condExp_loop_drift_gue : [propext, Classical.choice, Quot.sound]
DriftInst.oneStepEnvelopeGUE_check : [propext, Classical.choice, Quot.sound]
DriftInst.gueH_succ_check : [propext, Classical.choice, Quot.sound]
DriftInst.condExp_loop_step_gue_check : [propext, Classical.choice, Quot.sound]
DriftInst.condExp_loop_drift_gue_check : [propext, Classical.choice, Quot.sound]
error lines in the output: 0; the process exit code printed by the run was EXIT=0
$ equality examples in check_eq.lean (all elaborate):
97:example : T2343Check.T2343_oneStepEnvelopeGUE := @oneStepEnvelopeGUE
98:example : T2343Check.T2343_gueH_succ := @gueH_succ
99:example : T2343Check.T2343_condExp_loop_step_gue := @condExp_loop_step_gue
100:example : T2343Check.T2343_condExp_loop_drift_gue := @condExp_loop_drift_gue

### Registry pre-check (scratch registry.lean = import RBM3D, import Drift, #assert_rbm_axioms; not committed)
$ lake env lean registry.lean; echo EXIT=$?   # first 2 lines of output
axiom audit: 10273 theorems, 3041 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
EXIT=0

### Target statements (extracted from Drift.lean by script stmt.sh: theorem line to `:= by`)
theorem oneStepEnvelopeGUE :
    ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E : ℝ), |E| < 2 → ∀ (I : Loop.LoopIdx (Zd d L)), I.WF →
      ∀ (u Δ : ℝ), 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
        ∀ M : Matrix (Idx d L W) (Idx d L W) ℂ, M.IsHermitian →
          ‖(∫ ω', loopL d L W (blockMat d L W (M + (Real.sqrt Δ : ℂ) • Xmat d L W ω'))
                (zt E (u + Δ)) I ∂(gueP d L W)) -
              loopL d L W (blockMat d L W M) (zt E u) I -
              (Δ : ℂ) * genMatGUE d L W E u M I‖ ≤
            envConst d L W E I.length (u + Δ) * Δ ^ ((3 : ℝ) / 2) := by
theorem gueH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    gueH sz t1 t0 K n (k + 1) ω
      = gueH sz t1 t0 K n k ω
        + (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) : ℂ) •
          Sizes.seqXmat sz n (ω (k + 1)) := by
theorem condExp_loop_step_gue (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ)
    (hE : |E| < 2) {I : Loop.LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (hu1 : gridTime t1 t0 K n (k + 1) < 1) :
    (Pgue sz)[fun ω : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (k + 1) ω))
          (zt E (gridTime t1 t0 K n (k + 1))) I | filt sz k]
      =ᵐ[Pgue sz] fun ω =>
        ∫ x, loopL d (sz.L n) (sz.W n)
          (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω
            + (Real.sqrt (gridStep t1 t0 K n) : ℂ) • Xmat d (sz.L n) (sz.W n) x))
          (zt E (gridTime t1 t0 K n (k + 1))) I ∂(gueP d (sz.L n) (sz.W n)) := by
theorem condExp_loop_drift_gue :
    ∀ {d : ℕ} (sz : Sizes d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ), |E| < 2 →
    ∀ {I : Loop.LoopIdx (Zd d (sz.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
    gridTime t1 t0 K n (k + 1) < 1 →
    ∀ᵐ ω ∂(Pgue sz),
      ‖(Pgue sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n (k + 1) ω'))
              (zt E (gridTime t1 t0 K n (k + 1))) I | filt sz k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n k ω))
              (zt E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUE d (sz.L n) (sz.W n) E
              (gridTime t1 t0 K n k) (gueH sz t1 t0 K n k ω) I‖
        ≤ envConst d (sz.L n) (sz.W n) E I.length (gridTime t1 t0 K n (k + 1))
            * gridStep t1 t0 K n ^ ((3 : ℝ) / 2) := by

### Compiled nonempty instances (namespace RBM.Univ.GUEPhase.DriftInst, Drift.lean §14; statement lines elided where marked)
theorem oneStepEnvelopeGUE_check :
    ‖(∫ ω', loopL 3 2 2 (blockMat 3 2 2 ((0 : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ)
          + (Real.sqrt (1 / 4) : ℂ) • Xmat 3 2 2 ω')) (zt 0 (0 + 1 / 4))
          (DriftInst_loop1 3 2) ∂(gueP 3 2 2)) -
        loopL 3 2 2 (blockMat 3 2 2 (0 : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ)) (zt 0 0)
          (DriftInst_loop1 3 2) -
        ((1 / 4 : ℝ) : ℂ) * genMatGUE 3 2 2 0 0 (0 : Matrix (Idx 3 2 2) (Idx 3 2 2) ℂ)
          (DriftInst_loop1 3 2)‖ ≤
      envConst 3 2 2 0 (DriftInst_loop1 3 2).length (0 + 1 / 4) * (1 / 4 : ℝ) ^ ((3 : ℝ) / 2) :=
  oneStepEnvelopeGUE 3 2 2 0 (by norm_num) (DriftInst_loop1 3 2) (DriftInst_loop1_wf 3 2)
    0 (1 / 4) le_rfl (by norm_num) (by norm_num) 0 Matrix.isHermitian_zero
theorem gueH_succ_check (ω : PathΩ sz0) :
    gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 (0 + 1) ω
      = gueH sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω
        + (Real.sqrt (gridStep DriftInst_t1 DriftInst_t0 DriftInst_K 0 / ((sz0.size 0 : ℕ) : ℝ)) : ℂ)
          • Sizes.seqXmat sz0 0 (ω (0 + 1)) :=
  gueH_succ sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 ω
-- condExp_loop_step_gue_check: statement = the target at sz0, n=0, k=0, E=0, loop (+,-;0,1) (Drift.lean:1431-1446); proof term:
  condExp_loop_step_gue sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 0 (by norm_num)
    (DriftInst_loop2_wf _ 0 1) DriftInst_gridTime_lt
-- condExp_loop_drift_gue_check: statement = the target at the same data (Drift.lean:1449-1466); proof term:
  condExp_loop_drift_gue sz0 DriftInst_t1 DriftInst_t0 DriftInst_K 0 0 0 (by norm_num)
    (DriftInst_loop2_wf _ 0 1) DriftInst_t1_nonneg DriftInst_t1_le_t0 (by norm_num) (by norm_num)
    DriftInst_gridTime_lt
-- data: DriftInst_t1 = fun _ => (1 - ouZeta (1/20)) * (9/10), t0 = 9/10, K = 4, loops (+;0) and (+,-;0,1); labels_sz0 : (0 : Zd 3 (sz0.L 0)) ≠ 1

### Name clashes (new public names; helpers are private with the prefix `Drift_`) and the port source
$ grep -rnwE "oneStepEnvelopeGUE|gueH_succ|condExp_loop_step_gue|condExp_loop_drift_gue|DriftInst|oneStepEnvelopeGUE_check|gueH_succ_check|labels_sz0" RBM3D RBM3D.lean | grep -v "^RBM3D/Probe/" | grep -v "GUEPhase/Drift.lean" | wc -l
       0
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/Drift.lean
9e0f275
(empty diff stat: the source file is unchanged between 9e0f275 and HEAD)

### Narrative (script output above is the evidence)
1. Deliverables: `RBM3D/Universality/GUEPhase/Drift.lean` (1474 lines, 70 lines starting with `private`, instances in `RBM.Univ.GUEPhase.DriftInst`) and 21 keyword deletions in `RBM3D/Path/OneStep.lean` (diff checked above: every hunk is a line minus `private `, all inside `:809-1666`).
2. Port source: RBM2D `Universality/GUEPhase/Drift.lean`, commit 9e0f275 (= HEAD, diff stat empty), 2067 lines. Map (source line range to file line range): §1-§3 `:60-707` not copied (reused: the 21 `OneStep_` twins); §4 `:709-932` to `:67-214` (law-free items reused, GUE items ported); §5 `:934-1142` to `:215-425`; §6 `:1144-1326` to `:426-609`; §7 `:1328-1634` to `:610-917` (`oneStepEnvelopeGUE` at `:756`); §8-§13 `:1636-2065` to `:918-1348`; instances `:1349-1472` (new).
3. Method: the source text was renamed by regex scripts (scratch `tr.py`, `tr2.py`: the ticket's port map `Z2 L` to `Zd d L`, `Idx L W` to `Idx d L W`, `BlockIndex` to `Vtx`, `gloop` to `loopL d L W`, `d : Sizes` to `sz : Sizes d`, `d.L n` to `sz.L n`, `spectralZ` to `zt`, `Gsig` to `Gres`, `(W L)^2` to `(W L)^d`, `RBM.Endpoints.gueP/gueVar` to `RBM.Univ`), then compiled and corrected by hand.
4. `d`-dependent lines changed (all in (a)(ii) token table): `Drift_one_le_N` (`N = (W L)^d >= 1`), `Drift_gueVar_diag/offDiag/le_inv/le_one`, `Drift_sum_gueVar_le` (via `OneStep_card_Idx`), `Drift_integral_normX_le` (`4 N^2`, `N = (W L)^d`), `Drift_size_pos`, `Drift_unitVar_div` (`hsz` is `rfl` at `Sizes.size = (W L)^d`), `Drift_norm_Phi_le` (crude bound `(L W)^d (|Im z|^-1 (W^d)^-1)^k`). `|Coord| = 2 |Idx|^2` and `Drift_closure` (any `N >= 1`) are `d`-free; `envConst d L W` is the merged band constant (`N^4`), unchanged.
5. Adaptations beyond the token table: `Sizes.size_eq` (source `Drift_size_pos`) is absent in RBM3D (`Sizes.size` is the def `(W L)^d`): the proof is `unfold Sizes.size; positivity`. `blockMat`, `Xmat`, `Xentry`, `Eblk`, `coordinateMatrix` take explicit `d L W`; `simp [blockMat]` lists keep the bare constant. `Drift_Phi` takes `d L W` explicitly (as `LoopStep_Phi`). `Drift_integral_normX_le` needs `(d := d)` at its two uses. The private `Drift_` copies of `LoopStep_herm`, `LoopStep_Phi`, `LoopStep_continuous_Phi`, `LoopStep_norm_Phi_le`, `LoopStep_isHermitian_add_smul` (`LoopStep.lean` is outside the allowed edit scope) and `Drift_condExp_freezeC` (complex-valued freeze for `gueCondExp_freeze`) are ported as in the source; so are `Drift_continuous_gloop/J1/J2`, `Drift_card_Block`, `Drift_norm_Cb_le` (their twins lie outside `:809-1666`).
6. Generality: all four targets are stated for every `d`, `L`, `W` (`NeZero`) or every `sz : Sizes d`, with no `3 <= d`; they are the general statements, not special cases. No target has an external hypothesis, so no limit check is owed ((a), §29 lines).
7. Instances (DriftInst, `:1349-1472`): `oneStepEnvelopeGUE_check` at `d = 3`, `L = W = 2` (`N = 64`), `E = 0`, `u = 0`, `Delta = 1/4`, `M = 0`, loop `(+; 0)`; `gueH_succ_check`, `condExp_loop_step_gue_check`, `condExp_loop_drift_gue_check` at `sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `N = 2097152`), `n = 0`, `k = 0`, `E = 0`, `t1 = (1 - ouZeta(1/20)) * 9/10`, `t0 = 9/10`, `K = 4`, loop `(+,-; 0, 1)`, `labels_sz0 : 0 != 1`. Every deterministic hypothesis is discharged (`by norm_num`, `rfl`, `DriftInst_t1_nonneg`, `DriftInst_t1_le_t0`, `DriftInst_gridTime_lt`); no hypothesis remains.
8. The Lean statements equal the ticket's check texts (the four `example`s above elaborate with no error); binder style of the source is kept for `gueH_succ` and `condExp_loop_step_gue` (section variables `{d : ℕ} (sz : Sizes d)`), `∀`-form for the other two, as in the check file.

## (c) Verified Mathlib names used (each `#check @name` in scratch `names.lean` after `import RBM3D.Universality.GUEPhase.Drift`, 0 errors; names occurring in `Drift.lean`)
- `Measure.infinitePi_map_eval`
- `memLp_id_gaussianReal`
- `variance_fun_id_gaussianReal`
- `variance_eq_integral`
- `integral_map`
- `integrable_map_measure`
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
- `ContinuousLinearMap.comp_condExp_comm`
- `Measure.eq_infinitePi`
- `Measure.infinitePi_pi`
- `Measure.infinitePi_map_pi`
- `gaussianReal_map_const_mul`
- `Real.sqrt_div'`
- `inv_le_one_of_one_le₀`
- `Real.exp_le_one_iff`
- `Real.sq_sqrt`
- `integral_finsetSum`
- `integrable_finsetSum`
- `norm_integral_le_of_norm_le`
- `memLp_top_of_bound`
- `Integrable.bdd_mul`
- `Measure.map_map`
- `Nat.one_le_pow`
- `Matrix.isHermitian_add_transpose_self`
- `integral_re`
- `integral_im`
- `NNReal.coe_injective`
- verified absent: `RBM.Gauss.Sizes.size_eq` (`Unknown constant`, from the first compile of the source `Drift_size_pos`); `isHermitian_add_transpose_self` unqualified is unknown (it is `Matrix.isHermitian_add_transpose_self`, reached through `open Matrix`).

## (d) Open issues and paper-delta candidates
- No open issue on the four targets; all deterministic hypotheses are discharged in the instances; none of the targets has an external hypothesis.
- Paper-delta candidates: none new (no Lean/paper statement difference was introduced; `envConst` is the merged band constant). Carried from the pin: `K n ≠ 0` and `k < K n` are hypotheses of `condExp_loop_drift_gue` but the proof does not use them (binders `_hK`, `_hk` in the source, `Drift.lean:2033` there; in the file the `intro` names are `_hK _hk`).
- For the hub: `OneStep.lean` changed (21 keywords), so the full library build recompiled 4152 jobs (started 19:26:27 UTC, log last written 20:31:03 UTC; the four slowest modules are in (b)). The root import `import RBM3D.Universality.GUEPhase.Drift` is the hub's step; the temporary registry pre-check above passed with it.
- Consumers UN-36/37/38/40 can call `RBM.Path.OneStep_J1/J2/Dsp/...` (now public) and the four targets without further edits.
