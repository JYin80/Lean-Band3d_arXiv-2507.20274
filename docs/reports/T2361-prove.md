Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct  9 04:04:00 UTC 2026

Sources: `S:N` = RBM2D `Universality/GUEPhase/PathBounds.lean:N` (9e0f275, 532 lines); paths below are relative to `RBM3D/` (main 8d76de9 + eb56169). Notation: `x = 1 - t₁`, `A_n = 1 + 2 lam_n²`, `Λ_u = (N η_u)⁻¹`, `N = (W L)^d`. `Bctl n t = W^{-d} Bparam d L lam t 0` (`Defs/Sizes.lean:214`).

### (i) Exponent table and statement points

| # | quantity | value (d = 3, `sz0`, n = 0 / limit) | constraint | slack |
|---|---|---|---|---|
| 1 | κ, 𝔠, 𝔡, τ_U, n₀ | 1/10, 1/6, 1/10, 1/1000, 2 | all > 0, n₀ ≥ 2; `sz0.Admissible 𝔠 𝔡` (`Defs/Sizes.lean:331`) | script cols 2-3 True, n ≤ 10^6 |
| 2 | grid `K = (N+1)^{32n₀+64}` | exponent 128, log10 K = 809 | `HypB_ev_grid`: N ≥ 3(2n₀)^6 + (2n₀)^3 + 1 = 12353 | N(0) = 2097152, factor 170 |
| 3 | `gueDelta = N^{-τ_U/4}` | N^{-1/4000} | `δ ≤ N^{-c₀}`, c₀ = τ_U/4 (equality); `HypB_ev_delta`: δ ≤ Im m/2, i.e. N^{τ_U/4} ≥ 4/√(2κ) | eventual: log10 N ≥ 3806 |
| 4 | τ₁ = min(τ,τ_U)/16 | τ₁ < τ; 2τ₁ − τ_U/2 ≤ −3τ_U/8 = −3/8000 | `hsmallN`: N^{2τ₁−τ_U/2} ≤ 1/32; `h4N`: 2 ≤ N^{τ−τ₁} | exponent slack 3/8000; at τ = τ_U: log10 N ≥ 4014 resp. 321 |
| 5 | `hbig` constant (new vs S:252) | 2 + 2^{2n₀} + (3 + 4A)(2n₀)² = 12930 with A ≤ 1 + 2𝔡⁻² = 201 (S: 2+16+7·16 = 130) | `HypB_fixed (hbig)`: ≤ N^{τ/2}; A_n bounded needs `lam ≤ 𝔡⁻¹` of `WO` | at τ = τ_U: log10 N ≥ 8223 |
| 6 | `Ce = (2l) A N^{τ/2} N` | S: `4(2l) N^{τ/2} N` | `hCe`: Ce ≤ 4 A m² N^{τ/2} N | factor 4m ≥ 4 |
| 7 | `h730` | (t₀−t₁)/(N^{-τ_U} η_{t₀}) = 1/2 (all n) | ≤ 1 | factor 2 |
| 8 | `hscale` | (Nη_{t₀})⁻¹/N^{-τ_U} = 0.9855 (n=0), 0.7686 (n=10^6) | ≤ 1 | exponent τ_U (`1 - t₀ = N^{-1+2τ_U}`) |
| 9 | `hell` `L^d x ≤ lam²` | ratio 0.192 (n=0), 0.0245 (n=1), 2.9e-19 (n=10^6) | ≤ 1; replaces S:97 `L²(1−t₁) ≤ 1` | factor 5.2 at n=0 |
| 10 | `hell1` `L^d x ≤ 1` | 4.7e-5 (n=0) | ≤ 1 (`Bounds_path hellN`, `BoundsA.lean:509`) | not implied by 9: WO gives only `lam ≤ 𝔡⁻¹ = 10` |
| 11 | conversion `N η_{t₁} Bctl(t₁)` (replaces `scaleM = gueScale`, S:95) | 1 + L^d x/(lam²+x) = 1.1915 (n=0); → 1 (n = 10^3, 10^6, 10^9) | ≤ 2 ⇔ L^d x ≤ lam² + x; `hell` suffices (`HypA.lean:494`, private) | 0.81 at n=0 |
| 12 | `STWB(K)/Bctl` | 1.0 for K ∈ {0,1,2,10,10^6} | ≤ 1: `((K+1)^{d−2})⁻¹ ≤ 1`, d ≥ 2 | equality at K = 0 |
| 13 | step-0 loops: level s ⇐ STLK at s/2, `2^k ≤ N^{s/2}`, k ≤ 2n₀ | 2^4 = 16 | at s = τ/2, τ = τ_U: N^{τ_U/4} ≥ 16 | eventual: log10 N ≥ 4816 |
| 14 | step-0 local: level s ⇐ STLocalEntry at s, `2 ≤ N^s` (‖x‖² ≤ N^s Bctl ≤ 2N^s Λ) | s = τ₁ = τ_U/16 | N^{τ₁} ≥ 2 | eventual: log10 N ≥ 4816 |
| 15 | union counts S:105-126 (`N^{k+1}`, `N²`) | not needed | `STLK`, `STLocalEntry` are `Prec` (union inside P), S's `InitLK/InitLocal` are `PerTimeDomAt` | rows dropped |

The `log10 N ≥ …` entries are thresholds of `∀ᶠ n` conclusions (up to 10^8223); the instance (ii) discharges hypotheses only and claims no conclusion at a fixed n.

Statement points of the ticket (all verdicts below are for the targets):
* **S(i) `hB : MLConcl d E t1` ↦ `hLK : sz.STLK E t1`, `hLoc : sz.STLocalEntry E t1`.** No FAIL. S uses only `hB.1.1 = InitLK` (S:236, 332) and `hB.1.2.2 = InitLocal` (S:500); `InitDecay`, the loop bound `hB.2` are unused, so `STLmax`, `STDecay`, `STExp2` of `UNMLOut` (`Universality/Pins.lean:432`) are not consumed. Loops: `Lloop = loopFine (seqHflow …) (zt E t) σ a = loopL (blockMat …) (loopOf σ a)` (`Loop/GLoopFlow.lean:110,158`, `loopM_eq_loopL`); `gueH … 0 ω = seqHflow … (t1 n) (ω 0)` and `(Pgue).map (· 0) = seqP` (`Grid.lean:542`); `gridTime … 0 = t1 n` (`simp [gridTime]`); `hKinit` gives `Kt n t1 (loopOf σ a) = STKloop`. `STLK`: `‖L − STKloop‖ ≺ Bctl^k`, and row 11 gives `Bctl ≤ 2Λ_{t₁}`, so `≺ (Nη_{t₁})^{-k}` (row 13), the input `h0` of `HypB_fixed` and the `lk` field at step 0. Local: `Gt … true = green` (`cont_Gres_true_eq_green`, `Induction/ContinuityNet.lean:430`), `STGM = (green − mE•1)_{xy}`, `STLocalEntry`: `‖STGM‖² ≺ STWB(K)` ≤ Bctl ≤ 2Λ (rows 11-12), so `‖(G−m)_{xy}‖ ≺ Λ^{1/2}` (row 14), the hypothesis `hinit` of `BoundsACheck.highProbAt_hD` (`BoundsA.lean:724`). S's `scaleM = W² ℓ² η` with `ℓ_{t₁} = L` becomes the inequality of row 11 (finding F1).
* **S(ii)** `hell ↦ ∀ᶠ n, L^d(1−t₁) ≤ lam²` plus `hKb : sz.STKbound E`, `hKinit` on `loopOf σ a` with `STKloop`, as `Hyp_Kt_detDom` (`HypA.lean:690`) and `gueKproc_detDom` (`ProcK.lean:553`) (T2352a). PASS.
* **S(iii)** `hE ht1 ht10 ht0` stay `∀ n` (as S); good data is the consumer's (T2356 F2); `STLK`, `STLocalEntry` are `∀ τ D ∀ᶠ n`, so finitely many bad `n` do not matter.
* **S(iv) d = 2 tokens** (script `tokens.py` on S, 533 lines): `d.size/L/W` 85 lines, `Z2` 14, `spectralZ/M` 8, `gloop/blockMat` 3, `KLoop.Kcal` 4, `scaleM/ellT_eq_L` 5, `MLConcl/InitLK/InitLocal` 13, `Admissible 𝔠 d` 5, `L² (1−t₁)` (hell) 6, count tokens (`N^{k+1}`, `N²`, `flucAvg_card`) 11+2, `Pgue/gueH/… d` 67, constant `7(2n₀)²` 2. Map: `d ↦ sz : Sizes d`, `Z2 ↦ Zd d`, `spectral ↦ zt/mE`, `gloop … (blockMat M) ↦ loopL d L W (blockMat d L W M)`. Dimension-specific: hell (row 9), `scaleM` (row 11), counts (row 15), hbig (row 5).
* **S(v) MISS names:** `GoodEvent_gridTime_zero` re-derive 1 line (`simp [gridTime]`; private twin `BoundsA.lean:276`); `Kcal` ↦ `STKloop` (`Induction/Defs.lean:64`); `InitLK` ↦ `STLK` (:104); `InitLocal` ↦ `STLocalEntry`; `MLConcl` no twin, replaced by `hLK`, `hLoc`; `one_le_rpow` is Mathlib `Real.one_le_rpow` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:678`); `scaleM` re-derive as row 11 (private `Hyp_Bctl_le` `HypA.lean:494`, `ProcK_Bctl_le`: ≈ 45 lines, re-derive privately; `Hyp_im_le_one` 4 lines).
* **S(vi) DECISIONS §29:** (1) time domain `0 ≤ t₁ ≤ t₀ < 1` as `∀ n` hypotheses, `x > 0` from `ht10`, `ht0`; (2) boundary `L^d(1−t₁) ≤ lam²` is hypothesis `hell` (row 9, no negative time: `t₁ < 1`); (3) no `L^d ≤ W^K` relation is used here (entry bound takes `hadm`); (4) `hell`, `h730`, `hscale` `∀ᶠ n`, time facts `∀ n`; (5) `Prec` vs `PrecPT`: the pins are `Prec` (row 15); (6) `lam ≤ 𝔡⁻¹`, `N → ∞` come from `hadm` (rows 1, 5), `0 < lam` is not used; (7) scale `N η` vs `Bctl`: row 11.

Findings (statement differences, paper-delta candidates T2361a/b/c, to the report (d)):
* **F1 (T2361a)** `hB` ↦ `hLK`, `hLoc` (S(i)); `scaleM` ↦ `Bctl` via row 11, constant 2 absorbed into `N^{τ}`.
* **F2 (T2361b)** `gueGrid_pathBounds` needs an extra hypothesis `hell1 : ∀ᶠ n, L^d(1−t₁) ≤ 1`: merged `Bounds_path` has `hellN : L^d(1−t₁) ≤ 1` (`BoundsA.lean:509`), written for "`≤ ilambda² ≤ 1`" (`BoundsA.lean:37-39`), but `(eq:WO)` gives only `lam ≤ 𝔡⁻¹` (`Defs/Sizes.lean:164`; paper `1_2:362-363`, footnote `1_2:372`), so `hell` does not imply it. `gueBds_h745E`, `gueBds_h746` do not need it. T2356 design (`docs/reports/T2356-design.md` §2: `L^d η_Q W^{4𝔡/3} = ilambda W^{-d/2+𝔡}`) (with `1 − t₀ ≤ η_Q/c`, `ζ ≤ N^{-1+τ_U}`, `lam ≤ 𝔡⁻¹`) are the ingredients for `L^d(1−t₁) ≤ 1` on the consumer side; not recomputed here.
* **F3 (T2361c)** S's `hsz` of `gueBds_h746` ↦ `hadm : sz.Admissible 𝔠 𝔡` (needs `lam ≤ 𝔡⁻¹` for row 5), `3 ≤ d`; `h745E`, main theorem as S: `h𝔠`, `hadm` ↦ `hd : 3 ≤ d`, `hadm`.

### (ii) One concrete nondegenerate instance

Data (merged `ProcKInst`, `ProcK.lean:740-963`, and `SizesInst.sz0`, `Defs/Sizes.lean:260`): d = 3, `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = 2^{21}(n+1)^{18}` (n = 0: L = 4, W = 32, lam = 1/64, N = 2097152), E ≡ 0 (Im m = 1), κ = 1/10, 𝔠 = 1/6, 𝔡 = 1/10, τ_U = 1/1000, n₀ = 2, `1 − t₀ = N^{-1+1/500}`, `t₀ − t₁ = N^{-τ_U}(1 − t₀)/2`. Hypotheses of `gueGrid_pathBounds`: `hadm` (cols 2-3), `hE`, `ht1`, `ht10`, `ht0` (col 4), `h730` (row 7), `hscale` (row 8), `hell` (row 9), `hell1` (row 10), `hKb` (merged `stKbound_holds`, `Loop/KLFinal.lean:243`, with `0 < lam ≤ 1/64`, `|E| = 0 ≤ 2 − κ`), `Kt`, `hKinit`, `hK` (`gueK_exists`, as `ProcKInst` and T2352), `hLK`, `hLoc` (external pins: `UNMLOut`, owed by ST-6; stay hypotheses of the example).
```
$ python3 <scratch>/T2361/inst_numbers.py     (mpmath, 400 digits; E = 0, d = 3)
n | W>=N^c | lam in [W^(-3/2+dd),1/dd] | 0<=t1<t0<1 | h730 ratio | hscale ratio | hell L^3(1-t1)/lam^2 | L^3(1-t1) | N·eta·Bctl(t1) | max_K STWB/Bctl
0 True True True 0.5 0.985549 0.192109 4.69016e-5 1.191534 1.0
1 True True True 0.5 0.973329 0.0245196 1.46148e-9 1.0245184 1.0
10 True True True 0.5 0.943916 0.000155153 1.20695e-20 1.0001552 1.0
1000 True True True 0.5 0.870303 2.36137e-10 5.69634e-50 1.0 1.0
1000000 True True True 0.5 0.768561 2.92938e-19 7.15173e-95 1.0 1.0
n=0: 1-t0= 4.9092297e-7  1-t1= 7.3283737e-7  t0-t1= 2.419144e-7  Bctl(t1)= 0.77529846  2/(N eta_t1)= 1.3013451
hbig constant d>=3 (lam<=1/dd=10, A=1+2*lam^2=201.0): 12930.0 ; RBM2D: 130
HypB_ev_grid threshold 3(2n0)^6+(2n0)^3+1 = 12353  <= N(0)=2097152: True
```
The window is genuine (0 < t₁ < t₀ < 1, t₀ − t₁ = 2.4e-7 at n = 0), `N = 2097152`, no collapsed window.

**External hypotheses, limit computation (TEAM §8 lesson 14), k = 1 and the entry, bulk E = 0.** `STLK` at k = 1 says `|L^{(1)} − m| ≺ Bctl(t₁)`; the consumer wants `(Nη_{t₁})^{-1}`; the ratio `N η_{t₁} Bctl(t₁) = 1 + L^d x/(lam² + x)` (exact for E = 0, `Im m = 1`, `Bparam` at K = 0) is 1.1915, 1.0245, 1.00016 at n = 0, 1, 10 and → 1.0 at n = 10^3, 10^6, 10^9 (script lines `limit check`), always ≤ 2: both sides have the same order, no normalisation factor is lost. `STLocalEntry` at x = y, K = 0: `‖G_xx − m‖² ≺ Bctl ≈ Λ_{t₁}`, i.e. `‖G − m‖ ≺ (Nη)^{-1/2}`, the standard local-law scale of `GUEPathBounds.localLaw` (`Grid.lean:97`): the limits agree.

### Verdicts

* `gueBds_h745E`: **PASS** (rows 2-6, 9, 13; differences F1, F3).
* `gueBds_h746`: **PASS** (rows 2, 4-5, 13; F1, F3).
* `gueGrid_pathBounds`: **PASS** (rows 1-14 and instance (ii); differences F1-F3; with `hell1` added the hypothesis set is nonempty, as shown). The `MLConcl` statement point S(i) is **not** a FAIL: `STLK ∧ STLocalEntry` at `t₁` with `hell` give the step-0 inputs.

## (a′) Preflight corrections — Fri Oct  9 04:22:44 UTC 2026
No verdict of (a) changes.  Three differences between (a) and the file, none a mistake in a number:
* F3 lists `3 ≤ d` next to `gueBds_h746`; that theorem does not use it (no `hd` in the file); `hd : 3 ≤ d` is in `gueBds_h745E` and `gueGrid_pathBounds` only.
* (a)(ii) names the window `1 − t₀ = N^{-1+1/500}`, `t₀ − t₁ = N^{-τ_U}(1 − t₀)/2`; the instances in (b) use the window of `HypAInst` (T2352): `1 − t₁ = ilambda²/L^d`, `t₀ − t₁ = y/(N+1)` (algebraic proofs for all `n`); the rows of (a)(i) (exponents, `hbig`, `Ce`) are unchanged.
* (a)(i) row 12 writes `d ≥ 2` for `STWB ≤ Bctl`; `PathBounds_STWB_le` needs no hypothesis on `d` (`(K+1)^{d-2} ≥ 1` in ℕ-subtraction).

## (b) Script output — Fri Oct  9 04:22:44 UTC 2026 (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2361`, branch `t/T2361`, commit `f9cce14`)

**Build, registry pre-check, axioms** (logs of the final commit; exit codes)
```
$ lake build RBM3D.Universality.GUEPhase.PathBounds | tail -1 ; grep -c 'PathBounds.lean' <log>   (messages mentioning the file)
Build completed successfully (3825 jobs).
0
$ lake build | tail -1   (the root does not import the file yet: hub at merge)
Build completed successfully (4173 jobs).
$ lake env lean RBM3D/Universality/GUEPhase/PathBounds.lean | wc -l
0
$ registry pre-check, scratch file outside the worktree: import RBM3D / import RBM3D.Universality.GUEPhase.PathBounds / #assert_rbm_axioms ; lake env lean <file>
exit codes: mod exit=0; full exit=0; axioms exit=0; registry exit=0; names exit=0; alone exit=0 lines=       0
axiom audit: 10545 theorems, 3090 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ #print axioms of the three targets (scratch file importing the module)
'RBM.Univ.GUEPhase.gueBds_h745E' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueBds_h746' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueGrid_pathBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE 'sorry|admit|native_decide|^axiom|^ *axiom ' RBM3D/Universality/GUEPhase/PathBounds.lean | wc -l   ->  0
```

**Sizes and the stop rule** (ticket sizes 550 / 700 / 950, stop 1100; `git show <commit>:<file> | wc -l`)
```
b146001 04:10:19 UTC lines=     301
345baf3 04:11:44 UTC lines=     529
155de99 04:12:39 UTC lines=     669
6266d91 04:15:50 UTC lines=     903
f9cce14 04:20:49 UTC lines=     903
```

**Target statements** (`python3 -I extract.py RBM3D/Universality/GUEPhase/PathBounds.lean gueBds_h745E gueBds_h746 gueGrid_pathBounds`, verbatim)
```lean
-- gueBds_h745E: lines 330-351
theorem gueBds_h745E (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (_hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hLK : sz.STLK E t1) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : TimeIcc t1 t0 n × {m : ℕ // m ∈ Set.Icc 2 (2 * n0) ∧ Even m}) ω =>
        gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n p.2.1 p.1 ω)
      (fun n p ω => rhs745G ((sz.size n : ℕ) : ℝ) (etaT (E n)) (t1 n)
        (fun m t => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n m t ω)
        (fun m t => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω) p.2.1 p.1) := by
-- gueBds_h746: lines 433-454
theorem gueBds_h746 {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hLK : sz.STLK E t1) :
    StochDomAt (Pgue sz) sz.size
      (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω =>
        gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n p.2 p.1 ω)
      (fun n p ω => rhs746G ((sz.size n : ℕ) : ℝ) (etaT (E n)) (t1 n)
        (fun m t => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n m t ω)
        (fun m t => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω) p.2 p.1) := by
-- gueGrid_pathBounds: lines 550-567
theorem gueGrid_pathBounds (hd : 3 ≤ d) {𝔠 𝔡 κ τU : ℝ} (hadm : sz.Admissible 𝔠 𝔡)
    (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ}
    (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
    (hell1 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1)
    (hKb : sz.STKbound E)
    (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a)
    (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF →
      1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I)
        (Set.Icc (t1 n) (t0 n)) t)
    (hLK : sz.STLK E t1) (hLoc : sz.STLocalEntry E t1) :
    GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt := by
```

**Compiled nonempty instances** (`sed -n 878,899p RBM3D/Universality/GUEPhase/PathBounds.lean`; data and discharged hypotheses in the docstring of `PathBoundsInst`, lines 669-681)
```lean
example (hLK : sz0.STLK Ei tw1) :=
  gueBds_h745E sz0 (le_refl 3) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK

/-- **`gueBds_h746` at `sz0`** (same data; no `hd`, no entry bound). -/
example (hLK : sz0.STLK Ei tw1) :=
  gueBds_h746 sz0 (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK

/-- **`gueGrid_pathBounds` at `sz0`** (same data, plus `hell1`): `GUEPathBounds` for the window,
`n₀ = 2`, the band K-loops `Kt0`; `hLK`, `hLoc` (conclusions of `UNMLOut`) are hypotheses. -/
example (hLK : sz0.STLK Ei tw1) (hLoc : sz0.STLocalEntry Ei tw1) :
    GUEPathBounds sz0 Ei tw1 tw0 (gueGridK sz0 2) 2 Kt0 :=
  gueGrid_pathBounds sz0 (le_refl 3) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := 1 / 10) (τU := 1 / 1000)
    sz0_admissible (by norm_num) (by norm_num) 2 le_rfl (E := Ei) (t1 := tw1) (t0 := tw0)
    hE_at tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at)
    (Eventually.of_forall hscale_at) (Eventually.of_forall hell_at)
    (Eventually.of_forall hell1_at) hKb0 Kt0 Kt0_init Kt0_deriv hLK hLoc
```
Numbers of the window (`python3 inst_window.py`, mpmath, `E = 0`, `d = 3`, `sz0`; `1 − t₁ = y`, `t₀ − t₁ = y/(N+1)`, `1 − t₀ = yN/(N+1)`):
```
n | N | L^3(1-t1)/lam^2 | L^3(1-t1) | h730 ratio | hscale ratio | N eta_t0 | y<1 (0<t1)
0 2097152 1.0000 2.4414e-04 4.838e-07 0.126833 8.0000 True
1 5.498e+11 1.0000 5.9605e-08 1.869e-12 0.016053 64.0000 True
10 1.166e+25 1.0000 7.7791e-17 9.086e-26 0.000099 10648.0000 True
1000 2.135e+60 1.0000 2.4123e-40 5.381e-61 0.000000 8024024008.0000 True
1000000 2.097e+114 1.0000 2.4414e-76 6.204e-115 0.000000 8000024000024000512.0000 True
n=0: 1-t1 = 3.814697e-06  t0-t1 = 1.818989e-12  1-t0 = 3.814695e-06
N*y = 8.0 ; (2(n+1))^3 = 8 ; N^(1/1000) = 1.014663 <= 2(n+1) = 2
```

**Name clash, ports, scope**
```
$ grep -rnE 'gueBds_h745E|gueBds_h746|gueGrid_pathBounds|PathBoundsInst' RBM3D/ | grep -v Probe/ | grep -v 'RBM3D/Universality/GUEPhase/PathBounds.lean:' | wc -l   ->  0
$ declarations (def|theorem|lemma|structure|abbrev|instance) named GoodEvent_gridTime_zero|Kcal|InitLK|MLConcl|InitLocal|scaleM in RBM3D/ outside Probe/ | wc -l   ->  0
$ git diff --stat main...t/T2361
 RBM3D/Universality/GUEPhase/PathBounds.lean | 903 ++++++++++++++++++++++++++++
 1 file changed, 903 insertions(+)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; ... diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/PathBounds.lean | wc -l ; ... status --short -- (same file) | wc -l ; wc -l (source, port)
9e0f275
       0
       0
     532
     903
```

**Translation table** (S = RBM2D `Universality/GUEPhase/PathBounds.lean` 9e0f275; P = the file; token map in the docstring of P, lines 33-37).
| S:line | P:line | change |
|---|---|---|
| `PathBounds_map_eval0` 67, `_step0_le` 74, `_gueH_zero` 80 | 73, 81, 87 | types only (`Pgue sz`, `Sizes.seqP sz`, `Sizes.seqHflow sz`) |
| `PathBounds_llErr_eq` 86 | `PathBounds_Gres_true` 168, `_STGM_eq` 173, `_Lloop_eq` 160 | `STGM`, `Lloop` of the band flow are `(G − m)_{xy}`, `loopL … (blockMat …) (loopOf σ a)` |
| `PathBounds_scale_eq` 96 (`scaleM = gueScale` at `ℓ_{t₁} = L`) | `_Bctl_le` 97, `_Bctl_nonneg` 142, `_STWB_le` 147 | replaced by `Bctl ≤ 2 (N η)⁻¹` under `hell` (T2361a) |
| `_card_loops` 106, `_card_idx` 123 | dropped | the union is inside `Prec` (`STLK`, `STLocalEntry`) |
| `PathBounds_init_loops` 137, `_init_local` 171 | 188, 247 | `InitLK`, `InitLocal` of `MLConcl` ↦ `hLK`, `hLoc`; level `τ/2` with `2^k ≤ N^{τ/2}`, level `τ` with `2 ≤ N^τ` |
| `gueBds_h745E` 212 | 330 | `h𝔠`, `Endpoints.Admissible 𝔠 d` ↦ `hd : 3 ≤ d`, `hadm : sz.Admissible 𝔠 𝔡`; `hell` `L²(1−t₁) ≤ 1` ↦ `L^d(1−t₁) ≤ lam²`; `+ hKb`; `hKinit` on `loopOf σ a` with `STKloop` (for `Kcal`); `hB` ↦ `hLK`; proof: `hbig` `7` ↦ `3 + 4A`, `Ce = (2l) A N^{τ/2} N` |
| `gueBds_h746` 309 | 433 | `hsz` ↦ `hadm` (no `hd`); `hell`, `hKb`, `hKinit`, `hLK` as above; `Ce = m N` unchanged, `hCe` with `A` |
| `gueGrid_pathBounds` 416 | 550 | as `gueBds_h745E`, `hB` ↦ `hLK` and `hLoc`; `+ hell1` (T2361b); conclusion `GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt` (`Grid.lean:89`); `gueKproc_detDom` (`ProcK.lean:553`) takes `hscale hell hKb` |

**Narrative** (prover claude-sonnet-5-5)
1. One new file, 903 lines (ticket 550 / 700 / 950, stop 1100 not reached), four section commits plus one linter fix: step-0 laws and conversion (70-298), `gueBds_h745E`, `gueBds_h746` (302-526), `gueGrid_pathBounds` (530-665), `PathBoundsInst` (669-901, 233 lines).
2. Statement point (i), no FAIL: `hLK : sz.STLK E t1` gives the step-0 loops and `hLoc : sz.STLocalEntry E t1` the step-0 local law; of the five conclusions of `UNMLOut` only these two are consumed (`STLmax`, `STDecay`, `STExp2` are not).  The transfer to `Pgue` is the coordinate marginal at step 0 (`Measure.le_map_apply`, no measurability), as in the source.
3. The comparison `W^{-d} B_{t₁,0} ≤ 2 (N η_{t₁})⁻¹` is `PathBounds_Bctl_le`, a private re-derivation of the private `Hyp_Bctl_le` (`HypA.lean:494`); `STWB(K) ≤ Bctl` is `PathBounds_STWB_le`.  The constant `2` is absorbed in `N^{τ/2}` (loops) and `N^τ` (local law).
4. The proofs of `gueBds_h745E`, `gueBds_h746`, `gueGrid_pathBounds` follow the source with the renaming; changes: `hbig` and `hCe` carry `A = 1 + 2 lam²` (merged `HypB_fixed`, T2354a), `HypB_entry_le` takes `2 ≤ d` (from `hd`), `gueKproc_detDom` comes from `ProcK` (one import beyond the ticket's list, the ticket's check file imports it).
5. Statement difference F2 (T2361b): `Bounds_path` (`BoundsA.lean:503`) needs `L^d(1−t₁) ≤ 1` and `hell` gives only `≤ ilambda²`; the main theorem carries `hell1` as a hypothesis (also in the instance).  `gueBds_h745E`, `gueBds_h746` do not need it.
6. Instances: the three `example`s at `sz0` (`d = 3`, `n₀ = 2`, `κ = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τ_U = 1/1000`, `E = 0`) discharge `hadm` (`sz0_admissible`), `hE`, `ht1`, `ht10`, `ht0`, `h730`, `hscale`, `hell`, `hell1`, `hKb` (`stKbound_holds`), `hKinit`, `hK` (`gueK_exists`); `hLK`, `hLoc` stay hypotheses (`UNMLOut`, owed by ST-6; limit check in (a)).  The window is the one of `HypAInst` (`hell` with equality); at `n = 0` it is `0 < t₁ < t₀ < 1` with `t₀ − t₁ = 1.8e-12`; `hscale` is proved for all `n` (`N^{1/1000} ≤ 2(n+1) ≤ N η_{t₀}`).
7. Registry: none (ticket); the pre-check with `import RBM3D` exits 0; the full `lake build` does not import the file until the hub adds the root import.

## (c) Verified names
Script: `import RBM3D.Universality.GUEPhase.PathBounds` + `#check @NAME` for each name below, `lake env lean names.lean`: exit 0, 0 `error` lines.
Mathlib: `MeasureTheory.Measure.infinitePi_map_eval`, `MeasureTheory.Measure.le_map_apply`, `measurable_pi_apply`, `Real.one_le_rpow`, `Real.rpow_nonneg`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_one`, `Real.rpow_pos_of_pos`, `Real.rpow_add_one`, `Real.sqrt_le_iff`, `Real.sqrt_mul`, `Real.sqrt_nonneg`, `Real.sqrt_sq`, `Real.continuous_sqrt`, `pow_le_pow_left₀`, `pow_lt_pow_left₀`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `one_le_pow₀`, `pow_le_one₀`, `div_le_one`, `div_le_div_iff₀`, `mul_div_cancel₀`, `mul_le_of_le_one_right`, `Nat.one_le_cast`, `Matrix.nonsing_inv_eq_ringInverse`, `even_two_mul`, `Matrix.sub_apply`, `Matrix.smul_apply`, `abs_of_pos`, `mul_pow`, `Set.mem_ofPred_eq`, `Filter.eventually_ge_atTop`, `Filter.Eventually.of_forall`.
RBM3D: `Pgue`, `gueH`, `PathΩ`, `Sizes.seqHflow_eq_smul`, `loopM_eq_loopL` (explicit `d L W`), `Sizes.STGM`, `Sizes.Gt`, `Sizes.STLK`, `Sizes.STLocalEntry`, `Sizes.STWB`, `Sizes.Bctl`, `Hyp_Kt_detDom`, `Hyp_time_mem`, `gueKproc_detDom`, `gueGrid_entry_bound`, `gueGrid_loop_duhamel`, `HypB_fixed`, `HypB_entry_le`, `HypB_eG_745`, `HypB_eG_746`, `HypB_q_745`, `HypB_ev_grid`, `HypB_ev_delta`, `HypB_highProb_range`, `HypB_step_le`, `HypB_Kt_le_one`, `HypB_Lproc_grid`, `HypB_Dproc_grid`, `HypB_sqrt_cont`, `eq727GEAt`, `eq728GAt`, `Bounds_path`, `BoundsACheck.highProbAt_{hA,hB,HC,hD,hF}`, `BoundsACheck.pathBounds_of_forall_highProbAt`, `Sizes.tendsto_size` (namespace `RBM.Gauss`), `SizesInst.sz0_admissible`, `Sizes.stKbound_holds`, `gueK_exists`, `GUEPathBounds`, `eventually_le_rpow`, `eventually_rpow_le_of_neg`, `highProbAt_univ`, `perTimeCalc_highProbAt_{inter,of_stochDomAt,mono}`.
Verified absent or renamed: `Set.mem_setOf_eq` (deprecated in the first compile of the file, use `Set.mem_ofPred_eq`); RBM3D declarations `GoodEvent_gridTime_zero`, `Kcal`, `InitLK`, `MLConcl`, `InitLocal`, `scaleM`: 0 (declaration grep in (b)); twins used (also checked by the script): `STKloop`, `STKbound`, `STLK`, `STLocalEntry`, `Bctl`.

## (d) Open issues and paper-delta candidates
- **T2361a**: the loop estimate `MLConcl d E t1` (no twin) ↦ `hLK : sz.STLK E t1`, `hLoc : sz.STLocalEntry E t1` (conclusions of `UNMLOut`, `Universality/Pins.lean:432`); `scaleM = N η_{t₁}` (`ℓ_{t₁} = L`) ↦ the inequality `Bctl ≤ 2 (N η_{t₁})⁻¹` under `hell`; the `(σ, a)`, `(x, y)` counting lemmas of the source are not needed.
- **T2361b**: `gueGrid_pathBounds` has the extra hypothesis `hell1 : ∀ᶠ n, L^d(1 − t₁) ≤ 1` (merged `Bounds_path` has `hellN`, written for `ilambda² ≤ 1`; `(eq:WO)` gives only `ilambda ≤ 𝔡⁻¹`).  A consumer (UN-51) must supply it; the ingredients are in `docs/reports/T2356-design.md` §2 (not recomputed here).
- **T2361c**: `h𝔠`, `Admissible 𝔠 d` ↦ `hd : 3 ≤ d`, `hadm : sz.Admissible 𝔠 𝔡`; `gueBds_h746` has `hadm` for `hsz` and no `hd`; `hKb : sz.STKbound E` is a hypothesis of all three (as `Hyp_Kt_detDom`, T2352a (2)); `hKinit` only on `loopOf σ a` with `STKloop` (T2352a (3)); `hell` as `L^d(1−t₁) ≤ ilambda²` (T2352a (1)).
- Open 1: `hLK`, `hLoc` are conclusions of `UNMLOut` (owed by ST-6) at flow energies `STflowE z`, times `t ≤ lemT z`; the consumer must supply `E`, `t₁` in that form and good data for the `∀ n` facts (T2356 F2).
- Open 2: file size 903 lines (third ticket size 950); `PathBoundsInst` is 233 of them.
