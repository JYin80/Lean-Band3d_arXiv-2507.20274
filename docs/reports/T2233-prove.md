Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 00:30:22 UTC 2026

Notation: `x_v = 1-v`, `A_n = λ_n² W_n^d`, `B_v = Bctl n v = W^{-d}((λ²+x_v)⁻¹ + (L^d x_v)⁻¹)` (`Bparam` at `K = 0`: the factor `(0+1)^{d-2} = 1`),
`T_u = B_u²(A^{-1/5} + B_u)`, `X_v = x_v⁻¹(B_v^{11/5} + B_v^{5/2})`, `N = (WL)^d`. Regime (ii) `STReg5II`: `λ²/L^d ≤ 1-t`, `1-s ≤ λ²/L²`.

### (i) Exponent table

| # | quantity | value | constraint / source | slack |
|---|---|---|---|---|
| 1 | drift exponents | `11/5` (`eq:Exp(L-K)1`, `6:58-62`), `5/2` (`eq:ExpLWn=2`, `6:83-88`), prefactor `x_v⁻¹` | premise `STExpDriftHiConcl` (`Step6Pins.lean:311`), window `λ²/L^d ≤ 1-t` = `STReg5II.1` | exact; `‖D_v‖ ≤ ‖ELKLK‖ + ‖EGt‖ ≤ N^{τ'} X_v` (no factor 2) |
| 2 | target exponent | `T = B²(A^{-1/5}+B)`: `2`, `-1/5`, `1` | `STExpTarget` (`Step6Pins.lean:65`), `(Eq:Gtlp_exp_flow)` `1_2:1390-1396` | — |
| 3 | `B_u ≤ 2 A⁻¹` (target 2) | constant `2` | `(λ²+x)⁻¹ ≤ λ⁻²` (`λ ≠ 0`); `x_u ≥ λ²/L^d ⇒ (L^d x_u)⁻¹ ≤ λ⁻²` | tight: ratio `B/(2A⁻¹) → 1` as `x_u → 0⁺` (grid max `1.0`) |
| 4 | `λ ≠ 0` | follows | `0 < 1-t < 1-s ≤ λ²/L²` and `L ≥ 3` (`three_le_L`) give `λ² > 0` | strict: `λ² ≥ L²(1-s) > 0` |
| 5 | `B^{11/5} = B²·B^{1/5}`, `B^{1/5} ≤ 2^{1/5}A^{-1/5}` | `2^{1/5} = 1.1487` | `rpow` monotone, `mul_rpow`, `inv_rpow` | — |
| 6 | `B^{5/2} = B²·B^{1/2}`, `B^{1/2} ≤ max(B^{1/5}, B) ≤ B^{1/5} + B` | split `B ≤ 1` / `B > 1` | `B ≤ 1 ⇒ B^{1/2} ≤ B^{1/5}`; `B > 1 ⇒ B^{1/2} ≤ B` | `B > 1` occurs (1170 grid points) |
| 7 | rates constant (target 3) | `B^{11/5}+B^{5/2} ≤ 2·2^{1/5} T = 2.2974 T ≤ 3T` | sum of rows 5, 6: `B²(2·2^{1/5}A^{-1/5} + B) ≤ 2·2^{1/5} T` | `3 - 2.2974 = 0.7026`; max ratio to `3T` on grid `0.4883` (bound `0.7658`) |
| 8 | monotonicity `B_v ≤ B_u` | `s ≤ v ≤ u < 1` | `STBctl_mono`; `rpow_le_rpow` (exponents `> 0`) | `X_v ≤ 3T_u x_v⁻¹` |
| 9 | `u`-integral (targets 1, 4) | `∫_s^u x_v⁻¹ dv = log(x_s/x_u)` | `0 < x_u ≤ x_s`; `x_s ≤ λ²/L²`, `x_u ≥ λ²/L^d` ⇒ `x_s/x_u ≤ L^{d-2}` | `log(x_s/x_u) ≤ (d-2) log L`; tight (grid max ratio `1.0` at the two boundaries); needs `L ≥ 1`, `d ≥ 2` |
| 10 | one-size drift integral | `‖∫‖ ≤ M·3T_u·(d-2) log L` | `‖∫ f‖ ≤ ∫ ‖f‖`, a.e. bound `3MT_u x_v⁻¹` (continuous on `[s,u]`, `x_v ≥ x_u > 0`), `M ≥ 0` | — |
| 11 | kernel `(sum_res_Ndecay_nonzero)` `3_5:1667` (`STEKNonzero` `Step34Pins.lean:666`) | `n_ = 2`, `κ' = √(2κ)/2`, no loss, no ratio | window `1-λ²/L² ≤ s` (= `STReg5II.2`), `0 ≤ s`, `s ≤ u`, `u < 1` (`st5_t_lt_one`), `‖m‖ = 1`, `κ' ≤ Im m`, `A ⊇ I_diff(σ)`, `X ≥ 0` | `X_v ≥ 0`: `v ≤ u < 1`, `B_v > 0` (`STBctl_pos`) |
| 12 | `A ⊇ I_diff(σ)` | `A = {1,2}` for `σ₁ ≠ σ₂` (any `σ`, `P = STSigMixed`); `A = ∅` for `σ₁ = σ₂` (`I_diff = ∅`, `3_5:1470`, `st6_Idiff_same`) | `STEKNonzero` hypothesis `∀ i, σ i ≠ σ(rot i) → i ∈ A` | — |
| 13 | `log L ≺ 1` (target 5a) | `∀ C, τ > 0`: eventually `C log L ≤ N^τ` | `L ≤ N` (`W ≥ 1`, `d ≥ 1`); `log N ≤ N^{τ/2}/(τ/2)`; `N → ∞`; `log L ≥ 0` handles `C < 0` | threshold `N^{τ/2} ≥ 2|C|/τ` (numbers below) |
| 14 | `τ`-bookkeeping (targets 5b, 6) | initial term at `τ`, kernel at `τ/2`, `3(d-2) log L ≤ N^{τ/2}` | `N^{τ/2}·N^{τ/2} = N^τ` (`rpow_add`, `N ≥ 1`); `T_u ≥ 0` (`st6_target_nonneg`, `u < 1`) | total `≤ N^τ F + N^τ T_u = N^τ(F + T_u)` |
| 15 | pin constant `𝔠_d` | `1/100` | `0 < 𝔠_d ≤ 1/100`; no premise of `STIngR6` beyond `STFlow`, regime, Duhamel, drift is used | exact |
| 16 | lift over `u` (target 5b) | two-time `s ≤ v ≤ u ≤ t` | per time sequence `u`: `stek_nonzero_holds` with `t ↦ u` gives an eventual bound for all `v ∈ [s_n,u_n]`, `σ`; a failing `(n, u_n, v_n, σ)` for infinitely many `n` defines a sequence `u_n`, contradicting it | both sides deterministic (`D_v` is an expectation, `X_v` a number): `st6_prec_det_iff` makes each `Prec` an eventual pointwise bound; no random right side is lifted |

Two derivations the prover may use (mathematics only; neither changes a pinned statement). (1) The conclusion of target 6 could also be lifted per time sequence `u` directly, since the kernel estimate per sequence is already uniform in `v ∈ [s_n,u_n]`. (2) `‖Q^{(A)}𝒰_{v,u}D_v‖` is bounded directly by `STEKNonzero`; `(normQA2)` is not needed.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `λ = 1`, `N = (4W)^3 ≥ 4096`), `(s,t) = (15/16, 31/32)` constant, `n ∈ {0, 10, 100}`. Hypotheses:
`3 ≤ d`; `0 ≤ s < t < 1`; `1-s = 1/16 = λ²/L²` (window boundary, `s ≥ 1-λ²/L² = 15/16`); `λ²/L^3 = 1/64 ≤ 1-t = 1/32`; `λ = 1 ≠ 0`;
`t ≤ lemT(zB) ` with `lemT zB ≥ 31/32` and `STFlow szB (1/10) (1/10) (1/6) (1/10) zB` (`flow_zB`, `lemT_zB`, `Step34Pins.lean`), `N → ∞` (`W_n → ∞`).
External hypothesis `(sum_res_Ndecay_nonzero)`: it is the merged theorem `stek_nonzero_holds` (no hypothesis left external). Its concrete window check at this data: `1 - λ²/L² = 15/16 ≤ s = 15/16 ≤ u ≤ 31/32 < 1` for every `u ∈ [s,t]`; `|m| = 1` (`norm_mE`), `Im m ≥ √(2κ)/2 = √(1/5)/2 = 0.2236` at `κ = 1/10`.
The drift premises `STExpDriftHiConcl` stay hypotheses (other gates' pins); the quantities they are compared with are computed below.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2233/pre.py`
```
== szB (L=4, lam=1, W=n+4, d=3), regime (ii) times s=15/16, t=31/32
n=  0 W=  4 u=0.93750 B=1.8612e-02 2/(lam^2W^d)=3.1250e-02 B<=2/A:True B^(11/5)+B^(5/2)=2.0341e-04 3T=4.7170e-04 ratio=0.431
n=  0 W=  4 u=0.96875 B=2.2964e-02 2/(lam^2W^d)=3.1250e-02 B<=2/A:True B^(11/5)+B^(5/2)=3.2783e-04 3T=7.2495e-04 ratio=0.452
n= 10 W= 14 u=0.93750 B=4.3410e-04 2/(lam^2W^d)=7.2886e-04 B<=2/A:True B^(11/5)+B^(5/2)=4.3985e-08 3T=1.1629e-07 ratio=0.378
n= 10 W= 14 u=0.96875 B=5.3560e-04 2/(lam^2W^d)=7.2886e-04 B<=2/A:True B^(11/5)+B^(5/2)=7.0239e-08 3T=1.7712e-07 ratio=0.397
n=100 W=104 u=0.93750 B=1.0590e-06 2/(lam^2W^d)=1.7780e-06 B<=2/A:True B^(11/5)+B^(5/2)=7.2723e-14 3T=2.0733e-13 ratio=0.351
n=100 W=104 u=0.96875 B=1.3066e-06 2/(lam^2W^d)=1.7780e-06 B<=2/A:True B^(11/5)+B^(5/2)=1.1558e-13 3T=3.1562e-13 ratio=0.366
integral_{15/16}^{31/32} 1/(1-v) dv = log2 = 0.6931471805599453 <= (d-2)log L = 1.3862943611198906
grid points: 3536 (B>1 points: 1170 ) max B/(2/(lam^2W^d)) = 1.0
max (B^(11/5)+B^(5/2))/(3T) = 0.4883 at (lam,W,L,x,B)= (1, 3, 50, 8e-06, 0.07407377778014812) ; bound 2*2^(1/5)/3 = 0.7658
max int/((d-2)logL) over cases hs=lam^2/L^2 (should be <=1): 1.0
== threshold 3(d-2)log L <= N^(tau/2), szB: L=4, N=(4W)^3, W=n+4
tau=1: 3 log4=4.159; N0>=17.3; n0=0; N^(tau/2) at n0 = 64.000; at n0-1 = 64.000
tau=0.5: 3 log4=4.159; N0>=299.2; n0=0; N^(tau/2) at n0 = 8.000; at n0-1 = 8.000
tau=0.1: 3 log4=4.159; N0>=2.396e+12; n0=3342; N^(tau/2) at n0 = 4.159; at n0-1 = 4.159
2^(1/5)= 1.148698354997035 2*2^(1/5)= 2.29739670999407 <=3: True
```
Grid: `λ ∈ {1e-3,…,100}`, `W ∈ {1,…,1e5}`, `L ∈ {3,4,5,10,50}`, 13 log-spaced `x ∈ [λ²/L^d, min(λ²/L², 1))`, `d = 3`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2233/pre2.py` (same grid, `d = 4, 5`; exact threshold at `τ = 1/10`)
```
d=3: grid points 3536, max rates/(3T)=0.4883 (<=0.7658), max int/((d-2)log L)=1.0000 (<=1)
d=4: grid points 3640, max rates/(3T)=0.4876 (<=0.7658), max int/((d-2)log L)=1.0000 (<=1)
d=5: grid points 3848, max rates/(3T)=0.4885 (<=0.7658), max int/((d-2)log L)=1.0000 (<=1)
tau=1/10: first n with N^(1/20)>=3 log 4: 3342 ; N^(1/20) at n-1,n: 4.158803655298414 4.158990125045258 ; 3 log 4 = 4.1588830833596715
```
Eventual thresholds at `szB` for `3(d-2) log L ≤ N^{τ/2}`: `n ≥ 0` for `τ = 1, 1/2`; `n ≥ 3342` for `τ = 1/10`. The theorem is eventual in `n`, `W_n = n+4 → ∞`, so these finite thresholds are the expected form (no astronomically large witness is needed for the deterministic one-size theorems 1-4, which hold at `n = 0`).

### Verdicts

- Target 1 `expIntII_log_ratio`: PASS. `g ≠ 0` follows from `1-s ≥ 1-u > 0`, `1-s ≤ g²/L²`; `(1-s)/(1-u) ≤ L^{d-2}`.
- Target 2 `expIntII_Bctl_le`: PASS (row 3, row 4).
- Target 3 `expIntII_rates_le_target`: PASS (rows 5-7; constant `2·2^{1/5} ≤ 3`).
- Target 4 `expIntII_drift_integral_le`: PASS (rows 8-10). The hypothesis `λ ≠ 0` of targets 2, 3 is derived inside from `1-s ≤ λ²/L²`, `s ≤ u < 1`, `L ≥ 3` (row 4).
- Target 5a `expIntII_log_eventually`: PASS (row 13).
- Target 5b `expIntII_kernel_unif`: PASS. All hypotheses of `STEKNonzero` hold per time sequence `u` (row 11); `‖D_v‖_∞ ≤ N^{τ'} X_v` for all `v ∈ [s_n,t_n]`, `σ`, `a` follows from `STExpDriftHiConcl` and `st6_prec_det_iff`; lift by row 16 (two-time index handled by setting the integrand to `0` for `v > u`, or by the per-sequence derivation (1)).
- Target 6 `STExpIntConcl_of_kernel`: PASS (rows 9-10, 13, 14; uses `STReg5II` for `1-s ≤ λ²/L²` and `λ²/L^d ≤ 1-t ≤ 1-u`).
- Target 7a `STExpIntIIConcl_of_flow`: PASS. `SizeTendsto` from `hflow.1.2.2.1`; `t < 1` from `st5_t_lt_one`; window `1-λ²/L² ≤ s` from `STReg5II.2`; `(univ, STSigMixed)` and `(∅, STSigSame)` (row 12).
- Target 7b `stExpIntII_holds`: PASS (row 15). Consumer shapes verified: `inst_expIntII (h : STExpIntII 3)` (`Step6Pins.lean:629-633`), `inst_skeleton6II … (hInt : STExpIntII 3) …` (`Step6Kit.lean:1116-1119`), and `hint.1`/`hint.2` with `F = T_s` at `Step6Kit.lean:896-899` (the conjunct order `(univ, STSigMixed)`, `(∅, STSigSame)` matches `STExpIntII`).
- Target 8 instances: PASS. At `szB`, `zB`, `κ = 1/10`, `(15/16, 31/32)`: `szB_reg5II`, `szB_flow_ht`, `flow_zB` exist; deterministic numbers in (ii) above; `inst_expIntII_concl` keeps `STExpDriftHiConcl` as hypothesis. Observation: `main` is now `e64e4f0` (T2229 merged: `grep -n "STExpWardII" RBM3D/Test/Axioms.lean` in the worktree shows only `STExpWardIIConcl` at `:331`); the `STExpIntII` registry line is at `Axioms.lean:241` in the worktree, not `:235`.

No hypothesis set fails, no exponent fails to close, no missing input. No paper-delta beyond those named in the ticket (a)-(c): the constant `3` (`2·2^{1/5}`), `(normQA2)` not needed, `σ₁ = σ₂` with `A = ∅`.

Overall verdict: PASS

## (b) Script output — Tue Oct  6 00:56:17 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2233`, branch `t/T2233`, commit `ac625a0` (base `e64e4f0`; `main` is now `3a58663`). Files: `RBM3D/Induction/ExpIntII.lean`
  (new, 653 lines), `RBM3D/Test/Axioms.lean` (-1 line). Scratch scripts named below (`axioms_check.lean`, `precheck.lean`, `check_eq.lean`, `consumer.lean`, `clash.sh`,
  `extract2.py`, `where.lean`, `gen_b.sh`) are in `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2233/`.
### Build
```
$ lake build RBM3D.Induction.ExpIntII          # Tue Oct  6 00:48:50 UTC 2026
Build completed successfully (3857 jobs).
exit=0
$ lake build     # full library, temporary uncommitted 'import RBM3D.Induction.ExpIntII' in RBM3D.lean (removed again), Tue Oct  6 00:44:34 UTC 2026
RBM3D.lean:277:0: axiom audit: 6836 theorems, 2328 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 145 owed + 84 structural + 7 refuted; 109 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4037 jobs).
$ git diff -- RBM3D.lean | wc -l       # after removing the temporary import
0
```
### Axioms (18 public declarations of the file: 9 targets, 9 instances)
```
$ lake env lean axioms_check.lean | sed "s/.*depends on axioms: //" | sort | uniq -c
  18 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/Induction/ExpIntII.lean ; echo rc=$?
rc=1
```
### Target statements, extracted from the file by script (`extract2.py stmt <names>`; file lines 71, 106, 159, 202, 279, 393, 472, 533, 553)
```
theorem expIntII_log_ratio {d L : ℕ} {g s u : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ L) (hsu : s ≤ u) (hu : u < 1)
    (h1 : 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2) (h2 : g ^ 2 / (L : ℝ) ^ d ≤ 1 - u) :
    ∫ v in s..u, (1 - v)⁻¹ ≤ ((d : ℝ) - 2) * Real.log (L : ℝ) := by
theorem expIntII_Bctl_le (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0)
    (hw : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) :
    sz.Bctl n u ≤ 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
theorem expIntII_rates_le_target (n : ℕ) {u : ℝ} (hu : u < 1) (hl : sz.lam n ≠ 0)
    (hw : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) :
    sz.Bctl n u ^ (11 / 5 : ℝ) + sz.Bctl n u ^ (5 / 2 : ℝ) ≤ 3 * STExpTarget sz n u := by
theorem expIntII_drift_integral_le (n : ℕ) {E s u M : ℝ} (hd : 2 ≤ d) (hM : 0 ≤ M) (hsu : s ≤ u) (hu : u < 1)
    (hwin : 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hlo : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u)
    (σ : Fin 2 → Bool) (A : Finset (Fin 2))
    (hker : ∀ v : ℝ, s ≤ v → v ≤ u →
      ‖RBM.zeroModeSet d (sz.L n) A
          (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b))‖ ≤
        M * ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∫ v in s..u, RBM.zeroModeSet d (sz.L n) A
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ v u (fun b => STExpDrift sz n E v σ b)) a‖ ≤
      M * (3 * STExpTarget sz n u * (((d : ℝ) - 2) * Real.log ((sz.L n : ℕ) : ℝ))) := by
theorem expIntII_log_eventually (hsz : sz.SizeTendsto) (hd : 1 ≤ d) (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, C * Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
theorem expIntII_kernel_unif (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hsg : ∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n)
    (hdr : STExpDriftHiConcl sz (STflowE z) s t) (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hA : ∀ σ, P σ → ∀ i, σ i ≠ σ (finRotate 2 i) → i ∈ A) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖RBM.zeroModeSet d (sz.L n) A
            (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (STflowE z n) σ v (u : ℝ)
              (fun b => STExpDrift sz n (STflowE z n) v σ b))‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ))) := by
theorem STExpIntConcl_of_kernel (hsz : sz.SizeTendsto) (hd : 2 ≤ d) {E s t : ℕ → ℝ}
    (_hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5II sz s t) (hduh : STExpDuhEq sz E s t)
    (A : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop)
    (hker : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (v : ℝ), s n ≤ v → v ≤ (u : ℝ) →
      ∀ σ : Fin 2 → Bool, P σ →
        ‖RBM.zeroModeSet d (sz.L n) A
            (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v (u : ℝ) (fun b => STExpDrift sz n (E n) v σ b))‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - v)⁻¹ * (sz.Bctl n v ^ (11 / 5 : ℝ) + sz.Bctl n v ^ (5 / 2 : ℝ)))) :
    STExpIntConcl sz A P E s t := by
theorem STExpIntIIConcl_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (htT : ∀ n, t n ≤ lemT (z n))
    (hR : STReg5II sz s t) (hduh : STExpDuhEq sz (STflowE z) s t) (hdr : STExpDriftHiConcl sz (STflowE z) s t) :
    STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed (STflowE z) s t ∧
      STExpIntConcl sz ∅ STSigSame (STflowE z) s t := by
theorem stExpIntII_holds (d : ℕ) : STExpIntII d := by
```
### Compiled nonempty instances (`extract2.py full <names>`; namespace `RBM.Gauss.Step6Inst`)
```
theorem inst_expIntII_holds :
    InstIng6Concl (fun sz E s t => STExpDuhEq sz E s t → STExpDriftHiConcl sz E s t →
      STExpIntConcl sz (Finset.univ : Finset (Fin 2)) STSigMixed E s t ∧ STExpIntConcl sz ∅ STSigSame E s t) szB zB
      (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_expIntII (stExpIntII_holds 3)
theorem inst_skeleton6II_Int (hLW : LWtermEXP 3) (hWd : STExpWardII 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  inst_skeleton6II (stExpLKLKHi_holds 3) hLW (stImproveExpAver_holds 3) (stExpDuhamelZ_holds 3)
    (stExpIntII_holds 3) hWd
theorem inst_expIntII_concl :
    STExpDriftHiConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
      STExpIntConcl szB (Finset.univ : Finset (Fin 2)) STSigMixed (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
        STExpIntConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  STExpIntIIConcl_of_flow szB (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5II
    (st6_duhEq_of_pin szB (stExpDuhamelZ_holds 3) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) flow_zB
      (fun _ => by norm_num) (szB_flow_ht (by norm_num)))
theorem inst_expIntII_log_ratio :
    ∫ v in (15 / 16 : ℝ)..(31 / 32), (1 - v)⁻¹ ≤ (((3 : ℕ) : ℝ) - 2) * Real.log ((szB.L 0 : ℕ) : ℝ) :=
  expIntII_log_ratio (d := 3) (L := szB.L 0) (g := szB.lam 0) (by norm_num) (by simp [szB]) (by norm_num)
    (by norm_num) (by simp [szB]; norm_num) (by simp [szB]; norm_num)
theorem inst_expIntII_Bctl_le :
    szB.Bctl 0 (31 / 32) ≤ 2 * (szB.lam 0 ^ 2 * ((szB.W 0 : ℕ) : ℝ) ^ 3)⁻¹ :=
  expIntII_Bctl_le szB 0 (by norm_num) (by simp [szB]) (by simp [szB]; norm_num)
theorem inst_expIntII_rates_le_target :
    szB.Bctl 0 (31 / 32) ^ (11 / 5 : ℝ) + szB.Bctl 0 (31 / 32) ^ (5 / 2 : ℝ) ≤ 3 * STExpTarget szB 0 (31 / 32) :=
  expIntII_rates_le_target szB 0 (by norm_num) (by simp [szB]) (by simp [szB]; norm_num)
$ grep -n "^theorem inst_expIntII_\(log_eventually\|kernel_unif\|drift_integral_le\)" RBM3D/Induction/ExpIntII.lean   # extra instances (targets 5a, 5b, 4)
613:theorem inst_expIntII_log_eventually :
620:theorem inst_expIntII_kernel_unif
634:theorem inst_expIntII_drift_integral_le
```
### Registry pre-check (DECISIONS §20 (2))
```
$ lake env lean precheck.lean    # import RBM3D; import RBM3D.Induction.ExpIntII; #assert_rbm_axioms (temporary root import in place); Tue Oct  6 00:45:38 UTC 2026
exit=0
axiom audit: 6836 theorems, 2328 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 145 owed + 84 structural + 7 refuted; 109 registered premise(s) carry nothing yet: [RBM.Loop.KLPT
$ grep -cE 'STExpIntII($|[^I])' precheck.log build_full.log
0 0
$ #eval RBM.Audit.owedProps.length; #eval RBM.Audit.owedProps.contains `RBM.Gauss.Sizes.STExpIntII   (Axioms.lean at the base commit, then at the branch)
base:   146 true
branch: 145 false
```
### Check-file equality, consumer, name clash, diff
```
$ lake env lean check_eq.lean    # check sections 1-2 + import ExpIntII + 9 'example : T2233Check.X := @X' + 'example (d) : STExpIntII d := stExpIntII_holds d' + 6 section-3 'example : <stmt> := @inst_*'; Tue Oct  6 00:46:56 UTC 2026
examples: 16; 0 error lines; exit=0
$ lake env lean consumer.lean    # ST_step6_caseII_of_pins hLK hLW hAvg hDu (stExpIntII_holds d) hWd : STStep6II d; Tue Oct  6 00:49:25 UTC 2026
exit=0
$ bash clash.sh   # grep -rnw over RBM3D/ and RBM3D.lean for the 24 new names (18 public, 6 private), excluding ExpIntII.lean
names checked: 24, total hits: 0, sanity (existing name stExpWardII_holds): 6
$ git diff --stat main...t/T2233
 RBM3D/Induction/ExpIntII.lean | 653 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   1 -
 2 files changed, 653 insertions(+), 1 deletion(-)
$ git diff e64e4f0 t/T2233 -- RBM3D/Induction/Step6Pins.lean | wc -l
0
$ git merge-tree --write-tree main t/T2233; echo rc=$?
6097e15bd82d
rc=0
```
Ports: none. The ticket marks S6-12b as a new proof without RBM2D source (regime (ii) is empty at d = 2); no RBM1D/RBM2D file was read or copied, so there is no `git diff
  --stat` for ports. `expIntII_lift` is a copy of the argument of `st6_precU_of_forall_seq` (`Step6Kit.lean:115-153`, RBM3D, merged).
**Narrative.**
1. Result: `stExpIntII_holds (d : ℕ) : STExpIntII d`, `𝔠_d = 1/100`; the merged pin text is unchanged (`Step6Pins.lean` diff empty, above). The proof (file lines 553-557)
   uses `3 ≤ d`, `κ`, `hflow`, `hs0`, `hst`, `htT`, `hR`, `STExpDuhEq`, `STExpDriftHiConcl`; `ε`, `𝔡`, `STLK`, `STDecay`, `STExp2`, `STConStInd`, `STStep2Core`,
   `STLmaxU`, `STLKU`, `STGdecayW … 0` are introduced and not used. No hypothesis added, no signature changed, no primed successor, no obstruction.
2. Kernel (`expIntII_kernel_unif`): for each time sequence `u ∈ [s,t]` the merged `stek_nonzero_holds` at `t ↦ u` (`n_ = 2`, `κ' = √(2κ)/2`, `m n = mE (E n)`, `A ⊇
   I_diff(σ)`) is applied to the deterministic `𝒜 n v _ = D_v^σ` and `X = (1-v)⁻¹(B_v^{11/5} + B_v^{5/2})`; the premise `Prec ‖𝒜‖ X` is `STExpDriftHiConcl` through
   `st6_prec_det_iff` (`expIntII_drift_pi`, file line 323, no factor 2); `Ugen … E σ = UN … (EKsgn (mE E) σ)` by `rfl` (`expIntII_Ugen_eq`); the output returns to a
   pointwise bound by `st6_prec_det_iff`.
3. Lift: `expIntII_lift` (private, line 357, generic in a property `Φ n u v`) copies the `Classical.choose` failing-sequence argument of `st6_precU_of_forall_seq` and
   keeps `v ≤ u` inside `Φ`, so no `W n` trick or zero integrand is needed. Only the kernel bound is lifted. The conclusion of target 6 needs no second lift: `STExpDuhEq`
   holds for every `u ∈ [s_n,t_n]` and the uniform kernel bound is already pointwise in `u` (report (a), derivations (1), (2)). This differs from the ticket's sentence
   "the conclusion of target 6 is lifted", not from any statement.
4. Arithmetic: `B ≤ 2(λ²W^d)⁻¹` (`st6_Bctl_eq`); `B^{11/5} = B²B^{1/5}`, `B^{5/2} = B²B^{1/2}`, `B^{1/2} ≤ B^{1/5} + B` (cases `B ≤ 1`, `B > 1`), `2^{1/5} ≤ 3/2`
   (`(3/2)^5 = 243/32 ≥ 2`), so the sum is `≤ B²(2·2^{1/5}G + B) ≤ 3T` (`G = (λ²W^d)^{-1/5}`). `∫_s^u (1-v)⁻¹ = log((1-s)/(1-u)) ≤ (d-2) log L` (`integral_comp_sub_left`,
   `integral_inv`, `(1-s)/(1-u) ≤ L^{d-2}`). `log L ≺ 1`: `L ≤ N`, `log N ≤ N^{τ/2}/(τ/2)`, `N^{τ/2} → ∞`.
5. `STExpIntConcl_of_kernel`: initial term at `τ`, kernel at `τ/2` (`M = N^{τ/2}`), `3(d-2) log L ≤ N^{τ/2}` eventually, `N^{τ/2} N^{τ/2} = N^τ`; the result is `N^τ (F +
   T_u)`. `λ_n ≠ 0` is derived inside `expIntII_drift_integral_le` from `0 < 1-u ≤ 1-s ≤ λ²/L²`; `1 ≤ L` from `three_le_L`.
6. §29 / §45 O2 checklist: (1) `0 ≤ s`, `s ≤ v ≤ u ≤ t < 1` (`st5_t_lt_one`); (2) regime (ii): the kernel window `1-λ²/L² ≤ s` is `(hR n).2`, `x_u ≥ λ²/L^d` is `(hR n).1`
   with `u ≤ t n`, `x_s/x_u ≤ L^{d-2}` is `expIntII_log_ratio`; (3) no `L`–`W` relation, only `L ≤ N`; (4) hypotheses `∀ n`, conclusions eventual (`st6_prec_det_iff`);
   (5) uniform in `u` by `expIntII_lift`; (6) `lam n` arbitrary beyond the derived `λ_n ≠ 0`; (7) scale `N = sz.size`. Mollifier constants: none. Consumer:
   `stExpIntII_holds d` is accepted as `hInt` of `ST_step6_caseII_of_pins` (`consumer.lean`) and `stExpIntII_holds 3` as the argument of `inst_expIntII` and
   `inst_skeleton6II`.
7. Instances: the six of the ticket, plus `inst_expIntII_log_eventually`, `inst_expIntII_kernel_unif`, `inst_expIntII_drift_integral_le` for targets 5a, 5b, 4 (targets 6,
   7a are exercised by `inst_expIntII_concl`). Open hypotheses: `STExpDriftHiConcl` (`stExpLKLKHi_holds` is proved under the stochastic premises of `STIngR6`;
   `(eq:ExpLWn=2)` rests on `LWtermEXP`, owed, `Axioms.lean:154`), the stochastic premises inside `InstIng6Concl`, and `LWtermEXP 3`, `STExpWardII 3` in
   `inst_skeleton6II_Int`. Every deterministic hypothesis is discharged at `d = 3`, `szB` (`L = 4`, `W_n = n+4`, `lam = 1`), `zB`, `κ = 1/10`, `(s,t) = (15/16, 31/32)`;
   `1-s = 1/16 = λ²/L²` is the window boundary. `hker` of target 4 has no closed form (`STExpDrift` is an expectation); `inst_expIntII_drift_integral_le` takes it from
   `inst_expIntII_kernel_unif`.
8. Registry: the owed line of `STExpIntII` (`Axioms.lean:241` on the base, not `:235`; the `STExpWardII` line was deleted by the merge of T2229, `e64e4f0`) is deleted,
   owed 146 → 145, and `STExpIntII` does not occur in the audit output. The pre-check and the full build ran with a temporary uncommitted root import (the ticket, citing
   T2222, says the root audit needs it once the line is deleted); it was removed again (`git diff -- RBM3D.lean` empty), the hub adds the root import at merge.
9. Report (a) was not edited; nothing in it was found wrong, so there is no (a′). Size 653 lines against the ticket estimate 700 / 950 / 1250.
## (c) Verified names used (all resolved by the compile; `where.lean` prints module and first line of the declaration's range)
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`: `intervalIntegral.integral_comp_sub_left` 1055, `intervalIntegral.norm_integral_le_of_norm_le` 758,
  `intervalIntegral.integral_const_mul` 818, `ContinuousOn.intervalIntegrable` 504
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`: `Real.log_le_log` 150, `Real.log_pow` 287, `Real.log_nonneg` 212
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`: `Real.rpow_natCast` 61, `Real.rpow_mul` 415, `Real.rpow_one` 148, `Real.rpow_nonneg` 163, `Real.rpow_le_rpow` 549,
  `Real.rpow_le_rpow_of_exponent_ge` 643, `Real.rpow_le_rpow_of_exponent_le` 616, `Real.mul_rpow` 477, `Real.inv_rpow` 485, `Real.rpow_neg` 259, `Real.rpow_add` 208,
  `Real.log_le_rpow_div` 884
- Other: `integral_inv` (Analysis.SpecialFunctions.Integrals.Basic:211), `ContinuousOn.inv₀` (Topology.Algebra.GroupWithZero:129), `ContinuousOn.mul`
  (Topology.Algebra.Monoid.Defs:105), `norm_le_pi_norm` (Analysis.Normed.Group.Constructions:346), `pi_norm_le_iff_of_nonneg` (Analysis.Normed.Group.Constructions:318),
  `tendsto_rpow_atTop` (Analysis.SpecialFunctions.Pow.Asymptotics:37), `Filter.eventually_all` (Order.Filter.Finite:246), `inv_anti₀`
  (Algebra.Order.GroupWithZero.Basic:1220), `div_le_iff₀` (Algebra.Order.GroupWithZero.Basic:1132), `div_pos_iff_of_pos_right` (Algebra.Order.Field.Basic:154),
  `pow_lt_pow_left₀` (Algebra.Order.GroupWithZero.Basic:589), `Set.uIcc_of_le` (Order.Interval.Set.UnorderedInterval:76), `Nat.le_self_pow` (Init.Data.Nat.Lemmas:1262),
  `Nat.le_mul_of_pos_left` (Init.Data.Nat.Lemmas:605), `Filter.Frequently.and_eventually` (Order.Filter.Basic:793), `Filter.Frequently.exists` (Order.Filter.Basic:802),
  `Filter.not_eventually` (Order.Filter.Basic:828), `le_abs_self` (Algebra.Order.Group.Unbundled.Abs:67), `mul_inv` (Algebra.Group.Basic:522)
- Signatures seen in the tool log: `Real.log_pow (x : ℝ) (n : ℕ)`; `div_le_iff₀ (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c`; `pow_lt_pow_left₀ : a < b → 0 ≤ a → n ≠ 0 → a ^ n <
  b ^ n`; `integral_inv : 0 ∉ Set.uIcc a b → ∫ x in a..b, x⁻¹ = Real.log (b / a)`.
- Verified absent: `Filter.Eventually.and_eventually` (unknown constant in `where.lean`; the lemma used is `Filter.Frequently.and_eventually`, applied to `¬ ∀ᶠ`).
## (d) Open issues and paper-delta candidates
- `T2233a` (`6:146-147`, "integrate over `u`"): made explicit as `∫_s^u (1-v)⁻¹ dv = log((1-s)/(1-u)) ≤ (d-2) log L ≺ 1` and `B^{11/5} + B^{5/2} ≤
  B²(2·2^{1/5}(λ²W^d)^{-1/5} + B) ≤ 3 T_u` from `1-u ≥ λ²/L^d` (`W^{-d}B_{u,0} ≤ 2(λ²W^d)⁻¹`), constant `3` (`expIntII_log_ratio`, `expIntII_Bctl_le`,
  `expIntII_rates_le_target`).
- `T2233b` (`6:147`): `(normQA2)` is not used; `(sum_res_Ndecay_nonzero)` bounds `Q^{(A)} 𝒰_{v,u}` directly.
- `T2233c` (`6:136-147`): the paper treats `σ₁ ≠ σ₂` only; `σ₁ = σ₂` is the same argument with `A = ∅` (`I_diff = ∅`, `st6_Idiff_same`), as `T2191a`.
- Open: none. No step needed a hypothesis the pin lacks, so there is no primed successor (`T2233a…`) and the owed line is deleted.
- Merge note: `git merge-tree` of `t/T2233` with `main` `3a58663` is clean (rc 0; the merge of T2232, `b112700`, deleted the `STExpWardI` line two lines above the deleted
  one). Keep every deleted line deleted. Root import: `import RBM3D.Induction.ExpIntII` after the last `import` line of `RBM3D.lean`.
- Follow-up, not done (ticket: not a target): `inst_skeleton6II_Int hLW (stExpWardII_holds 3)` leaves only `LWtermEXP 3` open (`stExpWardII_holds` is merged); a one-liner
  for the hub or a later ticket.
