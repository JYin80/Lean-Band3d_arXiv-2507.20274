Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 11:21:55 UTC 2026

Targets: `Bounds_path` (pathwise unfreezing; RBM2D `BoundsA.lean:416`, last touched by 81fca44; RBM2D HEAD is 9e0f275), `HC`, `Concl`, `highProbAt_HC/hA/hB/hD/hF`, `pathBounds_of_forall_highProbAt`. Notation: `N = sz.size n = (W L)^d`, `η_u = etaT (E n) u = (1-u)·Im m(E)`, `Λ_u = (gueScale u)⁻¹ = (N η_u)⁻¹`, `δ = gueDelta = N^{-τU/4}`, `K = gueGridK = (N+1)^{32 n0+64}`, `p = N^{τ₁}`.

### (i) Exponent table (every constant the chain `Bounds_jump`/`Bounds_rpow_key`/`Bounds_T3`/`Bounds_sq_le`/`Bounds_final` uses)

| quantity | value in the source | constraint it must satisfy | slack at the instance (d=3, N=2^21, E=0, t1=99/100, t0=199/200, τU=3/5, τ₁=1/50, τ=1/10) |
|---|---|---|---|
| `hscN` | `Λ_t ≤ N^{-τU}` on `[t₁,t₀]` | `N η_{t₀} ≥ N^{τU}`, i.e. `τU ≤ 1 + log_N(1-t₀)` (so `τU ≤ 1`, as `η ≤ 1`) | `N η_{t₀} = 10485.76 ≥ N^{0.6} = 6208.4` (τU ≤ 0.636) |
| `hellN` (d-line 2) | `L^d (1-t₁) ≤ 1` (source: `L²`) | `L^d η_u ≤ L^d (1-t₁)·Im m ≤ 1` for `u ≥ t₁` (`Im m ≤ 1`) | `L^d(1-t₁) = 16/25` (1-t₁ ≤ 1/64) |
| `T3` (d-line 1) | `(W^d)⁻¹ ≤ Λ_u` on `[t₁,t₀]` (source `(W²)⁻¹`) | `N η_u = W^d (L^d η_u) ≤ W^d` (uses `(WL)^d = W^d L^d`, `hellN`) | `N η_{t₁} = 20971.5 ≤ W^d = 32768` |
| `hsmallN` | `N^{2τ₁-τU/2} ≤ 1/32` | `2τ₁ - τU/2 ≤ -5/(log₂N)`; forces `τ₁ < τU/4` (N>1) | exponent `-13/50`: `0.02272 ≤ 0.03125` (τ₁ ≤ 0.03095) |
| `h4N` | `2 ≤ N^{τ-τ₁}` | `τ-τ₁ ≥ 1/log₂N` | `N^{2/25} = 3.204 ≥ 2` (τ-τ₁ ≥ 1/21 = 0.0476; have 0.08) |
| `Bounds_rpow_key` | `2p²·N^{-τU} ≤ (δ/4)²` | equivalent to `hsmallN` (`2p²N^{-τU} = 2 N^{2τ₁-τU/2}·N^{-τU/2}`, `(δ/4)² = N^{-τU/2}/16`) | same as `hsmallN` |
| `Bounds_jump` grid | `Δ (N+1)^64 ≤ 1`, `Δ = (t₀-t₁)/K` | `K ≥ (N+1)^64`; `32 n0+64 ≥ 64` (any `n0`; source takes `2 ≤ n0`) | `Δ(N+1)^64 = 1.3·10⁻⁴⁰⁷` |
| `Bounds_jump` scale | `e = η_{t₀}⁻¹ ≤ S = N`, `1 ≤ S ≤ N` | `η_{t₀} ≥ 1/N` (from `hscN` at `t₀` and `η ≤ 1`) | `e = 200 ≤ N` |
| `Bounds_jump` floor | `1/N ≤ δ` | follows from `hscN` (`N⁻¹ ≤ Λ_{t₀} ≤ N^{-τU} ≤ δ`) | `4.8·10⁻⁷ ≤ 0.1127` |
| `Bounds_jump` conclusion | `e²(√(Δ/N)·Sg + Δ) ≤ δ/2`, `Sg ≤ N²·N` | `Sg`: sum of `N²` entries each `≤ N` (`card Idx = N`, `Sizes.card_Idx`) | `4.7·10⁻³⁸⁶ ≤ 0.0563` |
| unfreezing induction | `dev_0 ≤ δ/4`, `dev_j<δ ⇒ dev_j ≤ δ/4`, `dev_{j+1} ≤ dev_j + δ/2` | `δ/4+δ/2 < δ` (constants `1/4, 1/2`) | slack `δ/4` |
| entry step `x² ≤ 2p²Λ` | `x² ≤ p(L₂ + w)`, `L₂ ≤ pΛ`, `w=(W^d)⁻¹ ≤ Λ` | `2p²Λ ≤ 2p²N^{-τU} ≤ (δ/4)²` | as `Bounds_rpow_key` |
| final bound | `‖·‖ ≤ N^τ Λ^{1/2}` from `x² ≤ 2p²Λ`, `2p ≤ N^τ` | `N^{τ-τ₁} ≥ 2` (`h4N`) | as `h4N` |
| `hF` | `size → ∞` (`Tendsto`) | no further bound; `K` is a proof device | `size_n = 2^21 (n+1)^18 ≥ n+1` |

Dimension-sensitivity of the exponents: the exponents `τU, τ₁, τ`, `1/32`, `64`, `32 n0+64`, `δ/4, δ/2` are dimension-free (they only see `N`); `d` enters only through `N=(WL)^d`, `W^d` and `L^d`.

**d = 2 token table of the source** (command: comment-stripped regex scan of `RBM2D/Universality/GUEPhase/BoundsA.lean`; output verbatim):
```
Z2 9 [271, 272, 277, 417, 451, 612, 614, 665, 705]
W^2 (cast) 14 [293, 302, 320, 323, 326, 327, 328, 440, 443, 482, 493, 605, 608, 645]
L^2 (cast) 9 [301, 313, 314, 315, 316, 318, 323, 326, 422]
size_eq 1 [324]
pow_two/sq 0 []
card 5 [288, 289, 293, 294, 296]
size^2 literal 1 [287]
lines with "^ 2" total 70
```
Classification (lines read in the source): `Z2` (9 lines, all index types) ↦ `Zd d`. `(W : ℝ)^2`: the regex also hits lines `293, 440, 493, 605` where `^ 2` is `card²` (293) or `‖·‖^2` (440, 493, 605: entry square); the true `(W²)⁻¹` tokens are `302` (`Bounds_T3`), `443`, `608`, `645` (the `HC` control, `highProbAt_HC`), `482` (`hT3`), and `W^2` in `Bounds_T3` `320, 323, 326-328` ↦ `W^d`; `323` also `L^2 η` ↦ `L^d η`. `L^2 (cast)`: `301, 422` (the two `hellN`), `313-318, 326` (`Bounds_T3` body) ↦ `L^d`. `size_eq` (324) ↦ the `d`-form `size = (W L)^d` (`Sizes.size`, `mul_pow`, cast). `card` 288-296 and `287` (`card² · N = N²·N`): `card Idx = N` (`Sizes.card_Idx`), dimension-free. The remaining lines with `^ 2`: `‖·‖²` in `HC`/`hsq`, `x²`, `p²`, `(N^{τ₁})²`, `η⁻¹ ^ 2` of `gueDev_succ_le`, `Bounds_*` algebra, literal loop length `2` in `gueLmax … 2`: dimension-free. **Confirmed: the only dimension-dependent mathematics is the two ticket lines (`(W²)⁻¹ ↦ (W^d)⁻¹` in `HC`/`T3`/`highProbAt_HC`, `hellN`'s `L²` ↦ `L^d` in `Bounds_T3`/`Bounds_path`), plus `Z2`/`size_eq` renamings. No correction to the ticket.** Re-derivations needed (ticket port map): `GoodEvent_gridStep_nonneg/_gridTime_le/_gridTime_mono/_gridTime_zero`, `(mE e).im ≤ 1`, `one_le_rpow`, `size_eq`.

### (ii) One concrete nondegenerate instance
Core of `Bounds_path` (`Bounds_jump`/`Bounds_final` chain) at `d=3` on `sz0`, `n=0` (`L=4, W=32, N=(WL)^3=2^21`), `n0=2`, `E=0` (`Im m(0)=1`), `1-t₁=1/100 ≤ L^{-d}=1/64` (zero-mode regime, `1-t₀=1/200`). `python3 inst.py` (exact `Fraction` plus 80-digit `mpmath`):
```
d=3 L=4 W=32 N=2097152=2^21 n0=2 E=0 t1=99/100 t0=199/200 tauU=3/5 tau1=1/50 tau=1/10; K=(N+1)^128
n0>=2,tauU>0,|E|<2,0<=t1<=t0<1,0<tau1<tau               OK   
hellN: L^d (1-t1) <= 1                                  OK   16/25
hscN: N eta(t) >= N^tauU, worst t=t0                    OK   10485.76 >= 6208.375 (ratio 1.689)
hsmallN: N^(2tau1-tauU/2) <= 1/32                       OK   exp -13/50: 0.0227183 <= 0.03125 (ratio 1.376)
h4N: 2 <= N^(tau-tau1)                                  OK   exp 2/25: 3.20428 (ratio 1.602)
T3: N eta(u) <= W^d, worst u=t1                         OK   20971.52 <= 32768
literal d=2 hellN L^2(1-t1)<=1 at t1=15/16              OK   L^2(1-t1)=1; but L^d(1-t1)=4 and N eta(t1)=131072.0 > W^d=32768: T3 fails
GridCheck t1=(1-ouZeta(1/20))*9/10=0.856106: L^d(1-t1)=9.2092 > 1, so hellN fails there (O4: Bounds_path consumers use zero-mode t1)
Bounds_jump: 1<=N, 1<=S=N<=N, 0<=e<=S                   OK   e=eta(t0)^-1=200
Bounds_jump: Delta (N+1)^64 <= 1                        OK   1.3021e-407
Bounds_jump: 1/N <= delta=N^(-tauU/4)                   OK   4.7684e-7 <= 0.112656
Bounds_jump: e^2(sqrt(D/N) Sg+D) <= delta/2 (Sg=N^3)    OK   4.6913e-386 <= 0.0563282
```
Reading: all hypotheses of `Bounds_path` that are deterministic (`n0≥2, τU>0, |E|<2, 0≤t₁≤t₀<1, 0<τ₁<τ, hscN, hellN, hsmallN, h4N`) and the real-variable hypotheses of `Bounds_jump` hold together. The row `literal d=2 hellN` is a negative control (`OK` there only means `L²(1-t₁) ≤ 1` holds): at `t₁=15/16` the `d=2` form of `hellN` holds, `L^d(1-t₁)=4`, and `T3` fails (`N η = 131072 > W^d = 32768`), so the literal port is false and `L^d` is needed. At the `GridCheck` times `t₁ ≈ 0.856`, `L^d(1-t₁) = 9.2 > 1`: `hellN` fails there, consistent with O4 (consumers take zero-mode `t₁`); the `GridCheck` times are used only for `hF`, which has no `hellN`.
The pathwise hypotheses `hA, hB, hC, hD, hF` are `∀ω` statements (events of w.h.p. sources); they are not part of the deterministic core and are hypotheses of `Bounds_path`.

`highProbAt_hF` at `d=3`, `sz0`, `n0=2`; external hypothesis `Tendsto sz.size atTop atTop`. Limit computation (`python3 hf.py`, verbatim):
```
size n == 2^21 (n+1)^18 for n=0..50: True
size n >= n+1 for n=0..2000: True
n=0 size=2097152  log2=21.00
n=1 size=549755813888  log2=39.00
n=2 size=812479653347328  log2=49.53
n=10 size=11659991713824860234842112  log2=83.27
n=100 size=2508503070931240586116700541954360451530752  log2=140.85
n0=2: gueGridK 0 = (size 0+1)^128 has 810 decimal digits (proof device, not a witness for hF)
thresholds at N=2^21, E=0, t0=199/200, t1=99/100:
```
Exact: `sz0.size n = ((2(n+1))^5 · 4(n+1))^3 = 2^21 (n+1)^18 ≥ n+1 → ∞` (identity checked for `n ≤ 50`, inequality for `n ≤ 2000`; merged `sz0_size_tendsto_nat`, `Markov.lean:1122`, gives the `Tendsto`). `HighProbAt` of `gue_highProb_incr_le` at this `sz0, n0 = 2` is the merged `gue_highProb_incr_le` (`Markov.lean:863`), (`Markov.lean:1127` applies it at `sz0` with `n0 = 1`; here `n0 = 2`, the same term with `n0 := 2`).

### (iii) Merged signatures against the source's uses
Command: `python3 sig.py` (token-normalised statements, renaming `d.L↦sz.L`, `spectralZ/M↦zt/mE`, `Z2↦Zd`, `gloop↦loopL`, dropping `d`/`sz` arguments), output verbatim:
```
gueLproc_time          2D-found=True 3D-found=True equal-modulo-renaming=True
gueDproc_time          2D-found=True 3D-found=True equal-modulo-renaming=False
    -LoopIdx
    +RBM.Loop.LoopIdx
gueDev_succ_le         2D-found=True 3D-found=True equal-modulo-renaming=True
gue_highProb_incr_le   2D-found=True 3D-found=True equal-modulo-renaming=True
gueDelta               2D-found=True 3D-found=True equal-modulo-renaming=True
gueScale               2D-found=True 3D-found=True equal-modulo-renaming=True
gueGridK               2D-found=True 3D-found=True equal-modulo-renaming=True
```
The only difference is the qualified name `RBM.Loop.LoopIdx` (3D) vs the opened `LoopIdx` (2D); the check file already writes `RBM.Loop.LoopIdx`. Explicit-argument order of the calls in the source (`gueLproc_time d E t1 t0 K δ n m k ht10 hk ω`, `gueDproc_time … Kt n m k ht10 hk ω`, `gueDev_succ_le d E t1 t0 K n k hE ht10 ht0 hk ω`) matches the merged `Proc.lean:460, 469, 771` with `sz` first. `gueDev_succ_le` has the same increment term `η_{t₀}⁻¹^2 (√(Δ/N)·Σ‖X‖ + Δ)` as in the `Bounds_jump_le` call. `gue_highProb_incr_le sz n0 hsize` (`Markov.lean:863`): same shape as the source `highProbAt_hF` body. `stochDomAt_of_forall_highProbAt` (`BootstrapAt.lean:551`) has `h : ∀ τ > 0, HighProbAt P size (fun N => {ω | ∀ u, ξ N u ω ≤ size^τ * ζ N u ω})`; `perTimeCalc_highProbAt_of_stochDomAt` (`PerTimeCalc.lean:130`) and `_mono` (`:112`) are the source's `RBM.Ind.PerTimeCalc` calls (`P`, `size` implicit as in 2D). No merged twin differs.

### §29 fixed checks, one line each (DECISIONS §29 (1)-(4), §45 O2 (5)-(7), §34 argument order)
1. Time domain `0 ≤ t₁ ≤ t₀ < 1`: `Bounds_path` carries `ht1 ht10 ht0` as hypotheses; the check text has them; instance `0.99 ≤ 0.995`.
2. Boundary `1 - ilambda²/L²` / `ilambda > L`: not used by `BoundsA`; the only boundary is `hellN` `L^d(1-t₁) ≤ 1` (hypothesis; zero-mode regime of O4).
3. `L^d ≤ W^K`: not used (the instance has `L=4 ≤ W=32`, but no step needs it); `W^d` vs `N` enters only via `T3`, above.
4. `∀ n` vs `∀ᶠ n`: `Bounds_path` is pathwise at one `n` (no `∀ n` quantifier); `highProbAt_*` carry no `n`-bound; `hF` needs `size → ∞`, which is the `Tendsto` hypothesis.
5. `PrecPT` vs `Prec`: not applicable (`HighProbAt` on the event with `∀ u` inside; union inside the probability).
6. Parameter lower bounds from `(eq:WO)`/`SizeTendsto`: `size → ∞` is explicit in `hF`; `0<τ₁` is explicit; `Bounds_path` assumes only the stated inequalities at the one `n`.
7. Scale vs consumer: thresholds are `N^τ` with `N = sz.size n` (the scale of `GUEPathBounds`), not `(log W)^k`.
8. Argument order of the calls: `HC`, `Concl`, targets are pinned by the check file; the explicit order of `gueH sz t1 t0 K n k ω`, `gridTime t1 t0 K n k`, `loopL d L W (blockMat d L W M)` is as in `Grid.lean:61-110`/`Proc.lean`.

### Verdict per target
- `HC`, `Concl`: PASS (definitions; `(W^d)⁻¹` is the only d-token).
- `Bounds_path`: PASS (hypotheses jointly satisfiable at the instance; `L^d` form of `hellN` is necessary and sufficient for `T3`; all other lines dimension-free).
- `highProbAt_HC`, `highProbAt_hA`, `highProbAt_hB`, `highProbAt_hD`: PASS (pure transcription of `perTimeCalc_*`; the `StochDomAt` hypotheses are other gates' outputs and stay hypotheses).
- `highProbAt_hF`: PASS (the merged `gue_highProb_incr_le`; limit computed above).
- `pathBounds_of_forall_highProbAt`: PASS (`stochDomAt_of_forall_highProbAt` + `perTimeCalc_highProbAt_mono`; conditional on the w.h.p. conclusion, as the ticket says).

## (a′) Preflight corrections — Thu Oct  8 11:52:53 UTC 2026
Section (a), last line of (i): "Re-derivations needed ...: `one_le_rpow`, `size_eq`". The RBM2D source calls Mathlib's `Real.one_le_rpow` (BoundsA.lean:542 here, `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:678`), so only the four `GoodEvent_*`, `im ≤ 1` and `size = W^d L^d` (inside `Bounds_T3`) are re-derived. No verdict changes.

## (b) Script output — commit c7bc524 on t/T2330
```
$ date -u; git log --oneline -1; git diff --stat main...t/T2330
Thu Oct  8 11:37:11 UTC 2026
c7bc524 T2330: UN-33 Universality/GUEPhase/BoundsA (Bounds_path, BoundsACheck, instances)
 RBM3D/Test/Axioms.lean                   |   2 +-
 RBM3D/Universality/GUEPhase/BoundsA.lean | 920 +++++++++++++++++++++++++++++++
 2 files changed, 921 insertions(+), 1 deletion(-)
$ lake build RBM3D.Universality.GUEPhase.BoundsA 2>&1 | tail -1; lake env lean RBM3D/Universality/GUEPhase/BoundsA.lean; echo lean_exit=$?   (no warning from BoundsA.lean)
Build completed successfully (3763 jobs).
lean_exit=0
$ lake build 2>&1 | tail -1   (full library; RBM3D.lean does not import BoundsA before the hub's merge, the precheck below covers it)
Build completed successfully (4138 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/GUEPhase/BoundsA.lean | wc -l
       0
$ lake env lean ax.lean | python3 axfmt.py   (#print axioms of the targets, HC, Concl and the compiled instance theorem)
Bounds_path: [propext, Classical.choice, Quot.sound]
BoundsACheck.HC: [propext, Classical.choice, Quot.sound]
BoundsACheck.Concl: [propext, Classical.choice, Quot.sound]
BoundsACheck.highProbAt_HC: [propext, Classical.choice, Quot.sound]
BoundsACheck.highProbAt_hA: [propext, Classical.choice, Quot.sound]
BoundsACheck.highProbAt_hB: [propext, Classical.choice, Quot.sound]
BoundsACheck.highProbAt_hD: [propext, Classical.choice, Quot.sound]
BoundsACheck.highProbAt_hF: [propext, Classical.choice, Quot.sound]
BoundsACheck.pathBounds_of_forall_highProbAt: [propext, Classical.choice, Quot.sound]
BoundsAInst.highProbAt_hF_sz0: [propext, Classical.choice, Quot.sound]
$ python3 stmts.py   (target statements extracted from RBM3D/Universality/GUEPhase/BoundsA.lean, whitespace-normalized, wrapped at 300)
def HC (E t1 t0 : ℕ → ℝ) (n0 : ℕ) (τU τ₁ : ℝ) (n : ℕ) (ω : PathΩ sz) : Prop := ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)), {ω' : PathΩ sz | ∀ a b : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE
    (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) a b‖ ≤ gueDelta sz τU n}.indicator (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n))
    ℂ)) i j‖ ^ 2) ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueLmax sz E t1 t0 (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
abbrev Concl (E t1 t0 : ℕ → ℝ) (n0 : ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (τ : ℝ) (n : ℕ) (ω : PathΩ sz) : Prop := (∀ m : ℕ, 1 ≤ m → m ≤ n0 → ∀ (k : Fin (gueGridK sz n0 n + 1)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
    (gueH sz t1 t0 (gueGridK sz n0) n k ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf σ a) - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf σ a)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ m) ∧ (∀ (k : Fin (gueGridK sz n0 n + 1)) (i j
    : Idx d (sz.L n) (sz.W n)), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n
    k))⁻¹ ^ ((1 : ℝ) / 2))
theorem Bounds_path {τU : ℝ} (n0 : ℕ) (hn0 : 2 ≤ n0) {E t1 t0 : ℕ → ℝ} (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n : ℕ) (hτU : 0 < τU) (hEb : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) {τ τ₁ : ℝ} (hτ₁0 : 0 < τ₁) (hτ₁τ : τ₁ < τ) (hscN : ∀ t ∈ Set.Icc (t1 n) (t0 n),
    (gueScale sz E n t)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU)) (hellN : ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 1) (hsmallN : ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁ - τU / 2) ≤ 1 / 32) (h4N : 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - τ₁)) (ω : PathΩ sz) (hA : ∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0), gueLproc sz E t1
    t0 (gueGridK sz n0) (gueDelta sz τU) n u.2 u.1 ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ ((u.2 : ℕ) - 1)) (hB : ∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0, gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n u.2 u.1 ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^
    (u.2 : ℕ)) (hC : ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)), {ω' : PathΩ sz | ∀ a b : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L
    n) (sz.W n)) ℂ)) a b‖ ≤ gueDelta sz τU n}.indicator (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ^ 2) ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueLmax sz
    E t1 t0 (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) (hD : ∀ i j : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n 0 ω) (zt (E n) (t1 n)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale
    sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)) (hF : ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n → ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)) : BoundsACheck.Concl sz E t1 t0 n0 Kt τ n ω := by
theorem highProbAt_HC (τU : ℝ) (hτ₁ : 0 < τ₁) (h : StochDomAt (Pgue sz) sz.size (fun n (p : Fin (gueGridK sz n0 n + 1) × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) ω => {ω' : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω') (zt (E n) (gridTime
    t1 t0 (gueGridK sz n0) n p.1)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ≤ gueDelta sz τU n}.indicator (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n p.1 ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) - mE (E n) • (1 : Matrix (Idx d (sz.L
    n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) p.2.1 p.2.2‖ ^ 2) ω) (fun n p ω => gueLmax sz E t1 t0 (gueGridK sz n0) n 2 p.1 ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) : HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | HC sz E t1 t0 n0 τU τ₁ n ω}) :=
theorem highProbAt_hA (τU : ℝ) (hτ₁ : 0 < τ₁) (h : StochDomAt (Pgue sz) sz.size (fun n (p : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0)) ω => gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n p.2 p.1 ω) (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaT (E n) p.1)⁻¹ ^ ((p.2 : ℕ) - 1))) : HighProbAt (Pgue
    sz) sz.size (fun n => {ω : PathΩ sz | ∀ u : TimeIcc t1 t0 n × Set.Icc 2 (2 * n0), gueLproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n u.2 u.1 ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ ((u.2 : ℕ) - 1)}) :=
theorem highProbAt_hB (τU : ℝ) (hτ₁ : 0 < τ₁) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (h : StochDomAt (Pgue sz) sz.size (fun n (p : TimeIcc t1 t0 n × Set.Icc 1 n0) ω => gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n p.2 p.1 ω) (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaT (E
    n) p.1)⁻¹ ^ (p.2 : ℕ))) : HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | ∀ u : TimeIcc t1 t0 n × Set.Icc 1 n0, gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n u.2 u.1 ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n u.1)⁻¹ ^ (u.2 : ℕ)}) :=
theorem highProbAt_hD (hτ₁ : 0 < τ₁) (h : StochDomAt (Pgue sz) sz.size (fun n (ij : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) ω => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n 0 ω) (zt (E n) (t1 n)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) ij.1 ij.2‖)
    (fun n _ _ => (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2))) : HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n 0 ω) (zt (E n) (t1 n)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i
    j‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * (gueScale sz E n (t1 n))⁻¹ ^ ((1 : ℝ) / 2)}) :=
theorem highProbAt_hF (hsize : Tendsto (fun n => sz.size n) atTop atTop) : HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | ∀ k, 1 ≤ k → k ≤ gueGridK sz n0 n → ∀ i j : Idx d (sz.L n) (sz.W n), ‖Sizes.seqXmat sz n (ω k) i j‖ ≤ ((sz.size n : ℕ) : ℝ)}) :=
theorem pathBounds_of_forall_highProbAt (E t1 t0 : ℕ → ℝ) (n0 : ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hmain : ∀ τ : ℝ, 0 < τ → HighProbAt (Pgue sz) sz.size (fun n => {ω : PathΩ sz | Concl sz E t1 t0 n0 Kt τ n ω})) : GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt := by
```
```
$ python3 -I eqcheck.py   (docstring-stripped, whitespace-normalized text of `def HC` / `abbrev Concl`: T2330-check.lean vs BoundsA.lean)
HC equal: True 716 716
Concl equal: True 912 912
$ lake env lean eqscratch.lean   (= T2330-check.lean + `import RBM3D.Universality.GUEPhase.BoundsA` + `example {d : ℕ} (sz : Sizes d) : T2330_<n> sz := <n> sz` for the 7 names)
Bounds_path highProbAt_HC highProbAt_hA highProbAt_hB highProbAt_hD highProbAt_hF pathBounds_of_forall_highProbAt
exit=0  error lines: 0
$ lake env lean precheck.lean   (uncommitted scratch: import RBM3D; import RBM3D.Universality.GUEPhase.BoundsA; #assert_rbm_axioms)
Thu Oct  8 11:42:03 UTC 2026
exit=0
axiom audit: 9921 theorems, 2978 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 143 (borrowed 1, owed 83, structural 41, refuted 6, superseded 12).
registry: 2 borrowed + 136 owed + 105 structural + 7 refuted + 13 superseded; 120 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ name-clash grep: grep -rn --include=*.lean -F <name> RBM3D RBM3D.lean | grep -v Probe/ | grep -v BoundsA.lean | wc -l   (hits per name)
Bounds_path=0 BoundsACheck=1 BoundsAInst=0 pathBounds_of_forall_highProbAt=1 highProbAt_HC=0 highProbAt_hA=0 highProbAt_hB=0 highProbAt_hD=0 highProbAt_hF=0 
RBM3D/Test/Axioms.lean:228:   `RBM.Univ.GUEPhase.GUEPathBoun
$ diff <(sed -n 43,236p RBM2D/Universality/GUEPhase/BoundsA.lean) <(sed -n 59,252p RBM3D/Universality/GUEPhase/BoundsA.lean)   (the eight real-variable helpers vs the source)
3c3
< open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
---
> open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Univ
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h -- RBM2D/Universality/GUEPhase/BoundsA.lean; git -C ../RBM2D --no-optional-locks diff --stat 81fca44 HEAD -- RBM2D/Universality/GUEPhase/BoundsA.lean | wc -l; git -C ../RBM2D --no-optional-locks log -1 --format=%h
81fca44
0
9e0f275
$ printf "import RBM3D
#assert_rbm_axioms
" > precheck0.lean; lake env lean precheck0.lean | sed -n 145,146p   (baseline without BoundsA, same worktree; premises found / registry lines)
premises found by scanning: 144 (borrowed 1, owed 84, structural 41, refuted 6, superseded 12).
registry: 2 borrowed + 136 owed + 105 structural + 7 refuted + 13 superseded; 119 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
```
$ awk <instance lines of RBM3D/Universality/GUEPhase/BoundsA.lean, docstrings stripped>   (namespace RBM.Univ.GUEPhase.BoundsAInst; sz0 = merged RBM.Gauss.SizesInst.sz0: d = 3, n = 0, L = 4, W = 32, N = 2097152; private lemmas Inst_hscN, Inst_hsmallN, Inst_h4N, Inst_hellN discharge the four numeric hypotheses at n0 = 2, E = 0, t1 = 99/100, t0 = 199/200, tauU = 3/5, tau1 = 1/50, tau = 1/10)
788: private abbrev E0 : ℕ → ℝ := fun _ => 0
789: private abbrev t1c : ℕ → ℝ := fun _ => 99 / 100
790: private abbrev t0c : ℕ → ℝ := fun _ => 199 / 200
example (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ) :=
  Bounds_path sz0 (τU := 3 / 5) 2 le_rfl (E := E0) (t1 := t1c) (t0 := t0c) Kt 0
    (by norm_num) (by norm_num [E0]) (by norm_num [t1c]) (by norm_num [t1c, t0c])
    (by norm_num [t0c]) (τ := 1 / 10) (τ₁ := 1 / 50) (by norm_num) (by norm_num)
    Inst_hscN Inst_hellN Inst_hsmallN Inst_h4N
example :=
  BoundsACheck.highProbAt_HC sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (3 / 5) (by norm_num)
example :=
  BoundsACheck.highProbAt_hA sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (3 / 5) (by norm_num)
example (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ) :=
  BoundsACheck.highProbAt_hB sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (3 / 5) (by norm_num) Kt
example :=
  BoundsACheck.highProbAt_hD sz0 E0 t1c t0c 2 (τ₁ := 1 / 50) (by norm_num)
theorem highProbAt_hF_sz0 :
    HighProbAt (Pgue sz0) sz0.size (fun n => {ω : PathΩ sz0 | ∀ k, 1 ≤ k → k ≤ gueGridK sz0 2 n →
      ∀ i j : Idx 3 (sz0.L n) (sz0.W n), ‖Sizes.seqXmat sz0 n (ω k) i j‖ ≤ ((sz0.size n : ℕ) : ℝ)}) :=
  BoundsACheck.highProbAt_hF sz0 2 MarkovInst.sz0_size_tendsto_nat
example (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ) :=
  BoundsACheck.pathBounds_of_forall_highProbAt sz0 E0 t1c t0c 2 Kt
example : (200 : ℝ) ^ 2 *
      (Real.sqrt (((1 / 200) / (2097153 : ℝ) ^ 128) / 2097152) * (2097152 : ℝ) ^ 3 +
        (1 / 200) / (2097153 : ℝ) ^ 128) ≤ (2097152 : ℝ) ^ (-((3 / 5 : ℝ) / 4)) / 2 :=
  Bounds_jump (N := 2097152) (S := 2097152) (e := 200) (Δ := (1 / 200) / (2097153 : ℝ) ^ 128)
    (Sg := (2097152 : ℝ) ^ 3) (δ := (2097152 : ℝ) ^ (-((3 / 5 : ℝ) / 4))) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) (by norm_num)
    (by positivity) (by norm_num)
    (by
      rw [Nat.cast_ofNat, one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
example : 2 * ((2097152 : ℝ) ^ (1 / 50 : ℝ)) ^ 2 * (2097152 : ℝ) ^ (-(3 / 5 : ℝ)) ≤
    ((2097152 : ℝ) ^ (-((3 / 5 : ℝ) / 4)) / 4) ^ 2 :=
  Bounds_rpow_key (by norm_num) (by simpa [Inst_size_real] using Inst_hsmallN)
example : (1 / 10 : ℝ) ≤ 2 * Real.sqrt 1 :=
  Bounds_final (x := 1 / 10) (p := 1) (P := 2) (Λ := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
example : ∀ k ≤ 3, ∀ i ≤ k, (fun _ : ℕ => (1 / 10 : ℝ)) i < 1 :=
  Bounds_unfreeze (K := 3) (fun _ => (1 / 10 : ℝ)) 3 (δ := 1) (fun k hk _ => hk)
    (by norm_num) (fun j _ _ _ => by norm_num) (fun j _ => by norm_num) (by norm_num)
$ lake env lean scratch_inst.lean   (BoundsA.lean with each `example` renamed `def instN`; `#check @inst1`: only the five pathwise hypotheses of Bounds_path remain)
inst1 : ∀ (Kt : (n : ℕ) → ℝ → Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ) (ω : PathΩ sz0),
  ... five hypotheses (hA hB hC hD hF) ...
BoundsACheck.Concl sz0 E0 t1c t0c 2 Kt (1 / 10) 0 ω
```

### Narrative
- Port of RBM2D `Universality/GUEPhase/BoundsA.lean` (718 lines; last commit touching it 81fca44; its diff to RBM2D HEAD 9e0f275 is empty, see the `wc -l` = 0 above) into `RBM3D/Universality/GUEPhase/BoundsA.lean` (920 lines). Imports exactly `Proc`, `BootstrapAt`, `Markov` (nothing else was needed). Only the two files of the ticket are in `git diff --stat main...t/T2330`.
- The eight real-variable helpers (`Bounds_le_firstHit`, `_unfreeze`, `_sq_le`, `_jump`, `_rpow_key`, `_le_of_sqrt`, `_le_of_sq`, `_final`, file lines 59-252) differ from the source lines 43-236 only in the `open` line (`diff` of the two ranges: one line, `+ RBM.Univ`). The remaining lemmas and `Bounds_path` are the source text renamed as in the ticket (`d : Sizes` to `sz : Sizes d`, `Z2` to `Zd d`, `spectralZ/M` to `zt/mE`, `gloop … (blockMat M)` to `loopL d … (blockMat d … M)`, `Idx` with `d`).
- The two `d`-dependent lines: `(W^d)⁻¹` in `HC` and in `Bounds_T3`, and `hellN : L^d (1 - t₁) ≤ 1`. In `Bounds_T3` the identity `N = W^d L^d` is `unfold Sizes.size; push_cast; rw [mul_pow]`; `Bounds_sum_le` uses `Sizes.card_Idx` (replacing RBM2D `flucAvg_card_Idx_eq_size`). `Bounds_gridStep_nonneg/_gridTime_zero/_gridTime_mono/_gridTime_le` and `Bounds_im_le_one` are local re-derivations (the RBM3D names `GoodEvent_*`, `MLExpVocab_im_le_one` do not exist: 0 hits outside BoundsA.lean).
- `HC`, `Concl` are the check text (equality script above), placed before `Bounds_path`. The conclusion of `Bounds_path` is `BoundsACheck.Concl …` (the check's text); its hypothesis `hC` is the unfolded form of the source, not `HC …`. Reason: the registry pre-check at 11:32:39 UTC (first run, with the unfolded conclusion) exited 1 with "1 premise(s) … in none of `borrowedProps`, … `[RBM.Univ.GUEPhase.BoundsACheck.Concl]`" (`scanPremises`, `RBM3D/Test/Axioms.lean:447`: a Prop-valued def that some theorem assumes and no theorem concludes). With `Concl` as the conclusion head of `Bounds_path` the scan passes (exit 0 above). By the same rule `HC` as a hypothesis would be flagged (not tested); the check-equality examples elaborate with the unfolded `hC` by delta (exit 0 above).
- Registry: the `GUEPathBounds` line is kept and its comment extended as the ticket says. The pre-check output shows the effect of `pathBounds_of_forall_highProbAt` (its conclusion head is `GUEPathBounds`): without BoundsA `premises found … 144 (… owed 84 …)`, `119 registered premise(s) carry nothing yet`; with BoundsA `143 (… owed 83 …)`, `120` (`GUEPathBounds` moved to the "carry nothing yet" list).
- Instances: `Bounds_path` at `sz0` (d = 3, n = 0, N = 2097152) with all twelve deterministic hypotheses discharged (`Inst_hscN`, `Inst_hsmallN`, `Inst_h4N`, `Inst_hellN` plus `norm_num`); the five pathwise hypotheses `hA hB hC hD hF` stay as hypotheses (`#check @inst1`). The five `highProbAt_*` and `pathBounds_of_forall_highProbAt` are applied at the same data with their `0 < τ₁` discharged; the `StochDomAt` / `hmain` inputs of other gates remain hypotheses. `highProbAt_hF_sz0` is fully discharged (`MarkovInst.sz0_size_tendsto_nat`), `n₀ = 2`. The real-variable core (`Bounds_jump`, `Bounds_rpow_key`, `Bounds_final`, `Bounds_unfreeze`) is instantiated at the numbers of section (a)(ii) (`Δ = (1/200)/(N+1)^128`, `Sg = N³`, `δ = N^{-3/20}`).

## (c) Verified Mathlib names (all compile in `BoundsA.lean`; file:line by grep)
`Real.one_le_rpow` (Pow/Real.lean:678); `Real.sqrt_eq_rpow` (Pow/Real.lean:986); `Real.sqrt_le_iff` (Real/Sqrt.lean:228); `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_pos_of_pos`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_natCast`, `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.iSup_le`; `pow_le_pow_iff_left₀` (Algebra/Order/GroupWithZero/Basic.lean:682); `pow_le_one_iff_of_nonneg` (:708); `inv_anti₀` (:1221); `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `inv_le_one₀`, `le_ciSup`; `MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt` (Probability/Process/HittingTime.lean:197); `Set.indicator_of_mem`, `Nat.min_eq_left`, `Nat.one_le_pow`, `Nat.cast_ofNat`. Absent from RBM3D (grep, 0 hits outside BoundsA.lean): `GoodEvent_gridTime_le/_mono/_zero`, `MLExpVocab_im_le_one`; `GoodEvent_gridStep_nonneg` occurs only in a docstring of `Induction/AzumaProxyN2.lean:50` stating it does not exist.

## (d) Open issues and paper-delta candidates
- T2330a (registry, dispatcher): `pathBounds_of_forall_highProbAt` is conditional on `hmain`, but the axiom-audit scan treats its conclusion `GUEPathBounds` as proved (numbers in the narrative); consumers UN-44/47/50/51 still assume `GUEPathBounds` unproved. The registry line is kept as ordered; the dispatcher may want a ledger note or a certificate.
- T2330b (Lean/paper difference, d-dependent lines): `hellN : L^d (1 - t₁) ≤ 1` and `(W^d)⁻¹` replace RBM2D `L²`, `(W²)⁻¹`. The paper (`paper/tex/1_2_Intro_model_result.tex:566-570`) only says the GUE phase is "essentially identical to [YY_25, Theorem 2.6]", so there is no d ≥ 3 statement to compare with. Section (a)(ii) shows the literal d = 2 form is not enough at d = 3 (`t₁ = 15/16`: `L²(1-t₁) = 1` but `N η_{t₁} = 131072 > W^d = 32768`, so (T3) fails).
- T2330c: `Bounds_path` is not applicable at the `GridCheck` times of `Grid.lean` (`t₁ = (1 - ouZeta(1/20))·9/10 ≈ 0.856`: `L^d(1-t₁) = 9.2 > 1`, section (a)(ii)); consumers must take `t₁` in the zero-mode regime of O4 (`L^d (1 - t₁) ≤ 1`).
- T2330d: `hC` of `Bounds_path` is the unfolded form of `BoundsACheck.HC` (defeq, verified by the check-equality examples); the reason is the registry scan above.
- Not proved here (as the ticket says): the w.h.p. conclusion `hmain` of `pathBounds_of_forall_highProbAt` for every `τ > 0`, and the `StochDomAt` inputs of `highProbAt_HC/hA/hB/hD`.
