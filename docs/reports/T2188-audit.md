Auditor model: claude-opus-5-5

# T2188 audit (round 1) — UN-05 rest, `Universality/GreenCorr` (`unGreenCorr`, `greenCorrAll`)

Written: Mon Oct  5 15:10:38 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2188-audit1`,
detached at `t/T2188` = `939857e`.

## 0. Diff scope

```
$ git diff --stat main...t/T2188
 RBM3D/Test/Axioms.lean            |    2 -
 RBM3D/Universality/GreenCorr.lean | 1004 +++++++++++++++++++++++++++++++++++++
$ git diff main...t/T2188 -- RBM3D/Test/Axioms.lean   (the only two hunks)
-   `RBM.Univ.UNGreenCorr, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
-   `RBM.Univ.UNGreenCorrAll, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```
These are the sole writable files. The registry edit deletes exactly the two owed lines the ticket names.
`Pins.lean` is untouched, so the pins and frozen signatures are unchanged.

## 1. Statements against the pins

```
$ cat stmt.lean
import RBM3D.Universality.GreenCorr
open Filter
example : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d), Tendsto (fun n => sz.size n) atTop atTop →
    ∀ M : RBM.Univ.UNModel sz, RBM.Univ.UNGreenCorr sz M := @RBM.Univ.unGreenCorr
example : RBM.Univ.UNGreenCorrAll := RBM.Univ.greenCorrAll
#check @RBM.Univ.unGreenCorr
#check @RBM.Univ.greenCorrAll
$ lake env lean stmt.lean; echo "exit $?"
@RBM.Univ.unGreenCorr : ∀ {d : ℕ} (sz : RBM.Gauss.Sizes d),
  Tendsto (fun n => sz.size n) atTop atTop → ∀ (M : RBM.Univ.UNModel sz), RBM.Univ.UNGreenCorr sz M
RBM.Univ.greenCorrAll : RBM.Univ.UNGreenCorrAll
exit 0
```
- Target 1 has the ticket's exact binder list (`sz`, `hsize`, `M`) and its conclusion is the merged pin
  `UNGreenCorr sz M` (`Pins.lean:535`). The pin covers every `E, k, c' > 0, Cn`, and `τ₀` comes before `τU`.
  Hypotheses `(417)` for `nf ≤ k` plus `UNApriori`. Every test function `O`, and every `r, a, b` with `0 < a` and `∀ᶠ n, a ≤ r n ≤ b`.
- Target 2's conclusion is the merged pin `UNGreenCorrAll` (`Pins.lean:546`).
- Witness `τ₀ = c' / (2 * (gccCmax k Cn + 1))` (`GreenCorr.lean:866`). It depends only on `k, c', Cn`, as the ticket requires.

The public non-target `greenCorr_step` (recommended by the ticket) differs from RBM2D `gcc_step` (`c9a24cf`, `:484`) as follows.
```
$ diff <(git -C ../RBM2D show c9a24cf:RBM2D/Universality/GreenCorr.lean | sed -n 484,515p) <(sed -n 489,520p GreenCorr.lean)
< private theorem gcc_step (t₁ : ℝ) {k : ℕ} {O : (Fin k → ℝ) → ℝ} (E : ℝ)
---
> theorem greenCorr_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
>     {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
>     {H0 H1 : Ω → Matrix ι ι ℂ} (hm0 : Measurable H0) (hm1 : Measurable H1)
>     (hH0 : ∀ ω, (H0 ω).IsHermitian) (hH1 : ∀ ω, (H1 ω).IsHermitian)
<     (hdec : ∀ lam : Idx L W → ℝ, ...      >     (hdec : ∀ lam : ι → ℝ, ...
<     (hCs : ∀ i, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ...   >     (hCs : ∀ i, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ...
>     (hε₀ : Nr ^ (-τU) ≤ ε₀)
<   ... ouMat L W 0 / ouMat L W t₁ ∂(ouP L W)   >   ... H0 ω / H1 ω ∂P
```
(Lines are abbreviated by hand, but the diff contains only these hunks.) These are change (A), the generic carrier,
and change (B)(iii), `ε ≤ ε₀` with `N^{-τU} ≤ ε₀`. The bound `K (N^{-c'+Cτ_U} + N^{-τ_U/2})` and every other hypothesis are unchanged.

`gcc_quantitative` (`:701`) bounds the dilation constant uniformly in `n`, as `K = 2^k Σ|c_i|(μa^k ∫|Oj i| + 2 Cs_i·mb·ca^k)`.
Here `μa = max 1 a⁻¹`, `ca = max 1 a⁻²` and `mb = max 1 b`, so this matches the ticket's `K̄`. The window radius is `R/a + 1`.
`gcc_tendsto` (`:820`) is the explicit-threshold form and has no extra hypotheses.

Per-target statement verdict: target 1 PASS, target 2 PASS.

## 2. Vacuity, hidden hypotheses, cycles

- No hypothesis is hidden in a structure. The only premises are `hsize` and the pin's own premises, `UNClaim417` and `UNApriori`, which are other gates' pins.
- The file imports `PoissonSmoothing` and `EigenMeasurable`, both merged, so it has no cycle.
- No external hypothesis is added (the pin's model-independent comparison is internal, DECISIONS §5).
- `sorry`/`admit`/`axiom`/`native_decide`: `grep -nE "sorry|admit|axiom|native_decide" GreenCorr.lean` matches only the
  `#print axioms` lines `:994-1000`.

## 3. Compiled nonempty instances (`GreenCorrCheck`, `:880-992`)

All of them use `d = 3` and `sz = sz0`, with `sz0.size 0 = 2097152` proved by `sz0_values`. They take `E = 0`, `k = 1`, `c' = 1`, `Cn ≡ 1` and `O = bump`.
`bump 0 = 1` and `bump (3) = 0` (`bump_nondegenerate`), and `IsTestFun` is discharged by `bump_testFun`. `size → ∞` is discharged by `sz0_size_tendsto`.
- `instance_band` (`:892`): `unGreenCorr` for `UNModel.band sz0`, with `r ≡ rhoSC 0`, `a = b = rhoSC 0`, and `0 < rhoSC 0` from `rhoSC_pos`.
- `instance_ba` (`:918`): `UNModel.ba sz0`, with the non-constant `r n = 1 + 1/(n+1)` (`r 0 ≠ r 1` is proved). It takes `a = 1`, `b = 2`, and the bounds are proved for every `n`.
- `instance_greenCorrAll` (`:945`): `greenCorrAll 3 le_rfl sz0 … (UNModel.band sz0)`, with `r ≡ 1`.
- `instance_greenCorrAll_tauU` (`:967`): `τU = 1/10 ≤ τ₀ = 1/4`, with `gccCmax 1 1 = 1` discharged.
  It uses the BA model and the non-constant `r`.
In all four, only `UNClaim417 …` and `UNApriori …` remain as hypotheses. Each instance's data is nondegenerate and the dilation window is not collapsed (`instance_ba` has `a < b`).
Both targets have an instance: PASS.

## 4. Build and axioms

```
$ lake build RBM3D.Universality.GreenCorr ; echo exit $?
(grep '^error' build.log: no lines; 7 lines mention GreenCorr.lean: the axiom prints below)
info: RBM3D/Universality/GreenCorr.lean:994:0: 'RBM.Univ.unGreenCorr' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:995:0: 'RBM.Univ.greenCorr_step' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:996:0: 'RBM.Univ.greenCorrAll' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:997:0: 'RBM.Univ.GreenCorrCheck.instance_band' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:998:0: 'RBM.Univ.GreenCorrCheck.instance_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:999:0: 'RBM.Univ.GreenCorrCheck.instance_greenCorrAll' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/GreenCorr.lean:1000:0: 'RBM.Univ.GreenCorrCheck.instance_greenCorrAll_tauU' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3337 jobs).
exit 0
```
Registry pre-check:
```
$ printf 'import RBM3D\nimport RBM3D.Universality.GreenCorr\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean; echo "lean exit $?"
lean exit 0
axiom audit: 5546 theorems, 1977 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
```
Name-clash check: `grep -rnE "theorem (unGreenCorr|greenCorrAll|greenCorr_step)\b|namespace GreenCorrCheck" RBM3D/` on `main`,
excluding the new file, gives `0` hits. Port citation:
`git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GreenCorr.lean` gives `1 file changed, 36 insertions(+), 120 deletions(-)`.
This matches the ticket.

## 5. Paper deltas

- The only statement-level difference from the paper and from RBM2D is the dilation sequence `r_n ∈ [a,b]`. It is already
  `docs/paper-deltas.md:1344` (**D385**, T2162d).
- The generic-carrier `greenCorr_step` is an internal lemma and makes no paper statement.
- The prove report (d) proposes no new candidate. The coverage is complete.

## Observations (no verdict effect)

- `greenCorr_step` is public, but it is not a target and has no instance of its own. It is applied inside `unGreenCorr` and
  so inside every instance above. The ticket recommends it but does not pin it.
- Unlike RBM2D, `greenCorr_step` does not require `ε₀ ≤ 1`. It is still applied only with `ε₀ = mb⁻¹ = (max 1 b)⁻¹ ≤ 1` (`:739`, `:765`, `:792`).

## Verdict

- `unGreenCorr`: **PASS**
- `greenCorrAll`: **PASS**

Ticket T2188: **PASS**. No dispatcher sign-off is needed.
