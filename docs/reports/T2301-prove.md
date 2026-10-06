Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 13:59:24 UTC 2026

Source for the mathematics: RBM2D `KPrim.lean` at `c9a24cf` lines 1-797 (read with `git show`), the ticket's check file `docs/tickets/checks/T2301-check.lean` §2 (pins), merged `ThetaTilde_eq`, `sum_Theta_row_of_three_le`, `sum_SB_row`, `norm_SB`, `KLgen`, `primRhsGUE`, `profPMTilde/profPPTilde`. Notation: `μ = m(σ₁)m(σ₂)`, `p = 1 - t₁μ`, `q = 1 - tμ`, `s = t - t₁`, `β(t) = sμ/(L^d p q)`.

### (i) Exponent table

| # | Quantity | Value (d ≥ 3 / source d = 2) | Constraint it must satisfy | Slack / check |
|---|---|---|---|---|
| 1 | `W` exponent in `kTwoGUE` and in `primRhsGUE` | `W^{-d}` in `K₂`, `W^{+d}` in (7.33) / `W^{-2}`, `W^{2}` | derivative identity: `K₂' = W^{-d}μ²/(L^d q²)` must equal `W^d·L^{-d}·(W^{-d}μ)²·(p⁻¹+L^dβ)²`; W-exponent `d - 2d = -d` | exact, 0 slack, any `d`; `target 5` hand check: `L.h.s. = W^{-d}μ²/(L^d q²) = r.h.s.` using `q + sμ = p` |
| 2 | `L` exponent: `gueShift` denominator, `SBgue = L^{-d}`, `card (Zd d L)` | `L^d` / `L²` | `Σ_{a∈Zd d L} c = L^d c`; `L^d β = sμ/(pq)` so that `p⁻¹ + L^dβ = q⁻¹` | exact, 0 slack; `d` enters only as the exponent |
| 3 | Row/column sums `Σ_b Θ_ξ(g)_{ab} = (1-ξ)⁻¹` | `ξ = t₁μ`, `‖ξ‖ = t₁` | `‖ξ‖ < 1`, `3 ≤ L` (merged `sum_Theta_row_of_three_le`, `Theta_transpose_of_three_le`); `SB(g)` doubly stochastic for every real `g` (kernel `(1+2dg²)⁻¹` at 0 plus `2d` neighbours of `g²(1+2dg²)⁻¹`, needs `L ≥ 3` so the `2d` neighbours are distinct) | instance: `1 - ‖ξ‖ = 13/20`; row-sum error `1.3e-15` (below) |
| 4 | Coupling `g` | any real | none: kernel depends on `g²`; `Θ(g)`, `Θ̃(g)`, `SB(g)` all defined and bounded for all `g` | tested `g ∈ {1/64, 1/2, 1}` |
| 5 | Time window | `0 ≤ t₁ ≤ t ≤ t₀ < 1`; instance `[7/20, 7/10]` | `‖tμ‖ = t < 1` so `q ≠ 0` and `‖t₁μ‖ < 1`, since `|m(±)| = 1` for `|E| < 2` | `1 - t₀ = 3/10`; `t₁ = 7/20 ≥ 0` |
| 6 | Energy | `|E| < 2`; instance `E = 0`; at Lemma 2.8 `E = lemE z` | `|mSigma E σ| = 1` (`norm_mSigma`, `|E| ≤ 2`); for Lemma 2.8, `|lemE z| < 2` | `E = 0`, slack 2; `lemE(i) = 0` (below) |
| 7 | Zero-mode split (7.25) | `ζ ∈ [0,1]`, `t₁ = (1-ζ)t₀`, `ξ = t₀μ`, `‖ξ‖ < 1` | `ThetaTilde_eq`: `Θ̃_ξ = Θ_{ξ(1-ζ)} + ξζ/(L^d(1-ξ(1-ζ))(1-ξ)) J`; `β(t₀)` with `t₁ = (1-ζ)t₀` is `(t₀-t₁)μ/(L^d(1-t₁μ)(1-t₀μ)) = ξζ/(L^d(1-ξ(1-ζ))(1-ξ))`, identical | exact; instance `ζ = 1/2`, `t₁ = (1-1/2)(7/10) = 7/20` |
| 8 | Lemma 2.8 times, `t₀ = lemT z = ‖msc z‖²` | `lemT z ∈ (0,1)`; `(+,-)`: `μ = ‖mE‖² = 1`, `ξ = lemT`; `(+,+)`: `μ = mE²`, `ξ = lemT·mE² = msc²` (`msc_eq_sqrt_mul_mE`) | `lemT_pos`, `lemT_lt_one` (hz : `0 < Im z`); `t₁ = (1-ζ)lemT ≥ 0` | `z = i`: `lemT = 0.381966`, slack `1 - lemT = 0.618` |
| 9 | Bridge to `UNOUProfile.band` (targets 9, 10) | `profPMTilde sz n ζ z a b = ‖msc‖²·Θ̃(sz.lam n)_{‖msc‖²}/W^d`; `profPPTilde` with `msc²` | equals `lemT·kTwoGUE d (sz.L n)(sz.W n)(sz.lam n) …` by rows 7, 8 with `g = sz.lam n`, `W^d` cast the same (`((sz.W n : ℕ) : ℂ)^d`) | exact; numerics at `sz0 n=0` below |
| 10 | Pair count and Lipschitz constant of the length-`n+1` slice `{WF, length = n+1}` | `C = W^d·#{(k,l): 1 ≤ k < l ≤ n+1}·L^{2d}·(L^{-d}M) = W^d L^d M·n(n+1)/2` / `W²L²M·…` | the cut factors have lengths `k+(n+1)-l+1` and `l-k+1` (`length_cutGlueL/R`, `Loop/TreeRep.lean:86-92`), total `n+3`, each `≥ 2`; both equal `n+1` only if `n+1 = 2`, so on a slice with `n+1 ≥ 3` at most one factor has length `n+1`, so `Lip ≤ M L^{-d}` per `(a,b)` term; `M` = sup of `‖K_J‖` over lengths `2..n` on `[t₁,t₀]` (continuous on compact); Picard step `h = 1/(2(C+1))` has `Ch ≤ 1/2` | length 3 (`n = 2`, 3 pairs): `C = 100.57` (`g = 1/2`), `92.21` (`g = 1`); `72` / `66` steps (below), finite |
| 11 | `d`-token census of `:1-797` (script `cls.py`) | lattice-size `^ 2` (`W`, `L`): 55 tokens on 35 lines, all `→ ^ d`; `Z2`: 53 lines `→ Zd d L`; `card` step `ZMod.card, Fintype.card_prod`: line 202 only `→ card (Zd d L) = L^d` | scalar `^ 2` (keep): `:134` outer `(L²pq)²`, `:135`, `:192` `μ²`, `:196` outer square, `:256` ×3 (`‖msc‖² = re² + im²`), `:270`, `:287` `msc²` / `‖msc‖²`, `:291` | tokens `log`, `Kstab`, `(W * L)`, `neighbo`, `5`: 0 hits |
| 12 | §29 items | (1) time/`ζ`: rows 5, 7, 8; (2) n/a; (3) no `L`-`W` relation, `L^d`, `W^d`: rows 1-2; (4) no `∀ᶠ`, fixed `(d,L,W,g)`; (5) deterministic; (6) `3 ≤ L`, `NeZero W`, `|E| < 2`, `0 < Im z`, no `3 ≤ d`, no condition on `g`; (7) `W^{-d}`, `W^dL^{-d}` | all hypotheses are scalar/size conditions; no probabilistic or external input | the only upstream input is the merged `ThetaTilde_eq` (a proved theorem) and `msc` facts; no external hypothesis, so no limit computation applies |
| 13 | Consumer shapes | UN-31: `gueK_exists d L W hL g …` then `KLgen d L g W (mSigma E) t₁ I` (`= KLK d L g W E t₁ I` by `rfl`, `KLK := KLgen … (mSigma E)`); UN-47: row 8 then row 9; UN-48: `gueShift d L μ t1 t` unfolds with `L^d` | argument order `d L g W` in `KLgen/KLK`, `d L W g` in `kTwo`/`kTwoGUE` (as in the merged signatures read above) | consistent |

### (ii) One concrete nondegenerate instance

Instance: `d = 3`, `L = 3` (`|Z_L^d| = 27`, `N = (WL)^d = 216`), `W = 2`, `g ∈ {1/2, 1}`, `E = 0` (`m(+) = i`, `m(-) = -i`), `[t₁, t₀] = [7/20, 7/10]`, `ζ = 1/2`, `t = 1/2`, all four sign pairs, all `27 × 27` entries. Lemma 2.8 at `z = i`; the `UNOUProfile.band` bridge also at the sizes of `SizesInst.sz0` at `n = 0` (`d = 3`, `L = 4`, `W = 32`, `lam = 1/64`, matrix `64 × 64`).
Hypotheses checked at this data: `3 ≤ L`, `NeZero W`, `|E| < 2`, `0 ≤ t₁ ≤ t₀ < 1`, `‖t₁μ‖ = 7/20 < 1`, `‖t₀μ‖ = 7/10 < 1`, `tμ ≠ 1` (`|tμ| = 1/2`), `0 ≤ ζ ≤ 1`, `0 < Im z`, `(1-ζ)t₀ = t₁` (asserted in the script). No `N = 0`, empty index, collapsed window (`t₀ - t₁ = 7/20`) or large witness. The script reads the lattice kernel of `SB` from `Defs/Block.lean:38-41` (`sbKernel`: `(1+2dg²)⁻¹` at `0`, `g²(1+2dg²)⁻¹` at `zdistD = 1`) and computes `Θ`, `Θ̃` by direct matrix inverse.

Command (scratch script, Python/numpy only; no Lean) and verbatim output:

```
$ cd <scratchpad>/T2301 && python3 pf.py
== (A) d=3, L=3, W=2, E=0, [t1,t0]=[7/20,7/10], zeta=1/2 ==
N=(WL)^d = 216  |Z_L^d| = 27  |m(+)|= 1.0  m(+)= 1j
g=0.5: row sums SB: 2.220446049250313e-16  symmetric: 0.0
  self err 0.0e+00; (7.25) rel err 1.8e-15; d/dt (7.33) rel err 2.7e-09; Theta row-sum err 1.1e-15
  length-3 slice: M2=max|K2|=0.1552, C=3 W^d L^d M2=100.57, Picard step h=1/(2(C+1))=0.00492, steps=72
g=1.0: row sums SB: 2.220446049250313e-16  symmetric: 0.0
  self err 0.0e+00; (7.25) rel err 1.6e-15; d/dt (7.33) rel err 2.7e-09; Theta row-sum err 1.3e-15
  length-3 slice: M2=max|K2|=0.1423, C=3 W^d L^d M2=92.21, Picard step h=1/(2(C+1))=0.00536, steps=66
== (B) scalar identity (target kTwoGUE_deriv_identity), exact rationals, d=3 ==
lhs = 1/54  rhs = 1/54  equal: True
== (C) Lemma 2.8 at z=i, zeta=1/2 (targets lemT_mul_kTwoGUE_pm/pp and the profPM/PPTilde bridges) ==
msc(i)=0.000000+0.618034j lemT=0.381966 lemE=-0.00e+00 |mE|=1.000 0<=lemT<1: True
  d=3,L=3,W=2,g=1: pm rel err 1.7e-15, pp rel err 1.5e-15
  d=3,L=3,W=2,g=1/2: pm rel err 1.3e-15, pp rel err 1.1e-15
  sz0 n=0: d=3,L=4,W=32,g=1/64: pm rel err 3.5e-15, pp rel err 4.7e-15
```

What the lines test (all entries): `self err` = `kTwoGUE(t₁,t₁)` vs `kTwo` (target 2); `(7.25) rel err` = `kTwoGUE(·, (1-ζ)t₀, t₀)` vs `W^{-d} μ Θ̃_{t₀μ}` with `Θ̃` the direct inverse of `1 - ξ((1-ζ)SB + ζ L^{-d}J)` (target 3); `d/dt (7.33)` = central difference (`h = 1e-6`, `t = 1/2`) vs `W^d K S_GUE K` (targets 6, row 1); `Theta row-sum err` vs `(1 - t₁μ)⁻¹` (row 3); `(B)` is the exact-rational `kTwoGUE_deriv_identity` instance at `d = 3, W = 2, μ = 1, p = 13/20, q = 1/2, s = 3/20, L = 3` (`q + sμ = p` holds); `(C)` is `lemT·kTwoGUE(mSigma(lemE z), (1-ζ)lemT, lemT, σ₁, σ₂)` vs `W^{-d}ξ Θ̃_ξ` with `ξ = ‖msc‖²` for `(+,-)` and `ξ = msc²` for `(+,+)`, the right sides of targets 7, 8 and `profPMTilde`/`profPPTilde` (targets 9, 10). The length-3 existence data of row 10 is the Lipschitz constant of the length-3 slice; the sign of the hypotheses of `gueK_exists` (`|E| < 2`, `0 ≤ t₁ ≤ t₀ < 1`) holds at this instance.

Census command and output (`cls.py`, over lines 1-797 of the RBM2D source; comment text after `--` ignored; the `d` identifier occurs in code only in `:132-140` (scalar `d = t - t₁`, to be renamed `s`) and `g` only in `:611-747` (local `let g`, to be renamed):

```
$ python3 cls.py
Z2 (index type) lines: 53 e.g. [37, 71, 77, 85, 94, 111] ... [789, 790, 791]
card lines (ZMod.card / card_prod): [202]
lattice-size `^ 2` lines (L^2, W^2, pow_ne_zero 2, hL20): 35 lines; 55 tokens
  [65, 72, 96, 114, 134, 135, 136, 137, 139, 140, 155, 167, 172, 174, 175, 177, 190, 192, 194, 195, 196, 270, 287, 635, 652, 654, 685, 689, 699, 700, 706, 707, 713, 720, 726]
other `^ 2` (scalar candidates): 134 (1), 135 (1), 192 (1), 196 (1), 256 (3), 270 (2), 287 (2), 291 (1)
token 'Real.log' / 'Complex.log' / 'log ' / 'Kstab' / '(W * L)' / 'neighbo' / ' 5' in code lines 1-797: 0 each
```

Hand derivation of the two identities the numerics test (all with the same hypotheses as the pins): (1) `μ(L^dpq) - sμ(L^dp(-μ)) = μL^dp(q + sμ) = μL^dp²`, so the left side of target 5 is `W^{-d}μ²/(L^d q²)`; `p⁻¹ + L^d·(sμ/(L^dpq)) = (q+sμ)/(pq) = q⁻¹`, so the right side is `W^{-d}μ²L^{-d}q⁻²`. (2) `∂_t[(t-t₁)/(1-tμ)] = (1-t₁μ)/(1-tμ)²`, so `K₂' = W^{-d}μ²/(L^d q²)`; the right side of (7.33) at `n = 2` is `W^dL^{-d}(W^{-d}μ)²(Σ_aΘ_{a₁a}+L^dβ)(Σ_bΘ_{ba₂}+L^dβ)` with both brackets `= q⁻¹` (row sums `p⁻¹`; columns by `Θ^T = Θ`).

### Verdict

- Targets 1-4 (`gueShift`, `kTwoGUE`, `kTwoGUELoop`, `kTwoGUE_self`, `kTwoGUE_eq_ThetaTilde`, `primRhsGUE_two`, `kTwoGUE_deriv_identity`): PASS (exponent rows 1, 2, 7; instance rows `self err`, `(7.25)`, `(B)`).
- Target 5-6 (`hasDerivAt_kTwoGUE`, `hasDerivAt_kTwoGUELoop`): PASS (rows 1-3; `d/dt (7.33)` check).
- Targets 7-8 (`lemT_mul_kTwoGUE_pm/pp`): PASS (row 8; `(C)`).
- Targets 9-10 (`…_eq_profPMTilde/_profPPTilde`): PASS (row 9; `(C)` at `sz0 n = 0`; the three right-side formulas coincide with the definitions `profPMTilde`/`profPPTilde`, `Universality/ZeroModeProfile.lean:88, :93`).
- Target 11 (`gueK_exists`): PASS (rows 5, 6, 10; every length-`n+1` slice is finite and globally Lipschitz, so the Picard chain closes). Observation (no defect): the ticket's target list puts `hL` before `g` and the check pin `T2301_gueK_exists` puts `g E t1 t0 n0` before `3 ≤ L`; the `example`-adapter lambda reorders, no mathematical effect.
- Overall: PASS. Every hypothesis of every target holds at the instance above; no hypothesis on `g` or `3 ≤ d` is needed.

## (b) Script output — Tue Oct  6 14:11:09 UTC 2026

File `RBM3D/Universality/GUEPhase/KPrim.lean` (930 lines), branch `t/T2301`, commit `c3204a2` (only this file: `git diff --stat main...t/T2301`: `1 file changed, 930 insertions(+)`).

```
$ cd ../RBM3D-wt/T2301 && lake build RBM3D.Universality.GUEPhase.KPrim 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3745 jobs).
$ lake env lean RBM3D/Universality/GUEPhase/KPrim.lean ; echo "exit $?"   (no output)
lake env lean exit 0
$ lake build 2>&1 | tail -3     (worktree; the root `RBM3D.lean` does not yet import KPrim, so this is the unchanged library)
non-vacuity certificates: 0 of 147 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4106 jobs).
exit 0
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/Universality/GUEPhase/KPrim.lean ; echo "grep exit $?"
grep exit 1
```

Registry pre-check (temporary uncommitted file `import RBM3D` + `import RBM3D.Universality.GUEPhase.KPrim` + `#assert_rbm_axioms`, in the scratchpad; no registry line is needed, none edited):
```
$ lake env lean scratchpad/T2301/registry.lean > registry.out 2>&1 ; echo "exit $?"
exit 0
$ head -2 registry.out ; grep -c "KPrim\|gueK\|kTwoGUE\|gueShift\|GUEPhase.lemT" registry.out
axiom audit: 8637 theorems, 2826 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
0
```

`#print axioms` of every public declaration (scratch `axioms.lean`, `import RBM3D.Universality.GUEPhase.KPrim`):
```
'RBM.Univ.GUEPhase.gueShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUELoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE_eq_ThetaTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.primRhsGUE_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.kTwoGUE_deriv_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.hasDerivAt_kTwoGUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.hasDerivAt_kTwoGUELoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pm_eq_profPMTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.lemT_mul_kTwoGUE_pp_eq_profPPTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.GUEPhase.gueK_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Target statements, extracted from the file by script (`stmts.py`: text from `theorem`/`def` to the depth-0 `:=`, whitespace collapsed; `Ln` = line in the file):
```
L61: def gueShift (d L : ℕ) (μ : ℂ) (t1 t : ℝ) : ℂ
L68: def kTwoGUE (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) : ℂ
L75: def kTwoGUELoop (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ) (I : LoopIdx (Zd d L)) : ℂ
L83: theorem kTwoGUE_self (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ) (m : Bool → ℂ) (t1 : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    kTwoGUE d L W g m t1 t1 σ₁ σ₂ a b = kTwo d L W g m t1 σ₁ σ₂ a b
L91: theorem kTwoGUE_eq_ThetaTilde (d L : ℕ) [NeZero L] (W : ℕ) (hL : 3 ≤ L) (g : ℝ) (m : Bool → ℂ) {ζ t0 : ℝ} (σ₁ σ₂
    : Bool) (hT : ‖(t0 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (a b : Zd d L) : kTwoGUE d L W g m ((1 -
    ζ) * t0) t0 σ₁ σ₂ a b = ((W : ℂ) ^ d)⁻¹ * (m σ₁ * m σ₂) * ThetaTilde d L g ζ ((t0 : ℂ) * (m σ₁ * m σ₂)) a b
L110: theorem primRhsGUE_two (d L W : ℕ) [NeZero L] (K : LoopIdx (Zd d L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    primRhsGUE d L W K ⟨[σ₁, σ₂], [a₁, a₂]⟩ = (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L, K ⟨[σ₁, σ₂], [a₁, a]⟩ * SBgue
    d L a b * K ⟨[σ₁, σ₂], [b, a₂]⟩
L131: theorem kTwoGUE_deriv_identity (d : ℕ) (W μ p q s L : ℂ) (h : q + s * μ = p) (hp : p ≠ 0) (hq : q ≠ 0) (hL : L ≠
    0) : (W ^ d)⁻¹ * μ * ((μ * (L ^ d * p * q) - s * μ * (L ^ d * p * -μ)) / (L ^ d * p * q) ^ 2) = (W ^ d)⁻¹ * μ ^ 2
    * (L ^ d)⁻¹ * ((p⁻¹ + L ^ d * (s * μ / (L ^ d * p * q))) * (p⁻¹ + L ^ d * (s * μ / (L ^ d * p * q))))
L150: theorem hasDerivAt_kTwoGUE (d L W : ℕ) [NeZero L] (hL : 3 ≤ L) [NeZero W] (g : ℝ) (m : Bool → ℂ) {t1 t : ℝ} (σ₁
    σ₂ : Bool) (h1 : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h2 : (t : ℂ) * (m σ₁ * m σ₂) ≠ 1) (a₁ a₂ : Zd d L) : HasDerivAt
    (fun s => kTwoGUE d L W g m t1 s σ₁ σ₂ a₁ a₂) ((W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L, kTwoGUE d L W g m t1 t σ₁
    σ₂ a₁ a * SBgue d L a b * kTwoGUE d L W g m t1 t σ₁ σ₂ b a₂) t
L209: theorem hasDerivAt_kTwoGUELoop (d L W : ℕ) [NeZero L] [NeZero W] (hL : 3 ≤ L) (g : ℝ) (m : Bool → ℂ) {t1 t : ℝ}
    (σ₁ σ₂ : Bool) (h1 : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h2 : (t : ℂ) * (m σ₁ * m σ₂) ≠ 1) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => kTwoGUELoop d L W g m t1 s ⟨[σ₁, σ₂], [a₁, a₂]⟩) (primRhsGUE d L W (kTwoGUELoop d L W g m t1
    t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t
L234: theorem lemT_mul_kTwoGUE_pm (d L W : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {z : ℂ} (hz : 0 < z.im) {ζ : ℝ} (hζ0 : 0
    ≤ ζ) (hζ1 : ζ ≤ 1) (a b : Zd d L) : (lemT z : ℂ) * kTwoGUE d L W g (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z)
    true false a b = ((W : ℂ) ^ d)⁻¹ * ((‖msc z‖ ^ 2 : ℝ) : ℂ) * ThetaTilde d L g ζ ((‖msc z‖ ^ 2 : ℝ) : ℂ) a b
L251: theorem lemT_mul_kTwoGUE_pp (d L W : ℕ) [NeZero L] (hL : 3 ≤ L) (g : ℝ) {z : ℂ} (hz : 0 < z.im) {ζ : ℝ} (hζ0 : 0
    ≤ ζ) (hζ1 : ζ ≤ 1) (a b : Zd d L) : (lemT z : ℂ) * kTwoGUE d L W g (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z)
    true true a b = ((W : ℂ) ^ d)⁻¹ * msc z ^ 2 * ThetaTilde d L g ζ (msc z ^ 2) a b
L275: theorem lemT_mul_kTwoGUE_pm_eq_profPMTilde {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) {z : ℂ} (hz : 0 < z.im) {ζ :
    ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (a b : Zd d (sz.L n)) : (lemT z : ℂ) * kTwoGUE d (sz.L n) (sz.W n) (sz.lam n)
    (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true false a b = profPMTilde sz n ζ z a b
L285: theorem lemT_mul_kTwoGUE_pp_eq_profPPTilde {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) {z : ℂ} (hz : 0 < z.im) {ζ :
    ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (a b : Zd d (sz.L n)) : (lemT z : ℂ) * kTwoGUE d (sz.L n) (sz.W n) (sz.lam n)
    (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true true a b = profPPTilde sz n ζ z a b
L749: theorem gueK_exists (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (hL : 3 ≤ L) (g : ℝ) {E : ℝ} (hE : |E| < 2) {t1 t0 :
    ℝ} (ht1 : 0 ≤ t1) (ht10 : t1 ≤ t0) (ht0 : t0 < 1) (n0 : ℕ) : ∃ Kt : ℝ → LoopIdx (Zd d L) → ℂ, (∀ I, Kt t1 I =
    KLgen d L g W (mSigma E) t1 I) ∧ (∀ t ∈ Set.Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length → I.length ≤ n0
    → HasDerivWithinAt (fun s => Kt s I) (primRhsGUE d L W (Kt t) I) (Set.Icc t1 t0) t) ∧ (∀ t ∈ Set.Icc t1 t0, ∀ σ₁
    σ₂ : Bool, ∀ a b : Zd d L, Kt t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE d L W g (mSigma E) t1 t σ₁ σ₂ a b)
```

Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.KPrimCheck`, `d = 3`, `L = 3`, `W = 2`, `g = 1`, `E = 0`, `[t₁, t₀] = [7/20, 7/10]`, `ζ = 1/2`; 13 `example`s, built by the command above; the proof term of each, extracted by script `inst.py`; the data of each statement is in the file, lines 786-928):
```
L802: PROOF  fun σ₁ σ₂ a b => kTwoGUE_self 3 3 2 1 (mSigma 0) (7 / 20) σ₁ σ₂ a b
L810: PROOF  fun σ₁ σ₂ a b => kTwoGUE_eq_ThetaTilde 3 3 2 (by norm_num) 1 (mSigma 0) σ₁ σ₂ (KPrim_norm_lt0 (by norm_num) (by norm_num) σ₁ σ₂) (by norm_num) (by...
L818: PROOF  fun σ₁ σ₂ a b => kTwoGUE_eq_ThetaTilde 3 3 2 (by norm_num) (1 / 2) (mSigma 0) σ₁ σ₂ (KPrim_norm_lt0 (by norm_num) (by norm_num) σ₁ σ₂) (by norm_nu...
L828: PROOF  fun σ₁ σ₂ a₁ a₂ => hasDerivAt_kTwoGUELoop 3 3 2 (by norm_num) 1 (mSigma 0) σ₁ σ₂ (KPrim_norm_lt0 (by norm_num) (by norm_num) σ₁ σ₂) (KPrim_ne_one_...
L838: PROOF  gueK_exists 3 3 2 (by norm_num) 1 (E := 0) (by norm_num) (t1 := 7 / 20) (t0 := 7 / 10) (by norm_num) (by norm_num) (by norm_num) 3
L850: PROOF  by obtain ⟨Kt, -, h2, -⟩ := gueK_exists 3 3 2 (by norm_num) 1 (E := 0) (by norm_num) (t1 := 7 / 20) (t0 := 7 / 10) (by norm_num) (by norm_num) (by...
L860: PROOF  primRhsGUE_two 3 3 2 _ true false 0 ![1, 0, 0]
L869: PROOF  kTwoGUE_deriv_identity 3 2 1 (13 / 20) (1 / 2) (3 / 20) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
L879: PROOF  hasDerivAt_kTwoGUE 3 3 2 (by norm_num) 1 (mSigma 0) true true (KPrim_norm_lt0 (by norm_num) (by norm_num) true true) (KPrim_ne_one_of_norm_lt (KPr...
L891: PROOF  fun a b => lemT_mul_kTwoGUE_pm 3 3 2 (by norm_num) 1 (z := Complex.I) (by simp) (ζ := 1 / 2) (by norm_num) (by norm_num) a b
L901: PROOF  fun a b => lemT_mul_kTwoGUE_pp 3 3 2 (by norm_num) 1 (z := Complex.I) (by simp) (ζ := 1 / 2) (by norm_num) (by norm_num) a b
L910: PROOF  fun a b => lemT_mul_kTwoGUE_pm_eq_profPMTilde RBM.Gauss.SizesInst.sz0 0 (z := Complex.I) (by simp) (ζ := 1 / 2) (by norm_num) (by norm_num) a b
L920: PROOF  fun a b => lemT_mul_kTwoGUE_pp_eq_profPPTilde RBM.Gauss.SizesInst.sz0 0 (z := Complex.I) (by simp) (ζ := 1 / 2) (by norm_num) (by norm_num) a b
```
Reading guide: L802 `kTwoGUE_self` (all sign pairs, all `27 × 27` entries); L810 `kTwoGUE_eq_ThetaTilde` (`t₀ = 7/10`, `t₁ = (1-1/2)·7/10`); L818 same at `g = 1/2`; L828 `hasDerivAt_kTwoGUELoop` at `t = 1/2`; L838 `gueK_exists` at `n₀ = 3`; L850 its consequence at the length-3 loop `⟨[true, false, true], [0, ![1,0,0], ![2,0,0]]⟩`; L860 `primRhsGUE_two` at signs `(+,-)`, entries `(0, ![1,0,0])`; L869 `kTwoGUE_deriv_identity` at `d = 3`, `W = 2`, `μ = 1`, `p = 13/20`, `q = 1/2`, `s = 3/20`, `L = 3`; L879 `hasDerivAt_kTwoGUE` at `t = 1/2`, signs `(+,+)`; L891/L901 `lemT_mul_kTwoGUE_pm/pp` at `z = Complex.I`, `ζ = 1/2`; L910/L920 targets 9-10 at `SizesInst.sz0` (`L 0 = 4`, `W 0 = 32`, `lam 0 = 1/64`), `n = 0`, `z = Complex.I`. Every deterministic hypothesis is discharged (`by norm_num`, `by simp`, `rfl`, `by decide`, merged `norm_mul_mSigma_lt_one`); no `N = 0`, empty index set, collapsed window or `False` premise.

Pins of the check file (§2 of `docs/tickets/checks/T2301-check.lean`, lines 90-197 copied verbatim into `scratchpad/T2301/pins.lean` after `import RBM3D.Universality.GUEPhase.KPrim`), one `example : T2301Check.<pin> := fun … => <target> …` per pin (11 pins) and the three vocabulary `rfl` examples (`gueShift`, `kTwoGUE`, `kTwoGUELoop` = `…V`, the last by `cases I`):
```
$ lake env lean scratchpad/T2301/pins.lean > pins.out 2>&1 ; echo "exit $?" ; wc -c pins.out
exit 0
0 pins.out
$ grep -c "^example" scratchpad/T2301/pins.lean
14
```

Comparison with RBM2D `c9a24cf:RBM2D/Universality/GUEPhase/KPrim.lean` `:1-797` (script `cmp.py`: declaration statements up to the depth-0 `:=`, source text mapped by the ticket's import map, `L² ↦ L^d` on lattice tokens only, then compared as token strings):
```
$ python3 cmp.py
source decls (:1-797): 30  port decls: 28
not ported (merged twins): ['KPrim_abs_lemE_lt_two', 'KPrim_lemT_lt_one', 'KPrim_lemT_pos', 'KPrim_norm_mSig']
new decls: ['lemT_mul_kTwoGUE_pm_eq_profPMTilde', 'lemT_mul_kTwoGUE_pp_eq_profPPTilde']
source decls missing in port: []
statements identical after the map: 9
   KPrim_mSig_true_mul_false KPrim_ode_step KPrim_ode_glue KPrim_ode_global KPrim_two_le_length_cutGlueL KPrim_two_le_length_cutGlueR KPrim_length_cutGlueL_le KPrim_length_cutGlueR_le KPrim_norm_lt
statements with binder/argument changes (token diff after the map): 17
  gueShift: (L => (d L
  kTwoGUE: (L => (d L; - => (g : ℝ)
  kTwoGUELoop: (L => (d L; - => (g : ℝ)
  kTwoGUE_self: (L => (d L; - => (g : ℝ)
  kTwoGUE_eq_ThetaTilde: (L => (d L; - => (g : ℝ)
  primRhsGUE_two: (L => (d L
  kTwoGUE_deriv_identity: - => (d : ℕ); d => s; d => s; d => s; (d => (s; (d => (s
  hasDerivAt_kTwoGUE: (L => (d L; - => (g : ℝ)
  hasDerivAt_kTwoGUELoop: (L => (d L W; (W : ℕ) => -; - => (g : ℝ)
  lemT_mul_kTwoGUE_pm: (L => (d L; - => (g : ℝ)
  lemT_mul_kTwoGUE_pp: (L => (d L; - => (g : ℝ)
  KPrim_Kgen_two: (L => (d L; - => (g : ℝ)
  KPrim_primRhsGUE_congr: (L => (d L
  KPrim_primRhsGUE_len_one: (L => (d L
  KPrim_eq_two: {L => {d L
  KPrim_exists_upto: (L => (d L; - => (g : ℝ)
  gueK_exists: (L => (d L; - => (g : ℝ)
```
The four source declarations not ported are the merged twins; the new declarations are targets 9-10 (ticket). The private helper `KPrim_norm_lt0` (instances only, at `E = 0` via the merged `norm_mul_mSigma_lt_one`) and `KPrimCheck.KPrim_ne_one_of_norm_lt` are new and private.
```
$ diff -q <source :308-457> <port 295-444> && echo identical        (section KPrimODE, generic in a complete normed space V)
ODE section: byte-identical to source :308-457
```

Port citation and name clash:
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUEPhase/KPrim.lean
 RBM2D/Universality/GUEPhase/KPrim.lean | 139 +++------------------------------
 1 file changed, 10 insertions(+), 129 deletions(-)
$ for n in <14 public names> KPrimCheck T2301Check; do grep -rnw --include='*.lean' "$n" RBM3D/ | grep -v GUEPhase/KPrim.lean | wc -l; done   (worktree HEAD = main = 8a0c4cd)
gueShift:0 kTwoGUE:0 kTwoGUELoop:0 kTwoGUE_self:0 kTwoGUE_eq_ThetaTilde:0 primRhsGUE_two:0 kTwoGUE_deriv_identity:0 hasDerivAt_kTwoGUE:0 hasDerivAt_kTwoGUELoop:0 lemT_mul_kTwoGUE_pm:0 lemT_mul_kTwoGUE_pp:0 lemT_mul_kTwoGUE_pm_eq_profPMTilde:0 lemT_mul_kTwoGUE_pp_eq_profPPTilde:0 gueK_exists:0 KPrimCheck:0 T2301Check:0 
```
Source: RBM2D `RBM2D/Universality/GUEPhase/KPrim.lean` at `c9a24cf`, `:1-797` (instances `:799-907` rewritten at `d = 3`), read with `git show`; the compared and ported pieces are listed above.

Narrative (statements only):
- Ported in the structure of the source: `TwoLoop` (`:61-218`), `LemT` (`:222-306`), `KPrimODE` (byte-identical), `KPrimLoops`, `gueK_exists`. Edits: `Z2 L ↦ Zd d L`; every lattice-size `^ 2` (`W`, `L`, `(L:ℝ)`, `(W:ℝ)`) is `^ d`; `Theta ↦ Theta d L g`, `ThetaTilde ↦ ThetaTilde d L g`; row sums by `sum_Theta_row_of_three_le`, `Theta_transpose_of_three_le`; `card (Zd d L) = L^d` by `card_Zd`; `kTwo d L W g`, `KLgen d L g W` (note the argument orders `d L W g` and `d L g W`).
- The scalar `d = t - t₁` of `kTwoGUE_deriv_identity` is `s` and `d : ℕ` is a new explicit first argument; the local `let g` of `KPrim_exists_upto` is `gv` (the coupling `g` is a parameter).
- The three private `lemT` helpers and `KPrim_norm_mSig` are replaced by the merged `lemT_pos`, `lemT_lt_one`, `abs_lemE_lt_two`, `norm_mSigma`; `KPrim_mSig_true_mul_false` stays private (uses `norm_mE`); `msc_eq_sqrt_mul_mE hz`.
- Binder order of theorems with `hL`: `d L W hL g …` (as the ticket's consumer line `gueK_exists d L W hL g`); definitions and `kTwoGUE_self`: `d L W g` (as the merged `kTwo`). `ζ t0` of `kTwoGUE_eq_ThetaTilde` and `t1 t` of the `hasDerivAt_*` stay implicit as in the source; the pins' `∀` orders differ in these two places and the instances above absorb them by the adapter lambdas of `pins.lean` (the preflight's observation on `gueK_exists`).
- Targets 9-10 are `rw [lemT_mul_kTwoGUE_pm/pp …, profPMTilde/profPPTilde, div_eq_mul_inv]; ring` at `g = sz.lam n`, `hL = sz.three_le_L n`.
- No statement uses `3 ≤ d`, a size or sign condition on `g`, or a hypothesis not in the source; nothing owed is assumed or proved; no registry line.
- Whole file builds without warnings (`lake env lean` prints nothing).

## (c) Verified Mathlib names (`#check` in `scratchpad/T2301/chk2.lean` succeeded for each; file:line by `grep`)
- `IsPicardLindelof` (`Mathlib/Analysis/ODE/PicardLindelof.lean:79`); `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` (`Analysis/ODE/ExistUnique.lean:70`).
- `HasDerivWithinAt.union` (`Analysis/Calculus/Deriv/Basic.lean:405`); `HasFDerivWithinAt.of_notMem_closure` (`Analysis/Calculus/FDeriv/Basic.lean:376`); `hasDerivWithinAt_pi` (`Analysis/Calculus/Deriv/Prod.lean:81`); `HasDerivAt.comp_ofReal` (`Analysis/Complex/RealDeriv.lean:97`).
- `Set.Icc_union_Icc_eq_Icc` (`Order/Interval/Set/LinearOrder.lean:423`); `Complex.mul_conj` (`Basic/Complex/Basic.lean:585`: `z * conj z = ↑(normSq z)`); `Complex.normSq_eq_norm_sq`.
- `LipschitzWith.of_dist_le_mul`, `IsCompact.exists_bound_of_continuousOn`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `norm_sum_le_of_le`, `continuousOn_finsetSum`, `Finset.sum_pair`, `div_add_div`, `div_eq_div_iff`: `#check` succeeds.
- Merged RBM3D names (`#check` in `chk.lean`): `RBM.card_Zd`, `RBM.norm_mSigma`, `RBM.norm_mE`, `RBM.lemT_pos`, `RBM.lemT_lt_one`, `RBM.abs_lemE_lt_two`, `RBM.msc_eq_sqrt_mul_mE`, `RBM.norm_mul_mSigma_lt_one`, `RBM.Univ.ThetaTilde_eq` (explicit `d L lam`), `RBM.sum_Theta_row_of_three_le`, `RBM.Theta_transpose_of_three_le` (`{d L g}` implicit: the file passes `(d := d) (g := g)`), `LoopIdx.wf_cutGlueL`/`R` (explicit `x b`), `LoopIdx.length_cutGlueL_add_length_cutGlueR`, `RBM.Univ.GUEPhase.finite_loopIdx d L n`, `SBgue_apply`.
- Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- Section (a) is unchanged (no `(a′)` needed): verdict PASS stands.
- `T2301a` (Lean structure, not a paper delta): the GUE-phase 2-loop primitive carries the band coupling `g` through `Θ(g)`, `Θ̃(g)` (RBM2D had none); every statement holds for all real `g`; consumers pass `g = sz.lam n` (targets 9-10 fix this at `sz.lam n`).
- `T2301b` (bookkeeping): `W⁻² ↦ W^{-d}`, `L² ↦ L^d` (`β(t)`, `S_GUE = L^{-d}`), no other `d`-dependence; no `3 ≤ d`.
- `T2301c` (Lean structure): class T per T2173 — band form here, BA form in BA-C3 `BA/GUEKPrim`; the ODE section `KPrim_ode_*` is generic in `V` and may be copied there; the bridge to `UNOUProfile.band` (targets 9-10, new) is not a paper statement.
- Consumer shapes (UN-31/47/48/49/51): `gueK_exists d L W hL g hE ht1 ht10 ht0 n0` with initial value `KLgen d L g W (mSigma E) t1 I` (`KLK d L g W E t1 I` unfolds to it by `rfl`); `gueShift d L μ t1 t` unfolds with `L^d`.
- The name-clash grep ran at worktree HEAD `8a0c4cd` (= main at start of stage 1b), not at `f9e070b` as in the ticket text. Root import: added by the hub at merge.
