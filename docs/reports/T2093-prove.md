Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 00:40:31 UTC 2026

Target: `STK2decay d` (`Induction/Step2Defs.lean:568`): for `3 ≤ d`, `κ,𝔡 > 0` there is `C > 0` with
`‖𝒦^{(2)}_{u,σ,a}‖ ≤ C · STprof(u,D,ℓ=L)(a₀,a₁)` for all `n`, `0 < λ ≤ 𝔡⁻¹`, `|E| ≤ 2-κ`, `0 ≤ u < 1`, `D ≥ 0`.
`STprof = W^{-d} · tailW(ℓ=L, D, r = |a₀-a₁|_∞)`, `tailW = max(𝒯_u(min(r,L)), W^{-D})`,
`𝒯_u(r) = B_{u,r} e^{-√(r/ℓ_u)}`, `ℓ_u = ellT L λ u`, `B_{u,r} = BparamR` (`Defs/Tail.lean`, `Defs/Params.lean:32,36`).

Derivation on paper (each step names the merged fact it uses):
1. `KLK_two` (`Loop/KLTree.lean:211`): `𝒦^{(2)} = W^{-d} m_{σ₀} m_{σ₁} Θ_{u m_{σ₀} m_{σ₁}}(a₀,a₁)`, and `‖m(σ)‖ = 1` for `|E| ≤ 2`
   (`|mE E|² = (E² + 4 - E²)/4 = 1`). So `‖𝒦^{(2)}‖ = W^{-d} ‖Θ(a₀,a₁)‖`; `mSigma E σ` has the shape of `PropSpin (mE E) σ`.
2. Translation invariance (`Theta_apply_add_right_of_three_le`, `Propagator/Props4.lean:100`, `‖ξ‖ = u < 1`, `L ≥ 3`):
   `Θ(a₀,a₁) = Θ(0, a₁-a₀)`. Put `ρ = |a₁-a₀|_1` (`zdistD`), `r = |a₁-a₀|_∞ = |a₀-a₁|_∞` (`zdist_neg`, coordinatewise).
3. `Prop5Decay d Λ` is **proved** (`prop5Decay_holds`, `Propagator/Prop5Hold.lean:784`; it left `borrowedProps`, `Test/Axioms.lean:76`),
   so `STK2decay` needs no hypothesis. With `Λ = 𝔡⁻¹`: `∃ C₅, c > 0` (depending on `d, 𝔡` only) with
   `‖Θ(0,a)‖ ≤ C₅ B_{u,ρ} e^{-cρ/ℓ_u}` for all `L ≥ 3`, `0 < λ ≤ Λ`, `0 ≤ u < 1`, `‖m‖ = 1`, all sign pairs. No bulk condition, no `L^d ≤ W^K`.
4. `r ≤ ρ` (`zdistInf_le_zdistD`, `Defs/Sizes.lean:117`). `B` is nonneg and antitone in `r ≥ 0` (`BparamR_nonneg`, `BparamR_antitone`,
   `Defs/Tail.lean:63,71`; `BparamR_natCast:57` for the cast), so `B_{u,ρ} ≤ B_{u,r}`; `ℓ_u ≥ 1` (`one_le_ellT`) so `ℓ_u > 0`.
5. With `x = r/ℓ_u ≥ 0`: `cρ/ℓ_u ≥ c x`, and `√x ≤ c x + 1/(4c)` (from `(√x - 1/(2c))² ≥ 0`), so `e^{-c x} ≤ e^{1/(4c)} e^{-√x}`.
   Hence `‖Θ(0,a)‖ ≤ C₅ e^{1/(4c)} · B_{u,r} e^{-√(r/ℓ_u)} = C 𝒯_u(r)`, `C := C₅ e^{1/(4c)}`.
6. `r = zdistInf ≤ L` (`zdist L x = min(val, L-val) ≤ L`), so `min(r,L) = r`; `tailW ≥ 𝒯_u(r)` by `le_max_left`. The floor `W^{-D}` only helps,
   so the bound is uniform in `D ≥ 0`. The `ℓ¹` versus `L^∞` comparison costs nothing here: `r ≤ ρ` is the direction used; the factor `d` of
   `zdistD ≤ d·zdistInf` is not needed (the pin docstring's "`c_d` in the exponent" is not used).
Verdict on the pin: true as written, no counterexample (see (ii): `λ > L`, `u` near `1`, `D` large all bounded; the large ratios are `C`'s dependence on `𝔡`).

### (i) Exponent table

| item | value | constraint | slack / note |
|---|---|---|---|
| decay constants of `Prop5Decay` | `C₅, c` from `prop5Decay_holds d 𝔡⁻¹` | depend on `(d, 𝔡)` only, fixed before `L, W, λ, u, D, E` | pin order `∀ κ 𝔡, ∃ C, ∀ sz n …` matches; `κ` unused beyond `\|E\| ≤ 2` |
| `C` of the pin | `C₅ · e^{1/(4c)}` | independent of `n, L, W, λ, u, D, E, σ, a` | sharp: `sup_x e^{√x - c x} = e^{1/(4c)}` (script: equality at `c = 0.05, 0.1, 1`) |
| `‖m(σ)‖` | `1` | `\|E\| ≤ 2 - κ < 2` | exact for all `\|E\| ≤ 2`; script prints `\|mE\|²` = 1.0 at `E = 0, 1.5, 1.99` |
| spectral radius `‖ξ‖ = u·‖m₀m₁‖` | `u` | `< 1` for `Prop5Decay`, `Theta_apply_add_right` | slack `1 - u > 0`; no `u`-uniformity of `C` needed beyond `Prop5Decay` |
| `g = λ` | `0 < λ ≤ 𝔡⁻¹ = Λ` | `Prop5Decay` range `0 < g ≤ Λ` | equality allowed |
| `L` | `3 ≤ L` (`Sizes.three_le_L`) | `Prop5Decay`, translation invariance | no `L^d ≤ W^K` used (§29 (3)); `λ > L` allowed since `ℓ_u = min(max(·,1),L)` is the same on both sides |
| `r` versus `L` | `r = \|a₀-a₁\|_∞ ≤ L` | `min(r,L) = r` in `tailW` (`ℓ = L`) | `zdistInf ≤ L/2` in fact; only `≤ L` needed |
| `ρ` versus `r` | `r ≤ ρ ≤ d r` | `B` antitone, `c ρ/ℓ ≥ c r/ℓ` | only `r ≤ ρ` used; script: `r ≤ ρ ≤ 3r` on all `Z_8^3` |
| `D` | `D ≥ 0` | none | floor `W^{-D}` only enlarges `tailW`; `D` does not enter `C` |
| quantifier `∀ n` (not `∀ᶠ n`) | pointwise in `n` | §29 (4) | proof uses only `L n ≥ 3`, `0 < lam n ≤ 𝔡⁻¹`; no eventual statement needed |
| time domain `0 ≤ u < 1` | as pinned | §29 (1) | no `u ≤ lemT`, no `1 - λ²/L²` boundary (§29 (2)) is used; `(ii)` case boundary never appears |
| constants vs `W, L, λ` | `C` implicit in none | §29 last line | explicit: `C = C₅ e^{1/(4c)}`, `C₅, c` from `(d, 𝔡)` |

DECISIONS §29 items: (1) `0 ≤ u < 1` is a hypothesis of the pin and of `Prop5Decay`: holds. (2) the boundary `1 - λ²/L²` does not occur
(no case split; `λ > L` is covered by `ℓ_u = L`): holds. (3) `L^d ≤ W^K` not used: holds. (4) `∀ n` is harmless: the argument is pointwise
in `n` using only `Sizes` fields: holds. A `λ`-lower bound `W^{-d/2+𝔡} ≤ λ` is not needed either.

### (ii) Concrete nondegenerate instance

`d = 3`, `κ = 1/2`, `𝔡 = 1/20`, `Sizes` with `L = 8`, `W = 4` (`N = 32³ = 32768`), `λ ∈ {1/8, 1, 4, 20}` (`≤ 𝔡⁻¹ = 20`; `λ = 20 > L = 8` is the
`λ > L` case), `E ∈ {0, 3/2}` (`|E| ≤ 3/2 = 2-κ`), `u ∈ {0, 1/2, 0.99}`, `D ∈ {0, 5}`, all four `σ`, all `a ∈ Z_8^3` (512 points).
Quantity: `|𝒦^{(2)}|/(W^{-d} tailW) = |Θ(0,a₁-a₀)|/tailW(ℓ=L, D, |a₁-a₀|_∞)`, with `Θ = (1 - ξ S^{(B)})⁻¹`, `ξ = u m m'`, `S^{(B)}` the
`sbKernel` (`Defs/Block.lean:36`: centre `1/(1+2dg²)`, 6 neighbours `g²/(1+2dg²)`), computed by FFT (first line: cross-check against dense 512x512 inverse).
Both sides are nonzero (`W^{-d-D} > 0`, `tailW ≥ W^{-D}`), no empty index, no collapsed window.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2093/ratio.py`
```
direct-vs-FFT max diff 3.342213888644167e-16
lam   u     D  max over E in {0,1.5}, 4 sign pairs, all a of |Theta|/tailW  (= |K2|/(W^-d tailW))   [r_inf at argmax]
 0.125  0.00  0     1.0000  [0]
 0.125  0.00  5     1.0136  [0]
 0.125  0.50  0     0.9489  [0]
 0.125  0.50  5     0.9489  [0]
 0.125  0.99  0     0.3336  [1]
 0.125  0.99  5     0.3336  [1]
 1.000  0.00  0     1.0000  [0]
 1.000  0.00  5     1.9922  [0]
 1.000  0.50  0     1.1190  [0]
 1.000  0.50  5     1.6688  [0]
 1.000  0.99  0     1.4667  [0]
 1.000  0.99  5     1.4667  [0]
 4.000  0.00  0     1.0000  [0]
 4.000  0.00  5    16.4537  [0]
 4.000  0.50  0     1.0516  [0]
 4.000  0.50  5    16.3013  [0]
 4.000  0.99  0     1.5369  [0]
 4.000  0.99  5     5.9621  [0]
20.000  0.00  0     1.0000  [0]
20.000  0.00  5   224.8762  [0]
20.000  0.50  0     1.0470  [0]
20.000  0.50  5   163.5065  [0]
20.000  0.99  0     1.5239  [0]
20.000  0.99  5     7.7039  [0]
worst ratio 224.8762322015334
r_inf<=r_1<=d*r_inf: True max r_inf 4 <= L: True
c 0.05 sup_x exp(sqrt x - c x) = 148.4131591025766 vs exp(1/(4c)) = 148.4131591025766
c 0.1 sup_x exp(sqrt x - c x) = 12.182493960703473 vs exp(1/(4c)) = 12.182493960703473
c 1.0 sup_x exp(sqrt x - c x) = 1.2840254166877414 vs exp(1/(4c)) = 1.2840254166877414
|mE|^2 at E 0 1.0
|mE|^2 at E 1.5 1.0
|mE|^2 at E 1.99 1.0
```
Reading: the ratio is bounded at every point, with no blow-up at `u = 0.99` or `λ > L`. The largest ratios sit at `u` away from 1, `a = 0`, `D = 5`,
where `Θ(0,0) ≈ 1` (at `u = 0`, `Θ = 1`) but `tailW = 𝒯_0(0) = 1/(1+λ²) + L^{-d}`; ratio `= 1/(1/(1+λ²) + 8⁻³) = 224.876` at `λ = 20`
(exact, matches the table), `≤ 1+λ² ≤ 1+𝔡⁻²`. So the constant must depend on `𝔡` (it does: `C₅(d,𝔡)`), and any valid `C` at `𝔡 = 1/20` is `≥ 224.88`.
External hypothesis: none (`Prop5Decay` is proved: `prop5Decay_holds`, `Propagator/Prop5Hold.lean:784`); no limit computation needed.

### Verdicts

- `stK2decay_holds (d : ℕ) : STK2decay d`: **PASS**. True as written; every hypothesis is satisfiable at the instance above; the exponent chain closes
  with `C = C₅ e^{1/(4c)}`. No hypothesis on `Prop5Decay` is needed (proved). Pin is not false at `λ > L`, `u → 1`, `D` large.
- Remarks for 1b (mathematical only): the ticket calls `Prop5Decay` "borrowed", but it is proved and out of `borrowedProps`; once `stK2decay_holds`
  merges the `STK2decay` line of `owedProps` can go. Paper-delta candidate `T2093a`: the pin docstring's "costs `c_d` in the exponent" is not needed (`r ≤ ρ` suffices).

## (b) Script output — Sun Oct  4 00:48:09 UTC 2026

Branch `t/T2093`, commit `de6076c`, file `RBM3D/Induction/Step2K2.lean` (new, 220 lines). `RBM3D.lean` and `Test/Axioms.lean` are not edited (the hub adds the root import at merge). Scratch: `scratchpad/T2093/`.

### Builds, pre-check, axioms, hygiene
```
$ lake build RBM3D.Induction.Step2K2 2>&1 | tail -2
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3717 jobs).
$ lake build 2>&1 | tail -2 | cut -c1-200
non-vacuity certificates: 4 of 97 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3833 jobs).
$ lake env lean precheck.lean (import RBM3D; import RBM3D.Induction.Step2K2; #assert_rbm_axioms); echo exit=$?
exit=0
axiom audit: 2947 theorems, 1136 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
60:  RBM.Gauss.Sizes.STK2decay: 2 [no certificate]
123: RBM.Gauss.Sizes.STK2decay,
105:registry: 5 borrowed + 92 owed + 37 structural; 54 registered premise(s) carry nothing yet: [RBM.ThetaDiff
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stK2decay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean RBM3D/Induction/Step2K2.lean 2>&1 | wc -l   (warnings/errors of the file)
       0
$ grep -cE "sorry|admit|native_decide|^axiom" Step2K2.lean; wc -l Step2K2.lean
0
     220 RBM3D/Induction/Step2K2.lean
$ git diff main...t/T2093 --stat
 RBM3D/Induction/Step2K2.lean | 220 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 220 insertions(+)
```
(precheck file, not committed: `import RBM3D`, `import RBM3D.Induction.Step2K2`, `#assert_rbm_axioms`; line 123 of its output is the `carry nothing yet` list, line 60 the usage ledger.)

### Target statement (extracted by script) and the pin it must equal

```
$ grep -n "^theorem stK2decay_holds" RBM3D/Induction/Step2K2.lean
132:theorem stK2decay_holds (d : ℕ) : STK2decay d := by
```

```
$ sed -n 568,572p RBM3D/Induction/Step2Defs.lean   # the pin
def STK2decay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
      0 ≤ u → u < 1 → 0 ≤ D → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STKloop sz n E u σ a‖ ≤ C * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)
```

```
$ lake env lean chk.lean   # import RBM3D.Induction.Step2K2; #check @RBM.Gauss.Sizes.stK2decay_holds
RBM.Gauss.Sizes.stK2decay_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STK2decay d
```

The theorem has type `STK2decay d` itself: the pin is used exactly (no hypothesis added, no signature changed).

### The compiled nonempty instances (in the same file; `d = 3`, merged `sz0`)

```
$ sed -n 185,220p RBM3D/Induction/Step2K2.lean

open RBM.Gauss.SizesInst in
/-- **`stK2decay_holds`, instantiated** at `d = 3`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`),
`E = 1/2`, `u = 1/2`, `D = 5`, all four sign patterns and all `a ∈ (Z_4^3)²`. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STKloop sz0 0 (1 / 2) (1 / 2) σ a‖ ≤
        C * STprof sz0 0 (1 / 2) 5 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C, hC, hall⟩ := stK2decay_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  exact ⟨C, hC, fun σ a => hall sz0 0 (1 / 2) (1 / 2) 5 hlam hlam' (by norm_num [abs_of_pos])
    (by norm_num) (by norm_num) (by norm_num) σ a⟩

open RBM.Gauss.SizesInst in
/-- The same at `n = 1` (`L = 8`, `W = 1024`, `lam = 1/4096`), `E = 0`, `u = 99/100` (near `1`),
`D = 0`, at the concrete off-diagonal pair `a = (0, e₁)` and signs `(+, -)`. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖STKloop sz0 1 0 (99 / 100) ![true, false] ![0, Pi.single 0 1]‖ ≤
        C * STprof sz0 1 (99 / 100) 0 ((sz0.L 1 : ℕ) : ℝ) 0 (Pi.single 0 1) := by
  obtain ⟨C, hC, hall⟩ := stK2decay_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 1 := by simp [sz0]
  have hlam' : sz0.lam 1 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 1 = 1 / 4096 := by norm_num [sz0]
    rw [this]; norm_num
  refine ⟨C, hC, ?_⟩
  have := hall sz0 1 0 (99 / 100) 0 hlam hlam' (by norm_num) (by norm_num) (by norm_num)
    le_rfl ![true, false] ![0, Pi.single 0 1]
  simpa using this

end RBM.Gauss.Sizes
```

### Name-clash grep, port citation

```
$ grep -rn "stK2decay_holds\|k2d_" RBM3D <main worktree>/RBM3D | grep -v Step2K2.lean | wc -l   # public name stK2decay_holds; private helpers k2d_*
       0
```

```
$ grep -n "^private theorem\|^theorem\|^example" RBM3D/Induction/Step2K2.lean
51:private theorem k2d_KLloopOf_two {d L : ℕ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
56:private theorem k2d_zdistInf_neg {d L : ℕ} (x : Zd d L) [NeZero L] :
61:private theorem k2d_zdistInf_le {d L : ℕ} (x : Zd d L) : zdistInf d L x ≤ L :=
65:private theorem k2d_sqrt_le {c : ℝ} (hc : 0 < c) (y : ℝ) (hy : 0 ≤ y) :
78:private theorem k2d_theta_tail {d : ℕ} {C₅ c : ℝ} (hC₅ : 0 < C₅) (hc : 0 < c) {L : ℕ}
132:theorem stK2decay_holds (d : ℕ) : STK2decay d := by
189:example :
205:example :
```

```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; ... diff --stat c9a24cf HEAD -- RBM2D/Path/KellStar.lean; ... show c9a24cf:RBM2D/Path/KellStar.lean | grep -n "^def KpmBoundProp5\|^theorem kpmBoundProp5"
9e0f275
 RBM2D/Path/KellStar.lean | 77 +++++++-----------------------------------------
 1 file changed, 10 insertions(+), 67 deletions(-)
39:def KpmBoundProp5 : Prop :=
240:theorem kpmBoundProp5 : KpmBoundProp5 := by
```

RBM2D `Path/KellStar.lean:39` (`KpmBoundProp5`), `:240` (`kpmBoundProp5`) at `c9a24cf` is the model cited for the `n = 2` formula and the Theta bound; no RBM2D text is copied (its statement is `|K| <= C (1+log L) M_u^{-1}`, `d = 2`, no decay in `|a-b|`). The registry pre-check is the `precheck.lean` run above.

### Registry: removal of the owed line tested in a scratch copy (not committed)

```
$ diff Test/Axioms.lean (without the STK2decay line); precheck.lean rebuilt against it; grep -c STK2decay
136d135
<    `RBM.Gauss.Sizes.STK2decay, -- `(eq:kn2sol_decay)`, `(eq:simpleboundK)` (`3_5:457`, `518`): ST2-06 (T2066, DECISION
104:registry: 5 borrowed + 91 owed + 37 structural; 53 registered premise(s) carry nothing yet: [RBM.ThetaDiff
0
```

```
$ git status --short   # empty: Test/Axioms.lean restored, nothing uncommitted

```

## (c) Verified Mathlib and project names (Sun Oct  4 00:49:09 UTC 2026)

```
$ lake env lean names.lean   # 19 lines "#check @name", output cut to the name; no error line (each name resolves)
@Real.exp_le_exp: Real.exp_add: @Real.sq_sqrt: @div_le_div_of_nonneg_right: @min_eq_left: @Finset.sup_le: Complex.norm_natCast: 
@Theta_apply_add_right_of_three_le: prop5Decay_holds: @norm_mSigma: @norm_mul_mSigma_lt_one: @norm_mE: @BparamR_natCast: @BparamR_antitone: 
@BparamR_nonneg: Gauss.zdistInf_le_zdistD: @ellT_pos: zdist_neg: Loop.KLK_two: 
```
Mathlib: `Real.exp_le_exp`, `Real.exp_add`, `Real.sq_sqrt`, `div_le_div_of_nonneg_right`, `min_eq_left`, `Finset.sup_le`, `Complex.norm_natCast` (the first seven of the list). Project: the rest (`Gauss.zdistInf_le_zdistD` is `RBM.Gauss.zdistInf_le_zdistD`, found after the first run reported `Unknown identifier` for the bare name). Names verified absent: none searched.

## (d) Narrative, open issues, paper-delta candidates

- `stK2decay_holds (d : ℕ) : STK2decay d` is proved as pinned: no hypothesis added, no signature changed, no counterexample; `(a)` needed no correction (no `(a′)`).
- Chain (file docstring, lines 19-33): `KLK_two` and `norm_mSigma` give `‖𝒦^{(2)}‖ = W^{-d} ‖Θ(a₀,a₁)‖`; `Theta_apply_add_right_of_three_le` gives `Θ(0, a₁-a₀)`; `prop5Decay_holds d 𝔡⁻¹` gives `(C₅, c)` and the bound in `ρ = zdistD`; `zdistInf ≤ zdistD`, `BparamR` antitone and `√y ≤ c y + 1/(4c)` give `‖Θ‖ ≤ C₅ e^{1/(4c)} 𝒯_u(r)`; `r ≤ L` gives `min r L = r`; `le_max_left` gives `tailW ≥ 𝒯_u(r)`.
- The constant is `C = C₅ e^{1/(4c)}`, from `(d, 𝔡)` only; `κ` is used only to get `|E| ≤ 2`. No split on `λ > L`, `u` near `1`, or `D`; `∀ n` pointwise.
- Imports: `Step2Defs`, `Loop.KLTree`, `Propagator.Pins`, `Propagator.Prop5Hold` (for `prop5Decay_holds`), `Propagator.Props4`. The ticket's `Evolution.PropTInf` is not imported: only the direction `r ≤ ρ` is used, so no `L^∞` proposition `EKPropTInf` is needed.
- `Prop5Decay` is proved, not borrowed (`Propagator/Prop5Hold.lean:784`), so the theorem takes no hypothesis; `inst_K2decay (h : STK2decay 3)` in `Step2Defs.lean` can now be fed by `stK2decay_holds 3` (that file is not touched).
- Instances: two `example`s at `d = 3` (`sz0`, `n = 0` and `n = 1`, `u = 1/2` and `u = 99/100`, `D = 5` and `D = 0`, `E = 1/2` and `E = 0`, `κ = 𝔡 = 1/10`), every deterministic hypothesis discharged (`0 < lam`, `lam ≤ 𝔡⁻¹`, `|E| ≤ 2-κ`, `0 ≤ u < 1`, `0 ≤ D`); the second at the off-diagonal pair `(0, e₁)`, signs `(+,-)`.
- Registry: `RBM.Gauss.Sizes.STK2decay` (`Test/Axioms.lean:136`) can go once this merges (ticket: "say so"). Evidence above: a scratch copy without the line gives `precheck.lean` exit `0`, `91 owed`, no `STK2decay` in the output; the committed `Test/Axioms.lean` is unchanged (the diff of `t/T2093` is the one new file).
- Open issues: none for the target. `RBM3D.lean` is not edited here (root import is the hub's at merge); the full `lake build` above was run in this worktree without the new module in the root file, and the pre-check imports it explicitly.

Paper-delta candidates:
- `T2093a`: the pin docstring (`Step2Defs.lean:564-567`) says the `ℓ¹` versus `L^∞` distance "costs only the constant `c_d` in the exponent"; the proof uses only `zdistInf ≤ zdistD` (no `c_d`, no doubling of `𝒯`). Statement unaffected.
- `T2093b`: the same docstring and the ticket call `Prop5Decay` borrowed; it is proved (`prop5Decay_holds`, `Propagator/Prop5Hold.lean:784`). The `STK2decay` docstring is stale (the header of `Step2Defs.lean` already says so for the probe docstrings).
- `T2093c`: paper `(eq:kn2sol_decay)` (`3_5:457`) is `𝒦^{(2)}_{u,(-,+),(a₁,a₂)} ≺ W^{-d} B_{u,|a₁-a₂|}`, `(eq:simpleboundK)` (`3_5:518`) is `𝒦^{(2)}_{u,σ,a} ≺ W^{-d} 𝒯̃^L_{u,D}(|a-b|)`, both with `≺` on a deterministic quantity. The pin states the second form for all four `σ` as `≤ C ·` with an explicit `C` (no `N^ε` loss; `|·|` is `zdistInf`, paper-delta T2002b). The `B`-only form follows from `‖Θ‖ ≤ C 𝒯_u(r) ≤ C B_{u,r}` (`k2d_theta_tail`) but is not a separate Lean statement.
- `T2093d`: registry line `STK2decay` in `owedProps` removable after merge (above).
