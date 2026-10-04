Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct  4 02:34:36 UTC 2026

Mathematics of `STNewKLKAt` (`Step2Defs.lean:363`; paper `3_5:371-378`, proof `3_5:610-654`), fixed `σ`, `a = (a₀,a₁)`.
Notation: `T = tailT` (`Defs/Tail.lean:48`) at `(g, t) = (lam n, u)`, `x = 1-u`; `P(r) = tailW(ℓ)(r) = max(T(min(r,ℓ)), W^{-D})`;
`STprof = W^{-d} P(|a₀-a₁|_∞)`; `F_σ = STLKM`; `|F_σ(x,y)| ≤ Ĵ W^{-d} P(|x-y|_∞)` by definition of `Ĵ` (sup over all `σ, a`).
Steps, with the merged lemma each uses:
- S1 (kernel sums, `K`): `|Θ_ξ| ≤ Θ_{|ξ|}` entrywise (series, `S ≥ 0`), `|ξ| = u|m||m| = u` (`norm_mSigma`), `Σ_b ‖SB a b‖ = 1` (`sum_norm_SB_row`, `Block.lean:118`) so `Σ_c |K_σ(a,c)| ≤ W^{-d}/(1-u)` and `Σ_b |(SΘ_ξ)(a,b)| ≤ 1/(1-u)`. (Also available: `KLK_ward`, `KLWard.lean:1123`.)
- S2 (Ward for `L`): `H` Hermitian, `G⁻ = (G⁺)^*`: `L_{+-}(a,c) = W^{-2d}Σ_{x∈a,y∈c}|G_xy|² ≥ 0`, `L_{-+}(a,c) = W^{-2d}Σ|G_yx|²`, and `|L_{±±}(a,c)| ≤ (L_{+-}+L_{-+})(a,c)/2` (Cauchy–Schwarz). Ward (both charge orders, private `npq_loopL_ward`, `NewPQ.lean:211`, to be re-proved privately; `sum_gloop_ward_last_div`): `Σ_c L_{(s,¬s),(a,c)} = Im L¹_{+,a}/(W^d η_u)`, `η_u = (1-u) Im m(E)`. `|L¹_{+,a} - m| = |W^{-d}Σ_{x∈a}(G-M)_xx| ≤ δ₀`, so `Im L¹ ≤ Im m + δ₀`. Sums over the first index use `L_{+-}(x,a₁) = L_{-+}(a₁,x)` and `Θ` symmetric (`SB_isSymm`).
  Result: `W^d(1-u) Σ_c(|L_σ(a,c)|+|K_σ(a,c)|) ≤ (1 + δ₀/Im m) + 1 ≤ 3` for `δ₀ := c_κ`.
- S3 (shift): `T(max(r-1,0)) ≤ C_s T(r)`, `C_s = 2^{d-2} e` (`B`: `((r+1)/(r'+1))^{d-2} ≤ 2^{d-2}`, zero mode `d ≥ 3`; exp: `√(r/ℓ_t) - √(r'/ℓ_t) ≤ 1` as `ℓ_t ≥ 1`, `one_le_ellT`). With `S_xy ≠ 0 ⟹ |x-y|_∞ ≤ zdistD ≤ 1` (`sbKernel`, `zdistInf_le_zdistD`) and the triangle inequality for `zdistInf` (private `pti_zdistInf_add_le`, `PropTInf.lean:43`; re-prove).
- S4 (sharp decay of `Θ`): `|Θ_ξ(a,b)| ≤ C₁ T(|a-b|_∞)`, `C₁ = C₅ e^{1/(4c)}`, `(C₅,c)` of `prop5Decay_holds d 𝔡⁻¹`, = private `k2d_theta_tail` (`Step2K2.lean:78`, re-prove, ≈40 lines). **`stK2decay_holds` alone is not enough**: its right side is `tailW ≥ W^{-D}`, and summing the floor `W^{-D}` over `L^d` points needs `L^d ≤ W^K` (DECISIONS §29 (3)).
- S5 (`(TTT2)`, `ekPropTInf_holds`, `PropTInf.lean:534`), `u = t`: `Σ_c T(|a-c|)T(|c-b|) ≤ C_T/(1-u) · T(|a-b|)`. Its regime hypothesis `g²/L² ≤ 1-u ∨ 1-u ≤ g²/L²` is `le_total`; `0 < g` is `0 < lam n`.
- S6 (cut `K`, the paper's "WLOG `T_u(ℓ) ≥ W^{-D}`", `3_5:611`): the paper does it by choosing `K ≤ ℓ` with `T(K) = W^{-D}`. Case `T(0) < W^{-D}`: `P ≡ W^{-D}`, every pair is "far" (use S2 only). Case `T(0) ≥ W^{-D}`: `T` is continuous and nonincreasing in `r ∈ ℝ`, so (IVT) there is `K ∈ [0, min(ℓ,L)]` with `P(r) = T(min(r,K))` for `r ≤ L` (`K = min(ℓ,L)` if `T(min(ℓ,L)) ≥ W^{-D}`). Then `P(r) = T(r)` for `r ≤ K`, `P(r) ≥ T(K)` for all `r`, `P(r) ≤ T((K-1)_+) ≤ C_s T(K)` for `r ≥ (K-1)_+`, `1_{K ≥ 1} ≤ 1_{ℓ ≥ 1}`.
- Bound 1 (`STthetaOp`, `3_5:615-624`): `|Θ^{(2)}∘F| ≤ Σ_{i<2} Σ_b |(SΘ)(a_i,b)| Ĵ W^{-d} P(|b-a_{1-i}|)`. Far `b` (`|b-a_{1-i}| ≥ K`): `T(K)·Σ_b|SΘ| ≤ T(K)/(1-u)` (S1). Near `b`: `|(SΘ)(a_i,b)| ≤ Σ_x S_{a_i x} C₁ T(|x-b|) ≤ C₁C_s T(|a_i-b|)` (S3, S4), then S5: `≤ C₁C_sC_T/(1-u) · T(|a₀-a₁|)`. `T(K), T(|a₀-a₁|) ≤ P(|a₀-a₁|)`. So `‖·‖ ≤ 2(1 + C₁C_sC_T)/(1-u) · Ĵ · STprof`.
- Bound 2 (`STELKLKM = W^dΣ_{x,y}F(x,a₁)S_xy F(a₀,y)`, `3_5:626-654`): split pairs (I) `y` far (`|y-a₀| ≥ (K-1)_+`): `(Σ_x|F(x,a₁)|)·sup_y|F(a₀,y)|·(row sum 1) ≤ [3/(W^d(1-u))]·Ĵ W^{-d} C_s T(K)`; (II) `y` near, `x` far: same with column sums (`S` symmetric); (III) both near (empty if `K ≤ 1`): `|F| ≤ Ĵ W^{-d}T(·)`, `T(|a₀-y|) ≤ C_s T(|a₀-x|)` (S3), `Σ_y S_xy = 1`, S5. Total `W^d|·| ≤ [6C_s + C_sC_T·Ĵ 1_{ℓ≥1}]/(1-u) · Ĵ W^{-d}P`, i.e. `≤ C/(1-u)(Ĵ + Ĵ² 1_{ℓ≥1}) STprof`.
- Constants: `C := max(2(1+C₁C_sC_T), 6C_s + C_sC_T)` (any larger is fine), `δ₀ := c_κ = √(κ(4-κ))/2` (`≤ Im m(E)` for `|E| ≤ 2-κ`, `κ ≤ 2`; for `κ > 2` the hypothesis `|E| ≤ 2-κ` is empty). Both depend only on `(d, κ, 𝔡)`: `C₁` on `(d,𝔡)`, `C_T` on `d`, `C_s` on `d`, `c_κ` on `κ`. No `L, W, n, E, u, D, ℓ, H`. No `W`, `L`, `lam` enters a constant.

### (i) Exponent table
| item | value / form | constraint | slack |
|---|---|---|---|
| `C_s` | `2^{d-2} e` = 10.873 at `d=3` | `T(max(r-1,0)) ≤ C_s T(r)`, all `r ≥ 0`, `ℓ_t ≥ 1` | measured max 5.436 / 4.636 / 3.507 at `u = 0, .5, .9` (script 3) |
| `C_T` | `ptiConstI+ptiConstII` (d only) | `(1-u)ΣTT ≤ C_T T`, `u = t`, any `L ≥ 1`, `g > 0` | measured 149.6 / 132.7 / 61.1 at `L=24`; T2039 report: ≈ 1.1·10³ at `L=96`, saturating in `L` |
| `C₁` | `C₅ e^{1/(4c)}` (`Prop5Decay d 𝔡⁻¹`) | `|Θ_ξ(a,b)| ≤ C₁ T(|a-b|_∞)`, `‖ξ‖<1`, `lam ≤ 𝔡⁻¹` | T2039 `theta_decay.py`: max ratio 2.028 (`L ≤ 48`) |
| `δ₀` | `c_κ = √(κ(4-κ))/2` (0.968 at `κ=1.5`) | `δ₀ ≤ Im m(E)` (so Ward factor `1+δ₀/Im m ≤ 2`) | instance `‖G-M‖_max` = 0.0299 (u=.5), 0.0773 (u=.9) vs 0.968 |
| Ward sum | `W^d(1-u)Σ_c(|L|+|K|) ≤ 3` | S1+S2 | measured 2.0000 (u = 0, .5, .9) |
| `Σ_b|SΘ|` | `≤ 1/(1-u)` | `|ξ| = u < 1`, `S` stochastic | measured `(1-u)Σ = 1.0000` (equality) |
| factor `1/(1-u)` | from `Σ_c K = W^{-d}/(1-u)`, `η_u = (1-u)Im m`, TTT2 | `0 ≤ u < 1` (pin has both) | none needed |
| `ℓ ≤ L`, `1_{ℓ≥1}` | pin as stated | `ℓ > L` is harmless (`min(r,ℓ)=r` as `r ≤ L`), indicator used only through `1_{K≥1} ≤ 1_{ℓ≥1}` | pin may keep `ℓ ≤ L` |
| floor `W^{-D}` | enters only via `K` (S6) | never summed over `L^d` points | no `L^d ≤ W^K` used |
| `d ≥ 3` | pin hypothesis | zero-mode term of `B` is constant, `1 ≤ 2^{d-2}` in S3; `Prop5Decay`, `EKPropTInf` need `3 ≤ d` | exact |
| exponents `W^{-ε}`, `1/5`, `1/6` | none in this ticket | `Ĵ` is a free real, no smallness used; bounds linear in `Ĵ` (+`Ĵ²`) | n/a |
| `∀ n` vs `∀ᶠ n` | `∀ n` (§29 (4)) | no `n` large used; `L ≥ 3` from `sz.three_le_L` | n/a |

§29 checks: (1) `0 ≤ u < 1` used (`|ξ| = u ≥ 0`, `‖ξ‖<1`); no `s`/`t<1` beyond this. (2) `ℓ>L` boundary: harmless, no negative time (time is `u`, `1-u>0`). (3) `L^d ≤ W^K` is NOT used (S4/S6). (4) `∀ n`: nothing eventual. Verdict on the pin as written: true; deterministic (Ward identity + `‖G-M‖_max ≤ δ₀` only, no stochastic input), as T2039 F5 pinned.

### (ii) One concrete nondegenerate instance
`d = 3, L = 24, W = 8` (`W^{-D} = 1/64`, `D = 2`), `lam = 1` (`𝔡 = 1`), `E = 0.5` (`κ = 1.5`), `u ∈ {0, .5, .9}`, `ℓ ∈ {0, 1, 6}`.
`H = Ĥ ⊗ I_{W^d}` with `Ĥ` a Hermitian circulant on `Z_L^3` (real Fourier symbol), so `L_{σ,(a,b)} = W^{-d} Ĝ^{σ₀}(a-b) Ĝ^{σ₁}(b-a)`, `K = W^{-d} m m Θ(a-b)`, all `W^{-d}` cancel against `STprof`.
Symbol = semicircle(variance `u`) quantiles in random order (`G_u(0,0) = m(E)` since `u m² + z_u m + 1 = 0`), hence `‖G-M‖_max` small. `u = 0`: `H = 0` gives `L = K` exactly (`Ĵ = 0`, both sides 0, ratio is roundoff); the `u = 0` row uses instead `Ĥ = ε·(phased nearest-neighbour hopping)`, `ε = 0.05`.
Cut is nondegenerate: `T(0) ≥ 0.50 > W^{-D} = 0.0156`; `K = 1.0 (ℓ=1)`, `3.69 / 5.237 / 6.0 (ℓ=6; u = 0/.5/.9)`, so `K < ℓ` at `u = 0, .5`.
```
$ python3 newklk.py 0.05 | grep -E "^E=|^ +0\.00|u +l"          # u=0, eps H: ||G-M|| = 0.048 (Ward columns: sum_a L_{+-} vs Im G_aa/eta, then sum K_{-+} vs 1/(1-u))
E=0.5 lam=1 W=8 D=2 eps=0.05  L=24 d=3
    u     l |       Jhat      maxGM |     R1max     R2max   Ward/KW
 0.00   0.0 |    0.05772    0.04842 |    0.4249    0.0083   Ward: 0.98893 vs 0.98893 ; 1/(1-u)=1.0000 vs sumK=1.0000
 0.00   1.0 |    0.05772    0.04842 |    1.6746    0.0266   Ward: 0.98893 vs 0.98893 ; 1/(1-u)=1.0000 vs sumK=1.0000
 0.00   6.0 |    0.05772    0.04842 |    1.6746    0.0266   Ward: 0.98893 vs 0.98893 ; 1/(1-u)=1.0000 vs sumK=1.0000
$ python3 newklk2.py                                     # u = .5, .9: semicircle-calibrated H ('random'), plus the 'radial' ordering
order       u    l |       Jhat    ||G-M|| |     R1max     R2max
random   0.50  0.0 |     0.1785    0.02986 |    1.1304    0.1654
random   0.50  1.0 |     0.6343    0.02986 |    0.7614    0.1003
random   0.50  6.0 |     0.6343    0.02986 |    0.7614    0.1003
random   0.90  0.0 |     0.4374    0.07731 |    0.5117    0.1805
random   0.90  1.0 |       1.09    0.07731 |    0.5399    0.1002
random   0.90  6.0 |       1.09    0.07731 |    0.5618    0.1106
radial   0.50  0.0 |     0.1785     0.2649 |    0.4381    0.0305
radial   0.50  1.0 |     0.1785     0.2649 |    1.2006    0.0667
radial   0.50  6.0 |     0.1785     0.2649 |    1.2006    0.0667
radial   0.90  0.0 |     0.4374     0.3507 |    0.3406    0.0822
radial   0.90  1.0 |     0.6186     0.3507 |    0.6406    0.0984
radial   0.90  6.0 |     0.6186     0.3507 |    0.6430    0.1061
$ python3 exps.py                                        # script 3: constants of the table
Im m(E)=0.9682  c_kappa(kappa=1.5)=0.9682  4e=10.873
    u |       Cs       CT      Sth       Wd |     T(0)     W^-D
 0.00 |    5.436   149.61   1.0000   2.0000 |   0.5001   0.0156
 0.50 |    4.636   132.69   1.0000   2.0000 |   0.6668   0.0156
 0.90 |    3.507    61.14   1.0000   2.0000 |   0.9098   0.0156
cut K=sup{r<=min(l,L): T_u(r)>=W^-D}: {(0.0, 1.0): 1.0, (0.0, 6.0): 3.69, (0.5, 1.0): 1.0, (0.5, 6.0): 5.237, (0.9, 1.0): 1.0, (0.9, 6.0): 6.0}
```
(`R1 = (1-u)|W^dΘ∘(L-K)|/(Ĵ P)`, `R2 = (1-u)|W^d E^{LKLK}|/((Ĵ+Ĵ²1_{ℓ≥1})P)`, maxima over `σ ∈ {±}²`, all `a₀-a₁ ∈ Z_{24}^3`, i.e. the pin's `C` taken as 1; the ratios stay ≤ 1.7.) Hypotheses: `0 < lam = 1 ≤ 𝔡⁻¹ = 1`, `|E| = .5 ≤ 2-κ = .5`, `0 ≤ u < 1`, `0 ≤ D`, `0 ≤ ℓ ≤ L`, `H` Hermitian, `‖G-M‖_max ≤ δ₀ = c_κ = 0.968` all hold. No external hypothesis (the pin is deterministic; `Prop5Decay` and `(TTT2)` are proved), so no limit computation is needed.

### Verdict
- `stNewKLK_holds (d) : STNewKLK d` — **PASS**. Proof route above uses only merged facts (`prop5Decay_holds`, `ekPropTInf_holds`, `KLK_ward`/Ward for `L`, `sum_norm_SB_row`, `SB_isSymm`) plus three private re-proofs (Ward for `L` at both charge orders, `zdistInf` triangle, `k2d_theta_tail`) and one IVT (cut `K`). Registry lines `STNewKLK`, `STNewKLKAt` (`Test/Axioms.lean:133, 178`) can go once it merges.

## (b) Script output — written Sun Oct  4 03:07:41 UTC 2026

Branch `t/T2099` commit: `8b43795 T2099: ST2-07 Induction/NewKLK (proves the pin STNewKLK, lem:newKLK)`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2099`.

### Build of the new module (log `scratchpad/T2099/b1.full`; the output below is `tail -2` of it plus two lines; the `uses hc'` line belongs to the existing note on `Step2Defs.lean:978`)
```
$ lake build RBM3D.Induction.NewKLK   # run at Sun Oct  4 03:06:24 UTC 2026
exit 0
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3723 jobs).
warnings/errors mentioning NewKLK.lean: 0
```

### Full library build with the module imported (temporary, uncommitted `import RBM3D.Induction.NewKLK` after the last import of `RBM3D.lean`; reverted after the run, `git status` clean)
```
$ lake build   # scratchpad/T2099/fullbuild_final.log, exit 0
570:info: RBM3D.lean:142:0: axiom audit: 3142 theorems, 1162 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
682:registry: 5 borrowed + 100 owed + 37 structural; 60 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
743:Build completed successfully (3843 jobs).
668:  RBM.Gauss.Sizes.STNewKLKAt: 3 [no certificate]
```

### Axioms and exact type (`lake env lean scratchpad/T2099/ev.lean`)
```
Sun Oct  4 03:05:36 UTC 2026
'RBM.Gauss.Sizes.stNewKLK_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
stNewKLK_holds : ∀ (d : ℕ), STNewKLK d
```

### Target statement, extracted by script (`sed` from the file) and the pin it must have
```
$ sed -n '1198,1201p' RBM3D/Induction/NewKLK.lean
theorem stNewKLK_holds (d : ℕ) : STNewKLK d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨C, hC, h⟩ := nkl_at d hd κ 𝔡 hκ h𝔡
  exact ⟨C, κ / 2, hC, by positivity, h⟩
$ sed -n 376,378p RBM3D/Induction/Step2Defs.lean     # the merged pin (`git diff main -- Step2Defs.lean`: 0 lines)
/-- **`lem:newKLK`**, the pin: `∃ C, δ₀` with `STNewKLKAt`. -/
def STNewKLK (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAt d κ 𝔡 C δ₀
$ sed -n 363,375p RBM3D/Induction/Step2Defs.lean     # STNewKLKAt, the body of the pin
def STNewKLKAt (d : ℕ) (κ 𝔡 C δ₀ : ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOp sz n E u σ (STLKM sz n E u H σ) a‖ ≤
            C / (1 - u) * STJhatM sz n E D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKM sz n E u H σ a‖ ≤
            C / (1 - u) * (STJhatM sz n E D ℓ u H +
              STJhatM sz n E D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)
  ... (conclusion: the two norm bounds)
```

### Compiled nonempty instances (`d = 3`, `sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`), same file, built by the command above
```
$ sed -n '1253,1287p' RBM3D/Induction/NewKLK.lean   # example 1: applies stNewKLK_holds itself
open RBM.Gauss.SizesInst in
/-- **`stNewKLK_holds`, instantiated**: the constants `C, δ₀` of the pin (`κ = 𝔡 = 1/10`), then the
time `u = δ₀/(1+δ₀) ∈ (0,1)` (so that `‖G_u - M‖_max = u/(1-u) = δ₀`, `G_u ≠ M`), and the two
bounds of `(juwo2=klk)`, `(juwo=Lklk)` at `n = 0`, `E = 0`, `D = 1`, `ℓ = 2`, `H = 0`, for all
sign patterns `σ` and all `a ∈ (Z_4^3)²`. -/
example : ∃ C δ₀ u : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < u ∧ u < 1 ∧
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STthetaOp sz0 0 0 u σ (STLKM sz0 0 0 u
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ) a‖ ≤
          C / (1 - u) * STJhatM sz0 0 0 1 2 u
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
            STprof sz0 0 u 1 2 (a 0) (a 1) ∧
        ‖STELKLKM sz0 0 0 u
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
          C / (1 - u) * (STJhatM sz0 0 0 1 2 u
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) +
            STJhatM sz0 0 0 1 2 u
              (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
              (if 1 ≤ (2 : ℝ) then 1 else 0)) * STprof sz0 0 u 1 2 (a 0) (a 1) := by
  obtain ⟨C, δ₀, hC, hδ, hAt⟩ := stNewKLK_holds 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hL4 : (2 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by norm_num [sz0]
  have hu0 : 0 < δ₀ / (1 + δ₀) := by positivity
  have hu1 : δ₀ / (1 + δ₀) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have huδ : δ₀ / (1 + δ₀) / (1 - δ₀ / (1 + δ₀)) = δ₀ := by
    field_simp
    ring
  refine ⟨C, δ₀, δ₀ / (1 + δ₀), hC, hδ, hu0, hu1, fun σ a => ?_⟩
  exact hAt sz0 0 0 (δ₀ / (1 + δ₀)) 1 2 hlam hlam' (by norm_num) hu0.le hu1 zero_le_one
    (by norm_num) hL4 0 Matrix.isHermitian_zero
    (fun x y => (nkl_STGMM_zero sz0 0 hu0.le hu1 x y).trans huδ.le) σ a
```
```
$ sed -n '1289,1314p' RBM3D/Induction/NewKLK.lean   # example 2: explicit numbers (via the private nkl_at, δ₀ = κ/2)
open RBM.Gauss.SizesInst in
/-- The same with every number explicit (`δ₀ = κ/2 = 1/20` from `nkl_at`): `u = 1/32`,
`‖G_u - M‖_max = 1/31 ≤ 1/20`, `n = 0`, `E = 0`, `D = 1`, `ℓ = 2`, `H = 0`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
    ‖STthetaOp sz0 0 0 (1 / 32) σ (STLKM sz0 0 0 (1 / 32)
        (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ) a‖ ≤
        C / (1 - 1 / 32) * STJhatM sz0 0 0 1 2 (1 / 32)
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
          STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) ∧
      ‖STELKLKM sz0 0 0 (1 / 32)
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
        C / (1 - 1 / 32) * (STJhatM sz0 0 0 1 2 (1 / 32)
          (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) +
          STJhatM sz0 0 0 1 2 (1 / 32)
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
            (if 1 ≤ (2 : ℝ) then 1 else 0)) * STprof sz0 0 (1 / 32) 1 2 (a 0) (a 1) := by
  obtain ⟨C, hC, hAt⟩ := nkl_at 3 (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hL4 : (2 : ℝ) ≤ ((sz0.L 0 : ℕ) : ℝ) := by norm_num [sz0]
  refine ⟨C, hC, fun σ a => ?_⟩
  exact hAt sz0 0 0 (1 / 32) 1 2 hlam hlam' (by norm_num) (by norm_num) (by norm_num)
    zero_le_one (by norm_num) hL4 0 Matrix.isHermitian_zero
    (fun x y => (nkl_STGMM_zero sz0 0 (by norm_num) (by norm_num) x y).trans (by norm_num)) σ a
```

### Hygiene, name-clash and diff greps
```
$ grep -n 'sorry\|admit\|native_decide\|^axiom' RBM3D/Induction/NewKLK.lean ; echo "exit $?"
exit 1
$ grep -n '^theorem\|^def\|^noncomputable def\|^lemma\|^structure\|^abbrev\|^instance' RBM3D/Induction/NewKLK.lean   # all non-private declarations
1198:theorem stNewKLK_holds (d : ℕ) : STNewKLK d := by
$ grep -c '^private theorem\|^private def' RBM3D/Induction/NewKLK.lean ; grep -c '^example' RBM3D/Induction/NewKLK.lean
38
2
$ grep -rn 'stNewKLK_holds' RBM3D | grep -v '^RBM3D/Induction/NewKLK.lean'      # name clash of the public name (the only hit is the comment edited by this commit)
RBM3D/Test/Axioms.lean:177:   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise in `(n, E, u, D, ℓ, H)`, the form `ST_g
$ grep -rln 'nkl_\|nklQ' RBM3D | grep -v NewKLK.lean ; echo "exit $?"        # clash of the private helper prefix
exit 1
$ git diff main...t/T2099 --stat
 RBM3D/Induction/NewKLK.lean | 1316 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    3 +-
 2 files changed, 1317 insertions(+), 2 deletions(-)
```

### Registry pre-check (`RBM3D/Test/Axioms.lean`), three full builds with the temporary import
```
1. unchanged registry:                         exit 0; 'STNewKLK' listed under 'carry nothing yet' (fullbuild1.log:702)
2. STNewKLK and STNewKLKAt lines removed:      576:error: build failed ; error: RBM3D.lean:142:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`: |   [RBM.Gauss.Sizes.STNewKLKAt]
3. only the STNewKLK line removed (committed): exit 0, 743:Build completed successfully (3843 jobs).
$ git diff main...t/T2099 -- RBM3D/Test/Axioms.lean | grep '^[-+] '
-   `RBM.Gauss.Sizes.STNewKLK, -- `lem:newKLK` (`3_5:371-378`): ST2-07 (+ST2-06b) (T2066, DECISIONS §28)
-   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise in `(n, E, u, D, ℓ, H)`, the form `ST_good_engine` takes: ST2-07 (+ST2-06b), `STNewKLK` is its `∃ C δ₀` form (T2071; class proposed: owed)
+   `RBM.Gauss.Sizes.STNewKLKAt, -- `lem:newKLK` (`3_5:371-378`) pointwise in `(n, E, u, D, ℓ, H)`, the form `ST_good_engine` takes: ST2-07 (+ST2-06b), `STNewKLK` is its `∃ C δ₀` form and is proved by `stNewKLK_holds` (T2099; its registry line is removed); thi
```

### Ports
No port from `../RBM1D` or `../RBM2D` (no `git -C ../RBM2D` command was run; diff-stat not applicable).  Copies of RBM3D private lemmas, adapted in the new file (all `private`):
`nkl_sqrt_le`, `nkl_theta_tail` <- `Induction/Step2K2.lean:65`, `:78` (last commit of that file `0fc2597`); `nkl_gres_blockMat_true`, `nkl_Gres_false` <- `Green/Pins.lean:350`, `:367` (`64bdfd3`); `nkl_mE_zero` <- `Induction/ConArgDet.lean:1371` (`bbd22a5`); `nkl_zdistInf_add_le` <- `Evolution/PropTInf.lean:43` (`a84c579`).

### Narrative
- Verdict: `stNewKLK_holds (d : ℕ) : STNewKLK d` is proved; its type is the merged pin (the `example : ∀ d, STNewKLK d := stNewKLK_holds` compiles). Deterministic: the main inputs are `prop5Decay_holds`, `ekPropTInf_holds`, `Ind.Gres_mul_conjTranspose`, `Ind.half_le_mE_im`, `sum_norm_Theta_row_le`; no stochastic premise, no new hypothesis.
- Constants (`nkl_at`, `Induction/NewKLK.lean:993`): `δ₀ = κ/2`, `C = 2(C₁C_sC_T + C_s) + 10C_s + C_sC_T`, `C₁ = C₅e^{1/(4c)}` (`Prop5Decay d 𝔡⁻¹`), `C_s = 2^{d-2}e`, `C_T` from `(TTT2)`; they depend on `(d, 𝔡)` only (`C`) and `κ` (`δ₀`).
- Route differs from section (a) in two places, verdict (a) unaffected, so no (a′): (S6) the cut `K` with an intermediate-value argument is replaced by a near/far split of `𝒯̃` (`nkl_tailW_eq_of_near`, `nkl_tailW_far`): `r` near iff `1 ≤ ℓ ∧ r ≤ ℓ ∧ W^{-D} ≤ 𝒯(r)`, then `𝒯̃ = 𝒯`; else `𝒯̃(r) ≤ C_s 𝒯̃(r')` for every distance `r'`. (S2) Ward for `𝓛` is entrywise: `‖𝓛_{σ,(a,b)}‖ ≤ W^{-2d}(Q_{ab}+Q_{ba})`, `Q_{ab} = Σ_{l∈[b],j∈[a]}|G_{lj}|²`, row and column masses `Im G_{ll}/η` from `G G† = G†G = (G-G†)/(2iη)`; so `npq_loopL_ward`, `sum_gloop_ward_last_div` and `KLK_ward` are not used, and `δ₀ = c_κ` of (a) became `κ/2`.
- The bounds hold for every `ℓ ≥ 0` and every real `D`: the hypotheses `ℓ ≤ L` and `0 ≤ D` of the pin are not used (the floor `W^{-D}` enters only through `0 < W^{-D}`; it is never summed over `L^d` points, DECISIONS §29 (3)).
- Instances: example 1 uses `stNewKLK_holds` as stated (abstract `C, δ₀`), `E = 0`, `D = 1`, `ℓ = 2` (so `1_{ℓ≥1}` is on), `H = 0` and `u = δ₀/(1+δ₀)`: `‖G_u - M‖_max = u/(1-u) = δ₀` and `G_u ≠ M` (`nkl_STGMM_zero`). Example 2 is the same with `κ = 1/10`, `u = 1/32`, `‖G_u - M‖_max = 1/31 ≤ 1/20`. Every deterministic hypothesis (`0 < lam ≤ 𝔡⁻¹`, `|E| ≤ 2 - κ`, `0 ≤ u < 1`, `0 ≤ D`, `0 ≤ ℓ ≤ L`, Hermitian, weak law) is discharged; none is left open.
- Registry: removing the `STNewKLK` line passes the audit; removing `STNewKLKAt` fails it (the scan finds it: it is a hypothesis of `ST_good_engine`, `Induction/Step2Core.lean:1002`, and no theorem concludes `STNewKLKAt` itself). The commit removes the `STNewKLK` line and edits the `STNewKLKAt` comment only.

## (c) Verified names (`#exists` script in `scratchpad/T2099/names.lean`, `env.contains`; run Sun Oct  4 03:08:29 UTC 2026)
```
$ lake env lean scratchpad/T2099/names.lean   # one line per name: `<name>: true|false`; 36 names, 36 true, 0 false
Finset.le_sup', Matrix.IsHermitian.submatrix, Complex.abs_im_le_norm, Real.sqrt_le_iff, one_le_pow₀, Real.one_le_exp, Matrix.mul_diagonal, Finset.sum_comm, Complex.sub_conj, Complex.mul_conj, Complex.inv_I, Complex.normSq_eq_norm_sq, Complex.norm_natCast, norm_sum_le, Matrix.one_apply_ne, Matrix.one_apply_eq, Fin.sum_univ_two, Finset.sum_ite_eq', div_le_iff₀, Matrix.conjTranspose_nonsing_inv, Matrix.inv_submatrix_equiv, Real.sq_sqrt, Real.exp_le_exp, Real.rpow_pos_of_pos, Complex.star_def, Matrix.mul_apply, RBM.Gauss.ring_inverse_smul_one, RBM.prop5Decay_holds, RBM.ekPropTInf_holds, RBM.Ind.Gres_mul_conjTranspose, RBM.Ind.half_le_mE_im, RBM.sum_norm_Theta_row_le, RBM.Theta_transpose_of_three_le, RBM.sum_norm_SB_row, RBM.Loop.KLK_two, RBM.norm_mul_mSigma_lt_one
```
Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- `T2099a` (proof route, not a statement change): `3_5:611` takes "WLOG `𝒯_u(ℓ) ≥ W^{-D}`" and a cut `K ≤ ℓ` with `𝒯_u(K) = W^{-D}`; the Lean proof keeps the floor and splits near/far (`1 ≤ ℓ`, `r ≤ ℓ`, `W^{-D} ≤ 𝒯(r)`), uses `𝒯(max(r-1,0)) ≤ 2^{d-2}e 𝒯(r)` for `𝒯_u(K+1) ≍ 𝒯_u(K)` (`3_5:651`), and needs no `ℓ ≤ L`.
- `T2099b` (statement refinement): the paper's "weak local law `(Gtmwc)`" with `1 + o(1)` in `3_5:644` is the explicit `‖G_u - M‖_max ≤ δ₀ = κ/2` (`Ind.half_le_mE_im`: `κ/2 ≤ Im m`), giving `Im G_{xx} ≤ 2 Im m` and the Ward factor `5 W^{-d}/(1-u)` (`4` from `𝓛`, `1` from `𝒦`) instead of `(1+o(1))/(W^d(1-u))`; absorbed in `C`. The pin already carries `δ₀`, so no change of the merged signature.
- `T2099c` (proof route): the paper bounds `|𝓛_{±±}|` by Cauchy-Schwarz against `𝓛_{-+}` and uses `(WI_calL)`, `(WI_calK)`; Lean bounds `|𝓛_σ(a,b)| ≤ W^{-2d}(Q_{ab}+Q_{ba})` for all four sign patterns and `Σ_c |𝒦_σ(a,c)| ≤ W^{-d}(1-u)⁻¹` from `sum_norm_Theta_row_le` (no Ward for `𝒦`).
- Registry: the `STNewKLKAt` line must stay (see above) until a theorem concludes `STNewKLKAt` itself or the downstream hypotheses are discharged; the `STNewKLK` line is removed in this commit (the ticket allows it).
- Hub: `RBM3D.lean` needs `import RBM3D.Induction.NewKLK` after the last import at merge; the unused import `RBM3D.Loop.KLWard` (named by the ticket) is kept.
- Open: none for this target. The ticket (T2039 F5) says the pin is deterministic; no stochastic input was needed and no stop condition occurred.
