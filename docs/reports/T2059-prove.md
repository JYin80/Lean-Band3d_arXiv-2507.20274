Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 15:01:26 UTC 2026

Notation: `R = W^ε ℓ_t`, `ℓ = ellT L g t ≥ 1`, `ϑ` with `STMollifierProps g C c` (`‖ϑ_t(a)‖ ≤ C ℓ^{-dm} e^{-cΣ_{i≥1}|a_i-a_0|/ℓ}`), `‖𝒜‖ = max_b |𝒜_b|`, `(𝒫𝒜)(a₁)` sums `L^{dm}` terms.

### (i) Exponent table
| Quantity | Value | Constraint / source | Slack |
|---|---|---|---|
| near set (all pair distances `< R`) | `≤ ((2R+1)^d)^m` terms: each `b_i` lies in the `ℓ¹`-ball of radius `R` about `b_0=a₁`; per coordinate `≤ 2R+1` residues | counted in script below (`near ≤ ball count`, 24 rows) | e.g. L=9,g=1,m=2,t=0: 1663 vs 531441 |
| near contribution to `‖𝒫𝒜·ϑ‖` | `≤ C (2R+1)^{dm} ℓ^{-dm} ‖𝒜‖ ≤ C (3W^ε)^{dm}‖𝒜‖ ≤ C W^{2εdm}‖𝒜‖` | `ℓ ≥ 1` gives `(2W^εℓ+1)/ℓ ≤ 2W^ε+1 ≤ 3W^ε`; `3 ≤ 4 ≤ W^ε` gives `3W^ε ≤ W^{2ε}` | `W^{2ε}/(3W^ε)=W^ε/3 ≥ 4/3` |
| far part (some pair `≥ R`), `|𝒜_b| ≤ W^{-D}` | `≤ L^{dm}` terms (those `b` with `b_0=a₁`); `L^{dm} ≤ W^{Km}` | hyp. `L^d ≤ W^K` (T2041c / D50 / §21); `|ϑ| ≤ Cℓ^{-dm} ≤ C` | contribution `≤ C W^{Km-D}` |
| mollifier constant `C` absorbed | `1+C ≤ 4^C ≤ W^{Cε}`; `C ≤ W^{Cε} ≤ W^C` | `4 ≤ W^ε`; `x ≤ 4^x`, `1+x ≤ 4^x` for `x>0` (grid-checked below; true since `4^x ≥ 1+x ln4`); `ε<1, W>1` | `4^C/(1+C) ≥ 1` |
| **`C_n`** (target 1) | `C_n = C + (2d+K)·m` (> 0) | chain: `‖𝒬𝒜‖ ≤ ‖𝒜‖ + C W^{2dmε}‖𝒜‖ + C W^{Km-D} ≤ W^{(C+2dm)ε}‖𝒜‖ + W^{-D+C+Km}`; `(C+2dm)ε ≤ C_n ε`, `C+Km ≤ C_n` | exponent slack `C_n-(C+2dm)=Km` (first term), `C_n-(C+Km)=2dm` (second) |
| dependence of `C_n` | on `(d,m,K,C)`; not on `Λ, c, ε, D, L, g, W, t` | ticket allows `(d,m,Λ,K,C,c)`; the proof needs less | — |
| unused hypotheses (target 1) | `1 < D`, `Λ`, `c>0` beyond `e^{-…} ≤ 1` | harmless | — |
| `ε` | `0<ε<1`, `4 ≤ W^ε` | instance: `W=16, ε=1/2` gives `W^ε=4`, slack 0 | tight by design |
| `K` | `L^d ≤ W^K` | instance: `125 ≤ 16^2=256` | `256/125 ≈ 2.05` |
| decay clause (target 2): `A−𝒬𝒜 = (𝒫𝒜)ϑ` | `‖𝒜‖ ≤ W^{C₀}`, `C₀ ≥ 0` | far `a` (pair `≥ W^{ε'}ℓ`): triangle inequality gives some `i≥1` with `|a_i-a_0| ≥ W^{ε'}ℓ/2`, hence `Σ_{i≥1}|a_i-a_0|/ℓ ≥ W^{ε'}/2` | — |
| | `‖(𝒫𝒜)ϑ‖(a) ≤ L^{dm}W^{C₀}·C e^{-cW^{ε'}/2} ≤ C W^{Km+C₀} e^{-cW^{ε'}/2}` | uses `ℓ^{-dm} ≤ 1`, `L^d ≤ W^K` | needs `≤ W^{-D'}` |
| threshold `W₀` | `p = C₀+Km+D'`, `k = ⌈p/ε'⌉+1`, `W₀ = max(1, (C·k!·(2/c)^k)^{1/ε'})` | `e^y ≥ y^k/k!` with `y=cW^{ε'}/2`: `e^y ≥ (c/2)^k W^{ε'k}/k! ≥ (c/2)^k W^{p+ε'}/k!` (as `ε'k ≥ p+ε'`, `W ≥ 1`) `≥ C W^p` iff `W^{ε'} ≥ C k!(2/c)^k` | checked exactly in script (4) |
| dependence of `W₀` | on `(d,m,C,c,K,C₀,ε',D')`; **not** `Λ`; **needs `K`** | the bound `L^{dm} ≤ W^{Km}` is used; without a bound on `L` the factor `L^{dm}` is not dominated by `e^{-cW^{ε'}/2}` | propose `T2059a`: add `K` and `L^d ≤ W^K` to the decay clause (same shape as D50); `Λ` is not needed |
| registry | `STQopNorm` is registered owed (`RBM3D/Test/Axioms.lean:128`); its line can go once this merges (cleanup ticket) | — | — |

### (ii) One concrete nondegenerate instance
**Target 1** (`stQopNorm_holds 3`): `d=3, m=1, Λ=1, K=2, C=(1+40dm)6^{dm}=26136, c=1/2` (T2055 `QopAlgebra_mollifier_props`), `L=5, g=1, t=1/2`, `W=16, ε=1/2, D=4` (`W^ε=4`), `𝒜 = 1` on `{b_0=b_1}` else 0 (all pair distances 0 on its support, so `EKFastDecay` holds for any `D`; `‖𝒜‖=1`, `𝒫𝒜≡1`), `C_n=26144`. (Recommend `W=16, ε=1/2` over `W=64, ε=1/3`: `16^{1/2}=4` is simpler than `64^{1/3}`.) Numerics of the proof chain at the ticket's grid (`W=64, ε=1/3, D=4, K=2`, T2055 mollifier, `ϑ=exp(-uS)/z^{dm}`, `u=1/(1+g/√(1-t))+1/L`, `ℓ=ellT`; `𝒜` = (near: 1 or uniform[-1,1]; far: ±W^{-D}), 3 sampled `a₁` per row, each row uses the full fibre `{b : b_0=a₁}` (`(L^d)^m` entries)):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2059/pf.py
cols: LHS=max||QA|| over modes/a0, sharp=||A||(1+Ceff(2R+1)^{dm}/l^{dm})+Ceff L^{dm}W^-D, near<=ball count, #far a, Ceff
L=5 g=0.1 m=1 t=0: LHS=7.615 sharp=106.9 near=57<=729 far#=68 Ceff=0.151 True
L=5 g=0.1 m=1 t=0.9: LHS=5.527 sharp=82.83 near=57<=729 far#=68 Ceff=0.115 True
L=5 g=0.1 m=1 t=0.999: LHS=3.128 sharp=595.8 near=125<=1.819e+04 far#=0 Ceff=1.04 True
L=5 g=0.1 m=2 t=0: LHS=42.61 sharp=1.213e+04 near=1909<=5.314e+05 far#=13716 Ceff=0.0228 True
L=5 g=0.1 m=2 t=0.9: LHS=24.03 sharp=6964 near=1909<=5.314e+05 far#=13716 Ceff=0.0131 True
L=5 g=0.1 m=2 t=0.999: LHS=16.04 sharp=3.607e+05 near=15625<=3.308e+08 far#=0 Ceff=1.09 True
L=5 g=1.0 m=1 t=0: LHS=2.708 sharp=47.21 near=57<=729 far#=68 Ceff=0.0651 True
L=5 g=1.0 m=1 t=0.9: LHS=3.128 sharp=594.4 near=125<=1.819e+04 far#=0 Ceff=1.04 True
L=5 g=1.0 m=1 t=0.999: LHS=1.192 sharp=1192 near=125<=6.892e+04 far#=0 Ceff=2.19 True
L=5 g=1.0 m=2 t=0: LHS=7.08 sharp=2249 near=1909<=5.314e+05 far#=13716 Ceff=0.00423 True
L=5 g=1.0 m=2 t=0.9: LHS=16.04 sharp=3.608e+05 near=15625<=3.308e+08 far#=0 Ceff=1.09 True
L=5 g=1.0 m=2 t=0.999: LHS=3.806 sharp=1.461e+06 near=15625<=4.75e+09 far#=0 Ceff=4.81 True
L=9 g=0.1 m=1 t=0: LHS=5.721 sharp=75.05 near=63<=729 far#=666 Ceff=0.107 True
L=9 g=0.1 m=1 t=0.9: LHS=3.582 sharp=52.49 near=63<=729 far#=666 Ceff=0.0727 True
L=9 g=0.1 m=1 t=0.999: LHS=6.561 sharp=188.6 near=729<=1.819e+04 far#=0 Ceff=0.328 True
L=9 g=0.1 m=2 t=0: LHS=17.93 sharp=6047 near=1663<=5.314e+05 far#=529778 Ceff=0.0114 True
L=9 g=0.1 m=2 t=0.9: LHS=7.796 sharp=2810 near=1663<=5.314e+05 far#=529778 Ceff=0.00529 True
L=9 g=0.1 m=2 t=0.999: LHS=56.17 sharp=3.559e+04 near=531441<=3.308e+08 far#=0 Ceff=0.108 True
L=9 g=1.0 m=1 t=0: LHS=1.012 sharp=23.47 near=63<=729 far#=666 Ceff=0.0315 True
L=9 g=1.0 m=1 t=0.9: LHS=6.561 sharp=188.9 near=729<=1.819e+04 far#=0 Ceff=0.328 True
L=9 g=1.0 m=1 t=0.999: LHS=1.442 sharp=1303 near=729<=3.89e+05 far#=0 Ceff=2.44 True
L=9 g=1.0 m=2 t=0: LHS=1.006 sharp=526.6 near=1663<=5.314e+05 far#=529778 Ceff=0.000989 True
L=9 g=1.0 m=2 t=0.9: LHS=56.17 sharp=3.559e+04 near=531441<=3.308e+08 far#=0 Ceff=0.108 True
L=9 g=1.0 m=2 t=0.999: LHS=4.963 sharp=1.698e+06 near=531441<=1.513e+11 far#=0 Ceff=5.96 True
ALL OK: True  log10 of Lean RHS W^{Cn eps} (Cn=C+(2d+K)m, C=(1+40dm)6^{dm}): m=1: 15740.256413278246  m=2: 6769629.973210637
```
(`sharp` is the proof's bound with the mollifier's measured `C_eff`; the Lean bound `W^{C_n ε}‖𝒜‖+…` has `log10 ≈ 1.6e4` (m=1), `6.8e6` (m=2), so it holds trivially there; both sides are reported as asked. Rows with `far#=0` have no far `a` at `W=64` (`R > diam`), so the far values of `(𝒫𝒜)ϑ` are only measurable where `far#>0`; at `W=64` they are not `≤ W^{-4}` (not asymptotic), consistent with target 2 being a statement for `W ≥ W₀`.)
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2059/pf2.py
m 1 C 26136 Cn 26144
m 2 C 11244096 Cn 11244112
x<=4^x: True 1+x<=4^x: True
W^eps= 4.0 >=4: True | L^d= 125 <= W^K= 256 : True | Cn= 26144
C0=0 eps'=1 D'=1: k=4 W0=1.606e+08 W=1.606e+08: ln(C W^p)=66.85 <= c W^eps'/2=4.014e+07: True
C0=0 eps'=1 D'=1: k=4 W0=1.606e+08 W=1.606e+09: ln(C W^p)=73.76 <= c W^eps'/2=4.014e+08: True
C0=0 eps'=0.5 D'=1: k=7 W0=4.658e+24 W=4.658e+24: ln(C W^p)=180.6 <= c W^eps'/2=5.395e+11: True
C0=0 eps'=0.5 D'=1: k=7 W0=4.658e+24 W=4.658e+25: ln(C W^p)=187.5 <= c W^eps'/2=1.706e+12: True
C0=1 eps'=0.5 D'=2: k=11 W0=1.915e+37 W=1.915e+37: ln(C W^p)=439.4 <= c W^eps'/2=1.094e+18: True
C0=1 eps'=0.5 D'=2: k=11 W0=1.915e+37 W=1.915e+38: ln(C W^p)=450.9 <= c W^eps'/2=3.459e+18: True
diam Z_5^3 = 6  W0 (eps'=1,C0=0,D'=1) = 160579584.0
```
**Target 2** (`stQop_sub_fastDecay`) at the same data with `ε'=D'=1`, `C₀=0`: `p=3, k=4, W₀=1.606e8` (script (4), inequality holds at `W₀` and `10·W₀`; `L^d=125 ≤ W₀^2`). Observation: for `L=5` (`diam=6`) and `W ≥ W₀`, `W^{ε'}ℓ ≥ 1.6e8 > diam`, so `EKFastDecay` is **vacuous** here; this is inherent for `ε' > K/d` and large `W` (`diam = d⌊L/2⌋ ≤ (d/2)W^{K/d}` against `W^{ε'}`), not a defect of the statement. The compiled instance is therefore a valid but conclusion-vacuous check; the content is carried by the proof (far bound above).
**External hypotheses:** none (the mollifier is the merged T2055 theorem; `STMollifierProps` is discharged, not assumed), so no limit computation is owed.

### Verdicts
- Target 1 `stQopNorm_holds`: **PASS** (hypotheses of the pin jointly satisfiable at the instance; exponent `C_n = C + (2d+K)m` closes with the slack above).
- Target 2 `stQop_sub_fastDecay`: **PASS**, with the quantifier-order correction `T2059a`: `W₀` depends on `K` (and the extra hypothesis `L^d ≤ W^K`), not on `Λ`.

## (b) Script output — written Sat Oct  3 15:08:56 UTC 2026

```
$ lake build RBM3D.Induction.QopNorm   (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2059, branch t/T2059, commit 386d02a)
warning: RBM3D/Induction/QopNorm.lean:22:100: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3705 jobs).
$ lake build   (full library; the root does not yet import QopNorm, the hub adds it at merge)
Build completed successfully (3772 jobs).   [exit 0, run 2026-10-03 15:08 UTC]
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/QopNorm.lean  -> no match (rc=1)
```

**Registry pre-check** (temporary file `scratchpad/T2059/ax.lean`: `import RBM3D`, `import RBM3D.Induction.QopNorm`, two `#print axioms`, `#assert_rbm_axioms`; `lake env lean`, exit 0):
```
'RBM.Gauss.Sizes.stQopNorm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stQop_sub_fastDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 1835 theorems, 815 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
```
No new `Prop` predicate is defined, so no registry line is added (`RBM3D/Test/Axioms.lean` untouched). The registered-owed line `RBM.Gauss.Sizes.STQopNorm` (`Axioms.lean:128`) can go once this merges (cleanup ticket, T2049).

**Target statements** (extracted by `sed -n` from the file):
```lean
theorem stQopNorm_holds (d : ℕ) : STQopNorm d := by
theorem stQop_sub_fastDecay (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' (A - STQop (d := d) ϑ t A) := by
  obtain ⟨W₁, hW₁, hW₁'⟩ := qn_growth (p := C₀ + K * m + D') hC hc hε'
  refine ⟨W₁, hW₁, ?_⟩
  intro L hL g hg W hW hLW
```
**Type check that target 1 is exactly the pin** (`scratchpad/T2059/ty.lean`):
```
$ lake env lean scratchpad/T2059/ty.lean   (#check (stQopNorm_holds : ∀ d, STQopNorm d); #check @stQop_sub_fastDecay)
stQopNorm_holds : ∀ (d : ℕ), STQopNorm d
stQop_sub_fastDecay : ∀ (d m : ℕ) (K C c C₀ ε' D' : ℝ),
  0 < C →
    0 < c →
      0 < ε' →
        ∃ W₀,
          1 < W₀ ∧
            ∀ (L : ℕ) (x : 3 ≤ L) (g : ℝ),
              0 < g →
                ∀ (W : ℝ),
                  W₀ ≤ W →
                    ↑L ^ d ≤ W ^ K →
                      ∀ (ϑ : ℝ → (Fin (m + 1) → RBM.Zd d L) → ℂ),
                        STMollifierProps g C c ϑ →
                          ∀ (t : ℝ),
                            0 ≤ t →
                              t < 1 →
                                ∀ (A : (Fin (m + 1) → RBM.Zd d L) → ℂ),
                                  ‖A‖ ≤ W ^ C₀ → RBM.EKFastDecay g t W ε' D' (A - STQop ϑ t A)
```

**Compiled nonempty instances** (same file, `example`s; every deterministic hypothesis discharged: `STMollifierProps` by the merged T2055 theorem `QopAlgebra_mollifier_props`, `EKFastDecay` for `qnA` by `qnA_fastDecay`, `4 ≤ W^ε` by `16^{1/2} = 4`, `5^3 ≤ 16^2`; no pin of another gate is assumed):
```lean
private def qnA : (Fin 2 → Zd 3 5) → ℂ := fun b => if b 0 = b 1 then 1 else 0
private theorem qnA_ne : qnA ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [qnA] at this
private theorem qnA_norm_le : ‖qnA‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
  unfold qnA
  split_ifs <;> simp
private theorem qnA_fastDecay (W ε D : ℝ) (hW : 0 < W) (_hε : 0 < ε) :
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W ε D qnA := by
  intro a ⟨i, j, hij⟩
  by_cases h : a 0 = a 1
  · exfalso
    have hz : zdistD 3 5 (a i - a j) = 0 := by
      have : a i - a j = 0 := by
        fin_cases i <;> fin_cases j <;> simp [h]
      rw [this]; simp
    have hpos : 0 < W ^ ε * ellT 5 1 (1 / 2) :=
      mul_pos (Real.rpow_pos_of_pos hW _) (lt_of_lt_of_le zero_lt_one (one_le_ellT (by norm_num)))
    rw [hz] at hij
    simp at hij
    linarith
  · simp [qnA, h, Real.rpow_nonneg hW.le]
/-- **Instance of `stQopNorm_holds`** at `d = 3`, `m = 1`, `Λ = 1`, `K = 2`, the mollifier of
`QopAlgebra_mollifier_props` (`C = 26136`, `c = 1/2`) at `L = 5`, `g = 1`, `t = 1/2`, `W = 16`, `ε = 1/2`
(`W^ε = 4`), `D = 4`, and the nonzero decaying tensor `qnA`. -/
example : ∃ Cn : ℝ, 0 < Cn ∧ qnA ≠ 0 ∧
    ‖STQop (d := 3) (QopAlgebra_mollifier 3 5 1 1) (1 / 2) qnA‖ ≤
      (16 : ℝ) ^ (Cn * (1 / 2 : ℝ)) * ‖qnA‖ + (16 : ℝ) ^ (-4 + Cn) := by
  obtain ⟨Cn, hCn, h⟩ := stQopNorm_holds 3 (le_refl 3) 1 1 2 ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1))
    (1 / 2) one_pos two_pos (by positivity) (by norm_num)
  have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨Cn, hCn, qnA_ne, ?_⟩
  exact h 5 (by norm_num) 1 one_pos le_rfl 16 (1 / 2) 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [h16]) (by rw [Real.rpow_two]; norm_num)
    (QopAlgebra_mollifier 3 5 1 1) (QopAlgebra_mollifier_props 3 5 1 (by norm_num) one_pos)
    (1 / 2) (by norm_num) (by norm_num) qnA (qnA_fastDecay 16 (1 / 2) 4 (by norm_num) (by norm_num))
/-- **Instance of `stQop_sub_fastDecay`** at the same data with `ε' = D' = 1`, `C₀ = 0`: there is a `W` (any
`W ≥ max W₀ 16`) with `L^d = 125 ≤ W^2` and `‖qnA‖ ≤ W^0` at which `qnA - 𝒬_{1/2} qnA` is `(1/2, 1, 1)`-decaying.
For `L = 5` the diameter of the torus is `6`, so for large `W` the window `W^{ε'} ℓ_t` exceeds it and the
conclusion `EKFastDecay` is vacuous at this `L`: the content is in the proof (far bound for `L^d ≤ W^K`). -/
example : ∃ W : ℝ, 16 ≤ W ∧
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W 1 1
      (qnA - STQop (d := 3) (QopAlgebra_mollifier 3 5 1 1) (1 / 2) qnA) := by
  obtain ⟨W₀, hW₀, h⟩ := stQop_sub_fastDecay 3 1 2 ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1))
    (1 / 2) 0 1 1 (by positivity) (by norm_num) one_pos
  have hW16 : (16 : ℝ) ≤ max W₀ 16 := le_max_right _ _
  refine ⟨max W₀ 16, hW16, ?_⟩
  refine h 5 (by norm_num) 1 one_pos (max W₀ 16) (le_max_left _ _) ?_
    (QopAlgebra_mollifier 3 5 1 1) (QopAlgebra_mollifier_props 3 5 1 (by norm_num) one_pos)
    (1 / 2) (by norm_num) (by norm_num) qnA ?_
  · rw [Real.rpow_two]; norm_num; nlinarith [hW16]
  · rw [Real.rpow_zero]; exact qnA_norm_le
```

**Name-clash grep** (main worktree `RBM3D/` and `RBM3D.lean`, excluding the new file):
```
$ grep -rn "stQopNorm_holds\|stQop_sub_fastDecay\|qn_card\|qn_Psum\|qn_arith\|qn_growth\|qn_one_add\|qnA" /Users/junyin/Lean_proof/RBM3D/RBM3D /Users/junyin/Lean_proof/RBM3D/RBM3D.lean | grep -v Induction/QopNorm
(no output, rc=1)
$ git diff --name-only main...t/T2059
RBM3D/Induction/QopNorm.lean
```

**Ports.** No RBM1D/RBM2D text was copied or read; the proof route is the one named in the ticket (RBM2D `Induction/QopBounds.lean:525`, `:622`, commit `c9a24cf`) and the Lean was written here for `Zd d L` and the abstract `STMollifierProps`. No `git diff --stat` owed.

**Narrative.**
- Target 1 `stQopNorm_holds`: `C_n = C + 2dm + Km` (preflight table). Near set (all `|b_i - b_1| < W^ε ℓ_t`, `b_1 = a_1`): `≤ ((2R+2)^d)^m` tensors (`qn_card_zball`, `qn_card_ball`, `qn_card_pi`), `R = W^ε ℓ_t`; with `ℓ_t ≥ 1` and `W^ε ≥ 4` the factor `((2R+2)/ℓ_t)^{dm} ≤ (3W^ε)^{dm} ≤ W^{2dmε}`. Far set: `≤ (L^d)^m ≤ W^{Km}` tensors of size `W^{-D}` (`EKFastDecay` with `j = 0`). `1 + C ≤ (W^ε)^C` and `C ≤ W^C` (`qn_one_add_le`, `qn_arith`) absorb the mollifier constant. Hypotheses `3 ≤ d`, `Λ`, `g ≤ Λ`, `1 < D`, `c > 0` (beyond `exp ≤ 1`) are unused by the proof.
- Target 2 `stQop_sub_fastDecay`: `(𝒜 - 𝒬_t𝒜)_a = (𝒫𝒜)_{a_1} ϑ_{t,a}`; a far `a` (some `|a_i - a_j| ≥ W^{ε'} ℓ_t`) has `Σ_{k≥1} |a_k - a_1| ≥ W^{ε'} ℓ_t/2` by the triangle inequality (`zdistD_add_le`, `zdistD_neg`), so `‖ϑ‖ ≤ C e^{-cW^{ε'}/2}` (`ℓ^{-dm} ≤ 1`); `‖𝒫𝒜‖ ≤ (L^d)^m W^{C₀} ≤ W^{C₀+Km}`. The threshold is existential (`qn_growth`: `C W^p ≤ exp(c W^{ε'}/2)` for large `W`, from Mathlib `isLittleO_rpow_exp_atTop`), `p = C₀ + Km + D'`; no explicit `W₀` formula (the preflight factorial formula is not formalised).
- Statement of target 2 differs from the ticket text in that `Λ`, `g ≤ Λ` do not occur (not needed), `K` and `L^d ≤ W^K` do, `0 < K`, `0 ≤ C₀`, `0 < D'` are dropped (unused; `D' ∈ ℝ` arbitrary, `C₀ ∈ ℝ` arbitrary).
- Instance 2 is conclusion-vacuous at `L = 5` for large `W` (as preflight observed: window `W^{ε'} ℓ_t` exceeds the diameter `6`); its hypotheses are nondegenerate and discharged.
- Scope: only `RBM3D/Induction/QopNorm.lean` committed (`386d02a`); `RBM3D/Test/Axioms.lean` and the root are untouched.

## (c) Verified Mathlib names (all used in the compiled file)
Nat.lt_ceil, Nat.ceil_lt_add_one, ZMod.natCast_zmod_val, ZMod.natCast_self, Fintype.card_piFinset, Fintype.mem_piFinset, Finset.prod_le_prod₀ (h0 h1), Finset.sum_filter_add_sum_filter_not, Finset.card_image_le, Real.add_one_le_exp, Real.exp_one_lt_d9, Real.rpow_def_of_pos, Real.rpow_natCast, Real.rpow_two, Real.rpow_add, Real.rpow_mul, Real.rpow_neg, Real.mul_rpow, Real.one_le_rpow, Real.rpow_le_rpow_of_exponent_le, pi_norm_le_iff_of_nonneg, norm_le_pi_norm, inv_le_one_of_one_le₀, one_le_pow₀, pow_le_one₀, pow_le_pow_left₀, tendsto_rpow_atTop, Filter.Tendsto.const_mul_atTop, Filter.Tendsto.atTop_div_const, isLittleO_rpow_exp_atTop (root namespace).
Verified absent / different shape: `Real.isLittleO_rpow_exp_atTop` (absent: the name is root-level `isLittleO_rpow_exp_atTop`, `Pow/Asymptotics.lean:345`); `Finset.prod_le_prod` in this Mathlib takes a single hypothesis (`Algebra/Order/BigOperators/Group/Finset.lean:111`), use `prod_le_prod₀`.

## (d) Open issues and paper-delta candidates
- `T2059a` (quantifier order of the decay clause, `lem_+Q`, `3_5:1284-1289`): the paper states no order. Lean: `∃ W₀ (depending on d, m, K, C, c, C₀, ε', D')`, `∀ W ≥ W₀`, `L^d ≤ W^K`; the hypothesis `L^d ≤ W^K` and the dependence on `K` are needed (without a bound on `L` the factor `L^{dm}` of the far sum is not dominated by `e^{-cW^{ε'}/2}`); `Λ` is not needed. Same shape as D50 (`T2041c`).
- `T2059b` (cite D50 / `T2041c`): `STQopNorm` carries `4 ≤ W^ε` and `L^d ≤ W^K`; `C_n = C + 2dm + Km` depends on `(d, m, K, C)` only (not on `Λ`, `c`).
- Registry: line `RBM.Gauss.Sizes.STQopNorm` in `Axioms.lean` can be removed by the cleanup ticket.
