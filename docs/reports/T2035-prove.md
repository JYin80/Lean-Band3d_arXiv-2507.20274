Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct  3 13:00:52 UTC 2026

Target (only as far as used): `EKSumDecayNonzero d n Λ κ` (`RBM3D/Evolution/Pins.lean:128`): given `Prop5Short`, `Prop8ZeroMode`, `3 ≤ d`,
`2 ≤ n`, `0 < Λ`, `0 < κ`, there is `C > 0` such that for all `L ≥ 3`, `0 < g ≤ Λ`, `0 ≤ s`, `1 - g²/L² ≤ s ≤ t < 1`, `‖m‖ = 1`,
`κ ≤ Im m`, `σ`, `A ⊇ {i : σ i ≠ σ (finRotate n i)}`, all `𝒜`: `‖Q^(A) U^(n)_{s,t,σ} 𝒜‖ ≤ C ‖𝒜‖`.
Write `d = k + 2`, `μ_i = m(σ_i) m(σ_{i+1})` (`cycProd (EKsgn m σ) i = PropSpin m (σ i) * PropSpin m (σ (finRotate n i))`,
`Kernel/Evolution.lean:49`), `K_i = uKer μ_i s t = (1 - sμ_i SB) Θ_{tμ_i}`.

### (i) Exponent table

| # | quantity | value / bound | constraint | slack |
|---|---|---|---|---|
| 1 | structure | `Q^(A) U 𝒜 = tensorKer (K_i or Proj·K_i) 𝒜`, `‖·‖ ≤ (∏_i ‖K'_i‖_{∞→∞}) ‖𝒜‖` | `zeroModeSet_tensorKer` (`:298`), `norm_tensorKer_le` (`:420`), merged (`Kernel/Evolution.lean`) | none needed; for `n`-fold tensors of matrices the abs-row-sum norm is exactly `∏ ‖K'_i‖` (so `∏` is the sharp sup over `𝒜`) |
| 2 | case `i ∉ A` | `σ_i = σ_{i+1}` (contrapositive of `A ⊇ I_diff`), so `μ_i = PropSpin m (σ_i)²`; `‖K_i‖ ≤ C_s` by `ekSameRow_holds` (EK-2, `XiPins.lean:357`; `C_s = 1 + C_5s(1 + Λ² expC k c_5s)`) | needs `‖m‖=1`, `κ ≤ Im m`, `0 ≤ s ≤ t < 1` (all in the pin) | numerics (d=3): `max ‖K_i‖` over table below = 1.0128 (L=5) → 1.0008 (L=21) |
| 3 | case `i ∈ A` (either sign pattern) | `Proj·K_i = Proj + (t-s) μ_i · SB · Θ̊_{tμ_i}` (`projMat_mul_SB_comm`, `projMat_mul_Theta`, `:359,:373`), so `‖Proj K_i‖ ≤ 2 + (t-s) ‖SB‖ ‖Θ̊‖ = 2 + (t-s) Σ_b ‖Θ̊_{tμ_i}(0,b)‖` (`norm_projMat_le` `:331` ≤ 2, `‖SB‖ = 1`, `norm_le_sum_row_zero` + `Theta0_apply_add_right`) | `‖tμ_i‖ = t < 1` (`norm_t_mul_lt_one`) | numerics: `max ‖Proj K_i‖` = 2.0022 (diff sign), 2.0000 (same sign) |
| 4 | pin 8 row sum | `‖Θ̊_{tμ}(0,b)‖ ≤ C_8 (g²+|1-t|)⁻¹ (|b|+1)^{-k}`, `σ₁,σ₂` arbitrary, `κ ≤ Im m`, `g ≤ Λ` | `Prop8ZeroMode d Λ κ` (antecedent of the pin; `Pins.lean:88`) | numerics d=3: `C_8,est = max (g²+|1-t|)(|a|+1)|Θ̊_t(0,a)|` = 1.984 (L=5) … 1.9999 (L=31), stable |
| 5 | lattice sum | `Σ_b (|b|+1)^{-k} ≤ E L²`, `E = e^{√(k+2)} 2^{k+2} radC 1`; merged `sum_radial_pow_le` (`Defs/RadialSum.lean:192`), any `k ≥ 1` | `1 ≤ L` | `d=3`: `E = 1.043e6`; true `S_L/L² = 1.21 (L=5), 1.44 (L=21), 1.48 (L=31)` (huge slack, harmless) |
| 6 | window arithmetic | `(t-s)(g²+|1-t|)⁻¹L² ≤ (1-s)(g²)⁻¹L² ≤ 1` | `s ≤ t`, `|1-t| ≥ 0`, `(1-s)L² ≤ g²` (⇔ `1 - g²/L² ≤ s`) | none: the exact constant is 1; at `s = 1-g²/L²`, `t=(1+s)/2` the quantity `(1-s)L²/(g²+|1-t|) = 1/(1+1/(2L²))` = 0.9804 (L=5), 0.9989 (L=21) |
| 7 | use of `A ⊇ I_diff` | only to force `σ_i = σ_{i+1}` for `i ∉ A` (row 2); `i ∈ A` needs no sign information (row 3 is uniform in `σ₁,σ₂`) | hypothesis `∀ i, σ i ≠ σ (finRotate n i) → i ∈ A` | none; `A = univ` and `A = I_diff` both covered |
| 8 | per-index constant | `C_ind = max(C_s, 2 + C_8 E)`, uniform in `L, g, s, t, m, σ, A, i` | depends on `(d, Λ, κ)` only | — |
| 9 | final constant | `C = C_ind^n` (`n` only as exponent; no `L^{nτ}`) | `C > 0`: `C_s > 0`, `2 + C_8 E > 0` | numerics `∏` (n=2): ≤ 4.0047, (n=3) ≤ 7.9048, vs `2^n` = 4, 8 |
| 10 | ranges | `3 ≤ d`, `d = k+2`, `0 < Λ`, `0 < κ`, `0 < g ≤ Λ`, `L ≥ 3`, `0 ≤ s` (gives `0 ≤ t`) | all pin hypotheses; pin 5s used only via `ekSameRow_holds` (proved), pin 8 is the one antecedent used | `Prop5Short` antecedent of the pin is not needed in the proof |

### (ii) Concrete nondegenerate instance and numerical check

Ticket instances: `d = 3`, `Λ = 1`, `κ = 1/2`, `L = 5`, `g = 1/2`, `s = 995/1000`, `t = 999/1000`, `m = i`, `Im m = 1 ≥ κ`.
(1) `n = 2`, `σ = ![true,false]`, `I_diff = {0,1}`, `A = univ`, `𝒜 = δ₀`. (2) `n = 3`, `σ = ![true,true,false]`, `I_diff = {1,2}`, `A = {1,2}` (index 0 same-sign).
Exact `Θ` on `Z_L³` (`SB` = circulant of `sbKernel`, `Θ = (1 - ξ SB)⁻¹`, `Θ̊ = Proj Θ`), computed by FFT (circulant) and cross-checked against dense linear algebra.
Scripts (scratch, no Lean): `scratchpad/T2035/pf1.py`, `pf2.py`, `pf3.py`.

Command 1: `python3 pf1.py` (one-index norms; max over `g ∈ {.1,.5}`, `t ∈ {s,(1+s)/2}`, `m ∈ {i, e^{.3i}}` (`Im = .2955`), all sign pairs, `s = 1-g²/L²`):
```
dense vs FFT (L=5,g=.5,mu=1,s=.995,t=.999) [||Proj uKer||dense, FFT, ||uKer|| dense, FFT]: [1.992687, 1.992687, 5.0, 5.0]
  L | same-sign ||uKer|| | diff-sign ||Proj uKer|| | same-sign ||Proj uKer|| | max (1-s)L^2/(g^2+|1-t|)
  5 | 1.0128 | 1.9947 | 1.9866 | 0.9804
  7 | 1.0067 | 2.0003 | 1.9956 | 0.9899
  9 | 1.0041 | 2.0012 | 1.9981 | 0.9939
 15 | 1.0015 | 2.0021 | 1.9998 | 0.9978
 21 | 1.0008 | 2.0022 | 2.0000 | 0.9989
```
(Without `Proj` the same data give `‖uKer‖ = 5.0` at `L=5`: `Proj` is what removes the `(1-s)/(1-t)` growth.)

Command 2: `python3 pf2.py` (tensor `n`-fold, `d=3`, all `σ ∈ {±}^n`, `A ∈ {I_diff, univ}`, `g,t,m` as above; `𝒜 = δ₀` and one random `𝒜`, `‖𝒜‖ = 1`):
```
 L n | max prod||K_i|| (=sup_A ratio) | max ratio A=delta_0 | max ratio random A | #configs
 5 2 |   3.9790 |   1.0023 |   1.0115 | 64
 7 2 |   4.0011 |   1.0012 |   1.0053 | 64
 9 2 |   4.0047 |   1.0012 |   1.0143 | 64
 5 3 |   7.9048 |   1.0035 |   1.0035 | 128
```
(`n = 3` only at `L = 5`: `L = 7, 9` arrays of `343³`, `729³` entries were not run; row 1 of the table gives the exact `∏` for any `n`.)

Command 3: `python3 pf3.py` (external hypotheses at concrete data; `κ = sin .3`, `Λ = 1`, `g ∈ {.1,.5,1}`, `t ∈ {0,.5,.9,.99,.999,1-1e-6}`, both `m`, all sign pairs):
```
lattice sum S_L=sum_b (|b|_1+1)^{-1} (k=1, d=3) and S_L/L^2; merged bound constant exp(sqrt3)*2^3*radC(1)=1.043e+06
  L= 5  S_L=   30.343  S_L/L^2=1.2137
  L= 9  S_L=  107.250  S_L/L^2=1.3241
  L=21  S_L=  635.445  S_L/L^2=1.4409
  L=31  S_L= 1419.381  S_L/L^2=1.4770
  L   C8_est=max (g2+|1-t|)(|a|+1)|Th0_t(0,a)|   C5s_est=max |Th(0,a)|/(delta_a0+g2 e^{-c|a|}), c=.3
   5     1.9840     3.8129
   9     1.9973     3.8129
  15     1.9994     3.8129
  21     1.9998     3.8129
  31     1.9999     3.8129
window arithmetic: ... max = 0.9988674971692975 (<=1 needed)
instance: 1-g2/L2=0.9900 <= s=0.995 <= t=0.999 < 1: True ; Im(i)=1 >= kappa=.5: True; (t-s)(g2+|1-t|)^-1 L2 = 0.3984
  n=2 sigma=(True, False) sign-change set I_diff = [0, 1]
  n=3 sigma=(True, True, False) sign-change set I_diff = [1, 2]
```
(The table above is the lines of the script output for `L ∈ {5,9,21,31}` of the lattice sum; the script also prints `L = 7, 15`.)
Concrete limit computation for the external hypotheses: `C_8,est` stabilises at `≈ 2` (≤ `1.9999`) as `L` grows 5 → 31 and `C_5s,est = 3.8129` is constant in `L`,
so `Prop8ZeroMode` / `Prop5Short` hold with finite `L`-independent constants at `d = 3` on the tested grid (a numerical check at tested data, not a proof).
Hypotheses of the pin at the ticket instance: `3 ≤ 3`, `2 ≤ n`, `0 < 1`, `0 < 1/2`, `L = 5 ≥ 3`, `0 < 1/2 ≤ 1`, `0 ≤ .995`, `.99 ≤ .995 ≤ .999 < 1`, `‖i‖ = 1`, `1/2 ≤ 1`,
`A ⊇ I_diff`: all hold with no degenerate data (`N`, `L³ = 125` points, `n`-index tensors of `125^n` entries).

### Verdict

- `ekSumDecayNonzero_holds`: **PASS**. All hypotheses of the pin can hold at once (instances above); the exponents close (rows 2–9: bounded per-index factors, window arithmetic `≤ 1`
  with the exact constant 1, final `C = C_ind^n` with no loss); the statement is consistent with numerics (`∏‖K_i‖ ≈ 2^n`, bounded in `L`).
  The route (copy-adapt `norm_zeroModeSet_UN_le` with `ekSameRow_holds` and `Prop8ZeroMode`) needs no new mathematics.

## (b) Script output — Sat Oct  3 13:05:20 UTC 2026

Branch t/T2035, commit b9a2440 (sole file RBM3D/Evolution/Nonzero.lean, 227 lines).

### Build (worktree /Users/junyin/Lean_proof/RBM3D-wt/T2035)
```
$ lake build RBM3D.Evolution.Nonzero 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
Build completed successfully (3418 jobs).
$ lake build 2>&1 | tail -1   # whole library (root does not yet import the new module; hub adds it at merge)
Build completed successfully (3747 jobs).
```

### Axioms and registry pre-check (DECISIONS §20; scratch file: import RBM3D, import RBM3D.Evolution.Nonzero, #print axioms, #assert_rbm_axioms)
```
$ lake env lean scratch/ax.lean ; echo exit $?
exit 0
'RBM.ekSumDecayNonzero_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.ekDelta0' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: 1570 theorems, 629 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
...
 RBM.Gauss.Sizes.STFlow].
non-vacuity certificates: 4 of 48 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
```
No new Prop-valued definition in the file, so no registry line is needed; `RBM3D/Test/Axioms.lean` is untouched.

### Type of the target against the pin (script)
```
$ cat scratch/ty.lean; lake env lean scratch/ty.lean ; echo exit $?
import RBM3D.Evolution.Nonzero
#check @RBM.ekSumDecayNonzero_holds
example : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecayNonzero d n Λ κ := RBM.ekSumDecayNonzero_holds
RBM.ekSumDecayNonzero_holds : ∀ (d n : ℕ) (Λ κ : ℝ), RBM.EKSumDecayNonzero d n Λ κ
exit 0
```

### Target statement (sed -n 146p of the file) and pin (Pins.lean)
```
theorem ekSumDecayNonzero_holds (d n : ℕ) (Λ κ : ℝ) : EKSumDecayNonzero d n Λ κ := by
128:def EKSumDecayNonzero (d n : ℕ) (Λ κ : ℝ) : Prop :=
129-  Prop5Short d Λ κ → Prop8ZeroMode d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
130-    ∃ C : ℝ, 0 < C ∧
131-      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
132-        ∀ s t : ℝ, 0 ≤ s → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s → s ≤ t → t < 1 →
133-        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : Finset (Fin n),
134-          (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) →
135-          ∀ 𝒜 : (Fin n → Zd d L) → ℂ,
136-            haveI : NeZero L := ⟨by omega⟩
137-            ‖zeroModeSet d L A (UN d L g (EKsgn m σ) s t 𝒜)‖ ≤ C * ‖𝒜‖
138-
139-/-- **Pin `lem:propT`**, `(TTT2)`: `Σ_c 𝒯_u(|a-c|) 𝒯_t(|c-b|) ≤ C_d/(1-u) · 𝒯_t(|a-b|)` for
140-`0 ≤ u ≤ t < 1` with (i) `1-t ≥ g²/L²` or (ii) `1-u ≤ g²/L²`; `C_d` depends on `d` only.  No
```

### Compiled nonempty instances (sed -n 190,225p; both compiled in the build above)
```lean

/-- the point mass `δ₀` on `n`-index tensors -/
noncomputable def ekDelta0 (n d L : ℕ) : (Fin n → Zd d L) → ℂ := fun a => if a = 0 then 1 else 0

/-- `d = 3`, `n = 2`, `Λ = 1`, `κ = 1/2`, `L = 5`, `g = 1/2`, `s = 995/1000 ≥ 1 - g²/L² = 99/100`,
`t = 999/1000`, `m = i`, `σ = (+,-)`, `A = univ`, `𝒜 = δ₀`; both pins are discharged by their proofs. -/
example :
    haveI : NeZero 5 := ⟨by norm_num⟩
    ∃ C : ℝ, 0 < C ∧ ekDelta0 2 3 5 0 ≠ 0 ∧
      ‖zeroModeSet 3 5 (Finset.univ : Finset (Fin 2))
          (UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, false]) (995 / 1000) (999 / 1000)
            (ekDelta0 2 3 5))‖ ≤ C * ‖ekDelta0 2 3 5‖ := by
  obtain ⟨C, hC, H⟩ := ekSumDecayNonzero_holds 3 2 1 (1 / 2) (prop5Short_holds 3 1 (1 / 2))
    (prop8ZeroMode_holds 3 1 (1 / 2)) le_rfl le_rfl one_pos (by norm_num)
  refine ⟨C, hC, by simp [ekDelta0], ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (995 / 1000) (999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by rw [Complex.I_im]; norm_num) ![true, false] Finset.univ (fun i _ => Finset.mem_univ i)
    (ekDelta0 2 3 5)

/-- `n = 3`, `σ = (+,+,-)`, `A = {1, 2}` the two sign-change indices (index `0` is same-sign). -/
example :
    haveI : NeZero 5 := ⟨by norm_num⟩
    ∃ C : ℝ, 0 < C ∧ ekDelta0 3 3 5 0 ≠ 0 ∧
      ‖zeroModeSet 3 5 ({1, 2} : Finset (Fin 3))
          (UN 3 5 (1 / 2 : ℝ) (EKsgn Complex.I ![true, true, false]) (995 / 1000) (999 / 1000)
            (ekDelta0 3 3 5))‖ ≤ C * ‖ekDelta0 3 3 5‖ := by
  obtain ⟨C, hC, H⟩ := ekSumDecayNonzero_holds 3 3 1 (1 / 2) (prop5Short_holds 3 1 (1 / 2))
    (prop8ZeroMode_holds 3 1 (1 / 2)) le_rfl (by norm_num) one_pos (by norm_num)
  refine ⟨C, hC, by simp [ekDelta0], ?_⟩
  exact H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (995 / 1000) (999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by rw [Complex.I_im]; norm_num) ![true, true, false] ({1, 2} : Finset (Fin 3))
    (by decide) (ekDelta0 3 3 5)

end Instances
```

### Name clash and hygiene grep
```
$ grep -rnE "(ekSumDecayNonzero_holds|ekDelta0|ekE_pos|ek_norm_PropSpin|ek_norm_spin_mul|ek_norm_projMat_mul_uKer_le|def ekE)" RBM3D | grep -v Evolution/Nonzero.lean ; echo "exit $?"
exit 
$ grep -nE "sorry|admit|native_decide|axiom" RBM3D/Evolution/Nonzero.lean ; echo exit $?
exit 1
$ git diff --stat main...t/T2035
 RBM3D/Evolution/Nonzero.lean | 227 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 227 insertions(+)
```
Public new names: `ekSumDecayNonzero_holds`, `ekDelta0`; helpers `ekE`, `ekE_pos`, `ek_norm_PropSpin`, `ek_norm_spin_mul`, `ek_norm_projMat_mul_uKer_le` are `private`.

### Ports
Ported from RBM3D itself (merged `RBM3D/Kernel/Evolution.lean:520-683`, last commit on that file ff8d36d): `exists_norm_projMat_mul_uKer_le` (:520-610) -> `ek_norm_projMat_mul_uKer_le`; `norm_zeroModeSet_UN_le` (:629-683) -> `ekSumDecayNonzero_holds`. Same-sign factor: `ekSameRow_holds` (`RBM3D/Evolution/XiPins.lean:357`, EK-2, last commit 3dc4f1c), used unchanged. Nothing was copied from RBM1D or RBM2D, so no RBM1D/RBM2D diff-stat applies.

### Narrative
- The proof is the structure of `norm_zeroModeSet_UN_le`: `UN_eq_tensorKer` + `zeroModeSet_tensorKer` turn `Q^(A) U` into `tensorKer` of per-index kernels; `norm_tensorKer_le` gives `(∏_i ‖K_i‖) ‖𝒜‖`.
- Index `i ∈ A`: `Proj * uKer = Proj + (t-s) μ SB Θ̊` (`projMat_mul_SB_comm`, `projMat_mul_Theta`); `‖Θ̊‖ ≤ Σ_b |Θ̊(0,b)|` by translation invariance; pin 8 (`h8`, antecedent of the pin) and `sum_radial_pow_le` give `C₀ (g²+|1-t|)⁻¹ E L²`; `(t-s)(g²+|1-t|)⁻¹ L² ≤ (1-s)L²/g² ≤ 1` from `1 - g²/L² ≤ s ≤ t`; so the factor is at most `2 + C₀ E`, with `E = e^{√(k+2)} 2^{k+2} radC 1` (`k = d-2`).
- Index `i ∉ A`: contrapositive of `A ⊇ I_diff` gives `σ i = σ (finRotate n i)`, hence `cycProd (EKsgn m σ) i = PropSpin m (σ i)^2`, bounded by `Cs` from `ekSameRow_holds`.
- Constant `C = (max Cs (2 + C₀ E))^n` depends on `(d, n, Λ, κ)` only; no `L^{nτ}`. The hypothesis `Prop5Short` of the pin is not used in the proof (consistent with preflight row 10). `Prop8ZeroMode` is used as the pin states it (antecedent); it is proved by `prop8ZeroMode_holds`, which the instances apply.
- The pin is true as written; no deviation, no new hypothesis, no weakening.

## (c) Verified Mathlib names used (all compiled in this build)
`Real.exp_pos`, `Real.sqrt`, `Real.exp`, `Complex.norm_I`, `Complex.I_im`, `Complex.ofReal_sub`, `Complex.norm_real`, `Real.norm_of_nonneg`, `norm_smul_le`, `norm_mul_le`, `norm_add_le`, `inv_anti₀`, `le_div_iff₀`, `div_le_one`, `Finset.prod_le_prod₀`, `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin`, `Finset.sum_le_sum`, `Finset.mul_sum`, `Matrix.mul_add`, `Matrix.mul_smul`, `Matrix.mul_assoc`, `pow_pos`, `lt_of_lt_of_le`, `le_max_left`, `le_max_right`. Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (T2016e, T2016f of DECISIONS §18 cover the loss-free reading of `≺` and the pin-8 route; not re-proposed).
- No open issues. The first `example` uses `A = univ` and `σ = (+,-)`, the second `σ = (+,+,-)`, `A = {1,2}` (index 0 same-sign); `𝒜 = δ₀` (`ekDelta0 _ 3 5 0 ≠ 0` is part of the statement), both at `d=3, L=5, g=1/2, s=995/1000, t=999/1000, m=i, Λ=1, κ=1/2`; the conclusion is existential in `C` (the theorem gives `C` abstractly).
