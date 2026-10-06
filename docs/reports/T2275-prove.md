Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 09:09:43 UTC 2026

Notation: `N = Nsz sz n = (W L)^d`, `η₁ = N^{-1+τ'}`, `z₀ = E + i/N`, `z₁ = E + iη₁`, `C` = upper constant of `UNDens` (`Pins.lean:462-465`), `Bctl n (1-η) = (W^d)⁻¹ Bparam d L lam (1-η) 0` (`Sizes.lean:214`, `Params.lean:36`).

### (i) Exponent table

| quantity | value / choice | constraint (source) | slack |
|---|---|---|---|
| `d` | any `d ≥ 3`; instance `d = 3` | used only as `0 < d` in `W_rpow_le` (`Sizes.lean:220`); also `Bparam`'s `(0+1)^(d-2) = 1` for every `d` | none needed |
| `𝔠` | `1/6` | `0 < 𝔠` (`Admissible`, `Sizes.lean:177`); not used by targets 1-6 | `W ≥ N^𝔠`: `11.31 ≤ 32` at `n=0` |
| `𝔡` | `1/10` | `0 < 𝔡` (`hA.2.1`): gives `W^{-2𝔡} ≤ 1` (`W ≥ 1`); target 4 itself needs no sign of `𝔡` | `W^{-2𝔡} = 0.5` at `n=0` |
| `(eq:WO)` lower | `W^{-d/2+𝔡} ≤ lam` (`Sizes.lean:164`) | gives `lam² W^d ≥ W^{2𝔡} > 0` (`lam_sq_mul_pow_ge`, `:193`), hence `lam ≠ 0` and `(W^d)⁻¹(lam²+η)⁻¹ ≤ (lam² W^d)⁻¹ ≤ W^{-2𝔡}` | `n=0`: `32^{-7/5} = 2^{-7} ≤ 1/64`, factor 2 |
| `τ'` | `min(ε/(4(p+1)), 1/2)`, `ε > 0`, `p ∈ ℕ` | (1) `τ' > 0`; (2) `τ' ≤ 1/2` so `η₁ ≤ 1` (`N ≥ 1`), inside `UNTrLocal`'s window `N^{-1+τ'} ≤ Im z ≤ 1` (`Pins.lean:449`) and `η₁ ≤ 10` for `UNDens`; (3) `2pτ' ≤ ε/2` | `ε/2 - 2pτ' ≥ ε/(2(p+1)) > 0` (since `2pτ' ≤ pε/(2(p+1))`) |
| `D` (of `UNTrLocal`) | `p + 1`, at `ε = τ = τ'` | `N^p · N^{-(p+1)} = N⁻¹ ≤ 1` | `1 - N⁻¹` |
| `Bctl n (1-η₁)` | `≤ W^{-2𝔡} + (N η₁)⁻¹ = W^{-2𝔡} + N^{-τ'} ≤ 2` | `|1-(1-η)| = η`; `(W^d)⁻¹(L^d η)⁻¹ = (Nη)⁻¹` as `size = (W L)^d = W^d L^d` (`Sizes.lean:157`); `W^{-2𝔡} ≤ 1`, `N^{-τ'} ≤ 1` | `≥ 0` each; table (ii): `0.527` vs `0.9026` vs `2` |
| `W^{τ'}` | `≤ N^{τ'/d} ≤ N^{τ'}` | `W_rpow_le`; `N ≥ 1`, `d ≥ 1` | `N^{τ'(1-1/d)}` |
| good-event size | `Im m_N(z₁) ≤ C + 2N^{τ'}`; `Im m_N(z₀) ≤ (η₁/η₀) Im m_N(z₁) = N^{τ'}(C+2N^{τ'}) ≤ (C+2)N^{2τ'}` | `η₀ = N⁻¹ ≤ η₁`; `η Im m(E+iη)` nondecreasing (`InjSum.lean:203`); `N^{τ'} ≤ N^{2τ'}` | `N^{2τ'} - N^{τ'}` |
| bad event | `μ(B) ≤ N^{-(p+1)}`; on `B`: `Im m(z₀) ≤ 1/η₀ = N` (`InjSum.lean:196`) | `F^p ≤ c + N^p 1_{B'}`, `B' = toMeasurable B` | `E[F^p] ≤ c + N⁻¹` |
| final | `c = ((C+2)N^{2τ'})^p ≤ (C+2)^p N^{ε/2}`; `E F^p ≤ (C+2)^p N^{ε/2} + 1 ≤ ((C+2)^p+1) N^{ε/2} ≤ N^{ε}` | needs `N^{ε/2} ≥ 1` and eventually `(C+2)^p + 1 ≤ N^{ε/2}` (`N → ∞`, `sz.SizeTendsto`) | eventual; fails at `n=0` for `p=2, ε=1/4` (`10 > 6.17`), true from `n=1` |
| `UNApriori` conclusion | `E F^p ≤ N^ε`, `F = Im m_N(E+iN⁻¹)` under `ouP` | `ouMat M n 0 ω = M.H n ω.1` (`Pins.lean:160`), `ouP = M.μ.prod gueP` (`:145`), both probability measures: `∫ g(ouMat..) ∂ouP = ∫ g(M.H n ·) ∂M.μ` (no measurability of `g`) | n/a |
| band row | `δ ≤ κ/2`, `0 < δ` | `UNDensBandRow` (`:826-828`) gives `δ ≤ κ/2` and `UNDens` (so `0 < δ` from `.1`); `UNTrLocalBandRow` (`:842-845`) needs exactly `0 < δ`, `δ ≤ κ/2`, `|E| ≤ 2-κ` | `κ = 1/2, E = 1`: `1 ≤ 3/2` |

Checks of the table, read from the files: `Bparam d L g t K = (g²+|1-t|)⁻¹ * ((K+1)^(d-2))⁻¹ + (L^d |1-t|)⁻¹` (`Params.lean:36`); `UNTrLocal` event is `∃ z, |z.re-E| ≤ δ ∧ N^{-1+ε} ≤ z.im ∧ z.im ≤ 1 ∧ W^τ Bctl n (1-z.im) < ‖stieltjesN (M.H n ω) z - m n z‖` with bound `ofReal (N^{-D})` (`Pins.lean:447-451`); `UNApriori`: `∀ p : ℕ, ∀ ε > 0, ∀ᶠ n, ∫ (Im stieltjesN (ouMat M n 0 ω) (E + N⁻¹ I))^p ∂ouP ≤ N^ε` (`:522-525`). Lower half of `(eq:WO)` is used (first `Bctl` term); upper half and `Bandwidth` are not. A non-integrable left side has Bochner integral `0 ≤ N^ε`, and `integral_mono_of_nonneg` needs only integrability of the majorant `c + N^p 1_{B'}` on a probability space.

### (ii) One concrete nondegenerate instance

Data: `sz0` (`SizesInst.sz0`, `Sizes.lean:260`), `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `n = 0`: `L = 4, W = 32, lam = 1/64, N = 2^21` (`sz0_values`, `:267`); band model `M = UNModel.band sz0`, `m = msc`, `E = 0`, `δ = 1/2`, `ρ = ρ_sc(0)`; `UNDens` holds with `c = 9/100, C = 1` (`un_dens_msc_zero`, `Pins.lean:1455`). `sz0.Admissible (1/6)(1/10)` is `sz0_admissible` (`:331`). Hypothesis `UNTrLocal sz0 band msc 0 (1/2)` is the owed external pin; its only use is the eventual event bound, and every deterministic inequality around it is checked below at the concrete numbers (`Bctl` is computed from the definition `(W^d)⁻¹((lam²+η)⁻¹ + (L^d η)⁻¹)`).

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2275/pf2.py`
(source: `d,dd,cc,C=3,0.1,1/6,1.0`; `sz0(n)` returns `L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^{-6}, N=(WL)^3`; `bctl(n,eta)=(W^d)^-1*((lam^2+eta)^-1+(L^d*eta)^-1)`; `row(n,p,eps)` computes `tau, eta1=N^(-1+tau), WO, Bctl<=W^-2dd+(N eta1)^-1<=2, W^tau<=N^(tau/d)<=N^tau, im0=N^tau(C+W^tau Bctl)<=(C+2)N^(2tau), 2p tau<=eps/2, (C+2)^p+1<=N^(eps/2), tot=((C+2)N^(2tau))^p+N^p N^-(p+1)<=N^eps`)

```
n=0: L,W,lam,N = (4, 32, 0.015625, 2097152)
p=1 eps=0.5 {'WO': True, 'tau': 0.0625, 'Bctl': 0.527, 'bnd': 0.9026, 'B_ok': True, 'W_N': True, 'im0': 4.109, 'cap': 18.507, 'im0_ok': True, 'exp_ok': True, 'thr': True, 'tot': 18.507, 'NE': 1448.155, 'fin': True}
p=2 eps=0.5 {'WO': True, 'tau': 0.0417, 'Bctl': 0.6698, 'bnd': 1.0453, 'B_ok': True, 'W_N': True, 'im0': 3.253, 'cap': 10.091, 'im0_ok': True, 'exp_ok': True, 'thr': True, 'tot': 101.823, 'NE': 1448.155, 'fin': True}
p=4 eps=1.0 {'WO': True, 'tau': 0.05, 'Bctl': 0.6075, 'bnd': 0.983, 'B_ok': True, 'W_N': True, 'im0': 3.566, 'cap': 12.861, 'im0_ok': True, 'exp_ok': True, 'thr': True, 'tot': 27361.316, 'NE': 2097152.0, 'fin': True}
p=2 eps=0.25 {'WO': True, 'tau': 0.0208, 'Bctl': 0.8631, 'bnd': 1.2384, 'B_ok': True, 'W_N': True, 'im0': 2.611, 'cap': 5.502, 'im0_ok': True, 'exp_ok': True, 'thr': False, 'tot': 30.272, 'NE': 38.055, 'fin': True}
p=2 eps=1/4: least n with every inequality true: 1 ; true for all n in [n0,20000]: True
n= 0 log10 N= 6.32 N^(1/8)= 6.169
n= 1 log10 N= 11.74 N^(1/8)= 29.34
n= 10 log10 N= 25.07 N^(1/8)= 1359
n= 1000 log10 N= 60.33 N^(1/8)= 3.477e+07
n= 1000000 log10 N= 114.32 N^(1/8)= 1.951e+14
WO at all n<=20000: True
```

Limit computation for the eventual and external parts: `N(n) = ((2(n+1))^5 · 4(n+1))^3 → ∞` (table above), so `N^{ε/2} → ∞` and `(C+2)^p + 1 = 10 ≤ N^{1/8}` holds for every `n ≥ 1` at `(p, ε) = (2, 1/4)` (the `thr: False` row at `n = 0` is the only failure, and is why that inequality sits inside `∀ᶠ n`); `lam = (2(n+1))^{-6} → 0` and `WO` holds at every `n ≤ 20000` (`W^{-7/5} = (2(n+1))^{-7} ≤ (2(n+1))^{-6}` for all `n`). `UNTrLocal` is a hypothesis of the instance and of target 5, never derived here.

Other instances (hand-checked, same hypotheses as the check file 2.7): target 2 at `H = 0 : Matrix (Fin 1) (Fin 1) ℂ`, `E = 0`, `η₀ = 1/2`, `η₁ = 1`, `w = m(i)`, `ζ = 0`: `Gres 0 z true = Ring.inverse (0 - z • 1)` (`Loop/GLoopFlow.lean:74`), so `m(iη) = (-iη)⁻¹`, `Im = 1/η`: `Im m(i/2) = 2 ≤ (1/(1/2))(Im m(i) + 0) = 2` (equality case; `‖w-w‖ = 0 ≤ 0`). Target 4 at `sz0`, `n = 0`, `𝔡 = 1/10`, `η = 1/2`: premise `32^{-7/5} = 2^{-7} ≤ 1/64`; `Bctl 0 (1/2) = (32^3)⁻¹ ((1/64² + 1/2)⁻¹ + (64/2)⁻¹) = 6.196e-5 ≤ 32^{-1/5} + (2^21/2)⁻¹ = 0.5000010` (`python3 -c` on the definitions; `L^d = 64`).

### Verdict

- Target 1 `apriori_im_bounds`: PASS (`0 ≤ Im m ≤ 1/η` for nonempty Hermitian index; `Im m = N⁻¹ Σ η/((λ-E)²+η²)`, `InjSum.lean:196`; nonempty since `card_Idx = N ≥ 1`).
- Target 2 `apriori_im_le_of_near`: PASS (`η₀ Im m(η₀) ≤ η₁ Im m(η₁) ≤ η₁(Im w + ζ)`; no `Meta`, no nonempty hypothesis needed).
- Target 3 `apriori_ouMat_zero_integral`: PASS (`ouMat_zero`, first marginal of a product of probability measures, no measurability).
- Target 4 `apriori_bctl_le`: PASS (`Bctl n (1-η) ≤ W^{-2𝔡} + (Nη)⁻¹` under `W^{-d/2+𝔡} ≤ lam n`, `η > 0`, no sign condition on `𝔡`; `lam² W^d ≥ W^{2𝔡} > 0` gives `lam² > 0`).
- Target 5 `unApriori_of_trLocal`: PASS (exponents close with slack `ε/(2(p+1))`; the `Bctl ≤ 2` step uses `Admissible`'s `WO` half; `UNTrLocal` is a hypothesis).
- Target 6 `unApriori_band_of_rows`: PASS (`δ` from `UNDensBandRow`, `0 < δ` from `UNDens`, `UNTrLocalBandRow` premises `0 < δ ≤ κ/2` match).
- Instances (a)-(d) of check 2.7: PASS (every deterministic hypothesis discharged at `sz0`; owed pins `UNTrLocal` / the three band rows stay hypotheses).
- No FAIL or BLOCKED; no statement of the check file needs a successor.

## (b) Script output — Tue Oct  6 09:19 UTC 2026 (all commands run in `/Users/junyin/Lean_proof/RBM3D-wt/T2275`, branch `t/T2275`)

Commit: `c05917a` (`git diff --stat main...t/T2275`):
```
 RBM3D/Test/Axioms.lean          |   1 -
 RBM3D/Universality/Apriori.lean | 407 ++++++++++++++++++++++++++++++++++++++++
 2 files changed, 407 insertions(+), 1 deletion(-)
```
Registry diff (`git diff main...t/T2275 -- RBM3D/Test/Axioms.lean | grep '^[-+]'`):
```
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNApriori, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```

### Build (`lake build RBM3D.Universality.Apriori 2>&1 | tail -2`)
```
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3334 jobs).
```

### Axioms (`#print axioms`, scratch file importing `RBM3D.Universality.Apriori`)
```
'RBM.Univ.apriori_im_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.apriori_im_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.apriori_ouMat_zero_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.apriori_bctl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unApriori_of_trLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unApriori_band_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_unApriori_band_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_unApriori_band_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_im_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_bctl_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_im_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.AprioriInst.inst_ouMat_zero_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Target statements (extracted by script from `RBM3D/Universality/Apriori.lean`)
```lean
theorem apriori_im_bounds {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) :
    0 ≤ (stieltjesN H ((E : ℂ) + (η : ℂ) * Complex.I)).im ∧
      (stieltjesN H ((E : ℂ) + (η : ℂ) * Complex.I)).im ≤ 1 / η :=

theorem apriori_im_le_of_near {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (E η₀ η₁ : ℝ) (w : ℂ) (ζ : ℝ) (h0 : 0 < η₀) (h01 : η₀ ≤ η₁)
    (hnear : ‖stieltjesN H ((E : ℂ) + (η₁ : ℂ) * Complex.I) - w‖ ≤ ζ) :
    (stieltjesN H ((E : ℂ) + (η₀ : ℂ) * Complex.I)).im ≤ η₁ / η₀ * (w.im + ζ) :=

theorem apriori_ouMat_zero_integral {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ)
    (g : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ) :
    ∫ ω, g (ouMat M n 0 ω) ∂(ouP M n) = ∫ ω, g (M.H n ω) ∂M.μ :=

theorem apriori_bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) (𝔡 η : ℝ) (hη : 0 < η)
    (hwo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) :
    sz.Bctl n (1 - η) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) + (Nsz sz n * η)⁻¹ :=

theorem unApriori_of_trLocal (d : ℕ) (hd : 3 ≤ d) (𝔠 𝔡 : ℝ) (sz : Sizes d)
    (hA : sz.Admissible 𝔠 𝔡) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ)
    (hD : UNDens m E ρ δ) (hT : UNTrLocal sz M m E δ) : UNApriori sz M E :=

theorem unApriori_band_of_rows (hT : UNTrLocalBandRow) (hD : UNDensBandRow) (hL : UNLocAvgBand)
    (d : ℕ) (hd : 3 ≤ d) (𝔠 𝔡 : ℝ) (sz : Sizes d) (hA : sz.Admissible 𝔠 𝔡) (κ : ℝ) (hκ : 0 < κ)
    (E : ℝ) (hE : |E| ≤ 2 - κ) : UNApriori sz (UNModel.band sz) E :=

theorem inst_unApriori_band_zero :
    UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
      UNApriori sz0 (UNModel.band sz0) 0 :=

theorem inst_unApriori_band_one :
    UNTrLocalBandRow → UNDensBandRow → UNLocAvgBand → UNApriori sz0 (UNModel.band sz0) 1 :=

theorem inst_im_le_of_near :
    (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ) (((0 : ℝ) : ℂ) + (((1 / 2 : ℝ)) : ℂ) * Complex.I)).im ≤
      1 / (1 / 2) * ((stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im + 0) :=

theorem inst_bctl_le :
    sz0.Bctl 0 (1 - 1 / 2) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 10 : ℝ))) + (Nsz sz0 0 * (1 / 2))⁻¹ :=

theorem inst_im_bounds :
    0 ≤ (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im ∧
      (stieltjesN (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im ≤ 1 / 1 :=

theorem inst_ouMat_zero_integral :
    ∫ ω, (fun _ => (1 : ℝ)) (ouMat (UNModel.band sz0) 0 0 ω) ∂(ouP (UNModel.band sz0) 0) =
      ∫ ω, (fun _ => (1 : ℝ)) ((UNModel.band sz0).H 0 ω) ∂(UNModel.band sz0).μ :=

```

### Compiled instances and statement match
Instances are the theorems `RBM.Univ.AprioriInst.inst_*` of the same file (statements above): `inst_unApriori_band_zero` (target 5 at `sz0`, `UNInst.sz0_adm`, band, `msc`, `E = 0`, `δ = 1/2`, `un_dens_msc_zero`; `UNTrLocal` kept as hypothesis), `inst_unApriori_band_one` (target 6 at `sz0`, `κ = 1/2`, `E = 1`; the three owed band rows kept), `inst_im_le_of_near` (target 2 at `H = 0 : Matrix (Fin 1) (Fin 1) ℂ`, `ζ = 0`, equality case), `inst_bctl_le` (target 4 at `sz0`, `n = 0`, `𝔡 = 1/10`, `η = 1/2`, `WO` premise from `sz0_values`), plus `inst_im_bounds` (target 1 at the `1×1` zero matrix) and `inst_ouMat_zero_integral` (target 3 at `sz0`, band, `n = 0`, `g ≡ 1`).

Scratch check = the ticket check file with `import RBM3D.Universality.Apriori` and these lines appended (`lake env lean $S/check.lean`, exit 0, 0 `error` lines):
```
189:example : T2275_apriori_im_bounds := @apriori_im_bounds
191:example : T2275_apriori_im_le_of_near := @apriori_im_le_of_near
193:example : T2275_apriori_ouMat_zero_integral := @apriori_ouMat_zero_integral
195:example : T2275_apriori_bctl_le := @apriori_bctl_le
197:example : T2275_unApriori_of_trLocal := @unApriori_of_trLocal
199:example : T2275_unApriori_band_of_rows := @unApriori_band_of_rows
200:example : T2275_inst_unApriori_band_zero := AprioriInst.inst_unApriori_band_zero
201:example : T2275_inst_unApriori_band_one := AprioriInst.inst_unApriori_band_one
202:example : T2275_inst_im_le_of_near := AprioriInst.inst_im_le_of_near
203:example : T2275_inst_bctl_le := AprioriInst.inst_bctl_le
```

### Registry pre-check (`import RBM3D` + `import RBM3D.Universality.Apriori` + `#assert_rbm_axioms`, after `lake build RBM3D.Test.Axioms`; exit 0)
```
axiom audit: 7994 theorems, 2619 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
premises found by scanning: 153 (borrowed 1, owed 95, structural 40, refuted 6, superseded 11).
registry: 2 borrowed + 148 owed + 103 structural + 7 refuted + 12 superseded; 119 registered premise(s) carry nothing ye
```
Owed count 149 -> 148 (the first pre-check run before rebuilding `RBM3D.Test.Axioms` gave 149 and still listed `UNApriori`: stale olean). No "unregistered premise" message; `grep UNApriori` in the output: 0 hits.

### Full `lake build`
Without the root import: `RBM3D.lean:318: axiom audit: 1 premise(s) ... in none of the ledgers: [RBM.Univ.UNApriori]` (expected: the root does not import the new file; the hub adds the import at merge). With `import RBM3D.Universality.Apriori` temporarily inserted after the last import of `RBM3D.lean` (reverted, not committed): `Build completed successfully (4082 jobs).` (root `#assert_rbm_axioms` passes; `git status --short` after revert: `M RBM3D/Test/Axioms.lean`, `?? RBM3D/Universality/Apriori.lean`, before the commit).

### Name-clash grep (`grep -rnw --include=*.lean <name> RBM3D RBM3D.lean`, excluding the new file)
```
apriori_im_bounds:        0 hits outside the new file
apriori_im_le_of_near:        0 hits outside the new file
apriori_ouMat_zero_integral:        0 hits outside the new file
apriori_bctl_le:        0 hits outside the new file
unApriori_of_trLocal:        0 hits outside the new file
unApriori_band_of_rows:        0 hits outside the new file
AprioriInst:        0 hits outside the new file
inst_unApriori_band_zero:        0 hits outside the new file
inst_unApriori_band_one:        0 hits outside the new file
inst_im_le_of_near:        0 hits outside the new file
inst_bctl_le:        0 hits outside the new file
inst_im_bounds:        0 hits outside the new file
inst_ouMat_zero_integral:        0 hits outside the new file
```
`grep -rn Apriori_` outside the new file: 0 hits (no private helper was needed). `docs/tickets/`: hits only in `T2275.md` and `checks/T2275-check.lean`. `sorry|admit|native_decide|^axiom` in the file: 0 hits.

### Port (RBM2D read-only)
Source: `git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/Apriori.lean` (424 lines). RBM2D HEAD is `9e0f275`; `git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/Apriori.lean` output:
```
 RBM2D/Universality/Apriori.lean | 59 +++++------------------------------------
 1 file changed, 6 insertions(+), 53 deletions(-)
(the RBM2D file differs between `c9a24cf` and HEAD; this port reads `c9a24cf` as the ticket says)
```
Map (RBM2D line -> here): `:32` `apriori_im_bounds` -> target 1 (public, `Type`); `:51` `apriori_ratio_le_one` -> dropped, replaced by target 4; `:112-149` measurability helpers -> dropped; `:153` `apriori_transfer` -> target 3 (`ouMat_zero`, `integral_fun_fst`); `:179` `apriori_F_bounds` -> inside target 5 (`hFb`, target 1 at `η = N⁻¹`); `:192` `apriori_good_bound` -> target 2 + `Bctl`/`W_rpow_le` steps in target 5; `:270` `aprioriRow` -> target 5; `:380-422` `AprioriCheck` -> `AprioriInst`.

### Narrative
- Stage 1b ran as `prover`, claude-sonnet-5-5; section (a) was not edited; no `(a')` section is needed (every deterministic inequality of (a) was used as stated; the `Bctl <= 2` step uses `Admissible.2.2.2.2 = WO` and `0 < 𝔡` as in (a)).
- The six targets are public as spelled in the ticket; the file has no private helper; statements equal the check file (all ten `example : T2275_<name> := ...` lines elaborate).
- Target 5 follows RBM2D `aprioriRow`: `tau = min (eps/(4(p+1))) (1/2)`, `D = p+1`, bad set `B'` = `toMeasurable` of the `UNTrLocal` event, `F^p <= c + N^p 1_{B'}` pointwise, `integral_mono_of_nonneg` (no measurability of `F`), `c = ((C+2) N^(2 tau))^p <= (C+2)^p N^(eps/2)`; the one eventual threshold is the conjunction `UNTrLocal` at `(tau,tau,p+1)`, `UNDens`, `WO`, `(C+2)^p+1 <= N^(eps/2)`, `1 <= N`.
- `UNTrLocal` (owed registry line kept) is a hypothesis of targets 5, 6 and of instances (a), (b); it is not proved here. `UNDensBandRow`, `UNTrLocalBandRow`, `UNLocAvgBand` stay hypotheses of target 6 and instance (b). `UNUnivMainRow` (UN-24) and the BA data are not touched.
- Not targets, not touched: any merged file other than the one registry line; refuted/superseded pins (`UNTrLocalInit` is not used).
- Registry: exactly one deletion (`UNApriori`), per the ticket; the pre-check flagged no further premise, so no line was added.
- `3 <= d` is used only as `0 < d` (`Sizes.W_rpow_le`); `d` enters through `Idx d`, `N = (W L)^d`, `Bctl`.
- `maxHeartbeats` is not raised in the committed file (the first draft of target 5 hit the default limit; four `nlinarith` calls, profiled at 0.9-2.5 s each, were replaced by `linarith` and explicit `mul_le_mul_of_nonneg_left`).

## (c) Verified Mathlib names (all compiled in `Apriori.lean`; the release check file `#check`s `integral_fun_fst`, `integral_mono_of_nonneg`, `measure_toMeasurable`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `tendsto_rpow_atTop`)
`MeasureTheory.integral_fun_fst` (`Integral/Prod.lean:548`, `ν.real univ • ∫`), `MeasureTheory.integral_mono_of_nonneg`, `MeasureTheory.measure_toMeasurable`, `MeasureTheory.integral_indicator_one`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `tendsto_rpow_atTop`, `Nat.one_le_cast`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `div_le_iff₀`, `le_div_iff₀`, `Set.indicator_of_notMem`, `ENNReal.toReal_ofReal`, `Matrix.isHermitian_zero`, `Complex.im_le_norm`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- **T2275a (design, no paper statement)**: (1) `UNApriori` is proved for every `M : UNModel sz` from `UNDens` + `UNTrLocal` at admissible sizes (RBM2D proved only the band row from `locSC`); the owed registry line is deleted (DECISIONS §90); the content stays owed in `UNTrLocal`. (2) The RBM2D `Meta` ratio `W^tau/sqrt(Meta) <= 1` is replaced by `W^tau Bctl n (1 - N^(-1+tau)) <= 2 N^tau`, which uses the lower half of `(eq:WO)` (target 4); without `(eq:WO)` the first `Bctl` term is only `<= L^d N^(-tau)`.
- No statement difference against the ticket: no T2275c candidate.
- Merge note for the hub: root import `import RBM3D.Universality.Apriori` after the last `import` of `RBM3D.lean` is required (without it the root `#assert_rbm_axioms` reports `UNApriori` as an unclassified premise, see (b)); `Axioms.lean` conflicts only in registry lists (union minus the deleted line).
