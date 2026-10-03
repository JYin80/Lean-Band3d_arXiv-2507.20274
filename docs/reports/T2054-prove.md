Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 14:35:30 UTC 2026

Notation (paper `3_5:918–1000`, Lean pins): `η = η_τ = (1-τ) Im m(E) = (1-τ)√(4-E²)/2` (`GLoopFlow.lean:58`, `Defs/Semicircle.lean:42`); `E_a = W^{-d} P_a`, `P_a` the projection on block `a` (`Eblk`, `GLoop.lean:55`), so `Σ_a E_a = W^{-d} I`; `𝓛^{(m)}_{σ,a} = tr ∏_i G(σ_i) E_{a_i}` (`Lloop`, `GLoopFlow.lean:158`, `STLI` `Step34Pins.lean:107`); `G(±) = (H - z_τ^{(±)})^{-1}`, `G(-) = G(+)^*` (`Gres`, `GLoopFlow.lean:74`), `H = √τ X` Hermitian (`gLoopFlow_seqHflow_isHermitian`, `GLoopFlow.lean:172`); `M_k := STmaxL k = max_{σ,a}|𝓛^{(k)}|` (`Step34Pins.lean:51`). Target: `STContract d` (`Step34Pins.lean:307`), part (1) and part (2); no external hypothesis, no randomness (every `ω`, every Hermitian `H`).

### (i) Exponent table
Proof, both parts, in the paper's notation (`X_k` := `G_1E_1⋯G_{k-1}E_{k-1}G_k`, `P_k = W^d E_k`):
- (P1) `𝓛^{(m)} = tr(E_m X E_k Y)`, `X = X_k`, `Y = G_{k+1}E_{k+1}⋯G_m`. With `E = W^{-d}P`: `𝓛^{(m)} = W^{-2d} tr[(P_mXP_k)(P_kYP_m)]`, so Hilbert–Schmidt Cauchy–Schwarz gives `|𝓛^{(m)}_{σ,a}| ≤ (𝓛^{(2k)}_{σ1,a1} 𝓛^{(2m-2k)}_{σ2,a2})^{1/2}` (`eq:CS1`, `3_5:936`), `𝓛^{(2k)}_{σ1,a1} = tr(E_m X E_k X^*) ≥ 0`, `𝓛^{(2m-2k)}_{σ2,a2} = tr(E_k Y E_m Y^*) ≥ 0` (`σ1,a1,σ2,a2` as in the paper).
- (P2) CS over `a_m`: `Σ_{a_m}|𝓛^{(m)}| ≤ (Σ 𝓛^{(2k)}_{σ1})^{1/2}(Σ 𝓛^{(2m-2k)}_{σ2})^{1/2}` (`eq;genWard0`).
- (P3) Ward `G(+)G(-) = (G(+)-G(-))/(2iη)` (from `G(+)-G(-) = (z-z̄)G(+)G(-)`, `Im z = η`), and `Σ_{a_m}E_{a_m} = W^{-d}I`, give `Σ_{a_m}𝓛^{(2k)}_{σ1,a1} = (𝓛^{(2k-1)}_{σ^+} - 𝓛^{(2k-1)}_{σ^-})/(2iW^dη)`, modulus `≤ M_{2k-1}/(W^dη)`; same for `2m-2k` (`eq;genWard1`). Product of square roots: `(W^dη)^{-1}(M_{2k-1}M_{2m-2k-1})^{1/2}`. This is the only place `W^dη` enters in part (1).
- (P4) Part (2): `𝓛^{(m)} = W^{-3d}Σ_{x_k,x_l,x_m}C^{(k)}_{x_mx_k}C^{(l-k)}_{x_kx_l}C^{(m-l)}_{x_lx_m}` (`C` = `defC=GEG`, `3_5:970`, `C` carries its own inner `E`'s). `|Σ_{x_k,x_l}u A v| ≤ ‖u‖‖A‖‖v‖` gives `eq:Apsipsi`; `‖A‖ ≤ tr[(AA^*)^p]^{1/(2p)}` and `W^{-2pd}tr[(AA^*)^p] = 𝓛^{(2(l-k)p)}_{σ,b}` (symmetric charges, `b = (a_{k+1..l-1},a_l,a_{l-1..k+1},a_k)` repeated `p` times) give `W^{-d}‖A‖ ≤ M_{2(l-k)p}^{1/(2p)}` (`eq:Apsipsi1`, `3_5:985`). `a_j`, `k<j<l`, lies only in `A`: the bound is uniform in `a_j`, so `Σ_{a_j∈𝒜(a_m)}` costs the factor `|𝒜(a_m)| ≤ C`. CS over `(a_m,x_m)`: `(W^{-2d}Σ_{x_m}Σ_{x_k∈a_k}|C^{(k)}_{x_mx_k}|²)^{1/2}`, and `W^{-2d}Σ_{x_m}Σ_{x_k∈a_k}|C^{(k)}_{x_mx_k}|² = W^{-d} tr(E_k C^*C)` with `G(-σ_1)G(σ_1)` Ward-reduced `= W^{-d}(𝓛^{(2k-1)}_+ - 𝓛^{(2k-1)}_-)/(2iη)`, modulus `≤ M_{2k-1}/(W^dη)`; likewise `(CC^*)` for `C^{(m-l)}`: `M_{2m-2l-1}/(W^dη)`. Second `W^dη` enters here (square-rooted twice: total exponent 1).

| Row | Quantity | Value | Constraint | Slack |
|---|---|---|---|---|
| 1 | constant in `(W^dη)^{-1}` (part 1) | `1`: each `Σ𝓛^{(2k)} ≤ (2M)/(2W^dη)`, then `½·1+½·1`, per `(P3)` | no loss allowed (pin has constant 1) | 0 (sharp: numeric ratio `0.999992` at `m=2,k=1`, `E=0`, `τ=0.5`, below) |
| 2 | exponent of `(W^dη)` | `-1 = -(½+½)` | pin `(W^dη)⁻¹` | 0 |
| 3 | exponent of the loop product | `½` on `M_{2k-1}M_{2m-2k-1}` | pin `(…)^{1/2}` | 0 |
| 4 | loop lengths, part (1) | `2k-1 ≥ 1`, `2m-2k-1 ≥ 1` | `1 ≤ k ≤ m-1` (so `ℕ`-subtraction never truncates; `m ≥ 2`) | `k-1`, `m-k-1` |
| 5 | loop lengths, part (2) | `2k-1 ≥ 1`, `2m-2l-1 ≥ 1`, `2(l-k)p ≥ 4` | `1 ≤ k < j < l ≤ m-1` (Lean: `k < j.val+1 < l`, `l+1 ≤ m`), hence `l-k ≥ 2`, `m ≥ 4` | `l-k-2`, `m-l-1`, `4(p-1)` in length |
| 6 | Hölder exponent | `1/(2p) ∈ (0,½]` | `p ∈ ℕ`, `p ≥ 1` (needs `‖A‖ ≤ tr[(AA^*)^p]^{1/(2p)}`, eigenvalue sum) | `p=1`: `‖A‖ ≤ ‖A‖_{HS}`, loses `‖A‖_{HS}/‖A‖ ≥ 1`; `p→∞` sharp |
| 7 | factor `C` | `C ≥ card 𝒜(x)` | Lean `0 ≤ C`, `∀x, card(𝒜 x) ≤ C` | 0 (used exactly: `Σ_{a_j}` of a bound uniform in `a_j`) |
| 8 | `η_τ > 0` | `(1-τ)√(4-E²)/2` | `|E|<2`, `τ<1` | instance: `η = 0.5`; `η → 0` as `τ → 1` is allowed (RHS grows like `η⁻¹`) |
| 9 | index shift | Lean `j : Fin (m-1)` ↔ paper `a_{j.val+1}` | pin uses `j.val+1` in `k < j.val+1 < l` | matches `1 ≤ k < j < l ≤ n-1` (`3_5:920`) |

No exponent is lost anywhere, so no `W^{-ε}`, `ℓ_t`, `Θ` or lattice sum enters: the statement is independent of `d`, `L`, `W` except through `W^d`; no `d = 2` specific input, no `d ≥ 3` hypothesis used.

### (ii) One concrete nondegenerate instance
(a) Numerics of both parts, `d=3, W=2, L=3` (`N=216`, 27 blocks of size 8), `E ∈ {0,1}`, `τ ∈ {0.5, 0.9, 1-g²/L²=0.9722}` (`g=0.5`), one sampled Hermitian `H` (complex Gaussian entries, scaled by 1.5 inside a diagonal block and 1 elsewhere) per `(E,τ)`. LHS: exact max over all `σ` and all `a_1..a_{m-1}` of `Σ_{a_m}|𝓛^{(m)}|` (part 1, `m∈{2,3,4}`, all `k`) and of the top-`C` sum over `a_2=a_j` (part 2, `m=4, k=1, j=2, l=3`, `C∈{1,3}`, worst `𝒜(x)`). RHS: `M_k` exact over all `σ,a` for `k ≤ 5`; `M_{4p}` for `p=2` is the max over `σ_2,σ_3,a_1,a_2,a_3` of the loops `W^{-4d}tr[(AA^*)^2]` (a lower bound of `M_8`, so the printed part-2 ratios for `p=2` are upper bounds of the true ratios). Printed numbers are LHS/RHS.
```
$ python3 contract.py            # row 1;  python3 contract_cfg.py i   # i = 1..5 (same code, one (E,τ) each); part-1 columns m{m}k{k}
  0.5000 E=0.0 eta=0.5000 | m2k1:0.999992 m3k1:0.974977 m3k2:0.974977 m4k1:0.979495 m4k2:0.999992 m4k3:0.979495
  0.5000 E=1.0 eta=0.4330 | m2k1:0.897008 m3k1:0.876623 m3k2:0.876623 m4k1:0.880191 m4k2:0.908797 m4k3:0.880191
  0.9722 E=0.0 eta=0.0278 | m2k1:0.997425 m3k1:0.787817 m3k2:0.787817 m4k1:0.739071 m4k2:0.986470 m4k3:0.739071
  0.9000 E=0.0 eta=0.1000 | m2k1:0.999451 m3k1:0.864019 m3k2:0.864019 m4k1:0.792967 m4k2:0.998777 m4k3:0.792967
  0.9000 E=1.0 eta=0.0866 | m2k1:0.905096 m3k1:0.805096 m3k2:0.805096 m4k1:0.790762 m4k2:0.959693 m4k3:0.790762
  0.9722 E=1.0 eta=0.0241 | m2k1:0.863172 m3k1:0.723335 m3k2:0.723335 m4k1:0.689602 m4k2:0.999315 m4k3:0.689602
max over all rows, all (m,k): 0.999992   (must be <= 1)
$ python3 part2.py   # part 2, exact LHS, M_1 exact, M_{4p} from the proof's own loops
  tau=0.5000 E=0.0 eta=0.5000 M1=1.025 Mstruct(4)=0.002505 Mstruct(8)=9.136e-07 | C1p1:0.353892 C1p2:0.572883 C3p1:0.128672 C3p2:0.208296
  tau=0.9000 E=0.0 eta=0.1000 M1=1.043 Mstruct(4)=0.006886 Mstruct(8)=2.003e-05 | C1p1:0.351383 C1p2:0.435855 C3p1:0.190027 C3p2:0.235709
  tau=0.9722 E=0.0 eta=0.0278 M1=1.169 Mstruct(4)=0.0718 Mstruct(8)=0.004157 | C1p1:0.458666 C1p2:0.484025 C3p1:0.324226 C3p2:0.342152
  tau=0.5000 E=1.0 eta=0.4330 M1=1.017 Mstruct(4)=0.002544 Mstruct(8)=1.084e-06 | C1p1:0.322109 C1p2:0.503512 C3p1:0.118065 C3p2:0.184556
  tau=0.9000 E=1.0 eta=0.0866 M1=1.095 Mstruct(4)=0.009132 Mstruct(8)=3.157e-05 | C1p1:0.346725 C1p2:0.442042 C3p1:0.191439 C3p2:0.244067
  tau=0.9722 E=1.0 eta=0.0241 M1=1.103 Mstruct(4)=0.05194 Mstruct(8)=0.002441 | C1p1:0.431760 C1p2:0.442698 C3p1:0.329613 C3p2:0.337963
```
All ratios are `≤ 1` (max `0.999992`, attained at `m=2,k=1`, `E=0`, where `Σ_{a_2}|𝓛^{(2)}_{(+,-)}| = Im 𝓛^{(1)}_+/(W^dη)` by (P3), so that ratio is at most `max Im 𝓛^{(1)}/max|𝓛^{(1)}| ≤ 1`; it is `0.999992` here, the sharpness of row 1). The first run of `contract.py` with sampled `M_5` gave `m=4,k=1: 1.102 > 1`; with `M_5` exact it is `0.979`: sampling underestimates a max on the RHS, it is not a counterexample.

(b) The compiled instances the ticket asks for: `stContract_holds 3` at merged `sz0` (`Defs/Sizes.lean:260`), `n=0`, `E=0`, `τ=1/2`: `d=3, L=4, W=32`, `W^d = 32768`, `η = 1/2`, `(W^dη)^{-1} = 1/16384`, 64 blocks. Hypotheses of the target at this data (script):
```
$ python3 inst.py
  sz0 n=0: d,L,W,W^d,#blocks L^d = 3 4 32 32768 64
  hyp |E|<2: True  0<=tau: True  tau<1: True  eta_tau=(1-tau)Im m(E)= 0.5 >0: True
  (W^d eta)^-1 = 6.103515625e-05
  A: 1<=k: True  k+1<=m: True  lengths 2k-1,2m-2k-1 = 1 1 (>=1)
  B: 4<=m: True  1<=p: True  1<=k: True  k<j+1: True  j+1<l: True  l+1<=m: True  0<=C: True  j<m-1: True
  B: card A(x)=1<=C: True  lengths: 1 1 4 exponent 1/(2p)= 0.5
```
Instance A: `m=2, k=1`, lengths `1,1`. Instance B: `m=4, k=1, l=3, p=1`, `j = ⟨1,_⟩ : Fin 3` (paper `a_2`), `C = 1`, `𝒜 x = {x}`, lengths `1,1,4`, exponent `1/(2p) = 1/2`. Every hypothesis of part (1)/(2) is a decidable inequality on these numbers (`|E|<2`, `0 ≤ τ < 1`, the index chain, `0 ≤ C`, `card ≤ C`); the conclusion is the inequality of the pin, to be proved for all `ω`; `ω = 0` is a permitted choice.

External hypothesis: none (`STContract` is deterministic), so no limit computation is needed.

### Verdicts
- `stContract_holds` part (1): PASS (proof above closes with constant 1, no exponent loss; numerics max ratio `0.999992 ≤ 1`).
- `stContract_holds` part (2): PASS (proof above; numerics max ratio `0.572883` with the proof's own `M_{4p}`; the Lean index chain matches the paper's).
- Remark for stage 1b (not a defect): in Lean `STLI`/`Lloop` are traces over `Vtx`-blocks with `E_a = W^{-d}P_a` (`Eblk`), `STmaxL` is a `sup'` over all `(σ,a)` (nonneg real), so `M_k ≥ 0` and the real power `M^{1/(2p)}` is monotone; `η>0` needs `Im m(E) = √(4-E²)/2 > 0`.

## (b) Script output (Sat Oct  3 15:13:18 UTC 2026)

### b.1 Commit, hygiene, build
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2054 && git log -1 --format=%h\ %an\ %s && git rev-parse --abbrev-ref HEAD
607d0e0 Jun Yin: T2054: S3-02 contraction inequality stContract_holds (RBM3D/Induction/Contract.lean)
t/T2054
$ git diff --name-only main...t/T2054; wc -l RBM3D/Induction/Contract.lean
RBM3D/Induction/Contract.lean
    1143 RBM3D/Induction/Contract.lean
$ grep -n "sorry\|admit\|native_decide\|^axiom" RBM3D/Induction/Contract.lean; echo grep-exit=$?
grep-exit=1
$ lake env lean RBM3D/Induction/Contract.lean; echo exit=$?
exit=0
$ lake build RBM3D.Induction.Contract 2>&1 | tail -4
Hint: Type `m(odule docstring) + [tab]` to insert a template via snippet.

Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3706 jobs).
$ lake build RBM3D.Induction.Contract 2>&1 | grep -c "Induction/Contract.lean"   # warnings or errors reported for this file
0
```
### b.2 Axioms and the target statement
```
$ cat scratchpad/T2054/ax.lean; lake env lean scratchpad/T2054/ax.lean
import RBM3D.Induction.Contract
#print axioms RBM.Gauss.Sizes.stContract_holds
#check @RBM.Gauss.Sizes.stContract_holds
'RBM.Gauss.Sizes.stContract_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.Gauss.Sizes.stContract_holds : ∀ (d : ℕ), RBM.Gauss.Sizes.STContract d

$ grep -n "^theorem stContract_holds" RBM3D/Induction/Contract.lean   # the target statement, extracted by script
1046:theorem stContract_holds (d : ℕ) : STContract d := by

$ sed -n "/^def STContract/,/^$/p" RBM3D/Induction/Step34Pins.lean   # the merged pin (unchanged by this ticket)
def STContract (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ ω : sz.SeqΩ,
    (∀ (m k : ℕ), 1 ≤ k → k + 1 ≤ m → ∀ (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖ ≤
        (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
          (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * m - 2 * k - 1) ω) ^ (1 / 2 : ℝ)) ∧
    (∀ (m k l p : ℕ) (j : Fin (m - 1)) (C : ℝ), 4 ≤ m → 1 ≤ p → 1 ≤ k → k < j.val + 1 →
      j.val + 1 < l → l + 1 ≤ m → 0 ≤ C → ∀ (𝒜 : Zd d (sz.L n) → Finset (Zd d (sz.L n))),
      (∀ x, ((𝒜 x).card : ℝ) ≤ C) → ∀ (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ∑ y ∈ 𝒜 x,
          ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn (Function.update a j y) ++ [x]⟩‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
          (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * m - 2 * l - 1) ω) ^ (1 / 2 : ℝ) *
          STmaxL sz n E τ (2 * (l - k) * p) ω ^ (1 / (2 * (p : ℝ))))

$ the type of the theorem is the pin: ty.lean elaborates
import RBM3D.Induction.Contract
open RBM.Gauss.Sizes
example : ∀ d : ℕ, STContract d := stContract_holds
#check @stContract_holds
stContract_holds : ∀ (d : ℕ), STContract d
exit=0
```
### b.3 Compiled nonempty instances (same file)
```
$ sed -n "/^section Instances/,/^end Instances/p" RBM3D/Induction/Contract.lean   # compiled in the same file (lake env lean exit=0 above)
section Instances

open RBM.Gauss.SizesInst

/-- `η_{1/2}(E = 0) = 1/2 > 0`: the data of the instances are in the bulk, away from `η = 0`. -/
example : etaT 0 (1 / 2) = 1 / 2 := by
  unfold etaT
  rw [mE_im, show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- `(yi2oslxj2)` for `m = 2`, `k = 1`, `σ = (+,-)`, `a_1 = 0`. -/
example :
    (∑ x : Zd 3 (sz0.L 0), ‖STLI sz0 0 0 (1 / 2) (0 : sz0.SeqΩ)
        ⟨List.ofFn (![true, false] : Fin 2 → Bool),
          List.ofFn (![0] : Fin 1 → Zd 3 (sz0.L 0)) ++ [x]⟩‖) ≤
      (((sz0.W 0 : ℕ) : ℝ) ^ 3 * etaT 0 (1 / 2))⁻¹ *
        (STmaxL sz0 0 0 (1 / 2) (2 * 1 - 1) (0 : sz0.SeqΩ) *
          STmaxL sz0 0 0 (1 / 2) (2 * 2 - 2 * 1 - 1) (0 : sz0.SeqΩ)) ^ (1 / 2 : ℝ) :=
  (stContract_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0).1 2 1
    (by norm_num) (by norm_num) ![true, false] ![0]

/-- `(u2jzooi-2)` for `m = 4`, `k = 1`, `l = 3`, `p = 1`, `j = 2` (`a_2`, `1 < 2 < 3`), `C = 1`,
`𝒜 x = {x}`, `σ = (+,-,+,-)`. -/
example :
    (∑ x : Zd 3 (sz0.L 0), ∑ y ∈ ({x} : Finset (Zd 3 (sz0.L 0))),
        ‖STLI sz0 0 0 (1 / 2) (0 : sz0.SeqΩ) ⟨List.ofFn (![true, false, true, false] : Fin 4 → Bool),
          List.ofFn (Function.update (![0, 0, 0] : Fin 3 → Zd 3 (sz0.L 0)) (1 : Fin 3) y) ++ [x]⟩‖) ≤
      1 * (((sz0.W 0 : ℕ) : ℝ) ^ 3 * etaT 0 (1 / 2))⁻¹ *
        (STmaxL sz0 0 0 (1 / 2) (2 * 1 - 1) (0 : sz0.SeqΩ) *
          STmaxL sz0 0 0 (1 / 2) (2 * 4 - 2 * 3 - 1) (0 : sz0.SeqΩ)) ^ (1 / 2 : ℝ) *
          STmaxL sz0 0 0 (1 / 2) (2 * (3 - 1) * 1) (0 : sz0.SeqΩ) ^ (1 / (2 * ((1 : ℕ) : ℝ))) :=
  (stContract_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0).2 4 1 3 1
    ⟨1, by norm_num⟩ 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun x => {x}) (fun x => by simp) ![true, false, true, false]
    ![0, 0, 0]

end Instances
$ grep -n "theorem sz0_values" RBM3D/Defs/Sizes.lean   # the data of the instances (merged)
267:theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64 := by
```
### b.4 Name clashes; ports
```
$ grep -rn "stContract_holds" RBM3D | grep -v "Induction/Contract.lean"; echo grep-exit=$?   # name clash of the new public name
grep-exit=1
$ grep -nE "^(theorem|lemma|def|abbrev|instance|structure|inductive|axiom|example|class)" RBM3D/Induction/Contract.lean   # non-private top-level declarations
1046:theorem stContract_holds (d : ℕ) : STContract d := by
1110:example : etaT 0 (1 / 2) = 1 / 2 := by
1116:example :
1128:example :
$ grep -c "^private" RBM3D/Induction/Contract.lean   # helpers (all private, CLAUDE.md 3 (E))
56
$ grep -rnE "(def|abbrev) (hs|wd|Ref|Pm) " RBM3D | grep -v Induction/Contract.lean; echo grep-exit=$?   # names of the private helpers vs the library
grep-exit=1
$ grep -nE "^private (def|abbrev)" RBM3D/Induction/Contract.lean   # the private definitions
52:private def hs (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2
309:private def wd (l : List (Bool × κ)) : Matrix ι ι ℂ := (l.map fun p => G p.1 * E p.2).prod
325:private def Ref (c : κ → List (Bool × κ)) : List (Bool × κ) → κ → List (Bool × κ)
706:private def Pm (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
```
Ports: none (the ticket names no RBM2D source; no RBM1D/RBM2D text was copied, so no diff-stat applies).
### b.5 Registry pre-check and full build
```
$ cat scratchpad/T2054/precheck.lean   # registry pre-check (DECISIONS §16, §20): the root file plus this module, then the hard audit
import RBM3D
import RBM3D.Induction.Contract
#assert_rbm_axioms
$ lake env lean scratchpad/T2054/precheck.lean > precheck.out 2>&1; echo exit=$?
exit=0
$ grep -nE "axiom audit:|STContract|premises found|registry:" precheck.out   # with RBM3D.Induction.Contract
1:axiom audit: 1570 theorems, 628 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
43:  RBM.Gauss.Sizes.STContract: 2 [no certificate]
55:premises found by scanning: 49 (borrowed 2, owed 35, structural 12).
56:registry: 5 borrowed + 43 owed + 23 structural; 22 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
66: RBM.Gauss.Sizes.STContract,
$ same on the file with `import RBM3D` only (the base state, no Contract)
exit=0
1:axiom audit: 1569 theorems, 628 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
43:  RBM.Gauss.Sizes.STContract: 1 [no certificate]
55:premises found by scanning: 50 (borrowed 2, owed 36, structural 12).
56:registry: 5 borrowed + 43 owed + 23 structural; 21 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
$ git diff --stat main...t/T2054 -- RBM3D/Test/Axioms.lean RBM3D.lean   # not touched
(empty)
$ lake build   # full library in the worktree (the hub adds the root import at merge)
Build completed successfully (3747 jobs).
```
### b.6 Map of the proof
```
$ grep -nE "^private (lemma|def) (hs|psd_quad_pow_le|rowbound_of_pow|Gres_sub|Gres_ward_left|wd|Ref|wd_Ref|trace_reflect_X|trace_reflect_Y|core1|core2|list_split1|list_split2|part1_matrix|part2_matrix)( |$)" RBM3D/Induction/Contract.lean | cut -c1-48   # map of the proof
52:private def hs (A : Matrix ι ι ℂ) : ℝ := ∑ i,
100:private lemma psd_quad_pow_le {B : Matrix ι 
176:private lemma rowbound_of_pow (A : Matrix ι 
239:private lemma Gres_sub {H : Matrix ι ι ℂ} (h
276:private lemma Gres_ward_left {H : Matrix ι ι
309:private def wd (l : List (Bool × κ)) : Matri
325:private def Ref (c : κ → List (Bool × κ)) : 
337:private lemma wd_Ref (hG : ∀ σ, (G σ)ᴴ = G (
353:private lemma trace_reflect_X (hG : ∀ σ, (G 
391:private lemma trace_reflect_Y (hG : ∀ σ, (G 
508:private lemma core1 (X Y : Matrix ι ι ℂ) (q 
535:private lemma core2 (X₁ X₃ : Matrix ι ι ℂ) (
587:private lemma list_split1 {α : Type*} {m k :
670:private lemma list_split2 {α : Type*} {m k l
847:private lemma part1_matrix (hH : H.IsHermiti
887:private lemma part2_matrix (hH : H.IsHermiti
$ grep -n "^theorem stContract_holds" RBM3D/Induction/Contract.lean
1046:theorem stContract_holds (d : ℕ) : STContract d := by
```
### b.7 Narrative
1. Route, as in `3_5:918-1000`, no hypothesis added, no exponent lost: `𝓛^{(m)} = tr(E_x X E_q Y)`, `X = wd l · G(σ_k)`,
   `Y = wd r · G(σ_m)`, `E_a = W^{-d} P_a`. Hilbert-Schmidt Cauchy-Schwarz on `P_x X P_q` and `P_q Y P_x` (`core1`, `hs_proj`),
   then Cauchy-Schwarz over the endpoint label `x` (`Real.sum_sqrt_mul_sqrt_le`); `Σ_x P_x = 1` turns the two sums into
   `tr(X P_q X^*)` and `tr(P_q Y Y^*)`; Ward (`Gres_ward_left/right`) reduces each to two words of length `2k-1` resp. `2m-2k-1`
   (`trace_reflect_X/Y`, the reflected list `Ref`, `wd_Ref`), each bounded by `STmaxL` (`norm_trace_wd_le_STmaxL`).
2. Part (2): the loop is split at `a_k, a_l, a_n` (`list_split2`; the summed label `a_j`, `k < j < l`, lies in the middle word `r₂ y`).
   `|tr(S₁ A S₂)| ≤ √μ ‖S₁‖_HS ‖S₂‖_HS` with `A = P_q X₂ P_{q₂}` (`norm_trace_mul_mul_le`), `μ` a bound of `ρ ↦ ‖ρᵀA‖²`.
   `tr[(AA^*)^p] = W^{2pd} tr(wd(Lc^p))` with `Lc` the reflected middle word (`trace_pow_proj`, `wd_Ref`, `wd_pow`): a word of length
   `2(l-k)p`, bounded by `STmaxL (2(l-k)p)` for every `y`, so `Σ_{y ∈ 𝒜 x}` costs `card ≤ C` (`core2`). Powers of `W^d`: `W^{-3d}` from
   `E = W^{-d} P` against `W^d` from `√μ` and `W^d/η` from `√(MαMβ)` (`arith_sqrt_rpow`, `sqrt_mul_sqrt_eq`): total `(W^d η)⁻¹`.
3. Differences from the paper's route (proof-internal, not statement differences, so no paper-delta): (i) the non-negativity of the
   symmetric loops in `eq:CS1` is replaced by `‖P_x X P_q‖²_HS = tr(P_x X P_q X^*)` (`hs_proj`); (ii) `‖A‖ ≤ tr[(AA^*)^p]^{1/(2p)}` of
   `eq:Apsipsi1` is proved as the row-wise quadratic-form bound `⟨v, Bv⟩^p ≤ ‖v‖^{2p} tr(B^p)`, `B = AA^* ⪰ 0`, by the spectral
   theorem (`psd_quad_pow_le`, `rowbound_of_pow`, `hs_mul_le`).
4. `3 ≤ d` is not used; `L ≥ 1`, `W ≥ 1` enter only through `NeZero`. No obstruction; the statement of `STContract` is unchanged.
   Section (a): no mistake found (no (a′)); its numerics were not re-run.

## (c) Verified Mathlib names
Every dotted name of the comment-stripped file (125 names, `scratchpad/T2054/names.txt`) resolves by `#check` (0 errors, b.8). Method-style names used, all resolved by compilation: `Matrix.IsHermitian.eigenvectorUnitary`, `.eigenvalues`, `.spectral_theorem`, `.submatrix`, `.eq`, `Matrix.PosSemidef.eigenvalues_nonneg`, `.isHermitian`.
```
Bool.false_eq_true Bool.not_false Bool.not_true Complex.I Complex.conj_conj Complex.conj_mul' Complex.mul_conj' Complex.norm_I Complex.norm_real
Complex.ofReal_pow Complex.ofReal_re Complex.re_le_norm Complex.re_sum Complex.star_def Complex.sub_conj Finset.exists_max_image Finset.le_sup'
Finset.mem_univ Finset.mul_sum Finset.single_le_sum Finset.sum_comm Finset.sum_congr Finset.sum_le_sum Finset.sum_mul Finset.sum_nonneg Finset.univ
Finset.univ_nonempty Fintype.sum_prod_type Function.comp_def Function.update Function.update_apply List.append_assoc List.dropLast_append_getLast
List.drop_eq_getElem_cons List.eq_nil_or_concat' List.ext_getElem List.flatten_cons List.getElem_ofFn List.getElem_set List.getElem_zip List.length
List.length_dropLast List.length_flatten List.map_replicate List.ofFn List.replicate List.replicate_succ List.set_eq_take_append_cons_drop
List.sum_replicate List.take_append_drop List.zip_append Matrix.conjTranspose_apply Matrix.conjTranspose_conjTranspose Matrix.conjTranspose_mul
Matrix.conjTranspose_nonsing_inv Matrix.conjTranspose_one Matrix.conjTranspose_smul Matrix.conjTranspose_sub Matrix.diag_apply Matrix.diagonal
Matrix.diagonal_apply Matrix.diagonal_mul_diagonal Matrix.diagonal_pow Matrix.dotProduct_mulVec Matrix.isHermitian_diagonal_iff.mpr
Matrix.isUnit_iff_isUnit_det Matrix.mulVec Matrix.mulVec_diagonal Matrix.mulVec_mulVec Matrix.mul_apply Matrix.mul_assoc Matrix.mul_nonsing_inv
Matrix.mul_one Matrix.mul_smul Matrix.mul_sub Matrix.nonsing_inv_eq_ringInverse Matrix.nonsing_inv_mul Matrix.one_apply Matrix.one_mul
Matrix.one_mulVec Matrix.posSemidef_self_mul_conjTranspose Matrix.smul_mul Matrix.star_eq_conjTranspose Matrix.star_mulVec Matrix.sub_mul
Matrix.sum_apply Matrix.trace Matrix.trace_diagonal Matrix.trace_mul_comm Matrix.trace_mul_cycle Matrix.trace_smul Matrix.trace_sub Matrix.trace_sum
Nat.cast_ne_zero.2 Nat.pos_iff_ne_zero.mp Nat.pos_of_ne_zero Real.mul_rpow Real.norm_of_nonneg Real.pow_rpow_inv_natCast Real.rpow_inv_natCast_pow
Real.rpow_mul Real.rpow_nonneg Real.sqrt_eq_rpow Real.sqrt_mul Real.sqrt_nonneg Real.sqrt_sq Real.sum_mul_le_sqrt_mul_sqrt Real.sum_sqrt_mul_sqrt_le
Unitary.conjStarAlgAut_apply inv_mul_cancel₀ le_of_pow_le_pow_left₀ mul_inv_cancel₀ mul_pow norm_inv norm_mul norm_pow norm_sub_le norm_sum_le
pow_le_pow_left₀ pow_succ pow_succ' smul_pow smul_smul star_sum sub_smul sub_sub_sub_cancel_left
```
### b.8 Name check and one environment fact (script output)
```
$ lake env lean scratchpad/T2054/fullmathlib.lean   # `import Mathlib`
fullmathlib.lean:1:0: error: object file '/Users/junyin/Lean_proof/RBM3D/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean' of module Mathlib does not exist
$ python3 (dotted names of Contract.lean without comments -> #check each): names checked / lines with "error"
125 / 0
```
Names verified absent: none. Scratch files must import specific Mathlib modules (`Mathlib.olean` is not built here).
## (d) Open issues and paper-delta candidates
1. Registry (DECISIONS §16, §20): `STContract` is in `owedProps` (`RBM3D/Test/Axioms.lean:119`). With this module imported the scan finds 49 premises
   instead of 50 and lists `STContract` under "carry nothing yet" (b.5), so that `owedProps` line can be removed; the removal is the cleanup ticket's
   (`Test/Axioms.lean` is untouched here).
2. `inst_contract` in `Step34Pins.lean` still takes `h : STContract 3` as a hypothesis; it can now be discharged by `stContract_holds 3` (not a writable file here).
3. Paper-delta candidates: none (no Lean/paper statement difference; the two route differences are in b.7 item 3).
4. The file sets `linter.unusedSectionVars` and `linter.unusedDecidableInType` to false (generic-matrix sections); the `lake build` output replays lint warnings of
   other modules (b.1 tail), none is reported for this file (b.1: count 0).

