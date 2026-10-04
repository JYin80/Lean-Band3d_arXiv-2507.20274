Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 02:50:21 UTC 2026

Notation. `L^{(k)}` = `loopFine` (`tr ∏ G(σ_i)E_{a_i}`, `E_x = W^{-d}P_x`); `Q_{σ,a,b} := Σ_{|a'-a|≤1,|b'-b|≤1,σ'∈{(+,-),(-,+)}} L²_{σ',(a',b')}`;
`r = |a-b|` (`zdistInf`); `η = etaT E t`; `N = sz.size`. Pin: `STEMn2Poly` (`Step2Defs.lean:441`), loop `STEEkM` (`:131`), `SB_{cc'} ≤ 1_{|c-c'|≤1}` (kernel `(1+2dg²)⁻¹ ≤ 1` at 0, `g²(1+2dg²)⁻¹ ≤ 1/2` when `zdistD = 1`, which needs `d ≥ 1`).

### (i) Proof on paper, steps mapped; entry bounds; exponent table

1. `|EE_k| ≤ W^d Σ_{c'}Σ_{c∼c'} ‖L⁶_{(σ⊗σ̄)^{(1)},(a,b,c',b,a,c)}‖` (k=0; k=1 is `a↔b, σ₀↔σ₁`, the pin has `|a-b|` symmetric). Split the `c` by `|c-b| > |c-a|` (R1) vs `≤` (R2) (`(eq:S1+S2)`); all terms `≥ 0`, so enlarging the `c`-sum to all `c ∼ c'` is allowed.
2. **R1 (S₁).** `𝒜₁ = {c' : ∃c∈R1, c∼c'}`; `|c'-b| > r/2 - 1`. Bound `M := N^{τ'}K Ψ(r)²` on `𝒜₁`  (`(eq:pointwise_loop)`, step 4). `stContractPt_holds` (T2094, `Step2Defs.lean:391`) gives `Σ ≤ 3^d/(W^dη)·M·max_{σ̄}‖L³_{(σ̄,σ₁,-σ₁),(a,b,a)}‖`; the `W^d` cancels: `S₁ ≤ 3^d η⁻¹ M max‖L³‖` (`(eq:reduce4to3)`).
3. **R2 (S₂), the partner `(eq_sym_loop_bound2)`: NOT a second proof.** Cyclic rotation by 3: `L⁶_{σ,(a,b,c',b,a,c)} = L⁶_{σ̄,(b,a,c,a,b,c')}` with `σ̄ = (σ₀',σ₁') = (¬σ₀,¬σ₁)` (signs `(σ,-σ)` rotate to `(-σ,σ)`), which is the pin's pattern at `(a,b,c',c) := (b,a,c,c')`. So `STContractPt` applies verbatim with `𝒜₂ = {c ∈ R2}` (`|c-a| ≥ r/2`, no shift) and `max‖L³_{(·,..),(b,a,b)}‖`. Only the Lean lemma "`loopFine` is invariant under rotation by 3 of a 6-loop" (`trace_mul_comm` on `List.ofFn` product) is new; numerics below.
4. **Entries (`(eq:pointwise_loop)`, `(eq:reduce4_bdd3)`).** On `Ω(t,ε₀/2) = {‖G-M‖_max ≤ W^{-ε₀/2}}`: `|G_xx| ≤ |m(E)|+1 ≤ 2` (`|m(E)|=1`); `x≠y`: `|G_xy|² ≤ N^{τ_G}(Q_{σ,[x],[y]} + W^{-d}1_{|[x]-[y]|≤1})` (`(GijGEX)`), `Q ≤ 2·9^d N^{τ_L} max Ψ(|a'-b'|)²` (`STLWassm`, both `σ₀≠σ₁` patterns). Diagonal entries occur only for equal blocks, i.e. `c'=b` (needs `r<2` in R1) or `a=b`; each diagonal-index coincidence costs a factor `W^{-d}` of the count (`W^{-d} ≲ Ψ(0)²` by the `STPsiClass` window clause). Expanding `L⁴_alt = W^{-4d}Σ∏` gives `L⁴ ≤ Q̃⁴ + 8W^{-d}Q̃³ + … + 16W^{-3d}`, hence `√L⁴ ≤ K N^{τ_G+τ_L}Ψ(r)²`; `|L³| ≤ K N^{3(τ_G+τ_L)/2}Ψ(0)Ψ(r)²` (long legs `Ψ(r)²`, short leg `Ψ(0)`).
5. **Profile comparison (`STPsiClass`).** `Ψ(s) ≤ K₁Ψ(r)` for `s ≥ r/2-1` and for `s ≥ r-2`: `r ≥ 4`: `s ≥ r/4 ≥ 1`, `Ψ(s)/Ψ(r) ≤ C₁4^{C₂}` (ratio clause; if `s ≥ r` monotone); `r ≤ 3`: `Ψ(s) ≤ Ψ(0) ≤ c⁻¹Ψ(r)` (window clause at `C = 4`). `K₁ = max(C₁4^{C₂}, c⁻¹)`: depends on the class only, not on `W, L, λ`.
6. **Which premises give entry bounds: none of `STInitialGT2, STLWassm, STPsiClass` bounds a single entry of `G`** (they bound `L²` and `‖G-M‖_max ≺ W^{-ε₀}`; `(GijGEX)` is the lemma `lem_GbEXP`, not a consequence by Ward, which only gives `η⁻¹`). Hence the target is `theorem stEMn2Poly_of_GbEXP (d : ℕ) : STGbEXPii d → STGbEXPij d → STEMn2Poly d` (the form the ticket pins). **Finding:** the proof above uses `STGbEXPij` only; `STGbEXPii` (`(GiiGEX)`) and `STInitialGT2.2` (`max L² ≺ Ψ₀²`) are unused (diagonal entries are bounded by `2`, not by `Ψ(0)`). Keep `STGbEXPii` as an unused premise in the stated form (so the downstream S1-30 supplier has one signature), or state `stEMn2Poly_of_GbEXPij` first and derive the pinned form; candidate `T2102a`.
7. **Hidden trap handled.** `(GijGEX)` is stated with the indicator `Ω(t,ε₀) = 1(‖G-M‖_max ≤ W^{-ε₀})` (`STindMax`, `Defs.lean:197`) but `STInitialGT2.1` only gives `‖G-M‖_max ≤ N^{τ_Ω}W^{-ε₀}`. Fix: use `STGbEXPij` at `ε₀' = ε₀/2` and `τ_Ω = 𝔠ε₀/2` (`size_rpow_le_W_rpow`: `N^{τ_Ω} ≤ W^{τ_Ω/𝔠} = W^{ε₀/2}`); then `Ω(t,ε₀/2)` holds w.p. `≥ 1-N^{-D-1}`. Candidate `T2102b` is not needed (no statement change).

| quantity | value | constraint | slack |
|---|---|---|---|
| `η = etaT E t = (1-t) Im m(E)` | `0.9077` at `E = 1/2, t = 1/16` | `> 0`: `t ≤ lemT z < 1`, `|E| ≤ 2-κ` (`STFlow`, `locDomain`) | `t ≤ lemT = 0.999991` at n=0 |
| neighbour count | `3^d = 27` (`d=3`) | contraction pin constant (`stContractPt_holds`) | exact |
| `L²`-stencil count | `2·9^d = 1458` | `Q ≤ 1458·max` | absorbed in `N^{τ/2}` eventually |
| `τ_L = τ_G` | `τ/10` | `(5/2)(τ_L+τ_G) ≤ τ/2` (`M`: `N^{τ_G+τ_L}`; `L³`: `N^{3(τ_G+τ_L)/2}`; total exponent `5/2(τ_G+τ_L)`) | `τ/2` left for constants `K, 3^d, 1458` (`N→∞`) |
| `τ_Ω` | `𝔠ε₀/2 = 1/240` (`𝔠 = 1/6, ε₀ = 1/20`) | `N^{τ_Ω}W^{-ε₀} ≤ W^{-ε₀/2}` | exact |
| failure probability | `3·N^{-(D+1)} ≤ N^{-D}` | three premises (`InitialGT2.1`, `GijGEX`, `LWassm`) at `D+1` | holds for `N ≥ 3` (`SizeTendsto`) |
| `ε₀'` for `(GijGEX)` | `ε₀/2 = 1/40` | `GbEXPij` is `∀ ε₀ > 0` | exact |
| `Ψ` window | `W^{-3/2} ≤ Ψ₀ = W^{-1} ≤ W^{-1/20}` | `STPsiClass` clause 1, 3 (`c = 1`) | `W^{1/2}` and `W^{19/20}` at n=0 |
| `Ψ` ratio clause | `C₁ = C₂ = 2` (`Ψ₀` const.: ratio `1`) | `STPsiClass` clause 4 | `1 ≤ 2(r₂/r₁)²` |
| `K₁` | `max(C₁4^{C₂}, c⁻¹) = 32` | free of `W, L, λ` (§29) | — |
| diagonal fraction | `W^{-d} ≲ Ψ(0)²` | window `W^{-d/2} ≲ Ψ(0)` | `W^{-3}` vs `W^{-2}` |
| `SB_{cc'}` bound | `≤ 1` | `|sbKernel| ≤ 1` all `d` | `≤ 1/2` off the diagonal |
| `Ψ(0)` extra factor | `Ψ₀ = 1/32` at n=0 | from `|L³| ≲ Ψ(0)Ψ(r)²` | — |

DECISIONS §29: (1) `0 ≤ t ≤ lemT z` only used for `η > 0`; (3) no `L^d ≤ W^K` anywhere: the union over `(k,σ,a,b)` and all entries is inside one `Prec` (`badSetAt`, `StochDomAt.lean:53`) and the sums are deterministic on the intersection of three good events; (4) `Prec` eventual, `STPsiClass` clause 3 `∀ᶠ`; constants `K, K₁, 3^d, 1458` free of `W, L, λ`. `d ≥ 3` is not used; no `lam` bound is used.

### (ii) Concrete instance and checks

Deterministic hypotheses at the merged instance (`sz0`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z_n = 1/2 + iN^{-4/5}`, `t = 1/16`, `ε₀ = 1/20`, `Ψ = W^{-1}`):
`python3 inst.py | sed -n '1p;4p;5,6p'` (scratchpad `T2102/inst.py`)
```
n=0: L=4 W=32 lam=1.562e-02 N=2097152; E=lemE=0.5000 lemT=0.999991 eta_t=0.9077; N^-4/5=8.76e-06;  {'bandwidth': True, 'loc': True, 'WO': True, 't_le_lemT': np.True_, 'eta_pos': np.True_, 'PsiWindow': True, 'absE_lt_2': np.True_}
n=10: L=44 W=5153632 lam=8.820e-09 N=11659991713824860234842112; E=lemE=0.5000 lemT=1.000000 eta_t=0.9077; N^-4/5=8.84e-21;  {'bandwidth': True, 'loc': True, 'WO': True, 't_le_lemT': np.True_, 'eta_pos': np.True_, 'PsiWindow': True, 'absE_lt_2': np.True_}
loss budget: tau=0.100, tau_L=tau_G=0.0100, total 5/2*(tau_L+tau_G)=0.0500 <= tau/2=0.0500; tau_Omega=c*eps0/2=0.00417; N^tauOm*W^-eps0 <= W^-eps0/2 since N^tauOm<=W^(tauOm/c)=W^(eps0/2)
neighbour counts d=3: ball 3^d=27 ; L2-stencil 2*9^d=1458
```
External premises (`STInitialGT2`, `STLWassm`, `STGbEXPii/ij`; stay hypotheses of the example; limit computation, TEAM §8 lesson 14): one Gaussian sample of the model (`E|X_ij|² = W^{-d}SB_{[i][j]}`, real/imag parts of variance `S/2`, `H_t = √t X`, `z_t = E+(1-t)m(E)`, `E = lemE(z0)`, `t=1/16`), `d=3, L=3`, `W = 2,3,4`, `λ ∈ {1/64, 1}`: `max_{a,b,σ} L² ≈ 1.07 W^{-3}`, hence `max L²/Ψ₀² ≈ 1.07/W → 0` and `‖G-M‖_max` decreases to `W^{-3/2}`:
`python3 limit.py` (verbatim)
```
lam=0.0156 L=3 W=2 N=216: max L2=1.372e-01  W^3*maxL2=1.097  Psi0^2=W^-2=2.500e-01  ratio L2/Psi0^2=0.549  ||G-M||max=0.230 vs W^-3/2=0.354
lam=0.0156 L=3 W=3 N=729: max L2=3.983e-02  W^3*maxL2=1.075  Psi0^2=W^-2=1.111e-01  ratio L2/Psi0^2=0.358  ||G-M||max=0.158 vs W^-3/2=0.192
lam=0.0156 L=3 W=4 N=1728: max L2=1.673e-02  W^3*maxL2=1.070  Psi0^2=W^-2=6.250e-02  ratio L2/Psi0^2=0.268  ||G-M||max=0.112 vs W^-3/2=0.125
lam=1.0000 L=3 W=2 N=216: max L2=1.278e-01  W^3*maxL2=1.022  Psi0^2=W^-2=2.500e-01  ratio L2/Psi0^2=0.511  ||G-M||max=0.110 vs W^-3/2=0.354
lam=1.0000 L=3 W=3 N=729: max L2=3.758e-02  W^3*maxL2=1.015  Psi0^2=W^-2=1.111e-01  ratio L2/Psi0^2=0.338  ||G-M||max=0.059 vs W^-3/2=0.192
lam=1.0000 L=3 W=4 N=1728: max L2=1.580e-02  W^3*maxL2=1.011  Psi0^2=W^-2=6.250e-02  ratio L2/Psi0^2=0.253  ||G-M||max=0.043 vs W^-3/2=0.125
```
Target check (ticket (iii)): `d=3, L=4, W=2` (`N=512`, 64 blocks of 8; `lam` as `sz0 0` `= 1/64`; `z = 1/2 + iN^{-4/5}`, `t=1/16`), literal `|(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,(a,b),(a,b)}| = |W^d Σ_{c,c'}SB_{cc'}L⁶|` for all `k ∈ {0,1}`, all four `σ`, all 64×64 `(a,b)` (32768 cases), against `η⁻¹Ψ(0)Ψ(|a-b|)⁴` with `Ψ ≡ W^{-1}` (the `Ψ0` of `Step2Defs.lean:982`):
`python3 probe2.py 0.015625 1` (verbatim; the "cross-check" lines compare the block formula with the literal 512×512 product)
```
d=3 L=4 W=2 N=512 lam=0.015625 seed=1 z=0.50000+0.00680j E=lemE(z)=0.5000 lemT=0.9930 t=0.0625 eta_t=0.9077
||G-M||_max=0.2975 (W^-1/20=0.9659)
max_(a,b,sigma in {(+,-),(-,+)}) |L2|=1.3793e-01  Psi^2=2.5000e-01  holds=True
cross-check block vs literal: 0 (False, True) 0 0 0.0003399191756034383 0.0003399191756034376
cross-check block vs literal: 1 (True, False) 5 17 3.9544863632046065e-21 3.954486363204594e-21
32768 cases (k,sigma,a,b); bound eta^-1 Psi0 Psi(|a-b|)^4 = 0.03443
max ratio |EE|/bound = 9.8738e-03 at k=0 sigma=(False, True) a=(0, 0, 0) b=(0, 0, 0) |EE|=3.3992e-04
  |a-b|=0: cases 512, max ratio 9.8738e-03
  |a-b|=1: cases 13312, max ratio 7.0448e-11
  |a-b|=2: cases 18944, max ratio 2.6555e-19
```
`python3 probe2.py 1.0 1 | grep -E "^(d=|max ratio)"` (`λ = 1`, the strongest coupling)
```
d=3 L=4 W=2 N=512 lam=1.0 seed=1 z=0.50000+0.00680j E=lemE(z)=0.5000 lemT=0.9930 t=0.0625 eta_t=0.9077
max ratio |EE|/bound = 1.2187e-03 at k=0 sigma=(False, True) a=(3, 0, 2) b=(3, 0, 2) |EE|=4.1955e-05
```
Rotation identity of step 3 (200 random `(a,b,c,c',σ)` at the same sample): `python3 rot.py | tail -1`
```
max |L6(sigma,(a,b,c',b,a,c)) - L6((!s0,!s1),(b,a,c,a,b,c'))| over 200 random draws: 2.068870057447226e-35
```
All premises of the target hold at this sample (`‖G-M‖_max = 0.2975 ≤ 0.966`, `max L² = 0.138 ≤ Ψ² = 0.25`, `t ≤ lemT = 0.9930`); the largest ratio is `≈ 10^{-2}` (at `a = b`, where `Ψ(|a-b|)` does not decay), the loss factor needed is `< 1`. The ratio is a finite-size sanity check, not a proof of `≺`.

### Verdicts

- `STEMn2Poly` / `stEMn2Poly_of_GbEXP (d) : STGbEXPii d → STGbEXPij d → STEMn2Poly d`: **PASS**. Exponents close (budget `τ/2` spare); statement not false at the sample; the premises of the pin alone do not bound entries (step 6), so the proof is conditional on `STGbEXPij` (owed by S1-30) and the registry owed line of `STEMn2Poly` stays. `STGbEXPii` is not used by the proof (step 6).
- Partner `(eq_sym_loop_bound2)`: **PASS**, obtained from `stContractPt_holds` by rotation + sign flip (step 3); new Lean content: one rotation lemma for `loopFine`, not a second contraction proof.

## (a′) Preflight corrections — Sun Oct  4 03:37:12 UTC 2026

Section (a) is unchanged. Two points of it are superseded; the verdict (PASS) is not.

1. **Entry bounds are not needed** (supersedes (a) steps 4, 6, 7 and the line "conditional on `STGbEXPij`" of the Verdicts).
   (a) routes `(eq:pointwise_loop)`, `(eq:reduce4_bdd3)` through `(GijGEX)`, `(GiiGEX)`. Both are deterministic consequences of `(eq:LW_assm)`:
   for Hermitian `H`, `Im z > 0`, `E_a = W^{-d}P_a`, `G(σ)^* = G(-σ)` (block Cauchy–Schwarz, file §4):
   (F1) `(𝓛⁴_{(σ,-σ,σ,-σ),(c',b,c',b)})^{1/2} ≤ |𝓛²_{(σ,-σ),(c',b)}|`  [`‖XX^*‖_HS ≤ ‖X‖²_HS`, `X = P_b G P_{c'}`];
   (F2) `|𝓛³_{(s,σ₂,-σ₂),(a,b,a)}| ≤ |𝓛²_{(s,-s),(a,a)}|^{1/2} |𝓛²_{(σ₂,-σ₂),(b,a)}|`  [`|tr(Y^*BY)| ≤ ‖B‖_HS‖Y‖²_HS`, `B = P_aG(s)P_a`, `Y = P_aG(σ₂)P_b`].
   The three 2-loops have the pattern `(σ,-σ)` of `STLWassm`. So the target is the ticket's second branch,
   `stEMn2Poly_holds (d : ℕ) : STEMn2Poly d`; `STInitialGT2` is unused, `STGbEXPii/ij` do not occur. (b.8) checks F1, F2 and the final bound numerically.
2. **Exponent table** (replaces the rows `τ_L = τ_G`, `τ_Ω`, failure probability, `ε₀'`, `K₁` of (a)): one stochastic premise (`STLWassm` at `(τ', D)`), no event `Ω`, no union of three events.

| quantity | value | constraint | slack |
|---|---|---|---|
| `τ'`, `y` | `τ' = τ/5`, `y = N^{τ/10}`, `y² = N^{τ'}` | `STLWassm` at `(τ', D)` | exact |
| loss | `y⁵ = N^{5τ'/2} = N^{τ/2}` | `2·3^d K² y⁵ ≤ N^τ` | `N^{τ/2}` left for `2·3^d K²` (`N → ∞`, `SizeTendsto`) |
| `K` | `max(C₁ 3^{C₂}, c⁻¹)`, `c` from the window clause at `C = 1` | `r ≤ 2s+1 ⇒ Ψ(s) ≤ KΨ(r)`: monotone for `s ≥ r`; ratio clause with `r/s ≤ 3` for `1 ≤ s < r`; window for `s = 0` | free of `W, L, λ` (§29) |
| `S₁` distances | `c ∈ R₁`, `|c-c'| ≤ 1` ⇒ `r ≤ 2|c'-b| + 1` | triangle inequality of `zdistInf` | exact |
| `S₂` distances | `c ∈ R₂` ⇒ `r ≤ 2|c-a|` | same | exact |
| `η` | `etaT > 0` | `t ≤ lemT < 1`, `|lemE| < 2` (`STFlow`) | — |

DECISIONS §29: (1) `0 ≤ t ≤ lemT` is used only for `η > 0`; (3) no `L^d ≤ W^K`; (4) the window clause is `∀ᶠ`, used eventually; constants free of `W, L, λ`.

## (b) Script output — Sun Oct  4 03:37:12 UTC 2026

Branch `t/T2102`, commit `db20bf8`; worktree `RBM3D-wt/T2102`; scratch scripts in `scratchpad/T2102/`.

### b.1 Build
`lake build RBM3D.Induction.EMn2Poly 2>&1 | grep -n EMn2Poly` (after the last edit of the file; every line that mentions the module):
```
53:✔ [3722/3722] Built RBM3D.Induction.EMn2Poly (4.9s)
```
`lake build RBM3D.Induction.EMn2Poly 2>&1 | tail -3` (Sun Oct  4 03:27:17 UTC 2026; the two `info` lines are replayed diagnostics of the merged `Step2Defs.lean:978`):
```
info: RBM3D/Induction/Step2Defs.lean:978:46: `exact le_rfl`
uses `hc'`, which was modified by the flexible tactic `simp` on line 978!
Build completed successfully (3722 jobs).
```

### b.2 Axioms
`lake env lean axioms.lean` (`import RBM3D.Induction.EMn2Poly`, `#print axioms` of the five public declarations):
```
'RBM.Gauss.Sizes.stEMn2Poly_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_loop6_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_contractPt_partner' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_norm_loop4_alt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.emn2Poly_norm_loop3_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Target statements (extracted by script)
`sed -n 441,450p RBM3D/Induction/Step2Defs.lean` (the pin, unchanged by this ticket) and `#check @stEMn2Poly_holds`:
```
def STEMn2Poly (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2 sz (STflowE z) t ε₀ (fun n => Ψ n 0) → STLWassm sz (STflowE z) t Ψ →
            Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1))) ^ 4)
stEMn2Poly_holds : ∀ (d : ℕ), STEMn2Poly d
```
`git diff main...t/T2102 --stat | tail -2`: ` RBM3D/Induction/EMn2Poly.lean | 1028 +++++++++++++++++++++++++++++++++++++++++ |  1 file changed, 1028 insertions(+)` — only the new file; `example (d : ℕ) : STEMn2Poly d := stEMn2Poly_holds d` compiles. The partner `(eq_sym_loop_bound2)` (`sed -n 496,503p`; F1, F2 and the rotation are `emn2Poly_norm_loop4_alt_le`, `emn2Poly_norm_loop3_le`, `emn2Poly_loop6_rot` at lines 289, 359, 250, stated in (a′)):
```
theorem emn2Poly_contractPt_partner (hH : H.IsHermitian) (hz : 0 < z.im) (s0 s1 : Bool)
    (a b : Zd d L) (𝒜 : Finset (Zd d L)) (M : ℝ) (hM : 0 ≤ M)
    (h4 : ∀ c ∈ 𝒜, ‖loopFine d L W H z ![!s0, s0, !s0, s0] ![c, a, c, a]‖ ^ (1 / 2 : ℝ) ≤ M) :
    ∑ c ∈ 𝒜, ∑ c' ∈ Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c' - c) ≤ 1),
        ‖loopFine d L W H z ![s0, s1, s0, !s0, !s1, !s0] ![a, b, c', b, a, c]‖ ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * M *
        max ‖loopFine d L W H z ![true, !s1, s1] ![b, a, b]‖
          ‖loopFine d L W H z ![false, !s1, s1] ![b, a, b]‖ := by
```

### b.4 Compiled nonempty instances (`RBM3D/Induction/EMn2Poly.lean`, §9)
The endpoint theorem at `d = 3`, `sz0`, `z0`, `t ≡ 1/16`, `ε₀ = 1/20`, `Ψ = W^{-1}`; `STInitialGT2`, `STLWassm` stay hypotheses (other gates' pins; limit check in (a)):
```
/-- **`stEMn2Poly_holds` at `d = 3`** (`(eq:MG_conclusion)`): the conclusion at the data above. -/
example (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1))) ^ 4) :=
  stEMn2Poly_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) Ψ0 Ψ0_class hI hA
```
A second `example` applies the merged `inst_EMn2Poly (stEMn2Poly_holds 3) hI hA`. The deterministic core `emn2_ee_le` at a concrete Hermitian matrix (`d = 3, L = 3, W = 2`, `N = 216`), all hypotheses discharged, no stochastic hypothesis (statement; the proof is in the file):
```
example :
    ‖(((2 : ℕ) : ℂ) ^ 3) * ∑ c : Zd 3 3, ∑ c' : Zd 3 3, SB 3 3 ((1 : ℝ) / 8) c c' *
        loopFine 3 3 2 emH emZ ![true, false, true, !true, !false, !true]
          ![0, emB, c', emB, 0, c]‖ ≤
      2 * 3 ^ 3 / emZ.im * 1 ^ 2 * (emZ.im⁻¹) ^ 5 * 1 * 1 ^ 4 := by
```

### b.5 Name clashes
`grep -rn "stEMn2Poly_holds\|emn2Poly_" RBM3D RBM3D.lean docs/tickets /Users/junyin/Lean_proof/RBM1D/RBM1D /Users/junyin/Lean_proof/RBM2D/RBM2D | grep -v "^RBM3D/Induction/EMn2Poly.lean"`: no output. Public declarations, `grep -nE "^(theorem|lemma|def|abbrev|instance)" RBM3D/Induction/EMn2Poly.lean`:
```
250:theorem emn2Poly_loop6_rot (s0 s1 : Bool) (a b c c' : Zd d L) :
289:theorem emn2Poly_norm_loop4_alt_le (hH : H.IsHermitian) (s0 : Bool) (b c' : Zd d L) :
359:theorem emn2Poly_norm_loop3_le (hH : H.IsHermitian) (s s1 : Bool) (a b : Zd d L) :
496:theorem emn2Poly_contractPt_partner (hH : H.IsHermitian) (hz : 0 < z.im) (s0 s1 : Bool)
838:theorem stEMn2Poly_holds (d : ℕ) : STEMn2Poly d := by
```
The other 37 top-level declarations are `private`. Hygiene: `grep -nEw "sorry|admit|axiom|native_decide|sorryAx" RBM3D/Induction/EMn2Poly.lean`: no output (exit 1).

### b.6 Ports
No RBM1D/RBM2D port (no `git -C ../RBM2D` command run). §1–§3 of the file (`hs`, `norm_trace_mul_mul_conjTranspose_le`, `Gres_conjTranspose`, `Pm`, …) are copies of private lemmas of the merged `RBM3D/Induction/ContractPt.lean` at `2b7c4f6` (file:line in each docstring).

### b.7 Registry pre-check (DECISIONS §20) and full build
`lake env lean precheck.lean` (Sun Oct  4 03:27:25 UTC 2026; the file is `import RBM3D`, `import RBM3D.Induction.EMn2Poly`, `#assert_rbm_axioms`): precheck exit 0:
```
1:axiom audit: 3194 theorems, 1177 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
114:premises found by scanning: 83 (borrowed 2, owed 66, structural 15).
115:registry: 5 borrowed + 102 owed + 38 structural; 62 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
59:  RBM.Gauss.Sizes.STEMn2Poly: 2 [no certificate]
135: RBM.Gauss.Sizes.STEMn2Poly,
```
Baseline `lake build` (worktree, root without the module; Sun Oct  4 03:27:39 UTC 2026): full build exit 0:
```
576:info: RBM3D.lean:145:0: axiom audit: 3189 theorems, 1177 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
690:registry: 5 borrowed + 102 owed + 38 structural; 61 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
Build completed successfully (3846 jobs).
```
`Test/Axioms.lean` is not touched. With the module imported `STEMn2Poly` is proved, so it is in the "carry nothing yet" list (62 registered premises; baseline 61, where `STEMn2Poly` carries 1 theorem). `RBM.Audit.scanPremises` (the scan of `#assert_rbm_axioms`) on the same environment (`found_test.lean`, Sun Oct  4 03:35:54 UTC 2026) and, without the module, on the baseline (`found_base.lean`, Sun Oct  4 03:36:23 UTC 2026):
```
scanned premises: 83; STEMn2Poly among them: false
scanned premises: 84; STEMn2Poly among them: true
```

### b.8 Numerical checks (Sun Oct  4 03:30:29 UTC 2026; scripts `chkF.py`, `chkF2.py`, `chk_final.py`, built on the preflight `probe2.py` sample `d=3, L=4, W=2, t = 1/16`)
`python3 chkF.py | tail -2` (all `(s,c',b)` and `(s,s₁,a,b)` at the model sample, `λ = 1/64`):
```
F1 worst ratio sqrt|L4|/|L2| (<=1 expected): 0.7518187317501691
F2 worst ratio |L3|/(|L2aa|^(1/2)|L2ba|) (<=1 expected): 0.35861364557996245
```
`python3 chkF2.py | tail -1` (30 random Hermitian matrices, random `z`, 2 to 5 blocks, block size ≤ 4; the excess `2·10⁻¹⁶` is rounding):
```
random Hermitian, 30 trials: F1 worst 1.0000000000000002  F2 worst 1.0000000000000004
```
`python3 chk_final.py 0.015625 | tail -1` and `python3 chk_final.py 1.0 | tail -1` (`y` = smallest constant with `h2` for `Ψ ≡ W^{-1}`, `K = 1`; all 32768 `(k,σ,a,b)`):
```
y=0.7428 (y^2 = max|L2|/Psi^2 = 0.5517);  bound 2*3^d/eta*y^5*Psi^5 = 4.2031e-01;  max over 32768 cases |EE|/bound = 8.087e-04  (<= 1 expected)
y=0.7168 (y^2 = max|L2|/Psi^2 = 0.5137);  bound 2*3^d/eta*y^5*Psi^5 = 3.5168e-01;  max over 32768 cases |EE|/bound = 1.193e-04  (<= 1 expected)
```

### b.9 Narrative
1. `stEMn2Poly_holds (d : ℕ) : STEMn2Poly d` is proved outright for every `d` (the ticket's second branch; the pin is unchanged). Premises used: `STFlow` (`η_t > 0`, `N → ∞`), `STPsiClass`, `STLWassm`; `STInitialGT2` and `0 ≤ t` are not used.
2. Reduction (l. 838): `Prec` is `StochDomAt`; for each `τ > 0` the bad set of the conclusion is eventually inside the bad set of `STLWassm` at `τ' = τ/5` (`stochDomAt_of_subset'`, l. 797). On the complement every 2-loop `(s,-s)` is `≤ y²Ψ²(|x-x'|)`, `y² = N^{τ'}`.
3. Deterministic core `emn2_ee_le` (l. 679): `|W^d ΣΣ S^{(B)}_{cc'} 𝓛⁶| ≤ W^d Σ_{|c-c'|≤1} |𝓛⁶|` (`|S^{(B)}| ≤ 1`, support `|c-c'| ≤ 1`), split by `|c-a| < |c-b|` (`(eq:S1+S2)`).
4. `S₁` (`part1_le`, l. 534): `stContractPt_holds` with `𝒜 = {c' : ∃ c ∈ R₁, |c-c'| ≤ 1}`, `M = y²K²Ψ²(r)` (F1, `r ≤ 2|c'-b|+1`) and the 3-loop `≤ yΨ(0)·y²Ψ²(r)` (F2). `S₂` (`part2_le`, l. 615): the partner `emn2Poly_contractPt_partner` (l. 496), i.e. `stContractPt_holds` at `((-σ₁,-σ₂), b, a)` after the rotation by three positions `emn2Poly_loop6_rot` (trace cyclicity).
5. Result `2·3^d K² η⁻¹ y⁵ Ψ(0)Ψ(r)⁴`, `y⁵ = N^{τ/2}`; `2·3^d K² ≤ N^{τ/2}` eventually, so `≤ N^τ η⁻¹Ψ(0)Ψ(r)⁴`. The cut `k = 1` is `k = 0` at `((σ₂,σ₁),(a₂,a₁))` (`STEEkM_one_eq`, l. 821). `K` depends on the class `(C₁, C₂, c)` only.
6. New public declarations: 5 (`stEMn2Poly_holds`, four `emn2Poly_*` helpers); 37 `private`. `RBM3D.lean` does not import the module (hub, at merge).

## (c) Verified Mathlib names (all used in the compiled module; signatures printed by `lake env lean names.lean`)
- `Real.sum_mul_le_sqrt_mul_sqrt s f g` : `Σ_s f g ≤ √(Σ f²) √(Σ g²)`
- `Real.sqrt_le_sqrt` : `x ≤ y → √x ≤ √y`; `Real.sqrt_sq` : `0 ≤ x → √(x²) = x`; `Real.sq_sqrt` : `0 ≤ x → √x² = x`
- `Real.mul_self_sqrt` : `0 ≤ x → √x * √x = x`; `Real.sqrt_mul` : `0 ≤ x → ∀ y, √(x y) = √x √y`; `Real.sqrt_eq_rpow` : `√x = x^(1/2)`
- `Real.rpow_natCast` : `x^(↑n : ℝ) = x^n`; `Real.rpow_mul` : `0 ≤ x → x^(y z) = (x^y)^z`; `Real.rpow_add` : `0 < x → x^(y+z) = x^y x^z`
- `Real.rpow_le_rpow` : `0 ≤ x → x ≤ y → 0 ≤ z → x^z ≤ y^z`; `Real.one_le_rpow` : `1 ≤ x → 0 ≤ z → 1 ≤ x^z`
- `tendsto_rpow_atTop` : `0 < y → Tendsto (fun x => x^y) atTop atTop`; `Filter.Tendsto.eventually_ge_atTop` : `Tendsto f l atTop → ∀ c, ∀ᶠ x in l, c ≤ f x`
- `Finset.sum_filter_add_sum_filter_not s p f` : `Σ_{s with p} f + Σ_{s with ¬p} f = Σ_s f`; `Finset.sum_filter p f` : `Σ_{s with p} f = Σ_s if p a then f a else 0`
- `Finset.sum_subset` : `s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → Σ_{s₁} f = Σ_{s₂} f`
- `Finset.sum_le_sum_of_subset_of_nonneg` : `s ⊆ t → (∀ i ∈ t, i ∉ s → 0 ≤ f i) → Σ_s f ≤ Σ_t f`; `Finset.single_le_sum` : `(∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ Σ_s f`
- `Matrix.trace_mul_comm A B` : `(A * B).trace = (B * A).trace`; `Matrix.conjTranspose_mul` : `(M * N)ᴴ = Nᴴ * Mᴴ`; `Matrix.conjTranspose_nonsing_inv` : `A⁻¹ᴴ = Aᴴ⁻¹`
- `Matrix.IsHermitian.submatrix` : `A.IsHermitian → ∀ f, (A.submatrix f f).IsHermitian`; `Complex.mul_conj'` : `z * conj z = ↑‖z‖ ^ 2`
- `pow_le_pow_left₀` : `0 ≤ a → a ≤ b → ∀ n, a^n ≤ b^n`; `le_of_mul_le_mul_left` : `a * b ≤ a * c → 0 < a → b ≤ c`; `div_le_iff₀` : `0 < c → (b / c ≤ a ↔ b ≤ a * c)`
- Absent: `blockMat_isHermitian` (`Unknown identifier`; `Matrix.IsHermitian.submatrix` is used). Deprecated here: `rw [if_neg]` reports "`if_neg` has been deprecated: Use `ite_eq_right`"; `simp only [h, ↓reduceIte]` is used.

## (d) Open issues and paper-delta candidates
1. **T2102a** (proof route, no statement change): the paper bounds `(𝓛⁴)^{1/2}` and `𝓛³` (`3_5:812–825`) with the entry bounds `(GijGEX)`, `(GiiGEX)`; Lean uses F1, F2 (block Cauchy–Schwarz) and needs only `(eq:LW_assm)`, so `STEMn2Poly` holds without `STGbEXP*`; `(initialGT2)` is an unused premise of the pin.
2. **T2102b**: `(eq_sym_loop_bound2)` (`3_5:758`) is `emn2Poly_contractPt_partner` (rotation + flip of all charges). Its alternating 4-loop is `(-σ₁,σ₁,-σ₁,σ₁)` at `(c,a,c,a)`; the paper writes `σ^{(alt)} = (σ₁,-σ₁,σ₁,-σ₁)` at `(c,a,c,a)`, which involves the block `P_aGP_c` instead of `P_cGP_a` and differs in general. Harmless: both are `≤ |𝓛²_{(±)}|` by F1.
3. **Registry**: `Test/Axioms.lean` is untouched; the owed line of `STEMn2Poly` stays. Removing it before the root imports the module breaks the plain full build (`inst_EMn2Poly`, `Step2Defs.lean:1021`, assumes `STEMn2Poly 3` and nothing proves it without this module). With the module imported the pre-check lists the line among those carrying nothing (b.7), so it can be dropped in the merge commit or later.
4. For ST2-10/11 (`STEMn2Exp`), ST2-14: `emn2Poly_*` are public (F1, F2, the partner, the rotation); the third estimate needs `𝒯̃`-weights in place of `Ψ`, so `emn2_ee_le` itself (private) is not reusable as is.
5. No `sorry`, no new hypothesis, no weakened target, no frozen signature changed; the file touches only `RBM3D/Induction/EMn2Poly.lean`.
