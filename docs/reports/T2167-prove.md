Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 03:47:02 UTC 2026

Notation: `g = sz.lam n`, `W = sz.W n`, `L = sz.L n`, `r_{i,m} = (g²+|1-u_i|)/(g²+|1-u_m|)`, `B_u = sz.Bctl n u = W^{-d} Bparam d L g u 0 = W^{-d}[(g²+|1-u|)⁻¹ + (L^d|1-u|)⁻¹]` (Defs/Params.lean:36, Defs/Sizes.lean:214), `η_u = (1-u) Im m(E)` (Loop/GLoop.lean:75), `Im m(E) = √(4-E²)/2` (Defs/Semicircle.lean:42), `N = (WL)^d`.

### (i) Exponent table

| # | quantity | value / instance | constraint | slack |
|---|---|---|---|---|
| 1 | `C = nqGood1C d k Λg κ'` | `Classical.choose` of EK-6; only `C > 0` is known (`nqGood1C_pos`, NQGood1.lean:267; `1` outside the range) | fixed first, from `(d,k,Λg,κ')`, before `τ', ε, D', D''` | none needed: script sweeps `C ∈ {1/2,1,5,20}` |
| 2 | `κ_{i,m} = W^{Cε} r_{i,m}^{k-1}`, `ε_{i,m} = W^C` | `r ≥ 1` for `u_i ≤ u_m < 1` | `κ ≥ 0` (`W > 0`, ratio of nonnegatives), `ε_{i,m} ≥ 0` | — |
| 3 | `ε` | `4/5` | `0 < ε < 1` | `1/5` |
| 4 | `W^ε` | `16` (`W = 32`) | `4 ≤ W^ε` | factor `4` |
| 5 | `τ'`, `d W^{τ'}` | `1/5`; `3·2 = 6` | `d W^{τ'} ≤ W^ε` (needs `τ' < ε` as `W → ∞`) | `6 ≤ 16`; `W^{ε-τ'} = 8 ≥ 3` |
| 6 | class level `Dc`, `D'` | `Dc = D' = 6` | `1 < Dc ≤ D'` (class: `δ ≤ W^{-Dc}`; `hA0cls`, `hDcls` give `δ0 = δD = W^{-D'} ≤ W^{-Dc}` as `W > 1`) | slack `0` at `Dc = D'`; `Dc` may be any value in `(1, 6]` |
| 7 | `D''` | `5` | `k + 1 < D''` (nqGood1 `hD`) and `D'' ≤ D'` (forced by the shift hypothesis, row 8, since `ee ≥ 0`) | `4 < 5 ≤ 6` |
| 8 | shift hypothesis `W^{-D'} + eeShiftErrN d L W E k u u' ≤ W^{-D''}` | `W^{-5} - W^{-6} = 2.887e-8`; `eeShiftErrN ≤ 1.725e-26` at the four steps | at `(u_j, u_{j+1})`, `j < m ≤ K` | factor `1.7e18` |
| 9 | (5.93) `r_{u,t} B_u ≤ B_t` (`3_5:1158`), `u ≤ t < 1`, `g` any real | first term: `r·(g²+1-u)⁻¹ = (g²+1-t)⁻¹` exactly (`(K+1)^{d-2} = 1` at `K = 0`); second term `r (L^d(1-u))⁻¹ ≤ (L^d(1-t))⁻¹ ⇔ (g²+1-u)(1-t) ≤ (g²+1-t)(1-u)`, difference `= g²(t-u) ≥ 0` | `u ≤ t < 1`; `g²+|1-t| > 0` | `g²(t-u)`: `0` if `g = 0` or `u = t` (RBM2D's identity becomes an inequality) |
| 10 | `κ_{i,m} B_{u_i}^k ≤ W^{Cε} B_{u_m}^k` | `r^{k-1}B_u^k = (rB_u)^{k-1} B_u ≤ B_t^{k-1} B_t` (row 9, `B_u ≤ B_t` = `STBctl_mono`, `B ≥ 0`); `k-1+1 = k` for `k ≥ 1`, `k = 0` is `1 ≤ 1` | `u_i ≤ u_m < 1`, `0 ≤ W` | — |
| 11 | succ form `κ_{j+1,m} B_{u_j}^k ≤ W^{Cε} B_{u_m}^k` | `B_{u_j} ≤ B_{u_{j+1}}` then row 10 | `u_j ≤ u_{j+1} ≤ u_m < 1` | — |
| 12 | `dDrift = Γ(ΓΦ)(B_u^k/η_u)((k-1)+kΓΦ)` | equals the right side of `driftTensorN_norm_le_of_goodSet` (NQGood1.lean:104); `6.88e-12` at `u_0`, `7.82e-12` at `u_4` | `dDrift ≥ 0`: `0 ≤ Γ, Φ`, `1 ≤ k`, `η_u > 0` (`|E| < 2`, `u < 1`) | — |
| 13 | `qvBd(u',w)` vs `M_ee` at `u' = u_{j+1}` | `‖STeeM_{u'}‖ ≤ Γ(ΓΛ)B_u^{2k}/η_u + ee ≤ Γ(ΓΛ)B_{u'}^{2k}/η_{u'} + W^{-D''}`: `B_u ≤ B_{u'}` (`STBctl_mono`), `η_{u'} ≤ η_u` (`etaT_le_of_le`, needs `|E| < 2`), `ee ≤ W^{-D''}-W^{-D'} ≤ W^{-D''}`; far clause: `ℓ_u ≤ ℓ_{u'}` (`nqGood1_ellT_mono`) so (Vb) at `u` applies, `δ = W^{-D'} + ee ≤ W^{-D''}` | `0 ≤ Γ(ΓΛ)` (`Λ ≥ 0`), `0 ≤ u ≤ u' ≤ w`, `u' < 1` | row 8 |
| 14 | `qvBd > 0` | last term `W^C W^k W^{-D''} > 0`; the others are `≥ 0` (`η ≥ 0`, `Γ(ΓΛ) ≥ 0`, ratio `≥ 0`) | `1 < W`, `0 ≤ Λ`, `|E| ≤ 2`, `u ≤ 1` | min `qvBd = 5.5e-3` (`C = 1/2`) |
| 15 | window premises for all `s ≤ u_i ≤ u_{i'} ≤ w ≤ v` | `(1-w)/(1-u') ≥ (1-v)/(1-s) ≥ W⁻¹` (`1-w ≥ 1-v > 0`, `0 < 1-u' ≤ 1-s`); `w ≤ v ≤ 1-g²/L²`, `u_i < 1` as `g > 0` | endpoint premises only | `31/32 ≥ 1/32`; `1/32 ≤ 1 - 1/65536` |
| 16 | `hc_pos`: `Σ_{j<m} c_j > 0` | `c_j = (Δ k qvBd(u_{j+1},u_m)).toNNReal`, positive iff `Δ > 0` (`k ≥ 1`, row 14) | `s n < v n`, `K n ≠ 0`, `1 ≤ m ≤ K` (`AssembledN` only gives `0 ≤ Δ`) | `Δ = 1/128` |
| 17 | levels (D366) | `Γ = 4, Λ = 3, Φ = 1`: `Γ²Λ = 48` | `≥ 3(1+g²)^6 = 3.0044` (`g = 1/64`) | factor `15.98` |
| 18 | consumer order (S3-11/12, not a target hypothesis) | `(d,k,Λg,κ') → C → (τ', ε), d W^{τ'} ≤ W^ε → D'' > k+1 → D' > D''`; budget terms `W^{C-D'}` (`εK δ`), `W^{C+k-D''}` (`qvBd`) need `D'' > C + k`, hence `D', D''` after `C` | shift hypothesis eventually: `ee = k(2k+2) N η^{-(2k+3)} W^{-d(2k+1)} Δ ≤ k(2k+2) N η^{-(2k+3)} Δ` (`W^d L^d = N`), so `Δ ≤ N^{-C_K}` closes it once `C_K` is chosen after `D''` (`AssembledN` allows any larger `C_K`) | table in (ii) |

Refinements of the ticket text (no target fails; the statements must carry them): (n1) `qvFormN_le_of_goodSetN_shiftN` needs `|E| < 2`, not only `|E| ≤ 2` (`norm_STeeM_shiftN_le` NQGood1.lean:996 and `etaT_le_of_le` CondDom.lean:288 take `hE : |E| < 2`; checked by reading); every consumer has `|E n| < 2`. (n2) `u' < 1` follows from `u' ≤ w ≤ 1-g²/L²` with `g > 0`. (n3) `C` is not computable; every instance is at an abstract `C > 0`, and the claims that involve `C` (rows 10, 14, 16) hold for all `C > 0` (sweep).

### (ii) Concrete nondegenerate instance

Data: `d = 3`, `sz0` at `n = 0` (`L = 4, W = 32, lam = 1/64`, Defs/Sizes.lean:260-267), `E ≡ 1/2`, `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4` (`Δ = 1/128`, `u_j = j/128`, `grid_data` GridGoodN.lean:1129), `k = 3`, `σ = (+,-,+)` (`σ_2 = σ_{finRotate 3 2} = σ_0`), `(Γ,Λ,Φ) = (4,3,1)`, `τ' = 1/5`, `ε = 4/5`, `D' = Dc = 6`, `D'' = 5`, `Λg = 10`, `κ' = 1/2 ≤ Im m(1/2) = 0.968`. All premises of targets 2-4 (list: `3 ≤ d, 2 ≤ k, 0<Λg, 0<κ', 3 ≤ L, 0<g≤Λg, 1<W, 0<ε<1, 4 ≤ W^ε, dW^{τ'} ≤ W^ε, 1<Dc≤D', k+1<D''<D', u_i ≥ 0 monotone, u_K ≤ 1-g²/L², W⁻¹ ≤ (1-u_K)/(1-u_0), |E|<2, κ' ≤ Im m, Γ,Φ,Λ ≥ 0, Γ²Λ ≥ 3(1+g²)^6, non-alternating σ, s<v, K ≠ 0, Δ > 0`, and the window for every pair `i ≤ m ≤ K`) are checked in the script (line "premise checks: 22 all True").

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2167/pre.py` (exact rationals for the grid, mpmath at 60 digits for `Im m`, `η`, `W^r`). Output (verbatim, `pre.out`):

```
Delta 1/128 u ['0', '1/128', '1/64', '3/128', '1/32'] Im m(E)= 0.96824584
premise checks: 22 all True: True
threshold W^-5-W^-6 = 2.8871e-8
 step 0 -> 1  eeShiftErrN= 1.39081e-26  <= k(2k+2)N eta^-(2k+3) Delta = 564179.0 True  W^-6+ee<=W^-5: True
 step 1 -> 2  eeShiftErrN= 1.49336e-26  <= k(2k+2)N eta^-(2k+3) Delta = 605780.0 True  W^-6+ee<=W^-5: True
 step 2 -> 3  eeShiftErrN= 1.60439e-26  <= k(2k+2)N eta^-(2k+3) Delta = 650819.0 True  W^-6+ee<=W^-5: True
 step 3 -> 4  eeShiftErrN= 1.72467e-26  <= k(2k+2)N eta^-(2k+3) Delta = 699608.0 True  W^-6+ee<=W^-5: True
 dDrift at u_0 = 6.8833455e-12 >=0: True
 dDrift at u_4 = 7.8152452e-12 >=0: True
 C=0.5: min qvBd=0.00552542 >0:True ; sum_{j<m}c_j>0 for all m in 1..4: True
 C=1: min qvBd=0.0312729 >0:True ; sum_{j<m}c_j>0 for all m in 1..4: True
 C=5: min qvBd=1.11411e+6 >0:True ; sum_{j<m}c_j>0 for all m in 1..4: True
 C=20: min qvBd=4.5672e+46 >0:True ; sum_{j<m}c_j>0 for all m in 1..4: True
(5.93) grid d in{3,4}, L,g incl. g=0, g>L, g<0, t->1-g^2/L^2, random: cases 14040 violations 0
identity RHS-LHS = g^2 (t-u) on 2000 random rational cases: hits 2000
kappa_{i,m} B_{u_i}^k <= W^{C eps}B_{u_m}^k (W-power factor common), all i<=m<=4: True
shift hypothesis ee/(W^-5-W^-6) along sz0, Delta=N^-11, u'=1-lam^2/L^2 (smallest eta):
 E=0.0 ['2.78e-43', '1.24e-83', '7.64e-183', '7.09e-312', '2.35e-445', '2.65e-579', '2.69e-847']
 E=0.5 ['3.71e-43', '1.65e-83', '1.02e-182', '9.48e-312', '3.15e-445', '3.55e-579', '3.6e-847']
 E=1.5 ['1.15e-41', '5.1e-82', '3.15e-181', '2.93e-310', '9.71e-444', '1.1e-577', '1.11e-845']
 E=1.99 ['2.81e-34', '1.25e-74', '7.73e-174', '7.17e-303', '2.38e-436', '2.68e-570', '2.72e-838']
```

Reading of the output: (5.93) is checked on 14040 triples (d ∈ {3,4}; L ∈ {3,4,17,100}; g ∈ {0, 1/64, 1, L+5, -2}; points `-5, 0, 0.3, 0.9, top-1e-9, top` with `top = min(1-g²/L², 1-1e-12)`, plus 20 random per case), 0 violations; the identity `RHS-LHS = g²(t-u)` holds on 2000 random rational cases. The last block is the lesson-14 limit computation for the shift hypothesis (the only hypothesis that depends on the consumer's `Δ ≤ N^{-C_K}`): along `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `g = (2(n+1))^{-6}`), with `Δ = N^{-11}` (`C_K ≥ D₁+4D+k+2C_P+8 ≥ 11` at `k = 3`), the worst `u' = 1-g²/L²` (smallest `η`), `E ∈ {0, 1/2, 3/2, 1.99}`, the ratio `ee/(W^{-5}-W^{-6})` is `≤ 3e-34` for `n = 0` and tends to 0 (`n = 0,1,10,100,10³,10⁴,10⁶`); so the hypothesis holds eventually and is not vacuous. The EK-6 input behind `hker` is merged (`hker_of_case1N`), not external here.

### Verdicts

- Target 1 (vocabulary, six definitions): PASS (rows 1-2, 12-14; all five are total real-valued definitions; positivity/nonnegativity rows as above).
- Target 2 ((5.93) at `d ≥ 3` and the two kernel-scale inequalities): PASS (rows 9-11; the two-term `Bparam` reduces to `g²(t-u) ≥ 0`).
- Target 3 (the fields of `GridAssemblyHypN`: `hκ0, hε0, hker, hδ0, hA0cls, hdDrift0, hδD0, hdrift, hDcls`): PASS (rows 2-7, 12, 15; the class radius `ℓ_{u_j} W^{τ'} ≤ ℓ_{u_{j+1}} W^{τ'}` via `nqGood1_ellT_mono`).
- Target 4 (`qvBdNonAltN_pos`, `qvFormN_le_of_goodSetN_shiftN`, `hQ_nonAltN`, `subGaussStop_nonAltN`, `cQVNonAltN_sum_pos`): PASS with refinement (n1) (`|E| < 2`) and the premise `s n < v n`, `K n ≠ 0` for `hc_pos` (row 16); `hδ` at `(u_j, u_{j+1})` is satisfied at the instance with slack `1.7e18` and eventually in `n` (row 8, limit table).
- Overall: PASS.

## (b) Script output — Mon Oct  5 04:06:48 UTC 2026

Branch `t/T2167`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2167`, one new file `RBM3D/Induction/NQGood2.lean` (commit in (b.1)). Section (a) was not edited; no (a′): no mistake of (a) was found (refinement (n1) is carried by the statements; the hypotheses `1 < W` and `|E| ≤ 2` of row 14 are sufficient but turned out unnecessary, see (b.9)).

### (b.1) Build, scope, hygiene
$ lake build RBM3D.Induction.NQGood2 2>&1 | grep -E "NQGood2.lean.*(warning|error|sorry)|Built RBM3D.Induction.NQGood2|Build completed"
Build completed successfully (3838 jobs).
$ lake build 2>&1 | tail -1
Build completed successfully (3941 jobs).
$ git log --oneline -1; git diff --stat main...t/T2167; wc -l RBM3D/Induction/NQGood2.lean
1e0d03a T2167: S3-10b Induction/NQGood2 (class, constants, fields of GridAssemblyHypN, QV constant)
 RBM3D/Induction/NQGood2.lean | 1185 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1185 insertions(+)
    1185 RBM3D/Induction/NQGood2.lean
$ grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/Induction/NQGood2.lean
0
(the full `lake build` does not contain the new module: the root import is added by the hub at merge, CLAUDE.md §3 (A); the registry pre-check below loads it with the whole library.)

### (b.2) Axioms
$ lake build RBM3D.Induction.NQGood2 2>&1 | grep "NQGood2.lean.*depends on axioms" > axioms.out   (`#print axioms` of every public declaration is at the end of the file)
declarations printed:       56
with exactly [propext, Classical.choice, Quot.sound]: 56
other axiom lines (sorryAx, ...):        0
target theorems (17) and definitions (6) of the ticket are among the 56: the names are the 23 lines of (b.5).

### (b.3) Registry pre-check (CLAUDE.md §3 (A); `Test/Axioms.lean` untouched)
$ lake env lean reg.lean   (scratch: import RBM3D, import RBM3D.Induction.NQGood2, #assert_rbm_axioms)
axiom audit: 5097 theorems, 1759 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
30:  RBM.Gauss.Sizes.STOeqNQ: 1 [no certificate]
$ diff reg0.out reg.out   (reg0.lean = import RBM3D + #assert_rbm_axioms, without the new module)
1c1
< axiom audit: 5051 theorems, 1749 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 5097 theorems, 1759 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
(only the totals change: +46 theorems, +10 definitions; STOeqNQ stays at 1, no new premise is reported, so no registry line is needed.)

### (b.4) The six definitions of target 1 against the check file
$ diff <(NQGood2.lean, the six defs: lines 76-118) <(docs/tickets/checks/T2167-check.lean:101-143)
(empty diff: the six definitions, docstrings included, are identical; 43 lines each)

### (b.5) Target statements, extracted by script
$ python3 extract.py <23 names>   (declaration text up to the top-level ":=", whitespace collapsed; file RBM3D/Induction/NQGood2.lean)
def nonAltClsN (d L : ℕ) {k : ℕ} (g W τ' Dc : ℝ) (u : ℕ → ℝ) : ℕ → ℝ → ((Fin k → Zd d L) → ℂ) → Prop
def kappaNonAltN (d k : ℕ) (Λg κ' g W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ
def epsNonAltN (d k : ℕ) (Λg κ' W : ℝ) (_i _m : ℕ) : ℝ
def dDriftNonAltN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ : ℝ) : ℝ
def qvBdNonAltN {d : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (k : ℕ) (Λg κ' ε Γ Λ D'' u w : ℝ) : ℝ
def cQVNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ : ℕ → ℝ) (D'' : ℝ) (m : ℕ) (_a : Fin k → Zd d (sz.L n)) (j : ℕ) : ℝ≥0
theorem nqGood2_ratio_mul_Bctl_le (n : ℕ) {u t : ℝ} (hut : u ≤ t) (ht : t < 1) : ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - t|)) * sz.Bctl n u ≤ sz.Bctl n t
theorem kappaNonAltN_mul_Bctl_pow_le (n k : ℕ) (Λg κ' ε : ℝ) {W : ℝ} (hW : 0 ≤ W) (u : ℕ → ℝ) {i m : ℕ} (him : u i ≤ u m) (hm1 : u m < 1) : kappaNonAltN d k Λg κ' (sz.lam n) W ε u i m * (sz.Bctl n (u i)) ^ k ≤ W ^ (nqGood1C d k Λg κ' * ε) * (sz.Bctl n (u m)) ^ k
theorem kappaNonAltN_succ_mul_Bctl_pow_le (n k : ℕ) (Λg κ' ε : ℝ) {W : ℝ} (hW : 0 ≤ W) (u : ℕ → ℝ) (j m : ℕ) (hjj : u j ≤ u (j + 1)) (hj1m : u (j + 1) ≤ u m) (hm1 : u m < 1) : kappaNonAltN d k Λg κ' (sz.lam n) W ε u (j + 1) m * (sz.Bctl n (u j)) ^ k ≤ W ^ (nqGood1C d k Λg κ' * ε) * (sz.Bctl n (u m)) ^ k
theorem nonAlt_hkerN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg) (hκ' : 0 < κ') {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg) {W ε τ' Dc : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε) (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hDc : 1 < Dc) {K : ℕ} {u : ℕ → ℝ} (hu0 : ∀ i ≤ K, 0 ≤ u i) (hmono : ∀ i m, i ≤ m → m ≤ K → u i ≤ u m) (huK : u K ≤ 1 - g ^ 2 / (L : ℝ) ^ 2) (hWt : W⁻¹ ≤ (1 - u K) / (1 - u 0)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) : ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d L) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ → (∀ b, ‖X b‖ ≤ M) → nonAltClsN d L g W τ' Dc u i δ X → ∀ a : Fin k → Zd d L, ‖Ugen d L g E σ (u i) (u m) X a‖ ≤ kappaNonAltN d k Λg κ' g W ε u i m * M + epsNonAltN d k Λg κ' W i m * δ
theorem goodSetN_A0clsN {n k : ℕ} (hk : 1 ≤ k) {E Γ Λ Φ τ' D' Dc : ℝ} (hDc : Dc ≤ D') (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) {u : ℕ → ℝ} {i : ℕ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E (u i) k Γ Λ Φ τ' D') (σ : Fin k → Bool) : nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i (((sz.W n : ℕ) : ℝ) ^ (-D')) (fun a => sz.STLKM n E (u i) M σ a)
theorem nonAlt_hA0clsN {n k : ℕ} (hk : 1 ≤ k) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (σ : Fin k → Bool) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' Dc : ℝ) (hDc : Dc ≤ D') (τ : PathΩ sz → ℕ) (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D') : ∀ ω, 0 < τ ω → nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc (gridTime s v K n) 0 (((sz.W n : ℕ) : ℝ) ^ (-D')) (AvecN sz E s v K n 0 σ ω)
theorem nonAlt_hdriftN {n k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (τ : PathΩ sz → ℕ) (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D') : ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n), ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤ dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n)
theorem goodSetN_driftClsN {n k : ℕ} {E Γ Λ Φ τ' D' Dc : ℝ} (hDc : Dc ≤ D') (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) {u : ℕ → ℝ} {i i' : ℕ} (hii' : u i ≤ u i') (hi'1 : u i' < 1) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E (u i) k Γ Λ Φ τ' D') (σ : Fin k → Bool) : nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i' (((sz.W n : ℕ) : ℝ) ^ (-D')) (driftTensorN sz n E (u i) M σ)
theorem nonAlt_hDclsN {n k : ℕ} (E s v : ℕ → ℝ) (K : ℕ → ℕ) (hsv : s n ≤ v n) (hv1 : v n < 1) (hW : 1 ≤ ((sz.W n : ℕ) : ℝ)) (σ : Fin k → Bool) (Γ Λ Φ : ℕ → ℝ) (τ' D' Dc : ℝ) (hDc : Dc ≤ D') (τ : PathΩ sz → ℕ) (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D') : ∀ ω j, j < K n → j < τ ω → nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc (gridTime s v K n) (j + 1) (((sz.W n : ℕ) : ℝ) ^ (-D')) (driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ)
theorem nonAlt_hκ0N (d k : ℕ) (Λg κ' g W ε : ℝ) (hW : 0 ≤ W) (K : ℕ) (u : ℕ → ℝ) : ∀ i m, i ≤ m → m ≤ K → 0 ≤ kappaNonAltN d k Λg κ' g W ε u i m
theorem nonAlt_hε0N (d k : ℕ) (Λg κ' W : ℝ) (hW : 0 ≤ W) (K : ℕ) : ∀ i m, i ≤ m → m ≤ K → 0 ≤ epsNonAltN d k Λg κ' W i m
theorem nonAlt_hdDrift0N {n k : ℕ} (E s v : ℕ → ℝ) (K : ℕ → ℕ) (hk : 1 ≤ k) (hE : |E n| < 2) (hsv : s n ≤ v n) (hv1 : v n < 1) (Γ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΦ : 0 ≤ Φ n) : ∀ (_ : PathΩ sz) (j : ℕ), j < K n → 0 ≤ dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n)
theorem qvBdNonAltN_pos {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} {k : ℕ} {Λg κ' ε Γ Λ D'' u w : ℝ} (hΛ : 0 ≤ Λ) (hu1 : u ≤ 1) : 0 < qvBdNonAltN sz n E k Λg κ' ε Γ Λ D'' u w
theorem qvFormN_le_of_goodSetN_shiftN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg) (hκ' : 0 < κ') (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hD'' : (k : ℝ) + 1 < D'') {u u' w : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'w : u' ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - u')) {E : ℝ} (hE : |E| < 2) (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) {Γ Λ Φ : ℝ} (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D') (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) E k u u' ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) (a : Fin k → Zd d (sz.L n)) : qvFormN sz n E u' w σ M a ≤ qvBdNonAltN sz n E k Λg κ' ε Γ Λ D'' u' w
theorem hQ_nonAltN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg) (hκ' : 0 < κ') (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (Γ Λ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (m : ℕ) (hm : m ≤ K n) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) : ∀ M ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D', M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormN sz n (E n) (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j : ℝ)
theorem subGaussStop_nonAltN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg) (hκ' : 0 < κ') (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ) (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (Γ Λ Φ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (m : ℕ) (hm : m ≤ K n) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) : SubGaussStopN sz (E n) σ (gridTime s v K n) (goodExitTauN sz E s v K k Γ Λ Φ τ' D' n) (fun j ω => ZvecN sz E s v K n j σ ω) m a j (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)
theorem cQVNonAltN_sum_pos {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (hk : 1 ≤ k) (hsv : s n < v n) (hv1 : v n < 1) (hK : K n ≠ 0) (Γ Λ : ℕ → ℝ) (hΛ : 0 ≤ Λ n) (D'' : ℝ) : ∀ m, 1 ≤ m → m ≤ K n → ∀ a : Fin k → Zd d (sz.L n), 0 < ∑ j ∈ Finset.range m, (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j : ℝ)

### (b.6) Compiled nonempty instances (namespace `RBM.Ind.NQGood2Inst`, `d = 3`, `sz0`, `n = 0`)
$ python3 instmap.py   (the target theorem names occurring in the proof of each public instance, docstrings removed)
nqGood2_ratio_mul_Bctl_le: ratio_instance
kappaNonAltN_mul_Bctl_pow_le: kappa_Bctl_instance
kappaNonAltN_succ_mul_Bctl_pow_le: kappa_succ_instance
nonAlt_hkerN: hker_field_instance
goodSetN_A0clsN: A0cls_instance
nonAlt_hA0clsN: hA0cls_instance
nonAlt_hdriftN: hdrift_instance
goodSetN_driftClsN: driftCls_instance
nonAlt_hDclsN: hDcls_instance
nonAlt_hκ0N: hκ0_instance
nonAlt_hε0N: hε0_instance
nonAlt_hdDrift0N: hdDrift0_instance
qvBdNonAltN_pos: qvBd_pos_instance
qvFormN_le_of_goodSetN_shiftN: qvFormN_shift_instance
hQ_nonAltN: hQ_instance
subGaussStop_nonAltN: subGaussStop_instance
cQVNonAltN_sum_pos: hc_pos_instance
$ python3 extract.py hDcls_far_instance subGaussStop_instance hQ_instance qvFormN_shift_instance delta_shift_ok bundle_fields_instance tau0_pos hker_applied   (first 1200 characters)
theorem hDcls_far_instance (ω : PathΩ sz0) : ‖driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) (pathH sz0 sInst vg Kg 0 0 ω) sig3 aFar‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))
theorem subGaussStop_instance (m : ℕ) (hm : m ≤ Kg 0) (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < m) : SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0 (fun j ω => ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω) m a j (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j)
theorem hQ_instance (m : ℕ) (hm : m ≤ Kg 0) (j : ℕ) (hj : j < m) (a : Fin 3 → Zd 3 (sz0.L 0)) : ∀ M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Λ3 0) (Φ1 0) (1 / 5) 6, M.IsHermitian → gridStep sInst vg Kg 0 * (((3 : ℕ) : ℝ) * qvFormN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 m) sig3 M a) ≤ (cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j : ℝ)
theorem qvFormN_shift_instance : qvFormN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 4) sig3 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) aFar ≤ qvBdNonAltN sz0 0 (Einst 0) 3 10 (1 / 2) (4 / 5) (Γ4 0) (Λ3 0) 5 (gridTime sInst vg Kg 0 1) (gridTime sInst vg Kg 0 4)
theorem delta_shift_ok (j : ℕ) (hj : j < Kg 0) : ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) + eeShiftErrN 3 (sz0.L 0) (sz0.W 0) (Einst 0) 3 (gridTime sInst vg Kg 0 j) (gridTime sInst vg Kg 0 (j + 1)) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))
theorem bundle_fields_instance (ω : PathΩ sz0) : ‖Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 0) (gridTime sInst vg Kg 0 1) Xinst aFar‖ ≤ kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 0 1 * 1 + epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) 0 1 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) ∧ nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) 0 (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (A0f ω) ∧ (∀ b, ‖Dr0 0 ω b‖ ≤ dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Φ1 0)) ∧ nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0) (0 + 1) (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (Dr0 0 ω)
theorem tau0_pos (ω : PathΩ sz0) : 0 < tau0 ω
theorem hker_applied : ‖Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 0) (gridTime sInst vg Kg 0 4) Xinst aFar‖ ≤ kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0) 0 4 * 1 + epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ) 0 4 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))
$ python3 extract.py gridAssemblyHyp_instance   (the bundle; the fields are the theorems of targets 3-4, process `Af` drift-only, Z = Y = R = 0)
theorem gridAssemblyHyp_instance : GridAssemblyHypN sz0 (n := 0) (k := 3) (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0 (gridStep sInst vg Kg 0) (Kg 0) (nonAltClsN 3 (sz0.L 0) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (1 / 5) 6 (gridTime sInst vg Kg 0)) A0f Af Dr0 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (kappaNonAltN 3 3 10 (1 / 2) (sz0.lam 0) ((sz0.W 0 : ℕ) : ℝ) (4 / 5) (gridTime sInst vg Kg 0)) (epsNonAltN 3 3 10 (1 / 2) ((sz0.W 0 : ℕ) : ℝ)) (((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (fun j _ => dDriftNonAltN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0)) (fun _ _ => ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) (fun m a j => cQVNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 5 m a j) (fun _ => 0) (fun _ => 0) (fun _ => 0)

### (b.7) Name-clash grep of the new public names
$ bash clash.sh   (grep -rnw <name> RBM3D RBM3D.lean --include=*.lean --exclude=NQGood2.lean, the 23 names of targets 1-4)
cQVNonAltN_sum_pos: 0 hits outside NQGood2.lean
names:       23, total hits outside NQGood2.lean: 0
$ grep -rn NQGood2Inst RBM3D RBM3D.lean --include=*.lean --exclude=NQGood2.lean | wc -l
       0

### (b.8) Port provenance (RBM2D read-only; text read with `git show c9a24cf:RBM2D/Induction/NonAltGood.lean`)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/NonAltGood.lean | tail -2
9e0f275
 RBM2D/Induction/NonAltGood.lean | 1629 ++-------------------------------------
 1 file changed, 59 insertions(+), 1570 deletions(-)
(RBM2D HEAD is 9e0f275, not c9a24cf: the file changed after c9a24cf, so every port follows c9a24cf as the ticket pins it; RBM1D files were not used.) Ports: NonAltGood.lean:1143 `NonAltGood_rhoR_mul_scaleM_inv`, :1168-1184 vocabulary, :1232/:1250 `kappaNonAlt_*_scale_pow_*`, :1272 `nonAlt_hker`, :1283 `goodSetN_A0cls`, :1297 `goodSetN_driftCls`, :1317-1366 pathwise fields, :1385-1395 `qvBdNonAlt(_pos)`, :1424 `qvFormN_le_of_goodSet_shiftN`, :1495-1549 `cQVNonAlt`, `hQ_nonAlt`, `subGaussStop_nonAlt`, `cQVNonAlt_sum_pos`, :1883-2191 instances; each is re-derived for `d ≥ 3` (header of the file has the port map).

### (b.9) Narrative (route and deviations; each claim is checkable in the file)
- §2. `nqGood2_ratio_mul_Bctl_le` unfolds `Bctl`/`Bparam` at `K = 0` (`(0+1)^(d-2) = 1`): the first term is the identity `r (g²+1-u)⁻¹ = (g²+1-t)⁻¹`, the second reduces to the defect `g²(t-u)/(L^d(1-t)(1-u)(g²+1-t)) ≥ 0` (`field_simp; ring`); only `u ≤ t < 1` is used, `g` is any real. The two kernel-scale inequalities follow from the private `nqGood2_pow_aux` (`r^{k-1} a^k ≤ b^k` if `a ≤ b`, `r a ≤ b`) and `STBctl_mono`.
- Fields. `nonAlt_hkerN` turns the endpoint window `W⁻¹ ≤ (1-u_K)/(1-u_0)` into `W⁻¹ ≤ (1-u_m)/(1-u_i)` (`div_le_div₀`) and applies `hker_of_case1N` with `D := Dc`; the class is exactly its hypotheses `hδD`, `hXcls`. `goodSetN_A0clsN` is clause (Dec) at length `k` (`‖𝓛-𝒦‖ ≤ ‖𝓛‖ + ‖𝓛-𝒦‖ ≤ W^{-D'}`) with `W^{-D'} ≤ W^{-Dc}`; `goodSetN_driftClsN` is `driftTensorN_far_of_goodSet` with the radius monotone through `nqGood1_ellT_mono` (every real `g`: no `0 ≤ lam n` hypothesis; no `L^d ≤ W^K`). Both are stated at the index form `u i`, `u i'` because `nonAltClsN` takes a time sequence.
- QV constant. `qvFormN_le_of_goodSetN_shiftN` applies `nqGood1_qvFormN_le_of_bounds` at `v = u'` with `M_ee = Γ(ΓΛ)B_{u'}^{2k}/η_{u'} + W^{-D''}`, `δ = W^{-D''}`: (D4) at `u`, `norm_STeeM_shiftN_le`, `STBctl_mono`, `etaT_le_of_le`; (Vb) at `u` with `nqGood1_ellT_mono` and the shift; its conclusion is `qvBdNonAltN` after `unfold`. `hQ_nonAltN` derives the window of the shifted form for `u_j ≤ u_{j+1} ≤ u_m` from the endpoint ones `(s n, v n)`; `subGaussStop_nonAltN` is `azumaProxy_subG_goodExit` with the proved `azumaSubGN` and `hQ_nonAltN`.
- Instances. All 17 target theorems have a compiled instance at the ticket's data (map in (b.6)). The shift hypothesis for every grid step `j < 4` is `delta_shift_ok`: `eeShiftErrN ≤ 10^{-20}` for `0 ≤ u ≤ u' ≤ 1/32` (`η ≥ 4/5`, factor `32768·3·64`, loop length 8, `(W^{-3})^7 = 2^{-105}`), against `W^{-5} - W^{-6} ≈ 2.9·10^{-8}`. `C = nqGood1C` stays abstract. `0 < τ ω` for every sample (`tau0_pos` from `zero_mem_goodSetN_inst_grid`, levels `(4,3,1)`, D366); far clauses at `aFar`: `hA0cls_far_instance`, `hDcls_far_instance`; the nonzero kernel input of `hker` is `Xinst` (`hker_applied`). The bundle takes all ten fields from the theorems of §§3-4, with `tau0` and the proxy `cQVNonAltN` that `subGaussStop_instance` uses for every `m ≤ 4`, `j < m`, `a`; no unproved pin remains.
- Against the ticket's premise lists: added `|E| < 2` in the shifted majorant (preflight (n1)); `nonAlt_hdDrift0N` and `nonAlt_hDclsN` carry `s n ≤ v n`, `v n < 1` (needed for `u_j < 1`, as in RBM2D). Not needed and so absent: `1 < W` and every energy condition in `qvBdNonAltN_pos` and `cQVNonAltN_sum_pos` (`sz.W_pos`; `η_u ≥ 0` for `u ≤ 1` because Lean's `√` is nonnegative). `0 ≤ Γ` is unused in the shifted majorant (`Γ(ΓΛ) = Γ²Λ`); it is kept there, in `hQ_nonAltN` and in `subGaussStop_nonAltN` because the ticket lists it.

## (c) Verified Mathlib names (`#check @name` in `mnames.lean` returned no error for any of the 26)
- Real.rpow_le_rpow_of_exponent_le
- Real.rpow_nonneg
- Real.rpow_pos_of_pos
- Real.rpow_natCast
- Real.rpow_neg
- Real.rpow_mul
- div_le_div₀
- inv_anti₀
- pow_le_pow_left₀
- Even.pow_nonneg
- even_two_mul
- Real.coe_toNNReal
- Real.le_coe_toNNReal
- Finset.single_le_sum
- NNReal.coe_nonneg
- Real.sqrt_pos
- Real.le_sqrt_of_sq_le
- Real.sqrt_sq
- Real.sqrt_le_sqrt
- div_le_one
- max_eq_right
- add_pos_of_nonneg_of_pos
- norm_add_le
- add_sub_cancel
- Matrix.isHermitian_zero
- mul_le_mul
Project names used, all resolving in the build above: `hker_of_case1N`, `nqGood1_qvFormN_le_of_bounds`, `nqGood1_ellT_mono`, `nqGood1C`, `norm_STeeM_shiftN_le`, `eeShiftErrN`, `driftTensorN_norm_le_of_goodSet`, `driftTensorN_far_of_goodSet`, `Sizes.STBctl_pos`, `Sizes.STBctl_mono`, `RBM.Green.etaT_le_of_le`, `etaT_pos`, `ST_gridTime_zero`, `ST_gridTime_mono`, `gridTime_last`, `ST_gridStep_nonneg`, `azumaProxy_subG_goodExit`, `azumaSubGN`, `azumaProxy_pos_gridExitTauN`, `azumaProxy_pathH_zero_of_s_zero`, `mem_of_lt_gridExitTauN`, `NQGood1Inst.zero_mem_goodSetN_inst_grid`, `NQGood1Inst.aFar`, `NQGood1Inst.diam_aFar`, `NQGood1Inst.Xinst`, `NQGood1Inst.Xinst_norm_le`, `NQGood1Inst.Xinst_far`, `AzumaProxyNInst.{Einst,sig3,Γ4,Λ3,Φ1}`. Names verified absent: none needed.

## (d) Open issues and paper-delta candidates
Open issues (none blocks the audit; no dispatcher decision is needed):
- `C = nqGood1C d k Λg κ'` is a `Classical.choose` of EK-6; every statement holds for the actual `C`, so S3-11 must fix `D'' > C + k` and `D' ≥ D''` after `C` ((a) row 18).
- The shift hypothesis `W^{-D'} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-D''}` is a premise of `qvFormN_le_of_goodSetN_shiftN`, `hQ_nonAltN`, `subGaussStop_nonAltN`; it is not a field of the bundle and is not proved here for general data: S3-12 must obtain it from `Δ ≤ N^{-C_K}` ((a) (ii), the lesson-14 limit table). At the instance it is proved for every `j < 4` (`delta_shift_ok`).
- `nonAltClsN` carries `Dc`; `nonAlt_hkerN` needs `1 < Dc` and the field theorems `Dc ≤ D'`; the instances use `Dc = D' = 6`.
- `0 ≤ Γ` is an unused hypothesis in three statements (see (b.9)); the root import of `RBM3D.Induction.NQGood2` is added by the hub at merge; `Test/Axioms.lean` is untouched.
- RBM2D `NonAltGood.lean` differs between `c9a24cf` (read) and HEAD `9e0f275` ((b.8)); only `c9a24cf` was used.

Paper-delta candidates (Lean/paper or Lean/RBM2D statement differences):
- T2167a: (5.93) at `d ≥ 3` is the inequality `r_{u,t} B_u ≤ B_t` (paper `3_5:1158` states `≤`) with defect `g²(t-u) ≥ 0`, not RBM2D's identity `ρ_{s,t} M_s⁻¹ = M_t⁻¹`; the kernel weights satisfy `κ_{i,m} B_{u_i}^k ≤ W^{Cε} B_{u_m}^k` and the succ form.
- T2167b: the kernel class carries `δ ≤ W^{-Dc}`, `1 < Dc ≤ D'`, and the additive weight is `εK = W^C` (EK-6), not RBM2D's `((1-u_i)/(1-u_m))^k`; `κ_{i,m} = W^{Cε} r^{k-1}`, no `(1+log L)^k K_w^{2(k-1)}`.
- T2167c: the shifted majorant needs `k + 1 < D''`, `W^{-D'} + eeShiftErrN ≤ W^{-D''}` (hence `D'' ≤ D'`) and `|E| < 2`.
- T2167d: `hc_pos` needs `Δ > 0`, i.e. `s n < v n` and `K n ≠ 0` (`AssembledN` gives only `0 ≤ Δ`).
- T2167e: `qvBdNonAltN_pos` and `cQVNonAltN_sum_pos` need no energy condition and no `1 < W`.
- T2167f: the drift level `dDriftNonAltN` is the right side of `driftTensorN_norm_le_of_goodSet` with no additive `2 W^{-D'}` (RBM2D had it; T2154 (d)); the matrix-level class theorems are at the index form `u i`, `u i'`.
