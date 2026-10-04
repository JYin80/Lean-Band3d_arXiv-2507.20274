Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 18:45:20 UTC 2026

### (i) Exponent table, dictionary and `d`-changes

Source: RBM2D `Induction/GridEnvelopeN.lean` at `c9a24cf` (713 lines), cited `GEN:line`. Merged: `RBM3D/Induction/GridDriftN.lean` (`GDN3`), `Green/Pins.lean` (`Pins`), `Path/Walk.lean`.

| Item | RBM2D (GEN) | RBM3D | Constraint / slack |
|---|---|---|---|
| sizes | `d : Sizes`, `d.L n`, `d.W n`, `d.size n`, `Sizes.size_eq` (`N = W^2 L^2`) | `sz : Sizes d`, `d : ℕ` implicit; `sz.size n = (W n * L n)^d` by `def`; `W^d * L^d = N` is `mul_pow` | exact (no exponent changes) |
| `RangeCond d τ' t` | `N^(-1+τ') ≤ 1-t n` eventually | `sz.RangeCond τ' t` (`Pins:55`), same inequality | exact |
| `SizeTendsto d` | | `sz.SizeTendsto` | exact |
| `spectralM`, `etaT`, `etaT_pos` | | `mE` (`spectralM_im(_pos)` are `mE_im`), `etaT E t = (1-t)(mE E).im` (`Loop/GLoop:75`) | exact |
| `stepErrN L W E k u v Δ Bk` | `((W⁻¹)^2)^(k-1)` factor, `W^2 L^2` | `stepErrN d L W E k u v Δ Bk` (`GDN3:289`), `((W^d)⁻¹)^(k-1)`, `c = W^d k^2 L^d` | see rows below |
| `kStepC` | `2k^4 N^2 B^3 + k^6 N^3 B^4` (GEN:225) | `kStepC d L W k B = 2 c B (c B^2) + c (c B^2)^2`, `c = W^d k^2 L^d = N k^2` (`GDN3:275`) | `2c^2B^3 + c^3B^4 = 2k^4N^2B^3 + k^6N^3B^4` identical form in `N` (`hWL : W^d L^d = N`) |
| `envConst` | `16(k+3)^4 N^4 (1+η⁻¹)^(k+4)` | `envConst d L W E k v`, `N = ((W*L)^d : ℕ)` (`Path/OneStep:78`) | identical in `N`; `hcast` becomes `rfl`/`push_cast` |
| `uStepC` | dimension-free | same (`GDN3:283`) | exact |
| `‖A_j‖` envelope factor | `(W⁻¹)^2 ≤ 1` for `W ≥ 1` (GEN:264) | `(W^d)⁻¹ ≤ 1` for `W ≥ 1` (`one_le_pow₀`) | needs `1 ≤ W^d`, holds |
| `exists_norm_Kcal_le_win` (GEN:71) | unconditional | `exists_norm_Kcal_le_win sz hsz E hKb hE v hv0 hv1 m τ hτ` (`GDN3:1098`), needs `sz.STKbound E` (owed pin, KL7) and a FIXED sequence `v : ℕ → ℝ`; bound `N^τ η_{v n}^{-m}` over `w ∈ [0, v n]` | NEW hypothesis `hKb : sz.STKbound E` in `gridDriftN_envelope` (paper-delta `T2153a`); see next row |
| uniformity in `j` | GEN:71 uses the bound uniform in `v` | merged lemma gives one `v n`; applied at `v = t n` it only gives `η_{t n}^{-m} ≥ η_{u_{j+1}}^{-m}`, a weaker `B_k` than the pinned `N^{τK} η_{u_{j+1}}^{-k}` | Route that keeps the pinned form: by contradiction, choose for each `n` with a failure a bad `j*(n) < K n`, put `v n = u_{j*(n)+1}` (else `0`); `v n ∈ [0,1)` since `0 ≤ s n ≤ u_{j+1} ≤ t n < 1`; the merged lemma at this `v` then contradicts the failure (same choice trick as private `gdn_STKbound_win`, `GDN3:1027`). Sound, no new input |
| `gridDriftN` use (GEN:83) | `gridDriftN d E s t K …` | `gridDriftN sz E s t K hE hs0 hst ht1 hK0 n j hj k hk σ Bk hBk hB` or `gridDriftN_at` (`GDN3:918, 777`); no `[NeZero k]` (T2111a) | `[NeZero k]` can be dropped from `gridDriftN_envelope` and the Stmt (stronger; paper-delta `T2153b`); `κ`, `hκ` become unused in the envelope but stay in the Stmt (needed by `exists_c`) |
| time/size helpers | `GoodEvent_gridTime_mono/le`, `GoodEvent_gridStep_nonneg`, `GoodEvent_one_le_size` (`Path/GoodEvent`, not ported) | `gridTime_last` (`Path/Walk:160`) public; mono/nonneg/`1 ≤ N` are private in other files; `ST_gridTime_mono`, `ST_gridStep_nonneg` are in `Induction/Step2Events`, which is NOT in the import closure of `GridGoodN`/`GridDriftN` (checked by script) | private `gridEnv_` helpers (about 20 lines: `Δ ≥ 0`, `u_j ≤ u_k`, `N ≥ 1`) |

Rows that carry numbers (all in `N`, independent of `d`; `H = N^θ`, `θ = 1-τ'`, `Y = N^{τK}`, `c ≤ Im m(E)`, `c = min(√(2κ)/2, 1)`):

| Row | Monomial (GEN:296-304) | Pin inequality (GEN:520-523) | Source of the number | `d`-dependence |
|---|---|---|---|---|
| A | `N^4 H^{2k+4} N^{-C_K/2}` | `8 + (4k+8)θ + 2D_t < C_K` | `envConst` (`N^4`, `(..H)^{k+4}`) times weight `(2H)^k`, `K Δ^{3/2} ≤ N^{-C_K/2}` | none (`N^4` is in `N`) |
| B | `N^3 Y^4 H^{5k} N^{-C_K}` | `3 + 4τK + 5kθ + D_t < C_K` | `kStepC` (`N^3 B^4`, `B = Y (H/c)^k`) | none (`c^3 = k^6 N^3`) |
| C | `Y H^{2k+2} N^{-C_K}` | `2θ + τK + 2kθ + D_t < C_K` | `uStepC`, `H^2 B (2k...)`, weight `H^k` | none |
| D | `Δ H ≤ 1` | `θ < C_K` | `Δ ≤ N^{-C_K}`, `H = N^θ` | none |
| `m ≤ K` | `K Δ = t-s ≤ 1`, `K Δ^2 ≤ N^{-C_K}` | | | none |
| Log sum | `Σ Δ/η_{u_j} ≤ (Im m)^{-1} log N` from `-log(1-t) ≤ log N` (GEN:138) | `RangeCond` | | none; no `L^2` or `138` appears in the 4 public results |

The `138` (GEN:582, `rpow_138_le_Kg`, `gridK sizes 28 2`) belongs only to the RBM2D instance; no `gridK` exists in RBM3D. Instance below takes `K n = N_n^{C_K}` (a natural power), `C_K = 21`. No statement changes beyond: sizes dictionary, `W^d`, new `hKb`, dropped `[NeZero k]`. No arithmetic fails.

Consumers in RBM2D at `c9a24cf` (script grep; code uses, not docstrings): `gridDriftN_envelope`: `NonAltEnd:891`, `PPVocab:806`. `sum_gridStep_div_etaT_le`: `AltBudget:685`, `AltEnd:811,1589`, `NonAltBudget:834`, `PPClosure:962,984`, `PPVocab:1254`. `sum_weighted_stepErrN_le`: `NonAltBudget:835`, `PPVocab:801`, `AltGridQ:2167`, `StoppedEndDefs:83`; `SumWeightedStepErrN_Stmt`: `StoppedEndDefs:78`, `AltGridQ`(doc). `GridAssemblyN` and `NonAltGood` use none of the four (0 hits). `GridGoodEvent_*` helpers: not used by the four results (no occurrence in GEN code); the `GridGoodN` references to the results are docstrings. Consumers `NonAltEnd`/`PPVocab` calling the envelope will need `hKb`.

### (ii) One concrete nondegenerate instance (`d = 3`, merged `sz0`)

Data: `sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_n = (W_n L_n)^3 = 128^3 (n+1)^18`, `N_0 = 2097152`. `sum_weighted_stepErrN_le`: `κ=1`, `E ≡ 0` (`|E| ≤ 1 = 2-κ`), `s ≡ 0`, `t ≡ 1/2`, `k = 3`, `τ' = τK = 1/2`, `D_t = 1`, `C_K = 21`, `K n = N_n^21`. `sum_gridStep_div_etaT_le`: `τ' = 2/3`, `t_n = 1 - N_n^{-1/3} = 1 - 1/(128 (n+1)^6)` (the boundary of `RangeCond`), `K ≡ 4`, `s ≡ 0`. `gridDriftN_envelope`: `κ=1`, `k=3`, `τK = 1/2`, `E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`, `K ≡ 4` (as `GridDriftNCheck`), `STKbound sz0 E0` stays a hypothesis of the example (owed pin KL7; the merged `stKbound_timeIcc` is restricted to a time window, not the full pin).

Command and output:

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2153/inst.py
N_0 = 2097152  (W,L,d)= (32, 4, 3)
row A threshold 20.0 < C_K = 21 slack 1.0
row B threshold 13.5 < C_K = 21 slack 7.5
row C threshold 5.5 < C_K = 21 slack 15.5
row D threshold 0.5 < C_K = 21 slack 20.5
monomial A exponent e = -1.5 target f = -1 gap f-e = 0.5 coef 3a =2.379e+08
monomial B exponent e = -8.5 target f = -1 gap f-e = 7.5 coef 3a =1.369e+06
monomial C exponent e = -16.5 target f = -1 gap f-e = 15.5 coef 3a =3666
first n from which A,B,C absorb (checked 50 consecutive): 3 N(n0) = 1.44e+17
RangeCond (tp=1/2,t=1/2): N_0^(-1/2) = 6.905e-04 <= 0.5 : True
N_n = 128^3 (n+1)^18 for n<50; N_1/N_0 = 262144
K_0 = N_0^21 has 133 digits; Delta*H<=1: log10(Delta*N^th)=-129.89
n=0  RangeCond(2/3) at boundary: True; sum Delta/eta = 2.0396 <= log N = 14.5561 : True
n=1  RangeCond(2/3) at boundary: True; sum Delta/eta = 2.0826 <= log N = 27.0327 : True
n=5  RangeCond(2/3) at boundary: True; sum Delta/eta = 2.0833 <= log N = 46.8078 : True
```

Hypotheses at the instance (each checked above or by inspection): `0 < κ = 1`; `0 < τ' = 1/2 ≤ 1`; `0 < τK = 1/2`; `0 ≤ D_t = 1`; `2 ≤ k = 3`; `|E_n| = 0 ≤ 2-κ`; `0 = s ≤ t = 1/2 < 1`; `K n ≠ 0`; the four inequalities are `20 < 21`, `13.5 < 21`, `5.5 < 21`, `0.5 < 21`; `K n ≥ N^{21}` holds with equality.

External hypotheses, limit computations (TEAM §8 lesson 14):
- `SizeTendsto sz0`: `N_n = 128^3 (n+1)^18 → ∞` (script: `N_1/N_0 = 262144`, closed form verified for `n < 50`).
- `RangeCond`: `N_n^{-1/2} ≤ 1/2` for every `n` (`N_n ≥ N_0` and `N_0^{-1/2} = 6.9e-4`); at the boundary `t_n`, `N_n^{-1/3} = 1 - t_n` exactly (assert in script for `n = 0, 1, 5`).
- eventual absorption `3 a_i N^{e_i} ≤ N^{-D_t}` in `sum_weighted_stepErrN_le`: holds from `n = 3` on (script), gaps `0.5, 7.5, 15.5`; the largest coefficient is `3 a_1 = 2.4e8` against `N^{0.5} = 1448 (n+1)^9`.
- `STKbound sz0 E0`: owed pin (`docs/DECISIONS.md:167`); no limit computation exists, it stays a hypothesis of the `gridDriftN_envelope` example (CLAUDE.md §4 step 2 allows an unproved gate pin as a hypothesis).

Witness size: `K n = N_n^{21}` is forced by the hypothesis `K n ≥ N^{C_K}` (133 digits at `n = 0`); it enters only as a hypothesis value, no step is enumerated.

### Verdict per target

1. `gridDriftN_envelope`: PASS (conditional on the owed pin `STKbound`, new hypothesis; uniform-in-`j` envelope by the bad-index choice argument above).
2. `sum_gridStep_div_etaT_le`: PASS (dimension-free, only `RangeCond` and `N ≥ 1`).
3. `SumWeightedStepErrN_Stmt` / `sum_weighted_stepErrN_le`: PASS (the four inequalities are unchanged; `W^d` replaces `W^2` only inside `stepErrN`, `kStepC`, `envConst`, which are expressed in `N`).
4. Instances on `sz0`: PASS.

## (b) Script output — Sun Oct  4 18:51:09 UTC 2026

### Build and axioms
```
$ lake build RBM3D.Induction.GridEnvelopeN 2>&1 | grep "GridEnvelopeN\|Build completed\|error"
ℹ [3792/3792] Replayed RBM3D.Induction.GridEnvelopeN
GridEnvelopeN.lean:786:0: 'RBM.Ind.gridDriftN_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
GridEnvelopeN.lean:787:0: 'RBM.Ind.sum_gridStep_div_etaT_le' depends on axioms: [propext, Classical.choice, Quot.sound]
GridEnvelopeN.lean:788:0: 'RBM.Ind.SumWeightedStepErrN_Stmt' depends on axioms: [propext, Classical.choice, Quot.sound]
GridEnvelopeN.lean:789:0: 'RBM.Ind.sum_weighted_stepErrN_le' depends on axioms: [propext, Classical.choice, Quot.sound]
GridEnvelopeN.lean:790:0: 'RBM.Ind.GridEnvelopeNCheck.sum_weighted_stepErrN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
GridEnvelopeN.lean:791:0: 'RBM.Ind.GridEnvelopeNCheck.sum_gridStep_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
GridEnvelopeN.lean:792:0: 'RBM.Ind.GridEnvelopeNCheck.gridDriftN_envelope_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3792 jobs).
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Induction/GridEnvelopeN.lean | wc -l
       0
$ git diff --stat main...t/T2153
 RBM3D/Induction/GridEnvelopeN.lean | 792 +++++++++++++++++++++++++++++++++++++
 1 file changed, 792 insertions(+)
```

### Target statements (extracted by sed from the file, line ranges from grep)
```
$ sed -n '111,127p;180,189p;595,611p;613p' RBM3D/Induction/GridEnvelopeN.lean
theorem gridDriftN_envelope (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) (hk : 2 ≤ k) (τK : ℝ)
    (hτK : 0 < τK) {E s t : ℕ → ℝ} {K : ℕ → ℕ} (hsize : sz.SizeTendsto)
    (hKb : sz.STKbound E)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hK0 : ∀ n, K n ≠ 0) (σ : Fin k → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz), ∀ j, j < K n → ∀ a : Fin k → Zd d (sz.L n),
      ‖predIncN sz E s t K n j σ ω a - (gridStep s t K n : ℂ) *
          (∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n (E n) (gridTime s t K n j)
              (pathH sz s t K n j ω) l (loopOf σ a) +
            sz.STelklkM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a) +
            sz.STegtM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) (loopOf σ a))‖ ≤
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
          (gridStep s t K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) := by
  classical
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith
  have hv1 : ∀ n j, j < K n → gridTime s t K n (j + 1) < 1 := fun n j hj =>
  ...
theorem sum_gridStep_div_etaT_le (sz : Sizes d) {τ' : ℝ} (hτ' : 0 < τ') {E s t : ℕ → ℝ}
    {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hK0 : ∀ n, K n ≠ 0) (hrange : sz.RangeCond τ' t) :
    ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range (K n),
        gridStep s t K n / etaT (E n) (gridTime s t K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange] with n hn
  have hu1 : ∀ j ≤ K n, gridTime s t K n j < 1 := fun j hj =>
    (gridEnv_gridTime_le (hst n) (hK0 n) hj).trans_lt (ht1 n)
  have hpos : ∀ j ≤ K n, 0 < 1 - gridTime s t K n j := fun j hj => by linarith [hu1 j hj]
  ...
def SumWeightedStepErrN_Stmt : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) {κ τ' τK C_K D_t : ℝ} {E s t : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ),
    0 < κ → 0 < τ' → τ' ≤ 1 → 0 < τK → 0 ≤ D_t → 2 ≤ k → sz.SizeTendsto →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    (∀ n, K n ≠ 0) → sz.RangeCond τ' t →
    8 + (4 * (k : ℝ) + 8) * (1 - τ') + 2 * D_t < C_K →
    3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K →
    2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K →
    1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ K n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime s t K n m)⁻¹) ^ k *
          stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s t K n j) (gridTime s t K n (j + 1))
            (gridStep s t K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t)

theorem sum_weighted_stepErrN_le : SumWeightedStepErrN_Stmt := by
```

### Compiled nonempty instances (d = 3, sz0)
```
$ sed -n '707,720p;744,753p;756,759p;777,780p' RBM3D/Induction/GridEnvelopeN.lean
theorem sum_weighted_stepErrN_instance :
    ∀ᶠ n : ℕ in atTop, ∀ m ≤ Kc n,
      ∑ j ∈ Finset.range m, (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n m)⁻¹) ^ 3 *
          stepErrN 3 (sz0.L n) (sz0.W n) (E1 n) 3
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n j)
            (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1))
            (gridStep (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc n (j + 1)))⁻¹ ^ 3) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  sum_weighted_stepErrN_le 3 sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 21) (D_t := 1)
    (E := E1) (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc) 3 one_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sz0_tendsto
    (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
  ...
theorem sum_gridStep_instance :
    ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range ((fun _ => 4 : ℕ → ℕ) n),
        gridStep (fun _ => (0 : ℝ)) tBd (fun _ => 4) n /
          etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) tBd (fun _ => 4) n j) ≤
      (mE (E1 n)).im⁻¹ * Real.log ((sz0.size n : ℕ) : ℝ) :=
  sum_gridStep_div_etaT_le sz0 (τ' := 2 / 3) (by norm_num) (E := E1) (s := fun _ => 0) (t := tBd)
    (K := fun _ => 4) (fun _ => by norm_num) (fun _ => le_rfl) (fun n => zero_le_tBd n) tBd_lt_one
    (fun _ => by norm_num) rangeCond_tBd

/-- **Instance of `gridDriftN_envelope`** at `sz0` (`d = 3`), `κ = 1`, `k = 3`, `τ_K = 1/2`,
  ...
theorem gridDriftN_envelope_instance (hKb : sz0.STKbound E1) (σ : Fin 3 → Bool) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂(pathP sz0), ∀ j, j < 4 → ∀ a : Fin 3 → Zd 3 (sz0.L n),
      ‖predIncN sz0 E1 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => 4) n j σ ω a -
          (gridStep (fun _ => (1 / 10 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n : ℂ) *
  ...
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) σ

end GridEnvelopeNCheck
```

### Name-clash grep, ports
```
$ grep -rnE "gridDriftN_envelope|sum_gridStep_div_etaT_le|SumWeightedStepErrN_Stmt|sum_weighted_stepErrN_le|GridEnvelopeNCheck|gridEnv_" RBM3D --include="*.lean" | grep -v Induction/GridEnvelopeN.lean
RBM3D/Induction/QGridA.lean:37:`sum_weighted_stepErrN_le` of ST2-31 (S3-13b).
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/GridEnvelopeN.lean
 RBM2D/Induction/GridEnvelopeN.lean | 185 ++++---------------------------------
 1 file changed, 16 insertions(+), 169 deletions(-)
```

### Narrative (stage 1b)

- Commit `bab80fd` on `t/T2153`: new file `RBM3D/Induction/GridEnvelopeN.lean` (792 lines), the only file touched; no registry line added to `RBM3D/Test/Axioms.lean`.
- Port of RBM2D `Induction/GridEnvelopeN.lean` at `c9a24cf` (`GEN:54` envelope, `GEN:96` log sum, `GEN:161-566` weighted-sum bookkeeping, `GEN:515, 534` pin and theorem); dictionary exactly as section (a)(i): `sz : Sizes d`, `sz.size n = (W L)^d`, `mE`, `sz.RangeCond`, `W^d L^d = N` in `gridEnv_stepErr_le`, `(((W:ℝ)^d)⁻¹)^(k-1)` for the `‖A_j‖` factor.
- No numeric statement changed with `d` (the four pin inequalities are in powers of `N`); the RBM2D `138`/`gridK` data is replaced by `C_K = 21`, `K n = N_n^21` on `sz0`.
- `gridDriftN_envelope`: new hypothesis `hKb : sz.STKbound E` and `[NeZero k]` dropped (as in (a) rows 20-22). The merged `exists_norm_Kcal_le_win` fixes one time sequence `v`; the bound along the grid at `B_k = N^{τ_K} η_{u_{j+1}}^{-k}` is recovered by the worst-index choice `v n = u_{j*(n)+1}` (by contradiction against `∃ᶠ n`), inside the file, no new input. `κ`, `hκ` are unused in the proof but kept in the statement as in RBM2D.
- `sum_gridStep_div_etaT_le` and `sum_weighted_stepErrN_le` are proved with no new hypotheses; `SumWeightedStepErrN_Stmt` quantifies over `d` and `sz`.
- Instances at `d = 3` on `sz0`: `sum_weighted_stepErrN_instance` and `sum_gridStep_instance` have every hypothesis discharged (`SizeTendsto` by `sz0_tendsto`, `RangeCond` proved, `K n = N_n^21`, boundary `t_n = 1 - N_n^{-1/3}`); `gridDriftN_envelope_instance` keeps only `STKbound sz0 E1` (owed pin KL7) as a hypothesis, as the merged `exists_norm_Kcal_le_win_instance` does.
- `GridGoodEvent.lean` not ported (its `gridGoodN` is merged as `gridGoodN_holds`); no `GridGoodEvent_*` helper is used by the four results (section (a)); the three time/size helpers they needed are private `gridEnv_*` in this file.
- `RBM3D.lean` does not import the new module (hub adds the import at merge); the full `lake build` was not run by this stage, only `lake build RBM3D.Induction.GridEnvelopeN`.
- RBM2D `GridEnvelopeN.lean` differs between `c9a24cf` and HEAD `9e0f275` (see diff-stat above); the port is from `c9a24cf` as the ticket requires.

## (c) Verified Mathlib names (all compile in this file)

- `Real.one_sub_inv_le_log_of_pos`, `Real.log_div`, `Real.log_rpow`, `Real.log_le_log`, `Real.log_nonneg`, `Real.log_nonpos`
- `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_add`, `Real.rpow_mul`, `Real.one_le_rpow`, `Real.sqrt_eq_rpow`, `Real.sqrt_sq`
- `tendsto_rpow_atTop`, `Filter.not_eventually`, `Filter.Frequently.and_eventually`, `ae_all_iff`, `Finset.sum_range_sub'`
- `Nat.one_le_pow`, `Nat.pow_le_pow_left`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `pow_le_one₀`, `inv_le_comm₀`, `inv_anti₀`

## (d) Open issues and paper-delta candidates

- `T2153a`: `gridDriftN_envelope` has the extra hypothesis `hKb : sz.STKbound E` (owed pin KL7, via the merged `exists_norm_Kcal_le_win`, T2111a); RBM2D proved the bound unconditionally. Consumers `NonAltEnd`/`PPVocab` analogues must supply it.
- `T2153b`: `[NeZero k]` dropped from `gridDriftN_envelope` and `SumWeightedStepErrN_Stmt` (stronger).
- `T2153c`: the instance of `gridDriftN_envelope` keeps `STKbound sz0 E1` as a hypothesis (no proof of the pin yet).
- No paper (arXiv:2507.20274) statement is changed; all differences are RBM2D-to-RBM3D vocabulary or the owed-pin hypothesis.
