Prover model: claude-sonnet-5-5

## (a) Math preflight — 2026-10-04 19:10:43 UTC

Sources: RBM2D `Induction/AltGridQ.lean` at `c9a24cf` (`:1680-2262`, `:2344-2358`); merged `QGridA.lean:1319-1355` (`lkEnvN`, `driftEnvN`, `qStepErrN`, `qErrQN`), `GridEnvelopeN.lean:588-613, 679-722`, `GridDriftN.lean:283-291`. Script: `scratchpad/T2156/pre.py` (math only; no Lean).

### (i) Dictionary and exponent table

Notation: tensor index `m ≥ 1` (T2132c, `m+1` indices), loop length `k = m+1` (RBM2D's `k`), `N = (WL)^d`, `θ = 1−τ'`, `H = N^θ`, `Y = N^{τ_K}`, `Lp = (L^d)^m`.

| RBM2D (`AltGridQ`) | RBM3D | note |
|---|---|---|
| `Lp = (L²)^{k-1} ≤ N^{k-1}` | `(L^d)^m ≤ N^m` (as `L^d ≤ W^d L^d = N`, `W ≥ 1`) | script: true at sz0, n=0,1 |
| `qStepErrN L k u Δ Mk Dm S`, factor `1+Lp` | `qStepErrN d L m C C₂ …`, factor `1+C·Lp`, `Ust = uStepC (m+1)`, `Dm ≤ 10k³ N Q²` (`driftEnvN` has `W^d L^d = N`) | NEW: constants `C, C₂` (merged `QGridA.lean:1339`) |
| `Σ_{j<m}` (sum length `m ≤ K n`) | sum length must be renamed (`p ≤ K n`): `m` is the tensor index | |
| `D_t + k` for `stepErrN` sum | **`D_t + m + 1 = D_t + k`**, not `D_t + m` (see below) | ticket text says `D_t + m` |
| `d.size n`, `d.W n` | `sz.size n = (W L)^d`, `sz.W n`; `sz.RangeCond τ' t`; `mE` for `spectralM` | as T2153 |
| `SumWeightedStepErrN_Stmt` (merged `GridEnvelopeN:595`) | applied at loop length `k = m+1`, decay `D_t+m+1`, `stepErrN d (sz.L n) (sz.W n) (E n) (m+1) …` | exact shape of `qErrQN` |
| `Bk = N^{τK} η_{u_{j+1}}^{-k}` | same, `k = m+1`; `STKbound` NOT needed: the sum theorem is deterministic (`sum_weighted_stepErrN_le` has no `STKbound`; `STKbound` enters only via `gridDriftN_envelope`, i.e. at the consumer) | corrects the ticket's "with the hypothesis STKbound" |
| RBM2D pin | none: grep `SumWeightedQErr` in `c9a24cf` finds nothing; RBM2D states the theorem directly (`:2146`) | state it directly |

Exponent table (all are exponents of `N`; `d` enters only through `N`, so the rows are those of RBM2D with `k=m+1`):

| row | value (`k=m+1`, `D' = D_t+k`) | must satisfy | slack at `m=3,τ'=τ_K=1/2,D_t=1` |
|---|---|---|---|
| R1 | `8+(4k+8)θ+2(D_t+k)` | `< C_K` | `30 < 31`: 1 |
| R2 | `3+4τ_K+5kθ+(D_t+k)` | `< C_K` | `20 < 31`: 11 |
| R3 | `2θ+τ_K+2kθ+(D_t+k)` | `< C_K` | `10.5 < 31`: 20.5 |
| R4 | `θ` | `< C_K` | `0.5 < 31` |
| Rx (`Δ²` part) | `k+2τ_K+(3k+2)θ+D_t` | `< C_K` | `13 < 31`; implied by R2: R2 − Rx = `3+2τ_K+(2k−2)θ > 0` (script: 5, 6, 7 for `m=1,2,3`) |
| first term | `(1+C·Lp)·N^{-(D_t+k)} ≤ (1+C)N^{-D_t-1}` | `≤ N^{-D_t}/2` | iff `N ≥ 2(1+C)` (eventually, `SizeTendsto`, `C` fixed) |
| `Δ`-scale | `ΔH ≤ N^{-C_K+θ} ≤ 1`; `KΔ ≤ 1`, `KΔ² ≤ Δ ≤ N^{-C_K}` | `C_K ≥ θ` | R4 |
| `Δ²`-part constant | per step `≤ Δ² a_Q N^k Q² H²`, `Q = Y (H/c)^k`, weight `≤ (2H)^k`, `m_sum ≤ K`; derived (not copied) `a_Q ≤ C(10k³+4(k+k2^k)+2k)+2C₂` | eventual `2·2^k a_Q c^{-2k} N^{(k+(3k+2)θ+2τ_K)−C_K} ≤ N^{-D_t}`, i.e. `C_K > Rx` | exponent gap `C_K−Rx = 18` (`Rx` contains `D_t`; script prints `C_K−extra_exp−D_t`); `log10(2A)=15.2 ≤ 18·log10 N_0 = 113.8` (script) |
| `C, C₂` | merged `gridDriftQN`: `C=(1+40dm)6^{dm}`, `C₂=1000(1+dm)²` (`QGridA.lean:2127-2128`), independent of `n` | statement: fixed `0 ≤ C, C₂`, quantified before `∀ᶠ n` | |

Why `D_t + m` cannot close: the first term is `(1+C·Lp) S` with `S ≤ N^{-(D_t+e)}` and `Lp ≤ N^m`. At `e = m` the product is `≤ (1+C)N^{-D_t}`, which exceeds `N^{-D_t}/2` for every `N`. At `e = m+1 = k` it is `(1+C)N^{-D_t-1}`. So the pin `SumWeightedStepErrN_Stmt` is applied with `D_t + k` (RBM2D's exponent, `:1680-1687`, `:2146-2160`), and the target `sum_weighted_qErrQN_le` keeps rows R1–R4 with `D_t+k` in place of `D_t`.

### (ii) Concrete instance (`d = 3`, merged `sz0`: `L_n=4(n+1)`, `W_n=(2(n+1))^5`, `N_n = 2097152 (n+1)^18`)

`m = 3` (`k=4`, as merged `gridDriftQN_instance`), `κ=1`, `E≡0`, `s≡0`, `t≡1/2` (`rangeCond_half`, merged), `τ'=τ_K=1/2`, `D_t=1`, `C_K=31`, `K n = N_n^{31}` (new; the merged `Kc = N^{21}` is too small: R1 = 30), `C=(1+40·9)6^9`, `C₂=1000(1+9)²=100000`. No hypothesis is left open (no `STKbound`). The statement is eventual; the first-term threshold is met from `n = 1` (`N_1 = 549755813888 ≥ 7276096514`); `n=0` is not needed.

```
$ python3 scratchpad/T2156/pre.py
rows (R1,R2,R3,R4) at D' = D_t+k, k=m+1; extra row; R2-extra; (tau'=tK=1/2)
d=3 m=1 k=2 D_t=1: rows=['22', '13', '13/2', '1/2'] extra=8 R2-extra=5 minC_K>22
d=3 m=2 k=3 D_t=1: rows=['26', '33/2', '17/2', '1/2'] extra=21/2 R2-extra=6 minC_K>26
d=3 m=3 k=4 D_t=1: rows=['30', '20', '21/2', '1/2'] extra=13 R2-extra=7 minC_K>30
ticket reading D'=D_t+m, m=3,k=4,D_t=1: ['28', '19', '19/2', '1/2']
RBM2D instance k=4,D_t=5,D'=D_t+k=9 (its rows 38,24,14.5,0.5): ['38', '24', '29/2', '1/2']
merged T2153 instance k=3,D'=D_t=1 (its rows 20,13.5,5.5,0.5): ['20', '27/2', '11/2', '1/2']
d=3,m=3: C = 3638048256 C2 = 100000
e=m (ticket) : (1+C) N^m N^-(D+e) / N^-D = (1+C) N^(m-e) -> (1+C) =3638048257 (never <= 1/2)
e=m+1=k (RBM2D) : (1+C) N^m N^-(D+e) / N^-D = (1+C) N^(m-e) -> (1+C)/N, <=1/2 iff N >= 7276096514
sz0 N_0 = 2097152 N_1 = 549755813888 N_n=2097152 (n+1)^18: True
Lp=(L^3)^3 <= N^3 at n=0,1: True True  ratio N/L^3 = 32768.0
first term threshold N>=2(1+C)= 7276096514 : n=0: False  n=1: True
k=4 c=0.7071 aQ'=3.347e+12 A=8.568e+14; exponent gap C_K-extra_exp-D_t=18.0; need 2A <= N^gap: log10(2A)=15.2 <= gap*log10(N_0)=113.8
instance m=3 (k=4), tau'=tK=1/2, D_t=1, C_K=31: rows= ['30', '20', '21/2', '1/2'] all <31: True ; merged Kc (C_K=21) suffices: False
```

External hypotheses: none new (`SizeTendsto sz0`, `RangeCond` merged; limit check: `N_n = 2097152(n+1)^18 → ∞`, `N_n^{-1/2} ≤ 1/2` for `n ≥ 0` as in merged `rangeCond_half`).

### Consumers (RBM2D, `c9a24cf`)

`grep` of `qErrQN|sum_weighted_q` over `Induction/Alt*.lean` outside `AltGridQ`: `AltProxyQ` and `AltDriftQ` do not use it. Users: `AltEnd.lean:812` (general `k`, `D_t := k+1`, rows `hrow1-4` stated with `((k+1)+k)` i.e. `D_t+k`, `C_K := altCK …`, `τ_K=1`), `AltEnd.lean:1591` and `AltBudget.lean:687` (`k=4`, `C_K=138`, `D_t=5`, `τ'=τ_K=1/2`), all at `m = K n`, in the form `Σ_{j<K n}(1+(1-u_{K n})⁻¹)^k qErrQN_j ≤ N^{-D_t}` (`BudgetAlt` hypothesis, `AltEnd.lean:601`). So the `D_t+k` row form matches the consumers; in RBM3D the consumer's `k` is `m+1`.

### Verdicts
- Target 1 (`sum_weighted_qErrQN_le`): **PASS**, with these corrections to the ticket: decay exponent `D_t+m+1` (not `D_t+m`); extra fixed constants `C, C₂ ≥ 0`; no `STKbound`; sum length renamed (tensor index is `m`); no RBM2D pin to copy.
- Target 2 (instance): **PASS** at the data of (ii) (`C_K=31`, new grid `N^{31}`); nothing left as hypothesis.

## (b) Script output — 2026-10-04 19:17:05 UTC

```
$ lake build RBM3D.Induction.QGridB 2>&1 | grep -v Replayed | tail -6   (worktree RBM3D-wt/T2156, branch t/T2156)
info: RBM3D/Induction/QGridB.lean:741:0: 'RBM.Ind.sum_weighted_qErrQN_le' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:742:0: 'RBM.Ind.QGridBCheck.Kc31' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:743:0: 'RBM.Ind.QGridBCheck.Kc31_ne_zero' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:744:0: 'RBM.Ind.QGridBCheck.rpow_31_le_Kc31' : [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/QGridB.lean:745:0: 'RBM.Ind.QGridBCheck.sum_weighted_qErrQN_instance' : [propext, Classical.choice, Quot.sound]
Build completed successfully (3795 jobs).
$ lake build   (full library, worktree)
Build completed successfully (3920 jobs).
lake build  1.36s user 3.03s system 225% cpu 1.941 total
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/QGridB.lean ; echo exit $?
exit 1
$ git diff --stat main...t/T2156
 RBM3D/Induction/QGridB.lean | 745 ++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 745 insertions(+)
$ git log -1 --format='%h %an <%ae>'
07cb977 Jun Yin <321276894+JYin80@users.noreply.github.com>

$ sed -n '565,580p' RBM3D/Induction/QGridB.lean   (target statement)
theorem sum_weighted_qErrQN_le (d : ℕ) (sz : Sizes d) {κ τ' τK C_K D_t C C₂ : ℝ}
    {E s t : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hκ : 0 < κ) (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hτK : 0 < τK) (hDt : 0 ≤ D_t) (hm : 1 ≤ m)
    (hsize : sz.SizeTendsto)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hK0 : ∀ n, K n ≠ 0) (hrange : sz.RangeCond τ' t)
    (h1 : 8 + (4 * ((m : ℝ) + 1) + 8) * (1 - τ') + 2 * (D_t + ((m : ℝ) + 1)) < C_K)
    (h2 : 3 + 4 * τK + 5 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K)
    (h3 : 2 * (1 - τ') + τK + 2 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K)
    (h4 : 1 - τ' < C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          qErrQN sz E s t K n m C C₂ (((sz.size n : ℕ) : ℝ) ^ τK *
            (etaT (E n) (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by

$ sed -n '717,726p' RBM3D/Induction/QGridB.lean   (compiled nonempty instance, all hypotheses discharged)
theorem sum_weighted_qErrQN_instance :
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ Kc31 n,
      ∑ j ∈ Finset.range p,
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc31 n p)⁻¹) ^ (3 + 1) *
          qErrQN sz0 E1 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc31 n 3
            ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) Kc31 n
                (j + 1)))⁻¹ ^ (3 + 1)) j ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
$ sed -n '727,736p' RBM3D/Induction/QGridB.lean
  sum_weighted_qErrQN_le 3 sz0 (κ := 1) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 31) (D_t := 1)
    (C := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (C₂ := 1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
    (E := E1) (s := fun _ => 0) (t := fun _ => 1 / 2) (K := Kc31) 3 (by positivity)
    (by positivity) one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sz0_tendsto (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun _ => by norm_num) Kc31_ne_zero rangeCond_half (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Eventually.of_forall rpow_31_le_Kc31)

end QGridBCheck


$ grep -rnE 'sum_weighted_qErrQN_le|sum_weighted_qErrQN_instance|QGridBCheck|qGridB_|Kc31' /Users/junyin/Lean_proof/RBM3D/RBM3D /Users/junyin/Lean_proof/RBM3D/RBM3D.lean | grep -v QGridA.lean:36
(no match; exit 1)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/AltGridQ.lean | tail -2
 RBM2D/Induction/AltGridQ.lean | 272 ++++++++++--------------------------------
 1 file changed, 63 insertions(+), 209 deletions(-)
```

Narrative (facts from the file and the log above).
- New file `RBM3D/Induction/QGridB.lean` (745 lines, one commit 07cb977 on `t/T2156`; `git diff --stat main...t/T2156` touches only it). `Test/Axioms.lean` untouched (no registry line: no new frozen premise, no `STKbound`).
- Port of RBM2D `Induction/AltGridQ.lean:1680-2262` at `c9a24cf` (RBM2D HEAD `9e0f275`; the file has changed since, the diff-stat is above). Ported with adaptation: `binom_rem`, `uStepC_nonneg/le`, `qStepErrN_split`, `extra_le`, `mono`, `eventually_le`, `exists_c`, `extra_sum_le`, and the main theorem; all private helpers carry the prefix `qGridB_`.
- Changes against RBM2D: `Z2 ↦ Zd d`, `sz : Sizes d`, `W²L² = N ↦ W^d L^d = N`, `Lp = (L^d)^m ≤ N^m`, `k = m+1` (hypothesis `hk : k = m+1` in the private lemmas), sum length renamed `p`, `spectralM ↦ mE`. The merged `qStepErrN` carries constants `C, C₂` (`QGridA.lean:1339`): the four terms of the `Δ²`-part give `Δ² a_Q N^k Q² H²` with `a_Q = C(10k³+4(k+k2^k)+2k)+2C₂` (`qGridB_aQ`, re-derived, not copied).
- Exponent rows (arithmetic, `θ = 1-τ'`, `k = m+1`, `D' = D_t+k`): R1 `8+(4k+8)θ+2D'`, R2 `3+4τ_K+5kθ+D'`, R3 `2θ+τ_K+2kθ+D'`, R4 `θ`, all `< C_K`; the `Δ²`-part needs `k+2τ_K+(3k+2)θ+D_t < C_K`; the proof derives it from R2 (`R2 - Rx = 3+2τ_K+(2k-2)θ > 0`, `nlinarith` step `hef`). At `d = 3`, `m = 3`, `τ'=τ_K=1/2`, `D_t=1`: rows `30, 20, 10.5, 0.5 < C_K = 31` (the instance discharges them by `norm_num`). The dimension `d` enters only through `N`, so the rows are those of the preflight table (a)(i).
- Decay exponent applied to the merged `sum_weighted_stepErrN_le`: `D_t + (m+1)` (the ticket text says `D_t + m`; with `m` the product `(1+C)N^m N^{-(D_t+m)} = (1+C)N^{-D_t}` cannot be `≤ N^{-D_t}/2`; the file proves the version with `D_t+(m+1)` and uses `N ≥ 2(1+C)` eventually). This is as (a) states; (a) needed no correction, so there is no section (a′).
- No `STKbound` hypothesis (as (a) says): the sum theorem is deterministic.
- The instance uses a new grid `K n = N_n^{31}` (`Kc31`), because the merged `Kc = N^{21}` is too small for row R1 (`30`).

## (c) Verified Mathlib names (all compile in `QGridB.lean`)
`one_add_mul_le_pow`, `Nat.lt_two_pow_self`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `pow_le_one₀`, `inv_le_one_of_one_le₀`, `le_self_pow₀`, `inv_le_comm₀`, `inv_anti₀`, `div_le_iff₀`, `le_of_mul_le_mul_left`, `one_div_le_one_div_of_le`, `div_le_div_of_nonneg_right`, `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.one_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.sqrt_le_sqrt`, `tendsto_rpow_atTop`, `Filter.Tendsto.eventually_ge_atTop`. Names verified absent: none checked.

## (d) Open issues and paper-delta candidates
- **T2156a**: statement carries fixed constants `0 ≤ C`, `0 ≤ C₂` (arguments of the merged `qStepErrN`), quantified before `∀ᶠ n`; RBM2D has none. At the merged `gridDriftQN` values (`C = (1+40dm)6^{dm}`, `C₂ = 1000(1+dm)²`) the instance applies it.
- **T2156b**: decay exponent `D_t + (m+1)` in the four rows (ticket: `D_t + m`); RBM2D uses `D_t + k`.
- **T2156c**: no `STKbound` hypothesis (ticket: "with the hypothesis `STKbound`"); `STKbound` enters at the consumer via `gridDriftN_envelope`. Not a stronger or weaker statement than RBM2D's: the statement is the same deterministic one.
- The tensor index is `m ≥ 1` (`hm : 1 ≤ m`), loop length `m+1 ≥ 2`; the conclusion is for all `p ≤ K n` (RBM2D `m ≤ K n`).
- Consumers (S3-14, S3-15a) use the form `Σ_{j<K n}(1+(1-u_{K n})⁻¹)^{m+1} qErrQN_j ≤ N^{-D_t}` with `p = K n`; the rows must then be applied with `D_t + (m+1)` (preflight (a) "Consumers").
