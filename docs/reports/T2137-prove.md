Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 15:31:58 UTC 2026

Notation: `n` = the paper's loop length (Lean `k`), `B = sz.Bctl n u = W^{-d}B_{u,0}`, `η = etaT (E n) u`, `S = SB d (L n) (lam n)`, `maxL_m = STmaxL … m`, `Ξ̂_m = STXiL … m = 1 + maxL_m/B^{m-1}`, `Ξ̂^{LK}_m = STXiLK … m = 1 + maxLK_m/B^m`.

### (i) Exponent table
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | `STegt` cut loop `I.cutGlue j b` (`GLoopFlow.lean:317`) | length `n+1`, pair `(σ_j,b)` at position `j` (`σ' = σ.take j ++ σ.drop (j-1)`) | `STContract` (1st conjunct) sums the LAST label, so rotate `j` steps (`loopL = trace ∏ Gres·Eblk`, trace cyclicity) | needs a `loopL` rotation lemma (private copies exist: `DecayLoopB.lean:946`, `B45.lean:1044`, `DecayLoopA.lean:270`; port, name `SEforLn1_…`) |
| 2 | contraction index | `m = n+1`, `k' = (n+1)/2 = ⌈n/2⌉` | `1 ≤ k'`, `k'+1 ≤ m` | `n ≥ 2`: `m - (k'+1) = n-k' ≥ 1` |
| 3 | lengths from contraction | `(2k'-1, 2m-2k'-1) = (n-1,n+1)` (n even), `(n,n)` (n odd) | `= STn12E n` exactly | 0 (exact match, both parities, `n ≥ 2`) |
| 4 | part (1) power of `B` | `W^d · B^1 · (W^dη)^{-1} · (B^{n1-1}·B^{n2-1})^{1/2} = B^{1+(n1+n2)/2-1}` | target `B^n/η` | `n1+n2 = 2n` both parities: exponent exactly `n`, slack 0; `W^d·(W^dη)^{-1} = η^{-1}` |
| 5 | `tr(G̃E_a)` bound | `‖STavgErr‖ = ‖𝓛^{(1)}-𝒦^{(1)}‖ ≺ B^1` (`STAvgU`, `STKloop` at length 1 `= mSigma E σ`, `KLgen` len-1 clause) | uniform in `(u,σ,a)`: bad set `∃p` inside `Prec` (`badSetAt`), so no extra union bound over `a` | none needed; `STAvgU` is already uniform (in `STStep2Concl.2.1`) |
| 6 | `≺` losses | loss `N^{τ}`; constant `C = n` (sum over cut edge `j=1..n`) | use `STAvgU` at `τ/2`; `n ≤ N^{τ/2}` eventually | any `τ>0`: threshold in `N` depends on `n,τ` only |
| 7 | `Ξ̂` conversion | `maxL_m = B^{m-1}(Ξ̂_m-1) ≤ B^{m-1}Ξ̂_m` | needs `B>0` (`st_Bctl_pos`, `u<1`) | `B>0` strict for all `n` |
| 8 | `S` row/column sums | `Σ_a S_ab = Σ_b S_ab = (1+2dg²)^{-1}+2d·g²(1+2dg²)^{-1} = 1`, entries real `≥ 0` | `L ≥ 3` (the `2d` neighbours at `zdistD = 1` distinct), any real `g` | `L_n ≥ 3` (`three_le_L`); script: row/col sums `=1` at `d=3,L=5` |
| 9 | part (2) piece lengths | `lenR = l'-k+1`, `lenL = k+n-l'+1`, `lenL+lenR = n+2` | `K`-piece length `l ≥ 3` ⇒ `(L-K)`-piece length `n+2-l = k-l+2 ∈ [2, k-1]` | `l ≤ k`: index `k-l+2 ≥ 2`; nat. subtraction safe |
| 10 | part (2) power of `B` | `W^d · B^{k-l+2}(Ξ̂^{LK}_{k-l+2}-1) · (W^dη)^{-1}B^{l-2}` (`STKward` at length `l`) | target `B^k η^{-1} Ξ̂^{LK}_{k-l+2}` | exponent `(k-l+2)+(l-2) = k`, slack 0; `(eq:bcal_k)` (`STKbound`) is NOT needed on this route |
| 11 | part (2) number of terms | `(cut k<l', order) pairs ≤ k(k-1)` | constant | `≤ N^{τ/2}` eventually |
| 12 | which label `STKward` sums | `K`-piece `= cutGlueR k l' b`: last label `b` (direct). `K`-piece `= cutGlueL k l' a`: `a` at position `k < l`, NOT last | rotate `k` steps with `KLK_rotate` (`KLUnique.lean:604`: `3≤L, 1≤W, |E|<2, t∈[0,1)`, one step per application) | needed only in the second order of `STksimLK`; script: `max|K-K∘rot|=3.8e-20` |
| 13 | `STKward` is per time sequence `τ`; targets are uniform on `TimeIcc s t` | route A: `stKward_timeIcc` (`KDecay.lean:1081`) with `hd, κ>0, gmax>0, SizeTendsto, ∀ᶠ|E n|≤2-κ, ∀ᶠ 0<lam n≤gmax, 0≤s, s≤t, t<1` | `STFlow` gives them: `SizeTendsto` from `Admissible`, `|E|≤2-κ` and `lam ≤ 𝔡⁻¹` (`KLFinal_flowE/flowLam`, PRIVATE, `KLFinal.lean:286,294`: re-prove), `t<1` from `t ≤ lemT z < 1` (`lemT_lt_one`) | route B: use the hypothesis `STKward` + the generic per-time→`TimeIcc` bridge (`KDecay_prec_timeIcc`, private). Either route; DECISIONS §39 precedent satisfied |
| 14 | deterministic inputs at time `u` | `|E n| ≤ 2-κ < 2`, `0 ≤ s ≤ u ≤ t ≤ lemT(z n) < 1` ⇒ `etaT > 0` | hypotheses of `stContract_holds`/`KLK_rotate` | slack `κ`, and `1-lemT>0` |
| 15 | hypotheses of `STSEforLn` NOT used by parts 1,2 | `STKbound, STLK, STConStInd, STLocalEntryU, STGdecayW` | carried as unused hypotheses | parts 3,4 (S3-09) use them |
| 16 | list/`Fin` bridge | cut pieces `⟨σ',a'⟩` have `σ'.length = a'.length = m` | to apply `STmaxLK`/`STKward` (Fin-form) | bookkeeping only |

Part (1) hypotheses used: `STAvgU` (uniform), `stContract_holds`, flow facts (row 14), `S` sums (row 8), `loopL` rotation (row 1). Part (2): `STKward` (row 13), `KLK_rotate` (row 12), `S` sums, definition of `Ξ̂^{LK}`. No `Ξ̂` hypothesis is needed (the `Ξ̂` are random controls; the bounds are deterministic given `S`, `STKward`).
Neither pinned conjunct is false: exponents of `B`, the `η^{-1}` and `(n1,n2)=STn12E` close exactly (rows 3, 4, 10).

### (ii) One concrete nondegenerate instance
(A) Deterministic inequalities of the proof, sampled `H`, `d=3, L=5, W=1, g=1/2, E=0, u=1/2` (`W^d=1`, so this checks the inequalities, not the `≺` asymptotics). `maxL_m` exact (max-times DP over all `(σ,a)`), `maxLK_{2,3}` exact, `LHS` = max over sampled `(σ,a)` (all `2^k` signs, 20 / 6 label samples each), `STegt`/`STksimLK` implemented from `Step34Pins.lean:144,120` verbatim (`cutGlue`, `cutGlueL/R`, `KLK` tree sums for `n=3,4` via `TSP 3 = {∅}`, `TSP 4`).
Command: `python3 scratchpad/T2137/check.py`
```
d=3 L=5 W=1 g=0.5 E=0.0 u=0.5: V=L^d=125, m(+)=1j, z_u=0.5j, eta_u=0.5, B=W^-d B_(u,0)=1.349333
self-consistency -1/m = z_u + u*m : 1j 1j
loop formula = tr prod G E_a: ok
max |K - K∘rot|, |L - L∘rot| over 40 random loops (n=3,4): 3.83e-20
max_{sigma,a}|L^(m)| m=1..5: {1: 1.653659, 2: 2.734587, 3: 4.522073, 4: 7.477965, 5: 12.366001}
max_{sigma,a}|(L-K)^(m)| m=2,3: {2: 2.048772, 3: 4.019873}
max_a |tr(G~ E_a)|: {True: 0.9183758074406291, False: 0.9183758074406294}, vs B = 1.349333

== Part (1): |E^{G~,(k)}| <= B^k/eta (Xi_n1 Xi_n2)^(1/2), n1,n2 = STn12E k ==
k=2 (n1,n2)=(1,3) contraction worst ratio(sampled)=0.932<=1 | #samples=80 max|E^G~|=1.9078e+00 | det. bound (A)=1.0046e+01 holds per-sample=True | RHS=B^k/eta (XiXi)^1/2=1.1072e+01 | LHS/RHS=0.1723
k=3 (n1,n2)=(3,3) contraction worst ratio(sampled)=0.729<=1 | #samples=160 max|E^G~|=5.1955e+00 | det. bound (A)=2.4918e+01 holds per-sample=True | RHS=B^k/eta (XiXi)^1/2=1.7117e+01 | LHS/RHS=0.3035
k=4 (n1,n2)=(3,5) contraction worst ratio(sampled)=0.842<=1 | #samples=320 max|E^G~|=1.0167e+01 | det. bound (A)=5.4941e+01 holds per-sample=True | RHS=B^k/eta (XiXi)^1/2=2.6914e+01 | LHS/RHS=0.3778

ward (wardineq_K) l=3 exact: max sum_x|K^(3)| = 2.12342; (W^d eta)^-1 B^(l-2) = 2.69867; ratio 0.7868
ward l=4 sampled (300): max sum_x|K^(4)| = 0.03694; (W^d eta)^-1 B^2 = 3.64140; ratio 0.0101
== Part (2): |[K^(l)~(L-K)]^(k)| <= B^k/eta Xi^{LK}_{k-l+2} ==
k=3 l=3 piece len k-l+2=2: #samples=48 max|ksim|=7.8221e-01 | RHS=B^k/eta Xi^LK_2=1.0442e+01 | LHS/RHS=0.0749 | #(cut,order) terms=3
      det. bound W^d*#terms*max|(L-K)^(2)|*max_sum|K^(3)| = 1.3051e+01 ; LHS<=A2: True
k=4 l=3 piece len k-l+2=3: #samples=96 max|ksim|=7.4506e+00 | RHS=B^k/eta Xi^LK_3=1.7478e+01 | LHS/RHS=0.4263 | #(cut,order) terms=4
      det. bound W^d*#terms*max|(L-K)^(3)|*max_sum|K^(3)| = 3.4144e+01 ; LHS<=A2: True
k=4 l=4 piece len k-l+2=2: #samples=96 max|ksim|=4.0794e+00 | RHS=B^k/eta Xi^LK_2=1.4090e+01 | LHS/RHS=0.2895 | #(cut,order) terms=4
done
```
(B) Lean-level data (merged `sz0`, `z0`, `s ≡ 0`, `t ≡ 1/16`, `κ=ε=𝔡=1/10`, `𝔠=1/6`; `STFlow` = `flow_z0`; `d=3`), checked at `n = 0,1,2,10`, with the external hypothesis `(con_st_ind)` and the `k=1`, `l=2` bulk limits (TEAM §8 lesson 14). `STKbound, STKward, STLK, STStep2Concl` stay hypotheses of the compiled instance.
Command: `python3 scratchpad/T2137/inst.py`
```
n L W lam N | locDomain(|Re z|<=1.9, N^-0.9<=Im z<=1) | N^(1/6)<=W | W^(-1.4)<=lam<=10 | s<t<=lemT | |E_n|<2 | Bctl(n,t)
0 4 32 1.562e-02 2097152 True True True True E=0.5000 lemT=1.0000 Bctl=3.305e-05
1 8 1024 2.441e-04 549755813888 True True True True E=0.5000 lemT=1.0000 Bctl=9.954e-10
2 12 7776 2.143e-05 812479653347328 True True True True E=0.5000 lemT=1.0000 Bctl=2.270e-12
10 44 5153632 8.820e-09 11659991713824860234842112 True True True True E=0.5000 lemT=1.0000 Bctl=7.793e-21
self-consistency -1/m(E) = z_t + t m(E) at E=lemE(z0_n), t=1/16, n=0,1,2,10: ok
con_st_ind with c_d=0.01: holds from n=0 on (checked n=0..499: True); limit: log Bctl ~ -15 log(2(n+1)) -> -inf
con_st_ind with c_d=0.001: holds from n=37 on (checked n=37..536: True); limit: log Bctl ~ -15 log(2(n+1)) -> -inf
k=1: K^(1)_sigma = m(sigma) = +-i; M=m(E) I solves -1/m = E+m: 1j 1j
l=2 ward: max_sigma sum_x|K^(2)| = W^-d/(1-u) = 2.0  vs (W^d eta)^-1 = 2.0  (equal at E=0: Im m=1); (+,+):  0.6666666666666666
```
`Bctl ≤ 2(1-c)^{-1}W^{-3}` (`Bctl_const_le_gen`, `Induction/Defs.lean:450`) gives `Bctl → 0`, so `(con_st_ind)` holds eventually for every `𝔠_d > 0`; the `k=1` limit is consistent (`K^{(1)} = m(σ)`, `-1/m = z_t + t m`), and `l=2` ward is an equality at `E=0` (`Σ_x|K^{(2)}_{+,-}| = (W^dη)^{-1}`).

## Verdicts
* Target 1 `stSEforLn_part1` (first conjunct of `STSEforLnConcl`): PASS. Exponents close with slack 0 (rows 3,4); inputs `STAvgU` (uniform), `stContract_holds`; script LHS/RHS = 0.17, 0.30, 0.38 for `k=2,3,4` and the deterministic bound (A) holds on every sample.
* Target 2 `stSEforLn_part2` (second conjunct, `3 ≤ l ≤ k`): PASS. Exponent `k` exact (row 10); needs `KLK_rotate` for the second order (row 12) and a uniform-in-`u` ward input (row 13); script LHS/RHS = 0.07, 0.43, 0.29 for `(k,l) = (3,3),(4,3),(4,4)`; `(4,4)` has no exact intermediate bound (ward for `l=4` only sampled).

## (b) Script output - Sun Oct  4 15:51:29 UTC 2026
```
$ git log -1 --format='%h %cI %an: %s'; git diff --stat main...t/T2137 | cat
2a7a856 2026-10-04T08:48:13-07:00 Jun Yin: T2137: S3-08 Induction/SEforLn1 (lem:SEforLn parts (1) and (2): stSEforLn_part1, stSEforLn_part2)
 RBM3D/Induction/SEforLn1.lean | 804 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 804 insertions(+)
```
```
$ lake build RBM3D.Induction.SEforLn1 2>&1 | grep -v '^info' | tail -3
Note: This linter can be disabled with `set_option linter.style.longLine false`
ℹ [3766/3768] Replayed RBM3D.Induction.HierAlgebra
Build completed successfully (3768 jobs).
```
```
$ lake env lean scratchpad/T2137/ax.lean   # imports RBM3D.Induction.SEforLn1; #print axioms of both targets
'RBM.Gauss.Sizes.stSEforLn_part1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stSEforLn_part2' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Induction/SEforLn1.lean || echo 'no matches'
no matches
```
```
$ scratchpad/T2137/extract.sh   # the two target statements, extracted from the file
theorem stSEforLn_part1 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hAvg : STAvgU sz (STflowE z) s t) (k : ℕ) (hk : 2 ≤ k) :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegt sz n (STflowE z n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (STflowE z n) (p.1 : ℝ) *
        (STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12E k).1 ω *
          STXiL sz n (STflowE z n) (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ)) :=

theorem stSEforLn_part2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (k : ℕ) :
    ∀ l : ℕ, 3 ≤ l → l ≤ k →
      Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STksimLK sz n (STflowE z n) (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (STflowE z n) (p.1 : ℝ) *
          STXiLK sz n (STflowE z n) (p.1 : ℝ) (k - l + 2) ω) := by
```
```
$ scratchpad/T2137/examples.sh   # every `example` of the file (section 7), extracted
example (n : ℕ) :
    Nonempty (TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n))) :=
  ⟨⟨0, by simp [sInst, tInst]⟩, fun _ => true, fun _ => 0⟩

example : STn12E 2 = (1, 3) := by decide
example : STn12E 3 = (3, 3) := by decide

example (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STegt sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 2 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 1 ω * STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω) ^
          (1 / 2 : ℝ)) :=
  stSEforLn_part1 sz0 flow_z0 sz0_hs0 sz0_ht hAvg 2 le_rfl

example (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STegt sz0 n (STflowE z0 n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 3 / etaT (STflowE z0 n) (p.1 : ℝ) *
        (STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω * STXiL sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω) ^
          (1 / 2 : ℝ)) :=
  stSEforLn_part1 sz0 flow_z0 sz0_hs0 sz0_ht hAvg 3 (by norm_num)

example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STksimLK sz0 n (STflowE z0 n) (p.1 : ℝ) ω 3 ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 3 / etaT (STflowE z0 n) (p.1 : ℝ) *
        STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 2 ω) :=
  stSEforLn_part2 (by norm_num) sz0 (κ := 1 / 10) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht 3 3
    le_rfl le_rfl

example :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 4 → Bool) × (Fin 4 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STksimLK sz0 n (STflowE z0 n) (p.1 : ℝ) ω 3 ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz0.Bctl n (p.1 : ℝ)) ^ 4 / etaT (STflowE z0 n) (p.1 : ℝ) *
        STXiLK sz0 n (STflowE z0 n) (p.1 : ℝ) 3 ω) :=
  stSEforLn_part2 (by norm_num) sz0 (κ := 1 / 10) (by norm_num) flow_z0 sz0_hs0 sz0_hst sz0_ht 4 3
    le_rfl (by norm_num)

example {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ lemT (z n))
    (hAvg : STAvgU sz (STflowE z) s t) (hconcl : STSEforLnConcl sz (STflowE z) s t) (k : ℕ)
    (hk : 2 ≤ k) :
    stSEforLn_part1 sz hflow hs ht hAvg k hk = (hconcl k hk).1 := rfl

example {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht : ∀ n, t n ≤ lemT (z n)) (hconcl : STSEforLnConcl sz (STflowE z) s t) (k : ℕ)
    (hk : 2 ≤ k) :
    stSEforLn_part2 hd sz hκ hflow hs hst ht k = (hconcl k hk).2.1 := rfl
```
```
$ grep -nE '^(theorem|def|lemma|abbrev|structure|instance|noncomputable def) ' RBM3D/Induction/SEforLn1.lean   # all public declarations
466:theorem stSEforLn_part1 (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
702:theorem stSEforLn_part2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ)
```
```
$ git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks grep -n -E 'stSEforLn_part|SEforLn1Inst|SEforLn1_' main -- 'RBM3D/*.lean' 'RBM3D.lean'; echo exit=$?
exit=1
```
```
$ registry pre-check: root import added temporarily, lake build (full), root restored; grep of the output
info: RBM3D.lean:185:0: axiom audit: 4194 theorems, 1438 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STAvgU: 3 [no certificate]
registry: 1 borrowed + 74 owed + 39 structural; 44 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3886 jobs).
lines containing 'unregistered': 0
```

Narrative.
* `RBM3D/Induction/SEforLn1.lean`, 804 lines, one commit on `t/T2137`; two public theorems, 36 `private theorem`s prefixed `SEforLn1_`, no private `def`. The build run after the last edit printed `✔ [3768/3768] Built RBM3D.Induction.SEforLn1 (4.0s)` with no warning from this file.
* Design: a deterministic bound for every `(n, E, τ, ω)` with `|E| < 2`, `0 ≤ τ < 1` (§1-§3, §5 of the file), then `≺` by inclusion of the bad events: `SEforLn1_of_subset` (the proof of `StochDomAt.of_subset`, `StochDomAt.lean:325`, with a source family indexed differently from the target), exponent `τ/2`, and eventually `2k² ≤ N^{τ/2}` (`eventually_le_rpow`), `N^{τ/2} N^{τ/2} = N^τ`.
* Part 1: `STegt` is `W^d Σ_{j ≤ k} Σ_{a,b} avgErr · S_ab · STLI(cutGlue j b)`; the column sums of `S` (`SEforLn1_sum_glue_left`) leave `δ Σ_b |STLI(cutGlue j b)|`, `δ = N^{τ/2} B` from `STAvgU` at `(u, σ_j, a)` (`SEforLn1_avgErr_eq`). The new label `b` sits at position `j`, so the loop is rotated by `j` (trace cyclicity, `SEforLn1_cut_rotate`, `SEforLn1_STLI_rotate`) and `stContract_holds` (first conjunct) is applied at `m = k+1`, `k' = (k+1)/2`; its lengths `(2k'-1, 2m-2k'-1)` equal `STn12E k` for both parities (`SEforLn1_n12`). With `max L_m ≤ B^{m-1} Ξ̂_m` and `n₁ + n₂ = 2k` the exponent is `B · B^{k-1} = B^k`, and `W^d (W^d η)⁻¹ = η⁻¹` (`SEforLn1_det_egt`, `SEforLn1_R_le`, `SEforLn1_arith1`).
* Part 2: for each cut pair `k < l'` the lengths of the two pieces add to `m + 2` (`LoopIdx.length_cutGlueL/R`). If the `𝒦`-piece is `cutGlueR` its summed label is last and the Ward bound applies (`SEforLn1_sum_cutGlueR_K`); if it is `cutGlueL` the label is at position `k < l` and the loop is rotated by `k` with `KLK_rotate` (`SEforLn1_STKI_rotate`, `SEforLn1_sum_cutGlueL_K`). Row/column sums of `S` give `≤ W^d m² · 2 · max|(𝓛-𝒦)^{(m+2-l)}| · Kw` (`SEforLn1_det_ksim`); `Kw` comes from `stKward_timeIcc` (route A of (a) row 13), exponent `(k+2-l) + (l-2) = k` (`SEforLn1_arith2`).
* The `STFlow` consequences (`Im z > 0`, `|E| < 2`, `|E| ≤ 2 - κ`, `t < 1`, `0 < lam ≤ 𝔡⁻¹`) are re-derived inline (`KLFinal_flowE`, `KLFinal_flowLam` are private).
* Relative to section (a): no verdict changes, so no (a′). Hypotheses: (a) row 15 planned to carry `STKbound, STLK, STConStInd, STLocalEntryU, STGdecayW` as unused hypotheses and row 13 allowed either route for `STKward`; none of them is a hypothesis of either theorem (more general statements, S3-09 passes fewer arguments). `hst : s < t` is only in part 2 (for `stKward_timeIcc`), `2 ≤ k` only in part 1 (`3 ≤ l ≤ k` implies it in part 2). The two `rfl` examples show the conclusions are definitionally the first two conjuncts of `STSEforLnConcl sz (STflowE z) s t` at `k`.
* Ports: no text copied from RBM1D/RBM2D (RBM2D `Induction/BcalE.lean` lines 1-300 were read for the plan; its window method is not used), so no RBM1D/RBM2D `diff --stat` applies. Same-project copies of private lemmas: `DecayLoopB.lean:931,946,957` (`loopL` rotation), `:507` (`loopOf_eq`), `:555` (`sum_pairs`), `:1748` (`STLKI_eq`), under the prefix `SEforLn1_`.
* Registry pre-check (root import added temporarily, restored afterwards): full `lake build` completed, `4194 theorems, 0 axioms`, no unregistered premise (audit line `STAvgU: 3`). The premise predicates in the hypotheses of the two theorems are `STFlow` (structural, `Test/Axioms.lean:197`) and `STAvgU` (owed, `:117`), both registered. `RBM3D/Test/Axioms.lean` is unchanged; the root import is for the hub.
* The hypothesis `STAvgU` of part 1 (another gate's output, `STStep2Concl.2.1`) stays a hypothesis of the part-1 examples; its limit check is (a)(ii)(B): `K^{(1)}_σ = m(σ)`, `-1/m = z_t + t m`. Every other hypothesis is discharged at `d = 3` (`sz0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `κ = 1/10`).

## (c) Verified Mathlib and core names (script: `#eval` of `getModuleIdxFor?` for each name, file `scratchpad/T2137/names.lean`)
```
List.ofFn_get : Mathlib.Data.List.OfFn
List.ofFn_getElem : Init.Data.List.OfFn
List.ext_getElem : Init.Data.List.Lemmas
List.rotate_cons_succ : Mathlib.Data.List.Rotate
List.rotate_eq_drop_append_take : Mathlib.Data.List.Rotate
List.drop_left' : Init.Data.List.TakeDrop
List.take_left' : Init.Data.List.TakeDrop
List.zip_append : Init.Data.List.Zip
Matrix.trace_mul_comm : Mathlib.LinearAlgebra.Matrix.Trace
Real.rpow_le_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.mul_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.sqrt_eq_rpow : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.sqrt_sq : Mathlib.Analysis.Real.Sqrt
Real.rpow_nonneg : Mathlib.Analysis.SpecialFunctions.Pow.Real
Real.rpow_pos_of_pos : Mathlib.Analysis.SpecialFunctions.Pow.Real
Finset.le_sup' : Mathlib.Data.Finset.Lattice.Fold
norm_sum_le : Mathlib.Analysis.Normed.Group.Basic
norm_add_le : Mathlib.Analysis.Normed.Group.Basic
Nat.card_Icc : Mathlib.Order.Interval.Finset.Nat
Nat.card_Ioc : Mathlib.Order.Interval.Finset.Nat
ite_true : Init.SimpLemmas
mul_div_cancel₀ : Mathlib.Algebra.GroupWithZero.Units.Basic
Finset.sum_comm : Mathlib.Algebra.BigOperators.Group.Finset.Sigma
```
Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
* No open issue for the two targets. Parts (3), (4) and the assembly `STSEforLn` are S3-09; `stSEforLn_part1` still rests on the owed `STAvgU` (Step 2 chain).
* `T2137a` (proof detail, no statement difference): `(yi2oslxj2)` sums the last label, but in `(bEwGn)` the glued label `b` of `cut_k^{(b)}` sits at position `k`; the text of the proof (`3_5:1048-1053`) does not mention the cyclic rotation by `k` that the Lean proof uses.
* `T2137b` (proof detail, no statement difference): in `(eq:KsimL-K)` the second order of `[𝒦^{(l)} ∼ (𝓛-𝒦)]` has the summed label at position `k < l`; `(wardineq_K)` is applied after cyclic invariance of `𝒦` (`KLK_rotate`); the text of `3_5:1054-1061` does not mention it.
* `T2137c` (observation): the proof of `(eq:KsimL-K)` uses only `(wardineq_K)`; `(eq:bcal_k)`, cited at `3_5:1056`, is not needed (the loop count `≤ m²·2` is absorbed in `N^τ`).
