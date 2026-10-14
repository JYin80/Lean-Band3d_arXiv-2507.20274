Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 00:44:46 UTC 2026

Row b only (targets 10-15, `Chain/IterationsGen`, `Chain/IterationsGen2`). Restatement: target 14 = the merged R2* texts `STIterationsgL'`, `STIterationsIIgL'` (`Chain/NQEndFlowGen:140-149`) at `(mkM sz z).toFlowFM`; target 12 = the nine scale facts of band `IterationsAScale` (`IterationsA:1058`) with `etaT (E n)` read as `Cf.eta n`; target 11 = odd chain bound; target 13 = the step `iterationsB_step` with `hboot = STXiBootgL'`.

### (i) Exponent table (case (i): `A = STAI = lam² W^d`, `T = 2A⁻¹`, `cB = cv = K = 2`; case (ii): `A = STAII s = Bctl(s)⁻¹`, `T = A^{-1+𝔠d}`, `cB = cv = K = 1`; `ρ = η_s/η_u = (1-s)/(1-u)`)
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| `𝔠d` (pinned `∃`, before `(sz,z)`, no dependence on `κ ε 𝔡 Cd`) | `1/100` | `0 < 𝔠d ≤ 1/100` (`STIterRgL'`); `≤ 1/16` (`iterationsA_scale_I`, `IterationsA:1631`); `≤ 1/24` (`iterationsA_scale_II`, `:1704`) | `1/16 - 1/100 = 21/400`; `1/24 - 1/100 = 19/600` |
| case (i) `ρ² ≤ K A^{1/8}` | `ρ² ≤ (2A)^{2𝔠d} ≤ 2·A^{2𝔠d} ≤ 2A^{1/8}` | `2𝔠d ≤ 1/8`, `A ≥ 1`, `2^{2𝔠d} ≤ 2` | exponent `1/8 - 2/100 = 21/200` |
| case (i) `T ρ² A^{7/8} ≤ cB K` | `2A⁻¹ · 2A^{1/8} · A^{7/8} = 4` | `≤ cB·K = 4` | 0 (exact equality; no room, none needed) |
| case (i) `T A^{3/4} ≤ cB` | `2A^{-1/4}` | `≤ 2` for `A ≥ 1` | factor `A^{-1/4}` |
| case (i) `(cv A)⁻¹ ≤ B_w ≤ T` | `(2A)⁻¹ ≤ B_w ≤ 2A⁻¹` | upper: `L^d ≥ L²`, `d ≥ 2` (here `d ≥ 3`); lower: `1 - s ≤ lam²` | `L^d/L² = L^{d-2} ≥ 4` at `L = 4`, `d = 3` |
| case (ii) `ρ² ≤ K A^{1/8}` | `ρ² ≤ A^{2𝔠d}` | `2𝔠d ≤ 1/8` | `1/8 - 2/100 = 21/200` |
| case (ii) `T ρ² A^{7/8} ≤ cB K` | exponent `-1 + 3𝔠d + 7/8 = 3𝔠d - 1/8` | `≤ 0` | `1/8 - 3/100 = 19/200` (`𝔠d ≤ 1/24` is the sharp form) |
| case (ii) `T A^{3/4} ≤ cB` | exponent `-1 + 𝔠d + 3/4 = 𝔠d - 1/4` | `≤ 0` | `1/4 - 1/100 = 6/25` |
| case (ii) `B_w ≤ T = B_s^{1-𝔠d}`, `B_w ≥ B_s` | `scaleFacts_R2` (band, `ScaleFacts`), `STBctl_mono` | `STConStInd 𝔠d` | eventual in `n` |
| `STPsi A ρ n k` | `A^{3/4} + ρ^{n-1} A^{1-k/8}` | `A ≥ 1`; used at `(N,k)`, `(r,k)`, `(r,k-1)` | — |
| loop length `N`, level `k` | `N ≥ 2`, `k ≥ 1` (pin); odd bound needs `3 ≤ N` | chain lengths `2N-1`, `4p` of `STlenL` | `STlenL N (N+4) m` covers `m ≤ N+1 ∨ 2N-1 ∨ 4(N+4)` |
| martingale exponent `p` | `p = N + 4` | `iterationsA_boot_bound` needs `p ≥ 2`; `STXiBootgL'` allows `p ≥ 1` | `N + 4 - 2 ≥ 4` |
| `E'_n = 2√(1 - y_n²)`, `y_n = Im m_n` (E′ route, targets 12) | `Im mE(E') = y` (`GridEnvelopeGen_mE_im_Ep`), `|E'| < 2 ⇔ y > 0` | `0 < y` (`LoopForm` conjunct 1), `y ≤ 1` (inline `‖m‖ ≤ 1`, `NQGood1Gen_im_le_one`), `η_u = (1-u) y` (`NQGood1Gen_eta_eq`) so `etaT E' u = Cf.eta n u` | `y > 0` strict; `y = 1` gives `E' = 0` |
| mollifier `C`, `C₂`, four rows of 8 | n/a, because they belong to row a (targets 6-8) | — | — |
| comparison `gK` (UBA-C1, R1) | n/a, because targets 10-15 read only `sz.lam` (`STAI`, `STRegIterI`, `STCaseII`, `WO`, `Bctl`) | R1 never enters | — |
| file sizes (forecast `IterationsGen` ≈ 465, `IterationsGen2` ≈ 400-500; ticket :15) | stop line 2,000 | `wc -l < 2000` | `2000/465 = 4.3×`, `2000/500 = 4.0×` |

Hypothesis sources for the scale facts at a generic carrier, no `|E| < 2`: `WO 𝔡`, `SizeTendsto` from `Admissible` (`Step2EventsGen_Flow` conjunct 1); `t < 1` from `t ≤ T0 < 1` (conjunct 2, uses `0 < κ`, a premise of `STIterRgL'`); `Cf.eta n u = (1-u) Im m_n`, `Im m_n > 0` from `StepDecompGen_LoopForm` (family row 3); `Im m_n ≤ 1` from inline `‖m‖ ≤ 1` (row 4). The ratio fact `etaT E' s / etaT E' t = (1-s)/(1-t)` needs only `|E'| < 2` (`scaleFacts_etaT_div_etaT`, `ScaleFacts:342`). Odd chain bound (target 11) needs `Hf` Hermitian only (`loopMax_odd_sq_le`, `loopXi_le` take `H.IsHermitian`, no `z`-dependent hypothesis; `Split:598`, `:640`); `STXiLg = 1 + loopXi` follows from `Step34Gen_LCompat` + `LoopForm` conjuncts 2-3 at `ztOf`.

### (ii) One nondegenerate instance (target 14 at `szB`/`zB`, targets 12, 13 at the same data)
Data (file `Induction/Step34Pins.lean:710-790, 830-842`): `d = 3`, `L = 4`, `W_n = n + 4`, `lam = 1`, `size = (4(n+4))³ ≥ 4096`, `zB = 1/2 + i/64`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`, `Cd` any `> 0`; carrier `mkM = bandStep2Mat szB (STflowE zB)`, `Hf = seqHflow`, `Es = STflowE zB`, `T0 = lemT (zB n)`, law `seqP szB`; case (i) `(s,t) = (7/8, 15/16)`, case (ii) `(15/16, 31/32)`; `(N,k) = (3,2)`: `IH1` at `r = 2` (level 2), `IH2` at `r = 2..5` (level 1), both nonempty; `p = N+4 = 7`, chain lengths `5` and `28`. The script checks the numerical hypotheses (family rows 1, 3-4 numerically, regime inequalities, the nine scale facts on the sampled pairs, `STConStInd` threshold, exponent slacks); the Lean-level facts `flow_zB`, `szB_regIterI`, `szB_caseII`, `szB_flow_ht`, `lemT_zB` are theorems of the file `Step34Pins.lean`.
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2497b/inst.py
E=lemE(z)=0.499984 |E|<2:True  T0=lemT(z)=0.983992 >=31/32:True
m=mE(E)=-0.249992+0.968248j |m|=1.000000000000 Im m=0.968248 in (0,1]:True
E'=2sqrt(1-y^2)=0.499984 Im mE(E')=0.968247937632 (= Im m: True) |E'|<2:True
-- I (case i): s=0.875 t=0.9375 cB=2 cv=2 K=2
  1-s<=lam^2: True  lam^2/L^2<=1-t: True
  (1-t)/(1-s) = 0.5 <1 ; need Bctl(n,t)^cd <= that
  con_st_ind holds for all n >= 11472512971 (Bctl decreasing in n)
  n=0              A=64 1<=A:True rho^2<=K A^1/8:False T rho^2 A^7/8<=cB K:False T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
  n=3              A=343 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
  n=10             A=2744 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
  n=1000           A=1.012e+09 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
  n=1000000        A=1e+18 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
  n=100000000000   A=1e+33 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
-- II (case ii): s=0.9375 t=0.96875 cB=1 cv=1 K=1
  1-s<=lam^2/L^2: True
  (1-t)/(1-s) = 0.5 <1 ; need Bctl(n,t)^cd <= that
  con_st_ind holds for all n >= 12304834824 (Bctl decreasing in n)
  n=0              A=53.73 1<=A:True rho^2<=K A^1/8:False T rho^2 A^7/8<=cB K:False T A^3/4<=cB:True (cvA)^-1<=B_w<=T:False
  n=3              A=288 1<=A:True rho^2<=K A^1/8:False T rho^2 A^7/8<=cB K:False T A^3/4<=cB:True (cvA)^-1<=B_w<=T:False
  n=10             A=2304 1<=A:True rho^2<=K A^1/8:False T rho^2 A^7/8<=cB K:False T A^3/4<=cB:True (cvA)^-1<=B_w<=T:False
  n=1000           A=8.496e+08 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:False
  n=1000000        A=8.395e+17 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
  n=100000000000   A=8.395e+32 1<=A:True rho^2<=K A^1/8:True T rho^2 A^7/8<=cB K:True T A^3/4<=cB:True (cvA)^-1<=B_w<=T:True
case i : rho^2<= (2A)^(2cd) <= 2A^(1/8) needs 2cd<=1/8: cd<=1/16 slack 21/400
case ii: -1+cd+2cd+7/8<=0 needs cd<=1/24 slack 19/600 ; -1+cd+3/4<=0 slack 6/25
IH1 r in [2] level 2 | IH2 r in [2, 3, 4, 5] level 1 | chain lengths 2N-1 = 5 , 4p = 28 , p=N+4 >=2: True
```
External-hypothesis limit computation (TEAM §8 lesson 14): the only eventual hypothesis not given by a stochastic pin is `STConStInd 𝔠d s t`, `Bctl(n,t)^{𝔠d} ≤ (1-t)/(1-s) < 1`. At both cases `(1-t)/(1-s) = 1/2` (constant) and `Bctl(n,t) = (n+4)^{-3}(1/(lam²+1-t) + 1/(L³(1-t)))` tends to `0` as `n → ∞`, so `Bctl^{1/100} → 0 < 1/2`; the script's bisection gives the thresholds `n ≥ 11472512971` (case i) and `n ≥ 12304834824` (case ii). They are thresholds of an `∀ᶠ n` hypothesis (discharged in the file by `conStInd_const` through the limit), not a witness size of any target. In the script's sampled `n`, the scale facts' inequalities hold from `n = 3` (case i) and from `n = 10^6` (case ii) onward.

### Verdict
- Target 10 (`≺` at a law, `PrecL` ports; `st_one_le_XiLg`, `st_one_le_XiLKg`): PASS (no exponent; `PrecL sz μ` replaces `Prec sz`, proofs verbatim).
- Target 11 (odd chain bound): PASS (Hermitian `Hf` only; `3 ≤ N`).
- Target 12 (`IterationsAScaleg`, `iterationsA_scale_Ig/_IIg`, `avg/apriori/rela`): PASS (exponents close with the slacks above; E′ substitution feasible: `0 < y ≤ 1` from family rows 3-4).
- Target 13 (`iterationsB_stepg`): PASS (`hboot` = merged `STXiBootgL'`; `p = N+4 ≥ 2`).
- Target 14 (`stIterationsgL'_of`, `stIterationsIIgL'_of`): PASS (`𝔠d = 1/100` closes in both cases; bundle `T2497_IterFam` stays exactly as drafted, rows 1-6: no change needed; the instance above satisfies every deterministic hypothesis).
- Target 15 (instances of 13-14 at `szB`/`zB`): PASS (data above, nonempty `IH1`/`IH2`).
- Layout and rows: unchanged (two new files `IterationsGen`, `IterationsGen2`, forecast within 2,000); no 1a-audit needed.
## (b) Script output — Wed Oct 14 01:09:13 UTC 2026

### Build (worktree `RBM3D-wt/T2497b`, branch `t/T2497b`, HEAD `351c0e05`)
```
$ lake build RBM3D.Chain.IterationsGen RBM3D.Chain.IterationsGen2 2>&1 | tail -2
info: RBM3D/Chain/IterationsGen2.lean:601:0: 'RBM.BA.IterationsGen2Inst.inst_iterationsIIgL'' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3895 jobs).
$ lake build   # whole library incl. #assert_rbm_axioms, last run before the commit; tail -2 of its output
non-vacuity certificates: 0 of 122 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4374 jobs).
$ wc -l RBM3D/Chain/IterationsGen.lean RBM3D/Chain/IterationsGen2.lean
     633 RBM3D/Chain/IterationsGen.lean
     601 RBM3D/Chain/IterationsGen2.lean
    1234 total
```

### Axioms of every new public declaration (`lake env lean` on a scratch file of `#print axioms`, 26 declarations)
```
$ awk -F'depends on axioms: ' '{print $2}' ax.out | sort | uniq -c
  26 [propext, Classical.choice, Quot.sound]
```

### Target statements (script `stmts.py`: the declaration text from the file up to `:=`)
```
IterationsGen.lean:47
theorem st_prec_one_add_supg {U V : ℕ → Type*} [∀ n, Fintype (V n)] [hV : ∀ n, Nonempty (V n)]
    (hsize : Tendsto sz.size atTop atTop) (f : ∀ n, U n → V n → sz.SeqΩ → ℝ) (B : ∀ n, U n → ℝ)
    (hB : ∀ n u, 0 < B n u)
    (h : PrecL sz μ (U := fun n => U n × V n) (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1)) :
    PrecL sz μ (U := U)
      (fun n u ω => 1 + Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u)
      (fun _ _ _ => 1) := by
IterationsGen.lean:73
theorem st_prec_of_xig {U V : ℕ → Type*} [∀ n, Fintype (V n)] [hV : ∀ n, Nonempty (V n)]
    (f : ∀ n, U n → V n → sz.SeqΩ → ℝ) (B : ∀ n, U n → ℝ) (hB : ∀ n u, 0 < B n u)
    (h : PrecL sz μ (U := U)
      (fun n u ω => 1 + Finset.univ.sup' Finset.univ_nonempty (fun v => f n u v ω) / B n u)
      (fun _ _ _ => 1)) :
    PrecL sz μ (U := fun n => U n × V n) (fun n p ω => f n p.1 p.2 ω) (fun n p _ => B n p.1) := by
IterationsGen.lean:119
theorem iterationsA_prec_mono_rightg {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) : PrecL sz μ ξ ζ' := by
IterationsGen.lean:127
theorem iterationsA_prec_mono_leftg {U : ℕ → Type*} {ξ ξ' ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hle : ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ξ' n u ω) (h : PrecL sz μ ξ' ζ) : PrecL sz μ ξ ζ := by
IterationsGen.lean:135
theorem iterationsA_prec_absorbg (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ℝ} (hζ : ∀ᶠ n in atTop, ∀ u ω, 0 ≤ ζ n u ω)
    (h : PrecL sz μ ξ (fun n u ω => c * ζ n u ω)) : PrecL sz μ ξ ζ := by
IterationsGen.lean:151
theorem iterationsA_prec_rpowg {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω, 0 ≤ ξ n u ω) (hζ : ∀ n u ω, 0 ≤ ζ n u ω) {θ : ℝ} (hθ : 0 < θ)
    (h : PrecL sz μ ξ ζ) : PrecL sz μ (fun n u ω => ξ n u ω ^ θ) (fun n u ω => ζ n u ω ^ θ) := by
IterationsGen.lean:166
theorem iterationsA_prec_one_add_mulg (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ} (hc : ∀ n u, 0 ≤ c n u)
    (hξ : ∀ n u ω, 0 ≤ ξ n u ω) (h : PrecL sz μ ξ ζ) :
    PrecL sz μ (fun n u ω => 1 + c n u * ξ n u ω) (fun n u ω => 1 + c n u * ζ n u ω) := by
IterationsGen.lean:95
theorem st_one_le_XiLg (Cf : FlowFM sz) {n : ℕ} {v : ℝ} (k : ℕ) (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) :
    1 ≤ STXiLg Cf n v k ω := by
IterationsGen.lean:105
theorem st_one_le_XiLKg (Cf : FlowFM sz) {n : ℕ} {v : ℝ} (k : ℕ) (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) :
    1 ≤ STXiLKg Cf n v k ω := by
IterationsGen.lean:211
theorem iterationsA_xiL_odd_leg {Cm : Step2Mat sz} {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {E : ℕ → ℝ} (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E)
    (hHf : ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf n u ω).IsHermitian) (n : ℕ) {v : ℝ} (ω : sz.SeqΩ) (hB : 0 < sz.Bctl n v) {N : ℕ} (hN : 3 ≤ N) :
    STXiLg Cm.toFlowFM n v (2 * N - 1) ω ≤ 1 + (sz.Bctl n v)⁻¹ *
      ((STXiLg Cm.toFlowFM n v (2 * ((N + 1) / 2)) ω * STXiLg Cm.toFlowFM n v (2 * (N / 2)) ω) *
        (STXiLg Cm.toFlowFM n v (2 * (N / 2)) ω * STXiLg Cm.toFlowFM n v (2 * ((N - 1) / 2)) ω)) ^ (1 / 2 : ℝ) := by
IterationsGen.lean:284
structure IterationsAScaleg (Cf : FlowFM sz) (s t A T : ℕ → ℝ) (cB cv K : ℝ) : Prop where
IterationsGen.lean:346
theorem iterationsA_avg_of_STAvgUg (Cf : FlowFM sz) (hsize : Tendsto sz.size atTop atTop) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (h : STAvgUgL Cf μ s t) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 1 ω) (fun _ _ _ => 1) := by
IterationsGen.lean:377
theorem iterationsA_apriori_of_lRB1g {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hsize : Tendsto sz.size atTop atTop) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) (h : STStep1LoopgL Cm.toFlowFM μ s t)
    (m : ℕ) (hm : 1 ≤ m) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1)) := by
IterationsGen.lean:448
theorem iterationsA_rela_of_Kg (Cf : FlowFM sz) (hsize : Tendsto sz.size atTop atTop) {s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (m : ℕ) (hm : 1 ≤ m)
    (hK : PrecL sz μ (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖Cf.K n p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1))) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg Cf n q.1.1 m ω) := by
IterationsGen.lean:505
theorem iterationsA_scale_Ig (hd : 2 ≤ d) {Cm : Step2Mat sz} {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ}
    (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 16)
    (hreg : STRegIterI sz s t) (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡) (ht1 : ∀ n, t n < 1) :
    IterationsAScaleg Cm.toFlowFM s t (fun n => sz.STAI n) (fun n => 2 * (sz.STAI n)⁻¹) 2 2 2 := by
IterationsGen.lean:514
theorem iterationsA_scale_IIg {Cm : Step2Mat sz} {E s t : ℕ → ℝ} {𝔠d : ℝ}
    (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (h𝔠d : 0 < 𝔠d) (hc : 𝔠d ≤ 1 / 24)
    (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) :
    IterationsAScaleg Cm.toFlowFM s t (fun n => sz.STAII s n) (fun n => (sz.STAII s n) ^ (-1 + 𝔠d)) 1 1 1 := by
IterationsGen2.lean:272
theorem iterationsB_stepg {Cm : Step2Mat sz}
    {Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {E : ℕ → ℝ}
    (hLC : Step34Gen_LCompat Cm Hf) (hL : StepDecompGen_LoopForm Cm E)
    (hHf : ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf n u ω).IsHermitian) (hsize : Tendsto sz.size atTop atTop)
    {s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScaleg Cm.toFlowFM s t A T cB cv K)
    (hboot : STXiBootgL' Cm.toFlowFM μ s t)
    (hrela : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg Cm.toFlowFM n q.1.1 m ω))
    (havg : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 1 ω) (fun _ _ _ => 1))
    (hapri : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
      (fun n q _ => (Cm.eta n (s n) / Cm.eta n q.1.2) ^ (m - 1)))
    {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k)
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHypgL Cm.toFlowFM μ s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHypgL Cm.toFlowFM μ s t A r (k - 1)) :
    STIterHypgL Cm.toFlowFM μ s t A N k := by
IterationsGen2.lean:373
def IterationsGen2_Fam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
      Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  Step2EventsGen_Flow d Flow T0 ∧ (∀ sz : Sizes d, IsProbabilityMeasure (law sz)) ∧
    (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (Es sz z) ∧ ∀ n : ℕ, ‖(mkM sz z).m n‖ ≤ 1) ∧
    (∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z) ∧
      ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), (Hf sz z n u ω).IsHermitian)
IterationsGen2.lean:389
theorem stIterationsgL'_of :
    ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 →
        STIterationsgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
IterationsGen2.lean:409
theorem stIterationsIIgL'_of :
  -- binders (d law Flow mkM Hf Es T0) and IterationsGen2_Fam hypothesis: as in stIterationsgL'_of (script output abbreviated)
      IterationsGen2_Fam d law Flow mkM Hf Es T0 →
        STIterationsIIgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
```

### Compiled nonempty instances (`d = 3`, `szB`, `zB`, `Step34Pins.lean:710-842`; `grep -n "^example\|^theorem inst_"`)
```
IterationsGen.lean:545 548 552 558 565 569 573 577 582 589 599 604 610 615 621 
IterationsGen2.lean:468 490 513 532 553 574 
IterationsGen.lean §4 (lines 521-633): targets 10, 11, 12 (15 examples); IterationsGen2.lean §5 (lines 427-601): `IterationsGen2_famBand` (theorem, bundle at the band for every d),
  `inst_iterationsgL'`, `inst_iterationsIIgL'` (target 14, both cases), 4 examples (target 13: case (ii) (N,k) = (3,2) and (2,1), case (i) (3,2); target 14 with STKboundgL discharged)
```

### Pin and bridge checks (scratch file `pincheck.lean`: the `T2497_*` texts of the check file, then `example`s)
```
$ grep -n '^example' pincheck.lean | cut -c1-100
68:example : ∀ {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (s t A T : ℕ → ℝ) (cB cv K : ℝ),
71:example : T2497_IterationsOf T2497_IterFam := stIterationsgL'_of
72:example : T2497_IterationsIIOf T2497_IterFam := stIterationsIIgL'_of
73:example : T2497_IterationsOf IterationsGen2_Fam := stIterationsgL'_of
74:example : T2497_IterationsIIOf IterationsGen2_Fam := stIterationsIIgL'_of
76:example : @IterationsGen2_Fam = @T2497_IterFam := rfl
78:example : ∀ {d : ℕ} (sz : Sizes d) (E s t A T : ℕ → ℝ) (cB cv K : ℝ),
82:example : ∀ d : ℕ,
$ lake env lean pincheck.lean
exit 0  error lines: 0
```

### Greps (`zsh greps.sh`, `clash.sh`; patterns of the ticket)
```
C1/X1-C1 regex, code lines without backtick (docstrings and comments excluded), non-instance region (IterationsGen.lean < 528, IterationsGen2.lean < 427):
RBM3D/Chain/IterationsGen.lean:196:  rw [hLC n v p.1 p.2 ω, (hL n).2.2.1 v (Hf n v ω) (KLloopOf d (sz.L n) p.1 p.2)]
RBM3D/Chain/IterationsGen.lean:320:    (hη : ∀ n u, etaT (E n) u = Cf.eta n u) (h : IterationsAScale sz E s t A T cB cv K) :
RBM3D/Chain/IterationsGen.lean:334:    ∃ E' : ℕ → ℝ, (∀ n, |E' n| < 2) ∧ ∀ n u, etaT (E' n) u = Cm.eta n u := by
RBM3D/Chain/IterationsGen.lean:341:  · unfold etaT
  (196 = `KLloopOf`, the merged name; 320/334/341 are inside the private bridge lemmas `IterationsAScaleg_of_band`, `IterationsGen_Ep`; no public generic statement hits)
X1-C4 (def/abbrev/structure of merged texts), TN-C4+UBA (`STGridRepNgL|sz.withLam|gK|import RBM3D.BA`), `sorry|admit|native_decide|axiom`: each `hits: 1` (grep exit 1 = none)
hits: 1  (1 = none)
hits: 1  (1 = none)
hits: 1  (1 = none)
U5S-C3 (`∀ (sz : Sizes d)`): 11 hits, all in `IterationsGen2_Fam` and the two target statements (rows 1-6 of the ticket table)
Name clash (`clash.sh`: 26 new public names, `grep -rnwF` over RBM3D and RBM3D.lean excluding the two new files): the only hits are my own registry text in Test/Axioms.lean:
RBM3D/Test/Axioms.lean:229:   `RBM.BA.STXiBootgL', -- `(am;asoi222)` at `B_s` (DECISIONS §80) over a carrier (
RBM3D/Test/Axioms.lean:122:   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot
RBM3D/Test/Axioms.lean:122:   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot
$ git diff main...t/T2497b -- <the ticket's band/Chain/BA pathspec> | wc -l  ->  0
$ git diff --name-only main...t/T2497b  ->  RBM3D.lean RBM3D/Chain/IterationsGen.lean RBM3D/Chain/IterationsGen2.lean RBM3D/Test/Axioms.lean 
Ports: from the RBM3D band files `Induction/IterationsA.lean` (last commit 6583ca26) and `IterationsB.lean` (64ed77ff), not from RBM1D/RBM2D: no RBM1D/RBM2D diff-stat applies.
```

### Narrative
- Delivered: targets 10-15 in `Chain/IterationsGen` (633 lines: §1 target 10, §2 target 11, §3 target 12, §4 instances 521-633) and `Chain/IterationsGen2` (601 lines: §1-§2 target 13, §3-§4 target 14, §5 instances 427-601), the `STIterR'` owner text in `Test/Axioms.lean`, two import lines in `RBM3D.lean` after `import RBM3D.BA.Step5IIIWalk2`. Commits b7530920 (`wc -l` 521), 351c0e05 (633 / 601); the stop size 2,000 was never approached.
- Size against the ticket forecast (865-1,020, ticket :19): 1,234 lines, of which instances 288 and the rest 946 (1.21-1.43 x the forecast range).
- No hypothesis added, no pinned signature changed: `stIterationsgL'_of`, `stIterationsIIgL'_of` equal `T2497_IterationsOf/IIOf` at `IterationsGen2_Fam` (`@IterationsGen2_Fam = @T2497_IterFam := rfl`, `example`s above); `IterationsAScaleg` is `T2497_IterScaleg` (`IterationsGen_scaleg_iff`, `bandFM_IterationsAScale`).
- E' route (target 12): `IterationsGen_Ep` gives `E'` with `|E' n| < 2` and `etaT (E' n) = Cm.eta n` from `StepDecompGen_LoopForm` and `‖m‖ ≤ 1`; the unedited band `iterationsA_scale_I/II` are applied at `E'`. The substitution went through; no restatement.
- Target 11: `STmaxLg` is `loopMax` of `blockMat (Hf n v ω)` by `Step34Gen_LCompat` and the third conjunct of the loop class; `loopXi_le`, `loopMax_odd_sq_le` are used by name.
- Target 13: `iterationsB_stepg` is stated over `Cm : Step2Mat sz` with `hLC`, `hL`, `hHf` (the odd-chain obligation needs the loop class); the rest is the band step with `Cm.eta`.
- Target 14: the pin's own `STKboundgL` premise is used (`stKbound_timeIccgL`, law a probability measure, Fam row 2); the band proof rebuilt it. `STLKgL` is unused.
- The 24 band privates of `IterationsB:64-445`: 12 reused by `open private` (`Bctl_nonneg`, `XLv`, `XLKv`, `XLv_ge_one`, `XLv_le_pred`, `XLv_le`, `XLv_le_chain`, `XLv_four_p`, `XLKv_ge_one`, `XLKv_le`, `XLv_le_Z`, `sqrt_prod_le`), 11 private `…g` twins (`prec_XL_of`, `rho`, `XL`, `XLK`, `rho_ge_one`, `rho_eq`, `obl_short`, `prec_chain_abs`, `obl_chain`, `obl_four_p`, `obl_K`), 1 unused (`one_le_ratio`). `IterationsA`: no `open private`; two private copies `IterationsGen_apriori_aux`, `IterationsGen_one_le_ratio`.
- Family table as used: rows 1-6 are `IterationsGen2_Fam`; rows 3-4 guarded by `0 < κ` and the flow, rows 5-6 unguarded. At the band the bundle is proved for every `d` (`IterationsGen2_famBand`).
- UBA-C1: `sz.lam` enters only through `STAI`, `STAII`, `STRegIterI`, `WO`, `Bctl`; R1 never enters (`withLam|gK`: no hit).
- Registry: the first full build stopped in `#assert_rbm_axioms` with "1 premise(s) ... [RBM.BA.STXiBootgL']" (hypothesis of the public `iterationsB_stepg`); one `owedProps` line added next to `STAvgUgL` (the ticket expected none); the second full build passes.
- Instance data: `d = 3`, `szB`, `zB`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `(7/8, 15/16)`, `(15/16, 31/32)`, `(N,k) = (3,2)` and `(2,1)`; the stochastic premises (`STKboundgL` except in the third example, `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'`, `IH1`, `IH2`, the averaged-law, a priori and `𝒦` pins) stay hypotheses; every deterministic one is discharged.

## (c) Verified Mathlib names (all resolved by the build; nothing probed absent)
`Real.sqrt_lt'` (new, `IterationsGen_Ep`); `mul_div_mul_right` (new, `IterationsGen_eta_ratio`); `Finset.sup'_univ_eq_ciSup`, `Finset.exists_mem_eq_sup'`, `Real.sqrt_eq_rpow`, `le_div_iff₀`, `div_le_div_of_nonneg_left`, `inv_le_of_inv_le₀` (copied unchanged from the band proofs).

## (d) Open issues and paper-delta candidates
- No (a′): section (a) needs no correction. Landed sizes differ from the forecast (above).
- `owedProps` gained `RBM.BA.STXiBootgL'` (ticket expected none); the hub or dispatcher may want it in the ledger text of U3s3/U3s4.
- Consumers of `iterationsB_stepg` (U3s4) supply `Step34Gen_LCompat`, `StepDecompGen_LoopForm` and a Hermitian flow matrix (family rows 5-6).
- Row a and row b both insert import lines after `import RBM3D.BA.Step5IIIWalk2` in `RBM3D.lean`: the hub merges the union.
- Paper-delta candidates: none new. Inherited and unchanged: T2246a (R2*: `B_s` in the first summand), T2087a (`Ψ` at `d ≥ 3`), `p = N + 4 ≥ 2` (paper `p ≥ 4`), as in the headers of `IterationsA.lean`, `IterationsB.lean`.
