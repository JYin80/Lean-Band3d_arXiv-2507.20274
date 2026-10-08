Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 04:08:15 UTC 2026

Targets (mathematics only): T1 `STStep4I d`, T2 `STStep4II d` (`STStep4R d R`, `R = STCaseI/II`: given `STLmaxU` and the hypotheses of `STIngR`
plus `STStep1Loop`, conclude `STLKU`, `(Eq:L-KGt-flow)`); T3 `ST_mainInd_of_pins'`. Sources read: `Step34Pins.lean:170-300,380-470`,
`NQEndFlow.lean:80-130`, `IterationsA.lean:100-170,1355-1385`, `ScaleFacts3.lean:50-110`, `MainIndRegimes.lean:36-64,120-236,600-690`,
probe `3c58211:RBM3D/Probe/T2041Pins.lean:925-1045`, paper `3_5:1360-1392,1598-1616`, `1_2:1366-1376`, DECISIONS §29, §80, §132, §133.

### (i) Exponent / constant table

| # | Quantity | Value | Constraint | Slack |
|---|---|---|---|---|
| 1 | `Ξ^{(L)}_{v,m} ≡ 1` (all `m ≥ 1`) | `XL := 1` | needs `Ξ̂^{(L)}_m ≺ 1` for `m ≤ n+1`, `2n-1`, `4p` (`STlenL`); `st_prec_one_add_sup` of `STLmaxU` (`k ≥ 1`, bound `B^{k-1}`) | exact (STLmaxU is a hypothesis of `STStep4R`) |
| 2 | `Ξ^{(L-K)}_{v,m} ≡ 1`, `m ≤ n-1` | `XLK := 1` | `m = 1`: `iterationsA_avg_of_STAvgU` (`IterationsA:1359`); `2 ≤ m < n`: strong induction | `STStep2Concl.2.1 = STAvgU` is a hypothesis |
| 3 | `Λ` of `(eq:WO)` (`st_Bctl_ge` hyp.) | `Λ = 𝔡⁻¹` | `∀ᶠ n, 0 < lam ∧ lam ≤ Λ`; `STFlow → Admissible → WO 𝔡`: `lam ≥ W^{-d/2+𝔡} > 0` (`W ≥ 1`), `lam ≤ 𝔡⁻¹` | exact; `sz0`: `lam→0`, `szB`: `lam = 1 ≤ 10` |
| 4 | `B_s ≥ N^{-2}` (R2*: `B_{s,0}` in the first summand of `STbootRHS`, `NQEndFlow:95`) | `st_Bctl_ge` at `u = s n` | `0 ≤ s n` (hyp.), `s n < t n < 1` (`st5_t_lt_one`: `t ≤ lemT < 1`); eventually `N ≥ Λ²+1` | `sz0` n=0: `B_s/N^{-2} = 1.4e8`; `szB` n=0: `3.1e5` (script) |
| 5 | absorption exponent | `B_s^{-1/(4p)} ≤ N^{2/(4p)} = N^{1/(2p)}` | target `≤ N^{τ/4}`; `2/(4p) ≤ τ/4 ⟸ p > 2/τ` | `τ = 1/2`, `p = 5`: `0.1 ≤ 0.125`, slack `0.025` |
| 6 | `c_k` in `st_bootRHS_one` (`STbootRHS 1 1 1 B k p = B^{-1/(4p)} + c_k`) | `c_k = |Icc 1 (k-1)|+|Icc (k-1)(k+1)|+|Icc((k+1)/2+1)(k-1)|` | `N^{τ/4} ≥ c_k + 1` eventually (`τ = 1/2`) | `c_2,c_3,c_4,c_6 = 4,5,7,10`; threshold `n0` in (ii) |
| 7 | closing sum | `N^{τ/4}·N^{τ/4} = N^{τ/2}` | `B^{-1/(4p)} + c_k ≤ N^{τ/2}` (`B^{-1/(4p)} ≤ N^{τ/4}`, `c_k ≤ N^{τ/4}`); then `N^{τ/2}·N^{τ/2} = N^τ` against the `Prec` bound at `τ/2` | exact (`rpow_half_mul_rpow_half`) |
| 8 | `lo` in `STbootRHS` of `STXiBoot'` | `lo = 1` (`NQEndFlow:95-105`; paper `(am;asoi222)` `3_5:1360-1366` has `n'=1`) | the ticket (preflight (i)) says `lo = 2` (that is `STNQConcl''`, not used here) | no effect: with `XLK ≡ 1` the `lo` sum is a constant; the hypothesis `∀ m, 1 ≤ m, m+1 ≤ n_` supplies `m = 1` |
| 9 | `B_u^{1/6} XLK` term | absent from `STXiBoot'` (it is in `STNQConcl''`) | ticket (S4) says it must be absorbed | nothing to absorb; `B ≤ 1` checked anyway (script) |
| 10 | `𝔠d` (T1, T2) | the `𝔠d` of `stOeqQt'_holds` (case I) / `stOeqQtNZ'_holds` (case II), taken verbatim | `STIngR` already gives `0 < 𝔠d ≤ 1/100` and the same `∃ 𝔠d` position as `STStep4R` (after `κ ε 𝔡 Cd`) | `min(𝔠d, 1/100) = 𝔠d`; no `st5_conStInd_mono` needed (ticket (C) is unnecessary; harmless) |
| 11 | assembly constants (T3) | `ST_mainIndR_of_steps` takes `min c₂ (min c₃ …)` itself | `R34 ⊇ R` by `st_caseI_of_reg5III d` (`:125`), `st_caseI_of_reg5I d` (`:137`) | exact; `st_caseII_*` as in the unprimed `:674-683` |
| 12 | `(con_st_ind)` threshold (hypothesis `∀ᶠ n`) | `(B_t)^{𝔠d} ≤ (1-t)/(1-s) < 1` | at `𝔠d = 1/100` | see (ii): `sz0`: `n ≥ 0`; `szB (15/16, 61/64)`: `W ≥ 10^{4.2}` |

(S4) against `3_5:1602-1613` (`(saww02)`): first term `(W^{-d}B_{s,0})^{-1/(4p)}` is the R2* form (DECISIONS §80); `n = 2` has
the `XLK` sum empty/constant, `p` large gives `Ξ̂_2 ≺ 1`, then induction in `n`; this is the probe `hall` with `q.1.2` replaced by `s n` in `hpp`
and `hBn (s n) (hs0 n) (s n ≤ 1)` (`st_Bctl_ge` at `u = s n`); no other change (`STXiBoot'` has the same hypotheses `m+1 ≤ n_`, `STlenL` as `STXiBoot`).
The `Prec` index types agree: `STXiBoot'` and `STLKU` conclude over `STPair s t` resp. `TimeIcc s t × …`; the closing step is `st_prec_of_xi`
with `φ`, as in the probe.

(A) against `MainIndRegimes.lean:674-683` and `:165-236`: `ST_mainIndR_of_steps d R R34 hR h1 h2 h3 h4 h5 h6` needs `h3 : STStep3R d R34`,
`h4 : STStep4R d R34`, `hR : 3 ≤ d → ∀ sz s t, R sz s t → R34 sz s t`. Regime (iii): `R = R34 = STReg5III`, `h3 = h3III` (target hyp. `STStep3R d STReg5III`),
`h4 = step4R_mono (stStep4I_holds d) (st_caseI_of_reg5III d)`, `h5 = stStep5III_holds d`, `h6 = h6III`. Regime (i): same with `STReg5I`, `st_caseI_of_reg5I d`,
`h5I`, `h6I`. Regimes (ii), (iv): `ST_mainIndR_II/IV_of_steps` with `STStep3II d` (target hyp.) and `stStep4II_holds d`, `h5II`/`stStep5IV_holds d`,
`h6II`/`stStep6IV_holds d`. Hypotheses of T3 (`STStep2`, `STStep3R · STReg5III`, `STStep3R · STReg5I`, `STStep3II`, `STStep5I/II`, `STStep6I/II/III`) = the ten hypotheses of the unprimed `:674` minus `STStep4I/II`, with `STStep3I` replaced by the two regime pins (nine in all); `h1 = RBM.Green.stStep1_holds hd`. `step4R_mono` holds at fixed `d` (`STStep4R d R` only uses `R` at `Sizes d`); the ticket's
`(fun _ _ _ _ h => h)` has binders `hd, sz, s, t, h`, matching `hR`. Closes.

DECISIONS §29, one line each: (1) `0 ≤ s`, `s < t`, `t ≤ lemT < 1` are hypotheses of `STStep4R`; `s n ∈ [0,1)` is used for `B_s ≥ N^{-2}`. (2) the case-(ii) boundary
is not used (`STCaseII` is only passed to `stOeqQtNZ'_holds`; `0 ≤ s` already forces `1-s ≤ 1`). (3) `L`–`W` polynomial relation: only `W^d ≤ N`
(inside `st_Bctl_ge`) is used; `W ≥ N^𝔠` is not used by Step 4. (4) `∀ n` data are hypotheses (`hs0`, `hst`, `htT`); every conclusion and every use is `∀ᶠ n` (`hlam`, `STConStInd`, `Prec`).

### (ii) Concrete nondegenerate instance (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, merged data of `SizesInst`/`Step34Inst`)

- Case I (T1; regime (iii) ⊂ case I, so also T3): `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `z0 = 1/2 + i N^{-4/5}`, `(s,t) = (0, 1/16)`.
- Case II (T2): `szB` (`L = 4`, `W = n+4`, `lam = 1`), `zB = 1/2 + i/64`, `(s,t) = (15/16, 61/64)` (`1-s = lam²/L²`; `61/64 ≤ 31/32 ≤ lemT zB`, merged `lemT_zB`).
  The merged data has `t = 31/32`; I use `61/64` so that the ratio `(1-t)/(1-s) = 3/4` keeps `(con_st_ind)` threshold small.
- Premises left as hypotheses (other gates' pins / stochastic): `STKbound`, `STKward`, `STLK` at `s`, `STStep1Loop`, `STStep2Concl`, and `STLmaxU` (Step 3, T2320).
  The ten step pins of T3. These are statements true in the paper, not constraints on the numbers.
- External hypotheses: none (no borrowed `Prop` is added; `stOeqQt'_holds`, `stOeqQtNZ'_holds` are merged theorems), so no limit computation is owed.

Command (`python3 -I inst.py`, scratch in `…/scratchpad/T2321/`; `lemT` evaluated with 200-digit `decimal`, `<1` check needs it):

```
d=3, kappa=eps=dlt=1/10, c=1/6
== sz0 s=0.000000 t=0.062500
 n=0: N=2.097e+06 WO=True Band=True loc=True 0<=s<t<=lemT:True lemT<1:True caseI=True caseII=False
   B_s=3.099e-05 N^-2=2.274e-13 B_s>=N^-2:True B_u<=1 (u=s,t):True lam<=1/dlt:True
 n=1000: N=2.135e+60 WO=True Band=True loc=True 0<=s<t<=lemT:True lemT<1:True caseI=True caseII=False
   B_s=3.006e-50 N^-2=2.193e-121 B_s>=N^-2:True B_u<=1 (u=s,t):True lam<=1/dlt:True
 absorption B_s^{-1/(4p)} <= N^{1/(2p)} <= N^{tau/4} (p=5,tau=1/2), n<3000: True
   k=2: c_k=4, N^(tau/4) >= c_k+1 from n0=0
   k=3: c_k=5, N^(tau/4) >= c_k+1 from n0=0
   k=4: c_k=7, N^(tau/4) >= c_k+1 from n0=1
   k=6: c_k=10, N^(tau/4) >= c_k+1 from n0=1
   (con_st_ind) at c_d=1/100: B_t^c <= (1-t)/(1-s) = 0.9375, first n = 0
== szB s=0.937500 t=0.953125
 n=0: N=4.096e+03 WO=True Band=True loc=True 0<=s<t<=lemT:True lemT<1:True caseI=False caseII=True
   B_s=1.861e-02 N^-2=5.960e-08 B_s>=N^-2:True B_u<=1 (u=s,t):True lam<=1/dlt:True
 n=1000: N=6.477e+10 WO=True Band=True loc=True 0<=s<t<=lemT:True lemT<1:True caseI=False caseII=True
   B_s=1.177e-09 N^-2=2.384e-22 B_s>=N^-2:True B_u<=1 (u=s,t):True lam<=1/dlt:True
 absorption B_s^{-1/(4p)} <= N^{1/(2p)} <= N^{tau/4} (p=5,tau=1/2), n<3000: True
   k=2: c_k=4, N^(tau/4) >= c_k+1 from n0=15
   k=3: c_k=5, N^(tau/4) >= c_k+1 from n0=26
   k=4: c_k=7, N^(tau/4) >= c_k+1 from n0=60
   k=6: c_k=10, N^(tau/4) >= c_k+1 from n0=146
   (con_st_ind) at c_d=1/100: B_t^c <= (1-t)/(1-s) = 0.7500, first n = 15894
c'=0.001: c_d=min(c',1/100)=0.001, 0<c_d<=1/100: True
c'=0.02: c_d=min(c',1/100)=0.01, 0<c_d<=1/100: True
c'=5.0: c_d=min(c',1/100)=0.01, 0<c_d<=1/100: True
```

Second command (`python3 -I con.py`): `(con_st_ind)` threshold for `szB`, `𝔠d = 1/100`:

```
szB s=0.0000 t=0.9688 ratio=0.0312 c=1/100: need W >= 10^50.2
szB s=0.9375 t=0.9688 ratio=0.5000 c=1/100: need W >= 10^10.1
szB s=0.9375 t=0.9531 ratio=0.7500 c=1/100: need W >= 10^4.2
```

Reading: every deterministic hypothesis (flow `WO`, bandwidth, `locDomain`, `0 ≤ s < t ≤ lemT < 1`, regime, `B_s ≥ N^{-2}`, `lam ≤ 𝔡⁻¹`, absorption, `c_d ∈ (0, 1/100]`)
holds from `n = 0` except the `∀ᶠ` ones: `N^{1/8} ≥ c_k+1` (`n0 ≤ 146` at `k ≤ 6`) and `(con_st_ind)` (`n0 = 0` at `sz0`; `15894` at `szB (15/16, 61/64)`).
The merged instance `(szB, 0, 31/32)` used by `inst_mainInd3_data` needs `W ≥ 10^{50.2}` for `𝔠d = 1/100` (and more for a smaller `𝔠d`): the lemma `conStInd_const`
discharges it for every `𝔠d > 0` (it is `∀ᶠ`), but T3's instance should use `(sz0, z0, 0, 1/16)` or `(szB, zB, 15/16, 61/64)` so that no astronomical `n0` is visible.
`B_u ≤ 1` holds on both families (so `B_u^{1/6} ≤ 1`, not needed for `STXiBoot'`).

### Verdicts

- T1 `stStep4I_holds`: **PASS**.
- T2 `stStep4II_holds`: **PASS**.
- T3 `ST_mainInd_of_pins'`: **PASS**.
- Ticket inaccuracies (no effect on the verdict; for the prover): row 8 (`lo = 1` in `STXiBoot'`, not `2`), row 9 (no `B_u^{1/6}` term to absorb), row 10 (no `min` / `st5_conStInd_mono` step).

## (b) Script output — Thu Oct  8 04:18:23 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2321`, branch `t/T2321`, commit `f4809fb`; `wc -l RBM3D/Induction/Step4.lean` = 312 (ticket size 450/600/850; stop rule 1500 not reached).

### b.1 Module build, axioms (printed by `#print axioms` lines at the end of the file)
```
$ lake build RBM3D.Induction.Step4   # exit 0; Step4.lean emits no warning
Build completed successfully (3935 jobs).
lake build RBM3D.Induction.Step4  4.48s user 4.76s system 154% cpu 5.995 total
  :303:0: 'RBM.Ind.stStep4I_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
  :304:0: 'RBM.Ind.stStep4II_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
  :305:0: 'RBM.Gauss.Sizes.ST_mainInd_of_pins'' depends on axioms: [propext, Classical.choice, Quot.sound]
  :306:0: 'RBM.Ind.Step4Inst.inst_step4R_dis' depends on axioms: [propext, Classical.choice, Quot.sound]
  :307:0: 'RBM.Ind.Step4Inst.inst_stStep4I' depends on axioms: [propext, Classical.choice, Quot.sound]
  :308:0: 'RBM.Ind.Step4Inst.inst_stStep4II' depends on axioms: [propext, Classical.choice, Quot.sound]
  :309:0: 'RBM.Ind.Step4Inst.inst_stStep4I'' depends on axioms: [propext, Classical.choice, Quot.sound]
  :310:0: 'RBM.Ind.Step4Inst.inst_stStep4II'' depends on axioms: [propext, Classical.choice, Quot.sound]
  :311:0: 'RBM.Ind.Step4Inst.inst_mainInd3'_data' depends on axioms: [propext, Classical.choice, Quot.sound]
  :312:0: 'RBM.Ind.Step4Inst.inst_mainInd3'_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.2 Targets, extracted from the file by script (python, regex from `theorem` to `:=`)
```lean
theorem stStep4I_holds : ∀ d : ℕ, STStep4I d :=

theorem stStep4II_holds : ∀ d : ℕ, STStep4II d :=

theorem ST_mainInd_of_pins' (d : ℕ) (h2 : STStep2 d) (h3III : STStep3R d STReg5III)
    (h3I : STStep3R d STReg5I) (h3II : STStep3II d) (h5I : STStep5I d) (h5II : STStep5II d)
    (h6I : STStep6I d) (h6II : STStep6II d) (h6III : STStep6III d) : STMainInd d :=

```
Check-file equality (scratch = the check file's imports + `import RBM3D.Induction.Step4` + the check's section-2 defs + three `example`s; `lake env lean`):
```
$ python3 -I mkcheck.py checkeq.lean && lake env lean checkeq.lean ; echo "exit $?"
example : RBM.Ind.T2321Check.T2321_stStep4I := RBM.Ind.stStep4I_holds
example : RBM.Ind.T2321Check.T2321_stStep4II := RBM.Ind.stStep4II_holds
example : RBM.Ind.T2321Check.T2321_mainInd_of_pins' := RBM.Gauss.Sizes.ST_mainInd_of_pins'
exit 0
```

### b.3 Compiled nonempty instances (namespace `RBM.Ind.Step4Inst`, `d = 3`; extracted by script)
```lean
def Step4Concl (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLK sz (STflowE z) s → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
      STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t)

theorem inst_stStep4I : Step4Concl sz0 z0 sInst tInst 1 :=
  inst_step4R_dis STCaseI (stStep4I_holds 3) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1
    one_pos

theorem inst_stStep4II : Step4Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_step4R_dis STCaseII (stStep4II_holds 3) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

theorem inst_mainInd3'_data (h2 : STStep2 3) (h3III : STStep3R 3 STReg5III) (h3I : STStep3R 3 STReg5I)
    (h3II : STStep3II 3) (h5I : STStep5I 3) (h5II : STStep5II 3) (h6I : STStep6I 3) (h6II : STStep6II 3)
    (h6III : STStep6III 3) :
    InstMainIndRConcl STAny szB zB (fun _ => 0) (fun _ => 31 / 32) :=
  inst_mainIndR _ ((ST_mainInd_iff_any 3).1 (ST_mainInd_of_pins' 3 h2 h3III h3I h3II h5I h5II h6I h6II h6III))
    szB zB flow_zB _ _ (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) trivial
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

```
Data: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `C_d = 1`; T1: `sz0, z0, s ≡ 0, t ≡ 1/16` (`sz0_caseI`); T2: `szB, zB, s ≡ 15/16, t ≡ 31/32` (`szB_caseII`: `1-s = ilambda²/L²`); T3: `szB, zB, 0, 31/32` as `inst_mainInd3_data`, and `sz0, z0, 0, 1/16` (`inst_mainInd3'_sz0`). `(con_st_ind)` for every `𝔠_d > 0` (`conStInd_const`, `sz0_con`); `STKbound`, `STKward` discharged (`stKbound_of_flow`, `stKward_of_flow`). Left as hypotheses (other gates' pins): `STLK s`, `STStep1Loop`, `STStep2Concl`, `STLmaxU` (Step 3, T2320); for T3 the nine step pins. Also `inst_stStep4I'`, `inst_stStep4II'`: the same through the merged `inst_step4I/II` (`InstStep4Concl`).

### b.4 Registry pre-check and full build
```
$ lake env lean precheck.lean   # = import RBM3D / import RBM3D.Induction.Step4 / #assert_rbm_axioms (temporary, uncommitted)
exit 0
premises found by scanning: 147 (borrowed 1, owed 87, structural 41, refuted 6, superseded 12).
registry: 2 borrowed + 137 owed + 105 structural + 7 refuted + 13 superseded; 117 registered premise(s) carry nothing yet: [...]

$ lake build   # worktree as committed (RBM3D.lean unchanged: Step4 not yet imported)
error: RBM3D.lean:361:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Gauss.Sizes.STStep4I, RBM.Gauss.Sizes.STStep4II]
exit 1

$ lake build   # temporary uncommitted line "import RBM3D.Induction.Step4" after the last import of RBM3D.lean (removed afterwards)
Build completed successfully (4128 jobs).
lake build  43.65s user 5.11s system 104% cpu 46.735 total
exit 0
```

### b.5 Name-clash grep, hygiene, scope
```
$ grep -rn --include='*.lean' -F <name> RBM3D | grep -v RBM3D/Probe/ | grep -v RBM3D/Induction/Step4.lean | wc -l
stStep4I_holds: 0
stStep4II_holds: 0
ST_mainInd_of_pins': 1
Step4Inst: 0
step4R_mono: 0
step4_of_ing: 0
step4_skeleton: 1
inst_step4R_dis: 0
inst_stStep4I: 0
inst_stStep4II: 0
inst_mainInd3': 0
# the one hit of ST_mainInd_of_pins': my registry comment, RBM3D/Test/Axioms.lean:382; the one hit of step4_skeleton: a docstring, RBM3D/Induction/IterationsA.lean:1358 (st_step4_skeleton)
$ grep -w Step4Concl (whole word) outside Step4.lean: 0  (the substring hits are InstStep4Concl, Step34Pins.lean)
$ grep -n "sorry\|admit\|native_decide\|axiom" RBM3D/Induction/Step4.lean | grep -v "print axioms"
(no output)
$ git diff --stat main...t/T2321
 RBM3D/Induction/Step4.lean | 312 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   4 +-
 2 files changed, 313 insertions(+), 3 deletions(-)
$ git diff main...t/T2321 -- RBM3D/Test/Axioms.lean   (registry hunk)
-   `RBM.Gauss.Sizes.STStep3I, -- Step 3, case (i): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
-   `RBM.Gauss.Sizes.STStep4I, -- Step 4, case (i): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
-   `RBM.Gauss.Sizes.STStep4II, -- Step 4, case (ii): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
+   `RBM.Gauss.Sizes.STStep3I,   -- superseded by the regime pins `STStep3R · STReg5III`, `STStep3R · STReg5I` (T2320) and `ST_mainInd_of_pins'` (T2321), DECISIONS §133; 
```

### b.6 Ports
```
No RBM1D/RBM2D port. Source of the skeleton: the T2041 probe, 3c58211:RBM3D/Probe/T2041Pins.lean:945-1040 (`st_step4_skeleton`).
$ git -C ../RBM3D --no-optional-locks log -1 --format='%h %s' 3c58211
3c58211 T2041: probe repair R1, R2: instances of STLmax_of_STLmaxU, STLK_of_STLKU and the case-(ii) Step 3 skeleton
```

### b.7 Skeleton against the probe
```
$ diff probe_full.txt mine_full.txt   # probe st_step4_skeleton (3c58211:RBM3D/Probe/T2041Pins.lean) vs step4_skeleton (the whole theorem)
1,2c1,2 4c4 26,30c26 33c29 57,59c53 61c55 63c57 72c66 83c77 86c80 
changed lines (< and >): 28
```

### b.8 Narrative
- `step4_skeleton` (private, `RBM.Gauss.Sizes`) is the probe skeleton with the changes of b.7: `private`, the added parameter `hst : ∀ n, s n < t n`, hypothesis `STXiBoot'` for `STXiBoot`, the argument `sz.Bctl n (s n)` of `STbootRHS` (probe: `q.1.2`), `hB := hBn (s n) (hs0 n) …` (so `hu0/hu1` are gone), and the base case `k = 1` by `iterationsA_avg_of_STAvgU`.
- `step4_of_ing d R hI` (private, generic in the regime `R`) turns `STIngR d R (fun … => STXiBoot' …)` into `STStep4R d R`: the constant `𝔠_d` is the one of the bootstrap pin (same `∃ 𝔠d` position, `0 < 𝔠d ≤ 1/100` given), `(con_st_ind)` is passed on unchanged; no `min` and no `st5_conStInd_mono` are used (preflight row 10).
- The skeleton's side conditions come from the flow: `t n < 1` by `st5_t_lt_one`; `Tendsto sz.size` from `hflow.1.2.2.1` by `tendsto_natCast_atTop_iff`; `0 < ilambda ≤ 𝔡⁻¹` eventually from `hflow.1.2.2.2.2 : WO 𝔡` and `st5_eventually_A_ge_one` (`Λ = 𝔡⁻¹`).
- `stStep4I_holds := step4_of_ing d STCaseI (stOeqQt'_holds d)`, `stStep4II_holds := step4_of_ing d STCaseII (stOeqQtNZ'_holds d)`; no regime split.
- `ST_mainInd_of_pins'` is the ticket's (A): `ST_mainIndR_of_steps d R R (fun _ _ _ _ h => h) …` for `R = STReg5III`, `STReg5I` with `step4R_mono` (private) from case (i) through `st_caseI_of_reg5III/I`; `ST_mainIndR_II/IV_of_steps` with `stStep4II_holds` for (ii), (iv); `ST_mainInd_of_regimes` closes. The unprimed `ST_mainInd_of_pins` is unchanged (no merged file edited: b.5 diff stat).
- Registry (`Axioms.lean`, anchored by text): deleted the owed lines `STStep4I`, `STStep4II`, and moved `STStep3I` from `owedProps` to `supersededProps` with the ticket's comment. The pre-check b.4 exits 0 with the move in place (`STStep3I` is still found as a hypothesis of the unprimed `ST_mainInd_of_pins`, now classified superseded).
- Full `lake build`: without a root import it fails (b.4, first run): the audit reports `STStep4I`, `STStep4II` as premises that no theorem proves, since `RBM3D.lean` does not yet import `Step4` (the theorems that prove them are outside the library). With one temporary, uncommitted line `import RBM3D.Induction.Step4` after the last import it passes (b.4); that line was removed again, `git status --short` before the commit listed only `RBM3D/Test/Axioms.lean` and `RBM3D/Induction/Step4.lean`. The root import is the hub's at merge.
- Instances (b.3): T1 at `(sz0, z0, 0, 1/16)`, T2 at `(szB, zB, 15/16, 31/32)`, T3 at `(szB, zB, 0, 31/32)` and `(sz0, z0, 0, 1/16)`; every deterministic hypothesis is discharged, including `STKbound`, `STKward` (theorems of the flow) and `(con_st_ind)` for all `𝔠_d > 0`.
- Section (a): rows 8-10 and the verdicts agree with what compiled (`STXiBoot'` has `lo = 1`, no `B_u^{1/6}` term, constant `𝔠_d` without `min`); no (a′) section is needed. (a)(ii) numerics used `(szB, 15/16, 61/64)`; the compiled instance uses the merged `(15/16, 31/32)`, where `(con_st_ind)` comes from `conStInd_const` for every `𝔠_d > 0`, so no threshold is visible.
- No RBM1D/RBM2D port (b.6).

## (c) Verified Mathlib and project names (all by `#check @name` in a scratch file importing `RBM3D.Induction.Step4`, exit 0)

- `Nat.strong_induction_on`: exists
- `exists_nat_gt`: exists
- `div_le_div_iff₀`: exists
- `div_lt_iff₀`: exists
- `Real.one_le_rpow`: exists
- `Real.rpow_le_rpow_of_nonpos`: exists
- `Real.rpow_mul`: exists
- `Real.rpow_le_rpow_of_exponent_le`: exists
- `Real.rpow_add`: exists
- `Real.rpow_nonneg`: exists
- `Real.rpow_pos_of_pos`: exists
- `div_nonpos_of_nonpos_of_nonneg`: exists
- `mul_le_mul_of_nonneg_left`: exists
- `tendsto_natCast_atTop_iff`: exists
- `MeasureTheory.measure_mono`: exists
- `Filter.eventually_ge_atTop`: exists
- `Filter.Tendsto.eventually`: exists
- `half_pos`: exists
- `Nat.cast_nonneg`: exists
- project: `eventually_le_rpow` (`RBM3D/Defs/Domination.lean:68`), `UnifDetDom.rpow_half_mul_rpow_half` (`:104`), `st5_eventually_A_ge_one`, `st5_t_lt_one` (`Induction/Step5Kit.lean:199,192`), `stKbound_of_flow`, `stKward_of_flow` (`Loop/KLFinal.lean:302,308`).
- Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
- d.1 Merge order and registry: the ticket's sibling scan says T2320 merges first; this ticket's registry hunk deletes the owed `STStep3I` line, which T2320 edits (its comment), so the hub rebases that single line (delete it, keep the superseded line added here).
- d.2 Process: the ticket's "full `lake build` before handing over" cannot pass in the ticket worktree unless `RBM3D.lean` imports `RBM3D.Induction.Step4` (b.4); I ran it with a temporary uncommitted import and removed it. The hub's merge step (A.4-A.5) does the same.
- d.3 What stays hypothesis in the instances: `STLK s`, `STStep1Loop`, `STStep2Concl`, `STLmaxU` (Step 3, T2320) for T1/T2; the nine step pins of `ST_mainInd_of_pins'` for T3 (`STStep3R · STReg5III`, `STStep3R · STReg5I`, `STStep3II` are T2320's; the final plug-in is ST-6's).
- d.4 Ticket text (no effect on the targets): the "Mathematics" paragraph mentions `lo = 2`, a `B_u^{1/6} XLK` term to absorb and a `min (𝔠d, 1/100)`; none occurs in `STXiBoot'` / `STIngR` (preflight rows 8-10, confirmed by the compile).
- d.5 Paper-delta candidates: none new. The Lean `STStep4R` is the dispatcher's pinned conditional form (premises `STLmaxU`, `STStep1Loop`, `STStep2Concl`, `STLK s`, `STConStInd`; constants first), not a standalone Step 4; the R2* form of the bootstrap (`B_s` in the first summand) is covered by `T2246a`.
