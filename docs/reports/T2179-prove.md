Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 06:18:29 UTC 2026

Notation as in the ticket: `W, N, g, C = nqGood1C`, `u_j`, `Δ = (v-s)/K` (`gridStep`, `Walk.lean:67`), `KΔ = v-s ≤ 1`, `u_0 = s`, `u_K = v` (`gridTime_last`), `B_t = Bctl`, `η_t = (1-t) Im m(E)`, `Ls = (Im m)⁻¹ log N`, `Γ = N^{ε₁}`.

### (i) Exponent table (all rows checked by hand against the merged statements; `C > 0` is not even needed, only `W ≥ 0`; `N ≥ 1` follows from `η_v⁻¹ ≤ N`, `η_v > 0`)

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `C = nqGood1C d k Λg κ'` | abstract; `W^{Cε}, W^C ≥ 0` is all the budget uses (`nqGood1C_pos` only for the instance) | none needed |
| 2 | `κ_{i,m} B_{u_i}^k ≤ W^{Cε} B_{u_m}^k` (`u_i ≤ u_m < 1`) | merged (5.93) `nqGood2_ratio_mul_Bctl_le` + `kappaNonAltN_mul_Bctl_pow_le`; also `i = j+1` with `B_{u_j} ≤ B_{u_{j+1}}` | merged inequality, no loss beyond `W^{Cε}` |
| 3 | `κ_{i,m} ≤ kapFar` | `r = (g²+1-u_i)/(g²+1-u_m) ≤ (1+g²)(1-u_m)⁻¹ ≤ (1+g²)N` (`u_i ≥ 0`, `g²+1-u_m ≥ 1-u_m`); `(1-v)⁻¹ = Im m · η_v⁻¹ ≤ η_v⁻¹ ≤ N` as `Im m = √(4-E²)/2 ≤ 1` | holds for every real `g` (g=0, g>L) |
| 4 | `B_v ≥ N⁻¹` | `cont_inv_size_le_Bctl` (`0 ≤ v < 1`); so `X ≤ c N^{-k}` ⇒ `X ≤ c B_v^k`; `KΔ = v-s ≤ 1` | factor `N^{-k}` vs `B_v^k` ≥ 1 |
| 5 | drift level | `dDriftNonAltN = a B_u^k/η_u`, `a = Γ²Φ((k-1)+kΓΦ) ≥ 0`, `b = 0`; `(k-1)Γ²Φ + kΓ³Φ² ≤ kΓ³(Φ+Φ²)` needs `Γ = N^{ε₁} ≥ 1` (`N ≥ 1`, `ε₁ ≥ 0`) | `Γ² ≤ Γ³`, and `k-1 < k` |
| 6 | QV | `qvBdNonAltN = qvShape k κ W^C W^C W^k Γ(ΓΛ) W^{-D''} B_u η_u` (ring); `κ²G B_u^{2k} = G(κB_u^k)² ≤ G W^{2Cε}(B_v^k)²`; far part `κ² Wd + κ Ce Wd + Cc Wd ≤ qvFar·Wd`; `G = Γ²Λ ≥ 0` needs only `Λ ≥ 0` | exact |
| 7 | `Σ_{j<K} Δ/η_{u_{j+1}} ≤ Ls + 1` | `sum_succ_le` with `f j = Δ/η_{u_j}`, `f 0 ≥ 0`, `f K = Δ/η_v ≤ 1` (`hΔη`), `hlog` | `+1` |
| 8 | coefficients of `Λ^{1/2}B_v^k` | init `1/6` (`ha1`, `Λ ≥ 1`), `εK_{0K}δ₀` `1/12` (`he1`), drift far `1/12` (`he1`), QV main `1/12` (`ha3`), QV far `1/12` (`he2`), `N^{-D_Y}` `1/6` (`he3`), remainder `1/6` (`he4`): sum `10/12 = 5/6` | `1/6` |
| 9 | coefficients of `Φ, Φ²` | drift main `kW^{Cε}Γ³Ls ≤ N^{ε₀}/12` (`ha2`) on `(Φ+Φ²)B_v^k`; the three groups (`Λ^{1/2}`: `5/6`; `Φ`: `1/12`; `Φ²`: `1/12`) are each `≤ N^{ε₀}` times their own factor, and `Λ^{1/2} ≥ 1` lets the `Λ`-free pieces sit under `Λ^{1/2}B_v^k` | `1/6`, `11/12`, `11/12` |
| 10 | limit regime (T2167 (d) order): `(d,k,Λg,κ') → C → ε₀ → ε₁ = εq = ε₀/8, ε = ε₀/(8C) → D'', D'` | with `W ≥ N^𝔠`, `W^d ≤ N`, `g` bounded: `ha1` exp `≤ ε₀(1/8d+1/8)`, slack `≥ 5ε₀/6` (d=3); `ha2` `3ε₁+ε₀/(8d) = 5ε₀/12` + `log N`, slack `7ε₀/12`; `ha3` `7ε₀/24`, slack `17ε₀/24`; `he1` needs `𝔠(D'-C) ≥ k+1`; `he2` needs `D'' ≥ C + (4k+1)/𝔠` (three pieces: `2k-1+..`, `(3k-1)/2+..`, `k+..` vs `𝔠D''/2`), `D' = D''+1`; `he3`: `D_Y ≥ k+1`; `he4`: `D_t ≥ k+1` | strict negative exponent `≥ 1/2` in `he1–he4`; table below (`𝔠 = 1/6`, `D'' = C+24k+12`) |

`ε` (kernel) and `εq` (Azuma) are different parameters; `D', D''` are chosen after `C` (`W^C` in the far parts). The far parts `N^k W^{C-D'}`, `N^k√(qvFar W^{-D''})` become small only through `Bandwidth` in S3-12.

### (ii) One concrete nondegenerate instance
Data (`sz0`, `n = 0`: `L=4, W=32, N=2^21, g=1/64`), `d=3`, `E=1/2`, `s=0`, `v=1/32`, `K=4` (`Δ=1/128`, `u_j=j/128`), `k=3`, `Λg=10`, `κ'=1/2`, `ε=4/5`, `Γ=4, Λ=3, Φ=1`, `D'=6, D''=5`, `ε₁=2/21` (`N^{ε₁}=(2^21)^{2/21}=4`), `X0=4B_0^3`, `τK=1/21`, `εq=1`, `D_Y=1`, `D_t=-5`, `ε₀=C+12`. Target 4 `budgetNonAltN`: every hypothesis, the seven numerical inequalities for `C ∈ {1/2,1,5,20}` (and `C=10⁻³, 0.1` checked separately), `hlog`, `hR` at `n=0`, and the assembled RHS against `N^{ε₀}(√3+2)B_v^3`.
Command: `cd $SCR && python3 inst.py` (`SCR` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2179`; mpmath 60 digits; `stepErrN`, `envConst`, `kStepC`, `uStepC`, `Bparam d L g t 0` transcribed from the merged text)
```
N=2^21, W=32, g=1/64, Delta=0.0078125, u_j=j/128: [0.0, 1.0, 2.0, 3.0, 4.0]
N^e1 = 4.0 (= Gamma 4);  Im m(1/2) = 0.968245836551854221294816349945599902708230426322897706646893
hlog: sum=0.032660118423185044 <= Ls=15.033465925964045;  hR: log2 sum=100.17609617007002 vs log2 N^5=105.0
N^{1/21}*... Delta/eta_v=0.008328996443456811, eta_v^-1=1.0661115447624718
C=  0.5 eps0= 12.5  log10(LHS/RHS): ha1 -77.0 ha2 -73.9 ha3 -69.6 he1 -67.3 he2 -42.9 he3 -65.6 he4 -27.7 | all<=1:True | log10(RHS_asm/budget)=-36.0
C=  1.0 eps0= 13.0  log10(LHS/RHS): ha1 -79.6 ha2 -76.4 ha3 -72.1 he1 -69.7 he2 -45.5 he3 -68.8 he4 -30.8 | all<=1:True | log10(RHS_asm/budget)=-39.1
C=  5.0 eps0= 17.0  log10(LHS/RHS): ha1 -100.1 ha2 -96.9 ha3 -92.6 he1 -88.9 he2 -66.0 he3 -94.0 he4 -56.1 | all<=1:True | log10(RHS_asm/budget)=-64.4
C= 20.0 eps0= 32.0  log10(LHS/RHS): ha1 -176.8 ha2 -173.7 ha3 -169.4 he1 -161.2 he2 -142.7 he3 -188.9 he4 -150.9 | all<=1:True | log10(RHS_asm/budget)=-159.2
hypotheses: {'2<=k': True, '|E|<2': True, '0<=s<=v<1': True, 'K!=0': True, 'eta_v^-1<=N': True, 'Delta*eta_v^-1<=1': True, '1<=Lam, 0<=Phi': True, 'hlog': True, 'hX0 (N^e1=(2^21)^(2/21)=4 exactly, X0=4 B_0^3)': True, 'hR (sum<=N^-Dt)': True} ALL: True
```
`hR` slack at `n=0` is `2^{4.82}` (sum `2^{100.18}` vs `N^5 = 2^{105}`); with `D_t = -6` it would be `2^{25.8}`, and `he4` still holds (`2^{189} ≤ 2^{21C+252}/6`). `ha1–he4` for all `C > 0`: the log2 left sides grow at most like `4C, 4C, 4C, 5C, 4.5C` (and are constant for `he3, he4`) against `21C` on the right; margins at `C = 10⁻³` are as large as at `C = 1/2` (rows above), so the instance is `C`-uniform for the abstract `C = nqGood1C 3 3 10 (1/2) > 0`.

Targets 2 and 3, instance (a) (constant weights `κ≡2, ε≡1`, `Cκ = Cfar = 2`, `Ce = Cc = 1`, `G = 3`, `a = 1`, `b = δ = 1/2`, `Wd = 1/2`, `B_i = Bctl(0, u_i)`), and target 5 (instance (d), `GridEnvelopeNCheck` data, premises of `SumWeightedStepErrN_Stmt`): command `cd $SCR && python3 gen.py`
```
B_0..B_4 = [3.0986966521151624e-05, 3.1230899284571097e-05, 3.147870305132705e-05, 3.1730470702636844e-05, 3.1986298115142864e-05] nondecreasing: True
hyp tbInitN: kap*B_0^k <= Ck*B_K^k: True
tbInitN: kap*X0=1.7852064165793325e-13 <= Ck*G*B_K^k=1.9635555498206835e-13
hyp tbDriftN: kap*B_j^k<=Ck*B_K^k (j<K): True
tbDriftN: lhs=0.04687500000000201 <= rhs=0.04687500000000214: True
hyp tbQvN: kap*B_{j+1}^k<=Ck*B_K^k: True
tbQvN: lhs=0.328125 <= rhs=0.328125: True
(d) four C_K inequalities: [20.0, 13.5, 5.5, 0.5] < 21
(d) |E|=0<=2-kappa=1, s=0<=v=1/2<1, N^(-1/2)<=1/2 iff N>=4 (N(0)=2^21)
(d) n=      0: log10 N=6.3  log_N(sum bound)=-5.13  (need <= -1=-D_t)
(d) n=     10: log10 N=25.1  log_N(sum bound)=-6.16  (need <= -1=-D_t)
(d) n=   1000: log10 N=60.3  log_N(sum bound)=-6.36  (need <= -1=-D_t)
(d) n=1000000: log10 N=114.3  log_N(sum bound)=-6.42  (need <= -1=-D_t)
```
Target 5 external-statement limit (lesson 14): `K n = N^{21}`, `Δ = 1/(2K)`, bound `27·K·(envConst Δ^{3/2} + kStepC Δ² + uStepC(...))` with every term at its worst time `u = 1/2`, `B_k = N^{1/2}η^{-3}`; `log_N` of it is `≤ -5.1 < -1 = -D_t` at `n = 0` and tends to about `-6.4` (rows `(d) n=...` above). Target 5 is a conjunction of two merged `∀ᶠ n` facts at `m = K n`; `hlog` is `sum_gridStep_div_etaT_le`, `hR` is `sum_weighted_stepErrN_le` at `m = K n ≤ K n`; the four `C_K` inequalities hold (`20, 13.5, 5.5, 0.5 < 21`).

Limit regime for the consumer (row 10): `cd $SCR && python3 lim.py`
```
sz0, E=1/2, k=3, eps0=1/10, eps1=epsq=eps0/8, eps=eps0/(8C), D''=C+24k+12, D'=D''+1, D_Y=k+2, D_t=k+1; cols ha1 ha2 ha3 he1 he2 he3 he4 = log10[LHS/(N^eps0/c)], <=0 holds
n=10       C=0.5  log10N^e0=  2.51     -1.33     1.85     0.41  -496.76  -159.04   -51.86   -26.80
n=10       C=1.0  log10N^e0=  2.51     -1.33     1.85     0.41  -496.76  -160.72   -51.86   -26.80
n=10       C=5.0  log10N^e0=  2.51     -1.33     1.85     0.41  -496.76  -174.15   -51.86   -26.80
n=10       C=20.0 log10N^e0=  2.51     -1.33     1.85     0.41  -496.76  -182.48   -51.86   -26.80
n=100      C=0.5  log10N^e0=  4.24     -2.79     1.05    -0.71  -855.74  -277.26   -88.26   -45.86
n=100      C=1.0  log10N^e0=  4.24     -2.79     1.05    -0.71  -855.74  -280.14   -88.26   -45.86
n=100      C=5.0  log10N^e0=  4.24     -2.79     1.05    -0.71  -855.74  -303.19   -88.26   -45.86
n=100      C=20.0 log10N^e0=  4.24     -2.79     1.05    -0.71  -855.74  -316.85   -88.26   -45.86
n=1000     C=0.5  log10N^e0=  6.03     -4.29     0.15    -1.92 -1227.09  -399.54  -125.91   -65.58
n=1000     C=1.0  log10N^e0=  6.03     -4.29     0.15    -1.92 -1227.09  -403.67  -125.91   -65.58
n=1000     C=5.0  log10N^e0=  6.03     -4.29     0.15    -1.92 -1227.09  -436.68  -125.91   -65.58
n=1000     C=20.0 log10N^e0=  6.03     -4.29     0.15    -1.92 -1227.09  -455.85  -125.91   -65.58
n=1000000  C=0.5  log10N^e0= 11.43     -8.83    -2.76    -5.64 -2345.33  -767.78  -239.30  -124.98
n=1000000  C=1.0  log10N^e0= 11.43     -8.83    -2.76    -5.64 -2345.33  -775.65  -239.30  -124.98
n=1000000  C=5.0  log10N^e0= 11.43     -8.83    -2.76    -5.64 -2345.33  -838.66  -239.30  -124.98
n=1000000  C=20.0 log10N^e0= 11.43     -8.83    -2.76    -5.64 -2345.33  -874.42  -239.30  -124.98
```
`ha2` and `ha3` are positive for `n ≤ 10³` at `ε₀ = 1/10` (polylog factor `Ls` and the constants `1/12` against `N^{ε₀}`) and negative from `n = 10⁶` (`-8.8, -2.8` decades), as the exponent counts of row 10 predict (`ε₀ > 3ε₁ + ε₀/(8d)`); this is "for large `n`" in S3-12, not a defect of the pin. `he1–he4` hold at every row.

### Verdicts
- Target 1 (vocabulary, pinned text): PASS (no hypotheses; `qvShape`, `kapFar`, `qvFar` agree with `qvBdNonAltN` and with the far bound, rows 3 and 6).
- Target 2 (`nqBudget_im_le_one`, `_inv_one_sub_le`, `_sum_succ_le`, `_sqrt_add_le`, `_kappa_le_kapFar`): PASS (rows 3, 7).
- Target 3 (`tbInitN`, `tbDriftN`, `tbQvN`): PASS (instance (a) above; the hypotheses of RBM2D `tbInit`/`tbDrift`/`tbQv` with `(scaleM^k)⁻¹ ↦ B^k` suffice, no `N`-dependence is needed).
- Target 4 (`qvBdNonAltN_eq_qvShape`, `tbInitNonAltN`, `tbDriftNonAltN`, `tbQvNonAltN`, `budgetNonAltN`): PASS. All seven term estimates close with the stated coefficients (rows 2–9; coefficients `5/6` of `Λ^{1/2}B_v^k`, `1/12` of `ΦB_v^k`, `1/12` of `Φ²B_v^k`), no hypothesis beyond the pinned ones is used (`N ≥ 1`, `Γ ≥ 1`, `Ls ≥ 0` are derived from the pinned `hη`, `hΓ`, `hlog`, `hΔη`); the pinned `hlog` is the literal conclusion of `sum_gridStep_div_etaT_le`.
- Target 5 (`nqBudget_merged_inputs`): PASS (the pinned `hlog`, `hR` are the literal conclusions of the two merged theorems at `m = K n`).

## (a′) Preflight corrections — Mon Oct  5 06:50:25 UTC 2026
- Line 78 of (a) ("`ha2` and `ha3` are positive for `n ≤ 10³` ... negative from `n = 10⁶` (`-8.8, -2.8` decades)") misreads the pasted `lim.py` table. In the columns `ha1 ha2 ha3 he1 he2 he3 he4` (rows `C = 0.5`): `ha2` = 1.85, 1.05, 0.15, -2.76 and `ha3` = 0.41, -0.71, -1.92, -5.64 at `n = 10, 10², 10³, 10⁶`; `-8.83` is `ha1` at `n = 10⁶`. So `ha3` is positive only at `n = 10` and `ha2` up to `n = 10³`; both are negative at `n = 10⁶`.
- No verdict changes: row 10 claims only eventual validity (the last row of the table has all seven columns negative), and at `n = 0` all seven inequalities hold by the `inst.py` output of (ii). The Lean instance (c) proves `ha1`-`he4` at `n = 0` for every `C > 0`.

## (b) Script output — Mon Oct  5 06:50:25 UTC 2026

### Build, hygiene, registry pre-check
```
$ cd RBM3D-wt/T2179 && lake build RBM3D.Induction.NQBudget          (build2.out; started Mon Oct  5 06:46:16 UTC 2026)
exit=0   | grep -n NQBudget build2.out | grep -v "depends on axioms"  ->  "Replayed RBM3D.Induction.NQBudget" (no warning line from NQBudget.lean)
Build completed successfully (3840 jobs).
$ lake build        (whole library in the worktree, root RBM3D.lean does not yet import the module; the hub adds the import at merge)
Build completed successfully (3978 jobs).
exit=0
$ scratch file: import RBM3D / import RBM3D.Induction.NQBudget / #assert_rbm_axioms   (lake env lean assert.lean, exit=0)
axiom audit: 5356 theorems, 1890 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Induction/NQBudget.lean   ->  0
$ git diff --stat main...t/T2179        (commit c3ce7445e603e533cb4f9551578211f7eb51f250 Jun Yin 2026-10-04T23:45:55-07:00)
 RBM3D/Induction/NQBudget.lean | 1511 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1511 insertions(+)
```

### `#print axioms` of every public declaration (the file ends with 26 `#print axioms` lines: 18 targets, 8 instance theorems; `build2.out`)
```
$ grep "NQBudget.lean.*depends on axioms" build2.out | sed ... | sort | uniq -c        (axiom sets of the 26 lines)
      26 [propext, Classical.choice, Quot.sound]
names: assembledRHSNonAltN, nqBudget_qvShape, nqBudget_kapFar, nqBudget_qvFar, nqBudget_im_le_one, nqBudget_inv_one_sub_le, nqBudget_sum_succ_le, nqBudget_sqrt_add_le, nqBudget_kappa_le_kapFar, tbInitN, tbDriftN, tbQvN, qvBdNonAltN_eq_qvShape, tbInitNonAltN, tbDriftNonAltN, tbQvNonAltN, budgetNonAltN, nqBudget_merged_inputs
instances: tbInitN_instance, tbDriftN_instance, tbQvN_instance, hR_instance, hlog_instance, budgetNonAltN_instance, nqBudget_merged_inputs_instance, nqBudget_merged_inputs_exists
```

### Target 1 and the pin of target 4 against the check file (`cmp.py`: text of the four definitions; hypotheses of `budgetNonAltN` against the body of `budgetNonAltN_pin`)
```
def assembledRHSNonAltN    docstring+text identical to check file: True (19 lines)
def nqBudget_qvShape       docstring+text identical to check file: True (5 lines)
def nqBudget_kapFar        docstring+text identical to check file: True (5 lines)
def nqBudget_qvFar         docstring+text identical to check file: True (6 lines)
ALL FOUR IDENTICAL: True
theorem budgetNonAltN: 22 hypothesis binders, names in order: hk hε₁ hE hs0 hsv hv1 hK hη hΔη hΓ hΛ hΦ hlog hX0 hR ha1 ha2 ha3 he1 he2 he3 he4
pin: 22 hypotheses (arrows before the conclusion)
variable binders identical: True
hypotheses syntactically identical: 20 of 22 ; the other 2 (hlog, hR) differ only by the parentheses around the leading ∑
hypotheses pairwise identical after dropping those parentheses: True 22 of 22
conclusion identical: True
$ lake env lean pincheck.lean   (check-file sections 2-3 verbatim + `theorem pin_ok : budgetNonAltN_pin := fun .. => RBM.Ind.budgetNonAltN ..`)
'RBM.Ind.T2179Check.pin_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Statements of targets 2-5 (`ext2.py stmt`, whitespace collapsed; `sz` is a `variable (sz : Sizes d)` of its section where not shown)
```
theorem nqBudget_im_le_one (E : ℝ) : (mE E).im ≤ 1
theorem nqBudget_inv_one_sub_le {E v Nn : ℝ} (hE : |E| < 2) (hv1 : v < 1) (hη : (etaT E v)⁻¹ ≤ Nn) : (1 - v)⁻¹ ≤ Nn
theorem nqBudget_sum_succ_le {K : ℕ} (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) : ∑ j ∈ Finset.range K, f (j + 1) ≤ ∑ j ∈ Finset.range K, f j + f K
theorem nqBudget_sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y
theorem nqBudget_kappa_le_kapFar {d : ℕ} (sz : Sizes d) (n k : ℕ) (Λg κ' ε : ℝ) (u : ℕ → ℝ) {i m : ℕ} (hu0 : 0 ≤ u i) (hium : u i ≤ u m) (hm1 : u m < 1) (hN : (1 - u m)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : 
kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε u i m ≤ nqBudget_kapFar sz n k Λg κ' ε
theorem tbInitN {k K : ℕ} {Cκ G X0 : ℝ} (B : ℕ → ℝ) (κ : ℕ → ℕ → ℝ) (hκ0 : 0 ≤ κ 0 K) (hG : 0 ≤ G) (hker : κ 0 K * B 0 ^ k ≤ Cκ * B K ^ k) (hX0 : X0 ≤ G * B 0 ^ k) : κ 0 K * X0 ≤ Cκ * G * B K ^ k
theorem tbDriftN {E : ℝ} {k K : ℕ} {Δ Cκ Cε Cfar a b δmax : ℝ} (u B : ℕ → ℝ) (κ ε : ℕ → ℕ → ℝ) (dd δ : ℕ → ℝ) (hΔ : 0 ≤ Δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hκ0 : ∀ j < K, 0 ≤ κ (j + 1) K) (hε0 : ∀ j < K, 0 
≤ ε (j + 1) K) (hκM : ∀ j < K, κ (j + 1) K * B j ^ k ≤ Cκ * B K ^ k) (hκfar : ∀ j < K, κ (j + 1) K ≤ Cfar) (hεC : ∀ j < K, ε (j + 1) K ≤ Cε) (hd : ∀ j < K, dd j ≤ a * (B j ^ k / etaT E (u j)) + b) 
(hδ0 : ∀ j < K, 0 ≤ δ j) (hδ : ∀ j < K, δ j ≤ δmax) (hη : ∀ j < K, 0 < etaT E (u j)) : Δ * ∑ j ∈ Finset.range K, (κ (j + 1) K * dd j + ε (j + 1) K * δ j) ≤ Cκ * a * B K ^ k * ∑ j ∈ Finset.range K, Δ 
/ etaT E (u j) + ((K : ℝ) * Δ) * (Cfar * b + Cε * δmax)
theorem tbQvN {E : ℝ} {k K : ℕ} {Cκ Cfar Ce Cc G Wd Δ : ℝ} (u B κ : ℕ → ℝ) (hB0 : ∀ j < K, 0 ≤ B (j + 1)) (hκ0 : ∀ j < K, 0 ≤ κ j) (hκM : ∀ j < K, κ j * B (j + 1) ^ k ≤ Cκ * B K ^ k) (hκfar : ∀ j < 
K, κ j ≤ Cfar) (hG : 0 ≤ G) (hWd : 0 ≤ Wd) (hCe : 0 ≤ Ce) (hΔ : 0 ≤ Δ) (hη : ∀ j < K, 0 < etaT E (u (j + 1))) : ∑ j ∈ Finset.range K, Δ * ((k : ℝ) * nqBudget_qvShape k (κ j) Ce Cc G Wd (B (j + 1)) 
(etaT E (u (j + 1)))) ≤ (k : ℝ) * Cκ ^ 2 * G * (B K ^ k) ^ 2 * ∑ j ∈ Finset.range K, Δ / etaT E (u (j + 1)) + ((K : ℝ) * Δ) * ((k : ℝ) * ((Cfar * (Cfar + Ce) + Cc) * Wd))
theorem qvBdNonAltN_eq_qvShape (n k : ℕ) (E : ℝ) (Λg κ' ε Γ Λ D'' u w : ℝ) : qvBdNonAltN sz n E k Λg κ' ε Γ Λ D'' u w = nqBudget_qvShape k (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.lam n 
^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ') (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ k) (Γ * (Γ * Λ)) (((sz.W n : ℕ) : ℝ) ^ 
(-D'')) (sz.Bctl n u) (etaT E u)
theorem tbInitNonAltN {s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε G X0 : ℝ) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hG : 0 ≤ G) (hX0 : X0 ≤ G * (sz.Bctl n (s n)) ^ k) : 
kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 0 (K n) * X0 ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * G * (sz.Bctl n (v n)) ^ k
theorem tbDriftNonAltN {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε : ℝ) (Γ Φ : ℕ → ℝ) (D' : ℝ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hk : 1 ≤ k) (hΓ : 
0 ≤ Γ n) (hΦ : 0 ≤ Φ n) (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : gridStep s v K n * ∑ j ∈ Finset.range (K n), (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) 
(j + 1) (K n) * dDriftNonAltN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ n) + epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k 
Λg κ' * ε) * (Γ n * (Γ n * Φ n) * (((k : ℝ) - 1) + (k : ℝ) * (Γ n * Φ n))) * (sz.Bctl n (v n)) ^ k * ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) + ((K n : ℝ) * 
gridStep s v K n) * (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D'))
theorem tbQvNonAltN {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ : ℕ → ℝ) (D'' : ℝ) (a : Fin k → Zd d (sz.L n)) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K 
n ≠ 0) (hΛ : 0 ≤ Λ n) (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : ∑ j ∈ Finset.range (K n), (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' (K n) a j : ℝ) ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ 
(nqGood1C d k Λg κ' * ε)) ^ 2 * (Γ n * (Γ n * Λ n)) * ((sz.Bctl n (v n)) ^ k) ^ 2 * ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n (j + 1)) + ((K n : ℝ) * gridStep s v K n) 
* ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))
theorem nqBudget_merged_inputs {d : ℕ} (sz : Sizes d) {κ τ' τK C_K D_t : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) (hκ : 0 < κ) (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) (hτK : 0 < τK) (hDt : 0 ≤ D_t) (hk : 2 ≤ k) 
(hsize : sz.SizeTendsto) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0) (hrange : sz.RangeCond τ' v) (h1 : 8 + (4 * (k : ℝ) + 8) * (1 
- τ') + 2 * D_t < C_K) (h2 : 3 + 4 * τK + 5 * (k : ℝ) * (1 - τ') + D_t < C_K) (h3 : 2 * (1 - τ') + τK + 2 * (k : ℝ) * (1 - τ') + D_t < C_K) (h4 : 1 - τ' < C_K) (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : 
ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) : ∀ᶠ n : ℕ in atTop, (∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ∧ (∑ j ∈ Finset.range 
(K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) (gridStep s v K n) (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) 
(gridTime s v K n (j + 1)))⁻¹ ^ k) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t))
theorem budgetNonAltN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ Φ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) (a : Fin k → Zd d (sz.L n)) (hk : 2 ≤ k) (hε₁ : 0 
≤ ε₁) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hΔη : gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1) (hΓ : Γ 
n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ : 0 ≤ Φ n) (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) 
(hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) 
(gridTime s v K n (j + 1)) (gridStep s v K n) (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t)) (ha1 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k 
Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) (ha2 : (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 3 * ((mE (E n)).im⁻¹ * 
Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ * Real.sqrt ((k : ℝ) 
* ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (he1 : ((sz.size n : ℕ) : ℝ) ^ k * (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) 
≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k * Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤ ((sz.size n 
: ℕ) : ℝ) ^ ε₀ / 12) (he3 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) (he4 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size 
n : ℕ) : ℝ) ^ ε₀ / 6) : assembledRHSNonAltN sz E s v K n k Λg κ' ε Γ Λ Φ D' D'' D_Y τK εq X0 a ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ n + Φ n ^ 2) * (sz.Bctl n (v n)) ^ k
```

### Compiled nonempty instances (`namespace RBM.Ind.NQBudgetInst`: 9 anonymous `example`s (target 2 and four target-4 statements) and 8 named instance theorems; `budgetNonAltN_instance` shown)
```
theorem budgetNonAltN_instance : assembledRHSNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 6 5 1 (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤ ((sz0.size 0 : ℕ) : ℝ) ^ (nqGood1C 
3 3 10 (1 / 2) + 12) * (Λ3 0 ^ ((1 : ℝ) / 2) + Φ1 0 + Φ1 0 ^ 2) * (sz0.Bctl 0 (vg 0)) ^ 3 := budgetNonAltN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 6 5 1 (-5) (1 / 21) 1 (nqGood1C 3 3 10 
(1 / 2) + 12) (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar (by norm_num) (by norm_num) (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg]) (by norm_num [Kg]) 
eta_inv_le_N (by rw [step0]; linarith [eta_inv_le_v]) (by rw [N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1]) hlog_instance (by rw [N_eps1]) hR_instance (ha1_inst _ Cpos) (ha2_inst _ Cpos) (ha3_inst _ 
Cpos) (he1_inst _ Cpos) (he2_inst Cpos) (he3_inst _ Cpos) (he4_inst _ Cpos)
```

### Name clash and port citations
```
$ grep -rnwE "NQBudgetInst|nqBudget_[A-Za-z_0-9]*|tbInitN|tbDriftN|tbQvN|tbInitNonAltN|tbDriftNonAltN|tbQvNonAltN|budgetNonAltN|qvBdNonAltN_eq_qvShape|assembledRHSNonAltN" RBM3D | wc -l
main worktree (main = 4c52041): 0    ; branch worktree, `--exclude=NQBudget.lean`: 0
Port: RBM2D `RBM2D/Induction/NonAltBudget.lean` at c9a24cf, §1 :57, §2 :77-158, §3 :173-307, §4 :386-516, §5 :587, §5b :815 (read with `git show c9a24cf:...`).
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  ->  9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/NonAltBudget.lean
 RBM2D/Induction/NonAltBudget.lean | 709 ++------------------------------------
 1 file changed, 35 insertions(+), 674 deletions(-)
$ grep -nE "Bandwidth|pathP|volume|lemT" RBM3D/Induction/NQBudget.lean
554:  parts become small only in S3-12 through `Bandwidth`. -/
```

### Narrative (stage 1b)
- Delivered: `RBM3D/Induction/NQBudget.lean` (new, 1511 lines, commit c3ce744 on `t/T2179`, the only file of the diff): the four definitions of target 1 and targets 2-5 (18 public names in all), and `NQBudgetInst` with 9 `example`s (the five facts of target 2; `qvBdNonAltN_eq_qvShape`, `tbInitNonAltN`, `tbDriftNonAltN`, `tbQvNonAltN`) and 8 instance theorems (`tbInitN`, `tbDriftN`, `tbQvN`; `hR`, `hlog`, `budgetNonAltN`; `nqBudget_merged_inputs` and its `∃ n` form). `RBM3D/Test/Axioms.lean` is not touched (the file states no `Prop`).
- Section (a) needed one prose correction ((a′), no verdict changes); no definition, pin or hypothesis list of the ticket was changed. `budgetNonAltN` equals `budgetNonAltN_pin`: binders identical, 22 hypotheses (20 syntactically, `hlog`/`hR` differ only by parentheses around a leading `∑`), conclusion identical; `pin_ok` compiles by `exact budgetNonAltN ..`.
- Route of `budgetNonAltN`: `T1` = `tbInitNonAltN` + `ha1`; `T2` and the drift far part = `he1` + `N⁻¹ ≤ B_v` (`ContinuityNet.cont_inv_size_le_Bctl`); `T3` = `tbDriftNonAltN` + `hlog` + `a ≤ kΓ³(Φ+Φ²)` + `ha2`; `T4` = `tbQvNonAltN` + `nqBudget_sum_succ_le` with `hΔη` + `nqBudget_sqrt_add_le` + `ha3` + `he2`; `T5` = `he3`; `T6` = `hR` + `he4`; then the private real lemma `nqBudget_final` (coefficients `5/6` of `Λ^{1/2}B_v^k`, `1/12` of `ΦB_v^k` and of `Φ²B_v^k`). `C = nqGood1C` stays abstract; no sign of `C` is used.
- Differences from the ticket's prose (none is a pin): `tbQvNonAltN` is stated with `(W^{Cε})²` for `W^{2Cε}`; `tbQvN` assumes `0 ≤ B (j+1)` for `j < K` (`tbInitN`, `tbDriftN` need no sign of `B`); `hs0` of `tbInitNonAltN` is kept as listed but is unused; `nqBudget_kappa_le_kapFar` is stated at `sz.lam n` and `(sz.W n : ℝ)`, as `nqBudget_kapFar` is.
- Instance (c) (`d = 3`, `sz0`, `n = 0`, `ε₀ = C + 12`, abstract `C = nqGood1C 3 3 10 (1/2) > 0` by `nqGood1C_pos`): all 22 hypotheses are discharged. `ha1`-`he4` are proved for every `C > 0` with `x = 2^C ≥ 1`, `W^{Cε} = x⁴`, `W^C = x⁵`, `N^{ε₀} = x²¹·2²⁵²`, `x^m c ≤ x²¹ 2²⁵²/12`. `hlog`: the sum is `≤ 4Δ(11/10)`, `Ls = Im⁻¹·21 log 2 ∈ [14, 16]`. `hR` (`D_t = -5`, `τK = 1/21`): with `η⁻¹ ≤ 11/10`, `Δ^{3/2} ≤ 1/1408`, `kStepC` at `B_k ≤ 3`, `uStepC ≤ 1`, the sum is `≤ 4 (63/31)³ SE`, and `log₂` of that bound is 100.442 (python, exact fractions) against `log₂ N⁵ = 105`.
- Instance (d): `nqBudget_merged_inputs` at the `GridEnvelopeNCheck` data (`κ = 1`, `τ' = τK = 1/2`, `C_K = 21`, `D_t = 1`), `∀ᶠ n` and the `∃ n` consequence. The theorem carries `0 ≤ D_t` (premise of the merged `sum_weighted_stepErrN_le`); `budgetNonAltN` allows every real `D_t`.
- §29 checklist: (1) `0 ≤ s n`, `s n ≤ v n`, `v n < 1` are `hs0 hsv hv1`; (2) `v ≤ 1 - g²/L²` is not used (no `lemT`, no `g²/L²` in the file); (3) no `L^d ≤ W^K`, no `W ≥ N^𝔠`: `Bandwidth` occurs only in the docstring (grep above); the far parts are `N^k W^C W^{-D'}` and `N^k √(k qvFar W^{-D''})`, small only in S3-12 through `Bandwidth`, with `D', D''` chosen after `C`; (4) fixed `n` throughout except `nqBudget_merged_inputs` (its `∀ n` premises are those of the two merged statements); (5) deterministic (no `pathP`, `volume`); (6) no hypothesis on `sz.lam n` (every real `g`) or `1 < W`; (7) the normalisation is `B_v^k = (sz.Bctl n (v n))^k` of `STNQConcl`.

## (c) Verified Mathlib names (`#check` in names.lean after `import RBM3D.Induction.NQBudget`; all also used by the compiled file)
```
Real.sqrt_le_iff : ∀ {x y : ℝ}, √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2
Real.le_sqrt' : ∀ {x y : ℝ}, 0 < x → (x ≤ √y ↔ x ^ 2 ≤ y)
Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
Real.sqrt_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), √(x * y) = √x * √y
Real.sqrt_eq_rpow : ∀ (x : ℝ), √x = x ^ (1 / 2)
Real.coe_toNNReal : ∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
Real.rpow_one : ∀ (x : ℝ), x ^ 1 = x
Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
Real.one_le_rpow : ∀ {x z : ℝ}, 1 ≤ x → 0 ≤ z → 1 ≤ x ^ z
Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
Real.log_pow : ∀ (x : ℝ) (n : ℕ), Real.log (x ^ n) = ↑n * Real.log x
Real.log_nonneg : ∀ {x : ℝ}, 1 ≤ x → 0 ≤ Real.log x
Real.log_two_gt_d9 : 0.6931471803 < Real.log 2
Real.log_two_lt_d9 : Real.log 2 < 0.6931471808
pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [Mul
pow_le_pow_right₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} {m n : ℕ} [ZeroLEOneC
one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMul
one_le_inv₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 
div_le_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}
le_div_iff₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}
mul_div_cancel₀ : ∀ {G₀ : Type u_1} [inst : CommGroupWithZero G₀] {b : G₀} (a : G₀), b ≠ 0 → b * (a / b) = a
Finset.sum_range_succ' : ∀ {M : Type u_1} [inst : AddCommMonoid M] (f : ℕ → M) (n : ℕ), ∑ k ∈ Finset.range (n + 1), f 
Finset.sum_congr : ∀ {ι : Type u_1} {M : Type u_2} {s₁ s₂ : Finset ι} [inst : AddCommMonoid M] {f g : ι → M}, s₁ = s₂ 
Nat.one_le_pow : ∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
Filter.Eventually.exists : ∀ {α : Type u_1} {p : α → Prop} {f : Filter α} [f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
```

## (d) Open issues and paper-delta candidates
- `T2179a` (budget target): `assembledRHSNonAltN ≤ N^{ε₀}(Λ^{1/2} + Φ + Φ²) B_v^k`; the `Φ²` is the `kΓ³Φ²` part of `dDriftNonAltN` (clause (D2) of `GoodSetN`), where RBM2D `budgetNonAlt` (`NonAltBudget.lean:587`, c9a24cf) has `(Λ^{1/2} + Φ) M_v^{-k}`; `B_v^k = (W^{-d}B_{v,0})^k` replaces `M_v^{-k}`.
- `T2179b`: hypothesis `hΔη : Δ η_v⁻¹ ≤ 1` replaces RBM2D `hΔN : Δ N ≤ 1`; it is used only for `Δ/η_v ≤ 1` in `Σ_j Δ/η_{u_{j+1}} ≤ Ls + 1`.
- `T2179c`: the far parts carry `W^C` (`C = nqGood1C`, abstract): `he1 : N^k W^C W^{-D'} ≤ N^{ε₀}/12` and `he2` with `nqBudget_qvFar` (`kapFar = W^{Cε}((1+g²)N)^{k-1}`); `D', D''` must be chosen after `C`. RBM2D has `he1`-`he5` with `cKap`/`aQv`; here the pin has `he1`-`he4` and `ha1`-`ha3` without `cCase1`, `cPair1`, `(1+log L)^k`.
- `T2179d`: `N⁻¹ ≤ B_v` (`cont_inv_size_le_Bctl`) replaces `M_v ≤ N` (RBM2D `scaleM_le_size`); `κ_{i,m} ≤ nqBudget_kapFar` via `r_{i,m} ≤ (1+g²)(1-u_m)⁻¹ ≤ (1+g²)N` replaces RBM2D `NonAltBudget_far_kappa` (`κ ≤ C_κ N^k`).
- `T2179e`: `ha2` reads `k W^{Cε}(N^{ε₁})³ Ls ≤ N^{ε₀}/12` (from `Γ²Φ((k-1)+kΓΦ) ≤ kΓ³(Φ+Φ²)`, `Γ ≥ 1`), against RBM2D `((k-1)²+1) cKap (N^{ε₁})² Ls`.
- Open for S3-12 (not defects of this ticket): `ha1`-`he4` are hypotheses here; `he1`, `he2` need `W ≥ N^𝔠` (`Bandwidth`) and `D', D''` large after `C`; `ha2`, `ha3` carry the factor `Ls` (a `log N`) and hold only for large `n` at fixed `ε₀` (limit table of (a), read as in (a′): at `ε₀ = 1/10`, `ha2` is positive up to `n = 10³` and negative at `n = 10⁶`; `ha3` is negative from `n = 10²`).
- `nqBudget_merged_inputs` needs `0 ≤ D_t`, so the `hR` it yields has `N^{-D_t} ≤ 1`; instance (c) uses `D_t = -5` only at `n = 0`, where `hR` is proved directly.
- `RBM2D/Induction/NonAltBudget.lean` at HEAD differs from `c9a24cf` (diff-stat above); the port was read at `c9a24cf` as the ticket says. Mathlib names verified absent: none searched (every name used exists, section (c)). Root import of the module: the hub adds it at merge.
