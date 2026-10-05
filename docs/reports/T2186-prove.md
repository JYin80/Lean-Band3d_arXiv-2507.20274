Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 15:19:09 UTC 2026

Notation: `N = sz.size n`, `Γ = N^ε` (or `N^{ε₁}`), `B_u = Bctl n u`, `η_u = etaT E u`, `Ls = Im m(E)⁻¹ log N`, `X = B_v^k`, `P0 = N^{ε₀}`, `Λ^{1/2} = B_v^{-1/(4p)} XL(2k-1)^{1/2} XL(4p)^{1/(4p)}`. Scripts: `$SCR/{levels,table,inst,impl}.py`, `SCR=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2186` (exact `Fraction` / mpmath 40-50 digits; `STn12`, `STn12E`, `STbootRHS`, `Bparam`, `stepErr` transcribed from `Step34Pins.lean:340-410`, `Params.lean:36`, T2179 `inst.py`).

### (i) Exponent table
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | pin change 1(b) | `ε`-split `τ/2 + τ/2`: `N^{τ/2}(B^{1/6}N^{τ/2}XLK + R) ≤ N^τ(B^{1/6}XLK + R)` needs `N ≥ 1`, `B^{1/6} ≥ 0`, `R = STbootRHS 2 ≥ 0` (all need `u ≤ t_n < 1`; `XL, XLK ≥ 1`) | none lost |
| 2 | probability of 1(b) | old pin at `(τ/2, D+1)` plus new hypothesis `m = n_` at `(τ/2, D+1)`: `2N^{-(D+1)} ≤ N^{-D}` iff `N ≥ 2` (`SizeTendsto`) | factor `N/2` |
| 3 | sup over `w ∈ [s_n,u]` | `STsupXiLK = ⨆_{w∈Icc s u} Ξ̂_w ≤ N^{τ/2}XLK n_ n u` on the one event of `Prec` over `STPair` (union inside `P`, `StochDomAt` def `:61`); `Real.iSup_le` needs only the bound `≥ 0` | none lost |
| 4 | index ranges, `k = 2..8` | (D1') `k-l+2 ∈ [2,k-1] ⊆ Icc 2 (k-1)`; (D3') `STn12E k ∈ [k-1,k+1]`; (D2') `XLK(k+2-n') ≤ k`, `STn12 n' ≤ k-1`, `≥ 1`; all `XL` lengths `∈ [1,k+1]`, `XLK` lengths `∈ [2,k]` = hypothesis ranges of `NQLinConcl` | exact |
| 5 | `ε/3` split for `nqLinGood_holds` | (D1'), (D3'): `N^{ε/3}·N^{ε/3}` = `N^{2ε/3}` vs `Γ(ΓΦ) = N^{2ε}Φ`; (D2'): `N^{ε/3}(N^{2ε/3}Σ + B_u^{1/6}N^{ε/3}XLK_k) ≤ N^{ε}·Φ₂` (uses `B_u^{1/6} ≤ B_v^{1/6}`, `STBctl_mono`, `u ≤ v < 1`; linear, no `B ≤ 1`) | `4ε/3, 4ε/3, ε` in the exponent |
| 6 | `Φ₁ ≥ XLK(k-l+2)`, `Φ₃ ≤ ΣXL`, `Φ₂ ≤` pin sums | `Λ^{1/2} + Φ₁ + Φ₂ + Φ₃ ≤ B_v^{1/6}XLK_k + STbootRHS 2` (the pin RHS) with constant 1 | ratio `≤ 1` (max `0.99999998` in 20000 random cases) |
| 7 | drift identity 4(a) | `dDriftNonAltN Γ Φ = dDriftLinN Γ Φ (kΓΦ²) Φ`; `GoodSetN ⊆ GoodLinN Γ Φ (kΓΦ²) Φ` (D2: `Γ(k(ΓΦ)²) = Γ(Γ(kΓΦ²))`) | exact (0 error, 2000 rationals) |
| 8 | `tbDriftLinN` | `a = Γ²((k-2)Φ₁+Φ₂+Φ₃) ≥ 0` (`k ≥ 2`, `Φ_i ≥ 0`), `b = 0`; `(k-2)Φ₁+Φ₂+Φ₃ ≤ k(Φ₁+Φ₂+Φ₃)` | 0 violations in 5000 cases |
| 9 | budget coefficients (`P0·X`-pieces) | init `1/6`, `εK₀₀δ` `1/12`, drift far `1/12`, QV main `1/12` on `Λ^{1/2}X`, QV far `1/12`, `N^{-D_Y}` `1/6`, `N^{-D_t}` `1/6`: `Λ`-free `3/4 ≤ 3/4·Λ^{1/2}` plus `1/12` = `5/6 ≤ 1` on `Λ^{1/2}X` (`Λ ≥ 1`); each `Φ_iX`: `1/12 ≤ 1`; no `Φ²`, no crude `Φ` | `1/6`; `11/12` |
| 10 | `ha2'` (new): `kW^{Cε}(N^{ε₁})²Ls ≤ P0/12` | `W^{Cε} = W^{ε₀/8}` (`ε = ε₀/(8C)`, independent of `C`), `W ≤ N^{1/3}`; exponent `ε₀(1/24 + 1/4) = 0.2917ε₀` (was `ε₀(1/24+3/8) = 5ε₀/12` with `Γ³`) | slack `0.7083ε₀`; crossover `log10 N ≥ 48.61 / 51.45 / 56.24` for `k = 2/3/6` (polylog and the constant 12; the same character as T2179 row 10) |
| 11 | `ha1, ha3, he1-he4`, `D', D'', D_Y, D_t` | unchanged from `budgetNonAltN` (T2179 row 10): `ha1` exp `ε₀(1/24+1/8)`, `ha3` `7ε₀/24`, `he1` `𝔠(D'-C) ≥ k+1`, `he2` `D'' ≥ C + (4k+1)/𝔠`, `he3, he4`: `D_Y, D_t ≥ k+1` | as T2179 |
| 12 | `Λ ≥ 1` (`hΛ`) for the consumer | `XL ≥ 1` and `B_v ≤ 1` (`(con_st_ind)`, as `gridGoodN_holds`); `K+1 ≤ N^C` for the union (`highProbAt_iInter`) | instance `B_v = 3.2e-5`, `K+1 = 5 ≤ N` |

Gap closed (supervisor instance `XL ≡ 1`, `XLK ≡ N^δ`, `p = 2`, `B = N^{-β}`, `ε₀ = 1/10`; `log_N` of: pin RHS | primed budget | merged budget `N^{ε₀}(Λ^{1/2}+Φ+Φ²)`, `Φ = N^δ`):
```
  delta=0.025  k=3 beta=1.0 N=1e6: pin 0.168 | primed 0.252 (=pin+eps0-0.016) | merged 0.259 (=pin+eps0-0.009)
  delta=0.500  k=3 beta=1.0 N=1e6: pin 0.507 | primed 0.607 (=pin+eps0-0.000) | merged 1.100 (=pin+eps0+0.493)
  delta=2.000  k=6 beta=1.0 N=1e6: pin 2.131 | primed 2.231 (=pin+eps0-0.000) | merged 4.100 (=pin+eps0+1.869)
random check (20000 samples, k=2..9, p=1..6, B in (0,1], XL,XLK>=1): max (Lam^1/2+Phi1+Phi2+Phi3)/(B^1/6 XLK_k + STbootRHS 2) = 0.9999999792950087 (<=1)
```
(`python3 table.py`; 48 rows in all over `N = 10..10^6`, `β ∈ {1/2,1}`, `k ∈ {3,6}` in `$SCR/table.out`: primed `≤ pin + ε₀`, merged `= pin + ε₀ + δ`-type excess for `δ ≥ 1/2`.)

### (ii) One concrete nondegenerate instance
Data (`sz0`, `n = 0`: `d=3, L=4, W=32, N=2^21, g=1/64`; `E=1/2`; `s=0, v=1/32, K=4, Δ=1/128`; `k=3`, `Λg=10, κ'=1/2, ε=4/5`; `Γ=4=N^{2/21}`, `Λ=3`, `Φ₁=Φ₃=1`, `Φ₂=12=kΓΦ²`; `D'=6, D''=5, D_Y=1, D_t=-5, τ_K=1/21, ε_q=1`, `ε₀ = C+12`, `X0 = 4B_0³`). Target 5 `budgetNonAltLinN` (all 24 hypotheses) and 4(a)-(e) levels. Command `python3 inst.py`:
```
sz0,n=0: d=3 L=4 W=32 N=2^21 g=1/64 E=1/2 Imm=0.968246; grid s=0 v=1/32 K=4 Delta=1/128 k=3; N^e1=4.0 (=Gamma=4)
check Phi2 = k*Gam*Phi^2 = 12.0 ; dDriftNonAltN-level (Gam^2 Phi((k-1)+k Gam Phi)) = 224.0 = Gam^2((k-2)P1+P2+P3) = 224.0
C= 0.5 eps0=C+12=12.5: log10(LHS/RHS) ha1 -77.0 ha2' -74.5 ha3 -69.6 he1 -67.3 he2 -42.9 he3 -65.6 he4 -27.7 all<=1:True | log10(assembledRHSLinN/budget)=-36.6
C= 1.0 eps0=C+12=13.0: log10(LHS/RHS) ha1 -79.6 ha2' -77.0 ha3 -72.1 he1 -69.7 he2 -45.5 he3 -68.8 he4 -30.8 all<=1:True | log10(assembledRHSLinN/budget)=-39.7
C= 5.0 eps0=C+12=17.0: log10(LHS/RHS) ha1 -100.1 ha2' -97.5 ha3 -92.6 he1 -88.9 he2 -66.0 he3 -94.0 he4 -56.1 all<=1:True | log10(assembledRHSLinN/budget)=-65.0
C=20.0 eps0=C+12=32.0: log10(LHS/RHS) ha1 -176.8 ha2' -174.3 ha3 -169.4 he1 -161.2 he2 -142.7 he3 -188.9 he4 -150.9 all<=1:True | log10(assembledRHSLinN/budget)=-159.8
hypotheses of budgetNonAltLinN (C-independent ones): {'2<=k': True, '|E|<2': True, '0<=s<=v<1': True, 'K!=0': True, 'eta_v^-1<=N': True, 'Delta/eta_v<=1': True, '1<=Lam,0<=Phi1,Phi2,Phi3': True, 'Gam=N^e1': True, 'X0<=N^e1 B_s^k': True, 'hlog': True, 'hR': True} ALL: True
```
(The witness has `ε₀ = C+12` as in the merged `budgetNonAltN_instance`; at the limit regime `ε₀ = 1/10` the `ha2'` slack is row 10: `ha2'` is a hypothesis of the theorem and holds `∀ᶠ n` in S3-12b.)

`nqLinGood_holds` data (same grid, `ε = 1/10`, `XL ≡ XLK ≡ 1`, `K+1 = 5 ≤ N^1`), `k ∈ {2, 4}`, `Γ = N^ε = 4.2871`, `B_v = 3.1986e-05`:
```
  k=2: Phi1=0, Phi2=0.17817 (sum over n'=[] of XLK(k+2-n')*(XL XL)^1/2 = 0, + B_v^1/6), Phi3=1.0, STn12E=(1, 3); levels Gam(Gam*Phi_i) = 0.000, 3.275, 18.379; (D1')-(D3') chain at all u_j<=v: True
  k=4: Phi1=2.0, Phi2=1.17817 (sum over n'=[3] of XLK(k+2-n')*(XL XL)^1/2 = 1.0, + B_v^1/6), Phi3=1.0, STn12E=(3, 5); levels Gam(Gam*Phi_i) = 36.758, 21.654, 18.379; (D1')-(D3') chain at all u_j<=v: True
```
`k = 2`: `Icc 3 2 = ∅` (no `l`; (D1') vacuous) and `Icc((k+1)/2+1)(k-1) = ∅`, so `Φ₂ = B_v^{1/6}XLK 2`; `k = 3`: `Icc 3 2 = ∅`, `Φ₂ = B_v^{1/6}XLK 3` (the `n ∈ {2,3}` case `3_5:1064-1069`); `k = 4`: `Icc 3 3 = {3}`: `XLK(3)·(XL(1)XL(3))^{1/2}`, since `STn12 3 = (1,3)` (odd: `(n'-2, n')`). **Correction to the ticket's (iii): the `XL` lengths at `k = 4` are `1` and `3`, not `2`** (no effect on any exponent; both `≤ k+1`). Level script (`python3 levels.py`):
```
4 | [3, 2] | [3] | [(3, (1, 3), 3)] | (3, 5) | True | True | D1 lengths in Icc 2 (k-1): True
max |dDriftNonAltN - dDriftLinN(Phi,k*Gam*Phi^2,Phi)| over 2000 exact rational samples: 0
violations of (k-2)P1+P2+P3 <= k(P1+P2+P3): 0
coefficient of P0*X: 3/4 ; + Lambda-term 1/12 = 5/6 (<=1 needed on Lr*X since X<=Lr*X); coeff of each Phi_i*X: 1/12 (<=1)
```
Target 1(b)/(c) at the same data (`z0 = 1/2 + iN^{-4/5}`, window `[0,1/16]`, `n_=3, p=1`, `XL ≡ XLK ≡ 1`), `python3 impl.py`:
```
msc(z0) = (-0.2499988685888675255394752607818969348444 + 0.9682414546259569658142225360418338660917j)  Im>0: True  lemT(z0)=|msc|^2 = 0.9999909487519029357550291390587156210451 < 1: True  t=1/16 <= lemT: True
u=0.0625: B_u=3.305e-05 >0, B^{1/6}=0.1791 >=0, STbootRHS 2 = 17.1886 >= 0
tau=1/10,D=3: old pin used at (tau/2, D+1); new hypothesis at m=n_ used at (tau/2, D+1); bad prob <= 2N^{-(D+1)} = 1.0339757656912846e-25 <= N^{-D} = 1.0842021724855044e-19 : True
```
External hypotheses: none new. `STOeqNQ` (owed pin, S3-12c) and `STKbound, STKward, STLK, STStep2Concl, STLmaxU, STLKU` (other gates' pins) stay hypotheses of the examples exactly as in the merged `gridGood_instance`; their deterministic content at the data is checked above (`lemT(z0) < 1`, `1/16 ≤ lemT`, `K+1 ≤ N`).
Measurability (iv): the three clauses of `GoodLinN` are `∀`-conjunctions over `l`, `σ`, `a` of `‖f(H)‖ ≤ c` with `f ∈ {STksimLKM, STelklkM, STegtM}`, whose measurability helpers exist as private in `GridGoodN.lean` (`gridGood_meas_STksimLKM :307`, `_STelklkM :324`, `_STegtM :338`; `gridGood_measurableSet_forall :239`, `_imp :247`) and are used by `measurableGoodSetN :361-397` for the same three clauses.

### Verdicts
- Target 1 (`STNQConcl'`, `STOeqNQ'`, `stNQConcl'_of_stNQConcl`, `stOeqNQ'_of_stOeqNQ`, `inst_OeqNQ'`): PASS (rows 1-3).
- Target 2 (`GoodLinN`, `measurableGoodLinN`, `goodSetN_subset_goodLinN`): PASS (rows 4, 6, 7; measurability).
- Target 3 (`NQLinGood`, `nqLinGood_holds`): PASS (rows 4-5, 12).
- Target 4 (`dDriftLinN`, `nqLinExitTauN`, `subGaussStop_linN`, `nqLin_hdriftN`, `driftTensorN_norm_le_of_goodLin`): PASS (rows 7-8).
- Target 5 (`assembledRHSLinN`, `tbDriftLinN`, `budgetNonAltLinN`): PASS (rows 8-11; the 24-hypothesis list of the pin is as `budgetNonAltN` with `ha2'`).

## (b) Script output — Mon Oct  5 16:01:10 UTC 2026

### Build, hygiene, registry pre-check (commit 5a9f3c2b55159615ac199bc6395414554d576243, `Jun Yin`; scripts and outputs: `final_checks.sh`, `fresh_build.*`)
```
$ [isolated clone of the worktree at 5a9f3c2, build artifacts of the two modules removed] lake build RBM3D.Induction.Step34PinsP RBM3D.Induction.NQLin   (Mon Oct  5 15:59:37 UTC 2026 .. Mon Oct  5 15:59:57 UTC 2026, exit 0)
ℹ [3841/3842] Built RBM3D.Induction.Step34PinsP (5.4s)
ℹ [3842/3842] Built RBM3D.Induction.NQLin (17s)
Build completed successfully (3842 jobs).
$ cd RBM3D-wt/T2186 && lake build RBM3D.Induction.Step34PinsP RBM3D.Induction.NQLin   (Mon Oct  5 15:59:57 UTC 2026, exit 0):  Build completed successfully (3842 jobs).
$ lake build   (whole library; the root RBM3D.lean does not import the two modules yet, the hub adds the imports at merge; Mon Oct  5 15:59:59 UTC 2026, exit 0):  Build completed successfully (3995 jobs).
$ lake env lean assert.lean  [import RBM3D / import RBM3D.Induction.Step34PinsP / import RBM3D.Induction.NQLin / #assert_rbm_axioms]   (Mon Oct  5 16:00:01 UTC 2026, exit 0)
axiom audit: 5612 theorems, 2021 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 110 (borrowed 1, owed 86, structural 23).
usage line of the registered premise: RBM.Gauss.Sizes.STOeqNQ': 2 [no certificate]   (theorems whose type mentions STOeqNQ': stOeqNQ'_of_stOeqNQ, inst_OeqNQ')
in the list of registered premises that carry nothing yet: True
registry: 2 borrowed + 128 owed + 58 structural; 78 registered premise(s) carry nothing yet: [RBM.Loop.KLPT, ...
scan reports an unregistered premise: False
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Induction/NQLin.lean RBM3D/Induction/Step34PinsP.lean   ->  0, 0
$ git diff --stat main...t/T2186      (main is at 6f8b2e2, the branch base is 0818c49)
 RBM3D/Induction/NQLin.lean       | 1775 ++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/Step34PinsP.lean |  220 +++++
 RBM3D/Test/Axioms.lean           |    1 +
 3 files changed, 1996 insertions(+)
$ git diff main...t/T2186 -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.Gauss.Sizes.STOeqNQ', -- `lem:STOeq_NQ`, primed (DECISIONS §62): S3-12c
```

### `#print axioms` of the 34 public declarations of the two files (the files end with `#print axioms` lines)
```
$ grep "depends on axioms" (build output) | grep -E "NQLin.lean|Step34PinsP.lean" | sort | uniq -c
    34 [propext, Classical.choice, Quot.sound]
names: STNQConcl', STOeqNQ', stOeqNQ'_of_stOeqNQ, inst_OeqNQ', GoodLinN, nqLinPhi1, nqLinPhi2, nqLinPhi3, NQLinConcl, NQLinGood, measurableGoodLinN, goodSetN_subset_goodLinN, nqLinGood_holds, dDriftLinN, nqLinExitTauN, dDriftNonAltN_eq_lin, driftTensorN_norm_le_of_goodLin, nqLin_hdriftN, mem_of_lt_nqLinExitTauN, nqLinExitMeasN, subGaussStop_linN, assembledRHSLinN, tbDriftLinN, budgetNonAltLinN, nqLinExitTauN_eq_tau0, nqLinExitTauN_pos, zero_mem_goodLinN_inst, drift_lin_instance, dDriftLinN_inst_pos, hdrift_lin_instance, subGaussStop_lin_instance, nqLinGood_instance, nqLinGood_instance_nonempty, budgetNonAltLinN_instance
```

### Pinned definitions and statements against the check file (`cmpdefs.py`, `diffnq.py`, `stmts.py`)
```
$ python3 cmpdefs.py   (docstring + text of each check-file section 2-3 definition against the Lean file): 11 of 11 exactly identical: STNQConcl', STOeqNQ', GoodLinN, nqLinPhi1, nqLinPhi2, nqLinPhi3, NQLinConcl, NQLinGood, dDriftLinN, nqLinExitTauN, assembledRHSLinN
$ python3 diffnq.py   (merged `STNQConcl`, Step34Pins.lean:428, against `STNQConcl'`; names and docstrings excluded)
--- Step34Pins.lean:428 STNQConcl
+++ Step34PinsP.lean STNQConcl'
@@ -6 +6 @@
-    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
+    (∀ m, 1 ≤ m → m ≤ n_ →
@@ -12 +12 @@
-      (fun n q ω => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * STsupXiLK sz n (E n) (s n) (q.1 : ℝ) n_ ω +
+      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
STOeqNQ' is STOeqNQ with STNQConcl' : True
each edit changes the text: True True True | the three edits applied to STNQConcl give STNQConcl' exactly: True
$ python3 stmts.py   (the check-file section-4 `def T2186_*` text copied verbatim; `example : T2186_X := @X` for each public target) ->  section-4 statements in the check file: 11; lake env lean stmts.lean: exit 0; examples compiled: 10
private T2186_stNQConcl'_of_stNQConcl: 150:example : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.SizeTendsto → (∀ n, t n < 1) → ... := @stNQConcl'_of_stNQConcl   (compiled with the file)
```

### Statements of the targets (`ext.py stmt`, whitespace collapsed; `variable (sz : Sizes d)` of the section where not shown)
```
Step34PinsP.lean:156  theorem stOeqNQ'_of_stOeqNQ : ∀ d : ℕ, STOeqNQ d → STOeqNQ' d
Step34PinsP.lean:97  private theorem stNQConcl'_of_stNQConcl (sz : Sizes d) (E s t : ℕ → ℝ) (hsz : sz.SizeTendsto) (ht1 : ∀ n, t n < 1) (h : STNQConcl sz E s t) : STNQConcl' sz E s t
Step34PinsP.lean:184  theorem inst_OeqNQ' (h : STOeqNQ' 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIngConcl (fun sz E s t => STNQConcl' sz E s t) sz0 z0 sInst tInst Cd
NQLin.lean:196  theorem measurableGoodLinN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℝ) : MeasurableSet (GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃)
NQLin.lean:212  theorem goodSetN_subset_goodLinN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ) : sz.GoodSetN n E u k Γ Λ Φ τ' D' ⊆ GoodLinN sz n E u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ
NQLin.lean:591  theorem nqLinGood_holds (d : ℕ) : NQLinGood d
NQLin.lean:724  theorem dDriftNonAltN_eq_lin {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Φ : ℝ) : dDriftNonAltN sz n E u k Γ Φ = dDriftLinN sz n E u k Γ Φ ((k : ℝ) * Γ * Φ ^ 2) Φ
NQLin.lean:732  theorem driftTensorN_norm_le_of_goodLin {d : ℕ} (sz : Sizes d) {n : ℕ} {E u Γ Φ₁ Φ₂ Φ₃ : ℝ} {k : ℕ} (hk : 2 ≤ k) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ GoodLinN sz n E u k Γ Φ₁ Φ₂ Φ₃) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ‖driftTensorN sz n E u M σ a‖ ≤ dDriftLinN sz n E u k Γ Φ₁ Φ₂ Φ₃
NQLin.lean:761  theorem nqLin_hdriftN {d : ℕ} (sz : Sizes d) {n k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ) (hτG : ∀ ω j, j < τ ω → pathH sz s v K n j ω ∈ GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) : ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n), ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ b‖ ≤ dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
NQLin.lean:772  theorem mem_of_lt_nqLinExitTauN {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ} {Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ} {τ' D' : ℝ} {n : ℕ} {ω : PathΩ sz} {j : ℕ} (h : j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω) : pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' ∩ GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
NQLin.lean:781  theorem nqLinExitMeasN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ) : MeasurableSet[filt sz j] {ω | j < nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n ω}
NQLin.lean:792  theorem subGaussStop_linN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛg : 0 < Λg) (hκ' : 0 < κ') (sz : Sizes d) {E s v : ℕ → ℝ} {K : ℕ → ℕ} (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (n : ℕ) (hwL : v n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - v n) / (1 - s n)) (hκm : κ' ≤ (mE (E n)).im) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' D'' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hD'' : (k : ℝ) + 1 < D'') {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΓ : 0 ≤ Γ n) (hΛ : 0 ≤ Λ n) (m : ℕ) (hm : m ≤ K n) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m) (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) : SubGaussStopN sz (E n) σ (gridTime s v K n) (nqLinExitTauN sz E s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n) (fun j ω => ZvecN sz E s v K n j σ ω) m a j (cQVNonAltN sz E s v K n k Λg κ' ε Γ Λ D'' m a j)
NQLin.lean:876  theorem tbDriftLinN {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n k : ℕ) (Λg κ' ε : ℝ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' : ℝ) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hk : 2 ≤ k) (hΓ : 0 ≤ Γ n) (hΦ₁ : 0 ≤ Φ₁ n) (hΦ₂ : 0 ≤ Φ₂ n) (hΦ₃ : 0 ≤ Φ₃ n) (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) : gridStep s v K n * ∑ j ∈ Finset.range (K n), (kappaNonAltN d k Λg κ' (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) (j + 1) (K n) * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) + epsNonAltN d k Λg κ' ((sz.W n : ℕ) : ℝ) (j + 1) (K n) * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤ ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (Γ n * Γ n * (((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n)) * (sz.Bctl n (v n)) ^ k * ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) + ((K n : ℝ) * gridStep s v K n) * (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D'))
NQLin.lean:966  theorem budgetNonAltLinN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Λg κ' ε : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D' D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) (a : Fin k → Zd d (sz.L n)) (hk : 2 ≤ k) (hε₁ : 0 ≤ ε₁) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0) (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hΔη : gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1) (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n) (hΦ₁ : 0 ≤ Φ₁ n) (hΦ₂ : 0 ≤ Φ₂ n) (hΦ₃ : 0 ≤ Φ₃ n) (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) (gridStep s v K n) (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D_t)) (ha1 : ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) (ha2 : (k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (ha3 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ * Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (he1 : ((sz.size n : ℕ) : ℝ) ^ k * (((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (he2 : ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k * Real.sqrt ((k : ℝ) * (nqBudget_qvFar sz n k Λg κ' ε * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12) (he3 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) (he4 : ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) : assembledRHSLinN sz E s v K n k Λg κ' ε Γ Λ Φ₁ Φ₂ Φ₃ D' D'' D_Y τK εq X0 a ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k
```

### Compiled nonempty instances (every deterministic hypothesis discharged; other gates' pins stay hypotheses)
```
Step34PinsP.lean:184  theorem inst_OeqNQ' (h : STOeqNQ' 3) (Cd : ℝ) (hCd : 0 < Cd) : InstIngConcl (fun sz E s t => STNQConcl' sz E s t) sz0 z0 sInst tInst Cd
Step34PinsP.lean `example`s (the first is the pinned statement of the private implication): 150:example : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.SizeTendsto → (∀ n, t n < 1) →|196:example (h : STOeqNQ 3) : InstIngConcl (fun sz E s t => STNQConcl' sz E s t) sz0 z0 sInst tInst 1 :=|201:example (h : STOeqNQ 3) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))|209:example (h : STNQConcl sz0 (STflowE z0) sInst tInst) : STNQConcl' sz0 (STflowE z0) sInst tInst :=|
NQLin.lean:1314  theorem nqLinExitTauN_eq_tau0 : nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 = tau0
NQLin.lean:1331  theorem nqLinExitTauN_pos (ω : PathΩ sz0) : 0 < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω
NQLin.lean:1338  theorem zero_mem_goodLinN_inst : (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈ GoodLinN sz0 0 (1 / 2) 0 3 4 1 12 1
NQLin.lean:1361  theorem drift_lin_instance (a : Fin 3 → Zd 3 (sz0.L 0)) : ‖driftTensorN sz0 0 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 a‖ ≤ dDriftLinN sz0 0 (1 / 2) 0 3 4 1 12 1
NQLin.lean:1367  theorem dDriftLinN_inst_pos : 0 < dDriftLinN sz0 0 (1 / 2) 0 3 4 1 12 1
NQLin.lean:1376  theorem hdrift_lin_instance : ∀ ω j, j < Kg 0 → j < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω → ∀ b : Fin 3 → Zd 3 (sz0.L 0), ‖driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) (pathH sz0 sInst vg Kg 0 j ω) sig3 b‖  ...
NQLin.lean:1403  theorem subGaussStop_lin_instance (m : ℕ) (hm : m ≤ Kg 0) (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < m) : SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) (nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0) (fun j ω => ...
NQLin.lean:1428  theorem nqLinGood_instance (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1) (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : ST ...
NQLin.lean:1454  theorem nqLinGood_instance_nonempty (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1) (hL : STLmaxU sz0 (STflowE z0) sInst tInst) ( ...
NQLin.lean:1724  theorem budgetNonAltLinN_instance : assembledRHSLinN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 (fun _ => 12) Φ1 6 5 1 (1 / 21) 1 (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar ≤ ((sz0.size 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) + 12) * (Λ3 0 ^ ((1 : ℝ) / 2) + Φ1 0 + (fun _ : ℕ => (12 : ℝ)) 0 + Φ1 0) * (sz0.Bctl 0 (vg 0)) ^ 3 := budgetNonAltLinN sz0 Einst sInst vg Kg 0 3 10 (1 / 2) (4 / 5) Γ4 Λ3 Φ1 (fun _ => 12) Φ1 6 5 1 (-5) (1 / 21) 1 (nqGood1C 3 3 10 (1 / 2) + 12) (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) aFar (by norm_num) (by norm_num) (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg]) (by norm_num [Kg]) eta_inv_le_N (by rw [step0]; linarith [eta_inv_le_v]) (by rw [N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1]) (by norm_num) (by norm_num [Φ1]) NQBudgetInst.hlog_instance (by rw [N_eps1]) NQBudgetInst.hR_instance (ha1_inst _ nqGood1C_pos_instance) (ha2_inst _ nqGood1C_pos_instance) (ha3_inst _ nqGood1C_pos_instance) (he1_inst _ nqGood1C_pos_instance) (he2_inst nqGood1C_pos_instance) (he3_inst _ nqGood1C_pos_instance) (he4_inst _ nqGood1C_pos_instance)
NQLin.lean anonymous `example`s (goodSetN_subset_goodLinN, measurableGoodLinN, dDriftNonAltN_eq_lin, mem_of_lt_nqLinExitTauN, nqLinExitMeasN, the index sets and levels at k = 2, 4, nqLinGood_instance at k = 2, 4, tbDriftLinN) at lines: 1348 1352 1356 1387 1395 1468 1471 1477 1480 1483 1488 1698
```

### No `Φ²`, no crude level, no merged budget in `assembledRHSLinN`/`budgetNonAltLinN` (preflight (ii)); heartbeat option (`nophi2.py`)
```
assembledRHSLinN: 1053 chars
  mentions dDriftNonAltN: False | mentions budgetNonAltN/assembledRHSNonAltN: False
  occurrences of an unsubscripted level `Φ` (crude level): 0
  `Φ_i ^ 2` (square of a level): 0
  all `^ 2` occurrences: []
budgetNonAltLinN: 2227 chars
  mentions dDriftNonAltN: False | mentions budgetNonAltN/assembledRHSNonAltN: False
  occurrences of an unsubscripted level `Φ` (crude level): 0
  `Φ_i ^ 2` (square of a level): 0
  all `^ 2` occurrences: ['n : ℕ) : ℝ) ^ ε₁) ^ 2 *']
$ grep -c maxHeartbeats RBM3D/Induction/NQBudget.lean RBM3D/Induction/NQLin.lean  ->  RBM3D/Induction/NQBudget.lean:0 RBM3D/Induction/NQLin.lean:1 
```

### Name clash and port citations
```
$ grep -rnwF [38 names: new public names, instance names, `stP_bootRHS_nonneg`] RBM3D RBM3D.lean --include="*.lean" | wc -l   (names in names38.txt)
main worktree (HEAD 6f8b2e2): 0; prefix `nqLin_`: 0; branch worktree without the two new files: RBM3D/Test/Axioms.lean:114:   `RBM.Gauss.Sizes.STOeqNQ', -- `lem:STOeq_NQ`, primed (DECISIONS §62): S3-12c  (the registry line added by this ticket)
Port (the pin form only, no code): RBM2D `Induction/Defs.lean:236-262` (`PT`, `STOeqPT`) at c9a24cf, read with `git show`.
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h  ->  9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/Defs.lean  ->   RBM2D/Induction/Defs.lean | 259 +++++++++++-----------------------------------| 1 file changed, 62 insertions(+), 197 deletions(-)|
Copies of merged RBM3D declarations (private originals cannot be called; `grep -n` on the worktree): GridGoodN.lean:239 gridGood_measurableSet_forall -> nqLin_measurableSet_forall; GridGoodN.lean:307 gridGood_meas_STksimLKM -> nqLin_meas_STksimLKM; GridGoodN.lean:444 gridGood_whp_iInter -> nqLin_whp_iInter; GridGoodN.lean:655 gridGood_one_le_STXiL -> nqLin_one_le_STXiL; GridGoodN.lean:879 gridGood_grid -> nqLin_grid; GridGoodN.lean:990 gridGood_prec_XiL_one -> nqLin_prec_XiL_one; NQBudget.lean:327 nqBudget_absorb -> nqLin_absorb; NQBudget.lean:527 nqBudget_final -> nqLin_final; NQBudget.lean:391 tbDriftNonAltN -> tbDriftLinN; NQBudget.lean:555 budgetNonAltN -> budgetNonAltLinN; NQGood1.lean:104 driftTensorN_norm_le_of_goodSet -> driftTensorN_norm_le_of_goodLin; also the sibling helpers of the same blocks (see the narrative).
```

### Narrative (stage 1b)
- Delivered, commit 5a9f3c2 on `t/T2186` (the three files of the diffstat): `Induction/Step34PinsP.lean` (220 lines), `Induction/NQLin.lean` (1775 lines), one line in `Test/Axioms.lean` (`STOeqNQ'` after `STOeqNQ` in `owedProps`). Root imports are the hub's. Section (a) was not edited; no (a′) was needed (no verdict of (a) changed).
- Pins: 11 of 11 pinned definitions are exactly the check-file text; `STNQConcl'` is `STNQConcl` with the three edits of the ticket (edits 2 and 3 lie on one line, hence 2 hunks); the 10 public section-4 statements typecheck as `example : T2186_X := @X`; the pinned statement of the private `stNQConcl'_of_stNQConcl` is an `example` in `Step34PinsP.lean`. No pin, signature or hypothesis list was changed; merged files are untouched (diffstat).
- 1(b): `StochDomAt.of_subset_union` with the old conclusion and the new hypothesis at `m = n_` (both at `τ/2`), `Real.iSup_le` for `STsupXiLK`; `B ≥ 0`, `R = STbootRHS 2 … ≥ 0` use `t_n < 1` (private `stP_bootRHS_nonneg`). 1(c) takes `SizeTendsto` from `hflow.1` and `t_n < 1` from `lemT_lt_one`, as `gridGoodN_holds`.
- `nqLinGood_holds`: `nqLin_SE_restrict` (`[s,t] → [s,v]` by `StochDomAt.precomp_param`), `nqLin_whp_uniform` (hypotheses `hX`, `hY` and conjuncts 1-3 of `STSEforLnConcl` as `Prec.whp` events at `ε/3`, closed by `nqLin_clause`, `nqLin_D2_arith`, `nqLin_sqrt_bound`; (D2') uses `B_u^{1/6} ≤ B_v^{1/6}` (`STBctl_mono`, `v_n < 1`) and `(N^{ε/3})³ = N^ε ≤ Γ²`; no `B ≤ 1`, no `gridGood_D2_arith`), `nqLin_grid` (`map_pathH_eq`, `measurableGoodLinN`, `highProbAt_iInter`). The ticket prose names a `StochDomAt.mul`-type product for (D2'); `gridGood_whp_uniform` itself works with `Prec.whp` events and pointwise arithmetic, and so does the copy.
- Targets 4-5: `dDriftNonAltN_eq_lin` by `ring`; `driftTensorN_norm_le_of_goodLin` is the proof of `driftTensorN_norm_le_of_goodSet` with three levels; `subGaussStop_linN` is `azumaProxy_subG_ugen` with `G j = GoodSetN ∩ GoodLinN` and `hQ_nonAltN` on the first component; `tbDriftLinN` is `tbDriftNonAltN` with `a = Γ²((k-2)Φ₁+Φ₂+Φ₃)`; `budgetNonAltLinN` is the proof of `budgetNonAltN` with the drift term linear in the levels (`ha2` with `(N^{ε₁})²`) and `nqLin_final` (coefficients `5/6` of `Λ^{1/2}B_v^k`, `1/12` of each `Φ_iB_v^k`).
- `budgetNonAltLinN` carries `set_option maxHeartbeats 400000 in` (comment in the file): a first compile at the default 200000 stopped at the heartbeat limit (tool log); `NQBudget.lean` has no such option (grep above).
- Instances: Step34PinsP as listed (`stOeqNQ'_of_stOeqNQ` through `inst_OeqNQ'` at `sz0`, `z0`; the private implication applied at `sz0` with `STNQConcl` as hypothesis; the owed `STOeqNQ 3` and the premises `STKbound`, `STKward`, `STLK`, `STStep2Concl` of `STIngR` are hypotheses). NQLin: the exit time equals `tau0` and is positive at every sample; `0 ∈ GoodLinN`; the drift bound at `H_0 = 0` with a positive level; `nqLin_hdriftN`, `mem_of_lt_nqLinExitTauN`, `nqLinExitMeasN`, `subGaussStop_linN` at the data of `NQGood2Inst`; `nqLinGood_holds 3` through `inst_ing` at `v ≡ 1/32`, `K ≡ 4`, `XL ≡ XLK ≡ 1`, `ε = 1/10`, every `k ≥ 2` (examples `k = 2, 4`), with `hX`, `hY` discharged from `STLmaxU`, `STLKU` (restricted from `[0,1/16]` to `[0,1/32]`); `budgetNonAltLinN` with all 24 hypotheses discharged for every `C > 0` (`hlog`, `hR` from `NQBudgetInst`, `ha1`-`he4` re-derived, `ha2` with `(N^{ε₁})² = 16`).
- Registry: `STOeqNQ'` is in `owedProps`; the pre-check reports no unregistered premise and lists `STOeqNQ'` among the registered premises that carry nothing yet (`stOeqNQ'_of_stOeqNQ` concludes it), as the ticket expects; `STNQConcl` and `STSEforLnConcl` occur in this ticket's theorems only in private ones. Private helpers are `nqLin_*`/`stP_*`; the copies table above lists the originals.
- Not done / not claimed: no consumer (S3-12b, S3-12c, S3-18b, S3-24b, S3-26) was touched; the owed pins `STOeqNQ`, `STKbound`, `STKward`, `STLK`, `STStep2Concl`, `STLmaxU`, `STLKU` remain hypotheses.

## (c) Verified Mathlib and project names (`#check`, `names2.lean`; all used by the compiled files; first line of each)
```
@Real.iSup_le : ∀ {ι : Sort u_1} {f : ι → ℝ} {a : ℝ}, (∀ (i : ι), f i ≤ a) → 0 ≤ a → ⨆ i, f i ≤ a
@Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_add' : ∀ {x y z : ℝ}, 0 ≤ x → y + z ≠ 0 → x ^ (y + z) = x ^ y * x ^ z
@Real.mul_rpow : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → (x * y) ^ z = x ^ z * y ^ z
@Real.sqrt_mul_self : ∀ {x : ℝ}, 0 ≤ x → √(x * x) = x
@Finset.single_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N}
@Finset.sum_nonneg : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N}
@le_mul_of_one_le_left : ∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Zero α] {a b : α} [inst_2 : Preorder α]
@Measure.map_apply : ∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
@RBM.StochDomAt.of_subset_union : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type u_2}
@RBM.StochDomAt.precomp_param : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type u_2}
@RBM.Gauss.HighProbAt.inter : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ},
verified absent: none searched (every name used exists)
```

## (d) Open issues and paper-delta candidates
- `T2186a` (`lem:STOeq_NQ`, `3_5:1136`, `(am;asoiuw)` `3_5:1143-1148`): the random self-term `B_u^{1/6} sup_{w∈[s,u]} Ξ̂^{𝓛-𝒦}_{w,n_}` is replaced by the deterministic `B_u^{1/6} XLK n_ n u` under the hypothesis `Ξ̂^{𝓛-𝒦}_m ≺ XLK m` for `m ≤ n_` (as RBM2D `STOeqPT`); the merged pin implies the primed one (`stOeqNQ'_of_stOeqNQ`); self-absorption moves to S3-18b (ticket, DECISIONS §60, §62).
- `T2186b`: the clauses (D1)-(D3) of the paper's good set (`lem:SEforLn`) sit at separate deterministic levels `Φ₁, Φ₂, Φ₃` in `GoodLinN`, with `Φ₂` linear (`Γ(ΓΦ₂)B^k/η`, in place of `Γ k (ΓΦ)²`); `GoodSetN` is used only at a crude level.
- `T2186c`: every `≺` of `lem:SEforLn` and of the hypotheses `XL`, `XLK` is used at the exponent `ε/3`; the loss `Γ = N^ε` appears as `Γ(ΓΦ_i)` (slack in the exponent: `4ε/3` in (D1'), (D3'), `ε` in (D2'); preflight (a) row 5).
- `T2186d`: `NQLinConcl` takes the controls on the grid window `[s_n,v_n]` (not `[s_n,t_n]`); `lem:SEforLn` is restricted from `[s,t]` to `[s,v]`, and `Φ₂` carries `B_v^{1/6}` (not `B_u^{1/6}`) by monotonicity of `B_{u,0}`.
- `T2186e`: `ha2` of `budgetNonAltLinN` has `(N^{ε₁})²` where `budgetNonAltN` has `(N^{ε₁})³`, and the conclusion is degree 1 in the controls, `N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` (instead of `Φ + Φ²`).
- Open for S3-12b/c (not defects here): `ha2` (new) and `ha3` hold only for large `n` at fixed `ε₀` (polylog factor `Ls`; preflight (a) rows 10-11, T2179 report (a′): `ha2` crossover at `log₁₀ N ≥ 48.6 / 51.5 / 56.2` for `k = 2 / 3 / 6`); `he1`, `he2` need `W ≥ N^𝔠` and `D', D''` chosen after `C`; the removal of the owed line `STOeqNQ'` is S3-12c's (it proves `STOeqNQ'`); the `maxHeartbeats` option above is the only non-default heartbeat setting.
