Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 20:21:39 UTC 2026

Notation: g = ilambda, x = 1-u, B_{u,0} = (g²+x)⁻¹ + (L^d x)⁻¹ (`Defs/Params.lean:35-36`), T_u = B²(A^{-1/5}+B) with B = W^{-d}B_{u,0}, A = g²W^d (`STExpTarget`, `Step6Pins.lean:65`); d = 3, κ=ε=𝔡=1/10, 𝔠=1/6. T2211 moves compiled text (no new mathematics); regime data are those of T2204 (`docs/reports/T2204-prove.md` (a) (ii)), re-checked by script below. Scratch: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2211/{blocks,final,inst}.py`.

### (i) Exponent table and declaration table

| quantity | value | constraint (source) | slack |
|---|---|---|---|
| d | 3 | `3 ≤ d` in every pin; `st6_hi_of_reg5I` needs `2 ≤ d` (probe `:796`) | 1 |
| κ, ε, 𝔡 | 1/10 | `> 0` | - |
| 𝔠_d | min of the pin constants, ≤ 1/100 | skeleton III `min c₁ c₂` (probe `:1247-1248`), IV `min c₁ c₂` (`:1296-1297`), II `min c₁ (min c₂ c₃)` (`:1376-1377`), I `min c₁ … c₅` (`:1461-1463`); `st5_conStInd_mono` (`Step5Kit.lean:100`): smaller `𝔠_d` is the stronger hypothesis, so the minimum serves every pin | d·𝔠_d ≤ 3/100 |
| 𝔠 | 1/6 | `W ≥ N^𝔠`: sz0 n=0 N^{1/6}=11.314 ≤ W=32 | factor 2.83 |
| WO | 𝔡 = 1/10 | `W^{-d/2+𝔡} ≤ g ≤ 1/𝔡` (`st6_lam_pos`, `:182`) | sz0: W^{-1.4}/g = 1/(2(n+1)) ≤ 1/2; szB 0.144 ≤ 1 ≤ 10; szG 0.144 ≤ 5 ≤ 10 |
| target exps | 2, 1/5 | `(Eq:Gtlp_exp_flow)` `1_2:1392`; `0^{-1/5}=0` in Mathlib so `lam = 0` is the defect `st6_target_lam_zero` (`:193`) | sz0 n=0: A=8, T_{1/16} = 7.2e-10 > 0 |
| drift exps | 11/5, 5/2 | `6:58-62` (`eq:Exp(L-K)1`), `6:84-88` (`eq:ExpLWn=2`) | 11/5-2 = 1/5; 5/2-11/5 = 3/10 |
| windows | (i) g²/L² ≤ 1-t ≤ 1-s ≤ g²; (ii) g²/L^d ≤ 1-t ≤ 1-s ≤ g²/L²; (iii) 1-t ≥ g²; (iv) 1-s ≤ g²/L^d | `STReg5I..IV` (`Step5Pins.lean:44-65`); `STDriftHi`: g²/L^d ≤ 1-t (`Step6Pins.lean:286`) holds in (i)-(iii) (`st6_hi_of_reg5I/II/III`), false in (iv) | table in (ii) |
| (iii) init comparison | `(1-s)B_s ≤ 2(1-u)B_u`, ratio² T_s ≤ 4T_u | `st6_xB_III`, `st6_cmp_ini` (`:913`, `:980`); (iv) via `st6_xB_IV` (`:933`) | boundary data in (ii): 1.0154 ≤ 1.0313; 0.0310 ≤ 0.0511 |
| (ii) init | `1-s ≤ g²/L²` for `(sum_res_Ndecay_nonzero)` | `st6_ini_nonzero` (`:1156`) | equality (boundary) at szB 15/16 |

Declaration table (script `final.py`: names@probe line, kept blocks of the ticket; 81 = 48 kit lemmas (2 `private`: `st6_trace_six`, `st6_loop_rot`) + 33 theorems of blocks 7-13). What each says / consumer:
- §2: `st6_lam_pos` `0<lam` eventually from WO; `st6_G_pos` `(g²W^d)^{-1/5}>0`; `st6_target_lam_zero` the `lam=0` defect; `st6_prec_det_iff`, `st6_precU_of_forall_seq` the `Prec` calculus (g): per-time sequences ⇒ uniform in u (consumers: `st6_expAvgU_of_pin`, `st6_EGtHi_of_LW`, `inst_precU`); five bridges `*_at`: uniform statement restricted to a section `u` (`precomp_param`), consumers: regime assembly (§68 (7)) and `st6_expAvgU_of_pin`/`st6_EGtHi_of_LW`; `STLocalEntry_of_STLocalEntryU`: endpoint u=t (`STMainInd` conclusion).
- §5: `st6_prec_pi_norm`, `st6_prec_of_forall_fin` (Prec on products/finite families); `st6_flowE_lt_two` |lemE|<2 on the flow; `st6_hi_of_reg5I/II/III` regime ⇒ `STDriftHi` (skeletons); `st6_trace_six`, `st6_loop_rot`, `st6_EGt_eq_LWE`, `st6_expEGt_eq` rotation bridge `STEGt = LWE` (consumer `st6_EGtHi_of_LW`); `st6_duhEq_of_pin` Duhamel identity along `[s,t]` from `STExpDuhamelZ` (skeletons I-IV; S6-05).
- §6: `st6_Bctl_eq`, `st6_xB_eq`, `st6_xB_III/IV`, `st6_ratio_sq`, `st6_cmp_ini` initial-term comparisons (skeletons III, IV); `st6_target_nonneg/mono`, `st6_cube_le_target` target positivity/monotonicity (skeletons, II).
- §7: `st6_flowE_le`, `st6_mE_im_ge` flow bounds; `st6_expAvgU_of_pin` (res_ELK_n=1) from `STImproveExpAver` (skeletons I, II, IV); `st6_EGtHi_of_LW` (eq:ExpLWn=2) from `LWtermEXP` (I, II, III); `st6_ini_sumNdecay` (III), `st6_ini_nonzero` (II, I) initial terms; `st6_cover_exp2U`, `st6_Idiff_same` sign-class gluing (II); `st6_F1_window_vs_reg5II` STCaseI ∧ STReg5II ⇒ t ≤ s (D485); `st6_duhEqQ_of_pin`, `st6_mollifier_family` (I); the four skeletons.
- §7b: `st6_GdecayW_of_zero` (`STGdecayW … 0` ⇒ lossy `C_d`, D486; instance only); `ST_step6R_mono` (monotone in the regime; instance only).
- instances (33): see (ii).
```
$ python3 final.py        # extracts the 13 blocks from `git show 96c6b4c:RBM3D/Probe/T2191Pins.lean` (comments stripped for the dependency check)
blocks (probe 96c6b4c) line counts: [167, 155, 149, 511, 32, 6, 21, 22, 9, 36, 17, 27, 56] total 1208
decls: kept 81 moved(S6-01) 80 not ported 33 sum 194 = all in probe 194
kept kinds: {'theorem': 81} | private: ['st6_trace_six', 'st6_loop_rot']
kept ∩ moved: [] | kept ∩ not-ported: []
refs to the 33 not-ported names in kept blocks (comments stripped): []
declaration-clash of 81 names at cda3bb2 ( cda3bb2 ): (0, [])
declaration-clash of 81 names at main ( a42cad0 ): (0, [])
Step6Kit.lean on main exists: False
§2 167-333 : st6_lam_pos@182 st6_G_pos@187 st6_target_lam_zero@193 st6_prec_det_iff@202 st6_precU_of_forall_seq@236 STLK_of_STLKU_at@291 STLmax_of_STLmaxU_at@297 STLocalEntry_of_STLocalEntryU_at@303 LWAvgLaw_of_STAvgU_at@310 STDecay_of_STGdecayW_at@320 STLocalEntry_of_STLocalEntryU@329
§5 719-873 : st6_prec_pi_norm@730 st6_prec_of_forall_fin@746 st6_flowE_lt_two@787 st6_hi_of_reg5I@796 st6_hi_of_reg5II@800 st6_hi_of_reg5III@803 st6_trace_six@815 st6_loop_rot@821 st6_EGt_eq_LWE@832 st6_expEGt_eq@858 st6_duhEq_of_pin@866
§6 875-1023 : st6_Bctl_eq@888 st6_xB_eq@903 st6_xB_III@913 st6_xB_IV@933 st6_ratio_sq@963 st6_cmp_ini@980 st6_target_nonneg@998 st6_target_mono@1006 st6_cube_le_target@1016
§7 1025-1535 : st6_flowE_le@1040 st6_mE_im_ge@1049 st6_expAvgU_of_pin@1062 st6_EGtHi_of_LW@1076 st6_ini_sumNdecay@1105 st6_ini_nonzero@1156 st6_cover_exp2U@1201 st6_Idiff_same@1223 st6_F1_window_vs_reg5II@1233 ST_step6_caseIII_of_pins@1242 ST_step6_caseIV_of_pins@1291 st6_duhEqQ_of_pin@1338 st6_mollifier_family@1350 ST_step6_caseII_of_pins@1370 ST_step6_caseI_of_pins@1452
§7b 1594-1625,1728-1733 : st6_GdecayW_of_zero@1596 ST_step6R_mono@1729
inst 1838-2346 : inst_hiI@1845 inst_hiII@1846 inst_hiIII@1847 inst_expLKLK_I@1850 inst_expLKLK_II@1853 inst_expLKLK_III@1856 inst_skeleton6I@1910 inst_skeleton6II@1916 inst_skeleton6III@1921 inst_skeleton6IV@1926 inst_precU@2131 inst_GdecayW_of_zero@2160 inst_F1@2164 inst_step6R_mono@2169 inst_bridges@2174 inst_endpoints@2192 inst_expAvgU@2209 inst_EGtHi@2216 inst_duhEq@2223 inst_G_pos_sz0@2231 inst_G_pos_szB@2236 inst_G_pos_szG@2239 st6_target_pos@2243 inst_target_pos_sz0@2250 inst_target_pos_szB@2253 inst_target_pos_szG@2256 inst_lam_pos@2292 inst_target_lam_zero@2295 inst_cmp_III@2301 inst_cmp_IV@2311 inst_ini_sumNdecay@2323 inst_ini_nonzero@2332 inst_mollifier_family@2343
```

Skeletons vs paper and the T2204 regime table (arguments read from probe `:1242-1243, :1291-1292, :1370-1371, :1452-1454`; the T2204 assignment `6:94-97`; `STIngR6` premises at `Step6Pins.lean:324, 362, 377`):
- III `ST_step6_caseIII_of_pins` (hLK `STExpLKLKHi`, hLW `LWtermEXP`, hDu `STExpDuhamelZ`, hInt `STExpIntIII`) ⊢ `STStep6III` (`STReg5III`): exactly the ticket's list for (iii); initial term `st6_ini_sumNdecay` + `st6_xB_III`, `st6_cmp_ini` (constant 4, no 𝔠_d loss).
- IV `ST_step6_caseIV_of_pins` (hAvg `STImproveExpAver`, hDu, hLo `STExpDriftLo`, hInt `STExpIntIV`) ⊢ `STStep6IV` (`STReg5IV`): exactly the ticket's list for (iv); no `LWtermEXP` (`(eq:ExpLWn=2_smalleta)` is inside `STExpDriftLo`, `6:73-79`); `STImproveExpAver` feeds the premise `STExpAvgU` of `STExpDriftLo` (`Step6Pins.lean:324`).
- II `ST_step6_caseII_of_pins` (hLK, hLW, hAvg, hDu, hInt `STExpIntII`, hWd `STExpWardII`) ⊢ `STStep6II` (`STReg5II`): the ticket's (iii)-list with `STExpIntIII` replaced by `STExpIntII`, plus `STExpWardII`, plus `STImproveExpAver`; the ticket's wording omits `STImproveExpAver`, which is needed because `STExpWardII` has the premise `STExpAvgU` (`Step6Pins.lean:377`, paper `6:141` uses `(res_ELK_n=1)` in regime (ii)). Not at odds with the T2204 table; no `T2211a`.
- I `ST_step6_caseI_of_pins` (hLK, hLW, hAvg, hDu, hDuQ `STExpDuhamelQ`, hDec `STExpDriftDecay`, hWd `STExpWardI`, hIni `STExpIniI`, hInt `STExpIntI`) ⊢ `STStep6I` (`STReg5I`): the ticket's list for (i) plus `STImproveExpAver` (premise `STExpAvgU` of `STExpWardI`, `Step6Pins.lean:362`; paper `6:104,120,131`). The constant is the minimum of the five pin constants (table above).

§29 / §45 O2 (5)-(7), one line each:
- bridges: `*_at` are sections of uniform statements (`StochDomAt.precomp_param`, the union lives inside `Prec`); `STDecayStrong` has no bridge (index set `ilambda² ≤ 1-t`, probe `:283`).
- `0 < lam n` eventually from `WO` (`st6_lam_pos`); `lam = 0` is the defect `st6_target_lam_zero`.
- windows: `STDriftHi` holds in (i)-(iii) and fails in (iv) (table below), (iv) is covered by `STExpDriftLo`; `st6_F1_window_vs_reg5II`: `STCaseI` (`1-t ≥ g²/L²`, `Step34Pins.lean:237`) is empty in regime (ii) (`1-s ≤ g²/L²`, `s<t`).
- instance data are in their regimes (rows of (ii)); table reused from T2204 and re-checked.

Consumer check (§45 O2): the regime assembly consumes `STStep6I..IV` (merged statements, `Step6Pins.lean:131-140`), the five bridges and `STLocalEntry_of_STLocalEntryU` with the statements of the check file section 2; the dropped declarations (33, the `not ported` count above) have no consumer under §68 (7); `ST_mainInd_of_steps` is a pattern for `ST_mainIndR_of_steps R`, not a dependency (the dependency script finds no reference to any of the 33).

### (ii) One concrete nondegenerate instance (d = 3, κ=ε=𝔡=1/10, 𝔠=1/6, 𝔠_d ≤ 1/100)

Data (`Step34Pins.lean:710`, `Step5Pins.lean:497`, `Sizes.lean:260`, `Defs.lean:439-440`): szB (L=4, W=n+4, g=1) with zB; szG = szB with g=5; sz0 (L=4(n+1), W=(2(n+1))^5, g=(2(n+1))^{-6}) with z0, `sInst=0`, `tInst=1/16`. Windows: (i) szB (7/8, 15/16); (ii) szB (15/16, 31/32); (iii) sz0 (0, 1/16); (iv) szG (5/8, 3/4). Sections: `u ≡ 1/32`; `inst_precU` on [0, 1/2]; `inst_ini_nonzero` at `A = {1,2}`, `σ₁ ≠ σ₂`.
```
$ python3 inst.py
(i)  szB n=0 g2= 1 g2/L2= 1/16 g2/L3= 1/64 1-t= 1/16 1-s= 1/8 regimes: ['i'] DriftHi g2/L3<=1-t: True s<t: True
(ii) szB n=0 g2= 1 g2/L2= 1/16 g2/L3= 1/64 1-t= 1/32 1-s= 1/16 regimes: ['ii'] DriftHi g2/L3<=1-t: True s<t: True
(iii) sz0 n=0 g2= 1/4096 g2/L2= 1/65536 g2/L3= 1/262144 1-t= 15/16 1-s= 1 regimes: ['iii'] DriftHi g2/L3<=1-t: True s<t: True
(iv) szG n=0 g2= 25 g2/L2= 25/16 g2/L3= 25/64 1-t= 1/4 1-s= 3/8 regimes: ['iv'] DriftHi g2/L3<=1-t: False s<t: True
WO szB W^-1.4=0.14359 g=1.00000 1/dd=10: True
WO szG W^-1.4=0.14359 g=5.00000 1/dd=10: True
WO sz0 W^-1.4=0.00781 g=0.01562 1/dd=10: True
sz0 WO exact all n: W^-1.4/g = [0.5, 0.25, 0.05] <=1
sz0 n=0: L,W,N,lam = 4 32 2097152 1/64 ; N^(1/6)=11.314<=W=32 ; A=g2 W^3= 8
cmp_III: 1-u= 1/4096 = g2: True | (1-s)B_s=1.015381 <= 2(1-u)B_u=1.031250: True | ratio^2 T_s=1.0629e-02 <= 4 T_u=1.2034e-02: True | T_s,T_u>0: True True
cmp_IV: 1-s= 25/64 = g2/L3: True | (1-s)B_s=0.031010 <= 2(1-u)B_u=0.051052: True | ratio^2 T_s=8.6353e-07 <= 4 T_u=2.3441e-06: True
ini_nonzero: 1-s= 1/16 = g2/L2: True ; F1: 1-t= 1/32 < g2/L2= 1/16 (STCaseI fails: True )
T>0: sz0 n=0 u=1/16 7.2078e-10 ; szB n=0 u=15/16 1.5723e-04 ; szG n=0 u=3/4 5.8603e-07
bridges/endpoints: section u=1/32 in [0,1/16]: True  s<t endpoint: True ; precU: 1-u<=2(1-u) on [0,1/2]: True
(i) szB W^-d B_{t,0} n=0,10,1000: 1.86e-02 4.34e-04 1.18e-09 | A=g2W^d: 64 2.74e+03 1.01e+09
(ii) szB W^-d B_{t,0} n=0,10,1000: 2.30e-02 5.36e-04 1.45e-09 | A=g2W^d: 64 2.74e+03 1.01e+09
(iii) sz0 W^-d B_{t,0} n=0,10,1000: 3.31e-05 7.79e-21 3.21e-50 | A=g2W^d: 8 1.06e+04 8.02e+09
(iv) szG W^-d B_{t,0} n=0,10,1000: 1.60e-03 3.72e-05 1.01e-10 | A=g2W^d: 1.6e+03 6.86e+04 2.53e+10
d*c_d <= 3/100 <1; (1-t)/(1-s) at (i),(ii),(iii),(iv): [0.5, 0.5, 0.9375, 0.6666666666666666]
11/5-2= 1/5 5/2-11/5= 3/10
```
External hypotheses (pins, kept as hypotheses of the instances: `STExpLKLKHi`, `LWtermEXP`, `STImproveExpAver`, `STExpDuhamelZ/Q`, `STExpIntI..IV`, `STExpDriftLo`, `STExpDriftDecay`, `STExpWardI/II`, `STExpIniI`, `STStep6`, `STExp2`, `STStep2Core`, `STLmaxU`, `STLKU`, `STAvgU`, `STLocalEntryU`, `STGdecayW`): limit computations are the lines `W^-d B_{t,0}` (→ 0) and `A = g²W^d` (→ ∞) above for each datum; sz0 has A_n = (2(n+1))^3, szB (n+4)^3, szG 25(n+4)^3 (`Sizes.lean:260`, `Step34Pins.lean:710`), so `(g²W^d)^{-1/5} → 0` and `W^{-d}B_{t,0} → 0` with `(1-t)/(1-s)` fixed < 1 (last-but-one line). All deterministic hypotheses of the 33 instances are closed numbers at these data (`s<t` printed above; `t ≤ lemT z` is the T2204 report's computation lemT(zB)=0.983992 ≥ 31/32, lemT(z0,n=0)=0.999991 ≥ 1/16, not recomputed here).

## Verdicts
- Targets 1-3 (verbatim move of the 13 blocks; 81 theorems; imports; no registry line): **PASS**. Hypotheses of all four skeletons are the ingredient pins of their regime; every instance datum lies in its regime (only (iv) has `STDriftHi` false, as required); no 𝔠_d or exponent obstruction; dependency check `[]`; 0 name clashes on `main`.
- Findings for the dispatcher (no FAIL): (1) the ticket's ingredient list for regimes (ii), (i) omits `STImproveExpAver`, which the skeletons take (premise `STExpAvgU` of the Ward pins); (2) `main` is now a42cad0 (the ticket's check was at cda3bb2); the clash grep is 0 at both.

## (b) Script output — Mon Oct  5 20:26:57 UTC 2026 (stage 1b, branch t/T2211, commit 55fe9e5)

```
$ lake build RBM3D.Induction.Step6Kit   (tail; the warnings are long-line lints on my new module docstring, lines 24-35; none elsewhere)

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3846 jobs).
lake build RBM3D.Induction.Step6Kit  13.44s user 6.52s system 250% cpu 7.969 total
$ errors in build output: grep -c error build.out
0

$ lake env lean ax.lean   (#print axioms of the 79 public theorems of Step6Kit.lean; script-generated list from the file)
lines 'depends on axioms: [propext, Classical.choice, Quot.sound]': 79 of 79 printed; other lines:        0
forbidden tokens (sorry|admit|native_decide|axiom) in Step6Kit.lean: 0

$ python3 verb.py   # each probe block of Targets 1 (git show 96c6b4c:RBM3D/Probe/T2191Pins.lean | sed -n a,bp) in Step6Kit.lean: python `block in text`
167 333 167 True
719 873 155 True
875 1023 149 True
1025 1535 511 True
1594 1625 32 True
1728 1733 6 True
1838 1858 21 True
1908 1929 22 True
2129 2137 9 True
2159 2194 36 True
2208 2224 17 True
2231 2257 27 True
2291 2346 56 True

$ diff of non-blank lines: concatenated 13 blocks vs Step6Kit.lean: lines only in blocks (<): 0; lines only in file (>), by kind:
  copyright 4 + comment close; 12 import lines (Step6Pins + the probe's 11); module docstring (S6-02); set_option/noncomputable section/2 open (probe :39-44);
  7b section comment; namespace RBM.Gauss.Sizes + open + variable (probe :1550-1554); end RBM.Gauss.Sizes; 2 x end RBM.Gauss.Step6Inst; namespace RBM.Gauss.Step6Inst + open (probe :2077-2080); final end.
  (full list: 'diff' output above reduced to these categories; no other line)

$ check-file equality: scratch chk.lean = check-file imports + import RBM3D.Induction.Step6Kit + sections 1-2 (lines 1-360) + 25 `example : RBM.Gauss.Sizes.T2211Check.X := @RBM.Gauss.Sizes.X`
examples in chk.lean: 25
lake env lean chk.lean: exit 0, error lines: 0

$ registry pre-check: temporary file (import RBM3D; import RBM3D.Induction.Step6Kit; #assert_rbm_axioms), lake env lean   (exit 0)
axiom audit: 6258 theorems, 2166 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
  ... lines in output mentioning Step6Kit/st6_/ST_step6/inst_: 0; lines with unregistered/flag/error/warning: 0; RBM3D/Test/Axioms.lean untouched

$ lake build   (full library, worktree; Step6Kit is not in RBM3D.lean until the hub adds the root import)
Build completed successfully (4013 jobs).
exit 0

$ git diff --stat main...t/T2211
 RBM3D/Induction/Step6Kit.lean | 1288 +++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1288 insertions(+)

$ declaration-clash grep: 81 theorem names of Step6Kit.lean against `git grep` of main (a42cad0), RBM3D/ :  matches = 0
$ dependency check (comments stripped; the 33 not-ported names in the 13 blocks): [] (final.py, section (a))
$ ports: from the T2191 probe (RBM3D branch t/T2191 @96c6b4c), not from RBM1D/RBM2D; no RBM1D/RBM2D diff-stat applies.
```

Target statements (script: stmts.py extracts each declaration up to its first ':='; Step6Kit.lean line):
```lean
-- 737
theorem ST_step6_caseIII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hDu : STExpDuhamelZ d)
    (hInt : STExpIntIII d) : STStep6III d
-- 786
theorem ST_step6_caseIV_of_pins (hAvg : STImproveExpAver d) (hDu : STExpDuhamelZ d) (hLo : STExpDriftLo d)
    (hInt : STExpIntIV d) : STStep6IV d
-- 865
theorem ST_step6_caseII_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hInt : STExpIntII d) (hWd : STExpWardII d) : STStep6II d
-- 947
theorem ST_step6_caseI_of_pins (hLK : STExpLKLKHi d) (hLW : LWtermEXP d) (hAvg : STImproveExpAver d)
    (hDu : STExpDuhamelZ d) (hDuQ : STExpDuhamelQ d) (hDec : STExpDriftDecay d) (hWd : STExpWardI d)
    (hIni : STExpIniI d) (hInt : STExpIntI d) : STStep6I d
-- 170
theorem STLK_of_STLKU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLKU sz E s t) : STLK sz E u
-- 176
theorem STLmax_of_STLmaxU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLmaxU sz E s t) : STLmax sz E u
-- 182
theorem STLocalEntry_of_STLocalEntryU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STLocalEntryU sz E s t) : STLocalEntry sz E u
-- 189
theorem LWAvgLaw_of_STAvgU_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STAvgU sz E s t) : LWAvgLaw sz E u
-- 199
theorem STDecay_of_STGdecayW_at {E s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n)
    (h : STGdecayW sz E s t 0) : STDecay sz E u
-- 208
theorem STLocalEntry_of_STLocalEntryU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLocalEntryU sz E s t) :
    STLocalEntry sz E t
-- 361
theorem st6_duhEq_of_pin (hDu : STExpDuhamelZ d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ lemT (z n)) :
    STExpDuhEq sz (STflowE z) s t
-- 327
theorem st6_EGt_eq_LWE (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STEGt sz n E t σ a ω = LWE sz n E t σ a ω
-- 1046
theorem st6_GdecayW_of_zero (hsz : sz.SizeTendsto) {E s t : ℕ → ℝ} (ht1 : ∀ n, t n < 1) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (h : STGdecayW sz E s t 0) : STGdecayW sz E s t Cd
-- 1078
theorem ST_step6R_mono {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (hRR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) (h : STStep6R d R) : STStep6R d R'
```

Compiled nonempty instances (all 33 in Step6Kit.lean, namespace RBM.Gauss.Step6Inst; script grep of 'theorem inst_*' and st6_target_pos, name@line):
```
inst_hiI@1093 inst_hiII@1094 inst_hiIII@1095 inst_expLKLK_I@1098 inst_expLKLK_II@1101 inst_expLKLK_III@1104 inst_skeleton6I@1110 inst_skeleton6II@1116 inst_skeleton6III@1121 inst_skeleton6IV@1126 inst_precU@1140 inst_GdecayW_of_zero@1149 inst_F1@1153 inst_step6R_mono@1158 inst_bridges@1163 inst_endpoints@1181 inst_expAvgU@1186 inst_EGtHi@1193 inst_duhEq@1200 inst_G_pos_sz0@1203 inst_G_pos_szB@1208 inst_G_pos_szG@1211 st6_target_pos@1215 inst_target_pos_sz0@1222 inst_target_pos_szB@1225 inst_target_pos_szG@1228 inst_lam_pos@1232 inst_target_lam_zero@1235 inst_cmp_III@1241 inst_cmp_IV@1251 inst_ini_sumNdecay@1263 inst_ini_nonzero@1272 inst_mollifier_family@1283 
-- 1110
theorem inst_skeleton6I (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hDuQ : STExpDuhamelQ 3) (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hIni : STExpIniI 3)
    (hInt : STExpIntI 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
-- 1116
theorem inst_skeleton6II (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3)
    (hInt : STExpIntII 3) (hWd : STExpWardII 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)
-- 1121
theorem inst_skeleton6III (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hInt : STExpIntIII 3)
    :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) sz0 z0 sInst tInst
-- 1126
theorem inst_skeleton6IV (hAvg : STImproveExpAver 3) (hDu : STExpDuhamelZ 3) (hLo : STExpDriftLo 3)
    (hInt : STExpIntIV 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
-- 1163
theorem inst_bridges (hLE : STLocalEntryU sz0 (STflowE z0) sInst tInst) (hAvg : STAvgU sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hDec : STGdecayW sz0 (STflowE z0) sInst tInst 0) :
    STLocalEntry sz0 (STflowE z0) (fun _ => 1 / 32) ∧ LWAvgLaw sz0 (STflowE z0) (fun _ => 1 / 32) ∧
      STLmax sz0 (STflowE z0) (fun _ => 1 / 32) ∧ STLK sz0 (STflowE z0) (fun _ => 1 / 32) ∧
      STDecay sz0 (STflowE z0) (fun _ => 1 / 32)
-- 1181
theorem inst_endpoints (h : STExp2U sz0 (STflowE z0) sInst tInst) (hLE : STLocalEntryU sz0 (STflowE z0) sInst tInst) :
    STExp2 sz0 (STflowE z0) tInst ∧ STLocalEntry sz0 (STflowE z0) tInst
-- 1153
theorem inst_F1 : ¬ STCaseI szB (fun _ => 15 / 16) (fun _ => 31 / 32)
-- 1158
theorem inst_step6R_mono (h : STStep6 3) :
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
-- 1200
theorem inst_duhEq (hDu : STExpDuhamelZ 3) : STExpDuhEq sz0 (STflowE z0) sInst tInst
```
Data of every instance: d=3, regimes (i)-(iv) rows of the table in (a)(ii); deterministic hypotheses are discharged inside the instance proofs; open hypotheses are pins/stochastic premises (STExpLKLKHi, LWtermEXP, STImproveExpAver, STExpDuhamelZ/Q, STExpInt*, STExpDriftLo/Decay, STExpWard*, STExpIniI, STStep6, STExp2U, STLocalEntryU, STAvgU, STLmaxU, STLKU, STGdecayW, STStep2Core).

Narrative (stage 1b):
- `RBM3D/Induction/Step6Kit.lean` (1288 lines) was assembled by script (`assemble.py`) from the thirteen probe blocks of Targets 1 plus the lines the ticket allows; no block was edited. It compiled at the first build against `main`; no proof was written.
- 81 theorems (79 public, `st6_trace_six` and `st6_loop_rot` private), 0 definitions; 33 of them are the instances of blocks 7-13.
- Every endpoint theorem has a compiled instance in the same file (the 33 instances, namespace `RBM.Gauss.Step6Inst`, `d = 3`); the four skeletons are applied by `inst_skeleton6I..IV`, the bridges by `inst_bridges`/`inst_endpoints`; stochastic premises and the pins stay hypotheses.
- Registry: the pre-check printed no flag for any name of this file; `RBM3D/Test/Axioms.lean` untouched.
- `ST_mainInd_of_steps` and the intermediate-time gluing are not ported (ticket Decision (a), (b)); `STGenericPos` is not defined (Decision (d)).

## (c) Verified Mathlib names

No Mathlib name was written or changed by this ticket: the file is the verbatim probe text, whose every Mathlib reference resolves (`lake build RBM3D.Induction.Step6Kit` exit 0, 0 errors). No name was checked absent.

## (d) Open issues and paper-delta candidates

- Paper-delta candidates: none new (`T2211a` not used: the preflight found no skeleton at odds with the T2204 regime table). Cite D485-D489 (T2191a-e) as the ticket says.
- Preflight finding (a), reproduced: the ticket's ingredient lists for regimes (ii) and (i) omit `STImproveExpAver`, which `ST_step6_caseII_of_pins` and `ST_step6_caseI_of_pins` take (hypothesis `hAvg`, lines 865 and 947 of `Step6Kit.lean`); no change of text.
- The full `lake build` above does not contain `RBM3D.Induction.Step6Kit` (the root import in `RBM3D.lean` is the hub's step at merge); the registry pre-check imported `RBM3D` and `RBM3D.Induction.Step6Kit` together.
- Lint warnings: 8 long-line warnings in my new module docstring (lines 24-35, before the `set_option linter.style.longLine false` of probe `:39-44`); no statement affected.
- `STRegSeq` (`Step6Pins.lean:482`) has no consumer and no instance in this file (ticket Decision (d)); the regime-assembly ticket moves it to the "superseded, not needed" class.
