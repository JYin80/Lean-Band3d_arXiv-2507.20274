Prover model: claude-sonnet-5-5
## (a) Math preflight — Tue Oct 13 04:00:53 UTC 2026

Verdicts: targets 1-12 PASS (stop rules 2, 3, 4 not triggered: the one loop, F7 at mixed coupling and the K2 comparison close from `0 < κ`, `BAFlow` and the forward bound R1). Three decisions for the 1b: (D1) the pre-signed 1,950 split does **not** apply (central 1,408); (D2) note (3) case "prove here" applies (`baSTGijDecgL_holds`, 45 lines); (D3) the premise scan needs two new registry lines, `BALWterm`, `BALWtermExp`.

### (i) Exponent / constant table
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | R1 `A=(κ+1)/κ`, `g₀²=t₀g²` (`TwistStep2_lam0_sq`, `TwistStep2.lean:740`) | 3 (κ=1/2), 11 (κ=1/10) | `g₀²≤g²`, `g²≤A g₀²`, `t₀≥κ/(κ+1)` | 0 at `t₀=κ/(κ+1)`; instance `t₀=25/36`: `g²/g₀²=1.44≤3` |
| 2 | forward comparison `tailT_{g₀}≤A tailT_g`, `tailW_{g₀}≤A tailW_g`, `STprof(g₀)≤A STprof(g)` | proof: `(g₀²+w)⁻¹≤A(g²+w)⁻¹` (`g²≤Ag₀²`, `A≥1`), `ellT` monotone in `g≥0`, `max(Ax,y)≤A max(x,y)` | `0<g₀≤g` (`baStep2Fam_lam_pos_le`) | max 10.9999≤11, 3.0000≤3 over 54 cases each (below); reverse `tailW_g/tailW_{g₀}` up to 10^15: never stated (UBA-C1 respected) |
| 3 | F7 constant `K_c` (target 5) | `A·Q₀C_T+C_s ≤ A·K_c⁰`, `K_c⁰=Q₀C_T+C_s` (`baNewKLKGenHyp`, `NewKLKBA.lean:446-548`) | kernel tail `‖X_{ab}‖≤Q₀𝒯_{g₀}≤A Q₀𝒯_g` (`NewKLKBA_tail`, `Λ=𝔡⁻¹`), then `NewKLKBA_conv_P` and `HT` at `g=sz.lam` (the profile): no reverse bound | `(A-1)C_s≥0`; `K_c` depends on `(d,κ,𝔡)` only: uniform in `(sz,z)` (F1) |
| 4 | `lem:newKLK` constant (target 5) | `C=2K_c+2C_s(4+C_K)+C_sC_T`, `C_K=1`, `δ₀=κ/2`, `C_s=2^{d-2}e` (`NewKLKGen:416`) | `C,δ₀` before `sz` (class order) | explicit, positive |
| 5 | window of target 5 | `0<g₀≤g≤𝔡⁻¹`, `κ≤Im m_F≤1` (`EMn2BA_mF_data`) | `m_F=m/√t₀` | instance `Im m_F=1.00000`: 0.5 below, 0 above (Ward, binding) |
| 6 | size data (target 6) | `cB=(𝔡⁻²+1)⁻¹=0.0099`, `c=min(2𝔡𝔠,ε)/2=1/60` | `cBW^{-d}≤Bctl≤N^{-c}` | `Bctl(t₀)=8.6e-35≤N^{-c}=0.1965` |
| 7 | BA `1-u≥Im z/2` (`EMn2BA_one_sub_T0`) vs band `/4` | `(N(1-u))⁻¹≤2N^{-ε}` (band 4) | sum `3N^{-2c}≤N^{-c}` needs `3N^{-c}≤1` (band: 5) | `1-t₀=0.3056≥0.1833`; `3N^{-c}=0.5895`; band's `5N^{-c}=0.9825` (n₀=95) |
| 8 | P3 (target 7) | `c₀=min(2𝔠𝔡,ε/2)=1/30`, `RangeCond(ε/2)`, `M(D)=6⌈(2+D)/c₀⌉` | `N^{-1+ε/2}≤1-t` from `1-t₀≥N^{-1+ε}/2`, `N^{ε/2}≥2` (`baFlow_premises`, `NetLiftBA:65`) | `5.3e-41≤0.3056`; `N^{ε/2}=132≥2`; `Bctl≤2N^{-c₀}`: 8.6e-35≤0.0772 |
| 9 | skeleton constants (unchanged, `Step2IterGen2:299-371`) | `C_d=3C+1`, `𝔠_d=min(1/100,1/(60C_d),𝔠₀)` | `C_d𝔠_d≤1/60` | 0 (binding by design, T2478 row 1); no exponent re-derived here |
| 10 | F2 guard | `hOne sz z` is read once, `Step2IterGen2:371`, after `hκ` (:320) and `hflow` (:341) are in scope | `hOne : ∀ sz κ ε 𝔠 𝔡 z, 0<κ → Flow → OneLoop`; conj. 1 needs `0<κ`, `0<g₀` eventually (`BAflow_lam0_window`), `BAReal` (`BAflow_real`) | nothing beyond `0<κ`, `BAFlow` (stop rule 2 clear); conj. 2 = `ST_Lloop_one_false` argument at `seqHflowBA` (`EMn2BA_seqHflowBA_herm`) |
| 11 | target 9 data at `baStep2Data` | `hdat` from `STBdatagL` (reorder `∃cB,c`); `hGii,hGav` = `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds` (`2≤d`); `flowOK=BAFlow`, `T0=BAflowT0` (`rfl`, `Step2BA:123-130`), `L_swap` field present; `0<d` | `2≤d` (G7) | only `hGij` open; closed by D2 |
| 12 | `baSTGijDecgL_holds` (D2) | from `baGbEXPij'_holds d hd` (`GreenOff:1289`, `2≤d`): `c` after `(κ,ε,𝔡)`, loop premise of `STGijDecgL` (both charges) restricted to `(-,+)` by `StochDomAt.precomp_param` (`StochDomAt.lean:335`), `φ n p=(⟨![false,true],_⟩,p)`; conclusion defeq (`FlowFM.indMax` `Step1Boot:54` = `STindMaxg` `Step2Gen:742`; `GreenCore_decayRHS` unfolds) | ≤100 lines | 45 (30/80): case "prove here" applies |
| 13 | lines (script below) | Step2IterBA 898 (hdr 35 + t1-7 863); Step2CloseBA 510 (hdr 30 + t8-12 with 9b 480); row 1,408 | split `>1,950`; reserve `>1,800`; stop 2,000/file; REQ 3,900 | 542 below split; IterBA 902 below reserve; calibrated ×0.93-1.31: 835-1,176 / 474-668 / 1,309-1,844 |

### (ii) One concrete nondegenerate instance
`d=3`, `sz0` (`Defs/Sizes.lean:260`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N=(WL)^3`), `z_n=zS`, `flow_sz0` (`FlowPins:1214`) at `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`; `s≡1/10<t≡1/2<t₀` (`half_lt_t0`); `E_n=0`, `m_F=i`. The Lean-proved bounds `Im m ∈ [1.2/(1.44+g²L³), 5/6]`, `Im z=6/5-Im m`, `t₀=Im m/(6/5)` give the limits below as `g²L³→0` (the concrete limit computation: `g²L³=64(n+1)³/(2(n+1))^{12}→0`; `WO`: `W^{-7/5}=(2(n+1))^{-7}≤lam=(2(n+1))^{-6}≤10`; `W≥N^{1/6}`: `32(n+1)^5≥11.3(n+1)^3`).
Hypotheses per target at this data: 1, 3 none; 2, 4, 5: `0<κ`, `0<𝔡`, `BAFlow`, `3≤d`; 6, 7: also `0<ε`, `t≤BAflowT0`; 8, 11: `3≤d`, `BALWterm 3`, `BALWtermExp 3` stay hypotheses of the example (BA-L6); 9, 9b: `2≤d`, Green input from G7 unconditionally; Step 1, `STLKgL`, `STDecaygL`, `STConStInd` binders of `STStep2G` stay hypotheses (V). The eventual thresholds (e.g. n₀=95 for `5N^{-c}≤1`) are `∀ᶠ n` in the proofs, not part of the instance (Lean instance 12 fixes `sz0`, `zSeq`, `flow_sz0` for all `n`).
```
$ S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2487; python3 $S/pre.py
R1: g0^2=t0 g^2, t0>=k/(k+1), A=(k+1)/k; per t0 in {k/(k+1), 0.9, 0.999}: (g0^2/g^2<=1, g^2/g0^2<=A)
  k=0.1 A=11.0: t0=0.0909: (True, 11.0000<=11.0 True); t0=0.9000: (True, 1.1111<=11.0 True); t0=0.9990: (True, 1.0010<=11.0 True)
  k=0.5 A=3.0: t0=0.3333: (True, 3.0000<=3.0 True); t0=0.9000: (True, 1.1111<=3.0 True); t0=0.9990: (True, 1.0010<=3.0 True)
tail comparison tail_{g0}/tail_g <= A (forward) and tail_g/tail_{g0} (reverse); d=3 W=1e11 D=10, g in {1e-13,1e-3,1}, L in {1e3,1e4,1e6}, u in {0,.5,1-1e-6}, ell'=L and ell'=10
  k=0.1 A=11.0: 54 cases, max forward tailW ratio 10.9999, tailT ratio 10.9999, violations of <=A: 0; max reverse tailW_g/tailW_g0 = 10^15.05
  k=0.5 A=3.0: 54 cases, max forward tailW ratio 3.0000, tailT ratio 3.0000, violations of <=A: 0; max reverse tailW_g/tailW_g0 = 10^15.20
instance: sz0 (Defs/Sizes.lean:260) L=4(n+1) W=(2(n+1))^5 lam=(2(n+1))^-6, flow_sz0 at (kappa,eps,c,dd)=(1/2,1/10,1/6,1/10)
  n=0: WO True Bandwidth(1/6) True (ln W/ln N=0.238) g^2L^3=1.6e-02; Im m in [0.82439,0.83333] Im z in [0.36667,0.37561] t0 in [0.68699,0.69444] BAdom True
  n=100: WO True Bandwidth(1/6) True (ln W/ln N=0.272) g^2L^3=1.4e-20; Im m in [0.83333,0.83333] Im z in [0.36667,0.36667] t0 in [0.69444,0.69444] BAdom True
  n=1000000: WO True Bandwidth(1/6) True (ln W/ln N=0.276) g^2L^3=1.6e-56; Im m in [0.83333,0.83333] Im z in [0.36667,0.36667] t0 in [0.69444,0.69444] BAdom True
n=100: L=404 W=202^5=3.363e+11 g=1.472e-14 N=10^42.40; Im m->5/6 Im z->11/30 t0->25/36=0.69444>=k/(k+1)=0.3333; A=3; g0^2=1.505e-28<=g^2, g^2/g0^2=1.4400<=A
  m_F = m/sqrt(t0): Im m_F = 1.00000 (kappa<=Im m_F<=1: True); s=0.1 < t=0.5 <= t0: True; window 0<g0<=g<=1/dd=10: True
size data: cB=1/(dd^-2+1)=0.00990 c=min(2*dd*c,eps)/2=0.01667: cB W^-3<=Bctl True; Bctl(t0)=8.60e-35<=N^-c=1.965e-01 True; 5N^-c=0.9825<=1 (BA: 3N^-c=0.5895); 1-t0=0.3056>=Imz/2=0.1833 (band uses /4=0.0917)
  eventual threshold 5 N^-c <= 1 first at n=95 (the Lean statement is  forall-eventually n, not part of the instance)
P3: c0=min(2*c*dd, eps/2)=0.03333; RangeCond(eps/2): N^(-1+eps/2)=5.3e-41<=1-t0=0.3056; Bctl(t0)=8.60e-35<=2N^-c0=0.0772; N^(eps/2)>=2: 1.32e+02
F7 constant: K_c = A*K_c0 (A=(k+1)/k=3 at k=1/2, 11 at k=1/10), uniform in (sz,z); F5/F6/F8/F9: C_K=1, K_c0=Q0*C_T+C_s
$ python3 $S/lines.py
newKLK copy (NewKLKGen stNewKLKAtgL'_of): Chain/NewKLKGen.lean:413-606 = 194 lines
size data (Step2Iterate ST_Bdata_holds): Induction/Step2Iterate.lean:1045-1173 = 129 lines
P3 (Step2Scale stScaleExists_holds): Induction/Step2Scale.lean:422-567 = 146 lines
skeleton (Step2IterGen2 ST_step2_of_pinsg): Chain/Step2IterGen2.lean:292-373 = 82 lines
F7 shell (NewKLKBA baNewKLKGenHyp): BA/NewKLKBA.lean:438-548 = 111 lines
K2 (NewKLKBA stK2decaygL'_ba): BA/NewKLKBA.lean:563-602 = 40 lines
LocalAvg reader (Step2CloseGen stLocalAvgOfL2_holdsDecG): Chain/Step2CloseGen.lean:777-805 = 29 lines
  Step2IterBA: t1 10/20/35; t2 50/80/140; t3 15/30/60; t4 80/130/220; t5 280/316/560; t6 90/134/200; t7 110/153/300
  Step2CloseBA: t8 15/30/60; t9 40/70/150; t9b 30/45/80; t10 70/85/180; t11 40/70/120; t12 120/180/320
Step2IterBA targets 1-7 lo/c/hi = [635, 863, 1515]; + header 35: central 898, hi 1550
Step2CloseBA targets 8-12 (+9b) lo/c/hi = [315, 480, 910]; + header 30: central 510, hi 940
row central 1408 (ticket 1,450 without headers and 9b); hi 2490; split line 1,950 (central): does not fire; REQ line 3,900: no
  calibration x0.93: Step2IterBA 835, Step2CloseBA 474, row 1309
  calibration x1.31: Step2IterBA 1176, Step2CloseBA 668, row 1844
2.6x own central (TLC-4 reference): Step2IterBA 2335, Step2CloseBA 1326, row 3661; reserve rule (central > 1,800): no; stop 2,000/file on central: not hit
```
### Registry check (`RBM3D/Test/Axioms.lean`, 641 lines on `t/T2487` = `main` Lean; `#assert_rbm_axioms` = `scanPremises` `:440-487`, failure at `:557`)
The scan reads public theorems only (`keep` needs the prefix `RBM`, private names excluded); a `Prop`-valued `def`/`abbrev` in a binder type (`binderConsts`, `getUsedConstants`, no unfolding) is assumed; it is "proved" if some theorem's conclusion head (through the `∀`-telescope) is that name. T2482's audit failed on exactly this (CONTROL `done: 03:48:47`).
Binder premises of the public targets: 1, 3, 4, 5, 6, 7, 9b: none besides `3 ≤ d`/`0 < d`/`2 ≤ d`. 2: `BAFlow` (proved: `flow_sz0`, `FlowPins:1214`). 9: `BAFlow`, `STGijDecgL` (registered `:202`; proved by `bandFM_STGijDecgL_of_three_le` and by 9b). 8, 11: `BALWterm`, `BALWtermExp` — `abbrev … : ℕ → Prop := baPin …` (`LWPinsBA:45, 47`), so `defnInfo` with `Prop` result: **unclassified and unproved** (`grep` in `Axioms.lean`: only comment hits at `:218-219`; no registered name is an `abbrev`; no merged theorem has them in a binder, only `example`s). Target 10 is private (not scanned).
Lines needed: (R1) add `RBM.BA.BALWterm` and `RBM.BA.BALWtermExp` to `owedProps` after `:219`, owner BA-L6 ("= `baPin LWtermG`/`LWtermExpG`; hypothesis of `baSTOptL2gL_holds`, `baStep2_holds` (T2487)"); alternative without new lines: state 8, 11 with `baPin LWtermG d`-unfolded `LWtermG d (fun sz => Sizes.seqP (sz.withLam 0)) … baFMz BAflowT0` (then only `LWtermG`, `LWtermExpG` at `:218-219` are read), equal to the pin by `abbrev`. Recommend R1 (pin text kept); the dispatcher decides.
Owner-text edits (comment text only, lines re-located by name): `STAvgUgL :228`, `STStep2ConclgL :229`, `STGdecayWgL :197`, `STLocalEntryUgL :201` → "BA: `baStep2_holds` (T2487; inputs `BALWterm`/`BALWtermExp` (BA-L6))" (no U4-BA input under D2); `STStep2DecayPTgL :196`, `STL2decayPTgL :147`, `STScaleInvgL :216` → "BA: inside `baStep2_holds` (T2487)"; `STGijGEXgL :149` → "BA: not needed; `baSTLocalAvgOfL2gL_holds` takes `STGijDecgL` (GMN-C1, T2487)"; `STGijDecgL :202` → owner "BA: `baSTGijDecgL_holds` (T2487)" (moves from U4-BA, D2).
No other line is added or removed.
Verdicts: targets 1-12 PASS; 9b (`baSTGijDecgL_holds`, new, D2) PASS. Findings for the dispatcher: D1 no split, no reserve; D2 target 11 becomes `BALWterm d → BALWtermExp d → BAStep2 d` (`T2487_Step2Holds` follows by an unused third argument; target 9 keeps the pin's `T2487_BAGijDec` hypothesis); D3 R1 above.

### (b) Script output, stage 1b (prover-hard role, model claude-sonnet-5-5), written Tue Oct 13 04:29:19 UTC 2026
**Result: every target delivered (1-9 and 11 public, 10 private, plus 9b), no split (D1: 1,092 lines in all, per file 833 / 259, stop line 2,000, reserve rule 1,800 not reached; no `Step2IterBA2`); D2 applied (`baSTGijDecgL_holds` proved here, 10 lines): target 11 `baStep2_holds` takes only `BALWterm d`, `BALWtermExp d` (dispatcher answer (3)), the pin `T2487_Step2Holds` follows by an unused third argument; premise scan asked for 2 new registry lines (D3, R1), added with the root imports (Test/Axioms.lean is a sole writable file); full `lake build` with the root imports passes.**
```
$ git log --oneline main..HEAD ; git merge-base main HEAD
3b9c210d T2487: docstring wording (no forbidden-form text in Step2CloseBA)
503cb185 T2487: root imports and registry (BALWterm, BALWtermExp; owner texts of the Step 2 pins)
633d5114 T2487: BA/Step2CloseBA targets 8-11 (+9b Green input) and instances
5635865d T2487: BA/Step2IterBA targets 1-7 (Hermitian walk, one loop, list link, K2, newKLK, size data, P3) and instances
ba7e559e
$ merged-source column (script: first `theorem|def|abbrev|structure NAME` line, file without RBM3D/ and .lean : line)
baStep2Mat BA/Step2BA:54; baStep2Data BA/Step2BA:123; baStep2Mat_Hpath BA/Step2BA:94; baStep2Fam_lam_pos_le BA/Step2BA:170; BAFlow BA/FlowPins:389; baFMz BA/FlowPins:393; BAflowLam0 BA/FlowPins:386; BAflowEs BA/FlowPins:383
BAflowT0 BA/FlowPins:380; baKsol_one BA/KInduct:77; BAflow_real BA/GreenSchur:59; BAflow_lam0_window BA/GreenSchur:72; EMn2BA_seqHflowBA_herm BA/EMn2BA:68; EMn2BA_mF_data BA/EMn2BA:125; EMn2BA_one_sub_T0 BA/EMn2BA:111
EMn2BA_T0_lt_one BA/EMn2BA:106; EMn2BA_zim_pos BA/EMn2BA:85; TwistStep2_lam0_sq BA/TwistStep2:740; stK2decaygL'_ba BA/NewKLKBA:567; baNewKLKGenHyp BA/NewKLKBA:446; NewKLKBA_tail BA/NewKLKBA:269; NewKLKBA_conv_P BA/NewKLKBA:61
baComp_row_le BA/EMn2BA:386; Step2Kern_thetaKer_BA Chain/Step2Kern:90; ekPropTInf_holds Evolution/PropTInf:534; baFlow_premises BA/NetLiftBA:65; baGridMart_holds BA/GridMartBA:673; baNetLift2_holds BA/NetLiftBA:782
baSTEMn2Poly BA/EMn2BA:753; baSTEMn2Exp BA/EMn2BA:777; baSTGiiGEXgL_holds BA/Step1Prime:904; baSTGavLGEXgL_holds BA/Step1Prime:913; baGbEXPij'_holds BA/GreenOff:1289; GreenCore_loopPrem BA/GreenCore:1616
stOptL2_of_pinsg Chain/OptL2Gen:1109; stLocalAvgOfL2_holdsDecG Chain/Step2CloseGen:781; stLWBgL_of_LWtermG Chain/Step2EventsGen:1005; stLWTgL_of_LWtermExpG Chain/Step2EventsGen:1080; Step2EventsGenTw_baFlow Chain/Step2EventsGenTw:53
Step2EventsGenTw_baGrid Chain/Step2EventsGenTw:73; Step2EventsGenTw_baRot3 Chain/Step2EventsGenTw:58; ST_Eblk_herm Induction/Step2Iterate:1209; ST_Gres_false Induction/Step2Iterate:1198; loopM_eq_loopL Loop/GLoopFlow:127
pathH_isHermitian Path/Walk:98; PsiI_isHermitian Gauss/BlockAnderson:65; Step2IterGen_OneLoop Chain/Step2IterGen:81; Step2IterGen_ListLink Chain/Step2CloseGen:65; Step2IterGen_K2 Chain/Step2IterGen:71
Step2IterGen_NewKLK Chain/Step2IterGen:63; Step2IterGen_NewKLKAtN Chain/Step2IterGen:50; STBdatagL Chain/Step2EventsGen:966; STScaleExistsgL Chain/Step2Gen:632; STOptL2gL Chain/Step2Gen:621; STLocalAvgOfL2gL Chain/Step2Gen:613
STGijDecgL Chain/CltGen:94; NewKLKGen_bound2 Chain/NewKLKGen:139; NewKLKGen_ward_LKM Chain/NewKLKGen:296; stNewKLKAtgL'_of Chain/NewKLKGen:416; ST_Bdata_holds Induction/Step2Iterate:1049; stScaleExists_holds Induction/Step2Scale:430
ST_step2_of_pinsg Chain/Step2IterGen2:299; BAStep2 BA/FlowPins:432; BALWterm BA/LWPinsBA:45; BALWtermExp BA/LWPinsBA:47; nkl_Cs_ge_one Induction/NewKLK:112; st2sSeq Induction/Step2Scale:131
StochDomAt.precomp_param Defs/StochDomAt:335
$ open private (no `private` deleted): ticket list used: NewKLKBA_conv_P NewKLKBA_tail (NewKLKBA_real not needed); nkl_Cs_ge_one nkl_tailT_le_tailW nkl_zdistInf_sub_comm (RBM3D.Induction.NewKLK);
  st2sSeq st2sSeq_bounds st2sSeq_cap st2sSeq_clause4 st2sSeq_floor st2sSeq_mono_succ st2sSeq_tailT_mono_time st2s_cap_arith st2s_floor_arith (RBM3D.Induction.Step2Scale);
  ADDED beyond the ticket list: NewKLKGen_bound2 NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen (the two private lemmas that the copied proof of target 5 calls; not copied)
$ imports Step2IterBA: Chain.Step2CloseGen Chain.Step2EventsGenTw Chain.NewKLKGen BA.Step2BA BA.NewKLKBA BA.KInduct BA.EMn2BA BA.GreenSchur BA.TwistStep2 BA.NetLiftBA Induction.Step2Scale (the ticket's list)
  imports Step2CloseBA: BA.Step2IterBA BA.GridMartBA BA.Step1Prime BA.LWPinsBA BA.GreenOff (GreenOff added: `baGbEXPij'_holds`); layering: `git grep 'import RBM3D.BA.Step2(Iter|Close)BA'` = RBM3D.lean:568-569 and Step2CloseBA.lean:6 only
$ name clash: git grep -l -w <the 11 public names> main -- 'RBM3D/*.lean' 'RBM3D.lean'  -> exit 1 (no hit); same over the other 496 `t/*` branches -> 0 branches with a hit (a run over docs/tickets on main had hits only in T2486.md, T2487.md, checks/T2487-check.lean)
$ lake build RBM3D.BA.Step2IterBA RBM3D.BA.Step2CloseBA | tail -1
Build completed successfully (4089 jobs).
$ lake build | grep -E 'axiom audit:|Build completed'   (RBM3D.lean with the two new imports; #assert_rbm_axioms)
info: RBM3D.lean:572:0: axiom audit: 14433 theorems, 4533 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4340 jobs).
$ lake env lean docs/tickets/checks/T2487-check.lean  -> exit 0, 0 error lines
$ lake env lean axfinal.lean   (#print axioms of the 11 public declarations; prefix 'RBM.BA. dropped)
baStep2Mat_Hpath_herm [propext, Classical.choice, Quot.sound]
baStep2_oneLoop [propext, Classical.choice, Quot.sound]
baStep2Mat_listLink [propext, Classical.choice, Quot.sound]
baStep2_K2 [propext, Classical.choice, Quot.sound]
baStep2_newKLK [propext, Classical.choice, Quot.sound]
baSTBdatagL_holds [propext, Classical.choice, Quot.sound]
baScaleExists_holds [propext, Classical.choice, Quot.sound]
baSTOptL2gL_holds [propext, Classical.choice, Quot.sound]
baSTGijDecgL_holds [propext, Classical.choice, Quot.sound]
baSTLocalAvgOfL2gL_holds [propext, Classical.choice, Quot.sound]
baStep2_holds [propext, Classical.choice, Quot.sound]
$ statements extracted by script (regex from `theorem NAME` to the first `:=`, whitespace joined; [n] = target of the ticket, file:line)
[1] Step2IterBA.lean:62: theorem baStep2Mat_Hpath_herm {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) : ((baStep2Mat sz lam0 E).Hpath s t K n k ω).IsHermitian
[2] Step2IterBA.lean:74: theorem baStep2_oneLoop {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) : Step2IterGen_OneLoop (baFMz sz z)
[3] Step2IterBA.lean:105: theorem baStep2Mat_listLink {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : Step2IterGen_ListLink (baStep2Mat sz lam0 E)
[4] Step2IterBA.lean:198: theorem baStep2_K2 (d : ℕ) : Step2IterGen_K2 d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
[5] Step2IterBA.lean:706: theorem baStep2_newKLK (d : ℕ) : Step2IterGen_NewKLK d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
[6] Step2IterBA.lean:226: theorem baSTBdatagL_holds (d : ℕ) (hd : 0 < d) : STBdatagL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0
[7] Step2IterBA.lean:351: theorem baScaleExists_holds (d : ℕ) : STScaleExistsgL d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0
[8] Step2CloseBA.lean:48: theorem baSTOptL2gL_holds (d : ℕ) (hd : 3 ≤ d) (hLW : BALWterm d) : STOptL2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
[9b] Step2CloseBA.lean:66: theorem baSTGijDecgL_holds (d : ℕ) (hd : 2 ≤ d) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ BAflowT0 sz z n) → STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u
[9] Step2CloseBA.lean:81: theorem baSTLocalAvgOfL2gL_holds (d : ℕ) (hd : 2 ≤ d) (hGij : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ BAflowT0 sz z n) → STGijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) : STLocalAvgOfL2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
[10 (private)] Step2CloseBA.lean:100: private theorem Step2CloseBA_step2_of_pins (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hFl : Step2EventsG … [binders as ST_step2_of_pinsg; hOne guarded; see skeleton diff]
[11] Step2CloseBA.lean:181: theorem baStep2_holds (d : ℕ) (hLW : BALWterm d) (hLWE : BALWtermExp d) : BAStep2 d
$ pins.lean = the T2487_* defs cut from the check file + `example : T2487_HpathHerm := @baStep2Mat_Hpath_herm` ... `T2487_OneLoop/ListLink/K2/NewKLK/Bdata/ScaleExists/OptL2/LocalAvgOfL2 := @name`, `∀ d, 2 ≤ d → T2487_BAGijDec d := @baSTGijDecgL_holds`, `T2487_Step2Holds := fun d hL hE _ => baStep2_holds d hL hE`: lake env lean -> exit 0, empty output
$ shape.lean: def T2487_skeleton_shape (the check's `example : Prop` of the guarded skeleton, cut by script) + `example : T2487_skeleton_shape := @Step2CloseBA_step2_of_pins` (open private): exit 0, 0 error lines, 54 unused-variable warning lines
$ difflib.unified_diff(merged ST_step2_of_pinsg statement+proof (Step2IterGen2:299-372), private copy)   [73 vs 74 lines]
@@ -10 +10,2 @@  -    (hOne : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2IterGen_OneLoop (mk sz z).toFlowFM)
               +    (hOne : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →   +      Step2IterGen_OneLoop (mk sz z).toFlowFM)
@@ -73 +74 @@      -  exact ST_concl_of_step2g _ _ hl ha hd' (hOne sz z) hs ht1   +  exact ST_concl_of_step2g _ _ hl ha hd' (hOne sz κ ε 𝔠 𝔡 z hκ hflow) hs ht1
$ compiled nonempty instances (`example`s, d = 3, sz0 / zSeq / flow_sz0 at (1/2, 1/10, 1/6, 1/10), s ≡ 1/10 < t ≡ 1/2 < t₀ by half_lt_t0; all built in the commands above)
Step2IterBA.lean:793:example (ω : PathΩ sz0) :
Step2IterBA.lean:798:example : Step2IterGen_OneLoop (baFMz sz0 zSeq) :=
Step2IterBA.lean:802:example : Step2IterGen_ListLink (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) :=
Step2IterBA.lean:806:example : ∃ C_K : ℝ, 0 < C_K ∧ ∀ᶠ n in atTop, ∀ (u D : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)),
Step2IterBA.lean:814:example : ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
Step2IterBA.lean:820:example : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
Step2IterBA.lean:827:example : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) Kseq :=
Step2CloseBA.lean:211:example : STGijDecgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) :=
Step2CloseBA.lean:216:example (hLW : BALWterm 3) : ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
Step2CloseBA.lean:228:example : STStep1WeakgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
Step2CloseBA.lean:237:example (hLW : BALWterm 3) (hLWE : BALWtermExp 3) : ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
Step2CloseBA.lean:251:example (d : ℕ) : BALWterm d → BALWtermExp d →
  hypotheses left open in the examples: BALWterm 3, BALWtermExp 3 (stage L, BA-L6) for targets 8, 11; Step 1 (STStep1LoopgL, STStep1WeakgL), STLKgL, STDecaygL, STConStInd, STL2decayPTgL binders of the pins; target 1 has a sample point ω
$ greps on the new files
withLam: public statements: only `Sizes.seqP (sz.withLam 0)` (Step2CloseBA:49, 68, 84-85, 254); proof-internal hits: Step2IterBA:65, 209, 214, 733-737 and Step2CloseBA:50, 56, 86, 184, 191; docstrings Step2IterBA:60, 195-196, 701 and Step2CloseBA:177; `local notation μ0` Step2CloseBA:208; the PRIVATE lemma `Step2IterBA_prof_le` statement Step2IterBA:178-180 (R1, proof-internal)
forbidden-form grep (STGridRepNgL|STGijGEXgL|baStep1_holds\b|\|E\||2 - κ|STFlow|lemT|\bmE\b): Step2IterBA 0, Step2CloseBA 0   X1-C4 `^(noncomputable )?(def|abbrev|structure) (STGijDecgL|STBdatagL|STScaleExistsgL|Step2IterGen_|BAStep2|T2487)`: 0 hits; the files contain no def/abbrev/structure at all
`≤ A *` / `A *` hits: Step2IterBA:128-189 (the private R1 comparison lemmas of target 4) and :719-776 (proof of target 5); no public statement contains a comparison
$ wc -l: Step2IterBA 833 (header 57; targets 1-3: 58-110; 4: 111-218 with 5 private comparison lemmas; 6: 219-343; 7: 344-480; 5: 481-781 (private copy 207 lines, theorem 73); instances 782-833); Step2CloseBA 259 (8: 42-59; 9b+9: 60-93; 10: 94-174 (74 lines); 11: 175-197; instances 198-259)
$ git diff main...HEAD --stat: RBM3D.lean +2; RBM3D/BA/Step2CloseBA.lean 259; RBM3D/BA/Step2IterBA.lean 833; RBM3D/Test/Axioms.lean +12 -9 (no Chain/, Induction/, Evolution/, Path/ or merged BA/ file)
$ registry diff (Test/Axioms.lean, comment text; script: name | tail of the changed line)
NEW BALWterm, BALWtermExp (owedProps, after LWtermExpG): premise scan error before the lines: '2 premise(s) ... [RBM.BA.BALWterm, RBM.BA.BALWtermExp]'; they are `abbrev … : ℕ → Prop := baPin …` in a binder of baSTOptL2gL_holds, baStep2_holds
EDITED owner text: STAvgUgL, STStep2ConclgL, STGdecayWgL, STLocalEntryUgL -> 'BA: `baStep2_holds` (T2487; inputs `BALWterm`/`BALWtermExp` (BA-L6); the Green input is proved by `baSTGijDecgL_holds`)'; STStep2DecayPTgL, STL2decayPTgL, STScaleInvgL -> 'BA: inside `baStep2_holds` (T2487)'; STGijGEXgL -> 'BA: not needed; `baSTLocalAvgOfL2gL_holds` takes `STGijDecgL` (GMN-C1, T2487)'; STGijDecgL -> 'BA: proved by `baSTGijDecgL_holds` (T2487); hypothesis of `baSTLocalAvgOfL2gL_holds`' (owner moves U4-BA -> T1-BA)
```
**Narrative** (facts only; the evidence is the script output above)
1. Size: central of (a) was 1,408 (Step2IterBA 898, Step2CloseBA 510); actual 833 and 259. The pre-signed split (central > 1,950) did not apply; stop rule 1 not reached.
2. F1 (target 5). `Step2IterBA_newKLKAtN_of` (private, 207 lines) is the per-carrier copy of `stNewKLKAtgL'_of` (Chain/NewKLKGen.lean:416-605, last commit ef345e15, same repository, no RBM1D/RBM2D text): F5, F7, F8, F9 are hypotheses at one `(Cm, n)`, the `(TTT2)` bound is a hypothesis at the profile `g = sz.lam n`, the constant is the explicit `2 K_c + 2 C_s (4 + C_K) + C_s C_T`. `baStep2_newKLK` fixes, per `(κ, 𝔡)`, `Q₀` (`NewKLKBA_tail`, `Λ = 𝔡⁻¹`), `C_T` (`ekPropTInf_holds`), `C_K` (`baNewKLKGenHyp`), sets `K_c = A (Q₀ C_T + C_s)`, `A = (κ+1)/κ`, and gives `C = 2 K_c + 2 C_s (4 + C_K) + C_s C_T` before `ε 𝔠 sz z`. F5, F8, F9 are read from `baNewKLKGenHyp` at `sz.withLam (BAflowLam0 sz z)` by definitional unfolding (`baStep2Fam (sz.withLam g₀) (fun _ => E_n)` and `baStep2Mat sz g₀ E` agree at index `n`). F7 is proved at mixed coupling: `NewKLKBA_tail` at `g₀` with `baComp_row_le` and `BAflow_real`, then the forward comparison `𝒯_{g₀} ≤ A 𝒯_g` (`Step2IterBA_tailT_le`; `g₀ ≤ g` and `g² ≤ A g₀²` from `baStep2Fam_lam_pos_le`, `TwistStep2_lam0_sq`), then `NewKLKBA_conv_P` at `g = sz.lam n`. No reverse comparison.
3. F2 (targets 10, 11). `Step2CloseBA_step2_of_pins` differs from `ST_step2_of_pinsg` in the `hOne` binder and its one use (diff above); `baStep2_holds` supplies `hOne` from `baStep2_oneLoop` (target 2) under `0 < κ` and `BAFlow`. T1a's statement is not edited; no second public skeleton.
4. Target 2 is the single BA one-loop proof (`baKsol_one` at `g₀ > 0`, `BAflow_real`; `ST_Lloop_one_false` argument at `seqHflowBA`); T2486 2 (b) can read it by the unchanged name `baStep2_oneLoop`.
5. Target 4: `stK2decaygL'_ba` at `sz.withLam g₀`, `E ≡ E_n`, then `Step2IterBA_prof_le` (private, forward, R1); `C_K = Q₀ A`. Target 6: copy of `ST_Bdata_holds` (Induction/Step2Iterate.lean:1049-1173, last commit c5bbae7b): the chain with `Im z/4` is unchanged, `Im z/4 ≤ 1 - u` follows from `EMn2BA_one_sub_T0` (`Im z/2 ≤ 1 - t₀`), `u < 1` from `EMn2BA_T0_lt_one`; so `cB`, `c` are the band's. Target 7: copy of `stScaleExists_holds` (Induction/Step2Scale.lean:430-567, last commit 6e7bb9c5) with `v3_premises_of_stFlow` replaced by `baFlow_premises` and `hflow.1` (two lines).
6. Target 9b (`baSTGijDecgL_holds`, 10 lines; priced 45 in (a)): `baGbEXPij'_holds` gives `c`; the two-charge loop premise of `STGijDecgL` is restricted to `(-,+)` by `StochDomAt.precomp_param` (`Defs/StochDomAt.lean:335`) with `p ↦ (⟨![false, true], _⟩, p)`; the conclusion is the one of `BAGbEXPij'` by unfolding. Target 9 is `stLocalAvgOfL2_holdsDecG` at `baStep2Data` (`flowOK`, `T0`, `toFlowFM` by `rfl`), `hdat` from target 6 (reordered), `hGii`, `hGav` from G7, `hGij` the pin's hypothesis. Target 8 is `stOptL2_of_pinsg` at the BA family (F3 inline with `κm = κ`).
7. UBA-C1 table as used (R1 only: `g₀² ≤ g²`, `g² ≤ A g₀²`, `A = (κ+1)/κ`, `TwistStep2_lam0_sq`): targets 1, 3: size level none, kernel `lam0 • PsiI`, `KI`, no crossing. 2: none; `baKsol_one` at `g₀ > 0`; no crossing. 4: `STprof sz`; `stK2decaygL'_ba` at `sz.withLam g₀`; `STprof (sz.withLam g₀) ≤ A STprof sz`, forward. 5: `STprof sz`, `tailW` and `(TTT2)` at `sz.lam n`, WO window; F5, F8, F9 and the kernel tail at `g₀`; `𝒯_{g₀} ≤ A 𝒯_g`, forward, and `0 < g₀ ≤ g`. 6, 7: `Bctl`, WO, `tailT … (sz.lam n)`, `ellT`, `RangeCond`; no kernel level; no crossing. 8-11: inherited, no crossing in statements. No public statement reads `withLam` except `seqP (sz.withLam 0)`; no Ĵ-form bound at `sz.withLam g₀` is transported.
8. TN-C4: the only grid input is `baGridMart_holds` (`STGridMartgL`); no `STGridRepNgL`. Step 1 enters only as the `STStep2G` binders (`STStep1LoopgL`, `STStep1WeakgL`, `STLKgL`, `STDecaygL`, `STConStInd`); no `baStep1_holds`.

### (c) Verified Mathlib names (`#check` in a scratch file importing the module; all exist, signatures as used)
`le_div_iff₀`, `div_le_div_iff₀`, `div_le_div_of_nonneg_right`, `div_le_div_of_nonneg_left`, `le_mul_of_one_le_left`, `Real.sqrt_le_sqrt`, `Real.exp_le_exp`, `Real.sqrt_nonneg`, `Real.rpow_nonneg`, `min_le_min`, `max_le_max`, `neg_le_neg`, `inv_pos`, `_root_.inv_zero` (needs the prefix under `open Matrix`: `Matrix.inv_zero` is ambiguous), `Matrix.IsHermitian.add`, `Matrix.IsHermitian.submatrix`, `Matrix.conjTranspose_smul`, `Matrix.conjTranspose_mul`, `Matrix.trace_conjTranspose`, `Matrix.trace_mul_comm`, `Complex.conj_ofReal`. Names verified absent: none searched.

### (d) Open issues and paper-delta candidates
1. Target 11 differs from the pin `T2487_Step2Holds` by design (dispatcher answer (3), case ≤ 100 lines): two inputs, not three; the pin follows by the last `example` of Step2CloseBA §5. The owner of `STGijDecgL` at BA moves from U4-BA to T1-BA (registry text edited); consumers (U5c T2485, U3-BA, T2486, `twSteps`, V, U4-BA/X1) read `baStep2_holds d hLW hLWE`, U4-BA reads `baSTGijDecgL_holds` for its Green input. The dispatcher updates the tickets.
2. `open private NewKLKGen_bound2 NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen` is beyond the ticket's list (no `private` deleted, no merged file edited).
3. Registry: the scan required `BALWterm`, `BALWtermExp` in `owedProps` (R1 of (a)); added with owner BA-L6 and nine owner-text edits; dispatcher to confirm. `RBM3D.lean` import lines are in the branch (commit 503cb185); CLAUDE.md §3 (A) step 4 adds them at merge, they are already present.
4. The examples leave `BALWterm 3`, `BALWtermExp 3` (BA-L6) and the Step 1, `STLKgL`, `STDecaygL`, `STConStInd`, `STL2decayPTgL` binders open; every other premise is discharged. Target 6 keeps the band's `cB`, `c` (not sharpened with `Im z/2`).
5. Paper-delta candidates: **T2487a** `lem:newKLK` at BA (`3_5:371`, `7_8:1994`): the kernel is at `g₀ = √t₀ g` and the profile at `g`; the constant is uniform in `(sz, z)` with `K_c = A K_c⁰`, `A = (κ+1)/κ` (R1); the paper's proof does not name this crossing. **T2487b** the one-loop input of Step 2 (`Def_Ktza`, `1_2:988`; `𝒦^{(1)} = m(σ)`) is read under `0 < κ` and the flow: `BAKsol` is `0` when no tree solution exists (`BA/FlowPins.lean:283`), so the first conjunct needs `BAReal`.
