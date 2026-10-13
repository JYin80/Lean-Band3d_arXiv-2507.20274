Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 23:32:50 UTC 2026

Verdicts: targets 1-8, 10-12 PASS. Target 9: the mathematics closes (PASS), but its itemised cost is 525 lines (400/740), above the ticket's 300-line cap, so by the ticket's rule it moves to T1-BA (no RETURN; row 18). Split confirmed: T1a = targets 1-6 (central 1,586), T1b = targets 7, 8, 10, 11 (1,379; 1,904 if 9 stayed); row 2,965 (3,490 with 9) > 1,950. Class fields with no band discharge: none. Tripwire not fired (g 0.195, f_sem 0.003). Finding for T1-BA (row 17): the UBA-C1 comparison holds from R1 but only through F7 of `NewKLKGenHyp`, not by transporting the Ĵ-form conclusion of `stNewKLKgL'_ba`.

### (i) Exponent / threshold / constant table
| # | item | value | constraint | slack |
|---|---|---|---|---|
| 1 | `Cd`, `𝔠d` (`Step2Iterate:1393+`) | `Cd=3C+1`, `𝔠d=min(1/100, 1/(60Cd), 𝔠₀)` | `Cd·𝔠d ≤ 1/60` (h3, :700); `𝔠d ≤ 1/100` (`STStep2G`) | C=1: Cd=4, 𝔠d=1/240, `Cd·𝔠d=1/60` exactly (0, binding by design); 1/100−1/240=0.00583 |
| 2 | `hq` closure (`ST_hq_arith`, :683) | `b^{1/5−Cd𝔠d} ≤ b^{1/6}` with `r ≤ bt^{−𝔠d}` | `1/5−Cd𝔠d ≥ 1/6` | 11/60 vs 10/60: 1/60; worst measured `r^{Cd}b^{1/5}/b^{1/6}` = 0.091 (n=100, 17 grid times) |
| 3 | P4 `hsmall` (`Step2Core:997`) | `(3+3/κm)Λ²(1+q+log r_k)r_k^{3C}B_k^{1/30} < 1`, all `k ≤ K` | `< 1` | worst 0.598 at the instance (slack 0.402, Λ=C=1, q=1/10); closure form `(3+3/κm)Λ²(1+Λ)B_t^{1/60}<1` uses `r^{3C} ≤ B^{−3C𝔠d}`, `3C𝔠d ≤ 1/60` |
| 4 | target 3 smallness (hP1) | `Λ=q=2N^{ε₁}`, `ε₁=min(τ/6, c/400)`, `cstar=3+3/κm`: `12·cstar·N^{3ε₁−c/60} < 1` | `3ε₁ < c/60` | `c/60−3c/400 = 11c/1200` (0.00747 at c=0.815); eventual threshold log10 N > 324 (κm=√κ/2, τ=0.3): the band proof's `∀ᶠ n`, not a witness |
| 5 | hP2, weak law (E1) | `12·cstar·N^{3ε₁} ≤ N^τ`; `N^{ε₁}Bctl^{1/4} ≤ δ₀` | `3ε₁ < τ`; `ε₁ < c/4` | τ/2; 99c/400 |
| 6 | grid and martingale tail | `Dm=D'+2D+10`; `K_n=⌈N^{CK'}⌉`, `CK'=max(CK, 2(C₀+D+3))`; `Di=(D+3)/𝔠` | `D'+4 ≤ Dm`, `2D+6 ≤ Dm`; `C₀−CK'/2 ≤ −(D+3)`; `W^{−Di} ≤ N^{−(D+3)}` | `2D+6`; `D'+4`; 0 (binding); 0 (binding, `W ≥ N^𝔠`) |
| 7 | target 8 (`OptL2b_arith`, :57) | `𝔠₀=1/(8C₀+10)`, `C₀=2C`; `ε₀=dc/4` (`c ≤ 1`), `ε₁=τ/8` | `𝔠d ≤ 𝔠₀`: `C₀𝔠d ≤ 1`, `𝔠d(C₀+5/4) ≤ 1/4`, `𝔠d ≤ 1/2` | C=1: 𝔠d=1/240 vs 𝔠₀=1/26; `C₀𝔠d`=0.0083 (0.99); `𝔠d(C₀+5/4)`=0.0135 (0.236). `STBdatagL` has no `c ≤ 1`: take `min(c,1)` (`N ≥ 1`) |
| 8 | size data and admissibility (n=100) | `cB=1.000`, `c=0.815`, `𝔠=1/6`, `𝔡=κ=ε=1/10`; `ln W/ln N=0.272` | `cB W^{−d} ≤ Bctl ≤ N^{−c}`; `W^{−1.4} ≤ lam ≤ 1/𝔡`; `N^{1/6} ≤ W` | `W^{−1.4}`=1e-16.14 ≤ lam=1e-13.83 ≤ 10; `N^{1/6}`=1.17e7 vs W=3.4e11 |
| 9 | F3 spectral datum | `κm=√κ/2=0.158` (band, `DecayGen_bandSpec`); BA `κm=κ` | `0 < κm ≤ Im m` | Im m = 1 (E=0) |
| 10 | T9 exponents | `τ ≤ 2c` (WLOG), `τ₁=τ₂=τ/4`, `ε₀=min(1/2, dc/8)`, `Ψ=W^{−d/2}`, `Φ_n(a,b)=N^{τ₁/2}√STWB(u,\|a−b\|)`, `D=d/𝔠` | `Φ ≤ W^{−ε₀}` (needs `τ₁ ≤ 3c/4`, `W^d ≤ N`); `Ψ ≤ W^{−ε₀}` (`ε₀ ≤ d/2`) | τ=0.3: log10 Φ=−15.70 vs log10 W^{−ε₀}=−3.52; `ε₀ ≤ 1/2 ≤ d/2`, slack 1 at d=3 |
| 11 | T9 regularity (replaces `(eq:Psirelations)`, `7_8:2033-2050`) | `K ≤ K'+j ⇒ STWB(K') ≤ (j+1)^{d−2} STWB(K)` (from `Bparam=(g²+\|1−u\|)⁻¹(K+1)^{−(d−2)}+(L^d\|1−u\|)⁻¹`); `localAvg1_STWB_comp` is `j=2` with `3^{d−2}`, exponential in `j`: unusable | needs only `c'>0` arbitrary (the `∃c` of `STGijDecgL`) | sampled max ratio / `(j+1)^{d−2}` = 1.0000 (tight); `S_∞(c'=1)=Σ_m(2m+1)^d(m+1)^{d−2}e^{−m}`=356.0; `M=sup(x+1)^{d−2}e^{−2c'x}`=1.0 |
| 12 | T9 floor and constant | `W^{−2D} ≤ cB W^{−d}(L+1)^{−(d−2)} ≤ STWB(r)` (`r ≤ L ≤ N`, `W ≥ N^𝔠`); `C₂=3(S⁴+cB⁻¹M+1) ≤ N^{τ/4}`; exponents `2τ₂+τ₁+τ/4 = τ` | `D ≥ d/𝔠`; `C₂ ≤ N^{τ/4}` eventually | log10: −415 vs −37.2; C₂=4.8e10, holds for log10 N ≥ 142 (eventual); exponent sum slack 0 (binding) |
| 13 | (vi) R1 at BA: `g₀=√t₀ g`, `t₀ ≥ κ/(κ+1)` | `A=(κ+1)/κ=11`: `g₀² ≤ g²`, `g² ≤ A g₀²` (equality at `t₀=κ/(κ+1)`) | forward `tailW_{g₀} ≤ A·tailW_g` | sup `P_{g₀}/P_g`=10.956 ≤ 11 (slack 0.044); reverse `P_g/P_{g₀}` = 3.6, 1.0e4, 8.1e14, 3.8e48 at L=1e3..1e6: not ≤ const |
| 14 | (vi) consequence | `Ĵ_{sz}=max‖LK‖/STprof_{sz}`: transport of the Ĵ-form of `stNewKLKgL'_ba` (at `sz.withLam g₀`) to `sz` needs the reverse bound (row 13 fails); `K2` (absolute bound) needs only the forward one | see row 17 | `T2478_K2` at BA: forward suffices (PASS); `T2478_NewKLK`: via F7 only |
| 15 | line estimate, central (script `lines.py`) | `Step2IterGen` 1,115; `Step2IterGen2` 471; `OptL2Gen` 1,098; `Step2CloseGen` 281 (+525 if 9 stays); factor 0.88 on restated band spans (T2453 683/778) + itemised new text, instances ×0.6 (T2474 method) | split if row > 1,950; each half ≤ 1,950; stop 2,000/file; reserve 1,800; REQ line 3,900 | T1a 1,586 (ticket 1,550); T1b 1,379 (ticket 1,300 incl. 9=250); with 9: 1,904 (slack 46); row 2,965 / 3,490 (ticket 2,850); no file above 1,800 on central; 2.6× own central: Step2IterGen 2,899, OptL2Gen 2,854 (above 2,000; precedent ratios 0.74-0.88 say central) |
| 16 | T9 itemised new text (`lines.py`) | shift lemma 35; lattice shell sum 90; absorption 40; Φ/Ψ ranges + D floor 45; loop premise from `localAvg1_whp_L2G` (both charges via `L_swap`) 50; entry bound 110; reader assembly (`LocalAvg2` reader, 95×0.88, + new events) 125; `…holdsDecG` 30 | cap 300 | 525 (range 400 / 740 = 0.76× / 1.4×): above the cap by 225 |
| 17 | BA obligation of target 1 (statement level) | F5, F6, F8, F9 of `NewKLKGenHyp` are profile-free; F7 uses the profile only through `NewKLKBA_conv_P` at `g := sz.lam`, `HT` (`ekPropTInf`) at `sz.lam`, and the kernel tail `HQ`; at the pair (kernel `g₀`, profile `sz`) the tail is `Q₀𝒯_{g₀} ≤ Q₀A𝒯_g` (row 13, forward) | T1-BA: apply `stNewKLKgL'_of` to the family `E ↦ baStep2Mat sz (BAflowLam0 sz z) E` with F7 re-proved by that substitution (`Q := A·Q₀`), domain `0<g₀≤g≤1/𝔡`, `κ ≤ Im m` (`baStep2Fam_lam_pos_le`, BAdom) | R1 suffices; not UBA-C1; estimate ≈ 60 lines of F7 plus the `K2` line `STprof(g₀) ≤ A STprof(sz)`; `NewKLKBA_conv_P`, `NewKLKBA_tail` are `private` in `BA/NewKLKBA.lean` (`open private … from`) |
| 18 | target 9 argument | data of row 10. (1) `localAvg1_whp_L2G` gives `‖L_{−+}(a,b)‖ ≤ N^{τ₁}STWB(u,\|a−b\|)` for all `(a,b)` w.h.p.; `(+,−)` by `Cm.L_swap` and `\|b−a\|=\|a−b\|`: this is the loop premise `PrecL(indMax‖L_σ‖ ≺ Φ²)` of `STGijDecgL`. (2) ranges, row 10. (3) `STGijDecgL` gives w.h.p. `indMax‖GM_{xy}‖ ≤ N^{τ/4}R`, `R=Σ_{a',b'}Φ(a',b')e^{−c'(\|a'−[x]\|+\|b'−[y]\|)} + Ψe^{−c'r} + W^{−D}`, `r=\|[x]−[y]\|`. (4) with `j=\|a'−[x]\|+\|b'−[y]\|`, `r ≤ \|a'−b'\|+j` and row 11: `ΣΦe^{−c'j} ≤ S_∞(c',d)²N^{τ₁/2}√STWB(r)`; `Ψ²e^{−2c'r} ≤ cB⁻¹M STWB(r)` (`STWB(r) ≥ (r+1)^{−(d−2)}cB W^{−d}`); `W^{−2D} ≤ STWB(r)` (row 12). (5) square: `‖GM_{xy}‖² ≤ N^τ STWB(r)` eventually; `x=y` from `STGiiGEXgL` as in `localAvg2_entry_leG`; Ω from `localAvg1_whp_omegaG`. No truncation at `(log W)^{3/2}`: the Lean window sums all `(a',b')` and `c'>0` is arbitrary. | closes from merged names (`localAvg1_*`, `STGijDecgL`, `Cm.L_swap`, `flowOK_adm`, `hdat`) | decision: lines 525 > 300, so the target moves to T1-BA; if kept, T1b is 1,904 ≤ 1,950 (slack 46) |
| 19 | tripwire (`gfsem.py`) | `g` proxy = band-token lines / restated code lines = 442/2,269 = 0.195; `f_sem` = declarations naming a star-tree / K closed form = 8/3,161 = 0.003 (raw `KLtreeValW\|KLSigmaPi\|kTwo\|KLIsTSP\|couplingLen` hits: 0) | fire above 0.50 / 0.30 | 0.305 / 0.297 |
| 20 | (iii) hypothesis table: band fact → generic premise → band discharge → BA source | `\|E\|≤2−κ`, `0<lam≤𝔡⁻¹`, `κ≤Im m` → inside `T2478_NewKLK/K2` (Flow-quantified, `∀ᶠ n`) → `stNewKLK_holds`, `ST_K2e_of_flow`, `hflow.2 n`, WO → T1-BA (row 17). `√κ/2 ≤ Im m` → `DecayGen_Spec` → `DecayGen_bandSpec` → `EMn2BA_mF_data`, κm=κ. `flow_im_pos`, `lemT<1`, Admissible → `Step2EventsGen_Flow` → `Step2EventsGen_bandFlow` → `baStep2Data.flowOK_T/_adm`. `ST_pathP_eq_seqP`, LM/GMM links → `Step2EventsGen_Grid` → `_bandGrid` → `Step2EventsGenTw_baGrid`. `pathH_isHermitian` → inline premise → itself → `baStep2Mat_Hpath`, `PsiI_isHermitian`. `ST_Bdata_holds` → `STBdatagL` → `bandFM_STBdata` → T1-BA. `KLK_one` → `T2478_OneLoop` → `ST_Kloop_one`, `ST_Lloop_one_false` → `baKsol_one`. `stGridMart_of_repN` → `STGridMartgL` → `bandStep2_STGridMart` → `baGridMart_holds`. `stNetLift2/ScaleExists/LocalAvgOfL2/OptL2` → their `…gL` pins → `bandFM_*` → P2, P3, T1-BA (target 9), target 8 at BA | | no field without a band discharge |
| 21 | (v) site-1 obligations (`T2379-design:73`) | ev1 weak law ← `STStep1WeakgL` (`ST_event_weakg`); ev2 initial ← `STDecaygL` (`ST_event_initg`); ev3 LW ← `STLWTgL` (`ST_event_lwg`); ev4 QV ← `STEMn2ExpgL`, **Ĵ form** (`ST_event_mgg`); Good ← `ST_good_probg`; ident, martTail ← clauses 1, 3 of `STGridMartAtgL`; pLWT, pEMe ← `STLWTgL`, `STEMn2ExpgL`; pNew ← `T2478_NewKLK`; flowOK_m ← `DecayGen_Spec`. BA: ev1, ev2 are binders of `STStep2G` itself; ev3/pLWT `BASTLWT`; ev4/pEMe `baSTEMn2Exp`; ident/martTail `baGridMart_holds`; pNew row 17; flowOK_m `EMn2BA_mF_data` | Grönwall at `J:=Ĵ` suffices: `STEMn2ExpgL` is the Ĵ form, the stopped bootstrap is pathwise in Ĵ | no step needs a deterministic `J` (no T1-BA twin) |
| 22 | (iv) copy table and `open private` | band→generic map: `Lloop sz n (E n)`→`Cm.L n`, `STKloop`→`Cm.K`, `STLKM/STGMM/STEGtM/STEEM/STJhatM/STgA/STgDrift/STstopIdx`→`…g Cm`, `pathP/pathH`→`Cm.Pp/Cm.Hpath`, `mE (E n)`→`Cm.m n`, `etaT`→`Cm.eta`, `lemT (z n)`→`T0`, `STFlow`→`Flow`, `√κ/2`→`κm`, `STNewKLKAt`→`T2478_NewKLKAtN`, `ST_good_prob/ST_event_*/ST_LW_sections`→T7b `…g`. Sources: P4 `Step2Core:997-1312`; T3 `Step2Iterate:56, 85-263, 276-669, 700-723`; T4 `725-781, 924-1000, 1316-1373`; T5 `1261-1275`; T6 `1393-1480`; T7 `OptL2a:51-146, 283-542, 758-904, 983-1419`; T8 `OptL2b:101-176, 195-316`; T10 `Step2Iterate:1586-1721` | `open private` list: empty (`Step2Iterate`, `OptL2b`: no `private`; `OptL2a`: only `:1436`, an instance helper; `Step2Core:997-1312`: none; every helper named in these proofs, e.g. `ST_hcard`, `ST_bP_lower`, `ST_hsmall_aux`, `ST_final_cmp`, is public) | G1: no band file edit needed |
| 23 | (x) premise scan and registry | Prop binders of the public results: `T2478_NewKLK/K2/OneLoop/ListLink` and `STBdatagL`, `STScaleExistsgL`, `STGridMartgL`, `STNetLift2gL`, `STLocalAvgOfL2gL`, `STLWTgL`, `STLWBgL`, `STEMn2PolygL`, `STEMn2ExpgL`, F1-F3/F9 (all concluded by a merged or target-1/6 band reading), `STOptL2gL` (concluded by target 8) | lines kept: `:147, :199, :200, :219, :223` (BA forms owed: T1-BA); text-only rewrite of `:195-196` (answer (6)) | no new registry line expected |
| 24 | layering (`cone.py`) | no `RBM3D.BA.*` module in any cone (output below); `Step2CloseGen` without 9 needs `LocalAvg2` only (no `FarEntry`, no `CltGen`) | `grep '^import RBM3D.BA'` empty | cones 106 / 113 / 137 modules |

### (ii) One concrete nondegenerate instance
Data: `sz0` at `n=100` (`RBM3D/Defs/Sizes.lean:260`, the instance of `Step2Core:1314-1771`): d=3, L=404, W=202^5, lam=202^{−6}, N=(WL)^3; E=0 (m=i); κ=ε=𝔡=1/10, 𝔠=1/6; s=0, t=1/16, K=16 (Δ=1/256), D=1/2, Λ=C=1, q=1/10; target 9 at τ=0.3. All numeric hypotheses of targets 2-4, 6-9 hold at once (rows 1-3, 7-12 are the printed checks); the pins (`STLWTgL`, `STGridMartgL`, …) and the good event stay hypotheses of the instance (other gates' outputs); the eventual constants of rows 4, 12 are `∀ᶠ n` thresholds, not part of the instance.
```
$ S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2478
$ python3 $S/instance.py; python3 $S/lines.py; python3 $S/gfsem.py; python3 $S/cone.py
sz0 n=100: d=3 L=404 W=202^5=3.363e+11 lam=202^-6=1.47e-14 N=(WL)^3=2.509e+42; kappa=eps=0.1 dd=0.1 E=0 (m=i, Im m=1) s=0.0 t=0.0625 K=16 C=Lam=1 q=1/10
Admissible: WO True (W^(-1.4)=1e-16.14 <= lam=1e-13.83 <= 10), Bandwidth(1/6) True (N^(1/6)=1.17e+07 <= W), ln W/ln N=0.2719; F3 kappam=0.1581 <= Im m=1: True; |E|<=2-kappa: True
Cd=3C+1=4 cd=0.004167 Cd*cd=0.016667 (<=1/60=0.016667); Bctl(s)=2.63e-35 Bctl(t)=2.80e-35; ConStInd Bctl(t)^cd=0.7178 <= (1-t)/(1-s)=0.9375
hq r^Cd b^(1/5)/b^(1/6) worst 0.091 (<=1); P4 hsmall worst 0.598 (<1) over the 17 grid times; OptL2b: C0=2C=2 c0=1/(8C0+10)=0.03846 >= cd; cd*C0=0.0083<=1, cd*(C0+5/4)=0.0135<=1/4
Bdata: cB=1.000000, c=0.8149 (Bctl<=N^-c); target 3 eventual: eps1=min(tau/6,c/400), slack c/60-3eps1=0.00747, log10 N must exceed 324 (as in the band proof)
T9: tau=0.3 tau1=0.075 eps0=0.3056: log10 Phi=-15.70 <= log10 W^-eps0=-3.52: True; Psi=W^(-d/2) <= W^-eps0: True
    shift lemma max STWB(K')/STWB(K)/(j+1)^(d-2) = 1.0000 (<=1, 20000 samples, K<=K'+j); S_inf(c'=1)=356.0; M=sup(x+1)^(d-2)e^(-2c'x)=1.000
    W^-2D floor: D=18: log10 -415 <= log10 STWB-lower -37.2: True; C2=3(S^4+M/cB+1)=4.82e+10 <= N^(tau/4)=1.51e+03: False -> eventual, log10 N >= 142; 2tau2+tau1+tau/4=0.3
(vi) R1: g0=sqrt(t0) g, t0=kappa/(kappa+1), A=11: g0^2<=g^2: True, g^2<=A g0^2: True; ell_g=50, W=1e11, D=10, tailW at l=L:
     L=1e+03: sup P_g0/P_g = 10.956 (<=A)   sup P_g/P_g0 = 3.599e+00
     L=1e+04: sup P_g0/P_g = 10.956 (<=A)   sup P_g/P_g0 = 1.009e+04
     L=1e+05: sup P_g0/P_g = 10.956 (<=A)   sup P_g/P_g0 = 8.112e+14
     L=1e+06: sup P_g0/P_g = 10.956 (<=A)   sup P_g/P_g0 = 3.813e+48
band spans (decl+docstring): Step2IterGen 909, Step2IterGen2 308, OptL2Gen 1026, Step2CloseGen(12.2) 126; factor 0.88 (T2453 683/778), instances x0.6
central lines: Step2IterGen 1115, Step2IterGen2 471, OptL2Gen 1098, Step2CloseGen 281; target 9 itemised 525 (ticket cap 300)
T1a (targets 1-6) 1586; T1b without 9 1379, with 9 1904; row 2965 without 9, 3490 with 9; ticket 1550/1300/2850; split 1,950 fires: True; each half <= 1,950: True; REQ line 3,900: False
2.6x ticket central: T1a 4030 T1b 3380 row 7410; 2.6x own central: Step2IterGen 2899 OptL2Gen 2854 (stop line 2,000; reserve line 1,800 on central: False)
restated spans: 2269 code lines; band-token-bearing lines 442  -> proxy g = 0.195  (fire above 0.50)
f_sem (declarations naming a star-tree / K closed form: KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|couplingLen|KLtree|treeEq|KLK_two|KLK_one|KLmaxDist|STKloop_two|star.?tree) = 8/3161 = 0.003   (fire above 0.30)
raw lines naming KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|couplingLen, three files + Step2Core: Step2Iterate.lean:0 OptL2a.lean:0 OptL2b.lean:0 Step2Core.lean:0 
cones (transitive imports): Step2IterGen: 106 modules, 84293 lines, RBM3D.BA.* modules: 0; OptL2Gen: 113 modules, 91507 lines, RBM3D.BA.* modules: 0; Step2CloseGen (T10, T11): 137 modules, 120842 lines, RBM3D.BA.* modules: 0; +FarEntry,CltGen (if target 9 stayed): 148 modules, 131053 lines, RBM3D.BA.* modules: 0
```
Script notes: `instance.py` evaluates `Bparam`, `Bctl`, `STWB`, `tailT`, `tailW`, `ellT` exactly as defined in `Defs/Params.lean:32-38`, `Defs/Tail.lean:44-60`, `Defs/Sizes.lean:214`, `Induction/Defs.lean:69`; the (vi) rows evaluate `tailW` at `ℓ=L` over `r ∈ L·{0, 1e-4, …, 1}`. `lines.py` takes the declaration spans (with docstrings) from the band files by name; `gfsem.py` counts the token-bearing lines of the same spans.

### Verdicts
- T1 (classes `NewKLKAtN/NewKLK/K2/OneLoop`): **PASS**. K2 at BA follows from R1 (forward); NewKLK at BA follows from R1 only through F7 (rows 13, 14, 17), so UBA-C1 is not triggered, but the T1-BA plan "`stNewKLKgL'_ba` at `sz.withLam g₀` with `STprof(g₀) ≤ A·STprof(sz)`" must be changed as in row 17 (the Ĵ-form does not transport).
- T2 (P4), T3, T4, T5, T6, T7, T8, T10, T11, T12: **PASS** (every exponent closes, rows 1-9; no false statement, no hypothesis set that cannot hold; G1 by construction, `open private` list empty).
- T9: **PASS** on the mathematics (row 18); placement decision: itemised cost 525 (400/740) > 300, so it moves to T1-BA as a BA-only primed reader (the band needs none: `stLocalAvgOfL2_holds` is merged in place). Observation: if the dispatcher keeps it generic the half stays within 1,950 (1,904).
- Split: confirmed at the file boundary, T1a = `Step2IterGen` + `Step2IterGen2` (targets 1-6), T1b = `OptL2Gen` + `Step2CloseGen` (targets 7, 8, 10, 11; `Step2CloseGen` is 281 lines without 9 and could be folded into `OptL2Gen`, 1,379 < 1,800, if the dispatcher prefers).

## (a′) Preflight corrections — Mon Oct 12 23:41:17 UTC 2026
Author: claude-opus-5-5 (the one rule-(B) repair of the 1a-audit RETURN, `docs/reports/T2478-1a-audit.md` §6 "Required for resubmission" 1-3). Section (a) above is not edited; the entries below supersede the lines they name. No Lean is written in this repair.

1. **Target 9: go.** Target 9 stays in this ticket, in `RBM3D/Chain/Step2CloseGen.lean` (T1b), with pins `T2478_LocalReaderDec` (`stStep2LocalPT_of_L2decayDecG`) and `T2478_LocalAvgOfL2Dec` (`stLocalAvgOfL2_holdsDecG`), ticket `:38`. Reason: dispatcher answer (3) (ticket `:72`, DECISIONS §279) is binding. It makes one condition the only fallback trigger: "if the 1a finds that `STGijDecgL` plus `(eq:Psirelations)` does not close the local bound". Row 18 closes the argument from merged names (verdict "T9: PASS on the mathematics", line 66), so the fallback does not apply. The 300-line cap of ticket `:38` is not a trigger under answer (3); the itemised 525 (400/740, row 16) is a line estimate only. Struck:
   - line 4: "so by the ticket's rule it moves to T1-BA (no RETURN; row 18)";
   - line 26 (row 18, last column): "decision: lines 525 > 300, so the target moves to T1-BA";
   - line 66: "placement decision: itemised cost 525 (400/740) > 300, so it moves to T1-BA as a BA-only primed reader (the band needs none: …). Observation: if the dispatcher keeps it generic …".
   Line 66 now reads: T9 **PASS**, go, generic reader in T1b (one reader for both models, answer (3)). The BA reading of target 9 stays in T1-BA (ticket `:43`).
2. **Split (pre-signed, ticket `:10`, answer (1)):** T1a = `Step2IterGen` + `Step2IterGen2` (targets 1-6, central 1,586) / T1b = `OptL2Gen` + `Step2CloseGen` (**targets 7-11**, central 1,904 with target 9; `Step2CloseGen` 281 + 525 = 806). Row 3,490 < 3,900 (no third row, no REQ). Each half ≤ 1,950; no file above the 1,800 reserve on central (max `Step2IterGen` 1,115); stop line 2,000 not hit. Struck:
   - line 4: "T1b = targets 7, 8, 10, 11 (1,379; 1,904 if 9 stayed)";
   - line 67: "(targets 7, 8, 10, 11; `Step2CloseGen` is 281 lines without 9 and could be folded into `OptL2Gen`, 1,379 < 1,800, if the dispatcher prefers)", the folding remark included.
   Line 67 now reads: split confirmed, T1a = targets 1-6 / T1b = targets 7-11 (T1b stacked on `t/T2478`, merged after T1a). The row 15 figures stand, with "with 9" as the plan.
3. **Layering of T1b with target 9:** as the ticket layout says (`:14`), `Step2CloseGen` imports `Step2IterGen2`, `OptL2Gen`, `Induction/LocalAvg2` and `Evolution/FarEntry`, which imports `Chain/CltGen`. This supersedes row 24's "`Step2CloseGen` without 9 needs `LocalAvg2` only (no `FarEntry`, no `CltGen`)". Cone: 148 modules, `RBM3D.BA.*` modules 0 (line 59; reprinted below).

```
$ S=<scratchpad>/T2478; python3 -I $S/lines.py | grep -E "central lines|^T1a"
central lines: Step2IterGen 1115, Step2IterGen2 471, OptL2Gen 1098, Step2CloseGen 281; target 9 itemised 525 (ticket cap 300)
T1a (targets 1-6) 1586; T1b without 9 1379, with 9 1904; row 2965 without 9, 3490 with 9; ticket 1550/1300/2850; split 1,950 fires: True; each half <= 1,950: True; REQ line 3,900: False
$ python3 -I $S/cone.py | tr ';' '\n' | grep -E "Step2CloseGen|FarEntry"
 Step2CloseGen (T10, T11): 137 modules, 120842 lines, RBM3D.BA.* modules: 0
 +FarEntry,CltGen (if target 9 stayed): 148 modules, 131053 lines, RBM3D.BA.* modules: 0
$ grep -n "^import" RBM3D/Evolution/FarEntry.lean | grep CltGen
12:import RBM3D.Chain.CltGen
$ python3 -I -c 'print(281+525, 1379+525, 1586+1904)'
806 1904 3490
```

## (b) Script output, T1a = targets 1-6 — Tue Oct 13 00:30:49 UTC 2026
T1a = `RBM3D/Chain/Step2IterGen.lean` + `RBM3D/Chain/Step2IterGen2.lean` (targets 1-6) and `RBM3D/Test/Axioms.lean` (TLC-2 owner texts, one registry line). Targets 7-11 (T1b, incl. target 9) are not touched: they run on a branch stacked on `t/T2478`, report `T2478b-prove.md`. Branch `t/T2478`, worktree `RBM3D-wt/T2478`, HEAD `1f0c2b4e`, merge-base with `main` `2dcfcda5`. Ports: from RBM3D band files `Induction/Step2Iterate.lean`, `Induction/Step2Core.lean` only (same repository, not edited); nothing from RBM1D/RBM2D, so no RBM1D/RBM2D diff-stat.

### (1) Lines per file against the stop line (CONTROL H134: `wc -l` at every section commit; stop 2,000 per file; reserve 1,800)
```
$ for h in $(git log --format=%h 2dcfcda5..HEAD --reverse); do wc -l of the two files at $h; done
f57c3738  436    0  T2478: Step2IterGen section 1-2 (classes, P4 ST_good_engineg)
2b84487f 1075    0  T2478: Step2IterGen target 3 (STSelfImpgL, ST_nextg, ST_decay_of_final
3261f6fd 1075  366  T2478: Step2IterGen2 targets 4-6 (iteration, per-time outputs, avgU, s
0fb5fecd 1222  366  T2478: Step2IterGen newKLKAtN band discharge, instances for targets 1-
d8fc9ec7 1222  512  T2478: Step2IterGen2 band readings, band re-derivation, instances for
29558bac 1223  518  T2478: STGridMartgL premise, inline avg/concl premises, STOptL2gL regi
48452365 1263  538  T2478: band re-derivation examples for targets 2-4
1f0c2b4e 1263  538  T2478: Step2IterGen2 docstring (TN-C4 grep)
$ wc -l RBM3D/Chain/Step2IterGen.lean RBM3D/Chain/Step2IterGen2.lean
    1263 RBM3D/Chain/Step2IterGen.lean
     538 RBM3D/Chain/Step2IterGen2.lean
    1801 total
```
No file reaches the stop line; no reserve hand-over. Split: T1a 1,801 lines (a: central 1,586), as pre-signed and confirmed by the 1a-audit (a′ 2).

### (2) Build, axioms, premise scan, layout
```
$ lake build RBM3D.Chain.Step2IterGen RBM3D.Chain.Step2IterGen2 2>&1 | tail -1
Build completed successfully (3812 jobs).
$ lake env lean <scratch>/lean/axioms.lean     # #print axioms of all 26 `theorem`/`def` of the two files
  26 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^private axiom" RBM3D/Chain/Step2IterGen*.lean | wc -l
0
$ lake env lean <scratch>/lean/scan.lean       # import RBM3D; import RBM3D.Chain.Step2IterGen; import RBM3D.Chain.Step2IterGen2; #assert_rbm_axioms
axiom audit: 14110 theorems, 4457 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 128 (borrowed 1, owed 62, structural 45, refuted 6, superseded 14).
registry: 2 borrowed + 107 owed + 122 structural + 7 refuted + 18 superseded; 128 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -n '^import RBM3D.BA' RBM3D/Chain/Step2IterGen*.lean | wc -l
0
$ grep -rn "^import RBM3D.Chain.Step2IterGen" RBM3D RBM3D.lean
RBM3D/Chain/Step2IterGen2.lean:6:import RBM3D.Chain.Step2IterGen
$ cone (transitive `import RBM3D.*` of the branch files)
RBM3D.Chain.Step2IterGen 110 modules 89165 lines; RBM3D.BA.* modules: 0 ; NewKLK in cone: True
RBM3D.Chain.Step2IterGen2 111 modules 89704 lines; RBM3D.BA.* modules: 0 ; NewKLK in cone: True
$ git diff main...t/T2478 --stat
 RBM3D/Chain/Step2IterGen.lean  | 1263 +++++...
 RBM3D/Chain/Step2IterGen2.lean |  538 +++++...
 RBM3D/Test/Axioms.lean         |    6 +-
 3 files changed, 1805 insertions(+), 2 deletions(-)
$ git diff main...t/T2478 --stat -- RBM3D/Induction RBM3D/Path RBM3D/Evolution RBM3D/BA RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/Carrier.lean 'RBM3D/Chain/DecayGen*.lean' 'RBM3D/Chain/Step2EventsGen*.lean' RBM3D/Chain/NewKLKGen.lean RBM3D/Chain/CltGen.lean | wc -l
0
```
`RBM3D.lean` is not edited (root imports are the hub's step at merge, CLAUDE.md §3 (A)4): the two lines to add after the last `import` are `import RBM3D.Chain.Step2IterGen` and `import RBM3D.Chain.Step2IterGen2`; `scan.lean` is the same check with those imports. `Step2IterGen` imports `Chain/Step2EventsGen`, `Induction/Step2Iterate` and, in addition to the ticket line 13, `Induction/NewKLK` (for `stNewKLK_holds`, the band discharge of target 1); `Induction/NewKLK` is not a `BA/*` module.

### (3) Statements against the pins (script diff by compilation)
`<scratch>/lean/audit.lean` = the Part 2 definitions of `docs/tickets/checks/T2478-check.lean` (`T2478_*`, copied by script) + the block below; it imports only the two new modules (and `OptL2b`, `LocalAvg2`, `FarEntry` for the check-file imports).
```
$ lake env lean <scratch>/lean/audit.lean 2>&1 | grep -c error
0
example ... : T2478_NewKLKAtN Cm n C δ₀ ↔ Step2IterGen_NewKLKAtN Cm n C δ₀ := Iff.rfl
example ... : T2478_NewKLK d Flow mk ↔ Step2IterGen_NewKLK d Flow mk := Iff.rfl
example ... : T2478_K2 d Flow mk ↔ Step2IterGen_K2 d Flow mk := Iff.rfl
example ... : T2478_OneLoop C ↔ Step2IterGen_OneLoop C := Iff.rfl
example : T2478_GoodEngineg := @ST_good_engineg
example ... : T2478_SelfImpgL C μ Cd s t Kf ↔ STSelfImpgL C μ Cd s t Kf := Iff.rfl
example : T2478_Step2OfPinsg := @ST_step2_of_pinsg
example ... : STSelfImp sz Cd E s t Kf ↔ T2478_SelfImpgL (bandFM sz E) (Sizes.seqP sz) Cd s t Kf := Iff.rfl
```
Declarations of targets 1-6 (file:line of the `def`/`theorem`):
```
T1 Step2IterGen.lean: NewKLKAtN 50, NewKLK 63, K2 71, OneLoop 81, newKLKAtN_band 104, newKLK_band 115, K2_band 124, oneLoop_band 129
T2 Step2IterGen.lean: ST_good_engineg 143
T3 Step2IterGen.lean: STSelfImpgL 447, bandFM_STSelfImp 456, ST_nextg 474, ST_decay_of_finalg 582, ST_selfImprove_sectiong 663, ST_selfImproveg 1056
T4 Step2IterGen2.lean: ST_iterateg 45, ST_decay_ptg 72, ST_L2_decay_ptg 105, ST_base_invg 184
T5 Step2IterGen2.lean: ST_avgU_of_avgg 266, ST_concl_of_step2g 281
T6 Step2IterGen2.lean: ST_step2_of_pinsg 299, stBdatagL_band 377, stScaleExistsgL_band 383, step2IterGen_step2_of_pins_band 394
```

### (4) Compiled nonempty instances and band re-derivations (CLAUDE.md §4 step 2)
24 `example`s in the two files (`grep -c "^example"`), data `d = 3`, `sz0`, `z0`, `flow_z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, window `[0, 1/16]` (the engine at `n = 100`, `E = 0`, `K ≡ 16`). Discharged: F1-F3, F9, the Hermitian walk, size data (`bdata_spec`), `hK2_sz0`, `hq_sz0`, `Kseq0_adm`, `conStInd_inst`, the target-1 classes by their band discharges. Left as hypotheses (another gate's pin or a stochastic premise): `STLWTgL`, `STEMn2ExpgL`, `STGridMartgL`, `STOptL2gL`, `STLocalAvgOfL2gL`, `STDecaygL`, `STStep1WeakgL`, `STScaleInvgL`, `STSelfImpgL`, `Step2IterGen_NewKLKAtN` at `C = 1`, `STGoodAtg`.
```
Step2IterGen.lean  target 1: ∃ C δ₀, … ∀ᶠ n, Step2IterGen_NewKLKAtN (bandStep2Mat sz0 (STflowE z0)) n C δ₀   (from step2IterGen_newKLK_band 3 at flow_z0)
                   target 1: ∃ C_K, … ‖(bandStep2Mat sz0 (STflowE z0)).K n u σ a‖ ≤ C_K * STprof …  (step2IterGen_K2_band 3);  Step2IterGen_OneLoop (bandFM sz0 (STflowE z0))
                   target 2: ST_good_engineg sz0 (bandStep2Mat sz0 (fun _ => 0)) sI tI KI 100 (1/2) (fun _ _ => 1) (√(1/10)/2) 1 δ₀ 1 a0 a0 (a0^2) (1/10) …   (line 1115)
                   target 3: ST_nextg, ST_decay_of_finalg, ST_selfImprove_sectiong (tt ≡ 1/32, D = 1, C = 1, δ₀ = 1/10, 𝔠d = 1/240), ST_selfImproveg
                   band re-derivations: example : type_of% @RBM.Gauss.Sizes.{ST_good_engine, ST_selfImprove, ST_next, ST_decay_of_final}
Step2IterGen2.lean target 4: ST_iterateg, ST_decay_ptg, ST_L2_decay_ptg, ST_base_invg (Kseq0, hK2_sz0, hq_sz0);  target 5: ST_avgU_of_avgg, ST_concl_of_step2g
                   target 6: ST_step2_of_pinsg 3 (fun sz => seqP sz) STFlow (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) … specialised to (sz0, z0, s ≡ 0, t ≡ 1/16)
                   band re-derivations: type_of% @RBM.Gauss.Sizes.{ST_iterate, ST_decay_pt, ST_L2_decay_pt, ST_base_inv}; step2IterGen_step2_of_pins_band 3 (+ inst_step2)
```
`open private` list: proofs: empty (as a: row 22). Instances only, from `RBM3D.Induction.Step2Core` (precedent `Chain/Step2EventsGen.lean`): `sI tI KI lam_pos one_le_L100 core_small r_bounds gt_eq gt_le Bctl_small a0 a0_nonneg mE_zero_im`.

### (5) Hypothesis and bridge table as used, site-1 table, J decision
| premise of `ST_step2_of_pinsg` | band discharge (this file) | BA source (shape only; a: row 20) |
|---|---|---|
| F1-F2 `Step2EventsGen_Flow` | `Step2EventsGen_bandFlow` | `baStep2Data.flowOK_T/_adm` |
| F9 `Step2EventsGen_Grid`, Hermitian walk | `Step2EventsGen_bandGrid`, `pathH_isHermitian` | `Step2EventsGenTw_baGrid`, `baStep2Mat_Hpath` |
| F3 `DecayGen_Spec` | `DecayGen_bandSpec` (κm = √κ/2) | `EMn2BA_mF_data` (κm = κ) |
| `Step2IterGen_OneLoop`, `_NewKLK`, `_K2` | `step2IterGen_oneLoop_band`, `_newKLK_band`, `_K2_band` | `baKsol_one`; T1-BA (a: rows 13, 14, 17) |
| `STBdatagL`, `STScaleExistsgL`, `STNetLift2gL` | `stBdatagL_band`, `stScaleExistsgL_band`, `stNetLift2_holds` | T1-BA, P3, `baNetLift2_holds` (P2) |
| `STGridMartgL` | pin; `bandStep2_STGridMart` | `baGridMart_holds` |
| `STLWTgL`, `STEMn2ExpgL` (Ĵ form) | pins; `bandFM_STLWT`, `bandFM_STEMn2Exp` | `BASTLWT`, `baSTEMn2Exp` |
| `STOptL2gL`, `STLocalAvgOfL2gL` | pins; `bandFM_STOptL2`, `bandFM_STLocalAvgOfL2` | T1b targets 8, 9; T1-BA |

Site-1 obligations (T2379 `:73`) inside `ST_selfImprove_sectiong` (`Step2IterGen.lean`):
```
$ grep -nE "obtain ⟨C₀|obtain ⟨Mart, Rem, hident|have hE[1-4] :=|have hgp :=|hmart0|hnewn hKf0|Step2EventsGen_model_le_path" RBM3D/Chain/Step2IterGen.lean
688 obtain ⟨C₀, hC₀, hmart⟩ := hmart            (ident, martTail: clauses 1, 3 of STGridMartAtgL, from the premise STGridMartgL)
735 obtain ⟨Mart, Rem, hident, hrem0, hmart0⟩    789 hE1 := ST_event_weakg … hS1W (ev1)   823 hE2 := ST_event_initg … hDec (ev2)
826 hE3 := ST_event_lwg … hLWT hEMe … hSpec (ev3; pLWT, flowOK_m)    828 hE4 := ST_event_mgg … hLWT hEMe … hSpec (ev4; pEMe, flowOK_m)
867 hgp := ST_good_probg … hE1 hE2 hE3 hE4 … hident (Good)   869 (hmart0 ε₁ hε₁pos)   942 hmodel := Step2EventsGen_model_le_path   995 … hnewn hKf0 … (pNew)
```
J decision: the Grönwall at `J := Ĵ` suffices. `ST_selfImprove_sectiong` takes `STEMn2ExpgL` (the Ĵ form) and no deterministic `J`; it compiles with the Ĵ-form event `ST_event_mgg` and the engine bound on `STJhatMg`. No step needs a deterministic `J` (no T1-BA twin).

### (6) Tripwire (C6/I1: fire if `g > 0.5` or `f_sem > 0.30`)
```
$ python3 -I gfsem.py     # the 1a script, band files unchanged
restated spans: 2269 code lines; band-token-bearing lines 442  -> proxy g = 0.195  (fire above 0.50)
f_sem (declarations naming a star-tree / K closed form: …) = 8/3161 = 0.003   (fire above 0.30)
$ grep -c -E 'KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|couplingLen|KLtree|treeEq|KLK_two|KLmaxDist|STKloop_two' RBM3D/Chain/Step2IterGen.lean RBM3D/Chain/Step2IterGen2.lean
Step2IterGen2.lean:0   Step2IterGen.lean:0
```
Not fired. No step of the port used a star-tree or `K` closed form.

### (7) Target 9
Not in T1a. Per (a′) 1 it is `go` (generic reader in T1b, `Step2CloseGen`, report `T2478b-prove.md`).

### (8) Greps
```
$ X1-C1: grep -nE "\bmE\b|zt E|zt \(|2 - κ|\|E\||etaT|lemT|STFlow|STflowE|mSigma|Lloop|STKloop|KLK d|ThetaN d|Ugen|uKer d|pathP sz|pathH sz|seqHflow|seqP|withLam|lam0|BAflowLam0|gK" (53 hits Step2IterGen, 65 Step2IterGen2)
  Step2IterGen.lean:   lines 80-133 docstrings and band discharges (flow_data, newKLKAtN_band, newKLK_band, K2_band, oneLoop_band), 457 band bridge `bandFM_STSelfImp`, 1085-1257 instance prose and examples
  Step2IterGen2.lean:  312 = `(hNew : Step2IterGen_NewKLK d Flow mk)` (pattern `KLK d` false positive), 378 and 384 `stBdatagL_band`, `stScaleExistsgL_band`, 398-415 `step2IterGen_step2_of_pins_band`, 423-532 examples and `Step2IterGen2_inst_step2`
  no other hit: none in lines 134-456 and 458-1084 of Step2IterGen (generic statements and proofs) nor in 40-311 and 313-372 of Step2IterGen2.
$ grep -n "\.lam" RBM3D/Chain/Step2IterGen*.lean   # `sz.lam n` only in tailT/ellT/Bparam arguments, in `0 ≤ sz.lam n` (target 2, line 146) and in the band-only lines 95, 105
$ U-C4: grep -nE "^(noncomputable )?def" RBM3D/Chain/Step2IterGen*.lean
  Step2IterGen.lean:50 Step2IterGen_NewKLKAtN, :63 Step2IterGen_NewKLK, :71 Step2IterGen_K2, :81 Step2IterGen_OneLoop, :447 STSelfImpgL   (all `: Prop`; no matrix- or tensor-valued kernel)
$ TN-C4: grep -nE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" RBM3D/Chain/Step2IterGen*.lean | wc -l
0
$ UBA-C1: grep -nE "gK|BAflowLam0|withLam|lam0" RBM3D/Chain/Step2IterGen*.lean | wc -l
0
$ name clash: git grep -l -w -E "<the 29 new names>" <ref> -- RBM3D RBM3D.lean   for main (d34419a0) and the 482 local branches t/* except t/T2478
refs scanned: 483, Lean files with a hit: 0
```

### Narrative (facts of the files and the tool log)
1. All six targets are delivered as generic results over `Cm : Step2Mat sz` / `C : FlowFM sz` and a law `μ`; the proofs are ports of `Step2Iterate:56-1013, 1261-1289, 1316-1480` and `Step2Core:997-1295` with the substitutions of (a) row 22. The skeleton `ST_step2_of_pinsg` is `T2478_Step2OfPinsg` (compiled `@ST_step2_of_pinsg`); its only grid premise is `STGridMartgL`.
2. Differences from the ticket text (not from a pin): (i) `ST_selfImprove_sectiong`, `ST_selfImproveg` take `STGridMartgL d Flow mk T0` and take `C₀` inside, instead of `STGridMartAtgL d C₀ …`, because `STGridMartAtgL` has no concluding theorem and would need a registry line; (ii) `ST_avgU_of_avgg` and `ST_concl_of_step2g` state their hypotheses as the unfolded `STStep2AvggL` (`PrecL …`), `STLocalEntryUgL` (`= STStep2LocalgL`), `STGdecayWgL … Cd` (`= STStep2DecaygL`) for the same reason; the examples apply them to the named forms (definitional); (iii) `ST_avgU_of_avgg` has the window premises `0 ≤ s n`, `t n < 1`, because the pinned `Step2IterGen_OneLoop` states `𝒦^{(1)} = m(σ)` for `0 ≤ u < 1` only; the band `ST_avgU_of_avg` has no window, so it is not re-derived (the ticket lists no band re-derivation for target 5).
3. `Test/Axioms.lean`: the owner texts of `BATwistAvgLaw`, `BATwistLoopLaw` are rewritten to the dispatcher's wording (answer (6)); they are at lines 192-193 of this branch (the ticket says `:195-196`). One registry line is added, `STOptL2gL` (hypothesis of `ST_step2_of_pinsg`, concluded by `stOptL2_of_pinsg` in T1b, which removes the line). The registered lines `STStep2DecayPTgL`, `STScaleInvgL` now sit among "registered premise(s) carry nothing yet" (their generic proofs `ST_decay_ptg`, `ST_nextg` are here; BA forms stay T1-BA); `STGoodAtg` stays (the event is assumed).
4. `set_option maxHeartbeats 3200000 in` is kept for `ST_selfImprove_sectiong` only (default 200000 times out, as the band); no other file-level option beyond the T7b set.
5. T1b may use: `Step2IterGen_NewKLK`, `step2IterGen_newKLK_band`, `step2IterGen_newKLKAtN_band` (for `stOptL2_of_pinsg`, target 1 band), `ST_step2_of_pinsg`, `step2IterGen_step2_of_pins_band`.

## (c) Verified names (all by compilation in this branch)
- Lean core: `type_of%` (elaborator; precedent `RBM3D/Induction/LoopGenN.lean`), `open private … from` (Mathlib command; precedent `Chain/Step2EventsGen.lean`).
- Mathlib: `Filter.Eventually.of_forall`, `Filter.eventually_ge_atTop`, `MeasureTheory.measure_mono`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Complex.norm_conj`, `map_sub`, `Finset.le_sup'`, `lt_of_mul_lt_mul_right`, `inv_le_one_of_one_le₀`, `one_le_pow₀` (all used by the ported proofs).
- RBM names used and not in the ticket's list: `RBM.StochDomAt.{add, of_le_left, of_subset, trans, refl, const_mul_left, precomp_param}` (namespace `RBM`, not `RBM.Gauss`), `Step2EventsGen_prec_dom`, `Step2EventsGen_STJhatMg_measurable`, `Step2EventsGen_STLKMg_eq`, `stNewKLK_holds` (in `Induction/NewKLK`, not in the cone of `Chain/Step2EventsGen` + `Induction/Step2Iterate`).
- Verified absent in the cone before the extra import: `RBM.Gauss.Sizes.stNewKLK_holds` (unknown constant with the two ticket imports only).

## (d) Open issues and paper-delta candidates
- **T2478a** (ticket note 8): the Step 2 iteration over the carrier, with `lem:newKLK` (`Step2IterGen_NewKLK`, index-wise `Step2IterGen_NewKLKAtN`) and the `𝒦^{(2)}` decay (`Step2IterGen_K2`) as carrier inputs; the local bound from `STGijDecgL` is T1b.
- **T2478b** (candidate): `Step2IterGen_OneLoop` carries the window `0 ≤ u < 1`; the band `ST_Kloop_one` is for all `u`. A consumer that needs the one-loop value outside `[0, 1)` must use the band lemma.
- **T2478c** (candidate): `ST_selfImprove_sectiong`/`ST_selfImproveg` read `STGridMartgL` (constant `C₀` inside) and `ST_avgU_of_avgg`/`ST_concl_of_step2g` the unfolded premises (item 2 above); statement-level, not a paper difference.
- For the hub at merge: add the two root imports (item in (2)); T1b removes the `STOptL2gL` line when `stOptL2_of_pinsg` lands.
- For T1-BA: (a) rows 13, 14, 17 (the Ĵ-form conclusion of `stNewKLKgL'_ba` does not transport to `sz` under R1; the comparison holds through F7 of `NewKLKGenHyp`) are carried, not re-verified here.
