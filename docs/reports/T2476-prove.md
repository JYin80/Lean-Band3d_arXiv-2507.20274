Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 22:45:47 UTC 2026
Base: worktree `../RBM3D-wt/T2476` = `main` eaa247c4 (`git merge-base --is-ancestor 8ea70675 HEAD`: true). Scratch scripts `scratchpad/T2476/{pre.py,alg.py,cone.py,readers.py}`: plain Python, no Lean written. Scope: mathematics only; Lean statements are the check file's `T2476_*` shapes.
**Fill-in table (CONTROL H250 (4)).** Rows: item, report lines, status.
| item | where | status |
|---|---|---|
| (i) exponent table | L18 | done, all slacks >= 0 |
| (ii) instance + script + external-hypothesis limit check | L42 | done |
| (iii) two cones per file | L62 | done, no `LWExpCert*` |
| (iv) signature dump, out-of-file readers (G1 list) | L70 | baseline dumped; no public change planned |
| (v) private-lemma change table | L71 | 4 privates change, 4 callers |
| (vi) K-hypothesis table, `kappa_eff` | L79 | done |
| (vii) E1 transfer table, `open private` list | L88 | done (7 names) |
| (viii) predicted lines vs 2,000 / 1,800 / 1,950 | L96 | done |
| (ix) premise-scan preview, registry list | L97 | done, no new registry line |
| (x) `#print axioms band_terminal` / `bUniv_holds` on main | L98 | covered by `#assert_rbm_axioms` run; the literal prints are NOT taken at 1a (they need a Lean command; 1a writes none) -> probe step / auditor |
| D1 (bulk window, bad-event transfer, BA discharges) | L99 | math closes; compile = probe step `RBM3D/Probe/T2476Pins.lean` |
**(i) Exponent table** (d=3, nf=2, tau=1/4, (ca,dd)=(1/6,1/10) = `UNInst.sz0_adm`; `pre.py` sections A-D reproduce the numbers).
| quantity | value | constraint (source) | slack |
|---|---|---|---|
| ca*dd | 1/60 | <= 1/2 (`un_cd_le_half`, `Jak:451`) | 29/60 |
| c = 2 ca dd | 1/30 | 0<c<36 (`Jak_pointwise_good_norm`), c<=1 (`Uyw`) | 29/30 |
| c' = ca dd/30 | 1/1800 | c' <= c/36 (`*_good_total_le`) | c/36-c' = 1/2700 |
| tau (<= 1/4) | 1/4 | 0<tau, -1+2tau<0 (`h3`) | exponent -1+2tau = -1/2 |
| delta = tau/(nf+5) | 1/28 | (nf+3) delta <= tau (`hmδ`) | 2tau/(nf+5) = 1/14 |
| D_Jak / D_Uyw | 37/4 / 21/2 | D >= (1+tau)(nf+3)+3 / (nf+4)+3; crude exponent a+2-D = -1 | 0 (equality), needs 12(3+nf) <= X / 16(4+nf) <= X |
| K = 2d+1 (band), 1 (BA) | 7, 1 | BA `unBadYBA_measure_le` has no factor; 1 <= 7 | 6 |
| Jak target 1-c'+Cτ, C=3nf+16=22 | 11699/1800 | good a+b+e-1 <= T-6tau; bad a+b+f+g-1 <= T-6tau | good 10807/18900, bad tau-(nf+3)delta = 1/14 |
| Uyw target 2-c'+Cτ | 13499/1800 | good a+e-1 <= T-6tau; bad a+f-1-c' <= T-6tau | good 6757/18900, bad 2tau-(nf+2)delta = 5/14 |
| `h3`: C0/X + 2X^{-1+2tau} < kf/4 | X^{-1/2} | eventual | n=0: 1.38e-3 vs kf/4 = 0.125 (band) |
| `h4`: X^{-1+c/6} < kf/2 | X^{-179/180} | eventual | n=0: 5.2e-7 vs 0.25 |
| `h5` Jak: 3((193+128/kf²)+4K)(6+16/tau+8/kf) <= X^{6tau} | 1.89e5 (kf=1/2) | X^{3/2} | n=0: 3.0e9 (ratio 1.6e4) |
| `h5` Uyw: 2((193+256/kf²)+4K) <= X^{6tau} | 2490 (kf=1/2) | X^{3/2} | n=0: 3.0e9 |
| QUE params (eps0,c)=(dd/3,dd/6), tau_Q=dd/30 | 1/30, 1/60, 1/300 | eps0<dd/2, c<eps0, c<dd/5 | 1/60, 1/60, 1/300 |
| queBound exponent -2dd/5+dd/3+dd/30 | -dd/30 = -1/300 | = `Jak_queBound_eq` exponent | 0 (identity) |
| window `un_window_sub`: W^{-d/2+dd} <= lam | sz0 n=0: 1/128 <= 1/64 | (eq:WO), `hlam` | factor 2 |
| Bandwidth X^ca <= W | n=0: 11.3 <= 32 | `hWc` | factor 2.8 |
| EMCTE2: tau <= Cn tau, Cn=1, tau0=1 | equality | `unEMCTE2_of_sizeTendsto` | 0 (equality); (1/2)nf² = 2 <= N^eps eventual |
| band window kappa' = r = kappa/2 | kappa=1/2: 1/4 | kf = min(kappa,2,2r) = kappa; need kf/2 <= r; \|E\|<=2-kappa, \|e-E\|<=kappa/2 => \|e\|<=2-kappa/2 | 0 (equalities) |
| BA window kappa'=kappa/2, r=(pi kappa)^3/8 | kappa=0.1: r=0.003876 | kf=min(kappa,2,2r)=0.007752 (2r binds); kf/2 <= r | 0 (equality) |
| grid energies \|e-E\| < kf/2 | band max 0.1264 < 0.25; BA max 0.001945 < 0.003876 | C0/X + r_grid + 2eta < kf/2 | factor 2 |
**(ii) One concrete instance.** Command: `cd scratchpad/T2476 && python3 -I pre.py | grep -E "^A\.|^   Jak:|^   Uyw:|^B\.|^   BA kappa|band (J|U) n=0|BA   J n=(0|1)|BA   U n=0|failing|C0=1|^D\." | sed 's/ n: / /'` (`n` = row of `sz0`; `S0` = `clsSz 4 g0`). Output:
```
A. exponents: c=2cd=1/30 c'=cd/30=1/1800 delta=1/28 K=2d+1=7 C=3nf+16=22 D_Jak=37/4 D_Uyw=21/2
   Jak: target exponent 1-c'+C tau=11699/1800 ; good-part slack (T-6tau minus exponent)=10807/18900 ; bad-part slack=1/14 ; crude: exponent a+2-D=-1 exactly (needs 12(3+m)<=X)
   Uyw: target exponent 2-c'+C tau=13499/1800 ; good-part slack=6757/18900 ; bad-part slack=5/14 ; crude exponent -1 (needs 16(4+m)<=X)
B. window: band kappa'=r=kappa/2 -> kappa_eff=min(k,2,2r)=k (kappa<=2): [(0.1, 0.1), (0.5, 0.5), (1.0, 1.0), (2.0, 2.0)]
   BA kappa'=kappa/2, r=(pi k)^3/8 -> [(0.01, 4e-06, 8e-06), (0.05, 0.000484, 0.000969), (0.1, 0.003876, 0.007752), (0.3, 0.104646, 0.209292)]
   band J n=0 L=4 W=32 N=2.097e+06 lam=0.01562 kf=0.5 const_h5=1.891e+05 X^(6tau)=3.037e+09 -> all numeric hypotheses True
   band U n=0 L=4 W=32 N=2.097e+06 lam=0.01562 kf=0.5 const_h5=2490 X^(6tau)=3.037e+09 -> all numeric hypotheses True
   BA   J n=0 L=4 W=32 N=2.097e+06 lam=0.3 kf=0.0077516 const_h5=7.044e+09 X^(6tau)=3.037e+09 -> all numeric hypotheses False
      failing: ['h5 const<=X^(6tau)']
   BA   J n=1 L=4 W=1024 N=6.872e+10 lam=0.3 kf=0.0077516 const_h5=7.044e+09 X^(6tau)=1.801e+16 -> all numeric hypotheses True
   BA   U n=0 L=4 W=32 N=2.097e+06 lam=0.3 kf=0.0077516 const_h5=8.521e+06 X^(6tau)=3.037e+09 -> all numeric hypotheses True
   C0=1 at n=0 band (h2 needs X>=2^180): False  ; 2^180 = 1.53e+54
D. grid-energy window band n=0: max|e-E|=0.126355 < kf/2=0.25 : True
D. grid-energy window BA n=1: max|e-E|=0.00194547 < kf/2=0.00387578 : True
```
Data: band `UNKind.band 3`, `sz0` (`Defs/Sizes:260`), n=0, kappa=1/2, E=1, nf=2, tau in (0,1/4] (shown at 1/4), C0=1/2 (a window `\|z.re-E\| <= 1/(2N)`, `z = 1 + i/N` nonempty: `JakInst.inst_window`). C0=1 needs N >= 2^180 (`h2`): the pin's "eventually" is per C0, so the instance fixes C0=1/2. BA: `S0`, `(kappa_*, E_*, g0)` come from `exists_flowPt` (no closed form); stand-ins kappa=0.1, g0=0.3 show the BA arithmetic needs n>=1 for Jak (kf = 0.00775 raises `h5`; n=1: N=6.9e10 = (4·1024)³), nothing else changes with kappa>0. `UNOUQUEk`, `UNOUDiagk`, `UNLocAvgBA` stay hypotheses (owed pins; `Loc` unused by the proofs, as `jakRow:935` `_hloc`).
Algebra checks (`python3 alg.py`): `(1)` blockM2 at weights delta_{a0} = `u_a0`, `‖u‖>=W^{-dd/6}` iff `‖S-(W^d/N)δ‖ >= W^{d-dd/6}/N`: max deviation 2.2e-16, 0 mismatches of 576 pairs (W=2,d=3); `(2)` translation: d²/ds² Φ(A+M+sB) both ways 0.0418246771721 vs 0.041824677173.
External-hypothesis limit check (TEAM §8.14): QUE bound `W^{-dd/30} <= X^{-ca dd/30} = X^{-1/1800}` (`hWc`), times K=7; majorant exponents of Jak good/bad/crude parts are `T-6tau-slack` with slacks above, so each part is `O(X^{-slack} · X^{6tau})` against `X^{6tau}` absorbed by `h5`: limits agree, nothing vacuous; BA K=1 is the sharper (`unBadYBA_measure_le`).
**(iii) Cones** (condensed from `python3 -I cone.py . RBM3D.Universality.{Jak,JakSpectral,Uyw,EMCTE2}` and `RBM3D.BA.{EMCTE2BA,JakUywBA}` on the worktree; reverse cone size [members] | `LWExpCert*` in either cone | in `BandTerminal` closure).
```
Jak: 5 [BUniv,BUnivHolds,BandTerminal,UnivMain,Uyw] | none | yes     JakSpectral: 8 [+JakKernel,UywKernel,Jak] | none | yes
Uyw: 4 [BUniv,BUnivHolds,BandTerminal,UnivMain]     | none | yes     EMCTE2 (read only): 4 | none | yes
BA/EMCTE2BA, BA/JakUywBA (new): reverse 0 | forward closure of imports 104 modules, LWExpCert none, BandTerminal not imported
Jak/JakSpectral/Uyw forward closures contain no `RBM3D.BA.*` module (layering L1 holds); PinsK in forward closure of Jak/Uyw: False
```
Equal to the ticket table and GMN-F2.
**(iv) Signature baseline** (ticket's awk on `main`, files `sig-<f>-main.txt`, sha1 7b30439c / 40661814 / 9966be39 / 235795ae): public declarations Jak 7, JakSpectral 24, Uyw 7, EMCTE2 8; 0 indented public declarations. Planned diff: additions only, none in these four files (K-forms and instances live in the leaf). G1 names (`example : <old statement> := <old name>`, generated by the auditor from the dump): Jak `un_cd_le_half, unJak_of_ouClaims, jakRow, JakInst.{inst_row,inst_window,inst_unJak,inst_cd_le_half}`; Uyw `unUyw_of_ouClaims, uywRow, jakUywRow, UywInst.{inst_row,inst_uywRow,inst_unUyw,inst_window}`; JakSpectral all 24 (`spectralPole, spectralGsigPole, isOrthoEigenbasis_eigenvectorBasis, Gres_sq_apply_self, Gres_apply_self_spectral, Gres_sq_apply_self_spectral, spectralGsigPole_norm_eq_spectralPole, siteBlock, blockM, blockM_eq_unMy, blockM_eq, green_spectral_identity_blockM, norm_green_spectral_identity_blockM_le, sum_norm_blockM_le, unBadY_of_blockM, measure_bad_le_of_queBadMat, JakSpectralInst.*`). Readers outside the file (grep): `un_cd_le_half, unJak_of_ouClaims, jakRow` <- Uyw; `jakUywRow` <- UnivMain:622,652, Main/BUniv:49; `unEMCTE2Row` <- UnivMain:621, Main/BUniv:49; `unEMCTE2Rowk_band` <- UnivMain:651; JakSpectral names <- JakKernel, UywKernel, Jak, Uyw (`readers.py`). `blockM_eq_unMy`, `unBadY_of_blockM`, `Gres_sq_apply_self_spectral` have no outside reader.
**(v) Private-lemma change table** (all four are `private`, hence free to change; statements of the public band theorems stay verbatim).
| private | old | new | in-file callers |
|---|---|---|---|
| `Jak_grid_energy_lt` `:354` | hyp `\|E\|<=2-κ`; concl `\|E0-r+2ηj\| < 2-κ/2` | no `hE`; concl `\|E0-r+2ηj-E\| < κ/2` (same proof: `\|e-E0\| <= r+2η`, `C+2η<κ/4`, `r<=κ/4`) | `Jak_fixed_time:700` |
| `Jak_fixed_time` `:561` | `lam`, `hlam`, `hE`, `hdiag` on `\|e\|<2-κ/2`, `hque` | `lamV` in scirc/blockM; drop `hlam`, `hE`, `hque`; `hdiag` on `\|e-E\|<κ/2`; add `hbad : P{blockM-event at lamV} <= (2d+1:ℝ≥0∞)*ofReal(W^{-dd/30})` | `unJak_of_ouClaims:908` (builds `hbad` from `measure_bad_le_of_queBadMat`) |
| `Uyw_grid_energy_lt` `:328` | as Jak | as Jak | `Uyw_fixed_time:643` |
| `Uyw_fixed_time` `:497` | as Jak, pair event `blockM2` | as Jak, `hbad` for the `blockM2` event | `unUyw_of_ouClaims:846` (from `measure_bad2_le_of_queBadMat`) |
Unchanged: `*_pointwise_good_norm` (one `lam` = `lamV`), `*_queBound_eq`, the `*_total_le`, `*_prod_*`. `JakSpectral`: no edit (`unBadY_of_blockM` is coupling-generic, `measure_bad_le_of_queBadMat` public; `measure_bad2_le_of_queBadMat` public in `UywKernel`). Decision: the K-forms go in the leaf by `open private` (dispatcher answer (4)); they CAN reach `Jak_fixed_time, Jak_queBound_eq, Uyw_fixed_time, Uyw_queBound_eq` (4 names; `open private` is used at `Graph/BAS3CloseC:41`), so no `PinsK` import in the band files. Consequence: the band theorems keep re-instantiated calls (the K-forms come after them).
**(vi) K-hypothesis table** (`κ_eff = min κ (min 2 (2r))`, `r,κ'` from `T2476_BulkWindowk`; fixed-time lemma at `κ_eff`, `hque`/QUE at `κ` for `E`, `hdiag` via `UNOUDiagk` at `κ'`; `κ_eff/2 <= r` gives `bulk κ' e n` for `\|e-E\|<κ_eff/2`).
| hypothesis of `unJak_of_ouClaimsk` / `unUyw_of_ouClaimsk` / `jakUywRowk` | band producer | BA producer |
|---|---|---|
| `T2476_BulkWindowk K` | `κ'=r=κ/2` (`\|E\|<=2-κ`, `\|e-E\|<=κ/2` => `\|e\|<=2-κ/2`) | `BAbulk_window` (`MReg:122`): `κ/2`, `(πκ)³/8` |
| `T2476_BadBoundk K` (factor 2d+1) | `measure_bad_le_of_queBadMat` through `ouMatC_toC` | `unBadY_of_blockM` + `unBadYBA_measure_le` (`UNPins:738`), `p <= (2d+1)p` |
| `T2476_Bad2Boundk K` | `measure_bad2_le_of_queBadMat` (`UywKernel:1061`) | new: `SBR_zero_ne` + `sum_SBR_row` => `blockM2 0 = u_a0`; `isOrthoEigenbasis_eigenvectorBasis`, `un_window_sub` => `queBadMat` at `a0` (`alg.py` (1)) |
| `UNOUQUEk (K d) sz dd tau`, `UNOUDiagk (K d) sz tau` | inside `UNOUClaimsk` (hyp of `UNJakUywRowk`) | same, `Loc = UNLocAvgBA` hyp |
| `Admissible`, `κ>0`, `E` eventually in `bulk`, `tau in (0,1/4]` | binders | binders |
No premise beyond these is needed (grep of `Jak_fixed_time`/`Uyw_fixed_time`: `lam` occurs only in `scirc`, `blockM`/`blockM2`, `*_pointwise_*` calls, `hlam`, `hque` and the `measure_bad*` call; `E` only in `hE` (dropped), the windows `hw, hu, hS, hwin` (`\|·-E\| <= C0/X`), the bad event and `hque`).
**(vii) E1 transfer** (all by script-checked identities, no edit of `OUGenerator/OUHessian/OUContraction/EMCTE2`).
| step | statement | source |
|---|---|---|
| 1 | `TestFunH Φ`, `A` Hermitian => `TestFunH (Φ(A+·))`; `fderiv`, `fderiv²` of a translate are the translates; hence `wirtSecond Φ_A M a b = wirtSecond Φ (A+M) a b` | `OUGenerator:68`, `OUHessian:216`; `alg.py` (2) |
| 2 | `eq225_intervalShift`: `eq225_interval` body at `Φ_A = ∏ Im stieltjesN (A+·) z`; `ouGenerator_*` generic in Φ; kernel bound at `H = A+ouMat` (Hermitian) | `EMCTE2:455-589`, `OUGenerator:1057,1073`, `OUContraction:1077` |
| 3 | `ouMatC (UNModelC.ba sz) - λΨ = ouMat (band (sz.withLam 0))` (statement is in this subtract form at `UNPins:445`, not `λΨ + ·`); same carrier `ouP_ba_eq_band` (`rfl`); `lamV = 0 = (sz.withLam 0).lam`; `A = λ_nΨ` Hermitian (`mean_herm`) | `UNPins:445-470` |
| 4 | `unEMCTE2k_ba` = copy of `unEMCTE2_of_sizeTendsto:597-679` with `ouMat band` replaced by `A+ouMat`; `unEMCTE2RowBA_holds`: `Cn=1, τ0=1`, `SizeTendsto` of `sz.withLam 0` = of `sz` | `EMCTE2:681` |
`open private ... from RBM3D.Universality.EMCTE2` (7): `EMCTE2_hsum` (def in the statement of the bound), `EMCTE2_hsum_nonneg` (`Bd>=0`), `EMCTE2_hsum_bdd` (instance), `EMCTE2_integrable_hsum` (∫‖·‖ <= ∫hsum), `EMCTE2_integrable_L1t_term`, `EMCTE2_integrable_L2t_term` (split of the kernel integral), `EMCTE2_sum_integral_swap` (generic `TestFunH Φ`, used at `Φ_A`). `EMCTE2_integrable_wirtSecond`, `EMCTE2_BM_*` are used only inside these.
**(viii) Predicted lines** (central, new/changed): `Jak` +30 (private edits 15, band caller `hbad` 15) -> 1,033; `Uyw` +30 -> 998; `JakSpectral` 0 -> 675; `BA/EMCTE2BA` E1 360 + K-forms 195 + 3 band hypothesis instances 36 + `jakUywRowk` 25 + BA part (targets 7-10: 145) + header/`open private` 30 = 791. Total 851 (ticket 930; split threshold 1,950: no pre-signed split). 2.6x reference: `Jak` 1,081, `Uyw` 1,046, twin 2,057 (> 1,800 only at the upper reference). Plan: single twin; at 1,500 lines in the twin move targets 7-10 to the reserve `BA/JakUywBA.lean` (about 165 lines, imports `EMCTE2BA`); the 1,800 rule then applies as written. All three stop lines (2,000) hold at central.
**(ix) Premise scan** (`lake env lean RBM3D.lean` on the worktree, exit 0): `premises found by scanning: 132 (borrowed 1, owed 66, structural 45, refuted 6, superseded 14)`; `registry: ... 126 registered premise(s) carry nothing yet`; resting counts `UNEMCTE2k 8, UNJakk 7, UNUywk 7, UNJakUywRowk 7, UNEMCTE2RowBA 5, UNJakUywRowBA 5`. Rule (`Test/Axioms.lean:453-479`): a premise leaves `found` when a theorem's conclusion head is it. Prediction: `unEMCTE2k_ba`, `unJak_of_ouClaimsk`, `unUyw_of_ouClaimsk`, `jakUywRowk`, `unEMCTE2RowBA_holds`, `unJakUywRowBA_holds` move six premises out of `found` (132 -> 126, "carry nothing yet" 126 -> 132, as `UNEMCTE2Rowk` already is). Registry lines to touch (comments only, premises stay in `owedProps`): `Test/Axioms.lean:177,178,179,180,181` (`UNEMCTE2k, UNJakk, UNUywk, UNEMCTE2Rowk, UNJakUywRowk`) and `:187,188` (`UNEMCTE2RowBA, UNJakUywRowBA`). New `Prop` defs for the three K-hypotheses need no line: a theorem concludes each (`...band`, `...ba`), so the scan finds them proved; inline binders also need none.
**(x) Axioms baseline** (`lake env lean RBM3D.lean`, includes `#assert_rbm_axioms`, exit 0, 56 s): `axiom audit: 14065 theorems, 4452 definitions, 0 axioms in RBM ... All within [propext, Classical.choice, Quot.sound]`. This covers `band_terminal` (`Main/BandTerminal:104`) and `bUniv_holds` (`Main/BUnivHolds:227`); the two literal `#print axioms` lines are not taken here (no Lean at 1a); the auditor takes them on `main` and on `t/T2476` (GMN-C2 (c)).
**D1 (bulk window; bad-event transfer; BA/band discharges).** Math closes: (c) `hdiag` on `\|e-E\|<κ/2` is all `Jak_grid_energy_lt` uses; the kind supplies the window (rows `T2476_BulkWindowk`); (b) transfer hypothesis is the Jak/Uyw `hbad` of (v); BA one-block pair bound in (vi). Probe must compile: `hdiag`-window form of `Jak_fixed_time` signature (as a statement), the three `T2476_*` at `UNKind.band` and `UNKind.ba`, `eq225_intervalShift` and `unEMCTE2k_ba` statements; BA discharge failing => stop before 1b (short REQ).
**Findings.** (1) `ouMatC_ba_eq_band_add` is `ouMatC - λΨ = ouMat band`, not `λΨ + ouMat` (equivalent; ticket target 3 wording only). (2) Instance needs `C0 <= 1/2` at n=0 (`h2`), see (ii). (3) K-forms go in the leaf by `open private`; the ticket header/targets place them in `Jak`/`Uyw`: the dispatcher answer (4) overrides, consequence in (v). (4) Names `eq225_intervalShift, unEMCTE2k_ba, unEMCTE2RowBA_holds, unJak_of_ouClaimsk, unUyw_of_ouClaimsk, jakUywRowk, unJakUywRowBA_holds, UNBulkWindowk, UNBadBoundk, UNBad2Boundk, EMCTE2BA, JakUywBA`: 0 hits (`grep -rw RBM3D RBM3D.lean`).
**Verdicts.** Target 1 PASS; 2 PASS; 3 PASS; 4 PASS; 5 PASS; 6 PASS; 7 PASS; 8 PASS; 9 PASS; 10 PASS. D1: PASS (math), compile pending the probe.

## (a″) Probe compile — Mon Oct 12 22:57:05 UTC 2026
Probe step of the D1 gate (dispatcher answer (1), H250 (4)); section (a) is not edited. File `RBM3D/Probe/T2476Pins.lean` in `../RBM3D-wt/T2476`, branch `t/T2476`; never merged, no root import.
```
$ git log --oneline -2 (worktree); git rev-parse --short HEAD (main)
86eecc2d T2476: probe step (D1): bulk-window hdiag, bad-event transfers, BA and band discharges
eaa247c4 T2474: merge T5s2b Chain/HierDriftGen (pre-signed split, second row)
ab435c6e
$ git diff --stat eaa247c4 ab435c6e -- RBM3D RBM3D.lean   # main moved since (a); is it relevant?
 RBM3D/Chain/CltGen.lean | 5 +++--
 1 file changed, 3 insertions(+), 2 deletions(-)
$ git diff --stat eaa247c4 HEAD -- RBM3D.lean RBM3D/Universality RBM3D/BA RBM3D/Main   # worktree sources behind band_terminal / bUniv_holds
(exit 0)
$ wc -l RBM3D/Probe/T2476Pins.lean; grep -c "sorry\|admit\|native_decide" RBM3D/Probe/T2476Pins.lean
300 RBM3D/Probe/T2476Pins.lean
0
$ date -u; lake env lean RBM3D/Probe/T2476Pins.lean; echo "exit $?"; date -u
Mon Oct 12 22:55:45 UTC 2026
--- output (verbatim, 38 lines) ---
RBM.BA.BAbulk_window : ∀ (d L : ℕ) [inst : NeZero L] (g κ E x : ℝ),
  0 < κ → RBM.BA.BAbulk d L g κ E → |x - E| ≤ (Real.pi * κ) ^ 3 / 8 → RBM.BA.BAbulk d L g (κ / 2) x
@RBM.Univ.unBadYBA_measure_le : ∀ {d L W : ℕ} [inst : NeZero L] [inst_1 : NeZero W] {Ω : Type u_1}
  [inst_2 : MeasurableSpace Ω] (μ : Measure Ω),
  3 ≤ L →
    ∀ {lamQ 𝔡 E : ℝ},
      1 ≤ ↑W →
        0 < 𝔡 →
          ↑W ^ (-↑d / 2 + 𝔡) ≤ lamQ →
            ∀ (y : RBM.Gauss.Idx d L W) (Mf : Ω → Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ) (p : ℝ≥0∞),
              (∀ (b : RBM.Zd d L), μ {ω | RBM.Univ.queBadMat d L W lamQ (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} ≤ p) →
                μ {ω | RBM.Univ.UNBadY d L W 0 𝔡 E y (Mf ω)} ≤ p
@RBM.Univ.unBadY_of_blockM : ∀ {d L W : ℕ} [inst : NeZero L] [inst_1 : NeZero W],
  3 ≤ L →
    ∀ {lam 𝔡 E : ℝ} {M : Matrix (RBM.Gauss.Idx d L W) (RBM.Gauss.Idx d L W) ℂ} (hH : M.IsHermitian)
      (y α : RBM.Gauss.Idx d L W),
      |hH.eigenvalues α - E| ≤ (↑((W * L) ^ d))⁻¹ * ↑W ^ (𝔡 / 3) →
        ↑W ^ (-(𝔡 / 6)) ≤ ‖RBM.Univ.blockM d L W lam hH (RBM.Univ.siteBlock d L W y) α‖ →
          RBM.Univ.UNBadY d L W lam 𝔡 E y M
Jak_queBound_eq : ∀ (W : ℕ) {𝔡 : ℝ},
  0 < 𝔡 → RBM.Univ.queBound W 𝔡 (𝔡 / 3) (𝔡 / 6) (𝔡 / 30) = ENNReal.ofReal (↑W ^ (-(𝔡 / 30)))
Uyw_queBound_eq : ∀ (W : ℕ) {𝔡 : ℝ},
  0 < 𝔡 → RBM.Univ.queBound W 𝔡 (𝔡 / 3) (𝔡 / 6) (𝔡 / 30) = ENNReal.ofReal (↑W ^ (-(𝔡 / 30)))
'RBM.Univ.T2476_ouMatC_ba_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_grid_energy_win' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_hdiagWin_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_keff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_hdiagWin_of_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_hbad_of_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_BulkWindowk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_BulkWindowk_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_BadBoundk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_BadBoundk_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_Bad2Boundk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_bad2_subset_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2476_Bad2Boundk_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
Mon Oct 12 22:55:52 UTC 2026
```
**Fill-in table (H250 (4)).** Rows of the table in (a), by script (rows 7-17 of this report; "open" = status text of (a) still pointing to this step):
```
$ awk -F'|' 'NR>=7 && NR<=17' docs/reports/T2476-prove.md | wc -l; awk -F'|' 'NR>=7 && NR<=17 && ($4 ~ /NOT taken|compile = probe/) {print "open: " $2}' docs/reports/T2476-prove.md
11
open:  (x) `#print axioms band_terminal` / `bUniv_holds` on main 
open:  D1 (bulk window, bad-event transfer, BA discharges) 
```
Both open rows are closed here: (x) the two literal prints are the last two lines of the output above (`band_terminal`, `bUniv_holds`: standard three) on a worktree whose `RBM3D.lean`, `Universality`, `BA`, `Main` equal `eaa247c4` (empty diff above); D1 is the exit 0 above. Rows (i)-(ix) carry their results in (a). No row is open.
**D1 results** (probe file:line; the statements `T2476_BulkWindowk`, `T2476_BadBoundk`, `T2476_Bad2Boundk`, `T2476_unEMCTE2k_ba` are copied from the check file):
- Window `hdiag` (target 5 (c)): `T2476_grid_energy_win` (79) is `Jak_grid_energy_lt` without `hE`, conclusion `|E₀ - r + 2ηj - E| < κ/2`, same proof; `T2476_hdiagWin` (100) is the new `hdiag` hypothesis; `T2476_band_window` (96), `T2476_hdiagWin_of_band` (107): band caller from `|E| ≤ 2 - κ`; `T2476_keff` (115): `κ_eff = min κ (min 2 (2r))` is positive, `≤ κ`, `≤ 2`, `κ_eff/2 ≤ r`; `T2476_hdiagWin_of_K` (124): from `UNOUDiagk (K d)` and `T2476_BulkWindowk K`, for every `κe ≤ 2r`, any kind.
- Bad-event transfer: `T2476_BadBoundk_band` (134), `T2476_Bad2Boundk_band` (139) from `measure_bad_le_of_queBadMat`, `measure_bad2_le_of_queBadMat`; `T2476_BadBoundk_ba` (144) from `unBadY_of_blockM` + `unBadYBA_measure_le`, then `p ≤ (2d+1) p`; BA pair form (target 9): `T2476_bad2_subset_ba` (153-203) + `T2476_Bad2Boundk_ba` (205-211), 58 lines (1a estimate: 60); `T2476_hbad_of_K` (214): Jak's `hbad` for any kind from `T2476_BadBoundk`, `UNOUQUEk` (at `τ_Q = 𝔡/30`) and `sz.WO 𝔡`, with `Jak_queBound_eq` taken by `open private`.
- Bulk window: `T2476_BulkWindowk_band` (229) with `κ' = r = κ/2`; `T2476_BulkWindowk_ba` (236) by `BAbulk_window`, `κ' = κ/2`, `r = (πκ)³/8`.
- Instances (`example`, lines 242-275): band numbers `κ = 1/2`, `E = 1`, `e = 9/8`; the K-forms feeding `hdiag` and `hbad` at `SizesInst.sz0` (band) and `BAInst.S0` (BA) with `UNOUDiagk`, `UNOUQUEk` as hypotheses (other gates' pins); the BA window at `(κ_*/2, E_* + (πκ_*)³/8)` from `S0_bulk`; both BA transfers at `S0`, `𝔡 = 1/10`, `p = 1`.
**Observations for the 1a-audit and 1b.** (1) No stop rule fires: both transfer forms and their BA discharges compile; `3 ≤ L` and `1 ≤ W` come from `Sizes.three_le_L`, `Sizes.W_pos`, so the check-file shapes need no extra binder. (2) `open private` of `Jak_fixed_time, Jak_queBound_eq, Uyw_fixed_time, Uyw_queBound_eq` compiles (probe lines 25-26); the `_queBound_eq` pair is `#check`ed above. (3) The additive form of the translation, `T2476_ouMatC_ba_add` (70), elaborates only through `show Matrix (Idx d (sz.L n) (sz.W n)) … from ouMat (UNModel.band (sz.withLam 0)) …`: `+` across `Idx d ((sz.withLam 0).L n) …` and `Idx d (sz.L n) …` is not found by instance search, so 1b should use the merged subtract form `ouMatC_ba_eq_band_add` or this `show`. (4) Not compiled by the probe (outside answer (1)): the window-form proofs of `Jak_fixed_time`/`Uyw_fixed_time` (edits in `Jak.lean`, `Uyw.lean`, 1b), `eq225_intervalShift` and the translation lemmas (E1); `T2476_unEMCTE2k_ba` (66) is a statement only. **D1 verdict: PASS (compile, exit 0, the 15 printed declarations, including `band_terminal` and `bUniv_holds`, depend only on the standard three axioms).**

## (b) Script output — Mon Oct 12 23:40:20 UTC 2026 (branch `t/T2476` at b27bc334; base `eaa247c4`; scripts and logs in `scratchpad/T2476/`)
```
$ git log --oneline main..t/T2476      # probe commit (never merged) + the three section commits and three follow-ups
b27bc334 band recovery instance | 304f73df rename of the consumer instance | b6a709b9 header wrap, axioms prints | c2065a99 BA/EMCTE2BA twin
b09ee6be Uyw two couplings and bulk window | 3a4a3afc Jak two couplings and bulk window | 86eecc2d probe step (D1)
$ lake build RBM3D.Universality.Jak RBM3D.Universality.Uyw RBM3D.BA.EMCTE2BA RBM3D.Universality.UnivMain RBM3D.Main.BUniv RBM3D.Main.BUnivHolds RBM3D.Main.BandTerminal
Build completed successfully (4156 jobs).      # after Jak and after Uyw alone: `lake build ...Main.BandTerminal ...Main.BUnivHolds` completed (4149 jobs)
$ lake build      # whole library, includes `#assert_rbm_axioms` (RBM3D.lean:549), 23:39:01 -> 23:39:57 UTC
RBM3D.lean:549:0: axiom audit: 14102 theorems, 4456 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4317 jobs).   exit 0
$ wc -l   (stop line 2,000 per file; census 680 / 930 / 1,280; 1a prediction: Jak 1,033, Uyw 998, twin 791)
  1017 Jak.lean | 984 Uyw.lean | 675 JakSpectral.lean (unchanged) | 986 BA/EMCTE2BA.lean | 300 Probe/T2476Pins.lean (not merged)
$ python3 -I cone.py . <module>...    # reverse cone (library members; the leaf and the probe are new members), LWExpCert*, BandTerminal closure
Jak: 7 = {Uyw, UnivMain, BUniv, BUnivHolds, BandTerminal} + leaf + probe | none | yes      JakSpectral: 10 = + {JakKernel, UywKernel, Jak} | none | yes
Uyw: 6 = {UnivMain, BUniv, BUnivHolds, BandTerminal} + leaf + probe | none | yes           EMCTE2 (not edited): 6, same | none | yes
BA/EMCTE2BA: reverse cone 0; forward closure 104 modules, LWExpCert none, BandTerminal not imported; BA.* in Jak/JakSpectral/Uyw forward closures: none
$ signature diff (ticket awk over Jak JakSpectral Uyw EMCTE2, main vs t/T2476)      # prints CHANGED only if a main header is missing
(no CHANGED line)  public headers main/branch/diff lines: Jak 7/7/0, JakSpectral 24/24/0, Uyw 7/7/0, EMCTE2 8/8/0
$ git diff --numstat main...t/T2476 -- RBM3D/Universality/      # JakSpectral, EMCTE2 and every other Universality file unchanged
45 31 Jak.lean | 47 31 Uyw.lean
$ lake env lean scratchpad/T2476/G1.lean   # 14 `example : <old statement> := <old name>` (Jak 7, Uyw 7) generated from the main dump
exit 0, 14 examples      # JakSpectral (24 declarations) and EMCTE2 (8): file unchanged, text identical
$ lake env lean scratchpad/T2476/props.lean   # check-file proposals T2476_* against the final names (Iff.rfl / identity), binder adjustments: none
exit 0, 13 examples (eq225Shift, unEMCTE2k_ba, 3 Iff.rfl for the kind hypotheses, the three K-forms, both pins, the band and BA triples, T2476_BUnivBA as a term from baBUniv_of_rows)
$ lake env lean scratchpad/T2476/ax2.lean   # branch; main baseline = the same two lines in (a″) (worktree sources equal to main for these modules)
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ private-lemma changes (4 privates; `git diff -U0 eaa247c4 HEAD`; Jak shown, Uyw is the same with `blockM2`, `Uyw_*`)
- Jak_grid_energy_lt: hyp `(hE : |E| ≤ 2 - κ)` dropped; concl `|E₀ - r + 2 * ηt * j| < 2 - κ / 2`  ->  `|E₀ - r + 2 * ηt * j - E| < κ / 2`
- Jak_fixed_time:    `(lam : ℝ)` -> `(lamV : ℝ)` (scirc, blockM); dropped `hlam`, `hE`, `hque`; `hdiag : ∀ e, |e| < 2 - κ / 2 →` -> `|e - E| < κ / 2 →`
                     added `(y) (hbad : P {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ ... ∧ W^(-(𝔡/6)) ≤ ‖blockM d L W lamV (hH ω) (siteBlock d L W y) α‖} ≤ (2d+1) * ofReal (W^(-(𝔡/30))))`
- callers: unJak_of_ouClaims / unUyw_of_ouClaims (in-file) pass `hbad := measure_bad_le_of_queBadMat ...` / `measure_bad2_le_of_queBadMat ...` and `hdiag` through
  `hew : |e - E| < κ/2 -> |e| ≤ 2 - κ/2` (from `|E| ≤ 2 - κ`); no other in-file caller; public statements unchanged (signature diff above)
$ target statements, extracted by awk from RBM3D/BA/EMCTE2BA.lean (first 3 header lines of each)
theorem EMCTE2BA_testFunH_translate {Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ} (hΦ : TestFunH d L W Φ)
  {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) : TestFunH d L W (fun K => Φ (A + K)) := by
theorem EMCTE2BA_wirtSecond_translate (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
  (A M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Idx d L W) :
  wirtSecond d L W (fun K => Φ (A + K)) M a b = wirtSecond d L W Φ (A + M) a b := by
theorem eq225_intervalShift (d : ℕ) (sz : Sizes d) (n nf : ℕ) (z : Fin nf → ℂ)
  (hz : ∀ i : Fin nf, 0 < (z i).im)
  (A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hA : A.IsHermitian)
  ... (18 header lines)
theorem unEMCTE2k_ba (d : ℕ) (sz : Sizes d) (hd : sz.SizeTendsto) (E : ℝ) (nf : ℕ) (τU Cn : ℝ)
  (hτ : τU ≤ Cn * τU) : UNEMCTE2k (UNKind.ba d) sz E nf τU Cn := by
def UNBulkWindowk (K : ∀ d, UNKind d) : Prop :=
def UNBadBoundk (K : ∀ d, UNKind d) : Prop :=
def UNBad2Boundk (K : ∀ d, UNKind d) : Prop :=
theorem unJak_of_ouClaimsk (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBadBoundk K) :
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
  ... (5 header lines)
theorem unUyw_of_ouClaimsk (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBad2Boundk K) :
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
  ... (5 header lines)
theorem jakUywRowk (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBadBoundk K) (hbb2 : UNBad2Boundk K)
  (Loc : Prop) : UNJakUywRowk K Loc := by
theorem unEMCTE2RowBA_holds : UNEMCTE2RowBA := by
theorem UNBulkWindowk_ba : UNBulkWindowk (fun d => UNKind.ba d) := fun d sz κ hκ =>
  ⟨κ / 2, (Real.pi * κ) ^ 3 / 8, by positivity, by positivity,
  fun n E e hE he => BAbulk_window d (sz.L n) (sz.lam n) κ E e hκ hE he⟩
theorem UNBadBoundk_ba : UNBadBoundk (fun d => UNKind.ba d) := by
theorem EMCTE2BA_bad2_subset {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {lamQ 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ))
  (h𝔡 : 0 < 𝔡) (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lamQ) (a0 : Zd d L)
  {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (α β : Idx d L W)
  ... (7 header lines)
theorem UNBad2Boundk_ba : UNBad2Boundk (fun d => UNKind.ba d) := by
theorem unJakUywRowBA_holds : UNJakUywRowBA :=
# UNBulkWindowk / UNBadBoundk / UNBad2Boundk are Iff.rfl to the check-file T2476_BulkWindowk / BadBoundk / Bad2Boundk (props.lean); eq225_intervalShift ≡ T2476_eq225Shift, unEMCTE2k_ba ≡ T2476_unEMCTE2k_ba (identity examples)
$ axioms of every new declaration: `#print axioms` lines of the leaf build (35 lines) / non-standard: 0 ; sorry|admit|native_decide|axiom in Jak, Uyw, EMCTE2BA: 0, 0, 0
  all of the form  [propext, Classical.choice, Quot.sound]   (eq225_intervalShift, unEMCTE2k_ba, unEMCTE2RowBA_holds, unJak_of_ouClaimsk, unUyw_of_ouClaimsk, jakUywRowk, unJakUywRowBA_holds, the kind hypotheses, instances)
$ compiled nonempty instances, namespace RBM.Univ.EMCTE2BAInst (d = 3; lines of BA/EMCTE2BA.lean): target 1: inst_translate :805, inst_wirtSecond_translate :811 | target 2: inst_eq225_intervalShift :820 (sz0, n = 0, z = ![I], A = λ_0 Ψ ≠ 0, kernel hyp by EMCTE2_hsum_bdd)
  A = 0 recovery of eq225_interval: example :249 | target 3: inst_unEMCTE2k_ba_sz0 :860 (sz0, nf = 2, τU = 1/2) | target 4: inst_unEMCTE2Rowk_ba :865 (S0, κ_*, E_*, nf = 1: `UNEMCTE2k (UNKind.ba 3) S0 E_* 1 τU Cn`, no hypothesis left)
  targets 5, 6: inst_unJak_k_band :871, inst_unUyw_k_band :879, inst_unJak_unUyw_band_recover :888 (gives the band `UNJak`, `UNUyw` of JakInst.inst_unJak, UywInst.inst_unUyw by UNJakk_band, UNUywk_band), inst_jakUywRowk_band :899 (UNKind.band 3, sz0, κ = 1/2, E = 1, nf = 2), inst_unJak_k_ba :910, inst_unUyw_k_ba :917 (S0, κ_*, E_*, nf = 2)
  targets 7-9: inst_bulk_window_ba :925 (κ' = κ_*/2, r = (π κ_*)³/8 > 0), inst_bad_ba :932 | target 10: inst_unJakUywRowBA :943 | consumer: inst_univ_ba_rows :951 and the `example` :960 (baBUniv_of_rows with rE, rJ discharged)
  hypotheses left (other gates' pins): UNOUQUEk, UNOUDiagk (K-form instances), UNLocAvgBA and rO hML hLoc hQ (inst_unJakUywRowBA, as BAInst.inst_UNJakUywRowBA), the rows of the other gates (inst_univ_ba_rows); inst_bad_ba applies the transfers with the QUE bound p = 1 (prob_le_one)
$ name-clash grep of the 41 new top-level names (git grep -w on main, files other than the leaf)
41 names checked, 0 hits      # inst_translate etc. live in RBM.Univ.EMCTE2BAInst; helpers carry the stem EMCTE2BA_; Jak_/Uyw_ privates are not renamed
$ git diff main...t/T2476 -- {Pins,PinsK,PinsC2,PinsDens,JakKernel,UywKernel,EMCTE2,OUGenerator,OUHessian,OUContraction,UnivMain,JakSpectral}.lean BA/UNPins.lean BA/MReg.lean Main | wc -l
0
$ git diff --stat main...t/T2476  /  grep -n '^import RBM3D.BA' Jak JakSpectral Uyw  /  grep -rln 'import RBM3D.BA.EMCTE2BA' RBM3D RBM3D.lean
RBM3D.lean +1 | BA/EMCTE2BA.lean +986 | Probe/T2476Pins.lean +300 (not merged) | Test/Axioms.lean 7+/7- | Jak.lean 45+/31- | Uyw.lean 47+/31-   ;   0 BA imports in the band files   ;   RBM3D.lean only
$ registry: Test/Axioms.lean comments only (7 lines, premises stay in owedProps); scan output of `lake build` (23:39 UTC)
lines changed: UNEMCTE2k, UNJakk, UNUywk, UNEMCTE2Rowk, UNJakUywRowk (:177-181), UNEMCTE2RowBA, UNJakUywRowBA (:187-188); no new registry line (the three kind hypotheses are concluded by *_band / *_ba theorems)
premises found by scanning: 126 (borrowed 1, owed 60, structural 45, refuted 6, superseded 14).   [1a (ix) baseline: 132 found, owed 66]
registry: 2 borrowed + 109 owed + 122 structural + 7 refuted + 18 superseded; 132 registered premise(s) carry nothing yet   [baseline 126]
resting counts: UNEMCTE2k 11, UNJakk 12, UNUywk 12, UNEMCTE2Rowk 8, UNJakUywRowk 8, UNEMCTE2RowBA 6, UNJakUywRowBA 6   [baseline 8, 7, 7, ·, 7, 5, 5]
```
**Narrative.**
1. Order and sizes as ticketed: `Jak`, `Uyw`, then the leaf. After `Jak` and after `Uyw` the band terminal modules built (4149 jobs). The stop rule `wc -l` was applied at each section commit (Jak 1016, Uyw 984, twin 955; final 1017, 984, 986; all < 2,000); the twin is below the 1,500 rule, so the reserve `BA/JakUywBA.lean` is not created.
2. Layout follows 1a (v)/(dispatcher answer (4)): the K-forms (`unJak_of_ouClaimsk`, `unUyw_of_ouClaimsk`, `jakUywRowk`) and the kind hypotheses are in the leaf; `Jak_fixed_time`, `Jak_queBound_eq`, `Uyw_fixed_time`, `Uyw_queBound_eq` are reached by `open private`; no import was added to a band file. The band theorems keep their in-file re-instantiated calls (they are not derived from the K-forms). The ticket text places the K-forms in `Jak`/`Uyw` (targets 5-6 header); this is the 1a finding (3).
3. E1: `eq225_intervalShift` is the text of `eq225_interval` at the shifted functional `Φ_A = Φ₀(A + ·)`; the kernel bound is `centeredVariance_wirtProduct_kernel_bound_Lt` at `A + ouMat`, brought to `Φ_A` by `EMCTE2BA_wirtSecond_translate`; the `open private` list is the seven names of 1a (vii) (reasons there), each used at least once after the `open private` line (grep counts 1-2); the helpers are generic in the matrix family. `unEMCTE2k_ba` states the kernel bounds at `ouMatC (UNModelC.ba sz)`, rewrites by `ouMatC_ba_eq_band_add` (the `A + ouMat` form needs `show Matrix (Idx d (sz.L n) _) _ ℂ from ouMat (band (sz.withLam 0)) …`, as in the probe observation (3)) and applies `eq225_intervalShift (sz.withLam 0)`; `lamV = 0 = (sz.withLam 0).lam n` is by `rfl`.
4. E2: the K-forms are the bodies of `unJak_of_ouClaims`, `unUyw_of_ouClaims` with `κ_eff = min κ (min 2 (2r))` for the fixed-time lemma, `UNOUDiagk` at the window's `κ'`, `UNOUQUEk` at `κ`, `hbad` from `EMCTE2BA_hbad_of_K` / `EMCTE2BA_hbad2_of_K` (transfer, QUE at `τ_Q = 𝔡/30`, `(eq:WO)`); the factor `2d + 1` is kept for both kinds (block Anderson: `p ≤ (2d + 1) p`).
5. The pair lemma (target 9, `EMCTE2BA_bad2_subset`) is the probe lemma `T2476_bad2_subset_ba` (copied); `UywKernel` and `JakSpectral` are not edited. Merge notes for the hub: `RBM3D.lean` import line and the seven comment lines of `Test/Axioms.lean` are in the branch; `main` moved after the base by `CltGen.lean` only (per (a″)); the merge re-runs the `band_terminal`/`bUniv_holds` comparison and the full build on the merged base (dispatcher answer (6)); `RBM3D/Probe/T2476Pins.lean` is on the branch and must not be brought in.

## (c) Verified Mathlib names (all used by `BA/EMCTE2BA.lean`; file:line from `grep -rn`)
- `fderiv_comp_add_left` (`Mathlib/Analysis/Calculus/FDeriv/Add.lean:900`; `f` and `x` need explicit arguments at `f := fderiv ℝ Φ`)
- `Measurable.of_eval_matrix`, `Measurable.eval_matrix` (`Mathlib/Analysis/Matrix/MeasurableSpace.lean:33, 30`); `Matrix.IsHermitian.add` (`Mathlib/LinearAlgebra/Matrix/Hermitian.lean:209`)
- `contDiffAt_const` (`.../ContDiff/Basic.lean:111`), `contDiffAt_id` (`:186`), `ContDiffAt.comp` (`.../ContDiff/Comp.lean:223`); `sub_eq_iff_eq_add'` (`to_additive` of `div_eq_iff_eq_mul'`, `Mathlib/Algebra/Group/Basic.lean:953`)
- Names verified absent: none searched. `ouMatC_measurable`-type lemmas: only private copies exist (`UnivMain_`, `QUEFlow_`, `OUInterfaceK_measurable_ouMatC`); the leaf avoids them by the explicit shift `EMCTE2BA_measurable_shift`.

## (d) Open issues and paper-delta candidates
- No port from RBM1D/RBM2D is added: the copied texts are RBM3D's own `eq225_interval`, `unEMCTE2_of_sizeTendsto`, `unJak_of_ouClaims`, `unUyw_of_ouClaims` (RBM3D `EMCTE2.lean`, `Jak.lean`, `Uyw.lean`); no RBM1D/RBM2D diff-stat applies.
- Open (other gates): `UNOUQUEk`, `UNOUDiagk` (rows `UNOURowBA`), `UNLocAvgBA` stay hypotheses of the K-form instances and of `UNJakUywRowBA`; the pins `UNEMCTE2RowBA`, `UNJakUywRowBA` remain hypotheses of the merged consumers (`baBUniv_of_rows`, `un_claimAll_of_rowsBA`), now with producers.
- Instances: the BA targets 7-9 are exercised with the trivial QUE bound `p = 1` (`inst_bad_ba`) and through the K-form instances (QUE as a hypothesis); no instance with the nontrivial `queBound` exists until `UNQueBA` is produced (BA-M3).
- Paper-delta candidates: `T2476a` and `T2476b` as in the ticket. Additions: (T2476a) the shifted generator identity holds with the kernels `L₁`, `L₂` at coupling `0` (`S^{(B)}(0) = I`), the matrix argument being `λΨ + 𝐇^{band}_t`; Lean states it as `eq225_intervalShift` for a deterministic Hermitian shift `A`. (T2476b) the Lean K-forms assume the kind's bulk window (`UNBulkWindowk`: band `κ' = r = κ/2`; block Anderson `κ' = κ/2`, `r = (πκ)³/8`, `BAbulk_window`) and run the fixed-time lemma at `κ_eff = min κ (min 2 (2r))`; the paper does not state the window. The pair/one-block event is stated in Lean with the factor `2d + 1` for both kinds (`UNBadBoundk`, `UNBad2Boundk`), weaker than the one-block bound `unBadYBA_measure_le` (no factor).

