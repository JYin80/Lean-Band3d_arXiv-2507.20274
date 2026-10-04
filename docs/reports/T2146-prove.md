Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 17:45:10 UTC 2026

Targets (mathematics only): the good set `GoodSetN` of the grid walk at loop length `k ≥ 2` (matrix level, `Γ = N^ε`, levels `Λ Φ ≥ 1`, window `ℓ_u W^{τ'}`, decay `W^{-D'}`), its exit time `gridExitTauN`/`goodExitTauN`, measurability (`MeasurableGoodSetN`, `GoodExitMeasN`), and `GridGoodN`: `P(∃ j ≤ K_n: H_j ∉ GoodSetN(u_j)) ≤ N^{-D}`. Notation: `B = Bctl n u = W^{-d}B_{u,0}`, `η = etaT E u`, `X_m = STXiL(m)`, `Y_m = STXiLK(m)` (random, `Step34Pins.lean:63,68`), matrix-level versions `STXiLM, STXiLKM` (new vocabulary: `1 + max_{σ,a}|loopFine …|/B^{m-1}`, `1 + max|loopFine − STKloop|/B^m`). RBM2D source: `git show c9a24cf:RBM2D/Induction/GridGoodN.lean` (`GoodSetN` :81, `GridGoodN` :207, exit times :123-186, measurability :532-1000).

### (i) Exponent table and clause table
Consumer = destructuring of `hM : M ∈ GoodSetN` at `c9a24cf` (`RBM2D/Induction/<file>:line`). The 12 conjuncts of `GoodSetN` are (Herm, G1, G2, G3, G4, Dec, D1, D2, D3, D4, Va, Vb).

| # | RBM2D clause (`GoodSetN`) | d ≥ 3 clause, level, scale | merged statement that gives it w.h.p. | consumer (file:line) |
|---|---|---|---|---|
| 1 | Herm | `H.IsHermitian` | `pathH_isHermitian` (Walk.lean:98), `seqHflow` Hermitian (always) | AltEnd:506, AltLevelsQ:321, AltEndCompose:448, NonAltGood:424,1431 |
| 2 | G1 `Ξ^L_{2k+2} ≤ ΓΛ` | **dropped**: no destructuring uses position 2; the d≥3 `lem:SEforLn`(4) uses `X_{2k-1}`, `X_{4q}`, not `X_{2k+2}` (row 12) | — | none |
| 3 | G2 `Ξ^{LK}_m ≤ ΓΦ`, `1 ≤ m < k` | `Y_m(H) ≤ ΓΦ`, `1 ≤ m < k` (`STXiLKM`) | `Prec.whp` of hypothesis hY (row 11) | AltEnd:518, AltLevelsQ:333 (only `m = k-1`) |
| 4 | G3 `Ξ_mΞ_{k-m+2}M⁻¹ ≤ ΓΦ` | **dropped**: no consumer; `PPVocab:1193-1200` shows it is too strong at `k = 2`; d≥3 conjunct (3) has no `M⁻¹` factor | — | none |
| 5 | G4 `Ξ^L_{k+1} ≤ ΓΦ` | **dropped as clause**, kept as hypothesis hX (used inside D3) | — | none |
| 6 | Dec: `(|𝓛|+|𝓛−𝒦|)(H) ≤ W^{-D'}` if `ℓ_u W^{τ'} ≤ diam`, lengths `1..2k+2` | same with `loopFine`, `STKloop`, `diam = STdiamInf` (l^∞, `DecayLoopA.lean:71`), `ℓ_u = ellT (sz.L n)(sz.lam n) u` | `STDecayLoopU` (DecayLoopB.lean:792) `←` `stDecayLoopU_of_step2` from `STStep2Concl.2.2`; then `N^{1}W^{-D''} ≤ W^{-D'}` with `D'' = D'+1/𝔠` | AltEnd:531, AltLevelsQ:346 (`k-1`), NonAltGood:431 (`1..2k+2`), :1289 (`k`) |
| 7 | D1 `‖ksimLK_l‖ ≤ Γ(k-1)(ΓΦ)M^{-k}η⁻¹`, `3 ≤ l ≤ k` | `‖STksimLKM … l (loopOf σ a)‖ ≤ Γ(ΓΦ) B^k η⁻¹` (sharper: single `Y_{k-l+2}`, index `2..k-1`) | conjunct (2) of `STSEforLnConcl` (`stSEforLn_holds`) + `Y ≤ ΓΦ` | NonAltGood:79, AltLevelsQ:173 |
| 8 | D2 `‖elklkN‖ ≤ Γ(k-1)(ΓΦ)M^{-k}η⁻¹ + W^{-D'}` | `‖STelklkM‖ ≤ Γ·k(ΓΦ)² B^k η⁻¹`, **no additive term**, `Φ²` (conjunct (3) is `ΣY(XX)^{1/2} + B^{1/6}Y_k`, no `M⁻¹` to absorb one `Φ`) | conjunct (3) + `Y_m, X_m ≤ ΓΦ` (`#n' ≤ k/2`, `B ≤ 1`) | NonAltGood:79, AltLevelsQ:173 |
| 9 | D3 `‖egtN‖ ≤ ΓΓΦ M^{-k}η⁻¹ + W^{-D'}` | `‖STegtM‖ ≤ Γ(ΓΦ) B^k η⁻¹` (conjunct (1): `(X_{n1}X_{n2})^{1/2}`, `n1,n2 ∈ [k-1,k+1]`) | conjunct (1) + `X ≤ ΓΦ` | NonAltGood:79, AltLevelsQ:173 |
| 10 | D4 `‖eeN‖ ≤ ΓΓΛ M^{-2k}η⁻¹ + W^{-D'}` | `‖STeeM σ a a'‖ ≤ Γ(ΓΛ) B^{2k} η⁻¹`, no additive term | conjunct (4), every `q ≥ 1`, `= B^{2k}η⁻¹ X_{2k-1}(X_{4q}/B)^{1/(2q)}`; level hQ (row 12) | NonAltGood:130,1432, AltProxyQ:955, AltEndCompose:449 |
| 11 | PT levels G2/G4 | **hX**: `∀ m ≤ k+1, Prec[TimeIcc s t] X_m ≺ Φ`; **hY**: `∀ m ≤ k, Prec Y_m ≺ Φ` (`m = k` enters D2 via `B^{1/6}Y_k`; the shape of `STXiBoot`'s hypotheses `STlenL`) | external (Steps 3-4 levels); at `Φ = 1` they are `STLmaxU`/`STLKU` (`1 + a/b ≺ 1`) | — |
| 12 | PT level G1 | **hQ**: parameter `q ≥ 1`; `Prec[TimeIcc s t] X_{2k-1}(X_{4q}/B)^{1/(2q)} ≺ Λ`. `Λ ≥ B^{-1/(2q)}` up to `X`: `B ≥ 1/N` so `q ≥ 1/(2ε)` gives `B^{-1/(2q)} ≤ N^ε`; `q` is a parameter of `GridGoodN` only, not of `GoodSetN` | external; `st_Bctl_ge` (ScaleFacts3:56): `B ≥ N^{-2}`; script: `N·B ≥ 1` | — |
| 13 | Va: `‖Σ_l ksimLK‖+‖elklk‖+‖egt‖ ≤ W^{-D'}` far | same, far = `ℓ_u W^{τ'} ≤ STdiamInf a` (`diam_∞ ≤ KLmaxDist`, `DecayLoopA_diam_le_KLmaxDist`) | `stEtermDecay` (DecayLoopB.lean:2209) at `ε = τ'`, `D = D'+1`; `k·W^{-D'-1} ≤ W^{-D'}` eventually | NonAltGood:103, AltLevelsQ:173 |
| 14 | Vb: `‖eeN‖ ≤ W^{-D'}` far in `Fin.append a a'` | same | `stEtermDecay` 4th component, `b = Fin.append a a'` | NonAltGood:130, AltProxyQ:955, AltEndCompose:449 |
| 15 | `0 ∈ GoodSetN` at `u = 0` | needed non-vacuity (`s = 0`, `H_0 = 0`, `pathH` Walk.lean:75) | `L = K` at `u = 0`: `Theta_zero` (Primitive.lean:51), `kTwo_zero` (:80); script part E | AzumaProxyN:1300-1304, NonAltGood:996 |

| # | exponent / constant | value | constraint | slack |
|---|---|---|---|---|
| 16 | `B` window | `N^{-1} ≤ B ≤ 1` on `[s,t]` | D2 uses `B^{1/6} ≤ 1` (`st5_Bctl_le_one`, Step5Kit:362); hQ uses `B ≥ N^{-1}` (`(L^d|1-u|)⁻¹ ≤ Bparam`, so `B ≥ (WL)^{-d}`; merged: `N^{-2}`) | script: `N·B ≥ 1` at `n = 0..3`; `log_N(1/B(0)) = 0.71, 0.77, 0.78` (`n = 0,1,2`) |
| 17 | loss budget per conjunct | one `N^{ε}` from `≺`, one `N^{ε}` from `Ξ̂ ≤ N^{ε}Φ` (`Γ(ΓΦ)`); `ε` free | `Γ ≥ 1`, `Φ,Λ ≥ 1` | script ratio clause/RHS `≥ N^{2ε} = 18.4` (D1,D3,D4), `≥ 267` (D2) |
| 18 | `q(ε)` | `q ≥ 1/(2ε)` (script: `3.57, 3.85, 3.91` for `ε = 1/10`, `n = 0,1,2`) | `B^{-1/(2q)} ≤ N^ε` | `q = 5` closes all `n` (`B ≥ 1/N`) |
| 19 | Dec absorption | `D'' = D' + 1/𝔠` (`τ = 1`); `W ≥ N^𝔠` (`Admissible`) | `N W^{-D''} ≤ W^{-D'}` iff `N ≤ W^{1/𝔠}` | `𝔠 = 1/6`: `N W^{-6} = 2^{-9}` at `n = 0` |
| 20 | union over `j ≤ K_n` | `D₂ = D + max(C,0)`, `K_n + 1 ≤ N^C`; `u_j ∈ [s, v] ⊆ [s,t]`, `map_pathH_eq` (Walk.lean:598) | `(K+1) N^{-D₂} ≤ N^{-D}` | exact (0); measurability of `GoodSetN` needed to transfer (target 3) |
| 21 | number of events | `1 + (2k+2) + (k-1) + (k-2) + 3 + 2·2^k`; **no label factor** (labels, signs of Prec statements are inside `P`; RBM2D had `(2N)^{2k+2}` per clause, `GridGoodEvent:31-35`) | `≤ N` eventually (`HighProbAt.inter`/`biInter`, StochDomAt.lean:571,589) | `k` fixed, `N → ∞` |
| 22 | replaced RBM2D hypotheses | `MainIndHyp ↦ STFlow, STConStInd, 0 ≤ s < t ≤ lemT z, STLK s`; `KboundConcl ↦ STKbound, STKward`; `KcalDecay ↦ inst_stKcalDecay_admissible` (KDecay.lean:976, inside `stEtermDecay`); `GbEXPHypV3, Step2LocalPT ↦ STLocalEntryU`; `Step2DecayPT ↦ STGdecayW`; `DecayLoopPT ↦ STDecayLoopU`; `PT ↦ Prec` over `TimeIcc s t n` (union over `u` inside `P`, DECISIONS §39); `Bandwidth ↦ Admissible`; `M_u ↦ (Bctl)⁻¹`; `N = (WL)^d` | all inside `STIngR` (Step34Pins.lean:445) | `gridGoodN_holds` is `STIngR d STAny (fun sz E s t => …)` using `stSEforLn_holds` |
| 23 | measurability chain | `H ↦ loopFine/loopL (blockMat H) z I` measurable (`walk_measurable_loopL`, `_blockMat`, `_loopFine`, Walk.lean:780-800); `STmaxLM` is `Finset.sup'` of norms; the far clauses are `if (const) then {…} else univ`; finite `⋂` over `Fin j → Bool`, `Fin j → Zd d L` | `MeasurableSet (GoodSetN …)` without hypotheses | exit time: `lt_firstHit_grid_measurableSet` (Stop.lean:185); `gridExitTauN_le`, `mem_of_lt_`, `_eq_of_forall_mem` are `firstHit_le`, `lt_firstHit_imp` (Stop.lean:56,75) |

Findings: (F1) D2 carries `Φ²` and no additive `W^{-D'}`; D1 has no `(k-1)`; consumers ported from `AltLevelsQ:173` (`k²Γ(ΓΦ)`) must use the clause levels of rows 7-10 (paper-delta candidates `T2146a` (G1/G3/G4 dropped, hQ replaces G1), `T2146b` (levels of D1-D4, no additive term), `T2146c` (far clauses in `STdiamInf`)). (F2) hQ, hX, hY are new hypotheses of the pin (as RBM2D's `PT` ones), not registry premises: they hold at `Φ = 1` under `STLmaxU`, `STLKU` and `Λ = B(0)^{-1/(2q)}`. (F3) no clause needs a per-time or stopping-time law: stop condition of the ticket not triggered.

### (ii) One nondegenerate instance
`d = 3`, `sz0` (`Defs/Sizes.lean`), `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2^{21}`; `𝔠 = 1/6`, `𝔡 = κ = ε_flow = 1/10`; flow `z_n = 1/2 + i N^{-4/5}` (`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, Defs.lean:435), `E_n = lemE z_n = 0.5`; `s ≡ 0`, `t ≡ 1/16 ≤ lemT z_n` (`sixteenth_le_lemT`, Defs.lean:429), `v ≡ 1/32`, `K ≡ 4` (grid `u_j = j/128`, `j ≤ 4`), `K+1 = 5 ≤ N^C`, `C = 1`; `k = 2`, `q = 5`, `Γ = N^{1/10}`, `τ' = 1/2`, `D' = 1`, `Cd = 1`, `𝔠_d = 1/100`; `Φ ≡ 1`, `Λ_n = B_n(0)^{-1/10} = 2.82` (`≤ N^{1/10} = 4.29`). External hypotheses: `STKbound` (owed, KL7): limit computation `docs/reports/T2111-prove.md:72-79` (`max|𝒦^{(k)}|/B^{k-1}` = 0.93-1.16 for `W = 2..16`); `STConStInd` computed in part F; `STKward, STLK, STStep2Concl` are other gates' registered outputs (kept as hypotheses of the example, ticket); hX, hY, hQ as in rows 11-12 and 15 (at `H = 0`, `u = 0`: `X_m = 1.97-1.98 ≤ N^{ε}`, `Y_m = 1`). The good set contains `H_0 = 0` at `u_0 = 0` (sampling a random `H` at `N = 2^{21}` is not possible); `L = K`, `ee(0) = k·S_cc|z|^{-(2k+2)}W^{-2kd}` with `S_cc = 1/(1+2dg²)` (`sbKernel`, Block.lean:38), `|z| = 1`.

Command (scratch `scratchpad/T2146/check.py`, full output 42 lines, selection below):
`python3 check.py | grep -E "^PART|k= 2 |k= 4 |k=10 |n=0 L=|n=1 L=|n=0 u=0.0000 k=2|n=0 u=0.0625 k=4|all ratios|D2 check|q needed|n=0 k=2 |n=0 k=3 |n=0 B\(|n=4 B\(|monotone" | cut -c1-215`
```
PART A: lengths used by the RHS of the four conjuncts (X=Xi^L, Y=Xi^LK); hX needs X_m, m<=k+1; hY needs Y_m, m<=k
 k= 2 #n'=0 X-lengths=[1, 3] Y-lengths=[2] in[1,k+1]/[1,k]: True; (4): X_3, X_4q
 k= 4 #n'=1 X-lengths=[1, 3, 5] Y-lengths=[2, 3, 4] in[1,k+1]/[1,k]: True; (4): X_7, X_4q
 k=10 #n'=4 X-lengths=[5, 7, 9, 11] Y-lengths=[2, 3, 4, 5, 6, 7, 8, 9, 10] in[1,k+1]/[1,k]: True; (4): X_19, X_4q
PART B: sz0 (d=3), z0_n=1/2+i N^(-4/5), E_n=lemE z0, window s=0,t=1/16,v=1/32
 n=0 L=4 W=32 N=2.097e+06 E=0.50000 lemT=0.99999095>=1/16:True  B(0,1/32,1/16)=3.0987e-05,3.1986e-05,3.3052e-05 B<=1:True N*B>=1:True N^-2<=B:True W>=N^(1/6):True N<=W^6:True
 n=1 L=8 W=1024 N=5.498e+11 E=0.50000 lemT=1.00000000>=1/16:True  B(0,1/32,1/16)=9.3314e-10,9.6324e-10,9.9535e-10 B<=1:True N*B>=1:True N^-2<=B:True W>=N^(1/6):True N<=W^6:True
PART C: clause levels vs RHS of STSEforLnConcl with Xi:=levels (Phi=1, q=5, Lam=B(0)^(-1/(2q))), eps=1/10, Gamma=N^eps; ratio=clause/RHS must be >=1
 n=0 u=0.0000 k=2 B=3.099e-05 eta=0.9682 ratios conj(1) egt,(2) ksimLK,(3) elklk,(4) ee = 18.4, 18.4, 889, 18.4
 n=0 u=0.0625 k=4 B=3.305e-05 eta=0.9077 ratios conj(1) egt,(2) ksimLK,(3) elklk,(4) ee = 18.4, 18.4, 267, 18.5
 all ratios >= 1: True  min ratio: 18.379173679952565
 D2 check cnt*x^2+x<=k*x^2 for k=2..12, x in {1,2,8.3}: True
 n=0: log_N(1/B(0))=0.7132 (<=1); q needed for B^(-1/(2q))<=N^(1/10): q>=3.57
 n=1: log_N(1/B(0))=0.7692 (<=1); q needed for B^(-1/(2q))<=N^(1/10): q>=3.85
 n=2: log_N(1/B(0))=0.7828 (<=1); q needed for B^(-1/(2q))<=N^(1/10): q>=3.91
PART D: closure at n=0: Dec N^1 W^-(D'+1/c) <= W^-D' (c=1/6): N*W^-6 = 0.001953125  (<=1); union (K+1)=5<=N^C, C=1:  True ; D2=D+C: (K+1)N^-(D+C) = 5/N * N^-D <= N^-D
PART E: H=0,u=0: G=-1/z=m, L=K => Xi^LK_m(0)=1, D1,D2,D3,Va=0; ee(0)=k*S_cc*|z|^-(2k+2)*W^(-2kd); S_cc=1/(1+2d g^2); level G^2*Lam*B0^(2k)/eta0
 n=0 k=2 |z|=1.000000 |m|=1.000000 ee(0)=1.732e-18 level_D4=4.942e-17 ee<=level:True; Xi^L_m(0) m=2,3,k+1 = 1.9849, 1.9699, 1.9699 <= N^eps=4.287: True
 n=0 k=3 |z|=1.000000 |m|=1.000000 ee(0)=2.420e-27 level_D4=4.746e-26 ee<=level:True; Xi^L_m(0) m=2,3,k+1 = 1.9849, 1.9699, 1.9552 <= N^eps=4.287: True
PART F: instance window s=0,t=1/16,v=1/32,K=4: grid u_j = [0.0, 0.0078125, 0.015625, 0.0234375, 0.03125]  (K+1)=5<=N^1; STConStInd at cd=1/100 (s=0,t=1/16): B(t)^cd <= (1-t)/(1-s)=15/16 < 1
 n=0 B(1/16)^(1/100)=0.90197 <= 0.9375: True  Lambda_n=B(0)^(-1/(2q))=2.824 <= N^(1/10)=4.287: True  (q=5)
 n=4 B(1/16)^(1/100)=0.70840 <= 0.9375: True  Lambda_n=B(0)^(-1/(2q))=31.62 <= N^(1/10)=77.68: True  (q=5)
monotone B in u (STBctl_mono) at n=0: True
```
Part A shows that the lengths of `Ξ̂` entering the four conjuncts lie in `[1,k+1]` (`X`) and `[1,k]` (`Y`), for `k = 2..10`. Part C's ratios are `Γ²` (`18.4 = N^{0.2}`) for D1, D3, D4 and `≥ 267` for D2: the clause levels dominate the right sides of `STSEforLnConcl` with `Ξ̂ := level`. Part E checks `0 ∈ GoodSetN` only at `u = 0` (not for `u > 0`).

### Verdicts
- `GoodSetN` (target 1): PASS with the clause list of rows 1, 3, 6-10, 13-14 (G1, G3, G4 dropped: no consumer; D4's `Λ` through hQ). No clause of rows 1-14 is missing from the merged uniform statements.
- Exit times (target 2): PASS (generic `G`, `firstHit` lemmas as RBM2D).
- Measurability (target 3): PASS (row 23).
- `GridGoodN`/`gridGoodN_holds` (target 4): PASS with the hypothesis set hX, hY, hQ of rows 11-12 (replacing RBM2D's `PT` hypotheses) and the replacements of row 22; the exponents close (rows 16-21).

## (a′) Preflight corrections — Sun Oct  4 18:22:02 UTC 2026
No verdict of (a) changes.  Differences from the preflight tables (the first two are routes, verified by the build):
- Rows 6/19 (Dec closing): the proof takes `τ = 𝔠`, `D'' = D'+1` in `STDecayLoopU` and `N^𝔠 ≤ W` (`Bandwidth`): `N^𝔠 W^{-(D'+1)} ≤ W^{-D'}` (`gridGood_pow_absorb`), not `τ = 1`, `D'' = D'+1/𝔠`.
- Rows 16/D2 (`B ≤ 1`): obtained from `STConStInd` (`(B_t)^{𝔠_d} < 1`) and `STBctl_mono` (`ScaleFacts.lean:74`), not from `st5_Bctl_le_one` (`Step5Kit` is not imported).
- Row 15 (`0 ∈ GoodSetN` at `u = 0`) is a script check in (a) only; it is not a Lean statement here (see (d)).

## (b) Script output — Sun Oct  4 18:22:02 UTC 2026
### Build, axioms, scans
Sun Oct  4 18:20:13 UTC 2026
$ lake build RBM3D.Induction.GridGoodN 2>&1 | grep -E "GridGoodN.lean:[0-9]+:[0-9]+: (warning|error)|Build completed|Replayed RBM3D.Induction.GridGoodN|Built RBM3D.Induction.GridGoodN"
ℹ [3783/3783] Replayed RBM3D.Induction.GridGoodN
Build completed successfully (3783 jobs).
$ lake build RBM3D.Induction.GridGoodN 2>&1 | grep GridGoodN.lean | grep "depends on axioms"   # (per-line: name)
lines:       15; lines whose axioms are exactly [propext, Classical.choice, Quot.sound]: 15
Gauss.Sizes.gridGood_STmaxLM_seqHflow Gauss.Sizes.gridGood_STmaxLKM_seqHflow Gauss.Sizes.gridGood_STXiLM_seqHflow Gauss.Sizes.gridGood_STXiLKM_seqHflow Path.gridExitTauN_le Path.mem_of_lt_gridExitTauN Path.gridExitTauN_eq_of_forall_mem Path.gridExitTauN_measurableSet Gauss.Sizes.measurableGoodSetN Path.goodExitMeasN Gauss.Sizes.gridGoodN_holds Gauss.GridGoodNInst.grid_data Gauss.GridGoodNInst.tInst_lt_one Gauss.GridGoodNInst.gridGood_instance Gauss.GridGoodNInst.gridGood_instance_nonempty 
$ grep -nE "sorry|admit|native_decide|^axiom|^private axiom" RBM3D/Induction/GridGoodN.lean | wc -l
       0
$ wc -l RBM3D/Induction/GridGoodN.lean
    1249 RBM3D/Induction/GridGoodN.lean
$ git diff --stat main...t/T2146
 RBM3D/Induction/GridGoodN.lean | 1249 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1249 insertions(+)
### Registry pre-check and full build
$ lake env lean reg0.lean   # `import RBM3D` (library without the module); `#assert_rbm_axioms`
axiom audit: 4479 theorems, 1575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 89 (borrowed 0, owed 69, structural 20).
registry: 1 borrowed + 91 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ lake env lean reg.lean    # `import RBM3D` + `import RBM3D.Induction.GridGoodN`; `#assert_rbm_axioms`
axiom audit: 4494 theorems, 1588 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 89 (borrowed 0, owed 69, structural 20).
registry: 1 borrowed + 91 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ [RBM3D.lean temporarily with `import RBM3D.Induction.GridGoodN` after the last import; restored after] lake build 2>&1 | grep -E "error|Build completed|axiom audit:|premises found|registry:"
info: RBM3D.lean:192:0: axiom audit: 4494 theorems, 1588 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 89 (borrowed 0, owed 69, structural 20).
registry: 1 borrowed + 91 owed + 49 structural; 52 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (3893 jobs).
$ git status --short RBM3D.lean   # (empty: restored)
### Target statements (extracted by `python3 scratchpad/T2146/extract.py NAME:full|sig` from the file; `sig` stops at the end of the signature)
```lean
def GoodSetN (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | H.IsHermitian ∧
    (∀ m : ℕ, 1 ≤ m → m < k → STXiLKM sz n E u m H ≤ Γ * Φ) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a‖ +
          ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a - STKloop sz n E u σ a‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKM sz n E u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkM sz n E u H (loopOf σ a)‖ ≤
        Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtM sz n E u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ‖STeeM sz n E u H σ a a'‖ ≤ Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / etaT E u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖∑ l ∈ Finset.Icc 3 k, STksimLKM sz n E u H l (loopOf σ a)‖ +
          ‖STelklkM sz n E u H (loopOf σ a)‖ + ‖STegtM sz n E u H (loopOf σ a)‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append a a') : ℝ) →
        ‖STeeM sz n E u H σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'))}
def GridGoodNConcl (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 1 ≤ Λ n) → (∀ n, 1 ≤ Φ n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    ∀ q : ℕ, 1 ≤ q →
    Prec sz (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) (2 * k - 1) ω *
        (STXiL sz n (E n) (u : ℝ) (4 * q) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (q : ℝ))))
      (fun n _ _ => Λ n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k
          (((sz.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'})
def GridGoodN (d : ℕ) : Prop := STIngR d STAny (fun sz E s t => GridGoodNConcl sz E s t)
def gridExitTauN (s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) :
    PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) =>
    (G j)ᶜ.indicator (fun _ => (1 : ℝ)) (pathH sz s v K n j ω)) (1 / 2) (K n)
def goodExitTauN (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ)
    (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D')
def MeasurableGoodSetN (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ),
    MeasurableSet (sz.GoodSetN n E u k Γ Λ Φ τ' D')
def GoodExitMeasN (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ),
    MeasurableSet[filt sz j] {ω | j < goodExitTauN sz E s v K k Γ Λ Φ τ' D' n ω}
theorem measurableGoodSetN (d : ℕ) : MeasurableGoodSetN d := by
theorem goodExitMeasN (E s v : ℕ → ℝ) (K : ℕ → ℕ) : GoodExitMeasN sz E s v K :=
theorem gridGoodN_holds (d : ℕ) : GridGoodN d := by
variable {sz} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
theorem gridExitTauN_le (ω : PathΩ sz) : gridExitTauN sz s v K n G ω ≤ K n :=
theorem mem_of_lt_gridExitTauN {ω : PathΩ sz} {j : ℕ} (h : j < gridExitTauN sz s v K n G ω) :
    pathH sz s v K n j ω ∈ G j := by
theorem gridExitTauN_eq_of_forall_mem {ω : PathΩ sz}
    (hgood : ∀ j ≤ K n, pathH sz s v K n j ω ∈ G j) : gridExitTauN sz s v K n G ω = K n := by
theorem gridExitTauN_measurableSet (hG : ∀ j, MeasurableSet (G j)) (j : ℕ) :
    MeasurableSet[filt sz j] {ω | j < gridExitTauN sz s v K n G ω} :=
```
### Compiled nonempty instances (same file, §7)
```lean
theorem gridGood_instance (k : ℕ) (hk : 2 ≤ k) (hKb : STKbound sz0 (STflowE z0)) (hKw : STKward sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hL : STLmaxU sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) :
    HighProbAt (pathP sz0) sz0.size (fun n => {ω | ∀ j ≤ Kg n,
      pathH sz0 sInst vg Kg n j ω ∈ sz0.GoodSetN n (STflowE z0 n) (gridTime sInst vg Kg n j) k
        (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ))
        (max 1 ((sz0.Bctl n (sInst n)) ^ (-(1 / (2 * ((5 : ℕ) : ℝ))))))
        1 (1 / 2) 1}) := by
example : MeasurableSet (sz0.GoodSetN 0 (1 / 2) (1 / 32) 2 4 3 1 (1 / 2) 1) :=
  measurableGoodSetN 3 sz0 0 (1 / 2) (1 / 32) 2 4 3 1 (1 / 2) 1
example (j : ℕ) : MeasurableSet[filt sz0 j] {ω | j < goodExitTauN sz0 (fun _ => 1 / 2) sInst vg Kg 2
    (fun _ => 4) (fun _ => 3) (fun _ => 1) (1 / 2) 1 0 ω} :=
  goodExitMeasN sz0 (fun _ => 1 / 2) sInst vg Kg 0 2 (fun _ => 4) (fun _ => 3) (fun _ => 1) (1 / 2) 1 j
```
### Name-clash grep of the public names against main (script `clash.sh`)
main HEAD: 4f4612b
Kg 0
vg 0
GridGoodN 12
total hits outside GridGoodN.lean: 12
(public names checked: 29; every name except `GridGoodN` has zero hits; the hits of `GridGoodN` are the docstring mentions in StepDecompN.lean/LoopC2N.lean)
### Branch
$ git -C /Users/junyin/Lean_proof/RBM3D-wt/T2146 log --oneline -3; git status --short
9b4564f T2146: wrap a docstring line
19892fa T2146: prefix unpinned helper lemmas (rule E)
4b04492 T2146: GridGoodN, general-k instance, GridGoodNConcl docstring
### Ports (rewrite: structure and the `firstHit` lemma copied; RBM2D read-only)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h; git ... diff --stat c9a24cf HEAD -- RBM2D/Induction/GridGoodN.lean RBM2D/Path/Bootstrap.lean
9e0f275
 RBM2D/Induction/GridGoodN.lean | 847 ++++-------------------------------------
 RBM2D/Path/Bootstrap.lean      | 156 +-------
 2 files changed, 104 insertions(+), 899 deletions(-)
Sources at c9a24cf: `GridGoodN.lean:123-186` (exit times), `:671` (`measurableGoodSetN`), `:532-670` (measurability helpers), `Path/Bootstrap.lean:78` (`firstHit_eq_of_below`, reproved as private `gridGood_firstHit_eq_of_below`).
### Narrative
- All four targets are in `RBM3D/Induction/GridGoodN.lean` (line count above, below the ticket's 1800-line split threshold): §1 matrix-level controls `STmaxLM`, `STmaxLKM`, `STXiLM`, `STXiLKM` (the `gridGood_*_seqHflow` lemmas are `rfl`), §2 `GoodSetN`, §3 exit times (namespace `RBM.Path`), §4 measurability, §5 `GridGoodNConcl`, `GridGoodN`, `gridGoodN_holds`, §6 the levels at `Φ ≡ 1`, §7 instances.
- `GoodSetN` has the 9 clauses of preflight rows 1, 3, 6-10, 13, 14 (Herm, G2, Dec, D1-D4, Va, Vb).  Not clauses: RBM2D G1, G3, G4 (preflight rows 2, 4, 5: no consumer); `Ξ̂_{2k-1}(Ξ̂_{4q}/B)^{1/(2q)}` enters through the hypothesis `hQ`, `Ξ̂_m`, `m ≤ k+1`, through `hX`.  No clause was invented.
- Measurability: `GoodSetN` is a finite conjunction of level sets of measurable functions of `H` (`loopFine`, `STLIM`, `STLKIM`, `STksimLKM`, `STelklkM`, `STegtM`, `STeeM`, `STXiLKM`, from `walk_measurable_loopL/_blockMat/_loopFine`) and of the closed set `IsHermitian`; no hypothesis.  `goodExitMeasN` follows by `gridExitTauN_measurableSet`.
- `gridGoodN_holds`: `𝔠_d` and `STSEforLnConcl` come from `stSEforLn_holds d`; `STDecayLoopU` from `stDecayLoopU_of_step2`; the label decay of the four `ℰ` terms from `stEtermDecay` (every `σ`, `l ∈ [3,k]`).  Private `gridGood_whp_uniform` intersects 12 w.h.p. events (`hY`, `hX`, `hQ`, Dec for `j ≤ 2k+2`, D1 for every `l`, D2, D3, D4 at the given `q`, four label-decay families), uniform in `u ∈ [s_n,t_n]` and in the labels (no label factor), then does the clause arithmetic.  Private `gridGood_grid` transfers each grid index by `map_pathH_eq` and `measurableGoodSetN`, then takes the union over `Fin (K n + 1)` by `highProbAt_iInter` with exponent `max C 0`.
- The replacement of each RBM2D hypothesis (`MainIndHyp`, `KboundConcl`, `KcalDecay`, `GbEXPHypV3`, `Step2LocalPT`, `Step2DecayPT`, `DecayLoopPT`, `PT`, `M_u`) is written in the docstring of `GridGoodNConcl`.
- `STKbound`, `STKward`, `STLK s` are only passed on to `stSEforLn_holds`, which does not use them; the hypothesis `1 ≤ Λ n` (in the ticket's statement) is not used by the proof.
- No new premise: the registry scan finds 89 premises with and without the module and `RBM3D/Test/Axioms.lean` is unchanged; the full `lake build` with the module imported by a temporary edit of `RBM3D.lean` (restored) passes `#assert_rbm_axioms`.
- Instance `gridGood_instance k hk` (every `k ≥ 2`; examples at `k = 2` and `k = 4`): `sz0`, `s ≡ 0`, `t ≡ 1/16`, `v ≡ 1/32`, `K ≡ 4`, `q = 5`, `ε = 1/10`, `τ' = 1/2`, `D' = 1`, `Φ ≡ 1`, `Λ_n = max 1 (B_{0,0})^{-1/10}`.  Kept as hypotheses: `STKbound`, `STKward`, `STLK`, `STStep2Concl` (the `STIngR` premises) and `STLmaxU`, `STLKU` (registered owed pins).  The levels `hX`, `hY`, `hQ` are discharged from `STLmaxU`, `STLKU` by `gridGood_prec_XiL_one`, `gridGood_prec_XiLK_one`, `gridGood_prec_Q_one` (§6), so the hypothesis set of `GridGoodNConcl` is satisfiable modulo these pins.  `gridGood_instance_nonempty`: eventually in `n` some sample of the grid walk is in `GoodSetN` at every grid time.
- Imports: `SEforLn2`, `DecayLoopB`, `StepDecompN`, `Path.Walk`, `Path.Stop` (`LoopC2N`, `GridDuhamelN` come through `StepDecompN`).

## (c) Verified Mathlib names used (`#check` in `scratchpad/T2146/names_check.lean`, Sun Oct  4 18:22:08 UTC 2026)
`Finset.exists_mem_eq_sup`, `Finset.sup'_apply`, `Finset.sup'_le`, `Finset.measurable_sup'`, `Finset.measurable_sum`, `Finset.sum_le_card_nsmul`
`Measurable.ite`, `MeasurableSet.const`, `measurableSet_le`, `MeasureTheory.Measure.map_apply`, `Measurable.of_eval_matrix`, `MeasureTheory.measure_univ`
`Real.rpow_le_rpow_of_nonpos` (`0 < x → x ≤ y → z ≤ 0 → y^z ≤ x^z`), `Real.rpow_le_one`, `Real.one_le_rpow`, `Real.div_rpow`, `Real.rpow_sub`, `Real.rpow_natCast`
`Real.sqrt_eq_rpow`, `Real.sqrt_le_iff`, `Real.rpow_add'`, `Real.rpow_le_rpow_of_exponent_le`, `norm_sum_le`, `Nat.card_Icc`, `Filter.eventually_all`, `Filter.tendsto_atTop_mono'`
`Set.mem_ofPred_eq`, `Set.indicator_of_notMem`, `Fin.append_left`, `Fin.append_right`, `MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt`
Deprecated here: `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`).  Absent in RBM3D (grep): `firstHit_eq_of_below` (reproved privately); the unqualified `tendsto_atTop_mono'`, `measure_univ` are the `Filter.`/`MeasureTheory.` ones.

## (d) Open issues and paper-delta candidates
- Open: `0 ∈ GoodSetN` at `u = 0` (preflight row 15: consumers AzumaProxyN:1300, NonAltGood:996 at `c9a24cf`) is checked by script in (a) only, not proved in Lean; the instance proves eventual nonemptiness of the good event, conditional on the owed pins `STLmaxU`, `STLKU`, `STStep2Concl`.
- Open: `hX`, `hY`, `hQ` (levels `Φ`, `Λ`) are hypotheses of `GridGoodNConcl`, as RBM2D's `PT` ones; ST2-33/34/35, S3-10, S3-21 must supply them (at `Φ ≡ 1` they follow from `STLmaxU`, `STLKU`, §6).
- Open: consumers ported from RBM2D `AltLevelsQ:173` (`k²Γ(ΓΦ)`) must use the clause levels here (preflight F1).
- `T2146a`: `GoodSetN` drops RBM2D (G1) `Ξ^{(𝓛)}_{2k+2} ≤ ΓΛ`, (G3) `Ξ_mΞ_{k-m+2}M⁻¹ ≤ ΓΦ`, (G4) `Ξ^{(𝓛)}_{k+1} ≤ ΓΦ` as clauses; `Λ` enters through `hQ` (conjunct (4) of `lem:SEforLn` with a parameter `q ≥ 1` of `GridGoodN`), `Φ` through `hX`, `hY`.
- `T2146b`: levels of (D1)-(D4): `Γ(ΓΦ)B^k/η`, `Γ k (ΓΦ)²B^k/η`, `Γ(ΓΦ)B^k/η`, `Γ(ΓΛ)B^{2k}/η`, no additive `W^{-D'}`, no factor `(k-1)` in (D1) (RBM2D has `Γ(k-1)(ΓΦ)M^{-k}η⁻¹ (+ W^{-D'})`); conjunct (3) has no `M⁻¹` to absorb one `Φ`.
- `T2146c`: far clauses use the `ℓ^∞` spread `STdiamInf` (T2002b) with `ℓ_u W^{τ'}`; `GoodSetN`, `MeasurableGoodSetN`, `GoodExitMeasN` take `sz : Sizes d` (RBM2D `L W`, `d : Sizes`); `GridGoodNConcl` is the conclusion of an `STIngR`-shaped pin (`GridGoodN d`), the RBM2D hypotheses `MainIndHyp` ... `PT` being replaced as in its docstring.
