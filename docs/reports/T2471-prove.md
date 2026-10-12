Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 19:54:51 UTC 2026
Base `main` d0d9fe0f. **T2460 is merged** (ad52b370, `docs/queue/T2460.state` 19:33:28): `baGridBridge_holds` is on main (`BA/GridMartBA.lean:538`), so 6 (b) is in this row. Scratch: scratchpad `T2471/` (numpy, `*.py`). No Lean written.
**Decisions.** D1 route **(i)** (census below: every band-only row becomes a field of K/Inc/window, BA discharge merged or ≤ 400 lines). The BA cross-label QV **is of the band's form** (`QVPropagated`, `Path/QVIdentity.lean:410`; (v)): ticket condition (7) is not met, the 1b stays `prover-hard`. Central **2,960** lines (1,530 Chain + 1,430 BA) **> 1,950: the pre-signed split fires** (P1b-1 = the two Chain files, P1b-2 = the BA leaf); each half < 1,950, central < 3,900, so no third row. All seven targets PASS (end).
### (i) Exponent table  (m = 2: two slots, two cuts; N = `sz.size n`; ND = N^D)
| quantity | value (source) | constraint | slack |
|---|---|---|---|
| CK (clause 4) | 9m+3D+22 = **3D+40** (D=1: 43) (`DifREP3.lean:2343-2346`); TL one-slot CK = 3D+40 (`TwistGridWTail2:1236`), equal | K ≥ N^CK ⇒ Δ·N^{9m+22}·ND³ ≤ 1 (`difRep3_tail_at` `:2245`) | assembled CK = max(Rem 6 (`TwistGridRem2:397`), Tail 2D+20 (`TwistGridTail2:306`), 3D+40) = 3D+40; over 2D+20 by D+20 |
| C′, P | C′ = 4m+D+6 = D+14 (D=1: 15), P = ⌈N^{C′}⌉, K-free (`tail_at`) | P+1 ≤ 3·N^{4m+6}·ND = 3N^{14}ND | — |
| C₀ | 11 (`TwistGridRem2:395`), unchanged | `Rem` := residual at every n (UN-C5, `CONTROL.md` H256 (3)); clause 2 via `twRem` | none needed |
| window | s≡1/10 < t≡1/2 ≤ 2/3 ≤ T0 ≤ 25/36 (`t0_sz0` `FlowPins:1227`; Im m ≤ 5/6 `:1123`; Im m+Im z = 6/5 `:1117, 1127`) | 0≤s≤t≤T0<1; (1−u)⁻¹ ≤ 16N and η_u ≥ 1/(16N) for u ≤ t | (1−t)⁻¹ = 2 vs 16N ≥ 3.3e7; general BAFlow: TL derivation `TwistGridWTail2:1251-1276` (needs N^ε ≥ 1/(8κ), eventually) |
| shift budget (B1) | c_shift·N^{4m+4}·Δ ≤ ND⁻¹/2 (`:1946`) | 2c_shift = 6.76e15 ≤ N | N-exponent 5m+18+2D = 30 |
| f2 budget | c₃·ρ₁ ≤ ND⁻¹/4 (`:1969`) | 4c₃(1) = 1.80e16 ≤ N | N² |
| f1 budget | (`:1997`) | N ≥ 64m2^m+128m2^m·VQ(1) | N^{2m+3.5+D/2} = N^8 |
| Y budget | (P+1)N^m·4ΔP_Y/(ρ√δ)² ≤ ND⁻¹/4 (`:2095`), P_Y = 2000((32N)^m C₂)²N⁸, C₂ = m(m+1)N(16N)^{m+2} | 1536·P_Y(1) = 4.98e23 ≤ N | N² (m-free; with f2 the smallest polynomial slack) |
| Z budget | 24(2VQ(1)+2)N^{9m+9}ND³·e^{−N^{2ε′}/(256m)} ≤ 1 (`:2193`) | eventual; ε′=1/10: first holds at sz0 index n=21 (N=3.06e30, `thr.py`) | N₀(2) = Cbig = 4.98e23 (`inst.py`); smaller ε′ later |
| ε′/2 shift (6 (a) clause 3) | ‖twEEk‖ ≤ 2‖STEEMg‖ (H3′, constant 2 sharp, `T2460-prove.md` (a)) | N^{ε′/2} ≥ √2 ⟸ N ≥ 2^{1/ε′} | ε′=1/10: N ≥ 2^10; N_0 = 2^21 |
| class fields Q1, Q2 (pure N-form) | ‖STeeMg_u(H)‖ ≤ 2N(16N)^6; ‖STeeMg_{u′}−STeeMg_u‖ ≤ 12·16^7·N^8·(u′−u); H Hermitian, η_u ≥ 1/(16N), \|z_{u′}−z_u\| ≤ u′−u (\|m\| ≤ 1, `BAm_norm_le_one` `Ward:136`) | the band constants m N(16N)^{2m+2} (`DifREP3:1437`), m(2m+2)16^{2m+3}N^{2m+4} (`eeShiftErrN` `NQGood1:982`) | `crude.py`: ratios ≤ 8.2e-10 / 2.1e-11 (below) |
| external hypotheses | none: every input is merged | TEAM §8 lesson 14: no limit owed | — |
### (ii) One concrete instance
Data: d=3, sz0 (`Defs/Sizes.lean:260`: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6, N=(WL)^3), `flow_sz0` at (κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10) (`FlowPins:1214`), s≡1/10 < t≡1/2, D=1, ε′=1/10, K_n=⌈N^43⌉+1; T0∈[2/3,25/36] from the Lean bounds 4/5 ≤ Im m (`mS_im_half` `:1147`), Im m ≤ 5/6, Im m+Im z=6/5; lam0=√T0·lam. Command `cd scratchpad/T2471 && python3 inst.py; python3 thr.py; python3 band.py`:
```
m=2 D=1 eps'=1/10: CK=9m+3D+22=43, C'=4m+D+6=15, P=ceil(N^15), TL one-slot CK=3D+40=43
constants at N=1: cShift=3.378e+15 c3=4.504e+15 VQ=3.518e+13 PY=3.243e+20  N0(m)=Cbig=4.981e+23 (log2=78.7)
n= 0 L=4 W=32 lam=1/64 N=2097152 (2.097e+06) lam0 in [1.276e-02,1.302e-02]>0 K_n=ceil(N^43)+1 has 272 digits
      fail: ['N>=Cbig (budgets, eventual)']
n= 1 L=8 W=1024 lam=1/4096 N=549755813888 (5.498e+11) lam0 in [1.993e-04,2.035e-04]>0 K_n=ceil(N^43)+1 has 505 digits
      fail: ['N>=Cbig (budgets, eventual)']
n=10 L=44 W=5153632 lam=1/113379904 N=11659991713824860234842112 (1.166e+25) lam0 in [7.201e-09,7.350e-09]>0 K_n=ceil(N^43)+1 has 1078 digits
      fail: []
budget slacks (N-exponent beyond N^-D): shift 30  f2 2  f1 8.0  Y 2;  2cShift=6.76e+15 4c3(1)=1.80e+16 1536PY(1)=4.98e+23
eventual budgets (N>=Cbig, Z budget; D=1, eps'=1/10) first hold at n=21, N=3.057e+30; n=10 (N=1.2e25) is below
n= 0 N=2.097e+06 Im z0=8.764e-06  msc(z0)=-0.249999+0.968241j  lemT=0.999991 >= 1/16: True
n= 1 N=5.498e+11 Im z0=4.054e-10  msc(z0)=-0.250000+0.968246j  lemT=1.000000 >= 1/16: True
n=10 N=1.166e+25 Im z0=8.844e-21  msc(z0)=-0.250000+0.968246j  lemT=1.000000 >= 1/16: True
```
Reading: the `fail` entries at n=0,1 are the *conclusion's* eventual thresholds (budgets), not hypotheses; every hypothesis of T2/T4/T6 (flow datum, window s<t≤T0, D, K, and the bridge, supplied by `baGridBridge_holds`) holds at n=0,1,10; K_n is forced by the pin (∀K ≥ N^CK), not by the identities. Band (`DifREP3Inst`, `DifREP3.lean:2386-2412`; `Induction/Defs.lean:413, 429-439`): z0 n = 1/2 + i N^{-4/5}, `flow_z0` (1/10,1/10,1/6,1/10), s≡0, t≡1/16 ≤ lemT(z0 n), K≡4 (Δ=1/64).
### D1 census (reuse of the band route; K kernel, I per-step increment, Q proxy, M model-free, B band-only)
| band part (`DifREP3` lines; regex decl count) | class | generic form |
|---|---|---|
| §1-2 vocabulary, transfer (85-186; 7) | B (`uKerQ`, `STeeUQM`, `zeroModeSet`, `sz.lam`) | Q=∅ ⇒ `uKer`/`STeeUMg`/`T2471_WTail2`; transfer ⇒ `Step2Gen_UN_comp` (`GridDuhamelGen:99`, K1) |
| §3a kernel algebra (187-296; 8) | B (`mSigma`, `\|E\|≤2`, `SB`) | fields K2 (row sums), K4 (conj) |
| §3b sum/prod (298-397; 4), §4 grid/coarse (718-834; 11), §5 Doob (836-936; 2), §8 budgets (1912-2171; 11), §9 `eventually_Z`, `rpow_CK`, `Cbig` | M | `open private` (list in row (x)); §8 reused verbatim: the classes state Q1/Q2 in band N-form |
| §3c transfer (399-589; 6) | K | copy-adapt on K1-K3: `:420` ⇒ K3; `:444` (f1) ⇒ K3; `:515` ⇒ K1+K3+K2 (uKer(u,w₂)−uKer(u,w₁) = (uKer(w₁,w₂)−1)·uKer(u,w₁), row sum ≤ (w₂−w₁)(16N)² ≤ band 4(16N)²(w₂−w₁)) |
| §3d STee (591-716; 4) | Q | `:607` ⇒ Σκκ̄·STeeMg via K4; `:627`, `:645` ⇒ Q1 + K2/K3 |
| §5b Y tail (938-1086; 2) | I | copy-adapt on Inc-Y (TL twin `TwistGridWTail_Y_tail`, `WTail:1742`, 80 lines) |
| §6 Z part (1088-1428; 22) | B (defs 1128-1164 read `uKerQ`, `pathH sz`, `E n`), Q (`:1211` shift), I (`:1354` mgf), M (`:1397` peel) | defs on `Step2Gen_uKer`/`Cm.Hpath`; mgf ⇒ Inc-Z; peel = `difRep2_peel` (`DifREP2:478`) |
| §7 pathwise/core (1430-1910; 6), `tail_at` (2245) | B only via `hη`, `hE` | window field + Q1/Q2; copy-adapt at m=2, Q=∅ |
| per-step layer | I/Q | `ZvecN`/`YvecN` (`StepDecompN:185-192`) ⇒ `stepZCN` of Φ; `YMomentsN` (`GridAssemblyN:173`) ⇒ `TwistGridWTail_Y_fields` (`WTail:1419`); `hermTestFunLoopN` (`LoopC2N:469`) ⇒ `LoopC2N_second_deriv_bound` (`:424`, z-generic) + shift by g₀Ψ; `eeShift`/`norm_STeeM_shiftN_le` (`QVIdentity:1115`, `NQGood1:996`) ⇒ `norm_loopL_zshiftN_le` (`NQGood1:676`); `difRep2_norm_STeeM_le_N` (`DifREP2:1277`) ⇒ `norm_loopM_le_sharp` (`GLoopFlow:903`) |
**Route (i).** Rule: every B row has a field. BA discharge: K1-K4 and window merged (below); new: Z-mgf with the cross-label QV ≈ 300, Y-fields + hermTest ≈ 230, Q1+Q2 ≈ 150 lines, each ≤ 400 (basis: `T2460-prove.md` (b): H3′ diagonal case 248 lines). No stop rule fires.
### Hypothesis table (viii) and probe spec (iv)
| premise (D2 field) | band discharge | BA discharge |
|---|---|---|
| K1 `Step2Gen_USemigroup C n` | `step2Gen_USemigroup_band` (`GridDuhamelGen:58`, `\|E n\|≤2`) | `BAuKerSemigroup_holds` (`TwistGrid:199`) via `Step2Kern_uKer_BA` (`Step2Kern:112`, Im(E+m)=Im m ≥ κ), `BAflow_real` (`GreenSchur:59`) |
| K2 Σ_b‖uKer(v,w)(a,b)‖ ≤ (1−v)/(1−w), 0≤v≤w<1 | `norm_uKer_le` (`Evolution:114`) + `sum_norm_row_le` (`:78`) | `TwistGridWTail_sum_norm_twU_le` (`WTail:104`) via `twU_eq_uKer` (`TwistGrid:214`) |
| K3 Σ_b‖uKer(s,t)(a,b)−δ‖ ≤ \|t−s\|(1−t)⁻¹, 0≤t<1 | `difRep3_sum_norm_uKer_sub_one` (`:420`, private) | `TwistGridWTail_norm_twU_sub_one_le` (`:112`) + `sum_norm_row_le` |
| K4 uKer(!σ,!σ′) = conj uKer(σ,σ′), 0≤w<1 — **confirmed needed**: `difRep3_STeeUQM_eq` (`:607`) rewrites the second product as conj of the first | `difRep3_conj_uKer` (`:226`, private) | `TwistGridWTail_twU_conj` (`:83`) |
| Inc-Z: ∀κ r, Re/Im of Σκ_b Z_b integrable, cond. mgf ≤ exp(r²Δ·2Re(Σκκ̄ STeeMg_{u_{j+1}}(H_j))/2) | not required (dispatcher answer (5)); model `difRepTail_condMGF_Z` (`DifREP2:1404`) | `TwistGridWTail_condMGF_generic` (`:1333`, ι=Fin 2→Zd) + cross-label QV (v) + `xi_ae`-type identification (`:1526`) |
| Inc-Y: ξ−Z centred, L², E(Re Σκ Y)² ≤ 4(Σ\|κ\|C₂/2)²Δ²·768N⁸ | `YMomentsN` | `TwistGridWTail_Y_fields` (`:1419`), Φ_b = loopFine(g₀Ψ+·, z_{u_{j+1}}) hermTest |
| Inc-Q0/Q3: `Hpath` Hermitian, adapted/measurable, `IsProbabilityMeasure Pp`; Q1, Q2 (table (i)); window ∀u≤t: (1−u)⁻¹ ≤ 16N, η_u ≥ 1/(16N) | `pathH_isHermitian` (`Walk:98`), `isProbabilityMeasure_pathP` (`:94`), `difRep_flow_bounds` (`DifREP1:600`) | `PsiI_isHermitian` (`BlockAnderson:65`), `pathH_measurable_filt` (`Stop:159`); `EMn2BA_one_sub_T0` (`EMn2BA:111`), `EMn2BA_mF_data` (`:125`), `BAm_norm_le_one` |
Probe spec (the probe compiles; no Lean at 1a): `Hyp d Flow mk T0` = ∀ datum, window, **∀K inside** the eventual set (`∀ K, K n ≠ 0 → Inc …`; the BA eventual set is K-free), so `CK` stays before `K`; `Inc`/`Hyp` in band N-form so §8 is reused verbatim.
### (v) Target 5 and the cross-label QV (formulas, numerics)
G_s = G(σ_s), Q₁^b = G₀E_{b₀}G₁E_{b₁}G₀, Q₂^b = G₁E_{b₁}G₀E_{b₀}G₁; ∂_X L_b = −tr((Q₁^b+Q₂^b)X) (BA path = `sz.withLam 0`, S=δ: `TwistGridWTail_svarF_zero` `:1117`). `STeeLoop` k=1,2 at m=2 (`Step34Pins:152`) are tr(Q_k^b E_c (Q_k^{b′})^* E_c): **per-cut cross-label identity** W^{-d}Σ_{[x]=[y]} Q_k^b(y,x)·conj Q_k^{b′}(y,x) = W^d Σ_c loop6_k(b,b′;c,c), any (b,b′), any charges, H Hermitian. With κ: Σ_c gvar_c|Σκ_b∂_cL_b|² = Σ wS|Σκ(Q₁+Q₂)|² ≤ 2Σ_k Σ wS|ΣκQ_k|² = 2 Re ΣΣ κκ̄ STeeMg (Cauchy–Schwarz, 2 = m): exactly `QVPropagated` (`QVIdentity:410`) with EE → STeeMg. Equality fails (cross term), the diagonal case is T2460's H3′. `python3 qv.py; python3 lists.py; python3 crude.py` (toy lattice: 3 blocks × 2 points, random Hermitian H, complex z, κ):
```
cases (sigma x labels, half with a1'!=a1): 960
per-cut cross-label identity max |lhs-rhs| (k=1,2, all 4 charge pairs): 2.97e-16
derivative formula d loop = -sum (Q1+Q2)^T X, max err (finite diff 1e-6): 5.05e-10
exact QV == sum of cut terms (no cross term) in 0 of 960 cases
CS bound  sum_c gvar|sum kap dL|^2 <= 2 Re sum kap kap* STeeMg: violations 0  min slack 3.156e-04  max ratio 0.999
STEEkMg k=0 list == STeeLoop k=1 (a'=a): True ; k=1 list == STeeLoop k=2: True
cutGlueL 1 2 x == (s, [x,a1]): True ; cutGlueR 1 2 y == (s, [a0,y]): True
Icc 1 2 pairs (k,l'>k): only (1,2) -> [(1, 2)] ; Icc 3 2 empty: True
1200 cases; max |STeeMg|/(m N (16N)^6) = 8.20e-10 (<=1); max |shift|/(m(2m+2)16^7 N^8 (u'-u)) = 2.14e-11 (<=1)
```
Target 5 = algebra from F1 `LM = LIM∘KLloopOf` and F2 `K = KI∘KLloopOf`, both definitional at `baStep2Mat` (`loopM_eq_loopL`, `baStep2Mat_KI` `Step2BA:89`; `baFM.K = BAKloop`, `FlowPins:324`): (5a) `STgAg = STgANg`; (5b) `STthetaOpg` is `Step2Gen_ThetaN` at m=2 (same text), `STELKLKMg`/`STEGtMg` = `STelklkMg`/`STegtMg` by `KLloopOf_cutL/R/cutGlue1/2` (`Step2Iterate:1625-1657`), `Icc 3 2 = ∅`; (5c) `STeeLoop_one/two` (`:1686, 1691`) + `sum_pair`. All true, no counterexample; no generic list-identity lemma exists on main (grep `STELKLKMg|STEGtMg|STEEMg`: definitions, band `rfl` bridges `Step2Gen:424-444`, bounds), ≈ 130 lines, BA-only. `filt sz j = filt (sz.withLam 0) j` by `rfl` expected: `SeqCoord` reads L, W only (`FineModel:156`), `withLam` changes `lam` (`Sizes:182`); the probe confirms.
### (vi) Target 6
Clause 1: `Rem` := A_k−A_0−ΔΣSTgDriftNg−Mart at **every** n, `Mart(k)` = Σ_{j<k}`martIncNg` (`GridDuhamelGen:198`) — a ring identity (UN-C5; target 5 not needed here; 'telescoping using target 5' in the ticket is not required). Eventually in n (Bridge H1, H2 at j+1 ≤ k ≤ K n): ω′ ↦ STgAg_{j+1}(a) and ω′ ↦ twAk_{j+1}(a₀) are equal as functions, so the condExps are equal: `martIncNg` = `twMartInc`(σ,a₁,a₁)(a₀) for **every** ω (not only a.e.), hence Mart = `twMart`, and Rem = Σ_j(E[A_{j+1}|F_j]−A_j−ΔDrift_j) = `twRem` (H1, H2, (5b)). Clause 2: `baTwistGridRem_holds` (C₀=11, CK=6). Clause 3: pin event(ε′) ⊂ TL event(ε′/2) (H3′, (5c), N^{ε′/2} ≥ √2) then `baTwistGridTail_holds`. Clause 4 = `baGridWTail2_holds`. CK = max = 3D+40. T2460: `BAGridBridge` body == `T2471_Bridge` body (script, whitespace-normalised: True, 851 = 851 chars), so 6 (b) = `baGridRepNAt2_of_bridge d (baGridBridge_holds d)`; `BAGridBridge d` may replace the inline hypothesis (defeq; concluded by `baGridBridge_holds`, so the premise scan stays quiet).
### Fill-in table (CONTROL H250 (4); rows give a line of this section or the answer)
| # | deliverable | line / answer |
|---|---|---|
| (i) | exponent table | lines 5-19 above: CK = 3D+40 (TL one-slot 3D+40), C′ = D+14, P, budgets with slacks |
| (ii) | instance + script | lines 20-37: sz0/zSeq n=0,1,10 (N, lam0, K_n digits), eventual thresholds (first n=21 for ε′=1/10), band `DifREP3Inst` data |
| (iii) | D1 census, route | lines 38-50: route (i) |
| (iv) | D2 texts compiled | n/a at 1a (no Lean; the probe compiles); spec lines 51-61 (K1-K4 confirmed, `∀K` inside, N-form fields) |
| (v) | target 5, cross-label QV | lines 62-75: formulas; 960 label/charge cases (cut identity err 3e-16, all 4 charge pairs, b₁≠b₁′ in half), 160 weighted CS cases (0 violations), 1,200 crude/shift cases; list identities true; `filt` rfl expected |
| (vi) | target 6 | lines 76-77; T2460 merged ad52b370, bridge text equal, `baGridBridge_holds` `GridMartBA:538` |
| (vii) | UBA-C1 table | no crossing, not triggered: grep of check lines 165-300 for `sz.lam\|withLam\|lam0\|BAflowLam0`: `T2471_GridRepN2`/`T2471_Bridge` read `BAflowLam0` only (the carrier's g₀), `T2471_WTail2` and the classes read `Step2Gen_uKer`, `sz.size n`; the R1 literal (check:262) is the only `sz.lam` hit, unused; X1-C1 grep (`\|E\|`, `lemT`, `STFlow`, `STflowE`) hits only the band-bridge shape (check:227-228) |
| (viii) | hypothesis table | lines 51-61 |
| (ix) | premise scan, registry | none: `scanPremises` (`Test/Axioms.lean:447`) flags a Prop-def assumed and never concluded; `Hyp` assumed by `stGridWTail2gL_of`, concluded by `gridRepTailGen_hyp_BA` (4); `Ker` concluded by 3 (b); the bridge is inline or `BAGridBridge` (concluded by `baGridBridge_holds`); no line needed |
| (x) | `open private` | `DifREP3`: 301, 306, 316, 339 (sum/prod), 600, 726-767, 787-807 (grid, coarse, c₃), 845, 859 (Doob), 1437-1444, 1671, 1921-1939, 1946-2146 (budgets), 2179-2236 (asymptotics); `LoopC2N`: 116, 365, 376, 424; copies (adapt): `DifREP3` 420, 444, 494-645, 946-1086, 1128-1428, 1457-1910, 2245; BA leaf: TL private jets `TwistGridWTail_hasDerivAt_Gres` (`:459`), `_hasDerivAt_line` (`:446`), `_isHermitian_add_realSmul` (`:453`) |
| (xi) | layout | `GridRepTailGen` imports `Chain.GridDuhamelGen`, `Path.DifREP3`; `GridRepTailGen2` imports it; `GridRepTailBA` imports `Chain.GridRepTailGen2`, `BA.TwistGridWTail2`, `TwistGridTail2`, `TwistGridRem2`, `GreenSchur`, `GridMartBA`, `EMn2BA`, `Induction.LoopC2N`; new files have 0 importers; no `BA/*` direct import in `Chain` (Chain deps: `Step2Gen`, `GridDuhamelGen`, `Path/DifREP*`, `Kernel/Evolution`) |
| (xii) | lines, 2.6×, split | table below: central 2,960 > 1,950 ⇒ split; files 790 / 740 / 1,430 < 1,800 (no reserve file) |
| (xiii) | name clash | `git grep` of `GridRepTailGen\|GridRepTailBA\|TwistGridQTail\|STGridWTail2gL\|stGridWTail2gL_of\|bandStep2_STGridWTail2\|gridRepTailGen_hyp_band\|gridRepTailGen_hyp_BA\|baGridWTail2_holds\|baGridRepNAt2_of_bridge\|baGridRepNAt2_holds\|T2471_` in `RBM3D/*.lean`, `RBM3D.lean`: 0 hits on main (d0d9fe0f) and on all 470 `t/*` branches (471 refs, parsed), incl. t/T2460, t/T2471; `baGridRepNAt2_holds` appears only in `docs/tickets/T2460.md` (2) and `T2471.md` (5) |
**D3 sizes** (basis: band sections above; TL one-slot twin 3,156 lines; T2460 landed 747 vs 760 central; 2.6× = TLC-4 upper reference)
| target | central | 2.6× | file |
|---|---|---|---|
| 1 classes 90; 2 generic clause 4: kernel 180, STee 110, Y 150, Z 260, pathwise+core 420, tail_at+statement 150 = 1,270; 3 band (a) 90 + (b) 80 = 170 | 1,530 (3,978) | | `GridRepTailGen` 790 (2,054), `GridRepTailGen2` 740 (1,924) |
| 4 BA clause 4: K 120, Φ+hermTest+C₂ 130, cross-label QV 300, Q1/Q2 150, Z/Y assembly 150, window+statement 70 = 920; 5: 130; 6: 260; 7: 120 | 1,430 (3,718) | | `GridRepTailBA` 1,430 (3,718) |
Split: P1b-1 = Chain files (1,530), P1b-2 = BA leaf (1,430), total 2,960 (7,696 at 2.6×); the 2.6× reference exceeds the 2,000 stop line for every file, the central does not; if the leaf passes 1,800, targets 6-7 (≈ 380) move to the reserve `GridRepTailBA2` (no REQ).
### Verdicts
* T1 classes PASS. T2 `T2471_WTail2`/`stGridWTail2gL_of` PASS (true statement; CK = 3D+40, every budget closes, slacks above). T3 band bridge PASS ((a) iff, (b) Ker; (c) dropped by dispatcher answer (5)). T4 `baGridWTail2_holds` PASS (largest BA field ≈ 300 ≤ 400). T5 list identities PASS (true). T6 (a), (b) PASS (T2460 merged). T7 instances PASS.
* Not blocking, for the probe/1a-audit: `filt` rfl; `∀K` inside `Hyp`; 6 (a) head `BAGridBridge` vs inline. Paper-delta: none new (H3′ is `T2460a`). Role: `prover-hard`.
## (a′) Preflight corrections — Mon Oct 12 21:00:15 UTC 2026 (1b, `prover-hard`)
The verdict of (a) stays PASS. One statement of (a) is corrected; the delivered D2 shapes are listed.
* (a) (ix) says the premise scan needs no registry line. That holds for the whole row, not for P1b-1 alone: under the pre-signed split P1b-1 merges first, and `GridRepTailGen_Hyp` (assumed by `stGridWTail2gL_of`) is concluded only by target 4 (P1b-2). Measured on the 1b's first full state (the band `Inc` assumed, not proved): `import RBM3D` + `import RBM3D.Chain.GridRepTailGen2` + `#assert_rbm_axioms` failed at 20:43:13 UTC with `axiom audit: 3 premise(s) that no theorem of this development proves are in none of … : [RBM.BA.GridRepTailGen_Zfields, RBM.BA.GridRepTailGen_Yfields, RBM.BA.GridRepTailGen_Inc]`. Resolution without a registry line (`Test/Axioms.lean` untouched): P1b-1 proves the band discharge of every class (`gridRepTailGen_zfields_band`, `_yfields_band`, `_inc_band`, `_hyp_band`, File 2 l.691-837), so each class and `Hyp` is concluded by a theorem; the pre-check passes (exit 0, (b)). This is the ticket's 3 (b) in full, beyond dispatcher answer (5) (`Ker` only).
* D2 shapes as delivered (shapes not binding; `Ker` and `STGridWTail2gL` equal the check, (b)): `Inc` = Q0 (probability measure, `Hpath` adapted and Hermitian, `STeeMg` measurable in the matrix) ∧ (∃ Z Y, a.e. split `martIncNg = Z + Y`, `Zfields`, `Yfields`) ∧ Q1 ∧ Q2. `Yfields` has the second moment `Δ²·2000((Σ|κ|)C₂)²N⁸`, `C₂ = 6N(16N)^4` (the band constant of `AzumaProxyN_YfieldsW`; TL's `TwistGridWTail_Y_fields` bound `4((Σ|κ|)C₂/2)²Δ²·768N⁸` implies it). `Window` = `t n < 1 ∧ (1-u)⁻¹ ≤ 16N` (the probe's η conjunct is not used by the proof and is dropped). Consequences for P1b-2: (d) item 1.
## (a″) Probe compile — Mon Oct 12 20:13:39 UTC 2026  [condensed by the 1b to the 300-line limit of CLAUDE.md §6: the scratch listing of `unc5.lean` and the duplicate fill-in table are replaced by the summaries below; no result changed]
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2471`, branch `t/T2471`, base `main` d0d9fe0f. Probe `RBM3D/Probe/T2471Pins.lean`, 400 lines, committed `3044b47e`, never merged, no root import; merged names only. The untracked leftover of the interrupted first attempt (360 lines) was read, kept and completed. Section (a) is not edited; at the probe step it needed no correction (the 1b adds (a′) below (a)). Scratch (uncommitted): scratchpad `T2471/`.
### Compile (command, exit code, output; the empty output means no error, no warning)
```
$ date -u
Mon Oct 12 20:10:55 UTC 2026
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2471 && lake env lean RBM3D/Probe/T2471Pins.lean; echo "exit=$?"
exit=0
$ wc -l RBM3D/Probe/T2471Pins.lean
     400 RBM3D/Probe/T2471Pins.lean
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2471Pins.lean; echo "grep-exit=$?"
grep-exit=1
$ git log --oneline -1 -- RBM3D/Probe/T2471Pins.lean
3044b47e T2471: probe step (D2 texts, band/BA Ker discharge, target 5, UN-C5 clause 1)
```
### `#print axioms` (scratch copy of the committed probe, first 400 lines identical by `diff`, with the lines appended; exit 0)
```
'RBM.BA.T2471_bandStep2_STGridWTail2' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_ker_band' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_ker_BA' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_window_BA' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_STgAg_eq' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_STgDriftg_eq' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_STEEMg_eq' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_F1_ba' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_F2_ba' : [propext, Classical.choice, Quot.sound]
'RBM.BA.T2471_clause1' : [propext, Classical.choice, Quot.sound]
exit=0
```
### Statements against the check file (script `diffstmt.py`: whitespace-normalised bodies, `T2471-check.lean` vs the probe)
```
T2471_WTail2 check==probe: True 925 925
T2471_Bridge check==probe: True 851 851
T2471_GridRepN2 check==probe: True 118 118
Ker body check==probe: True 494 494
5a check==probe: True
5b check==probe: True
5c check==probe: True
```
`STGridWTail2gL` is `abbrev … := @T2471_WTail2` in the probe (l.121); the 1b defines it with this text. `GridRepTailGen_Ker` body = the check's D2 shape (True above).
### Probe index (line: item; all compile)
* l.27 `open private difRep3_sum_norm_uKer_sub_one difRep3_conj_uKer from RBM3D.Path.DifREP3` (K3, K4 band).
* D2 texts: l.40 `GridRepTailGen_Ker` (K1 `Step2Gen_USemigroup`, K2, K3, K4), l.50 `_Window`, l.56 `_Inc` (m = 2: `martIncNg = Z + Y`, mgf proxy `2 Re ΣΣ κκ̄ STeeMg`, `Y` second moment, crude bound Q1, `u`-shift Q2), l.90 `_Hyp` (`∀ K` inside the eventual set), l.99 `T2471_WTail2`, l.121-126 `STGridWTail2gL`, `stGridWTail2gL_of` and target 4 as statements.
* Target 3 (a) proved: l.133 `T2471_bandStep2_STGridWTail2 d : GridRepWTailNAt d 2 ↔ STGridWTail2gL d (STFlow …) (bandStep2Mat …) lemT` (route of `bandStep2_STGridRepNAt`; uses `bandStep2_martIncN`, `Step2Kern_UN_band`, `bandStep2_STeeUM`).
* Ker proved: l.145 `T2471_ker_band` (hyp `|E n| ≤ 2`); l.166 `T2471_ker_BA` (hyps `BAReal`, `0 < κ`); l.196 `T2471_window_BA` (hyps `t n ≤ BAflowT0`, `0 < N`, `1/(8κ) ≤ N^ε`; copy of `baTwistGridWTail_holds` `hη`, `hR16`, `TwistGridWTail2.lean:1251, 1269`).
* Instances (d = 3): l.221 Ker at `bandStep2Mat sz0 (STflowE z0)` all `n` (`DifREP3Inst` datum, `flow_z0`, `difRep_flow_bounds`); l.228 Ker at `baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)` all `n` (`flow_sz0` through `BAflow_real`, κ = 1/2); l.394 Window at the same BA datum, `t ≡ 1/2`, all `n` (`half_lt_t0`, `N ≥ 1`); l.364 `∀ d, T2471_Bridge d := baGridBridge_holds`; l.363 `BAGridBridge d = T2471_Bridge d := rfl`.
* Target 5 proved: l.238-240 `T2471_F1`, `_F2` (`LM = LIM ∘ KLloopOf`, `K = KI ∘ KLloopOf`), l.254 `T2471_STgAg_eq`, l.268 `T2471_STgDriftg_eq` (uses `Icc 3 2 = ∅`, `KLloopOf_cutL/R/cutGlue1/2`, `rfl` for `STthetaOpg = Step2Gen_ThetaN`), l.302 `T2471_STEEMg_eq`; l.314, 320 `T2471_F1_ba`, `_F2_ba`; the three statements at `baStep2Mat sz lam0 E` l.324, 329, 334 (all `d`, `sz`, `lam0`, `E`); l.340 `filt (sz.withLam 0) j = filt sz j := rfl`.
* Target 6 texts: l.345 `T2471_GridRepN2`, l.350 `T2471_Bridge`, l.366 `T2471_baGridRepNAt2_of_bridge_stmt`.
* UN-C5 (H256 (3)): l.373 `T2471_Mart` (`Σ_{j<k} martIncNg`), l.376 `T2471_Rem` (the residual `A_k − A_0 − Δ Σ STgDriftNg − Mart`), l.381 `T2471_clause1` (clause 1 of `STGridRepNAtgL`, every `n`, `ring`; no bridge, no target 5), l.388 (`Mart (j+1) − Mart j` is the telescoping difference of `T2471_WTail2`, `rfl`).
### UN-C5 eventual clauses 2-4 at `baStep2Mat` (scratch `unc5.lean`, uncommitted; 55 lines; imports `BA.GridMartBA`, `BA.TwistGridRem2`, `Chain.GridDuhamelGen`)
`lake env lean unc5.lean` (20:11:32 UTC): exit 0; `unc5_inc`, `unc5_mart`, `unc5_rem` depend on [propext, Classical.choice, Quot.sound]. `unc5_inc`: under H1 at `j+1` (as functions of `ω'`) `martIncNg … j σ ω a = twMartInc … (a 1) (a 1) j ω (a 0)` (`unfold martIncNg twMartInc; rw [hf, hA ω]; rfl`). `unc5_mart`: `Σ_{j<k} martIncNg = twMart … σ (a 0) (a 1) (a 1) k ω` under H1 for `j+1 ≤ k` (`Finset.sum_congr` over `unc5_inc`). `unc5_rem`: `A_k − A_0 − Δ Σ STgDriftNg − Σ martIncNg = twRem …` under H1, H2 and the target-5 identities (`baTwistGrid_decomp`, `linear_combination`). Clauses 2-3 then reduce to `baTwistGridRem_holds` and, with H3′ at ε′/2, `baTwistGridTail_holds` (not compiled; P1b-2).
### Greps over the probe (UBA-C1, X1-C1)
* `grep -nE "sz\.lam|withLam|lam0|BAflowLam0"`: 0 hits of `sz.lam`; hits at l.127 (target 4 statement), 166-212 (BA discharges), 227-228, 314-337 (target 5 at `baStep2Mat`), 340 (`filt`), 347-360 (`T2471_GridRepN2`, `T2471_Bridge`), 394 (BA window instance). None in l.40-121 (D2 texts, `T2471_WTail2`): no crossing, UBA-C1 not triggered.
* `grep -nE "\|E\||zt E|etaT|mSigma|STflowE|lemT|STFlow|mE|2 - κ|BA|ba[A-Z]|sz\.lam|withLam|lam0"` over l.40-120: no hit (grep exit 1).
* Chain-only imports: l.40-121 compiled alone after `import RBM3D.Chain.GridDuhamelGen`, `import RBM3D.Path.DifREP3` (scratch `d2_chain_only.lean`, 92 lines): exit 0 (20:12:21 UTC).
### Name-clash grep (`git -C /Users/junyin/Lean_proof/RBM3D --no-optional-locks grep -nE "GridRepTailGen|GridRepTailBA|TwistGridQTail|STGridWTail2gL|stGridWTail2gL_of|bandStep2_STGridWTail2|gridRepTailGen_hyp_|baGridWTail2_holds|baGridRepNAt2_of_bridge|baGridRepNAt2_holds|T2471_" HEAD -- RBM3D RBM3D.lean`)
Same pattern and pathspec on `main` d0d9fe0f and on `t/T2460` (79339380): 0 hits each (empty output, `wc -l` = 0). In `docs/tickets`: `baGridRepNAt2_holds` only in `T2460.md:17, 84` and `T2471.md`. On `t/T2471` the probe defines `GridRepTailGen_*`, `STGridWTail2gL`, `T2471_*`: probe-only, never merged.
Fill-in table (H250 (4)): every row is filled in (a) l.78-93 and was confirmed row by row in the 1a-audit (`docs/reports/T2471-1a-audit.md` §6).
### Open for the 1a-audit
* `GridRepTailGen_Inc` BA discharge and the cross-label QV are not compiled (outside the Probe line). No paper-delta candidate new; H3′ is `T2460a`.

## (b) Script output (1b, P1b-1 = targets 1-3: `Chain/GridRepTailGen.lean`, `Chain/GridRepTailGen2.lean`) — Mon Oct 12 21:00:15 UTC 2026
Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2471`, branch `t/T2471`, HEAD `d6f59884` (commits `a79521fb`, `539de62c`, `e9f80929`, `d6f59884` over the probe `3044b47e`). Scratch (uncommitted): scratchpad `T2471/` (`axsum.sh`, `greps.sh`, `clash.sh`, `stmtcheck.py`, `extract.py`, `precheck.lean`).
```
$ lake build RBM3D.Chain.GridRepTailGen RBM3D.Chain.GridRepTailGen2   (20:55:53 UTC)
exit=0   last line: Build completed successfully (3860 jobs).   lines with `error` or `sorry`: 0
$ wc -l RBM3D/Chain/GridRepTailGen.lean RBM3D/Chain/GridRepTailGen2.lean   # stop line 2,000 per file; (a) central 790 / 740 (2.6×: 2,054 / 1,924)
     795 RBM3D/Chain/GridRepTailGen.lean
     929 RBM3D/Chain/GridRepTailGen2.lean
$ lake env lean precheck.lean   # import RBM3D; import RBM3D.Chain.GridRepTailGen2; #assert_rbm_axioms   (20:56:14 UTC)
exit=0   first line: axiom audit: 13598 theorems, 4351 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).   lines with `error`: 0
$ bash axsum.sh   # #print axioms of the 50 public `theorem`/`def` declarations of both files; the targets below
exit=0
declarations printed:       50; with exactly [propext, Classical.choice, Quot.sound]: 50; other: 0
'RBM.BA.GridRepTailGen_Ker': [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailGen_Window': [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailGen_Inc': [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailGen_Hyp': [propext, Classical.choice, Quot.sound]
'RBM.BA.STGridWTail2gL': [propext, Classical.choice, Quot.sound]
'RBM.BA.stGridWTail2gL_of': [propext, Classical.choice, Quot.sound]
'RBM.BA.bandStep2_STGridWTail2': [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_ker_band': [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_inc_band': [propext, Classical.choice, Quot.sound]
'RBM.BA.gridRepTailGen_hyp_band': [propext, Classical.choice, Quot.sound]
'RBM.BA.GridRepTailGenInst.inst_stGridWTail2gL_band': [propext, Classical.choice, Quot.sound]
$ python3 stmtcheck.py   # whitespace-normalised bodies: docs/tickets/checks/T2471-check.lean vs File 1
T2471_WTail2 (check) vs STGridWTail2gL (GridRepTailGen.lean): body equal: True 925 925
signature (args, type) equal: True
Ker body (check shape l.211-218) vs GridRepTailGen_Ker body equal: True 494 494
$ python3 extract.py   # statements of targets 2 and 3 (File 2). D2 texts: File 1 l.54 Ker, 65 Window, 70 Zfields, 88 Yfields, 106 Inc, 123 Hyp, 133 STGridWTail2gL
GRTG2:625: theorem stGridWTail2gL_of {d : ℕ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
GRTG2:626:     {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}
GRTG2:627:     (hH : GridRepTailGen_Hyp d Flow mk T0) : STGridWTail2gL d Flow mk T0 := by
GRTG2:659: theorem bandStep2_STGridWTail2 (d : ℕ) :
GRTG2:660:     RBM.Ind.GridRepWTailNAt d 2 ↔
GRTG2:661:       STGridWTail2gL d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
GRTG2:662:         (fun _ z n => lemT (z n)) := by
GRTG2:672: theorem gridRepTailGen_ker_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| ≤ 2) :
GRTG2:673:     GridRepTailGen_Ker (bandStep2Mat sz E).toFlowFM n := by
GRTG2:826: theorem gridRepTailGen_hyp_band (d : ℕ) :
GRTG2:827:     GridRepTailGen_Hyp d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z))
GRTG2:828:       (fun _ z n => lemT (z n)) := by
$ bash clash.sh   # the 50 new names (stems GridRepTailGen*, STGridWTail2gL, stGridWTail2gL_of, bandStep2_STGridWTail2, gridRepTailGen_*, inst_stGridWTail2gL_band) in RBM3D, RBM3D.lean
main 8ea70675: files with a hit: 0
t/* branches scanned (all but t/T2471): 471; branches with a hit: 0
docs: main:docs/DECISIONS.md main:docs/queue/CONTROL.md main:docs/tickets/T2460.md main:docs/tickets/T2471.md
$ bash greps.sh   # 8 (a)-(d) and hygiene
$ grep -nE "sz\.lam|withLam|lam0|BAflowLam0" F1 F2   # 8 (a) UBA-C1
hits: RBM3D/Chain/GridRepTailGen.lean:0 RBM3D/Chain/GridRepTailGen2.lean:0 
$ grep -nE "<X1-C1 regex>" F1 F2   # 8 (b): hit counts and line ranges
RBM3D/Chain/GridRepTailGen.lean: hits 1; lines: 24 ... 24
RBM3D/Chain/GridRepTailGen2.lean: hits 38; lines: 658 ... 914
F2 hits with line < 655 (generic part, l.1-654 = sections 6-9): 0   (l.655+ = target 3, the band-bridge section 10, and the d=3 instances)
F1 hit l.24 (module docstring): `STeeUQM`, `etaT`, `zt E u` or `pathH` are copied and adapted under th
$ grep -nE "Ring\.inverse|Matrix\.of|cycProd|Ugen" F1 F2   # 8 (c)
hits: 0 if empty above
$ grep -nE "STGridRepNgL|∀ m|\{m |\(m :" F1 F2   # 8 (d)
(empty = 0 hits)
$ grep -nE "^import" F1 F2
RBM3D/Chain/GridRepTailGen.lean:6:import RBM3D.Chain.GridDuhamelGen
RBM3D/Chain/GridRepTailGen.lean:7:import RBM3D.Path.DifREP3
RBM3D/Chain/GridRepTailGen2.lean:6:import RBM3D.Chain.GridRepTailGen
$ grep -rln GridRepTailGen RBM3D RBM3D.lean
RBM3D/Chain/GridRepTailGen2.lean
RBM3D/Chain/GridRepTailGen.lean
RBM3D/Probe/T2471Pins.lean
$ grep -nE "sorry|admit|native_decide|^axiom" F1 F2
(empty = 0 hits)
$ git diff --stat main...t/T2471
 RBM3D/Chain/GridRepTailGen.lean  | 795 +++++++++++++++++++++++++++++++++
 RBM3D/Chain/GridRepTailGen2.lean | 929 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2471Pins.lean       | 400 +++++++++++++++++
 3 files changed, 2124 insertions(+)
$ git diff --stat main...t/T2471 -- RBM3D/Path RBM3D/Induction RBM3D/BA RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean RBM3D/Chain/GridDuhamelGen.lean
(empty: no merged file edited)
Instances (File 2 l.857-926, namespace `RBM.BA.GridRepTailGenInst`; `d = 3`, `sz0`, `z0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`; all deterministic hypotheses discharged, no hypothesis left): l.857 `example` Ker (every n), l.863 Window, l.869 Inc (every K, n), l.878 Hyp, l.884 `STGridWTail2gL` from `gridRepWTailN_holds` through 3 (a), l.888 and l.894 `GridRepWTailNAt 3 2` (through 3 (a); and through `gridRepTailGen_hyp_band` + `stGridWTail2gL_of` + 3 (a): the ticket's 3 (c)), l.899 `theorem inst_stGridWTail2gL_band`: `CK` from `stGridWTail2gL_of`, `K_n = ⌈N_n^CK⌉ + 1`, `D = 1`, `ε′ = 1/10`, the tail bound `≤ N^{-1}` eventually for every label.
```
### Hypothesis table (final classes)
| class field | band discharge (File 2) | BA discharge (P1b-2, source) |
|---|---|---|
| `Ker` K1-K4 | `gridRepTailGen_ker_band` l.672 (`|E n| ≤ 2`; `step2Gen_USemigroup_band`, `norm_uKer_le`, `difRep3_sum_norm_uKer_sub_one`, `difRep3_conj_uKer`) | probe `T2471_ker_BA` (l.166; `BAReal`, `0 < κ`) |
| `Window` | `gridRepTailGen_window_band` l.708 (`difRep_flow_bounds`, `difRep3_inv_le`) | probe `T2471_window_BA` l.196 (its `(1 - u)⁻¹ ≤ 16N` component) |
| `Inc` Q0 | `isProbabilityMeasure_pathP`, `pathH_measurable_filt`, `pathH_isHermitian`, `difRep3_measurable_STeeM` (l.799) | `baStep2Mat` path law and `Hpath`, `PsiI_isHermitian`, measurability of `STeeMg` at `baStep2Mat` (new) |
| `Zfields` | `gridRepTailGen_zfields_band` l.726 (`difRepTail_condMGF_Z`) | `TwistGridWTail_condMGF_generic` (ι = `Fin 2 → Zd`) + cross-label QV (factor 2, (a) l.62-75) |
| `Yfields` | `gridRepTailGen_yfields_band` l.739 (`AzumaProxyN_YfieldsW`, `hermTestFunLoopN`) | `TwistGridWTail_Y_fields` (768-form ⇒ 2000-form) |
| Q1, Q2 | `gridRepTailGen_inc_band` l.799 (`difRep2_norm_STeeM_le_N`, `norm_STeeM_shiftN_le`, `difRep2_eeShiftErrN_le`) | twins of `TwistGridWTail_twEEM_norm_le`, `_sub_le`; H3′ machinery |
### Narrative
* Delivered: **P1b-1 (targets 1-3)**, as split by the 1a-audit (`T2471-1a-audit.md` §7). Condition (7) is not met (D1 route (i); BA cross-label QV of the band's form: (a) l.4), so the role stays `prover-hard`. Targets 4-7 (BA leaf) are P1b-2, stacked on `t/T2471` after this audit.
* Route: carrier-generic copy-adapt of `DifREP3` §3-§9 at `m = 2`, `Q = ∅`, on the classes. Reused by `open private` (model-free band lemmas): `difRep3_sum_norm_prod_le`, `_norm_double_sum_le`, `_sum_prod_sub_prod`, `_tensorKer_one`, the `gridTime`/coarse-grid lemmas, `_memLp_two_of_pow4`, `_doob_tail`, `_Mee`, `_VQ`, `_c3`, `_PY`, `_cShift`, `_Cbig`, `_budget_shift/_f2/_f1/_Y/_Z`, `_eventually_Z`, `_rpow_CK`, `_inv_le`, `_stopW_eq`, `_measurable_STeeM`, `_sum_norm_uKer_sub_one`, `_conj_uKer`. Copied and adapted (stem `GridRepTailGen_`): the kernel layer (K1-K3 replace `norm_uKer_le` and the `projMat` factor 2), the proxy (K4), the `Y` tail, the `Z` part, `difRep3_pathwise`, `_core`, `_tail_at`. Ports are from RBM3D's own band (`Path/DifREP3` `b3c37aae`, `Path/DifREP2` `76b840ee`, `Induction/AzumaProxyN2`): no RBM1D/RBM2D port, so no RBM1D/RBM2D diff-stat.
* `CK = 9m + 3D + 22 = 3D + 40` (as (a) row (i)); `C′ = 4m + D + 6`; every budget lemma is the band's at `m = 2`. The a.e. split `martIncNg = Z + Y` is used through `ae_all_iff` and `measure_mono_ae`; the telescoped martingale of `T2471_WTail2` is `martIncNg` by `Finset.sum_range_succ_sub_sum`. The generic part (File 1 and File 2 l.1-654) has no `|E|`, `etaT`, `mSigma`, `sz.lam` read ((b) greps).
* T2460 status at target 6: merged (`ad52b370`, `docs/queue/T2460.state` 19:33:28 UTC; (a) l.3). Target 6 (a), (b) are P1b-2; the UN-C5 binding note (H256 (3)) applies there and is already compiled in the probe ((a″)).

## (c) Verified Mathlib names used (new in this ticket's code, by compilation of both files; the band-copied names are those of `Path/DifREP3`)
* `Finset.sum_range_succ_sub_sum` (explicit `f`, implicit `n`); `MeasureTheory.measure_mono_ae`; `MeasureTheory.ae_all_iff`; `Nat.cast_ofNat`; `Finset.sum_comm`; `mul_le_of_le_one_left`; `Matrix.mul_apply`, `Matrix.sub_apply`, `sub_mul`, `one_mul` (entry of `(uKer − 1) · uKer`); `MeasureTheory.integral_condExp`, `integral_mono_ae`, `integrable_condExp` (second moments); `Complex.norm_le_sqrt_two_mul_max`; `MeasureTheory.measureReal_biUnion_finset_le`, `ofReal_measureReal`; `Finset.stronglyMeasurable_fun_sum`, `Finset.measurable_sum`, `Measurable.max`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
1. **P1b-2 obligations from the final classes** (hypothesis table above): the BA discharge of `Inc` has more fields than the probe's: Q0 (probability measure of the BA path law, `Hpath` adapted and Hermitian, `STeeMg` at `baStep2Mat` measurable in the matrix) and the `Yfields` constant in the 2000-form; `Window` is the first conjunct only. `Hyp` has `SizeTendsto` first, then `∀ᶠ n, Ker ∧ Window ∧ ∀ K, K n ≠ 0 → Inc`; `CK = 3D + 40` is fixed by `stGridWTail2gL_of`.
2. **Merge of P1b-1** (hub): add `import RBM3D.Chain.GridRepTailGen` and `import RBM3D.Chain.GridRepTailGen2` after the last `import` of `RBM3D.lean` (not done here: hub-only). The pre-check with both modules passes without a registry line. The probe `RBM3D/Probe/T2471Pins.lean` stays on the branch and is never merged. The new files have no importer.
3. The target-2 instance is at the band (Chain files cannot import `BA/*`); the BA instances (`sz0`, `zSeq`, `flow_sz0`) are P1b-2's.
4. Paper-delta candidates: none new. The slot-count factor 2 in the proxy (`2 Re Σ κκ̄ STeeMg`) is the recorded `docs/paper-deltas.md:821`; H3′ is `T2460a`.
