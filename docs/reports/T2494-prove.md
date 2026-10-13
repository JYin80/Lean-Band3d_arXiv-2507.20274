Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 07:28:30 UTC 2026

Base: worktree `T2494` at `bbe91c0a` (T2489b merged). `main` is now `0a68e61d` (H278, after the T2492 merge `b3ead83b`); its `Test/Axioms.lean` has the same line numbers for every `BA-L6` line (`diff` of the `grep -n` outputs: empty). Lines below are the worktree's. Scratch: `<scratchpad>/T2494/pre2.py` (Python, no Lean).
**Result: targets 1-9 PASS. Switch (a) to `prover-max` HOLDS; switch (b) does not. Cut A | B + C (no third row). Three corrections to the ticket text: row (i)-3 (M-part), R6 (radius), instance 8 (b) (N regime).**
Fill-in table (§269 (5)): (i) = lines 9-22 | (ii) = lines 24-38 | (iii) = lines 40-64 | (iv) = line 64 | (v) = lines 66-68 | (vi) = lines 70-74 | verdicts 76-80.

### (i) BA reading of `7_8:15-91`: band input -> BA producer (file:line) -> premises read; S1 check
| # | step | band input (`Graph/LWTermHolds.lean`) | BA producer (merged) | premises / remark |
|---|---|---|---|---|
| 1 | Markov, `7_8:86-91` | `LWTermHolds_prec_of_moments` :97 (public), `LWInteg` :55 | `baLWMoment_closed` BAAnpLift:255, `baLWMomentExp_closed` :258; pins `LWMomentG` BAMomentGen:124, `LWMomentExpG` BAMomentExpGen:157; `BAMomentExp_integrable` BAMomentExpGenB:263 at `LWfgD_univ` BAMomentExpGen:91; `BAExp14a_det_iff` BAExp14a:58; `LWPsiAll.shift` LWPsi:303 | `∃ c` before `𝔠` (U5S-C3 ok); S pin on `λ²/L² < 1-t`; hcard = N² |
| 2 | cut as a frame, `7_8:9-14` | `_cut_true` :149, `_cut_le` :351 (weights `r`) | `BAExp14b_cut_true` BAExp14bB:146 (frame `BAExp14b_fr`; hSelf = `BAflow_real`.1), `baExp14b_cut_conj` BAExp14bB:210 (def `BAExp14bCutConj` BAExp14b:202), `BAExp14a_X_eq` BAExp14aB:188, `BAMomentGen_sumS` BAMomentGenB:51, `card_Iblk` Defs/Sizes:95 | `F_α = X_[α] = L¹_{[α]} - m` |
| 3 | **closing edge `G_yx` = `GM_yx + M_yx`** (not in ticket) | none: band `M = m·1`, `G_xy = GM_xy` for `x ≠ y` | `BAMomentGen_consts` BAMomentGen:364 via `BAMomentGen_D_M` :342 (`‖M_xy‖ ≤ C e^{-c·lwBdist}`, `M_xy = 0` off equal offset), `BAflow_lam0_window` GreenSchur:72, `ba_G_data` GreenLDE:55 (`‖M‖ ≤ 1`) | `(GijGEX)` is for `G - M`; the available bound `C e^{-c r}` is O(1) at bounded `r` while `Φ ≤ W^{-ε₀}` (`LWClass`), so `‖M_yx‖ ≤ N^τ Φ(r)` does not follow; the offset count (R10) recovers the target |
| 4 | `(eq:directG1)`, `7_8:20-23` | `_Gij_B` :461 (`lwGbyXi_holds`) | `baGbyZeta_holds` BAAuxGraph2B:623, `baZetaClaim_holds` :83 at `ρ_n = (log N_n)^{3/2}`, `R = 0` (not `ρ = 1`: R6); diagonal `BAMomentGen_entry_whp` BAMomentGen:540 (`baEntryPsi_holds` BAAuxGraph2B:817) | `hent` = `STInitialGT2gL`.1 (hassm); `LWPsiAll`, `LWLoop2gL` from hassm |
| 5 | averaged law, B | `lwMoment_avg_whp` | `BAMomentGen_avg_whp` BAMomentGenB:198 (on `baGbEXPav_holds` BA/GbEXPav:24) | none |
| 6 | `(eq:directG2)`, `7_8:24-30` | `_Gij_T` :1047 with `_xiSq_le` :762, `_sfT_shift` :841 | `baGbyZeta_holds` + `baZetaExpClaim_holds` BAZetaExp:325 (gives `ζ ≺ 𝖳(r∧ℓ) + W^{-D}`; the shift is inside it) | `BAAuxGraph2_zetaSq_le` BAAuxGraph2:950 not read |
| 7 | `(GavLGEX)` at `Ψ_t = max(W^{-d/2}, Bctl^{1/2})` | `_avg_T` :1182 | `baGbEXPav_holds` BA/GbEXPav:24 (`baSTGavLGEXgL_holds` BA/Step1Prime:913), `LWWindow_max_Bctl` LWPsi:344, `BAExp14d_Bctl_small` BAExp14dB:74 (`Bctl ≤ 2N^{-c₀}`; replaces the twin of `lwN_Bctl_le` LWTermExpN:225) | loops at `D = 1` from `LWAssmExpgL` |
| 8 | T reduction, `D ≥ 2d+1` / `D < 2d+1` | `_reduceT_core` :1270, `_concT` :1551, `_arithT` :934, `_fT` :1487 | copies; `tailW_regime1_bounds` LWPsi:475; Markov as row 1 | R4, R8 |
| 9 | N regime, `7_8:20` | `lwtermExpN_of_LWterm` LWTermExpN:414 | `lwN_prec_mono` :42, `lwN_tailW_le` :121, `lwN_B_le_tail` :145, `lwN_size_rpow_neg_le` :340, `lwN_Wneg_le` :355, `LWPhiB_psiAll` LWPsi:417; `hLW` = `baLWterm_holds` (theorem, no binder) | R7, R9 |
| 10 | Step 2, L6 | `lwtermExp_holds` :1604 | `baStep2_holds` BA/Step2CloseBA:181; `baLWCutExpTw_of_S2` BAExp14a2:272, `baLWtermEXPTw_of_S2` :326, `baExp14bS2_holds` BAExp14b2B:1064 | types `BAExp14bS2 d →` Of-defs: `fun d => f d (baExp14bS2_holds d)` |
S1: every producer above is merged on `bbe91c0a`; data enter only through `BAFlow`, `BAflowT0`, `BAReal`, `κ ≤ Im m` (`ba_G_data`); no new pin, no hypothesis outside C1. T2470 target 4 (vii): `BAAnpAuxG` is concluded by `baAnpAuxG_holds` BAAnpLift:229, the path binder by `baLWMomentOfAnp_closed` BAMomentExpGen:189; nothing left. `baGGGamma_holds` BAGGExp:358 (iv).

### (ii) Exponent and constant table (d = 3, `sz0`, `(κ,ε,𝔠,𝔡) = (1/2, 1/10, 1/6, 1/10)`, `ε₀ = 1/10`, `Λ = 𝔡⁻¹ = 10`)
| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| R1 | `p₀ = ⌈(D+2)/τ₀⌉+1`, `p = 2p₀` | `τ₀=1/10`: D=5: 71/142; D=7: 91/182 | `τ₀ p ≥ D+2`; `K^p ≤ N` eventually | 14.2 vs 7 (7.2); 18.2 vs 9 (9.2) |
| R2 | `\|V_n\| ≤ N^C` | `Idx×Idx`: exactly `N²`, `C = 2` | `N·K^p ≤ N² ≤ N^{τp-D}` | 0 in `C` (needs only `≤`) |
| R3 | `LWPsiAll.shift` `K` | `K ≤ max(C₁c^{-C₂}, Cc(C))` (LWPsi:298); `Φ0`: `C₁=C₂=2`, `Cc≡1` | `K^p ≤ N` eventually (`SizeTendsto`) | eventual |
| R4 | `D ≥ 2d+1` split | `D' = max(D, 7)`: D=1,7 -> 7; D=9 -> 9 | cross term `W^{-D}𝖳` absorbed iff `D' ≥ 2d+1` (`_reduceT_core` hypothesis) | 0 at D' = 7 |
| R5 | `D₁` (B side, `baZetaClaim`) | `max(d + 2C₂/(𝔠d) + 1, 1/𝔠) = 12` at `C₂=2` | `D₁ ≥` that | 0 (tight; merged instance uses 12) |
| R6 | radius `ρ_n`, `R = 0` | `ρ_n = (log N_n)^{3/2}` | `baGbyZeta` (def BAAuxGraph2B:586): `∀K ∀ᶠn, K log W ≤ ρ-2R`; `baZetaClaim`: `ρ+1 ≤ N^τ`; `baZetaExpClaim`: `√ρ ≤ τ log N` | first: `log N ≥ K²` suffices (`W ≤ N`); third: iff `log N ≥ τ^{-4}`. **Ticket `ρ = 1, R = 0` fails the first** (K=1: `log W_0 = 3.47 > 1`) |
| R7 | window `ε₁ = min(ε₀, d c₀/4)`, `c₀ = min(2𝔠𝔡, ε)/2` | `c₀ = 1/60`, `ε₁ = 1/80`, `2ε₁ = 1/40` | `Bctl ≤ 2N^{-c₀} ≤ 2W^{-d c₀} ≤ W^{-2ε₁}` iff `W^{d c₀/2} ≥ 2` | `2ε₁ = d c₀/2` exactly; factor 2 absorbed eventually |
| R8 | T arithmetic | `K0 = 6+16(1+Λ²)+2(4+8(1+Λ²))(1+Λ²) = 165646`; `Γ = X²`, `N^τ = X⁶` | `2K0 ≤ X = N^{τ/6}`; `W ≥ 1+Λ² = 101` | eventual: τ=1 from n=30; W from n=1 |
| R9 | N regime (B class) | `C₁=2^d=8`, `C₂=d=3`, `C₃=√(1+Λ²)=10.05`, `e·2^{d-2}=5.437`; `D'=1/𝔠=6` | `W^{-1/𝔠} ≤ L^{-d}` (`lwN_Wneg_le`) | eventual |
| R10 | M-part count | `#{(x,y)∈[a]×[b]: off x = off y} = W^d` of `W^{2d}` (brute force W=2: 8/64; W=3: 27/729) | `W^{-d}C e^{-cr} ≲ Φ(r)` via `W^{-d/2} ≤ C₃Φ(0) ≤ C₃C₁(r∨1)^{C₂}Φ(r)` (`LWClass`, `LWPsiRel`); S regime: same with `𝖳(r∧ℓ)` | relative slack `W^{-d/2}`, 5.5e-3 at n=0 |
| R11 | `η` | `0<η≤1` (BAExp14a:1266, BAExp14c:712); `η⁻¹ ≤ κ⁻¹(1-t)⁻¹ = 4` (BAExp14aB:1271) at `κ=t=1/2` | `η ∈ [κ(1-t), 1-t] = [1/4, 1/2]` | `η⁻¹` in `[2, 4]` |
| R12 | `‖G_xx‖ ≤ 2` | `‖GM_xx‖ ≤ N^{τ₁}Φ(0) ≤ W^{-ε₀/2} ≤ 1` (`BAMomentGen_Psi_facts` BAMomentGen:500, `τ₁ ≤ 𝔠ε₀/4`), `‖M‖ ≤ 1` | sum `≤ 2` | 0 |

### (iii) Nondegenerate instance (script; every deterministic hypothesis discharged, stochastic pins stay hypotheses)
Data: `d=3`, `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `λ_n=(2(n+1))^{-6}`; Defs/Sizes:260-264), `zSeq`, `flow_sz0` (FlowPins:1214), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0` :1254), `ε₀ = 1/10`, `Ψ0 = Φ0 = W^{-1/2}` (LWPinsBA §3 private: re-derive; `LWPsiAll sz0 (1/10) 2 2 1 (fun _ => 1) Φ0`, as BAMomentGenB:454).
- 8 (a) target 2: `baLWterm_holds 3 le_rfl (1/2) (1/10) (1/10) … sz0 zSeq flow_sz0 (fun _ => 1/2) … Ψ0 Φ0 hassm`, `hassm = LWAssmgL …` hypothesis (`STInitialGT2gL`, `LWLoop2gL` inside).
- 8 (b) target 5 with `LWAssmExpgL … ℓ ≡ 0` (hypothesis): S regime nonempty (`λ²/L² < 1-t` at every n; slack 0.49998 at n=0). **N regime is empty at `(sz0, zSeq)`**: `1-t ≥ 1-BAflowT0 ≥ 11/36` (`zSeq_im_ge` FlowPins:1205, `t0_sz0` :1227: `BAflowT0 = Im m/(6/5)`) while `λ²/L² ≤ 2^{-16}`. So 8 (b) is the union `baLWtermExp_holds` at all pairs (nonempty), and target 3 has no instance: n/a, reason as above (no merged flow data with `1-t ≤ λ²/L²`).
- 8 (c) target 7 (b): `BALWtermEXPTw 3`, TL1 by `baTwistAvgProd_holds 3` (BA/TwistAvgB:451), TL2 and the five pins hypotheses (shape of the check, as BAExp14a2 §6 instance 6 (c)).
- 8 (d): `baStep2_closed 3 le_rfl …` at `s ≡ 1/10 < t ≡ 1/2` (shape of Step2CloseBA §5 instance 11 with `hLW`, `hLWE` now discharged).
```
$ python3 -I <scratchpad>/T2494/pre2.py
sz0 n=0: L,W,N,lam = 4 32 2097152 =2^21: True 1/64 | lam^2/L^2 = 1/65536 (n=1: 9.313225746154785e-10 )
Markov tau0=1/10 D=5: p0=71 p=2p0=142 tau0*p=14.2 >= D+2=7 slack 7.2; |V_n|=N^2 exactly (C=2)
Markov tau0=1/10 D=7: p0=91 p=2p0=182 tau0*p=18.2 >= D+2=9 slack 9.2; |V_n|=N^2 exactly (C=2)
t0 in [ 2/3 , 25/36 ] (Im m>=4/5, Im z>=11/30, Im z+Im m=6/5) => 1-t>= 11/36 = 0.3056
S regime (n=0,t=1/2): lam^2/L^2 = 1.52587890625e-05 < 1-t = 0.5 : slack 0.499985 | N regime 1-t<=lam^2/L^2: max_n lam^2/L^2 = 1.52587890625e-05 < 0.3056 -> EMPTY at sz0,zSeq
B_{t,0}= 2.0303 Bctl= 6.195904278883183e-05 <=2 ok | eta in [ 1/4 , 1/2 ], eta^-1<=kap^-1(1-t)^-1= 4 | window W^-3/2<=W^-1/2<=W^-1/10: 0.00552 0.1768 0.7071
c0=min(2cd,eps)/2 = 1/60 eps1=min(eps0,d c0/4) = 1/80 (2eps1 = 1/40 <= d c0/2 = 1/40 : slack factor 2 absorbs Bctl<=2N^-c0)
D1 (B side, baZetaClaim) >= max(d+2C2/(c d)+1,1/c) = 12.0 (C2=2) | T side D'=max(D,2d+1),D1>=max(2(d+D'),1/c): {1: 20, 7: 20, 9: 24}
Lam=1/fd = 10 K0 = 165646 2K0 = 331292 ; eventual: N^(tau/6)>=2K0 at tau=1 from n = 30 ; W>=1+Lam^2=101 from n = 1
B class (N regime) d=3: C1=2^d=8, C2=d=3, C3=sqrt(1+Lam^2)= 10.05 , comparison const e*2^(d-2) = 5.4366
M-part: W=2: |[a]x[b]| = 64, equal-offset pairs = 8 = W^d = 8
M-part: W=3: |[a]x[b]| = 729, equal-offset pairs = 27 = W^d = 27
radius rho_n=(log N)^(3/2): K log W <= rho if log N >= K^2 (W<=N); sqrt(rho)<=tau log N iff log N>=tau^-4; rho=1,R=0 fails hsep: K=1,n=0: log W = 3.466 >1
census central: A=1185 B=1057 C=140 total=2382; low(x0.85)=1007/898/119=2025; high(x1.4)=1659/1480/196=3335
cut A | B+C: 1185 | 1197 (<=1950: True); cut A+B | C: 2242 | 140 (A+B<=1950: False); reserve C file if A or B>1800: False; high halves 1659 | 1676
```
External-hypothesis limits (TEAM §8 lesson 14): (LW_assm) at `Φ0² = W^{-1}`: `W^{-d}B_{t,0} ≤ W^{-3}·2/(1-t) ≤ 6.55·W^{-3}` for `t ≤ 25/36` (`B ≤ 1/(1-t)+L^{-d}/(1-t)`), ratio to `Φ0²` is `≤ 6.55 W^{-2} -> 0` (n=0: `Bctl/Φ0² = 2.0e-3`); `(initialGT2)` threshold `W^{-ε₀} = 0.707` at n=0 vs `Bctl^{1/2} = 7.9e-3`; TL2 and the five pins as in the merged BAExp14a2 §6 examples (no new limit claim). **(iv)** L40-C2: L5 reads only `0 < sz.lam n ≤ 𝔡⁻¹` eventually per index (`WO`, Defs/Sizes:164-165) and `0 < g₀ ≤ 𝔡⁻¹` (`BAflow_lam0_window` GreenSchur:72); its own constants (`K0`, `C₃`, `BAMomentGen_consts`) depend on `(d, 𝔡, κ)` only; the producers' thresholds are those of T2483b-prove.md:61 (sup at `Λ = 𝔡⁻¹`, range `(0, 𝔡⁻¹]`). Not wider: no stop.

### (v) Census, split, projection (basis: band 1,801 + 546 lines; BA twin re-priced by component, `pre2.py`)
A (`BATermHolds`; targets 1-3, 8a): header 55, Markov/integrability 70, algebra §3 285, M-part 125 (consts 45, offset count 40, propagation 40), B side 435 (radius 55, `Gij_B` 75, diag 45, arithB+M 70, reduceB 105, `fB` 65, `lwterm` 20), N regime 175, instance 40 = **1,185**. B (`BATermHoldsB`; targets 4-6, 8b/d): header 55, T facts+arithT(+M) 205, `Gij_T` 130 (`baZetaExpClaim` route: no `xiSq`), `avg_T` 110, `reduceT_core` 250, `fT` 95, `concT` 50, S def/holds 40, union 40, `baStep2_closed` 12, instances 70 = **1,057**. C (`BALWOut`; target 7, 8c): header 45, two closures 25, instance 55, slack 15 = **140**. Total central **2,382** (low x0.85: 2,025; high x1.4: 3,335). Registry edits (target 9): 8 lines of `Test/Axioms.lean`, not Lean lines of A-C.
Decision: total > 1,950, so the pre-signed split applies: **L5a = A (1,185) | L5b = B + C (1,197)**. The alternative cut A + B | C does not apply (A + B = 2,242 > 1,950). No half above 1,950 (high: 1,659 | 1,676), so no third row; reserve `BATermHoldsC` not predicted (A, B < 1,800). Projection: **L 48 / 50** (= L40-C3 projection); stop line 2,000 per file. The ticket draft (A 1,000, B 990, C 250 = 2,240) agrees within 6%: the M-part (about +190, estimate) is offset by the savings from `baZetaExpClaim` and `BAExp14d_Bctl_small` (about -240, estimate); A carries the M-part, B the savings.

### (vi) UBA-C1, U5S-C3, hypotheses, registry
- UBA-C1: not triggered; `sz.lam` is read only through the pin vocabulary and `WO`; the radius `ρ_n` depends on `sz.size` only, constants in `(d, κ, ε, 𝔡, 𝔠)` before `(sz, z)`; no comparison other than R1 occurs.
- U5S-C3 family-premise table: public statements `baLWterm_holds`, `baLWtermExp_holds`, `baStep2_closed`, `baLWCutExpTw_holds`, `baLWtermEXPTw_holds` and the regime def `∀ d, P d`: binder `d : ℕ` only -> **empty**; eventual BA facts enter as `∀ᶠ n` inside (`BAflow_lam0_window`, `BAMomentGen_consts`); TN-C4: `STGridRepNgL` not read.
- Hypothesis table: 8a `LWAssmgL` (`STInitialGT2gL` Axioms:190 owed; `LWLoop2gL` inside); 8b `LWAssmExpgL` (`STInitialGT2gL`, `LWLoopExpgL`); 8c `STLocalEntrygL` :144, `LWAvgLawgL` (no line; feeds TL1), `STLmaxgL` :133, `STLKgL` :135, `STDecaygL` :217, `BATwistLoopLaw` :193 (TL1 `BATwistAvgLaw` :192 produced by `baTwistAvgProd_holds`); 8d none. Helpers with an `LWAssmgL`/`LWAssmExpgL`/`LWLoopExpgL` binder stay `private`; the scan (`scanPremises`, Axioms:471) does not see `_private` names; cross-file helpers A -> B use the unfolded `hassm` as BAMomentGen §6.
- Registry lines (target 9, by name): delete `BALWterm`, `BALWtermExp` (:221-222) and the T2487 header comment (:220) (the scan only fails for unclassified premises, so this is hygiene; both leave `found` since `baLWterm_holds`, `baLWtermExp_holds` conclude them); text only: `LWtermG` :218, `LWtermExpG` :219, `STLocalEntryUgL` :201, `STAvgUgL` :231, `STStep2ConclgL` :232. Not edited: :196-197 (T2495). `BAStep2`, `BALWCutExpTw`, `BALWtermEXPTw`, `BALWtermEXP`, `LWtermEXPG`: no registry line (grep), nothing to add.

### Verdicts
- T1 inputs PASS (rows 1-3; M-part is the new step). T2 `baLWterm_holds` PASS. T3 N regime PASS (instance n/a: empty index set at merged data). T4 S regime PASS. T5 union PASS. T6 `baStep2_closed` PASS (one line). T7 L6 PASS (two lines). T8 PASS with (b) amended (S regime and union only). T9 PASS (8 registry lines).
- **Switch (a) HOLDS**: step row 3 (the M-part of the closing edge, the offset count R10, `BAMomentGen_consts`) is an estimate beyond the ticket's listed producers; it is not a new pin (merged producers exist), so S1 is not triggered. Recommend `prover-max` for stage 1b. **Switch (b) does not hold**: `BAAuxGraph2_zetaSq_le` has the shape of `_xiSq_le` plus an additive floor `W^{-D₁}` (BAAuxGraph2:950-957), and the `𝖳` shift is delivered by merged `baZetaExpClaim_holds` (row 6), so neither is read.
- Paper-delta candidates: `T2494a` (`eq:directG1`/`eq:directG2` at BA read `|G_yx| ≺ δ_xy + Ψ + |M_yx|`; the offset support of `M` recovers the stated bound, `B:286-288` "analogously"); `T2494b` (radius `ρ = (log N)^{3/2}` for `baGbyZeta`, the ticket's `ρ = 1` is invalid).
- Corrections for the dispatcher: row 8 (b) -> "S regime nonempty, N regime n/a (empty)"; target 2/5 text "ρ = 1, R = 0" -> "ρ = (log N)^{3/2}, R = 0".

## (b) Script output, row a (L5a = file A only: `RBM3D/Graph/BATermHolds.lean`, targets 1-3, 8 (a)); stage 1b `prover-max` — written Tue Oct 13 08:05:13 UTC 2026
Start decision: row a starts now (ticket start condition); T2489b merged at `bbe91c0a` (`git merge-base --is-ancestor bbe91c0a main` succeeds); branch `t/T2494`, commit `e50823fe`.
```
$ date -u; git log --oneline -2; git diff --stat 3238c365...t/T2494   (3238c365 was `main` at that time; worktree T2494)
Tue Oct 13 08:01:05 UTC 2026
e50823fe T2494 (L5a): Graph/BATermHolds: baLWterm_holds, BALWtermExpN, baLWtermExpN_holds, instance; import line
bbe91c0a T2489: merge L4b2b Graph/BAExp14b2B (second half of the split, t/T2489b)
 RBM3D.lean                   |   1 +
 RBM3D/Graph/BATermHolds.lean | 914 +++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 915 insertions(+)
$ wc -l RBM3D/Graph/BATermHolds.lean
     914 RBM3D/Graph/BATermHolds.lean
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Graph/BATermHolds.lean
(exit 1)
$ lake build RBM3D.Graph.BATermHolds 2>&1 | grep -c error  (prints the count); then the same build | tail -1   (module alone; its warnings are the long-line style lint of the header docstring)
0
Build completed successfully (4071 jobs).
$ lake build > fullbuild2.log   (full library, import line in RBM3D.lean, after the commit); tail -1 fullbuild2.log; grep -n 'axiom audit:' fullbuild2.log; grep -c 'error:' fullbuild2.log
Build completed successfully (4357 jobs).
6249:info: RBM3D.lean:589:0: axiom audit: 14709 theorems, 4576 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
$ lake env lean axioms.lean   (#print axioms of the three public declarations)
'RBM.BA.baLWterm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWtermExpN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BALWtermExpN' depends on axioms: [propext, Classical.choice, Quot.sound]
$ sed -n 706,707p / 715,726p / 758p RBM3D/Graph/BATermHolds.lean   (target statements, extracted by script)
706: theorem baLWterm_holds : ∀ d : ℕ, BALWterm d := by
707:   intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ C₁ C₂ C₃ Cc Ψ Φ hassm
715: def BALWtermExpN (d : ℕ) : Prop :=
716:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
717:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
718:       ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
719:         ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
720:           ∀ D : ℝ, 0 < D →
721:             PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
722:                 1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
723:               (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
724:               (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
725:                 ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
726:                   ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))
758: theorem baLWtermExpN_holds : ∀ d : ℕ, BALWtermExpN d := by
$ diff <(check file: def T2494_TermClosed ... ) <(F: theorem baLWterm_holds ...)   (statement of target 2 against T2494_TermClosed, modulo the name)
(identical)
$ lake env lean check_rowa.lean   (scratch copy of the check file + import RBM3D.Graph.BATermHolds + `example : T2494_TermClosed := baLWterm_holds`; not committed)
exit=0; error lines: 0
256:example : T2494_TermClosed := baLWterm_holds
$ diff of the body of LWtermExpG (Chain/LWGen.lean:96-105, instance names substituted) against BALWtermExpN (F:716-726)
6,7c6,8
< PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
< (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1 p.2 ω‖)
---
> PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
> 1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
> (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
10c11
< ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)))
---
> ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))
$ sed -n 883,891p F   (compiled nonempty instance of target 2, d = 3)
883: example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) BAMomentExpGen_Ψ0)
884:     (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAMomentExpGen_Φ0) :
885:     PrecL sz0 μ0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
886:       (fun n p ω => ‖LWEg (baFMz sz0 zSeq) n ((fun _ => (1 / 2 : ℝ)) n) p.1 p.2 ω‖)
887:       (fun n p _ => ((baFMz sz0 zSeq).eta n ((fun _ => (1 / 2 : ℝ)) n))⁻¹ * BAMomentExpGen_Φ0 n 0 *
888:         BAMomentExpGen_Φ0 n ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2) :=
889:   baLWterm_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
890:     (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1)
891:     BAMomentExpGen_Ψ0 BAMomentExpGen_Φ0
$ grep -nE "sz\.lam|withLam|gK" F | awk -F: '$1>=706 && $1<=726'   (the public statement text)
719:        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
721:            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
722:                1 - t n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2})
725:                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
total hits of the pattern in F: 22 (the rest are proof terms, the pin vocabulary of the proofs and the instance data)
$ grep -nE "LWAssmgL|LWAssmExpgL|BAExp14bS2|BATwist|BALWCutExpTw" F | cut -c1-72
39:**Premise scan** (`Test/Axioms.lean:471`): the public theorems have t
40:the pin `BALWterm` and the statement def `BALWtermExpN`); the private
704:/-- **`lem:LWterm` at the block Anderson data** (`3_5:385-404`, `7_8
719:        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.se
871:`(C₁, C₂, C₃, Cc) = (2, 2, 1, 1)`.  What stays a hypothesis is anoth
$ grep -cE "BAAnpAuxG|BAShapePath|STGridRepNgL" F; grep -cwE "mE|STGM|STKloop|etaT|STflowE|lwS|gK" F
0
0
$ grep -nE "^(theorem|def|abbrev|inductive|structure|instance|lemma)" F
706:theorem baLWterm_holds : ∀ d : ℕ, BALWterm d := by
715:def BALWtermExpN (d : ℕ) : Prop :=
758:theorem baLWtermExpN_holds : ∀ d : ℕ, BALWtermExpN d := by
$ census (file:line of the producers; from the grep -n output ev6.txt of the scratchpad, grouped by use)
Markov / integrability: LWTermHolds_prec_of_moments LWTermHolds.lean:97 | baLWMoment_closed BAAnpLift.lean:255 | BAMomentExp_integrable BAMomentExpGenB.lean:263 | LWfgD_univ BAMomentExpGen.lean:91
Algebra / M-part: BAExp14b_cut_true BAExp14bB.lean:146 | baExp14b_cut_conj :210 | BAExp14a_X_eq BAExp14aB.lean:188 | BAMomentGen_decay BAMomentGen.lean:651 | BAMomentGen_sumS BAMomentGenB.lean:51
B side: baGbyZeta_holds BAAuxGraph2B.lean:623 | baZetaClaim_holds BAAuxGraph2B.lean:83 | lwXiRad_holds AuxGraph2.lean:1241 | BAMomentGen_avg_whp BAMomentGenB.lean:198 | BAMomentGen_entry_whp BAMomentGen.lean:540 | BAMomentGen_Psi_facts :500 | lwMoment_phi_facts LWMoment.lean:409
N regime: lwN_prec_mono LWTermExpN.lean:42 | lwN_tailW_le :121 | lwN_B_le_tail :145 | lwN_size_rpow_neg_le :340 | lwN_Wneg_le :355 | LWPhiB_psiAll LWPsi.lean:417 | BAExp14d_Bctl_small BAExp14dB.lean:74
open private (instance only, F:879): BAMomentExpGen_Φ0 :911, _Ψ0 :913, _Ψ0_window :916, _psiAll0 :926 (BAMomentExpGen.lean)
stem copies (private, F): wneg :729, phi_zero :733, phi_sq :740, zdistInf_le :749 <- lwN_* LWTermExpN.lean:383-406; zdistInf_zero :67, zdistInf_sub_comm :71 <- LWTermHolds.lean:378-384 (no RBM1D/RBM2D port: all sources are RBM3D files, so no diff-stat)
$ for ref in main t/T2489b t/T2491 t/T2492 t/T2493 t/T2495; do echo "$ref $(git rev-parse --short $ref): $(git grep -c -E "baLWterm_holds|BALWtermExpN|baLWtermExpN_holds|BATermHolds" $ref -- RBM3D RBM3D.lean | wc -l) files"; done
main 6ccc6be2:        0 files
t/T2489b a4e272dc:        0 files
t/T2491 ae93f0a2:        0 files
t/T2492 9f0a3641:        0 files
t/T2493 b430f3c2:        0 files
t/T2495 add74cd9:        0 files
```

**Narrative** (line numbers: `RBM3D/Graph/BATermHolds.lean` at `e50823fe`).
1. Scope. Row a = L5a = file A only (targets 1-3 and 8 (a)); the ticket start condition for row a is "start now". Worktree base `bbe91c0a` (T2489b merged; it is an ancestor of `main`, now `6ccc6be2`). The S regime, the union, `baStep2_closed`, files B and C, L6 and the registry target 9 are row b (`t/T2494b`): none is written here. Stage 1b is the pre-signed switch to `prover-max` ((a) lines 76-78).
2. Delivered. Target 1 (private): Markov `BATermHolds_fB` :458, averaging `BATermHolds_cut_true_le` :171, offset count `BATermHolds_card_off` :144, pathwise bound `BATermHolds_LWE_le` :213. Target 2: `baLWterm_holds` :706 (through private `BATermHolds_reduceB` :577). Target 3: `BALWtermExpN` :715 and `baLWtermExpN_holds` :758. Instance 8 (a): :883. The only public names are these three; every helper is `private` (row b reads them by `open private`).
3. The M-part (the step beyond the listed producers, (a) row 3). `BAExp14b_cut_true` gives `LWcutg = W^{-2d} Σ_{x∈[a_o], y∈[a_c]} G(σ)_{yx} Σ_α X_{[α]} G_{xα} G_{αy}`. At BA `G = (G-M) + M`, `M_{xy} = 0` unless the offsets agree, `‖M_{xy}‖ ≤ C' e^{-c|[x]-[y]|}` (`BATermHolds_Mpart` :556 from `BAMomentGen_decay`). Exactly `W^d` of the `W^{2d}` pairs of two blocks have equal offsets, so the M-part carries the weight `W^{-d}`: `‖LWEg‖ ≤ 2 (γ(φ + 2μAγ) + W^{-d} (γ+Mb)(φ + 2μA(γ+Mb)))`. With `W^{-d} ≤ C₃² Φ(0)²` and `Φ(0) e^{-cr} ≲ Φ(r)` (`BATermHolds_poly_exp` :402 and `(eq:Psi)`), `BATermHolds_arithB` :300 bounds this by `K X³ η⁻¹ Φ(0) Φ(r)²`.
4. Route of target 2: four w.h.p. events at `τ/4`: `‖f_{xy}‖ ≤ N^{τ/4} η⁻¹Φ(0)Φ(r)` (Markov of `baLWMoment_closed`, `p = 2p₀`, `p₀ = ⌈(D+2)/τ₀⌉ + 1`), `‖(G-M)_{xy}‖ ≤ N^{τ/4} Φ(r)` (`BATermHolds_GM_B` :514: `baGbyZeta_holds` at `R = 0`, `ρ = (log W)^{3/2}`, `baZetaClaim_holds`, `D₁ = max(d + 2C₂/(𝔠d) + 1, 1/𝔠)`), `‖G-M‖_max ≤ N^{τ₁} Φ(0)` (hence `‖G_{xx}‖ ≤ 2`) and `‖𝓛^{(1)}-m‖ ≤ N^{τ₁} Ψ'²` with `τ₁ = min(τ/4, 𝔠ε₀/4)`; on the intersection `‖LWEg‖ ≤ 2K0 N^{3τ/4} η⁻¹Φ(0)Φ(r)² ≤ N^τ …`, `2 K0 ≤ N^{τ/4}` eventually (K0 of `c₃ = C₃²`, `c₃' = (max 1 C₃)²`, `Kz`).
5. Target 3: `baLWterm_holds` at the B class `LWPhiB sz d K t`, `K n = ⌊ℓ_n⌋ ∧ L_n`, window `ε₁ = min(ε₀, d c₀/4)` with `c₀` of `BAExp14d_Bctl_small` (in the place of the twin of `lwN_Bctl_le`, (a) R7); the comparison with `tailW` is `lwN_B_le_tail` (constant `e·2^{d-2}`). The diff above shows `BALWtermExpN` equals the generic pin `LWtermExpG` at the BA data except for the regime subtype and the projections `.1`.
6. Corrections to the ticket text, as in (a) lines 79-80: radius `ρ = (log W)^{3/2}`, `R = 0` (the ticket's `ρ = 1` fails `K log W ≤ ρ - 2R`); R6 of (a) names `(log N)^{3/2}`, the Lean radius is `(log W)^{3/2}` because `lwXiRad_holds` is stated with `log W`; both satisfy the first two constraints of R6 (`K log W ≤ ρ - 2R`, `ρ + 1 ≤ N^τ`; the third, for `baZetaExpClaim`, belongs to row b), so (a) needs no (a′). Instance 8 (b): the N regime is empty at the merged flow data at `t ≡ 1/2` (compiled, :896), so target 3 has no nonempty instance; hence the instance of the N regime is carried by the union in row b.
7. Tables. UBA-C1: not triggered (no `gK`, no comparison other than the pin vocabulary; the `gK`/band-object grep counts above are 0). U5S-C3 (family premises of public statements): empty; the public theorems have the binder `d : ℕ` only, `BALWtermExpN` has the merged-pin shape. L40-C2: `sz.lam` is read through `WO` (`hg` :782-784) and inside `BAMomentGen_decay` (`BAflow_lam0_window`, `0 < g₀ ≤ 𝔡⁻¹`), the range of (a) line 64; the constants `C', c` come from `BAMomentGen_consts` at `Λ = 𝔡⁻¹` (functions of `(d, 𝔡, κ)`). Hypotheses of instance 8 (a): `hI : STInitialGT2gL …` (registered, owner BA-V) and `hL : LWLoop2gL …` (`LWAssmgL`'s stochastic part); discharged: `3 ≤ 3`, `κ, ε, 𝔡 > 0`, `flow_sz0`, `0 ≤ t`, `t ≤ BAflowT0` (`half_lt_t0`), window, class, `(eq:Psi)`.
8. Closing conditions (i)-(ix), this row: (i) `BALWterm`: `baLWterm_holds` :706; `BALWtermExp`: row b. (ii) row b. (iii) (a) :883; (b)-(d) row b. (iv) `baGGGamma_holds` `BAGGExp.lean:358` (merged, not edited). (v) row b; after this row `RBM.BA.BALWterm` appears under "registered premise(s) carry nothing yet" (`fullbuild2.log:6433`, the registry build log in the scratchpad), its line is removed by target 9. (vi) `BALWterm d` is unchanged (`baPin LWtermG d`); `example : T2494_TermClosed := baLWterm_holds` compiles; target 6 is row b. (vii) `BAAnpAuxG` is concluded by `baAnpAuxG_holds` `BAAnpLift.lean:229` (T2488) and the path binder by `baLWMomentOfAnp_closed` `BAMomentExpGen.lean:189` (T2483): nothing left; the grep above finds neither name in F. (viii) row b. (ix) row b ((a) line 74).
9. Line counts: F = 914 (`wc -l` above) against the stop line 2,000 and the 1a central 1,185 for A; no section commit exceeded it. Split A | B + C as in (a) line 68.

## (c) Verified Mathlib names used (69 tokens extracted from F by script and `#check @`-ed in the scratchpad `names.lean`, plus `tendsto_atTop_mono'`, `Real.tendsto_log_atTop` in `n2.lean`: 0 errors; deduplicated list below; names verified absent: none)
`Real`: `abs_le_sqrt add_one_le_exp exp_add exp_le_exp exp_le_one_iff exp_mul exp_pos log_nonneg mul_rpow one_le_rpow one_rpow rpow_add rpow_le_one_of_one_le_of_nonpos rpow_le_rpow rpow_le_rpow_of_exponent_le rpow_mul rpow_natCast rpow_neg rpow_nonneg rpow_one rpow_pos_of_pos rpow_two sq_sqrt sqrt_eq_rpow tendsto_log_atTop`
`Finset`: `insert_eq_of_mem mem_filter mem_singleton mem_univ mul_sum pair_eq_singleton sum_add_distrib sum_boole sum_congr sum_const sum_filter sum_le_sum sum_mul sum_pair sum_singleton sup_le`; `Nat`: `cast_nonneg eq_zero_of_le_zero floor_natCast le_ceil one_le_cast`; `Equiv`: `eq_symm_apply ofBijective_apply`; `Complex.norm_natCast`; `ZMod.val_lt`
Root: `inv_le_one_of_one_le₀ le_div_iff₀ le_mul_of_one_le_left mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right norm_add_le norm_star norm_sum_le one_le_inv_iff₀ one_le_pow₀ pow_le_one₀ pow_le_pow_left₀ tendsto_rpow_atTop tendsto_atTop_mono'`

## (d) Open issues and paper-delta candidates
- Target 3 has no nonempty instance (the N regime is empty at `sz0`, `zSeq`, `t ≡ 1/2`; a nonempty one needs a BA flow point with `1 - t ≤ λ²/L²`, e.g. bounded `L`, which is not in the merged data). Row b: the instance of the union (target 5) is nonempty through the S regime.
- For row b: the private lemmas `BATermHolds_LWE_le` :213, `BATermHolds_Mpart` :556, `BATermHolds_poly_exp` :402, `BATermHolds_W_tendsto` :432 are meant to be read by `open private … from RBM3D.Graph.BATermHolds`.
- `main` moved after the branch point (`bbe91c0a` to `6ccc6be2`): `git diff --stat bbe91c0a 6ccc6be2 -- RBM3D RBM3D.lean` lists new leaf files, `RBM3D.lean` +6 lines and `Test/Axioms.lean` 7 changed lines, and no existing module that F imports. `RBM3D.lean` carries one added line on `t/T2494` (`import RBM3D.Graph.BATermHolds` after the last import): a union of lines at the merge.
- Style only: the header docstring has lines over 100 characters (the lint option is set after it, as in the sibling files).
- `T2494a` (paper delta candidate): `(eq:directG1)`, `(eq:directG2)` and the cut average at BA read `|G_{yx}| ≺ δ_{xy} + Ψ + |M_{yx}|`; the paper (`B_graphical_lemmas.tex:286-288`, "analogously") gives no argument for the `M_{yx}` term, which Lean closes by the offset support and the decay of `M` with the weight `W^{-d}` of the equal-offset pairs (`BATermHolds_LWE_le`, `BATermHolds_card_off`).
- `T2494b`: `baGbyZeta_holds` needs `K log W ≤ ρ - 2R` for every `K`, so `claim:xi` at BA is applied at a polylogarithmic radius (Lean: `ρ = (log W)^{3/2}`, `R = 0`), not at `ρ = 1`.
- Inherited, not new: the regime split of `lem: EWGn2_N` and the B class `LWPhiB` in the N regime (band candidate `T2342a`, `Graph/LWTermExpN.lean:413`).
