Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 23:33:49 UTC 2026

### (i) Exponent table
Data `sz0` (`Defs/Sizes.lean:260`, d=3): L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6; n=0: L=4, W=32, lam=1/64; 𝔡=1/10 (Λ=𝔡⁻¹=10). `B_u = sz.Bctl n u` (Sizes:214), `η_u = etaT E u` (GLoop:75), `r_{im} = (g²+1-u_i)/(g²+1-u_m)`, g = `sz.lam n`.

| # | quantity | value / form | constraint (source) | slack |
|---|---|---|---|---|
| 1 | drift sup bound `dDrift` | Γ(ΓΦ)(B_u^k/η_u)((k-1)+kΓΦ) | = (k-2)·(D1) + (D2) + (D3) of `GoodSetN` (GridGoodN:124); `Nat.card_Icc 3 k = k-2`; needs 2≤k. No additive W^{-D'} (RBM2D had +2W^{-D'}) | equality; sz0 Γ=4,Λ=3,Φ=1: coefficient 224 (k=3), 144 (k=2) |
| 2 | drift far bound | ‖drift‖ ≤ W^{-D'} if ℓ_u W^{τ'} ≤ STdiamInf a | clause (Va) of `GoodSetN` + `norm_add₃_le`; any τ', D' | equality |
| 3 | class radius vs EK window | Cls radius ℓ_{u_i}W^{τ'} (STdiamInf, L^∞) vs `EKFastDecay` W^ε ℓ_s (`zdistD`, ℓ¹; Pins:51) | `zdistD_le_mul_zdistInf` (Sizes:122): need d·W^{τ'} ≤ W^ε, ε<1 | sz0 τ'=1/2, ε=9/10: 16.97 ≤ 22.63 (min ε = 0.817) |
| 4 | EK-6 constant C | ∃C>0, C=C(d,k,Λ,κ'), fixed before L,g,W,ε,D | `ekSumDecayNAL_holds d k Λ κ'` (SumDecay:420); antecedents `prop5Decay_holds` (Prop5Hold:784), `prop5Short_holds` (Prop5Short:400) are theorems, so no external hypothesis | — |
| 5 | `hker` coefficients | κ_{im} = W^{Cε} r_{im}^{k-1}; ε_{im} = W^{C}; log L power 0; no ρ_{u,w}, K_w factors | pin conclusion `W^{Cε}r^{n-1}‖A‖ + W^{-D+C}` (Pins:92), `Ugen = UN (EKsgn (mE E) σ)` is `rfl` (ZeroModeCalc:445). RBM2D had (1+log L)^k K_w^{2(k-1)} ρ^k and ((1-u)/(1-w))^k δ: replaced (candidate T2166a) | — |
| 6 | pin hypotheses at (s,t)=(u_i,u_m) | 3≤d, 2≤k, 3≤L, 0<g≤Λ, 1<W, 0<ε<1, 4≤W^ε, 1<D, 0≤u_i≤u_m≤1-g²/L², W⁻¹≤(1-u_m)/(1-u_i), ‖m‖=1, κ'≤Im m, σ non-alternating | written as premises of the theorem (g>0, g≤Λ eventual from `(eq:WO)`, `Sizes.WO` Sizes:164). Window = D74 (follows from `(con_st_ind)` only if d𝔠_d<1, `3_5:1633`). κ'=min(κ,4/5): `mE_im` gives Im m ≥ √(κ-κ²/4) ≥ κ' | sz0: g=1/64≤10; u_m≤1-1.5e-5; window ≥0.969 vs 1/W=0.031; Im m=0.968 vs κ'=1/2 |
| 7 | class level δ | Cls i δ X: 0≤δ<W^{-1} (D = -log_W δ > 1); δ=0 by δ'↓0 | EK-6 needs 1<D (so S3-10b's Cls must carry δ<W^{-1}) | D'=6: δ=9.3e-10 |
| 8 | pair majorant of `qvFormN` | κ_1²·Mee + (κ_1ε_1 + ε_1W^k)W^{-D'}; κ_1=W^{Cε}r^{k-1}, ε_1=W^C; Mee=Γ(ΓΛ)B_u^{2k}/η_u (D4), W^{-D'} from (Vb) | **no 3D `UgenPair` / `ugenPairCase1Explicit`** (grep RBM3D: 0 hits). Route: Re ≤ norm; stage 1 EK-6 on the b'-block with σ̄ (non-alt iff σ), stage 2 on the b-block with σ; stage-2 level W^kδ from row sums `norm_uKer_le` (Evolution:114) ≤ P^k ≤ W^k (window); (Vb) with `Fin.append b b'` gives decay in each block | needs D'-k>1; D'=6,k=3: 3>1 |
| 9 | conj identity | conj(uKer μ v w) = uKer (conj μ) v w (SB real); `qvFormN = Re Σ_b κ_b·(Ugen σ̄ ee(b,·))(a)` | port of `StoppedEndDefs_Theta_star`/`conj_ukerMat` (SED:630/658) via `Theta_mul_of_three_le` (Props4:86), `eq_Theta_of_mul` (Basic:92), `norm_SB` (Block:136) | — |
| 10 | loop shift error | `loopShiftErr` = ℓ η_{u'}^{-(ℓ+1)} (W^{-d})^{ℓ-1} Δ | η≤\|Im z\| at u,u'; \|z'-z\|=Δ (`norm_mE` Semicircle:63); proof via `green_sub_green` (ConArgDet:73), `norm_Gsig_le` (Split:673), `norm_Eblk_le` (Split:681, W^{-d}), `trace_gchain_mul_Eblk` (Split:379) | worst LHS/RHS 0.992 (H=0, E=0, Δ=1/128), all ≤1 |
| 11 | η⁻¹ shift (corrected) | η_{u'}⁻¹ ≤ η_u⁻¹(1+2Δη_u⁻¹), 2Δ≤η_u, u'<1 | RBM2D ticket form (1+Δη⁻¹) false at E=0,u=0,Δ=1/10: 1.1111>1.1000 (`etaT_pos` GLoop:83, Im m ≤ 1) | E=0: 1.111 ≤ 1.2; grid worst 0.992 |
| 12 | Dec shift | W^{-D'} + loopShiftErr(ℓ) ≤ W^{-D''} for 2≤ℓ≤2k+2; ℓ=1 vacuous (STdiamInf of one label = 0, ℓ_u≥1; `one_le_ellT` Params:39) | keep all 2≤ℓ≤2k+2 as hypothesis (η⁻¹W^{-d} can exceed 1 near η~1/N); conclusion only ‖𝓛‖ ≤ W^{-D''} (no 𝒦-shift) | sz0 E=1/2, D'=6: Δ=1/128 D''=4.165; Δ=1/10 D''=3.345; real Δ≤N^{-C_K} gives D''→D' |
| 13 | ee shift | `eeShiftErr` = W^d·k·L^d·loopShiftErr(2k+2) | Σ_{b,b'}\|SB\|=L^d (`sum_SB_row` Block:108); `eeLoop_WF`/`length_eeLoop` (DecayLoopB:468/461) | ratio ≤3.6e-2 (all labels equal) |
| 14 | `ellT_mono` (O3 (3)) | ℓ_u ≤ ℓ_{u'} for every real g | g≥0: `ellT_mono` (PropT:58); g<0: max(g/√·,1)=1 so ellT=min 1 L at both times. **Chosen: direct argument**, no `0≤lam n` hypothesis, no finite-modification lemma. Uses: dec shift; S3-10b `hDcls` (class j+1 from (Va) at u_j) | 0 violations / 20000 samples (g of both signs) |
| 15 | crude Ξ, Ξ shift | STXiLKM ≤ 1+(η^{-n}+M_K)(B_u^{-1})^n needs B_u≤1; B_u monotone in u (g²≥0) so STXiLM(u') ≤ STXiLM(u)+err/B_u^{m-1} | `GoodSetN` has only (G2) STXiLKM, no Ξ^{(𝓛)} clause (T2146a); `norm_gloop_le_of_le_abs_im` (Split:757) | sz0 B_0=3.1e-5 ≤ 1 |
| 16 | D366 level at u=0 | Γ²Λ ≥ k(1+g²)^{2k}, 1≤ΓΦ | `zero_mem_goodSetN_of_levels` (AzumaProxyN:924), any τ', D' | k=3: 3.0044 ≤ 48 (Γ=4,Λ=3,Φ=1) |

Declaration map (RBM2D c9a24cf `Induction/NonAltGood.lean`, `StoppedEndDefs.lean` → 3D). `driftTensor` (SED:570) → new `driftTensorN` := Σ_{l∈Icc 3 k} STksimLKM + STelklkM + STegtM at `loopOf σ a`: `GridDriftN` (GridDriftN:663) states this inline with no named def, so the name is new; it is the `Dr_j` of `GridAssemblyHypN.hexp` (`(Δ:ℂ)•Dr`) and `hdrift` is `‖Dr j ω b‖ ≤ dDrift` (GridAssemblyN:183), not including the `ThetaN` term of `STgDriftN`. :72/:98 → rows 1-2. :120 → rows 8-9. :576 `hker_of_case1` → rows 5-7. :690 → row 9. :159/:185 `Gsig`/`gchain` differences → `Gres`/`gchain` (GLoopFlow:74, Split:306). :245/:338/:359 → `loopL`, `STmaxLM`, `loopFine` (GLoopFlow:123/110). :266, :308, :380, :416, :439/:457/:477, :503/:510 → rows 10, 11, 15, 12, 15, 13 (`STeeM` Step2Defs:757; `STXiLM`/`STXiLKM` GridGoodN:76/82).

### (ii) One concrete nondegenerate instance
`sz0`, n=0, E=1/2, k=3, σ=(+,-,+) (σ_2=σ_0 cyclically, non-alternating), grid u_j=j/128 (K=4, Δ=1/128, the merged `AzumaProxyNInst` data), Γ=4, Λ=3, Φ=1, τ'=1/2, D'=6 (the pair stage needs D'>k+1), ε=9/10, κ=1/2, κ'=1/2, 𝔡=1/10. `0 ∈ GoodSetN` at u=0 is `zero_mem_goodSetN_of_levels` (D366, row 16), so targets 1 and 3 apply to a genuine member. External hypotheses: none (rows 4, 6); the eventual premises are checked along the whole sequence n→∞ below.
Command (scripts in `scratchpad/T2166/`, outside the repository): `cd scratchpad/T2166 && python3 tokcount.py; python3 inst.py; python3 shift_scalar.py; python3 shift_matrix.py`
(first line: d=2-specific token occurrences, §§1-2 of NonAltGood / SED 570-720; matrix script: d=3, L=3, W=2, N=216, random Hermitian H, H=0, E in {0,1.9}, steps (0,1/128), (0,0.1), (0.5,0.1), lengths 1..8, ee loops with `STeeLoop` and `sbKernel`)
```
Z2: 31/11; W^-2 insertion (W:R)^-1^2: 22/0; scaleM: 21/0; BlockIndex: 8/0; Idx L W: 20/4; gloop L W: 14/0; spectralZ/spectralM: 30/2; ellT L (no g): 5/1; SB L: 4/7; rhoR/cCase1/cPair1: 2/2
OK  3<=d, 2<=k, 3<=L 
OK  0<g<=Lambda_pin(=1/dd) g=0.015625 Lam=10.0
OK  1<W, 0<eps<1, 4<=W^eps W^eps=22.6274
OK  1<D(=Dp) and pair stage Dp-k>1 Dp-k=3
OK  nonalternating: exists i sig_i=sig_{i+1 cyc} 
OK  bulk |E|<=2-kap and kap<=Im m Im m=0.9682
OK  1/W <= (1-u_m)/(1-u_i) all i<=m min ratio=0.96875 vs 1/W=0.03125
OK  u_m <= 1-g^2/L^2 g^2/L^2=1.526e-05
OK  class radius: d*W^tau' <= W^eps (zdistD<=d*zdistInf) 16.971 <= 22.627; min eps=0.8170
OK  (eq:WO) dd=1/10: W^(-d/2+dd) <= lam <= 1/dd 0.00781 <= 0.01562
OK  D366: k(1+g^2)^(2k) <= Gam^2 Lam, 1<=Gam*Phi 3.00440 <= 48
OK  drift: sum(D1..D3) = dDrift coefficient (u_0) coef=224, B=3.0987e-05, eta=0.9682, dDrift=6.8833e-12
OK  B_u <= 1 (crude Xi_LK envelope) u_0 
OK  drift: sum(D1..D3) = dDrift coefficient (u_4) coef=224, B=3.1986e-05, eta=0.9380, dDrift=7.8152e-12
OK  B_u <= 1 (crude Xi_LK envelope) u_4 
OK  (k-2)+1 = k-1 for k=2,3 (Icc 3 k has k-2 terms; empty at k=2) 
OK  eventual premises at n=0,1,2,10,1e3,1e6 (0<lam<=1/dd, d W^tau'<=W^eps, 4<=W^eps, WO) W^eps/(d W^tau') = W^0.4/3 >= 4/3, increasing in n
ALL OK
corrected form eta'^-1 <= eta^-1 (1+2 D eta^-1) [2D<=eta]: worst LHS/RHS = 0.992368  (<=1 required)
uncorrected (1+D eta^-1): 77 violations in the grid; at E=0,u=0,D=1/10: eta'^-1=1.11111 > eta^-1(1+D eta^-1)=1.10000: ratio 1.01010
ellT L g u <= ellT L g u' (u<=u'<1), g of both signs: 0 violations in 20000 samples; g<0: both sides equal min 1 L
Delta=0.00781: err(l=1)=8.465e-03 (excluded: STdiamInf=0), err(2)=5.378e-07; k=2: eeShiftErr=6.89e-18, D''=4.164778765; k=3: eeShiftErr=1.39e-26, D''=4.164778765
Delta=0.10000: err(l=1)=1.317e-01 (excluded: STdiamInf=0), err(2)=9.223e-06; k=2: eeShiftErr=1.75e-16, D''=3.345221808; k=3: eeShiftErr=4.28e-25, D''=3.345221808
loop shift, H=gue: max LHS/RHS over l=1..8, 2 energies, 3 steps = 0.1909 at E=0.0 u=0.0 D=0.0078  (<=1 required)
loop shift, H=zero: max LHS/RHS over l=1..8, 2 energies, 3 steps = 0.9922 at E=0.0 u=0.0 D=0.0078  (<=1 required)
loop shift, H=big: max LHS/RHS over l=1..8, 2 energies, 3 steps = 0.0150 at E=0.0 u=0.0 D=0.0078  (<=1 required)
ee shift |ee(u')-ee(u)|/(W^d k L^d err(2k+2)): random labels max 1.48e-08; all labels equal max 3.60e-02  (<=1 required)
```

### Verdicts
- Target 1 (drift tensor, norm bound, far bound, `qvFormN` bound): **PASS**. Norm and far bounds close exactly from (D1)-(D3), (Va). The `qvFormN` bound closes (rows 8-9) but there is no merged 3D pair-kernel estimate; the prover derives it from two applications of `ekSumDecayNAL_holds` and the row sums, with `D' > k+1` as an added premise (paper-delta candidate T2166b, route only).
- Target 2 (`hker` from EK-6): **PASS**; shape differs from RBM2D (rows 5-7: no log L, δ-coefficient W^C, class level δ<W^{-1}, radius with d·W^{τ'} ≤ W^ε); candidate T2166a.
- Target 3 (shift lemmas): **PASS** with the corrected η⁻¹ form (row 11), hypothesis kept for all 2≤ℓ≤2k+2 (row 12), `ellT_mono` handled directly (row 14). `xiL`/`xiLK_crude` have no `GoodSetN` consumer (row 15); 3D forms use `Bctl`.

## (a′) Preflight corrections — Mon Oct  5 01:11:47 UTC 2026
- (ii) fixes `τ' = 1/2`, `ε = 9/10`.  At `n = 0` (`sz0_values`: `L = 4`, `W = 32`) `ℓ_0 = 1` (`ell0` below), so `ℓ_0 W^{τ'} = 5.66 > 2 ≥ diam_∞`
  (`zdist ≤ L/2 = 2`): the far hypotheses of (Va)/(Vb) have no label vector at that datum.  The compiled instances use `τ' = 1/5`,
  `ε = 4/5` (`W^{τ'} = 2`, `W^ε = 16`, `d W^{τ'} = 6 ≤ 16`) and `a = (0, (2,2,2), 0)` with `diam_∞ a = 2`.  No verdict changes.

## (b) Script output

### (b.1) Build, scope, hygiene
$ lake build RBM3D.Induction.NQGood1 2>&1 | grep -E "NQGood1|Build completed|error|sorry" ; lake build 2>&1 | tail -1
Build completed successfully (3799 jobs).
Build completed successfully (3936 jobs).
$ git log --oneline -1; git diff --stat main...t/T2166; wc -l RBM3D/Induction/NQGood1.lean
ff596fc T2166: S3-10a Induction/NQGood1 (drift tensor, hker, QV majorant, good-set shift)
 RBM3D/Induction/NQGood1.lean | 1481 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1481 insertions(+)
    1481 RBM3D/Induction/NQGood1.lean
$ grep -c -E "sorry|admit|native_decide|^axiom" RBM3D/Induction/NQGood1.lean
0

### (b.2) Axioms
$ lake env lean axioms.lean   (scratch file: `#print axioms` of all 63 public declarations of the file, namespaces RBM.Ind and RBM.Ind.NQGood1Inst)
declarations printed: 63; with exactly [propext, Classical.choice, Quot.sound]: 63; any other axiom line (sorryAx, ...): 0
target theorems with exactly those three axioms: 18 of 18: driftTensorN_norm_le_of_goodSet driftTensorN_far_of_goodSet qvFormN_eq_re_UgenPairN hker_of_case1N qvFormN_le_of_goodSetN nqGood1_qvFormN_le_of_bounds nqGood1_ugenPairN_le_of_bounds norm_loopL_zshiftN_le loopMax_zshiftN_le loopFine_shiftN_le STXiLM_shiftN_le goodSetN_dec_shiftN norm_loopFine_crudeN STmaxLKM_crudeN STXiLKM_crudeN etaT_inv_shiftN_le norm_STeeM_shiftN_le nqGood1_ellT_mono

### (b.3) Registry pre-check (CLAUDE.md §3 (A): the hub adds the root import at merge)
$ lake env lean reg.lean   (scratch file: `import RBM3D`, `import RBM3D.Induction.NQGood1`, `#assert_rbm_axioms`)
axiom audit: 4913 theorems, 1723 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
RBM.Gauss.Sizes.STOeqNQ: 1 [no certificate]
non-vacuity certificates: 0 of 86 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` sa
$ diff reg0.out reg.out   (reg0.lean = `import RBM3D` + `#assert_rbm_axioms`, without the new module)
1c1
< axiom audit: 4859 theorems, 1714 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
> axiom audit: 4913 theorems, 1723 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).

### (b.4) Target statements, extracted by script
$ python3 extract.py <names>   (declaration text up to the top-level ":=", whitespace collapsed; file RBM3D/Induction/NQGood1.lean)
def driftTensorN (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ
theorem driftTensorN_norm_le_of_goodSet {n : ℕ} {E u Γ Λ Φ τ' D' : ℝ} {k : ℕ} (hk : 2 ≤ k) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D') (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ‖driftTensorN sz n E u M σ a‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / etaT E u) * (((k : ℝ) - 1) + (k : ℝ) * (Γ * Φ))
theorem driftTensorN_far_of_goodSet {n : ℕ} {E u Γ Λ Φ τ' D' : ℝ} {k : ℕ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D') (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (hfar : ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)) : ‖driftTensorN sz n E u M σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')
def UgenPairN (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) : ℂ
theorem qvFormN_eq_re_UgenPairN (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) {v w : ℝ} (hw : |w| < 1) {k : ℕ} (σ : Fin k → Bool) (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin k → Zd d (sz.L n)) : qvFormN sz n E v w σ M a = (UgenPairN d (sz.L n) (sz.lam n) E σ v w (fun b b' => sz.STeeM n E v M σ b b') a).re
def nqGood1C (d k : ℕ) (Λg κ' : ℝ) : ℝ
theorem hker_of_case1N {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg) (hκ' : 0 < κ') {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg) {W ε τ' D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε) (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hD : 1 < D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2) (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (X : (Fin k → Zd d L) → ℂ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδD : δ ≤ W ^ (-D)) (hXM : ∀ b, ‖X b‖ ≤ M) (hXcls : ∀ b : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf b : ℝ) → ‖X b‖ ≤ δ) (a : Fin k → Zd d L) : ‖Ugen d L g E σ s t X a‖ ≤ W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1) * M + W ^ nqGood1C d k Λg κ' * δ
theorem nqGood1_ugenPairN_le_of_bounds {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg) (hκ' : 0 < κ') {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λg) {W ε τ' D : ℝ} (hW : 1 < W) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ W ^ ε) (hdW : (d : ℝ) * W ^ τ' ≤ W ^ ε) (hD : (k : ℝ) + 1 < D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2) (hWt : W⁻¹ ≤ (1 - t) / (1 - s)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) {Mee δ : ℝ} (hδ : 0 ≤ δ) (hδD : δ ≤ W ^ (-D)) (hT : ∀ b b', ‖T b b'‖ ≤ Mee) (hTfar : ∀ b b' : Fin k → Zd d L, ellT L g s * W ^ τ' ≤ (STdiamInf (Fin.append b b') : ℝ) → ‖T b b'‖ ≤ δ) (a : Fin k → Zd d L) : ‖UgenPairN d L g E σ s t T a‖ ≤ (W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1)) * ((W ^ (nqGood1C d k Λg κ' * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (k - 1)) * Mee + W ^ nqGood1C d k Λg κ' * δ) + W ^ nqGood1C d k Λg κ' * (W ^ k * δ)
theorem qvFormN_le_of_goodSetN {d k : ℕ} (Λg κ' : ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) (hΛ : 0 < Λg) (hκ' : 0 < κ') (sz : Sizes d) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) {ε τ' D' : ℝ} (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hε0 : 0 < ε) (hε1 : ε < 1) (hWε : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hdW : (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε) (hD' : (k : ℝ) + 1 < D') {u w : ℝ} (hu0 : 0 ≤ u) (huw : u ≤ w) (hwL : w ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hWt : (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - w) / (1 - u)) {E : ℝ} (hE : |E| ≤ 2) (hκm : κ' ≤ (mE E).im) {σ : Fin k → Bool} (hσ : ∃ i, σ i = σ (finRotate k i)) {Γ Λ Φ : ℝ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D') (a : Fin k → Zd d (sz.L n)) : qvFormN sz n E u w σ M a ≤ ((((sz.W n : ℕ) : ℝ)) ^ (nqGood1C d k Λg κ' * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) * ((((sz.W n : ℕ) : ℝ) ^ (nqGood1C d k Λg κ' * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) * (Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / etaT E u)) + ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * ((sz.W n : ℕ) : ℝ) ^ (-D')) + ((sz.W n : ℕ) : ℝ) ^ nqGood1C d k Λg κ' * (((sz.W n : ℕ) : ℝ) ^ k * ((sz.W n : ℕ) : ℝ) ^ (-D'))
def loopShiftErrN (d W : ℕ) (η : ℝ) (ℓ : ℕ) (Δ : ℝ) : ℝ
theorem norm_loopL_zshiftN_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (I : Loop.LoopIdx (Zd d L)) (hwf : I.σ.length = I.a.length) (hlen : 1 ≤ I.a.length) : ‖loopL d L W H z' I - loopL d L W H z I‖ ≤ (I.a.length : ℝ) * (η⁻¹ ^ (I.a.length + 1) * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1) * ‖z' - z‖)
theorem loopFine_shiftN_le {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) {u u' : ℝ} (huu' : u ≤ u') (hu'1 : u' < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d L) : ‖loopFine d L W M (zt E u') σ a‖ ≤ ‖loopFine d L W M (zt E u) σ a‖ + loopShiftErrN d W (etaT E u') ℓ (u' - u)
theorem STXiLM_shiftN_le (n : ℕ) {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u u' : ℝ} (huu' : u ≤ u') (hu'1 : u' < 1) {m : ℕ} (hm : 1 ≤ m) : sz.STXiLM n E u' m M ≤ sz.STXiLM n E u m M + loopShiftErrN d (sz.W n) (etaT E u') m (u' - u) / (sz.Bctl n u) ^ (m - 1)
theorem goodSetN_dec_shiftN (n : ℕ) {E : ℝ} (hE : |E| < 2) {k : ℕ} {Γ Λ Φ τ' D' D'' : ℝ} {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {u u' : ℝ} (hM : M ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D') (huu' : u ≤ u') (hu'1 : u' < 1) (hδ : ∀ ℓ : ℕ, 2 ≤ ℓ → ℓ ≤ 2 * k + 2 → ((sz.W n : ℕ) : ℝ) ^ (-D') + loopShiftErrN d (sz.W n) (etaT E u') ℓ (u' - u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)), ellT (sz.L n) (sz.lam n) u' * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) → ‖loopFine d (sz.L n) (sz.W n) M (zt E u') σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')
theorem norm_loopFine_crudeN (n : ℕ) {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u : ℝ} (hu1 : u < 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (σ : Fin ℓ → Bool) (a : Fin ℓ → Zd d (sz.L n)) : ‖loopFine d (sz.L n) (sz.W n) M (zt E u) σ a‖ ≤ (etaT E u)⁻¹ ^ ℓ
theorem STXiLKM_crudeN (n : ℕ) {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hB1 : sz.Bctl n u ≤ 1) {n' m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n') {MK : ℝ} (hK : ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)), ‖STKloop sz n E u σ a‖ ≤ MK) : sz.STXiLKM n E u m M ≤ 1 + ((etaT E u)⁻¹ ^ n' + MK) / (sz.Bctl n u) ^ n'
theorem etaT_inv_shiftN_le {E : ℝ} (hE : |E| < 2) {u u' : ℝ} (huu' : u ≤ u') (hu'1 : u' < 1) (hΔ : 2 * (u' - u) ≤ etaT E u) : (etaT E u')⁻¹ ≤ (etaT E u)⁻¹ * (1 + 2 * (u' - u) * (etaT E u)⁻¹)
def eeShiftErrN (d L W : ℕ) (E : ℝ) (k : ℕ) (u u' : ℝ) : ℝ
theorem norm_STeeM_shiftN_le (n : ℕ) {E : ℝ} (hE : |E| < 2) {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {u u' : ℝ} (huu' : u ≤ u') (hu'1 : u' < 1) {k : ℕ} (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)) : ‖sz.STeeM n E u' M σ a a' - sz.STeeM n E u M σ a a'‖ ≤ eeShiftErrN d (sz.L n) (sz.W n) E k u u'
theorem nqGood1_ellT_mono (L : ℕ) (g : ℝ) {u t : ℝ} (hut : u ≤ t) (ht : t < 1) : ellT L g u ≤ ellT L g t

$ sed -n '/^def <name> /,/^$/p' RBM3D/Induction/NQGood1.lean   (bodies of the five `def`s: driftTensorN, UgenPairN, nqGood1C, loopShiftErrN, eeShiftErrN)
def driftTensorN (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  ∑ l ∈ Finset.Icc 3 k, sz.STksimLKM n E u H l (loopOf σ a) +
    sz.STelklkM n E u H (loopOf σ a) + sz.STegtM n E u H (loopOf σ a)
def UgenPairN (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (T : (Fin k → Zd d L) → (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) : ℂ :=
  ∑ b : Fin k → Zd d L, ∑ b' : Fin k → Zd d L,
    (∏ i : Fin k, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
      (∏ i : Fin k, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) * T b b'
def nqGood1C (d k : ℕ) (Λg κ' : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' then
    Classical.choose (ekSumDecayNAL_holds d k Λg κ' (prop5Decay_holds d Λg)
      (prop5Short_holds d Λg κ') h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 1
def loopShiftErrN (d W : ℕ) (η : ℝ) (ℓ : ℕ) (Δ : ℝ) : ℝ :=
  (ℓ : ℝ) * (η⁻¹ ^ (ℓ + 1) * (((W : ℝ) ^ d)⁻¹) ^ (ℓ - 1) * Δ)
def eeShiftErrN (d L W : ℕ) (E : ℝ) (k : ℕ) (u u' : ℝ) : ℝ :=
  ((W : ℝ) ^ d) * ((k : ℝ) * (((L : ℝ) ^ d) * loopShiftErrN d W (etaT E u') (2 * k + 2) (u' - u)))

### (b.5) Compiled nonempty instances (`d = 3`, `sz0`, `n = 0`, `E = 1/2`, `k = 3`, `σ = (+,-,+)`, `(Γ,Λ,Φ) = (4,3,1)` with `Γ²Λ = 48 ≥ 3(1+g²)^6` (D366), `τ' = 1/5`, `D' = 6`, `ε = 4/5`, `Λ_g = 10`, `κ' = 1/2`, grid `u_0 = 0`, `u_1 = 1/128`)
$ python3 extract.py <instance names>   (statements of compiled instances; namespace RBM.Ind.NQGood1Inst; 34 declarations in the section)
theorem zero_mem_goodSetN_inst : (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈ sz0.GoodSetN 0 (1 / 2) 0 3 4 3 1 (1 / 5) 6
theorem drift_norm_instance (a : Fin 3 → Zd 3 (sz0.L 0)) : ‖driftTensorN sz0 0 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 a‖ ≤ 4 * (4 * 1) * ((sz0.Bctl 0 0) ^ 3 / etaT (1 / 2) 0) * (((3 : ℕ) : ℝ) - 1 + ((3 : ℕ) : ℝ) * (4 * 1))
theorem drift_far_instance : ‖driftTensorN sz0 0 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 aFar‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))
theorem qvFormN_instance : qvFormN sz0 0 (1 / 2) 0 (1 / 128) sig3 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) aFar ≤ ((((sz0.W 0 : ℕ) : ℝ)) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) * ((sz0.lam 0 ^ 2 + |1 - 0|) / (sz0.lam 0 ^ 2 + |1 - 1 / 128|)) ^ (3 - 1)) * ((((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) * ((sz0.lam 0 ^ 2 + |1 - 0|) / (sz0.lam 0 ^ 2 + |1 - 1 / 128|)) ^ (3 - 1)) * (4 * (4 * 3) * ((sz0.Bctl 0 0) ^ (2 * 3) / etaT (1 / 2) 0)) + ((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ))) + ((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2) * (((sz0.W 0 : ℕ) : ℝ) ^ 3 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
theorem etaT_inv_shift_instance : (etaT (1 / 2) (1 / 128))⁻¹ ≤ (etaT (1 / 2) 0)⁻¹ * (1 + 2 * (1 / 128 - 0) * (etaT (1 / 2) 0)⁻¹)
theorem dec_shift_instance : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * 3 + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd 3 (sz0.L 0)), ellT (sz0.L 0) (sz0.lam 0) (1 / 128) * ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf a : ℝ) → ‖loopFine 3 (sz0.L 0) (sz0.W 0) (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) (zt (1 / 2) (1 / 128)) σ a‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(3 : ℝ))
theorem STeeM_shift_instance : ‖sz0.STeeM 0 (1 / 2) (1 / 128) (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 aFar aFar - sz0.STeeM 0 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 aFar aFar‖ ≤ eeShiftErrN 3 (sz0.L 0) (sz0.W 0) (1 / 2) 3 0 (1 / 128)
theorem ellT_mono_instance : ellT (sz0.L 0) (sz0.lam 0) 0 ≤ ellT (sz0.L 0) (sz0.lam 0) (1 / 128) ∧ ellT (sz0.L 0) (-(1 / 64)) 0 ≤ ellT (sz0.L 0) (-(1 / 64)) (1 / 128)
$ sed -n '/^theorem hker_instance/,/^$/p' RBM3D/Induction/NQGood1.lean   (every hypothesis discharged in the term)
theorem hker_instance (a : Fin 3 → Zd 3 (sz0.L 0)) :
    ‖Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) sig3 0 (1 / 128) Xinst a‖ ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (nqGood1C 3 3 10 (1 / 2) * (4 / 5)) *
          ((sz0.lam 0 ^ 2 + |1 - 0|) / (sz0.lam 0 ^ 2 + |1 - 1 / 128|)) ^ (3 - 1) * 1 +
        ((sz0.W 0 : ℕ) : ℝ) ^ nqGood1C 3 3 10 (1 / 2) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) :=
  hker_of_case1N (d := 3) (k := 3) 10 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (sz0.three_le_L 0) (g := sz0.lam 0) (by rw [lam0]; norm_num)
    (by rw [lam0]; norm_num) hW_inst (by norm_num) (by norm_num) hWε_inst hdW_inst
    (D := 6) (by norm_num) (s := 0) (t := 1 / 128) le_rfl (by norm_num) hwL_inst hWt_inst
    (E := 1 / 2) (by norm_num [abs_of_pos]) im_mE_half hσ_inst Xinst (M := 1) (δ := ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)))
    zero_le_one (Real.rpow_nonneg (by rw [W0]; norm_num) _) le_rfl Xinst_norm_le Xinst_far a
$ sed -n '/^theorem drift_far_instance/,/^$/p' RBM3D/Induction/NQGood1.lean   (the far label vector `aFar`, `diam_aFar : 2 ≤ STdiamInf aFar`)
theorem drift_far_instance :
    ‖driftTensorN sz0 0 (1 / 2) 0 (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0))
        (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) sig3 aFar‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(6 : ℝ)) := by
  refine driftTensorN_far_of_goodSet sz0 zero_mem_goodSetN_inst sig3 aFar ?_
  rw [ell0, W0, rpow32_fifth]
  have := diam_aFar
  exact_mod_cast (by omega : (1 : ℕ) * 2 ≤ STdiamInf aFar)

### (b.6) Name-clash grep (new public names against `main`)
$ for n in <the 63 short names of the file>; do git grep -n -E "(theorem|def|lemma|abbrev|structure|instance)[[:space:]]+(private[[:space:]]+)?([A-Za-z0-9_.]*\.)?$n([[:space:]]|$)" main -- RBM3D; done   (main = daa7cc1)
names checked: 63; total hits on main: 0; names with hits: none
$ git grep -n -E "ugenPairCase1Explicit|UgenPair|ugenCase1Explicit|driftTensor" main -- RBM3D | wc -l
       0

### (b.7) Ports (read-only sources: RBM2D `NonAltGood.lean:67-559`, `StoppedEndDefs.lean:570,575,690` at `c9a24cf`)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/NonAltGood.lean RBM2D/Induction/StoppedEndDefs.lean
9e0f275
 RBM2D/Induction/NonAltGood.lean     | 1629 ++---------------------------------
 RBM2D/Induction/StoppedEndDefs.lean |  598 ++-----------
 2 files changed, 149 insertions(+), 2078 deletions(-)

### (b.8) Narrative (written Mon Oct  5 01:12:40 UTC 2026)
- One new file, `RBM3D/Induction/NQGood1.lean`, 1481 lines, commit `ff596fc` on `t/T2166`; it imports the ten merged modules of the ticket plus
  `Mathlib.Analysis.SpecialFunctions.Log.Base` (without it `Real.logb` is an unknown constant: first compile of the `hker` proof).
- Drift: `GridDriftN` states `Σ_{l=3}^k STksimLKM + STelklkM + STegtM` inline (`GridDriftN.lean:670-673`), so `driftTensorN` is a new name.  The norm bound
  `Γ(ΓΦ)(B_u^k/η_u)((k-1)+kΓΦ)` (needs `2 ≤ k`) is `(k-2)` copies of (D1) plus (D2) plus (D3); the far bound is clause (Va).  No additive `W^{-D'}`.
- `hker_of_case1N` comes from `ekSumDecayNAL_holds` with `Prop5Decay`, `Prop5Short` discharged by `prop5Decay_holds`, `prop5Short_holds`; the constant is
  `nqGood1C d k Λ_g κ'` (`Classical.choose` of the EK-6 existential, `0 <` by `nqGood1C_pos`).  The kernel bound has no `log L` power and no `ρ`, `K_w` factors:
  `W^{Cε} ((g²+|1-s|)/(g²+|1-t|))^{k-1} M + W^C δ`.  The class is `δ ≤ W^{-D}`, `D > 1`; `δ = 0` is the limit `D → ∞`.  The `L^∞` radius
  `ℓ_s W^{τ'}` of `GoodSetN` becomes the `ℓ¹` window `W^ε ℓ_s` of EK-6 under the premise `d W^{τ'} ≤ W^ε` (`zdistD_le_mul_zdistInf`).
- QV majorant: no 3D `ugenPairCase1Explicit` exists (0 hits, (b.6)), so `nqGood1_ugenPairN_le_of_bounds` applies `hker_of_case1N` twice: the `b'`-block with `σ̄ = !σ`
  (non-alternating iff `σ`) on `b' ↦ T_{b,b'}`, then the `b`-block with `σ` on `b ↦ (𝒰_σ̄ ∘ T_{b,·})(a)`, whose far level `W^k δ` is the row-sum bound
  `norm_UN_apply_le` with `(1-s)/(1-t) ≤ W`.  It needs `D' > k+1`.  `nqGood1_qvFormN_le_of_bounds` takes bounds on `STeeM n E v M` at any time `v`, so S3-10b can
  feed it `M_ee + eeShiftErrN`, `δ + eeShiftErrN`; `qvFormN_le_of_goodSetN` is the case `v = u` with (D4), (Vb).
- Shift: the loop bound is `ℓ η_{u'}^{-(ℓ+1)} (W^{-d})^{ℓ-1} Δ` (`loopShiftErrN`); `goodSetN_dec_shiftN` takes the hypothesis for `2 ≤ ℓ ≤ 2k+2` because `ℓ = 1` is
  vacuous (`nqGood1_STdiamInf_one`, `ℓ_{u'} W^{τ'} > 0`); its conclusion is the `𝓛` part only (no `𝒦` shift).  `η⁻¹` shift: corrected form
  `η_{u'}⁻¹ ≤ η_u⁻¹(1 + 2Δη_u⁻¹)` under `2Δ ≤ η_u`.
- `ellT_mono` (CONTROL §45 O3 (3)): `nqGood1_ellT_mono` is the direct argument (`g ≥ 0`: `ellT_mono`; `g < 0`: both sides `min 1 L`); no finite-modification lemma, no `0 ≤ lam n`
  hypothesis.  `0 < g ≤ Λ_g` is a premise of `hker_of_case1N` and `0 < lam n ≤ Λ_g` of `qvFormN_le_of_goodSetN` (as `0 < g ≤ Λ` in EK-6).
- Premise shapes (§29 (6)): `|E| ≤ 2` and `κ' ≤ Im m(E)` replace `|E| ≤ 2 - κ`; `nqGood1_mE_im_ge` gives `min κ (4/5) ≤ Im m(E)` from `|E| ≤ 2 - κ`.  `u_j < 1` follows from
  `t ≤ 1 - g²/L²`.  D366: every instance passes the levels `(4,3,1)` through `zero_mem_goodSetN_of_levels`.
- Not in this file: the fields `hker`, `hdrift`, `hDcls`, `hA0cls` of `GridAssemblyHypN`, the classes, `qvBd` constants, the shifted majorant (S3-10b); the root import (hub).

## (c) Verified names
Mathlib/core names used, each `#check`ed by script (`mathlib_names.sh`, 49 names, 0 missing): `Real.logb`, `Real.rpow_logb`, `Real.logb_le_iff_le_rpow` (these three need the import above),
`Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`,
`le_of_forall_pos_le_add`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `inv_le_of_inv_le₀`, `inv_anti₀`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`,
`pow_le_pow_of_le_one`, `pow_le_pow_left₀`, `pow_le_one₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `one_le_inv₀`, `Finset.sup'_le`, `Finset.le_sup'`, `Finset.le_sup'_of_le`, `Finset.le_sup`,
`Finset.sup_le`, `Finset.sum_le_card_nsmul`, `Finset.sum_sub_distrib`, `Nat.card_Icc`, `Fin.append_left`, `Fin.append_right`, `List.eq_nil_or_concat'`, `Matrix.isHermitian_zero`,
`Matrix.IsHermitian.submatrix`, `Matrix.trace_sub`, `dite_eq_left_of_eq_true`, `Complex.re_le_norm`, `Complex.abs_im_le_norm`, `ciSup_le`, `le_ciSup`, `norm_sub_norm_le`, `norm_add₃_le`,
`div_nonpos_of_nonpos_of_nonneg`, `Subsingleton.elim`, `Complex.conj_ofReal`.
Names whose old forms the tool log rejected: `dif_pos`, `dite_cond_eq_true`, `if_false`, `push_neg` (deprecated warnings); `add_le_add_left` has the form `b + a ≤ c + a` (type mismatch), used `add_le_add le_rfl`.
Merged names used (all resolve): `GoodSetN`, `qvFormN`, `STksimLKM`, `STelklkM`, `STegtM`, `STeeM`, `ekSumDecayNAL_holds`, `prop5Decay_holds`, `prop5Short_holds`, `zero_mem_goodSetN_of_levels`,
`norm_UN_apply_le`, `green_sub_green`, `Gres_eq_green_zSig`, `isUnit_sub_zSig`, `norm_gchain_le`, `norm_gloop_le_of_le_abs_im`, `Sizes.STBctl_pos`, `Sizes.STBctl_mono`, `ellT_mono`, `eeLoop_WF`, `length_eeLoop`.

## (d) Open issues and paper-delta candidates
Paper-delta candidates (Lean/paper differences; the dispatcher numbers them):
- `T2166a`: `hker` for non-alternating `σ` has the coefficients `W^{Cε} r^{k-1}` and `W^C δ` of EK-6 (`r = (g²+|1-s|)/(g²+|1-t|)`), class `δ ≤ W^{-D}`, `D > 1`; RBM2D's
  `(1+log L)^k K_w^{2(k-1)} ρ^k` and `((1-u)/(1-w))^k δ` do not occur; premise `d W^{τ'} ≤ W^ε` (`L^∞` window of `GoodSetN` to the `ℓ¹` window of EK-6).
- `T2166b`: the QV majorant `κ₁(κ₁ Γ(ΓΛ)B_u^{2k}/η_u + W^C W^{-D'}) + W^C W^k W^{-D'}` needs `D' > k+1`; route (two uses of EK-6, row sums), not the paper's one-step pair estimate.
- `T2166c`: `η⁻¹` shift in the corrected form `η_{u'}⁻¹ ≤ η_u⁻¹(1 + 2Δη_u⁻¹)`, `2Δ ≤ η_u` (the form `(1 + Δη_u⁻¹)` is false at `E = 0`, `u = 0`, `Δ = 1/10`: preflight row 11).
- `T2166d`: `goodSetN_dec_shiftN` has the hypothesis for `2 ≤ ℓ ≤ 2k+2` and concludes the `𝓛` part only; `ℓ = 1` is vacuous.
- `T2166e`: `ℓ_u ≤ ℓ_{u'}` for every real `g` (`nqGood1_ellT_mono`), so no `0 ≤ lam n` hypothesis is needed (O3 (3)).
- `T2166f`: `STXiLM_shiftN_le` (the `Ξ̂^{(𝓛)}` shift) uses `Bctl` monotone (`STBctl_mono`); `GoodSetN` has no `Ξ̂^{(𝓛)}` clause (T2146a), so it has no clause to shift; `STXiLKM_crudeN` needs `B_u ≤ 1` and a bound `M_K` of `‖𝒦‖`.
- `T2166g`: `nqGood1C` is the EK-6 constant for `(d, k, Λ_g, κ')`, `κ' = min κ (4/5)` from `|E| ≤ 2 - κ`; `driftTensorN` is a new name for the inline sum of `GridDriftN`.
Open issues:
- S3-10b must supply as premises: `0 < lam n ≤ Λ_g`, `4 ≤ W^ε`, `d W^{τ'} ≤ W^ε`, `D' > k+1`, `W⁻¹ ≤ (1-u_m)/(1-u_i)`, `u_m ≤ 1 - g²/L²`; its class `Cls i δ X` must carry `0 ≤ δ ≤ W^{-D}`, `D > 1`.
- `ε` with `τ' + log_W d ≤ ε < 1` and `4 ≤ W^ε` is a consumer choice (instances: `ε = 4/5`, `τ' = 1/5` at `W = 32`).
- The new module is not imported by `RBM3D.lean` (hub, at merge); no registry line is needed: no theorem takes a pin `Prop` as a hypothesis ((b.3)).
