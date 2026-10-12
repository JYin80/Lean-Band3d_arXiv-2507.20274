Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 12:08:42 UTC 2026
Targets (mathematics only). T1: `BATwistStepFixed d R → BATwistLoopStep d R` (same frame `BATwFrame`, `TwistPins:146,160`; `h` at the same `(κ,ε,𝔡,Cd)` gives the same `𝔠d`). T2: T1 at `STCaseI/II`. T3: `K̃^∘ := K̃ − W^{-d} M(σ₁)_{ac₁} M(σ₀)_{c₂a}` obeys `‖K̃^∘‖ ≤ C·Bctl`, `Σ_a‖K̃^∘‖ ≤ C(W^dη)⁻¹`. Route of T1: round 0 `Ξ₀ = 2(2/κ)²N⁴` (`TwistStep_zcrude`, `TwistStep:769`); round j: `h` at `Ξ_j` per `τ` → `PerTimeDomAt` (sections) → `cont_core` → `PrecL` on `TimeIcc` at `Ξ_{j+1} = 1 + Ξ_j·b_n`, `b_n = Bctl_n(t_n)^{1/6}` (`Bctl` increasing in `v<1`); after `J` rounds `Ξ_J ≤ J+1`; one more round gives TL2 at `τ`.

### (i) Exponent table  (N = sz.size n; all `∀ᶠ n` are finitely many and composed only in the last step)
| # | constant | value / source | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠d` | `h`'s, `0<𝔠d≤1/100`, depends on `(d,κ,ε,𝔡,Cd)` only; frame premises pass unchanged | none new; `J` below depends on `𝔠` (inside `∀𝔠`), not `𝔠d` | – |
| 2 | `Ξ₀` | `2(2/κ)²N⁴`, `κ ≤ Im m ≤ 1` (`BAflow_real`, `BAself_im_le_one`) | `‖Z_v‖ ≤ Ξ₀B_v^{3/2}` on `[s,t]⊂[0,T₀]` (`ST_prec_of_le_ev`); pin needs `Ξ≥1` | `Ξ₀ ≥ 8N⁴` |
| 3 | `C`, `C'` of `baGopbound` | `C_G = 6`, `C' = 2C+10 = 22`; net exponent `A = 22` | `A ≥ C'`, `0≤u,u'≤1−N⁻¹` | `A = C'` exactly |
| 4 | window | `1−T₀ ≥ Im z/2 ≥ N^{-1+ε}/2` (`EMn2BA_one_sub_T0`, `EMn2BA:111`); need `t_n ≤ 1−N⁻¹` | `N^ε ≥ 2` | factor `N^ε/2` |
| 5 | `Cv` of `cont_core` | `4`: `#V = 4·(L^d)³ ≤ 4N³` (`(Fin 2→Bool)` has 4 elements) | `4N³ ≤ N⁴` | `N/4` |
| 6 | `ε_n` (hlow) | `N^{-3/2}` ≤ `Ξ_{j+1}B^{3/2}` since `B ≥ N⁻¹` (`cont_inv_size_le_Bctl`, `ContinuityNet:701`), `Ξ_{j+1}≥1` | `ε_n ≥` both Lipschitz errors | rows 7, 8 |
| 7 | `G`-part of the time-Lipschitz constant | `‖G_u−G_{u'}‖_max ≤ N⁻⁶` on the `baGopbound` event; `‖G_u‖ ≤ N/κ`; `‖ΔL̃‖ ≤ 2N·N⁻⁶/κ` (average of `W^{2d}` products) | `≤ ε_n/2` | `N^{7/2}κ/4 ≥ 1` |
| 8 | `K̃`-part (new) | `Θ_s−Θ_t=(s−t)Θ_sMΘ_t`, `‖M^{σσ'}‖_{∞→∞}≤1`, `‖Θ_t‖_{∞→∞}≤(1−t)⁻¹` ⇒ `Σ_{a'}‖ΔΘ‖ ≤ N²|Δt|`; `|M_{xy}| ≤ C_M` (`BAMB_row_l1`) ⇒ `‖ΔK̃‖ ≤ C_M²N²·N⁻²²` | `≤ ε_n/2` | `N^{37/2} ≥ 2C_M²` |
| 9 | factor 2 for `ζ=Ξ B^{3/2}` | `x=(1−t)⁻¹|Δu| ≤ N⁻²¹`; `B_{u'} ≤ (1+x)B_u` (`cont_inv_add_one_sub_ratio` `:676` on both terms of `cont_Bctl_eq`) | `(1+x)^{3/2} ≤ 2` iff `x ≤ 0.587` | `0.587/N⁻²¹` |
| 10 | contraction `c` | `Bctl_t ≤ (lam²W^d)⁻¹+(N(1−t))⁻¹ ≤ W^{-2𝔡}+2N^{-ε} ≤ 3N^{-c₀}`, `c₀=min(2𝔡𝔠,ε)` (`lam_sq_mul_pow_ge`, `Sizes:193`; `W≥N^𝔠`; row 4); `c=c₀/12` | `b_n ≤ N^{-c}` iff `N^{c₀/12} ≥ 3^{1/6}` | sz0: `c₀=1/30`, `c=1/360`; szII: `c₀=1/45`, `c=1/540` |
| 11 | `J` | `⌈5/c⌉` (sz0 1800; szII 2700); `Ξ_J ≤ Σ_{i<J}b^i + b^JΞ₀ ≤ J + N^{-cJ}·2(2/κ)²N⁴ ≤ J+1` | `N^{cJ−4} ≥ 2(2/κ)²`; `cJ−4 ≥ 1` | needs only `N ≥ 2(2/κ)²` |
| 12 | final absorption | `1+b_nΞ_J ≤ J+2` (`b_n≤1`), absorbed by `N^{τ'/2} ≥ J+2` (apply round `J+1` at `τ'/2`) | eventually | – |
| 13 | T3 constant `C` | `C = C_K + (𝔡⁻²+1)C_M²`, `C_K` of `twK_bound_holds` (`TwistPins:692`), `C_M = c⁻¹expC` of `BAMB_row_l1` (`GreenSchur:139`) | `W^{-d} ≤ (𝔡⁻²+1)Bctl` (`twB0_ge_holds`); `Σ_a|M_{ac₁}||M_{c₂a}| ≤ C_M²`; `η=(1−t)Im m ≤ 1` | `(𝔡⁻²+1)` is 101 at `𝔡=1/10` |
Stop rules checked: `baGopbound` gives the `G`-entries of `twL2'` (`baFM.G := BAGt`, `FlowPins:325`) with `κ ≤ Im m`, `‖m‖≤1`; the contraction uses only `BAFlow.1 = Admissible` (`WO`, `Bandwidth`). No premise outside `BATwistStepFixed`/`BATwFrame` is needed.

### (ii) Concrete instance (d=3), command and output (scripts `ev.py`, `kc.py`, `lines.py` in the scratchpad `T2451/`, Python only)
`python3 ev.py` (L=4(n+1), W=(2(n+1))⁵, lam=(2(n+1))⁻⁶, z=w−m_w, w=6i/5, `m_w = L⁻³Σ_k(lam·λ_k−w)⁻¹`, `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)` = `flow_sz0`, s≡1/2, t≡2/3 (STCaseI); szII: L=4, W=n+25, lam=5, w=5003i/5000, `(3/5000,1/2,1/9,1/10)` = `TwistStep2_flowII`, s≡0, t≡1/2000 (STCaseII))
```
sz0 n=8: N=3.148e+23 Imm=0.8333 T0=0.69444 t=0.66667<=T0 ok; 1-T0=3.056e-01>=N^(-1+e)/2=3.55e-22 ok, >=1/N ok
   W>=N^cc ok; WO ok; kappa<=Imm ok; Bctl_t=4.447e-19<=W^-2dd+2N^-eps=6.449e-02 ok; b=8.737e-04<=N^-c=0.860 ok
   Xi0=2(2/k)^2N^4=3.141e+95; rounds with Xi_j<=2 (actual b)=32; Xi_60=1.000874; thresholds: N^(cJ-4)>=N=True ; N>=2(2/k)^2 ok; N>=4 ok
sz0 n=20: N=1.323e+30 Imm=0.8333 T0=0.69444 t=0.66667<=T0 ok; 1-T0=3.056e-01>=N^(-1+e)/2=3.89e-28 ok, >=1/N ok
   W>=N^cc ok; WO ok; kappa<=Imm ok; Bctl_t=1.344e-24<=W^-2dd+2N^-eps=2.575e-02 ok; b=1.051e-04<=N^-c=0.825 ok
   Xi0=2(2/k)^2N^4=9.805e+121; rounds with Xi_j<=2 (actual b)=31; Xi_60=1.000105; thresholds: N^(cJ-4)>=N=True ; N>=2(2/k)^2 ok; N>=4 ok
sz0 generic: c0=min(2*dd*cc,eps)=0.03333 c=c0/12=0.002778 J=ceil(5/c)=1800
szII n=0: N=1.000e+06 Imm=0.3175 T0=0.31727 t=0.00050<=T0 ok; 1-T0=6.827e-01>=N^(-1+e)/2=5.00e-04 ok, >=1/N ok
   W>=N^cc ok; WO ok; kappa<=Imm ok; Bctl_t=3.462e-06<=W^-2dd+2N^-eps=5.273e-01 ok; b=1.230e-01<=N^-c=0.975 ok
   Xi0=2(2/k)^2N^4=2.222e+31; rounds with Xi_j<=2 (actual b)=35; Xi_60=1.140245; thresholds: N^(cJ-4)>=N=True ; N>=2(2/k)^2 FAIL; N>=4 ok
szII n=200: N=7.290e+08 Imm=0.3175 T0=0.31727 t=0.00050<=T0 ok; 1-T0=6.827e-01>=N^(-1+e)/2=1.85e-05 ok, >=1/N ok
   W>=N^cc ok; WO ok; kappa<=Imm ok; Bctl_t=4.749e-09<=W^-2dd+2N^-eps=3.386e-01 ok; b=4.100e-02<=N^-c=0.963 ok
   Xi0=2(2/k)^2N^4=6.276e+42; rounds with Xi_j<=2 (actual b)=31; Xi_60=1.042751; thresholds: N^(cJ-4)>=N=True ; N>=2(2/k)^2 ok; N>=4 ok
szII generic: c0=0.02222 c=0.001852 J=2700
```
Limit of the contraction at sz0: `b_n(n+1)^{5/2} = 0.2123 (n=8), 0.2124 (n=20)` (`python3 -c "print(8.737e-4*9**2.5, 1.051e-4*21**2.5)"` -> `0.2123091 0.2123982591430777`, the `b` printed above), so `b_n → 0` like `(n+1)^{-5/2}`; the printed checks of rows 4, 5, 10 (`b_n ≤ N^{-c}`) and `N ≥ 2(2/κ)²` (row 11) hold at sz0 `n=8, 20` and szII `n=0, 200` except `N ≥ 2(2/κ)² = 2.2e7` at szII (fails at n=0 and n=20, first holds at n=46 on `W=n+25`; n=200 shown). The *sufficient* condition `N^{c₀/12} ≥ 3^{1/6}` of row 10 is `ln N ≥ 2ln3/c₀` = 65.9 (sz0, first n=17) and 98.9 (szII, N ≥ 1e43); it only enters the `∀ᶠ n` of the proof, not the hypotheses of the instance, and the actual `b_n ≤ N^{-c}` holds at every printed n. External hypotheses (`twSteps` on `[s,t]`, TL2 at `s`) are owed pins; they are probabilistic and stay hypotheses of the instance (no deterministic limit exists); everything else (frame, `BAFlow`, `STConStInd` by `s1Setup_conStInd_const`/`conStInd_const`, `STCaseI/II`, the pin `BATwistStepFixed` by `baTwistStepFixed_caseI/II`) is discharged at the datum.

### (iii) Target 3 at `sz0`, n=0, t≡1/2, σ=(−,+), c₁=0, c₂=(1,1,0)  (`python3 kc.py`; Ψ = ℓ¹-nearest-neighbour matrix of Z₄³, `M^B=(g₀Ψ−E−m₀)⁻¹`, `Θ=(1−tM^{σσ'})⁻¹`)
```
sz0 n=0: L=4 W=32 W^d=32768 N=2097152 lam=1.5625e-02 Imm=0.832488 t0=0.693740 E=0.0e+00 g0=1.3014e-02 Imm0=0.999493 |m0-trM/L^d|=2.2e-16
t=1/2 eta=0.499746 (<=1) Bctl=6.1959e-05 W^-d/Bctl=0.4925 (<= 1/dd^2+1 = 101); max row l1 of M^B = 1.0828 (C_M proxy, <1.1)
TARGET INSTANCE sigma=(-,+), c1=0, c2=(1,1,0): max_a|Kcirc|/Bctl=1.658e-04   sum_a|Kcirc|*W^d*eta=5.065e-04   (max_a|K|/Bctl=3.321e-04; Kcirc != K, != 0)
max over 4 charge pairs x c2 in {0,(1,0,0),(1,1,0)}: max|Kcirc|/Bctl=0.4910, sum|Kcirc|*W^d*eta=0.4997
Theta Lipschitz/norm check (4 charges x 2 time pairs): max_a sum_a'|Th_t-Th_t'| <= |dt|/((1-t)(1-t')) and ||Th_t||_inf <= 1/(1-t): violations = 0
```
`C` is the existential constant of `twK_bound_holds` plus `(𝔡⁻²+1)C_M²` (no numeric value is claimed; the proxy `C_M ≈ 1.08` and `W^{-d}/Bctl = 0.49 ≤ 101` are consistent with ratios `≤ 0.49`).

### (iv) Privates (none is deleted; no amend)
`BASetup_norm_BAmF_le_one` (`Step1Setup:1048`, `‖m_F‖≤1` for `baGopbound`; public alternative `BAself_norm_le_one`, `ConArg:92`); `BAKBase_sub` (`KBase:216`), `BAKBase_norm_le` (`:151`), `BAKBase_norm` (`:312`) for row 8 (`open private … from RBM3D.BA.KBase`, as `Graph/BASim3.lean:29`; public alternative `BATheta_resolvent`, `BATheta_isUnit`, `BAMss_norm_eq_BAK`, `BAK_row_sum`). Not needed: `TwistPins_zim_pos` (`:656`), `TwistPins_B_le` (`:665`) (T3 uses `twK_bound_holds` as a black box); `BASetup_LP_zeta_ratio` (`:580`) is replaced by row 9. Name clash: `git grep` of the new names and stems on `main`, `t/T2449`, `t/T2450`: no match; `git log --all -- 'RBM3D/BA/TwistLoop*'`: 0 commits.

### (v) Predicted lines (estimate, `python3 lines.py`) and reserve decision
```
file1 (targets 1-2 + instances): 1240  file2 (target 3 + instance): 200  total: 1440
ticket central 850 x landed/central (min,median,max)= [969, 1751, 2329]
component estimate scaled by (min,median,max)/median ratio: file1 [686, 1240, 1649] file2 [111, 200, 266]
```
Ticket central 850 × landed/central (1.14/2.06/2.74, T2441-prove (viii)) gives 969/1751/2329 for one file, over the 1,500 trigger at the median and over the 2,000 stop line at the maximum. Decision: use the reserve. `TwistLoop.lean` = targets 1–2 and their instances (≈ 1,240); `TwistLoop2.lean` = target 3 and its instance (≈ 200; does not use T1–T2; it imports `TwistLoop` only to keep the order `TwistLoop → TwistLoop2`). With the split the maximum-ratio estimate is ≈ 1,650 and ≈ 270.

### Verdict
T1 PASS (net with `N⁻²²` mesh, `#net·#V ≤ N^{28}`, contraction `b_n ≤ N^{-c}`, `J = ⌈5/c⌉`). T2 PASS (T1 at `baTwistStepFixed_caseI/II`; regime unused). T3 PASS (`twK_bound_holds`, `BAMB_row_l1`, `twB0_ge_holds`; no unproved `Prop` premise). Instances PASS (ii)–(iii). No stop rule is triggered. Observation for 1b: row 9 and row 6 use public `cont_inv_add_one_sub_ratio`, `cont_Bctl_eq`, `cont_inv_size_le_Bctl` (all public, `ContinuityNet:676,691,701`); the ticket's `BASetup_LP_zeta_ratio` copy is unnecessary.

## (a′) Preflight corrections — Mon Oct 12 12:40:45 UTC 2026
Facts of the proof differ from section (a) in these places (no verdict changes; no stop rule):
1. Rows 3, 7: `baGopbound` (`Step1Setup:346`) returns an existential `C'`; the `22` is inside its proof. The proof uses `C = 6` and the net exponent `A = C' + 22` (`TwistLoop_arith` needs `A ≥ 22`).
2. Rows 8, 13: `|M(σ)_{xy}| ≤ 1` (`TwistKer2_M_le_one`) is used instead of `C_M`: `‖ΔK̃‖ ≤ |Δu| (1-u)⁻¹(1-u')⁻¹ ≤ N²|Δu|`; target 3 has `C = C_K + 𝔡⁻² + 1` (`Σ_a |M_{ac₁}||M_{c₂a}| ≤ 1` by AM-GM and `BAMB_row_sq_real`); `BAMB_row_l1` is not used.
3. Row 9: the ratio of `Bctl^{3/2}` uses `x ≤ 1/4` (`TwistLoop_zeta_ratio`), not `0.587`.
4. Rows 10-11: the contraction is the public `baEMn2ExpFacts` (`EMn2BA:160`): `∃ c > 0`, `Bctl n u ≤ N^{-c}` for all `u ∈ [0,T₀_n]`, eventually; the proof uses only this existence, no monotonicity of `Bctl`; `b_n = N^{-c/6}`, `J = ⌈30/c⌉`. The witness built in its proof is `c = min(2𝔡𝔠, ε)/2` (EMn2BA:166), which gives the `b`, `J` of (a): 1800 / 2700.
5. (iv): privates opened: `TwistKer_twLoopX_le` (TwistKer:1266), `TwistKer2_norm_sigma`, `TwistKer2_M_le_one` (:1275), `TwistKer2_norm_winv` (TwistKer2), `BAKBase_sub` (KBase:216). Not used: `BASetup_norm_BAmF_le_one`, `BAKBase_norm_le`, `BAKBase_norm`.
6. (v): the reserve is not used: one file, 904 lines (the 1a estimated 1,240 + 200); `TwistLoop2.lean` does not exist.

## (b) Script output — Mon Oct 12 12:40:45 UTC 2026
### Lines against the stop line; builds; axioms
```
$ wc -l RBM3D/BA/TwistLoop.lean   (stop line 2,000 per file; ticket central 850; landed/central = 904/850 = 1.06)
     904 RBM3D/BA/TwistLoop.lean
$ git diff main...t/T2451 --stat
 RBM3D/BA/TwistLoop.lean | 904 ++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 904 insertions(+)
$ git diff main...t/T2451 -- RBM3D/BA/TwistPins.lean RBM3D/BA/TwistStep.lean RBM3D/BA/TwistStep2.lean RBM3D/Test/Axioms.lean | wc -l
0
$ lake build RBM3D.BA.TwistLoop 2>&1 | tail -1
Build completed successfully (4061 jobs).
$ lake env lean ax2.lean   (import RBM3D.BA.TwistLoop; #print axioms of the five public declarations)
'RBM.BA.baTwistLoopStep_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistLoopStep_caseI' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistLoopStep_caseII' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BATwKcircBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwKcircBound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -c 'sorry\|admit\|native_decide\|axiom ' RBM3D/BA/TwistLoop.lean
0
$ lake env lean RBM3D.lean   (unmodified root = main) | grep ...   /   lake build (root + temporary "import RBM3D.BA.TwistLoop", restored afterwards)
[root only]
  RBM.BA.BATwistAvgLaw: 1 [no certificate]
  RBM.BA.BATwistLoopLaw: 0 [no certificate]
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
registry: 2 borrowed + 88 owed + 120 structural + 7 refuted + 17 superseded; 117 registered premise(s) carry nothing yet: [RBM.Loop.KLP
non-vacuity certificates: 0 of 90 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lea
[root + import]
  RBM.BA.BATwistAvgLaw: 1 [no certificate]
  RBM.BA.BATwistLoopLaw: 0 [no certificate]
premises found by scanning: 117 (borrowed 1, owed 52, structural 45, refuted 6, superseded 13).
registry: 2 borrowed + 88 owed + 120 structural + 7 refuted + 17 superseded; 117 registered premise(s) carry nothing yet: [RBM.Loop.KLP
non-vacuity certificates: 0 of 90 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lea
full build exit=0: Build completed successfully (4280 jobs).
```
### Target statements (extracted by script) and their diff against the check file
```
$ awk (print each target declaration from the file up to its ":=")
RBM3D/BA/TwistLoop.lean:696: theorem baTwistLoopStep_of_fixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : BATwistStepFixed d R) :
RBM3D/BA/TwistLoop.lean:697:     BATwistLoopStep d R := by
RBM3D/BA/TwistLoop.lean:705: theorem baTwistLoopStep_caseI (d : ℕ) : BATwistLoopStep d STCaseI :=
RBM3D/BA/TwistLoop.lean:709: theorem baTwistLoopStep_caseII (d : ℕ) : BATwistLoopStep d STCaseII :=
RBM3D/BA/TwistLoop.lean:725: def BATwKcircBound (d : ℕ) : Prop :=
RBM3D/BA/TwistLoop.lean:758: theorem baTwKcircBound_holds (d : ℕ) : BATwKcircBound d := by
$ awk (the target-3 definition, TwistLoop.lean:725-734)
725: def BATwKcircBound (d : ℕ) : Prop :=
726:   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
727:     ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
728:       ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
729:         (∀ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
730:             BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 1) a c₁ * BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 0) c₂ a‖ ≤
731:           C * sz.Bctl n (t n)) ∧
732:         ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
733:             BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 1) a c₁ * BAMsigma d (sz.L n) (twMB (baFMz sz z) n) (σ 0) c₂ a‖ ≤
734:           C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹
$ python3 stmt_diff.py   (check file body vs file body, whitespace-normalised)
target 3: check-file body == file body: True ( 693 chars )
target 1: check-file  : ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R
target 1: file (binders folded): ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R
target 1: equal: True
$ lake env lean check_on_branch.lean  (docs/tickets/checks/T2451-check.lean + import RBM3D.BA.TwistLoop + 4 equality examples)
185:example : T2451_TL2e := baTwistLoopStep_of_fixed
186:example : ∀ d, T2451_TwKcircBound d := baTwKcircBound_holds
187:example (d : ℕ) : T2451_TwKcircBound d = BATwKcircBound d := rfl
188:example : T2451_TL2e = (∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R) := rfl
exit=0
```
### Compiled nonempty instances (TwistLoop.lean; `twSteps` and TL2 at `s` stay hypotheses, every other hypothesis is discharged)
```
$ awk (instances: example headers and the application lines)
TwistLoop.lean:712: example : ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop), BATwistStepFixed d R → BATwistLoopStep d R :=
TwistLoop.lean:713:   baTwistLoopStep_of_fixed
TwistLoop.lean:715: example : ∀ d, BATwistLoopStep d STCaseI ∧ BATwistLoopStep d STCaseII := fun d => ⟨baTwistLoopStep_caseI d, baTwistLoopStep_caseII d⟩
TwistLoop.lean:718: example : BATwistLoopStep 3 STCaseI := baTwistLoopStep_of_fixed 3 STCaseI (baTwistStepFixed_caseI 3)
TwistLoop.lean:825: example : ∀ d, BATwKcircBound d := baTwKcircBound_holds
TwistLoop.lean:841: example {Cd : ℝ} (hC : 0 < Cd)
TwistLoop.lean:842:     (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd)
TwistLoop.lean:843:     (hL : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
TwistLoop.lean:844:     (τ : ℕ → ℝ) (h1 : ∀ n, 1 / 2 ≤ τ n) (h2 : ∀ n, τ n ≤ 2 / 3) :
TwistLoop.lean:864:   obtain ⟨c, hc, -, H⟩ := baTwistLoopStep_caseI 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hC
TwistLoop.lean:865:   exact H (1 / 6) sz0 zSeq flow_sz0 _ _ (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) hcase
TwistLoop.lean:866:     (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) hc) hS hL τ h1 h2
TwistLoop.lean:869: example {Cd : ℝ} (hC : 0 < Cd)
TwistLoop.lean:870:     (hS : twSteps (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) Cd)
TwistLoop.lean:884:   obtain ⟨c, hc, -, H⟩ := baTwistLoopStep_caseII 3 le_rfl (3 / 5000) (1 / 2) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hC
TwistLoop.lean:885:   exact H (1 / 9) TwistStep2_szII TwistStep2_zII hflow _ _ (fun _ => le_rfl) (fun _ => by norm_num) ht0 hcase
TwistLoop.lean:886:     (RBM.Gauss.Step34Inst.conStInd_const TwistStep2_szII hWt (by norm_num) (by norm_num) hc) hS hL τ h1 h2
TwistLoop.lean:889: example : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
TwistLoop.lean:896:   obtain ⟨C, hC, H⟩ := baTwKcircBound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
TwistLoop.lean:897:   exact ⟨C, hC, (H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)).mono
TwistLoop.lean:898:     fun n hn => hn ![false, true] 0 ![1, 1, 0]⟩
```
Data: `STCaseI`: `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/2`, `t ≡ 2/3` (`t0_sz0`), `STConStInd` by `s1Setup_conStInd_const`; `STCaseII`: `TwistStep2_szII`, `TwistStep2_zII`, `TwistStep2_flowII`, `s ≡ 0`, `t ≡ 1/2000`, `conStInd_const`; target 3: `sz0`, `t ≡ 1/2`, `σ = (false,true)`, `c₁ = 0`, `c₂ = (1,1,0)`. `baTwistLoopStep_caseI/II` (:705-710) are `baTwistLoopStep_of_fixed` at `baTwistStepFixed_caseI/II`; :718 applies target 1 directly.
### Name clash, ports
```
$ for n in <new public names and stems>; git grep -n $n main t/T2449 t/T2450 -- RBM3D
baTwistLoopStep_of_fixed: main 0, t/T2449 0, t/T2450 0
baTwistLoopStep_caseI: main 0, t/T2449 0, t/T2450 0
baTwistLoopStep_caseII: main 0, t/T2449 0, t/T2450 0
BATwKcircBound: main 0, t/T2449 0, t/T2450 0
baTwKcircBound_holds: main 0, t/T2449 0, t/T2450 0
TwistLoop_: main 0, t/T2449 0, t/T2450 0
TwistLoop2_: main 0, t/T2449 0, t/T2450 0
$ git log --all --oneline -- 'RBM3D/BA/TwistLoop*' | wc -l  (before this ticket's 3 commits: 0)
3
```
Ports: none (no text copied from RBM1D/RBM2D; nothing there read). `grep -c 'Step2Gen_\|STthetaOpg' RBM3D/BA/TwistLoop.lean` = 0.
### Bootstrap table (as written)
| item | statement | source | datum `sz0` / `szII` |
|---|---|---|---|
| `𝔠d` | `h`'s at the same `(κ, ε, 𝔡, Cd)`; every frame premise passes unchanged | `hfix` in :696 | – |
| `Ξ₀` | `2 (2/κ)² N⁴ ≥ 1` (`κ ≤ Im m ≤ 1`) | `TwistStep_zcrude` (TwistStep:769), `ST_prec_of_le_ev`, `TwistLoop_unif_zero` (:558) | `κ = 1/2` / `3/5000` |
| round | `Ξ_{j+1} = 1 + b Ξ_j`, `b = N^{-c/6}`: `h` at `Ξ_j` per `τ`, sections (`perTimeDomAt_iff_forall_section`), net | `TwistLoop_round` (:569), `TwistLoop_net` (:408) | – |
| `c` | `∃ c > 0`: `Bctl n u ≤ N^{-c}`, `u ∈ [0,T₀_n]`, eventually; its proof's witness is `min(2𝔡𝔠, ε)/2` | `baEMn2ExpFacts` (EMn2BA:160, :166) | `1/60` / `1/90` |
| `J` | `⌈30/c⌉`, so `J c/6 ≥ 5` | `TwistLoop_core` (:617) | `1800` / `2700` |
| `Ξ_J` | `≤ J + b^J Ξ₀ ≤ J + 2(2/κ)²/N ≤ J + 1` once `N ≥ 2(2/κ)²` | `TwistLoop_Xi_le` (:544) | `N₀ = 2097152 ≥ 32` / first `n = 46` |
| last | round `J+1` at `τ`: `Bctl^{3/2}(1 + Bctl^{1/6} Ξ_J) ≤ (J+2) Bctl^{3/2}`; `J + 2` absorbed by `N^{τ/2}` | `TwistLoop_prec_of_le_const` (:66) | – |
| net | `C = 6`, `A = C'+22`, `#V = 4(L^d)³ ≤ N⁴` (`N ≥ 4`), `ε_n = N^{-3/2} ≤ Bctl^{3/2}`; eventually `N^ε ≥ 2`, `N ≥ 8/κ`; `η⁻¹ ≤ N/κ`, `‖ΔL̃‖ ≤ 2(N/κ)N^{-6}`, `‖ΔK̃‖ ≤ N²·|Δu|`, `x ≤ 1/4` | `TwistLoop_Z_close` (:320), `TwistLoop_arith` (:270) | – |
```
$ python3 boot.py   (exact arithmetic of c, J and the thresholds at the two data)
sz0   : (kappa,eps,cc,dd)=(1/2,1/10,1/6,1/10); c=min(2*dd*cc,eps)/2=1/60 (0.01667); b=N^-(1/360) ; J=ceil(30/c)=1800; J*c/6=5
   Xi0=2(2/kappa)^2 N^4 ; need N >= max(4, 8/kappa, 2(2/kappa)^2) = 32 and N^eps>=2 ; first n = 0, N_n = 2.097e+06
szII  : (kappa,eps,cc,dd)=(3/5000,1/2,1/9,1/10); c=min(2*dd*cc,eps)/2=1/90 (0.01111); b=N^-(1/540) ; J=ceil(30/c)=2700; J*c/6=5
   Xi0=2(2/kappa)^2 N^4 ; need N >= max(4, 8/kappa, 2(2/kappa)^2) = 2.222e+07 and N^eps>=2 ; first n = 46, N_n = 2.291e+07
sz0 n=0: N = 2097152 ; Xi_J <= J + b^J Xi0 <= J + N^-5 * 2(2/kappa)^2 N^4 = 1800.000015258789 <= J+1 = 1801
```
### Narrative
- Layout of `TwistLoop.lean`: `TwistLoop_prec_of_le_const` (:66); carrier facts `TwistLoop_win` (:87), `TwistLoop_G_entry` (:112), `TwistLoop_L2_diff` (:177), `TwistLoop_K_diff` (:208), `TwistLoop_arith` (:270), `TwistLoop_Z_close` (:320); the net `TwistLoop_net` (:408); the rounds (:569, :602, :617); targets 1-2 (:696-710); target 3 (:725, :758); instances (:836-900).
- S2 is `TwistLoop_net`: `cont_core` (ContinuityNet:142) on `TimeIcc s t n × V n`, `V n = (Fin 2 → Bool) × Zd³`; good event = complement of the `baGopbound` event at `C = 6` (`HighProbAt` by `compl_compl`); `hlow` from `cont_inv_size_le_Bctl`; `hclose` from `TwistLoop_Z_close` + `TwistLoop_arith` and `cont_Bctl_ratio` + `TwistLoop_zeta_ratio`.
- `L̃` part: `twLoopX` is bilinear (`TwistLoop_loopX_sub`), each average is bounded by `TwistKer_twLoopX_le`; entries of `G` by `TwistKer_entry_le`, `η⁻¹ ≤ N/κ` from `1 - T₀ ≥ N⁻¹` (`EMn2BA_one_sub_T0`, `N^ε ≥ 2`). `K̃` part: `Θ_u - Θ_{u'} = (u-u') Θ_u Q Θ_{u'}` (`BAKBase_sub`), `‖Θ‖ ≤ (1-u)⁻¹` (`EKPins_norm_Theta_le`), `‖Q‖ ≤ 1` (`EKPins_norm_Q_le`).
- Each round turns `BATwistStepFixed`'s per-`τ` bound into the section form (`StochDomAt.precomp_param` on `Unit`), then `TwistLoop_net` gives the uniform bound at the next level. No `∀ᶠ n` is carried from round to round: `Ξ_j n` is an explicit function of `n`, each round's conclusion is a `StochDomAt` statement, and the eventual facts (`hb` from `baEMn2ExpFacts`; the threshold `N ≥ 2(2/κ)²` of `hXJ`) are used once.
- Target 3: `‖K̃^∘‖ ≤ ‖K̃‖ + W^{-d}` and `Σ_a ‖K̃^∘‖ ≤ Σ_a ‖K̃‖ + W^{-d}`, `W^{-d} ≤ (𝔡⁻²+1) Bctl` (`twB0_ge_holds`), `W^{-d} ≤ (W^d η)⁻¹` (`η ≤ 1`), `C = C_K + 𝔡⁻² + 1` with `C_K` of `twK_bound_holds`.
- No stop rule fired: no merged file edited, no `private` deleted, `Test/Axioms.lean` unchanged, no public theorem takes `twSteps` (the premise `TwistLoop_Step` is a private def used by private lemmas only), no new `Prop` premise. The root import line is not on the branch (hub step, CLAUDE.md §3 (A)); the full `lake build` above ran with `import RBM3D.BA.TwistLoop` added temporarily to `RBM3D.lean` and restored (`git status` clean).

## (c) Verified Mathlib names (script `names.lean`: 52 `#check @name`, 50 resolve)
`Real.rpow_nonneg`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_two`, `Real.inv_rpow`, `Real.mul_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.norm_eq_abs`;
`inv_anti₀`, `inv_pow`, `one_le_inv₀`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `pow_le_pow_of_le_one`, `le_mul_of_one_le_left`, `le_mul_of_one_le_right`, `mul_inv_cancel₀`, `inv_le_one_of_one_le₀`, `div_le_one`, `div_le_iff₀`, `le_div_iff₀`, `abs_lt`, `abs_sub_comm`, `compl_compl`, `map_sub`;
`norm_sub_le`, `norm_add_le`, `norm_smul`, `norm_mul_le`, `norm_sum_le`, `Complex.norm_conj`, `Complex.norm_real`, `Nat.le_ceil`, `ZMod.card`;
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, `Finset.sum_congr`, `Finset.sum_div`, `Finset.mul_sum`, `Finset.sum_le_sum`, `Fintype.card_prod`, `Fintype.card_fun`, `Fintype.card_bool`, `Fintype.card_fin`.
Verified absent (`Unknown constant`): `Set.compl_compl` (use `compl_compl`), `Real.rpow_four_natCast` (use `by norm_cast` for `N ^ (4:ℝ) = N ^ 4`).

## (d) Open issues, paper-delta candidates, stage-TL closing block (a)-(h)
- Open (other gates' pins, hypotheses of the instances and of `BATwistLoopStep`): `twSteps` on `[s,t]` (owners U3s1, T7-BA; TLF-C5) and `BATwistLoopLaw` at `s` (BA-V: V2a/V2b, base case `STG0M`/`GLoopAtT0`). Not here: footnote 6 (BA-V item (v)), a public uniform-in-`u` TL2 (the last round stays inside `TwistLoop_core`), T.13 (i) and (iii), T.12's `2 - δ` form.
- Paper-delta candidates: none new (`T2451a`: none). Proof-level remark: the paper closes `Ξ̃ ≺ 1` (TP:171); Lean ends at the constant `J + 2`, `J = ⌈30/c⌉` depending on `(𝔠, 𝔡, ε)`, absorbed in `≺`; the statement of `BATwistLoopLaw` (exponent 3/2) is unchanged. `T2441a` (a deterministic level `Ξ_n` in place of the random `Ξ̃_u`) is the device iterated here; no new difference.
- (a) targets: 1 `baTwistLoopStep_of_fixed` :696, 2 `baTwistLoopStep_caseI` :705 / `_caseII` :709, 3 `BATwKcircBound` :725 / `baTwKcircBound_holds` :758; axioms, instance lines :712-718, :825, :841, :869, :889, the statement diff and the empty `git diff` of TwistPins/TwistStep/TwistStep2 are in (b).
- (b) bootstrap: table in (b): `𝔠d` = `h`'s, `c` from `baEMn2ExpFacts` (witness `min(2𝔡𝔠, ε)/2`), `J = ⌈30/c⌉` (1800 at `sz0`, 2700 at `szII` for that witness).
```
$ grep -n "^theorem baTwistAvgProd_holds\|^theorem baTwistLoopStep_\|^theorem baTwistLoopBase_holds\|^theorem baChainTL_holds" RBM3D/BA/{TwistAvgB,TwistLoop,TwistChain}.lean
RBM3D/BA/TwistChain.lean:110:theorem baTwistLoopBase_holds (d : ℕ) : BATwistLoopBase d := by
RBM3D/BA/TwistChain.lean:240:theorem baChainTL_holds (d : ℕ) : BAChainTL d := by
RBM3D/BA/TwistAvgB.lean:451:theorem baTwistAvgProd_holds (d : ℕ) : BATwistAvgProd d :=
RBM3D/BA/TwistLoop.lean:696:theorem baTwistLoopStep_of_fixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
RBM3D/BA/TwistLoop.lean:705:theorem baTwistLoopStep_caseI (d : ℕ) : BATwistLoopStep d STCaseI :=
RBM3D/BA/TwistLoop.lean:709:theorem baTwistLoopStep_caseII (d : ℕ) : BATwistLoopStep d STCaseII :=
```
- (c) producers: `BATwistAvgProd` :451 (TwistAvgB), `BATwistLoopStep` :696/:705/:709 (this row), `BATwistLoopBase` :110 and `BAChainTL` :240 (TwistChain) are proved theorems with instances (TwistAvgB:465-486, TwistChain:275-292; here :712-718).
- (d) S2 = `TwistLoop_net` (:408), used by `TwistLoop_round` (:569) → `TwistLoop_core` (:617) → `baTwistLoopStep_of_fixed` (:696); S3 = `baTwKcircBound_holds` (:758) with `TwistLoop_sum_M` (:741).
- (e) registry lines in (b): `BATwistAvgLaw: 1`, `BATwistLoopLaw: 0` (usage counts), `registry: 2 borrowed + 88 owed + 120 structural + 7 refuted + 17 superseded` and `premises found by scanning: 117` identical without and with the new import; both pins stay owed (owner texts at `Test/Axioms.lean:196-197` unchanged).
- (f) open hypotheses of targets 1-2: `twSteps` and `BATwistLoopLaw` at `s`, as above; `R sz s t` and `STConStInd` are frame premises (discharged in the instances); no other.
- (g) lines: `TwistLoop.lean` 904 (stop line 2,000); landed/central = 904/850 = 1.06 (the ticket quotes 1.14-2.74 for the earlier TL rows).
- (h) paper deltas: none new. Hub: add `import RBM3D.BA.TwistLoop` after the last `import` line of `RBM3D.lean` at merge.
