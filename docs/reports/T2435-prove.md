Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 05:14:40 UTC 2026

Notation: `N=(WL)^d`, `[x]` block of `x`, `|·|=zdistInf`, `C=baFMz sz z`, `μ=seqP(sz.withLam 0)`, `GM=G−M`, `η=C.eta n (t n)=(1−t)Im m` (`etaOf`, `Loop/GLoopFlow.lean:58`), `Λ=𝔡⁻¹`, `c=BAct_rate d Λ κ`, `γ=c_λ=GreenStab_clam d Λ κ=min(c/12,BAp5s_rate/6)` (`BA/GreenStab.lean:221`), `B:n`=`paper/tex/B_graphical_lemmas.tex:n`. Scratch: `<scratchpad>/T2435/{consts,ii_check,inst}.py` (no Lean anywhere).

### (i) Exponent table, and the design argument

| # | item | value | constraint | slack |
|---|---|---|---|---|
| E1 | `κ`, `Im z`, `c` at `g=1/64, 1, 10` (`κ` uniform in `L`: `L=64`, `z+m=w=1.2i,1.2i,1.0i`; T2390 table `docs/reports/T2390-prove.md:17-22`, reproduced) | `Im m=0.8325/0.3435/0.0442`, `Im z=0.3675/0.8565/0.9558`, `κ=0.5/0.25/0.04`, `c=4.158e-3/2.081e-3/3.333e-4` | `κ ≤ Im m`, `Im z ≤ 1` (`BAdom`, `MFixedPoint.lean:435`) | `Im m/κ=1.67×/1.37×/1.11×`; `1−Im z=0.63/0.14/0.044` |
| E2 | `γ=c_λ` (`BAct_C=16d²/κ³`, `A=4(C/c)²`, `S=expC(d−2,c)`, `μ_{5s}=BAp5s_rate`) | `2.145e-33 / 1.648e-38 / 4.894e-52` (`μ_{5s}=1.29e-32/9.9e-38/2.9e-51`) | `>0`, depends on `(d,κ,𝔡)` only, fixed before `(𝔠,sz,z,t)`; no `M=mI`, no smallness of `g` (L5 / C1) | enters only the eventual thresholds E5 |
| E3 | Ω exponent `ε₀:=min(ε₁/2,d/2)`, `τ₀≤𝔠ε₀`, `δ=W^{-ε₀}` | `1/40`, `≤1/240` (`ε₁=1/20`, `𝔠=1/6`) | `Ω={‖GM‖≤δ}` whp from the entry bound (`τ≤𝔠ε₁/2`); `W^{-d}≤δ²` (`2ε₀≤d`); `δ≤κ/2` eventual | `2ε₀=0.05` vs `d=3` (2.95); `τ`: equality |
| E4 | floor exponent `D₁` of `ζ²` (the paper's `+W^{-D}`, `B:426`) | `12` (`d=3,C₂=2,𝔠=1/6`) | `D₁ ≥ d+2C₂/(𝔠d)+1`: floor `≤N^τΦ(|a−b|)²` for all `|a−b|≤L` (`Φ(r)²≥W^{-d}L^{-2C₂}/(C₃Cc(2)C₁)²`, `L≤N^{1/d}≤W^{1/(𝔠d)}`); Ward floor `NW^{-D₁}≤1` needs `D₁≥1/𝔠=6` | `1` / `6`; a parameter (L3c3b needs `D₁≥D+d`) |
| E5 | separation `ρ−2R≥K log W` (`∀K`, eventually; hypothesis of target 4), `R≥|E⊕I|r` | `K_tail=2(1/𝔠+D₁+1)/γ=1.8e34/2.3e39/7.8e52` | tail `L_max e^{-γ(ρ−2R)/2}S'²≤W^{-D₁}`, `L_max≤2(W^dη)⁻¹≤N`, `log N≤log W/𝔠`; `ρ+1≤N^τ ∀τ` (`lwXiRad_holds`) | eventual (conclusion only): with `ρ−2R=(log W)^{3/2}`, `log₁₀log W ≥ 68.5/78.7/105.8`; not a hypothesis of any target |
| E6 | Ward constant (block form) | `Σ_bζ² ≤ 4(2ρ+1)^{2d}(W^dη)⁻¹+(2ρ+1)^dW^{-d}+L^dW^{-D₁}` (`‖G_yy‖≤|m|+A≤2`) | `≲N^τ(W^dη)⁻¹`; `η≤1` from `|m|≤1` (`BAm_norm_le_one`, `BA/Ward.lean:136`) | polylog `ρ` ⇒ `N^{o(1)}`; floor part `NW^{-D₁}=1.8e-12` (n=0) |
| E7 | (ii) class `(eq:Psi)`, `Ψ:=W^{-d/2}≤C₃Φ(0)` | `K₂=C₃Cc(2)C₁(C₂/γ)^{C₂}`: `log₁₀=66.2/76.5/103.5` (`C₁=C₂=2`, `Cc(2)=C₃=1`); `K₁=Cc(2)C₁(Σ_u(2C₂/γ)^{C₂}e^{-γ|u|/2})²` finite | `n`-independent | script `ii_check.py` ratios identical for `W=1e2,1e6` |
| E8 | (ii) class `𝖳` (`(defTUL)` `3_5:313`, `Φ_T²=W^{-d}T̃`) | `K_{T2}=(Λ²+1)^{1/2}e^{1/(8γ)}((d−2)/γ)^{(d−2)/2}`, `1/(8γ)=5.8e31` at `g=1/64`; `K_{T1}` finite | `Φ_T≤W^{-ε₀}`: `Φ_T(0)²≤W^{-2𝔡}+(2/κ)N^{-ε}`, so `ε₀<min(𝔡,ε/2)=1/20` | `ε₀=1/40`: slack `1/40`; `n`-independent |
| E9 | sup constants | `sup_r(r+1)^{C₂}e^{-γr}≤(C₂/γ)^{C₂}`; `sup_s e^{-γs+√s/2}≤e^{1/(16γ)}` | `γ≤C₂`; `ℓ_t≥1` (`(eq:ellt)`) | checked (`ii_check.py`): `1.367=1.367` at `γ=0.2`, `518=518` at `0.01` |
| E10 | block Ward of the pin-form `ζ=Φ(|a−b|)` | `(Σ_bΦ0²)(W^dη) ≥ 2.6e4/9.1e17/2.2e34 = N^{0.70/0.72/0.72}` (n=0/10/199, `η≥0.4` from `Im m≥4/5`) | needs `≤N^τ ∀τ>0` | **fails** by `N^{0.7}`: the pin's RHS cannot be the block `ζ` |

**Argument (i), the joint check: PASS with the loop-form `ζ` and no unprimed pin; the sup/pin-form `ζ` fails (E10).**
1. *Sup form* `ζ_S(a,b)=max_{R-balls}‖GM_xy‖` (T2420d: "the sum `ζ` of `B:424` is the sup-form"): (a) is trivial and `ζ_S≺Φ(|a−b|)` follows from `BAGbEXPij'` with `Φ:=Ψ_t(|a−b|)` and (ii). But `(eq:Gbyxi2_BA)`'s Ward bound is fine-lattice (`Σ_{y}|G_xy|²≲η⁻¹`); a sup over a block of `W^d` points becomes `Σ_bζ_S²≲(W^dη)⁻¹` only if entries in a block are comparable, i.e. the random-window `(GijGEX)` (`3_5:21`). A deterministic right side cannot carry it (E10), and `Σ_bΨ²≲(W^dη)⁻¹` is not in `LWPsiAll`.
2. *Loop form* (band `(eq:xia1a2)`, `7_8:882`) on `C`: `ζ²=Σ_{|b₁−a₁|,|b₂−a₂|≤ρ}Σ_{σ∈{(t,f),(f,t)}}‖L_σ(b₁,b₂)‖+W^{-d}1(|a₁−a₂|≤ρ)+W^{-D₁}`. (b): symmetric (trace cyclicity of `loopFine`), `ζ≺Φ(|a−b|)` from `LWLoop2gL` and `(eq:Psi)` (twin of `AuxGraph2:965-1100`), Ward block form by the model-generic private Ward lemmas (`AuxGraph2:264-505`, any Hermitian `H`, `Im z>0`; `H=seqHflowBA`, `z=ztOf`; `‖G_yy‖≤|m|+A`, `M_yy=m` by `BAMB_diag_eq`) — E6. Block form of `(eq:Gbyxi2_BA)`'s Ward sum: **paper-delta T2435d** (the paper's `Σ_α…≺η⁻¹` is fine-lattice; `W^d×` the block sum).
3. (a) for the loop form comes from the **public sample-wise core** `GreenOff_carrier_decay` (`BA/GreenOff.lean:916`, all `x,y` incl. `x=y`): on `Ω`∩LDE events, for **any** `φ≥0` with `‖L_{(f,t)}(a,b)‖≤φ(a,b)²`: `‖GM_xy‖≤2C_ℓP·T_γ(φ,Ψ)([x],[y])`, `T_γ(a,c)=Σφ(a',b')e^{-γ(|a'−a|+|b'−c|)}+Ψe^{-γ|a−c|}`. Take `φ:=‖L_{(f,t)}‖^{1/2}` (sample-dependent: no loop premise), `Ψ:=W^{-d/2}` (`hΨw` equality). Cauchy–Schwarz `(Σφw)²≤(Σw)(Σφ²w)`, `Σw≤S²`; outside the radius `ρ'=ρ−2R` the loop sum is `≤L_max e^{-γρ'/2}S'²≤W^{-D₁}` (E5); `Ψ²e^{-2γ|a−c|}≤W^{-d}1(|a−c|≤ρ')+W^{-D₁}`. So `‖GM_xy‖²≤K N^{2τ₀}ζ(a,b)²` for `[x],[y]` within `R` of `a,b`. Events: `baLDEin_holds`, `GreenOff_pin_consts` (`:1198`), `GreenOff_ev_small/big` (`:1235,1252`), `Ω` from the entry hypothesis: the proof of `baGbEXPij'_holds` (`:1290-1370`) with `Φ` random; its private `GreenOff_whp`, `GreenOff_card_*` are copied. **This is new Lean (est. 350 lines, file B), not a twin; no new hypothesis.** `BAGbEXPij` (G7) is not used, not even as a hypothesis (iii): it is slated for supersession (2254 Q2), and the paper's `(GijGEX_BA)` has deterministic `Φ` (`7_8:1942`), not random windows; `BAGbEXPij'`'s loop premise is not needed.

**Argument (ii) (2149 L6 (i)–(iv), 2254 G3): TRUE for both terms and both classes; not on the path of the chosen `ζ`.** (i) `0<Φ≤W^{-ε₀}` from `LWClass`; `GreenCore_loopPrem` from `LWLoop2gL` at `p.1=false` (`indMax∈{0,1}`, `GreenOff.lean:1333,1366`). Term 1 (class `(eq:Psi)`): `s=|a'−a|+|b'−b|`, `r=|a−b|`: antitone + `(eq:Psi)` at `ℓ₁=r−s,ℓ₂=r` (`r/(r−s)≤s+1`) and `Φ(0)≤Cc(2)Φ(1)` give `Φ(|a'−b'|)≤Cc(2)C₁(s+1)^{C₂}Φ(r)`; the far part `|a'−a|>(log W)^{3/2}` is `≤W^{-ε₀}S²e^{-γ(log W)^{3/2}/2}≤W^{-D}` eventually (E5 type). Term 2: `Ψe^{-γr}≤C₃Cc(2)C₁r^{C₂}e^{-γr}Φ(r)` (E9). Class `𝖳`: `B_{t,m₁}≤((m₂+1)/(m₁+1))^{d−2}B_{t,m₂}`, `√m₂−√m₁≤√s`, truncation monotone, `max(Kx,F)≤K max(x,F)`: Term 1 `≤K_{T1}Φ_T(r)`; Term 2 from `T(m)^{1/2}≥A^{1/2}(m+1)^{-(d−2)/2}e^{-√(m/ℓ_t)/2}`, `A=(g²+|1−t|)⁻¹≥(Λ²+1)⁻¹` (E8). Constants depend on `(γ,d,C₁,C₂,Cc(2),C₃,Λ)` only; `c_λ≈1e-33` makes them `exp(6e31)`-size, finite.
(iii) unprimed pin: not used. (iv) C1: E1–E2, no `M=mI`, no smallness; `BAMB_row_l1`/`BAMfine_decay` are not needed on this path (only `|m|≤1`); they stay inside G3.
(v) Consumers (grep): L3c3b `LWXiExp`: `lwXiSq`, `lwXiVar(_nonneg,_symm)`, `lwXi_ward_sum`, `lwXiClaim_holds`; L3d2 `LWMoment`: `lwXiClaim_holds`, `lwGbyXi_holds/_hxi`, `lwEntryPsi_holds`, `lwXiRad_holds`, `LWMomentExp`: `lwGbyXi(_hxi)`, `lwXiVar(_nonneg,_symm)`, `lwXiRad_holds`; L4c `LWExpTerm3`: `lwGbyXi_holds`, `lwXi_ward_sum`, `lwXiRad_holds`, `lwXiSq/Var`; L5 `LWTermHolds`: `lwGbyXi_holds`, `lwXiClaim_holds`, `lwXiSq/Var`; L3d1: G4. All read the loop-window shape, which the sup form would break. Generic over the carrier: only `LWXigL` (target 2); `ζ` and its proofs are twinned on `baFMz` (`loopFine`, Hermitian `H`).

**(vi) Statements for the probe (pseudo-Lean; names proposals; namespace `RBM.Graph`).**
```
baZetaSq sz z t ρ D₁ n a₁ a₂ ω := Σ_{b₁∈B(a₁,ρ n)} Σ_{b₂∈B(a₂,ρ n)} Σ_{σ∈{![true,false],![false,true]}} ‖(baFMz sz z).L n (t n) σ ![b₁,b₂] ω‖
    + (W^d)⁻¹·1(|a₁−a₂|≤ρ n) + W^{-D₁n};  baZetaVar := √baZetaSq          -- D₁ : ℕ → ℝ or ℝ
def LWXigL (C : FlowFM sz) (μ) (t) (Φ) (ξ) : Prop := (check file `T2435_LWXigL`);  bridge `LWXigL (bandFM sz E) (seqP sz) t Φ ξ ↔ LWXi sz E t Φ ξ` is `Iff.rfl`
   (`Prec=PrecL (seqP sz)`, `bandFM.eta=etaT`, by unfolding; the compile is the probe's)
baZetaVar_nonneg, baZetaVar_symm, baZeta_ward_sum   (twins `AuxGraph2:135,160,507`; `BAm_norm_le_one` for `|G_yy|`)
def BAZetaClaim d : Prop := 3≤d → ∀κ ε 𝔡>0, ∀𝔠 sz z, BAFlow sz κ ε 𝔠 𝔡 z → ∀t, (0≤t n) → (t n≤BAflowT0 sz z n) → ∀ε₀ C₁ C₂ C₃ Cc Φ,
   LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ → LWLoop2gL C μ t Φ → ∀ε₁>0, PrecL (U:=pairs) ‖C.GM‖ (W^{-ε₁}) → ∀ρ, (0≤ρ n) → (∀τ>0, ∀ᶠn, ρ n+1≤N^τ) →
   ∀D₁, d+2C₂/(𝔠d)+1 ≤ D₁ → LWXigL C μ t Φ (baZetaVar sz z t ρ D₁)            -- baZetaClaim_holds
def BAGbyZeta d : Prop := (same flow/entry hypotheses, no LWPsiAll/LWLoop2gL) → ∀ρ R D₁, (0≤R n) → (∀K, ∀ᶠn, K·log W ≤ ρ n−2R n) →
   PrecL (U:={(x,y,a,b) | zdistD([x],a)≤R n ∧ zdistD([y],b)≤R n}) ‖GM_xy‖ (baZetaVar … a b)     -- all x,y (x=y included); baGbyZeta_holds
baGbyZeta_hxi: ‖GM_xy‖≤c·ζ(a,b) on the R-balls ⇒ `(∀a b, 0≤c·ζ a b)` ∧ the hξ premise of `baGtoAG_holds`/`baGtoAG_E` (BAAtom2:403-406,606) verbatim (D.G=C.G, D.M=C.M)
def BAEntryPsi d : Prop := (flow, LWPsiAll, LWLoop2gL, entry hyp.) → PrecL ‖C.GM_xy‖ (Φ n 0) all pairs     -- via baGbEXPii_holds (GreenLocal:474) + LWLoop2gL, twin of :1177-1230
def BAAnpAuxG d : Prop := BAAnpAux (BAAtom2:677) with BAFlow, BAflowT0, baFMz, PrecL μ, LWXigL, η=C.eta; docstring owner "L3d1"   -- pin only
```
`BAAnpAuxG` stays pinned: `lwAnp_holds` is stated for `Prec sz`/`STFlow`/`etaT`; `AnpKey*.lean` have no `seqP` (grep: 0), so the argument is law-generic, but a statement at `μ`, `C.eta` needs the chain re-proved (L3d1, 500–1,200 lines): not "no new mathematics". Section map: `AuxGraph2` §1–§3 (`:61-945`) → `BAAuxGraph2` (ζ, `LWXigL`, facts, Ward, helpers, comparisons); §4 (`:946-1100`) + §5 (`:1101-1232`, `lwGbyXi_holds` replaced by the sample-wise route above) + §7 (`:1297-1500`) → `BAAuxGraph2B`; §6 `LWXiRad` imported. Predicted lines (stop line 2,000 each): A ≈ 950, B ≈ 950–1,150 (the 350-line route is the only non-twin part). Paper-delta candidates: `T2435a` ζ is the block loop-window variable, not the atom-centre entry sum `(Gyiyjatom)` (`B:424`); `T2435b` floor `W^{-D₁}` in `ζ²`; `T2435c` (a) from the sample-wise core instead of `(GijGEX_BA)` (`7_8:1942`); `T2435d` block Ward form.

### (ii) One concrete nondegenerate instance

`d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`, `n=0`: `L=4,W=32,N=2097152`), `flow_sz0` (`FlowPins.lean:1214`: `κ=1/2, ε=𝔡=1/10, 𝔠=1/6`, `Im m≥4/5`, `T₀≥2/3`), `t≡1/2`, `Φ0≡W^{-1/2}` (`LWPsiAll`: `ε₀=1/10, C₁=C₂=2, C₃=1, Cc≡1`), `ε₁=1/20`, `D₁=12`; window `ρ=2R+(log W)^{3/2}`, `R=(log W)^{1+ε₁}` (proper subset of the torus from `n=99` on, script). External hypotheses (other gates' pins): `LWLoop2gL` at `Φ0` and `‖GM‖≺W^{-ε₁}`. Their concrete check: Ward ceiling `2/(W^dη)` (`η≥0.4`) against `Φ0²=W^{-1}` has ratio `W²η/2→∞` (205 / 5.3e12 / 2.1e25), so `LWLoop2gL` holds with that slack once `‖G_yy‖≤2`; the entry bound asks `W^{-1/20}` against the window floor `W^{-3/2}`: factor `W^{1.45}` (152 / 5.4e9 / 7.3e18).
```
$ cd <scratchpad>/T2435; python3 consts.py; python3 inst.py; python3 ii_check.py
g=0.015625 Im m=0.8325 Im z=0.3675 kappa<=Im m:True Im z<=1:True c=4.1580e-03 C=1.152e+03 A=3.070e+11 S=2.055e+13 p5s=1.287e-32 c_lam=2.145e-33
g=1 Im m=0.3435 Im z=0.8565 kappa<=Im m:True Im z<=1:True c=2.0812e-03 C=9.216e+03 A=7.844e+13 S=3.275e+14 p5s=9.889e-38 c_lam=1.648e-38
g=10 Im m=0.0442 Im z=0.9558 kappa<=Im m:True Im z<=1:True c=3.3328e-04 C=2.250e+06 A=1.823e+20 S=4.980e+17 p5s=2.937e-51 c_lam=4.894e-52
D1 = d + 2*C2/(c*d) + 1 = 12;  Ward floor needs D1 >= 1/c = 6;  eps0 = eps1/2 = 0.025;  tau0 <= c*eps0 = 0.00417;  class T needs eps0 < min(dd, eps/2) = 0.05
n=0: L=4 W=32 N=2.097e+06 lam=0.0156 | hypotheses True | Phi0=0.177 W^-3/2=0.00552 W^-1/10=0.707 | Ward ceiling 2/(W^d eta)=0.000153 <= Phi0^2=0.0313 (ratio 205) | W^-eps1/W^-d/2=152 | N*W^-D1=1.8e-12
n=10: L=44 W=5.154e+06 N=1.166e+25 lam=8.82e-09 | hypotheses True | Phi0=0.00044 W^-3/2=8.55e-11 W^-1/10=0.213 | Ward ceiling 2/(W^d eta)=3.65e-20 <= Phi0^2=1.94e-07 (ratio 5.31e+12) | W^-eps1/W^-d/2=5.4e+09 | N*W^-D1=3.3e-56
n=199: L=800 W=1.024e+13 N=5.498e+47 lam=2.44e-16 | hypotheses True | Phi0=3.13e-07 W^-3/2=3.05e-20 W^-1/10=0.05 | Ward ceiling 2/(W^d eta)=4.66e-39 <= Phi0^2=9.77e-14 (ratio 2.1e+25) | W^-eps1/W^-d/2=7.33e+18 | N*W^-D1=4.1e-109
      window n=199: R=35.5, rho=235.0, L/2=400, ball volume (2rho+1)^3/L^3 = 0.204 (proper subset iff rho<L/2: True)   [n=0,10: rho>L/2, ball = whole torus]
      pin-form zeta=Phi0: (sum_b Phi0^2)*(W^d eta) = 2.62e+04 | 9.05e+17 | 2.15e+34 = N^0.699 | N^0.716 | N^0.719
g=0.015625: gamma=c_lam=2.145e-33  K_tail=1.772e+34  with rho-2R=(log W)^(3/2): log10(log W) >= 68.5   (g=1: 78.7, g=10: 105.8)
class (eq:Psi) ratios Term1/Phi, Term2/Phi at r=0,3,6 (Z_12^3, c=0.2): W=1e2: (22080, 0.01),(351400, 0.0878),(1071000, 0.148); W=1e6: same Term1, Term2 x1e-4
class T: W=1e2 and W=1e6 identical: (154300, 9.77),(470900, 16.4),(555300, 10.6)
c=0.2 C2=2: max (r+1)^C2 e^-cr = 16.53 <= (C2/c)^C2 = 100;  c=0.2: max e^(-cs+sqrt(s)/2) = 1.367 <= e^(1/(16c)) = 1.367
```
Every deterministic hypothesis holds at all three `n`. The eventual thresholds (E5) are properties of the conclusion's `≺`, never of a hypothesis, so no astronomically large witness enters; `K_tail` shows they are astronomical for the real `c_λ`.

### Verdicts

- **Target 1** (`baZeta*`, nonneg, symm, Ward block): **PASS** (twin plus the BA Ward link).
- **Target 2** (`LWXigL`, bridge): **PASS** (equals the check file's `T2435_LWXigL`; bridge by unfolding).
- **Target 3** (`baZetaClaim_holds`): **PASS** (twin of `lwXiClaim_holds`; `D₁≥d+2C₂/(𝔠d)+1` is a new hypothesis, E4).
- **Target 4** (`baGbyZeta_holds`, `_hxi`): **PASS** by the sample-wise route (argument (i) 3); needs no unprimed pin, no `LWPsiAll`, no `LWLoop2gL`; new Lean ≈ 350 lines; for the 1a-audit: if the dispatcher prefers the hypothesis `BAGijGEX`, it saves those lines but makes L3c3a, L3d2 conditional on a pin slated for supersession (not recommended).
- **Target 5** (`BAEntryPsi`): **PASS** (twin via `baGbEXPii_holds`).
- **Target 6** (`BAAnpAuxG`): **PASS as a pin**; not proved here (needs L3d1's re-proof).
- **Target 7** (instances): **PASS** at `sz0`, `flow_sz0`; `LWLoop2gL` and the entry bound stay hypotheses.
- **(ii) per term and class:** both terms TRUE for class `(eq:Psi)` and class `𝖳`, constants independent of `n` (E7–E9). **Stop rule not triggered.**

## (a′) Preflight corrections — Mon Oct 12 05:45:00 UTC 2026

- Row E4 of (i) cites `B:426` for the paper's `+W^{-D}` floor. The floor is on `B:425` (the `(Gyiyjatom)` display is `B:424-426`); script output in (a″): the `sed -n 424,426p` block. No verdict changes.
- No other mismatch found: 33 Lean `file:line` citations taken from (a) and from the ticket were checked by `cite.sh` (output in (a″)): 33 of 33 name the cited declaration. The numeric tables of (a) were not re-run.
- Mon Oct 12 06:29:23 UTC 2026 (stage 1b): the probe's `BAZetaClaim` hypothesis `d + 2C₂/(𝔠 d) + 1 ≤ D₁` (E4, first constraint) does not imply `1/𝔠 ≤ D₁` (E4, Ward floor): `d=3, C₂=1.01, 𝔠=0.01` give `71.33 < 100` (`python3 -c`, tool log); 1b states `max (d + 2C₂/(𝔠 d) + 1) (1/𝔠) ≤ D₁`. The probe's `BAZetaWard` had `t n < 1` and no `0 < κ`; 1b has `0 < κ`, `0 ≤ t n ≤ BAflowT0` (`ba_G_data`). No verdict of (a) changes.

## (a″) Probe compile — Mon Oct 12 05:45:00 UTC 2026

Probe: `RBM3D/Probe/T2435Pins.lean` in `/Users/junyin/Lean_proof/RBM3D-wt/T2435`, commit e9a3986 on `t/T2435` (never merged, no root import). Scratch files: `scratchpad/T2435/{ev.sh,ev.out,cite.sh,closure.py}` (CONTROL H28). In the listing `CHECKFILE` is `docs/tickets/checks/T2435-check.lean` of the main worktree and `MAIN` is `/Users/junyin/Lean_proof/RBM3D`; the two negative controls are copies of the probe with one edit each, first error line only.

```
$ date -u
Mon Oct 12 05:38:36 UTC 2026
$ git --no-optional-locks log -1 --format="%h %s"; git --no-optional-locks diff --quiet HEAD -- RBM3D/Probe/T2435Pins.lean; echo "probe == HEAD: $?"
e9a3986 T2435: probe step: the statements of (vi) compile (zeta, LWXigL, targets 3-6; never merged)
probe == HEAD: 0
$ lake env lean RBM3D/Probe/T2435Pins.lean; echo "exit code: $?"
@baZetaSq : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ
@baZetaVar : {d : ℕ} →
  (sz : Sizes d) → (ℕ → ℂ) → (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ
BAZetaVarNonneg : Prop
BAZetaVarSymm : Prop
BAZetaWard : Prop
@LWXigL : {d : ℕ} →
  {sz : Sizes d} →
    FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ → ℝ) → ((n : ℕ) → Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) → Prop
BAZetaClaim : ℕ → Prop
@BAGbyZetaU : {d : ℕ} → Sizes d → (ℕ → ℝ) → ℕ → Type
BAGbyZeta : ℕ → Prop
BAGbyZetaHxi : Prop
BAEntryPsi : ℕ → Prop
BAAnpAuxG : ℕ → Prop
baGtoAG_holds : ∀ (d : ℕ), BAGtoAG d
baGbEXPij'_holds : ∀ (d : ℕ), 2 ≤ d → BAGbEXPij' d
baGbEXPii_holds : ∀ (d : ℕ), 2 ≤ d → BAGbEXPii d
BAm_norm_le_one : ∀ (d L : ℕ) [inst : NeZero L] (g : ℝ) (z m : ℂ), 0 ≤ z.im → BASelf d L g z m → ‖m‖ ≤ 1
exit code: 0
$ date -u
Mon Oct 12 05:38:52 UTC 2026
$ wc -l RBM3D/Probe/T2435Pins.lean; grep -n -E "sorry|admit|axiom|native_decide" RBM3D/Probe/T2435Pins.lean; echo "grep exit: $? (1 = no match)"
     331 RBM3D/Probe/T2435Pins.lean
grep exit: 1 (1 = no match)
$ diff <(sed -n "/^def T2435_LWXigL/,/^$/p" CHECKFILE | sed "s/T2435_LWXigL/LWXigL/") <(sed -n "/^def LWXigL/,/^$/p" RBM3D/Probe/T2435Pins.lean); echo "diff exit: $?"
diff exit: 0
$ diff -w <(sed -n 405,406p RBM3D/Graph/BAAtom2.lean) <(sed -n 617,618p RBM3D/Graph/BAAtom2.lean); echo "diff exit: $?"
diff exit: 0
$ negative controls (copies of the probe in the scratchpad; first error line only)
$ [.1 and .2 of the BAGbyZetaHxi conclusion swapped in the baGtoAG_holds call, line 308]
neg1.lean:308:4: error: Application type mismatch: The argument
$ [D1 = 11 instead of 12 in the BAZetaClaim call, line 263]
neg2.lean:263:48: error: unsolved goals
$ git -C MAIN --no-optional-locks diff --name-status t/T2435~1 main -- RBM3D RBM3D.lean lean-toolchain lake-manifest.json lakefile.toml; git ... log -1 --format=%h main
M	RBM3D.lean
A	RBM3D/BA/TwistGridWTail.lean
A	RBM3D/BA/TwistGridWTail2.lean
main 0113635; branch base 0b55de5
$ git -C MAIN --no-optional-locks diff --stat main...t/T2435
 RBM3D/Probe/T2435Pins.lean | 331 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 331 insertions(+)
$ name clash: grep -w of the 20 new/proposed names in main worktree RBM3D/ and in RBM3D/ of every other t/* branch
main worktree matches:        0
other t/* branches scanned: 438, matches: 0
$ grep -n "^/-! ## " RBM3D/Graph/AuxGraph2.lean; line counts of the section map ranges
61:/-! ## 1. The vocabulary of `(eq:xia1a2)` (target 1) -/
79:/-! ## 2. Deterministic facts (target 2) -/
609:/-! ## 3. The `≺` helpers and the deterministic comparisons -/
946:/-! ## 4. `claim:xi` (target 3) -/
1101:/-! ## 5. `(eq:Gbyxi)` off the diagonal and entrywise (targets 4 and 5) -/
1233:/-! ## 6. The radii (target 6) -/
1297:/-! ## 7. Compiled nonempty instances at the merged `d = 3` data
AuxGraph2:61,945 =      885 lines
AuxGraph2:946,1232 =      287 lines
AuxGraph2:1233,1296 =       64 lines
AuxGraph2:1297,1500 =      204 lines
$ grep -c seqP RBM3D/Graph/AnpKey*.lean
RBM3D/Graph/AnpKey.lean:0
RBM3D/Graph/AnpKey2.lean:0
RBM3D/Graph/AnpKey3.lean:0
RBM3D/Graph/AnpKey4.lean:0
RBM3D/Graph/AnpKey5.lean:0
RBM3D/Graph/AnpKey6.lean:0
$ grep -n "theorem GreenOff_carrier_decay\|theorem baGbEXPij._holds\|theorem baGbEXPii_holds" RBM3D/BA/GreenOff.lean RBM3D/BA/GreenLocal.lean
RBM3D/BA/GreenOff.lean:916:theorem GreenOff_carrier_decay (hd : 2 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes 
RBM3D/BA/GreenOff.lean:1289:theorem baGbEXPij'_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPij' d := by
RBM3D/BA/GreenLocal.lean:474:theorem baGbEXPii_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPii d := by
$ sed -n 424,426p paper/tex/B_graphical_lemmas.tex | cut -c1-100 ; the +W^{-D} floor line
\be\label{Gyiyjatom}
\big|(\Gc_t)_{\beta\beta'}\big|\prec \zeta(x_{i,j},x_{i',j'}):=\sum_{|[a]|+|[b]|\le (\log W)^{1+\e_1
\ee
line 425 ends with: W^{-D}
$ python3 -I closure.py /Users/junyin/Lean_proof/RBM3D-wt/T2435 RBM3D/Probe/T2435Pins.lean
import closure of RBM3D/Probe/T2435Pins.lean: 263 files; in it: RBM3D.lean / BA/TwistGridWTail / BA/TwistGridWTail2: none
$ cite.sh   # 33 (file, line, name) triples from (a) and the ticket; prints the lines whose text contains the name
citations checked: 33; line contains the cited name: 33; not: 0
OK   RBM3D/BA/FlowPins.lean: 259 1214
OK   RBM3D/BA/GreenOff.lean: 916 1198 1235 1252 1289 1333 1366
OK   RBM3D/BA/Ward.lean: 108 136
OK   RBM3D/BA/GreenStab.lean: 221
OK   RBM3D/BA/GreenCore.lean: 1625 1644
OK   RBM3D/Loop/GLoopFlow.lean: 58
OK   RBM3D/Graph/LWPins.lean: 360
OK   RBM3D/Graph/AuxGraph2.lean: 67 76 135 160 507 951 1106 1122 1160 1177
OK   RBM3D/BA/GreenSchur.lean: 124 139
OK   RBM3D/Graph/BAAtom2.lean: 418 606 677
OK   RBM3D/BA/GreenLocal.lean: 474
OK   RBM3D/BA/MFixedPoint.lean: 435
$ grep -n -E "^(def|abbrev|example)" RBM3D/Probe/T2435Pins.lean | cut -c1-110
40:def baZetaSq {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
50:def baZetaVar {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
55:def BAZetaVarNonneg : Prop :=
60:def BAZetaVarSymm : Prop :=
66:def BAZetaWard : Prop :=
78:def LWXigL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
87:example {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
95:def BAZetaClaim (d : ℕ) : Prop :=
110:abbrev BAGbyZetaU {d : ℕ} (sz : Sizes d) (R : ℕ → ℝ) (n : ℕ) : Type :=
117:def BAGbyZeta (d : ℕ) : Prop :=
132:def BAGbyZetaHxi : Prop :=
147:def BAEntryPsi (d : ℕ) : Prop :=
161:def BAAnpAuxG (d : ℕ) : Prop :=
184:def pPhi : ℕ → ℝ → ℝ := fun n _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
185:def pR : ℕ → ℝ := fun n => Real.log ((sz0.W n : ℕ) : ℝ) ^ (21 / 20 : ℝ)
186:def pρ : ℕ → ℝ := fun n => 2 * pR n + Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
191:example (hNn : BAZetaVarNonneg) (hSy : BAZetaVarSymm) (hWd : BAZetaWard) (h3 : BAZetaClaim 3) (h4 : BAGbyZ
280:example (ω : sz0.SeqΩ) : ∃ D : BALData (Idx 3 (sz0.L 0) (sz0.W 0)),
287:example (hX : BAGbyZetaHxi) {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGr
```

Narrative (facts from the listing above and from the probe file):
- Result: `lake env lean RBM3D/Probe/T2435Pins.lean` has exit code 0 (05:38:36-05:38:52 UTC); the output is the 20 lines of the 16 `#check` commands, no error or warning line. The probe has 331 lines (limit 400), no `sorry`/`admit`/`axiom`/`native_decide`, and is the only file `t/T2435` adds to `main` (`diff --stat main...t/T2435`).
- Base: compiled on the branch base 0b55de5. `main` (0113635) differs from the base in `RBM3D.lean` and in two new modules `BA/TwistGridWTail`, `BA/TwistGridWTail2`; the import closure of the probe (263 files, the probe included) contains none of the three, so the compile is also a compile against main's sources of every module the probe imports.
- Statements (lines 40-174 of the probe): `ζ = baZetaVar sz z t ρ D₁` on `baFMz sz z` with `D₁ : ℝ` a constant (floor `W^{-D₁}`, `baZetaSq`); `BAZetaVarNonneg`, `BAZetaVarSymm`, `BAZetaWard` (twins of `AuxGraph2:135, 160, 507`; `BAFlow` hypothesis, Ward floor term `L^d W^{-D₁}`); `LWXigL` (target 2; body identical to the check file's `T2435_LWXigL`, diff exit 0; the bridge `LWXigL (bandFM sz E) (seqP sz) t Φ ξ ↔ LWXi sz E t Φ ξ` is `Iff.rfl`, compiled at line 87); `BAZetaClaim` (target 3); `BAGbyZeta` with the index set `BAGbyZetaU` (all `x, y`, `x = y` included; no `LWPsiAll`, no `LWLoop2gL`, no unprimed `BAGbEXPij`) and `BAGbyZetaHxi` (target 4); `BAEntryPsi` (target 5); `BAAnpAuxG` (target 6, pin only). These are the names the probe fixes; none starts with `BAXi`; the 20 names (these and the 1b theorem names `baZetaVar_nonneg`, `baZetaVar_symm`, `baZeta_ward_sum`, `baZetaClaim_holds`, `baGbyZeta_holds`, `baGbyZeta_hxi`, `baEntryPsi_holds`, `baAnpAuxG_holds`) have 0 matches in the main worktree and on 438 other `t/*` branches.
- Instances (lines 191-308) at the data of (a)(ii): `d = 3`, `sz0`, `flow_sz0`, `t ≡ 1/2`, `Φ0 ≡ W^{-1/2}` (`ε₀ = 1/10`, `C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`), `ε₁ = 1/20`, `D₁ = 12`, `R = (log W)^{21/20}`, `ρ = 2R + (log W)^{3/2}`. Proved inside the examples: `LWPsiAll sz0 (1/10) 2 2 1 (fun _ => 1) Φ0`; `ρ ≥ 0`; `ρ + 1 ≤ N^τ` for every `τ > 0` (from `lwXiRad_holds`); `D₁ ≥ d + 2C₂/(𝔠d) + 1`, which is `12 ≤ 12` (tight: `D₁ = 11` fails, neg2); `R ≥ 0`; `ρ - 2R ≥ K log W` eventually for every `K`; the Ward premise `hA` with `A = Σ‖G - M‖`; `ζ(a, a) > 0` at `n = 0`; every diagonal pair `(x, x)` lies in `BAGbyZetaU`. Left as hypotheses of the examples: `LWLoop2gL` and `‖G - M‖ ≺ W^{-1/20}` (other gates' pins) and the unproved pins that are applied (`BAZetaVarNonneg`, `BAZetaVarSymm`, `BAZetaWard`, `BAZetaClaim 3`, `BAGbyZeta 3`, `BAEntryPsi 3`, `BAAnpAuxG 3`, `BAGbyZetaHxi`).
- Joint check of (i): one `ζ = baZetaVar sz0 zSeq (fun _ => 1/2) pρ 12` and one `(ρ, R, D₁)` satisfy the hypotheses of `BAZetaClaim` (part (b)) and of `BAGbyZeta` (part (a)) at once, and target 6 is fed with `ζ` through the conclusion `LWXigL` of target 3 (graph `baPQ`, `p = 2`). This shows the hypotheses are jointly satisfiable at (a)(ii)'s data, not that the conclusions hold.
- Bridge to G3 (last example): `(BAGbyZetaHxi …).1` and `.2` are accepted as `hξ0`, `hξ` of `baGtoAG_holds` at `ξ = cξ·ζ`, `R = pR 0`, without a cast; swapping them fails (neg1). The `hξ` premise of `baGtoAG_E` is the same text (`diff -w`, exit 0). A `D : BALData` with `D.G = C.G`, `D.M = C.M` exists (lines 280-283). The sample event `h` and the other premises of `baGtoAG_holds` are hypotheses of that example: it checks types, it is not an instance of G3.
- Target 6 stays a pin: the six `AnpKey*.lean` files contain no `seqP` (0 each), so `lwAnp_holds` (for `Prec sz`, `STFlow`, `etaT`) does not give the statement at `μ`, `C.eta` without a re-proof, as (a) says.
- Section map by script: `AuxGraph2` `:61-945` is 885 lines, `:946-1232` 287, `:1233-1296` 64, `:1297-1500` 204; section 4 starts at line 946, so the boundary of (a) (end of section 3, `:945`) is a section boundary.
- Mathlib names used by the examples (all compile): `Real.le_log_iff_exp_le`, `Real.exp_one_lt_d9`, `Real.abs_le_sqrt`, `Real.sqrt_eq_rpow`, `Real.rpow_add`, `Real.rpow_one`, `Real.tendsto_log_atTop`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.sqrt_pos`, `tendsto_natCast_atTop_atTop`, `tendsto_atTop_mono`, `Finset.single_le_sum`, `Finset.sum_nonneg`, `Nat.le_self_pow`, `one_le_div`, `add_pos_of_nonneg_of_pos`.
- Stop rule (a pin that does not compile, or a missing input): not triggered. This step compiles statements and instance hypotheses; it does not test whether a pin is true.

## (b) Script output and verdicts — Mon Oct 12 06:29:23 UTC 2026

**Verdicts.** (i) PASS: ζ = `baZetaVar` (the block loop-window variable of `(eq:xia1a2)` on `baFMz`, floor `W^{-D₁}`); one definition serves (a) `baGbyZeta_holds` (all `x, y`, `x = y` included; no unprimed pin, no `LWPsiAll`, no `LWLoop2gL`) and (b) `baZetaClaim_holds` (`LWXigL`); `baGbyZeta_hxi` is G3's `hξ` verbatim. (ii) not on the proved path (no `BAGbEXPij'`, no `GreenCore_decayRHS`); per-term, per-class (ii) not formalized, as (a) says. Targets 1-5 and 7 proved and compiled; 6 is the pin `BAAnpAuxG` (owner L3d1). Lines: `BAAuxGraph2` 1113, `BAAuxGraph2B` 1064 (stop line 2000 each).
Section map (`grep -n "^/-! ##"`): `AuxGraph2` §1-§3 `:61-945` -> A `:64-1027` (§4 `LWXigL` `:1028`, §5 instances `:1048`); §4 `:946-1100` -> B `:62-232`; §5 `:1101-1232` -> B `:233-858` (the new route: `BAAuxGraph2B_T_le`, `_zeta_bound`); §6 `:1233-1296` imported (`lwXiRad_holds`); §7 -> A `:1048-1113`, B `:880-1064`; G4 pin B `:859`.
```
$ git --no-optional-locks log --oneline main..t/T2435 | cut -c1-7 | paste -sd" " -
e1cdda3 d5c4b80 e9a3986
$ lake build -v RBM3D.Graph.BAAuxGraph2 RBM3D.Graph.BAAuxGraph2B 2>&1 | grep -E "Replayed RBM3D.Graph.BAAuxGraph2B|warning: RBM3D/Graph/BAAuxGraph2|error|Build completed"
ℹ [4002/4002] Replayed RBM3D.Graph.BAAuxGraph2B
Build completed successfully (4002 jobs).
$ wc -l BAAuxGraph2.lean BAAuxGraph2B.lean | head -2; cat <both> | grep -c -E "sorry|admit|axiom|native_decide"
    1113 RBM3D/Graph/BAAuxGraph2.lean
    1064 RBM3D/Graph/BAAuxGraph2B.lean
0
$ lake env lean ax.lean   # `#print axioms` of the 50 public declarations of both files
50 of 50 depend on exactly [propext, Classical.choice, Quot.sound], incl. baZetaVar_nonneg, baZetaVar_symm, baZeta_ward_sum, LWXigL_bandFM, baZetaClaim_holds, baGbyZeta_holds, baGbyZeta_hxi, baEntryPsi_holds
$ lake env lean precheck.lean (import RBM3D; import RBM3D.Graph.BAAuxGraph2B; #assert_rbm_axioms); lake env lean docs/tickets/checks/T2435-check.lean; diff <(def T2435_LWXigL, renamed) <(def LWXigL)
precheck (exit code 0, run 06:25:11-06:25:51): axiom audit: 12809 theorems, 4023 definitions, 0 axioms in `RBM` (compiler-generated decla
check exit: 0
diff exit: 0
$ python3 stmts.py <targets>   # statements extracted from the files (whitespace collapsed; theorem bodies cut at `:=`)
BAAuxGraph2.lean:69: def baZetaSq {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ := (∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n), ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n), ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), ‖(baFMz sz z).L n (t n) σ ![b₁, b₂] ω‖) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) + ((sz.W n : ℕ) : ℝ) ^ (-D₁)
BAAuxGraph2.lean:79: def baZetaVar {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ := Real.sqrt (baZetaSq sz z t ρ D₁ n a₁ a₂ ω)
BAAuxGraph2.lean:461: theorem baZeta_ward_sum {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (h0 : 0 ≤ t n) (hT : t n ≤ BAflowT0 sz z n) (hρ : 0 ≤ ρ n) (ω : sz.SeqΩ) {A : ℝ} (hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ A) (a₁ : Zd d (sz.L n)) : ∑ a₂, baZetaSq sz z t ρ D₁ n a₁ a₂ ω ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (t n))⁻¹ * (1 + A)) + (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁)
BAAuxGraph2.lean:1034: def LWXigL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop := (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧ PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω) (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧ PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2) (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)
BAAuxGraph2.lean:1044: theorem LWXigL_bandFM {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : LWXigL (bandFM sz E) (Sizes.seqP sz) t Φ ξ ↔ LWXi sz E t Φ ξ
BAAuxGraph2B.lean:69: def BAZetaClaim (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ → LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ → ∀ ε₁ : ℝ, 0 < ε₁ → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) → (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ) → ∀ D₁ : ℝ, max ((d : ℝ) + 2 * C₂ / (𝔠 * d) + 1) (1 / 𝔠) ≤ D₁ → LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ (baZetaVar sz z t ρ D₁)
BAAuxGraph2B.lean:83: theorem baZetaClaim_holds (d : ℕ) : BAZetaClaim d
BAAuxGraph2B.lean:578: abbrev BAGbyZetaU {d : ℕ} (sz : Sizes d) (R : ℕ → ℝ) (n : ℕ) : Type := {q : (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) × (Zd d (sz.L n) × Zd d (sz.L n)) // (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.1).1 - q.2.1) : ℝ) ≤ R n ∧ (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) q.1.2).1 - q.2.2) : ℝ) ≤ R n}
BAAuxGraph2B.lean:586: def BAGbyZeta (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₁ : ℝ, 0 < ε₁ → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) → ∀ (ρ R : ℕ → ℝ) (D₁ : ℝ), (∀ n, 0 ≤ R n) → (∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρ n - 2 * R n) → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := BAGbyZetaU sz R) (fun n q ω => ‖(baFMz sz z).GM n (t n) ω q.1.1.1 q.1.1.2‖) (fun n q ω => baZetaVar sz z t ρ D₁ n q.1.2.1 q.1.2.2 ω)
BAAuxGraph2B.lean:623: theorem baGbyZeta_holds (d : ℕ) : BAGbyZeta d
BAAuxGraph2B.lean:769: theorem baGbyZeta_hxi {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ R : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (D : BALData (Idx d (sz.L n) (sz.W n))) (ω : sz.SeqΩ) {c : ℝ} (hc : 0 ≤ c) (hG : ∀ x y, D.G x y = (baFMz sz z).G n (t n) ω x y) (hM : ∀ x y, D.M x y = (baFMz sz z).M n x y) (h : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n → (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n → ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ c * baZetaVar sz z t ρ D₁ n a b ω) : (∀ a b : Zd d (sz.L n), 0 ≤ (fun a b : Zd d (sz.L n) => c * baZetaVar sz z t ρ D₁ n a b ω) a b) ∧ (∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ R n → (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ R n → ‖D.G x y - D.M x y‖ ≤ (fun a b : Zd d (sz.L n) => c * baZetaVar sz z t ρ D₁ n a b ω) a b)
BAAuxGraph2B.lean:805: def BAEntryPsi (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ), LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ → LWLoop2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ → ∀ ε₁ : ℝ, 0 < ε₁ → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Φ n 0)
BAAuxGraph2B.lean:817: theorem baEntryPsi_holds (d : ℕ) : BAEntryPsi d
BAAuxGraph2B.lean:865: def BAAnpAuxG (d : ℕ) : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ) (P : BAPGraph (Fin 2)), 0 < p → P.g.nM ≤ p → (BAShadowPG P).LocReg345 p → P.g.mol (Sum.inl (P.ext 0)) ≠ P.g.mol (Sum.inl (P.ext 1)) → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ), ∃ c : ℝ, 0 < c ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ Φ : ℕ → ℝ → ℝ, LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ → ∀ ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ, LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ξ → PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n ab ω => P.g.auxVal (fun α β => ξ n α β ω) (fun e => if e = P.ext 0 then ab.1 else ab.2)) (fun n ab _ => ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ ^ P.g.nM * Φ n (c * ((zdistInf d (sz.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ p * Φ n 0 ^ (P.g.auxOrd - p))
$ python3 exs.py <file> <line>   # three of the eight compiled `example`s (all: A:1073 1086 1093 1104, B:965 979 1019 1046; targets in the narrative)
BAAuxGraph2.lean:1093: example (ω : sz0.SeqΩ) (a₁ : Zd 3 (sz0.L 0)) : ∑ a₂, baZetaSq sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2_ρ0 12 0 a₁ a₂ ω ≤ 2 * (2 * BAAuxGraph2_ρ0 0 + 1) ^ (2 * 3) * ((((sz0.W 0 : ℕ) : ℝ) ^ 3 * (baFMz sz0 zSeq).eta 0 (1 / 2))⁻¹ * (1 + ∑ x, ∑ y, ‖(baFMz sz0 zSeq).GM 0 (1 / 2) ω x y‖)) + (2 * BAAuxGraph2_ρ0 0 + 1) ^ 3 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ + ((sz0.L 0 : ℕ) : ℝ) ^ 3 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(12 : ℝ)) := baZeta_ward_sum sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2_ρ0 12 0 (κ := 1 / 2) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) flow_sz0 (by norm_num) (half_lt_t0 0).le (BAAuxGraph2_ρ0_nonneg 0) ω (fun x y => BAAuxGraph2_entry_le_sum 0 ω x y) a₁
BAAuxGraph2B.lean:965: example (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAAuxGraph2B_Φ0) (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)) (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) : LWXigL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAAuxGraph2B_Φ0 (baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12) := baZetaClaim_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0 BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0 BAAuxGraph2B_ρ0_nonneg BAAuxGraph2B_ρ0_rad 12 (by norm_num)
BAAuxGraph2B.lean:979: example (h6 : BAAnpAuxG 3) (hL : LWLoop2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BAAuxGraph2B_Φ0) (hent : PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)) (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))) : PrecL sz0 μ0 (U := BAGbyZetaU sz0 BAAuxGraph2B_R0) (fun n q ω => ‖(baFMz sz0 zSeq).GM n ((fun _ => (1 / 2 : ℝ)) n) ω q.1.1.1 q.1.1.2‖) (fun n q ω => baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 n q.1.2.1 q.1.2.2 ω) ∧ (∀ n (x : Idx 3 (sz0.L n) (sz0.W n)), ∃ q : BAGbyZetaU sz0 BAAuxGraph2B_R0 n, q.1.1 = (x, x)) ∧ PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)) (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => BAAuxGraph2B_Φ0 n 0) ∧ ∃ c : ℝ, 0 < c ∧ PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) (fun n ab ω => BAAtomInst2.baPQ.g.auxVal (fun α β => baZetaVar sz0 zSeq (fun _ => 1 / 2) BAAuxGraph2B_ρ0 12 n α β ω) (fun e => if e = BAAtomInst2.baPQ.ext 0 then ab.1 else ab.2)) (fun n ab _ => ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ ^ BAAtomInst2.baPQ.g.nM * BAAuxGraph2B_Φ0 n (c * ((zdistInf 3 (sz0.L n) (ab.1 - ab.2) : ℕ) : ℝ)) ^ 2 * BAAuxGraph2B_Φ0 n 0 ^ (BAAtomInst2.baPQ.g.auxOrd - 2)) := by have hR0 := BAAuxGraph2B_R0_nonneg refine ⟨baGbyZeta_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0 BAAuxGraph2B_R0 12 hR0 BAAuxGraph2B_sep, fun n x => ⟨⟨((x, x), ((split 3 (sz0.L n) (sz0.W n) x).1, (split 3 (sz0.L n) (sz0.W n) x).1)), by simpa using hR0 n, by simpa using hR0 n⟩, rfl⟩, baEntryPsi_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0 BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent, ?_⟩ have c3 := baZetaClaim_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) 2 2 1 (fun _ => 1) BAAuxGraph2B_Φ0 BAAuxGraph2B_psiAll hL (1 / 20) (by norm_num) hent BAAuxGraph2B_ρ0 BAAuxGraph2B_ρ0_nonneg BAAuxGraph2B_ρ0_rad 12 (by norm_num) obtain ⟨c, hc, H⟩ := h6 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 BAAtomInst2.baPQ (by norm_num) (by decide) localReg2_inst_Q_locReg345 (by decide) (1 / 10) 2 2 1 (fun _ => 1) exact ⟨c, hc, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) BAAuxGraph2B_Φ0 BAAuxGraph2B_psiAll _ c3⟩
$ names.sh | wc -l   # public names of the two files (stems BAAuxGraph2_/BAAuxGraph2B_ or the pinned target names)
      50 names
$ git grep -w -F -l <50 names> HEAD -- RBM3D (main, excluding the two new files); same on every other refs/heads/t/* branch
main:        0 files; branches scanned (excluding t/T2435): 439; files matching:        0
$ git --no-optional-locks diff --stat main...t/T2435
 RBM3D/Graph/BAAuxGraph2.lean  | 1113 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAAuxGraph2B.lean | 1064 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2435Pins.lean    |  331 ++++++++++++
 3 files changed, 2508 insertions(+)
```

Narrative (every item is in the listing above or in the files):
- Route of (a): per sample `GreenOff_carrier_decay` (`BA/GreenOff.lean:916`) at `φ = ‖𝓛_{(-,+)}‖^{1/2}`, `Ψ = W^{-d/2}`, `P = N^{τ₀}`, `δ = W^{-ε₂}`, `ε₂ = min(ε₁/2, d/2)`, with the events of `baLDEin_holds` and `Ω` from `hent` (`BAAuxGraph2_whp_entry`); then `BAAuxGraph2B_T_le`: `GreenOff_T ≤ (S+1) ζ + 2F`, `S = expC (d-2) (γ/2)`, `γ = GreenStab_clam d 𝔡⁻¹ κ`, tails at `s = K log W`, `K = (max D₁ 0 + 1)/γ`, `F = W^{-max(D₁,0)/2} ≤ ζ` (`BAAuxGraph2B_floor_zeta`).
- `φ ≤ 2` comes from `‖G‖_max ≤ 2` (`‖G-M‖ ≤ δ ≤ 1`, `‖M‖_max ≤ 1` in `ba_G_data`; `BAAuxGraph2B_loop_le`), not from (a) (i) 3's `L_max ≤ 2(W^d η)⁻¹`: no lower bound on `η` is used. `ε'`, `K_cl`, `γ`, `S` depend on `(d, κ, 𝔡)` only (`GreenOff_pin_consts`), fixed before `𝔠, sz, z, t`; no `M = mI`, no smallness of `g` (C1).
- Ward block form, proved: `Σ_{a₂} ζ² ≤ 2(2ρ+1)^{2d} (W^d η)⁻¹ (1+A) + (2ρ+1)^d W^{-d} + L^d W^{-D₁}` (`baZeta_ward_sum`); the floor term is `≤ W^{-d}` only for `D₁ ≥ 1/𝔠` (`BAAuxGraph2_floorL_le`), hence the `max` in `BAZetaClaim`.
- Differences from the statements of (vi): (A) the `D₁` hypothesis (see (a′)); (B) `baZeta_ward_sum` has `0 < κ`, `0 ≤ t n ≤ BAflowT0` instead of `t n < 1`; (C) `baGbyZeta_hxi` is a theorem (probe: the `Prop` `BAGbyZetaHxi`). `BAGbyZeta`, `BAEntryPsi`, `BAAnpAuxG`, `LWXigL` are the probe's statements; `LWXigL` equals the check file's `T2435_LWXigL` (diff exit 0).
- Instances (the eight `example`s, line numbers above): A:1073-1104 targets 1, 2; B:965 target 3 (`LWLoop2gL`, `hent` as hypotheses); B:979 targets 4, 5 and `BAAnpAuxG 3` fed with `ζ` from target 3 (`h6` is L3d1's pin); B:1019, 1046 `baGbyZeta_hxi` into `hξ` of `baGtoAG_holds`. Data: `d=3`, `sz0`, `flow_sz0`, `t ≡ 1/2`, `D₁ = 12 = max(12, 6)` (tight), `ρ - 2R = (log W)^{3/2}`, `R = (log W)^{21/20}`.
- Not done: `BAAnpAuxG` is not proved (a pin; `AnpKey*` have no `seqP`, per (a)); `RBM3D.lean` untouched (the hub adds `import RBM3D.Graph.BAAuxGraph2` and `import RBM3D.Graph.BAAuxGraph2B` after the last `import`, CLAUDE.md §3 (A) 4); the full `lake build` is the hub's at merge (the pre-check above imports both modules).

## (c) Verified Mathlib names (compile; each used in the two files)

`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`, `Finset.sum_filter_add_sum_filter_not`, `Finset.sum_product`, `Finset.sum_mul_sum`, `Real.pow_rpow_inv_natCast`, `Real.rpow_def_of_pos`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_le_iff`, `Real.sqrt_le_one`, `Complex.im_le_norm`, `Real.rpow_le_one_of_one_le_of_nonpos`, `le_of_sq_le_sq`, `inv_le_one_of_one_le₀`, `Nat.pow_le_pow_left`, `Nat.le_mul_of_pos_left`, `one_le_pow₀`. Deprecated, replaced (compiler warnings, tool log): `mul_le_one₀` -> `mul_le_mul`, `if_pos` -> `simp [hab]`.

## (d) Open issues and paper-delta candidates

- `T2435a`: ζ is the block loop-window variable of `(eq:xia1a2)` at the block radius `ρ`, not the atom-centre entry sum of `(Gyiyjatom)` (`B:424`).
- `T2435b`: the floor `W^{-D}` of `B:425` is an explicit exponent `D₁ ≥ max (d + 2C₂/(𝔠 d) + 1) (1/𝔠)` in `BAZetaClaim` (the paper: any large `D`).
- `T2435c`: `(eq:Gbyxi2_BA)` (a) is proved from `GreenOff_carrier_decay` sample-wise, not from `(GijGEX_BA)` with deterministic `Φ`; it needs `ρ - 2R ≥ K log W` for all `K` (the paper's window is `(log W)^{1+ε₁}`).
- `T2435d`: Ward in block form, `Σ_{a₂} ζ([a₁],[a₂])² ≺ (W^d η_t)⁻¹` (the paper's `Σ_α ... ≺ η_t⁻¹` is fine-lattice).
- Open: `BAAnpAuxG` (L3d1); the root imports (hub). Report length: (a), (a′), (a″) took 219 lines before this stage, so the ticket's 250 is exceeded; CLAUDE.md §6's 300 holds.
