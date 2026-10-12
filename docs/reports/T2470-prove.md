Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 19:47:15 UTC 2026
Scratch `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2470`. Instance data = `BA/LWPinsBA.lean` §3 / `BAAuxGraph2B` §7 (`sz0`, `flow_sz0`). "ev." = eventually in `n`.

### (i) Exponent table (`p=2`, `d=3`, `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `ε₀=1/10`, `C₁=C₂=2`, `C₃=1`, `Cc≡1`, `Ψ=Φ≡W^{-1/2}`, `t≡1/2`)
| # | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | bandwidth `𝔠` | 1/6 | `N^𝔠 ≤ W` (`Sizes.lean:168`) | `N^{1/6}=11.31(n+1)^3 ≤ 32(n+1)^5`; n=0: 11.31 ≤ 32 |
| 2 | `K0` | `⌈1/𝔠⌉=6` | `L^d ≤ W^{K0}` (BALocRegConcl (b); `LWMoment:1799`) | `64(n+1)^3 ≤ 2^30(n+1)^30` (script, n<300) |
| 3 | `D` | `(p(2+C₂)+1)/𝔠 = 54` | `W^{-D} ≤ N^{-(Kf+1)}`, `Kf=p(2+C₂)=8`, `N ≤ W^{1/𝔠}` (`LWMoment:1801`, `prec_err`) | 0 (equality choice, as band) |
| 4 | window exponent `c` of (b) | `ε₀/2=1/20` | `W^{-d/2} ≤ Ψ' ≤ W^{-c}`, `Ψ'=max(1,C₃)N^{τ₁}Φ(0)`, `τ₁ ≤ 𝔠ε₀/4=1/240` | upper: `Ψ' ≤ W^{-0.475}` vs `W^{-0.05}` (0.425); lower: `W^{-1/2}` vs `W^{-3/2}` (1.0) |
| 5 | `(W^d)^{-1} ≤ AΨ'^2` (`baGtoAG_E`) | `A=1` | `Ψ'^2 ≥ Φ(0)^2 = W^{-1}` | `W^{-3} ≤ W^{-1}` (exponent 2) |
| 6 | `D₁` (`baZetaClaim_holds`), `ε₁` | `max(d+2C₂/(𝔠d)+1, 1/𝔠)=max(12,6)=12`; `ε₁=ε₀` | `D₁ ≥` that max (`BAAuxGraph2B:80`) | 0 at 12 |
| 7 | radius `R`, `ρ` | `R=K(log W)^2`, **`ρ=(2K+1)(log W)^2`** | BA `baGbyZeta_holds`: `∀K', ev. K' log W ≤ ρ−2R` (`BAAuxGraph2B:594`); `baZetaClaim`: `ρ+1 ≤ N^τ` | band choice `ρ=2R+1` (`AuxGraph2:1114`) gives `ρ−2R=1`: **fails**. New choice: `ρ−2R=(log W)^2`, closes for log W ≥ K'; `ρ+1 ≤ N^τ` by `lwXiRad_holds` with `C=2K+1, K=2` |
| 8 | `η_t=(1−t)Im m` upper | `≤ 1/2` | `η ≤ 1` needs `Im m_F ≤ |m_F| ≤ 1` (`m_F=L^{-d}tr M^{(B)}` by `BASelf`, `‖M‖_max ≤ 1` from `ba_G_data`, `GreenLDE:55`) and `t ≥ 0` | `η⁻¹ ≥ 1` as `anp_arith` needs |
| 9 | `η_t` lower | `η ≥ (κ/2) N^{-1+ε}` | `t ≤ BAt0=Im m/(Im m+Im z)` (`MFixedPoint:279`) ⇒ `η ≥ (1−t0)Im m_F ≥ Im z·Im m/(Im m+Im z) ≥ κ Im z/2`, `Im m=Im m(z,g) ≥ κ` and `Im z ∈ [N^{-1+ε},1]` (`BAdom`, `MFixedPoint:435`), `m_F=m/√t0` (`BAflow_real`) | need `N^ε ≥ 2/κ=4`: n=0 `N^ε=4.287` (7%); ev. generally. (At `sz0`, `Im z ≥ 11/30`: `zSeq_im_ge`, so `η` is O(1).) |
| 10 | decay `(C,c)` of `BAAtom_decay_E` | `c = min(μ, c_M, 1)`, `c_M=BAct_rate(3,Λ,κ)=4.158e-3`, `μ=BAp5s_rate=1.287e-32`, `Λ=𝔡⁻¹=10` | `c` depends on `(d,Λ,κ)` only, valid for all `0<g0≤Λ`, `BAReal` (`BAAtom2:537`) | uniform in `g0`: same `c` at `g=1/64,1,10` (script) |
| 11 | tail | `e^{-c r/2}`, **`r=(log W)^2`** (not `K(log W)^2`) | `exp(−c(log W)^2/2) N^{a} ≤ N^{−b}` ev.: `log W ≥ M=2(a+b)/(𝔠c)` (`lwMoment_tail:473`); `K` enters only as far pairs `bdist > K(log W)^2 ≥ card·r` | `a=nM+nV+1`, `b=Kf`; with `a+b=21` (assumed `nV≤10`): `M=1.96e34`. Only in `∀ᶠ n`; no hypothesis of any target depends on it |
| 12 | `t`-power | `t^{nW−p}` | `E|LWfg|^p = t^{-p}E|fxyVal(BAlwData)|^p` and `val(BAlwData)=t^{nW}val(D₁)` (`BAExp14d_val_scale`); `nW ≥ p` (target 3, 2nd conjunct) | `t^{nW−p} ≤ 1` for `0<t<1`; `t=0`: `G−M=−M(√tV+tm)G` (`ba_G_data`, 5th conjunct) gives `GM=0`, `LWfg=0` |
| 13 | `ord`, `n_M` | `2p ≤ ord`, `n_M ≤ p` | `lwMoment_anp_arith:998`: `η^{-nM}Φ(0)^{ord−p} ≤ η^{-p}Φ(0)^p` (`η ≤ 1`, `Φ(0) ≤ 1`) | `3p ≤ ord` (distinct atoms) is **not** read |
| 14 | `Φ(c·)` | `c=1` | `Φ(c_G s) ≤ K_G Φ(s)` for `c_G'=min(c_G,1)` (`LWPsiRel`, `hPcK` in `lwMoment_prec_anp:1034`); `∃c` precedes `𝔠`, `K0`, `K` | `c=1`, as band (`lwMoment_holds:1787`) |
| 15 | near pairs | `bdist ≤ K(log W)^2` | `|f| ≤ A η⁻¹ μ`, `μ=max_a|𝓛^{(1)}_a−m| ≺ Ψ'^2` (`baGbEXPav_holds`, `Step1Boot:97` needs `Ψ'` in `[W^{-d/2},W^{-ε₀}]`), `A ≤ 2`, `Ψ'≤max(1,C₃)Φ(0)`, `Φ(0) ≤ C₁(K log²W)^{C₂}Φ(cr)` | `(max 1 (K log²W))^{C₂} ≤ N^{τ₁}` ev. (`lwMoment_rad`) |

**Contract (1)–(5) vs premises of the `𝓜_x≠𝓜_y` branch** (`Q ∈ outs`, `P0 ∈ partition` from (c)):
| premise read | conjunct that gives it |
|---|---|
| `Q.g.Normal`, `BAReach K P0 Q` (K=`lvl1Cutoff`), `n_V` counters | `BALocRegConcl` (c) |
| `Q.g.LocStd`, `2p ≤ scalingOrder` | (a) |
| `Q.g.nM ≤ p` (for `BAAnpAuxG`, `anp_arith`) | `BALocReg15` 2nd conjunct, from (c) |
| `(BAShadowPG Q).LocReg345 p` (for `baAuxNested_holds`, `BAAnpAuxG`) | `BALocReg15` 4th conjunct at `LocStd` (a), `BAReach` from (c) |
| `𝓜_x ≠ 𝓜_y` | branch hypothesis (`by_cases` as `LWMoment:1290`) |
| errors: size `≤ W^{-D}` in window | (b) only; no (1)–(5) |
| identity of expectations | (d): `BASelf`, `0≤t<1`, `3 ≤ L` from `ba_G_data`/`BAflow_real` |
`BALocReg15` quantifies `∀ P0 ∈ (ofLGraph (fxyPowGraph p)).partition, ∀ K Q, BAReach K P0 Q`, the same shape as (c): the composition closes with no extra premise beyond the path binder of `baLocReg15_holds` (`BALocReg1B:264`).

### (ii) One nondegenerate instance, and L4-C4 (b)
Instance: `d=3`, `p=2` (`2∣p`), `sz0` (`n=0`: `L=4`, `W=32`, `N=2097152`, `λ=1/64`), `z=zSeq`, `flow_sz0 : BAFlow sz0 (1/2)(1/10)(1/6)(1/10) zSeq`, `t≡1/2 ≤ BAflowT0` (`t0_sz0`: `≥ 2/3`, `FlowPins:1227`), `ε₀=1/10`, `Ψ=Φ≡W^{-1/2}`, `C₁=C₂=2`, `C₃=1`, `Cc≡1`, `K0=6`, `D=54`, `D₁=12`, `ε₁=ε₀`. Deterministic hypotheses checked: `LWWindow` (`W^{-3/2} ≤ W^{-1/2} ≤ W^{-1/10}`), `LWClass` (`Φ ≤ W^{-ε₀}`, `W^{-3/2} ≤ C₃Φ(0)`), `LWPsiRel` (`Φ` constant: antitone; `Φ(0)=Cc·Φ(ℓ)`; `Φ(ℓ₁)≤2(ℓ₂/ℓ₁)^2Φ(ℓ₂)`), `WO` (`W^{-1.4} ≤ λ ≤ 10`), bandwidth, `N^ε ≥ 4`, `κ ≤ Im m`. Target 3 has no hypothesis (`p=2, c=1/4, K0=2, d=3, D=10` as in the ticket are admissible: it is unconditional). Target 1 (b): `BASelf`, `0≤t<1` from `ba_G_data`. Hypotheses left as hypotheses (other gates): `STInitialGT2gL`, `LWLoop2gL` (inside `LWAssmgL`), `BAAnpAuxG 3`, the path binder (while T2469 unmerged).
```
cd $S && python3 -I pre2.py        # pre2.py = 30 lines, sz0 sequences + BASelf on Z_4^3 + constants of BAAtom_decay_E
K0=6  D=54  D1=12  window exponent c=eps0/2=0.05  Kf=p(2+C2)=8
sz0, n<300: N^c<=W, L^d<=W^K0, W^(-d/2+dd)<=lam<=1/dd, Phi=Psi=W^-1/2 in class/window: True
n=0: (L,W,N)=(4,32,2097152) N^c=11.31 lam=0.01562  N^eps=4.287 (need >=2/kap=4)
Psi' = N^tau1 W^-1/2, tau1<=c*eps0/4=0.00417: exponent of W <= -0.4750; need <= -eps0/2=-0.05
logW=10: rho-2R = 1 (band choice 2R+1) vs 100 ((2K+1)log^2 W choice); need >= K'*logW for every K'
logW=100: rho-2R = 1 (band choice 2R+1) vs 10000 ((2K+1)log^2 W choice); need >= K'*logW for every K'
BAct_rate(d,Lam=10,kap=1/2)=4.1580e-03  BAp5s_rate=1.2868e-32  c of BAAtom_decay_E=1.2868e-32 (depends on d,Lam,kap only)
g=0.01562: Im m=0.9993>=kap, selfm resid 1e-16, max_x|M_0x|e^(cM|x|)cM=0.0042<=1 ; logW*=2(a+b)/(cc*c)=1.958e+34 (a+b=21 assumed)
g=1.00000: Im m=0.5959>=kap, selfm resid 4e-16, max_x|M_0x|e^(cM|x|)cM=0.0025<=1 ; logW*=2(a+b)/(cc*c)=1.958e+34 (a+b=21 assumed)
g=10.00000: Im m=0.5594>=kap, selfm resid 1e-16, max_x|M_0x|e^(cM|x|)cM=0.0024<=1 ; logW*=2(a+b)/(cc*c)=1.958e+34 (a+b=21 assumed)
n=0 Bctl(t=1/2)=6.196e-05 = W^-2.796 ; Bctl^(1/4)=W^-0.699 vs eps0 target W^-0.1 ; Bctl<=Psi^2=W^-1: True
n=10 Bctl(t=1/2)=1.461e-20 = W^-2.955 ; Bctl^(1/4)=W^-0.739 vs eps0 target W^-0.1 ; Bctl<=Psi^2=W^-1: True
n=1000 Bctl(t=1/2)=6.013e-50 = W^-2.982 ; Bctl^(1/4)=W^-0.745 vs eps0 target W^-0.1 ; Bctl<=Psi^2=W^-1: True
```
(`Bctl=W^{-d}Bparam(d,L,λ,t,0)`, `Params.lean:36`, `Sizes.lean:214`; `E=0`, `Λ=10=𝔡⁻¹`, `κ=1/2`; `BASelf` solved on the spectrum `2Σcos(2πk_j/4)` of `Ψ^{(B)}`, `zdistD` = ℓ¹ torus distance.)

**External hypotheses (TEAM §8 lesson 14), exponent compatibility at the instance only** (the chain pins for BA are other gates): `STInitialGT2gL` asks `‖G−M‖_max ≺ W^{-1/10}` and `max 𝓛^{(2)} ≺ Ψ²=W^{-1}`; the chain bounds `STStep1WeakgL` (`Bctl^{1/4}`, `Carrier:184`) and `STKboundgL` (`Bctl^{k−1}`, `Carrier:147`) have exponents `−0.70…−0.75` and `−2.8…−2.98` at `t=1/2` (script), so `W^{-1/10}` and `W^{-1}` are not contradicted. `BAAnpAuxG`: pin of L3d1, same exponents as the merged band `lwAnp_holds` (rate `((W^dη)⁻¹)^{nM}Φ(c·)^pΦ(0)^{ord−p}`, `BAAuxGraph2B:865` vs `lwMoment_anp_arith`); path binder: concluded by T2469 (state file: `proving`, 19:33:51 UTC); T2466 state file: `merged 03109267` (19:00:37 UTC).

**L4-C4 (b): the `x ~ y` outputs.** `x ~ y` means `atomSetoid Q.g (ext 0) (ext 1)`; `BALocReg1_mol_of_atom` (`BALocReg1:304`) gives `ext 1 ∈ Q.g.mol (ext 0)`, so `𝓜_x = 𝓜_y` and the output goes to the tail branch with every output having `molOf ext0 = molOf ext1` (atom or not). Far pair ⇒ `card(E'⊕I')·r < bdist(ℓ ext0, ℓ ext1)`, `r=(log W)^2`. If every `J`-edge (waved, `M`-dotted, `Ψ`-dotted) had `bdist ≤ r`, `BAAtom_shadow_conf` (`BAAtom:515`) gives all waved edges of `Γ.shadow` within `r`, and `auxGraph_mol_dist` (`AuxGraph:174`, `hD` = `Γ.Normal.1`, `shadow.dotted=Γ.dotted`, `BAAtom_shadow_molOf_eq_iff`) gives `bdist ≤ card·r`, a contradiction; so `BAAtom_term_tail` (hypothesis `hbad`) applies, then `BAAtom_tail_sum`, then row 11. Only `2p ≤ ord` (row 13) is read at `𝓜_x≠𝓜_y`; `3p` is not. Numbers at `g=1/64,1,10` (script): `Im m ≥ κ=1/2` holds at all three (0.999, 0.596, 0.559), the same `c=1.287e-32` serves all three (`g0 ≤ Λ`, no smallness of `g`), `M^{(B)}` decays within `c_M⁻¹e^{-c_M|x|}` (max ratio ≤ 0.0042); the tail beats `N^{a+b}` for `log W ≥ 2(a+b)/(𝔠c) ≈ 2e34`, an `∀ᶠ n` threshold only. The pair-count route (T2398a) is not needed.

### Verdict
- Target 1 (`LWfg`, 1(a) band bridge, 1(b) BA bridge): **PASS** (`S=1` in `baFM`, `FlowPins:327`; `t·LWfg = fxyVal` with `BAlwS=t·svarF(0)`; `GM=0` at `t=0`, row 12).
- Target 2 (`LWMomentG`, `LWMoment_iff_bandPin`, `BALWMoment`): **PASS** (all quantifiers as `LWMoment`; `∃c` before `𝔠`).
- Target 3 (`ba_localregularX_holds`): **PASS**, unconditional.
- Target 4 (`baLWMoment_of_anp`): **PASS** with the following changes of route, none changing a pinned statement:
  - **F1** `ρ` must be `(2K+1)(log W)^2`, not the band's `2R+1` (row 7); the BA `baGbyZeta_holds` separation hypothesis is `∀K', ev. K' log W ≤ ρ−2R`.
  - **F2** the tail exponent is `c(log W)^2/2` (ticket text has `cK(log W)^2/2`); `K` only fixes the far set.
  - **F3** `c=1.287e-32` (row 10): thresholds are astronomically large but occur only inside `∀ᶠ n`.
  - **F4** `S'=svarF(0)`, `Sp'=lift(BATheta)` decay for the `D₁` data (needed by the tail branch, which cannot use `baGtoAGT_holds`: its main term is not small when `𝓜_x=𝓜_y`) is proved inside `baGtoAGT_holds` (`BAExp14d:307-`), not exported; it must be redone in 1b (`BAExp14d_svar0` private).
  - **F5** ticket instance 5(i) "lists nonempty" does not follow from `∃ outs errs`; it would need (d) plus a proof that its left side `E|f_{xy}|^p` is nonzero at one datum (not checked here; `g0=0`, `E=0`, `m=i` solves `m=−1/m`, `Im m>0`, and (d) has no `g0>0` premise) — a separate argument. Applying the theorem at `p=2,c=1/4,K0=2,d=3,D=10` is unconditional.
- Not written here (outside this stage's format): section map, line prediction.

## (b) Script output and narrative (stage 1b, `prover-hard`, claude-sonnet-5-5; written Mon Oct 12 21:05:34 UTC 2026; branch t/T2470, head `1010ab31`)
A = `RBM3D/Graph/BAMomentGen.lean`, B = `RBM3D/Graph/BAMomentGenB.lean`; `Test/Axioms.lean` and every merged file unchanged.
### Decisions (i), (ii) of the start condition, taken once at the 1b start
```
$ date -u; cat docs/queue/T2469.state; git log --oneline main | grep -E "T2469|T2466"
Mon Oct 12 19:54:34 UTC 2026
state: proving
reason: started (H255, H12): workflow wf_a4c55321-0da, stage 1a preflight → 1b prover-hard → auditor; branch t/T2469 from main ad52b370
updated: Mon Oct 12 19:33:51 UTC 2026
reports: docs/reports/T2469-prove.md, docs/reports/T2469-audit.md
03109267 T2466: merge BA-L L4c2 Graph/BAExp14d, BAExp14dB
5812a277 H255: tickets T2469-T2471 and checks, T2467 Amend 1, REQ Unotice, DECISIONS §274, CONTROL, ROUTES
a1628b9d H252: tickets T2464-T2466 and checks, T2460 Amend 1, T2457 sign-off, DECISIONS §271, CONTROL
```
- (i) T2469 not merged (no T2469 merge commit; the two `H` lines above are docs commits that name T2469 / T2466) -> the path binder of `baLocReg15_holds` is the first hypothesis of
  `baLWMoment_of_anp`, verbatim (no new `Prop`). Re-check at 20:34:35 UTC: `docs/queue/T2469.state` = `blocked` (its 1a, §227 split question), main head c986735f.
- (ii) T2466 merged at `03109267`, an ancestor of t/T2470 -> imported `BAExp14d_dataT`, `BAExp14d_val_scale`, `baGtoAGT_holds` (BAExp14d.lean:60, 111, 307); no private copy
  of the rescaling. The rescaled-kernel decay (preflight F4) is redone in `BAMomentGen_consts` (copy of the first half of the proof of `baGtoAGT_holds`, BAExp14d.lean:307-379).
### Size against the stop line (2,000 per file)
```
$ wc -l RBM3D/Graph/BAMomentGen.lean RBM3D/Graph/BAMomentGenB.lean
    1549 RBM3D/Graph/BAMomentGen.lean
     847 RBM3D/Graph/BAMomentGenB.lean
    2396 total
```
`wc -l` at the section commits (tool log): A 149 / 856 / 1468, then A 1468 + B 409 = 1877; B grew to 847 with `BAMomentGen_lists_nonempty`. No stop rule fired.
### Verdict of 1a (ii) (L4-C4 (b)) with its numbers
Confirmed by the compiled proof: `by_cases hmol` (mol equality) in `BAMomentGen_prec_far_r` covers every output, so `x ~ y` needs no separate case; an output with `𝓜_x = 𝓜_y` goes to `BAMomentGen_scalemole` (A:738: no labelling is confined, so
`BAAtom_term_tail` + `BAAtom_tail_sum` apply); `BAMomentGen_consts` (A:364) gives `(C, c)` with `c = min(c₁, BAp5s_rate, 1)`, uniform in `0 < g₀ ≤ 𝔡⁻¹` and `BAReal`: no smallness
of `g`, no `M = mI`. The numbers of (a) (ii) (`g = 1/64, 1, 10`: `Im m ≥ 1/2`, one `c = 1.287e-32`) stand; nothing outside C1 is read; `3p ≤ ord` is not read.
### Section map (band `LWMoment.lean` line -> BA), as finally written
```
imported unchanged: lwMoment_sum_det, _phi_facts, _zdistInf_le, _expC_nonneg, _anp_arith, _near_arith, _rad, _norm_list_sum_le, _pow_conj, Ward lwMoment_CS, lwXiRad_holds; BAExp14c_eta_le_one for lwMoment_etaT_le_one
band:57 lwMoment_val_smul -> BAExp14d_val_scale (imported, BAExp14d.lean:111)
band:79 lwMoment_fxy_bridge -> A:93 LWfg_baFMz
band:112 lwMoment_prec_of_whp -> A:165 prec_of_whp, A:179 whp_of_prec
band:160 LWMomentCtx, lwMoment_flow_facts, _size_tendsto, _eta_lower -> dropped: hyps hd..hassm; ba_G_data, BAExp14a_eventual_scalars
band:208 lwMoment_D, _Dt_eq, _pval_smul, _pval_evX -> BAMomentGen_D A:335; rest dropped (BAPGraph lists, no m-evaluation)
band:258 lwMoment_expand -> A:1287 BAMomentGen_expand (+ cont_term/val/comb/fxyVal, integral_list_sum)
band:343 lwMoment_decay -> A:364 consts, A:651 decay
band:380 lwMoment_scalingSize_le / _tail_le -> A:195 / A:223 (counters)
band:473 lwMoment_tail / _Wneg_le / _L_le_W -> A:247 / A:283 / A:311
band:514 lwMoment_floor -> A:548 floor
band:644 lwMoment_pval_claim / _env -> A:444 / A:1127
band:725 lwMoment_R / _Psi_facts / _psiAll / _entry_whp -> A:487 / A:500 / A:490 / A:540
band:827 lwMoment_prec_err -> A:672
band:896 lwMoment_auxVal_smul, _ext_mol -> A:877, A:885
band:925 lwMoment_prec_scale (+ lwScalemole_holds, AuxGraph:1130) -> A:802 + A:738 scalemole
band:1034 lwMoment_prec_anp (+ lwGtoAG/AuxNested/Anp) -> A:904 (baGtoAGT_holds, BAAnpAuxG instance; baAuxNested_holds not needed)
band:1252 lwMoment_prec_int -> A:1175
band:1233 LWMomFar, lwMoment_LWf_zero -> A:1386 Far, A:1391 LWfg_zero
band:1266 lwMoment_prec_far_r / _prec_far -> A:1438 / A:1467
band:1353 §9 gres_blockMat, avgErr_sum, row_le -> dropped: BAMomentGen_sumS B:51 + BAExp14a_X_eq
band:1492 lwMoment_f_le -> B:77
band:1546 LWMomNear, Psi', Psi'_facts, maxLoop2_prec, avg_whp -> B:128, B:133, B:166, B:178, B:198
band:1652 lwMoment_prec_near_pre / _fxyPow_val / _prec_near -> B:211 / dropped (BAMomentGen_LWfg_env B:301) / B:336
band:1785 lwMoment_holds (target 4) -> baLWMoment_of_anp B:370
band:- (preflight F5, not in the band) -> BAMomentGen_lists_nonempty B:774 (+ pt, P, sigma, resolvent, pt_fxy, PF_pos, selfI, fxyPow_pt)
band:- §11 instances (:1818-1870) -> examples A:1528-1549 (targets 1-3); B:[471, 840] (target 4; target 3 with nonempty lists)
```
### Input table of target 4 (name, file:line; branch base e9d820fc = main incl. T2466)
```
ba_localregularX Graph/BAEngine.lean:335  baShapeLL_e2_tn Graph/BAShapeO2B.lean:221  baShapeLL_macroA_tn Graph/BAShapeO2B.lean:269
baShapeLL_macroB_tn Graph/BAShapeO2B.lean:303  BALocRegConcl Graph/BAEngine.lean:220  baLocReg15_holds Graph/BALocReg1B.lean:264
BAReach Graph/BALvl1C.lean:80  baGtoAGT_holds Graph/BAExp14d.lean:307  BAAtom_term_tail Graph/BAAtom2.lean:82
BAAtom_tail_sum Graph/BAAtom2.lean:274  BAAtom_shadow_conf Graph/BAAtom.lean:515  BAAtom_shadow_molOf_eq_iff Graph/BAAtom.lean:100
auxGraph_mol_dist Graph/AuxGraph.lean:174  baZetaClaim_holds Graph/BAAuxGraph2B.lean:83  baGbyZeta_holds Graph/BAAuxGraph2B.lean:623
baEntryPsi_holds Graph/BAAuxGraph2B.lean:817  baGbEXPav_holds BA/GbEXPav.lean:24  BAAnpAuxG Graph/BAAuxGraph2B.lean:865
baClaimSize Graph/BASizeClaim2.lean:473  baKBound_E Graph/BASizeClaim.lean:410  BAAtom_decay_E Graph/BAAtom2.lean:537
BASizeClaim_theta_decay Graph/BASizeClaim.lean:241  BAExp14d_dataT Graph/BAExp14d.lean:60  BAExp14d_val_scale Graph/BAExp14d.lean:111
BAExp14a_slc Graph/BAExp14aB.lean:698  BAExp14a_int_slice Graph/BAExp14aB.lean:702  BAExp14a_prec_integral Graph/BAExp14a.lean:163
BAExp14a_det_iff Graph/BAExp14a.lean:58  BAExp14a_X_eq Graph/BAExp14aB.lean:188  BAExp14a_G_le Graph/BAExp14a.lean:1273
BAExp14a_G_green Graph/BAExp14a.lean:1245  BAExp14a_eventual_scalars Graph/BAExp14aB.lean:1138  BAExp14a_cont_G Graph/BAExp14aB.lean:791
BAExp14a_cont_lwG Graph/BAExp14aB.lean:685  ba_G_data BA/GreenLDE.lean:55  BAflow_real BA/GreenSchur.lean:59
BAflow_lam0_window BA/GreenSchur.lean:72  ba_fxyPow_integral_eq Graph/BALocReg1B.lean:294  BAExp14c_eta_le_one Graph/BAExp14c.lean:712
lwXiRad_holds Graph/AuxGraph2.lean:1241  lwMoment_anp_arith Graph/LWMoment.lean:998  lwMoment_near_arith Graph/LWMoment.lean:1610
lwMoment_rad Graph/LWMoment.lean:1630  lwMoment_phi_facts Graph/LWMoment.lean:409  lwMoment_CS Graph/LWMoment.lean:1461
lwMoment_sum_det Graph/LWMoment.lean:126
```
### Targets 1-4 extracted by script (`python3 extract2.py`, signatures; defs with body)
```lean
def LWfg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, if α = x ∨ α = y then (0 : ℂ) else
    ∑ β, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (STblk sz n α) (STblk sz n β)) * C.GM n t ω β β * C.G n t ω x α * C.G n t ω α y
theorem LWfg_bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    LWfg (bandFM sz E) n t ω x y = LWf sz n (E n) t ω x y :=
theorem LWfg_baFMz {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    (t : ℂ) * LWfg (baFMz sz z) n t ω x y =
      fxyVal (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData x y :=
def LWMomentG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (p : ℕ), 2 ∣ p → ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ),
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
          ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
            ∀ (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
              LWAssmgL (mk sz z) (law sz) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
              PrecL sz (law sz) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
                (fun n q _ => ∫ ω, ‖LWfg (mk sz z) n (t n) ω q.1 q.2‖ ^ p ∂(law sz))
                (fun n q _ => (((mk sz z).eta n (t n))⁻¹ * Φ n 0 *
                  Φ n (c * ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ))) ^ p)
theorem LWMoment_iff_bandPin (d : ℕ) : LWMoment d ↔ bandPin LWMomentG d :=
abbrev BALWMoment : ℕ → Prop := baPin LWMomentG
theorem ba_localregularX_holds : ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col) :=
def BALWMomentOfAnp (d : ℕ) : Prop := BAAnpAuxG d → BALWMoment d
theorem baLWMoment_of_anp
    (hb : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) :
    ∀ d : ℕ, BALWMomentOfAnp d :=
```
### Statement identity with the check file (script diff up to the name and the unfolding of `LWfg`)
`stmtcheck.lean` = `import RBM3D.Graph.BAMomentGenB` + Part 2 of `docs/tickets/checks/T2470-check.lean` verbatim + these lines; `lake env lean stmtcheck.lean`: exit 0, 0 errors
```lean
example : T2470_LWfgBand := fun {d} sz E n t ω x y => LWfg_bandFM sz E n t ω x y
example : T2470_LWMomentG = @LWMomentG := rfl
example : T2470_MomentBand := LWMoment_iff_bandPin
example : T2470_BALWMoment = BALWMoment := rfl
example : T2470_LocRegXHolds := ba_localregularX_holds
example : T2470_MomentOfAnp = BALWMomentOfAnp := rfl
example : T2470_Moment := @baLWMoment_of_anp
example : T2470_PathBinder = (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) := rfl
```
### Builds, axioms, instances, clash, diff
```
$ lake build RBM3D.Graph.BAMomentGen RBM3D.Graph.BAMomentGenB 2>&1 | tail -1
Build completed successfully (4061 jobs).
$ lake build | grep 'Build completed'   (whole library, run before the `date -u` of 21:03:18 UTC; `#assert_rbm_axioms` passes; RBM3D.lean has the two import lines)
Build completed successfully (4305 jobs).
$ lake env lean axsum.lean   (#axsummary over all declarations of the two modules; `#print axioms` of the 8 targets, uniq -c)
declarations of the two modules: 85; axioms used (union): [propext,  Classical.choice,  Quot.sound]; declarations with other axioms: 0 
   8 [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2470 | tail -4
 RBM3D.lean                    |    2 +
 RBM3D/Graph/BAMomentGen.lean  | 1549 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Graph/BAMomentGenB.lean |  847 ++++++++++++++++++++++
 3 files changed, 2398 insertions(+)
$ for b in all 473 other refs: git grep -l -E '\b(LWfg|LWfg_bandFM|LWfg_baFMz|LWMomentG|LWMoment_iff_bandPin|BALWMoment|BALWMomentOfAnp|baLWMoment_of_anp|ba_localregularX_holds|BAMomentGen_\w*)\b' $b -- 'RBM3D/*.lean' RBM3D.lean
(no output; `git ls-tree -r --name-only main | grep -c BAMomentGen` = 0)
$ grep -nE 'sorry|admit|native_decide|^axiom|^structure|^inductive' A B
(no output)
```
Instances (compiled, same file as the target): A:1528-1549 `bandPin LWMomentG 3` from `lwMoment_holds 3` (target 2); target 3 at `p = 2, c = 1/4, K0 = 2, d = 3, D = 10`; target 1 (b) and (a) at `sz0`, `n = 0`, `t = 1/2`,
`x = 0`, `y = 1`. B:840: the same target 3 instance with `outs ++ errs ≠ []` (`BAMomentGen_lists_nonempty`). Target 4, B:471: `example (hb) (hAnp : BAAnpAuxG 3) (hI : STInitialGT2gL ..) (hL : LWLoop2gL ..) : ∃ c > 0, PrecL sz0 μ0 ..`
applies `baLWMoment_of_anp hb 3 hAnp` at `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ = Φ ≡ W^{-1/2}`, `C₁ = C₂ = 2`, `C₃ = 1`, `Cc ≡ 1`, `p = 2` with all deterministic hypotheses discharged (window, class,
`(eq:Psi)` by `BAMomentGen_psiAll0`, `flow_sz0`, `half_lt_t0`); left as hypotheses: the path binder, `BAAnpAuxG 3`, `STInitialGT2gL`, `LWLoop2gL`.
Ports: none from RBM1D/RBM2D (not read); twins of RBM3D's band `Graph/LWMoment.lean` and copies inside RBM3D (`BAMomentGen_svar0/_relax/_consts` from `baGtoAGT_holds`, `BAMomentGen_X_le` from `BAExp14a_X_le`).
### Narrative
- Route as in the ticket (band `lwMoment_holds` proof in new files, order A -> B). Changes of route: `baAuxNested_holds` is not used (`BAAnpAuxG` is stated for `P.g.auxVal` directly, so the nested graph
  is not needed); the private (1)-(5) composition helper is inlined as `h15` in `baLWMoment_of_anp` (`BALocRegConcl` (a), (c) with `baLocReg15_holds hb p P0 hP0 _ Q hreach`); `baStart_nM_le`,
  `baClaimSize_E` are not needed (`BAMomentGen_pval_claim` uses `baClaimSize` with the kernel bounds of `BAMomentGen_consts`).
- Preflight items realised: F1 `ρ = (2K+1)(log W)²`, `R = K (log W)²` (`BAMomentGen_prec_anp`: `ρ - 2R = (log W)²`, `baGbyZeta_holds` separation); F2 tail exponent `c (log W)²/2`, `K` only fixes the far set;
  F4 `BAMomentGen_consts`; F3 thresholds occur only inside `∀ᶠ n`. The instance data of (a) (ii) are used unchanged.
- F5 closed (B:492-836): `BAMomentGen_lists_nonempty : BALocRegConcl 2 c K0 3 D outs errs → outs ++ errs ≠ []`. With empty lists (d) gives `∫ |f_{xx}|² dPF = 0` at `d = 3`, `L = 3`, `W = 2`, `g₀ = 0`, `E = 0`, `t = 1/4`,
  `m = i` (`BAMomentGen_selfI`); at `ω₀ = 2 P_σ` (`σ = Fin.rev` on the offset of each block, so `X(ω₀)` is supported in blocks) `G = a + b P_σ` (`BAMomentGen_resolvent`) and `f_{xx}(ω₀) = t (a - i) b² ≠ 0` (`BAMomentGen_pt_fxy`,
  `BAMomentGen_num_F`); `f_{xx}` is continuous, `PF` charges every open set around `ω₀` (`BAMomentGen_PF_pos`, zero-variance coordinates of `ω₀` are `0`), integrability from `BALvl1A_integrable_val`.
- Premise scan (`Test/Axioms.lean:390-445`): a first build failed the audit with `LWAssmgL`, `LWLoop2gL`, `BAAnpAuxG`, then `LWXigL` (theorem hypotheses). Fixed without touching the registry: the lemmas take
  `LWAssmgL` unfolded (`hassm`, `LWLoop2gL` as `PrecL`), `lem:Anp` instantiated at the data and one graph (`hAnpQ`/`hAnpL`, `LWXigL` unfolded); in the two files `LWAssmgL` is only in `LWMomentG`, `BAAnpAuxG` only in
  `BALWMomentOfAnp` (and the instance), `LWLoop2gL` only in the instance `example`. The full `lake build` then passes. Target 4 is a conditional adapter (hypotheses: the path binder, and `BAAnpAuxG d` inside the statement def),
  not the unconditional `lem:LW_moment` at BA (CLAUDE.md §5.6).
- `LWMoment_iff_bandPin` is not definitional: it rewrites `LWfg_bandFM` under the integral (`simp only [LWfg_bandFM]`). The expansion identity moves `BALocRegConcl` (d) from `PF d L W 0` to the sample space
  with `BAExp14a_int_slice` (continuity of `fxyVal`, of graph values and of lists: `BAMomentGen_cont_*`); integrability of the summands is a hypothesis of `BAMomentGen_expand`, supplied for large `n` by the envelope.
## (c) Verified Mathlib names
`continuous_list_prod`, `continuous_list_sum`, `continuous_finsetSum` (not `continuous_finset_sum`: deprecated), `integral_complex_ofReal`, `integral_add`, `integral_const_mul`, `integral_eq_zero_iff_of_nonneg`, `Integrable.const_mul`,
`Integrable.add`, `Integrable.norm`, `Filter.eventually_all_finite`, `List.finite_toSet`, `List.le_sum_of_mem`, `List.countP_le_length`, `Matrix.one_apply_eq`, `Matrix.one_apply_ne`, `Matrix.inv_eq_right_inv`, `Measure.infinitePi_pi`,
`gaussianReal_zero_var`, `gaussianReal_absolutelyContinuous'`, `isOpen_pi_iff`, `Finset.prod_ne_zero_iff`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Int.toNat_of_nonneg`, `inv_le_iff_one_le_mul₀'`, `Nat.le_ceil`, `pow_le_pow_of_le_one`.
Verified absent: `integral_list_sum` (grep in `Mathlib/MeasureTheory/Integral/Bochner/*.lean`: none; own `BAMomentGen_integral_list_sum`); `if_pos`/`if_neg`/`if_true` are deprecated here.
## (d) Open issues and paper-delta candidates
1. Target 4 keeps the path binder until T2469 (state `blocked` at 20:34:35) and `BAAnpAuxG` (L3d1) as the antecedent of `BALWMomentOfAnp`; `STInitialGT2gL`, `LWLoop2gL` stay hypotheses of the instance.
2. Paper-delta candidates: none new. Reading: the BA `f_{xy}` carrier is `(fxyG_sum)` (`7_8:31-34`) with `Ǧ = G - M` (`M` non-scalar) and `S^{(B)} = I` (B:288); the paper's BA proof is a sketch (B:408-416),
   so `t · LWfg = fxyVal` at `BAlwData` (target 1 (b)) is Lean's bridge. F1 and F2 are proof choices and change no statement.
