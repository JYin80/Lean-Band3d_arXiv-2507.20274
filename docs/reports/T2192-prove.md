Prover model: claude-sonnet-5-5
## Top notice: split count against DECISIONS §9 O2 (25 / 40 / 50), script `split.py`, portmap P.5, and verdict
| ticket | file | role | central lines (lo-hi) |
|---|---|---|---|
| MA-01 | `RBM3D/Endpoints.lean` | prover-hard | 760 (610-990) |
| MA-02 | `RBM3D/Main/ZTransfer.lean` | prover | 540 (430-700) |
| MA-03 | `RBM3D/Main/FixedZ.lean` | prover | 830 (660-1080) |
| MA-04 | `RBM3D/Main/ZNet.lean` | prover-max | 1030 (820-1340) |
| MA-05 | `RBM3D/Main/QUEFromQDiff.lean` | prover-hard | 1440 (1160-1880) |
| MA-06 | `RBM3D/MainTheorems.lean` | prover | 340 (270-440) |
COUNT: 6 tickets (5 if MA-06 merges into the final cleanup ticket, DECISIONS §45 O5; 7 if MA-05 splits at its carrier-free boundary), total central 4940 lines (lo 3950, hi 6430); 6 < 25: no threshold of §9 O2 is reached. Lines are estimates from measured probe sections and RBM2D line ranges.
VERDICT: all six targets delivered (probe compiled, three standard axioms, instances, coverage, split). Not compiled by design, owed by the split: `MANetLoc`, `MANetQD` (MA-04), `MAQUE` (MA-05); `∀ d, UNMLOut d` is owed by ST-6.
## (a) Math preflight — Mon Oct  5 15:42:24 UTC 2026

Notation: `d=3`, `N=(WL)^d`, `η=Im z`, `B_η=𝓑_{η,0}`, `θ=(1-t₀)/η`, `t₀=lemT z=|m|²`, `g=ilambda`. Paper lines are `1_2:` (`paper/tex/1_2_Intro_model_result.tex`). "Derived" = my own computation from the stated facts, to be proved in Lean; "numeric" = the script grid below, not a proof.

### (i) Exponent table

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `(𝔠,𝔡)` | `sz0`: `(1/6,1/10)` (`sz0_admissible`); second sequence `sz1`: `L=n+3, W=(n+2)^6, 𝔠=1/4, 𝔡=1/5`, `g=W^{-1.3}` (lower edge of `(eq:WO)`) or `g=5=𝔡⁻¹` (upper edge) | script A: `W≥N^𝔠`, `W^{-d/2+𝔡}≤g≤𝔡⁻¹` at every listed `n` |
| 2 | `Prec`↔`W^τ` (`StochDomAt` `Defs/StochDomAt.lean:61`: union inside, `∀τ,D>0`, scale `N^{-D}`) | `Prec(τ')⇒` explicit `W^τ` with `τ'=𝔠τ` (`N^{τ'}≤W^{τ'/𝔠}`, `size_rpow_le_W_rpow`); explicit `⇒Prec(τ')` with `τ=dτ'` (`W^τ≤N^{τ/d}`, `W_rpow_le`); both ∀τ>0, so the two forms are equivalent, same `N^{-D}` | A, `τ=0.1`: `0.11≤0.15≤0.21` (`sz0 n=0`) |
| 3 | `(eq:BtBt)` at `t₀` | `1-t₀=η/(Im m+η)` exactly, so `θ=1/(Im m+η)∈[1/2, 1/Im m]` (derived: `|m|<1`, `η≤1`); `W^{-d}B_{t₀,K}/𝓑_{η,K}∈[min(1,θ⁻¹),max(1,θ⁻¹)]` (derived; `K` in blocks, `(Wk+W)^{d-2}=W^{d-2}(k+1)^{d-2}`). Merged route: `lemma28_quant` (`Semicircle.lean:359`) gives `t₀≥1/16`; `st5_Bctl_le_one` (`Induction/Step5Kit.lean`) derives `(1/16)η≤1-t₀` (the identity gives the better `η/2`) | numeric (κ=0.1): `θ∈[0.618,3.203]`, `R∈[0.312,1.618]⊂[0.295,2]`; `min t₀=0.245≥1/16` (C, B) |
| 4 | `zdistInf≤zdistD≤d·zdistInf` (T2001e) | `((K_D+1)/(K_∞+1))^{d-2}≤d^{d-2}=3`; one constant, absorbed by `W^{τ}` (eventually `W^{τ/2}≥3`) | D: max ratio `2.33` (L=4), `2.5` (L=6) `<3` |
| 5 | additive `W^{-D}` of `(Eq:Gdecay)` (`1_2:1205`, `STDecay` `Induction/Defs.lean:121`) | the QDiff bound is `W^τ[(B^{1/5}B_{η,W|a-b|})∧B²]`, `B²≥(Nη)^{-2}≥N^{-2}`, and `N≤W^{1/𝔠}`: `W^{-D}≤N^{-2}` iff `D≥D₀=2/𝔠` (`D₀=12` at sz0, `8` at sz1); `D` is a free ∀ in `STDecay`. `(Gt_bound)` (`ML:GtLocal`, `1_2:1217`) has no additive term | E: `log10(N^{-2}/W^{-D₀})≥0.75` |
| 6 | `z`-net (derived) | direct parametrization, no probability: `|G_xy(z)-G_xy(z')|≤|z-z'|/(ηη')`, `|m-m'|≤|z-z'|/(ηη')`; `‖Θ(ξ)‖_op≤(1-|ξ|)⁻¹` (Neumann series, `‖SB‖=1`; entries `≤‖·‖_op`), `|ξ|=t₀`, `1-t₀≥η/16` (merged constant), so `‖Θ‖≤16/η`, `Θ-Θ'=Θ(ξ'-ξ)SΘ'`: Lip(G-parts)`≤8N³`, Lip(`m²Θ/W^d`)`≤544N⁴` (`η_min≥N^{-1+ε}`, `ε>0`); mesh `N^{-7}`, `|net|≤25N^{14}`, error `≤552N^{-3}≤N^{-2}/2` for `N≥1089`; target RHS `≥B²≥N^{-2}`, shifts `η→η'` change `B` by a factor in `[1/2,2]`; per-point probability `N^{-(D+15)}` | F: err `5.9e-17≤1.1e-13` at `N=2.1e6` |
| 7 | `(eq:ukx)` `1_2:399` | `η=N^{-1+ε}`, `ε=τ/2` (the paper's `η=N^{-1+τ}` gives `ψ²≤2N^{-1+τ}`, constant not absorbed: candidate `T2192a`); `M=mI` (`1_2:343`); `Im G_xx≤Im m+(W^{τ_L}B)^{1/2}`, `B≤W^{-2𝔡}+N^{-ε}`; `τ_L=min(𝔡,dε/2)`, need `W^{τ_L}B≤1` and `N^{τ-ε}≥2` (`N≥2^{2/τ}`) | G: `max W^{τ_L}B=0.876`; `2η≤N^{-1+τ}` true at all 7 (tightest `1.97e-6≤2.04e-6`, `sz0 n=0`) |
| 8 | QUE window (`1_2:408`) | `η_Q=W^{-ε₀}gW^{d/2}/N`; `η_Q∈𝐃_{κ,ε_Q}` with `ε_Q=𝔠(𝔡-ε₀)∈(𝔠𝔡/2,𝔠𝔡)`; `η_Q≤1` (`η_Q≤𝔡⁻¹W^{-ε₀-d/2}L^{-d}→0`) | H: `lg(η_Q/N^{-1+ε_Q})≥0.01` (tightest, `sz1lo n=0`) |
| 9 | `(eq:BetaK)` `1_2:514` | `η_Q≤g²/L^d` iff `g≥W^{-d/2-ε₀}`; from `(eq:WO)` the slack is the factor `W^{𝔡+ε₀}`; then `B_{η_Q,0}∈[1,2]·(Nη_Q)^{-1}`; `(Nη_Q)^{-1}≤W^{ε₀-𝔡}`, `(g²W^d)^{-1/5}≤W^{-2𝔡/5}` | H: `lg(g²/L^d/η_Q)≥0.36`; I: ratio `∈[1.0000,1.3259]` |
| 10 | `(ssfa2_deter)` `1_2:531` | three terms `N^{-2}W^τ(W^{-𝔡+ε₀}+W^{-2𝔡/5}+W^{-2ε₀})`; `-𝔡+ε₀≤-2𝔡/5` iff `ε₀≤3𝔡/5` (slack `𝔡/10` at `ε₀=𝔡/2`); third term is exact: `η_Q²W^{-d}g^{-2}=W^{-2ε₀}N^{-2}` | H: identity dev `≤4e-16` |
| 11 | Markov, `(Meq:QUE)` `1_2:411-415` | event `≥W^{-c}/N` for `ψ_i^*(E_a-N⁻¹)ψ_j`, factor `N²W^{2c}`; bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}`, non-trivial iff `c<ε₀∧𝔡/5`; UN choice `ε₀=𝔡/3, c=𝔡/6`: `-𝔡/15+τ` (`un_que_exponent`, `Universality/Pins.lean:894`) | slack `2(ε₀∧𝔡/5-c)`; `1/150-τ` at `𝔡=1/10` |
| 12 | `Θ`-differences (QUE) | `max|Θ^{(σσ')}_{ab}-Θ^{(σσ')}_{ab'}|≤2C₈g^{-2}`, deterministic, no `≺`, no log: `Θ_{ab}-Θ_{ab'}=Θ0_{ab}-Θ0_{ab'}` (`Theta0_apply`, `Propagator/Basic.lean:225`: `Θ0=Θ-(L^{2d})⁻¹ΣΣΘ`, constant matrix); `Prop8ZeroMode d (𝔡⁻¹) κ'` (`prop5to8_holds`, `Prop6Hold.lean:433`; no `L^τ` loss, unlike `ThetaZeroMode`) gives `|Θ0(0,a)|≤C₈(g²+1-t)⁻¹≤C₈g⁻²`; applied at `t=t₀`, `m'=m/|m|` (`‖m'‖=1`, `t·m'·conj m'=t₀`, `t m'²=m²`), `g≤Λ=𝔡⁻¹`, `κ'≤Im m'`. Rows `a,b` reduce to row `0` by `Theta_apply_add_right` (`Propagator/Basic.lean:154`, `Θ(a+c,b+c)=Θ(a,b)`, hypothesis `‖SB‖=1`; `norm_SB`, `Props4.lean`), so no `Θ0`-invariance lemma is needed | numeric `min Im m'=0.312` (κ=0.1, hence `κ'=1/4`); the analytic bound `Im m≥c_κ` on `𝐃_{κ,ε}` is not checked here |

### (ii) One nondegenerate instance, with script

Instance: `d=3`, `sz0`, `𝔠=1/6, 𝔡=1/10`, `n=0`: `L=4, W=32, N=2097152, g=1/64` (`sz0_values`); `κ=1/10`, locSC/QDiff `ε=1/20`, `τ=1/10`, `D=2` (net `D'=17`); QUE `ε₀=1/30, c=1/60`, `τ=1/10`, `E∈{±1.9,0}`, `a=0`, `A={0}`; `z=E+iη_Q`, `η_Q=1.2e-6`. Every constraint of rows 1-12 holds at `n=0,1,9` of `sz0` and at the edge sequences `sz1lo, sz1up` (`n=0,9`), and the large-`n` tendency is monotone in every row. Hypotheses of the MA pins: `Admissible` (all of row 1); `UNMLOut` is owed by ST-6, a hypothesis, not external. The only external input on the final shape, `UNL32` (borrowed), is not a hypothesis of any band pin: it enters only through `UNBUniv`; its limit computation is `un_L32_arith` (`Universality/Pins.lean:307`, instance at `:1555`, T2162), not repeated here.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2192/pre2.py` (stdlib only, no Lean). Output, verbatim:
```
A  Prec scale (tau=0.1), log10: c*tau*N <= tau*W <= tau/d*N ; W>=N^c, WO window, lam<=1/dd
 sz0 n=0: L=4 W=32 N=2.10e+06 lam=1.56e-02 ok=True  0.11<=0.15<=0.21
 sz0 n=1: L=8 W=1024 N=5.50e+11 lam=2.44e-04 ok=True  0.20<=0.30<=0.39
 sz0 n=9: L=40 W=3200000 N=2.10e+24 lam=1.56e-08 ok=True  0.41<=0.65<=0.81
 sz1lo n=0: L=3 W=64 N=7.08e+06 lam=4.49e-03 ok=True  0.17<=0.18<=0.23
 sz1lo n=9: L=12 W=1771561 N=9.61e+21 lam=7.54e-09 ok=True  0.55<=0.62<=0.73
 sz1up n=0: L=3 W=64 N=7.08e+06 lam=5.00e+00 ok=True  0.17<=0.18<=0.23
 sz1up n=9: L=12 W=1771561 N=9.61e+21 lam=5.00e+00 ok=True  0.55<=0.62<=0.73
C  theta=(1-t0)/eta (=1/(Im m+eta)), grid |E|<=2-k, eta in [1e-6,1]
 k=0.1: theta in [0.618,3.203], 1/min Im m=3.391; min t0=0.245; max|lemE|-(2-k)=0e+00; min Im m'=0.312; id err=3e-10
 k=0.5: theta in [0.618,1.512], 1/min Im m=2.362; min t0=0.297; max|lemE|-(2-k)=0e+00; min Im m'=0.661; id err=4e-10
B  (eq:BtBt) R=W^-d B_(t0,K)/calB_(eta,K), K<=3, 7 seqs x 3E x 3eta: R in [0.312,1.618]  (bound [1/3.391,2]=[0.295,2])
D  max (zdistD+1)/(zdistInf+1) on Z_L^3, L=4,6: [2.3333333333333335, 2.5]; ^(d-2) <= d^(d-2)=3
E  W^-D0 <= N^-2, D0=2/c: min over seqs of log10(N^-2/W^-D0) = 0.75 >=0
F  net: mesh N^-7, |net|<=25N^14, Lip(G-part)<=8N^3, Lip(det)<=544N^4: err=(8N^3+544N^4)N^-7=5.9e-17 <= N^-2/2=1.1e-13 at min N=2.10e+06; smallest N with err<=N^-2/2: 1089
G  (eq:ukx) eps=tau/2=.05, tauL=min(dd,d*eps/2): W^tauL*B_(eta,0)<=1 and 2eta<=N^(-1+tau) at all 7 seqs: True; max W^tauL*B=0.876
H  QUE, 3 choices (e0,c)=(dd/3,dd/6),(.49dd,.99min(.49dd,dd/5)),(.01dd,.99*.01dd); eps=c(dd-e0)
 sz0 n=0: ok=True lg(eta_Q/N^(-1+eps))>=0.32 lg(lam^2/L^d/eta_Q)>=0.45 3rd-term dev=2e-16 slack(2e0^2dd/5)-2c>=2e-05
 sz0 n=1: ok=True lg(eta_Q/N^(-1+eps))>=0.66 lg(lam^2/L^d/eta_Q)>=0.91 3rd-term dev=2e-16 slack(2e0^2dd/5)-2c>=2e-05
 sz0 n=9: ok=True lg(eta_Q/N^(-1+eps))>=1.43 lg(lam^2/L^d/eta_Q)>=1.96 3rd-term dev=4e-16 slack(2e0^2dd/5)-2c>=2e-05
 sz1lo n=0: ok=True lg(eta_Q/N^(-1+eps))>=0.01 lg(lam^2/L^d/eta_Q)>=0.36 3rd-term dev=4e-16 slack(2e0^2dd/5)-2c>=4e-05
 sz1lo n=9: ok=True lg(eta_Q/N^(-1+eps))>=0.08 lg(lam^2/L^d/eta_Q)>=1.26 3rd-term dev=2e-16 slack(2e0^2dd/5)-2c>=4e-05
 sz1up n=0: ok=True lg(eta_Q/N^(-1+eps))>=3.06 lg(lam^2/L^d/eta_Q)>=3.41 3rd-term dev=2e-16 slack(2e0^2dd/5)-2c>=4e-05
 sz1up n=9: ok=True lg(eta_Q/N^(-1+eps))>=8.90 lg(lam^2/L^d/eta_Q)>=9.00 3rd-term dev=2e-16 slack(2e0^2dd/5)-2c>=4e-05
I  B_(eta_Q,0)*N*eta_Q in [1.0000,1.3259] subset [1,2] (e0=dd/3)
   dispatcher sz0 n=0 e0=dd/3: eta_Q=1.20e-06 N^(-1+eps)=5.61e-07 lam^2/L^3=3.81e-06 eps=0.01111 final exp(-2dd/5+2c)=-0.00667
J  eps=1: N^(-1+1)=1.0 (domain {eta=1}); kappa=2: 2-kappa=0; A=univ: |1-W^dL^d/N|=0 < W^(d-c)L^d/N=0.944; A=empty: (0>=0)=True
```
Extreme inputs (line J): `ε=1` gives `{η=1}` and `κ=2` gives `{E=0}`, both nonempty; the domain is empty only for `ε>1` or `κ>2` (the ticket's "`κ≥2`, `ε≥1`" is off at equality). `A=univ`: the event is empty (`0<W^{d-c}L^d/N`); `A=∅`: the event is `{0≥0}`, so (Meq:QUE2) needs `A≠∅` (T2001f).

### Verdicts
- Target 1 (endpoint pins, form decision): PASS. `Prec` and explicit `W^τ` are equivalent (row 2); (Meq:QUE) has a `W`-power probability, not `≺`, so only locSC/QDiff face the form choice.
- Target 2 (assembly chain): PASS. (a),(b): rows 3-4; (c): net is deterministic (row 6), no `RegionUnif` port needed on this count; (d): row 7, no net once `∩_z` is inside; (e): row 12, all inputs merged (`prop5to8_holds`, `Theta_apply_add_right`); only the analytic bulk bound `Im m≥c_κ` for the hypothesis `κ'≤Im m'` is to be located.
- Target 3 (interfaces): PASS at the level of mathematics (same constants `W^τ B_{η,0}`, `N^{-D}`, `ε₀`, `c` as `UNLocAvgBand`, `UNQueBand`); `UNMLOut` is a hypothesis.
- Target 4 (exponent table, skeleton, instances): PASS; no row fails, tightest slack rows 7, 8, 11 above.
- Target 5, 6 (split, coverage): nothing to check in preflight beyond the above; no hypothesis set fails. No BLOCKED input.
- Candidates: `T2192a` (eq:ukx needs `η=N^{-1+τ/2}`); `T2192b` (the ticket's empty-domain cases are `κ>2`, `ε>1`).

## (a′) Preflight corrections — Mon Oct  5 18:08:33 UTC 2026
None changes a verdict. (a) is unchanged above; its tags `T2192a` (eq:ukx constant) and `T2192b` (empty domain) are `T2192c` and `T2192f` in (d).
1. Row 7 states `ε = τ/2`; the compiled `decol_scalars`, `decol_of_locSC` use `ε = min(τ/2, 1/2)`, so that `η = N^{-1+ε} ≤ 1` for every `τ > 0` (equal for `τ ≤ 1`).
2. Row 5 asks `D ≥ 2/𝔠` (for `W^{-D} ≤ N^{-2}`); the compiled `QDiffFixed_of_ML` needs only `D = 6/(5𝔠)`: the additive `W^{-D}` is absorbed into the first option `𝓑_{η,0}^{1/5}𝓑_{η,K}` only (`floor_X`), with `min (2aX, aY) ≤ 2a min (X, Y)` (`qd_core`).
3. Row 12 citations: `Theta0_apply` is `RBM3D/Propagator/Basic.lean:229` (225 is `Theta0`); `norm_SB` is `RBM3D/Defs/Block.lean:136` (not `Props4.lean`).
4. Row 12, open item `Im m ≥ c_κ` on `𝐃_{κ,ε}`: `im_msc_ge` (`√(κ(4-κ))/8 ≤ Im m`) is compiled.
5. Row 6 and verdict 2(c): "no `RegionUnif` port" holds for the Gaussian tail event and the `(E,t)`-net; the abstract union-bound core `regionUnif_core` (RBM2D `Main/RegionUnif.lean:85`, about 150 lines) is ported into MA-04 (portmap P.5).

## (b) Script output. Probe `RBM3D/Probe/T2192Pins.lean` (2492 lines, branch `t/T2192`, head `97d958e`); companion `docs/reports/T2192-portmap.md` (script output: P.1 statements, P.2 diffs and copies, P.3 chain pins, P.4 d=2 facts, P.5 split, P.6 interfaces, P.7 coverage, P.8 exponent table, P.9 hygiene and names)
```
$ git log --format=%h 76b840e..HEAD; git diff --name-only $(git merge-base main t/T2192) t/T2192; git merge-base --is-ancestor ...
97d958e 6c7e6d4 8bfa71f ce5bfa3 e26d757 48bc7a3 d23c3b3 ba84f95 
RBM3D/Probe/T2192Pins.lean
fdbb6f0 (T2187: merge UN-01b Universality/PinsK) is an ancestor of the base 76b840e
ae63e74 (T2189: merge BA-D1a + BA-D2 BA/MFixedPoint) is an ancestor of the base 76b840e
```
```
$ lake env lean RBM3D/Probe/T2192Pins.lean; lake build RBM3D.Probe.T2192Pins; grep -E "T2192Pins|error|Build completed" <build output>
exit=0 bytes=0
exit=0
Build completed successfully (3996 jobs).
```
```
$ python3 axioms.py   # #print axioms of every public declaration of the probe, one each
declarations printed: 146  lines of axiom output: 146
146 [propext, Classical.choice, Quot.sound]
other output lines: 0
```
```
$ python3 axioms_key.py; grep -cE 'sorry|admit|native_decide|^axiom ' RBM3D/Probe/T2192Pins.lean
#print axioms of the 29 key declarations: 29 printed; on exactly [propext, Classical.choice, Quot.sound]: 29; others: []
names: decol, locSC, QUE, QDiff, BUniv, calB, calB_zero_eq_Bctl, explicit_of_stochDomAt, prec_of_explicit, det_of_prec, locSC_to_UNLocAvgBand, QUE_to_UNQueBand, locSCFixed_of_ML, QDiffFixed_of_ML, fixed_of_ML, decol_of_locSC, thetaDiff, btBt, zTrace, zProfile, band_endpoints_of_pins, final_shape, Inst.inst_decol, Inst.inst_locSC, Inst.inst_QUE, Inst.inst_QDiff, Inst.inst_BUniv, Inst.inst_bridge_loc, Inst.inst_bridge_que
0
```
```
$ python3 stmts.py --compact decol locSC QUE QDiff BUniv calB calB_zero_eq_Bctl explicit_of_stochDomAt prec_of_explicit QDiffFixed_of_ML fixed_of_ML locSC_to_UNLocAvgBand QUE_to_UNQueBand   # target statements extracted from the file; `-- :a-b` = lines of RBM3D/Probe/T2192Pins.lean
def decol : Prop :=  -- :164-167
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def locSC : Prop :=  -- :171-175
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def QUE : Prop :=  -- :181-190
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
        (∀ a : Zd d (sz.L n),
          Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ) ∧
        (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
          Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ)
def QDiff : Prop :=  -- :196-205
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      (Sizes.seqP sz {ω | qd1Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, sz.locDomain κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im
abbrev BUniv : Prop := UNBUniv  -- :208-208
def calB (sz : Sizes d) (n : ℕ) (η K : ℝ) : ℝ :=  -- :57-59
  (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) +
    (((sz.size n : ℕ) : ℝ) * η)⁻¹
theorem calB_zero_eq_Bctl (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) :  -- :230-231
    calB sz n η 0 = sz.Bctl n (1 - η) := by
theorem explicit_of_stochDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)  -- :375-380
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → Ω → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : StochDomAt P sz.size ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, P {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D)) := by
theorem prec_of_explicit (hd : 0 < d) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}  -- :400-405
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (h : ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))) :
    sz.Prec ξ ζ := by
theorem QDiffFixed_of_ML (hML : ∀ d, UNMLOut d) : QDiffFixed := by  -- :1475-1475
theorem fixed_of_ML : MAFixed := fun hML => ⟨locSCFixed_of_ML hML, QDiffFixed_of_ML hML⟩  -- :1594-1594
theorem locSC_to_UNLocAvgBand : locSC → UNLocAvgBand := by  -- :2055-2055
theorem QUE_to_UNQueBand : QUE → UNQueBand := by  -- :2066-2066
```
```
$ python3 inst_extract.py --compact inst_decol inst_locSC inst_QUE inst_QDiff   # compiled nonempty instances at d = 3 on sz0 (each pin is a hypothesis of its example)
theorem inst_decol (h : decol) :  -- :2128-2131
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)
theorem inst_locSC (h : locSC) :  -- :2134-2139
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
theorem inst_QUE (h : QUE) :  -- :2142-2151
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
      (∀ a : Zd 3 (sz0.L n),
        Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) ∧
      (∀ A : Finset (Zd 3 (sz0.L n)), A.Nonempty →
        Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E A (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (by norm_num) (1 / 30) (1 / 60) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem inst_QDiff (h : QDiff) :  -- :2154-2164
    ∀ᶠ n in atTop,
      (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
```
Other compiled instances, edge and extreme-input theorems of the same file (script grep): inst_BUniv inst_bridge_loc inst_bridge_que inst_final_shape inst_decol_of_locSC inst_locSCFixed inst_QDiffFixed inst_zRange inst_btBt inst_zLocal inst_zAve inst_zTrace inst_zProfile szLo_admissible szUp_admissible inst_locSC_lo inst_locSC_up inst_QUE_up domain_extreme locBad1_empty_kappa im_mE_edge queDomain_edge que2BadMat_univ que2BadMat_empty_zero inst_thetaDiff inst_queDomain inst_decol_scalars inst_calB inst_distB_compare inst_BetaK inst_three_terms 
```
$ python3 clash.py | head -6; python3 clash_main.py | tail -3; grep -nE "^namespace |^end RBM|^end Inst" RBM3D/Probe/T2192Pins.lean   # name-clash grep of the new public names (outside Probe/); both matches are `private` declarations of merged files in other namespaces; every declaration sits in `RBM.Probe.T2192`
new public names in the probe: 146
CLASH zI
    RBM3D/Green/FlucVanish.lean:1355:private noncomputable def zI : ℂ := (1 / 2 : ℂ) + Complex.I / 2
CLASH zdistInf_zero
    RBM3D/Green/Pins.lean:1303:private theorem zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
names with a match outside Probe/: 2
    main:RBM3D/Green/Pins.lean:1303:private theorem zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
names with a match on main outside Probe/: 2
main has Endpoints.lean / MainTheorems.lean / Main/ : ''
RBM3D/Probe/T2192Pins.lean:46:namespace RBM.Probe.T2192
RBM3D/Probe/T2192Pins.lean:2112:namespace Inst
RBM3D/Probe/T2192Pins.lean:2490:end Inst
RBM3D/Probe/T2192Pins.lean:2492:end RBM.Probe.T2192
```
```
$ python3 cite_list.py | grep ...   # ports: `eventually_forall_of_sections` and `Gres_apply_self` are ported proofs, `im_identity` is re-derived; sources at RBM2D c9a24cf (the sections lemma itself comes from RBM1D `eventually_forall_of_forall_sequences`, RBM1D/Flow/EventuallyUniformBySequences.lean:25, commit d6add37)
RBM2D/Main/EndpointsFromSTO.lean:35  theorem EndpointsFromSTO_eventually_forall_of_sections {Z : ℕ → Type*} (hne : ∀ n, N
RBM2D/Main/ZRescale.lean:168  theorem ZRescale_im_identity {z : ℂ} (hz : 0 < z.im) :
RBM2D/Main/DecolFromLocal.lean:35  private theorem DecolFromLocal_green_apply_self (hψ : IsOrthoEigenbasis H μ ψ) {z : 
$ git -C ../RBM1D --no-optional-locks diff --stat d6add37 HEAD -- RBM1D/Flow/EventuallyUniformBySequences.lean
(no diff-stat line above = file unchanged since d6add37) RBM1D HEAD de0de42
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- <the 3 ported RBM2D files and RegionUnif.lean>
 RBM2D/Main/DecolFromLocal.lean   |  43 +-
 RBM2D/Main/EndpointsFromSTO.lean | 226 +---------
 RBM2D/Main/RegionUnif.lean       | 950 ---------------------------------------
 RBM2D/Main/ZRescale.lean         |  51 +--
 4 files changed, 47 insertions(+), 1223 deletions(-)
RBM2D HEAD 9e0f275
```
```
$ python3 coverage.py | grep ...; python3 copies.py | tail -4; python3 exptab.py | tail -1; python3 carrier.py | tail -1; python3 price.py | grep ...   # coverage over 1_2:250-669, copies of the frozen statements (lesson 26), exponent table against signatures, carrier pricing
labels scanned in 1_2:250-669 (comments stripped): 43; mapped: 43; unmapped (gaps): 0 []; Thm 2.7 bullets: 5; locations not found: 0 []
chain labels listed: 16; locations not found: 0
copies listed and verified by git show at the cited ref: 39; mismatches: 0 []
BAcalB (T2161:1483) and calB (probe) bodies identical after whitespace normalisation: True
  T2161 body: (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) + (((sz.size n : ℕ) : ℝ) * η)⁻¹
  probe body: (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) + (((sz.size n : ℕ) : ℝ) * η)⁻¹
rows checked: 15  failures: 0
carrier-free compiled lines: 675; band-specific compiled lines: 955; (declaration ranges incl. docstrings, excluding the instances section)
saving in lines, after a 25% instantiation overhead on the uncompiled part: 1068 of 3300 central (32%)
BA total (T2173 prove report, top line): 62 (61..66) if UN-25..52 are model-generic; cap 70 (DECISIONS 52, 57). Effect of the saving: 62 -> 61..62 (<= 1 ticket); the cap is not binding with or without it.
```
Narrative (the evidence is the script output above and the portmap; names are in the probe):
- Delivered: the pins `decol`, `locSC`, `QUE`, `QDiff` (Thm 2.1, 2.2, 2.3, 2.5), `BUniv := UNBUniv` (Thm 2.4), `calB` with `calB_zero_eq_Bctl`; Thm 2.7 is referenced through the BA names (portmap P.7, rows 37-48) and enters `final_shape` as an abstract `Thm27 : Prop`.
- Proved in the probe: the form bridges; the `zztE` transfer (`zRange`, `zGreen` = merged `Gt_lemT`, `zLocal`, `zAve`, `zTrace`, `zProfile`); `(eq:BtBt)` (`btBt`, constants `2` and `√(κ(4-κ))/8`; `calB_distB_compare`, the `zdistInf`/`zdistD` conversion, factor `d^{-(d-2)}`); the fixed-`z` statements from `∀ d, UNMLOut d` (`fixed_of_ML`); `decol_of_locSC`; `thetaDiff`; the QUE scalars (`queDomain`, `etaQ_le`, `calB_le_two_inv`, `que_three_terms`); both UN bridges; `band_endpoints_of_pins`, `final_shape`.
- Form decision: explicit `W^τ`, `N^{-D}` for all six results. The merged `Prec` is equivalent: `explicit_of_stochDomAt` (`Prec` at `𝔠τ` gives explicit at `τ`, any law, so also `seqP (sz.withLam 0)`) and `prec_of_explicit` (explicit at `dτ` gives `Prec` at `τ`). BA-M1..M3 may keep `Prec` inside and export the explicit form; `BAcalB` has the body of `calB` (`copies.py` lines above).
- Differences from the copies (portmap P.2: 39 copies, each checked by `git show`): T2001 has the same quantifier order and bounds on its own carrier, with the `ℓ¹` block distance where the freeze has `L^∞` (`distB`, as the merged `STLocalEntry`); RBM2D `Endpoints.lean` is pointwise in `z` with threshold `W^τ/√Meta` (the freeze: `∩_z` inside, `W^τ 𝓑_{η,|x-y|}`) and its QUE (window `N^{-1-τ}W^{2/3}`, bound `N^{-τ/6}`) is not comparable.
- Shapes: `∩_z` inside for `locSC` and the probability halves of `QDiff` (T2001b); `QUE` has `A ≠ ∅` (T2001f) and `N₀` uniform in `E, a, A`; the expectation halves of `QDiff` have `N₀` uniform over `𝐃_{κ,ε}` (`T2192a`); `(a,b)` of `(eq:diffu1,2)` are inside the probability (`T2192d`).
- The transfer swaps the loop indices: `W^{-2d} Σ_{x∈[a],y∈[b]} G_xy G^σ_yx = t₀ 𝓛^{(2)}_{(+,σ),(b,a)}` (`zTrace`), because `E_b` multiplies the column index of the first factor; RBM2D states its endpoint with `trGEGE`, where no swap shows. The profile is symmetric (`Theta_transpose`), so no statement changes (`T2192g`).
- Fixed `z`: the sections lemma is a verbatim port of RBM2D `EndpointsFromSTO_eventually_forall_of_sections`; `UNMLOut` is used at `t_n = lemT z_n` only, four of its five outputs (`STLmax` unused). `QDiffFixed_of_ML` needs both options of `qdBound` (`STDecay` with `D = 6/(5𝔠)`, `STLK` at `k = 2`), the floor `W^{-6/(5𝔠)} ≤ 𝓑_{η,0}^{1/5} 𝓑_{η,K}` and `W^{τ/2} ≥ 8`.
- Net `[net]`: deterministic resolvent net in the direct parametrization (`cont_green_diff`, Stieltjes `m`, Neumann series for `Θ`; the constants of (a) row 6 are numeric only). Of RBM2D `Main/RegionUnif.lean` (950 lines at `c9a24cf`, deleted at RBM2D HEAD, diff-stat above) only the abstract core `regionUnif_core` survives (about 150 lines); the Gaussian tail event and the `(E,t)`-net are not needed. Not compiled: MA-04, role `prover-max`.
- `decol` needs no net once `∩_z` is inside (`decol_core` at `z = λ_k + iη`, `η = N^{-1+ε}`); `ukx` is exact at `E = μ_k`; `ε = min(τ/2, 1/2)` because the paper's `η = N^{-1+τ}` yields `2N^{-1+τ}` (`T2192c`).
- QUE: the `Θ`-differences are on `main`: `thetaDiff` (deterministic, `Θ^{(+,-)}` and `Θ^{(+,+)}`, zero mode cancelled by `Theta0_apply`, no `log L`, no `≺`) from `prop5to8_holds` and `Theta_apply_add_right`; RBM2D's `QUEFromQDiff_profile_diff` (`QUEFromQDiff.lean:465`, via `norm_Theta_sub_le_log`, used at `:478`) is not needed. `MAQUE` consumes the expectation halves at `ε = 𝔠(𝔡-ε₀)` (`queDomain`); not compiled (MA-05: RBM2D port of `QUEFromQDiff.lean` 44-797 and 798-812, the `d = 3` chain is new).
- Interfaces: `locSC_to_UNLocAvgBand` is not a projection (8 lines: `calB … 0` is rewritten to `Bctl` under the binder), `QUE_to_UNQueBand` is (3 lines); both compiled with instances. The iteration `STMainInd → UNMLOut` belongs to ST-D6 (RBM2D `mlConcl_of_R3`, `Induction/MainInd.lean:144`, `mainIndPinV3_of_R3` :110); RBM3D needs neither `P7FromSTO_tmod` nor `STOAll` (RBM2D `Main/P7FromSTO.lean:89, 63`) because `UNMLOut` is already stated for every `0 ≤ t_n ≤ lemT z_n`.
- Carrier pricing (portmap P.6, `carrier.py`, `price.py`): 675 compiled lines are carrier-free, 955 band-specific; stating the cores carrier-free saves BA-M1..M3 at most 32% of their 3300 central lines (under one ticket): the BA total 62 (61..66) becomes 61..62 of cap 70, not binding. Recommendation: no carrier structure.
- Lead corrections (checked against files): T2187 and T2189 are merged in the base (ancestry lines above), so `PinsK.lean` is read from the tree; the ticket's empty domain for `κ ≥ 2`, `ε ≥ 1` holds only for `κ > 2`, `ε > 1` (`domain_extreme`, `locDomain_nonempty`, `locDomain_empty_kappa`, `locDomain_empty_eps`); RBM2D HEAD differs from `c9a24cf` (diff-stat above), so every RBM2D citation is at `c9a24cf`.
- Extreme inputs compiled (lesson 25): `κ = 2`, `ε = 1` (`domain_extreme`); `E = ±(2-κ)` (`queDomain_edge`, `im_mE_edge`); `A = univ` (empty bad event, `que2BadMat_univ`) and `A = ∅` (bad event at the zero matrix, `que2BadMat_empty_zero`: why `A ≠ ∅`); `ilambda` at both `(eq:WO)` edges (`szLo_admissible`, `szUp_admissible`, `inst_locSC_lo`, `inst_locSC_up`, `inst_QUE_up`).

## (c) Verified Mathlib and core names used (one line each; all 227 names typed in the probe, resolved by Lean, with their types and modules, are in portmap P.9, script `names.py`; the 12 below are the non-trivial ones)
Real.rpow_le_rpow_of_nonpos [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.rpow_le_rpow_of_exponent_le [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
Real.rpow_le_one_of_one_le_of_nonpos [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.rpow_mul [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.mul_rpow [Mathlib.Analysis.SpecialFunctions.Pow.Real] : ∀ {x y z : ℝ}, 0 ≤ x → 0 ≤ y → (x * y) ^ z = x ^ z * y ^ z
tendsto_rpow_atTop [Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics] : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
MeasureTheory.measure_union_le [Mathlib.MeasureTheory.OuterMeasure.Basic] : ∀ {α : Type u_1} {F : Type u_3} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasure
MeasureTheory.integral_const_mul [Mathlib.MeasureTheory.Integral.Bochner.Basic] : ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {L : Type u_6} [i
Set.mem_ofPred_eq [Mathlib.Data.Set.Operations] : ∀ {α : Type u} {x : α} {p : α → Prop}, (x ∈ {y | p y}) = p x
Finset.sup_congr [Mathlib.Data.Finset.Lattice.Fold] : ∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s₁ s₂ : Finset β} {f g : β → α},   
pow_le_pow_left₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono 
inv_anti₀ [Mathlib.Algebra.Order.GroupWithZero.Basic] : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀]  
absent (Lean `#check`: unknown constant): Matrix.trace_submatrix_equiv, Matrix.trace_reindex, Matrix.cons_val_succ?
deprecated in this Mathlib/core (Lean warning): Set.mem_setOf_eq (use Set.mem_ofPred_eq), if_true (use ite_true)

## (d) Open issues and paper-delta candidates
Open (owed by the split; none blocks the freeze):
1. Pins not compiled: `MANetLoc`, `MANetQD` (MA-04) and `MAQUE` (MA-05); `∀ d, UNMLOut d` is owed by ST-6 (ST-D6 is unwritten); `Thm27` by BA.
2. Registry (DECISIONS §16, §20; the rows are in `RBM3D/Test/Axioms.lean`): `decol`, `locSC`, `QUE`, `QDiff` owed (MA-01 registers them); `UNMLOut` owed (ST-6) and `UNL32` borrowed (both registered); `MANetLoc`, `MANetQD`, `MAQUE` become theorems of MA-04, MA-05, not rows.
3. The literal fine-lattice distance of `(G_bound)` (`K = |x-y|` on `Z_{WL}^d`, comparable to `W|[x]-[y]|_∞` up to `2^{d-2}`) is not compiled; the freeze uses the block reading of T2001e (`T2192b`).
4. For the dispatcher: ST-D6 states the iteration `STMainInd → UNMLOut`; BA-M1..M3 export the explicit form (bridges compiled); MA-02 and MA-03 of the split are ports of compiled text.
Paper-delta candidates (the dispatcher numbers them):
- `T2192a`: `(Meq:QdS1)`, `(Meq:QdS2)` read "for each `z ∈ 𝐃_{κ,ε}`, `N` large" with `N₀` uniform over `𝐃_{κ,ε}` (third and fourth conjunct of `QDiff`).
- `T2192b`: `|x-y|` of `(G_bound)` and `W|a-b|` of `(eq:diffu1,2)` read as `W|[x]-[y]|_∞` (`L^∞` block distance, `1_2:274`, as the merged `STLocalEntry`); T2001 and T2161 use the `ℓ¹` block distance (`calB_distB_compare`: factor `d^{-(d-2)}`).
- `T2192c`: proof of Thm 2.1: `η = N^{-1+τ}` gives `‖ψ_k‖² ≤ 2N^{-1+τ}`; the compiled proof uses `η = N^{-1+ε}`, `ε = min(τ/2, 1/2)`.
- `T2192d`: `(eq:diffu1)`, `(eq:diffu2)` "for all `a, b`" is read with `a, b` inside the probability (union over `L^{2d} ≤ N²` pairs), like the `∩_z`.
- `T2192e`: endpoint form decision: explicit `W^τ`, `N^{-D}` for Thm 2.1-2.5 and 2.7; the merged `Prec` is equivalent (`explicit_of_stochDomAt`, `prec_of_explicit`): a decision, no statement change.
- `T2192f`: the domain `𝐃_{κ,ε}` is empty exactly for `κ > 2` or `ε > 1` (`N > 1`), not at equality.
- `T2192g`: `(eq:diffu1,2)` reduce to `ML:GLoop` with the loop indices `(b,a)` (`zTrace`); the profile is symmetric, so no statement changes.
