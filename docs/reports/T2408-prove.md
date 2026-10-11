Prover model: claude-sonnet-5-5

# T2408 stage 1a: design gate for BA-G6a (CONTROL H203). Mathematics only; no Lean was written in this stage.

Citations: `path:N` is relative to `RBM3D/` on `main` 1c25de0; `7_8:N`, `3_5:N` are lines of `paper/tex/7_8_light_weight.tex`, `3_5_Loop_Hierarchy.tex`. Scripts (scratchpad `T2408/`, not in the repository): `g6a.py consts|inst|sample`, `est.py`, `span.sh`; verbatim outputs below.
Notation: `Δ = G_t - M` (`(baFMz sz z).GM`), `μ = seqP (sz.withLam 0)`, `N = sz.size n`, `w₀ = W^{-d}`, `𝓛max = max_{a,b} ‖𝓛^{(2)}_{(-,+),(a,b)}‖` (`STmaxLoop2g`, `Chain/Carrier.lean:135`), `Ω(ε) = {‖Δ‖_max ≤ W^{-ε}}` (`FlowFM.indMax`, `BA/Step1Boot.lean:54`), `(initialGT2) = STInitialGT2gL` (`Chain/Carrier.lean:140`) = (A) `‖Δ‖_max ≺ W^{-ε₀}` and (B) `𝓛max ≺ Ψ²` (paper `3_5:28-30`, `7_8:1917`). GL1-GL6 are the targets of (G)(v).

## (a) Math preflight — Sun Oct 11 04:55:08 UTC 2026

### (i) Exponent table
Instance: `d=3`, `sz0` at `n=0` (`L=4, W=32, N=2097152, λ=1/64`), `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`, `Λ=𝔡⁻¹=10`, `ε₀=1/10`, `Ψ=W^{-1}`, `τ=1/20`. Values from `python3 g6a.py inst|consts|sample` (outputs in (ii) and (G)(iv)).

| quantity | value | constraint | slack |
|---|---|---|---|
| `W ≥ N^𝔠` | `W=32`, `N^{1/6}=11.31` | `Admissible` (`Defs/Sizes.lean:177`) | 2.83× |
| `(eq:WO)` | `W^{-d/2+𝔡}=7.8e-3 ≤ λ=1/64 ≤ 𝔡⁻¹=10` | `BAFlow.1` | 2.0× / 640× |
| `ε₀`, window of `Ψ` | `[W^{-3/2}, W^{-ε₀}]=[5.52e-3, 0.7071]`, `Ψ=3.125e-2` | window nonempty iff `ε₀ ≤ d/2=3/2` (hypothesis of `BAGavLGEX` only; GL3, GL4 need `Ψ ≥ 0` at most) | 15× in `ε₀`; `Ψ` 5.7× above, 22.6× below the ends |
| floor | `w₀=3.05e-5` against `(4/κ²)Ψ²=1.56e-2` | `w₀ ≤ (4/κ²) N^ε Ψ²` (GL4), `Ψ² ≥ w₀` (window) | 512× |
| `ζ=𝔠ε₀/2` | `1/120=8.33e-3` | `N^ζ W^{-ε₀} ≤ W^{-ε₀/2}` (bridge GL3, GL5) | `0.7983 ≤ 0.8409` (1.053×); equals `(W/N^𝔠)^{ε₀/2} ≥ 1`, true for every `n` |
| `ε'=min(ε₀,d/2)` | `1/10` | `w₀ ≤ δ²=W^{-2ε'}` (`hwd` of `GreenCore_diag`) iff `ε' ≤ d/2` | exponent ratio `ε'/(d/2)=1/15` |
| `τ₀=min(τ/4, 𝔠ε')` | `0.0125` | `τ₀ ≤ 𝔠ε'=0.0167`; `2τ₀ < τ` (loss `Φ²=N^{2τ₀}`) | 1.33×; 2× |
| loss `C_gii N^{2τ₀} ≤ N^τ` | `C_gii=7.96e91 / 1.30e102 / 1.45e129` (`κ=0.5/0.25/0.04`) | eventual: `log₁₀N ≥ log₁₀C_gii/(τ-2τ₀)` = 3676 / 4085 / 5166 | eventual in `n` only |
| closure `δ≤κ/2`, `K_BAδ≤1/2`, (C1) | `log₁₀W ≥ 196.1 / 216.4 / 282.7` at `ε'=1/10`; `19.6 / 21.6 / 28.3` at `ε'=1` | analytic constants, (G)(iv) | eventual in `n` only; not a hypothesis of any target |
| `κ` uniform in `L` | `0.5 / 0.25 / 0.04` at `g=1/64, 1, 10`; `Im m(z)` at `L=64`: `0.8325 / 0.3435 / 0.0442` | `κ ≤ Im m` (`BAdom`) | 1.67× / 1.37× / 1.10× |
| `g₀=√t₀ g` (`L=64`) | `0.0130 / 0.535 / 2.10` | `0<g₀≤Λ=10` (`BAflow_lam0_window`, `BA/GreenSchur.lean:72`) | 769× / 18.7× / 4.76× |
| `t` | `1/2` | `0 ≤ t ≤ BAflowT0`; `half_lt_t0`, `BA/FlowPins.lean:1254` | `T₀ > 1/2` |
| `d` | 3 | `2 ≤ d` (guard of GL2, GL3, GL6, as `baGbEXPij'_holds`, `BA/GreenOff.lean:1289`) | 1 |
| rate `c₀`, `ρ`, `S`, `K_Θ=16κ⁻⁴`, `K_BA`, floor constant `4/κ²` | (G)(iv) | depend on `(d,κ,𝔡)` only | — |

### (ii) One concrete nondegenerate instance
Data as in (i). Hypotheses at these numbers: GL2: `BAFlow` (`FlowPinsInst.flow_sz0`, merged), `0 ≤ t ≤ T₀`, `ε₀>0`, `2 ≤ d`. GL3, GL4: the same, and (initialGT2). GL5: (A) of it. GL6: the same, and `hFA` (= the conclusion of `BAFAav`, T2401 probe `t/T2401:RBM3D/Probe/T2401Pins.lean:337`; owed by G5b). GL1: matrices `G, M` with `‖G-M‖_max ≤ κ/2`. Command and output (`n` table: `sz0` is `L_n=4(n+1)`, `W_n=(2(n+1))^5`; the check `W^{-ε₀} ≤ κ/2` is the closure, eventual):
```
$ python3 g6a.py inst
sz0 n=0: L=4 W=32 N=2097152 lam=0.015625; flow_sz0: kappa=0.5 eps=0.1 c=0.16666666666666666 dd=0.1; d=3; eps0=0.1; Psi=W^-1=0.03125; 2<=d: True
Admissible: W=32 >= N^c = 11.314 (slack 2.83x); (eq:WO) W^(-d/2+dd) = 7.8125e-03 <= lam = 1.5625e-02 <= 1/dd = 10
window of Psi: W^-d/2 = 5.5243e-03 <= Psi = 3.1250e-02 <= W^-eps0 = 0.7071: True; nonempty iff eps0 <= d/2 = 1.5
BA floor: W^-d = 3.0518e-05; Psi^2 = 9.7656e-04 >= W^-d: True; 4/kappa^2 = 16.0
local-law bridge: zeta = c eps0/2 = 0.00833; N^zeta W^-eps0 = 0.79830 <= W^(-eps0/2) = 0.84090: True (exact W >= N^c gives it for every n)
diag law exponents at tau = 0.05: eps' = min(eps0, d/2) = 0.1; tau0 = min(tau/4, c eps') = 0.01250: tau0 <= c eps' (slack 1.33x), 2 tau0 = 0.0250 < tau (slack 2.00x)
  n=0    L=4     W=32           N=2.097e+06  W>=N^c: True  window nonempty/Psi=W^-1 inside: True  W^-eps0 <= kappa/2: False
  n=1    L=8     W=1024         N=5.498e+11  W>=N^c: True  window nonempty/Psi=W^-1 inside: True  W^-eps0 <= kappa/2: False
  n=2    L=12    W=7776         N=8.125e+14  W>=N^c: True  window nonempty/Psi=W^-1 inside: True  W^-eps0 <= kappa/2: False
  n=5    L=24    W=248832       N=2.130e+20  W>=N^c: True  window nonempty/Psi=W^-1 inside: True  W^-eps0 <= kappa/2: False
  n=10   L=44    W=5153632      N=1.166e+25  W>=N^c: True  window nonempty/Psi=W^-1 inside: True  W^-eps0 <= kappa/2: True
  n=100  L=404   W=336323216032 N=2.509e+42  W>=N^c: True  window nonempty/Psi=W^-1 inside: True  W^-eps0 <= kappa/2: True
```
External hypotheses, concrete computations. (1) (initialGT2) at `t ≡ 0` holds for every `n`, at the same `(d, sz0, flow_sz0, ε₀, Ψ)`: `X=0` (`BAX`, `BA/GreenLDE.lean:77`, is `seqHflow (sz.withLam 0) n t ω`; `seqHflow n 0 ω = 0`, `localLaw_seqHflow_zero`, `Green/LocalLaw.lean`, via `Sizes.seqHflow_eq_smul`), `z_0=s`, so `G=(D-s)⁻¹=M` (`GreenCore_carrier`, `BA/GreenCore.lean:1532`: `(D-s)M=1`, `z=s-tm`), hence (A) is `0 ≤ …`; `𝓛_{ab}(G=M)=w₀|M^{(B)}_{ab}|²` (`GreenCore_loop`, `:374`, with `M_{xy}=1_{o(x)=o(y)}M^{(B)}_{[x][y]}`) `≤ w₀` (`BAMfine_norm_le_one`, `BA/GreenSchur.lean:105`) and `w₀=3.05e-5 ≤ Ψ²=9.77e-4` (line "BA floor" above; `W^{-d} ≤ W^{-2}` for `d ≥ 2`, `W ≥ 1`): (B) holds. So the hypothesis set of GL3, GL4, GL5 is nonempty and not collapsed (`N`, `W`, `L` are `sz0`'s). (2) At `t > 0` (initialGT2) is the induction's output and stays a hypothesis; finite-size computation (`d=3, L=3, W=2, N=216`, `g=1` design flow data, `t=0.9t₀`, 40 samples of `X`; `κ:=Im m₀`), same model as `docs/reports/T2390/chk.py`:
```
$ python3 g6a.py sample
data: g0=0.5994 m0=-0.0256+0.7193j t=0.3234 N=216 kappa:=Im m0=0.7193  floor const 4/kappa^2 = 7.73  16/kappa^4 = 59.8
40 samples: averaged identity residual max = 8.77e-16; E3 entrywise residual max = 3.62e-15
floor: samples with min_u |G_uu| >= kappa/2: 40/40; max over them of W^-d / ((4/kappa^2) max L) = 0.201 (<= 1 required)
max over samples of ||Delta||_max^2 / max L = 2.174;  max ||vbar||_max / ||<MK>||_max = 0.868 (<= 16/kappa^4 = 59.8 required)
```
The averaged identity is `v̄_a - tΣ_b M^{(B)}_{ab}M^{(B)}_{ba} v̄_b = ⟨M𝒦⟩_a` (GL6) and `‖Δ‖²_max/𝓛max = O(1)` is the shape of GL2 (finite size, not a limit). (3) `hFA` at `t ≡ 0`: `𝒦 = 0` (`X=0`, `Δ=0`, `A_u=0`), so `⟨M𝒦⟩=0`: nonempty.

## (G) Design gate (items (i)-(v) of the ticket)

### (G)(i) The route: band `Green/LocalLaw.lean` read at BA
Band route (module docstring `:24-27`): `AsGMcSeq` + `LoopDetSeq Ψ'` → `LocalLawDetSeq Ψ'` (`localLawDetThm :658`) → pins FA, IBP → `GavLDetSeq Ψ'` (`avgBoundDetThm :739`) → `GavLDetSeq Ψ` by the floor (`loopFloorThm :786`, `gavLDetThm_of_floor :352`) → `gbEXPV3Theorem_of_parts :427`.

| band step | BA replacement | owner |
|---|---|---|
| `AsGMcSeq` (`3_5:30`) | (A) of `STInitialGT2gL`: hypothesis of `lem_GbEXP_BA` (`7_8:1917`) | input (induction) |
| `LoopDetSeq Ψ'`, `Ψ'=max(Ψ,W^{-d/2})` | (B) of the same; no `Ψ'`: GL2 has no `+W^{-d}` term (the floor GL1 absorbs it) | input |
| `giiSeq_of_asGMc`, `gijSeq_of_asGMc` (entry pins) | `BAGiiGEX`, all pairs: **GL2 `baGbEXPii_holds`**, new in G6a from `GreenCore_diag` (`BA/GreenCore.lean:1361`), `baStab_holds` (`BA/GreenOff.lean:809`), `baLDEin_holds` (`BA/GreenLDE.lean:199`), `GreenOff_pin_consts` (`:1198`), `GreenOff_ev_small` (`:1235`), `GreenOff_loop_eq` (`:878`), GL1. `baGbEXPij'_holds` (`:1289`, merged) is not used by the local law | G6a (new) |
| `LocalLaw_gexRHS_le_maxLoopPM` (`:531`, `9^d` near ball), `LocalLaw_trans`, `_absorb` (`:601`, `:582`) | not needed: `BAGiiGEX` covers diagonal and off-diagonal pairs; `‖Δ_xy‖² ≤ N^τ𝓛max ≤ N^{2τ}Ψ²` | — |
| `LocalLawDetSeq` (`:104`), `localLawDetThm` | **GL3**: `‖Δ‖_max ≺ Ψ` = `GreenIBP_hll` (probe `t/T2402:…/T2402Pins.lean:177`) | G6a (new) |
| `FixedTimeFAThm`, `FARowDet`, `FABlkDet` (`:122-176`) | conclusion of `BAFAav` (`|⟨M𝒦⟩_a| ≺ Ψ²`) with `BAFamGain` (T2401 Amend 1 D1, D3) | owed by G5a (families, S6) and G5b (`BAFamGain`, `BAFAav`; `docs/reports/T2401-prove.md:183`) |
| `IBPDetThm`, `IBPDetSeq` (`:186`, `:145`) | none on the T2401 route (`docs/tickets/T2402-amend-1.md` F2); `BAIBPDet` (T2402 probe `:201`) only if G5c is revived: its premises come from GL3, GL5 | G5c (held); no owner needed |
| `avgBoundDetThm` (`norm_avgErr_le`, `Kstab3`) | **GL6**: `GreenCore_E3` (`:1253`) gives `v̄ - tM^{(++)}v̄ = ⟨M𝒦⟩`; `BAStab` (`:1268`) at `K=16κ⁻⁴` (`baStab_holds`); `L^{(1)}-m = v̄`; the `PrecL` assembly | G6a (new) |
| `loopFloorThm`, `inv_Wd_le_maxLoopPM` (`Green/EntryDom.lean:386`) | **GL1** (one sample) and **GL4** (along the flow); not merged in G3a: the grep below finds no such lemma | G6a (new) |
| `gavLDetThm_of_floor`, `loopDetSeq_mono` (`:352`, `:340`) | not needed: `BAGavLGEX` has the window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` as hypotheses (`Step1Boot.lean:97-103`) | — |
| `gavLDetFloorThm_of_parts`, `gbEXPV3Theorem_of_parts` (`:412`, `:427`) | `BAGbEXPav d` = `BAFAav d` + `baGbEXPii_holds … (ε₀/2)` + GL6 (one `intro`) | G6b |

G6a takes: the per-sequence diagonal law (GL2), the local law (GL3), the floor (GL1, GL4), the bridges (GL5), the averaged wiring (GL6). Stays with G6b: the composition `BAGbEXPav`, its registry line, and (with G7) the primed consumers of `baGbEXPij'_holds`. Every step has a BA argument or an owner: the stop condition is not triggered.
```
$ grep -n -e floor -e "4 / κ ^ 2) \* Lm" RBM3D/BA/GreenCore.lean RBM3D/BA/GreenOff.lean RBM3D/BA/GreenStab.lean | wc -l ; grep -rn -e GreenLocal -e baGbEXPii_holds -e BAFAav -e GreenIBP_hll RBM3D RBM3D.lean --include='*.lean' | wc -l
       0
       0
```

### (G)(ii) The interface to G5a and G5c
- **T2401** (`BAFAav`, `BAFamGain`, Amend 1 D1) takes `BAGiiGEX sz z t (ε₀/2)`. `BAGbEXPii` (`Step1Boot.lean:108`) has the same binder prefix (`κ ε 𝔡`, positivity, `𝔠 sz z`, `BAFlow`, `t`, `0 ≤ t`, `t ≤ BAflowT0`, `ε₀>0`), so `baGbEXPii_holds d hd κ ε 𝔡 … (ε₀/2) (half_pos hε₀)` discharges it literally; the form `∀ ε₁ ≤ ε₀` is `fun ε₁ h _ => baGbEXPii_holds … ε₁ h`.
- **T2402** (`BAIBPDet`, probe `:201`) takes `HighProbAt Ω_δ`, `δ ≤ κ/2` eventually, `GreenIBP_hll sz z t Ψ`. GL3's conclusion is `GreenIBP_hll` verbatim (a `PrecL` over `Idx×Idx` of `‖GM‖` against `Ψ`; bridge `fun h => h`). GL5 gives `HighProbAt` of `{∀ x y, ‖GM‖ ≤ N^ζ W^{-ε₀}}` and `N^ζ W^{-ε₀} ≤ κ/2` eventually, `ζ ≤ 𝔠ε₀/2`: `δ n := N^ζ W^{-ε₀}`.
- `ε₀` handling (D1 of Amend 1): (A) at `(ζ=𝔠ε₀/2, D+1)` gives `P(‖Δ‖>N^ζW^{-ε₀}) ≤ N^{-D-1}`, and `{‖Δ‖_max ≤ N^ζW^{-ε₀}} ⊆ Ω(ε₀/2)`; GL2 at `ε₀/2` gives `1_Ω|Δ_xy|² ≤ N^τ𝓛max` w.h.p.; (B) gives `𝓛max ≤ N^τΨ²` w.h.p.; the union of three events of probability `≤ N^{-D-1}` is `≤ N^{-D}` for `N ≥ 3`, hence `‖Δ‖_max ≤ N^τΨ` (`Ψ ≥ 0` eventually).
- `hFA` of GL6 is literally the conclusion of `BAFAav` (T2401 probe `:337-346`); GL6's conclusion is literally that of `BAGavLGEX` (`Step1Boot.lean:97-103`).

### (G)(iii) The floor at BA
The band `W^{-d} ≤ 4 max𝓛` (`inv_Wd_le_maxLoopPM`) uses `|G_uu| ≥ 1/2` (`|m|=1`, `δ ≤ 1/2`). At BA `|M_uu| = |m| ≥ κ` (`BAMB_diag_eq`, `BA/Ward.lean:89`; `κ ≤ Im m` from `BAReal`), so on `{‖Δ‖_max ≤ κ/2}`: `|G_uu| ≥ κ/2` and `GreenCore_loop G a a = w₀² Σ_{o,o'}|G_{(a,o)(a,o')}|² ≥ w₀² Σ_o |G_{(a,o)(a,o)}|² ≥ w₀ κ²/4`: **BA floor `W^{-d} ≤ (4/κ²) 𝓛max`** (GL1; constants `16 / 64 / 2500` at `κ=0.5/0.25/0.04`; sample ratio `0.201 ≤ 1`, (ii)). The statement "G3a's `W^{-d} ≤ 4κ⁻² max𝓛`" is a sentence of `docs/reports/T2390-prove.md` G.3, not a merged lemma (grep above: 0 lines). GL4 (twin of `loopFloorThm`): under (A) and (B), for every `ε>0`, eventually `W^{-d} ≤ (4/κ²) N^ε Ψ²`; proof: `{‖Δ‖≤κ/2}` has probability `≥ 1-N^{-1}` (A, `N^ζW^{-ε₀} ≤ κ/2` eventually), on it `w₀ > (4/κ²)N^εΨ²` forces `𝓛max > N^εΨ²` (probability `≤ N^{-1}`), and `2N^{-1} < 1` for `N ≥ 3`. Consumers: the Step-1 rewire (G7: `W^{-d} ≤ 4κ⁻²N^τ g` on `Ω`) and the `BAFamGain` condition `c=W^{-d} ≤ ρ²`.

### (G)(iv) Constants (C1, 2254 G2)
All constants are functions of `(d, κ, 𝔡)`: `c₀=BAct_rate d Λ κ`, `ρ=c₀⁻¹expC(d-2,c₀)` (`baM_col_l1`, `baM_row_l1`, `GreenStab.lean:123,116`), `S=expC(d-2,c₀/2)`, `ρ₂ ≤ 1` (`baM_rho2 :132`), `K_Θ=16κ⁻⁴` (`baStab_holds`), `K_BA=ρ(1+ρ₂K_Θ)`, `4/κ²`, `C_gii=8K_BA²(9/4 A_b + X_b)` at `Φ=1, δ=κ/2, g₀=Λ, w₀=(4/κ²)𝓛max` (`GreenCore_R0/Xb/Ab`, `:1348-1357`; `C_gii(Φ)/Φ² ≤ C_gii(1)` checked at `Φ=100`). No `g ≤ W^{-ε}`, no smallness of `‖M-m₀I‖`, no `(Cλ)^{|a-b|}`: the new steps use `|G_uu| ≥ κ/2`, event algebra and merged lemmas of the C1 audit. `κ` is uniform in `L` (table row). Command and output (`d=3`, `Λ=10`):
```
$ python3 g6a.py consts
analytic constants, d = 3, Lambda = 1/dd = 10 (depend on (d, kappa, dd) only; kappa uniform in L):
kappa   c0         S          rho        K_Theta    K_BA       floor 4/kappa^2   C_gii(Phi=1)   C_gii(Phi=100)/100^2  (<= C_gii(1)?)
0.5     4.158e-03 3.289e+14 4.943e+15 2.560e+02 1.270e+18 16.0              7.962e+91     7.962e+91  True
0.25    2.081e-03 5.240e+15 1.574e+17 4.096e+03 6.447e+20 64.0              1.298e+102     1.298e+102  True
0.04    3.333e-04 7.968e+18 1.494e+21 6.250e+06 9.339e+27 2500.0            1.448e+129     1.448e+129  True

thresholds on log10 W (eventual in n) for delta = W^-eps': delta <= kappa/2 | K_BA delta <= 1/2 | (C1) at Phi = 1; and n of sz0 (W_n = (2(n+1))^5) with W_n >= the max threshold
eps'=0.1  kappa=0.5        6.0     184.0     196.1   max =     196.1   sz0 index n >= 8.290e+38
eps'=0.1  kappa=0.25       9.0     211.1     216.4   max =     216.4   sz0 index n >= 9.375e+42
eps'=0.1  kappa=0.04      17.0     282.7     271.3   max =     282.7   sz0 index n >= 1.744e+56
eps'=1.0  kappa=0.5        0.6      18.4      19.6   max =      19.6   sz0 index n >= 4.177e+03
eps'=1.0  kappa=0.25       0.9      21.1      21.6   max =      21.6   sz0 index n >= 1.062e+04
eps'=1.0  kappa=0.04       1.7      28.3      27.1   max =      28.3   sz0 index n >= 2.255e+05
eps'=1.5  kappa=0.5        0.4      12.3      13.1   max =      13.1   sz0 index n >= 2.049e+02
eps'=1.5  kappa=0.25       0.6      14.1      14.4   max =      14.4   sz0 index n >= 3.826e+02
eps'=1.5  kappa=0.04       1.1      18.8      18.1   max =      18.8   sz0 index n >= 2.940e+03

survey: at g = 1/64, 1, 10 the kappa used are 0.5, 0.25, 0.04; Im m(z) at L = 64 from stab.flow_point (w = 1.2i, 1.2i, 1.0i), kappa <= Im m:
g=0.015625: Im m(z) = 0.8325, Im z = 0.368, t0 = 0.6937, g0 = 0.0130 <= Lambda True, kappa = 0.5 <= Im m: True, Im m0 = 0.9995, |m0| = 0.9995
g=1: Im m(z) = 0.3435, Im z = 0.857, t0 = 0.2862, g0 = 0.5350 <= Lambda True, kappa = 0.25 <= Im m: True, Im m0 = 0.6420, |m0| = 0.6420
g=10: Im m(z) = 0.0442, Im z = 0.956, t0 = 0.0442, g0 = 2.1024 <= Lambda True, kappa = 0.04 <= Im m: True, Im m0 = 0.2102, |m0| = 0.2102
```
The closure thresholds are the analytic ones (as T2390 (a) R2): GL2, GL3, GL4 are `∀ᶠ n` statements and their conclusions are proved with the analytic constants; no concrete `n` witnesses the closure, and no target has the closure as a hypothesis.

### (G)(v) Pins, instance and split
Pseudo-statements (mathematics; merged identifiers as atoms; the probe `RBM3D/Probe/T2408Pins.lean` is compiled by the Lean-capable step). Common prefix `P(d)`: for `κ ε 𝔡 > 0`, `𝔠, sz, z` with `BAFlow sz κ ε 𝔠 𝔡 z`, `t` with `0 ≤ t n ≤ BAflowT0 sz z n`, `ε₀ > 0` (the order of `BAGbEXPii`).
- **GL1** `GreenLocal_floor_sample`: for `G, M` on `Vtx d L W`, `Mb`, `m`, `κ>0`, `M_uv = 1_{o(u)=o(v)} Mb_{[u][v]}`, `Mb_aa = m`, `κ ≤ ‖m‖`, `δ ≤ κ/2`, `‖G_uv-M_uv‖ ≤ δ` for all `u,v`: `∀ a, (W^d)⁻¹ ≤ (4/κ²) · GreenCore_loop G a a`.
- **GL2** `baGbEXPii_holds`: `2 ≤ d → BAGbEXPii d` (unchanged text, `Step1Boot.lean:108`). Proof: `ε'=min(ε₀,d/2)`, `τ₀=min(τ/4,𝔠ε')`, `Φ=N^{τ₀}`; the four events of `baLDEin_holds` w.h.p. (`StochDomAt.highProb`); eventually (`BAflow_lam0_window`, `GreenOff_ev_small`) `GreenOff_pin_consts` gives `δ=W^{-ε'} ≤ κ/2` and (C1), and `K_BAδ ≤ 1/2`; on `Ω(ε₀) ⊆ Ω(ε')` `GreenCore_diag` (with `GreenOff_loop_eq`, `baStab_holds`, `baM_*`) and GL1 give `‖Δ_xy‖² ≤ C_gii N^{2τ₀} 𝓛max ≤ N^τ 𝓛max`.
- **GL3** `GreenLocal_LocalLaw d := P(d) → ∀ Ψ, (∀ᶠ n, 0 ≤ Ψ n) → STInitialGT2gL (baFMz sz z) μ t ε₀ Ψ → PrecL sz μ (U := Idx×Idx) (n p ω ↦ ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (n _ _ ↦ Ψ n)`, theorem `greenLocal_localLaw : 2 ≤ d → GreenLocal_LocalLaw d`.
- **GL4** `GreenLocal_Floor d := P(d) → ∀ Ψ, STInitialGT2gL … → ∀ ε > 0, ∀ᶠ n, (W^d)⁻¹ ≤ (4/κ²) · N^ε · Ψ n ^ 2`; theorem for `2 ≤ d`.
- **GL5** `GreenLocal_omega d := P(d) → (PrecL sz μ (U := Idx×Idx) (n p ω ↦ ‖GM n (t n) ω p.1 p.2‖) (n _ _ ↦ W^{-ε₀})) → ∀ ζ, 0<ζ → ζ ≤ 𝔠ε₀/2 → (∀ᶠ n, N^ζ W^{-ε₀} ≤ κ/2) ∧ HighProbAt μ sz.size (n ↦ {ω | ∀ x y, ‖GM n (t n) ω x y‖ ≤ N^ζ W^{-ε₀}})`.
- **GL6** `GreenLocal_gav_of_fa` (`2 ≤ d`): for `κ ε 𝔡`, `𝔠 sz z`, `BAFlow`, `t`, and any `Ψ`: `PrecL (U := Zd) (n a ω ↦ ‖W^{-d} Σ_o Σ_{b'} BAMB … a b' · GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω) (GreenCore_Dc sz z n) (t n) m (b',o) (a,o)‖) (n _ _ ↦ Ψ n ^ 2)` implies `PrecL (U := Zd) (n a ω ↦ ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖) (n _ _ ↦ Ψ n ^ 2)`. Proof: `L^{(1)}_a - m = v̄_a` (`Eblk`, `Loop/GLoop.lean:55`); `GreenCore_E3` at `x=y=(a,o)`, averaged over `o`, gives the identity of (ii); `baStab_holds` gives `‖v̄‖_max ≤ 16κ⁻⁴ max_a‖⟨M𝒦⟩_a‖`; `16κ⁻⁴ N^{τ'} ≤ N^τ` eventually.
- **Instance** (probe): `d=3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2` (`half_lt_t0`), `ε₀=1/10`, `Ψ=W^{-1}`: `example (h : GreenLocal_LocalLaw 3) (hinit : STInitialGT2gL (baFMz sz0 zSeq) μ (fun _ => 1/2) (1/10) (fun n => W^{-1})) : PrecL … := h … hinit`, and likewise GL4, GL5, GL6 (`hFA` a hypothesis, owed by G5b); GL2 applied at the same data with no extra hypothesis. 1b adds the `t ≡ 0` instance of (ii)(1) to discharge `hinit`.

Registry: no new owed line (`hFA` is the conclusion of T2401's `BAFAav`, whose owed line T2401's 1b adds); one line retired: `RBM.BA.BAGbEXPii` leaves `owedProps` at G6a's merge, as T2403 retired `BAStab`, `BAGbEXPij'` (`docs/reports/T2403-prove.md` (b), Registry); then `Test/Axioms.lean` is a sole writable file; pre-check `import RBM3D` + `#assert_rbm_axioms`.

Split against the stop line 2000 (`python3 est.py`; bases measured by `span.sh`: `baGbEXPij'_holds` 1289-1368 (80), `GreenOff_carrier_decay` 916-964 (49), `localLawDetThm` 658-724 (67), `LocalLaw_maxLoop_dom` 634-650 (17), `avgBoundDetThm` 739-779 (41), `loopFloorThm` 786-840 (55), `inv_Wd_le_maxLoopPM` 386-414 (29)):
```
S0 header, imports, docstring, vocabulary                                             70    90   130
S1 GL1 floor at one sample                                                            40    55    90
S2 GL2 baGbEXPii_holds (consts lemma, whp helpers, carrier wrapper, pin)             190   240   400
S3 GL3 local law at a deterministic control                                          110   160   260
S4 GL4 floor along the flow                                                           60    90   150
S5 GL5 bridges (hll literal, Omega high probability, eps1 <= eps0 form)               40    70   120
S6 GL6 wiring (L1 - m = vbar, averaged E3 identity, BAStab, PrecL assembly)          180   230   380
S7 compiled nonempty instances of GL1-GL6 (d = 3, sz0, zSeq, flow_sz0)               200   300   480
sum (one file BA/GreenLocal.lean)                                                    890  1235  2010
central 1235 <= 1500: no split at ticket time; cut rule: S6 + S7 -> BA/GreenLocal2.lean if GreenLocal.lean passes 1700 lines (GreenLocal2 central 530 + 40 header)
```
One file `BA/GreenLocal.lean`; the cut by section (never inside a proof) is pre-fixed because `hi` is 2010. The estimates are assumptions with measured bases, not measurements.

## Verdicts
- GL1: PASS. GL2: PASS (hypothesis set nonempty at the instance; the exponents close eventually; the guard `2 ≤ d` as T2403a). GL3: PASS. GL4: PASS. GL5: PASS. GL6: PASS (`hFA` external, owed by G5b). Items (G)(i)-(v): answered; the stop condition of the ticket is not triggered.

## (a″) Probe compile — Sun Oct 11 05:16:28 UTC 2026
Stage 1a probe step (CONTROL H203, as H194 for T2401/T2402), role `prover-max` (claude-sonnet-5-5), run after the design-gate preflight. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2408`, branch `t/T2408`, commit `0547dc6` (parent `1c25de0`): one file, `RBM3D/Probe/T2408Pins.lean` (370 lines, never merged, no root import). Sections (a), (G), Verdicts and (d) are not edited; writing the pins gave no correction of (a), so there is no (a′). No port from RBM1D/RBM2D. The file has 10 pin defs (`GreenLocal_*`, `*_pin`), 3 copied premises (`BAFAav`, `GreenIBP_Omega`, `GreenIBP_hll`), 2 abbrevs (`Ψ0`, `δ0`), 13 `#check` lines and 9 `example`s; no theorem, no `sorry`. Compile on the clean tree (`git status --short` printed no line) at HEAD `0547dc6`, started Sun Oct 11 05:14:03 UTC 2026, finished Sun Oct 11 05:14:08 UTC 2026:
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2408 && lake env lean RBM3D/Probe/T2408Pins.lean > out.txt 2>&1; echo "exit code: $?"
exit code: 0
$ cat out.txt        # the 13 `#check` lines, verbatim; no error and no warning line
RBM.BA.GreenLocal_floor_sample_pin : Prop
RBM.BA.baGbEXPii_holds_pin : Prop
RBM.BA.GreenLocal_LocalLaw (d : ℕ) : Prop
RBM.BA.greenLocal_localLaw_pin : Prop
RBM.BA.GreenLocal_Floor (d : ℕ) : Prop
RBM.BA.greenLocal_floor_pin : Prop
RBM.BA.GreenLocal_omega (d : ℕ) : Prop
RBM.BA.greenLocal_omega_pin : Prop
RBM.BA.GreenLocal_Gav (d : ℕ) : Prop
RBM.BA.greenLocal_gav_of_fa_pin : Prop
RBM.BA.BAFAav (d : ℕ) : Prop
RBM.BA.GreenIBP_Omega {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t δ : ℕ → ℝ) (n : ℕ) : Set sz.SeqΩ
RBM.BA.GreenIBP_hll {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t Ψ : ℕ → ℝ) : Prop
```
Scope, hygiene and the copied premises (scripts in the scratchpad `T2408/`, not committed; verbatim):
```
$ grep -nE "sorry|admit|axiom|native_decide|^theorem|^lemma" RBM3D/Probe/T2408Pins.lean; echo grep-exit=$?
grep-exit=1
$ git --no-optional-locks diff --stat main...t/T2408
 RBM3D/Probe/T2408Pins.lean | 370 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 370 insertions(+)
$ git --no-optional-locks grep -n -e GreenLocal -e greenLocal -e baGbEXPii_holds -e BAFAav -e GreenIBP_ main -- RBM3D RBM3D.lean | wc -l
       0
$ grep -rnF -e "import RBM3D.Probe" -e T2408Pins RBM3D.lean RBM3D --include=*.lean | grep -vF "RBM3D/Probe/T2408Pins.lean" | wc -l
       0
$ python3 -I copycheck.py     # the `def` blocks of the three copied premises, source commit against the probe
aec5a16:RBM3D/Probe/T2401Pins.lean def BAFAav (12 lines): identical
4b5f864:RBM3D/Probe/T2402Pins.lean def GreenIBP_Omega (2 lines): identical
4b5f864:RBM3D/Probe/T2402Pins.lean def GreenIBP_hll (3 lines): identical
```
Axioms. An `example` has no name, so a scratch copy (not committed; `ax.py` renames each `example` to `theorem T2408_exK` and appends `#print axioms`) was compiled at HEAD `0547dc6`, finished Sun Oct 11 05:16:25 UTC 2026:
```
$ python3 -I ax.py RBM3D/Probe/T2408Pins.lean ax.lean; lake env lean ax.lean > ax.out 2>&1; echo "exit code: $?"; grep "depends on" ax.out
examples converted: 9
exit code: 0
'RBM.BA.T2408_ex1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex4' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex6' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex7' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex8' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2408_ex9' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Pins, probe lines and instances (`:N` are lines of the probe at `0547dc6`). Data of the concrete examples (all but :225 and :232, which are generic in `d` and the data): `d=3`, `sz0`, `zSeq`, `flow_sz0` (`κ=1/2`, `ε=1/10`, `𝔠=1/6`, `𝔡=1/10`), `ε₀=1/10`, `Ψ0=W^{-1}` (`W^{-3/2} ≤ Ψ0 ≤ W^{-1/10}`), `ζ=1/120=𝔠ε₀/2`; `hinit` is `STInitialGT2gL (baFMz sz0 zSeq) (seqP (sz0.withLam 0)) t ε₀ Ψ0`.
| pin of (G)(v) | Lean | example(s) | discharged / left as hypothesis |
|---|---|---|---|
| GL1 `GreenLocal_floor_sample` | `GreenLocal_floor_sample_pin` :41 | :246, conjunct :354-358 (`t=0`, `n=0`: `L=4`, `W=32`; every `ω`, `a`) | all: `G=M` (`hZ` :275, `BAGt_sub_BAMfine`), Kronecker `M` and `Mb_aa=m` (`GreenCore_carrier`), `κ=1/2 ≤ ‖m‖` (`BAflow_real`), `δ=0`; none left |
| GL2 `baGbEXPii_holds` | `baGbEXPii_holds_pin` :48 | :178 (`ε₀=1/10`), :182 (`ε₀/2`) | all (`t ≡ 1/2 ≤ T₀`, `half_lt_t0`); none left |
| GL3 `greenLocal_localLaw` | `GreenLocal_LocalLaw` :52, `greenLocal_localLaw_pin` :62 | :187 (`t ≡ 1/2`); :246, :359-360 (`t ≡ 0`) | `0 ≤ Ψ0`, `BAFlow`, `t`, `ε₀`; `hinit` left at `t ≡ 1/2`, proved at `t ≡ 0` (`hinit0` :328) |
| GL4 `GreenLocal_Floor` | `GreenLocal_Floor` :66, `greenLocal_floor_pin` :76 | :195 (`t ≡ 1/2`, `ν` arbitrary); :246, :361-362 | as GL3 |
| GL5 `GreenLocal_omega` | `GreenLocal_omega` :80, `greenLocal_omega_pin` :94 | :202 (`hinit.1`); :246, :363-366 | `ζ=1/120`, `ζ ≤ 𝔠ε₀/2` (equality); `hinit.1` left at `t ≡ 1/2`, proved at `t ≡ 0` |
| GL6 `greenLocal_gav_of_fa` | `GreenLocal_Gav` :99, `greenLocal_gav_of_fa_pin` :114 | :211 (`t ≡ 1/2`); :246, :367-368 | `hFA` left at `t ≡ 1/2` (G5b's pin); proved at `t ≡ 0` (`𝒦=0`: `hK0` :270, `hX0` :266) |
| (ii) G5a, G6b | `BAFAav` :119 (copy) | :225: `BAGbEXPav d` from `BAFAav d`, GL2 at `ε₀/2` (`half_pos`) and GL6, one `intro`, generic `d ≥ 2` | `BAFAav d` is the hypothesis |
| (ii) G5c | `GreenIBP_Omega` :133, `GreenIBP_hll` :137 (copies) | :232: GL3 and GL5 give `hll`, `δ ≤ κ/2`, `hΩ` of `BAIBPDet` for every `d ≥ 2` and all data; :187, :202 type the results at `GreenIBP_hll`, `GreenIBP_Omega … δ0` | `hinit` |
Resolutions of the pseudo-Lean of (G)(v) (each visible in the file):
- Each theorem is a closed `Prop` `*_pin`: `baGbEXPii_holds_pin` is `∀ d, 2 ≤ d → BAGbEXPii d` (the text of `BAGbEXPii`, `Step1Boot.lean:108`, is unchanged); `greenLocal_localLaw_pin`, `greenLocal_floor_pin`, `greenLocal_gav_of_fa_pin` are `∀ d, 2 ≤ d → …`; `greenLocal_omega_pin` is `∀ d, …` (GL5 has no guard, as (G)(v)). `GreenLocal_Gav` :99 names the body of GL6.
- GL4's floor exponent is `ν` (:72), the `ε` of (G)(v): `ε` is the `BAFlow` parameter of the prefix `P(d)` (`κ ε 𝔡`, the order of `BAGbEXPii`). The floor is `(W^d)⁻¹ ≤ 4/κ² * N^ν * Ψ n ^ 2` (:73), `N = sz.size n`.
- GL3-GL6 write `P(d)` as `BAGbEXPii` does (`κ ε 𝔡`, positivity, `𝔠 sz z`, `BAFlow`, `t`, `0 ≤ t n`, `t n ≤ BAflowT0 sz z n`); GL3-GL5 then `ε₀ > 0`, GL6 has no `ε₀` (as (G)(v)). GL1 has `∀ {d L W} [NeZero L] [NeZero W] {G M Mb m κ δ}` (:41-44) and no `0 ≤ δ`.
- Textual matches, by script: GL3's conclusion (:58-59) is the body of `GreenIBP_hll` (:138-139); GL6's premise (:103-108) is the conclusion of `BAFAav` (:125-130) apart from the arrow ending :108 (`diff` printed only that line). GL5's event is `GreenIBP_Omega sz z t δ` at `δ n = N^ζ W^{-ε₀}` by unfolding and beta. O2 of (d) (the "literal" matches were text matches) is thus compiled against the probe copies: :187, :202, :211, :225, :232.
Facts for 1b (compile results):
- `Sizes.seqHflow (sz.withLam 0) n t ω` expects `ω : (sz.withLam 0).SeqΩ`; for `ω : sz.SeqΩ`, `rw [Sizes.seqHflow_eq_smul]` fails (error: the target is not type-correct under the `implicit` transparency level; "Application type mismatch: ω has type sz0.SeqΩ but is expected to have type (sz0.withLam 0).SeqΩ") and `simp [Sizes.seqHflow_eq_smul]` leaves the goal with the lemma unused (scratch compiles); `change (((Real.sqrt 0 : ℝ) : ℂ) • (sz0.withLam 0).seqXmat n ω) i j = 0` works (:263).
- The link between `STmaxLoop2g` and `GreenCore_loop (GreenCore_Gc ..)` is `change ‖loopFine …‖ ≤ _`, `rw [GreenOff_loop_eq hH]`, `change GreenCore_loop (GreenCore_Gc sz0 zSeq n 0 ω) p.1 p.2 ≤ _` (:343-346), `hH` the Hermitian proof (:337-342); the route (G)(iii) of GL4 needs the same link with `Finset.le_sup'` in place of `Finset.sup'_le` (:336).
- `intro U ξ ζ hξ hζ τ hτ D hD` opens `PrecL` and `StochDomAt` without `unfold`; a deterministic `ξ ≤ ζ`, `0 ≤ ζ` gives `ξ ≺ ζ` by `measure_mono_null`, `measure_empty` and `N^τ ≥ 1` (`det` :319-326).
- Names used by the examples (each compiled): `BAGt_sub_BAMfine` `BA/GreenSchur.lean:219`, `BAflowPert` `:196`, `BAflow_real` `:59`, `BAMB_row_sq_real` `BA/Ward.lean:125`, `GreenCore_carrier` `BA/GreenCore.lean:1532`, `GreenCore_avg_le` `:154`, `GreenCore_w_pos` `:151`, `GreenOff_loop_eq` `BA/GreenOff.lean:878`, `BAmF_sz0_im_pos` `BA/FlowPins.lean:1270`, `half_lt_t0` `:1254`, `flow_sz0` `:1214`; Mathlib `measure_mono_null`, `measure_empty`, `Real.one_le_rpow`, `inv_anti₀`, `pow_le_pow_right₀`, `Finset.sup'_le`, `Finset.sum_eq_single`, `Finset.single_le_sum`, `Complex.abs_im_le_norm`, `Real.rpow_neg_one`.
Not done here (open for the 1a-audit): the pins are statements; none is proved, and the stochastic content of GL2-GL6 rests on (G)(i)-(v). Compiled are: the statements elaborate; the premises of G5a, G6b and G5c fit (:225, :232); the hypothesis sets of GL1, GL3-GL6 are nonempty at `t ≡ 0` with `hinit` and `hFA` proved (`G=M`, `𝒦=0`, so `Δ=0` there) and at `t ≡ 1/2` modulo `hinit` and `hFA`, which stay hypotheses (the induction's output and G5b's pin; O4 of (d)); there is no Lean witness of `hinit` at `t > 0`. Paper-delta candidates: none new in this step (`T2408a-c` of (d) unchanged).

## (d) Open issues and paper-delta candidates
- O1 (partition, no sign-off needed by the T2403 precedent): the per-sequence diagonal law `BAGbEXPii` closes in G6a (GL2), so G6b has no diagonal row; the design table (`T2378-design.md` §5) lists it under G6b. If the dispatcher wants the line retired at G6b, 1b leaves `Test/Axioms.lean` untouched.
- O2: `GreenIBP_hll` and `BAFAav` exist only in probes (`t/T2402`, `t/T2401`); the "literal" matches are text matches, compiled at 1b only against G6a's own statements.
- O3: T2401 S6 (G5a) and GL6 both prove the averaged identity from `GreenCore_E3`; the names carry their stems, so whichever merges first does not clash.
- O4: the closure is eventual with analytic constants (`W` above `10^{196}` at `ε₀=1/10`); not a hypothesis of any target; instances are at `n=0` (hypotheses) and `t ≡ 0` (initialGT2).
- Paper-delta candidates: `T2408a` GL3 has no window hypothesis (paper `7_8:1917`: `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`); GL4 shows the lower end follows up to `N^ε` and `4/κ²`. `T2408b` GL2, GL3, GL4, GL6 carry `2 ≤ d` (paper `d ≥ 3`; as T2403a). `T2408c` the Lean local law is `PrecL ‖Δ‖_max ≺ Ψ` per sequence; the paper's `7_8:1930-1938` first display, and its second display `max_a|tr((G_t-M)E_a)| ≺ Ψ²` is `BAGavLGEX` (G6b), not GL3.

## (b) Stage 1b: script output (branch t/T2408, HEAD 2caa2d7; the full build and the diff are rerun at the repair HEAD dd10171; the first `date -u` of stage 1b printed Sun Oct 11 05:25:10 UTC 2026)
```
$ for h in 809bbd9 2e13630 2caa2d7; do git show $h:RBM3D/BA/GreenLocal.lean | wc -l; done   # stop line 2000: one file, no GreenLocal2
809bbd9 540 lines (Oct 11 05:37:04 UTC)  2e13630 789 lines (Oct 11 05:41:25 UTC)  2caa2d7 1005 lines (Oct 11 05:47:51 UTC)  
$ lake build RBM3D.BA.GreenLocal 2>&1 | tail -n 1
Build completed successfully (3791 jobs).
$ date -u; lake build RBM3D > full2.out 2>&1; echo $?; date -u; <audit lines of full2.out>; tail -n 1 full2.out   # HEAD dd10171; full library with #assert_rbm_axioms
Sun Oct 11 06:04:05 UTC 2026
0
Sun Oct 11 06:04:08 UTC 2026
info: RBM3D.lean:448:0: axiom audit: 11417 theorems, 3441 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 117 (borrowed 1, owed 51, structural 46, refuted 6, superseded 13).
Build completed successfully (4216 jobs).
$ python3 -I axrun.py   # #print axioms: the 16 public declarations; the 9 examples (renamed to theorems in a scratch copy)
public declarations: 16 ; examples: 9
ax_ex.lean: 9 x [propext, Classical.choice, Quot.sound]
ax_pub.lean: 16 x [propext, Classical.choice, Quot.sound]
$ python3 -I stmt.py | cut -c1-150   # statements extracted from the file; the four pin Props against the probe
def text equal to the probe's: GreenLocal_LocalLaw: True; GreenLocal_Floor: True; GreenLocal_omega: True; GreenLocal_Gav: True
theorem GreenLocal_floor_sample {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {κ δ : ℝ} (hκ : 0 < κ) (hM : ∀ u v,
theorem baGbEXPii_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPii d
theorem greenLocal_omega (d : ℕ) : GreenLocal_omega d
theorem greenLocal_localLaw (d : ℕ) (hd : 2 ≤ d) : GreenLocal_LocalLaw d
theorem greenLocal_floor (d : ℕ) (hd : 2 ≤ d) : GreenLocal_Floor d
theorem greenLocal_gav_of_fa (d : ℕ) (hd : 2 ≤ d) : GreenLocal_Gav d
theorem greenLocal_gii_of_le (d : ℕ) (hd : 2 ≤ d) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀
theorem greenLocal_ibp_premises (d : ℕ) (hd : 2 ≤ d) : GreenLocal_IBPPrem d
theorem greenLocal_gbEXPav_of_fa (d : ℕ) (hd : 2 ≤ d) : GreenLocal_Wiring d
probe GreenLocal_floor_sample_pin : def GreenLocal_floor_sample_pin : Prop := ∀ {d L W : ℕ} [NeZero L] [NeZero W] {G M : Matrix (Vtx d L W) (Vtx d L W
probe baGbEXPii_holds_pin : def baGbEXPii_holds_pin : Prop := ∀ d : ℕ, 2 ≤ d → BAGbEXPii d
$ python3 -I pincheck.py   # `example : <probe pin text> := <theorem>` for GL1-GL6 (probe 0547dc6)
pin examples: 6 ; exit code: 0
$ lake env lean docs/tickets/checks/T2408-check.lean; echo $?   # the ticket check file, on the branch
0
$ git diff main...t/T2408 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep "^[+-][^+-]" | cut -c1-90; git diff --stat main...t/T2408   # HEAD dd10171, main 1aa96d2
+import RBM3D.BA.GreenLocal
 RBM3D.lean                 |    1 +
 RBM3D/BA/GreenLocal.lean   | 1005 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2408Pins.lean |  370 ++++++++++++++++
 3 files changed, 1376 insertions(+)
$ grep -rnwE "<16 public names>" RBM3D RBM3D.lean | grep -v GreenLocal.lean/probe | wc -l; git grep (main 1f79c74) | wc -l; grep ../RBM1D ../RBM2D | wc -l
0 0 0
$ grep -n "^example" RBM3D/BA/GreenLocal.lean | cut -d: -f1   # the nine instances; namespace GreenLocalInst at :806
816 821 826 834 840 849 862 865 879 
$ python3 -I names.py   # `#check @n` of the 30 Mathlib/core names used, section (c)
used names: 30 ; #check exit code: 0 ; error lines: 0
```
Narrative (stage 1b):
- Proved in `BA/GreenLocal.lean` (one file, 1005 lines, namespace `RBM.BA`, stop line 2000, no `GreenLocal2`; the cut rule of (G)(v) was not needed): GL1 `GreenLocal_floor_sample` (:118), GL2 `baGbEXPii_holds` (:474), GL3 `greenLocal_localLaw` (:553), GL4 `greenLocal_floor` (:582), GL5 `greenLocal_omega` (:234), GL6 `greenLocal_gav_of_fa` (:693); the bridges `greenLocal_gii_of_le` (G5a, :759), `greenLocal_ibp_premises` (G5c, :781), `greenLocal_gbEXPav_of_fa` (G6b, :793). `pincheck.py`: GL1-GL6 have exactly the types of their probe pins.
- GL2: `GreenCore_diag` through the private one-sample lemma `GreenLocal_gii_sample` at `Φ = N^{τ₀}`, `δ = W^{-ε'}`, `ε' = min(ε₀, d/2)`, `τ₀ = min(τ/4, 𝔠ε')`; `GreenOff_pin_consts` gives (C1); `K_BAδ ≤ 1/2` and `C₂N^{2τ₀} ≤ N^τ` hold eventually, `C₂ = 8K_BA²C_gii` (private defs `GreenLocal_C2`, `GreenLocal_Cgl`) depends on `(d, κ, 𝔡)` only; the floor GL1 turns `W^{-d}` into `(4/κ²)𝓛max` inside `A_b`, `X_b`. No `g ≤ W^{-ε}`, no smallness of `‖M − m₀I‖`, no `(Cλ)^{|a−b|}`.
- GL3 = GL2 at `ε₀/2` + GL5 at `ζ = 𝔠ε₀/2` + (B); on `N^ζW^{-ε₀} ≤ W^{-ε₀/2}` the indicator is 1. GL4 = GL5 + (B) + `HighProbAt.nonempty` + GL1. GL6 = `GreenCore_E3` at `x = y = (a,o)` (the averaged identity), `baStab_holds`, `StochDomAt.of_subset`, `16κ⁻⁴N^{τ/2} ≤ N^τ` eventually.
- Two deliberate departures from the pseudo-code of (G)(v). (i) The wiring lemma is `greenLocal_gbEXPav_of_fa : GreenLocal_Wiring d`, `GreenLocal_Wiring d := GreenLocal_FAav d → BAGbEXPav d`, with the premise inside the `Prop` (as `BAGbEXPij'` holds `GreenCore_loopPrem`): no theorem takes an unproved named premise as a binder (`scanPremises`, `Test/Axioms.lean:421`), so the registry gets no new line. `GreenLocal_FAav` (:744) is the text of T2401's `BAFAav` under the stem. (ii) `GreenIBP_hll`, `GreenIBP_Omega` (probe copies) are not copied; `GreenLocal_IBPPrem` (:768) states the three premises of G5c literally.
- Instances (namespace `GreenLocalInst`, `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `ε₀ = 1/10`, `Ψ = W⁻¹`, `ζ = 1/120`): :816 GL2 and :821 `greenLocal_gii_of_le` at `ε₀/2` leave no hypothesis; :826-:865 (GL3, GL4, GL5, GL6, the wiring lemma, `greenLocal_ibp_premises`) are at `t ≡ 1/2` and keep `STInitialGT2gL` (the induction's output) resp. `GreenLocal_FAav` (owed by G5b) as hypotheses of the example; :879 at `t ≡ 0` (`X = 0`, `G_0 = M`, `𝒦 = 0`; the probe's example :246-368 with the theorems applied) discharges every hypothesis of GL1, GL3, GL4, GL5, GL6.
- Registry: `import RBM3D.BA.GreenLocal` added (diff above); `Test/Axioms.lean` is unchanged against the merge base: `BAGbEXPii` is proved by GL2 and its owed line stays until G6b (1a-audit F1; supervisor 2254 Q2). The full build passes (above).
- No port from RBM1D/RBM2D (grep 0). Copied inside RBM3D at 1c25de0, private under the stem: `GreenOff_gres_blockMat_true` (`BA/GreenOff.lean:819`), `GreenOff_card_vtx/_off`, `GreenOff_whp` (`:1266`, `:1269`, `:1274`), the identity `hbar` (`BA/GreenCore.lean:1291`) and `hstab'` (`:1487`).

## (c) Verified Mathlib names
All 30 names below were `#check`ed (`names.py`, exit 0) and are used: Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow, Real.rpow_natCast, Real.rpow_neg, Real.rpow_mul, Real.rpow_add, Real.one_le_rpow, Real.one_le_sqrt, Real.sqrt_eq_rpow, Real.rpow_nonneg, tendsto_rpow_atTop, pow_le_pow_left₀, div_le_iff₀, le_mul_of_one_le_left, mul_one_div, div_le_div_iff₀, Finset.single_le_sum, Finset.le_sup', Finset.sum_eq_single, Fintype.sum_prod_type, Fintype.card_subtype_le, Matrix.mul_diagonal, Matrix.inv_submatrix_equiv, Matrix.nonsing_inv_eq_ringInverse, Set.mem_ofPred_eq, MeasureTheory.measure_univ, MeasureTheory.measure_mono, Complex.abs_im_le_norm, norm_sub_norm_le, Filter.Eventually.of_forall. Present, unused: pow_le_pow_iff_left₀, sq_le_sq₀, abs_le_of_sq_le_sq' (own lemma `GreenLocal_le_of_sq_le`). Deprecated here: `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`), tactic `push_neg` (use `push Not`).

## (d′) Open issues (stage 1b) and paper-delta candidates
- P1: the ticket asks for a report of at most 250 lines; stage 1a (sections (a), (G), Verdicts, (a″), (d)) is 229 lines, so this report meets CLAUDE.md §6's 300 only.
- P2: at stage 1b main was 1f79c74 (`git diff --stat 1c25de0 1f79c74`: `RBM3D.lean` +2); at the repair main is 1aa96d2 (`git diff --stat 1c25de0 1aa96d2`: `RBM3D.lean` +5, `Test/Axioms.lean` +2). The branch adds one import after `import RBM3D.Chain.NewKLKGen` and, after the repair, does not touch `Test/Axioms.lean`, so the merge conflicts at the import line only; the hub adds the import after the last import line (CLAUDE.md §3 (A) 4). The probe `RBM3D/Probe/T2408Pins.lean` is on the branch (0547dc6) and is not to be merged.
- P3: `GreenLocal_FAav` is a text copy of `BAFAav` (`t/T2401` at `aec5a16`, `Probe/T2401Pins.lean:337-346`); when T2401's 1b merges, G6b checks that the two texts agree and applies `greenLocal_gbEXPav_of_fa` to `BAFAav d` (definitional unfolding).
- P4: no Lean witness of `STInitialGT2gL` at `t > 0` (the induction's output): the examples at `t ≡ 1/2` keep it as a hypothesis. The closure thresholds of (G)(iv) (`W` above `10^{196}` at `ε' = 1/10`) are eventual and analytic; no target has them as a hypothesis.
- P5 (partition, as (d) O1): `BAGbEXPii` is proved by GL2; its owed line in `Test/Axioms.lean` stays and retires at G6b.
- Paper-delta candidates: `T2408a`, `T2408b`, `T2408c` as in (d), unchanged. New `T2408d`: the Lean floor constant is `4/κ²` (the band lemma `inv_Wd_le_maxLoopPM`, `Green/EntryDom.lean:386`, has 4) since `|M_uu| = |m| ≥ κ` replaces `|m| = 1`; the paper's `lem_GbEXP_BA` has no floor statement (`grep -c -i floor paper/tex/7_8_light_weight.tex`: 0), so this is a Lean-side lemma.
## Repair (Repairer model: claude-opus-5-5; audit round 1, D1; `date -u`: Sun Oct 11 06:04:41 UTC 2026)
- D1: `git checkout 1c25de0 -- RBM3D/Test/Axioms.lean`, commit dd10171; `git diff main...t/T2408 -- RBM3D/Test/Axioms.lean | wc -l`: 0; `git show <main 1aa96d2 | t/T2408>:RBM3D/Test/Axioms.lean | grep -c "RBM.BA.BAGbEXPii,"`: 1, 1. No `.lean` file other than `Test/Axioms.lean` changed; `GreenLocal.lean` stays 1005 lines (`wc -l`). Full build at dd10171: (b) above. The (G) line `Registry: ... one line retired` of stage 1a is superseded by F1.
