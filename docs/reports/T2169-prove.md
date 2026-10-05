Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 03:47:42 UTC 2026

### (i) Exponent table (d = 3 unless stated; `lw = log W`, `ℓ = ℓ_s`, `w = lw³ℓ`, `ρ = lw⁴ℓ`, `R = 10w`, cluster radius `2R = 20w`; `π(β) = (|β₀−β₁|^{d−2}+1)⁻¹`)

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `40w ≤ ρ` (comparability at `2R`; `cltMom1_scale_comparable`, p=1) | `⇔ lw ≥ 40` (`ℓ>0`) | premise `40 ≤ lw` | szCL n=34: `lw−40 = 0.2025`; n=33: `lw = 39.5094` fails; n=100: `45.95` (script A) |
| 2 | `2d·w ≤ ρ` (`(prop:BD1)` window; `cltMom1_scale_bd1`) | `⇔ lw ≥ 2d = 6` | premise `2d ≤ lw` | szCL: `lw = (n+24) ln 2 ≥ 16.6` for all `n ≥ 0`; n=34: `lw−6 = 34.2025` |
| 3 | `ℓ_s = min(max(g/√|1−s|,1),L) ≥ 1` (`one_le_ellT`, `three_le_L`) | szCL, `g=1, s=0`: `ℓ=1` | `1 ≤ ℓ` | exact (script A) |
| 4 | regime `g²/L² ≤ 1−t` (zero mode of `Θ_t`, `cltMom1_weight_a1`) | szCL: `t=1−L⁻²`, `g=1`: `L⁻² ≤ L⁻²` | premise | equality (edge allowed); `1−s ≤ g²` not used here |
| 5 | `‖t·m₁m₂‖ < 1` | `‖mE E‖=1` (`norm_mE`, `\|E\|≤2`), `0≤t<1` | `t<1` | szCL `1−t = L⁻² > 0` |
| 6 | weight constant `M_w = C₅(1+2^{d−1})C₆·d`, `M = 4^d M_w` | `C₅(d,Λ)`, `C₆(d,Λ,κ)` existential (`prop5Decay_holds`, `prop6Diff1_holds`); `4^3 = 64` | fixed after `(d,Λ,κ)`, before `sz,n,E,s,t,σ,a,p`; `M>0` | no numeric value in the files; limit rows carry `M_w` as a parameter |
| 7 | `‖Z_β‖π(β) ≤ uw(β₀)G(β₀−β₁)`; on the region `π = G`, both profiles `≤ 1` | `‖Z_β‖ ≤ M_w·w` on the region, `Z=0` off it | `\|E\|≤2, κ≤Im mE, 0<g≤Λ, 3≤L, 2d≤lw` | orientations `β₀−a_i` vs `a_i−β₀` bridged by `zdistInf_sub_comm` |
| 8 | comparability of `uw` at radius `20w`: profiles `≤ 2^{d−2}, 2^{d−1} ≤ 2^d` each, total `4^d` | `4^3 = 64` | `2·20w = 40w ≤ ρ` (row 1) | toy (B): ratio `64 = 4^d` from the `M ↦ 4^d M` factor, profile ratio `1` |
| 9 | envelope `BY = A^{6/5}(η_s⁻² + Σ_β‖K_β‖)`, `A = g²W^d`; `‖𝗕‖ ≤ BY` (`norm_Lloop_le`, `k+1=2`) | `\|E\|<2, s<1` (`η_s=(1−s)Im mE>0`) | `s<1` | szCL `s=0,E=0`: `η_s = 1`; the bound `Σ‖K‖ ≤ L⁶K₀W⁻³` is S5-25's (`LemDecCalE.lean:88`) |
| 10 | `‖𝗕_β‖/π(β) ≤ BY(w^{d−2}+1)` on the window; `≤ L^{2d}` window labels | `w^{d−2} = w` | `\|β₀−β₁\|≤w` | toy: `B(w+1) = 2 = Λ'`, event `{Λ'<·}` empty (`q₁=0`) |
| 11 | tuple bound `‖𝔼∏X‖ ≤ ∏π·2^{2p}𝔼Ymax^{2p}`; `𝔼Ymax^{2p} ≤ Λ'^{2p} + (BY(w^{d−2}+1))^{2p}·card·q₁` | centring `(Ymax+𝔼Ymax)^{2p} ≤ 2^{2p−1}(…)`, Jensen | `q₁ ≥ 0` (`Λ'` free: `Λ'<0` forces `q₁ ≥ 1`) | `2^{2p}` as in `CltMom2.rhs` |
| 12 | paired sum `PB = (2p)^{2p}(2cs)^p(C_d M lw^{12})^{2p}(ℓ⁴/(\|a₁−a₂\|^{d−2}+1))^{2p}` | `cs_3 = 24`, `C_3 = 317587968` (script A); `lw^{24p}` explicit | `3 ≤ d, 1 ≤ lw, 1 ≤ ℓ, 0 ≤ M` | equals the right side of `cltMom1_paired_moment_le` |
| 13 | isolated part `εf(Σ_β‖Z_β‖)^{2p}`, `Σ‖Z‖ ≤ L^{2d} M_w w` | nonzero weight forces all labels in the window; isolated ⇔ `¬Paired(10w)` (`cltMom1_not_paired_iff`) | `0 ≤ εf` | exact split, no overlap loss |
| 14 | `c_n = (1−s)²/(g⁴A^{6/5})` | `Θ·(STLKM−∫)·ΔΘ = (Z/g⁴)(STcltB−∫STcltB)/A^{6/5}` | `\|E\|<2, s<1, g>0` | exact identity (S5-25 uses `1−s ≤ g²` for `c_nℓ⁴ ≤ A^{-6/5}`) |
| 15 | Markov `P(θ<‖fluc‖) ≤ rhs/θ^{2p}` | `meas_gt_le_of_moment` | `θ>0` | — |
| 16 | consumer limit (lesson 14): `θ = N^τℓ⁴/(\|a₁−a₂\|^{d−2}+1)`, `Λ'=N^{τ/4}`, `q₁=N^{−D₁}`, `εf=W^{−D'}` | main term `≍ N^{−3pτ/2}·lw^{24p}` | `3pτ/2 > D`, i.e. `p > 2D/(3τ)`; `D₁ ≳ 10p`, `D' ≳ 30p` | script C: `(τ,D)=(1/10,1)`: `p=7` margin `1.05−1`, threshold `n=19163` (`M_w=1`); `p=20`: `n=969/1043/1117` for `M_w=1,10³,10⁶`; `p=40,D=3`: `n=1376/1475/1572` |

Quantifier orders are as pinned: `M` after `(d,Λ,κ)`; `p, D` before `∀ᶠ n` in `TailStmt`; `a : Fin 2 → Zd d (sz.L n)` after `∀ᶠ`. `IsoHyp` at `(n,σ,p,W^{−D})` is the inner clause of `STCltIsoConcl` (`Step5Pins.lean:417-423`); the `∀ᶠ n` of target 6 is that one only. The row 16 threshold is `n ≈ 10³` (`N ≈ 10^{10³}`) since `lw^{24p}` is absorbed by `N^{3pτ/2−D}` (the paper's `≺`); the targets themselves have no such threshold (every premise is per `n ≥ 34`).

### (ii) One concrete nondegenerate instance

Script A/B: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2169/inst.py` (exact `Fraction`/integer arithmetic; `zd` = periodic `|·|_∞` on `Z_L^3`). Data A: `szCL` (`L=2m⁵, W=2^m, lam=1, m=n+24`), `E=0, s=0, t=1−L⁻², σ=(+,−), a=(0,0)`, `β⁰=(x_n,x_n)`, `x_n=(m⁵,0,0)`. Data B: `d=3, L=83, a₁=0, a₂=(0,0,1)`, `b⁰=((41,41,41),(41,41,42))`, `b¹=((36,41,41),(36,41,40))`.
```
cs_3= 24 C_3= 317587968
n=33: L=1203384114 log10W=17.16 lw=39.5094 lw-40=-0.4906 lw-2d=33.5094 ell_s=1.0 w=61673.8 rho=2436695.5 40w<=rho:False regime lam^2/L^2=1/1448133325827564996 <= 1-t=1/1448133325827564996: True; |x_n|=m^5=601692057 > rho: True; |x_n|<=L/2: True
n=34: L=1312713536 log10W=17.46 lw=40.2025 lw-40=0.2025 lw-2d=34.2025 ell_s=1.0 w=64977.1 rho=2612244.5 40w<=rho:True regime lam^2/L^2=1/1723216827597623296 <= 1-t=1/1723216827597623296: True; |x_n|=m^5=656356768 > rho: True; |x_n|<=L/2: True
n=100: L=58632501248 log10W=37.33 lw=85.9503 lw-40=45.9503 lw-2d=79.9503 ell_s=1.0 w=634952.8 rho=54574351.6 40w<=rho:True regime lam^2/L^2=1/3437770202596721557504 <= 1-t=1/3437770202596721557504: True; |x_n|=m^5=29316250624 > rho: True; |x_n|<=L/2: True
Im mE(0)= 1.0 ; for |E|<=1/2: Im mE >= 0.9682458365518543  (>=1/20 slack 0.9182458365518542 )
zd(a1-b0_0) 41 zd(a2-b0_0) 41 window |b0_0-b0_1| 1
zd(a1-b1_0) 41 zd(a2-b1_0) 41 window |b1_0-b1_1| 1 dist of first labels 5 (<=20w=20, <R=10)
|a1-a2|= 1
target2: c=uw*G = 1/141288 = 7.0777419172187305e-06  ||Z||=c/pi = 1/70644  pi= 1/2
target2: window tail event B*(|b0-b1|+1)= 2 vs Lam'= 2  (event {Lam'<.} empty)
target2: LHS int|Z(Y-intY)|^2 = ||Z||^2 = 2.0037772258702028e-10  <= rhs = 7.746210617730741e+19  <= rhs/theta^2 same; paired (b0,b0): dist first labels 0 < R=10
target2: tuples isolated with all labels in window: eps_f=1 >= |E[X X']| since |Y|<=1 -> ok
4c far: b0 True True
4c far: b1 True True
4c z values {(41, 41, 41): (Fraction(1, 141288), 7.0777419172187305e-06), (36, 41, 41): (Fraction(1, 141288), 7.0777419172187305e-06)}
4c beta=(41, 41, 41) beta'=(41, 41, 41) dist=0<=20w:True  z(beta')=7.0777419172187305e-06 <= uw(4^d)*G=0.00045297548270199875: True; ratio=64.0<=4^d=64
4c beta=(41, 41, 41) beta'=(36, 41, 41) dist=5<=20w:True  z(beta')=7.0777419172187305e-06 <= uw(4^d)*G=0.00045297548270199875: True; ratio=64.0<=4^d=64
4c beta=(36, 41, 41) beta'=(41, 41, 41) dist=5<=20w:True  z(beta')=7.0777419172187305e-06 <= uw(4^d)*G=0.00045297548270199875: True; ratio=64.0<=4^d=64
4c beta=(36, 41, 41) beta'=(36, 41, 41) dist=0<=20w:True  z(beta')=7.0777419172187305e-06 <= uw(4^d)*G=0.00045297548270199875: True; ratio=64.0<=4^d=64
```
Reading. A: at n=34 (`lw=40.2025>40`) and n=100: window `|β⁰₀−β⁰₁|=0 ≤ w`, `|x_n|=m⁵>ρ` (far from `a=(0,0)`), `(β⁰,β⁰)` paired at `R=10w` (distance `0<R`), regime equality, `Im mE(0)=1`; for target 6, `|E_n| ≤ 1/2` (`abs_lemE_le`, `zCL.re=1/2`), so `Im mE(E_n) ≥ 0.968 ≥ 1/20`. n=33 violates `40 ≤ lw`, consistent with the ticket (instances use `n ≥ 34`). B: target 2 (`lw=ℓ=1`): `‖Z_{b⁰}‖=1/70644`, `p=1`, `Y=±1`, `Λ'=2`, `q₁=0`, `εf=1`: LHS `2.0e-10 ≤ rhs 7.7e19`; isolated tuples satisfy `‖𝔼∏X‖ ≤ 1 = εf` as `|Y|≤1`. Target 4c (`w=1, ρ=40, M=1`): the two-point `z` (at `b⁰, b¹`, both far at distance 41>40, first labels 5 ≤ 20w apart) meets the hypothesis with equality and the conclusion with factor `4^d=64`; the ticket's point mass at `b⁰` is the case `z(b¹)=0`.

External pin `STCltIsoConcl` (target 6) and `DomHyp` (supplied by S5-25 from `STGdecayW`): concrete limit computation, script C (`python3 .../scratchpad/T2169/limit2.py`, `log10` domain; `BY ≤ W^{18/5}(1+K₀L⁶W⁻³)` with illustrative `K₀=1`; worst `|a₁−a₂|=L/2` in the isolated term; the `q`-term slack is `>10^5` in `log10`, so a `K₀` polynomial in `N` is absorbed; `p=7` at `M_w ≥ 10³` has no solution below `n=20000`, as `1.05−1` leaves no room). Columns are `log10` of the three terms of `rhs/θ^{2p}` against `log10 N^{−D}`:
```
Mw=1 p=7 D=1 D1=70 D'=210: n=19163 log10N=17393 main=-17393 q=-949565 iso=-1234984 target=-17393
Mw=1 p=20 D=1 D1=200 D'=600: n=969 log10N=943 main=-944 q=-146934 iso=-178516 target=-943
Mw=1 p=40 D=3 D1=400 D'=1200: n=1376 log10N=1312 main=-3939 q=-409344 iso=-506559 target=-3937
Mw=1000 p=7 D=1 D1=70 D'=210: None
Mw=1000 p=20 D=1 D1=200 D'=600: n=1043 log10N=1010 main=-1011 q=-157315 iso=-191983 target=-1010
Mw=1000 p=40 D=3 D1=400 D'=1200: n=1475 log10N=1402 main=-4209 q=-437143 iso=-542710 target=-4207
Mw=1e+06 p=7 D=1 D1=70 D'=210: None
Mw=1e+06 p=20 D=1 D1=200 D'=600: n=1117 log10N=1077 main=-1078 q=-167691 iso=-205454 target=-1077
Mw=1e+06 p=40 D=3 D1=400 D'=1200: n=1572 log10N=1490 main=-4471 q=-464368 iso=-578131 target=-4471
```

### Verdict per target
- Target 1 (vocabulary, six statements): PASS. `Z, fluc, off` are the `(eq:2p_product)` weight, window and off-window pieces (`3_5:2213-2220`); `BY, DomHyp, IsoHyp, rhs` and the six `Stmt` agree with rows 6-16; no hypothesis set is empty (scripts A/B).
- Target 2 (`cltMom2_expand`, `_moment_le`, `_markov`): PASS. Engine hypotheses hold in the toy (B); route and constants close (rows 10-13, 15).
- Target 3 (`cltMom2_decomp`): PASS. Exact identity from `STcltB = A^{6/5}·STLKM`, `Z/g⁴ = Θ·ΔΘ`, complementary regions (`≤` vs `>` window), far orientation as in `STfFar` (row 14).
- Target 4 (`cltMom2_norm_stcltB_le`, `_weight_le`, `_hzu`): PASS. 4a from `norm_Lloop_le` (`\|E\|<2, s<1`); 4b from `cltMom1_weight_a1/a2` with `M_w` (row 7; its premises `\|E\|≤2, 2d≤lw`, regime, `3≤L` are available); 4c comparability `2^d·2^d = 4^d` (rows 8, B).
- Target 5 (`cltMom2_moment_fixed`): PASS. `40w ≤ ρ` from `40 ≤ lw` (row 1), `hzu` from 4b+4c with `M = 4^d M_w`, tuples literally `STcltX … (decide (p ≤ k.val))`.
- Target 6 (`cltMom2_tail_eventually`): PASS. `εf = W^{−D} ≥ 0` (`W>0`); the clause of `STCltIsoConcl` at `(p,D)` is `IsoHyp … (W^{−D})`; row 16: the consumer exponent closes for `p > 2D/(3τ)`.
- Overall: PASS, no BLOCKED input. Open points for later stages, not defects: `C₅, C₆` have no numeric value in the files (row 6); the polynomial bound of `Σ‖K‖` entering `D₁` is S5-25's (row 9).

## (b) Script output — Mon Oct  5 04:20:21 UTC 2026

```
$ date -u
Mon Oct  5 04:18:32 UTC 2026
$ cd RBM3D-wt/T2169 && git log -1 --format="%h %s" && git diff main...t/T2169 --stat
6931a27 T2169: S5-24 CLT moment bound, probabilistic half (Evolution/CltMoments2)
 RBM3D/Evolution/CltMoments2.lean | 1706 ++++++++++++++++++++++++++++++++++++++
 1 file changed, 1706 insertions(+)

$ lake build RBM3D.Evolution.CltMoments2 2>&1 | tail -n 12
Note: This linter can be disabled with `set_option linter.style.longLine false`
ℹ [3817/3817] Replayed RBM3D.Evolution.CltMoments2
info: RBM3D/Evolution/CltMoments2.lean:1693:0: 'RBM.Evol.cltMom2_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1694:0: 'RBM.Evol.cltMom2_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1695:0: 'RBM.Evol.cltMom2_markov' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1696:0: 'RBM.Evol.cltMom2_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1697:0: 'RBM.Evol.cltMom2_norm_stcltB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1698:0: 'RBM.Evol.cltMom2_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1699:0: 'RBM.Evol.cltMom2_hzu' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1700:0: 'RBM.Evol.cltMom2_moment_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltMoments2.lean:1701:0: 'RBM.Evol.cltMom2_tail_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3817 jobs).

$ grep -nE "sorry|admit|native_decide|^axiom|^[a-z ]*axiom " RBM3D/Evolution/CltMoments2.lean | wc -l
       0
$ wc -l RBM3D/Evolution/CltMoments2.lean
    1706 RBM3D/Evolution/CltMoments2.lean
```

Statements extracted by script (`python3 extract.py`, line numbers of the committed file; targets 3-6 are `theorem … : CltMom2.…Stmt d`,
`CltMom2.HzuStmt` without `d`, whose texts are the verbatim check-file definitions):
```
312: theorem cltMom2_expand [IsProbabilityMeasure P] (hYm : ∀ β, Measurable (Y β)) (hYB : ∀ β ω, ‖Y β ω‖ ≤ B)
313:     (Z : (Fin 2 → Zd d L) → ℂ) (p : ℕ) :
314:     ∫ ω, ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ ^ (2 * p) ∂P ≤
315:       ∑ b : Fin (2 * p) → (Fin 2 → Zd d L), (∏ k, ‖Z (b k)‖) *
316:         ‖∫ ω, ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω ∂P‖ := by

628: theorem cltMom2_moment_le [IsProbabilityMeasure P] (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz Λ' q₁ εf : ℝ}
629:     (hlw : 1 ≤ lw) (hℓ : 1 ≤ ℓ) (hMz : 0 ≤ Mz) (hq₁ : 0 ≤ q₁) (hεf : 0 ≤ εf) (a₁ a₂ : Zd d L)
630:     (hYm : ∀ β, Measurable (Y β)) (hYB : ∀ β ω, ‖Y β ω‖ ≤ B) (Z : (Fin 2 → Zd d L) → ℂ)
631:     (hZ : ∀ β : Fin 2 → Zd d L, lw ^ 3 * ℓ < ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) → Z β = 0)
632:     (hzu : ∀ β β' : Fin 2 → Zd d L,
633:       0 < ‖Z β‖ * (1 / (((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)) →
634:       ((zdistInf d L (β 0 - β' 0) : ℕ) : ℝ) ≤ 20 * (lw ^ 3 * ℓ) →
635:       ‖Z β'‖ * (1 / (((zdistInf d L (β' 0 - β' 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤
636:         CltMom1.uw a₁ a₂ (lw ^ 4 * ℓ) (lw ^ 3 * ℓ) Mz (β 0) * CltMom1.G d L (lw ^ 3 * ℓ) (β' 0 - β' 1))
637:     (hdom : ∀ β : Fin 2 → Zd d L, ((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ≤ lw ^ 3 * ℓ →
638:       P {ω | Λ' < ‖Y β ω‖ * (((zdistInf d L (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1)} ≤ ENNReal.ofReal q₁)
639:     (hiso : ∀ b : Fin (2 * p) → (Fin 2 → Zd d L),
640:       (∀ k, ((zdistInf d L ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤ lw ^ 3 * ℓ) →
641:       (∃ i, ∀ j, j ≠ i → 10 * lw ^ 3 * ℓ ≤ ((zdistInf d L ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
642:       ‖∫ ω, ∏ k : Fin (2 * p), CltMom2.X P Y (b k) (decide (p ≤ k.val)) ω ∂P‖ ≤ εf) :
643:     ∫ ω, ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖ ^ (2 * p) ∂P ≤
644:       2 ^ (2 * p) * (Λ' ^ (2 * p) + (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) *
645:           (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) *
646:         (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
647:           ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
648:             (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
649:       εf * (∑ β, ‖Z β‖) ^ (2 * p) := by

747: theorem cltMom2_markov [IsProbabilityMeasure P] (hd : 3 ≤ d) (p : ℕ) {lw ℓ Mz Λ' q₁ εf : ℝ}   [... the hypotheses of cltMom2_moment_le, then:]
762:     (θ : ℝ) (hθ : 0 < θ) :
763:     P {ω | θ < ‖∑ β, Z β * (Y β ω - ∫ ω', Y β ω' ∂P)‖} ≤
764:       ENNReal.ofReal ((2 ^ (2 * p) * (Λ' ^ (2 * p) + (B * ((lw ^ 3 * ℓ) ^ (d - 2) + 1)) ^ (2 * p) *
765:           (Fintype.card (Fin 2 → Zd d L) : ℝ) * q₁) *
766:         (((2 * p : ℕ) : ℝ) ^ (2 * p) * (2 * CltMom1.cs d) ^ p *
767:           ((CltMom1.Cd d * Mz * lw ^ 12) ^ (2 * p) *
768:             (ℓ ^ 4 / (((zdistInf d L (a₁ - a₂) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p))) +
769:       εf * (∑ β, ‖Z β‖) ^ (2 * p)) / θ ^ (2 * p)) := by

975: theorem cltMom2_decomp (d : ℕ) : CltMom2.DecompStmt d := by
992: theorem cltMom2_norm_stcltB_le (d : ℕ) : CltMom2.BYStmt d := by
1009: theorem cltMom2_weight_le (d : ℕ) : CltMom2.WeightStmt d := by
1090: theorem cltMom2_hzu : CltMom2.HzuStmt := by
1147: theorem cltMom2_moment_fixed (d : ℕ) : CltMom2.MomentStmt d := by
1198: theorem cltMom2_tail_eventually (d : ℕ) : CltMom2.TailStmt d := by
```

Target 1 and the isolation clause (`python3 verify_defs.py`):
```
diff lines (check text vs section 1, namespace line stripped): 0

IsoHyp body == STCltIsoConcl inner clause (lines 417-423, (E n)->E, (s n)->s, W^(-D)->εf): True
```

Constants of section (a) row 12: `lake env lean const.lean` with `example : CltMom1.Cd 3 = 317587968 := by unfold CltMom1.Cd; norm_num` and
`example : CltMom1.cs 3 = 24 := by unfold CltMom1.cs; norm_num` -> exit=0.

Registry pre-check (`#assert_rbm_axioms` with the module imported, in a scratch file):
```
$ lake env lean precheck0.lean   # import RBM3D; #assert_rbm_axioms   (library without the new module)
axiom audit: 5051 theorems, 1749 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 0, owed 63, structural 19).
registry: 1 borrowed + 85 owed + 49 structural; 53 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ lake env lean precheck.lean    # import RBM3D; import RBM3D.Evolution.CltMoments2; #assert_rbm_axioms
axiom audit: 5060 theorems, 1763 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 82 (borrowed 0, owed 63, structural 19).
registry: 1 borrowed + 85 owed + 49 structural; 53 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -c "error\|CltMom2" precheck.out
0
```

Compiled nonempty instances (`python3 inst_list.py`: line of each `example`, its docstring head, the theorem it applies; nonvacuity rows apply none):
```
1333: **Instance of `cltMom2_expand`** (`d = 3`, `L = 83`, `p = 1`): `Ω = Bool` with -> cltMom2_expand
1339: **Instance of `cltMom2_moment_le`** (`d = 3`, `L = 83`, `p = 1`, `lw = ℓ = 1`, -> cltMom2_moment_le
1346: **Instance of `cltMom2_markov`** (the same data, `θ = 1`). -/ -> cltMom2_markov
1406: **Instance of `cltMom2_hzu`** (`d = 3`, `L = 83`, `w = 1`, `ρ = 40`, `M = 1`,  -> cltMom2_hzu
1523: **Instance of target 4a** (`cltMom2_norm_stcltB_le`) at `szCL`, `E = 0`, `s =  -> cltMom2_norm_stcltB_le
1529: **Instance of target 4b** (`cltMom2_weight_le`) at `szCL`, `E = 0`, `s = sCL n -> cltMom2_weight_le
1543: **Instance of target 3** (`cltMom2_decomp`) at the same data, every `n`, every -> cltMom2_decomp
1555: **Instance of target 5** (`cltMom2_moment_fixed`) at the same data for every ` -> cltMom2_moment_fixed
1604: **Instance of target 6** (`cltMom2_tail_eventually`) at `(szCL, STflowE zCL, s -> cltMom2_tail_eventually
1628: **Nonvacuity** (CLAUDE.md §4 step 2): for every `n`, the label `β⁰ = (x_n, x_n -> -
1666: **Nonvacuity** of the isolated/paired split at `p = 1`: `(β⁰, β⁰)` is paired a -> -
```
Private toy/data helpers used by them: `cltMom2_unifBool`, `cltMom2_signY`, `cltMom2_Z0`, `cltMom2_z40`, `cltMom2_toy_hZ/hzu/hdom/hiso`,
`cltMom2_domHyp_zero`, `cltMom2_isoHyp_envelope`.

Name clashes and ports:
```
$ git -C /Users/junyin/Lean_proof/RBM3D grep -il cltMom2 main -- "RBM3D/*.lean" "RBM3D.lean" | wc -l      # new names on main
       0
$ grep -rl "CltMom2\|cltMom2" RBM3D RBM3D.lean     # in the T2169 worktree
RBM3D/Evolution/CltMoments2.lean
$ grep -nE "^(private )?(noncomputable )?(theorem|def|abbrev|instance|lemma)" RBM3D/Evolution/CltMoments2.lean | grep -v "private" | grep -vE "cltMom2_|CltMom2\." | wc -l   # unpinned public helpers without the prefix
       0
$ grep -cE "^private (noncomputable )?(theorem|def|abbrev|instance)" RBM3D/Evolution/CltMoments2.lean   # private helpers
75
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf ; git -C ../RBM2D --no-optional-locks log -1 --format=%h
c9a24cf
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/CltMoments.lean
 RBM2D/Evolution/CltMoments.lean | 240 ++++------------------------------------
 1 file changed, 24 insertions(+), 216 deletions(-)
```

Narrative (facts from the files and the logs above).
- All nine target theorems compile at the pinned statements; the seven definitions and six `Stmt` of target 1 are a
  verbatim copy of the check file (script diff: 0 lines); no stop-and-report; nothing added to, removed from or
  weakened in a pinned statement.  No (a') was written; the constants of section (a) row 12 (`C_3`, `cs_3`) were re-checked by script (block above).
- File layout (`grep "^/-! #"`): vocabulary L78-225, engine L226-782, decomposition L783-985, deterministic inputs
  L986-1131, fixed `n` L1132-1208, instances L1209-1706 (11 `example`s, 75 private helpers); 1706 lines against the
  ticket's estimate of 1450.
- Target 2 (`Ω : Type*`, `[IsProbabilityMeasure P]`; hypotheses `3 <= d`, `1 <= lw`, `1 <= ℓ`, `0 <= Mz`, `0 <= q₁`,
  `0 <= εf`, measurability, envelope `B`, `hZ`, `hzu`, `hdom`, `hiso`, no `1 <= p`).  Route: `cltMom2_expand`; per
  tuple `b` the weight `∏|Z|` vanishes unless every label is in the window; a paired window tuple is bounded by
  `∏π(b_k) 2^{2p} 𝔼 ymax^{2p}` and the paired sum by `cltMom1_paired_moment_le`; an unpaired tuple is isolated
  (`cltMom1_not_paired_iff`, `mul_assoc`) and bounded by `hiso`.  `ymax` is the maximum of `|Y_β| q(β)` over the
  window labels (`0` off the window), so `hdom` is needed on window labels only; the case `Λ' < 0` is closed
  inside `cltMom2_Emax_pow_le` (the event of the window label `0` is everything, hence `q₁ >= 1`).
- Target 3: exact identity, no inequality: `cltMom2_integral_fFar` (copy of the private `meanFar_integral_fFar`), the
  termwise lemma `cltMom2_term` (algebra `cltMom2_weight_algebra`, `STcltX … false = A^{6/5}(STLKM - ∫ STLKM)`), the
  reindexing `β = ![u₀, u₁]` (`piFinTwoEquiv`), far/window/complement as `if`-sums.
- Target 4: `M = C₅(1 + 2^{d-1}) C₆ d` from `cltMom1_weight_a1/a2`; `cltMom2_hzu` has the factor `4^d = 2^d 2^d` from
  `cltMom1_comparable_weights` at `r = 20 w`.  Target 5: `Y = STcltB`, `B = BY`, `M = 4^d M_w`, `40 w <= ρ` from
  `cltMom1_scale_comparable` (`p = 1`); `DomHyp`/`IsoHyp` are consumed literally (`exact`, no translation lemma).
  Target 6 is `cltMom2_moment_fixed` with `εf = W^{-D} >= 0` inside `filter_upwards`.
- Instances: target 2 on `Ω = Bool` (uniform measure, `Y = ±1`, `𝔼Y = 0` proved) at the S5-23 point-mass data;
  `cltMom2_domHyp_zero` (event of `DomHyp` empty at `Λ' = BY (w+1)`, `q₁ = 0`) and `cltMom2_isoHyp_envelope`
  (`εf = (2 BY)^{2p}`) discharge `DomHyp`/`IsoHyp` at `szCL`; target 6 keeps the nine stochastic pins of
  `inst_cltIso` (`STKbound … STLKU`) as hypotheses and discharges every per-`n` premise for `n >= 34`.
- Deviations from the ticket's instance list: (i) the `cltMom2_hzu` instance uses the two-point row `{β⁰, β'}` (equal
  weights `c₄₀`), the ticket's point mass is the sub-case `z β' = 0`; (ii) for target 6, `|E_n| <= 1/2` is
  `abs_lemE_le` and `1/2 <= Im mE(E_n)` is the argument of `lemT_zCL`, so `v3_premises_of_stFlow` and
  `nqGood1_mE_im_ge` are not used (grep count 0) and `Green/Pins`, `Induction/NQGood1` are not imported.
- Imports added: `Mathlib.Analysis.Convex.Integral` (`ConvexOn.map_integral_le`), `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`
  (`integral_fintype`), `RBM3D.Gauss.Domination`.  `RBM3D/Test/Axioms.lean` is untouched: the registry pre-check finds no
  new premise (82 before and after), so `DomHyp`, `IsoHyp` need no `structuralProps` line.
- `lake build` of the worktree library (3941 jobs) succeeds; `RBM3D.lean` does not yet import the module (the hub does
  at merge), so the pre-check above imports it explicitly.  RBM2D `CltMoments.lean` changed after `c9a24cf` (stat above);
  the ports cite `c9a24cf` as pinned.

## (c) Verified Mathlib names (each elaborates under `#check`; `lake env lean names.lean`)
integral_fintype, ConvexOn.map_integral_le, convexOn_pow, Integrable.of_finite, measurable_of_finite,
norm_integral_le_of_norm_le_const, norm_integral_le_integral_norm, integral_finsetSum, measureReal_mono,
measureReal_iUnion_fintype_le, probReal_univ, integral_indicator_const, Finset.measurable_sup',
Finset.exists_mem_eq_sup', Finset.le_sup', Finset.sup'_le, Finset.prod_univ_sum, Finset.prod_le_prod₀,
Finset.single_le_sum, Fintype.piFinset_univ, piFinTwoEquiv, Fintype.sum_equiv, Complex.mul_conj', RCLike.norm_conj,
pow_le_pow_left₀, pow_lt_pow_right₀, Real.log_two_gt_d9, Real.rpow_nonneg, Set.mem_ofPred_eq,
ENNReal.inv_two_add_inv_two, Filter.eventually_ge_atTop, Real.sqrt_le_sqrt, Real.sqrt_sq
- Verified absent under these names: `MeasureTheory.ConvexOn.map_integral_le` (the name is root-level `ConvexOn.map_integral_le`, needs
  `import Mathlib.Analysis.Convex.Integral`), `MeasureTheory.integral_complex_ofReal` (root-level `integral_complex_ofReal`).
- `MeasureTheory.integral_fintype` is not reachable from the `RBM3D.Gauss.Domination` chain: `import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`.
- Deprecated in this Mathlib (warnings in the trial compile): `if_pos`, `if_neg` (use `simp only [h, ↓reduceIte]`), `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`).

## (d) Open issues and paper-delta candidates
- Open for S5-25 (`Evolution/CltFar`): supply `CltMom2.DomHyp` from `STGdecayW` at `u = s` (`q₁ = N^{-D₁}`, as `meanFar_bad_le`); bound
  `CltMom2.off` by `(eq:propcalB)`; bound `Σ_β ‖𝒦^{(2)}‖` inside `CltMom2.BY` (section (a), row 9); choose `p`; use `1-s <= g²` for
  `c_n ℓ_s⁴ <= A^{-6/5}`; take the union over the index set inside `Prec`.
- The target-6 instance leaves the nine stochastic premises of `inst_cltIso` as hypotheses (other gates' pins); `CltMom2.IsoHyp` is
  supplied by `stCltIso_holds` only through them.
- No registry line, no `L^d <= W^K` premise, no `Prec`, no `∀ n` premise was needed (ticket §29 checklist items 3-5 hold as written).
- Paper-delta candidates (`T2169a…`, numbers assigned by the dispatcher):
  - `T2169a`: the per-factor `≺` of the first line of `(eq:2p_product_pair)` (`|𝕀𝔼𝗕| ≺ 1/(|b₁-b₂|^{d-2}+1)` inside `𝔼`) is made explicit as the
    profile-normalised maximum over the window with the tail `(Λ', q₁)` (`CltMom2.DomHyp`) and the a.s. envelope `CltMom2.BY`; the `≺ ⟹ 𝔼` step is
    the factor `(Λ'^{2p} + (BY (w^{d-2}+1))^{2p} |labels| q₁)` of `CltMom2.rhs` (D370).
  - `T2169b`: the `O(W^{-D})` of `(eq:2p_product)` is the separate exact term `CltMom2.off` (`f^{far} - 𝔼f^{far} = c_n · fluc + off`,
    `c_n = (1-s)²/(ilambda⁴ A^{6/5})`), not an error inside the moment.
  - `T2169c`: the comparability at the cluster radius `2R = 20 w` costs the factor `4^d` (`2^d` per profile) and the weight constant is
    `M_w = C₅ (1 + 2^{d-1}) C₆ d` (the factor `1 + 2^{d-1}` absorbs the zero mode under `g²/L² <= 1-t`); `log W >= 40`, `log W >= 2d` are premises.
  - `T2169d`: the moment bound is stated at one `n` with `|𝔼 ∏ 𝕀𝔼𝗕| <= εf` for isolated window tuples, explicit `Λ', q₁, εf`, the centring
    `2^{2p}` and the explicit `lw^{24p}` of `cltMom1_paired_moment_le` (D393).
