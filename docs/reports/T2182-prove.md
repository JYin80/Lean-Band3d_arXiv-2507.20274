Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 06:17:49 UTC 2026

### (i) Exponent table (`d ≥ 3`; `g = sz.lam n`, `A = STAI = g²W^d`, `lw = log W`, `ℓ = ℓ_s = min(max(g/√(1−s),1),L)`, `w = lw³ℓ`, `R_a = |a₁−a₂|^{d−2}+1`, `κ' = min κ ½`, `N = (WL)^d`, `c₀ = (1+2^{d−1})^{6/5}`, `c_Θ = C₅(1+2^{d−1})` with `C₅ = C₅(d,𝔡⁻¹)` of `prop5Decay_holds`)

Size facts used throughout: `L^d ≤ N`, `W^d ≤ N`, `N ≤ W^{1/𝔠}` (`Bandwidth`), `g ≤ 𝔡⁻¹`, `g ≥ W^{−d/2+𝔡}` (so `A ≥ 1`, `A ≤ 𝔡⁻²W^d`), `ℓ ≤ L`, `zdistInf ≤ L` (`st5_zdistInf_le`).

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `θ/θ₀ = g⁴/((1−s)²ℓ⁴)` (`θ = N^τ g⁴/((1−s)²R_a)` from `N^τ A^{-6/5}/R_a < c_n‖fluc‖`, `c_n = (1−s)²/(g⁴A^{6/5})`; `θ₀ = N^τℓ⁴/R_a`) | `1−s ≤ g²` ⇒ `g/√(1−s) ≥ 1` ⇒ `ℓ = min(g/√(1−s),L) ≤ g/√(1−s)` | `θ/θ₀ ≥ 1` (`STReg5I.2`) | equality iff `ℓ = g/√(1−s)`; szCL: `θ/θ₀ = 1` exactly (script A). The factor `(ℓ⁴/R_a)^{2p}` of `CltMom2.rhs` cancels exactly against `θ₀^{2p}`. |
| 2 | target 1, `DomHyp` at `Λ' = N^{τ}` (own `τ`) | event `{N^τ < A^{6/5}‖LKM‖(r^{d−2}+1)} ⊂ {N^{τ/2}ζ' < ‖LKM‖}`, `ζ' = Bctl^{1/5}STWB(r)e^{−(r/ℓ)^{1/2}}+W^{−Dw}`, iff `A^{6/5}(r^{d−2}+1)ζ' ≤ N^{τ/2}` | `meanFar_BctlSTWB`: `A^{6/5}Bctl^{1/5}STWB(r) ≤ c₀/(r+1)^{d−2}`, and `r^{d−2}+1 ≤ (r+1)^{d−2}` (`d−2 ≥ 1`; script B), so first part `≤ c₀` (ticket's `2c₀` is not needed); second part `A^{6/5}(L^{d−2}+1)W^{−Dw} ≤ 2𝔡^{−12/5}W^{6d/5+(d−2)/𝔠−Dw}` | `Dw₁ = D₀ := 6d/5+(d−2)/𝔠+1` leaves `2𝔡^{−12/5}W^{−1} → 0`; need `c₀+o(1) ≤ N^{τ/2}` (eventually, `N → ∞`). szCL: second part `4.3·10⁻⁴⁴`, `c₀ = 6.899`, holds `n ≥ 0` (script C). Hypotheses: `s ≤ t` gives `g²/L² ≤ 1−t ≤ 1−s` (regime for `meanFar_BctlSTWB` at `s`); `(1−s)/(1−s) = 1` kills `Cd`. |
| 3 | target 2, off-window exponential | `r > lw³ℓ ⇒ e^{−(r/ℓ)^{1/2}} ≤ e^{−lw^{3/2}} ≤ W^{−Dw}` iff `lw^{1/2} ≥ Dw` | `Dw² ≤ lw` (eventually, `W → ∞`) | with `Dw₂ = D + 3/𝔠 + 1` (`D = D₀ = 10.6` at the consumer): `Dw₂ = 29.6`, `Dw₂² = 876.2`, szCL needs `n ≥ 1241` (script C) |
| 4 | target 2, polynomial prefactor | `‖off‖ ≤ (1−s)²·L^{2d}·K_Θ·2K_Θ·(‖LKM‖+‖𝔼LKM‖)`, `K_Θ = c_Θ/g²` (**not a constant**: `meanFar_T1` gives `‖Θ_t(a,b)‖ ≤ c_Θ g⁻²/(r+1)^{d−2}`), but `(1−s)² ≤ g⁴` ⇒ `(1−s)²K_Θ² ≤ c_Θ²`, so `‖off‖ ≤ 2c_Θ²N²(2N^{τ'}(c₀+1)W^{−Dw}+(η_s⁻²+Σ‖𝒦‖)N^{−D₁''})`, `τ' = 1` | `≤ W^{−D}`: `Dw₂ ≥ D+3/𝔠+1` (from `N³ ≤ W^{3/𝔠}`), `D₁'' = D'+D+7`; probability of the good event `≥ 1−N^{−D'}` (one event for all `σ,b₁,b₂`, `hG` at `(Dw₂, τ', D')`) | `η_s⁻² ≤ L⁴/(g⁴κ'²) ≤ N^{10/3}/κ'²` (`1−s ≥ 1−t ≥ g²/L²`, `Im mE ≥ κ'`, `L⁴ ≤ N^{4/3}`, `g⁻⁴ ≤ N²`); `Σ‖𝒦‖ ≤ L^{2d}W^{−d}K₁ ≤ c_Θ N²` (`meanFar_n_K`, `K₁ = c_Θ g⁻²` at time `s`, `g²/L² ≤ 1−t ≤ 1−s`); leftover factors `W^{−1}`, `N^{−1}` |
| 5 | `C_BY`: `BY = A^{6/5}(η_s⁻²+Σ_β‖𝒦_β‖) ≤ N^{C_BY}` | `A^{6/5} ≤ 𝔡^{−12/5}N^{6/5}`; `η_s⁻²+Σ‖𝒦‖ ≤ N^{10/3}/κ'²+c_ΘN²` ⇒ `BY ≤ c N^{68/15}`; `w^{d−2}+1 ≤ 2lw^{3(d−2)}L^{d−2} ≤ N` eventually (`L^{d−2} ≤ N^{(d−2)/d}`) | `C_BY := 5` (`68/15 = 4.53`), `BY·(w^{d−2}+1) ≤ N^{6}` | `0.47` in `C_BY`; the `lw`, `c`, `κ'` factors go into `N^{ε}` (`meanFar_polylog`) |
| 6 | `p`, `D₁`, `D'` as functions of target 3's `(τ,D)` (ticket route `Λ' = N^{τ/2}`, `q₁ = N^{−D₁}`, `εf = W^{−D'}`) | `p = ⌈(D+2)/τ⌉ ≥ 1`; `D₁ = 2p(C_BY+2)+D+2 = 14p+D+2`; `D' = (6p+D+2)/𝔠` | (a) `Λ'`-term `≤ N^{−pτ}·P_p`, `P_p = 2^{2p}(2p)^{2p}(2·24)^p(C_dM)^{2p}lw^{24p} ≤ N` eventually; `pτ ≥ D+2` ⇒ `≤ N^{−D−1}`. (b) `q₁`-term `≤ P_pN^{12p+2−D₁}` `= P_pN^{−2p−D}` `≤ N^{−D−1}` (as `p ≥ 1`). (c) `W^{−D'}(ΣZ·R_a)^{2p}N^{−2pτ}`, `‖Z_β‖ ≤ g⁴·K_Θ·2K_Θ = 2c_Θ²` (constant), `ΣZ ≤ 2c_Θ²N²`, `R_a ≤ 2N`; `W^{−D'} ≤ N^{−𝔠D'}` ⇒ `≤ (4c_Θ²)^{2p}N^{6p−6p−D−2}` | each term `≤ N^{−D−1}`, so `3N^{−D−1} ≤ N^{−D}` for `N ≥ 3`; slack in (a): `N^{1}` (the polylog), in (b) at `p = 1`: `0`, in (c): `N^{−1}`. Alternative `Λ' = N^{τ/4}` improves (a) to `N^{−3pτ/2}` (T2169 row 16) and is allowed. |
| 7 | target 4: `p, D₁, D', Dw` are chosen for target 3 at `(τ/2, D+3)` | `p = ⌈2(D+5)/τ⌉`, `D₁ = 14p+D+5`, `D' = (6p+D+5)/𝔠` | before `∀ᶠ n` (quantifier order of `STCltIsoConcl`) | consumer `(τ,D) = (1/10,1)`: `p = 120`, `D₁ = 1686`, `D' = 4356` (`𝔠 = 1/6`), script C |
| 8 | target 4: `ζ ≥ W^{−D₀}`, `ζ = A^{−6/5}/R_a` | `A^{−6/5} ≥ 𝔡^{12/5}W^{−6d/5}`, `R_a ≤ L^{d−2}+1 ≤ 2W^{(d−2)/𝔠}` | `D₀ = 6d/5+(d−2)/𝔠+1`: at `d=3, 𝔠=1/6`: `D₀ = 10.6` | slack: `ζ ≥ (𝔡^{12/5}/2)·W^{−D₀+1} ≥ W^{−D₀}` eventually |
| 9 | target 4 splitting: `‖f‖ ≤ ‖𝔼f‖+‖c_n fluc‖+‖off‖` (`cltMom2_decomp`) | `‖𝔼f‖ ≤ N^{τ/2}ζ` (`meanFar_eventually`, every `σ,a`); `‖off‖ ≤ W^{−D₀} ≤ ζ`; `‖c_n fluc‖ ≤ N^{τ/2}ζ` | total `≤ 2N^{τ/2}ζ+ζ ≤ 3N^{τ/2}ζ ≤ N^τζ` iff `N^{τ/2} ≥ 3` | szCL `(τ=1/10)`: holds `n ≥ 0` (script C). Bad event `⊂ {∃σ a: W^{−D₀} < ‖off‖} ∪ ⋃_{σ,a}{N^{τ/2}ζ < ‖c_n fluc‖}` |
| 10 | union bound | `#((Fin 2→Bool)×(Fin 2→Zd d L)) = 4L^{2d} ≤ 4N²` | `P ≤ N^{−(D+1)} (target 2 at (D₀,D+1)) + 4N²·N^{−(D+3)} (target 3 at (τ/2,D+3)) = 5N^{−D−1} ≤ N^{−D}` | needs `N ≥ 5`; szCL `4L⁶ ≤ 4N²` slack `10^{43.4}` (n=0), `10^{104.8}` (n=34) |
| 11 | premises of `TailStmt` per `n`, derived eventually | `|E n| ≤ 2−κ < 2`; `κ' ≤ Im mE(E n)` (`mE_im`, as `MeanFar.lean:2046-2056`); `0 < g ≤ 𝔡⁻¹`, `A ≥ 1` (`WO`); `s<1`, `0≤t<1`; regime `(hreg n).1`; `40 ≤ lw`, `2d ≤ lw` (`lw ≥ 𝔠 log N → ∞`); `q₁ ≥ 0` | all from `Admissible`, `STReg5I`, hypotheses of the targets; none is a premise at `n` of the pins | szCL: `40 ≤ lw` from `n ≥ 34` (`lw(33) = 39.51 < 40`) |
| 12 | consumer limit (lesson 14), ticket route (`Λ'=N^{τ₃/2}`, `p=120`) at szCL, `(τ,D) = (1/10,1)`, target 3 at `(1/20,4)` | thresholds `n*` such that each of the three terms `≤ N^{−4}/3` | `M_w ∈ {1,10³,10⁶}` (`M = 4^d M_w`), `cs_3 = 24`, `C_3 = 317587968` (T2169 report), `K₀ = 1` | `n* = 7694 / 8130 / 8564` (`log₁₀N ≈ 7029 / 7423 / 7816`); alt `Λ'=N^{τ₃/4}`, `p = 68`: `7916 / 8366 / 8813`. Moderate (`N = 10^{7·10³}`), 8× the T2169 `p = 20` figure because target 4 calls target 3 at `(τ/2, D+3)`; not blocking: the targets are eventual statements, per-`n` premises hold from `n ≥ 34` |

Quantifier orders: `M` (from `cltMom2_tail_eventually`) after `(d, Λ=𝔡⁻¹, κ')`, before `sz, n`; `p, D` before `∀ᶠ n`; `a` after `∀ᶠ`. Hypotheses of target 2 are those of target 3 minus `STCltIsoConcl`; of target 1: `s ≤ t`, no energy hypothesis (none is used). Right sides: `STCltFarConcl` U-set and bound equal those of `STMeanFarConcl` (script D).

### (ii) One concrete nondegenerate instance (`szCL`: `d=3, L=2m⁵, W=2^m, m=n+24, g=1, s=0, t=1−L⁻², 𝔠=1/6, 𝔡=1/10, E_n=lemE z_n, σ=(+,−), a=(x_n,0)`)

Command A: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2182/inst.py`
```
n=34: L=1312713536 W=2^58 log10N=79.73 (N<=W^6: True) lw=40.2025 (40<=lw:True, 2d<=lw:True) ell_s=1.0 w=lw^3=64977.1 rho=lw^4=2.612e+06
   regime g^2/L^2 = 1/L^2 <= 1-t = 1/L^2 (equal); 1-s=1<=g^2=1 ; |E_n|<=1/2<2; Im mE>= 0.9682 (>=kappa'=1/20) ; log10 A=3 m log10 2=52.38 A>=1
   a=(x_n,0): |a1-a2|=m^5=656356768 <=L/2:True; R_a=656356769; c_n=A^(-6/5) (log10 -62.86); theta/theta0=1.0
   far radius (lw^4 ell)=2.612e+06 < |a1-a2|:True; index set: lw^5 ell_s=1.05e+08<=ell_t=L:True; |a1-a2|<= 1/2 lw^1.5 L+..:True
n=100: L=58632501248 W=2^124 log10N=144.29 (N<=W^6: True) lw=85.9503 (40<=lw:True, 2d<=lw:True) ell_s=1.0 w=lw^3=634952.8 rho=lw^4=5.457e+07
   regime g^2/L^2 = 1/L^2 <= 1-t = 1/L^2 (equal); 1-s=1<=g^2=1 ; |E_n|<=1/2<2; Im mE>= 0.9682 (>=kappa'=1/20) ; log10 A=3 m log10 2=111.98 A>=1
   a=(x_n,0): |a1-a2|=m^5=29316250624 <=L/2:True; R_a=29316250625; c_n=A^(-6/5) (log10 -134.38); theta/theta0=1.0
   far radius (lw^4 ell)=5.457e+07 < |a1-a2|:True; index set: lw^5 ell_s=4.691e+09<=ell_t=L:True; |a1-a2|<= 1/2 lw^1.5 L+..:True
== r^k+1<=(r+1)^k for k>=1,r>=0 (so 2c0 of ticket is c0 here): True
```
Reading: at `n ∈ {34,100}` every deterministic hypothesis of targets 1–4 holds at the same data: `Admissible(1/6,1/10)` (`W^6 ≥ N`, `g=1`), `s<t<1`, both halves of `STReg5I` (first with equality), `|E_n| ≤ 1/2 ≤ 2−κ` (`κ = 1/10`), `κ' = 1/20 ≤ 0.968 ≤ Im mE(E_n)`, `ℓ_s = 1` (`θ/θ₀ = 1`), `40 ≤ lw`, `2d ≤ lw`, `A = W³ ≥ 1`, index set `U n` nonempty at `a = (x_n,0)` (`lw⁵ℓ_s ≤ ℓ_t = L`; `|a₁−a₂| ≤ ½lw^{3/2}L`), far region nonempty (`|a₁−a₂| > lw⁴ℓ_s`), `σ₀ ≠ σ₁`. The nonlinear premises (`STGdecayW`, `STCltIsoConcl`, `STStep2Concl`) are other gates' pins and stay hypotheses of the examples; `STCltIsoConcl` is `inst_cltIso (stCltIso_holds 3) 1 one_pos`.

External hypotheses, concrete limit computation (lesson 14; row 12): command C: `python3 .../scratchpad/T2182/limit.py`
```
consumer (tau,D)=(1/10,1): target3 at (tau3,D3)=(1/20,4); c=1/6,d=3; D0=6d/5+(d-2)/c+1 = 10.6
ticket p=ceil((D3+2)/t3), Lambda'=N^(t3/2): p=120 Mw=1: n*=7694 log10N=7029 a=-28119 b=-9911450 c=-10169089 target=-28118 D1=1686 D'=4356
ticket p=ceil((D3+2)/t3), Lambda'=N^(t3/2): p=120 Mw=1000: n*=8130 log10N=7423 a=-29695 b=-10466435 c=-10744601 target=-29694 D1=1686 D'=4356
ticket p=ceil((D3+2)/t3), Lambda'=N^(t3/2): p=120 Mw=1e+06: n*=8564 log10N=7816 a=-31264 b=-11018844 c=-11317482 target=-31263 D1=1686 D'=4356
alt Lambda'=N^(t3/4), p=ceil((D3+1)/(1.5 t3)): p=68 Mw=1: n*=7916 log10N=7230 a=-28921 b=-5795609 c=-5966031 target=-28920 D1=958 D'=2484
alt Lambda'=N^(t3/4), p=ceil((D3+1)/(1.5 t3)): p=68 Mw=1000: n*=8366 log10N=7637 a=-30548 b=-6121260 c=-6304757 target=-30547 D1=958 D'=2484
alt Lambda'=N^(t3/4), p=ceil((D3+1)/(1.5 t3)): p=68 Mw=1e+06: n*=8813 log10N=8041 a=-32164 b=-6444723 c=-6641228 target=-32163 D1=958 D'=2484
target2: Dw_off=D2+3/c+1 with D2=D0=10.6: Dw_off=29.6, Dw^2=876.2<=log W needs n>=1241
log W>=40 from n>= 34
target1 at Lambda'=N^0.025: A^(6/5)(L+1)W^-D0 term=4.26e-44 ; c0=6.899; holds from n>=0
target1 at Lambda'=N^0.0125: A^(6/5)(L+1)W^-D0 term=4.82e-89 ; c0=6.899; holds from n>=22
n=0: N^(tau/2)>=3: True; zeta_min log10=-32.91 >= -D0 log10 W=-76.58: True; 4L^6<=4N^2 slack log10=43.35
n=34: N^(tau/2)>=3: True; zeta_min log10=-71.67 >= -D0 log10 W=-185.07: True; 4L^6<=4N^2 slack log10=104.76
```
(`a, b, c` = `log₁₀` of the Λ'-term, the `q₁`-term (`BY ≤ W^{18/5}(1.07+K₀L⁶W⁻³)`), and the isolated term of `rhs/θ₀^{2p}` against `log₁₀(N^{−4}/3)`; `b, c` have slack `>10⁶` in `log₁₀`, so a polynomial `K₀`, `c_Θ` is absorbed; the binding term is (a), `lw^{24p}` against `N^{pτ₃−D₃}`.)

Script D (the pin's U-set is that of `STMeanFarConcl`): `diff <(sed -n 386,391p RBM3D/Induction/Step5Pins.lean) <(sed -n 2089,2094p RBM3D/Evolution/MeanFar.lean)` printed no difference (exit 0).

### Verdict per target
- Target 1 `cltFar_dom`: PASS (rows 2, 5; hypotheses all hold at szCL).
- Target 2 `cltFar_off`: PASS (rows 3, 4; `Dw² ≤ lw` is an eventual condition).
- Target 3 `cltFar_fluc`: PASS (rows 1, 5, 6, 11, 12).
- Target 4 `stCltFar_holds`: PASS (rows 7–10; the same `𝔠_d` from `stCltIso_holds` feeds `H`).
Notes for stage 1b: (1) `K_Θ` is `c_Θ g⁻²`, not a constant (rows 4, 6); the products `(1−s)²K_Θ²` and `g⁴K_Θ²` are constants, which uses `1−s ≤ g²` (`STReg5I.2`). (2) `r^{d−2}+1 ≤ (r+1)^{d−2}` (row 2) makes the ticket's factor `2` unnecessary. (3) `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` are carried by the index set only (no row uses them).

## (b) Script output — Mon Oct  5 07:21:37 UTC 2026

Branch `t/T2182` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2182`), commit `5b9f637` on `a52eb85`; only `RBM3D/Evolution/CltFar.lean` (new) and `RBM3D/Test/Axioms.lean` (one line deleted) are changed. Scripts and outputs: scratchpad `T2182/`.
```
$ lake build RBM3D.Evolution.CltFar     # started Mon Oct  5 07:20:09 UTC 2026; exit code 0; build_module.out
ℹ [3819/3819] Built RBM3D.Evolution.CltFar (13s)
info: RBM3D/Evolution/CltFar.lean:1951:0: 'RBM.Gauss.Sizes.cltFar_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFar.lean:1952:0: 'RBM.Gauss.Sizes.cltFar_off' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFar.lean:1953:0: 'RBM.Gauss.Sizes.cltFar_fluc' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Evolution/CltFar.lean:1954:0: 'RBM.Gauss.Sizes.stCltFar_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3819 jobs).
$ grep -c error build_module.out; grep CltFar.lean build_module.out | grep -vc "depends on axioms"      # errors; other lines (warnings) on the module
0
0
$ grep -nE "sorry|admit|native_decide|^axiom|\baxiom\b" RBM3D/Evolution/CltFar.lean; echo "exit=$?"
exit=1
$ python3 count.py
1958 lines; public: ['CltFar.DomStmt', 'CltFar.OffStmt', 'CltFar.FlucStmt', 'cltFar_dom', 'cltFar_off', 'cltFar_fluc', 'stCltFar_holds']; private declarations: 70; examples: 5
```
Targets, extracted by script (`extract.py`: the three definitions to the first blank line, the theorem lines to `:= by`):
```
-- CltFar.lean:73
def CltFar.DomStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), sz.Admissible 𝔠 𝔡 →
    (∀ n, s n < 1) → (∀ n, s n ≤ t n) → STReg5I sz s t → STGdecayW sz E s t Cd →
    ∀ τ D₁ : ℝ, 0 < τ → 0 < D₁ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      CltMom2.DomHyp sz n (E n) (s n) σ (((sz.size n : ℕ) : ℝ) ^ τ) (((sz.size n : ℕ) : ℝ) ^ (-D₁))

-- CltFar.lean:81
def CltFar.OffStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ 𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), 0 < κ → sz.Admissible 𝔠 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STGdecayW sz E s t Cd →
    ∀ D D' : ℝ, 0 < D → 0 < D' → ∀ᶠ n in atTop,
      sz.seqP {ω | ∃ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
          ((sz.W n : ℕ) : ℝ) ^ (-D) < ‖CltMom2.off sz n (E n) (s n) (t n) σ a ω‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

-- CltFar.lean:92
def CltFar.FlucStmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (κ 𝔠 𝔡 Cd : ℝ) (E s t : ℕ → ℝ), 0 < κ → sz.Admissible 𝔠 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n < 1) → STReg5I sz s t →
    STGdecayW sz E s t Cd → STCltIsoConcl sz E s t →
    ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
      ∀ a : Fin 2 → Zd d (sz.L n),
        sz.seqP {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
              (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
            ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
              CltMom2.fluc sz n (E n) (s n) (t n) σ a ω‖} ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

-- CltFar.lean:586
theorem cltFar_dom (d : ℕ) : CltFar.DomStmt d := by
-- CltFar.lean:1167
theorem cltFar_off (d : ℕ) : CltFar.OffStmt d := by
-- CltFar.lean:1505
theorem cltFar_fluc (d : ℕ) : CltFar.FlucStmt d := by
-- CltFar.lean:1757
theorem stCltFar_holds (d : ℕ) : STCltFar d := by
```
Definitions against the check file (`docs/tickets/checks/T2182-check.lean`; namespace line, `open` lines and blank lines stripped):
```
$ diff pin.txt lean1.txt; echo "diff exit $?"       # pin.txt 30 lines (check file), lean1.txt 30 lines (CltFar.lean, section 1); run 07:21:55 UTC
diff exit 0
```
Compiled nonempty instances (`extract_inst.py`: statements; the applications follow), `d = 3`, data `szCL`, `Cd = 1`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `s ≡ 0`, `1 - t_n = L_n^{-2}`. The index set of `STCltFarConcl` is nonempty at every `n` (`example (n) := szCL_cltFar_index_nonempty n`). Open hypotheses: `STStep2Concl` (for `STGdecayW`, targets 1-3) and, for target 3, the nine stochastic premises of `inst_cltIso` (other gates' pins).
```
-- CltFar.lean:1890-1890 (statement; proof follows)
example : InstIng5Concl (fun sz E s t => STCltFarConcl sz E s t) szCL zCL sCL tCL 1 :=
-- CltFar.lean:1895
example (n : ℕ) := szCL_cltFar_index_nonempty n
-- CltFar.lean:1900-1906 (statement; proof follows)
example (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    ∀ᶠ n in atTop, CltMom2.DomHyp szCL n (STflowE zCL n) (sCL n) ![true, false]
        (((szCL.size n : ℕ) : ℝ) ^ (1 : ℝ)) (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) ∧
      szCL.seqP {ω | ((szCL.size n : ℕ) : ℝ) ^ (1 : ℝ) <
          ‖STcltB szCL n (STflowE zCL n) (sCL n) ![true, false] (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) ω‖ *
            (((zdistInf 3 (szCL.L n) ((![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 0 - (![0, 0] : Fin 2 → Zd 3 (szCL.L n)) 1) : ℕ) : ℝ) ^ (3 - 2) + 1)} ≤
        ENNReal.ofReal (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
-- CltFar.lean:1919-1922 (statement; proof follows)
example (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    ∀ᶠ n in atTop, szCL.seqP {ω | ∃ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (szCL.L n)),
        ((szCL.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) < ‖CltMom2.off szCL n (STflowE zCL n) (sCL n) (tCL n) σ a ω‖} ≤
      ENNReal.ofReal (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
-- CltFar.lean:1931-1941 (statement; proof follows)
example (hK : STKbound szCL (STflowE zCL)) (hKw : STKward szCL (STflowE zCL)) (ha : STLK szCL (STflowE zCL) sCL)
    (hD : STDecay szCL (STflowE zCL) sCL) (hDS : STDecayStrong szCL (STflowE zCL) sCL)
    (h1 : STStep1Loop szCL (STflowE zCL) sCL tCL) (h2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1)
    (h3 : STLmaxU szCL (STflowE zCL) sCL tCL) (h4 : STLKU szCL (STflowE zCL) sCL tCL) :
    ∀ᶠ n in atTop, szCL.seqP {ω | ((szCL.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
          (STAI szCL n ^ (-(6 / 5 : ℝ)) /
            (((zdistInf 3 (szCL.L n) ((![xCL n, 0] : Fin 2 → Zd 3 (szCL.L n)) 0 -
              (![xCL n, 0] : Fin 2 → Zd 3 (szCL.L n)) 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) <
        ‖(((1 - sCL n) ^ 2 / (szCL.lam n ^ 4 * (szCL.lam n ^ 2 * ((szCL.W n : ℕ) : ℝ) ^ 3) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.fluc szCL n (STflowE zCL n) (sCL n) (tCL n) ![true, false] ![xCL n, 0] ω‖} ≤
      ENNReal.ofReal (((szCL.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
-- applications (proof bodies, CltFar.lean:1907-1908, 1923-1925, 1944-1947):
  filter_upwards [cltFar_dom 3 le_rfl szCL (1 / 6) (1 / 10) 1 (STflowE zCL) sCL tCL szCL_admissible
    cltFar_sCL_lt (fun n => (szCL_hst n).le) szCL_reg5I h2.2.2 1 1 one_pos one_pos] with n hn
  cltFar_off 3 le_rfl szCL (1 / 10) (1 / 6) (1 / 10) 1 (STflowE zCL) sCL tCL (by norm_num) szCL_admissible
    (fun n => (cltFar_zCL_E n).trans (by norm_num)) (fun _ => le_rfl) szCL_hst cltFar_tCL_lt szCL_reg5I h2.2.2
    1 1 one_pos one_pos
  filter_upwards [cltFar_fluc 3 le_rfl szCL (1 / 10) (1 / 6) (1 / 10) 1 (STflowE zCL) sCL tCL (by norm_num)
    szCL_admissible (fun n => (cltFar_zCL_E n).trans (by norm_num)) (fun _ => le_rfl) szCL_hst cltFar_tCL_lt szCL_reg5I
    h2.2.2 hiso (1 / 10) 1 (by norm_num) one_pos] with n hn
  exact hn ![true, false] (by decide) ![xCL n, 0]
```
Name clash (main worktree, `RBM3D`, re-run on the final commit `Mon Oct  5 07:21:55 UTC 2026`, output identical to the earlier run) and ports:
```
$ grep -rn "cltFar_dom\|cltFar_off\|cltFar_fluc\|stCltFar_holds\|CltFar\.DomStmt\|CltFar\.OffStmt\|CltFar\.FlucStmt" RBM3D | grep -v Evolution/CltFar.lean
(no output)
$ grep -rn "cltFar_\|cltFarZ\|cltFarKp\|CltFarH5" RBM3D | grep -v Evolution/CltFar.lean | cut -c1-100     # only the merged Step5Inst name
RBM3D/Evolution/MeanFar.lean:2285:  Step5Inst.szCL_cltFar_index_nonempty n
RBM3D/Induction/Step5Pins.lean:625:(`szCL_cltFar_index_nonempty`) and the premises of `STCltIsoConcl
RBM3D/Induction/Step5Pins.lean:898:theorem szCL_cltFar_index_nonempty (n : ℕ) :
RBM3D/Induction/Step5Pins.lean:960:/-- `lem;CLT` at `(szCL, zCL, 0, 1 - L_n^{-2})` (case (i); index 
$ ls RBM3D/Evolution/CltFar.lean   (main worktree)   →   No such file or directory
$ git --no-optional-locks diff --stat a21a819 HEAD -- RBM3D/Evolution/MeanFar.lean     # source of the copies (RBM3D commit a21a819): unchanged
(no output)
```
No RBM1D/RBM2D file is read, copied or cited. The 12 copied private lemmas and the adapted blocks come from the merged RBM3D `Evolution/MeanFar.lean` (lines 845-1964); each source line is in the module docstring and in the docstring of the copy.
Registry (DECISIONS §16, §20): the line `RBM.Gauss.Sizes.STCltFar` of `owedProps` is deleted; the pre-check files are outside the worktree and never committed:
```
$ git diff main...t/T2182 -- RBM3D/Test/Axioms.lean | grep "^[-+]" | cut -c1-110
--- a/RBM3D/Test/Axioms.lean      +++ b/RBM3D/Test/Axioms.lean
-   `RBM.Gauss.Sizes.STCltFar, -- `lem;CLT`, far part (`3_5:2160-2250`); S5-01 (T2138, DECISIONS §40: owed)
$ lake build RBM3D.Test.Axioms; lake env lean precheck.lean   # precheck.lean = import RBM3D; import RBM3D.Evolution.CltFar; #assert_rbm_axioms (07:21:06 UTC)
exit code: 0   axiom audit: 5338 theorems, 1889 definitions, 0 axioms in `RBM`   premises found by scanning: 100 (borrowed 1, owed 78, structural 21)   lines mentioning CltFar: 0
$ lake env lean pre0.lean   # control: import RBM3D; #assert_rbm_axioms; run 06:58:03 UTC, before the root olean was rebuilt with the module
exit code: 1   error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:  [RBM.Gauss.Sizes.STCltFar]
$ lake build   # whole library with a temporary uncommitted `import RBM3D.Evolution.CltFar` after the last import of RBM3D.lean (07:20:39 UTC); RBM3D.lean restored afterwards
exit code: 0   RBM3D.lean:225:0: axiom audit: 5338 theorems, 1889 definitions, 0 axioms in `RBM`   Build completed successfully (3979 jobs).
registry: 2 borrowed + 112 owed + 56 structural; 70 registered premise(s) carry nothing yet
$ git status --short | wc -l; git diff --stat main...t/T2182
0
 RBM3D/Evolution/CltFar.lean | 1958 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    1 -
 2 files changed, 1958 insertions(+), 1 deletion(-)
```
The committed branch alone does not pass the whole-library `lake build` (no visible theorem proves `STCltFar` without the root import); the hub adds `import RBM3D.Evolution.CltFar` after the last `import` of `RBM3D.lean` (CLAUDE.md §3 (A) 4) before its full build.

Consumer limit check (CLAUDE.md §5 item 5, lesson 14) for the parameters actually in the file (`limit2.py`: every eventual condition of `CltFar.lean` along `szCL`; `stCltFar_holds` calls `cltFar_fluc` at `(τ/2, D+3) = (1/20, 4)` and `cltFar_off` at `(D₀, D+1)`, `D₀ = 10.6`; the pins' own thresholds (`STGdecayW`, `STCltIsoConcl`, `meanFar_eventually`) belong to their tickets):
```
$ python3 limit2.py
params: (tau,D)=(1/10,1); target 3 at (tau3,D3)=(0.05,4): p=120, m3=727, D1=2168; target 2 at (D0,D')=(10.6,2), Dw=29.6; cs=24, Cd=3.17588e+08, c0=6.899
M_w=1, C5=1: n*=8530, log10 N=7785; largest per-condition thresholds: T3: 4 Kp (ln N)^(24p) <= N^2: n>=8530; T2: Dw^2<=log W: n>=1241; T3: (4cT^2)^(2p)<=N: n>=462
M_w=1000, C5=10: n*=8963, log10 N=8176; largest per-condition thresholds: T3: 4 Kp (ln N)^(24p) <= N^2: n>=8963; T2: Dw^2<=log W: n>=1241; T3: (4cT^2)^(2p)<=N: n>=989
M_w=1e+06, C5=100: n*=9393, log10 N=8565; largest per-condition thresholds: T3: 4 Kp (ln N)^(24p) <= N^2: n>=9393; T3: (4cT^2)^(2p)<=N: n>=1517; T2: Dw^2<=log W: n>=1241
```
(`M = 4^d M_w` is the constant of `cltMom2_tail_eventually`, `c_Θ = C₅(1 + 2^{d-1})` with `C₅` of `prop5Decay_holds`; the thresholds are finite and of the size of the preflight's table (`n* = 7694 / 8130 / 8564` for its own, slightly different exponents).)

Narrative:
1. Target 1 (`cltFar_dom`): the event `{N^τ < |𝗕_β| R}` lies in the `≺` event of `STGdecayW` at `u = (s, σ, ![β₀, β₁])` at `(τ/2, D₁, D_w = 3/𝔠)`, because `A^{6/5} R ζ' ≤ c₀ + 2𝔡^{-4} ≤ N^{τ/2}` (`cltFar_dom_key`: copied `cltFar_BctlSTWB`, `R ≤ (r+1)^{d-2}`, `exp ≤ 1`; `cltFar_dom_tail`: `A ≤ 𝔡^{-2}N`, `R ≤ 2N`, `W^{-3/𝔠} ≤ N^{-3}`).
2. Target 2 (`cltFar_off`): one good event for all `(σ, a, b)` (`cltFar_good_event`: the union over `u = (s, σ, ![a,b])` is inside `STGdecayW`) at `D_w = D + 3/𝔠 + 1`. On it `‖off‖ ≤ (1-s)²(L^d)² K_Θ X (2K_Θ)` (`cltFar_off_sum_le`) with `K_Θ = c_Θ/g²`, `(1-s)²K_Θ² ≤ c_Θ²` (`1-s ≤ g²`), the off-window profile `ζ' ≤ (c₀+1) W^{-D_w}` (`cltFar_zeta_off`) and `‖𝔼𝓑‖ ≤ N ζ' + (η_s^{-2} + |𝒦|) N^{-D₁}` (`cltFar_B_bound`, adapted copy of `meanFar_B_bound`), `D₁ = D + 6/𝔠 + 2`; the numerics are `cltFar_off_numeric` (`N³ ≤ W^{3/𝔠}`, `N⁶ ≤ W^{6/𝔠}`, `W → ∞`, `D_w² ≤ log W`).
3. Target 3 (`cltFar_fluc`): `cltMom2_tail_eventually` at `Λ' = N^{τ/2}`, `q₁ = N^{-D₁}`, `εf = W^{-D'}`, `p = ⌈(D+2)/τ⌉`. The event is `{θ < ‖fluc‖}`, `θ = N^τ g⁴/((1-s)²R) ≥ θ₀ = N^τ ℓ_s⁴/R` (`cltFar_theta_ge`); the factor `(ℓ_s⁴/R)^{2p}` of `CltMom2.rhs` cancels exactly (`cltFar_div_step`); `cltFar_rhs_bound` bounds the three terms by `N^{-D}` using `BY (w^{d-2}+1) ≤ N⁹` (`cltFar_BYw_le`), `Σ|Z| ≤ 2c_Θ² N²`, `R ≤ 2N`.
4. Target 4 (`stCltFar_holds`): `stCltIso_holds` gives `𝔠_d = 1/100` and `STCltIsoConcl` (the same `𝔠_d` feeds `H`); the mean part is `meanFar_eventually` (not `stMeanFar`, so `st5_conStInd_mono` is not used); `W^{-D₀} ≤ ζ` (`cltFar_zeta_ge`); `cltMom2_decomp` splits `f` (`cltFar_far_le`); the bad set lies in `Eoff ∪ ⋃_{(σ,a)} Ef` over `{σ // σ₀ ≠ σ₁} × (Fin 2 → Z_L^d)` (`≤ 4N²` elements, `cltFar_union_bound`), total `≤ 5N^{-(D+1)} ≤ N^{-D}` (`cltFar_union_numeric`, `N ≥ 5`).
5. Against the ticket route: the factor 2 of `2c₀` is not needed (`R ≤ (r+1)^{d-2}`, as (a) row 2); `D₀, D_w, D₁, D'` are the explicit exponents of the module docstring; `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` are never used; no `(a′)` correction was needed.
6. Size: 1958 lines against the estimate 1450 (exponent bookkeeping of targets 2-3 and the cancellation lemmas).

## (c) Verified Mathlib names (`lake env lean names.lean`: exit 0, 0 errors; imports of `CltFar.lean`, `open MeasureTheory Filter`)
- Real: `rpow_def_of_pos, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_le_rpow_of_nonpos, rpow_le_one_of_one_le_of_nonpos, one_le_rpow, rpow_two, rpow_natCast, rpow_neg, rpow_neg_one, rpow_mul, rpow_add, rpow_one, rpow_nonneg, rpow_pos_of_pos, mul_rpow, log_le_log, log_rpow, log_nonneg, tendsto_log_atTop, exp_le_exp, exp_le_one_iff, norm_of_nonneg, sqrt_sq`; `Filter.Tendsto.const_mul_atTop`, `tendsto_rpow_atTop`, `Filter.tendsto_atTop_mono'`, `Filter.eventually_ge_atTop`.
- Finset, Fintype, measure: `Finset.sum_le_card_nsmul, card_filter_le, card_univ, sum_const, sum_nonneg`; `Fintype.card_prod, card_fun, card_subtype_le`; `MeasureTheory.measure_mono, measure_union_le, measure_iUnion_fintype_le`; `ENNReal.ofReal_add, ofReal_mul, ofReal_natCast, ofReal_le_ofReal`; `Nat.ceil_pos, Nat.le_ceil, Nat.cast_sub`.
- Order and algebra: `pow_add_pow_le, one_le_pow₀, pow_le_pow_left₀, pow_le_pow_right₀, inv_anti₀, inv_le_one_of_one_le₀, div_le_div_of_nonneg_left, div_le_div_of_nonneg_right, div_lt_iff₀', div_le_div_iff₀, div_le_one_of_le₀, div_le_iff₀, le_div_iff₀, mul_one_div_cancel, mul_inv_cancel₀, le_mul_of_one_le_left, mul_le_of_le_one_right`.
- Deprecated in this Mathlib (tool log), absent from the final file (`grep -c` gives 0): `push_neg` (use `push Not`), `Set.mem_setOf_eq` (use `Set.mem_ofPred_eq`). Names verified absent: none looked up.

## (d) Open issues and paper-delta candidates
- Registry and root import: see (b); the line `STCltFar` is deleted only together with the root import of the module (the hub's step).
- `STStep2Concl` and the nine stochastic premises of `inst_cltIso` stay hypotheses of the instances (other gates' pins); the instance of target 4 is the merged `inst_cltFar (stCltFar_holds 3)`.
- Paper-delta candidates (numbers assigned by the dispatcher):
  - `T2182a`: `(eq:ells_to_ellt)`, `(eq:ells_to_ellt2)` are not used by the far part: the estimates hold for every `σ₀ ≠ σ₁` (target 2: every `σ`) and every `a`; they only describe the index set of `STCltFarConcl` (cf. D369).
  - `T2182b`: `(eq:propcalB)` (`3_5:2155`) is the event `{N^τ ζ' < |𝓑|}` of `(Eq:Gdecay_w)` at `u = s` with the explicit scale `Λ' = N^τ` of the per-label tail `CltMom2.DomHyp` (`c₀ = (1+2^{d-1})^{6/5}(1+2^{d-1})`, `R ≤ (r+1)^{d-2}`), and its off-window half is `‖off‖ ≤ W^{-D}` for all `(σ, a)` at once, off one event of probability `≤ N^{-D'}` (`D_w = D + 3/𝔠 + 1`, `D_w² ≤ log W`).
  - `T2182c`: the moment order and exponents are explicit: `p = ⌈(D+2)/τ⌉`, `Λ' = N^{τ/2}`, `q₁ = N^{-D₁}`, `D₁ = 18p + ⌈D⌉ + 4`, `εf = W^{-D'}`, `D' = (6p + ⌈D⌉ + 3)/𝔠`; the paper's "any fixed `p`" (`3_5:2213`) and `≺` hide them.
  - `T2182d`: `‖Θ_t‖ ≤ c_Θ/g²` is not a constant (`(prop:ThfadC)`, `meanFar_T1`); the sums use `(1-s)² (c_Θ/g²)² ≤ c_Θ²` and `g⁴ (c_Θ/g²)² = c_Θ²`, i.e. `1-s ≤ g²` (`STReg5I.2`), which the paper's `≲` (`3_5:2204-2211`) hides.
  - `T2182e`: the `≺` over the index set is the explicit finite union over `{σ // σ₀ ≠ σ₁} × (Fin 2 → Z_L^d)` (`≤ 4N²` elements, exponents `D+1`, `D+3`), inside `P` (not `PrecPT`).
  - `T2182f` (DECISIONS §36): the statements are under `3 ≤ d` (the pins are `3 ≤ d → …`); `3 ≤ d` is used by `meanFar_BctlSTWB`, `prop5Decay_holds`, `cltMom2_tail_eventually`; the consumer `ST_step5_caseI_of_pins` (via `STIniTermI`) uses `STIngR5`, which has it.
