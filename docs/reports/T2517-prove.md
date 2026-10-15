Prover model: claude-sonnet-5-5
## (a) Math preflight — Thu Oct 15 08:50:11 UTC 2026
**Targets (mathematics; texts of `T2517-check.lean:108-205`, instance arguments added).** Data `(g,E,m)` real axis, `BAReal d L g κ E m` (`(gΨ-E-m)M=1`, `m=L^{-d}trM`, `κ≤Im m`; `M=M^{(B)}⊗1`; `Q=M^{(++)}`, `Q_ab=M_baM_ab`); path `gΨ_I+gueH_k` at `sz.withLam 0` (`SeqCoord=Σn,CoordF d (L n)(W n)`, `FineModel:155`; `withLam` changes only `lam`, `Sizes:182`); `z_u=E+(1-u)m`, `η_u=(1-u)Im m`, `Ŝ=t₁1+σJ` (`S^{(B)}(0)=1`, `EMn2BA:77`), `u=t₁+L^dσ`.
- T2: `∃K(κ)` (before `d,L,g,E,m`): `x=Q(t₁x+σΣx)+y`, `|y|≤B`, `u≤1` ⇒ `|x|≤KB`; gap `κ⁴/16≤|1-u r_a|`, `r_a=Σ_bQ_ab`. T4: pathwise `h1` (diagonal, `(Nη_u)^{-1}`) and `hoff` (below) ⇒ `∀ε ∀ᶠn ∀(k,a): |E g_a-m|≤N^ε(Nη_u)^{-2}`. T6: conditional drift of `loopL` at `ztOf m E`, `0<Im m`, `‖m‖≤1`, bound `16(ℓ+3)^4N^4(1+η^{-1})^{ℓ+4}Δ^{3/2}`. T7: one step of `e_k` (`eq729c` bound).
- Instance arguments (every `n`; no new mathematical hypothesis): `NeZero (sz.L n)` (from `sz.three_le_L n`) and `NeZero (sz.W n)` (from `sz.W_pos n`), global instances `neZeroL`, `neZeroW` (`Defs/Sizes.lean:152-153`), needed wherever a declaration is applied at `(sz.L n) (sz.W n)` (`Iblk`, `loopL`, `PsiI`, `BAMB`, `gueH`, ...); in T7 `n` is fixed and `Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ`. Whether instance synthesis succeeds with `(sz.withLam 0).L n` in types is for the probe (not compiled here).
### (i) Exponent table
| # | quantity | value / constraint | slack (numbers: `final.out` below) |
|---|---|---|---|
| 1 | `ε=κ²/4` (`BAoffDiag_scalar`, `Ward:202`) | needs `κ≤Im m`, `‖m‖≤1`, `0≤t≤1`: `ε≤|1-tm²|`, `1-|m|²≤(1-ε)|1-tm²|` | `min_u|1-um²|`=1.000 vs 0.0625 (κ=1/2); 0.786 vs 0.046 (E=1.8, κ=.43) |
| 2 | gap `κ⁴/16` (T2 gap) | `|1-ur_a|≥|1-um²|-(1-|m|²)≥εD≥ε²` since `r_a-m²=Σ_{b≠a}Q_ab`, `Σ_{b≠a}|Q_ab|=1-|m|²`, `u≤1` | 1.000 vs 3.9e-3 (x256); 0.787 vs 2.1e-3 |
| 3 | `K=16κ⁻⁴(1+16κ⁻⁴)` (T2) | `S=Σx`: `(1-ur)S=Σy` (row sums of `Q` const by `EKNonzero_Mss_shift`, col sum = row sum as `Q_ab=Q_ba`) ⇒ `|S|≤16κ⁻⁴L^dB`; `y'=y+σrS`, `|r|≤Σ|Q_ab|=1`, `σL^d≤u≤1` ⇒ `|y'|≤(1+16κ⁻⁴)B`; `baStab_of_real` at `t=t₁≤1` | κ=1/2: K=65,792; `K_emp`=1.50 (u=1 in grid); no `L`, `g` |
| 4 | `CM`, row `ℓ¹` of `M^{(B)}` (`baM_row_l1`) | `c₀⁻¹expC(d-2,c₀)`, `c₀=min(log(1+κ/(4dΛ)),κ/2)`; needs `0<g≤Λ`, `3≤L` | `d=3,κ=1/2,Λ=1/64`: c₀=.25, CM=6.29e6 vs true row `ℓ¹` 1.10 |
| 5 | bad event `D`, `c_bad` (T4) | `P(B)≤2N^{-D}`; `Σ_pqŜ_pq=L^du≤N`; `|g_q-m|≤2η⁻¹`, `|τ_ap|≤|t_ap|+|Q_ap|≤2η⁻¹` (`|t_ap|≤|M_ap|η⁻¹`, `|M_ap|≤1` Ward), `η⁻¹=NΛ_u`; bad part `≤2N^{1-D}·4N²Λ_u²=8N^{3-D}Λ_u²` | `D=5` (as band): 8N⁻²; `D≥3` closes, `c_bad=8` |
| 6 | `ρ=N^{ε/4}`, `X=N^{ε/2}`, threshold (T4) | `R=x-QŜx`: good event `|R_a|≤ρ²CM·uΛ_u²`; `|x|≤K(CM X+8)Λ_u²≤N^εΛ_u²` iff `X≥K(CM+8)` | `K(CM+8)`=4.14e11; ε=1: N≥1.7e23 (`sz0`, n≥8); ε=1/2: N≥2.9e46 (n≥169): a constant, eventual in n, not a witness |
| 7 | `R` at `(Nη)^{-2}`: input forms | `R_a=Σ_pqŜ_pqE[τ_ap(g_q-m)]`, `τ=t-Q`: with `h1`, `hoff` closes (row 6). With only `‖G-M‖_max≺(Nη)^{-1/2}` (`GUEPathBounds.localLaw`, `Grid:97`): `τ_ap≺|M_ap|(Nη)^{-1/2}`, `R≺CM(Nη)^{-3/2}`: loses `(Nη)^{1/2}` | no `hoff`-free route found |
| 8 | `hoff` consumer form | keep the check's text (`|t_aq-Q_aq|≺|M^{(B)}_{aq}|(Nη_u)^{-1}`, `U_n=Fin(K+1)×Zd×Zd`); identity `t_aq-Q_aq=M^{(B)}_{aq}twTr(q,a)`, `twTr(q,a)=W^{-d}Σ_i(G-M)_{(q,i),(a,i)}`, so `hoff` ⇐ `twTr≺(Nη_u)^{-1}` for all ordered pairs: grid twin of TL1 `BATwistAvgLaw` (`TwistPins:91`; chain identity `Step6BridgeBA_iii_ident`); diagonal pair = `h1`. Producer: C5 | identity err 5e-16 (`[B]`); limit (lesson 14): `g→0`: `M^{(B)}→mδ`, off-diagonal weights →0, diagonal = `h1` (`|t_aa-Q_aa|=|m||g_a-m|`); MC: `ρ_τ=ρ_g` (max of `twTr` over all pairs = diagonal max) |
| 9 | T6 constants | `16`, `(ℓ+3)^4`, `((WL)^d)^4`, `(1+η⁻¹)^{ℓ+4}`, `Δ^{3/2}` = `envConst` (`OneStep:78`); `E` enters the band proof only via `z'=-m` (`OneStep_Dsp`, `Drift:643`: `‖m‖≤1`) and `η>0`; `oneStepEnvelopeGUE` (`Drift:756`) already takes any Hermitian `M` (`gΨ_I+gueH_k`) | ℓ=1 at datum: 8.8e19 (hypotheses: Im m=.9676>0, ‖m‖=.99927≤1) |
| 10 | T7 constants | `16·5⁴=10⁴`, `N⁴(1+η⁻¹)^6`, `η_{u_{k+1}}≥η_{t0}=1/(NΛ)≥1/N` (`Λ≤1`, `Im m>0`); per step `12N⁵pΔ` ⇒ `12(t0-t1)N⁵p` over the grid | `Λ`=9.9e-7≤1; `ρΛ`=9.9e-6≤1; `NΔ`=.125≤1; `eq729c`=2.4e56 at K=2^22 (conclusion true, uninformative; `K≥N^{20+2c}` is C5's `gueGridK`) |
| 11 | census, price (script below) | split rule: central >1,950 ⇒ **a \| b** at `GUEOneLoop` \| `GUEEq729BA`; stop lines 1,400/file, 2,000 binding | total 2,002 (pure) / 2,445 (wide) / ticket 2,035, 2,015 without target 8: all >1,950; rows 1,044 / 958 (wide 1,199 / 1,246); wide upper ends 1,535, 1,595 exceed 1,400 |
| 12 | ticket inconsistency | Layout row b imports `BA/GUEKPrim` and lists target 8 (`baEq729_Kdisc`); Decision (1) removes target 8 and says C4 reads no C3 name | drop import and target 8: row b = targets 6, 7, 9; price −20 (row 11 uses it) |
### (ii) One concrete nondegenerate instance
`d=3`, `L_0=4` (64 blocks), `κ=1/2`, `Λ=1/64`, `g=1/64`, `E=0.5` (the shape of `hr0I`, `GreenStab:352`; the Lean flow datum itself is not numerically accessible), `sz0` of `Defs/Sizes.lean:257` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `N_0=2^21`), `t₁=1/4`, `t₀=1/2`, `K=2^22`, `k=0`, `I=⟨[+],[a]⟩`. External hypotheses `h1`, `hoff` (and `hX`, `hB`, `hg_i` of T7) are C5's pins; limit check: `N_n=2^21(n+1)^18≥n→∞` (`sz0_tendsto`), `Λ_u=(Nη)^{-1}→0`; `[C]` below measures the pathwise constants at fixed `u` near the GUE end (`η_u=.0081`, `Nη=4.1,13.9`): `ρ` ≈ 3.1 → 2.6. `[B]` checks the exact block identity `x_a=Σ_pqŜ_pqE[t_ap(g_q-m)]` by Monte Carlo (`z`-score 0.8; with `σ→1.5σ` `z`=11.7, so it discriminates).
Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2517 && python3 final.py` (numpy; `[A]` `inst.py`, `[B]` `ident2.py`, `[C]` `mc3.py`); output verbatim:
```
[A] d=3 L=4 g=0.015625 E=0.5: m=-0.2496+0.9676j |m|=0.999269 Im m=0.9676 kappa=0.5; BASelf res 3e-17; Ward |sum|M_ab|^2-1| 2e-15; Q=M^(++): diag=m^2 (2e-15), row sum r const (3e-15) =col sum (8e-16), sum_b|Q_ab|-1 (2e-15)
    GapBA: min_u,a|1-u r_a|=1.0000 >= kappa^4/16=3.91e-03 (True); min_u|1-u m^2|=1.0000 >= eps=kappa^2/4=0.0625 (True); StableBA: K_emp=1.500 at (t1,sigma L^d)=(0, 1) <= K=16k^-4(1+16k^-4)=6.579e+04 (True); 2000 random (t1,sigma,y): 0 violations; CM=c0^-1 expC(d-2,c0)=6.292e+06 (c0=0.2500) >= max_a sum_b|M_ab|=1.101
[A] d=3 L=4 g=0.015625 E=1.8: m=-0.8987+0.4369j |m|=0.999267 Im m=0.4369 kappa=0.43; BASelf res 1e-16; Ward |sum|M_ab|^2-1| 3e-15; Q=M^(++): diag=m^2 (3e-15), row sum r const (4e-15) =col sum (7e-16), sum_b|Q_ab|-1 (3e-15)
    GapBA: min_u,a|1-u r_a|=0.7872 >= kappa^4/16=2.14e-03 (True); min_u|1-u m^2|=0.7865 >= eps=kappa^2/4=0.0462 (True); StableBA: K_emp=2.129 at (t1,sigma L^d)=(0.1, 0.9) <= K=16k^-4(1+16k^-4)=2.195e+05 (True); 2000 random (t1,sigma,y): 0 violations; CM=c0^-1 expC(d-2,c0)=1.338e+07 (c0=0.2150) >= max_a sum_b|M_ab|=1.101
[B] d=1 L=3 W=2 N=6 g=0.4 E=0.8 t1=0.2 sigma L^d=0.5 u=0.7 Im m=0.7468 S=1000000: identity x_a=sum_pq S^_pq E[t_ap(g_q-m)]: max_a|x_a - rhs_a|=4.5e-04 (max z-score 0.80, se 4.6e-04); negative control (sigma->1.5 sigma): max|diff|=5.7e-03, z=11.7; twisted-trace identity t_aq-Q_aq=M^B_aq twTr(q,a) err 5e-16
[C] d=3 L=4 W=2 N=512 g=0.3 E=0.5 t1=0.3 sigma L^d=0.69 u=0.99: eta_u=0.0081 N*eta=4.1 Lu=(N eta)^-1=2.424e-01 Lu^2=5.88e-02 S=300
    pathwise constants over samples: rho_g=max|g_q-m|/Lu=3.06 (99%: 1.83); rho_tau=max|twTr|/Lu=3.06 (99%: 1.42) [|tau_ap|=|M_ap||twTr(p,a)| exactly]
    R_a=E sum S^_pq tau_ap (g_q-m): max_a|R_a|=4.27e-03 (MC se max 2.1e-03); |R|/Lu^2=0.073; good-event bound (t1+sigma L^d) rho_g rho_tau max_a sum_p|M_ap| Lu^2 = 2.45e+00 >= |R|: True; row l1 max=4.512
[C] d=3 L=4 W=3 N=1728 g=0.3 E=0.5 t1=0.3 sigma L^d=0.69 u=0.99: eta_u=0.0081 N*eta=13.9 Lu=(N eta)^-1=7.183e-02 Lu^2=5.16e-03 S=60
    pathwise constants over samples: rho_g=max|g_q-m|/Lu=2.61 (99%: 1.79); rho_tau=max|twTr|/Lu=2.61 (99%: 1.39) [|tau_ap|=|M_ap||twTr(p,a)| exactly]
    R_a=E sum S^_pq tau_ap (g_q-m): max_a|R_a|=9.47e-04 (MC se max 4.6e-04); |R|/Lu^2=0.184; good-event bound (t1+sigma L^d) rho_g rho_tau max_a sum_p|M_ap| Lu^2 = 1.58e-01 >= |R|: True; row l1 max=4.512
[T4] N_0=2097152=2^21; K_stab=65792; CM=6.2925e+06; c_bad=8 (D=5: 2N^-5 * L^d u * Env_tau Env_g, Env<=2/eta=2N*Lam -> 8N^-2 Lam^2); threshold N^(eps/2)>=K(CM+8)=4.140e+11
     eps=1.0: need N>=1.714e+23; sz0 (N_n=2^21 (n+1)^18, N_n>=n) first n=8
     eps=0.5: need N>=2.938e+46; sz0 (N_n=2^21 (n+1)^18, N_n>=n) first n=169
[T6] Im m=0.9676>0, |m|=0.999269<=1; grid time(k=1)=0.25000006<1; |I|=1: envelope 16(l+3)^4 N^4 (1+1/eta)^(l+4) D^(3/2) = 8.767e+19
[T7] eta_t0=0.4838; Lam=(N eta_t0)^-1=9.856e-07<=1; rho*Lam=9.86e-06<=1; N*Delta=0.125<=1; p=N^-5=2.5e-32>=0; eq729c=2.395e+56 (10000N^4(1+N)^6 D^1.5 term 2.395e+56); sz0 coupling window: g<=lam_0=1/64=0.015625
     sum over K steps needs K>=N^(20+2c): 1e4 N^10 K^-1/2 <= N^-c; at K=2^22 this fails (conclusion is a true bound, hypotheses hold); gueGridK=(N+1)^(32 n0+64)
```
Census (the ticket's `$HOME/scr_c4/census2.py` does not exist: `ls $HOME/scr_c4` → "No such file or directory"; `census2.py` = T2515's `census.py` with the ticket's wide tokens; T2515's regex has no `zt`, so Drift pure is 80 and row b pure uses the ticket's Drift 422; central = census − reuse + new + inst/hdr, `central.py`): `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2517 && python3 census2.py && python3 central.py`
```
OneLoop 1-1368: pure B/P/M 829/7/442 -> 906 | wide B/P/M 1015/7/256 -> 1091 | ticket 875 / 1031
Eq729A  1-1085: pure B/P/M 355/0/679 -> 416 | wide B/P/M 580/18/436 -> 652 | ticket 460 / 620
Drift   1-1359: pure B/P/M 0/0/1286 -> 80 | wide B/P/M 470/21/795 -> 560 | ticket 422 / 533
row a GUEOneLoop: central(pure)=1044 (1002-1336), central(wide)=1199 (1151-1535)
row b GUEEq729BA: central(pure)=958 (920-1226), central(wide)=1246 (1196-1595)
total central: pure 2002, wide 2445; ticket (with target 8, +20): 2035 / 2346; ticket minus target 8: 2015 / 2326; pre-signed split threshold 1950 -> split=True
```
### Verdicts
- T1 (`gueHBA`, Hermitian, `succ`, `ol_gueHBA_eq`): PASS (shift by `gΨ_I`; `gueH_succ` `Drift:925`). T2 (gap, `baOneLoop_stable`): PASS (rows 1-3; `K` independent of `L`, `g`; stop rule not triggered). T3/T4 (block identity, `gueGrid_expect_oneLoopBA`): PASS with `h1`, `hoff` as hypotheses (rows 5-8); `hoff` has a route to a C5 producer (`twTr`), so the D1 (i) stop rule does not fire; price risk is C5's.
- T5/T9 (instances): PASS (all deterministic hypotheses hold at the numbers above; `h1`, `hoff`, T7's pathwise hypotheses stay hypotheses). T6 (`condExp_loop_drift_gueBA`): PASS (row 9). T7 (`eq729_one_stepBA`): PASS (row 10). T8: removed by Decision (1) (row 12), not written.
- D1 (iii): free `(g,E,m)` with `BAReal`; substitution table of the ticket stands; `PathΩ (sz.withLam 0)=PathΩ sz` by `rfl` expected (definitional, see Targets), to be confirmed by the probe. Split: a | b stands (row 11).

## (a′) Preflight corrections — Thu Oct 15 09:14:09 UTC 2026
One citation in (a): `sz0` is given as "`Defs/Sizes.lean:257`"; it is `def sz0` at `:260` (`:257` is the `namespace` line):
```
$ grep -n "def sz0\|^namespace RBM.Gauss.SizesInst" RBM3D/Defs/Sizes.lean
257:namespace RBM.Gauss.SizesInst
260:def sz0 : Sizes 3 where
```
No verdict, number or instance of (a) changes.

## (a″) Probe compile — Thu Oct 15 09:14:09 UTC 2026 (`date -u`)
Role `prover-max` (`claude-sonnet-5-5`), probe step, D1 (i) only. Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2517`, branch `t/T2517`, base `242d669e`, one commit, new file `RBM3D/Probe/T2517Pins.lean` (never merged, no root import). Section (a) is not edited. `<scratch>` = scratchpad `T2517/w/` (not in the repository).
```
$ git show --stat --format="%h %s" HEAD
c305806d T2517 probe: D1 (i) text, pathwise step, instance (stage 1a; branch only, never merged)
 RBM3D/Probe/T2517Pins.lean | 142 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 142 insertions(+)
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2517 && lake env lean RBM3D/Probe/T2517Pins.lean     # 09:09:00 .. 09:09:05 UTC, on c305806d, `git status --short | wc -l` = 0
@gueHBA : {d : ℕ} →
  (sz : Sizes d) →
    (ℕ → ℝ) →
      (ℕ → ℝ) →
        (ℕ → ℝ) →
          (ℕ → ℕ) → (n : ℕ) → ℕ → PathΩ (sz.withLam 0) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
T2517_OneLoopBA : ℕ → Prop
@probe_R_good : ∀ {d L : ℕ} [inst : NeZero L] {t1 σ ρ Λ₁ Λ₂ : ℝ},
  0 ≤ t1 →
    0 ≤ σ →
      ∀ (w : Zd d L → ℝ) (τ γ : Zd d L → ℂ),
        (∀ (p : Zd d L), ‖τ p‖ ≤ ρ * w p * Λ₁) →
          (∀ (q : Zd d L), ‖γ q‖ ≤ ρ * Λ₂) →
            ‖∑ p, ∑ q, ↑((if p = q then t1 else 0) + σ) * (τ p * γ q)‖ ≤
              (ρ ^ 2 * (t1 + ↑L ^ d * σ) * ∑ p, w p) * (Λ₁ * Λ₂)
@probe_R_row7 : ∀ {d : ℕ},
  3 ≤ d →
    ∀ {L : ℕ} [inst : NeZero L],
      3 ≤ L →
        ∀ {κ Λ g E : ℝ} {m : ℂ},
          0 < κ →
            0 < Λ →
              0 < g ∧ g ≤ Λ →
                BAReal d L g κ E m →
                  ∀ {t1 σ ρ Λu : ℝ},
                    0 ≤ t1 →
                      0 ≤ σ →
                        ∀ (a : Zd d L) (τ γ : Zd d L → ℂ),
                          (∀ (p : Zd d L), ‖τ p‖ ≤ ρ * ‖BAMB d L g (↑E) m a p‖ * Λu) →
                            (∀ (q : Zd d L), ‖γ q‖ ≤ ρ * Λu) →
                              ‖∑ p, ∑ q, ↑((if p = q then t1 else 0) + σ) * (τ p * γ q)‖ ≤
                                ρ ^ 2 * (t1 + ↑L ^ d * σ) * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) *
                                  Λu ^ 2
probe_window : ∀ (n : ℕ),
  0 < BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n ∧ BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq n ≤ 1
'RBM.BA.T2517Probe.probe_R_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2517Probe.probe_R_row7' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2517Probe.probe_window' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0     # 38 output lines, none with "error" or "warning"
$ lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true -DrelaxedAutoImplicit=false RBM3D/Probe/T2517Pins.lean     # the lakefile leanOptions, 09:09:05 .. 09:09:11 UTC
EXIT=0     # output byte-identical to the run above (`cmp`)
$ python3 -I <scratch>/closure.py     # "against main": the probe's import closure vs the Lean files main has gained since the worktree base
base=242d669e main=dec8e150 | Lean files differing: RBM3D.lean RBM3D/BA/MAQDiff.lean | import closure of the probe: 209 modules | differing files in the closure: none
$ python3 -I <scratch>/textdiff.py     # check lines 129-154 (the commented target 4 text) against probe lines 49-71
check text: 1758 chars, 3 inline-body occurrences; probe text: 1599 chars
identical after substituting the inline body by `gueHBA ... ω`: True
$ lake env lean <scratch>/v0.lean     # check lines 14-26, 102, 104 (`namespace`, `open`), 124-154 verbatim; 09:09:11 .. 09:09:15 UTC
EXIT=1
<scratch>/v0.lean:30:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HAdd (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Matrix (Idx d ((sz.withLam 0).L n) ((sz.withLam 0).W n)) (Idx d ((sz.withLam 0).L n) ((sz.withLam 0).W n)) ℂ) ?m.91
<scratch>/v0.lean:37:20: error(lean.synthInstanceFailed): failed to synthesize instance of type class
<scratch>/v0.lean:44:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
$ lake env lean <scratch>/v8.lean     # check lines 156-205 (targets 6, 7) verbatim, header as v0 plus `noncomputable section`
EXIT=1     # 4 errors, each `synthInstanceFailed` `HAdd (Matrix (Idx d (sz.L n) (sz.W n)) ...) ...`; the check has 4 inline bodies there (165, 168, 171, 182)
$ lake env lean <scratch>/v7.lean     # v8 with the def of probe :37-39 added and the 4 inline bodies replaced by `gueHBA sz g t1 t0 K n k ω`
EXIT=0     # no output
$ grep -cE 'sorry|admit|native_decide|^axiom |^ *axiom ' RBM3D/Probe/T2517Pins.lean
0
$ grep -rnwE 'gueHBA|T2517_OneLoopBA|probe_R_good|probe_R_row7|probe_window' RBM3D RBM3D.lean --include='*.lean' | grep -vc '^RBM3D/Probe/T2517Pins.lean'     # this worktree; the main worktree: 0
0
$ python3 -I <scratch>/c1.py     # the ticket's C1 / UBA-C1 regex (+ `sz.lam`) and the X1-C4 def regex, comments dropped
C1/UBA-C1 hits: 0 | X1-C4 def hits: 0
$ grep -cE '^import RBM3D\.BA\.(MainInd|TwistPins|Step6)' RBM3D/Probe/T2517Pins.lean
0
```
Findings (probe line numbers are those of `RBM3D/Probe/T2517Pins.lean` at `c305806d`; numbers are script output above):
1. **Diagnosis; corrects the note at `T2517-check.lean:123` ("instance synthesis failed ... `NeZero (sz.L n)`").** The only errors of v0 and v8 are `HAdd` of `g • PsiI d (sz.L n) (sz.W n)` and `gueH (sz.withLam 0) ...`: `Matrix (Idx d (sz.L n) ...)` against `Matrix (Idx d ((sz.withLam 0).L n) ...)`; no `NeZero` error occurs in any run. Remedy: `gueHBA` (`:37-39`: `PsiI` read at `sz.withLam 0`, result type over `sz.L n`, `sz.W n`), `rfl`-equal to the check's inline reading (`:42-44`). With it the target 4 text compiles (`:49-71`) and so do the check's targets 6, 7 (v7). Proposed for the 1a-audit: targets 4, 6, 7 are stated through `gueHBA`, which is row a's target 1.
2. `PathΩ (sz.withLam 0) = PathΩ sz` is `rfl` (`:46`): the item (a) left to the probe.
3. **D1 (i) text** = `T2517_OneLoopBA` (`:49-71`): the check's text, `gueHBA` for the 3 inline bodies (script diff identical). `h1` is `:55-59`. **`hoff`, the consumer form for C5, is the second premise `:60-67`**: `t_{aq} = W^{-d} Σ_{x∈[a], y∈[q]} M_{xy} G_{yx}` (`Mres (gΨ_I) E m`, `Gres` at `gueHBA`, `z_u = ztOf m E u`) against `BAMss … true true a q`, with bound `‖BAMB … a q‖ (N η_u)^{-1}`, for `p : Fin (K n + 1) × Zd × Zd` (`ExpAvgGen_tM`, `ExpAvgGen_W1iii` have the same `t_{aq}`).
4. **Pathwise step of D1 (i).** `probe_R_good` (`:74`): `|τ_p| ≤ ρ w_p Λ₁`, `|γ_q| ≤ ρ Λ₂` give `‖Σ_{p,q} Ŝ_{pq} τ_p γ_q‖ ≤ ρ² (t₁ + L^d σ) (Σ_p w_p) Λ₁ Λ₂`, `Ŝ_{pq} = t₁ δ_{pq} + σ`. `probe_R_row7` (`:95`): `w_p = ‖M^{(B)}_{ap}‖`, `Λ₁ = Λ₂ = Λ_u`, `Σ_p w_p ≤ CM` by `baM_row_l1` (its premises `2 ≤ d`, `3 ≤ L`, `0 < Λ`, `0 < g ≤ Λ`, `0 < κ`, `BAReal` are the text's `3 ≤ d`, `0 < Λ`, `0 < κ`, `0 < g n ≤ Λ`, `BAReal` and the field `sz.three_le_L n`) give `ρ² u CM Λ_u²`, `u = t₁ + L^d σ`. So `h1` and `hoff` at one scale close `R` at `(N η_u)^{-2}`: the pathwise part of the D1 (i) stop rule does not fire. **Not compiled:** the identity `x = Q Ŝ x + R` (Stein, target 3), the bad event, the absorption into `N^ε`, and the producer of `h1`, `hoff` (C5; (a) row 8).
5. **Instance** (`:118-124`): `T2517_OneLoopBA 3`, as the hypothesis `hA` (the theorem is the 1b's), applied at `d = 3`, `sz0`, `κ = 1/2`, `Λ = 1`, `g n = BAflowLam0 sz0 zSeq n`, `E n = BAflowEs ..`, `m n = BAmF ..`, `t₁ = 1/4`, `t₀ = 1/2`, `K = 4`: `Tendsto size` by `sz0_tendsto`, `0 < g n ≤ 1` by `probe_window` (`:110`, every `n`), `BAReal` for every `n` by `BAflow_real` (`GreenSchur:59`), the time premises by `norm_num`; `t₁ < t₀ < 1`, `K = 4`, no empty index set; only `h1`, `hoff` remain premises (C5's pins). The ticket's target 5 cites `hr0I` (`GreenStab:352`), which is `n = 0` only: the family premise `∀ n, BAReal ...` needs `BAflow_real` at every `n`.
6. `open private ... from` (`:29-30`, used `:128-131`) resolves 5 band privates (`OneLoop_contraction`, `_stein`, `_selfcons`, `_stable`, `_expect_bound`) and 3 chain privates (`ExpAvgGen_stein_trace`, `_selfcons_fixed`, `_ward`); a name that does not exist is an error (scratch test, tool log). The public names of rows 1-7 are `#check`ed in `T2517-check.lean` Part 1 and not repeated; `baM_row_l1`, `BAflow_real`, `BAg0_le`, `BAt0_pos`, `mS_im_half` are exercised by the compiled lemmas and the instance.
7. Axioms of the three theorems: `propext`, `Classical.choice`, `Quot.sound` (output above). Registry: no line; `RBM3D.lean` untouched. Paper-delta candidates: none new.

## (b) Script output, stage 1b, row a — written Thu Oct 15 10:27:12 UTC 2026 (`date -u`; the times below are script output)
Role `prover-max` (`claude-sonnet-5-5`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2517`, branch `t/T2517`; scratch `<S>` = scratchpad `T2517/w1b/` (not in the repository). Row a only: new `RBM3D/BA/GUEOneLoop.lean` and one `RBM3D.lean` import line (`:651`); the probe `c305806d` stays on the branch. Sections (a), (a′), (a″) are not edited.
```
$ git log --format='%h %cd' (UTC) 4aaf3ef8..HEAD ; git show <h>:RBM3D/BA/GUEOneLoop.lean | wc -l
4aaf3ef8 09:22:38  merge main (13b68cea) into t/T2517                        (before the first Lean line)
db2015e4 09:33:36    85  §1 gueHBA, gueHBA_isHermitian, gueHBA_succ, ol_gueHBA_eq + root import   <- FIRST COMMIT (row b stacks here)
d7e792ca 09:36:20   229  §2 baOneLoop_gap, baOneLoop_stable
849617ef 09:42:36   602  §3 mixed-law Stein layer, GUEOneLoop_blockId
60492dac 09:48:52   834  §4 core GUEOneLoop_expect_core
49ca4aa1 10:02:40  1255  §5 one-grid-time bound, gueGrid_expect_oneLoopBA
2aa46e6e 10:13:47  1395  §5-§6 instances, block identity stated at g = 0 (C1)
6dcfe9c9 10:17:50  1395  docstring citations only
bd9781b1 10:26:23  1395  target 3 named GUEOneLoop_blockId (file-stem prefix, rule E)   <- last commit
census row a (1a-audit §5): pure 1,044 (1,002-1,336), wide 1,199 (1,151-1,535); stop line 1,400, binding 2,000 -> 1,395: not over either
```
**Name-level tables at the 1b start (0149 :98)**, run after the merge and before the first Lean line:
```
$ python3 -I <S>/nametab.py      34 ticket names (rows 1-7, 12, twin sources): expected file:line vs found -> 34 OK, 0 MOVED, 0 MISSING
 private (twin sources / open private): OneLoop_stable :857, OneLoop_contraction :484, OneLoop_selfcons :700, ExpAvgGen_stein_trace :348, ExpAvgGen_selfcons_fixed :470; all others public
 row 1 BAMss_ss_diag Prop5Short:110, BAMss_row_offdiag_sum :121, BAoffDiag_of_real Ward:289 (and BAoffDiag_scalar :202), EKNonzero_Mss_shift EKNonzero:110
 row 2 baStab_of_real GreenStab:46, BAStab GreenCore:1268 | row 3 EMn2BA_SB_zero EMn2BA:77, ouP_ba_eq_band UNPins:467, Pgue Grid:61 | row 7 baM_row_l1 GreenStab:116
 row 5 BAMB MFixedPoint:190, Mres GLoopFlow:81, BAMB_diag_eq Ward:89, BAMB_symm :83, BAMB_row_sq_real :125 | row 6 ztOf_im GLoopFlow:64, etaOf :58, BAReal MFixedPoint:432, BAm_norm_le_one Ward:136
 row 12 gueH_succ Drift:925, gueH_isHermitian Grid:164, PsiI_isHermitian BlockAnderson:65 | ol_gueH_eq OneLoop:125, ExpAvgGen_tM :72, ExpAvgGen_W1iii :81
$ closure.py: planned 5 imports 209 modules; final 6 imports (+ Universality/GUEPhase/Drift, owner of gueH_succ) 213 (214 with the module itself); V hits [] in both; importers: RBM3D.lean:651 only
$ grep -rnw (8 new public names, GUEOneLoopInst) RBM3D RBM3D.lean, minus the file and the probe: 0 hits each ; private helpers not starting GUEOneLoop_/GUEOneLoopInst_: none
```
**Build, axioms.**
```
$ lake build RBM3D.BA.GUEOneLoop 2>&1 | tail -2      (10:26:42 UTC, on bd9781b1)
info: RBM3D/Chain/CltGen.lean:266:0: 'RBM.BA.bandFM_STExpInv' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3933 jobs).
$ lake build  (full library with #assert_rbm_axioms; 10:24:39 .. 10:26:07 UTC on the content of bd9781b1: `Built RBM3D.BA.GUEOneLoop (13s)`, no warning line from the file; same result on 6dcfe9c9, 10:16:18 .. 10:17:43, and on 2aa46e6e, 10:11:55 .. 10:13:33)
Build completed successfully (4424 jobs).   EXIT=0
$ lake env lean <S>/ax_all.lean      (#print axioms of the 8 new public declarations; every line identical)
'RBM.BA.gueHBA' | gueHBA_isHermitian | gueHBA_succ | ol_gueHBA_eq | baOneLoop_gap | baOneLoop_stable | GUEOneLoop_blockId | gueGrid_expect_oneLoopBA : [propext, Classical.choice, Quot.sound]
$ git show bd9781b1:RBM3D/BA/GUEOneLoop.lean | grep -cE 'sorry|admit|native_decide|^ *axiom '  ->  0
```
**Target statements, extracted by script** (`python3 -I <S>/stmts.py`, file at `bd9781b1`, whitespace collapsed):
```
theorem baOneLoop_gap : ∀ κ : ℝ, 0 < κ → ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a : Zd d L, κ ^ 4 / 16 ≤ ‖1 - (u : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b‖
theorem baOneLoop_stable : ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧ ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BAReal d L g κ E m → ∀ t1 σ : ℝ, 0 ≤ t1 → 0 ≤ σ → t1 + (L : ℝ) ^ d * σ ≤ 1 → ∀ (x y : Zd d L → ℂ) (B : ℝ), (∀ a, ‖y a‖ ≤ B) → (∀ a, x a = ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * ((t1 : ℂ) * x b + (σ : ℂ) * ∑ c, x c) + y a) → ∀ a, ‖x a‖ ≤ K * B
theorem gueGrid_expect_oneLoopBA (d : ℕ) : 3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ → ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ), Tendsto (fun n => sz.size n) atTop atTop → (∀ n, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) → (∀ n, K n ≠ 0) → StochDomAt (Pgue (sz.withLam 0)) sz.size (fun n (p : Fin (K n + 1) × Zd d (sz.L n)) ω => ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n p.1 ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ - m n‖) (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹) → StochDomAt (Pgue (sz.withLam 0)) sz.size (fun n (p : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω => ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2, Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y * Gres (gueHBA sz g t1 t0 K n p.1 ω) (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) true y x - BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖) (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹) → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (K n + 1) × Zd d (sz.L n), ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n p.1 ω)) (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ 2
def gueHBA {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := ((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n) + gueH (sz.withLam 0) t1 t0 K n k ω
theorem gueHBA_isHermitian {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) : (gueHBA sz g t1 t0 K n k ω).IsHermitian
theorem gueHBA_succ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) : gueHBA sz g t1 t0 K n (k + 1) ω = gueHBA sz g t1 t0 K n k ω + show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from (Real.sqrt (gridStep t1 t0 K n / (((sz.withLam 0).size n : ℕ) : ℝ)) : ℂ) • Sizes.seqXmat (sz.withLam 0) n (ω (k + 1))
theorem ol_gueHBA_eq {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) : gueHBA sz g t1 t0 K n k ω = ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from Xmat d ((sz.withLam 0).L n) ((sz.withLam 0).W n) (Sizes.slice (sz.withLam 0) n (olComb (sz.withLam 0) (Real.sqrt (t1 n)) (Real.sqrt (gridStep t1 t0 K n / (((sz.withLam 0).size n : ℕ) : ℝ))) k ω))
theorem GUEOneLoop_blockId (hL : 3 ≤ L) {t1 c0 σ u : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (hu : t1 + (L : ℝ) ^ d * σ = u) (v : CoordF d L W → ℝ≥0) (hv : ∀ c : CoordF d L W, (v c : ℝ) = t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2)) {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0) (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1) (hm : ∀ a : Zd d L, Matrix.trace (Mb * Eblk d L W a) = m) (a : Zd d L) : (∫ ω : Ω d L W, Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W a) ∂(GaussianProduct.law v)) - m = ∑ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * ∫ ω : Ω d L W, (((W : ℂ) ^ d) * Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W a * Mb * Eblk d L W p)) * (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W q) - m) ∂(GaussianProduct.law v)
```
**Statement diff against the 1a-audit texts** (3):
```
$ python3 -I <S>/diffall.py      (signed.lean sha256 48cb8c998f82415b = the 1a-audit's)
baOneLoop_gap              vs T2517_GapBA     :  199 vs  199 chars, identical=True
baOneLoop_stable           vs T2517_StableBA  :  333 vs  333 chars, identical=True
gueGrid_expect_oneLoopBA   vs T2517_OneLoopBA : 1561 vs 1561 chars, identical=True
gueHBA def vs probe c305806d:37-39: identical=True
$ lake env lean <S>/chk3full.lean   (signed defs + `example : T2517_GapBA := baOneLoop_gap`, `example : T2517_StableBA := baOneLoop_stable`, `example : ∀ d, T2517_OneLoopBA d := gueGrid_expect_oneLoopBA`) -> exit 0, no output
```
**Compiled nonempty instances** (`namespace GUEOneLoopInst`, `GUEOneLoop.lean:1283-1391`; `d = 3`, `sz0`, the flow datum of `sz0`):
```
:1298,1302,1305 gueHBA_isHermitian (n=0,k=4), gueHBA_succ, ol_gueHBA_eq (every n, k, sample point) at g = BAflowLam0 sz0 zSeq, t1 = 1/4, t0 = 1/2, K = 4
:1309 baOneLoop_gap at κ = 1/2, GreenStabInst.hr0I (n = 0), u = 1/2, a = 0
:1343 baOneLoop_stable: ∃ K > 0 and the nonzero x = vI (δ_0), y := x - Σ Q(t1 x + σ Σ x), B = Σ‖y‖, t1 = 1/4, σ = 1/(4 L^3) (t1 + L^3 σ = 1/2): hypotheses hold, conclusion ‖x a‖ ≤ K B
:1363 GUEOneLoop_blockId at hr0I, t1 = 1/4, σ = 1/(4 L^3), c0 = σ/W^3, u = 1/2, v_c = t1 gvar_c + c0 w_c, z = z_{1/2}, a = 0 (hM, hm from GUEOneLoop_Mdata)
:1385 example := gueGrid_expect_oneLoopBA 3 le_rfl sz0 (1 / 2) 1 (by norm_num) one_pos (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 4) (fun _ => 1 / 2)
        (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (fun _ => 4) (tendsto_natCast_atTop_iff.mp sz0_tendsto) GUEOneLoopInst_window
        (fun n => BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
```
Open arrows of the last example: `h1`, `hoff` (the two `StochDomAt` premises, C5's pins). Discharged: `3 ≤ d`, `κ = 1/2 > 0`, `Λ = 1 > 0`, `Tendsto size` (`sz0_tendsto`, `N_0 = 2^21`), `0 < g n ≤ 1` and `BAReal` at `κ = 1/2` for every `n` (audit observation 3: `hr0I` is `n = 0` only), `0 ≤ t1 ≤ t0 < 1`, `K n ≠ 0`; no empty index set, no collapsed window. Limit check for `h1`, `hoff`: (a)(ii) `[C]` (`ρ_τ = ρ_g`) and the identity `t_aq - Q_aq = M^B_aq twTr(q,a)` at `5e-16` (`[B]`).
**Greps and diff** (`python3 -I <S>/c1.py` on the 8 public statements, comments dropped; `git diff --stat main...t/T2517`):
```
C1 / UBA-C1 regex hits in public statements: []  | gueH/Pgue/PathΩ/filt arguments: ['(sz.withLam']  | X1-C4 (def|abbrev|structure) hits: 0  | ^import RBM3D.BA.(MainInd|TwistPins|Step6): 0
 RBM3D.lean | 1 +   RBM3D/BA/GUEOneLoop.lean | 1395 +++   RBM3D/Probe/T2517Pins.lean | 142 +  -> 3 files changed, 1538 insertions(+)   (main head 99aa2fe8, merge-base 13b68cea)
```
**Ports and twins.** Nothing is copied from `../RBM1D` or `../RBM2D` (no RBM1D/RBM2D diff-stat). Twins of merged RBM3D files (last commit touching the three sources: `089052ca`), source line -> here: `ExpAvgGen_stein_coord :237` -> `GUEOneLoop_stein_coord :256`; `ExpAvgGen_stein_int :303` -> `_stein_int :300`; `ExpAvgGen_contract :275` -> `_contract :377`; `ExpAvgGen_stein_trace :348` -> `_stein_trace :425`; `ExpAvgGen_sid1 :415`, `_selfcons_fixed :470` -> `GUEOneLoop_blockId :471`; `OneLoop_stable :857` -> `baOneLoop_stable :146`; `OneLoop_expect_core :953` -> `GUEOneLoop_expect_core :664`; `OneLoop_expect_bound :1125` -> `GUEOneLoop_expect_bound :898`; `gueGrid_expect_oneLoop :1308` -> `gueGrid_expect_oneLoopBA :1196`; `ol_gueH_eq :125` -> `ol_gueHBA_eq :85`; `gueH_succ Drift:925` -> `gueHBA_succ :72`. Re-checked against the paper TeX `6_Step6_two_loop.tex:12-21`: `lem:improve_exp_aver` is stated for the matrix `M` of the setting, `max_a |𝔼 tr((G_u - M) E_a)| ≺ (W^{-d} B_{u,0})²`, proof "the same as [YY_25, Lemma 5.15]"; here `M = M^{(B)} ⊗ 1` (not `m 1`) and the grid bound is `N^ε (N η_u)⁻²`.
**Coverage as used** (ticket rows; script counts of non-comment uses in the file): 1 `BAMss_ss_diag` 2×, `BAMss_row_offdiag_sum` 2×, `BAoffDiag_scalar` 1× (`BAoffDiag_of_real` 0×), `EKNonzero_Mss_shift` 1×; 2 `baStab_of_real` 1× (`BAStab` 0×); 3 `EMn2BA_SB_zero` 1×, `Pgue` 11×, `ouP_ba_eq_band` 0×; 4 twins (`OneLoop_contraction`, `ExpAvgGen_stein_trace` 0× by name), `OneLoop_sum_gue_block` 2×, `sum_coordinateBlock_trace_pair` 1×, `GaussianProduct.stein` 1×; 5 `BAMB` 22×, `Mres` 9×, `BAMB_diag_eq` 1×, `BAMB_row_sq_real` 1×, `BAMres_fine_apply` 1×, `ExpAvgGen_resolvent_id` 2×; 6 `ztOf_im` 2×, `etaOf` 11×, `BAReal` 5×, `BAm_norm_le_one` 3×; 7 `baM_row_l1` 2×; 8, 9 the premises `h1`, `hoff` of the target 4 text; 10, 11, 13, 14, 15 not read by row a; 12 `gueH_succ` 1×, `gueH_isHermitian` 1×, `PsiI_isHermitian` 3×.
**Registry and scan.** No registry line (`h1`, `hoff` are inline premises; no `Prop` or structure added); `RBM3D/Test/Axioms.lean` is not in the diff; the full build ran `#assert_rbm_axioms`. `git diff --name-only main...t/T2517` lists only the three files above.
**Narrative.**
1. D1 (i) closes as signed: `x = Q Ŝ x + R`, `R_a = Σ_{p,q} Ŝ_{pq} 𝔼[(t_ap - Q_ap)(g_q - m)]`; good event `ρ² u C_M Λ_u²` by `GUEOneLoop_R_good` and `baM_row_l1` (`C_M = c₀⁻¹ S_{c₀}`, `c₀ = BAct_rate d Λ κ`); no premise beyond the signed `h1`, `hoff`.
2. The bad event is taken at `D = 7` (the band has `D = 5`): `δ = 2N^{-7}`, envelopes `E_Φ = 2 L^d η⁻¹`, `E_τ = 2 L^d κ⁻¹ η⁻¹` (`‖M‖ ≤ κ⁻¹` from `norm_Gsig_le_inv_eta`, `‖Q_ap‖ ≤ 1` by Ward), `δ L^d u E_τ E_Φ ≤ 8 κ⁻¹ Λ_u²`; `h1`, `hoff` are used at `D = 7`, `τ = ε/4`.
3. Final constant `K_st (ρ² C_M + 8 κ⁻¹)`, `K_st = 16 κ⁻⁴ (1 + 16 κ⁻⁴)` from `baOneLoop_stable`; absorbed by `N^{ε/2} ≥ K_st (C_M + 8 κ⁻¹) + 1` eventually (`C_M`, `K_st`, `κ⁻¹` do not depend on `n`).
4. `GUEOneLoop_blockId` is stated at `g = 0` (`SB d L 0`, `gvarF d L W 0`: C1); the private Stein layer (`GUEOneLoop_stein_coord/_int/_contract/_stein_trace`) is the law `GaussianProduct.law v`, `v_c = t₁ gvar_c + c₀ w_c`, with `H₀ ≠ 0` and general `P`, `Q`; `_contract` and `_stein_trace` keep a general `g`. D1 (ii) is row b's. D1 (iii) is used as signed: free `(g, E, m)` under `BAReal`, `PsiI` read at `sz.withLam 0` inside `gueHBA`.
5. Row b reads from the first commit `db2015e4`: `gueHBA`, `gueHBA_isHermitian`, `gueHBA_succ` (the `gueH_succ` form at `sz.withLam 0`, second summand under `show Matrix (Idx d (sz.L n) _) … from`), `ol_gueHBA_eq`. `GUEOneLoop_Mdata`, `GUEOneLoop_H0_herm` are private (row b would need `open private`).
## (c) Verified Mathlib names (module by `env.getModuleIdxFor?`, script `<S>/mnames.lean`; each resolves)
`Finset.sum_mul_sum` ← `Mathlib.Algebra.BigOperators.Ring.Finset`; `Finset.single_le_sum` ← `Mathlib.Algebra.Order.BigOperators.Group.Finset`; `Finset.sum_ite_eq` ← `…Group.Finset.Piecewise`; `Finset.add_sum_erase` ← `…Group.Finset.Basic`
`MeasureTheory.integral_map`, `integral_finsetSum`, `norm_integral_le_integral_norm`, `integral_mono` ← `Mathlib.MeasureTheory.Integral.Bochner.Basic`; `integral_indicator_const` ← `…Bochner.Set`; `Integrable.of_bound` ← `…Integral.IntegrableOn`
`MeasureTheory.measure_toMeasurable` ← `…Measure.MeasureSpaceDef`; `measure_union_le` ← `…OuterMeasure.Basic`; `ENNReal.toReal_le_of_le_ofReal`, `ENNReal.ofReal_add` ← `Mathlib.Basic.ENNReal.Real`; `Real.coe_toNNReal` ← `Mathlib.Basic.NNReal.Defs`
`tendsto_rpow_atTop` ← `…SpecialFunctions.Pow.Asymptotics`; `tendsto_natCast_atTop_iff` ← `Mathlib.Order.Filter.AtTopBot.Archimedean`; `Real.rpow_neg/_natCast/_mul/_add` ← `…Pow.Real`; `Real.sq_sqrt` ← `…Real.Sqrt`
`le_inv_comm₀`, `inv_anti₀`, `one_le_inv₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀` ← `Mathlib.Algebra.Order.GroupWithZero.Basic`; `Complex.abs_im_le_norm`, `Complex.norm_real` ← `Mathlib.Analysis.Complex.Norm`; `continuous_finsetSum` ← `Mathlib.Topology.Algebra.Monoid`
Deprecated in this Mathlib (flagged by `Linter.isDeprecated`; not used): `continuous_finset_sum`, `if_pos`, `if_neg`, `if_true` (replaced by `continuous_finsetSum`, `↓reduceIte`, `eq_true`/`eq_false`). No name was invented.
## (d) Open issues and paper-delta candidates
- `T2517a` (BA Lemma 5.15 at the GUE-phase grid): paper `6:12-21` proves `lem:improve_exp_aver` by "the same as [YY_25, Lemma 5.15]"; here the stability is of `1 - M^{(+,+)} Ŝ`, `Ŝ = t₁ 1 + σ J`, `K = 16 κ⁻⁴ (1 + 16 κ⁻⁴)` (zero mode `κ⁴/16 ≤ |1 - u r_a|`, then `baStab_of_real`), uniform in `L`, `g`; the bound is the grid form `N^ε (N η_u)⁻²`, not `(W^{-d} B_{u,0})²`.
- `T2517b` (input `hoff`, absent at the band): `|t_aq - M^{(++)}_aq| ≺ |M^{(B)}_aq| (N η_u)⁻¹`, `t_aq = W^{-d} Σ_{x∈[a], y∈[q]} M_xy G_yx`, for all ordered pairs; producer C5 (grid twin of TL1 `BATwistAvgLaw`; chain identity `t_aq - Q_aq = M^B_aq twTr(q,a)`); the band has `M = m 1` and needs only `h1`.
- Observations: (1) the ticket's row a import list lacks `Universality/GUEPhase/Drift` (owner of `gueH_succ`, needed by `gueHBA_succ`); added, V hits none. (2) `T2517_OneLoopBA` strengthens the band `hlam` (`∀ᶠ n`, `sz.lam`) to `∀ n, 0 < g n ∧ g n ≤ Λ` on the free family (audit observation 4); not a paper difference. (3) Coverage row 1 cites `BAoffDiag_of_real`; the scalar `BAoffDiag_scalar` (`Ward:202`) is read instead (same `ε = κ²/4`).
- Risk (C5): `h1`, `hoff` have no producer yet (Decision (2)); every other premise of the target 4 text is discharged at the instance.
