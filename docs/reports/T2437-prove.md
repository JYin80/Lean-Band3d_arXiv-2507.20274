Prover model: claude-sonnet-5-5
## Result (stage 1b, `prover-max`) — Mon Oct 12 04:18:04 UTC 2026
Branch `t/T2437` at `1869c73` (5 commits ahead of `main`); `RBM3D.lean` is untouched (the hub adds `import RBM3D.BA.TwistGridRem`, `import RBM3D.BA.TwistGridRem2` after the last import line at merge; the full `lake build` with them is in (b)). Section (a) is unchanged; no (a′): no value of its table (i) needed a correction (of row 8 only the bound `‖E_a‖, ‖P_{c₁c₂}‖ ≤ 1` is used).
- **1a (i), as proved.** `C₀ = 11`, `CK = 6` (any `CK ≥ 6`); `Z₁ = 10⁴ N⁴ (1+q)⁶ ≤ c₁ N^{10}`, `c₁ = 10⁴ (1+2/κ)⁶`, `q = η_{u_{j+1}}⁻¹ ≤ (2/κ) N`; `Z₂ = (1−u_{j+1})⁻³ ≤ 8 N³`; `N ≥ c₁ + 8` eventually in `n`; no `3 ≤ d`.
- **1a (ii), route table (band ↦ twisted twin).** `OneStep` §1 generic word jets `w0/w1/w2` with their norm, Lipschitz and derivative lemmas: *kept* (`open private`, not copied); `L̃` is the word `[(σ₁,E_a),(σ₂,P)]` over the letters `Eblk a`, `P_{c₁c₂}` (norms `≤ 1`), not a direct `C³` Taylor. `OneStep` §2-§3 (loop jets, norms), §5 Stein, §6 space step, §7 time step and assembly: *copied with generic letters* at `z_v = ztOf m_F E v`, `∂_v z_v = −m_F` (`TwistGridRem.lean` §1-§5); §4 counts, `OneStep_closure`, `OneStep_taylor2`: *kept*. `LoopStep` `condExp_loop_step`: *copied* for `L̃ − K̃` at `H_k = g₀Ψ + pathH` (`TwistGridRem2_condExp_step`; `LoopStep_condExp_freezeC` and the Hermitian-part trick *kept*); `condExp_loop_drift` ↦ `TwistGridRem2_step_le`. `K̃`: the exact identity `Θ_{u+Δ} − Θ_u − ΔΘ_uQΘ_u = Δ²Θ_{u+Δ}QΘ_uQΘ_u` (`TwistGridRem_twK_taylor`); drift `= twGenM − ∂_uK̃` by `BATwistHier_holds`. `DifREP1` `difRep_rem_arith`: *copied* with `Z₁, Z₂` of this ticket (`TwistGridRem2_rem_arith`). `GridEnvelopeN`, `difRep_flow_bounds`, `stKbound_of_flow`, `difRep_stepErr_le`: *dropped* (no `𝒦`-tree error, no `Ũ`-mismatch).
- **Line counts** (stop line 2,000 per file; the ticket predicted ≈ 2,070–2,900 in all): `RBM3D/BA/TwistGridRem.lean` 1078, `RBM3D/BA/TwistGridRem2.lean` 494.
- **Verdict.** Target 1 `baTwistGridRem_holds` (`TwistGridRem2.lean:394`) and target 2 (instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `s ≡ 1/2`, `t ≡ 2/3`, `K_n = ⌈N_n^{CK}⌉ + 1`, then `baTwistGridAssemble_holds 3` with `BATwistGridTail 3`, `BATwistGridWTail 3` as hypotheses) are built, committed on `t/T2437`, with the standard three axioms; target 3 (registry): none. No hypothesis added, nothing weakened, no pinned signature changed, no external input.
## (a) Math preflight — Mon Oct 12 03:23:22 UTC 2026

Target 1: `baTwistGridRem_holds d : ∃ C₀ ≥ 0, BATwistGridRem d C₀`; clause (i) is merged (`baTwistGrid_decomp_ae`, `TwistGrid2.lean:182`); clause (ii) is `‖twRem_k‖ ≤ N^{C₀}√Δ`, all `k ≤ K`, eventually in `n`.
Math used: `r_j = E[A_{j+1}|F_j] − A_j − Δ·Drift_j = [E L̃_{u_{j+1}}(H_j+√ΔX) − L̃_{u_j}(H_j) − Δ·twGenM] − [K̃_{u_{j+1}} − K̃_{u_j} − Δ∂_uK̃]` (`Drift = twGenM − ∂_uK̃` by `BATwistHier_holds`, `TwistGrid.lean:855`, which needs `BAReal`, `0 < g₀`, `0 ≤ u < 1`), so `‖r_j‖ ≤ Z₁Δ^{3/2} + Z₂Δ²`, summed over `j < k ≤ K`.
Notation: `N = sz.size n = (W_n L_n)^d`, `η_v = (1−v) Im m_F`, `z_v = E + (1−v) m_F` (`∂_v z_v = −m_F`), `q = η_t⁻¹`.

### (i) Exponent table
| # | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `3 ≤ d` | not needed: every `d` | used inputs: `BAflow_real` (GreenSchur:59), `BAflow_lam0_window` (:72), `EMn2BA_T0_lt_one/_one_sub_T0/_mF_data` (EMn2BA:106/111/125), `EKPins_norm_Q_le/_Theta_le` (EKPins:151/161), `BATheta_hasDerivAt` (KBase:341), `BAm_norm_le_one` (Ward:136), `oneStepEnvelope` (OneStep:2205, `∀ d L W`); `grep "3 ≤ d"` over EMn2BA, EKPins, KBase, GreenSchur, Ward, TwistGrid, TwistGrid2, TwistPins, Step2BA, FlowPins, OneStep, Markov, LoopStep, Walk hits only pins not used (EKPins:98-262, EMn2BA:452, TwistPins:123-218) and comments (Ward:16, :302). The band's `3 ≤ d` enters only through `stKbound_of_flow` (DifREP1 header): not used, `K̃ = twK` is explicit | none |
| 2 | step law, base matrix | step `PF d L W 0` (`Pp = pathP (sz.withLam 0)`); `H_j = g₀Ψ + pathH` Hermitian | Step2BA:68-72; `PsiI_isHermitian` (BlockAnderson:65); `pathH_isHermitian` (Walk:98); `twGenM` uses `gvarF … 0` (TwistGrid:118) | exact |
| 3 | `N` | `N_n → ∞` | `BAFlow.1 = Admissible`, third conjunct `SizeTendsto` (Sizes.lean:177); every threshold below is `N ≥ N₀` | `N₀ = c₁ + 8` (rows 10, 12) |
| 4 | times | `0 ≤ s ≤ u_j < u_{j+1} ≤ t ≤ T0 < 1`, `KΔ = t−s ≤ 1` | `EMn2BA_T0_lt_one` (:106); `1 − T0 ≥ Im z/2` (EMn2BA:111); `BAdom`: `N^{−1+ε} ≤ Im z ≤ 1` (MFixedPoint:435); hence `(1−t)⁻¹ ≤ 2N^{1−ε} ≤ 2N` | instance `1−T0 = 0.3056`, `1−t = 1/3` |
| 5 | `m_F` | `‖m_F‖ ≤ 1`, `κ ≤ Im m_F ≤ 1` | `EMn2BA_mF_data` (:125; uses `BAm_norm_le_one`); spectral direction `D_σ = PropSpin m_F σ · 1`, `‖D_σ‖ = ‖m_F‖ ≤ 1` (`b = 1`) | instance `‖m_F‖ = 1.000000` |
| 6 | `η⁻¹` on `[0,t]` | `η_v⁻¹ ≤ (2/κ) N^{1−ε} ≤ (2/κ) N` | `η_v ≥ κ(1−T0) ≥ κ N^{−1+ε}/2` (private `TwistKer2_eta_inv_le`, TwistKer2:708: copy). Sharper: `η_{T0} = √T0·Im z`, so `η⁻¹ ≤ √((κ+1)/κ) N^{1−ε}` (T2428-prove.md:20) | instance `η_t⁻¹ = 3.0000`, `η_{T0}⁻¹ = 3.2727` (`η_{T0} = √T0 Im z` printed below) |
| 7 | `g₀_n` | `0 < g₀_n` eventually | `BAflow_lam0_window` (GreenSchur:72); needed only by `BATwistHier_holds`; clause (ii) is already `∀ᶠ n` | `g₀ = 2.0e-4` at `n = 1` |
| 8 | letters, dimension | `‖E_a‖ = ‖P_{c₁c₂}‖ = W^{−d} ≤ 1`; trace over `N` vertices | `L̃ = Tr(R_{σ₁} E_a R_{σ₂} P_{c₁c₂})`, `R_σ = G(σ)`, `‖R_σ‖ ≤ K := η⁻¹` (Hermitian `H`) | consts.py: both norms `0.25 = W^{−d}` |
| 9 | jets of `L̃`, 2 resolvents | `‖w₁‖ ≤ 2K³b`, `‖w₂‖ ≤ 6K⁴b²`, `b = 1` (`r₁ = −RDR`, `r₂ = 2RDRDR`; terms `2+2+2 = 6`) | band's `OneStep_norm_w1_le/_w2_le` (OneStep:919, :936) at list length `k = 2` | exact |
| 10 | `Z₁` (envelope (a)) | `Z₁ = 16·5⁴·N⁴(1+q)⁶ = 10⁴N⁴(1+q)⁶ ≤ c₁N^{10}`, `c₁ = 10⁴(1+2/κ)⁶` (`1.5625e8` at `κ = 1/2`) | space step `(32/3)·24·N⁴q⁵τ³` (Stein; uses only `∫‖X‖ ≤ 4N²`, OneStep:1643) + time step `6Nq⁴(½+4N²)τ³`, both `≤ 16(k+3)⁴N⁴(1+q)^{k+4}τ³` at `k = 2`, `τ = √Δ` (`OneStep_closure`, :2139); uses only `Δ ≥ 0`, `u+Δ < 1` | closure ratio LHS/RHS `≤ 0.00157` (consts.py); `1+(2/κ)N ≤ (1+2/κ)N` |
| 11 | `Z₂` (`K̃` Taylor (c)) | `Z₂ = (1−t)⁻³ ≤ 8N³` | exact resolvent identity `Θ_{u+Δ} − Θ_u − ΔΘ_uMΘ_u = Δ²Θ_{u+Δ}MΘ_uMΘ_u` (`M = M^{(σ₁σ₂)}`); `K̃ = W^{−d}Σ_{a'}Θ(a,a')M(σ₁)_{c₂a'}M(σ₂)_{a'c₁}`, `|M(σ)_{xy}| ≤ 1` (`TwistKer2_M_le_one`, TwistKer2:1275), `‖M^{(σσ')}‖_∞ ≤ 1`, `‖Θ_v‖_∞ ≤ (1−v)⁻¹` (EKPins:151/161); `∂_uK̃` from `BATheta_hasDerivAt`; remainder `≤ Δ²(1−u−Δ)⁻¹(1−u)⁻² ≤ Δ²(1−t)⁻³`, no second derivative. Not the band's `N^{15}` (DifREP1:1062-1080); below T2428 row 7's hand count `N⁵` (`8N³ ≤ N⁵` for `N ≥ 3`) | toy.py (c): max ratio `0.1979 ≤ 1` |
| 12 | `C₀` | **`11`** (∃, before `sz, z`) | need `Z₁ + Z₂√Δ ≤ N^{C₀}`: with row 13, `c₁N^{10} + 8 ≤ (c₁+8)N^{10} ≤ N^{11}` iff `N ≥ c₁+8`. `C₀ = 10` fails because `c₁ > 1` (keeping `N^{1−ε}` instead of `N` would need `N^{6ε} ≥ c₁`: `ε`-dependent, not pursued) | `N/(c₁+8)`: `n=0`: 0.0134 (fails), `n=1`: 3518 |
| 13 | `CK` | **`6`** (any `CK ≥ 6` is admissible; the band's `36 = 8m+20` also works: a larger `CK` only strengthens `N^{CK} ≤ K`) | `K ≥ N^{CK}` gives `Δ = (t−s)/K ≤ N^{−CK}`, `√Δ ≤ N^{−CK/2}`; need `Z₂√Δ ≤ 8N^{3−CK/2} ≤ 8` | tight at `CK = 6` |
| 14 | sum | `‖twRem_k‖ ≤ k(Z₁Δ^{3/2}+Z₂Δ²) ≤ KΔ(Z₁√Δ+Z₂Δ) ≤ √Δ(Z₁+Z₂√Δ)` | `k ≤ K`, `KΔ = t−s ≤ 1`; copy of `difRep_rem_arith` (DifREP1:1089) with `Z₁, Z₂` of rows 10-11; no `ΔH ≤ 1` hypothesis | `≤ N^{11}√Δ` |

Route facts. `L̃` enters the generic word jets with `P_{c₁c₂}` as a second letter (letters `E_a`, `P`; hypothesis `‖Ei‖ ≤ 1`, row 8), specialised to the fixed word `[(σ₁,E_a),(σ₂,P)]`. A direct `C³` Taylor in `M` is not used: it needs `E‖X‖³`, and the merged moment lemma is the first absolute moment only (OneStep:1643). `TwistGrid_second` (TwistGrid:467) and `TwistGrid_deriv_spec` (:544) are private: copy. The band's `GridEnvelopeN` (K-tree error, `N^{15}`) and `difRep_flow_bounds` (`STFlow`) are not used.

### (ii) One concrete nondegenerate instance
`d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))⁵`, `lam_n = (2(n+1))⁻⁶`, Sizes.lean:260-266), `κ = 1/2, ε = 1/10, 𝔠 = 1/6, 𝔡 = 1/10` (`flow_sz0`, FlowPins:1214), `z = zSeq`, `s ≡ 1/2 < t ≡ 2/3 ≤ T0` (`t0_sz0`, FlowPins:1227), `K_n = ⌈N^6⌉+1`, `C₀ = 11`, `CK = 6`; first admissible `n = 1` (`N = 5.5e11 ≥ c₁+8`). `m_S = L⁻³Σ_k (gλ_k − 6i/5)⁻¹` over the spectrum of the adjacency of `Z_L³` (`PsiB`, `mS`, `zS = w − mS`, MFixedPoint:849-868), `T0 = Im m/(Im m+Im z)` (`BAt0`, :279), `m_F = m_S/√T0`. Budgets of the proof (`η⁻¹ ≤ (2/κ)N`, `(1−t)⁻¹ ≤ 2N`) are used for `Z₁, Z₂`, not the true `η⁻¹ = 3`.
```
$ S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2437; python3 $S/inst.py | head -13
c1 = 16*5^4*(1+2/kappa)^6 = 156250000.0  threshold N0 = c1+8 = 156250008.0
n=0 eta_T0=(1-T0)Im mF=0.306105 vs sqrt(T0)Im zS=0.306105; sqrt((kappa+1)/kappa)N^(1-eps)=8.473e+05; g0=sqrt(T0)lam=1.301e-02
n=0 L=4 W=32 N=2.0972e+06 g=1.562e-02 Im mS=0.832488 Im zS=0.367512 T0=0.693740 |mF|=0.999493 Im mF=0.999493 eta_t=0.333164 1/eta_t=3.0015 hyps_ok=True
     N>=N0: False; Z1=1.5625e8*N^10 ratio Z1/(c1 N^10)=0.2621; Z2/N^3=8.0; log10 K=37.93; D=1.959e-39
     sum_j bound = 1.1233e+70 * sqrt(D)  vs N^11 = 3.4509e+69: ok=False; slack N^11/(sum/sqrtD)=3.0720e-01
n=1 eta_T0=(1-T0)Im mF=0.305556 vs sqrt(T0)Im zS=0.305556; sqrt((kappa+1)/kappa)N^(1-eps)=6.378e+10; g0=sqrt(T0)lam=2.035e-04
n=1 L=8 W=1024 N=5.4976e+11 g=2.441e-04 Im mS=0.833333 Im zS=0.366667 T0=0.694444 |mF|=1.000000 Im mF=1.000000 eta_t=0.333333 1/eta_t=3.0000 hyps_ok=True
     N>=N0: True; Z1=1.5625e8*N^10 ratio Z1/(c1 N^10)=0.2621; Z2/N^3=8.0; log10 K=70.44; D=6.037e-72
     sum_j bound = 1.7215e+124 * sqrt(D)  vs N^11 = 1.3863e+129: ok=True; slack N^11/(sum/sqrtD)=8.0531e+04
n=2 eta_T0=(1-T0)Im mF=0.305556 vs sqrt(T0)Im zS=0.305556; sqrt((kappa+1)/kappa)N^(1-eps)=4.544e+13; g0=sqrt(T0)lam=1.786e-05
n=2 L=12 W=7776 N=8.1248e+14 g=2.143e-05 Im mS=0.833333 Im zS=0.366667 T0=0.694444 |mF|=1.000000 Im mF=1.000000 eta_t=0.333333 1/eta_t=3.0000 hyps_ok=True
     N>=N0: True; Z1=1.5625e8*N^10 ratio Z1/(c1 N^10)=0.2621; Z2/N^3=8.0; log10 K=89.46; D=5.794e-91
     sum_j bound = 8.5572e+155 * sqrt(D)  vs N^11 = 1.0184e+164: ok=True; slack N^11/(sum/sqrtD)=1.1902e+08
$ python3 $S/consts.py
dim = 12 ||E_a|| = 0.25 ||P_{c1c2}|| = 0.25 (W^-d = 0.25 )
k=2: max LHS/RHS = 0.0015721435546875 ; 16(k+3)^4 = 10000
k(k+1) = 6 = 2 (r2 E R P) + 2 (r1 E r1 P) + 2 (R E r2 P)
$ python3 $S/toy.py   (c): d=1 toy, 5 blocks, W^d=4, unimodular phases, row sums of |M^(σσ')| = 1; (a): 3 vertices, w=1, exact Gauss-Hermite E f(M+√ΔX,u+Δ)
(c) max rem/bound over 2x2 charges x 3 (u,D) x 3 (a,c1,c2): 0.1979 (<=1; Theta_{u+D}-Theta_u-D Th Q Th = D^2 Th_{u+D} Q Th_u Q Th_u exact)
(a) D=0.1: |E f - f - D gen| = 4.656e-03; /D^1.5 = 1.472e-01; /D^2 = 4.656e-01; envelope Z1*D^1.5 with Z1=16*5^4*n^4(1+1/eta)^6 = 1.378e+07
(a) D=0.05: |E f - f - D gen| = 1.125e-03; /D^1.5 = 1.007e-01; /D^2 = 4.501e-01; envelope Z1*D^1.5 with Z1=16*5^4*n^4(1+1/eta)^6 = 4.872e+06
(a) D=0.025: |E f - f - D gen| = 2.760e-04; /D^1.5 = 6.982e-02; /D^2 = 4.416e-01; envelope Z1*D^1.5 with Z1=16*5^4*n^4(1+1/eta)^6 = 1.722e+06
(a) D=0.0125: |E f - f - D gen| = 6.818e-05; /D^1.5 = 4.879e-02; /D^2 = 4.364e-01; envelope Z1*D^1.5 with Z1=16*5^4*n^4(1+1/eta)^6 = 6.090e+05
```
Reading: for `n ≥ 1` every hypothesis of target 1 holds with a nonempty window (`s = 1/2 < t = 2/3 < T0 = 0.6944`, `Im m_F = 1 ≥ κ`, `hyps_ok = True`: `κ ≤ Im m`, `N^{−1+ε} ≤ Im z ≤ 1`, `T0 ≥ t`, `‖m_F‖ ≤ 1`, `0 < lam ≤ 10`, `g₀` printed), `K_n ≠ 0`, `N^{CK} ≤ K_n`; the summed budget is `≤ N^{11}√Δ` with slack `8.1e4` (`n=1`), `1.2e8` (`n=2`). It fails at `n = 0` (`N = 2.1e6 < c₁+8`), which the `∀ᶠ n` of clause (ii) allows. No external hypothesis occurs in target 1 (every input of rows 1-11 is merged and proved). `BATwistGridTail 3`, `BATwistGridWTail 3` of target 2's example are T2438/T2439's pins and enter only as hypotheses of `baTwistGridAssemble_holds`. The (a) toy shows `|E f − f − Δ·gen f| ≈ 0.44Δ²`, inside the envelope `Z₁Δ^{3/2}`.

### Verdicts
- Target 1 `baTwistGridRem_holds`: PASS (`C₀ = 11`, `CK = 6`, `Z₁ = 10⁴N⁴(1+q)⁶ ≤ c₁N^{10}`, `Z₂ = (1−t)⁻³ ≤ 8N³`, no `3 ≤ d`).
- Target 2 (instance `baTwistGridRem_holds 3` at `sz0`, `zSeq`, `flow_sz0`, then `baTwistGridAssemble_holds 3` with `BATwistGridTail 3`, `BATwistGridWTail 3` as hypotheses): PASS (`n_* = 1` for target 1).
- Target 3 (registry: none): nothing to check.
- Not given (outside the stage-1a format, which excludes size estimates): the per-file line prediction and the kept/copied/dropped route table.

## (b) Script output (stage 1b; scripts in scratchpad `T2437/`, not in the repository)
```
$ date -u; git log -1 --format="%h %s"; git status --short | wc -l; git log --oneline main..t/T2437 | wc -l
Mon Oct 12 04:15:43 UTC 2026
1869c73 T2437: TwistGridRem: drop two redundant open-private names
       0
       5
$ lake build RBM3D.BA.TwistGridRem RBM3D.BA.TwistGridRem2 > build.log; grep -E "error:|Build completed" build.log; grep -c "^warning: RBM3D/BA/TwistGridRem" build.log
Build completed successfully (4015 jobs).
0
$ grep -E "axiom audit|Build completed|^exit" fullbuild2.log   (full `lake build`, two import lines after `import RBM3D.Graph.BASymm2`, reverted)
info: RBM3D.lean:485:0: axiom audit: 12439 theorems, 3865 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4253 jobs).
exit: 0
$ wc -l RBM3D/BA/TwistGridRem.lean RBM3D/BA/TwistGridRem2.lean; grep -c "sorry\|admit\|native_decide\|^axiom" (both)
    1078 RBM3D/BA/TwistGridRem.lean
     494 RBM3D/BA/TwistGridRem2.lean
    1572 total
RBM3D/BA/TwistGridRem.lean:0
RBM3D/BA/TwistGridRem2.lean:0
$ lake env lean ax.lean | sed "s/.* depends on axioms: //" | sort | uniq -c   (27 public theorems, names in ax.lean)
  27 [propext, Classical.choice, Quot.sound]
'RBM.BA.baTwistGridRem_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistGridRem_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistGridRem_step' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2437-check.lean > /dev/null; echo exit $?
exit 0
$ git diff --stat main...t/T2437
 RBM3D/BA/TwistGridRem.lean  | 1078 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistGridRem2.lean |  494 ++++++++++++++++++++
 2 files changed, 1572 insertions(+)
$ grep -rnE "(^|[^A-Za-z0-9_])TwistGridRem2?_|baTwistGridRem_holds" RBM3D RBM3D.lean | grep -v "^RBM3D/BA/TwistGridRem" | wc -l
       0
$ git log --all --oneline -- "RBM3D/BA/TwistGridRem*" | wc -l   (all on t/T2437)
       5
$ open private names per source module (python over the two files)
{'RBM3D.BA.TwistGrid': 5, 'RBM3D.BA.TwistPins': 1, 'RBM3D.Path.OneStep': 32, 'RBM3D.Path.LoopStep': 6} 44
$ grep -n "^theorem baTwistGridRem_holds" RBM3D/BA/TwistGridRem2.lean     (target 1, statement)
394:theorem baTwistGridRem_holds (d : ℕ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridRem d C₀ := by
$ sed -n '465p;468,479p' RBM3D/BA/TwistGridRem2.lean     (target 2: the acceptance example and the typed instance)
example : ∀ d : ℕ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ BATwistGridRem d C₀ := baTwistGridRem_holds
example : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ CK : ℝ, 0 ≤ CK ∧
    ∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n),
      ∀ᵐ ω ∂((baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).Pp), ∀ k, k ≤ ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1 →
        ‖twRem sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3)
            (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep (fun _ => 1 / 2) (fun _ => 2 / 3)
            (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) n) := by
  obtain ⟨C₀, hC₀, hRem⟩ := baTwistGridRem_holds 3
  obtain ⟨CK, hCK, H2⟩ := hRem (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n)
  exact ⟨C₀, hC₀, CK, hCK, (H2 (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _))).2⟩
$ sed -n '483,490p' RBM3D/BA/TwistGridRem2.lean     (target 2: fed to the assembly)
example (hTail : BATwistGridTail 3) (hW : BATwistGridWTail 3) {D : ℝ} (hD : 0 < D) : True := by
  obtain ⟨C₀, hC₀, hRem⟩ := baTwistGridRem_holds 3
  have H := baTwistGridAssemble_holds 3 C₀ hC₀ hRem hTail hW
  obtain ⟨CK, hCK, H2⟩ := H (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) D hD
  have := H2 (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ + 1) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _))
  trivial
```
Ports: none from `../RBM1D`/`../RBM2D` (not read); the copies are from the merged RBM3D band files `Path/OneStep.lean:1667-2357`, `Path/LoopStep.lean:206-300`, `Path/DifREP1.lean:1089-1153` (themselves ports of RBM2D), so no RBM1D/RBM2D diff-stat is owed.
Narrative.
- Envelope for a word: for letters with `‖Eᵢ‖ ≤ 1` and any list `l`, `TwistGridRem_envelope_word` gives `‖E Φ_{u+Δ}(M+√ΔX) − Φ_u(M) − Δ (g_u(M) + J1_u(M))‖ ≤ 16 (k+3)⁴ N⁴ (1+η⁻¹)^{k+4} Δ^{3/2}`, `η = (1−u−Δ) Im m_F`, every real coupling `g`; at `k = 2` the constant is `10⁴ N⁴ (1+η⁻¹)⁶`.
- `TwistGridRem_twGenM_eq`: `twGenM = g_z + J1_z` (the line Hessian is the band's second jet `w2`; `TwistGrid_second` is not needed).  `‖P_{c₁c₂}‖ ≤ 1` by `‖A‖ ≤ Σ|A_{pq}|` (`W^d` entries of modulus `W^{-d}`).
- `TwistGridRem_step`: `‖E A_{u+Δ}(M+√ΔX) − A_u(M) − Δ twDriftM_u(M)‖ ≤ 10⁴N⁴(1+η⁻¹)⁶Δ^{3/2} + (1−u−Δ)⁻³Δ²` for Hermitian `M`, `0 ≤ u`, `u+Δ < 1`, `BAReal`, `0 < g₀`.
- Path level: the law of the walk is `pathP (sz.withLam 0)`, one step has the law `PF d L W 0` (`(sz.withLam 0).lam n = 0` by `rfl`, `Sizes.seqP_map_slice`); the clause holds on the set `{n : 0 < g₀_n, N_n ≥ max(1, c₁+8), N_n^6 ≤ K_n}`, for all `j < K_n` a.s. at once (`ae_all_iff`), with `K Δ = t − s ≤ 1`, `Δ N⁶ ≤ 1`.
- Norm scopes: file 2 opens `Matrix.Norms.L2Operator` (it gives `MeasurableAdd₂ (Matrix ..)` through `ContinuousAdd.measurableMul₂`); file 1 opens it per section and uses `Matrix.Norms.Operator` (the `ℓ∞` norm, as `EKPins`) only in §7.

## (c) Verified Mathlib names (by compile, `lake build` above)
`Real.rpow_natCast`, `Real.rpow_neg_one`, `Real.rpow_add'`, `Real.rpow_le_rpow_of_exponent_le`, `Real.sqrt_eq_rpow`, `Real.mul_self_sqrt`, `Real.sq_sqrt`, `pow_le_pow_left₀`, `one_le_pow₀`, `pow_le_one_iff_of_nonneg`, `inv_anti₀`, `inv_le_one_of_one_le₀`; `MeasureTheory.condExp_congr_ae`, `memLp_top_of_bound`, `integral_map`, `integral_sub`, `integral_finsetSum`, `norm_integral_le_of_norm_le`, `Integrable.of_bound`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `ae_all_iff`, `Measurable.const_add`, `Measurable.prodMk`; `image_norm_le_of_norm_deriv_right_le_deriv_boundary`, `HasDerivAt.scomp`, `HasDerivAt.ofReal_comp`; `Filter.Tendsto.eventually_ge_atTop`; `Matrix.trace_sub`, `Matrix.trace_sum`.
Changed or absent in this Mathlib: `add_le_add_right h c` has the shape `c + a ≤ c + b` (use `add_le_add h le_rfl`); `if_neg` is deprecated; `MeasurableAdd₂ (Matrix ..)` is not found without the `Matrix.Norms.L2Operator` scope.

## (d) Open issues and paper-delta candidates
1. **`open private` instead of copy.** 44 private names are reused: 32 from `Path/OneStep.lean`, 6 from `Path/LoopStep.lean`, 5 from `BA/TwistGrid.lean`, 1 from `BA/TwistPins.lean` (precedent `BA/Step2BA.lean:35`; the ticket said "copy" for the two `TwistGrid_*` lemmas, which are not needed).  If the dispatcher wants no private-name dependency, the fallback is to copy them into `TwistGridRem.lean`; it has room (1078 of 2,000 lines).
2. **Constants.** `C₀ = 11`, `CK = 6` are not optimal; the `κ`-dependence of `c₁` is absorbed by the `∀ᶠ n` of clause (ii) (it fails at `n = 0` of `sz0`, see (a); the instance quantifies over `n`).
3. **Registry/merge.** None.  The hub adds the two import lines in the order `TwistGridRem`, `TwistGridRem2`; downstream TL2d consumes `baTwistGridRem_holds` with TL2a3, TL2a4 through `baTwistGridAssemble_holds`.
4. **Paper-delta candidates:** none (the target is the merged pin of T2428; no new Lean/paper statement difference).
