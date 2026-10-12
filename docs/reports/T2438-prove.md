Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 03:41:09 UTC 2026

Target: `baTwistGridTail_holds d : BATwistGridTail d` for every `d` (`BA/TwistGrid2.lean:239`); `Δ = (t-s)/K`, `K Δ ≤ 1`, `Δ ≤ N^{-CK}`, `N = (WL)^d`, `η_u = (1-u) Im m_F`, `κ = 1/2` at the instance. Scripts: scratchpad `T2438/{var,thr,datum}.py` (mathematics only, no Lean).

### (i) Exponent table
| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | `CK(D)` | `2D + 20` (band `2m+2D+16`, `m = 2`; `CK` chosen after `D`, before `K`, `ε'`; no `κ, ε` dependence) | `Δ ≤ N^{-CK}` from `N^{CK} ≤ K`; shift row 4: `c₂N⁸Δ ≤ N^{-D}`; `Y` row 6: `16ΔP N^D ≤ N^{-D}/2` | shift: `N^{8+D+12-CK} = N^{-D}` exactly with `c₂ ≤ N^{D+12}`; `Y`: `N^{18+D-CK} = N^{-D-2}`, closes iff `32cP ≤ N²` |
| 2 | `η_u⁻¹` on `[s,t]` | `η_u ≥ η_{T0} = (1-T0) Im m/√T0 = √T0 Im z ≥ √(κ/(κ+1)) N^{-1+ε}`; need `η_u⁻¹ ≤ 16N` | `T0 = Im m/(Im m + Im z) ≥ κ/(κ+1)` from `κ ≤ Im m`, `Im z ≤ 1` (`BAdom` `BA/MFixedPoint:435`, `BAt0` `:279`); `(1-T0) Im m = T0 Im z` (`BAt0_mul` `:290`); `T0 < 1` (`BAt0_lt_one` `:285`); `Im m_F = Im m/√T0` (`FlowPins_BAmF_flow_im`, `BA/FlowPins:769`, **private**: copy) | `√((κ+1)/κ) N^{1-ε} ≤ 16N` iff `N^ε ≥ √((κ+1)/κ)/16`: eventually (`SizeTendsto`); at `κ = 1/2` all `N ≥ 1`. Instance: `1/η_{T0} = 3.267` vs `16N = 3.4e7` (datum output) |
| 3 | crude `‖twEEM‖` (twin of `difRep2_norm_STeeM_le_N` `:1277`) | `|twDerM| ≤ 2η⁻³` (two terms of (D.2), each `W^{-2d}·W^{2d}` terms `≤ η⁻³`); `‖twEEM(b,b')‖ ≤ 4Nη⁻⁶ ≤ c'N⁷`, `c' = 4·16⁶ = 67,108,864` | `S = 1` (`baFM`, `BA/FlowPins:327`) so `Σ_{xy} W^{-d} S_{[x][y]} = N`; Cauchy-Schwarz in `(b,b')`; `η⁻¹ ≤ 16N` | band `m=2`: `2N(16N)⁶`; twist is 2x larger (two-term gradient). Toy: `0.017 ≤ 2478` |
| 4 | shift `u_{j+1} → u_j` (twin of `difRep2_eeShift_sum_le` `:1353`) | `|twEEM_{u'}(a,a) - twEEM_u(a,a)| ≤ 24 N |z_{u'}-z_u| η_{u'}⁻⁷`, `|z_{u'}-z_u| = (u'-u)|m_F|`, `|m_F| = ‖m‖/√T0 ≤ √((κ+1)/κ)` (`BAm_norm_le_one` `BA/Ward:136`); `Σ_j Δ·err ≤ c₂N⁸Δ`, `c₂ = 24·16⁷√((κ+1)/κ) = 1.116e10` at `κ = 1/2` | `G(z')-G(z) = (z'-z)G(z')G(z)`, telescoping 3 factors per term, `||D'|²-|D|²| ≤ |D'-D|(|D'|+|D|)`; need `c₂ ≤ N^{D+12}` | `N ≥ 5.93` (`D = 1`), `N ≥ 6.88` (`D → 0`); band `c₂ = 12·16⁷ = 3.22e9`. Toy: `3.7e-3 ≤ 2726` |
| 5 | `C₂` of `Φ_b(M) = L̃_{u_{j+1}}(g₀Ψ+M)` (item 1 (a)) | `C₂ = 6Nη⁻⁴ ≤ 6N(16N)⁴` = band `m(m+1)N(16N)^{m+2}` at `m = 2` | `L̃ = Tr(G(σ₁) E_a G(σ₂) P_{c₁c₂})`: Leibniz `2+2+2 = 6` terms, `‖E_a‖, ‖P‖ ≤ W^{-d} ≤ 1`, trace `≤ N`·norm; `Im z_u = η_u > 0`, no `|E| < 2` needed | entrywise count gives `6η⁻⁴` (no `N`): not used. Toy: `0.106 ≤ 792` |
| 6 | `Y` budget | `P = 2000 C₂² N⁸ = c_P N^{18}`, `c_P = 2000·36·16⁸ = 3.092e14` | `16 Δ P N^D ≤ N^{-D}/2` at `Δ ≤ N^{-(2D+20)}` iff `32 c_P ≤ N²` | `N ≥ 9.95e7`; `N_0 = 2.1e6` fails, `N_1 = 5.5e11` passes (thr output) |
| 7 | `Z` budget | `(⌈c'N^{7+D}⌉ + 1)·4·exp(-N^{2ε'}/(64c)) ≤ N^{-D}/2`, levels `L = ⌈c'N^{7+D}⌉`, `ρ = N^{ε'}/2`, proxy factor `c ∈ {1,2,4}` (row 8) | polynomial against stretched exponential; eventual for all `D, ε' > 0` (twin of `difRepTail_eventually_Z` `:2112` with `64c` for `64m`) | at `ε' = 1/10, D = 1`: first `n`: `c=1`: 7 (`N = 3.78e22`); `c=2`: 9 (`2.10e24`, equals the T2428 row 9 value); `c=4`: 12 (`2.36e26`) |
| 8 | proxy factor `c` in `v_j ≤ c(a_j + e_j)`, `a_j = Δ‖twEEk‖`, `e_j = Δ·err_j` | exact variance identity `c = 1` (part (ii)); `difRep2_peel_N` takes `m ∈ ℕ`, `1 ≤ m`: `m = c` | `linTrVar(A), linTrVar(-iA) ≤ Σ_c gvar_c‖D_c‖²`; any `c ≥ 1` valid; Lean route by per-coordinate bound `|tr(AX_c)|² ≤ 2(‖A_ij‖²+‖A_ji‖²)` (`Universality/GUEPhase/DuhamelA1:135`, private) gives `c = 4` | `n_*` in row 7 for `c = 1, 2, 4` |
| 9 | `ε'`, `D`, exponent `1/2` | free `> 0`; `N^{ε'}(Σ_{j<k}Δ‖twEEk‖ + N^{-D})^{1/2}` | `ρ = N^{ε'}/2` each for `Z`, `Y` (core `:1951`) | none |

### (ii) Variance identity, reuse table, one nondegenerate instance
**Variance identity.** `∂_{xy}L̃_b = A_{b,yx}` (`twDerM`, (D.2)). The merged coordinates `(i,j,β)` (`Gauss/FineModel:89,384`) with `key i < key j` give `X = E_ij + E_ji`, `iE_ij - iE_ji`, and `gvar = S_ij/2`; the diagonal `X = E_ii`, `gvar = S_ii`; others are `0`. So `Σ_c gvar_c |Σ_b κ_b tr(A_b X_c)|² = Σ_{xy} S_{xy}|Σ_b κ_b ∂_{xy}L̃_b|² = Re Σ_{b,b'} κ_b κ̄_{b'} twEEM(b,b')` with **constant 1** (`S_xy = W^{-d}·1[[x]=[y]]`, `lam = 0`). Band: factor `k` through `qvPropagatedN` (`Induction/QVN.lean:813`) because a `k`-loop gradient has `k` terms; here the two terms of (D.2) sit inside `twDerM`. `K̃` deterministic cancels in `twMartInc`; `C₂` is row 5. Monte Carlo of the QV in T2428 (`T2428-prove.md:88`): ratios `1.0052, 1.0111, 1.0059, 1.0000`.
```
$ python3 var.py     (d=1 toy, L=3, W=2, N=6, random Hermitian H, E=0.3, m_F=0.37+0.81i, u=0.43; all 4 charge pairs x 3 (c1,c2), weights kappa on 3 labels)
(1) D.2 vs finite differences, and variance identity with weights kappa
   max rel err (D.2 vs fd): 1.7972930860582865e-10
   max rel err sum_c gvar_c|sum_b k_b d_c L_b|^2 vs Re sum k k' twEEM (factor 1), and |Im|: 8.731551897674674e-11
(2) crude: |twDerM|max=0.09506 <= 2 eta^-3=20.32 ; twEEM(b,b)=0.01722 <= 4 N eta^-6=2478
(3) shift: |twEEM_u' - twEEM_u|=0.003671 <= 24 N |dz| eta'^-7=2726  (|dz|=0.04453=(u'-u)|mF|=0.04453)
(4) |d^2 L~[y,y]|=0.1063 <= 6 N eta^-4 ||y||^2=792.3 ; (entrywise-sharper 6 eta^-4=132)
```
**Reuse table** (`DifREP2.lean` lines, band size in lines): imported, public and model-free: `difRep2_peel` `:478`, `difRep2_peel_N` `:757`, `azumaRandProxy_max` `:283` (inside the peel), `stepDecompCN` `StepDecompN:844`, `stepDecompCN_Z_subG` `:881`, `stepDecompCN_Y_sq` `:965`, `AzumaProxyN_integral_normPow8_incr_le` `AzumaProxyN2:367`, `condExp_freeze` `Markov:57`, `linTrVar` `Markov:238`. Copied with the stem (private): §1c `659-756` (98), §2 `801-917` (117), §3 `921-956` (36), §5 `1051-1187` (137), §8 `1541-1768` (228, sequences retyped), §9 `1772-1910` (139), §10 `1914-2090` (177), §11 `2094-2167` (74), §12 `2170-2276` (107). Rewritten for the twist: §4 `960-1039` (80, row 8), §6 `1191-1390` (200, rows 3-4), §7 `1392-1539` (148, public `TwistGridTail_condMGF_Z`). Dropped (loop-specific): `STeeLoop` §6 part, §13-14. **Not in the ticket's list:** `AzumaProxyN_YfieldsW` (`AzumaProxyN2:1025-1226`, 202) is stated for `loopFamN` and uses the private `azumaProxy2_moments_of_dom`, `_condExp_stopped_reim`, `_condExp_incr`, `_measurable_normX` (`:385-538`, 154): the twist needs a copy generic in `Φ` (through the public `stepDecompCN`). Row 5 also needs a twisted `HermTestFun` and second-derivative bound: the loop word jets `LoopC2N:150-470` and `TwistGrid:467` (`TwistGrid_second`) are private, so copy. No `3 ≤ d` is used: `stepDecompCN` and the peel are for every `sz`, `three_le_L` is a field of `Sizes`.
Band lines of the copied and rewritten parts: 1,541; with the two twins above 356 + about 200 to 410, the total is 2,100 to 2,300 by band line counts: above 1,700, so plan for `TwistGridTail2` (ticket (v)).

**Instance** (target 1 and 2): `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))⁵`, `lam_n = (2(n+1))⁻⁶`, `Defs/Sizes:260`), `zSeq` (`z_S = 6i/5 - m_S`), `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/2 < t ≡ 2/3 ≤ T0` (`t0_sz0`, `BA/FlowPins:1227`: `T0 ≥ 2/3`), `D = 1`, `ε' = 1/10`, `CK = 22`, `K_n = ⌈N_n^{22}⌉ + 1` (`log10 K_7 = 496.7`; passed as a function, never evaluated), the label `i = (σ, a, c₁, c₂)` is quantified inside the pin (no instance datum); the conclusion is eventual in `n`, and the proof's budgets close from `n_* = 7` (`c = 1`; 9 for `c = 2`; 12 for `c = 4`): `N_7 = 3.78e22` (thr output). Then fed to `baTwistGridAssemble_holds 3` with `BATwistGridRem 3 11`, `BATwistGridWTail 3` as hypotheses of the example only (T2437, T2439); target 1 has no external hypothesis, so the owed limit computation is the budget limit of rows 6-7 (`thr.py`, evaluated at `n = 0..9`).
```
$ python3 datum.py   (BA datum of sz0: m_S = L^-d tr(g Psi^B - 6i/5)^-1 with Psi^B the adjacency of Z_L^3, z_S = 6i/5 - m_S, T0 = Im m/(Im m + Im z), m_F = m/sqrt(T0))
n=0 L=4 W=32 g=0.015625 N=2097152  |self-consistency resid|=0.00e+00
  Im m=0.832488 (>=kappa=0.5:True, >=4/5:True) Im z=0.367512 in [N^(-1+eps)=2.044e-06, 1]:True  Im z+Im m=1.200000
  T0=0.693740 >= 2/3:True >= kappa/(kappa+1)=0.3333 ;  window s=0.5000 < t=0.6667 <= T0:True
  |m|=0.832488 <= 1:True ; |mF|=0.999493 <= sqrt((k+1)/k)=1.732051:True ; Im mF=0.999493
  eta_t=0.333164 eta_T0=0.306105 = sqrt(T0) Im z=0.306105 ; eta_T0 >= sqrt(k/(k+1)) N^(-1+eps)=1.180e-06:True ; 1/eta_T0=3.267 <= 16N=3.355e+07:True
n=7 L=32 W=1048576 g=5.96046e-08 N=37778931862957161709568  |self-consistency resid|=0.00e+00
  Im m=0.833333 (>=kappa=0.5:True, >=4/5:True) Im z=0.366667 in [N^(-1+eps)=4.792e-21, 1]:True  Im z+Im m=1.200000
  T0=0.694444 >= 2/3:True >= kappa/(kappa+1)=0.3333 ;  window s=0.5000 < t=0.6667 <= T0:True
  |m|=0.833333 <= 1:True ; |mF|=1.000000 <= sqrt((k+1)/k)=1.732051:True ; Im mF=1.000000
  eta_t=0.333333 eta_T0=0.305556 = sqrt(T0) Im z=0.305556 ; eta_T0 >= sqrt(k/(k+1)) N^(-1+eps)=2.766e-21:True ; 1/eta_T0=3.273 <= 16N=6.045e+23:True
$ python3 thr.py     (budgets along sz0, D=1, eps'=1/10, kappa=1/2, CK=2D+20=22)
c' = 4*16^6 = 67108864 ; c2^tw = 24*16^7*sqrt(3) = 1.11587e+10 ; cP = 2000*36*16^8 = 3.09238e+14 ; 32 cP = 9.8956e+15 ; CK = 2D+20 = 22.0
band c2 = 12*16^7 = 3221225472 ; band cP = same
c=1 (exponent N^{2e'}/(64c)): first n with Z,shift,Y budgets all true: n*=7  N*=3.778e+22
c=2 (exponent N^{2e'}/(64c)): first n with Z,shift,Y budgets all true: n*=9  N*=2.097e+24
c=4 (exponent N^{2e'}/(64c)): first n with Z,shift,Y budgets all true: n*=12  N*=2.358e+26
 c=1 n=0 N=2.097e+06  Z:False shift:True Y:False  log10 K_n=ceil(N^22)+1: 139.1
 c=1 n=1 N=5.498e+11  Z:False shift:True Y:True  log10 K_n=ceil(N^22)+1: 258.3
 c=1 n=2 N=8.125e+14  Z:False shift:True Y:True  log10 K_n=ceil(N^22)+1: 328.0
 c=1 n=3 N=1.441e+17  Z:False shift:True Y:True  log10 K_n=ceil(N^22)+1: 377.5
 c=1 n=5 N=2.13e+20  Z:False shift:True Y:True  log10 K_n=ceil(N^22)+1: 447.2
 c=1 n=7 N=3.778e+22  Z:True shift:True Y:True  log10 K_n=ceil(N^22)+1: 496.7
 c=1 n=8 N=3.148e+23  Z:True shift:True Y:True  log10 K_n=ceil(N^22)+1: 517.0
 c=1 n=9 N=2.097e+24  Z:True shift:True Y:True  log10 K_n=ceil(N^22)+1: 535.1
```
The `self-consistency resid` is `0` by construction (`z_S + m_S = w`); the nondegeneracy content is `Im m ≥ κ`, `N^{-1+ε} ≤ Im z ≤ 1`, `T0 ≥ 2/3 ≥ t`, `1/η ≤ 16N`.

### Verdicts
- Target 1 `baTwistGridTail_holds d` (every `d`): **PASS**. `CK = 2D + 20` closes (rows 1, 4, 6; slack row 1); the proxy constant is 1 exactly (row 8), `c ∈ {1,2,4}` all close; no hypothesis set is empty; no `3 ≤ d`. Findings for 1b (not defects of the statement): the `Y`-moment twin (`YfieldsW`, 356 lines) and the twisted `C₂` jets are not importable (reuse table); `FlowPins_BAmF_flow_im` is private.
- Target 2 (instance): **PASS** (`n_* = 7` for `c = 1`; the three part pins of `baTwistGridAssemble_holds` stay example hypotheses).
- Target 3 (registry): none.

## (b) Script output — Mon Oct 12 04:52:45 UTC 2026 (stage 1b, ticket role `prover-hard`, branch `t/T2438`, commit `7c201be`)
**Summary** (each item is shown by the output below): `CK(D) = 2D + 20`; the variance identity `Σ_c gvar_c |Σ_b κ_b tr (Der_b X_c)|² = Re Σ_{b,b'} κ_b conj κ_{b'} twEEM(b,b')` has constant `1` (no factor `k`);
`TwistGridTail.lean` 1501 lines and `TwistGridTail2.lean` 449 lines against the stop line 2,000 per file; **`TwistGridTail2` was used**: the content totals 1950 lines, above the 1,700 trigger, so the one-size-index tail, target 1 and its instance are in file 2 (the ticket's split).
```
$ git log -1 --format=%h; date -u
7c201be
Mon Oct 12 04:50:23 UTC 2026
$ lake build RBM3D.BA.TwistGridTail RBM3D.BA.TwistGridTail2 2>&1 | tail -1
Build completed successfully (4026 jobs).
$ [RBM3D.lean temporarily + import RBM3D.BA.TwistGridTail, RBM3D.BA.TwistGridTail2; reverted, not committed] lake build 2>&1 | tail -1
Build completed successfully (4254 jobs).
$ lake env lean RBM3D/BA/TwistGridTail.lean | wc -l; lake env lean RBM3D/BA/TwistGridTail2.lean | wc -l   (warning and error lines)
0
0
$ grep -c "sorry\|admit\|native_decide\|^axiom" RBM3D/BA/TwistGridTail.lean RBM3D/BA/TwistGridTail2.lean
RBM3D/BA/TwistGridTail.lean:0
RBM3D/BA/TwistGridTail2.lean:0
$ lake env lean ax.lean   [import RBM3D.BA.TwistGridTail2; #print axioms of the three public declarations]
'RBM.BA.baTwistGridTail_holds' [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistGridTail_condMGF_Z' [propext, Classical.choice, Quot.sound]
'RBM.BA.TwistGridTail_phi' [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2438-check.lean (main worktree file, branch toolchain); echo exit
exit=0
$ wc -l RBM3D/BA/TwistGridTail.lean RBM3D/BA/TwistGridTail2.lean
    1501 RBM3D/BA/TwistGridTail.lean
     449 RBM3D/BA/TwistGridTail2.lean
    1950 total
$ git diff --stat main...t/T2438
 RBM3D/BA/TwistGridTail.lean  | 1501 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/TwistGridTail2.lean |  449 +++++++++++++
 2 files changed, 1950 insertions(+)
$ grep -n "^theorem\|^def\|^lemma\|^abbrev\|^instance\|^structure" RBM3D/BA/TwistGridTail.lean RBM3D/BA/TwistGridTail2.lean   (public declarations)
RBM3D/BA/TwistGridTail.lean:196:def TwistGridTail_phi (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
RBM3D/BA/TwistGridTail.lean:949:theorem TwistGridTail_condMGF_Z (j : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L
RBM3D/BA/TwistGridTail2.lean:304:theorem baTwistGridTail_holds (d : ℕ) : BATwistGridTail d := by
```
```
$ sed -n '239,246p' RBM3D/BA/TwistGrid2.lean | cut -c1-120     (the merged pin; the target is its type)
def BATwistGridTail (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK 
      ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) → ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp) {ω | ∃ k, k ≤ K n ∧
          ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s t K n *
            ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 j ω‖ + ((sz.size n : ℕ) : ℝ) ^
          ‖twMart sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n i.1 i.2.1 i.2.2.1 i.2.2.2 k ω‖} ≤ ENNReal.ofReal (((sz.si
$ sed -n '304p;306p' RBM3D/BA/TwistGridTail2.lean     (target 1; CK)
theorem baTwistGridTail_holds (d : ℕ) : BATwistGridTail d := by
  refine ⟨2 * D + 20, by positivity, ?_⟩
$ sed -n '196,198p' RBM3D/BA/TwistGridTail.lean | cut -c1-130     (the twisted family, public)
def TwistGridTail_phi (u : ℝ) (σ : Fin 2 → Bool) (c₁ c₂ b : Zd d (sz.L n))
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℂ :=
  twL2M sz lam0 E n u (((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) + M) σ b c₁ c₂
$ sed -n '531,535p' RBM3D/BA/TwistGridTail.lean | cut -c1-130     (variance identity)
private theorem TwistGridTail_quadVar (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (κ : Zd d (sz.L n) → ℂ) :
    ∑ c : CoordF d (sz.L n) (sz.W n), (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) *
        ‖∑ b, κ b * Matrix.trace (TwistGridTail_Der sz lam0 E n u H σ b c₁ c₂ * coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 =
      (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * twEEM sz lam0 E n u H σ b b' c₁ c₂).re := by
$ sed -n '949,952p' RBM3D/BA/TwistGridTail.lean | cut -c1-130     (TwistGridTail_condMGF_Z, hypotheses; conclusion: 2 integrability + 2 conditional-mgf conjuncts, next 16 lines)
theorem TwistGridTail_condMGF_Z (j : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n))
    (hm : 0 < (BAmF sz lam0 E n).im) (hu : gridTime s t K n (j + 1) < 1) (hΔ : 0 ≤ gridStep s t K n)
    (κ : Zd d (sz.L n) → ℂ) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * (stepZCN (sz.withLam 0) s t K n j
$ sed -n '419,420p;425,429p;432p;435,436p' RBM3D/BA/TwistGridTail2.lean | cut -c1-130     (instances of target 1)
example : ∃ CK : ℝ, 0 ≤ CK ∧ ∀ᶠ n in atTop, ∀ i : (Fin 2 → Bool) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n),
    ((baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).Pp) {ω | ∃ k, k ≤ TwistGridTail2_Kinst CK n ∧
      ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨CK, hCK, H⟩ := baTwistGridTail_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z
    (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) 1 one_pos
  exact ⟨CK, hCK, H (TwistGridTail2_Kinst CK) (fun n => Nat.succ_ne_zero _)
    (Eventually.of_forall fun n => (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)) (1 / 10) (by norm_num)⟩
example : ∀ d, BATwistGridTail d := baTwistGridTail_holds
example (hRem : BATwistGridRem 3 11) (hW : BATwistGridWTail 3) : BATwistGridMartAt 3 11 :=
  baTwistGridAssemble_holds 3 11 (by norm_num) hRem (baTwistGridTail_holds 3) hW
$ sed -n '1486,1487p;1494,1497p' RBM3D/BA/TwistGridTail.lean | cut -c1-130     (instance of TwistGridTail_condMGF_Z)
example : Integrable (fun ω => Real.exp (1 * (stepZCN (sz0.withLam 0) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0 0
        (TwistGridTail_phi sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 (gridTime (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4
  have h := TwistGridTail_condMGF_Z sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => 4) 0
    ![false, true] 0 ![1, 0, 0] (BAmF_sz0_im_pos 0) (by norm_num [gridTime, gridStep]) (by norm_num [gridStep])
    (fun a : Zd 3 (sz0.L 0) => if a = ![1, 0, 0] then (1 : ℂ) else 0) 1
  exact ⟨h.1, h.2.1⟩
$ python3 budgets.py | grep 'CK\|n=7\|n=8'   (scratchpad T2438/budgets.py: shift 24*16^7<=N, Y 32*768*36*16^8<=N^2, Z (ceil(4*16^6 N^8 N^D)+1)*4*exp(-N^(2e')/64)<=N^-D/2 along sz0, D=1, e'=1/10)
CK = 2D+20 = 22.0
n=7 N=3.778e+22 Z:False shift:True Y:True  log10K=ceil(N^22)+1:496.7
n=8 N=3.148e+23 Z:True shift:True Y:True  log10K=ceil(N^22)+1:517.0
$ grep -rn 'norm_entry_le_l2\|l2_opNorm_le_frobenius\|theorem condExp_re\b' .lake/packages/mathlib/Mathlib | wc -l     (names verified absent)
0
```
```
$ for b in <local branches>; do git grep -l "baTwistGridTail_holds\|TwistGridTail_phi\|TwistGridTail_condMGF_Z" $b -- RBM3D docs/tickets/checks; done   (name clash)
t/T2438:RBM3D/BA/TwistGridTail.lean
t/T2438:RBM3D/BA/TwistGridTail2.lean
```
RBM1D/RBM2D diff-stat: not applicable; no text was ported from `../RBM1D` or `../RBM2D` (nothing under them was read or run). The adapted band text is RBM3D's own:
`DifREP2.lean` (`76b840e`) `:1404-1537` (condMGF), `:1623-1659` (vSeq_le), `:1740-1766` (Z_tail), `:1790-1908` (Y_tail), `:1951-2087` (core), `:2112-2165` (eventually_Z), `:2180-2275` (main);
`StepDecompLoop.lean` (`e88681b`) `:337-452, 603-658` (observable, `C²`, second derivative); `QVIdentity.lean` (`fe32346`) `:553` (coordinate sum); `StepDecompN.lean` (`45ca385`) (`stepDecompCN`, `stepDecompCN_Y_sq`).

**Narrative.**
- Proved: `baTwistGridTail_holds d : BATwistGridTail d` for every `d` (pin unchanged, no `3 ≤ d`), `CK = 2D + 20`. New public names: `TwistGridTail_phi`, `TwistGridTail_condMGF_Z`, `baTwistGridTail_holds`; the other 74 declarations are `private` (`grep -c '^private'`: 71 + 3).
- (a) of the ticket: `stepDecompCN` at `sz.withLam 0` for `Φ_b(M) = L̃_{u_{j+1}}(g₀Ψ + M)`; `HermTestFun` and `C₂ = 6 N η⁻⁴` are proved on the fine lattice (`L̃ = tr (G₁ E_b G₂ Q_{c₁c₂})`, `‖E_b‖, ‖Q‖ ≤ W^{-d}`, `Matrix` jets of `StepDecompLoop`); `K̃` cancels a.e. in `twMartInc` (`TwistGridTail_martInc_ae`).
- (b): `dirDerivN Φ_b M X = tr (Der_b X)` with `Der_b` the matrix of (D.2) (`TwistGridTail_Der_eq`); the coordinate sum `QVIdentity_coord_sum` then gives constant `1` (not the band's `k`), so the peel runs at `c = 1`.
- (c): `Z` by `difRep2_peel` (`c = 1`, `ρ = N^{ε'}/2`, exponent `N^{2ε'}/64`); `Y` by Doob; the proxy shift `u_{j+1} → u_j` costs `24 N² Δ η⁻⁷` per step; budgets `24·16⁷ ≤ N`, `32·768·36·16⁸ ≤ N²`, `Z` eventually.
- Deviations from the ticket's route (none changes a statement): (i) the private band helpers are reached by `open private` (pattern `BA/Step2BA.lean:35`) instead of copies (`TwistGridTail.lean:45-55`, `TwistGridTail2.lean:30-33`);
  (ii) `difRep2_peel` at `c = 1` instead of `difRep2_peel_N`; (iii) the `Y` fields come from `stepDecompCN` (iii), (iv) and `stepDecompCN_Y_sq` (`∫‖Y‖² ≤ 768 C₂² Δ² N⁸`, unconditional second moments suffice for Doob), so `AzumaProxyN_YfieldsW` and its private moment lemmas are not used.
- Constants differ from (a) rows 3-6, none is a defect of (a): the crude counts use the number of pairs `N²` (not `N`): `‖twEEM‖ ≤ N²(2η⁻³)² ≤ 4·16⁶ N⁸`, shift `24·16⁷ N⁹ Δ ≤ N^{-D}` (a: `N⁸`, `c₂ ≤ N^{D+12}`), `P = 768·36·16⁸ N¹⁸` (a: `2000·36·16⁸ N¹⁸`).
  `η_u ≥ (Im z/2) κ` from `EMn2BA_one_sub_T0`, `EMn2BA_mF_data` gives `1/(16N) ≤ η_u` once `N^ε ≥ 1/(8κ)`; `‖m_F‖ ≤ 1` from `BAm_norm_le_one` (a: `√((κ+1)/κ)`).
- Instance: the first `n` at which the three budgets of the proof all hold at the BA datum is `n = 8` (script above scans `n = 0..12`, shows `n = 7, 8`; (a) predicted `n_* = 7` with the `N⁷` bound); the theorem is eventual in `n`.
- Not done here (other rows): `BATwistGridRem` (T2437), `BATwistGridWTail` (T2439); the assembly example keeps them as hypotheses.

## (c) Verified Mathlib names (a `#check` run on the branch: 28 names, 0 errors; absent: see the `grep` count 0 above)
`Matrix.l2_opNorm_diagonal`, `Matrix.l2_opNorm_conjTranspose_mul_self`, `Matrix.l2_opNorm_conjTranspose`, `Matrix.trace_mul_comm`, `Matrix.mul_diagonal`, `Matrix.diagonal_mul`, `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`, `Matrix.isUnit_iff_isUnit_det`,
`Finset.sum_ite_mem`, `pi_norm_le_iff_of_nonneg`, `contDiffAt_ringInverse`, `MeasureTheory.MemLp.condExp`, `MemLp.mono'`, `MemLp.of_le`, `condExp_sub`, `condExp_const`, `ae_all_iff`, `ae_iff`, `ContinuousLinearMap.comp_condExp_comm`,
`measureReal_union_le`, `ofReal_measureReal`, `norm_le_norm_add_norm_sub'`, `Complex.norm_le_sqrt_two_mul_max`, `Complex.normSq_eq_norm_sq`, `Nat.lt_two_pow_self`, `tendsto_rpow_atTop`, `Measurable.of_eval_matrix`.
Verified absent: `Matrix.norm_entry_le_l2_opNorm`-type lemma (used `norm_matrix_entry_le_opNorm`, `Gauss/FlowCalculus.lean:591`), a `condExp_re` (used `RCLike.reCLM.comp_condExp_comm`).

## (d) Open issues and paper-delta candidates
- `T2438a`: grid exponent `CK = 2D + 20` hard-coded (`TwistGridTail2.lean:306`; the band's `2m + 2D + 16` at `m = 2`); the QV constant of the twisted gradient is `1` (band loops: `k`).
- No other Lean/paper statement difference: the pin `BATwistGridTail` is the merged one, unchanged; Azuma with a random predictable proxy in place of BDG is the existing delta D90.
- Open: the new files depend on private names of `Path/DifREP2`, `Path/StepDecompLoop`, `Path/QVIdentity`, `Induction/StepDecompN`, `Induction/GridAssemblyN` (`open private`); a rename there breaks the build, not a statement.
- No `(a′)` section: the differences from (a) are different routes and looser constants, not mistakes.
