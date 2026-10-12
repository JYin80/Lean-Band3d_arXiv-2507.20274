Prover model: claude-sonnet-5-5
## (a) Math preflight — Sun Oct 11 22:22:37 UTC 2026
Notation: `k = d-2 ≥ 1`; `κ ≤ Im m` the model bulk constant; kernel `g = g₀ = √t₀·lam ≤ lam`, `t₀ = Im m/(Im m + Im z) ≥ κ/(κ+1)` (BAdom `Im z ≤ 1`); `m_F = m/√t₀`, `κ ≤ Im m ≤ Im m_F ≤ 1` (`EMn2BA_mF_data`, `BA/EMn2BA.lean:125`); `Q = M^{(σ₁σ₂)}`, `‖Q‖_{∞→∞} ≤ 1`, `Ξ = (u-v)QΘ_u`.

### (i) Exponent table
| row | value | constraint | slack |
|---|---|---|---|
| T.10(a) factor | `(1-v)/(1-u)` | `‖I+Ξ‖ ≤ 1+(u-v)‖Q‖‖Θ_u‖ ≤ 1+(u-v)/(1-u)` (`‖Θ_u‖ ≤ (1-u)⁻¹`) | 0 at `u=v`; script ratio max 1.0000 |
| (b) `C₁` | `4·C₀·ballC(k)`, `C₀ = C₅(1+2(2d)^k)+Λ²+1` (`baEKXiBall_holds` via `baEKXiDecay_holds`, `EKPins.lean:545-556`), `C₅` of `baProp5_holds(d,Λ,κ)` | ball lemma needs `1 ≤ Λ' = W^ε`, `1 ≤ R = W^ε ℓ_v(g)`, `g²/L² ≤ 1-u`, `0 ≤ v` | `W^ε > 1`; `ℓ_v ≥ 1` (`one_le_ellT`); measured `C₁` needed 0.034 / 0.028 |
| (b) far part | `≤ W^{-D}·(u-v)/(1-u) ≤ W^{-D}(W-1) ≤ W^{-D+1}` | `W⁻¹ ≤ (1-u)/(1-v)` (pin hypothesis); `ε<1`, `D>1` unused | factor `W/(W-1)` |
| (b) near/far split | near `zdistD(b-c₁) < W^ε ℓ_v`, `zdistD(-x)=zdistD x` | `D = near`, `R = W^ε ℓ_v` equals `Λ'ℓ_v` | 0 |
| (d) `C(A)` | `2 + A·C₀′·E_k`, `E_k = e^{√(k+2)}2^{k+2}radC 1`, `C₀′` of `baProp8_holds` (any `t ∈ [0,1)`) | `(u-v)(g²+|1-u|)⁻¹L² ≤ (1-v)L²/g² ≤ A` replaces `EKNonzero_coef` (A=1) | two inequalities (`u-v ≤ 1-v`, `(g²+|1-u|)⁻¹ ≤ g⁻²`); A=1 is the merged `2+C₀E_k` |
| (d) `A` | `A = (κ+1)/κ` | `g² = g₀²/t₀ ≤ ((κ+1)/κ) g₀²` | at κ=1/2: A=3, `1/t₀ = 1.44` (slack 1.56) |
| F1 `ℓ` chain | `ℓ_v(g₀) ≤ ℓ_v(lam) ≤ √((κ+1)/κ)·ℓ_v(g₀)` | `ellT = min(max(g/√|1-v|,1),L)` increasing in `g`; `lam/g₀ = t₀^{-1/2} ≤ √((κ+1)/κ)` | script F1 line, 100 `v`, both data |
| F1 uses here | (1) T.1(iii): hypothesis at `ℓ_v(lam)` implies it at `ℓ_v(g₀)` (forward, no ε loss); (2) T.11(v), `twDec` and `twSteps` conj 4: both cut at `ℓ_v(lam)`, same scale; (3) T.10 (a),(b),(d): the kernel's own `g` | reverse step `ε′ = ε+log(3√((κ+1)/κ))/log W` is not needed by any of the 8 targets (it is TL2d's use of (b)) | A=(κ+1)/κ only fixes the instance of (d) |
| T.1(iii) prefactor | `Θ ≤ C·B_{t,K}e^{-cK/ℓ}`, `B_{t,K} ≤ g₀⁻²+(L^d(1-t))⁻¹`; `g₀⁻² ≤ ((κ+1)/κ)W^{d-2𝔡}`; `(L^d(1-t))⁻¹ ≤ 2W^{d(1-ε)}` (`1-t ≥ 1-t₀ ≥ Im z/2 ≥ N^{-1+ε}/2`, `N=(WL)^d`) | `lam ≥ W^{-d/2+𝔡}` (WO), `t₀ ≥ κ/(κ+1)`, `Im m ≤ 1` | exponents 2.8 and 2.7 at `d=3, 𝔡=ε=1/10`; `W^{-d}` cancels |
| T.1(iii) rate | `|K̃| ≤ C₄e^{-c₃W^{ε₁}}`, `c₃ = min(c/2, r/2)`, `r = BAct_rate d Λ κ = min(log(1+κ/(4dΛ)), κ/2)`, `Λ = 𝔡⁻¹` | split `|a-a'| ≥ X/2` (Θ factor, `Σ|M||M| ≤ C_M r⁻¹`) or `|a'-c₁| ≥ X/2` (`M` factor, `sup|Θ|` and `Σ_{a'}|M|`); `X ≥ W^{ε₁}ℓ(g₀)`; `zdistInf ≤ zdistD` | factor 2 (X/2); no `L` bound needed |
| T.1(iii) `W₀(ε₁,D)` | `c₃W^{ε₁} ≥ D ln W + ln C₄` | any `ε₁, D > 0` | route threshold at `(1/10, 2, κ=1/2, 𝔡=1/10)`: `ln W₀ ≈ 116` (`C₄` dropped), enters only `∀ᶠ n`, no hypothesis |
| T.11 (i) | `2` | `W^d·Bctl²·C(W^dη)⁻¹ = Cη⁻¹Bctl²` (`twSteps` k=2, `twK_bound` (ii)) | 0 |
| T.11 (ii) | `2` | `W^d·(Bctl [STAvgUgL])·(W^dη)⁻¹·(Bctl⁰·Bctl²)^{1/2}` (T.4, n=3) `= η⁻¹Bctl²` | 0 |
| T.11 (iv) | `γ+1/6`, `γ ∈ [1,2]` | `1/5 - 𝔠d·Cd ≥ 1/6 ⇔ 𝔠dCd ≤ 1/30`; `𝔠d = min(1/100, 1/(30Cd))` (`stSumTwoLoop_exists`, `KDecay.lean:1339`) | `1/30 - 𝔠dCd = 0.0233` at Cd=1; 0 for Cd ≥ 10/3; use the `(1-t)⁻¹` form of `KDecay.lean:1328`, `(1-t)⁻¹ ≤ η⁻¹` since `Im m_F ≤ 1` |
| T.11 `Dw` | `Dw ≥ 1/𝔠+d+1` (=10 at `𝔠=1/6, d=3`) | `N W^{-Dw} ≤ Bctl` (`SEforLn2_sum2` `hWD`): `N ≤ W^{1/𝔠}`, `Bctl ≥ W^{-d}/(1+𝔡⁻²)`, `W ≥ 1+𝔡⁻²` | eventually |
| T.11 (v) | cut `3W^εℓ = W^εℓ + 2W^εℓ`; `D′ = D+1/𝔠+1` (=9 at D=2) | `|a-c₁| ≥ 3W^εℓ ⇒ |b-c₁| ≥ W^εℓ or |a-b| ≥ 2W^εℓ`; `N·W^{ε′}W^{-D′} ≤ W^{-D}`, `ε′ ≤ 1` | `W^εℓ` in the cut |
| a-priori `N^C` | `‖G_u‖ ≤ η_u⁻¹ ≤ 2N^{1-ε}/κ` for `u ≤ t₀` | `η_u ≥ κ(1-t₀) ≥ κ Im z/2 ≥ κN^{-1+ε}/2` | script: `1-t₀ ≥ Im z/2` at n=0,1,2 |
| T.11(iv) hyp `Ξ` | `Ξ_n = max(1, poly(N)/Bctl_min^γ)` | `‖Z_v‖ ≤ ‖G‖²+C·Bctl ≤ (2N^{1-ε}/κ)²+C`, `Bctl ≥ W^{-d}/(1+𝔡⁻²)` | satisfiable: hypothesis not vacuous |

### (ii) One concrete nondegenerate instance
Data (`d=3`). T.10: flow points `(L, lam) = (4, 1/2)` and `(8, 2)` of `M = (g₀Ψ - (E+m_F))⁻¹`, `m = L⁻³tr(lamΨ - 6i/5)⁻¹`, `κ := Im m` (model), `Λ = max(1, lam)`; (b) `W=16, ε=1/2, D=2`, `(v,u) = (0,1/2)` resp. `(0.6,0.8)`, `c₁=0`, `A` random with `|A_b| ≤ W^{-D}` on the far set, near set a proper subset (`#far` 22/64, 302/512); (d) with `A = 1, (κ+1)/κ, 5` (A > 1 exercised), `u = 1-10⁻³g₀²/L²`. T.1(iii), T.11: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))⁵`, `lam_n = (2(n+1))⁻⁶`), `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)` (`flow_sz0`, `FlowPins.lean:1214`, proved in Lean; the script re-checks BAdom, bandwidth, WO), `ε₁ = 1/10`, `D = 2`, `c₁ = 0`, all `c₂`, `v ∈ {0, 1/2, t₀}`; T.11 frame `s ≡ 1/2`, `t ≡ 0.55 ≤ 2/3 ≤ t₀` (`t0_sz0`, `FlowPins.lean:1227`), `Cd = 1`, `𝔠d = 1/100`, regime `STAny`. Cut region nonempty for every n: `a-c₁ = (2(n+1),0,0)` has `zdistInf = 2(n+1) ≥ (2(n+1))^{1/2} = W_n^{1/10}` and `ℓ_v(lam_n) = 1` for `v ≤ t₀` (`lam_n ≤ 1/64`).
External hypothesis `twSteps` (other gates' pins) and `(con_st_ind)`: limit computation in the `[lim]` and `[T11]` lines (`Bctl_n(t)·(2(n+1))^{15} → 1/(1-t)`, so `Bctl_n^{𝔠d} → 0 < (1-t)/(1-s)`; `n₀ = 1` for `t = 0.55`; for `t = 2/3` already `n₀ = 8`, `L=36, W=1889568`).
Command (script `…/scratchpad/T2429/inst.py`, numpy, no Lean): `python3 inst.py > out.txt` (8 s). Output verbatim:
```
[T10] L=4 lam=0.5: t0=0.4466 g0=0.3341 kappa=Im mS=0.5359<=Im mF=0.8019, Im zS=0.6641<=1:True Lambda=max(1,lam)=1 g0<=Lambda:True BASelf residual=1.1e-16
  F1: ell_v(g0)<=ell_v(lam)<=sqrt((kappa+1)/kappa)*ell_v(g0)=1.693*ell_v(g0) for 100 v in [0,.99]: True
  (a) max over 4 charges, 4 (v,u): ||U||/((1-v)/(1-u)) = 1.0000 <= 1: True
  (b) W=16.0 eps=0.5 D=2.0 v=0.0 u=0.5: {'regime': True, 'Winv': True, 'R_ge_1': True, 'ell': 1.0, 'R': 4.0}; far part ||Xi||<=(u-v)/(1-u)<=W-1: True; C1needed=0.0335
      #far b (A tiny)=22 of 64; max LHS/RHS over charges = 0.7213
  (d) u=1-1e-3 g0^2/L^2; A=1.000: v=0.99302 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=1.995 | A=2.866: v=0.98000 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=2.043 | A=5.000: v=0.96511 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=2.098
[T10] L=8 lam=2.0: t0=0.1774 g0=0.8424 kappa=Im mS=0.2129<=Im mF=0.5054, Im zS=0.9871<=1:True Lambda=max(1,lam)=2.0 g0<=Lambda:True BASelf residual=8.6e-17
  F1: ell_v(g0)<=ell_v(lam)<=sqrt((kappa+1)/kappa)*ell_v(g0)=2.387*ell_v(g0) for 100 v in [0,.99]: True
  (a) max over 4 charges, 4 (v,u): ||U||/((1-v)/(1-u)) = 1.0000 <= 1: True
  (b) W=16.0 eps=0.5 D=2.0 v=0.6 u=0.8: {'regime': True, 'Winv': True, 'R_ge_1': True, 'ell': 1.331972822989796, 'R': 5.327891291959184}; far part ||Xi||<=(u-v)/(1-u)<=W-1: True; C1needed=0.0281
      #far b (A tiny)=302 of 512; max LHS/RHS over charges = 0.6733
  (d) u=1-1e-3 g0^2/L^2; A=1.000: v=0.98891 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=2.004 | A=5.697: v=0.93683 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=2.051 | A=5.000: v=0.94456 (1-v)L^2<=A g0^2:True max_sigma||Proj U||=2.041
[T1iii] n=0: L=4 W=32 lam=1.562e-02 Im mS=0.8325 Im zS=0.3675 t0=0.6937 BAdom: kappa=1/2<=Im m:True, N^(-1+eps)<=Im z:True, Im z<=1:True; Bandwidth N^(1/6)<=W:True; WO W^(-3/2+1/10)<=lam<=10:True
        eps1=0.1: threshold W^eps1*ell=1.414 (ell_v(lam)=1.000); #a with zdistInf(a-c1)>=thr: 37 of 64; max|K|=9.932e-05; max|K| on cut region=3.354e-08 <= W^-D (D=2.0): True; effective D=-log max/log W=4.97
[T1iii] n=1: L=8 W=1024 lam=2.441e-04 Im mS=0.8333 Im zS=0.3667 t0=0.6944 BAdom: kappa=1/2<=Im m:True, N^(-1+eps)<=Im z:True, Im z<=1:True; Bandwidth N^(1/6)<=W:True; WO W^(-3/2+1/10)<=lam<=10:True
        eps1=0.1: threshold W^eps1*ell=2.000 (ell_v(lam)=1.000); #a with zdistInf(a-c1)>=thr: 485 of 512; max|K|=3.048e-09; max|K| on cut region=1.262e-16 <= W^-D (D=2.0): True; effective D=-log max/log W=5.28
[T1iii] n=2: L=12 W=7776 lam=2.143e-05 Im mS=0.8333 Im zS=0.3667 t0=0.6944 BAdom: kappa=1/2<=Im m:True, N^(-1+eps)<=Im z:True, Im z<=1:True; Bandwidth N^(1/6)<=W:True; WO W^(-3/2+1/10)<=lam<=10:True
        eps1=0.1: threshold W^eps1*ell=2.449 (ell_v(lam)=1.000); #a with zdistInf(a-c1)>=thr: 1603 of 1728; max|K|=6.961e-12; max|K| on cut region=3.966e-26 <= W^-D (D=2.0): True; effective D=-log max/log W=6.53
[T11] Cd=1.0: c_d=min(1/100,1/(30Cd))=0.01; c_d*Cd=0.0100 <= 1/30=0.0333; 1/5-c_d*Cd=0.1900 >= 1/6=0.1667 (slack 0.0233)
      s=0.5 t=0.51: (1-t)/(1-s)=0.9800<1; smallest n0 with Bctl_n(t)^c_d <= ratio: n0=0 (L=4, W=32); t<=2/3<=t0(t0_sz0)
      s=0.5 t=0.55: (1-t)/(1-s)=0.9000<1; smallest n0 with Bctl_n(t)^c_d <= ratio: n0=1 (L=8, W=1024); t<=2/3<=t0(t0_sz0)
      s=0.5 t=0.6666666666666666: (1-t)/(1-s)=0.6667<1; smallest n0 with Bctl_n(t)^c_d <= ratio: n0=8 (L=36, W=1889568); t<=2/3<=t0(t0_sz0)
      Dw>=1/c+d+1=10 (N<=W^(1/c), Bctl>=W^-d/(1+dd^-2)); D'=D+1/c+1: D=2 -> 9
      check N<=W^(1/c) at n=3: True; Bctl>=W^-d/(1+dd^-2): True
      n=0: 1-t0=0.3063 >= Im z/2=0.1838: True; t0>=kappa/(kappa+1)=1/3: True; g(lam)^2/g0^2=1/t0=1.441 <= (kappa+1)/kappa=3: True
      n=1: 1-t0=0.3056 >= Im z/2=0.1833: True; t0>=kappa/(kappa+1)=1/3: True; g(lam)^2/g0^2=1/t0=1.440 <= (kappa+1)/kappa=3: True
      n=2: 1-t0=0.3056 >= Im z/2=0.1833: True; t0>=kappa/(kappa+1)=1/3: True; g(lam)^2/g0^2=1/t0=1.440 <= (kappa+1)/kappa=3: True
[W0] kappa=0.5 Lam=1/dd=10: r=0.00416, c3=r/2=0.00208; c3*W^eps1 >= D*ln W first holds at ln W=116.2 (the larger root; the smaller root is below ln W=1), W0~1e50
[lim] Bctl_n(0.55)*(2(n+1))^15 for n=1,10,100,1000: [2.2266, 2.2222, 2.2222, 2.2222] ; Bctl_n^c_d at n=1000: 0.3223 <= (1-t)/(1-s)=0.9
```
### Verdicts
- **T.10 (a) `baTwKerA_holds`: PASS.** `(1-v)/(1-u)` from `‖Q‖ ≤ 1`, `‖Θ‖ ≤ (1-u)⁻¹`; instance ratio 1.0000.
- **T.10 (b) `baTwKerFar_holds`: PASS.** Ball lemma at `Λ' = W^ε`, `R = W^ε ℓ_v` (hypotheses hold: `1 ≤ R`, regime `u ≤ 1-g²/L²`), far part `W^{-D}(W-1)`; `C₁` independent of `W, ε, D, g, L`.
- **T.10 (d) `baTwKerZero_holds`: PASS.** The merged lemma is at `A = 1` only; the pin needs the `A`-form of `EKNonzero_coef`, proof otherwise unchanged (`C(A) = 2 + A C₀′E_k`). Not derivable from the `A=1` lemma by rescaling (the kernel depends on `g`).
- **T.1(iii) `baTwKDecay_holds`: PASS** with `C`-free statement `|K̃| ≤ W^{-D}` eventually, uniform in `v ∈ [0,t₀]`, `σ, a, c₁, c₂`; inputs `twK_ba`, `baProp5_holds`, `BAMB_decay_large` (needs `g₀ ≤ 𝔡⁻¹`, `BAflow_lam0_window`), `BAMB_row_l1`. The route threshold `W₀` is large (`ln W₀ ≈ 116`), which affects only the `∀ᶠ n` conclusion; the compiled instance needs a nonempty cut region (any n) and an `∃ a c₁` form.
- **T.11 (i), (ii), (iv), (v) `baTwistSrcN_holds`, N = 1, 2, 4, 5: PASS** for every regime `R` (no use of `R`). Exponents close with slack 0, 0, `1/30-𝔠dCd`, factor `W^εℓ`. Points for 1b: (iv)'s deterministic hypothesis on `Z` needs `Ξ` chosen as in the last table row (resolvent bound `‖G_u‖ ≤ η_u⁻¹`); (iv) uses the `(1-t)⁻¹` form of the `(4.16)` core, not `etaT(E)`; (v) for `twEE` may need the Cauchy–Schwarz conjunct of `BATwistSrc3` (a stem copy).
- No pin is false; no input outside TP and merged files is needed (the `EKPins`/`EKNonzero` lemmas are used as stated, with `private` removed or copied).

## (a″) Probe compile — Sun Oct 11 22:54:04 UTC 2026 (stage 1a probe step, `prover-max`, claude-sonnet-5-5)

Probe `RBM3D/Probe/T2429Pins.lean` (limit 400 lines), worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2429`, branch `t/T2429` from `main` `0a8176c`; never merged, no root import. Scripts: `<scratchpad>/T2429/` (not in the repository).
**Result.** `lake env lean RBM3D/Probe/T2429Pins.lean` exits 0 (run below). The T.1 (iii) pin text is fixed (probe lines 54-59) and its instance is nonempty. The keyword list is fixed (9 deletions, under (iv)). The prediction (vi) says that `TwistKer2.lean` exceeds 1,800 lines at the ticket's literal boundary (central 2,249; 1,584 with the deterministic helpers moved to `TwistKer.lean`).
```
$ git status --short | wc -l; git rev-parse --short HEAD; git log --format=%h main..t/T2429; wc -l RBM3D/Probe/T2429Pins.lean; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2429Pins.lean; git diff --stat main...t/T2429; git merge-base main t/T2429 | cut -c1-7
0
e1edb72
e1edb72 d24d701 f81c0c7
119 RBM3D/Probe/T2429Pins.lean
0
 RBM3D/Probe/T2429Pins.lean | 119 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 119 insertions(+)
0a8176c
$ date -u; lake env lean RBM3D/Probe/T2429Pins.lean > out.txt 2>&1; echo exit=$?; date -u      # 37 output lines, no warning, no error
Sun Oct 11 22:47:35 UTC 2026
exit=0
Sun Oct 11 22:47:41 UTC 2026
$ awk '/^[@A-Za-z'"'"']/ {if (l) print l; l=$0; next} {sub(/^ +/," "); l = l $0} END {print l}' out.txt      # continuation lines joined, nothing else changed
@twK_ba : ∀ {d : ℕ} {sz : Sizes d} (z : ℕ → ℂ) (n : ℕ), 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im → ∀ (t : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)), twK (baFMz sz z) n t σ a c₁ c₂ = (↑(sz.W n) ^ d)⁻¹ * ∑ a', BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t (σ 0) (σ 1) a a' * BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (↑(BAflowEs sz z n)) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' * BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (↑(BAflowEs sz z n)) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁
baProp5_holds : ∀ (d : ℕ) (Λ κ : ℝ), BAProp5 d Λ κ
BAMB_decay_large : ∀ (d L : ℕ) [inst : NeZero L], 3 ≤ L → 0 < d → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ → BAReal d L g κ E m → ∀ (a b : Zd d L), ‖BAMB d L g (↑E) m a b‖ ≤ (BAct_rate d Λ κ)⁻¹ * Real.exp (-BAct_rate d Λ κ * ↑(zdistD d L (a - b)))
@BAflow_lam0_window : ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ (n : ℕ) in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹
EMn2BA_ellT_mono_g : ∀ (L : ℕ) {g₀ g : ℝ}, g₀ ≤ g → ∀ (t : ℝ), ellT L g₀ t ≤ ellT L g t
@EMn2BA_one_sub_T0 : ∀ {d : ℕ} {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → ∀ (sz : Sizes d) {z : ℕ → ℂ}, BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ), (z n).im / 2 ≤ 1 - BAflowT0 sz z n
baComp_holds : ∀ (d : ℕ) (Λ κ : ℝ), BACompBound d Λ κ
zdistInf_le_zdistD : ∀ (d L : ℕ) (x : Zd d L), zdistInf d L x ≤ zdistD d L x
FlowPinsInst.flow_sz0 : BAFlow SizesInst.sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) FlowPinsInst.zSeq
FlowPinsInst.half_lt_t0 : ∀ (n : ℕ), 1 / 2 < BAflowT0 SizesInst.sz0 FlowPinsInst.zSeq n
'RBM.BA.BATwKDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
$ awk '/^def BATwKDecay/,/^$/' RBM3D/Probe/T2429Pins.lean      # the pin as written (lines 54-59)
def BATwKDecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ ε₁ D : ℝ, 0 < ε₁ → 0 < D →
      ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ BAflowT0 sz z n → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
        ((sz.W n : ℕ) : ℝ) ^ ε₁ * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) →
        ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)
$ awk '/^open RBM.BA.FlowPinsInst/{p=1} p{print} /:= by$/{if(p) exit}' RBM3D/Probe/T2429Pins.lean      # the instance, statement (lines 68-72; proof 73-115)
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst in
example (h : BATwKDecay 3) : ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ 1 / 2 → ∃ a c₁ : Zd 3 (sz0.L n),
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L n) (sz0.lam n) v ≤ (zdistInf 3 (sz0.L n) (a - c₁) : ℝ) ∧
    ∀ (σ : Fin 2 → Bool) (c₂ : Zd 3 (sz0.L n)),
      ‖twK (baFMz sz0 zSeq) n v σ a c₁ c₂‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (-2 : ℝ) := by
```
Pin and instance (facts from the file and the output above):
- **Shape.** Prefix of `twK_bound` (`TwistPins:122-124`), then `∀ ε₁ D > 0, ∀ᶠ n, ∀ v ∈ [0, BAflowT0 n], ∀ σ a c₁ c₂`, cut `W_n^{ε₁} ℓ_v(lam_n) ≤ zdistInf (a - c₁)`, bound `‖K̃‖ ≤ W_n^{-D}`; no `∃ C`. Cut and bound are those of `twDec` (`TwistPins:253-257`) without the factor 3 (T.11 (v) applies the pin at `X = W^ε ℓ_v`).
- **F1.** The kernels of `twK` are at `g₀ = BAflowLam0 = √t₀ · lam ≤ lam` (`FlowPins:386`; the inequality is proved at `EMn2BA.lean:693-699`), and `ellT` is nondecreasing in `g` (`EMn2BA_ellT_mono_g`, `EMn2BA.lean:591`): the hypothesis at `ℓ_v(lam)` implies it at `ℓ_v(g₀)`, no ε loss; the reverse step is not used.
- **Instance.** `h : BATwKDecay 3` is a hypothesis of the example (it is the target of 1b; in `TwistKer.lean` the example applies `baTwKDecay_holds 3`). At `sz0`, `zSeq`, `flow_sz0`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, `ε₁ = 1/10`, `D = 2`, every deterministic hypothesis is discharged. For every `n` and `v ∈ [0, 1/2]` (`half_lt_t0`) the pair `a = (2(n+1), 0, 0)`, `c₁ = 0` is in the cut-off region (proved in the example: `zdistInf ≥ 2(n+1)`, `ℓ_v(lam_n) ≤ 1`, `W_n^{1/10} ≤ 2(n+1)`), so the pin is applied to a nonempty set for large `n`, every `σ`, every `c₂`.
- **Twins on `main` not named by the ticket.** `baComp_holds` (`EMn2BA:472`: the two-case split `|a - c| ≥ |a - b|/2` or `|c - b| ≥ |a - b|/2` for `Θ M^{(σσ')}`, with `baProp5_holds` and `BAMB_decay_large`) and `baEMn2ExpHK` (`EMn2BA:637`: its eventual absorption at the carrier, `1 - t₀ ≥ Im z/2` by `EMn2BA_one_sub_T0`); T.1 (iii) is the same split with `M(c₂, a') M(a', c₁)` in place of `M^{(σσ')}(c, b)`.

### (iv) keyword list, name clashes, cone (`main` `0a8176c`)
```
$ for f in EKPins EKNonzero; do printf "%s.lean: " $f; awk '/^private (theorem|def) /{print FNR, $3}' RBM3D/BA/$f.lean | paste -sd' ' -; done      # (files as on main 0a8176c)
EKPins.lean: 151 EKPins_norm_Q_le 161 EKPins_norm_Theta_le 185 EKPins_norm_uKer_le 276 EKPins_Mss_shift 289 EKPins_Theta_shift 308 EKPins_Theta_apply 314 EKPins_Xi_eq 331 EKPins_theta_absorb 367 EKPins_Xi_entry_le 452 EKPins_sum_ball_le
EKNonzero.lean: 50 EKNonzero_E 53 EKNonzero_E_pos 60 EKNonzero_row_sum 70 EKNonzero_col_sum 84 EKNonzero_projMat_mul_apply 92 EKNonzero_mul_projMat_apply 102 EKNonzero_projMat_comm 110 EKNonzero_Mss_shift 123 EKNonzero_projMat_mul_Theta 143 EKNonzero_Theta0_shift 149 EKNonzero_norm_Q_le 168 EKNonzero_coef 191 EKNonzero_norm_projMat_mul_uKer_le
$ sed -n 196,252p RBM3D/BA/EKNonzero.lean | grep -o "EKNonzero_[A-Za-z0-9_]*" | sort | uniq -c | awk '{printf "%s x%s  ", $2, $1}'      # the body the A-form copies
EKNonzero_coef x1  EKNonzero_E x10  EKNonzero_E_pos x1  EKNonzero_Mss_shift x1  EKNonzero_norm_Q_le x1  EKNonzero_projMat_comm x1  EKNonzero_projMat_mul_Theta x1  EKNonzero_Theta0_shift x1  
$ sed -n 191,252p RBM3D/BA/EKNonzero.lean | grep -n "hsg\|hcoef"   (line numbers relative to 191)
3:    (hsg : 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s) (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bo
28:  have hcoef := EKNonzero_coef hg hL hsg hst ht
58:          mul_le_mul_of_nonneg_left hcoef (by positivity)
$ sed -n 196,252p RBM3D/BA/EKNonzero.lean | grep -o "norm_le_sum_row_zero\|sum_radial_pow_le\|norm_projMat_le\|BAuKer_eq_one_add" | sort -u   (public names the body needs)
BAuKer_eq_one_add norm_le_sum_row_zero norm_projMat_le sum_radial_pow_le
$ grep -rcw NAME RBM3D RBM3D.lean   (git-archive snapshot of main; NAME file:count, files with a hit)
EKPins_norm_Q_le EKPins:4 EKNonzero:1 | EKPins_norm_Theta_le EKPins:2 | EKPins_norm_uKer_le EKPins:2 TwistPins:1 | EKNonzero_E EKNonzero:14 | EKNonzero_E_pos EKNonzero:3 | EKNonzero_projMat_comm EKNonzero:2 | EKNonzero_Mss_shift EKNonzero:2 | EKNonzero_projMat_mul_Theta EKNonzero:2 | EKNonzero_Theta0_shift EKNonzero:2 | EKNonzero_norm_projMat_mul_uKer_le EKNonzero:2 TwistPins:1 | EKNonzero_norm_Q_le EKNonzero:2 | EKNonzero_coef EKNonzero:2 | 
$ python3 -I cone.py <snapshot of main> RBM3D.BA.EKPins RBM3D.BA.EKNonzero
RBM3D.BA.EKPins: transitive reverse cone 6: ['RBM3D', 'RBM3D.BA.EKNonzero', 'RBM3D.BA.EKSum', 'RBM3D.BA.NewKLKBA', 'RBM3D.BA.TwistPins', 'RBM3D.Chain.Step2Kern']
RBM3D.BA.EKNonzero: transitive reverse cone 1: ['RBM3D']
$ git grep -c 'baTwKerA_holds|baTwKerFar_holds|baTwKerZero_holds|BATwKDecay|baTwKDecay_holds|baTwistSrc[0-9N]_holds|TwistKer_|TwistKer2_|TwistKer2' <main | each t/* branch> -- RBM3D RBM3D.lean | wc -l
Sun Oct 11 22:48:12 UTC 2026
main: files with a hit =        0; other t/* branches scanned = 427, files with a hit = 0
branches t/T2430, t/T2431 existing: 0
```
Fixed list for 1b: **9 deletions of `private `**, nothing else changes in either file.
- `BA/EKPins.lean`: :151 `EKPins_norm_Q_le`, :161 `EKPins_norm_Theta_le`, :185 `EKPins_norm_uKer_le` (T.10 (a) `‖BAuKer‖ ≤ (1-v)/(1-u)`; (b) far part `‖Ξ‖ ≤ (u-v) ‖Q‖ ‖Θ‖ ≤ (u-v)/(1-u)`; (d) `‖Q‖ ≤ 1`).
- `BA/EKNonzero.lean`: :50 `EKNonzero_E`, :53 `EKNonzero_E_pos`, :102 `EKNonzero_projMat_comm`, :110 `EKNonzero_Mss_shift`, :123 `EKNonzero_projMat_mul_Theta`, :143 `EKNonzero_Theta0_shift` (the body of the `A`-form).
- The ticket's expected EKNonzero list (:50, :53, :102) is incomplete: the scan above shows that lines 196-252 of `EKNonzero_norm_projMat_mul_uKer_le`, which the `A`-form copies, name also :110, :123, :143, `EKNonzero_norm_Q_le` (:149) and `EKNonzero_coef` (:168). In that body `hsg` occurs only in the line `hcoef := EKNonzero_coef hg hL hsg hst ht` (file line 218), so the `A`-form is the same body with `hcoef : (t - s) * ((g² + |1-t|)⁻¹ * L²) ≤ A` (from `(1 - s) L² ≤ A g²`, `t - s ≤ 1 - s`, `(g² + |1-t|)⁻¹ ≤ g⁻²`) and conclusion `2 + A * C₀ * EKNonzero_E k`. No deletion for :149 (same statement as `EKPins_norm_Q_le`, which becomes public) or :168 (replaced). :191 is not applied by the `A`-form (a new lemma in `TwistKer.lean`; for `A > 1` its `hsg` fails and the kernel depends on `g`, so a rescaling of `g` does not reduce to it): its `private` stays; the ticket's permission to delete it is not used unless 1b applies it and lists it in (b).
- Name clashes: none outside the two files; the hits in `TwistPins.lean` (:192, :206) and `EKNonzero.lean` (:148) are docstring mentions (`grep -nw`, checked). Reverse cone on `main`: `EKPins` has 5 importers (`EKNonzero`, `EKSum`, `NewKLKBA`, `TwistPins`, `Step2Kern`) plus the root, `EKNonzero` the root only; no `Graph/LWExpCert*` module is in either. T2423, T2427, T2428, T2430, T2431 do not list `EKPins` or `EKNonzero` in their sole writable files (`grep -n "Sole writable files"` of the five tickets).
- New public names `baTwKerA_holds`, `baTwKerFar_holds`, `baTwKerZero_holds`, `BATwKDecay`, `baTwKDecay_holds`, `baTwistSrc{1,2,4,5}_holds` and the stems `TwistKer_`, `TwistKer2_`: no hit (last command); `t/T2430`, `t/T2431` do not exist yet, so they are not scanned.

### (v) inputs of T.1 (iii) and of the T.11 items (file:line on `main`; script `inputs.sh`: grep of the declaration line, grouped by file)
```
# T.1 (iii)
BA/TwistPins.lean: 279 twK_ba 253 twDec 692 twK_bound_holds
BA/Prop6Path.lean: 850 baProp5_holds
BA/CombesThomas.lean: 509 BAMB_decay_large
BA/GreenSchur.lean: 59 BAflow_real 72 BAflow_lam0_window 139 BAMB_row_l1
BA/EMn2BA.lean: 111 EMn2BA_one_sub_T0 125 EMn2BA_mF_data 472 baComp_holds 591 EMn2BA_ellT_mono_g 637 baEMn2ExpHK
Defs/Sizes.lean: 117 zdistInf_le_zdistD
# T.11
BA/TwistPins.lean: 146 BATwFrame 133 twSteps 70 twL2' 224 twL3 230 twB1 232 twB2 234 twEG 240 twDer 244 twEE 352 twFold_holds 412 twWard_holds
Chain/Step2Gen.lean: 491 STAvgUgL 503 STGdecayWgL 514 STStep2ConclgL
BA/KInduct.lean: 77 baKsol_one
Induction/Contract.lean: 1011 STContractM 1069 stContractM_holds
Induction/KDecay.lean: 1262 stSumTwoLoop 1339 stSumTwoLoop_exists
Induction/SEforLn2.lean: 269 SEforLn2_of_subset 282 SEforLn2_Bctl_ge_inv 307 SEforLn2_WD 330 SEforLn2_det_of_prec 352 SEforLn2_conU 380 SEforLn2_sumTwo_pt 443 SEforLn2_sum2
Loop/GLoop.lean: 75 etaT
Green/MinorDiff.lean: 978 mE_zero
```
| item | inputs (file:line above) | to write in 1b |
|---|---|---|
| (i) `twB1` | `twSteps` conj 3 (`TwistPins:137-138`, `k = 2`, uniform on `TimeIcc`); `twK_bound_holds` (:692, `Σ_a ‖K̃‖ ≤ C (W^d η)⁻¹`) | `‖twB1‖ ≤ W^d (Σ_b ‖K̃_b‖) max_b ‖(L-K)_{(a,b)}‖`; `≺` transfer of the `max_b` (stem copy of `SEforLn2_of_subset` :269) |
| (ii) `twEG` | `STAvgUgL` (`Step2Gen:491`, middle conjunct of `STStep2ConclgL` :514 = `twSteps` conj 1, `TwistPins:134`) with `baKsol_one` (`KInduct:77`, `K^{(1)} = m(σ)`); `twSteps` conj 2 (:135-136, `k = 1, 3`); `twFold_holds` (:352), `twWard_holds` (:412), `twL3` (:224); `stContractM_holds` (`Contract:1069`, pin `STContractM` :1011: `Σ_x ‖L^{(m)}_{(σ, a ++ [x])}‖ ≤ (W^d Im z)⁻¹ (max L^{(2k-1)} max L^{(2m-2k-1)})^{1/2}`) | T.4 at `n = 3`: fold at the twist (`twFold_holds`), `twSq` read as `loopFine` 2- and 4-loops (private twin `Green/Pins:377-437`), Ward and Cauchy-Schwarz through `STContractM` |
| (iv) `twB2` | `stSumTwoLoop_exists` (`KDecay:1339`; `stSumTwoLoop` :1262); `STGdecayWgL` (`Step2Gen:503`); `sz.STConStInd 𝔠d s t` in `BATwFrame` (`TwistPins:150`); `Im m_F ≤ 1` (`EMn2BA_mF_data` :125), `η = (1-t) Im m_F` (`TwistPins:729`, `rfl`) | `(4.16)` at the carrier: stem copies of `SEforLn2_{of_subset 269, Bctl_ge_inv 282, WD 307, det_of_prec 330, conU 352, sumTwo_pt 380, sum2 443}` with `C.eta` for `etaT E u`; `(1-t)⁻¹ ≤ η⁻¹` as `Im m_F ≤ 1`; `etaT 0 t = 1 - t` needs `mE 0 = I` (private in `Green/MinorDiff:978`, short stem copy) |
| (v) | `BATwKDecay` (this probe, `TwistKer.lean`) for `K̃`; `twSteps` conj 4 (`TwistPins:139-142`, all `k`); `twFold_holds` (:352); `twDer` (:240), `twEE` (:244), `twDec` (:253) | triangle inequality for `zdistInf` (on `main` only `zdistInf_le_zdistD`, `Sizes:117`) and the split `3X ≤ |a-c₁| ⟹ X ≤ |b-c₁| ∨ 2X ≤ |a-b|`; folds of `twL3` and of the `twDer` products into loops with two indices at distance `≥ X`; deterministic `N^C` bounds |

### (vi) predicted lines per file against the stop line 2,000 (flag 1,800)
```
$ python3 -I lines.py <worktree>   # columns low / central / high; comparables = line counts of the cited ranges; new lemmas x 1.0/1.3/1.8 (the multipliers of T2418-prove.md (a')(iv)), copies x 1.0/1.0/1.1, one summation x 0.7/1.0/1.5; F = fixed estimate, no landed twin
item                                                                       cmp    low   cent   high
K0 header+imports+docstring (copy)                                          42     42     42     42
K1 T.10(a) wrapper (twin baEKSumNdecay_holds)                               13     13     17     23
K2 T.10(b) near/far split (twin EKSum_UN_anchor_bound)                      73     73     95    131
K3a T.10(d) A-form body (copy of EKNonzero_coef + main lemma)               87     87     87     96
K3b T.10(d) wrapper (twin baEKSumDecayNonzero_holds)                        43     30     43     64
K4a T.1(iii) case split (twin baComp_holds)                                122     85    122    183
K4b T.1(iii) eventual absorption (twin baEMn2ExpHK)                        104     73    104    156
K5a instances target 1 (twin TwistPins 926-953)                             28     28     36     50
K5b instance target 2 (twin: this probe, lines 63-115)                      53     53     69     95
K5c (d) with A>1 window, F                                                   0     30     40     55
D1 twSq/twLoopX = loopFine 2-,4-loops (3 x twin trace_pm..loopFine_pm_formula)   183    183    238    329
D2 T.4 n=3: fold + Ward + CS sum (twin SEforLn2 538-663)                   126    126    164    227
D3 (4.16) deterministic: stem copies SEforLn2 267-529                      263    263    263    289
P0 header (copy)                                                            42     42     42     42
P1 frame instance + 4 examples (twin TwistPins 759-790)                     32     32     42     58
P2 T.11(i) PrecL glue, F                                                     0    100    140    210
P3 T.11(ii) PrecL glue, F                                                    0     80    120    180
P4 T.11(iv) PrecL glue, F                                                    0    100    150    220
P5 T.11(v) five decays, F                                                    0    700   1000   1500
P6 deterministic N^C bounds, F                                               0     60     90    140

literal boundary: TwistKer.lean (K)                                               514    655    895   vs 1800/2000: <=1800 | <=1800 | <=1800
literal boundary: TwistKer2.lean (P + D)                                         1686   2249   3195   vs 1800/2000: <=1800 | >2000 | >2000
D moved to TwistKer.lean: TwistKer.lean (K + D)                                  1086   1320   1740   vs 1800/2000: <=1800 | <=1800 | <=1800
D moved to TwistKer.lean: TwistKer2.lean (P)                                     1114   1584   2350   vs 1800/2000: <=1800 | <=1800 | >2000
both files                                                                       2200   2904   4090   vs 1800/2000: >2000 | >2000 | >2000
```
Reading of the table (a prediction, not a measurement: the comparable line counts are measured, the multipliers and the F rows are estimates):
- **Literal boundary of the ticket** (`T.4`, `T.5`, `(4.16)` helpers in `TwistKer2`): `TwistKer.lean` 514 / 655 / 895 (low / central / high); `TwistKer2.lean` 1,686 / 2,249 / 3,195, **above 1,800 at the central column and above the 2,000 stop line at central and high: this step says so** (ticket :5).
- D1-D3 are deterministic (no `PrecL`). Under the ticket's rule (boundary = deterministic vs `PrecL`; 1b may move helpers across it keeping `TwistKer → TwistKer2`) they go to `TwistKer.lean`: 1,086 / 1,320 / 1,740, and `TwistKer2.lean` 1,114 / 1,584 / 2,350 (high column above 2,000). The largest uncertainty is row P5 (T.11 (v), no landed twin).
- Both files: 2,200 / 2,904 / 4,090, against the ticket's estimate 1,082 / 1,478 / 2,571 and its expectation 2,200-3,100 (ticket :5).
- Suggestion: start with the moved boundary; if `TwistKer2.lean` passes about 1,500 lines before (v) is written, a third file for T.11 (v) is named by amend (dispatcher).

### Paper-delta candidates (tag `T2429a`) and stop rule
- T2429a-1 (T.1 (iii)): the paper's `W ≥ W₀(ε, D)` (TP:38) is `∀ᶠ n in atTop` along a flow, as T2421a for `twK_bound`; the cut `|a - c₁| ≥ W^{ε₁} ℓ_u` is stated in `zdistInf` at `ellT (sz.L n) (sz.lam n) v` (the model coupling, while the kernels sit at `g₀ ≤ lam`: F1 of `T2413-design.md`), uniformly in `v ∈ [0, BAflowT0 n]`.
- Stop rule (ticket :17): no obstruction at the probe step. The T.1 (iii) pin compiles and its instance is nonempty; every input of T.1 (iii) and of the T.11 items is merged or a prescribed stem copy (tables (iv), (v)).
## (b) Script output (stage 1b, `prover-hard`, claude-sonnet-5-5) — Mon Oct 12 00:17 UTC 2026 (`date -u`)
Branch `t/T2429`, HEAD `1f23fe8` (base `0a8176c`). Sections (a), (a″), (iv)-(vi) above occupy 215 lines (`wc -l` before this section).
```
$ wc -l RBM3D/BA/TwistKer.lean RBM3D/BA/TwistKer2.lean; git show <c>:<file> | wc -l     # stop line 2,000 (flag 1,800)
HEAD: 1599 / 1442 (total 3041; (a″)(vi) central 2,904). Commits fad2ded..671c0cc (TwistKer, TwistKer2): (633,-) (633,510) (1234,644) (1591,644) (1591,1271) (1599,1322) (1599,1443)
$ lake build RBM3D.BA.EKPins RBM3D.BA.EKNonzero RBM3D.BA.TwistKer RBM3D.BA.TwistKer2 | tail -1  # 00:10:09 UTC: Build completed successfully (4012 jobs).
$ lake build | tail -1   # 00:10:00 UTC, HEAD 1f23fe8 (the root does not import the two new modules: hub step): Build completed successfully (4242 jobs).
$ lake env lean PreCheck.lean   # import RBM3D, RBM3D.BA.TwistKer, RBM3D.BA.TwistKer2, #assert_rbm_axioms; 00:11 UTC
exit=0   axiom audit: 12247 theorems, 3794 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean docs/tickets/checks/T2429-check.lean -> exit=0, 181 output lines, 0 `error`;  Chk2.lean (the 7 target shapes of the check file's section 2 and `∀ d, BATwKDecay d` as terms; `baTwistSrc1_holds 3 STCaseI`, `baTwistSrc5_holds 3 STCaseII`) -> exit=0, no output
$ #print axioms of the 19 new public declarations, EKPins_norm_uKer_le, EKNonzero_E_pos: 21 of 21 lines `[propext, Classical.choice, Quot.sound]`; grep -cE "sorry|admit|native_decide|^axiom" on both files: no match
$ git diff -U0 main...t/T2429 -- RBM3D/BA/EKPins.lean RBM3D/BA/EKNonzero.lean | awk   # removed lines, file:line name
EKPins 151 EKPins_norm_Q_le, 161 EKPins_norm_Theta_le, 185 EKPins_norm_uKer_le;  EKNonzero 50 EKNonzero_E, 53 EKNonzero_E_pos, 102 EKNonzero_projMat_comm, 110 EKNonzero_Mss_shift, 123 EKNonzero_projMat_mul_Theta, 143 EKNonzero_Theta0_shift
9 pairs: each `+` line is its `-` line without `private ` (diff exit 0); `git diff --stat main...t/T2429`: EKNonzero 12 +-, EKPins 6 +-, TwistKer 1599, TwistKer2 1442, Probe/T2429Pins 119 (not merged)
$ grep -n "^theorem baTw" RBM3D/BA/TwistKer.lean RBM3D/BA/TwistKer2.lean     # the targets as written
TwistKer.lean:78 baTwKerA_holds, :86 baTwKerFar_holds, :256 baTwKerZero_holds (all `(d : ℕ) (Λ κ : ℝ) : BATwKerX d Λ κ`); :455 `baTwKDecay_holds (d : ℕ) : BATwKDecay d` (def `BATwKDecay` :447-452: `diff` of its text against the probe's, exit 0; the text is printed in (a″))
TwistKer2.lean:168, 589, 422, 1364 baTwistSrc{1,2,4,5}_holds `(d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc{1,2,4,5} d R`
$ grep -n "^example" RBM3D/BA/TwistKer.lean RBM3D/BA/TwistKer2.lean     # the compiled instances
TwistKer.lean:542 (T.10 (a)) 548 (b) 564 (d, A = 2) 576 (d, A = (κ+1)/κ) 589 (T.1 (iii));  TwistKer2.lean:1393 (i) 1396 (ii) 1400 (iv) 1431 (v)
$ git grep -nwE "<the 19 new names>|TwistKer2?_[A-Za-z0-9_']*" main -- RBM3D RBM3D.lean | wc -l ; git grep -l ... over the 428 other t/* branches     # main hits=0; other t/* branches with a hit=0
```
Instances. Targets 1: flow point `Pf` of `FlowPt 4 (1/2)`, `κ = Im Pf.m0`, `Λ = 1`: (a) `v = 0 < u = 1/2`, `A = δ₀ ≠ 0`; (b) `W = 16, ε = 1/2, D = 2`, `c₁ = 0`, `A = δ₀`; (d) `A = 2` at `v = 1 - g₀²/8 < u = 1 - g₀²/16` (`(1-v)L² = 2g₀²`; the example also proves `¬ ((1-v)L² ≤ 1·g₀²)`, the regime of the merged `A = 1` lemma) and `A = (κ+1)/κ`. Target 2: `sz0, zSeq, flow_sz0`, `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`, `ε₁ = 1/10`, `D = 2`, every `v ∈ [0,1/2]`, `a = (2(n+1),0,0)`, `c₁ = 0` in the cut for every `n`. Targets 3: `TwistKer2_frame_inst` (stem copy of the private `TwistPins_frame_inst`, `TwistKer2.lean:1382`) discharges every deterministic hypothesis of `BATwFrame` at `sz0`, `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0`, `STAny`, `STConStInd`; `twSteps` (other gates' pins) and `0 < Cd` stay hypotheses. The (iv) example also discharges its a priori hypothesis: for every `γ ∈ [1,2]`, `Ξ_n = 32 N_n⁴ ≥ 1` has `‖Z_v‖ ≤ Ξ B^γ` for all `n, ω, σ, a, c₁, c₂`, `v ∈ [1/2,2/3]` (`TwistKer2_Z_crude`, `_eta_inv_le`, `_Bctl_rpow_ge`).
T.11 input table (definition `file:line` on `main`; use sites in `TwistKer2.lean`). (i): `twSteps` conj 3, `k = 2` (TwistPins:137), `twK_bound_holds` (TwistPins:692) — :174; :159 (`TwistKer2_twK_unif` :154, uniform in `v` by `TwistKer2_unif` :90). (ii): `STAvgUgL` (Step2Gen:491), conj 2 `k = 1, 3` (TwistPins:135), `baKsol_one` (KInduct:77), `TwistKer_twEG_le` (TwistKer:1193) — :594; :595-596; :577; :630. (iv): `STGdecayWgL` (Step2Gen:503), `KDecay_sum_tailT_le`, `KDecay_tailC` (KDecay:1241, 1119), stem copies of `SEforLn2_{Bctl_ge_inv, WD, conU, sumTwo_pt, sum2}` (SEforLn2:282, 307, 352, 380, 443) — :437; :338, :314; :234, 259, 281, 308, 350. (v): conj 4 `k = 2` (TwistPins:139), `baTwKDecay_holds` (TwistKer:455), `TwistKer_entry_decay`, `_twEG_decay`, `_twEE_decay` (TwistKer:1555, 1390, 1486) — engine :777, used at :881, 931, 989, 1063, 1161; `baTwKDecay_holds` :884, 1066, 1164; `_entry_decay` :869, `_twEG_decay` :966, `_twEE_decay` :1017.
F1: the forward comparison `EMn2BA_ellT_mono_g` (`ℓ_v(g₀) ≤ ℓ_v(lam)`, no `ε` loss) is used once (`TwistKer.lean:489`); the reverse step `ℓ_v(g) ≤ √((κ+1)/κ) ℓ_v(g₀)` is not used; the cuts of (v) and of `twSteps` conj 4 are at `ellT (sz.L n) (sz.lam n)`; the kernel pins stay at the kernel's own `g`. Ports: no text from `../RBM1D`, `../RBM2D`. Stem copies of `main` files (RBM3D, base `0a8176c`): `Induction/Contract.lean:225-294`, `Green/Pins.lean:346-437`, `BA/EKNonzero.lean:168,191`, `BA/TwistPins.lean:517,526,766`, `BA/GreenLocal.lean:178`, `Universality/EMCTE2.lean:144`, `Induction/SEforLn2.lean` (above), `Defs/StochDomAt.lean:355`, `Defs/StochDom.lean:49`; twins `BA/EMn2BA.lean:472,637,661`.
Narrative. (1) T.10 (a), (b) from the now public `EKPins_norm_{uKer,Q,Theta}_le` and `baEKXiBall_holds` (ball at `Λ' = W^ε`, `R = W^ε ℓ_v`; far part `‖Ξ‖ ≤ (u-v)/(1-u) ≤ W`); (d) is the `A`-form of the body of `EKNonzero_norm_projMat_mul_uKer_le` (`C(A) = 2 + A C₀ E_k`; that lemma stays `private`, not applied; the 9 deletions are the list of (a″)(iv)). (2) T.1 (iii): the case split of `baComp_holds` and `W^{D+1/𝔠} ≲ e^{cW^{ε₁}/2}` (`isLittleO_rpow_exp_pos_mul_atTop`). (3) The deterministic core of T.2, T.4 (`n = 3`), T.5 is `TwistKer.lean` section 5 (fine-lattice `E_a`, trace sandwich, `loopFine` as a fine trace, Ward); the `PrecL` assembly and the `(4.16)` copies are in `TwistKer2.lean`; import order `TwistKer → TwistKer2`. (4) (v): entries of `G` between blocks at distance `≥ W^ε ℓ_v` are `≤ W^d ρ^{1/2}` from the 2-loop `ρ` (`TwistKer_entry_decay`); `Ẽ^{G̊}`, `(Ẽ⊗Ẽ)`, `L̃` are products of entries (one far entry, the others `≤ η⁻¹`; second term of `∂L̃`: the block `[x] = [y]` and the triangle inequality), `K̃` by `baTwKDecay_holds`, `B̃₁`, `B̃₂` by `|b - c₁| ≥ X` or `|a - b| ≥ 2X`; polynomial factors go through `W ≥ N^𝔠` with `D_pp = 2D + 16/𝔠` (`TwistKer2_arith`, `_close`). Not used: the Cauchy-Schwarz conjunct of `BATwistSrc3`, the Schatten trick, 6-loops, `stContractM_holds`. `TwistPins.lean` is unchanged.
## (c) Verified Mathlib names
Present (compiled): `Matrix.linfty_opNorm_mulVec`, `pi_norm_le_iff_of_nonneg`, `Finset.sum_filter_add_sum_filter_not`, `isLittleO_rpow_exp_pos_mul_atTop`, `Real.sum_sqrt_mul_sqrt_le`, `Real.le_sqrt_of_sq_le`, `Matrix.reindexAlgEquiv`, `map_list_prod`, `Matrix.isHermitian_diagonal_iff`, `Matrix.inv_submatrix_equiv`, `Matrix.trace_mul_comm`, `Finset.sum_le_card_nsmul`, `Finset.sum_fiberwise`, `Finset.exists_max_image`, `Matrix.one_apply_ne`. Absent (`Unknown constant` in the tool log): `Matrix.conjTranspose_diagonal`, `Finset.sum_filter_congr`. Deprecated (warning in the log): `if_pos`, `if_neg`, `dif_pos`, `dif_neg`, `if_true`.
## (d) Open issues and paper-delta candidates
- T2429a-1 (T.1 (iii), as (a″)): `BATwKDecay` is `∀ᶠ n`, uniform in `v ∈ [0, t₀]`, cut at `ellT (sz.L n) (sz.lam n)` and in `zdistInf`, bound `W^{-D}` without constant; the threshold `W₀` is large ((a) table) and enters only `∀ᶠ n`. T2429a-2 (route, statement unchanged): T.11 (v) is proved from entry decay (T.5 at `n = 2`) and polynomial bounds, not from T.5 for 3- and 6-loops (TP:146-147).
- The four T.11 theorems are conditional on `twSteps` (the frame): by design; TL2d supplies Steps 1-4. Public stem helpers for TL2c/TL2d: `TwistKer_{twL2_bounds, loop2_le, loop1_le, entry_le, entry_decay, far_split, zdistInf_neg, twEG_le, twEG_decay, twEE_decay}`.
- Hub: after the last `import` of `RBM3D.lean` add `import RBM3D.BA.TwistKer` and `import RBM3D.BA.TwistKer2` (pre-check above). `RBM3D/Probe/T2429Pins.lean` stays on the branch, not for merge. No (a′): nothing in (a) was contradicted by the compiled proofs.
