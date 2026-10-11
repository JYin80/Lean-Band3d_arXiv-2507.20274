Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 12:28:32 UTC 2026

Notation: `Λ := 𝔡⁻¹`; `(L, g, E, m) = (sz.L n, sz.lam n, E, BAm d L g E)`; `BAReal d L g κ E m` = `BASelf ∧ κ ≤ Im m`. It follows from the premise `κ ≤ Im m` by
`BAm_self_of_im_pos` (`BA/Step1Fam.lean:48`, `m = BAmF`, `baStep2Fam_m` `BA/Step2BA.lean`, `rfl`). `Q := BAMss … σ σ'`, `Θ := BATheta … t σ σ'`, `thetaKer = ΘQ`
(`Step2Kern_thetaKer_BA`, `Chain/Step2Kern.lean:90`; `hIm : (E+m).im ≠ 0` from `κ ≤ Im m`). `‖Q_ab‖ = BAK_ab = ‖M_ab‖²` (`BAMss_norm_eq_BAK`, `BA/KKernel.lean:102`).

### (i) Exponent / constant table (all constants in `(d, κ, 𝔡)`; no exponent of `N` occurs; `u ∈ [0,1)`, `0 < g ≤ Λ`, `L ≥ 3`)

| constant | value / source | constraint | slack |
|---|---|---|---|
| `(C₅, c₅)` | `baProp5_holds d Λ κ` (`BA/Prop6Path.lean:850`), all four charge pairs | `‖Θ_ab‖ ≤ C₅ B_{u,|a-b|₁} e^{-c₅|a-b|₁/ℓ_u}` | none: exists |
| `C₁` | `C₅ e^{1/(4c₅)}` | `‖Θ_ab‖ ≤ C₁ 𝒯_u(|a-b|_∞)` via `r ≤ ρ`, `√y ≤ c y + 1/(4c)` (copy of `k2d_theta_tail`, `Induction/Step2K2.lean:78`, with `EMn2BA_theta_shift` `BA/EMn2BA.lean:424`) | exact |
| `(C_Q, c_Q)` | `baComp_holds d Λ κ` (`BA/EMn2BA.lean:472`, `BACompBound :457`) | `‖(ΘQ)_ab‖ ≤ C_Q (1-u)⁻¹ e^{-c_Q zdistD/ℓ_u}`, no `B_{u,r}` factor | used only for `u < 1/2` |
| row/col sums | `baComp_row_le`, `baComp_col_le` (`EMn2BA.lean:386, 403`) | `Σ_b ‖(ΘQ)_ab‖ ≤ (1-u)⁻¹`, `Σ_a … ≤ (1-u)⁻¹` | equality at `u = 0` (`‖Q‖` row sum `1`) |
| `c₀` | `BAct_rate d Λ κ = min(log(1+κ/(4dΛ)), κ/2)` (`BA/CombesThomas.lean:45`) | `> 0`; enters only through `C_Q, c_Q` | `d=3`: `0.0800` (`Λ=1, κ=0.9993`), `0.0343` (`Λ=1, κ=0.4189`), `0.00278` (`Λ=10, κ=0.334`) |
| `C_s` | `2^{d-2} e` | `𝒯(r') ≤ C_s 𝒯(r)` for `r ≤ r'+1` (`nkl_tailT_shift`) | `d=3`: `5.4366` |
| `C_T` | `ekPropTInf_holds d` (`Evolution/PropTInf.lean:534`) | `Σ_z 𝒯(a-z)𝒯(z-b) ≤ C_T/(1-u) 𝒯(a-b)` | none |
| split | `u* = 1/2` | `u ≥ 1/2: 1/u ≤ 2`; `u < 1/2: (1-u)⁻¹ ≤ 2`, `ℓ_u ≤ ℓ_* := max(√2 Λ, 1)` (`g/√(1-u) ≤ √2 g`), `ℓ_u ≥ 1` | `ℓ_*`: `1.414` (`Λ=1`), `14.14` (`Λ=10`) |
| `C_P` | `sup_r (r+1)^{d-2} e^{√r - c_Q r/ℓ_*} ≤ e^{ℓ_*/(2c_Q)} e^{a} (k/(a e))^k`, `a = c_Q/(2ℓ_*)`, `k = d-2` | `e^{-c_Q r/ℓ_*} ≤ C_P (r+1)^{-(d-2)} e^{-√r}` | `python3 cp.py` (`c=0.03, ℓ_*=1.4142, k=1`): `sup_r (r+1)^k e^(sqrt r - c r/l*) = 7.900e+07 <= bound = 6.040e+11: True` |
| `Q₀` | `max(2C₁ + 2(Λ²+1), 2 C_Q C_P (Λ²+1))` | tail (B): `‖(ΘQ)_ab‖ ≤ Q₀ 𝒯_u(|a-b|_∞)` for every `u ∈ [0,1)` | see (B1), (B2) below |
| `K_c` (F7) | `Q₀ C_T + C_s` | `Σ_b ‖thetaKer_ab‖ tailW(|b-a'|) ≤ K_c/(1-u) tailW(|a-a'|)` | not `1`: numerics `K_c ≥ 1.48 / 2.98 / 1.96` (below) |
| `C_K` (F8) | `1` | `Σ_x ‖K_{(x,a₁)}‖ ≤ C_K W^{-d}(1-u)⁻¹` | equality at `u = 0` |
| `δ₀`, `C` | `κ/2`; `C = 2K_c + 2C_s(4 + C_K) + C_s C_T` (`stNewKLKAtgL'_of`, `Chain/NewKLKGen.lean:416`) | `0 < C`, `0 < δ₀` | none |

**Reduction of F7 (the exact lemmas).** F7 does **not** follow from the third conjunct of `baComp_holds` alone: that bound has no `B_{u,r}` factor, so it does not give the tail `𝒯_u` as `u → 1`.
The route is the band route (`newKLKGenHyp_band`, `Chain/NewKLKGen.lean:669-747`, `nkl_conv_P`, `Induction/NewKLK.lean:334`) with `SΘ` replaced by `thetaKer = ΘQ`:
(A) row sum `c = (1-u)⁻¹` is `baComp_row_le` (`EMn2BA.lean:386`) after `Step2Kern_thetaKer_BA`; (C) `hTTT` is `ekPropTInf_holds`; (B) tail `Q₀ 𝒯_u(|a-b|_∞)`:
* (B1) `u ≥ 1/2`: `Θ = 1 + uΘQ` (`BATheta_resolvent`, `BA/KBase.lean:330`, 2nd conjunct) gives `‖(ΘQ)_ab‖ ≤ (‖Θ_ab‖ + 1_{a=b})/u ≤ 2C₁𝒯_u(|a-b|_∞) + 2(Λ²+1)𝒯_u(0)·1_{a=b}`, since `𝒯_u(0) ≥ (g²+1-u)⁻¹ ≥ (Λ²+1)⁻¹`.
* (B2) `u < 1/2`: `baComp_holds` (3rd conjunct), `zdistD ≥ zdistInf = r`, `ℓ_u ≤ ℓ_*`: `‖(ΘQ)_ab‖ ≤ 2C_Q e^{-c_Q r/ℓ_*} ≤ 2C_Q C_P (r+1)^{-(d-2)}e^{-√r}`, and `𝒯_u(r) ≥ (Λ²+1)⁻¹(r+1)^{-(d-2)}e^{-√r}` (`g²+|1-u| ≤ Λ²+1`, `ℓ_u ≥ 1`).
* Then a copy of `nkl_conv_P` for a generic kernel `‖X_ab‖` (it reads only `hTail`, `hRow`, `hTTT`; opened-private `nkl_tailW_eq_of_near`, `nkl_tailW_far`, `nkl_tailT_le_tailW`, `nkl_Cs_ge_one`) gives `(Q₀ C_T/(1-u)) + C_s (1-u)⁻¹ = K_c/(1-u)`.
`tailW(ℓ', D')` with arbitrary `ℓ', D' ≥ 0` is handled exactly as at the band (the floor `W^{-D'}` and `min(r, ℓ')` are inside `nkl_conv_P`).
`BAMfine_decay` and `BAK_row_sum` are not needed beyond their use inside `baComp_holds`.

**Remaining clauses (all by merged lemmas, C1-clean: `g` unrestricted except `0 < g ≤ Λ`, `Q`/`M` non-scalar).**
* F5: `S = 1` (`baFM`, `BA/FlowPins.lean:322`): `1 x y ≠ 0 → x = y`, `zdistInf 0 = 0 ≤ 1`; row sums `1`; symmetric.
* F6: `‖m‖² = ‖M_aa‖² ≤ Σ_b ‖M_ab‖² = 1` from `BAMB_diag_eq` (`BA/Ward.lean:89`), `BAMB_row_sq_real` (`:125`); `BAPropM` is not used.
* F8: `K n u σ ![x,a₁] = BAKsol … (KLloopOf σ ![x,a₁])`; `baKsolve` (`BA/KTreeRep.lean:1699`, clause `(Kn2sol)`) + `BAKsol_isKLoopS` (`BA/KSolve.lean:606`) + `baK_unique` (`:568`, loop WF of length 2) give `K = W^{-d}(ΘQ)_{x a₁}`; marginals by `baComp_col_le`, `baComp_row_le`.
* F9: `LM = loopFine … ζ` with `ζ = ztOf m E u` (rfl in `baStep2Mat`); `ζ.im = (1-u) Im m` (`ztOf = E + (1-u) m`, `Loop/GLoopFlow.lean:55`); `GMM x x = Gres H ζ true x x − BAMfine x x`, `BAMfine x x = BAMB a a = m` (`BAMfine_eq`, `BA/GreenSchur.lean:93`; `BAMB_diag_eq`).
* Target 3 (`STK2decaygL'`): `K = W^{-d}(ΘQ)_{a₀a₁}` as in F8, and `STprof sz n u D L = W^{-d} tailW(…, ℓ=L, D)(r) ≥ W^{-d} 𝒯_u(r)` (`r ≤ L`, `min r L = r`, as `stK2decay_holds`, `Induction/Step2K2.lean:132`); (B) gives `C = Q₀`; no convolution.

### (ii) Concrete nondegenerate instance and numerics

Instance: `d = 3`, `κ = 1/2`, `𝔡 = 1` (`Λ = 1`), `sz := sz0.withLam (BAflowLam0 sz0 zSeq)`, `n = 0` (`L = 4`, `W = 32`, `lam 0 = gI`), `E = EI`, the BA datum `(gI, EI, mI)` of
`EKPinsInst` (`BA/EKPins.lean:643-645`); `hrI : BAReal 3 4 gI (1/2) EI mI` (`:668`), `gI_pos`, `gI_le : gI ≤ 1/64 ≤ 𝔡⁻¹`. Then `(baStep2Fam sz (fun _ => EI)).m 0 = mI` (`baStep2Fam_m`).
Every hypothesis of the targets is a closed fact there (`3 ≤ d`, `0<κ`, `0<𝔡`, `0 < lam ≤ 𝔡⁻¹`, `κ ≤ Im m`, `0 ≤ u < 1`); no external pin occurs (all inputs are merged theorems); `n`, `u` are free, `u = 1/32` is used below.
Script `inst.py` rebuilds the datum from `zS = 6i/5 − mS`, `t₀ = Im mS/(Im mS + Im zS)`, `g₀ = √t₀ g`, `E = (t₀ Re zS − (1−t₀) Re mS)/√t₀`, `m = mS/√t₀` (definitions `BAt0`, `BAflowE`, `BAflowLam0`, `FlowPins.lean:1263`),
solves `(self_m)` independently, and tests F5, F6, F8 row sums, F9 imaginary part, and the F7 ratio over `ℓ' ∈ {0.5,1,3,4}`, floors `{0, 1e-3𝒯(0), 1e-1𝒯(0)}`, all four charge pairs.
Command: `cd <scratch>/T2424 && python3 inst.py` (numpy 2.0.2; `f7.py` is imported). Output:
```
mS=-0.000000+0.832488j zS=0.000000+0.367512j t0=0.693740  g0=0.01301423  E=3.12e-18
BA datum: g0=0.01301423 (<= 1/64=0.01562500), E=3.1e-18, m=-0.000000+0.999493j, |m|=0.999493, Im m=0.999493, self-consistency residual=2.0e-13
mS/sqrt(t0) = -0.000000+0.999493j
hyp: kappa=1/2 <= Im m: True ; 0<lam<=1/dd=1: True ; L>=3: True
F5/F8-input: S=1 row sum 1; Ward sum_b |M_ab|^2 = 0.9999999999998018 ; M_aa - m = 1.9784174299004732e-13
F6: |m| <= 1: True
u=0      Im zeta=(1-u)Im m=0.99949  [++: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.984, (1-u)*F7ratio=1.001]  [--: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.984, (1-u)*F7ratio=1.001]  [+-: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.984, (1-u)*F7ratio=1.001]  [-+: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.984, (1-u)*F7ratio=1.001]
u=0.03125 Im zeta=(1-u)Im m=0.96826  [++: (1-u)*rowsum=0.9394<=1, max|K|/tailT=0.924, (1-u)*F7ratio=0.940]  [--: (1-u)*rowsum=0.9394<=1, max|K|/tailT=0.924, (1-u)*F7ratio=0.940]  [+-: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.984, (1-u)*F7ratio=1.001]  [-+: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.984, (1-u)*F7ratio=1.001]
u=0.5    Im zeta=(1-u)Im m=0.49975  [++: (1-u)*rowsum=0.3333<=1, max|K|/tailT=0.328, (1-u)*F7ratio=0.333]  [--: (1-u)*rowsum=0.3333<=1, max|K|/tailT=0.328, (1-u)*F7ratio=0.333]  [+-: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.983, (1-u)*F7ratio=1.001]  [-+: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.983, (1-u)*F7ratio=1.001]
u=0.99   Im zeta=(1-u)Im m=0.00999  [++: (1-u)*rowsum=0.0050<=1, max|K|/tailT=0.005, (1-u)*F7ratio=0.005]  [--: (1-u)*rowsum=0.0050<=1, max|K|/tailT=0.005, (1-u)*F7ratio=0.005]  [+-: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.910, (1-u)*F7ratio=1.061]  [-+: (1-u)*rowsum=1.0000<=1, max|K|/tailT=0.910, (1-u)*F7ratio=1.061]
g=1/64: Lambda=1 kappa=0.999269  c0=BAct_rate=0.07999  Cs=2^(d-2)e=5.4366  (Lambda^2+1)=2  ell*=max(sqrt2*Lam,1)=1.4142
g=1: Lambda=1 kappa=0.418931  c0=BAct_rate=0.03432  Cs=2^(d-2)e=5.4366  (Lambda^2+1)=2  ell*=max(sqrt2*Lam,1)=1.4142
g=10: Lambda=10 kappa=0.334034  c0=BAct_rate=0.00278  Cs=2^(d-2)e=5.4366  (Lambda^2+1)=101  ell*=max(sqrt2*Lam,1)=14.1421
```
`mS/√t₀` matches `m`, as `FlowPins.lean:1263` states; all `(1-u)*rowsum ≤ 1`. The last three lines are the explicit constants `c₀`, `C_s`, `Λ²+1`, `ℓ_*` of the table (`Λ`, `κ` as printed). `M^{(B)} = (g₀Ψ − (E+m))⁻¹` is not diagonal (`Chain/Step2Kern.lean` §2 doc), so no scalar `m` occurs.

**K_c numerics** (torus `d = 3`, `L = 8`, general `g`, real `E`, `m` solved from `(self_m)` with `Im m > 0`; `a = 0` by translation invariance; `u ∈ {0,.5,.9,.99,.999,1−1e-5,1−1e-7}`, `ℓ' ∈ {.5,1,3,L}`, three floors, all `a'`; `(1-u)·ratio` is a lower bound for `K_c`, `max|K|/tailT` one for `Q₀`).
Command: `python3 f7.py 8 | grep -A2 -E "^g=0.015625 L=8 E=0 |^g=1 L=8 E=0 |^g=10 L=8 E=0 |^g=1 L=8 E=0.7"`. Output (`++` and `+-` pairs; `κ := Im m`):
```
g=0.015625 L=8 E=0  m=-0.000000+0.999269j  Im m=0.999269  selfres=1.05e-13
   pair ++:  (1-u)*ratio = 1.0011;  max_b |K(0,b)|/tailT = 0.9968
   pair +-:  (1-u)*ratio = 1.4817;  max_b |K(0,b)|/tailT = 1.9464
g=1 L=8 E=0  m=-0.000000+0.466463j  Im m=0.466463  selfres=5.00e-16
   pair ++:  (1-u)*ratio = 2.9775;  max_b |K(0,b)|/tailT = 2.8704
g=1 L=8 E=0.7  m=-0.085744+0.379196j  Im m=0.379196  selfres=2.78e-17
   pair ++:  (1-u)*ratio = 2.3022;  max_b |K(0,b)|/tailT = 1.5301
g=10 L=8 E=0  m=-0.000000+0.365395j  Im m=0.365395  selfres=1.01e-14
   pair ++:  (1-u)*ratio = 1.9589;  max_b |K(0,b)|/tailT = 67.7364
```
(`+-` at `g=1`, `g=10` equals `++`: same lines in `f7_L8.txt`.) Reading: `K_c ≥ 1.48, 2.98, 1.96` at `g = 1/64, 1, 10`, bounded in `u → 1`, so F7 holds with `K_c/(1-u)`, `K_c ≠ 1`; `Q₀ ≥ 1.95, 2.87, 67.7` grows with `Λ`, as the `Λ²+1` in `Q₀` predicts.
`C₅, c₅, C_Q, C_T` are existential in the merged theorems and have no numeric value; so `K_c = Q₀C_T + C_s` is a formula, and only the quantities above are numerically checked. `g = 1, E = 0`, `++`: `(1-u)·ratio = 2.46 / 2.98 / 2.35 / 2.18` at `L = 6 / 8 / 10 / 14` (same script, other `L`; not pasted): no growth with `L`.
At `g = 10` the iteration finds `Im m = 0` for `L ≥ 10, E = 0` (`BAReal` fails there; those rows are not data).

### Verdict
* Target 1 (`baNewKLKGenHyp`, F5-F9): **PASS** (F7 via (A), (B1), (B2), (C) above, not via `baComp_holds` alone).
* Target 2 (`STNewKLKgL'` at `baStep2Fam`): **PASS** (`stNewKLKgL'_of`, constant as the generic theorem gives; needs target 1 for every `κ, 𝔡 > 0`).
* Target 3 (`STK2decaygL'` at BA): **PASS** (corollary of (B), `C = Q₀`).
* Target 5 (instances): **PASS**, datum named above. Predicted size: ≈ 600-700 lines (`k2d_theta_tail` copy 50, generic `nkl_conv_P` 90, tail (B) 110, F5-F9 190, assembly + target 3 80, instances 80, header 50), below the stop line 1,200.
* Paper-delta candidate `T2424a`: none expected (F7 over the block kernel is already `T2414`).

## (b) Script output — Sun Oct 11 12:53:27 UTC 2026

```
$ wc -l RBM3D/BA/NewKLKBA.lean; git log --oneline -4; git diff main...t/T2424 --stat | tail -2   (worktree RBM3D-wt/T2424)
     824 RBM3D/BA/NewKLKBA.lean
31a2210 T2424: instance doc: state only what is proved
d46ba8b T2424: BA/NewKLKBA instances at the BA datum, GMM-small lemma, doc
d76cdbe T2424: BA pins stNewKLKgL'_ba, stK2decaygL'_ba
3f6bf50 T2424: BA/NewKLKBA F5-F9 at baStep2Fam (baNewKLKGenHyp)
 RBM3D/BA/NewKLKBA.lean | 824 +++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 824 insertions(+)
```

**F5-F9 as finally proved** (`baNewKLKGenHyp`, `RBM3D/BA/NewKLKBA.lean:446`; domain `0 < lam n ≤ 𝔡⁻¹`, `κ ≤ Im m`, `0 ≤ u < 1`; `mk = fun sz E => baStep2Fam sz E`):

| clause | proved | lemmas (file:line) | constant |
|---|---|---|---|
| F5 | `S = 1`: support `x = y` (`zdistInf 0 = 0 ≤ 1`), row sums `1`, symmetric | `Matrix.one_apply` | none |
| F6 | `‖m‖ ≤ 1`, `m = BAm d L g E` | `BAm_norm_le_one` (`BA/Ward.lean:136`); `BAm_self_of_im_pos` (`BA/Step1Fam.lean:48`) in `NewKLKBA_real` | none |
| F7 | `Σ_b ‖thetaKer_{ab}‖ tailW(ℓ',D')(b-a') ≤ K_c/(1-u) tailW(ℓ',D')(a-a')`, all `s,s'`, all `ℓ',D' ≥ 0` | `Step2Kern_thetaKer_BA` (`Chain/Step2Kern.lean:90`); `NewKLKBA_tail` (`:269`: `BATheta_resolvent` `BA/KBase.lean:330`, `baProp5_holds` `BA/Prop6Path.lean:850`, `EMn2BA_theta_shift` `BA/EMn2BA.lean:424`, `baComp_holds` `:472`); `baComp_row_le` (`:386`); `ekPropTInf_holds` (`Evolution/PropTInf.lean:534`); `NewKLKBA_conv_P` (`:61`) | `K_c = Q₀ C_T + C_s` |
| F8 | `Σ_x ‖K_{(x,a₁)}‖`, `Σ_y ‖K_{(a₀,y)}‖` `≤ C_K W^{-d}(1-u)⁻¹` | `NewKLKBA_K_two` (`:417`: `baKsolve` `BA/KTreeRep.lean:1699`, `BAKsol_isKLoopS` `BA/KSolve.lean:606`, `baK_unique` `:568`); `baComp_col_le` (`BA/EMn2BA.lean:403`), `baComp_row_le` | `C_K = 1` |
| F9 | `LM = loopFine … ζ`, `ζ = ztOf m E u`, `Im ζ = (1-u) Im m`; `GMM x x = Gres H ζ true x x - m` | `ztOf_im` (`Loop/GLoopFlow.lean:64`); `BAMfine_eq` (`BA/GreenSchur.lean:93`); `BAMB_diag_eq` (`BA/Ward.lean:89`) | none |

**`K_c`** (in `(d, κ, 𝔡)` only; not `1`: `K_c ≥ C_s ≥ 1` and `Q₀ C_T > 0`): `K_c = Q₀ C_T + C_s`, `C_s = 2^{d-2} e`, `C_T` of `ekPropTInf_holds d`,
`Q₀ = max(2C₁ + 2(Λ²+1), 2 C_Q C_P (Λ²+1))`, `Λ = 𝔡⁻¹`, `C₁ = C₅ e^{1/(4c₅)}`, `(C₅,c₅)` of `baProp5_holds d Λ κ`, `(C_Q,c_Q)` of `baComp_holds d Λ κ`,
`C_P = k!(4k/c')^k e^{1/c'+c'/4}`, `k = d-2`, `c' = c_Q/(2Λ+1)` (`NewKLKBA_exp_poly`).  The constants of the merged theorems are existential: no numeric value.
Pin constant (`stNewKLKAtgL'_of`, `Chain/NewKLKGen.lean:416`): `C = 2K_c + 2C_s(4 + C_K) + C_s C_T`, `δ₀ = κ/2`; target 3: `C = Q₀`.

```
$ lake build RBM3D.BA.NewKLKBA 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3839 jobs).
$ tail -2 <full build log>   (lake build with a TEMPORARY uncommitted line "import RBM3D.BA.NewKLKBA" in RBM3D.lean, reverted afterwards; at commit 31a2210; 12:51:25-12:52:08 UTC)
non-vacuity certificates: 0 of 90 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4235 jobs).
$ lake env lean docs/tickets/checks/T2424-check.lean >/dev/null; echo "exit=$?"
exit=0
$ lake env lean <scratch>/ax.lean   (import RBM3D.BA.NewKLKBA; #print axioms of the three public theorems)
'RBM.BA.baNewKLKGenHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKgL'_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stK2decaygL'_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
$ python3 -I <scratch>/stmt.py   (prints each public theorem header from the file, up to ":=")
446: theorem baNewKLKGenHyp (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    NewKLKGenHyp d κ 𝔡 (fun sz E => baStep2Fam sz E) := by
560: theorem stNewKLKgL'_ba (d : ℕ) : STNewKLKgL' d (fun sz E => baStep2Fam sz E) :=
567: theorem stK2decaygL'_ba (d : ℕ) : STK2decaygL' d (fun sz E => baStep2Fam sz E) := by
```

Compiled nonempty instances (`d = 3`; file lines 761-786 F5-F9 at the BA datum, 795 + 797-810 target 2, 814 + 816-820 target 3; datum `(gI, EI, mI)` of `EKPinsInst`
(`BA/EKPins.lean:643-645`), `szI = sz0.withLam (BAflowLam0 sz0 zSeq)`, `n = 0` (`L = 4`, `W = 32`), `κ = 1/2`, `𝔡 = 1`, `u = 1/32`, `ℓ' = 2`, `D' = 1`, `H = g₀ Ψ`):
```
$ sed -n "761p;779,786p;795p;797,820p" RBM3D/BA/NewKLKBA.lean | cut -c1-165
example : ∃ K_c C_K : ℝ, 0 ≤ K_c ∧ 0 ≤ C_K ∧
  obtain ⟨K_c, C_K, hKc, hCK, h5, h6, h7, h8, h9⟩ :=
    baNewKLKGenHyp (d := 3) (by norm_num) (1 / 2) 1 (by norm_num) (by norm_num)
  exact ⟨K_c, C_K, hKc, hCK, h5 szI 0 EI szI_lam_pos szI_lam_le szI_im, h6 szI 0 EI szI_lam_pos szI_lam_le szI_im,
    fun s s' a a' => h7 szI 0 EI (1 / 32) szI_lam_pos szI_lam_le szI_im (by norm_num) (by norm_num) s s' 2 1
      (by norm_num) (by norm_num) a a',
    fun σ => h8 szI 0 EI (1 / 32) szI_lam_pos szI_lam_le szI_im (by norm_num) (by norm_num) σ,
    h9 szI 0 EI (1 / 32) szI_lam_pos szI_lam_le szI_im (by norm_num) (by norm_num)⟩

example : STNewKLKgL' 3 (fun sz E => baStep2Fam sz E) := stNewKLKgL'_ba 3
example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (szI.L 0)),
    ‖STthetaOpg cmI 0 (1 / 32) σ (STLKMg cmI 0 (1 / 32) HI σ) a‖ ≤
        C / (1 - 1 / 32) * STJhatMg cmI 0 1 2 (1 / 32) HI * STprof szI 0 (1 / 32) 1 2 (a 0) (a 1) ∧
      ‖STELKLKMg cmI 0 (1 / 32) HI σ a‖ ≤
        C / (1 - 1 / 32) * (STJhatMg cmI 0 1 2 (1 / 32) HI +
          STJhatMg cmI 0 1 2 (1 / 32) HI ^ 2 * (if 1 ≤ (2 : ℝ) then 1 else 0)) *
          STprof szI 0 (1 / 32) 1 2 (a 0) (a 1) := by
  obtain ⟨C, hC, h⟩ := stNewKLKAtgL'_of (d := 3) (by norm_num) (1 / 2) 1 (by norm_num) _
    (baNewKLKGenHyp (d := 3) (by norm_num) (1 / 2) 1 (by norm_num) (by norm_num))
  refine ⟨C, hC, fun σ a => ?_⟩
  exact h szI 0 EI (1 / 32) 1 2 szI_lam_pos szI_lam_le szI_im (by norm_num) (by norm_num) zero_le_one
    (by norm_num) szI_L HI (NewKLKBA_hermitian szI 0)
    (fun x y => (NewKLKBA_GMM_small (κ := 1 / 2) (by norm_num) szI 0 EI szI_im (u := 1 / 32) (by norm_num)
      (by norm_num) x y).trans (by norm_num)) σ a

/-- **Target 3 (BAT-F2) at the BA datum**: the pin `STK2decaygL'` at `d = 3` (`stK2decaygL'_ba`), applied at `κ = 1/2`, `𝔡 = 1`,
`(szI, n = 0, E = EI, u = 1/32, D = 1)`, all `σ`, `a`. -/
example : STK2decaygL' 3 (fun sz E => baStep2Fam sz E) := stK2decaygL'_ba 3

example : ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (szI.L 0)),
    ‖cmI.K 0 (1 / 32) σ a‖ ≤ C * STprof szI 0 (1 / 32) 1 ((szI.L 0 : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C, hC, h⟩ := stK2decaygL'_ba 3 (by norm_num) (1 / 2) 1 (by norm_num) (by norm_num)
  exact ⟨C, hC, fun σ a => h szI 0 EI (1 / 32) 1 szI_lam_pos szI_lam_le szI_im (by norm_num) (by norm_num)
    zero_le_one σ a⟩
```
```
$ <scratch>/clash.sh   (grep -rnE of the new public names and NewKLKBA_* / NewKLKBAInst in RBM3D/**/*.lean, minus RBM3D/BA/NewKLKBA.lean)
grep-v exit=1 (1 = no line outside NewKLKBA.lean)
$ grep -n "sorry\|admit\|native_decide\|^axiom\|mSigma\|M = m I" RBM3D/BA/NewKLKBA.lean; echo "exit=$?"
exit=1
```

**Narrative.**
* One file `RBM3D/BA/NewKLKBA.lean`, 824 lines (stop line 1,200); `wc -l` at the section commits: 550 (`3f6bf50`, F5-F9), 604 (`d76cdbe`, pins), 825 (`d46ba8b`, GMM lemma and instances), 824 (`31a2210`, comment-only edit).
* Layout: §1 `NewKLKBA_conv_P` (a copy of `nkl_conv_P`, `Induction/NewKLK.lean:334`, for a generic kernel `X`); §2 `NewKLKBA_theta_tail` (copy of `k2d_theta_tail`, `Induction/Step2K2.lean:78`, for a generic `Θ`), `NewKLKBA_exp_poly`, `NewKLKBA_tail`; §3 F5-F9 and `baNewKLKGenHyp`; §4 the two pins; §5 `NewKLKBA_GMM_small`; §6 instances.
* F7 is not obtained from the third conjunct of `baComp_holds` alone (it has no `B_{u,r}` factor): `NewKLKBA_tail` gives `‖(Θ M^{(σσ')})_{ab}‖ ≤ Q₀ 𝒯_u(|a-b|_∞)` for every `0 ≤ u < 1`, by the split at `u = 1/2` of (a): `u ≥ 1/2` from `Θ = 1 + u ΘM` and `baProp5_holds`, `u < 1/2` from `baComp_holds`. The convolution against `tailW` is then `NewKLKBA_conv_P` with the row sum `(1-u)⁻¹` of `baComp_row_le`.
* Constants differ from the values written in the table of (a) but not in form: the Lean proof uses `ℓ_* = 2Λ+1` (not `max(√2 Λ, 1)`) and `C_P = k!(4k/c')^k e^{1/c'+c'/4}`; the formulas for `Q₀` and `K_c` are those of (a). No statement of (a) needed a correction, so there is no section (a′).
* `𝒦^{(2)}` at BA: `NewKLKBA_K_two` identifies `BAKloop` with `W^{-d}(Θ M^{(σσ')})(a₀,a₁)` through `baKsolve` (clause `(Kn2sol)`) and `baK_unique` (premise `κ ≤ Im m` gives `BAReal`); target 3 reads off `K`, so it needs no convolution.
* The instance uses `u = 1/32 > 0`: the pin's hypothesis `‖G_u - M‖_max ≤ δ₀` is discharged at `H = g₀ Ψ` by `NewKLKBA_GMM_small` (`G - M = -u m M G`, Ward `Σ_z |M_{zx}|² = 1` and `Σ_z |G_{zy}|² ≤ (Im ζ)⁻²`, Cauchy-Schwarz, `|m| ≤ 1`, `κ ≤ Im m`): `‖G_u - M‖_max ≤ u/((1-u)κ) = 2/31 ≤ 1/4 = κ/2`. The pointwise pin instance uses `stNewKLKAtgL'_of` (it fixes `δ₀ = κ/2`); `stNewKLKgL'_ba` is built from the same theorem.
* No hypothesis was added, no pinned signature changed. `RBM3D.lean` is **not** edited or committed (CLAUDE.md §1, §3 (A) 4: the hub adds the import line at merge); the full `lake build` above used a temporary import line, reverted (`git status --short` empty).
* Reuse of private names by `open private`: `nkl_Cs_ge_one nkl_tailT_le_tailW nkl_tailW_eq_of_near nkl_tailW_far nkl_tailT_shift` (`Induction/NewKLK.lean`), `k2d_sqrt_le k2d_zdistInf_neg k2d_zdistInf_le` (`Induction/Step2K2.lean`). Ports from `../RBM1D`, `../RBM2D`: none (no file there was read); no diff-stat applies.
* The module docstring has lines over 100 characters (style-linter warnings in the build log, as in sibling files); no other warning from `NewKLKBA.lean`.

## (c) Verified Mathlib names (`#check` in the worktree, after `import RBM3D.BA.NewKLKBA`)
`Real.pow_div_factorial_le_exp` (`0 ≤ x → ∀ n, x ^ n / n ! ≤ exp x`); `Real.le_sqrt'` (`0 < x → (x ≤ √y ↔ x ^ 2 ≤ y)`; `Real.le_sqrt` needs `0 ≤ x → 0 ≤ y`);
`Finset.sum_mul_sq_le_sq_mul_sq`; `abs_le_of_sq_le_sq` (`a ^ 2 ≤ b ^ 2 → 0 ≤ b → |a| ≤ b`); `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel` (`IsUnit x → …`);
`inv_anti₀` (`0 < b → b ≤ a → a⁻¹ ≤ b⁻¹`); `inv_le_comm₀`; `div_le_self`; `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`; `Real.sqrt_le_sqrt`;
`Complex.im_le_norm`, `Complex.norm_natCast`, `Complex.norm_real`; `Matrix.conjTranspose_smul`, `Matrix.mul_smul`, `Matrix.smul_mul`; `Finset.sum_ite_eq`.
Names verified absent: none searched. Compiler warnings seen: `if_pos`, `if_neg`, `if_true` are deprecated in this Mathlib (not used in the final file).

## (d) Open issues and paper-delta candidates
* Paper-delta candidates: none (`T2424a` not needed): the Lean statements are the pins `NewKLKGenHyp` (`Chain/NewKLKGen.lean:383`), `STNewKLKgL'` (`:69`), `STK2decaygL'` (`Chain/Step2Gen.lean:1118`) at `fun sz E => baStep2Fam sz E`, as the ticket states them.
* The hub must add `import RBM3D.BA.NewKLKBA` to `RBM3D.lean` at merge (not committed here).
* The ticket asks for a report of at most 150 lines; with section (a) (written by `preflight`, 90 lines) this report is longer (CLAUDE.md §6 allows 300).
* `Q₀`, `K_c`, `C` have no numeric value: they are built from existential constants of merged theorems (`baProp5_holds`, `baComp_holds`, `ekPropTInf_holds`).
