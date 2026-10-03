Prover model: claude-sonnet-5-5
## (a) Math preflight — Sat Oct  3 09:48:42 UTC 2026

Targets (S1-15): `Kstab` constant for `d ≥ 3`; `Stable (svar d L W g) ((t:ℂ)·m(E)²) K` on `Vtx d L W = Zd d L × Fin (W^d)`,
uniformly in `t∈[0,1)`, `|E| ≤ 2-κ`, `0<g≤Λ`; absorption `K·W^{-c} ≤ 1/2` eventually along `sz.Admissible 𝔠 𝔡`.
Proof sketch (as in RBM2D `Green/Stability.lean:53` `stable_svar`, `d`-free): `S = S^(B)⊗W^{-d}J`; a solution of `v-ξSv=r`
has block averages `ṽ=Θ_ξ r̃`, `v=r+ξ S^(B)ṽ`, `‖v‖∞ ≤ (1+KΘ)‖r‖∞` with `KΘ = max_a Σ_b|Θ_ξ(a,b)|`, `ξ=t m²`.
`d≥3` row sum: pin 5s (`Prop5Short`, **proved**: `prop5Short_holds`, `RBM3D/Propagator/Prop5Short.lean:400`) at `m=mE E`,
`σ=true` (`PropSpin m true * PropSpin m true = m²`): `|Θ(0,a)| ≤ C_s(1_{a=0}+g² e^{-c_s|a|})`; translation invariance
(`Theta_apply_add_right`) gives every row; `Σ_{a∈Z_L^d} e^{-c|a|} ≤ expC(d-2,c)` uniformly in `L` (merged
`sum_radial_exp_decay_le`, `RBM3D/Defs/RadialSum.lean:275`, stated for `Zd (k+2) L`, `d=k+2`). Hence
**`Kstab3(d,Λ,κ) = 1 + C_s(1 + Λ²·expC(d-2, c_s))`, no `L`, no `log L`** (RBM2D: `Kstab2 = 1 + A(1+log L)`).
`log L` does **not** survive in this ticket: it enters only through `latticesum_d3` (`Kernel/SumDecay.lean:149`), not used here.
The absorption `K W^{-c} ≤ 1/2` then needs only `W→∞` (from `SizeTendsto`+`Bandwidth`); no `log`-vs-power step.

### (i) Exponent / constant table
| item | value | constraint | slack |
|---|---|---|---|
| `κ''` (pin-5s bulk parameter) | `sqrt(κ(4-κ))/2` | `κ'' ≤ Im mE(E) = sqrt(4-E²)/2` for `|E|≤2-κ` (since `4-E² ≥ κ(4-κ)`); `0<κ''` iff `0<κ<4` | equality at `|E|=2-κ`; at `κ=1/2`: `0.66144` vs `Im m(1.5)=0.66144` |
| `κ'` inside `prop5Short_holds` | `min κ'' 1` | `κ' ≤ κ''` | `κ''<1` for `κ=1/2` (instance) |
| `ξ = t m²`, `‖ξ‖` | `t·‖m‖² = t` | `‖ξ‖<1` (needs `ht1 : t<1`, `‖m‖=1` from `|E|≤2`) | `1-t` |
| `Λ` (g-window) | `𝔡⁻¹` | `0<g=lam n ≤ Λ`; both eventually from `sz.WO 𝔡` (`lam ≥ W^{-d/2+𝔡}>0`, `lam ≤ 𝔡⁻¹`) | instance: `g=1/64 ≤ 10` |
| `s_min` | `(1+2dΛ²)⁻¹` | `0<s_min≤1` | `d=3,Λ=10`: `1/601` |
| `q,r,r₂,θ` | `q=(1+4 s_min κ'²)⁻¹, r=(1+q)/2, r₂=(1+r)/2, θ=r/r₂` | `0<θ<1`: `q<r<r₂<1` | `1-r₂=7.3e-4` (`Λ=10`) |
| `c_s` | `-log θ` | `>0` | `7.27e-4` (`Λ=10`), `5.41e-2` (`Λ=1`) |
| `C_s` | `κ'⁻¹(1-r₂)⁻¹(1+2d/(κ' r))` | `>0` | `2.10e4` (`Λ=10`), `335` (`Λ=1`) |
| `expC(k,c)` | `2^{k+2}·2·2^{k+3}(1+(k+3)!/c^{k+3})`, `k=d-2` | `c>0`; uniform in `L` | `2.2e16` (`Λ=10`, `k=1`) |
| `Kstab3` | `1+C_s(1+Λ² expC(d-2,c_s))` | `≥ 1+max_a Σ_b|Θ_ξ(a,b)|` | `4.6e22` (`Λ=10`), `2.4e11` (`Λ=1`) vs measured `≤2.2` (script 1) |
| absorption exponent `c>0` | any; `K W^{-c} ≤ 1/2` | `W ≥ (2K)^{1/c}`, `W→∞` | `c=1/2,Λ=1`: `W ≥ 2.3e23` (limit statement only) |
| `Bandwidth 𝔠`, `WO 𝔡` | `𝔠=1/6`, `𝔡=1/10` | `W≥N^𝔠`; `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` | instance `sz0`, `n=0`: `N^{1/6}=11.31 ≤ 32`; `W^{-1.4}=0.0078 ≤ 0.0156 ≤ 10` |
| bulk gap `gapK κ` (RBM2D route) | `min 1 sqrt(κ(4-κ)/2)` | not needed for `d≥3` (PT route replaces it) | `d=2` value at `κ=1/2`: `Kstab2(L=4)=2.5e21`, grows `1+log L` |
Stage-1b notes: (1) `prop5Short_holds` is `∃ C c`; `Kstab3` must be `Classical.choose`-style or the theorem stated `∃ K` (the explicit
constants in its proof body, read above, are `κ'⁻¹(1-r₂)⁻¹(1+2d/(κ' r))`, `-log θ`; the statement hides them) — a decision for 1b; constants are
non-sharp (measured `C_s≈1.6`, `K≈2.2`). (2) `Prop5Short` needs `3≤d`, `0<Λ`, `0<κ''`, `g>0`: `d=k+2` rewrite for `sum_radial_exp_decay_le`.
(3) `eventually_` statement takes `sz.Admissible 𝔠 𝔡` (RBM3D R1), `Kstab3` depends on `(d,Λ=𝔡⁻¹,κ)` only. (4) RBM2D file read from the
working tree (HEAD `9e0f275`); `git show c9a24cf:RBM2D/Green/Stability.lean | diff` differs only in comments and a `Checks` section (lines 362-413); declaration lines at `c9a24cf`: Kstab2:40, stable_svar:53, stable_svar_bulk:213, eventually_Kstab2_mul_rpow_le:304.

### (ii) Concrete nondegenerate instance and numeric check (no Lean; python scripts in scratchpad `T2046/`)
Instance: `d=3`, `κ=1/2`, `E=1` (`|E|=1 ≤ 3/2`), `m=mE 1=(-1/2+i√3/2)`, `‖m‖=1`, `Im m=0.866 ≥ κ''=0.661`, `t=9/10`, `ξ=t m²`, `|ξ|=0.9`;
`sz0` (merged `RBM.Gauss.SizesInst.sz0`) at `n=0`: `L=4`, `W=32`, `lam=g=1/64`, `N=(WL)^3=2097152`, `𝔠=1/6`, `𝔡=1/10`, `Λ=10`; all hypotheses
of the three targets (`3≤L`, `0<g≤Λ`, `0<κ`, `|E|≤2-κ`, `0≤t<1`, `Admissible 𝔠 𝔡`) hold simultaneously. The external hypothesis is the pin 5s
(proved, not external); its limit check is the measured `C_s(c=1)` column below (bounded in `L`, no growth like `1+log L`).
Script 1 `stab.py` (`d=3`, `W=2`, `L∈{3,5,9}`, `g∈{0.1,0.5}`, `t∈{0.5,0.99,0.9999}`, `E∈{0,1,1.5}`, `κ=1/2`; `Θ(0,·)=ifft(1/(1-ξ·fft(SB)))`;
exact `‖(1-ξS)⁻¹‖_{∞→∞}` on the fine lattice by block formula, checked against dense inversion):
`$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2046 && python3 stab.py` (rows below are verbatim lines of its output)
```
check block formula vs dense fine inverse (L=3, g=0.5, E=1, t=0.9):
1.6636917798182025 1.6636917798182138
L=3 g=0.1 E=0 t=0.99: 1.3773445437828697 1.3773445437828764
 L    g      t   E | ||inv||_fine 1+rowsum|Th|    1/(1-t)    1+logL   Cs(c=1) 1+g2*sumexp
 3  0.5 0.9999 1.5 |     2.009268     2.640541    10000.0     2.099    0.9092    2.3074 
 5  0.5 0.9999 1.5 |     2.143318     2.769904    10000.0     2.609    0.9162    3.0194 
 9  0.1 0.9999 1.5 |     1.621410     1.813019    10000.0     3.197    1.5500    1.0984 
 9  0.5 0.9999 1.5 |     2.161895     2.788511    10000.0     3.197    0.9159    3.4591 
violations of ||inv||<=1+rowsum: 0
```
(excerpt of the worst rows of the 54-row table; all 54 rows: `‖inv‖ ≤ 1+rowsum` holds, `‖inv‖ ≤ 2.17`, `C_s(c=1) ≤ 1.55`, bounded as `1/(1-t)` runs `2→10⁴`, and `L=5→9` changes `‖inv‖` by `<0.02` while `1+log L` grows `2.61→3.20`.)
Script 2 (explicit constants, `d=2` comparison, instance `sz0, n=0`): `$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/d787b0e7-ec73-431d-9968-a805c3e11390/scratchpad/T2046 && python3 inst.py` (verbatim output)
```
kappa'' = sqrt(k(4-k))/2 = 0.6614378277661477 ; Im m(E=1.5) = 0.6614378277661477 >=  0.6614378277661477
min Im m over |E|<=3/2: 0.6614378277661477
Lambda=10: s_min=0.00166389 q=0.99709664 r=0.99854832 r2=0.99927416 c_s=0.000726631 C_s=21004.7 expC(1,c_s)=2.204e+16
   K3 = 1+C_s(1+Lam^2 expC) = 4.629e+22 ; threshold W for K3*W^(-1/2)<=1/2: W>=8.572e+45 (log10 45.93)
Lambda=1: s_min=0.142857 q=0.80000000 r=0.90000000 r2=0.95000000 c_s=0.0540672 C_s=334.999 expC(1,c_s)=7.19e+08
   K3 = 1+C_s(1+Lam^2 expC) = 2.409e+11 ; threshold W for K3*W^(-1/2)<=1/2: W>=2.32e+23 (log10 23.37)
RBM2D Kstab2(1/2,L=4)=2.514e+21
RBM2D Kstab2(1/2,L=1000)=8.33e+21
RBM2D Kstab2(1/2,L=1000000)=1.561e+22
|xi| = 0.8999999999999999 < 1 ; |m|= 0.9999999999999999
max row sum |Theta| (translation inv.) = 0.6083568654204793 ; ||(1-xi S)^-1||_{inf->inf} (fine, W=32) = 1.5467386990904164  <= 1+rowsum = 1.6083568654204794
size= 2097152 ; size^(1/6)= 11.31370849898476  <= W= 32 ; W^(-3/2+1/10)= 0.007812500000000002  <= lam= 0.015625  <= 1/frakd=10
```
The `K W^{-c} ≤ 1/2` conclusion is a limit statement (`∀ᶠ`); its threshold is huge with the proof-derived constants, as RBM2D's (`Kstab2 ~ 1e21`), not a hypothesis defect.

### Verdicts
- `Kstab3` / `stable_svar` (d-free port, `1+KΘ`): **PASS**.
- `stable_svar_bulk` for `d≥3` via `prop5Short_holds` + `sum_radial_exp_decay_le`, constant `Kstab3(d,Λ,κ)` independent of `L`: **PASS**.
- `eventually_Kstab3_mul_rpow_le` under `sz.Admissible 𝔠 𝔡`: **PASS** (needs only `W→∞`; `lam n ∈ (0, 𝔡⁻¹]` eventually).
- Overall: **PASS**.

## (a′) Preflight corrections: none. The line citations of (a) were re-checked (`python3 cite_check.py`); the numeric tables of (a) were not re-run.
RBM3D (cited in (a)): Prop5Short.lean prop5Short_holds 400; RadialSum.lean sum_radial_exp_decay_le 275; SumDecay.lean latticesum_d3 149
RBM2D@c9a24cf Green/Stability.lean: Kstab2 40; stable_svar 53; stable_svar_bulk 213; eventually_Kstab2_mul_rpow_le 304

## (b) Script output (stage 1b, `prover-max`, claude-sonnet-5-5), started Sat Oct  3 10:18:00 UTC 2026 (`date -u`); `scratchpad/T2046/final.sh` runs every command below, outputs pasted verbatim
$ git status --short; git log --oneline -2          # b.1 branch state; worktree /Users/junyin/Lean_proof/RBM3D-wt/T2046, branch t/T2046
(status rc=0; empty = clean)
d46b4ec T2046: S1-15 Green/Stability, stability of 1 - t m² S on the band profile, d ≥ 3 constant Kstab3
d9de66f T2042: merge EK-4 (sumAzero) => (sum_res_2) under L^d <= W^K (Amend 1)
$ lake build RBM3D.Green.Stability 2>&1 | tail -n 5;  TZ=UTC stat -f '%Sm UTC %N' <Stability.lean, Stability.olean>;   # b.2 build
$ lake build 2>&1 | grep -E "Build completed|error|warning: .*Stability"        # full library, root #assert_rbm_axioms included
Build completed successfully (3297 jobs).
2026-10-03 10:07:46 UTC RBM3D/Green/Stability.lean
2026-10-03 10:07:52 UTC .lake/build/lib/lean/RBM3D/Green/Stability.olean
Build completed successfully (3743 jobs).
$ lake env lean ax1.lean      # b.3 `#print axioms` of the 8 public declarations (import RBM3D.Green.Stability)
'RBM.Green.stable_svar_vtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stable_svar' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.Kstab3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.one_le_Kstab3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stable_svar_bulk_vtx' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stable_svar_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.eventually_Kstab3_mul_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.eventually_stable_svar_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
$ inst_named.lean = the 8 `example`s of section 4 copied as `theorem inst1..inst8` + `#print axioms`; `| sort | uniq -c`
   8 inst_k depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom|^ *axiom " RBM3D/Green/Stability.lean
grep rc=1 (1 = no match)
### b.4 Target statements, extracted from the file by script (`extract2.py`: docstrings and proofs omitted; `pin5sC`, `pin5sc` are private)
```
-- RBM3D/Green/Stability.lean lines: variable:65 variable:314 stable_svar_vtx:80 stable_svar:175 Kstab3:212 one_le_Kstab3:230 stable_svar_bulk_vtx:320 stable_svar_bulk:352 eventually_Kstab3_mul_rpow_le:368 eventually_stable_svar_bulk:383
variable {d L W : ℕ} {g : ℝ} [NeZero L] [NeZero W]
theorem stable_svar_vtx (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {KΘ : ℝ}
    (hΘ : ∀ a : Zd d L, ∑ b : Zd d L, ‖Theta d L g ξ a b‖ ≤ KΘ) :
    Stable (svar d L W g) ξ (1 + KΘ) :=
theorem stable_svar (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {KΘ : ℝ}
    (hΘ : ∀ a : Zd d L, ∑ b : Zd d L, ‖Theta d L g ξ a b‖ ≤ KΘ) :
    Stable (svarF d L W g) ξ (1 + KΘ) :=
noncomputable def Kstab3 (d : ℕ) (Λ κ : ℝ) : ℝ :=
  1 + pin5sC d Λ (Real.sqrt (κ * (4 - κ)) / 2) *
    (1 + Λ ^ 2 * expC (d - 2) (pin5sc d Λ (Real.sqrt (κ * (4 - κ)) / 2)))
theorem one_le_Kstab3 (d : ℕ) (Λ κ : ℝ) : 1 ≤ Kstab3 d Λ κ :=
theorem stable_svar_bulk_vtx (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ κ E t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (svar d L W g) ((t : ℂ) * mE E ^ 2) (Kstab3 d Λ κ) :=
theorem stable_svar_bulk (hd : 3 ≤ d) (hL : 3 ≤ L) {Λ κ E t : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (svarF d L W g) ((t : ℂ) * mE E ^ 2) (Kstab3 d Λ κ) :=
theorem eventually_Kstab3_mul_rpow_le {d : ℕ} (sz : Sizes d) (Λ κ : ℝ) {𝔠 c : ℝ}
    (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto) (hbw : sz.Bandwidth 𝔠) :
    ∀ᶠ n in atTop, Kstab3 d Λ κ * (sz.W n : ℝ) ^ (-c) ≤ 1 / 2 :=
theorem eventually_stable_svar_bulk {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 κ : ℝ}
    (hadm : sz.Admissible 𝔠 𝔡) (hκ : 0 < κ) :
    ∀ᶠ n in atTop, ∀ E t : ℝ, |E| ≤ 2 - κ → 0 ≤ t → t < 1 →
      Stable (svarF d (sz.L n) (sz.W n) (sz.lam n)) ((t : ℂ) * mE E ^ 2) (Kstab3 d 𝔡⁻¹ κ) :=
```
### b.5 The compiled nonempty instances (`extract_inst.py`, section `Checks` of the same file; every `by norm_num` discharges one hypothesis)
```
-- RBM3D/Green/Stability.lean:403-457 (`section Checks`, docstrings omitted)
example : Stable (svar 3 4 32 (1 / 64)) (((1 / 2 : ℝ) : ℂ) * mE 1) (1 + (1 - (1 / 2 : ℝ))⁻¹) :=
  stable_svar_vtx (W := 32) (g := 1 / 64) (by norm_num)
    (norm_t_mul_lt_one (by norm_num) (by norm_num) (norm_mE (by norm_num)))
    (fun a => sum_norm_Theta_row_le (by norm_num) (by norm_num) (by norm_num)
      (norm_mE (by norm_num)) a)
example : Stable (svarF 3 4 32 (1 / 64)) (((1 / 2 : ℝ) : ℂ) * mE 1) (1 + (1 - (1 / 2 : ℝ))⁻¹) :=
  stable_svar (W := 32) (g := 1 / 64) (by norm_num)
    (norm_t_mul_lt_one (by norm_num) (by norm_num) (norm_mE (by norm_num)))
    (fun a => sum_norm_Theta_row_le (by norm_num) (by norm_num) (by norm_num)
      (norm_mE (by norm_num)) a)
example : Stable (svar 3 4 32 (1 / 64)) (((9 / 10 : ℝ) : ℂ) * mE 1 ^ 2) (Kstab3 3 10 (1 / 2)) :=
  stable_svar_bulk_vtx (W := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : Stable (svarF 3 4 32 (1 / 64)) (((9 / 10 : ℝ) : ℂ) * mE 1 ^ 2) (Kstab3 3 10 (1 / 2)) :=
  stable_svar_bulk (W := 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : 1 ≤ Kstab3 3 10 (1 / 2) := one_le_Kstab3 3 10 (1 / 2)
example : ∀ᶠ n in atTop,
    Kstab3 3 10 (1 / 2) * (sz0.W n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 :=
  eventually_Kstab3_mul_rpow_le sz0 10 (1 / 2) (𝔠 := 1 / 6) (c := 1 / 2) (by norm_num)
    (by norm_num) sz0_tendsto sz0_bandwidth
example : ∀ᶠ n in atTop, ∀ E t : ℝ, |E| ≤ 2 - 1 / 2 → 0 ≤ t → t < 1 →
    Stable (svarF 3 (sz0.L n) (sz0.W n) (sz0.lam n)) ((t : ℂ) * mE E ^ 2)
      (Kstab3 3 (1 / 10)⁻¹ (1 / 2)) :=
  eventually_stable_svar_bulk sz0 (by norm_num) sz0_admissible (by norm_num)
example : ∃ n : ℕ, ∀ E t : ℝ, |E| ≤ 2 - 1 / 2 → 0 ≤ t → t < 1 →
    Stable (svarF 3 (sz0.L n) (sz0.W n) (sz0.lam n)) ((t : ℂ) * mE E ^ 2)
      (Kstab3 3 (1 / 10)⁻¹ (1 / 2)) :=
  (eventually_stable_svar_bulk sz0 (by norm_num) sz0_admissible (by norm_num)).exists
```
### b.6 Name clash: `git grep -nw -e <each new public name> -e Kstab2 -e stable_relabel main -- RBM3D RBM3D.lean`
git grep rc=1 (1 = no hit); main = 1c1f5e4
### b.7 Port from RBM2D at `c9a24cf` (RBM1D: not read, not copied)
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/Stability.lean
 RBM2D/Green/Stability.lean | 73 ++++++----------------------------------------
 1 file changed, 9 insertions(+), 64 deletions(-)
RBM2D HEAD = 9e0f275; port source commit = c9a24cf
Statement diff (`stmtdiff.py`: RBM2D statements at c9a24cf renamed by R1-R4 and `spectralM → mE`, token diff against the RBM3D statements):
== RBM2D stable_svar (c9a24cf) renamed  ->  RBM3D stable_svar
   identical after renaming
== RBM2D stable_svar_bulk (c9a24cf) renamed  ->  RBM3D stable_svar_bulk
   insert  RBM2D: []   RBM3D: [(hd : 3 ≤ d)]
   replace RBM2D: [{κ]   RBM3D: [{Λ κ]
   insert  RBM2D: []   RBM3D: [(hg : 0 < g) (hgΛ : g ≤ Λ)]
   replace RBM2D: [(Kstab2 κ L)]   RBM3D: [(Kstab3 d Λ κ)]
== RBM2D eventually_Kstab2_mul_rpow_le (c9a24cf) renamed  ->  RBM3D eventually_Kstab3_mul_rpow_le
   replace RBM2D: [{κ 𝔠]   RBM3D: [(Λ κ : ℝ) {𝔠]
   delete  RBM2D: [(hκ : 0 < κ)]   RBM3D: []
   replace RBM2D: [Filter.atTop, Kstab2]   RBM3D: [atTop, Kstab3 d Λ]
   delete  RBM2D: [L]   RBM3D: []
`d = 2` tokens of the RBM2D file (`tok3.py`; portmap row S1-15: W^2:1 L^2:2 W⁻²/L⁻²:9 d=2:8 Z2/zdist2:16):
W2 (W^2, W²)           2 tokens at RBM2D lines: 24 49
L2 (L²)                2 tokens at RBM2D lines: 19 49
N2 (size)             11 tokens at RBM2D lines: 320 332 333 334 338 339 341 383 384 392 393
inv2 (W⁻²)             9 tokens at RBM2D lines: 24 50 67 72 86 96 97 99 116
fibre Fin W × Fin W    8 tokens at RBM2D lines: 72 86 87 96 97 99 111 116
d=2                    8 tokens at RBM2D lines: 16 19 19 22 36 39 48 302
Z2/zdist2             16 tokens at RBM2D lines: 54 54 61 71 86 131 131 249 249 275 276 277 280 281 286 286
### b.8 Registry pre-check (DECISIONS §20): scratch `precheck.lean` = `import RBM3D`, `import RBM3D.Green.Stability`, `#assert_rbm_axioms`; output filtered by `grep -E "axiom audit:|premises found|^registry:"`
axiom audit: 1484 theorems, 543 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 28 (borrowed 2, owed 14, structural 12).
registry: 5 borrowed + 19 owed + 23 structural; 19 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
exit: 0
lines mentioning RBM.Green.Stable (list of registered premises that carry nothing): 1
-- baseline (`import RBM3D` only):
axiom audit: 1477 theorems, 542 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 29 (borrowed 2, owed 14, structural 13).
registry: 5 borrowed + 19 owed + 23 structural; 18 registered premise(s) carry nothing yet: [RBM.ThetaDiffOne,
exit: 0
lines mentioning RBM.Green.Stable: 0
### b.9 Scope: `git diff main...t/T2046 --stat; git diff main...t/T2046 --name-only`
 RBM3D/Green/Stability.lean | 459 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 459 insertions(+)
RBM3D/Green/Stability.lean

### Narrative (≤ 40 lines; every figure is from the blocks above or the files)
1. **Result.** `RBM3D/Green/Stability.lean` (459 lines, commit d46b4ec on `t/T2046`): 8 public declarations (7 theorems + `Kstab3`; the scan counts +7 theorems, +1 def, b.8) and
   10 private helpers. `RBM3D/Test/Axioms.lean` is unchanged (no new `Prop`-valued definition). Build, full build, axioms, pre-check: b.2, b.3, b.8.
2. **The `d ≥ 3` constant.** `Kstab3 d Λ κ = 1 + C_s (1 + Λ² · expC(d-2, c_s))`, `(C_s, c_s)` the constants of the proved pin 5s `(prop:ThfadC_short)` (`prop5Short_holds d Λ κ''`,
   `κ'' = √(κ(4-κ))/2 ≤ Im m_E(E)` on `|E| ≤ 2-κ`), chosen with `Classical.choose` (private `pin5sC`, `pin5sc`) because the pin states `∃ C c` (preflight note 1). The explicit values
   (`C_s = κ'⁻¹(1-r₂)⁻¹(1+2d/(κ' r))`, `c_s = -log θ`) are only in the docstring of `prop5Short_holds` (`Prop5Short.lean:395-400`), not in its statement: `Kstab3` is a constant, not
   a formula, with no computable value (the preflight figures 4.6e22 / 2.4e11 evaluate those explicit constants and are not Lean-checked). It depends on `(d, Λ, κ)` only; `1 ≤ Kstab3`.
3. **`log L` does not survive.** `Kstab3` has no `L`: `Σ_{a ∈ Z_L^d} e^{-c|a|} ≤ expC(d-2, c)` uniformly in `L` (`sum_radial_exp_decay_le`, `d = k+2`; paper
   `A_deterministic_estimates.tex:67`: for `d ≥ 3` the series are summable). At `d = 3` the logarithm sits in `(eq:latticesum_d3)` (`Kernel/SumDecay.lean:149`, K-loop sums), not imported
   here. Nothing is absorbed as `L^{o(1)}`/`N^ε`: `eventually_Kstab3_mul_rpow_le` needs only `W → ∞` (`tendsto_rpow_atTop` from `SizeTendsto`, `Bandwidth`), while RBM2D must also bound
   `log L ≤ 𝔠⁻¹ log W` (RBM2D `Stability.lean:344`).
4. **Route.** Pin 5s at `σ₁ = σ₂ = +`, `m = m_E(E)` (`PropSpin m true * PropSpin m true = m²`), `ξ = t m_E(E)²`, `‖ξ‖ = t < 1`; translation invariance (`Theta_apply_add_right_of_three_le`):
   `Σ_b|Θ(a,b)| = Σ_x|Θ(0,x)| ≤ C_s(1 + g² Σ_x e^{-c_s|x|}) ≤ C_s(1 + Λ² expC)`; then `stable_svar_vtx` (`S = S^(B) ⊗ W^{-d} J`, `Σ_b‖S^(B)_{ab}‖ = 1`, `sum_norm_SB_row`). Property 4
   (`norm_Theta_apply_le`) gives only `(1-t)⁻¹`, not uniform in `t`: used in instances 1-2 only. `STKbound` is not taken; no PT or KL premise is a hypothesis (`prop5Short_holds` is a
   theorem); the added hypotheses `3 ≤ d`, `0 < g ≤ Λ` are those of pin 5s.
5. **Differences from RBM2D** (b.7 diff). `stable_svar`: identical after renaming. `stable_svar_bulk`: `+ 3 ≤ d`, `+ 0 < g ≤ Λ`, `Kstab2 κ L → Kstab3 d Λ κ`, `spectralM → mE`. `eventually_`: R1
   (`d : Sizes → sz : Sizes d`), `hκ` dropped (unused in RBM2D: `have _ := hκ`), `Λ κ` explicit, `Kstab2 κ (d.L n) → Kstab3 d Λ κ` (`Filter.atTop → atTop` is `open Filter`). Not ported: RBM2D's private d = 2 gap route (`gapK_*`,
   `norm_one_sub_sq`, RBM2D `Stability.lean:159-207`, replaced by pin 5s) and its `Checks` (`witSizes`, replaced by the instances at `sz0`).
6. **`d = 2` tokens (b.7 table).** `d=2` (8): docstring text only → `d ≥ 3`. `Z2/zdist2` (16): `Z2 L → Zd d L`; `zdist2 → zdistD d L` (inside pin 5s; ℓ¹ distance of the propagator layer, D18).
   `W⁻²` (9), `Fin W × Fin W` (8): `(W:ℂ)⁻¹ ^ 2 → ((W:ℂ)^d)⁻¹`, fibre `Fin (W^d)`. `W²`, `L²` (docstrings) → `W^d`, `Z_{WL}^d` (my `W2` count is 2, the portmap's 1). `size` (11): `sz.size n =
   (W n * L n)^d` enters only through `SizeTendsto`/`Bandwidth`; the `L ≤ size` and `log` steps (RBM2D lines 332-345) are not needed.
7. **Choices.** (i) Both index forms: `stable_svar(_bulk)` on `Idx d L W` with `svarF` (literal R4 port) and `stable_svar_vtx`/`stable_svar_bulk_vtx` on `Vtx d L W` with the merged `svar` (base proof,
   no bridge; the `Idx` form is a relabelling through `splitEquiv`, private `stability_relabel`). (ii) `eventually_Kstab3_mul_rpow_le` takes `SizeTendsto` + `Bandwidth` (as RBM2D, weaker than
   `Admissible`); the extra `eventually_stable_svar_bulk` takes `Admissible 𝔠 𝔡` (preflight note 3) and gets `0 < sz.lam n ≤ 𝔡⁻¹` eventually from `WO`, so `Λ = 𝔡⁻¹`.
8. **Instances (b.5).** `d = 3`, `L = 4`, `W = 32`, `g = 1/64 ≤ Λ = 10`, `κ = 1/2`, `E = 1`, `t = 9/10` (`ξ = m_E(1)/2` for the row-sum form), and `sz0` (admissible at `𝔠 = 1/6`, `𝔡 = 1/10`, `lam → 0`):
   every deterministic hypothesis is discharged by `norm_num` or merged lemmas; the last example extracts one `n`. A scratch copy with `E = 2` failed (`unsolved goals ⊢ False`): the discharges are real.
9. **Registry.** With the new import the structural premises *found* by the scan drop 13 → 12 and `RBM.Green.Stable` appears in the "carry nothing" list (b.8): `stable_svar*` conclude `Stable (..)`,
   which the scan counts as proving `Stable` (for the band profile only), the effect the `certificates` list documents for `TwoLoopBounded`. A certificate `(RBM.Green.Stable,
   RBM.Green.stable_svar_bulk)` is outside this ticket's rule (three tables only, DECISIONS §20): left to the dispatcher.

## (c) Verified Mathlib names used (`#check @name`, one line each; script `mathlibnames2.py`)
```
lake env lean mn2.lean: exit 0 | errors: 0 | 41 names checked
@Fintype.sum_prod_type : ∀ {γ : Type u_1} {α₁ : Type u_2} {α₂ : Type u_3} (f : α₁ × α₂ → γ), ∑ x, f x = 
@Fintype.sum_equiv : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} (e : ι ≃ κ) (f : ι → M) (g : κ → M),
@Equiv.sum_comp : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} (e : ι ≃ κ) (g : κ → M), ∑ i, g (e i) =
@Equiv.subRight : {G : Type u_1} → [AddGroup G] → G → G ≃ G
@Finset.sum_ite_eq' : ∀ {ι : Type u_1} {M : Type u_2} (s : Finset ι) (a : ι) (b : ι → M), (∑ x ∈ s, if x
@Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
@div_le_div_of_nonneg_right : ∀ {G₀ : Type u_1} [MulPosReflectLT G₀] {a b c : G₀}, a ≤ b → 0 ≤ c → a / c
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n :
@Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
@tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
@tendsto_rpow_neg_atTop : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ (-y)) Filter.atTop (nhds 0)
@Filter.tendsto_atTop_mono' : ∀ {α : Type u_1} {β : Type u_2} (l : Filter α) ⦃f₁ f₂ : α → β⦄, f₁ ≤ᶠ[l] f
@gt_mem_nhds : ∀ {α : Type u_1} [ts : TopologicalSpace α] [OrderTopology α] {a b : α}, b < a → ∀ᶠ (x : α
@Filter.Tendsto.const_mul : ∀ {M : Type u_1} [SeparatelyContinuousMul M] {α : Type u_2} {f : α → M} {x :
@Filter.Eventually.exists : ∀ {α : Type u_1} {p : α → Prop} {f : Filter α} [f.NeBot], (∀ᶠ (x : α) in f, 
@Classical.choose_spec : ∀ {α : Sort u_1} {p : α → Prop} (h : ∃ x, p x), p (Classical.choose h)
Complex.norm_real : ∀ (r : ℝ), ‖↑r‖ = ‖r‖
Complex.norm_natCast : ∀ (n : ℕ), ‖↑n‖ = ↑n
@Real.norm_of_nonneg : ∀ {r : ℝ}, 0 ≤ r → ‖r‖ = r
@sq_abs : ∀ {α : Type u_1} (a : α), |a| ^ 2 = a ^ 2
@norm_sum_le : ∀ {ι : Type u_1} {E : Type u_2} (s : Finset ι) (f : ι → E), ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f 
@Matrix.mulVec_mulVec : ∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type u_1} (v : o → α) (M : M
also checked (same run): Equiv.symm_symm Finset.sum_le_sum Finset.sum_nonneg Finset.mul_sum Finset.sum_mul Finset.sum_add_distrib Finset.sum_sub_distrib Matrix.sub_mulVec Matrix.one_mulVec Matrix.smul_mulVec Real.exp_pos Filter.Tendsto.comp Filter.Tendsto.eventually Filter.Eventually.mono Classical.choose mul_le_mul mul_le_mul_of_nonneg_left norm_pow norm_inv
```
Names verified absent / deprecated in this Mathlib (warnings of the first compile, tool log): `dif_pos` (deprecated), `if_true` (deprecated; `ite_true` used); tendsto_atTop_mono' lives in namespace `Filter`.

## (d) Open issues and paper-delta candidates
- **O1** `Kstab3` is a chosen constant (narrative 2). Every downstream use that needs only the `(d, Λ, κ)`-dependence and `Kstab3 · W^{-c} ≤ 1/2` eventually is served; an explicit
  formula needs a PT ticket that restates `prop5Short_holds` with explicit `C, c`. No obstruction was met; besides `3 ≤ d` and `0 < g ≤ Λ` (the model's parameters, b.7 diff) no hypothesis was added to any target.
- **O2** `RBM3D/Test/Axioms.lean`: the comment of `RBM.Green.Stable` says "band profile S1-24"; the band-profile proofs are here (S1-15). File unchanged (a comment edit is not a registry line).
  Scan effect and the possible `Stable` certificate: narrative 9.
- **O3** S1-16 needs no relabelling lemma: `stable_svar_bulk_vtx` is stated on `Vtx d L W` (the block profile). `stability_relabel`, `stability_vtx_to_idx` are private here, so a public port of RBM2D
  `stable_relabel` (`EntryBlock.lean:226`) in S1-16 does not clash. The root import `import RBM3D.Green.Stability` is added by the hub at merge.
- **T2046a** The stability constant depends on `(d, Λ, κ)`, `Λ = 𝔡⁻¹` the upper end of `(eq:WO)`, and is stated for `0 < g ≤ Λ`; the paper only says "constants depending on `d` and `κ`" for
  `(prop:ThfadC_short)` (`1_2:1147`). Same convention as the pins of T2003 (`Prop5Short d Λ κ`).
- **T2046b** The paper uses one letter `κ` for the spectral domain `|E| ≤ 2-κ` and for the bulk condition `κ ≤ Im m` of `(prop:ThfadC_short)`; Lean passes `κ'' = √(κ(4-κ))/2` to the pin
  (`Im m_E(E) = √(4-E²)/2 ≥ κ''` on the domain, `stability_bulkIm_le`), a reparametrisation of the dependence of the constant on `κ`.
