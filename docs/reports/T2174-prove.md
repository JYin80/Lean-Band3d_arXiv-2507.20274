Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct  5 04:37:47 UTC 2026

Scratch scripts (no Lean): `.../scratchpad/T2174/pre.py` (table), `.../scratchpad/T2174/inst.py` (instance); stdlib Python, exact `Fraction` for the table, float for the instance.
Source read: probe `73b451c:RBM3D/Probe/T2162Pins.lean` sections 3, 5, 5b, 5d, 7; `RBM3D/Defs/Sizes.lean:177,260,331` (`Admissible`, `sz0`, `sz0_admissible`); `docs/reports/T2162-prove.md` (a) lines 29-30.
Dimension d = 3 throughout; `N = (WL)^d`; `W ≥ N^𝔠` and `(eq:WO)`: `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`Sizes.lean:177`).

### (i) Exponent table (probe section 5 lemma in the last column)

| quantity | value | constraint | slack | probe lemma |
|---|---|---|---|---|
| `𝔠` | 1/6 (second row 1/4) | `0 < 𝔠`, `d𝔠 < 1` (from `W ≥ N^𝔠`, `L ≥ 3`) | `1 − d𝔠` = 1/2 (1/4) | `un_dc_lt_one` |
| `𝔡` | 1/10 (second row 1/5) | `0 < 𝔡 < d/2` (from `(eq:WO)`, `W → ∞`) | `d/2 − 𝔡` = 7/5 (13/10) | `un_d_lt_half` |
| `ε₀ = 𝔡/3` | 1/30 (1/15) | `ε₀ ∈ (0, 𝔡/2)` | `𝔡/2 − ε₀ = 𝔡/6` = 1/60 (1/30) | `un_que_params` |
| `c = 𝔡/6` | 1/60 (1/30) | `0 < c < ε₀`, `c < 𝔡/5` | `ε₀ − c = 𝔡/6` = 1/60 (1/30); `𝔡/5 − c = 𝔡/30` = 1/300 (1/150) | `un_que_params` |
| QUE exponent | `−(2ε₀ ∧ 2𝔡/5) + 2c = −𝔡/15` = −1/150 (−1/75) | equals `−𝔡/15` (`1_2:577`) | equality | `un_que_exponent` |
| `τ_Q = 𝔡/30` | 1/300 (1/150) | `0 < τ_Q < 𝔡/15` | `𝔡/15 − τ_Q = 𝔡/30` | `un_cprime` |
| window `N⁻¹W^{𝔡/3}` in I_E(ε₀) | `W^{𝔡/3} ≤ W^{−𝔡/3} lam W^{d/2}` | `lam ≥ W^{−d/2+𝔡}`, `W ≥ 1` | W-exponent `𝔡/3` | `un_window_sub` |
| window in N-scale | exponent in `[−1+𝔠𝔡/3, −1+𝔡/(3d))` = `[−179/180, −89/90)` (`[−59/60, −44/45)`) | `⊂ (−1, 0)` | `𝔠𝔡/3` = 1/180 (1/60) above `−1`; `1/(3d)·𝔡` = 1/90 below `0` | `un_window_N_scale` |
| `W → N` conversion | `W^{−x} ≤ N^{−𝔠x}`, `x ≥ 0` | `N^𝔠 ≤ W` | equality at `W = N^𝔠` | `un_W_neg_le` |
| `θ = W^{−𝔡/6}` in N | `N^{−𝔠𝔡/6}` = `N^{−1/360}` (`N^{−1/120}`) | — | — | — |
| `ℙ(𝓑)` in N | `7 N^{−𝔠(𝔡/15−τ_Q)}`, exponent 1/1800 (1/600); constant `2d+1 = 7` | `W^{τ/2} ≥ 2d+1` (eventually) | absorbed at `W ≥ 7^{2/τ}` | `un_const_absorb` |
| `c'` | `min(𝔠𝔡/6, 𝔠(𝔡/15−τ_Q)) = 𝔠𝔡/30` = 1/1800 (1/600) | `> 0`; `ℙ(𝓑)` binds, not `θ` | `θ` exponent 1/360 vs 1/1800 | `un_cprime` |
| `τ_U` | `≤ c'/(2(C_n'+1))`, `C_n' = 21`: 1/79200 (1/26400) | `−c' + C_n' τ_U ≤ −c'/2` | at `τ_U = c'/44`: `−c' + 21τ_U = −23/79200 ≤ −1/3600` | `un_claim_exponent` |
| `τ_s` (Step 1 floor) | `≤ 𝔠𝔡` = 1/60 (1/20) | `W^{τ_s/8}W^{−2𝔡} ≤ N^{−15τ_s/16}` iff `τ_s ≤ 32𝔠𝔡/(15+2𝔠)` (when `W = N^𝔠`) | exact range 4/115 (16/155) vs used 1/60 (1/20) | `un_step1_floor` |
| `UNL32` arithmetic premises | `σ = δ = min(τ/4,(1−τ)/3)`, `g = N^{−1+τ/4}`, `G = N^{−σ}`, `t = 1−e^{−N^{−1+τ}}`, `q = 1/2`, `E = 0` | `N ≥ 1`, `0<τ<1`, `N^{τ/2} ≥ 2` | at `N = 2097152, τ = 1/2`: `N^{τ/2} = 38.05 ≥ 2`; `N = 65536, τ = 1/8`: `N^{τ/2} = 2` (sharp) | `un_L32_arith` |
| `ρ_sc` on the bulk | `ρ_sc(E) ≥ √(4κ−κ²)/(2π)` on `|E| ≤ 2−κ`, `κ = 1/10` | equality at `|E| = 2−κ` | 0.0994 (edge) vs 0.3183 (`E = 0`) | `un_rhoSC_lower` |
| `UNDens` for `msc`, `E = 0` | `c = 9/100 ≤ Im msc ≤ 1 = C` on `|x| ≤ 1/2`, `0<η≤10`; `Lp = 10000/81` | stated constants of 5d | grid min 0.0988 vs 0.09 | `un_dens_msc_zero` |

Script `python3 pre.py` (exact fractions; the two rows `(𝔠,𝔡) = (1/6,1/10)`, `(1/4,1/5)` of the ticket), verbatim:
```
c=1/6 D=1/10: e0=1/30(<D/2:True,slack 1/60) c_Q=1/60(<e0:True, <D/5:True; slacks 1/60,1/300) QUEexp=-1/150=-D/15:True tauQ=1/300
   c'=1/1800=cD/30:True thetaexp=cD/6=1/360 PBexp=c(D/15-tauQ)=1/1800 | tauU<=1/79200 | (417) exp=-23/79200<=-c'/2:True | dc=1/2<1:True D<d/2:True
   Nwindow in [-179/180,-89/90) subset(-1,0):True | step1 floor sharp tau_s*=32cD/(15+2c)=4/115 (used range cD=1/60, slack 5/276); docstring '16cD/(3+c)'=8/95 (differs:True)
c=1/4 D=1/5: e0=1/15(<D/2:True,slack 1/30) c_Q=1/30(<e0:True, <D/5:True; slacks 1/30,1/150) QUEexp=-1/75=-D/15:True tauQ=1/150
   c'=1/600=cD/30:True thetaexp=cD/6=1/120 PBexp=c(D/15-tauQ)=1/600 | tauU<=1/26400 | (417) exp=-23/26400<=-c'/2:True | dc=3/4<1:True D<d/2:True
   Nwindow in [-59/60,-44/45) subset(-1,0):True | step1 floor sharp tau_s*=32cD/(15+2c)=16/155 (used range cD=1/20, slack 33/620); docstring '16cD/(3+c)'=16/65 (differs:True)
```
Row-by-row match with `docs/reports/T2162-prove.md` (a) lines 29-30 (16 tokens `e0, c_Q, QUEexp, tauQ, theta, c', tau_U, wN` of both rows, each found by `grep -cF`): all 16 return 1.

Finding (docstring, no statement): the docstring of `un_step1_floor` (probe `:995`, "sharp up to `τ_s < 16𝔠𝔡/(3+𝔠)`") is wrong; the inequality as stated holds iff `τ_s ≤ 32𝔠𝔡/(15+2𝔠)` (derivation: `𝔠(2𝔡 − τ_s/8) ≥ 15τ_s/16`; script rows above: 4/115 vs the docstring's 8/95). The lemma statement (`τ_s ≤ 𝔠𝔡`) is true and unchanged; stage 1b should correct the docstring sentence (candidate `T2174a`, comment only).

### (ii) One nondegenerate instance (d = 3, `sz0` at `n = 0`)

Data: `L = 4`, `W = 32`, `lam = 1/64`, `N = (WL)^3 = 2097152`; `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `k = 1`, `E = 0`, `𝒪 =` smooth bump (`bump 0 = 1`, `bump = 0` at `x = 3`). `sz0_values` (`Sizes.lean`): `L 0 = 4 ∧ W 0 = 32 ∧ size 0 = 2097152 ∧ lam 0 = 1/64`. `Sizes.lean:331`: `sz0.Admissible (1/6) (1/10)` is merged. Hypotheses checked: `Admissible` (`W ≥ N^𝔠`, `(eq:WO)`), `un_window_sub` at three values of `lam`, `un_W_neg_le`, `un_step1_floor` at `τ_s = 𝔠𝔡`, window in N-scale, `un_Bctl_le` (`A = 2 ≤ lam²W^d`), `un_L32_arith` at two `(N, τ)`, `un_const_absorb` at `W = 2^200` (asymptotic: not instantiable at `W = 32`, since `32^{1/20} < 7`), `ρ_sc` bounds, `UNDens` for `msc`, the bad event `badY_zero` (zero matrix, eigenbasis = standard basis, `y = 0`).
Command `python3 inst.py`, verbatim:
```
N= 2097152 W^(1/... ) N^c= 11.31370849898476 W>=N^c: True
WO: W^(-d/2+D)= 0.007812500000000002 <=lam= 0.015625 <=1/D= 10.0 True
(eq:WO) lam^2 W^d = 8.0 >= A=2 (W^{2D}=2.0000): True
window_sub lam=0.007812500000000002: 5.352e-07 <= 6.008e-07: True
window_sub lam=0.015625: 5.352e-07 <= 1.202e-06: True
window_sub lam=10.0: 5.352e-07 <= 7.690e-04: True
W^-x<=N^-cx x=1/5: True
step1 floor tau_s=cD=1/60: 0.503623206111852 <= 0.7965710756711335 True
Nscale: 5.169996596819963e-07 <= 5.352316133067002e-07 <= 5.605449229639092e-07
Bctl instance A=2<=lam^2W^d: 8.0
L32 arith N=2097152 tau=1/2: (True, True, True, True, True, 38.05462768008707)
L32 arith N=65536 tau=1/8: (True, True, True, True, True, 2.0)
absorb: 7<=(2^200)^(1/20)= 1024.0000000000005
M_yy= 62.90638712823013  threshold W^(-D/6)= 0.9438743126816935  |mu-E|=0<=N^-1 W^(D/3)= 5.352316133067002e-07 True
support of weights 2d+1 = 7 <= L^d = 64
rho_sc(0)= 0.3183098861837907 lower bd 0.09939223010440974 edge rho_sc(2-k)= 0.09939223010440976
Im msc on |x|<=1/2, 0<eta<=10 (grid): min 0.09878433528724617 >=0.09: True  max 0.999999500000125 <=1: True
Im msc(i eta)/pi at eta=1e-9 vs rho_sc(0): 0.3183098860246357 0.3183098861837907
```
External hypothesis `UNL32` (LSY Thm 2.2, DECISIONS §5), limit computation at `d = 3`: its six arithmetic premises involve only `N` and `τ` (probe `:269-270`: not `d`, `W`, `L`); the printed `L32 arith` lines show them at `(N, τ) = (2097152, 1/2)` and `(65536, 1/8)` (all True), and in general they hold when `N ≥ 1`, `0<τ<1`, `N^{τ/2} ≥ 2` (`un_L32_arith`; threshold `N ≥ 2^{2/τ}`, an "eventually" condition as `size n → ∞`). The regularity premises (`IsRegular32`, `IsFreeConv32`, the density limit) are not instantiated at `sz0`; they are carried by the pin `UNStep1Good` and by `UNDens`, whose density limit `Im msc(iη)/π → ρ_sc(0)` is shown by the last printed line (η = 1e-9) and proved as `un_dens_msc_zero`.

### Verdict per target
1. Sections 1-6 of the probe promoted to `RBM3D/Universality/Pins.lean`: PASS (every exponent row closes with positive slack; no hypothesis set is empty; the one docstring error above does not touch a statement).
2. Registry lines: PASS (no mathematics beyond the structural/borrowed/owed classification of T2162 report (d) 4).
3. Section 7 instances at `sz0`, `n = 0`: PASS (every deterministic hypothesis holds at the stated data; the only "eventually" hypotheses are `N^{τ/2} ≥ 2` and `W^{τ/2} ≥ 7`, discharged at explicit finite values above).
Overall: **PASS**.

## (b) Script output — Mon Oct  5 04:43:25 UTC 2026

Branch `t/T2174`, commit e989d82; files: `RBM3D/Universality/Pins.lean` (new,     1900 lines), `RBM3D/Test/Axioms.lean` (registry lines only).

### b.1 Build
```
$ lake build RBM3D.Universality.Pins 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3328 jobs).
$ lake build   (whole library in the worktree; Pins is not yet a root import, the hub adds it at merge)
Build completed successfully (3946 jobs).
```
### b.2 Registry pre-check (scratch file: `import RBM3D`, `import RBM3D.Universality.Pins`, `#assert_rbm_axioms`; `lake env lean`)
```
axiom audit: 5297 theorems, 1872 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
  RBM.Univ.UNL32: 5 [no certificate]
premises found by scanning: 101 (borrowed 1, owed 79, structural 21).
registry: 2 borrowed + 113 owed + 56 structural; 70 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
non-vacuity certificates: 0 of 115 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
```
Registry diff (`git diff main...t/T2174 -- RBM3D/Test/Axioms.lean`, +/- lines): 1 line removed (`KLPT]` list close), 34 added: `UNL32` in `borrowedProps`; 26 `RBM.Univ.UN*` in `owedProps` (the 15 pins of ticket target 2, the nine rows `UNInfty1Row UNUnivMainRow UNOURow UNEMCTE2Row UNJakUywRow UNClaimRow UNDensBandRow UNTrLocalBandRow UNNormBandRow`, and `UNGreenCorrAll UNNormBound`); `UNDens IsRegular32 IsFreeConv32 InWindow queBadMat UNBadY` in `structuralProps`. The first pre-check run reported exactly `UNGreenCorrAll UNNormBandRow UNTrLocalBandRow UNDensBandRow UNNormBound` as unclassified beyond the ticket list; they are classed owed as in T2162 portmap P.4 (NormBound/NormBandRow owed; the band rows are rows).
```
$ git diff --stat main...t/T2174
 RBM3D/Test/Axioms.lean       |   35 +-
 RBM3D/Universality/Pins.lean | 1900 ++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 1934 insertions(+), 1 deletion(-)
```
### b.3 Axioms
```
$ lake env lean ax.lean   # 139 `#print axioms` lines = the probe section 8 list, on the library module
lines of output:      139; lines that are not 'depends on axioms: [propext, Classical.choice, Quot.sound]': 0
'RBM.Univ.UNBUniv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNUnivDilAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNL32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_core_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_claimAll_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_bUniv_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unBadY_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_dens_msc_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.bump_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.badY_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.inst_bUniv_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.inst_core_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.inst_core_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.inst_claimAll_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.inst_core_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Universality/Pins.lean | wc -l
0
```
### b.4 Script diff against the probe (statements verbatim)
```
$ git show 73b451c:RBM3D/Probe/T2162Pins.lean | head -1899 | diff - RBM3D/Universality/Pins.lean | grep -c "^[<>]"
7
$ ... | diff - Pins.lean   # full output (header lines 16-19 and the docstring of un_step1_floor only)
16c16
< # T2162 probe (UN-D1): the pins of bulk universality `Thm: B_Univ` at `d ≥ 3`
---
> # `RBM3D.Universality.Pins` (UN-01): the pins of bulk universality `Thm: B_Univ` at `d ≥ 3`
18c18,19
< Design probe of ticket T2162 (branch `t/T2162` only, never merged, no root import).  Paper:
---
> Promotion of the UN-D1 design probe of ticket T2162 (`RBM3D/Probe/T2162Pins.lean` at `73b451c`) to
> the library (ticket T2174; statements unchanged).  Paper:
995c996
< convolution step is `τ_s ≤ 𝔠𝔡` (sharp up to `τ_s < 16𝔠𝔡/(3+𝔠)`), RBM2D `τ_s ≤ 𝔠`. -/
---
> convolution step is `τ_s ≤ 𝔠𝔡` (for `W = N^𝔠` the inequality holds exactly for `τ_s ≤ 32𝔠𝔡/(15+2𝔠)`, so `τ_s ≤ 𝔠𝔡` is not the sharp range; paper-delta candidate T2174a, docstring only), RBM2D `τ_s ≤ 𝔠`. -/
```
Probe lines 1900-2041 (section 8, 139 `#print axioms` lines) are not copied into the library file; they are run above.
### b.5 Target statements (extracted by `ext.py` from the file)
```lean
-- Pins.lean:177
def UNBUniv : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        Tendsto (fun n =>
          (∫ ω, kPoint k O E (Sizes.seqXmat_isHermitian sz n ω).eigenvalues ∂(Sizes.seqP sz)) -
          (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))))
          atTop (𝓝 0)
-- Pins.lean:195
def UNUnivDilAt (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
    (∫ ω, kPoint k (fun α => O (rhoSC E' • α)) E' (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
      ∂(gueP d (sz.L n) (sz.W n)))) atTop (𝓝 0)
-- Pins.lean:281
def UNL32 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ n, Idx d (sz.L n) (sz.W n) → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ n in atTop,
      ((sz.size n : ℕ) : ℝ) ^ δ / ((sz.size n : ℕ) : ℝ) ≤ g n ∧
      g n ≤ ((sz.size n : ℕ) : ℝ) ^ (-δ) ∧ G n ≤ ((sz.size n : ℕ) : ℝ) ^ (-δ) ∧
      g n * ((sz.size n : ℕ) : ℝ) ^ σ ≤ t n ∧ t n ≤ ((sz.size n : ℕ) : ℝ) ^ (-σ) * G n ^ 2 ∧
      |E n| ≤ q * G n ∧
      IsRegular32 (v n) (g n) (G n) c C CV ∧ IsFreeConv32 (v n) (t n) (m n) ∧
      Tendsto (fun η : ℝ => (m n ⟨E n, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
      Tendsto (fun n =>
        (∫ ω, kPoint k (fun α => O (ρ n • α)) (E n)
            (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (t n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        (∫ ω, kPoint k (fun α => O (rhoSC (E n) • α)) (E n)
            (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
        atTop (𝓝 0)
-- Pins.lean:584
def UNStep1Good : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))
-- Pins.lean:1147
def UNBadY (lam 𝔡 E : ℝ) (y : Idx d L W) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ), IsOrthoEigenbasis M μ ψ ∧
    ∃ α, |μ α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
      (W : ℝ) ^ (-(𝔡 / 6)) ≤ |unMy d L W lam (ψ α) y|
-- Pins.lean:1320
theorem unBadY_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (hL : 3 ≤ L)
    {lam 𝔡 E : ℝ} (hW : 1 ≤ (W : ℝ)) (h𝔡 : 0 < 𝔡)
    (hlam : (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam) (y : Idx d L W)
    (Mf : Ω → Matrix (Idx d L W) (Idx d L W) ℂ) (p : ℝ≥0∞)
    (hp : ∀ b : Zd d L, μ {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Mf ω)} ≤ p) :
    μ {ω | UNBadY d L W lam 𝔡 E y (Mf ω)} ≤ ((2 * d + 1 : ℕ) : ℝ≥0∞) * p := by
-- Pins.lean:866
theorem un_bUniv_of_rows (rI : UNInfty1Row) (rU : UNUnivMainRow) (rC : UNClaimRow)
    (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow)
    (rT : UNTrLocalBandRow) (rN : UNNormBandRow) :
    UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUELocal → UNGreenCorrAll →
      UNBUniv := by
-- Pins.lean:1455
theorem un_dens_msc_zero : UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) := by
-- Pins.lean:772
theorem un_core_of_rows (h1 : UNInfty1Row) (h2 : UNUnivMainRow) : UNCore := by
-- Pins.lean:849
theorem un_claimAll_of_rows (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
      ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E := by
```
### b.6 Compiled nonempty instances (section 7 of the probe, unchanged; data `sz0`: d = 3, L = 4, W = 32, lam = 1/64, N = 2097152; `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `E = 0`, `k = 1`, `𝒪 = bump`)
```lean
-- Pins.lean:1757
theorem inst_bUniv_band (rI : UNInfty1Row) (rU : UNUnivMainRow) (rC : UNClaimRow) (rE : UNEMCTE2Row)
    (rJ : UNJakUywRow) (rO : UNOURow) (rD : UNDensBandRow) (rT : UNTrLocalBandRow)
    (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand)
    (hQ : UNQueBand) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0
          (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
      atTop (𝓝 0) :=
-- Pins.lean:1773
theorem inst_core_band (hcore : UNCore) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll)
    (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.band sz0) 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
-- Pins.lean:1786
theorem inst_core_ba (hcore : UNCore) (h32 : UNL32) (hGL : UNGUELocal) (hGC : UNGreenCorrAll)
    (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ) (hD : UNDens m E ρ δ)
    (hT : UNTrLocal sz0 (UNModel.ba sz0) m E δ)
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.ba sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.ba sz0) E) (E' : ℝ) (hE' : |E'| < 2) :
    UNUnivDilAt sz0 (UNModel.ba sz0) ρ E E' 1 (bump : (Fin 1 → ℝ) → ℝ) :=
-- Pins.lean:1797
theorem inst_claimAll_band (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNClaimAll sz0 (UNModel.band sz0) 0 :=
-- Pins.lean:1888
theorem inst_core_of_rows (rI : UNInfty1Row) (rU : UNUnivMainRow) (h32 : UNL32) (hGL : UNGUELocal)
    (hGC : UNGreenCorrAll) (hT : UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2))
    (hN : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀)
    (hC : UNClaimAll sz0 (UNModel.band sz0) 0) :
    UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) :=
-- Pins.lean:1721
theorem badY_zero : UNBadY 3 4 32 (1 / 64) (1 / 10) 0 (0 : Idx 3 4 32) 0 := by
-- Pins.lean:1507
theorem bump_nondegenerate :
    (bump : (Fin 1 → ℝ) → ℝ) 0 = 1 ∧ (bump : (Fin 1 → ℝ) → ℝ) (fun _ => 3) = 0 := by
```
Hypotheses left on the instances are other gates' unproved pins and rows (`UNL32`, rows, `UNGUELocal`, `UNGreenCorrAll`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand`, `UNTrLocal`, `UNNormBound`, `UNClaimAll`), as CLAUDE.md §4 step 2 allows; every deterministic hypothesis (`sz0.Admissible (1/6) (1/10)`, the exponent rows, `UNDens` at `msc`, `badY_zero`, window/N-scale/Bctl inequalities) is discharged by the named `inst_*` theorems of section 7 (list: `grep -nE "^theorem (inst_|badY_zero|bump_nondegenerate)" Pins.lean`, lines 1507-1888, 30 theorems).
### b.7 Name clash
```
$ python3 clash.py   # public theorem/def/structure names of Pins.lean vs `^(theorem|def|...) RBM.Univ.<name>` and `namespace RBM.Univ` in every other RBM3D/**/*.lean (Axioms.lean excluded for the registry names)
139 public names in Pins.lean; hits: 0
```
Ports: none new in this ticket (the file is the T2162 probe, which carries its own RBM2D citations at `c9a24cf` in docstrings); `RBM1D`/`RBM2D` were not read or touched; no diff-stat applies.

### b.8 Narrative
1. Pins.lean = probe lines 1-1899 (imports, namespace `RBM.Univ`, sections 1-7); only the module docstring (probe wording replaced by the module name) and one docstring sentence of `un_step1_floor` differ (b.4).
2. The probe's section 8 (`#print axioms` lines) is run, not copied, so the library file has no `#print`.
3. Registry: see b.2; the pre-check passes (`#assert_rbm_axioms`, exit 0 with the output above).
4. Per CONTROL/ticket: no statement changed, no hypothesis added, no signature changed; the root import is left to the hub.

## (c) Verified Mathlib names used
None new: no Mathlib name was introduced; the file compiles unchanged from the probe (imports `Mathlib.Analysis.Calculus.BumpFunction.Basic`, `.FiniteDimension` as in the probe).

## (d) Open issues and paper-delta candidates
1. **T2174a** (docstring only, no statement): the probe docstring of `un_step1_floor` said the range `τ_s ≤ 𝔠𝔡` is "sharp up to `τ_s < 16𝔠𝔡/(3+𝔠)`". Preflight (a) shows the inequality at `W = N^𝔠` holds iff `τ_s ≤ 32𝔠𝔡/(15+2𝔠)` (4/115 at `(1/6,1/10)`; 16/155 at `(1/4,1/5)`), so the sentence was wrong; corrected in the docstring (Pins.lean:992-996). The lemma statement is unchanged and true.
2. Registry observation: the pre-check logs the registered `RBM.Univ` names `InWindow IsFreeConv32 IsRegular32 UNApriori UNBadY UNBUniv UNClaim417 UNDens UNEMCTE2 UNGreenCorr UNJak UNOUDiag UNOUQUE UNStep1Good UNUyw` among "registered premises that carry nothing yet" (the scan finds no theorem of the development taking them as a hypothesis). Not an error; unchanged by this ticket.
3. No other open issue; every statement of the probe is promoted as is.
