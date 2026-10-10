Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 10:06:42 UTC 2026

Targets (mathematics only). **G:** the three owed pins `BAGbEXPii/ij/av` (`BA/Step1Boot.lean:108,116,123`): for all `κ,ε,𝔡,ε₀>0`, `BAFlow sz κ ε 𝔠 𝔡 z` (`BA/FlowPins.lean:546` = `Admissible 𝔠 𝔡` ∧ `∀n, BAdom κ ε (z n)`), `0 ≤ t n ≤ BAflowT0 sz z n` (`FlowPins.lean:537`), the event form of `lem_GbEXP_BA` (`7_8:1916-1946`); `av` carries `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` (`Step1Boot.lean:97`). **E:** `sum_res_1/_2_NAL/_2`, `sum_decay_nonzero` (`A:88-220`, `3_5:1639-1666`) at real `t ∈ [0,1)`.

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `d` | 3 | `d ≥ 3` (`A:80-90`, d=3 borderline in `eq:latticesum_d3`, `A:194`) | none needed |
| 2 | `𝔠` (`Bandwidth`), `𝔡` (`WO`, `1_2:363`) | `1/6`, `1/10` | `W ≥ N^𝔠`; `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` (`Sizes.lean:164,168`) | n=0: `32 ≥ 11.31`; `7.8e-3 ≤ 1/64 ≤ 10` |
| 3 | `g²W^d ≥ W^{2𝔡}` (from row 2) | `g=1/64`: `8.0 ≥ 32^{0.2}=2.0` | needed for `B`-type factors in E (`Sizes.lean:193`) | factor 4 |
| 4 | `κ`, `ε` of `BAdom` (`MFixedPoint.lean:435`) | `κ ≤ Im m(z,g)`, `N^{-1+ε} ≤ Im z ≤ 1` | `κ` depends on `g`: `Im m = 0.8325 (g=1/64), 0.3777 (g=1), 0.2620 (g=10)` at `Im z` of the instances; so `κ=1/2` is impossible at those `z` for `g ≥ 1`, `κ=1/4` is used for `g=1,10` | A: `0.8325 ≥ 0.5`; B2: `0.2620 ≥ 0.25` |
| 5 | horizon `t₀ = BAflowT0 = Im m/(Im m+Im z)` | `0.6937 (n=0), 0.6944 (n=1,2)`, limit `25/36 = 0.69444` along `sz0` | `0 ≤ t ≤ t₀ < 1`; `1-t₀ = Im z/(Im m+Im z) ≥ N^{-1+ε}/(Im m+1)` | `1-t₀ = 0.306` vs `1.1e-6` |
| 6 | shift `g₀ = √t₀ g`, `E = BAflowE` (`MFixedPoint.lean:280`), `m₀ = m/√t₀` | `g₀ = 0.0130 ≤ g = 0.0156 ≤ Λ = 𝔡⁻¹ = 10` | `BAReal(g₀,κ,E,m₀)` (self_m at real `E`, `κ ≤ Im m₀`) via `BAflow_real` (`GreenSchur.lean:59`); `BAMfine_decay` needs `0 < g₀ ≤ Λ` | `Im m₀ = 0.9995 ≥ 0.5` |
| 7 | Ward `Σ_b|M_ab|² = 1` (`7_8:1870`), `‖M‖_max ≤ 1` (`BAMfine_norm_le_one`, `GreenSchur.lean:105`) | row error `≤ 2e-15` | exact identity | machine precision |
| 8 | decay of `M` (`Mbound_AO2`, `7_8:1902`): Lean `BAMfine_decay` (`GreenSchur.lean:124`) `|M_ab| ≤ c⁻¹e^{-c|a-b|}`, `c = min(log(1+κ/(4dΛ)), κ/2)` (`CombesThomas.lean:45`) | `c = 0.004158` (`κ=1/2,d=3,Λ=10`); `c = 0.002081` (`κ=1/4`) | uniform in `n` and in `g₀ ≤ Λ`; the paper's `c_λ` of `(GijGEX_BA)` (`7_8:1942`) is at most this | max ratio `|M|/(c⁻¹e^{-cr}) = 4.2e-3 ≤ 1` |
| 9 | `Mbound_AO` regime (`7_8:1888-1891`): `C = 16d²/κ³` (`CombesThomas.lean:42`) | `C=1152` (`κ=1/2`); needs `g₀ < (2C)⁻¹ = 4.34e-4` | regime split of the paper; not needed in Lean (row 8 covers all `g₀ ≤ Λ`) | n=0: `1.3e-2` violates, n=1: `2.0e-4` holds; no gap |
| 10 | **RBSO1D premise `g ≤ W^{-ε}`** (`7_8:1948`) | holds along `sz0` (`g = W^{-6/5}`) | `BAFlow` only gives `g ≤ 𝔡⁻¹ = 10`; instances B1 (`g=1`), B2 (`g=10`) satisfy every hypothesis of the pins and violate it (`W^{-1/10} = 0.707`) | **no slack**: the paper claims "verbatim" for the range `W^{-ε} < g ≤ 𝔡⁻¹` with text of `[RBSO1D] L6.1` not in the repo (GE3 gap candidate) |
| 11 | `ε₀` and the window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` (`7_8:1917`; `Step1Boot.lean:97`) | `ε₀ ∈ {1/10, 1}` | nonempty iff `ε₀ ≤ d/2 = 3/2`; for `ε₀ > 3/2` `BAGavLGEX` is vacuous in `Ψ` | `W^{d/2-ε₀}`: 128.0 (`ε₀=0.1`), 5.66 (`ε₀=1`), `n=0` |
| 12 | `≺` constants: `τ > 0`, `D > 0` arbitrary (`StochDomAt`, `Defs/StochDomAt.lean:61`), `∀ᶠ n` | none to fix | `W^{-D}` in `(GijGEX_BA)` is `∀ D` | — |
| 13 | E: scale `ℓ_t = min(max(g|1-t|^{-1/2},1), L)` (`1_2:1122`); `(1-s)ℓ_s² ≍ g²+|1-s|` for `s ≤ 1-g²/L²` (`A:138`) | n=0 instance below: `ℓ_{t₀} = 4 = L`, `ℓ_s = 2.21` | `(1-t)/(1-s) ≥ W⁻¹` (`A:139`); `1-s ≥ g²/L²` | `0.0409 ≥ 0.03125`; `0.830 ∈ [1/2,1]` |
| 14 | E: lattice sum `≲ log L / R^{d-3}`, absorbed by `log L ≤ W^{ε_E}` (`A:194-198`, d = 3 only) | `ε_E = 1/10` | holds only for large `n` along `sz0` (`W=(2(n+1))^5`, `L=4(n+1)`) | n=0: `1.386 ≤ 1.414` (2%); n=1: `2.079 > 2.000` (fails); n=2 fails; `n ≥ 3` holds (see output) |
| 15 | E: `W^{(n+5)ε_E}`-type losses, `sum_res_2` prefactor `((g²+|1-s|)/(g²+|1-t|))^n` | `(n_loop ≥ 1)`, `C_n` constants | `ε_E` small, fixed before `∀ᶠ` | n=0: factor `1.195` at the instance |

### (ii) One concrete nondegenerate instance

`d=3`, `sz0` (`Sizes.lean:260`: `L=4(n+1)`, `W=(2(n+1))^5`, `g=(2(n+1))^{-6}`), `n=0`: `L=4, W=32, N=(WL)³=2097152, g=1/64`; `(κ,ε,𝔠,𝔡)=(1/2,1/10,1/6,1/10)`; `Ψ^{(B)}` = adjacency of `Z_L³`, periodic `ℓ¹` distance (`zdistD`); `z = w - m_S(w)`, `w=1.2i` (`zS`); `m` solves `(self_m)` by damped iteration; `M=(g₀Ψ-E-m₀)⁻¹`. G-instances A (`g=1/64`), B1, B2 (`g=1, 10`, same `L,W`, `κ=1/4`), and the limit rows `n=1,2`. `t ∈ {0, t₀/2, t₀}`, `ε₀ ∈ {1/10, 1}`, `Ψ` the geometric mean of the window.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2378/inst2.py`
```
[A sz0 n=0] L=4 W=32 N=2097152 g=0.01562 kappa=0.5 z=0.3675i Im m=0.8325 t0=0.6937 g0=0.01301 E=1.0e-18 Im m0=0.9995 selfres=0e+00/2e-16
   Admissible True (W=32>=N^(1/6)=11.31; W^(-d/2+dd)=7.81e-03<=g<=10); BAdom True (N^(-1+eps)=2.0e-06<=Im z<=1); t in [0.0, np.float64(0.3469), np.float64(0.6937)] <= t0: True
   RBSO1D premise g<=W^-eps: 1.56e-02<=0.707 True; Mbound_AO regime g0<1/(2C), C=1152: 1.30e-02<4.34e-04 False
   Ward max|sum_b|M_ab|^2-1|=2e-15; max|M_ab|=0.9995; BAMfine_decay (rate=0.004158) max ratio=4.16e-03<=1 True
   eps0=0.1: Psi in [5.524e-03,7.071e-01], Psi=6.250e-02;   eps0=1.0: Psi in [5.524e-03,3.125e-02], Psi=1.314e-02;
[B1 g=1] L=4 W=32 N=2097152 g=1 kappa=0.25 z=0.8223i Im m=0.3777 t0=0.3148 g0=0.561 E=-9.6e-17 Im m0=0.6732 selfres=0e+00/1e-16
   Admissible True (W=32>=N^(1/6)=11.31; W^(-d/2+dd)=7.81e-03<=g<=10); BAdom True (N^(-1+eps)=2.0e-06<=Im z<=1); t in [0.0, np.float64(0.1574), np.float64(0.3148)] <= t0: True
   RBSO1D premise g<=W^-eps: 1.00e+00<=0.707 False; Mbound_AO regime g0<1/(2C), C=9216: 5.61e-01<5.43e-05 False
   Ward max|sum_b|M_ab|^2-1|=1e-15; max|M_ab|=0.6732; BAMfine_decay (rate=0.002081) max ratio=1.40e-03<=1 True
   eps0=0.1: Psi in [5.524e-03,7.071e-01], Psi=6.250e-02;   eps0=1.0: Psi in [5.524e-03,3.125e-02], Psi=1.314e-02;
[B2 g=10] L=4 W=32 N=2097152 g=10 kappa=0.25 z=0.9380i Im m=0.2620 t0=0.2183 g0=4.672 E=-9.8e-16 Im m0=0.5607 selfres=0e+00/1e-15
   Admissible True (W=32>=N^(1/6)=11.31; W^(-d/2+dd)=7.81e-03<=g<=10); BAdom True (N^(-1+eps)=2.0e-06<=Im z<=1); t in [0.0, np.float64(0.1092), np.float64(0.2183)] <= t0: True
   RBSO1D premise g<=W^-eps: 1.00e+01<=0.707 False; Mbound_AO regime g0<1/(2C), C=9216: 4.67e+00<5.43e-05 False
   Ward max|sum_b|M_ab|^2-1|=1e-15; max|M_ab|=0.5607; BAMfine_decay (rate=0.002081) max ratio=1.17e-03<=1 True
   eps0=0.1: Psi in [5.524e-03,7.071e-01], Psi=6.250e-02;   eps0=1.0: Psi in [5.524e-03,3.125e-02], Psi=1.314e-02;
[sz0 n=1] L=8 W=1024 N=549755813888 g=0.0002441 kappa=0.5 z=0.3667i Im m=0.8333 t0=0.6944 g0=0.0002035 E=0.0e+00 Im m0=1.0000 selfres=0e+00/3e-16
   Admissible True (W=1024>=N^(1/6)=90.51; W^(-d/2+dd)=6.10e-05<=g<=10); BAdom True (N^(-1+eps)=2.7e-11<=Im z<=1); t in [0.0, np.float64(0.3472), np.float64(0.6944)] <= t0: True
   RBSO1D premise g<=W^-eps: 2.44e-04<=0.500 True; Mbound_AO regime g0<1/(2C), C=1152: 2.03e-04<4.34e-04 True
   Ward max|sum_b|M_ab|^2-1|=1e-15; max|M_ab|=1.0000; BAMfine_decay (rate=0.004158) max ratio=4.16e-03<=1 True
   eps0=0.1: Psi in [3.052e-05,5.000e-01], Psi=3.906e-03;   eps0=1.0: Psi in [3.052e-05,9.766e-04], Psi=1.726e-04;
[sz0 n=2] L=12 W=7776 N=812479653347328 g=2.143e-05 kappa=0.5 z=0.3667i Im m=0.8333 t0=0.6944 g0=1.786e-05 E=-2.4e-21 Im m0=1.0000 selfres=0e+00/2e-16
   Admissible True (W=7776>=N^(1/6)=305.47; W^(-d/2+dd)=3.57e-06<=g<=10); BAdom True (N^(-1+eps)=3.8e-14<=Im z<=1); t in [0.0, np.float64(0.3472), np.float64(0.6944)] <= t0: True
   RBSO1D premise g<=W^-eps: 2.14e-05<=0.408 True; Mbound_AO regime g0<1/(2C), C=1152: 1.79e-05<4.34e-04 True
   Ward max|sum_b|M_ab|^2-1|=4e-16; max|M_ab|=1.0000; BAMfine_decay (rate=0.004158) max ratio=4.16e-03<=1 True
   eps0=0.1: Psi in [1.458e-06,4.082e-01], Psi=7.716e-04;   eps0=1.0: Psi in [1.458e-06,1.286e-04], Psi=1.369e-05;
```
E-instance (rows 13-15): `z = N^{-1+ε}i` (`Re z = 0`), `ε_E=1/10`, `s` with `1-s ≤ W(1-t₀)`. Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2378/inst3.py`
```
[E n=0] L=4 W=32 g=1.562e-02 N=2097152 Im z=N^(-1+eps)=2.044e-06 Im m=0.9993 1-t0=2.046e-06 g^2/L^2=1.526e-05 (1-t0<=g^2/L^2: True)
   l_t=4.000 (=L: True); s: 1-s=5.0e-05, 1-s>=g^2/L^2 True, l_s=2.210; (1-t)/(1-s)=4.091e-02 >= 1/W=3.125e-02: True; s<=t: True
   (1-s) l_s^2/(g^2+1-s)=0.830 in [1/2,1]; (g^2+1-s)/(g^2+1-t)=1.195; l_t^2/l_s^2=3.277
   log L=1.386 <= W^eps=1.414: True
[E n=1] L=8 W=1024 g=2.441e-04 N=549755813888 Im z=N^(-1+eps)=2.715e-11 Im m=1.0000 1-t0=2.715e-11 g^2/L^2=9.313e-10 (1-t0<=g^2/L^2: True)
   l_t=8.000 (=L: True); s: 1-s=2.0e-08, 1-s>=g^2/L^2 True, l_s=1.726; (1-t)/(1-s)=1.358e-03 >= 1/W=9.766e-04: True; s<=t: True
   (1-s) l_s^2/(g^2+1-s)=0.749 in [1/2,1]; (g^2+1-s)/(g^2+1-t)=1.335; l_t^2/l_s^2=21.475
   log L=2.079 <= W^eps=2.000: False
n=2: log L=2.485 <= W^(1/10)=2.449: False
n=3: log L=2.773 <= W^(1/10)=2.828: True
n=4: log L=2.996 <= W^(1/10)=3.162: True
n=5: log L=3.178 <= W^(1/10)=3.464: True
n=10: log L=3.784 <= W^(1/10)=4.690: True
```
External-input limit check (TEAM §8 l.14). The unmerged inputs (stage-K outputs `STKboundgL`, `BAKbound`; `[RBSO1D] L6.1`; `A:88-220` as written) enter the probe as hypotheses; the data they are evaluated at are the `sz0` rows `n=0,1,2` above: `t₀ → 25/36`, `Im m₀ → 1`, `g₀ → 0` (`1.3e-2, 2.0e-4, 1.8e-5`), `Ward` error `≤ 2e-15`, `BAMfine_decay` ratio constant `4.16e-3`, `Admissible` and `BAdom` true for every `n` printed. The `≺` statements are asymptotic, so a finite-`n` instance checks the hypotheses and constants, not the conclusions.

### Verdicts
* **G, pins `BAGbEXPii`, `BAGbEXPij`, `BAGbEXPav`: PASS** (hypotheses satisfiable at nondegenerate data; instances A, B1, B2; no exponent obstruction). Two points for the design, neither a failure of the hypothesis set: (1) row 10: the premise `g ≤ W^{-ε}` of `[RBSO1D] L6.1` is not implied by `BAFlow` (instances B1, B2), and the cited text is not in the repo (`paper/tex/Jun.bib:168` only), so GE3 for `lem_GbEXP_BA` must name this gap or give the argument for `W^{-ε} < g ≤ 𝔡⁻¹`; (2) shape: `BAGijGEX` (`Step1Boot.lean:88-94`) has the band right side `FlowFM.gexRHS` (`Step1Boot.lean:59-66`: window `|a'-a|_∞ ≤ 1` sums of 2-loops `+ W^{-d}1_{|a-b|≤1}`, as `3_5:24`), whereas `(GijGEX_BA)` (`7_8:1942`) has `Σ Φ_t e^{-c_λ(|a'-a|+|b'-b|)} + Ψ_t e^{-c_λ|a-b|} + W^{-D}` on `(G_t-M)_{xy}`; the two forms are not syntactically comparable, to be settled in GE2/GE3 (not decided here).
* **E, `sum_res_1`, `sum_res_2_NAL`, `sum_res_2`, `sum_decay_nonzero`: PASS** at the mathematical level (rows 13-15, E-instance: `ℓ_t = L` regime and the intermediate regime `1 < ℓ_s < L` both exercised at `n=0`). One constraint for the design: row 14, `log L ≤ W^{ε_E}` fails at `n = 1, 2` of `sz0` for `ε_E = 1/10`, so the E statements must be eventual in `n` (`∀ᶠ`) with the order of quantifiers of the paper (`ε` fixed first, then `N` large).
* Overall: **PASS**.

### (b) Script output — assembled Sat Oct 10 11:09:08 UTC 2026 (scratchpad `S = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2378`; scripts `*.py`, `*.sh`, `*.lean` there, not in the repository; each block is the verbatim output of the command shown or named; counts are `wc -l`)
**B1 build and acceptance** (probe on branch `t/T2378`, commits `67dfde8`, `f2c609a`; the reports are in the main worktree, so the branch diff lists the probe)
```
Sat Oct 10 11:00:53 UTC 2026
$ lake env lean RBM3D/Probe/T2378Pins.lean; echo "exit=$?"; wc -l RBM3D/Probe/T2378Pins.lean
exit=0
     367 RBM3D/Probe/T2378Pins.lean
$ touch RBM3D/Probe/T2378Pins.lean; lake build RBM3D.Probe.T2378Pins 2>&1 | grep -E "T2378Pins|error"; lake build RBM3D.Probe.T2378Pins 2>&1 | tail -1
Build completed successfully (3778 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2378Pins.lean
0
$ git log -1 --format=%h; git status --short | wc -l; git diff --stat main...t/T2378
f2c609a
       0
 RBM3D/Probe/T2378Pins.lean | 367 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 367 insertions(+)
```
**B2 axioms** (`bash S/mkax.sh`: `#print axioms` of the 31 declarations of the probe, grouped by the printed axiom set)
```
exit=0
31 declarations: [propext, Classical.choice, Quot.sound]
  BAGbEXP BAGt_eq_green ba_G_data ba_M_decay ba_av_window inst_BAGbEXP BAMfine_diag BAMfine_block_zero BAX BALDEin BALDEin_diag BAFlow_not_small BAuKer BAUN BAEKSumNdecay BAEKSumDecay1 BAEKSumDecayNAL BAEKSumDecay2 BAEKSumDecayNonzero BAuKer_eq_one_add BAuKer_convex gI EI mI AI AI_fastDecay inst_BAEKSumDecay1 inst_ba_M_decay inst_BAMfine_block_zero inst_BALDEin_diag inst_BAuKer_convex
```
**B3 statements** (`S/extract2.py`: `lines: text`, definitions in full, theorems up to `:=`; the three owed pins are read from the merged `BA/Step1Boot.lean`)
```
$ python3 extract2.py BAGbEXP BAFlow_not_small BALDEin BAX BAuKer BAUN BAEKSumNdecay BAEKSumDecay1 BAEKSumDecayNAL BAEKSumDecay2 BAEKSumDecayNonzero   # probe: lines a-b, text; theorems up to :=
40-40: def BAGbEXP (d : ℕ) : Prop := BAGbEXPii d ∧ BAGbEXPij d ∧ BAGbEXPav d
136-138: def BAX {d : ℕ} (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => seqHflow (sz.withLam 0) n t ω i j
143-164: def BALDEin (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Green.OffPair d (sz.L n) (sz.W n)) (fun n u ω => Green.ldeRowLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω)) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) (fun n u ω => Green.ldeRowRHS (svar d (sz.L n) (sz.W n) 0) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) ∧ Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Green.OffPair d (sz.L n) (sz.W n)) (fun n u ω => Green.ldeColLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω)) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) (fun n u ω => Green.ldeColRHS (svar d (sz.L n) (sz.W n) 0) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) ∧ Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n)) (fun n i ω => Green.ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω)) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) (svar d (sz.L n) (sz.W n) 0) (t n) i) (fun n i ω => Green.ldeQuadRHS (svar d (sz.L n) (sz.W n) 0) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) i) ∧ Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n)) (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω) i i‖ ^ 2) (fun n i _ => svar d (sz.L n) (sz.W n) 0 i i)
183-189: theorem BAFlow_not_small : ∃ (sz : Sizes 3) (z : ℕ → ℂ), BAFlow sz (9 / 10) (1 / 2) (1 / 9) (1 / 2) z ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ¬ ∀ᶠ n in atTop, sz.lam n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₁)
198-199: def BAuKer (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (s t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ := (1 - (s : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * BATheta d L g E m t σ₁ σ₂
202-204: def BAUN (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) {n : ℕ} (σ : Fin n → Bool) (s t : ℝ) (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ := fun a => ∑ b : Fin n → Zd d L, (∏ i, BAuKer d L g E m s t (σ i) (σ (finRotate n i)) (a i) (b i)) * A b
208-211: def BAEKSumNdecay (d n : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 2 ≤ n → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ A : (Fin n → Zd d L) → ℂ, ‖BAUN d L g E m σ s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖
214-221: def BAEKSumDecay1 (d n : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A → ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * (ellT L g t ^ 2 / ellT L g s ^ 2) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
224-231: def BAEKSumDecayNAL (d n : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ σ : Fin n → Bool, (∃ k, σ k = σ (finRotate n k)) → ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A → ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (n - 1) * ‖A‖ + W ^ (-D + C)
235-242: def BAEKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A → EKSumZero A → ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)
245-250: def BAEKSumDecayNonzero (d n : ℕ) (Λ κ : ℝ) : Prop := 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ s t : ℝ, 0 ≤ s → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s → s ≤ t → t < 1 → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩ BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : Finset (Fin n), (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) → ∀ 𝒜 : (Fin n → Zd d L) → ℂ, ‖zeroModeSet d L A (BAUN d L g E m σ s t 𝒜)‖ ≤ C * ‖𝒜‖
$ the three owed pins (merged, BA/Step1Boot.lean:108-123), extracted the same way (statements up to the first ":= ")
108-112: def BAGbEXPii (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z t ε₀
116-120: def BAGbEXPij (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z t ε₀
123-127: def BAGbEXPav (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGavLGEX sz z t ε₀
```
**B4 compiled nonempty instances** (`S/extract2.py`; the proofs are applications of the pins and of the theorems at `sz0`, `n = 0`)
```
$ python3 extract2.py inst_BAGbEXP inst_BAEKSumDecay1 inst_BALDEin_diag   # statements, cut at 330 characters (also compiled: inst_BAMfine_block_zero, inst_ba_M_decay, inst_BAuKer_convex, an `example` of ba_G_data: probe 326-366)
99-111: theorem inst_BAGbEXP (h : BAGbEXP 3) : BAGiiGEX SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10) ∧ BAGijGEX SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10) ∧ BAGavLGEX SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10)
301-321: theorem inst_BAEKSumDecay1 (h : BAEKSumDecay1 3 2 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧ ‖BAUN 3 (SizesInst.sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) * (ellT (SizesInst.sz0.L 0) gI (1 / 2) ^ 2 / ellT (SizesInst.sz0.L 0) gI 0 ^ 2) * ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ 2 * ‖AI‖ + (16 : ℝ
352-358: theorem inst_BALDEin_diag : Path.PerTimeDomAt (Sizes.seqP (SizesInst.sz0.withLam 0)) SizesInst.sz0.size (U
$ sed -n 103,105p RBM3D/Probe/T2378Pins.lean   # inst_BAGbEXP, first of the three pins applied (t = 1/2 <= T0, eps0 = 1/10; every deterministic hypothesis discharged by norm_num and the merged flow_sz0, half_lt_t0)
  ⟨h.1 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) SizesInst.sz0 FlowPinsInst.zSeq
      FlowPinsInst.flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le) (1 / 10)
      (by norm_num),
$ sed -n 318,321p RBM3D/Probe/T2378Pins.lean   # inst_BAEKSumDecay1: the pin applied at L = sz0.L 0, g0, W = 16, eps = 1/2, D = 2, s = 0, t = 1/2, BAReal from BAflow_real, A = delta_0
  refine ⟨C, hC, H (SizesInst.sz0.L 0) (SizesInst.sz0.three_le_L 0) gI hg hg1 16 (1 / 2) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [h16]) 0 (1 / 2) le_rfl (by norm_num) (by rw [hL]; nlinarith) (by norm_num) EI mI
    (FlowPinsInst.flow_sz0 |> BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq <| 0)
    ![true, false] AI AI_fastDecay⟩
```
**B5 name clash and ports** (`bash S/b5.sh`)
```
$ NAMES=$(grep -oE "^(noncomputable |private )*(theorem|def|structure|abbrev) +[^ (:{\[]+" RBM3D/Probe/T2378Pins.lean | awk '{print $NF}'); echo $NAMES | wc -w
      31
$ for n in $NAMES; do grep -rnE "^\s*(private |noncomputable |protected )*(theorem|lemma|def|abbrev|structure|inductive|instance) +([A-Za-z0-9_.]*\.)?$n( |$|\(|:)" RBM3D --include="*.lean" | grep -v "^RBM3D/Probe/T2378Pins.lean"; done | wc -l
       0
$ grep -rn T2378 RBM3D --include="*.lean" | grep -v "^RBM3D/Probe/T2378Pins.lean" | wc -l
       0
$ grep -c "RBM1D\|RBM2D" RBM3D/Probe/T2378Pins.lean
0
```
**B6 GE1 evidence** (`python3 S/ge1rows.py table`; `S/ge1rows.py stmt_tokens`; the greps; `python3 S/consumers2.py G`, last line; `python3 S/facts.py`, first and last line; the output of `S/cons_names.py` is in design §1). The segment list is in design §1 (verbatim output of `ge1rows.py segments`); class = a reading of the statements, not compiled.
```
file                     lines   H+I     R     G     T     X
Green/EntryCore           1352   304   418     0   630     0
Green/EntryDom            1628   399   305    53   871     0
Green/LDE                 1404   319   435   650     0     0
Green/LDEQuad             1049   210   839     0     0     0
Green/LDEQuadMom           977   258   719     0     0     0
Green/LDEQuadT            1200   245   955     0     0     0
Green/RowIndep            1595   221  1085   289     0     0
Green/FlucVanish          1613   342  1115   156     0     0
Green/FlucIter            1085   345   714    26     0     0
Green/FlucIterGain        1288   403   736   149     0     0
Green/MinorGoodLe         1326   385     0   749   192     0
Green/MinorDiff           1371   551   325    65   430     0
Green/MinorDiffCond       1418   593   254     0   571     0
Green/CondDom             1458   719   529     0   210     0
Green/IBP                 1687   379     0  1024   284     0
Green/IBPPoly             1157   127   348   682     0     0
Green/IBPRem               815   348     0     0   467     0
Green/LocalLaw            1255   382     0     0   873     0
Green/FlucThreshold       1295   440   721     0   134     0
Green/GbEXP               1124   387   108   144   485     0
Green/Pins                1643   280    52   317   742   252
Green/Stability            459   106     0     0   353     0
Evolution/XiPins           485    86     0     0   399     0
Evolution/SumDecay         631   145   217    68   201     0
Evolution/SumDecayZero    1746   263   802     0   681     0
Evolution/Nonzero          227    67     0     0   160     0
Evolution/Pins             418   236    75     5   102     0
Evolution/Prec             657   252    87    90   228     0
subtotal Green/          28199  7743  9658  4304  6242   252
subtotal Evolution/       4164  1049  1181   163  1771     0
TOTAL                    32363  8792 10839  4467  8013   252   (non-H/I lines 23571)

outside the list: Kernel/Evolution    685 lines: H+I 38, R 264, G 0, T 383
outside the list: Kernel/SumDecay     708 lines: H+I 40, R 272, G 75, T 321
declarations of the non-H/I segments (theorem, lemma, def, abbrev, structure), by class; statement = text up to `:=`:
  class R:  682 declarations (106 private) | statement mentions (m)   21 ( 3%) (h)   21 ( 3%) (p)   27 ( 3%)
  class G:  248 declarations ( 63 private) | statement mentions (m)   50 (20%) (h)   50 (20%) (p)   20 ( 8%)
  class T:  333 declarations ( 94 private) | statement mentions (m)  108 (32%) (h)   26 ( 7%) (p)   24 ( 7%)
  class X:   19 declarations (  5 private) | statement mentions (m)   12 (63%) (h)    1 ( 5%) (p)    0 ( 0%)
  total 1282 declarations, 268 private
$ grep -c "‖m‖ = 1\|‖m n‖ = 1\|‖mE" <the 22 Green files and the 6 Evolution files of the table>   # nonzero counts
Green/CondDom.lean:1 Green/EntryCore.lean:13 Green/EntryDom.lean:1 Green/IBPRem.lean:1 Green/LocalLaw.lean:1 Green/MinorGoodLe.lean:3 Green/Pins.lean:1 Green/Stability.lean:2 Evolution/XiPins.lean:3 Evolution/SumDecay.lean:2 Evolution/SumDecayZero.lean:1 Evolution/Nonzero.lean:4 Evolution/Pins.lean:8 Evolution/Prec.lean:1 
$ grep -ln "KLK\|STKbound\|Kbound\|KLoop\|IsKLoop\|BAKsol\|BAKloop\|STKloop" Green/*.lean Evolution/{XiPins,SumDecay,SumDecayZero,Nonzero,Pins,Prec}.lean Kernel/{Evolution,SumDecay}.lean
Green/GbEXP.lean
$ grep -n "KLK\|STKbound\|Kbound\|KLoop\|IsKLoop\|STKloop" Green/GbEXP.lean | cut -c1-100
835:third clause of `lem_GbEXP`, and `STKbound`, `STLK`, `STLocalMax` at `s` of Step 1.  Every
970:discharged; `STKbound`, `STLK`, `STLocalMax` at `s` are other gates' pins (the ST-6 chain).  Bot
972:private theorem gbEXP_inst_stStep1 (hK : STKbound sz0 (STflowE z0))
$ grep -rln "BAWinBulk\|BAmWindow\|BAwindow_" --include="*.lean" . | grep -v Probe
Test/Axioms.lean BA/Step1Fam.lean BA/Step1Trivial.lean BA/Step1.lean BA/CouplingWindow.lean BA/Step1Boot.lean 
$ grep -rln "prop5Decay_holds\|prop5Short_holds\|prop6Diff1_holds\|prop8ZeroMode_holds" Green Evolution Kernel
Green/Stability.lean Evolution/MeanFar.lean Evolution/Pins.lean Evolution/CltFar.lean Evolution/SumDecayZero.lean Evolution/SumDecay.lean Evolution/CltMoments1.lean Evolution/Nonzero.lean Evolution/Prec.lean Evolution/XiPins.lean 
$ python3 S/consumers2.py G | tail -1
TOTAL                         185      74         10
$ python3 S/facts.py | sed -n "1p;$p"   (columns: bulk t1 adm zim m1 kst lam)
file                      bulk    t1   adm   zim    m1   kst   lam
TOTAL                       39   266   132   444   306    39   196
```
**B7 row table** (`python3 S/rows.py measured | groups | rows`; segments of B6; TW 0.73/0.97/1.61, NW 0.85/1.37/2.10, G in place g 0.15/0.24/0.30 + 15 lines per outside name + BA instance 0.15/0.25/0.40, assumptions with measured end points)
```
measured BA / band line ratios (wc -l), merged twins:
  BA/ConArg         1982 /   876 (Induction/ConArg        ) = 2.26
  BA/Step1           784 /   750 (Induction/Step1         ) = 1.05
  BA/Step1Setup     1279 /  1554 (Induction/Step1Setup    ) = 0.82
  BA/Prop5          1479 /  1399 (Propagator/Prop5Hold    ) = 1.06
  BA/PropUnit       1119 /  1008 (Propagator/PropUnit     ) = 1.11
  BA/Prop5Short      814 /   506 (Propagator/Prop5Short   ) = 1.61
  BA/Prop6Path      1178 /   560 (Propagator/Prop6Hold    ) = 2.10
  BA/KHeat+Tail+Diff  3963 /  2152 (HeatProduct+LaplaceGauss     ) = 1.84
group              G lines names | in place lo/c/hi | twin lo/c/hi | choice
A LDE inputs          1621    28 |   906  1214  1554 |  1183  1572  2610 | in place
B FA machinery        1145    44 |  1004  1221  1462 |   836  1111  1843 | twin
C IBP display         1024     0 |   308   502   717 |   748   993  1649 | in place
D EntryDom nbr          53     1 |    31    41    52 |    39    51    85 | in place
E GbEXP, Pins          461     0 |   138   226   322 |   337   447   742 | in place
F Evolution            163     1 |    63    95   129 |   119   158   262 | in place
row  kind    lo central    hi  deps           role         basis
G2   g      906    1214  1554  -              prover-hard  G 1621 lines, 28 names
G3a  t      796    1274  1942  G2             prover-max   T 900 x NW + group D
G3b  t      300     484   741  G3a            prover-max   T 353 x NW
G4   b      500     800  1200  G3a, G3b       prover-max   assumed 500/800/1200 (no band base)
G5a  t     1123    1642  2617  G3a            prover-max   T 622 x NW + G 814 x TW
G5b  t      910    1209  2006  G5a            prover-hard  T 915 x TW + G 331 x TW
G5c  t      946    1531  2294  G2, G3a        prover-max   T 751 x NW + group C
G6a  t     1076    1430  2373  G3a, G3b, G4   prover-hard  T 1474 x TW
G6b  t     1034    1416  2297  G6a, G5b, G5c  prover-hard  T 1227 x TW + group E
E1   t      880    1169  1940  -              prover-hard  T 1205 (E/Pins, E/XiPins, Kernel/Evolution, Kernel/SumDecay) x TW
E2   t      664     889  1467  E1             prover-hard  T 882 x TW + G 68 in place
E3   t      326     438   706  E1,E2,T2379    prover       T 388 x TW + G 95 in place
sum        9461   13496 21137   rows = 12 (G 9, E 3); G 7591/11000/17024; E 1870/2496/4113
      class-t rows only: 8055 / 11482 / 18383;  rows with hi > 2000: ['G5a', 'G5b', 'G5c', 'G6a', 'G6b'];  per-stage flag 1.5 x 12 = 18
      lines classed T only (T lines x ratio): 6679 / 9507 / 15320;  plus the twinned G lines of group B: 836 / 1111 / 1844;  together 7515 / 10618 / 17164
old plan (T2161-portmap.md:1015-1023): G2-G6 1400+1400+1400+1400+800 = 6400 central (G1 1400 merged), E1-E3 1000+1500+700 = 3200; T2325-portmap.md:95-107 revised centrals: G2-G6 1400+1400+770+1400+800 = 5770, E1-E3 550+1500+700 = 2750
```
**B8 limit check of the three pins and of `M`** (external hypothesis, TEAM §8 l.14; finite-size, `d = 1` ring of 15-21 blocks of 40-60 sites and `d = 2` torus 7x7 blocks of 36 sites, not `d = 3`, not a limit): `python3 S/glimit.py brief`, `python3 S/glimit2.py`, `python3 S/moff.py`
```
d=1 ring (glimit.py brief): r1 = ||G-M||^2_max/max L2 (GiiGEX), rR = max_{|a-b|=R}(max_xy |(G-M)_xy|^2)/RHS_window1 (GijGEX), r3 = max_a|tr((G-M)E_a)|/max L2 (GavLGEX); median/max over 6 samples
Lb=21 W=40 g=0.3 Imz=0.3 t=t0*0.5: t0=0.727 g0=0.26 eta_t=0.596 Im m0=0.937 | max|G-M| 0.34 | r1 3.5/4.2 | rR max over R 0.51 (R=0..10) | r3 0.8/0.9
Lb=21 W=40 g=1.0 Imz=0.3 t=t0*0.5: t0=0.609 g0=0.78 eta_t=0.416 Im m0=0.598 | max|G-M| 0.15 | r1 2.0/2.6 | rR max over R 0.45 (R=0..10) | r3 1.2/1.4
Lb=21 W=40 g=3.0 Imz=0.3 t=t0*0.5: t0=0.337 g0=1.74 eta_t=0.219 Im m0=0.263 | max|G-M| 0.06 | r1 1.4/1.9 | rR max over R 0.20 (R=0..10) | r3 2.0/2.7
Lb=21 W=40 g=1.0 Imz=0.05 t=t0*0.9: t0=0.906 g0=0.95 eta_t=0.094 Im m0=0.508 | max|G-M| 0.34 | r1 6.9/7.7 | rR max over R 0.86 (R=0..10) | r3 1.7/2.1
Lb=21 W=40 g=1.0 Imz=0.05 t=t0*0.99: t0=0.906 g0=0.95 eta_t=0.052 Im m0=0.508 | max|G-M| 0.45 | r1 8.3/9.0 | rR max over R 0.91 (R=0..10) | r3 1.8/2.1
Lb=15 W=60 g=1.0 Imz=0.05 t=t0*0.99: t0=0.906 g0=0.95 eta_t=0.052 Im m0=0.507 | max|G-M| 0.40 | r1 9.2/11.3 | rR max over R 0.81 (R=0..7) | r3 1.6/2.1
Lb=21 W=40 g=3.0 Imz=0.05 t=t0*0.99: t0=0.555 g0=2.23 eta_t=0.038 Im m0=0.084 | max|G-M| 0.15 | r1 7.9/8.6 | rR max over R 0.55 (R=0..10) | r3 5.1/6.0
d=2 Lb=7 W=6 (block 36 sites) N=1764 g=1.0 Imz=0.3 t=t0*0.5: t0=0.601 g0=0.78 eta_t=0.407 Im m0=0.582 | max|G-M| 0.12 | r1 1.4/1.5 | rR max over R 0.04 (R=0..6) | r3 1.2/1.3
d=2 Lb=7 W=6 (block 36 sites) N=1764 g=1.0 Imz=0.05 t=t0*0.99: t0=0.902 g0=0.95 eta_t=0.052 Im m0=0.487 | max|G-M| 0.28 | r1 5.5/6.3 | rR max over R 0.09 (R=0..6) | r3 2.2/2.6
d=2 Lb=7 W=6 (block 36 sites) N=1764 g=3.0 Imz=0.05 t=t0*0.99: t0=0.336 g0=1.74 eta_t=0.029 Im m0=0.044 | max|G-M| 0.07 | r1 5.3/5.6 | rR max over R 0.04 (R=0..6) | r3 7.9/10.7
A  sz0 n=0 g=1/64: |m0|=0.9995 Im m0=0.9995 g0=0.0130; max_(a!=b)|M_ab|=0.0130; max over adjacent a~b |M_ab|=0.0130; W^-3/2=5.52e-03 W^-1/10=0.707; sum_b!=a |M_ab|^2=0.0010 (= 1-|m0|^2 = 0.0010)
B1 g=1: |m0|=0.6732 Im m0=0.6732 g0=0.5610; max_(a!=b)|M_ab|=0.3011; max over adjacent a~b |M_ab|=0.1624; W^-3/2=5.52e-03 W^-1/10=0.707; sum_b!=a |M_ab|^2=0.5467 (= 1-|m0|^2 = 0.5467)
B2 g=10: |m0|=0.5607 Im m0=0.5607 g0=4.6723; max_(a!=b)|M_ab|=0.5546; max over adjacent a~b |M_ab|=0.0245; W^-3/2=5.52e-03 W^-1/10=0.707; sum_b!=a |M_ab|^2=0.6856 (= 1-|m0|^2 = 0.6856)
```
**B9 exponent table** (`python3 S/exp.py`)
```
window of BAGavLGEX  W^{-d/2} <= Psi <= W^{-eps0} (7_8:1917), geometric mean, nonempty iff eps0 <= d/2 = 1.5:
  n=0 W=32: W^-1.5=5.524e-03; eps0=0.1: W^-eps0=7.071e-01 ok; eps0=1.0: W^-eps0=3.125e-02 ok; eps0=1.5: W^-eps0=5.524e-03 ok; eps0=2.0: W^-eps0=9.766e-04 EMPTY;
  n=1 W=1024: W^-1.5=3.052e-05; eps0=0.1: W^-eps0=5.000e-01 ok; eps0=1.0: W^-eps0=9.766e-04 ok; eps0=1.5: W^-eps0=3.052e-05 ok; eps0=2.0: W^-eps0=9.537e-07 EMPTY;
  n=2 W=7776: W^-1.5=1.458e-06; eps0=0.1: W^-eps0=4.082e-01 ok; eps0=1.0: W^-eps0=1.286e-04 ok; eps0=1.5: W^-eps0=1.458e-06 ok; eps0=2.0: W^-eps0=1.654e-08 EMPTY;
M-decay rate c = min(log(1 + kappa/(4 d Lam)), kappa/2) (BAct_rate, BA/CombesThomas.lean:45), d=3, Lam = 1/dd = 10:
  kappa=0.5: c = 0.004158, 1/c = 240.5
  kappa=0.25: c = 0.002081, 1/c = 480.5
thresholds on W (real) for the fixed constants of the band pins:
  delta = W^-0.1 <= 2^-19 (FlucThreshold, hB1 at M = 1): W >= 2^190 = 1.569e+57
  delta = W^-1.0 <= 2^-19 (FlucThreshold, hB1 at M = 1): W >= 2^19 = 5.243e+05
  delta = W^-1.5 <= 2^-19 (FlucThreshold, hB1 at M = 1): W >= 2^13 = 6.502e+03
  4 <= W^0.5 (E pins, T2016b): W >= 4^2 = 16; sz0 reaches it at n >= 0
  4 <= W^0.1 (E pins, T2016b): W >= 4^10 = 1048576; sz0 reaches it at n >= 7
  log L <= W^eps_E (E pin sum_res_2, (eq:latticesum_d3), A:194-198), eps_E = 1/10, sz0:
   n=0:ok n=1:FAIL n=2:FAIL n=3:ok n=4:ok n=5:ok n=6:ok
  window (i) of lem:sum_decay: t <= 1 - g0^2/L^2 at sz0 n=0 with g0 <= lam = 1/64, L = 4: g0^2/L^2 <= 1.53e-05
```
Narrative. Section (a) needed no correction (its row 10 is strengthened from the finite instances B1, B2 to a sequence by the compiled `BAFlow_not_small`, probe 183; its shape point is settled as F1 of `docs/reports/T2378-design.md`). The probe pins the target as the conjunction of the three merged pins (nothing is re-pinned), pins the G2 interface `BALDEin` and the five E pins, and compiles the data facts, the gap witness and the instances; it imports no `RBM1D`/`RBM2D` text. The classification is a reading (one class off at a boundary); the row sizes are assumptions with measured end points; the numerics of B8 are finite-size checks in `d = 1, 2` that the three pins are not contradicted (ratios bounded, not growing with the block distance), not evidence in `d = 3` and not a proof. The claims marked "reading" in the design (§2 F1, §3 (ii), (iii)) are not verified.

### (c) Verified names (run Sat Oct 10 11:07:19 UTC 2026; `lake env lean S/chk_names.lean`, `#check @NAME`, 48 names, exit 0, 0 lines with `error`)
Mathlib: `Real.sqrt_eq_rpow`, `Real.sqrt_sq`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_pos_of_pos`, `tendsto_rpow_neg_atTop`, `tendsto_natCast_atTop_atTop`, `Filter.tendsto_add_atTop_nat`, `gt_mem_nhds`, `Filter.Eventually.exists`, `Filter.Eventually.and`, `Matrix.nonsing_inv_eq_ringInverse`, `sub_eq_of_eq_add'`, `inv_mul_cancel₀`, `mul_le_of_le_one_left`, `Real.sqrt_le_one`, `Real.sqrt_pos`, `smul_smul`, `smul_mul_assoc`, `Complex.ofReal_ne_zero`, `Finset.single_le_sum`, `ProbabilityTheory.gaussianReal_zero_var` (route only, not used). Tactics `module`, `linear_combination (norm := module)`, `match_scalars`. Project: `BAflow_real`, `BAflow_lam0_window`, `BAGt_sub_BAMfine`, `BAMfine_norm_le_one`, `BAMfine_decay`, `BAMfine_eq`, `BAMB_diag_eq`, `BAt0_lt_one`, `BAg0_le`, `ztOf_im`, `BATheta_resolvent`, `BAMss_norm_eq_BAK`, `BAK_row_sum`, `baProp5to8_holds`, `baProp5_holds`, `baProp5s_holds`, `baProp6_holds`, `baProp8_holds`, `Green.stochDom_normSq_Hflow_diag`, `Green.ldeRowLHS`, `Green.OffPair`, `split_injective`, `GreenSchurInst.inst_BAFlow`, `FlowPinsInst.flow_sz0`, `FlowPinsInst.half_lt_t0`, `SizesInst.sz0_values`, `one_le_ellT`, `Sizes.seqHflowBA`.
Verified absent: (1) a bound `‖BATheta‖ ≤ (1-t)⁻¹` or a strict `‖m‖ < 1` in `BA/*.lean` (`grep -rn "theorem BATheta_norm\|norm_lt_one" RBM3D/BA/*.lean`: 0 hits); (2) a merged a.s. block-support lemma of `seqHflow (sz.withLam 0)` (`grep -rn "block support\|off-block\|in-block"` over `BA Gauss Defs Green Induction`: only docstrings, `Gauss/FlowCalculus.lean:220`, `Induction/ConArgDet.lean:1357`, `BA/GreenSchur.lean:18`); (3) a public `Gres H z true = green H z` in `Green/` (`python3 S/gres.py`: `17 private (5 in Green/), 1 public: [('Induction/ContinuityNet.lean', 430, False)]`)

### (d) Open issues and paper-delta candidates
1. Decisions requested of the supervisor (design §7): shape of `BAGbEXPij`/`BAGbEXPii` (F1); the range `W^{-ε} < g ≤ 𝔡⁻¹` (F2); TEAM §3 design gates for G3a, G3b, G4, G5a, G5c; route (in place A, C, D, E, F; twin B); flag 18 and the T count; closing conditions.
2. Owed inside G2, not compiled: a.s. block support of `X` (route in (c)); measurability and off-row dependence of the minor of `D + X`.
3. `BAEKSumNdecay` (`lem:sum_Ndecay`) is not in the ticket's four E lemmas; it is pinned (probe 208) because the band pin `EKSumNdecay` exists and the consumer `STEKSumNdecay` (`Induction/Step34Pins.lean:613`) needs its BA form.
4. Observation: `Gres H z true = green H z` has 17 private copies, 5 of them in `Green/` (c), and one public statement outside `Green/`; a publishing ticket would save the copy tax of the G rows.
5. Paper-delta candidates (design §7): `T2378a` `BAGijGEX` against `(GijGEX_BA)` (`7_8:1940-1946`); `T2378b` `BAGiiGEX` against `(GiiGEX_BA)`, `(GavLGEX_BA)` (`7_8:1930-1938`); `T2378c` `lem_GbEXP_BA` cited for `g ≤ W^{-ε}`, claimed for `g ≤ 𝔡⁻¹` (`7_8:1948`); `T2378d` route remark `Ξ = ((t-s)/t)(Θ - 1)` (probe 264), no statement difference.
