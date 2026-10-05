Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 21:39:53 UTC 2026

Setting (from the files): `G = (H - z)^{-1}` (`Gres`), `H_u = √u X`, `z_u = E + (1-u) m` (`zt`), `m = mE E`, `m(m+E) = -1` (`mE_mul`), `Θ_ξ = (1 - ξ S)^{-1}` (`Theta`), `tr E_a = 1`, `E_a E_q = δ_{aq} W^{-d} E_a`. Scripts: scratchpad `T2217/{inst2,ext,alg}.py` (commands below).

### (i) Exponent table

| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | self-consistent eq. (target 1b) | Stein `1 + z g_a = -u Σ_p S_{pa} E[g_p g_a]`, `g=m+Z`, `Σ_p S_{pa}=1`, `z_u + u m = E + m = -1/m` gives `x_a = u m² Σ_b S_{ba} x_b + y_a`, `y_a = u m Σ_b S_{ba} E[Z_b Z_a]` | exact; residual 7.6e-16 (alg.py, below) |
| 2 | Stein normalization (1a) | `Σ_c gvar_c tr(A B_c C B_c) = W^d Σ_{pq} tr(A E_p) S_{pq} tr(C E_q)` (`sum_coordinateBlock_trace_pair`, `ContractionSecondLoop.lean:239`); `A=G`, `C=G E_a`, `tr(G E_a E_q) = δ_{aq} W^{-d} g_a` (`trace_Eblk_mul_Eblk`) ⇒ `W^d·W^{-d}=1`, left with `Σ_p S_{pa} g_p g_a` | exact (alg.py: fine-lattice contraction vs `W^d Σ SB tr tr`, diff 8.9e-16). `gvarF` profile is `svarF = W^{-d} SBR d L g` (`FineModel.lean:47`), `SB d L g` has the same `g`; `seqP_map_slice` (`:184`) gives `PF d (L n) (W n) (lam n)`: no `lam` mismatch |
| 3 | bulk `κ' = √(2κ)/2` | `|E| ≤ 2-κ ⇒ Im m = √(4-E²)/2 ≥ κ'` (`4-E² ≥ 4κ-κ² ≥ 2κ` iff `κ ≤ 2`; `st6_mE_im_ge`) | κ=1/10: κ'=0.2236; Im m=0.9682 at E=1/2; 0.312 at worst `|E|=1.9` |
| 4 | `Λ = 𝔡⁻¹` | eventually `0 < lam ≤ Λ` (`WO`: `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`, `W^x>0`, `st6_lam_pos`) | 𝔡=1/10: Λ=10; sz0: `lam_0=1/64` |
| 5 | `ξ = u m²` | `‖ξ‖ = u < 1` (`norm_mE`); `u ≤ lemT z <1` (`st5_t_lt_one`) | `1-u ≥ Im z/(1+‖z‖) ≥ N^{-1+ε}/4` (`‖z‖ ≤ (2-κ)+1 < 3`); u=1/16: 15/16 |
| 6 | row sum `C₀` (1c) | `x = Θ_ξ y` (`Theta_mul_of_three_le`: `Θ(1-ξS)=1`, `S` symmetric); `‖x_a‖ ≤ ‖Θ‖_{∞→∞}·max‖y‖` (`Matrix.linfty_opNorm_mulVec`; `‖A‖ = sup_i Σ_j ‖A_ij‖`, `linfty_opNorm_def`, `Mathlib/Analysis/Matrix/Normed.lean:284,364`); `uKer d L g (m·m) 0 u = (1 - 0•SB)·Θ_{u m²} = Θ_{u m²}` (`Kernel/Evolution.lean:56`), `PropSpin m true = m`; `EKSameRow d Λ κ'` hypotheses: `3≤d`, `0<Λ`, `0<κ'`, `3≤L`, `0<g≤Λ`, `‖m‖=1`, `κ'≤Im m`, `0≤0≤u<1` all hold | `C₀ = C₀(d,Λ,κ)` only. Numerics (below): flat in `L=4..32` (no `log L`); 0.50–4.05 except `E=0, g=Λ=10, u→1`: 300.41 ≈ `(2dΛ²+1)/2 = 300.5` (mode `(π,π,π)`), so `C₀` must depend on Λ, as stated |
| 7 | `y` bound (1d) | `|E Z_b Z_a| ≤ (E|Z_b|²+E|Z_a|²)/2 ≤ K`; `|u m| = u ≤ 1`; `Σ_b ‖S_{ba}‖ = 1` (`sum_nnnorm_SB_row`) ⇒ `‖y‖ ≤ K`, `‖x‖ ≤ C₀ K` | exact, no loss; `C = C₀` |
| 8 | floor `B=1` (2a) | `Bctl = W^{-d}[(g²+1-u)⁻¹ + (L^d(1-u))⁻¹] ≥ W^{-d}L^{-d}/(1-u) ≥ N⁻¹` (`0≤u<1`; first term `≥0`) | `Bctl·N` = 69.3 (n=0), 547 (n=1) |
| 9 | envelope (2c) | `‖𝓛^{(1)}‖ ≤ (LW)^d (η⁻¹ W^{-d}) = L^d η⁻¹` (`norm_gloop_le_crude`); `‖Y‖ ≤ L^d η⁻¹ + 1` (`‖m‖=1`); `Kenv = 3`; `L^d ≤ N`, `W^d ≤ N` | with `η⁻¹ ≤ N`: `N²+1 ≤ N³` for `N ≥ 2`; sz0 n=0, u=lemT z: `Env=7.3e6 ≤ N³` (True, ext.py) |
| 10 | `η_u⁻¹ ≤ N` (2b) | `η_u = (1-u) Im m ≥ (N^{-1+ε}/4)(√(2κ)/2)` for `u ≤ lemT z` (`ST_one_sub_lemT`); holds once `N^ε ≥ 8/√(2κ)` | κ=ε=1/10: `8/√(2κ)=17.89`, `N ≥ 3.36e12`: **above** `N_0 = 2097152`, so the statement is eventual only; a witness holds anyway at `u=lemT z`: n=0 `1/η=1.14e5 ≤ 2.1e6`, n=1 `2.5e9 ≤ 5.5e11`. Alternative needing only `N ≥ 18.89`: `17.9 L^d N^{1-ε}+1 ≤ N³` |
| 11 | moments (2c) | `hdom` = `LWAvgLaw` = `Prec` (uniform over `a`), `hΦ` = `STBctl_pos`, `hY0` (norm ≥0), measurable, `momentDomAt_of_stochDomAt_of_nonneg`; `MomentDomAt` at `(ε=τ/2, p=1)`: `∫‖Z‖² ≤ C₁ N^{τ/2} Bctl²` | `C₁=C₁(τ)`, fixed before `n` |
| 12 | absorption (3a) | `‖E 𝓛 - m‖ ≤ C₀ C₁ N^{τ/2} Bctl² ≤ N^τ Bctl²` iff `C₀C₁ ≤ N^{τ/2}`; `N→∞` (`SizeTendsto`, `tendsto_size`) | eventual (any `τ>0`) |
| 13 | charge `-`, `u=0` | `mSigma E false = conj mE E`, `𝓛_- = conj 𝓛_+` (`ST_Lloop_one_false`) so equal moduli; `u=0`: `zt E 0 = E+m`, `G_0 = -(E+m)^{-1} = m` | `|-(E+mE)^{-1} - mE| = 1.2e-16` (E=1/2) |
| 14 | deterministic `Prec` | `st6_prec_det_iff` (`SizeTendsto`): `STExpAvgAt` ⇔ `∀τ>0, ∀ᶠ n, ∀ v, F ≤ N^τ G`; no `ω`-dependence in `F` | — |

Route (checked against RBM2D `Step61.lean` at `c9a24cf`, `git show`): `step61_stein :271`, `selfcons :339`, `expErr_le :528`, `integral_slice :670`, `moment :683`, `step61 :853`, `check_u_zero :998` (all present, file has 1021 lines there). `d≥3` changes: `W^d` for `W²` (row 2), `Bctl` for `scaleM⁻¹` (rows 8-9), row sum from `ekSameRow_holds` with no `log L` (row 6), charge `-` by `ST_Lloop_one_false` (row 13). RBM2D's working tree is at `ec26147` (939 lines); the ticket's line numbers hold only at `c9a24cf`, so read it with `git show c9a24cf:RBM2D/Evolution/Step61.lean`.

Consumer check (§45 O2): `STImproveExpAver d` binders `3≤d → κ ε 𝔡 → 0<κ → 0<ε → 0<𝔡 → 𝔠 sz z → STFlow → u → 0≤u → u≤lemT → LWAvgLaw → STLK → STExpAvgAt` (`Step6Pins.lean:191-195`); `st6_expAvgU_of_pin` applies `hAvg hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u (…) (…) (LWAvgLaw…) (STLK…)` (`Step6Kit.lean:565-566`): same order. `STLK` is unused (RBM2D's `Step61Pin` uses `(Eq:L-KGt)` at `k=1` only = `LWAvgLaw`).
Registry plan: delete the owed line of `STImproveExpAver` (`Axioms.lean:229`); the skeletons still carry it as a premise, `scanPremises` counts it proved by `stImproveExpAver_holds`; no new `Prop`.

### (ii) One concrete nondegenerate instance (`d=3`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `sz0`, `z0 = 1/2 + i N^{-4/5}`, `u ≡ 1/16`)
`sz0`: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`; `n=0`: `L=4, W=32, N=2097152, lam=1/64`. No hypothesis degenerate: `N>0`, nonempty index `Zd 3 4` (64 labels), `0<lam<Λ`, `1/16 ≤ lemT z0 < 1`.
Command: `python3 T2217/inst2.py` (scratchpad), output (n=5 and floating rounding of `lemT=1-10^{-17}` omitted; trimmed to n=0,1):
```
kappa'=sqrt(2k)/2 = 0.22360679774997896  Lambda=1/frakd = 10.0
n=0: L=4 W=32 lam=1.562e-02 N=2.0972e+06 L^d<=N:True W^d<=N:True
  locDomain: |Re z|=0.5<=2-k:True  N^(-1+eps)=2.044e-06<=Im z=8.764e-06:True Im z<=1
  WO: W^(-d/2+fd)=7.813e-03<=lam:True  lam<=1/fd:True
  E=lemE z=0.500000 |E|<=2-k:True; |m|=1.000000000000; Im m=0.9682>=kappa':True
  t0=lemT z=0.999991 (>=1/16:True, <1:True); u=1/16<=t0; z_n=zt(E,t0)? |diff|=2.26e-06
  identity z_u m + u m^2 = -1.000000000000+0.000000000000j (expect -1); z_u+u m + 1/m = 5.55e-17
  Bctl=3.3052e-05 >= 1/N=4.7684e-07: True; Bctl*N=69.3156
  eta_u=0.9077, 1/eta_u=1.102 <= N: True; Env=L^d/eta+1=7.1506e+01 <= N^3: True
n=1: L=8 W=1024 lam=2.441e-04 N=5.4976e+11 L^d<=N:True W^d<=N:True
  locDomain: ...:True  WO: ...:True  lam<=1/fd:True  |E|<=2-k:True; Im m=0.9682>=kappa':True
  Bctl=9.9535e-10 >= 1/N=1.8190e-12: True; Bctl*N=547.2000
eta^-1<=N guaranteed once N^eps>=8/sqrt(2k): 8/sqrt(2k)=17.8885, N>= 3.355e+12; N_0=2097152 is below it
Kenv=3 route: 8/sqrt(2k) N^(1-eps)*L^d+1 <= 8/sqrt(2k)*N^2+1 <= N^3 once N>=18.89
max row sum of Theta_{u m^2}, d=3, L=4,8,16,32
 E=0.0 g=0.0156 u=0.0625 [0.941, 0.941, 0.941, 0.941]
 E=0.0 g=10.0000 u=0.999999 [300.41, 300.41, 300.41, 300.41]
 E=1.9 g=10.0000 u=0.0625 [1.066, 1.066, 1.066, 1.066]
 E=1.9 g=10.0000 u=0.999999 [3.531, 4.005, 4.048, 4.048]
```
(rows `E=0,g=1/64,u→1` 0.501; `E=1.9,g=1/64,u→1` 1.606; `E=1.9,g=1/64,u=1/16` 1.052; `E=0,g=10,u=1/16` 1.066 omitted here, all flat in `L`.)
Commands `python3 T2217/ext.py`, `python3 T2217/alg.py`:
```
n=0: u=lemT z=0.999990949, eta_u=8.764e-06, 1/eta_u=1.141e+05 <= N=2.097e+06: True; Env=7.303e+06 <= N^3: True; 1-t0 >= Im z/(1+|z|): True
n=1: u=lemT z=1.000000000, eta_u=4.054e-10, 1/eta_u=2.467e+09 <= N=5.498e+11: True; Env=1.263e+12 <= N^3: True; 1-t0 >= Im z/(1+|z|): True
S symmetric: True  column sums=1: True
max |R_a - (-1/m)(x_a - u m^2 (Sx)_a - u m sum_p S_pa C_pa)| = 7.550332863779066e-16
|u m| = 0.8  <=1;  z_u m + u m^2 + 1 = 1.1102230246251565e-16
```
External hypothesis `LWAvgLaw` (`(Gt_avgbound_flow)`, another gate's pin, stays a hypothesis of the instances), concrete limit: its scale `Bctl(1/16)·W^d = (lam²+15/16)^{-1} + (L^d·15/16)^{-1}`: `1.08306 (n=0), 1.06875 (n=1), 1.0666667 (n=50), 1.0666667 (n=10^4) → 1/(1-u) = 16/15` (as `lam→0`, `L→∞`); so `Bctl ~ (16/15) W^{-d} → 0` and `Bctl·N ~ (16/15) L^d → ∞`, consistent with the floor of row 8; the pin's right side is `N^τ Bctl² ~ N^τ W^{-2d}`. `STLK`, `STStep2Core`, `STLKU`, `LWtermEXP`, `STExp*` stay hypotheses (not used by the target proofs except `LWAvgLaw`).

### Verdicts
- Target 1 (a) `expAvg_stein`, (b) `expAvg_selfcons`, (c) `expAvg_norm_solve`, (d) `expAvg_expErr_le`: PASS (rows 1,2,5,6,7).
- Target 2 (a) `expAvg_Bctl_ge`, (b) `expAvg_eta_inv_le`, (c) `expAvg_moment`, (d) `expAvg_integral_conj`, (e) `expAvg_u_zero`: PASS (rows 8-13). Finding (non-blocking): 2b is true but eventual only, with threshold `N ≥ 3.36e12` at `κ=ε=1/10`; the prover must not look for a concrete `n` (as the ticket says); row 9 needs only `N ≥ 18.89` if the prover prefers the weaker `η⁻¹ ≤ 17.9 N^{1-ε}`.
- Target 3 (a) `STExpAvgAt_of_LWAvgLaw`, (b) `stImproveExpAver_holds`: PASS (rows 11,12,14, consumer check).
- Target 4 (the 8 instances): PASS (instance above; `inst_eta_inv_le` eventual).

## (a′) Preflight corrections — Mon Oct  5 22:05:20 UTC 2026
Section (a), Route paragraph: "RBM2D's working tree is at `ec26147` (939 lines)". Script output: `git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h` prints `9e0f275`; `log --oneline -4 -- RBM2D/Evolution/Step61.lean` lists `ec26147` as the last commit touching that file (`wc -l RBM2D/Evolution/Step61.lean` in that tree prints 939; at `c9a24cf`: 1021 lines, `git show c9a24cf:... | wc -l` below). No verdict changes: the route line numbers of (a) (`step61_stein :271`, `selfcons :339`, `expErr_le :528`, `integral_slice :670`, `moment :683`, `step61 :853`, `check_u_zero :998`) hold in `c9a24cf`, the copy this stage read.

## (b) Script output
Branch `t/T2217`, head `f8cf545` (two commits, both touch only the two writable files).
```
$ date -u
Mon Oct  5 22:04:35 UTC 2026
$ git log --oneline -1 t/T2217; git diff --stat main...t/T2217
f8cf545 T2217: fix the RBM2D line citation in the docstring of expAvg_eta_inv_le
 RBM3D/Induction/ExpAvg.lean | 1019 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean      |    1 -
 2 files changed, 1019 insertions(+), 1 deletion(-)
$ git diff main -- RBM3D/Induction/Step6Pins.lean | wc -l
       0
$ grep -n -E "sorry|admit|native_decide|^axiom" RBM3D/Induction/ExpAvg.lean | wc -l
       0
$ name-clash grep: grep -rn --include=*.lean -w <name> RBM3D RBM3D.lean (outside ExpAvg.lean), every top-level theorem/def of the file
names checked: 55, total hits outside ExpAvg.lean: 0
$ grep -rn --include=*.lean -E "Induction[./]ExpAvg|T2217Check" RBM3D RBM3D.lean | wc -l
       0
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Evolution/Step61.lean
 RBM2D/Evolution/Step61.lean | 130 ++++++++------------------------------------
 1 file changed, 24 insertions(+), 106 deletions(-)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Evolution/Step61.lean | wc -l
    1021
$ wc -l RBM3D/Induction/ExpAvg.lean
    1019 RBM3D/Induction/ExpAvg.lean
$ lake build RBM3D.Induction.ExpAvg 2>&1 | tail -2   # `✔` (not `⚠`): no warning for ExpAvg.lean
✔ [3851/3851] Built RBM3D.Induction.ExpAvg (6.3s)
Build completed successfully (3851 jobs).
$ lake env lean RBM3D/Induction/ExpAvg.lean; echo exit=$?
exit=0
$ for ref in main t/T2217: git show $ref:RBM3D/Test/Axioms.lean | python3 count_owed.py   # entries of `owedProps`
main: 147
t/T2217: 146
$ git diff main...t/T2217 -- RBM3D/Test/Axioms.lean | grep "^[-+][^-+]" | cut -c1-110
-   `RBM.Gauss.Sizes.STImproveExpAver, -- `6:12-17` improved averaged bound per time: S6-03; S6-01 (T2204, DEC
```
Full build (root `#assert_rbm_axioms`) with the import line the hub adds, then without it, and the registry pre-check (§20 (2)):
```
Mon Oct  5 22:02:58 UTC 2026
$ lake build   # RBM3D.lean with the temporary (uncommitted) line `import RBM3D.Induction.ExpAvg` after PinsC2
info: RBM3D.lean:261:0: axiom audit: 6460 theorems, 2222 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 95, structural 25, refuted 6).
registry: 2 borrowed + 146 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
Build completed successfully (4021 jobs).
exit=0
Mon Oct  5 22:04:28 UTC 2026
$ lake build   # RBM3D.lean as committed (no ExpAvg import: the hub adds it at merge)
error: RBM3D.lean:260:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`:
[...]
$ lake env lean scratchpad/T2217/precheck.lean ; echo exit=$?   # file = import RBM3D / import RBM3D.Induction.ExpAvg / #assert_rbm_axioms
exit=0
axiom audit: 6460 theorems, 2222 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 95, structural 25, refuted 6).
registry: 2 borrowed + 146 owed + 80 structural + 7 refuted; 108 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -c STImproveExpAver precheck.out
0
$ grep -c "no theorem of this development proves" precheck.out
0
```
(The root olean used by the pre-check was built from `RBM3D.lean` plus the temporary uncommitted import line; `RBM3D.lean` was restored afterwards, `git status --short` empty.)
Check-file equality and axioms (`#print axioms` of the 11 targets and the 15 instances; raw lines in scratchpad `T2217/axioms.out`):
```
$ lake env lean check_eq.lean; echo exit=$?   # check file imports + `import RBM3D.Induction.ExpAvg` + its sections 1-2 + equality examples + section 3 as examples
exit=0
$ grep -c "^example" check_eq.lean : 20
$ grep -c "^example.*:= @RBM.Gauss.Sizes\." check_eq.lean : 11
$ grep -c "error" check_eq.out check_eq.err : check_eq.err:0 check_eq.out:0 
$ lake env lean scratchpad/T2217/axioms.lean   # 26 `#print axioms` lines, grouped by script
26 declarations depend on exactly [propext, Classical.choice, Quot.sound]:
Sizes.expAvg_stein, Sizes.expAvg_selfcons, Sizes.expAvg_norm_solve, Sizes.expAvg_expErr_le, Sizes.expAvg_Bctl_ge, Sizes.expAvg_eta_inv_le, Sizes.expAvg_moment, Sizes.expAvg_integral_conj, Sizes.expAvg_u_zero, Sizes.STExpAvgAt_of_LWAvgLaw, Sizes.stImproveExpAver_holds, Step6Inst.inst_expAvgAt_holds, Step6Inst.inst_improveExpAver_holds, Step6Inst.inst_expAvgU_holds, Step6Inst.inst_skeleton6I_avg, Step6Inst.inst_skeleton6II_avg, Step6Inst.inst_skeleton6IV_avg, Step6Inst.inst_eta_inv_le, Step6Inst.inst_expAvg_u_zero, Step6Inst.inst_expAvg_stein, Step6Inst.inst_expAvg_selfcons, Step6Inst.inst_expAvg_norm_solve, Step6Inst.inst_expAvg_expErr_le, Step6Inst.inst_expAvg_Bctl_ge, Step6Inst.inst_expAvg_moment, Step6Inst.inst_expAvg_integral_conj
```
Target statements, extracted from `RBM3D/Induction/ExpAvg.lean` by script (`extract.py`; whitespace collapsed to one line per declaration; the last 8 are the instances of the ticket, proofs omitted):
```
theorem expAvg_stein {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g u : ℝ) (hu : 0 ≤ u) {z : ℂ} (hz : z.im ≠ 0) (a : Zd d L) : ∫ ω : Ω d L W, Matrix.trace (HflowBlock d L W u ω * Gres (HflowBlock d L W u ω) z true * Eblk d L W a) ∂(PF d L W g) = -(u : ℂ) * ∑ p : Zd d L, SB d L g p a * ∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) z ⟨[true], [p]⟩ * loopL d L W (HflowBlock d L W u ω) z ⟨[true], [a]⟩ ∂(PF d L W g)
theorem expAvg_selfcons {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (a : Zd d L) : (∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ ∂(PF d L W g)) - mE E = (u : ℂ) * mE E ^ 2 * ∑ b : Zd d L, SB d L g b a * ((∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ ∂(PF d L W g)) - mE E) + (u : ℂ) * mE E * ∑ b : Zd d L, SB d L g b a * ∫ ω : Ω d L W, (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - mE E) * (loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ - mE E) ∂(PF d L W g)
theorem expAvg_norm_solve {d : ℕ} (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ E u : ℝ, |E| ≤ 2 - κ → 0 ≤ u → u < 1 → ∀ x y : Zd d L → ℂ, (∀ a, x a = ((u : ℂ) * mE E ^ 2) * ∑ b, SB d L g b a * x b + y a) → ∀ K : ℝ, (∀ a, ‖y a‖ ≤ K) → ∀ a, ‖x a‖ ≤ C * K
theorem expAvg_expErr_le {d : ℕ} (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) : ∃ C : ℝ, 0 < C ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ E u : ℝ, |E| ≤ 2 - κ → 0 ≤ u → u < 1 → ∀ K : ℝ, (∀ b : Zd d L, ∫ ω : Ω d L W, ‖loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [b]⟩ - mE E‖ ^ 2 ∂(PF d L W g) ≤ K) → ∀ a : Zd d L, ‖(∫ ω : Ω d L W, loopL d L W (HflowBlock d L W u ω) (zt E u) ⟨[true], [a]⟩ ∂(PF d L W g)) - mE E‖ ≤ C * K
theorem expAvg_Bctl_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u
theorem expAvg_eta_inv_le {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z n) → (etaT (STflowE z n) u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)
theorem expAvg_moment {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hut : ∀ n, u n ≤ lemT (z n)) (hLW : LWAvgLaw sz (STflowE z) u) : MomentDomAt sz.seqP sz.size (U := fun n => Zd d (sz.L n)) (fun n b ω => ‖Lloop sz n (STflowE z n) (u n) (fun _ : Fin 1 => true) (fun _ => b) ω - mE (STflowE z n)‖) (fun n _ => sz.Bctl n (u n))
theorem expAvg_integral_conj {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (a : Zd d (sz.L n)) : ∫ ω, Lloop sz n E u (fun _ : Fin 1 => false) (fun _ => a) ω ∂(sz.seqP) = (starRingEnd ℂ) (∫ ω, Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP))
theorem expAvg_u_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (a : Zd d (sz.L n)) : ∫ ω, Lloop sz n E 0 (fun _ : Fin 1 => true) (fun _ => a) ω ∂(sz.seqP) = mE E
theorem STExpAvgAt_of_LWAvgLaw {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hut : ∀ n, u n ≤ lemT (z n)) (hLW : LWAvgLaw sz (STflowE z) u) : STExpAvgAt sz (STflowE z) u
theorem stImproveExpAver_holds (d : ℕ) : STImproveExpAver d
theorem inst_expAvgAt_holds (hA : LWAvgLaw sz0 (STflowE z0) tInst) : STExpAvgAt sz0 (STflowE z0) tInst
theorem inst_improveExpAver_holds (hA : LWAvgLaw sz0 (STflowE z0) tInst) (hK : STLK sz0 (STflowE z0) tInst) : STExpAvgAt sz0 (STflowE z0) tInst
theorem inst_expAvgU_holds (hS2 : STStep2Core sz0 (STflowE z0) sInst tInst) (hLKU : STLKU sz0 (STflowE z0) sInst tInst) : STExpAvgU sz0 (STflowE z0) sInst tInst
theorem inst_skeleton6I_avg (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hDuQ : STExpDuhamelQ 3) (hDec : STExpDriftDecay 3) (hWd : STExpWardI 3) (hIni : STExpIniI 3) (hInt : STExpIntI 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
theorem inst_skeleton6II_avg (hLK : STExpLKLKHi 3) (hLW : LWtermEXP 3) (hDu : STExpDuhamelZ 3) (hInt : STExpIntII 3) (hWd : STExpWardII 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)
theorem inst_skeleton6IV_avg (hDu : STExpDuhamelZ 3) (hLo : STExpDriftLo 3) (hInt : STExpIntIV 3) : InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
theorem inst_eta_inv_le : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ lemT (z0 n) → (etaT (STflowE z0 n) u)⁻¹ ≤ ((sz0.size n : ℕ) : ℝ)
theorem inst_expAvg_u_zero : ∫ ω, Lloop sz0 0 (1 / 2) 0 (fun _ : Fin 1 => true) (fun _ => 0) ω ∂(sz0.seqP) = mE (1 / 2)
```
Narrative.
1. Delivered: `RBM3D/Induction/ExpAvg.lean` (`wc -l` above) and one deleted line of `RBM3D/Test/Axioms.lean` (the owed line of `STImproveExpAver`); `git diff --stat main...t/T2217` lists exactly these two files; `Step6Pins.lean` is unchanged (0 diff lines).
2. Layout (`/-! ##` headings): §1 fixed size `:56` (`expAvg_stein :295`, `expAvg_selfcons :370`), §2 deterministic `:448` (`expAvg_norm_solve :479`, `expAvg_expErr_le :530`), §3 sequence `:596` (`expAvg_Bctl_ge :604`, `expAvg_eta_inv_le :631`, `expAvg_moment :711`, `expAvg_integral_conj :769`, `expAvg_u_zero :777`), §4 the pin `:791` (`STExpAvgAt_of_LWAvgLaw :799`, `stImproveExpAver_holds :879`), §5 instances `:885` (15 `inst_*` theorems: the 8 of the ticket and 7 more, for `expAvg_stein/selfcons/norm_solve/expErr_le/Bctl_ge/moment/integral_conj`).
3. Ports from RBM2D `Evolution/Step61.lean` at `c9a24cf` (read by `git show`): `step61_stein :271` (helpers `:59-268`, among them `step61_sub_mul_green :59`, `step61_contraction :192`) to `expAvg_stein`; `step61_selfcons :339` to `expAvg_selfcons`; `step61_theta_solve :428`, `step61_theta_row_sum :449`, `step61_norm_solve :486` to `expAvg_theta_solve` (private) and `expAvg_norm_solve`; `step61_expErr_le :528` to `expAvg_expErr_le`; `step61_integral_slice :670` to `expAvg_integral_slice` (private); `step61_moment :683` to `expAvg_moment`; `step61 :853` to `STExpAvgAt_of_LWAvgLaw`; `step61_check_u_zero :998` to `expAvg_u_zero`. Not ported: `step61_log_absorb :808`, `step61_scaleM_le :631`, `Path/PerTime`, the `RangeCond`/`InitLK` vocabulary, the private checks `step61Inst*`. RBM2D `HEAD` differs from `c9a24cf` in this file (diff-stat above); the port follows `c9a24cf`.
4. `d ≥ 3` changes, all in the file: the `W^d` of `sum_coordinateBlock_trace_pair` cancels the `(W^d)⁻¹` of `expAvg_Eblk_mul_Eblk` (re-proved privately; `Eblk_mul_Eblk` of `LoopGenerator` is private); the row sum of `Θ_{u m²}` is bounded through `uKer d L g (m*m) 0 u = Theta d L g (u*m^2)` and `RBM.sum_norm_row_le` by the constant of `ekSameRow_holds d Λ (√(2κ)/2)`, so `C = C(d, Λ, κ)` with no `log L`; `Bctl` replaces `scaleM⁻¹` (`expAvg_Bctl_ge`); the reverse bridge `momentDomAt_of_stochDomAt_of_nonneg` is used with `B = 1`, `Env n = L^d η⁻¹ + 1`, `Kenv = 3`, and `hdom` is the hypothesis `LWAvgLaw` itself (a `Prec`, uniform in `a`: no per-time to uniform step); the charge `-` is `expAvg_integral_conj`.
5. The premise `STLK` of the pin is unused (binder `_hLK` in `stImproveExpAver_holds`); `STExpAvgAt_of_LWAvgLaw` takes `LWAvgLaw` only; `0 < 𝔡` is `hz.1.2.1` (from `STFlow`).
6. `expAvg_eta_inv_le` and `inst_eta_inv_le` are eventual statements (threshold `N^ε ≥ 8/√(2κ)`, row 10 of (a)).
7. Instances: every deterministic hypothesis is discharged at `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6` (`flow_z0`, `sz0_ht`, `norm_num`). Stochastic premises stay hypotheses: `LWAvgLaw` (`inst_expAvgAt_holds`, `inst_improveExpAver_holds`, `inst_expAvg_moment`), `STLK`, `STStep2Core`, `STLKU`; and the other gates' pins in the skeleton instances (`STExpLKLKHi`, `LWtermEXP`, `STExpDuhamelZ/Q`, `STExpDriftDecay/Lo`, `STExpWardI/II`, `STExpIniI`, `STExpIntI/II/IV`).
8. Registry: `owedProps` has 147 entries on `main` and 146 on the branch (script above); `STImproveExpAver` does not occur in the pre-check output; the output has no "no theorem of this development proves" error.
9. Merge order: with `RBM3D.lean` as committed the root build reports `STImproveExpAver` unclassified (output above), because `RBM3D.lean` does not import `ExpAvg`; with the temporary import line the full build exits 0 (4021 jobs). The hub adds `import RBM3D.Induction.ExpAvg` after `import RBM3D.Universality.PinsC2`, the last import line of `RBM3D.lean` at this stage.
10. No hypothesis was added to a target, no target weakened, no pinned signature changed, no file outside the two writable files committed.

## (c) Verified Mathlib names used
Script: every dotted or underscored identifier of the file (comments stripped) was tested with `env.contains` over the namespaces `MeasureTheory, Matrix, Filter, ProbabilityTheory, Real, Finset, Complex, Nat` (126 resolved, list in scratchpad `T2217/mathlibnames.out`); the non-trivial subset, all resolved and all used by a compiled proof:
Complex.norm_conj, Complex.norm_le_abs_re_add_abs_im, Complex.norm_of_nonneg, Complex.norm_real, Filter.eventually_ge_atTop, Filter.Eventually.of_forall, Finset.single_le_sum,
integral_conj, inv_anti₀, inv_eq_of_mul_eq_one_right, Matrix.add_mul, Matrix.diagonal_apply, Matrix.diagonal_mul_diagonal, Matrix.mulVec_mulVec, Matrix.one_mulVec,
Matrix.smul_mul, Matrix.smul_mulVec, Matrix.sub_mul, Matrix.sub_mulVec, Matrix.trace_add, Matrix.trace_mul_comm, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_sum,
MeasureTheory.integrable_const, MeasureTheory.integrable_map_measure, MeasureTheory.Integrable.of_bound, MeasureTheory.integral_add, MeasureTheory.integral_const,
MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum, MeasureTheory.integral_map, MeasureTheory.integral_mono_of_nonneg, MeasureTheory.integral_nonneg,
MeasureTheory.integral_sub, MeasureTheory.norm_integral_le_integral_norm, Nat.le_mul_of_pos_left, Nat.pow_le_pow_left, norm_sum_le, pow_le_pow_left₀, Real.mul_self_sqrt,
Real.rpow_add, Real.rpow_natCast, Real.rpow_neg, Real.rpow_neg_one, Real.rpow_pos_of_pos, Ring.mul_inverse_cancel, tendsto_rpow_atTop, MeasureTheory.Integrable.bdd_mul
(Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1068), tendsto_natCast_atTop_iff (Mathlib/Order/Filter/AtTopBot/Archimedean.lean:35), div_le_div_iff₀
Names verified absent: none looked for (no name was guessed; every name above elaborates in the compiled file).

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none new (no step needed a hypothesis the pin lacks); D487 (T2191c, pin per time sequence `u`) cited, not re-proposed.
- For the dispatcher: (a′) above (RBM2D hash in (a)); `expAvg_eta_inv_le` is eventual only (consistent with the eventual conclusion `Prec` of the pin); RBM2D `HEAD` has a later version of `Step61.lean` (130 changed lines in the diff-stat above), the port follows `c9a24cf` as the ticket says.
- For the hub (ticket merge note, §20 (3)): add `import RBM3D.Induction.ExpAvg` after the last `import` line of `RBM3D.lean`; if `RBM3D/Test/Axioms.lean` conflicts only in the lists, take the union except that `STImproveExpAver` stays deleted.

