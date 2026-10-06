Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 03:09:55 UTC 2026

Amended targets (T2237-amend-1): `BAConArg''` = `BAConArg'` hypotheses, then `∀ C₀ > 0, (∀ k ≥ 2, BAConArgLoop'' k C₀) ∧ BAConArgVec`;
`BAConArgLoop''`: `1(Ω_t)·max_{σ,a}|𝓛_t^{(k)}(z_t,g₀)| ≺ a^{k-1}`, `Ω_t = {max_{x,y}|(G_t)_{xy}| ≤ C₀}`, `a = (η_s/η_t)·Bctl_s`, law `seqP (sz.withLam 0)`.
Notation: `g₀ = BAflowLam0`, `g_s = √(s/t) g₀`, `m_s = m(E,g_s)`, `m₀ = m(E,g₀)`, `η_s = (1-s)Im m_s`, `η_t = (1-t)Im m₀`, `z̃ = √(t/s) z_s`,
`a₁ = Bctl_s` (at `sz.lam`), `Λ = 2+2d/𝔡`. Scratch (Python, no Lean): `scratchpad/T2237/{det,sb,mc,mc2}.py`.

### (i) Exponent table (d = 3; instance `κ=1/2, ε=𝔡=1/10, 𝔠=1/6, ε₁=c=1/2`)
| quantity | value | constraint / source | slack |
|---|---|---|---|
| `Λ` | 62 | `|E_n| ≤ 2+2d g_s ≤ 2+2d/𝔡` eventually (contrapositive of `BAm_eq_zero_of_gt` `FlowPins.lean:885`; `g_s ≤ g₀ = √t₀ g ≤ g ≤ 𝔡⁻¹` by `BAt0_lt_one`, `WO` `Defs/Sizes.lean:164`) | exact |
| `‖m₀‖, ‖m_s‖` | 0.9995 (n=0), 1.0000 (n≥1) | `≤ 1` (`BAward_avg` `MFixedPoint.lean:389` + Cauchy–Schwarz); `BASelf` at `m_s` from `κ ≤ Im m_s`, at `m₀` from `BAzztE_data` | 5e-4 / 0 |
| `t/s` | ≤ 2 | `c ≤ s ≤ t < 1`; `1 ≤ √(t/s) ≤ c^{-1/2} = 1.414` | 0.414 |
| `η_t/η_s` | 1 / .80 / .20 / .02 at `t = .5/.6/.9/.99` | `η_t ≤ (1-t)‖m₀‖ ≤ 1-s ≤ η_s/κ` | `≤ 2` |
| `‖z_t - z̃‖/η_s` | ≤ 1.39 (table below) | `≤ C_lin := Λ/(2cκ)+1/κ+1/(κ√c) = 128.83`: `E(1-√(t/s)) ≤ Λ(1-s)/(2c)`, `(1-t)‖m₀‖ ≤ 1-s`, `√(t/s)(1-s)‖m_s‖ ≤ c^{-1/2}(1-s)`, `1-s ≤ η_s/κ` | factor 92 |
| `BAztTilde_arith` `C` | `C_lin² = 16596.8` | conjuncts 1-4 of the check; 2: `√(t/s) ≥ 1`; 3: `≤ c^{-1/2}`; 4: `η_t ≤ η_s/κ` | — |
| `K = ‖z_t-z̃‖²/(Im z_t·Im z̃)` | `K a₁/a ≤ 1.37` at the pairs below | `K ≤ C_lin² η_s/η_t` (`Im z̃ ≥ η_s`) so `K a₁ ≤ C a` | 1.2e4 |
| `a₁/a = η_t/η_s` | ≤ 1 (s=t), 0.8, 0.2, 0.02 | recursion needs `a₁ ≤ a'`: take `a' = M a`, `M = max(1,1/κ) = 2`; `K a₁ ≤ C a ≤ C a'`; `Y_n ≺ a'^{n-1} = M^{n-1}a^{n-1}` (constant absorbed, `size → ∞`) | exact |
| `Bctl_s` (n=0) | `W^{-3}(1/(g²+1-s)+1/(L³(1-s))) = 6.20e-5` | `a₁⁻¹ ≤ size` (`Bctl_inv_le`, `ConArg.lean:624`): 1.6e4 ≤ 2.1e6; n=0..3: 6.2e-5, 1.9e-9, 4.3e-12, 5.7e-14 | 130× at n=0 |
| `Ω_t` threshold | `1/η_t = 2.001` at `t = .5` | `‖G_t‖_max ≤ ‖G_t‖ ≤ 1/Im z_t`: `Ω_t` is sure iff `C₀ ≥ 1/η_t`; the claim is for every `C₀>0` | — |
| recursion constant | `D1 = (k+2)(1+(k+C₀)C)` | `ConArg.lean:305`, linear in the base bound `Y_1 ≤ C₀` | depends on `C₀` only |
| `(eq:WO)` | `W^{-1.4} = 7.81e-3 ≤ g = 1.5625e-2 ≤ 10` | `W^{-d/2+𝔡} ≤ g ≤ 𝔡⁻¹` (eventually) | 2× / 640× |
| `Bandwidth` | `W = 32 ≥ N^{1/6} = 11.31` | `W ≥ N^𝔠` | 2.83× |

### (ii) Concrete instance and checks
Instance: `sz0` (n=0: `L=4, W=32, g=1/64, N=2097152`), `zSeq`, `s≡t≡1/2` (merged `inst_BAConArg'`, `FlowPins.lean:1396`; `flow_sz0 :1366`), `C₀ = 5/2 ≥ 1/η_t = 2.001`
(so `Ω_t` is the whole sample space and the left side is the full `‖𝓛_t^{(k)}‖`; also true for every smaller `C₀`), plus the pairs `s<t` below.
External hypothesis `STLmaxgL` at `s` (stochastic, stays a hypothesis): its deterministic limits are in `det.out` (`Bctl_s → 0`, `a₁⁻¹ ≤ size`, `WO`, `W ≥ N^𝔠`,
`κ ≤ Im m`; `m(E,g₀)` by iteration of `(self_m)` compared with `m_S/√t₀`, `BAzztE_data`).
```
$ python3 scratchpad/T2237/det.py      (verbatim, columns cut at 260)
Lambda= 62.0
n=0 L=4 W=32 N=2.10e+06 WO=True W>=N^c=True t0=0.6937 E=3.1e-18 Im m0=0.9995 |m0|=0.9995 |m0-mS/sqrt t0|=1.3e-18 eta_s=eta_t=0.4997 Bctl_s=6.20e-05 1/Bctl<=N:True
n=1 L=8 W=1024 N=5.50e+11 WO=True W>=N^c=True t0=0.6944 E=2.4e-20 Im m0=1.0000 |m0|=1.0000 |m0-mS/sqrt t0|=1.1e-16 eta_s=eta_t=0.5000 Bctl_s=1.87e-09 1/Bctl<=N:True
n=2 L=12 W=7776 N=8.12e+14 WO=True W>=N^c=True t0=0.6944 E=6.6e-21 Im m0=1.0000 |m0|=1.0000 |m0-mS/sqrt t0|=1.1e-16 eta_s=eta_t=0.5000 Bctl_s=4.26e-12 1/Bctl<=N:True
n=3 L=16 W=32768 N=1.44e+17 WO=True W>=N^c=True t0=0.6944 E=1.5e-21 Im m0=1.0000 |m0|=1.0000 |m0-mS/sqrt t0|=2.5e-22 eta_s=eta_t=0.5000 Bctl_s=5.69e-14 1/Bctl<=N:True
pair table (n=0), c=1/2,kappa=1/2: C_lin= 128.828
  s     t    | Im m_s  |z_t-zt|/eta_s  Im zt/eta_s (in [1,1/sqrt c=1.414])  eta_t/eta_s (<=1/kappa=2) |m_s|
 0.50  0.50 | 0.9995 | 0.0000  1.0000  1.0000 |0.9995  kappa<=Im m_s:True
 0.50  0.60 | 0.9996 | 0.2955  1.0954  0.7999 |0.9996  kappa<=Im m_s:True
 0.50  0.90 | 0.9997 | 1.1417  1.3416  0.2000 |0.9997  kappa<=Im m_s:True
 0.50  0.99 | 0.9997 | 1.3871  1.4071  0.0200 |0.9997  kappa<=Im m_s:True
 0.60  0.90 | 0.9997 | 0.9748  1.2247  0.2500 |0.9997  kappa<=Im m_s:True
$ python3 scratchpad/T2237/sb.py       (verbatim)
C=Clin^2=16596.8, M=max(1,1/kappa)=2.0
 s    t   | a1=Bctl_s   a=a1*eta_s/eta_t  a1/a(<=M)  K*a1/a (<=C)   1/eta_t (Omega_t sure iff C0>=)  a1^-1<=size
0.50 0.50 | 6.196e-05  6.196e-05  1.000  0.0000  2.0010  True
0.50 0.60 | 6.196e-05  7.746e-05  0.800  0.0797  2.5013  True
0.50 0.90 | 6.196e-05  3.099e-04  0.200  0.9715  10.0051  True
0.50 0.99 | 6.196e-05  3.099e-03  0.020  1.3674  100.0508  True
0.60 0.90 | 7.744e-05  3.098e-04  0.250  0.7758  10.0051  True
```
(`Im zt/eta_s` is `Im z̃/η_s`; `|z_t-zt|` is `|z_t-z̃|`.) All hypotheses of the pin hold at once (`N = 2·10⁶`, `E ≈ 0`, bulk `Im m ≈ 1`, `t₀ = 0.69`); no degenerate datum.
Sample check of the scaling, `Ω_t` and loop/vector claims (`W=2, L=4, g=1/64`, `N = 512`: small-`W` sample, *not* an instance of `(eq:WO)`; `V` block-diagonal GUE, `S^{(B)}(0)=I`):
```
$ python3 scratchpad/T2237/mc2.py | tail -7
S-B sample (W=2,L=4,g=1/64: small-W check, NOT an instance of (eq:WO)); Cmax=max_xy|G_t,xy|, a=(eta_s/eta_t)*a1, a1=Bctl_s
 t     eta_s/eta_t | Cmax  1/eta_t | Y1_t<=Cmax | L2_t/a  L3_t/a^2 | T2_s/a1 (T_2 of s-model) | Im Gt_vv  |Gt_vw|  bound eta_s/eta_t
 0.5        1.00 | 1.65 2.00 | True | 1.156 0.841 | 1.156 | 1.02 0.19 1.00
 0.6        1.25 | 1.93 2.50 | True | 1.199 0.832 | 1.156 | 1.03 0.21 1.25
 0.9        5.00 | 5.75 10.01 | True | 2.219 1.812 | 1.157 | 1.04 0.29 5.00
 0.99       50.01 | 33.57 100.05 | True | 10.308 9.203 | 1.157 | 1.02 0.71 50.01
```
(`scratchpad/T2237/mc.py` verifies `‖H_t(g₀) − √(t/s)H_s(g_s)‖_max ≤ 2.3e-16` at `t = .5,…,.99999`.) On this sample `L_k/a^{k-1}` stays `O(C₀-eff)` with `C₀-eff = Cmax`, as `D ∝ C₀`; `|Y_1| ≤ Cmax`.

### P1 (conjunct 1 in the `Ω_t` form; the recursion closes)
`Y_j = 1(Ω_t)·loopMax_j(blockMat H_t(g₀), z_t)`, `T_j = loopMax_j(blockMat H_t(g₀), z̃)`, `K` as in the table, `a₁ = Bctl_s`, `a' = M a`. Inputs of `conArg_continuity_recursion` (`Induction/ConArg.lean:125-375`, generic in the measure `P`; copy needed, `private`):
- `T_j ≺ a₁^{j-1}`: `H_t(g₀) − z̃ = √(t/s)(H_s(g_s) − z_s)` (scaling below), so each loop of `(H_t(g₀), z̃)` is `(s/t)^{j/2} ≤ 1` times the loop of `(H_s(g_s), z_s)` (band: `conArg_loopMax_tilde_le :448`); `STLmaxgL` at `(g_s, s)` is exactly `max|𝓛^{(j)}_{s}(z_s,g_s)| ≺ Bctl_s^{j-1}` (`FlowPins.lean:364`, `ztOf m_s E s = z_s`) and passes to `loopMax` per time (`conArg_loopMax_perTime :597`). The `T`-bounds carry no `Φ`.
- `Y_1 ≤ C₀` (`hY1`): on `Ω_t`, `|G_{ii}| ≤ C₀` gives `max|𝓛^{(1)}| ≤ C₀` (`E_a = W^{-d}1_{[a]}`, `∑_p bw_a(p) = 1`; `conArg_loopMax_one_le :519`); off `Ω_t` the product is `0 ≤ C₀`. No `Φ_t` and no lower bound on `Φ_s` is needed.
- `hodd`, `hrec`: `loopMax_odd_sq_le`, `loopMax_two_mul_le_tilde` (`Induction/Split.lean:598`, `ConArgDet.lean:1334`) need only `H` Hermitian and `Im z_t, Im z̃ > 0`. `H = blockMat(seqHflowBA g₀ t ω)` is Hermitian: `PsiI_isHermitian` (`Gauss/BlockAnderson.lean:65`) + `seqHflow_isHermitian` (`FineModel.lean:531`) (no merged `seqHflowBA` Hermiticity lemma: one private line-sized lemma). `Im z_t = η_t > 0` (`Im m₀ > 0` from `BAzztE_data`), `Im z̃ ≥ η_s > 0`.
- `ha1a`, `hK`: table; `a₁⁻¹ ≤ size`: `Bctl_inv_le`.
- Eventual hypotheses: `|E_n| ≤ Λ` and `WO` hold for `n ≥ n₀`; the finitely many `n < n₀` are handled by replacing `Y,T,K` there with `0` (all recursion hypotheses are then trivial) because `PerTimeDomAt` is an eventual statement in `n`.
Conclusion `Y_k ≺ a^{k-1}` per time for `k ≥ 1`, then to `(σ,a)` and `PrecL` (`conArg_norm_Lloop_le_loopMax :569`, `conArg_card_le :577`, `stochDomAt_of_perTimeDomAt`), as in `stConArg_holds :806`; `Sizes.tendsto_size` from `BAFlow.1.2.2.1`. The `loopFine`/`BALloop` ↔ `loopL(blockMat)` step is that of `conArg_norm_Lloop_eq :559` (`Lloop` is `loopFine` of `seqHflow`, `GLoopFlow.lean:158`; `BALloop` is `loopFine` of `seqHflowBA`, `FlowPins.lean:262`): same proof. The statement is the band `STConArg` shape (`Induction/Defs.lean:334-345`) with `etaT → etaOf`, `STLmax → STLmaxgL`; no premise on `Φ`.
**P2 (scaling and `z̃`)**: `H_t(g₀) = g₀Ψ + √t X = √(t/s)(g_sΨ + √s X)` since `√(t/s)√(s/t) = 1` and `√(t/s)√s = √t` (`BAhflow_scale`; numeric 2.3e-16 in `mc.py`). `BAGres_smul`: `(rH − rw)` inverse is `r⁻¹(H−w)⁻¹`; charge `false` since `conj(rw) = r conj w` (`r` real); `Ring.inverse` of a non-unit is `0` on both sides. Arithmetic: tables (i) and `sb.out`.
**P3 (vector part, unchanged from the previous verdict)**: `v^*G(z')w = v^*G(z_s)w + (z'−z_s)v^*G(z')G(z_s)w` (`z' = √(s/t)z_t`; resolvent identity); `|v^*G(z')G(z_s)w| ≤ √(Im G(z')_vv/y' · Im G_s,ww/η_s)` (Ward). `Im G(z')_vv ≤ max(η_s/y', y'/η_s)(2+2C_lin²) Im G_s,vv` (`BAimG_eta_mono`, `BAimG_poisson` at height `η_s`, `|z'−z_s| ≤ √(s/t) C_lin η_s`, `y' = √(s/t)η_t ≤ η_s/κ`). Hence `|(G_t)_{vw}|, Im (G_t)_{vv} ≤ C₁ η_s/η_t`, `C₁ = C₁(c, κ, Λ, C₀)`; `G_t(z_t) = √(s/t)G_s(z')`; deterministic on the event of the premise. Sample: `|G_t,vw| ≤ 0.71`, `Im G_t,vv ≈ 1.03` vs bound `η_s/η_t` up to 50.
**P4 (dependencies)**: `grep -n "GbEXP\|Kbound\|STKbound"` on `Induction/{ConArg,ConArgDet,Split,ScaleFacts,PerTimeCalc}.lean` returns no line: no `STGbEXP*`/`STKbound*` input; BA-G6, BA-K4 dropped. Private band helpers to copy (`Induction/ConArg.lean`, 8a8cfeb; line starts): `conArg_rpow_pow_mul_sub_one_le :71`, `conArg_det_mul :89`, `conArg_of_le_left :97`, `conArg_odd_of_even :104`, `conArg_continuity_recursion :125-375`, `conArg_inv_smul :386`, `conArg_green_smul_mul :400`, `conArg_Gres_smul_mul :409`, `conArg_foldr_smul_mul :422`, `conArg_loopL_smul_mul :435`, `conArg_loopMax_tilde_le :448`, `conArg_norm_trace_mul_Eblk_le_of_diag :492`, `conArg_Gres_false :506`, `conArg_loopMax_one_le :519`, `conArg_gres_blockMat_true :538`, `conArg_norm_Lloop_eq :559`, `conArg_norm_Lloop_le_loopMax :569`, `conArg_card_le :577`, `conArg_loopMax_perTime :597`, `conArg_Bctl_inv_le :624`.

### Verdicts
- `BAConArg''` / its proof (target 1, S-B): **PASS** (P1: recursion closes with `a' = max(1,1/κ)·a`, base `Y_1 ≤ C₀` on `Ω_t`, `K a₁ ≤ C a'`; no lower bound on `Φ`).
- `baConArgLoop''` (conjunct 1, `∀ C₀ > 0`, `k ≥ 2`): **PASS** (P1, P2).
- `baConArgVec_holds` (conjunct 2): **PASS** (P3).
- `BAConArgHyp`, `BAhflow_scale`, `BAGres_smul`, `BAimG_eta_mono`, `BAimG_poisson`, `BAself_norm_le_one`, `BAenergy_le`, `BAztTilde_arith`: **PASS**. `BAimTrace_compare`: **PASS** as stated (deterministic: `η_t > 0` from `Im m₀ > 0`); the S-B route does not use it.
- `BAConArg'` itself (`Φ_t` form): not a target after Amend 1; not shown false, not provable from its premises by the band route (the `Φ_t` factor needs a lower bound on `Φ_s` and `|tr G_tE_a| ≲ Φ_t`; sample `Y_1/Φ_t = 347` at `t = 0.99999`, `mc.out`).
- Overall: **PASS** for the amended targets.

## (b) Script output — Tue Oct  6 03:56:58 UTC 2026 (stage 1b started 03:10:58 UTC; first `date -u` of the stage)
Branch `t/T2237`, commit `e258fb7` on `05e5052`; `git diff --stat 05e5052 HEAD`:
```
 RBM3D/BA/ConArg.lean   | 1982 ++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |    2 +-
 2 files changed, 1983 insertions(+), 1 deletion(-)
$ lake build RBM3D.BA.ConArg 2>&1 | grep -E 'Build completed|error|BA/ConArg.lean'   # no line mentions BA/ConArg.lean: no warning, no error
Build completed successfully (3745 jobs).
$ lake env lean RBM3D/BA/ConArg.lean; echo exit=$?   # direct compile of the 1982 lines, run 03:52:38 UTC
exit=0, no output
$ grep -c 'sorry\|admit\|native_decide\|^axiom' RBM3D/BA/ConArg.lean
0
$ lake env lean axioms.lean   # #print axioms: the 11 theorems and the main instance (6 further theorems, `bandFM_omegaC` and 5 instance theorems: the same three axioms)
'baConArg''_holds': [propext, Classical.choice, Quot.sound]
'baConArgLoop''_holds': [propext, Classical.choice, Quot.sound]
'baConArgVec_holds': [propext, Classical.choice, Quot.sound]
'BAimTrace_compare': [propext, Classical.choice, Quot.sound]
'BAhflow_scale': [propext, Classical.choice, Quot.sound]
'BAGres_smul': [propext, Classical.choice, Quot.sound]
'BAimG_eta_mono': [propext, Classical.choice, Quot.sound]
'BAimG_poisson': [propext, Classical.choice, Quot.sound]
'BAself_norm_le_one': [propext, Classical.choice, Quot.sound]
'BAenergy_le': [propext, Classical.choice, Quot.sound]
'BAztTilde_arith': [propext, Classical.choice, Quot.sound]
'ConArgInst.inst_baConArg''': [propext, Classical.choice, Quot.sound]
```
Statements, extracted by script from `RBM3D/BA/ConArg.lean` (`python3 extract.py`):
```lean
-- BA/ConArg.lean:55
def FlowFM.omegaC {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t C₀ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n t ω x y‖ ≤ C₀ then 1 else 0
-- BA/ConArg.lean:61
def BAConArgLoop'' {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (k : ℕ) (C₀ : ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => (baFMz sz z).omegaC n (t n) C₀ ω * ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
    (fun n _ _ => ((etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
          (baFMz sz z).eta n (t n)) * sz.Bctl n (s n)) ^ (k - 1))
-- BA/ConArg.lean:70
def BAConArg'' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) →
        STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s →
        ∀ C₀ : ℝ, 0 < C₀ → (∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz z s t k C₀) ∧ BAConArgVec sz z s t
-- BA/ConArg.lean:83
def BAConArgHyp {d : ℕ} (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  0 < κ ∧ 0 < ε ∧ 0 < 𝔡 ∧ 0 < ε₁ ∧ BAFlow sz κ ε 𝔠 𝔡 z ∧ (∀ n, ε₁ ≤ s n) ∧ (∀ n, s n ≤ t n) ∧
    (∀ n, t n < 1) ∧ (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) ∧
    STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s
-- BA/ConArg.lean:1824
theorem baConArg''_holds (d : ℕ) : BAConArg'' d := by
-- BA/ConArg.lean:1241
theorem baConArgLoop''_holds (d : ℕ) :
    ∀ (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t →
      ∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz z s t k C₀ := by
-- BA/ConArg.lean:1639
theorem baConArgVec_holds (d : ℕ) :
    ∀ (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t →
      BAConArgVec sz z s t := by
```
```
$ diff <(sed -n 630,636p RBM3D/BA/FlowPins.lean) <(sed -n 70,77p RBM3D/BA/ConArg.lean)   # BAConArg' vs BAConArg''
1c1
< def BAConArg' (d : ℕ) : Prop :=
---
> def BAConArg'' (d : ℕ) : Prop :=
7c7,8
<         (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t
---
>         ∀ C₀ : ℝ, 0 < C₀ → (∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz z s t k C₀) ∧ BAConArgVec sz z s t
> 
$ python3 stmtdiff.py | paste -sd' ' -   # whitespace-normalised body of each `X_stmt` in docs/tickets/checks/T2237-check.lean vs theorem X here
BAhflow_scale: IDENTICAL BAGres_smul: IDENTICAL BAimG_eta_mono: IDENTICAL BAimG_poisson: IDENTICAL BAself_norm_le_one: IDENTICAL BAenergy_le: IDENTICAL BAztTilde_arith: IDENTICAL BAimTrace_compare: IDENTICAL baConArgVec_holds: IDENTICAL BAConArgHyp: IDENTICAL
$ lake env lean accept.lean   # check section 2/3 text, then `example : X_stmt := X` (9 lemmas), `@BAConArgHyp = @T2237Check.BAConArgHyp := rfl`, `BAConArg'' d`, conjunct 1
exit 0 ; output lines        0
```
Compiled nonempty instance (same file, namespace `RBM.BA.ConArgInst`, lines 1841-1982; `sz0`, `zSeq`; at `n = 0`: `L = 4, W = 32, g = 1/64, N = 2097152`):
```lean
theorem inst_baConArg''
    (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    (∀ k : ℕ, 2 ≤ k →
        BAConArgLoop'' sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) k 2) ∧
      BAConArgVec sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) :=
  baConArg''_holds 3 (1 / 2) (1 / 10) (1 / 10) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by norm_num) inst_premise_diag hL 2 (by norm_num)
```
Other instances there (all deterministic hypotheses discharged): `inst_BAConArgHyp`, `inst_baConArgLoop''` (every `C₀>0`, `k≥2`), `inst_baConArgVec`, `inst_hflow_scale` (`s=1/2<t=3/4`, every `ω`), `inst_imTrace` (every `ω`, `a`), and `example`s for `BAGres_smul` (`diag(1,-1)`, `r=2`), `BAimG_eta_mono`, `BAimG_poisson` (`diag(1,-1)`, `e₀`), `BAself_norm_le_one`, `BAenergy_le` (flow point `MFixedPointInst.P`), `BAztTilde_arith` (`E=1/10, s=1/2, t=3/4, m₀=1/10+i/2, m_s=i`), `bandFM_omegaC`.  The one hypothesis left, `hL = STLmaxgL …`, is the BA chain's owed pin (in `owedProps`).
```
$ for n in <21 new public names>; do grep -rnwF -- $n RBM3D | grep -v 'BA/ConArg.lean\|Probe/'; done   # name-clash scan
BAConArg'' -> RBM3D/Test/Axioms.lean:379:   `RBM.BA.BAConArg',            -- `lem_ConArg_BA` in the `Φ_t` form (T2197 Amend 
baConArg''_holds -> RBM3D/Test/Axioms.lean:379:   `RBM.BA.BAConArg',            -- `lem_ConArg_BA` in the `Φ_t` form (T2197 Amend 
ConArgInst -> RBM3D/Induction/ConArg.lean:832:namespace RBM.Ind.ConArgInst
ConArgInst -> RBM3D/Induction/ConArg.lean:874:end RBM.Ind.ConArgInst
(every other name: 0 matches; these hits are the registry comment and `RBM.Ind.ConArgInst`, another namespace)
$ python3 ports.py   # port citations; band = RBM3D/Induction/ConArg.lean at 8a8cfeb (itself RBM2D `ConArg.lean` at c9a24cf <- RBM1D `ContinuityAssembly.lean` at 86573b9); copies are `private ConArg_*`
copied/ported helper: band `Induction/ConArg.lean` line (8a8cfeb) -> `BA/ConArg.lean` line
  conArg_rpow_pow_mul_sub_one_le: 71 -> 684
  conArg_det_mul: 89 -> 702
  conArg_of_le_left: 97 -> 710
  conArg_odd_of_even: 104 -> 717
  conArg_continuity_recursion: 125 -> 738
  conArg_inv_smul: 386 -> 273
  conArg_green_smul_mul: 400 -> 286
  conArg_foldr_smul_mul: 422 -> 320
  conArg_loopL_smul_mul: 435 -> 332
  conArg_loopMax_tilde_le: 448 -> 343
  conArg_norm_trace_mul_Eblk_le_of_diag: 492 -> 998
  conArg_Gres_false: 506 -> 1012
  conArg_loopMax_one_le: 519 -> 1025
  conArg_gres_blockMat_true: 538 -> 1044
  conArg_card_le: 577 -> 1063
  conArg_Bctl_inv_le: 624 -> 1082
  conArg_loopMax_perTime: 597 -> 1216
  conArg_norm_Lloop_eq: 559 -> 1195
recursion block (band :65-376, renamed conArg_->ConArg_) vs `section Recursion` here: 2 differing lines
    -open PerTimeCalc.PerTime
    +open RBM.Ind.PerTimeCalc.PerTime
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/ConArg.lean
9e0f275
 RBM2D/Induction/ConArg.lean | 156 ++++++++++++++------------------------------
 1 file changed, 50 insertions(+), 106 deletions(-)
$ git -C ../RBM1D --no-optional-locks log -1 --format=%h; git -C ../RBM1D --no-optional-locks diff --stat 86573b9 HEAD -- RBM1D/Loop/ContinuityAssembly.lean
de0de42
 RBM1D/Loop/ContinuityAssembly.lean | 368 +------------------------------------
 1 file changed, 10 insertions(+), 358 deletions(-)
$ git diff 05e5052 HEAD -- RBM3D/Test/Axioms.lean | grep '^[+-] ' | cut -c1-110   # registry: BAConArg' owed -> superseded (Amend 1)
-   `RBM.BA.BAConArg', -- `lem_ConArg_BA` repaired (`7_8:1956-1987`, premise `κ ≤ Im m(E, g_s)`; Amend 1, DECI
+   `RBM.BA.BAConArg',            -- `lem_ConArg_BA` in the `Φ_t` form (T2197 Amend 1): not refuted, not prova
$ lake build RBM3D   # whole library incl. the changed Axioms.lean; run 03:55:22 UTC (cached, 1.4 s; the first run, before the last docstring edits, rebuilt it)
Build completed successfully (4048 jobs).
$ printf 'import RBM3D\nimport RBM3D.BA.ConArg\n#assert_rbm_axioms\n' > precheck.lean; lake env lean precheck.lean   # registry pre-check (§20 (2)), finished 03:54:47 UTC
exit 0;  axiom audit: 7148 theorems, 2398 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).;  premises found by scanning: 144 (borrowed 1, owed 97, structural 33, refuted 6, superseded 7).
```

Narrative.
- **Target.** Target 1 is the Amend 1 successor `BAConArg''` (S-B), pinned and proved here: the hypotheses of `BAConArg'` verbatim, then for every `C₀ > 0`, `BAConArgLoop''` (indicator `FlowFM.omegaC`, right side `((η_s/η_t) Bctl_s)^{k-1}`, no `Φ_t`) for `k ≥ 2` and `BAConArgVec`.  `BAConArg'` (the `Φ_t` form) is not proved and not refuted; `Axioms.lean`: moved from `owedProps` to `supersededProps`; `STLmaxgL` stays owed (hypothesis of every instance).
- **Conjunct 1** = port of the band `conArg` (`Induction/ConArg.lean:673-789`).  BA changes: the tilde bound uses `BAhflow_scale`, `BAGres_smul` (`ConArg_loopMax_tilde_le`) at the shifted parameter `z̃ = √(t/s) z_s`; `T_j ≺ a₁^{j-1}` comes from `STLmaxgL` at `(g_s, s)` by event inclusion into the union event (`ConArg_loopMax_perTime`), the union over `(σ,a)` goes back inside `P` by `stochDomAt_of_perTimeDomAt`; the arithmetic is `BAztTilde_arith` (inputs `|m| ≤ 1`, `κ ≤ Im m_s`, `|E_n| ≤ Λ`), whose 4th conjunct `η_t ≤ C_a η_s` replaces the band's `η_t ≤ η_s`, so the copied recursion runs at `a' = M a`, `M = max(1, C_a)`, then `perTimeCalc_mono` with the constant `M^{k-1}`.
- **Section (a) not edited, no (a′).**  Two implementation choices differ from (a): `|E_n| ≤ Λ` for all `n` with `Λ = 2 + 2d(𝔡⁻¹ + Σ_{i<n₀}|g_i|)` (`ConArg_energy_bound`, `n₀` from `(eq:WO)`) instead of the cut-off of `Y, T, K` for `n < n₀`; and `M = max(1, C_a)` instead of `max(1, 1/κ)`.  No statement or verdict of (a) changes.
- **Conjunct 2** is deterministic on the event of its premise: `G_t(z_t; H_t(g₀)) = r⁻¹ G(a; H_s(g_s))`, `a = r⁻¹ z_t`, `r = √(t/s) ∈ [1, ε₁⁻¹]` (`ConArg_setup`); the spectral theorem gives `BAimG_eta_mono`, `BAimG_poisson` and `ConArg_offdiag` (resolvent identity and Cauchy-Schwarz in the eigenbasis); `C₁ = A₁ + K₀C_a + Z + 1`, `A₁ = (C_a² + ε₁⁻¹)(2 + 2C_a)K₀`; the event inclusion is `HighProbAt.mono`.
- **Other.** `BAimTrace_compare` is proved (unused by the S-B route; `ConArg_loop1_im`: `Im(L⁺−L⁻) = 2 Σ_p bw_a(p) Im G_pp`); the optional `rfl` bridge `bandFM_omegaC` is included; the optional `BAConArg'_imp''` is not written.
- **Names.** `T2237Check.baConArgLoop_holds_stmt` is the `Φ_t` form (`BAConArgLoop`), superseded by Amend 1 and not proved; its successor theorem is `baConArgLoop''_holds` (the only deviation from the ticket's theorem names).  Size: 1982 lines, about 480 of them copies (recursion block 312, base case 70, scaling and counting helpers); not split (section (a) has no size estimate).
- **Hub.** Root import `import RBM3D.BA.ConArg` after the last import line of `RBM3D.lean`; the `Axioms.lean` diff is 1 deletion + 1 insertion.

## (c) Verified Mathlib names (each compiled in `RBM3D/BA/ConArg.lean`; the first ones also by `#check` in `names.lean`)
- `Real.sum_mul_le_sqrt_mul_sqrt` (`Mathlib/Analysis/Real/Sqrt.lean:500`), `sq_sum_le_card_mul_sum_sq` (`Algebra/Order/Chebyshev.lean:144`), `Real.sqrt_le_sqrt`, `Real.sqrt_le_one`, `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.sqrt_mul`, `Real.le_sqrt_of_sq_le`
- `Matrix.IsHermitian.spectral_theorem` (`hH.eigenvectorUnitary`, `hH.eigenvalues`), `Matrix.star_mulVec`, `Matrix.dotProduct_mulVec`, `Matrix.mulVec_mulVec`, `Matrix.mulVec_diagonal`, `Matrix.mulVec_single`, `Matrix.smul_mulVec`, `dotProduct_smul`, `Matrix.inv_smul`, `Matrix.inv_eq_right_inv`, `Matrix.nonsing_inv_eq_ringInverse`
- `Complex.inv_im`, `Complex.im_ofReal_mul`, `Complex.abs_re_le_norm`, `Complex.im_le_norm`, `Complex.mul_conj`, `Complex.sq_norm`, `Complex.normSq_apply`, `Complex.re_add_im`
- `pow_le_pow_iff_left₀`, `norm_le_norm_add_norm_sub'`, `div_le_div_of_nonneg_left`, `div_le_div_of_nonneg_right`, `div_le_div_iff₀`, `inv_le_one_of_one_le₀`, `div_le_one_of_le₀`, `one_le_div`, `Finset.single_le_sum`, `exists_lt_of_lt_ciSup`, `eventually_atTop`, `measure_mono`
- Verified unqualified-absent (project names live under `RBM.Ind`): `Gres_eq_green_zSig`, `zSig_true`, `zSig_false` are `RBM.Ind.*`; `perTimeCalc_mono` is `RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_mono` (the band's `open PerTimeCalc.PerTime` resolves only inside `namespace RBM.Ind`).  `private` declarations of a module are invisible from a scratch file that imports it.

## (d) Open issues and paper-delta candidates
- **T2237a** (`lem_ConArg_BA` (1), `7_8:1956-1981`): used in the event form `1(Ω_t) max|𝓛^{(n)}_t| ≺ ((η_s/η_t) W^{-d}B_{s,0})^{n-1}` for every `C₀ > 0`, `Ω_t = {‖G_t‖_max ≤ C₀}`, with the premise `κ ≤ Im m(E, g_s)` (T2197c); the printed factor `max_a tr(Im G_t E_a)` (`7_8:1965`) would need a lower bound on `Φ_s` and `|tr G_tE_a| ≲ Φ_t`, neither of which follows from `(eq:loopbound_s)` (section (a), P1).
- **T2237b**: the BA arithmetic of `z̃` replaces the band's `|E| ≤ 2 − κ` and `η_t ≤ η_s` by `|E| ≤ 2 + 2d|g_s| ≤ Λ`, `‖m‖ ≤ 1` (`BAself_norm_le_one`) and `η_t ≤ C_a η_s` (`BAztTilde_arith`, constants in `(ε₁, κ, Λ)`).
- **T2237c** (observation): the constants depend on the sequence only through `Λ`, which absorbs the finitely many `n < n₀` before `(eq:WO)`; for `n ≥ n₀` it is `2 + 2d/𝔡`.
- **Consumers switch** (named in Amend 1, not written here): BA-S3 `BAStep1_of_parts'` (`hC : BAConArg'' d`, `BAConArgLoop_congr` gets a `''` twin), BA-S2b `BABootstrap'`.  Every instance carries `STLmaxgL` at the `g_s` carrier (owed, BA chain); `inst_BAConArg'` of `FlowPins.lean:1396` stays a conditional instance.
- `BAself_norm_le_one`, `BAenergy_le`, `BAimG_eta_mono`, `BAimG_poisson`, `BAimTrace_compare` are public and reusable (e.g. a `Φ_t`-type consumer, if a lower bound on `Φ_s` is ever supplied).
