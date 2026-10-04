Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 10:13:50 UTC 2026

Notation: `N = sz.size n = (W L)^d`, `δ = detFlucDelta Ψ θ` (`FlucThreshold.lean:432`), `θ = detFlucTheta a τ = min(a/8, τ/32, 1/8)` (`:442`), `Ψ' = 2δ`, `ρ = 2Ψ' = 4δ`. Sources read: ticket; RBM2D `Green/{FlucAvgDet,IBPDet,GbEXP}` at `c9a24cf`; merged `LocalLaw.lean` (pins :166-192, :850, :917), `FlucThreshold.lean`, `FlucIterGain.lean:823`, `FlucVanish.lean` (`BoundedWeight` :941, `boundedWeight_svarF` :1169), `LDE.lean:410-450`, `IBPRem.lean` (:126, :514), `CondDom.lean` (:209, :295), `IBP.lean:1227`, `Pins.lean:224,1152`, `Defs/Sizes.lean`; reports T2123 (a)(d), T2114 (d).

### (i) Exponent table
| # | Quantity | Value (`d=3`) | Constraint | Slack |
|---|---|---|---|---|
| 1 | Floor (pin FA/IBP, `LocalLaw.lean:176,186`) | `W^{-d/2} ≤ Ψ` (RBM2D `W⁻¹ ≤ Ψ`) | holds at `Ψ = W^{-3/2}` with equality; `W^{-1} ≤ W^{-3/2}` is FALSE, so no step may use `W⁻¹ ≤ Ψ` (output G) | `0` at the floor |
| 2 | Ceiling `Ψ ≤ N^{-a}` | `a = 1/4` on `sz0`: `N^{-a} = 2.6e-2` vs `Ψ = 5.5e-3` at `n=0` | exists since `W ≥ N^{1/6}`; `W^{-3/2} ≤ N^{-a}` needs `a ≤ 1/4` for `L = W`, `5/12` on `sz0` asymptotically | output A |
| 3 | `θ` after `τ` (FA absorb) | `τ=1: 1/32`; `τ=1/4: 1/128` | `θ ≤ a/4 = 1/16`, `θ ≤ 1/4`, `θ < τ/16` (`detFlucTheta_specs`, `:445`) | `τ/16 - θ = 1/32` (`τ=1`), `1/128` (`τ=1/4`); output B |
| 4 | Markov step | `‖flucAvg‖ ≺ 4δ²` from `E|X|^{2p} ≤ (2p+1)(2p)^{2p}(2^{2p-1} ρ B_p)^{2p}`, `B_p = (8C_{2p}+4)δ` (M=K=2p), `ρB_p = 4(8C_{2p}+4)δ²` | `hρ1: ρ ≤ 1` iff `δ ≤ 1/4` (`detFlucDelta_le_quarter`); constants depend on `p` only; no `d` in any exponent | `δ ≤ 1/4` always (`min`) |
| 5 | `θ < τ/16` to `≺ Ψ²` (FA absorb) | `N^{τ/2}·4δ² ≤ N^τ Ψ²` | `δ ≤ N^{2θ}Ψ` (needs `(N+4)^{-2} ≤ Ψ`, `N ≥ 4`), `N^{4θ} ≤ N^{τ/4}` (`θ ≤ τ/16`), `4 ≤ N^{τ/4}`: exponents `τ/2+τ/4+τ/4 = τ` | `τ=1`: from `n=0`; `τ=1/4`: `n≥1`; `τ=1/16`: `n≥61` (D) |
| 6 | FA floor chain | `(N+4)^{-2} ≤ N^{-2} ≤ N^{-1/2} ≤ W^{-d/2} ≤ Ψ`, the middle step is `W^d ≤ (WL)^d = N` (`L ≥ 1`, for every `d`; same proof as `IBPRem_hΨlow_of_floor`) | RBM2D used `W ≤ size` (`W_le_self`, `CondDom.lean:295`, needs `1 ≤ d`) with `W⁻¹ ≤ Ψ`; here `W^d ≤ N` needs no `hd` | holds at `n=0,3,10^4` (E: `Nm2_le_Psi`) |
| 7 | Weight families | row `T_j = svarF i j`, `c = W^{-d}`, `A` = block of `i` and its `2d` neighbours, `#A = (2d+1)W^d = 7W^3` (`card_Sblk_support`, `LDE.lean:419`), `∑T = 1`; block `T = blkCoef2`, `c = W^{-d}`, `#A = W^d` (`card_blockAvg_support`) | `BoundedWeight T c A` (`:941`): `0 ≤ T ≤ c`, `∑T ≤ 1`; mass bound `c·#A ≤ 1` is NOT used (row: `c·#A = 7 > 1`, DECISIONS §30) | row `c·#A = 7`; `∑T = 1` exactly |
| 8 | `c ≤ ρ²` at `ρ = 4δ` | `(W^d)⁻¹ ≤ (2(2δ))²`, second conjunct of `flucGain_of_localLaw` (`:868`); proof `W^{-d} = (W^{-d/2})² ≤ Ψ² ≤ (4δ)²` | RBM2D `(W⁻¹)² ≤ ρ²` is false for `n ≥ 1` (output B, `d2form False`) | `c/(4δ)² = 2.5e-2, 5.3e-3, 8e-7` at `n=0,3,10^4` (`τ=1`) |
| 9 | `2p ≤ #A` (Markov/moment) | needs `p ≤ W^d/2` (block, binding), `eventually_le_W` (`LDE.lean:450`: `W → ∞` from `SizeTendsto`+`Bandwidth`) | each fixed `p` eventually | output C: `p=10^6`: `n≥1`; `p=10^9`: `n≥2` (block) |
| 10 | IBP union over rows | `#Idx = N` sites (`flucAvg_card_Idx_eq_size`, `LDE.lean:428`), each at `(τ/2, D+2)`; `N·N^{-(D+2)} = N^{-(D+1)} ≤ N^{-D}` | `D → D+2` spent (`D+1` would do); the `hΩ` union (`highProbAt_detFlucDelta_of_localLaw`) has `N²` pairs, `D+2` | slack `N^{-1}` (E `union_row`, D=3) |
| 11 | IBP bound | `a = N^{τ/2}`, `A = aΨ²`, `A_diag = a`; remainder `≤ A + S_ii A_diag ≤ 2aΨ²` (`norm_condExpDiag_sub_le_offdiag`, `CondDom.lean:209`), `S_ii = W^{-d}(1+2dg²)⁻¹ ≤ W^{-d} ≤ Ψ²` (`svarF_diag`, `FineModel.lean:61`; floor) | `2a ≤ a²` iff `N^{τ/2} ≥ 2`; then `2aΨ² ≤ N^τΨ²` | `τ=1`: from `n=0` (`N^{1/2}=1448`); `τ=1/16`: `n ≥ 1` (D) |
| 12 | `K_env` (`hEnv`) | `K_env = 3`: `η ≥ N^{-1}` gives `(η⁻¹+1)² ≤ (N+1)² ≤ N³` for `N ≥ 3` | `flucThreshold_etaInv_le_rpow_of_lower` (`FlucThreshold.lean:766`) | `N ≥ 4` eventually; `sz0 n=0: N=2.1e6` (E `env_A/env_B`) |
| 13 | `hΨlow` (`B=1`) | `N^{-1} ≤ Ψ·Ψ` from `W^{-d/2} ≤ Ψ`, `W^d ≤ N` (`IBPRem_hΨlow_of_floor`, `IBPRem.lean:126`, every `d`, every `n`) | replaces RBM2D `IBPDet_hΨlow` (floor `W⁻¹`) | `N/W^d = L^d = 64` at `n=0` |
| 14 | `hΨ1`, `hδ1` | `Ψ·Ψ ≤ 1` from `Ψ ≤ N^{-a} ≤ 1` (`N ≥ 1`); `δ ≤ 1/4 ≤ 1/2` | `hδ1` is `detFlucDelta_le_quarter` then `1/4 ≤ 1/2` | `1/4` |
| 15 | `hη` | `K_η = 1`: `eta_lower_of_rangeCond` (`LocalLaw.lean:917`), `(zt).im = etaT` (`etaT_eq_zt_im`, `GLoop.lean:79`) | `N^{δ_R} ≥ 1/c0`, `c0 = √(κ(4-κ))/2`; `κ=1/10`: `N ≥ 1.1e5` | `sz0 n=0: N=2.1e6` (H) |
| 16 | `hEnv`, `hΩ` sources | `hEnv`: row 12; `hΩ := highProbAt_detFlucDelta_of_localLaw sz hsz ha hθ0 hθa hθ1 hΨhi hll` at `θ = detFlucTheta a 1` (`1/32` here) | `0<a`, `0<θ ≤ a/4`, `θ ≤ 1/4`; `hΨhi` from the pin's `∀ᶠ (floor ∧ ceiling)` by `Eventually.mono` | as rows 3, 2 |
| 17 | DECISIONS §29 | (1) `0 ≤ t` used only to feed `norm_condExpDiag_sub_le_offdiag` (`ht0`) and the pins; `t < 1` gives `η > 0`; `|E n| < 2` from `|E n| < 2-κ`. (2) no `ilambda`, no window. (3) `L^d ≤ W^K` unused (`#Idx = N` exact; `W^d ≤ N` from `L ≥ 1`). (4) pins' `Ψ`-floor/ceiling are `∀ᶠ n`, conclusions `∀ᶠ n` (`PerTimeDomAt`); `∀ n` only on `E`, `t`, `Ψ ≥ 0` as in the pins | | none |
| 18 | `hd` | `fixedTimeFAThm`: none predicted (`flucGain_of_localLaw`, `integral_norm_flucAvg_pow_le_iter_budget`, `boundedWeight_svarF`, `eventually_le_W` carry no `hd`; `3 ≤ L` is `sz.three_le_L`). `ibpDetThm`: `1 ≤ d` (from `perTimeDomAt_ibpRem`, `IBPRem.lean:514`; via `perTimeDomAt_of_le_left_on`, D200). `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds`: `3 ≤ d` (`LocalLaw.lean:850`) | `ibpDetThm (by omega)` inside `gbEXPV3` | |

### (ii) One concrete nondegenerate instance
`d = 3`, `sz0` (`Defs/Sizes.lean:258`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n=0`: `L=4, W=32, N=2097152`), `κ = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`, `δ_R = 1/10`, `E ≡ 0` (`mE 0 = i`), time `tA ≡ 1/2` (`η = 1/2`) and `tB = 1 - 2N^{-1/2}` (`η = 2N^{-1/2}`, `t → 1`; `RangeCond`: `N^{-9/10} ≤ 2N^{-1/2}`), `Ψ = W^{-3/2}` (the floor), `a = 1/4`. External hypothesis `LocalLawDetSeq sz0 E t Ψ` (the owed `GavLGEX` local law, `Acta:4564`): its limit check is the table rows 3-14 at `n = 0, 3, 10^4` below plus T2123 (a) (ii) (as quoted there: measured `rms|G_kk - m| ∝ W^{-1.494}` at `d=3` against `W^{-3/2}`, source `docs/reports/T2117-prove.md`, not re-read); not derived here.
`cd scratchpad/T2126 && python3 inst_short.py` (mpmath, 80 digits; `inst_short.py` is Python, no Lean), output verbatim:
```
== (A) hypotheses of the pins, d=3, sz0, E=0, a=1/4, Psi=W^(-3/2); times tA=1/2, tB=1-2N^(-1/2)
n=0 L=4 N~2.097e+06 Psi=5.524e-03 N^-a=2.628e-02 all=True []
n=3 L=16 N~1.441e+17 Psi=1.686e-07 N^-a=5.132e-05 all=True []
n=10000 L=40004 N~2.101e+78 Psi=5.520e-33 N^-a=2.627e-20 all=True []
== (B) weights: c=W^-d <= (4 delta)^2, delta=detFlucDelta(Psi,theta(a,tau)); #A_blk=W^3, #A_row=7 W^3
tau=1.0 theta=0.03125  theta<=a/4:True theta<tau/16:True theta<=1/4:True
  n=0 delta=8.706e-03 4delta/Psi=6.3 W^-3=3.052e-05 (4delta)^2=1.213e-03 ratio c/(4delta)^2=2.516e-02 ok=True d2form (W^-1)^2<=(4delta)^2: True
  n=3 delta=5.795e-07 4delta/Psi=13.7 W^-3=2.842e-14 (4delta)^2=5.373e-12 ratio c/(4delta)^2=5.290e-03 ok=True d2form (W^-1)^2<=(4delta)^2: False
  n=10000 delta=1.547e-30 4delta/Psi=1.12e+03 W^-3=3.047e-65 (4delta)^2=3.830e-59 ratio c/(4delta)^2=7.957e-07 ok=True d2form (W^-1)^2<=(4delta)^2: False
tau=0.25 theta=0.0078125  theta<=a/4:True theta<tau/16:True theta<=1/4:True
  n=0 delta=6.190e-03 4delta/Psi=4.48 W^-3=3.052e-05 (4delta)^2=6.130e-04 ratio c/(4delta)^2=4.979e-02 ok=True d2form (W^-1)^2<=(4delta)^2: False
  n=3 delta=2.296e-07 4delta/Psi=5.45 W^-3=2.842e-14 (4delta)^2=8.431e-13 ratio c/(4delta)^2=3.371e-02 ok=True d2form (W^-1)^2<=(4delta)^2: False
  n=10000 delta=2.259e-32 4delta/Psi=16.4 W^-3=3.047e-65 (4delta)^2=8.162e-63 ratio c/(4delta)^2=3.733e-03 ok=True d2form (W^-1)^2<=(4delta)^2: False
== (C) 2p <= #A: first n with 2p <= W^3 (block) and 2p <= 7 W^3 (row), W=(2(n+1))^5
  p=1 first n: block 0 (W^3=32768)  row 0
  p=10000 first n: block 0 (W^3=32768)  row 0
  p=1000000 first n: block 1 (W^3=1073741824)  row 1
  p=1000000000 first n: block 2 (W^3=470184984576)  row 1
== (D) 2 N^(tau/2) <= N^tau  <=>  N^(tau/2)>=2 ; and 4 <= N^(tau/4) (FA absorb): first n
  tau=1.0 first n: N^(tau/2)>=2: 0 ; N^(tau/4)>=4: 0  (N=2.097e+06)
  tau=0.25 first n: N^(tau/2)>=2: 0 ; N^(tau/4)>=4: 1  (N=5.498e+11)
  tau=0.0625 first n: N^(tau/2)>=2: 1 ; N^(tau/4)>=4: 61  (N=3.843e+38)
== (E) IBP / FA chain at the floor, E=0, tB (eta=2N^-1/2) and tA (eta=1/2), tau=1
  n=0 all=True [] (failing keys listed)
  n=3 all=True [] (failing keys listed)
  n=10000 all=True [] (failing keys listed)
== (F) the ceiling 2*size^(tau/2)*Psi^2 <= size^tau*Psi^2 at n=0 (N=2097152), tau=1: True
== (G) RBM2D floor W^-1 <= Psi fails at the pin floor Psi=W^(-3/2): [(0, False), (1, False), (3, False)]
== (H) eta_lower_of_rangeCond threshold: c0=sqrt(k(4-k))/2, need N^dR >= 1/c0
  c0=0.3122 1/c0=3.2026 N>= 1.135e+05 ; sz0 n=0 N=2.097e+06 ok=True
```
Reading: (A) every pin premise (floor, ceiling, `Bandwidth 1/6`, `WO` at `𝔡=1/10`, `RangeCond`, `η ≥ N^{-1}`) holds at `n = 0, 3, 10^4` for both times. (B) `W^{-d} ≤ (4δ)²` for both families at `τ = 1, 1/4`; RBM2D's `(W⁻¹)² ≤ (4δ)²` fails from `n=1` (`τ=1`). (C)-(D) the eventual thresholds in `n`. (E) IBP/FA chain at the floor (keys: `Nm2_le_Psi`, `polyfloor`, `Psi2_le_1`, `Sii_le_Psi2`, `env_A`, `env_B`, `delta_le_half`, `dl_le_N2th_Psi`, `absorb`, `union_row` at `D = 3`): none fails. Nondegenerate: `N ≥ 2.1·10^6`, `t = 1/2` (not the `t = 0` collapse), no empty index, `W^3 = 32768` sites per block.

### Verdict per target
- `fixedTimeFAThm d` (no `hd` predicted): **PASS** (rows 3-9, 14-15; weights are `BoundedWeight`, `c = W^{-d}`; `FlucAvgDet_*_eq` bridge uses `svarF_eq_svar` (`FineModel.lean:68`, `rfl`) and `splitEquiv`).
- `ibpDetThm d (hd : 1 ≤ d)`: **PASS** (rows 10-16; `hΨlow` by `IBPRem_hΨlow_of_floor`, not `IBPDet_hΨlow`).
- `gbEXPV3 (hd : 3 ≤ d)`: **PASS** (composition of the above with `LocalLaw_gbEXPV3Theorem_of_fa_ibp`).
- `stGbEXP_holds`, `stStep1_holds`: **PASS**. `Induction/Step1.lean` imports `Step1Setup`, `Continuity` only (both import `Green/Pins`, none imports a `Green/GbEXP`), so no cycle; `step1TargetV3_holds d (stGbEXPii_of_v3 h) (stGbEXPij_of_v3 h) : STStep1 d`.
- Registry (for 1b): `RBM3D/Test/Axioms.lean` lines `GbEXPV3Theorem` (:104), `FixedTimeFAThm` (:190), `IBPDetThm` (:191), `STStep1` (:100) are the candidates; `STStep1`/`GbEXPV3Theorem` may stay with `hd` in the comment if the scan still lists them; decide by the registry pre-check.
- Paper-delta candidates for 1b: `T2126a` floor `W^{-d/2}` and `W^d ≤ N` in place of RBM2D `W⁻¹ ≤ Ψ`, `W ≤ size`; `T2126b` `BoundedWeight` for the row family (continues `T2061a`).

### (a′) Preflight corrections — Sun Oct  4 10:52:05 UTC 2026
1. Row 18 and the first "Verdict per target" line predict no `hd` for `fixedTimeFAThm`.  The proof needs `hd : 1 ≤ d`: `2 p ≤ #A` is `2 p ≤ W ≤ W^d ≤ (2d+1) W^d` (`GbEXP.lean:536`; `Nat.le_self_pow` needs `d ≠ 0`), so `fixedTimeFAThm (hd : 1 ≤ d)`, like `ibpDetThm`.  Verdict PASS unchanged.  Separately, `SizeTendsto` forces `1 ≤ d` (`size n = (W L)^0 = 1` at `d = 0`): scratch `hd0.lean`, outside the repository, `lake env lean` exit 0.

## (b) Script output (stage 1b: first command Sun Oct  4 10:15:02 UTC 2026; scripts and outputs in `scratchpad/T2126/`, runs between 10:28 and 10:50 UTC)

### b.1 Build, hygiene, scope, commit (worktree `RBM3D-wt/T2126`, branch `t/T2126`, base `471b643`; main has since moved to `6329018`)
```
$ lake build RBM3D.Green.GbEXP | tail -1        # the fresh build, tool log: "✔ [3359/3359] Built RBM3D.Green.GbEXP (5.9s)"
Build completed successfully (3359 jobs).
$ lake build RBM3D.Green.GbEXP 2>&1 | grep -c "RBM3D/Green/GbEXP.lean:"      # warnings/messages of the new file
0
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Green/GbEXP.lean ; wc -l RBM3D/Green/GbEXP.lean
0 ; 1124   (20 public theorems, 27 private theorems/defs)
$ lake build   # whole library, `import RBM3D.Green.GbEXP` inserted after the last import (line 170) of RBM3D.lean, restored after (`git status --short`: empty); Sun Oct  4 10:42:49 UTC 2026 -> 10:43:05
exit=0
info: RBM3D.lean:174:0: axiom audit: 3904 theorems, 1351 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (3875 jobs).
$ lake build   # the branch as committed, no root import (the hub adds it at merge); Sun Oct  4 10:45:33 UTC 2026
exit=1
error: RBM3D.lean:173:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Green.IBPDetThm, RBM.Green.FixedTimeFAThm]
$ git diff --name-only main...t/T2126 ; git log --oneline -1
RBM3D/Green/GbEXP.lean
RBM3D/Test/Axioms.lean
298d757 T2126: port S1-30 Green/GbEXP (fixedTimeFAThm, ibpDetThm, gbEXPV3, stGbEXP_holds, stStep1_holds)
$ git diff 471b643..HEAD --stat -- RBM3D/Green/LocalLaw.lean RBM3D/Green/Pins.lean RBM3D/Green/IBPRem.lean RBM3D/Green/FlucThreshold.lean | wc -l    # the pins and imported statements are untouched
0
$ git merge-tree --write-tree main t/T2126 | head -1        # main moved by T2124 and T2118; its Test/Axioms.lean differs from the base by one deleted line (STEMn2Exp)
f77e87008d40f6ae76f34ef32ebbd2f075472f32      (a tree id, no conflict message: the merge is clean)
```

### b.2 Registry pre-check (ST1-COMMON item 8, DECISIONS §20; scratch file outside the repository, `lake env lean`, exit 0 in all three runs)
```
$ cat scratchpad/T2126/precheck.lean
import RBM3D
import RBM3D.Green.GbEXP

#assert_rbm_axioms
P0  `import RBM3D` only, registry as on main (10:28:54 UTC): 3884 theorems, 1351 definitions, 0 axioms; scan found 77 premises (owed 61); 67 registered premises carry nothing yet
P1  + `import RBM3D.Green.GbEXP`, registry as on main (10:44:15 UTC): 3904 theorems, 0 axioms; scan found 75 (owed 59); 69 carry nothing; newly carrying nothing vs P0: RBM.Green.FixedTimeFAThm, RBM.Green.IBPDetThm
P2  + `import RBM3D.Green.GbEXP`, registry edited = committed (10:43:38 UTC): 3904 theorems, 0 axioms; scan found 75 (owed 59); registry 5 borrowed + 96 owed + 39 structural; 65 carry nothing
$ git diff -U0 main...t/T2126 -- RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]" | cut -c1-100
-   `RBM.Gauss.Sizes.STStep1,        -- Step 1 of `lem:main_ind` (`1_2:1317`): S1-36 (T2028, §20 rul
-   `RBM.Green.GbEXPV3Theorem,       -- `lem_GbEXP` in the RBM2D form (`3_5:14`): S1-30 `gbEXPV3` (T
-   `RBM.Green.FlucGainUpTo', -- gain interface of the higher-order minor expansion `(GavLGEX)` (`3_
-   `RBM.Green.FixedTimeFAThm, -- fixed-time fluctuation averaging `jasdu` (`Acta:4571`, determinist
-   `RBM.Green.IBPDetThm] -- IBP display (`Acta:4587`, deterministic control) for the (`GavLGEX`) ch
+   `RBM.Green.FlucGainUpTo'] -- gain interface of the higher-order minor expansion `(GavLGEX)` (`3_
```
The scan reads the conclusion head only, so `hd` plays no role: all four removed names carry nothing in P1 (`STStep1`, `GbEXPV3Theorem` already did in P0: `stStep1_of_target`, `gbEXPV3Theorem_of_ports` conclude them), and no line stays with a "proved for 3 ≤ d" comment.  The `FlucGainUpTo'` line is rewritten only to end the list with `]`.

### b.3 Axioms (`#print axioms` of all 47 declarations of the file, private included, in a copy of the file; `ax4.out`, 10:44:32 UTC)
```
47 declarations printed; exactly {propext, Classical.choice, Quot.sound}: 47; no axioms: 0; other: []; sorryAx mentions: 0
  fixedTimeFAThm: ['Classical.choice', 'Quot.sound', 'propext']
  ibpDetThm: ['Classical.choice', 'Quot.sound', 'propext']
  gbEXPV3: ['Classical.choice', 'Quot.sound', 'propext']
  stGbEXP_holds: ['Classical.choice', 'Quot.sound', 'propext']
  stStep1_holds: ['Classical.choice', 'Quot.sound', 'propext']
```

### b.4 Target statements, extracted from the file by script (`python3 extract.py NAME…`; `d` is the file's `variable {d : ℕ}`); the pins `FixedTimeFAThm`, `IBPDetThm` (`LocalLaw.lean:176, 186`), `GbEXPV3Theorem` (`Pins.lean:224`) are the merged ones
```
-- GbEXP.lean:524
theorem fixedTimeFAThm (hd : 1 ≤ d) : FixedTimeFAThm d
-- GbEXP.lean:769
theorem ibpDetThm (hd : 1 ≤ d) : IBPDetThm d
-- GbEXP.lean:806
theorem gbEXPV3 (hd : 3 ≤ d) : GbEXPV3Theorem d
-- GbEXP.lean:811
theorem stGbEXP_holds (hd : 3 ≤ d) : STGbEXP d
-- GbEXP.lean:816
theorem stStep1_holds (hd : 3 ≤ d) : STStep1 d
```

### b.5 Statement diff against RBM2D `c9a24cf` after the renaming rules (`python3 stmtdiff.py`; R1-R4 of ST1-COMMON item 2, W30 = DECISIONS §30; the R1/MD rules are not listed)
```
SAME  FlucAvgDet_iter_budget_eventually          rules: R2 Idx, W30 UniformWeight->BoundedWeight
DIFF  FlucAvgDet_family                          rules: R2 Idx, R3 (W^-1)^2 -> (W^d)^-1, W30 UniformWeight->BoundedWeight
         residual  RBM2D(renamed): ℝ))⁻¹   |  RBM3D: ℕ) : ℝ) ^ (-(d : ℝ) / 2)
DIFF  FlucAvgDet_budgetFamily_absorb             rules: -
         residual  RBM2D(renamed): ℝ))⁻¹   |  RBM3D: ℕ) : ℝ) ^ (-(d : ℝ) / 2)
DIFF  FlucAvgDet_weighted                        rules: R2 Idx, R3 (W^-1)^2 -> (W^d)^-1, W30 UniformWeight->BoundedWeight
         residual  RBM2D(renamed): ℝ))⁻¹   |  RBM3D: ℕ) : ℝ) ^ (-(d : ℝ) / 2)
DIFF  FlucAvgDet_greenBlk_true_apply             rules: R2 BlockIndex L W, R2 Idx L W, R2 greenBlk L W, R2 splitEquiv L W, R2 {L W}
         residual  RBM2D(renamed): (M - zt   |  RBM3D: green M (zt
         residual  RBM2D(renamed): u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹   |  RBM3D: u)
SAME  FlucAvgDet_greenBlk_sub_eq                 rules: R2 BlockIndex, R2 greenBlk, R2 splitEquiv
SAME  FlucAvgDet_condDiagBlk_eq                  rules: R2 BlockIndex, R2 splitEquiv
SAME  FlucAvgDet_row_sum_eq                      rules: R2 BlockIndex, R2 greenBlk, R2 splitEquiv, R4 Sblk2->svar, R4 svar->svarF
DIFF  FlucAvgDet_blk_sum_eq                      rules: R2 Idx, R2 Z2, R2 blkCoef2, R2 greenBlk, R3 (W^-1)^2 -> (W^d)^-1
         residual  RBM2D(renamed): (blk   |  RBM3D: (split d
         residual  RBM2D(renamed): j.1, blk (sz.L n) (sz.W n) j.2)   |  RBM3D: j).1
SAME  FlucAvgDet_ibp_sum_eq                      rules: R2 BlockIndex, R2 greenBlk, R2 splitEquiv, R4 Sblk2->svar, R4 svar->svarF
SAME  FlucAvgDet_perTime_reindex                 rules: -
DIFF  fixedTimeFAThm                             rules: -
         residual  RBM2D(renamed): ∅   |  RBM3D: (hd : 1 ≤ d)
         residual  RBM2D(renamed): ∅   |  RBM3D: d
SAME  IBPDet_norm_condExpDiag_sub_le_two_phi     rules: R2 Idx, R3 (W^-1)^2 -> (W^d)^-1, R4 svar->svarF
SAME  IBPDet_weighted_of_rem                     rules: R3 (W^-1)^2 -> (W^d)^-1
SAME  IBPDet_hEnv                                rules: -
SAME  IBPDet_hΨ1                                 rules: -
DIFF  ibpDetThm                                  rules: -
         residual  RBM2D(renamed): ∅   |  RBM3D: (hd : 1 ≤ d)
         residual  RBM2D(renamed): ∅   |  RBM3D: d
DIFF  gbEXPV3                                    rules: -
         residual  RBM2D(renamed): ∅   |  RBM3D: (hd : 3 ≤ d)
         residual  RBM2D(renamed): ∅   |  RBM3D: d
NEW (no RBM2D counterpart): stGbEXP_holds
NEW (no RBM2D counterpart): stStep1_holds
10 of 20 public statements equal RBM2D after the renaming rules above; differing: 8
RBM2D public decls (kept region) without an RBM3D counterpart: ['IBPDet_hΨlow']
```
Residual differences (all): the floor premise in 3 theorems (`W⁻¹ ≤ Ψ` → `W^{-d/2} ≤ Ψ`); `FlucAvgDet_greenBlk_true_apply` concludes `green M (zt E u)`, which is `(M - zt E u • 1)⁻¹` by definition; `FlucAvgDet_blk_sum_eq`: the `Z2` pair `(blk j.1, blk j.2) = a` is `(split d L W j).1 = a`; `hd` on the three endpoints and `d` on the pins; `stGbEXP_holds`, `stStep1_holds` are new; `IBPDet_hΨlow` is replaced by `IBPRem_hΨlow_of_floor`.

### b.6 Compiled nonempty instances (statements by script; data in `GbEXP.lean:821-839`; `gbEXPPsi n = W n ^ (-((3:ℕ):ℝ)/2)`)
```
-- GbEXP.lean:895
private theorem gbEXP_inst_fixedTimeFA
    (hll : LocalLawDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    FARowDet sz0 (STflowE z0) tInst (condDiagBlk sz0 (STflowE z0) tInst) gbEXPPsi ∧
      FABlkDet sz0 (STflowE z0) tInst (condDiagBlk sz0 (STflowE z0) tInst) gbEXPPsi
-- GbEXP.lean:906
private theorem gbEXP_inst_ibpDet (hll : LocalLawDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    IBPDet sz0 (STflowE z0) tInst (condDiagBlk sz0 (STflowE z0) tInst) gbEXPPsi
-- GbEXP.lean:939
private theorem gbEXP_inst_gbEXPV3_ij_ii (c : ℝ) (hc : 0 < c) :
    GijOmegaSeq sz0 (STflowE z0) tInst c ∧ GiiOmegaSeq sz0 (STflowE z0) tInst c
-- GbEXP.lean:950
private theorem gbEXP_inst_gbEXPV3_avg (c : ℝ) (hc : 0 < c)
    (hAs : AsGMcSeq sz0 (STflowE z0) tInst c) (hLoop : LoopDetSeq sz0 (STflowE z0) tInst gbEXPPsi) :
    GijSeq sz0 (STflowE z0) tInst ∧ GiiSeq sz0 (STflowE z0) tInst ∧
      GavLDetSeq sz0 (STflowE z0) tInst gbEXPPsi
-- GbEXP.lean:963
private theorem gbEXP_inst_stGbEXP :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tInst (1 / 20)
-- GbEXP.lean:972
private theorem gbEXP_inst_stStep1 (hK : STKbound sz0 (STflowE z0))
    (hLK : STLK sz0 (STflowE z0) sInst) (hLoc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst
-- the proof term of the first (the others have the same shape):
  fixedTimeFAThm (by norm_num : 1 ≤ 3) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Instance.premises.1 (STflowE z0) tInst
    Instance.premises.2.1 Instance.premises.2.2.1 Instance.premises.2.2.2.1
    Instance.premises.2.2.2.2 gbEXPPsi (1 / 4) (by norm_num) gbEXPPsi_nonneg
    (Eventually.of_forall fun n => ⟨le_rfl, gbEXPPsi_ceiling n⟩) hll
```
Also compiled: the same two pins at `t ≡ 0` with no hypothesis (`gbEXP_inst_fixedTimeFA_zero`, `gbEXP_inst_ibpDet_zero`, lines 916, 927), `FlucAvgDet_weighted` for the block and the row family (`gbEXP_inst_weighted_block` 995, `_row` 1022), the IBP inputs (`gbEXP_inst_ibp_inputs`, 1050), `IBPDet_weighted_of_rem` (1064), the bridge identities at `n = 0` for every `ω` (`gbEXP_inst_bridge`, 1085) and the negative `gbEXP_W_inv_not_le_psi` (874: `¬ (W⁻¹ ≤ Ψ)` at `n = 0`, `W = 32`).

### b.7 `d = 2` tokens (`python3 tokens.py`; counts = code lines / docstring-or-comment lines of the RBM2D kept region; portmap P.7 row in brackets)
```
FlucAvgDet  [W⁻²/L⁻²:23 d=2:3 Z2/zdist2:4]  inv2:11/13  Winv:6/0  W2:2/0  N2:0/1  d=2:0/3  Z2:10/2  1/5:1/6  W_le_self/AvgPins:7/6
IBPDet      [W⁻²/L⁻²:11 d=2:2]  inv2:7/9  Winv:2/0  W2:1/0  d=2:0/2  1/5:0/2  W_le_self/AvgPins:2/2
GbEXP       [W⁻²/L⁻²:1]  inv2:0/2
RBM2D total  inv2:18/24  Winv:8/0  W2:3/0  N2:0/1  d=2:0/5  Z2:10/2  1/5:1/8  scal:0/0  W_le_self/AvgPins:9/8
RBM3D GbEXP.lean (before the instances) inv2:0/9  N2:0/1  Z2:0/1  1/5:0/3  W_le_self/AvgPins:0/4
```
| RBM2D token (code lines) | here |
|---|---|
| floor `((d.W n : ℝ))⁻¹ ≤ Ψ n` (`Winv`, 8: FlucAvgDet:106,139,228,279,300,461; IBPDet:207,249) | `W^{-d/2} ≤ Ψ n` (D213); `FlucAvgDet_floor_le` for `(N+4)^{-2} ≤ Ψ`; `IBPDet:207` (`IBPDet_hΨlow`) = merged `IBPRem_hΨlow_of_floor` |
| `⁻¹ ^ 2` (`inv2`, 18: FlucAvgDet:234,254,306,391,395,401,464,470,485,489,490; IBPDet:67,73,75,90,218,258,261) | `(((sz.W n : ℕ) : ℝ) ^ d)⁻¹` (R3): `hcW`, `cw`, `Tw`, `hWΦ`, `hWΨ`, `S_ii ≤ W^{-d}` (`svarF_diag`) |
| `W ^ 2` (`W2`, 3: FlucAvgDet:481,498; IBPDet:212) | `W ≤ W^d` (`hWd`, needs `1 ≤ d`); `W^d ≤ size` (`FlucAvgDet_floor_le`, merged `IBPRem_hΨlow_of_floor`) |
| `Z2`, `blk` (`Z2`, 10: FlucAvgDet:384,390,394,399,400,472,473,487,488,492) | `Zd d (sz.L n)`, `(split d L W j).1 = a`, `flucVanish_sbSupport d (sz.L n)` |
| `(5 : ℝ)⁻¹` (`1/5`, FlucAvgDet:470); `5 W²` | none: `c = W^{-d}`, `#A = (2d+1) W^d` (`boundedWeight_svarF`, `card_Sblk_support`) |
| `W_le_self`, `AvgPins_one_le_size`, `Sblk2` (9: FlucAvgDet:110,146,210,367,378,410,421; IBPDet:108,229) | `FlucAvgDet_floor_le`, merged `Sizes.one_le_size`, `svar`/`svarF` with `FlucAvgDet_svar_eq_svarF` |
| `d = 2` (docstrings: FlucAvgDet 3, IBPDet 2), `(W L)²` (1), `L2`, `scal` (0) | docstrings rewritten; the script finds 0 code lines of this file with any token (its 9 `inv2` hits are docstrings quoting RBM2D) |

### b.8 Name clash (CLAUDE.md §5.2): the 20 public names, `git grep` on `main` (6329018) and on the base `471b643`
```
declarations (theorem|lemma|def|abbrev|instance|structure, any namespace): main 0, base 0
word hits on main (all docstrings or comments; the last three are the removed registry lines): Green/EntryDom.lean:287 Green/FlucThreshold.lean:855 Green/LocalLaw.lean:174 Green/LocalLaw.lean:185 Test/Axioms.lean:104 Test/Axioms.lean:189 Test/Axioms.lean:190
```

### b.9 Ports
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/FlucAvgDet.lean RBM2D/Green/IBPDet.lean RBM2D/Green/GbEXP.lean
 RBM2D/Green/FlucAvgDet.lean | 214 +++++++++-----------------------------------
 RBM2D/Green/GbEXP.lean      |  93 +++----------------
 RBM2D/Green/IBPDet.lean     | 128 ++++++--------------------
 3 files changed, 86 insertions(+), 349 deletions(-)
```
Ported from `c9a24cf` (the ticket), kept regions `FlucAvgDet:1-503`, `IBPDet:1-269`, `GbEXP:1-47` (the Checks sections start at 505, 270, 48 of 623, 335, 111 lines); RBM2D HEAD has moved on (not read).  RBM1D: not ported from; the RBM1D `file:line` citations in the docstrings (commit `c06b103`, taken from the RBM2D headers) were checked by `git -C ../RBM1D --no-optional-locks show c06b103:<file> | sed -n <line>p`: 9 of 9 cited lines are the cited `theorem`.

### b.10 Limit check of the external hypothesis at the Lean data (`python3 limit_check.py`, numpy; model of `Gauss/FineModel.lean`, `d = 3`, `E = 1/2`, `t = 1/16`, `g = lam_0 = 1/64`, `L = 3`, `W = 1..4`; 10:34:57 UTC)
```
m = (-0.25+0.9682458365518543j)  z_t = (0.265625+0.9077304717673633j)  eta_t = 0.9077304717673633
W=1 N=  27  rms|G_ii-m|=0.2532  rms*W^{d/2}=0.2532  max|G-m|=0.5278  max/Psi=0.528  (Psi=W^-3/2=1.0000)
W=2 N= 216  rms|G_ii-m|=0.0919  rms*W^{d/2}=0.2599  max|G-m|=0.2727  max/Psi=0.771  (Psi=W^-3/2=0.3536)
W=3 N= 729  rms|G_ii-m|=0.0501  rms*W^{d/2}=0.2602  max|G-m|=0.1608  max/Psi=0.835  (Psi=W^-3/2=0.1925)
W=4 N=1728  rms|G_ii-m|=0.0322  rms*W^{d/2}=0.2577  max|G-m|=0.1152  max/Psi=0.922  (Psi=W^-3/2=0.1250)
```
`rms |G_ii - m| W^{3/2}` stays between `0.253` and `0.260` and `max|G - m| / W^{-3/2}` grows slowly (`0.528` to `0.922`), as `‖G_t - m‖_max ≺ W^{-d/2}` predicts; the hypothesis `LocalLawDetSeq` of the instances is not derived here.

### b.11 Narrative
1. **Delivered, no stop**: the five targets of b.4 in the new `RBM3D/Green/GbEXP.lean` (commit `298d757`); their conclusions are the unchanged pins (b.1: `LocalLaw.lean`, `Pins.lean` untouched).  `Induction/Step1` imports without a cycle (the file compiled), so `stStep1_holds` is in.
2. **Ported with the RBM2D names**: the 11 supporting public theorems of `FlucAvgDet` (chain 4, bridge 6, `perTime_reindex`) and 4 of `IBPDet`.  Dropped: `IBPDet_hΨlow` (replaced by the merged `IBPRem_hΨlow_of_floor`, as the ticket says), RBM2D's `Checks` and `#print axioms` (replaced by section 11); nothing else.  Private: the real-variable cores, `FlucAvgDet_tendsto_size`, and the new `FlucAvgDet_floor_le`, `FlucAvgDet_svar_eq_svarF`, `IBPDet_hWΨ`.
3. **Floor.**  The pins give `W^{-d/2} ≤ Ψ` (`3_5:27`), not RBM2D's `W⁻¹ ≤ Ψ`, which fails at `Ψ = W^{-3/2}` (`gbEXP_W_inv_not_le_psi`).  No step needs it: the proofs use `(N+4)^{-2} ≤ Ψ` (from `W^{d/2} ≤ W^d ≤ N + 4 ≤ (N+4)²`, `FlucAvgDet_floor_le`; (a) row 6 chains `N^{-2} ≤ N^{-1/2} ≤ W^{-d/2}`, the same mathematics), `W^{-d} ≤ Ψ²` (`(W^{-d/2})² = W^{-d}`, `IBPDet_hWΨ`) and `size^{-1} ≤ Ψ²` (the merged lemma).
4. **Weights and counts.**  Row `S_{ij}`: bounded weight, `c = W^{-d}`, `#A = (2d+1) W^d` (`7 W^3` at `d = 3`, `c·#A = 7 > 1`, so not uniform, DECISIONS §30); block: `c = W^{-d}`, `#A = W^d`; `c ≤ ρ²` is the second conjunct of `flucGain_of_localLaw`; `2p ≤ #A` from `eventually_le_W` and `W ≤ W^d`.  The IBP union runs over the `size = (W L)^d` sites (`D + 2` on `D`); the diagonal coefficient is `S_ii ≤ W^{-d}`.
5. **`hd`.**  `fixedTimeFAThm`: `1 ≤ d` only at `W ≤ W^d` ((a′)); `ibpDetThm`: `1 ≤ d` for `perTimeDomAt_ibpRem` (D200); `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds`: `3 ≤ d` (`localLawDetThm`, D201).
6. **Bridge.**  The pins sit on `Vtx` (`svar`, `blkCoef2`, `greenBlk`, `condDiagBlk`), `flucAvg` and `condExpDiag` on `Idx` (`svarF`); `splitEquiv`, `svarF_eq_svar` and `Matrix.inv_submatrix_equiv` carry one to the other (`FlucAvgDet_*_eq`).
7. **Instances.**  `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the merged `Instance.premises` (`κ = δ = (1/10)/2`, `𝔠 = 1/6`, `𝔡 = 1/10`, `E = lemE z_n`, `t ≡ 1/16`), `Ψ = W^{-3/2}` (the floor itself), `a = 1/4`.  Every deterministic hypothesis is proved at the data; kept as hypotheses (other gates): `LocalLawDetSeq` (= `AsGMcSeq` at `c = 3/2`), `AsGMcSeq` and `LoopDetSeq` (third clause of `lem_GbEXP`), `STKbound`, `STLK`, `STLocalMax` at `s ≡ 0`.  The `t ≡ 0` instances need none (collapsed flow: complements).  The data differ from (a)(ii) (`E ≡ 0`, `t ≡ 1/2`); the limit check was redone at them (b.10).
8. **Registry and hub.**  Four registry lines removed (b.2).  The branch alone fails the root audit (b.1); with the root import the full build passes, as for T2119.

## (c) Verified Mathlib names (new proofs of this ticket; `#check @name` in `names_check.lean` over the file's `open`s, exit 0, 0 errors; the ported proofs reuse RBM2D's names, all resolved by the build)
`Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_lt_rpow_of_exponent_lt`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_one`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.one_le_rpow`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `pow_le_pow_left₀`, `Nat.le_self_pow`, `Nat.le_mul_of_pos_left`, `Nat.le_mul_of_pos_right`, `Nat.pow_le_pow_left`, `Equiv.sum_comp`, `Equiv.apply_symm_apply`, `Matrix.inv_submatrix_equiv`, `Matrix.nonsing_inv_eq_ringInverse`, `MeasureTheory.measure_iUnion_fintype_le`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`, `ENNReal.ofReal_le_ofReal`, `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.sum_congr`, `Finset.card_univ`, `nsmul_eq_mul`, `max_eq_left`, `min_le_right`, `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonneg_right`, `tendsto_natCast_atTop_iff`, `Set.mem_ofPred_eq`, `Set.mem_iUnion`, `zero_le_one'`.  Deprecated in this Mathlib (warning in the tool log): `Set.mem_setOf_eq`, use `Set.mem_ofPred_eq`.  Verified absent: none searched.

## (d) Open issues and paper-delta candidates
1. **Hub**: add `import RBM3D.Green.GbEXP` after the last `import` line of `RBM3D.lean` at merge (b.1: the branch alone fails the root audit, with the import the full build passes; the merge with `main` is clean).
2. **Import closure**: `Green/GbEXP` imports `Induction/Step1` (hence `Step1Setup`, `Continuity`, ...), so no file of that closure can import `Green/GbEXP` later (cycle).
3. **External hypotheses of the instances** (not derived here): `LocalLawDetSeq sz0 (STflowE z0) tInst Ψ`, `AsGMcSeq`, `LoopDetSeq`, `STKbound`, `STLK`, `STLocalMax`; limit check of the local law in b.10.
4. **`hd`**: the signatures keep the ticket's `hd` binders; `1 ≤ d` is derivable from `SizeTendsto` ((a′)), so `FixedTimeFAThm 0`, `IBPDetThm 0` hold vacuously.
5. **Paper-delta candidates**: `T2126a` (continues T2108a, T2123a): the FA/IBP proofs run at the paper's floor `W^{-d/2} ≤ Ψ` (`3_5:27`) with `W^d ≤ N` in place of RBM2D's `W⁻¹ ≤ Ψ`, `W ≤ size`; `T2126b` (continues T2061a, D192): the fluctuation-averaging weights are `BoundedWeight` (row `c = W^{-d}`, `#A = (2d+1) W^d`; block `c = W^{-d}`, `#A = W^d`), the form of `jasdu` (`Acta:4571`: `0 ≤ |t_k| ≤ W^{-1}`, `∑|t_k| ≤ 1`) in `d` dimensions; `T2126c` (D200, D201 pattern): `hd : 1 ≤ d` on `fixedTimeFAThm`, `ibpDetThm`, `hd : 3 ≤ d` on `gbEXPV3`, `stGbEXP_holds`, `stStep1_holds`.
6. **No separate instance** for `FlucAvgDet_perTime_reindex` and `IBPDet_norm_condExpDiag_sub_le_two_phi`: they are used inside the endpoint instances and the `IBPDet_weighted_of_rem` instance.
