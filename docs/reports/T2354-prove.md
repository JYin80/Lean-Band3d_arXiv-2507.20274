Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct  9 01:09:48 UTC 2026

Notation: `N = sz.size n = (W L)^d` (`Defs/Sizes.lean:157`), `A := 1 + 2 lam²` (`lam = sz.lam n`), `Δ = (t0-t1)/K`, `K = gueGridK = (N+1)^(32 n0+64)` (`Grid.lean:106`), `m = mE E`, `η_u = (1-u) Im m`. Sources: RBM2D `GUEPhase/HypB.lean` (1021 lines), `LLTransfer.lean` (440 lines), HEAD 9e0f275.

### (i) Exponent table
**A. `d = 2` token table** (counts = source lines, `bash tok.sh | head -2`):
```
HypB: Z2=36 pow2(^ 2)=63 W^2=7 L^2=3 WL^2=8 d.size=77 logL=0 spectralZM=69 gloop=10 green=10 BlockIndex=1 Idx=38 loopMax=28 Kcal/mSig/LLf=5
LLTransfer: Z2=2 pow2(^ 2)=4 W^2=0 L^2=0 WL^2=2 d.size=22 logL=0 spectralZM=21 gloop=0 green=30 BlockIndex=0 Idx=6 loopMax=0 Kcal/mSig/LLf=0
```
| token (source lines) | replacement at `d` | constraint | slack / remark |
|---|---|---|---|
| `Z2 L` (HypB 36, LLT 2: type of `Kt`), `Idx L W` (38/6), `BlockIndex` (1: `HypB_q_745`) | `Zd d L`, `Idx d L W`, `Vtx d L W` | types | none |
| `(((W*L)^2:ℕ):ℝ)` HypB 81 (`rfl` to `d.size`), 455, 459 (`HypB_bil`), 813 (`hsmall` in `HypB_fixed`); `d.size` 77/22 | `(((W*L)^d:ℕ):ℝ)` = `sz.size n` (`rfl`) | merged `norm_primBilGUE_le` (`Bootstrap.lean:228`) has the same `n² N ∑ B B'`, `N=(W L)^d` | exact |
| `((W:ℝ)^2)⁻¹` HypB 123, 158, 182, 186 (`hD4`, A3) | `((W:ℝ)^d)⁻¹` | merged `EntryGrid.lean:454,510` write `gueLmax + W^{-d}` | exact |
| `(d.L n)^2 (1 - t1) ≤ 1` HypB 112 (`hellN`), 170 | `L^d (1 - t1) ≤ lam²` (T2352a (1); `Hyp_Bctl_le` `HypA.lean:494`, private) | `L² (1-u) ≤ g²` with `g² = lam²/L^{d-2}` is what merged `gue_inv_W_le_loopMax` (`Proc.lean:539`) takes; needs `2 ≤ d` | inst. 2: `64 ≤ 64` (equality) |
| A3 constant `3 = 1 + 2` (HypB 150ff `√(3 c L₂)`, `hdiag` of `HypB_eG_745`, `h3: √(3c) ≤ 4c`, `hCe: Ce ≤ 4 m² c N`, `7 = 3+4` in `HypB_path`/`hbig`) | `A = 1 + 2 lam²` (Ward: `W^{-d} ≤ 2 L^d(1-u) maxLoopPM ≤ 2 lam² L₂`, `Proc.lean:25-48`) | `A = 3` iff `lam = 1`; `lam` is a sequence, `lam ≤ 𝔡⁻¹` only (`Sizes.WO`) | **departure T2354a**, see (iii) |
| other `^ 2` (`N^2` in `hgrid2` 336-372, 739; `n²`, `m²`, `η⁻²`, `√` concavity) | unchanged | no `d` | none |
| `log L` | 0 occurrences in both files | – | nothing to replace |
| `spectralZ/M` (69/21), `gloop` (10), `Gsig` (0) | `zt/mE`, `loopL d L W (blockMat d L W ·)` | renaming | `green` (10/30) stays `green`: `gueDev`, `GUEPathBounds.localLaw` (`Grid.lean:99`) use `green` |
| LLT docstring `N = (W L)²` (lines 12, 406) | `(W L)^d` | comment only | – |

**B. Constants and thresholds** (all numbers from `python3 -I inst.py`, below)
| quantity | value | constraint | slack |
|---|---|---|---|
| grid `K` | `(N+1)^128` (`n0=2`), `log10 K = 809.2` | `M³ N Δ ≤ 1`, `3 M⁶ N² Δ ≤ N^{-2 n0}` (`HypB_grid_of_size`: `3 M⁶+M³+1 ≤ N`) | `12353 ≤ N=2097152`; log10 slack `801.0` and `767.1` |
| `hbig` (`HypB_fixed`) | `2+2^{2n0}+(3+4A)(2n0)² ≤ N^{τ/2}` (source: `7` for `3+4A`) | `τ>0` free | inst. 2 `A=129`: `8322 ≤ 3.04e9` |
| `hCe` (`HypB_fixed`) | `Ce ≤ 4 A m² N^{τ/2} N` | `Ce ≥ 0` | `1 ≤ 1.3e19` |
| `h0` at `m=2`, `t1=0` | `W^{-d} = 3.05e-5 ≤ N^{τ/2} (N η_{t1})^{-2}` | needs `τ ≥ 2.4` | `τ=3`: `6.9e-4` (×22.6); `τ=1`: `3.3e-10` False |
| `hδN` (`HypB_entry_le`) | `gueDelta = N^{-τU/4} ≤ Im m/2` | `τU=0.3`: `0.3356 ≤ 0.5`; `HypB_ev_delta` at `τU=1/1000`, `κ=1/10` | eventual: `log10 N* = 3806` (conclusion only) |
| Lemma 2.8 (`lemma28_quant`, `Semicircle.lean:359`) | `1/16 ≤ lemT z < 1`, `η_{t0} = √t0 η ≥ η/4` | `0<η≤1`, `\|Re z\| ≤ 2-κ` | n=0: `lemT = 0.99999951`; `η_{t0} ≥ η/4` True at n=0..2 |
| LLT scale `N η_{t0} ≥ N^{2τU}/4` | `1.03 ≥ 0.2574` (n=0) | gives `N^{τU/2}(N η_{t0})^{-1/2} ≤ 2 N^{-τU/2}` | ×4.0 |
| LLT envelope `(4N)^{2p} N^{-(2p+1)} ≤ 4^{2p}` | `4^{2p}/N` | `N ≥ 1` | factor `N` |
| LLT thresholds, `p=1`, `δ=1/10` | `C = 2^{2p}+4^{2p} = 20 ≤ N^δ`: `log10 N* = 13.0`; `N^{τU/2} ≥ 2`: `602.1` (`τU=1/1000`), `60.2` (`τU=1/100 = ouTauMax` cap) | `0<τU<1/2` (`ouTauMax ≤ 1/100`, `ZeroModeProfile.lean:78`) | conclusion only `∀ᶠ` |

### (ii) One concrete nondegenerate instance
Instance 1 (window targets: `HypB_step_le`, `HypB_Kt_le_one`, `HypB_ev_*`, `HypB_sqrt_cont`, LLT): `d=3`, merged `SizesInst.sz0`, `n=0` (`L=4, W=32, lam=1/64, N=2097152`, `Defs/Sizes.lean:260-275`), `E≡0` (`m=i`), `κ=1/10`, `τU=1/1000`, `n0=2`, window of T2352 `1-t0=N^{1/500}/N`, `t0-t1 = N^{-τU}(1-t0)/2`.
Instance 2 (path targets: `HypB_entry_le`, `HypB_eG_745/746`, `HypB_fixed`, `HypB_Lproc/Dproc_grid`): `Sizes 3` with `L≡4, W≡32, lam≡8` (`lam` is an arbitrary real sequence, `Sizes` has no constraint on it), `n=0`, `E≡0`, `τU=0.3`, `t1=0`, `t0=1/1000`, `ω₀=0` (so `gueH = 0`, `G = i/(1-u)·I`, `\|G-m\| = u/(1-u)`, `gueStop = K`). Reason for `t1=0`: for `t1` near 1 a deterministic `H` with `G ≈ m I` does not exist (`G_xx = m` forces `h = -u m`, real only at `u=0`), so with `t1>0` at `ω₀=0` `gueStop=0` and `j<gueStop` is vacuous. `hD4`: `loopL((+,-),(a,a))` at `H=0` is `\|z\|⁻² tr(E_a E_a) = W^{-d}/(1-u)²` (`Eblk`, `GLoop.lean:55`; `loopL`, `GLoopFlow.lean:123`), so `L₂ ≥ W^{-d}`.
Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2354/inst.py`
```
sz0 n=0: L,W,lam,N = 4 32 0.015625 2097152
window: 1-t0=4.909e-07 t0-t1=2.419e-07 0<t1<t0<1: True
h730 (step_le hyp) t0-t1=2.419e-07 <= N^-tU*eta_t0=4.838e-07 : True
step_le concl: Delta=(t0-t1)/K=10^-815.8 <= 1-t0=4.909e-07 : True (Delta<=t0-t1<=N^-tU eta_t0<=1-t0)
Kt_le_one hscale: (N eta_t0)^-1=0.97131 <= N^-tU=0.98555 : True
Kt_le_one: N^(tU/2)*N^-tU=0.99275 <=1; hK1 toy Kt=0 on |J|>=2
ev_grid thresh: 3M^6+M^3+1 = 12353 <= N: True
ev_grid conc at n=0: M^3 N/K: log10=-801.0 <=0 ; 3M^6N^2/K: log10=-792.4 <= log10 N^-2n0=-25.3
ev_delta (tU=1/1000): need N^(tU/4)>=8.944 i.e. log10 N* = 3806 (conclusion eventual; hyps hE,hsz hold)
--- instance 2: lam=8, tauU=0.3, t1=0, t0=0.001, omega0=0 (gueH=0 matrix)
hellN: L^d(1-t1)=64 <= lam^2=64 : True (equality)
hdeltaN: gueDelta=N^-tU/4=0.3356 <= Im m/2=0.5 : True
gueDev_k=u_k/(1-u_k)<= 0.001001 < gueDelta=0.3356 => gueStop=K (j<gueStop nonvacuous): True
hD4 (c=1): max entry^2=1.002e-06 <= c(L2+W^-d) >= 3.052e-05 : True
A3 const A=1+2lam^2=129 (RBM2D: 3); entry concl: 0.001001 <= sqrt(A c L2)=0.06281 : True
Ward core: W^-d=3.052e-05 <= 2 lam^2 L2 = 0.003914 (from L^d(1-u)<=lam^2)
HypB_fixed tau=3: c=N^(tau/2)=3.037e+09 ; hbig 2+2^4+7*16=130 <= c : True
  departure form: hbig (3+4A)(2n0)^2+2+2^(2n0)=8322 <= c: True ; hCe Ce<=4 A m^2 c N = 1.315e+19
  hCe: Ce=1 <= 4 m^2 c N = 1.019e+17
  h0 (m=2,u=t1=0): |loopL(0,i)|=W^-d=3.052e-05 <= c (N eta_t1)^-2=0.0006905 : True (needs tau>=2.4; tau=1 gives 3.29e-10: False)
  hgrid1 log10 -801.0 <=0 ; hgrid2 log10 -792.4 <= -25.3
  hDelta: Delta=10^-812.2 <= 1-t0=0.999
  hM,hq,heG: LHS finite for k<=K; RHS >= c (N eta)^-m >0 and g3,g4,Ce free => hold for tau large; not evaluated here
--- LLTransfer, p=1, delta=1/10
C=2^(2p)+4^(2p)=20 <= N^delta : log10 N* = 13.0
 tauU=0.001: N^(tU/2)>=2 : log10 N* = 602.1 ; tauU<1/2: True
 tauU=0.01: N^(tU/2)>=2 : log10 N* = 60.2 ; tauU<1/2: True
 n=0 N=2.097e+06 eta=4.909e-07 lemT=|m|^2=0.99999951 in[1/16,1): True ; eta_t0>=eta/4: True ; N eta_t0=1.03 >= N^(2tU)/4=0.2574: True ; N^(tU/2)(N eta_t0)^-1/2=0.9927
 n=1 N=5.498e+11 eta=1.92e-12 lemT=|m|^2=1.00000000 in[1/16,1): True ; eta_t0>=eta/4: True ; N eta_t0=1.056 >= N^(2tU)/4=0.2639: True ; N^(tU/2)(N eta_t0)^-1/2=0.9866
 n=2 N=8.125e+14 eta=1.318e-15 lemT=|m|^2=1.00000000 in[1/16,1): True ; eta_t0>=eta/4: True ; N eta_t0=1.071 >= N^(2tU)/4=0.2678: True ; N^(tU/2)(N eta_t0)^-1/2=0.983
 t_n=N^(-1+tU)=4.838e-07>=0, zeta=4.838e-07, t1=(1-zeta)t0 <t0: True (nondegenerate window)
```
External hypothesis `GUEPathBounds sz E' t1 t0 (gueGridK sz n0) n0 Kt` of `oull_of_pathBounds` (output of UN-50b, not proved here): it stays a hypothesis of the example. Limit computation of its `localLaw` field at the cutoff `τ'=τU/2`, failure rate `N^{-(2p+1)}`: the level `N^{τU/2}(N η_{t0})^{-1/2} ≤ 2 N^{-τU/2} → 0` (values `0.9927, 0.9866, 0.983` at n=0..2; `≤ 1` iff `N ≥ 10^{602.1}` at `τU=1/1000`), and `N η_{t0} ≥ N^{2τU}/4` holds at every n shown. The `∀ᶠ` conclusions (`HypB_ev_*`, `oull_of_pathBounds`) are instantiated at the hypotheses only; `hsz`/`hd` is `Sizes.tendsto_size sz0 sz0_tendsto` (`Defs/StochDomAt.lean:735`, `Defs/Sizes.lean:300`).
`HypB_highProb_range`: `Ξ m n = Set.univ`, `P = Pgue sz0` (`Grid.lean:61`, a probability measure), `M = 3`: `HighProbAt P size univ` holds, range statement is nonvacuous for `1 ≤ m ≤ M`.
Instance 2 caveat: `h0` needs `τ ≥ 2.4`, so `τ = 3` (`c = 3.0e9`, no astronomical size); `hM` is not evaluated numerically here: its left side is finite for `k ≤ K` and independent of `τ`, its right side is `≥ N^{τ/2}(N η)^{-m} > 0`, and `τ` is free, so it holds for `τ` large; `g3, g4, Ce` are free. If `hM` resists at 1b, it stays a hypothesis of that example (pathwise output of UN-50b).

### (iii) Merged signatures against the source's uses, MISS list, §29
**Merged vs source (HypA, T2352 report `:219,241`).** `Hyp_Kt_detDom` is not called by `HypB` (`grep -o` in the source: `Hyp_Kt_one` 2 occurrences, `Hyp_Kt_detDom` 0), so `hKb`, `hell`-∀ᶠ are not carried. `HypB_eG_746` calls `Hyp_Kt_one` (`HypA.lean:712`): its `hKinit` is the merged `Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a` (source: `∀ I, … = Kcal`), conclusion `mSigma (E n) s` (T2352a (3), inherited). `Hyp_eps_le_dev` (`:353`), `Hyp_trace_eq_gloop_one` (`:384`, extra argument `m : Bool → ℂ`), `Hyp_cutGlue_le` (`:412`), `Hyp_Kt_disc` (`:864`), `Hyp_grid` (`:981`), `Hyp_interp_bound` (`:204`), `Hyp_time_*`: renamed only. `norm_egtNGUE_le` (`Proc.lean:596`): same shape, `N=(W L)^d`. `llErrMat` (`Green/Pins.lean:73`) is stated with `Gres _ _ true`: `HypB_llErr_eq` becomes `Gres H z true = green H z` (`Ring.inverse` = `⁻¹`; the merged twin `IBPRem_Gres_true`, `IBPRem.lean:106`, is private: re-derive ≈ 3 lines).
**Departure T2354a (statement difference).** `HypB_entry_le`: add `(hd : 2 ≤ d)`; `hellN : L^d (1 - t1 n) ≤ lam²`; `(W^d)⁻¹` in `hD4`; conclusion `√(A c L₂)`, `A = 1 + 2 lam²` (source `3`). `HypB_eG_745`: `hdiag` with `√(A c L₂)`, conclusion prefactor `m A c N` (uses `√(A c) ≤ A c`, `A c ≥ 1`; source `4 m c N`). `HypB_fixed`: `hCe: Ce ≤ 4 A m² N^{τ/2} N`, `hbig` with `3+4A` for `7`. All reduce to the source at `lam = 1`. Alternative not adopted: hypothesis `lam ≤ 1`.
**MISS list (twin or re-derive).**
| RBM2D name | RBM3D twin (file:line) / re-derive |
|---|---|
| `Kcal`, `KLoop.mSig` (HypB) | `KLK` (`Loop/KLTree.lean:145`), `STKloop` (`Induction/Defs.lean:64`); `mSigma` (`Defs/Semicircle.lean:85`) |
| `Ind.LLf` (HypB) | `loopL d L W (blockMat d L W M) (zt E u)` |
| `one_le_rpow` (HypB) | Mathlib `Real.one_le_rpow` (as in T2352 (c)) |
| `ZRescale_green_smul_mul`, `ZRescale_lemT_pos` (LLT) | re-derive (≈ 10 lines: `green (c•H) (c z) = c⁻¹ green H z`); `lemT_pos` (`Semicircle.lean:204`); `Main/ZTransfer.lean:57,100` is `im_identity`/`zRange`, not the scaling |
| `size_eq` (HypB, LLT) | re-derive `0 < size n`, `1 ≤ size n` from `three_le_L`, `W_pos` (≈ 6 lines each; `Sizes.size` is `(W L)^d` by `def`) |
| `eq_inv_sqrt_mul_spectralZ` | `eq_inv_sqrt_mul_zt` (`Semicircle.lean:270`); `zt_im_lemma28` (`:344`) gives `Im z_t = √t0 Im z` directly |
| `zztE_quant` | `lemma28_quant` (`:359`), same constants `1/16`, `\|lemE\| ≤ 2-κ` |
| `norm_green_le` | `norm_Gsig_le_inv_eta` (`Gauss/FlowCalculus.lean:644`, `Gres`, via `Gres H z true = green H z`); `Ind.norm_apply_le_l2_opNorm` (`Induction/Split.lean:670`) |
| `LLTransfer_continuous_ouMat` (LLT private) | `measurable_ouMat` (`Universality/OU.lean:80`, public, transitive import): the merged `ouMat` has `M.H n ω.1`, measurable not continuous; `integral_map` needs only measurability |
| `Pgue`, `map_gueH_last`, `gueH_measurable`, `gridTime_last`, `norm_msc_lt_one`, `norm_spectralM`, `lemT_lt_one` | merged (`Grid.lean:61,559,205`, `Path/Walk.lean:160`, `Semicircle.lean:152`, `FlowCalculus.lean:96`, `Semicircle.lean:209`) |
**LLTransfer conclusion.** Source (`green … x x`, `d.size`) is rewritten to the pinned body of `UNOULL` (`ZeroModeProfile.lean:97`) at fixed `(κ,E,t,δ,p)`: `Gres (ouMat (UNModel.band sz) n (t n) ω) (E n + i ouEtaLL sz τU n) true x x` and `Nsz sz n ^ δ` (`Pins.lean:372`, `= ((sz.size n:ℕ):ℝ)`); hypotheses `0 ≤ t n` (not `t n ≤ ouTStar`), `τU < 1/2`, `hd : Tendsto sz.size atTop atTop`; `map_gueH_last` is at `UNModel.band sz`, as needed.
**§29 (DECISIONS §29), one line each.** (1) time domain: `HypB_entry_le` has `t1 ≤ t0 < 1` (no `0 ≤ t1`; not used), `HypB_fixed`/`step_le`/`Kt_le_one`: `0 ≤ t1`, `t1 ≤ t0`, `t0 < 1` as in the source; LLT: `0 ≤ t n`, `lemT < 1`, `t1 = (1-ζ(t_n)) t0 ≤ t0`, collapsed only at `t_n = 0`, instance has `t_n = 4.8e-7 > 0`. (2) boundary: `hellN` with `lam² > L^d` restricts only `t1 ≥ 1 - lam²/L^d < 0`, harmless; instance 2 sits on the boundary (`64 = 64`). (3) `L`-`W` relation: none used (only `N=(W L)^d`, `W^{-d}`). (4) `∀ n` / `∀ᶠ n`: `hellN`, `hδN` are per-`n` hypotheses (consumer gets them from `Hyp`-level `∀ᶠ` and `HypB_ev_delta`); `he`, `ht` of LLT are `∀ n`, conclusions `∀ᶠ n`, finitely many `n` do not matter.

### Verdict per target
- (A) `HypB_entry_le`, `HypB_eG_745`, `HypB_fixed`: PASS (with T2354a; instance 2). `HypB_eG_746`, `HypB_q_745`, `HypB_ev_grid`, `HypB_ev_delta`, `HypB_highProb_range`, `HypB_step_le`, `HypB_Kt_le_one`, `HypB_Lproc_grid`, `HypB_Dproc_grid`, `HypB_sqrt_cont`: PASS (renaming only; `HypB_eG_746` with the inherited `hKinit` form). All names used exist in merged RBM3D except the MISS rows above (twins or re-derivations listed).
- (B) `oull_of_pathBounds`: PASS (all steps of the RBM2D proof carry over: the only `d`-token is `N=(W L)^d`, already in `sz.size`; the external `GUEPathBounds` stays a hypothesis).

## (a′) Preflight corrections — Fri Oct  9 01:49:45 UTC 2026
(a)(iii) "Departure T2354a ... All reduce to the source at `lam = 1`" is exact for `HypB_entry_le` (`A = 3`) and sharper for `HypB_eG_745` (`m A c N = 3 m c N ≤ 4 m c N`), but not for `HypB_fixed`: at `lam = 1`, `4A = 12` and `3 + 4A = 15` where the source has `4` and `7`. The port implements the departure exactly as (a) states it (`hCe : Ce ≤ 4 A m² N^{τ/2} N`, `hbig` with `3 + 4A`); the constants are not optimal (CLAUDE.md §7). No verdict changes: the consumer's pair `Ce := m A c N ≤ 4 A m² c N` (`m ≥ 1`) fits both statements. The file docstring and (d) T2354a say the same.

## (b) Script output — Fri Oct  9 01:49:45 UTC 2026 (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2354`, branch `t/T2354`)

**Build** (each module; full library; each file alone: number of message lines):
```
$ lake build RBM3D.Universality.GUEPhase.HypB | tail -1; ...LLTransfer | tail -1; lake build | tail -1; lake env lean <HypB.lean | LLTransfer.lean> | wc -l
Build completed successfully (3780 jobs).
Build completed successfully (3739 jobs).
Build completed successfully (4166 jobs).
0
0
```
**Sizes and the stop rule** (`git show <commit>:<file> | wc -l` at each section commit; stop line 2050):
```
f985a03 01:19:56 UTC HypB=1081 LLT=0
e5eb578 01:22:17 UTC HypB=1081 LLT=468
2328311 01:29:55 UTC HypB=1372 LLT=468
c0fae47 01:31:43 UTC HypB=1501 LLT=468
7db0a19 01:33:37 UTC HypB=1501 LLT=503
70371d1 01:44:24 UTC HypB=1504 LLT=503
```
**Axioms**: `lake env lean axioms.lean` (both modules imported, `#print axioms` of the 14 public declarations); and the 13 compiled instances (12 `example`s of `HypB.lean`, 1 of `LLTransfer.lean`, rewritten to `def`/`theorem` in a scratch copy with `#print axioms`):
```
public declarations: HypB_entry_le HypB_eG_745 HypB_eG_746 HypB_q_745 HypB_ev_grid HypB_ev_delta HypB_highProb_range HypB_fixed HypB_step_le HypB_Kt_le_one HypB_Lproc_grid HypB_Dproc_grid HypB_sqrt_cont oull_of_pathBounds 
$ ... | sed ... | sort | uniq -c ; ... | grep -c sorryAx/error/"does not depend"
  14 [propext, Classical.choice, Quot.sound]
0
instances:
  13 [propext, Classical.choice, Quot.sound]
0
```
**Registry pre-check** (uncommitted scratch file `import RBM3D`, `import` of the two new modules, `#assert_rbm_axioms`; then the same without the two modules; the two full outputs differ in two lines):
```
exit=0
axiom audit: 10505 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
< axiom audit: 10491 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
> axiom audit: 10505 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
<   RBM.Univ.GUEPhase.GUEPathBounds: 1 [no certificate]
>   RBM.Univ.GUEPhase.GUEPathBounds: 2 [no certificate]
```
**Targets** (statements extracted by script `python3 -I stmts.py stmt`, whitespace-normalised, `[n]` = line in the port; the full text is in the files):
```
[131] theorem HypB_entry_le (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} {τU : ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (n : ℕ) (hellN : (sz.L n : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) (hδN : gueDelta sz τU n ≤ (mE (E n)).im / 2) (ω : PathΩ sz) {c : ℝ} (hc : 0 ≤ c) (hD4 : ∀ (k : Fin (gueGridK sz n0 n + 1)) (i j : Idx d (sz.L n) (sz.W n)), {ω' : PathΩ sz | ∀ a b : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) a b‖ ≤ gueDelta sz τU n}.indicator (fun ω' => ‖(green (gueH sz t1 t0 (gueGridK sz n0) n k ω') (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) i j‖ ^ 2) ω ≤ c * (gueLmax sz E t1 t0 (gueGridK sz n0) n 2 k ω + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) {j : ℕ} (hj : j < gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω) (q : Idx d (sz.L n) (sz.W n)) : ‖(green (gueH sz t1 t0 (gueGridK sz n0) n j ω) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) q q‖ ≤ Real.sqrt ((1 + 2 * sz.lam n ^ 2) * c * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) 2)
[260] theorem HypB_eG_745 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz) {c : ℝ} (hc : 1 ≤ c) {l : ℕ} (hl : 1 ≤ l) (hdiag : ∀ q : Idx d (sz.L n) (sz.W n), ‖(green (gueH sz t1 t0 K n j ω) (zt (E n) (gridTime t1 t0 K n j)) - mE (E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)) q q‖ ≤ Real.sqrt ((1 + 2 * sz.lam n ^ 2) * c * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)) 2)) (x : (Fin (2 * l) → Bool) × (Fin (2 * l) → Zd d (sz.L n))) : ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤ (((2 * l : ℕ) : ℝ) * (1 + 2 * sz.lam n ^ 2) * c * ((sz.size n : ℕ) : ℝ)) * (RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)) 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)) (2 * l))
[320] theorem HypB_eG_746 {E t1 t0 : ℕ → ℝ} (K : ℕ → ℕ) (n0 : ℕ) (hn0 : 1 ≤ n0) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a) (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) (n j m : ℕ) (hu : gridTime t1 t0 K n j ∈ Set.Icc (t1 n) (t0 n)) (ω : PathΩ sz) (x : (Fin m → Bool) × (Fin m → Zd d (sz.L n))) : ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 K n j) (gueH sz t1 t0 K n j ω) (loopOf x.1 x.2)‖ ≤ ((m : ℝ) * ((sz.size n : ℕ) : ℝ)) * (gueDmax sz E t1 t0 K Kt n 1 j ω * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)) (m + 1))
[360] theorem HypB_q_745 {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) {a : ℝ} (ha : 0 ≤ a) {l : ℕ} (hl : 1 ≤ l) : Real.sqrt (a * RBM.Ind.loopMax d L W H z (2 * (2 * l))) ≤ Real.sqrt a * RBM.Ind.loopMax d L W H z (2 * l)
[416] theorem HypB_ev_grid (hsz : Tendsto sz.size atTop atTop) (n0 : ℕ) : ∀ᶠ n : ℕ in atTop, ((2 * n0 : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1 ∧ 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ (((sz.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0)
[427] theorem HypB_ev_delta {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (hsz : Tendsto sz.size atTop atTop) {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) : ∀ᶠ n : ℕ in atTop, gueDelta sz τU n ≤ (mE (E n)).im / 2
[457] theorem HypB_highProb_range {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (hsz : Tendsto sz.size atTop atTop) (M : ℕ) (Ξ : ℕ → ℕ → Set Ω) (h : ∀ m, 1 ≤ m → m ≤ M → HighProbAt P sz.size (Ξ m)) : HighProbAt P sz.size (fun n => {ω | ∀ m, 1 ≤ m → m ≤ M → ω ∈ Ξ m n})
[783] theorem HypB_fixed {τ : ℝ} (hτ : 0 < τ) (n0 : ℕ) {E t1 t0 : ℕ → ℝ} (τU : ℝ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hK : ∀ n, ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun s => Kt n s I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n t) I) (Set.Icc (t1 n) (t0 n)) t) (n m : ℕ) (ω : PathΩ sz) (g3 g4 : ℝ → ℝ) {Ce : ℝ} (hEb : |E n| < 2) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hm1 : 1 ≤ m) (hm : m ≤ 2 * n0) (hΔ : gridStep t1 t0 (gueGridK sz n0) n ≤ 1 - t0 n) (hgrid1 : ((2 * n0 : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ 1) (hgrid2 : 3 * ((2 * n0 : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ 2 * ((gueGridK sz n0 n : ℝ))⁻¹ ≤ (((sz.size n : ℕ) : ℝ)⁻¹) ^ (2 * n0)) (hbd : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1) (hKtc : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (gueScale sz E n t)⁻¹ ^ (J.length - 1)) (hbig : 2 + 2 ^ (2 * n0) + (3 + 4 * (1 + 2 * sz.lam n ^ 2)) * ((2 * n0 : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (hCe0 : 0 ≤ Ce) (hCe : Ce ≤ 4 * (1 + 2 * sz.lam n ^ 2) * (m : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ)) (hg3 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g3 u) (hg4 : ∀ u ∈ Set.Icc (t1 n) (t0 n), 0 ≤ g4 u) (hg3c : ContinuousOn g3 (Set.Icc (t1 n) (t0 n))) (hg4c : ContinuousOn g4 (Set.Icc (t1 n) (t0 n))) (h0 : ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n 0 ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf x.1 x.2) - Kt n (gridTime t1 t0 (gueGridK sz n0) n 0) (loopOf x.1 x.2)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (gueScale sz E n (t1 n))⁻¹ ^ m) (hM : ∀ k ≤ gueGridK sz n0 n, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n k ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf x.1 x.2) - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n 0 ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf x.1 x.2) - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range k, genMatGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j) (gueH sz t1 t0 (gueGridK sz n0) n j ω) (loopOf x.1 x.2)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n k - t1 n) * (⨆ j : Fin k, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * m))) + (gueScale sz E n (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ m)) (hq : ∀ j < gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 * RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 (gueGridK sz n0) n j ω)) (zt (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * m)) ≤ g4 (gridTime t1 t0 (gueGridK sz n0) n j)) (heG : ∀ j < gueStop sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) n ω, ∀ x : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ‖egtNGUE d (sz.L n) (sz.W n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j) (gueH sz t1 t0 (gueGridK sz n0) n j ω) (loopOf x.1 x.2)‖ ≤ Ce * g3 (gridTime t1 t0 (gueGridK sz n0) n j)) {t : ℝ} (ht : t ∈ Set.Icc (t1 n) (t0 n)) : gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n m t ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m, ((((sz.size n : ℕ) : ℝ) * etaT (E n) u)⁻¹ ^ (k - 1) + gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n k u ω) * gueDproc sz E t1 t0 (gueGridK sz n0) (gueDelta sz τU) Kt n (m - k + 2) u ω) (t1 n) t + (((sz.size n : ℕ) : ℝ) * etaT (E n) t)⁻¹ ^ m + ((sz.size n : ℕ) : ℝ) * (t - t1 n) * supOn g3 (t1 n) t + Real.sqrt (t - t1 n) * supOn g4 (t1 n) t)
[985] theorem HypB_step_le {E t1 t0 : ℕ → ℝ} {τU : ℝ} (n0 n : ℕ) (hEb : |E n| < 2) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (h730 : t0 n - t1 n ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU) * etaT (E n) (t0 n)) (hτU : 0 < τU) : gridStep t1 t0 (gueGridK sz n0) n ≤ 1 - t0 n
[1012] theorem HypB_Kt_le_one {E t1 t0 : ℕ → ℝ} {τU : ℝ} (hτU : 0 < τU) (n0 n : ℕ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hEb : |E n| < 2) (ht0 : t0 n < 1) (hK1 : ∀ p : TimeIcc t1 t0 n × LoopSet d (sz.L n) (2 * n0), ‖Kt n p.1 p.2.1‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (τU / 2) * (gueScale sz E n p.1)⁻¹ ^ ((p.2.1).length - 1)) (hscale : (gueScale sz E n (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU)) : ∀ t ∈ Set.Icc (t1 n) (t0 n), ∀ J : RBM.Loop.LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ 2 * n0 → ‖Kt n t J‖ ≤ 1
[1051] theorem HypB_Lproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (n m j : ℕ) (ω : PathΩ sz) (ht10 : t1 n ≤ t0 n) (hj : j < gueStop sz E t1 t0 K δ n ω) : gueLproc sz E t1 t0 K δ n m (gridTime t1 t0 K n j) ω = RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n j ω)) (zt (E n) (gridTime t1 t0 K n j)) m
[1061] theorem HypB_Dproc_grid (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (n m j : ℕ) (ω : PathΩ sz) (ht10 : t1 n ≤ t0 n) (hj : j < gueStop sz E t1 t0 K δ n ω) : gueDproc sz E t1 t0 K δ Kt n m (gridTime t1 t0 K n j) ω = gueDmax sz E t1 t0 K Kt n m j ω
[1069] theorem HypB_sqrt_cont {E t1 t0 : ℕ → ℝ} (n : ℕ) (hEb : |E n| < 2) (ht0 : t0 n < 1) : ContinuousOn (fun u => Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ * (etaT (E n) u)⁻¹ ^ 2)) (Set.Icc (t1 n) (t0 n))
[443] theorem oull_of_pathBounds {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (hτU1 : τU < 1 / 2) (n0 : ℕ) (_hn0 : 1 ≤ n0) (hd : Tendsto sz.size atTop atTop) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ) (hP : GUEPathBounds sz (fun n => lemE ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) (fun n => (1 - ouZeta (t n)) * lemT ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) (fun n => lemT ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I)) (gueGridK sz n0) n0 Kt) (δ : ℝ) (hδ : 0 < δ) (p : ℕ) : ∀ᶠ n in atTop, ∀ x : Idx d (sz.L n) (sz.W n), ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω) ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p) ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ
```
**Translation table** (RBM2D `Universality/GUEPhase/HypB.lean` 1021 lines, `LLTransfer.lean` 440 lines, HEAD 9e0f275 -> port). Token map (source -> port): `d : Sizes`, `d.L n`, `d.W n`, `d.size n` -> `sz : Sizes d`, `sz.L n`, `sz.W n`, `sz.size n`; `Z2 L` -> `Zd d L`; `LoopIdx` -> `RBM.Loop.LoopIdx`; `BlockIndex L W` -> `Vtx d L W`; `Idx L W` -> `Idx d L W`; `spectralZ`/`spectralM` -> `zt`/`mE`; `gloop L W (blockMat M) z` -> `loopL d L W (blockMat d L W M) z`; `RBM.Ind.LLf L W E u M` -> `loopL d L W (blockMat d L W M) (zt E u)`; `RBM.Ind.loopMax L W` -> `RBM.Ind.loopMax d L W`; `primRhsGUE/egtNGUE/genMatGUE/primBilGUE/norm_primBilGUE_le/avgErr L W` -> `... d L W`; `KLoop.mSig` -> `mSigma`; `KLoop.Kcal` -> `sz.STKloop` (on `loopOf`); `(((W*L)^2:ℕ):ℝ)` -> `(((W*L)^d:ℕ):ℝ)`; `(((W:ℕ):ℝ)^2)⁻¹` -> `(((W:ℕ):ℝ)^d)⁻¹`; `green`/`Gsig` -> `green`/`Gres` (`HypB_llErr_eq` through the private `HypB_Gres_true`; LLTransfer conclusion `Gres … true x x`); `(d.L n)^2 (1 - t1) ≤ 1` -> `L^d (1 - t1) ≤ lam^2`; A3 constants `3`, `4`, `7` -> `1 + 2 lam^2`, `A`, `3 + 4A` (T2354a); `LLTransfer_continuous_ouMat` -> `measurable_ouMat`; `zztE_quant`, `eq_inv_sqrt_mul_spectralZ`, `ZRescale_lemT_pos`, `norm_green_le` -> `lemma28_quant`, `eq_inv_sqrt_mul_zt`, `lemT_pos`, `norm_Gsig_le_inv_eta`; `ZRescale_green_smul_mul`, `size_eq`, `measurable_matrix_inv_apply` re-derived (private, prefix `LLTransfer_`/`HypB_`). Residual d=2 tokens (`Z2|d.L|d.W|d.size|spectralZ|spectralM|gloop|BlockIndex|Gsig|KLoop|LLf|^ 2 : ℕ`): HypB source 250 lines / port 6, LLTransfer source 63 / port 5; past the docstrings only the merged names `Hyp_trace_eq_gloop_one`, `norm_Gsig_le_inv_eta`.
Per-target source:port line and the word diff of the token-mapped RBM2D statement (the regex pass, `body.lean`) against the final port statement:
```
HypB_entry_le (src:110 port:131) DIFF:  -> (hd : 2 ≤ d) || 2 -> d || 1) -> sz.lam n ^ 2) || (3 -> ((1 + 2 * sz.lam n ^ 2)
HypB_eG_745 (src:220 port:260) DIFF: (3 -> ((1 + 2 * sz.lam n ^ 2) || (4 * ((2 -> (((2 ||  -> * (1 + 2 * sz.lam n ^ 2)
HypB_eG_746 (src:274 port:320) DIFF: I, -> {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), || I -> (loopOf σ a) || KLoop.Kcal (sz.L n) (sz.W n) -> sz.STKloop n || I) -> σ a)
HypB_q_745 (src:313 port:360) identical
HypB_ev_grid (src:369 port:416) identical
HypB_ev_delta (src:380 port:427) identical
HypB_highProb_range (src:410 port:457) identical
HypB_fixed (src:728 port:783) DIFF: 7 -> (3 + 4 * (1 + 2 * sz.lam n ^ 2)) ||  -> * (1 + 2 * sz.lam n ^ 2)
HypB_step_le (src:921 port:985) identical
HypB_Kt_le_one (src:948 port:1012) DIFF:  -> d
HypB_Lproc_grid (src:987 port:1051) identical
HypB_Dproc_grid (src:997 port:1061) identical
HypB_sqrt_cont (src:1005 port:1069) identical
oull_of_pathBounds (src:415 port:443): conclusion = body of UNOULL (narrative 5)
```
**Compiled instances** (`grep -n "^example"` plus the named checks `entry_at`, `step_at`; the data are in the docstrings at HypB.lean:1084-1091 and LLTransfer.lean:470-478):
```
HypB.lean:1214:private theorem entry_at (q : Idx 3 (szT.L 0) (szT.W 0)) :
HypB.lean:1244:example := HypB_eG_745 szT (E := E0) (t1 := tA) (t0 := tB) Kg 0 1 ω0 (c := 
HypB.lean:1248:example := HypB_q_745 (d := 3) (L := 3) (W := 2) (H := 0) Matrix.isHermitia
HypB.lean:1269:example : ∃ Kt : (n : ℕ) → ℝ → RBM.Loop.LoopIdx (Zd 3 (szT.L n)) → ℂ,
HypB.lean:1280:example := HypB_ev_grid szT hszT 2
HypB.lean:1282:example := HypB_ev_delta szT (κ := 1 / 10) (τU := 1 / 1000) (by norm_num) (
HypB.lean:1286:example := HypB_highProb_range szT (P := Pgue szT) hszT 3 (fun _ _ => Set.u
HypB.lean:1307:private theorem step_at : gridStep tA tB (gueGridK szT 2) 0 ≤ 1 - tB 0 :=
HypB.lean:1312:example := step_at
HypB.lean:1350:example := HypB_Kt_le_one szT (E := E0) (t1 := tA) (t0 := tB) (τU := 1 / 10
HypB.lean:1364:example := HypB_Lproc_grid szT E0 tA tB Kg (gueDelta szT τT) 0 2 1 ω0 (by n
HypB.lean:1367:example := HypB_Dproc_grid szT E0 tA tB Kg (gueDelta szT τT) Kt0 0 2 1 ω0 (
HypB.lean:1370:example := HypB_sqrt_cont szT (E := E0) (t1 := tA) (t0 := tB) 0 (by norm_nu
HypB.lean:1436:example : ∃ τ : ℝ, 0 < τ ∧ gueDproc szT E0 tA tB Kg (gueDelta szT τT) Kt0 0
LLTransfer.lean:490:example (Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd 3 (sz0.L n)) → ℂ)
```
**Name clash, public declarations, hygiene, files:**
```
clash: 0 hits outside the two files
public decls: HypB 13 theorems, 0 other; LLTransfer 1 theorem, 0 other
sorry/admit/native_decide/axiom: 0 / 0
RBM2D names declared in RBM3D outside Probe (Kcal mSig LLf one_le_rpow ZRescale_* size_eq eq_inv_sqrt_mul_spectralZ norm_green_le zztE_quant): 2 (both private: GUELocalBootstrap.lean:598 one_le_rpow, ProcK.lean:789 size_eq at sz0)
 RBM3D/Universality/GUEPhase/HypB.lean       | 1504 +++++++++++++++++++++++++++
 RBM3D/Universality/GUEPhase/LLTransfer.lean |  503 +++++++++
 2 files changed, 2007 insertions(+)
```
**Ports**: `git -C RBM2D log -1 --format=%h: 9e0f275; diff --stat 9e0f275 HEAD -- HypB.lean LLTransfer.lean | wc -l: 0; status --short: 0`

### Narrative (prover, claude-sonnet-5-5)
1. Two new files, six section commits (table above; stop line 2050 not reached): `HypB.lean` 1504 lines (port 1-1082, `HypBInst` 1084-1504), `LLTransfer.lean` 503 lines (port 1-468, `LLTransferInst` 470-503). The root import is the hub's.
2. Method: both RBM2D files went through one regex token pass (token map above), then the compile errors were fixed by hand. The word diff above is the complete list of statement differences: 8 of the 13 HypB targets are the token-mapped source verbatim; the other five differ as in 3-4.
3. Departure T2354a, the only mathematical change: the merged `gue_inv_W_le_loopMax` (`Proc.lean:539`) takes `hell : L² (1 - u) ≤ g²` and gives `(W⁻¹)^d ≤ 2 L^{d-2} g² L₂`. `HypB_entry_le` takes `hd : 2 ≤ d`, `hellN : L^d (1 - t₁) ≤ lam²` (the form of the merged `Hyp_Kt_detDom`), applies it with `g² = lam²/L^{d-2}`, so `(W^d)⁻¹ ≤ 2 lam² L₂` and `‖(G - m)_{qq}‖² ≤ c (1 + 2 lam²) L₂`: the A3 constant is `A = 1 + 2 lam²` (source `3`). `HypB_eG_745` uses `√(A c) ≤ A c` (`A c ≥ 1`) for the prefactor `m A c N` (source `4 m c N`); the private `HypB_path` carries `A ≥ 0`, `hCe : Ce ≤ 4 A m² c N` and `(3 + 4A) m²` for `7 m²`; `HypB_fixed` sets `A = 1 + 2 lam²`. For the constants at `lam = 1` see (a′).
4. `HypB_eG_746` has `hKinit` in the merged form (`Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a`, inherited T2352a(3)); `HypB_Kt_le_one` has `LoopSet d` (the merged `abbrev` carries `d`). HypB does not call `Hyp_Kt_detDom` (preflight (a)(iii)), so `hKb` and the eventual `hell` are not carried.
5. LLTransfer: the source proof under the port map. The conclusion is the body of `UNOULL sz τU` (`ZeroModeProfile.lean:97`) at fixed `(κ, E, t, δ, p)`: `∀ᶠ n, ∀ x, ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω) (E n + i ouEtaLL sz τU n) true x x‖^(2p) ∂ouP (UNModel.band sz) n ≤ Nsz sz n ^ δ`; internally the `green` form of `localLaw` is converted by the private `LLTransfer_Gres_true`. `E` for `e`; the only time hypothesis is `ht : ∀ n, 0 ≤ t n` (the pin also has `t n ≤ ouTStar`, not needed); `_hn0` is unused as in the source. Re-derived privately (the merged twins are private): positivity of `N`, `green (c • H) (c * z) = c⁻¹ • green H z`, `zt (lemE z) (lemT z) = √t₀ z`, measurability of `M ↦ G(M, z)_{ij}`; `measurable_ouMat` replaces the source's continuity of `ouMat` (`integral_map` needs measurability only).
6. Instances (HypB): `szT := { sz0 with lam := fun _ => 8 }` (`L = 4`, `W = 32`, `N = 2097152` at `n = 0`), path `ω₀ = 0` (`gueH = 0`; `entry_aux`: `‖G - m‖_max ≤ 1/500` for `u ∈ [0, 1/1000]`), `E ≡ 0`, `κ = 1/10`, `τ_U = 4/7` (`gueDelta = 1/8`, `gueDelta_val`), `n₀ = 2`, window `[0, 1/1000]`, `K = gueGridK szT 2`; `stop_eq : gueStop = K` (and `1 < K`), so every `j < gueStop` hypothesis is non-vacuous. `entry_at` (`HypB_entry_le`, `j = 1`, `c = 1`): `hellN` is the equality `64 = 64`, `hD4` is discharged for every `k ≤ K` and every entry (`(1/500)² ≤ (W^d)⁻¹`), `hδN` is `1/8 ≤ 1/2`. `HypB_eG_745` is applied to the output of `entry_at` (`hdiag`). `HypB_eG_746`: `Kt` from `gueK_exists` (private copy of the merged `HypAInst` step).
7. `HypB_fixed` instance: `K̃ = toyK` (`m_σ` on 1-loops, `0` on longer loops; `primRhsGUE toyK = 0`), `Ce = 1`, `g₃ ≡ ∑_{j ≤ K, x} ‖𝓔̃_j(x)‖`, `g₄ ≡ ∑_{j ≤ K} Q_j`, and `τ` from `exists_tau` with `N^{τ/2} ≥ 8322 + Cm`, where `8322 = 2 + 2⁴ + (3 + 4·129)·16` is the `hbig` constant (`A = 1 + 2·8² = 129`) and `Cm` the finite sums (over `x` and `k ≤ K`) that `h0` and `hM` need against `(N η)^{-2}`; `hgrid1/2` come from the private `HypB_grid_of_size`, `hΔ` from `step_at`, `hq`/`heG` from the sums. No hypothesis of `HypB_fixed` remains (the example is `∃ τ > 0, bound`).
8. `HypB_step_le`, `HypB_Kt_le_one` use the window `[0, 1/1000]` at `τ_U = 1/1000` (`half_le`: `N^{-τ_U} ≥ 1/2`); `HypB_ev_grid`, `HypB_ev_delta`, `HypB_highProb_range` are applied with `hsz = Sizes.tendsto_size sz0 sz0_tendsto` (`szT.size = sz0.size` by `rfl`), `Ξ ≡ univ`, `P = Pgue szT`, `M = 3`; `HypB_q_745` at `d = 3`, `L = 3`, `W = 2`, `H = 0`. `LLTransferInst`: `sz0`, `E ≡ 0`, `τ_U = 1/1000`, `n₀ = 2`, `t_n = ouTStar sz0 (1/1000) n`, `δ = 1/10`; `GUEPathBounds` (UN-50b's output) is the one hypothesis kept.
9. Data differences from section (a) (choices of data, not corrections): `szT` is `sz0` with `lam ≡ 8` (same values at `n = 0`); `τ` is existential instead of `τ = 3`; `hM` is discharged instead of kept as a hypothesis; one window `[0, 1/1000]` for the HypB window targets instead of the window of T2352; `HypB_Dproc_grid` takes `Kt0` (`toyK`).

## (c) Verified names
Script: `import` of the two modules, `open MeasureTheory RBM RBM.Gauss RBM.Path RBM.Univ`, `#check @NAME` for 93 names, `lake env lean names.lean`: 92 resolve, 1 error line (`Real.logb`, absent from the import closure: `exists_tau` uses `Real.log`, `Real.rpow_def_of_pos`).
Mathlib: Real.rpow_def_of_pos Real.exp_log Real.exp_add Real.log_pos Real.log_nonneg Real.rpow_neg Real.rpow_natCast Real.rpow_mul Real.rpow_add Real.rpow_one Real.rpow_nonneg Real.rpow_pos_of_pos Real.one_le_rpow Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow_of_exponent_le Real.sqrt_le_left Real.sqrt_le_one Real.sq_sqrt Real.le_sqrt Real.le_sqrt_of_sq_le Real.iSup_le Real.iSup_nonneg Nat.one_lt_pow one_le_inv₀ inv_le_comm₀ inv_anti₀ inv_le_one_of_one_le₀ pow_le_pow_left₀ pow_le_pow_right₀ pow_le_pow_of_le_one pow_le_one₀ Finset.single_le_sum Matrix.inv_eq_right_inv inv_eq_of_mul_eq_one_right Matrix.inv_smul Matrix.nonsing_inv_apply_not_isUnit Matrix.nonsing_inv_eq_ringInverse Set.indicator_apply Set.indicator_of_mem tendsto_rpow_atTop tendsto_natCast_atTop_atTop MeasureTheory.integral_map integral_mono integral_const_mul Matrix.isHermitian_zero Complex.abs_im_le_norm Complex.norm_real MeasureTheory.hittingBtwn measure_toMeasurable ENNReal.toReal_le_of_le_ofReal Integrable.of_bound.
RBM3D: gueK_exists norm_primBilGUE_le primRhsGUE_sub norm_egtNGUE_le gue_inv_W_le_loopMax gueLoopMax_odd_succ_le gueLoopMax_four_mul_le map_gueH_last gueH_measurable gueH_isHermitian gueGridK_ne_zero Hyp_Kt_one Hyp_Kt_disc Hyp_grid Hyp_interp_bound Hyp_eps_le_dev Hyp_time_mem (all `RBM.Univ.GUEPhase`); RBM.Green.{entryDom_goodEvent_of_llErr,llErrMat,avgErr}; RBM.Ind.{loopMax_nonneg,norm_gloop_le_loopMax,norm_apply_le_l2_opNorm}; RBM.Path.{gridTime_last,firstHit_le,lt_firstHit_imp}; RBM.{lemma28_quant,lemT_pos,lemT_lt_one,eq_inv_sqrt_mul_zt,zt_im_lemma28,norm_mE,mE_im_pos}; RBM.Univ.measurable_ouMat; RBM.Gauss.{norm_Gsig_le_inv_eta,etaT_eq_zt_im,highProbAt_univ,Xmat_smul,Sizes.tendsto_size,SizesInst.sz0_tendsto}; RBM.Loop.LoopIdx.length_cutGlueL.
Verified absent as public RBM3D declarations (grep line above): `Kcal`, `mSig`, `LLf`, `ZRescale_green_smul_mul`, `ZRescale_lemT_pos`, `eq_inv_sqrt_mul_spectralZ`, `norm_green_le`, `zztE_quant`; `one_le_rpow` and `size_eq` exist only as `private` (unusable): re-derived or replaced by `Real.one_le_rpow`.

## (d) Open issues and paper-delta candidates
- **T2354a** (statement differences to RBM2D `HypB.lean`): `HypB_entry_le` takes `hd : 2 ≤ d`, `hellN : L^d (1 - t₁) ≤ lam²` for `L² (1 - t₁) ≤ 1`, `(W^d)⁻¹` for `(W²)⁻¹` in `hD4`, concludes `√(A c L₂)`, `A = 1 + 2 lam²` (source `√(3 c L₂)`); `HypB_eG_745`: `hdiag` with `A`, prefactor `m A c N` (source `4 m c N`); `HypB_fixed`: `hCe : Ce ≤ 4 A m² N^{τ/2} N`, `hbig` with `3 + 4A` for `7` (constants not optimal; see (a′)). Reason: the Ward step `W^{-d} ≤ 2 L^d (1 - u) maxLoopPM` at `d ≥ 3` (merged `gue_inv_W_le_loopMax`).
- **T2354b** (inherited T2352a(3)): `HypB_eG_746` has `hKinit` for `loopOf σ a` with `sz.STKloop` (source: every `I`, `Kcal`).
- **T2354c**: `oull_of_pathBounds` concludes the `UNOULL` body (`Gres … true`, `Nsz`, `ouMat (UNModel.band sz) n`) instead of the source's `green`/`d.size`/`ouMat L W`; hypothesis `0 ≤ t n` only; `E` for `e`.
- Open 1 (instance data): `τ_U = 4/7` in the path instances is outside the paper's range (`τ_U ≤ ouTauMax ≤ 1/100`): `hδN : N^{-τ_U/4} ≤ Im m/2` at `n = 0` (`N = 2097152`) needs `N^{τ_U/4} ≥ 2`; the eventual regime is stated by the `HypB_ev_delta` instance at `τ_U = 1/1000`. `lam ≡ 8` (`Sizes` has no constraint on `lam`; `hellN` is an equality at `t₁ = 0`).
- Open 2: the `HypB_highProb_range` instance has `Ξ ≡ univ` (the statement is generic in the events; the data `P = Pgue szT`, `M = 3` are non-degenerate). The `HypB_fixed` example is `∃ τ > 0, bound` (τ large: `N^{τ/2} ≥ 8322 + Cm`); all hypotheses are discharged.
- Open 3: `GUEPathBounds` stays a hypothesis of the `oull_of_pathBounds` instance (UN-50b); the registry ledger line `RBM.Univ.GUEPhase.GUEPathBounds` goes from 1 to 2 theorems with the two modules (diff above); no registry change is requested by the ticket.
- Open 4: total size 2007 lines (`HypB` 1504: port 1082 + instances 421; `LLTransfer` 503) against the ticket's 1250 / 1500 / 1850; the binding stop 2050 was not reached.

## Repair — Fri Oct  9 02:01:20 UTC 2026 (repairer claude-opus-5-5; audit round 1, `docs/reports/T2354-audit.md` §7 items 1–3)
Commit `08b8c81` on `t/T2354`.
```
$ git diff --stat 70371d1 HEAD
 RBM3D/Universality/GUEPhase/HypB.lean | 68 ++++++++++++++++++-----------------
$ git diff --name-only main...t/T2354
RBM3D/Universality/GUEPhase/HypB.lean
RBM3D/Universality/GUEPhase/LLTransfer.lean
$ wc -l HypB.lean LLTransfer.lean
    1508 RBM3D/Universality/GUEPhase/HypB.lean
     503 RBM3D/Universality/GUEPhase/LLTransfer.lean
    2011 total
$ lake build RBM3D.Universality.GUEPhase.HypB 2>&1 | tail -1; hygiene grep
Build completed successfully (3780 jobs).   exit=0;  hyg=1 (no sorry/admit/native_decide/axiom)
$ grep -n "Finset.range (Kg 0 + 1)" HypB.lean      (no grid sum left; only maxima)
1400:private theorem rg_ne : (Finset.range (Kg 0 + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
1405:    ((Finset.range (Kg 0 + 1)).sup' rg_ne fun k => Finset.univ.sup' X2_ne fun x => AMj k x / scj k)
1408:private abbrev g3v : ℝ := (Finset.range (Kg 0 + 1)).sup' rg_ne fun j => Finset.univ.sup' X2_ne (AEj j)
1409:private abbrev g4v : ℝ := (Finset.range (Kg 0 + 1)).sup' rg_ne Qj
$ grep -n "fun _ => g3v\|fun _ => g4v\|le_sup' Qj\|le_sup' (AEj j)" HypB.lean
1453:          supOn (fun _ => g3v) (tA 0) (tB 0)
1455:          supOn (fun _ => g4v) (tA 0) (tB 0)) := by
1472:    (fun _ => g3v) (fun _ => g4v) (Ce := 1) (by norm_num [E0])
1499:    (fun j hj => Finset.le_sup' Qj (Finset.mem_range.2 (lt_K hj)))
1501:      have h1 := (Finset.le_sup' (AEj j) (Finset.mem_univ x)).trans
```
`Cm` (`:1403`) is now `max (max_x ‖L_0(x) - K̃‖/scj 0) (max_{k ≤ K} max_x AM_k(x)/scj k)`. Axioms of the
instance (scratch copy of HypB.lean with the `HypB_fixed` example `:1445` named `HypBfixedInst`, `lake env lean`):
```
'RBM.Univ.GUEPhase.HypBInst.HypBfixedInst' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Univ.GUEPhase.HypBInst.Cm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Univ.GUEPhase.HypBInst.AM_le_Cm' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Univ.GUEPhase.HypBInst.L0_le_Cm' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Univ.GUEPhase.HypBInst.g3v_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.RBM.Univ.GUEPhase.HypBInst.g4v_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Witness sizes (item 2), script `sizes.py` (closed forms at `H = 0`, derivation below):
```
$ python3 -I sizes.py
N = 2097152, K = (N+1)^128: log10(K+1) = 809.2
h0 term = N^2 W^-d = 1.34218e+08 = 2^27;  hM term <= 8.101e+05
Cm = 1.34218e+08 (max attained by the h0 term at x00);  tau = 4.5714
N^(tau/2) = 2.81492e+14 >= 8322 + Cm = 1.34226e+08
g3 <= 3.922e-06;  1.164e-10 <= g4 <= 1.168e-10
```
Narrative (derivation of the closed forms; none of these numbers is proved in Lean, the instance does not need them):
- `ω₀ = 0` gives `gueH = 0`, `z_u = zt 0 u = (1-u) i`, `Gres 0 z σ = g_σ I` with `g_+ = i/(1-u)`, `g_- = -i/(1-u)`,
  `|g| = r = 1/(1-u) ≤ 1000/999`; `Eblk a = W^{-d} 1_[a]` (`Loop/GLoop.lean:55`), so a loop of length `l`
  (`loopL`, `Loop/GLoopFlow.lean:123`) is `∏ g · W^{-d(l-1)}` if all blocks agree, else `0`.
- h0: `K̃ = toyK` is `0` on 2-loops, `scj 0 = (N η_0)^{-2} = N^{-2}`, so the first max is `N² W^{-d} = 2^27`, attained
  at `x00 = ((+,+),(0,0))`.
- hM: `AM_k ≤ u_k (2 sup|∂_u L| + sup|Itô|)` with `|∂_u L| ≤ 2 r³ W^{-d}`; the Itô term `½ Σ_c gueVar ∂²_c L`
  (coordinate matrices `e_ij + e_ji`, `i e_ij − i e_ji`, `e_ii`, `Gauss/FineModel.lean:105`; `gueVar`,
  `Universality/Pins.lean:61`; `Σ_c gueVar C_c² = I`, `Σ_c gueVar tr(C E_a C E_b) = N^{-1}`, each summand ≥ 0)
  is at most `r⁴ (2 W^{-d} + N^{-1})`; `scj k⁻¹ ≤ N²`.
- g3: `|avgErr| = |g_σ − m_σ| = u/(1-u) ≤ 1/999`, cut loops have length 3 (`cutGlue`, `GLoopFlow.lean:317`),
  so `‖𝓔̃‖ ≤ 2 L^d W^{-d} r³/999`. g4: `Q_j = (N^{-1} η_j^{-2} r_j⁴ W^{-3d})^{1/2}`.
- So `Cm = 2^27`, `τ = 2 log(8322 + Cm)/log N + 2 ≈ 4.57` (`exists_tau`, `:1376`), `g₃ ≤ 3.9·10⁻⁶`, `g₄ ≈ 1.17·10⁻¹⁰`:
  none scales with `K`. `τ` is set by `h0` because `K̃ = toyK` vanishes on 2-loops (audit observation O3);
  the preflight's `τ = 3` is not reached with this `K̃`.
Verified Mathlib names (repair): `Finset.le_sup'` (`Data/Finset/Lattice/Fold.lean:564`, `f` explicit),
`Finset.le_sup'_of_le` (`:572`), `Finset.univ_nonempty` (`Data/Finset/BooleanAlgebra.lean:50`).
