Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct  9 00:10:31 UTC 2026

Source: RBM2D `Universality/GUEPhase/OneLoop.lean` (1729 lines, RBM2D HEAD 9e0f275); line numbers below are that file's.
Targets (maths): `olComb/olVar/ol_map_comb(_slice)/ol_gueH_eq` (law of `√t₁ω₀+√(Δ/N)Σ_{i≤k}ω_i`) and `gueGrid_expect_oneLoop`
(pathwise `‖⟨(G-m)E_a⟩‖ ≺ (Nη_u)⁻¹` ⇒ `‖𝔼⟨(G-m)E_a⟩‖ ≤ N^ε (Nη_u)⁻²` eventually, all ε>0, uniformly in grid step and block).

### (i) Exponent table (d = 3 values; instance data of (ii): L=4, W=32, lam=1/64, N=2097152, E=1, κ=1/2, t₁=0.9e^{-1/20}, t₀=0.9, K=4)
| quantity | value / constraint | slack |
|---|---|---|
| dimension `d` | `3 ≤ d` (`Prop5Short` is `3 ≤ d →`, `Propagator/Pins.lean:~38`) | 0 at d=3 |
| coupling window `Λ`, `g = sz.lam n` | `0 < g ≤ Λ` (`prop5Short_holds`, `Propagator/Prop5Short.lean:400`); Λ=𝔡⁻¹=10 from `(eq:WO)` | g=1/64 vs 10: factor 640; `W^{-d/2+𝔡}=0.0078 ≤ g` |
| bulk `κ''=√(κ(4-κ))/2` | `κ'' ≤ Im m(E)` for `|E|≤2-κ` (`stability_bulkIm_le`, `Green/Stability.lean`, private) | 0.6614 vs 0.8660 |
| `gapK κ` | `‖1-u m²‖ ≥ gapK`, `u≥0` (`Loop.gapK_le_norm`, `Loop/KLSumZero.lean:456`) | 0.9354 vs 1.609 (u=t₁), 1.646 (u=0.9) |
| row-sum constant `K_Θ=C_s(1+Λ²expC(d-2,c_s))` | `max_a Σ_b‖Θ_{t m²}(a,b)‖ ≤ K_Θ`, all `t∈[0,1)`, all `L≥3` (replaces `1+cShortRow κ(1+log L)`) | proof const 4.63e22; actual row sum 0.5783 (g=1/64), 2.326 (g=1) |
| stability const `K'=K_Θ(1+1/gapK)` | `‖x‖_∞ ≤ K' B` for `x=m²Ŝx+y`, `‖y‖≤B`, `Ŝ=t₁SB+σJ`, row sums `u<1` | proof 9.58e22; actual `‖(1-m²Ŝ)⁻¹‖_{∞→∞}` 0.62-0.64 vs `R_Θ(1+1/gapK)`=1.288 |
| row-sum identity | `t₁+L^d·(c₀W^d)=u`, `c₀=kΔ/N`, `N=(WL)^d` (no `2`; exact) | residual 0.0 |
| time | `u=t₁+kΔ ≤ t₀ <1`; `η=(1-u)Im m ≤ 1`; `Λ_u=(Nη)⁻¹` | `1-u ≥ 0.1`; η 0.0866..0.1246 |
| envelope | `‖loopL‖ ≤ (LW)^d η⁻¹(W^d)⁻¹ = L^d η⁻¹ ≤ Nη⁻¹` (needs only `L^d ≤ (WL)^d`); `‖·-m‖ ≤ 2Nη⁻¹=2N²Λ_u` | 64 ≤ 2097152 |
| failure exponent `D` | need `N^{-D}(2N²Λ)² ≤ 4Λ²` i.e. `D ≥ 4`; source uses `D=5` (`StochDomAt` gives any `D>0`) | ratio `N^{-1}`=4.77e-07 |
| `ρ=N^{ε/4}`, `X=N^{ε/2}`, `N^ε=X²` | `K'(X+4) ≤ X²` follows from `X ≥ 8K'+1` (then `X² ≥ 8K'X+X`); eventually, only `N→∞` | N≥ (7.66e23)^{2/ε}: ε=2: n≥9, ε=1: n≥200 (sz0, proof consts) |
| `ε` vs hypothesis | conclusion `N^εΛ² < Λ` iff `N^εΛ<1` | ε < 0.8319 at k=K (n=0) |
| `N→∞` | `N_n=2^21(n+1)^18` for `sz0` (`Defs/Sizes.lean` `SizesInst.sz0`), `N_0=2^21` | `hsize` hypothesis, as source |

**d = 2 token table (source line → d-dim replacement).**
| token (count) | source lines | replacement |
|---|---|---|
| `Z2 L` (93) | 47-49,612-1651 | `Zd d L`; `Fintype.card (Z2 L)=L^2` (1008,1188,1307) → `L^d` (unfold `Zd`,`Fintype.card_fun`,`ZMod.card`, cf. `card_BlockIndex`, `Gauss/FlowCalculus.lean:701`) |
| `(L:ℝ)^2` (19) | 964,1174-1232,1277,1304,1388,1460,1505,1541-1567,1680 | `(L:ℝ)^d`; `hL2N : L^2≤N` → `L^d ≤ N` from `N=W^d L^d`, `1≤W^d` (`one_le_pow₀`); `hLN: L≤N` (1685, `le_self_pow₀ _ two_ne_zero`) → `d≠0` from `hd` |
| `(W:ℝ/ℂ)^2`, `(W⁻¹)^2` (24) | 766-982,1277,1302 | `^d`: σ=`c₀W^d`; `tr G=W^d Σ_p tr(G E_p)`; `tr(GE_aE_q)=δ_{aq}(W⁻¹)^d tr(GE_a)` |
| `(L*W)^2` (6) | 631,683,694,858,880,881 | `(L*W)^d` (`norm_matrix_trace_le_card_mul`+`card_BlockIndex`) |
| `size` (24) | 18-1681 | `d.size n=(W L)^2` (`Sizes.size_eq`, 1460,1655) → `sz.size n=(W n*L n)^d`, definitional (`Sizes.size`); `hNeq` by `mul_pow` |
| other `^ 2` (≈100) | ρ²,Λ²,`a²,b²` in `olVar`, norms | dimension-free: unchanged |
| `log` (35) | see next table | `K_Θ` / deleted |
`log L` lines: 19,34,39,42,43,50 (docstring); 1133-1166 `OneLoop_theta_row_sum` (`xiRowBoundShort`,`xiMat`,`ukerMat`,`mSig`,`hone`): statement → `Σ_{a'}‖Theta d L g (t·mE E^2) a a'‖ ≤ K_Θ`, proof = `stability_rowsum_le` (`Green/Stability.lean:268-318`, private; re-derive ≈40 lines from public `prop5Short_holds`, `expC`/`sum_radial_exp_decay_le` (`Defs/RadialSum.lean:271,275`), `Theta_apply_add_right_of_three_le`, `Props4.lean:100`) with `PropSpin (mE E) true * PropSpin (mE E) true = mE E^2` as at `Stability.lean:343-345`; 1171,1177,1257,1259 (`OneLoop_stable`): `1+cShortRow κ(1+log L)` → `K_Θ`; 1274,1291,1418,1420,1439,1453 (`OneLoop_expect_core/bound`): same; 1606-1624 `OneLoop_log_absorb`: delete, use `tendsto_rpow_atTop` ∘ `hsz` for `8K'+1 ≤ N^{ε/2}` (1672: `C := 8(1+1/g)+1` → `8K_Θ(1+1/g)+1`); 1699-1711 (`Rl`,`hlogL`,`hRlN`) and `hcs: 0≤cShortRow` (1664-1668, uses `cShortRow`,`cProp5`): delete, `hCs` is the absorption itself. Alternative to the row sum: public `stable_svar_bulk_vtx` (`Green/Stability.lean:320`, `Stable (svar d L W g) (t m²) (Kstab3 d Λ κ)`, `Kstab3` :212) applied to `v(a,α)=x a` gives `‖x‖≤Kstab3·B` for `x=t₁m²SBᵀx+r` (lift as in `stable_svar_vtx` :80, `stability_svar_cast` :70); prover chooses. No other line uses `cShortRow`/`cProp5` (grep: 39,50,1133-1711 as listed; `hLN` at 1685 uses `le_self_pow₀ … two_ne_zero` and survives with `d≠0`).

### (ii) Concrete nondegenerate instance (d=3, `SizesInst.sz0` at n=0, the `Grid.lean` §GridCheck data: `Grid.lean:795-860`)
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/ec1cbe39-5957-4519-82e4-38af3363ddc4/scratchpad/T2353/inst.py
N=2097152 L^d=64 W^d=32768 LW^d=2097152  t1=0.856106 t0=0.90 g=0.015625 gapK=0.935414
k=0 u=0.85611 eta=0.12462 Lam=3.826e-06  t1+L^d*sig-u=0.0e+00  u<1:True  L^d<=N:True  N^-5*Env^2/(4Lam^2)=4.768e-07
k=4 u=0.90000 eta=0.08660 Lam=5.506e-06  t1+L^d*sig-u=0.0e+00  u<1:True  L^d<=N:True  N^-5*Env^2/(4Lam^2)=4.768e-07
kappa''=0.6614 c=7.266e-04 C=2.100e+04 expC=2.204e+16  K_Theta=C(1+L^2 expC)=4.629e+22  Kstab3=4.629e+22
stability constant K_Theta*(1+1/gapK)=9.578e+22
eps=0.5: need N^(eps/2)>=7.663e+23  i.e. N>=3.447e+95  i.e. sz0 index n>=90455
eps=1.0: need N^(eps/2)>=7.663e+23  i.e. N>=5.871e+47  i.e. sz0 index n>=200
eps=2.0: need N^(eps/2)>=7.663e+23  i.e. N>=7.663e+23  i.e. sz0 index n>=9
u=0.85611 |1-u m^2|=1.60904 >= gapK=0.93541; Im m=0.8660 >= kappa''=0.6614; W^(-d/2+1/10)=0.00781 <= lam=0.01562 <= 10
u=0.90000 |1-u m^2|=1.64621 >= gapK=0.93541; Im m=0.8660 >= kappa''=0.6614; W^(-d/2+1/10)=0.00781 <= lam=0.01562 <= 10
k=K: N^eps*Lam^2 < Lam  iff eps < 0.8319 ; N_n=2^21(n+1)^18 at n=0: 2097152
$ python3 .../T2353/rows.py   # numerical check of the log-token replacement (R = Σ_a|Θ_{t m²}(0,a)|, FFT, t=1-1e-6, E=1)
d=2 (g=1, uniform 5-point SB) vs d=3: R(L)=sum_a|Theta_{t m^2}(0,a)|, t=1-1e-6
d=2 g=1.00000  L=8: 1.9194; L=32: 1.9240; L=128: 1.9240; L=512: 1.9240; L=2048: 1.9240
d=3 g=1.00000  L=4: 2.2171; L=8: 2.3225; L=16: 2.3260; L=32: 2.3260; L=64: 2.3260
d=3 g=0.01562  L=4: 0.5783; L=8: 0.5783; L=16: 0.5783; L=32: 0.5783; L=64: 0.5783
k=0 u=0.8561  max-row-sum |(1-m^2 S^)^-1| = 0.62238  <= R_Theta(t1)*(1+1/gapK) = 0.62238 * 2.0690 = 1.28773 : True
k=4 u=0.9000  max-row-sum |(1-m^2 S^)^-1| = 0.63847  <= R_Theta(t1)*(1+1/gapK) = 0.62238 * 2.0690 = 1.28773 : True
```
(rows.py prints k=0..4; k=1..3 omitted here, all `True`, values 0.62647, 0.63052, 0.63452.) The script's `K_Theta` uses the explicit constants of the `prop5Short_holds` docstring (`Prop5Short.lean:398-399`) at Λ=10; the Lean proof does not need the numbers (it uses `∃ C c` of `prop5Short_holds`).
Hypotheses of the main target at this data: `3≤d` ✓; `0<κ` ✓; `hsize` (N_n→∞) ✓; `|E|=1 ≤ 3/2` ✓; `0≤t₁≤t₀<1` ✓ (0.856 ≤ 0.9); `K=4≠0` ✓; `0<lam≤Λ` ✓ (1/64 ≤ 10, and `lam_n=(2(n+1))^{-6}→0`, in `(0,10]` for all n); external `h1` (`StochDomAt` pathwise one-loop bound, another gate's pin) stays a hypothesis of the instance; the conclusion is taken with `Filter.Eventually.exists` (no explicit n: the proof constants first bite at n≥9 for ε=2, n≥200 for ε=1, so the instance must not name an n).
Limit computation for the external hypothesis (TEAM §8 lesson 14): `Λ_n=(N_nη)⁻¹ ≤ 11.6/N_n → 0` (η≥0.0866, N_n=2^21(n+1)^18); hypothesis size `Λ`, conclusion size `N^εΛ²`; ratio conclusion/hypothesis `N^εΛ → 0` for ε<1 (η bounded below), so the conclusion is a strict improvement and not contradictory; at n=0,k=K ε<0.83 already.
Real-variable core: `OneLoop_expect_core` at the numbers above (`t₁,c₀,σ,u,v`) has every deterministic hypothesis discharged (row-sum identity exact, `u<1`, `|E|≤2-κ`).

**(ii-b) Twins of RBM2D names not found by name in RBM3D (by content); signatures vs source uses.**
| RBM2D (source use) | RBM3D twin (file:line) |
|---|---|
| mixed-grid carrier, `OneLoop_Pgue_eq_mixed`, `OneLoop_map_slice_infinitePi`, `OneLoop_map_combined_eq_mixed`, `seqXmat_add/smul/sum`, `real_smul_matrix` (source 70-389) | public in `Grid.lean`: `GUEPhaseGrid_map_combined_eq_mixed:428`, `_Pgue_eq_mixed:473`, `_map_slice_infinitePi:484`, `_seqXmat_add/smul/sum:128-138`, `_real_smul_matrix:145` (source 70-389 not re-ported) |
| `GaussianProduct.law/stein`, `integrable_id_gaussianReal` | `Gauss/DominationAt.lean:559`, `Gauss/Stein.lean:182` (same argument shape as `LoopFlowStein.lean:495`) |
| `sum_coordinateBlock_trace_pair L W A C` | `Hierarchy/ContractionSecondLoop.lean:239`, extra explicit `d`, `g` first; RHS `(W:ℂ)^d*Σ_pΣ_q tr(AE_p) SB d L g p q tr(CE_q)`, `gvarF d L W g γ` |
| `trace_coordinate_real/imag/diag`, `idxKey_*`, `coordinateMatrix_lower_zero/diag_imag_zero`, `blockRelabel_submatrix_split` | public, `Hierarchy/ContractionBasic.lean:225,237,251,554,532,696`; `Gauss/FineModel.lean:75,116` |
| `OneLoop_trace_blockRelabel`, `_blockRelabel_mul`, `trace_coordinateBlock_pair`, `sum_Eblk`, `Eblk_mul_Eblk`, `gloopProd_cons/nil` | private twins (`ContractionSecondLoop:54`, `ContractionBasic:755` `Σ_a Eblk a=(W^d)⁻¹•1`, `LoopGenerator:462`, `GLoopFlow:391,394`): re-derive locally (≤15 lines each) |
| `Gsig_true`, `gloop L W H z ⟨[true],[b]⟩ = tr(G E_b)` | `loopL d L W H z I` (`GLoopFlow.lean:123`) `= tr(foldr …)`; `green H z` ↦ `Gres H z true` (`:74`), `trace_Eblk_eq_one` (`LoopGenerator:431`) |
| `norm_green_le`, `OneLoop_sub_mul_green` | `norm_Gsig_le_inv_eta` (`FlowCalculus:644`); `isUnit_sub_smul_one_of_im_ne_zero` (`Induction/ConArgDet:380`) + `Ring.mul_inverse_cancel` |
| `norm_gloop_le_crude`, `continuous_gloop_HflowBlock_sample`, `hasDerivAt_green_HflowBlock_update`, `Xblock_eq_sum_coordinates` | `FlowCalculus:708,348`; `LoopCoordinate:69`; `LoopFlowStein:106`. Crude bound is `(LW)^d·(η⁻¹(W^d)⁻¹)^{len}`; `len=1` by `List.length_singleton`, `inv_pow` for `(W⁻¹)^d` |
| `xiMat`, `xiRowBoundShort`, `cProp5`, `cShortRow`, `ukerMat`, `KLoop.mSig`, `Theta_mul` | no twin needed: replaced by `K_Θ` row sum (above). `ukerMat` exists (`Path/Kernel.lean:46`), unused. `Theta_mul_of_three_le` (`Props4:86`), `SB_transpose` (`Block.lean:58`), `sum_SB_row`, `sum_nnnorm_SB_row` (`Block.lean:108,124`) |
| `KLoop.gapK`, `OneLoop_gapK_le_norm`, `spectralM_*` | `Loop.gapK` (`KLSumZero:424`, `gapK_pos` private: re-derive 3 lines), `gapK_le_norm :456` (states `mSigma E s*mSigma E s`; `mSigma E true=mE E`), `mE`/`zt` (`Semicircle`), `norm_spectralM`, `spectralM_quadratic`, `spectralZ_im` (`FlowCalculus:96,89,51`), `etaT_pos` (`GLoop:83`) |
| Local lemmas of the source `size_eq`, `one_le_rpow` | trivial re-derivations (`Sizes.size` def; `Real.one_le_rpow`) |
Signature points: `Theta d L g ξ`, `SB d L g` carry `g`: `g=sz.lam n` throughout (`Sizes.seqGvar sz ⟨n,c⟩ = gvarF d (sz.L n) (sz.W n) (sz.lam n) c`, `FineModel:164`, `rfl` as source `hg`). `CoordF d L W` replaces `Coord L W`, `Ω d L W` replaces `Ω L W`. Pre-named cut (:430 in source = end of `ol_*`, lines 394-433) is available, but with 320 lines of 70-389 not re-ported the central share is smaller.

**§29 items.** (1) time domain: `0 ≤ t₁ ≤ t₀ < 1`, `K n ≠ 0`, `k ≤ K n` explicit hypotheses as source; `u<1`. (2) `ilambda²/L²` boundary: not used (only `0<g≤Λ`). (3) `L`-`W` relation: none used; only `L^d ≤ N=(WL)^d`, `3≤L`, `W>0`. (4) `∀ n` vs `∀ᶠ n`: the added `0<lam n≤Λ` must be `∀ᶠ n` (as `Sizes.WO`), conclusion is `∀ᶠ`; source's `∀ n` hypotheses `hE,ht1,ht10,ht0,hK` unchanged. (5) per-time (`StochDomAt` unions inside `h1`) as source. (6) parameter lower/upper bounds: `lam ≤ Λ`, `0<lam` and `N→∞` written as hypotheses (`hsize`; `hlam : ∀ᶠ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ`); `W^{-d/2+𝔡} ≤ lam` is not needed. (7) scale: `N^ε` vs `(Nη)⁻²`, no `log W` or `W^τ` (the `log L` of source disappears).

### Verdict per target
- `olComb`, `olComb_measurable`, `olVar`, `ol_map_comb`, `ol_map_comb_slice`, `ol_gueH_eq`: PASS (index renaming only; `Grid.lean` public lemmas cover the carrier; `olVar`'s `seqGvar` is `rfl`).
- `gueGrid_expect_oneLoop`: PASS, with one statement change required by the mathematics: add `(hd : 3 ≤ d) {Λ : ℝ} (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)` (source has no `g`; the `d≥3` row-sum bound `K_Θ` of `prop5Short_holds` needs `0<g≤Λ`; `Sizes.WO 𝔡` gives it with `Λ=𝔡⁻¹`). The conclusion keeps the form `∀ ε>0, ∀ᶠ n, ∀ p, ‖𝔼…-m‖ ≤ N^ε(Nη)⁻²`; the `log L` factor is replaced by `K_Θ(d,Λ,κ)` independent of `L`; no log table entry FAILs (35 `log` tokens classified above). BLOCKED/FAIL: none.
- Paper-delta candidates: `T2353a` (extra hypotheses `3≤d`, `lam ∈ (0,Λ]` eventually vs the d=2 source); `T2353b` (`1+cShortRow κ(1+log L)` ↦ `K_Θ(d,Λ,κ)`, no `log L`).

## (b) Script output (commit `c924852` on `t/T2353`; evidence run Fri Oct  9 00:47:16 UTC 2026; written Fri Oct  9 00:47:58 UTC 2026)

File `RBM3D/Universality/GUEPhase/OneLoop.lean`: 1528 lines (ticket stop line 2300 not reached; `wc -l` of the file at each commit of the branch: 927 at `d772b96`, 1355 at `d1ee7b2`, 1525 at `697816c`, 1525 at `2cf106a`, 1528 at `c924852`).

### b.1 Build, registry pre-check, hygiene
```
$ lake build RBM3D.Universality.GUEPhase.OneLoop > b1.log 2>&1; echo "exit=$?" >> b1.log; tail -2 b1.log
Build completed successfully (3743 jobs).
exit=0
$ lake env lean RBM3D/Universality/GUEPhase/OneLoop.lean > lean.out 2>&1; echo "exit=$?"; wc -l < lean.out   # no warning, no message
exit=0
0
$ lake env lean registry_precheck.lean > pre.log 2>&1; echo "exit=$?" >> pre.log; head -4 pre.log; tail -1 pre.log   # temp file outside the repo: import RBM3D; import RBM3D.Universality.GUEPhase.OneLoop; #assert_rbm_axioms
axiom audit: 10475 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
exit=0
$ diff pre_base.log pre.log   # pre_base.log = the same pre-check without the OneLoop import (premise ledgers: every count identical, so the module's theorems rest on no ledgered premise)
1c1
< axiom audit: 10470 theorems, 3076 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 10475 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake build > fullbuild.log 2>&1; echo "exit=$?" >> fullbuild.log; tail -2 fullbuild.log   # whole library in the worktree (the root does not import OneLoop yet; the hub adds the import at merge)
Build completed successfully (4163 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^ *axiom " OneLoop.lean | wc -l   ->  0
$ grep -c "^private" OneLoop.lean   ->  48 ;  grep -n "^private" OneLoop.lean | grep -v "OneLoop_\|OneLoopInst_" | wc -l   ->  0   # CLAUDE.md 3 (E)
```
### b.2 Axioms (`#print axioms`: 7 targets, 12 private lemmas of the chain, `OneLoopInst_main`)
```
$ lake env lean ax.lean > axioms.out   # ax.lean = OneLoop.lean + 20 `#print axioms` lines
$ grep -c "depends on axioms" axioms.out;  sed "s/.*depends on axioms: //" axioms.out | tr -d '\n' | sed 's/\]/]\n/g' | sed 's/^ *//' | sort | uniq -c;  grep -c sorryAx axioms.out
20
  20 [propext, Classical.choice, Quot.sound]
0
```
### b.3 Targets: statements extracted from the file by script (whitespace joined), and the comparison with the source under the port map
```
def olComb (a b : ℝ) (k : ℕ) (ω : PathΩ sz) : Sizes.SeqΩ sz :=
theorem olComb_measurable (a b : ℝ) (k : ℕ) : Measurable (olComb sz a b k) :=
def olVar (a b : ℝ) (k : ℕ) : Sizes.SeqCoord sz → ℝ≥0 :=
theorem ol_map_comb (a b : ℝ) (k : ℕ) : (Pgue sz).map (olComb sz a b k) = Measure.infinitePi (fun c : Sizes.SeqCoord sz => gaussianReal 0 (olVar sz a b k c)) :=
theorem ol_map_comb_slice (a b : ℝ) (k n : ℕ) : (Pgue sz).map (fun ω => Sizes.slice sz n (olComb sz a b k ω)) = GaussianProduct.law (fun c : CoordF d (sz.L n) (sz.W n) => olVar sz a b k ⟨n, c⟩) :=
theorem ol_gueH_eq (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) : gueH sz t1 t0 K n k ω = Xmat d (sz.L n) (sz.W n) (Sizes.slice sz n (olComb sz (Real.sqrt (t1 n)) (Real.sqrt (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ))) k ω)) :=
theorem gueGrid_expect_oneLoop (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) {E t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} (hsize : Tendsto (fun n => sz.size n) atTop atTop) (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) (hK : ∀ n, K n ≠ 0) (h1 : StochDomAt (Pgue sz) sz.size (fun n (p : Fin (K n + 1) × Zd d (sz.L n)) ω => ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω)) (zt (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ - mE (E n)‖) (fun n p _ => (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹)) : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (K n + 1) × Zd d (sz.L n), ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueH sz t1 t0 K n p.1 ω)) (zt (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue sz)) - mE (E n)‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (gueScale sz E n (gridTime t1 t0 K n p.1))⁻¹ ^ 2 :=
$ python3 -I stmts.py   # source statement after the token map of b.6 vs this file; "identical" = equal as whitespace-joined text
=== olComb   source OneLoop.lean:394   this file:91
mapped source statement == this file statement (identical)
=== olComb_measurable   source OneLoop.lean:397   this file:94
mapped source statement == this file statement (identical)
=== olVar   source OneLoop.lean:404   this file:101
mapped source statement == this file statement (identical)
=== ol_map_comb   source OneLoop.lean:410   this file:107
mapped source statement == this file statement (identical)
=== ol_map_comb_slice   source OneLoop.lean:417   this file:115
mapped source statement == this file statement (identical)
=== ol_gueH_eq   source OneLoop.lean:426   this file:125
mapped source statement == this file statement (identical)
=== gueGrid_expect_oneLoop   source OneLoop.lean:1642   this file:1308
  replace: source[{κ] -> this[(hd : 3 ≤ d) {Λ κ]
  insert: source[] -> this[(hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)]
```
### b.4 Compiled nonempty instances (namespace `RBM.Univ.GUEPhase.OneLoopInst`, extracted by script; 11 `example`s and the private theorem `OneLoopInst_main`)
Data: `SizesInst.sz0` (`d = 3`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `lam n = (2(n+1))^{-6}`), `Grid.lean` §GridCheck grid (`t₀ = 9/10`, `t₁ = (1 - ζ(1/20)) t₀ = 0.856`, `K = 4`), `E = 1`, `κ = 1/2`, `Λ = 10`.  Every deterministic hypothesis of `gueGrid_expect_oneLoop` is discharged; only `h1` (the `StochDomAt` pathwise one-loop bound, the §7.2 output = another gate's pin) stays a hypothesis; its limit check is (a)(ii), last paragraphs.
```
example (ω : PathΩ sz0) : olComb sz0 (1 / 2) (1 / 3) 0 ω = (1 / 2 : ℝ) • ω 0 := by simp [olComb]
example (ω : PathΩ sz0) : olComb sz0 (1 / 2) (1 / 3) 4 ω = (1 / 2 : ℝ) • ω 0 + (1 / 3 : ℝ) • ∑ i ∈ Finset.Icc 1 4, ω i := rfl
example : Measurable (olComb sz0 (1 / 2) (1 / 3) 4) := olComb_measurable sz0 _ _ _
example (i : Idx 3 (sz0.L 0) (sz0.W 0)) : (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, i, true)⟩ : ℝ) = (1 / 2) ^ 2 * (Sizes.seqGvar sz0 ⟨0, (i, i, true)⟩ : ℝ) + 4 * ((1 / 3) ^ 2 * 1) := by simp [olVar, gueUnitVar]
example (i j : Idx 3 (sz0.L 0) (sz0.W 0)) (hij : i ≠ j) : (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, j, true)⟩ : ℝ) = (1 / 2) ^ 2 * (Sizes.seqGvar sz0 ⟨0, (i, j, true)⟩ : ℝ) + 4 * ((1 / 3) ^ 2 * (1 / 2)) := by simp [olVar, gueUnitVar, hij]
example (i : Idx 3 (sz0.L 0) (sz0.W 0)) : 0 < (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, i, true)⟩ : ℝ) := by have : (olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, (i, i, true)⟩ : ℝ) = (1 / 2) ^ 2 * (Sizes.seqGvar sz0 ⟨0, (i, i, true)⟩ : ℝ) + 4 * ((1 / 3) ^ 2 * 1) := by simp [olVar, gueUnitVar] rw [this] have h0 : (0 : ℝ) ≤ (Sizes.seqGvar sz0 ⟨0, (i, i, true)⟩ : ℝ) := NNReal.coe_nonneg _ nlinarith
example : (Pgue sz0).map (olComb sz0 (1 / 2) (1 / 3) 4) = Measure.infinitePi (fun c : Sizes.SeqCoord sz0 => gaussianReal 0 (olVar sz0 (1 / 2) (1 / 3) 4 c)) := ol_map_comb sz0 _ _ _
example : (Pgue sz0).map (fun ω => Sizes.slice sz0 0 (olComb sz0 (1 / 2) (1 / 3) 4 ω)) = GaussianProduct.law (fun c : CoordF 3 (sz0.L 0) (sz0.W 0) => olVar sz0 (1 / 2) (1 / 3) 4 ⟨0, c⟩) := ol_map_comb_slice sz0 _ _ _ 0
example (ω : PathΩ sz0) : gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K 0 4 ω = Xmat 3 (sz0.L 0) (sz0.W 0) (Sizes.slice sz0 0 (olComb sz0 (Real.sqrt (OneLoopInst_t1 0)) (Real.sqrt (gridStep OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K 0 / ((sz0.size 0 : ℕ) : ℝ))) 4 ω)) := ol_gueH_eq sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K 0 4 ω
example (n k : ℕ) (ω : PathΩ sz0) : gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n k ω = Xmat 3 (sz0.L n) (sz0.W n) (Sizes.slice sz0 n (olComb sz0 (Real.sqrt (OneLoopInst_t1 n)) (Real.sqrt (gridStep OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n / ((sz0.size n : ℕ) : ℝ))) k ω)) := ol_gueH_eq sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n k ω
private theorem OneLoopInst_main (h1 : StochDomAt (Pgue sz0) sz0.size (fun n (p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n)) ω => ‖loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n) (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω)) (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1)) ⟨[true], [p.2]⟩ - mE (OneLoopInst_E n)‖) (fun n p _ => (gueScale sz0 OneLoopInst_E n (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹)) : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n), ‖(∫ ω, loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n) (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω)) (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue sz0)) - mE (OneLoopInst_E n)‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ ε * (gueScale sz0 OneLoopInst_E n (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹ ^ 2 := gueGrid_expect_oneLoop sz0 (by norm_num) (Λ := 10) (κ := 1 / 2) (by norm_num) (E := OneLoopInst_E) (t1 := OneLoopInst_t1) (t0 := OneLoopInst_t0) (K := OneLoopInst_K) (tendsto_natCast_atTop_iff.mp sz0_tendsto) OneLoopInst_lam_window (fun _ => by norm_num [OneLoopInst_E]) OneLoopInst_t1_nonneg OneLoopInst_t1_le_t0 (fun _ => by norm_num [OneLoopInst_t0]) (fun _ => by norm_num [OneLoopInst_K]) h1
example (h1 : StochDomAt (Pgue sz0) sz0.size (fun n (p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n)) ω => ‖loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n) (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω)) (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1)) ⟨[true], [p.2]⟩ - mE (OneLoopInst_E n)‖) (fun n p _ => (gueScale sz0 OneLoopInst_E n (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹)) : ∃ n : ℕ, ∀ p : Fin (OneLoopInst_K n + 1) × Zd 3 (sz0.L n), ‖(∫ ω, loopL 3 (sz0.L n) (sz0.W n) (blockMat 3 (sz0.L n) (sz0.W n) (gueH sz0 OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1 ω)) (zt (OneLoopInst_E n) (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue sz0)) - mE (OneLoopInst_E n)‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * (gueScale sz0 OneLoopInst_E n (gridTime OneLoopInst_t1 OneLoopInst_t0 OneLoopInst_K n p.1))⁻¹ ^ 2 := (OneLoopInst_main h1 (1 / 2) (by norm_num)).exists
```
### b.5 Name-clash, scope, port source
```
$ grep -rnE "\b(olComb|olComb_measurable|olVar|ol_map_comb|ol_map_comb_slice|ol_gueH_eq|gueGrid_expect_oneLoop|OneLoopInst)\b" RBM3D --include=*.lean | grep -v "^RBM3D/Probe/" | grep -v "^RBM3D/Universality/GUEPhase/OneLoop.lean" | cut -c1-140
RBM3D/Universality/GUEPhase/Eq729A.lean:730:(`gueGrid_expect_oneLoop`, the `lk` field of `GUEPathBounds`) (`Eq729A:692`). -/
RBM3D/Universality/GUEPhase/Eq729A.lean:1281:`hg1`-`hg3` (second half: `gueGrid_expect_oneLoop`, the `lk` field of `GUEPathBounds`) stay
$ same pattern restricted to declarations: grep -rnE "^\s*(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure) (RBM\.[A-Za-z.]*\.)?(olComb|olComb_measurable|olVar|ol_map_comb|ol_map_comb_slice|ol_gueH_eq|gueGrid_expect_oneLoop)\b" RBM3D --include=*.lean | grep -v "^RBM3D/Probe/" | grep -v "^RBM3D/Universality/GUEPhase/OneLoop.lean" | wc -l   ->  0   (the hits above are docstrings of the consumer Eq729A)
$ git diff --stat main...t/T2353
 RBM3D/Universality/GUEPhase/OneLoop.lean | 1528 ++++++++++++++++++++++++++++++
 1 file changed, 1528 insertions(+)
$ git log --format="%h %s" main..t/T2353 | cat
c924852 T2353: OneLoop docstrings: paper citation (lem:improve_exp_aver), drop unverified equation numbers
2cf106a T2353: OneLoop header line wrap
697816c T2353: OneLoop header (statement change note), private instance helpers, lint fixes
d1ee7b2 T2353: OneLoop sections 7-9 (core, one-time bound, gueGrid_expect_oneLoop)
d772b96 T2353: OneLoop sections 1-6 (one-time law, contraction, Stein step, self-consistent equation, stability)
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   ->  9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/OneLoop.lean   ->  (empty: source unchanged since the port commit; 1729 lines)
```
### b.6 Port: translation table (source `RBM2D/Universality/GUEPhase/OneLoop.lean` 391-1726 -> this file 87-1367; no RBM1D source)
Token map applied to the source text by `declmap.py` (regexes): `d.L n -> sz.L n`, `Z2 L -> Zd d L`, `Coord L W -> CoordF d L W`, `gloop L W -> loopL d L W`, `spectralZ/M -> zt/mE`, `green X z -> Gres X z true`, `SB L -> SB d L g`, `gvar L W c -> gvarF d L W g c`, `blockRelabel/idxKey/split/trace_coordinate_* L W -> .. d L W`, `(L:R)^2, (W:R)^2, ((L*W)^2:N) -> ^d`, `OneLoop_{Pgue_eq_mixed,map_combined_eq_mixed,map_slice_infinitePi,seqXmat_*,real_smul_matrix} -> GUEPhaseGrid_*`, `KLoop.gapK -> Loop.gapK`; comments stripped; then a token-level `difflib` edit count.
```
$ python3 -I declmap.py   # 45 source declarations (docstrings stripped): 19 identical modulo map, 22 edited, 4 absent under this name; rows with edit tokens > 0 and the absent ones:
source decl                            src line this file edit tokens
ol_map_comb_slice                           417       115           3
ol_gueH_eq                                  426       125           1
OneLoop_sum_gue_fine                        521       217          11
OneLoop_trace_blockRelabel                  558       255           4
OneLoop_blockRelabel_mul                    563       260           2
OneLoop_sub_mul_green                       605       302          12
OneLoop_gloop_one                           611       308           6
OneLoop_trace_HGE                           618       314           1
OneLoop_green_norm_le                       661       357           1
OneLoop_stein_coord                         706       405           2
OneLoop_HflowBlock_eq                       738       437           3
OneLoop_contraction                         759       484          25
OneLoop_stein                               888       621           3
OneLoop_SB_symm                             951       684           3
OneLoop_sum_SB_col                          954       688           4
OneLoop_selfcons                            961       700          24
OneLoop_gapK_le_norm                       1084       818         228
OneLoop_stable                             1172       857         244
OneLoop_expect_core                        1275       953          65
OneLoop_blockMat_Xmat                      1431      1116           5
OneLoop_expect_bound                       1441      1125          82
gueGrid_expect_oneLoop                     1642      1308         443
OneLoop_norm_one_sub_sq                    1066         -           -
OneLoop_theta_solve                        1114         -           -
OneLoop_theta_row_sum                      1135         -           -
OneLoop_log_absorb                         1607         -           -
identical modulo map (19): olComb olComb_measurable olVar ol_map_comb OneLoop_sum_orderedPairs_from_upper OneLoop_trace_coordinateBlock_pair OneLoop_sum_gue_block OneLoop_norm_trace_mul3_le OneLoop_integrable_coord_smul OneLoop_integrable_of_cont_bdd OneLoop_g_cont OneLoop_g'_cont OneLoop_g_bdd OneLoop_g'_bdd OneLoop_gloop_bdd OneLoop_gloop_cont OneLoop_integrable_gloop OneLoop_integrable_gloop_mul OneLoop_gapK_pos
new private declarations (not in the source): OneLoop_Eblk_mul_Eblk:453  OneLoop_sum_Eblk:469  OneLoop_card_Zd:694  OneLoop_svar_cast:826  OneLoop_stable_SB:834
$ python3 -I tokcount.py   # occurrences in the source body vs this file body (comments included)
RBM2D token (source body)            n  RBM3D token (this file body)       n
d.L n                               56  sz.L n                            51
d.W n                               34  sz.W n                            39
d.size n                             9  sz.size n                         10
Z2 L | Z2 (d.L n)                  101  Zd d L | Zd d (sz.L n)            89
Coord L W | Coord (d.L n)           38  CoordF d (L | (sz.L n))           38
Ω L W | Ω (d.L n)                   51  Ω d (L | (sz.L n))                51
BlockIndex                          18  Vtx d                             20
gloop (fn)                          35  loopL d                           34
spectralZ (fn)                      25  zt                                25
spectralM (fn)                      35  mE                                28
green (fn)                          31  Gres .. true                      32
HflowBlock L W                      65  HflowBlock d ..                   65
Eblk L W                            54  Eblk d L W                        59
gvar L W c                           6  gvarF d L W g                      8
SB L                                37  SB d L g                          35
Theta L                              9  Theta d L g                        0
^ 2 on L, W, (L*W)                  42  ^ d on L, W, (L*W)                58
(sz/d).L n ^ 2                       8  (sz.L n : ℝ) ^ d                   7
cShortRow                           21  Kstab3                            13
cProp5 | xiRowBoundShort | xiMat     9  (none)                             3
Real.log (the log L)                24  Real.log                           0
$ python3 -I residual.py   # d = 2 tokens in this file outside comments
d=2 tokens outside comments in this file (code only): {'Z2': 0, 'd.L n': 0, 'd.W n': 0, 'd.size': 0, 'gloop': 0, 'spectralZ(?![_A-Za-z0-9])': 0, 'spectralM(?![_A-Za-z0-9])': 0, 'cShortRow': 0, 'cProp5': 0, 'xiMat': 0, 'xiRowBoundShort': 0, 'Theta L': 0, 'BlockIndex': 0, 'Real.log': 0, 'KLoop': 0, '^ 2 : ℕ': 0, '(L : ℝ) ^ 2': 0, '(W : ℝ) ^ 2': 0}
lines of code (comments stripped, blank removed): 1232
$ python3 -I sq.py   # bases of the remaining `^ 2` in code
87 occurrences of "^ 2" in code; base token: count -> Λu: 20, m: 17, (ρ * Λu): 13, Env: 6, E: 5, ⁻¹: 5, ρ: 3, (1 / 2): 3, (1 / 3): 3, bb: 2, N: 2, (2 * N ^ 2 * Λu): 2, a: 1, b: 1, aa: 1
```
Hand edits (the whole list; spans = `declmap.py spans`; the remaining spans of the rows above are the explicit `d` / `g` arguments of the port map, and the unapplied `blockRelabel` in one `simp only` list):
- H1 `ol_map_comb_slice` 3, `ol_gueH_eq` 1: `d -> sz` as explicit sizes argument; the `OneLoop_*` carrier copies (source 70-389) are the public `GUEPhaseGrid_*` of `Grid.lean:128-145, 428-484`.
- H2 `OneLoop_sub_mul_green` 12: `Matrix.mul_nonsing_inv` -> `simp only [Gres, ↓reduceIte]; exact Ring.mul_inverse_cancel _ (isUnit_sub_smul_of_isHermitian ..)` (`Gres` is `Ring.inverse`).  `OneLoop_gloop_one` 6: `simp [loopL]` for `gloop, gloopProd_cons/nil, Gsig_true`.  `OneLoop_trace_HGE` 1: `trace_Eblk` (`GLoopFlow.lean:231`) for `trace_Eblk_eq_one`.  `OneLoop_green_norm_le` 1: `norm_Gsig_le_inv_eta .. true`.  `OneLoop_HflowBlock_eq` 3: simp set gains `blockMat`, `Matrix.submatrix_apply`.
- H3 `OneLoop_contraction` 25: `g`; `Eblk_mul_Eblk`, `sum_Eblk` -> new private `OneLoop_Eblk_mul_Eblk`, `OneLoop_sum_Eblk` (twins `Gauss/LoopGenerator.lean:462`, `Hierarchy/ContractionBasic.lean:755`, both private); `inv_pow` and `hWd : (W:C)^d != 0` before `field_simp` (symbolic exponent).  `OneLoop_selfcons` 24: `g`; local `g -> g'` (pre-rename); `card (Zd d L) = L^d` by new `OneLoop_card_Zd`.
- H4 `OneLoop_gapK_le_norm` 228: 3-line proof from the public `Loop.gapK_le_norm` (`KLSumZero.lean:456`, `mSigma E true = mE E`); the source `OneLoop_norm_one_sub_sq` (1066-1076) and the 25-line proof of `OneLoop_gapK_le_norm` (1084-1108) are not needed; `OneLoop_gapK_pos` re-derived (`gapK_pos` is private there).
- H5 `OneLoop_stable` 244: hypothesis `hK : Green.Stable (svar d L W g) (t1 m^2) K`, conclusion `K (1 + 1/gapK) B`, `t1 < 1` dropped; the zero-mode part (`hsum`, `hSle`, `hrle`) is the source's; source `OneLoop_theta_solve` (1112-1131) and `OneLoop_theta_row_sum` (1133-1166) are replaced by new `OneLoop_stable_SB` (lifts `Stable (svar ..)` to functions of the block label).
- H6 `OneLoop_expect_core` 65, `OneLoop_expect_bound` 82: `hd : 3 <= d`, `hg : 0 < g`, `hgΛ : g <= Λ`; `hK := Green.stable_svar_bulk_vtx ..` (`Green/Stability.lean:320`); constant `Green.Kstab3 d Λ κ (1 + 1/gapK κ)`; scale `Λ -> Λu` (pre-rename); `Sizes.size_eq` -> `unfold Sizes.size` / `sz.one_le_size n`; `pow_pos`, `mul_pow`, `pow_nonneg` for the `W^d`, `L^d` positivity; `nlinarith` -> `one_le_mul_of_one_le_of_one_le` (the `nlinarith` timed out at 200000 heartbeats with the symbolic exponent).
- H7 `gueGrid_expect_oneLoop` 443: statement change (b.3; T2353a, T2353b); proof: `OneLoop_log_absorb` (1606-1632), `hcs`, `hlogL`, `hRlN`, `hLN`, `hL2N` dropped; `habs : 8K' + 1 <= N^(ε/2)` eventually by `tendsto_rpow_atTop`, `K' = Kstab3 d Λ κ (1 + 1/gapK κ)`; `hXC : K'(X+4) <= X X` from `X >= 8K'+1`.

### b.7 Numbers and narrative
```
$ python3 -c "K=4.629e22; g=0.935414; print('Kstab3*(1+1/gapK) =', '%.4g' % ((1+K)*(1+1/g)), '; K_Theta*(1+1/gapK) =', '%.4g' % (K*(1+1/g)))"   # K_Theta, gapK as in (a)(ii)
Kstab3*(1+1/gapK) = 9.578e+22 ; K_Theta*(1+1/gapK) = 9.578e+22
```
- Port of RBM2D `OneLoop.lean` (9e0f275, 1729 lines): 1528 lines, 5 commits; the ticket's pre-named cut at `:430` (2100 central) was not needed.  2 defs and 5 theorems are public; each is the source statement under the map (b.3), except `gueGrid_expect_oneLoop` (T2353a, T2353b).  Every unpinned helper is `private` with the prefix `OneLoop_`/`OneLoopInst_`.
- The `d ≥ 3` form of the `log L` tokens (ticket Preflight): the 24 `Real.log` tokens and the `cShortRow`/`cProp5`/`xiRowBoundShort`/`xiMat`/`Theta L` lines of the source body are gone (b.6 residual line: 0 outside comments).  The `d = 2` row sum `1 + cShortRow κ (1 + log L)` is replaced by the merged `d ≥ 3` stability `Green.stable_svar_bulk_vtx`: `Stable (svar d L W g) (t m²) (Kstab3 d Λ κ)` for `0 < g ≤ Λ`, `Kstab3 = 1 + C_s(1 + Λ² expC(d-2, c_s))` from the proved pin 5s (`prop5Short_holds`, `Propagator/Prop5Short.lean:400`) and `sum_radial_exp_decay_le`: no `L`, no `log L`.  This is the alternative named in (a)(i) (public `stable_svar_bulk_vtx`, not a re-derived row sum).
- Constant: Lean has `Kstab3 (1 + 1/gapK κ)` with `Kstab3 = 1 + K_Θ`; (a)(i) writes `K_Θ (1 + 1/gapK)`; the two agree at the instance data to the printed digits (b.7 script), and only `N^(ε/2) >= 8K'+1` eventually is used.  (a) contains no statement that needed correction, so there is no (a′).
- `d`-lines: `W^d`, `L^d`, `(L W)^d` enter through `card (Zd d L) = L^d`, the block normalisation `(W⁻¹)^d` of `Eblk`, `tr G = W^d Σ_p tr(G E_p)`, `‖loopL‖ <= (L W)^d (η⁻¹ (W^d)⁻¹)` (`norm_gloop_le_crude`) and `L^d <= N = (W L)^d`.  The 87 remaining `^ 2` in code (b.6, `sq.py`; base `E` is `mE E ^ 2`, base `⁻¹` is `(N η)⁻¹ ^ 2`) have no base `L`, `W` or `L W`.
- Instances: `olComb`, `olVar`, `olComb_measurable`, `ol_map_comb`, `ol_map_comb_slice`, `ol_gueH_eq` at `sz0` (b.4: 10 `example`s); `gueGrid_expect_oneLoop` through the private `OneLoopInst_main` and an `example` concluding `∃ n` (from `Filter.Eventually.exists`, since the proof constants only bite for large `n`).  Deterministic hypotheses: `hd` (3 ≤ 3), `hκ`, `hsize` (from `sz0_tendsto`), `hlam` (`OneLoopInst_lam_window`: `lam n = (2(n+1))^{-6} ∈ (0, 1] ⊂ (0, 10]`), `hE`, `ht1`, `ht10`, `ht0`, `hK`.
- Registry: the module defines and assumes no `Prop` predicate other than the merged `StochDomAt` (in `h1`); b.1 pre-check exit 0, ledgers unchanged.

## (c) Verified Mathlib names (script: `names.lean`, 72 `#check @` lines, 0 errors, then `absent.lean`)
`Ring.mul_inverse_cancel`, `Matrix.trace_mul_comm`, `Matrix.submatrix_mul_equiv`, `Matrix.trace_smul`, `Matrix.trace_sum`, `Matrix.trace_add`, `Matrix.sum_apply`, `Matrix.diagonal_mul_diagonal`, `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Fintype.card_fin`, `Finset.sum_comm`, `Finset.sum_mul_sum`, `Finset.sum_ite_eq`, `Finset.card_univ`, `nsmul_eq_mul`, `integral_finsetSum`, `integral_const_mul`, `integral_add`, `integral_sub`, `integral_const`, `integral_map`, `integral_mono`, `integral_indicator_const`, `norm_integral_le_integral_norm`, `integrable_map_measure`, `MeasureTheory.Integrable.of_bound`, `MeasureTheory.Integrable.bdd_mul`, `MeasureTheory.Integrable.ofReal`, `MeasureTheory.Measure.infinitePi_map_eval`, `MeasureTheory.measureReal_def`, `MeasureTheory.measure_toMeasurable`, `MeasureTheory.subset_toMeasurable`, `MeasureTheory.measurableSet_toMeasurable`, `MeasureTheory.probReal_univ`, `ENNReal.toReal_le_of_le_ofReal`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_nonneg`, `Real.sq_sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_pos`, `tendsto_rpow_atTop`, `tendsto_natCast_atTop_iff`, `Filter.eventually_ge_atTop`, `Filter.Eventually.exists`, `one_le_pow₀`, `le_inv_comm₀`, `inv_le_one_of_one_le₀`, `one_le_mul_of_one_le_of_one_le`, `div_le_iff₀`, `le_div_iff₀`, `Complex.abs_im_le_norm`, `Complex.norm_real`, `Complex.real_smul`, `hasDerivAt_const`, `HasDerivAt.mul`, `HasDerivAt.mul_const`, `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.congr_deriv`, `LinearMap.toContinuousLinearMap`, `Matrix.traceLinearMap`, `NNReal.coe_sum`, `coe_nnnorm`, `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `inv_pow`, `pow_pos`, `pow_nonneg`, `mul_pow`.
Verified absent (`unknownIdentifier`/`unknownConstant`, `absent.lean`): `cShortRow`, `cProp5`, `RBM.Evol.xiRowBoundShort`, `RBM.Evol.xiMat`, `RBM.Gauss.norm_green_le`, `RBM.Gauss.Gsig_true`, `RBM.Gauss.Sizes.size_eq`, `RBM.Univ.GUEPhase.OneLoop_log_absorb`, `RBM.KLoop.gapK`, `RBM.Gauss.Eblk_mul_Eblk` and `RBM.Gauss.sum_Eblk` (both private in RBM3D: re-derived).

## (d) Open issues and paper-delta candidates
- `T2353a` (hypotheses): `gueGrid_expect_oneLoop` has two hypotheses the `d = 2` source does not: `3 ≤ d` and `∀ᶠ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ`.  Reason: the `d ≥ 3` stability constant `Kstab3 d Λ κ` is uniform in `L` only for the coupling window `0 < g ≤ Λ` of the proved pin 5s; `(eq:WO)` (`Sizes.WO 𝔡`, part of `Sizes.Admissible`) gives it with `Λ = 𝔡⁻¹` eventually.  Both hold at the instance (b.4).
- `T2353b` (constant): `1 + cShortRow κ (1 + log L)` (the `d = 2` row sum of `Θ_{t m²}`, a `log L` lattice sum) ↦ `Kstab3 d Λ κ`, independent of `n` and `L` (`lem_propTH` property 5 `(prop:ThfadC_short)`, `1_2:1148`); the conclusion `N^ε (N η_u)^{-2}` is unchanged.
- `T2353c` (statement form): the paper states the band-flow lemma `lem:improve_exp_aver` (`paper/tex/6_Step6_two_loop.tex:12-21`: `max_a |𝔼 tr((G_u - M) E_a)| ≺ (W^{-d} B_{u,0})²`, "the proof is the same as that of [YY_25, Lemma 5.15]") and for the GUE phase of Thm 2.4 only "essentially identical" to [YY_25, Thm 2.6] and [DYYY25, Thm 2.6] (`1_2_Intro_model_result.tex:566-570`); the Lean target is the GUE-phase-grid form (pathwise `(N η_u)^{-1}` ⇒ `N^ε (N η_u)^{-2}`) of RBM2D `OneLoop.lean`, as the ticket prescribes.
- Consumer UN-47 (`Eq729A.lean:730` names `gueGrid_expect_oneLoop` as the second half of its stochastic inputs) must supply `hd`, `hlam` (`Sizes.Admissible` contains `WO 𝔡`, which gives `0 < lam ≤ 𝔡⁻¹` eventually) and `h1`; `h1` is stated for `loopL .. ⟨[true], [p.2]⟩ - mE (E n)` as in the source.
- DECISIONS §29 (pin boundary, one line each; (a)(iv)): (1) time domain `0 ≤ t₁ ≤ t₀ < 1`, `K n ≠ 0`, `k ≤ K n` explicit, `u < 1` derived; (2) the `ilambda²/L²` boundary is not used (only `0 < g ≤ Λ`); (3) no `L`-`W` relation, only `L^d ≤ N`, `3 ≤ L`, `0 < W`; (4) `hlam` and the conclusion are `∀ᶠ n`, `hE ht1 ht10 ht0 hK` are `∀ n` as in the source; (5) the union over times is inside `h1` (`StochDomAt`) as in the source; (6) `0 < lam ≤ Λ` and `N → ∞` are hypotheses, `W^{-d/2+𝔡} ≤ lam` is not needed; (7) scale `N^ε (N η)^{-2}`, no `log W`, no `W^τ`.
- Observation (not a defect): `ht1 : t1 < 1` is not a hypothesis of the private `OneLoop_stable` (it was needed in the source only for the `Θ`-solve); the target statements are unaffected.
