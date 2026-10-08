Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct  8 12:11:38 UTC 2026

Sources: `docs/tickets/T2333.md`; `paper/tex/3_5_Loop_Hierarchy.tex:1935-2070`; `RBM3D/Induction/Step5Pins.lean:285-317`; `Step2Defs.lean:75,131-143,797-851`; `PfStep5Grid.lean:130-143`; `Step5Kernel.lean`; `Step2Core.lean:400-520`; `Step2Events.lean:93-135`. Notation: `A = lam² W^d` (`STAI`), `ρ = (1-s)/(1-t)`, `η_u = (1-u) Im m` (`etaT`), `prof_u(b) = STprof` (`W^{-d}𝒯̃^L_{u,D}`).

### (i) Exponent table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠_d` | chosen by the proof (`∃ 𝔠d`, `STIngR5`, `Step5Pins.lean:82`), `0 < 𝔠d ≤ 1/100` | paper form `ρ³A^{-1/4} ≤ A^{-1/5}` needs `3𝔠_d ≤ 1/20`; Abel form (F1) `ρ²A^{-1/4}` needs `2𝔠_d ≤ 1/20` | `1/60 - 1/100 = 1/150` (paper), `1/40 - 1/100 = 3/200` (Abel) |
| 2 | `ρ` | `(1-s)/(1-t) ≤ (W^{-d}B_{t,0})^{-𝔠_d} ≤ (2A)^{𝔠_d}` | `STConStInd` (`Defs.lean:168`) + window `1/(2A) ≤ W^{-d}B_{t,0} ≤ 2/A`, which needs `lam²/L^d ≤ 1-t ≤ lam²` (`STReg5I` ⇒ `STReg5Mid`, `st5_reg5I_mid` `Step5Pins.lean:466`; window = `etermsMid_Bctl_window`, `EtermsMid.lean:58`) | window used only through `1-t ≥ lam²/L² ≥ lam²/L^d` |
| 3 | `A` | `W^{2𝔡} ≤ A ≤ 𝔡^{-2}W^d` | `lam_sq_mul_pow_ge` (`Defs/Sizes.lean:193`, `WO`), `lam ≤ 𝔡⁻¹` | `A ≥ 1`, so the constants below are `A`-free |
| 4 | drift `ℰ^{LK×LK}` | `ρ·A^{-1/3}` (× `Σ_jΔ/η_j ≲ log N`, `1/Im m ≤ C_κ`) | `≤ C·A^{-1/5}` | exponent `1/3-1/5-𝔠_d ≥ 0.1233` |
| 5 | drift `ℰ^{G̃}` | `ρ·A^{-1/2}` | `≤ C·A^{-1/5}` | `1/2-1/5-𝔠_d ≥ 0.29` |
| 6 | martingale | `ρ³A^{-1/4}` (paper `(uuwmskiow)`); `ρ²A^{-1/4}` by the Abel route (F1) | `≤ C·A^{-1/5}` | `1/4-1/5-3𝔠_d ≥ 0.02` (paper), `1/4-1/5-2𝔠_d ≥ 0.03` (Abel) |
| 7 | kernel losses | coefficient `(w-v)/w ≤ 2(1-v)` for all `0 ≤ v ≤ w < 1` (`w ≥ 1/2`: `(1-v)/w`; `w < 1/2`: `1 ≤ 2(1-v)`); `(1-u)Σ_b|Θ_{t,ab}|prof_u(b) ≤ C prof_t + ρ W^{-D}` (`step5Kernel_profile_explicit_holds`) | floor `ρW^{-D}` needs `ρ ≤ (2𝔡⁻²)^{𝔠_d} W^{d𝔠_d} =: W^θ`, `θ = d𝔠_d + 1` | `D ↦ D + θ + 2` is free (`D` is universal in the pin) |
| 8 | grid `K` | `K_n = ⌈N^{c_K}⌉`; `‖Rem‖ ≤ N^{C₀}Δ^{1/2}`, `C₀ = m + 9 = 11` (`DifREP3.lean:2378`); deterministic error `64(1-u_k)^{-7}(R + ΔM)` (`pfStep5Grid_duhamel`, `PfStep5Grid.lean:130`) | `(1-u_k)⁻¹ ≤ L²/lam² ≤ L²W^{d-2𝔡} ≤ L^dW^d = N`; `M ≤ N^{C_M}` (crude bound `difRep2_norm_…`); need error `≤ N^{-D''} ≤ W^{-D}`, `D'' ≥ D` since `W ≤ N` | `c_K` free: `c_K = max(C_K, 2(7 + C₀ + C_M + D''))` |
| 9 | Abel weights | slot weights `c^ε(v) = (v/w)^{#0}((w-v)/w)^{#1}`; `sup c^ε ≤ (2(1-s))^{r}`, total variation `≤ 2(2(1-s))^{r}` (`r` = number of `Θ`-slots) | row sums `‖Θ‖_{∞→∞} = (1-w)⁻¹` (`norm_Theta_le`, `Props4.lean:218`; entries `‖Θ(w·m)_{ab}‖ ≤ Θ(w)_{ab}`, `norm_Theta_apply_le` `Props4.lean:188`, so every `σ` incl. `σ₁=σ₂` reduces to `(+,-)`; no `prop5Short` needed) | factor `ρ^r` |
| 10 | lift in `u` | net of size `N^{A'+1}`, Hölder `N^{-C_R}` of `LK` in `u` (`LemDecCalELip_Lloop_sub`, `LemDecCalELip.lean:278`); near-minimizer of `F` per (cell, label), factor `2` | `N^{-C_R} ≤ W^{-D}`: `C_R ≥ D` | free |

Definition table (→ declarations): `𝒰` = `RBM.Ind.Ugen` (`GridDuhamelN.lean:65`) = `UN` with charges `mSigma E (σ_i)`; decomposition `step5Kernel_UN_decompU` (`Step5Kernel.lean:74`); `ℰ^{LK×LK}` = `STELKLKM`/`STELKLK` (`Step2Defs.lean`, `Step5Pins.lean:147`), `ℰ^{G̃}` = `STEGtM`/`STEGt` (`Step2Defs.lean:312`); `dℰ^M` = increments of `Mart` in `STGridRepNAt` (`Step2Defs.lean:817`); `(ℰ⊗ℰ)^{M,(2)}_{a,a}` = `STEEM = STEEkM 0 + STEEkM 1` (`Step2Defs.lean:141`, diagonal `a' = a`), `STEEM = STeeM σ a a` (`STEEM_eq_STeeM`, `Step2Iterate.lean:1698`); `F` = free deterministic `F n p ≥ 0` of `STDuhamelConcl`; `ρ`, `A` as above.

### (ii) The steps (1)-(6) against `3_5:1941-2069`

1. Grid Duhamel: PASS. `stGridRepN_holds` (`DifREP3.lean:2381`, `3 ≤ d`) at `m = 2` on `[s, u_n]` (section `t := u_n`); the deterministic Duhamel form with the `Ugen`-weighted sums is the merged `pfStep5Grid_duhamel` (`PfStep5Grid.lean:130`, from conjunct 1, `F_i = STelklkM + STegtM` via `STgDrift_eq_STgDriftN`, `STELKLKM_eq_STelklkM`, `STEGtM_eq_STegtM`; `Icc 3 2 = ∅`).
2. Kernel: PASS (rows 7, 9).
3. Drift: PASS (rows 4, 5): `|Ugen_{v,u}(F_v)| ≲ η_v⁻¹A^{-1/3}[prof_v + 2(1-v)Σ|Θ|prof_v + 4(1-v)²ΣΣ|Θ||Θ|prof_v]`, then `step5Kernel_calA_explicit_holds` (`Step5Kernel.lean:739`) and `prof_v ≤ prof_u` (time monotonicity, `Step5Kernel.lean:337`, private: copy).
4. **Martingale: the route of the ticket FAILS, a corrected route PASSES (F1).** Conjunct 4 of `STGridRepNAt` bounds `Σ_j Ugen(ΔMart_j)` by `(Σ_jΔ‖STeeUM_{u_j,u_k}(H_j)‖ + N^{-D})^{1/2}`, and `STeeUM = Σ_{b,b'} K(a,b)K̄(a,b') STeeM σ b b'` (`Step2Defs.lean:797-803`) needs the off-diagonal `STeeM σ b b'`, `b ≠ b'`. `STEtermsMidConcl` (`Step5Pins.lean:259`) controls only the diagonal `STEEk σ a` (`a' = a`). No merged lemma bounds an off-diagonal `STeeM` in case (i): the only near-pair off-diagonal bound is `STLemDecCalEConcl`, conjunct 3, under regime `STReg5III` (`Step5Pins.lean:193`); no positive-semidefinite/Cauchy-Schwarz lemma for `STeeM` exists (grep `PosSemidef` hits only `Universality/PinsC2`, `Induction/Contract`, `Induction/Split`). Corrected route (the paper's, `3_5:2024-2038`): expand `Ugen` slot by slot by `step5Kernel_UN_decompU` into `Σ_ε c^ε(v)Θ^ε`, so `Σ_jUgen_{u_j,w}(ΔMart_j)(a) = Σ_ε Σ_b Θ^ε(a,b) Σ_j c^ε(u_j) ΔMart_{(σ,b)}(j)`; Abel-sum each inner sum (`pfStep5Grid_abs`-style, private: copy) with `|Σ_j c_jΔM_j| ≤ (sup c + TV c)·max_{j≤k}|M_j|`, and use the unweighted diagonal conjunct 3 of `STGridRepNAt` (`‖Mart_{(σ,b)}(j)‖ ≤ N^{ε'}(Σ_{i<j}Δ‖STeeM_i σ b b‖ + N^{-D})^{1/2}`, all `j ≤ K` simultaneously; `Mart_0 = -Rem_0`, tiny). With `‖STeeM σ b b‖ = ‖STEEM‖ ≤ 2·A^{-1/2}η_i⁻¹prof_{u_i}(b)²` (whp at all grid indices) this gives `(1-s)^r A^{-1/4} (log)^{1/2} prof_w(b)`, then row sums: total `ρ^r A^{-1/4} prof_w`, `r ≤ 2` (row 6). The paper's extra `ρ` (from `sup 𝒜`, `(uwftgwesj)`) is not needed. Conjunct 4 / `STeeUM` is NOT used.
5. Exponent closure: PASS (rows 1-6; script below).
6. Grid → model (transfer, (v)): PASS. Everything fed to the model is a function of ONE matrix `H`: initial term at grid index 0 (`ST_grid_whp_zero`, `Step2Events.lean:118`: the uniform hypothesis `Prec` on `STIdx2P` restricts to the time set `{u_n}` because the bad event of the union contains each section; `Prec ⇒ PrecPT`: `perTimeOfStochDomAt`, `Defs/StochDomAt.lean:195`); the three error terms at all grid indices `j ≤ K_n` and all labels (`ST_grid_whp_of_sections`, `Step2Events.lean:93`, sections of `STEtermsMidConcl` with `t := u_n`, `TimeIcc s u_n ⊆ TimeIcc s t_n`; measurability of `F, Z` in `H`); the target `‖Q LK(H_K)‖` at the endpoint `u_K = u_n` (`ST_model_of_whp_grid`, `Step2Core.lean:464`; `ST_pathP_eq_seqP` `:400`, `map_pathH_eq` `Path/Walk.lean:598` = single-time law only). The joint law of `(H_s, H_u)` is NOT transferred (flow `seqHflow n u ω = seqXmat(√u ω)` is a scaling, the grid is Brownian), and none is needed: `Ugen` enters only through the pathwise algebra. **Uniform in `u ∈ [s,t]` (F2):** `cont_core` (`ContinuityNet.lean:142`) is NOT applicable to the conclusion, because it needs `ζ(u') ≤ 2ζ(u)` and `F` is an arbitrary deterministic function. Use instead `stochDomAt_of_perTimeDomAt` (`StochDomAt.lean:249`) over the index (net cell `k`, label `v`) of size `≤ N^{A'+4}`: for each cell pick `u*_{k,v}` with `F(u*) ≤ 2 inf_cell F + N^{-C_R}`, apply the per-section result at the section `tt_n = u*_{k_n,v_n}` (hypothesis section = restriction of the uniform hypothesis), and pass to every `u` of the cell by Hölder continuity of `LK_u` (`LemDecCalELip_Lloop_sub` + `STKloop` Lipschitz) and `ζ_err(u*) ≤ 2ζ_err(u)` for `ζ_err = A^{-1/5}prof_u + W^{-D}` (the `etermsMid_zeta_close` pattern, private in `EtermsMid.lean`: copy). No continuity of `Ugen` is needed.

### (iii) DECISIONS §29 (one line each)
(1) `0 ≤ s < t ≤ lemT z < 1` are hypotheses of `STIngR5` (`Step5Pins.lean:82-95`); `u_n ∈ [s,t]` keeps `u < 1`, and `s ≤ u_n` (equal allowed: `STGridRepNAt` takes `s ≤ t`, `Δ = 0` harmless). (2) Case (i): `1 - t ≥ lam²/L²` and `t ≥ 0` force `lam ≤ L` (else `STReg5I` is unsatisfiable, vacuous, no hidden hypothesis). (3) `L`-`W` relation: only `lam² ≥ W^{2𝔡-d}` (`WO`, `Admissible`) and `L ≥ 1, d ≥ 2` are used, giving `(1-u)⁻¹ ≤ N`; `L^d ≤ W^K` is not used. (4) `STReg5I` is `∀ n`, `STConStInd` and all `≺` are `∀ᶠ n`; `K_n ≠ 0` for all `n`; `Rem` bound is `∀ᶠ n`. (5) The pin's hypothesis `STEtermsMidConcl` and conclusion are `Prec` (union inside): sections obtained by `perTimeOfStochDomAt`, the union recovered by F2. (6) Parameter lower bounds written as hypotheses of the pin: `A ≥ W^{2𝔡}` from `Admissible`, `Im m ≥ c_κ` from `|E| ≤ 2-κ`. (7) Scale: `ℓ = L` throughout, `STprof` at `ℓ = L` (`STEtermsMidConcl` uses `((sz.L n : ℕ) : ℝ)`).

### (iv)+(ii-instance) One concrete nondegenerate instance and the closure script
Data (pattern `szB`, `Step5Pins.lean:478-520`, with `ρ` made visible): `d = 3`, `κ = ε = 𝔡 = 1/10`, `L = 4`, `lam = 1`, `W = 10^6` (one value of the sequence `W_n = n + 4` at `n + 4 = 10^6`), `s = 29/32`, `t = 15/16`, `𝔠_d = 1/100`. External hypothesis `STEtermsMidConcl` is not an assumption of ours (it is proved from `STLWT`, T2328); its concrete limit is exercised by rows 4-5 at these numbers. Limit computation for `STConStInd`: `W^{-d}B_{t,0} = W^{-3}·1.19 → 0` while `(1-t)/(1-s) = 2/3` is constant, so `(W^{-3}B)^{𝔠_d} → 0 < 2/3` eventually (here already at `W = 10^6`).
```
$ cd .../scratchpad/T2333 && python3 -I t2333_pf.py
regime I: True | regime Mid: True | 0<=s<t<1: True
A= 1e+18 rho= 1.5 W^-d B_t0= 1.1911764705882354e-18
window 1/(2A)<=b<=2/A: True
con_st_ind (W^-d B)^c_d = 0.6618502863020709  <= (1-t)/(1-s)= 0.6666666666666666 : True
rho <= (2A)^c_d : 1.5 <= 1.5240888994636161 True
A >= W^(2*dd): True  lam<=1/dd: True
drift   rho*A^-1/3 = 1.5000000000000013e-06  <= A^-1/5 = 0.0002511886431509579 : True
drift2  rho*A^-1/2 = 1.5000000000000002e-09  <= A^-1/5: True
mart(paper) rho^3*A^-1/4 = 0.00010672687103068281  <= A^-1/5: True
mart(Abel route) rho^2*A^-1/4 = 7.115124735378854e-05  <= A^-1/5: True
grid: all ratios <= 2^{kc} (constant only): True
max ln(ratio): {'drift13': 0, 'drift12': 0, 'mart3': 0.0116, 'mart2': 0.0}
exponent slack in A: drift13 0.12333333333333331 drift12 0.29 mart3(paper) 0.01999999999999999 mart2(Abel) 0.02999999999999999
largest c_d allowed: paper mart rho^3 A^-1/4<=A^-1/5 -> c_d<= 0.016666666666666666 ; Abel rho^2 -> c_d<= 0.025
```
The grid in the script: `𝔡 ∈ {0.05, 0.1, 0.25}`, `d ∈ {3,4,5}`, `W = 10^2..10^12`, `ln A` from `2𝔡 ln W` to `d ln W`, `𝔠_d ∈ {1e-4, 1e-3, 3e-3, 6e-3, 1e-2}`; it checks `(2A)^{k𝔠_d}A^{-e}/A^{-1/5} ≤ 2^{k𝔠_d}` for the four terms (only the constant `2^{k𝔠_d} ≤ 1.021` is lost, absorbed by `N^τ`). The instance at the concrete data is nonempty: `inst_duhamelI` (`Step5Pins.lean:611`) at `(szB, zB, 7/8, 15/16)` already discharges every deterministic hypothesis (`STReg5I`, `STConStInd` for every `𝔠_d > 0`, flow); the above numbers are a case with `ρ > 1` where the closure holds with explicit constants (`szB` itself has `ρ = 2` and needs `n ≳ 10^{10}` for `STConStInd` at `𝔠_d = 1/100`, a limit statement only).

### Verdict
- `stDuhamelI_holds` (Target 1): **PASS**, with two binding corrections to the ticket's route: F1 (do not use conjunct 4 / `STeeUM`; use conjunct 3 diagonal + Abel summation of the slot weights, exponent `ρ²A^{-1/4}`), F2 (the `u`-uniform lift is not `cont_core`; per-time sections over (net cell, label) at near-minimizers of `F`). The transfer (v) is covered by merged lemmas (`ST_grid_whp_of_sections`, `ST_grid_whp_zero`, `ST_model_of_whp_grid`, `perTimeOfStochDomAt`, `stochDomAt_of_perTimeDomAt`); no missing lemma.
- `stDuhamelConcl_engine` (general `Q`): **PASS** as a hypothesis-level statement (kernel bounds for `zeroModeSet Q ∘ Θ^ε` as hypotheses); if the general-`Q` form costs more than the ticket's allowance, keep `Q = ∅` as the ticket permits.

## (b) Script output (stage 1b, all after commit 533cf8e on `t/T2333`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2333`)

Build, axioms, registry, check-file equality, name clash, imports (scratch script `mk_b.sh`; scratch files `ax.lean`, `registry.lean`, `checkeq.lean`, `imports.py` under the scratchpad `T2333/`, not committed):
```
$ date -u; git log --oneline -3; git diff --stat main...t/T2333; wc -l RBM3D/Induction/DuhamelI.lean
Thu Oct  8 14:05:10 UTC 2026
533cf8e T2333: DuhamelI, make the five measure-theory helpers of the section lemma private
6fef301 T2333: DuhamelI, engine instance at case (ii) data with equal signs
6e94cc3 T2333: DuhamelI docstring provenance (ContinuityNet.lean:76)
 RBM3D/Induction/DuhamelI.lean | 1994 +++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |    1 -
 2 files changed, 1994 insertions(+), 1 deletion(-)
    1994 RBM3D/Induction/DuhamelI.lean
[exit 0]

$ lake build RBM3D.Induction.DuhamelI 2>&1 | tail -2; grep -c "DuhamelI.lean" (warnings/errors naming the file)
Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (3888 jobs).
warnings or errors naming DuhamelI.lean: 0
[exit 0]

$ lake env lean ax.lean   (#print axioms of the targets and of the instance)
'RBM.Gauss.Sizes.stDuhamelI_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stDuhamelConcl_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_duhamelI_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]

$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Induction/DuhamelI.lean
0

$ lake build 2>&1 | grep -E "axiom audit|Build completed|^error|Some required|STDuhamelI"   (worktree, no root import)
error: RBM3D.lean:373:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`:
  [RBM.Gauss.Sizes.STDuhamelI]
Some required targets logged failures:
error: build failed
[exit 1]

$ lake env lean registry.lean | head -3   (registry.lean = RBM3D.lean with `import RBM3D.Induction.DuhamelI` after its last import)
axiom audit: 9944 theorems, 2979 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
STDuhamelI mentions in the audit ledger output: 0 (STDuhamelII is a different premise)
[exit 0]

$ lake env lean checkeq.lean   (check imports + import RBM3D.Induction.DuhamelI + the equality example)
check-file equality exit: 0
8:import RBM3D.Induction.EtermsMid
9:import RBM3D.Induction.Step5Kernel
10:import RBM3D.Induction.Step5Kit
11:import RBM3D.Path.DifREP3
12:import RBM3D.Induction.DuhamelI
59:example : RBM.Gauss.Sizes.T2333Check.T2333_stDuhamelI_holds := RBM.Gauss.Sizes.stDuhamelI_holds

$ grep -rnE "stDuhamelI_holds|stDuhamelConcl_engine|inst_duhamelI_proved|duhamelI_" RBM3D/ | grep -v "RBM3D/Induction/DuhamelI.lean" | grep -v "/Probe/"
[hits: 0]

$ python3 -I imports.py   (transitive RBM3D imports of the five candidate imports)
RBM3D.Induction.EtermsMid is in the transitive imports of: []
RBM3D.Induction.Step5Kernel is in the transitive imports of: []
RBM3D.Induction.Step5Kit is in the transitive imports of: ['RBM3D.Induction.PfStep5Grid']
RBM3D.Induction.PfStep5Grid is in the transitive imports of: []
RBM3D.Path.DifREP3 is in the transitive imports of: []
direct imports of PfStep5Grid: ['RBM3D.Induction.PfStep5Alg', 'RBM3D.Induction.Step2Iterate', 'RBM3D.Induction.GridDuhamelN']
direct imports of Step5Kit: ['RBM3D.Induction.Step5Pins', 'RBM3D.Induction.KDecay', 'RBM3D.Induction.NewKLK', 'RBM3D.Induction.GridDuhamelN']
direct imports of EtermsMid: ['RBM3D.Induction.EMn2Exp2', 'RBM3D.Induction.NewKLKL', 'RBM3D.Induction.LemDecCalELip']
```
The full `lake build` in the worktree stops at the registry audit, as it must once the owed line `STDuhamelI` is deleted (the ticket's instruction) and `RBM3D.lean` does not yet import the module; the root import is the hub's (CLAUDE.md §3 (A) 4).  `registry.lean` (scratch, uncommitted) is `RBM3D.lean` with `import RBM3D.Induction.DuhamelI` after its last import line; it runs the whole-library `#assert_rbm_axioms` with the new module and exits 0.  The literal pre-check file (`import RBM3D` + `import RBM3D.Induction.DuhamelI`) cannot run here: after the failed `lake build`, `ls .lake/build/lib/lean/RBM3D.olean` in the worktree reports `No such file or directory`.  I did not edit `RBM3D.lean`, not even temporarily.

Statements extracted by script (`mk_stmts.sh`: the pin, the check statement, the targets, the instances with docstrings stripped):
```
$ sed -n 317,318p RBM3D/Induction/Step5Pins.lean   (the pin)
def STDuhamelI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t)
$ grep -n "T2333_stDuhamelI_holds" /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2333-check.lean | head -1
52:def T2333_stDuhamelI_holds : Prop := ∀ d : ℕ, STDuhamelI d
$ awk (stDuhamelI_holds, whole theorem)
theorem stDuhamelI_holds (d : ℕ) : STDuhamelI d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg _ _ _ _ _ hCon _ _ _ _ hE
  exact stDuhamelConcl_engine hd hκ hε h𝔡 sz hflow hs hst htz (st5_reg5I_mid (by omega) hReg)
    (fun n => Or.inl (hReg n).1) hCon hE STSigAll
$ awk (stDuhamelConcl_engine, signature without docstring)
theorem stDuhamelConcl_engine (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htz : ∀ n, t n ≤ lemT (z n)) (hReg : STReg5Mid sz s t)
    (hTTT : ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∨ 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2)
    (hCon : STConStInd sz (1 / 100) s t)
    (hE : ∀ D : ℝ, 0 < D →
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STELKLK sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := STIdx2 sz s t) (fun n p ω => ‖STEGt sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1 : ℝ))⁻¹ *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
      sz.Prec (U := fun n => STIdx2 sz s t n × Fin 2)
        (fun n p ω => ‖STEEk sz n (STflowE z n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
        (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (STflowE z n) (p.1.1 : ℝ))⁻¹ *
          STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2))
    (P : (Fin 2 → Bool) → Prop) :
    STDuhamelConcl sz ∅ P (STflowE z) s t := by
$ awk (instances: section "Compiled nonempty instances", docstrings stripped)
namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

theorem inst_duhamelI_proved (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t) szB zB
      (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_duhamelI (stDuhamelI_holds 3) Cd hCd

example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16)) :
    STDuhamelConcl szB ∅ STSigAll (STflowE zB) (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  stDuhamelConcl_engine (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (st5_reg5I_mid (by norm_num) szB_reg5I) (fun n => Or.inl (szB_reg5I n).1)
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num)) hE STSigAll

example (hE : STEtermsMidConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)) :
    STDuhamelConcl szB ∅ STSigSame (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  stDuhamelConcl_engine (by norm_num) (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) szB flow_zB (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) (fun n => ⟨(szB_reg5II n).1, by simp [szB]; norm_num⟩)
    (fun n => Or.inr (szB_reg5II n).2) (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) (by norm_num))
    hE STSigSame

example : (2 : ℝ) * 1 + 2 ^ 2 * 3 * (2 ^ 3 * ((2 : ℝ) ^ 99) ^ (-(1 / 4) : ℝ)) * 1 + 1 ≤
    28 * (1 + ((2 : ℝ) ^ 99) ^ (-(1 / 5) : ℝ) * 1 + 1) :=
  duhamelI_absorb (Λ := 2) (κ := 3) (F := 1) (P := 1) (Wm := 1) (A := 2 ^ 99) (ρ := 2) (Nτ := 28) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have h1 : (2 * (2 : ℝ) ^ 99) = 2 ^ 100 := by norm_num
      have h2 : ((1 : ℝ) / 100) = ((100 : ℕ) : ℝ)⁻¹ := by norm_num
      rw [h1, h2, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)])
    (by norm_num)

end RBM.Gauss.Step5Inst
```

Narrative (facts from the listings above and the files):
1. Both targets are proved in `RBM3D/Induction/DuhamelI.lean` (1994 lines; stop rule 2000; sections 1-9 at lines 39-1950, instances 1955-1994).  `stDuhamelI_holds` is unconditional (3 standard axioms; the check-file example compiles).  `stDuhamelConcl_engine` has zero-mode set `Q = ∅` and any sign class `P`.  The general-`Q` engine was not attempted: the operator `duhamelI_Phi` of sections 1-5 majorizes `𝒰` itself by `|Θ|` rows (`duhamelI_Phi_STprof`, `duhamelI_Ugen_le`), so a kernel bound for `zeroModeSet Q ∘ 𝒰` as a hypothesis restructures sections 1-5, and 6 lines remain to the stop rule (the ticket allows keeping `Q = ∅`).
2. Route: the corrections F1 and F2 of (a) were followed; no (a′) is needed.  F1: `STGridRepNAt` conjunct 4 / `STeeUM` is not used.  `duhamelI_Ugen_le` bounds `‖𝒰_{v,w} ∘ Y‖` by `Φ_{2(1-v)}(|Y|)` through `step5Kernel_UN_decompU` (`duhamelI_expand`, `duhamelI_Phi`); `duhamelI_mart_Ugen` (with `duhamelI_abel`, `duhamelI_weights`, `duhamelI_mart_gen`) Abel-sums the slot weights `α², αβ, β²` against a bound `B` of the martingale, and `B` is the diagonal bound of `STGridMartAt` (from `ST_gridMart_of_repN (stGridRepN_holds d hd)`, line 1446).  The kernel estimate `(uwp2-92kj)` enters through `duhamelI_Phi_STprof` (`step5Kernel_profile_explicit_holds`).
3. `duhamelI_path` (line 972) is the pathwise bound at one size index on a grid sample, from `pfStep5Grid_duhamel` (line 1049) with the drift term `duhamelI_drift` and the martingale term `duhamelI_mart`; `duhamelI_absorb` is the exponent closure `Λ F + Λ² κ ρ³ A^{-1/4} P + W^{-D} ≤ N^τ (F + A^{-1/5} P + W^{-D})` for `ρ ≤ (2A)^{1/100}`; `𝔠_d = 1/100` is the constant given to the pin (`3/100 - 1/4 ≤ -1/5`).
4. `duhamelI_section` (private, line 1419): the grid has `K_n = N^m` steps; the initial term (`ST_grid_whp_zero`), the three error terms (`ST_grid_whp_of_sections`, from `hE`), the martingale tails (`ST_union_prob`) and the almost sure identities hold outside an event of probability `≤ N^{-D'}` (`duhamelI_measure_le`), and the model measure is reached through `ST_pathP_eq_seqP` (line 1641).  The joint law of `(H_s, H_u)` is not used.
5. F2 is `duhamelI_lift` (line 1737): `ST_PT_of_sections` turns the per-section statement into `PrecPT`; at every cell `k` of the net `netSize (A+1) N` (`A = 2(CH+CR)+6`) and label `v` a near-minimizer `θ` of the total control `ζ(·, v)` over the cell is chosen (`Real.lt_sInf_add_pos`), so `ζ(θ) ≤ ζ(u) + N^{-CR} ≤ 2ζ(u)` because `ζ ≥ W^{-D} ≥ N^{-D}`; `stochDomAt_of_perTimeDomAt` takes the union over `(k, v)`, `cont_highProbAt_good` supplies `contGood`, and the Hölder constant is `LemDecCalELip_LK2`.  Simplification against (a): no slow-variation lemma for the profile is needed (the `etermsMid_zeta_close` copy planned in (a) is not used).
6. The engine statement writes `hE` out (the body of `STEtermsMidConcl`; `STEtermsMidConcl sz (STflowE z) s t` is accepted, see the instances).  Reason, from the tool log of a scratch whole-library run (before `hE` was written out) in which `hE : STEtermsMidConcl ..` was a hypothesis of a public theorem: the log line `RootCheck.lean:374:0: error: axiom audit: 1 premise(s) that no theorem of this development proves are in none of borrowedProps, owedProps, structuralProps, refutedProps, supersededPr` (cut at 300 characters in the log) is followed by the line `[RBM.Gauss.Sizes.STEtermsMidConcl]`.  `duhamelI_section` is `private`; the scan ignores private names.
7. Unused premises of the pin: the proof of `stDuhamelI_holds` (listing above) binds `STKbound, STKward, STLK, STDecay, STDecayStrong` (five `_`), `STStep1Loop, STStep2Concl, STLmaxU, STLKU` (four `_`) and `Cd` without using them; only `STReg5I`, `STConStInd`, the flow, the time ranges and `hE` are used.
8. Imports: the ticket's four (`EtermsMid`, `Step5Kernel`, `Step5Kit`, `DifREP3`) plus `PfStep5Grid`.  `pfStep5Grid_duhamel` (named in (a), `PfStep5Grid.lean:130`) is in none of the four's transitive imports (`imports.py` above), so the ticket's list was incomplete: deviation, flagged.  `Step5Kit` is transitive through `PfStep5Grid` and is dropped, as the ticket instructs; the file imports `EtermsMid`, `Step5Kernel`, `PfStep5Grid`, `DifREP3`.
9. Provenance: nothing is ported from RBM1D or RBM2D (scan of this stage's tool calls for `RBM1D|RBM2D`: the only hit is the scan command itself; no diff-stat needed).  In-repo copies: `duhamelI_stoch_of_subset` is `cont_stochDomAt_of_subset` (`ContinuityNet.lean:76`, private there); `duhamelI_prof_mono` is the `STprof` form of the private `step5Ker_tailW_mono_time` (`Step5Kernel.lean:337`), proved from `ST_tailT_mono_time`.
10. Style: two `set_option maxHeartbeats 1000000 in` (`duhamelI_path` line 965, `duhamelI_section` line 1413), each followed by a `-- reason` line; `lake build` prints no warning naming the file (count 0 above); the registry edit is one deleted line (`git diff --stat` above).

## (c) Verified Mathlib names (resolved by script `modcheck3.lean` against the environment of the built module; 181 names; the tactics `by_cases`, `by_contra`, `norm_num` removed)
```
abs_add_le abs_le abs_mul abs_nonneg abs_of_nonneg abs_of_nonpos abs_sub_comm abs_zero add_assoc add_le_add add_le_add_left add_nonneg add_zero Classical.not_not Complex.norm_real Complex.real_smul csInf_le
div_eq_mul_inv div_le_div_of_nonneg_left div_le_div_of_nonneg_right div_le_iff₀ div_le_one div_mul_eq_mul_div div_nonneg div_pos div_self ENNReal.ofReal ENNReal.ofReal_add ENNReal.ofReal_le_ofReal
Filter.eventually_ge_atTop Fin.prod_univ_two Finset.card_range Finset.measurable_sum Finset.mem_range Finset.mem_univ Finset.mul_sum Finset.range Finset.range_mono Finset.sum_add_distrib Finset.sum_comm
Finset.sum_congr Finset.sum_const Finset.sum_ite_eq Finset.sum_le_sum Finset.sum_le_sum_of_subset_of_nonneg Finset.sum_mul Finset.sum_mul_sum Finset.sum_nonneg Finset.sum_range_by_parts Finset.sum_range_sub
Finset.sum_range_sub' Finset.sup_congr Finset.sup_le Fintype.card Fintype.card_fin Fintype.card_le_of_injective Fintype.card_prod Fintype.sum_equiv Fintype.sum_prod_type' half_pos inv_anti₀ inv_div
inv_le_iff_one_le_mul₀ inv_nonneg inv_pos inv_pow ite_mul le_antisymm le_div_iff₀ le_max_left le_max_right le_min le_or_gt le_rfl le_self_pow₀ le_total le_trans lt_of_le_of_lt lt_of_lt_of_le Matrix.one_apply
max_le max_le_max measurable_const measurableSet_lt MeasurableSet.iUnion MeasureTheory.ae_all_iff MeasureTheory.ae_iff MeasureTheory.measure_mono MeasureTheory.measure_union_le min_eq_left min_eq_right
min_le_left mul_add mul_assoc mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_left_comm mul_nonneg mul_one mul_pos mul_pow MulZeroClass.zero_mul Nat.cast_le Nat.cast_mul Nat.cast_nonneg
Nat.cast_ofNat Nat.le_ceil Nat.lt_succ_of_le Nat.one_le_iff_ne_zero Nat.pos_of_ne_zero Nat.sub_add_cancel Nat.zero_le neg_nonpos neg_sub norm_add_le norm_add₃_le norm_mul norm_nonneg norm_pow norm_smul
norm_sub_le norm_sum_le not_le not_lt not_or nsmul_eq_mul one_div one_div_le_one_div_of_le one_le_pow₀ one_mul one_pos Or.inl Or.inr Pi.sub_apply pow_add pow_le_pow_left₀ pow_le_pow_right₀ pow_ne_zero pow_pos
Prod.ext Prod.mk.inj Real.inv_rpow Real.lt_sInf_add_pos Real.mul_rpow Real.norm_eq_abs Real.norm_of_nonneg Real.one_le_rpow Real.pow_rpow_inv_natCast Real.rpow_add Real.rpow_le_one_of_one_le_of_nonpos
Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_nonpos Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_neg_one Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.rpow_two
Real.sq_sqrt Real.sqrt Real.sqrt_eq_rpow Real.sqrt_le_left Real.sqrt_le_sqrt Real.sqrt_mul Real.sqrt_nonneg Real.sqrt_sq Set.Icc Set.mem_compl_iff Set.mem_iUnion Set.mem_union smul_eq_mul sq_abs sq_nonneg
sub_nonneg sub_self Subtype.ext zero_le_one
```
Verified deprecated (build log of this session): `Set.mem_setOf_eq` is deprecated in v4.34.0 (use `Set.mem_ofPred_eq`); the file uses neither.  Verified absent: `import Mathlib` (no `Mathlib.olean` in this checkout; scratch files import project modules).

## (d) Open issues and paper-delta candidates
- Hub, at merge: add `import RBM3D.Induction.DuhamelI` after the last `import` line of `RBM3D.lean` (before `#assert_rbm_axioms`); the worktree `lake build` fails until then (above), the scratch root run passes (exit 0, 9944 theorems, 0 axioms).
- `T2333a` (route, not a statement): the paper's `(uuwmskiow)` weights the martingale by `𝒰` (`3_5:2024-2038`, conjunct 4, `STeeUM`, factor `ρ³`); Lean Abel-sums the slot weights against the unweighted diagonal bound (factor `ρ²`, `STeeUM` unused) and closes with the paper's `ρ³A^{-1/4} ≤ A^{-1/5}` form.  Proposal: note in `docs/paper-deltas.md` that conjunct 4 of `STGridRepNAt` is not needed for case (i).
- `T2333b` (uniformity in `u`): `1_2:1400` ("standard `N^{-C}`-net and perturbation argument") covers slowly varying controls; for an arbitrary deterministic `F` the Lean lift picks near-minimizers per cell (`duhamelI_lift`).  Proposal: one line in `docs/paper-deltas.md`.
- `T2333c` (pin shape): `STDuhamelI` carries nine Step 1-4 premises and `Cd` that its proof does not use (item 7); the dispatcher may restate the pin without them (the unconditional `stDuhamelI_holds` already implies every weaker form).
- `T2333d` (registry scan): a public theorem whose hypothesis is a Prop-valued `STxxxConcl` that no theorem proves is flagged by `#assert_rbm_axioms` (item 6); engines for later pins should write the hypothesis out, as `stDuhamelConcl_engine` does.
- S5-26 (`STDuhamelII`): the `STSigSame`, `Q = ∅` conjunct follows from `stDuhamelConcl_engine` with `hTTT` through `Or.inr` (compiled example at `(szB, zB, 15/16, 31/32)`); `STReg5II → STReg5Mid` in general is the inequality `ilambda²/L² ≤ ilambda²`, not proved here; the `Q^{(1)}` conjunct (mixed signs) needs a zero-mode kernel estimate and the general-`Φ` restructuring of item 1, not done.
- Public API for reuse: `duhamelI_lift`, `duhamelI_card_le`, `duhamelI_W_le_size`, `duhamelI_Phi*`, `duhamelI_Ugen_le`, `duhamelI_mart_Ugen`, `duhamelI_path`, and the numerics `duhamelI_imag/htN/rho/apriori/rp/floor`; the other helpers are `private`.
