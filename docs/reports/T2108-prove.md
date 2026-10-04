Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 03:50:24 UTC 2026

Sources: RBM2D `c9a24cf` (`Green/AvgPins` 736 lines, `Green/LocalLaw` 378 as shown by `git show`); merged RBM3D at worktree HEAD `90a2761` (`Green/Pins.lean`, `Green/EntryDom.lean`, `Green/CondDom.lean`, `Green/Stability.lean`). `SP` = scratchpad `T2108/`.

### (i) Exponent table

| # | quantity | value (d=3) | constraint / what changes with d | slack |
|---|---|---|---|---|
| 1 | near set of `LocalLaw_near_card`, `_mem_sbSupport` | RBM2D `zdist2 = zdist x + zdist y` (`Defs/Dist.lean:94`, an `ℓ¹` ball, 5 pts, `sbSupport`). Merged `gexRHS` (`Pins.lean:101-105`) uses `zdistInf` (`Defs/Sizes.lean:115`, `L^∞`): near set `{v : ∀ i, v i ∈ {0,1,-1}}` has `3^d = 27` points (`L ≥ 3`), **not `2d+1 = 7` as the ticket says**; the `ℓ¹` ball is `7` | `mem_sbSupport` (`zdist ≤ 1 → ∈ sbSupport`) is false for `zdistInf` (`(1,1,0)`): merged `flucVanish_sbSupport` (`FlucVanish.lean:1070`, `x = 0 ∨ zdistD x = 1`, `2d+1` points by `flucVanish_card_sbSupport`) is the `ℓ¹` ball and the likely source of the ticket's count. Count by injection into `piFinset (fun _ => {0,1,-1})`, card `3^d` | `SP/near.py` row 1-3: `#{zdistInf≤1}=27`, `#{zdistD≤1}=7`, `L^∞`-ball not inside `ℓ¹`-ball (L=3,4,5) |
| 2 | `LocalLaw_gexRHS_le` factor (RBM2D `25 = 5·5`) | `9^d = 729` | sharp for the merged `gexRHS`: it is `3^d · 3^d` double sum; the `ℓ¹` value `(2d+1)² = 49` is **false** | model-law, 10³ samples: `729` never violated, `49` violated in 291/1000 (max ratio 267.8); rank-one `M = s·11ᵀ/N`: ratio 728.8 `≤ 729`, `49` fails (row 2 output) |
| 3 | `W⁻²` diagonal term of `gexRHS` | `(W^d)⁻¹ = 1/8` at `W=2` (`Pins.lean:105`) | `1(|a-b|≤1)·(W^d)⁻¹ ≤ (W^d)⁻¹` | exact |
| 4 | `LocalLaw_absorb`/`_trans` threshold (RBM2D `26 = 25+1`) | `9^d + 1 = 730` | `X ≤ a(Ka Q+Q) ≤ (K+1)bQ ≤ b²Q` needs `b = N^{τ/2} ≥ K+1`, `K = 9^d`; diagonal branch `maxLoop ≤ K maxLoop + Ψ²` | `τ=1`: `N ≥ 5.3e5` (`sz0` n=0 ok); `τ=0.1`: `N ≥ 1.8e57` (`sz0` n ≥ 676); eventual only |
| 5 | `hW2 : (W^d)⁻¹ ≤ Ψ²` from floor `W⁻¹ ≤ Ψ` | RBM2D `(W²)⁻¹ ≤ Ψ²` (equality at d=2) | `(W⁻¹)^d ≤ (W⁻¹)² ≤ Ψ²`: needs `d ≥ 2`, `W ≥ 1` (`W_pos`) | `W=2,d=3`: `1/8 ≤ 1/4`, ratio `W^{d-2} = 2` |
| 6 | floor in the pins (`LocalLawDetThm`, FA, IBP, `GavLDetFloorThm`): RBM2D `W⁻¹ ≤ Ψ` | paper floor is `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` (`3_5:30`); RBM2D `W⁻¹` is `W^{-d/2}` at `d=2` (`AvgPins:143`) | literal port keeps `W⁻¹ ≤ Ψ`: a stronger hypothesis than the paper's for `d ≥ 3` (`W⁻¹ ≥ W^{-3/2}`), a true statement; `GavLDetThm` (the pin inside `GbEXPHypV3`) has no floor | `W=2`: `W⁻¹ = .5 ≥ W^{-3/2} = .354`. Candidate T2108a (see (d) of 1b); a `(W^d)⁻¹ ≤ Ψ²` form would be the d-faithful floor, a dispatcher choice for S1-28/29 |
| 7 | `loopFloorThm`: RBM2D `(W⁻¹)² ≤ 4N^εΨ²` | `inv_Wd_le_maxLoopPM : (W^d)⁻¹ ≤ 4 maxLoopPM` (`EntryDom.lean:386`, needs `hM`, `|E| ≤ 2`, `GoodEvent`, `δ ≤ 1/2`); then `(W⁻¹)² ≤ (W^d)⁻¹` | needs `d ≥ 2` (take `hd : 3 ≤ d`) | `E=.5,t=1/16`: `max 𝓛 ∈ [.1300,.1336]` vs `W^{-d}/4 = .03125` (20 samples, SP/gex.py) |
| 8 | grid cardinalities | `Unit × Zd × Zd`: `L^{2d} ≤ (WL)^{2d} = size²`; `Zd`: `L^d ≤ size^1`; `Vtx`, `Idx`: `= size` | `m = 2, 1, 1` are `d`-free; `L^d ≤ size` uses `W ≥ 1` only | `L=3,W=2`: `729 ≤ 46656`; `27 ≤ 216` |
| 9 | stability constant in `avgBoundDetThm`: RBM2D `1+2Kstab2 κ L_n ≤ N^ε` (log growth, needs `Bandwidth`) | `1 + 2 Kstab3 d 𝔡⁻¹ κ` (`Stability.lean:212`), independent of `n` | `≤ N^ε` eventually from `size → ∞` only; needs `0 < lam n ≤ 𝔡⁻¹` eventually (`(eq:WO)`), `hd : 3 ≤ d`, `norm_avgErr_le` (`EntryDom.lean:573`) | `W_le_size'` (needs `d ≥ 1`), `eventually_Kstab2_*'` not needed |
| 10 | `eta_lower_of_rangeCond` | `N⁻¹ ≤ (1-t) Im m(E)`, `Im m ≥ c₀ = √(κ(4-κ))/2` (`mE_im`, `zt_im`) | `d`-free; `N^δ c₀ ≥ 1` eventually | `κ=δ=1/20`: `c₀ = .2222`, `N ≥ 1.16e13` (`sz0` n ≥ 2); eventual |
| 11 | constants `κ,𝔠,𝔡,δ,c,a` | `1/20, 1/6, 1/10, 1/20, 1/40` (merged `Instance.premises`, `inst_gijGEXPTSwap`), `a = 1/6` (chosen here) | `Admissible 𝔠 𝔡 = 0<𝔠 ∧ 0<𝔡 ∧ SizeTendsto ∧ Bandwidth ∧ WO` replaces `SizeTendsto → Bandwidth` (D39); `Ψ = W⁻¹ ≤ N^{-a}` needs `a ≤ 𝔠` | `W ≥ N^{1/6}` at `sz0` all n; `Ψ ≤ N^{-1/6}` True |

**Pins, merged vs RBM2D** (`Pins.lean`): `GbEXPHypV3 sz κ 𝔠 𝔡 δ` takes `sz.Admissible 𝔠 𝔡` (`:210-219`); `GbEXPV3Theorem (d : ℕ)` has no `hd` (`:224`); `LoopDetSeq` over `Unit × Zd × Zd` (`:172`, `d`-free shape, RBM2D `Z2`); `GijOmegaSeq/GijSeq/GiiSeq` live on `Unit × Idx × Idx` with right side `gexRHS … (STblk q) (STblk p)` (swapped pair, `:132-167`), so RBM2D's `LocalLaw_reindex` along `splitEquiv` and the bridge `step2Local_llErrMat_eq` are not needed: `llErrMat`, `offSq`, `diagSq` (`:73,115,119`) are on `Idx`, `llErrMat i j = √offSq i j` (`i≠j`), `= √diagSq i` (`i=j`) by `Real.sqrt_sq`. `giiOmegaSeq`, `giiSeq_of_asGMc` take `hd : 3 ≤ d` (`CondDom.lean:765,792`), `gijOmegaSeq`, `gijSeq_of_asGMc` do not.

**Where `hd` enters** (theorem arguments, as D201; the `Prop` pins stay `∀ sz` with no `hd`, like `GbEXPV3Theorem d`): `localLawDetThm` (via `giiSeq_of_asGMc`; also `d ≥ 2` of row 5), `avgBoundDetThm` (`norm_avgErr_le`), `loopFloorThm` (row 7), `gavLDetThm_of_floor` (calls `loopFloorThm`), `gbEXPV3Theorem_of_gavLDetThm` (`giiOmegaSeq`), `gbEXPV3Theorem_of_parts`, `gbEXPV3Theorem_of_ports`. `gavLDetFloorThm_of_parts` takes the pins as hypotheses: no `hd`.

**Port decisions** (no Lean written): public declarations dropped: `AvgPins_one_le_size` (merged `Sizes.one_le_size`, `StochDomAt.lean:130`, `Nat` form, cast in place), `llErrMat_time_zero` (merged `Pins.lean:1242`; same for `greenBlk_time_zero`, `perTimeDomAt_of_nonpos`); private copies replace the `Kstab2`, `W_le_size'`, `card_z2*'`, `sbSupport` helpers. RBM2D `Step2Local` has three private helpers (`Step2Local_mem_sbSupport/_near_card/_gexRHS_le`, lines 129-158) and one public bridge (line 66), not "two private helpers": only `near_card` and `gexRHS_le` are re-proved (rows 1-2), the other two are dropped (see above). `d=2` tokens: neither text contains `scaleM, ellT, tailT, ellStar, Meta, ellz, 1/5, N2, inv2` (grep count 0/0); `UniformWeight`/`BoundedWeight` occur in neither (D192 needs no action); `W⁻²` → `(W^d)⁻¹` (`LocalLaw` `130,136-141,284`; `AvgPins` `132,175,182,460`), `Z2/zdist2` (portmap P.7 counts: `LocalLaw` 43, `AvgPins` 8) → `Zd d`, `zdistInf`, `^ 2` on `Z2` cardinalities (`AvgPins:336-349`, `LocalLaw:243-248`) → `L^d`, `size`, row 8.

**DECISIONS §29 items.** (1) time domain: pins take `∀ n, 0 ≤ t n`, `t n < 1`, as the merged `GbEXPHypV3`; no `s`, `lemT`, `ℓ`, `ilambda` occurs; `LoopFloorThm` takes no time hypothesis at all (`|E n| ≤ 2` only; `inv_Wd_le_maxLoopPM` has no `u` condition). (2) case (ii) boundary / negative time: not present. (3) `L^d ≤ W^K` not used; `W`-`size` relations only via `Bandwidth` (`hWhalf: W^{-c/2} ≤ 1/2`, `Ψ' ≤ N^{-min(a,𝔠)}`) and `L^d ≤ size` (row 8). (4) `∀ n`/`∀ᶠ n`: `|E n| < 2-κ`, `0 ≤ t n < 1` `∀ n` are the merged pin's own; `Admissible`, `RangeCond`, `Ψ ≤ N^{-a}` are `∀ᶠ`; the floor `∀ n, W⁻¹ ≤ Ψ n` is kept `∀ n` as ported (it is a hypothesis of `LocalLawDetThm`, FA, IBP, `GavLDetFloorThm`; `gavLDetThm_of_floor` supplies it with `Ψ' = max Ψ W⁻¹`); `|E n| ≤ 2` of the time-zero lemmas is `∀ n` and is used at `t ≡ 0` (`G_0 = m·1`, so `|E| = 2` is allowed, as merged `llErrMat_time_zero`). `|E n| ≤ 2` is derived from `< 2-κ`. `t = 0`: `RangeCond` at `t ≡ 0` holds for `δ ≤ 1` (`N^{-1+δ} ≤ 1`); `asGMcSeq_time_zero` (`Pins.lean:1401`) discharges `AsGMcSeq`, so the conclusions `localLawDetSeq_time_zero`, `fixedTimeFASeq_time_zero`, `ibpDetSeq_time_zero` have a compiled-instance route at `t ≡ 0`.

### (ii) One concrete nondegenerate instance

**SA** `cd SP && python3 near.py; python3 gex.py; python3 inst.py` (`d=3, L=3, W=2, g=1/2`, `N=216`, 27 blocks of 8 sites; `gex.py` builds `svarF = W⁻ᵈ SB(blk i - blk j)`, `H = √u X`, `z = zt E u`, `loopPM(a,b) = tr(G Eₐ G* E_b) = (W⁻ᵈ)² Σ_{rows in b, cols in a}|G|²` as `Pins.lean:1278`, `gexRHS` as `Pins.lean:101`; trace and block-sum agree in line 2). Output, verbatim:
```
d=3 L=3: #{zdistInf<=1}=27 (3^d=27)  #{zdistD<=1}=7 (2d+1=7)  Linf-ball subset of l1-ball: False
d=3 L=4: #{zdistInf<=1}=27 (3^d=27)  #{zdistD<=1}=7 (2d+1=7)  Linf-ball subset of l1-ball: False
d=3 L=5: #{zdistInf<=1}=27 (3^d=27)  #{zdistD<=1}=7 (2d+1=7)  Linf-ball subset of l1-ball: False
constants d=3: 3^d = 27 , gexRHS factor 9^d = 729 , absorb 9^d+1 = 730  (ticket's l1 count: (2d+1)^2 = 49 , +1 = 50 ; RBM2D 25/26)
SB row sum [1. 1.] svarF diag 0.05 =W^-d/(1+2dg^2)= 0.05 N= 216 #blocks 27 near-row sum [27. 27.]
trace check: tr(G+ Ea G- Eb) = (0.0024397447317852064+1.1079190950086248e-18j)   block-sum formula = 0.002439744731785205
model-law samples: 1000; violations of gexRHS<=729*max+W^-d: 0; of gexRHS<=49*max+W^-d: 291; max (gexRHS-W^-d*1_near)/max over samples = 267.828 (<=729)
rank-one M, E=0.5, u=0.9999: eta=9.68e-05 maxLoop=2286.7368 max_(a,b) gexRHS=1666680.231 ; (gexRHS-W^-d*1)/max = 728.8 ; 49*max+W^-d=112050.229 -> l1-count inequality FAILS; 729*max+W^-d=1667031.266 -> holds
rank-one M, E=0.5, u=0.999: eta=9.68e-04 maxLoop=23.3628 max_(a,b) gexRHS=16680.243 ; (gexRHS-W^-d*1)/max = 714.0 ; 49*max+W^-d=1144.901 -> l1-count inequality FAILS; 729*max+W^-d=17031.593 -> holds
rank-one M, E=0.5, u=0.99: eta=9.68e-03 maxLoop=0.7334 max_(a,b) gexRHS=180.359 ; (gexRHS-W^-d*1)/max = 245.8 ; 49*max+W^-d=36.061 -> l1-count inequality FAILS; 729*max+W^-d=534.762 -> holds
E=0.5,t=1/16 (20 samples): max_ab|L| in [0.1300,0.1336]  vs floor W^-d=0.1250 and Psi^2=W^-2=0.2500;  ||G-m||_max in [0.148,0.192]
sz0: L=4(n+1), W=(2(n+1))^5, lam=(2(n+1))^-6, N=(W L)^3; z_n=1/2+i N^(-4/5); E_n=lemE(z_n); t=1/16; Psi_n=W^-1
n=0: L=4 W=32 N=2.1e+06 lam=0.016 E=0.5000 |E|<1.95:True t0=0.99999>=1/16:True Bandwidth:True WO:True RangeCond:True Psi<=N^-1/6:True W^-d=3.05e-05<=Psi^2=9.77e-04:True N^-1=4.8e-07<=Im zt=0.9077
n=1: L=8 W=1024 N=5.5e+11 lam=0.00024 E=0.5000 |E|<1.95:True t0=1.00000>=1/16:True Bandwidth:True WO:True RangeCond:True Psi<=N^-1/6:True W^-d=9.31e-10<=Psi^2=9.54e-07:True N^-1=1.8e-12<=Im zt=0.9077
n=50: L=204 W=11040808032 N=1.14e+37 lam=8.9e-13 E=0.5000 |E|<1.95:True t0=1.00000>=1/16:True Bandwidth:True WO:True RangeCond:True Psi<=N^-1/6:True W^-d=7.43e-31<=Psi^2=8.20e-21:True N^-1=8.8e-38<=Im zt=0.9077
--- eventual thresholds (all are 'for n large', not instance hypotheses)
tau=1.0: N^(tau/2)>=9^d+1=730 <=> N>=5.329e+05; first n at sz0: 0
tau=0.1: N^(tau/2)>=9^d+1=730 <=> N>=1.847e+57; first n at sz0: 676
c=1.0: hWhalf W^(-c/2)<=1/2 <=> W>=4.000e+00; first n at sz0: 0
eta_lower_of_rangeCond: c0=sqrt(k(4-k))/2=0.2222; N^delta*c0>=1 <=> N>=1.161e+13; sz0 first n: 2
floor slack at W=2,d=3: (W^-1)^2 = 0.25  W^-d = 0.125  ratio W^(d-2) = 2
limits (external hyps AsGMcSeq c=1/40, LoopDetSeq Psi=W^-1): W_n^-c ->0: ['9.170e-01', '8.409e-01', '5.610e-01', '2.900e-01'] ; paper window W^(-d/2)<=Psi<=W^(-eps0): d/2=1.5 >= 1 >= eps0=c=1/40; max L floor W^-d / Psi^2 = W^-(d-2): ['3.125e-02', '9.766e-04', '9.057e-11']
```
Instance data for the targets: merged `sz0` (`Defs/Sizes.lean:260`), `E = lemE ∘ z₀`, `t ≡ 1/16`, `κ=δ=1/20`, `𝔠=1/6`, `𝔡=1/10`, `c=1/40`, `Ψ = W⁻¹` (floor with equality, `Ψ ≤ N^{-1/6}`), `a = 1/6`. Deterministic hypotheses of `localLawDetThm`, `loopFloorThm`, `avgBoundDetThm` (`Admissible`, bulk, `0 ≤ t < 1`, `RangeCond`, floor) hold at every `n` printed (`sz0` Admissible/RangeCond: `Instance.premises`, `Pins.lean:1426`); `hWhalf`, the `730` threshold and `eta_lower` are `∀ᶠ` steps of the proofs, not hypotheses. The targets taking pins as hypotheses (`gavLDetFloorThm_of_parts`, `gavLDetThm_of_floor`, `gbEXPV3Theorem_of_*`) keep the other gates' pins (`FixedTimeFAThm`, `IBPDetThm`) as hypotheses of the example.
**External hypotheses, limit computation (TEAM §8 l.14).** `AsGMcSeq sz0 E t (1/40)` (`3_5:30`) and `LoopDetSeq sz0 E t W⁻¹` are inputs, not proved, truth not claimed: consistent with the paper window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` (`1.5 ≥ 1 ≥ 1/40`); floor `W^{-d}`-vs-`Ψ²=W^{-2}` ratio `W^{-(d-2)} → 0` (`3.1e-2, 9.8e-4, 9.1e-11` at n=0,1,50); `W_n^{-1/40} → 0` (`.917, .841, .561, .290` at n=0,1,50,10⁴); at `d=3,L=3,W=2,E=.5,t=1/16` the sampled `max 𝓛` is `.130-.134 ≤ Ψ² = .25` and `≥ W^{-d}/4`. `IBPDet/FARowDet/FABlkDet` of `avgBoundDetThm` are the outputs of the open pins `FixedTimeFAThm`, `IBPDetThm` (S1-28/29); not claimed.

### Verdicts
- `localLawDetThm` (`LocalLaw:279`), `LocalLawDetSeq`/`LocalLawDetThm` (`AvgPins:70,134`): **PASS** with the correction of rows 1, 2, 4: constants `9^d`, `9^d+1` (ticket's `2d+1` count and the `sbSupport` route are false for `zdistInf`); `hd : 3 ≤ d` and `d ≥ 2` (row 5).
- `FixedTimeFASeq`, `IBPDetSeq` (`AvgPins:110,115`), `FixedTimeFAThm`, `IBPDetThm`, `AvgBoundDetThm`, `avgBoundDetThm` (`:416`): **PASS** (rows 9-11; `Vtx`-indexed `svar`, `blkCoef2` of merged `EntryDom`; `Kstab3` replaces `Kstab2`; `Admissible`, `hd`).
- `loopFloorThm` (`:462`), `gavLDetThm_of_floor`, `gavLDetFloorThm_of_parts`, `gbEXPV3Theorem_of_parts/_of_ports/_of_gavLDetThm`, `_time_zero` lemmas, `eta_lower_of_rangeCond`, `not_sizeTendsto_bandwidth_of_W_one`: **PASS** (rows 5-7, 10; floor kept `W⁻¹`, row 6).
- No statement is false at `d ≥ 3` except the ticket's `2d+1`-count of the near set (a statement of the ticket, not of a target); no BLOCKED input.

## (a′) Preflight corrections — Sun Oct  4 04:53:12 UTC 2026
1. (i) row 7 writes `(W⁻¹)² ≤ (W^d)⁻¹`. For `d > 2`, `W > 1` it is the other way: line 55 of this file (`floor slack at W=2,d=3: (W^-1)^2 = 0.25  W^-d = 0.125`). With the floor `W⁻¹` of row 6 the loop floor `(W⁻¹)² ≤ 4 N^ε Ψ²` does not follow from `inv_Wd_le_maxLoopPM` (`W^{-d} ≤ 4 max𝓛`), and it is false at `d = 3`: compiled `LocalLaw_loopFloor_literal_false` (b.2; file line 1207).
2. Row 6 calls the literal floor `W⁻¹ ≤ Ψ` "a true statement". That holds for `LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm` taken one at a time, not for the chain: `gavLDetThm_of_floor` needs `floor² ≤ 4 N^ε Ψ²` (item 1). Rows 6-7 and the verdicts of `loopFloorThm`, `gavLDetThm_of_floor`, `gbEXPV3Theorem_of_parts` hold for the statements with the floor `W^{-d/2}` of the paper and `LoopFloorThm d` concluding `(W^d)⁻¹ ≤ 4 N^ε Ψ²`: paper-delta candidate T2108a (d.1).
3. Row 6 cites the paper floor at `3_5:30`; it is at `3_5:27` (`grep -n "Finally, suppose" paper/tex/3_5_Loop_Hierarchy.tex` gives line 27; `3_5:28` is the label of (`initialGT2`)).
4. Row 7 "needs `d ≥ 2` (take `hd : 3 ≤ d`)": `loopFloorThm` takes no `hd`; `gavLDetThm_of_floor` takes `2 ≤ d` (`W^{-d/2} ≤ W⁻¹`); `hd : 3 ≤ d` only where `giiSeq_of_asGMc`, `giiOmegaSeq`, `norm_avgErr_le` are called (b.3).
5. Verdict effect: no verdict of (a) becomes FAIL or BLOCKED; the PASS verdicts hold for the d-faithful statements compiled in (b); the literal-floor statements do not close (item 1). The change is the exponent recount of CLAUDE.md §5.2 / rule R3 of ST1-COMMON item 2, flagged for sign-off in (d.1).

## (b) Script output — Sun Oct  4 04:53:12 UTC 2026
Worktree `RBM3D-wt/T2108`, branch `t/T2108`. Builds and scripts below were re-run from Sun Oct  4 04:45:12 UTC 2026 (`scratchpad/T2108/rep/t_start.txt`) to the time above; scripts and raw outputs are in `scratchpad/T2108/` (`rep/*.full`).
### b.1 Build, hygiene, registry pre-check
```
$ git rev-parse --short HEAD; git status --short | wc -l; git log main..t/T2108 --oneline | wc -l
8f518d4
0
1
$ git diff --name-only main...t/T2108
RBM3D/Green/LocalLaw.lean
RBM3D/Test/Axioms.lean
$ grep -cE "\bsorry\b|\badmit\b|native_decide|^axiom |^\s*axiom " RBM3D/Green/LocalLaw.lean
0
$ lake build RBM3D.Green.LocalLaw 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3337 jobs).
$ lake build 2>&1 | tail -2        # full library, root #assert_rbm_axioms (exit 0)
non-vacuity certificates: 4 of 108 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3854 jobs).
$ lake env lean scratchpad/T2108/precheck.lean     # import RBM3D; import RBM3D.Green.LocalLaw; #assert_rbm_axioms  (exit 0)
axiom audit: 3304 theorems, 1207 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Green.FixedTimeFAThm: 4 [no certificate]
  RBM.Green.IBPDetThm: 4 [no certificate]
$ # same file before the two registry lines were added (scratchpad/T2108/precheck0.out)
scratchpad/T2108/precheck.lean:3:0: error: axiom audit: 2 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`:
  [RBM.Green.IBPDetThm, RBM.Green.FixedTimeFAThm]
```
Registry (`RBM3D/Test/Axioms.lean`, `owedProps`, lines 191-193; 191 only gets a comma): `RBM.Green.FixedTimeFAThm`, `RBM.Green.IBPDetThm`, class owed (ST1-COMMON item 8). The other new `Prop` defs are proved by theorems of the file (the pre-check accepts them).
### b.2 `#print axioms` (script `axioms.lean`: one line per new public declaration, 33 names)
```
$ lake env lean scratchpad/T2108/axioms.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
33
$ lake env lean scratchpad/T2108/axioms.lean | grep -vc "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
0
$ lake env lean scratchpad/T2108/axioms.lean | sed -E "s/'RBM\.Green\.([^']*)' depends.*/\1/" | tr '\n' ' '
condDiagBlk LocalLawDetSeq IBPDet FARowDet FABlkDet FixedTimeFASeq IBPDetSeq asGMcSeq_iff LocalLawDetThm FixedTimeFAThm IBPDetThm AvgBoundDetThm LoopFloorThm GavLDetFloorThm GavLDetThm gbEXPV3Theorem_of_gavLDetThm loopDetSeq_mono gavLDetThm_of_floor gavLDetFloorThm_of_parts gbEXPV3Theorem_of_parts LocalLaw_gexRHS_le_maxLoopPM localLawDetThm avgBoundDetThm loopFloorThm gbEXPV3Theorem_of_ports LocalLaw_gbEXPV3Theorem_of_fa_ibp localLawDetSeq_time_zero condDiagBlk_time_zero fixedTimeFASeq_time_zero ibpDetSeq_time_zero not_sizeTendsto_bandwidth_of_W_one eta_lower_of_rangeCond LocalLaw_loopFloor_literal_false 
```
### b.3 Target statements, extracted from the file by `extract.py` (comments stripped, whitespace collapsed; `extract.py | grep -v '^$'`)
```
def LocalLawDetThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t → ∀ c > (0 : ℝ), AsGMcSeq sz E t c → ∀ Ψ : ℕ → ℝ, (∀ n, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) → LoopDetSeq sz E t Ψ → LocalLawDetSeq sz E t Ψ
def FixedTimeFAThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t → ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) → (∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧ Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) → LocalLawDetSeq sz E t Ψ → FixedTimeFASeq sz E t Ψ
def IBPDetThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t → ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) → (∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧ Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) → LocalLawDetSeq sz E t Ψ → IBPDetSeq sz E t Ψ
def AvgBoundDetThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → ∀ (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ) (Ψ : ℕ → ℝ), IBPDet sz E t x Ψ → FARowDet sz E t x Ψ → FABlkDet sz E t x Ψ → GavLDetSeq sz E t Ψ
def LoopFloorThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (𝔠 𝔡 : ℝ), 0 < 𝔠 → 0 < 𝔡 → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2) → ∀ c > (0 : ℝ), AsGMcSeq sz E t c → ∀ Ψ : ℕ → ℝ, LoopDetSeq sz E t Ψ → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ ε * Ψ n ^ 2
def GavLDetFloorThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t → ∀ c > (0 : ℝ), AsGMcSeq sz E t c → ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) → (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) → LoopDetSeq sz E t Ψ → GavLDetSeq sz E t Ψ
def GavLDetThm (d : ℕ) : Prop := ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 → ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t → ∀ c > (0 : ℝ), AsGMcSeq sz E t c → ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) → (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) → LoopDetSeq sz E t Ψ → GavLDetSeq sz E t Ψ
theorem localLawDetThm (hd : 3 ≤ d) : LocalLawDetThm d
theorem avgBoundDetThm (hd : 3 ≤ d) : AvgBoundDetThm d
theorem loopFloorThm (d : ℕ) : LoopFloorThm d
theorem gavLDetThm_of_floor (hd : 2 ≤ d) (hL0 : LoopFloorThm d) (hF : GavLDetFloorThm d) : GavLDetThm d
theorem gavLDetFloorThm_of_parts (hLL : LocalLawDetThm d) (hFA : FixedTimeFAThm d) (hIBP : IBPDetThm d) (hAvg : AvgBoundDetThm d) : GavLDetFloorThm d
theorem gbEXPV3Theorem_of_parts (hd : 3 ≤ d) (hLL : LocalLawDetThm d) (hFA : FixedTimeFAThm d) (hIBP : IBPDetThm d) (hAvg : AvgBoundDetThm d) (hL0 : LoopFloorThm d) : GbEXPV3Theorem d
theorem gbEXPV3Theorem_of_ports (hd : 3 ≤ d) (hLL : LocalLawDetThm d) (hFA : FixedTimeFAThm d) (hIBP : IBPDetThm d) : GbEXPV3Theorem d
theorem LocalLaw_gbEXPV3Theorem_of_fa_ibp (hd : 3 ≤ d) (hFA : FixedTimeFAThm d) (hIBP : IBPDetThm d) : GbEXPV3Theorem d
theorem gbEXPV3Theorem_of_gavLDetThm (hd : 3 ≤ d) (h : GavLDetThm d) : GbEXPV3Theorem d
theorem LocalLaw_gexRHS_le_maxLoopPM (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) : gexRHS d L W E u M a b ≤ (9 : ℝ) ^ d * maxLoopPM d L W E u M + ((W : ℝ) ^ d)⁻¹
```
### b.4 Statement diff against RBM2D `c9a24cf` (`python3 stmtdiff2.py`)
The script extracts each public statement from `git show c9a24cf:RBM2D/Green/{AvgPins,LocalLaw}.lean` (scratch copies verified identical by `diff -q`) and from the new file, applies the rename table (R1 `d : Sizes` to `sz : Sizes d`; R2 `Z2 L`, `Idx L W`, `BlockIndex` to `Zd d L`, `Idx d L W`, `Vtx d L W`; R3 `W⁻²` to `(W^d)⁻¹`; R4 `Sblk2` to `svar d L W (sz.lam n)`; `spectralM/Z` to `mE/zt`; `SizeTendsto d → Bandwidth d 𝔠` to `sz.Admissible 𝔠 𝔡` with `0 < 𝔡`; the `(d : ℕ)` of the pins; the dropped `hL : 3 ≤ L` of `LocalLaw_gexRHS_le_maxLoopPM`) and prints the token hunks that remain (`2D => 3D`). The floor is not in the table, so it shows.
```
## LocalLawDetThm, FixedTimeFAThm, IBPDetThm, GavLDetFloorThm: (((sz.W => ((sz.W | ℝ))⁻¹ => ℝ) ^ (-(d : ℝ) / 2)
## LoopFloorThm:  => 𝔡 | ℝ)⁻¹) => ℝ) | 2 => d)⁻¹
## gbEXPV3Theorem_of_gavLDetThm, gbEXPV3Theorem_of_parts, avgBoundDetThm, gbEXPV3Theorem_of_ports:  => (hd : 3 ≤ d)
## gavLDetThm_of_floor:  => (hd : 2 ≤ d)
## LocalLaw_gexRHS_le_maxLoopPM: 25 => (9 : ℝ) ^ d
## localLawDetThm:  => (hd : 3 ≤ d) |  => d
## identical after renaming (19): condDiagBlk, LocalLawDetSeq, IBPDet, FARowDet, FABlkDet, FixedTimeFASeq, IBPDetSeq, asGMcSeq_iff, AvgBoundDetThm, GavLDetThm, loopDetSeq_mono, gavLDetFloorThm_of_parts, loopFloorThm, localLawDetSeq_time_zero, condDiagBlk_time_zero, fixedTimeFASeq_time_zero, ibpDetSeq_time_zero, not_sizeTendsto_bandwidth_of_W_one, eta_lower_of_rangeCond
```
### b.5 Compiled nonempty instances (same file, section 9: `sz0`, `d = 3`, `E_n = lemE z_n`, `κ = δ = (1/10)/2`, `𝔠 = 1/6`, `𝔡 = 1/10`; `python3 ex.py`, 17 `example`s)
```
L1037 example: `localLawDetThm` at `t ≡ 1/16`
L1047 example: `localLawDetThm` at `t ≡ 0`, no hypothesis left
L1056 example: `loopFloorThm` at `t ≡ 1/16`
L1065 example: `loopFloorThm` at `t ≡ 0`, no hypothesis left
L1076 example: `avgBoundDetThm` at `t ≡ 1/16`
L1085 example: `avgBoundDetThm` at `t ≡ 0`, no hypothesis left
L1105 example: `gbEXPV3Theorem_of_gavLDetThm`, instantiated
L1113 example: `gavLDetThm_of_floor`, instantiated
L1124 example: `gavLDetFloorThm_of_parts`, instantiated
L1137 example: `gbEXPV3Theorem_of_parts`, `_of_ports`, `LocalLaw_gbEXPV3Theorem_of_fa_ibp`, instantiated
L1150 example: `loopDetSeq_mono`, instantiated
L1155 example: `asGMcSeq_iff`, instantiated
L1161 example: `localLawDetSeq_time_zero`, `fixedTimeFASeq_time_zero`, `ibpDetSeq_time_zero`, `condDiagBlk_time_zer
L1172 example: `eta_lower_of_rangeCond`, instantiated
L1179 example: `not_sizeTendsto_bandwidth_of_W_one`, instantiated
L1190 example: `LocalLaw_gexRHS_le_maxLoopPM`, instantiated
L1197 example: The same at `d = 3`, `L = 3`, `W = 1`, `E = 0`, `u = 1/2`, `M = 0`, `a = b =
```
One verbatim (lines 1047-1053 of the file; `t ≡ 0`, no hypothesis left):
```
example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0)
    (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) :=
  localLawDetThm (d := 3) (by norm_num) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) premises.1 (STflowE z0) (fun _ => 0)
    premises.2.1 (fun _ => le_rfl) (fun _ => one_pos)
    (localLaw_inst_rangeCond_zero (by norm_num)) (1 / 40) (by norm_num)
    (asGMcSeq_time_zero sz0 localLaw_inst_hE _) _ (fun _ => le_rfl) localLaw_inst_loopDet_zero
```
### b.6 Name clashes (`python3 clash.py`: `grep -rnw` of the 33 new public names over `RBM3D/**/*.lean`; the hits are this ticket's own registry lines, comments naming the pins)
```
new public names: 33; names in axioms.lean: 33; missing from axioms.lean: []
files searched: 150 (RBM3D/**/*.lean except Green/LocalLaw.lean)
names with a hit elsewhere: 5, all in RBM3D/Test/Axioms.lean at the listed lines: FixedTimeFAThm[192] IBPDetThm[193] gavLDetFloorThm_of_parts[192,193] gbEXPV3Theorem_of_parts[192,193] LocalLaw_gbEXPV3Theorem_of_fa_ibp[192,193]
```
### b.7 Ports and `d = 2` tokens
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/AvgPins.lean RBM2D/Green/LocalLaw.lean RBM2D/Path/Step2Local.lean
 RBM2D/Green/AvgPins.lean   | 325 ++++++++++-----------------------------------
 RBM2D/Green/LocalLaw.lean  |  62 +++------
 RBM2D/Path/Step2Local.lean | 191 ++++----------------------
 3 files changed, 110 insertions(+), 468 deletions(-)
$ python3 tokens.py      # code only (comments stripped): RBM2D at c9a24cf vs the new file
token class (code only, comments stripped)     AvgPins LocalLaw      new
Z2 / zdist2                                          8       43        0
W ^ 2 / ^ 2)⁻¹ / (W⁻¹) ^ 2                           1        4        2
L ^ 2                                                1        0        0
literal 25 / 26                                      0       15        0
Kstab2 / W_le_size / card_z2                        16        0        0
Sblk2 / spectralM / spectralZ / Bandwidth d         49        0        0
(1 : ℕ) ^ 2 / `1 / 5` / N2                           0        0        0
```
Sources: `Green/AvgPins.lean:61-601` and `Green/LocalLaw.lean:91-279` at `c9a24cf` (cited per declaration in the docstrings); `Path/Step2Local.lean:129,145,158` are RBM2D's three private helpers (not imported; the near-set count and the `gexRHS` bound are re-proved, see (a) Port decisions).
### b.8 Notes (narrative)
1. Scope. `t/T2108` is one commit on `90a2761` (`main`), `8f518d4`, commit time Sat Oct 3 21:27:47 2026 -0700 (`git log -1 --format=%cd`). This stage changed no Lean file: it rebuilt that commit and re-ran every script of (b) on it.
2. Targets. Every name of the ticket's list is in the file (b.2): `LocalLawDetSeq`, `FixedTimeFASeq`, `IBPDetSeq`, `LocalLawDetThm`, `localLawDetThm`, `avgBoundDetThm`, `loopFloorThm`, `gavLDetThm_of_floor`, `gavLDetFloorThm_of_parts`, `gbEXPV3Theorem_of_parts`, `gbEXPV3Theorem_of_ports`, the four `_time_zero` lemmas, plus `asGMcSeq_iff`, `loopDetSeq_mono`, `eta_lower_of_rangeCond`, `not_sizeTendsto_bandwidth_of_W_one`, the vocabulary and the pins `FixedTimeFAThm`, `IBPDetThm`, `AvgBoundDetThm`, `LoopFloorThm`, `GavLDetFloorThm`, `GavLDetThm`.
3. Dimension. The near set of (`GijGEX`) in the merged `gexRHS` is the `zdistInf ≤ 1` ball, counted by injection into `{0,1,-1}^d` (`3^d` points): `LocalLaw_gexRHS_le_maxLoopPM` has `9^d` (RBM2D `25`), the absorption threshold of `LocalLaw_absorb` is `9^d + 1` (RBM2D `26`). The ticket's `2d + 1` is the `zdistD` ball of `flucVanish_sbSupport`; a `(2d+1)^2` constant is false for the merged `gexRHS` (line 41 of this file: 291 of 1000 samples violate `49`). `hL : 3 ≤ L` of RBM2D's statement is not needed and is dropped.
4. Floor (T2108a). RBM2D's `W⁻¹ ≤ Ψ` is the paper's `W^{-d/2} ≤ Ψ_t` (`3_5:27`) at `d = 2`; the pins `LocalLawDetThm`, `FixedTimeFAThm`, `IBPDetThm`, `GavLDetFloorThm` take `W^{-d/2} ≤ Ψ`, `LoopFloorThm d` concludes `(W^d)⁻¹ ≤ 4 N^ε Ψ²` (R3: `W⁻²`-type to `W^{-d}`). The literal port is compiled false (`LocalLaw_loopFloor_literal_false`, `sz0`, `t ≡ 0`, `ε = 1/18`). With the paper floor, `gavLDetThm_of_floor` needs `2 ≤ d` for `W^{-d/2} ≤ W⁻¹`.
5. `hd` (D201). `3 ≤ d`: `localLawDetThm` and `avgBoundDetThm` (via `giiSeq_of_asGMc`, `norm_avgErr_le`), `gbEXPV3Theorem_of_gavLDetThm`, `_of_parts`, `_of_ports`, `LocalLaw_gbEXPV3Theorem_of_fa_ibp` (via `giiOmegaSeq`, `giiSeq_of_asGMc`); `2 ≤ d`: `gavLDetThm_of_floor`; none: `loopFloorThm`, `gavLDetFloorThm_of_parts`. The `Prop` pins take `d : ℕ` and no `hd`, as merged `GbEXPV3Theorem d`. The stability constant of `avgBoundDetThm` is `1 + 2 Kstab3 d 𝔡⁻¹ κ` (n-independent; RBM2D `Kstab2 κ L_n`).
6. Dropped RBM2D public declarations: `AvgPins_one_le_size` (merged `Sizes.one_le_size`, `Defs/StochDomAt.lean:130`), `llErrMat_time_zero` (merged `Green/Pins.lean:1242`), the `AvgPinsCheck` instance section (`AvgPins.lean`, section 6; theorems at lines 644, 648, 657, 667, 682, 690, 699 and `psi2` at 665; replaced by b.5), the bridge `step2Local_llErrMat_eq` of `Path/Step2Local` (the merged `offSq`, `diagSq` are on `Idx`), and RBM2D's private `Kstab2`, `W_le_size'`, `card_z2*'`, `sbSupport` helpers (replaced by `Kstab3` and `localLaw_card_*`). No ST-2 file is imported (`PerTimeCalc` is imported by merged `EntryDom`).
7. `d = 2` tokens (b.7 table). `Z2`/`zdist2` (8 + 43), literal `25`/`26` (15), `Kstab2`-type (16), `Sblk2`/`spectralM`/`Bandwidth d` (49) have 0 hits in the new file. `W ^ 2` / `(W⁻¹) ^ 2` (AvgPins:182, LocalLaw:106,130,141,284) become `(W^d)⁻¹`; `L ^ 2` (`card_z2'`, AvgPins:336) becomes `localLaw_card_Zd : card (Zd d L) = L ^ d`. The 2 hits in the new file are the example at line 1060 (`Ψ² = (W⁻¹)²` for the control `Ψ = W⁻¹`) and the counterexample statement at line 1212.
8. Instances. `t ≡ 0` examples have no hypothesis left (`asGMcSeq_time_zero`, exact loop value `W^{-d}`; `t = 0` is in the paper's range `t ∈ [0, t_0]`, `3_5:15`). `t ≡ 1/16` examples discharge `Admissible`, bulk, `0 ≤ t < 1`, `RangeCond`, `c > 0`, the floor and `Ψ ≤ N^{-1/6}` at `sz0`; they keep `AsGMcSeq` (`ε₀ = 1/40`), `LoopDetSeq` and, where the target takes them, the pins FA/IBP (or their outputs) as hypotheses: other gates' inputs (S1-28..S1-30, the random hypotheses of the paper).

## (c) Verified Mathlib names used (`lake env lean scratchpad/T2108/used.lean`: `#check @name`, one line each, exit 0, 77 names). Names checked absent: none.
```
Complex.ofReal_zero : ↑0 = 0
ENNReal.ofReal : ℝ → ENNReal
@ENNReal.ofReal_add : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
@ENNReal.ofReal_lt_one : ∀ {p : ℝ}, ENNReal.ofReal p < 1 ↔ p < 1
@Finset.card_image_le : ∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {f : α → β} [inst : DecidableEq β], (Finset.image f s).card ≤ s.card
@Finset.card_le_card : ∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.card ≤ t.card
@Finset.card_le_three : ∀ {α : Type u_1} [inst : DecidableEq α] {a b c : α}, {a, b, c}.card ≤ 3
@Finset.card_univ : ∀ {α : Type u_1} [inst : Fintype α], Finset.univ.card = Fintype.card α
@Finset.le_sup : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {b : β}, b ∈ s → f b ≤ s.sup f
@Finset.le_sup' : ∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {s : Finset β} (f : β → α) {b : β} (h : b ∈ s), f b ≤ s.sup' ⋯ f
@Finset.lt_sup'_iff : ∀ {α : Type u_1} {ι : Type u_2} [inst : LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}, a < s.sup' H f ↔ ∃ b ∈ s, a < f b
@Finset.mem_filter : ∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
@Finset.mem_image : ∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {f : α → β} {s : Finset α} {b : β}, b ∈ Finset.image f s ↔ ∃ a ∈ s, f a = b
@Finset.mem_univ : ∀ {α : Type u_1} [inst : Fintype α] (x : α), x ∈ Finset.univ
@Finset.sum_const : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [inst : AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
@Finset.sum_const_zero : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [inst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
@Finset.sum_eq_single : ∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid M] {s : Finset ι} {f : ι → M} (a : ι), (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s → f a = 0) → ∑ x 
@Finset.sum_filter : ∀ {ι : Type u_1} {M : Type u_2} {s : Finset ι} [inst : AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p] (f : ι → M), ∑ a ∈ s with p a, f a 
@Finset.sum_le_sum : ∀ {ι : Type u_1} {N : Type u_2} [inst : AddCommMonoid N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι} [AddLeftMono N], (∀ i ∈ s, f i ≤ g i) → ∑
Fintype.card : (α : Type u_1) → [Fintype α] → ℕ
@Fintype.card_congr : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (f : α ≃ β), Fintype.card α = Fintype.card β
Fintype.card_fin : ∀ (n : ℕ), Fintype.card (Fin n) = n
@Fintype.card_piFinset : ∀ {ι : Type u_1} {α : ι → Type u_2} [inst : DecidableEq ι] [inst_1 : Fintype ι] (s : (i : ι) → Finset (α i)), (Fintype.piFinset s).card = ∏ i, (s
Fintype.card_prod : ∀ (α : Type u_1) (β : Type u_2) [inst : Fintype α] [inst_1 : Fintype β], Fintype.card (α × β) = Fintype.card α * Fintype.card β
Fintype.card_unit : Fintype.card Unit = 1
@Fintype.mem_piFinset : ∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {δ : α → Type u_2} {t : (a : α) → Finset (δ a)} {f : (a : α) → δ a}, f ∈ Fintype.piFi
@Fintype.piFinset : {α : Type u_1} → [DecidableEq α] → [Fintype α] → {δ : α → Type u_2} → ((a : α) → Finset (δ a)) → Finset ((a : α) → δ a)
@Matrix.isHermitian_zero : ∀ {α : Type u_1} {n : Type u_2} [inst : AddMonoid α] [inst_1 : StarAddMonoid α], Matrix.IsHermitian 0
@Matrix.one_apply_eq : ∀ {n : Type u_2} {α : Type u_1} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] (i : n), 1 i i = 1
@Matrix.one_apply_ne : ∀ {n : Type u_2} {α : Type u_1} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] {i j : n}, i ≠ j → 1 i j = 0
@Matrix.smul_apply : ∀ {m : Type u_3} {n : Type u_4} {α : Type u_1} {β : Type u_2} [inst : SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n), (r • A) i j = r • A i j
@Nat.cast_nonneg : ∀ {α : Type u_1} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] (n : ℕ), 0 ≤ ↑n
@Nat.cast_sub : ∀ {R : Type u_1} [inst : AddGroupWithOne R] {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
@Nat.le_mul_of_pos_left : ∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
@Nat.le_one_iff_eq_zero_or_eq_one : ∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
@Nat.mul_le_mul : ∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * m₂
@Nat.one_le_iff_ne_zero : ∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
@Nat.pos_of_ne_zero : ∀ {n : ℕ}, n ≠ 0 → 0 < n
@Nat.pow_le_pow_left : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
@Real.pow_rpow_inv_natCast : ∀ {x : ℝ} {n : ℕ}, 0 ≤ x → n ≠ 0 → (x ^ n) ^ (↑n)⁻¹ = x
@Real.rpow_add : ∀ {x : ℝ}, 0 < x → ∀ (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
@Real.rpow_add' : ∀ {x y z : ℝ}, 0 ≤ x → y + z ≠ 0 → x ^ (y + z) = x ^ y * x ^ z
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
@Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_mul : ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
Real.rpow_natCast : ∀ (x : ℝ) (n : ℕ), x ^ ↑n = x ^ n
@Real.rpow_neg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), x ^ (-y) = (x ^ y)⁻¹
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
@Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y
@Real.rpow_pos_of_pos : ∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 0 < x ^ y
Real.sqrt : ℝ → ℝ
@Real.sqrt_le_sqrt : ∀ {x y : ℝ}, x ≤ y → √x ≤ √y
@Real.sqrt_pos : ∀ {x : ℝ}, 0 < √x ↔ 0 < x
@Real.sqrt_sq : ∀ {x : ℝ}, 0 ≤ x → √(x ^ 2) = x
@Set.union_compl_self : ∀ {α : Type u_1} (s : Set α), s ∪ sᶜ = Set.univ
@Set.univ : {α : Type u_1} → Set α
ZMod.card : ∀ (n : ℕ) [inst : Fintype (ZMod n)], Fintype.card (ZMod n) = n
@ZMod.natCast_zmod_val : ∀ {n : ℕ} [NeZero n] (a : ZMod n), ↑a.val = a
@ZMod.val_lt : ∀ {n : ℕ} [NeZero n] (a : ZMod n), a.val < n
@inv_anti₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < b → b ≤ a → a⁻¹ ≤ b⁻¹
@inv_le_comm₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b : G₀}, 0 < a → 0 < b → (a⁻¹ ≤ b ↔ b⁻
@one_le_pow₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀], 1 ≤ a → ∀ {n : ℕ}, 1 ≤ a ^ n
@pow_le_pow_left₀ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^
@tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
@MeasureTheory.measure_mono : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F} {s t : Set α}, s ⊆ t → μ s 
@MeasureTheory.measure_union_le : ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] [MeasureTheory.OuterMeasureClass F α] {μ : F} (s t : Set α), μ (s ∪ t
@MeasureTheory.measure_univ : ∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabilityMeasure μ], μ Set.univ = 1
@le_max_left : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max a b
@le_max_right : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max a b
@max_le : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤ c → max a b ≤ c
@max_eq_left : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → max a b = a
@max_eq_right : ∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b → max a b = b
@mul_le_mul_of_nonneg_left : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α], b ≤ c → 0 ≤ a → a * b ≤ a * c
@mul_le_mul_of_nonneg_right : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α], b ≤ c → 0 ≤ a → b * a ≤ c * a
@div_le_div_of_nonneg_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}, a ≤ b → 0 ≤ c → a / c ≤ b / c
@inv_mul_cancel₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a⁻¹ * a = 1
```

## (d) Open issues and paper-delta candidates
1. **T2108a (needs sign-off; ST1-COMMON item 6 says stop if a statement changes beyond renaming and exponents).** Floor `W^{-d/2} ≤ Ψ` (paper `3_5:27`) in `LocalLawDetThm d`, `FixedTimeFAThm d`, `IBPDetThm d`, `GavLDetFloorThm d` instead of RBM2D's `W⁻¹ ≤ Ψ`; `LoopFloorThm d` concludes `(W^d)⁻¹ ≤ 4 N^ε Ψ²` instead of `(W⁻¹)² ≤ 4 N^ε Ψ²`. I took this as the exponent recount (R3 and CLAUDE.md §5.2) because the literal statement is compiled false at `d = 3` (b.2; file line 1207). The pins `FixedTimeFAThm d`, `IBPDetThm d`, defined here and proved later (S1-28..S1-30), now carry the weaker hypothesis `W^{-d/2} ≤ Ψ` (the paper's); whether RBM2D's proofs of FA and IBP use `W⁻¹ ≤ Ψ` beyond the `d = 2` coincidence was not checked here.
2. **Ticket text.** The ticket's near-set count `2d + 1` and the `(2d+1)^2` constant are for the `zdistD` ball; the merged `gexRHS` uses `zdistInf`, so the counts are `3^d` and `9^d` (b.8 item 3). Ticket-text correction for the dispatcher.
3. **Registry.** `FixedTimeFAThm`, `IBPDetThm` are classed owed (results the paper proves and this ticket takes as `Prop` pins; proved by S1-29/S1-30 per portmap rows 37, 45, 47, 52). If the dispatcher prefers `structuralProps`, only `RBM3D/Test/Axioms.lean` changes.
4. **Certificates.** `FixedTimeFAThm`, `IBPDetThm`: pre-check says `[no certificate]` (b.1). The `t ≡ 1/16` examples keep `AsGMcSeq` (`ε₀ = 1/40`), `LoopDetSeq` as hypotheses (satisfiability not claimed here; limit check in (a), last paragraph of (ii)); the `t ≡ 0` examples need none.
5. **Paper-delta candidates:** T2108a (item 1). No other Lean/paper statement difference: the other residuals of b.4 are `hd`, the `d` binder of the pins and the constants `9^d` (a derived bound, not a paper statement); `Admissible` for `SizeTendsto → Bandwidth` and `hd : 3 ≤ d` are cited signed entries (D39, D201).
