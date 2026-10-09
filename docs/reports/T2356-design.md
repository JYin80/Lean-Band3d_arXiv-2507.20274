# T2356 (UN-47 Eq729B) stage 1a design: statements, exponent chain, bridge, twins, tokens, sizes

Prover `claude-sonnet-5-5` (prover-max, stage 1a only, CONTROL H146; `Eq729B.lean` not written). Branch `t/T2356` (base `5869c29`), probe `RBM3D/Probe/T2356Pins.lean` (398 lines, limit 400), final commit `fe9888f`; the probe stays on the branch, never merged. Last edit: Fri Oct  9 02:10:06 UTC 2026.
Citations: `path.lean:N` is relative to `RBM3D/` at the base of the branch (echo in section 8); `RBM2D:N` is `RBM2D/Universality/GUEPhase/Eq729B.lean:N` at `9e0f275`; `probe N` is line N of the probe; `(a) row k` is row k of the exponent table in `docs/reports/T2356-prove.md`; `T:N` is line N of `docs/tickets/T2356.md`; `1_2:N` is `paper/tex/1_2_Intro_model_result.tex:N`.
Evidence: build, axioms, statements, instances, name-clash in `docs/reports/T2356-prove.md` (b); scripts and their output in sections 4-6 and 8.

## 0. The answer

| item | answer | where |
|---|---|---|
| 1 statements | Three Prop pins and the bridge compile (probe 85-125). Target 1 `gueGrid_eq729` = `RBM2D:531` under the port map plus `hlam`, `hell`/`hKb`/`hKinit` as the merged `Hyp_Kt_detDom` (`Universality/GUEPhase/HypA.lean:690`, T2352a), `hB := STExp2`, conclusion `N^δ((Nη_{t₀})^{-3} + I₀(t₁))`. Target 2: `H729` gives the body of `UNOUEq747`, no `hell`. Target 3: the same from the inputs, `h730 hscale hell hlam hKb` derived; its conclusion is the body of `UNOUEq747` (`ueq747_iff` by `Iff.rfl`, probe 75); `pin3_of_pins` (probe 384) composes targets 1 and 2 with the derived inputs into target 3. | 1 |
| 2 chain | Every link is true and is a merged lemma or one of 9 compiled real-variable lemmas of the probe (standard axioms) and is evaluated at `d = 3, 4` (B1): (i) `eq729_one_step` + Grönwall (`Eq729B_perN`, port; `gronwall_factor`, probe 364) + `gueGrid_expect_oneLoop`; (ii) `Eq729B_arith` verbatim + `final_729`; (iii) `bctl_le_two_calB`, `assembly_747`: `t₀N^{δ'}(Λ³ + I₀) ≤ 12N^{δ'}𝓑²(X + 𝓑) ≤ W^τ𝓑²(X + 𝓑)`. | 2, 8 |
| 3 bridge | No new pin: `bridge : PinSTExp2OfUNMLOut` and `goodFlow : PinGoodFlow` are PROVED in the probe (probe 132-187). Of the five conclusions of `UNMLOut` only `STExp2` is consumed. | 3 |
| 4 MISS list | 28 names: 18 twins (file:line), 8 not needed under the new pins, 2 re-derived (`Gres_conjTranspose` 12 lines; `trGEGEmat` as `avg2 = loopL`, 40-60 lines). | 4 |
| 5 tokens | 16 token classes; 48 lines with a dimension-specific `^ 2` (`N = W²L²`, `hell`, `η_Q ≤ L^{-2}`, `Meta`), none survives; `N ≥ 3^d ≥ 27`. | 5 |
| 6 sizes | lo / central / hi **1355 / 1687 / 2265** (ticket 1400 / 1750 / 2200); one row; the cut at `:784` is A (7.29) 658 / 778 / 984 and B (7.47) + bridge 697 / 909 / 1281. | 6 |

**Verdict: PASS.** No FAIL trigger: no link of (2) is false or unprovable from merged lemmas, and (3) needs no new pin. Findings that change earlier readings:
* **F1 (`hell`).** `Bctl(t₁) ≤ 2𝓑_{η_Q,0}` needs only `η_Q ≤ 2(1 - t₁)` (`zRange`, `Main/ZTransfer.lean:79`) and no `hell` (`bctl_le_two_calB`, probe 192). `hell` (`L^d(1 - t₁) ≤ ilambda²`) is needed only by the K̃ bounds of target 1 through `Hyp_Kt_detDom`; target 3 derives it from `τ_U ≤ ouTauMax 𝔠 𝔡` (`hell_of_scales`, probe 238). (a) row (i) says "iff `hell`".
* **F2 (good data).** `E', t₀, t₁` are formulas in `z_n = E_n + iη_Q(n)`. `Sizes.lam : ℕ → ℝ` has no positivity field and `(eq:WO)` is eventual (`Defs/Sizes.lean:138-146`, `:164`), so at finitely many `n` `Im z_n ≤ 0`, where `msc` is a root branch (`Defs/Semicircle.lean:116`; B3: at `z = -i` the roots are `1.618i` and `-0.618i`, `lemT = 2.618 ≥ 1`). The `∀ n` facts `|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` of RBM2D (`Eq729B_pw`, `RBM2D:1139`) and of `Hyp_Kt_detDom` are false there (DECISIONS §29 (4)). Fix: `FlowData` holds eventually; `goodFlow` (probe 177, proved) gives data with those facts for every `n`; targets 1 and 3 keep the `∀ n` hypotheses; the consumer builds `Kt`, `hP` for the good data once.
* **F3 (loss form).** (7.29) carries `I₀(t₁)`: the target of `STExp2` is not of the form `Λ³` (the factor `(ilambda²W^d)^{-1/5}`). The paper's remark (commented out, `1_2:596`) has `(Nη)^{-3}` only for `η = N^{-1+2τ_U}`; `UNOUEq747` is at `η_Q`.
* **F4 (savings).** `Eq729B_Kt_one`, `_initial`, `_K_bounds` (131 source code lines) are the merged `Hyp_Kt_one`, `Hyp_Kt_detDom`; `Eq729B_arith` (119) is `N`-only; `gueGrid_loop_duhamel` (`Universality/GUEPhase/DuhamelC.lean:1485`, in the ticket's import list) is not used: RBM2D `Eq729B.lean` mentions "Duhamel" in one docstring line and its consumer is RBM2D `PathBounds.lean` (B2 in section 8).

## 1. Item 1: the statements (source ↦ RBM3D; probe 42-125, all compiled)

**Target 1 `gueGrid_eq729`** (`RBM2D:531-553` ↦ probe 85-98; conclusion `Eq729Concl` probe 53, `eqErr` probe 46)
| RBM2D | RBM3D |
|---|---|
| `(d : Sizes)` | `{d} (sz : Sizes d)`, `3 ≤ d` (new: `gueGrid_expect_oneLoop`, `Universality/GUEPhase/OneLoop.lean:1308`) |
| `hκ hτU n0 hn0`, `hsize`, `hE ht1 ht10 ht0` | same (`∀ n`; `Tendsto sz.size atTop atTop`) |
| none | `hlam : ∀ᶠ n, 0 < lam n ∧ lam n ≤ Λ` (new, `Universality/GUEPhase/OneLoop.lean:1308`; target 3 takes it from `(eq:WO)`) |
| `h730`, `hscale` | same with `Nsz sz n`, `etaT`, `gueScale sz E n (t0 n)` (`Universality/GUEPhase/Grid.lean:84`) |
| `hell : (d.L n)² (1 - t1 n) ≤ 1` | `L^d (1 - t₁) ≤ lam²`, as `Hyp_Kt_detDom` (`Universality/GUEPhase/HypA.lean:690`, T2352a) |
| none (`Kbound_prec_uncond` inside the source proof) | `hKb : sz.STKbound E` (`Induction/Defs.lean:174`; target 3 discharges it by `stKbound_holds`, `Loop/KLFinal.lean:243`) |
| `Kt`, `hKinit : Kt n t₁ I = KLoop.Kcal …` | `hKinit` on `loopOf σ a` with `sz.STKloop` (`Induction/Defs.lean:64`; T2352a) |
| `hK`, `hK2` | same with `primRhsGUE d …`, `kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) …` (`Universality/GUEPhase/KPrim.lean:68`) |
| `hB : MLExpConcl d E t1` (`N^ε scaleM^{-3}`) | `sz.STExp2 E t1` (`Induction/Defs.lean:159`) |
| `hP : GUEPathBounds d E t1 t0 (gueGridK d n0) n0 Kt` | `GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt` (`Universality/GUEPhase/Grid.lean:89`) |
| `≤ N^δ (gueScale)⁻¹ ^ 3` | `≤ N^δ ((gueScale)⁻¹ ^ 3 + initTerm sz n (t1 n))`, `initTerm` = the right side of `STExp2` (probe 42) |

**Target 2 `Eq729B_eq747_of_eq729`** (`RBM2D:1041-1058` ↦ probe 102-105)
| RBM2D | RBM3D |
|---|---|
| `(d) (h𝔠) (hA : Admissible 𝔠 d)` | `sz`, `3 ≤ d`, `hA : sz.Admissible 𝔠 𝔡` (`Defs/Sizes.lean:177`; `h𝔠 = hA.1`) |
| `hκ hE`, `ht : 0 ≤ t n`, `K`, `hK : K n ≠ 0` | same |
| `hE' ht0 ht1`, `z_n = E_n + iη_Q`, `η_Q = W^{2/3}/N` | `FlowData` (probe 36), eventually; `η_Q = ouEtaQ sz 𝔡 n = W^{-𝔡/3} ilambda W^{d/2}/N` (`Universality/ZeroModeProfile.lean:84`) |
| `H729` (`N^δ Λ³`) | `Eq729Concl sz E' t1 t0 K` (loss form with `initTerm`) |
| `‖𝔼 trGEGEmat … - profileTilde‖ ≤ W^δ Meta^{-3}` | `OUBody` (probe 58): `avg2` (`Endpoints.lean:75`) of `‖G_xy‖²` and `G_xy G_yx` against `profPMTilde`/`profPPTilde` at `ζ(t_n)` (`Universality/ZeroModeProfile.lean:88-93`), bound `qdBoundExp sz n τ η_Q` (`Endpoints.lean:101`), every `τ > 0` |

**Target 3 `Eq729B_eq747_of_inputs`** (`RBM2D:1384-1407` ↦ probe 109-119)
| RBM2D | RBM3D |
|---|---|
| `hA`, `hτUm : τ_U ≤ ouTauMax 𝔠` | `hA : sz.Admissible 𝔠 𝔡`, `τ_U ≤ ouTauMax 𝔠 𝔡` (`Universality/ZeroModeProfile.lean:78`) |
| `ht : 0 ≤ t n ∧ t n ≤ ouTStar d τ_U n` | `ouTStar sz τ_U n` (`Universality/Pins.lean:142`) |
| `hKinit hK hK2 hB hP` as target 1 at `E'` | same, `sz.STExp2 E' t1`; plus `hgood : ∀ n, abs E' ≤ 2 - κ ∧ 0 ≤ t₁ ≤ t₀ < 1` (F2; RBM2D derives it, `Eq729B_pw`) |
| derived `h730 hscale hell`, `Tendsto size` | derived (eventually) and `hlam`, `hKb` (`PinDerived`, `pin3_of_pins`, probe 376-384) |
| conclusion as target 2 | the body of `UNOUEq747 sz 𝔡 τ_U` (`Universality/ZeroModeProfile.lean:107`), `ueq747_iff` probe 75 |

**Bridge** `PinSTExp2OfUNMLOut` (probe 123) and **good data** `PinGoodFlow` (probe 128): section 3.

## 2. Item 2: the exponent chain (probe lemmas 192-371; numbers: section 8; constants `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `τ_U = ouTauMax = 1/720`)

**(i) The propagated initial term.** `STExp2 sz E' t₁` is `‖𝔼𝓛₂ - 𝒦₂‖(t₁) ≺ I₀(t₁) = 𝓑(t₁)²((ilambda²W^d)^{-1/5} + 𝓑(t₁))`, `𝓑 = sz.Bctl n t₁` (`Induction/Defs.lean:159`, `1_2:1281`); its left side is deterministic, so `det_of_prec` (`Endpoints.lean:443`) makes it `≤ N^τ I₀(t₁)` eventually for every `τ > 0`. With `hKinit`, `map_gueH_zero` (`Universality/GUEPhase/Grid.lean:542`) and `loopM_eq_loopL` (`Loop/GLoopFlow.lean:127`) it is the initial error `e₀ = eq729e … 0` (RBM2D `Eq729B_transfer`, `RBM2D:330`). Evolution from `t₁` to `t₀`: `eq729_one_step` (`Universality/GUEPhase/Eq729A.lean:731`), `‖e_{k+1}‖ ≤ (1 + Δ·2NρΛ)‖e_k‖ + eq729c(N,ρ,Λ,p,Δ)`, closed by the discrete Grönwall of `Eq729B_perN` (`RBM2D:75-146`, port) to `‖e_K‖ ≤ exp((t₀ - t₁)·2NρΛ)(B₀ + K·eq729c)`; the factor is `≤ e² < 7.4` (`gronwall_factor`, probe 364) since `(t₀ - t₁)NΛ = (t₀ - t₁)/η_{t₀} ≤ N^{-τ_U}` (`h730`) and `ρN^{-τ_U} ≤ 1` (`τ ≤ τ_U`): exponent 0.81 (`d = 3`) and 0.14 (`d = 4`) at `n = 0` ((a) row "Grönwall"). `gueGrid_expect_oneLoop` (`Universality/GUEPhase/OneLoop.lean:1308`) gives the 1-loop input `hX`; `gueGrid_loop_duhamel` is **not** used (F4). The K̃ bounds `‖K̃₂‖ ≤ ρΛ`, `‖K̃₃‖ ≤ ρΛ²` on `[t₁, t₀]` are `Hyp_Kt_detDom` (`Universality/GUEPhase/HypA.lean:690`), which needs `hell`.
**(ii) The GUE-phase terms.** `K·eq729c ≤ 40ρ²Λ³N^{-τ_U} + 10⁴N^{-70}` ((a) row "(ii)", `K = (N+1)^{160}`); `Eq729B_arith` (`RBM2D:368-494`, 119 lines, `N`-only, needs `9 ≤ N`: `N ≥ 3^d ≥ 27`) gives `exp(E₀·2NρΛ)(ρΛ³ + Kc) ≤ 56ρΛ³`; with `B₀ = N^τ I₀` instead of `ρΛ³`, `final_729` (probe 359) gives `≤ 56ρ(Λ³ + I₀)`, `ρ = N^τ`, `τ = min(δ/4, τ_U)`: (7.29) is `‖e_K‖ ≤ N^δ(Λ³ + I₀(t₁))`.
**(iii) After the (7.47) step.** (7.26) (`map_gueH_last`, `Universality/GUEPhase/Grid.lean:559`; `GUEPhaseGrid_gloop_two_smul_lemT_eq`, `Universality/GUEPhase/Grid.lean:772`) gives `𝔼 tr(…) = t₀ 𝔼𝓛`; `η_{t₀} = √t₀ η_Q` (`zt_im_lemma28`, `Defs/Semicircle.lean:344`) and `t₀ ≥ 1/16` (`lemma28_quant`, `Defs/Semicircle.lean:359`) give `t₀(Nη_{t₀})^{-3} ≤ 4(Nη_Q)^{-3}`; `(Nη_Q)^{-1} ≤ 𝓑 := calB sz n η_Q 0` (the first term of `calB` is `≥ 0`); `Bctl(t₁) ≤ 2𝓑` (F1); `qdBoundExp = W^τ𝓑²(X + 𝓑)` with the `X` of `initTerm` (`qdBoundExp_eq`, probe 322: the exponents `-(1:ℝ)/5` and `-(1/5:ℝ)` agree). `assembly_747` (probe 328): `t₀ N^{δ'}(Λ³ + I₀) ≤ 12 N^{δ'}𝓑²(X + 𝓑)`; `12 N^{δ'} ≤ W^τ` for `δ' = 𝔠τ/2` by `size_rpow_le_W_rpow` (`Defs/Sizes.lean:237`) and `W → ∞` (`Green/LDE.lean:444`). `calB_le_two_inv` (`Main/QUEFromQDiff.lean:166`, `Nη_Q 𝓑 ≤ 2`) is not needed: the bound has `𝓑`, not `(Nη)⁻¹`.
**The inputs of target 1 at `(E', t₁, t₀)`** (RBM2D `Eq729B_good_pw`, `RBM2D:1207`, 125 lines, redone with the new `η_Q`): `claimA` (probe 279) `4N^{2τ_U} ≤ Nη_Q` for `τ_U ≤ 𝔠𝔡/12`, `W ≥ N^𝔠`, `W^{𝔡/2} ≥ 4`; `h730_hscale_real` (probe 305): `h730` and `hscale` from it and `η_{t₀} ≥ η_Q/4`; `hell_of_scales` (probe 238) with `Ld_mul_etaQ` (probe 215, `L^d η_Q W^{4𝔡/3} = ilambda W^{-d/2+𝔡}`): `L^d(1 - t₁) ≤ ilambda²` from `1 - t₀ ≤ η_Q/c`, `c = √(κ(4-κ))/8` (`zRange`, `im_msc_ge`, `Main/ZTransfer.lean:79,130`), `ζ ≤ N^{-1+τ_U}` (`ZeroModeProfile_ouZeta_le`, `Universality/ZeroModeProfile.lean:151`), `ilambda ≥ W^{-d/2+𝔡}`, `2/c ≤ W^{4𝔡/3}`, `2N^{τ_U} ≤ W^{2𝔡}`. The thresholds are `W`-only: `W ≥ (2/c)^{15/2} ≈ 4·10^{10}` for `2/c ≤ W^{4𝔡/3}` and `W ≥ 4^{20} ≈ 1.1·10^{12}` for `W^{𝔡/2} ≥ 4` (both hold from `n = 2^7 - 1` in the scan), `n ≥ 1` for `2N^{τ_U} ≤ W^{2𝔡}` (B1); slacks as (a) rows `h730` 1/120, `hscale` 7/720, `hell` 23/720.
**Evaluation at `d = 3, 4`**: B1 evaluates the hypotheses `H` and the conclusion `C` of the probe lemmas at `n ∈ {0, 10, 2100, 10⁶}`: no violation of `H ⇒ C`; the lemmas with `W`-only thresholds have `H` false at small `n` (not a defect: `H` is a sufficient condition, e.g. `hell` itself holds at `n = 0`, `L^d(1 - t₁)/ilambda² = 0.45` (`d = 3`) and `0.06` (`d = 4`)). The loss `W^τ` at `τ = 1/100` absorbs the constant 12 only for `W ≥ 10^{216}`: inherent in `∀ᶠ n` with arbitrary `τ`; the nonempty instances of 1b discharge the hypotheses, never the conclusion at a fixed `n` ((a) (ii)).

## 3. Item 3: `STExp2 sz E' t₁` from `UNMLOut` (probe 123-187: statement, `goodFlow_aux`, `goodFlow`, `bridge`, all proved)

`UNMLOut d` (`Universality/Pins.lean:432`): `∀ κ ε 𝔡 𝔠 sz z, STFlow sz κ ε 𝔠 𝔡 z → ∀ t, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → STLK ∧ STLmax ∧ STDecay ∧ STExp2 ∧ STLocalEntry` at `(STflowE z, t)`; `STFlow sz κ ε 𝔠 𝔡 z = sz.Admissible 𝔠 𝔡 ∧ ∀ n, sz.locDomain κ ε n (z n)` (`Induction/Defs.lean:286`; `STflowE z n = lemE (z n)`, `:283`). Taking `z_n = E_n + iη_Q(n)` and `t = t₁ = (1 - ζ(t_n)) lemT z_n ≤ lemT z_n` (`ζ ≥ 0`), `E' = lemE z_n = STflowE z`. One line per field:
| field (`Induction/Defs.lean`) | consumed by Eq729B? |
|---|---|
| `STLK` (:104) | no: Eq729B uses no pathwise loop bound at `t₁` except through `hP : GUEPathBounds` (`lk`, `localLaw`, `Universality/GUEPhase/Grid.lean:89-102`), a pin of UN-49/50/51 |
| `STLmax` | no: the K̃ size bounds come from `hKb` and `Hyp_Kt_detDom`, not from `𝓛` |
| `STDecay` | no: no spatial decay in `|a₁ - a₂|` enters (7.29) or (7.47) |
| `STExp2` (:159) | **yes**: `hB := sz.STExp2 E' t₁` (targets 1 and 3), the initial term |
| `STLocalEntry` | no: the entrywise `G` bound at the grid times is `hP.localLaw` |
The one gap is `∀ n, locDomain κ ε n (z n)`: `queDomain` (`Main/QUEFromQDiff.lean:91`, `ε₀ = 𝔡/3`, `ε = 𝔠(𝔡 - 𝔡/3)`) gives it only eventually (`η_Q ≤ 1` and `η_Q ≥ N^{-1+ε}` need `W` large). `goodFlow_aux` (probe 148): with `ε = min(𝔠(𝔡 - 𝔡/3), 1)` keep `z_n` where `z_n ∈ 𝐃_{κ,ε}` and put a fixed point of `𝐃_{κ,ε}` elsewhere (`locDomain_nonempty`, `Endpoints.lean:486`: `κ ≤ 2`, `ε ≤ 1`); `STFlow` holds at every `n`, `FlowData` eventually, and `|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1` for every `n` (`lemma28_quant`, `lemT_lt_one`, `Defs/Semicircle.lean:209`). `STExp2` is `∀ τ D ∀ᶠ n`, so `STExp2_congr` (probe 135) transfers it to any `(E', t₁)` equal to the formulas eventually (`FlowData.ev_eq`, probe 141). No pin is added.

## 4. Item 4: RBM2D names not found by name in RBM3D (script `twins.py`: each twin resolved by grep to its declaration line)

`KLoop.Kcal` → `STKloop` (`Induction/Defs.lean:64`) | `KLoop.Kgen / Kcal of a 1-loop` → `KLK_one` (`Loop/KLTree.lean:206`)
`KLoop.mSig` → `mSigma` (`Defs/Semicircle.lean:85`) | `KLoop.Kbound_prec_uncond` → `STKbound` (`Induction/Defs.lean:174`)
`KLoop.Kbound_prec_uncond (proof)` → `stKbound_holds` (`Loop/KLFinal.lean:243`) | `RBM.Evol.MLExpConcl` → `STExp2` (`Induction/Defs.lean:159`)
`RBM.Evol.expLoopErr` → `STExpErr` (`Induction/Step6Pins.lean:45`) | `KLoop.Mt / scaleM / kloop_Mt_eq` → `Bctl` (`Defs/Sizes.lean:214`)
`Meta (def_meta)` → `calB` (`Endpoints.lean:58`) | `RBM.Endpoints.ZRescale_lemT_pos` → `lemT_pos` (`Defs/Semicircle.lean:204`)
`zztE_quant` → `lemma28_quant` (`Defs/Semicircle.lean:359`) | `eq_inv_sqrt_mul_spectralZ` → `eq_inv_sqrt_mul_zt` (`Defs/Semicircle.lean:270`)
`mSC / mSC_eq_msc` → `msc` (`Defs/Semicircle.lean:116`) | `spectralM / spectralZ` → `zt` (`Defs/Semicircle.lean:179`)
`Z-rescale one_sub bound (Eq729B_one_sub_lemT_le)` → `zRange` (`Main/ZTransfer.lean:79`) | `... Im m lower bound` → `im_msc_ge` (`Main/ZTransfer.lean:130`)
`GoodEvent_measurable_gloop` → `walk_measurable_loopL` (`Path/Walk.lean:780`) | `GoodEvent_measurable_gloop (matrix part)` → `walk_measurable_blockMat` (`Path/Walk.lean:788`)
`GoodEvent_gridTime_zero` → `gridTime` (`Path/Walk.lean:70`) | `ZRescale_blockMat_mul / _gsig_block / _trace_block / gloop_two` → `Gres_blockMat'` (`Main/ZTransfer.lean:253`)
`... gloop_two (tr(G E G E))` → `trace_four` (`Main/ZTransfer.lean:269`) | `... one-loop trace` → `trace_two` (`Main/ZTransfer.lean:319`)
`Gsig_conjTranspose` → `Gres_conjTranspose'` (`Main/ZTransfer.lean:344`) | `trGEGEmat / profileTilde` → `profPMTilde` (`Universality/ZeroModeProfile.lean:88`)
`... profile bridge` → `lemT_mul_kTwoGUE_pm_eq_profPMTilde` (`Universality/GUEPhase/KPrim.lean:275`) | `Eq729B_Kt_one (K~ on 1-loops)` → `Hyp_Kt_one` (`Universality/GUEPhase/HypA.lean:712`)
`Eq729B_initial + Eq729B_K_bounds (7.36)` → `Hyp_Kt_detDom` (`Universality/GUEPhase/HypA.lean:690`) | `Eq729B_perN: one step` → `eq729_one_step` (`Universality/GUEPhase/Eq729A.lean:731`)
`Lemma 5.15` → `gueGrid_expect_oneLoop` (`Universality/GUEPhase/OneLoop.lean:1308`) | `(7.26) law at the last step` → `map_gueH_last` (`Universality/GUEPhase/Grid.lean:559`)
`(7.25) law at step 0` → `map_gueH_zero` (`Universality/GUEPhase/Grid.lean:542`) | `homogeneity of the 2-loop` → `GUEPhaseGrid_gloop_two_smul_lemT_eq` (`Universality/GUEPhase/Grid.lean:772`)
`Lloop = loopL` → `loopM_eq_loopL` (`Loop/GLoopFlow.lean:127`) | `deterministic Prec -> pointwise` → `det_of_prec` (`Endpoints.lean:443`)
`eta_Q <= lam^2/L^d` → `etaQ_le` (`Main/QUEFromQDiff.lean:208`) | `eta_Q in the spectral domain` → `queDomain` (`Main/QUEFromQDiff.lean:91`)
`Bctl vs calB comparison` → `STWB_compare` (`Main/ZTransfer.lean:174`)
Fate of the 28 names of the MISS list (`T:7`):
* **18 twins**: `Kcal` `Kgen` `mSig` `Kbound_prec_uncond` `MLExpConcl` `expLoopErr` (inline body of `STExp2`; `STExpErr` is outside the closure) `mSC` `eq_inv_sqrt_mul_spectralZ` `zztE_quant` `GoodEvent_measurable_gloop` `GoodEvent_gridTime_zero` and `ZRescale_{lemT_pos, blockMat_mul, gsig_block, trace_block, blockMat_Epaper}` (`blockMat` is a `submatrix`, `Loop/GLoopFlow.lean:105`; `Gres_blockMat'`, `trace_two`, `trace_four`; RBM3D has `Eblk` only, no `Epaper`) `gloop_two` `profileTilde` (the rows above).
* **8 not needed**: `Mt` `Par` `kloop_Mt_eq` `scaleM` (the initial-data route through `Kbound_prec_uncond` is replaced by `hKb`, `hell` and `Hyp_Kt_detDom`), `Meta` `ellz` `ZRescale_rpow_neg_half` (only used for `Meta`), `Gsig_true` (RBM3D works with `Gres … true`).
* **2 re-derived**: `Gsig_conjTranspose` (RBM3D `Gres_conjTranspose'` is private, `Main/ZTransfer.lean:344`): 12 lines; `trGEGEmat` as `avg2 = loopL` for `Gres (ouMat …)`: the core `hcore` of `zTrace` (`Main/ZTransfer.lean:394`) with `trace_four`, `Gres_blockMat'` and the `(b, a)` order of the loops, 40-60 lines.
Also needed, outside the MISS list: `Eq729B_spectralZ_eq` (8 lines; the twin `GUEPhaseGrid_zt_eq`, `Universality/GUEPhase/Grid.lean:744`, is private), `kTwoGUE … a b = kTwoGUE … b a` from `Theta_transpose` (`Propagator/Basic.lean:104`; 10 lines, as `zProfile`, `Main/ZTransfer.lean:473`), `9 ≤ N` (8 lines).

## 5. Item 5: the `d = 2` token table (script `tokens.py` on `RBM2D/Universality/GUEPhase/Eq729B.lean`, 1419 lines)

| RBM2D token | lines / occ | first lines | RBM3D |
|---|---|---|---|
| `d : Sizes / d.L n / d.W n / d.size / d.W_pos / d.three_le_L` | 284 / 442 | [27,44,46,74,75] | sz : Sizes d, sz.L n, sz.W n, sz.size n, sz.W_pos, sz.three_le_L; `3 ≤ d` added |
| `Z2 L / Z2 (d.L n)` | 31 / 31 | [76,101,158,160,212] | Zd d L |
| `gloop L W (blockMat M) z` | 22 / 22 | [332,333,336,340,341] | loopL d L W (blockMat d L W M) z |
| `spectralZ / spectralM / spectralZ_eq` | 37 / 39 | [91,289,293,510,517] | zt E u / mE E / eq_inv_sqrt_mul_zt |
| `KLoop.mSig` | 14 / 15 | [45,94,164,546,552] | mSigma |
| `KLoop.Kcal / Kgen` | 9 / 10 | [45,159,173,229,235] | STKloop (hKinit on loopOf σ a) / KLK_one |
| `KLoop.Mt / Par / Kbound_prec_uncond / kloop_Mt_eq` | 8 / 8 | [222,234,236,238,242] | Bctl / none / STKbound (hKb) / none |
| `scaleM / Meta / ellz` | 25 / 26 | [36,45,255,717,718] | Bctl, calB (qdBoundExp); gueScale kept |
| `trGEGEmat / profileTilde` | 17 / 17 | [36,787,789,800,825] | avg2 of Gres (ouMat band) / profPMTilde, profPPTilde |
| `MLExpConcl / expLoopErr` | 9 / 9 | [29,44,530,547,704] | STExp2 / its body |
| `ouEtaQ d n (= W^{2/3}/N), (2:ℝ)/3 exponents` | 63 / 67 | [890,891,900,901,906] | ouEtaQ sz 𝔡 n = W^{-𝔡/3} ilambda W^{d/2}/N; exponents rewritten |
| `(d.L n : ℝ) ^ 2 (hell, η_Q ≤ L^{-2}) / (d.W n)^2 (d.L n)^2 (N)` | 45 / 55 | [227,269,537,896,906] | L^d (1-t1) ≤ lam^2; N = W^d L^d |
| `9 ≤ d.size n (N ≥ 9)` | 6 / 7 | [183,605,759,1167,1189] | 3^d ≤ (W L)^d, d ≥ 3: N ≥ 27 |
| `Admissible 𝔠 d / ouTauMax 𝔠 / ouTStar d / ouP,ouMat (d.L n)` | 27 / 29 | [39,825,826,835,840] | sz.Admissible 𝔠 𝔡; ouTauMax 𝔠 𝔡; ouTStar sz; ouP (UNModel.band sz) n; ouMat (UNModel.band sz) n |
| `Pgue d / gueH d / gueScale d / PathΩ d / GUEPathBounds d / gueGridK d` | 110 / 139 | [29,44,91,92,192] | same with sz (Grid.lean) |
| `Z-rescale lemmas (ZRescale_*, Gsig_*)` | 18 / 22 | [39,336,713,792,796] | see item (4) |
lines with a dimension-specific `^ 2`: 48
  N = (W L)^2: [189, 295, 304, 896] | hell: [227, 269, 537, 1217, 1348, 1363] | eta_Q <= L^-2 (:900-935): 11 lines | Meta (:936-970): [940, 951, 965, 966, 969] | good_pw hell part (:1225-1335): 22 lines
`N^δ`, the grid `K = (N+1)^{32n₀+64}` (`gueGridK`, `Universality/GUEPhase/Grid.lean:106`) and `eq729c` (`Universality/GUEPhase/Eq729A.lean:723`) are functions of `N` only and keep their form.

## 6. Item 6: sizes of stage 1b and the pre-named cut at `:784` (script `rows.py`, run Fri Oct  9 02:09:50 UTC 2026; bases are code lines from `decls.py`; port multiplier 1.05 central, 1.00 / 1.15 lo / hi (T2352: HypA 1010 → 1056 lines, `docs/reports/T2352-prove.md` (b) item 1); local changes 1.00 / 1.15 / 1.40; merged-twin glue, new code and instances absolute)
```
part A (source :1-783, (7.29))
  c_nonneg, perN, gueScale_{pos,anti,inv}, exp_two_lt, arith, Bad, not_bad (ports)                     base  231    231   243   266
  size_pos (merged one_le_size), nine_le_size (3^d >= 27)                                              base   14      8    14    22
  Kt_one, ofFn_getD, loopOf_eq, initial, K_bounds -> merged Hyp_Kt_one, Hyp_Kt_detDom (glue)           base  131     15    25    40
  transfer (+ Lloop = loopL, hKinit)                                                                   base   20     24    30    40
  gueGrid_eq729 (port; hinit from STExp2 by det_of_prec; final_729 step)                               base  240    240   276   336
  header, docstring, imports                                                                           base    0     50    60    80
  instances Eq729BInst for target 1 (as T2352 HypAInst: 300 lines for 13 targets)                      base    0     90   130   200
  total part A                                                                                                     658   778   984
part B (source :784-1419, (7.47) + bridge)
  real-variable lemmas written and compiled in the probe (reused as they are)                          base  160    160   160   192
  law726 (port)                                                                                        base   44     44    46    51
  avg2 = loopL for Gres (ouMat), (b,a) swap; Gres_conjTranspose copy; spectralZ_eq; kTwoGUE symmetry   base   41     56    82   124
  zRange / im_msc_ge glue (1-t0 >= eta/2, <= eta/c); Eq729B_pw                                         base   42     35    49    70
  target 2 body (law726 + loss + assembly glue; Meta lemmas deleted)                                   base  138     70   110   160
  h730 / hscale / hell instantiation of the lemmas (rpow facts), eta_Q facts                           base  214     95   145   220
  derived + target 3 body (hlam, hsz, hKb by stKbound_holds, UNOUEq747 packaging)                      base   67     60    90   135
  good data for every n + bridge UNMLOut -> STExp2 (probe: STExp2_congr, ev_eq, goodFlow_aux, goodFlow, bridge, proved) base   47     47    47    59
  header, docstring                                                                                    base    0     40    50    70
  instances Eq729BInst for targets 2, 3 and the bridge                                                 base    0     90   130   200
  total part B                                                                                                     697   909  1281
total (lo / central / hi): 1355 / 1687 / 2265   (ticket provisional 1400 / 1750 / 2200)
source code lines of all 41 declarations: 1182  probe reuse lines: 160  bridge lines: 47
```
Role `prover-max`. Ticket size 1400 / 1750 / 2200 (`T:13`); the estimate is 1355 / 1687 / 2265, central below the 1800 of the cut rule of `docs/reports/T2348-design.md:93`, so **one row**. **Pre-named cut (fallback)**: A = `Eq729B.lean` (`:1-783`: ports, `gueGrid_eq729`, instance of target 1; imports `Eq729A`, `OneLoop`, `KPrim`, `BootstrapAt`, `HypA`, `Endpoints`) | B = new file `Eq747.lean` (`:784-1419`: targets 2 and 3, `goodFlow`, `bridge`, instances; imports `Eq729B`, `ZeroModeProfile`, `Main/ZTransfer`, `Main/QUEFromQDiff`, `Loop/KLFinal`); the dispatcher names the second file. Stop line (binding, `T:13`): 2400 for the row (hi 2265); at the cut the dispatcher sets the stop lines of A (hi 984) and B (hi 1281). Instances as T2352 `HypAInst` (`Hyp_Kt_detDom` at `sz0`, `d = 3`, `n = 0`; `Kt` from `gueK_exists`, `Universality/GUEPhase/KPrim.lean:749`; `hKb` from `stKbound_holds`); `hB` and `hP` stay hypotheses of the examples (other gates' pins); the real lemmas (probe 192-371) bring their own examples.

## 7. Risks, paper-delta candidates, open questions (for the REQ)
* **Risk 1: consumer work for good data.** Targets 1 and 3 keep the `∀ n` hypotheses (as RBM2D and `Hyp_Kt_detDom`); the consumer must build `Kt` and `hP` for the good data of `goodFlow`; `gueK_exists` (`Universality/GUEPhase/KPrim.lean:749`) needs only `|E| < 2`, `0 ≤ t₁ ≤ t₀ < 1` and any `ilambda`.
* **Risk 2: import of `HypA`** (`Universality/GUEPhase/HypA.lean:6-9` imports `Proc`, `EntryTailMain`, `Loop/KBound`, `Loop/KLFinal`). Without it `Eq729B_Kt_one`, `_initial`, `_K_bounds` (131 source lines) must be re-derived with `hell`, `hKb`: +150 to +200 lines on A (central A ≈ 950).
* **Risk 3: no witness of the conclusion at fixed `n`**: the loss `W^τ` absorbs 12 only for `W ≥ 10^{216}` at `τ = 1/100` (B1); the instances discharge hypotheses, as `Eq729AInst` (`docs/reports/T2350-prove.md`) does.
* **Paper-delta candidates** (the dispatcher numbers them): `T2356a` (7.29) at `t₀` carries `I₀(t₁)` (F3; `RBM2D:531`, `1_2:1281`); `T2356b` (7.47): `W^δ Meta^{-3}` ↦ `W^τ𝓑²((ilambda²W^d)^{-1/5} + 𝓑)` at `η_Q = W^{-𝔡/3} ilambda W^{d/2}/N`, profile `Θ̃_{ζ(t_n)}` of the OU matrix (`1_2:504-512`, `UNOUEq747`); `T2356c` the `∀ n` facts replaced by `goodFlow` (F2, formal); `hell`, `hKb`, `hKinit` as T2352a.
* **Open questions**: (1) `∀ n` targets plus `goodFlow` for the consumer (this design) or eventual hypotheses with the reduction inside target 1 (+80 lines, a `GUEPathBounds` congruence); (2) `goodFlow` and `bridge` in `Eq729B.lean` (47 proved lines) or in UN-51; (3) import of `HypA`; (4) one row with the cut as fallback; (5) the block Anderson kind `UNOUEq747k` (`Universality/OUInterfaceK.lean:80`) needs its own target 3: this ticket is the band kind.

## 8. Script output
**B1** `python3 chain2.py` (8 of the 9 chain lemmas of the probe, `qdBoundExp_eq` being an identity of definitions, a script-only loss row, and the chain at the instance; hypotheses `H`, conclusion `C`; run Fri Oct  9 02:09:50 UTC 2026; `W`-only thresholds scanned at `n = 2^k - 1`)
```
constants: c=1/6 dd=1/10 kappa=1/10 c=sqrt(kappa(4-kappa))/8=0.0781 tauU=ouTauMax=1/720 tau=1/100
lemma                          d=3 n=0     d=3 n=10    d=3 n=2100  d=3 n=1e6   d=4 n=0     d=4 n=10    d=4 n=2100  d=4 n=1e6  
bctl_le_two_calB               H&C         H&C         H&C         H&C         H&C         H&C         H&C         H&C        
Ld_mul_etaQ                    H&C         H&C         H&C         H&C         H&C         H&C         H&C         H&C        
hell_of_scales                 H false     H false     H&C         H&C         H false     H false     H&C         H&C        
claimA                         H false     H false     H&C         H&C         H false     H false     H&C         H&C        
h730_hscale_real               H false     H&C         H&C         H&C         H&C         H&C         H&C         H&C        
assembly_747                   H false     H false     H false     H false     H false     H false     H false     H false    
loss_conv (script only)        H false     H false     H false     H false     H false     H false     H false     H false    
gronwall_factor                H&C         H&C         H&C         H&C         H&C         H&C         H&C         H&C        
final_729                      H&C         H&C         H&C         H&C         H&C         H&C         H&C         H&C        
violations of H => C: []
the same two rows for the loss tau = 1 (the target quantifies over every tau > 0; tau = 1/100 needs W^(tau/2) >= 12, W >= 1e216):
assembly_747 (tau=1)           H false     H&C         H&C         H&C         H false     H&C         H&C         H&C        
loss_conv (script only) (tau=1)H false     H&C         H&C         H&C         H false     H&C         H&C         H&C        
the chain at the instance n = 0 (tau = 0 in W^tau; constants of the Lean lemmas: Bctl(t1) <= 2 calB, I0 <= 8 Tgt, t0 Lam0^3 <= 4 Tgt, total <= 12 Tgt):
  d=3: eta_Q/(2(1-t1))=0.3478 (<=1 needed)  Bctl(t1)/calB=0.7677 (<=2)  I0/Tgt=0.5289 (<=8)  t0*Lam0^3/Tgt=0.1948 (<=4)  t0(Lam0^3+I0)/Tgt=0.7237 (<=12)  hell: L^d(1-t1)/lam^2=0.4529
  d=4: eta_Q/(2(1-t1))=0.4525 (<=1 needed)  Bctl(t1)/calB=0.9101 (<=2)  I0/Tgt=0.8146 (<=8)  t0*Lam0^3/Tgt=0.1558 (<=4)  t0(Lam0^3+I0)/Tgt=0.9705 (<=12)  hell: L^d(1-t1)/lam^2=0.0615
d=3, first scanned n = 2^k - 1 after which the hypothesis holds: Bandwidth N^c<=W k=0; WO W^(-d/2+dd)<=lam k=0; hell 2/c<=W^(4dd/3) k=7; hell 2N^tauU<=W^(2dd) k=1; claimA 4<=W^(dd/2) k=7; assembly 12<=W^(tau/2) k=143
d=4, first scanned n = 2^k - 1 after which the hypothesis holds: Bandwidth N^c<=W k=0; WO W^(-d/2+dd)<=lam k=0; hell 2/c<=W^(4dd/3) k=7; hell 2N^tauU<=W^(2dd) k=1; claimA 4<=W^(dd/2) k=7; assembly 12<=W^(tau/2) k=143
```
**B2** the Duhamel lemma is not used (item F4)
```
$ grep -c "duhamel\|Duhamel" RBM2D/Universality/GUEPhase/Eq729B.lean
1
$ grep -n "duhamel\|Duhamel" RBM2D/Universality/GUEPhase/Eq729B.lean | cut -c1-90
20:first half (the 2-loop algebra, Duhamel in expectation, one grid step of the recursion 
$ grep -ln "gueGrid_loop_duhamel" RBM2D/Universality/GUEPhase/*.lean
RBM2D/Universality/GUEPhase/DuhamelC.lean
RBM2D/Universality/GUEPhase/PathBounds.lean
```
**B3** the `msc` branch at `Im z ≤ 0` (finding F2): `python3 -I msc_check.py`
```
z = -i: roots of m^2 + z m + 1 = 0: [1.618034j, -0.618034j]  moduli: [1.618034, 0.618034]
the root with Im > 0 (what msc returns, Defs/Semicircle.lean:116): lemT = |m|^2 = 2.618034
```
**B4** echo of every citation of sections 0-7 (script `echo_cites.py design.md`, run Fri Oct  9 02:10:06 UTC 2026; per file the first 30 characters of each cited line, both ends of a range; `probe N` is the probe at commit `fe9888f`; `RBM2D` is `RBM2D/Universality/GUEPhase/Eq729B.lean` at `9e0f275`)
```
1_2: 504 «\begin{align}\label{Meq:QdS1}» | 512 «» | 596 «% $\tau=\mathfrak{c} / 3$ and » | 1281 «\be \label{Eq:Gtlp_exp+IND}»
Defs/Semicircle.lean: 85 «noncomputable def mSigma (E : » | 116 «noncomputable def msc (z : ℂ) » | 179 «noncomputable def zt (E t : ℝ)» | 204 «theorem lemT_pos : 0 < lemT z » | 209 «theorem lemT_lt_one : lemT z <» | 270 «theorem eq_inv_sqrt_mul_zt : z» | 344 «theorem zt_im_lemma28 : (zt (l» | 359 «theorem lemma28_quant {κ : ℝ} »
Defs/Sizes.lean: 138 «structure Sizes (d : ℕ) where» | 146 «W_pos : ∀ n, 0 < W n» | 177 «def Admissible (𝔠 𝔡 : ℝ) : Pro» | 214 «def Bctl (n : ℕ) (t : ℝ) : ℝ :» | 237 «theorem size_rpow_le_W_rpow {𝔠»
Endpoints.lean: 58 «def calB (sz : Sizes d) (n : ℕ» | 75 «def avg2 (sz : Sizes d) (n : ℕ» | 101 «def qdBoundExp (sz : Sizes d) » | 443 «theorem det_of_prec (hsz : sz.» | 486 «theorem locDomain_nonempty (sz»
Green/LDE.lean: 444 «theorem tendsto_W {d : ℕ} (sz »
Induction/Defs.lean: 64 «def STKloop (n : ℕ) (E τ : ℝ) » | 159 «def STExp2 (E τ : ℕ → ℝ) : Pro» | 174 «def STKbound (E : ℕ → ℝ) : Pro» | 286 «def STFlow {d : ℕ} (sz : Sizes»
Induction/Step6Pins.lean: 45 «def STExpErr (n : ℕ) (E u : ℝ)»
Loop/GLoopFlow.lean: 105 «def blockMat (M : Matrix (Idx » | 127 «theorem loopM_eq_loopL (H : Ma»
Loop/KLFinal.lean: 243 «theorem stKbound_holds (hd : 3»
Loop/KLTree.lean: 206 «theorem KLK_one (W : ℕ) (E t :»
Main/QUEFromQDiff.lean: 91 «theorem queDomain (sz : Sizes » | 166 «theorem calB_le_two_inv (sz : » | 208 «theorem etaQ_le (sz : Sizes d)»
Main/ZTransfer.lean: 79 «theorem zRange : MAZRange := b» | 130 «theorem im_msc_ge {κ : ℝ} (hκ » | 174 «theorem STWB_compare (sz : Siz» | 253 «theorem Gres_blockMat' {L W : » | 269 «theorem trace_four {L W : ℕ} [» | 319 «theorem trace_two {L W : ℕ} [N» | 344 «private theorem Gres_conjTrans» | 394 «theorem zTrace : MAZTrace := b» | 473 «theorem zProfile : MAZProfile »
Path/Walk.lean: 70 «def gridTime (s t : ℕ → ℝ) (K » | 780 «theorem walk_measurable_loopL » | 788 «theorem walk_measurable_blockM»
Propagator/Basic.lean: 104 «theorem Theta_transpose (hS : »
RBM2D: 75 «private theorem Eq729B_perN (d» | 146 «» | 330 «private theorem Eq729B_transfe» | 368 «private theorem Eq729B_arith {» | 494 «» | 531 «theorem gueGrid_eq729 (d : Siz» | 553 «((d.size n : ℕ) : ℝ) ^ δ * (gu» | 1041 «theorem Eq729B_eq747_of_eq729 » | 1058 «((E n : ℂ) + ((ouEtaQ d n : ℝ)» | 1139 «private theorem Eq729B_pw (d :» | 1207 «private theorem Eq729B_good_pw» | 1384 «theorem Eq729B_eq747_of_inputs» | 1407 «((E n : ℂ) + ((ouEtaQ d n : ℝ)»
T: 7 «**Stage 1a (design, report `do» | 13 «Role: `prover-max` (1a and 1b)»
Universality/GUEPhase/DuhamelC.lean: 1485 «theorem gueGrid_loop_duhamel {»
Universality/GUEPhase/Eq729A.lean: 723 «def eq729c (N ρ Λ p Δ : ℝ) : ℝ» | 731 «theorem eq729_one_step {d : ℕ}»
Universality/GUEPhase/Grid.lean: 84 «def gueScale (E : ℕ → ℝ) (n : » | 89 «structure GUEPathBounds (E t1 » | 102 «(fun n p _ => (gueScale sz E n» | 106 «def gueGridK (n0 n : ℕ) : ℕ :=» | 542 «theorem map_gueH_zero (t1 t0 :» | 559 «theorem map_gueH_last (t0 τ : » | 744 «private lemma GUEPhaseGrid_zt_» | 772 «theorem GUEPhaseGrid_gloop_two»
Universality/GUEPhase/HypA.lean: 6 «import RBM3D.Universality.GUEP» | 9 «import RBM3D.Loop.KLFinal» | 690 «theorem Hyp_Kt_detDom {κ τU : » | 712 «theorem Hyp_Kt_one {E t1 t0 : »
Universality/GUEPhase/KPrim.lean: 68 «def kTwoGUE (d L : ℕ) [NeZero » | 275 «theorem lemT_mul_kTwoGUE_pm_eq» | 749 «theorem gueK_exists (d L : ℕ) »
Universality/GUEPhase/OneLoop.lean: 1308 «theorem gueGrid_expect_oneLoop»
Universality/OUInterfaceK.lean: 80 «def UNOUEq747k {d : ℕ} (K : UN»
Universality/Pins.lean: 142 «def ouTStar (sz : Sizes d) (τU» | 432 «def UNMLOut (d : ℕ) : Prop :=»
Universality/ZeroModeProfile.lean: 78 «def ouTauMax (𝔠 𝔡 : ℝ) : ℝ := » | 84 «def ouEtaQ {d : ℕ} (sz : Sizes» | 88 «def profPMTilde {d : ℕ} (sz : » | 93 «def profPPTilde {d : ℕ} (sz : » | 107 «def UNOUEq747 {d : ℕ} (sz : Si» | 151 «theorem ZeroModeProfile_ouZeta»
probe: 36 «structure FlowData (sz : Sizes» | 42 «def initTerm (sz : Sizes d) (n» | 46 «def eqErr (sz : Sizes d) (E t1» | 53 «def Eq729Concl (sz : Sizes d) » | 58 «def OUBody (sz : Sizes d) (𝔡 :» | 75 «theorem ueq747_iff (sz : Sizes» | 85 «def PinGueGrid729 : Prop :=» | 98 «sz.STExp2 E t1 → GUEPathBounds» | 102 «def PinEq747OfEq729 : Prop :=» | 105 «∀ {K : ℕ → ℕ}, (∀ n, K n ≠ 0) » | 109 «def PinEq747OfInputs : Prop :=» | 119 «sz.STExp2 E' t1 → GUEPathBound» | 123 «def PinSTExp2OfUNMLOut : Prop » | 125 «(∀ n, |E n| ≤ 2 - κ) → (∀ n, 0» | 128 «def PinGoodFlow : Prop :=» | 132 «/-! ## 3. Good data and the br» | 135 «theorem STExp2_congr (sz : Siz» | 141 «theorem FlowData.ev_eq {sz : S» | 148 «theorem goodFlow_aux (sz : Siz» | 177 «theorem goodFlow : PinGoodFlow» | 187 «(hML hd κ ε 𝔡 𝔠 hκ hε hA.2.1 s» | 192 «theorem bctl_le_two_calB (sz :» | 215 «theorem Ld_mul_etaQ (sz : Size» | 238 «theorem hell_of_scales (sz : S» | 279 «theorem claimA (sz : Sizes d) » | 305 «theorem h730_hscale_real {N ηQ» | 322 «theorem qdBoundExp_eq (sz : Si» | 328 «theorem assembly_747 {t0 N ηQ » | 359 «theorem final_729 {E ρ I0 Λ3 K» | 364 «theorem gronwall_factor {N η d» | 371 «» | 376 «def PinDerived : Prop :=» | 384 «theorem pin3_of_pins (P1 : Pin»
-- 124 citation lines (both ends of ranges), 26 files, missing lines: 0
```
