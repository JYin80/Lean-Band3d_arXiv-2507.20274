# T2338 (ST-D6) design: from `lem:main_ind` (one step `s -> t`) to `UNMLOut` (every time sequence `0 <= t_n <= lemT z_n`)

Prover `claude-sonnet-5-5` (prover-max, stage 1b = the design). Branch `t/T2338` (base `3f750b6`), probe `RBM3D/Probe/T2338Pins.lean` (399 lines, limit 400), commit `854aa29`; the probe stays on the branch, never merged. Last edit: Thu Oct  8 17:03:04 UTC 2026 (`date -u` at the final edit).
Citations: `path.lean:line` is at the base of the branch (`3f750b6`), path relative to `RBM3D/`; `RBM2D/path.lean:line` is in the sister project at `c9a24cf` (DECISIONS §12); paper `1_2:line` is `paper/tex/1_2_Intro_model_result.tex`; "probe NNN" is line NNN of the probe.
Evidence: Lean side in `docs/reports/T2338-prove.md` (b) (B1-B4, B7, B10, B12); numbers, counts and the line-by-line echo of every citation of this report in section 10 (B5, B6, B8, B9, B11, B13).

## 0. The answer

| Q | answer (one line) | evidence |
|---|---|---|
| Q1 base case | the five hypotheses at `s = 0` follow from two deterministic facts at `t = 0`: `𝓛_0 = 𝒦_0` (**owed**: only a private chain of six lemmas, 120 lines) and `G_0 = M` (**merged**); given the identity, `STLK`, `STDecay`, `STDecayStrong`, `STExp2` are trivial and `STLocalMax` is merged; the gluing of section 4 adds `STLmax`, `STLocalEntry` at `0` (`ML:Kbound`, merged) | section 2; probe 86-136, 338-355 |
| Q2 closure | the induction closes: the only mismatch (`STLocalMax` needed at the next `s`, `STLocalEntry` produced) is closed by the merged `STLocalMax_of_STLocalEntry`; the carrier-generic twin is proved in 11 lines | section 3; probe 244-254 |
| Q3 chain | run the chain **to each `t_n`**: `1 - p_k = (1 - t_n)^{k/K}`, `K = ⌈2/(𝔠_d μ)⌉` fixed (6000 at the data of the compiled example); steps are strict iff `t_n > 0`, so the class `{t_n = 0}` is glued by a formal mixing lemma; no interpolation, no explicit union bound, no subsequence machinery | section 4; probe 175-254, 140-173, 256-315 |
| Q4 shape | the candidate `∀ d, STMainInd d → UNMLOut d` is the right statement, **compiled** as `unMLOut_of_mainInd` (probe 360-362) with one extra hypothesis, the named identity `STLoopZeroId` (probe 338-342), and a compiled instance at `sz0`, `z0` (probe 389-392); no consumer needs more | section 5 |
| Q5 route G | state the assembly once over `(law, Flow, mk, T0)`: 236 generic lines + 43 pin lines; `UNMLOutBA` follows in 6 lines from three BA pins (probe 364-369); a band-only version needs a second generic text (estimate: ≈ 236 lines) | section 6; probe 360-369 |
| Q6 rows | R1 base, R2 chain, R3 output (+ `STMainInd` from the owed LW pins), R4 closure; R1-R3 wait for nothing; R4 waits for LW-01 (`LWterm`, `LWtermExp`) only: `STDuhamelII` was owed at the branch base and is proved on main since T2339 (B13) | section 7 |

**Verdict: PASS.** No merged pin contradicts the chain. Corrections to earlier readings (found while compiling): (i) `STMainInd` needs `s_n < t_n` for **every** `n`, so a chain cannot start at `t_n = 0`;
(ii) the preflight's split of `n` into `≤ K+1` classes by step pattern is not needed (prove report (a′)); (iii) at the branch base `STMainInd` is derivable from exactly **three** still-owed pins (`LWterm d`, `LWtermExp d`, `STDuhamelII d`), compiled as an `example` (probe 373-380, B1); on main `STDuhamelII` is proved since T2339, so two remain (B13).

## 1. What the merged code already contains (the inputs of the design)

* `STMainInd d` (`Induction/Defs.lean:294-305`): `3 ≤ d → ∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∃ 𝔠d ∈ (0, 1/100], ∀ 𝔠 sz z, STFlow sz κ ε 𝔠 𝔡 z → ∀ s t, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
  (∀ n, t n ≤ lemT (z n)) → (STLK s ∧ STDecay s ∧ STDecayStrong s ∧ STLocalMax s ∧ STExp2 s) → STConStInd sz 𝔠d s t → STLK t ∧ STLmax t ∧ STDecay t ∧ STExp2 t ∧ STLocalEntry t ∧ STDecayStrong t`.
  Paper: `lem:main_ind` `1_2:1256-1305` (hypotheses (a)-(d) `1_2:1261-1283`, `(con_st_ind)` `1_2:1296-1298`, conclusions `1_2:1299-1304`).
* The paper's proof of `ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal` (`1_2:1309-1311`: induction to `t_1 = (1-λ²) ∨ 1/2` keeping the strong 2-loop estimate, then to `t_0`) fixes **no grid**.
  In Lean both phases are inside one `STMainInd`: `STDecayStrong` is a hypothesis at `s` and a conclusion at `t`, on the index set `λ_n² ≤ 1 - τ_n` (`Induction/Defs.lean:134-141`), and `1-t ≥ λ²` implies `1-s ≥ λ²`.
* The (A) machinery (subsequences, ten stage patterns, `Induction/MainIndRegimes.lean:42`) is **inside** `STMainInd`: `ST_mainInd_of_regimes` (`Induction/MainIndRegimes.lean:616`), `STLK_iff_comp_cover` (`Induction/MainIndRegimes.lean:311`), `ST_mainIndR_seq` (`Induction/MainIndRegimes.lean:289`). The ST-6 rows below do not use it.
* The producers of the step pins: `ST_mainInd_of_pins'` (`Induction/Step4.lean:209`) takes `STStep2`, Step 3 at three regimes, `STStep5I/II`, `STStep6I/II/III`; Step 3 and Step 6 are proved
  (`stStep3RegIII_holds`, `stStep3RegI_holds`, `stStep3II_holds` at `Induction/Step3.lean:377`, `Induction/Step3.lean:408`, `Induction/Step3.lean:432`; `stStep6I_holds`, `stStep6II_holds`, `stStep6III_holds` at `Graph/LWExpTerm6.lean:623`, `Graph/LWExpTerm6.lean:626`, `Graph/LWExpTerm6.lean:631`). Exact remaining dependency: section 7, R4.
* The consumers: `UNMLOut` (`Universality/Pins.lean:432`, owed), `UNMLOutBA` (`BA/UNPins.lean:110`, owed), `MAFixed` (`Main/FixedZ.lean:73`; **proved** `fixed_of_ML` `Main/FixedZ.lean:538` from `∀ d, UNMLOut d`),
  the carrier-generic `STMainIndG` (`BA/FlowPins.lean:565`) with `STMainInd_iff` (`BA/FlowPins.lean:583`, `Iff.rfl`). Registry (`Test/Axioms.lean`): `STMainInd` owed `Test/Axioms.lean:108`, `UNMLOut` `Test/Axioms.lean:191`, `UNMLOutBA` `Test/Axioms.lean:214`.

## 2. Q1: the base case `t = 0` (paper `1_2:1240-1243`: `G_0 = M`, `𝓛^{(n)}_0 = 𝒦^{(n)}_0`)

All seven predicates at the zero sequence are used: the five hypotheses of `STMainInd`, plus `STLmax` and `STLocalEntry` for the gluing of section 4. Generic proofs over any carrier `C : FlowFM sz` and any law `μ`: probe 86-136 (compiled, B1, B3).

| predicate at `τ ≡ 0` | left side | status | source |
|---|---|---|---|
| `STLK` (`Induction/Defs.lean:104`) | `‖𝓛 - 𝒦‖ = 0` | **owed** (deterministic identity, below) | probe `STLKgL_zero` 97 |
| `STDecay` (`Induction/Defs.lean:121`) | `0` | trivial given the identity (right side `≥ 0`) | probe `STDecaygL_zero` 105 |
| `STDecayStrong` (`Induction/Defs.lean:134`) | `0` | trivial given the identity; index set `λ² ≤ 1 - 0` | probe `STDecayStronggL_zero` 110 |
| `STLocalMax` (`Induction/Defs.lean:144`) | `‖G_0 - M‖ = 0` | **merged**: `lwExpTerm3_Gt_zero` (`Graph/LWExpTerm3.lean:1675`), or from `STLocalEntry` by the bridge (section 3) | probe `STLocalEntrygL_zero` 115 |
| `STExp2` (`Induction/Defs.lean:159`) | `‖∫ 𝓛_0 - 𝒦_0‖ = 0` | trivial given the identity, `integral_const`, `isProbabilityMeasure_seqP` (`Gauss/FineModel.lean:171`) | probe `STExp2gL_zero` 119 |
| `STLmax` (`Induction/Defs.lean:112`), for section 4 | `‖𝓛_0‖ = ‖𝒦_0‖` | **merged**: `ML:Kbound` at `τ ≡ 0`, `stKbound_of_flow` (`Loop/KLFinal.lean:302`), plus the identity (`‖𝓛_0‖ = ‖𝒦_0‖`) | probe `STLmaxgL_zero` 101 |
| `STLocalEntry` (`Induction/Defs.lean:151`), for section 4 | `‖G_0 - M‖² = 0` | **merged**, as `STLocalMax` | probe `STLocalEntrygL_zero` 115 |

The one owed fact, `𝓛^{(k)}_0 = 𝒦^{(k)}_0` for every `k ≥ 1` (band: `H_0 = 0`, `z_0 = E + m`), is named `STLoopZeroId` in the probe (probe 338-342). In the repository it exists only as the **private** `azumaProxy_loopFine_sub_STKloop`
(`Induction/AzumaProxyN.lean:597`), whose chain is six private lemmas, `Induction/AzumaProxyN.lean:353-606`, **120 lines** (B9: 14+17+25+11+42+11). The merged public `Lloop_zero_one` (`Loop/GLoopFlow.lean:260`) is `k = 1` only;
`zero_mem_goodSetN` (`Induction/AzumaProxyN.lean:801`) is public but states `H = 0 ∈ GoodSetN` (levels `Γ Λ Φ`), not the identity.
Two ways to obtain it (the dispatcher chooses; section 8): copy the six lemmas into the R1 file (≈ 120 lines), or delete the one word `private` from the last lemma (a one-token edit of a merged ST file; precedent for removing `private` markers in a merged file: T2318, `a2c8dd6`, `Graph/LWExpSim.lean`, B9).
The band base case is assembled in the probe from exactly this fact plus the three merged ones: `stBase_band` (probe 344-355; `STLoopZeroId` is its hypothesis `hpriv`).
The generic form (`stBaseG_of_init`, probe 126-136) takes `STLK0`, `STG0M` and `STKboundgL` as premises, i.e. the interface that the block Anderson instance (BA-V `GLoopAtT0`, BA-K) has to supply.

## 3. Q2: closure of the induction

Hypotheses at the next `s` (`Induction/Defs.lean:300-301`): `STLK, STDecay, STDecayStrong, STLocalMax, STExp2`. Conclusions at `t` (`Induction/Defs.lean:303-305`): `STLK, STLmax, STDecay, STExp2, STLocalEntry, STDecayStrong`.
Four coincide. `STLocalMax` (paper (c) `1_2:1277`, exponent `1/2`) is not produced; `STLocalEntry` (paper `(Gt_bound)` `1_2:1221`) is. **No new pin is needed:**
`STLocalMax_of_STLocalEntry` (`Induction/MainIndRegimes.lean:244`, merged; paper-delta candidate T2245b, `Induction/MainIndRegimes.lean:240`): `‖G-M‖² ≺ W^{-d}B_{τ,K} ≤ W^{-d}B_{τ,0}` (`localAvg1_STWB_le`, `Induction/LocalAvg1.lean:94`) and the square root.
For carriers the same argument is proved in 11 lines over `PrecL` (probe 244-254, `STLocalMaxgL_of_STLocalEntrygL`, one `StochDomAt.of_subset` with `σ' = 2σ`), so the chain induction is stated once for every carrier.

## 4. Q3: the chain of times, the number of steps, every sequence `t_n`

**Construction** (probe 78-79, 175-254, 262-287). RBM2D's `chainTime` (`RBM2D/Induction/Defs.lean:318`; its docstring, finding F2: a fixed `n₀`, not `n`-dependent) with strictness added:
`stChainTime t K k n := 1 - (1 - t n)^{k/K}`, `p_0 = 0`, `p_K = t`. For `0 < t_n < 1`: `0 ≤ p_k < p_{k+1} ≤ t_n` for `k < K` (`stChainTime_facts`, probe 183-195) and
`(1 - p_{k+1})/(1 - p_k) = (1 - t_n)^{1/K} < 1`. **Every step is a legal `STMainInd` application** for every `n` (the hypothesis `∀ n, s n < t n` holds), and the ratio is `< 1` exactly because `t_n > 0`.

**The step condition** `(con_st_ind)` at `(p_k, p_{k+1})`, eventually in `n` (`stChainSteps`, probe 197-240, compiled, B1): with `μ = min(2𝔠𝔡, τ)`, `τ = ε/2`, and `K·𝔠_d·μ ≥ 2`,
`(W^{-d}B_{p_{k+1},0})^{𝔠_d} ≤ (2N^{-μ})^{𝔠_d} ≤ N^{-1/K} ≤ (N^{-1+τ})^{1/K} ≤ (1-t_n)^{1/K}`. Inputs, all merged: `scaleFacts_R1` (`Induction/ScaleFacts.lean:193`, `W^{-d}B_{u,0} ≤ 2N^{-μ}` for `u ≤ T_n`, from `(eq:WO)` and `W ≥ N^𝔠`),
the horizon `N^{-1+τ} ≤ 1 - T_n` (band: `ST_one_sub_lemT`, `Induction/Step2Iterate.lean:1014`; `stHorizon_band`, probe 319-336), and `K·𝔠_d·μ ≥ 2` absorbs `2^{𝔠_d}` (`N^{𝔠_d μ/2} ≥ 2^{𝔠_d}` eventually).
`K = ⌈2/(𝔠_d μ)⌉` depends on `(𝔠_d, 𝔠, 𝔡, ε)` only, **never on `n` or on `t`**: it is chosen after `𝔠_d` (which `STMainInd` fixes before `𝔠`, `Induction/Defs.lean:296-297`) and before `sz`, `z` (probe 268-271). This is the point of the fixed grid:
with `n`-dependent step counts the induction over `k` would not be an induction in the logic. (A chain with the true ratio `Bctl(t0)^{𝔠_d}` needs `≤ 2701` steps asymptotically at the same data, prove report (a) row 8; the uniform grid takes `K = 6000` but is a formula in `t`, with no per-`n` construction.)
It replaces RBM2D `chainStepCond` (`RBM2D/Induction/ScaleFacts.lean:171-270`, 100 lines): the `d ≥ 3` version is `stChainSteps`, 44 lines with its docstring (probe 197-240), because `scaleFacts_R1` is merged.

**Numbers** (B5; `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠_d = 1/100`): `μ = min(1/30, 1/20) = 1/30`, `K = 6000`. At the merged sizes `sz0` (`Defs/Sizes.lean:260`, `n = 0,1,2`) and the merged flow points `z0 n = 1/2 + i N_n^{-4/5}` (`Induction/Defs.lean:413`, `flow_z0` `Induction/Defs.lean:435`; `Im z0 = 8.76e-06, 4.05e-10, 1.18e-12`),
for `t = lemT z/2` and `t = lemT z` the true inequality `Bctl(t)^{𝔠_d} ≤ (1-t)^{1/K} < 1` holds (e.g. `n = 0`, `t = lemT`: `0.98262 ≤ 0.998066`); the same at the preflight points `1/2 + 0.05 i`. One of the eventual conditions in the proof of `stChainSteps`, `2^{𝔠_d} ≤ N^{𝔠_d μ/2}`,
holds iff `N ≥ 2^{2/μ} = 2^{60}`; the other conditions come from `scaleFacts_R1` and the horizon (no explicit threshold). `sz0` has `N = 2^{21}, 2^{39}, 2^{49.5}`: the Lean statement is eventual and the table checks the inequality, not a threshold.
A compiled **nonempty instance** of `stChainSteps` at `sz0`, `z0`, `K = 6000`, `t = lemT z/2`, last step `k = 5999` (probe 382-387) discharges every deterministic hypothesis (`hbw`, `hWO`, `hsz`, `hr` come from `flow_z0` through `stHorizon_band`).

**Every sequence, uniformity.** `UNMLOut` quantifies over sequences; the theorem is proved for an arbitrary `t` and the chain is built **from `t`** (`k ↦ stChainTime t K k` are sequences), so there is nothing to interpolate and no "chain times fixed in advance".
There is no explicit union bound over the `K` steps: each application of `STMainInd` turns a `Prec` statement at `p_k` into one at `p_{k+1}`; the losses are inside `STMainInd`. (The `N^{-C}`-net of `1_2:1400` is not needed: `≺` is per sequence, as the consumers use it, section 5.)

**The class `t_n = 0`** (probe 140-173, 262-287, 289-313). `STMainInd` cannot start from `s_n = t_n = 0`. Put `t'_n = t_n` if `t_n > 0` and `t'_n = lemT z_n / 2` if `t_n = 0` (positive, `≤ lemT`); the chain to `t'` gives the six conclusions at `t'` (`stPosConclG_of_mainIndG`, probe 262-287);
the base case gives them at the zero sequence (section 2); and for each `n` either `t_n = 0` (the bad event at `t` equals the bad event at `0`) or `t_n = t'_n`, so `bad_t(n) ⊆ bad_0(n) ∪ bad_{t'}(n)` and `StochDomAt.of_subset_union` (`Defs/StochDomAt.lean:355`) concludes.
These are five lemmas of 4-5 lines (`STLKgL_mix` ... `STLocalEntrygL_mix`, probe 147-171), **no subsequence, no `Sizes.comp`, no pattern classes**; `STDecayStrong` is not needed in the output, so its `t`-dependent index set never enters the mixing.
`stMLOutG_of_mainIndG` (probe 289-313) is the whole assembly, compiled (B1, B3).

## 5. Q4: shape check against the consumers

* **`MAFixed`/MA-06** is already a proved theorem from `∀ d, UNMLOut d` (`Main/FixedZ.lean:538`). It uses `UNMLOut` at `t = lemT z` only and extracts `STLK`, `STLocalEntry` (`Main/FixedZ.lean:121`, in `locSCFixed_of_ML`, `Main/FixedZ.lean:100`), and `STLK`, `STDecay`, `STExp2` (`Main/FixedZ.lean:444`, in `QDiffFixed_of_ML`, `Main/FixedZ.lean:419`); it never uses `STLmax`.
* **UN-51/52.** The merged UN rows take `∀ d, UNMLOut d` as a hypothesis (e.g. `UNOURow`, `Universality/Pins.lean:793`). The port source uses `P7Out` and `P7ExpOut` (`RBM2D/Universality/Pins.lean:238`, `RBM2D/Universality/Pins.lean:250`: all bulk energy sequences and time sequences with `N^{-1+τ} ≤ 1 - t`),
  applied at `(E', t₁)` with `E' = lemE z_n`, `t₀ = lemT z_n`, `t₁ = (1 - ζ(t_n)) t₀ ≤ t₀` (`RBM2D/Universality/GUEPhase/RandomLayerB.lean:35`; the uses are `RBM2D/Universality/GUEPhase/RandomLayerA.lean:738`, `RBM2D/Universality/GUEPhase/RandomLayerA.lean:748`, `RBM2D/Universality/GUEPhase/Eq729B.lean:1613`).
  There `P7Out` is `MLConcl` (`RBM2D/Induction/Defs.lean:308`: `InitLK ∧ InitDecay ∧ InitLocal` and the loop-maximum bound) and `P7ExpOut` is `MLExpConcl` (`RBM2D/Evolution/Defs.lean:138`); `InitLK`, `InitLocal` are consumed as `hB.1.1`, `hB.1.2.2` (`RBM2D/Universality/GUEPhase/PathBounds.lean:254`, `RBM2D/Universality/GUEPhase/PathBounds.lean:521`).
  In RBM3D these are `STLK`, `STLocalMax` (from `STLocalEntry` by the bridge of section 3), `STDecay`, `STLmax`, `STExp2`: exactly the five conclusions of `UNMLOut`.
* **Not needed** (B6): no file of `RBM3D/Universality`, `RBM3D/Main`, `RBM3D/Endpoints.lean` mentions `STGbEXP`, `STLKU`, `STLmaxU` or `STStep*`; the only RBM2D mention of `GbEXP` under `Universality` is a docstring (`RBM2D/Universality/GUEPhase/EntryTail.lean:108`).
  `STGbEXP d` is proved (`stGbEXP_holds`, `Green/GbEXP.lean:811`) and its parts (ii), (ij) prove Step 1 (`stStep1_holds`, `Green/GbEXP.lean:816`); `STLKU` (`Induction/Step34Pins.lean:184`) is produced by Step 4 and consumed inside `ST_mainIndR_of_steps` (`Induction/MainIndRegimes.lean:197`, `Induction/MainIndRegimes.lean:212`): both are internal to `STMainInd`.
  Uniformity in `t` inside `Prec` is not used by any consumer: each fixes its time sequence.
* **Verdict.** `UNMLOut` has the right shape: constants before `sz, z` (`κ ε 𝔡 𝔠`), `t` last, the five conclusions of `STMainInd` at `t` (the sixth, `STDecayStrong`, only matters for `1-t ≥ λ²` inside the induction). The statement
  `∀ d, STMainInd d → UNMLOut d` is **compiled** as `unMLOut_of_mainInd` (probe 360-362) with the single extra hypothesis `STLoopZeroId` (section 2); `unMLOut_iff` (probe 357-358) is `Iff.rfl`; the instance at `sz0`, `z0`, `t = lemT z/2` (probe 389-392) keeps `STMainInd 3` and `STLoopZeroId 3` as hypotheses and discharges the rest.

## 6. Q5: route G (the assembly over a carrier)

**Statement.** Over `(law, Flow, mk, T0)` exactly as `STMainIndG` (`BA/FlowPins.lean:565`): `STMLOutG` (probe 69-76) is `UNMLOut` for `(seqP, STFlow, bandFM, lemT)` and `UNMLOutBA` for `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, both by `Iff.rfl`
(`unMLOut_iff` probe 357-358; `unMLOutBA_of_pins` probe 364-369 type-checks by unification). The generic theorem `stMLOutG_of_mainIndG` (probe 289-313) takes **three pins** and nothing else:
`STMainIndG`, `STBaseG` (probe 55-59: the six conclusions at the zero sequence), `STHorizonG` (probe 61-67: admissible sizes, `0 < T0 < 1`, `N^{-1+ε/2} ≤ 1 - T0` eventually).

**What the band rows must not hard-wire** (each is a premise or an instance in the probe): (1) `STFlow` (only `Admissible` is read, through `STHorizonG`); (2) `lemT`/`msc` (only `0 < T0 < 1` and the range inequality; band proof probe 319-336);
(3) `Lloop`, `Gt`, `STKloop`, `mE` (only `C.L, C.K, C.G, C.M` through `STLK0`, `STG0M`; band instance probe 338-355); (4) the law `seqP sz` (any `μ`; `IsProbabilityMeasure` only in `STExp2gL_zero`, probe 119);
(5) `Bandwidth`/`WO` are read from `Admissible`, never from `STFlow`; (6) the closure bridge is the generic `STLocalMaxgL_of_STLocalEntrygL`, not the band theorem;
(7) the constant order `κ ε 𝔡 → 𝔠_d → 𝔠 → sz z` and the `∃ 𝔠_d` position (probe 268-271); (8) nothing may use `Sizes.comp` or `STLK_iff_comp_cover`: they are stated for the band `Prec` and the assembly does not need them.

**Cost** (B8, probe 399 lines): header 28, `#check` 9, pins 43 (`STConclgL`, `STLK0`, `STG0M`, `STBaseG`, `STHorizonG`, `STMLOutG`, `stChainTime`), generic proofs **236** (base 59, mixing 35, chain 81, assembly 61),
band-specific 40 (horizon 18, identity 5, base 12, `Iff.rfl` + target 5), block Anderson wrapper **6**, instances 18 (probe 373-387, 389-392), end + axiom prints 6.

| | route G (generic first) | band first, BA twin later |
|---|---|---|
| ST-6 generic text | 236 lines (+43 pin lines), written once | ≈ 236 lines with `Lloop`, `Gt`, `STKloop`, `seqP`, `lemT` written out (estimate: the carrier adds only the binders `{sz} (C : FlowFM sz) (μ)`) |
| band-specific | 40 lines + the base identity (120-line port, or 1 token) | the same |
| BA | `unMLOutBA_of_pins`: 6 lines + the BA instances of the three pins | a second ≈ 236-line copy for BA + the same BA instances |
| difference | | **≈ +236 lines (≈ 0.24 of a 1000-line ticket)** (estimate: the twin has the length of the generic text) |

The BA instances common to both routes (not ST-6 work): `STMainIndG` for BA (BA-V main induction, conversion of `ST_mainInd_of_regimes`: pilot `docs/reports/T2326-pilot.md` §7); `STBaseG` for BA (`STLK0`, `STG0M`: `GLoopAtT0` with the non-scalar `M^{(B)} ⊗ I`; `STKboundgL`: BA K-stage,
needed only for `STLmax` on the class `t_n = 0`); `STHorizonG` for BA (merged `BAt0 = Im m/(Im m + Im z)`, `BAt0_pos`, `BAt0_lt_one`, `BA/MFixedPoint.lean:279`, `BA/MFixedPoint.lean:282`, `BA/MFixedPoint.lean:285`; `BAflowT0` `BA/FlowPins.lean:537`; `1 - BAt0 = Im z/(Im m + Im z)` and `Im m ≤ 1` must be proved:
`Im m ≤ ‖m‖ ≤ 1` follows from the merged `BAm_norm_le_one`, `BA/Ward.lean:136`, and `BAm_spec`, `BA/MFixedPoint.lean:441`; no lemma `(BAm d L g z).im ≤ 1` is merged by name).
**Recommendation: route G for ST-6** (the saving is small in absolute terms because ST-6 is small; there is no reason to pay for a twin).

## 7. Q6: rows, sizes, roles, dependencies, registry

Every proof of R1-R3 below is compiled in the probe at the branch base; a row is "move the probe text into the file, add the band instance, docstrings, a nonempty instance, registry lines". Sizes in lines (lo / central / hi) are **estimates**: compiled probe lines of the row (B8) times 1.3 / 2.0 / 3.0
(docstrings, header, nonempty instance, registry lines, the usual overrun), plus 120 lines for the port route of the identity. `prover` = Sonnet effort high.

| row | sole writable files | content (probe lines) | compiled | size | role | depends on |
|---|---|---|---|---|---|---|
| **R1 base** | `Induction/MainIndBase.lean` (+ optionally `Induction/AzumaProxyN.lean`: drop `private` at `Induction/AzumaProxyN.lean:597`) | `STConclgL`, `STLK0`, `STG0M`, `STBaseG` (probe 42-59); zero lemmas and `stBaseG_of_init` (probe 81-138); `STLoopZeroId` and `stBase_band` (probe 338-355); nonempty instance | 95 | edit route 120 / 190 / 280; port route 240 / 310 / 400 | `prover` | nothing |
| **R2 chain** | `Induction/MainIndChain.lean` | `STHorizonG`, `stChainTime` (probe 61-67, 78-79); chain facts and `stChainSteps` (probe 175-240); `STLocalMaxgL_of_STLocalEntrygL` (probe 242-254); `stPosConclG_of_mainIndG` (probe 262-287); `stHorizon_band` (probe 319-336); the `stChainSteps` instance (probe 382-387) | 138 | 180 / 280 / 410 | `prover` | R1 merged (imports `STConclgL`, `STBaseG`) |
| **R3 output** | `Induction/MainIndOut.lean` | `STMLOutG` (probe 69-76); the five mixing lemmas (probe 140-173); `stMLOutG_of_mainIndG` (probe 289-313); `unMLOut_iff`, `unMLOut_of_mainInd` (probe 357-362) with `STLoopZeroId` discharged by R1; BA wrapper (probe 364-369); `stMainInd_of_LW` (the `example`, probe 373-380, as a theorem; hypotheses `LWterm d`, `LWtermExp d`; the `STDuhamelII d` of the example is `stDuhamelII_holds d` on main) and `unMLOut_of_LW`; endpoint instance (probe 389-392) | 92 | 120 / 180 / 280 | `prover` | R1, R2 merged |
| **R4 closure** | `Induction/MainIndFinal.lean` (or inside the LW-01 closing ticket), `Test/Axioms.lean` | `stMainInd_holds : ∀ d, STMainInd d` (the producers of `LWterm`, `LWtermExp`: names not yet fixed), `unMLOut_holds`; registry | - | 20 / 40 / 80 | `prover` | LW-01 (`LWterm`, `LWtermExp`); T2339 is merged (B13) |

Totals R1-R3 (B8): edit route 420 / 650 / 970, port route 540 / 770 / 1090 (one ticket of ≈ 650-770 lines `prover-hard` is equally possible: no row waits for outside work; imports go one way R1 → R2 → R3; for R1 ∥ R2 move the pin defs (probe 42-79) into a small row R0).
**Which row owns `stMainInd_holds`:** R4. R3 already makes `STMainInd` visibly **owed through exactly `LWterm`, `LWtermExp`, `STDuhamelII`** at the branch base (`example`, probe 373-380: `ST_step2_of_pinsLW'` `Induction/Step2Iterate.lean:1793` needs `LWtermExp` and, through `stOptL2_of_pins` and `STLWB_of_LWterm` (`Induction/Step2Events.lean:1355`), `LWterm`;
`STStep5I` needs `STEtermsMid` ← `stEtermsMid_of_LWT` (`Induction/EtermsMid.lean:1670`) ← `STLWT_of_LWtermExp` (`Induction/Step2Events.lean:1427`) and no S5 ticket, since `stDuhamelI_holds` (`Induction/DuhamelI.lean:1943`) and `stIniTermI_holds` (`Induction/IniTermI.lean:3715`) are merged; `STStep5II` needs `STDuhamelII` (T2339, DECISIONS §150 (4)) and `LWtermExp`).
Status after the branch base (B13): T2339 is merged on main (`0853ac1`): `stDuhamelII_holds` is proved and the registry line of `STDuhamelII` is deleted, so the R3 theorem `stMainInd_of_LW` takes `LWterm d`, `LWtermExp d` and uses `stDuhamelII_holds d`; `LWterm`, `LWtermExp` are still owed on main.
Registry owners: `LWterm` `Test/Axioms.lean:147` (LW-01), `LWtermExp` `Test/Axioms.lean:149` (LW-01, LW-16), `STDuhamelII` `Test/Axioms.lean:179` (S5-01; at the branch base; T2339 deleted the line, B13). So "waits for `STStep2` ← LW-01 and `STStep5I/II` ← S5-15/S5-26" reduces to LW-01 alone: S5-15 = T2333 is merged (DECISIONS §150 (1)) and S5-26 = T2339 is merged (B13).
R1-R3 and the MA/UN statements wait for nothing: `UNOURow` and `fixed_of_ML` are stated and proved over the owed `UNMLOut` already; ST-6 discharges the debt.

**Registry classes of the new pins** (`Test/Axioms.lean`; precedent `owedProps` `Test/Axioms.lean:142-145` for the generic `STLmaxgL`, `STKboundgL`, `STLKgL`, `STLocalMaxgL`, and `structuralProps` `Test/Axioms.lean:239` with `STMainIndR` at `Test/Axioms.lean:317`). Proposal, for dispatcher sign-off:

| new name | class | note |
|---|---|---|
| `STLK0`, `STG0M`, `STBaseG`, `STHorizonG` | **owed** (BA-V instances; owner BA-V `GLoopAtT0` / horizon) | band instances proved in R1, R2 (`stBase_band`, `stHorizon_band`); carried as hypotheses of `stBaseG_of_init`, `stPosConclG_of_mainIndG`, `stMLOutG_of_mainIndG` |
| `STConclgL`, `STMLOutG`, `stChainTime` | **structural** / not carried | bundle, restatement of `UNMLOut`/`UNMLOutBA`, a definition of times |
| `STLoopZeroId` | not a library pin | R1 proves it (port or edit); named only in the probe |
| existing `STMainInd` (`Test/Axioms.lean:108`), `UNMLOut` (`Test/Axioms.lean:191`) | deleted by R4 | `unMLOut_holds`; `UNMLOutBA` (`Test/Axioms.lean:214`) stays, owner BA-V3 |
| existing `STLK, STLmax, STDecay, STDecayStrong, STLocalMax, STExp2` (`Test/Axioms.lean:102-107`, "ST-6 chain induction") | reconcile in R4 | open question 2 (section 8) |

## 8. Risks, paper deltas (candidates `T2338a`..), open questions

* **Risk 1 (R1).** The base identity is private. Port (120 lines, mechanical: the proofs are in the repository) or the one-token edit. Either way `STLoopZeroId` is the interface. If neither is acceptable, `UNMLOut` stays conditional on it.
* **Risk 2 (BA).** `STMainIndG`, `STBaseG`, `STHorizonG` at BA are BA-V work; ST-6 only fixes their statements. `STHorizonG` for BA needs `Im m(z,g) ≤ 1` for `BAm` (no named lemma; a few lines from `BAm_norm_le_one`, `BAm_spec`, section 6).
* **Risk 3 (threshold).** `stChainSteps` is eventual; the condition `N ≥ 2^{2/μ}` is one of several and nothing in the consumers needs an explicit `N_0`.
* **`T2338a` (organisation):** the Lean chain is the uniform grid `1 - p_k = (1-t)^{k/K}` with fixed `K = ⌈2/(𝔠_d μ)⌉` instead of the paper's two phases without a grid (`1_2:1309-1311`); the strong 2-loop phase is carried by `STDecayStrong` inside `STMainInd`; same conclusion.
* **`T2338b` (needed):** `lem:main_ind` requires `s < t` and `(1-t)/(1-s) < 1`; it does not cover `t = 0`, which the base case (`1_2:1240-1243`) supplies; "uniformly in `t ∈ [0,t_0]`" (`1_2:1194`, `1_2:1204`, `1_2:1218`) includes `t = 0`.
* **`T2338c` (reading):** "uniformly in `t`" is read per time sequence (`UNMLOut`: `∀ t : ℕ → ℝ`), as RBM2D `P7Out`; the `N^{-C}`-net of `1_2:1400` in `t` is not formalised (in `z` it is the sections lemma, `Endpoints.lean:419`).
* **`T2338d` (the base case needs `ML:Kbound`):** at `t = 0`, `‖𝓛_0‖ = ‖𝒦_0‖ ≺ (W^{-d}B_{0,0})^{k-1}` is the bound `(eq:bcal_k)` (`STKbound`, `Induction/Defs.lean:174`), not "no error" (used only for `STLmax` on the class `t_n = 0`).
* **Open question 1 (dispatcher):** R1: port or edit `Induction/AzumaProxyN.lean:597`? Pack R1-R3 in one ticket or three? (section 7).
* **Open question 2 (supervisor/dispatcher):** after R4 the six owed predicate lines `STLK ... STExp2` (`Test/Axioms.lean:102-107`, "owed: ST-6 chain induction") have no remaining debt as predicates; delete or move to `structuralProps`? I do not decide.
* **Not claimed.** The probe contains no proof of `STMainInd`, `STLoopZeroId` or any BA instance; every `example`/theorem names its hypotheses. The generic theorems are over the merged `STMainIndG` pin, which is conditional (`STMainInd` is owed).

## 9. Evidence index

B1 `lake env lean RBM3D/Probe/T2338Pins.lean` exit 0 (no `sorry`, no warning); B2 `lake build RBM3D.Probe.T2338Pins` exit 0; B3 `#print axioms` of the declarations of the probe: `propext, Classical.choice, Quot.sound` only;
B4 statements extracted by script; B5 `chain2.py` (section 4); B6 consumer greps (section 5); B7 name-clash grep; B8 section sizes and row ranges (sections 6, 7); B9 size of the private chain (section 2) and the `private` precedent;
B10 RBM2D citations and `git diff --stat`; B11 echo of every citation of this report; B12 the compiled instances; B13 the state of main after the branch base. B1-B4, B7, B10, B12 are in `docs/reports/T2338-prove.md` (b); B5, B6, B8, B9, B11, B13 are in section 10 below.
Port statement: the idea of `chainTime` (`RBM2D/Induction/Defs.lean:318`) and the shape of `chainStepCond`/`chainTarget` (`RBM2D/Induction/ScaleFacts.lean:171`, `RBM2D/Induction/Chain.lean:368`) are ported; no RBM2D text is copied.

## 10. Script output
**B5 chain numbers at the data of the compiled example: the script `chain2.py`, then its output** (run Thu Oct  8 17:03:03 UTC 2026)
```
$ python3 -I chain2.py
import cmath, math
d=3; eps=dd=0.1; cfr=1/6; cd=1/100                      # eps, fd, fc, fc_d of the compiled example
mu=min(2*cfr*dd, eps/2); K=math.ceil(2/(cd*mu))           # K = ceil(2/(fc_d*mu)), tau = eps/2
print(f"mu=min(2*fc*fd, eps/2)={mu:.5f}; K=ceil(2/(fc_d*mu))={K}; K*fc_d*mu={K*cd*mu:.3f} >= 2: {K*cd*mu>=2}")
def msc(z):
    r=cmath.sqrt(z*z-4)
    return next(m for m in ((-z+r)/2,(-z-r)/2) if m.imag>0)
def Bctl(W,L,lam,v): return W**(-d)*(1/(lam**2+v)+1/(L**d*v))     # W^{-d} B_{t,0}, v = 1-t
def run(tag,n,eta_of):
    L=4*(n+1); W=(2*(n+1))**5; lam=(2*(n+1))**-6.0; N=(W*L)**d
    eta=eta_of(N); z=complex(0.5,eta); m=msc(z); v0=eta/(m.imag+eta)      # 1-t0 = Im z/(Im m + Im z)  (1_2:789)
    for name,v in (("t=lemT/2",(1+v0)/2),("t=lemT",v0)):
        B=Bctl(W,L,lam,v); r=v**(1.0/K)
        ks=range(0,K,97)                                         # sampled steps: 1-p_{k+1} = v^{(K-k-1)/K}... Bctl(p_{k+1}) <= Bctl(t)
        ok=all(Bctl(W,L,lam,v**((k+1)/K))**cd<=r and r<1 for k in ks)
        print(f"{tag} n={n} N=2^{math.log2(N):.1f} Im z={eta:.2e} {name}: 1-t={v:.3e} Bctl^cd={B**cd:.5f} <= (1-t)^(1/K)={r:.6f}: {B**cd<=r}; sampled steps ok: {ok}")
for n in (0,1,2): run("z0 ",n,lambda N: N**(-0.8))             # the merged flow points z0 n = 1/2 + i N_n^{-4/5}
for n in (0,1,2): run("pre",n,lambda N: 0.05)                  # the preflight points 1/2 + 0.05 i
print(f"one eventual condition of stChainSteps, 2^cd <= N^(cd*mu/2), holds iff N >= 2^(2/mu) = 2^{2/mu:.0f} (the others come from scaleFacts_R1)")
# ---- output ----
mu=min(2*fc*fd, eps/2)=0.03333; K=ceil(2/(fc_d*mu))=6000; K*fc_d*mu=2.000 >= 2: True
z0  n=0 N=2^21.0 Im z=8.76e-06 t=lemT/2: 1-t=5.000e-01 Bctl^cd=0.90766 <= (1-t)^(1/K)=0.999884: True; sampled steps ok: True
z0  n=0 N=2^21.0 Im z=8.76e-06 t=lemT: 1-t=9.051e-06 Bctl^cd=0.98262 <= (1-t)^(1/K)=0.998066: True; sampled steps ok: True
z0  n=1 N=2^39.0 Im z=4.05e-10 t=lemT/2: 1-t=5.000e-01 Bctl^cd=0.81792 <= (1-t)^(1/K)=0.999884: True; sampled steps ok: True
z0  n=1 N=2^39.0 Im z=4.05e-10 t=lemT: 1-t=4.187e-10 Bctl^cd=0.96157 <= (1-t)^(1/K)=0.996407: True; sampled steps ok: True
z0  n=2 N=2^49.5 Im z=1.18e-12 t=lemT/2: 1-t=5.000e-01 Bctl^cd=0.76964 <= (1-t)^(1/K)=0.999884: True; sampled steps ok: True
z0  n=2 N=2^49.5 Im z=1.18e-12 t=lemT: 1-t=1.219e-12 Bctl^cd=0.94952 <= (1-t)^(1/K)=0.995438: True; sampled steps ok: True
pre n=0 N=2^21.0 Im z=5.00e-02 t=lemT/2: 1-t=5.252e-01 Bctl^cd=0.90721 <= (1-t)^(1/K)=0.999893: True; sampled steps ok: True
pre n=0 N=2^21.0 Im z=5.00e-02 t=lemT: 1-t=5.032e-02 Bctl^cd=0.92870 <= (1-t)^(1/K)=0.999502: True; sampled steps ok: True
pre n=1 N=2^39.0 Im z=5.00e-02 t=lemT/2: 1-t=5.252e-01 Bctl^cd=0.81752 <= (1-t)^(1/K)=0.999893: True; sampled steps ok: True
pre n=1 N=2^39.0 Im z=5.00e-02 t=lemT: 1-t=5.032e-02 Bctl^cd=0.83692 <= (1-t)^(1/K)=0.999502: True; sampled steps ok: True
pre n=2 N=2^49.5 Im z=5.00e-02 t=lemT/2: 1-t=5.252e-01 Bctl^cd=0.76927 <= (1-t)^(1/K)=0.999893: True; sampled steps ok: True
pre n=2 N=2^49.5 Im z=5.00e-02 t=lemT: 1-t=5.032e-02 Bctl^cd=0.78752 <= (1-t)^(1/K)=0.999502: True; sampled steps ok: True
one eventual condition of stChainSteps, 2^cd <= N^(cd*mu/2), holds iff N >= 2^(2/mu) = 2^60 (the others come from scaleFacts_R1)
```
**B6 consumer greps** (run Thu Oct  8 17:03:03 UTC 2026)
```
$ grep -rln 'STGbEXP\|STLKU\|STLmaxU\|STStep' RBM3D/Universality RBM3D/Main RBM3D/Endpoints.lean | wc -l;  git -C ../RBM2D --no-optional-locks grep -n GbEXP c9a24cf -- RBM2D/Universality
RBM3D files mentioning STGbEXP|STLKU|STLmaxU|STStep under Universality, Main, Endpoints.lean: 0
c9a24cf:RBM2D/Universality/GUEPhase/EntryTail.lean:108:`b = 0` is the merged band statement (`gbEXPV3`), `a = 0` the flat GUE.  Paper: `lem_GbEXP`
```
**B8 probe sizes and row ranges (lines, inclusive)** (run Thu Oct  8 17:03:03 UTC 2026)
```
$ python3 -I ranges.py RBM3D/Probe/T2338Pins.lean
probe RBM3D/Probe/T2338Pins.lean: 399 lines
header                             1-28                                     = 28
s1 #check                          29-37                                    = 9
s2 pins                            38-80                                    = 43
s3 base (generic)                  81-139                                   = 59
s4 mixing (generic)                140-174                                  = 35
s5 chain (generic)                 175-255                                  = 81
s6 assembly (generic)              256-316                                  = 61
s7 band + BA                       317-370                                  = 54
s8 instances + end + prints        371-399                                  = 29
sum of the sections: 399
generic proofs s3+s4+s5+s6 = 236
band: horizon                      319-336                                  = 18
band: identity                     338-342                                  = 5
band: base                         344-355                                  = 12
band: iff + target                 357-358 360-362                          = 5
BA wrapper                         364-369                                  = 6
instances                          373-380 382-387 389-392                  = 18
end + axiom prints                 394-399                                  = 6
band-specific total = 40
row R1 compiled                    42-59 81-139 338-355                     = 95
row R2 compiled                    61-67 78-79 175-240 242-254 262-287 319-336 382-387 = 138
row R3 compiled                    69-76 140-174 289-313 357-362 364-369 373-380 389-392 = 92
R1: compiled 95; x1.3/x2.0/x3.0 = 120/190/280; port route (+120): 240/310/400
R2: compiled 138; x1.3/x2.0/x3.0 = 180/280/410
R3: compiled 92; x1.3/x2.0/x3.0 = 120/180/280
totals R1-R3 lo: edit route 420, port route 540
totals R1-R3 central: edit route 650, port route 770
totals R1-R3 hi: edit route 970, port route 1090
```
**B9 private chain of `L_0 = K_0` (dependency closure of the last lemma inside the file) and the `private` precedent** (run Thu Oct  8 17:03:03 UTC 2026)
```
$ python3 -I b9.py RBM3D/Induction/AzumaProxyN.lean azumaProxy_loopFine_sub_STKloop;  git show a2c8dd6 ... LWExpSim.lean
azumaProxy_initialGreenScalar: lines 353-366 = 14
azumaProxy_adjacentMismatch: lines 368-384 = 17
azumaProxy_adjacentBlockWeight: lines 386-410 = 25
azumaProxy_loopL_zero_eq: lines 445-455 = 11
azumaProxy_loopL_zero_eq_KLK: lines 489-530 = 42
azumaProxy_loopFine_sub_STKloop: lines 596-606 = 11
closure: 6 declarations, total 120 lines; span 353 - 606
a2c8dd6 T2318: merge LW-14e-4 Sound Graph/LWExpSound
lines starting with '-private' in that file's diff: 29
```
**B11 echo of every citation of sections 0-9 (source text at the cited line, first 34 characters; `..` = range, first and last line)** (run Thu Oct  8 17:03:04 UTC 2026)
```
$ python3 -I echo_cites.py docs/reports/T2338-design.md
RBM3D/BA/FlowPins.lean: 537 «def BAflowT0 (z : ℕ → ℂ) (n : ℕ) :» | 565 «def STMainIndG (d : ℕ) (law : ∀ sz» | 583 «theorem STMainInd_iff (d : ℕ) :»
RBM3D/BA/MFixedPoint.lean: 279 «def BAt0 (z m : ℂ) : ℝ := m.im / (» | 282 «theorem BAt0_pos {z m : ℂ} (hz : 0» | 285 «theorem BAt0_lt_one {z m : ℂ} (hz » | 441 «theorem BAm_spec {g : ℝ} {z : ℂ} (»
RBM3D/BA/UNPins.lean: 110 «def UNMLOutBA (d : ℕ) : Prop :=»
RBM3D/BA/Ward.lean: 136 «theorem BAm_norm_le_one (g : ℝ) (z»
RBM3D/Defs/Sizes.lean: 260 «def sz0 : Sizes 3 where»
RBM3D/Defs/StochDomAt.lean: 355 «theorem of_subset_union (hsize : T»
RBM3D/Endpoints.lean: 419 «/-- **Sections ⟹ eventually for al»
RBM3D/Gauss/FineModel.lean: 171 «instance isProbabilityMeasure_seqP»
RBM3D/Graph/LWExpTerm3.lean: 1675 «theorem lwExpTerm3_Gt_zero {E : ℝ}»
RBM3D/Graph/LWExpTerm6.lean: 623 «theorem stStep6I_holds : ∀ d : ℕ, » | 626 «theorem stStep6II_holds : ∀ d : ℕ,» | 631 «theorem stStep6III_holds : ∀ d : ℕ»
RBM3D/Green/GbEXP.lean: 811 «theorem stGbEXP_holds (hd : 3 ≤ d)» | 816 «theorem stStep1_holds (hd : 3 ≤ d)»
RBM3D/Induction/AzumaProxyN.lean: 353 «/-- The scalar of a signed Green f» .. 606 «(by simpa [loopOf, LoopIdx.length]» | 597 «private theorem azumaProxy_loopFin» | 801 «theorem zero_mem_goodSetN {E : ℝ} »
RBM3D/Induction/Defs.lean: 104 «def STLK (E τ : ℕ → ℝ) : Prop :=» | 112 «def STLmax (E τ : ℕ → ℝ) : Prop :=» | 121 «def STDecay (E τ : ℕ → ℝ) : Prop :» | 134 «def STDecayStrong (E τ : ℕ → ℝ) : » | 134 «def STDecayStrong (E τ : ℕ → ℝ) : » .. 141 «((sz.W n : ℕ) : ℝ) ^ (-D))» | 144 «def STLocalMax (E τ : ℕ → ℝ) : Pro» | 151 «def STLocalEntry (E τ : ℕ → ℝ) : P» | 159 «def STExp2 (E τ : ℕ → ℝ) : Prop :=» | 174 «def STKbound (E : ℕ → ℝ) : Prop :=» | 294 «def STMainInd (d : ℕ) : Prop :=» .. 305 «STDecayStrong sz (STflowE z) t» | 296 «∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧» .. 297 «∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → » | 300 «(STLK sz (STflowE z) s ∧ STDecay s» .. 301 «STLocalMax sz (STflowE z) s ∧ STEx» | 303 «STLK sz (STflowE z) t ∧ STLmax sz » .. 305 «STDecayStrong sz (STflowE z) t» | 413 «def z0 (n : ℕ) : ℂ := ⟨1 / 2, ((sz» | 435 «theorem flow_z0 : STFlow sz0 (1 / »
RBM3D/Induction/DuhamelI.lean: 1943 «theorem stDuhamelI_holds (d : ℕ) :»
RBM3D/Induction/EtermsMid.lean: 1670 «theorem stEtermsMid_of_LWT (d : ℕ)»
RBM3D/Induction/IniTermI.lean: 3715 «theorem stIniTermI_holds (d : ℕ) :»
RBM3D/Induction/LocalAvg1.lean: 94 «theorem localAvg1_STWB_le (n : ℕ) »
RBM3D/Induction/MainIndRegimes.lean: 42 «single-time conclusions (`ST_mainI» | 197 «have hS4 : STLKU sz (STflowE z) s » | 212 «exact ⟨STLK_of_STLKU sz (fun n => » | 240 «paper-delta candidate `T2245b`): `» | 244 «theorem STLocalMax_of_STLocalEntry» | 289 «theorem ST_mainIndR_seq (d : ℕ) (R» | 311 «theorem STLK_iff_comp_cover (d : ℕ» | 616 «theorem ST_mainInd_of_regimes (d :»
RBM3D/Induction/ScaleFacts.lean: 193 «theorem scaleFacts_R1 (𝔠 𝔡 τ : ℝ) »
RBM3D/Induction/Step2Events.lean: 1355 «theorem STLWB_of_LWterm {d : ℕ} (h» | 1427 «theorem STLWT_of_LWtermExp {d : ℕ}»
RBM3D/Induction/Step2Iterate.lean: 1014 «theorem ST_one_sub_lemT {z : ℂ} (h» | 1793 «theorem ST_step2_of_pinsLW' {d : ℕ»
RBM3D/Induction/Step3.lean: 377 «theorem stStep3RegIII_holds : ∀ d » | 408 «theorem stStep3RegI_holds : ∀ d : » | 432 «theorem stStep3II_holds : ∀ d : ℕ,»
RBM3D/Induction/Step34Pins.lean: 184 «def STLKU (E s t : ℕ → ℝ) : Prop :»
RBM3D/Induction/Step4.lean: 209 «theorem ST_mainInd_of_pins' (d : ℕ»
RBM3D/Loop/GLoopFlow.lean: 260 «theorem Lloop_zero_one (n : ℕ) {E »
RBM3D/Loop/KLFinal.lean: 302 «theorem stKbound_of_flow (hd : 3 ≤»
RBM3D/Main/FixedZ.lean: 73 «def MAFixed : Prop := (∀ d : ℕ, UN» | 100 «theorem locSCFixed_of_ML (hML : ∀ » | 121 «obtain ⟨hLK, -, -, -, hLoc⟩ := hML» | 419 «theorem QDiffFixed_of_ML (hML : ∀ » | 444 «obtain ⟨hLK, -, hDec, hExp, -⟩ := » | 538 «theorem fixed_of_ML : MAFixed := f»
RBM3D/Test/Axioms.lean: 102 «[`RBM.Gauss.Sizes.STLK, -- (a) of » .. 107 «`RBM.Gauss.Sizes.STExp2, -- (d) `(» | 108 «`RBM.Gauss.Sizes.STMainInd, -- `le» | 142 «`RBM.BA.STLmaxgL, -- `(Eq:L-KGt2)`» .. 145 «`RBM.BA.STLocalMaxgL, -- `(Gt_boun» | 147 «`RBM.Gauss.Sizes.LWterm, -- `lem:L» | 149 «`RBM.Gauss.Sizes.LWtermExp, -- `le» | 179 «`RBM.Gauss.Sizes.STDuhamelII, -- i» | 191 «`RBM.Univ.UNMLOut, -- bulk univers» | 214 «`RBM.Univ.UNMLOutBA, -- bulk unive» | 239 «def structuralProps : List Name :=» | 317 «`RBM.Gauss.Sizes.STMainIndR, -- `l»
RBM3D/Universality/Pins.lean: 432 «def UNMLOut (d : ℕ) : Prop :=» | 793 «def UNOURow : Prop := (∀ d : ℕ, UN»
RBM2D/Evolution/Defs.lean: 138 «def MLExpConcl (E t : ℕ → ℝ) : Pro»
RBM2D/Induction/Chain.lean: 368 «theorem chainTarget (κ c τ : ℝ) : »
RBM2D/Induction/Defs.lean: 308 «def MLConcl (E : ℕ → ℝ) (t : ℕ → ℝ» | 318 «def chainTime (t : ℕ → ℝ) (n₀ k : »
RBM2D/Induction/ScaleFacts.lean: 171 «theorem chainStepCond (κ c τ : ℝ) » | 171 «theorem chainStepCond (κ c τ : ℝ) » .. 270 «exact ⟨key.mono fun n h => h.2, ke»
RBM2D/Universality/GUEPhase/EntryTail.lean: 108 «`b = 0` is the merged band stateme»
RBM2D/Universality/GUEPhase/Eq729B.lean: 1613 «theorem mlExp_of_pin (h7e : P7ExpO»
RBM2D/Universality/GUEPhase/PathBounds.lean: 254 «PathBounds_init_loops d t0 (gueGri» | 521 «have hinit := PathBounds_init_loca»
RBM2D/Universality/GUEPhase/RandomLayerA.lean: 738 «example (h7 : P7Out) (h7e : P7ExpO» | 748 «example (h7 : P7Out) :=»
RBM2D/Universality/GUEPhase/RandomLayerB.lean: 35 «(`E' = lemE z_n`, `t₀ = lemT z_n`,»
RBM2D/Universality/Pins.lean: 238 «def P7Out : Prop :=» | 250 «def P7ExpOut : Prop :=»
paper 1_2: 1194 «In the setting of \Cref{MR:locSC},» | 1204 «In the setting of \Cref{ML:GLoop},» | 1218 «In the setting of \Cref{ML:GLoop},» | 1221 «|(G_{t}-M)_{xy}|^2\prec W^{-d}B_{t» | 1240 «Before concluding this section, we» .. 1243 «Now, for $t>0$, we will establish » | 1256 «\begin{theorem}\label{lem:main_ind» .. 1305 «\end{theorem}» | 1261 «\item[(a)] {\bf $G$-loop estimate}» .. 1283 «\ee» | 1277 «\|G_{s}-M\|_{\max} \prec (W^{-d}B_» | 1296 «\begin{equation}\label{con_st_ind}» .. 1298 «\end{equation}» | 1299 «the estimates \eqref{Eq:L-KGt}--\e» .. 1304 «\ee» | 1309 «\begin{proof}[\bf Proof of \Cref{M» .. 1311 «\end{proof}» | 1400 «We remark that the estimates estab»
probe: 42 «/-- The six conclusions of `lem:ma» .. 59 «Flow sz κ ε 𝔠 𝔡 z → STConclgL (mk » | 42 «/-- The six conclusions of `lem:ma» .. 79 «noncomputable def stChainTime (t :» | 55 «/-- **R1 (base case)**: the six co» .. 59 «Flow sz κ ε 𝔠 𝔡 z → STConclgL (mk » | 61 «/-- **R2 (horizon)**: what the cha» .. 67 «∀ᶠ n in atTop, ((sz.size n : ℕ) : » | 69 «/-- **R3 (the ST-6 output)**: `ML:» .. 76 «STExp2gL (mk sz z) (law sz) t ∧ ST» | 78 «/-- The geometric chain `1 - p_k =» .. 79 «noncomputable def stChainTime (t :» | 81 «/-! ## 3. Row R1: the base case `t» .. 138 «end Base» | 86 «theorem bctl_nonneg (n : ℕ) (t : ℝ» .. 136 «STLocalEntrygL_zero _ _ (hG _ _ _ » | 97 «theorem STLKgL_zero (h : STLK0 C) » | 101 «theorem STLmaxgL_zero (h : STLK0 C» | 105 «theorem STDecaygL_zero (h : STLK0 » | 110 «theorem STDecayStronggL_zero (h : » | 115 «theorem STLocalEntrygL_zero (h : S» | 119 «theorem STExp2gL_zero [IsProbabili» | 126 «/-- **R1, generic**: the base case» .. 136 «STLocalEntrygL_zero _ _ (hG _ _ _ » | 140 «/-! ## 4. Row R3: mixing at the cl» .. 173 «end Mix» | 147 «theorem STLKgL_mix (h0 : STLKgL C » .. 171 «exacts [Or.inl ⟨u, by simpa [h] us» | 175 «/-! ## 5. Row R2: the chain times,» .. 240 «(hr.trans (by linarith [htT n])) (» | 175 «/-! ## 5. Row R2: the chain times,» .. 254 «_ < _ := pow_lt_pow_left₀ hp (mul_» | 183 «theorem stChainTime_facts {t : ℕ →» .. 195 «exact ⟨by linarith, by linarith, b» | 197 «/-- **The chain-step count**: if `» .. 240 «(hr.trans (by linarith [htT n])) (» | 242 «/-- **R2 (closure of the induction» .. 254 «_ < _ := pow_lt_pow_left₀ hp (mul_» | 244 «theorem STLocalMaxgL_of_STLocalEnt» .. 254 «_ < _ := pow_lt_pow_left₀ hp (mul_» | 256 «/-! ## 6. The assembly (generic ov» .. 315 «end Assembly» | 262 «/-- **R2**: the conclusions at eve» .. 287 «exact key K le_rfl» | 268 «obtain ⟨𝔠d, h𝔠d, -, H⟩ := hmain hd» .. 271 «obtain ⟨K, hK⟩ := exists_nat_ge (2» | 289 «/-- **R3**: every `0 ≤ t_n ≤ T0`: » .. 313 «STExp2gL_mix _ _ hs hm h0.2.2.2.1 » | 319 «/-- Band horizon: `0 < lemT z < 1`» .. 336 «linarith [(hf.2 n).2.1, ST_one_sub» | 338 «/-- **The owed identity** `𝓛_0 = 𝒦» .. 342 «(zt E 0) σ a - sz.STKloop n E 0 σ » | 338 «/-- **The owed identity** `𝓛_0 = 𝒦» .. 355 «exact sub_eq_zero.1 (hpriv sz n (h» | 344 «/-- Band base case from the three » .. 355 «exact sub_eq_zero.1 (hpriv sz n (h» | 357 «theorem unMLOut_iff (d : ℕ) : RBM.» .. 358 «(fun sz z => bandFM sz (STflowE z)» | 357 «theorem unMLOut_iff (d : ℕ) : RBM.» .. 362 «(unMLOut_iff d).2 (stMLOutG_of_mai» | 360 «/-- **The candidate target** `∀ d,» .. 362 «(unMLOut_iff d).2 (stMLOutG_of_mai» | 360 «/-- **The candidate target** `∀ d,» .. 369 «RBM.Univ.UNMLOutBA d := stMLOutG_o» | 364 «/-- **Route G**: `UNMLOutBA` is `S» .. 369 «RBM.Univ.UNMLOutBA d := stMLOutG_o» | 373 «/-- R4a: `STMainInd d` from exactl» .. 380 «(ST_step5_caseII_of_pins hEM hD2 (» | 373 «/-- R4a: `STMainInd d` from exactl» .. 387 «(fun n => (hT n).2) hr (fun n => h» | 382 «open RBM.Gauss.SizesInst RBM.Gauss» .. 387 «(fun n => (hT n).2) hr (fun n => h» | 389 «open RBM.Gauss.SizesInst RBM.Gauss» .. 392 «(fun n => (half_pos (lemT_pos (z0_» | 399 «#print axioms RBM.Probe.T2338.unML»
-- 147 distinct citations in 41 files; missing lines: 0
```
**B13 state of main after the branch base (read-only commands in the main worktree)** (run Thu Oct  8 17:03:04 UTC 2026)
```
$ TZ=UTC git log -3 (local time zone forced to UTC); grep -n 'theorem stDuhamelII_holds' RBM3D/Induction/DuhamelII.lean; grep -n 'Sizes.STDuhamelII,|Sizes.LWterm,|Sizes.LWtermExp,' RBM3D/Test/Axioms.lean; git diff --stat 3f750b6 HEAD -- RBM3D; head -3 docs/queue/T2339.state
0853ac1 Thu Oct  8 16:45:54 UTC 2026 T2339: merge S5-26 Induction/DuhamelII
f234507 Thu Oct  8 14:54:48 UTC 2026 T2336: merge BA-P4c BA/KHeatDiff
3f750b6 Thu Oct  8 14:52:24 UTC 2026 Dispatcher V1: DECISIONS §150 (T2297 Amend 1 with the LW engine; S5-26 = 
923:theorem stDuhamelII_holds (d : ℕ) : STDuhamelII d := by
registry lines of STDuhamelII, LWterm, LWtermExp on main:
147:   `RBM.Gauss.Sizes.LWterm, -- `lem:LWterm` (`3_5:385-404`): LW-01
149:   `RBM.Gauss.Sizes.LWtermExp, -- `lem: EWGn2_N` (`3_5:406-415`): LW-01, LW-16
 RBM3D/BA/KHeatDiff.lean        | 1757 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/DuhamelII.lean |  976 ++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    1 -
 3 files changed, 2733 insertions(+), 1 deletion(-)
state: merged 0853ac1
reason: audit PASS round 1 (claude-opus-5-5, t/T2339 at 9457596; stage 1b rerun under rule H after the usage-limit error); merged under rule (A), full lake build 4151 job
updated: Thu Oct  8 16:45:54 UTC 2026
```
