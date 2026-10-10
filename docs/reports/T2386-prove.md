Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 12:58:28 UTC 2026

Base: worktree `../RBM3D-wt/T2386` = `main` 61849a6 (the ticket measured at ada2b54). Scripts (Python, no Lean): `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2386`: `layout.py`, `inst.py`, `sz.py`, `decl.py`.

### (i) Table (the ticket has no exponents of its own; R1-R5 are its five stage-1a items, R6 the exponents of `LocalAvg`)

**R1 Layout and cones.** `python3 -I $S/layout.py ../RBM3D-wt/T2386 RBM3D.Induction.Step2Defs RBM3D.Chain.Carrier RBM3D.BA.FlowPins RBM3D.Induction.LocalAvg1`
```
RBM3D.Induction.Step2Defs: cone 177 modules / 207314 lines; LWExpCert* in cone: 6
RBM3D.Chain.Carrier: cone 39 modules / 33295 lines; LWExpCert* in cone: 0
RBM3D.BA.FlowPins: cone 38 modules / 33117 lines; LWExpCert* in cone: 0
RBM3D.Induction.LocalAvg1: cone 8 modules / 2854 lines; LWExpCert* in cone: 0
union of the four edited modules' cones: 43 modules / 35423 lines; LWExpCert*: 0
closure(Induction.Defs) contains Loop.GLoopFlow : True
closure(Induction.Defs) contains Loop.GLoop : True
closure(Induction.Defs) contains Defs.Block : True
closure(Induction.Defs) contains Defs.Semicircle : True
closure(Step2Defs+Carrier) contains RBM3D.Induction.Step2Events : False
closure(Step2Defs+Carrier) contains RBM3D.Induction.Step2Iterate : False
closure(Step2Defs+Carrier) contains LocalAvg1/FlowPins (cycle): False
```
Ticket table confirmed: Carrier and LocalAvg1 identical; Step2Defs 207,314 vs the ticket's 207,253, the +61 is `git diff --stat ada2b54 HEAD -- RBM3D` = `LoopGenN.lean 160 insertions, 99 deletions` (T2383). No text goes into `Step2Defs`; the merge rebuilds the union (43 modules plus the new file, about 10 module-minutes at design §2's 16.8 s per 1000 lines), no certificate: not the certificate lane. Two amendments, both inside the sole writable files:
- **A1** `Step2Gen` may import only `Chain.Carrier` and `Induction.Step2Defs`: `Step2Events` and `Step2Iterate` are not in that closure (above), `Step2Events` imports `Graph.LWPins` (`Step2Events.lean:7`). So `bandStep2Data.flowOK_T` re-proves `ST_flow_im_pos` (`Step2Events.lean:317`, 4 lines) as a private `Step2Gen_*` lemma, and `L_swap` (R3) re-proves the trace-cyclicity of `LocalAvg2.lean:100-121` privately.
- **A2** `STJhatg` and `STLWassmExpgL` (`FlowPins.lean:324-334`, namespace `RBM.BA`) move into `Step2Gen` with names unchanged: `STLWTgL` and `STEMn2ExpgL` read them, and `Step2Gen` cannot import `FlowPins` (which imports `Step2Gen`, target 4). `Carrier.lean:17-18` (docstring: "stay in `BA/FlowPins.lean`") is updated. `bandFM_STJhat` (`STJhat ... = STJhatg (bandFM ...)`, `rfl`) is added: no such bridge exists in `FlowPins` today.

**R2 Vocabulary of `Step2Defs`** (`awk`: 58 `def`, 11 `theorem` before line 870; the pilot's 49 names are only those referenced outside the chain). Band objects read: `L` = `loopFine (zt E u)`, `K` = `STKloop`, `m` = `mE`, `S` = `SB`/`Theta`, `G`/`M` = `Gt`/`mE`, `pathP`/`pathH`, `STFlow`/`lemT`/`STflowE`.
| class (names) | generic form | bridge |
|---|---|---|
| C0, 5: `STprof STPsiClass STScaleOk STScaleAdm STContractPt` read only `sz` (or an arbitrary `H, z`) | none, reused | none |
| C1, matrix level: `STmsig STJhatM STavgM STEGtM STELKLKM STthetaOp STEEkM STEEM` (`STLM` = field `LM`, `STLKM` = derived `Step2Data.LKM := LM - K`) | `STmsigg`, `STJhatMg`, ... over `Cm : Step2Data sz` | `rfl`; `STthetaOp`: `Theta d L g ξ := Ring.inverse (1 - ξ • SB d L g)` (`Propagator/Basic.lean:70`), generic `Ring.inverse (1 - ξ • C.S n)`, `rfl` by delta |
| C2, model level: `STJhat STEEk STInitialGT2 STLWassmExp` (exist: `STJhatg STEEg STInitialGT2gL STLWassmExpgL`), `STEGt STLWassm` (new `STEGtg STLWassmgL`) | over `C : FlowFM sz`, `μ` | `rfl` (`STLM_seqHflow` is `rfl`, `Step2Defs.lean:64`) |
| C3, Step 2 pins: `STStep2Local/Avg/Decay` and `PT`, `STStep2` | `...gL`; new `PrecPTL μ := Path.PerTimeDomAt μ sz.size`; `STStep2G` and the (c) family: probe 39-104, compiled (`T2379-prove.md:75-80`: `lake build` and `lake env lean`, exit 0) | `Iff.rfl` |
| C4, L pins and closing pins: `STLWB STLWT STEMn2Poly STEMn2Exp STL2decayPT STLocalAvgOfL2 STOptL2 STNetLift2 STScaleExists` | shape of `STStep2G`: `(law, Flow, mk, T0)`; `lemT (z n)` -> `T0 sz z n`, `etaT (STflowE z n) (t n)` -> `(mk sz z).eta n (t n)` | `Iff.rfl` |
| C5, grid: `STgA STgDrift STGridMartAt STGridMart STstopIdx` | full formula over `Hpath`, `Pp`, `LM`, `S`, `m` (not the pilot's opaque `ident`/`martTail`) | `Iff.rfl`; `STstopIdx_isStoppingTime` and the 8 measurability theorems: no generic form (no consumer in T8; T1/T7) |
| C6, GbEXP forms (`Induction/Defs.lean:92-98`, `:197-230`, not edited): `STindMax STgexRHS STGiiGEX STGijGEX STGavLGEX` | `STindMaxg STgexRHSg STGiiGEXgL STGijGEXgL STGavLGEXgL` | `Iff.rfl`, except `STGijGEXgL` (R4, F1) |
| **Deferred, 16**: `STGMM STNewKLKAt STNewKLK STK2decay` | quantify over every energy `E`, every `sz`, every `H` inside the pin; one `Step2Data` fixes `E`, so the band pin is stronger than the along-flow form: only `→`, no `Iff.rfl` | T3 (NewKLK) / T7 |
| **Deferred**: N-loop family, 12: `STLIM STLKIM STksimLKM STelklkM STavgErrM STegtM STeeM STgAN STgDriftN STeeUM STGridRepNAt STGridRepN` | read `KLK d L lam W E τ I` at list indices `I` (`cutGlue`), `ThetaN`, `uKer`, `UN`; `FlowFM.K` is indexed by `Fin k`: new fields needed, no T8 consumer reads them (they sit in `GridDuhamelN`, `Step2Iterate`: T1/T4/T5); adding them here costs about +200 lines, not in R5 | dispatcher to ratify |
`Iff.rfl` failure checks: `seqHflow` appears only through `STLM_seqHflow` (`rfl`); `pathH` only as the value of the field `Hpath`; `Classical.choose` only inside `msc`/`lemT`, which appears as the value of `T0` and is never unfolded; band `if`s (`STmsig`, `STGM`: `if x = y then mE E else 0`, `STEEkM`: `if k = 0`) are copied verbatim through `C.m`, `C.M`, `C.S`, so the bridge is `rfl`. The only failure is `STGijGEX` (F1).

**R3 `Step2Data` fields** (`extends FlowFM sz`). Kept, data: `T0 := fun n => lemT (z n)`, `flowOK := STFlow sz · · · · z`, `LM := STLM sz n (STflowE z n)`, `Pp := pathP sz`, `Hpath := pathH sz`, `toFlowFM := bandFM sz (STflowE z)`: all by definition (`rfl`). Kept, base facts: `flowOK_adm := fun h => h.1` (`STFlow := Admissible ∧ ...`, `Defs.lean:286`); `flowOK_T` (`0 < κ -> flowOK -> T0 n < 1`: `lemT_lt_one` + private `Im z > 0`; at BA it needs `0 < κ`); `L_swap` (new: `L n t ![true,false] ![a,b] ω = L n t ![false,true] ![b,a] ω`; band and `BALloop` (`FlowPins.lean:263-265`) are `loopFine` of a matrix, trace commutes). Not kept (no T8 text reads them): `μ` (the pins take `μ` as an argument, ticket (d)), `E`, `Hflow`, `imLow`, `flowOK_m`, `imLow_pos`, `LKM_eq`, `LKM_meas`, `ident`, `martTail`, `pLWT`, `pEMe`, `pNew` (left for T1), `ev1`-`ev4`, `Good` (left for T7), added there by `extends`. **F1:** `M_offdiag` is NOT a field: `la2_stGM_ne` (`LocalAvg2.lean:241`) needs `M` diagonal, but at BA `M = BAMfine = Mres ((lam0 n) • PsiI) ...` (`FlowPins.lean:254-255`) `= Ring.inverse (H0 - (z+m) • 1)` (`GLoopFlow.lean:81-82`) with `PsiI` the hopping matrix (`BlockAnderson.lean:52`); `BAMfine_eq` (`GreenSchur.lean:93-99`) gives `M_xy = 1(same offset) M^{(B)}_{[x][y]}`, off-diagonal blocks bounded by a decaying profile (`BAMfine_decay`, :124-130), nothing says they vanish. So `STGijGEXgL` is stated for `‖C.GM ..‖^2` and the band corollary converts the band `STGijGEX` (`‖Gt ..‖^2`, `Defs.lean:210`) by `STGM = Gt` off the diagonal inside `StochDomAt` (a proof, not `Iff.rfl`).

**R4 `LocalAvg1/2`** (grep over `RBM3D/`, `RBM3D.lean`, `docs/tickets/checks`). Read no model object, unchanged: `localAvg1_{stochDomAt_of_whp, domAt_of_le_const, perTime_of_stoch, STWB_le, STWB_ge, STWB_comp, rpow_half_sq, det}`, `stLocalPsi`. Outside users: `localAvg1_STWB_le` (`Graph/LWExpTerm3`, `Induction/MainIndChain`, `MainIndRegimes`), `stLocalAvgOfL2_holds` (`MainIndHolds`, `MainIndOut`); the other band names only the check file. Step2Iterate names the two files use (script over its top-level names): `ST_Bdata_holds` (`Step2Iterate.lean:1049`) and, in instance examples only, `hs0 hst htT`, `ST_step2_of_pins`, `ST_step2_of_pins'`.
| band theorem (file:line) | generic form (in place, `Cm : Step2Data sz`, `μ`) | facts as arguments (band discharge) | corollary |
|---|---|---|---|
| `localAvg1_whp_L2` (LA1:258), `_whp_omega` (:298), `_maxLoop2_le` (:318), `localAvg2_rhs_le` (LA2:126), `_entry_le` (:249); no outside user | `...G` over `C : FlowFM sz`, `μ` | `L_swap` (rhs_le) | old name and statement, at `bandFM sz (fun _ => E)` |
| `stInitialGT2_of_L2decay` (LA1:343) | `...G`, conclusion `STInitialGT2gL` | `hdat`: `∃ cB c > 0, ∀ t ≤ Cm.T0, ∀ᶠ n, ∀ u ≤ t n, cB W^{-d} ≤ Bctl ≤ N^{-c}` (band: `localAvg1_data` :238 from `ST_Bdata_holds`); `flowOK_adm`, `flowOK_T` | `bandStep2Data sz z`, `seqP sz` |
| `stStep2AvgPT_of_L2decay` (LA1:406) | `...G`, `STStep2AvgPTgL` | `hdat`, `hGav : STGavLGEXgL` for `u ≤ T0` (band: `(Green.stGbEXP_holds hd).2.2`, `GbEXP.lean:811`) | same |
| `stStep2LocalPT_of_L2decay` (LA2:321) | `...G`, `STStep2LocalPTgL` | `hdat`, `hGii`, `hGij` (GM form), `L_swap` (band `.1`, `.2.1`) | same |
| `stLocalAvgOfL2_holds` (LA2:394) | `...G` + pin `STLocalAvgOfL2gL d law Flow mk T0` | the above as `∀`-flow hypotheses | `stLocalAvgOfL2_holds` at `bandStep2Data` |
G1 list for the check file: the 5 helper names, the 4 theorems, `stLocalPsi`, `localAvg1_STWB_le`, `bandFM`, the 13 existing `bandFM_*` bridges (`grep -c '^theorem bandFM_' RBM3D/BA/FlowPins.lean` = 13), and every new bridge.

**R5 Predicted lines** (stop line 1,500; `sz.py`: the band definitions to restate total 204 lines (C1-C5) + 30 (C6); `decl.py`: 115 lines of the 12 band-reading `LocalAvg` declarations mention a band object). Reading of "net diff": insertions minus deletions; the gross reading (insertions plus deletions) is also given.
| piece | low / central / high | basis |
|---|---|---|
| new `Step2Gen.lean` | 650 / 760 / 900 | generic defs about 1.3x the band text + one-line docstrings 310, C6 50, probe family 66, bridges about 105, moved defs 14, `Step2Data` 45, `bandStep2Data` 30, header 40, instances 70 |
| `LocalAvg1/2` in place, net | 110 / 160 / 230 | 9 generic statements 80, hypotheses 20, corollary bodies 54, conversion lemma 15 |
| `FlowPins`, `Carrier`, `Axioms`, `RBM3D.lean` | -17, +12, +1, +1 | -8 `bandFM` block, -14 moved defs, +1 import, +4 `BAStep2` |
| **total, net** | **775 / 917 / 1,150** | ticket estimate 700 / 1,000 / 1,400 |
| total, gross | 1,000 / 1,180 / 1,480 | `LocalAvg` gross about 380 |
Both readings are at most 1,500: no split into T8a/T8b. Registry: `scanPremises` (`Test/Axioms.lean:389-433`) fails the build for a `Prop` definition that a theorem assumes and no theorem concludes: expect 4 more `owedProps` lines than the ticket's one (`STL2decayPTgL`, `STGiiGEXgL`, `STGijGEXgL`, `STGavLGEXgL`); `BAStep2` is assumed by no theorem (the pre-check decides).

**R6 Constants of `LocalAvg`** (instance values `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ 0`, `t ≡ 1/16`).
| constant | value | constraint | slack |
|---|---|---|---|
| `cB` | `(𝔡^{-2}+1)^{-1} = 1/101` | `cB W^{-d} ≤ W^{-d} B_{u,0}` | `B_{0,0} ≥ (lam²+1)^{-1}`, script column `cB` |
| `c` | `min(2𝔡𝔠, ε) = 1/30` (instance choice from `W^{-d}B ≤ W^{-2𝔡} + 4N^{-ε}`, `Step2Iterate.lean:1046-1048`; the theorem's `c` is existential) | `W^{-d} B_{t,0} ≤ N^{-c}` | `N^{-c}/(W^{-3}B)` ≥ 1.9e4 (n=0) |
| `ε₀` | `min(1/2, dc/8) = 1/80` | `ε₀ ≤ 1/2`, `ε₀ ≤ dc/8` | 39/80, 0 (the minimum) |
| `(E)` | `N^{c/8} B^{1/4} ≤ W^{-ε₀}` | at `u = t` | ratio ≥ 12 (n=0) |
| `CΨ` | `cB^{-1}+1 = 102` | `B ≤ Ψ² ≤ CΨ B`, `Ψ = max(W^{-d/2}, B^{1/2})` | script column `win` |
| `C_ij` | `2·3^d·3^d·3^{d-2} + 2^{d-2} cB^{-1} = 4576` | `C_ij ≤ N^{τ/3}` eventually in `n` (a conclusion threshold, not a hypothesis) | least `n`: 1 (τ=1), 7 (τ=1/2), 561,834 (τ=1/10) |

### (ii) One concrete nondegenerate instance
Data of the merged `sz0` (`Induction/Defs.lean:392-394`): `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`, `z_n = 1/2 + i N_n^{-4/5}`. Hypotheses of the targets at once: `3 ≤ d`; `Admissible` (`W ≥ N^𝔠`, `W^{-d/2+𝔡} ≤ lam ≤ 𝔡^{-1}`); `locDomain` (`|Re z| ≤ 2-κ`, `N^{-1+ε} ≤ Im z ≤ 1`); `0 ≤ s ≤ t ≤ T0 = lemT(z_n) < 1`; the size data `hdat` with `cB, c` of R6; the window; `flowOK_T`. Kept as hypotheses of the examples (other gates' outputs, as in `LocalAvg1Inst`): `STStep1WeakgL`, `STL2decayPTgL`; the GbEXP forms are discharged at the band by the merged `stGbEXP_holds`. `BAStep2 3` is a `Prop` with no numeric hypothesis. `python3 -I $S/inst.py`:
```
cB=1/101=0.00990 c=min(2*dd*cc,eps)=1/30=0.03333 eps0=min(1/2,dc/8)=0.01250 CPsi=102 Cij=4576
n=   0 N=1e 6.3 adm,WO,loc,cB,c,(E),win=1111111 slack W/N^(1/6)=2.83 N^-c/(W^-3B)=1.9e+04 W^-e0/(N^(c/8)B^.25)=12
n=   1 N=1e11.7 adm,WO,loc,cB,c,(E),win=1111111 slack W/N^(1/6)=11.3 N^-c/(W^-3B)=4.1e+08 W^-e0/(N^(c/8)B^.25)=1.5e+02
n=   2 N=1e14.9 adm,WO,loc,cB,c,(E),win=1111111 slack W/N^(1/6)=25.5 N^-c/(W^-3B)=1.4e+11 W^-e0/(N^(c/8)B^.25)=6.3e+02
n=  10 N=1e25.1 adm,WO,loc,cB,c,(E),win=1111111 slack W/N^(1/6)=342 N^-c/(W^-3B)=1.9e+19 W^-e0/(N^(c/8)B^.25)=6.9e+04
n= 100 N=1e42.4 adm,WO,loc,cB,c,(E),win=1111111 slack W/N^(1/6)=2.89e+04 N^-c/(W^-3B)=1.4e+33 W^-e0/(N^(c/8)B^.25)=2.1e+08
n=1000 N=1e60.3 adm,WO,loc,cB,c,(E),win=1111111 slack W/N^(1/6)=2.83e+06 N^-c/(W^-3B)=3e+47 W^-e0/(N^(c/8)B^.25)=8.2e+11
n=0: lemT(z_n)=0.999990948752  1/16<=lemT<1: True
n=1: lemT(z_n)=0.999999999581  1/16<=lemT<1: True
n=2: lemT(z_n)=0.999999999999  1/16<=lemT<1: True
tau=1.0: least n with Cij<=N^(tau/3): 1
tau=0.5: least n with Cij<=N^(tau/3): 7
tau=0.1: least n with Cij<=N^(tau/3): 561834
ALL HYPOTHESIS CHECKS: True
```
Limit computation for the non-merged-at-BA inputs (`hdat`; the three GbEXP forms are band theorems here, with no numeric content): `N = 128 (n+1)^6` cubed, so `N^{-c} = N^{-1/30} ~ (n+1)^{-3/5}` while `W^{-3} B_{t,0} <= 1.1 (2(n+1))^{-15} ~ (n+1)^{-15}`; the ratio `N^{-c}/(W^{-3}B)` grows like `(n+1)^{14.4}` (column above: 1.9e4 at n=0 to 3e47 at n=1000), and `W/N^{1/6} ~ (n+1)^2` (2.83 to 2.83e6). All hypotheses hold at every `n` tested; only the conclusion's `≺` threshold `n_0(τ)` depends on `τ`.

### Verdicts
- Target 1 (`bandFM` into `Carrier`): **PASS**. Its ingredients are in `closure(Induction.Defs)` (R1); no new import.
- Target 2 (`Step2Gen`, (a)-(d)): **PASS** with A1, A2 and the 16 deferred names of R2 (4 energy-quantified pins, 12 N-loop names) for the dispatcher to ratify in the 1a-audit; the vocabulary bridges are `rfl`/`Iff.rfl` except `STGijGEX` (F1).
- Target 3 (`LocalAvg1/2`): **PASS** with F1 (`M_offdiag` is not a field; `STGijGEXgL` in `GM` form) and the only T1 input `ST_Bdata_holds`.
- Target 4 (`BAStep2` in `FlowPins`): **PASS** (probe 95-96 compiled, `T2379-prove.md:75-80`; `BAFlow`, `baFMz`, `BAflowT0` have the shapes `STStep2G` takes).
- Targets 5-7 (G1 checks, instances at `d = 3`, registry): **PASS**; registry needs about 4 more `owedProps` lines (R5). Stop line: predicted 917 net / 1,180 gross, at most 1,500.

## (a′) Preflight corrections under Amend 1 (`docs/tickets/T2386-amend-1.md`, R1; round-1 1a-audit R1/R3, O1-O5) — Sat Oct 10 15:28:13 UTC 2026

Section (a) is unchanged except where this section says so. Scripts (Python, no Lean) in `S/a1/`: `nl.py`, `pred.py`, `sz16.py`. Worktree still `61849a6`; `Step2Defs.lean` is not edited, so the layout and cones of (a) R1 are unchanged (`Step2Gen` imports only `Chain.Carrier` and `Induction.Step2Defs`; the 16 names and every kernel they read (`KLK`, `ThetaN`, `UN`, `uKer`, `blockMat`) are already in that closure because `Step2Defs` itself defines them from these).

**C1. `Step2Data` fields, revised (replaces (a) R3's field list; items 1 and 3 of the amend).** The three energy-quantified pins (`STNewKLKAt`, `STNewKLK`, `STK2decay`) quantify over every `E : ℝ` and every `sz`, and `lemE z` is `-2 Re(msc z)/‖msc z‖` (`Defs/Semicircle.lean:190`), not `Re z`, so a family `mk sz z` cannot be instantiated at an arbitrary `E` by `rfl`. A `Step2Data`-valued family at an arbitrary `E` would also need `flowOK_T`, which holds only along a flow `z`. So the data fields go into a fact-free layer, one structure inside the same file (`FlowFM` is not changed):
- `structure Step2Mat sz extends FlowFM sz` (data only): `LM` (the `𝓛^{(k)}` of a fine matrix; band `STLM sz n (E n)`), `GMM` (**new, the `STGMM` datum**: `(G_u-M)_{xy}` of a fine matrix; band `STGMM sz n (E n)`), `LIM`, `KI` (**new, list-indexed**: `𝓛_{τ,I}` of a fine matrix, band `STLIM sz n (E n)`, and `KLK d (sz.L n) (sz.lam n) (sz.W n) (E n) τ I`), `Pp := pathP sz`, `Hpath := pathH sz`. All band values by `rfl`; derived `LKM := LM - K`, `LKIM := LIM - KI`.
- `structure Step2Data sz extends Step2Mat sz`: `T0 := fun n => lemT (z n)`, `flowOK := STFlow sz · · · · z`, and the facts `flowOK_adm`, `flowOK_T`, `L_swap` of (a) R3 (unchanged).
- `bandStep2Mat sz (E : ℕ → ℝ) : Step2Mat sz` (`toFlowFM := bandFM sz E`), `bandStep2Data sz z := {bandStep2Mat sz (STflowE z) with T0, flowOK, facts}`.
- N-loop kernels are **not** fields. `ThetaN`, `UN`, `uKer`, `thetaKer` read only `SB d L (sz.lam n)` (`Kernel/Evolution.lean:51-67`) and `Theta ξ = Ring.inverse (1 - ξ • SB d L g)` (`Propagator/Basic.lean:70`); none of `Kernel/Evolution`, `Propagator/Basic`, `Loop/KLTree`, `Defs/Semicircle` contains `irreducible` (grep, no output). So `Step2Gen_thetaKer S μ t := (μ • S) * Ring.inverse (1 - ((t:ℂ)*μ) • S)`, `Step2Gen_ThetaN`, `Step2Gen_uKer`, `Step2Gen_UN` are written over `Cm.S n` (as `STthetaOpg` already is), with bridge `rfl` by delta. At BA `S = I` then gives the BA kernels with no extra field. The one-loop charge `mSigma E σ` (`Semicircle.lean:85`) has the same body as `STmsig E σ` (`Step2Defs.lean:56`); generic `STmsigg Cm n σ := if σ then Cm.m n else conj (Cm.m n)` serves both.
Fields of the pilot's 19 left for T7 / T1 (added there by `extends Step2Data`): `ev1`-`ev4`, `Good` (T7), `ident`, `martTail`, `pLWT`, `pEMe`, `pNew` (T1); not kept (no T8 text reads them): `E`, `Hflow`, `imLow`, `LKM` (now derived), and the base facts `flowOK_m`, `imLow_pos`, `LKM_eq`, `LKM_meas`. Band values filled by `rfl`: every data field above, `T0`, `flowOK`, `flowOK_adm := fun h => h.1`.

**C2. The 16 generic forms (R1; amend items 1-3).** None is deferred; the bridge kind is `rfl` / `Iff.rfl` for all 16 (no `→`). For the `Iff.rfl` claim I checked, by reading the band bodies (`Step2Defs.lean:146-148, 363-378, 568-572, 713-854`), that each band object read is either a `Step2Mat` field value at the band instance, `sz`-only, or a plain `def` (no `Classical.choose`, `seqHflow`, `pathH` unfolding, or band-specific `if` is crossed: the `if`s are `if x = y`, `if 1 ≤ ℓ`, `if k = 0`, copied verbatim). 1b confirms by compiling.
| band name | band objects read | generic form | bridge |
|---|---|---|---|
| `STGMM` | `Gres H (zt E u)`, `mE E` | `STGMMg Cm n u H x y := Cm.GMM n u H x y` | `STGMM sz n (E n) u H x y = STGMMg (bandStep2Mat sz E) n u H x y`, `rfl` |
| `STNewKLKAt` (12 lines) | `STGMM`, `STthetaOp`, `STELKLKM`, `STJhatM`, `STprof`, `lam`, `L` | `STNewKLKAtgL d κ 𝔡 C δ₀ (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz)`: the pin's `∀ sz n E ...` stays, every band object is read from `mk sz (fun _ => E)` | `Iff.rfl` at `mk := bandStep2Mat` (`(fun _ => E) n` reduces by β) |
| `STNewKLK` | `STNewKLKAt` | `STNewKLKgL d mk` | `Iff.rfl` |
| `STK2decay` | `STKloop`, `STprof` | `STK2decaygL d mk`, reads `(mk sz (fun _ => E)).K` | `Iff.rfl` |
| `STLIM`, `STLKIM` | `loopL`, `blockMat`, `KLK` | `Cm.LIM`, `Cm.LIM - Cm.KI` | `rfl` |
| `STksimLKM`, `STelklkM` | `STLKIM`, `KLK`, `SB`, `cutGlue*` | same text with `Cm.LKIM`, `Cm.KI`, `Cm.S n` | `rfl` |
| `STavgErrM`, `STegtM`, `STeeM` | `STLIM`, `mSigma`, `SB`, `STeeLoop` | with `Cm.LIM`, `STmsigg`, `Cm.S n` | `rfl` |
| `STgAN`, `STgDriftN` | `STLKIM`, `pathH`, `gridTime`, `KLloopOf`, `ThetaN`, `mSigma` | `Cm.Hpath`, `Step2Gen_ThetaN (Cm.S n)` | `rfl` |
| `STeeUM` | `uKer`, `cycProd`, `mSigma`, `STeeM` | `Step2Gen_uKer (Cm.S n)` | `rfl` |
| `STGridRepNAt`, `STGridRepN` | `pathP`, `pathH`, `STgAN`, `STgDriftN`, `STeeM`, `STeeUM`, `UN`, `STflowE`, `STFlow`, `lemT` | `STGridRepNAtgL d m C₀ Flow (mk : ∀ sz z, Step2Mat sz) T0` (shape of `STStep2G`; `STflowE z n` becomes `(mk sz z).m`/`.S`, `pathP sz` becomes `(mk sz z).Pp`) | `Iff.rfl` at `Flow := STFlow`, `mk := fun sz z => bandStep2Mat sz (STflowE z)`, `T0 := fun _ z n => lemT (z n)` |
`STGridMartAt/STGridMart/STgA/STgDrift` of (a) C5 take the same `(Flow, mk : Step2Mat, T0)` shape, since they read only `Pp, Hpath, LM, S, m`. Risk flagged for 1b, not asserted: `Iff.rfl` on the 34-line `STGridRepNAt` is the heaviest defeq check; the fallback is `Iff.intro id id`/`unfold`, still no proof content.

**C3. Instance for the new pins (the (a)(ii) data, `d = 3`, `κ=ε=𝔡=1/10`, `s≡0`, `t≡1/16`, `z_n = 1/2 + i N_n^{-4/5}`).** Hypotheses of `STNewKLKAt`/`STK2decay` (`0 < lam ≤ 𝔡⁻¹`, `|E| ≤ 2-κ`, `0 ≤ u < 1`, `0 ≤ D`, `0 ≤ ℓ ≤ L`) at `u=D=ℓ=0`, `E = lemE z_n`, and of `STGridRepNAt` (`m=2`, `D=1`, `K_n = ⌈N_n⌉ ≠ 0`, `N_n^{CK} ≤ K_n` at `CK=1`, `s ≤ t ≤ lemT z_n`, grid step `Δ>0`); the conclusions' `C, δ₀, CK, C₀` are existential. `python3 -I S/a1/nl.py`:
```
n= 0 lam=1.562e-02 1/dd=10 E_n=lemE(z_n)=+0.500000 2-kap=1.9 L=4 K_n=ceil(N^1)=1e6.32 Delta=2.98e-08 t<=lemT=0.999990948752  newKLK/K2decay/grid hyps: True
n= 1 lam=2.441e-04 1/dd=10 E_n=lemE(z_n)=+0.500000 2-kap=1.9 L=8 K_n=ceil(N^1)=1e11.74 Delta=1.14e-13 t<=lemT=0.999999999581  newKLK/K2decay/grid hyps: True
n= 2 lam=2.143e-05 1/dd=10 E_n=lemE(z_n)=+0.500000 2-kap=1.9 L=12 K_n=ceil(N^1)=1e14.91 Delta=7.69e-17 t<=lemT=0.999999999999  newKLK/K2decay/grid hyps: True
n=10 lam=8.820e-09 1/dd=10 E_n=lemE(z_n)=+0.500000 2-kap=1.9 L=44 K_n=ceil(N^1)=1e25.07 Delta=5.36e-27 t<=lemT=1.000000000000  newKLK/K2decay/grid hyps: True
ALL NEW-PIN HYPOTHESIS CHECKS: True
```
Limit: `lam_n = (2(n+1))^{-6} -> 0` stays below `𝔡⁻¹ = 10`; `E_n = lemE z_n` is `0.500000` at every tested `n` (so `|E_n| <= 1.9`); `Delta_n = (1/16)/⌈N_n⌉ -> 0` but positive. The compiled examples (1b) are the bridge `Iff.rfl`s at `bandStep2Mat sz0 (fun _ => 0)` and `bandStep2Data sz0 z0` (no numeric hypothesis), as in the ticket's item 6.

**C4. Revised line prediction (amend item 4).** `python3 -I S/a1/sz16.py; python3 -I S/a1/pred.py` (tail):
```
total body lines of the 16: 112     (STGMM 3, energy3 19, N-loop 12 names 90)
(a) rows recomputed total net: [757, 917, 1127]  (a) states 775/917/1150
Amend-1 additions (all in Step2Gen/Axioms): [215, 268, 333]
revised net total low/central/high: [972, 1185, 1460]  stop line 1500; margin at high: 40
new file alone:  [861, 1023, 1228]
```
Correction of (a) R5: its rows sum to 757 / 917 / 1,127 (low and high), not 775 / 1,150; the central is unchanged. The additions are 16 generic defs with docstrings 128/162/195, kernel helpers 12/16/22, `Step2Mat` and band instances 25/29/38, 16 bridges 32/36/45, 16 instance examples 14/20/28, owed lines 4/5/5. Net reading (the ticket's stop line, `wc -l` of the new file plus the net diff of the edited files): **972 / 1,185 / 1,460, at most 1,500 in all three cases, margin 40 at the high case**. Gross reading ((a) R5 gross row plus the additions): 1,215 / 1,448 / 1,813; the high case exceeds 1,500 on this reading, which the ticket does not use. No RETURN with a split. If the new file passes about 1,230 lines during 1b, the split T8a (targets 1, 2, 4: new file 861 / 1,023 / 1,228 plus the small edits) and T8b (target 3: 110 / 160 / 230 net) is the fallback, since `LocalAvg1/2` do not depend on the 16 names. Rebuild cones unchanged (a) R1: 43 modules plus the new file, no `LWExpCert*`.

**C5. Observations.**
- **O1 not applied as stated; fact checked.** The pilot structure does have a `μ` field: `git show t/T2326:RBM3D/Probe/T2326PilotStep2.lean` line 75 is `  μ : Measure sz.SeqΩ`; the structure's fields are the 18 names `E T0 Pp Hflow Hpath LKM flowOK imLow ev1 ev2 ev3 ev4 Good ident martTail pLWT pEMe pNew` (awk over lines 69-178) plus `μ` = 19, matching the ticket's "19 fields + 6 base facts". So (a) R3 "not kept: `μ`" is true: `μ` is a pilot field that `Step2Data` does not keep, since every generic pin takes the law as an argument `(law)`/`μ` (ticket (d), `bandStep2Data … (seqP sz)`). The 1a-audit's O1 count of the pilot fields omitted `μ`. The dispatcher may confirm.
- **O3 (accepted).** The G1 list also elaborates the moved `STJhatg`, `STLWassmExpgL` and `bandFM_STLWassmExp` (`FlowPins.lean:381`; 13 `bandFM_*` bridges there, `grep` of `^theorem bandFM_` lines 359-384), plus the 16 new bridges and the three `Step2Mat` data bridges.
- **O4 (registry).** `scanPremises` (`Test/Axioms.lean:389-433`) lists a `Prop` definition that some theorem assumes and no theorem concludes (conclusion head); an `Iff` bridge has head `Iff`, so it does not count. The 16 new pins are assumed by no theorem: no owed line. Owed lines only if the pre-check requires them, for the four generic LocalAvg premises (`STL2decayPTgL`: owner T1; `STGiiGEXgL`, `STGijGEXgL`, `STGavLGEXgL`: owner BA stage G, G6b / G7), plus `BAStep2`; H23 (b) union.
- **O5 (instruction to 1b).** Record the `GM` form of `STGijGEXgL` ((a) F1) as paper-delta candidate `T2386a` in `(d)` of the prove report, not in `paper-deltas.md`.
- Name check on the worktree (`grep -rlw` over `RBM3D`, `RBM3D.lean`): `Step2Mat`, `bandStep2Mat`, `bandStep2Data`, `Step2Data`, `STGMMg`, `STNewKLKAtgL`, `STNewKLKgL`, `STK2decaygL`, `STGridRepNAtgL`, `STGridRepNgL`, `STLIMg`, `STLKIMg`, `STksimLKMg`, `STelklkMg`, `STavgErrMg`, `STegtMg`, `STeeMg`, `STgANg`, `STgDriftNg`, `STeeUMg`, `Step2Gen_thetaKer`, `Step2Gen_uKer`, `Step2Gen_ThetaN`, `Step2Gen_UN`: 0 files each.

**Verdicts under Amend 1** (supersede the target 2 line of (a) Verdicts; others unchanged). Target 2 (`Step2Gen` (a)-(d)): **PASS**, all 58 `Step2Defs` definitions now have a generic form or are `sz`-only/reused (C0), none deferred; bridges `rfl`/`Iff.rfl` except `STGijGEX` (F1). Targets 1, 3-7: **PASS** as in (a). Predicted net 972 / 1,185 / 1,460 against the stop line 1,500.

## (a′) Preflight corrections, stage 1b addendum — Sat Oct 10 16:18:28 UTC 2026

- (a) R5 and (a′) O4 expected four more `owedProps` lines, `BAStep2` only if required.  The registry scan of the first whole-library `lake build` listed six premises (`RBM.BA.STL2decayPTgL`, `STStep1WeakgL`, `STGavLGEXgL`, `Step2Data.flowOK`, `STGijGEXgL`, `STGiiGEXgL`; `scratchpad/T2386/b/full1.log:4308-4314`): the four of the amend, `STStep1WeakgL` (hypothesis of every generic `LocalAvg` theorem) and the field projection `Step2Data.flowOK` (entered in `structuralProps`).  `BAStep2` is assumed by no theorem and needs no line.  No verdict changes.
- (a) C4 gives `STScaleExists` the shape `(law, Flow, mk, T0)`; `STScaleExistsgL` reads only the setting and the horizon, so it is `STScaleExistsgL d Flow T0`.  (a) A2 puts `bandFM_STJhat` in the moved block; it is in `Chain/Step2Gen.lean` next to `STJhatg`, not in `BA/FlowPins.lean`.

## (b) Script output (stage 1b; the scripts are `scratchpad/T2386/b/report_b.sh` and the Python files it calls; Python with `-I`)

```
$ date -u
Sat Oct 10 16:16:59 UTC 2026
$ python3 -I $S/layout.py . RBM3D.Induction.Step2Defs RBM3D.Chain.Step2Gen ... | grep -e Step2Defs -e Step2Gen -e union   (reverse cones on the branch)
RBM3D.Induction.Step2Defs: cone 178 modules / 208612 lines; LWExpCert* in cone: 6
RBM3D.Chain.Step2Gen: cone 43 modules / 36543 lines; LWExpCert* in cone: 0
union of the four edited modules' cones: 44 modules / 36732 lines; LWExpCert*: 0
$ git diff --numstat 61849a6 HEAD   (ins del file), then the stop-line arithmetic
1 0 RBM3D.lean; 14 30 RBM3D/BA/FlowPins.lean; 12 1 RBM3D/Chain/Carrier.lean; 986 0 RBM3D/Chain/Step2Gen.lean; 215 72 RBM3D/Induction/LocalAvg1.lean; 258 73 RBM3D/Induction/LocalAvg2.lean; 7 0 RBM3D/Test/Axioms.lean; 
ins 1493 del 176; new file 986; in-place net 331; STOP LINE 1500, net reading (ticket, (a') C4): 1317; gross reading: 1669
$ git diff main...t/T2386 --name-only | tr "\n" " "; git diff main...t/T2386 -- RBM3D/Induction/Step2Defs.lean | wc -l
RBM3D.lean RBM3D/BA/FlowPins.lean RBM3D/Chain/Carrier.lean RBM3D/Chain/Step2Gen.lean RBM3D/Induction/LocalAvg1.lean RBM3D/Induction/LocalAvg2.lean RBM3D/Test/Axioms.lean 
       0
$ git log --oneline 61849a6..HEAD   (branch t/T2386, base 61849a6)
3297200 T2386: instances for the generic LocalAvg helpers (checkpoint 4);580481f T2386: module docstrings, header tidy (checkpoint 3);f465c49 T2386: registry lines for the generic LocalAvg inputs (checkpoint 2);43a1a8f T2386: Step2Gen vocabulary over the carrier, bandFM into Carrier, LocalAvg1/2 generic restatements (checkpoint 1);
$ lake build RBM3D.Chain.Step2Gen RBM3D.Induction.LocalAvg2 RBM3D.BA.FlowPins 2>&1 | tail -1
Build completed successfully (3807 jobs).
$ lake build 2>&1 | tail -1   (whole library: #assert_rbm_axioms and the registry scan of Test/Axioms.lean)
Build completed successfully (4200 jobs).
$ lake env lean $S/b/axioms.lean   (#axs over the new public declarations: Step2Gen, the moved bandFM, the generic and band theorems of LocalAvg1/2, BAStep2, the instance lemmas)
declarations checked: 149; standard-axiom lines (propext, Classical.choice, Quot.sound only): 149; NONSTANDARD lines: 0
RBM.BA.bandStep2Data: [propext, Classical.choice, Quot.sound] OK
RBM.Gauss.Sizes.stInitialGT2_of_L2decayG: [propext, Classical.choice, Quot.sound] OK
RBM.Gauss.Sizes.stLocalAvgOfL2_holdsG: [propext, Classical.choice, Quot.sound] OK
RBM.Gauss.Sizes.stStep2AvgPT_of_L2decayG: [propext, Classical.choice, Quot.sound] OK
RBM.Gauss.Sizes.stStep2LocalPT_of_L2decayG: [propext, Classical.choice, Quot.sound] OK
$ lake env lean docs/tickets/checks/T2386-check.lean | grep -c error   (dispatcher check file, on the branch)
0
$ git diff --stat 61849a6 main -- <the 5 Lean files>; then G1: g1.lean = #check of 36 public declarations (19 of LocalAvg1/2, bandFM, STJhatg, STLWassmExpgL, 13 bandFM_*, STMainInd_iff); diff of the outputs, main worktree vs branch
       0
36 checks; lines main      197, branch      197; diff: IDENTICAL
$ python3 -I $S/b/cover.py   (every public def of Step2Defs.lean has a generic form or is sz-only)
Step2Defs.lean public defs: 58 with a generic form: 53 without: [] 
$ bridges.py (bridge theorems of Step2Gen.lean by proof kind; the 16 names of Amend 1; bandFM moved)
bridge theorems in Step2Gen.lean: 59 = rfl 28 + Iff.rfl 30 + proved ['bandFM_STGijGEX']
Amend 1 names with a generic def in Step2Gen.lean: 16 of 16
FlowPins.lean: theorem bandFM_*: 13 ; def bandFM: 0 ; Carrier.lean def bandFM: 1
$ clash.sh   (each new name incl. private ones, whole-word grep over RBM3D/ and RBM3D.lean outside the 7 writable files)
6 bandFM names checked: 152; names found in another file: 1 
$ added lines of the 6 Lean files matching sorry|admit|native_decide|axiom
0
$ extract_full.py / extract.py (declarations extracted from the files by script, one line each; the four theorem heads end at `:=`)
def bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : FlowFM sz where L := fun n t {_k} σ a ω => Lloop sz n (E n) t σ a ω K := fun n t {_k} σ a => STKloop sz n (E n) t σ a G := fun n t ω x y => Gt sz n (E n) t true ω x y M := fun n x y => if x = y then mE (E n) else 0 S := fun n => SB d (sz.L n) (sz.lam n) eta := fun n t => etaT (E n) t m := fun n => mE (E n) [Carrier.lean:180]
structure Step2Data {d : ℕ} (sz : Sizes d) extends Step2Mat sz where /-- the end `t₀_n` of the flow (band: `lemT (z n)`) -/ T0 : ℕ → ℝ /-- the setting of the flow at `(κ, ε, 𝔠, 𝔡)` (band: `STFlow sz κ ε 𝔠 𝔡 z`) -/ flowOK : ℝ → ℝ → ℝ → ℝ → Prop /-- **fact**: the setting contains the admissibility of the sizes -/ flowOK_adm : ∀ {κ ε 𝔠 𝔡 : ℝ}, flowOK κ ε 𝔠 𝔡 → sz.Admissible 𝔠 𝔡 /-- **fact**: `t₀ < 1` (the block Anderson reading needs `0 < κ`: `Im m ≥ κ`) -/ flowOK_T : ∀ {κ ε 𝔠 𝔡 : ℝ}, 0 < κ → flowOK κ ε 𝔠 𝔡 → ∀ n, T0 n < 1 /-- **fact**: trace cyclicity `𝓛_{(+,-),(a,b)} = 𝓛_{(-,+),(b,a)}` -/ L_swap : ∀ (n : ℕ) (t : ℝ) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ), L n t ![true, false] ![a, b] ω = L n t ![false, true] ![b, a] ω [Step2Gen.lean:97]
def bandStep2Data {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Step2Data sz where toStep2Mat := bandStep2Mat sz (STflowE z) T0 := fun n => lemT (z n) flowOK := fun κ ε 𝔠 𝔡 => STFlow sz κ ε 𝔠 𝔡 z flowOK_adm := fun h => h.1 flowOK_T := fun _ h n => lemT_lt_one (Step2Gen_flow_im_pos h n) L_swap := fun n t a b ω => Step2Gen_loopFine_swap _ _ a b [Step2Gen.lean:138]
def BAStep2 (d : ℕ) : Prop := STStep2G d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 [FlowPins.lean:432]
theorem stInitialGT2_of_L2decayG {sz : Sizes d} (Cm : Step2Data sz) (μ : Measure sz.SeqΩ) (hd : 0 < d) {κ ε 𝔠 𝔡 : ℝ} (hflow : Cm.flowOK κ ε 𝔠 𝔡) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ Cm.T0 n) (hdat : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ Cm.T0 n) → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) (hweak : STStep1WeakgL Cm.toFlowFM μ s t) (hL2 : STL2decayPTgL Cm.toFlowFM μ s t) : ∃ ε₀ CΨ : ℝ, 0 < ε₀ ∧ 0 < CΨ ∧ ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ stLocalPsi sz u n ∧ stLocalPsi sz u n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ∧ sz.Bctl n (u n) ≤ stLocalPsi sz u n ^ 2 ∧ stLocalPsi sz u n ^ 2 ≤ CΨ * sz.Bctl n (u n)) ∧ STInitialGT2gL Cm.toFlowFM μ u ε₀ (stLocalPsi sz u) [LocalAvg1.lean:379]
theorem stStep2AvgPT_of_L2decayG {sz : Sizes d} (Cm : Step2Data sz) (μ : Measure sz.SeqΩ) (hd : 0 < d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : Cm.flowOK κ ε 𝔠 𝔡) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ Cm.T0 n) (hdat : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ Cm.T0 n) → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) (hGav : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEXgL Cm.toFlowFM μ u ε₀) (hweak : STStep1WeakgL Cm.toFlowFM μ s t) (hL2 : STL2decayPTgL Cm.toFlowFM μ s t) : STStep2AvgPTgL Cm.toFlowFM μ s t [LocalAvg1.lean:468]
theorem stStep2LocalPT_of_L2decayG {sz : Sizes d} (Cm : Step2Data sz) (μ : Measure sz.SeqΩ) (hd : 0 < d) {κ ε 𝔠 𝔡 : ℝ} (hflow : Cm.flowOK κ ε 𝔠 𝔡) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ Cm.T0 n) (hdat : ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ Cm.T0 n) → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) (hGii : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEXgL Cm.toFlowFM μ u ε₀) (hGij : ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ Cm.T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEXgL Cm.toFlowFM μ u ε₀) (hweak : STStep1WeakgL Cm.toFlowFM μ s t) (hL2 : STL2decayPTgL Cm.toFlowFM μ s t) : STStep2LocalPTgL Cm.toFlowFM μ s t [LocalAvg2.lean:367]
theorem stLocalAvgOfL2_holdsG {d : ℕ} (hd : 0 < d) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Data sz) (hF : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → (mk sz z).flowOK κ ε 𝔠 𝔡) (hdat : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∃ cB c : ℝ, 0 < cB ∧ 0 < c ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ (mk sz z).T0 n) → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) (hGii : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEXgL (mk sz z).toFlowFM (law sz) u ε₀) (hGij : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEXgL (mk sz z).toFlowFM (law sz) u ε₀) (hGav : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ (mk sz z).T0 n) → ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEXgL (mk sz z).toFlowFM (law sz) u ε₀) : STLocalAvgOfL2gL d law Flow (fun sz z => (mk sz z).toFlowFM) (fun sz z => (mk sz z).T0) [LocalAvg2.lean:467]
$ the compiled nonempty instances (examples at d = 3, sz0, z0, s = 0, t = 1/16; heads, then the first 110 chars of the body)
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) := | stInitialGT2_of_L2decayG (bandStep2Data sz0 z0) sz0.seqP (by norm_num : 0 < 3) flow_z0 hs0 hst htT localAvg1_inst_hdat hweak hL2 
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) : STStep2AvgPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst := | stStep2AvgPT_of_L2decayG (bandStep2Data sz0 z0) sz0.seqP (by norm_num : 0 < 3) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 hs0 hst htT localAvg1_inst_hdat (fun u hu0 hul ε₀  
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) (ω : sz0.SeqΩ) := | have hu : ∀ n, (fun _ => (1 / 32 : ℝ)) n ∈ Set.Icc (sInst n) (tInst n) := fun n => by simp only [sInst, tInst, Set.mem_Icc]; norm_num And.intro (localAvg1_whp_L2G (bandSt 
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) : STStep2LocalPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst := | stStep2LocalPT_of_L2decayG (bandStep2Data sz0 z0) sz0.seqP (by norm_num : 0 < 3) flow_z0 hs0 hst htT RBM.Gauss.LocalAvg1Inst.localAvg1_inst_hdat (fun u hu0 hul ε₀ hε₀ =>  
example (hweak : STStep1WeakgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) (hL2 : STL2decayPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst) : STStep2LocalPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst ∧ STStep2AvgPTgL (bandStep2Data sz0 z0).toFlowFM sz0.seqP sInst tInst := | stLocalAvgOfL2_holdsG (by norm_num : 0 < 3) (fun sz => sz.seqP) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Data sz z) (fun _ _ _ _ _ _ h => h) (fun κ 
example (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) : ∃ X cB : ℝ, 1 ≤ X ∧ 0 < cB ∧ STgexRHSg (bandStep2Data sz0 z0).toFlowFM 0 (1 / 32) ω a b ≤ (2 * 3 ^ 3 * 3 ^ 3 * 3 ^ (3 - 2) + 2 ^ (3 - 2) * cB⁻¹) * X * STWB sz0 0 (1 / 32) (zdistInf 3 (sz0.L 0) (a - b)) := | by obtain ⟨X, hX, hL⟩ := RBM.Gauss.LocalAvg1Inst.localAvg1_inst_hL (bandStep2Data sz0 z0).toFlowFM 0 (by norm_num : (1 / 32 : ℝ) < 1) ω have hB := STBctl_pos sz0 0 (by no 
example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) (ε₀ Y : ℝ) (hY : 0 ≤ Y) (hΩ : ∀ x y : Idx 3 (sz0.L 0) (sz0.W 0), ‖(bandStep2Data sz0 z0).toFlowFM.GM 0 (1 / 32) ω x y‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-ε₀)) (hij : ∀ p : {p : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0) // p.1 ≠ p.2}, STindMaxg (bandStep2Data sz0 z0).toFlowFM 0 (1 / 32) (((sz0.W 0 : ℕ) : ℝ) ^ (-ε₀)) ω * ‖(bandStep2Data sz0 z0).toFlowFM.GM 0 (1 / 32) ω p.1.1 p.1.2‖ ^ 2 ≤ Y * STgexRHSg (bandStep2Data sz0 z0).toFlowFM 0 (1 / 32) ω (STblk sz0 0 p.1.1) (STblk sz0 0 p.1.2)) (hii : ∀ p : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0), STindMaxg (bandStep2Dat
Step2Gen.lean: 8 examples in namespace RBM.BA.Step2GenInst (the data example and 7 bridge families); FlowPins.lean:
example : BAStep2 3 = STStep2G 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz     BAflowT0 := rfl 
```

Narrative (what the output shows):
1. **Layout and stop line.** The vocabulary is the new file `Chain/Step2Gen.lean` (986 lines; imports only `Chain.Carrier`, `Induction.Step2Defs`); `Step2Defs.lean` is not edited (diff 0 lines); no `LWExpCert*` in any cone: not the certificate lane.  Stop line 1500, net reading as in (a′) C4: 986 + 331 = 1317; the gross reading (insertions plus deletions) is 1669, which the ticket does not use.
2. **Target 1.** `bandFM` moved with its body unchanged to `Chain/Carrier.lean` (its docstring now says so); the 13 `bandFM_*` bridges stay in `FlowPins`.  G1: `#check` of 36 public declarations is identical on `main` and on the branch.
3. **Target 2.** (a) `Step2Mat` (`FlowFM` + `LM`, `GMM`, `LIM`, `KI`, `Pp`, `Hpath`, no facts) and `Step2Data` (+ `T0`, `flowOK`, `flowOK_adm`, `flowOK_T`, `L_swap`); pilot fields left to T7 / T1: `ev1`-`ev4`, `Good`, `ident`, `martTail`, `pLWT`, `pEMe`, `pNew`.  (b) all 58 public defs of `Step2Defs.lean`: 5 `sz`-only (reused), 53 with a generic form, including the 16 names of Amend 1.  (c) the probe family `STAvgUgL`, ..., `STStep2G`, `STStep2_iff`.  (d) `bandStep2Mat`, `bandStep2Data` and 59 bridges: 28 `rfl`, 30 `Iff.rfl`, one proved, `bandFM_STGijGEX`.  The `Iff.rfl` risk of (a′) C2 (`STGridRepNAt`) did not occur.
4. **`STGijGEXgL`** is stated for `(G_t - M)_{xy}`, `x ≠ y`, the band `STGijGEX` for `(G_t)_{xy}`: they agree because the band `M` is diagonal (proof of `bandFM_STGijGEX`, `simp` with `x ≠ y`); at a carrier with a non-diagonal `M` they differ: paper-delta candidate T2386a.
5. **Target 3.** `localAvg1_whp_L2G`, `localAvg1_whp_omegaG`, `localAvg1_maxLoop2_leG`, `stInitialGT2_of_L2decayG`, `stStep2AvgPT_of_L2decayG`, `localAvg2_rhs_leG`, `localAvg2_entry_leG`, `stStep2LocalPT_of_L2decayG`, `stLocalAvgOfL2_holdsG` are stated over `FlowFM` / `Step2Data` and a law.  Facts as arguments: `hdat` (`ST_Bdata_holds`, per flow `∃ cB c`), `hGii`, `hGij`, `hGav` (`stGbEXP_holds`), `hswap` (`L_swap`); they need `0 < d` only (the band `stStep2AvgPT_of_L2decay`, `stStep2LocalPT_of_L2decay`, `stLocalAvgOfL2_holds` keep `3 ≤ d`).  Each band theorem keeps its name and statement (G1) and is proved from the generic one at `bandFM` / `bandStep2Data`; `localAvg2_rhs_le`, `localAvg2_entry_le` pass the private band `la2_loop_pm` as `hswap`.  Not done, by the ticket: a generic `Step2Iterate` (T1).
6. **Target 4.** `BAStep2` is in `FlowPins` (new import `Chain.Step2Gen`); a `Prop`, no proof, no BA instance (T8-BA).
7. **Registry.** `Test/Axioms.lean` gets 5 `owedProps` lines (`STStep1WeakgL`, `STL2decayPTgL`, `STGiiGEXgL`, `STGijGEXgL`, `STGavLGEXgL`) and 1 `structuralProps` line (`Step2Data.flowOK`); the whole-library `lake build` (with `#assert_rbm_axioms`) passes.
8. **Instances (d = 3, `sz0`, `z0`, `s = 0`, `t = 1/16`).** `Step2Gen.lean`: 8 examples (data, matrix level, model level and Step 2 pins, the `(law, Flow, mk, T0)` pins, the `lem_GbEXP` forms, grid, list-indexed loops, energy pins) that apply every bridge; `LocalAvg1.lean`/`LocalAvg2.lean`: examples for all nine generic theorems at `bandStep2Data sz0 z0` (`hdat`, `hL`, `hev`, `hswap`, `hlow`, the `lem_GbEXP` parts discharged; the weak law `STStep1WeakgL`, `(eq:L2_decay)` `STL2decayPTgL`, and for `localAvg2_entry_leG` the three event hypotheses `hΩ`, `hij`, `hii` stay hypotheses: other gates' outputs); `FlowPins.lean`: `BAStep2 3 = STStep2G … := rfl`.
9. **Hidden hypotheses.** The three facts of `Step2Data` are structure fields: proved at the band by `bandStep2Data`; at BA they are the obligations of T8-BA (`flowOK_T` needs `0 < κ` there).

## (c) Verified Mathlib names used (new text; `#check`-style existence test, `scratchpad/T2386/b/mathlib.lean`: all exist, none absent)

`Matrix.trace_mul_comm`, `List.ofFn_succ`, `List.ofFn_zero`, `List.prod_cons`, `List.prod_nil`, `Matrix.cons_val_zero`, `Matrix.cons_val_succ`, `Real.rpow_pos_of_pos`, `Real.rpow_two`, `Real.one_le_rpow`, `Real.rpow_nonneg`, `Finset.sup'_le`, `Finset.sup'_apply`, `Finset.sum_pair`, `Set.mem_iInter`, `Function.update`, `Ring.inverse`, `pow_le_pow_left₀`, `one_le_pow₀`, `mul_le_mul_of_nonneg_left`, `lt_of_lt_of_le`.

## (d) Open issues and paper-delta candidates

- **T2386a** (paper-delta candidate): `STGijGEXgL` states `(GijGEX)` for `(G_t - M)_{xy}`, `x ≠ y`, over a carrier; the band `STGijGEX` (docstring citing `3_5:24`) states it for `(G_t)_{xy}`.  Equal at the band (`bandFM_STGijGEX`); at BA `M = BAMfine` is not known to be diagonal ((a) F1), so BA stage G (G6b / G7) has to prove the `GM` form.
- Owed pins added to the registry with owners: `STL2decayPTgL` T1; `STGiiGEXgL`, `STGijGEXgL`, `STGavLGEXgL` BA stage G (G6b / G7); `STStep1WeakgL` the chain's Step 1 (Amend 1 item 7 names no owner for it; the existing line of `STLocalMaxgL` cites BA-S3).  H23 (b) union at merge: `Test/Axioms.lean` (7 lines) and `RBM3D.lean` (1 line).
- Left to later tickets: the BA instance `Step2Data` (`LM`, `GMM`, `LIM`, `KI`, `Pp`, `Hpath` and the three facts) is T8-BA; the pilot fields `ev1`-`ev4`, `Good` (T7) and `ident`, `martTail`, `pLWT`, `pEMe`, `pNew` (T1) are added by `extends Step2Data`.
- Ports: none from `../RBM1D` or `../RBM2D` (no RBM1D/RBM2D diff-stat).  Sources inside this repository: probe `t/T2379` (`00a2206`) `RBM3D/Probe/T2379Pins.lean:39-104` (`STAvgUgL`, ..., `STStep2G`, `STStep2_iff`, `BAStep2`), pilot `t/T2326` (`4fca3d2`) `RBM3D/Probe/T2326PilotStep2.lean:69-178` (the shape of `Step2Data`), and the merged `LocalAvg1.lean`, `LocalAvg2.lean`, `Step2Defs.lean` texts restated in place.
