Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 07:44:14 UTC 2026

Design gate (ticket T2375). Input `lwMomentExp_holds` read on `t/T2364` (`0b74a90`, `RBM3D/Graph/LWMomentExp.lean:1436`: `∀ d, LWMomentExp d`, index set `lam²/L² < 1 - t`); no `lake`, no Lean written. Scratch: `scratchpad/T2375/inst.py`. Line refs are `main` working tree (`Test/Axioms.lean` lines ≥156 are 1 less than the ticket's).

### (i) Tables

**(i-1) Premise ↔ producer** (`LWPins.lean` = `Graph/LWPins.lean`; "here" = proved in `LWTermHolds.lean`/`MainIndHolds.lean`)

| consumer | premise | producer |
|---|---|---|
| all pins | `3 ≤ d`, `κ ε 𝔡 > 0`, `STFlow`, `0 ≤ t ≤ lemT z` | hypotheses of the `_holds` theorems (as pinned); instance `flow_z0` |
| all pins | random premises `LWInit` (`LWPins:222`), `LWLoop2` (`:228`), `LWLoopExp` (`:274`), inside `LWAssm` (`:234`) / `LWAssmExp` (`:283`) | stay hypotheses of every `_holds` theorem (registry `Axioms:160-162,165-166` stay) |
| `LWterm`, `LWtermExpS` | f-premise (`Prec` of `‖LWf‖` by `η⁻¹Φ(0)Φ(r)` resp. `η⁻¹Bctl^{1/2}sfT + W^{-D}`) | here: Markov from `lwMoment_holds` (`LWMoment:1785`) resp. `lwMomentExp_holds` (T2364) + `lwInteg_holds` (here) + `LWPsiAll.shift` (`LWPsi:303`) |
| Markov | `Integrable ‖LWf‖^p` (`LWInteg`, `LWPins:205`) | here: `walk_measurable_Gt_apply` (`Path/Walk:813`), `lwMoment_norm_Gt_le` (`LWMoment:620`), `lwExpTerm2_BM_*` (`LWExpTerm2:1091-1131`); statement has `|E|<2`, `t<1`: closes as stated |
| `LWReduceB/T` | `(eq:Psi)` for `Φ(c r) ≲ Φ(r)` | `LWPsiAll.shift` (`LWPsi:303`); `LWPhiB_shift` (`:312`) for the B class |
| `LWReduceB/T` | `LWE = LWcut + LWcut`, `σc = ±`, split `W^{-2d}Σ_{x∈[a],y∈[b]} G_{yx}(f_{xy}+f̃_{xy})` | here, via `lwExpTerm2_LWcut_true` (`LWExpTerm2:1308`), `lwExpTerm2_cut_conj` (`:1627`), `svarF` (`Gauss/FineModel:47`) |
| `(eq:directG1/2)`, `(GijGEX)` | off-diagonal `\|G_{xy}\|² ≺ STgexRHS ≲ ΣL²(a',b') + W^{-d}1` | `lwGbyXi_holds` (`AuxGraph2:1122`, `ρ≡1`, `R≡0`; inside it `stGbEXP_holds.2.1`, `Green/GbEXP:811`); then `LWLoop2`/`LWLoopExp` + shift `r' ≥ r-2` (here) |
| `(eq:directG1/2)`, `(GiiGEX)` | diagonal `\|G_{xx}\| ≤ 1 + W^{-ε₀}` | `LWInit.1` + `norm_mE` (`Defs/Semicircle:63`); `(GiiGEX)` itself is not needed (it is used inside `lwEntryPsi_holds`, `AuxGraph2:1191`, only if the `Φ(0)` entry bound is wanted) |
| `(eq:recolterm/2)`, `(GavLGEX)` | `‖tr(Ǧ E_a)‖ ≺ Ψ'²`, `Ψ' = max(Φ(0), W^{-d/2})` | `lwMoment_avg_whp` (`LWMoment:1586`, uses `stGbEXP_holds.2.2`), `lwMoment_maxLoop2_prec` (`:1566`), `lwMoment_Psi'_facts` (`:1554`), `lwMoment_row_le` (`:1401`: `Σ_β S_{αβ}Ǧ_{ββ}` by the block averages) |
| `LWReduceT` | `(GavLGEX)` at `Ψ' = max(W^{-d/2}, Bctl^{1/2})`, `L² ≺ W^{-d}tailW ≤ Bctl` | `lwN_tailW_le` (`LWTermExpN:121`, `D' = 1/𝔠`), `lwN_Bctl_le` (`:225`), window `LWWindow_max_Bctl` (`LWPsi:344`); **new, here (BLow)**: `L²_{(-,+),(a,a)} ≥ W^{-d}/4` w.h.p. (`‖G-M‖ ≺ W^{-ε₀}`, `\|m\|=1`) forces `B_{t,0} ≥ N^{-τ}/4`, hence `W^{-d} ≤ 4N^τ Bctl` |
| `LWReduceT` | `W^{-d}tailW ≍ sfT² + W^{-d-D}`, zero mode | `tailW_regime1_bounds` (`LWPsi:475`, consts `1/2`, `1+2^{d-1}=5`), `zeroMode_le_of_ge` (`Defs/Tail:119`); `sfT` shift `r→r-2` here (const `3^{(d-2)/2}e^{√2/2}`) |
| `LWtermB` | `LWPsiRel`, `LWClass`, Bparam at `⌊r⌋` | `LWPhiB_psiRel` (`LWPsi:220`), hypotheses of the pin; `LWterm` at `Φ = LWPhiB` (here) |
| `LWtermExpN` | `LWterm` | `lwtermExpN_of_LWterm` (`LWTermExpN:414`) |
| `LWtermExp` | union of the two index sets | here: `StochDomAt.of_subset_union` (`Defs/StochDomAt:355`) on `lam²/L² < 1-t` / `≥` |
| `stMainInd_of_LW` (`MainIndOut:158`), `unMLOut_of_LW` (`:172`) | `LWterm d`, `LWtermExp d` | here (`lwterm_holds`, `lwtermExp_holds`); no other premise; Step 2 not re-proved |
| `STStep2` (`Axioms:130`) | `STNewKLK`, `STEMn2Exp`, `STGridRepN`, `STOptL2`, `STLocalAvgOfL2` | merged `stNewKLK_holds` (`NewKLK:1198`), `stEMn2Exp_holds` (`EMn2Exp2:1090`), `stGridRepN_holds` (`DifREP3:2381`), `stOptL2_of_pins` (`OptL2b:195`) with `STLWB_of_LWterm` (`Step2Events:1355`), `stGridMart_holds` (`DifREP2:2283`), `stLocalAvgOfL2_holds` (`LocalAvg2:394`); `ST_step2_of_pinsLW'` (`Step2Iterate:1793`) |

Registry (`Test/Axioms.lean`, current lines): delete `LWterm :151`, `LWtermB :152`, `LWtermExp :153`, `LWtermExpS :154`, `LWtermExpN :155`, `LWReduceB :156`, `LWReduceT :157`, `LWInteg :159`, `STMainInd :108`, `UNMLOut :191`, and `STStep2 :130` (its def has the guard `3 ≤ d →`, `Step2Defs:599`, so `∀ d, STStep2 d := fun d hd => ST_step2_of_pinsLW' …` is unconditional: one extra theorem in `MainIndHolds`). **Not deletable:** `STLWB :131`, `STLWT :132`, `STOptL2 :129` (defs `Step2Defs:406,421,667` have no `3 ≤ d` guard; only `3 ≤ d → STX d` is provable): update owner comments only. `STEtermsMid :180` is a `STIngR5` instance (`Step5Pins:275`), guard not checked: not claimed. The registry pre-check (target 4) decides any further name.

**(i-2) Exponent table** (`N = (WL)^d`, `W ≥ N^𝔠`, instance `d=3`, `𝔠=1/6`, `ε₀=1/20`; script (ii))

| item | value | constraint | slack |
|---|---|---|---|
| Markov (`LWterm`) | `τ=1/10`, `D=5`, `τ'=1`, `p=70` | `P ≤ N^{τ'}K_c^p N^{-τp} ≤ N^{-D}`: `τp ≥ D+τ'+1` | `τp-(D+τ') = 1.0` (used to absorb `K_c^p ≤ N`) |
| `Φ(cr) ≤ K_c Φ(r)` | `K_c = max(C₁c^{-C₂}, Cc(max(2,c⁻¹)))` (`c<1`), `1` (`c ≥ 1`) (`LWPsi_shift_aux`, `LWPsi:258`); instance `Φ0 ≡ W^{-1}`: `K=1` | `K_c^p ≤ N` eventually | `c=1/2`, `C₁=C₂=2`: `K=8`, `8^70 ≤ N_n` first at `n=1448`; `c=1`: all `n` |
| Markov (`LWtermExpS`) | `D' = pD = 350` in `LWMomentExp`; `(ζ+W^{-D})^p ≥ ζ^p + W^{-pD}` | `W^{-D'} = (W^{-D})^p` | equality (0) |
| window | `Ψ=Φ=W^{-1}`; `W^{-3/2} ≤ C₃Φ(0)`, `Φ ≤ W^{-1/20}` | `W^{-d/2} ≤ C₃Φ(0)`, `Φ ≤ W^{-ε₀}` | `log_W` slack `1/2` and `19/20` |
| `(eq:Psi)` | `C₁=C₂=2`, `Cc≡1`, `C₃=1` (`psiRel0`, `LWPins:542`) | `C₁,C₂>1` | `1` each |
| `(eq:directG1)` shift | `\|a'-b'\| ≥ \|a-b\|-2`, `Φ(max(r-2,0)) ≤ 18 Φ(r)`, `18 = max(Cc(3), C₁3^{C₂})`; `#terms = 2·9³ = 1458` | absorbed in `N^{τ}` | eventual |
| `W^{-D'} ≤ L^{-d}` | `D' = 1/𝔠 = 6` (`lwN_tailW_le`) | `D'𝔠 ≥ 1` (`W^{D'} ≥ N ≥ L^d`) | 0 (equality); `n=0`: `9.3e-10 ≤ 1.56e-2` |
| regimes | `t=1/16`: S for all `n`; `t=lemT`: N for all tested `n`; `t_n = lemT` (n even), `1/16` (n odd): 100 S + 100 N for `n<200` | `lam²/L² < 1-t` (S) / `1-t ≤ lam²/L²` (N) | `n=0`, `t=lemT`: `9.05e-6 ≤ 1.53e-5`; S, `t=1/16`: `1.5e-5 < 15/16` |
| BLow (`LWReduceT`) | needs `B_{t,0} ≥ N^{-τ}/4` | `W^{-d} ≤ 4N^τ Bctl` | instance `B_{t,0} = 1.083` (`t=1/16`), `5675.9` (`t=lemT`, `n=0`) |
| `sfT` shift, tail | `3^{(d-2)/2}e^{√2/2} = 3.5128`; `1+2^{d-1} = 5` | `ℓ_t ≥ 1`, `r ≤ L`, `ℓ ≤ L` (use `min(ℓ,L)`: `r ≤ L`) | grid max `3.5127982` (tight at `ℓ_t=1`, `s=2`) |
| `ℓ` | `ℓ = ℓ_t`: `1` (`t=1/16`), `4 = L` (`t=lemT`, `n=0`) | `0 ≤ ℓ ≤ (log W)^{10} ℓ_t` | `ℓ_t ≤ (log W)^{10}ℓ_t` |

Findings (paper-delta candidates): **T2375a** `(GavLGEX)` in `7_8:65` takes `Ψ_t = (W^{-d}B_{t,0})^{1/2}`, which needs `B_{t,0} ≥ 1` (`LWPsi:319`, T2040a); Lean uses `Ψ' = max(W^{-d/2}, ·)` and closes `W^{-d} ≲ N^τ Bctl` by BLow from `(LW_assm_exp)` at `a=b`. **T2375b** the Lean pins `LWterm`, `LWtermExp` carry the window control `Ψ` and the class `Φ` separately; the reduction uses `Φ(0)` only (`LWLoop2` gives `max L² ≺ Φ(0)²`), `Ψ` is unused.

### (ii) One concrete nondegenerate instance

Data: `sz0` (`L_n=4(n+1)`, `W_n=(2(n+1))^5`, `lam_n=(2(n+1))^{-6}`), `κ=ε=𝔡=1/10`, `𝔠=1/6`, `z_n = 1/2 + i N_n^{-4/5}`, `t ≡ 1/16` and the mixed `t_n ∈ {1/16, lemT z_n}` (both regimes occur), `ε₀=1/20`, `Φ0≡W^{-1}`, `C₁=C₂=2`, `C₃=Cc≡1`, `ℓ=ℓ_t`, `p=70`, `D=5`. Every deterministic hypothesis holds (rows above); the random premises `LWInit`, `LWLoop2`, `LWLoopExp` stay hypotheses of the example, as in merged `inst_LWterm`, `inst_LWtermExp` (`LWPins:567,626`; `tEnd` variants `:761,771`). External input: none (no `UNL32`, `KLPT`; `stGbEXP_holds` is proved). Unmerged input: T2364 (stage 1b waits for its merge).

Command: `cd scratchpad/T2375 && python3 inst.py` (mpmath, 60 digits), exit 0:
```
== (1) flow data: |E|<2, t<=lemT, regimes (S: lam^2/L^2 < 1-t ; N: 1-t <= lam^2/L^2)
n L W lam N | 1-lemT(z0 n) | lam^2/L^2 | regime(t=1/16) | regime(t=lemT) | E
0 4 32 0.0156 2.1e+6 | 9.051e-6 | 1.526e-5 | S | N | 0.5
1 8 1024 0.000244 5.5e+11 | 4.187e-10 | 9.313e-10 | S | N | 0.5
5 24 248832 3.35e-7 2.13e+20 | 5.641e-17 | 1.947e-16 | S | N | 0.5
50 204 11040808032 8.88e-13 1.14e+37 | 2.332e-30 | 1.895e-29 | S | N | 0.5
mixed t_n over n<200: #regime S = 100  #regime N = 100
== (2) Markov: P(|f|>N^tau zeta) <= N^{tau'} K^p N^{-tau p}; need <= N^{-D}
tau = 0.1 D = 5.0 tau' = 1.0 -> p = 70  tau*p - (D+tau') = 1.0 >= 1 (absorbs K^p<=N)
 c = 1.0  K_c = 1.0  K^p <= N_n first at n = 0
 c = 0.5  K_c = 8.0  K^p <= N_n first at n = 1448
moment-exp: W^{-D'} with D' = p*D = 350.0  (W^{-D'} = (W^{-D})^p exactly); n=0: log2 W^{-D'} = -1750.0
== (3) window / class slack at n=0,1  (W^{-d/2} <= C3*Phi(0), Phi <= W^{-eps0})
0 log_W slack lower: 0.5  upper: 0.95
== (4) W^{-D'} <= L^{-d} at D' = 1/cc = 6 ... holds for n<500; n=0: 9.313e-10 <= 0.01562
== (5) B_{t,0} (BLow) and Bctl vs W^{-d}
t=1/16 n = 0 B_{t,0} = 1.0830556 >= 1: True  ell_t = 1  eta_t^{-1} = 1.10165
t=lemT n = 0 B_{t,0} = 5675.8551 >= 1: True  ell_t = 4  eta_t^{-1} = 114105.0
== (6) sfT shift: max ratio on grid = 3.5127982  bound = 3.5127982  ok: True
== (7) LWInteg data: n=0, E=lemE(z0 0), t=1/16, p=2: eta_t^{-1} = 1.1016486 (|E| < 2: True)
== (8) 18.0 = max(Cc(3), C1*3^C2); #terms in STgexRHS = 2*3^d*3^d = 1458
OK
```
(The script also prints `n=1,10` rows and the `NNN…` regime string for `t_n=lemT`, `n ∈ [200,260)`; abridged here for the line limit, full output in `scratchpad/T2375/out.txt`.)

**Plan (ticket (iv); `wc -l` of the two new files together; stop line 2300).** `LWTermHolds`: §0 imports, helpers 20; §1 `lwInteg_holds` 60; §2 Markov (plain, and with `+W^{-D}`) 200; §3 algebra `LWE → W^{-2d}ΣG(f+f̃)`, conj branch `σc=-` 200; §4 one generic reduction skeleton (whp events → pointwise sum → `Prec`, shared by B and T) 450; §5 B instance, `lwReduceB_holds`, `lwterm_holds`, `lwtermB_holds` 270; §6 T instance (`(eq:directG2)`, `sfT` shift, BLow), `lwReduceT_holds` 350; §7 `lwtermExpS_holds`, `lwtermExpN_holds`, union `lwtermExp_holds` 220; §8 instances 120. `MainIndHolds`: `stMainInd_holds`, `unMLOut_holds`, `stStep2_holds`, instances 70. Central 1960 (lo 1500, hi 2650); hi exceeds the stop line, margin to 2000 is thin and rests on sharing §4 between B and T. Checkpoints: commit after §5 (≈1000); if the total after §6 exceeds 1900, stop and RETURN for the REQ with cut (b) (T side §6-§7 and R4, since R4 needs `LWtermExp`); no cut is taken by 1b itself.

### Verdicts
- Target 1 (`lwInteg_holds`, Markov, `lwReduceB_holds`, `lwterm_holds`, `lwtermB_holds`, `lwReduceT_holds`, `lwtermExpS_holds`, `lwtermExpN_holds`, `lwtermExp_holds`): **PASS** (`LWInteg` closes as stated; all hypothesis sets can hold at once; exponents close, slacks above; BLow is the one new lemma).
- Target 2 (`stMainInd_holds`, `unMLOut_holds`, plus `stStep2_holds`): **PASS** (one-line applications of `stMainInd_of_LW`, `unMLOut_of_LW`; needs target 1 and the T2364 merge).
- Target 3 (instances): **PASS** (data above; stochastic premises stay hypotheses).
- Target 4 (registry): **PASS** with the restriction above: `STLWB`, `STLWT`, `STOptL2` stay owed (no `3 ≤ d` guard in their defs).

## (a′) Preflight corrections — Sat Oct 10 09:07:09 UTC 2026

Two points of (a) differ from what the proof used; no verdict changes (targets 1-4 stay PASS).
1. (a)(i-1) row `LWReduceT` and (i-2) row "BLow" (new lemma from `L²_{(-,+),(a,a)}`): `W^{-d} ≤ (1+𝔡⁻²)·Bctl` is deterministic. `(eq:WO)` gives `lam ≤ 𝔡⁻¹`,
   so `B_{t,0} ≥ (g²+|1-t|)⁻¹ ≥ (1+𝔡⁻²)⁻¹` (`hBlow` in `LWTermHolds_reduceT_core`); no stochastic input.
2. (a)(i-2) does not list a condition on `D` for the T reduction. The cross term `W^{-D}·𝖳` of `(eq:recoltermwt2)` is absorbed into `η⁻¹B^{1/2}(𝖳² + W^{-d-D})` only if
   `(1+𝔡⁻²)W^{-D} ≤ W^{-2d}`, i.e. `D ≥ 2d+1` (`hwW`, `LWTermHolds_reduceT_core`). For `D < 2d+1` the premise at `D` does not give the conclusion at `D`:
   `lwReduceT_holds` uses its premise when `D ≥ 2d+1` and otherwise the premise at `2d+1` from `lwMomentExp_holds` (`LWTermHolds_concT`). The paper says "any large constant D" (`3_5:407-410`).

## (b) Script output

Branch `t/T2375` at `6646c14` (commits `main..HEAD` below); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2375`; no port from RBM1D/RBM2D (no file of either was read).

**Build** (`lake build RBM3D.Graph.LWTermHolds RBM3D.Induction.MainIndHolds RBM3D.Test.Axioms`, exit 0; the build log has 0 lines naming either new file):
```
✔ [4063/4064] Built RBM3D.Graph.LWTermHolds (67s)
✔ [4064/4064] Built RBM3D.Induction.MainIndHolds (3.5s)
Build completed successfully (4064 jobs).
```
**Section commits and the stop line** (`wc -l` of the two new files together at each commit; stop line 2300; no cut taken):
```
17ed18e 08:11:55Z total=703      442252c 08:22:49Z total=1162     dd7b16a 08:32:29Z total=1467     0c3135d 08:36:41Z total=1597
7741cec 08:50:09Z total=1760     6e0067c 08:54:01Z total=1781     748a085 08:56:56Z total=1799     6646c14 09:04:32Z total=1894 (1801+93)
```
**Axioms** (`lake env lean scratchpad/T2375/axioms_t.lean`, `#print axioms <name>` for the targets, prefix `RBM.Gauss.Sizes.` dropped; exit 0):
```
'lwInteg_holds' : [propext, Classical.choice, Quot.sound]
'lwReduceB_holds' : [propext, Classical.choice, Quot.sound]
'lwterm_holds' : [propext, Classical.choice, Quot.sound]
'lwtermB_holds' : [propext, Classical.choice, Quot.sound]
'lwReduceT_holds' : [propext, Classical.choice, Quot.sound]
'lwtermExpS_holds' : [propext, Classical.choice, Quot.sound]
'lwtermExpN_holds' : [propext, Classical.choice, Quot.sound]
'lwtermExp_holds' : [propext, Classical.choice, Quot.sound]
'stMainInd_holds' : [propext, Classical.choice, Quot.sound]
'stStep2_holds' : [propext, Classical.choice, Quot.sound]
'stEtermsMid_holds' : [propext, Classical.choice, Quot.sound]
'stStep5I_holds' : [propext, Classical.choice, Quot.sound]
'stStep5II_holds' : [propext, Classical.choice, Quot.sound]
'RBM.Univ.unMLOut_holds' : [propext, Classical.choice, Quot.sound]
```
All 38 new public declarations (the 14 targets above and 24 helpers `LWTermHolds_*`, 7 of them in `LWTermHoldsInst`) were printed (`scratchpad/T2375/axioms_all.out`):
`grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"` gives 38, and the file has 38 `depends on axioms` lines.

**Target statements** (`grep -n "^theorem <name>" RBM3D/Graph/LWTermHolds.lean RBM3D/Induction/MainIndHolds.lean`, verbatim; each is `∀ d, <pin> d` with the pin of `LWPins.lean`: `LWInteg :205`, `LWReduceB :428`, `LWterm :240`, `LWtermB :255`, `LWReduceT :478`, `LWtermExpS :447`, `LWtermExpN :462`, `LWtermExp :290`):
```
LWTermHolds.lean:55:theorem lwInteg_holds : ∀ d, LWInteg d := by
:551:theorem lwReduceB_holds : ∀ d, LWReduceB d := by             :682:theorem lwterm_holds : ∀ d, LWterm d := by
:688:theorem lwtermB_holds : ∀ d, LWtermB d := by                 :1588:theorem lwReduceT_holds : ∀ d, LWReduceT d := by
:1595:theorem lwtermExpS_holds : ∀ d, LWtermExpS d := by         :1601:theorem lwtermExpN_holds : ∀ d, LWtermExpN d := fun d => lwtermExpN_of_LWterm d (lwterm_holds d)
:1604:theorem lwtermExp_holds : ∀ d, LWtermExp d := by
MainIndHolds.lean:33:theorem stMainInd_holds : ∀ d, STMainInd d := fun d =>   (next line: stMainInd_of_LW d (lwterm_holds d) (lwtermExp_holds d))
:38:theorem stStep2_holds : ∀ d, STStep2 d := fun d hd =>         :44:theorem stEtermsMid_holds : ∀ d, STEtermsMid d := fun d hd =>
:48:theorem stStep5I_holds : ∀ d, STStep5I d := fun d =>          :52:theorem stStep5II_holds : ∀ d, STStep5II d := fun d =>
:61:theorem unMLOut_holds : ∀ d, UNMLOut d := fun d =>   (next line: unMLOut_of_LW d (lwterm_holds d) (lwtermExp_holds d))
```
The auditor's checks (`example : ∀ d, LWterm d := lwterm_holds`, same for `LWtermExp`, `STMainInd`, `UNMLOut`) compile (`scratchpad/T2375/axioms.lean`, exit 0).
Check file `docs/tickets/checks/T2375-check.lean` on the branch: `lake env lean`, exit 0.

**Compiled nonempty instances** (`d = 3`, merged data `sz0`, `z0`, `flow_z0`, `tInst`/`tEnd`; headers of the `example`s, `LWTermHolds.lean:1637-1800`, `MainIndHolds.lean:74-91`):
```
1637 example (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : Integrable (fun ω => ‖LWf sz0 0 (STflowE z0 0) (tInst 0) ω x y‖ ^ 2) sz0.seqP := lwInteg_holds 3 sz0 0 ..
1642 example (hI : LWInit ..) (hL : LWLoop2 ..) := lwReduceB_holds 3 le_rfl (1/10) (1/10) (1/10) .. (1/6) sz0 z0 flow_z0 tInst .. (LWTermHolds_fB ⟨..⟩)  [f-premise discharged]
1648 example (hI) (hL) := inst_LWterm (lwterm_holds 3) hI hL            1652 example (hI) (hL) := lwtermB_holds 3 .. (1/5) 3 (√(1+1^2)) (fun n => sz0.L n) ..
1660/1666 reduceT at D = 7 and D = 5 (premise `LWTermHolds_fT` discharged)   1673 lwtermExpS_holds at tInst (index set = all n, `strict_all`)
1679 inst_LWtermExpN (lwtermExpN_holds 3) at tEnd                    1683/1686 inst_LWtermExp (lwtermExp_holds 3) at tInst and tEnd
1692 Markov: (⌈(5+2)/(1/10)⌉₊+1 : ℕ) = 71 ∧ 5+2 ≤ (1/10)*(2*71)       1698 ∃ K>0, ∀ᶠ n, ∀ r ≥ 0, Φ0 n (1/2*r) ≤ K * Φ0 n r := LWPsiAll.shift sz0 psiAll0 ..
1701 regime split at n = 0: ĝ²/L² < 1-1/16 ∧ 1-(1-10⁻⁶) ≤ ĝ²/L²       1753 theorem LWTermHolds_N_regime_tEnd (n) (hn : 6000 ≤ n) : 1 - tEnd n ≤ lam²/L²
1788 example: 1 - LWTermHolds_tMix 0 > ĝ²/L² ∧ 1 - LWTermHolds_tMix 6001 ≤ ĝ²/L² (alternating time: both regimes nonempty)
1795 example (hI) (hL) := lwtermExp_holds 3 .. LWTermHolds_tMix ..   [the union at the alternating sequence; only LWInit, LWLoopExp remain hypotheses]
MainIndHolds 74: example : sz0.STLK (STflowE z0) (fun n => lemT (z0 n) / 2) := (RBM.Univ.unMLOut_holds 3 ..).1      [no hypothesis left]
:80 stMainInd_holds 3 le_rfl (1/10) (1/10) (1/10) ..   :84 stStep2_holds 3 ..   :87 stEtermsMid_holds 3 .. 1 one_pos   :89 stStep5I_holds 3 ..   :91 stStep5II_holds 3 ..
```
The only hypotheses left in the examples are `LWInit`, `LWLoop2`, `LWLoopExp` (other gates' stochastic pins, registered owed). `LWInteg`, the `f`-premises, `LWAssm`/`LWAssmExp` deterministic parts, the flow, the times, `D`, `ε₀`, `ℓ` are discharged.

**Name-clash grep** (`git grep -n <name> main -- RBM3D`, hits on `main`; the new public names are `lwInteg_holds`, `lwterm_holds`, `lwtermB_holds`, `lwReduceB_holds`, `lwReduceT_holds`,
`lwtermExpS_holds`, `lwtermExpN_holds`, `lwtermExp_holds`, `stMainInd_holds`, `stStep2_holds`, `unMLOut_holds`, `stEtermsMid_holds`, `stStep5I_holds`, `stStep5II_holds`, stems):
```
lwInteg_holds 0  lwReduceB_holds 0  lwterm_holds 0  lwtermB_holds 0  lwReduceT_holds 0  lwtermExpS_holds 0  lwtermExpN_holds 0  lwtermExp_holds 0
stMainInd_holds 0  stStep2_holds 0  unMLOut_holds 0  stEtermsMid_holds 0  stStep5I_holds 0  stStep5II_holds 0
LWTermHolds 0 (stem; also `LWTermHolds_`, `LWTermHoldsInst`)  MainIndHolds 0
```
**Registry** (`RBM3D/Test/Axioms.lean`, `git diff main...HEAD`: 14 `owedProps` lines deleted): `STMainInd`, `STStep2`, `LWterm`, `LWtermB`, `LWtermExp`, `LWtermExpS`, `LWtermExpN`,
`LWReduceB`, `LWReduceT`, `LWInteg`, `UNMLOut`, `STStep5I`, `STStep5II`, `STEtermsMid`. Owner comments updated: `STOptL2`, `STLWB`, `STLWT` (stay owed: their definitions at
`Step2Defs.lean:406, 421, 667` have no `3 ≤ d →`, so only `3 ≤ d → STX d` is provable), `STMainIndG`, `LWInit`, `LWLoop2`, `LWLoopExp`, the group header.
**Registry pre-check** (temporary uncommitted file `scratchpad/T2375/precheck.lean`: `import RBM3D`, `import RBM3D.Induction.MainIndHolds`, `#assert_rbm_axioms`; `lake env lean`):
```
exit=0
axiom audit: 10947 theorems, 3209 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 123 (borrowed 1, owed 61, structural 42, refuted 6, superseded 13).   (no unregistered premise)
```
**Diff**: `git diff --stat main...HEAD`: `RBM3D/Graph/LWTermHolds.lean | 1801 +`, `RBM3D/Induction/MainIndHolds.lean | 93 +`, `RBM3D/Test/Axioms.lean | 30 +-` (the sole writable files only).

**Narrative** (facts from the files; section numbers are those of `LWTermHolds.lean`):
- §1 `lwInteg_holds`: `LWf` is a finite sum of products of entries of `G_t` (`walk_measurable_Gt_apply`, `lwMoment_norm_Gt_le`), bounded measurable (`lwExpTerm2_BM_*`), so `‖f‖^p` is integrable. It closes as stated.
- §2 `LWTermHolds_prec_of_moments`: for `(τ₀, D)` take `p = 2p₀`, `p₀ = ⌈(D+2)/τ₀⌉ + 1` (so `D + 2 ≤ τ₀ p`), Markov on `E‖f‖^p ≤ N (Kζ)^p`, union over the index set (`#V ≤ N²`, `StochDomAt.of_forall_le`).
  B: the moment is `lwMoment_holds` (constant `c`), `K` from `LWPsiAll.shift` at `c`. T: the moment is `lwMomentExp_holds` at `D' = pD`, and `a^p + (W^{-D})^p ≤ (a + W^{-D})^p` gives `K = 1`.
- §3 `LWTermHolds_cut_true` (from `lwExpTerm2_LWcut_true`, `lwExpTerm2_eval3`): `LWcut(+,σ_o,a_c,a_o) = Σ_{c∈[a_c],o∈[a_o]} w w (Σ_v F_v G_{ov} G_{vc}) G^{σ_o}_{co}`, `F_v = Σ_β S_{vβ} Ǧ_{ββ}`;
  `LWTermHolds_F_split`: `Σ_v … = f + f̃` (`α ∈ {x,y}`); `LWTermHolds_pointwise` and `LWTermHolds_cut_le` (the diagonal pairs give `W^{-d} 1[a_c = a_o]`); the charge `σ_c = -` by `lwExpTerm2_cut_conj`;
  `LWTermHolds_LWE_le`: `‖LWE‖ ≤ 2[γ(r)(φ(r) + 2μAγ(r)) + A(φ(0) + μA²) W^{-d} 1[a_0 = a_1]]` for entry bounds `A, γ, φ` and average bound `μ`, shared by B and T.
- §4 B: `(eq:directG1)` off the diagonal is `lwGbyXi_holds` (ρ = 1, R = 0) composed with `lwXiClaim_holds` by `StochDomAt.trans`; the diagonal `‖G_xx‖ ≤ 2` w.h.p. is `LWInit.1`; the averages are `lwMoment_avg_whp`;
  `LWTermHolds_arithB` gives `≤ K X³ η⁻¹Φ(0)Φ(r)²`, `K = (1 + 4 max(1,C₃)²)(1 + 2C₃²)`. `lwtermB_holds` is `lwterm_holds` at `LWPhiB` with `LWPhiB_psiRel`.
- §5-6 T (regime `lam²/L² < 1 - t`): `LWTermHolds_Gij_T` uses `lwGbyXi_holds`, `LWLoopExp` at `D₂ = d + 2D`, the copy `LWTermHolds_xiSq_le` of the private `auxGraph2_xiSq_le`, `tailW_regime1_bounds` (with `ℓ' = min ℓ L`, since `r ≤ L`)
  and the shift `𝖳(max(u-2,0)) ≤ √(3^{d-2}) e^{√2/2} 𝖳(u)`; `LWTermHolds_avg_T` is `(GavLGEX)` at `Ψ_t = max(W^{-d/2}, √Bctl)` (window `LWWindow_max_Bctl`, `lwN_Bctl_le`, `LWLoopExp` at `D = 1`);
  `LWTermHolds_arithT` closes the sum; `LWTermHolds_reduceT_core` (`D ≥ 2d+1`, `set_option maxHeartbeats 1600000`) combines them. `lwReduceT_holds` is the core for `D ≥ 2d+1` and `LWTermHolds_concT` otherwise;
  `lwtermExpN_holds` is `lwtermExpN_of_LWterm`; `lwtermExp_holds` glues the two index sets with `StochDomAt.of_subset_union`.
- `LWInit.2` is not used in this file; the control parameter `Ψ` is used on the B side only through the window (`W^{-d/2} ≤ W^{-ε₀}`, in the merged `lwMoment_Psi'_facts`) and not at all on the T side (finding T2375b). No hypothesis was added, no pinned signature changed, no file outside the three.
- §7 instances: see the list; at `d = 3` the flow end `t = lemT z_n` is in the regime `1 - t ≤ ĝ²/L²` for `n ≥ 6000` (compiled from `lemma28_quant`: `η_{t₀} ≤ 16 Im z_n`, `Im m ≥ 3/10`, `54 N^{-4/5} ≤ ĝ²/L²`).
- Registry: 14 lines deleted (11 of the ticket's list plus `STEtermsMid`, `STStep5I`, `STStep5II`, which `stMainInd_of_LW` derives from `LWtermExp`; their theorems are in `MainIndHolds.lean`).

## (c) Verified Mathlib names (all occur in the compiled files; the types of the first eight come from `#check`, `scratchpad/T2375/names.lean`)
- `MeasureTheory.mul_meas_ge_le_integral_of_nonneg : 0 ≤ᵐ[μ] f → Integrable f μ → ∀ ε, ε * μ.real {x | ε ≤ f x} ≤ ∫ f` (Markov).
- `MeasureTheory.ofReal_measureReal : μ s ≠ ⊤ → ENNReal.ofReal (μ.real s) = μ s`.
- `pow_add_pow_le : 0 ≤ x → 0 ≤ y → n ≠ 0 → x ^ n + y ^ n ≤ (x + y) ^ n`.
- `Fintype.card_subtype_le : Fintype.card {x // p x} ≤ Fintype.card α`.
- `one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1`.   `pow_le_one_iff_of_nonneg : 0 ≤ a → n ≠ 0 → (a ^ n ≤ 1 ↔ a ≤ 1)`.   `le_self_pow₀ : 1 ≤ a → n ≠ 0 → a ≤ a ^ n`.
- `min_add_add_right : min (a + c) (b + c) = min a b + c`.   `div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)`.
- `Real.sqrt_le_iff`, `Real.le_sqrt_of_sq_le`, `Real.one_le_sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_le_one`, `Real.one_le_exp`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.rpow_intCast`, `Nat.le_ceil`, `Nat.ceil_eq_iff`, `Finset.sum_pair`, `inv_le_one_of_one_le₀`, `one_le_mul_of_one_le_of_one_le`, `le_mul_of_one_le_right`, `pow_lt_pow_left₀`, `mul_div_cancel₀`.
- Not in the build as written: `if_true`, `if_false` are deprecated (use `ite_true`, `ite_false`); with `open Matrix`, `zpow_neg` is ambiguous with `Matrix.zpow_neg` (use `_root_.zpow_neg`). No Mathlib name was found absent that the code needed.

## (d) Open issues and paper-delta candidates
- **T2375a** (`7_8:65`): `(GavLGEX)` at `Ψ_t = (W^{-d}B_{t,0})^{1/2}` needs `B_{t,0} ≥ 1` for the window `W^{-d/2} ≤ Ψ_t` (as T2040a). Lean uses `Ψ_t = max(W^{-d/2}, Bctl^{1/2})`; `Ψ_t² ≤ (1+𝔡⁻²) Bctl` follows from `(eq:WO)`.
- **T2375b**: the pins `LWterm`, `LWtermExp` carry the control parameter `Ψ` of `(initialGT2)` and the class `Φ` separately; this file uses `LWInit.1` (`‖G-M‖_max ≺ W^{-ε₀}`) only; `LWInit.2` (`max 𝓛^{(2)} ≺ Ψ²`) is unused (the averaged law is taken at `Ψ' = max(Φ(0), W^{-d/2})`, resp. `max(W^{-d/2}, Bctl^{1/2})`).
- **T2375c** (`3_5:407-410`, `7_8:79, 88`): the paper states `lem: EWGn2_N` for "any large constant D"; the pin `LWReduceT` quantifies all `D > 0` with the premise at the same `D`. The reduction needs `D ≥ 2d+1` (cross term `W^{-D} 𝖳`); small `D` go through the premise at `2d+1`.
  The shift of `(GijGEX)` by `2` in `(eq:directG2)` costs `√(3^{d-2}) e^{√2/2}` (not stated in the paper).
- **T2375d**: `LWAssmExp` gives `ℓ ≤ (log W)^{10} ℓ_t`, not `ℓ ≤ L`; `tailW_regime1_bounds` needs `ℓ ≤ L`; the proof uses `min(ℓ, L)` (valid since `|a-b| ≤ L`); no statement change.
- **Registry (extension)**: three lines beyond the ticket's list are deleted (`STEtermsMid`, `STStep5I`, `STStep5II`), each with a theorem in `MainIndHolds.lean` (the ticket's registry clause, "Per C8", allows "any other owed pin that becomes an unconditional corollary").
  `STLWB`, `STLWT`, `STOptL2` stay owed (no `3 ≤ d →` in their definitions).
- **Open**: the root imports (`import RBM3D.Graph.LWTermHolds`, `import RBM3D.Induction.MainIndHolds` after the last import of `RBM3D.lean`) and the full `lake build` are the hub's merge step (not run here: the root file is not a writable file).
  Compiled nonemptiness of the regime `1 - t ≤ ĝ²/L²` at the flow end is for `n ≥ 6000` only; smaller `n` are not decided (not needed). `LWTermHolds.lean` builds in 67 s.
