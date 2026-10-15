Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 06:31:28 UTC 2026

Row a of T2511 (targets 1-10; `t/T2511` from `main` 97779231). Mathematics only. No pin, row or stop line moves: no 1a-audit needed (one 1b instruction on the form of the Step-5 binder of target 6 in row F(iv), an unfolding the ticket's stop rule allows).

### (i) Exponent table (with the ticket's fill-in rows F(i)-F(vii))
| constant | value | constraint | slack |
|---|---|---|---|
| member flow `κ'` | `c_κ(κ)·κ`, `c_κ = √min(κ/(κ+1), 1/2)` (`Step1Fam:488`, `BAFlowMember_holds :624`) | `0 < κ' ≤ κ` (`cκ_le_one :493`) | at `κ = 1/4`: `c_κ = 0.44721`, `κ' = 0.11180`, gap `0.138` |
| member flow `ε'` | `ε/2` | `0 < ε' ≤ ε` | `ε = 1/10`: `ε' = 1/20` |
| member modification `n₀` | least `n` from which `size_n^{-ε/2} < κ'` (`Step1Fam:633`, `obtain` of `eventually_atTop`) | eventual; not an instance hypothesis | `n₀ = 5` at `(κ, ε) = (1/4, 1/10)` (output (3)); equals the probe's `n₀ = 5` (`T2503-design.md`, D3 (a)) |
| `Cd` (Step 2) | `∃ Cd` from `baStep2Decay_holds` (`DecayLoopBA:114`) at `(κ', ε', 𝔡)` | `0 < Cd`; chosen before `c₃, c₄, c₅, c_tl` (`∀ Cd, ∃ 𝔠d`) | none (existential) |
| `c₂` | Step 2 `𝔠d` of the same theorem | `0 < c₂ ≤ 1/100` | `c₂ ≤ 1/100` is the cap |
| `c₃, c₄` | `∃ 𝔠d` of `STStep3RgL/STStep4RgL d R34` at `Cd` | `0 < c ≤ 1/100` | existential |
| `c₅` | `∃ 𝔠d` of `STIngR5gL d R` (Step 5) at `Cd` | `0 < c₅ ≤ 1/100` | existential |
| `c₆` | `∃ 𝔠d` of `STIngR6gL d R Concl6` (no `Cd`: `Step6Gen:100-110`) | `0 < c₆ ≤ 1/100` | existential |
| `c_tl` | `∃ 𝔠d` of `BATwistLoopStep d Rtl` at `Cd` (`TwistPins:160`; `BATwFrame :146`) | `0 < c_tl ≤ 1/100` | existential |
| **`𝔠d_R`** (target 5) | `min(c₂, c₃, c₄, c₅, c₆, c_tl)` (six, one more than the band's five: `MainIndRegimes:170-176`) | `0 < 𝔠d_R ≤ 1/100` (the `∃ 𝔠d` of `BAMainIndFamTL`, `MainIndOutBA:60`); each step needs `STConStInd c_i` from `STConStInd 𝔠d_R` by `st5_conStInd_mono` (`Step5Kit:101`: `0 < 𝔠d_R ≤ c_i`, `t < 1`) | `𝔠d_R ≤ c₂ ≤ 1/100`; `t < 1` from `BAflowT0 < 1` (`BAflow_T0_bounds`, `Step1Trivial:47-48`) |
| `c₁` (window) | `BAWinBulk_of_dom_holds` (`CouplingWindow:836`): `min(1/2, κ_dom⁹/(64 d Λ))` (`:692`), window in the `κ_dom/2`-bulk | `0 < c₁ ≤ 1/2` | (iii): explicit `c₁ = 1/3` (`sz0_win_third`, `Step1Fam:802`); (i), (ii), (iv): proof value `1.3e-19`, `5.5e-31`, `8.7e-31`, numerical `c₁ = 1/2` passes (output (3)) |
| `d` | `3 ≤ d` (statements), `2 ≤ d` for `baStep1_holds'` (`Step1Prime:892`) and `st_caseII_of_reg5IV` (`MainIndRegimes:145`) | `3 ≤ d` | 1 |
| regime inclusions | `R ⊆ R34`, `R ⊆ Rtl`: (iii) `lam² ≤ 1-t ⟹ lam²/L² ≤ 1-t`; (i) first conjunct; (ii) second conjunct; (iv) `L^d ≥ L²` | `L ≥ 3` | (iii) factor `1/L² ≤ 1/9`; (iv) factor `L^{2-d} ≤ 1/3` at `d = 3` |

**F(i) `𝔠d` per regime** = row `𝔠d_R`; the six producers per regime (F(ii)). Order (U5S-C3): `(κ, ε, 𝔡)` → `(κ', ε')` → Step 2 `(Cd, c₂)` → `c₃, c₄, c₅, c_tl` at `Cd` → `c₆` → `𝔠d_R` fixed before `(𝔠, sz, z)`; no `∃` after `(sz, z)`; K12 (`baKbound_holds :245`, `baKward_holds :302`) has no constant.
**F(ii) route per target** (merged `file:line`):
| regime | `R34` / `Rtl` | Steps 3, 4 | `Rtl` step | Step 5 | Step 6 (target 10) |
|---|---|---|---|---|---|
| (iii) `STReg5III` | `STReg5III` / `STCaseI` | `baStep3RegIII_holds Step34BA:188`, `baStep4RegIII_holds :232` | `baTwistLoopStep_caseI TwistLoop:705` | hyp. `STStep5IIIgL d`; `d = 3`: `baStep5III_holds Step5IIITargets:57` | `baStep6RegIII_holds Step6BA:148` |
| (i) `STReg5I` | `STReg5I` / `STCaseI` | `baStep3RegI_holds :197`, `baStep4RegI_holds :238` | same | `baStep5I_holds Step5CasesBA:248` (`3 ≤ d`) | `:151` |
| (ii) `STReg5II` | `STCaseII` / `STCaseII` | `baStep3II_holds :206`, `baStep4II_holds :223` | `baTwistLoopStep_caseII :709` | `baStep5II_holds :254` (`3 ≤ d`) | `:154` |
| (iv) `STReg5IV` | `STCaseII` / `STCaseII` | as (ii) | as (ii) | `baStep5IV_holds :260` (all `d`) | `:157` |
Targets 1, 2: `BAFlowMember_holds Step1Fam:624`, `baKbound_holds`, `baFMz_eqAt :273`, `STKboundgL_congr :247`; `baStep1_holds' d (by omega)`. Target 4: `baFamMember_flow`, `BATwistLoopLaw_congr` (`MainIndOutBA:90, 79`). Target 5 body: `ST_mainIndR_of_steps` (`MainIndRegimes:165-214`) + Step 2 `baStep2Decay_holds` + TL1 `TwistStep2_tl1 :1137` (fed by Step 2's `.2.1`, `STLmaxUgL`) + TL2 `Rtl` step; the TL2 premises of `BATwFrame` (`TwistPins:146`) are `twSteps` (`:133`) = Step 2, `STLmaxUgL`, `STLKUgL`, `baDecayLoopU_of` (`DecayLoopBA:60`, inside `baStep2Decay_holds .2`); endpoints as the ticket's table.
**F(vii) slot unification of 10.** `BAStep6R` (`Step6PinsBA:59`) is `STIngR6gL … (fun sz z s t => (TL on [s,t]) → STStep6ConclgL …)`; `T2511_S6In d R ?Concl6` is `STIngR6gL … ?Concl6`, so `baStep6Reg*_holds d` fixes `?Concl6` by delta of `BAStep6R` in argument position. Bridge: the TL premise of `BAStep6R` equals the body of `T2511_TLOn` and the tails agree (script output (4)), so `fun _ _ _ _ h c => c h` closes `T2511_Bridge6` by delta of the check-local def; with the file's inline TL text it is syntactic.
**F(iv) registry scan preview** (`Test/Axioms.lean:494-519` `scanPremises`; `:585` unregistered `throwError`; `:624` `unused` is a report line only). Row a edits no registry line. (1) After row a, `BAMainIndFamTL` is the conclusion head of the new theorems 7-10, so `:140` shows as carrying nothing (F4); no throw. (2) **Finding for 1b (target 6):** the pin text `T2511_S5` is `STStep5RgL d R …`, and `STStep5RgL` is neither registered nor the conclusion head of any theorem (the crude scan, output (5), finds it only in `STStep5R_iff_gL`, an `Iff`; `baStep5*_holds` conclude `STStep5IgL … IVgL`). As a binder of the public target 6 it would be an unclassified premise and the full `#assert_rbm_axioms` (the hub's merge build) would fail, with no registry edit allowed in row a. Fix inside the ticket, no pin moves: state the Step-5 hypothesis of target 6 as its unfolding `STIngR5gL d R law Flow mk T0 (fun sz z s t => STStep5ConclgL (mk sz z) (law sz) s t)` (`STStep5RgL`, `Step5Gen:214-217`, is exactly this); `STIngR5gL` is concluded by the merged `stCltFarUgL_of` (`CltFarUGen:479-485`), so it is proved in the scan. The other binder constants are registered (`STIngR6gL :355`, `STStep6ConclgL :357`, `BATwistAvgLaw :188`, `BATwistLoopLaw :189`, `STLKgL :135`, `STDecaygL :204`, `STDecayStronggL :215`, `STLocalMaxgL :136`, `BAWinBulk :377`, `STConStInd :273`) or concluded by a merged theorem (`STStep3RgL`, `STStep4RgL`: `baStep3/4Reg*_holds`; `BATwistLoopStep`: `baTwistLoopStep_caseI`; `STStep5IIIgL`: `baStep5III_holds`; `BAFlow`, `BAFamZ`, `STExp2gL`). Private targets (3-5) are excluded from the scan (`isInternalDetail`).
**F(v) lines vs stop lines** (output (6); ticket arithmetic reproduced): `MainIndFamTL` 230 / 371 / 797 against 800; `MainIndRegBA` 37 / 70 / 150 against 250; one file 257 / 421 / 917 against 1,000. Sensitivity: the private-datum block of 9′ cannot be shared across files (`Step5CasesBA_sz`, `_flow`, `_datum` are `private`; the parametric block `Step5CasesBA:277-405` is 129 lines), so the instance line is about 184 (129 + 15 for (iii) + 4×10), not the ticket's central 95: `MainIndFamTL` central about 460, still under 800; the hi case keeps 797, 3 lines under the stop line, and is the only risk. Two files as the ticket has them.
**F(vi) greps (preview).** C1, UBA-C1: 0 expected (no `STFlow`, `bandFM`, `lemT`, `mE`; only `seqP (sz.withLam 0)`). X1-C4: the ticket's "= `MainIndFamTL_S1` only" conflicts with its own 9′ and T2501 Amend 1: a `Sizes 3` value needs a `private def` (as `Step5CasesBA:278, 285, 288`). 1b either labels those hits "datum (not a Prop)" or packs each datum in one private `∃ sz z, …` theorem; no public def either way. V2O-C1: row a states no `STAny`, `BAMLOutTL 3`, `UNMLOutBA 3`. `STIngR6gL` hits take the slot `Concl6` (targets 6-9) or come through `BAStep6R` by name (target 10).

### (ii) One concrete nondegenerate instance (`d = 3`)
(iii) `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `Defs/Sizes:260`), `zSeq = w - m_w`, `w = 6i/5`, `flow_sz0` weakened to `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2 ≤ T0` (`half_lt_t0`), regime `lam² ≤ 1/4096 ≤ 1-t`, `BAzSrc sz0 zSeq (2/3) (17/25)` (probe `:310-363`). (i), (ii), (iv) are empty at `sz0` (`1 - s ≤ lam²` fails, `TwistStep2_no_caseII_sz0`); private data on the pattern `Step5CasesBA:277-405` (`L_n = L`, `W_n = n + W₀`, `lam_n = lam`, `w = 5003i/5000`, `z = w - m_w`, flow `(κ_dom, 1/2, 1/9, 1/10)`, family `κ = κ_dom/2`, `s ≡ 0`):
| regime | `(L, W₀, lam)` | `κ_dom` | `t` | regime window | `κ'` | `n₀` |
|---|---|---|---|---|---|---|
| (iii) | `sz0` | `1/2` (family `1/4`) | `1/2` | `lam² ≤ 1-t` all `n` | `0.1118` | 5 |
| (i) | `(4, 25, 1)` | `1/70` | `1/100` | `1/16 ≤ 0.99`, `1 ≤ 1` | `6.0e-4` | 4899 |
| (ii) | `(4, 25, 4)` | `1/1100` | `9/10000` | `1/4 ≤ 0.9991`, `1 ≤ 1` | `9.7e-6` | 1,210,342 |
| (iv) | `(3, 40, 6)` | `1/1000` | `1/2000` | `1 ≤ 4/3` | `1.1e-5` | 1,333,738 |
Window: (iii) `c₁ = 1/3`; (i), (ii), (iv) `c₁` from `BAWinBulk_of_dom_holds 3 _ κ_dom lam` (existential; the numerical window is not collapsed: `min Im m = 0.65, 0.57, 0.67 ≥ κ_dom/2`, `c₁ = 1/2` passes). `STConStInd`: `conStInd_const` (`Step34Pins:825`), `s1Setup_conStInd_const` (`Step1Setup:1226`): any `𝔠d > 0`. The six family conjuncts per member stay binders (the induction hypothesis), as do the slot `Concl6` and bridge in 7-9; target 10 closes them with `baStep6Reg*_holds` and `baStep5III_holds` (`d = 3`). Members: the main flow (`BAFamZ_main`) for (i), (ii), (iv); `BAzSrc` for (iii).
Limit computation for `STConStInd` (the eventual hypothesis; `s = 1/10`, `t = 1/2`, `(1-t)/(1-s) = 5/9`): `Bctl(n, 1/2) ≤ 2(1-t)^{-1} W_n^{-3} = 4 W_n^{-3} → 0`, so `Bctl^{𝔠d} → 0 < 5/9`; the Lean `𝔠d` is the producers' minimum, so the first `n` depends on it (`n₀ = 26, 1326, 5.5e16` for `𝔠d = 1/100, 1/200, 1/1000`, output (3)); the statement is `∀ᶠ`, no `n₀` is chosen.
```
(1) $ cd <scratchpad>/T2511 && python3 preflight.py          # (3) = this output; script reads Defs/Lattice Adj (nearest neighbours), BAmSubord, BASelf, BAt0, BAflowE, Bparam as in the files
```
```
(3) (iii) n=0..39: lam^2<=1/4096<=1-t=1/2 and lam^2/L^2<=1/2 : True | s=1/10<t=1/2<2/3<=T0 (t0_sz0)
(iii) n=0: Im m=0.8325 T0=0.6937; window c1=1/3: min Im m(E,g') on [sqrt(2/3) g0,g0] = 0.9995 >= kappa=1/2 (flow) and 1/4 (family): True
(iii) Bctl(n,1/2) <= 2(1-t)^-1 W^-3 = 4 W^-3 (n<40): True ; (1-t)/(1-s) = 5/9
(iii) con_st_ind (Bctl^c_d <= 5/9): c_d=0.01: n0=26
(iii) con_st_ind (Bctl^c_d <= 5/9): c_d=0.005: n0=1326
(iii) con_st_ind (Bctl^c_d <= 5/9): c_d=0.001: n0=54601638786650584
(iii) member flow: c_kappa(1/4)=0.44721 kappa'=0.11180 (<= 1/4) eps'=eps/2=1/20 n0=5 (size_n0^-(eps/2) < kappa')
(i) L=4 W0=25 lam=1 kdom=0.014286 t=0.01: regime True, Case inclusion True; Im m=0.4180>=lb 0.01539>=kdom True; Im z=0.5826>=N0^-1/2=1.0e-03; t<=kdom/(1+kdom)=0.014085<=T0=0.4177: True
    c1 proof value min(1/2,kdom^9/(64 d lam))=1.29e-19; numerical window Im m>=kdom/2 on [sqrt(1/2) g0,g0]: min=0.6467 (c1=1/2 passes: True); kappa'=6.02e-04 eps'=1/4 n0=4899
(ii) L=4 W0=25 lam=4 kdom=0.000909 t=0.0009: regime True, Case inclusion True; Im m=0.3203>=lb 0.00098>=kdom True; Im z=0.6803>=N0^-1/2=1.0e-03; t<=kdom/(1+kdom)=0.000908<=T0=0.3201: True
    c1 proof value min(1/2,kdom^9/(64 d lam))=5.52e-31; numerical window Im m>=kdom/2 on [sqrt(1/2) g0,g0]: min=0.5661 (c1=1/2 passes: True); kappa'=9.69e-06 eps'=1/4 n0=1210342
(iv) L=3 W0=40 lam=6 kdom=0.001000 t=0.0005: regime True, Case inclusion True; Im m=0.4458>=lb 0.00103>=kdom True; Im z=0.5548>=N0^-1/2=7.6e-04; t<=kdom/(1+kdom)=0.000999<=T0=0.4455: True
    c1 proof value min(1/2,kdom^9/(64 d lam))=8.68e-31; numerical window Im m>=kdom/2 on [sqrt(1/2) g0,g0]: min=0.6679 (c1=1/2 passes: True); kappa'=1.12e-05 eps'=1/4 n0=1333738
```
```
(4) $ python3 (text compare of Step6PinsBA.lean:59-63 and T2511-check.lean, whitespace-normalised)
BAStep6R premise == T2511_TLOn body (modulo outer parens): True
BAStep6R tail: True | Bridge6 tail: True
(5) $ python3 scan.py STStep5RgL STIngR5gL STStep5IIIgL BATwistLoopStep   # public theorem headers mentioning the constant
STStep5RgL 1 [('Chain/Step5Gen.lean', 'STStep5R_iff_gL')]
STIngR5gL 3 [('Chain/Step5Gen.lean', 'Step5Gen_ingR5_iff_congr'), ('Chain/Step5Gen.lean', 'STIngR5_iff_gL'), ('Chain/CltFarUGen.lean', 'stCltFarUgL_of')]
STStep5IIIgL 3 [('Chain/Step5Gen.lean', 'STStep5III_iff_gL'), ('Chain/Step5CasesGen.lean', 'ST_step5_caseIII_of_pfgL'), ('BA/Step5IIITargets.lean', 'baStep5III_holds')]
BATwistLoopStep 3 [('BA/TwistLoop.lean', 'baTwistLoopStep_of_fixed'), ('BA/TwistLoop.lean', 'baTwistLoopStep_caseI'), ('BA/TwistLoop.lean', 'baTwistLoopStep_caseII')]
(6) $ python3 prices.py
family part lo/central/hi 41 62 107
MainIndFamTL lo/central/hi (230, 371, 797) stop 800
MainIndRegBA lo/central/hi (37, 70, 150) stop 250
row a total (267, 441, 947) one file stop 1000
instance block estimate 184 -> MainIndFamTL central 460  hi-case kept 797 (stop 800)
```
### Verdicts (row a)
Targets 1, 2 (K2, family Step-1 call), 3-5 (private def, wrapper, step body), 6 (generic step, with the Step-5 binder as `STIngR5gL … STStep5ConclgL`, F(iv)), 7-9 (four regimes), 10 (closed regimes): **PASS**. Every hypothesis of every target holds at the data above; no exponent fails (`𝔠d_R`, `κ'`, `ε'`, `c₁`, regime inclusions all have positive slack; the six `∃` constants are produced by merged theorems read by name).
1a-audit: not needed (no pin, row or stop line moves).

## (b) Script output and narrative (row a: `RBM3D/BA/MainIndFamTL.lean`, `RBM3D/BA/MainIndRegBA.lean`, two root import lines; branch `t/T2511`, commits 7407a4f3, 70407ac7, eed83cc4 on `main` 97779231)
Times from `date -u` in the tool log (Thu Oct 15 2026 UTC): first 1b command 06:33:55; the `date -u` printed in the same command as the three commits reads 06:40:12 (targets 1-9), 06:43:26 (instances), 06:50:23 (target 10, imports). No (a') section: nothing in (a) was wrong.
```
$ date -u
Thu Oct 15 06:51:15 UTC 2026
$ lake build RBM3D.BA.MainIndFamTL RBM3D.BA.MainIndRegBA 2>&1 | tail -1
Build completed successfully (4309 jobs).
$ lake build 2>&1 | tail -1      # whole library, runs #assert_rbm_axioms (root imports added)
Build completed successfully (4416 jobs).
$ lake env lean scan_after.lean | sed -n "1p;131p" | cut -c1-210   # import RBM3D; #assert_rbm_axioms
axiom audit: 15441 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 121 owed + 141 structural + 7 refuted + 19 superseded; 162 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ wc -l RBM3D/BA/MainIndFamTL.lean RBM3D/BA/MainIndRegBA.lean
     397 RBM3D/BA/MainIndFamTL.lean
     113 RBM3D/BA/MainIndRegBA.lean
     510 total
```
```
$ lake env lean auditcheck.lean   # scratch (uncommitted): T2511-check.lean + imports of the two new modules + the examples below; exit code, error count
exit=0  error lines: 0  sorry lines: 0
$ sed -n "/Auditor-style/,/^#print axioms MainIndFamTL_famOfS1/p" auditcheck.lean   # target = pin up to unfolding (each example compiles; private ones through open private)
open private MainIndFamTL_S1 MainIndFamTL_famOfS1 MainIndFamTL_s1OfSteps from RBM3D.BA.MainIndFamTL
example (d : ℕ) : T2511_K2Member d := baKboundMember_holds d
example (d : ℕ) : T2511_FamStep1Call d := baStep1Fam_call d
example (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : MainIndFamTL_S1 d R = T2511_S1 d R := rfl
example (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : T2511_FamOfS1 d R := MainIndFamTL_famOfS1 d R
example (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : T2511_S1OfSteps d R R34 Rtl := MainIndFamTL_s1OfSteps d R R34 Rtl
example (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : T2511_FamOfSteps d R R34 Rtl := baMainIndFamTL_of_steps d R R34 Rtl
example (d : ℕ) : T2511_RegIIIOf d := baMainIndFamTL_III_of d
example (d : ℕ) : T2511_RegIOf d := baMainIndFamTL_I_of d
example (d : ℕ) : T2511_RegIIOf d := baMainIndFamTL_II_of d
example (d : ℕ) : T2511_RegIVOf d := baMainIndFamTL_IV_of d
example : T2511_Closed := ⟨baMainIndFamTL_III, baMainIndFamTL_III_three, baMainIndFamTL_I, baMainIndFamTL_II, baMainIndFamTL_IV⟩
$ grep "depends on axioms" audit.out
'_private.RBM3D.BA.MainIndFamTL.0.RBM.BA.MainIndFamTL_famOfS1 :: [propext,
'_private.RBM3D.BA.MainIndFamTL.0.RBM.BA.MainIndFamTL_s1OfSteps :: [propext,
'_private.RBM3D.BA.MainIndFamTL.0.RBM.BA.MainIndFamTL_S1 :: [propext, Classical.choice, Quot.sound]
baKboundMember_holds :: [propext, Classical.choice, Quot.sound]
baStep1Fam_call :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_of_steps :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_III_of :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_I_of :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_II_of :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_IV_of :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_III :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_III_three :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_I :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_II :: [propext, Classical.choice, Quot.sound]
baMainIndFamTL_IV :: [propext, Classical.choice, Quot.sound]
```
```
$ grep "depends on axioms" audit.out | group by axiom list   (#print axioms of the 12 public targets and private 3-5)
15 declarations [propext, Classical.choice, Quot.sound]:
   private MainIndFamTL_famOfS1, private MainIndFamTL_s1OfSteps, private MainIndFamTL_S1, baKboundMember_holds, baStep1Fam_call, baMainIndFamTL_of_steps, baMainIndFamTL_III_of, baMainIndFamTL_I_of, baMainIndFamTL_II_of, baMainIndFamTL_IV_of, baMainIndFamTL_III, baMainIndFamTL_III_three, baMainIndFamTL_I, baMainIndFamTL_II, baMainIndFamTL_IV
```
```
$ python3 extract.py   # statement text up to ":=" of the 12 public targets and private 3-5 (3: `: Prop` here, body = the `rfl` example above), whitespace-normalised
MainIndFamTL.lean:53: theorem baKboundMember_holds (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' → STKboundgL (baFMz sz z') (Sizes.seqP (sz.withLam 0))
MainIndFamTL.lean:68: theorem baStep1Fam_call (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → (∀ z' : ℕ → ℂ, BAFamZ sz z c₁ s z' → let C := baFMz sz z'; let μ := Sizes.seqP (sz.withLam 0) STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) → sz.STConStInd 𝔠d s t → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' → STStep1LoopgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t ∧ STStep1WeakgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s t
MainIndFamTL.lean:187: theorem baMainIndFamTL_of_steps (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t) → (3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → Rtl sz s t) → BATwistLoopStep d Rtl → STStep3RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → STStep4RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → STIngR5gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) → ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6 → (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) → BAMainIndFamTL d R
MainIndFamTL.lean:210: theorem baMainIndFamTL_III_of (d : ℕ) : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, STIngR6gL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6 → (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) → BAMainIndFamTL d STReg5III
MainIndFamTL.lean:225: theorem baMainIndFamTL_I_of (d : ℕ) : ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, STIngR6gL d STReg5I (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6 → (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) → BAMainIndFamTL d STReg5I
MainIndFamTL.lean:239: theorem baMainIndFamTL_II_of (d : ℕ) : ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, STIngR6gL d STReg5II (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6 → (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) → BAMainIndFamTL d STReg5II
MainIndFamTL.lean:252: theorem baMainIndFamTL_IV_of (d : ℕ) : ∀ Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop, STIngR6gL d STReg5IV (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6 → (∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) → BAMainIndFamTL d STReg5IV
MainIndRegBA.lean:36: theorem baMainIndFamTL_III : ∀ d : ℕ, STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) → BAMainIndFamTL d STReg5III
MainIndRegBA.lean:42: theorem baMainIndFamTL_III_three : BAMainIndFamTL 3 STReg5III
MainIndRegBA.lean:45: theorem baMainIndFamTL_I : ∀ d : ℕ, BAMainIndFamTL d STReg5I
MainIndRegBA.lean:49: theorem baMainIndFamTL_II : ∀ d : ℕ, BAMainIndFamTL d STReg5II
MainIndRegBA.lean:53: theorem baMainIndFamTL_IV : ∀ d : ℕ, BAMainIndFamTL d STReg5IV
MainIndFamTL.lean:88: private def MainIndFamTL_S1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop
MainIndFamTL.lean:101: private theorem MainIndFamTL_famOfS1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : MainIndFamTL_S1 d R → BAMainIndFamTL d R
MainIndFamTL.lean:122: private theorem MainIndFamTL_s1OfSteps (d : ℕ) (R R34 Rtl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (hR : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → R34 sz s t) (hRtl : 3 ≤ d → ∀ (sz : Sizes d) (s t : ℕ → ℝ), R sz s t → Rtl sz s t) (hTL : BATwistLoopStep d Rtl) (h3 : STStep3RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (h4 : STStep4RgL d R34 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (h5 : STIngR5gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)) (Concl6 : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h6 : STIngR6gL d R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) Concl6) (hb : ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u ∧ BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) u) → Concl6 sz z s t → STStep6ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) : MainIndFamTL_S1 d R
```
```
$ grep -n "^example" A B | cut -d: -f1 | paste -sd" " -   # line numbers of the compiled instances; the comment above each names its target
MainIndFamTL.lean: 286 291 317 327 362 372 382
MainIndRegBA.lean: 76 81 86 94 102
$ sed -n 317,325p RBM3D/BA/MainIndFamTL.lean   # target 6 at (sz0, zSeq), regime (iii): R, R34, Rtl and Steps 3-5 by name
example (h6 : STIngR6gL 3 STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
      (fun sz z => BAflowT0 sz z) Concl6)
    (hfam : ∀ z', BAFamZ sz0 zSeq (1 / 3) (fun _ => 1 / 10) z' → Fam6(baFMz sz0 z', μ0, fun _ => 1 / 10)) :
    Fam7(baFMz sz0 mem0, μ0, fun _ => 1 / 2) :=
  MainIndFamTL_atSz0
    (baMainIndFamTL_of_steps 3 STReg5III STReg5III STCaseI (fun _ _ _ _ h => h) (fun _ => st_caseI_of_reg5III 3) (baTwistLoopStep_caseI 3)
      (baStep3RegIII_holds 3) (baStep4RegIII_holds 3) baStep5III_holds Concl6 h6 hb)
    (fun n => by nlinarith [sz0_lam_le n, sz0_lam_pos n]) hfam
$ sed -n 86,91p RBM3D/BA/MainIndRegBA.lean   # target 10, regime (i) at the Step5CasesBA datum: every premise discharged but the family conjuncts
example : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
    ((∀ z', BAFamZ Step5CasesBA_szI Step5CasesBA_zI c₁ (fun _ => 0) z' →
        Fam6(baFMz Step5CasesBA_szI z', Sizes.seqP (Step5CasesBA_szI.withLam 0), fun _ => 0)) →
      Fam7(baFMz Step5CasesBA_szI Step5CasesBA_zI, Sizes.seqP (Step5CasesBA_szI.withLam 0), fun _ => 1 / 100)) :=
  MainIndFamTL_atDatum STReg5I (baMainIndFamTL_I 3) Step5CasesBA_datI 10 (by norm_num)
    (fun n => ⟨by norm_num [Step5CasesBA_szI, Step5CasesBA_sz], by norm_num [Step5CasesBA_szI, Step5CasesBA_sz]⟩) Step5CasesBA_regI
```
```
$ grep -nE "mE\b|\|E\||SB d|M = m|m • 1|etaT|STFlow|bandFM|lemT" A B | wc -l      # C1
       0
$ grep -nE "^(private )?(noncomputable )?(def|abbrev|structure) " A B | cut -c1-80      # X1-C4
RBM3D/BA/MainIndFamTL.lean:88:private def MainIndFamTL_S1 (d : ℕ) (R : ∀ {d : ℕ}
$ grep -nE "STAny|BAMLOutTL 3|UNMLOutBA 3" A B | wc -l      # V2O-C1
       0
$ grep -nE "STIngR6gL|STStep6ConclgL|BATwistAvgLaw" B | wc -l      # no second text of BAStep6R in RegBA
       0
$ python3 classify.py     # the same three names in A, each hit classified (script reads the line and the next)
BATwistAvgLaw   bridge premise (TL1 at u in [s,t])   8 hit(s)  lines 137,202,218,231,245,258,312,357
STIngR6gL       doc/comment                          2 hit(s)  lines 32,185
STIngR6gL       slot variable Concl6                 11 hit(s)  lines 133,198,214,227,241,254,317,327,362,372,382
STStep6ConclgL  bridge conclusion                    8 hit(s)  lines 138,203,219,232,246,259,313,358
STStep6ConclgL  proof term/doc                       2 hit(s)  lines 175,186
$ grep -n withLam A B | grep -vE "seqP \((sz|sz0|Step5CasesBA_sz[IV]*)\.withLam 0\)" | wc -l      # UBA-C1
       0
$ grep -n "∃ 𝔠d" A B ; grep -n "∃ c₁" A B   # U5S-C3, file:line (these are all 9 hits of grep -n "∃")
∃ 𝔠d: MainIndFamTL.lean:89
∃ c₁: MainIndFamTL.lean:338 MainIndFamTL.lean:345 MainIndFamTL.lean:364 MainIndFamTL.lean:374 MainIndFamTL.lean:384 MainIndRegBA.lean:86 MainIndRegBA.lean:94 MainIndRegBA.lean:102
```
```
$ diff scan_before.out scan_after.out | grep -E "theorems|BAMainIndFamTL|BATwistLoopLaw" | grep -v "^[0-9]*c[0-9]*$"   # #assert_rbm_axioms output, imports of RBM3D.lean without / with the two new modules
< axiom audit: 15429 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
> axiom audit: 15441 theorems, 4728 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
<   RBM.BA.BAMainIndFamTL: 3 [no certificate]
>   RBM.BA.BAMainIndFamTL: 13 [no certificate]
<   RBM.BA.BATwistLoopLaw: 3 [no certificate]
>   RBM.BA.BATwistLoopLaw: 9 [no certificate]
>  RBM.BA.BAMainIndFamTL,
<  RBM.BA.BATwistLoopLaw,
$ grep -c "premise(s) that no theorem" scan_before.out scan_after.out    # the throw text of an unregistered premise
scan_after.out:0
scan_before.out:0
$ clash.sh | awk (summary of grep -rnw over the 18 new names: this worktree outside the two files, main RBM3D/ and DECISIONS.md, main docs/tickets outside T2511*)
18 names checked; worktree hits outside the two files: none
main RBM3D/ + DECISIONS.md hits: baKboundMember_holds(main:1)
main docs/tickets hits outside T2511*: baMainIndFamTL_III(tickets:1) baMainIndFamTL_III_three(tickets:1) baMainIndFamTL_I(tickets:1)
$ git diff --shortstat 97779231 HEAD ; git diff --name-only 97779231 HEAD
 3 files changed, 512 insertions(+)
RBM3D.lean
RBM3D/BA/MainIndFamTL.lean
RBM3D/BA/MainIndRegBA.lean
$ git diff --stat 97779231 HEAD -- RBM3D/Chain RBM3D/Induction RBM3D/Graph RBM3D/Test | wc -l ; git diff --name-only 97779231 HEAD -- RBM3D/BA | grep -v "BA/MainIndFamTL.lean\|BA/MainIndRegBA.lean" | wc -l
       0
       0
$ git diff 97779231 HEAD -- RBM3D.lean | grep "^[+-]import"
+import RBM3D.BA.MainIndFamTL
+import RBM3D.BA.MainIndRegBA
```
**Narrative (row a).**
1. **Lines against the ticket.** `MainIndFamTL` 397 (stop 800; bottom-up lo/central/hi 230/371/797), `MainIndRegBA` 113 (stop 250; 37/70/150), together 510 (row-a central 441, calibrated 423-564; one-file stop 1,000). Instances: `MainIndFamTL` lines 264-393 (130), `MainIndRegBA` lines 56-109 (54).
2. **Route per target** (every producer merged, read by name; no restated merged text):
   - 1: `BAFlowMember_holds` (`Step1Fam:624`), `baKbound_holds` at the modified flow, `baFMz_eqAt`, `STKboundgL_congr`. 2: `baStep1_holds' d (by omega)` with 1.
   - 3-4: private def `MainIndFamTL_S1` (T2503 D1 (b) text); wrapper = probe `T2503_famOfS1` with `baFamMember_flow`, `BATwistLoopLaw_congr`, the ten `_congr` (`Step1Fam:205-260`), `baStep1Fam_call`.
   - 5: the body of `ST_mainIndR_of_steps` (`MainIndRegimes:165-214`). Step 2 is `baStep2Decay_holds d (baLWterm_holds d) (baLWtermExp_holds d)` giving `(Cd, c₂)`; Steps 3, 4, 5, 6 and the TL2 step give `c₃..c₇`; `𝔠d = min c₂ (min c₃ (min c₄ (min c₅ (min c₆ c₇))))`. K12 `baKbound_holds`, `baKward_holds`.
     TL1 at every `u ∈ [s,t]` is `TwistStep2_tl1` (fed by Step 2's `STAvgUgL` and `STLmaxUgL`); TL2 at every `u` is the TL2 step with `twSteps = ⟨Step-2 conclusion, STLmaxUgL, STLKUgL, STDecayLoopUgL⟩` (no cast); the bridge gives `STStep6ConclgL`.
     Endpoints `ST_step5_assemblygL`, `STLKgL_of_STLKUgL`, `STLmaxgL_of_STLmaxUgL`, `STExp2gL_of_STExp2UgL`, `STLocalEntrygL_of_STLocalEntryUgL`; `st5_conStInd_mono` with `EMn2BA_T0_lt_one` for `t < 1`.
     The ticket's table also names `STLocalMaxgL_of_STLocalEntrygL` (`MainIndChain:126`): no step of 5 consumes it, so no name of `Induction/MainIndChain` is used (the import stays as the ticket lists it).
   - 6: `MainIndFamTL_famOfS1 d R (MainIndFamTL_s1OfSteps ...)`. 7-9: 6 at `(R, R34, Rtl)` = (iii) `(STReg5III, STReg5III, STCaseI)`, (i) `(STReg5I, STReg5I, STCaseI)`, (ii) `(STReg5II, STCaseII, STCaseII)`, (iv) `(STReg5IV, STCaseII, STCaseII)`; Steps 3-4 `baStep3RegIII_holds`/`baStep4RegIII_holds`, `baStep3RegI_holds`/`baStep4RegI_holds`, `baStep3II_holds`/`baStep4II_holds` (T2509);
     TL2 step `baTwistLoopStep_caseI/II`; Step 5 (iii) the hypothesis, (i) `baStep5I_holds d hd hd`, (ii) `baStep5II_holds d hd hd`, (iv) `baStep5IV_holds d`; inclusions `st_caseI_of_reg5III/I`, `st_caseII_of_reg5II/IV`.
   - 10: 7-9 at `_` with `baStep6Reg*_holds d` and the bridge `fun _ _ _ _ h c => c h`, no adapter; `baMainIndFamTL_III_three := baMainIndFamTL_III 3 baStep5III_holds`. The coverage table as used is (a) F(ii), unchanged.
3. **Step-5 binder of target 6** (the one 1b instruction of (a) F(iv)): targets 5-9 take `STIngR5gL d R ... (fun sz z s t => STStep5ConclgL ...)`, the unfolding of `STStep5RgL` (`Step5Gen:214-217`); `T2511_FamOfSteps d R R34 Rtl := baMainIndFamTL_of_steps d R R34 Rtl` compiles; the full scan throws nothing (scan block).
4. **Instance data.** (iii): `sz0`, `zSeq`, `flow_sz0` weakened to `κ = 1/4`, `(ε, 𝔠, 𝔡) = (1/10, 1/6, 1/10)`, `c₁ = 1/3`, `s ≡ 1/10 < t ≡ 1/2`, regime `lam² ≤ 1/4096 ≤ 1 - t`, member `BAzSrc sz0 zSeq (2/3) (17/25)`.
   (i), (ii), (iv): `(L, W₀, lam, κ_dom, t)` = (4, 25, 1, 1/70, 1/100), (4, 25, 4, 1/1100, 9/10000), (3, 40, 6, 1/1000, 1/2000), `s ≡ 0`, flow `(κ_dom, 1/2, 1/9, 1/10)`, family `κ = κ_dom/2`, `c₁` = the existential of `BAWinBulk_of_dom_holds 3 le_rfl κ_dom 10`, `(con_st_ind)` at every `𝔠d > 0` from the datum.
   These data and `MainIndOutBA`'s `_flow/_win/_mem` are read by `open private` (as `MainIndOutBA:49` does for `TwistChain`), not copied: no new datum def, so the X1-C4 grep shows `MainIndFamTL_S1` only. The ticket text suggested new private data on `TwistStep2_szII` or the `ZeroModeBA` pattern; this reuses the merged T2501 pattern with the (a) numbers.
5. **Hypotheses left in the instances:** `hfam` (the six conjuncts at every member of `Fam(s)`, the induction hypothesis) in all; in the `MainIndFamTL` instances of 6 and 7 also `Concl6`, the slot Step 6 `h6` and the bridge `hb`. The instances of target 10 (`MainIndRegBA`) leave only `hfam`.
6. **Registry (row a edits none).** `BAMainIndFamTL` (`:140`) is now in the "carry nothing" list; `BATwistLoopLaw` (`:189`) left it (a binder premise of public theorems now); 15,441 theorems (+12 public), 0 axioms, 0 unregistered premises.
7. **Stop rules:** none triggered: no target differs from its pin, no merged text or `private` changed (`RBM3D/BA` diff outside the two files and `Chain`, `Induction`, `Graph`, `Test` diffs empty), one private def and no public def, no terminal in row a (V2O grep 0), no file over a stop line.
8. **Ports:** none from RBM1D or RBM2D (neither project was read). Proof models: probe `t/T2503` 93bd54cd `RBM3D/Probe/T2503Pins.lean:103-139, 290-363` (texts of 1, 2, 4 adapted from `T2503_k2Member`, `T2503_famStep1Call`, `T2503_famOfS1`) and the band `ST_mainIndR_of_steps`.

## (c) Verified Mathlib names used (`#check` in a scratch file importing the new modules, exit 0)
```
@lt_min : ∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a < b → a < c → a < min b c
@min_le_left : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), min a b ≤ a
@min_le_right : ∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), min a b ≤ b
@half_pos : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α], 0 < a → 0 < a / 2
@Filter.eventually_atTop : ∀ {α : Type u_1} [inst : Preorder α] [IsDirectedOrder α] {p : α → Prop} [Nonempty α], (∀ᶠ (x : α) in Filter.atTop, p x) ↔ ∃ a, ∀ (b : α), a ≤ b
@LE.le.trans_lt : ∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b < c → a < c
@LT.lt.le : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
```
Names verified absent: none looked for. Merged project names read by name: the 51 `#check` lines of Part 1 of `T2511-check.lean` and the `T2511_*` pins all elaborate in `auditcheck.lean` (exit=0, 0 error lines, block above).

## (d) Open issues and paper-delta candidates
- **Paper-delta candidates:** none (`T2511a`: none). The only text difference between a target and its pin is an unfolding (target 6, Step-5 binder, narrative 3), not a paper difference.
- **Row b and T2512 read these names:** `baMainIndFamTL_III_three`, `baMainIndFamTL_I 3`, `baMainIndFamTL_II 3`, `baMainIndFamTL_IV 3` (binder order of `T2512_OfRegimes`: (iii), (i), (ii), (iv)); general `d`: `baMainIndFamTL_III d h5` with `h5 : STStep5IIIgL d ...` (DECISIONS §316, `d > 3` (iii) out of scope, Jun decision B).
- **Registry for row b:** `BAMainIndFamTL` (`:140`) stays registered until row b deletes it; `BATwistLoopLaw` now carries public theorems (no edit needed).
- **Coupling:** the instances read `private` data of merged `Step5CasesBA` and `MainIndOutBA` by `open private`; renaming those privates would break the instances, not the targets.
- **Windows:** `c₁` for (i), (ii), (iv) is existential (`BAWinBulk_of_dom_holds`; (a) computed the proof values 1.3e-19, 5.5e-31, 8.7e-31); the (a) numerical `c₁ = 1/2` is not used.
- **Imports:** `BA/MainIndFamTL` imports `Induction/MainIndChain` as the ticket lists it; nothing from it is used.
