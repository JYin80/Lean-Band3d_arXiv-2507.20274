Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 14:09:03 UTC 2026

Scope: stage 1a design gate of T2457 (D1-D3 as far as mathematics decides them; no Lean written). Facts below are cited
as file:line from the tree at `main` b25e37e, or are script output.

### (i) Exponent table

Notation: `g` = the kernel coupling (band: `sz.lam n`; BA: `lam0 n = BAflowLam0 = sqrt(t0)*sz.lam n`, `BA/FlowPins.lean:386`),
`t0 = Im m/(Im m + Im z)` (`BA/MFixedPoint.lean:279`), `r(g;v,t) = (g^2+|1-v|)/(g^2+|1-t|)`, `ell = ellT L g u` (`Defs/Params.lean:32`).

| # | quantity | value / constraint | slack (explicit) |
|---|---|---|---|
| 1 | `t0` | in (0,1) when `Im z > 0`, `Im m > 0` (`BAt0_pos`, `BAt0_lt_one`, `MFixedPoint:282-285`) | `lam0 = sqrt(t0) lam < lam`: gap `lam - lam0 > 0` |
| 2 | lower bound of `t0` | `t0 >= kappa/(kappa+1)` from `BAdom` (`kappa <= Im m`, `Im z <= 1`, `MFixedPoint:435-436`), since `x/(x+y)` increases in `x`, decreases in `y` | kappa=0.1: `1/11 = 0.0909`; instance `t0 = 1 - 8.1e-10` |
| 3 | stage-E range of `g` | `0 < g <= Lambda`, `Lambda = 1/dd` (`EKPins.lean:97-141`; `Admissible` gives `lam <= 1/dd` eventually, `Defs/Sizes.lean:164-165`) | band `g=lam`: instance `2.4e-4 <= 4`; BA `g=lam0 <= lam`: same slack |
| 4 | window `t <= 1 - g^2/L^2` (STEKWin; `EKSumDecay1/NAL/2` at `g`) | form at `lam`, kernel at `lam0`: `1-lam^2/L^2 <= 1-lam0^2/L^2`, so hypothesis at `lam` implies stage E's at `lam0` | gap `(1-t0) lam^2/L^2`; instance `t=1/16`, `1-t-lam^2/L^2 = 0.9375` |
| 5 | case (ii) threshold `1-g^2/L^2 <= s` (STEKNonzero; `EKPins:136-139`) | form at `lam`, kernel at `lam0`: `s >= 1-lam^2/L^2` does NOT imply `s >= 1-lam0^2/L^2`; range where stage E's case-(ii) hypothesis fails: `[1-lam^2/L^2, 1-lam0^2/L^2)` has length `(lam^2-lam0^2)/L^2 = (1-t0)lam^2/L^2` | worst `t0 = 1/11`: `8.5e-10` > 0 (nonempty at every `t0 < 1`) |
| 6 | ratio loss, `v <= t < 1` | `r(lam0)/r(lam) <= 1/t0` (per factor; `1/t0^n_` total) | grid max 9.52 <= 11 = `1/t0` (worst `t0`); `1/t0 <= (kappa+1)/kappa` |
| 7 | `ell` loss | `ell(lam0,u) >= sqrt(t0) ell(lam,u)` | grid min 0.3015 = `sqrt(1/11)` (equality) |
| 8 | decay cutoff conversion (producer side; hypothesis of no target) | decay beyond `W^{eps/2} ell(lam)` gives decay beyond `W^eps ell(lam0)` iff `W^{eps/2} >= 1/sqrt(t0)`; with row 2 suffices `W >= ((kappa+1)/kappa)^{1/eps}` | `eps=1/2`: `W >= 121`; `n=1: W=1024` (5.66 >= 3.32); `n=0: W=32` fails (2.38 < 3.32) |
| 9 | stage-E side conditions at `g` | `1<W`, `0<eps<1`, `1<D`, `4<=W^eps`, `log L <= W^eps`, `L^d <= W^K`, `K = 1/cc` (`EKPins:103-132`; `Bandwidth`, `Defs/Sizes.lean:168`) | instance `4<=32`, `log 8=2.08<=32`, `512<=2^50` |
| 10 | Step 3/4 constants (`STStep3R/4R`, `Step34Pins:250-261`) | `0<cd<=1/100`; `(con_st_ind)`: `Bctl^cd <= (1-t)/(1-s) < 1` (`Induction/Defs.lean:168`) | `cd=1/100`, `s=0,t=1/16`: `0.8128 <= 0.9375 < 1`; slack `0.125` |
| 11 | `Admissible`: `WO dd`, `Bandwidth cc` | `W^{-d/2+dd} <= lam <= 1/dd`; `N^cc <= W` | `dd=1/4`: `1.73e-4 <= 2.44e-4`; `cc=1/5`: `222.9 <= 1024` |
| 12 | band bridges `STEKDecay -> STEKDecaygL`, `STEKLow` | `STEKLow` has no `g` (`Step34Pins:601-603`); `STEKDecay` reads `EKFastDecay (sz.lam n)` (`Step34Pins:596-600`, `Evolution/Pins.lean:51-53`) | exact (syntactic) at `g := sz.lam` |

### (ii) One concrete nondegenerate instance and checks

Data: `d=3`, `sz0` at `n=1` (`Defs/Sizes.lean:260-263`: `L=8`, `W=1024`, `lam=(4)^-6=2.44e-4`, `N=(WL)^3=2^39`), `kappa=1/10`, `dd=1/4`, `cc=1/5`,
`eps=1/2`, `D=2`, `z = 1/2 + i N^{-4/5}` (`Induction/Defs.lean:413`), `Im m = 1/2`, `s=0`, `t=1/16` (`Induction/Defs.lean:439-440`), `cd=1/100`.
Every numeric hypothesis of targets 1-9 shared by the instance is checked: `Admissible` (WO, Bandwidth), the stage-E side conditions, the windows, `(con_st_ind)`,
`0 < lam0 <= lam <= 1/dd`. Hypotheses that are other gates' pins (`STKboundgL`, `STKwardgL`, `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, and the owed
`STLmaxUgL`, `STLKUgL`) stay hypotheses; they carry no numeric constraint beyond the above.

Command: `python3 -I $S/inst.py` (scratch, not Lean; `S` = scratchpad `T2457/`). Output:
```
L,W,lam,N = 8 1024 0.000244140625 549755813888
WO lower  W^(-d/2+dd) <= lam : 0.00017263349150062197 <= 0.000244140625 True
WO upper  lam <= 1/dd        : 0.000244140625 <= 4.0 True
Bandwidth N^cc <= W          : 222.86094420380783 <= 1024 True
stage E:  4<=W^eps True | log L<=W^eps True | L^d<=W^K True | 1<D True | eps<1 True
Im z = 4.0538169597095024e-10 t0 = 0.9999999991892365 lam0 = 0.00024414062490102985
0<lam0<=lam<=1/dd : True
t0 >= kap/(kap+1) = 0.09090909090909091 True
window at lam :  t<=1-lam^2/L^2 True | W^-1<=(1-t)/(1-s) True | con_st_ind:
   Bctl^(1/100) = 0.8127926399408196  <= (1-t)/(1-s) = 0.9375 <1 : True
window at lam0 (weaker):  True ; slack in 1-t-lam^2/L^2 = 0.9374999990686774
instance t0 : max r(lam0)/r(lam) = 1.000000000750598 <= 1/t0 = 1.0000000008107635 True | min ell(lam0)/ell(lam) = 0.9999999995946183 >= sqrt(t0)= 0.9999999995946183 True
   Nonzero case (ii) gap  [1-lam^2/L^2, 1-lam0^2/L^2) has length 7.55082309591987e-19
worst t0 : max r(lam0)/r(lam) = 9.518518518518519 <= 1/t0 = 11.0 True | min ell(lam0)/ell(lam) = 0.30151134457776363 >= sqrt(t0)= 0.30151134457776363 True
   Nonzero case (ii) gap  [1-lam^2/L^2, 1-lam0^2/L^2) has length 8.466568860140713e-10
conversion W^(eps/2) >= 1/sqrt(t0): 5.656854249492381 >= 3.3166247903554 True ; at n=0 (W=32): 2.378414230005442 False
```
External (eventual) hypotheses, concrete limit computation over the whole sequence `sz0` (`WO`, `Bandwidth`, `(con_st_ind)` at `cd=1/100`, `s=0,t=1/16`):
Command: `python3 -I $S/lim.py`. Output:
```
n in 0..20000 failing WO/Bandwidth/con_st_ind (cd=1/100): []
n= 0 Bctl^(1/100) = 0.9019698242288372
n= 1 Bctl^(1/100) = 0.8127926399408196
n= 10 Bctl^(1/100) = 0.629385793942528
n= 100 Bctl^(1/100) = 0.4513127281491712
n= 10000 Bctl^(1/100) = 0.226526635053139
```
(`Bctl^(1/100) -> 0`, so `(con_st_ind)` holds for all large `n` with the margin `0.9375`; `lam -> 0`, `t0 -> 1` along `z0` since `Im z -> 0`.)

### Decisions (mathematics only; Lean checks are the probe step's)

- **D3 (b), coupling.** Decision: the five `STEK*` consumer forms, `STEKWin`, and the decay form carry a coupling sequence `gK : ℕ → ℝ` read by the kernel class
  (`Ker sz C gK kappa` holds the link of `Step2Gen_UN C` to `gK`), by `EKFastDecay (gK n)`, by `ellT L (gK n)`, by the ratio `r(gK)` and by the
  windows; hypothesis `∀ᶠ n, 0 < gK n ∧ gK n <= dd⁻¹`. Band: `gK = sz.lam` (bridges from `stek_*_holds`, positivity eventually from `WO`).
  BA: `gK = lam0`, then each form is stage E's `BAEKSum*` at `g = lam0 n` literally (same `g` in kernel, `ellT`, ratio, window, `EKFastDecay`;
  `Lambda = dd⁻¹`, constants `C` depend on `Lambda, kappa` only), so no coupling argument is needed in this ticket.
  Reason for rejecting the form at `sz.lam` with the kernel at `lam0` (rows 5-8): row 5 (`STEKNonzero`): stage E's hypothesis fails on a nonempty range of `s`, so the form is not an instance of stage E;
  rows 6-7 need `t0 >= N^{-small}` (available only from `BAdom`, row 2, not from stage E); row 8 moves the burden into the decay hypothesis.
  Keeping the pinned names: `STEKDecaygL`/`STEKLowgL` stay as pinned (`g = sz.lam`, definitionally `STEKDecaygK (sz.lam) ...`), so
  `T2457_EKDecaygL`/`T2457_EKLowgL` bind unchanged and T7's target 7 reads `STEKDecaygL` unchanged; `STEKLow` has no `g`.
- **Consequence handed to U3-BA / T7-BA (not a hypothesis of any target here):** BA instances of the forms need `EKFastDecay (lam0)`, `STEKWin` at `lam0`,
  and for `STEKNonzero` the regime `1-lam0^2/L^2 <= s`; the regime predicate `R` of targets 5 is a parameter, so U3-BA picks it at `lam0`. Decay at `lam0`
  from the `twSteps` conjunct 4 (cutoff `ellT (sz.lam)`, TLF-C5) is rows 2, 7, 8 (needs `W >= ((kappa+1)/kappa)^{1/eps}`).
- **Band-class direction.** Stage E's `BAEKSumNdecay` carries `BAReal ... kappa` (`kappa <= Im m`, `EKPins:97-102`) while band `STEKSumNdecay` has only `‖m‖=1`
  (`Step34Pins:613-615`); so `STEKSumNdecaygL` takes the `kappa`-bulk class and its band instance goes from the band pin (one direction), not `Iff.rfl`.
- **D1/D2.** Mathematically neutral (definitional repackaging of T8's matrix forms and of `STStep2G`'s `(law, Flow, mk, T0)` shape); no exponent depends on
  them. Whether `Iff.rfl` / `rfl` closes the bridges is a compile fact for the probe step; not asserted here.
- **TLF-C5 (target 8) and targets 1, 2, 3, 4, 5, 7, 9** introduce no new exponent: rows 10-11 only (shared with merged `inst_step3R/4R`, `Step34Pins:705-1092`).

### Verdict per target

| target | verdict | reason |
|---|---|---|
| 1 (`STLmaxUgL`, `STLKUgL`) | PASS | no numeric constraint; hypotheses of the examples consistent (rows 10-11) |
| 2 (loop maxima) | PASS | same |
| 3 (D1 loops/ℰ-terms) | PASS | no exponent |
| 4 (ingredient conclusions) | PASS | no new exponent |
| 5 (`STStep3RgL`, `STStep4RgL`, D2) | PASS | `cd <= 1/100`, `(con_st_ind)` hold in the instance with slack 0.125 |
| 6 (`STEK*gL`, D3) | PASS with `gK` coupling (rows 3-9); form at `sz.lam` over a `lam0` kernel would be BLOCKED (rows 5-8) | decision above |
| 7 (`STNewPQgL`) | PASS | no `lam` occurs in the pin text (`Step34Pins:330-362`, 0 hits of `lam`); no exponent |
| 8 (leaf examples) | PASS (math) | pure conjunct unfoldings; `Iff.rfl` is a compile fact for 1b |
| 9 (instances) | PASS | rows 9-11 hold at `n=1`, `d=3` |

## (a″) Probe compile — Mon Oct 12 14:24:46 UTC 2026

Probe step of the 1a (role prover-hard, claude-sonnet-5-5). Section (a) is not edited. File `RBM3D/Probe/T2457Pins.lean` in `../RBM3D-wt/T2457`, commit `ee3d8a0` on `t/T2457`, 296 lines, never merged, no root import. Imports: `Chain/Step2Gen`, `Chain/Step2Kern`, `Induction/Step34PinsP`, `Evolution/Prec`, `Induction/NewPQ`, `Loop/GLoopFlow`, `BA/TwistPins`, `BA/Step2BA`, `BA/FlowPins`, `BA/EKPins`, `BA/EKSum`, `BA/EKNonzero` (the probe may import `BA/*`; `Step34Gen` may not).
Command (run at 14:24:04 UTC from the committed tree; `grep -c 'sorry\|admit\|native_decide'` on the file prints 0): `cd ../RBM3D-wt/T2457 && lake env lean RBM3D/Probe/T2457Pins.lean`. Exit code: 0. Output (verbatim, 28 lines; no `error`, no `warning`):
```
@bandStep34_LCompat : ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), Step34Gen_LCompat (bandStep2Mat sz E) sz.seqHflow
bandFM_STSEforLn : ∀ (d : ℕ),
  STSEforLn d ↔
    STSEforLngL d (fun {d} => STAny) (fun sz => sz.seqP) (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz x => sz.seqHflow) fun x z n => lemT (z n)
@bandFM_STLmaxU : ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ), sz.STLmaxU E s t ↔ STLmaxUgL (bandFM sz E) sz.seqP s t
stek_sumNdecaygL_band : ∀ (d : ℕ), STEKSumNdecay d → STEKSumNdecaygL d (fun sz => sz.seqP) STEKBandKer
stek_sumRes2gL_band : ∀ (d : ℕ), STEKSumRes2 d → STEKSumRes2gL d (fun sz => sz.seqP) STEKBandKer
stNewPQgL_band : ∀ (d : ℕ), STNewPQ d → STNewPQgL d fun sz C => ∃ E, C = bandFM sz E ∧ ∀ (n : ℕ), |E n| < 2
@STEKBandKer : {d : ℕ} → (sz : Sizes d) → FlowFM sz → (ℕ → ℝ) → ℝ → Prop
@probeBAKer : {d : ℕ} → (sz : Sizes d) → FlowFM sz → (ℕ → ℝ) → ℝ → Prop
@probe_feed : ∀ {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {gK : ℕ → ℝ} {κ : ℝ},
  probeBAKer sz C gK κ →
    0 < κ →
      ∀ (n : ℕ),
        ∃ E m,
          BAReal d (sz.L n) (gK n) κ E m ∧
            ∀ (k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
              Step2Gen_UN C n σ s t A = BAUN d (sz.L n) (gK n) E m σ s t A
@BAflow_lam0_window : ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
  BAFlow sz κ ε 𝔠 𝔡 z → ∀ᶠ (n : ℕ) in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹
'RBM.BA.bandStep34_LCompat' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STSEforLn' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stek_sumNdecaygL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stek_sumRes2gL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewPQgL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_feed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STLmaxU' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Probe line numbers below are those of `ee3d8a0`.

### Decisions (compile facts)
- **D1 default works** (functions `Cm : Step2Mat sz`, `Hf : ∀ n, ℝ → sz.SeqΩ → Matrix …`; no `Step34Mat` structure). `STLIg, STLKIg, STksimLKg, STelklkg, STegtg, STeeg` (`:35-40`) are `STxxMg Cm n τ (Hf n τ ω)`. Bridges `bandStep34_STLI/STegt/STksimLK/STelklk/STee` are `rfl` (`:49-53`). In a scratch file (`scratchpad/T2457/scratch1.lean`, not committed, exit 0) `STKI, STLKI, STavgErr, STmaxL, STmaxLK, STXiL, STXiLK` against `STKIg, STLKIg, STavgErrg, STmaxLg, STmaxLKg, STXiLg, STXiLKg` are also `rfl`. Carrier facts `Step34Gen_LCompat Cm Hf`, `Step34Gen_KCompat Cm` (`:42-45`): at the band, `LCompat` is proved by `loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a` (`:54-56`), `KCompat` is `rfl` (`:57`).
- **D2 default works** (`(law, Flow, mk, T0)`, `Concl` on `(sz, z, s, t)`): `STIngRgL` (`:103`, the shape of `T2457_IngRgL`); `STSEforLnConclgL (Cm) (Hf) (μ)` (`:73-94`; `etaT (E n) u` is `Cm.eta n u`); `STSEforLngL` (`:113`) takes `mkM : ∀ sz z, Step2Mat sz`, `Hf : ∀ sz z …` and reads `mk := (mkM sz z).toFlowFM` by construction: no equation hypothesis. Bridges: `bandFM_STSEforLnConcl` is `Iff.rfl` (`:96`); `bandFM_STIngR` is proved (`simp only [bandFM_STKward]; exact Iff.rfl`, `:119-125`); `bandFM_STSEforLn` is `bandFM_STIngR d STAny _` (`:126`). The BA reading elaborates at `baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`, `sz.seqHflowBA (BAflowLam0 sz z)`, `BAFlow`, `BAflowT0`, law `seqP (sz.withLam 0)` (`:285-286`, statement level; proofs owed by U3-BA).
- **D3 (a) works**: `Ker : ∀ sz, FlowFM sz → (ℕ → ℝ) → ℝ → Prop` (`STEKKer`, `:148`); the forms read the kernel only as `Step2Gen_UN C` (`STEKSumNdecaygL :150`, `STEKSumRes2gL :160`; Res1, NAL, Nonzero have the same pattern and are covered at BA by the pointwise examples below, not as defined forms). Band class `STEKBandKer` (`:170`) = `∃ E, C = bandFM sz E ∧ gK = sz.lam ∧ ∀ n, |E n| ≤ 2 ∧ κ ≤ (mE (E n)).im`. Band instances `stek_sumNdecaygL_band` (`:175`) and `stek_sumRes2gL_band` (`:180`) are proved from `STEKSumNdecay d`, `STEKSumRes2 d` through `Step2Kern_UN_band`, `norm_mE`: **one direction only, not `Iff.rfl`** (the generic forms carry `κ` and the class). `STNewPQgL d Cls` (`:192`) with `η = C.eta n τ`; `stNewPQgL_band` (`:205`) from `STNewPQ d` over `Cls = ∃ E, C = bandFM sz E ∧ ∀ n, |E n| < 2`. The class is inhabited at `sz0`: `STEKBandKer sz0 (bandFM sz0 (fun _ => 0)) sz0.lam (1/10)` (`:214`, `mE 0` has `Im = 1`), the `Cls` class likewise (`:215`); the generic `(sum_res_Ndecay)` applies at `d = 3`, `sz0`, `n_ = 2`, `κ = 1/10`, `Admissible` and class and `hg` discharged, tensor `δ₀`, `X ≡ 1` (`:220-226`).
- **Pinned shapes**: `STEKDecaygL`, `STEKLowgL` (`:143-146`, `STEKDecaygL = STEKDecayKgL sz.lam`) equal the bodies of `T2457_EKDecaygL`, `T2457_EKLowgL` by `⟨Iff.rfl, Iff.rfl⟩` (`:186-188`); bridges `bandFM_STEKDecay`, `bandFM_STEKLow` are `Iff.rfl` (`:189-190`). TLF-C5: `STLmaxUgL`, `STLKUgL` (`:277-280`) are the conjuncts 2, 3 of `twSteps` by the projections `⟨h.2.1, h.2.2.1⟩` (`:283`); band bridges `bandFM_STLmaxU`, `bandFM_STLKU` are `Iff.rfl` (`:281-282`). The stop rules "content-binding pin not definitionally equal" and "TLF-C5 projections fail" did not fire for the pins the probe covers (`STEKDecaygL`, `STEKLowgL`, `STLmaxUgL`, `STLKUgL`); `T2457_Step3RgL`, `T2457_Step4RgL` and the full `twSteps ↔ …` with conjunct 4 are 1b targets, not probed.

### D3 (b) settled: the class carries a coupling sequence `gK`; no coupling argument is needed from stage E
- The five forms, `STEKWinKgL` (`:135`) and `STEKDecayKgL` (`:138`) read `gK` in the window `t n ≤ 1 - gK n ^ 2 / L ^ 2`, in `EKFastDecay (gK n)`, in the ratio `(gK n ^ 2 + |1 - v|) / (gK n ^ 2 + |1 - t n|)` and (Res1) in `ellT (sz.L n) (gK n)`; they take the explicit hypothesis `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹`. Band: `gK = sz.lam`, the window from `Admissible` (`step34_band_hg`, `:172`). BA: `gK = lam0`, the window is `BAflow_lam0_window` (`BA/GreenSchur.lean:72`, `#check` above) at `gK = BAflowLam0 sz z`.
- BA class (probe shape; the real one is U3-BA's): `probeBAKer` (`:229`) = `∃ lam0 E, C = baFM sz lam0 E ∧ gK = lam0 ∧ ∀ n, BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)`. `probe_feed` (`:232`) derives from it `Step2Gen_UN C n σ s t A = BAUN d (sz.L n) (gK n) E m σ s t A` (`Step2Kern_UN_BA`; `hIm` from `κ ≤ Im m`, `0 < κ`) and `BAReal d (sz.L n) (gK n) κ E m`. `example : Prop := STEKSumRes2gL 3 (seqP (sz.withLam 0)) (@probeBAKer 3)` elaborates (`:231`).
- Five compiled examples give, for each generic form, its pointwise inequality at `g := gK n` from the stage-E theorem with the hypotheses matched one to one (the statement is the stage-E statement with `BAUN` read as `Step2Gen_UN`): `baEKSumNdecay_holds` (`:238`), `baEKSumDecay1_holds` (`:243`), `baEKSumDecayNAL_holds` (`:251`), `baEKSumDecay2_holds` (`:259`), `baEKSumDecayNonzero_holds` (`:268`). No lemma relating `lam0` to `sz.lam` is used. What remains for U3-BA is the shared absorption step to `Prec` (`prec_core`, private, `Evolution/Prec.lean:130`): it takes `ρ` and the decay hypothesis as inputs, and `prec_ratio_ge_one` (private, `:112`) is stated for arbitrary `g`; U3-BA copies them at `gK`.
- Rejected alternative (forms at `sz.lam` over the kernel at `lam0 < sz.lam`): `example` `:289` compiles `∃ s, 1 - lam²/L² ≤ s ∧ ¬ 1 - lam0²/L² ≤ s`, so the case-(ii) window of the `sz.lam` form is not inside the hypothesis of `BAEKSumDecayNonzero` at `lam0`; (a) rows 5-8 give the same for the ratio and the cutoff.
- **Consequence handed to T7 / U3-BA (not a hypothesis of any target here; not compiled in the probe):** T7's `stEtermDecaygL` reads the pinned `STEKDecaygL` (at `sz.lam`). A BA instance of `STEKDecayKgL lam0` is not an instance of it; it needs the `ellT` conversion of (a) rows 2, 7, 8 (`ellT L lam0 ≥ √t0 · ellT L lam`, `t0 ≥ κ/(κ+1)` from `BAdom`, `W^{ε/2} ≥ 1/√t0`). That uses BA flow data (`BA/MFixedPoint.lean:435-436`), not stage E.

### Verdict of the probe step
All D1-D3 definitions, one bridge each, the band class at `sz0` and the D3 (b) checks compile (exit 0); no stop rule fired; `Step34Pins`, `Step34PinsP`, `Chain/*` are untouched (`git diff main...t/T2457 -- RBM3D/Induction RBM3D/Chain` is empty).
Paper-delta candidate `T2457a` (for (d) of the 1b): the Lean `STEK` consumer forms carry a kernel coupling `gK` (band `sz.lam`, BA `lam0`) and the bulk parameter `κ` also for `(sum_res_Ndecay)` and `(sum_res_1)`, the paper pins read one `g`.

## (a‴) 1a resubmission (H249) — Mon Oct 12 16:24:29 UTC 2026
Answers the round-1 1a-audit (`docs/reports/T2457-1a-audit.md`, RETURN) items 1-6 under CONTROL H249 (2), H250 (3)-(4), H251 (2) and DECISIONS §269 (2). (a), (a″) are not edited. Tree `main` a1412ad, probe `ee3d8a0`; no Lean written in this stage. `S` = scratchpad `T2457/r3/`; scripts are Python (`python3 -I`), each block below is their verbatim output.
**Decisions recorded.**
- **(B)** (H249 (2); audit §7): `STEKDecaygL` stays at `sz.lam` (`= STEKDecayKgL sz.lam`, probe :143; it is the reading of `twSteps` conjunct 4, merged `STDecayLoopUgL`, `Chain/DecayGen.lean:66`, T2454 aa38bde); the five consumer forms read `STEKDecayKgL gK`. Replaces the last bullet of (a″) ("handed to T7 / U3-BA").
- **UBA-C1** (H250 (3); DECISIONS §269 (2), `docs/DECISIONS.md:2458-2470`; it narrows (B): the BAdom conversion is written once, generically, here): comparison hypothesis `Cmp(A): ∀ n, 0 < gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`, `1 ≤ A`; band `gK = sz.lam, A = 1`; BA `gK = lam0, A = (κ+1)/κ` (merged `TwistStep2_lam0_sq`, `BA/TwistStep2.lean:740`, squares form; `gK ≤ lam` follows for `0 ≤ gK`). In `Chain/Step34Gen` (within the stop line, (vii)): (a) window `STEKWin`-at-`lam` ⇒ `STEKWinKgL gK` (needs `gK ≤ lam`); (c) `r(gK;v,t) ≤ A·r(lam;v,t)` for `v ≤ t < 1` (proof: `f(x) = (x+a)/(x+b)` decreases for `a ≥ b`, `lam² ≤ A·gK²`, and `(A²-A)x² + b(A²-1)x + ab(A-1) ≥ 0`), hence `r(gK)^n ≤ A^n r(lam)^n`; (d) `ℓ(gK,u) ≤ ℓ(lam,u)` and `ℓ(gK,u) ≥ ℓ(lam,u)/√A` (`ℓ = min(max(g/√|1-u|,1),L)`); (e) `STEKDecayKgL sz.lam ⇒ STEKDecayKgL gK` from `Cmp(A)`, `W_n → ∞` (`Admissible`) via `√A ≤ W^{ε/2}` eventually (use the pinned decay at `ε/2`). (b) is the **A-form Nonzero**: `STEKNonzerogL d law Ker Aof` (`Aof : ℝ → ℝ`, `1 ≤ Aof κ`) with threshold hypothesis `(1 - s n) * L n ^ 2 ≤ Aof κ * gK n ^ 2` in place of the band `1 - lam²/L² ≤ s`; band instance `Aof = 1`, `gK = lam` (equivalent); the BA instance `A = (κ+1)/κ` is U3-BA (a) (§269 (2)(b), `baTwKerZero_holds`). (f) free, (g), (h) not here. U3-BA owes only `Cmp` from `TwistStep2_lam0_sq` and the BA forms; it no longer owes a BAdom conversion.
- **H251 (2):** target 7 stays the class pin `STNewPQgL d Cls` (probe :192-203, band instance `stNewPQgL_band` :205, abstract `Cls`, `η = C.eta n τ`). It carries no Ward-family text (`STWardTypePgL` is the Ward-type *P* pin, `3_5:1264`, not the Ward identity of the loops). U1s1 (T2463) owns the model-free expansion, `ZeroModeGen_WardFam`/`WardCls` and the link `STNewPQgL d WardCls` (its target 9). If this row reaches its 1a-audit first it fixes only the `STNewPQgL` text, whose coefficient `ξ/(2 i N C.eta)^{m-k}` equals T2463's `(L^{-d} κ)^{m-k}` with `κ = (2 i W^d C.eta)^{-1}`, `N = (W L)^d`.
**Fill-in table (H250 (4)): stage-1a deliverables of the ticket (`docs/tickets/T2457.md:76-83`) and of H249 (2) / H250 (3) / H251 (2).**
| item | status | where |
|---|---|---|
| (i) layout, cone lines, no `BA/*` import | done | (a‴) :172 |
| (ii) D1-D3 decided with probe lines, D3 (b) vs the five stage-E theorems | done in (a″); updated by (B) / UBA-C1 | (a″) :138-149; (a‴) :156 |
| (iii) scope table, 127 + 4 declarations with consumers | done | (a‴) :191 |
| (iv) bridge table, kinds, `STEK*gL` one-direction | done | (a‴) :211 |
| (v) premise scan, registry decision, exact lines | done | (a‴) :243 |
| (vi) forms T7 target 7 (now U2) reads | done | (a‴) :252 |
| (vii) predicted lines per file, `open private` list | done | (a‴) :255 |
| (B), UBA-C1 (cite, A-form Nonzero, (c)-(e) in `Step34Gen`), H251 (2) | recorded | (a‴) :156; numerics :230 |
| exponent table and nondegenerate instance (ticket has no new exponent) | n/a, because (a) :8-65 holds unchanged; UBA-C1 adds only the checks at :230 | (a) :8-65 |
### (i) Layout, reverse cones, `BA/*` grep (audit item 1)
`$ python3 -I $S/layout.py ; python3 -I $S/deps.py`
main a1412ad | modules 516
reverse cone Induction.Step34Pins: 281 modules, LWExpCert*: 6 ['LWExpCert', 'LWExpCertB', 'LWExpCertBS0', 'LWExpCertBS1', 'LWExpCertS0', 'LWExpCertS1']
reverse cone Induction.Step34PinsP: 13 modules, LWExpCert*: 0 
reverse cone Chain.Step34Gen: 0 modules, LWExpCert*: 0 
reverse cone Chain.Step34GenTw: 0 modules, LWExpCert*: 0 
reverse cone Chain.Step34GenB: 0 modules, LWExpCert*: 0 
Step34Gen planned imports ['Chain.Step2Gen', 'Induction.Step34PinsP', 'Evolution.Prec', 'Induction.NewPQ', 'Loop.GLoopFlow'] -> forward closure 143 modules; under RBM3D.BA: 0
leaf imports ['Chain.Step2Kern', 'BA.TwistPins', 'BA.Step2BA', 'Chain.DecayGen'] -> forward closure 390 modules; BA: 25 ; leaf imports lie in the Step34Pins reverse cone: ['BA.Step2BA', 'BA.TwistPins', 'Chain.DecayGen', 'Chain.Step2Kern'] (a cone member is fine: the leaf is imported by nobody)
Chain/ Step2Gen:Step2Kern_UN_band:328 Step2Gen:Step2Kern_ThetaN_band:317 Step2Gen:Step2Gen_UN:202 Step2Gen:Step2Gen_ThetaN:197 Step2Gen:bandFM_STKward:810 Step2Gen:bandStep2_STLIM:1040 Step2Gen:bandStep2_STeeM:1051 Step2Gen:bandStep2Mat:136 Carrier:bandFM:203 Step2Gen:STStep2ConclgL:514 Carrier:STKwardgL:169 Carrier:STKboundgL:147 Carrier:STLKgL:80 Carrier:PrecL:51
Defs/ Semicircle:norm_mE:63 Semicircle:mE_im:42 Semicircle:lemT:193 Params:ellT:32 StochDomAt:HighProbAt:82
Evolution/ Prec:stek_sumNdecay_holds:215 Prec:stek_sumRes1_holds:358 Prec:stek_sumRes2NAL_holds:242 Prec:stek_sumRes2_holds:391 Prec:stek_nonzero_holds:422 Pins:EKFastDecay:51 Pins:EKSumZero:56
Induction/ NewPQ:stNewPQ_holds:584 Defs:STflowE:283 Defs:STFlow:286
Kernel/ Evolution:zeroModeSet:199
Loop/ GLoopFlow:loopM_eq_loopL:127 KLTree:KLloopOf:149
used-name definitions under BA/: none
BA-side names (U3-BA / leaf only; not used by a Step34Gen declaration): TwistStep2_lam0_sq@BA/TwistStep2:740 TwistStep2_T0_ge@BA/TwistStep2:731 BAflowLam0@BA/FlowPins:386 twSteps@BA/TwistPins:133 baStep2Mat@BA/Step2BA:54 BAflow_lam0_window@BA/GreenSchur:72
Layout: `Chain/Step34Gen.lean` (targets 1-7, 9 and (a), (c)-(e)); leaf `Chain/Step34GenTw.lean` (target 8; the `twSteps` example uses `STDecayLoopUgL` since T2454 is merged); `Step34GenB` unused ((vii)). `Step34Pins`, `Step34PinsP`, `Carrier`, `Step2Gen`, `Step2Kern` are not edited. The ticket's 273 modules (4fad610) are 281 at a1412ad. `Step34Gen` needs no `BA/*` import: forward closure has 0 `BA` modules, no identifier of its bridges, instances or lemmas is defined in `BA/`; `bandFM_STLK`, `bandFM_STKbound`, `bandFM_STStep1Loop` (`BA/FlowPins.lean:333-351`) are not needed (probe :119-125 compiles without them).
### (iii) Scope of the two band files (audit item 2)
`$ python3 -I $S/scope.py` (regexp of the audit; `(n)` = other modules of `main` that mention the name; a name with `(0)` has no reader yet)
public declarations (auditor regexp): Step34Pins 127 Step34PinsP 4
unclassified after rules: []
classes: {'MF': 21, 'T2': 6, 'T3': 8, 'T1': 2, 'AG': 5, 'T5': 8, 'SU': 9, 'RA': 3, 'T1e': 2, 'CT': 1, 'T7': 1, 'T4': 7, 'T6': 8, 'ID': 50} total 131
[T1] target 1 generic form — 2: STLmaxU(22) STLKU(21)
[T1e] target 1 endpoint (generic endpoint theorem) — 2: STLmax_of_STLmaxU(1) STLK_of_STLKU(2)
[T2] target 2 generic form (rfl) — 6: STmaxL(10) STmaxLK(10) STXiL(15) STXiLK(17) STsupXiLK(0) STLKtensor(4)
[T3] target 3 generic form (D1) — 8: STLI(7) STKI(7) STLKI(4) STksimLK(5) STelklk(5) STavgErr(3) STegt(5) STee(8)
[T4] target 4 generic form — 7: STSEforLnConcl(5) STXiBoot(5) STNQConcl(0) STIterHyp(4) STWardTypeP(0) STB45(0) STNQConcl'(1)
[T5] target 5 step pin / setting — 8: STStep3R(8) STStep4R(4) STIngR(13) STSEforLn(1) STOeqNQ(2) STIterR(3) STWardTypePPin(1) STB45Pin(1)
[T6] target 6 STEK vocabulary — 8: STEKDecay(6) STEKLow(3) STEKWin(4) STEKSumNdecay(1) STEKSumRes1(1) STEKSumRes2NAL(1) STEKSumRes2(2) STEKNonzero(2)
[T7] target 7 class pin — 1: STNewPQ(1)
[MF] model-free, reused — 21: STPair(12) STPsi(4) STAI(17) STAII(5) STPsum(17) STQop(20) STIdiff(7) STeeLoop(11) STCaseI(13) STCaseII(13) STAny(14) STn12E(6) STn12(11) STlenL(9) STbootRHS(11) STRegIterI(5) STMollifierProps(20) STMollifierEx(1) STQopNorm(2) STAlternating(3) st_Bctl_pos(26)
[AG] already generic (Step2Gen/Carrier) — 5: STAvgU(17) STLocalEntryU(12) STGdecayW(24) STStep2Concl(33) STKward(26)
[CT] no carrier form (STContractM) — 1: STContract(2)
[SU] superseded — 9: STStep3(1) STStep4(1) STStep3I(4) STOeqQt(2) STOeqQtNZ(2) STIterations(1) STIterationsII(1) STOeqNQ'(2) stOeqNQ'_of_stOeqNQ(1)
[RA] regime abbreviation, no new name — 3: STStep3II(3) STStep4I(3) STStep4II(2)
[ID] instance data — 50: szB szB_W_tendsto szB_size szB_size_ge szB_tendsto szB_bandwidth szB_WO szB_admissible zB zB_locDomain flow_zB lemT_zB Bctl_tendsto_const conStInd_const szB_caseI szB_caseII szB_regIterI sz0_caseI InstIngConcl InstStep3Concl InstStep4Concl InstIterConcl inst_ing inst_iter inst_step3R inst_step4R sz0_hs0 sz0_hst sz0_ht sz0_con szB_flow_ht inst_step3 inst_step3I inst_step3II inst_step4 inst_step4I inst_step4II inst_SEforLn inst_OeqNQ inst_OeqQt inst_OeqQtNZ inst_WardTypeP inst_B45 inst_iterations inst_iterationsII inst_contract inst_newPQ inst_mollifier inst_qopNorm inst_OeqNQ'
Planned consumers per class (ticket lines): T1 :28; T2 :29; T3 :34; T4 :38; T5 :40-41; T6 :47; T7 :48. Model-free and already generic classes are read by the modules counted. `STContract`: `STContractM` (`Contract:1011`) is model-free. Superseded and regime-abbreviation rows get no generic name.
### (iv) Bridge table (audit item 3). P = compiled in the probe (`$ python3 -I $S/kinds.py`), E = expected from the unfolding, a compile fact owed to 1b
probe ee3d8a0 bridge kinds (name:line=kind): bandStep34_STLI:49=rfl bandStep34_STegt:50=rfl bandStep34_STksimLK:51=rfl bandStep34_STelklk:52=rfl bandStep34_STee:53=rfl bandStep34_LCompat:54=proved bandStep34_KCompat:57=rfl bandFM_STSEforLnConcl:96=Iff.rfl bandFM_STIngR:119=proved bandFM_STSEforLn:126=proved stek_sumNdecaygL_band:175=proved stek_sumRes2gL_band:180=proved bandFM_STEKDecay:189=Iff.rfl bandFM_STEKLow:190=Iff.rfl stNewPQgL_band:205=proved bandFM_STLmaxU:281=Iff.rfl bandFM_STLKU:282=Iff.rfl
| generic name(s) | band bridge | kind |
|---|---|---|
| `STLmaxUgL`, `STLKUgL` | `bandFM_STLmaxU`, `bandFM_STLKU` | `Iff.rfl` (P :281-282) |
| `STLmaxgL_of_STLmaxUgL`, `STLKgL_of_STLKUgL` | band :284, :291 | proved (E; precomposition at `u = t`); the two premises are the registry lines (v) |
| `STmaxLg STmaxLKg STXiLg STXiLKg` / `STsupXiLKg STLKtensorg` | `bandStep34_*` | `rfl` (P: scratch rfl exit 0 in (a″); E for the last two) |
| `STLIg STLKIg STksimLKg STelklkg STegtg STeeg` / `STKIg STavgErrg` | `bandStep34_STLI, STegt, STksimLK, STelklk, STee` / E | `rfl` (P :49-53) / E |
| `Step34Gen_LCompat Cm Hf`, `Step34Gen_KCompat Cm` | `bandStep34_LCompat`, `bandStep34_KCompat` | proved by `loopM_eq_loopL` (P :54-56) / `rfl` (P :57) |
| `STSEforLnConclgL` | `bandFM_STSEforLnConcl` | `Iff.rfl` (P :96) |
| `STXiBootgL STNQConclgL STNQConclgL' STIterHypgL STWardTypePgL` | `bandFM_*` | `Iff.rfl` (E; `etaT (E n) u` is `Cm.eta n u`, as at :96) |
| `STB45gL` | `bandFM_STB45` | proved via `Step2Kern_ThetaN_band` (`Step2Gen:317`) (E) |
| `STStep3RgL STStep4RgL STIngRgL STIterRgL` | `bandFM_STStep3R, STStep4R, STIngR, STIterR` | proved: `simp only [bandFM_STKward]; exact Iff.rfl` (P for `STIngR` :119-125; E for the rest) |
| `STSEforLngL STOeqNQgL STWardTypePPingL STB45PingL` | `bandFM_STSEforLn` (P :126), `bandFM_STOeqNQ`, `…WardTypePPin`, `…B45Pin` | proved from `bandFM_STIngR` (P / E) |
| `STEKDecayKgL` / `STEKDecaygL`, `STEKLowgL` / `STEKWinKgL` | `bandFM_STEKDecay`, `bandFM_STEKLow` / `STEKWinKgL sz sz.lam ↔ STEKWin sz` | `Iff.rfl` (P :189-190; audit §2) |
| `STEKSumNdecaygL`, `STEKSumRes2gL` | `stek_sumNdecaygL_band`, `stek_sumRes2gL_band` | **one direction**, proved (P :175, :180; `Step2Kern_UN_band`, `norm_mE`, `stek_*_holds`) |
| `STEKSumRes1gL`, `STEKSumRes2NALgL`, `STEKNonzerogL` (A-form, `Aof = 1`) | `stek_sumRes1gL_band`, `…Res2NALgL_band`, `…nonzerogL_band` | **one direction**, proved (E): same pattern as Ndecay / Res2 (their window and decay hypotheses at `gK = sz.lam` are `Iff.rfl` to `STEKWin`, `STEKDecay`); Nonzero needs `1 - lam²/L² ≤ s ⇔ (1 - s) L² ≤ 1·lam²` |
| `STNewPQgL d Cls` | `stNewPQgL_band` | one direction, proved (P :205) |
The five band instances are premise-free in 1b (from `stek_*_holds`, `stNewPQ_holds`, Prec:215-422, NewPQ:584). BA instances (class, forms at `BAUN`, `Cmp`): U3-BA.
### UBA-C1 checks at the sequence `sz0`, `κ = 1/10`, `ε = 1/2` (`A = 11`)
`$ python3 -I $S/uba.py` (grid of 4,920 `(v,t)` pairs at `n = 1` for six `t0` in [1/11, 1-1e-9]; the limit rows are `(e)`)
A=(kappa+1)/kappa = 11.0 sqrt(A) = 3.3166247903554
(c) r(gK)/r(lam)<=A, (d) ell(gK)<=ell(lam), ell(gK)>=ell(lam)/sqrt(A): violations {'c': 0, 'd1': 0, 'd2': 0, 'cnt': 4920} | max ratio/A = 0.9999443678774191 | min ell ratio*sqrt(A) = 1.0
(a) window at lam => at gK (t0=1/11): True True
A-form Nonzero at worst t0=1/11 : band boundary s_b=1-lam^2/L^2 satisfies (1-s)L^2<=A gK^2: True | stage-E form (A=1) at gK: False | extra window (A-1)gK^2/L^2 = 8.466568860140715e-10
A-form Nonzero at n=1 instance t0 : band boundary s_b=1-lam^2/L^2 satisfies (1-s)L^2<=A gK^2: True | stage-E form (A=1) at gK: False | extra window (A-1)gK^2/L^2 = 9.313225738611072e-09
(e) eps=0.5: first n with W^(eps/2)>=sqrt(A): n0=1 (W=1024) ; holds for n0..n0+20000: True ; n0-1 holds: False
(e) eps=0.25: first n with W^(eps/2)>=sqrt(A): n0=3 (W=32768) ; holds for n0..n0+20000: True ; n0-1 holds: False
(e) eps=0.1: first n with W^(eps/2)>=sqrt(A): n0=60 (W=27027081632) ; holds for n0..n0+20000: True ; n0-1 holds: False
(e) eps=0.05: first n with W^(eps/2)>=sqrt(A): n0=7320 (W=672979774968305299232) ; holds for n0..n0+20000: True ; n0-1 holds: False
(e) pointwise n=1, u in {0,1/2,1-lam^2/L^2}: W^eps ell(gK) >= W^(eps/2) ell(lam): True
`W_n = (2(n+1))^5` is increasing, so `√A ≤ W^{ε/2}` holds for all `n ≥ n0(ε)` (`n0 = 1, 3, 60, 7320` for `ε = 1/2, 1/4, 1/10, 1/20`); (e) needs it only eventually.
### (v) Premise scan and registry (audit item 4)
Scan rule: `Test/Axioms.lean:429-450` flags a `Prop`-valued `RBM` definition that is a binder constant of some theorem and the conclusion head of none; classes `borrowedProps` / `owedProps` (:91, :102) / `structuralProps` (:209, contains `EKFastDecay` :229).
- Bridges `bandFM_*`, `bandStep34_*`: all binders are data; no flag. Band instances `stek_*gL_band`, `stNewPQgL_band`: premise-free, concluded outright; no line.
- Lemmas (a), (c), (d), (e): binders are plain inequalities, `Tendsto W`, and `STEKDecayKgL sz.lam …` (head concluded by (e) itself). Rule for 1b: no lemma takes `STEKWin`, `STEKWinKgL` or `STEKDecaygL` as a binder (they would become unregistered premises); state them unfolded or via `STEKDecayKgL`.
- `Step34Gen_LCompat`, `Step34Gen_KCompat`: concluded by `bandStep34_*`, so the scan is silent at BA, where the instances are owed by U3-BA (the scan is by head constant; noted for U3-BA (a)/(b)).
- **Endpoints `STLmaxgL_of_STLmaxUgL`, `STLKgL_of_STLKUgL` bind `STLmaxUgL`, `STLKUgL`; no theorem concludes them: two `owedProps` lines, confirmed.** Insert after the `RBM.BA.STGdecayWgL` line (`Axioms.lean:201`):
`   `RBM.BA.STLmaxUgL, -- `(Eq:LGxb)` uniform in `u ∈ [s,t]` over a flow carrier (conjunct 2 of `twSteps`, `BA/TwistPins.lean:135`): hypothesis of `STLmaxgL_of_STLmaxUgL`; owed like its band form `STLmaxU`; owner Steps 3-4 (U3s4; U3-BA), consumed by V2a through `twSteps` (TLF-C5) (T2457)`
`   `RBM.BA.STLKUgL, -- `(Eq:L-KGt-flow)` uniform in `u ∈ [s,t]` over a flow carrier (conjunct 3 of `twSteps`, `BA/TwistPins.lean:137`): hypothesis of `STLKgL_of_STLKUgL`; owed like its band form `STLKU`; owner Steps 3-4 (U3s4; U3-BA), consumed by V2a through `twSteps` (TLF-C5) (T2457)`
Name-clash grep of the 54 final names (`$ bash $S/clash.sh`, `git grep -w -E` over `RBM3D/*.lean` and `docs/tickets/checks/*.lean` on main a1412ad and 457 `t/*` branches other than `t/T2457`): `refs scanned 458, refs with hits 4`. Hits: mentions in `checks/T2457-check`, `T2458-check`, `T2463-check` (main, `t/T2458`, `t/T2459`; 0 `def`/`theorem`/`abbrev`/`lemma` lines among them); `t/T2205:RBM3D/Probe/T2205Pins.lean:2124,2131,2197,2202` defines `STLmaxUgL`, `STLKUgL`, `STLKgL_of_STLKUgL`, `STLmaxgL_of_STLmaxUgL` in a never-merged probe (not a library module, no clash; a precedent for the endpoint proofs). Hits in library code on main, `t/T2454`, `t/T2455`, `t/T2456`: none.
### (vi) Forms T7 target 7 reads (now U2: `stEtermDecaygL`, T2454 merged T7a without it; for T2454 / U2; audit item 5)
- Statement shape: the four conjuncts of band `stEtermDecay` (`DecayLoopB.lean:2209-2227`) with `sz.STegt n (E n) ↦ STegtg Cm Hf n` etc. and `STEKDecay sz ↦ STEKDecaygL μ` (signatures, probe `ee3d8a0`): `STEKDecaygL (μ) {m} (s t) (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) := STEKDecayKgL sz.lam μ s t 𝒜` (:143, unchanged by (B)); `STegtg Cm Hf n τ ω I`, `STksimLKg Cm Hf n τ ω l I`, `STelklkg Cm Hf n τ ω I`, `STeeg Cm Hf n τ ω σ a a'` (:37-40; `Cm : Step2Mat sz`, `Hf : ∀ n, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ`); `STSEforLnConclgL Cm Hf μ s t` (:73); `STEKLowgL μ s t X` (:145).
- Inputs of U2's theorem, all merged or in this row: `STDecayLoopUgL C μ s t` (`Chain/DecayGen:66`), `STKcalDecaygL C` (`DecayGen:83`), `STKboundgL` (`Carrier:147`), and the carrier facts `Step34Gen_LCompat Cm Hf`, `Step34Gen_KCompat Cm`, `Cm.toFlowFM = C` (:42, :44) that tie `C.L`, `C.K` (read by `STDecayLoopUgL`) to `Cm.LIM ∘ Hf` (read by the ℰ-terms). No local `STEK` copy anywhere.
### (vii) Predicted lines per file; `open private` (audit item 6)
`$ python3 -I $S/est.py` (probe-measured block plus band spans, labelled)
   58  header, imports, docstrings (basis: Chain/DecayGen.lean:1-58)
  185  probe-measured block ee3d8a0:31-215 (D1, STSEforLnConclgL, D2, D3 with 2 of 5 forms, class, 2 band instances, STNewPQgL, hg, EK examples)
   12  T2 rest: STsupXiLKg, STLKtensorg + 2 rfl bridges (band spans 5)
    8  T3 rest: STKIg, STavgErrg + 2 bridges
   79  T4 rest: 6 forms + bridges (band spans 61, x1.3)
   90  T5: STStep3RgL, STStep4RgL, STIterRgL (spans 30, x1.5) + 3 proved bridges (24) + 3 instances with bridges (21)
   77  T6 rest: Res1, NAL, Nonzero(A-form) (spans 31, x1.5) + 3 one-direction band instances (27) + A parameter (4)
   25  T1: 2 Iff.rfl bridges + 2 proved endpoints (probe :277-283 is 7 lines)
  115  UBA-C1 (a),(c),(d),(e): window, ratio, ellT up/down, decay conversion with HighProbAt.mono (10+30+30+45)
  107  T9 instances: inst_step3R/4R (Step34Pins:917-940 = 24 lines each side) 30, E-term bridges 12, EK at sz0 + 5 band_3 55, A-form 10
  756  Step34Gen central; upper bound x1.5 = 1134 ; stop line 2000 ; B-rule threshold 1800 ; ticket estimate 1150
   65  Step34GenTw leaf (basis: Chain/DecayGenTw.lean = 80 lines with 3 examples; here 2 TLF-C5 examples + BA statement-level examples of targets 1, 3, 5)
Central 756 and upper 1,134 for `Step34Gen` against stop line 2,000 and the 1,800 rule: `Step34GenB` is not needed; the ticket's 1,150 is within the upper bound. `open private` list: empty. `grep -c "^private"`: `Step34Pins` 0, `Step34PinsP` 2 (`stP_bootRHS_nonneg`, `stNQConcl'_of_stNQConcl`, both band-internal), `Prec` 22, `NewPQ` 37, `GLoopFlow` 16, `Step2Gen` 4; none is used (public `stek_*_holds`, `stNewPQ_holds`, `loopM_eq_loopL`, `Step2Kern_*_band` suffice; `prec_core`, `prec_ratio_ge_one` are not needed because (e) is pointwise plus `HighProbAt.mono`).
### Corrections to (a), (a″) and verdict
- (a″) last bullet of "D3 (b) settled" ("needs the `ellT` conversion … uses BA flow data … handed to T7 / U3-BA") is replaced by (B) and UBA-C1 above: the conversion is (e) in `Step34Gen` and needs only `Cmp(A)`. (a) row 8 is now the hypothesis `∀ᶠ n, √A ≤ W^{ε/2}` of lemma (e), which follows from `W_n → ∞`. (a″) `STEKNonzerogL` is the A-form. Cone count 273 → 281 (main moved).
- Paper-delta candidate `T2457a` (a″) stands, plus: the A-form Nonzero and the comparison hypothesis are Lean-side generalisations (paper pins read one `g`). No new BLOCKED.
**Verdict (this resubmission): targets 1-9 PASS** (no stop rule fires; no exponent beyond (a); (c)-(e) hold on the grid at `A = 11`, max ratio/`A` = 0.99994).
## (a⁗) H252 (2) comparison text — Mon Oct 12 18:18:18 UTC 2026
Stage 1b, role prover-hard (claude-sonnet-5-5), tree: branch `t/T2457` merged with `main` 01b4c521, no Lean written yet. Replaces the comparison hypothesis of (a‴) `:158` (and `:163-171`, `:246`, `:271-272` where it is used). (a), (a″), (a‴) are not edited. Source: CONTROL H252 (2) (`docs/queue/CONTROL.md:207`), DECISIONS §271 (4) (`docs/DECISIONS.md:2494`).
- **Literal text.** `Cmp(A) := ∀ n, 0 ≤ gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`, with `1 ≤ A`. It is written inline in each lemma (no `def`), so no Prop-valued definition becomes a premise for the registry scan ((v), `Test/Axioms.lean:429-450`). The (a‴) conjunct `∀ n, 0 < gK n` is not used anywhere.
- **Sign consequences.** `sz.lam n = 0 → gK n = 0` (`0 ≤ gK n ≤ lam n`); `sz.lam n > 0 → gK n > 0` (`lam² ≤ A gK²`, `gK ≥ 0`). Both cases give `gK n ^ 2 ≤ sz.lam n ^ 2`, so the windows coincide at `lam n = 0` and nest at `lam n > 0`.
- **Hypotheses per lemma** (all `∀ n` unless stated): (a) `step34Gen_winK_of_cmp`: Cmp, window at `sz.lam` ⇒ window at `gK` (uses `0 ≤ gK ≤ lam` only). (c) `step34Gen_ratio_le`, `_pow_le`: at one `n`: Cmp at `n`, `v ≤ t < 1`, `1 ≤ A`; no positivity of `gK`. (d) `step34Gen_ellT_le`, `_ge`: at one `n` and every `u` (no `u < 1`): `0 ≤ gK ≤ lam` resp. Cmp. (e) `step34Gen_decayK_of_cmp`: Cmp `∀ n`, `1 ≤ A`, `Tendsto W atTop atTop` (from `Admissible`); `√A ≤ W^{ε/2}` holds eventually.
- **Check** (`python3 -I r4/cmp.py`, 200000 samples with `0 ≤ gK ≤ lam`, `lam² ≤ A gK²`, `1 ≤ A ≤ 21`, `b = |1-t| ≥ 1e-9`, `a = |1-v| ≥ b`, 65204 of them with `lam = 0`): the identity `A(Y+a)(X+b) − (X+a)(Y+b) = (A−1)XY + b(AY−X) + a(AX−Y) + (A−1)ab` (`X = gK²`, `Y = lam²`; all four terms are ≥ 0, so (c) does not need `a ≥ b`) and (c), (d) hold; output: `{'c': 0, 'ident': 0, 'd1': 0, 'd2': 0, 'cnt': 200000, 'lam0': 65204}` (violation counts; at `lam = 0` the script asserts `gK = 0`, `ℓ(gK) = ℓ(lam) = 1`).
- **Discharges (named sign premise).** Band, `gK = sz.lam`, `A = 1`: Cmp reads `∀ n, 0 ≤ sz.lam n`. `Sizes.lam : ℕ → ℝ` has no sign field (`Defs/Sizes.lean:144`) and `WO` is eventual (`:164`), so `Admissible` does not give it; it holds at `sz0` (`hl0`, `Step34Pins.lean:846`). BA, `gK = BAflowLam0 sz z = √(BAflowT0)·sz.lam`: the squares are `TwistStep2_lam0_sq` (`BA/TwistStep2.lean:740`, `A = (κ+1)/κ`); `0 ≤ gK ≤ lam` needs `0 ≤ sz.lam n` too (`BAflowT0 ∈ (0,1)`: `TwistStep2_T0_ge` :731, `EMn2BA_T0_lt_one`); the eventual window is `BAflow_lam0_window` (`BA/GreenSchur.lean:72`). Both discharges therefore name one premise `∀ n, 0 ≤ sz.lam n`; the lemmas here take Cmp itself and need nothing else. Handed to U3-BA / U3s2-U3s4 / T2462 as an observation ((d)); it does not change a verdict of this ticket (the five band instances use the class `STEKBandKer`, not Cmp).
## (a⁵) R1 comparison text (H254 (4)) — Mon Oct 12 18:22:52 UTC 2026
Stage 1b rerun, role prover-hard (claude-sonnet-5-5). R1 supersedes (a⁗) and the comparison text of (a‴) `:158`: `∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (CONTROL H254 (2),(4), DECISIONS §273 (1),(3)); inline in each lemma, no `def`. Window (a) reads `gK n ^ 2 ≤ sz.lam n ^ 2` at every n; `ellT` (d) splits on the sign of `sz.lam n`; a private lemma gives `0 < gK n → 0 < sz.lam n ∧ gK n ≤ sz.lam n` and `sz.lam n ≤ 0 → gK n ≤ 0`. Earlier sections are not edited.
## (b) Script output: verbatim in `docs/reports/T2457-prove-b.txt` (790 lines, generated Mon Oct 12 18:44:57 UTC 2026 at tree 676eef54; scripts in scratchpad `T2457/r5/`)
Commit `676eef54` on `t/T2457`: `Chain/Step34Gen.lean` 1255 lines (stop 2000; `Step34GenB` unused), leaf `Chain/Step34GenTw.lean` 99, `Test/Axioms.lean` +2 registry lines (`STLmaxUgL`, `STLKUgL`, after the `STGdecayWgL` line). `RBM3D.lean` is left to the hub (rule A step 4). `git diff --stat main...t/T2457`: these 3 files + `Probe/T2457Pins.lean` (never merged); G1 diff (`Induction`, `Carrier`, `Step2Gen`, `Step2Kern`): 0 lines.
Build: `lake build RBM3D.Chain.Step34Gen RBM3D.Chain.Step34GenTw RBM3D.Test.Axioms` -> `Build completed successfully (4003 jobs)`, 0 error lines (full `lake build`: hub at merge). `#print axioms` of the 99 new public declarations: 99 x `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`; grep `sorry|admit|native_decide|^axiom|open private`: no match.
Targets (statements by script in the evidence file, `Step34Gen` :123-578, leaf :579-): 1 `Step34Gen` :58-89 (`STLmaxUgL`, `STLKUgL`, endpoints, bridges); 2 :93-136; 3 :138-199 (D1 `Cm`, `Hf`; `Step34Gen_LCompat/KCompat`); 4 :201-341; 5 :343-491 (D2 `(law, Flow, mk, T0)`; `STSEforLngL` takes `mkM : Step2Mat`-valued); 6 :493-657 (D3 class `Ker sz C gK κ`; `gK` in window, decay, ratio, `ellT`) and the R1 lemmas :659-817; 7 :819-843 (`STNewPQgL d Cls`); 9 :845-1255; 8 leaf :37-99.
Built as decided: D1 functions, D2 family, D3 (a) abstract class (`STEKBandKer` at the band), D3 (b) coupling `gK`, (B) `STEKDecaygL = STEKDecayKgL sz.lam`. R1 literal in 6 lemmas (`grep -cF` = 6; the H252 text: 0 hits): (a) `winK_of_cmp` reads only `gK n ^ 2 ≤ sz.lam n ^ 2` at every n, no case split; (c) `ratio_le`, `ratio_pow_le` need `t < 1` only; (d) `ellT_le`, `ellT_ge` call private pointwise lemmas that split on the sign of `sz.lam` (private `step34Gen_cmp_idx`: `0 < g → 0 < l ∧ g ≤ l`, `l ≤ 0 → g ≤ 0`); (e) `decayK_of_cmp` from `Tendsto W` (`step34Gen_W_tendsto` of `Admissible`). `STEKNonzerogL` is the A-form (`Aof`, premise `1 ≤ Aof κ`).
Instances: 61 `example`s in `Step34Gen` (:864-1247: endpoints, Step 3/4, SEforLn, OeqNQ, B45, WardTypeP, iterations through the bridges at `sz0, z0, s = 0, t = 1/16` (`szB` for case (ii)); loop and ℰ-term bridges at n = 0; `STEKDecaygL`, `STEKLowgL` at `seqP sz0` (δ0, X = 1); the five `stek_*gL_band 3` at d = 3, n_ = 2, κ = 1/10 with δ0 / sum-zero `Az` / case (ii) at `szB`; `STNewPQgL`; R1 at `gK = lam/2, A = 4` and at `lam < 0`) and 10 in the leaf (target 8: `twSteps ↔ (… ∧ STLmaxUgL ∧ STLKUgL ∧ STDecayLoopUgL) := Iff.rfl`, `h.2.1`, `h.2.2.1`, abstract and at band data; 5 BA statement-level `Prop`s). Owed pins (`STLmaxUgL`, `STStep3RgL`, …) stay hypotheses of the examples.
Name clash (`clash.sh`, 99 names, 464 refs = main + other t/*): 0 same-name declarations. Layering `grep '^import RBM3D.BA' Step34Gen.lean`: no match. Spectral grep (ticket literal): 99 hits = 28 band bridges + 8 band instances/class + 1 private band-instance lemma + 48 examples at band data + 12 docstrings + 2 substring hits (`Lloop` inside `KLloopOf`, the model-free index constructor, in `Step34Gen_LCompat/KCompat`, the text of ticket target 3); 0 elsewhere.
Checks: `docs/tickets/checks/T2457-check.lean` exit 0, 0 errors; scratch binding file (check + `Iff.rfl` of `STLmaxUgL`, `STLKUgL`, `STStep3RgL`, `STStep4RgL`, `STEKDecaygL`, `STEKLowgL`, `STIngRgL` against `T2457_*`) exit 0, 0 errors; registry pre-check (`import RBM3D` + both modules + `#assert_rbm_axioms`) exit 0: `premises found by scanning: 120`, `RBM.BA.STLmaxUgL: 2`, `RBM.BA.STLKUgL: 2`.
## (c) Mathlib names (compiled, hence verified)
`div_le_div_of_nonneg_right`, `div_le_div_iff₀`, `pow_le_pow_left₀`, `pow_le_pow_iff_left₀`, `le_div_iff₀`, `Real.one_le_sqrt`, `Real.sq_sqrt`, `Real.sqrt_nonneg`, `Real.rpow_add`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `eventually_ge_atTop`, `div_nonpos_of_nonpos_of_nonneg`, `le_mul_of_one_le_left`, `mul_neg_of_pos_of_neg`, `mul_neg_of_neg_of_pos`, `max_eq_right`, `min_le_min_right`, `max_le_max_right`, `inv_anti₀`, `pi_norm_le_iff_of_nonneg`, `Finset.sum_filter`, `half_pos`. Names verified absent: none searched.
## (d) Open issues and paper-delta candidates
T2457a (from (a″)): the Lean `STEK` consumer forms carry a kernel coupling `gK` (band `sz.lam`, BA `lam0`) and the bulk `κ` also for `(sum_res_Ndecay)`, `(sum_res_1)`; the paper pins read one `g`. T2457b: the A-form Nonzero (threshold `(1-s)L² ≤ Aof κ · gK²`, premise `1 ≤ Aof κ`) and the comparison R1 are Lean-side generalisations (UBA-C1); band instance `Aof = 1`, `gK = sz.lam`. T2457c: `STSEforLngL`, `STOeqNQgL`, `STWardTypePPingL`, `STB45PingL` take the regime `R` as a parameter (the band pins fix `STAny` / `STCaseI`). Owed to U3-BA: the BA class `Ker`, the BA forms at `BAUN`, R1 for `gK = BAflowLam0`, `A = (κ+1)/κ` (DECISIONS §273 (1), `TwistStep2_lam0_sq`), `Step34Gen_LCompat/KCompat` at `baStep2Mat` (statement level in the leaf). Owed to U3s4 / U3-BA: `STLmaxUgL`, `STLKUgL` (registry), `STStep3RgL`, `STStep4RgL`, the `STIngRgL` instances. Observation: (a)-(a⁵) already fill 282 lines, so the verbatim (b) output is in the companion file `docs/reports/T2457-prove-b.txt` (the hub should commit it with the report); the ticket's 200-line limit was exceeded before this stage.
