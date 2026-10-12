Auditor model: claude-opus-5-5

# T2455 1a-audit round 2 (design gate): Mon Oct 12 15:18:44 UTC 2026

Inputs: ticket `docs/tickets/T2455.md`, check `docs/tickets/checks/T2455-check.lean`, sections (a), (a″), (a‴) of `docs/reports/T2455-prove.md`, branch `t/T2455` at `46fc313`, detached audit worktree `../RBM3D-wt/T2455-1a-audit` (moved from `b981c85` to `46fc313`). Scratch: `<scratchpad>/T2455/audit2/`. `Pins:N` = line N of `RBM3D/Probe/T2455Pins.lean`. Scope: R1-R3 of round 1 (§8 there), and fixing the three X1-C4 pins.

## 1. Probe compile, hygiene, diff
```
$ git diff --stat main...t/T2455
 RBM3D/Probe/T2455Meas.lean | 392 +++   RBM3D/Probe/T2455Pins.lean | 397 +++   2 files changed, 789 insertions(+)
$ git diff --stat 04118b1 main -- RBM3D RBM3D.lean lakefile.toml lean-toolchain lake-manifest.json   (main = 1debc23)
 RBM3D.lean | 1 +    RBM3D/Chain/Step5Gen.lean | 666 +++   (T2458 = U6, merged after the base; not imported by the probes)
$ lake env lean RBM3D/Probe/T2455Pins.lean   (15:14:10)  exit=0  output lines 0
$ lake env lean RBM3D/Probe/T2455Meas.lean               exit=0  output lines 0
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2455*.lean   -> grep exit=1
$ wc -l: 397 T2455Pins.lean, 392 T2455Meas.lean (cap 400 each)
$ for n in <36 def/theorem names of T2455Pins>; git grep -nE "(def|theorem|lemma|structure|abbrev) $n( |$)" main -- RBM3D ':!RBM3D/Probe'   -> 0 hits
$ grep -nE "STCltIso|STCltFar|STExpInv|HClt|CltRep|STGijDec|STKfarg|STThg|STfFar|CltGen" RBM3D/Chain/Step5Gen.lean   -> no hit (U6 does not state the pins)
```

## 2. R1 (round-1 D1): loop premise of `STGijDecgL`
```
$ git diff b981c85 46fc313 -- RBM3D/Probe/T2455Pins.lean     (3 hunks: docstring :204, premise :211-213, BA reading :386)
-      PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
-        (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (t n) ![false, true] ![p.1, p.2] ω‖)
-        (fun n p _ => Φ n p.1 p.2 ^ 2) →
+      PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n) × Zd d (sz.L n))
+        (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (t n) p.1.1 ![p.2.1, p.2.2] ω‖)
+        (fun n p _ => Φ n p.2.1 p.2.2 ^ 2) →
```
Scratch files of the repair, copied to `audit2/`, recompiled in the audit worktree (15:14:50):
```
$ head -397 {derive,conv,weaker}.lean | diff - RBM3D/Probe/T2455Pins.lean   -> identical prefix (all three); no sorry/admit/axiom
$ lake env lean derive.lean   exit=0; 2 deprecation warnings (if_neg :502, if_pos :506);
'RBM.BA.T2455_gijDec_of_gex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2455_stGijDecgL_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.T2455_stGijDecgL_band3' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean weaker.lean   exit=0   ('RBM.BA.hCltOf_szCL' depends on axioms: [propext, Classical.choice, Quot.sound])
$ diff <(sed -n 241,266p T2455-check.lean) <(sed -n 401,426p weaker.lean) && echo verbatim   -> verbatim
```
Statements (derive.lean): `T2455_gijDec_of_gex (C) (μ) (t) (hsize : Tendsto sz.size atTop atTop) (h : ∀ ε₀ > 0, STGijGEXgL C μ t ε₀) : STGijDecgL C μ t`; `T2455_stGijDecgL_band (hG : STGbEXPij d) … (hf : STFlow sz κ ε 𝔠 𝔡 z) (ht0) (htT : ∀ n, t n ≤ lemT (z n)) : STGijDecgL (bandFM sz (STflowE z)) (Sizes.seqP sz) t`; `_band3` discharges `hG` by `stGbEXPij_of_v3 (gbEXPV3 hd)`; an `example` proves the Pins:387 statement. weaker.lean: the check's one-charge `T2455_GijDecgL C μ t → STGijDecgL C μ t` (by `StochDomAt.precomp_param`). The BA reading Pins:383-386 compiles inside the probe. R1 is met: the band implication is compiled, BA follows from `baGbEXPij'_holds`, and the input is weaker than the check's proposal. The paper premise is one charge (`7_8:1924`: `{\cal L}^{(2)}_{t, (-,+), (a,b)}\prec [\Phi_t(a,b)]^2`), so paper-delta candidate **T2455a** (prove report last paragraph) covers the difference.

## 3. Numerics rerun
```
$ python3 inst.py > inst.out; diff <(sed -n 36,74p T2455-prove.md) inst.out && echo IDENTICAL   -> IDENTICAL; grep -c FAIL -> 0
$ git show 04118b1:…/MeanFar.lean | sed -n 874,1026p > b1; …/CltMoments2.lean | sed -n 791,929p > b2
$ sed -n 104,230p T2455Meas.lean > g1; sed -n 233,368p T2455Meas.lean > g2;  wc -l: b1 153 g1 127 b2 139 g2 136
$ git diff --no-index --numstat b1 g1  -> 59 85        b2 g2 -> 47 50
python: 144/153=0.941  97/139=0.698  24/153=0.157  241/292=0.825  24/292=0.082
```
All reported values reproduce. No segment has `f_sem > 0.30`; no X1a segment is measured (rule: X1b blocks).

## 4. R2 (X1-C2 table, (a‴))
- Every cited producer exists at the cited line (script `chk file line name`, 31 checks, all 1): `BAMB_ward_row` Ward:108, `BAMfine_eq` GreenSchur:93, `BAPropM` MFixedPoint:567, `emn2Exp2_bandHK` EMn2Exp2:945, `baEMn2ExpHK` EMn2BA:637, `Step2Kern_Mss_BA` Step2Kern:73, `baP8_BATheta_shift` Prop6Path:497, `BATheta_isSymm` KBase:371, `Theta_transpose_of_three_le` Props4:95, `prop5Decay_holds` Prop5Hold:784, `prop6Diff1_holds` / `prop7Diff2_holds` Prop6Hold:353/384, `BAProp5/6/7` FlowPins:173/194/205, `baProp5to8_holds` Prop6Path:1049, `BAKsolve` KSolve:58, `Step2Kern_BAKsolve_form` Step2Kern:104, `TwistStep2_lam0_sq`/`_T0_ge` TwistStep2:740/731, `BAflow_lam0_window`/`BAflow_real` GreenSchur:72/59, `baFMz`/`BAflowLam0` FlowPins:393/386.
- Premise comparison: `STThPropsg` conj. 4-5 use `zdistD r ≤ 1/2 * zdistD a` (Pins:244, 246); `BAProp6/7 Λ κ c` take `c`, read at `c = 1/2`. `grep -c "max τ 1" BA/PropUnit.lean` → 11; `sed -n 173,215p BA/FlowPins.lean | grep -c max` → 0: the factor does not reach the pins. Constants: `BAProp5` has `∃ C … ∃ c` after `(Λ κ)`, `BAProp6/7` `∃ C` after `(Λ κ c)` (FlowPins:173-205).
- Coupling: `TwistStep2_lam0_sq` states `BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2` (TwistStep2:740-741). The conversion is compiled:
```
$ lake env lean conv.lean   exit=0
'RBM.BA.T2455_baFM_STThg' / 'RBM.BA.T2455_Bparam_conv' / 'RBM.BA.T2455_P5_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
T2455_P5_conv … (h1 : g₀ ≤ g) (h2 : g ^ 2 ≤ (κ + 1) / κ * g₀ ^ 2) (hx : x ≤ C * Bparam d L g₀ t K * Real.exp (-c * K / ellT L g₀ t)) :
    x ≤ (κ + 1) / κ * C * Bparam d L g t K * Real.exp (-c * K / ellT L g t)
T2455_inv_conv … : (g₀ ^ 2 + x)⁻¹ ≤ (κ + 1) / κ * (g ^ 2 + x)⁻¹
```
  So `STThPropsg` read at `sz.lam = g` is reachable from the BA producers at `g₀` with constants in `(d, 𝔡⁻¹, κ)`. C1: no `g₀ ≤ W^{-ε}`, no smallness of `‖M − m₀I‖` in any pin. MN0: `T2449-design.md` (on main) §1.4: "`Ed κ'` is `BAReal d L (√t₀ g) κ' E m₀`", margin `κ' = (πκ)^5/2048 ≤ Im m`; covered by `κ ≤ Im (C.m n)`, `κ ≤ 1` of `HCltOf`. R2 is met.

## 5. R3 (X1-C3 table, KDecay, privates, line prediction)
```
$ sh x1c3_compact.sh > x1c3.txt; diff x1c3.txt <(sed -n 253,261p T2455-prove.md) && echo X1C3-IDENTICAL   -> X1C3-IDENTICAL
$ independent: 16 non-private KDecay names, grep -lw in the seven files  -> no file
$ sh privs_compact.sh
CltSwap 4 (S 0, B 0, R 4);CltResolvent 46 (S 9, B 0, R 37);CltPath 33 (S 4, B 13, R 16);FarEntry 22 (S 2, B 4, R 16);CltGood 9 (S 0, B 2, R 7);CltStep 26 (S 2, B 0, R 24);ExpInv 35 (S 0, B 2, R 33)
total 175 {'S': 17, 'B': 21, 'R': 137}
$ comm of the 38 S/B privates against the (a‴) plan (31 names + cltpath_chk_* 7)   -> no difference either way
$ grep -cE "^private (noncomputable )?(theorem|lemma|def|abbrev)" : 4 46 33 22 9 26 35 (=175); wc -l: 365 1118 551 940 680 1594 544
$ python3 closure.py RBM3D.Induction.EMn2Exp2 RBM3D.Evolution.FarEntry RBM3D.Induction.EMn2Exp1
EMn2Exp2 closure 97 BA/*: 2 ['RBM3D.BA.FlowPins', 'RBM3D.BA.MFixedPoint'];  FarEntry closure 120 BA/*: 0;  EMn2Exp1 closure 89 BA/*: 0
```
Predicted lines (a‴): highest CltStep 1,794 (high), FarEntry 1,500, CltGen 230 (cap 300): none past 2,000. No private is deleted in the plan. R3 is met.

## 6. Statement diff against the check (definitional, recompiled after R1)
`rfl2.lean` = current probe + the check's imports and Part 2 + examples; `lake env lean` exit=0 (15:15:47):
```
example (d L W : ℕ) : RBM.Evol.CltEtaLowerOf d L W ↔ T2455_CltEtaLowerOf d L W := Iff.rfl
example … : STfFarg C n s t σ a ω = T2455_STfFarg C n s t σ a ω := rfl
example … : STCltFarConclgL C μ s t ↔ T2455_STCltFarConclgL C μ s t := Iff.rfl
example … : STcltBg … = T2455_STcltBg … := rfl          example … : STcltXg … = T2455_STcltXg … := rfl
example … : STCltIsoConclgL C μ s ↔ T2455_STCltIsoConclgL C μ s := Iff.rfl
example … : STExpInvgL C μ ↔ T2455_STExpInvgL C μ := Iff.rfl
example … : CltRepg C μ H₀ g' E ↔ T2455_CltRepg C μ g' E H₀ := Iff.rfl
example … (h : T2455_GijDecgL C μ t) : STGijDecgL C μ t := …   (proposal, not binding; the repaired form is weaker)
'RBM.BA.cltRepg_band' / 'RBM.BA.hCltOf_szCL' / 'RBM.BA.bandFM_STCltFarConcl' / 'RBM.Evol.cltEta_lowerOf' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All five content-binding conclusions (`T2455_STfFarg`, `_STCltFarConclgL`, `_STCltIsoConclgL`, `_STExpInvgL`, `_CltEtaLowerOf`) hold by `rfl`/`Iff.rfl`.

## 7. X1-C1 spectral grep
```
$ python strip-comments + grep -nE "mE|zt E|zt \(|2 - κ|\|E\||cltCk|etaT|norm_mE|PropSpin|Theta d|mSigma|STmsig " T2455Pins.lean
code-line hits (all): [112, 113, 116, 118, 123, 125, 127, 128, 131, 306, 335, 336, 337, 360]   (cltCk_facts, band corollaries, bandFM_M_le, hCltOf_szCL, bandFM_STThg)
in generic ranges 30-108,141-285: []
$ diff <(sed -n 11,153p cltgen_R1.lean) <(sed -n 141,283p T2455Pins.lean) -> exit 0; imports Chain.Step2Gen, Induction.Step5Pins; grep -cE "BA\.|baFM" -> 0;
  lake env lean cltgen_R1.lean exit=0, output 0 lines; spectral grep on its non-comment lines -> no hit
```

## 8. Binding stop lines
| stop line | finding |
|---|---|
| file > 2,000 lines | not hit; prediction max 1,794 (CltStep, high) |
| band public declaration changed / private deleted | none (no source file edited; plan deletes no private) |
| X1-C1 item, `‖m‖ = 1`, `Theta d L g ξ`, `PropSpin`, C1, premise beyond (a)-(i) | none (§4, §7). `STThPropsg`, `STKpropsg`, `STExpInvgL`, `STReg5I` in `STCltFargL` only: (i), ruled in round 1 (F4) |
| second propagator / kernel | none: `STThg` = `Step2Gen_Theta (Step2Kern_Mss … * C.S n)` (Pins:142) |
| `BA/*` import in the eight files | none in the CltGen candidate; FarEntry's band (c) must avoid `EMn2Exp2` (closure, §5) |
| edit of Carrier/Step2Gen/Step2Kern/Step5Pins/Step34Pins/X1b | none (diff = two probes) |
| `f_sem > 0.30` on an X1a segment | none |
| T2449 MN0 conflicts with `κ ≤ Im (C.m n)` | no (§4) |

Hidden hypotheses / cycles: `HCltOf` is an explicit premise of both pins; `FlowFM` carries data only; every producer named is merged. Nonvacuity: `hCltOf_szCL` (Pins:328) discharges every deterministic premise at `szCL, zCL, s = 0, t = 1 − L⁻², κ = 1/2, δ = 1/10` with only (a)-(c) as hypotheses; `(b)` now has a compiled band producer (`T2455_stGijDecgL_band3`), `(c)` has `emn2Exp2_bandHK` (Pins:390).

## 9. X1-C4: the three pins, fixed by this audit
- **`STExpInvgL C μ`** = Pins:189-192 (`Iff.rfl` with `T2455_STExpInvgL`). Target 7: `CltRepg C μ H₀ g' E → CltInvg H₀ → STExpInvgL C μ` (Pins:284).
- **`STCltIsogL d`** = Pins:272-275: `∀ κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t, HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → STCltIsoConclgL C μ s`, with `HCltOf` = Pins:265-269 (`3 ≤ d`, (f) incl. `κ ≤ 1`, (g) `CltRepg`, (d) Ward row, (e) `STMfarg C s`, (a) `STLocalEntryUgL`, `STGdecayWgL … Cd`, (b) `STGijDecgL C μ s` in the two-charge form of `46fc313`, (c) `STKfargL C s`).
- **`STCltFargL d`** = Pins:278-282: `HCltOf … → STReg5I sz s t → STThPropsg C → STKpropsg C s → STExpInvgL C μ → STCltFarConclgL C μ s t`.
- These are to be copied verbatim into `Chain/CltGen` (with `HCltOf`, `STGijDecgL`, `STKfargL`, `STMfarg`, `STThPropsg`, `STKpropsg`, `CltRepg`, `CltInvg`, Pins:141-283).

## 10. Verdict: **PASS**
Every stage-1a deliverable ((i)-(viii), X1-C5 `g`/`f_sem`/`g₀`) is present and reproduces. R1-R3 of round 1 are met. No binding stop line is hit. Paper-delta coverage: T2455a (two-charge loop premise). needs dispatcher sign-off: no.

Observations (no RETURN):
- Registry (for 1b): `STLocalEntryUgL`, `STGdecayWgL` are not in `Test/Axioms.lean` (`grep` no hit). The prove report does not list the registry plan. The new premise pins `STMfarg`, `STThPropsg`, `STKpropsg` are not proved for every carrier either; 1b should decide their `owedProps` lines together with `STGijDecgL`, `STKfargL`.
- The 1b endpoint instances should discharge `hGij` (`T2455_stGijDecgL_band3`) and `hK` (the `kellStarEv`/`emn2Exp_kellStar_far` route, not `EMn2Exp2`, whose closure has `BA/*`). Only `hLoc`, `hDec` (Step 2 pins) may stay.
- Size: the predicted Δ sums to 1,095 central / 1,660 high, against the ticket's estimate of 650 / 1,100 (an estimate, not a stop line). The X1b extrapolation (≈ 1.2k changed lines) is not a measurement.
- The prove report is 297 lines (CLAUDE §6 limit 300; the ticket's final-report target is ≤ 200 lines). The 1b must keep it within limits.
- `T2455_baFM_STThg` needs `Im(E + m) ≠ 0`; U4-BA supplies it from `BAReal`.
