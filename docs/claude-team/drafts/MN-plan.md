# M/N row plan after V closes (draft for `REQ-<…>-MNopen`; dispatcher V4 drafting helper, <date -u>)

Sources: design `docs/reports/T2449-design.md` §1–§7 (`:1-17`, `:55-112`, `:125-158`); probe `t/T2449` 921369b `RBM3D/Probe/T2449Pins.lean` (397 lines; "probe N" = its line); supervisor `2026-10-12-2049.md` §2 `:155-175`, GMN-C2/C3/C4, O6 `:243`; `2026-10-14-1743.md` O3 `:62`; `2026-10-12-1152.md:170` (Q5 (6)); DECISIONS §260 (3), §266, §278, §281, §282, §316, §318 (4) (7), §320 (2), §325–§334 (calibration); portmaps `T2173-portmap.md:275-279`, `T2325-portmap.md:96-108`. `Test/Axioms.lean` line numbers at `main` 97779231 (before T2511/T2512's registry edits; M/N lines are not in their writable sets).

## 0. State
- **M/N 3 / 15 used**, flag 15 (2049 §2 `:169`):
  - C5g = T2475 35b7d6cb (`Universality/GUEPhase/RandomLayerBG` 526, `BA/RandomLayerBGBA` 219);
  - N3b = T2477 2dcfcda5 (in place: `GreenCorr`, `UnivMain`, `Step1Band`);
  - N3a = T2476 0f3ecb6b (`Jak`, `Uyw` in place; `BA/EMCTE2BA` 986).
- **Remaining (T2449 §5):** M1, M2, M3, N2, C3, C4, C5 = 7 rows.
  - N1 is folded into M1 (TrLocal, TrLocalInit, ≈ 360) and N2 (Norm, ≈ 70) (§266 (1)).
  - The BA `thetaDiff` belongs to M3; C3 may take it over (GMN-C4).
  - **New since T2449: MN-D3**, a design gate for the `d = 3` form of the UN-side assembly (§3). Jun B (§316) came after T2449.
- **Start rule.** Jun §260 (3): the M/N proof tickets wait for V to close. At T2511 row b's merge every row may start.
  - C3, C4 and C5 read no V output (`T2173 pm:275-277`; T2449 §5).
  - M1 and M2 read `UNMLOutBA 3`.
- **Calibration** (DECISIONS §325–§334):
  - BA leaves ×0.96–1.28 (T2501 a1/a2 ×0.96/0.98, T2500 ×1.28; T2511 uses the same range). Generic new files ×1.06–1.37 (V1s3′ ×1.06 booked, U3s4 ×1.37).
  - T2449's prices are portmap twin prices (T2325 0.70 / 1.00 / 1.30; landed ×1.155 on MA-01..05), not bottom-up. So the calibrated range is indicative, and each 1a re-prices bottom-up.
  - Split rule: a 1a central over 1,950 splits at a file boundary, pre-signed.

## 1. Row table (all new BA leaves unless said; nothing below edits a merged file except the registry lines named)
| row | files | content / targets | inputs (all merged once T2511 b merges) | registry lines it closes (owner today) | T2449 lo / c / hi | ×0.96–1.28 | role, gate | after |
|---|---|---|---|---|---|---|---|---|
| **MN-D3** (new) | report `docs/reports/T25xx-design.md`; probe `RBM3D/Probe/T25xxPins.lean` ≤ 300 | the `d = 3` form of the UN-side assembly (§3): options A/B, A's successor texts compiled at `UNKind.ba` with a `d = 3` instance, price of the implementation, its home (N2 or own row) | V terminal (`unMLOutBA_three`); `PinsK:398-442`, `OUInterfaceK:101`, `RandomLayerBG:399`, `UNPins:123-370` | none (decides the form of `:178`, `:179`, `:185`) | report (T2503 precedent: 1 row) | — | `prover-max`, design only | V closed |
| **M1** | a: `BA/MAPins` (all MN1 pin texts: probe 157-262 verbatim, one text, X1-C4) + `BA/MALocal`; b: `BA/MATrLocalBA` (N1) | fixed-`z` locSC from `UNMLOutBA d` conj. 1, 5 (`BAMAFixed` half, probe 249), net (`BAMANetLoc`, 251), `baEnd_locSCL : ∀ d, UNMLOutBA d → BAEnd_locSCL d` and `_three`; bridge `UNLocAvgBA_of_BAEnd_locSCL` (probe 220; `d = 3` form per MN-D3); `UNTrLocalBARow` (≈ 60; uniformisation lemma compiled in T2449 B8), `UNTrLocalInitBARow'` (≈ 300, dilation) | `unMLOutBA_three` (T2511 b); `ba_dom_of_bulk` (`RandomLayerBGBA:69`); `BAzztE_data`; `BAm_sub_le_of_im` (`MReg:84`), `BAbulk_window` (`:122`); `ouInit_ba` (`UNPins:472`), `admissible_lamHat` (`:503`); twins `locSCFixed_of_ML` (`FixedZ:100`), `netLoc` (`ZNet:999`), `unTrLocalBandRow` (`BUnivHolds:205`) | `:178` `UNLocAvgBA` (BA-M1); `:182` `UNTrLocalBARow`, `:183` `UNTrLocalInitBARow'` (BA-N1 → M1) | 735 / 1,360 / 2,550 | 1,306–1,741 | `prover-hard`; 1a only | V; batch 1 (row a) |
| **M2** | `BA/MAQDiff` | fixed-`z` QDiff from `UNMLOutBA d` conj. 1 (k = 2), 3, 4 (`BAQDiffFixed`); `(Kn2sol)` at BA; net with the Lipschitz constant of `BAprof` (new, T2449 §3.3 (ii)); `baEnd_QDiffL`, `_three` | M1 a (pins, net); `baKsolveLe3_holds` (`KSolve:478`); `BAm_sub_le_of_im`; twins `QDiffFixed_of_ML` (`FixedZ:419`), `netQD` (`ZNet:1024`) | none (`BAEnd_QDiffL` is a new pin it concludes) | 490 / 1,000 / 1,950 | 960–1,280 | `prover-hard`; the 1a names the `BAprof` Lipschitz route and adds a probe step if no merged lemma gives it | M1 a |
| **M3** | `BA/MADecolQUE` | `baEnd_decolL` (twin `decol_of_locSC`, `FixedZ:789`); `baEnd_QUEL` (twin `QUE_of_QDiff`, `QUEFromQDiff:502`) with the BA `thetaDiff` (twin `thetaDiff`, `QUECore:105`); `_three`; `UNQueBA` by merged `UNQueBA_of_BAEnd_QUEL` (`UNPins:357`; `d = 3` form per MN-D3) | M1, M2; `baProp5to8_holds` (`Prop6Path:1049`) | `:185` `BAEnd_QUEL` (BA-M3) | 630 / 1,300 / 2,470 + `thetaDiff` (unpriced, new math, GMN-F4) | 1,248–1,664 | `prover-hard`; **narrow design gate D1 + probe for `thetaDiff`** (§238 precedent), unless C3's D1 takes it | M1, M2 |
| **C3** | `BA/GUEKPrim`, `BA/GUEEntry` | profile `UNOUProfile.ba`; `UNOUProfRowk (ba)` in the lossless row-difference form (O9); `RBG_ProfComp` at BA (left by C5g, `RandomLayerBGBA:134`); entry bounds (twins KPrim, ZeroModeProfile, EntryDet, EntryTail) | P8 (`baProp5to8_holds`), K1, C1; `BAm_im_lower_window` (`MReg:227`) | `:171` `UNOUProfRowk` (BA-C3) | 552 / 1,102 / 2,048 | 1,058–1,411 | `prover-max`; **narrow D1 + probe** (O9: lossless `BAProp8`, DECISIONS `:580`; `thetaDiff` at `ζ = 0` if it falls out, GMN-C4) | V (rule only); batch 1 |
| **C4** | `BA/GUEOneLoop` | Lemma 5.15 with `1 − M^{(+,+)}S`, 2-loop algebra, `eq729_Kdisc` at BA | K4 (`BA/KCactus`), C3 | none (feeds C5) | 434 / 868 / 1,612 | 833–1,111 | `prover-max`; 1a only | C3 |
| **C5** | `BA/GUEHyp` | BA producers of `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` (T2449 §1.3; twins Eq729B, HypA, Proc, PathBounds); GMN-C3: a needed change is a C5 primed successor | T4, T5 (stage T), C4, C5g | BA part of `:169` `UNOULLk`, `:170` `UNG1Rowk` (C5g + BA-C5 + BA-N2) | 609 / 1,217 / 2,261 | 1,168–1,558 | `prover-max`; 1a checks the four `RBG_*` texts at exact type | C4 |
| **N2** | `BA/UNBUniv` | `UNNormBARow` (N1, ≈ 70; twin `unNormBandRow` `NormBand:173`, `unMeanBound_ba` `UNPins:285`); `UNOURowBA` by `ouRowk_of_pins` (`OUInterfaceK:292`) ← `UNG1Rowk (ba)` (C5g + C5), `g2bRowk` (`QUEFlow:898`), `UNOUProfRowk (ba)` (C3); `UNL32 → BAEnd_BUnivL 3` in MN-D3's form; `BAThm27L` (probe 217) and `UNL32 → BAThm27L 3` (or MA-06b, Q-b) | M1, M3, C3, C5, N3a/N3b, MN-D3 | `:179` `UNOURowBA`; `:184` `UNNormBARow`; instance halves of `:169-170`; `:180-181` (N3a-produced, hypotheses of `baBUniv_of_rows`) | 200 / 230 / 440 + MN-D3 implementation | 221–294 + impl. | `prover`; 1a only | all above |

Totals of the 7 rows: central **7,077**; calibrated **6,794–9,059**; T2449 landed (×1.155) 8,174; plus `thetaDiff` and MN-D3's implementation, both unpriced. Likely 1a splits (hi above 1,950): M1 (expected, 2049 `:169`), then M3, C3, C5.

## 2. Shape check (1743 O3 = the M/N half of 1152 Q5 (6)): T2449's pins against V's merged terminal types
| T2449 pin (probe 921369b) | reads | V on `main` (+ T2511 b) | lines up? |
|---|---|---|---|
| `BAMAFixed d := UNMLOutBA d → BAlocSCFixed d ∧ BAQDiffFixed d` (probe 249); `BAMANetLoc/QD`, `BAMADecol`, `BAMAQUE` (251-262) | `UNMLOutBA d`, one `d` | `UNMLOutBA` = `UNPins:110-115` (5 conjuncts; law `seqP (sz.withLam 0)`; carrier `baFMz`; `t ≤ BAflowT0`); `unMLOutBA_three : UNMLOutBA 3` (`T2511-check:209-210`) | **yes** at `d = 3`; at `d > 3` only under `STStep5IIIgL d` |
| T2449 §3.1 (`:103-105`): M1 reads conj. 1, 5 and M2 conj. 1, 3, 4 of `BAMLOutTL` (`TwistPins:178`) | `BAMLOutTL d` | `BAMLOutTL` unchanged at `TwistPins:178-181`; `baMLOutTL_three` (T2511 b); `baMLOutTL_of_famStep` `MainIndOutBA:315` | **yes** |
| `unMLOutBA_of_BAMLOutTL` (probe 259) | — | merged at `MainIndOutBA:320`, same statement | **yes** (identical) |
| `unMLOutBA_of_V` (probe 264): `BAMainIndTL d STAny` + `baChainTL_holds` | the single-flow step | off the route (V-F1, `TwistPins:168`); the route is `unMLOutBA_of_famStep` (`MainIndOutBA:326`) from `BAMainIndFamTL d STAny` (`:60`); `baMainIndFamTL_three` (T2511 b) | no M/N pin reads either step; **no effect** |
| `BAEnd_locSCL`, `BAEnd_QDiffL`, `BAEnd_decolL`, `BAThm27L` (probe 192-217); merged `BAEnd_QUEL` (`UNPins:333`), `BAEnd_BUnivL` (`:343`) | per `d`, `3 ≤ d →` | — | **yes** (the pins are per `d`; `d = 3` is an instance) |
| `UNLocAvgBA_of_BAEnd_locSCL (h : ∀ d, BAEnd_locSCL d)` (probe 220); merged `UNQueBA_of_BAEnd_QUEL (h : ∀ d, …)` (`UNPins:357`); `UNOURowBA := UNOURowk … (∀ d, UNMLOutBA d) …` (`:123-124`); `baBUniv_of_rows (hML : ∀ d, UNMLOutBA d) hLoc hQ` (`:367-370`); `UNLocAvgk`, `UNQuek`, `UNOUClaimsk` all `∀ d, 3 ≤ d` (`PinsK:398, 406, 421`) | `∀ d` | V gives `∀ d, STStep5IIIgL d … → BAMainIndFamTL d STAny` only (`baMainIndFamTL_any`, `T2511-check:213-215`) | **no**: `BAEnd_BUnivL 3` stays conditional on regime (iii) at every `d > 3`, against §316 ("BA terminal at `d = 3` unconditional") |

Result: the M rows line up with V at `d = 3`. The N assembly (Thm 2.7, third bullet) does not under Jun B. The four other bullets need no `∀ d` input. They need only the bridges (`UNLocAvgBA`, `UNQueBA`), which feed N.

## 3. MN-D3: the `d = 3` form of the UN-side assembly (§318 (4) (7); T2504 audit O3 in §320 (2))
- **(A) Dimension-filtered primed successors (recommended).** The K-row layer gets a filter `D : ℕ → Prop`: `UNOUClaimsk`, `UNOURowk`, `UNG1Rowk`, `UNJakUywRowk`, `UNEMCTE2Rowk`, `UNClaimRowk`, `UNLocAvgk`, `UNQuek`.
  - The band is recovered at `D = fun _ => True`; BA uses `D = (· = 3)`.
  - Rewrapped: `g1Rowk_of_inputsG`, `ouRowk_of_pins`, `unJak/unUyw_of_ouClaimsk`, `un_claimAll_of_rowsBA`, `baBUniv_of_rows`, the two bridges.
  - Why it should be mechanical (to be probed): the merged producers take per-`d` inputs `∀ d, 3 ≤ d → …` (`RandomLayerBG:406-411`) and `ML Loc Que` as opaque Props (`:399-400`; `OUInterfaceK:292` `{ML Loc Que : Prop}`). The only cross-`d` coupling is those Props at the BA kind.
  - GMN-C2 (b) applies: band statements unchanged, new names.
- **(B) Keep `∀ d`.** The third bullet at `d = 3` would carry `∀ d, STStep5IIIgL d …` as a hypothesis. This changes §316's "unconditional at `d = 3`" for bullet 3, so **Jun decides**.
- **(C) Generalise U5 to every `d`.** Rejected by Jun B (§316 (1)).
- **Price.**
  - Gate: 1 row (report + probe ≤ 300).
  - (A)'s implementation: unpriced, rough guess 300–600 generic + ≈ 100 BA; generic new file ×1.06–1.37.
  - It goes into N2 if N2's 1a central stays ≤ 1,950 (N2 itself is 221–294); otherwise it is its own generic row (+1).

## 4. Order: 2–4 running throughout
- **Batch 1** (as T2511 b merges): **M1 row a**, **C3** (D1 → 1a-audit → 1b) and **MN-D3**.
  - The 4th slot takes M1 row b (stacked, `BA/MATrLocalBA`), or M3's D1 `thetaDiff` probe. The probe would take M1/M2's pins as hypotheses of exact type (V2a design-gate precedent).
- **Batch 2:** M2 (after M1 row a), C4 (after C3), M1 row b.
- **Batch 3:** M3 (after M1, M2), C5 (after C4).
- **Last:** N2 (after M1, M3, C3, C5, MN-D3). Then MA-06b (MA 8 → 9), which reads `BAThm27L 3`.
- **Critical path:** two serial chains of three tickets, C3 → C4 → C5 (`prover-max`) and M1 → M2 → M3, then N2. MN-D3 runs beside them and only N2 waits for it.

## 5. Counts
- **Tickets.**
  - 7 rows + MN-D3 = 8, so M/N **11 / 15** with no split.
  - Likely splits: + M1 (2049 `:169`), + 0–2 (M3, C3, C5). MN-D3's implementation adds 0–1.
  - **Forecast ≈ 12 (11–14)**; the tail is 15–16 if C3 and C5 both split.
- **Proposed lines (as V, 0342 Q1):** keep flag 15. A release that puts the forecast at 15 or more → short REQ before that release. M/N at 15 used and not closed → HOLD recommended.
- **BA:** 195 at V's close → ≈ 204 (203–206) at M/N's close.
- **Proposed closing conditions:**
  - (i) public at `d = 3` with standard axioms: `BAEnd_decolL 3`, `BAEnd_locSCL 3`, `BAEnd_QDiffL 3`, `BAEnd_QUEL 3`, `UNL32 → BAEnd_BUnivL 3`, and `BAThm27L 3` under `UNL32` (N2 or MA-06b);
  - (ii) the registry lines of §1 removed, or rewritten to name the M/N producer;
  - (iii) the general-`d` forms stated under `STStep5IIIgL` (D723);
  - (iv) `#print axioms band_terminal` and `bUniv_holds` unchanged across MN-D3's successors (GMN-C2 (c));
  - (v) paper deltas: D689 (T2449a–c) already recorded; new ones from the 1a's.

## 6. Open questions (for the REQ)
- **Q-a.** MN-D3: approve the gate with (A) recommended? (B) would need Jun.
- **Q-b.** Who assembles `BAThm27L 3`: N2 (proposed; `band_terminal` is MA-06a's, so MA-06b can still do it) or MA-06b?
- **Q-c.** `thetaDiff`: M3's own D1, or C3's D1 at `ζ = 0` (GMN-C4)? Proposed: C3's D1 tries it first, and M3 keeps the fallback.
- **Q-d.** M1 row a publishes every MN1 pin text (`BA/MAPins`, the V3 precedent of publishing `BAMainIndFamTL`), so M2 and M3 read them by name. Agree?
- **Q-e.** Flag 15 and the lines of §5?
