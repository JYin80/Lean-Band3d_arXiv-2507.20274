Prover model: claude-sonnet-5-5

## (a) Math preflight — Fri Oct 16 13:19:11 UTC 2026

Sources read: `docs/tickets/T2520.md`, `docs/tickets/T2519-amend-3.md` (item 6: T2519 1a-audit counts as PASS), `docs/reports/T2513-design.md` §1-§6, `RBM3D/Universality/NormBand.lean`, `RBM3D/BA/UNPins.lean`, `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Main/QUEFromQDiff.lean:463`. Probe line counts from `git show a6d9966e:RBM3D/Probe/T2513Pins.lean`.

### (i) Exponent table

Target 5 (`unNormBARow_holds`, the one new proof): `H = λ_n Ψ + V`, `V = seqXmat (sz.withLam 0)`, `N = (W L)^3`. Entry event `E = {every real coordinate |ω_c| ≤ N}`; on `E` every entry of `V` is `≤ 2N` (`NormBand_Xentry_le`, `NormBand.lean:91`), `‖(λ_nΨ)_xy‖ ≤ λ_n ≤ 𝔡⁻¹` (`|Ψ_xy| ≤ 1`: entries are 0/1, row sum `2d`, `UNPins_psiI_rowsum` `UNPins:240`, private; `λ_n ≤ 𝔡⁻¹` is `WO 𝔡`, `Defs/Sizes:164-165`).

| quantity | value | constraint | slack |
|---|---|---|---|
| `CV₀` (target 5) | 3 (same as band `unNormBandRow`, `NormBand:173`) | `\|λ_i\| ≤ N·(2N + 𝔡⁻¹) ≤ N^{CV₀}` (`NormBand_eig_le`, `NormBand:66`: `\|λ_i\| ≤ #ι · B`, `#ι = N`, `B = 2N + 𝔡⁻¹`) | holds iff `N² ≥ 2N + 𝔡⁻¹`; suffices `N ≥ 2 + 𝔡⁻¹` (then `N² ≥ N(2+𝔡⁻¹) ≥ 2N+𝔡⁻¹`), eventually by `SizeTendsto`. At `𝔡 = 1/10`: needs `N ≥ 1+√11 = 4.317`; first S0 size `N = 2^21` |
| coordinate count | `2N²` (`(i,j,Bool)`, `Sizes.card_Idx`, as `NormBand:176-179`) | union bound | n/a |
| per-coordinate tail | `P(\|ω_c\| ≥ N) ≤ 2e^{-N²/2}` (sub-Gaussian, variance proxy 1: `NormBand_gvar_le` `:138` and `NormBand_subgaussian` `:155` at `sz.withLam 0`; both take no admissibility hypothesis, only `sz : Sizes d`) | variance `≤ 1` | n/a |
| total tail | `4N² e^{-N²/2}` | `≤ N^{-D}` eventually for each `D > 0` (`NormBand_tail_eventually` `:122`, uses `SizeTendsto` only) | lemma condition `N^{D+2}e^{-N/2} ≤ 1/4`; at `n=0` holds for `D ≤ 72034.8`; true tail holds for `D ≤ 1.5e11` (script below) |
| `Admissible` used | `SizeTendsto` (tail) and `WO 𝔡` upper half `λ_n ≤ 𝔡⁻¹` (entries of `λΨ`) | `sz.withLam 0` itself is not admissible (`WO` fails at `lam = 0`), so the twin applies the band lemmas to `sz.withLam 0` and `WO` to `sz` | n/a |
| `CV₀+1` of `unMeanBound_ba` (`UNPins:285`, used `UNPins:379`) | 4 | `2d·𝔡⁻¹ ≤ N^{CV₀+1}` | `60 ≤ N^4`; needs `N ≥ 2.8`; at `n=0` `N^4 = 2^84` |
| `(ε₀, c)` of `g2bRowk` (`QUEFlow:898`) | `(𝔡/3, 𝔡/6) = (1/30, 1/60)` | `0 < ε₀ < 𝔡/2` (`queChain`, `QUEFromQDiff:463`) | `1/30 < 1/20`: slack `1/60`; merged |
| `queChain` exponent | `−min(2ε₀, 2𝔡/5) + 2c + τ = τ − 𝔡/15` | negative iff `τ < 1/150`; the instance reads `τ_Q = 1/300` (`UNPins` docstring of `inst_UNOUQUEk`) | `1/300`; merged, arithmetic only, not a hypothesis of an N2 target |
| `τ_U ≤ ouTauMax 𝔠 𝔡` (`ZeroModeProfile:78`) | `min(min(𝔠/12, 𝔠𝔡/12), 1/100) = 1/720` at `(1/6, 1/10)` | `0 < τ_U ≤ 1/720` | instance takes `τ_U = 1/720` (`le_rfl`, `BA/RandomLayerBGBA:199-212`), slack 0, merged |
| `κ → κ/2 → κ/4`, `δ₀` of `UNDensBARow'` (`UNPins:159`) | merged `unDensBARow'_holds` (`MReg:333`) | n/a | n/a, merged |
| `UNL32` | borrowed `Universality/Pins:281` | the one external hypothesis of D6 | n/a |

Reprice (T2513-design D4 rule: code lines + 3 doc lines per declaration + 30 header + instance allowance; code-line counts of the probe ranges measured by `grep -vcE '^\s*(--.*)?$'`: `:38-116` = 68, `:120-188` = 65 (56 without `jakUywRowkD` `:142-150` = 9), `NormBand.lean:173-223` = 52 (+ 16 for the entry bound of `λΨ`, `seqHBA_isHermitian` and the Hermitian bridge, + 8 `open private`). BA leaf items (code): readings and two `Iff` 17; `jakUywRowkD`, `un_claimAll_of_rowsBAD`, `baBUniv_of_rowsD` 34; three `_holds` (probe `:302-312`) 20; F3 two rows 16; norm-bound twin 68; end (`_of_ML` 10, `baThm27L_of_ML` 6, D6 pair 8, `baThm27L_any` 8) 32; C5 names 10; instances 55 + 20 twins + 8 = 83. The retired probe copies (`T2513_BAEnd_locSCL`, two cores, `locAvg_core`, `que_core`, `n2_three`) are not counted (F1).

```
$ python3 -I price.py
G1 PinsKD          code= 68 decls=18 central= 168  landed x1.34-1.67 = 225-281
G2 RandomLayerBGD  code= 56 decls= 4 central= 118  landed x1.34-1.67 = 158-197
BA UNBUniv         code=197 decls=22 central= 376  landed x1.34-1.67 = 504-628
total central 662 landed 887 - 1106
G1 PinsKD hi landed 281 <= stop 450 True ; <=2000: True
G2 RandomLayerBGD hi landed 197 <= stop 400 True ; <=2000: True
BA UNBUniv hi landed 628 <= stop 1100 True ; <=2000: True
1,950 line / total hi landed = 1.7638439133816959 ; ticket hi-case 1250 vs 1950: 1.56
```

| file | reprice central | landed forecast (×1.34-1.67) | stop line | 2,000 per-file stop |
|---|---|---|---|---|
| `Universality/PinsKD` | 168 (ticket 166) | 225-281 | 450: slack 169 | slack 1,719 |
| `GUEPhase/RandomLayerBGD` | 118 (ticket 118) | 158-197 | 400: slack 203 | slack 1,803 |
| `BA/UNBUniv` | 376 (ticket 185+230+45 = 460) | 504-628 | 1,100: slack 472 | slack 1,372 |
| total | 662 (ticket 744; ticket's conservative reading 650-700) | 887-1,106 | 1,950 line: slack 844 | n/a |

The fallback (`BAThm27L 3` to MA-06b) is not needed: the total landed forecast 1,106 is under 1,950 with it kept in N2. The BA-leaf reprice drops below the ticket's 460 because the T2449 N2 line also priced pieces that M1/M3 have since merged (F1) and the 5-line `BAThm27L` conjunction is now at its merged text (F2).

Two deltas against the ticket's text, neither a pin or stop-line move: (1) the `open private` list (coverage row 13, Layout `NormBand`) is missing `NormBand_Xentry_le` (`NormBand:91-102`, 12 lines) and `NormBand_subgaussian` (`NormBand:155-162`, 8 lines), and the entry bound `|Ψ_xy| ≤ 1` needs either the private `UNPins_psiI_rowsum` (`UNPins:240`, under 25 lines) or the public `PsiB`/`Adj` entries; target 5's twin needs these, they are under the 60-line copy limit and reachable by `open private` as the listed ones are; (2) the ticket's G1 count 166 uses 66 code lines for `:38-116`, the measured count is 68 (168).

### (ii) Concrete nondegenerate instance (target 5 and the end `d = 3`)

`d = 3`, `S0 = clsSz 4` (`UNPins:776`): `L = 4`, `W_n = (2(n+1))^5`, `N_n = (4 W_n)^3`, `λ_n = g0 ∈ (0, 3/10]` (`FlowPt.g0_pos`, `g0_le`, `MFixedPoint:877-882`; `S0` is `(L, g) = (4, 3/10)`, `UNPins:884`), `(𝔠, 𝔡) = (1/6, 1/10)` (`S0_adm`, `UNPins:887`), `𝔡⁻¹ = 10`, `κ_* = clsκ 4`, `E_* = (fp 4 _).E`, `k = 1`, `E' = 0`, `O = bump` (the T2513 instances, probe `:322-387`). The script evaluates the two inequalities of (i), both in `λ ≤ 3/10` and in the worst admissible case `λ = 𝔡⁻¹`, at the first four sizes, with the log of the tail (no overflow).

```
$ python3 -I inst.py
n=0 W=32 N=2097152 (2^21) A(lam<=3/10)=True A(lam<=1/dd)=True Dsuff=72034.8 Dmax_true=1.511e+11
   D=1: log tail -2.1990e+12 <= -1.4556e+01: True;  lemma cond -1.0485e+06 <= -1.3863: True
   D=10: log tail -2.1990e+12 <= -1.4556e+02: True;  lemma cond -1.0484e+06 <= -1.3863: True
   D=100: log tail -2.1990e+12 <= -1.4556e+03: True;  lemma cond -1.0471e+06 <= -1.3863: True
   D=1000: log tail -2.1990e+12 <= -1.4556e+04: True;  lemma cond -1.0340e+06 <= -1.3863: True
n=1 W=1024 N=68719476736 (2^36) A(lam<=3/10)=True A(lam<=1/dd)=True Dsuff=1376961779.9 Dmax_true=9.462e+19
   D=1: log tail -2.3612e+21 <= -2.4953e+01: True;  lemma cond -3.4360e+10 <= -1.3863: True
   D=10: log tail -2.3612e+21 <= -2.4953e+02: True;  lemma cond -3.4360e+10 <= -1.3863: True
   D=100: log tail -2.3612e+21 <= -2.4953e+03: True;  lemma cond -3.4360e+10 <= -1.3863: True
   D=1000: log tail -2.3612e+21 <= -2.4953e+04: True;  lemma cond -3.4360e+10 <= -1.3863: True
n=2 W=7776 N=30091839012864 (2^45) A(lam<=3/10)=True A(lam<=1/dd)=True Dsuff=484800584087.9 Dmax_true=1.459e+25
   D=1: log tail -4.5276e+26 <= -3.1035e+01: True;  lemma cond -1.5046e+13 <= -1.3863: True
   D=10: log tail -4.5276e+26 <= -3.1035e+02: True;  lemma cond -1.5046e+13 <= -1.3863: True
   D=100: log tail -4.5276e+26 <= -3.1035e+03: True;  lemma cond -1.5046e+13 <= -1.3863: True
   D=1000: log tail -4.5276e+26 <= -3.1035e+04: True;  lemma cond -1.5046e+13 <= -1.3863: True
n=3 W=32768 N=2251799813685248 (2^51) A(lam<=3/10)=True A(lam<=1/dd)=True Dsuff=31849612002727.4 Dmax_true=7.172e+28
   D=1: log tail -2.5353e+30 <= -3.5351e+01: True;  lemma cond -1.1259e+15 <= -1.3863: True
   D=10: log tail -2.5353e+30 <= -3.5351e+02: True;  lemma cond -1.1259e+15 <= -1.3863: True
   D=100: log tail -2.5353e+30 <= -3.5351e+03: True;  lemma cond -1.1259e+15 <= -1.3863: True
   D=1000: log tail -2.5353e+30 <= -3.5351e+04: True;  lemma cond -1.1259e+15 <= -1.3863: True
mean bound: 2d/dd = 60.0 <= N^(CV0+1)=N^4 at n=0: True ; <= N^3: True
min N for N^2>=2N+10: 4.3166247903554
ouTauMax(1/6,1/10) = 0.001388888888888889 =1/720: True
queChain: eps0= 0.03333333333333333 c= 0.016666666666666666 -min(2e0,2dd/5)= -0.04 ; exponent <0 iff tau < 0.006666666666666668 (=1/150); tau_Q=1/300 slack 0.0033333333333333344
```

All hypotheses of target 5 hold together at `n = 0`: `N = 2^21 > 4.317`, `W^6 = 2^30 ≥ N = 2^21` (the `Bandwidth` inequality at `n = 0`, `𝔠 = 1/6`), `0 < λ ≤ 3/10 ≤ 10`, window `D` arbitrary up to the printed bounds. No `N = 0`, no empty index set (`2N² = 2^43` coordinates). The first inequality needs only `N ≥ 4.32`; the tail in the lemma form at `D = 1` (`N^3 e^{-N/2} ≤ 1/4`) first holds at `N = 22`, so the witness is not forced by an astronomical size. The probe takes `UNL32`, `UNMLOutBA 3`, the five C5 names (`BAKFam`, `BAPB`, `ba_prodG`, `ba_LLG`, `ba_QueG`) as hypotheses of exact type, as the ticket says; no external limit hypothesis is introduced (the only external input is the borrowed `UNL32`, unchanged and not a new hypothesis of N2).

### Verdict and the two ticket-asked statements

- Reprice per file: all three files under their stop lines and under 2,000 at the landed forecast (table above); total 662 central, 887-1,106 landed, under the 1,950 line by 844 at the top.
- Mathematics of target 5: closes with `CV₀ = 3`, slack as in (i); no exponent control beyond the two inequalities.
- The 1a moves no pin (no `T2520_*` text changed by this section), moves no stop line (450 / 400 / 1,100 / 2,000 unchanged), and does not fire the fallback (1,106 < 1,950). The `open private` addition in (i) is an addition to the ticket's list inside its stated rule (copy under 60 lines), not an amend.
- `1a-audit needed: no` — reason: no pin moved, no stop line moved, no fallback (Decisions (1), ticket row 8); the compile of `RBM3D/Probe/T2520Pins.lean` and the exact-type check of the five C5 names against the signed `T2519_*` texts are the next step's (not covered here).
- Verdict T2520 targets 1-7: PASS (mathematics and reprice). No target BLOCKED: every input is on `main` or is the signed C5 name list (T2519 Amend 3 item 6).

## (a″) Probe compile — Fri Oct 16 13:48:04 UTC 2026

Probe `RBM3D/Probe/T2520Pins.lean` in `/Users/junyin/Lean_proof/RBM3D-wt/T2520`, branch `t/T2520`, commit 82ef67a8 (`git diff --stat main...t/T2520`: this file only, 196 insertions; no root import, no importer). Inputs read: `docs/tickets/checks/T2520-pins.lean` (265 lines), the signed `T2519_*` texts (`git show b992c2e7:RBM3D/Probe/T2519Pins.lean`, lines 29-39), the T2513 probe (`git show a6d9966e:RBM3D/Probe/T2513Pins.lean`). `main` = cabd9a3d; `git diff --stat 43597737 main -- RBM3D RBM3D.lean` is empty (the ticket's `main` 43597737 and cabd9a3d carry the same Lean). Section (a) is not edited; no (a′): nothing in (a) was found wrong. Scratch scripts and outputs are in the scratchpad `T2520/` (not committed); every block below is their verbatim output.

### Acceptance: the probe compiles (fill-in row (iii))
```
$ lake env lean RBM3D/Probe/T2520Pins.lean; echo "exit=$?"        # run at 13:41:19 UTC (date -u)
@NormBand_eig_le : ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
  {B : ℝ}, (∀ (x y : ι), ‖H x y‖ ≤ B) → ∀ (i : ι), |hH.eigenvalues i| ≤ ↑(Fintype.card ι) * B
NormBand_Xentry_le : ∀ (d L W : ℕ) [inst : NeZero L] [inst_1 : NeZero W] (s : Ω d L W) {B : ℝ},
  (∀ (c : CoordF d L W), |s c| ≤ B) → ∀ (i j : Idx d L W), ‖Xentry d L W s i j‖ ≤ 2 * B
NormBand_tail_eventually : ∀ (D : ℝ) {d : ℕ} (sz : Sizes d),
  sz.SizeTendsto → ∀ᶠ (n : ℕ) in atTop, 4 * Nsz sz n ^ 2 * Real.exp (-(Nsz sz n ^ 2 / 2)) ≤ Nsz sz n ^ (-D)
@NormBand_gvar_le : ∀ {d : ℕ} (sz : Sizes d) (c : sz.SeqCoord), ↑(sz.seqGvar c) ≤ 1
@NormBand_subgaussian : ∀ {d : ℕ} (sz : Sizes d) (c : sz.SeqCoord),
  ProbabilityTheory.HasSubgaussianMGF (fun ω => ω c) 1 sz.seqP
UNPins_psiI_rowsum : ∀ (d L W : ℕ) [inst : NeZero L] [inst_1 : NeZero W],
  3 ≤ L → ∀ (x : Idx d L W), ∑ y, ‖PsiI d L W x y‖ = 2 * ↑d
'RBM.Univ.T2520_baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.T2520_unOURowBA_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
28 T2520_ theorems; distinct axioms lists: [[propext, Classical.choice, Quot.sound], [propext], [propext, Quot.sound]]
exit=0
$ wc -l RBM3D/Probe/T2520Pins.lean        -> 196   (ticket: <= 150, cap 200: target exceeded, cap held)
$ lake build RBM3D.Probe.T2520Pins | tail -1   -> Build completed successfully (4409 jobs).  (exit 0; warning/error lines naming the probe file: 0)
$ grep -cE "sorry|admit|axiom|native_decide|STStep5IIIgL" RBM3D/Probe/T2520Pins.lean   -> 0
$ grep -c "^def" / "^theorem" / "^example" RBM3D/Probe/T2520Pins.lean   -> 14 / 24 / 1
```
Contents by line (`grep -n`): `open private` 16-18; G1 eight pins 23-52, ten `Iff`s 53-68; G2 chain 69-111; BA leaf (readings, the two §340 (2) `Iff`s, `jakUywRowkD`, `un_claimAll_of_rowsBAD`, `baBUniv_of_rowsD`) 112-147; section `End` 148-181 (C5 producers as hypotheses `hProd hLL hQue`; `baEnd_BUnivL_of_ML`, `baThm27L_of_ML`, `baEnd_BUnivL_three`, `baThm27L_three`; F3 `unOURowBA_holds`; the `d = 3` instance at `S0`, 174-180); `#check`, `#print axioms`, `#eval` 182-194. 196 lines exceed the 150 target because the pins file is not importable: the probe restates the eight pins and compiles the thirteen merged proofs of G1/G2/`jakUywRowkD` (row (v)) instead of taking them as hypotheses.

### Fill-in table, one line per row (§269 (5))
- (i), (ii): done in (a); n/a here, because the probe has no new inequality (target 5 is not proved in the 1a).
- (iii) done. G1 texts and the ten `Iff`s (the eight at `Dm = fun _ => True`, `band_locAvg`, `band_ouRow`) compile; the two §340 (2) `Iff`s are `T2520_unLocAvgBAD_iff_at`, `T2520_unQueBAD_iff_at`; `baBUniv_of_rowsD` is applied at `Dm = (· = d)` (any `d`, so `d = 3`) with `rT0 := unTrLocalBAAt_of_locAvg`, `rT := unTrLocalInitBAAt'_of_locAvg`, `hLoc` from `unLocAvgBAAt_of_locSCL d hd (baEnd_locSCL d hML)`, `hQ` from `unQueBAAt_of_ML d hd hML` (`hML := unMLOutBA_three` at `d = 3`), no `∀ d` BA input; `T2520_Thm27ThreeOfC5` is `T2520_baThm27L_three KF PB hProd hLL hQue rN` (C5 as hypotheses of the signed types, `KF`, `PB` free); `#print axioms`: the standard three or a subset, for all 28 `T2520_` theorems (probe output above); nonempty instance: the `example` at `d = 3`, `S0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_*`, `E_*`, `k = 1`, `E' = 0`, `𝒪 = bump`, concluding `UNUnivDilAt S0 (UNModel.ba S0) …` with every deterministic hypothesis discharged; hypotheses left: `UNL32`, `UNNormBARow` (target 5), the three C5 producers.
- Pin texts against the probe (used by (iii)-(v)): scratch `pins_eq.lean` = the pins file with its namespace renamed `RBM.Univ.PC`, plus the signed `T2519` texts as namespace `T19`, plus 48 `example`/`theorem` lines tying each pins text to the probe (`rfl` for defs, the probe term for statements):
```
$ python3 -I gen_eq.py; lake env lean pins_eq.lean; echo "exit=$?"   (probe built first by `lake build RBM3D.Probe.T2520Pins`)
written pins_eq.lean 341 lines
exit=0     (empty output: all 48 ties elaborate: 8 pins, 6 BA readings, 10 `Iff`s, 4 G2 statements, the two M1/M3 `Iff`s, `T2520_TrLocalAt`, `T2520_TrLocalInitAt`, `T2520_JakUywRowkD`, `T2520_ClaimAllOfRowsBAD`, `T2520_BaBUnivOfRowsD`, `T2520_EMCTE2RowBAD`, 3 C5 texts, `T2520_BUnivOfML`, `T2520_Thm27OfML`, `T2520_BUnivThree`, `T2520_Thm27Three`, `T2520_Thm27Any` (OQ2: `baMainIndFamTL_any`, `unMLOutBA_of_famStep`), `T2520_OURowBA` (F3), `T2520_Thm27ThreeOfC5`, `T2520_G1RowBAD`, `T2520_OURowBAD`)
```
- (iv) the signed `T2519_*` texts against `T2520_C5*` (script diff, whitespace normalised; also T2519-pins on `main` and the probe's hypothesis binders; `pins_eq.lean` ties `T19.T2519_*` to `PC.T2520_C5*` by `rfl` too):
```
$ python3 -I c5diff.py
ProdBA   signed(b992c2e7) == T2520-pins: True ; T2519-pins(main) == T2520-pins: True
LLBA     signed(b992c2e7) == T2520-pins: True ; T2519-pins(main) == T2520-pins: True
QueBA    signed(b992c2e7) == T2520-pins: True ; T2519-pins(main) == T2520-pins: True
ProdBA   probe binder hProd  == body of the signed text: True
LLBA     probe binder hLL    == body of the signed text: True
QueBA    probe binder hQue   == body of the signed text: True
ALL EQUAL: True
```
  `T2519_KFamBA`, `T2519_PBBA` are not read by text: `KF`, `PB` are free in every probe theorem (ticket Decision (1)). On `t/T2519` (83170e46, 13:44 UTC) `BAKFam` (`BA/GUEProcBA.lean:76`) and `BAPB` (`:93`) exist with an exact-type check of the three producers (`:97-102`); `ba_prodG`, `ba_LLG`, `ba_QueG` do not exist yet (row d).
- (v) statdiff G1/G2 against the merged texts after deleting the filter (T2513 `statdiff.py`, adapted to the probe's layout):
```
$ python3 -I statdiff.py
UNQuek                               merged PinsK.lean:398-403  probe :24-27  identical after the filter map: True
UNLocAvgk                            merged PinsK.lean:406-414  probe :28-32  identical after the filter map: True
UNOUClaimsk                          merged PinsK.lean:421-423  probe :33-35  identical after the filter map: True
UNOURowk                             merged PinsK.lean:426-426  probe :36-36  identical after the filter map: True
UNEMCTE2Rowk                         merged PinsK.lean:429-432  probe :37-39  identical after the filter map: True
UNJakUywRowk                         merged PinsK.lean:435-439  probe :40-43  identical after the filter map: True
UNClaimRowk                          merged PinsK.lean:442-449  probe :44-49  identical after the filter map: True
UNG1Rowk                             merged OUInterfaceK.lean:101-105  probe :50-52  identical after the filter map: True
un_claimAll_of_rowsk (stmt+proof)    merged PinsK.lean:454-466  probe :70-81  identical after the filter map: True
unClaimRowk (stmt+proof)             merged UnivMain.lean:471-477  probe :82-88  identical after the filter map: True
jakUywRowk (stmt+proof)              merged EMCTE2BA.lean:629-637  probe :121-129  identical after the filter map: True
ouRowk_of_pins (stmt+proof)          merged OUInterfaceK.lean:292-298  probe :89-94  identical after the filter map: True
g1Rowk_of_inputsG (stmt+proof)       merged RandomLayerBG.lean:399-427  probe :95-111  identical after the filter map: True
ALL IDENTICAL: True
```
  The probe's `un_claimAll_of_rowsBAD`, `baBUniv_of_rowsD` differ from the merged `…_of_rowsBA`, `baBUniv_of_rows` by design (filter; `rT0`, `rT` at M1 b's per-`d` types); they are tied to the pins texts in `pins_eq.lean` instead.
- (vi) n/a here, because no pin, stop line or count moved: the probe declares nothing beyond the list priced in (a) (readings, `Iff`s, G1, G2, `jakUywRowkD`, assembly, end, F3); the reprice of (a) stands (total landed 887-1,106 against the 1,950 line).
- (vii) `open private` compiled (probe lines 16-18 and the `#check` outputs above): `RandomLayerBG_oull_seq`, `RandomLayerBG_eq747_seq`, `UNPins_normBound_mono`, `UNPins_hg_3_10` are used by the compiled proofs and the instance; `NormBand_eig_le`, `NormBand_Xentry_le`, `NormBand_tail_eventually`, `NormBand_gvar_le`, `NormBand_subgaussian`, `UNPins_psiI_rowsum` (with the additions named in (a) (i)) are reachable by `open private` and have the types printed above; no private is copied, so the 60-line copy limit is not touched.
- (viii) registry scan preview (`RBM.Audit.scanPremises`, whole library `import RBM3D` in the worktree, ignore `RBM.Audit`; newlines inside the lists collapsed):
```
$ lake env lean scan_before.lean      # the library as on main
scanPremises (whole library, ignore RBM.Audit): 124 premises found; watched names still found (assumed, never concluded): [RBM.Univ.UNNormBARow, RBM.Univ.UNOURowBA, RBM.Univ.UNOULLk, RBM.Univ.UNQuek]; watched names not found: [RBM.Univ.UNEMCTE2RowBA, RBM.Univ.UNJakUywRowBA, RBM.Univ.UNG1Rowk, RBM.Univ.UNLocAvgk] found premises with T2520_ in the name: []
$ lake env lean scan_after.lean       # + the probe
scanPremises (whole library, ignore RBM.Audit): 131 premises found; watched names still found (assumed, never concluded): [RBM.Univ.UNNormBARow, RBM.Univ.UNOULLk, RBM.Univ.UNQuek]; watched names not found: [RBM.Univ.UNOURowBA, RBM.Univ.UNEMCTE2RowBA, RBM.Univ.UNJakUywRowBA, RBM.Univ.UNG1Rowk, RBM.Univ.UNLocAvgk] found premises with T2520_ in the name: [RBM.Univ.T2520_UNQueBAD, RBM.Univ.T2520_UNLocAvgBAD, RBM.Univ.T2520_UNOURowBAD, RBM.Univ.T2520_UNJakUywRowBAD, RBM.Univ.T2520_UNEMCTE2RowBAD, RBM.Univ.T2520_UNClaimRowBAD, RBM.Univ.T2520_UNEMCTE2RowkD]
$ lake env lean scan_emul.lean        # + two scratch theorems emulating the 1b rows unEMCTE2RowBAD_holds, unOURowBAD_holds
probe + emulated rows: found with T2520_ in the name: [RBM.Univ.T2520_UNQueBAD, RBM.Univ.T2520_UNLocAvgBAD, RBM.Univ.T2520_UNJakUywRowBAD, RBM.Univ.T2520_UNClaimRowBAD, RBM.Univ.T2520_UNEMCTE2RowkD]
$ lake env lean scan_emul2.lean       # + two more: ∀ Dm, UNClaimRowBAD Dm and ∀ Dm, UNJakUywRowBAD Dm (one-liners from unClaimRowkD, jakUywRowkD)
probe + emulated rows: found with T2520_ in the name: [RBM.Univ.T2520_UNQueBAD, RBM.Univ.T2520_UNLocAvgBAD, RBM.Univ.T2520_UNEMCTE2RowkD]
```
  Reading. Before: 124 premises found; `UNEMCTE2RowBA`, `UNJakUywRowBA` are not found (concluded since T2476: owed lines `Test/Axioms:177-178` are stale, F4); `UNNormBARow` (`:179`) and `UNOURowBA` (`:176`) are found. With the probe: 131; `UNOURowBA` is concluded by `T2520_unOURowBA_holds` (F3). Owed lines to delete at 1b: `:176`, `:177`, `:178`, `:179` = −4 (ticket: −2 to −4). New premises found with the probe: seven `T2520_` names (`UNQueBAD`, `UNLocAvgBAD`, `UNOURowBAD`, `UNJakUywRowBAD`, `UNEMCTE2RowBAD`, `UNClaimRowBAD`, `UNEMCTE2RowkD`) plus `RBM.BA.BAMO` (a probe artefact: it occurs in the probe's hypothesis binders `hProd`, `hQue`; at 1b the C5 names are applied, not binders). After the 1b rows `unEMCTE2RowBAD_holds`, `unOURowBAD_holds` conclude two, **5 structural names remain: `UNQueBAD`, `UNLocAvgBAD`, `UNJakUywRowBAD`, `UNClaimRowBAD`, `UNEMCTE2RowkD`** (the ticket expected 0; its bound is "at most 5", report `:106`); with two extra one-liner theorems 3 remain (last block). `UNOULLk` (`:168`) and `UNQuek` (`:384`) stay found: their owner lines stay.
- (ix) C1 and forbidden-token greps, D6, X1-C4:
```
$ zsh greps.sh   (the lines of its output on C1, tokens, D6, importers)
G1 pin texts: lines 23-52; G2 chain: lines 69-111
C1 scan (BA/band vocabulary: BA|band|Band|\.ba) in G1 pin texts: 0  in G2 chain: 0
forbidden tokens (sorry|admit|axiom|native_decide|STStep5IIIgL) in probe: 0
D6 grep (no STStep5IIIgL, no '∀ d.*UNMLOutBA' form, no UNLocAvgBA/UNQueBA) on the probe's D6 theorems:
0
importers of the probe (RBM3D.lean and RBM3D/):        0; RBM3D.lean imports of Probe: 0
$ grep -c "T2513_" RBM3D/Probe/T2520Pins.lean; grep -c "BAGz|BAMz|BAendDom|BAlocBad" RBM3D/Probe/T2520Pins.lean   -> 0 / 0
```
  X1-C4: no `T2513_BAEnd_locSCL` vocabulary and no TrLocal core is copied; the probe reads `UNLocAvgBAAt`, `UNTrLocalBAAt`, `UNTrLocalInitBAAt'`, `UNQueBAAt`, `unLocAvgBAAt_of_locSCL`, `unQueBAAt_of_ML`, `unTrLocalBAAt_of_locAvg`, `unTrLocalInitBAAt'_of_locAvg`, `baEnd_locSCL`, `baEnd_decolL`, `baEnd_QUEL`, `baEnd_QDiffL`, `unMLOutBA_three` by name. The D6 grep ran on the probe's two end theorems, which carry the probe's stand-ins (`rN`, `hProd`, `hLL`, `hQue`) for `unNormBARow_holds`, `ba_prodG`, `ba_LLG`, `ba_QueG`; the final D6 signatures `UNL32 → BAEnd_BUnivL 3`, `UNL32 → BAThm27L 3` have none of them.
- (x) imports: the probe imports `Main.BandTerminal`, `BA.EMCTE2BA`, `BA.MATrLocalBA`, `BA.MADecolQUE`, `BA.GUEKPrim`, `Universality.NormBand` (the first draft had 13 imports; each was tried removed and this set of six compiles); importers of the probe: 0 (above); the three 1b modules do not exist in the worktree (`ls`: No such file or directory) and no file imports them; at 1b only `RBM3D.lean` gets import lines.
- (xi) name-clash grep of 52 names (the final names of every ticket target with the `T2520_` prefix dropped, the `…_true` names in both spellings `UN…D_true` and `…D_true`), `git grep -w` on refs `main`, `t/T2519`, `t/T2519b`, `t/T2519b2` and `grep -rnw` on the worktree, probe file excluded:
```
name-clash grep (git grep -w over RBM3D/): refs main, t/T2519, t/T2519b, t/T2519b2, and the worktree (excluding the probe)
names checked:       52; total hits: 0; names with hits:
```

### Verdict of the probe and the stated question
- Compiled or run: (iii) probe exit 0; (iv) 3 of 3 producer texts equal (and `rfl`); (v) 13 of 13 identical after the filter map; (vii) three `open private` lines compile; (viii) scan preview above.
- O1 (not a pin move): the pinned text `T2520_Thm27ThreeOfC5` has no `UNNormBARow` hypothesis, but `BAEnd_BUnivL 3` needs it until target 5 is proved, so the probe's `T2520_baThm27L_three` and `T2520_baEnd_BUnivL_three` carry `rN : UNNormBARow`; target 5 discharges it at 1b by `unNormBARow_holds`. The pinned `T2520_Thm27Three := UNL32 → BAThm27L 3` is the type of `T2520_baThm27L_three KF PB hP hL hQ rN` (scratch example).
- O2 (not a stop): the registry preview needs 5 new structural lines at 1b (the ticket expected 0 and allows at most 5; owed −4). The dispatcher may add `unClaimRowBAD_holds`, `unJakUywRowBAD_holds` (`∀ Dm, UNClaimRowBAD Dm`, `∀ Dm, UNJakUywRowBAD Dm`) to the 1b targets, which leaves 3 (last scan block); the 1b does not add them without an amend.
- O3: `T2520_Thm27ThreeOfC5At3` (producers at `d = 3` only, OQ5) is not compiled: C5's producers are signed `∀ d` (T2519-1a-audit §9, Amend 3 item 6), so that branch is unused.
- **1a-audit needed: no.** The 1a moves no pin (every `T2520_*` text used here is tied to the probe by `rfl` or by the probe term; the C5 texts equal the signed `T2519_*`), moves no stop line (450 / 400 / 1,100 / 2,000 and the 1,950 line unchanged; reprice of (a): landed 887-1,106) and does not fire the fallback (1,106 < 1,950; `BAThm27L 3` stays in N2); O1-O3 are observations (Decisions (1)).

## (b) Script output, stage 1b (`prover-hard`, claude-sonnet-5-5; worktree `RBM3D-wt/T2520`, branch `t/T2520`; started 19:13:53 UTC `date -u`)
(a), (a″) are unedited; no (a′): nothing in (a) was found wrong. Scratch scripts and outputs: scratchpad `T2520/`; every block is their verbatim output.
```
$ git merge main (07f90182) -> 82d43f2a; TZ=UTC git log --format='%h %cd %s' --date=format-local:'%H:%M:%S UTC' 82d43f2a..HEAD
d01e9789 19:30:01 UTC T2520: root imports and registry (owed UNOURowBA, UNEMCTE2RowBA, UNJakUywR...
116472bb 19:26:38 UTC T2520: BA leaf BA/UNBUniv (filtered BA assembly, unNormBARow_holds, rows, ...
3056caea 19:19:48 UTC T2520: G2 Universality/GUEPhase/RandomLayerBGD (filtered chain, band insta...
795ebf27 19:17:52 UTC T2520: G1 Universality/PinsKD (eight filtered pins, the _true equivalences...
$ git diff --name-only --diff-filter=M main...t/T2520     -> RBM3D.lean, RBM3D/Test/Axioms.lean   (no band or merged Lean file modified)
$ git diff --name-only --diff-filter=A main...t/T2520     -> RBM3D/BA/UNBUniv.lean, RBM3D/Probe/T2520Pins.lean (the 1a probe), RBM3D/Universality/GUEPhase/RandomLayerBGD.lean, RBM3D/Universality/PinsKD.lean
$ lake build RBM3D.Universality.PinsKD | tail -1 / ...GUEPhase.RandomLayerBGD / RBM3D.BA.UNBUniv   (19:33:21 UTC)
Build completed successfully (3740 jobs).  /  (3887 jobs).  /  (4426 jobs).      ($ lake env lean <file> | grep -c 'warning\|error', each of the three files: 0)
$ lake build   (full, 19:28:37 - 19:29:45 UTC, from the worktree at the content of d01e9789 (committed 19:30:01 UTC); latest mtime of the five committed Lean files 19:28:31 UTC)
info: RBM3D.lean:672:0: axiom audit: 15817 theorems, 4857 definitions, 0 axioms in `RBM` ...   Build completed successfully (4442 jobs).   exit=0
$ wc -l (at each section commit)                lines   price central   landed x1.34-1.67   stop line
RBM3D/Universality/PinsKD.lean                    188      168           225-281            450
RBM3D/Universality/GUEPhase/RandomLayerBGD.lean   183      118           158-197            400
RBM3D/BA/UNBUniv.lean                             397      376           504-628           1100
total 768 (central 662, landed 887-1106; 1,950 line; 2,000 per file): no stop line reached
```
### Targets, axioms, instances
```
$ python3 -I extract.py     (statements from the files; the D6 pair is the text for the M/N closing REQ, closing (vi))
UNBUniv.lean:276 theorem baEnd_BUnivL_three : UNL32 → BAEnd_BUnivL 3
UNBUniv.lean:281 theorem baThm27L_three : UNL32 → BAThm27L 3
UNBUniv.lean:262 theorem baEnd_BUnivL_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAEnd_BUnivL d
UNBUniv.lean:271 theorem baThm27L_of_ML (d : ℕ) (hd : 3 ≤ d) (h32 : UNL32) (hML : UNMLOutBA d) : BAThm27L d
UNBUniv.lean:286 theorem baThm27L_any (d : ℕ) (hd : 3 ≤ d) (h5 : STStep5IIIgL d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)) (h32 : UNL32) : BAThm27L d
UNBUniv.lean:145 theorem unNormBARow_holds : UNNormBARow
UNBUniv.lean:217 theorem unEMCTE2RowBAD_holds : ∀ Dm : ℕ → Prop, UNEMCTE2RowBAD Dm
UNBUniv.lean:233 theorem unOURowBAD_holds : ∀ Dm : ℕ → Prop, UNOURowBAD Dm
UNBUniv.lean:247 theorem unOURowBA_holds : UNOURowBA
UNBUniv.lean:238 theorem unG1RowkBA_holds : UNG1Rowk (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA
UNBUniv.lean:223 theorem unG1RowkBAD_holds : ∀ Dm : ℕ → Prop, UNG1RowkD Dm (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, Dm d → UNMLOutBA d) (UNLocAvgBAD Dm) (UNQueBAD Dm)
RandomLayerBGD.lean:60 theorem unClaimRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : UNClaimRowkD Dm K
UNBUniv.lean:82 theorem unLocAvgBAD_iff_at (d : ℕ) : UNLocAvgBAD (· = d) ↔ (3 ≤ d → UNLocAvgBAAt d)
UNBUniv.lean:86 theorem unQueBAD_iff_at (d : ℕ) : UNQueBAD (· = d) ↔ (3 ≤ d → UNQueBAAt d)
$ lake env lean ax_all.lean
'RBM.BA.baEnd_BUnivL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unNormBARow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
new declarations in the three modules: 45 theorems, 14 definitions; distinct axiom lists over all 45 theorems: [[propext, Classical.choice, Quot.sound]]; depending on sorryAx: 0
$ lake env lean pins_eq_1b.lean   (the `T2520-pins.lean` texts, namespace renamed `PC`, + 51 `example : PC.T2520_X := final name` / `= … := rfl` ties)
exit=0     (51 ties: 8 pins, 6 BA readings, 10 `Iff`s, 4 G2, 2 `Iff` to M1/M3, 2 TrLocal types, jakUywRowkD, claim, assembly, 6 rows, 5 end, C5 three, 2 C5 forms)
$ python3 -I c5diff.py   (signed T2519_* texts vs T2520_C5* texts; the Lean ties `PC.T2520_C5ProdBA BAKFam BAPB := ba_prodG`, `…LLBA BAPB := ba_LLG`, `…QueBA BAKFam BAPB := ba_QueG` are among the 51)
ProdBA signed(b992c2e7) == T2520-pins: True ; T2519-pins(main) == T2520-pins: True    (LLBA, QueBA alike)    ALL EQUAL: True
$ python3 -I statdiff_1b.py | awk '…'      (G1 8 pins + G2 4 theorems + jakUywRowkD against the merged text, after deleting the filter)
13 of 13 rows identical after the filter map; ALL IDENTICAL: True
$ lake env lean band_before.lean ; lake env lean band_after.lean     (MNO-C1; before = the two band modules alone, after = + the three new modules)
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]   (before and after: identical)
'RBM.Endpoints.bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]    (before and after: identical)
```
Instances (compiled, same files; `d = 3`, `S0` `(L, g) = (4, 3/10)` of (a) (ii), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_*`, `E_*`, `k = 1`, `E' = 0`, `𝒪 = bump`): `UNBUniv` 312-397: `inst_UNOURowBAD`, `inst_UNEMCTE2RowBAD`, `inst_UNJakUywRowBAD`, `inst_claimAll_baD` (no hypothesis), `inst_univ_baD (h32 : UNL32)`, `inst_unNormBARow`, `inst_unG1RowkBAD` (no hypothesis), `inst_unG1RowkBA`, `inst_unOURowBA` (the `∀ d` consumed inputs of the merged text as hypotheses), `inst_baEnd_BUnivL_three (h32)`, `inst_baThm27L_three (h32)` and an `example` of the per-`d` forms and `baThm27L_any 3 le_rfl baStep5III_holds h32`. `RandomLayerBGD` 122-183: `inst_unClaimRowkD_band_zero`, `inst_un_claimAll_of_rowskD`, `inst_ouRowk_of_pinsD`, `inst_g1Rowk_of_inputsGD` (band kind, `sz0`; other gates' pins stay hypotheses). `PinsKD` 151-186: ten `example`s at the band kind. The end instance, verbatim:
```
theorem inst_baThm27L_three (h32 : UNL32) : UNUnivDilAt S0 (UNModel.ba S0) (fun n => BArho 3 (S0.L n) (S0.lam n) (fp 4 UNPins_hg_3_10).E) (fp 4 UNPins_hg_3_10).E 0 1 (UNInst.bump : (Fin 1 → ℝ) → ℝ) :=
  (baThm27L_three h32).2.2.2.1 le_rfl (1 / 6) (1 / 10) S0 S0_adm 1 le_rfl (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk 0 (by norm_num) UNInst.bump UNInst.bump_testFun
```
### Registry scan (`RBM.Audit.scanPremises`, whole library, `ignore RBM.Audit`), greps, name table
```
$ lake env lean scan_1b.lean   # before (library as on main) / after (final worktree, `import RBM3D` built)
124 premises found; still found: [UNNormBARow, UNOURowBA, UNOULLk, UNQuek]; not found: [UNEMCTE2RowBA, UNJakUywRowBA, UNG1Rowk, UNLocAvgk]; found in no ledger: []
127 premises found; still found: [UNOULLk, UNQuek]; not found: [UNNormBARow, UNOURowBA, UNEMCTE2RowBA, UNJakUywRowBA, UNG1Rowk, UNLocAvgk]; found in no ledger: []
(scan before the registry edit, library + the three modules: found in no ledger = [UNQueBAD, UNLocAvgBAD, UNJakUywRowBAD, UNClaimRowBAD, UNEMCTE2RowkD] -> registered as 5 structural lines)
$ zsh greps_1b.sh
G1 pin texts lines 39-96; G2 chain lines 41-109;  C1 scan (BA|band|Band|\.ba) in G1 pin texts: 0  in G2 chain: 0
forbidden tokens (sorry|admit|axiom|native_decide) in the three files: 0;  T2513_/T2520_ vocabulary copied: 0 0 0;  BAGz|BAMz|BAendDom|BAlocBad|T2513_BAEnd_locSCL: 0
STStep5IIIgL: UNBUniv.lean:36 (docstring), :284 (docstring of baThm27L_any), :287 (its binder h5); D6 grep (STStep5IIIgL, '∀ d.*UNMLOutBA', UNLocAvgBA, UNQueBA) on the two D6 statements: hits 0
importers: PinsKD <- RBM3D.lean, RandomLayerBGD, UNBUniv; RandomLayerBGD <- RBM3D.lean, UNBUniv; UNBUniv <- RBM3D.lean
name-clash grep, 59 names (every public name of the three files), git grep -w on main, t/T2519, t/T2519b, t/T2519b2 and grep -rnw on the worktree outside the three files: total hits 0
$ lake env lean docs/tickets/checks/T2520-check.lean (in the worktree after the merge)   -> exit=0; 149 #check lines; error lines 0
name table (name @ module:line, by `findDeclarationRanges?`; C5 `grep -n` lines: BAKFam GUEProcBA:76, BAPB :93, ba_LLG GUEHyp:918, ba_QueG :924, ba_prodG :934):
BAKFam@BA.GUEProcBA:72 BAPB@:91 ba_prodG@BA.GUEHyp:929 ba_LLG@:917 ba_QueG@:922 unMLOutBA_three@BA.MainIndTermBA:46 baEnd_locSCL_three@BA.MALocal:837 unLocAvgBAAt_of_locSCL@:841
unQueBAAt_three@BA.MADecolQUE:381 unTrLocalBAAt_of_locAvg@BA.MATrLocalBA:77 unTrLocalInitBAAt'_of_locAvg@:230 baOUProfRowk_holds@BA.GUEKPrim:581 baProfComp@:601 ba_flowG@BA.RandomLayerBGBA:91
ba_domG@:102 ba_mlout@:113 RandomLayerBGBA_comp@:123 unCoreC''_holds@Universality.UnivMain:648 unDensBARow'_holds@BA.MReg:331 unEMCTE2RowBA_holds@BA.EMCTE2BA:653 g2bRowk@Universality.QUEFlow:894
baEnd_decolL@BA.MADecolQUE:142 baEnd_QUEL@:358 baEnd_QDiffL@BA.MAQDiff:1011 BAThm27L@BA.MAPins:125 UNL32@Universality.Pins:264
```
### Narrative
- Layout as the ticket: G1 `PinsKD` (eight filtered pins, ten `Iff`s, ten band-kind instances), G2 `RandomLayerBGD` (the four chain theorems, merged proofs with `Dm d` threaded, `open private` of `RandomLayerBG_oull_seq`, `_eq747_seq`; four band instances), BA leaf `UNBUniv`. The D6 theorems and the per-`d` forms are in namespace `RBM.BA` (as `T2521-check.lean:51`, `RBM.BA.baThm27L_three`); the rest in `RBM.Univ`. Ports: none from `../RBM1D`, `../RBM2D` (every copy is of a merged RBM3D text: the chain proofs of `PinsK`, `UnivMain`, `OUInterfaceK`, `RandomLayerBG`, `EMCTE2BA`, `NormBand`), so no sister diff-stat.
- C5 wiring is by name: `BAKFam`, `BAPB`, `ba_prodG`, `ba_LLG`, `ba_QueG` with `∀ d` producers, so F3 holds: `unG1RowkBA_holds`, `unOURowBA_holds` prove the merged `∀ d` row `UNOURowBA`; the `d = 3` branch (OQ5) is unused. `baEnd_BUnivL_three`/`baThm27L_three` have `UNL32` as the only hypothesis; the (a″) O1 stand-in `rN` is `unNormBARow_holds`.
- Target 5 (new proof, `CV₀ = 3`): twin of `unNormBandRow` at `sz.withLam 0` with `open private` of `NormBand_eig_le`, `_Xentry_le`, `_tail_eventually`, `_subgaussian`, `UNPins_psiI_rowsum`. Entry of `λΨ`: `‖Ψ_xy‖ ≤ 2d` (one entry of the row sum, `Finset.single_le_sum`), `0 ≤ λ ≤ 𝔡⁻¹` from `WO`, so `B = 2N + 2d𝔡⁻¹` and `|λ_i| ≤ N B ≤ N³` once `N ≥ 2 + 2d𝔡⁻¹` (eventually); (a)'s threshold `2 + 𝔡⁻¹` (entry `≤ 1`) is the same argument with a smaller constant, CV₀ unchanged. `NormBand_gvar_le` is not used (the sub-Gaussian lemma suffices).
- Registry (`Test/Axioms.lean`): owed `UNOURowBA`, `UNEMCTE2RowBA`, `UNJakUywRowBA`, `UNNormBARow` deleted (the header comment records it); owner texts of `UNOULLk`, `UNG1Rowk`, `UNNormBound`, `UNClaim417(C)`, `UNQuek`, `UNLocAvgk`, `UNOUQUEk` updated; five structural lines added (`UNQueBAD`, `UNLocAvgBAD`, `UNClaimRowBAD`, `UNJakUywRowBAD`, `UNEMCTE2RowkD`; the ticket's bound is 5). `#assert_rbm_axioms` passes in the full build.

## (c) Verified Mathlib names (all used by the compiled proof of `unNormBARow_holds`, copied from `NormBand.lean`; none invented)
`Finset.single_le_sum`; `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`, `.neg`; `MeasureTheory.measureReal_union_le`, `measure_iUnion_fintype_le`, `measure_mono`; `ENNReal.le_ofReal_iff_toReal_le`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`; `Fintype.card_prod`, `Fintype.card_bool`; `norm_add_le`, `abs_of_nonneg`, `Complex.norm_real`; `Filter.Tendsto.eventually_ge_atTop`. Names verified absent: none searched.

## (d) Open issues, paper-delta candidates
- O1: `UNClaimRowBAD`, `UNJakUywRowBAD` are registered as structural although proved at every filter (`unClaimRowkD`, `jakUywRowkD` at the BA hypotheses); one-line theorems `∀ Dm, UNClaimRowBAD Dm`, `∀ Dm, UNJakUywRowBAD Dm` would leave 3 structural names. Not added: not targets (a″ O2).
- O2: the owed-ledger line `UNG1Rowk` is not found by the scan before or after (already stale on `main`); its owner text was updated and the line kept, as the Registry paragraph words it. It can be deleted by the dispatcher.
- O3 (hub): the branch diff against `main` contains the 1a probe `RBM3D/Probe/T2520Pins.lean` (listed as sole writable, "never merged", no importer); merge the other five files only.
- Closing REQ (vi)/(vii): the two signatures are the first two lines of `extract.py` above; `d > 3` forms are `baEnd_BUnivL_of_ML`, `baThm27L_of_ML` (hypothesis `UNMLOutBA d`) and `baThm27L_any` (hypothesis `STStep5IIIgL d`).
- Paper deltas: none new (`T2520a`: the merged `UNNormBARow` text is the polynomial `N^{CV₀}` form, as proved; its docstring says `‖V‖ ≤ N`, an observation, no statement differs; `T2520b`: `BAThm27L 3` equals the merged text, D723 and the borrowed `UNL32` only).
