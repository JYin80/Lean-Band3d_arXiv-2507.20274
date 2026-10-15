Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 07:05:49 UTC 2026

Targets (mathematics only): option (A) of T2513 is a dimension filter `D : ℕ → Prop`. Each BA-side pin is read only at `d` with `D d ∧ 3 ≤ d`. At `D = (· = 3)` the BA bulk-universality path `UNL32 → BAEnd_BUnivL 3` then uses only `d = 3` inputs. At `D = fun _ => True` the filtered pin is the merged pin.

### (i) Exponent table

There are no analytic exponents in this gate. The table lists the thresholds and constants the probe's hypotheses depend on. Values are recomputed by the script in (ii).

| item | value | constraint | slack |
|---|---|---|---|
| dimension threshold | `3 ≤ d` (all pins) | filtered pins read `∀ d, D d → 3 ≤ d → …` | at `D = (·=3)`: `3 ≤ 3` is equality, nonempty |
| filter `D` | `(· = 3)` (BA), `fun _ => True` (band) | `D 3` true, so the filtered statement is not vacuous | `D=True`: `(∀ d, True → 3 ≤ d → P d) ↔ (∀ d, 3 ≤ d → P d)`; `D=(·=3)`: the statement collapses to `P 3` |
| `(𝔠, 𝔡)` | `(1/6, 1/10)` (`sz0_admissible`, `Defs/Sizes.lean:331`) | `0 < 𝔠`, `0 < 𝔡`, `W ≥ N^𝔠`, `W^{-d/2+𝔡} ≤ ilambda ≤ 𝔡⁻¹` | `d𝔠 = 1/2 < 1`; `𝔡 = 1/10 < d/2 = 3/2`; `n=0`: `N^𝔠 = 11.31 ≤ W = 32`; `W^{-7/5} = 7.8e-3 ≤ ilambda = 1.56e-2 ≤ 10` |
| `ouTauMax 𝔠 𝔡` | `min (min (𝔠/12) (𝔠𝔡/12)) (1/100) = 1/720` (`ZeroModeProfile.lean:78`) | `0 < τ_U ≤ 1/720` (`UNG1Rowk`, `OUInterfaceK:101-105`) | `1/720 < 1/100`; the instance takes `τ_U = ouTauMax`, equality |
| QUE parameters `(ε₀, c, τ)` | `(1/30, 1/60, 1/10)` | `0 < ε₀ < 𝔡/2`, `0 < c < ε₀`, `c < 𝔡/5`, `τ > 0` (`UNQuek`, `PinsK:398-403`) | `ε₀ = 1/30 < 1/20`; `c = 1/60 < 1/30`; `c = 1/60 < 1/50` |
| Jak/Uyw constants | `C = 3 nf + 16`, `c' = 𝔠𝔡/30 = 1/1800`, `τ₀ = min τ₁ (1/4)` (`jakUywRowk`, `EMCTE2BA:629-640`) | `0 < τ₀`; `nf` arbitrary | `nf = 2`: `C = 22` |
| bulk window (BA) | `κ' = κ/2`, `r = (πκ)³/8` (`UNBulkWindowk_ba`, `EMCTE2BA:684`) | `0 < κ'`, `0 < r` | `κ = 1/10`: `κ' = 0.05`, `r = 3.88e-3` |
| `UNL32` arithmetic premises | `σ = min (τ/4) ((1-τ)/3)`, `g = N^{-1+τ/4}`, `G = N^{-σ}`, `t = 1 - exp(-N^{-1+τ})` (`un_L32_arith`, `Pins.lean:307`) | six premises hold iff `N ≥ 1`, `0 < τ < 1`, `N^{τ/2} ≥ 2` (`Pins.lean:307-312`) | `N = 2^21`, `τ = 1/2`: `N^{τ/2} = 32 ≥ 2`; sharp case `N = 2^16`, `τ = 1/8`: `N^{τ/2} = 2` (equality) |

Cross-dimension reads: the quantified inputs `∀ d, UNMLOutBA d`, `UNLocAvgBA`, `UNQueBA`, `UNOUClaimsk`, `UNG1Rowk` and the `hT*` inputs of `g1Rowk_of_inputsG` are applied only at the current `d`. This is the single mathematical fact that makes (A) mechanical. Evidence, with line numbers, from one grep (command below):

```
$ grep -nE "\b(hML|hML'|hT5|hQ|hLoc|hclaims|rO|rJ|rE|rC|rD|rN|rT0|rT|r1|r2b|hprof) +(hML +)?(hLoc +)?(hQ +)?([0-9a-z]+) +(hd|le_rfl)" BA/UNPins.lean BA/EMCTE2BA.lean BA/RandomLayerBGBA.lean Universality/PinsK.lean Universality/OUInterfaceK.lean Universality/GUEPhase/RandomLayerBG.lean   # run in RBM3D/RBM3D; hits below are selected and abbreviated (…), not the full output
BA/UNPins.lean:372:  obtain ⟨δ₀, hδ₀, hδ⟩ := rD d hd 𝔠 𝔡 sz hA κ hκ E hE
BA/UNPins.lean:374:  have hCl := un_claimAll_of_rowsBA rC rE rJ rO hML hLoc hQ d hd 𝔠 𝔡 sz hA κ hκ E hE
BA/UNPins.lean:375:  obtain ⟨CV₀, hCV, hN⟩ := rN d hd 𝔠 𝔡 sz hA
BA/UNPins.lean:378:    (rT0 hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ₀ hδ₀ hbulk) (rT hLoc d hd 𝔠 𝔡 sz hA κ hκ E hE δ₀ hδ₀ hbulk)
Universality/PinsK.lean:462:  obtain ⟨Cn, τ₁, hτ₁, h1⟩ := rE d hd 𝔠 𝔡 sz hA κ hκ E hE nf
Universality/PinsK.lean:502:  filter_upwards [hQ d hd 𝔠 𝔡 sz hA κ hκ (𝔡 / 3) (𝔡 / 6) τQ …
BA/EMCTE2BA.lean:631-632:  intro _hloc hclaims d hd 𝔠 𝔡 sz hadm κ hκ E hE nf / obtain ⟨τ₁, hτ₁, hτ⟩ := hclaims d hd 𝔠 𝔡 sz hadm
Universality/OUInterfaceK.lean:295-298:  intro r1 r2b hML hLoc hQ d hd … / have h1 := r1 hML hLoc hQ d hd … / r2b d hd (hprof d hd) …
Universality/GUEPhase/RandomLayerBG.lean:418, 424: … (hT1 d hd) (hT1' d hd) (hT2 d hd) (hT3 d hd) (hT5 hML d hd) …
BA/RandomLayerBGBA.lean:212: … (fun hML' d hd => ba_mlout d hd (hML' d)) hML hLoc hQ …
```

(Lines `UNPins:1030-1141`, `PinsK:589-646`, `OUInterfaceK:397-463`, `RandomLayerBG:519` are `d = 3` instances or the band `Iff` copies.) Findings for D2:
- No line in the grep applies a `∀ d` input at a dimension other than the current `d` (`d` bound by the theorem's own `∀ d`, or the literal `3` in instances). This is read from the grep text above, not proved by Lean.
- Beyond the ticket's list, the grep adds `UNOUQUEk_zero_of_UNQuek` (`PinsK:494-505`, applies `hQ d hd`, consumed at `UNPins:1207`) and `un_claimAll_of_rowsk` (`PinsK:454-468`). Both are mechanical copies.
- `UNClaimRowk` (`PinsK:442-449`) needs a filtered successor: its antecedent is `∀ d, 3 ≤ d → … UNEMCTE2k ∧ UNJakk ∧ UNUywk`. With a filtered `UNJakUywRowk` that antecedent can only be supplied at `D`-dimensions. The merged proof `unClaimRowk` (`UnivMain:471-478`) applies the antecedent once at its own `d hd …`, so this is also a mechanical copy.
- Rows `UNEMCTE2Rowk`, `UNClaimRowk` read none of `ML`, `Loc`, `Que`. `g1Rowk_of_inputsG` states "`Loc`, `Que` are not used" (`RandomLayerBG:397`). `unJakUywRowBA_holds` states that `UNLocAvgBA` is not used (`EMCTE2BA:763-765`); its proof `jakUywRowk` discards `_hloc`.
- `ML` enters only through `hT5 : ML → ∀ d, 3 ≤ d → RandomLayerB_MLout …` (`RandomLayerBG:412`). Filtered form: `hT5 : ML → ∀ d, D d → 3 ≤ d → …`; the BA instance `fun hML' d hd => ba_mlout d hd (hML' d)` becomes `fun hML' d hD hd => ba_mlout d hd (hML' d hD)`, with `ML := ∀ d, D d → UNMLOutBA d`.
- Other `∀ d` rows of `baBUniv_of_rows` (`UNPins:367-370`: `rD`, `rN`, `rC`, `rE`, `rJ`, `rO`) and the proved `UNCoreC''` (`unCoreC''_holds`, `UnivMain:652`) are applied only at the current `d` (lines 372-378). `rT0`, `rT` take `UNLocAvgBA` and are D5's per-`d` cores (MNO-C3). `UNL32` is `∀ d, 3 ≤ d` (`Pins:281-283`); by its docstring its premises involve only `N`, so it is not a regime-(iii) input. Of `UNL32`'s premises only the six arithmetic ones are computed below; its regularity premises (`IsRegular32`, `IsFreeConv32`) are not computed here.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `D = (· = 3)`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`, `Defs/Sizes.lean:260-263`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`, `(ε₀, c, τ) = (1/30, 1/60, 1/10)`, `τ_U = 1/720`, `nf = 2`; `UNL32` arithmetic at `N = 2^21`, `τ = 1/2`. Every hypothesis of the filtered rows, `ouRowk_of_pins`, `g1Rowk_of_inputsG`, and `baBUniv_of_rows` at `D = (·=3)` that is a number or inequality holds here: `3 ≤ 3`, `D 3`, admissibility (`SizeTendsto`, `Bandwidth`, `WO`), QUE parameter ranges, `τ_U ≤ ouTauMax`, window. The `Iff`s (`D=True` is the merged pin; `D=(·=3)` collapses to `d=3`) are checked on all 64 predicates of `d ∈ {3..8}`. `UNMLOutBA 3` and the BA rows stay hypotheses of the probe (T2511 row b; other gates' pins).

```
$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2513 && python3 -I inst.py
n=0 L=4 W=32 N=2097152 lam=1.562e-02 N^c=11.314 W^(-d/2+dd)=7.813e-03 bandwidth=True WO=True
n=1 L=8 W=1024 N=549755813888 lam=2.441e-04 N^c=90.510 W^(-d/2+dd)=6.104e-05 bandwidth=True WO=True
n=2 L=12 W=7776 N=812479653347328 lam=2.143e-05 N^c=305.470 W^(-d/2+dd)=3.572e-06 bandwidth=True WO=True
n=10 L=44 W=5153632 N=11659991713824860234842112 lam=8.820e-09 N^c=15058.546 W^(-d/2+dd)=4.009e-10 bandwidth=True WO=True
d*c<1: 0.5 True  dd<d/2: True
ouTauMax(1/6,1/10) = 0.001388888888888889 0.001388888888888889 True
QUE: 0<e0<dd/2: True  0<c<e0: True  c<dd/5: True  tau>0: True
Jak/Uyw: C=3nf+16 = 22  c*dd/30 = 0.0005555555555555556 0.0005555555555555556
bulk window: kappa'= 0.05  r=(pi k)^3/8 = 0.003875784585037477
filter checks: Iff at D=True, collapse at D=(.=3), band=>filtered; violations = 0
L32 arith N=2097152 tau=0.5: (0.125, [True, True, True, True, True, True], True)
L32 arith N=65536 tau=0.125: (0.03125, [True, True, True, True, True, True], True)
L32 arith N=1073741824 tau=0.5: (0.125, [True, True, True, True, True, True], True)
ALL_OK True
```

(`inst.py` is a numeric script in the scratchpad; it contains no Lean.) Merged-side numbers: `sz0_values` (`Sizes.lean:267`: `L 0 = 4`, `W 0 = 32`, `size 0 = 2097152`, `lam 0 = 1/64`) agree with the `n = 0` row. The `UNL32` limit computation is `un_L32_arith` (`Pins.lean:307`) with the merged instances `inst_L32_arith_half` (`N = 2097152`, `τ = 1/2`) and `inst_L32_arith_sharp` (`N = 65536`, `τ = 1/8`), both of the same shape as the script rows above.

### Verdicts

- D1 (filter vocabulary; `D` a parameter, `D = True` recovers the merged pin): PASS. The merged texts have no cross-dimension dependence, so the successors are the merged definitions with `D d →` inserted before `3 ≤ d →`.
- D2 (MNO-C2 table): PASS as far as the grep shows. The preflight finds no "uses another dimension" row; the two extra statements `UNOUQUEk_zero_of_UNQuek`, `un_claimAll_of_rowsk` are mechanical. The auditor re-derives the table by compiling the probe.
- D3 (probe): PASS at the mathematical level. Every hypothesis of the filtered `baBUniv_of_rows` at `D = (·=3)` holds at the instance. The conclusion `BAEnd_BUnivL 3` needs `UNL32` plus `d = 3` inputs (`UNMLOutBA 3`, filtered `UNLocAvgBA`/`UNQueBA`, the rows applied at `d = 3`). The Lean proof is for stage 1b.
- D4 (price and placement): no mathematical obstruction. The price is not estimated in section (a) (rule: no size estimates).
- D5 (per-`d` cores `∀ d, 3 ≤ d → UNLocAvg d → TrLocal d`): PASS. `rT0`, `rT` are applied as `rT hLoc d hd …` at the current `d` (`UNPins:378`), so the merged `∀ d` texts follow from the per-`d` core by one `intro`. Their `D = (·=3)` forms follow by `d = 3`.
- D6 (final signatures): PASS. No `STStep5IIIgL`: `UNMLOutBA 3` is unconditional (`T2511-check:209-210`) and `STStep5IIIgL d` appears only in `T2511_AnyD` for general `d` (`:213-215`).

Overall: PASS

## (a′) Preflight corrections — Thu Oct 15 08:06:24 UTC 2026
- (ii) The instance data of (a) are `sz0`, `κ = 1/10`, `E`; they check the numeric premises. The premise `∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E` (`ρ_N(E) ≥ κ`) of `BAEnd_BUnivL` and of every filtered row is not a number or an inequality, and (a) does not claim it at `sz0`. The merged witness exists only for the class sequence `S0` of `BA/UNPins.lean` §8 (`S0_adm`, `S0_bulk`: `(L, g) = (4, 3/10)`, `κ_* = Im m₀/π`, `E_*`). The six compiled instances (probe :322, :330, :345, :361, :370, :381) therefore use `S0` at `(𝔠, 𝔡) = (1/6, 1/10)`, `k = 1`, `E' = 0`, `𝒪 = bump`. The exponent facts of (a) (`(1/6, 1/10)`, `ouTauMax = 1/720`, QUE ranges, `UNL32` arithmetic) do not depend on this choice; no verdict changes.
- (i), last bullet: (a) says `UNL32` is not a regime-(iii) input "by its docstring". A docstring is not evidence (CLAUDE.md §5.7). The Lean fact is: `UNL32` (`Pins.lean:281`) is the registered borrowed premise (`Test/Axioms.lean:91-93`, `borrowedProps`), and closing condition (vi) allows it as the single external hypothesis; the probe assembly takes it as `h32 : UNL32` and nothing else of that kind. No verdict changes.

## (b) Script output (report-only design ticket: the deliverables are `docs/reports/T2513-design.md`, 205 lines, and the probe `RBM3D/Probe/T2513Pins.lean`, 392 lines, branch only)
Branch `t/T2513` (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2513`). The design report has the further scripts in its section 0 (`statdiff.py`, `d2use.py`, `d2place.py`, `price.py`, `scan_probe.lean`, `cite_lines.py`: 125 citations, 0 mismatches). The block below is `prove_b.sh` (scratchpad `T2513/`), verbatim; the linter note in the build tail is a replayed warning of an imported module (warning/error lines in the probe file: 0, design report section 0).
```
$ git log --oneline main..t/T2513   # cwd = /Users/junyin/Lean_proof/RBM3D-wt/T2513
a6d9966e T2513: probe instances for the filtered chain theorems (392 lines), design report numbers
f5c42393 T2513: design report, rule C1 row
625829eb T2513: design report (MN-D3, option (A)) and probe comment (T2449 line range)
12427b16 T2513: probe docstring (no regime-(iii) token)
f80552ec T2513: probe (MN-D3 option (A): filtered pins, chain, per-d cores, BA assembly at d = 3, instances)
$ lake build RBM3D.Probe.T2513Pins 2>&1 | tail -3

Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (4190 jobs).
$ wc -l RBM3D/Probe/T2513Pins.lean docs/reports/T2513-design.md
392 RBM3D/Probe/T2513Pins.lean
205 docs/reports/T2513-design.md
597 total
$ lake env lean docs/tickets/checks/T2513-check.lean; echo exit=$?   # the check (acceptance)
exit=0 (output lines 85, lines containing 'error': 0)
$ #print axioms of every probe theorem (scratch file: import RBM3D.Probe.T2513Pins, one #print axioms per theorem)
T2513_UNQuekD_true : [propext, Classical.choice, Quot.sound]
T2513_UNLocAvgkD_true : [propext, Classical.choice, Quot.sound]
T2513_UNOUClaimskD_true : [propext, Classical.choice, Quot.sound]
T2513_UNOURowkD_true : [propext, Classical.choice, Quot.sound]
T2513_UNEMCTE2RowkD_true : [propext, Classical.choice, Quot.sound]
T2513_UNJakUywRowkD_true : [propext, Classical.choice, Quot.sound]
T2513_UNClaimRowkD_true : [propext, Classical.choice, Quot.sound]
T2513_UNG1RowkD_true : [propext, Classical.choice, Quot.sound]
T2513_band_locAvg : [propext, Classical.choice, Quot.sound]
T2513_band_ouRow : [propext, Classical.choice, Quot.sound]
T2513_un_claimAll_of_rowskD : [propext, Classical.choice, Quot.sound]
T2513_unClaimRowkD : [propext, Classical.choice, Quot.sound]
T2513_jakUywRowkD : [propext, Classical.choice, Quot.sound]
T2513_ouRowk_of_pinsD : [propext, Classical.choice, Quot.sound]
T2513_g1Rowk_of_inputsGD : [propext, Classical.choice, Quot.sound]
T2513_locAvg_core : [propext, Classical.choice, Quot.sound]
T2513_UNLocAvgBA_of_BAEnd_locSCL : [propext, Classical.choice, Quot.sound]
T2513_que_core : [propext, Classical.choice, Quot.sound]
T2513_UNQueBA_of_BAEnd_QUEL : [propext, Classical.choice, Quot.sound]
T2513_UNTrLocalBARow_of_core : [propext, Classical.choice, Quot.sound]
T2513_UNTrLocalInitBARow'_of_core : [propext, Classical.choice, Quot.sound]
T2513_un_claimAll_of_rowsBAD : [propext, Classical.choice, Quot.sound]
T2513_baBUniv_of_rowsD : [propext, Classical.choice, Quot.sound]
T2513_n2_three : [propext, Classical.choice, Quot.sound]
$ lake env lean band_axioms.lean   # band terminal and bUniv_holds, on t/T2513
band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
bUniv_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ python3 -I extract_targets.py    # statements of the targets, extracted from the probe (the eight pins: first line only)
:38  def T2513_UNQuekD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
:45  def T2513_UNLocAvgkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
:55  def T2513_UNOUClaimskD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
:59  def T2513_UNOURowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (ML Loc Que : Prop) : Prop :=
:62  def T2513_UNEMCTE2RowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
:67  def T2513_UNJakUywRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (Loc : Prop) : Prop :=
:73  def T2513_UNClaimRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : Prop :=
:82  def T2513_UNG1RowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop) : Prop :=
--
:120  theorem T2513_un_claimAll_of_rowskD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) {ML Loc Que : Prop}
:121      (rC : T2513_UNClaimRowkD Dm K) (rE : T2513_UNEMCTE2RowkD Dm K) (rJ : T2513_UNJakUywRowkD Dm K Loc)
:122      (rO : T2513_UNOURowkD Dm K ML Loc Que) (hML : ML) (hLoc : Loc) (hQ : Que) :
:123      ∀ d : ℕ, Dm d → 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
:124        ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAllC sz ((K d).M sz) E := by
:134  theorem T2513_unClaimRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) : T2513_UNClaimRowkD Dm K := by
:142  theorem T2513_jakUywRowkD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (hbw : UNBulkWindowk K) (hbb : UNBadBoundk K)
:143      (hbb2 : UNBad2Boundk K) (Loc : Prop) : T2513_UNJakUywRowkD Dm K Loc := by
:152  theorem T2513_ouRowk_of_pinsD (Dm : ℕ → Prop) (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) {ML Loc Que : Prop}
:153      (hprof : ∀ d : ℕ, Dm d → 3 ≤ d → UNOUProfRowk (K d) (P d)) :
:154      T2513_UNG1RowkD Dm K P ML Loc Que → UNG2bRowk K P → T2513_UNOURowkD Dm K ML Loc Que := by
:160  theorem T2513_g1Rowk_of_inputsGD (Dm : ℕ → Prop) :
:161      ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop)
:162        (Ed : ∀ d : ℕ, ℝ → Sizes d → ℕ → ℂ → Prop) (fE fT : ∀ d : ℕ, Sizes d → ℕ → ℂ → ℝ)
:163        (Fl : ∀ d : ℕ, Sizes d → ℝ → ℝ → ℝ → ℝ → (ℕ → ℂ) → Prop)
:164        (MO : ∀ d : ℕ, Sizes d → (ℕ → ℂ) → (ℕ → ℝ) → Prop)
:165        (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) →
:166          (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop),
:167        (∀ d, Dm d → 3 ≤ d → RBG_Flow (K d) (Ed d) (fT d)) →
:168        (∀ d, Dm d → 3 ≤ d → RBG_Dom (K d) (Fl d)) →
:169        (∀ d, Dm d → 3 ≤ d → RBG_Comp (K d) (P d)) →
:170        (∀ d, Dm d → 3 ≤ d → RBG_Prod (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
:171        (∀ d, Dm d → 3 ≤ d → RandomLayerB_LL (K d) (fE d) (fT d) (PB d)) →
:172        (∀ d, Dm d → 3 ≤ d → RBG_Que (K d) (P d) (Ed d) (fE d) (fT d) (MO d) (KF d) (PB d)) →
:173        (ML → ∀ d, Dm d → 3 ≤ d → RandomLayerB_MLout (fT d) (Fl d) (MO d)) →
:174        T2513_UNG1RowkD Dm K P ML Loc Que := by
:221  theorem T2513_locAvg_core (d : ℕ) (h : T2513_BAEnd_locSCL d) : T2513_UNLocAvgBAD (· = d) := by
:235  theorem T2513_que_core (d : ℕ) (h : BAEnd_QUEL d) : T2513_UNQueBAD (· = d) := by
:252  theorem T2513_UNTrLocalBARow_of_core (h : T2513_TrLocalCore) : UNTrLocalBARow :=
:254  theorem T2513_UNTrLocalInitBARow'_of_core (h : T2513_TrLocalInitCore) : UNTrLocalInitBARow' :=
:273  theorem T2513_baBUniv_of_rowsD (Dm : ℕ → Prop) (hcore : UNCoreC'') (h32 : UNL32) (hGL : UNGUELocal)
:274      (hGC : UNGreenCorrAllC) (rD : UNDensBARow') (rT0 : T2513_TrLocalCore) (rT : T2513_TrLocalInitCore)
:275      (rN : UNNormBARow) (rC : T2513_UNClaimRowBAD Dm) (rE : T2513_UNEMCTE2RowBAD Dm) (rJ : T2513_UNJakUywRowBAD Dm)
:276      (rO : T2513_UNOURowBAD Dm) (hML : ∀ d : ℕ, Dm d → UNMLOutBA d) (hLoc : T2513_UNLocAvgBAD Dm)
:277      (hQ : T2513_UNQueBAD Dm) (d : ℕ) (hD : Dm d) : BAEnd_BUnivL d := by
:294  theorem T2513_n2_three (P : ∀ d, UNOUProfile (UNKind.ba d))
:295      (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop)
:296      (h32 : UNL32) (hML : UNMLOutBA 3) (hLocB : T2513_BAEnd_locSCL 3) (hQueB : BAEnd_QUEL 3)
:297      (rT0 : T2513_TrLocalCore) (rT : T2513_TrLocalInitCore) (rN : UNNormBARow)
:298      (hProf : UNOUProfRowk (UNKind.ba 3) (P 3)) (hPC : RBG_ProfComp (UNKind.ba 3) (P 3))
:299      (hProd : RBG_Prod (BAEd 3) (BAfE 3) (BAfT 3) (BAMO 3) (KF 3) (PB 3))
:300      (hLL : RandomLayerB_LL (UNKind.ba 3) (BAfE 3) (BAfT 3) (PB 3))
:301      (hQue : RBG_Que (UNKind.ba 3) (P 3) (BAEd 3) (BAfE 3) (BAfT 3) (BAMO 3) (KF 3) (PB 3)) : BAEnd_BUnivL 3 := by
$ sed -n 321,342p RBM3D/Probe/T2513Pins.lean   # the first two of the six compiled nonempty instances (d = 3, class sequence S0)
/-- `T2513_un_claimAll_of_rowsBAD` at `Dm = (· = 3)`: `UNClaimAllC` of the BA model at `E_*` from the rows at `d = 3`. -/
example (rJ : T2513_UNJakUywRowBAD (· = 3)) (rO : T2513_UNOURowBAD (· = 3)) (hML : UNMLOutBA 3)
    (hLoc : T2513_UNLocAvgBAD (· = 3)) (hQ : T2513_UNQueBAD (· = 3)) :
    UNClaimAllC S0 (UNModelC.ba S0) (fp 4 UNPins_hg_3_10).E :=
  T2513_un_claimAll_of_rowsBAD (· = 3) (T2513_unClaimRowkD _ _) (fun d _ hd => unEMCTE2RowBA_holds d hd) rJ rO
    (fun d h => h ▸ hML) hLoc hQ 3 rfl le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 UNPins_hg_3_10)
    (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk

/-- `T2513_n2_three` at the class sequence: `UNUnivDilAt` of `UNModel.ba S0`; only the pins of other gates are hypotheses. -/
example (P : ∀ d, UNOUProfile (UNKind.ba d))
    (KF PB : ∀ d : ℕ, ∀ sz : Sizes d, (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → (∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) → Prop)
    (h32 : UNL32) (hML : UNMLOutBA 3) (hLocB : T2513_BAEnd_locSCL 3) (hQueB : BAEnd_QUEL 3)
    (rT0 : T2513_TrLocalCore) (rT : T2513_TrLocalInitCore) (rN : UNNormBARow)
    (hProf : UNOUProfRowk (UNKind.ba 3) (P 3)) (hPC : RBG_ProfComp (UNKind.ba 3) (P 3))
    (hProd : RBG_Prod (BAEd 3) (BAfE 3) (BAfT 3) (BAMO 3) (KF 3) (PB 3))
    (hLL : RandomLayerB_LL (UNKind.ba 3) (BAfE 3) (BAfT 3) (PB 3))
    (hQue : RBG_Que (UNKind.ba 3) (P 3) (BAEd 3) (BAfE 3) (BAfT 3) (BAMO 3) (KF 3) (PB 3)) :
    UNUnivDilAt S0 (UNModel.ba S0) (fun n => BArho 3 (S0.L n) (S0.lam n) (fp 4 UNPins_hg_3_10).E)
      (fp 4 UNPins_hg_3_10).E 0 1 (UNInst.bump : (Fin 1 → ℝ) → ℝ) :=
  T2513_n2_three P KF PB h32 hML hLocB hQueB rT0 rT rN hProf hPC hProd hLL hQue le_rfl (1 / 6) (1 / 10) S0 S0_adm 1
    le_rfl (clsκ 4 UNPins_hg_3_10) (clsκ_pos 4 UNPins_hg_3_10) (fp 4 UNPins_hg_3_10).E S0_bulk 0 (by norm_num)
    UNInst.bump UNInst.bump_testFun
$ grep -n '^/-- `T2513_\(g1Rowk\|ouRowk\|baBUniv\|jakUyw\)' RBM3D/Probe/T2513Pins.lean | cut -c1-170   # the docstrings of the other four instances (:344-387; each is an example applying the theorem at S0)
344:/-- `T2513_g1Rowk_of_inputsGD` at `Dm = (· = 3)` and the BA kind (the filtered twin of the example at `RandomLayerBGBA:201`). -/
360:/-- `T2513_ouRowk_of_pinsD` at `Dm = (· = 3)`: the `𝐇_t` claims of the BA kind at `S0` from the layer pin and the profile pin. -/
369:/-- `T2513_baBUniv_of_rowsD` at `Dm = (· = 3)`: the filtered BA rows and the `d = 3` forms of `hML`, `hLoc`, `hQ` are hypotheses. -/
380:/-- `T2513_jakUywRowkD` at `Dm = (· = 3)`, the BA kind, `S0`, `κ_*`, `E_*`, `n_f = 2`. -/
$ grep -rn 'T2513_' RBM3D | grep -v Probe/T2513Pins.lean | wc -l   -> 0
$ git grep -l T2513_ over every refs/heads/t/* except t/T2513 (RBM3D/)   -> 0 files
$ grep -rnE '\b(UNQuekD|UNLocAvgkD|UNOUClaimskD|UNOURowkD|UNEMCTE2RowkD|UNJakUywRowkD|UNClaimRowkD|UNG1RowkD|UNLocAvgBAD|UNQueBAD|UNOURowBAD|UNEMCTE2RowBAD|UNJakUywRowBAD|UNClaimRowBAD|un_claimAll_of_rowskD|unClaimRowkD|jakUywRowkD|ouRowk_of_pinsD|g1Rowk_of_inputsGD|baBUniv_of_rowsD|un_claimAll_of_rowsBAD)\b' RBM3D | grep -v Probe/ | wc -l   # the proposed final names (probe names without T2513_)   -> 0
$ git grep -nE '\b(UNQuekD|UNLocAvgkD|UNOUClaimskD|UNOURowkD|UNEMCTE2RowkD|UNJakUywRowkD|UNClaimRowkD|UNG1RowkD|UNLocAvgBAD|UNQueBAD|UNOURowBAD|UNEMCTE2RowBAD|UNJakUywRowBAD|UNClaimRowBAD|un_claimAll_of_rowskD|unClaimRowkD|jakUywRowkD|ouRowk_of_pinsD|g1Rowk_of_inputsGD|baBUniv_of_rowsD|un_claimAll_of_rowsBAD)\b' over every refs/heads/t/* (RBM3D/, minus Probe/), files   -> 0
$ grep -nE 'import RBM[12]D|RBM[12]D' RBM3D/Probe/T2513Pins.lean | wc -l   # imports or paths of the sister projects in the probe   -> 0
```
Ports: none from `../RBM1D` or `../RBM2D` (the last grep above: 0; no `git diff --stat` against them is needed). Copied texts: (i) the merged RBM3D declarations `UNQuek`, `UNLocAvgk`, `UNOUClaimsk`, `UNOURowk`, `UNEMCTE2Rowk`, `UNJakUywRowk`, `UNClaimRowk`, `UNG1Rowk`, `un_claimAll_of_rowsk`, `unClaimRowk`, `jakUywRowk`, `ouRowk_of_pins`, `g1Rowk_of_inputsG`, with the filter `Dm` added (design report section 0, `statdiff.py`: 13 of 13 identical after deleting the filter); (ii) from the unmerged T2449 probe (`t/T2449:RBM3D/Probe/T2449Pins.lean`, commit 921369b2, read with `git show`): `BAGz` :158, `BAMz` :161, `BAendDom` :169, `BAlocBad1z` :172, `BAlocBad2z` :176, `BAEnd_locSCL` :192 under the prefix `T2513_` (probe :195-215), and the proof of `UNLocAvgBA_of_BAEnd_locSCL` (:220-229) as `T2513_locAvg_core`.
Narrative:
- The probe has six sections: the eight filtered pins (:38-86); the band `Iff`s at `Dm = fun _ => True` (:91-116); the filtered chain `un_claimAll_of_rowskD`, `unClaimRowkD`, `jakUywRowkD`, `ouRowk_of_pinsD`, `g1Rowk_of_inputsGD` (:120-188); the per-`d` cores and bridges of D5 with the unmerged `BAEnd_locSCL` (:195-255); the BA readings, `T2513_baBUniv_of_rowsD` and `T2513_n2_three` (:260-313); six instances at the class sequence `S0` (:322-387).
- Every merged proof copied into the probe is the merged proof with the filter hypothesis threaded through: 13 of 13 texts are identical to the merged text after deleting the filter (design report section 0). This is the evidence for "per-`d`: mechanical copy" in D2: the filtered proof can only use an input at a dimension `d'` with `Dm d'`, and it compiles with `Dm d` for its own `d` only.
- `T2513_n2_three` concludes `BAEnd_BUnivL 3` from `UNL32` and the `d = 3` pins of V, M1, M1 b, M3, N2, C3, C5; the proved leaves are discharged inside it. No hypothesis is a `∀ d` form of `UNMLOutBA`, `UNLocAvgBA`, `UNQueBA`, and `STStep5IIIgL` does not occur (grep 0). So no D2 "uses another dimension" row exists, and (B) need not go to Jun.
- No merged file is edited; the probe is never merged; `band_terminal` and `bUniv_holds` print the standard axioms on `t/T2513`.
- Price and placement (design report §4): implementation central 469 lines, calibrated 479-626; N2 plus implementation 700-920 (hi-case 1,189) against the stop line 1,950; inside N2; the vocabulary file G1 must precede its first consumer (options α, β, γ for the dispatcher).
- No stop rule of the ticket fired (probe 392 ≤ 400, report 205 ≤ 250, no merged file changed, no hypothesis beyond `UNL32` and `d = 3` inputs).

## (c) Verified Mathlib names used (resolved by `#check` through the probe's imports, scratchpad `T2513/names.lean`)
- `le_min_iff` (`c ≤ min a b ↔ c ≤ a ∧ c ≤ b`)
- `lt_min`
- `min_le_left`, `min_le_right`
- `MeasureTheory.measure_mono`
- `Real.rpow_pos_of_pos`
- `Iff.trans`
- `Filter.Eventually.mono`
- `lt_of_lt_of_le`, `le_trans`
- Names verified absent: the proposed final names of the filtered pins and theorems (probe names without `T2513_`) do not exist in `RBM3D/` nor in any `refs/heads/t/*` (section (b), name-clash greps: 0 and 0); no Mathlib name was searched for and found missing.

## (d) Open issues and paper-delta candidates
- Paper-delta candidates: none. D723 (BA Thm 2.7 at `d = 3` only, DECISIONS §316) covers the restriction; the filter is Lean-internal (no `T2513a`).
- For the dispatcher (design report §4): where G1 (the vocabulary file, 176-227 calibrated lines) goes. M1 row a (T2514) is released; G1 is read first by M1's `d = 3` bridge, M1 row b's cores and M3's bridge. Options α (first file of M1 row b), β (small own row, forecast ≈ 13), γ (explicit body in M1 b and M3, G1 in N2).
- Registry (design report §1): the scan on the probe lists 8 assumed-and-unconcluded `Prop`s; G1, G2 and N2 add at most 5 structural lines; the owner comments of `UNLocAvgBA` (`Test/Axioms.lean:178`) and `UNOURowBA` (:179) are rewritten for closing condition (vii).
- `T2513_BAEnd_locSCL` copies unmerged T2449 text: re-check against `BA/MAPins` when M1 row a merges. `hML : UNMLOutBA 3` has the exact type of the merged `unMLOutBA_three` (`BA/MainIndTermBA.lean:47`, merged c536c603 after the branch point).
- The texts of D1 become binding only after the 1a-audit; the probe stays on `t/T2513` and is not merged (only `docs/reports/T2513-design.md` is).
- Preflight correction: (a′) above.
