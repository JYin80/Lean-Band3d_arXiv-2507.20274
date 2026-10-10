Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 22:08:25 UTC 2026

Scope: pins only (Props and `Iff.rfl` bridges); no estimate is proved here. Ticket lines (i)-(iv) are rows 1-4 of the table.

### (i) Exponent table

Exponents and constants the pins carry, copied from `Graph/LWPins.lean:240-311` and `Chain/Step2Gen.lean:441-483`: they must be
reproduced unchanged over the carrier (G1 of the ticket: `Iff.rfl` fails if one differs).

| # | quantity | value | constraint | slack / status |
|---|---|---|---|---|
| a | `LWtermG` bound | `η⁻¹ Φ(0) Φ(|a-b|)²` | equals `LWterm` (`LWPins:240`) | defeq, `Iff.rfl` |
| b | `LWtermExpG` bound | `η⁻¹ B^{1/2} (W^d)⁻¹ 𝒯̃` | equals `LWtermExp` (`LWPins:290`) | defeq |
| c | `LWtermEXPG` bound | `(1-t)⁻¹ B^{5/2}` on `lam²/L^d ≤ 1-t` | equals `LWtermEXP` (`LWPins:311`) | defeq |
| d | `ℓ ≤ (log W)^10 ellT` | 10 | `LWAssmExp` (`LWPins:283`); `STLWTgL` (`Step2Gen:453`) | same 10; at `n=0`: `(log 32)^10 = 2.50e5`, `ℓ = 0` |
| e | `3 ≤ d` premise | `LWterm*G` have it, `STLWBgL`/`STLWTgL` do not | band `STLWB d`/`STLWT d` have none (`Step2Defs:406,421`) | `BASTLWB d`, `BASTLWT d` provable only at `3 ≤ d` (as band, `Test/Axioms.lean:366-367`); instances at `d = 3` |
| f | window `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` | `d = 3`, `ε₀ = 1/10` | `Ψ = W^{-1/2}` | `W^{-1.5} < W^{-0.5} < W^{-0.1}`; ratios `W^{-1}`, `W^{-0.4}` (script below) |
| g | flow data | `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6` | `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`FlowPins:1214`) | merged theorem |
| h | horizon | `t ≡ 1/2` | `t ≤ BAflowT0`; `t0_sz0 : 2/3 ≤ BAflowT0` (`FlowPins:1227`), `half_lt_t0` (`:1254`) | slack `1/6` |
| i | EXP size set | `lam²/L^d ≤ 1-t` | `n = 0`: `3.81e-6 ≤ 0.5` | slack `0.5` |
| j | stop line | 600 lines (`wc -l` of both files) | plan below | row 4 |

**Row 1: name list against `Chain/Step2Gen` (grep, `Step2Gen`, `Carrier`, `FlowPins`, `LWPins`; whole tree minus `Probe/`: all 0 hits for the new names).**
Reading of the ticket: the ten names after "minus ... (L2):" (`LWcutg` ... `LWtermEXPG`) are **not** in `Step2Gen` (0 hits below); they are the new content of `LWGen`. The names `Step2Gen` has are the second list.

| probe name | decision | reason |
|---|---|---|
| `FlowFM.msig` | drop; inline `if σ then C.m n else (starRingEnd ℂ) (C.m n)` | `STmsigg` (`Step2Gen:156`) takes `Cm : Step2Mat sz`, not `FlowFM sz`; `Step2Gen` `STEGtg` (`:257-262`) inlines the same `if` and `bandFM_STEGt` (`:278`) is `rfl`, so no `FlowFM`-level copy is needed |
| `LWcutg LWEg LWAvgLawgL LWLoop2gL LWAssmgL LWLoopExpgL LWAssmExpgL LWtermG LWtermExpG LWtermEXPG` | keep (probe 48-56, 63-91, 99-141) | not in `Step2Gen` |
| `PinFam bandPin` / `baPin` | keep in `LWGen` / `LWPinsBA` | new; `baPin` has the shape of `BAStep2` (`FlowPins:432`) |
| `STEGtg`, `STLWassmgL` | drop | `Step2Gen:257`, `:265` |
| `STLWBG`, `STLWTG` | drop; use `STLWBgL` (`:441`), `STLWTgL` (`:453`) | same shape `(d law Flow mk T0)`, as `bandFM_STLWB` (`:521`) |
| `STEMn2ExpG`, `band_STEMn2ExpG`, `STEMn2Exp_iff`, `BASTEMn2Exp` | drop | `STEMn2ExpgL` (`:483`); row T2-BA |
| `band_STEGt`, `band_STLWassm`, `STLWB_iff`, `STLWT_iff` | drop | `bandFM_STEGt` (`:278`), `bandFM_STLWassm` (`:280`), `bandFM_STLWB` (`:521`), `bandFM_STLWT` (`:524`) |

```
$ grep -nE "^(def|theorem) (STmsigg|STEGtg|STLWassmgL|STLWBgL|STLWTgL|STEMn2ExpgL|bandFM_STEGt|bandFM_STLWassm|bandFM_STLWB|bandFM_STLWT|bandFM_STEMn2Exp)\b" RBM3D/Chain/Step2Gen.lean   (names only)
156 STmsigg   257 STEGtg   265 STLWassmgL   278 bandFM_STEGt   280 bandFM_STLWassm   441 STLWBgL
453 STLWTgL   483 STEMn2ExpgL   521 bandFM_STLWB   524 bandFM_STLWT   530 bandFM_STEMn2Exp
$ bash names.sh   (grep -rnw RBM3D RBM3D.lean, minus RBM3D/Probe; 37 names: the ten, PinFam bandPin baPin, band_LWE band_LWAvgLaw band_LWAssm band_LWAssmExp, the three *_iff, the three band_LW*G, BALWterm BALWtermExp BALWtermEXP BASTLWB BASTLWT, FlowFM.msig, STLWBG STLWTG band_STLWBgL band_STLWTgL LWGen LWPinsBA, ...)
every name: 0
```

**Row 2: import check.** `Chain/LWGen` imports `Chain.Step2Gen`, `Graph.LWPins` only. `closure.py` follows `import RBM3D.*` lines through the files.

```
$ python3 -I closure.py LWGen RBM3D.Chain.Step2Gen RBM3D.Graph.LWPins
LWGen closure size 69
forbidden in closure: []     (forbidden = Graph.LWTermHolds|LWExpTerm*|LWMoment*|AuxGraph*|*Step2Events|*Step2Iterate)
RBM3D.Induction.Step2Events False
$ python3 -I closure.py LWPinsBA RBM3D.Chain.Step2Gen RBM3D.Graph.LWPins RBM3D.Graph.LWTermHolds RBM3D.Graph.LWExpTerm6 RBM3D.BA.FlowPins
LWPinsBA closure size 227     (downstream by design: contains LWTermHolds, LWExpTerm6, Induction.Step2Events, so STLWB_of_LWterm is in scope)
```
`Chain/LWGen.lean` does not exist and no merged file imports it, so no cycle. `Chain/Step2Gen` does not import `Graph/LWPins` (imports: `Chain.Carrier`, `Induction.Step2Defs`).

**Row 3: bridge kinds.** All `Iff.rfl` / `rfl` (probe `t/T2387:RBM3D/Probe/T2387Pins.lean:208-226` compiled at its base: design `T2387-design.md:119`; `Step2Gen` bridges `bandFM_*` are the same shape and merged).

| bridge | kind | unfolding |
|---|---|---|
| `band_LWE : LWE sz n (E n) t σ a ω = LWEg (bandFM sz E) n t σ a ω` | `rfl` | `bandFM.S = SB`, `bandFM.m n = mE (E n)`, `mSigma = if σ then mE else conj mE` |
| `band_LWAvgLaw`, `band_LWAssm`, `band_LWAssmExp` | `Iff.rfl` | law `seqP sz`, carrier `bandFM sz E` |
| `LWterm_iff`, `LWtermExp_iff`, `LWtermEXP_iff` : `LWx d ↔ bandPin LWxG d` | `Iff.rfl` | `bandPin P d = P d seqP STFlow (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))`; EXP premises are `STLocalEntrygL` etc. (`Carrier`), `Iff.rfl` to the band ones (`FlowPins:333-343`) |
| `STLWBgL`, `STLWTgL` at band | `bandFM_STLWB d`, `bandFM_STLWT d` (merged `Iff.rfl`) | `bandPin STLWBgL d` unfolds to the right side of `bandFM_STLWB` |

Band instances (theorems, no hypothesis): `band_LWtermG := (LWterm_iff 3).1 (lwterm_holds 3)` (`LWTermHolds:682`); `band_LWtermExpG` from `lwtermExp_holds 3` (`:1604`); `band_LWtermEXPG` from `lwTermEXP_holds 3` (`LWExpTerm6:620`); `band_STLWBgL := (bandFM_STLWB 3).1 (STLWB_of_LWterm (by norm_num) (lwterm_holds 3))`; `band_STLWTgL := (bandFM_STLWT 3).1 (STLWT_of_LWtermExp (by norm_num) (lwtermExp_holds 3))` (`Step2Events:1355,1427`, `hd : 3 ≤ d`). Exact BA form: `abbrev BASTLWB : ℕ → Prop := baPin STLWBgL`, `abbrev BASTLWT := baPin STLWTgL`, with `PinFam` the `(d law Flow mk T0)` shape of `STStep2G`; `BAStep2 d := STStep2G d (seqP (sz.withLam 0)) BAFlow baFMz BAflowT0` (`FlowPins:432`) is `baPin STStep2G d`.

**Row 4: plan against the stop line 600** (line counts of the probe ranges to keep, by `sed -n a,bp | wc -l`):

| file | content | lines |
|---|---|---|
| `Chain/LWGen` | header, imports, doc, opens (about 40); `LWcutg LWEg` 9; `LWAvgLawgL ... LWAssmExpgL` 29; three pins 43; `PinFam bandPin` 7; bridges 11 + 3; section lines 8 | about 150-170 |
| `BA/LWPinsBA` | header (about 35); `baPin` 3; five abbrevs 5; five band instances about 10; `Ψ0`, `Ψ0_window`, `ell0` (`private`) 10; examples about 25 | about 90-110 |
| total | | about 250-290 (ticket 200 / 300 / 450) |

Slack to the stop line: about 310 lines. Registry (`Test/Axioms.lean:423`, `scanPremises`): a `Prop`-valued `defnInfo` (an `abbrev` is one) enters the scan only if a **theorem** has it in a binder type and no theorem concludes it. The new theorems have only `ℕ`/`Sizes`/`ℝ`/`Fin` binders and conclusions `bandPin ...` or `↔`; `example`s are not environment declarations. Predicted: no owed line needed now; owed lines are for the first theorem that takes `BALWterm d` etc. as a hypothesis (later rows). The 1b runs the pre-check to confirm.

### (ii) One concrete nondegenerate instance (`d = 3`)

Data: merged `sz0` (`Defs/Sizes.lean:260`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), flow `flow_sz0`, `t ≡ 1/2`, `ε₀ = 1/10`, `Ψ_n = W_n^{-1/2}`, `ℓ ≡ 0`, `D = 1`. All hypotheses below are deterministic; the stochastic ones (`STInitialGT2gL`, `LWLoopExpgL`, `STLWassmExpgL`, `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL`) are hypotheses of the example (other gates' pins), as in probe 369-387.

```
$ python3 -I inst.py        (n = 0..5000; exact integers/fractions, logs for the window)
failures over n=0..5000: []     (checked: Bandwidth N <= W^6 (𝔠=1/6); WO lower W^{7} >= (m^6)^5 i.e. W^{-1.4} <= lam; window; lam^2/L^d <= 1-t; ell range)
n=0: L,W,lam,N = 4 32 1/64 2097152
n=0: W^-1.5, Psi=W^-0.5, W^-0.1 = 0.005524271728019903 0.1767766952966369 0.7071067811865475
n=0: W^-1.4 <= lam <= 10 : 0.007812500000000002 0.015625
n=0: lam^2/L^d = 3.814697265625e-06 <= 1-t = 0.5
n=0: (log W)^10 = 250008.4305621398
n=10: W^-1.5/Psi = W^-1 = 1.940e-07 ; Psi/W^-0.1 = W^-0.4 = 2.066e-03
n=1000: W^-1.5/Psi = W^-1 = 3.109e-17 ; Psi/W^-0.1 = W^-0.4 = 2.495e-07
n=100000: W^-1.5/Psi = W^-1 = 3.125e-27 ; Psi/W^-0.1 = W^-0.4 = 2.500e-11
```

Hypotheses of `BALWtermExp 3` (the first of `LWtermExpG` unfolded): `3 ≤ 3`; `κ = 1/2, ε = 𝔡 = 1/10 > 0`; `BAFlow sz0 κ ε 𝔠 𝔡 zSeq` (`flow_sz0`); `0 ≤ t`, `t ≤ BAflowT0` (`half_lt_t0`: `1/2 < BAflowT0 sz0 zSeq n`); `0 < ε₀`; `LWWindow` (window above, holds for every `n`, hence eventually); `∀ n, 0 ≤ ℓ n`; `ℓ n ≤ (log W)^10 ellT` (`0 ≤ ...` since `ellT ≥ 1`, `one_le_ellT`); `D = 1 > 0`. For `BALWtermEXP 3`: `lam²/L^d ≤ 1-t` on the index set (row i). The data lie in the three limits the pins need: `W_n → ∞` (`sz0_tendsto`), `Ψ_n/W_n^{-1/10} = W_n^{-2/5} → 0`, `W_n^{-3/2}/Ψ_n = W_n^{-1} → 0` (the window's two sides hold with room, so nothing relies on a large witness: the `n = 0` row already satisfies them). External hypotheses: none (`BALW*` are owed pins of BA-L6, not external inputs).

Targets for the instance (1b): `band_LWtermG`, `band_LWtermExpG`, `band_LWtermEXPG`, `band_STLWBgL`, `band_STLWTgL` (theorems; `#print axioms`), and examples `BALWtermExp 3`, `BALWtermEXP 3`, `BASTLWT 3` applied at the data above (probe 369-387 pattern) plus `BALWterm 3` as a `Prop`. All the names used exist on `main`: `sz0` (`RBM.Gauss.SizesInst`), `zSeq`, `flow_sz0`, `half_lt_t0` (`RBM.BA.FlowPinsInst`, `FlowPins:984-1433`).

### Verdict

- File `Chain/LWGen.lean` (10 names, `PinFam`, `bandPin`, bridges): **PASS**.
- File `BA/LWPinsBA.lean` (`baPin`, BA readings, band instances, instances): **PASS**.
- Two points for the 1b, not blockers: (1) the ticket's first list reads as content of `LWGen`, not as names `Step2Gen` has (0 hits); (2) `FlowFM.msig` is replaced by an inline `if`, as `Step2Gen`'s `STEGtg` does.

## (b) Script output — Sat Oct 10 22:12:30 UTC 2026

```
$ wc -l RBM3D/Chain/LWGen.lean RBM3D/BA/LWPinsBA.lean   (stop line 600)
     151 RBM3D/Chain/LWGen.lean
     111 RBM3D/BA/LWPinsBA.lean
     262 total
$ python3 -I clos.py . RBM3D.Chain.LWGen   (import check (ii); forbidden = Graph.LWTermHolds|LWExpTerm*|LWMoment*|AuxGraph*|Step2Events|Step2Iterate)
RBM3D.Chain.LWGen closure size 70
forbidden in closure: []
$ grep -n "^import" RBM3D/Chain/LWGen.lean RBM3D/BA/LWPinsBA.lean
RBM3D/Chain/LWGen.lean:6:import RBM3D.Chain.Step2Gen
RBM3D/Chain/LWGen.lean:7:import RBM3D.Graph.LWPins
RBM3D/BA/LWPinsBA.lean:6:import RBM3D.Chain.LWGen
RBM3D/BA/LWPinsBA.lean:7:import RBM3D.Graph.LWTermHolds
RBM3D/BA/LWPinsBA.lean:8:import RBM3D.Graph.LWExpTerm6
RBM3D/BA/LWPinsBA.lean:9:import RBM3D.BA.FlowPins
$ lake build RBM3D.Chain.LWGen RBM3D.BA.LWPinsBA | tail -1;  lake build (full, after the two import lines) | tail -1
Build completed successfully (3963 jobs).
Build completed successfully (4207 jobs).   [full build, run once before the commit; the registry pre-check (#assert_rbm_axioms, no new owed line) ran inside it, exit 0]
$ lake env lean $S/ax.lean   (#print axioms of the new theorems)
'RBM.BA.band_LWtermG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWtermExpG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWtermEXPG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_STLWBgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_STLWTgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWterm_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWtermExp_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWtermEXP_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STLWB_bandPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STLWT_bandPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWAvgLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWAssm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWAssmExp' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2394-check.lean | tail -3   (exit 0, no error)
$ grep -c "sorry\|admit\|native_decide\|^axiom" <both files>
RBM3D/Chain/LWGen.lean:0
RBM3D/BA/LWPinsBA.lean:0
$ name-clash grep (31 new public names, def|abbrev|theorem lines, outside RBM3D/Probe/): files with a hit
  11 RBM3D/BA/LWPinsBA.lean
  21 RBM3D/Chain/LWGen.lean
$ git diff --stat HEAD~1 HEAD   (commit 3efd9da on t/T2394, base 5ba1ebe)
 RBM3D.lean             |   2 +
 RBM3D/BA/LWPinsBA.lean | 111 ++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/LWGen.lean | 151 +++++++++++++++++++++++++++++++++++++++++++++++++
 3 files changed, 264 insertions(+)
$ RBM1D/RBM2D diff-stat: not applicable (no port; the probe text of t/T2387 and merged Step2Gen are the sources)

### Target statements (extracted by sed from the files)
$ sed -n "/^def LWtermG/,/^def LWtermExpG/p" RBM3D/Chain/LWGen.lean | head -14
def LWtermG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T0 sz z n) →
        ∀ (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Ψ : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ),
          LWAssmgL (mk sz z) (law sz) t ε₀ Ψ Φ C₁ C₂ C₃ Cc →
          PrecL sz (law sz) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖LWEg (mk sz z) n (t n) p.1 p.2 ω‖)
            (fun n p _ => ((mk sz z).eta n (t n))⁻¹ * Φ n 0 *
              Φ n ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ 2)

/-- `lem: EWGn2_N` (`LWPins.lean:290`), the `T`-bound. -/
$ grep -nE "^(def|abbrev|theorem) (PinFam|bandPin|LWterm_iff|LWtermExp_iff|LWtermEXP_iff|STLWB_bandPin|STLWT_bandPin|band_LWE|baPin|BA|band_)" -A1 <both files>
130:def bandPin (P : PinFam) (d : ℕ) : Prop := P d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
131-  (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
--
142:theorem LWterm_iff (d : ℕ) : LWterm d ↔ bandPin LWtermG d := Iff.rfl
143:theorem LWtermExp_iff (d : ℕ) : LWtermExp d ↔ bandPin LWtermExpG d := Iff.rfl
144:theorem LWtermEXP_iff (d : ℕ) : LWtermEXP d ↔ bandPin LWtermEXPG d := Iff.rfl
145-/-- `bandFM_STLWB` (`Step2Gen`) in the `bandPin` form. -/
146:theorem STLWB_bandPin (d : ℕ) : STLWB d ↔ bandPin STLWBgL d := Iff.rfl
147:theorem STLWT_bandPin (d : ℕ) : STLWT d ↔ bandPin STLWTgL d := Iff.rfl
148-
39:def baPin (P : PinFam) (d : ℕ) : Prop := P d (fun sz => Sizes.seqP (sz.withLam 0))
40-  (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
--
45:abbrev BALWterm : ℕ → Prop := baPin LWtermG
46-/-- `lem: EWGn2_N` at the block Anderson data (owed: BA-L6). -/
47:abbrev BALWtermExp : ℕ → Prop := baPin LWtermExpG
48-/-- `lem:LWterm_EXP` at the block Anderson data (owed: BA-L6). -/
49:abbrev BALWtermEXP : ℕ → Prop := baPin LWtermEXPG
50-/-- `STLWB` at the block Anderson data (owed: T1-BA / T7-BA, through L5). -/
51:abbrev BASTLWB : ℕ → Prop := baPin STLWBgL
52-/-- `STLWT` at the block Anderson data (owed: T1-BA / T7-BA, through L5). -/
53:abbrev BASTLWT : ℕ → Prop := baPin STLWTgL
54-
--
57:theorem band_LWtermG : bandPin LWtermG 3 := (LWterm_iff 3).1 (lwterm_holds 3)
58:theorem band_LWtermExpG : bandPin LWtermExpG 3 := (LWtermExp_iff 3).1 (lwtermExp_holds 3)
59:theorem band_LWtermEXPG : bandPin LWtermEXPG 3 := (LWtermEXP_iff 3).1 (lwTermEXP_holds 3)
60:theorem band_STLWBgL : bandPin STLWBgL 3 := (STLWB_bandPin 3).1 (STLWB_of_LWterm (by norm_num) (lwterm_holds 3))
61:theorem band_STLWTgL : bandPin STLWTgL 3 := (STLWT_bandPin 3).1 (STLWT_of_LWtermExp (by norm_num) (lwtermExp_holds 3))
62-

### Compiled nonempty instances (RBM3D/BA/LWPinsBA.lean, section Inst; examples, d = 3, sz0, n = 0: L = 4, W = 32)
example : Prop := BALWterm 3

/-- `BALWtermExp 3` at the data above: every deterministic hypothesis is discharged; `(initialGT2)` and `(LW_assm_exp)` stay
hypotheses (other gates' pins). -/
example (h : BALWtermExp 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 0)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) Ψ0 (fun _ => 0)
    ⟨by norm_num, Ψ0_window, hI, fun _ => le_rfl, ell0, hL⟩ 1 one_pos

/-- `BASTLWT 3` at the data above. -/
example (h : BASTLWT 3) (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : ∀ D : ℝ, 0 < D → STLWassmExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) D (fun _ => 0)) :=
  h (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) (by norm_num) Ψ0 Ψ0_window hI (fun _ => 0)
    (Eventually.of_forall fun n => ⟨le_rfl, ell0 n⟩) hL 1 one_pos

/-- `BALWtermEXP 3` at the data above: the Step 1/2 bounds stay hypotheses. -/
example (h : BALWtermEXP 3) (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hM hK hD
end Inst
```

Narrative. `Chain/LWGen.lean` holds the ten new carrier-level names (`LWcutg`, `LWEg`, `LWAvgLawgL`, `LWLoop2gL`, `LWAssmgL`,
`LWLoopExpgL`, `LWAssmExpgL`, `LWtermG`, `LWtermExpG`, `LWtermEXPG`), copied from the probe lines 48-91 and 99-141 with
`C.msig n σ` replaced by the inline `if σ then C.m n else (starRingEnd ℂ) (C.m n)` (preflight point 2; `Step2Gen` has no
`FlowFM`-level `msig`).  It also holds `PinFam`, `bandPin` and the bridges.  `baPin`, the five BA readings, the five band
instances and the examples are in `BA/LWPinsBA.lean`.  `STLWB_bandPin`/`STLWT_bandPin` (`Iff.rfl`) are added because
`Step2Gen`'s `bandFM_STLWB`/`bandFM_STLWT` are not stated through `bandPin`.  No merged file is edited except `RBM3D.lean` (two import
lines after the last import).  `Test/Axioms.lean` is not edited: the registry pre-check passed with no new owed line.
All bridges are `rfl`/`Iff.rfl`, as in preflight row 3.  `BASTLWB 3` has no example; the examples cover `BALWtermExp 3`,
`BASTLWT 3`, `BALWtermEXP 3` (applied at the data) and `BALWterm 3` (as a `Prop`), as the ticket requires.
The instance data are those of preflight (ii); the hypotheses left in the examples are the stochastic ones of other gates
(`STInitialGT2gL`, `LWLoopExpgL`, `STLWassmExpgL`, `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL`).
The `3 ≤ d` premise is in `LWtermG`/`LWtermExpG`/`LWtermEXPG` but not in `STLWBgL`/`STLWTgL` (as in `Step2Gen`, band
`STLWB d`/`STLWT d`); `band_STLWBgL`/`band_STLWTgL` are proved at `d = 3` via `STLWB_of_LWterm`/`STLWT_of_LWtermExp` with `3 ≤ 3`.
The audit-relevant fact on import closure: `LWGen` has 70 modules and none of the forbidden ones; `LWPinsBA` is downstream by design.

## (c) Verified Mathlib names (compiled in `LWPinsBA`)

- `Real.rpow_le_rpow_of_exponent_le`, `Real.log_nonneg`, `pow_nonneg`, `mul_nonneg`, `Eventually.of_forall`: used in the `Ψ0_window` and `ell0` proofs; build passes.

## (d) Open issues and paper-delta candidates

- T2394a: Lean carrier pins `LWcutg`/`LWEg`/`LWtermG`/... read the kernel `C.S`, loops `C.L`, one-loop value `C.m` and `η` of the carrier `FlowFM`
  instead of `SB`, `Lloop`, `mE`, `etaT` of the band model; the band pins are recovered by `Iff.rfl` (no mathematical difference at the band).
- T2394b: `STLWBgL`/`STLWTgL` (`Step2Gen`) carry no `3 ≤ d`; `BASTLWB d`, `BASTLWT d` are provable only at `3 ≤ d` (as the band forms).
- Owed lines: none added (preflight prediction on `scanPremises` confirmed by the full build); the first theorem that takes `BALWterm d` etc. as hypothesis owes the line (BA-L6; BASTLWB/BASTLWT: T1-BA/T7-BA).
- No open issue; targets all delivered; both files at 262 lines of the 600 stop line.
