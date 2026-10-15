Prover model: claude-sonnet-5-5

## (a) Math preflight — Thu Oct 15 09:18:06 UTC 2026

Source of every value below: the files named (RBM3D/ paths) and the two scripts `T2518/inst.py`, `T2518/mm.py` in the scratchpad (output pasted in (ii)). Instance data: `d = 3`, `(𝔠, 𝔡) = (1/6, 1/10)` (`S0_adm`, `BA/UNPins:887`), `S0 = clsSz 4` (`UNPins:776`): `L = 4`, `W_n = (2(n+1))^5`, `lam_n = g0 ∈ (0, 3/10]` constant (`FlowPt.g0_le`, `MFixedPoint:882`), `N = (4W)^3`.

### (i) Exponent table

| # | quantity | value (instance) | constraint (file:line) | slack |
|---|---|---|---|---|
| 1 | decol `ε = min(τ/2, 1/2)` | `1/20` (τ = 1/10) | `0<ε≤1` (`decol_core` `hε1`, FixedZ:750) | `1/2 − 1/20 = 9/20` |
| 2 | decol `τ_L = min(𝔡, dε/2)` | `3/40` | `τ_L ≤ 𝔡 = 1/10`; `τ_L ≤ dε/2 = 3/40` (FixedZ:639 `hτL1,2`) | `1/40` / `0` (the min is attained by dε/2) |
| 3 | decol scalar 1: `W^{τ_L}𝓑_{η,0} ≤ 1`, `η = N^{-1+ε}` | `𝓑 ≤ W^{-2𝔡}+W^{-dε}` = `W^{-1/5}+W^{-3/20}`; times `W^{3/40}`: `W^{-1/8}`, `W^{-3/40}` | each `≤ 1/2` needs `W^{3/40} ≥ 2` (proof device), i.e. `W ≥ 2^{40/3} ≈ 1.03e4` | exponents `−1/8`, `−3/40` strictly negative |
| 4 | decol scalar 2: `2η ≤ N^{-1+τ}` | `N^{τ−ε} = N^{1/20}` | `≥ 2`, i.e. `N ≥ 2^{20}`; needs `τ − ε > 0` | `τ − ε = 1/20` |
| 5 | decol diagonal local-law input | `‖G_xx − M_xx‖² ≤ W^{τ_L}𝓑_{η,0} ≤ 1`, `Im M_xx ≤ ‖m‖ ≤ 1 = C_M` | `|ψ_k(x)|² ≤ η(C_M+1) = 2η ≤ N^{-1+τ}` (`ukx` FixedZ:596; `decol_spectral_core` :733) | `C_M = 1` exactly as band (`‖msc‖<1`); `BAm_norm_le_one` (Ward:136) |
| 6 | QUE `𝔡, ε₀, c, τ` | `1/10, 1/30, 1/60, 1/300` | `0<ε₀<𝔡/2 = 1/20`; `0<c<ε₀`; `c<𝔡/5 = 1/50`; `0<τ` | `1/60` (ε₀ vs 𝔡/2); `1/60` (c vs ε₀); `1/300` (c vs 𝔡/5 = 1/50); all strict |
| 7 | `que_three_terms` `ε₀ ≤ 3𝔡/5` (`que_three_terms`, QUEFromQDiff:196) | `1/30 ≤ 3/50` | used by `queChain_real` | `3/50 − 1/30 = 2/75`; `𝔡/10 = 1/100` at ε₀ = 𝔡/2 |
| 8 | QUE exponent `−min(2ε₀, 2𝔡/5) + 2c + τ` (`queBound`, Universality/Pins:384) | `−1/25 + 1/30 + 1/300 = −1/300` | `< 0` for non-vacuity; iff `τ < min − 2c = 1/150` | `1/300`; the merged `inst_BAEnd_QUEL` (UNPins:1225) uses τ = 1/100: exponent `+1/300`, bound `> 1` (vacuous) |
| 9 | `QDiff` parameters fed by M3 | `(κ, ε_Q, τ/2, D) = (κ, 1/90, 1/600, 1)` | `ε_Q = 𝔠(𝔡−ε₀) = (1/6)(1/15) = 1/90 > 0` (needs `ε₀<𝔡`) | `𝔡 − ε₀ = 1/15` |
| 10 | `η_Q` domain (`queDomain` QUEFromQDiff:91) | `N^{-1+1/90} ≤ η_Q ≤ 1` | `η_Q N ≥ W^{𝔡−ε₀} ≥ N^{𝔠(𝔡−ε₀)}` (uses `W ≥ N^𝔠`, `lam W^{d/2} ≥ W^𝔡` from `(eq:WO)`); `η_Q ≤ 1` from `lam ≤ 𝔡⁻¹`, `W^{ε₀} ≥ 𝔡⁻¹+1` | `W^{1/15}` vs `N^{1/90}` (at W = N^{1/6}: `N^{1/90}` vs `N^{1/90}`, equality: bandwidth `𝔠 = 1/6` is exactly tight) |
| 11 | `η_Q ≤ lam²/L^d` (`etaQ_le`, QUEFromQDiff:208) | needs `lam ≥ W^{-d/2−ε₀}` | `(eq:WO)`: `lam ≥ W^{-3/2+1/10}` | factor `W^{𝔡+ε₀} = W^{2/15}` |
| 12 | `(Nη_Q)⁻¹ ≤ W^{ε₀−𝔡}` | `W^{-1/15}` | from `lam W^{3/2} ≥ W^{1/10}` | exact (no slack lost) |
| 13 | `(lam² W^d)^{-1/5} ≤ W^{-2𝔡/5}` | `W^{-1/25}` | `lam²W^d ≥ W^{2𝔡}` (`lam_sq_mul_pow_ge`) | exact |
| 14 | `queChain` absorption `3 max(16C,128) ≤ W^{τ/2}` | `W^{1/600}` | proof's eventual `n_0` (a `∀ᶠ` threshold, not a hypothesis); `C = 2C₈/cT + 𝔡⁻²` from `baThetaDiff` | `W ≥ 384^{600} ≈ 10^{1551}` when `16C ≤ 128`; `4800^{600} ≈ 10^{2209}` at `C = 100` |
| 15 | row-difference constant `K = C lam⁻² W^{-d}` | `C` from `baThetaDiff` | `∃ C` before `sz` (as `queRowDiff` QUEFromQDiff:244); `0<lam≤𝔡⁻¹`, `0<Im z≤1`, `BAbulk κ z.re` | none (lossless, no `W^τ`) |
| 16 | bandwidth, `S0` | `N^{1/6} = (4W)^{1/2} ≤ W` | `W ≥ 4` | all `W = 4^5 = 1024` at n = 1 |
| 17 | `(eq:WO)`, `S0` | `W^{-7/5} ≤ g0 ≤ 10` | `g0 ∈ (0, 3/10]` | `W^{-7/5}` at n = 1: `6.1e-5` |

Remarks. (1) Row 3's `2^{40/3}` and row 14's `10^{1551}` are the proofs' own eventual thresholds; the statements of targets 3, 4, 8 are `∀ᶠ n` conclusions with only parameter-sign hypotheses, so no target hypothesis involves them. The row-8 bound `W^{-1/300} < 1` for every `W > 1`, so the instance is non-vacuous at all `n`; only the proof's absorption of the constant `3 max(16C,128)` into `W^{τ/2}` needs the astronomically large `n_0` (Lean proves `∀ᶠ`; an `example` needs no concrete `n`). (2) Row 10's equality case: at `𝔠 = 1/6` and `W = N^{1/6}` exactly the non-strict `≤` of `queDomain` is used (`Real.rpow_le_rpow`, closed inequality), so no strictness is needed. (3) Decol and QUE exponents are the band ones with `d = 3` replaced by `d`-free forms (`calB` uses only `d ≥ 2`, `decol_scalars` takes `hd : 2 ≤ d`, `queChain` takes `3 ≤ d`); no `d = 3`-only constant appears. (4) `1_2:399` `(eq:ukx)` is `|ψ_k(x)|² ≤ η Im G_xx(μ_k + iη)` at `z = μ_k + iη` (`ukx`, FixedZ:596): the BA reading `M_xx = m` agrees with the paper's `1_2:399` reading, so no paper-delta candidate from target 1.

### (ii) One concrete nondegenerate instance

Command: `cd <scratchpad>/T2518 && python3 inst.py` (exact `Fraction` hypothesis checks; `mpmath` 80 digits for the finite-size quantities at `S0`, `n = 1`, `g0 ∈ {0.3, 0.05}`), then `python3 mm.py`.

```
decol: eps= 1/20 tauL= 3/40  tau-eps= 1/20
QUE: epsQ= 1/90  min(2e0,2dd/5)= 1/25  queBound exponent= -1/300  nonvacuous iff tau< 1/150  QDiff tau/2= 1/600
  0<e0<dd/2 True / 0<c<e0 True / c<dd/5 True / 0<tau True / e0<=3dd/5 (que_three_terms) True
  eps<=1 True / 0<tauL<=dd True / tau-eps>0 True / 0<epsQ True / e0<dd (queDomain) True
g0=0.3: all finite-size conditions hold from n=1: W=(2*2)^5=1.024e+03, N=6.872e+10
   queBound = W^(-1/300) = 0.9771599684342459 (<1)
g0=0.05: all finite-size conditions hold from n=1: W=(2*2)^5=1.024e+03, N=6.872e+10
   queBound = W^(-1/300) = 0.9771599684342459 (<1)
decol W^(3/40)>=2 needs W >= 10321.273240738801 i.e. n+1 >= 3.174802103936399
queChain absorption C=1: needs W >= 384^600 = 10^1551
queChain absorption C=8: needs W >= 384^600 = 10^1551
queChain absorption C=100: needs W >= 4800^600 = 10^2209
```
"All finite-size conditions" (script, `checks`) = WO `W^{-7/5} ≤ lam ≤ 10`, bandwidth, decol scalars 1 and 2 (direct evaluation of `W^{τ_L}𝓑_{η,0}`), `η_Q ≤ 1`, `N^{-1+ε_Q} ≤ η_Q`, `η_Q ≤ lam²/L^d`, `(Nη_Q)⁻¹ ≤ W^{ε₀−𝔡}`; all `True` at `n = 1` for both `g0`. Every hypothesis of targets 3, 4, 8, 9 (`3 ≤ d`, `S0_adm`, `κ = clsκ 4 > 0` (`clsκ_pos`, UNPins:858), `0<τ`, `0<D`, QUE row 6) holds at the data above; `d = 3`, `L = 4`, `W = 1024` at `n = 1`, no empty index set, no collapsed window.

Target 1 (`baMz_diag`), `mm.py` (Z_4^3 nearest-neighbour adjacency, `Ψ^{(B)}` = `PsiB`, BlockAnderson:45; `(self_m)` = `BASelf`, MFixedPoint:193, `g = 0.3`):
```
z=1j: m=-0.000000+0.549085j Im m=0.5491>0 |m|=0.5491<=1 fixpt-res=5.6e-16 (Im m+Im z)*sum|M_ab|^2 - Im m = 1.1e-16
z=(0.5+0.05j): m=-0.172719+0.788544j Im m=0.7885>0 |m|=0.8072<=1 fixpt-res=5.6e-17 (Im m+Im z)*sum|M_ab|^2 - Im m = -1.2e-15
z=(0.5+0.001j): m=-0.176942+0.805353j Im m=0.8054>0 |m|=0.8246<=1 fixpt-res=6.1e-16 (Im m+Im z)*sum|M_ab|^2 - Im m = 7.8e-16
```
Route: `BAm_self` (MFixedPoint:809, with `BASelf`'s `0 < m.im`) gives `0 < Im m`, so `(z + m).im = Im z + Im m ≠ 0`; `BAMres_fine_apply` (FlowPins:102) then `BAMB_diag_eq` (Ward:89): `M_xx = m`; `Im M_xx ≤ ‖m‖ ≤ 1` by `BAm_norm_le_one` (Ward:136); Ward row identity `(Im m + Im z)Σ_b|M_ab|² = Im m` (`BAMB_ward_row`, Ward:108) agrees with the script (residual ~1e-16).

External-input check (`baThetaDiff`, the one hypothesis M3 reads from another ticket; TEAM §8 lesson 14): the text identity, script on the files (`BA/GUEKPrim:563` against `docs/tickets/checks/T2515-check.lean:166`, `main` 13b68cea):
```
baThetaDiff (GUEKPrim:563) text == T2515_ThetaDiffBA (check:166) after whitespace normalisation: True 474 474
```
It is a theorem on `main` (`C = 2C₈/cT + 𝔡⁻²`, `docs/reports/T2515-1a-audit.md:78-79`), so no hypothesis is carried. The limit computation is row 14/15: `C` depends on `(d, 𝔡, κ)` only, so `16C ≤ 128` or `C = 100` both give a finite eventual `n_0`; the target is `∀ᶠ n` for every fixed `C`. `baEnd_QDiffL` (`BA/MAQDiff:1012`) and `baEnd_QDiffL_three` (:1016) are on `main` (13b68cea), statements `BAEnd_QDiffL d`, `BAEnd_QDiffL 3` (`MAPins:107`).

### Notes on the ticket's fill-in table (math content only)
- (ii) `open private` in a compiled scratch: not done here (stage 1a writes no Lean); the reach of `QUEFlow_*` private names is checked by 1b at the file header (stop rule in the ticket). Precedent for `open private … from` exists in `RBM3D/Graph/BAExp14dB.lean:35`.
- (vii) registry lines on `main` 13b68cea by name: `BAEnd_QUEL` at `Test/Axioms.lean:180`, `UNQuek` at `:385` (ticket says `:183`, `:388`: shifted by 3, located by name per the ticket; no pin moves).
- (viii) twin sizes: `que2Bad_sub` QUECore:1013-1082 = 70 lines (target 6 central 75, stop 150 unaffected); price table unchanged by the mathematics.

### Verdict
- Target P (`UNQueBAAt`, `UNQueBA_iff_at`): PASS (no exponent).
- Targets 1–4 (decol): PASS (rows 1–5; `C_M = 1`; scalars hold eventually; script instance).
- Targets 5–9 (QUE, core, bridge): PASS (rows 6–15; exponent `−1/300 < 0`; τ = 1/300 < 1/150; `baThetaDiff` text identical, theorem on `main`; `baEnd_QDiffL(_three)` on `main`).
- Target 10 (instances): PASS at `S0`, `(ε₀,c,τ) = (1/30, 1/60, 1/300)`; the merged τ = 1/100 is vacuous (bound > 1), as the ticket says.
- No pin, row or stop line moves; no `1a-audit` needed.

## (b) Script output (stage 1b)

```
$ date -u; git log --oneline -3; git diff --stat main...t/T2518; wc -l RBM3D/BA/MADecolQUE.lean
Thu Oct 15 09:36:31 UTC 2026
d621c193 T2518: MADecolQUE section 3 (instances), RBM3D.lean import, registry (BAEnd_QUEL left owed list)
968c89f7 T2518: MADecolQUE section 2 (QUE targets 5-9)
d9482635 T2518: MADecolQUE section 1 (P, decol targets 1-4)
 RBM3D.lean               |   1 +
 RBM3D/BA/MADecolQUE.lean | 532 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   5 +-
 3 files changed, 535 insertions(+), 3 deletions(-)
     532 RBM3D/BA/MADecolQUE.lean
```

```
$ lake build RBM3D.BA.MADecolQUE 2>&1 | tail -2; lake build 2>&1 | tail -1
Note: This linter can be disabled with `set_option linter.style.header false`
Build completed successfully (4361 jobs).
Build completed successfully (4424 jobs).
```

Registry scan (`#assert_rbm_axioms` in the full `lake build`).  Before = this worktree with `RBM3D.lean`, `Test/Axioms.lean` as on `main` 13b68cea (`MADecolQUE` not imported); after = branch tip.  Lines located by name: `BAEnd_QUEL` was `Test/Axioms.lean:180`, `UNQuek` `:385` (the ticket says `:183`, `:388`).

```
$ grep -nE 'axiom audit|premises found by scanning|^registry:|RBM.BA.BAEnd_QUEL: ' <build log> | cut -c1-150
7723:info: RBM3D.lean:653:0: axiom audit: 15494 theorems, 4754 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7800:  RBM.BA.BAEnd_QUEL: 3 [no certificate]
7847:premises found by scanning: 125 (borrowed 1, owed 52, structural 52, refuted 6, superseded 14).
7848:registry: 2 borrowed + 116 owed + 142 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
---after---
7730:info: RBM3D.lean:654:0: axiom audit: 15506 theorems, 4755 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7853:premises found by scanning: 124 (borrowed 1, owed 51, structural 52, refuted 6, superseded 14).
7854:registry: 2 borrowed + 115 owed + 142 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
lines naming BAEnd_QUEL in the owed ledger after: 0
```

Target statements, extracted by script (`extract.py`: each public declaration, whitespace-collapsed, up to its `:=`; `Ln` = file line):

```
L52: def UNQueBAAt (d : ℕ) : Prop := ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ → ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ → ∀ᶠ n in atTop, ∀ E : ℝ, (UNKind.ba d).bulk sz κ E n → ∀ a : Zd d (sz.L n), ((UNKind.ba d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((UNKind.ba d).M sz).H n ω)} ≤ queBound (sz.W n) 𝔡 ε₀ c τ
L60: theorem UNQueBA_iff_at : UNQueBA ↔ ∀ d : ℕ, 3 ≤ d → UNQueBAAt d
L68: theorem baMz_diag {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (hz : 0 < z.im) (x : Idx d (sz.L n) (sz.W n)) : BAMz sz n z x x = BAm d (sz.L n) (sz.lam n) z ∧ (BAMz sz n z x x).im ≤ 1
L125: theorem baMADecol (d : ℕ) : BAMADecol d
L143: theorem baEnd_decolL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_decolL d
L147: theorem baEnd_decolL_three : BAEnd_decolL 3
L294: theorem baQueFixed {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E ε K : ℝ) (z : ℂ) (hz : z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) (hη : 0 < etaQ sz n ε₀) (hQ : ∀ a b : Zd d (sz.L n), ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) - BAprof sz n z true false a b‖ ≤ ε ∧ ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z ω x y * BAGz sz n z ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) - BAprof sz n z true true a b‖ ≤ ε) (hK : ∀ a b b' : Zd d (sz.L n), ‖BAprof sz n z true false a b - BAprof sz n z true false a b'‖ ≤ K ∧ ‖BAprof sz n z true true a b - BAprof sz n z true true a b'‖ ≤ K) : (∀ a : Zd d (sz.L n), Sizes.seqP (sz.withLam 0) {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqHBA n ω)} ≤ ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) ∧ (∀ A : Finset (Zd d (sz.L n)), A.Nonempty → Sizes.seqP (sz.withLam 0) {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqHBA n ω)} ≤ ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))))
L321: theorem baMAQUE (d : ℕ) : BAMAQUE d
L359: theorem baEnd_QUEL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_QUEL d
L363: theorem baEnd_QUEL_three : BAEnd_QUEL 3
L373: theorem unQueBAAt_of_QUEL (d : ℕ) (hd : 3 ≤ d) (h : BAEnd_QUEL d) : UNQueBAAt d
L378: theorem unQueBAAt_of_ML (d : ℕ) (hd : 3 ≤ d) (hML : UNMLOutBA d) : UNQueBAAt d
L382: theorem unQueBAAt_three : UNQueBAAt 3
```

`#print axioms` of all 13 new public declarations (`axioms.lean`: `#print axioms` per name; the 13 verbatim lines grouped by axiom set by the pipeline shown):

```
$ lake env lean axioms.lean | <group by axiom set>
[propext, Classical.choice, Quot.sound]: UNQueBAAt UNQueBA_iff_at baMz_diag baMADecol baEnd_decolL baEnd_decolL_three baQueFixed baMAQUE baEnd_QUEL baEnd_QUEL_three unQueBAAt_of_QUEL unQueBAAt_of_ML unQueBAAt_three
```

Statement diff against the pins: the Part 2 text of `docs/tickets/checks/T2518-check.lean` (lines from `## Part 2` to the end) plus 15 `example : T2518_X := <Lean name>` (`audit_scratch.lean`, uncommitted, in the scratchpad; the 15th, `T2518_RowDiff := MADecolQUE_rowDiff`, reads the private target 5c by `open private`):

```
$ lake env lean audit_scratch.lean; echo exit=$?   # then the 15 examples:
exit=0
T2518_QueIffAt:=UNQueBA_iff_at;example : ∀ d, UNQueBAAt d ↔ T2518_UNQueBAAt d := fun _ => Iff.rfl;T2518_MzDiag:=fun sz n z hz x => baMz_diag sz n z hz x;T2518_MADecolAll:=baMADecol;T2518_DecolOfML:=baEnd_decolL;T2518_DecolThree:=baEnd_decolL_three;T2518_QueFixed:=fun sz n ε₀ c E ε K z hz hη hQ hK => baQueFixed sz n ε;T2518_MAQUEAll:=baMAQUE;T2518_QUEOfML:=baEnd_QUEL;T2518_QUEThree:=baEnd_QUEL_three;T2518_QueCore:=unQueBAAt_of_QUEL;T2518_QueAtOfML:=unQueBAAt_of_ML;T2518_QueAtThree:=unQueBAAt_three;T2518_QueBridge:=fun h => UNQueBA_iff_at.2 fun d hd => unQueBAAt_of_QU;T2518_RowDiff:=MADecolQUE_rowDiff
```

The compiled nonempty instances (section 5 of the file, lines 386-528; short ones pasted; the longer `example`s at L412-433 (5b, 5c), L434-485 (targets 6, 7: `∃ n ε K`, every hypothesis of `baQueFixed` discharged in the proof), L499-505 (`queBound < 1`), L522-526 (`UNQueBA_iff_at` read at `d = 3`) are in the file).  Data: `d = 3`, `S0` (`L = 4`, `W_n = (2(n+1))^5`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ_* = clsκ 4`, `(ε₀, c, τ) = (1/30, 1/60, 1/300)` for QUE, `(τ, D) = (1/10, 1)` for decol:

```
example := baMz_diag sz0 0 Complex.I (by simp) (0 : Idx 3 (sz0.L 0) (sz0.W 0))
example := baMz_diag S0 1 (⟨(fp 4 MADecolQUE_hg).E, 1 / 2⟩ : ℂ) (by norm_num) (0 : Idx 3 (S0.L 1) (S0.W 1))
example := baEnd_decolL_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (1 / 10) 1
  (clsκ_pos 4 MADecolQUE_hg) (by norm_num) (by norm_num)
example := baEnd_QUEL_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg) (1 / 30) (1 / 60) (1 / 300)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example := unQueBAAt_three (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg) (1 / 30) (1 / 60) (1 / 300)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example (h : ∀ d : ℕ, BAEnd_QUEL d) : UNQueBA := UNQueBA_iff_at.2 fun d hd => unQueBAAt_of_QUEL d hd (h d)
```

Name-clash grep (hit counts on `main` 13b68cea, then on the sibling branches, then the hits of the tree outside the new file: my registry comments):

```
$ for n in <13 new names + MADecolQUE_que2Fixed>; do git grep -nw $n 13b68cea -- RBM3D | wc -l; done; (same on 5 sibling branches); grep -rnw <3 names> RBM3D | grep -v MADecolQUE.lean
baMz_diag=0 baMADecol=0 baEnd_decolL=0 baQueFixed=0 baMAQUE=0 baEnd_QUEL=0 UNQueBAAt=0 UNQueBA_iff_at=0 unQueBAAt_of_QUEL=0 unQueBAAt_of_ML=0 unQueBAAt_three=0 baEnd_decolL_three=0 baEnd_QUEL_three=0 MADecolQUE_que2Fixed=0 
t/T2514b=0 t/T2515=0 t/T2515b=0 t/T2516=0 t/T2517=0 
RBM3D/Test/Axioms.lean:175
RBM3D/Test/Axioms.lean:384
```

Ports: nothing is copied from `../RBM1D` or `../RBM2D` (no RBM1D/RBM2D diff-stat).  The copies are of merged RBM3D files (`que2Bad_sub` `Main/QUECore:1013-1082`, second half of `QUEFlow_queFixed` `Universality/QUEFlow:815-845`, `decol_core` `Main/FixedZ:750-785`); last commit of each file (`git log -1 --format=%h -- RBM3D/<f>.lean`):

```
Main/QUECore: 389ad9ed; Universality/QUEFlow: 5d7a660b; Main/FixedZ: 0d5868e9; Main/QUEFromQDiff: d822fd76; 
```

Hypothesis-rule greps (`file` = `RBM3D/BA/MADecolQUE.lean`):

```
C1  (statements; docstring hits only): 67@Mband 67@msc 67@msc 184@seqXmat
X1-C4 public defs in file: 1; MN1/BAEnd defs outside MAPins/UNPins: 0; Θ|PropThetaQ: 0; MN-D3 (ℕ → Prop)|· = 3: 0
UBA withLam hits not of the form seqP (_.withLam 0): 0 (of 16)
U5S-C3 ∃ at lines: 85 89 172 173 414 416 436  (85, 172 docstrings; 89 core event set `¬ ∃ z`; 173 `∃ C` before `sz`; 414, 416, 436 instances)
_three: `theorem` lines: 147 363 382; `example` lines: 402 406 409 489 492 496 509 512 515; other (docstrings, instance bodies): 39 41 42 146 362 381 401 435 458 508
sorry|admit|native_decide|axiom hits: 0
```

Lines per target (`spans2.py`, from `spans.py` declaration spans; rows exclude blank and `section`/`end` lines between them):

```
$ python3 spans2.py
header, imports, open private, doc             L  1- 47 =  47   table 35/40/50
P  UNQueBAAt, UNQueBA_iff_at                   L 48- 60 =  13   table 15/18/25
1  baMz_diag                                   L 66- 82 =  17   table 10/15/25
2  decol core (private)                        L 84-121 =  38   table 30/40/55
3  baMADecol                                   L123-140 =  18   table 15/20/30
4  baEnd_decolL, _three                        L142-147 =   6   table 6/8/10
5  meas, domain, rowDiff (private)             L155-181 =  27   table 23/45/120
6  generic que2Bad_sub + que2Fixed (private)   L183-289 = 107   table 60/75/95
7  baQueFixed                                  L291-315 =  25   table 25/35/45
8  baMAQUE, baEnd_QUEL, _three                 L317-363 =  47   table 46/63/90
9  unQueBAAt_of_QUEL, _of_ML, _three           L371-382 =  12   table 12/18/25
10 instances (section 5)                       L386-528 = 143   table 40/55/80
sum of rows = 500; file total = 532 (table 317/432/650; calibrated 415-553; stop line 900)
```

### Narrative (routes, target 6, price, instances, registry; every line below is backed by the output above or the file)
- (a): no correction needed.  Its registry lines `:180`, `:385` match my grep.  `baThetaDiff` (`GUEKPrim:563`) and `baEnd_QDiffL(_three)` (`MAQDiff:1012`, `:1016`) are theorems on `main` 13b68cea; `T2518_RowDiff := MADecolQUE_rowDiff` (15th example) compiles.
- Coverage table as used: rows 1-5, 8, 11-14 are the merged names of the routes below; rows 6, 7 (T2516, T2515 a) were merged at the start; row 9 = target 7, row 10 = target 6; no premise outside the table.
- Route per target (merged `file:line`). P: `UNQuek` at `UNKind.ba d` after `∀ d, 3 ≤ d →` (as `UNLocAvgBAAt`, `MAPins:170`); `UNQueBA_iff_at := Iff.rfl`. 1: `BAm_self` (`MFixedPoint:809`) gives `0 < Im m`, so `(z+m).im ≠ 0`; `BAMres_fine_apply` (`FlowPins:102`), `BAMB_diag_eq` (`Ward:89`), `Im M_xx ≤ ‖m‖ ≤ 1` by `BAm_norm_le_one` (`Ward:136`). 2: twin `decol_core` (`FixedZ:750`) with `decol_spectral_core` (`FixedZ:733`, `C_M = 1`) and `zdistInf_zero` (`FixedZ:633`); `BAendDom`'s real part is the ρ-bulk, so `μ_k + iη ∈ BAendDom` needs no window lemma. 3: `decol_scalars` (`FixedZ:639`) verbatim at `ε = min(τ/2, 1/2)`, `τ_L = min(𝔡, dε/2)`. 4: `baEnd_locSCL` (`MALocal:834`), `_three` (`:839`). 5: `(UNModel.ba sz).meas` (`Pins:125-133`) with `measurable_pi_iff` twice; the `Im` half of `queDomain` (`QUEFromQDiff:91`) at `(κ, E) = (1, 0)` (proof use only); `baThetaDiff` at `σ = false, true` by unfolding `BAprof`. 7: `QUEFlow_queFixed` (`QUEFlow:815`) at `Hm = sz.seqHBA n` (`seqHBA_isHermitian`, `BlockAnderson:101`) and `MADecolQUE_que2Fixed`. 8: `baEnd_QDiffL` (`MAQDiff:1012`, `_three` `:1016`), `queChain` (`QUEFromQDiff:463`) at the `C` of `baThetaDiff`. 9: first conjunct of `BAqueConclL`, as the merged bridge (`UNPins:357-359`).
- Target 6 as proved (not a second copy of a helper): `MADecolQUE_que2Bad_sub` (L183-256, 74 lines) is `que2Bad_sub` (`QUECore:1013-1082`) with `sz.seqXmat n ω ↦ Hm ω`, `queX ↦ QUEFlow_X`, `queCore_{obs_eq,obs_herm,sub_of_normSq,rpow_sub} ↦ QUEFlow_*` (reached by `open private`); `queCore_quad_blk` is `open private` from `QUECore`. `MADecolQUE_que2Fixed` (L258-289, 32 lines) is the `que2BadMat` half of `queFixed` (`QUEFromQDiff:285`) on a generic `(Ω, P, Hm)`: `QUEFlow_core` at `c = 1_A/|A|`, `queMarkov`; `QUEFlow_queFixed` has only the first half. Target 6 = 107 lines with the blank between the two (stop 150), above its table hi (95). The header's `open private` lists 7 `QUEFlow_*` names and `queCore_quad_blk`; all compile and all are used.
- Price: 532 lines against table 317 / 432 / 650 and calibrated 415-553 (stop line 900 not reached). Rows 6 (107) and 10 (143) exceed their table hi (95, 80); the instance of targets 6-7 (L434-485, 52 lines) is most of row 10; the other rows are within lo-hi except P (13, below lo 15).
- Instances: all at `S0`, `d = 3`. `baQueFixed` (targets 6, 7) is at an `∃ n` because `η_Q ≤ 1` and `W^{-7/5} ≤ λ` hold for `S0` only eventually: `n` comes from `Filter.Eventually.exists` of `MADecolQUE_domain`, `S0_adm`'s `(eq:WO)` and `S0_bulk`, with `ε = qdBoundExp` from M2's `baEnd_QDiffL_three` and `K = C λ⁻² W^{-3}` from `baThetaDiff`; all hypotheses discharged. QUE uses `τ = 1/300` (exponent `-1/300`, `queBound < 1` for every `W > 1`: L499-505), not the merged vacuous `τ = 1/100` of `inst_BAEnd_QUEL`.
- Registry: `BAEnd_QUEL` line deleted, header `T2241 ...` and `UNQuek` owner texts as the ticket; scan 125 -> 124 premises (owed 52 -> 51), theorems +12, definitions +1 (`UNQueBAAt`), 0 new unclassified premises, `BAEnd_QUEL` no longer in the owed ledger. `RBM3D.lean`: one import line after `import RBM3D.BA.GUEKPrim`; both files are a union with T2514 b / T2515 b / T2517 at merge.
- Stop rules: none triggered (every target equals its pin; all privates reachable; target 6 < 150; file < 900; `baThetaDiff`, `baEnd_QDiffL(_three)` on `main` at the start; no second public `def`).

### (c) Verified Mathlib names (`#check` in `chk.lean`, signatures in the tool log)
- `measurable_pi_iff`: `Measurable g ↔ ∀ a, Measurable fun x => g x a`.
- `Real.rpow_lt_one_of_one_lt_of_neg`: `1 < x → z < 0 → x ^ z < 1`.
- `ENNReal.ofReal_lt_ofReal_iff`: `0 < q → (ofReal p < ofReal q ↔ p < q)`.
- `ENNReal.ofReal_le_ofReal`: `p ≤ q → ofReal p ≤ ofReal q`.
- `Finset.sum_ite_mem`: `(∑ i ∈ s, if i ∈ t then f i else 0) = ∑ i ∈ s ∩ t, f i`.
- `Finset.univ_inter`: `univ ∩ s = s`.
- `Filter.Eventually.exists`: `[f.NeBot] → (∀ᶠ x in f, p x) → ∃ x, p x`.
- `MeasureTheory.integral_const_mul`: `∫ r * f a ∂μ = r * ∫ f a ∂μ` (`r : L`, `RCLike L`).
- `Complex.im_le_norm`, `mul_inv_cancel₀`, `Real.rpow_le_one_of_one_le_of_nonpos`: exist with the expected statements.
- Absent / unusable here: `if_pos` is deprecated (compiler warning "use `ite_eq_left`"); `*ᵥ` needs `open scoped Matrix`.

### (d) Open issues and paper-delta candidates
- Open issues: none; all targets (P, 1-9, 10) are built, committed on `t/T2518` and instantiated. Observations: the generic `que2Bad_sub` lives privately in `BA/MADecolQUE` (a later dedupe into `QUEFlow` is possible, not needed); the `baQueFixed` instance uses an existential `n` (eventual hypotheses).
- Paper-delta candidates: none (`T2518a` not opened). The BA reading `M_xx = m(z)`, `Im M_xx ≤ 1` agrees with `(eq:ukx)`, `|ψ_k(x)|² ≤ η Im G_xx(μ_k + iη)` (`1_2:397-401`), so no difference from `1_2:399`; decol uses `ε = min(τ/2, 1/2)`, `τ_L = min(𝔡, dε/2)` as the band `decol_of_locSC` (`FixedZ:789`).
