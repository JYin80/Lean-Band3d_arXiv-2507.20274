Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 10:49 UTC 2026 (`date -u` at start of stage: 10:46:44)

### (i) Exponent table

Notation: `W = sz.W n`, `N = (W L)^d`, `lam = sz.lam n`, `ε₀ = 𝔡/3`, `c = 𝔡/6`; instance values at `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `τ_U = 1/1000` (`sz0`).

| quantity | value / form | constraint | slack |
|---|---|---|---|
| `ouTauMax 𝔠 𝔡` (`ZeroModeProfile.lean:78`) | `min(min(𝔠/12, 𝔠𝔡/12), 1/100)` = 1/720 at the instance | `τ_U ≤ ouTauMax` (only in `UNG1Rowk`, `ouRowk_of_pins`); `> 0` from `𝔠,𝔡 > 0` (`ouTauMax_pos`) | `1/720 - 1/1000 = 0.000389`; `12τ_U ≤ 𝔠`, `12τ_U ≤ 𝔠𝔡`, `τ_U < 𝔠𝔡`, `3τ_U/2 < 2𝔠𝔡/3` all True |
| `η_LL = N^{-1+2τ_U}` (`ouEtaLL`) | exponent `-0.998` | `> 0`; token-equal to `UNOUDiagk`'s `Nsz^(-1+2τU)` | n/a |
| Markov moment `p` | `p = ⌈(1+ε+D)/(2ε)⌉` | `1+ε+D ≤ 2pε`; then `N^{1+ε-2pε} ≤ N^{-D}` for `N ≥ 1` | at `ε = 0.1, D = 1`: `p = 11`, `2pε = 2.2 ≥ 2.1`, slack 0.1 |
| `N` in union bound | `Fintype.card Idx = (W L)^d` (`Sizes.card_Idx`) | `N ≥ 1` | `L ≥ 3`, `W ≥ 1` |
| QUE scale `η_Q = ouEtaQ` | `W^{-ε₀} lam W^{d/2}/N`, `= etaQ sz n (𝔡/3)` (`QUEFromQDiff.lean:85`) | window half-width of `queBadMat … (𝔡/3)` in `UNOUQUEk` is `W^{-ε₀}(lam W^{d/2}/N)` = `η_Q` for every kind (`queWindow`, `Pins.lean:380`), so `Im z = η_Q` is forced | exact identity |
| `η_Q ≤ 1` (needed by `UNOUProfRowk`'s `z.im ≤ 1`; no bulk used) | `η_Q ≤ 𝔡⁻¹ W^{-𝔡/3-d/2}` (from `lam ≤ 𝔡⁻¹`, `N ≥ W^d`) | eventually, `W → ∞` (from `Admissible`) | at the instance n=0: `η_Q = 1.2e-6` vs bound `4.9e-2` |
| `N η_Q` | `W^{-ε₀} lam W^{d/2}` | `≥ W^{2𝔡/3}` from `(eq:WO)` | n=0: `2.52 ≥ 1.26` |
| row-difference shape `K = C lam⁻² W^{-d}` | `N² η_Q² K = C W^{-2ε₀}` (exact) | absorbed by `queChain` (`QUEFromQDiff.lean:463`: same `C * (lam²)⁻¹ / W^d`, `ε₀ < 𝔡/2`) | identity checked numerically below (ratio 1.000000) |
| `queBound` exponent (`Pins.lean:384`) | `-min(2ε₀, 2𝔡/5) + 2c + τ_Q` = `-𝔡/15 + τ_Q` = `-1/150 + τ_Q` | `ε₀ = 𝔡/3 < 𝔡/2`, `c = 𝔡/6 < ε₀`, `c < 𝔡/5` (the `queChain`/`UNQueBand` ranges) | `1/30 < 1/20`; `1/60 < 1/30`; `1/60 < 1/50` |
| `ζ = ouZeta t = 1 - e^{-t}` | `t ∈ [0, N^{-1+τ_U}]` so `ζ ∈ [0,1)` | `UNOUProfRowk` covers `ζ ∈ [0,1]` | n=0: `ζ(t*) = 4.8e-7` |
| `(eq:WO)`, bandwidth, `N → ∞` | `Admissible 𝔠 𝔡` | `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`, `N^𝔠 ≤ W` | `sz0`: `lam = W^{-6/5}` vs `W^{-7/5}` (slack `1/5` in the W-exponent); `N^{1/6} = √2 m³ ≤ m⁵` with `m = 2(n+1)`, n=0: `11.3 ≤ 32` |
| `κ`-range of the padding (band bridges 4.2, 4.3) | `E'_n := if |E_n| ≤ 2-κ then E_n else 0` | `|E'_n| ≤ 2-κ` needs `κ ≤ 2`; `κ > 2` makes the bulk empty, implication vacuous | `κ ≤ 2` uses `0 ≤ 2-κ` |

Mathematical checks of the statements (each argued from the files read; no Lean written):

1. `ouDiagk_of_ouLLk`: `ouDiag_of_ouLL` (`ZeroModeProfile.lean:641-712`) with the carrier `ouMatC (K.M sz)`: the `κ > 2` case is dropped and `T n = {(t,E) | 0 ≤ t ≤ ouTStar sz τU n}` is nonempty (`(0,0)`), the predicate being `bulk sz κ E n → ∀ x, …`, which is exactly what `UNOULLk` supplies per sequence (bulk inside `∀ᶠ n`). Markov needs: `ouP (K.M sz).toUNModel n` a probability measure (`isProbabilityMeasure_ouP`, `OU.lean:44`), `ouMatC` Hermitian (`ouMatC_isHermitian`, `PinsK.lean:79`) so `‖G_xy‖ ≤ η⁻¹`, and measurability of `ω ↦ ouMatC M n t ω` (`ouMatC = ouMat + const` by `ouMatC_eq_ouMat_add`, `PinsK.lean:100`; `measurable_ouMat`, `OU.lean:80`). Each holds for every `UNModelC`. True for every `K`.
2. `ouRowk_of_pins`: `UNOURowk K ML Loc Que = ML → Loc → Que → UNOUClaimsk K` (`PinsK.lean:421-426`); with `τ₀ = ouTauMax 𝔠 𝔡 > 0` (`hA.1`, `hA.2.1`), for `τ_U ≤ τ₀`: `UNOUQUEk` is `UNG2bRowk` applied to `UNOUProfRowk` and `(UNG1Rowk …).2`; `UNOUDiagk` is `ouDiagk_of_ouLLk (UNG1Rowk …).1`. All premise types match literally (check file section 3-4). True.
3. Band bridges: `UNOUProfRowk (band) (band profile)` is the body of `profTilde_rowDiff` (`:469`) with `K.bulk sz κ z.re n ≡ |z.re| ≤ 2-κ` (`unPinsK_band_bulk`, `PinsK.lean:517`, `rfl`) and `P.p· ≡ profP·Tilde` (field projections of the structure literal). `UNOULLk ↔ UNOULL`, `UNOUEq747k ↔ UNOUEq747` at the band: after `ouMatC_toC` (`PinsK.lean:119`) the integrands and measures agree (`unPinsK_toC_toUNModel`); `→` direction: the hypothesis `∀ n, |E n| ≤ 2-κ` makes the bulk condition true at every `n`; `←` direction: padding (table last row) gives `E'` with `|E' n| ≤ 2-κ` for all `n` and `E' n = E n` where `|E n| ≤ 2-κ`, so the eventual conclusion for `E'` gives that for `E` under the bulk condition. True. `UNG1Rowk (band) ↔ UNG1Row`: the two sides have the same prefix `(∀ d, UNMLOut d) → UNLocAvgBand → UNQueBand → ∀ d, 3 ≤ d → ∀ 𝔠 𝔡 sz, Admissible → ∀ τU, 0 < τU → τU ≤ ouTauMax → (· ∧ ·)` (`ZeroModeProfile.lean:126-130` vs check section 3), conclusion by the two iffs. `UNG2bRowk (band) → UNG2bRow`: given `UNG2bRow`'s premises `τU ≤ ouTauMax` (dropped) and `UNOUEq747 sz 𝔡 τU`, convert by `UNOUEq747k_band.2`, discharge `UNOUProfRowk` by bridge 4.1 (`3 ≤ d` is available), apply `UNG2bRowk`, convert by `UNOUQUEk_band.1` (`PinsK.lean:522`). True (one direction only, as pinned).
4. Design (d) (bulk inside `∀ᶠ`) is necessary: with the outside form `(∀ n, bulk (E n) n) → …`, a kind whose bulk is empty at one `n` (e.g. `bulk sz κ E n := n ≠ 0 ∧ |E| ≤ 2-κ`) makes the per-sequence pin vacuous, while `UNOUDiagk` constrains all large `n`. Witness: kind with `H = 0`, at `t = 0`, `E = 0`: `|G_xx| = 1/η_LL = N^{1-2τ_U}` deterministically, so the event `N^ε < |G_xx|` has probability 1, not `≤ N^{-D}` (numbers in (ii)). With the inside form, `T n` needs no bulk and is nonempty.
5. Design (c) (`UNG2bRowk`, not a target, for UN-52): `queFixed` (`QUEFromQDiff.lean:285`) takes `z = E + iη_Q` with `η_Q = etaQ sz n ε₀`, `0 < η_Q`, the expectation hypothesis at all `a b`, the row hypothesis at all `a b b'`; its statement and the visible part of its proof use `queBad_sub` with window `|x-E| ≤ η_Q` (this equals `UNOUQUEk`'s window for every `K`, see table); the proof of `queX_core` (`QUECore.lean:805`) was not read, so that it needs only a Hermitian matrix and a probability measure is the ticket's claim, not verified here. `queChain` (`:463`) depends on `sz` only and needs `3 ≤ d`, `Admissible`, `ε₀ = 𝔡/3 < 𝔡/2`, `C > 0`, error `qdBoundExp sz n (τ/2) (etaQ …)`; `UNOUEq747k` at `τ = τ_Q/2` supplies it. Per-sequence to uniform: filter lemma on the always nonempty `T n`. `τ_U` enters nowhere. So the owed row is true for every `(K,P)` given `UNOUProfRowk`. Not proved here (merged `queFixed` is stated on `sz.Gn`/`seqP`; UN-52 must restate it on the carrier `ouMatC`; this is the ticket's own stated plan).
6. `UNOURowBA` (`BA/UNPins.lean:123`) is by the ticket's statement `UNOURowk` at `UNKind.ba`; whether `Θ̃^{BA}` has the shape `C lam⁻² W^{-d}` is not decidable from the files read in this stage (BA-C3 not present); not a target, no verdict.

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`Defs/Sizes.lean:254-259`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `sz0_admissible : sz0.Admissible (1/6) (1/10)` is merged, `Sizes.lean:331`), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `τ_U = 1/1000`, `E = 0`, `t ∈ [0, N^{-1+τ_U}]`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `lam = 1/64` (`sz0_values`, `:267`). All pointwise hypotheses of the pins and of the row `UNOUProfRowk` (`0 < lam ≤ 𝔡⁻¹`, `0 < z.im = η_Q ≤ 1`, bulk, `ζ ∈ [0,1]`) hold already at `n = 0` and at every `n` checked, so no large witness is needed. The pins `UNOULLk`, `UNOUEq747k`, `UNG1Rowk`, `UNG2bRowk`, `UNOUProfRowk`-at-BA stay hypotheses of the examples (other gates; ticket §4 step 2).

External-limit computation (the `Admissible` limits at `sz0`, closed form): `m = 2(n+1)`, `W = m⁵`, `L = 2m`, `N = (m⁵·2m)³ = 8 m¹⁸ → ∞` (n=0: `8·2¹⁸ = 2097152`); `lam = m⁻⁶ = W^{-6/5}`, and `W^{-d/2+𝔡} = W^{-7/5} ≤ W^{-6/5}` for `W ≥ 1`, `lam ≤ 1/64 ≤ 10 = 𝔡⁻¹`; `N^{1/6} = 8^{1/6} m³ = √2 m³ ≤ m⁵` iff `m² ≥ √2`, true for `m ≥ 2`.

Command: `python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2282/inst.py` (pure Python, floats and `fractions`; `ok` = all of: `L ≥ 3`, `W^{-d/2+𝔡} ≤ lam ≤ 10`, `N^{1/6} ≤ W`, `η_Q ≤ 1`, `η_Q ≤ 𝔡⁻¹W^{-𝔡/3-d/2}`, `Nη_Q ≥ W^{2𝔡/3}`, `ζ ∈ [0,1)`, `N²η_Q²·lam⁻²W^{-d} = W^{-2ε₀}`, `0 < η_LL < 1`)

```
ouTauMax(1/6,1/10) = 1/720 = 0.001388888888888889  tauU= 1/1000  slack tauMax-tauU = 0.00038888888888888887
slack row: 12tauU<=c: True  12tauU<=c*dd: True  tauU<c*dd: True  3tauU/2<2c*dd/3: True
eps0=dd/3= 1/30 <dd/2: True ; c=dd/6= 1/60 <eps0: True ; <dd/5: True
queBound exponent -min(2e0,2dd/5)+2c = -1/150 (+tauQ)
Markov p= 11 2p*eps= 2.2 >= 1+eps+D = 2.1 slack 0.10000000000000009
n=  0 L=4 W=32 N=2.10e+06 WOlo=7.81e-03<=lam=1.56e-02 N^(1/6)=11.3<=W etaQ=1.20e-06<=bd=4.92e-02 NetaQ=2.52e+00>=W^(2dd/3)=1.26 zeta(t*)=4.84e-07 idt=1.000000 ok=True
n=  1 L=8 W=1024 N=5.50e+11 WOlo=6.10e-05<=lam=2.44e-04 N^(1/6)=90.5<=W etaQ=1.15e-11<=bd=2.42e-04 NetaQ=6.35e+00>=W^(2dd/3)=1.59 zeta(t*)=1.87e-12 idt=1.000000 ok=True
n=  2 L=12 W=7776 N=8.12e+14 WOlo=3.57e-06<=lam=2.14e-05 N^(1/6)=305<=W etaQ=1.34e-14<=bd=1.08e-05 NetaQ=1.09e+01>=W^(2dd/3)=1.82 zeta(t*)=1.27e-15 idt=1.000000 ok=True
n=  5 L=24 W=248832 N=2.13e+20 WOlo=2.79e-08<=lam=3.35e-07 N^(1/6)=2.44e+03<=W etaQ=1.29e-19<=bd=5.32e-08 NetaQ=2.75e+01>=W^(2dd/3)=2.29 zeta(t*)=4.92e-21 idt=1.000000 ok=True
n= 10 L=44 W=5153632 N=1.17e+25 WOlo=4.01e-10<=lam=8.82e-09 N^(1/6)=1.51e+04<=W etaQ=5.29e-24<=bd=5.11e-10 NetaQ=6.16e+01>=W^(2dd/3)=2.80 zeta(t*)=9.09e-26 idt=1.000000 ok=True
n=100 L=404 W=336323216032 N=2.51e+42 WOlo=7.29e-17<=lam=1.47e-14 N^(1/6)=1.17e+07<=W etaQ=4.72e-40<=bd=2.12e-17 NetaQ=1.19e+03>=W^(2dd/3)=5.87 zeta(t*)=4.40e-43 idt=1.000000 ok=True
ALL OK: True
kappa= 1/10 padding E'=0 admissible (|0|<=2-kappa): True
kappa= 3/2 padding E'=0 admissible (|0|<=2-kappa): True
kappa= 5/2 padding E'=0 admissible (|0|<=2-kappa): False
eps= 0.1  N^(1-2tauU)= 2036979.4568901274  > N^eps= 4.287093850145173 : True
eps= 0.5  N^(1-2tauU)= 2036979.4568901274  > N^eps= 1448.1546878700494 : True
old-form pin vacuous at n=0 (no E with bulk(E 0, 0)); new form constrains n>=1 only.
```

Verdict per target (mathematics only):
- Targets 1-2 (vocabulary, pins): PASS (definitions; shapes consistent with `UNOUQUEk`, `UNOUDiagk`, `queFixed`, `queChain`).
- Target 3 `ouDiagk_of_ouLLk`, `ouRowk_of_pins`: PASS (check items 1-2).
- Target 4 band bridges 4.1-4.6: PASS (check item 3; 4.2-4.4 need the padding argument, 4.5 is one-directional).
- Target 5 instances: PASS (instance above; deterministic hypotheses hold at `n = 0`; pins stay hypotheses).
- Overall: PASS.

## (b) Script output — stage 1b, `date -u` at writing: Tue Oct  6 10:58:06 UTC 2026

Commit: `6c0bf96 T2282: UN-51g Universality/OUInterfaceK (model-generic OU-layer interface)` on `t/T2282`; `git diff --stat main...t/T2282`:
```
RBM3D/Test/Axioms.lean               |   9 +-
 RBM3D/Universality/OUInterfaceK.lean | 488 +++++++++++++++++++++++++++++++++++
 2 files changed, 492 insertions(+), 5 deletions(-)
```
Module build (`lake build RBM3D.Universality.OUInterfaceK`, tail; the only warnings of the file are long-line lints of the module docstring):
```
[apply] _hK
Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [3739/3739] Replayed RBM3D.Universality.OUInterfaceK
Build completed successfully (3739 jobs).
```
Full `lake build` (run with `import RBM3D.Universality.OUInterfaceK` temporarily added to `RBM3D.lean` in the worktree, reverted by `git checkout RBM3D.lean`; the committed `RBM3D.lean` is unchanged, the hub adds the import at merge). Before the two `OUInterfaceK_*_of_k` theorems existed, the first such run failed with `axiom audit: 3 premise(s) ... [RBM.Univ.UNOUEq747k, RBM.Univ.UNG1Row, RBM.Univ.UNOULL]`. Tail of the passing run:
```
non-vacuity certificates: 0 of 147 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4090 jobs).
```
Registry pre-check (ticket §20 (2)): temp file `import RBM3D` + `import RBM3D.Universality.OUInterfaceK` + `#assert_rbm_axioms`, `lake env lean` (run with the temporary root import above), exit 0:
```
premises found by scanning: 152 (borrowed 1, owed 94, structural 40, refuted 6, superseded 11).
registry: 2 borrowed + 145 owed + 104 structural + 7 refuted + 12 superseded; 118 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
```
`owedProps` entry count (awk): main 146, branch 145 (5 deleted, 4 added in `RBM3D/Test/Axioms.lean`: `UNOULLk`, `UNG1Rowk`, `UNG2bRowk`, `UNOUProfRowk` in; `UNOULL`, `UNG1Row`, `UNG2bRow`, `UNOUDiagk`, `UNOURowk` out).
`#print axioms` of every public theorem (`ax.lean`):
```
'RBM.Univ.ouDiagk_of_ouLLk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.ouRowk_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unOUProfRowk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNOULLk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNOUEq747k_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNG1Rowk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unG2bRow_of_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.ouRow_of_pinsk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceK_UNOULL_of_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceK_UNG1Row_of_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_profRow_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_ouDiagk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_ouLLk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_Eq747k_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_g1k_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_g2b_of_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_ouRowk_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.OUInterfaceKInst.inst_ouRow_band' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`grep -nE "sorry|admit|native_decide|^axiom"` of the file: no hit.
Target statements, extracted by script from `RBM3D/Universality/OUInterfaceK.lean`:
```lean
theorem ouDiagk_of_ouLLk :
    ∀ {d : ℕ} {K : UNKind d} {sz : Sizes d} {τU : ℝ}, UNOULLk K sz τU → UNOUDiagk K sz τU

theorem ouRowk_of_pins (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) {ML Loc Que : Prop}
    (hprof : ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (K d) (P d)) :
    UNG1Rowk K P ML Loc Que → UNG2bRowk K P → UNOURowk K ML Loc Que

theorem unOUProfRowk_band :
    ∀ {d : ℕ}, 3 ≤ d → UNOUProfRowk (UNKind.band d) (UNOUProfile.band d)

theorem UNOULLk_band :
    ∀ {d : ℕ} (sz : Sizes d) (τU : ℝ), UNOULLk (UNKind.band d) sz τU ↔ UNOULL sz τU

theorem UNOUEq747k_band :
    ∀ {d : ℕ} (sz : Sizes d) (𝔡 τU : ℝ),
      UNOUEq747k (UNKind.band d) (UNOUProfile.band d) sz 𝔡 τU ↔ UNOUEq747 sz 𝔡 τU

theorem UNG1Rowk_band :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNG1Row

theorem unG2bRow_of_k :
    UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNG2bRow

theorem ouRow_of_pinsk_band :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand →
      UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNOURow
```
Extra public theorems (not pinned; prefixed with the file stem, CLAUDE.md §3 (E)); they conclude `UNOULL` / `UNG1Row`, because the registry scan (`scanPremises`: a premise counts as proved if some theorem has it as conclusion head; an `↔` does not) needs that:
```lean
theorem OUInterfaceK_UNOULL_of_k {d : ℕ} (sz : Sizes d) (τU : ℝ) :
    UNOULLk (UNKind.band d) sz τU → UNOULL sz τU

theorem OUInterfaceK_UNG1Row_of_k :
    UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
        (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand → UNG1Row
```
Compiled instances (`d = 3`, `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τ_U = 1/1000 ≤ ouTauMax = 1/720`; deterministic hypotheses discharged; `UNOULLk`, `UNG1Rowk`, `UNG2bRowk`, `UNMLOut`, `UNLocAvgBand`, `UNQueBand` stay hypotheses, other gates' pins):
```lean
namespace OUInterfaceKInst

open RBM.Gauss.SizesInst

/-- `UNOUProfRowk` at the band kind, `d = 3`: no hypothesis. -/
theorem inst_profRow_band : UNOUProfRowk (UNKind.band 3) (UNOUProfile.band 3) :=
  unOUProfRowk_band le_rfl

/-- `ouDiagk_of_ouLLk` at `sz0`, `τ_U = 1/1000`: the pin `UNOULLk` (another gate's) stays a hypothesis. -/
theorem inst_ouDiagk_band :
    UNOULLk (UNKind.band 3) sz0 (1 / 1000) → UNOUDiagk (UNKind.band 3) sz0 (1 / 1000) :=
  ouDiagk_of_ouLLk

theorem inst_ouLLk_band : UNOULLk (UNKind.band 3) sz0 (1 / 1000) ↔ UNOULL sz0 (1 / 1000) :=
  UNOULLk_band sz0 (1 / 1000)

theorem inst_Eq747k_band :
    UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000) ↔
      UNOUEq747 sz0 (1 / 10) (1 / 1000) :=
  UNOUEq747k_band sz0 (1 / 10) (1 / 1000)

/-- `UNG1Rowk` at the band, applied at `sz0` (admissible at `𝔠 = 1/6`, `𝔡 = 1/10`),
`τ_U = 1/1000 ≤ ouTauMax = 1/720`. -/
theorem inst_g1k_band
    (r1 : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
    UNOULLk (UNKind.band 3) sz0 (1 / 1000) ∧
      UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) sz0 (1 / 10) (1 / 1000) :=
  r1 hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 1000) (by norm_num)
    (by rw [show ouTauMax (1 / 6) (1 / 10) = 1 / 720 by unfold ouTauMax; norm_num [min_def]]
        norm_num)

theorem inst_g2b_of_k
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)) : UNG2bRow :=
  unG2bRow_of_k r2

/-- `ouRowk_of_pins` at the band kind (the rows are other gates' pins). -/
theorem inst_ouRowk_band
    (r1 : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)) :
    UNOURowk (fun d => UNKind.band d) (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand :=
  ouRowk_of_pins _ _ (fun _ hd => unOUProfRowk_band hd) r1 r2

/-- `ouRow_of_pinsk_band`: the merged `UNOURow` from the two generic rows at the band. -/
theorem inst_ouRow_band
    (r1 : UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand)
    (r2 : UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)) : UNOURow :=
  ouRow_of_pinsk_band r1 r2
```
Acceptance (A): `docs/tickets/checks/T2282-check.lean` with sections 2-3 deleted, `import RBM3D.Universality.OUInterfaceK`, plus `example : RBM.Univ.T2282Check.T2282_<name> := @RBM.Univ.<name>` for the 8 pinned theorems. Acceptance (B): the full check file plus the import, with `@RBM.Univ.UNOULLk = @RBM.Univ.T2282Check.UNOULLk := rfl`, the transports of `UNOUProfRowk`, `UNOUEq747k`, `UNG1Rowk`, `UNG2bRowk` through `⟨P.pm, P.pp⟩`, and the band profile field by field (`rfl`). Scripts: scratchpad `T2282/checkA.lean`, `checkB.lean`:
```
(A) lake env lean checkA.lean: exit 0, lines containing 'error': 0
(B) lake env lean checkB.lean: exit 0, lines containing 'error': 0
```
Name-clash grep (`grep -rnw`; worktree = main b39ac53 plus the branch; tickets in the main worktree, `T2282*` excluded):
```
OUInterfaceK: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNOUProfile: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNOUProfRowk: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNOULLk: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNOUEq747k: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNG1Rowk: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNG2bRowk: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
ouDiagk_of_ouLLk: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
ouRowk_of_pins: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
unOUProfRowk_band: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNOULLk_band: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNOUEq747k_band: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
UNG1Rowk_band: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
unG2bRow_of_k: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
ouRow_of_pinsk_band: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
OUInterfaceKInst: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
OUInterfaceK_UNOULL_of_k: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
OUInterfaceK_UNG1Row_of_k: hits in RBM3D/ + RBM3D.lean (outside the new file and Axioms.lean) = 0; hits in other tickets/checks = 0
```
Ports: none from RBM1D/RBM2D (the ticket names none), so no RBM1D/RBM2D diff-stat. Copied from merged RBM3D files (private there): `ZeroModeProfile.lean:547` filter lemma, `:583` entry bound, `:596` Markov, `:641` `ouDiag_of_ouLL`, `:719` `ouRow_of_pins`; band bridges after `PinsK.lean:522-563`.

Narrative.
- Definitions (`UNOUProfile`, `UNOUProfile.band`, the five pins) are copied from check sections 2-3 by script; acceptance (B) compares them with the check file by `rfl`.
- `ouDiagk_of_ouLLk`: copy of `ouDiag_of_ouLL` on `ouMatC (K.M sz)`; the `κ > 2` case is dropped and the predicate of the filter lemma carries `K.bulk sz κ a.2 n →`; Markov is restated over `UNModelC` (measurability from `ouMatC_eq_ouMat_add` + `measurable_ouMat`, Hermitian from `ouMatC_isHermitian`).
- `ouRowk_of_pins`: the assembly of `ouRow_of_pins` with `hprof` passed to `UNG2bRowk`.
- Bridges 4.2, 4.3 go through the private lemma `OUInterfaceK_pad` (bulk outside versus inside `∀ᶠ`: `κ > 2` both vacuous, `κ ≤ 2` padding `E' n := if |E n| ≤ 2-κ then E n else 0`); 4.1 is `profTilde_rowDiff` by definitional unfolding; 4.4-4.6 as designed.
- The registry scan counts a premise as proved only when a theorem has it as conclusion head; an `↔` does not. The ticket's plan (delete `UNOULL`, `UNG1Row` via `UNOULLk_band.1`, `UNG1Rowk_band.1`) therefore needed two extra theorems `OUInterfaceK_UNOULL_of_k`, `OUInterfaceK_UNG1Row_of_k`. `UNG2bRow` is covered by the pinned `unG2bRow_of_k`.
- `UNOUEq747k` is a hypothesis of no theorem (an earlier instance with such a hypothesis was removed for that reason); the registry has no line for it, as the ticket says.
- Not proved here (not targets): `UNOULLk`, `UNOUEq747k`, `UNG1Rowk` (UN-51), `UNG2bRowk` (UN-52), `UNOUQUEk`, the BA profile and `UNOUProfRowk` at `UNKind.ba` (BA-C3), the converse of `unG2bRow_of_k`, `ouTauMax'`. No merged file changed.

## (c) Verified Mathlib names used (all resolve in the module build)
`Filter.not_eventually`, `Filter.Eventually.of_forall`, `Filter.Eventually.and_eventually`, `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`, `MeasureTheory.measure_iUnion_fintype_le`, `MeasureTheory.ofReal_measureReal`, `MeasureTheory.Integrable.of_bound`, `Measurable.add_const`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_sub`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.rpow_mul`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`, `Nat.le_ceil`, `pow_le_pow_left₀`, `div_le_iff₀`, `le_div_iff₀`. Merged RBM3D names: `#check`ed in the check file section 1, compiled in (A)/(B). Deprecated in this Mathlib: `if_pos`, `if_neg` (build warning; replaced by `simp only [..., ↓reduceIte]`).

## (d) Open issues and paper-delta candidates
- **T2282a** (design, no paper statement): model-generic §7.2 interface: profile `UNOUProfile K` (T data) with row-difference pin `UNOUProfRowk` of shape `C lam⁻² W^{-d}`; scale `η_Q` fixed by the QUE window, error `qdBoundExp` (O3); bulk condition inside `∀ᶠ n`.
- **T2282b**: `UNG2bRowk` has no `τ_U ≤ ouTauMax` bound and takes `UNOUProfRowk` as a premise (O2).
- **T2282c** (registry mechanics, no paper statement): an `↔` does not discharge a registered premise in `scanPremises`; two extra public theorems `OUInterfaceK_UNOULL_of_k`, `OUInterfaceK_UNG1Row_of_k` let `UNOULL`, `UNG1Row` leave `owedProps`. Later bridge tickets of the same kind need the same.
- No `(a′)` correction to section (a).
- Merge note: `Axioms.lean` edits are 5 deletions, 4 additions inside `owedProps` (the four new lines replace the `UNOULL`/`UNG1Row`/`UNG2bRow` lines in place; the `UNOUDiagk`, `UNOURowk` lines are deleted); other tickets edit other lines. The hub adds `import RBM3D.Universality.OUInterfaceK` after `import RBM3D.Universality.ZeroModeProfile` in `RBM3D.lean`.
